-- Prove2me | solution 1 for syracuse_descends_range_2085435_2087435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:20.483434+00:00
-- url     : https://prove2.me/submissions/e1cf6005-26cc-4900-b1c5-604aec6830d6

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

theorem B3519173 : Blo 2085435 3519173 := bbase (se 4 (by rfl) ⟨329922, by rfl⟩ : syracuseStep 3519173 = 659845) (by norm_num)
theorem B2346115 : Blo 2085435 2346115 := bstep (se 1 (by rfl) ⟨1759586, by rfl⟩ : syracuseStep 2346115 = 3519173) B3519173
theorem B3128153 : Blo 2085435 3128153 := bstep (se 2 (by rfl) ⟨1173057, by rfl⟩ : syracuseStep 3128153 = 2346115) B2346115
theorem B2085435 : Blo 2085435 2085435 := bstep (se 1 (by rfl) ⟨1564076, by rfl⟩ : syracuseStep 2085435 = 3128153) B3128153
theorem B15836309 : Blo 2085435 15836309 := bbase (se 6 (by rfl) ⟨371163, by rfl⟩ : syracuseStep 15836309 = 742327) (by norm_num)
theorem B10557539 : Blo 2085435 10557539 := bstep (se 1 (by rfl) ⟨7918154, by rfl⟩ : syracuseStep 10557539 = 15836309) B15836309
theorem B7038359 : Blo 2085435 7038359 := bstep (se 1 (by rfl) ⟨5278769, by rfl⟩ : syracuseStep 7038359 = 10557539) B10557539
theorem B4692239 : Blo 2085435 4692239 := bstep (se 1 (by rfl) ⟨3519179, by rfl⟩ : syracuseStep 4692239 = 7038359) B7038359
theorem B3128159 : Blo 2085435 3128159 := bstep (se 1 (by rfl) ⟨2346119, by rfl⟩ : syracuseStep 3128159 = 4692239) B4692239
theorem B2085439 : Blo 2085435 2085439 := bstep (se 1 (by rfl) ⟨1564079, by rfl⟩ : syracuseStep 2085439 = 3128159) B3128159
theorem B3128165 : Blo 2085435 3128165 := bbase (se 4 (by rfl) ⟨293265, by rfl⟩ : syracuseStep 3128165 = 586531) (by norm_num)
theorem B2085443 : Blo 2085435 2085443 := bstep (se 1 (by rfl) ⟨1564082, by rfl⟩ : syracuseStep 2085443 = 3128165) B3128165
theorem B3959093 : Blo 2085435 3959093 := bbase (se 5 (by rfl) ⟨185582, by rfl⟩ : syracuseStep 3959093 = 371165) (by norm_num)
theorem B2639395 : Blo 2085435 2639395 := bstep (se 1 (by rfl) ⟨1979546, by rfl⟩ : syracuseStep 2639395 = 3959093) B3959093
theorem B3519193 : Blo 2085435 3519193 := bstep (se 2 (by rfl) ⟨1319697, by rfl⟩ : syracuseStep 3519193 = 2639395) B2639395
theorem B4692257 : Blo 2085435 4692257 := bstep (se 2 (by rfl) ⟨1759596, by rfl⟩ : syracuseStep 4692257 = 3519193) B3519193
theorem B3128171 : Blo 2085435 3128171 := bstep (se 1 (by rfl) ⟨2346128, by rfl⟩ : syracuseStep 3128171 = 4692257) B4692257
theorem B2085447 : Blo 2085435 2085447 := bstep (se 1 (by rfl) ⟨1564085, by rfl⟩ : syracuseStep 2085447 = 3128171) B3128171
theorem B2346133 : Blo 2085435 2346133 := bbase (se 6 (by rfl) ⟨54987, by rfl⟩ : syracuseStep 2346133 = 109975) (by norm_num)
theorem B3128177 : Blo 2085435 3128177 := bstep (se 2 (by rfl) ⟨1173066, by rfl⟩ : syracuseStep 3128177 = 2346133) B2346133
theorem B2085451 : Blo 2085435 2085451 := bstep (se 1 (by rfl) ⟨1564088, by rfl⟩ : syracuseStep 2085451 = 3128177) B3128177
theorem B2639405 : Blo 2085435 2639405 := bbase (se 3 (by rfl) ⟨494888, by rfl⟩ : syracuseStep 2639405 = 989777) (by norm_num)
theorem B7038413 : Blo 2085435 7038413 := bstep (se 3 (by rfl) ⟨1319702, by rfl⟩ : syracuseStep 7038413 = 2639405) B2639405
theorem B4692275 : Blo 2085435 4692275 := bstep (se 1 (by rfl) ⟨3519206, by rfl⟩ : syracuseStep 4692275 = 7038413) B7038413
theorem B3128183 : Blo 2085435 3128183 := bstep (se 1 (by rfl) ⟨2346137, by rfl⟩ : syracuseStep 3128183 = 4692275) B4692275
theorem B2085455 : Blo 2085435 2085455 := bstep (se 1 (by rfl) ⟨1564091, by rfl⟩ : syracuseStep 2085455 = 3128183) B3128183
theorem B3128189 : Blo 2085435 3128189 := bbase (se 3 (by rfl) ⟨586535, by rfl⟩ : syracuseStep 3128189 = 1173071) (by norm_num)
theorem B2085459 : Blo 2085435 2085459 := bstep (se 1 (by rfl) ⟨1564094, by rfl⟩ : syracuseStep 2085459 = 3128189) B3128189
theorem B4692293 : Blo 2085435 4692293 := bbase (se 4 (by rfl) ⟨439902, by rfl⟩ : syracuseStep 4692293 = 879805) (by norm_num)
theorem B3128195 : Blo 2085435 3128195 := bstep (se 1 (by rfl) ⟨2346146, by rfl⟩ : syracuseStep 3128195 = 4692293) B4692293
theorem B2085463 : Blo 2085435 2085463 := bstep (se 1 (by rfl) ⟨1564097, by rfl⟩ : syracuseStep 2085463 = 3128195) B3128195
theorem B7516165 : Blo 2085435 7516165 := bbase (se 4 (by rfl) ⟨704640, by rfl⟩ : syracuseStep 7516165 = 1409281) (by norm_num)
theorem B10021553 : Blo 2085435 10021553 := bstep (se 2 (by rfl) ⟨3758082, by rfl⟩ : syracuseStep 10021553 = 7516165) B7516165
theorem B6681035 : Blo 2085435 6681035 := bstep (se 1 (by rfl) ⟨5010776, by rfl⟩ : syracuseStep 6681035 = 10021553) B10021553
theorem B4454023 : Blo 2085435 4454023 := bstep (se 1 (by rfl) ⟨3340517, by rfl⟩ : syracuseStep 4454023 = 6681035) B6681035
theorem B5938697 : Blo 2085435 5938697 := bstep (se 2 (by rfl) ⟨2227011, by rfl⟩ : syracuseStep 5938697 = 4454023) B4454023
theorem B3959131 : Blo 2085435 3959131 := bstep (se 1 (by rfl) ⟨2969348, by rfl⟩ : syracuseStep 3959131 = 5938697) B5938697
theorem B5278841 : Blo 2085435 5278841 := bstep (se 2 (by rfl) ⟨1979565, by rfl⟩ : syracuseStep 5278841 = 3959131) B3959131
theorem B3519227 : Blo 2085435 3519227 := bstep (se 1 (by rfl) ⟨2639420, by rfl⟩ : syracuseStep 3519227 = 5278841) B5278841
theorem B2346151 : Blo 2085435 2346151 := bstep (se 1 (by rfl) ⟨1759613, by rfl⟩ : syracuseStep 2346151 = 3519227) B3519227
theorem B3128201 : Blo 2085435 3128201 := bstep (se 2 (by rfl) ⟨1173075, by rfl⟩ : syracuseStep 3128201 = 2346151) B2346151
theorem B2085467 : Blo 2085435 2085467 := bstep (se 1 (by rfl) ⟨1564100, by rfl⟩ : syracuseStep 2085467 = 3128201) B3128201
theorem B10557701 : Blo 2085435 10557701 := bbase (se 4 (by rfl) ⟨989784, by rfl⟩ : syracuseStep 10557701 = 1979569) (by norm_num)
theorem B7038467 : Blo 2085435 7038467 := bstep (se 1 (by rfl) ⟨5278850, by rfl⟩ : syracuseStep 7038467 = 10557701) B10557701
theorem B4692311 : Blo 2085435 4692311 := bstep (se 1 (by rfl) ⟨3519233, by rfl⟩ : syracuseStep 4692311 = 7038467) B7038467
theorem B3128207 : Blo 2085435 3128207 := bstep (se 1 (by rfl) ⟨2346155, by rfl⟩ : syracuseStep 3128207 = 4692311) B4692311
theorem B2085471 : Blo 2085435 2085471 := bstep (se 1 (by rfl) ⟨1564103, by rfl⟩ : syracuseStep 2085471 = 3128207) B3128207
theorem B3128213 : Blo 2085435 3128213 := bbase (se 6 (by rfl) ⟨73317, by rfl⟩ : syracuseStep 3128213 = 146635) (by norm_num)
theorem B2085475 : Blo 2085435 2085475 := bstep (se 1 (by rfl) ⟨1564106, by rfl⟩ : syracuseStep 2085475 = 3128213) B3128213
theorem B11877461 : Blo 2085435 11877461 := bbase (se 8 (by rfl) ⟨69594, by rfl⟩ : syracuseStep 11877461 = 139189) (by norm_num)
theorem B7918307 : Blo 2085435 7918307 := bstep (se 1 (by rfl) ⟨5938730, by rfl⟩ : syracuseStep 7918307 = 11877461) B11877461
theorem B5278871 : Blo 2085435 5278871 := bstep (se 1 (by rfl) ⟨3959153, by rfl⟩ : syracuseStep 5278871 = 7918307) B7918307
theorem B3519247 : Blo 2085435 3519247 := bstep (se 1 (by rfl) ⟨2639435, by rfl⟩ : syracuseStep 3519247 = 5278871) B5278871
theorem B4692329 : Blo 2085435 4692329 := bstep (se 2 (by rfl) ⟨1759623, by rfl⟩ : syracuseStep 4692329 = 3519247) B3519247
theorem B3128219 : Blo 2085435 3128219 := bstep (se 1 (by rfl) ⟨2346164, by rfl⟩ : syracuseStep 3128219 = 4692329) B4692329
theorem B2085479 : Blo 2085435 2085479 := bstep (se 1 (by rfl) ⟨1564109, by rfl⟩ : syracuseStep 2085479 = 3128219) B3128219
theorem B2346169 : Blo 2085435 2346169 := bbase (se 2 (by rfl) ⟨879813, by rfl⟩ : syracuseStep 2346169 = 1759627) (by norm_num)
theorem B3128225 : Blo 2085435 3128225 := bstep (se 2 (by rfl) ⟨1173084, by rfl⟩ : syracuseStep 3128225 = 2346169) B2346169
theorem B2085483 : Blo 2085435 2085483 := bstep (se 1 (by rfl) ⟨1564112, by rfl⟩ : syracuseStep 2085483 = 3128225) B3128225
theorem B3340549 : Blo 2085435 3340549 := bbase (se 4 (by rfl) ⟨313176, by rfl⟩ : syracuseStep 3340549 = 626353) (by norm_num)
theorem B4454065 : Blo 2085435 4454065 := bstep (se 2 (by rfl) ⟨1670274, by rfl⟩ : syracuseStep 4454065 = 3340549) B3340549
theorem B5938753 : Blo 2085435 5938753 := bstep (se 2 (by rfl) ⟨2227032, by rfl⟩ : syracuseStep 5938753 = 4454065) B4454065
theorem B7918337 : Blo 2085435 7918337 := bstep (se 2 (by rfl) ⟨2969376, by rfl⟩ : syracuseStep 7918337 = 5938753) B5938753
theorem B5278891 : Blo 2085435 5278891 := bstep (se 1 (by rfl) ⟨3959168, by rfl⟩ : syracuseStep 5278891 = 7918337) B7918337
theorem B7038521 : Blo 2085435 7038521 := bstep (se 2 (by rfl) ⟨2639445, by rfl⟩ : syracuseStep 7038521 = 5278891) B5278891
theorem B4692347 : Blo 2085435 4692347 := bstep (se 1 (by rfl) ⟨3519260, by rfl⟩ : syracuseStep 4692347 = 7038521) B7038521
theorem B3128231 : Blo 2085435 3128231 := bstep (se 1 (by rfl) ⟨2346173, by rfl⟩ : syracuseStep 3128231 = 4692347) B4692347
theorem B2085487 : Blo 2085435 2085487 := bstep (se 1 (by rfl) ⟨1564115, by rfl⟩ : syracuseStep 2085487 = 3128231) B3128231
theorem B3128237 : Blo 2085435 3128237 := bbase (se 3 (by rfl) ⟨586544, by rfl⟩ : syracuseStep 3128237 = 1173089) (by norm_num)
theorem B2085491 : Blo 2085435 2085491 := bstep (se 1 (by rfl) ⟨1564118, by rfl⟩ : syracuseStep 2085491 = 3128237) B3128237
theorem B4692365 : Blo 2085435 4692365 := bbase (se 3 (by rfl) ⟨879818, by rfl⟩ : syracuseStep 4692365 = 1759637) (by norm_num)
theorem B3128243 : Blo 2085435 3128243 := bstep (se 1 (by rfl) ⟨2346182, by rfl⟩ : syracuseStep 3128243 = 4692365) B4692365
theorem B2085495 : Blo 2085435 2085495 := bstep (se 1 (by rfl) ⟨1564121, by rfl⟩ : syracuseStep 2085495 = 3128243) B3128243
theorem B2639461 : Blo 2085435 2639461 := bbase (se 4 (by rfl) ⟨247449, by rfl⟩ : syracuseStep 2639461 = 494899) (by norm_num)
theorem B3519281 : Blo 2085435 3519281 := bstep (se 2 (by rfl) ⟨1319730, by rfl⟩ : syracuseStep 3519281 = 2639461) B2639461
theorem B2346187 : Blo 2085435 2346187 := bstep (se 1 (by rfl) ⟨1759640, by rfl⟩ : syracuseStep 2346187 = 3519281) B3519281
theorem B3128249 : Blo 2085435 3128249 := bstep (se 2 (by rfl) ⟨1173093, by rfl⟩ : syracuseStep 3128249 = 2346187) B2346187
theorem B2085499 : Blo 2085435 2085499 := bstep (se 1 (by rfl) ⟨1564124, by rfl⟩ : syracuseStep 2085499 = 3128249) B3128249
theorem B20043445 : Blo 2085435 20043445 := bbase (se 5 (by rfl) ⟨939536, by rfl⟩ : syracuseStep 20043445 = 1879073) (by norm_num)
theorem B26724593 : Blo 2085435 26724593 := bstep (se 2 (by rfl) ⟨10021722, by rfl⟩ : syracuseStep 26724593 = 20043445) B20043445
theorem B17816395 : Blo 2085435 17816395 := bstep (se 1 (by rfl) ⟨13362296, by rfl⟩ : syracuseStep 17816395 = 26724593) B26724593
theorem B23755193 : Blo 2085435 23755193 := bstep (se 2 (by rfl) ⟨8908197, by rfl⟩ : syracuseStep 23755193 = 17816395) B17816395
theorem B15836795 : Blo 2085435 15836795 := bstep (se 1 (by rfl) ⟨11877596, by rfl⟩ : syracuseStep 15836795 = 23755193) B23755193
theorem B10557863 : Blo 2085435 10557863 := bstep (se 1 (by rfl) ⟨7918397, by rfl⟩ : syracuseStep 10557863 = 15836795) B15836795
theorem B7038575 : Blo 2085435 7038575 := bstep (se 1 (by rfl) ⟨5278931, by rfl⟩ : syracuseStep 7038575 = 10557863) B10557863
theorem B4692383 : Blo 2085435 4692383 := bstep (se 1 (by rfl) ⟨3519287, by rfl⟩ : syracuseStep 4692383 = 7038575) B7038575
theorem B3128255 : Blo 2085435 3128255 := bstep (se 1 (by rfl) ⟨2346191, by rfl⟩ : syracuseStep 3128255 = 4692383) B4692383
theorem B2085503 : Blo 2085435 2085503 := bstep (se 1 (by rfl) ⟨1564127, by rfl⟩ : syracuseStep 2085503 = 3128255) B3128255
theorem B3128261 : Blo 2085435 3128261 := bbase (se 4 (by rfl) ⟨293274, by rfl⟩ : syracuseStep 3128261 = 586549) (by norm_num)
theorem B2085507 : Blo 2085435 2085507 := bstep (se 1 (by rfl) ⟨1564130, by rfl⟩ : syracuseStep 2085507 = 3128261) B3128261
theorem B3519301 : Blo 2085435 3519301 := bbase (se 4 (by rfl) ⟨329934, by rfl⟩ : syracuseStep 3519301 = 659869) (by norm_num)
theorem B4692401 : Blo 2085435 4692401 := bstep (se 2 (by rfl) ⟨1759650, by rfl⟩ : syracuseStep 4692401 = 3519301) B3519301
theorem B3128267 : Blo 2085435 3128267 := bstep (se 1 (by rfl) ⟨2346200, by rfl⟩ : syracuseStep 3128267 = 4692401) B4692401
theorem B2085511 : Blo 2085435 2085511 := bstep (se 1 (by rfl) ⟨1564133, by rfl⟩ : syracuseStep 2085511 = 3128267) B3128267
theorem B2346205 : Blo 2085435 2346205 := bbase (se 3 (by rfl) ⟨439913, by rfl⟩ : syracuseStep 2346205 = 879827) (by norm_num)
theorem B3128273 : Blo 2085435 3128273 := bstep (se 2 (by rfl) ⟨1173102, by rfl⟩ : syracuseStep 3128273 = 2346205) B2346205
theorem B2085515 : Blo 2085435 2085515 := bstep (se 1 (by rfl) ⟨1564136, by rfl⟩ : syracuseStep 2085515 = 3128273) B3128273
theorem B7038629 : Blo 2085435 7038629 := bbase (se 4 (by rfl) ⟨659871, by rfl⟩ : syracuseStep 7038629 = 1319743) (by norm_num)
theorem B4692419 : Blo 2085435 4692419 := bstep (se 1 (by rfl) ⟨3519314, by rfl⟩ : syracuseStep 4692419 = 7038629) B7038629
theorem B3128279 : Blo 2085435 3128279 := bstep (se 1 (by rfl) ⟨2346209, by rfl⟩ : syracuseStep 3128279 = 4692419) B4692419
theorem B2085519 : Blo 2085435 2085519 := bstep (se 1 (by rfl) ⟨1564139, by rfl⟩ : syracuseStep 2085519 = 3128279) B3128279
theorem B3128285 : Blo 2085435 3128285 := bbase (se 3 (by rfl) ⟨586553, by rfl⟩ : syracuseStep 3128285 = 1173107) (by norm_num)
theorem B2085523 : Blo 2085435 2085523 := bstep (se 1 (by rfl) ⟨1564142, by rfl⟩ : syracuseStep 2085523 = 3128285) B3128285
theorem B4692437 : Blo 2085435 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B3128291 : Blo 2085435 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B2085527 : Blo 2085435 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B6958453 : Blo 2085435 6958453 := bbase (se 5 (by rfl) ⟨326177, by rfl⟩ : syracuseStep 6958453 = 652355) (by norm_num)
theorem B9277937 : Blo 2085435 9277937 := bstep (se 2 (by rfl) ⟨3479226, by rfl⟩ : syracuseStep 9277937 = 6958453) B6958453
theorem B6185291 : Blo 2085435 6185291 := bstep (se 1 (by rfl) ⟨4638968, by rfl⟩ : syracuseStep 6185291 = 9277937) B9277937
theorem B65976437 : Blo 2085435 65976437 := bstep (se 5 (by rfl) ⟨3092645, by rfl⟩ : syracuseStep 65976437 = 6185291) B6185291
theorem B43984291 : Blo 2085435 43984291 := bstep (se 1 (by rfl) ⟨32988218, by rfl⟩ : syracuseStep 43984291 = 65976437) B65976437
theorem B58645721 : Blo 2085435 58645721 := bstep (se 2 (by rfl) ⟨21992145, by rfl⟩ : syracuseStep 58645721 = 43984291) B43984291
theorem B156388589 : Blo 2085435 156388589 := bstep (se 3 (by rfl) ⟨29322860, by rfl⟩ : syracuseStep 156388589 = 58645721) B58645721
theorem B104259059 : Blo 2085435 104259059 := bstep (se 1 (by rfl) ⟨78194294, by rfl⟩ : syracuseStep 104259059 = 156388589) B156388589
theorem B69506039 : Blo 2085435 69506039 := bstep (se 1 (by rfl) ⟨52129529, by rfl⟩ : syracuseStep 69506039 = 104259059) B104259059
theorem B46337359 : Blo 2085435 46337359 := bstep (se 1 (by rfl) ⟨34753019, by rfl⟩ : syracuseStep 46337359 = 69506039) B69506039
theorem B61783145 : Blo 2085435 61783145 := bstep (se 2 (by rfl) ⟨23168679, by rfl⟩ : syracuseStep 61783145 = 46337359) B46337359
theorem B41188763 : Blo 2085435 41188763 := bstep (se 1 (by rfl) ⟨30891572, by rfl⟩ : syracuseStep 41188763 = 61783145) B61783145
theorem B27459175 : Blo 2085435 27459175 := bstep (se 1 (by rfl) ⟨20594381, by rfl⟩ : syracuseStep 27459175 = 41188763) B41188763
theorem B36612233 : Blo 2085435 36612233 := bstep (se 2 (by rfl) ⟨13729587, by rfl⟩ : syracuseStep 36612233 = 27459175) B27459175
theorem B24408155 : Blo 2085435 24408155 := bstep (se 1 (by rfl) ⟨18306116, by rfl⟩ : syracuseStep 24408155 = 36612233) B36612233
theorem B16272103 : Blo 2085435 16272103 := bstep (se 1 (by rfl) ⟨12204077, by rfl⟩ : syracuseStep 16272103 = 24408155) B24408155
theorem B21696137 : Blo 2085435 21696137 := bstep (se 2 (by rfl) ⟨8136051, by rfl⟩ : syracuseStep 21696137 = 16272103) B16272103
theorem B14464091 : Blo 2085435 14464091 := bstep (se 1 (by rfl) ⟨10848068, by rfl⟩ : syracuseStep 14464091 = 21696137) B21696137
theorem B9642727 : Blo 2085435 9642727 := bstep (se 1 (by rfl) ⟨7232045, by rfl⟩ : syracuseStep 9642727 = 14464091) B14464091
theorem B12856969 : Blo 2085435 12856969 := bstep (se 2 (by rfl) ⟨4821363, by rfl⟩ : syracuseStep 12856969 = 9642727) B9642727
theorem B17142625 : Blo 2085435 17142625 := bstep (se 2 (by rfl) ⟨6428484, by rfl⟩ : syracuseStep 17142625 = 12856969) B12856969
theorem B22856833 : Blo 2085435 22856833 := bstep (se 2 (by rfl) ⟨8571312, by rfl⟩ : syracuseStep 22856833 = 17142625) B17142625
theorem B30475777 : Blo 2085435 30475777 := bstep (se 2 (by rfl) ⟨11428416, by rfl⟩ : syracuseStep 30475777 = 22856833) B22856833
theorem B40634369 : Blo 2085435 40634369 := bstep (se 2 (by rfl) ⟨15237888, by rfl⟩ : syracuseStep 40634369 = 30475777) B30475777
theorem B27089579 : Blo 2085435 27089579 := bstep (se 1 (by rfl) ⟨20317184, by rfl⟩ : syracuseStep 27089579 = 40634369) B40634369
theorem B18059719 : Blo 2085435 18059719 := bstep (se 1 (by rfl) ⟨13544789, by rfl⟩ : syracuseStep 18059719 = 27089579) B27089579
theorem B24079625 : Blo 2085435 24079625 := bstep (se 2 (by rfl) ⟨9029859, by rfl⟩ : syracuseStep 24079625 = 18059719) B18059719
theorem B16053083 : Blo 2085435 16053083 := bstep (se 1 (by rfl) ⟨12039812, by rfl⟩ : syracuseStep 16053083 = 24079625) B24079625
theorem B10702055 : Blo 2085435 10702055 := bstep (se 1 (by rfl) ⟨8026541, by rfl⟩ : syracuseStep 10702055 = 16053083) B16053083
theorem B28538813 : Blo 2085435 28538813 := bstep (se 3 (by rfl) ⟨5351027, by rfl⟩ : syracuseStep 28538813 = 10702055) B10702055
theorem B19025875 : Blo 2085435 19025875 := bstep (se 1 (by rfl) ⟨14269406, by rfl⟩ : syracuseStep 19025875 = 28538813) B28538813
theorem B25367833 : Blo 2085435 25367833 := bstep (se 2 (by rfl) ⟨9512937, by rfl⟩ : syracuseStep 25367833 = 19025875) B19025875
theorem B33823777 : Blo 2085435 33823777 := bstep (se 2 (by rfl) ⟨12683916, by rfl⟩ : syracuseStep 33823777 = 25367833) B25367833
theorem B45098369 : Blo 2085435 45098369 := bstep (se 2 (by rfl) ⟨16911888, by rfl⟩ : syracuseStep 45098369 = 33823777) B33823777
theorem B30065579 : Blo 2085435 30065579 := bstep (se 1 (by rfl) ⟨22549184, by rfl⟩ : syracuseStep 30065579 = 45098369) B45098369
theorem B20043719 : Blo 2085435 20043719 := bstep (se 1 (by rfl) ⟨15032789, by rfl⟩ : syracuseStep 20043719 = 30065579) B30065579
theorem B13362479 : Blo 2085435 13362479 := bstep (se 1 (by rfl) ⟨10021859, by rfl⟩ : syracuseStep 13362479 = 20043719) B20043719
theorem B8908319 : Blo 2085435 8908319 := bstep (se 1 (by rfl) ⟨6681239, by rfl⟩ : syracuseStep 8908319 = 13362479) B13362479
theorem B5938879 : Blo 2085435 5938879 := bstep (se 1 (by rfl) ⟨4454159, by rfl⟩ : syracuseStep 5938879 = 8908319) B8908319
theorem B7918505 : Blo 2085435 7918505 := bstep (se 2 (by rfl) ⟨2969439, by rfl⟩ : syracuseStep 7918505 = 5938879) B5938879
theorem B5279003 : Blo 2085435 5279003 := bstep (se 1 (by rfl) ⟨3959252, by rfl⟩ : syracuseStep 5279003 = 7918505) B7918505
theorem B3519335 : Blo 2085435 3519335 := bstep (se 1 (by rfl) ⟨2639501, by rfl⟩ : syracuseStep 3519335 = 5279003) B5279003
theorem B2346223 : Blo 2085435 2346223 := bstep (se 1 (by rfl) ⟨1759667, by rfl⟩ : syracuseStep 2346223 = 3519335) B3519335
theorem B3128297 : Blo 2085435 3128297 := bstep (se 2 (by rfl) ⟨1173111, by rfl⟩ : syracuseStep 3128297 = 2346223) B2346223
theorem B2085531 : Blo 2085435 2085531 := bstep (se 1 (by rfl) ⟨1564148, by rfl⟩ : syracuseStep 2085531 = 3128297) B3128297
theorem B10021877 : Blo 2085435 10021877 := bbase (se 5 (by rfl) ⟨469775, by rfl⟩ : syracuseStep 10021877 = 939551) (by norm_num)
theorem B6681251 : Blo 2085435 6681251 := bstep (se 1 (by rfl) ⟨5010938, by rfl⟩ : syracuseStep 6681251 = 10021877) B10021877
theorem B17816669 : Blo 2085435 17816669 := bstep (se 3 (by rfl) ⟨3340625, by rfl⟩ : syracuseStep 17816669 = 6681251) B6681251
theorem B11877779 : Blo 2085435 11877779 := bstep (se 1 (by rfl) ⟨8908334, by rfl⟩ : syracuseStep 11877779 = 17816669) B17816669
theorem B7918519 : Blo 2085435 7918519 := bstep (se 1 (by rfl) ⟨5938889, by rfl⟩ : syracuseStep 7918519 = 11877779) B11877779
theorem B10558025 : Blo 2085435 10558025 := bstep (se 2 (by rfl) ⟨3959259, by rfl⟩ : syracuseStep 10558025 = 7918519) B7918519
theorem B7038683 : Blo 2085435 7038683 := bstep (se 1 (by rfl) ⟨5279012, by rfl⟩ : syracuseStep 7038683 = 10558025) B10558025
theorem B4692455 : Blo 2085435 4692455 := bstep (se 1 (by rfl) ⟨3519341, by rfl⟩ : syracuseStep 4692455 = 7038683) B7038683
theorem B3128303 : Blo 2085435 3128303 := bstep (se 1 (by rfl) ⟨2346227, by rfl⟩ : syracuseStep 3128303 = 4692455) B4692455
theorem B2085535 : Blo 2085435 2085535 := bstep (se 1 (by rfl) ⟨1564151, by rfl⟩ : syracuseStep 2085535 = 3128303) B3128303
theorem B3128309 : Blo 2085435 3128309 := bbase (se 5 (by rfl) ⟨146639, by rfl⟩ : syracuseStep 3128309 = 293279) (by norm_num)
theorem B2085539 : Blo 2085435 2085539 := bstep (se 1 (by rfl) ⟨1564154, by rfl⟩ : syracuseStep 2085539 = 3128309) B3128309
theorem B16911989 : Blo 2085435 16911989 := bbase (se 5 (by rfl) ⟨792749, by rfl⟩ : syracuseStep 16911989 = 1585499) (by norm_num)
theorem B11274659 : Blo 2085435 11274659 := bstep (se 1 (by rfl) ⟨8455994, by rfl⟩ : syracuseStep 11274659 = 16911989) B16911989
theorem B7516439 : Blo 2085435 7516439 := bstep (se 1 (by rfl) ⟨5637329, by rfl⟩ : syracuseStep 7516439 = 11274659) B11274659
theorem B5010959 : Blo 2085435 5010959 := bstep (se 1 (by rfl) ⟨3758219, by rfl⟩ : syracuseStep 5010959 = 7516439) B7516439
theorem B3340639 : Blo 2085435 3340639 := bstep (se 1 (by rfl) ⟨2505479, by rfl⟩ : syracuseStep 3340639 = 5010959) B5010959
theorem B4454185 : Blo 2085435 4454185 := bstep (se 2 (by rfl) ⟨1670319, by rfl⟩ : syracuseStep 4454185 = 3340639) B3340639
theorem B5938913 : Blo 2085435 5938913 := bstep (se 2 (by rfl) ⟨2227092, by rfl⟩ : syracuseStep 5938913 = 4454185) B4454185
theorem B3959275 : Blo 2085435 3959275 := bstep (se 1 (by rfl) ⟨2969456, by rfl⟩ : syracuseStep 3959275 = 5938913) B5938913
theorem B5279033 : Blo 2085435 5279033 := bstep (se 2 (by rfl) ⟨1979637, by rfl⟩ : syracuseStep 5279033 = 3959275) B3959275
theorem B3519355 : Blo 2085435 3519355 := bstep (se 1 (by rfl) ⟨2639516, by rfl⟩ : syracuseStep 3519355 = 5279033) B5279033
theorem B4692473 : Blo 2085435 4692473 := bstep (se 2 (by rfl) ⟨1759677, by rfl⟩ : syracuseStep 4692473 = 3519355) B3519355
theorem B3128315 : Blo 2085435 3128315 := bstep (se 1 (by rfl) ⟨2346236, by rfl⟩ : syracuseStep 3128315 = 4692473) B4692473
theorem B2085543 : Blo 2085435 2085543 := bstep (se 1 (by rfl) ⟨1564157, by rfl⟩ : syracuseStep 2085543 = 3128315) B3128315
theorem B2346241 : Blo 2085435 2346241 := bbase (se 2 (by rfl) ⟨879840, by rfl⟩ : syracuseStep 2346241 = 1759681) (by norm_num)
theorem B3128321 : Blo 2085435 3128321 := bstep (se 2 (by rfl) ⟨1173120, by rfl⟩ : syracuseStep 3128321 = 2346241) B2346241
theorem B2085547 : Blo 2085435 2085547 := bstep (se 1 (by rfl) ⟨1564160, by rfl⟩ : syracuseStep 2085547 = 3128321) B3128321
theorem B5279053 : Blo 2085435 5279053 := bbase (se 3 (by rfl) ⟨989822, by rfl⟩ : syracuseStep 5279053 = 1979645) (by norm_num)
theorem B7038737 : Blo 2085435 7038737 := bstep (se 2 (by rfl) ⟨2639526, by rfl⟩ : syracuseStep 7038737 = 5279053) B5279053
theorem B4692491 : Blo 2085435 4692491 := bstep (se 1 (by rfl) ⟨3519368, by rfl⟩ : syracuseStep 4692491 = 7038737) B7038737
theorem B3128327 : Blo 2085435 3128327 := bstep (se 1 (by rfl) ⟨2346245, by rfl⟩ : syracuseStep 3128327 = 4692491) B4692491
theorem B2085551 : Blo 2085435 2085551 := bstep (se 1 (by rfl) ⟨1564163, by rfl⟩ : syracuseStep 2085551 = 3128327) B3128327
theorem B3128333 : Blo 2085435 3128333 := bbase (se 3 (by rfl) ⟨586562, by rfl⟩ : syracuseStep 3128333 = 1173125) (by norm_num)
theorem B2085555 : Blo 2085435 2085555 := bstep (se 1 (by rfl) ⟨1564166, by rfl⟩ : syracuseStep 2085555 = 3128333) B3128333
theorem B4692509 : Blo 2085435 4692509 := bbase (se 3 (by rfl) ⟨879845, by rfl⟩ : syracuseStep 4692509 = 1759691) (by norm_num)
theorem B3128339 : Blo 2085435 3128339 := bstep (se 1 (by rfl) ⟨2346254, by rfl⟩ : syracuseStep 3128339 = 4692509) B4692509
theorem B2085559 : Blo 2085435 2085559 := bstep (se 1 (by rfl) ⟨1564169, by rfl⟩ : syracuseStep 2085559 = 3128339) B3128339
theorem B3519389 : Blo 2085435 3519389 := bbase (se 3 (by rfl) ⟨659885, by rfl⟩ : syracuseStep 3519389 = 1319771) (by norm_num)
theorem B2346259 : Blo 2085435 2346259 := bstep (se 1 (by rfl) ⟨1759694, by rfl⟩ : syracuseStep 2346259 = 3519389) B3519389
theorem B3128345 : Blo 2085435 3128345 := bstep (se 2 (by rfl) ⟨1173129, by rfl⟩ : syracuseStep 3128345 = 2346259) B2346259
theorem B2085563 : Blo 2085435 2085563 := bstep (se 1 (by rfl) ⟨1564172, by rfl⟩ : syracuseStep 2085563 = 3128345) B3128345
theorem B3567413 : Blo 2085435 3567413 := bbase (se 5 (by rfl) ⟨167222, by rfl⟩ : syracuseStep 3567413 = 334445) (by norm_num)
theorem B9513101 : Blo 2085435 9513101 := bstep (se 3 (by rfl) ⟨1783706, by rfl⟩ : syracuseStep 9513101 = 3567413) B3567413
theorem B6342067 : Blo 2085435 6342067 := bstep (se 1 (by rfl) ⟨4756550, by rfl⟩ : syracuseStep 6342067 = 9513101) B9513101
theorem B8456089 : Blo 2085435 8456089 := bstep (se 2 (by rfl) ⟨3171033, by rfl⟩ : syracuseStep 8456089 = 6342067) B6342067
theorem B11274785 : Blo 2085435 11274785 := bstep (se 2 (by rfl) ⟨4228044, by rfl⟩ : syracuseStep 11274785 = 8456089) B8456089
theorem B7516523 : Blo 2085435 7516523 := bstep (se 1 (by rfl) ⟨5637392, by rfl⟩ : syracuseStep 7516523 = 11274785) B11274785
theorem B20044061 : Blo 2085435 20044061 := bstep (se 3 (by rfl) ⟨3758261, by rfl⟩ : syracuseStep 20044061 = 7516523) B7516523
theorem B13362707 : Blo 2085435 13362707 := bstep (se 1 (by rfl) ⟨10022030, by rfl⟩ : syracuseStep 13362707 = 20044061) B20044061
theorem B8908471 : Blo 2085435 8908471 := bstep (se 1 (by rfl) ⟨6681353, by rfl⟩ : syracuseStep 8908471 = 13362707) B13362707
theorem B11877961 : Blo 2085435 11877961 := bstep (se 2 (by rfl) ⟨4454235, by rfl⟩ : syracuseStep 11877961 = 8908471) B8908471
theorem B15837281 : Blo 2085435 15837281 := bstep (se 2 (by rfl) ⟨5938980, by rfl⟩ : syracuseStep 15837281 = 11877961) B11877961
theorem B10558187 : Blo 2085435 10558187 := bstep (se 1 (by rfl) ⟨7918640, by rfl⟩ : syracuseStep 10558187 = 15837281) B15837281
theorem B7038791 : Blo 2085435 7038791 := bstep (se 1 (by rfl) ⟨5279093, by rfl⟩ : syracuseStep 7038791 = 10558187) B10558187
theorem B4692527 : Blo 2085435 4692527 := bstep (se 1 (by rfl) ⟨3519395, by rfl⟩ : syracuseStep 4692527 = 7038791) B7038791
theorem B3128351 : Blo 2085435 3128351 := bstep (se 1 (by rfl) ⟨2346263, by rfl⟩ : syracuseStep 3128351 = 4692527) B4692527
theorem B2085567 : Blo 2085435 2085567 := bstep (se 1 (by rfl) ⟨1564175, by rfl⟩ : syracuseStep 2085567 = 3128351) B3128351
theorem B3128357 : Blo 2085435 3128357 := bbase (se 4 (by rfl) ⟨293283, by rfl⟩ : syracuseStep 3128357 = 586567) (by norm_num)
theorem B2085571 : Blo 2085435 2085571 := bstep (se 1 (by rfl) ⟨1564178, by rfl⟩ : syracuseStep 2085571 = 3128357) B3128357
theorem B2639557 : Blo 2085435 2639557 := bbase (se 4 (by rfl) ⟨247458, by rfl⟩ : syracuseStep 2639557 = 494917) (by norm_num)
theorem B3519409 : Blo 2085435 3519409 := bstep (se 2 (by rfl) ⟨1319778, by rfl⟩ : syracuseStep 3519409 = 2639557) B2639557
theorem B4692545 : Blo 2085435 4692545 := bstep (se 2 (by rfl) ⟨1759704, by rfl⟩ : syracuseStep 4692545 = 3519409) B3519409
theorem B3128363 : Blo 2085435 3128363 := bstep (se 1 (by rfl) ⟨2346272, by rfl⟩ : syracuseStep 3128363 = 4692545) B4692545
theorem B2085575 : Blo 2085435 2085575 := bstep (se 1 (by rfl) ⟨1564181, by rfl⟩ : syracuseStep 2085575 = 3128363) B3128363
theorem B2346277 : Blo 2085435 2346277 := bbase (se 4 (by rfl) ⟨219963, by rfl⟩ : syracuseStep 2346277 = 439927) (by norm_num)
theorem B3128369 : Blo 2085435 3128369 := bstep (se 2 (by rfl) ⟨1173138, by rfl⟩ : syracuseStep 3128369 = 2346277) B2346277
theorem B2085579 : Blo 2085435 2085579 := bstep (se 1 (by rfl) ⟨1564184, by rfl⟩ : syracuseStep 2085579 = 3128369) B3128369
theorem B2675581 : Blo 2085435 2675581 := bbase (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) (by norm_num)
theorem B14269765 : Blo 2085435 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B19026353 : Blo 2085435 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B12684235 : Blo 2085435 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B16912313 : Blo 2085435 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B11274875 : Blo 2085435 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B7516583 : Blo 2085435 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B5011055 : Blo 2085435 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B3340703 : Blo 2085435 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B8908541 : Blo 2085435 8908541 := bstep (se 3 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 8908541 = 3340703) B3340703
theorem B5939027 : Blo 2085435 5939027 := bstep (se 1 (by rfl) ⟨4454270, by rfl⟩ : syracuseStep 5939027 = 8908541) B8908541
theorem B3959351 : Blo 2085435 3959351 := bstep (se 1 (by rfl) ⟨2969513, by rfl⟩ : syracuseStep 3959351 = 5939027) B5939027
theorem B2639567 : Blo 2085435 2639567 := bstep (se 1 (by rfl) ⟨1979675, by rfl⟩ : syracuseStep 2639567 = 3959351) B3959351
theorem B7038845 : Blo 2085435 7038845 := bstep (se 3 (by rfl) ⟨1319783, by rfl⟩ : syracuseStep 7038845 = 2639567) B2639567
theorem B4692563 : Blo 2085435 4692563 := bstep (se 1 (by rfl) ⟨3519422, by rfl⟩ : syracuseStep 4692563 = 7038845) B7038845
theorem B3128375 : Blo 2085435 3128375 := bstep (se 1 (by rfl) ⟨2346281, by rfl⟩ : syracuseStep 3128375 = 4692563) B4692563
theorem B2085583 : Blo 2085435 2085583 := bstep (se 1 (by rfl) ⟨1564187, by rfl⟩ : syracuseStep 2085583 = 3128375) B3128375
theorem B3128381 : Blo 2085435 3128381 := bbase (se 3 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 3128381 = 1173143) (by norm_num)
theorem B2085587 : Blo 2085435 2085587 := bstep (se 1 (by rfl) ⟨1564190, by rfl⟩ : syracuseStep 2085587 = 3128381) B3128381
theorem B4692581 : Blo 2085435 4692581 := bbase (se 4 (by rfl) ⟨439929, by rfl⟩ : syracuseStep 4692581 = 879859) (by norm_num)
theorem B3128387 : Blo 2085435 3128387 := bstep (se 1 (by rfl) ⟨2346290, by rfl⟩ : syracuseStep 3128387 = 4692581) B4692581
theorem B2085591 : Blo 2085435 2085591 := bstep (se 1 (by rfl) ⟨1564193, by rfl⟩ : syracuseStep 2085591 = 3128387) B3128387
theorem B5279165 : Blo 2085435 5279165 := bbase (se 3 (by rfl) ⟨989843, by rfl⟩ : syracuseStep 5279165 = 1979687) (by norm_num)
theorem B3519443 : Blo 2085435 3519443 := bstep (se 1 (by rfl) ⟨2639582, by rfl⟩ : syracuseStep 3519443 = 5279165) B5279165
theorem B2346295 : Blo 2085435 2346295 := bstep (se 1 (by rfl) ⟨1759721, by rfl⟩ : syracuseStep 2346295 = 3519443) B3519443
theorem B3128393 : Blo 2085435 3128393 := bstep (se 2 (by rfl) ⟨1173147, by rfl⟩ : syracuseStep 3128393 = 2346295) B2346295
theorem B2085595 : Blo 2085435 2085595 := bstep (se 1 (by rfl) ⟨1564196, by rfl⟩ : syracuseStep 2085595 = 3128393) B3128393
theorem B3959381 : Blo 2085435 3959381 := bbase (se 8 (by rfl) ⟨23199, by rfl⟩ : syracuseStep 3959381 = 46399) (by norm_num)
theorem B10558349 : Blo 2085435 10558349 := bstep (se 3 (by rfl) ⟨1979690, by rfl⟩ : syracuseStep 10558349 = 3959381) B3959381
theorem B7038899 : Blo 2085435 7038899 := bstep (se 1 (by rfl) ⟨5279174, by rfl⟩ : syracuseStep 7038899 = 10558349) B10558349
theorem B4692599 : Blo 2085435 4692599 := bstep (se 1 (by rfl) ⟨3519449, by rfl⟩ : syracuseStep 4692599 = 7038899) B7038899
theorem B3128399 : Blo 2085435 3128399 := bstep (se 1 (by rfl) ⟨2346299, by rfl⟩ : syracuseStep 3128399 = 4692599) B4692599
theorem B2085599 : Blo 2085435 2085599 := bstep (se 1 (by rfl) ⟨1564199, by rfl⟩ : syracuseStep 2085599 = 3128399) B3128399
theorem B3128405 : Blo 2085435 3128405 := bbase (se 8 (by rfl) ⟨18330, by rfl⟩ : syracuseStep 3128405 = 36661) (by norm_num)
theorem B2085603 : Blo 2085435 2085603 := bstep (se 1 (by rfl) ⟨1564202, by rfl⟩ : syracuseStep 2085603 = 3128405) B3128405
theorem B13362965 : Blo 2085435 13362965 := bbase (se 6 (by rfl) ⟨313194, by rfl⟩ : syracuseStep 13362965 = 626389) (by norm_num)
theorem B8908643 : Blo 2085435 8908643 := bstep (se 1 (by rfl) ⟨6681482, by rfl⟩ : syracuseStep 8908643 = 13362965) B13362965
theorem B5939095 : Blo 2085435 5939095 := bstep (se 1 (by rfl) ⟨4454321, by rfl⟩ : syracuseStep 5939095 = 8908643) B8908643
theorem B7918793 : Blo 2085435 7918793 := bstep (se 2 (by rfl) ⟨2969547, by rfl⟩ : syracuseStep 7918793 = 5939095) B5939095
theorem B5279195 : Blo 2085435 5279195 := bstep (se 1 (by rfl) ⟨3959396, by rfl⟩ : syracuseStep 5279195 = 7918793) B7918793
theorem B3519463 : Blo 2085435 3519463 := bstep (se 1 (by rfl) ⟨2639597, by rfl⟩ : syracuseStep 3519463 = 5279195) B5279195
theorem B4692617 : Blo 2085435 4692617 := bstep (se 2 (by rfl) ⟨1759731, by rfl⟩ : syracuseStep 4692617 = 3519463) B3519463
theorem B3128411 : Blo 2085435 3128411 := bstep (se 1 (by rfl) ⟨2346308, by rfl⟩ : syracuseStep 3128411 = 4692617) B4692617
theorem B2085607 : Blo 2085435 2085607 := bstep (se 1 (by rfl) ⟨1564205, by rfl⟩ : syracuseStep 2085607 = 3128411) B3128411
theorem B2346313 : Blo 2085435 2346313 := bbase (se 2 (by rfl) ⟨879867, by rfl⟩ : syracuseStep 2346313 = 1759735) (by norm_num)
theorem B3128417 : Blo 2085435 3128417 := bstep (se 2 (by rfl) ⟨1173156, by rfl⟩ : syracuseStep 3128417 = 2346313) B2346313
theorem B2085611 : Blo 2085435 2085611 := bstep (se 1 (by rfl) ⟨1564208, by rfl⟩ : syracuseStep 2085611 = 3128417) B3128417
theorem B2574401 : Blo 2085435 2574401 := bbase (se 2 (by rfl) ⟨965400, by rfl⟩ : syracuseStep 2574401 = 1930801) (by norm_num)
theorem B6865069 : Blo 2085435 6865069 := bstep (se 3 (by rfl) ⟨1287200, by rfl⟩ : syracuseStep 6865069 = 2574401) B2574401
theorem B9153425 : Blo 2085435 9153425 := bstep (se 2 (by rfl) ⟨3432534, by rfl⟩ : syracuseStep 9153425 = 6865069) B6865069
theorem B24409133 : Blo 2085435 24409133 := bstep (se 3 (by rfl) ⟨4576712, by rfl⟩ : syracuseStep 24409133 = 9153425) B9153425
theorem B16272755 : Blo 2085435 16272755 := bstep (se 1 (by rfl) ⟨12204566, by rfl⟩ : syracuseStep 16272755 = 24409133) B24409133
theorem B10848503 : Blo 2085435 10848503 := bstep (se 1 (by rfl) ⟨8136377, by rfl⟩ : syracuseStep 10848503 = 16272755) B16272755
theorem B7232335 : Blo 2085435 7232335 := bstep (se 1 (by rfl) ⟨5424251, by rfl⟩ : syracuseStep 7232335 = 10848503) B10848503
theorem B38572453 : Blo 2085435 38572453 := bstep (se 4 (by rfl) ⟨3616167, by rfl⟩ : syracuseStep 38572453 = 7232335) B7232335
theorem B51429937 : Blo 2085435 51429937 := bstep (se 2 (by rfl) ⟨19286226, by rfl⟩ : syracuseStep 51429937 = 38572453) B38572453
theorem B68573249 : Blo 2085435 68573249 := bstep (se 2 (by rfl) ⟨25714968, by rfl⟩ : syracuseStep 68573249 = 51429937) B51429937
theorem B45715499 : Blo 2085435 45715499 := bstep (se 1 (by rfl) ⟨34286624, by rfl⟩ : syracuseStep 45715499 = 68573249) B68573249
theorem B30476999 : Blo 2085435 30476999 := bstep (se 1 (by rfl) ⟨22857749, by rfl⟩ : syracuseStep 30476999 = 45715499) B45715499
theorem B81271997 : Blo 2085435 81271997 := bstep (se 3 (by rfl) ⟨15238499, by rfl⟩ : syracuseStep 81271997 = 30476999) B30476999
theorem B54181331 : Blo 2085435 54181331 := bstep (se 1 (by rfl) ⟨40635998, by rfl⟩ : syracuseStep 54181331 = 81271997) B81271997
theorem B36120887 : Blo 2085435 36120887 := bstep (se 1 (by rfl) ⟨27090665, by rfl⟩ : syracuseStep 36120887 = 54181331) B54181331
theorem B24080591 : Blo 2085435 24080591 := bstep (se 1 (by rfl) ⟨18060443, by rfl⟩ : syracuseStep 24080591 = 36120887) B36120887
theorem B16053727 : Blo 2085435 16053727 := bstep (se 1 (by rfl) ⟨12040295, by rfl⟩ : syracuseStep 16053727 = 24080591) B24080591
theorem B21404969 : Blo 2085435 21404969 := bstep (se 2 (by rfl) ⟨8026863, by rfl⟩ : syracuseStep 21404969 = 16053727) B16053727
theorem B14269979 : Blo 2085435 14269979 := bstep (se 1 (by rfl) ⟨10702484, by rfl⟩ : syracuseStep 14269979 = 21404969) B21404969
theorem B38053277 : Blo 2085435 38053277 := bstep (se 3 (by rfl) ⟨7134989, by rfl⟩ : syracuseStep 38053277 = 14269979) B14269979
theorem B25368851 : Blo 2085435 25368851 := bstep (se 1 (by rfl) ⟨19026638, by rfl⟩ : syracuseStep 25368851 = 38053277) B38053277
theorem B16912567 : Blo 2085435 16912567 := bstep (se 1 (by rfl) ⟨12684425, by rfl⟩ : syracuseStep 16912567 = 25368851) B25368851
theorem B22550089 : Blo 2085435 22550089 := bstep (se 2 (by rfl) ⟨8456283, by rfl⟩ : syracuseStep 22550089 = 16912567) B16912567
theorem B30066785 : Blo 2085435 30066785 := bstep (se 2 (by rfl) ⟨11275044, by rfl⟩ : syracuseStep 30066785 = 22550089) B22550089
theorem B20044523 : Blo 2085435 20044523 := bstep (se 1 (by rfl) ⟨15033392, by rfl⟩ : syracuseStep 20044523 = 30066785) B30066785
theorem B13363015 : Blo 2085435 13363015 := bstep (se 1 (by rfl) ⟨10022261, by rfl⟩ : syracuseStep 13363015 = 20044523) B20044523
theorem B17817353 : Blo 2085435 17817353 := bstep (se 2 (by rfl) ⟨6681507, by rfl⟩ : syracuseStep 17817353 = 13363015) B13363015
theorem B11878235 : Blo 2085435 11878235 := bstep (se 1 (by rfl) ⟨8908676, by rfl⟩ : syracuseStep 11878235 = 17817353) B17817353
theorem B7918823 : Blo 2085435 7918823 := bstep (se 1 (by rfl) ⟨5939117, by rfl⟩ : syracuseStep 7918823 = 11878235) B11878235
theorem B5279215 : Blo 2085435 5279215 := bstep (se 1 (by rfl) ⟨3959411, by rfl⟩ : syracuseStep 5279215 = 7918823) B7918823
theorem B7038953 : Blo 2085435 7038953 := bstep (se 2 (by rfl) ⟨2639607, by rfl⟩ : syracuseStep 7038953 = 5279215) B5279215
theorem B4692635 : Blo 2085435 4692635 := bstep (se 1 (by rfl) ⟨3519476, by rfl⟩ : syracuseStep 4692635 = 7038953) B7038953
theorem B3128423 : Blo 2085435 3128423 := bstep (se 1 (by rfl) ⟨2346317, by rfl⟩ : syracuseStep 3128423 = 4692635) B4692635
theorem B2085615 : Blo 2085435 2085615 := bstep (se 1 (by rfl) ⟨1564211, by rfl⟩ : syracuseStep 2085615 = 3128423) B3128423
theorem B3128429 : Blo 2085435 3128429 := bbase (se 3 (by rfl) ⟨586580, by rfl⟩ : syracuseStep 3128429 = 1173161) (by norm_num)
theorem B2085619 : Blo 2085435 2085619 := bstep (se 1 (by rfl) ⟨1564214, by rfl⟩ : syracuseStep 2085619 = 3128429) B3128429
theorem B4692653 : Blo 2085435 4692653 := bbase (se 3 (by rfl) ⟨879872, by rfl⟩ : syracuseStep 4692653 = 1759745) (by norm_num)
theorem B3128435 : Blo 2085435 3128435 := bstep (se 1 (by rfl) ⟨2346326, by rfl⟩ : syracuseStep 3128435 = 4692653) B4692653
theorem B2085623 : Blo 2085435 2085623 := bstep (se 1 (by rfl) ⟨1564217, by rfl⟩ : syracuseStep 2085623 = 3128435) B3128435
theorem B4454365 : Blo 2085435 4454365 := bbase (se 3 (by rfl) ⟨835193, by rfl⟩ : syracuseStep 4454365 = 1670387) (by norm_num)
theorem B5939153 : Blo 2085435 5939153 := bstep (se 2 (by rfl) ⟨2227182, by rfl⟩ : syracuseStep 5939153 = 4454365) B4454365
theorem B3959435 : Blo 2085435 3959435 := bstep (se 1 (by rfl) ⟨2969576, by rfl⟩ : syracuseStep 3959435 = 5939153) B5939153
theorem B2639623 : Blo 2085435 2639623 := bstep (se 1 (by rfl) ⟨1979717, by rfl⟩ : syracuseStep 2639623 = 3959435) B3959435
theorem B3519497 : Blo 2085435 3519497 := bstep (se 2 (by rfl) ⟨1319811, by rfl⟩ : syracuseStep 3519497 = 2639623) B2639623
theorem B2346331 : Blo 2085435 2346331 := bstep (se 1 (by rfl) ⟨1759748, by rfl⟩ : syracuseStep 2346331 = 3519497) B3519497
theorem B3128441 : Blo 2085435 3128441 := bstep (se 2 (by rfl) ⟨1173165, by rfl⟩ : syracuseStep 3128441 = 2346331) B2346331
theorem B2085627 : Blo 2085435 2085627 := bstep (se 1 (by rfl) ⟨1564220, by rfl⟩ : syracuseStep 2085627 = 3128441) B3128441
theorem B5351285 : Blo 2085435 5351285 := bbase (se 5 (by rfl) ⟨250841, by rfl⟩ : syracuseStep 5351285 = 501683) (by norm_num)
theorem B3567523 : Blo 2085435 3567523 := bstep (se 1 (by rfl) ⟨2675642, by rfl⟩ : syracuseStep 3567523 = 5351285) B5351285
theorem B4756697 : Blo 2085435 4756697 := bstep (se 2 (by rfl) ⟨1783761, by rfl⟩ : syracuseStep 4756697 = 3567523) B3567523
theorem B3171131 : Blo 2085435 3171131 := bstep (se 1 (by rfl) ⟨2378348, by rfl⟩ : syracuseStep 3171131 = 4756697) B4756697
theorem B2114087 : Blo 2085435 2114087 := bstep (se 1 (by rfl) ⟨1585565, by rfl⟩ : syracuseStep 2114087 = 3171131) B3171131
theorem B5637565 : Blo 2085435 5637565 := bstep (se 3 (by rfl) ⟨1057043, by rfl⟩ : syracuseStep 5637565 = 2114087) B2114087
theorem B30067013 : Blo 2085435 30067013 := bstep (se 4 (by rfl) ⟨2818782, by rfl⟩ : syracuseStep 30067013 = 5637565) B5637565
theorem B20044675 : Blo 2085435 20044675 := bstep (se 1 (by rfl) ⟨15033506, by rfl⟩ : syracuseStep 20044675 = 30067013) B30067013
theorem B26726233 : Blo 2085435 26726233 := bstep (se 2 (by rfl) ⟨10022337, by rfl⟩ : syracuseStep 26726233 = 20044675) B20044675
theorem B35634977 : Blo 2085435 35634977 := bstep (se 2 (by rfl) ⟨13363116, by rfl⟩ : syracuseStep 35634977 = 26726233) B26726233
theorem B23756651 : Blo 2085435 23756651 := bstep (se 1 (by rfl) ⟨17817488, by rfl⟩ : syracuseStep 23756651 = 35634977) B35634977
theorem B15837767 : Blo 2085435 15837767 := bstep (se 1 (by rfl) ⟨11878325, by rfl⟩ : syracuseStep 15837767 = 23756651) B23756651
theorem B10558511 : Blo 2085435 10558511 := bstep (se 1 (by rfl) ⟨7918883, by rfl⟩ : syracuseStep 10558511 = 15837767) B15837767
theorem B7039007 : Blo 2085435 7039007 := bstep (se 1 (by rfl) ⟨5279255, by rfl⟩ : syracuseStep 7039007 = 10558511) B10558511
theorem B4692671 : Blo 2085435 4692671 := bstep (se 1 (by rfl) ⟨3519503, by rfl⟩ : syracuseStep 4692671 = 7039007) B7039007
theorem B3128447 : Blo 2085435 3128447 := bstep (se 1 (by rfl) ⟨2346335, by rfl⟩ : syracuseStep 3128447 = 4692671) B4692671
theorem B2085631 : Blo 2085435 2085631 := bstep (se 1 (by rfl) ⟨1564223, by rfl⟩ : syracuseStep 2085631 = 3128447) B3128447
theorem B3128453 : Blo 2085435 3128453 := bbase (se 4 (by rfl) ⟨293292, by rfl⟩ : syracuseStep 3128453 = 586585) (by norm_num)
theorem B2085635 : Blo 2085435 2085635 := bstep (se 1 (by rfl) ⟨1564226, by rfl⟩ : syracuseStep 2085635 = 3128453) B3128453
theorem B3519517 : Blo 2085435 3519517 := bbase (se 3 (by rfl) ⟨659909, by rfl⟩ : syracuseStep 3519517 = 1319819) (by norm_num)
theorem B4692689 : Blo 2085435 4692689 := bstep (se 2 (by rfl) ⟨1759758, by rfl⟩ : syracuseStep 4692689 = 3519517) B3519517
theorem B3128459 : Blo 2085435 3128459 := bstep (se 1 (by rfl) ⟨2346344, by rfl⟩ : syracuseStep 3128459 = 4692689) B4692689
theorem B2085639 : Blo 2085435 2085639 := bstep (se 1 (by rfl) ⟨1564229, by rfl⟩ : syracuseStep 2085639 = 3128459) B3128459
theorem B2346349 : Blo 2085435 2346349 := bbase (se 3 (by rfl) ⟨439940, by rfl⟩ : syracuseStep 2346349 = 879881) (by norm_num)
theorem B3128465 : Blo 2085435 3128465 := bstep (se 2 (by rfl) ⟨1173174, by rfl⟩ : syracuseStep 3128465 = 2346349) B2346349
theorem B2085643 : Blo 2085435 2085643 := bstep (se 1 (by rfl) ⟨1564232, by rfl⟩ : syracuseStep 2085643 = 3128465) B3128465
theorem B7039061 : Blo 2085435 7039061 := bbase (se 8 (by rfl) ⟨41244, by rfl⟩ : syracuseStep 7039061 = 82489) (by norm_num)
theorem B4692707 : Blo 2085435 4692707 := bstep (se 1 (by rfl) ⟨3519530, by rfl⟩ : syracuseStep 4692707 = 7039061) B7039061
theorem B3128471 : Blo 2085435 3128471 := bstep (se 1 (by rfl) ⟨2346353, by rfl⟩ : syracuseStep 3128471 = 4692707) B4692707
theorem B2085647 : Blo 2085435 2085647 := bstep (se 1 (by rfl) ⟨1564235, by rfl⟩ : syracuseStep 2085647 = 3128471) B3128471
theorem B3128477 : Blo 2085435 3128477 := bbase (se 3 (by rfl) ⟨586589, by rfl⟩ : syracuseStep 3128477 = 1173179) (by norm_num)
theorem B2085651 : Blo 2085435 2085651 := bstep (se 1 (by rfl) ⟨1564238, by rfl⟩ : syracuseStep 2085651 = 3128477) B3128477
theorem B4692725 : Blo 2085435 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B3128483 : Blo 2085435 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B2085655 : Blo 2085435 2085655 := bstep (se 1 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 2085655 = 3128483) B3128483
theorem B5011237 : Blo 2085435 5011237 := bbase (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) (by norm_num)
theorem B26726597 : Blo 2085435 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B17817731 : Blo 2085435 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B11878487 : Blo 2085435 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B7918991 : Blo 2085435 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B5279327 : Blo 2085435 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B3519551 : Blo 2085435 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B2346367 : Blo 2085435 2346367 := bstep (se 1 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 2346367 = 3519551) B3519551
theorem B3128489 : Blo 2085435 3128489 := bstep (se 2 (by rfl) ⟨1173183, by rfl⟩ : syracuseStep 3128489 = 2346367) B2346367
theorem B2085659 : Blo 2085435 2085659 := bstep (se 1 (by rfl) ⟨1564244, by rfl⟩ : syracuseStep 2085659 = 3128489) B3128489
theorem B9513541 : Blo 2085435 9513541 := bbase (se 4 (by rfl) ⟨891894, by rfl⟩ : syracuseStep 9513541 = 1783789) (by norm_num)
theorem B12684721 : Blo 2085435 12684721 := bstep (se 2 (by rfl) ⟨4756770, by rfl⟩ : syracuseStep 12684721 = 9513541) B9513541
theorem B16912961 : Blo 2085435 16912961 := bstep (se 2 (by rfl) ⟨6342360, by rfl⟩ : syracuseStep 16912961 = 12684721) B12684721
theorem B11275307 : Blo 2085435 11275307 := bstep (se 1 (by rfl) ⟨8456480, by rfl⟩ : syracuseStep 11275307 = 16912961) B16912961
theorem B7516871 : Blo 2085435 7516871 := bstep (se 1 (by rfl) ⟨5637653, by rfl⟩ : syracuseStep 7516871 = 11275307) B11275307
theorem B5011247 : Blo 2085435 5011247 := bstep (se 1 (by rfl) ⟨3758435, by rfl⟩ : syracuseStep 5011247 = 7516871) B7516871
theorem B3340831 : Blo 2085435 3340831 := bstep (se 1 (by rfl) ⟨2505623, by rfl⟩ : syracuseStep 3340831 = 5011247) B5011247
theorem B4454441 : Blo 2085435 4454441 := bstep (se 2 (by rfl) ⟨1670415, by rfl⟩ : syracuseStep 4454441 = 3340831) B3340831
theorem B2969627 : Blo 2085435 2969627 := bstep (se 1 (by rfl) ⟨2227220, by rfl⟩ : syracuseStep 2969627 = 4454441) B4454441
theorem B7919005 : Blo 2085435 7919005 := bstep (se 3 (by rfl) ⟨1484813, by rfl⟩ : syracuseStep 7919005 = 2969627) B2969627
theorem B10558673 : Blo 2085435 10558673 := bstep (se 2 (by rfl) ⟨3959502, by rfl⟩ : syracuseStep 10558673 = 7919005) B7919005
theorem B7039115 : Blo 2085435 7039115 := bstep (se 1 (by rfl) ⟨5279336, by rfl⟩ : syracuseStep 7039115 = 10558673) B10558673
theorem B4692743 : Blo 2085435 4692743 := bstep (se 1 (by rfl) ⟨3519557, by rfl⟩ : syracuseStep 4692743 = 7039115) B7039115
theorem B3128495 : Blo 2085435 3128495 := bstep (se 1 (by rfl) ⟨2346371, by rfl⟩ : syracuseStep 3128495 = 4692743) B4692743
theorem B2085663 : Blo 2085435 2085663 := bstep (se 1 (by rfl) ⟨1564247, by rfl⟩ : syracuseStep 2085663 = 3128495) B3128495
theorem B3128501 : Blo 2085435 3128501 := bbase (se 5 (by rfl) ⟨146648, by rfl⟩ : syracuseStep 3128501 = 293297) (by norm_num)
theorem B2085667 : Blo 2085435 2085667 := bstep (se 1 (by rfl) ⟨1564250, by rfl⟩ : syracuseStep 2085667 = 3128501) B3128501
theorem B5279357 : Blo 2085435 5279357 := bbase (se 3 (by rfl) ⟨989879, by rfl⟩ : syracuseStep 5279357 = 1979759) (by norm_num)
theorem B3519571 : Blo 2085435 3519571 := bstep (se 1 (by rfl) ⟨2639678, by rfl⟩ : syracuseStep 3519571 = 5279357) B5279357
theorem B4692761 : Blo 2085435 4692761 := bstep (se 2 (by rfl) ⟨1759785, by rfl⟩ : syracuseStep 4692761 = 3519571) B3519571
theorem B3128507 : Blo 2085435 3128507 := bstep (se 1 (by rfl) ⟨2346380, by rfl⟩ : syracuseStep 3128507 = 4692761) B4692761
theorem B2085671 : Blo 2085435 2085671 := bstep (se 1 (by rfl) ⟨1564253, by rfl⟩ : syracuseStep 2085671 = 3128507) B3128507
theorem B2346385 : Blo 2085435 2346385 := bbase (se 2 (by rfl) ⟨879894, by rfl⟩ : syracuseStep 2346385 = 1759789) (by norm_num)
theorem B3128513 : Blo 2085435 3128513 := bstep (se 2 (by rfl) ⟨1173192, by rfl⟩ : syracuseStep 3128513 = 2346385) B2346385
theorem B2085675 : Blo 2085435 2085675 := bstep (se 1 (by rfl) ⟨1564256, by rfl⟩ : syracuseStep 2085675 = 3128513) B3128513
theorem B3959533 : Blo 2085435 3959533 := bbase (se 3 (by rfl) ⟨742412, by rfl⟩ : syracuseStep 3959533 = 1484825) (by norm_num)
theorem B5279377 : Blo 2085435 5279377 := bstep (se 2 (by rfl) ⟨1979766, by rfl⟩ : syracuseStep 5279377 = 3959533) B3959533
theorem B7039169 : Blo 2085435 7039169 := bstep (se 2 (by rfl) ⟨2639688, by rfl⟩ : syracuseStep 7039169 = 5279377) B5279377
theorem B4692779 : Blo 2085435 4692779 := bstep (se 1 (by rfl) ⟨3519584, by rfl⟩ : syracuseStep 4692779 = 7039169) B7039169
theorem B3128519 : Blo 2085435 3128519 := bstep (se 1 (by rfl) ⟨2346389, by rfl⟩ : syracuseStep 3128519 = 4692779) B4692779
theorem B2085679 : Blo 2085435 2085679 := bstep (se 1 (by rfl) ⟨1564259, by rfl⟩ : syracuseStep 2085679 = 3128519) B3128519
theorem B3128525 : Blo 2085435 3128525 := bbase (se 3 (by rfl) ⟨586598, by rfl⟩ : syracuseStep 3128525 = 1173197) (by norm_num)
theorem B2085683 : Blo 2085435 2085683 := bstep (se 1 (by rfl) ⟨1564262, by rfl⟩ : syracuseStep 2085683 = 3128525) B3128525
theorem B4692797 : Blo 2085435 4692797 := bbase (se 3 (by rfl) ⟨879899, by rfl⟩ : syracuseStep 4692797 = 1759799) (by norm_num)
theorem B3128531 : Blo 2085435 3128531 := bstep (se 1 (by rfl) ⟨2346398, by rfl⟩ : syracuseStep 3128531 = 4692797) B4692797
theorem B2085687 : Blo 2085435 2085687 := bstep (se 1 (by rfl) ⟨1564265, by rfl⟩ : syracuseStep 2085687 = 3128531) B3128531
theorem B3519605 : Blo 2085435 3519605 := bbase (se 5 (by rfl) ⟨164981, by rfl⟩ : syracuseStep 3519605 = 329963) (by norm_num)
theorem B2346403 : Blo 2085435 2346403 := bstep (se 1 (by rfl) ⟨1759802, by rfl⟩ : syracuseStep 2346403 = 3519605) B3519605
theorem B3128537 : Blo 2085435 3128537 := bstep (se 2 (by rfl) ⟨1173201, by rfl⟩ : syracuseStep 3128537 = 2346403) B2346403
theorem B2085691 : Blo 2085435 2085691 := bstep (se 1 (by rfl) ⟨1564268, by rfl⟩ : syracuseStep 2085691 = 3128537) B3128537
theorem B4454509 : Blo 2085435 4454509 := bbase (se 3 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 4454509 = 1670441) (by norm_num)
theorem B5939345 : Blo 2085435 5939345 := bstep (se 2 (by rfl) ⟨2227254, by rfl⟩ : syracuseStep 5939345 = 4454509) B4454509
theorem B15838253 : Blo 2085435 15838253 := bstep (se 3 (by rfl) ⟨2969672, by rfl⟩ : syracuseStep 15838253 = 5939345) B5939345
theorem B10558835 : Blo 2085435 10558835 := bstep (se 1 (by rfl) ⟨7919126, by rfl⟩ : syracuseStep 10558835 = 15838253) B15838253
theorem B7039223 : Blo 2085435 7039223 := bstep (se 1 (by rfl) ⟨5279417, by rfl⟩ : syracuseStep 7039223 = 10558835) B10558835
theorem B4692815 : Blo 2085435 4692815 := bstep (se 1 (by rfl) ⟨3519611, by rfl⟩ : syracuseStep 4692815 = 7039223) B7039223
theorem B3128543 : Blo 2085435 3128543 := bstep (se 1 (by rfl) ⟨2346407, by rfl⟩ : syracuseStep 3128543 = 4692815) B4692815
theorem B2085695 : Blo 2085435 2085695 := bstep (se 1 (by rfl) ⟨1564271, by rfl⟩ : syracuseStep 2085695 = 3128543) B3128543
theorem B3128549 : Blo 2085435 3128549 := bbase (se 4 (by rfl) ⟨293301, by rfl⟩ : syracuseStep 3128549 = 586603) (by norm_num)
theorem B2085699 : Blo 2085435 2085699 := bstep (se 1 (by rfl) ⟨1564274, by rfl⟩ : syracuseStep 2085699 = 3128549) B3128549
theorem B5149021 : Blo 2085435 5149021 := bbase (se 3 (by rfl) ⟨965441, by rfl⟩ : syracuseStep 5149021 = 1930883) (by norm_num)
theorem B6865361 : Blo 2085435 6865361 := bstep (se 2 (by rfl) ⟨2574510, by rfl⟩ : syracuseStep 6865361 = 5149021) B5149021
theorem B4576907 : Blo 2085435 4576907 := bstep (se 1 (by rfl) ⟨3432680, by rfl⟩ : syracuseStep 4576907 = 6865361) B6865361
theorem B12205085 : Blo 2085435 12205085 := bstep (se 3 (by rfl) ⟨2288453, by rfl⟩ : syracuseStep 12205085 = 4576907) B4576907
theorem B32546893 : Blo 2085435 32546893 := bstep (se 3 (by rfl) ⟨6102542, by rfl⟩ : syracuseStep 32546893 = 12205085) B12205085
theorem B43395857 : Blo 2085435 43395857 := bstep (se 2 (by rfl) ⟨16273446, by rfl⟩ : syracuseStep 43395857 = 32546893) B32546893
theorem B28930571 : Blo 2085435 28930571 := bstep (se 1 (by rfl) ⟨21697928, by rfl⟩ : syracuseStep 28930571 = 43395857) B43395857
theorem B19287047 : Blo 2085435 19287047 := bstep (se 1 (by rfl) ⟨14465285, by rfl⟩ : syracuseStep 19287047 = 28930571) B28930571
theorem B12858031 : Blo 2085435 12858031 := bstep (se 1 (by rfl) ⟨9643523, by rfl⟩ : syracuseStep 12858031 = 19287047) B19287047
theorem B68576165 : Blo 2085435 68576165 := bstep (se 4 (by rfl) ⟨6429015, by rfl⟩ : syracuseStep 68576165 = 12858031) B12858031
theorem B45717443 : Blo 2085435 45717443 := bstep (se 1 (by rfl) ⟨34288082, by rfl⟩ : syracuseStep 45717443 = 68576165) B68576165
theorem B30478295 : Blo 2085435 30478295 := bstep (se 1 (by rfl) ⟨22858721, by rfl⟩ : syracuseStep 30478295 = 45717443) B45717443
theorem B20318863 : Blo 2085435 20318863 := bstep (se 1 (by rfl) ⟨15239147, by rfl⟩ : syracuseStep 20318863 = 30478295) B30478295
theorem B27091817 : Blo 2085435 27091817 := bstep (se 2 (by rfl) ⟨10159431, by rfl⟩ : syracuseStep 27091817 = 20318863) B20318863
theorem B18061211 : Blo 2085435 18061211 := bstep (se 1 (by rfl) ⟨13545908, by rfl⟩ : syracuseStep 18061211 = 27091817) B27091817
theorem B12040807 : Blo 2085435 12040807 := bstep (se 1 (by rfl) ⟨9030605, by rfl⟩ : syracuseStep 12040807 = 18061211) B18061211
theorem B16054409 : Blo 2085435 16054409 := bstep (se 2 (by rfl) ⟨6020403, by rfl⟩ : syracuseStep 16054409 = 12040807) B12040807
theorem B10702939 : Blo 2085435 10702939 := bstep (se 1 (by rfl) ⟨8027204, by rfl⟩ : syracuseStep 10702939 = 16054409) B16054409
theorem B14270585 : Blo 2085435 14270585 := bstep (se 2 (by rfl) ⟨5351469, by rfl⟩ : syracuseStep 14270585 = 10702939) B10702939
theorem B38054893 : Blo 2085435 38054893 := bstep (se 3 (by rfl) ⟨7135292, by rfl⟩ : syracuseStep 38054893 = 14270585) B14270585
theorem B50739857 : Blo 2085435 50739857 := bstep (se 2 (by rfl) ⟨19027446, by rfl⟩ : syracuseStep 50739857 = 38054893) B38054893
theorem B33826571 : Blo 2085435 33826571 := bstep (se 1 (by rfl) ⟨25369928, by rfl⟩ : syracuseStep 33826571 = 50739857) B50739857
theorem B22551047 : Blo 2085435 22551047 := bstep (se 1 (by rfl) ⟨16913285, by rfl⟩ : syracuseStep 22551047 = 33826571) B33826571
theorem B15034031 : Blo 2085435 15034031 := bstep (se 1 (by rfl) ⟨11275523, by rfl⟩ : syracuseStep 15034031 = 22551047) B22551047
theorem B10022687 : Blo 2085435 10022687 := bstep (se 1 (by rfl) ⟨7517015, by rfl⟩ : syracuseStep 10022687 = 15034031) B15034031
theorem B6681791 : Blo 2085435 6681791 := bstep (se 1 (by rfl) ⟨5011343, by rfl⟩ : syracuseStep 6681791 = 10022687) B10022687
theorem B4454527 : Blo 2085435 4454527 := bstep (se 1 (by rfl) ⟨3340895, by rfl⟩ : syracuseStep 4454527 = 6681791) B6681791
theorem B5939369 : Blo 2085435 5939369 := bstep (se 2 (by rfl) ⟨2227263, by rfl⟩ : syracuseStep 5939369 = 4454527) B4454527
theorem B3959579 : Blo 2085435 3959579 := bstep (se 1 (by rfl) ⟨2969684, by rfl⟩ : syracuseStep 3959579 = 5939369) B5939369
theorem B2639719 : Blo 2085435 2639719 := bstep (se 1 (by rfl) ⟨1979789, by rfl⟩ : syracuseStep 2639719 = 3959579) B3959579
theorem B3519625 : Blo 2085435 3519625 := bstep (se 2 (by rfl) ⟨1319859, by rfl⟩ : syracuseStep 3519625 = 2639719) B2639719
theorem B4692833 : Blo 2085435 4692833 := bstep (se 2 (by rfl) ⟨1759812, by rfl⟩ : syracuseStep 4692833 = 3519625) B3519625
theorem B3128555 : Blo 2085435 3128555 := bstep (se 1 (by rfl) ⟨2346416, by rfl⟩ : syracuseStep 3128555 = 4692833) B4692833
theorem B2085703 : Blo 2085435 2085703 := bstep (se 1 (by rfl) ⟨1564277, by rfl⟩ : syracuseStep 2085703 = 3128555) B3128555
theorem B2346421 : Blo 2085435 2346421 := bbase (se 5 (by rfl) ⟨109988, by rfl⟩ : syracuseStep 2346421 = 219977) (by norm_num)
theorem B3128561 : Blo 2085435 3128561 := bstep (se 2 (by rfl) ⟨1173210, by rfl⟩ : syracuseStep 3128561 = 2346421) B2346421
theorem B2085707 : Blo 2085435 2085707 := bstep (se 1 (by rfl) ⟨1564280, by rfl⟩ : syracuseStep 2085707 = 3128561) B3128561
theorem B2639729 : Blo 2085435 2639729 := bbase (se 2 (by rfl) ⟨989898, by rfl⟩ : syracuseStep 2639729 = 1979797) (by norm_num)
theorem B7039277 : Blo 2085435 7039277 := bstep (se 3 (by rfl) ⟨1319864, by rfl⟩ : syracuseStep 7039277 = 2639729) B2639729
theorem B4692851 : Blo 2085435 4692851 := bstep (se 1 (by rfl) ⟨3519638, by rfl⟩ : syracuseStep 4692851 = 7039277) B7039277
theorem B3128567 : Blo 2085435 3128567 := bstep (se 1 (by rfl) ⟨2346425, by rfl⟩ : syracuseStep 3128567 = 4692851) B4692851
theorem B2085711 : Blo 2085435 2085711 := bstep (se 1 (by rfl) ⟨1564283, by rfl⟩ : syracuseStep 2085711 = 3128567) B3128567
theorem B3128573 : Blo 2085435 3128573 := bbase (se 3 (by rfl) ⟨586607, by rfl⟩ : syracuseStep 3128573 = 1173215) (by norm_num)
theorem B2085715 : Blo 2085435 2085715 := bstep (se 1 (by rfl) ⟨1564286, by rfl⟩ : syracuseStep 2085715 = 3128573) B3128573
theorem B4692869 : Blo 2085435 4692869 := bbase (se 4 (by rfl) ⟨439956, by rfl⟩ : syracuseStep 4692869 = 879913) (by norm_num)
theorem B3128579 : Blo 2085435 3128579 := bstep (se 1 (by rfl) ⟨2346434, by rfl⟩ : syracuseStep 3128579 = 4692869) B4692869
theorem B2085719 : Blo 2085435 2085719 := bstep (se 1 (by rfl) ⟨1564289, by rfl⟩ : syracuseStep 2085719 = 3128579) B3128579
theorem B2227285 : Blo 2085435 2227285 := bbase (se 8 (by rfl) ⟨13050, by rfl⟩ : syracuseStep 2227285 = 26101) (by norm_num)
theorem B2969713 : Blo 2085435 2969713 := bstep (se 2 (by rfl) ⟨1113642, by rfl⟩ : syracuseStep 2969713 = 2227285) B2227285
theorem B3959617 : Blo 2085435 3959617 := bstep (se 2 (by rfl) ⟨1484856, by rfl⟩ : syracuseStep 3959617 = 2969713) B2969713
theorem B5279489 : Blo 2085435 5279489 := bstep (se 2 (by rfl) ⟨1979808, by rfl⟩ : syracuseStep 5279489 = 3959617) B3959617
theorem B3519659 : Blo 2085435 3519659 := bstep (se 1 (by rfl) ⟨2639744, by rfl⟩ : syracuseStep 3519659 = 5279489) B5279489
theorem B2346439 : Blo 2085435 2346439 := bstep (se 1 (by rfl) ⟨1759829, by rfl⟩ : syracuseStep 2346439 = 3519659) B3519659
theorem B3128585 : Blo 2085435 3128585 := bstep (se 2 (by rfl) ⟨1173219, by rfl⟩ : syracuseStep 3128585 = 2346439) B2346439
theorem B2085723 : Blo 2085435 2085723 := bstep (se 1 (by rfl) ⟨1564292, by rfl⟩ : syracuseStep 2085723 = 3128585) B3128585
theorem B10558997 : Blo 2085435 10558997 := bbase (se 6 (by rfl) ⟨247476, by rfl⟩ : syracuseStep 10558997 = 494953) (by norm_num)
theorem B7039331 : Blo 2085435 7039331 := bstep (se 1 (by rfl) ⟨5279498, by rfl⟩ : syracuseStep 7039331 = 10558997) B10558997
theorem B4692887 : Blo 2085435 4692887 := bstep (se 1 (by rfl) ⟨3519665, by rfl⟩ : syracuseStep 4692887 = 7039331) B7039331
theorem B3128591 : Blo 2085435 3128591 := bstep (se 1 (by rfl) ⟨2346443, by rfl⟩ : syracuseStep 3128591 = 4692887) B4692887
theorem B2085727 : Blo 2085435 2085727 := bstep (se 1 (by rfl) ⟨1564295, by rfl⟩ : syracuseStep 2085727 = 3128591) B3128591
theorem B3128597 : Blo 2085435 3128597 := bbase (se 6 (by rfl) ⟨73326, by rfl⟩ : syracuseStep 3128597 = 146653) (by norm_num)
theorem B2085731 : Blo 2085435 2085731 := bstep (se 1 (by rfl) ⟨1564298, by rfl⟩ : syracuseStep 2085731 = 3128597) B3128597
theorem B3567701 : Blo 2085435 3567701 := bbase (se 8 (by rfl) ⟨20904, by rfl⟩ : syracuseStep 3567701 = 41809) (by norm_num)
theorem B2378467 : Blo 2085435 2378467 := bstep (se 1 (by rfl) ⟨1783850, by rfl⟩ : syracuseStep 2378467 = 3567701) B3567701
theorem B12685157 : Blo 2085435 12685157 := bstep (se 4 (by rfl) ⟨1189233, by rfl⟩ : syracuseStep 12685157 = 2378467) B2378467
theorem B8456771 : Blo 2085435 8456771 := bstep (se 1 (by rfl) ⟨6342578, by rfl⟩ : syracuseStep 8456771 = 12685157) B12685157
theorem B5637847 : Blo 2085435 5637847 := bstep (se 1 (by rfl) ⟨4228385, by rfl⟩ : syracuseStep 5637847 = 8456771) B8456771
theorem B7517129 : Blo 2085435 7517129 := bstep (se 2 (by rfl) ⟨2818923, by rfl⟩ : syracuseStep 7517129 = 5637847) B5637847
theorem B20045677 : Blo 2085435 20045677 := bstep (se 3 (by rfl) ⟨3758564, by rfl⟩ : syracuseStep 20045677 = 7517129) B7517129
theorem B26727569 : Blo 2085435 26727569 := bstep (se 2 (by rfl) ⟨10022838, by rfl⟩ : syracuseStep 26727569 = 20045677) B20045677
theorem B17818379 : Blo 2085435 17818379 := bstep (se 1 (by rfl) ⟨13363784, by rfl⟩ : syracuseStep 17818379 = 26727569) B26727569
theorem B11878919 : Blo 2085435 11878919 := bstep (se 1 (by rfl) ⟨8909189, by rfl⟩ : syracuseStep 11878919 = 17818379) B17818379
theorem B7919279 : Blo 2085435 7919279 := bstep (se 1 (by rfl) ⟨5939459, by rfl⟩ : syracuseStep 7919279 = 11878919) B11878919
theorem B5279519 : Blo 2085435 5279519 := bstep (se 1 (by rfl) ⟨3959639, by rfl⟩ : syracuseStep 5279519 = 7919279) B7919279
theorem B3519679 : Blo 2085435 3519679 := bstep (se 1 (by rfl) ⟨2639759, by rfl⟩ : syracuseStep 3519679 = 5279519) B5279519
theorem B4692905 : Blo 2085435 4692905 := bstep (se 2 (by rfl) ⟨1759839, by rfl⟩ : syracuseStep 4692905 = 3519679) B3519679
theorem B3128603 : Blo 2085435 3128603 := bstep (se 1 (by rfl) ⟨2346452, by rfl⟩ : syracuseStep 3128603 = 4692905) B4692905
theorem B2085735 : Blo 2085435 2085735 := bstep (se 1 (by rfl) ⟨1564301, by rfl⟩ : syracuseStep 2085735 = 3128603) B3128603
theorem B2346457 : Blo 2085435 2346457 := bbase (se 2 (by rfl) ⟨879921, by rfl⟩ : syracuseStep 2346457 = 1759843) (by norm_num)
theorem B3128609 : Blo 2085435 3128609 := bstep (se 2 (by rfl) ⟨1173228, by rfl⟩ : syracuseStep 3128609 = 2346457) B2346457
theorem B2085739 : Blo 2085435 2085739 := bstep (se 1 (by rfl) ⟨1564304, by rfl⟩ : syracuseStep 2085739 = 3128609) B3128609
theorem B2969741 : Blo 2085435 2969741 := bbase (se 3 (by rfl) ⟨556826, by rfl⟩ : syracuseStep 2969741 = 1113653) (by norm_num)
theorem B7919309 : Blo 2085435 7919309 := bstep (se 3 (by rfl) ⟨1484870, by rfl⟩ : syracuseStep 7919309 = 2969741) B2969741
theorem B5279539 : Blo 2085435 5279539 := bstep (se 1 (by rfl) ⟨3959654, by rfl⟩ : syracuseStep 5279539 = 7919309) B7919309
theorem B7039385 : Blo 2085435 7039385 := bstep (se 2 (by rfl) ⟨2639769, by rfl⟩ : syracuseStep 7039385 = 5279539) B5279539
theorem B4692923 : Blo 2085435 4692923 := bstep (se 1 (by rfl) ⟨3519692, by rfl⟩ : syracuseStep 4692923 = 7039385) B7039385
theorem B3128615 : Blo 2085435 3128615 := bstep (se 1 (by rfl) ⟨2346461, by rfl⟩ : syracuseStep 3128615 = 4692923) B4692923
theorem B2085743 : Blo 2085435 2085743 := bstep (se 1 (by rfl) ⟨1564307, by rfl⟩ : syracuseStep 2085743 = 3128615) B3128615
theorem B3128621 : Blo 2085435 3128621 := bbase (se 3 (by rfl) ⟨586616, by rfl⟩ : syracuseStep 3128621 = 1173233) (by norm_num)
theorem B2085747 : Blo 2085435 2085747 := bstep (se 1 (by rfl) ⟨1564310, by rfl⟩ : syracuseStep 2085747 = 3128621) B3128621
theorem B4692941 : Blo 2085435 4692941 := bbase (se 3 (by rfl) ⟨879926, by rfl⟩ : syracuseStep 4692941 = 1759853) (by norm_num)
theorem B3128627 : Blo 2085435 3128627 := bstep (se 1 (by rfl) ⟨2346470, by rfl⟩ : syracuseStep 3128627 = 4692941) B4692941
theorem B2085751 : Blo 2085435 2085751 := bstep (se 1 (by rfl) ⟨1564313, by rfl⟩ : syracuseStep 2085751 = 3128627) B3128627
theorem B2639785 : Blo 2085435 2639785 := bbase (se 2 (by rfl) ⟨989919, by rfl⟩ : syracuseStep 2639785 = 1979839) (by norm_num)
theorem B3519713 : Blo 2085435 3519713 := bstep (se 2 (by rfl) ⟨1319892, by rfl⟩ : syracuseStep 3519713 = 2639785) B2639785
theorem B2346475 : Blo 2085435 2346475 := bstep (se 1 (by rfl) ⟨1759856, by rfl⟩ : syracuseStep 2346475 = 3519713) B3519713
theorem B3128633 : Blo 2085435 3128633 := bstep (se 2 (by rfl) ⟨1173237, by rfl⟩ : syracuseStep 3128633 = 2346475) B2346475
theorem B2085755 : Blo 2085435 2085755 := bstep (se 1 (by rfl) ⟨1564316, by rfl⟩ : syracuseStep 2085755 = 3128633) B3128633
theorem B2118637 : Blo 2085435 2118637 := bbase (se 3 (by rfl) ⟨397244, by rfl⟩ : syracuseStep 2118637 = 794489) (by norm_num)
theorem B2824849 : Blo 2085435 2824849 := bstep (se 2 (by rfl) ⟨1059318, by rfl⟩ : syracuseStep 2824849 = 2118637) B2118637
theorem B15065861 : Blo 2085435 15065861 := bstep (se 4 (by rfl) ⟨1412424, by rfl⟩ : syracuseStep 15065861 = 2824849) B2824849
theorem B160702517 : Blo 2085435 160702517 := bstep (se 5 (by rfl) ⟨7532930, by rfl⟩ : syracuseStep 160702517 = 15065861) B15065861
theorem B107135011 : Blo 2085435 107135011 := bstep (se 1 (by rfl) ⟨80351258, by rfl⟩ : syracuseStep 107135011 = 160702517) B160702517
theorem B142846681 : Blo 2085435 142846681 := bstep (se 2 (by rfl) ⟨53567505, by rfl⟩ : syracuseStep 142846681 = 107135011) B107135011
theorem B190462241 : Blo 2085435 190462241 := bstep (se 2 (by rfl) ⟨71423340, by rfl⟩ : syracuseStep 190462241 = 142846681) B142846681
theorem B126974827 : Blo 2085435 126974827 := bstep (se 1 (by rfl) ⟨95231120, by rfl⟩ : syracuseStep 126974827 = 190462241) B190462241
theorem B169299769 : Blo 2085435 169299769 := bstep (se 2 (by rfl) ⟨63487413, by rfl⟩ : syracuseStep 169299769 = 126974827) B126974827
theorem B225733025 : Blo 2085435 225733025 := bstep (se 2 (by rfl) ⟨84649884, by rfl⟩ : syracuseStep 225733025 = 169299769) B169299769
theorem B601954733 : Blo 2085435 601954733 := bstep (se 3 (by rfl) ⟨112866512, by rfl⟩ : syracuseStep 601954733 = 225733025) B225733025
theorem B401303155 : Blo 2085435 401303155 := bstep (se 1 (by rfl) ⟨300977366, by rfl⟩ : syracuseStep 401303155 = 601954733) B601954733
theorem B535070873 : Blo 2085435 535070873 := bstep (se 2 (by rfl) ⟨200651577, by rfl⟩ : syracuseStep 535070873 = 401303155) B401303155
theorem B1426855661 : Blo 2085435 1426855661 := bstep (se 3 (by rfl) ⟨267535436, by rfl⟩ : syracuseStep 1426855661 = 535070873) B535070873
theorem B951237107 : Blo 2085435 951237107 := bstep (se 1 (by rfl) ⟨713427830, by rfl⟩ : syracuseStep 951237107 = 1426855661) B1426855661
theorem B634158071 : Blo 2085435 634158071 := bstep (se 1 (by rfl) ⟨475618553, by rfl⟩ : syracuseStep 634158071 = 951237107) B951237107
theorem B422772047 : Blo 2085435 422772047 := bstep (se 1 (by rfl) ⟨317079035, by rfl⟩ : syracuseStep 422772047 = 634158071) B634158071
theorem B281848031 : Blo 2085435 281848031 := bstep (se 1 (by rfl) ⟨211386023, by rfl⟩ : syracuseStep 281848031 = 422772047) B422772047
theorem B187898687 : Blo 2085435 187898687 := bstep (se 1 (by rfl) ⟨140924015, by rfl⟩ : syracuseStep 187898687 = 281848031) B281848031
theorem B125265791 : Blo 2085435 125265791 := bstep (se 1 (by rfl) ⟨93949343, by rfl⟩ : syracuseStep 125265791 = 187898687) B187898687
theorem B83510527 : Blo 2085435 83510527 := bstep (se 1 (by rfl) ⟨62632895, by rfl⟩ : syracuseStep 83510527 = 125265791) B125265791
theorem B111347369 : Blo 2085435 111347369 := bstep (se 2 (by rfl) ⟨41755263, by rfl⟩ : syracuseStep 111347369 = 83510527) B83510527
theorem B74231579 : Blo 2085435 74231579 := bstep (se 1 (by rfl) ⟨55673684, by rfl⟩ : syracuseStep 74231579 = 111347369) B111347369
theorem B197950877 : Blo 2085435 197950877 := bstep (se 3 (by rfl) ⟨37115789, by rfl⟩ : syracuseStep 197950877 = 74231579) B74231579
theorem B131967251 : Blo 2085435 131967251 := bstep (se 1 (by rfl) ⟨98975438, by rfl⟩ : syracuseStep 131967251 = 197950877) B197950877
theorem B87978167 : Blo 2085435 87978167 := bstep (se 1 (by rfl) ⟨65983625, by rfl⟩ : syracuseStep 87978167 = 131967251) B131967251
theorem B58652111 : Blo 2085435 58652111 := bstep (se 1 (by rfl) ⟨43989083, by rfl⟩ : syracuseStep 58652111 = 87978167) B87978167
theorem B156405629 : Blo 2085435 156405629 := bstep (se 3 (by rfl) ⟨29326055, by rfl⟩ : syracuseStep 156405629 = 58652111) B58652111
theorem B104270419 : Blo 2085435 104270419 := bstep (se 1 (by rfl) ⟨78202814, by rfl⟩ : syracuseStep 104270419 = 156405629) B156405629
theorem B139027225 : Blo 2085435 139027225 := bstep (se 2 (by rfl) ⟨52135209, by rfl⟩ : syracuseStep 139027225 = 104270419) B104270419
theorem B185369633 : Blo 2085435 185369633 := bstep (se 2 (by rfl) ⟨69513612, by rfl⟩ : syracuseStep 185369633 = 139027225) B139027225
theorem B123579755 : Blo 2085435 123579755 := bstep (se 1 (by rfl) ⟨92684816, by rfl⟩ : syracuseStep 123579755 = 185369633) B185369633
theorem B82386503 : Blo 2085435 82386503 := bstep (se 1 (by rfl) ⟨61789877, by rfl⟩ : syracuseStep 82386503 = 123579755) B123579755
theorem B54924335 : Blo 2085435 54924335 := bstep (se 1 (by rfl) ⟨41193251, by rfl⟩ : syracuseStep 54924335 = 82386503) B82386503
theorem B36616223 : Blo 2085435 36616223 := bstep (se 1 (by rfl) ⟨27462167, by rfl⟩ : syracuseStep 36616223 = 54924335) B54924335
theorem B24410815 : Blo 2085435 24410815 := bstep (se 1 (by rfl) ⟨18308111, by rfl⟩ : syracuseStep 24410815 = 36616223) B36616223
theorem B130191013 : Blo 2085435 130191013 := bstep (se 4 (by rfl) ⟨12205407, by rfl⟩ : syracuseStep 130191013 = 24410815) B24410815
theorem B173588017 : Blo 2085435 173588017 := bstep (se 2 (by rfl) ⟨65095506, by rfl⟩ : syracuseStep 173588017 = 130191013) B130191013
theorem B231450689 : Blo 2085435 231450689 := bstep (se 2 (by rfl) ⟨86794008, by rfl⟩ : syracuseStep 231450689 = 173588017) B173588017
theorem B154300459 : Blo 2085435 154300459 := bstep (se 1 (by rfl) ⟨115725344, by rfl⟩ : syracuseStep 154300459 = 231450689) B231450689
theorem B205733945 : Blo 2085435 205733945 := bstep (se 2 (by rfl) ⟨77150229, by rfl⟩ : syracuseStep 205733945 = 154300459) B154300459
theorem B137155963 : Blo 2085435 137155963 := bstep (se 1 (by rfl) ⟨102866972, by rfl⟩ : syracuseStep 137155963 = 205733945) B205733945
theorem B182874617 : Blo 2085435 182874617 := bstep (se 2 (by rfl) ⟨68577981, by rfl⟩ : syracuseStep 182874617 = 137155963) B137155963
theorem B121916411 : Blo 2085435 121916411 := bstep (se 1 (by rfl) ⟨91437308, by rfl⟩ : syracuseStep 121916411 = 182874617) B182874617
theorem B81277607 : Blo 2085435 81277607 := bstep (se 1 (by rfl) ⟨60958205, by rfl⟩ : syracuseStep 81277607 = 121916411) B121916411
theorem B54185071 : Blo 2085435 54185071 := bstep (se 1 (by rfl) ⟨40638803, by rfl⟩ : syracuseStep 54185071 = 81277607) B81277607
theorem B72246761 : Blo 2085435 72246761 := bstep (se 2 (by rfl) ⟨27092535, by rfl⟩ : syracuseStep 72246761 = 54185071) B54185071
theorem B48164507 : Blo 2085435 48164507 := bstep (se 1 (by rfl) ⟨36123380, by rfl⟩ : syracuseStep 48164507 = 72246761) B72246761
theorem B32109671 : Blo 2085435 32109671 := bstep (se 1 (by rfl) ⟨24082253, by rfl⟩ : syracuseStep 32109671 = 48164507) B48164507
theorem B21406447 : Blo 2085435 21406447 := bstep (se 1 (by rfl) ⟨16054835, by rfl⟩ : syracuseStep 21406447 = 32109671) B32109671
theorem B28541929 : Blo 2085435 28541929 := bstep (se 2 (by rfl) ⟨10703223, by rfl⟩ : syracuseStep 28541929 = 21406447) B21406447
theorem B38055905 : Blo 2085435 38055905 := bstep (se 2 (by rfl) ⟨14270964, by rfl⟩ : syracuseStep 38055905 = 28541929) B28541929
theorem B25370603 : Blo 2085435 25370603 := bstep (se 1 (by rfl) ⟨19027952, by rfl⟩ : syracuseStep 25370603 = 38055905) B38055905
theorem B16913735 : Blo 2085435 16913735 := bstep (se 1 (by rfl) ⟨12685301, by rfl⟩ : syracuseStep 16913735 = 25370603) B25370603
theorem B11275823 : Blo 2085435 11275823 := bstep (se 1 (by rfl) ⟨8456867, by rfl⟩ : syracuseStep 11275823 = 16913735) B16913735
theorem B7517215 : Blo 2085435 7517215 := bstep (se 1 (by rfl) ⟨5637911, by rfl⟩ : syracuseStep 7517215 = 11275823) B11275823
theorem B10022953 : Blo 2085435 10022953 := bstep (se 2 (by rfl) ⟨3758607, by rfl⟩ : syracuseStep 10022953 = 7517215) B7517215
theorem B13363937 : Blo 2085435 13363937 := bstep (se 2 (by rfl) ⟨5011476, by rfl⟩ : syracuseStep 13363937 = 10022953) B10022953
theorem B8909291 : Blo 2085435 8909291 := bstep (se 1 (by rfl) ⟨6681968, by rfl⟩ : syracuseStep 8909291 = 13363937) B13363937
theorem B23758109 : Blo 2085435 23758109 := bstep (se 3 (by rfl) ⟨4454645, by rfl⟩ : syracuseStep 23758109 = 8909291) B8909291
theorem B15838739 : Blo 2085435 15838739 := bstep (se 1 (by rfl) ⟨11879054, by rfl⟩ : syracuseStep 15838739 = 23758109) B23758109
theorem B10559159 : Blo 2085435 10559159 := bstep (se 1 (by rfl) ⟨7919369, by rfl⟩ : syracuseStep 10559159 = 15838739) B15838739
theorem B7039439 : Blo 2085435 7039439 := bstep (se 1 (by rfl) ⟨5279579, by rfl⟩ : syracuseStep 7039439 = 10559159) B10559159
theorem B4692959 : Blo 2085435 4692959 := bstep (se 1 (by rfl) ⟨3519719, by rfl⟩ : syracuseStep 4692959 = 7039439) B7039439
theorem B3128639 : Blo 2085435 3128639 := bstep (se 1 (by rfl) ⟨2346479, by rfl⟩ : syracuseStep 3128639 = 4692959) B4692959
theorem B2085759 : Blo 2085435 2085759 := bstep (se 1 (by rfl) ⟨1564319, by rfl⟩ : syracuseStep 2085759 = 3128639) B3128639
theorem B3128645 : Blo 2085435 3128645 := bbase (se 4 (by rfl) ⟨293310, by rfl⟩ : syracuseStep 3128645 = 586621) (by norm_num)
theorem B2085763 : Blo 2085435 2085763 := bstep (se 1 (by rfl) ⟨1564322, by rfl⟩ : syracuseStep 2085763 = 3128645) B3128645
theorem B3519733 : Blo 2085435 3519733 := bbase (se 5 (by rfl) ⟨164987, by rfl⟩ : syracuseStep 3519733 = 329975) (by norm_num)
theorem B4692977 : Blo 2085435 4692977 := bstep (se 2 (by rfl) ⟨1759866, by rfl⟩ : syracuseStep 4692977 = 3519733) B3519733
theorem B3128651 : Blo 2085435 3128651 := bstep (se 1 (by rfl) ⟨2346488, by rfl⟩ : syracuseStep 3128651 = 4692977) B4692977
theorem B2085767 : Blo 2085435 2085767 := bstep (se 1 (by rfl) ⟨1564325, by rfl⟩ : syracuseStep 2085767 = 3128651) B3128651
theorem B2346493 : Blo 2085435 2346493 := bbase (se 3 (by rfl) ⟨439967, by rfl⟩ : syracuseStep 2346493 = 879935) (by norm_num)
theorem B3128657 : Blo 2085435 3128657 := bstep (se 2 (by rfl) ⟨1173246, by rfl⟩ : syracuseStep 3128657 = 2346493) B2346493
theorem B2085771 : Blo 2085435 2085771 := bstep (se 1 (by rfl) ⟨1564328, by rfl⟩ : syracuseStep 2085771 = 3128657) B3128657
theorem B7039493 : Blo 2085435 7039493 := bbase (se 4 (by rfl) ⟨659952, by rfl⟩ : syracuseStep 7039493 = 1319905) (by norm_num)
theorem B4692995 : Blo 2085435 4692995 := bstep (se 1 (by rfl) ⟨3519746, by rfl⟩ : syracuseStep 4692995 = 7039493) B7039493
theorem B3128663 : Blo 2085435 3128663 := bstep (se 1 (by rfl) ⟨2346497, by rfl⟩ : syracuseStep 3128663 = 4692995) B4692995
theorem B2085775 : Blo 2085435 2085775 := bstep (se 1 (by rfl) ⟨1564331, by rfl⟩ : syracuseStep 2085775 = 3128663) B3128663
theorem B3128669 : Blo 2085435 3128669 := bbase (se 3 (by rfl) ⟨586625, by rfl⟩ : syracuseStep 3128669 = 1173251) (by norm_num)
theorem B2085779 : Blo 2085435 2085779 := bstep (se 1 (by rfl) ⟨1564334, by rfl⟩ : syracuseStep 2085779 = 3128669) B3128669
theorem B4693013 : Blo 2085435 4693013 := bbase (se 6 (by rfl) ⟨109992, by rfl⟩ : syracuseStep 4693013 = 219985) (by norm_num)
theorem B3128675 : Blo 2085435 3128675 := bstep (se 1 (by rfl) ⟨2346506, by rfl⟩ : syracuseStep 3128675 = 4693013) B4693013
theorem B2085783 : Blo 2085435 2085783 := bstep (se 1 (by rfl) ⟨1564337, by rfl⟩ : syracuseStep 2085783 = 3128675) B3128675
theorem B7919477 : Blo 2085435 7919477 := bbase (se 5 (by rfl) ⟨371225, by rfl⟩ : syracuseStep 7919477 = 742451) (by norm_num)
theorem B5279651 : Blo 2085435 5279651 := bstep (se 1 (by rfl) ⟨3959738, by rfl⟩ : syracuseStep 5279651 = 7919477) B7919477
theorem B3519767 : Blo 2085435 3519767 := bstep (se 1 (by rfl) ⟨2639825, by rfl⟩ : syracuseStep 3519767 = 5279651) B5279651
theorem B2346511 : Blo 2085435 2346511 := bstep (se 1 (by rfl) ⟨1759883, by rfl⟩ : syracuseStep 2346511 = 3519767) B3519767
theorem B3128681 : Blo 2085435 3128681 := bstep (se 2 (by rfl) ⟨1173255, by rfl⟩ : syracuseStep 3128681 = 2346511) B2346511
theorem B2085787 : Blo 2085435 2085787 := bstep (se 1 (by rfl) ⟨1564340, by rfl⟩ : syracuseStep 2085787 = 3128681) B3128681
theorem B2227357 : Blo 2085435 2227357 := bbase (se 3 (by rfl) ⟨417629, by rfl⟩ : syracuseStep 2227357 = 835259) (by norm_num)
theorem B11879237 : Blo 2085435 11879237 := bstep (se 4 (by rfl) ⟨1113678, by rfl⟩ : syracuseStep 11879237 = 2227357) B2227357
theorem B7919491 : Blo 2085435 7919491 := bstep (se 1 (by rfl) ⟨5939618, by rfl⟩ : syracuseStep 7919491 = 11879237) B11879237
theorem B10559321 : Blo 2085435 10559321 := bstep (se 2 (by rfl) ⟨3959745, by rfl⟩ : syracuseStep 10559321 = 7919491) B7919491
theorem B7039547 : Blo 2085435 7039547 := bstep (se 1 (by rfl) ⟨5279660, by rfl⟩ : syracuseStep 7039547 = 10559321) B10559321
theorem B4693031 : Blo 2085435 4693031 := bstep (se 1 (by rfl) ⟨3519773, by rfl⟩ : syracuseStep 4693031 = 7039547) B7039547
theorem B3128687 : Blo 2085435 3128687 := bstep (se 1 (by rfl) ⟨2346515, by rfl⟩ : syracuseStep 3128687 = 4693031) B4693031
theorem B2085791 : Blo 2085435 2085791 := bstep (se 1 (by rfl) ⟨1564343, by rfl⟩ : syracuseStep 2085791 = 3128687) B3128687
theorem B3128693 : Blo 2085435 3128693 := bbase (se 5 (by rfl) ⟨146657, by rfl⟩ : syracuseStep 3128693 = 293315) (by norm_num)
theorem B2085795 : Blo 2085435 2085795 := bstep (se 1 (by rfl) ⟨1564346, by rfl⟩ : syracuseStep 2085795 = 3128693) B3128693
theorem B2969821 : Blo 2085435 2969821 := bbase (se 3 (by rfl) ⟨556841, by rfl⟩ : syracuseStep 2969821 = 1113683) (by norm_num)
theorem B3959761 : Blo 2085435 3959761 := bstep (se 2 (by rfl) ⟨1484910, by rfl⟩ : syracuseStep 3959761 = 2969821) B2969821
theorem B5279681 : Blo 2085435 5279681 := bstep (se 2 (by rfl) ⟨1979880, by rfl⟩ : syracuseStep 5279681 = 3959761) B3959761
theorem B3519787 : Blo 2085435 3519787 := bstep (se 1 (by rfl) ⟨2639840, by rfl⟩ : syracuseStep 3519787 = 5279681) B5279681
theorem B4693049 : Blo 2085435 4693049 := bstep (se 2 (by rfl) ⟨1759893, by rfl⟩ : syracuseStep 4693049 = 3519787) B3519787
theorem B3128699 : Blo 2085435 3128699 := bstep (se 1 (by rfl) ⟨2346524, by rfl⟩ : syracuseStep 3128699 = 4693049) B4693049
theorem B2085799 : Blo 2085435 2085799 := bstep (se 1 (by rfl) ⟨1564349, by rfl⟩ : syracuseStep 2085799 = 3128699) B3128699
theorem B2346529 : Blo 2085435 2346529 := bbase (se 2 (by rfl) ⟨879948, by rfl⟩ : syracuseStep 2346529 = 1759897) (by norm_num)
theorem B3128705 : Blo 2085435 3128705 := bstep (se 2 (by rfl) ⟨1173264, by rfl⟩ : syracuseStep 3128705 = 2346529) B2346529
theorem B2085803 : Blo 2085435 2085803 := bstep (se 1 (by rfl) ⟨1564352, by rfl⟩ : syracuseStep 2085803 = 3128705) B3128705
theorem B5279701 : Blo 2085435 5279701 := bbase (se 7 (by rfl) ⟨61871, by rfl⟩ : syracuseStep 5279701 = 123743) (by norm_num)
theorem B7039601 : Blo 2085435 7039601 := bstep (se 2 (by rfl) ⟨2639850, by rfl⟩ : syracuseStep 7039601 = 5279701) B5279701
theorem B4693067 : Blo 2085435 4693067 := bstep (se 1 (by rfl) ⟨3519800, by rfl⟩ : syracuseStep 4693067 = 7039601) B7039601
theorem B3128711 : Blo 2085435 3128711 := bstep (se 1 (by rfl) ⟨2346533, by rfl⟩ : syracuseStep 3128711 = 4693067) B4693067
theorem B2085807 : Blo 2085435 2085807 := bstep (se 1 (by rfl) ⟨1564355, by rfl⟩ : syracuseStep 2085807 = 3128711) B3128711
theorem B3128717 : Blo 2085435 3128717 := bbase (se 3 (by rfl) ⟨586634, by rfl⟩ : syracuseStep 3128717 = 1173269) (by norm_num)
theorem B2085811 : Blo 2085435 2085811 := bstep (se 1 (by rfl) ⟨1564358, by rfl⟩ : syracuseStep 2085811 = 3128717) B3128717
theorem B4693085 : Blo 2085435 4693085 := bbase (se 3 (by rfl) ⟨879953, by rfl⟩ : syracuseStep 4693085 = 1759907) (by norm_num)
theorem B3128723 : Blo 2085435 3128723 := bstep (se 1 (by rfl) ⟨2346542, by rfl⟩ : syracuseStep 3128723 = 4693085) B4693085
theorem B2085815 : Blo 2085435 2085815 := bstep (se 1 (by rfl) ⟨1564361, by rfl⟩ : syracuseStep 2085815 = 3128723) B3128723
theorem B3519821 : Blo 2085435 3519821 := bbase (se 3 (by rfl) ⟨659966, by rfl⟩ : syracuseStep 3519821 = 1319933) (by norm_num)
theorem B2346547 : Blo 2085435 2346547 := bstep (se 1 (by rfl) ⟨1759910, by rfl⟩ : syracuseStep 2346547 = 3519821) B3519821
theorem B3128729 : Blo 2085435 3128729 := bstep (se 2 (by rfl) ⟨1173273, by rfl⟩ : syracuseStep 3128729 = 2346547) B2346547
theorem B2085819 : Blo 2085435 2085819 := bstep (se 1 (by rfl) ⟨1564364, by rfl⟩ : syracuseStep 2085819 = 3128729) B3128729
theorem B8572517 : Blo 2085435 8572517 := bbase (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) (by norm_num)
theorem B5715011 : Blo 2085435 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B3810007 : Blo 2085435 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B5080009 : Blo 2085435 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B6773345 : Blo 2085435 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B4515563 : Blo 2085435 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B3010375 : Blo 2085435 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B4013833 : Blo 2085435 4013833 := bstep (se 2 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 4013833 = 3010375) B3010375
theorem B5351777 : Blo 2085435 5351777 := bstep (se 2 (by rfl) ⟨2006916, by rfl⟩ : syracuseStep 5351777 = 4013833) B4013833
theorem B3567851 : Blo 2085435 3567851 := bstep (se 1 (by rfl) ⟨2675888, by rfl⟩ : syracuseStep 3567851 = 5351777) B5351777
theorem B2378567 : Blo 2085435 2378567 := bstep (se 1 (by rfl) ⟨1783925, by rfl⟩ : syracuseStep 2378567 = 3567851) B3567851
theorem B6342845 : Blo 2085435 6342845 := bstep (se 3 (by rfl) ⟨1189283, by rfl⟩ : syracuseStep 6342845 = 2378567) B2378567
theorem B16914253 : Blo 2085435 16914253 := bstep (se 3 (by rfl) ⟨3171422, by rfl⟩ : syracuseStep 16914253 = 6342845) B6342845
theorem B22552337 : Blo 2085435 22552337 := bstep (se 2 (by rfl) ⟨8457126, by rfl⟩ : syracuseStep 22552337 = 16914253) B16914253
theorem B15034891 : Blo 2085435 15034891 := bstep (se 1 (by rfl) ⟨11276168, by rfl⟩ : syracuseStep 15034891 = 22552337) B22552337
theorem B20046521 : Blo 2085435 20046521 := bstep (se 2 (by rfl) ⟨7517445, by rfl⟩ : syracuseStep 20046521 = 15034891) B15034891
theorem B13364347 : Blo 2085435 13364347 := bstep (se 1 (by rfl) ⟨10023260, by rfl⟩ : syracuseStep 13364347 = 20046521) B20046521
theorem B17819129 : Blo 2085435 17819129 := bstep (se 2 (by rfl) ⟨6682173, by rfl⟩ : syracuseStep 17819129 = 13364347) B13364347
theorem B11879419 : Blo 2085435 11879419 := bstep (se 1 (by rfl) ⟨8909564, by rfl⟩ : syracuseStep 11879419 = 17819129) B17819129
theorem B15839225 : Blo 2085435 15839225 := bstep (se 2 (by rfl) ⟨5939709, by rfl⟩ : syracuseStep 15839225 = 11879419) B11879419
theorem B10559483 : Blo 2085435 10559483 := bstep (se 1 (by rfl) ⟨7919612, by rfl⟩ : syracuseStep 10559483 = 15839225) B15839225
theorem B7039655 : Blo 2085435 7039655 := bstep (se 1 (by rfl) ⟨5279741, by rfl⟩ : syracuseStep 7039655 = 10559483) B10559483
theorem B4693103 : Blo 2085435 4693103 := bstep (se 1 (by rfl) ⟨3519827, by rfl⟩ : syracuseStep 4693103 = 7039655) B7039655
theorem B3128735 : Blo 2085435 3128735 := bstep (se 1 (by rfl) ⟨2346551, by rfl⟩ : syracuseStep 3128735 = 4693103) B4693103
theorem B2085823 : Blo 2085435 2085823 := bstep (se 1 (by rfl) ⟨1564367, by rfl⟩ : syracuseStep 2085823 = 3128735) B3128735
theorem B3128741 : Blo 2085435 3128741 := bbase (se 4 (by rfl) ⟨293319, by rfl⟩ : syracuseStep 3128741 = 586639) (by norm_num)
theorem B2085827 : Blo 2085435 2085827 := bstep (se 1 (by rfl) ⟨1564370, by rfl⟩ : syracuseStep 2085827 = 3128741) B3128741
theorem B2639881 : Blo 2085435 2639881 := bbase (se 2 (by rfl) ⟨989955, by rfl⟩ : syracuseStep 2639881 = 1979911) (by norm_num)
theorem B3519841 : Blo 2085435 3519841 := bstep (se 2 (by rfl) ⟨1319940, by rfl⟩ : syracuseStep 3519841 = 2639881) B2639881
theorem B4693121 : Blo 2085435 4693121 := bstep (se 2 (by rfl) ⟨1759920, by rfl⟩ : syracuseStep 4693121 = 3519841) B3519841
theorem B3128747 : Blo 2085435 3128747 := bstep (se 1 (by rfl) ⟨2346560, by rfl⟩ : syracuseStep 3128747 = 4693121) B4693121
theorem B2085831 : Blo 2085435 2085831 := bstep (se 1 (by rfl) ⟨1564373, by rfl⟩ : syracuseStep 2085831 = 3128747) B3128747
theorem B2346565 : Blo 2085435 2346565 := bbase (se 4 (by rfl) ⟨219990, by rfl⟩ : syracuseStep 2346565 = 439981) (by norm_num)
theorem B3128753 : Blo 2085435 3128753 := bstep (se 2 (by rfl) ⟨1173282, by rfl⟩ : syracuseStep 3128753 = 2346565) B2346565
theorem B2085835 : Blo 2085435 2085835 := bstep (se 1 (by rfl) ⟨1564376, by rfl⟩ : syracuseStep 2085835 = 3128753) B3128753
theorem B3959837 : Blo 2085435 3959837 := bbase (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) (by norm_num)
theorem B2639891 : Blo 2085435 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B7039709 : Blo 2085435 7039709 := bstep (se 3 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 7039709 = 2639891) B2639891
theorem B4693139 : Blo 2085435 4693139 := bstep (se 1 (by rfl) ⟨3519854, by rfl⟩ : syracuseStep 4693139 = 7039709) B7039709
theorem B3128759 : Blo 2085435 3128759 := bstep (se 1 (by rfl) ⟨2346569, by rfl⟩ : syracuseStep 3128759 = 4693139) B4693139
theorem B2085839 : Blo 2085435 2085839 := bstep (se 1 (by rfl) ⟨1564379, by rfl⟩ : syracuseStep 2085839 = 3128759) B3128759
theorem B3128765 : Blo 2085435 3128765 := bbase (se 3 (by rfl) ⟨586643, by rfl⟩ : syracuseStep 3128765 = 1173287) (by norm_num)
theorem B2085843 : Blo 2085435 2085843 := bstep (se 1 (by rfl) ⟨1564382, by rfl⟩ : syracuseStep 2085843 = 3128765) B3128765
theorem B4693157 : Blo 2085435 4693157 := bbase (se 4 (by rfl) ⟨439983, by rfl⟩ : syracuseStep 4693157 = 879967) (by norm_num)
theorem B3128771 : Blo 2085435 3128771 := bstep (se 1 (by rfl) ⟨2346578, by rfl⟩ : syracuseStep 3128771 = 4693157) B4693157
theorem B2085847 : Blo 2085435 2085847 := bstep (se 1 (by rfl) ⟨1564385, by rfl⟩ : syracuseStep 2085847 = 3128771) B3128771
theorem B5279813 : Blo 2085435 5279813 := bbase (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) (by norm_num)
theorem B3519875 : Blo 2085435 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B2346583 : Blo 2085435 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B3128777 : Blo 2085435 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B2085851 : Blo 2085435 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B6682277 : Blo 2085435 6682277 := bbase (se 4 (by rfl) ⟨626463, by rfl⟩ : syracuseStep 6682277 = 1252927) (by norm_num)
theorem B4454851 : Blo 2085435 4454851 := bstep (se 1 (by rfl) ⟨3341138, by rfl⟩ : syracuseStep 4454851 = 6682277) B6682277
theorem B5939801 : Blo 2085435 5939801 := bstep (se 2 (by rfl) ⟨2227425, by rfl⟩ : syracuseStep 5939801 = 4454851) B4454851
theorem B3959867 : Blo 2085435 3959867 := bstep (se 1 (by rfl) ⟨2969900, by rfl⟩ : syracuseStep 3959867 = 5939801) B5939801
theorem B10559645 : Blo 2085435 10559645 := bstep (se 3 (by rfl) ⟨1979933, by rfl⟩ : syracuseStep 10559645 = 3959867) B3959867
theorem B7039763 : Blo 2085435 7039763 := bstep (se 1 (by rfl) ⟨5279822, by rfl⟩ : syracuseStep 7039763 = 10559645) B10559645
theorem B4693175 : Blo 2085435 4693175 := bstep (se 1 (by rfl) ⟨3519881, by rfl⟩ : syracuseStep 4693175 = 7039763) B7039763
theorem B3128783 : Blo 2085435 3128783 := bstep (se 1 (by rfl) ⟨2346587, by rfl⟩ : syracuseStep 3128783 = 4693175) B4693175
theorem B2085855 : Blo 2085435 2085855 := bstep (se 1 (by rfl) ⟨1564391, by rfl⟩ : syracuseStep 2085855 = 3128783) B3128783
theorem B3128789 : Blo 2085435 3128789 := bbase (se 7 (by rfl) ⟨36665, by rfl⟩ : syracuseStep 3128789 = 73331) (by norm_num)
theorem B2085859 : Blo 2085435 2085859 := bstep (se 1 (by rfl) ⟨1564394, by rfl⟩ : syracuseStep 2085859 = 3128789) B3128789
theorem B7919765 : Blo 2085435 7919765 := bbase (se 6 (by rfl) ⟨185619, by rfl⟩ : syracuseStep 7919765 = 371239) (by norm_num)
theorem B5279843 : Blo 2085435 5279843 := bstep (se 1 (by rfl) ⟨3959882, by rfl⟩ : syracuseStep 5279843 = 7919765) B7919765
theorem B3519895 : Blo 2085435 3519895 := bstep (se 1 (by rfl) ⟨2639921, by rfl⟩ : syracuseStep 3519895 = 5279843) B5279843
theorem B4693193 : Blo 2085435 4693193 := bstep (se 2 (by rfl) ⟨1759947, by rfl⟩ : syracuseStep 4693193 = 3519895) B3519895
theorem B3128795 : Blo 2085435 3128795 := bstep (se 1 (by rfl) ⟨2346596, by rfl⟩ : syracuseStep 3128795 = 4693193) B4693193
theorem B2085863 : Blo 2085435 2085863 := bstep (se 1 (by rfl) ⟨1564397, by rfl⟩ : syracuseStep 2085863 = 3128795) B3128795
theorem B2346601 : Blo 2085435 2346601 := bbase (se 2 (by rfl) ⟨879975, by rfl⟩ : syracuseStep 2346601 = 1759951) (by norm_num)
theorem B3128801 : Blo 2085435 3128801 := bstep (se 2 (by rfl) ⟨1173300, by rfl⟩ : syracuseStep 3128801 = 2346601) B2346601
theorem B2085867 : Blo 2085435 2085867 := bstep (se 1 (by rfl) ⟨1564400, by rfl⟩ : syracuseStep 2085867 = 3128801) B3128801
theorem B4454885 : Blo 2085435 4454885 := bbase (se 4 (by rfl) ⟨417645, by rfl⟩ : syracuseStep 4454885 = 835291) (by norm_num)
theorem B11879693 : Blo 2085435 11879693 := bstep (se 3 (by rfl) ⟨2227442, by rfl⟩ : syracuseStep 11879693 = 4454885) B4454885
theorem B7919795 : Blo 2085435 7919795 := bstep (se 1 (by rfl) ⟨5939846, by rfl⟩ : syracuseStep 7919795 = 11879693) B11879693
theorem B5279863 : Blo 2085435 5279863 := bstep (se 1 (by rfl) ⟨3959897, by rfl⟩ : syracuseStep 5279863 = 7919795) B7919795
theorem B7039817 : Blo 2085435 7039817 := bstep (se 2 (by rfl) ⟨2639931, by rfl⟩ : syracuseStep 7039817 = 5279863) B5279863
theorem B4693211 : Blo 2085435 4693211 := bstep (se 1 (by rfl) ⟨3519908, by rfl⟩ : syracuseStep 4693211 = 7039817) B7039817
theorem B3128807 : Blo 2085435 3128807 := bstep (se 1 (by rfl) ⟨2346605, by rfl⟩ : syracuseStep 3128807 = 4693211) B4693211
theorem B2085871 : Blo 2085435 2085871 := bstep (se 1 (by rfl) ⟨1564403, by rfl⟩ : syracuseStep 2085871 = 3128807) B3128807
theorem B3128813 : Blo 2085435 3128813 := bbase (se 3 (by rfl) ⟨586652, by rfl⟩ : syracuseStep 3128813 = 1173305) (by norm_num)
theorem B2085875 : Blo 2085435 2085875 := bstep (se 1 (by rfl) ⟨1564406, by rfl⟩ : syracuseStep 2085875 = 3128813) B3128813
theorem B4693229 : Blo 2085435 4693229 := bbase (se 3 (by rfl) ⟨879980, by rfl⟩ : syracuseStep 4693229 = 1759961) (by norm_num)
theorem B3128819 : Blo 2085435 3128819 := bstep (se 1 (by rfl) ⟨2346614, by rfl⟩ : syracuseStep 3128819 = 4693229) B4693229
theorem B2085879 : Blo 2085435 2085879 := bstep (se 1 (by rfl) ⟨1564409, by rfl⟩ : syracuseStep 2085879 = 3128819) B3128819
theorem B2969941 : Blo 2085435 2969941 := bbase (se 10 (by rfl) ⟨4350, by rfl⟩ : syracuseStep 2969941 = 8701) (by norm_num)
theorem B3959921 : Blo 2085435 3959921 := bstep (se 2 (by rfl) ⟨1484970, by rfl⟩ : syracuseStep 3959921 = 2969941) B2969941
theorem B2639947 : Blo 2085435 2639947 := bstep (se 1 (by rfl) ⟨1979960, by rfl⟩ : syracuseStep 2639947 = 3959921) B3959921
theorem B3519929 : Blo 2085435 3519929 := bstep (se 2 (by rfl) ⟨1319973, by rfl⟩ : syracuseStep 3519929 = 2639947) B2639947
theorem B2346619 : Blo 2085435 2346619 := bstep (se 1 (by rfl) ⟨1759964, by rfl⟩ : syracuseStep 2346619 = 3519929) B3519929
theorem B3128825 : Blo 2085435 3128825 := bstep (se 2 (by rfl) ⟨1173309, by rfl⟩ : syracuseStep 3128825 = 2346619) B2346619
theorem B2085883 : Blo 2085435 2085883 := bstep (se 1 (by rfl) ⟨1564412, by rfl⟩ : syracuseStep 2085883 = 3128825) B3128825
theorem B2540081 : Blo 2085435 2540081 := bbase (se 2 (by rfl) ⟨952530, by rfl⟩ : syracuseStep 2540081 = 1905061) (by norm_num)
theorem B6773549 : Blo 2085435 6773549 := bstep (se 3 (by rfl) ⟨1270040, by rfl⟩ : syracuseStep 6773549 = 2540081) B2540081
theorem B18062797 : Blo 2085435 18062797 := bstep (se 3 (by rfl) ⟨3386774, by rfl⟩ : syracuseStep 18062797 = 6773549) B6773549
theorem B24083729 : Blo 2085435 24083729 := bstep (se 2 (by rfl) ⟨9031398, by rfl⟩ : syracuseStep 24083729 = 18062797) B18062797
theorem B16055819 : Blo 2085435 16055819 := bstep (se 1 (by rfl) ⟨12041864, by rfl⟩ : syracuseStep 16055819 = 24083729) B24083729
theorem B10703879 : Blo 2085435 10703879 := bstep (se 1 (by rfl) ⟨8027909, by rfl⟩ : syracuseStep 10703879 = 16055819) B16055819
theorem B7135919 : Blo 2085435 7135919 := bstep (se 1 (by rfl) ⟨5351939, by rfl⟩ : syracuseStep 7135919 = 10703879) B10703879
theorem B76116469 : Blo 2085435 76116469 := bstep (se 5 (by rfl) ⟨3567959, by rfl⟩ : syracuseStep 76116469 = 7135919) B7135919
theorem B101488625 : Blo 2085435 101488625 := bstep (se 2 (by rfl) ⟨38058234, by rfl⟩ : syracuseStep 101488625 = 76116469) B76116469
theorem B67659083 : Blo 2085435 67659083 := bstep (se 1 (by rfl) ⟨50744312, by rfl⟩ : syracuseStep 67659083 = 101488625) B101488625
theorem B45106055 : Blo 2085435 45106055 := bstep (se 1 (by rfl) ⟨33829541, by rfl⟩ : syracuseStep 45106055 = 67659083) B67659083
theorem B30070703 : Blo 2085435 30070703 := bstep (se 1 (by rfl) ⟨22553027, by rfl⟩ : syracuseStep 30070703 = 45106055) B45106055
theorem B80188541 : Blo 2085435 80188541 := bstep (se 3 (by rfl) ⟨15035351, by rfl⟩ : syracuseStep 80188541 = 30070703) B30070703
theorem B53459027 : Blo 2085435 53459027 := bstep (se 1 (by rfl) ⟨40094270, by rfl⟩ : syracuseStep 53459027 = 80188541) B80188541
theorem B35639351 : Blo 2085435 35639351 := bstep (se 1 (by rfl) ⟨26729513, by rfl⟩ : syracuseStep 35639351 = 53459027) B53459027
theorem B23759567 : Blo 2085435 23759567 := bstep (se 1 (by rfl) ⟨17819675, by rfl⟩ : syracuseStep 23759567 = 35639351) B35639351
theorem B15839711 : Blo 2085435 15839711 := bstep (se 1 (by rfl) ⟨11879783, by rfl⟩ : syracuseStep 15839711 = 23759567) B23759567
theorem B10559807 : Blo 2085435 10559807 := bstep (se 1 (by rfl) ⟨7919855, by rfl⟩ : syracuseStep 10559807 = 15839711) B15839711
theorem B7039871 : Blo 2085435 7039871 := bstep (se 1 (by rfl) ⟨5279903, by rfl⟩ : syracuseStep 7039871 = 10559807) B10559807
theorem B4693247 : Blo 2085435 4693247 := bstep (se 1 (by rfl) ⟨3519935, by rfl⟩ : syracuseStep 4693247 = 7039871) B7039871
theorem B3128831 : Blo 2085435 3128831 := bstep (se 1 (by rfl) ⟨2346623, by rfl⟩ : syracuseStep 3128831 = 4693247) B4693247
theorem B2085887 : Blo 2085435 2085887 := bstep (se 1 (by rfl) ⟨1564415, by rfl⟩ : syracuseStep 2085887 = 3128831) B3128831
theorem B3128837 : Blo 2085435 3128837 := bbase (se 4 (by rfl) ⟨293328, by rfl⟩ : syracuseStep 3128837 = 586657) (by norm_num)
theorem B2085891 : Blo 2085435 2085891 := bstep (se 1 (by rfl) ⟨1564418, by rfl⟩ : syracuseStep 2085891 = 3128837) B3128837
theorem B3519949 : Blo 2085435 3519949 := bbase (se 3 (by rfl) ⟨659990, by rfl⟩ : syracuseStep 3519949 = 1319981) (by norm_num)
theorem B4693265 : Blo 2085435 4693265 := bstep (se 2 (by rfl) ⟨1759974, by rfl⟩ : syracuseStep 4693265 = 3519949) B3519949
theorem B3128843 : Blo 2085435 3128843 := bstep (se 1 (by rfl) ⟨2346632, by rfl⟩ : syracuseStep 3128843 = 4693265) B4693265
theorem B2085895 : Blo 2085435 2085895 := bstep (se 1 (by rfl) ⟨1564421, by rfl⟩ : syracuseStep 2085895 = 3128843) B3128843
theorem B2346637 : Blo 2085435 2346637 := bbase (se 3 (by rfl) ⟨439994, by rfl⟩ : syracuseStep 2346637 = 879989) (by norm_num)
theorem B3128849 : Blo 2085435 3128849 := bstep (se 2 (by rfl) ⟨1173318, by rfl⟩ : syracuseStep 3128849 = 2346637) B2346637
theorem B2085899 : Blo 2085435 2085899 := bstep (se 1 (by rfl) ⟨1564424, by rfl⟩ : syracuseStep 2085899 = 3128849) B3128849
theorem B7039925 : Blo 2085435 7039925 := bbase (se 5 (by rfl) ⟨329996, by rfl⟩ : syracuseStep 7039925 = 659993) (by norm_num)
theorem B4693283 : Blo 2085435 4693283 := bstep (se 1 (by rfl) ⟨3519962, by rfl⟩ : syracuseStep 4693283 = 7039925) B7039925
theorem B3128855 : Blo 2085435 3128855 := bstep (se 1 (by rfl) ⟨2346641, by rfl⟩ : syracuseStep 3128855 = 4693283) B4693283
theorem B2085903 : Blo 2085435 2085903 := bstep (se 1 (by rfl) ⟨1564427, by rfl⟩ : syracuseStep 2085903 = 3128855) B3128855
theorem B3128861 : Blo 2085435 3128861 := bbase (se 3 (by rfl) ⟨586661, by rfl⟩ : syracuseStep 3128861 = 1173323) (by norm_num)
theorem B2085907 : Blo 2085435 2085907 := bstep (se 1 (by rfl) ⟨1564430, by rfl⟩ : syracuseStep 2085907 = 3128861) B3128861
theorem B4693301 : Blo 2085435 4693301 := bbase (se 5 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 4693301 = 439997) (by norm_num)
theorem B3128867 : Blo 2085435 3128867 := bstep (se 1 (by rfl) ⟨2346650, by rfl⟩ : syracuseStep 3128867 = 4693301) B4693301
theorem B2085911 : Blo 2085435 2085911 := bstep (se 1 (by rfl) ⟨1564433, by rfl⟩ : syracuseStep 2085911 = 3128867) B3128867
theorem B2540117 : Blo 2085435 2540117 := bbase (se 8 (by rfl) ⟨14883, by rfl⟩ : syracuseStep 2540117 = 29767) (by norm_num)
theorem B6773645 : Blo 2085435 6773645 := bstep (se 3 (by rfl) ⟨1270058, by rfl⟩ : syracuseStep 6773645 = 2540117) B2540117
theorem B4515763 : Blo 2085435 4515763 := bstep (se 1 (by rfl) ⟨3386822, by rfl⟩ : syracuseStep 4515763 = 6773645) B6773645
theorem B6021017 : Blo 2085435 6021017 := bstep (se 2 (by rfl) ⟨2257881, by rfl⟩ : syracuseStep 6021017 = 4515763) B4515763
theorem B4014011 : Blo 2085435 4014011 := bstep (se 1 (by rfl) ⟨3010508, by rfl⟩ : syracuseStep 4014011 = 6021017) B6021017
theorem B2676007 : Blo 2085435 2676007 := bstep (se 1 (by rfl) ⟨2007005, by rfl⟩ : syracuseStep 2676007 = 4014011) B4014011
theorem B14272037 : Blo 2085435 14272037 := bstep (se 4 (by rfl) ⟨1338003, by rfl⟩ : syracuseStep 14272037 = 2676007) B2676007
theorem B9514691 : Blo 2085435 9514691 := bstep (se 1 (by rfl) ⟨7136018, by rfl⟩ : syracuseStep 9514691 = 14272037) B14272037
theorem B6343127 : Blo 2085435 6343127 := bstep (se 1 (by rfl) ⟨4757345, by rfl⟩ : syracuseStep 6343127 = 9514691) B9514691
theorem B4228751 : Blo 2085435 4228751 := bstep (se 1 (by rfl) ⟨3171563, by rfl⟩ : syracuseStep 4228751 = 6343127) B6343127
theorem B2819167 : Blo 2085435 2819167 := bstep (se 1 (by rfl) ⟨2114375, by rfl⟩ : syracuseStep 2819167 = 4228751) B4228751
theorem B15035557 : Blo 2085435 15035557 := bstep (se 4 (by rfl) ⟨1409583, by rfl⟩ : syracuseStep 15035557 = 2819167) B2819167
theorem B20047409 : Blo 2085435 20047409 := bstep (se 2 (by rfl) ⟨7517778, by rfl⟩ : syracuseStep 20047409 = 15035557) B15035557
theorem B13364939 : Blo 2085435 13364939 := bstep (se 1 (by rfl) ⟨10023704, by rfl⟩ : syracuseStep 13364939 = 20047409) B20047409
theorem B8909959 : Blo 2085435 8909959 := bstep (se 1 (by rfl) ⟨6682469, by rfl⟩ : syracuseStep 8909959 = 13364939) B13364939
theorem B11879945 : Blo 2085435 11879945 := bstep (se 2 (by rfl) ⟨4454979, by rfl⟩ : syracuseStep 11879945 = 8909959) B8909959
theorem B7919963 : Blo 2085435 7919963 := bstep (se 1 (by rfl) ⟨5939972, by rfl⟩ : syracuseStep 7919963 = 11879945) B11879945
theorem B5279975 : Blo 2085435 5279975 := bstep (se 1 (by rfl) ⟨3959981, by rfl⟩ : syracuseStep 5279975 = 7919963) B7919963
theorem B3519983 : Blo 2085435 3519983 := bstep (se 1 (by rfl) ⟨2639987, by rfl⟩ : syracuseStep 3519983 = 5279975) B5279975
theorem B2346655 : Blo 2085435 2346655 := bstep (se 1 (by rfl) ⟨1759991, by rfl⟩ : syracuseStep 2346655 = 3519983) B3519983
theorem B3128873 : Blo 2085435 3128873 := bstep (se 2 (by rfl) ⟨1173327, by rfl⟩ : syracuseStep 3128873 = 2346655) B2346655
theorem B2085915 : Blo 2085435 2085915 := bstep (se 1 (by rfl) ⟨1564436, by rfl⟩ : syracuseStep 2085915 = 3128873) B3128873
theorem B20047445 : Blo 2085435 20047445 := bbase (se 8 (by rfl) ⟨117465, by rfl⟩ : syracuseStep 20047445 = 234931) (by norm_num)
theorem B13364963 : Blo 2085435 13364963 := bstep (se 1 (by rfl) ⟨10023722, by rfl⟩ : syracuseStep 13364963 = 20047445) B20047445
theorem B8909975 : Blo 2085435 8909975 := bstep (se 1 (by rfl) ⟨6682481, by rfl⟩ : syracuseStep 8909975 = 13364963) B13364963
theorem B5939983 : Blo 2085435 5939983 := bstep (se 1 (by rfl) ⟨4454987, by rfl⟩ : syracuseStep 5939983 = 8909975) B8909975
theorem B7919977 : Blo 2085435 7919977 := bstep (se 2 (by rfl) ⟨2969991, by rfl⟩ : syracuseStep 7919977 = 5939983) B5939983
theorem B10559969 : Blo 2085435 10559969 := bstep (se 2 (by rfl) ⟨3959988, by rfl⟩ : syracuseStep 10559969 = 7919977) B7919977
theorem B7039979 : Blo 2085435 7039979 := bstep (se 1 (by rfl) ⟨5279984, by rfl⟩ : syracuseStep 7039979 = 10559969) B10559969
theorem B4693319 : Blo 2085435 4693319 := bstep (se 1 (by rfl) ⟨3519989, by rfl⟩ : syracuseStep 4693319 = 7039979) B7039979
theorem B3128879 : Blo 2085435 3128879 := bstep (se 1 (by rfl) ⟨2346659, by rfl⟩ : syracuseStep 3128879 = 4693319) B4693319
theorem B2085919 : Blo 2085435 2085919 := bstep (se 1 (by rfl) ⟨1564439, by rfl⟩ : syracuseStep 2085919 = 3128879) B3128879
theorem B3128885 : Blo 2085435 3128885 := bbase (se 5 (by rfl) ⟨146666, by rfl⟩ : syracuseStep 3128885 = 293333) (by norm_num)
theorem B2085923 : Blo 2085435 2085923 := bstep (se 1 (by rfl) ⟨1564442, by rfl⟩ : syracuseStep 2085923 = 3128885) B3128885
theorem B5280005 : Blo 2085435 5280005 := bbase (se 4 (by rfl) ⟨495000, by rfl⟩ : syracuseStep 5280005 = 990001) (by norm_num)
theorem B3520003 : Blo 2085435 3520003 := bstep (se 1 (by rfl) ⟨2640002, by rfl⟩ : syracuseStep 3520003 = 5280005) B5280005
theorem B4693337 : Blo 2085435 4693337 := bstep (se 2 (by rfl) ⟨1760001, by rfl⟩ : syracuseStep 4693337 = 3520003) B3520003
theorem B3128891 : Blo 2085435 3128891 := bstep (se 1 (by rfl) ⟨2346668, by rfl⟩ : syracuseStep 3128891 = 4693337) B4693337
theorem B2085927 : Blo 2085435 2085927 := bstep (se 1 (by rfl) ⟨1564445, by rfl⟩ : syracuseStep 2085927 = 3128891) B3128891
theorem B2346673 : Blo 2085435 2346673 := bbase (se 2 (by rfl) ⟨880002, by rfl⟩ : syracuseStep 2346673 = 1760005) (by norm_num)
theorem B3128897 : Blo 2085435 3128897 := bstep (se 2 (by rfl) ⟨1173336, by rfl⟩ : syracuseStep 3128897 = 2346673) B2346673
theorem B2085931 : Blo 2085435 2085931 := bstep (se 1 (by rfl) ⟨1564448, by rfl⟩ : syracuseStep 2085931 = 3128897) B3128897
theorem B5011901 : Blo 2085435 5011901 := bbase (se 3 (by rfl) ⟨939731, by rfl⟩ : syracuseStep 5011901 = 1879463) (by norm_num)
theorem B3341267 : Blo 2085435 3341267 := bstep (se 1 (by rfl) ⟨2505950, by rfl⟩ : syracuseStep 3341267 = 5011901) B5011901
theorem B2227511 : Blo 2085435 2227511 := bstep (se 1 (by rfl) ⟨1670633, by rfl⟩ : syracuseStep 2227511 = 3341267) B3341267
theorem B5940029 : Blo 2085435 5940029 := bstep (se 3 (by rfl) ⟨1113755, by rfl⟩ : syracuseStep 5940029 = 2227511) B2227511
theorem B3960019 : Blo 2085435 3960019 := bstep (se 1 (by rfl) ⟨2970014, by rfl⟩ : syracuseStep 3960019 = 5940029) B5940029
theorem B5280025 : Blo 2085435 5280025 := bstep (se 2 (by rfl) ⟨1980009, by rfl⟩ : syracuseStep 5280025 = 3960019) B3960019
theorem B7040033 : Blo 2085435 7040033 := bstep (se 2 (by rfl) ⟨2640012, by rfl⟩ : syracuseStep 7040033 = 5280025) B5280025
theorem B4693355 : Blo 2085435 4693355 := bstep (se 1 (by rfl) ⟨3520016, by rfl⟩ : syracuseStep 4693355 = 7040033) B7040033
theorem B3128903 : Blo 2085435 3128903 := bstep (se 1 (by rfl) ⟨2346677, by rfl⟩ : syracuseStep 3128903 = 4693355) B4693355
theorem B2085935 : Blo 2085435 2085935 := bstep (se 1 (by rfl) ⟨1564451, by rfl⟩ : syracuseStep 2085935 = 3128903) B3128903
theorem B3128909 : Blo 2085435 3128909 := bbase (se 3 (by rfl) ⟨586670, by rfl⟩ : syracuseStep 3128909 = 1173341) (by norm_num)
theorem B2085939 : Blo 2085435 2085939 := bstep (se 1 (by rfl) ⟨1564454, by rfl⟩ : syracuseStep 2085939 = 3128909) B3128909
theorem B4693373 : Blo 2085435 4693373 := bbase (se 3 (by rfl) ⟨880007, by rfl⟩ : syracuseStep 4693373 = 1760015) (by norm_num)
theorem B3128915 : Blo 2085435 3128915 := bstep (se 1 (by rfl) ⟨2346686, by rfl⟩ : syracuseStep 3128915 = 4693373) B4693373
theorem B2085943 : Blo 2085435 2085943 := bstep (se 1 (by rfl) ⟨1564457, by rfl⟩ : syracuseStep 2085943 = 3128915) B3128915
theorem B3520037 : Blo 2085435 3520037 := bbase (se 4 (by rfl) ⟨330003, by rfl⟩ : syracuseStep 3520037 = 660007) (by norm_num)
theorem B2346691 : Blo 2085435 2346691 := bstep (se 1 (by rfl) ⟨1760018, by rfl⟩ : syracuseStep 2346691 = 3520037) B3520037
theorem B3128921 : Blo 2085435 3128921 := bstep (se 2 (by rfl) ⟨1173345, by rfl⟩ : syracuseStep 3128921 = 2346691) B2346691
theorem B2085947 : Blo 2085435 2085947 := bstep (se 1 (by rfl) ⟨1564460, by rfl⟩ : syracuseStep 2085947 = 3128921) B3128921
theorem B2970037 : Blo 2085435 2970037 := bbase (se 5 (by rfl) ⟨139220, by rfl⟩ : syracuseStep 2970037 = 278441) (by norm_num)
theorem B15840197 : Blo 2085435 15840197 := bstep (se 4 (by rfl) ⟨1485018, by rfl⟩ : syracuseStep 15840197 = 2970037) B2970037
theorem B10560131 : Blo 2085435 10560131 := bstep (se 1 (by rfl) ⟨7920098, by rfl⟩ : syracuseStep 10560131 = 15840197) B15840197
theorem B7040087 : Blo 2085435 7040087 := bstep (se 1 (by rfl) ⟨5280065, by rfl⟩ : syracuseStep 7040087 = 10560131) B10560131
theorem B4693391 : Blo 2085435 4693391 := bstep (se 1 (by rfl) ⟨3520043, by rfl⟩ : syracuseStep 4693391 = 7040087) B7040087
theorem B3128927 : Blo 2085435 3128927 := bstep (se 1 (by rfl) ⟨2346695, by rfl⟩ : syracuseStep 3128927 = 4693391) B4693391
theorem B2085951 : Blo 2085435 2085951 := bstep (se 1 (by rfl) ⟨1564463, by rfl⟩ : syracuseStep 2085951 = 3128927) B3128927
theorem B3128933 : Blo 2085435 3128933 := bbase (se 4 (by rfl) ⟨293337, by rfl⟩ : syracuseStep 3128933 = 586675) (by norm_num)
theorem B2085955 : Blo 2085435 2085955 := bstep (se 1 (by rfl) ⟨1564466, by rfl⟩ : syracuseStep 2085955 = 3128933) B3128933
theorem B2227537 : Blo 2085435 2227537 := bbase (se 2 (by rfl) ⟨835326, by rfl⟩ : syracuseStep 2227537 = 1670653) (by norm_num)
theorem B2970049 : Blo 2085435 2970049 := bstep (se 2 (by rfl) ⟨1113768, by rfl⟩ : syracuseStep 2970049 = 2227537) B2227537
theorem B3960065 : Blo 2085435 3960065 := bstep (se 2 (by rfl) ⟨1485024, by rfl⟩ : syracuseStep 3960065 = 2970049) B2970049
theorem B2640043 : Blo 2085435 2640043 := bstep (se 1 (by rfl) ⟨1980032, by rfl⟩ : syracuseStep 2640043 = 3960065) B3960065
theorem B3520057 : Blo 2085435 3520057 := bstep (se 2 (by rfl) ⟨1320021, by rfl⟩ : syracuseStep 3520057 = 2640043) B2640043
theorem B4693409 : Blo 2085435 4693409 := bstep (se 2 (by rfl) ⟨1760028, by rfl⟩ : syracuseStep 4693409 = 3520057) B3520057
theorem B3128939 : Blo 2085435 3128939 := bstep (se 1 (by rfl) ⟨2346704, by rfl⟩ : syracuseStep 3128939 = 4693409) B4693409
theorem B2085959 : Blo 2085435 2085959 := bstep (se 1 (by rfl) ⟨1564469, by rfl⟩ : syracuseStep 2085959 = 3128939) B3128939
theorem B2346709 : Blo 2085435 2346709 := bbase (se 7 (by rfl) ⟨27500, by rfl⟩ : syracuseStep 2346709 = 55001) (by norm_num)
theorem B3128945 : Blo 2085435 3128945 := bstep (se 2 (by rfl) ⟨1173354, by rfl⟩ : syracuseStep 3128945 = 2346709) B2346709
theorem B2085963 : Blo 2085435 2085963 := bstep (se 1 (by rfl) ⟨1564472, by rfl⟩ : syracuseStep 2085963 = 3128945) B3128945
theorem B2640053 : Blo 2085435 2640053 := bbase (se 5 (by rfl) ⟨123752, by rfl⟩ : syracuseStep 2640053 = 247505) (by norm_num)
theorem B7040141 : Blo 2085435 7040141 := bstep (se 3 (by rfl) ⟨1320026, by rfl⟩ : syracuseStep 7040141 = 2640053) B2640053
theorem B4693427 : Blo 2085435 4693427 := bstep (se 1 (by rfl) ⟨3520070, by rfl⟩ : syracuseStep 4693427 = 7040141) B7040141
theorem B3128951 : Blo 2085435 3128951 := bstep (se 1 (by rfl) ⟨2346713, by rfl⟩ : syracuseStep 3128951 = 4693427) B4693427
theorem B2085967 : Blo 2085435 2085967 := bstep (se 1 (by rfl) ⟨1564475, by rfl⟩ : syracuseStep 2085967 = 3128951) B3128951
theorem B3128957 : Blo 2085435 3128957 := bbase (se 3 (by rfl) ⟨586679, by rfl⟩ : syracuseStep 3128957 = 1173359) (by norm_num)
theorem B2085971 : Blo 2085435 2085971 := bstep (se 1 (by rfl) ⟨1564478, by rfl⟩ : syracuseStep 2085971 = 3128957) B3128957
theorem B4693445 : Blo 2085435 4693445 := bbase (se 4 (by rfl) ⟨440010, by rfl⟩ : syracuseStep 4693445 = 880021) (by norm_num)
theorem B3128963 : Blo 2085435 3128963 := bstep (se 1 (by rfl) ⟨2346722, by rfl⟩ : syracuseStep 3128963 = 4693445) B4693445
theorem B2085975 : Blo 2085435 2085975 := bstep (se 1 (by rfl) ⟨1564481, by rfl⟩ : syracuseStep 2085975 = 3128963) B3128963
theorem B3759005 : Blo 2085435 3759005 := bbase (se 3 (by rfl) ⟨704813, by rfl⟩ : syracuseStep 3759005 = 1409627) (by norm_num)
theorem B10024013 : Blo 2085435 10024013 := bstep (se 3 (by rfl) ⟨1879502, by rfl⟩ : syracuseStep 10024013 = 3759005) B3759005
theorem B6682675 : Blo 2085435 6682675 := bstep (se 1 (by rfl) ⟨5012006, by rfl⟩ : syracuseStep 6682675 = 10024013) B10024013
theorem B8910233 : Blo 2085435 8910233 := bstep (se 2 (by rfl) ⟨3341337, by rfl⟩ : syracuseStep 8910233 = 6682675) B6682675
theorem B5940155 : Blo 2085435 5940155 := bstep (se 1 (by rfl) ⟨4455116, by rfl⟩ : syracuseStep 5940155 = 8910233) B8910233
theorem B3960103 : Blo 2085435 3960103 := bstep (se 1 (by rfl) ⟨2970077, by rfl⟩ : syracuseStep 3960103 = 5940155) B5940155
theorem B5280137 : Blo 2085435 5280137 := bstep (se 2 (by rfl) ⟨1980051, by rfl⟩ : syracuseStep 5280137 = 3960103) B3960103
theorem B3520091 : Blo 2085435 3520091 := bstep (se 1 (by rfl) ⟨2640068, by rfl⟩ : syracuseStep 3520091 = 5280137) B5280137
theorem B2346727 : Blo 2085435 2346727 := bstep (se 1 (by rfl) ⟨1760045, by rfl⟩ : syracuseStep 2346727 = 3520091) B3520091
theorem B3128969 : Blo 2085435 3128969 := bstep (se 2 (by rfl) ⟨1173363, by rfl⟩ : syracuseStep 3128969 = 2346727) B2346727
theorem B2085979 : Blo 2085435 2085979 := bstep (se 1 (by rfl) ⟨1564484, by rfl⟩ : syracuseStep 2085979 = 3128969) B3128969
theorem B10560293 : Blo 2085435 10560293 := bbase (se 4 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 10560293 = 1980055) (by norm_num)
theorem B7040195 : Blo 2085435 7040195 := bstep (se 1 (by rfl) ⟨5280146, by rfl⟩ : syracuseStep 7040195 = 10560293) B10560293
theorem B4693463 : Blo 2085435 4693463 := bstep (se 1 (by rfl) ⟨3520097, by rfl⟩ : syracuseStep 4693463 = 7040195) B7040195
theorem B3128975 : Blo 2085435 3128975 := bstep (se 1 (by rfl) ⟨2346731, by rfl⟩ : syracuseStep 3128975 = 4693463) B4693463
theorem B2085983 : Blo 2085435 2085983 := bstep (se 1 (by rfl) ⟨1564487, by rfl⟩ : syracuseStep 2085983 = 3128975) B3128975
theorem B3128981 : Blo 2085435 3128981 := bbase (se 6 (by rfl) ⟨73335, by rfl⟩ : syracuseStep 3128981 = 146671) (by norm_num)
theorem B2085987 : Blo 2085435 2085987 := bstep (se 1 (by rfl) ⟨1564490, by rfl⟩ : syracuseStep 2085987 = 3128981) B3128981
theorem B10024069 : Blo 2085435 10024069 := bbase (se 4 (by rfl) ⟨939756, by rfl⟩ : syracuseStep 10024069 = 1879513) (by norm_num)
theorem B13365425 : Blo 2085435 13365425 := bstep (se 2 (by rfl) ⟨5012034, by rfl⟩ : syracuseStep 13365425 = 10024069) B10024069
theorem B8910283 : Blo 2085435 8910283 := bstep (se 1 (by rfl) ⟨6682712, by rfl⟩ : syracuseStep 8910283 = 13365425) B13365425
theorem B11880377 : Blo 2085435 11880377 := bstep (se 2 (by rfl) ⟨4455141, by rfl⟩ : syracuseStep 11880377 = 8910283) B8910283
theorem B7920251 : Blo 2085435 7920251 := bstep (se 1 (by rfl) ⟨5940188, by rfl⟩ : syracuseStep 7920251 = 11880377) B11880377
theorem B5280167 : Blo 2085435 5280167 := bstep (se 1 (by rfl) ⟨3960125, by rfl⟩ : syracuseStep 5280167 = 7920251) B7920251
theorem B3520111 : Blo 2085435 3520111 := bstep (se 1 (by rfl) ⟨2640083, by rfl⟩ : syracuseStep 3520111 = 5280167) B5280167
theorem B4693481 : Blo 2085435 4693481 := bstep (se 2 (by rfl) ⟨1760055, by rfl⟩ : syracuseStep 4693481 = 3520111) B3520111
theorem B3128987 : Blo 2085435 3128987 := bstep (se 1 (by rfl) ⟨2346740, by rfl⟩ : syracuseStep 3128987 = 4693481) B4693481
theorem B2085991 : Blo 2085435 2085991 := bstep (se 1 (by rfl) ⟨1564493, by rfl⟩ : syracuseStep 2085991 = 3128987) B3128987
theorem B2346745 : Blo 2085435 2346745 := bbase (se 2 (by rfl) ⟨880029, by rfl⟩ : syracuseStep 2346745 = 1760059) (by norm_num)
theorem B3128993 : Blo 2085435 3128993 := bstep (se 2 (by rfl) ⟨1173372, by rfl⟩ : syracuseStep 3128993 = 2346745) B2346745
theorem B2085995 : Blo 2085435 2085995 := bstep (se 1 (by rfl) ⟨1564496, by rfl⟩ : syracuseStep 2085995 = 3128993) B3128993
theorem B2114461 : Blo 2085435 2114461 := bbase (se 3 (by rfl) ⟨396461, by rfl⟩ : syracuseStep 2114461 = 792923) (by norm_num)
theorem B2819281 : Blo 2085435 2819281 := bstep (se 2 (by rfl) ⟨1057230, by rfl⟩ : syracuseStep 2819281 = 2114461) B2114461
theorem B3759041 : Blo 2085435 3759041 := bstep (se 2 (by rfl) ⟨1409640, by rfl⟩ : syracuseStep 3759041 = 2819281) B2819281
theorem B2506027 : Blo 2085435 2506027 := bstep (se 1 (by rfl) ⟨1879520, by rfl⟩ : syracuseStep 2506027 = 3759041) B3759041
theorem B3341369 : Blo 2085435 3341369 := bstep (se 2 (by rfl) ⟨1253013, by rfl⟩ : syracuseStep 3341369 = 2506027) B2506027
theorem B8910317 : Blo 2085435 8910317 := bstep (se 3 (by rfl) ⟨1670684, by rfl⟩ : syracuseStep 8910317 = 3341369) B3341369
theorem B5940211 : Blo 2085435 5940211 := bstep (se 1 (by rfl) ⟨4455158, by rfl⟩ : syracuseStep 5940211 = 8910317) B8910317
theorem B7920281 : Blo 2085435 7920281 := bstep (se 2 (by rfl) ⟨2970105, by rfl⟩ : syracuseStep 7920281 = 5940211) B5940211
theorem B5280187 : Blo 2085435 5280187 := bstep (se 1 (by rfl) ⟨3960140, by rfl⟩ : syracuseStep 5280187 = 7920281) B7920281
theorem B7040249 : Blo 2085435 7040249 := bstep (se 2 (by rfl) ⟨2640093, by rfl⟩ : syracuseStep 7040249 = 5280187) B5280187
theorem B4693499 : Blo 2085435 4693499 := bstep (se 1 (by rfl) ⟨3520124, by rfl⟩ : syracuseStep 4693499 = 7040249) B7040249
theorem B3128999 : Blo 2085435 3128999 := bstep (se 1 (by rfl) ⟨2346749, by rfl⟩ : syracuseStep 3128999 = 4693499) B4693499
theorem B2085999 : Blo 2085435 2085999 := bstep (se 1 (by rfl) ⟨1564499, by rfl⟩ : syracuseStep 2085999 = 3128999) B3128999
theorem B3129005 : Blo 2085435 3129005 := bbase (se 3 (by rfl) ⟨586688, by rfl⟩ : syracuseStep 3129005 = 1173377) (by norm_num)
theorem B2086003 : Blo 2085435 2086003 := bstep (se 1 (by rfl) ⟨1564502, by rfl⟩ : syracuseStep 2086003 = 3129005) B3129005
theorem B4693517 : Blo 2085435 4693517 := bbase (se 3 (by rfl) ⟨880034, by rfl⟩ : syracuseStep 4693517 = 1760069) (by norm_num)
theorem B3129011 : Blo 2085435 3129011 := bstep (se 1 (by rfl) ⟨2346758, by rfl⟩ : syracuseStep 3129011 = 4693517) B4693517
theorem B2086007 : Blo 2085435 2086007 := bstep (se 1 (by rfl) ⟨1564505, by rfl⟩ : syracuseStep 2086007 = 3129011) B3129011
theorem B2640109 : Blo 2085435 2640109 := bbase (se 3 (by rfl) ⟨495020, by rfl⟩ : syracuseStep 2640109 = 990041) (by norm_num)
theorem B3520145 : Blo 2085435 3520145 := bstep (se 2 (by rfl) ⟨1320054, by rfl⟩ : syracuseStep 3520145 = 2640109) B2640109
theorem B2346763 : Blo 2085435 2346763 := bstep (se 1 (by rfl) ⟨1760072, by rfl⟩ : syracuseStep 2346763 = 3520145) B3520145
theorem B3129017 : Blo 2085435 3129017 := bstep (se 2 (by rfl) ⟨1173381, by rfl⟩ : syracuseStep 3129017 = 2346763) B2346763
theorem B2086011 : Blo 2085435 2086011 := bstep (se 1 (by rfl) ⟨1564508, by rfl⟩ : syracuseStep 2086011 = 3129017) B3129017
theorem B6343429 : Blo 2085435 6343429 := bbase (se 4 (by rfl) ⟨594696, by rfl⟩ : syracuseStep 6343429 = 1189393) (by norm_num)
theorem B8457905 : Blo 2085435 8457905 := bstep (se 2 (by rfl) ⟨3171714, by rfl⟩ : syracuseStep 8457905 = 6343429) B6343429
theorem B22554413 : Blo 2085435 22554413 := bstep (se 3 (by rfl) ⟨4228952, by rfl⟩ : syracuseStep 22554413 = 8457905) B8457905
theorem B15036275 : Blo 2085435 15036275 := bstep (se 1 (by rfl) ⟨11277206, by rfl⟩ : syracuseStep 15036275 = 22554413) B22554413
theorem B10024183 : Blo 2085435 10024183 := bstep (se 1 (by rfl) ⟨7518137, by rfl⟩ : syracuseStep 10024183 = 15036275) B15036275
theorem B13365577 : Blo 2085435 13365577 := bstep (se 2 (by rfl) ⟨5012091, by rfl⟩ : syracuseStep 13365577 = 10024183) B10024183
theorem B17820769 : Blo 2085435 17820769 := bstep (se 2 (by rfl) ⟨6682788, by rfl⟩ : syracuseStep 17820769 = 13365577) B13365577
theorem B23761025 : Blo 2085435 23761025 := bstep (se 2 (by rfl) ⟨8910384, by rfl⟩ : syracuseStep 23761025 = 17820769) B17820769
theorem B15840683 : Blo 2085435 15840683 := bstep (se 1 (by rfl) ⟨11880512, by rfl⟩ : syracuseStep 15840683 = 23761025) B23761025
theorem B10560455 : Blo 2085435 10560455 := bstep (se 1 (by rfl) ⟨7920341, by rfl⟩ : syracuseStep 10560455 = 15840683) B15840683
theorem B7040303 : Blo 2085435 7040303 := bstep (se 1 (by rfl) ⟨5280227, by rfl⟩ : syracuseStep 7040303 = 10560455) B10560455
theorem B4693535 : Blo 2085435 4693535 := bstep (se 1 (by rfl) ⟨3520151, by rfl⟩ : syracuseStep 4693535 = 7040303) B7040303
theorem B3129023 : Blo 2085435 3129023 := bstep (se 1 (by rfl) ⟨2346767, by rfl⟩ : syracuseStep 3129023 = 4693535) B4693535
theorem B2086015 : Blo 2085435 2086015 := bstep (se 1 (by rfl) ⟨1564511, by rfl⟩ : syracuseStep 2086015 = 3129023) B3129023
theorem B3129029 : Blo 2085435 3129029 := bbase (se 4 (by rfl) ⟨293346, by rfl⟩ : syracuseStep 3129029 = 586693) (by norm_num)
theorem B2086019 : Blo 2085435 2086019 := bstep (se 1 (by rfl) ⟨1564514, by rfl⟩ : syracuseStep 2086019 = 3129029) B3129029
theorem B3520165 : Blo 2085435 3520165 := bbase (se 4 (by rfl) ⟨330015, by rfl⟩ : syracuseStep 3520165 = 660031) (by norm_num)
theorem B4693553 : Blo 2085435 4693553 := bstep (se 2 (by rfl) ⟨1760082, by rfl⟩ : syracuseStep 4693553 = 3520165) B3520165
theorem B3129035 : Blo 2085435 3129035 := bstep (se 1 (by rfl) ⟨2346776, by rfl⟩ : syracuseStep 3129035 = 4693553) B4693553
theorem B2086023 : Blo 2085435 2086023 := bstep (se 1 (by rfl) ⟨1564517, by rfl⟩ : syracuseStep 2086023 = 3129035) B3129035
theorem B2346781 : Blo 2085435 2346781 := bbase (se 3 (by rfl) ⟨440021, by rfl⟩ : syracuseStep 2346781 = 880043) (by norm_num)
theorem B3129041 : Blo 2085435 3129041 := bstep (se 2 (by rfl) ⟨1173390, by rfl⟩ : syracuseStep 3129041 = 2346781) B2346781
theorem B2086027 : Blo 2085435 2086027 := bstep (se 1 (by rfl) ⟨1564520, by rfl⟩ : syracuseStep 2086027 = 3129041) B3129041
theorem B7040357 : Blo 2085435 7040357 := bbase (se 4 (by rfl) ⟨660033, by rfl⟩ : syracuseStep 7040357 = 1320067) (by norm_num)
theorem B4693571 : Blo 2085435 4693571 := bstep (se 1 (by rfl) ⟨3520178, by rfl⟩ : syracuseStep 4693571 = 7040357) B7040357
theorem B3129047 : Blo 2085435 3129047 := bstep (se 1 (by rfl) ⟨2346785, by rfl⟩ : syracuseStep 3129047 = 4693571) B4693571
theorem B2086031 : Blo 2085435 2086031 := bstep (se 1 (by rfl) ⟨1564523, by rfl⟩ : syracuseStep 2086031 = 3129047) B3129047
theorem B3129053 : Blo 2085435 3129053 := bbase (se 3 (by rfl) ⟨586697, by rfl⟩ : syracuseStep 3129053 = 1173395) (by norm_num)
theorem B2086035 : Blo 2085435 2086035 := bstep (se 1 (by rfl) ⟨1564526, by rfl⟩ : syracuseStep 2086035 = 3129053) B3129053
theorem B4693589 : Blo 2085435 4693589 := bbase (se 8 (by rfl) ⟨27501, by rfl⟩ : syracuseStep 4693589 = 55003) (by norm_num)
theorem B3129059 : Blo 2085435 3129059 := bstep (se 1 (by rfl) ⟨2346794, by rfl⟩ : syracuseStep 3129059 = 4693589) B4693589
theorem B2086039 : Blo 2085435 2086039 := bstep (se 1 (by rfl) ⟨1564529, by rfl⟩ : syracuseStep 2086039 = 3129059) B3129059
theorem B4455253 : Blo 2085435 4455253 := bbase (se 9 (by rfl) ⟨13052, by rfl⟩ : syracuseStep 4455253 = 26105) (by norm_num)
theorem B5940337 : Blo 2085435 5940337 := bstep (se 2 (by rfl) ⟨2227626, by rfl⟩ : syracuseStep 5940337 = 4455253) B4455253
theorem B7920449 : Blo 2085435 7920449 := bstep (se 2 (by rfl) ⟨2970168, by rfl⟩ : syracuseStep 7920449 = 5940337) B5940337
theorem B5280299 : Blo 2085435 5280299 := bstep (se 1 (by rfl) ⟨3960224, by rfl⟩ : syracuseStep 5280299 = 7920449) B7920449
theorem B3520199 : Blo 2085435 3520199 := bstep (se 1 (by rfl) ⟨2640149, by rfl⟩ : syracuseStep 3520199 = 5280299) B5280299
theorem B2346799 : Blo 2085435 2346799 := bstep (se 1 (by rfl) ⟨1760099, by rfl⟩ : syracuseStep 2346799 = 3520199) B3520199
theorem B3129065 : Blo 2085435 3129065 := bstep (se 2 (by rfl) ⟨1173399, by rfl⟩ : syracuseStep 3129065 = 2346799) B2346799
theorem B2086043 : Blo 2085435 2086043 := bstep (se 1 (by rfl) ⟨1564532, by rfl⟩ : syracuseStep 2086043 = 3129065) B3129065
theorem B2114509 : Blo 2085435 2114509 := bbase (se 3 (by rfl) ⟨396470, by rfl⟩ : syracuseStep 2114509 = 792941) (by norm_num)
theorem B2819345 : Blo 2085435 2819345 := bstep (se 2 (by rfl) ⟨1057254, by rfl⟩ : syracuseStep 2819345 = 2114509) B2114509
theorem B7518253 : Blo 2085435 7518253 := bstep (se 3 (by rfl) ⟨1409672, by rfl⟩ : syracuseStep 7518253 = 2819345) B2819345
theorem B10024337 : Blo 2085435 10024337 := bstep (se 2 (by rfl) ⟨3759126, by rfl⟩ : syracuseStep 10024337 = 7518253) B7518253
theorem B26731565 : Blo 2085435 26731565 := bstep (se 3 (by rfl) ⟨5012168, by rfl⟩ : syracuseStep 26731565 = 10024337) B10024337
theorem B17821043 : Blo 2085435 17821043 := bstep (se 1 (by rfl) ⟨13365782, by rfl⟩ : syracuseStep 17821043 = 26731565) B26731565
theorem B11880695 : Blo 2085435 11880695 := bstep (se 1 (by rfl) ⟨8910521, by rfl⟩ : syracuseStep 11880695 = 17821043) B17821043
theorem B7920463 : Blo 2085435 7920463 := bstep (se 1 (by rfl) ⟨5940347, by rfl⟩ : syracuseStep 7920463 = 11880695) B11880695
theorem B10560617 : Blo 2085435 10560617 := bstep (se 2 (by rfl) ⟨3960231, by rfl⟩ : syracuseStep 10560617 = 7920463) B7920463
theorem B7040411 : Blo 2085435 7040411 := bstep (se 1 (by rfl) ⟨5280308, by rfl⟩ : syracuseStep 7040411 = 10560617) B10560617
theorem B4693607 : Blo 2085435 4693607 := bstep (se 1 (by rfl) ⟨3520205, by rfl⟩ : syracuseStep 4693607 = 7040411) B7040411
theorem B3129071 : Blo 2085435 3129071 := bstep (se 1 (by rfl) ⟨2346803, by rfl⟩ : syracuseStep 3129071 = 4693607) B4693607
theorem B2086047 : Blo 2085435 2086047 := bstep (se 1 (by rfl) ⟨1564535, by rfl⟩ : syracuseStep 2086047 = 3129071) B3129071
theorem B3129077 : Blo 2085435 3129077 := bbase (se 5 (by rfl) ⟨146675, by rfl⟩ : syracuseStep 3129077 = 293351) (by norm_num)
theorem B2086051 : Blo 2085435 2086051 := bstep (se 1 (by rfl) ⟨1564538, by rfl⟩ : syracuseStep 2086051 = 3129077) B3129077
theorem B5012189 : Blo 2085435 5012189 := bbase (se 3 (by rfl) ⟨939785, by rfl⟩ : syracuseStep 5012189 = 1879571) (by norm_num)
theorem B3341459 : Blo 2085435 3341459 := bstep (se 1 (by rfl) ⟨2506094, by rfl⟩ : syracuseStep 3341459 = 5012189) B5012189
theorem B8910557 : Blo 2085435 8910557 := bstep (se 3 (by rfl) ⟨1670729, by rfl⟩ : syracuseStep 8910557 = 3341459) B3341459
theorem B5940371 : Blo 2085435 5940371 := bstep (se 1 (by rfl) ⟨4455278, by rfl⟩ : syracuseStep 5940371 = 8910557) B8910557
theorem B3960247 : Blo 2085435 3960247 := bstep (se 1 (by rfl) ⟨2970185, by rfl⟩ : syracuseStep 3960247 = 5940371) B5940371
theorem B5280329 : Blo 2085435 5280329 := bstep (se 2 (by rfl) ⟨1980123, by rfl⟩ : syracuseStep 5280329 = 3960247) B3960247
theorem B3520219 : Blo 2085435 3520219 := bstep (se 1 (by rfl) ⟨2640164, by rfl⟩ : syracuseStep 3520219 = 5280329) B5280329
theorem B4693625 : Blo 2085435 4693625 := bstep (se 2 (by rfl) ⟨1760109, by rfl⟩ : syracuseStep 4693625 = 3520219) B3520219
theorem B3129083 : Blo 2085435 3129083 := bstep (se 1 (by rfl) ⟨2346812, by rfl⟩ : syracuseStep 3129083 = 4693625) B4693625
theorem B2086055 : Blo 2085435 2086055 := bstep (se 1 (by rfl) ⟨1564541, by rfl⟩ : syracuseStep 2086055 = 3129083) B3129083
theorem B2346817 : Blo 2085435 2346817 := bbase (se 2 (by rfl) ⟨880056, by rfl⟩ : syracuseStep 2346817 = 1760113) (by norm_num)
theorem B3129089 : Blo 2085435 3129089 := bstep (se 2 (by rfl) ⟨1173408, by rfl⟩ : syracuseStep 3129089 = 2346817) B2346817
theorem B2086059 : Blo 2085435 2086059 := bstep (se 1 (by rfl) ⟨1564544, by rfl⟩ : syracuseStep 2086059 = 3129089) B3129089
theorem B5280349 : Blo 2085435 5280349 := bbase (se 3 (by rfl) ⟨990065, by rfl⟩ : syracuseStep 5280349 = 1980131) (by norm_num)
theorem B7040465 : Blo 2085435 7040465 := bstep (se 2 (by rfl) ⟨2640174, by rfl⟩ : syracuseStep 7040465 = 5280349) B5280349
theorem B4693643 : Blo 2085435 4693643 := bstep (se 1 (by rfl) ⟨3520232, by rfl⟩ : syracuseStep 4693643 = 7040465) B7040465
theorem B3129095 : Blo 2085435 3129095 := bstep (se 1 (by rfl) ⟨2346821, by rfl⟩ : syracuseStep 3129095 = 4693643) B4693643
theorem B2086063 : Blo 2085435 2086063 := bstep (se 1 (by rfl) ⟨1564547, by rfl⟩ : syracuseStep 2086063 = 3129095) B3129095
theorem B3129101 : Blo 2085435 3129101 := bbase (se 3 (by rfl) ⟨586706, by rfl⟩ : syracuseStep 3129101 = 1173413) (by norm_num)
theorem B2086067 : Blo 2085435 2086067 := bstep (se 1 (by rfl) ⟨1564550, by rfl⟩ : syracuseStep 2086067 = 3129101) B3129101
theorem B4693661 : Blo 2085435 4693661 := bbase (se 3 (by rfl) ⟨880061, by rfl⟩ : syracuseStep 4693661 = 1760123) (by norm_num)
theorem B3129107 : Blo 2085435 3129107 := bstep (se 1 (by rfl) ⟨2346830, by rfl⟩ : syracuseStep 3129107 = 4693661) B4693661
theorem B2086071 : Blo 2085435 2086071 := bstep (se 1 (by rfl) ⟨1564553, by rfl⟩ : syracuseStep 2086071 = 3129107) B3129107
theorem B3520253 : Blo 2085435 3520253 := bbase (se 3 (by rfl) ⟨660047, by rfl⟩ : syracuseStep 3520253 = 1320095) (by norm_num)
theorem B2346835 : Blo 2085435 2346835 := bstep (se 1 (by rfl) ⟨1760126, by rfl⟩ : syracuseStep 2346835 = 3520253) B3520253
theorem B3129113 : Blo 2085435 3129113 := bstep (se 2 (by rfl) ⟨1173417, by rfl⟩ : syracuseStep 3129113 = 2346835) B2346835
theorem B2086075 : Blo 2085435 2086075 := bstep (se 1 (by rfl) ⟨1564556, by rfl⟩ : syracuseStep 2086075 = 3129113) B3129113
theorem B2819389 : Blo 2085435 2819389 := bbase (se 3 (by rfl) ⟨528635, by rfl⟩ : syracuseStep 2819389 = 1057271) (by norm_num)
theorem B3759185 : Blo 2085435 3759185 := bstep (se 2 (by rfl) ⟨1409694, by rfl⟩ : syracuseStep 3759185 = 2819389) B2819389
theorem B2506123 : Blo 2085435 2506123 := bstep (se 1 (by rfl) ⟨1879592, by rfl⟩ : syracuseStep 2506123 = 3759185) B3759185
theorem B3341497 : Blo 2085435 3341497 := bstep (se 2 (by rfl) ⟨1253061, by rfl⟩ : syracuseStep 3341497 = 2506123) B2506123
theorem B4455329 : Blo 2085435 4455329 := bstep (se 2 (by rfl) ⟨1670748, by rfl⟩ : syracuseStep 4455329 = 3341497) B3341497
theorem B11880877 : Blo 2085435 11880877 := bstep (se 3 (by rfl) ⟨2227664, by rfl⟩ : syracuseStep 11880877 = 4455329) B4455329
theorem B15841169 : Blo 2085435 15841169 := bstep (se 2 (by rfl) ⟨5940438, by rfl⟩ : syracuseStep 15841169 = 11880877) B11880877
theorem B10560779 : Blo 2085435 10560779 := bstep (se 1 (by rfl) ⟨7920584, by rfl⟩ : syracuseStep 10560779 = 15841169) B15841169
theorem B7040519 : Blo 2085435 7040519 := bstep (se 1 (by rfl) ⟨5280389, by rfl⟩ : syracuseStep 7040519 = 10560779) B10560779
theorem B4693679 : Blo 2085435 4693679 := bstep (se 1 (by rfl) ⟨3520259, by rfl⟩ : syracuseStep 4693679 = 7040519) B7040519
theorem B3129119 : Blo 2085435 3129119 := bstep (se 1 (by rfl) ⟨2346839, by rfl⟩ : syracuseStep 3129119 = 4693679) B4693679
theorem B2086079 : Blo 2085435 2086079 := bstep (se 1 (by rfl) ⟨1564559, by rfl⟩ : syracuseStep 2086079 = 3129119) B3129119
theorem B3129125 : Blo 2085435 3129125 := bbase (se 4 (by rfl) ⟨293355, by rfl⟩ : syracuseStep 3129125 = 586711) (by norm_num)
theorem B2086083 : Blo 2085435 2086083 := bstep (se 1 (by rfl) ⟨1564562, by rfl⟩ : syracuseStep 2086083 = 3129125) B3129125
theorem B2640205 : Blo 2085435 2640205 := bbase (se 3 (by rfl) ⟨495038, by rfl⟩ : syracuseStep 2640205 = 990077) (by norm_num)
theorem B3520273 : Blo 2085435 3520273 := bstep (se 2 (by rfl) ⟨1320102, by rfl⟩ : syracuseStep 3520273 = 2640205) B2640205
theorem B4693697 : Blo 2085435 4693697 := bstep (se 2 (by rfl) ⟨1760136, by rfl⟩ : syracuseStep 4693697 = 3520273) B3520273
theorem B3129131 : Blo 2085435 3129131 := bstep (se 1 (by rfl) ⟨2346848, by rfl⟩ : syracuseStep 3129131 = 4693697) B4693697
theorem B2086087 : Blo 2085435 2086087 := bstep (se 1 (by rfl) ⟨1564565, by rfl⟩ : syracuseStep 2086087 = 3129131) B3129131
theorem B2346853 : Blo 2085435 2346853 := bbase (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) (by norm_num)
theorem B3129137 : Blo 2085435 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B2086091 : Blo 2085435 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B5940485 : Blo 2085435 5940485 := bbase (se 4 (by rfl) ⟨556920, by rfl⟩ : syracuseStep 5940485 = 1113841) (by norm_num)
theorem B3960323 : Blo 2085435 3960323 := bstep (se 1 (by rfl) ⟨2970242, by rfl⟩ : syracuseStep 3960323 = 5940485) B5940485
theorem B2640215 : Blo 2085435 2640215 := bstep (se 1 (by rfl) ⟨1980161, by rfl⟩ : syracuseStep 2640215 = 3960323) B3960323
theorem B7040573 : Blo 2085435 7040573 := bstep (se 3 (by rfl) ⟨1320107, by rfl⟩ : syracuseStep 7040573 = 2640215) B2640215
theorem B4693715 : Blo 2085435 4693715 := bstep (se 1 (by rfl) ⟨3520286, by rfl⟩ : syracuseStep 4693715 = 7040573) B7040573
theorem B3129143 : Blo 2085435 3129143 := bstep (se 1 (by rfl) ⟨2346857, by rfl⟩ : syracuseStep 3129143 = 4693715) B4693715
theorem B2086095 : Blo 2085435 2086095 := bstep (se 1 (by rfl) ⟨1564571, by rfl⟩ : syracuseStep 2086095 = 3129143) B3129143
theorem B3129149 : Blo 2085435 3129149 := bbase (se 3 (by rfl) ⟨586715, by rfl⟩ : syracuseStep 3129149 = 1173431) (by norm_num)
theorem B2086099 : Blo 2085435 2086099 := bstep (se 1 (by rfl) ⟨1564574, by rfl⟩ : syracuseStep 2086099 = 3129149) B3129149
theorem B4693733 : Blo 2085435 4693733 := bbase (se 4 (by rfl) ⟨440037, by rfl⟩ : syracuseStep 4693733 = 880075) (by norm_num)
theorem B3129155 : Blo 2085435 3129155 := bstep (se 1 (by rfl) ⟨2346866, by rfl⟩ : syracuseStep 3129155 = 4693733) B4693733
theorem B2086103 : Blo 2085435 2086103 := bstep (se 1 (by rfl) ⟨1564577, by rfl⟩ : syracuseStep 2086103 = 3129155) B3129155
theorem B5280461 : Blo 2085435 5280461 := bbase (se 3 (by rfl) ⟨990086, by rfl⟩ : syracuseStep 5280461 = 1980173) (by norm_num)
theorem B3520307 : Blo 2085435 3520307 := bstep (se 1 (by rfl) ⟨2640230, by rfl⟩ : syracuseStep 3520307 = 5280461) B5280461
theorem B2346871 : Blo 2085435 2346871 := bstep (se 1 (by rfl) ⟨1760153, by rfl⟩ : syracuseStep 2346871 = 3520307) B3520307
theorem B3129161 : Blo 2085435 3129161 := bstep (se 2 (by rfl) ⟨1173435, by rfl⟩ : syracuseStep 3129161 = 2346871) B2346871
theorem B2086107 : Blo 2085435 2086107 := bstep (se 1 (by rfl) ⟨1564580, by rfl⟩ : syracuseStep 2086107 = 3129161) B3129161
theorem B3341549 : Blo 2085435 3341549 := bbase (se 3 (by rfl) ⟨626540, by rfl⟩ : syracuseStep 3341549 = 1253081) (by norm_num)
theorem B2227699 : Blo 2085435 2227699 := bstep (se 1 (by rfl) ⟨1670774, by rfl⟩ : syracuseStep 2227699 = 3341549) B3341549
theorem B2970265 : Blo 2085435 2970265 := bstep (se 2 (by rfl) ⟨1113849, by rfl⟩ : syracuseStep 2970265 = 2227699) B2227699
theorem B3960353 : Blo 2085435 3960353 := bstep (se 2 (by rfl) ⟨1485132, by rfl⟩ : syracuseStep 3960353 = 2970265) B2970265
theorem B10560941 : Blo 2085435 10560941 := bstep (se 3 (by rfl) ⟨1980176, by rfl⟩ : syracuseStep 10560941 = 3960353) B3960353
theorem B7040627 : Blo 2085435 7040627 := bstep (se 1 (by rfl) ⟨5280470, by rfl⟩ : syracuseStep 7040627 = 10560941) B10560941
theorem B4693751 : Blo 2085435 4693751 := bstep (se 1 (by rfl) ⟨3520313, by rfl⟩ : syracuseStep 4693751 = 7040627) B7040627
theorem B3129167 : Blo 2085435 3129167 := bstep (se 1 (by rfl) ⟨2346875, by rfl⟩ : syracuseStep 3129167 = 4693751) B4693751
theorem B2086111 : Blo 2085435 2086111 := bstep (se 1 (by rfl) ⟨1564583, by rfl⟩ : syracuseStep 2086111 = 3129167) B3129167
theorem B3129173 : Blo 2085435 3129173 := bbase (se 9 (by rfl) ⟨9167, by rfl⟩ : syracuseStep 3129173 = 18335) (by norm_num)
theorem B2086115 : Blo 2085435 2086115 := bstep (se 1 (by rfl) ⟨1564586, by rfl⟩ : syracuseStep 2086115 = 3129173) B3129173
theorem B4229165 : Blo 2085435 4229165 := bbase (se 3 (by rfl) ⟨792968, by rfl⟩ : syracuseStep 4229165 = 1585937) (by norm_num)
theorem B2819443 : Blo 2085435 2819443 := bstep (se 1 (by rfl) ⟨2114582, by rfl⟩ : syracuseStep 2819443 = 4229165) B4229165
theorem B3759257 : Blo 2085435 3759257 := bstep (se 2 (by rfl) ⟨1409721, by rfl⟩ : syracuseStep 3759257 = 2819443) B2819443
theorem B10024685 : Blo 2085435 10024685 := bstep (se 3 (by rfl) ⟨1879628, by rfl⟩ : syracuseStep 10024685 = 3759257) B3759257
theorem B6683123 : Blo 2085435 6683123 := bstep (se 1 (by rfl) ⟨5012342, by rfl⟩ : syracuseStep 6683123 = 10024685) B10024685
theorem B4455415 : Blo 2085435 4455415 := bstep (se 1 (by rfl) ⟨3341561, by rfl⟩ : syracuseStep 4455415 = 6683123) B6683123
theorem B5940553 : Blo 2085435 5940553 := bstep (se 2 (by rfl) ⟨2227707, by rfl⟩ : syracuseStep 5940553 = 4455415) B4455415
theorem B7920737 : Blo 2085435 7920737 := bstep (se 2 (by rfl) ⟨2970276, by rfl⟩ : syracuseStep 7920737 = 5940553) B5940553
theorem B5280491 : Blo 2085435 5280491 := bstep (se 1 (by rfl) ⟨3960368, by rfl⟩ : syracuseStep 5280491 = 7920737) B7920737
theorem B3520327 : Blo 2085435 3520327 := bstep (se 1 (by rfl) ⟨2640245, by rfl⟩ : syracuseStep 3520327 = 5280491) B5280491
theorem B4693769 : Blo 2085435 4693769 := bstep (se 2 (by rfl) ⟨1760163, by rfl⟩ : syracuseStep 4693769 = 3520327) B3520327
theorem B3129179 : Blo 2085435 3129179 := bstep (se 1 (by rfl) ⟨2346884, by rfl⟩ : syracuseStep 3129179 = 4693769) B4693769
theorem B2086119 : Blo 2085435 2086119 := bstep (se 1 (by rfl) ⟨1564589, by rfl⟩ : syracuseStep 2086119 = 3129179) B3129179
theorem B2346889 : Blo 2085435 2346889 := bbase (se 2 (by rfl) ⟨880083, by rfl⟩ : syracuseStep 2346889 = 1760167) (by norm_num)
theorem B3129185 : Blo 2085435 3129185 := bstep (se 2 (by rfl) ⟨1173444, by rfl⟩ : syracuseStep 3129185 = 2346889) B2346889
theorem B2086123 : Blo 2085435 2086123 := bstep (se 1 (by rfl) ⟨1564592, by rfl⟩ : syracuseStep 2086123 = 3129185) B3129185
theorem B2712793 : Blo 2085435 2712793 := bbase (se 2 (by rfl) ⟨1017297, by rfl⟩ : syracuseStep 2712793 = 2034595) (by norm_num)
theorem B3617057 : Blo 2085435 3617057 := bstep (se 2 (by rfl) ⟨1356396, by rfl⟩ : syracuseStep 3617057 = 2712793) B2712793
theorem B2411371 : Blo 2085435 2411371 := bstep (se 1 (by rfl) ⟨1808528, by rfl⟩ : syracuseStep 2411371 = 3617057) B3617057
theorem B3215161 : Blo 2085435 3215161 := bstep (se 2 (by rfl) ⟨1205685, by rfl⟩ : syracuseStep 3215161 = 2411371) B2411371
theorem B4286881 : Blo 2085435 4286881 := bstep (se 2 (by rfl) ⟨1607580, by rfl⟩ : syracuseStep 4286881 = 3215161) B3215161
theorem B5715841 : Blo 2085435 5715841 := bstep (se 2 (by rfl) ⟨2143440, by rfl⟩ : syracuseStep 5715841 = 4286881) B4286881
theorem B7621121 : Blo 2085435 7621121 := bstep (se 2 (by rfl) ⟨2857920, by rfl⟩ : syracuseStep 7621121 = 5715841) B5715841
theorem B5080747 : Blo 2085435 5080747 := bstep (se 1 (by rfl) ⟨3810560, by rfl⟩ : syracuseStep 5080747 = 7621121) B7621121
theorem B6774329 : Blo 2085435 6774329 := bstep (se 2 (by rfl) ⟨2540373, by rfl⟩ : syracuseStep 6774329 = 5080747) B5080747
theorem B4516219 : Blo 2085435 4516219 := bstep (se 1 (by rfl) ⟨3387164, by rfl⟩ : syracuseStep 4516219 = 6774329) B6774329
theorem B24086501 : Blo 2085435 24086501 := bstep (se 4 (by rfl) ⟨2258109, by rfl⟩ : syracuseStep 24086501 = 4516219) B4516219
theorem B16057667 : Blo 2085435 16057667 := bstep (se 1 (by rfl) ⟨12043250, by rfl⟩ : syracuseStep 16057667 = 24086501) B24086501
theorem B10705111 : Blo 2085435 10705111 := bstep (se 1 (by rfl) ⟨8028833, by rfl⟩ : syracuseStep 10705111 = 16057667) B16057667
theorem B57093925 : Blo 2085435 57093925 := bstep (se 4 (by rfl) ⟨5352555, by rfl⟩ : syracuseStep 57093925 = 10705111) B10705111
theorem B76125233 : Blo 2085435 76125233 := bstep (se 2 (by rfl) ⟨28546962, by rfl⟩ : syracuseStep 76125233 = 57093925) B57093925
theorem B50750155 : Blo 2085435 50750155 := bstep (se 1 (by rfl) ⟨38062616, by rfl⟩ : syracuseStep 50750155 = 76125233) B76125233
theorem B67666873 : Blo 2085435 67666873 := bstep (se 2 (by rfl) ⟨25375077, by rfl⟩ : syracuseStep 67666873 = 50750155) B50750155
theorem B90222497 : Blo 2085435 90222497 := bstep (se 2 (by rfl) ⟨33833436, by rfl⟩ : syracuseStep 90222497 = 67666873) B67666873
theorem B60148331 : Blo 2085435 60148331 := bstep (se 1 (by rfl) ⟨45111248, by rfl⟩ : syracuseStep 60148331 = 90222497) B90222497
theorem B40098887 : Blo 2085435 40098887 := bstep (se 1 (by rfl) ⟨30074165, by rfl⟩ : syracuseStep 40098887 = 60148331) B60148331
theorem B26732591 : Blo 2085435 26732591 := bstep (se 1 (by rfl) ⟨20049443, by rfl⟩ : syracuseStep 26732591 = 40098887) B40098887
theorem B17821727 : Blo 2085435 17821727 := bstep (se 1 (by rfl) ⟨13366295, by rfl⟩ : syracuseStep 17821727 = 26732591) B26732591
theorem B11881151 : Blo 2085435 11881151 := bstep (se 1 (by rfl) ⟨8910863, by rfl⟩ : syracuseStep 11881151 = 17821727) B17821727
theorem B7920767 : Blo 2085435 7920767 := bstep (se 1 (by rfl) ⟨5940575, by rfl⟩ : syracuseStep 7920767 = 11881151) B11881151
theorem B5280511 : Blo 2085435 5280511 := bstep (se 1 (by rfl) ⟨3960383, by rfl⟩ : syracuseStep 5280511 = 7920767) B7920767
theorem B7040681 : Blo 2085435 7040681 := bstep (se 2 (by rfl) ⟨2640255, by rfl⟩ : syracuseStep 7040681 = 5280511) B5280511
theorem B4693787 : Blo 2085435 4693787 := bstep (se 1 (by rfl) ⟨3520340, by rfl⟩ : syracuseStep 4693787 = 7040681) B7040681
theorem B3129191 : Blo 2085435 3129191 := bstep (se 1 (by rfl) ⟨2346893, by rfl⟩ : syracuseStep 3129191 = 4693787) B4693787
theorem B2086127 : Blo 2085435 2086127 := bstep (se 1 (by rfl) ⟨1564595, by rfl⟩ : syracuseStep 2086127 = 3129191) B3129191
theorem B3129197 : Blo 2085435 3129197 := bbase (se 3 (by rfl) ⟨586724, by rfl⟩ : syracuseStep 3129197 = 1173449) (by norm_num)
theorem B2086131 : Blo 2085435 2086131 := bstep (se 1 (by rfl) ⟨1564598, by rfl⟩ : syracuseStep 2086131 = 3129197) B3129197
theorem B4693805 : Blo 2085435 4693805 := bbase (se 3 (by rfl) ⟨880088, by rfl⟩ : syracuseStep 4693805 = 1760177) (by norm_num)
theorem B3129203 : Blo 2085435 3129203 := bstep (se 1 (by rfl) ⟨2346902, by rfl⟩ : syracuseStep 3129203 = 4693805) B4693805
theorem B2086135 : Blo 2085435 2086135 := bstep (se 1 (by rfl) ⟨1564601, by rfl⟩ : syracuseStep 2086135 = 3129203) B3129203
theorem B8910917 : Blo 2085435 8910917 := bbase (se 4 (by rfl) ⟨835398, by rfl⟩ : syracuseStep 8910917 = 1670797) (by norm_num)
theorem B5940611 : Blo 2085435 5940611 := bstep (se 1 (by rfl) ⟨4455458, by rfl⟩ : syracuseStep 5940611 = 8910917) B8910917
theorem B3960407 : Blo 2085435 3960407 := bstep (se 1 (by rfl) ⟨2970305, by rfl⟩ : syracuseStep 3960407 = 5940611) B5940611
theorem B2640271 : Blo 2085435 2640271 := bstep (se 1 (by rfl) ⟨1980203, by rfl⟩ : syracuseStep 2640271 = 3960407) B3960407
theorem B3520361 : Blo 2085435 3520361 := bstep (se 2 (by rfl) ⟨1320135, by rfl⟩ : syracuseStep 3520361 = 2640271) B2640271
theorem B2346907 : Blo 2085435 2346907 := bstep (se 1 (by rfl) ⟨1760180, by rfl⟩ : syracuseStep 2346907 = 3520361) B3520361
theorem B3129209 : Blo 2085435 3129209 := bstep (se 2 (by rfl) ⟨1173453, by rfl⟩ : syracuseStep 3129209 = 2346907) B2346907
theorem B2086139 : Blo 2085435 2086139 := bstep (se 1 (by rfl) ⟨1564604, by rfl⟩ : syracuseStep 2086139 = 3129209) B3129209
theorem B12687637 : Blo 2085435 12687637 := bbase (se 6 (by rfl) ⟨297366, by rfl⟩ : syracuseStep 12687637 = 594733) (by norm_num)
theorem B16916849 : Blo 2085435 16916849 := bstep (se 2 (by rfl) ⟨6343818, by rfl⟩ : syracuseStep 16916849 = 12687637) B12687637
theorem B11277899 : Blo 2085435 11277899 := bstep (se 1 (by rfl) ⟨8458424, by rfl⟩ : syracuseStep 11277899 = 16916849) B16916849
theorem B7518599 : Blo 2085435 7518599 := bstep (se 1 (by rfl) ⟨5638949, by rfl⟩ : syracuseStep 7518599 = 11277899) B11277899
theorem B5012399 : Blo 2085435 5012399 := bstep (se 1 (by rfl) ⟨3759299, by rfl⟩ : syracuseStep 5012399 = 7518599) B7518599
theorem B13366397 : Blo 2085435 13366397 := bstep (se 3 (by rfl) ⟨2506199, by rfl⟩ : syracuseStep 13366397 = 5012399) B5012399
theorem B35643725 : Blo 2085435 35643725 := bstep (se 3 (by rfl) ⟨6683198, by rfl⟩ : syracuseStep 35643725 = 13366397) B13366397
theorem B23762483 : Blo 2085435 23762483 := bstep (se 1 (by rfl) ⟨17821862, by rfl⟩ : syracuseStep 23762483 = 35643725) B35643725
theorem B15841655 : Blo 2085435 15841655 := bstep (se 1 (by rfl) ⟨11881241, by rfl⟩ : syracuseStep 15841655 = 23762483) B23762483
theorem B10561103 : Blo 2085435 10561103 := bstep (se 1 (by rfl) ⟨7920827, by rfl⟩ : syracuseStep 10561103 = 15841655) B15841655
theorem B7040735 : Blo 2085435 7040735 := bstep (se 1 (by rfl) ⟨5280551, by rfl⟩ : syracuseStep 7040735 = 10561103) B10561103
theorem B4693823 : Blo 2085435 4693823 := bstep (se 1 (by rfl) ⟨3520367, by rfl⟩ : syracuseStep 4693823 = 7040735) B7040735
theorem B3129215 : Blo 2085435 3129215 := bstep (se 1 (by rfl) ⟨2346911, by rfl⟩ : syracuseStep 3129215 = 4693823) B4693823
theorem B2086143 : Blo 2085435 2086143 := bstep (se 1 (by rfl) ⟨1564607, by rfl⟩ : syracuseStep 2086143 = 3129215) B3129215
theorem B3129221 : Blo 2085435 3129221 := bbase (se 4 (by rfl) ⟨293364, by rfl⟩ : syracuseStep 3129221 = 586729) (by norm_num)
theorem B2086147 : Blo 2085435 2086147 := bstep (se 1 (by rfl) ⟨1564610, by rfl⟩ : syracuseStep 2086147 = 3129221) B3129221
theorem B3520381 : Blo 2085435 3520381 := bbase (se 3 (by rfl) ⟨660071, by rfl⟩ : syracuseStep 3520381 = 1320143) (by norm_num)
theorem B4693841 : Blo 2085435 4693841 := bstep (se 2 (by rfl) ⟨1760190, by rfl⟩ : syracuseStep 4693841 = 3520381) B3520381
theorem B3129227 : Blo 2085435 3129227 := bstep (se 1 (by rfl) ⟨2346920, by rfl⟩ : syracuseStep 3129227 = 4693841) B4693841
theorem B2086151 : Blo 2085435 2086151 := bstep (se 1 (by rfl) ⟨1564613, by rfl⟩ : syracuseStep 2086151 = 3129227) B3129227
theorem B2346925 : Blo 2085435 2346925 := bbase (se 3 (by rfl) ⟨440048, by rfl⟩ : syracuseStep 2346925 = 880097) (by norm_num)
theorem B3129233 : Blo 2085435 3129233 := bstep (se 2 (by rfl) ⟨1173462, by rfl⟩ : syracuseStep 3129233 = 2346925) B2346925
theorem B2086155 : Blo 2085435 2086155 := bstep (se 1 (by rfl) ⟨1564616, by rfl⟩ : syracuseStep 2086155 = 3129233) B3129233
theorem B7040789 : Blo 2085435 7040789 := bbase (se 6 (by rfl) ⟨165018, by rfl⟩ : syracuseStep 7040789 = 330037) (by norm_num)
theorem B4693859 : Blo 2085435 4693859 := bstep (se 1 (by rfl) ⟨3520394, by rfl⟩ : syracuseStep 4693859 = 7040789) B7040789
theorem B3129239 : Blo 2085435 3129239 := bstep (se 1 (by rfl) ⟨2346929, by rfl⟩ : syracuseStep 3129239 = 4693859) B4693859
theorem B2086159 : Blo 2085435 2086159 := bstep (se 1 (by rfl) ⟨1564619, by rfl⟩ : syracuseStep 2086159 = 3129239) B3129239
theorem B3129245 : Blo 2085435 3129245 := bbase (se 3 (by rfl) ⟨586733, by rfl⟩ : syracuseStep 3129245 = 1173467) (by norm_num)
theorem B2086163 : Blo 2085435 2086163 := bstep (se 1 (by rfl) ⟨1564622, by rfl⟩ : syracuseStep 2086163 = 3129245) B3129245
theorem B4693877 : Blo 2085435 4693877 := bbase (se 5 (by rfl) ⟨220025, by rfl⟩ : syracuseStep 4693877 = 440051) (by norm_num)
theorem B3129251 : Blo 2085435 3129251 := bstep (se 1 (by rfl) ⟨2346938, by rfl⟩ : syracuseStep 3129251 = 4693877) B4693877
theorem B2086167 : Blo 2085435 2086167 := bstep (se 1 (by rfl) ⟨1564625, by rfl⟩ : syracuseStep 2086167 = 3129251) B3129251
theorem B2378965 : Blo 2085435 2378965 := bbase (se 7 (by rfl) ⟨27878, by rfl⟩ : syracuseStep 2378965 = 55757) (by norm_num)
theorem B3171953 : Blo 2085435 3171953 := bstep (se 2 (by rfl) ⟨1189482, by rfl⟩ : syracuseStep 3171953 = 2378965) B2378965
theorem B2114635 : Blo 2085435 2114635 := bstep (se 1 (by rfl) ⟨1585976, by rfl⟩ : syracuseStep 2114635 = 3171953) B3171953
theorem B2819513 : Blo 2085435 2819513 := bstep (se 2 (by rfl) ⟨1057317, by rfl⟩ : syracuseStep 2819513 = 2114635) B2114635
theorem B7518701 : Blo 2085435 7518701 := bstep (se 3 (by rfl) ⟨1409756, by rfl⟩ : syracuseStep 7518701 = 2819513) B2819513
theorem B20049869 : Blo 2085435 20049869 := bstep (se 3 (by rfl) ⟨3759350, by rfl⟩ : syracuseStep 20049869 = 7518701) B7518701
theorem B13366579 : Blo 2085435 13366579 := bstep (se 1 (by rfl) ⟨10024934, by rfl⟩ : syracuseStep 13366579 = 20049869) B20049869
theorem B17822105 : Blo 2085435 17822105 := bstep (se 2 (by rfl) ⟨6683289, by rfl⟩ : syracuseStep 17822105 = 13366579) B13366579
theorem B11881403 : Blo 2085435 11881403 := bstep (se 1 (by rfl) ⟨8911052, by rfl⟩ : syracuseStep 11881403 = 17822105) B17822105
theorem B7920935 : Blo 2085435 7920935 := bstep (se 1 (by rfl) ⟨5940701, by rfl⟩ : syracuseStep 7920935 = 11881403) B11881403
theorem B5280623 : Blo 2085435 5280623 := bstep (se 1 (by rfl) ⟨3960467, by rfl⟩ : syracuseStep 5280623 = 7920935) B7920935
theorem B3520415 : Blo 2085435 3520415 := bstep (se 1 (by rfl) ⟨2640311, by rfl⟩ : syracuseStep 3520415 = 5280623) B5280623
theorem B2346943 : Blo 2085435 2346943 := bstep (se 1 (by rfl) ⟨1760207, by rfl⟩ : syracuseStep 2346943 = 3520415) B3520415
theorem B3129257 : Blo 2085435 3129257 := bstep (se 2 (by rfl) ⟨1173471, by rfl⟩ : syracuseStep 3129257 = 2346943) B2346943
theorem B2086171 : Blo 2085435 2086171 := bstep (se 1 (by rfl) ⟨1564628, by rfl⟩ : syracuseStep 2086171 = 3129257) B3129257
theorem B7920949 : Blo 2085435 7920949 := bbase (se 5 (by rfl) ⟨371294, by rfl⟩ : syracuseStep 7920949 = 742589) (by norm_num)
theorem B10561265 : Blo 2085435 10561265 := bstep (se 2 (by rfl) ⟨3960474, by rfl⟩ : syracuseStep 10561265 = 7920949) B7920949
theorem B7040843 : Blo 2085435 7040843 := bstep (se 1 (by rfl) ⟨5280632, by rfl⟩ : syracuseStep 7040843 = 10561265) B10561265
theorem B4693895 : Blo 2085435 4693895 := bstep (se 1 (by rfl) ⟨3520421, by rfl⟩ : syracuseStep 4693895 = 7040843) B7040843
theorem B3129263 : Blo 2085435 3129263 := bstep (se 1 (by rfl) ⟨2346947, by rfl⟩ : syracuseStep 3129263 = 4693895) B4693895
theorem B2086175 : Blo 2085435 2086175 := bstep (se 1 (by rfl) ⟨1564631, by rfl⟩ : syracuseStep 2086175 = 3129263) B3129263
theorem B3129269 : Blo 2085435 3129269 := bbase (se 5 (by rfl) ⟨146684, by rfl⟩ : syracuseStep 3129269 = 293369) (by norm_num)
theorem B2086179 : Blo 2085435 2086179 := bstep (se 1 (by rfl) ⟨1564634, by rfl⟩ : syracuseStep 2086179 = 3129269) B3129269
theorem B5280653 : Blo 2085435 5280653 := bbase (se 3 (by rfl) ⟨990122, by rfl⟩ : syracuseStep 5280653 = 1980245) (by norm_num)
theorem B3520435 : Blo 2085435 3520435 := bstep (se 1 (by rfl) ⟨2640326, by rfl⟩ : syracuseStep 3520435 = 5280653) B5280653
theorem B4693913 : Blo 2085435 4693913 := bstep (se 2 (by rfl) ⟨1760217, by rfl⟩ : syracuseStep 4693913 = 3520435) B3520435
theorem B3129275 : Blo 2085435 3129275 := bstep (se 1 (by rfl) ⟨2346956, by rfl⟩ : syracuseStep 3129275 = 4693913) B4693913
theorem B2086183 : Blo 2085435 2086183 := bstep (se 1 (by rfl) ⟨1564637, by rfl⟩ : syracuseStep 2086183 = 3129275) B3129275
theorem B2346961 : Blo 2085435 2346961 := bbase (se 2 (by rfl) ⟨880110, by rfl⟩ : syracuseStep 2346961 = 1760221) (by norm_num)
theorem B3129281 : Blo 2085435 3129281 := bstep (se 2 (by rfl) ⟨1173480, by rfl⟩ : syracuseStep 3129281 = 2346961) B2346961
theorem B2086187 : Blo 2085435 2086187 := bstep (se 1 (by rfl) ⟨1564640, by rfl⟩ : syracuseStep 2086187 = 3129281) B3129281
theorem B3341677 : Blo 2085435 3341677 := bbase (se 3 (by rfl) ⟨626564, by rfl⟩ : syracuseStep 3341677 = 1253129) (by norm_num)
theorem B4455569 : Blo 2085435 4455569 := bstep (se 2 (by rfl) ⟨1670838, by rfl⟩ : syracuseStep 4455569 = 3341677) B3341677
theorem B2970379 : Blo 2085435 2970379 := bstep (se 1 (by rfl) ⟨2227784, by rfl⟩ : syracuseStep 2970379 = 4455569) B4455569
theorem B3960505 : Blo 2085435 3960505 := bstep (se 2 (by rfl) ⟨1485189, by rfl⟩ : syracuseStep 3960505 = 2970379) B2970379
theorem B5280673 : Blo 2085435 5280673 := bstep (se 2 (by rfl) ⟨1980252, by rfl⟩ : syracuseStep 5280673 = 3960505) B3960505
theorem B7040897 : Blo 2085435 7040897 := bstep (se 2 (by rfl) ⟨2640336, by rfl⟩ : syracuseStep 7040897 = 5280673) B5280673
theorem B4693931 : Blo 2085435 4693931 := bstep (se 1 (by rfl) ⟨3520448, by rfl⟩ : syracuseStep 4693931 = 7040897) B7040897
theorem B3129287 : Blo 2085435 3129287 := bstep (se 1 (by rfl) ⟨2346965, by rfl⟩ : syracuseStep 3129287 = 4693931) B4693931
theorem B2086191 : Blo 2085435 2086191 := bstep (se 1 (by rfl) ⟨1564643, by rfl⟩ : syracuseStep 2086191 = 3129287) B3129287
theorem B3129293 : Blo 2085435 3129293 := bbase (se 3 (by rfl) ⟨586742, by rfl⟩ : syracuseStep 3129293 = 1173485) (by norm_num)
theorem B2086195 : Blo 2085435 2086195 := bstep (se 1 (by rfl) ⟨1564646, by rfl⟩ : syracuseStep 2086195 = 3129293) B3129293
theorem B4693949 : Blo 2085435 4693949 := bbase (se 3 (by rfl) ⟨880115, by rfl⟩ : syracuseStep 4693949 = 1760231) (by norm_num)
theorem B3129299 : Blo 2085435 3129299 := bstep (se 1 (by rfl) ⟨2346974, by rfl⟩ : syracuseStep 3129299 = 4693949) B4693949
theorem B2086199 : Blo 2085435 2086199 := bstep (se 1 (by rfl) ⟨1564649, by rfl⟩ : syracuseStep 2086199 = 3129299) B3129299
theorem B3520469 : Blo 2085435 3520469 := bbase (se 7 (by rfl) ⟨41255, by rfl⟩ : syracuseStep 3520469 = 82511) (by norm_num)
theorem B2346979 : Blo 2085435 2346979 := bstep (se 1 (by rfl) ⟨1760234, by rfl⟩ : syracuseStep 2346979 = 3520469) B3520469
theorem B3129305 : Blo 2085435 3129305 := bstep (se 2 (by rfl) ⟨1173489, by rfl⟩ : syracuseStep 3129305 = 2346979) B2346979
theorem B2086203 : Blo 2085435 2086203 := bstep (se 1 (by rfl) ⟨1564652, by rfl⟩ : syracuseStep 2086203 = 3129305) B3129305
theorem B8911205 : Blo 2085435 8911205 := bbase (se 4 (by rfl) ⟨835425, by rfl⟩ : syracuseStep 8911205 = 1670851) (by norm_num)
theorem B5940803 : Blo 2085435 5940803 := bstep (se 1 (by rfl) ⟨4455602, by rfl⟩ : syracuseStep 5940803 = 8911205) B8911205
theorem B15842141 : Blo 2085435 15842141 := bstep (se 3 (by rfl) ⟨2970401, by rfl⟩ : syracuseStep 15842141 = 5940803) B5940803
theorem B10561427 : Blo 2085435 10561427 := bstep (se 1 (by rfl) ⟨7921070, by rfl⟩ : syracuseStep 10561427 = 15842141) B15842141
theorem B7040951 : Blo 2085435 7040951 := bstep (se 1 (by rfl) ⟨5280713, by rfl⟩ : syracuseStep 7040951 = 10561427) B10561427
theorem B4693967 : Blo 2085435 4693967 := bstep (se 1 (by rfl) ⟨3520475, by rfl⟩ : syracuseStep 4693967 = 7040951) B7040951
theorem B3129311 : Blo 2085435 3129311 := bstep (se 1 (by rfl) ⟨2346983, by rfl⟩ : syracuseStep 3129311 = 4693967) B4693967
theorem B2086207 : Blo 2085435 2086207 := bstep (se 1 (by rfl) ⟨1564655, by rfl⟩ : syracuseStep 2086207 = 3129311) B3129311
theorem B3129317 : Blo 2085435 3129317 := bbase (se 4 (by rfl) ⟨293373, by rfl⟩ : syracuseStep 3129317 = 586747) (by norm_num)
theorem B2086211 : Blo 2085435 2086211 := bstep (se 1 (by rfl) ⟨1564658, by rfl⟩ : syracuseStep 2086211 = 3129317) B3129317
theorem B2411473 : Blo 2085435 2411473 := bbase (se 2 (by rfl) ⟨904302, by rfl⟩ : syracuseStep 2411473 = 1808605) (by norm_num)
theorem B3215297 : Blo 2085435 3215297 := bstep (se 2 (by rfl) ⟨1205736, by rfl⟩ : syracuseStep 3215297 = 2411473) B2411473
theorem B8574125 : Blo 2085435 8574125 := bstep (se 3 (by rfl) ⟨1607648, by rfl⟩ : syracuseStep 8574125 = 3215297) B3215297
theorem B91457333 : Blo 2085435 91457333 := bstep (se 5 (by rfl) ⟨4287062, by rfl⟩ : syracuseStep 91457333 = 8574125) B8574125
theorem B60971555 : Blo 2085435 60971555 := bstep (se 1 (by rfl) ⟨45728666, by rfl⟩ : syracuseStep 60971555 = 91457333) B91457333
theorem B40647703 : Blo 2085435 40647703 := bstep (se 1 (by rfl) ⟨30485777, by rfl⟩ : syracuseStep 40647703 = 60971555) B60971555
theorem B54196937 : Blo 2085435 54196937 := bstep (se 2 (by rfl) ⟨20323851, by rfl⟩ : syracuseStep 54196937 = 40647703) B40647703
theorem B36131291 : Blo 2085435 36131291 := bstep (se 1 (by rfl) ⟨27098468, by rfl⟩ : syracuseStep 36131291 = 54196937) B54196937
theorem B24087527 : Blo 2085435 24087527 := bstep (se 1 (by rfl) ⟨18065645, by rfl⟩ : syracuseStep 24087527 = 36131291) B36131291
theorem B16058351 : Blo 2085435 16058351 := bstep (se 1 (by rfl) ⟨12043763, by rfl⟩ : syracuseStep 16058351 = 24087527) B24087527
theorem B10705567 : Blo 2085435 10705567 := bstep (se 1 (by rfl) ⟨8029175, by rfl⟩ : syracuseStep 10705567 = 16058351) B16058351
theorem B14274089 : Blo 2085435 14274089 := bstep (se 2 (by rfl) ⟨5352783, by rfl⟩ : syracuseStep 14274089 = 10705567) B10705567
theorem B9516059 : Blo 2085435 9516059 := bstep (se 1 (by rfl) ⟨7137044, by rfl⟩ : syracuseStep 9516059 = 14274089) B14274089
theorem B6344039 : Blo 2085435 6344039 := bstep (se 1 (by rfl) ⟨4758029, by rfl⟩ : syracuseStep 6344039 = 9516059) B9516059
theorem B16917437 : Blo 2085435 16917437 := bstep (se 3 (by rfl) ⟨3172019, by rfl⟩ : syracuseStep 16917437 = 6344039) B6344039
theorem B11278291 : Blo 2085435 11278291 := bstep (se 1 (by rfl) ⟨8458718, by rfl⟩ : syracuseStep 11278291 = 16917437) B16917437
theorem B15037721 : Blo 2085435 15037721 := bstep (se 2 (by rfl) ⟨5639145, by rfl⟩ : syracuseStep 15037721 = 11278291) B11278291
theorem B10025147 : Blo 2085435 10025147 := bstep (se 1 (by rfl) ⟨7518860, by rfl⟩ : syracuseStep 10025147 = 15037721) B15037721
theorem B6683431 : Blo 2085435 6683431 := bstep (se 1 (by rfl) ⟨5012573, by rfl⟩ : syracuseStep 6683431 = 10025147) B10025147
theorem B8911241 : Blo 2085435 8911241 := bstep (se 2 (by rfl) ⟨3341715, by rfl⟩ : syracuseStep 8911241 = 6683431) B6683431
theorem B5940827 : Blo 2085435 5940827 := bstep (se 1 (by rfl) ⟨4455620, by rfl⟩ : syracuseStep 5940827 = 8911241) B8911241
theorem B3960551 : Blo 2085435 3960551 := bstep (se 1 (by rfl) ⟨2970413, by rfl⟩ : syracuseStep 3960551 = 5940827) B5940827
theorem B2640367 : Blo 2085435 2640367 := bstep (se 1 (by rfl) ⟨1980275, by rfl⟩ : syracuseStep 2640367 = 3960551) B3960551
theorem B3520489 : Blo 2085435 3520489 := bstep (se 2 (by rfl) ⟨1320183, by rfl⟩ : syracuseStep 3520489 = 2640367) B2640367
theorem B4693985 : Blo 2085435 4693985 := bstep (se 2 (by rfl) ⟨1760244, by rfl⟩ : syracuseStep 4693985 = 3520489) B3520489
theorem B3129323 : Blo 2085435 3129323 := bstep (se 1 (by rfl) ⟨2346992, by rfl⟩ : syracuseStep 3129323 = 4693985) B4693985
theorem B2086215 : Blo 2085435 2086215 := bstep (se 1 (by rfl) ⟨1564661, by rfl⟩ : syracuseStep 2086215 = 3129323) B3129323
theorem B2346997 : Blo 2085435 2346997 := bbase (se 5 (by rfl) ⟨110015, by rfl⟩ : syracuseStep 2346997 = 220031) (by norm_num)
theorem B3129329 : Blo 2085435 3129329 := bstep (se 2 (by rfl) ⟨1173498, by rfl⟩ : syracuseStep 3129329 = 2346997) B2346997
theorem B2086219 : Blo 2085435 2086219 := bstep (se 1 (by rfl) ⟨1564664, by rfl⟩ : syracuseStep 2086219 = 3129329) B3129329
theorem B2640377 : Blo 2085435 2640377 := bbase (se 2 (by rfl) ⟨990141, by rfl⟩ : syracuseStep 2640377 = 1980283) (by norm_num)
theorem B7041005 : Blo 2085435 7041005 := bstep (se 3 (by rfl) ⟨1320188, by rfl⟩ : syracuseStep 7041005 = 2640377) B2640377
theorem B4694003 : Blo 2085435 4694003 := bstep (se 1 (by rfl) ⟨3520502, by rfl⟩ : syracuseStep 4694003 = 7041005) B7041005
theorem B3129335 : Blo 2085435 3129335 := bstep (se 1 (by rfl) ⟨2347001, by rfl⟩ : syracuseStep 3129335 = 4694003) B4694003
theorem B2086223 : Blo 2085435 2086223 := bstep (se 1 (by rfl) ⟨1564667, by rfl⟩ : syracuseStep 2086223 = 3129335) B3129335
theorem B3129341 : Blo 2085435 3129341 := bbase (se 3 (by rfl) ⟨586751, by rfl⟩ : syracuseStep 3129341 = 1173503) (by norm_num)
theorem B2086227 : Blo 2085435 2086227 := bstep (se 1 (by rfl) ⟨1564670, by rfl⟩ : syracuseStep 2086227 = 3129341) B3129341
theorem B4694021 : Blo 2085435 4694021 := bbase (se 4 (by rfl) ⟨440064, by rfl⟩ : syracuseStep 4694021 = 880129) (by norm_num)
theorem B3129347 : Blo 2085435 3129347 := bstep (se 1 (by rfl) ⟨2347010, by rfl⟩ : syracuseStep 3129347 = 4694021) B4694021
theorem B2086231 : Blo 2085435 2086231 := bstep (se 1 (by rfl) ⟨1564673, by rfl⟩ : syracuseStep 2086231 = 3129347) B3129347
theorem B3960589 : Blo 2085435 3960589 := bbase (se 3 (by rfl) ⟨742610, by rfl⟩ : syracuseStep 3960589 = 1485221) (by norm_num)
theorem B5280785 : Blo 2085435 5280785 := bstep (se 2 (by rfl) ⟨1980294, by rfl⟩ : syracuseStep 5280785 = 3960589) B3960589
theorem B3520523 : Blo 2085435 3520523 := bstep (se 1 (by rfl) ⟨2640392, by rfl⟩ : syracuseStep 3520523 = 5280785) B5280785
theorem B2347015 : Blo 2085435 2347015 := bstep (se 1 (by rfl) ⟨1760261, by rfl⟩ : syracuseStep 2347015 = 3520523) B3520523
theorem B3129353 : Blo 2085435 3129353 := bstep (se 2 (by rfl) ⟨1173507, by rfl⟩ : syracuseStep 3129353 = 2347015) B2347015
theorem B2086235 : Blo 2085435 2086235 := bstep (se 1 (by rfl) ⟨1564676, by rfl⟩ : syracuseStep 2086235 = 3129353) B3129353
theorem B10561589 : Blo 2085435 10561589 := bbase (se 5 (by rfl) ⟨495074, by rfl⟩ : syracuseStep 10561589 = 990149) (by norm_num)
theorem B7041059 : Blo 2085435 7041059 := bstep (se 1 (by rfl) ⟨5280794, by rfl⟩ : syracuseStep 7041059 = 10561589) B10561589
theorem B4694039 : Blo 2085435 4694039 := bstep (se 1 (by rfl) ⟨3520529, by rfl⟩ : syracuseStep 4694039 = 7041059) B7041059
theorem B3129359 : Blo 2085435 3129359 := bstep (se 1 (by rfl) ⟨2347019, by rfl⟩ : syracuseStep 3129359 = 4694039) B4694039
theorem B2086239 : Blo 2085435 2086239 := bstep (se 1 (by rfl) ⟨1564679, by rfl⟩ : syracuseStep 2086239 = 3129359) B3129359
theorem B3129365 : Blo 2085435 3129365 := bbase (se 6 (by rfl) ⟨73344, by rfl⟩ : syracuseStep 3129365 = 146689) (by norm_num)
theorem B2086243 : Blo 2085435 2086243 := bstep (se 1 (by rfl) ⟨1564682, by rfl⟩ : syracuseStep 2086243 = 3129365) B3129365
theorem B6021973 : Blo 2085435 6021973 := bbase (se 9 (by rfl) ⟨17642, by rfl⟩ : syracuseStep 6021973 = 35285) (by norm_num)
theorem B8029297 : Blo 2085435 8029297 := bstep (se 2 (by rfl) ⟨3010986, by rfl⟩ : syracuseStep 8029297 = 6021973) B6021973
theorem B42822917 : Blo 2085435 42822917 := bstep (se 4 (by rfl) ⟨4014648, by rfl⟩ : syracuseStep 42822917 = 8029297) B8029297
theorem B28548611 : Blo 2085435 28548611 := bstep (se 1 (by rfl) ⟨21411458, by rfl⟩ : syracuseStep 28548611 = 42822917) B42822917
theorem B19032407 : Blo 2085435 19032407 := bstep (se 1 (by rfl) ⟨14274305, by rfl⟩ : syracuseStep 19032407 = 28548611) B28548611
theorem B12688271 : Blo 2085435 12688271 := bstep (se 1 (by rfl) ⟨9516203, by rfl⟩ : syracuseStep 12688271 = 19032407) B19032407
theorem B8458847 : Blo 2085435 8458847 := bstep (se 1 (by rfl) ⟨6344135, by rfl⟩ : syracuseStep 8458847 = 12688271) B12688271
theorem B5639231 : Blo 2085435 5639231 := bstep (se 1 (by rfl) ⟨4229423, by rfl⟩ : syracuseStep 5639231 = 8458847) B8458847
theorem B15037949 : Blo 2085435 15037949 := bstep (se 3 (by rfl) ⟨2819615, by rfl⟩ : syracuseStep 15037949 = 5639231) B5639231
theorem B10025299 : Blo 2085435 10025299 := bstep (se 1 (by rfl) ⟨7518974, by rfl⟩ : syracuseStep 10025299 = 15037949) B15037949
theorem B13367065 : Blo 2085435 13367065 := bstep (se 2 (by rfl) ⟨5012649, by rfl⟩ : syracuseStep 13367065 = 10025299) B10025299
theorem B17822753 : Blo 2085435 17822753 := bstep (se 2 (by rfl) ⟨6683532, by rfl⟩ : syracuseStep 17822753 = 13367065) B13367065
theorem B11881835 : Blo 2085435 11881835 := bstep (se 1 (by rfl) ⟨8911376, by rfl⟩ : syracuseStep 11881835 = 17822753) B17822753
theorem B7921223 : Blo 2085435 7921223 := bstep (se 1 (by rfl) ⟨5940917, by rfl⟩ : syracuseStep 7921223 = 11881835) B11881835
theorem B5280815 : Blo 2085435 5280815 := bstep (se 1 (by rfl) ⟨3960611, by rfl⟩ : syracuseStep 5280815 = 7921223) B7921223
theorem B3520543 : Blo 2085435 3520543 := bstep (se 1 (by rfl) ⟨2640407, by rfl⟩ : syracuseStep 3520543 = 5280815) B5280815
theorem B4694057 : Blo 2085435 4694057 := bstep (se 2 (by rfl) ⟨1760271, by rfl⟩ : syracuseStep 4694057 = 3520543) B3520543
theorem B3129371 : Blo 2085435 3129371 := bstep (se 1 (by rfl) ⟨2347028, by rfl⟩ : syracuseStep 3129371 = 4694057) B4694057
theorem B2086247 : Blo 2085435 2086247 := bstep (se 1 (by rfl) ⟨1564685, by rfl⟩ : syracuseStep 2086247 = 3129371) B3129371
theorem B2347033 : Blo 2085435 2347033 := bbase (se 2 (by rfl) ⟨880137, by rfl⟩ : syracuseStep 2347033 = 1760275) (by norm_num)
theorem B3129377 : Blo 2085435 3129377 := bstep (se 2 (by rfl) ⟨1173516, by rfl⟩ : syracuseStep 3129377 = 2347033) B2347033
theorem B2086251 : Blo 2085435 2086251 := bstep (se 1 (by rfl) ⟨1564688, by rfl⟩ : syracuseStep 2086251 = 3129377) B3129377
theorem B7921253 : Blo 2085435 7921253 := bbase (se 4 (by rfl) ⟨742617, by rfl⟩ : syracuseStep 7921253 = 1485235) (by norm_num)
theorem B5280835 : Blo 2085435 5280835 := bstep (se 1 (by rfl) ⟨3960626, by rfl⟩ : syracuseStep 5280835 = 7921253) B7921253
theorem B7041113 : Blo 2085435 7041113 := bstep (se 2 (by rfl) ⟨2640417, by rfl⟩ : syracuseStep 7041113 = 5280835) B5280835
theorem B4694075 : Blo 2085435 4694075 := bstep (se 1 (by rfl) ⟨3520556, by rfl⟩ : syracuseStep 4694075 = 7041113) B7041113
theorem B3129383 : Blo 2085435 3129383 := bstep (se 1 (by rfl) ⟨2347037, by rfl⟩ : syracuseStep 3129383 = 4694075) B4694075
theorem B2086255 : Blo 2085435 2086255 := bstep (se 1 (by rfl) ⟨1564691, by rfl⟩ : syracuseStep 2086255 = 3129383) B3129383
theorem B3129389 : Blo 2085435 3129389 := bbase (se 3 (by rfl) ⟨586760, by rfl⟩ : syracuseStep 3129389 = 1173521) (by norm_num)
theorem B2086259 : Blo 2085435 2086259 := bstep (se 1 (by rfl) ⟨1564694, by rfl⟩ : syracuseStep 2086259 = 3129389) B3129389
theorem B4694093 : Blo 2085435 4694093 := bbase (se 3 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 4694093 = 1760285) (by norm_num)
theorem B3129395 : Blo 2085435 3129395 := bstep (se 1 (by rfl) ⟨2347046, by rfl⟩ : syracuseStep 3129395 = 4694093) B4694093
theorem B2086263 : Blo 2085435 2086263 := bstep (se 1 (by rfl) ⟨1564697, by rfl⟩ : syracuseStep 2086263 = 3129395) B3129395
theorem B2640433 : Blo 2085435 2640433 := bbase (se 2 (by rfl) ⟨990162, by rfl⟩ : syracuseStep 2640433 = 1980325) (by norm_num)
theorem B3520577 : Blo 2085435 3520577 := bstep (se 2 (by rfl) ⟨1320216, by rfl⟩ : syracuseStep 3520577 = 2640433) B2640433
theorem B2347051 : Blo 2085435 2347051 := bstep (se 1 (by rfl) ⟨1760288, by rfl⟩ : syracuseStep 2347051 = 3520577) B3520577
theorem B3129401 : Blo 2085435 3129401 := bstep (se 2 (by rfl) ⟨1173525, by rfl⟩ : syracuseStep 3129401 = 2347051) B2347051
theorem B2086267 : Blo 2085435 2086267 := bstep (se 1 (by rfl) ⟨1564700, by rfl⟩ : syracuseStep 2086267 = 3129401) B3129401
theorem B7519061 : Blo 2085435 7519061 := bbase (se 9 (by rfl) ⟨22028, by rfl⟩ : syracuseStep 7519061 = 44057) (by norm_num)
theorem B5012707 : Blo 2085435 5012707 := bstep (se 1 (by rfl) ⟨3759530, by rfl⟩ : syracuseStep 5012707 = 7519061) B7519061
theorem B6683609 : Blo 2085435 6683609 := bstep (se 2 (by rfl) ⟨2506353, by rfl⟩ : syracuseStep 6683609 = 5012707) B5012707
theorem B4455739 : Blo 2085435 4455739 := bstep (se 1 (by rfl) ⟨3341804, by rfl⟩ : syracuseStep 4455739 = 6683609) B6683609
theorem B23763941 : Blo 2085435 23763941 := bstep (se 4 (by rfl) ⟨2227869, by rfl⟩ : syracuseStep 23763941 = 4455739) B4455739
theorem B15842627 : Blo 2085435 15842627 := bstep (se 1 (by rfl) ⟨11881970, by rfl⟩ : syracuseStep 15842627 = 23763941) B23763941
theorem B10561751 : Blo 2085435 10561751 := bstep (se 1 (by rfl) ⟨7921313, by rfl⟩ : syracuseStep 10561751 = 15842627) B15842627
theorem B7041167 : Blo 2085435 7041167 := bstep (se 1 (by rfl) ⟨5280875, by rfl⟩ : syracuseStep 7041167 = 10561751) B10561751
theorem B4694111 : Blo 2085435 4694111 := bstep (se 1 (by rfl) ⟨3520583, by rfl⟩ : syracuseStep 4694111 = 7041167) B7041167
theorem B3129407 : Blo 2085435 3129407 := bstep (se 1 (by rfl) ⟨2347055, by rfl⟩ : syracuseStep 3129407 = 4694111) B4694111
theorem B2086271 : Blo 2085435 2086271 := bstep (se 1 (by rfl) ⟨1564703, by rfl⟩ : syracuseStep 2086271 = 3129407) B3129407
theorem B3129413 : Blo 2085435 3129413 := bbase (se 4 (by rfl) ⟨293382, by rfl⟩ : syracuseStep 3129413 = 586765) (by norm_num)
theorem B2086275 : Blo 2085435 2086275 := bstep (se 1 (by rfl) ⟨1564706, by rfl⟩ : syracuseStep 2086275 = 3129413) B3129413
theorem B3520597 : Blo 2085435 3520597 := bbase (se 8 (by rfl) ⟨20628, by rfl⟩ : syracuseStep 3520597 = 41257) (by norm_num)
theorem B4694129 : Blo 2085435 4694129 := bstep (se 2 (by rfl) ⟨1760298, by rfl⟩ : syracuseStep 4694129 = 3520597) B3520597
theorem B3129419 : Blo 2085435 3129419 := bstep (se 1 (by rfl) ⟨2347064, by rfl⟩ : syracuseStep 3129419 = 4694129) B4694129
theorem B2086279 : Blo 2085435 2086279 := bstep (se 1 (by rfl) ⟨1564709, by rfl⟩ : syracuseStep 2086279 = 3129419) B3129419
theorem B2347069 : Blo 2085435 2347069 := bbase (se 3 (by rfl) ⟨440075, by rfl⟩ : syracuseStep 2347069 = 880151) (by norm_num)
theorem B3129425 : Blo 2085435 3129425 := bstep (se 2 (by rfl) ⟨1173534, by rfl⟩ : syracuseStep 3129425 = 2347069) B2347069
theorem B2086283 : Blo 2085435 2086283 := bstep (se 1 (by rfl) ⟨1564712, by rfl⟩ : syracuseStep 2086283 = 3129425) B3129425
theorem B7041221 : Blo 2085435 7041221 := bbase (se 4 (by rfl) ⟨660114, by rfl⟩ : syracuseStep 7041221 = 1320229) (by norm_num)
theorem B4694147 : Blo 2085435 4694147 := bstep (se 1 (by rfl) ⟨3520610, by rfl⟩ : syracuseStep 4694147 = 7041221) B7041221
theorem B3129431 : Blo 2085435 3129431 := bstep (se 1 (by rfl) ⟨2347073, by rfl⟩ : syracuseStep 3129431 = 4694147) B4694147
theorem B2086287 : Blo 2085435 2086287 := bstep (se 1 (by rfl) ⟨1564715, by rfl⟩ : syracuseStep 2086287 = 3129431) B3129431
theorem B3129437 : Blo 2085435 3129437 := bbase (se 3 (by rfl) ⟨586769, by rfl⟩ : syracuseStep 3129437 = 1173539) (by norm_num)
theorem B2086291 : Blo 2085435 2086291 := bstep (se 1 (by rfl) ⟨1564718, by rfl⟩ : syracuseStep 2086291 = 3129437) B3129437
theorem B4694165 : Blo 2085435 4694165 := bbase (se 6 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 4694165 = 220039) (by norm_num)
theorem B3129443 : Blo 2085435 3129443 := bstep (se 1 (by rfl) ⟨2347082, by rfl⟩ : syracuseStep 3129443 = 4694165) B4694165
theorem B2086295 : Blo 2085435 2086295 := bstep (se 1 (by rfl) ⟨1564721, by rfl⟩ : syracuseStep 2086295 = 3129443) B3129443
theorem B2970533 : Blo 2085435 2970533 := bbase (se 4 (by rfl) ⟨278487, by rfl⟩ : syracuseStep 2970533 = 556975) (by norm_num)
theorem B7921421 : Blo 2085435 7921421 := bstep (se 3 (by rfl) ⟨1485266, by rfl⟩ : syracuseStep 7921421 = 2970533) B2970533
theorem B5280947 : Blo 2085435 5280947 := bstep (se 1 (by rfl) ⟨3960710, by rfl⟩ : syracuseStep 5280947 = 7921421) B7921421
theorem B3520631 : Blo 2085435 3520631 := bstep (se 1 (by rfl) ⟨2640473, by rfl⟩ : syracuseStep 3520631 = 5280947) B5280947
theorem B2347087 : Blo 2085435 2347087 := bstep (se 1 (by rfl) ⟨1760315, by rfl⟩ : syracuseStep 2347087 = 3520631) B3520631
theorem B3129449 : Blo 2085435 3129449 := bstep (se 2 (by rfl) ⟨1173543, by rfl⟩ : syracuseStep 3129449 = 2347087) B2347087
theorem B2086299 : Blo 2085435 2086299 := bstep (se 1 (by rfl) ⟨1564724, by rfl⟩ : syracuseStep 2086299 = 3129449) B3129449
theorem B5500069 : Blo 2085435 5500069 := bbase (se 4 (by rfl) ⟨515631, by rfl⟩ : syracuseStep 5500069 = 1031263) (by norm_num)
theorem B29333701 : Blo 2085435 29333701 := bstep (se 4 (by rfl) ⟨2750034, by rfl⟩ : syracuseStep 29333701 = 5500069) B5500069
theorem B156446405 : Blo 2085435 156446405 := bstep (se 4 (by rfl) ⟨14666850, by rfl⟩ : syracuseStep 156446405 = 29333701) B29333701
theorem B104297603 : Blo 2085435 104297603 := bstep (se 1 (by rfl) ⟨78223202, by rfl⟩ : syracuseStep 104297603 = 156446405) B156446405
theorem B278126941 : Blo 2085435 278126941 := bstep (se 3 (by rfl) ⟨52148801, by rfl⟩ : syracuseStep 278126941 = 104297603) B104297603
theorem B370835921 : Blo 2085435 370835921 := bstep (se 2 (by rfl) ⟨139063470, by rfl⟩ : syracuseStep 370835921 = 278126941) B278126941
theorem B988895789 : Blo 2085435 988895789 := bstep (se 3 (by rfl) ⟨185417960, by rfl⟩ : syracuseStep 988895789 = 370835921) B370835921
theorem B659263859 : Blo 2085435 659263859 := bstep (se 1 (by rfl) ⟨494447894, by rfl⟩ : syracuseStep 659263859 = 988895789) B988895789
theorem B439509239 : Blo 2085435 439509239 := bstep (se 1 (by rfl) ⟨329631929, by rfl⟩ : syracuseStep 439509239 = 659263859) B659263859
theorem B293006159 : Blo 2085435 293006159 := bstep (se 1 (by rfl) ⟨219754619, by rfl⟩ : syracuseStep 293006159 = 439509239) B439509239
theorem B195337439 : Blo 2085435 195337439 := bstep (se 1 (by rfl) ⟨146503079, by rfl⟩ : syracuseStep 195337439 = 293006159) B293006159
theorem B130224959 : Blo 2085435 130224959 := bstep (se 1 (by rfl) ⟨97668719, by rfl⟩ : syracuseStep 130224959 = 195337439) B195337439
theorem B86816639 : Blo 2085435 86816639 := bstep (se 1 (by rfl) ⟨65112479, by rfl⟩ : syracuseStep 86816639 = 130224959) B130224959
theorem B57877759 : Blo 2085435 57877759 := bstep (se 1 (by rfl) ⟨43408319, by rfl⟩ : syracuseStep 57877759 = 86816639) B86816639
theorem B308681381 : Blo 2085435 308681381 := bstep (se 4 (by rfl) ⟨28938879, by rfl⟩ : syracuseStep 308681381 = 57877759) B57877759
theorem B205787587 : Blo 2085435 205787587 := bstep (se 1 (by rfl) ⟨154340690, by rfl⟩ : syracuseStep 205787587 = 308681381) B308681381
theorem B274383449 : Blo 2085435 274383449 := bstep (se 2 (by rfl) ⟨102893793, by rfl⟩ : syracuseStep 274383449 = 205787587) B205787587
theorem B182922299 : Blo 2085435 182922299 := bstep (se 1 (by rfl) ⟨137191724, by rfl⟩ : syracuseStep 182922299 = 274383449) B274383449
theorem B121948199 : Blo 2085435 121948199 := bstep (se 1 (by rfl) ⟨91461149, by rfl⟩ : syracuseStep 121948199 = 182922299) B182922299
theorem B81298799 : Blo 2085435 81298799 := bstep (se 1 (by rfl) ⟨60974099, by rfl⟩ : syracuseStep 81298799 = 121948199) B121948199
theorem B54199199 : Blo 2085435 54199199 := bstep (se 1 (by rfl) ⟨40649399, by rfl⟩ : syracuseStep 54199199 = 81298799) B81298799
theorem B36132799 : Blo 2085435 36132799 := bstep (se 1 (by rfl) ⟨27099599, by rfl⟩ : syracuseStep 36132799 = 54199199) B54199199
theorem B48177065 : Blo 2085435 48177065 := bstep (se 2 (by rfl) ⟨18066399, by rfl⟩ : syracuseStep 48177065 = 36132799) B36132799
theorem B32118043 : Blo 2085435 32118043 := bstep (se 1 (by rfl) ⟨24088532, by rfl⟩ : syracuseStep 32118043 = 48177065) B48177065
theorem B42824057 : Blo 2085435 42824057 := bstep (se 2 (by rfl) ⟨16059021, by rfl⟩ : syracuseStep 42824057 = 32118043) B32118043
theorem B114197485 : Blo 2085435 114197485 := bstep (se 3 (by rfl) ⟨21412028, by rfl⟩ : syracuseStep 114197485 = 42824057) B42824057
theorem B152263313 : Blo 2085435 152263313 := bstep (se 2 (by rfl) ⟨57098742, by rfl⟩ : syracuseStep 152263313 = 114197485) B114197485
theorem B101508875 : Blo 2085435 101508875 := bstep (se 1 (by rfl) ⟨76131656, by rfl⟩ : syracuseStep 101508875 = 152263313) B152263313
theorem B67672583 : Blo 2085435 67672583 := bstep (se 1 (by rfl) ⟨50754437, by rfl⟩ : syracuseStep 67672583 = 101508875) B101508875
theorem B45115055 : Blo 2085435 45115055 := bstep (se 1 (by rfl) ⟨33836291, by rfl⟩ : syracuseStep 45115055 = 67672583) B67672583
theorem B30076703 : Blo 2085435 30076703 := bstep (se 1 (by rfl) ⟨22557527, by rfl⟩ : syracuseStep 30076703 = 45115055) B45115055
theorem B20051135 : Blo 2085435 20051135 := bstep (se 1 (by rfl) ⟨15038351, by rfl⟩ : syracuseStep 20051135 = 30076703) B30076703
theorem B13367423 : Blo 2085435 13367423 := bstep (se 1 (by rfl) ⟨10025567, by rfl⟩ : syracuseStep 13367423 = 20051135) B20051135
theorem B8911615 : Blo 2085435 8911615 := bstep (se 1 (by rfl) ⟨6683711, by rfl⟩ : syracuseStep 8911615 = 13367423) B13367423
theorem B11882153 : Blo 2085435 11882153 := bstep (se 2 (by rfl) ⟨4455807, by rfl⟩ : syracuseStep 11882153 = 8911615) B8911615
theorem B7921435 : Blo 2085435 7921435 := bstep (se 1 (by rfl) ⟨5941076, by rfl⟩ : syracuseStep 7921435 = 11882153) B11882153
theorem B10561913 : Blo 2085435 10561913 := bstep (se 2 (by rfl) ⟨3960717, by rfl⟩ : syracuseStep 10561913 = 7921435) B7921435
theorem B7041275 : Blo 2085435 7041275 := bstep (se 1 (by rfl) ⟨5280956, by rfl⟩ : syracuseStep 7041275 = 10561913) B10561913
theorem B4694183 : Blo 2085435 4694183 := bstep (se 1 (by rfl) ⟨3520637, by rfl⟩ : syracuseStep 4694183 = 7041275) B7041275
theorem B3129455 : Blo 2085435 3129455 := bstep (se 1 (by rfl) ⟨2347091, by rfl⟩ : syracuseStep 3129455 = 4694183) B4694183
theorem B2086303 : Blo 2085435 2086303 := bstep (se 1 (by rfl) ⟨1564727, by rfl⟩ : syracuseStep 2086303 = 3129455) B3129455
theorem B3129461 : Blo 2085435 3129461 := bbase (se 5 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 3129461 = 293387) (by norm_num)
theorem B2086307 : Blo 2085435 2086307 := bstep (se 1 (by rfl) ⟨1564730, by rfl⟩ : syracuseStep 2086307 = 3129461) B3129461
theorem B3960733 : Blo 2085435 3960733 := bbase (se 3 (by rfl) ⟨742637, by rfl⟩ : syracuseStep 3960733 = 1485275) (by norm_num)
theorem B5280977 : Blo 2085435 5280977 := bstep (se 2 (by rfl) ⟨1980366, by rfl⟩ : syracuseStep 5280977 = 3960733) B3960733
theorem B3520651 : Blo 2085435 3520651 := bstep (se 1 (by rfl) ⟨2640488, by rfl⟩ : syracuseStep 3520651 = 5280977) B5280977
theorem B4694201 : Blo 2085435 4694201 := bstep (se 2 (by rfl) ⟨1760325, by rfl⟩ : syracuseStep 4694201 = 3520651) B3520651
theorem B3129467 : Blo 2085435 3129467 := bstep (se 1 (by rfl) ⟨2347100, by rfl⟩ : syracuseStep 3129467 = 4694201) B4694201
theorem B2086311 : Blo 2085435 2086311 := bstep (se 1 (by rfl) ⟨1564733, by rfl⟩ : syracuseStep 2086311 = 3129467) B3129467
theorem B2347105 : Blo 2085435 2347105 := bbase (se 2 (by rfl) ⟨880164, by rfl⟩ : syracuseStep 2347105 = 1760329) (by norm_num)
theorem B3129473 : Blo 2085435 3129473 := bstep (se 2 (by rfl) ⟨1173552, by rfl⟩ : syracuseStep 3129473 = 2347105) B2347105
theorem B2086315 : Blo 2085435 2086315 := bstep (se 1 (by rfl) ⟨1564736, by rfl⟩ : syracuseStep 2086315 = 3129473) B3129473
theorem B5280997 : Blo 2085435 5280997 := bbase (se 4 (by rfl) ⟨495093, by rfl⟩ : syracuseStep 5280997 = 990187) (by norm_num)
theorem B7041329 : Blo 2085435 7041329 := bstep (se 2 (by rfl) ⟨2640498, by rfl⟩ : syracuseStep 7041329 = 5280997) B5280997
theorem B4694219 : Blo 2085435 4694219 := bstep (se 1 (by rfl) ⟨3520664, by rfl⟩ : syracuseStep 4694219 = 7041329) B7041329
theorem B3129479 : Blo 2085435 3129479 := bstep (se 1 (by rfl) ⟨2347109, by rfl⟩ : syracuseStep 3129479 = 4694219) B4694219
theorem B2086319 : Blo 2085435 2086319 := bstep (se 1 (by rfl) ⟨1564739, by rfl⟩ : syracuseStep 2086319 = 3129479) B3129479
theorem B3129485 : Blo 2085435 3129485 := bbase (se 3 (by rfl) ⟨586778, by rfl⟩ : syracuseStep 3129485 = 1173557) (by norm_num)
theorem B2086323 : Blo 2085435 2086323 := bstep (se 1 (by rfl) ⟨1564742, by rfl⟩ : syracuseStep 2086323 = 3129485) B3129485
theorem B4694237 : Blo 2085435 4694237 := bbase (se 3 (by rfl) ⟨880169, by rfl⟩ : syracuseStep 4694237 = 1760339) (by norm_num)
theorem B3129491 : Blo 2085435 3129491 := bstep (se 1 (by rfl) ⟨2347118, by rfl⟩ : syracuseStep 3129491 = 4694237) B4694237
theorem B2086327 : Blo 2085435 2086327 := bstep (se 1 (by rfl) ⟨1564745, by rfl⟩ : syracuseStep 2086327 = 3129491) B3129491
theorem B3520685 : Blo 2085435 3520685 := bbase (se 3 (by rfl) ⟨660128, by rfl⟩ : syracuseStep 3520685 = 1320257) (by norm_num)
theorem B2347123 : Blo 2085435 2347123 := bstep (se 1 (by rfl) ⟨1760342, by rfl⟩ : syracuseStep 2347123 = 3520685) B3520685
theorem B3129497 : Blo 2085435 3129497 := bstep (se 2 (by rfl) ⟨1173561, by rfl⟩ : syracuseStep 3129497 = 2347123) B2347123
theorem B2086331 : Blo 2085435 2086331 := bstep (se 1 (by rfl) ⟨1564748, by rfl⟩ : syracuseStep 2086331 = 3129497) B3129497
theorem B60154325 : Blo 2085435 60154325 := bbase (se 7 (by rfl) ⟨704933, by rfl⟩ : syracuseStep 60154325 = 1409867) (by norm_num)
theorem B40102883 : Blo 2085435 40102883 := bstep (se 1 (by rfl) ⟨30077162, by rfl⟩ : syracuseStep 40102883 = 60154325) B60154325
theorem B26735255 : Blo 2085435 26735255 := bstep (se 1 (by rfl) ⟨20051441, by rfl⟩ : syracuseStep 26735255 = 40102883) B40102883
theorem B17823503 : Blo 2085435 17823503 := bstep (se 1 (by rfl) ⟨13367627, by rfl⟩ : syracuseStep 17823503 = 26735255) B26735255
theorem B11882335 : Blo 2085435 11882335 := bstep (se 1 (by rfl) ⟨8911751, by rfl⟩ : syracuseStep 11882335 = 17823503) B17823503
theorem B15843113 : Blo 2085435 15843113 := bstep (se 2 (by rfl) ⟨5941167, by rfl⟩ : syracuseStep 15843113 = 11882335) B11882335
theorem B10562075 : Blo 2085435 10562075 := bstep (se 1 (by rfl) ⟨7921556, by rfl⟩ : syracuseStep 10562075 = 15843113) B15843113
theorem B7041383 : Blo 2085435 7041383 := bstep (se 1 (by rfl) ⟨5281037, by rfl⟩ : syracuseStep 7041383 = 10562075) B10562075
theorem B4694255 : Blo 2085435 4694255 := bstep (se 1 (by rfl) ⟨3520691, by rfl⟩ : syracuseStep 4694255 = 7041383) B7041383
theorem B3129503 : Blo 2085435 3129503 := bstep (se 1 (by rfl) ⟨2347127, by rfl⟩ : syracuseStep 3129503 = 4694255) B4694255
theorem B2086335 : Blo 2085435 2086335 := bstep (se 1 (by rfl) ⟨1564751, by rfl⟩ : syracuseStep 2086335 = 3129503) B3129503
theorem B3129509 : Blo 2085435 3129509 := bbase (se 4 (by rfl) ⟨293391, by rfl⟩ : syracuseStep 3129509 = 586783) (by norm_num)
theorem B2086339 : Blo 2085435 2086339 := bstep (se 1 (by rfl) ⟨1564754, by rfl⟩ : syracuseStep 2086339 = 3129509) B3129509
theorem B2640529 : Blo 2085435 2640529 := bbase (se 2 (by rfl) ⟨990198, by rfl⟩ : syracuseStep 2640529 = 1980397) (by norm_num)
theorem B3520705 : Blo 2085435 3520705 := bstep (se 2 (by rfl) ⟨1320264, by rfl⟩ : syracuseStep 3520705 = 2640529) B2640529
theorem B4694273 : Blo 2085435 4694273 := bstep (se 2 (by rfl) ⟨1760352, by rfl⟩ : syracuseStep 4694273 = 3520705) B3520705
theorem B3129515 : Blo 2085435 3129515 := bstep (se 1 (by rfl) ⟨2347136, by rfl⟩ : syracuseStep 3129515 = 4694273) B4694273
theorem B2086343 : Blo 2085435 2086343 := bstep (se 1 (by rfl) ⟨1564757, by rfl⟩ : syracuseStep 2086343 = 3129515) B3129515
theorem B2347141 : Blo 2085435 2347141 := bbase (se 4 (by rfl) ⟨220044, by rfl⟩ : syracuseStep 2347141 = 440089) (by norm_num)
theorem B3129521 : Blo 2085435 3129521 := bstep (se 2 (by rfl) ⟨1173570, by rfl⟩ : syracuseStep 3129521 = 2347141) B2347141
theorem B2086347 : Blo 2085435 2086347 := bstep (se 1 (by rfl) ⟨1564760, by rfl⟩ : syracuseStep 2086347 = 3129521) B3129521
theorem B6344453 : Blo 2085435 6344453 := bbase (se 4 (by rfl) ⟨594792, by rfl⟩ : syracuseStep 6344453 = 1189585) (by norm_num)
theorem B16918541 : Blo 2085435 16918541 := bstep (se 3 (by rfl) ⟨3172226, by rfl⟩ : syracuseStep 16918541 = 6344453) B6344453
theorem B11279027 : Blo 2085435 11279027 := bstep (se 1 (by rfl) ⟨8459270, by rfl⟩ : syracuseStep 11279027 = 16918541) B16918541
theorem B7519351 : Blo 2085435 7519351 := bstep (se 1 (by rfl) ⟨5639513, by rfl⟩ : syracuseStep 7519351 = 11279027) B11279027
theorem B10025801 : Blo 2085435 10025801 := bstep (se 2 (by rfl) ⟨3759675, by rfl⟩ : syracuseStep 10025801 = 7519351) B7519351
theorem B6683867 : Blo 2085435 6683867 := bstep (se 1 (by rfl) ⟨5012900, by rfl⟩ : syracuseStep 6683867 = 10025801) B10025801
theorem B4455911 : Blo 2085435 4455911 := bstep (se 1 (by rfl) ⟨3341933, by rfl⟩ : syracuseStep 4455911 = 6683867) B6683867
theorem B2970607 : Blo 2085435 2970607 := bstep (se 1 (by rfl) ⟨2227955, by rfl⟩ : syracuseStep 2970607 = 4455911) B4455911
theorem B3960809 : Blo 2085435 3960809 := bstep (se 2 (by rfl) ⟨1485303, by rfl⟩ : syracuseStep 3960809 = 2970607) B2970607
theorem B2640539 : Blo 2085435 2640539 := bstep (se 1 (by rfl) ⟨1980404, by rfl⟩ : syracuseStep 2640539 = 3960809) B3960809
theorem B7041437 : Blo 2085435 7041437 := bstep (se 3 (by rfl) ⟨1320269, by rfl⟩ : syracuseStep 7041437 = 2640539) B2640539
theorem B4694291 : Blo 2085435 4694291 := bstep (se 1 (by rfl) ⟨3520718, by rfl⟩ : syracuseStep 4694291 = 7041437) B7041437
theorem B3129527 : Blo 2085435 3129527 := bstep (se 1 (by rfl) ⟨2347145, by rfl⟩ : syracuseStep 3129527 = 4694291) B4694291
theorem B2086351 : Blo 2085435 2086351 := bstep (se 1 (by rfl) ⟨1564763, by rfl⟩ : syracuseStep 2086351 = 3129527) B3129527
theorem B3129533 : Blo 2085435 3129533 := bbase (se 3 (by rfl) ⟨586787, by rfl⟩ : syracuseStep 3129533 = 1173575) (by norm_num)
theorem B2086355 : Blo 2085435 2086355 := bstep (se 1 (by rfl) ⟨1564766, by rfl⟩ : syracuseStep 2086355 = 3129533) B3129533
theorem B4694309 : Blo 2085435 4694309 := bbase (se 4 (by rfl) ⟨440091, by rfl⟩ : syracuseStep 4694309 = 880183) (by norm_num)
theorem B3129539 : Blo 2085435 3129539 := bstep (se 1 (by rfl) ⟨2347154, by rfl⟩ : syracuseStep 3129539 = 4694309) B4694309
theorem B2086359 : Blo 2085435 2086359 := bstep (se 1 (by rfl) ⟨1564769, by rfl⟩ : syracuseStep 2086359 = 3129539) B3129539
theorem B5281109 : Blo 2085435 5281109 := bbase (se 14 (by rfl) ⟨483, by rfl⟩ : syracuseStep 5281109 = 967) (by norm_num)
theorem B3520739 : Blo 2085435 3520739 := bstep (se 1 (by rfl) ⟨2640554, by rfl⟩ : syracuseStep 3520739 = 5281109) B5281109
theorem B2347159 : Blo 2085435 2347159 := bstep (se 1 (by rfl) ⟨1760369, by rfl⟩ : syracuseStep 2347159 = 3520739) B3520739
theorem B3129545 : Blo 2085435 3129545 := bstep (se 2 (by rfl) ⟨1173579, by rfl⟩ : syracuseStep 3129545 = 2347159) B2347159
theorem B2086363 : Blo 2085435 2086363 := bstep (se 1 (by rfl) ⟨1564772, by rfl⟩ : syracuseStep 2086363 = 3129545) B3129545
theorem B2506469 : Blo 2085435 2506469 := bbase (se 4 (by rfl) ⟨234981, by rfl⟩ : syracuseStep 2506469 = 469963) (by norm_num)
theorem B6683917 : Blo 2085435 6683917 := bstep (se 3 (by rfl) ⟨1253234, by rfl⟩ : syracuseStep 6683917 = 2506469) B2506469
theorem B8911889 : Blo 2085435 8911889 := bstep (se 2 (by rfl) ⟨3341958, by rfl⟩ : syracuseStep 8911889 = 6683917) B6683917
theorem B5941259 : Blo 2085435 5941259 := bstep (se 1 (by rfl) ⟨4455944, by rfl⟩ : syracuseStep 5941259 = 8911889) B8911889
theorem B3960839 : Blo 2085435 3960839 := bstep (se 1 (by rfl) ⟨2970629, by rfl⟩ : syracuseStep 3960839 = 5941259) B5941259
theorem B10562237 : Blo 2085435 10562237 := bstep (se 3 (by rfl) ⟨1980419, by rfl⟩ : syracuseStep 10562237 = 3960839) B3960839
theorem B7041491 : Blo 2085435 7041491 := bstep (se 1 (by rfl) ⟨5281118, by rfl⟩ : syracuseStep 7041491 = 10562237) B10562237
theorem B4694327 : Blo 2085435 4694327 := bstep (se 1 (by rfl) ⟨3520745, by rfl⟩ : syracuseStep 4694327 = 7041491) B7041491
theorem B3129551 : Blo 2085435 3129551 := bstep (se 1 (by rfl) ⟨2347163, by rfl⟩ : syracuseStep 3129551 = 4694327) B4694327
theorem B2086367 : Blo 2085435 2086367 := bstep (se 1 (by rfl) ⟨1564775, by rfl⟩ : syracuseStep 2086367 = 3129551) B3129551
theorem B3129557 : Blo 2085435 3129557 := bbase (se 7 (by rfl) ⟨36674, by rfl⟩ : syracuseStep 3129557 = 73349) (by norm_num)
theorem B2086371 : Blo 2085435 2086371 := bstep (se 1 (by rfl) ⟨1564778, by rfl⟩ : syracuseStep 2086371 = 3129557) B3129557
theorem B2227981 : Blo 2085435 2227981 := bbase (se 3 (by rfl) ⟨417746, by rfl⟩ : syracuseStep 2227981 = 835493) (by norm_num)
theorem B2970641 : Blo 2085435 2970641 := bstep (se 2 (by rfl) ⟨1113990, by rfl⟩ : syracuseStep 2970641 = 2227981) B2227981
theorem B7921709 : Blo 2085435 7921709 := bstep (se 3 (by rfl) ⟨1485320, by rfl⟩ : syracuseStep 7921709 = 2970641) B2970641
theorem B5281139 : Blo 2085435 5281139 := bstep (se 1 (by rfl) ⟨3960854, by rfl⟩ : syracuseStep 5281139 = 7921709) B7921709
theorem B3520759 : Blo 2085435 3520759 := bstep (se 1 (by rfl) ⟨2640569, by rfl⟩ : syracuseStep 3520759 = 5281139) B5281139
theorem B4694345 : Blo 2085435 4694345 := bstep (se 2 (by rfl) ⟨1760379, by rfl⟩ : syracuseStep 4694345 = 3520759) B3520759
theorem B3129563 : Blo 2085435 3129563 := bstep (se 1 (by rfl) ⟨2347172, by rfl⟩ : syracuseStep 3129563 = 4694345) B4694345
theorem B2086375 : Blo 2085435 2086375 := bstep (se 1 (by rfl) ⟨1564781, by rfl⟩ : syracuseStep 2086375 = 3129563) B3129563
theorem B2347177 : Blo 2085435 2347177 := bbase (se 2 (by rfl) ⟨880191, by rfl⟩ : syracuseStep 2347177 = 1760383) (by norm_num)
theorem B3129569 : Blo 2085435 3129569 := bstep (se 2 (by rfl) ⟨1173588, by rfl⟩ : syracuseStep 3129569 = 2347177) B2347177
theorem B2086379 : Blo 2085435 2086379 := bstep (se 1 (by rfl) ⟨1564784, by rfl⟩ : syracuseStep 2086379 = 3129569) B3129569
theorem B8911957 : Blo 2085435 8911957 := bbase (se 8 (by rfl) ⟨52218, by rfl⟩ : syracuseStep 8911957 = 104437) (by norm_num)
theorem B11882609 : Blo 2085435 11882609 := bstep (se 2 (by rfl) ⟨4455978, by rfl⟩ : syracuseStep 11882609 = 8911957) B8911957
theorem B7921739 : Blo 2085435 7921739 := bstep (se 1 (by rfl) ⟨5941304, by rfl⟩ : syracuseStep 7921739 = 11882609) B11882609
theorem B5281159 : Blo 2085435 5281159 := bstep (se 1 (by rfl) ⟨3960869, by rfl⟩ : syracuseStep 5281159 = 7921739) B7921739
theorem B7041545 : Blo 2085435 7041545 := bstep (se 2 (by rfl) ⟨2640579, by rfl⟩ : syracuseStep 7041545 = 5281159) B5281159
theorem B4694363 : Blo 2085435 4694363 := bstep (se 1 (by rfl) ⟨3520772, by rfl⟩ : syracuseStep 4694363 = 7041545) B7041545
theorem B3129575 : Blo 2085435 3129575 := bstep (se 1 (by rfl) ⟨2347181, by rfl⟩ : syracuseStep 3129575 = 4694363) B4694363
theorem B2086383 : Blo 2085435 2086383 := bstep (se 1 (by rfl) ⟨1564787, by rfl⟩ : syracuseStep 2086383 = 3129575) B3129575
theorem B3129581 : Blo 2085435 3129581 := bbase (se 3 (by rfl) ⟨586796, by rfl⟩ : syracuseStep 3129581 = 1173593) (by norm_num)
theorem B2086387 : Blo 2085435 2086387 := bstep (se 1 (by rfl) ⟨1564790, by rfl⟩ : syracuseStep 2086387 = 3129581) B3129581
theorem B4694381 : Blo 2085435 4694381 := bbase (se 3 (by rfl) ⟨880196, by rfl⟩ : syracuseStep 4694381 = 1760393) (by norm_num)
theorem B3129587 : Blo 2085435 3129587 := bstep (se 1 (by rfl) ⟨2347190, by rfl⟩ : syracuseStep 3129587 = 4694381) B4694381
theorem B2086391 : Blo 2085435 2086391 := bstep (se 1 (by rfl) ⟨1564793, by rfl⟩ : syracuseStep 2086391 = 3129587) B3129587
theorem B3960893 : Blo 2085435 3960893 := bbase (se 3 (by rfl) ⟨742667, by rfl⟩ : syracuseStep 3960893 = 1485335) (by norm_num)
theorem B2640595 : Blo 2085435 2640595 := bstep (se 1 (by rfl) ⟨1980446, by rfl⟩ : syracuseStep 2640595 = 3960893) B3960893
theorem B3520793 : Blo 2085435 3520793 := bstep (se 2 (by rfl) ⟨1320297, by rfl⟩ : syracuseStep 3520793 = 2640595) B2640595
theorem B2347195 : Blo 2085435 2347195 := bstep (se 1 (by rfl) ⟨1760396, by rfl⟩ : syracuseStep 2347195 = 3520793) B3520793
theorem B3129593 : Blo 2085435 3129593 := bstep (se 2 (by rfl) ⟨1173597, by rfl⟩ : syracuseStep 3129593 = 2347195) B2347195
theorem B2086395 : Blo 2085435 2086395 := bstep (se 1 (by rfl) ⟨1564796, by rfl⟩ : syracuseStep 2086395 = 3129593) B3129593
theorem B2819821 : Blo 2085435 2819821 := bbase (se 3 (by rfl) ⟨528716, by rfl⟩ : syracuseStep 2819821 = 1057433) (by norm_num)
theorem B3759761 : Blo 2085435 3759761 := bstep (se 2 (by rfl) ⟨1409910, by rfl⟩ : syracuseStep 3759761 = 2819821) B2819821
theorem B2506507 : Blo 2085435 2506507 := bstep (se 1 (by rfl) ⟨1879880, by rfl⟩ : syracuseStep 2506507 = 3759761) B3759761
theorem B53472149 : Blo 2085435 53472149 := bstep (se 6 (by rfl) ⟨1253253, by rfl⟩ : syracuseStep 53472149 = 2506507) B2506507
theorem B35648099 : Blo 2085435 35648099 := bstep (se 1 (by rfl) ⟨26736074, by rfl⟩ : syracuseStep 35648099 = 53472149) B53472149
theorem B23765399 : Blo 2085435 23765399 := bstep (se 1 (by rfl) ⟨17824049, by rfl⟩ : syracuseStep 23765399 = 35648099) B35648099
theorem B15843599 : Blo 2085435 15843599 := bstep (se 1 (by rfl) ⟨11882699, by rfl⟩ : syracuseStep 15843599 = 23765399) B23765399
theorem B10562399 : Blo 2085435 10562399 := bstep (se 1 (by rfl) ⟨7921799, by rfl⟩ : syracuseStep 10562399 = 15843599) B15843599
theorem B7041599 : Blo 2085435 7041599 := bstep (se 1 (by rfl) ⟨5281199, by rfl⟩ : syracuseStep 7041599 = 10562399) B10562399
theorem B4694399 : Blo 2085435 4694399 := bstep (se 1 (by rfl) ⟨3520799, by rfl⟩ : syracuseStep 4694399 = 7041599) B7041599
theorem B3129599 : Blo 2085435 3129599 := bstep (se 1 (by rfl) ⟨2347199, by rfl⟩ : syracuseStep 3129599 = 4694399) B4694399
theorem B2086399 : Blo 2085435 2086399 := bstep (se 1 (by rfl) ⟨1564799, by rfl⟩ : syracuseStep 2086399 = 3129599) B3129599
theorem B3129605 : Blo 2085435 3129605 := bbase (se 4 (by rfl) ⟨293400, by rfl⟩ : syracuseStep 3129605 = 586801) (by norm_num)
theorem B2086403 : Blo 2085435 2086403 := bstep (se 1 (by rfl) ⟨1564802, by rfl⟩ : syracuseStep 2086403 = 3129605) B3129605
theorem B3520813 : Blo 2085435 3520813 := bbase (se 3 (by rfl) ⟨660152, by rfl⟩ : syracuseStep 3520813 = 1320305) (by norm_num)
theorem B4694417 : Blo 2085435 4694417 := bstep (se 2 (by rfl) ⟨1760406, by rfl⟩ : syracuseStep 4694417 = 3520813) B3520813
theorem B3129611 : Blo 2085435 3129611 := bstep (se 1 (by rfl) ⟨2347208, by rfl⟩ : syracuseStep 3129611 = 4694417) B4694417
theorem B2086407 : Blo 2085435 2086407 := bstep (se 1 (by rfl) ⟨1564805, by rfl⟩ : syracuseStep 2086407 = 3129611) B3129611
theorem B2347213 : Blo 2085435 2347213 := bbase (se 3 (by rfl) ⟨440102, by rfl⟩ : syracuseStep 2347213 = 880205) (by norm_num)
theorem B3129617 : Blo 2085435 3129617 := bstep (se 2 (by rfl) ⟨1173606, by rfl⟩ : syracuseStep 3129617 = 2347213) B2347213
theorem B2086411 : Blo 2085435 2086411 := bstep (se 1 (by rfl) ⟨1564808, by rfl⟩ : syracuseStep 2086411 = 3129617) B3129617
theorem B7041653 : Blo 2085435 7041653 := bbase (se 5 (by rfl) ⟨330077, by rfl⟩ : syracuseStep 7041653 = 660155) (by norm_num)
theorem B4694435 : Blo 2085435 4694435 := bstep (se 1 (by rfl) ⟨3520826, by rfl⟩ : syracuseStep 4694435 = 7041653) B7041653
theorem B3129623 : Blo 2085435 3129623 := bstep (se 1 (by rfl) ⟨2347217, by rfl⟩ : syracuseStep 3129623 = 4694435) B4694435
theorem B2086415 : Blo 2085435 2086415 := bstep (se 1 (by rfl) ⟨1564811, by rfl⟩ : syracuseStep 2086415 = 3129623) B3129623
theorem B3129629 : Blo 2085435 3129629 := bbase (se 3 (by rfl) ⟨586805, by rfl⟩ : syracuseStep 3129629 = 1173611) (by norm_num)
theorem B2086419 : Blo 2085435 2086419 := bstep (se 1 (by rfl) ⟨1564814, by rfl⟩ : syracuseStep 2086419 = 3129629) B3129629
theorem B4694453 : Blo 2085435 4694453 := bbase (se 5 (by rfl) ⟨220052, by rfl⟩ : syracuseStep 4694453 = 440105) (by norm_num)
theorem B3129635 : Blo 2085435 3129635 := bstep (se 1 (by rfl) ⟨2347226, by rfl⟩ : syracuseStep 3129635 = 4694453) B4694453
theorem B2086423 : Blo 2085435 2086423 := bstep (se 1 (by rfl) ⟨1564817, by rfl⟩ : syracuseStep 2086423 = 3129635) B3129635
theorem B14275541 : Blo 2085435 14275541 := bbase (se 7 (by rfl) ⟨167291, by rfl⟩ : syracuseStep 14275541 = 334583) (by norm_num)
theorem B9517027 : Blo 2085435 9517027 := bstep (se 1 (by rfl) ⟨7137770, by rfl⟩ : syracuseStep 9517027 = 14275541) B14275541
theorem B12689369 : Blo 2085435 12689369 := bstep (se 2 (by rfl) ⟨4758513, by rfl⟩ : syracuseStep 12689369 = 9517027) B9517027
theorem B8459579 : Blo 2085435 8459579 := bstep (se 1 (by rfl) ⟨6344684, by rfl⟩ : syracuseStep 8459579 = 12689369) B12689369
theorem B5639719 : Blo 2085435 5639719 := bstep (se 1 (by rfl) ⟨4229789, by rfl⟩ : syracuseStep 5639719 = 8459579) B8459579
theorem B7519625 : Blo 2085435 7519625 := bstep (se 2 (by rfl) ⟨2819859, by rfl⟩ : syracuseStep 7519625 = 5639719) B5639719
theorem B5013083 : Blo 2085435 5013083 := bstep (se 1 (by rfl) ⟨3759812, by rfl⟩ : syracuseStep 5013083 = 7519625) B7519625
theorem B3342055 : Blo 2085435 3342055 := bstep (se 1 (by rfl) ⟨2506541, by rfl⟩ : syracuseStep 3342055 = 5013083) B5013083
theorem B4456073 : Blo 2085435 4456073 := bstep (se 2 (by rfl) ⟨1671027, by rfl⟩ : syracuseStep 4456073 = 3342055) B3342055
theorem B11882861 : Blo 2085435 11882861 := bstep (se 3 (by rfl) ⟨2228036, by rfl⟩ : syracuseStep 11882861 = 4456073) B4456073
theorem B7921907 : Blo 2085435 7921907 := bstep (se 1 (by rfl) ⟨5941430, by rfl⟩ : syracuseStep 7921907 = 11882861) B11882861
theorem B5281271 : Blo 2085435 5281271 := bstep (se 1 (by rfl) ⟨3960953, by rfl⟩ : syracuseStep 5281271 = 7921907) B7921907
theorem B3520847 : Blo 2085435 3520847 := bstep (se 1 (by rfl) ⟨2640635, by rfl⟩ : syracuseStep 3520847 = 5281271) B5281271
theorem B2347231 : Blo 2085435 2347231 := bstep (se 1 (by rfl) ⟨1760423, by rfl⟩ : syracuseStep 2347231 = 3520847) B3520847
theorem B3129641 : Blo 2085435 3129641 := bstep (se 2 (by rfl) ⟨1173615, by rfl⟩ : syracuseStep 3129641 = 2347231) B2347231
theorem B2086427 : Blo 2085435 2086427 := bstep (se 1 (by rfl) ⟨1564820, by rfl⟩ : syracuseStep 2086427 = 3129641) B3129641
theorem B3342061 : Blo 2085435 3342061 := bbase (se 3 (by rfl) ⟨626636, by rfl⟩ : syracuseStep 3342061 = 1253273) (by norm_num)
theorem B4456081 : Blo 2085435 4456081 := bstep (se 2 (by rfl) ⟨1671030, by rfl⟩ : syracuseStep 4456081 = 3342061) B3342061
theorem B5941441 : Blo 2085435 5941441 := bstep (se 2 (by rfl) ⟨2228040, by rfl⟩ : syracuseStep 5941441 = 4456081) B4456081
theorem B7921921 : Blo 2085435 7921921 := bstep (se 2 (by rfl) ⟨2970720, by rfl⟩ : syracuseStep 7921921 = 5941441) B5941441
theorem B10562561 : Blo 2085435 10562561 := bstep (se 2 (by rfl) ⟨3960960, by rfl⟩ : syracuseStep 10562561 = 7921921) B7921921
theorem B7041707 : Blo 2085435 7041707 := bstep (se 1 (by rfl) ⟨5281280, by rfl⟩ : syracuseStep 7041707 = 10562561) B10562561
theorem B4694471 : Blo 2085435 4694471 := bstep (se 1 (by rfl) ⟨3520853, by rfl⟩ : syracuseStep 4694471 = 7041707) B7041707
theorem B3129647 : Blo 2085435 3129647 := bstep (se 1 (by rfl) ⟨2347235, by rfl⟩ : syracuseStep 3129647 = 4694471) B4694471
theorem B2086431 : Blo 2085435 2086431 := bstep (se 1 (by rfl) ⟨1564823, by rfl⟩ : syracuseStep 2086431 = 3129647) B3129647
theorem B3129653 : Blo 2085435 3129653 := bbase (se 5 (by rfl) ⟨146702, by rfl⟩ : syracuseStep 3129653 = 293405) (by norm_num)
theorem B2086435 : Blo 2085435 2086435 := bstep (se 1 (by rfl) ⟨1564826, by rfl⟩ : syracuseStep 2086435 = 3129653) B3129653
theorem B5281301 : Blo 2085435 5281301 := bbase (se 6 (by rfl) ⟨123780, by rfl⟩ : syracuseStep 5281301 = 247561) (by norm_num)
theorem B3520867 : Blo 2085435 3520867 := bstep (se 1 (by rfl) ⟨2640650, by rfl⟩ : syracuseStep 3520867 = 5281301) B5281301
theorem B4694489 : Blo 2085435 4694489 := bstep (se 2 (by rfl) ⟨1760433, by rfl⟩ : syracuseStep 4694489 = 3520867) B3520867
theorem B3129659 : Blo 2085435 3129659 := bstep (se 1 (by rfl) ⟨2347244, by rfl⟩ : syracuseStep 3129659 = 4694489) B4694489
theorem B2086439 : Blo 2085435 2086439 := bstep (se 1 (by rfl) ⟨1564829, by rfl⟩ : syracuseStep 2086439 = 3129659) B3129659
theorem B2347249 : Blo 2085435 2347249 := bbase (se 2 (by rfl) ⟨880218, by rfl⟩ : syracuseStep 2347249 = 1760437) (by norm_num)
theorem B3129665 : Blo 2085435 3129665 := bstep (se 2 (by rfl) ⟨1173624, by rfl⟩ : syracuseStep 3129665 = 2347249) B2347249
theorem B2086443 : Blo 2085435 2086443 := bstep (se 1 (by rfl) ⟨1564832, by rfl⟩ : syracuseStep 2086443 = 3129665) B3129665
theorem B3387685 : Blo 2085435 3387685 := bbase (se 4 (by rfl) ⟨317595, by rfl⟩ : syracuseStep 3387685 = 635191) (by norm_num)
theorem B4516913 : Blo 2085435 4516913 := bstep (se 2 (by rfl) ⟨1693842, by rfl⟩ : syracuseStep 4516913 = 3387685) B3387685
theorem B3011275 : Blo 2085435 3011275 := bstep (se 1 (by rfl) ⟨2258456, by rfl⟩ : syracuseStep 3011275 = 4516913) B4516913
theorem B4015033 : Blo 2085435 4015033 := bstep (se 2 (by rfl) ⟨1505637, by rfl⟩ : syracuseStep 4015033 = 3011275) B3011275
theorem B85654037 : Blo 2085435 85654037 := bstep (se 6 (by rfl) ⟨2007516, by rfl⟩ : syracuseStep 85654037 = 4015033) B4015033
theorem B57102691 : Blo 2085435 57102691 := bstep (se 1 (by rfl) ⟨42827018, by rfl⟩ : syracuseStep 57102691 = 85654037) B85654037
theorem B76136921 : Blo 2085435 76136921 := bstep (se 2 (by rfl) ⟨28551345, by rfl⟩ : syracuseStep 76136921 = 57102691) B57102691
theorem B50757947 : Blo 2085435 50757947 := bstep (se 1 (by rfl) ⟨38068460, by rfl⟩ : syracuseStep 50757947 = 76136921) B76136921
theorem B33838631 : Blo 2085435 33838631 := bstep (se 1 (by rfl) ⟨25378973, by rfl⟩ : syracuseStep 33838631 = 50757947) B50757947
theorem B22559087 : Blo 2085435 22559087 := bstep (se 1 (by rfl) ⟨16919315, by rfl⟩ : syracuseStep 22559087 = 33838631) B33838631
theorem B15039391 : Blo 2085435 15039391 := bstep (se 1 (by rfl) ⟨11279543, by rfl⟩ : syracuseStep 15039391 = 22559087) B22559087
theorem B20052521 : Blo 2085435 20052521 := bstep (se 2 (by rfl) ⟨7519695, by rfl⟩ : syracuseStep 20052521 = 15039391) B15039391
theorem B13368347 : Blo 2085435 13368347 := bstep (se 1 (by rfl) ⟨10026260, by rfl⟩ : syracuseStep 13368347 = 20052521) B20052521
theorem B8912231 : Blo 2085435 8912231 := bstep (se 1 (by rfl) ⟨6684173, by rfl⟩ : syracuseStep 8912231 = 13368347) B13368347
theorem B5941487 : Blo 2085435 5941487 := bstep (se 1 (by rfl) ⟨4456115, by rfl⟩ : syracuseStep 5941487 = 8912231) B8912231
theorem B3960991 : Blo 2085435 3960991 := bstep (se 1 (by rfl) ⟨2970743, by rfl⟩ : syracuseStep 3960991 = 5941487) B5941487
theorem B5281321 : Blo 2085435 5281321 := bstep (se 2 (by rfl) ⟨1980495, by rfl⟩ : syracuseStep 5281321 = 3960991) B3960991
theorem B7041761 : Blo 2085435 7041761 := bstep (se 2 (by rfl) ⟨2640660, by rfl⟩ : syracuseStep 7041761 = 5281321) B5281321
theorem B4694507 : Blo 2085435 4694507 := bstep (se 1 (by rfl) ⟨3520880, by rfl⟩ : syracuseStep 4694507 = 7041761) B7041761
theorem B3129671 : Blo 2085435 3129671 := bstep (se 1 (by rfl) ⟨2347253, by rfl⟩ : syracuseStep 3129671 = 4694507) B4694507
theorem B2086447 : Blo 2085435 2086447 := bstep (se 1 (by rfl) ⟨1564835, by rfl⟩ : syracuseStep 2086447 = 3129671) B3129671
theorem B3129677 : Blo 2085435 3129677 := bbase (se 3 (by rfl) ⟨586814, by rfl⟩ : syracuseStep 3129677 = 1173629) (by norm_num)
theorem B2086451 : Blo 2085435 2086451 := bstep (se 1 (by rfl) ⟨1564838, by rfl⟩ : syracuseStep 2086451 = 3129677) B3129677
theorem B4694525 : Blo 2085435 4694525 := bbase (se 3 (by rfl) ⟨880223, by rfl⟩ : syracuseStep 4694525 = 1760447) (by norm_num)
theorem B3129683 : Blo 2085435 3129683 := bstep (se 1 (by rfl) ⟨2347262, by rfl⟩ : syracuseStep 3129683 = 4694525) B4694525
theorem B2086455 : Blo 2085435 2086455 := bstep (se 1 (by rfl) ⟨1564841, by rfl⟩ : syracuseStep 2086455 = 3129683) B3129683
theorem B3520901 : Blo 2085435 3520901 := bbase (se 4 (by rfl) ⟨330084, by rfl⟩ : syracuseStep 3520901 = 660169) (by norm_num)
theorem B2347267 : Blo 2085435 2347267 := bstep (se 1 (by rfl) ⟨1760450, by rfl⟩ : syracuseStep 2347267 = 3520901) B3520901
theorem B3129689 : Blo 2085435 3129689 := bstep (se 2 (by rfl) ⟨1173633, by rfl⟩ : syracuseStep 3129689 = 2347267) B2347267
theorem B2086459 : Blo 2085435 2086459 := bstep (se 1 (by rfl) ⟨1564844, by rfl⟩ : syracuseStep 2086459 = 3129689) B3129689
theorem B15844085 : Blo 2085435 15844085 := bbase (se 5 (by rfl) ⟨742691, by rfl⟩ : syracuseStep 15844085 = 1485383) (by norm_num)
theorem B10562723 : Blo 2085435 10562723 := bstep (se 1 (by rfl) ⟨7922042, by rfl⟩ : syracuseStep 10562723 = 15844085) B15844085
theorem B7041815 : Blo 2085435 7041815 := bstep (se 1 (by rfl) ⟨5281361, by rfl⟩ : syracuseStep 7041815 = 10562723) B10562723
theorem B4694543 : Blo 2085435 4694543 := bstep (se 1 (by rfl) ⟨3520907, by rfl⟩ : syracuseStep 4694543 = 7041815) B7041815
theorem B3129695 : Blo 2085435 3129695 := bstep (se 1 (by rfl) ⟨2347271, by rfl⟩ : syracuseStep 3129695 = 4694543) B4694543
theorem B2086463 : Blo 2085435 2086463 := bstep (se 1 (by rfl) ⟨1564847, by rfl⟩ : syracuseStep 2086463 = 3129695) B3129695
theorem B3129701 : Blo 2085435 3129701 := bbase (se 4 (by rfl) ⟨293409, by rfl⟩ : syracuseStep 3129701 = 586819) (by norm_num)
theorem B2086467 : Blo 2085435 2086467 := bstep (se 1 (by rfl) ⟨1564850, by rfl⟩ : syracuseStep 2086467 = 3129701) B3129701
theorem B3961037 : Blo 2085435 3961037 := bbase (se 3 (by rfl) ⟨742694, by rfl⟩ : syracuseStep 3961037 = 1485389) (by norm_num)
theorem B2640691 : Blo 2085435 2640691 := bstep (se 1 (by rfl) ⟨1980518, by rfl⟩ : syracuseStep 2640691 = 3961037) B3961037
theorem B3520921 : Blo 2085435 3520921 := bstep (se 2 (by rfl) ⟨1320345, by rfl⟩ : syracuseStep 3520921 = 2640691) B2640691
theorem B4694561 : Blo 2085435 4694561 := bstep (se 2 (by rfl) ⟨1760460, by rfl⟩ : syracuseStep 4694561 = 3520921) B3520921
theorem B3129707 : Blo 2085435 3129707 := bstep (se 1 (by rfl) ⟨2347280, by rfl⟩ : syracuseStep 3129707 = 4694561) B4694561
theorem B2086471 : Blo 2085435 2086471 := bstep (se 1 (by rfl) ⟨1564853, by rfl⟩ : syracuseStep 2086471 = 3129707) B3129707
theorem B2347285 : Blo 2085435 2347285 := bbase (se 6 (by rfl) ⟨55014, by rfl⟩ : syracuseStep 2347285 = 110029) (by norm_num)
theorem B3129713 : Blo 2085435 3129713 := bstep (se 2 (by rfl) ⟨1173642, by rfl⟩ : syracuseStep 3129713 = 2347285) B2347285
theorem B2086475 : Blo 2085435 2086475 := bstep (se 1 (by rfl) ⟨1564856, by rfl⟩ : syracuseStep 2086475 = 3129713) B3129713
theorem B2640701 : Blo 2085435 2640701 := bbase (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) (by norm_num)
theorem B7041869 : Blo 2085435 7041869 := bstep (se 3 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 7041869 = 2640701) B2640701
theorem B4694579 : Blo 2085435 4694579 := bstep (se 1 (by rfl) ⟨3520934, by rfl⟩ : syracuseStep 4694579 = 7041869) B7041869
theorem B3129719 : Blo 2085435 3129719 := bstep (se 1 (by rfl) ⟨2347289, by rfl⟩ : syracuseStep 3129719 = 4694579) B4694579
theorem B2086479 : Blo 2085435 2086479 := bstep (se 1 (by rfl) ⟨1564859, by rfl⟩ : syracuseStep 2086479 = 3129719) B3129719
theorem B3129725 : Blo 2085435 3129725 := bbase (se 3 (by rfl) ⟨586823, by rfl⟩ : syracuseStep 3129725 = 1173647) (by norm_num)
theorem B2086483 : Blo 2085435 2086483 := bstep (se 1 (by rfl) ⟨1564862, by rfl⟩ : syracuseStep 2086483 = 3129725) B3129725
theorem B4694597 : Blo 2085435 4694597 := bbase (se 4 (by rfl) ⟨440118, by rfl⟩ : syracuseStep 4694597 = 880237) (by norm_num)
theorem B3129731 : Blo 2085435 3129731 := bstep (se 1 (by rfl) ⟨2347298, by rfl⟩ : syracuseStep 3129731 = 4694597) B4694597
theorem B2086487 : Blo 2085435 2086487 := bstep (se 1 (by rfl) ⟨1564865, by rfl⟩ : syracuseStep 2086487 = 3129731) B3129731
theorem B2228105 : Blo 2085435 2228105 := bbase (se 2 (by rfl) ⟨835539, by rfl⟩ : syracuseStep 2228105 = 1671079) (by norm_num)
theorem B5941613 : Blo 2085435 5941613 := bstep (se 3 (by rfl) ⟨1114052, by rfl⟩ : syracuseStep 5941613 = 2228105) B2228105
theorem B3961075 : Blo 2085435 3961075 := bstep (se 1 (by rfl) ⟨2970806, by rfl⟩ : syracuseStep 3961075 = 5941613) B5941613
theorem B5281433 : Blo 2085435 5281433 := bstep (se 2 (by rfl) ⟨1980537, by rfl⟩ : syracuseStep 5281433 = 3961075) B3961075
theorem B3520955 : Blo 2085435 3520955 := bstep (se 1 (by rfl) ⟨2640716, by rfl⟩ : syracuseStep 3520955 = 5281433) B5281433
theorem B2347303 : Blo 2085435 2347303 := bstep (se 1 (by rfl) ⟨1760477, by rfl⟩ : syracuseStep 2347303 = 3520955) B3520955
theorem B3129737 : Blo 2085435 3129737 := bstep (se 2 (by rfl) ⟨1173651, by rfl⟩ : syracuseStep 3129737 = 2347303) B2347303
theorem B2086491 : Blo 2085435 2086491 := bstep (se 1 (by rfl) ⟨1564868, by rfl⟩ : syracuseStep 2086491 = 3129737) B3129737
theorem B10562885 : Blo 2085435 10562885 := bbase (se 4 (by rfl) ⟨990270, by rfl⟩ : syracuseStep 10562885 = 1980541) (by norm_num)
theorem B7041923 : Blo 2085435 7041923 := bstep (se 1 (by rfl) ⟨5281442, by rfl⟩ : syracuseStep 7041923 = 10562885) B10562885
theorem B4694615 : Blo 2085435 4694615 := bstep (se 1 (by rfl) ⟨3520961, by rfl⟩ : syracuseStep 4694615 = 7041923) B7041923
theorem B3129743 : Blo 2085435 3129743 := bstep (se 1 (by rfl) ⟨2347307, by rfl⟩ : syracuseStep 3129743 = 4694615) B4694615
theorem B2086495 : Blo 2085435 2086495 := bstep (se 1 (by rfl) ⟨1564871, by rfl⟩ : syracuseStep 2086495 = 3129743) B3129743
theorem B3129749 : Blo 2085435 3129749 := bbase (se 6 (by rfl) ⟨73353, by rfl⟩ : syracuseStep 3129749 = 146707) (by norm_num)
theorem B2086499 : Blo 2085435 2086499 := bstep (se 1 (by rfl) ⟨1564874, by rfl⟩ : syracuseStep 2086499 = 3129749) B3129749
theorem B3759949 : Blo 2085435 3759949 := bbase (se 3 (by rfl) ⟨704990, by rfl⟩ : syracuseStep 3759949 = 1409981) (by norm_num)
theorem B5013265 : Blo 2085435 5013265 := bstep (se 2 (by rfl) ⟨1879974, by rfl⟩ : syracuseStep 5013265 = 3759949) B3759949
theorem B6684353 : Blo 2085435 6684353 := bstep (se 2 (by rfl) ⟨2506632, by rfl⟩ : syracuseStep 6684353 = 5013265) B5013265
theorem B4456235 : Blo 2085435 4456235 := bstep (se 1 (by rfl) ⟨3342176, by rfl⟩ : syracuseStep 4456235 = 6684353) B6684353
theorem B11883293 : Blo 2085435 11883293 := bstep (se 3 (by rfl) ⟨2228117, by rfl⟩ : syracuseStep 11883293 = 4456235) B4456235
theorem B7922195 : Blo 2085435 7922195 := bstep (se 1 (by rfl) ⟨5941646, by rfl⟩ : syracuseStep 7922195 = 11883293) B11883293
theorem B5281463 : Blo 2085435 5281463 := bstep (se 1 (by rfl) ⟨3961097, by rfl⟩ : syracuseStep 5281463 = 7922195) B7922195
theorem B3520975 : Blo 2085435 3520975 := bstep (se 1 (by rfl) ⟨2640731, by rfl⟩ : syracuseStep 3520975 = 5281463) B5281463
theorem B4694633 : Blo 2085435 4694633 := bstep (se 2 (by rfl) ⟨1760487, by rfl⟩ : syracuseStep 4694633 = 3520975) B3520975
theorem B3129755 : Blo 2085435 3129755 := bstep (se 1 (by rfl) ⟨2347316, by rfl⟩ : syracuseStep 3129755 = 4694633) B4694633
theorem B2086503 : Blo 2085435 2086503 := bstep (se 1 (by rfl) ⟨1564877, by rfl⟩ : syracuseStep 2086503 = 3129755) B3129755
theorem B2347321 : Blo 2085435 2347321 := bbase (se 2 (by rfl) ⟨880245, by rfl⟩ : syracuseStep 2347321 = 1760491) (by norm_num)
theorem B3129761 : Blo 2085435 3129761 := bstep (se 2 (by rfl) ⟨1173660, by rfl⟩ : syracuseStep 3129761 = 2347321) B2347321
theorem B2086507 : Blo 2085435 2086507 := bstep (se 1 (by rfl) ⟨1564880, by rfl⟩ : syracuseStep 2086507 = 3129761) B3129761
theorem B5941669 : Blo 2085435 5941669 := bbase (se 4 (by rfl) ⟨557031, by rfl⟩ : syracuseStep 5941669 = 1114063) (by norm_num)
theorem B7922225 : Blo 2085435 7922225 := bstep (se 2 (by rfl) ⟨2970834, by rfl⟩ : syracuseStep 7922225 = 5941669) B5941669
theorem B5281483 : Blo 2085435 5281483 := bstep (se 1 (by rfl) ⟨3961112, by rfl⟩ : syracuseStep 5281483 = 7922225) B7922225
theorem B7041977 : Blo 2085435 7041977 := bstep (se 2 (by rfl) ⟨2640741, by rfl⟩ : syracuseStep 7041977 = 5281483) B5281483
theorem B4694651 : Blo 2085435 4694651 := bstep (se 1 (by rfl) ⟨3520988, by rfl⟩ : syracuseStep 4694651 = 7041977) B7041977
theorem B3129767 : Blo 2085435 3129767 := bstep (se 1 (by rfl) ⟨2347325, by rfl⟩ : syracuseStep 3129767 = 4694651) B4694651
theorem B2086511 : Blo 2085435 2086511 := bstep (se 1 (by rfl) ⟨1564883, by rfl⟩ : syracuseStep 2086511 = 3129767) B3129767
theorem B3129773 : Blo 2085435 3129773 := bbase (se 3 (by rfl) ⟨586832, by rfl⟩ : syracuseStep 3129773 = 1173665) (by norm_num)
theorem B2086515 : Blo 2085435 2086515 := bstep (se 1 (by rfl) ⟨1564886, by rfl⟩ : syracuseStep 2086515 = 3129773) B3129773
theorem B4694669 : Blo 2085435 4694669 := bbase (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) (by norm_num)
theorem B3129779 : Blo 2085435 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B2086519 : Blo 2085435 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B2640757 : Blo 2085435 2640757 := bbase (se 5 (by rfl) ⟨123785, by rfl⟩ : syracuseStep 2640757 = 247571) (by norm_num)
theorem B3521009 : Blo 2085435 3521009 := bstep (se 2 (by rfl) ⟨1320378, by rfl⟩ : syracuseStep 3521009 = 2640757) B2640757
theorem B2347339 : Blo 2085435 2347339 := bstep (se 1 (by rfl) ⟨1760504, by rfl⟩ : syracuseStep 2347339 = 3521009) B3521009
theorem B3129785 : Blo 2085435 3129785 := bstep (se 2 (by rfl) ⟨1173669, by rfl⟩ : syracuseStep 3129785 = 2347339) B2347339
theorem B2086523 : Blo 2085435 2086523 := bstep (se 1 (by rfl) ⟨1564892, by rfl⟩ : syracuseStep 2086523 = 3129785) B3129785
theorem B3172493 : Blo 2085435 3172493 := bbase (se 3 (by rfl) ⟨594842, by rfl⟩ : syracuseStep 3172493 = 1189685) (by norm_num)
theorem B8459981 : Blo 2085435 8459981 := bstep (se 3 (by rfl) ⟨1586246, by rfl⟩ : syracuseStep 8459981 = 3172493) B3172493
theorem B5639987 : Blo 2085435 5639987 := bstep (se 1 (by rfl) ⟨4229990, by rfl⟩ : syracuseStep 5639987 = 8459981) B8459981
theorem B15039965 : Blo 2085435 15039965 := bstep (se 3 (by rfl) ⟨2819993, by rfl⟩ : syracuseStep 15039965 = 5639987) B5639987
theorem B40106573 : Blo 2085435 40106573 := bstep (se 3 (by rfl) ⟨7519982, by rfl⟩ : syracuseStep 40106573 = 15039965) B15039965
theorem B26737715 : Blo 2085435 26737715 := bstep (se 1 (by rfl) ⟨20053286, by rfl⟩ : syracuseStep 26737715 = 40106573) B40106573
theorem B17825143 : Blo 2085435 17825143 := bstep (se 1 (by rfl) ⟨13368857, by rfl⟩ : syracuseStep 17825143 = 26737715) B26737715
theorem B23766857 : Blo 2085435 23766857 := bstep (se 2 (by rfl) ⟨8912571, by rfl⟩ : syracuseStep 23766857 = 17825143) B17825143
theorem B15844571 : Blo 2085435 15844571 := bstep (se 1 (by rfl) ⟨11883428, by rfl⟩ : syracuseStep 15844571 = 23766857) B23766857
theorem B10563047 : Blo 2085435 10563047 := bstep (se 1 (by rfl) ⟨7922285, by rfl⟩ : syracuseStep 10563047 = 15844571) B15844571
theorem B7042031 : Blo 2085435 7042031 := bstep (se 1 (by rfl) ⟨5281523, by rfl⟩ : syracuseStep 7042031 = 10563047) B10563047
theorem B4694687 : Blo 2085435 4694687 := bstep (se 1 (by rfl) ⟨3521015, by rfl⟩ : syracuseStep 4694687 = 7042031) B7042031
theorem B3129791 : Blo 2085435 3129791 := bstep (se 1 (by rfl) ⟨2347343, by rfl⟩ : syracuseStep 3129791 = 4694687) B4694687
theorem B2086527 : Blo 2085435 2086527 := bstep (se 1 (by rfl) ⟨1564895, by rfl⟩ : syracuseStep 2086527 = 3129791) B3129791
theorem B3129797 : Blo 2085435 3129797 := bbase (se 4 (by rfl) ⟨293418, by rfl⟩ : syracuseStep 3129797 = 586837) (by norm_num)
theorem B2086531 : Blo 2085435 2086531 := bstep (se 1 (by rfl) ⟨1564898, by rfl⟩ : syracuseStep 2086531 = 3129797) B3129797
theorem B3521029 : Blo 2085435 3521029 := bbase (se 4 (by rfl) ⟨330096, by rfl⟩ : syracuseStep 3521029 = 660193) (by norm_num)
theorem B4694705 : Blo 2085435 4694705 := bstep (se 2 (by rfl) ⟨1760514, by rfl⟩ : syracuseStep 4694705 = 3521029) B3521029
theorem B3129803 : Blo 2085435 3129803 := bstep (se 1 (by rfl) ⟨2347352, by rfl⟩ : syracuseStep 3129803 = 4694705) B4694705
theorem B2086535 : Blo 2085435 2086535 := bstep (se 1 (by rfl) ⟨1564901, by rfl⟩ : syracuseStep 2086535 = 3129803) B3129803
theorem B2347357 : Blo 2085435 2347357 := bbase (se 3 (by rfl) ⟨440129, by rfl⟩ : syracuseStep 2347357 = 880259) (by norm_num)
theorem B3129809 : Blo 2085435 3129809 := bstep (se 2 (by rfl) ⟨1173678, by rfl⟩ : syracuseStep 3129809 = 2347357) B2347357
theorem B2086539 : Blo 2085435 2086539 := bstep (se 1 (by rfl) ⟨1564904, by rfl⟩ : syracuseStep 2086539 = 3129809) B3129809
theorem B7042085 : Blo 2085435 7042085 := bbase (se 4 (by rfl) ⟨660195, by rfl⟩ : syracuseStep 7042085 = 1320391) (by norm_num)
theorem B4694723 : Blo 2085435 4694723 := bstep (se 1 (by rfl) ⟨3521042, by rfl⟩ : syracuseStep 4694723 = 7042085) B7042085
theorem B3129815 : Blo 2085435 3129815 := bstep (se 1 (by rfl) ⟨2347361, by rfl⟩ : syracuseStep 3129815 = 4694723) B4694723
theorem B2086543 : Blo 2085435 2086543 := bstep (se 1 (by rfl) ⟨1564907, by rfl⟩ : syracuseStep 2086543 = 3129815) B3129815
theorem B3129821 : Blo 2085435 3129821 := bbase (se 3 (by rfl) ⟨586841, by rfl⟩ : syracuseStep 3129821 = 1173683) (by norm_num)
theorem B2086547 : Blo 2085435 2086547 := bstep (se 1 (by rfl) ⟨1564910, by rfl⟩ : syracuseStep 2086547 = 3129821) B3129821
theorem B4694741 : Blo 2085435 4694741 := bbase (se 7 (by rfl) ⟨55016, by rfl⟩ : syracuseStep 4694741 = 110033) (by norm_num)
theorem B3129827 : Blo 2085435 3129827 := bstep (se 1 (by rfl) ⟨2347370, by rfl⟩ : syracuseStep 3129827 = 4694741) B4694741
theorem B2086551 : Blo 2085435 2086551 := bstep (se 1 (by rfl) ⟨1564913, by rfl⟩ : syracuseStep 2086551 = 3129827) B3129827
theorem B8912693 : Blo 2085435 8912693 := bbase (se 5 (by rfl) ⟨417782, by rfl⟩ : syracuseStep 8912693 = 835565) (by norm_num)
theorem B5941795 : Blo 2085435 5941795 := bstep (se 1 (by rfl) ⟨4456346, by rfl⟩ : syracuseStep 5941795 = 8912693) B8912693
theorem B7922393 : Blo 2085435 7922393 := bstep (se 2 (by rfl) ⟨2970897, by rfl⟩ : syracuseStep 7922393 = 5941795) B5941795
theorem B5281595 : Blo 2085435 5281595 := bstep (se 1 (by rfl) ⟨3961196, by rfl⟩ : syracuseStep 5281595 = 7922393) B7922393
theorem B3521063 : Blo 2085435 3521063 := bstep (se 1 (by rfl) ⟨2640797, by rfl⟩ : syracuseStep 3521063 = 5281595) B5281595
theorem B2347375 : Blo 2085435 2347375 := bstep (se 1 (by rfl) ⟨1760531, by rfl⟩ : syracuseStep 2347375 = 3521063) B3521063
theorem B3129833 : Blo 2085435 3129833 := bstep (se 2 (by rfl) ⟨1173687, by rfl⟩ : syracuseStep 3129833 = 2347375) B2347375
theorem B2086555 : Blo 2085435 2086555 := bstep (se 1 (by rfl) ⟨1564916, by rfl⟩ : syracuseStep 2086555 = 3129833) B3129833
theorem B57105749 : Blo 2085435 57105749 := bbase (se 11 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 57105749 = 83651) (by norm_num)
theorem B38070499 : Blo 2085435 38070499 := bstep (se 1 (by rfl) ⟨28552874, by rfl⟩ : syracuseStep 38070499 = 57105749) B57105749
theorem B50760665 : Blo 2085435 50760665 := bstep (se 2 (by rfl) ⟨19035249, by rfl⟩ : syracuseStep 50760665 = 38070499) B38070499
theorem B33840443 : Blo 2085435 33840443 := bstep (se 1 (by rfl) ⟨25380332, by rfl⟩ : syracuseStep 33840443 = 50760665) B50760665
theorem B22560295 : Blo 2085435 22560295 := bstep (se 1 (by rfl) ⟨16920221, by rfl⟩ : syracuseStep 22560295 = 33840443) B33840443
theorem B30080393 : Blo 2085435 30080393 := bstep (se 2 (by rfl) ⟨11280147, by rfl⟩ : syracuseStep 30080393 = 22560295) B22560295
theorem B20053595 : Blo 2085435 20053595 := bstep (se 1 (by rfl) ⟨15040196, by rfl⟩ : syracuseStep 20053595 = 30080393) B30080393
theorem B13369063 : Blo 2085435 13369063 := bstep (se 1 (by rfl) ⟨10026797, by rfl⟩ : syracuseStep 13369063 = 20053595) B20053595
theorem B17825417 : Blo 2085435 17825417 := bstep (se 2 (by rfl) ⟨6684531, by rfl⟩ : syracuseStep 17825417 = 13369063) B13369063
theorem B11883611 : Blo 2085435 11883611 := bstep (se 1 (by rfl) ⟨8912708, by rfl⟩ : syracuseStep 11883611 = 17825417) B17825417
theorem B7922407 : Blo 2085435 7922407 := bstep (se 1 (by rfl) ⟨5941805, by rfl⟩ : syracuseStep 7922407 = 11883611) B11883611
theorem B10563209 : Blo 2085435 10563209 := bstep (se 2 (by rfl) ⟨3961203, by rfl⟩ : syracuseStep 10563209 = 7922407) B7922407
theorem B7042139 : Blo 2085435 7042139 := bstep (se 1 (by rfl) ⟨5281604, by rfl⟩ : syracuseStep 7042139 = 10563209) B10563209
theorem B4694759 : Blo 2085435 4694759 := bstep (se 1 (by rfl) ⟨3521069, by rfl⟩ : syracuseStep 4694759 = 7042139) B7042139
theorem B3129839 : Blo 2085435 3129839 := bstep (se 1 (by rfl) ⟨2347379, by rfl⟩ : syracuseStep 3129839 = 4694759) B4694759
theorem B2086559 : Blo 2085435 2086559 := bstep (se 1 (by rfl) ⟨1564919, by rfl⟩ : syracuseStep 2086559 = 3129839) B3129839
theorem B3129845 : Blo 2085435 3129845 := bbase (se 5 (by rfl) ⟨146711, by rfl⟩ : syracuseStep 3129845 = 293423) (by norm_num)
theorem B2086563 : Blo 2085435 2086563 := bstep (se 1 (by rfl) ⟨1564922, by rfl⟩ : syracuseStep 2086563 = 3129845) B3129845
theorem B5941829 : Blo 2085435 5941829 := bbase (se 4 (by rfl) ⟨557046, by rfl⟩ : syracuseStep 5941829 = 1114093) (by norm_num)
theorem B3961219 : Blo 2085435 3961219 := bstep (se 1 (by rfl) ⟨2970914, by rfl⟩ : syracuseStep 3961219 = 5941829) B5941829
theorem B5281625 : Blo 2085435 5281625 := bstep (se 2 (by rfl) ⟨1980609, by rfl⟩ : syracuseStep 5281625 = 3961219) B3961219
theorem B3521083 : Blo 2085435 3521083 := bstep (se 1 (by rfl) ⟨2640812, by rfl⟩ : syracuseStep 3521083 = 5281625) B5281625
theorem B4694777 : Blo 2085435 4694777 := bstep (se 2 (by rfl) ⟨1760541, by rfl⟩ : syracuseStep 4694777 = 3521083) B3521083
theorem B3129851 : Blo 2085435 3129851 := bstep (se 1 (by rfl) ⟨2347388, by rfl⟩ : syracuseStep 3129851 = 4694777) B4694777
theorem B2086567 : Blo 2085435 2086567 := bstep (se 1 (by rfl) ⟨1564925, by rfl⟩ : syracuseStep 2086567 = 3129851) B3129851
theorem B2347393 : Blo 2085435 2347393 := bbase (se 2 (by rfl) ⟨880272, by rfl⟩ : syracuseStep 2347393 = 1760545) (by norm_num)
theorem B3129857 : Blo 2085435 3129857 := bstep (se 2 (by rfl) ⟨1173696, by rfl⟩ : syracuseStep 3129857 = 2347393) B2347393
theorem B2086571 : Blo 2085435 2086571 := bstep (se 1 (by rfl) ⟨1564928, by rfl⟩ : syracuseStep 2086571 = 3129857) B3129857
theorem B5281645 : Blo 2085435 5281645 := bbase (se 3 (by rfl) ⟨990308, by rfl⟩ : syracuseStep 5281645 = 1980617) (by norm_num)
theorem B7042193 : Blo 2085435 7042193 := bstep (se 2 (by rfl) ⟨2640822, by rfl⟩ : syracuseStep 7042193 = 5281645) B5281645
theorem B4694795 : Blo 2085435 4694795 := bstep (se 1 (by rfl) ⟨3521096, by rfl⟩ : syracuseStep 4694795 = 7042193) B7042193
theorem B3129863 : Blo 2085435 3129863 := bstep (se 1 (by rfl) ⟨2347397, by rfl⟩ : syracuseStep 3129863 = 4694795) B4694795
theorem B2086575 : Blo 2085435 2086575 := bstep (se 1 (by rfl) ⟨1564931, by rfl⟩ : syracuseStep 2086575 = 3129863) B3129863
theorem B3129869 : Blo 2085435 3129869 := bbase (se 3 (by rfl) ⟨586850, by rfl⟩ : syracuseStep 3129869 = 1173701) (by norm_num)
theorem B2086579 : Blo 2085435 2086579 := bstep (se 1 (by rfl) ⟨1564934, by rfl⟩ : syracuseStep 2086579 = 3129869) B3129869
theorem B4694813 : Blo 2085435 4694813 := bbase (se 3 (by rfl) ⟨880277, by rfl⟩ : syracuseStep 4694813 = 1760555) (by norm_num)
theorem B3129875 : Blo 2085435 3129875 := bstep (se 1 (by rfl) ⟨2347406, by rfl⟩ : syracuseStep 3129875 = 4694813) B4694813
theorem B2086583 : Blo 2085435 2086583 := bstep (se 1 (by rfl) ⟨1564937, by rfl⟩ : syracuseStep 2086583 = 3129875) B3129875
theorem B3521117 : Blo 2085435 3521117 := bbase (se 3 (by rfl) ⟨660209, by rfl⟩ : syracuseStep 3521117 = 1320419) (by norm_num)
theorem B2347411 : Blo 2085435 2347411 := bstep (se 1 (by rfl) ⟨1760558, by rfl⟩ : syracuseStep 2347411 = 3521117) B3521117
theorem B3129881 : Blo 2085435 3129881 := bstep (se 2 (by rfl) ⟨1173705, by rfl⟩ : syracuseStep 3129881 = 2347411) B2347411
theorem B2086587 : Blo 2085435 2086587 := bstep (se 1 (by rfl) ⟨1564940, by rfl⟩ : syracuseStep 2086587 = 3129881) B3129881
theorem B3342317 : Blo 2085435 3342317 := bbase (se 3 (by rfl) ⟨626684, by rfl⟩ : syracuseStep 3342317 = 1253369) (by norm_num)
theorem B8912845 : Blo 2085435 8912845 := bstep (se 3 (by rfl) ⟨1671158, by rfl⟩ : syracuseStep 8912845 = 3342317) B3342317
theorem B11883793 : Blo 2085435 11883793 := bstep (se 2 (by rfl) ⟨4456422, by rfl⟩ : syracuseStep 11883793 = 8912845) B8912845
theorem B15845057 : Blo 2085435 15845057 := bstep (se 2 (by rfl) ⟨5941896, by rfl⟩ : syracuseStep 15845057 = 11883793) B11883793
theorem B10563371 : Blo 2085435 10563371 := bstep (se 1 (by rfl) ⟨7922528, by rfl⟩ : syracuseStep 10563371 = 15845057) B15845057
theorem B7042247 : Blo 2085435 7042247 := bstep (se 1 (by rfl) ⟨5281685, by rfl⟩ : syracuseStep 7042247 = 10563371) B10563371
theorem B4694831 : Blo 2085435 4694831 := bstep (se 1 (by rfl) ⟨3521123, by rfl⟩ : syracuseStep 4694831 = 7042247) B7042247
theorem B3129887 : Blo 2085435 3129887 := bstep (se 1 (by rfl) ⟨2347415, by rfl⟩ : syracuseStep 3129887 = 4694831) B4694831
theorem B2086591 : Blo 2085435 2086591 := bstep (se 1 (by rfl) ⟨1564943, by rfl⟩ : syracuseStep 2086591 = 3129887) B3129887
theorem B3129893 : Blo 2085435 3129893 := bbase (se 4 (by rfl) ⟨293427, by rfl⟩ : syracuseStep 3129893 = 586855) (by norm_num)
theorem B2086595 : Blo 2085435 2086595 := bstep (se 1 (by rfl) ⟨1564946, by rfl⟩ : syracuseStep 2086595 = 3129893) B3129893
theorem B2640853 : Blo 2085435 2640853 := bbase (se 7 (by rfl) ⟨30947, by rfl⟩ : syracuseStep 2640853 = 61895) (by norm_num)
theorem B3521137 : Blo 2085435 3521137 := bstep (se 2 (by rfl) ⟨1320426, by rfl⟩ : syracuseStep 3521137 = 2640853) B2640853
theorem B4694849 : Blo 2085435 4694849 := bstep (se 2 (by rfl) ⟨1760568, by rfl⟩ : syracuseStep 4694849 = 3521137) B3521137
theorem B3129899 : Blo 2085435 3129899 := bstep (se 1 (by rfl) ⟨2347424, by rfl⟩ : syracuseStep 3129899 = 4694849) B4694849
theorem B2086599 : Blo 2085435 2086599 := bstep (se 1 (by rfl) ⟨1564949, by rfl⟩ : syracuseStep 2086599 = 3129899) B3129899
theorem B2347429 : Blo 2085435 2347429 := bbase (se 4 (by rfl) ⟨220071, by rfl⟩ : syracuseStep 2347429 = 440143) (by norm_num)
theorem B3129905 : Blo 2085435 3129905 := bstep (se 2 (by rfl) ⟨1173714, by rfl⟩ : syracuseStep 3129905 = 2347429) B2347429
theorem B2086603 : Blo 2085435 2086603 := bstep (se 1 (by rfl) ⟨1564952, by rfl⟩ : syracuseStep 2086603 = 3129905) B3129905
theorem B2115077 : Blo 2085435 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B5640205 : Blo 2085435 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B7520273 : Blo 2085435 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B5013515 : Blo 2085435 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B13369373 : Blo 2085435 13369373 := bstep (se 3 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 13369373 = 5013515) B5013515
theorem B8912915 : Blo 2085435 8912915 := bstep (se 1 (by rfl) ⟨6684686, by rfl⟩ : syracuseStep 8912915 = 13369373) B13369373
theorem B5941943 : Blo 2085435 5941943 := bstep (se 1 (by rfl) ⟨4456457, by rfl⟩ : syracuseStep 5941943 = 8912915) B8912915
theorem B3961295 : Blo 2085435 3961295 := bstep (se 1 (by rfl) ⟨2970971, by rfl⟩ : syracuseStep 3961295 = 5941943) B5941943
theorem B2640863 : Blo 2085435 2640863 := bstep (se 1 (by rfl) ⟨1980647, by rfl⟩ : syracuseStep 2640863 = 3961295) B3961295
theorem B7042301 : Blo 2085435 7042301 := bstep (se 3 (by rfl) ⟨1320431, by rfl⟩ : syracuseStep 7042301 = 2640863) B2640863
theorem B4694867 : Blo 2085435 4694867 := bstep (se 1 (by rfl) ⟨3521150, by rfl⟩ : syracuseStep 4694867 = 7042301) B7042301
theorem B3129911 : Blo 2085435 3129911 := bstep (se 1 (by rfl) ⟨2347433, by rfl⟩ : syracuseStep 3129911 = 4694867) B4694867
theorem B2086607 : Blo 2085435 2086607 := bstep (se 1 (by rfl) ⟨1564955, by rfl⟩ : syracuseStep 2086607 = 3129911) B3129911
theorem B3129917 : Blo 2085435 3129917 := bbase (se 3 (by rfl) ⟨586859, by rfl⟩ : syracuseStep 3129917 = 1173719) (by norm_num)
theorem B2086611 : Blo 2085435 2086611 := bstep (se 1 (by rfl) ⟨1564958, by rfl⟩ : syracuseStep 2086611 = 3129917) B3129917
theorem B4694885 : Blo 2085435 4694885 := bbase (se 4 (by rfl) ⟨440145, by rfl⟩ : syracuseStep 4694885 = 880291) (by norm_num)
theorem B3129923 : Blo 2085435 3129923 := bstep (se 1 (by rfl) ⟨2347442, by rfl⟩ : syracuseStep 3129923 = 4694885) B4694885
theorem B2086615 : Blo 2085435 2086615 := bstep (se 1 (by rfl) ⟨1564961, by rfl⟩ : syracuseStep 2086615 = 3129923) B3129923
theorem B5281757 : Blo 2085435 5281757 := bbase (se 3 (by rfl) ⟨990329, by rfl⟩ : syracuseStep 5281757 = 1980659) (by norm_num)
theorem B3521171 : Blo 2085435 3521171 := bstep (se 1 (by rfl) ⟨2640878, by rfl⟩ : syracuseStep 3521171 = 5281757) B5281757
theorem B2347447 : Blo 2085435 2347447 := bstep (se 1 (by rfl) ⟨1760585, by rfl⟩ : syracuseStep 2347447 = 3521171) B3521171
theorem B3129929 : Blo 2085435 3129929 := bstep (se 2 (by rfl) ⟨1173723, by rfl⟩ : syracuseStep 3129929 = 2347447) B2347447
theorem B2086619 : Blo 2085435 2086619 := bstep (se 1 (by rfl) ⟨1564964, by rfl⟩ : syracuseStep 2086619 = 3129929) B3129929
theorem B3961325 : Blo 2085435 3961325 := bbase (se 3 (by rfl) ⟨742748, by rfl⟩ : syracuseStep 3961325 = 1485497) (by norm_num)
theorem B10563533 : Blo 2085435 10563533 := bstep (se 3 (by rfl) ⟨1980662, by rfl⟩ : syracuseStep 10563533 = 3961325) B3961325
theorem B7042355 : Blo 2085435 7042355 := bstep (se 1 (by rfl) ⟨5281766, by rfl⟩ : syracuseStep 7042355 = 10563533) B10563533
theorem B4694903 : Blo 2085435 4694903 := bstep (se 1 (by rfl) ⟨3521177, by rfl⟩ : syracuseStep 4694903 = 7042355) B7042355
theorem B3129935 : Blo 2085435 3129935 := bstep (se 1 (by rfl) ⟨2347451, by rfl⟩ : syracuseStep 3129935 = 4694903) B4694903
theorem B2086623 : Blo 2085435 2086623 := bstep (se 1 (by rfl) ⟨1564967, by rfl⟩ : syracuseStep 2086623 = 3129935) B3129935
theorem B3129941 : Blo 2085435 3129941 := bbase (se 8 (by rfl) ⟨18339, by rfl⟩ : syracuseStep 3129941 = 36679) (by norm_num)
theorem B2086627 : Blo 2085435 2086627 := bstep (se 1 (by rfl) ⟨1564970, by rfl⟩ : syracuseStep 2086627 = 3129941) B3129941
theorem B2478217 : Blo 2085435 2478217 := bbase (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) (by norm_num)
theorem B52868629 : Blo 2085435 52868629 := bstep (se 6 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 52868629 = 2478217) B2478217
theorem B70491505 : Blo 2085435 70491505 := bstep (se 2 (by rfl) ⟨26434314, by rfl⟩ : syracuseStep 70491505 = 52868629) B52868629
theorem B93988673 : Blo 2085435 93988673 := bstep (se 2 (by rfl) ⟨35245752, by rfl⟩ : syracuseStep 93988673 = 70491505) B70491505
theorem B62659115 : Blo 2085435 62659115 := bstep (se 1 (by rfl) ⟨46994336, by rfl⟩ : syracuseStep 62659115 = 93988673) B93988673
theorem B41772743 : Blo 2085435 41772743 := bstep (se 1 (by rfl) ⟨31329557, by rfl⟩ : syracuseStep 41772743 = 62659115) B62659115
theorem B27848495 : Blo 2085435 27848495 := bstep (se 1 (by rfl) ⟨20886371, by rfl⟩ : syracuseStep 27848495 = 41772743) B41772743
theorem B74262653 : Blo 2085435 74262653 := bstep (se 3 (by rfl) ⟨13924247, by rfl⟩ : syracuseStep 74262653 = 27848495) B27848495
theorem B49508435 : Blo 2085435 49508435 := bstep (se 1 (by rfl) ⟨37131326, by rfl⟩ : syracuseStep 49508435 = 74262653) B74262653
theorem B132022493 : Blo 2085435 132022493 := bstep (se 3 (by rfl) ⟨24754217, by rfl⟩ : syracuseStep 132022493 = 49508435) B49508435
theorem B88014995 : Blo 2085435 88014995 := bstep (se 1 (by rfl) ⟨66011246, by rfl⟩ : syracuseStep 88014995 = 132022493) B132022493
theorem B58676663 : Blo 2085435 58676663 := bstep (se 1 (by rfl) ⟨44007497, by rfl⟩ : syracuseStep 58676663 = 88014995) B88014995
theorem B39117775 : Blo 2085435 39117775 := bstep (se 1 (by rfl) ⟨29338331, by rfl⟩ : syracuseStep 39117775 = 58676663) B58676663
theorem B52157033 : Blo 2085435 52157033 := bstep (se 2 (by rfl) ⟨19558887, by rfl⟩ : syracuseStep 52157033 = 39117775) B39117775
theorem B34771355 : Blo 2085435 34771355 := bstep (se 1 (by rfl) ⟨26078516, by rfl⟩ : syracuseStep 34771355 = 52157033) B52157033
theorem B23180903 : Blo 2085435 23180903 := bstep (se 1 (by rfl) ⟨17385677, by rfl⟩ : syracuseStep 23180903 = 34771355) B34771355
theorem B15453935 : Blo 2085435 15453935 := bstep (se 1 (by rfl) ⟨11590451, by rfl⟩ : syracuseStep 15453935 = 23180903) B23180903
theorem B10302623 : Blo 2085435 10302623 := bstep (se 1 (by rfl) ⟨7726967, by rfl⟩ : syracuseStep 10302623 = 15453935) B15453935
theorem B6868415 : Blo 2085435 6868415 := bstep (se 1 (by rfl) ⟨5151311, by rfl⟩ : syracuseStep 6868415 = 10302623) B10302623
theorem B18315773 : Blo 2085435 18315773 := bstep (se 3 (by rfl) ⟨3434207, by rfl⟩ : syracuseStep 18315773 = 6868415) B6868415
theorem B12210515 : Blo 2085435 12210515 := bstep (se 1 (by rfl) ⟨9157886, by rfl⟩ : syracuseStep 12210515 = 18315773) B18315773
theorem B8140343 : Blo 2085435 8140343 := bstep (se 1 (by rfl) ⟨6105257, by rfl⟩ : syracuseStep 8140343 = 12210515) B12210515
theorem B86830325 : Blo 2085435 86830325 := bstep (se 5 (by rfl) ⟨4070171, by rfl⟩ : syracuseStep 86830325 = 8140343) B8140343
theorem B57886883 : Blo 2085435 57886883 := bstep (se 1 (by rfl) ⟨43415162, by rfl⟩ : syracuseStep 57886883 = 86830325) B86830325
theorem B38591255 : Blo 2085435 38591255 := bstep (se 1 (by rfl) ⟨28943441, by rfl⟩ : syracuseStep 38591255 = 57886883) B57886883
theorem B25727503 : Blo 2085435 25727503 := bstep (se 1 (by rfl) ⟨19295627, by rfl⟩ : syracuseStep 25727503 = 38591255) B38591255
theorem B34303337 : Blo 2085435 34303337 := bstep (se 2 (by rfl) ⟨12863751, by rfl⟩ : syracuseStep 34303337 = 25727503) B25727503
theorem B22868891 : Blo 2085435 22868891 := bstep (se 1 (by rfl) ⟨17151668, by rfl⟩ : syracuseStep 22868891 = 34303337) B34303337
theorem B15245927 : Blo 2085435 15245927 := bstep (se 1 (by rfl) ⟨11434445, by rfl⟩ : syracuseStep 15245927 = 22868891) B22868891
theorem B10163951 : Blo 2085435 10163951 := bstep (se 1 (by rfl) ⟨7622963, by rfl⟩ : syracuseStep 10163951 = 15245927) B15245927
theorem B6775967 : Blo 2085435 6775967 := bstep (se 1 (by rfl) ⟨5081975, by rfl⟩ : syracuseStep 6775967 = 10163951) B10163951
theorem B18069245 : Blo 2085435 18069245 := bstep (se 3 (by rfl) ⟨3387983, by rfl⟩ : syracuseStep 18069245 = 6775967) B6775967
theorem B12046163 : Blo 2085435 12046163 := bstep (se 1 (by rfl) ⟨9034622, by rfl⟩ : syracuseStep 12046163 = 18069245) B18069245
theorem B32123101 : Blo 2085435 32123101 := bstep (se 3 (by rfl) ⟨6023081, by rfl⟩ : syracuseStep 32123101 = 12046163) B12046163
theorem B42830801 : Blo 2085435 42830801 := bstep (se 2 (by rfl) ⟨16061550, by rfl⟩ : syracuseStep 42830801 = 32123101) B32123101
theorem B28553867 : Blo 2085435 28553867 := bstep (se 1 (by rfl) ⟨21415400, by rfl⟩ : syracuseStep 28553867 = 42830801) B42830801
theorem B19035911 : Blo 2085435 19035911 := bstep (se 1 (by rfl) ⟨14276933, by rfl⟩ : syracuseStep 19035911 = 28553867) B28553867
theorem B12690607 : Blo 2085435 12690607 := bstep (se 1 (by rfl) ⟨9517955, by rfl⟩ : syracuseStep 12690607 = 19035911) B19035911
theorem B16920809 : Blo 2085435 16920809 := bstep (se 2 (by rfl) ⟨6345303, by rfl⟩ : syracuseStep 16920809 = 12690607) B12690607
theorem B11280539 : Blo 2085435 11280539 := bstep (se 1 (by rfl) ⟨8460404, by rfl⟩ : syracuseStep 11280539 = 16920809) B16920809
theorem B7520359 : Blo 2085435 7520359 := bstep (se 1 (by rfl) ⟨5640269, by rfl⟩ : syracuseStep 7520359 = 11280539) B11280539
theorem B10027145 : Blo 2085435 10027145 := bstep (se 2 (by rfl) ⟨3760179, by rfl⟩ : syracuseStep 10027145 = 7520359) B7520359
theorem B6684763 : Blo 2085435 6684763 := bstep (se 1 (by rfl) ⟨5013572, by rfl⟩ : syracuseStep 6684763 = 10027145) B10027145
theorem B8913017 : Blo 2085435 8913017 := bstep (se 2 (by rfl) ⟨3342381, by rfl⟩ : syracuseStep 8913017 = 6684763) B6684763
theorem B5942011 : Blo 2085435 5942011 := bstep (se 1 (by rfl) ⟨4456508, by rfl⟩ : syracuseStep 5942011 = 8913017) B8913017
theorem B7922681 : Blo 2085435 7922681 := bstep (se 2 (by rfl) ⟨2971005, by rfl⟩ : syracuseStep 7922681 = 5942011) B5942011
theorem B5281787 : Blo 2085435 5281787 := bstep (se 1 (by rfl) ⟨3961340, by rfl⟩ : syracuseStep 5281787 = 7922681) B7922681
theorem B3521191 : Blo 2085435 3521191 := bstep (se 1 (by rfl) ⟨2640893, by rfl⟩ : syracuseStep 3521191 = 5281787) B5281787
theorem B4694921 : Blo 2085435 4694921 := bstep (se 2 (by rfl) ⟨1760595, by rfl⟩ : syracuseStep 4694921 = 3521191) B3521191
theorem B3129947 : Blo 2085435 3129947 := bstep (se 1 (by rfl) ⟨2347460, by rfl⟩ : syracuseStep 3129947 = 4694921) B4694921
theorem B2086631 : Blo 2085435 2086631 := bstep (se 1 (by rfl) ⟨1564973, by rfl⟩ : syracuseStep 2086631 = 3129947) B3129947
theorem B2347465 : Blo 2085435 2347465 := bbase (se 2 (by rfl) ⟨880299, by rfl⟩ : syracuseStep 2347465 = 1760599) (by norm_num)
theorem B3129953 : Blo 2085435 3129953 := bstep (se 2 (by rfl) ⟨1173732, by rfl⟩ : syracuseStep 3129953 = 2347465) B2347465
theorem B2086635 : Blo 2085435 2086635 := bstep (se 1 (by rfl) ⟨1564976, by rfl⟩ : syracuseStep 2086635 = 3129953) B3129953
theorem B17826101 : Blo 2085435 17826101 := bbase (se 5 (by rfl) ⟨835598, by rfl⟩ : syracuseStep 17826101 = 1671197) (by norm_num)
theorem B11884067 : Blo 2085435 11884067 := bstep (se 1 (by rfl) ⟨8913050, by rfl⟩ : syracuseStep 11884067 = 17826101) B17826101
theorem B7922711 : Blo 2085435 7922711 := bstep (se 1 (by rfl) ⟨5942033, by rfl⟩ : syracuseStep 7922711 = 11884067) B11884067
theorem B5281807 : Blo 2085435 5281807 := bstep (se 1 (by rfl) ⟨3961355, by rfl⟩ : syracuseStep 5281807 = 7922711) B7922711
theorem B7042409 : Blo 2085435 7042409 := bstep (se 2 (by rfl) ⟨2640903, by rfl⟩ : syracuseStep 7042409 = 5281807) B5281807
theorem B4694939 : Blo 2085435 4694939 := bstep (se 1 (by rfl) ⟨3521204, by rfl⟩ : syracuseStep 4694939 = 7042409) B7042409
theorem B3129959 : Blo 2085435 3129959 := bstep (se 1 (by rfl) ⟨2347469, by rfl⟩ : syracuseStep 3129959 = 4694939) B4694939
theorem B2086639 : Blo 2085435 2086639 := bstep (se 1 (by rfl) ⟨1564979, by rfl⟩ : syracuseStep 2086639 = 3129959) B3129959
theorem B3129965 : Blo 2085435 3129965 := bbase (se 3 (by rfl) ⟨586868, by rfl⟩ : syracuseStep 3129965 = 1173737) (by norm_num)
theorem B2086643 : Blo 2085435 2086643 := bstep (se 1 (by rfl) ⟨1564982, by rfl⟩ : syracuseStep 2086643 = 3129965) B3129965
theorem B4694957 : Blo 2085435 4694957 := bbase (se 3 (by rfl) ⟨880304, by rfl⟩ : syracuseStep 4694957 = 1760609) (by norm_num)
theorem B3129971 : Blo 2085435 3129971 := bstep (se 1 (by rfl) ⟨2347478, by rfl⟩ : syracuseStep 3129971 = 4694957) B4694957
theorem B2086647 : Blo 2085435 2086647 := bstep (se 1 (by rfl) ⟨1564985, by rfl⟩ : syracuseStep 2086647 = 3129971) B3129971
theorem B5942069 : Blo 2085435 5942069 := bbase (se 5 (by rfl) ⟨278534, by rfl⟩ : syracuseStep 5942069 = 557069) (by norm_num)
theorem B3961379 : Blo 2085435 3961379 := bstep (se 1 (by rfl) ⟨2971034, by rfl⟩ : syracuseStep 3961379 = 5942069) B5942069
theorem B2640919 : Blo 2085435 2640919 := bstep (se 1 (by rfl) ⟨1980689, by rfl⟩ : syracuseStep 2640919 = 3961379) B3961379
theorem B3521225 : Blo 2085435 3521225 := bstep (se 2 (by rfl) ⟨1320459, by rfl⟩ : syracuseStep 3521225 = 2640919) B2640919
theorem B2347483 : Blo 2085435 2347483 := bstep (se 1 (by rfl) ⟨1760612, by rfl⟩ : syracuseStep 2347483 = 3521225) B3521225
theorem B3129977 : Blo 2085435 3129977 := bstep (se 2 (by rfl) ⟨1173741, by rfl⟩ : syracuseStep 3129977 = 2347483) B2347483
theorem B2086651 : Blo 2085435 2086651 := bstep (se 1 (by rfl) ⟨1564988, by rfl⟩ : syracuseStep 2086651 = 3129977) B3129977
theorem B51455573 : Blo 2085435 51455573 := bbase (se 8 (by rfl) ⟨301497, by rfl⟩ : syracuseStep 51455573 = 602995) (by norm_num)
theorem B34303715 : Blo 2085435 34303715 := bstep (se 1 (by rfl) ⟨25727786, by rfl⟩ : syracuseStep 34303715 = 51455573) B51455573
theorem B22869143 : Blo 2085435 22869143 := bstep (se 1 (by rfl) ⟨17151857, by rfl⟩ : syracuseStep 22869143 = 34303715) B34303715
theorem B15246095 : Blo 2085435 15246095 := bstep (se 1 (by rfl) ⟨11434571, by rfl⟩ : syracuseStep 15246095 = 22869143) B22869143
theorem B162625013 : Blo 2085435 162625013 := bstep (se 5 (by rfl) ⟨7623047, by rfl⟩ : syracuseStep 162625013 = 15246095) B15246095
theorem B108416675 : Blo 2085435 108416675 := bstep (se 1 (by rfl) ⟨81312506, by rfl⟩ : syracuseStep 108416675 = 162625013) B162625013
theorem B289111133 : Blo 2085435 289111133 := bstep (se 3 (by rfl) ⟨54208337, by rfl⟩ : syracuseStep 289111133 = 108416675) B108416675
theorem B192740755 : Blo 2085435 192740755 := bstep (se 1 (by rfl) ⟨144555566, by rfl⟩ : syracuseStep 192740755 = 289111133) B289111133
theorem B256987673 : Blo 2085435 256987673 := bstep (se 2 (by rfl) ⟨96370377, by rfl⟩ : syracuseStep 256987673 = 192740755) B192740755
theorem B171325115 : Blo 2085435 171325115 := bstep (se 1 (by rfl) ⟨128493836, by rfl⟩ : syracuseStep 171325115 = 256987673) B256987673
theorem B114216743 : Blo 2085435 114216743 := bstep (se 1 (by rfl) ⟨85662557, by rfl⟩ : syracuseStep 114216743 = 171325115) B171325115
theorem B76144495 : Blo 2085435 76144495 := bstep (se 1 (by rfl) ⟨57108371, by rfl⟩ : syracuseStep 76144495 = 114216743) B114216743
theorem B101525993 : Blo 2085435 101525993 := bstep (se 2 (by rfl) ⟨38072247, by rfl⟩ : syracuseStep 101525993 = 76144495) B76144495
theorem B67683995 : Blo 2085435 67683995 := bstep (se 1 (by rfl) ⟨50762996, by rfl⟩ : syracuseStep 67683995 = 101525993) B101525993
theorem B45122663 : Blo 2085435 45122663 := bstep (se 1 (by rfl) ⟨33841997, by rfl⟩ : syracuseStep 45122663 = 67683995) B67683995
theorem B30081775 : Blo 2085435 30081775 := bstep (se 1 (by rfl) ⟨22561331, by rfl⟩ : syracuseStep 30081775 = 45122663) B45122663
theorem B40109033 : Blo 2085435 40109033 := bstep (se 2 (by rfl) ⟨15040887, by rfl⟩ : syracuseStep 40109033 = 30081775) B30081775
theorem B26739355 : Blo 2085435 26739355 := bstep (se 1 (by rfl) ⟨20054516, by rfl⟩ : syracuseStep 26739355 = 40109033) B40109033
theorem B35652473 : Blo 2085435 35652473 := bstep (se 2 (by rfl) ⟨13369677, by rfl⟩ : syracuseStep 35652473 = 26739355) B26739355
theorem B23768315 : Blo 2085435 23768315 := bstep (se 1 (by rfl) ⟨17826236, by rfl⟩ : syracuseStep 23768315 = 35652473) B35652473
theorem B15845543 : Blo 2085435 15845543 := bstep (se 1 (by rfl) ⟨11884157, by rfl⟩ : syracuseStep 15845543 = 23768315) B23768315
theorem B10563695 : Blo 2085435 10563695 := bstep (se 1 (by rfl) ⟨7922771, by rfl⟩ : syracuseStep 10563695 = 15845543) B15845543
theorem B7042463 : Blo 2085435 7042463 := bstep (se 1 (by rfl) ⟨5281847, by rfl⟩ : syracuseStep 7042463 = 10563695) B10563695
theorem B4694975 : Blo 2085435 4694975 := bstep (se 1 (by rfl) ⟨3521231, by rfl⟩ : syracuseStep 4694975 = 7042463) B7042463
theorem B3129983 : Blo 2085435 3129983 := bstep (se 1 (by rfl) ⟨2347487, by rfl⟩ : syracuseStep 3129983 = 4694975) B4694975
theorem B2086655 : Blo 2085435 2086655 := bstep (se 1 (by rfl) ⟨1564991, by rfl⟩ : syracuseStep 2086655 = 3129983) B3129983
theorem B3129989 : Blo 2085435 3129989 := bbase (se 4 (by rfl) ⟨293436, by rfl⟩ : syracuseStep 3129989 = 586873) (by norm_num)
theorem B2086659 : Blo 2085435 2086659 := bstep (se 1 (by rfl) ⟨1564994, by rfl⟩ : syracuseStep 2086659 = 3129989) B3129989
theorem B3521245 : Blo 2085435 3521245 := bbase (se 3 (by rfl) ⟨660233, by rfl⟩ : syracuseStep 3521245 = 1320467) (by norm_num)
theorem B4694993 : Blo 2085435 4694993 := bstep (se 2 (by rfl) ⟨1760622, by rfl⟩ : syracuseStep 4694993 = 3521245) B3521245
theorem B3129995 : Blo 2085435 3129995 := bstep (se 1 (by rfl) ⟨2347496, by rfl⟩ : syracuseStep 3129995 = 4694993) B4694993
theorem B2086663 : Blo 2085435 2086663 := bstep (se 1 (by rfl) ⟨1564997, by rfl⟩ : syracuseStep 2086663 = 3129995) B3129995
theorem B2347501 : Blo 2085435 2347501 := bbase (se 3 (by rfl) ⟨440156, by rfl⟩ : syracuseStep 2347501 = 880313) (by norm_num)
theorem B3130001 : Blo 2085435 3130001 := bstep (se 2 (by rfl) ⟨1173750, by rfl⟩ : syracuseStep 3130001 = 2347501) B2347501
theorem B2086667 : Blo 2085435 2086667 := bstep (se 1 (by rfl) ⟨1565000, by rfl⟩ : syracuseStep 2086667 = 3130001) B3130001
theorem B7042517 : Blo 2085435 7042517 := bbase (se 7 (by rfl) ⟨82529, by rfl⟩ : syracuseStep 7042517 = 165059) (by norm_num)
theorem B4695011 : Blo 2085435 4695011 := bstep (se 1 (by rfl) ⟨3521258, by rfl⟩ : syracuseStep 4695011 = 7042517) B7042517
theorem B3130007 : Blo 2085435 3130007 := bstep (se 1 (by rfl) ⟨2347505, by rfl⟩ : syracuseStep 3130007 = 4695011) B4695011
theorem B2086671 : Blo 2085435 2086671 := bstep (se 1 (by rfl) ⟨1565003, by rfl⟩ : syracuseStep 2086671 = 3130007) B3130007
theorem B3130013 : Blo 2085435 3130013 := bbase (se 3 (by rfl) ⟨586877, by rfl⟩ : syracuseStep 3130013 = 1173755) (by norm_num)
theorem B2086675 : Blo 2085435 2086675 := bstep (se 1 (by rfl) ⟨1565006, by rfl⟩ : syracuseStep 2086675 = 3130013) B3130013
theorem B4695029 : Blo 2085435 4695029 := bbase (se 5 (by rfl) ⟨220079, by rfl⟩ : syracuseStep 4695029 = 440159) (by norm_num)
theorem B3130019 : Blo 2085435 3130019 := bstep (se 1 (by rfl) ⟨2347514, by rfl⟩ : syracuseStep 3130019 = 4695029) B4695029
theorem B2086679 : Blo 2085435 2086679 := bstep (se 1 (by rfl) ⟨1565009, by rfl⟩ : syracuseStep 2086679 = 3130019) B3130019
theorem B6345461 : Blo 2085435 6345461 := bbase (se 5 (by rfl) ⟨297443, by rfl⟩ : syracuseStep 6345461 = 594887) (by norm_num)
theorem B16921229 : Blo 2085435 16921229 := bstep (se 3 (by rfl) ⟨3172730, by rfl⟩ : syracuseStep 16921229 = 6345461) B6345461
theorem B45123277 : Blo 2085435 45123277 := bstep (se 3 (by rfl) ⟨8460614, by rfl⟩ : syracuseStep 45123277 = 16921229) B16921229
theorem B60164369 : Blo 2085435 60164369 := bstep (se 2 (by rfl) ⟨22561638, by rfl⟩ : syracuseStep 60164369 = 45123277) B45123277
theorem B40109579 : Blo 2085435 40109579 := bstep (se 1 (by rfl) ⟨30082184, by rfl⟩ : syracuseStep 40109579 = 60164369) B60164369
theorem B26739719 : Blo 2085435 26739719 := bstep (se 1 (by rfl) ⟨20054789, by rfl⟩ : syracuseStep 26739719 = 40109579) B40109579
theorem B17826479 : Blo 2085435 17826479 := bstep (se 1 (by rfl) ⟨13369859, by rfl⟩ : syracuseStep 17826479 = 26739719) B26739719
theorem B11884319 : Blo 2085435 11884319 := bstep (se 1 (by rfl) ⟨8913239, by rfl⟩ : syracuseStep 11884319 = 17826479) B17826479
theorem B7922879 : Blo 2085435 7922879 := bstep (se 1 (by rfl) ⟨5942159, by rfl⟩ : syracuseStep 7922879 = 11884319) B11884319
theorem B5281919 : Blo 2085435 5281919 := bstep (se 1 (by rfl) ⟨3961439, by rfl⟩ : syracuseStep 5281919 = 7922879) B7922879
theorem B3521279 : Blo 2085435 3521279 := bstep (se 1 (by rfl) ⟨2640959, by rfl⟩ : syracuseStep 3521279 = 5281919) B5281919
theorem B2347519 : Blo 2085435 2347519 := bstep (se 1 (by rfl) ⟨1760639, by rfl⟩ : syracuseStep 2347519 = 3521279) B3521279
theorem B3130025 : Blo 2085435 3130025 := bstep (se 2 (by rfl) ⟨1173759, by rfl⟩ : syracuseStep 3130025 = 2347519) B2347519
theorem B2086683 : Blo 2085435 2086683 := bstep (se 1 (by rfl) ⟨1565012, by rfl⟩ : syracuseStep 2086683 = 3130025) B3130025
theorem B2971085 : Blo 2085435 2971085 := bbase (se 3 (by rfl) ⟨557078, by rfl⟩ : syracuseStep 2971085 = 1114157) (by norm_num)
theorem B7922893 : Blo 2085435 7922893 := bstep (se 3 (by rfl) ⟨1485542, by rfl⟩ : syracuseStep 7922893 = 2971085) B2971085
theorem B10563857 : Blo 2085435 10563857 := bstep (se 2 (by rfl) ⟨3961446, by rfl⟩ : syracuseStep 10563857 = 7922893) B7922893
theorem B7042571 : Blo 2085435 7042571 := bstep (se 1 (by rfl) ⟨5281928, by rfl⟩ : syracuseStep 7042571 = 10563857) B10563857
theorem B4695047 : Blo 2085435 4695047 := bstep (se 1 (by rfl) ⟨3521285, by rfl⟩ : syracuseStep 4695047 = 7042571) B7042571
theorem B3130031 : Blo 2085435 3130031 := bstep (se 1 (by rfl) ⟨2347523, by rfl⟩ : syracuseStep 3130031 = 4695047) B4695047
theorem B2086687 : Blo 2085435 2086687 := bstep (se 1 (by rfl) ⟨1565015, by rfl⟩ : syracuseStep 2086687 = 3130031) B3130031
theorem B3130037 : Blo 2085435 3130037 := bbase (se 5 (by rfl) ⟨146720, by rfl⟩ : syracuseStep 3130037 = 293441) (by norm_num)
theorem B2086691 : Blo 2085435 2086691 := bstep (se 1 (by rfl) ⟨1565018, by rfl⟩ : syracuseStep 2086691 = 3130037) B3130037
theorem B5281949 : Blo 2085435 5281949 := bbase (se 3 (by rfl) ⟨990365, by rfl⟩ : syracuseStep 5281949 = 1980731) (by norm_num)
theorem B3521299 : Blo 2085435 3521299 := bstep (se 1 (by rfl) ⟨2640974, by rfl⟩ : syracuseStep 3521299 = 5281949) B5281949
theorem B4695065 : Blo 2085435 4695065 := bstep (se 2 (by rfl) ⟨1760649, by rfl⟩ : syracuseStep 4695065 = 3521299) B3521299
theorem B3130043 : Blo 2085435 3130043 := bstep (se 1 (by rfl) ⟨2347532, by rfl⟩ : syracuseStep 3130043 = 4695065) B4695065
theorem B2086695 : Blo 2085435 2086695 := bstep (se 1 (by rfl) ⟨1565021, by rfl⟩ : syracuseStep 2086695 = 3130043) B3130043
theorem B2347537 : Blo 2085435 2347537 := bbase (se 2 (by rfl) ⟨880326, by rfl⟩ : syracuseStep 2347537 = 1760653) (by norm_num)
theorem B3130049 : Blo 2085435 3130049 := bstep (se 2 (by rfl) ⟨1173768, by rfl⟩ : syracuseStep 3130049 = 2347537) B2347537
theorem B2086699 : Blo 2085435 2086699 := bstep (se 1 (by rfl) ⟨1565024, by rfl⟩ : syracuseStep 2086699 = 3130049) B3130049
theorem B3961477 : Blo 2085435 3961477 := bbase (se 4 (by rfl) ⟨371388, by rfl⟩ : syracuseStep 3961477 = 742777) (by norm_num)
theorem B5281969 : Blo 2085435 5281969 := bstep (se 2 (by rfl) ⟨1980738, by rfl⟩ : syracuseStep 5281969 = 3961477) B3961477
theorem B7042625 : Blo 2085435 7042625 := bstep (se 2 (by rfl) ⟨2640984, by rfl⟩ : syracuseStep 7042625 = 5281969) B5281969
theorem B4695083 : Blo 2085435 4695083 := bstep (se 1 (by rfl) ⟨3521312, by rfl⟩ : syracuseStep 4695083 = 7042625) B7042625
theorem B3130055 : Blo 2085435 3130055 := bstep (se 1 (by rfl) ⟨2347541, by rfl⟩ : syracuseStep 3130055 = 4695083) B4695083
theorem B2086703 : Blo 2085435 2086703 := bstep (se 1 (by rfl) ⟨1565027, by rfl⟩ : syracuseStep 2086703 = 3130055) B3130055
theorem B3130061 : Blo 2085435 3130061 := bbase (se 3 (by rfl) ⟨586886, by rfl⟩ : syracuseStep 3130061 = 1173773) (by norm_num)
theorem B2086707 : Blo 2085435 2086707 := bstep (se 1 (by rfl) ⟨1565030, by rfl⟩ : syracuseStep 2086707 = 3130061) B3130061
theorem B4695101 : Blo 2085435 4695101 := bbase (se 3 (by rfl) ⟨880331, by rfl⟩ : syracuseStep 4695101 = 1760663) (by norm_num)
theorem B3130067 : Blo 2085435 3130067 := bstep (se 1 (by rfl) ⟨2347550, by rfl⟩ : syracuseStep 3130067 = 4695101) B4695101
theorem B2086711 : Blo 2085435 2086711 := bstep (se 1 (by rfl) ⟨1565033, by rfl⟩ : syracuseStep 2086711 = 3130067) B3130067
theorem B3521333 : Blo 2085435 3521333 := bbase (se 5 (by rfl) ⟨165062, by rfl⟩ : syracuseStep 3521333 = 330125) (by norm_num)
theorem B2347555 : Blo 2085435 2347555 := bstep (se 1 (by rfl) ⟨1760666, by rfl⟩ : syracuseStep 2347555 = 3521333) B3521333
theorem B3130073 : Blo 2085435 3130073 := bstep (se 2 (by rfl) ⟨1173777, by rfl⟩ : syracuseStep 3130073 = 2347555) B2347555
theorem B2086715 : Blo 2085435 2086715 := bstep (se 1 (by rfl) ⟨1565036, by rfl⟩ : syracuseStep 2086715 = 3130073) B3130073
theorem B5942261 : Blo 2085435 5942261 := bbase (se 5 (by rfl) ⟨278543, by rfl⟩ : syracuseStep 5942261 = 557087) (by norm_num)
theorem B15846029 : Blo 2085435 15846029 := bstep (se 3 (by rfl) ⟨2971130, by rfl⟩ : syracuseStep 15846029 = 5942261) B5942261
theorem B10564019 : Blo 2085435 10564019 := bstep (se 1 (by rfl) ⟨7923014, by rfl⟩ : syracuseStep 10564019 = 15846029) B15846029
theorem B7042679 : Blo 2085435 7042679 := bstep (se 1 (by rfl) ⟨5282009, by rfl⟩ : syracuseStep 7042679 = 10564019) B10564019
theorem B4695119 : Blo 2085435 4695119 := bstep (se 1 (by rfl) ⟨3521339, by rfl⟩ : syracuseStep 4695119 = 7042679) B7042679
theorem B3130079 : Blo 2085435 3130079 := bstep (se 1 (by rfl) ⟨2347559, by rfl⟩ : syracuseStep 3130079 = 4695119) B4695119
theorem B2086719 : Blo 2085435 2086719 := bstep (se 1 (by rfl) ⟨1565039, by rfl⟩ : syracuseStep 2086719 = 3130079) B3130079
theorem B3130085 : Blo 2085435 3130085 := bbase (se 4 (by rfl) ⟨293445, by rfl⟩ : syracuseStep 3130085 = 586891) (by norm_num)
theorem B2086723 : Blo 2085435 2086723 := bstep (se 1 (by rfl) ⟨1565042, by rfl⟩ : syracuseStep 2086723 = 3130085) B3130085
theorem B2228357 : Blo 2085435 2228357 := bbase (se 4 (by rfl) ⟨208908, by rfl⟩ : syracuseStep 2228357 = 417817) (by norm_num)
theorem B5942285 : Blo 2085435 5942285 := bstep (se 3 (by rfl) ⟨1114178, by rfl⟩ : syracuseStep 5942285 = 2228357) B2228357
theorem B3961523 : Blo 2085435 3961523 := bstep (se 1 (by rfl) ⟨2971142, by rfl⟩ : syracuseStep 3961523 = 5942285) B5942285
theorem B2641015 : Blo 2085435 2641015 := bstep (se 1 (by rfl) ⟨1980761, by rfl⟩ : syracuseStep 2641015 = 3961523) B3961523
theorem B3521353 : Blo 2085435 3521353 := bstep (se 2 (by rfl) ⟨1320507, by rfl⟩ : syracuseStep 3521353 = 2641015) B2641015
theorem B4695137 : Blo 2085435 4695137 := bstep (se 2 (by rfl) ⟨1760676, by rfl⟩ : syracuseStep 4695137 = 3521353) B3521353
theorem B3130091 : Blo 2085435 3130091 := bstep (se 1 (by rfl) ⟨2347568, by rfl⟩ : syracuseStep 3130091 = 4695137) B4695137
theorem B2086727 : Blo 2085435 2086727 := bstep (se 1 (by rfl) ⟨1565045, by rfl⟩ : syracuseStep 2086727 = 3130091) B3130091
theorem B2347573 : Blo 2085435 2347573 := bbase (se 5 (by rfl) ⟨110042, by rfl⟩ : syracuseStep 2347573 = 220085) (by norm_num)
theorem B3130097 : Blo 2085435 3130097 := bstep (se 2 (by rfl) ⟨1173786, by rfl⟩ : syracuseStep 3130097 = 2347573) B2347573
theorem B2086731 : Blo 2085435 2086731 := bstep (se 1 (by rfl) ⟨1565048, by rfl⟩ : syracuseStep 2086731 = 3130097) B3130097
theorem B2641025 : Blo 2085435 2641025 := bbase (se 2 (by rfl) ⟨990384, by rfl⟩ : syracuseStep 2641025 = 1980769) (by norm_num)
theorem B7042733 : Blo 2085435 7042733 := bstep (se 3 (by rfl) ⟨1320512, by rfl⟩ : syracuseStep 7042733 = 2641025) B2641025
theorem B4695155 : Blo 2085435 4695155 := bstep (se 1 (by rfl) ⟨3521366, by rfl⟩ : syracuseStep 4695155 = 7042733) B7042733
theorem B3130103 : Blo 2085435 3130103 := bstep (se 1 (by rfl) ⟨2347577, by rfl⟩ : syracuseStep 3130103 = 4695155) B4695155
theorem B2086735 : Blo 2085435 2086735 := bstep (se 1 (by rfl) ⟨1565051, by rfl⟩ : syracuseStep 2086735 = 3130103) B3130103
theorem B3130109 : Blo 2085435 3130109 := bbase (se 3 (by rfl) ⟨586895, by rfl⟩ : syracuseStep 3130109 = 1173791) (by norm_num)
theorem B2086739 : Blo 2085435 2086739 := bstep (se 1 (by rfl) ⟨1565054, by rfl⟩ : syracuseStep 2086739 = 3130109) B3130109
theorem B4695173 : Blo 2085435 4695173 := bbase (se 4 (by rfl) ⟨440172, by rfl⟩ : syracuseStep 4695173 = 880345) (by norm_num)
theorem B3130115 : Blo 2085435 3130115 := bstep (se 1 (by rfl) ⟨2347586, by rfl⟩ : syracuseStep 3130115 = 4695173) B4695173
theorem B2086743 : Blo 2085435 2086743 := bstep (se 1 (by rfl) ⟨1565057, by rfl⟩ : syracuseStep 2086743 = 3130115) B3130115
theorem B4456757 : Blo 2085435 4456757 := bbase (se 5 (by rfl) ⟨208910, by rfl⟩ : syracuseStep 4456757 = 417821) (by norm_num)
theorem B2971171 : Blo 2085435 2971171 := bstep (se 1 (by rfl) ⟨2228378, by rfl⟩ : syracuseStep 2971171 = 4456757) B4456757
theorem B3961561 : Blo 2085435 3961561 := bstep (se 2 (by rfl) ⟨1485585, by rfl⟩ : syracuseStep 3961561 = 2971171) B2971171
theorem B5282081 : Blo 2085435 5282081 := bstep (se 2 (by rfl) ⟨1980780, by rfl⟩ : syracuseStep 5282081 = 3961561) B3961561
theorem B3521387 : Blo 2085435 3521387 := bstep (se 1 (by rfl) ⟨2641040, by rfl⟩ : syracuseStep 3521387 = 5282081) B5282081
theorem B2347591 : Blo 2085435 2347591 := bstep (se 1 (by rfl) ⟨1760693, by rfl⟩ : syracuseStep 2347591 = 3521387) B3521387
theorem B3130121 : Blo 2085435 3130121 := bstep (se 2 (by rfl) ⟨1173795, by rfl⟩ : syracuseStep 3130121 = 2347591) B2347591
theorem B2086747 : Blo 2085435 2086747 := bstep (se 1 (by rfl) ⟨1565060, by rfl⟩ : syracuseStep 2086747 = 3130121) B3130121
theorem B10564181 : Blo 2085435 10564181 := bbase (se 8 (by rfl) ⟨61899, by rfl⟩ : syracuseStep 10564181 = 123799) (by norm_num)
theorem B7042787 : Blo 2085435 7042787 := bstep (se 1 (by rfl) ⟨5282090, by rfl⟩ : syracuseStep 7042787 = 10564181) B10564181
theorem B4695191 : Blo 2085435 4695191 := bstep (se 1 (by rfl) ⟨3521393, by rfl⟩ : syracuseStep 4695191 = 7042787) B7042787
theorem B3130127 : Blo 2085435 3130127 := bstep (se 1 (by rfl) ⟨2347595, by rfl⟩ : syracuseStep 3130127 = 4695191) B4695191
theorem B2086751 : Blo 2085435 2086751 := bstep (se 1 (by rfl) ⟨1565063, by rfl⟩ : syracuseStep 2086751 = 3130127) B3130127
theorem B3130133 : Blo 2085435 3130133 := bbase (se 6 (by rfl) ⟨73362, by rfl⟩ : syracuseStep 3130133 = 146725) (by norm_num)
theorem B2086755 : Blo 2085435 2086755 := bstep (se 1 (by rfl) ⟨1565066, by rfl⟩ : syracuseStep 2086755 = 3130133) B3130133
theorem B6188933 : Blo 2085435 6188933 := bbase (se 4 (by rfl) ⟨580212, by rfl⟩ : syracuseStep 6188933 = 1160425) (by norm_num)
theorem B16503821 : Blo 2085435 16503821 := bstep (se 3 (by rfl) ⟨3094466, by rfl⟩ : syracuseStep 16503821 = 6188933) B6188933
theorem B11002547 : Blo 2085435 11002547 := bstep (se 1 (by rfl) ⟨8251910, by rfl⟩ : syracuseStep 11002547 = 16503821) B16503821
theorem B7335031 : Blo 2085435 7335031 := bstep (se 1 (by rfl) ⟨5501273, by rfl⟩ : syracuseStep 7335031 = 11002547) B11002547
theorem B9780041 : Blo 2085435 9780041 := bstep (se 2 (by rfl) ⟨3667515, by rfl⟩ : syracuseStep 9780041 = 7335031) B7335031
theorem B6520027 : Blo 2085435 6520027 := bstep (se 1 (by rfl) ⟨4890020, by rfl⟩ : syracuseStep 6520027 = 9780041) B9780041
theorem B8693369 : Blo 2085435 8693369 := bstep (se 2 (by rfl) ⟨3260013, by rfl⟩ : syracuseStep 8693369 = 6520027) B6520027
theorem B5795579 : Blo 2085435 5795579 := bstep (se 1 (by rfl) ⟨4346684, by rfl⟩ : syracuseStep 5795579 = 8693369) B8693369
theorem B3863719 : Blo 2085435 3863719 := bstep (se 1 (by rfl) ⟨2897789, by rfl⟩ : syracuseStep 3863719 = 5795579) B5795579
theorem B20606501 : Blo 2085435 20606501 := bstep (se 4 (by rfl) ⟨1931859, by rfl⟩ : syracuseStep 20606501 = 3863719) B3863719
theorem B54950669 : Blo 2085435 54950669 := bstep (se 3 (by rfl) ⟨10303250, by rfl⟩ : syracuseStep 54950669 = 20606501) B20606501
theorem B36633779 : Blo 2085435 36633779 := bstep (se 1 (by rfl) ⟨27475334, by rfl⟩ : syracuseStep 36633779 = 54950669) B54950669
theorem B24422519 : Blo 2085435 24422519 := bstep (se 1 (by rfl) ⟨18316889, by rfl⟩ : syracuseStep 24422519 = 36633779) B36633779
theorem B65126717 : Blo 2085435 65126717 := bstep (se 3 (by rfl) ⟨12211259, by rfl⟩ : syracuseStep 65126717 = 24422519) B24422519
theorem B43417811 : Blo 2085435 43417811 := bstep (se 1 (by rfl) ⟨32563358, by rfl⟩ : syracuseStep 43417811 = 65126717) B65126717
theorem B28945207 : Blo 2085435 28945207 := bstep (se 1 (by rfl) ⟨21708905, by rfl⟩ : syracuseStep 28945207 = 43417811) B43417811
theorem B154374437 : Blo 2085435 154374437 := bstep (se 4 (by rfl) ⟨14472603, by rfl⟩ : syracuseStep 154374437 = 28945207) B28945207
theorem B102916291 : Blo 2085435 102916291 := bstep (se 1 (by rfl) ⟨77187218, by rfl⟩ : syracuseStep 102916291 = 154374437) B154374437
theorem B137221721 : Blo 2085435 137221721 := bstep (se 2 (by rfl) ⟨51458145, by rfl⟩ : syracuseStep 137221721 = 102916291) B102916291
theorem B91481147 : Blo 2085435 91481147 := bstep (se 1 (by rfl) ⟨68610860, by rfl⟩ : syracuseStep 91481147 = 137221721) B137221721
theorem B60987431 : Blo 2085435 60987431 := bstep (se 1 (by rfl) ⟨45740573, by rfl⟩ : syracuseStep 60987431 = 91481147) B91481147
theorem B40658287 : Blo 2085435 40658287 := bstep (se 1 (by rfl) ⟨30493715, by rfl⟩ : syracuseStep 40658287 = 60987431) B60987431
theorem B54211049 : Blo 2085435 54211049 := bstep (se 2 (by rfl) ⟨20329143, by rfl⟩ : syracuseStep 54211049 = 40658287) B40658287
theorem B36140699 : Blo 2085435 36140699 := bstep (se 1 (by rfl) ⟨27105524, by rfl⟩ : syracuseStep 36140699 = 54211049) B54211049
theorem B96375197 : Blo 2085435 96375197 := bstep (se 3 (by rfl) ⟨18070349, by rfl⟩ : syracuseStep 96375197 = 36140699) B36140699
theorem B64250131 : Blo 2085435 64250131 := bstep (se 1 (by rfl) ⟨48187598, by rfl⟩ : syracuseStep 64250131 = 96375197) B96375197
theorem B85666841 : Blo 2085435 85666841 := bstep (se 2 (by rfl) ⟨32125065, by rfl⟩ : syracuseStep 85666841 = 64250131) B64250131
theorem B57111227 : Blo 2085435 57111227 := bstep (se 1 (by rfl) ⟨42833420, by rfl⟩ : syracuseStep 57111227 = 85666841) B85666841
theorem B38074151 : Blo 2085435 38074151 := bstep (se 1 (by rfl) ⟨28555613, by rfl⟩ : syracuseStep 38074151 = 57111227) B57111227
theorem B25382767 : Blo 2085435 25382767 := bstep (se 1 (by rfl) ⟨19037075, by rfl⟩ : syracuseStep 25382767 = 38074151) B38074151
theorem B33843689 : Blo 2085435 33843689 := bstep (se 2 (by rfl) ⟨12691383, by rfl⟩ : syracuseStep 33843689 = 25382767) B25382767
theorem B22562459 : Blo 2085435 22562459 := bstep (se 1 (by rfl) ⟨16921844, by rfl⟩ : syracuseStep 22562459 = 33843689) B33843689
theorem B15041639 : Blo 2085435 15041639 := bstep (se 1 (by rfl) ⟨11281229, by rfl⟩ : syracuseStep 15041639 = 22562459) B22562459
theorem B40111037 : Blo 2085435 40111037 := bstep (se 3 (by rfl) ⟨7520819, by rfl⟩ : syracuseStep 40111037 = 15041639) B15041639
theorem B26740691 : Blo 2085435 26740691 := bstep (se 1 (by rfl) ⟨20055518, by rfl⟩ : syracuseStep 26740691 = 40111037) B40111037
theorem B17827127 : Blo 2085435 17827127 := bstep (se 1 (by rfl) ⟨13370345, by rfl⟩ : syracuseStep 17827127 = 26740691) B26740691
theorem B11884751 : Blo 2085435 11884751 := bstep (se 1 (by rfl) ⟨8913563, by rfl⟩ : syracuseStep 11884751 = 17827127) B17827127
theorem B7923167 : Blo 2085435 7923167 := bstep (se 1 (by rfl) ⟨5942375, by rfl⟩ : syracuseStep 7923167 = 11884751) B11884751
theorem B5282111 : Blo 2085435 5282111 := bstep (se 1 (by rfl) ⟨3961583, by rfl⟩ : syracuseStep 5282111 = 7923167) B7923167
theorem B3521407 : Blo 2085435 3521407 := bstep (se 1 (by rfl) ⟨2641055, by rfl⟩ : syracuseStep 3521407 = 5282111) B5282111
theorem B4695209 : Blo 2085435 4695209 := bstep (se 2 (by rfl) ⟨1760703, by rfl⟩ : syracuseStep 4695209 = 3521407) B3521407
theorem B3130139 : Blo 2085435 3130139 := bstep (se 1 (by rfl) ⟨2347604, by rfl⟩ : syracuseStep 3130139 = 4695209) B4695209
theorem B2086759 : Blo 2085435 2086759 := bstep (se 1 (by rfl) ⟨1565069, by rfl⟩ : syracuseStep 2086759 = 3130139) B3130139
theorem B2347609 : Blo 2085435 2347609 := bbase (se 2 (by rfl) ⟨880353, by rfl⟩ : syracuseStep 2347609 = 1760707) (by norm_num)
theorem B3130145 : Blo 2085435 3130145 := bstep (se 2 (by rfl) ⟨1173804, by rfl⟩ : syracuseStep 3130145 = 2347609) B2347609
theorem B2086763 : Blo 2085435 2086763 := bstep (se 1 (by rfl) ⟨1565072, by rfl⟩ : syracuseStep 2086763 = 3130145) B3130145
theorem B6023477 : Blo 2085435 6023477 := bbase (se 5 (by rfl) ⟨282350, by rfl⟩ : syracuseStep 6023477 = 564701) (by norm_num)
theorem B4015651 : Blo 2085435 4015651 := bstep (se 1 (by rfl) ⟨3011738, by rfl⟩ : syracuseStep 4015651 = 6023477) B6023477
theorem B5354201 : Blo 2085435 5354201 := bstep (se 2 (by rfl) ⟨2007825, by rfl⟩ : syracuseStep 5354201 = 4015651) B4015651
theorem B3569467 : Blo 2085435 3569467 := bstep (se 1 (by rfl) ⟨2677100, by rfl⟩ : syracuseStep 3569467 = 5354201) B5354201
theorem B4759289 : Blo 2085435 4759289 := bstep (se 2 (by rfl) ⟨1784733, by rfl⟩ : syracuseStep 4759289 = 3569467) B3569467
theorem B3172859 : Blo 2085435 3172859 := bstep (se 1 (by rfl) ⟨2379644, by rfl⟩ : syracuseStep 3172859 = 4759289) B4759289
theorem B2115239 : Blo 2085435 2115239 := bstep (se 1 (by rfl) ⟨1586429, by rfl⟩ : syracuseStep 2115239 = 3172859) B3172859
theorem B22562549 : Blo 2085435 22562549 := bstep (se 5 (by rfl) ⟨1057619, by rfl⟩ : syracuseStep 22562549 = 2115239) B2115239
theorem B15041699 : Blo 2085435 15041699 := bstep (se 1 (by rfl) ⟨11281274, by rfl⟩ : syracuseStep 15041699 = 22562549) B22562549
theorem B10027799 : Blo 2085435 10027799 := bstep (se 1 (by rfl) ⟨7520849, by rfl⟩ : syracuseStep 10027799 = 15041699) B15041699
theorem B6685199 : Blo 2085435 6685199 := bstep (se 1 (by rfl) ⟨5013899, by rfl⟩ : syracuseStep 6685199 = 10027799) B10027799
theorem B4456799 : Blo 2085435 4456799 := bstep (se 1 (by rfl) ⟨3342599, by rfl⟩ : syracuseStep 4456799 = 6685199) B6685199
theorem B2971199 : Blo 2085435 2971199 := bstep (se 1 (by rfl) ⟨2228399, by rfl⟩ : syracuseStep 2971199 = 4456799) B4456799
theorem B7923197 : Blo 2085435 7923197 := bstep (se 3 (by rfl) ⟨1485599, by rfl⟩ : syracuseStep 7923197 = 2971199) B2971199
theorem B5282131 : Blo 2085435 5282131 := bstep (se 1 (by rfl) ⟨3961598, by rfl⟩ : syracuseStep 5282131 = 7923197) B7923197
theorem B7042841 : Blo 2085435 7042841 := bstep (se 2 (by rfl) ⟨2641065, by rfl⟩ : syracuseStep 7042841 = 5282131) B5282131
theorem B4695227 : Blo 2085435 4695227 := bstep (se 1 (by rfl) ⟨3521420, by rfl⟩ : syracuseStep 4695227 = 7042841) B7042841
theorem B3130151 : Blo 2085435 3130151 := bstep (se 1 (by rfl) ⟨2347613, by rfl⟩ : syracuseStep 3130151 = 4695227) B4695227
theorem B2086767 : Blo 2085435 2086767 := bstep (se 1 (by rfl) ⟨1565075, by rfl⟩ : syracuseStep 2086767 = 3130151) B3130151
theorem B3130157 : Blo 2085435 3130157 := bbase (se 3 (by rfl) ⟨586904, by rfl⟩ : syracuseStep 3130157 = 1173809) (by norm_num)
theorem B2086771 : Blo 2085435 2086771 := bstep (se 1 (by rfl) ⟨1565078, by rfl⟩ : syracuseStep 2086771 = 3130157) B3130157
theorem B4695245 : Blo 2085435 4695245 := bbase (se 3 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 4695245 = 1760717) (by norm_num)
theorem B3130163 : Blo 2085435 3130163 := bstep (se 1 (by rfl) ⟨2347622, by rfl⟩ : syracuseStep 3130163 = 4695245) B4695245
theorem B2086775 : Blo 2085435 2086775 := bstep (se 1 (by rfl) ⟨1565081, by rfl⟩ : syracuseStep 2086775 = 3130163) B3130163
theorem B2641081 : Blo 2085435 2641081 := bbase (se 2 (by rfl) ⟨990405, by rfl⟩ : syracuseStep 2641081 = 1980811) (by norm_num)
theorem B3521441 : Blo 2085435 3521441 := bstep (se 2 (by rfl) ⟨1320540, by rfl⟩ : syracuseStep 3521441 = 2641081) B2641081
theorem B2347627 : Blo 2085435 2347627 := bstep (se 1 (by rfl) ⟨1760720, by rfl⟩ : syracuseStep 2347627 = 3521441) B3521441
theorem B3130169 : Blo 2085435 3130169 := bstep (se 2 (by rfl) ⟨1173813, by rfl⟩ : syracuseStep 3130169 = 2347627) B2347627
theorem B2086779 : Blo 2085435 2086779 := bstep (se 1 (by rfl) ⟨1565084, by rfl⟩ : syracuseStep 2086779 = 3130169) B3130169
theorem B3760453 : Blo 2085435 3760453 := bbase (se 4 (by rfl) ⟨352542, by rfl⟩ : syracuseStep 3760453 = 705085) (by norm_num)
theorem B5013937 : Blo 2085435 5013937 := bstep (se 2 (by rfl) ⟨1880226, by rfl⟩ : syracuseStep 5013937 = 3760453) B3760453
theorem B6685249 : Blo 2085435 6685249 := bstep (se 2 (by rfl) ⟨2506968, by rfl⟩ : syracuseStep 6685249 = 5013937) B5013937
theorem B8913665 : Blo 2085435 8913665 := bstep (se 2 (by rfl) ⟨3342624, by rfl⟩ : syracuseStep 8913665 = 6685249) B6685249
theorem B23769773 : Blo 2085435 23769773 := bstep (se 3 (by rfl) ⟨4456832, by rfl⟩ : syracuseStep 23769773 = 8913665) B8913665
theorem B15846515 : Blo 2085435 15846515 := bstep (se 1 (by rfl) ⟨11884886, by rfl⟩ : syracuseStep 15846515 = 23769773) B23769773
theorem B10564343 : Blo 2085435 10564343 := bstep (se 1 (by rfl) ⟨7923257, by rfl⟩ : syracuseStep 10564343 = 15846515) B15846515
theorem B7042895 : Blo 2085435 7042895 := bstep (se 1 (by rfl) ⟨5282171, by rfl⟩ : syracuseStep 7042895 = 10564343) B10564343
theorem B4695263 : Blo 2085435 4695263 := bstep (se 1 (by rfl) ⟨3521447, by rfl⟩ : syracuseStep 4695263 = 7042895) B7042895
theorem B3130175 : Blo 2085435 3130175 := bstep (se 1 (by rfl) ⟨2347631, by rfl⟩ : syracuseStep 3130175 = 4695263) B4695263
theorem B2086783 : Blo 2085435 2086783 := bstep (se 1 (by rfl) ⟨1565087, by rfl⟩ : syracuseStep 2086783 = 3130175) B3130175
theorem B3130181 : Blo 2085435 3130181 := bbase (se 4 (by rfl) ⟨293454, by rfl⟩ : syracuseStep 3130181 = 586909) (by norm_num)
theorem B2086787 : Blo 2085435 2086787 := bstep (se 1 (by rfl) ⟨1565090, by rfl⟩ : syracuseStep 2086787 = 3130181) B3130181
theorem B3521461 : Blo 2085435 3521461 := bbase (se 5 (by rfl) ⟨165068, by rfl⟩ : syracuseStep 3521461 = 330137) (by norm_num)
theorem B4695281 : Blo 2085435 4695281 := bstep (se 2 (by rfl) ⟨1760730, by rfl⟩ : syracuseStep 4695281 = 3521461) B3521461
theorem B3130187 : Blo 2085435 3130187 := bstep (se 1 (by rfl) ⟨2347640, by rfl⟩ : syracuseStep 3130187 = 4695281) B4695281
theorem B2086791 : Blo 2085435 2086791 := bstep (se 1 (by rfl) ⟨1565093, by rfl⟩ : syracuseStep 2086791 = 3130187) B3130187
theorem B2347645 : Blo 2085435 2347645 := bbase (se 3 (by rfl) ⟨440183, by rfl⟩ : syracuseStep 2347645 = 880367) (by norm_num)
theorem B3130193 : Blo 2085435 3130193 := bstep (se 2 (by rfl) ⟨1173822, by rfl⟩ : syracuseStep 3130193 = 2347645) B2347645
theorem B2086795 : Blo 2085435 2086795 := bstep (se 1 (by rfl) ⟨1565096, by rfl⟩ : syracuseStep 2086795 = 3130193) B3130193
theorem B7042949 : Blo 2085435 7042949 := bbase (se 4 (by rfl) ⟨660276, by rfl⟩ : syracuseStep 7042949 = 1320553) (by norm_num)
theorem B4695299 : Blo 2085435 4695299 := bstep (se 1 (by rfl) ⟨3521474, by rfl⟩ : syracuseStep 4695299 = 7042949) B7042949
theorem B3130199 : Blo 2085435 3130199 := bstep (se 1 (by rfl) ⟨2347649, by rfl⟩ : syracuseStep 3130199 = 4695299) B4695299
theorem B2086799 : Blo 2085435 2086799 := bstep (se 1 (by rfl) ⟨1565099, by rfl⟩ : syracuseStep 2086799 = 3130199) B3130199
theorem B3130205 : Blo 2085435 3130205 := bbase (se 3 (by rfl) ⟨586913, by rfl⟩ : syracuseStep 3130205 = 1173827) (by norm_num)
theorem B2086803 : Blo 2085435 2086803 := bstep (se 1 (by rfl) ⟨1565102, by rfl⟩ : syracuseStep 2086803 = 3130205) B3130205
theorem B4695317 : Blo 2085435 4695317 := bbase (se 6 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 4695317 = 220093) (by norm_num)
theorem B3130211 : Blo 2085435 3130211 := bstep (se 1 (by rfl) ⟨2347658, by rfl⟩ : syracuseStep 3130211 = 4695317) B4695317
theorem B2086807 : Blo 2085435 2086807 := bstep (se 1 (by rfl) ⟨1565105, by rfl⟩ : syracuseStep 2086807 = 3130211) B3130211
theorem B7923365 : Blo 2085435 7923365 := bbase (se 4 (by rfl) ⟨742815, by rfl⟩ : syracuseStep 7923365 = 1485631) (by norm_num)
theorem B5282243 : Blo 2085435 5282243 := bstep (se 1 (by rfl) ⟨3961682, by rfl⟩ : syracuseStep 5282243 = 7923365) B7923365
theorem B3521495 : Blo 2085435 3521495 := bstep (se 1 (by rfl) ⟨2641121, by rfl⟩ : syracuseStep 3521495 = 5282243) B5282243
theorem B2347663 : Blo 2085435 2347663 := bstep (se 1 (by rfl) ⟨1760747, by rfl⟩ : syracuseStep 2347663 = 3521495) B3521495
theorem B3130217 : Blo 2085435 3130217 := bstep (se 2 (by rfl) ⟨1173831, by rfl⟩ : syracuseStep 3130217 = 2347663) B2347663
theorem B2086811 : Blo 2085435 2086811 := bstep (se 1 (by rfl) ⟨1565108, by rfl⟩ : syracuseStep 2086811 = 3130217) B3130217
theorem B4456901 : Blo 2085435 4456901 := bbase (se 4 (by rfl) ⟨417834, by rfl⟩ : syracuseStep 4456901 = 835669) (by norm_num)
theorem B11885069 : Blo 2085435 11885069 := bstep (se 3 (by rfl) ⟨2228450, by rfl⟩ : syracuseStep 11885069 = 4456901) B4456901
theorem B7923379 : Blo 2085435 7923379 := bstep (se 1 (by rfl) ⟨5942534, by rfl⟩ : syracuseStep 7923379 = 11885069) B11885069
theorem B10564505 : Blo 2085435 10564505 := bstep (se 2 (by rfl) ⟨3961689, by rfl⟩ : syracuseStep 10564505 = 7923379) B7923379
theorem B7043003 : Blo 2085435 7043003 := bstep (se 1 (by rfl) ⟨5282252, by rfl⟩ : syracuseStep 7043003 = 10564505) B10564505
theorem B4695335 : Blo 2085435 4695335 := bstep (se 1 (by rfl) ⟨3521501, by rfl⟩ : syracuseStep 4695335 = 7043003) B7043003
theorem B3130223 : Blo 2085435 3130223 := bstep (se 1 (by rfl) ⟨2347667, by rfl⟩ : syracuseStep 3130223 = 4695335) B4695335
theorem B2086815 : Blo 2085435 2086815 := bstep (se 1 (by rfl) ⟨1565111, by rfl⟩ : syracuseStep 2086815 = 3130223) B3130223
theorem B3130229 : Blo 2085435 3130229 := bbase (se 5 (by rfl) ⟨146729, by rfl⟩ : syracuseStep 3130229 = 293459) (by norm_num)
theorem B2086819 : Blo 2085435 2086819 := bstep (se 1 (by rfl) ⟨1565114, by rfl⟩ : syracuseStep 2086819 = 3130229) B3130229
theorem B10028069 : Blo 2085435 10028069 := bbase (se 4 (by rfl) ⟨940131, by rfl⟩ : syracuseStep 10028069 = 1880263) (by norm_num)
theorem B6685379 : Blo 2085435 6685379 := bstep (se 1 (by rfl) ⟨5014034, by rfl⟩ : syracuseStep 6685379 = 10028069) B10028069
theorem B4456919 : Blo 2085435 4456919 := bstep (se 1 (by rfl) ⟨3342689, by rfl⟩ : syracuseStep 4456919 = 6685379) B6685379
theorem B2971279 : Blo 2085435 2971279 := bstep (se 1 (by rfl) ⟨2228459, by rfl⟩ : syracuseStep 2971279 = 4456919) B4456919
theorem B3961705 : Blo 2085435 3961705 := bstep (se 2 (by rfl) ⟨1485639, by rfl⟩ : syracuseStep 3961705 = 2971279) B2971279
theorem B5282273 : Blo 2085435 5282273 := bstep (se 2 (by rfl) ⟨1980852, by rfl⟩ : syracuseStep 5282273 = 3961705) B3961705
theorem B3521515 : Blo 2085435 3521515 := bstep (se 1 (by rfl) ⟨2641136, by rfl⟩ : syracuseStep 3521515 = 5282273) B5282273
theorem B4695353 : Blo 2085435 4695353 := bstep (se 2 (by rfl) ⟨1760757, by rfl⟩ : syracuseStep 4695353 = 3521515) B3521515
theorem B3130235 : Blo 2085435 3130235 := bstep (se 1 (by rfl) ⟨2347676, by rfl⟩ : syracuseStep 3130235 = 4695353) B4695353
theorem B2086823 : Blo 2085435 2086823 := bstep (se 1 (by rfl) ⟨1565117, by rfl⟩ : syracuseStep 2086823 = 3130235) B3130235
theorem B2347681 : Blo 2085435 2347681 := bbase (se 2 (by rfl) ⟨880380, by rfl⟩ : syracuseStep 2347681 = 1760761) (by norm_num)
theorem B3130241 : Blo 2085435 3130241 := bstep (se 2 (by rfl) ⟨1173840, by rfl⟩ : syracuseStep 3130241 = 2347681) B2347681
theorem B2086827 : Blo 2085435 2086827 := bstep (se 1 (by rfl) ⟨1565120, by rfl⟩ : syracuseStep 2086827 = 3130241) B3130241
theorem B5282293 : Blo 2085435 5282293 := bbase (se 5 (by rfl) ⟨247607, by rfl⟩ : syracuseStep 5282293 = 495215) (by norm_num)
theorem B7043057 : Blo 2085435 7043057 := bstep (se 2 (by rfl) ⟨2641146, by rfl⟩ : syracuseStep 7043057 = 5282293) B5282293
theorem B4695371 : Blo 2085435 4695371 := bstep (se 1 (by rfl) ⟨3521528, by rfl⟩ : syracuseStep 4695371 = 7043057) B7043057
theorem B3130247 : Blo 2085435 3130247 := bstep (se 1 (by rfl) ⟨2347685, by rfl⟩ : syracuseStep 3130247 = 4695371) B4695371
theorem B2086831 : Blo 2085435 2086831 := bstep (se 1 (by rfl) ⟨1565123, by rfl⟩ : syracuseStep 2086831 = 3130247) B3130247
theorem B3130253 : Blo 2085435 3130253 := bbase (se 3 (by rfl) ⟨586922, by rfl⟩ : syracuseStep 3130253 = 1173845) (by norm_num)
theorem B2086835 : Blo 2085435 2086835 := bstep (se 1 (by rfl) ⟨1565126, by rfl⟩ : syracuseStep 2086835 = 3130253) B3130253
theorem B4695389 : Blo 2085435 4695389 := bbase (se 3 (by rfl) ⟨880385, by rfl⟩ : syracuseStep 4695389 = 1760771) (by norm_num)
theorem B3130259 : Blo 2085435 3130259 := bstep (se 1 (by rfl) ⟨2347694, by rfl⟩ : syracuseStep 3130259 = 4695389) B4695389
theorem B2086839 : Blo 2085435 2086839 := bstep (se 1 (by rfl) ⟨1565129, by rfl⟩ : syracuseStep 2086839 = 3130259) B3130259
theorem B3521549 : Blo 2085435 3521549 := bbase (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) (by norm_num)
theorem B2347699 : Blo 2085435 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B3130265 : Blo 2085435 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B2086843 : Blo 2085435 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B5640853 : Blo 2085435 5640853 := bbase (se 6 (by rfl) ⟨132207, by rfl⟩ : syracuseStep 5640853 = 264415) (by norm_num)
theorem B7521137 : Blo 2085435 7521137 := bstep (se 2 (by rfl) ⟨2820426, by rfl⟩ : syracuseStep 7521137 = 5640853) B5640853
theorem B5014091 : Blo 2085435 5014091 := bstep (se 1 (by rfl) ⟨3760568, by rfl⟩ : syracuseStep 5014091 = 7521137) B7521137
theorem B3342727 : Blo 2085435 3342727 := bstep (se 1 (by rfl) ⟨2507045, by rfl⟩ : syracuseStep 3342727 = 5014091) B5014091
theorem B17827877 : Blo 2085435 17827877 := bstep (se 4 (by rfl) ⟨1671363, by rfl⟩ : syracuseStep 17827877 = 3342727) B3342727
theorem B11885251 : Blo 2085435 11885251 := bstep (se 1 (by rfl) ⟨8913938, by rfl⟩ : syracuseStep 11885251 = 17827877) B17827877
theorem B15847001 : Blo 2085435 15847001 := bstep (se 2 (by rfl) ⟨5942625, by rfl⟩ : syracuseStep 15847001 = 11885251) B11885251
theorem B10564667 : Blo 2085435 10564667 := bstep (se 1 (by rfl) ⟨7923500, by rfl⟩ : syracuseStep 10564667 = 15847001) B15847001
theorem B7043111 : Blo 2085435 7043111 := bstep (se 1 (by rfl) ⟨5282333, by rfl⟩ : syracuseStep 7043111 = 10564667) B10564667
theorem B4695407 : Blo 2085435 4695407 := bstep (se 1 (by rfl) ⟨3521555, by rfl⟩ : syracuseStep 4695407 = 7043111) B7043111
theorem B3130271 : Blo 2085435 3130271 := bstep (se 1 (by rfl) ⟨2347703, by rfl⟩ : syracuseStep 3130271 = 4695407) B4695407
theorem B2086847 : Blo 2085435 2086847 := bstep (se 1 (by rfl) ⟨1565135, by rfl⟩ : syracuseStep 2086847 = 3130271) B3130271
theorem B3130277 : Blo 2085435 3130277 := bbase (se 4 (by rfl) ⟨293463, by rfl⟩ : syracuseStep 3130277 = 586927) (by norm_num)
theorem B2086851 : Blo 2085435 2086851 := bstep (se 1 (by rfl) ⟨1565138, by rfl⟩ : syracuseStep 2086851 = 3130277) B3130277
theorem B2641177 : Blo 2085435 2641177 := bbase (se 2 (by rfl) ⟨990441, by rfl⟩ : syracuseStep 2641177 = 1980883) (by norm_num)
theorem B3521569 : Blo 2085435 3521569 := bstep (se 2 (by rfl) ⟨1320588, by rfl⟩ : syracuseStep 3521569 = 2641177) B2641177
theorem B4695425 : Blo 2085435 4695425 := bstep (se 2 (by rfl) ⟨1760784, by rfl⟩ : syracuseStep 4695425 = 3521569) B3521569
theorem B3130283 : Blo 2085435 3130283 := bstep (se 1 (by rfl) ⟨2347712, by rfl⟩ : syracuseStep 3130283 = 4695425) B4695425
theorem B2086855 : Blo 2085435 2086855 := bstep (se 1 (by rfl) ⟨1565141, by rfl⟩ : syracuseStep 2086855 = 3130283) B3130283
theorem B2347717 : Blo 2085435 2347717 := bbase (se 4 (by rfl) ⟨220098, by rfl⟩ : syracuseStep 2347717 = 440197) (by norm_num)
theorem B3130289 : Blo 2085435 3130289 := bstep (se 2 (by rfl) ⟨1173858, by rfl⟩ : syracuseStep 3130289 = 2347717) B2347717
theorem B2086859 : Blo 2085435 2086859 := bstep (se 1 (by rfl) ⟨1565144, by rfl⟩ : syracuseStep 2086859 = 3130289) B3130289
theorem B3961781 : Blo 2085435 3961781 := bbase (se 5 (by rfl) ⟨185708, by rfl⟩ : syracuseStep 3961781 = 371417) (by norm_num)
theorem B2641187 : Blo 2085435 2641187 := bstep (se 1 (by rfl) ⟨1980890, by rfl⟩ : syracuseStep 2641187 = 3961781) B3961781
theorem B7043165 : Blo 2085435 7043165 := bstep (se 3 (by rfl) ⟨1320593, by rfl⟩ : syracuseStep 7043165 = 2641187) B2641187
theorem B4695443 : Blo 2085435 4695443 := bstep (se 1 (by rfl) ⟨3521582, by rfl⟩ : syracuseStep 4695443 = 7043165) B7043165
theorem B3130295 : Blo 2085435 3130295 := bstep (se 1 (by rfl) ⟨2347721, by rfl⟩ : syracuseStep 3130295 = 4695443) B4695443
theorem B2086863 : Blo 2085435 2086863 := bstep (se 1 (by rfl) ⟨1565147, by rfl⟩ : syracuseStep 2086863 = 3130295) B3130295
theorem B3130301 : Blo 2085435 3130301 := bbase (se 3 (by rfl) ⟨586931, by rfl⟩ : syracuseStep 3130301 = 1173863) (by norm_num)
theorem B2086867 : Blo 2085435 2086867 := bstep (se 1 (by rfl) ⟨1565150, by rfl⟩ : syracuseStep 2086867 = 3130301) B3130301
theorem B4695461 : Blo 2085435 4695461 := bbase (se 4 (by rfl) ⟨440199, by rfl⟩ : syracuseStep 4695461 = 880399) (by norm_num)
theorem B3130307 : Blo 2085435 3130307 := bstep (se 1 (by rfl) ⟨2347730, by rfl⟩ : syracuseStep 3130307 = 4695461) B4695461
theorem B2086871 : Blo 2085435 2086871 := bstep (se 1 (by rfl) ⟨1565153, by rfl⟩ : syracuseStep 2086871 = 3130307) B3130307
theorem B5282405 : Blo 2085435 5282405 := bbase (se 4 (by rfl) ⟨495225, by rfl⟩ : syracuseStep 5282405 = 990451) (by norm_num)
theorem B3521603 : Blo 2085435 3521603 := bstep (se 1 (by rfl) ⟨2641202, by rfl⟩ : syracuseStep 3521603 = 5282405) B5282405
theorem B2347735 : Blo 2085435 2347735 := bstep (se 1 (by rfl) ⟨1760801, by rfl⟩ : syracuseStep 2347735 = 3521603) B3521603
theorem B3130313 : Blo 2085435 3130313 := bstep (se 2 (by rfl) ⟨1173867, by rfl⟩ : syracuseStep 3130313 = 2347735) B2347735
theorem B2086875 : Blo 2085435 2086875 := bstep (se 1 (by rfl) ⟨1565156, by rfl⟩ : syracuseStep 2086875 = 3130313) B3130313
theorem B2115353 : Blo 2085435 2115353 := bbase (se 2 (by rfl) ⟨793257, by rfl⟩ : syracuseStep 2115353 = 1586515) (by norm_num)
theorem B5640941 : Blo 2085435 5640941 := bstep (se 3 (by rfl) ⟨1057676, by rfl⟩ : syracuseStep 5640941 = 2115353) B2115353
theorem B3760627 : Blo 2085435 3760627 := bstep (se 1 (by rfl) ⟨2820470, by rfl⟩ : syracuseStep 3760627 = 5640941) B5640941
theorem B5014169 : Blo 2085435 5014169 := bstep (se 2 (by rfl) ⟨1880313, by rfl⟩ : syracuseStep 5014169 = 3760627) B3760627
theorem B3342779 : Blo 2085435 3342779 := bstep (se 1 (by rfl) ⟨2507084, by rfl⟩ : syracuseStep 3342779 = 5014169) B5014169
theorem B2228519 : Blo 2085435 2228519 := bstep (se 1 (by rfl) ⟨1671389, by rfl⟩ : syracuseStep 2228519 = 3342779) B3342779
theorem B5942717 : Blo 2085435 5942717 := bstep (se 3 (by rfl) ⟨1114259, by rfl⟩ : syracuseStep 5942717 = 2228519) B2228519
theorem B3961811 : Blo 2085435 3961811 := bstep (se 1 (by rfl) ⟨2971358, by rfl⟩ : syracuseStep 3961811 = 5942717) B5942717
theorem B10564829 : Blo 2085435 10564829 := bstep (se 3 (by rfl) ⟨1980905, by rfl⟩ : syracuseStep 10564829 = 3961811) B3961811
theorem B7043219 : Blo 2085435 7043219 := bstep (se 1 (by rfl) ⟨5282414, by rfl⟩ : syracuseStep 7043219 = 10564829) B10564829
theorem B4695479 : Blo 2085435 4695479 := bstep (se 1 (by rfl) ⟨3521609, by rfl⟩ : syracuseStep 4695479 = 7043219) B7043219
theorem B3130319 : Blo 2085435 3130319 := bstep (se 1 (by rfl) ⟨2347739, by rfl⟩ : syracuseStep 3130319 = 4695479) B4695479
theorem B2086879 : Blo 2085435 2086879 := bstep (se 1 (by rfl) ⟨1565159, by rfl⟩ : syracuseStep 2086879 = 3130319) B3130319
theorem B3130325 : Blo 2085435 3130325 := bbase (se 7 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 3130325 = 73367) (by norm_num)
theorem B2086883 : Blo 2085435 2086883 := bstep (se 1 (by rfl) ⟨1565162, by rfl⟩ : syracuseStep 2086883 = 3130325) B3130325
theorem B7923653 : Blo 2085435 7923653 := bbase (se 4 (by rfl) ⟨742842, by rfl⟩ : syracuseStep 7923653 = 1485685) (by norm_num)
theorem B5282435 : Blo 2085435 5282435 := bstep (se 1 (by rfl) ⟨3961826, by rfl⟩ : syracuseStep 5282435 = 7923653) B7923653
theorem B3521623 : Blo 2085435 3521623 := bstep (se 1 (by rfl) ⟨2641217, by rfl⟩ : syracuseStep 3521623 = 5282435) B5282435
theorem B4695497 : Blo 2085435 4695497 := bstep (se 2 (by rfl) ⟨1760811, by rfl⟩ : syracuseStep 4695497 = 3521623) B3521623
theorem B3130331 : Blo 2085435 3130331 := bstep (se 1 (by rfl) ⟨2347748, by rfl⟩ : syracuseStep 3130331 = 4695497) B4695497
theorem B2086887 : Blo 2085435 2086887 := bstep (se 1 (by rfl) ⟨1565165, by rfl⟩ : syracuseStep 2086887 = 3130331) B3130331
theorem B2347753 : Blo 2085435 2347753 := bbase (se 2 (by rfl) ⟨880407, by rfl⟩ : syracuseStep 2347753 = 1760815) (by norm_num)
theorem B3130337 : Blo 2085435 3130337 := bstep (se 2 (by rfl) ⟨1173876, by rfl⟩ : syracuseStep 3130337 = 2347753) B2347753
theorem B2086891 : Blo 2085435 2086891 := bstep (se 1 (by rfl) ⟨1565168, by rfl⟩ : syracuseStep 2086891 = 3130337) B3130337
theorem B11885525 : Blo 2085435 11885525 := bbase (se 7 (by rfl) ⟨139283, by rfl⟩ : syracuseStep 11885525 = 278567) (by norm_num)
theorem B7923683 : Blo 2085435 7923683 := bstep (se 1 (by rfl) ⟨5942762, by rfl⟩ : syracuseStep 7923683 = 11885525) B11885525
theorem B5282455 : Blo 2085435 5282455 := bstep (se 1 (by rfl) ⟨3961841, by rfl⟩ : syracuseStep 5282455 = 7923683) B7923683
theorem B7043273 : Blo 2085435 7043273 := bstep (se 2 (by rfl) ⟨2641227, by rfl⟩ : syracuseStep 7043273 = 5282455) B5282455
theorem B4695515 : Blo 2085435 4695515 := bstep (se 1 (by rfl) ⟨3521636, by rfl⟩ : syracuseStep 4695515 = 7043273) B7043273
theorem B3130343 : Blo 2085435 3130343 := bstep (se 1 (by rfl) ⟨2347757, by rfl⟩ : syracuseStep 3130343 = 4695515) B4695515
theorem B2086895 : Blo 2085435 2086895 := bstep (se 1 (by rfl) ⟨1565171, by rfl⟩ : syracuseStep 2086895 = 3130343) B3130343
theorem B3130349 : Blo 2085435 3130349 := bbase (se 3 (by rfl) ⟨586940, by rfl⟩ : syracuseStep 3130349 = 1173881) (by norm_num)
theorem B2086899 : Blo 2085435 2086899 := bstep (se 1 (by rfl) ⟨1565174, by rfl⟩ : syracuseStep 2086899 = 3130349) B3130349
theorem B4695533 : Blo 2085435 4695533 := bbase (se 3 (by rfl) ⟨880412, by rfl⟩ : syracuseStep 4695533 = 1760825) (by norm_num)
theorem B3130355 : Blo 2085435 3130355 := bstep (se 1 (by rfl) ⟨2347766, by rfl⟩ : syracuseStep 3130355 = 4695533) B4695533
theorem B2086903 : Blo 2085435 2086903 := bstep (se 1 (by rfl) ⟨1565177, by rfl⟩ : syracuseStep 2086903 = 3130355) B3130355
theorem B5014237 : Blo 2085435 5014237 := bbase (se 3 (by rfl) ⟨940169, by rfl⟩ : syracuseStep 5014237 = 1880339) (by norm_num)
theorem B6685649 : Blo 2085435 6685649 := bstep (se 2 (by rfl) ⟨2507118, by rfl⟩ : syracuseStep 6685649 = 5014237) B5014237
theorem B4457099 : Blo 2085435 4457099 := bstep (se 1 (by rfl) ⟨3342824, by rfl⟩ : syracuseStep 4457099 = 6685649) B6685649
theorem B2971399 : Blo 2085435 2971399 := bstep (se 1 (by rfl) ⟨2228549, by rfl⟩ : syracuseStep 2971399 = 4457099) B4457099
theorem B3961865 : Blo 2085435 3961865 := bstep (se 2 (by rfl) ⟨1485699, by rfl⟩ : syracuseStep 3961865 = 2971399) B2971399
theorem B2641243 : Blo 2085435 2641243 := bstep (se 1 (by rfl) ⟨1980932, by rfl⟩ : syracuseStep 2641243 = 3961865) B3961865
theorem B3521657 : Blo 2085435 3521657 := bstep (se 2 (by rfl) ⟨1320621, by rfl⟩ : syracuseStep 3521657 = 2641243) B2641243
theorem B2347771 : Blo 2085435 2347771 := bstep (se 1 (by rfl) ⟨1760828, by rfl⟩ : syracuseStep 2347771 = 3521657) B3521657
theorem B3130361 : Blo 2085435 3130361 := bstep (se 2 (by rfl) ⟨1173885, by rfl⟩ : syracuseStep 3130361 = 2347771) B2347771
theorem B2086907 : Blo 2085435 2086907 := bstep (se 1 (by rfl) ⟨1565180, by rfl⟩ : syracuseStep 2086907 = 3130361) B3130361
theorem B5717989 : Blo 2085435 5717989 := bbase (se 4 (by rfl) ⟨536061, by rfl⟩ : syracuseStep 5717989 = 1072123) (by norm_num)
theorem B7623985 : Blo 2085435 7623985 := bstep (se 2 (by rfl) ⟨2858994, by rfl⟩ : syracuseStep 7623985 = 5717989) B5717989
theorem B10165313 : Blo 2085435 10165313 := bstep (se 2 (by rfl) ⟨3811992, by rfl⟩ : syracuseStep 10165313 = 7623985) B7623985
theorem B6776875 : Blo 2085435 6776875 := bstep (se 1 (by rfl) ⟨5082656, by rfl⟩ : syracuseStep 6776875 = 10165313) B10165313
theorem B36143333 : Blo 2085435 36143333 := bstep (se 4 (by rfl) ⟨3388437, by rfl⟩ : syracuseStep 36143333 = 6776875) B6776875
theorem B24095555 : Blo 2085435 24095555 := bstep (se 1 (by rfl) ⟨18071666, by rfl⟩ : syracuseStep 24095555 = 36143333) B36143333
theorem B16063703 : Blo 2085435 16063703 := bstep (se 1 (by rfl) ⟨12047777, by rfl⟩ : syracuseStep 16063703 = 24095555) B24095555
theorem B10709135 : Blo 2085435 10709135 := bstep (se 1 (by rfl) ⟨8031851, by rfl⟩ : syracuseStep 10709135 = 16063703) B16063703
theorem B7139423 : Blo 2085435 7139423 := bstep (se 1 (by rfl) ⟨5354567, by rfl⟩ : syracuseStep 7139423 = 10709135) B10709135
theorem B4759615 : Blo 2085435 4759615 := bstep (se 1 (by rfl) ⟨3569711, by rfl⟩ : syracuseStep 4759615 = 7139423) B7139423
theorem B6346153 : Blo 2085435 6346153 := bstep (se 2 (by rfl) ⟨2379807, by rfl⟩ : syracuseStep 6346153 = 4759615) B4759615
theorem B33846149 : Blo 2085435 33846149 := bstep (se 4 (by rfl) ⟨3173076, by rfl⟩ : syracuseStep 33846149 = 6346153) B6346153
theorem B22564099 : Blo 2085435 22564099 := bstep (se 1 (by rfl) ⟨16923074, by rfl⟩ : syracuseStep 22564099 = 33846149) B33846149
theorem B120341861 : Blo 2085435 120341861 := bstep (se 4 (by rfl) ⟨11282049, by rfl⟩ : syracuseStep 120341861 = 22564099) B22564099
theorem B80227907 : Blo 2085435 80227907 := bstep (se 1 (by rfl) ⟨60170930, by rfl⟩ : syracuseStep 80227907 = 120341861) B120341861
theorem B53485271 : Blo 2085435 53485271 := bstep (se 1 (by rfl) ⟨40113953, by rfl⟩ : syracuseStep 53485271 = 80227907) B80227907
theorem B35656847 : Blo 2085435 35656847 := bstep (se 1 (by rfl) ⟨26742635, by rfl⟩ : syracuseStep 35656847 = 53485271) B53485271
theorem B23771231 : Blo 2085435 23771231 := bstep (se 1 (by rfl) ⟨17828423, by rfl⟩ : syracuseStep 23771231 = 35656847) B35656847
theorem B15847487 : Blo 2085435 15847487 := bstep (se 1 (by rfl) ⟨11885615, by rfl⟩ : syracuseStep 15847487 = 23771231) B23771231
theorem B10564991 : Blo 2085435 10564991 := bstep (se 1 (by rfl) ⟨7923743, by rfl⟩ : syracuseStep 10564991 = 15847487) B15847487
theorem B7043327 : Blo 2085435 7043327 := bstep (se 1 (by rfl) ⟨5282495, by rfl⟩ : syracuseStep 7043327 = 10564991) B10564991
theorem B4695551 : Blo 2085435 4695551 := bstep (se 1 (by rfl) ⟨3521663, by rfl⟩ : syracuseStep 4695551 = 7043327) B7043327
theorem B3130367 : Blo 2085435 3130367 := bstep (se 1 (by rfl) ⟨2347775, by rfl⟩ : syracuseStep 3130367 = 4695551) B4695551
theorem B2086911 : Blo 2085435 2086911 := bstep (se 1 (by rfl) ⟨1565183, by rfl⟩ : syracuseStep 2086911 = 3130367) B3130367
theorem B3130373 : Blo 2085435 3130373 := bbase (se 4 (by rfl) ⟨293472, by rfl⟩ : syracuseStep 3130373 = 586945) (by norm_num)
theorem B2086915 : Blo 2085435 2086915 := bstep (se 1 (by rfl) ⟨1565186, by rfl⟩ : syracuseStep 2086915 = 3130373) B3130373
theorem B3521677 : Blo 2085435 3521677 := bbase (se 3 (by rfl) ⟨660314, by rfl⟩ : syracuseStep 3521677 = 1320629) (by norm_num)
theorem B4695569 : Blo 2085435 4695569 := bstep (se 2 (by rfl) ⟨1760838, by rfl⟩ : syracuseStep 4695569 = 3521677) B3521677
theorem B3130379 : Blo 2085435 3130379 := bstep (se 1 (by rfl) ⟨2347784, by rfl⟩ : syracuseStep 3130379 = 4695569) B4695569
theorem B2086919 : Blo 2085435 2086919 := bstep (se 1 (by rfl) ⟨1565189, by rfl⟩ : syracuseStep 2086919 = 3130379) B3130379
theorem B2347789 : Blo 2085435 2347789 := bbase (se 3 (by rfl) ⟨440210, by rfl⟩ : syracuseStep 2347789 = 880421) (by norm_num)
theorem B3130385 : Blo 2085435 3130385 := bstep (se 2 (by rfl) ⟨1173894, by rfl⟩ : syracuseStep 3130385 = 2347789) B2347789
theorem B2086923 : Blo 2085435 2086923 := bstep (se 1 (by rfl) ⟨1565192, by rfl⟩ : syracuseStep 2086923 = 3130385) B3130385
theorem B7043381 : Blo 2085435 7043381 := bbase (se 5 (by rfl) ⟨330158, by rfl⟩ : syracuseStep 7043381 = 660317) (by norm_num)
theorem B4695587 : Blo 2085435 4695587 := bstep (se 1 (by rfl) ⟨3521690, by rfl⟩ : syracuseStep 4695587 = 7043381) B7043381
theorem B3130391 : Blo 2085435 3130391 := bstep (se 1 (by rfl) ⟨2347793, by rfl⟩ : syracuseStep 3130391 = 4695587) B4695587
theorem B2086927 : Blo 2085435 2086927 := bstep (se 1 (by rfl) ⟨1565195, by rfl⟩ : syracuseStep 2086927 = 3130391) B3130391
theorem B3130397 : Blo 2085435 3130397 := bbase (se 3 (by rfl) ⟨586949, by rfl⟩ : syracuseStep 3130397 = 1173899) (by norm_num)
theorem B2086931 : Blo 2085435 2086931 := bstep (se 1 (by rfl) ⟨1565198, by rfl⟩ : syracuseStep 2086931 = 3130397) B3130397
theorem B4695605 : Blo 2085435 4695605 := bbase (se 5 (by rfl) ⟨220106, by rfl⟩ : syracuseStep 4695605 = 440213) (by norm_num)
theorem B3130403 : Blo 2085435 3130403 := bstep (se 1 (by rfl) ⟨2347802, by rfl⟩ : syracuseStep 3130403 = 4695605) B4695605
theorem B2086935 : Blo 2085435 2086935 := bstep (se 1 (by rfl) ⟨1565201, by rfl⟩ : syracuseStep 2086935 = 3130403) B3130403
theorem B2677321 : Blo 2085435 2677321 := bbase (se 2 (by rfl) ⟨1003995, by rfl⟩ : syracuseStep 2677321 = 2007991) (by norm_num)
theorem B3569761 : Blo 2085435 3569761 := bstep (se 2 (by rfl) ⟨1338660, by rfl⟩ : syracuseStep 3569761 = 2677321) B2677321
theorem B19038725 : Blo 2085435 19038725 := bstep (se 4 (by rfl) ⟨1784880, by rfl⟩ : syracuseStep 19038725 = 3569761) B3569761
theorem B12692483 : Blo 2085435 12692483 := bstep (se 1 (by rfl) ⟨9519362, by rfl⟩ : syracuseStep 12692483 = 19038725) B19038725
theorem B8461655 : Blo 2085435 8461655 := bstep (se 1 (by rfl) ⟨6346241, by rfl⟩ : syracuseStep 8461655 = 12692483) B12692483
theorem B5641103 : Blo 2085435 5641103 := bstep (se 1 (by rfl) ⟨4230827, by rfl⟩ : syracuseStep 5641103 = 8461655) B8461655
theorem B3760735 : Blo 2085435 3760735 := bstep (se 1 (by rfl) ⟨2820551, by rfl⟩ : syracuseStep 3760735 = 5641103) B5641103
theorem B5014313 : Blo 2085435 5014313 := bstep (se 2 (by rfl) ⟨1880367, by rfl⟩ : syracuseStep 5014313 = 3760735) B3760735
theorem B3342875 : Blo 2085435 3342875 := bstep (se 1 (by rfl) ⟨2507156, by rfl⟩ : syracuseStep 3342875 = 5014313) B5014313
theorem B8914333 : Blo 2085435 8914333 := bstep (se 3 (by rfl) ⟨1671437, by rfl⟩ : syracuseStep 8914333 = 3342875) B3342875
theorem B11885777 : Blo 2085435 11885777 := bstep (se 2 (by rfl) ⟨4457166, by rfl⟩ : syracuseStep 11885777 = 8914333) B8914333
theorem B7923851 : Blo 2085435 7923851 := bstep (se 1 (by rfl) ⟨5942888, by rfl⟩ : syracuseStep 7923851 = 11885777) B11885777
theorem B5282567 : Blo 2085435 5282567 := bstep (se 1 (by rfl) ⟨3961925, by rfl⟩ : syracuseStep 5282567 = 7923851) B7923851
theorem B3521711 : Blo 2085435 3521711 := bstep (se 1 (by rfl) ⟨2641283, by rfl⟩ : syracuseStep 3521711 = 5282567) B5282567
theorem B2347807 : Blo 2085435 2347807 := bstep (se 1 (by rfl) ⟨1760855, by rfl⟩ : syracuseStep 2347807 = 3521711) B3521711
theorem B3130409 : Blo 2085435 3130409 := bstep (se 2 (by rfl) ⟨1173903, by rfl⟩ : syracuseStep 3130409 = 2347807) B2347807
theorem B2086939 : Blo 2085435 2086939 := bstep (se 1 (by rfl) ⟨1565204, by rfl⟩ : syracuseStep 2086939 = 3130409) B3130409
theorem B2507161 : Blo 2085435 2507161 := bbase (se 2 (by rfl) ⟨940185, by rfl⟩ : syracuseStep 2507161 = 1880371) (by norm_num)
theorem B3342881 : Blo 2085435 3342881 := bstep (se 2 (by rfl) ⟨1253580, by rfl⟩ : syracuseStep 3342881 = 2507161) B2507161
theorem B8914349 : Blo 2085435 8914349 := bstep (se 3 (by rfl) ⟨1671440, by rfl⟩ : syracuseStep 8914349 = 3342881) B3342881
theorem B5942899 : Blo 2085435 5942899 := bstep (se 1 (by rfl) ⟨4457174, by rfl⟩ : syracuseStep 5942899 = 8914349) B8914349
theorem B7923865 : Blo 2085435 7923865 := bstep (se 2 (by rfl) ⟨2971449, by rfl⟩ : syracuseStep 7923865 = 5942899) B5942899
theorem B10565153 : Blo 2085435 10565153 := bstep (se 2 (by rfl) ⟨3961932, by rfl⟩ : syracuseStep 10565153 = 7923865) B7923865
theorem B7043435 : Blo 2085435 7043435 := bstep (se 1 (by rfl) ⟨5282576, by rfl⟩ : syracuseStep 7043435 = 10565153) B10565153
theorem B4695623 : Blo 2085435 4695623 := bstep (se 1 (by rfl) ⟨3521717, by rfl⟩ : syracuseStep 4695623 = 7043435) B7043435
theorem B3130415 : Blo 2085435 3130415 := bstep (se 1 (by rfl) ⟨2347811, by rfl⟩ : syracuseStep 3130415 = 4695623) B4695623
theorem B2086943 : Blo 2085435 2086943 := bstep (se 1 (by rfl) ⟨1565207, by rfl⟩ : syracuseStep 2086943 = 3130415) B3130415
theorem B3130421 : Blo 2085435 3130421 := bbase (se 5 (by rfl) ⟨146738, by rfl⟩ : syracuseStep 3130421 = 293477) (by norm_num)
theorem B2086947 : Blo 2085435 2086947 := bstep (se 1 (by rfl) ⟨1565210, by rfl⟩ : syracuseStep 2086947 = 3130421) B3130421
theorem B5282597 : Blo 2085435 5282597 := bbase (se 4 (by rfl) ⟨495243, by rfl⟩ : syracuseStep 5282597 = 990487) (by norm_num)
theorem B3521731 : Blo 2085435 3521731 := bstep (se 1 (by rfl) ⟨2641298, by rfl⟩ : syracuseStep 3521731 = 5282597) B5282597
theorem B4695641 : Blo 2085435 4695641 := bstep (se 2 (by rfl) ⟨1760865, by rfl⟩ : syracuseStep 4695641 = 3521731) B3521731
theorem B3130427 : Blo 2085435 3130427 := bstep (se 1 (by rfl) ⟨2347820, by rfl⟩ : syracuseStep 3130427 = 4695641) B4695641
theorem B2086951 : Blo 2085435 2086951 := bstep (se 1 (by rfl) ⟨1565213, by rfl⟩ : syracuseStep 2086951 = 3130427) B3130427
theorem B2347825 : Blo 2085435 2347825 := bbase (se 2 (by rfl) ⟨880434, by rfl⟩ : syracuseStep 2347825 = 1760869) (by norm_num)
theorem B3130433 : Blo 2085435 3130433 := bstep (se 2 (by rfl) ⟨1173912, by rfl⟩ : syracuseStep 3130433 = 2347825) B2347825
theorem B2086955 : Blo 2085435 2086955 := bstep (se 1 (by rfl) ⟨1565216, by rfl⟩ : syracuseStep 2086955 = 3130433) B3130433
theorem B5641157 : Blo 2085435 5641157 := bbase (se 4 (by rfl) ⟨528858, by rfl⟩ : syracuseStep 5641157 = 1057717) (by norm_num)
theorem B3760771 : Blo 2085435 3760771 := bstep (se 1 (by rfl) ⟨2820578, by rfl⟩ : syracuseStep 3760771 = 5641157) B5641157
theorem B5014361 : Blo 2085435 5014361 := bstep (se 2 (by rfl) ⟨1880385, by rfl⟩ : syracuseStep 5014361 = 3760771) B3760771
theorem B3342907 : Blo 2085435 3342907 := bstep (se 1 (by rfl) ⟨2507180, by rfl⟩ : syracuseStep 3342907 = 5014361) B5014361
theorem B4457209 : Blo 2085435 4457209 := bstep (se 2 (by rfl) ⟨1671453, by rfl⟩ : syracuseStep 4457209 = 3342907) B3342907
theorem B5942945 : Blo 2085435 5942945 := bstep (se 2 (by rfl) ⟨2228604, by rfl⟩ : syracuseStep 5942945 = 4457209) B4457209
theorem B3961963 : Blo 2085435 3961963 := bstep (se 1 (by rfl) ⟨2971472, by rfl⟩ : syracuseStep 3961963 = 5942945) B5942945
theorem B5282617 : Blo 2085435 5282617 := bstep (se 2 (by rfl) ⟨1980981, by rfl⟩ : syracuseStep 5282617 = 3961963) B3961963
theorem B7043489 : Blo 2085435 7043489 := bstep (se 2 (by rfl) ⟨2641308, by rfl⟩ : syracuseStep 7043489 = 5282617) B5282617
theorem B4695659 : Blo 2085435 4695659 := bstep (se 1 (by rfl) ⟨3521744, by rfl⟩ : syracuseStep 4695659 = 7043489) B7043489
theorem B3130439 : Blo 2085435 3130439 := bstep (se 1 (by rfl) ⟨2347829, by rfl⟩ : syracuseStep 3130439 = 4695659) B4695659
theorem B2086959 : Blo 2085435 2086959 := bstep (se 1 (by rfl) ⟨1565219, by rfl⟩ : syracuseStep 2086959 = 3130439) B3130439
theorem B3130445 : Blo 2085435 3130445 := bbase (se 3 (by rfl) ⟨586958, by rfl⟩ : syracuseStep 3130445 = 1173917) (by norm_num)
theorem B2086963 : Blo 2085435 2086963 := bstep (se 1 (by rfl) ⟨1565222, by rfl⟩ : syracuseStep 2086963 = 3130445) B3130445
theorem B4695677 : Blo 2085435 4695677 := bbase (se 3 (by rfl) ⟨880439, by rfl⟩ : syracuseStep 4695677 = 1760879) (by norm_num)
theorem B3130451 : Blo 2085435 3130451 := bstep (se 1 (by rfl) ⟨2347838, by rfl⟩ : syracuseStep 3130451 = 4695677) B4695677
theorem B2086967 : Blo 2085435 2086967 := bstep (se 1 (by rfl) ⟨1565225, by rfl⟩ : syracuseStep 2086967 = 3130451) B3130451
theorem B3521765 : Blo 2085435 3521765 := bbase (se 4 (by rfl) ⟨330165, by rfl⟩ : syracuseStep 3521765 = 660331) (by norm_num)
theorem B2347843 : Blo 2085435 2347843 := bstep (se 1 (by rfl) ⟨1760882, by rfl⟩ : syracuseStep 2347843 = 3521765) B3521765
theorem B3130457 : Blo 2085435 3130457 := bstep (se 2 (by rfl) ⟨1173921, by rfl⟩ : syracuseStep 3130457 = 2347843) B2347843
theorem B2086971 : Blo 2085435 2086971 := bstep (se 1 (by rfl) ⟨1565228, by rfl⟩ : syracuseStep 2086971 = 3130457) B3130457
theorem B12048149 : Blo 2085435 12048149 := bbase (se 6 (by rfl) ⟨282378, by rfl⟩ : syracuseStep 12048149 = 564757) (by norm_num)
theorem B32128397 : Blo 2085435 32128397 := bstep (se 3 (by rfl) ⟨6024074, by rfl⟩ : syracuseStep 32128397 = 12048149) B12048149
theorem B21418931 : Blo 2085435 21418931 := bstep (se 1 (by rfl) ⟨16064198, by rfl⟩ : syracuseStep 21418931 = 32128397) B32128397
theorem B57117149 : Blo 2085435 57117149 := bstep (se 3 (by rfl) ⟨10709465, by rfl⟩ : syracuseStep 57117149 = 21418931) B21418931
theorem B38078099 : Blo 2085435 38078099 := bstep (se 1 (by rfl) ⟨28558574, by rfl⟩ : syracuseStep 38078099 = 57117149) B57117149
theorem B25385399 : Blo 2085435 25385399 := bstep (se 1 (by rfl) ⟨19039049, by rfl⟩ : syracuseStep 25385399 = 38078099) B38078099
theorem B16923599 : Blo 2085435 16923599 := bstep (se 1 (by rfl) ⟨12692699, by rfl⟩ : syracuseStep 16923599 = 25385399) B25385399
theorem B11282399 : Blo 2085435 11282399 := bstep (se 1 (by rfl) ⟨8461799, by rfl⟩ : syracuseStep 11282399 = 16923599) B16923599
theorem B7521599 : Blo 2085435 7521599 := bstep (se 1 (by rfl) ⟨5641199, by rfl⟩ : syracuseStep 7521599 = 11282399) B11282399
theorem B5014399 : Blo 2085435 5014399 := bstep (se 1 (by rfl) ⟨3760799, by rfl⟩ : syracuseStep 5014399 = 7521599) B7521599
theorem B6685865 : Blo 2085435 6685865 := bstep (se 2 (by rfl) ⟨2507199, by rfl⟩ : syracuseStep 6685865 = 5014399) B5014399
theorem B4457243 : Blo 2085435 4457243 := bstep (se 1 (by rfl) ⟨3342932, by rfl⟩ : syracuseStep 4457243 = 6685865) B6685865
theorem B2971495 : Blo 2085435 2971495 := bstep (se 1 (by rfl) ⟨2228621, by rfl⟩ : syracuseStep 2971495 = 4457243) B4457243
theorem B15847973 : Blo 2085435 15847973 := bstep (se 4 (by rfl) ⟨1485747, by rfl⟩ : syracuseStep 15847973 = 2971495) B2971495
theorem B10565315 : Blo 2085435 10565315 := bstep (se 1 (by rfl) ⟨7923986, by rfl⟩ : syracuseStep 10565315 = 15847973) B15847973
theorem B7043543 : Blo 2085435 7043543 := bstep (se 1 (by rfl) ⟨5282657, by rfl⟩ : syracuseStep 7043543 = 10565315) B10565315
theorem B4695695 : Blo 2085435 4695695 := bstep (se 1 (by rfl) ⟨3521771, by rfl⟩ : syracuseStep 4695695 = 7043543) B7043543
theorem B3130463 : Blo 2085435 3130463 := bstep (se 1 (by rfl) ⟨2347847, by rfl⟩ : syracuseStep 3130463 = 4695695) B4695695
theorem B2086975 : Blo 2085435 2086975 := bstep (se 1 (by rfl) ⟨1565231, by rfl⟩ : syracuseStep 2086975 = 3130463) B3130463
theorem B3130469 : Blo 2085435 3130469 := bbase (se 4 (by rfl) ⟨293481, by rfl⟩ : syracuseStep 3130469 = 586963) (by norm_num)
theorem B2086979 : Blo 2085435 2086979 := bstep (se 1 (by rfl) ⟨1565234, by rfl⟩ : syracuseStep 2086979 = 3130469) B3130469
theorem B4457261 : Blo 2085435 4457261 := bbase (se 3 (by rfl) ⟨835736, by rfl⟩ : syracuseStep 4457261 = 1671473) (by norm_num)
theorem B2971507 : Blo 2085435 2971507 := bstep (se 1 (by rfl) ⟨2228630, by rfl⟩ : syracuseStep 2971507 = 4457261) B4457261
theorem B3962009 : Blo 2085435 3962009 := bstep (se 2 (by rfl) ⟨1485753, by rfl⟩ : syracuseStep 3962009 = 2971507) B2971507
theorem B2641339 : Blo 2085435 2641339 := bstep (se 1 (by rfl) ⟨1981004, by rfl⟩ : syracuseStep 2641339 = 3962009) B3962009
theorem B3521785 : Blo 2085435 3521785 := bstep (se 2 (by rfl) ⟨1320669, by rfl⟩ : syracuseStep 3521785 = 2641339) B2641339
theorem B4695713 : Blo 2085435 4695713 := bstep (se 2 (by rfl) ⟨1760892, by rfl⟩ : syracuseStep 4695713 = 3521785) B3521785
theorem B3130475 : Blo 2085435 3130475 := bstep (se 1 (by rfl) ⟨2347856, by rfl⟩ : syracuseStep 3130475 = 4695713) B4695713
theorem B2086983 : Blo 2085435 2086983 := bstep (se 1 (by rfl) ⟨1565237, by rfl⟩ : syracuseStep 2086983 = 3130475) B3130475
theorem B2347861 : Blo 2085435 2347861 := bbase (se 9 (by rfl) ⟨6878, by rfl⟩ : syracuseStep 2347861 = 13757) (by norm_num)
theorem B3130481 : Blo 2085435 3130481 := bstep (se 2 (by rfl) ⟨1173930, by rfl⟩ : syracuseStep 3130481 = 2347861) B2347861
theorem B2086987 : Blo 2085435 2086987 := bstep (se 1 (by rfl) ⟨1565240, by rfl⟩ : syracuseStep 2086987 = 3130481) B3130481
theorem B2641349 : Blo 2085435 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B7043597 : Blo 2085435 7043597 := bstep (se 3 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 7043597 = 2641349) B2641349
theorem B4695731 : Blo 2085435 4695731 := bstep (se 1 (by rfl) ⟨3521798, by rfl⟩ : syracuseStep 4695731 = 7043597) B7043597
theorem B3130487 : Blo 2085435 3130487 := bstep (se 1 (by rfl) ⟨2347865, by rfl⟩ : syracuseStep 3130487 = 4695731) B4695731
theorem B2086991 : Blo 2085435 2086991 := bstep (se 1 (by rfl) ⟨1565243, by rfl⟩ : syracuseStep 2086991 = 3130487) B3130487
theorem B3130493 : Blo 2085435 3130493 := bbase (se 3 (by rfl) ⟨586967, by rfl⟩ : syracuseStep 3130493 = 1173935) (by norm_num)
theorem B2086995 : Blo 2085435 2086995 := bstep (se 1 (by rfl) ⟨1565246, by rfl⟩ : syracuseStep 2086995 = 3130493) B3130493
theorem B4695749 : Blo 2085435 4695749 := bbase (se 4 (by rfl) ⟨440226, by rfl⟩ : syracuseStep 4695749 = 880453) (by norm_num)
theorem B3130499 : Blo 2085435 3130499 := bstep (se 1 (by rfl) ⟨2347874, by rfl⟩ : syracuseStep 3130499 = 4695749) B4695749
theorem B2086999 : Blo 2085435 2086999 := bstep (se 1 (by rfl) ⟨1565249, by rfl⟩ : syracuseStep 2086999 = 3130499) B3130499
theorem B9519653 : Blo 2085435 9519653 := bbase (se 4 (by rfl) ⟨892467, by rfl⟩ : syracuseStep 9519653 = 1784935) (by norm_num)
theorem B6346435 : Blo 2085435 6346435 := bstep (se 1 (by rfl) ⟨4759826, by rfl⟩ : syracuseStep 6346435 = 9519653) B9519653
theorem B8461913 : Blo 2085435 8461913 := bstep (se 2 (by rfl) ⟨3173217, by rfl⟩ : syracuseStep 8461913 = 6346435) B6346435
theorem B22565101 : Blo 2085435 22565101 := bstep (se 3 (by rfl) ⟨4230956, by rfl⟩ : syracuseStep 22565101 = 8461913) B8461913
theorem B30086801 : Blo 2085435 30086801 := bstep (se 2 (by rfl) ⟨11282550, by rfl⟩ : syracuseStep 30086801 = 22565101) B22565101
theorem B20057867 : Blo 2085435 20057867 := bstep (se 1 (by rfl) ⟨15043400, by rfl⟩ : syracuseStep 20057867 = 30086801) B30086801
theorem B13371911 : Blo 2085435 13371911 := bstep (se 1 (by rfl) ⟨10028933, by rfl⟩ : syracuseStep 13371911 = 20057867) B20057867
theorem B8914607 : Blo 2085435 8914607 := bstep (se 1 (by rfl) ⟨6685955, by rfl⟩ : syracuseStep 8914607 = 13371911) B13371911
theorem B5943071 : Blo 2085435 5943071 := bstep (se 1 (by rfl) ⟨4457303, by rfl⟩ : syracuseStep 5943071 = 8914607) B8914607
theorem B3962047 : Blo 2085435 3962047 := bstep (se 1 (by rfl) ⟨2971535, by rfl⟩ : syracuseStep 3962047 = 5943071) B5943071
theorem B5282729 : Blo 2085435 5282729 := bstep (se 2 (by rfl) ⟨1981023, by rfl⟩ : syracuseStep 5282729 = 3962047) B3962047
theorem B3521819 : Blo 2085435 3521819 := bstep (se 1 (by rfl) ⟨2641364, by rfl⟩ : syracuseStep 3521819 = 5282729) B5282729
theorem B2347879 : Blo 2085435 2347879 := bstep (se 1 (by rfl) ⟨1760909, by rfl⟩ : syracuseStep 2347879 = 3521819) B3521819
theorem B3130505 : Blo 2085435 3130505 := bstep (se 2 (by rfl) ⟨1173939, by rfl⟩ : syracuseStep 3130505 = 2347879) B2347879
theorem B2087003 : Blo 2085435 2087003 := bstep (se 1 (by rfl) ⟨1565252, by rfl⟩ : syracuseStep 2087003 = 3130505) B3130505
theorem B10565477 : Blo 2085435 10565477 := bbase (se 4 (by rfl) ⟨990513, by rfl⟩ : syracuseStep 10565477 = 1981027) (by norm_num)
theorem B7043651 : Blo 2085435 7043651 := bstep (se 1 (by rfl) ⟨5282738, by rfl⟩ : syracuseStep 7043651 = 10565477) B10565477
theorem B4695767 : Blo 2085435 4695767 := bstep (se 1 (by rfl) ⟨3521825, by rfl⟩ : syracuseStep 4695767 = 7043651) B7043651
theorem B3130511 : Blo 2085435 3130511 := bstep (se 1 (by rfl) ⟨2347883, by rfl⟩ : syracuseStep 3130511 = 4695767) B4695767
theorem B2087007 : Blo 2085435 2087007 := bstep (se 1 (by rfl) ⟨1565255, by rfl⟩ : syracuseStep 2087007 = 3130511) B3130511
theorem B3130517 : Blo 2085435 3130517 := bbase (se 6 (by rfl) ⟨73371, by rfl⟩ : syracuseStep 3130517 = 146743) (by norm_num)
theorem B2087011 : Blo 2085435 2087011 := bstep (se 1 (by rfl) ⟨1565258, by rfl⟩ : syracuseStep 2087011 = 3130517) B3130517
theorem B9649589 : Blo 2085435 9649589 := bbase (se 5 (by rfl) ⟨452324, by rfl⟩ : syracuseStep 9649589 = 904649) (by norm_num)
theorem B25732237 : Blo 2085435 25732237 := bstep (se 3 (by rfl) ⟨4824794, by rfl⟩ : syracuseStep 25732237 = 9649589) B9649589
theorem B34309649 : Blo 2085435 34309649 := bstep (se 2 (by rfl) ⟨12866118, by rfl⟩ : syracuseStep 34309649 = 25732237) B25732237
theorem B22873099 : Blo 2085435 22873099 := bstep (se 1 (by rfl) ⟨17154824, by rfl⟩ : syracuseStep 22873099 = 34309649) B34309649
theorem B30497465 : Blo 2085435 30497465 := bstep (se 2 (by rfl) ⟨11436549, by rfl⟩ : syracuseStep 30497465 = 22873099) B22873099
theorem B20331643 : Blo 2085435 20331643 := bstep (se 1 (by rfl) ⟨15248732, by rfl⟩ : syracuseStep 20331643 = 30497465) B30497465
theorem B27108857 : Blo 2085435 27108857 := bstep (se 2 (by rfl) ⟨10165821, by rfl⟩ : syracuseStep 27108857 = 20331643) B20331643
theorem B18072571 : Blo 2085435 18072571 := bstep (se 1 (by rfl) ⟨13554428, by rfl⟩ : syracuseStep 18072571 = 27108857) B27108857
theorem B24096761 : Blo 2085435 24096761 := bstep (se 2 (by rfl) ⟨9036285, by rfl⟩ : syracuseStep 24096761 = 18072571) B18072571
theorem B16064507 : Blo 2085435 16064507 := bstep (se 1 (by rfl) ⟨12048380, by rfl⟩ : syracuseStep 16064507 = 24096761) B24096761
theorem B10709671 : Blo 2085435 10709671 := bstep (se 1 (by rfl) ⟨8032253, by rfl⟩ : syracuseStep 10709671 = 16064507) B16064507
theorem B14279561 : Blo 2085435 14279561 := bstep (se 2 (by rfl) ⟨5354835, by rfl⟩ : syracuseStep 14279561 = 10709671) B10709671
theorem B9519707 : Blo 2085435 9519707 := bstep (se 1 (by rfl) ⟨7139780, by rfl⟩ : syracuseStep 9519707 = 14279561) B14279561
theorem B25385885 : Blo 2085435 25385885 := bstep (se 3 (by rfl) ⟨4759853, by rfl⟩ : syracuseStep 25385885 = 9519707) B9519707
theorem B16923923 : Blo 2085435 16923923 := bstep (se 1 (by rfl) ⟨12692942, by rfl⟩ : syracuseStep 16923923 = 25385885) B25385885
theorem B11282615 : Blo 2085435 11282615 := bstep (se 1 (by rfl) ⟨8461961, by rfl⟩ : syracuseStep 11282615 = 16923923) B16923923
theorem B7521743 : Blo 2085435 7521743 := bstep (se 1 (by rfl) ⟨5641307, by rfl⟩ : syracuseStep 7521743 = 11282615) B11282615
theorem B5014495 : Blo 2085435 5014495 := bstep (se 1 (by rfl) ⟨3760871, by rfl⟩ : syracuseStep 5014495 = 7521743) B7521743
theorem B6685993 : Blo 2085435 6685993 := bstep (se 2 (by rfl) ⟨2507247, by rfl⟩ : syracuseStep 6685993 = 5014495) B5014495
theorem B8914657 : Blo 2085435 8914657 := bstep (se 2 (by rfl) ⟨3342996, by rfl⟩ : syracuseStep 8914657 = 6685993) B6685993
theorem B11886209 : Blo 2085435 11886209 := bstep (se 2 (by rfl) ⟨4457328, by rfl⟩ : syracuseStep 11886209 = 8914657) B8914657
theorem B7924139 : Blo 2085435 7924139 := bstep (se 1 (by rfl) ⟨5943104, by rfl⟩ : syracuseStep 7924139 = 11886209) B11886209
theorem B5282759 : Blo 2085435 5282759 := bstep (se 1 (by rfl) ⟨3962069, by rfl⟩ : syracuseStep 5282759 = 7924139) B7924139
theorem B3521839 : Blo 2085435 3521839 := bstep (se 1 (by rfl) ⟨2641379, by rfl⟩ : syracuseStep 3521839 = 5282759) B5282759
theorem B4695785 : Blo 2085435 4695785 := bstep (se 2 (by rfl) ⟨1760919, by rfl⟩ : syracuseStep 4695785 = 3521839) B3521839
theorem B3130523 : Blo 2085435 3130523 := bstep (se 1 (by rfl) ⟨2347892, by rfl⟩ : syracuseStep 3130523 = 4695785) B4695785
theorem B2087015 : Blo 2085435 2087015 := bstep (se 1 (by rfl) ⟨1565261, by rfl⟩ : syracuseStep 2087015 = 3130523) B3130523
theorem B2347897 : Blo 2085435 2347897 := bbase (se 2 (by rfl) ⟨880461, by rfl⟩ : syracuseStep 2347897 = 1760923) (by norm_num)
theorem B3130529 : Blo 2085435 3130529 := bstep (se 2 (by rfl) ⟨1173948, by rfl⟩ : syracuseStep 3130529 = 2347897) B2347897
theorem B2087019 : Blo 2085435 2087019 := bstep (se 1 (by rfl) ⟨1565264, by rfl⟩ : syracuseStep 2087019 = 3130529) B3130529
theorem B2507257 : Blo 2085435 2507257 := bbase (se 2 (by rfl) ⟨940221, by rfl⟩ : syracuseStep 2507257 = 1880443) (by norm_num)
theorem B13372037 : Blo 2085435 13372037 := bstep (se 4 (by rfl) ⟨1253628, by rfl⟩ : syracuseStep 13372037 = 2507257) B2507257
theorem B8914691 : Blo 2085435 8914691 := bstep (se 1 (by rfl) ⟨6686018, by rfl⟩ : syracuseStep 8914691 = 13372037) B13372037
theorem B5943127 : Blo 2085435 5943127 := bstep (se 1 (by rfl) ⟨4457345, by rfl⟩ : syracuseStep 5943127 = 8914691) B8914691
theorem B7924169 : Blo 2085435 7924169 := bstep (se 2 (by rfl) ⟨2971563, by rfl⟩ : syracuseStep 7924169 = 5943127) B5943127
theorem B5282779 : Blo 2085435 5282779 := bstep (se 1 (by rfl) ⟨3962084, by rfl⟩ : syracuseStep 5282779 = 7924169) B7924169
theorem B7043705 : Blo 2085435 7043705 := bstep (se 2 (by rfl) ⟨2641389, by rfl⟩ : syracuseStep 7043705 = 5282779) B5282779
theorem B4695803 : Blo 2085435 4695803 := bstep (se 1 (by rfl) ⟨3521852, by rfl⟩ : syracuseStep 4695803 = 7043705) B7043705
theorem B3130535 : Blo 2085435 3130535 := bstep (se 1 (by rfl) ⟨2347901, by rfl⟩ : syracuseStep 3130535 = 4695803) B4695803
theorem B2087023 : Blo 2085435 2087023 := bstep (se 1 (by rfl) ⟨1565267, by rfl⟩ : syracuseStep 2087023 = 3130535) B3130535
theorem B3130541 : Blo 2085435 3130541 := bbase (se 3 (by rfl) ⟨586976, by rfl⟩ : syracuseStep 3130541 = 1173953) (by norm_num)
theorem B2087027 : Blo 2085435 2087027 := bstep (se 1 (by rfl) ⟨1565270, by rfl⟩ : syracuseStep 2087027 = 3130541) B3130541
theorem B4695821 : Blo 2085435 4695821 := bbase (se 3 (by rfl) ⟨880466, by rfl⟩ : syracuseStep 4695821 = 1760933) (by norm_num)
theorem B3130547 : Blo 2085435 3130547 := bstep (se 1 (by rfl) ⟨2347910, by rfl⟩ : syracuseStep 3130547 = 4695821) B4695821
theorem B2087031 : Blo 2085435 2087031 := bstep (se 1 (by rfl) ⟨1565273, by rfl⟩ : syracuseStep 2087031 = 3130547) B3130547
theorem B2641405 : Blo 2085435 2641405 := bbase (se 3 (by rfl) ⟨495263, by rfl⟩ : syracuseStep 2641405 = 990527) (by norm_num)
theorem B3521873 : Blo 2085435 3521873 := bstep (se 2 (by rfl) ⟨1320702, by rfl⟩ : syracuseStep 3521873 = 2641405) B2641405
theorem B2347915 : Blo 2085435 2347915 := bstep (se 1 (by rfl) ⟨1760936, by rfl⟩ : syracuseStep 2347915 = 3521873) B3521873
theorem B3130553 : Blo 2085435 3130553 := bstep (se 2 (by rfl) ⟨1173957, by rfl⟩ : syracuseStep 3130553 = 2347915) B2347915
theorem B2087035 : Blo 2085435 2087035 := bstep (se 1 (by rfl) ⟨1565276, by rfl⟩ : syracuseStep 2087035 = 3130553) B3130553
theorem B6686069 : Blo 2085435 6686069 := bbase (se 5 (by rfl) ⟨313409, by rfl⟩ : syracuseStep 6686069 = 626819) (by norm_num)
theorem B17829517 : Blo 2085435 17829517 := bstep (se 3 (by rfl) ⟨3343034, by rfl⟩ : syracuseStep 17829517 = 6686069) B6686069
theorem B23772689 : Blo 2085435 23772689 := bstep (se 2 (by rfl) ⟨8914758, by rfl⟩ : syracuseStep 23772689 = 17829517) B17829517
theorem B15848459 : Blo 2085435 15848459 := bstep (se 1 (by rfl) ⟨11886344, by rfl⟩ : syracuseStep 15848459 = 23772689) B23772689
theorem B10565639 : Blo 2085435 10565639 := bstep (se 1 (by rfl) ⟨7924229, by rfl⟩ : syracuseStep 10565639 = 15848459) B15848459
theorem B7043759 : Blo 2085435 7043759 := bstep (se 1 (by rfl) ⟨5282819, by rfl⟩ : syracuseStep 7043759 = 10565639) B10565639
theorem B4695839 : Blo 2085435 4695839 := bstep (se 1 (by rfl) ⟨3521879, by rfl⟩ : syracuseStep 4695839 = 7043759) B7043759
theorem B3130559 : Blo 2085435 3130559 := bstep (se 1 (by rfl) ⟨2347919, by rfl⟩ : syracuseStep 3130559 = 4695839) B4695839
theorem B2087039 : Blo 2085435 2087039 := bstep (se 1 (by rfl) ⟨1565279, by rfl⟩ : syracuseStep 2087039 = 3130559) B3130559
theorem B3130565 : Blo 2085435 3130565 := bbase (se 4 (by rfl) ⟨293490, by rfl⟩ : syracuseStep 3130565 = 586981) (by norm_num)
theorem B2087043 : Blo 2085435 2087043 := bstep (se 1 (by rfl) ⟨1565282, by rfl⟩ : syracuseStep 2087043 = 3130565) B3130565
theorem B3521893 : Blo 2085435 3521893 := bbase (se 4 (by rfl) ⟨330177, by rfl⟩ : syracuseStep 3521893 = 660355) (by norm_num)
theorem B4695857 : Blo 2085435 4695857 := bstep (se 2 (by rfl) ⟨1760946, by rfl⟩ : syracuseStep 4695857 = 3521893) B3521893
theorem B3130571 : Blo 2085435 3130571 := bstep (se 1 (by rfl) ⟨2347928, by rfl⟩ : syracuseStep 3130571 = 4695857) B4695857
theorem B2087047 : Blo 2085435 2087047 := bstep (se 1 (by rfl) ⟨1565285, by rfl⟩ : syracuseStep 2087047 = 3130571) B3130571
theorem B2347933 : Blo 2085435 2347933 := bbase (se 3 (by rfl) ⟨440237, by rfl⟩ : syracuseStep 2347933 = 880475) (by norm_num)
theorem B3130577 : Blo 2085435 3130577 := bstep (se 2 (by rfl) ⟨1173966, by rfl⟩ : syracuseStep 3130577 = 2347933) B2347933
theorem B2087051 : Blo 2085435 2087051 := bstep (se 1 (by rfl) ⟨1565288, by rfl⟩ : syracuseStep 2087051 = 3130577) B3130577
theorem B7043813 : Blo 2085435 7043813 := bbase (se 4 (by rfl) ⟨660357, by rfl⟩ : syracuseStep 7043813 = 1320715) (by norm_num)
theorem B4695875 : Blo 2085435 4695875 := bstep (se 1 (by rfl) ⟨3521906, by rfl⟩ : syracuseStep 4695875 = 7043813) B7043813
theorem B3130583 : Blo 2085435 3130583 := bstep (se 1 (by rfl) ⟨2347937, by rfl⟩ : syracuseStep 3130583 = 4695875) B4695875
theorem B2087055 : Blo 2085435 2087055 := bstep (se 1 (by rfl) ⟨1565291, by rfl⟩ : syracuseStep 2087055 = 3130583) B3130583
theorem B3130589 : Blo 2085435 3130589 := bbase (se 3 (by rfl) ⟨586985, by rfl⟩ : syracuseStep 3130589 = 1173971) (by norm_num)
theorem B2087059 : Blo 2085435 2087059 := bstep (se 1 (by rfl) ⟨1565294, by rfl⟩ : syracuseStep 2087059 = 3130589) B3130589
theorem B4695893 : Blo 2085435 4695893 := bbase (se 9 (by rfl) ⟨13757, by rfl⟩ : syracuseStep 4695893 = 27515) (by norm_num)
theorem B3130595 : Blo 2085435 3130595 := bstep (se 1 (by rfl) ⟨2347946, by rfl⟩ : syracuseStep 3130595 = 4695893) B4695893
theorem B2087063 : Blo 2085435 2087063 := bstep (se 1 (by rfl) ⟨1565297, by rfl⟩ : syracuseStep 2087063 = 3130595) B3130595
theorem B5943253 : Blo 2085435 5943253 := bbase (se 7 (by rfl) ⟨69647, by rfl⟩ : syracuseStep 5943253 = 139295) (by norm_num)
theorem B7924337 : Blo 2085435 7924337 := bstep (se 2 (by rfl) ⟨2971626, by rfl⟩ : syracuseStep 7924337 = 5943253) B5943253
theorem B5282891 : Blo 2085435 5282891 := bstep (se 1 (by rfl) ⟨3962168, by rfl⟩ : syracuseStep 5282891 = 7924337) B7924337
theorem B3521927 : Blo 2085435 3521927 := bstep (se 1 (by rfl) ⟨2641445, by rfl⟩ : syracuseStep 3521927 = 5282891) B5282891
theorem B2347951 : Blo 2085435 2347951 := bstep (se 1 (by rfl) ⟨1760963, by rfl⟩ : syracuseStep 2347951 = 3521927) B3521927
theorem B3130601 : Blo 2085435 3130601 := bstep (se 2 (by rfl) ⟨1173975, by rfl⟩ : syracuseStep 3130601 = 2347951) B2347951
theorem B2087067 : Blo 2085435 2087067 := bstep (se 1 (by rfl) ⟨1565300, by rfl⟩ : syracuseStep 2087067 = 3130601) B3130601
theorem B20332181 : Blo 2085435 20332181 := bbase (se 6 (by rfl) ⟨476535, by rfl⟩ : syracuseStep 20332181 = 953071) (by norm_num)
theorem B13554787 : Blo 2085435 13554787 := bstep (se 1 (by rfl) ⟨10166090, by rfl⟩ : syracuseStep 13554787 = 20332181) B20332181
theorem B18073049 : Blo 2085435 18073049 := bstep (se 2 (by rfl) ⟨6777393, by rfl⟩ : syracuseStep 18073049 = 13554787) B13554787
theorem B192779189 : Blo 2085435 192779189 := bstep (se 5 (by rfl) ⟨9036524, by rfl⟩ : syracuseStep 192779189 = 18073049) B18073049
theorem B128519459 : Blo 2085435 128519459 := bstep (se 1 (by rfl) ⟨96389594, by rfl⟩ : syracuseStep 128519459 = 192779189) B192779189
theorem B85679639 : Blo 2085435 85679639 := bstep (se 1 (by rfl) ⟨64259729, by rfl⟩ : syracuseStep 85679639 = 128519459) B128519459
theorem B57119759 : Blo 2085435 57119759 := bstep (se 1 (by rfl) ⟨42839819, by rfl⟩ : syracuseStep 57119759 = 85679639) B85679639
theorem B38079839 : Blo 2085435 38079839 := bstep (se 1 (by rfl) ⟨28559879, by rfl⟩ : syracuseStep 38079839 = 57119759) B57119759
theorem B101546237 : Blo 2085435 101546237 := bstep (se 3 (by rfl) ⟨19039919, by rfl⟩ : syracuseStep 101546237 = 38079839) B38079839
theorem B67697491 : Blo 2085435 67697491 := bstep (se 1 (by rfl) ⟨50773118, by rfl⟩ : syracuseStep 67697491 = 101546237) B101546237
theorem B90263321 : Blo 2085435 90263321 := bstep (se 2 (by rfl) ⟨33848745, by rfl⟩ : syracuseStep 90263321 = 67697491) B67697491
theorem B60175547 : Blo 2085435 60175547 := bstep (se 1 (by rfl) ⟨45131660, by rfl⟩ : syracuseStep 60175547 = 90263321) B90263321
theorem B40117031 : Blo 2085435 40117031 := bstep (se 1 (by rfl) ⟨30087773, by rfl⟩ : syracuseStep 40117031 = 60175547) B60175547
theorem B26744687 : Blo 2085435 26744687 := bstep (se 1 (by rfl) ⟨20058515, by rfl⟩ : syracuseStep 26744687 = 40117031) B40117031
theorem B17829791 : Blo 2085435 17829791 := bstep (se 1 (by rfl) ⟨13372343, by rfl⟩ : syracuseStep 17829791 = 26744687) B26744687
theorem B11886527 : Blo 2085435 11886527 := bstep (se 1 (by rfl) ⟨8914895, by rfl⟩ : syracuseStep 11886527 = 17829791) B17829791
theorem B7924351 : Blo 2085435 7924351 := bstep (se 1 (by rfl) ⟨5943263, by rfl⟩ : syracuseStep 7924351 = 11886527) B11886527
theorem B10565801 : Blo 2085435 10565801 := bstep (se 2 (by rfl) ⟨3962175, by rfl⟩ : syracuseStep 10565801 = 7924351) B7924351
theorem B7043867 : Blo 2085435 7043867 := bstep (se 1 (by rfl) ⟨5282900, by rfl⟩ : syracuseStep 7043867 = 10565801) B10565801
theorem B4695911 : Blo 2085435 4695911 := bstep (se 1 (by rfl) ⟨3521933, by rfl⟩ : syracuseStep 4695911 = 7043867) B7043867
theorem B3130607 : Blo 2085435 3130607 := bstep (se 1 (by rfl) ⟨2347955, by rfl⟩ : syracuseStep 3130607 = 4695911) B4695911
theorem B2087071 : Blo 2085435 2087071 := bstep (se 1 (by rfl) ⟨1565303, by rfl⟩ : syracuseStep 2087071 = 3130607) B3130607
theorem B3130613 : Blo 2085435 3130613 := bbase (se 5 (by rfl) ⟨146747, by rfl⟩ : syracuseStep 3130613 = 293495) (by norm_num)
theorem B2087075 : Blo 2085435 2087075 := bstep (se 1 (by rfl) ⟨1565306, by rfl⟩ : syracuseStep 2087075 = 3130613) B3130613
theorem B5083069 : Blo 2085435 5083069 := bbase (se 3 (by rfl) ⟨953075, by rfl⟩ : syracuseStep 5083069 = 1906151) (by norm_num)
theorem B6777425 : Blo 2085435 6777425 := bstep (se 2 (by rfl) ⟨2541534, by rfl⟩ : syracuseStep 6777425 = 5083069) B5083069
theorem B4518283 : Blo 2085435 4518283 := bstep (se 1 (by rfl) ⟨3388712, by rfl⟩ : syracuseStep 4518283 = 6777425) B6777425
theorem B6024377 : Blo 2085435 6024377 := bstep (se 2 (by rfl) ⟨2259141, by rfl⟩ : syracuseStep 6024377 = 4518283) B4518283
theorem B4016251 : Blo 2085435 4016251 := bstep (se 1 (by rfl) ⟨3012188, by rfl⟩ : syracuseStep 4016251 = 6024377) B6024377
theorem B5355001 : Blo 2085435 5355001 := bstep (se 2 (by rfl) ⟨2008125, by rfl⟩ : syracuseStep 5355001 = 4016251) B4016251
theorem B7140001 : Blo 2085435 7140001 := bstep (se 2 (by rfl) ⟨2677500, by rfl⟩ : syracuseStep 7140001 = 5355001) B5355001
theorem B9520001 : Blo 2085435 9520001 := bstep (se 2 (by rfl) ⟨3570000, by rfl⟩ : syracuseStep 9520001 = 7140001) B7140001
theorem B6346667 : Blo 2085435 6346667 := bstep (se 1 (by rfl) ⟨4760000, by rfl⟩ : syracuseStep 6346667 = 9520001) B9520001
theorem B4231111 : Blo 2085435 4231111 := bstep (se 1 (by rfl) ⟨3173333, by rfl⟩ : syracuseStep 4231111 = 6346667) B6346667
theorem B5641481 : Blo 2085435 5641481 := bstep (se 2 (by rfl) ⟨2115555, by rfl⟩ : syracuseStep 5641481 = 4231111) B4231111
theorem B3760987 : Blo 2085435 3760987 := bstep (se 1 (by rfl) ⟨2820740, by rfl⟩ : syracuseStep 3760987 = 5641481) B5641481
theorem B5014649 : Blo 2085435 5014649 := bstep (se 2 (by rfl) ⟨1880493, by rfl⟩ : syracuseStep 5014649 = 3760987) B3760987
theorem B13372397 : Blo 2085435 13372397 := bstep (se 3 (by rfl) ⟨2507324, by rfl⟩ : syracuseStep 13372397 = 5014649) B5014649
theorem B8914931 : Blo 2085435 8914931 := bstep (se 1 (by rfl) ⟨6686198, by rfl⟩ : syracuseStep 8914931 = 13372397) B13372397
theorem B5943287 : Blo 2085435 5943287 := bstep (se 1 (by rfl) ⟨4457465, by rfl⟩ : syracuseStep 5943287 = 8914931) B8914931
theorem B3962191 : Blo 2085435 3962191 := bstep (se 1 (by rfl) ⟨2971643, by rfl⟩ : syracuseStep 3962191 = 5943287) B5943287
theorem B5282921 : Blo 2085435 5282921 := bstep (se 2 (by rfl) ⟨1981095, by rfl⟩ : syracuseStep 5282921 = 3962191) B3962191
theorem B3521947 : Blo 2085435 3521947 := bstep (se 1 (by rfl) ⟨2641460, by rfl⟩ : syracuseStep 3521947 = 5282921) B5282921
theorem B4695929 : Blo 2085435 4695929 := bstep (se 2 (by rfl) ⟨1760973, by rfl⟩ : syracuseStep 4695929 = 3521947) B3521947
theorem B3130619 : Blo 2085435 3130619 := bstep (se 1 (by rfl) ⟨2347964, by rfl⟩ : syracuseStep 3130619 = 4695929) B4695929
theorem B2087079 : Blo 2085435 2087079 := bstep (se 1 (by rfl) ⟨1565309, by rfl⟩ : syracuseStep 2087079 = 3130619) B3130619
theorem B2347969 : Blo 2085435 2347969 := bbase (se 2 (by rfl) ⟨880488, by rfl⟩ : syracuseStep 2347969 = 1760977) (by norm_num)
theorem B3130625 : Blo 2085435 3130625 := bstep (se 2 (by rfl) ⟨1173984, by rfl⟩ : syracuseStep 3130625 = 2347969) B2347969
theorem B2087083 : Blo 2085435 2087083 := bstep (se 1 (by rfl) ⟨1565312, by rfl⟩ : syracuseStep 2087083 = 3130625) B3130625
theorem B5282941 : Blo 2085435 5282941 := bbase (se 3 (by rfl) ⟨990551, by rfl⟩ : syracuseStep 5282941 = 1981103) (by norm_num)
theorem B7043921 : Blo 2085435 7043921 := bstep (se 2 (by rfl) ⟨2641470, by rfl⟩ : syracuseStep 7043921 = 5282941) B5282941
theorem B4695947 : Blo 2085435 4695947 := bstep (se 1 (by rfl) ⟨3521960, by rfl⟩ : syracuseStep 4695947 = 7043921) B7043921
theorem B3130631 : Blo 2085435 3130631 := bstep (se 1 (by rfl) ⟨2347973, by rfl⟩ : syracuseStep 3130631 = 4695947) B4695947
theorem B2087087 : Blo 2085435 2087087 := bstep (se 1 (by rfl) ⟨1565315, by rfl⟩ : syracuseStep 2087087 = 3130631) B3130631
theorem B3130637 : Blo 2085435 3130637 := bbase (se 3 (by rfl) ⟨586994, by rfl⟩ : syracuseStep 3130637 = 1173989) (by norm_num)
theorem B2087091 : Blo 2085435 2087091 := bstep (se 1 (by rfl) ⟨1565318, by rfl⟩ : syracuseStep 2087091 = 3130637) B3130637
theorem B4695965 : Blo 2085435 4695965 := bbase (se 3 (by rfl) ⟨880493, by rfl⟩ : syracuseStep 4695965 = 1760987) (by norm_num)
theorem B3130643 : Blo 2085435 3130643 := bstep (se 1 (by rfl) ⟨2347982, by rfl⟩ : syracuseStep 3130643 = 4695965) B4695965
theorem B2087095 : Blo 2085435 2087095 := bstep (se 1 (by rfl) ⟨1565321, by rfl⟩ : syracuseStep 2087095 = 3130643) B3130643
theorem B3521981 : Blo 2085435 3521981 := bbase (se 3 (by rfl) ⟨660371, by rfl⟩ : syracuseStep 3521981 = 1320743) (by norm_num)
theorem B2347987 : Blo 2085435 2347987 := bstep (se 1 (by rfl) ⟨1760990, by rfl⟩ : syracuseStep 2347987 = 3521981) B3521981
theorem B3130649 : Blo 2085435 3130649 := bstep (se 2 (by rfl) ⟨1173993, by rfl⟩ : syracuseStep 3130649 = 2347987) B2347987
theorem B2087099 : Blo 2085435 2087099 := bstep (se 1 (by rfl) ⟨1565324, by rfl⟩ : syracuseStep 2087099 = 3130649) B3130649
theorem B11886709 : Blo 2085435 11886709 := bbase (se 5 (by rfl) ⟨557189, by rfl⟩ : syracuseStep 11886709 = 1114379) (by norm_num)
theorem B15848945 : Blo 2085435 15848945 := bstep (se 2 (by rfl) ⟨5943354, by rfl⟩ : syracuseStep 15848945 = 11886709) B11886709
theorem B10565963 : Blo 2085435 10565963 := bstep (se 1 (by rfl) ⟨7924472, by rfl⟩ : syracuseStep 10565963 = 15848945) B15848945
theorem B7043975 : Blo 2085435 7043975 := bstep (se 1 (by rfl) ⟨5282981, by rfl⟩ : syracuseStep 7043975 = 10565963) B10565963
theorem B4695983 : Blo 2085435 4695983 := bstep (se 1 (by rfl) ⟨3521987, by rfl⟩ : syracuseStep 4695983 = 7043975) B7043975
theorem B3130655 : Blo 2085435 3130655 := bstep (se 1 (by rfl) ⟨2347991, by rfl⟩ : syracuseStep 3130655 = 4695983) B4695983
theorem B2087103 : Blo 2085435 2087103 := bstep (se 1 (by rfl) ⟨1565327, by rfl⟩ : syracuseStep 2087103 = 3130655) B3130655
theorem B3130661 : Blo 2085435 3130661 := bbase (se 4 (by rfl) ⟨293499, by rfl⟩ : syracuseStep 3130661 = 586999) (by norm_num)
theorem B2087107 : Blo 2085435 2087107 := bstep (se 1 (by rfl) ⟨1565330, by rfl⟩ : syracuseStep 2087107 = 3130661) B3130661
theorem B2641501 : Blo 2085435 2641501 := bbase (se 3 (by rfl) ⟨495281, by rfl⟩ : syracuseStep 2641501 = 990563) (by norm_num)
theorem B3522001 : Blo 2085435 3522001 := bstep (se 2 (by rfl) ⟨1320750, by rfl⟩ : syracuseStep 3522001 = 2641501) B2641501
theorem B4696001 : Blo 2085435 4696001 := bstep (se 2 (by rfl) ⟨1761000, by rfl⟩ : syracuseStep 4696001 = 3522001) B3522001
theorem B3130667 : Blo 2085435 3130667 := bstep (se 1 (by rfl) ⟨2348000, by rfl⟩ : syracuseStep 3130667 = 4696001) B4696001
theorem B2087111 : Blo 2085435 2087111 := bstep (se 1 (by rfl) ⟨1565333, by rfl⟩ : syracuseStep 2087111 = 3130667) B3130667
theorem B2348005 : Blo 2085435 2348005 := bbase (se 4 (by rfl) ⟨220125, by rfl⟩ : syracuseStep 2348005 = 440251) (by norm_num)
theorem B3130673 : Blo 2085435 3130673 := bstep (se 2 (by rfl) ⟨1174002, by rfl⟩ : syracuseStep 3130673 = 2348005) B2348005
theorem B2087115 : Blo 2085435 2087115 := bstep (se 1 (by rfl) ⟨1565336, by rfl⟩ : syracuseStep 2087115 = 3130673) B3130673
theorem B5641589 : Blo 2085435 5641589 := bbase (se 5 (by rfl) ⟨264449, by rfl⟩ : syracuseStep 5641589 = 528899) (by norm_num)
theorem B15044237 : Blo 2085435 15044237 := bstep (se 3 (by rfl) ⟨2820794, by rfl⟩ : syracuseStep 15044237 = 5641589) B5641589
theorem B10029491 : Blo 2085435 10029491 := bstep (se 1 (by rfl) ⟨7522118, by rfl⟩ : syracuseStep 10029491 = 15044237) B15044237
theorem B6686327 : Blo 2085435 6686327 := bstep (se 1 (by rfl) ⟨5014745, by rfl⟩ : syracuseStep 6686327 = 10029491) B10029491
theorem B4457551 : Blo 2085435 4457551 := bstep (se 1 (by rfl) ⟨3343163, by rfl⟩ : syracuseStep 4457551 = 6686327) B6686327
theorem B5943401 : Blo 2085435 5943401 := bstep (se 2 (by rfl) ⟨2228775, by rfl⟩ : syracuseStep 5943401 = 4457551) B4457551
theorem B3962267 : Blo 2085435 3962267 := bstep (se 1 (by rfl) ⟨2971700, by rfl⟩ : syracuseStep 3962267 = 5943401) B5943401
theorem B2641511 : Blo 2085435 2641511 := bstep (se 1 (by rfl) ⟨1981133, by rfl⟩ : syracuseStep 2641511 = 3962267) B3962267
theorem B7044029 : Blo 2085435 7044029 := bstep (se 3 (by rfl) ⟨1320755, by rfl⟩ : syracuseStep 7044029 = 2641511) B2641511
theorem B4696019 : Blo 2085435 4696019 := bstep (se 1 (by rfl) ⟨3522014, by rfl⟩ : syracuseStep 4696019 = 7044029) B7044029
theorem B3130679 : Blo 2085435 3130679 := bstep (se 1 (by rfl) ⟨2348009, by rfl⟩ : syracuseStep 3130679 = 4696019) B4696019
theorem B2087119 : Blo 2085435 2087119 := bstep (se 1 (by rfl) ⟨1565339, by rfl⟩ : syracuseStep 2087119 = 3130679) B3130679
theorem B3130685 : Blo 2085435 3130685 := bbase (se 3 (by rfl) ⟨587003, by rfl⟩ : syracuseStep 3130685 = 1174007) (by norm_num)
theorem B2087123 : Blo 2085435 2087123 := bstep (se 1 (by rfl) ⟨1565342, by rfl⟩ : syracuseStep 2087123 = 3130685) B3130685
theorem B4696037 : Blo 2085435 4696037 := bbase (se 4 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 4696037 = 880507) (by norm_num)
theorem B3130691 : Blo 2085435 3130691 := bstep (se 1 (by rfl) ⟨2348018, by rfl⟩ : syracuseStep 3130691 = 4696037) B4696037
theorem B2087127 : Blo 2085435 2087127 := bstep (se 1 (by rfl) ⟨1565345, by rfl⟩ : syracuseStep 2087127 = 3130691) B3130691
theorem B5283053 : Blo 2085435 5283053 := bbase (se 3 (by rfl) ⟨990572, by rfl⟩ : syracuseStep 5283053 = 1981145) (by norm_num)
theorem B3522035 : Blo 2085435 3522035 := bstep (se 1 (by rfl) ⟨2641526, by rfl⟩ : syracuseStep 3522035 = 5283053) B5283053
theorem B2348023 : Blo 2085435 2348023 := bstep (se 1 (by rfl) ⟨1761017, by rfl⟩ : syracuseStep 2348023 = 3522035) B3522035
theorem B3130697 : Blo 2085435 3130697 := bstep (se 2 (by rfl) ⟨1174011, by rfl⟩ : syracuseStep 3130697 = 2348023) B2348023
theorem B2087131 : Blo 2085435 2087131 := bstep (se 1 (by rfl) ⟨1565348, by rfl⟩ : syracuseStep 2087131 = 3130697) B3130697
theorem B3343189 : Blo 2085435 3343189 := bbase (se 9 (by rfl) ⟨9794, by rfl⟩ : syracuseStep 3343189 = 19589) (by norm_num)
theorem B4457585 : Blo 2085435 4457585 := bstep (se 2 (by rfl) ⟨1671594, by rfl⟩ : syracuseStep 4457585 = 3343189) B3343189
theorem B2971723 : Blo 2085435 2971723 := bstep (se 1 (by rfl) ⟨2228792, by rfl⟩ : syracuseStep 2971723 = 4457585) B4457585
theorem B3962297 : Blo 2085435 3962297 := bstep (se 2 (by rfl) ⟨1485861, by rfl⟩ : syracuseStep 3962297 = 2971723) B2971723
theorem B10566125 : Blo 2085435 10566125 := bstep (se 3 (by rfl) ⟨1981148, by rfl⟩ : syracuseStep 10566125 = 3962297) B3962297
theorem B7044083 : Blo 2085435 7044083 := bstep (se 1 (by rfl) ⟨5283062, by rfl⟩ : syracuseStep 7044083 = 10566125) B10566125
theorem B4696055 : Blo 2085435 4696055 := bstep (se 1 (by rfl) ⟨3522041, by rfl⟩ : syracuseStep 4696055 = 7044083) B7044083
theorem B3130703 : Blo 2085435 3130703 := bstep (se 1 (by rfl) ⟨2348027, by rfl⟩ : syracuseStep 3130703 = 4696055) B4696055
theorem B2087135 : Blo 2085435 2087135 := bstep (se 1 (by rfl) ⟨1565351, by rfl⟩ : syracuseStep 2087135 = 3130703) B3130703
theorem B3130709 : Blo 2085435 3130709 := bbase (se 12 (by rfl) ⟨1146, by rfl⟩ : syracuseStep 3130709 = 2293) (by norm_num)
theorem B2087139 : Blo 2085435 2087139 := bstep (se 1 (by rfl) ⟨1565354, by rfl⟩ : syracuseStep 2087139 = 3130709) B3130709
theorem B2228801 : Blo 2085435 2228801 := bbase (se 2 (by rfl) ⟨835800, by rfl⟩ : syracuseStep 2228801 = 1671601) (by norm_num)
theorem B5943469 : Blo 2085435 5943469 := bstep (se 3 (by rfl) ⟨1114400, by rfl⟩ : syracuseStep 5943469 = 2228801) B2228801
theorem B7924625 : Blo 2085435 7924625 := bstep (se 2 (by rfl) ⟨2971734, by rfl⟩ : syracuseStep 7924625 = 5943469) B5943469
theorem B5283083 : Blo 2085435 5283083 := bstep (se 1 (by rfl) ⟨3962312, by rfl⟩ : syracuseStep 5283083 = 7924625) B7924625
theorem B3522055 : Blo 2085435 3522055 := bstep (se 1 (by rfl) ⟨2641541, by rfl⟩ : syracuseStep 3522055 = 5283083) B5283083
theorem B4696073 : Blo 2085435 4696073 := bstep (se 2 (by rfl) ⟨1761027, by rfl⟩ : syracuseStep 4696073 = 3522055) B3522055
theorem B3130715 : Blo 2085435 3130715 := bstep (se 1 (by rfl) ⟨2348036, by rfl⟩ : syracuseStep 3130715 = 4696073) B4696073
theorem B2087143 : Blo 2085435 2087143 := bstep (se 1 (by rfl) ⟨1565357, by rfl⟩ : syracuseStep 2087143 = 3130715) B3130715
theorem B2348041 : Blo 2085435 2348041 := bbase (se 2 (by rfl) ⟨880515, by rfl⟩ : syracuseStep 2348041 = 1761031) (by norm_num)
theorem B3130721 : Blo 2085435 3130721 := bstep (se 2 (by rfl) ⟨1174020, by rfl⟩ : syracuseStep 3130721 = 2348041) B2348041
theorem B2087147 : Blo 2085435 2087147 := bstep (se 1 (by rfl) ⟨1565360, by rfl⟩ : syracuseStep 2087147 = 3130721) B3130721
theorem B20059285 : Blo 2085435 20059285 := bbase (se 6 (by rfl) ⟨470139, by rfl⟩ : syracuseStep 20059285 = 940279) (by norm_num)
theorem B26745713 : Blo 2085435 26745713 := bstep (se 2 (by rfl) ⟨10029642, by rfl⟩ : syracuseStep 26745713 = 20059285) B20059285
theorem B17830475 : Blo 2085435 17830475 := bstep (se 1 (by rfl) ⟨13372856, by rfl⟩ : syracuseStep 17830475 = 26745713) B26745713
theorem B11886983 : Blo 2085435 11886983 := bstep (se 1 (by rfl) ⟨8915237, by rfl⟩ : syracuseStep 11886983 = 17830475) B17830475
theorem B7924655 : Blo 2085435 7924655 := bstep (se 1 (by rfl) ⟨5943491, by rfl⟩ : syracuseStep 7924655 = 11886983) B11886983
theorem B5283103 : Blo 2085435 5283103 := bstep (se 1 (by rfl) ⟨3962327, by rfl⟩ : syracuseStep 5283103 = 7924655) B7924655
theorem B7044137 : Blo 2085435 7044137 := bstep (se 2 (by rfl) ⟨2641551, by rfl⟩ : syracuseStep 7044137 = 5283103) B5283103
theorem B4696091 : Blo 2085435 4696091 := bstep (se 1 (by rfl) ⟨3522068, by rfl⟩ : syracuseStep 4696091 = 7044137) B7044137
theorem B3130727 : Blo 2085435 3130727 := bstep (se 1 (by rfl) ⟨2348045, by rfl⟩ : syracuseStep 3130727 = 4696091) B4696091
theorem B2087151 : Blo 2085435 2087151 := bstep (se 1 (by rfl) ⟨1565363, by rfl⟩ : syracuseStep 2087151 = 3130727) B3130727
theorem B3130733 : Blo 2085435 3130733 := bbase (se 3 (by rfl) ⟨587012, by rfl⟩ : syracuseStep 3130733 = 1174025) (by norm_num)
theorem B2087155 : Blo 2085435 2087155 := bstep (se 1 (by rfl) ⟨1565366, by rfl⟩ : syracuseStep 2087155 = 3130733) B3130733
theorem B4696109 : Blo 2085435 4696109 := bbase (se 3 (by rfl) ⟨880520, by rfl⟩ : syracuseStep 4696109 = 1761041) (by norm_num)
theorem B3130739 : Blo 2085435 3130739 := bstep (se 1 (by rfl) ⟨2348054, by rfl⟩ : syracuseStep 3130739 = 4696109) B4696109
theorem B2087159 : Blo 2085435 2087159 := bstep (se 1 (by rfl) ⟨1565369, by rfl⟩ : syracuseStep 2087159 = 3130739) B3130739
theorem B3173461 : Blo 2085435 3173461 := bbase (se 8 (by rfl) ⟨18594, by rfl⟩ : syracuseStep 3173461 = 37189) (by norm_num)
theorem B16925125 : Blo 2085435 16925125 := bstep (se 4 (by rfl) ⟨1586730, by rfl⟩ : syracuseStep 16925125 = 3173461) B3173461
theorem B22566833 : Blo 2085435 22566833 := bstep (se 2 (by rfl) ⟨8462562, by rfl⟩ : syracuseStep 22566833 = 16925125) B16925125
theorem B15044555 : Blo 2085435 15044555 := bstep (se 1 (by rfl) ⟨11283416, by rfl⟩ : syracuseStep 15044555 = 22566833) B22566833
theorem B10029703 : Blo 2085435 10029703 := bstep (se 1 (by rfl) ⟨7522277, by rfl⟩ : syracuseStep 10029703 = 15044555) B15044555
theorem B13372937 : Blo 2085435 13372937 := bstep (se 2 (by rfl) ⟨5014851, by rfl⟩ : syracuseStep 13372937 = 10029703) B10029703
theorem B8915291 : Blo 2085435 8915291 := bstep (se 1 (by rfl) ⟨6686468, by rfl⟩ : syracuseStep 8915291 = 13372937) B13372937
theorem B5943527 : Blo 2085435 5943527 := bstep (se 1 (by rfl) ⟨4457645, by rfl⟩ : syracuseStep 5943527 = 8915291) B8915291
theorem B3962351 : Blo 2085435 3962351 := bstep (se 1 (by rfl) ⟨2971763, by rfl⟩ : syracuseStep 3962351 = 5943527) B5943527
theorem B2641567 : Blo 2085435 2641567 := bstep (se 1 (by rfl) ⟨1981175, by rfl⟩ : syracuseStep 2641567 = 3962351) B3962351
theorem B3522089 : Blo 2085435 3522089 := bstep (se 2 (by rfl) ⟨1320783, by rfl⟩ : syracuseStep 3522089 = 2641567) B2641567
theorem B2348059 : Blo 2085435 2348059 := bstep (se 1 (by rfl) ⟨1761044, by rfl⟩ : syracuseStep 2348059 = 3522089) B3522089
theorem B3130745 : Blo 2085435 3130745 := bstep (se 2 (by rfl) ⟨1174029, by rfl⟩ : syracuseStep 3130745 = 2348059) B2348059
theorem B2087163 : Blo 2085435 2087163 := bstep (se 1 (by rfl) ⟨1565372, by rfl⟩ : syracuseStep 2087163 = 3130745) B3130745
theorem B22566869 : Blo 2085435 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B15044579 : Blo 2085435 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B10029719 : Blo 2085435 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B6686479 : Blo 2085435 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B35661221 : Blo 2085435 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B23774147 : Blo 2085435 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B15849431 : Blo 2085435 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B10566287 : Blo 2085435 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B7044191 : Blo 2085435 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B4696127 : Blo 2085435 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B3130751 : Blo 2085435 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B2087167 : Blo 2085435 2087167 := bstep (se 1 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 2087167 = 3130751) B3130751
theorem B3130757 : Blo 2085435 3130757 := bbase (se 4 (by rfl) ⟨293508, by rfl⟩ : syracuseStep 3130757 = 587017) (by norm_num)
theorem B2087171 : Blo 2085435 2087171 := bstep (se 1 (by rfl) ⟨1565378, by rfl⟩ : syracuseStep 2087171 = 3130757) B3130757
theorem B3522109 : Blo 2085435 3522109 := bbase (se 3 (by rfl) ⟨660395, by rfl⟩ : syracuseStep 3522109 = 1320791) (by norm_num)
theorem B4696145 : Blo 2085435 4696145 := bstep (se 2 (by rfl) ⟨1761054, by rfl⟩ : syracuseStep 4696145 = 3522109) B3522109
theorem B3130763 : Blo 2085435 3130763 := bstep (se 1 (by rfl) ⟨2348072, by rfl⟩ : syracuseStep 3130763 = 4696145) B4696145
theorem B2087175 : Blo 2085435 2087175 := bstep (se 1 (by rfl) ⟨1565381, by rfl⟩ : syracuseStep 2087175 = 3130763) B3130763
theorem B2348077 : Blo 2085435 2348077 := bbase (se 3 (by rfl) ⟨440264, by rfl⟩ : syracuseStep 2348077 = 880529) (by norm_num)
theorem B3130769 : Blo 2085435 3130769 := bstep (se 2 (by rfl) ⟨1174038, by rfl⟩ : syracuseStep 3130769 = 2348077) B2348077
theorem B2087179 : Blo 2085435 2087179 := bstep (se 1 (by rfl) ⟨1565384, by rfl⟩ : syracuseStep 2087179 = 3130769) B3130769
theorem B7044245 : Blo 2085435 7044245 := bbase (se 6 (by rfl) ⟨165099, by rfl⟩ : syracuseStep 7044245 = 330199) (by norm_num)
theorem B4696163 : Blo 2085435 4696163 := bstep (se 1 (by rfl) ⟨3522122, by rfl⟩ : syracuseStep 4696163 = 7044245) B7044245
theorem B3130775 : Blo 2085435 3130775 := bstep (se 1 (by rfl) ⟨2348081, by rfl⟩ : syracuseStep 3130775 = 4696163) B4696163
theorem B2087183 : Blo 2085435 2087183 := bstep (se 1 (by rfl) ⟨1565387, by rfl⟩ : syracuseStep 2087183 = 3130775) B3130775
theorem B3130781 : Blo 2085435 3130781 := bbase (se 3 (by rfl) ⟨587021, by rfl⟩ : syracuseStep 3130781 = 1174043) (by norm_num)
theorem B2087187 : Blo 2085435 2087187 := bstep (se 1 (by rfl) ⟨1565390, by rfl⟩ : syracuseStep 2087187 = 3130781) B3130781
theorem B4696181 : Blo 2085435 4696181 := bbase (se 5 (by rfl) ⟨220133, by rfl⟩ : syracuseStep 4696181 = 440267) (by norm_num)
theorem B3130787 : Blo 2085435 3130787 := bstep (se 1 (by rfl) ⟨2348090, by rfl⟩ : syracuseStep 3130787 = 4696181) B4696181
theorem B2087191 : Blo 2085435 2087191 := bstep (se 1 (by rfl) ⟨1565393, by rfl⟩ : syracuseStep 2087191 = 3130787) B3130787
theorem B3343285 : Blo 2085435 3343285 := bbase (se 5 (by rfl) ⟨156716, by rfl⟩ : syracuseStep 3343285 = 313433) (by norm_num)
theorem B17830853 : Blo 2085435 17830853 := bstep (se 4 (by rfl) ⟨1671642, by rfl⟩ : syracuseStep 17830853 = 3343285) B3343285
theorem B11887235 : Blo 2085435 11887235 := bstep (se 1 (by rfl) ⟨8915426, by rfl⟩ : syracuseStep 11887235 = 17830853) B17830853
theorem B7924823 : Blo 2085435 7924823 := bstep (se 1 (by rfl) ⟨5943617, by rfl⟩ : syracuseStep 7924823 = 11887235) B11887235
theorem B5283215 : Blo 2085435 5283215 := bstep (se 1 (by rfl) ⟨3962411, by rfl⟩ : syracuseStep 5283215 = 7924823) B7924823
theorem B3522143 : Blo 2085435 3522143 := bstep (se 1 (by rfl) ⟨2641607, by rfl⟩ : syracuseStep 3522143 = 5283215) B5283215
theorem B2348095 : Blo 2085435 2348095 := bstep (se 1 (by rfl) ⟨1761071, by rfl⟩ : syracuseStep 2348095 = 3522143) B3522143
theorem B3130793 : Blo 2085435 3130793 := bstep (se 2 (by rfl) ⟨1174047, by rfl⟩ : syracuseStep 3130793 = 2348095) B2348095
theorem B2087195 : Blo 2085435 2087195 := bstep (se 1 (by rfl) ⟨1565396, by rfl⟩ : syracuseStep 2087195 = 3130793) B3130793
theorem B7924837 : Blo 2085435 7924837 := bbase (se 4 (by rfl) ⟨742953, by rfl⟩ : syracuseStep 7924837 = 1485907) (by norm_num)
theorem B10566449 : Blo 2085435 10566449 := bstep (se 2 (by rfl) ⟨3962418, by rfl⟩ : syracuseStep 10566449 = 7924837) B7924837
theorem B7044299 : Blo 2085435 7044299 := bstep (se 1 (by rfl) ⟨5283224, by rfl⟩ : syracuseStep 7044299 = 10566449) B10566449
theorem B4696199 : Blo 2085435 4696199 := bstep (se 1 (by rfl) ⟨3522149, by rfl⟩ : syracuseStep 4696199 = 7044299) B7044299
theorem B3130799 : Blo 2085435 3130799 := bstep (se 1 (by rfl) ⟨2348099, by rfl⟩ : syracuseStep 3130799 = 4696199) B4696199
theorem B2087199 : Blo 2085435 2087199 := bstep (se 1 (by rfl) ⟨1565399, by rfl⟩ : syracuseStep 2087199 = 3130799) B3130799
theorem B3130805 : Blo 2085435 3130805 := bbase (se 5 (by rfl) ⟨146756, by rfl⟩ : syracuseStep 3130805 = 293513) (by norm_num)
theorem B2087203 : Blo 2085435 2087203 := bstep (se 1 (by rfl) ⟨1565402, by rfl⟩ : syracuseStep 2087203 = 3130805) B3130805
theorem B5283245 : Blo 2085435 5283245 := bbase (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) (by norm_num)
theorem B3522163 : Blo 2085435 3522163 := bstep (se 1 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 3522163 = 5283245) B5283245
theorem B4696217 : Blo 2085435 4696217 := bstep (se 2 (by rfl) ⟨1761081, by rfl⟩ : syracuseStep 4696217 = 3522163) B3522163
theorem B3130811 : Blo 2085435 3130811 := bstep (se 1 (by rfl) ⟨2348108, by rfl⟩ : syracuseStep 3130811 = 4696217) B4696217
theorem B2087207 : Blo 2085435 2087207 := bstep (se 1 (by rfl) ⟨1565405, by rfl⟩ : syracuseStep 2087207 = 3130811) B3130811
theorem B2348113 : Blo 2085435 2348113 := bbase (se 2 (by rfl) ⟨880542, by rfl⟩ : syracuseStep 2348113 = 1761085) (by norm_num)
theorem B3130817 : Blo 2085435 3130817 := bstep (se 2 (by rfl) ⟨1174056, by rfl⟩ : syracuseStep 3130817 = 2348113) B2348113
theorem B2087211 : Blo 2085435 2087211 := bstep (se 1 (by rfl) ⟨1565408, by rfl⟩ : syracuseStep 2087211 = 3130817) B3130817
theorem B2971837 : Blo 2085435 2971837 := bbase (se 3 (by rfl) ⟨557219, by rfl⟩ : syracuseStep 2971837 = 1114439) (by norm_num)
theorem B3962449 : Blo 2085435 3962449 := bstep (se 2 (by rfl) ⟨1485918, by rfl⟩ : syracuseStep 3962449 = 2971837) B2971837
theorem B5283265 : Blo 2085435 5283265 := bstep (se 2 (by rfl) ⟨1981224, by rfl⟩ : syracuseStep 5283265 = 3962449) B3962449
theorem B7044353 : Blo 2085435 7044353 := bstep (se 2 (by rfl) ⟨2641632, by rfl⟩ : syracuseStep 7044353 = 5283265) B5283265
theorem B4696235 : Blo 2085435 4696235 := bstep (se 1 (by rfl) ⟨3522176, by rfl⟩ : syracuseStep 4696235 = 7044353) B7044353
theorem B3130823 : Blo 2085435 3130823 := bstep (se 1 (by rfl) ⟨2348117, by rfl⟩ : syracuseStep 3130823 = 4696235) B4696235
theorem B2087215 : Blo 2085435 2087215 := bstep (se 1 (by rfl) ⟨1565411, by rfl⟩ : syracuseStep 2087215 = 3130823) B3130823
theorem B3130829 : Blo 2085435 3130829 := bbase (se 3 (by rfl) ⟨587030, by rfl⟩ : syracuseStep 3130829 = 1174061) (by norm_num)
theorem B2087219 : Blo 2085435 2087219 := bstep (se 1 (by rfl) ⟨1565414, by rfl⟩ : syracuseStep 2087219 = 3130829) B3130829
theorem B4696253 : Blo 2085435 4696253 := bbase (se 3 (by rfl) ⟨880547, by rfl⟩ : syracuseStep 4696253 = 1761095) (by norm_num)
theorem B3130835 : Blo 2085435 3130835 := bstep (se 1 (by rfl) ⟨2348126, by rfl⟩ : syracuseStep 3130835 = 4696253) B4696253
theorem B2087223 : Blo 2085435 2087223 := bstep (se 1 (by rfl) ⟨1565417, by rfl⟩ : syracuseStep 2087223 = 3130835) B3130835
theorem B3522197 : Blo 2085435 3522197 := bbase (se 6 (by rfl) ⟨82551, by rfl⟩ : syracuseStep 3522197 = 165103) (by norm_num)
theorem B2348131 : Blo 2085435 2348131 := bstep (se 1 (by rfl) ⟨1761098, by rfl⟩ : syracuseStep 2348131 = 3522197) B3522197
theorem B3130841 : Blo 2085435 3130841 := bstep (se 2 (by rfl) ⟨1174065, by rfl⟩ : syracuseStep 3130841 = 2348131) B2348131
theorem B2087227 : Blo 2085435 2087227 := bstep (se 1 (by rfl) ⟨1565420, by rfl⟩ : syracuseStep 2087227 = 3130841) B3130841
theorem B2115709 : Blo 2085435 2115709 := bbase (se 3 (by rfl) ⟨396695, by rfl⟩ : syracuseStep 2115709 = 793391) (by norm_num)
theorem B11283781 : Blo 2085435 11283781 := bstep (se 4 (by rfl) ⟨1057854, by rfl⟩ : syracuseStep 11283781 = 2115709) B2115709
theorem B15045041 : Blo 2085435 15045041 := bstep (se 2 (by rfl) ⟨5641890, by rfl⟩ : syracuseStep 15045041 = 11283781) B11283781
theorem B10030027 : Blo 2085435 10030027 := bstep (se 1 (by rfl) ⟨7522520, by rfl⟩ : syracuseStep 10030027 = 15045041) B15045041
theorem B13373369 : Blo 2085435 13373369 := bstep (se 2 (by rfl) ⟨5015013, by rfl⟩ : syracuseStep 13373369 = 10030027) B10030027
theorem B8915579 : Blo 2085435 8915579 := bstep (se 1 (by rfl) ⟨6686684, by rfl⟩ : syracuseStep 8915579 = 13373369) B13373369
theorem B5943719 : Blo 2085435 5943719 := bstep (se 1 (by rfl) ⟨4457789, by rfl⟩ : syracuseStep 5943719 = 8915579) B8915579
theorem B15849917 : Blo 2085435 15849917 := bstep (se 3 (by rfl) ⟨2971859, by rfl⟩ : syracuseStep 15849917 = 5943719) B5943719
theorem B10566611 : Blo 2085435 10566611 := bstep (se 1 (by rfl) ⟨7924958, by rfl⟩ : syracuseStep 10566611 = 15849917) B15849917
theorem B7044407 : Blo 2085435 7044407 := bstep (se 1 (by rfl) ⟨5283305, by rfl⟩ : syracuseStep 7044407 = 10566611) B10566611
theorem B4696271 : Blo 2085435 4696271 := bstep (se 1 (by rfl) ⟨3522203, by rfl⟩ : syracuseStep 4696271 = 7044407) B7044407
theorem B3130847 : Blo 2085435 3130847 := bstep (se 1 (by rfl) ⟨2348135, by rfl⟩ : syracuseStep 3130847 = 4696271) B4696271
theorem B2087231 : Blo 2085435 2087231 := bstep (se 1 (by rfl) ⟨1565423, by rfl⟩ : syracuseStep 2087231 = 3130847) B3130847
theorem B3130853 : Blo 2085435 3130853 := bbase (se 4 (by rfl) ⟨293517, by rfl⟩ : syracuseStep 3130853 = 587035) (by norm_num)
theorem B2087235 : Blo 2085435 2087235 := bstep (se 1 (by rfl) ⟨1565426, by rfl⟩ : syracuseStep 2087235 = 3130853) B3130853
theorem B2677705 : Blo 2085435 2677705 := bbase (se 2 (by rfl) ⟨1004139, by rfl⟩ : syracuseStep 2677705 = 2008279) (by norm_num)
theorem B14281093 : Blo 2085435 14281093 := bstep (se 4 (by rfl) ⟨1338852, by rfl⟩ : syracuseStep 14281093 = 2677705) B2677705
theorem B76165829 : Blo 2085435 76165829 := bstep (se 4 (by rfl) ⟨7140546, by rfl⟩ : syracuseStep 76165829 = 14281093) B14281093
theorem B50777219 : Blo 2085435 50777219 := bstep (se 1 (by rfl) ⟨38082914, by rfl⟩ : syracuseStep 50777219 = 76165829) B76165829
theorem B33851479 : Blo 2085435 33851479 := bstep (se 1 (by rfl) ⟨25388609, by rfl⟩ : syracuseStep 33851479 = 50777219) B50777219
theorem B45135305 : Blo 2085435 45135305 := bstep (se 2 (by rfl) ⟨16925739, by rfl⟩ : syracuseStep 45135305 = 33851479) B33851479
theorem B30090203 : Blo 2085435 30090203 := bstep (se 1 (by rfl) ⟨22567652, by rfl⟩ : syracuseStep 30090203 = 45135305) B45135305
theorem B20060135 : Blo 2085435 20060135 := bstep (se 1 (by rfl) ⟨15045101, by rfl⟩ : syracuseStep 20060135 = 30090203) B30090203
theorem B13373423 : Blo 2085435 13373423 := bstep (se 1 (by rfl) ⟨10030067, by rfl⟩ : syracuseStep 13373423 = 20060135) B20060135
theorem B8915615 : Blo 2085435 8915615 := bstep (se 1 (by rfl) ⟨6686711, by rfl⟩ : syracuseStep 8915615 = 13373423) B13373423
theorem B5943743 : Blo 2085435 5943743 := bstep (se 1 (by rfl) ⟨4457807, by rfl⟩ : syracuseStep 5943743 = 8915615) B8915615
theorem B3962495 : Blo 2085435 3962495 := bstep (se 1 (by rfl) ⟨2971871, by rfl⟩ : syracuseStep 3962495 = 5943743) B5943743
theorem B2641663 : Blo 2085435 2641663 := bstep (se 1 (by rfl) ⟨1981247, by rfl⟩ : syracuseStep 2641663 = 3962495) B3962495
theorem B3522217 : Blo 2085435 3522217 := bstep (se 2 (by rfl) ⟨1320831, by rfl⟩ : syracuseStep 3522217 = 2641663) B2641663
theorem B4696289 : Blo 2085435 4696289 := bstep (se 2 (by rfl) ⟨1761108, by rfl⟩ : syracuseStep 4696289 = 3522217) B3522217
theorem B3130859 : Blo 2085435 3130859 := bstep (se 1 (by rfl) ⟨2348144, by rfl⟩ : syracuseStep 3130859 = 4696289) B4696289
theorem B2087239 : Blo 2085435 2087239 := bstep (se 1 (by rfl) ⟨1565429, by rfl⟩ : syracuseStep 2087239 = 3130859) B3130859
theorem B2348149 : Blo 2085435 2348149 := bbase (se 5 (by rfl) ⟨110069, by rfl⟩ : syracuseStep 2348149 = 220139) (by norm_num)
theorem B3130865 : Blo 2085435 3130865 := bstep (se 2 (by rfl) ⟨1174074, by rfl⟩ : syracuseStep 3130865 = 2348149) B2348149
theorem B2087243 : Blo 2085435 2087243 := bstep (se 1 (by rfl) ⟨1565432, by rfl⟩ : syracuseStep 2087243 = 3130865) B3130865
theorem B2641673 : Blo 2085435 2641673 := bbase (se 2 (by rfl) ⟨990627, by rfl⟩ : syracuseStep 2641673 = 1981255) (by norm_num)
theorem B7044461 : Blo 2085435 7044461 := bstep (se 3 (by rfl) ⟨1320836, by rfl⟩ : syracuseStep 7044461 = 2641673) B2641673
theorem B4696307 : Blo 2085435 4696307 := bstep (se 1 (by rfl) ⟨3522230, by rfl⟩ : syracuseStep 4696307 = 7044461) B7044461
theorem B3130871 : Blo 2085435 3130871 := bstep (se 1 (by rfl) ⟨2348153, by rfl⟩ : syracuseStep 3130871 = 4696307) B4696307
theorem B2087247 : Blo 2085435 2087247 := bstep (se 1 (by rfl) ⟨1565435, by rfl⟩ : syracuseStep 2087247 = 3130871) B3130871
theorem B3130877 : Blo 2085435 3130877 := bbase (se 3 (by rfl) ⟨587039, by rfl⟩ : syracuseStep 3130877 = 1174079) (by norm_num)
theorem B2087251 : Blo 2085435 2087251 := bstep (se 1 (by rfl) ⟨1565438, by rfl⟩ : syracuseStep 2087251 = 3130877) B3130877
theorem B4696325 : Blo 2085435 4696325 := bbase (se 4 (by rfl) ⟨440280, by rfl⟩ : syracuseStep 4696325 = 880561) (by norm_num)
theorem B3130883 : Blo 2085435 3130883 := bstep (se 1 (by rfl) ⟨2348162, by rfl⟩ : syracuseStep 3130883 = 4696325) B4696325
theorem B2087255 : Blo 2085435 2087255 := bstep (se 1 (by rfl) ⟨1565441, by rfl⟩ : syracuseStep 2087255 = 3130883) B3130883
theorem B3962533 : Blo 2085435 3962533 := bbase (se 4 (by rfl) ⟨371487, by rfl⟩ : syracuseStep 3962533 = 742975) (by norm_num)
theorem B5283377 : Blo 2085435 5283377 := bstep (se 2 (by rfl) ⟨1981266, by rfl⟩ : syracuseStep 5283377 = 3962533) B3962533
theorem B3522251 : Blo 2085435 3522251 := bstep (se 1 (by rfl) ⟨2641688, by rfl⟩ : syracuseStep 3522251 = 5283377) B5283377
theorem B2348167 : Blo 2085435 2348167 := bstep (se 1 (by rfl) ⟨1761125, by rfl⟩ : syracuseStep 2348167 = 3522251) B3522251
theorem B3130889 : Blo 2085435 3130889 := bstep (se 2 (by rfl) ⟨1174083, by rfl⟩ : syracuseStep 3130889 = 2348167) B2348167
theorem B2087259 : Blo 2085435 2087259 := bstep (se 1 (by rfl) ⟨1565444, by rfl⟩ : syracuseStep 2087259 = 3130889) B3130889
theorem B10566773 : Blo 2085435 10566773 := bbase (se 5 (by rfl) ⟨495317, by rfl⟩ : syracuseStep 10566773 = 990635) (by norm_num)
theorem B7044515 : Blo 2085435 7044515 := bstep (se 1 (by rfl) ⟨5283386, by rfl⟩ : syracuseStep 7044515 = 10566773) B10566773
theorem B4696343 : Blo 2085435 4696343 := bstep (se 1 (by rfl) ⟨3522257, by rfl⟩ : syracuseStep 4696343 = 7044515) B7044515
theorem B3130895 : Blo 2085435 3130895 := bstep (se 1 (by rfl) ⟨2348171, by rfl⟩ : syracuseStep 3130895 = 4696343) B4696343
theorem B2087263 : Blo 2085435 2087263 := bstep (se 1 (by rfl) ⟨1565447, by rfl⟩ : syracuseStep 2087263 = 3130895) B3130895
theorem B3130901 : Blo 2085435 3130901 := bbase (se 6 (by rfl) ⟨73380, by rfl⟩ : syracuseStep 3130901 = 146761) (by norm_num)
theorem B2087267 : Blo 2085435 2087267 := bstep (se 1 (by rfl) ⟨1565450, by rfl⟩ : syracuseStep 2087267 = 3130901) B3130901
theorem B3761333 : Blo 2085435 3761333 := bbase (se 5 (by rfl) ⟨176312, by rfl⟩ : syracuseStep 3761333 = 352625) (by norm_num)
theorem B2507555 : Blo 2085435 2507555 := bstep (se 1 (by rfl) ⟨1880666, by rfl⟩ : syracuseStep 2507555 = 3761333) B3761333
theorem B6686813 : Blo 2085435 6686813 := bstep (se 3 (by rfl) ⟨1253777, by rfl⟩ : syracuseStep 6686813 = 2507555) B2507555
theorem B17831501 : Blo 2085435 17831501 := bstep (se 3 (by rfl) ⟨3343406, by rfl⟩ : syracuseStep 17831501 = 6686813) B6686813
theorem B11887667 : Blo 2085435 11887667 := bstep (se 1 (by rfl) ⟨8915750, by rfl⟩ : syracuseStep 11887667 = 17831501) B17831501
theorem B7925111 : Blo 2085435 7925111 := bstep (se 1 (by rfl) ⟨5943833, by rfl⟩ : syracuseStep 7925111 = 11887667) B11887667
theorem B5283407 : Blo 2085435 5283407 := bstep (se 1 (by rfl) ⟨3962555, by rfl⟩ : syracuseStep 5283407 = 7925111) B7925111
theorem B3522271 : Blo 2085435 3522271 := bstep (se 1 (by rfl) ⟨2641703, by rfl⟩ : syracuseStep 3522271 = 5283407) B5283407
theorem B4696361 : Blo 2085435 4696361 := bstep (se 2 (by rfl) ⟨1761135, by rfl⟩ : syracuseStep 4696361 = 3522271) B3522271
theorem B3130907 : Blo 2085435 3130907 := bstep (se 1 (by rfl) ⟨2348180, by rfl⟩ : syracuseStep 3130907 = 4696361) B4696361
theorem B2087271 : Blo 2085435 2087271 := bstep (se 1 (by rfl) ⟨1565453, by rfl⟩ : syracuseStep 2087271 = 3130907) B3130907
theorem B2348185 : Blo 2085435 2348185 := bbase (se 2 (by rfl) ⟨880569, by rfl⟩ : syracuseStep 2348185 = 1761139) (by norm_num)
theorem B3130913 : Blo 2085435 3130913 := bstep (se 2 (by rfl) ⟨1174092, by rfl⟩ : syracuseStep 3130913 = 2348185) B2348185
theorem B2087275 : Blo 2085435 2087275 := bstep (se 1 (by rfl) ⟨1565456, by rfl⟩ : syracuseStep 2087275 = 3130913) B3130913
theorem B7925141 : Blo 2085435 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B5283427 : Blo 2085435 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B7044569 : Blo 2085435 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B4696379 : Blo 2085435 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B3130919 : Blo 2085435 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B2087279 : Blo 2085435 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B3130925 : Blo 2085435 3130925 := bbase (se 3 (by rfl) ⟨587048, by rfl⟩ : syracuseStep 3130925 = 1174097) (by norm_num)
theorem B2087283 : Blo 2085435 2087283 := bstep (se 1 (by rfl) ⟨1565462, by rfl⟩ : syracuseStep 2087283 = 3130925) B3130925
theorem B4696397 : Blo 2085435 4696397 := bbase (se 3 (by rfl) ⟨880574, by rfl⟩ : syracuseStep 4696397 = 1761149) (by norm_num)
theorem B3130931 : Blo 2085435 3130931 := bstep (se 1 (by rfl) ⟨2348198, by rfl⟩ : syracuseStep 3130931 = 4696397) B4696397
theorem B2087287 : Blo 2085435 2087287 := bstep (se 1 (by rfl) ⟨1565465, by rfl⟩ : syracuseStep 2087287 = 3130931) B3130931
theorem B2641729 : Blo 2085435 2641729 := bbase (se 2 (by rfl) ⟨990648, by rfl⟩ : syracuseStep 2641729 = 1981297) (by norm_num)
theorem B3522305 : Blo 2085435 3522305 := bstep (se 2 (by rfl) ⟨1320864, by rfl⟩ : syracuseStep 3522305 = 2641729) B2641729
theorem B2348203 : Blo 2085435 2348203 := bstep (se 1 (by rfl) ⟨1761152, by rfl⟩ : syracuseStep 2348203 = 3522305) B3522305
theorem B3130937 : Blo 2085435 3130937 := bstep (se 2 (by rfl) ⟨1174101, by rfl⟩ : syracuseStep 3130937 = 2348203) B2348203
theorem B2087291 : Blo 2085435 2087291 := bstep (se 1 (by rfl) ⟨1565468, by rfl⟩ : syracuseStep 2087291 = 3130937) B3130937
theorem B3343445 : Blo 2085435 3343445 := bbase (se 8 (by rfl) ⟨19590, by rfl⟩ : syracuseStep 3343445 = 39181) (by norm_num)
theorem B2228963 : Blo 2085435 2228963 := bstep (se 1 (by rfl) ⟨1671722, by rfl⟩ : syracuseStep 2228963 = 3343445) B3343445
theorem B23775605 : Blo 2085435 23775605 := bstep (se 5 (by rfl) ⟨1114481, by rfl⟩ : syracuseStep 23775605 = 2228963) B2228963
theorem B15850403 : Blo 2085435 15850403 := bstep (se 1 (by rfl) ⟨11887802, by rfl⟩ : syracuseStep 15850403 = 23775605) B23775605
theorem B10566935 : Blo 2085435 10566935 := bstep (se 1 (by rfl) ⟨7925201, by rfl⟩ : syracuseStep 10566935 = 15850403) B15850403
theorem B7044623 : Blo 2085435 7044623 := bstep (se 1 (by rfl) ⟨5283467, by rfl⟩ : syracuseStep 7044623 = 10566935) B10566935
theorem B4696415 : Blo 2085435 4696415 := bstep (se 1 (by rfl) ⟨3522311, by rfl⟩ : syracuseStep 4696415 = 7044623) B7044623
theorem B3130943 : Blo 2085435 3130943 := bstep (se 1 (by rfl) ⟨2348207, by rfl⟩ : syracuseStep 3130943 = 4696415) B4696415
theorem B2087295 : Blo 2085435 2087295 := bstep (se 1 (by rfl) ⟨1565471, by rfl⟩ : syracuseStep 2087295 = 3130943) B3130943
theorem B3130949 : Blo 2085435 3130949 := bbase (se 4 (by rfl) ⟨293526, by rfl⟩ : syracuseStep 3130949 = 587053) (by norm_num)
theorem B2087299 : Blo 2085435 2087299 := bstep (se 1 (by rfl) ⟨1565474, by rfl⟩ : syracuseStep 2087299 = 3130949) B3130949
theorem B3522325 : Blo 2085435 3522325 := bbase (se 6 (by rfl) ⟨82554, by rfl⟩ : syracuseStep 3522325 = 165109) (by norm_num)
theorem B4696433 : Blo 2085435 4696433 := bstep (se 2 (by rfl) ⟨1761162, by rfl⟩ : syracuseStep 4696433 = 3522325) B3522325
theorem B3130955 : Blo 2085435 3130955 := bstep (se 1 (by rfl) ⟨2348216, by rfl⟩ : syracuseStep 3130955 = 4696433) B4696433
theorem B2087303 : Blo 2085435 2087303 := bstep (se 1 (by rfl) ⟨1565477, by rfl⟩ : syracuseStep 2087303 = 3130955) B3130955
theorem B2348221 : Blo 2085435 2348221 := bbase (se 3 (by rfl) ⟨440291, by rfl⟩ : syracuseStep 2348221 = 880583) (by norm_num)
theorem B3130961 : Blo 2085435 3130961 := bstep (se 2 (by rfl) ⟨1174110, by rfl⟩ : syracuseStep 3130961 = 2348221) B2348221
theorem B2087307 : Blo 2085435 2087307 := bstep (se 1 (by rfl) ⟨1565480, by rfl⟩ : syracuseStep 2087307 = 3130961) B3130961
theorem B7044677 : Blo 2085435 7044677 := bbase (se 4 (by rfl) ⟨660438, by rfl⟩ : syracuseStep 7044677 = 1320877) (by norm_num)
theorem B4696451 : Blo 2085435 4696451 := bstep (se 1 (by rfl) ⟨3522338, by rfl⟩ : syracuseStep 4696451 = 7044677) B7044677
theorem B3130967 : Blo 2085435 3130967 := bstep (se 1 (by rfl) ⟨2348225, by rfl⟩ : syracuseStep 3130967 = 4696451) B4696451
theorem B2087311 : Blo 2085435 2087311 := bstep (se 1 (by rfl) ⟨1565483, by rfl⟩ : syracuseStep 2087311 = 3130967) B3130967
theorem B3130973 : Blo 2085435 3130973 := bbase (se 3 (by rfl) ⟨587057, by rfl⟩ : syracuseStep 3130973 = 1174115) (by norm_num)
theorem B2087315 : Blo 2085435 2087315 := bstep (se 1 (by rfl) ⟨1565486, by rfl⟩ : syracuseStep 2087315 = 3130973) B3130973
theorem B4696469 : Blo 2085435 4696469 := bbase (se 6 (by rfl) ⟨110073, by rfl⟩ : syracuseStep 4696469 = 220147) (by norm_num)
theorem B3130979 : Blo 2085435 3130979 := bstep (se 1 (by rfl) ⟨2348234, by rfl⟩ : syracuseStep 3130979 = 4696469) B4696469
theorem B2087319 : Blo 2085435 2087319 := bstep (se 1 (by rfl) ⟨1565489, by rfl⟩ : syracuseStep 2087319 = 3130979) B3130979
theorem B6686981 : Blo 2085435 6686981 := bbase (se 4 (by rfl) ⟨626904, by rfl⟩ : syracuseStep 6686981 = 1253809) (by norm_num)
theorem B4457987 : Blo 2085435 4457987 := bstep (se 1 (by rfl) ⟨3343490, by rfl⟩ : syracuseStep 4457987 = 6686981) B6686981
theorem B2971991 : Blo 2085435 2971991 := bstep (se 1 (by rfl) ⟨2228993, by rfl⟩ : syracuseStep 2971991 = 4457987) B4457987
theorem B7925309 : Blo 2085435 7925309 := bstep (se 3 (by rfl) ⟨1485995, by rfl⟩ : syracuseStep 7925309 = 2971991) B2971991
theorem B5283539 : Blo 2085435 5283539 := bstep (se 1 (by rfl) ⟨3962654, by rfl⟩ : syracuseStep 5283539 = 7925309) B7925309
theorem B3522359 : Blo 2085435 3522359 := bstep (se 1 (by rfl) ⟨2641769, by rfl⟩ : syracuseStep 3522359 = 5283539) B5283539
theorem B2348239 : Blo 2085435 2348239 := bstep (se 1 (by rfl) ⟨1761179, by rfl⟩ : syracuseStep 2348239 = 3522359) B3522359
theorem B3130985 : Blo 2085435 3130985 := bstep (se 2 (by rfl) ⟨1174119, by rfl⟩ : syracuseStep 3130985 = 2348239) B2348239
theorem B2087323 : Blo 2085435 2087323 := bstep (se 1 (by rfl) ⟨1565492, by rfl⟩ : syracuseStep 2087323 = 3130985) B3130985
theorem B8915989 : Blo 2085435 8915989 := bbase (se 6 (by rfl) ⟨208968, by rfl⟩ : syracuseStep 8915989 = 417937) (by norm_num)
theorem B11887985 : Blo 2085435 11887985 := bstep (se 2 (by rfl) ⟨4457994, by rfl⟩ : syracuseStep 11887985 = 8915989) B8915989
theorem B7925323 : Blo 2085435 7925323 := bstep (se 1 (by rfl) ⟨5943992, by rfl⟩ : syracuseStep 7925323 = 11887985) B11887985
theorem B10567097 : Blo 2085435 10567097 := bstep (se 2 (by rfl) ⟨3962661, by rfl⟩ : syracuseStep 10567097 = 7925323) B7925323
theorem B7044731 : Blo 2085435 7044731 := bstep (se 1 (by rfl) ⟨5283548, by rfl⟩ : syracuseStep 7044731 = 10567097) B10567097
theorem B4696487 : Blo 2085435 4696487 := bstep (se 1 (by rfl) ⟨3522365, by rfl⟩ : syracuseStep 4696487 = 7044731) B7044731
theorem B3130991 : Blo 2085435 3130991 := bstep (se 1 (by rfl) ⟨2348243, by rfl⟩ : syracuseStep 3130991 = 4696487) B4696487
theorem B2087327 : Blo 2085435 2087327 := bstep (se 1 (by rfl) ⟨1565495, by rfl⟩ : syracuseStep 2087327 = 3130991) B3130991
theorem B3130997 : Blo 2085435 3130997 := bbase (se 5 (by rfl) ⟨146765, by rfl⟩ : syracuseStep 3130997 = 293531) (by norm_num)
theorem B2087331 : Blo 2085435 2087331 := bstep (se 1 (by rfl) ⟨1565498, by rfl⟩ : syracuseStep 2087331 = 3130997) B3130997
theorem B3962677 : Blo 2085435 3962677 := bbase (se 5 (by rfl) ⟨185750, by rfl⟩ : syracuseStep 3962677 = 371501) (by norm_num)
theorem B5283569 : Blo 2085435 5283569 := bstep (se 2 (by rfl) ⟨1981338, by rfl⟩ : syracuseStep 5283569 = 3962677) B3962677
theorem B3522379 : Blo 2085435 3522379 := bstep (se 1 (by rfl) ⟨2641784, by rfl⟩ : syracuseStep 3522379 = 5283569) B5283569
theorem B4696505 : Blo 2085435 4696505 := bstep (se 2 (by rfl) ⟨1761189, by rfl⟩ : syracuseStep 4696505 = 3522379) B3522379
theorem B3131003 : Blo 2085435 3131003 := bstep (se 1 (by rfl) ⟨2348252, by rfl⟩ : syracuseStep 3131003 = 4696505) B4696505
theorem B2087335 : Blo 2085435 2087335 := bstep (se 1 (by rfl) ⟨1565501, by rfl⟩ : syracuseStep 2087335 = 3131003) B3131003
theorem B2348257 : Blo 2085435 2348257 := bbase (se 2 (by rfl) ⟨880596, by rfl⟩ : syracuseStep 2348257 = 1761193) (by norm_num)
theorem B3131009 : Blo 2085435 3131009 := bstep (se 2 (by rfl) ⟨1174128, by rfl⟩ : syracuseStep 3131009 = 2348257) B2348257
theorem B2087339 : Blo 2085435 2087339 := bstep (se 1 (by rfl) ⟨1565504, by rfl⟩ : syracuseStep 2087339 = 3131009) B3131009
theorem B5283589 : Blo 2085435 5283589 := bbase (se 4 (by rfl) ⟨495336, by rfl⟩ : syracuseStep 5283589 = 990673) (by norm_num)
theorem B7044785 : Blo 2085435 7044785 := bstep (se 2 (by rfl) ⟨2641794, by rfl⟩ : syracuseStep 7044785 = 5283589) B5283589
theorem B4696523 : Blo 2085435 4696523 := bstep (se 1 (by rfl) ⟨3522392, by rfl⟩ : syracuseStep 4696523 = 7044785) B7044785
theorem B3131015 : Blo 2085435 3131015 := bstep (se 1 (by rfl) ⟨2348261, by rfl⟩ : syracuseStep 3131015 = 4696523) B4696523
theorem B2087343 : Blo 2085435 2087343 := bstep (se 1 (by rfl) ⟨1565507, by rfl⟩ : syracuseStep 2087343 = 3131015) B3131015
theorem B3131021 : Blo 2085435 3131021 := bbase (se 3 (by rfl) ⟨587066, by rfl⟩ : syracuseStep 3131021 = 1174133) (by norm_num)
theorem B2087347 : Blo 2085435 2087347 := bstep (se 1 (by rfl) ⟨1565510, by rfl⟩ : syracuseStep 2087347 = 3131021) B3131021
theorem B4696541 : Blo 2085435 4696541 := bbase (se 3 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 4696541 = 1761203) (by norm_num)
theorem B3131027 : Blo 2085435 3131027 := bstep (se 1 (by rfl) ⟨2348270, by rfl⟩ : syracuseStep 3131027 = 4696541) B4696541
theorem B2087351 : Blo 2085435 2087351 := bstep (se 1 (by rfl) ⟨1565513, by rfl⟩ : syracuseStep 2087351 = 3131027) B3131027
theorem B3522413 : Blo 2085435 3522413 := bbase (se 3 (by rfl) ⟨660452, by rfl⟩ : syracuseStep 3522413 = 1320905) (by norm_num)
theorem B2348275 : Blo 2085435 2348275 := bstep (se 1 (by rfl) ⟨1761206, by rfl⟩ : syracuseStep 2348275 = 3522413) B3522413
theorem B3131033 : Blo 2085435 3131033 := bstep (se 2 (by rfl) ⟨1174137, by rfl⟩ : syracuseStep 3131033 = 2348275) B2348275
theorem B2087355 : Blo 2085435 2087355 := bstep (se 1 (by rfl) ⟨1565516, by rfl⟩ : syracuseStep 2087355 = 3131033) B3131033
theorem B30091925 : Blo 2085435 30091925 := bbase (se 6 (by rfl) ⟨705279, by rfl⟩ : syracuseStep 30091925 = 1410559) (by norm_num)
theorem B20061283 : Blo 2085435 20061283 := bstep (se 1 (by rfl) ⟨15045962, by rfl⟩ : syracuseStep 20061283 = 30091925) B30091925
theorem B26748377 : Blo 2085435 26748377 := bstep (se 2 (by rfl) ⟨10030641, by rfl⟩ : syracuseStep 26748377 = 20061283) B20061283
theorem B17832251 : Blo 2085435 17832251 := bstep (se 1 (by rfl) ⟨13374188, by rfl⟩ : syracuseStep 17832251 = 26748377) B26748377
theorem B11888167 : Blo 2085435 11888167 := bstep (se 1 (by rfl) ⟨8916125, by rfl⟩ : syracuseStep 11888167 = 17832251) B17832251
theorem B15850889 : Blo 2085435 15850889 := bstep (se 2 (by rfl) ⟨5944083, by rfl⟩ : syracuseStep 15850889 = 11888167) B11888167
theorem B10567259 : Blo 2085435 10567259 := bstep (se 1 (by rfl) ⟨7925444, by rfl⟩ : syracuseStep 10567259 = 15850889) B15850889
theorem B7044839 : Blo 2085435 7044839 := bstep (se 1 (by rfl) ⟨5283629, by rfl⟩ : syracuseStep 7044839 = 10567259) B10567259
theorem B4696559 : Blo 2085435 4696559 := bstep (se 1 (by rfl) ⟨3522419, by rfl⟩ : syracuseStep 4696559 = 7044839) B7044839
theorem B3131039 : Blo 2085435 3131039 := bstep (se 1 (by rfl) ⟨2348279, by rfl⟩ : syracuseStep 3131039 = 4696559) B4696559
theorem B2087359 : Blo 2085435 2087359 := bstep (se 1 (by rfl) ⟨1565519, by rfl⟩ : syracuseStep 2087359 = 3131039) B3131039
theorem B3131045 : Blo 2085435 3131045 := bbase (se 4 (by rfl) ⟨293535, by rfl⟩ : syracuseStep 3131045 = 587071) (by norm_num)
theorem B2087363 : Blo 2085435 2087363 := bstep (se 1 (by rfl) ⟨1565522, by rfl⟩ : syracuseStep 2087363 = 3131045) B3131045
theorem B2641825 : Blo 2085435 2641825 := bbase (se 2 (by rfl) ⟨990684, by rfl⟩ : syracuseStep 2641825 = 1981369) (by norm_num)
theorem B3522433 : Blo 2085435 3522433 := bstep (se 2 (by rfl) ⟨1320912, by rfl⟩ : syracuseStep 3522433 = 2641825) B2641825
theorem B4696577 : Blo 2085435 4696577 := bstep (se 2 (by rfl) ⟨1761216, by rfl⟩ : syracuseStep 4696577 = 3522433) B3522433
theorem B3131051 : Blo 2085435 3131051 := bstep (se 1 (by rfl) ⟨2348288, by rfl⟩ : syracuseStep 3131051 = 4696577) B4696577
theorem B2087367 : Blo 2085435 2087367 := bstep (se 1 (by rfl) ⟨1565525, by rfl⟩ : syracuseStep 2087367 = 3131051) B3131051
theorem B2348293 : Blo 2085435 2348293 := bbase (se 4 (by rfl) ⟨220152, by rfl⟩ : syracuseStep 2348293 = 440305) (by norm_num)
theorem B3131057 : Blo 2085435 3131057 := bstep (se 2 (by rfl) ⟨1174146, by rfl⟩ : syracuseStep 3131057 = 2348293) B2348293
theorem B2087371 : Blo 2085435 2087371 := bstep (se 1 (by rfl) ⟨1565528, by rfl⟩ : syracuseStep 2087371 = 3131057) B3131057
theorem B2229049 : Blo 2085435 2229049 := bbase (se 2 (by rfl) ⟨835893, by rfl⟩ : syracuseStep 2229049 = 1671787) (by norm_num)
theorem B2972065 : Blo 2085435 2972065 := bstep (se 2 (by rfl) ⟨1114524, by rfl⟩ : syracuseStep 2972065 = 2229049) B2229049
theorem B3962753 : Blo 2085435 3962753 := bstep (se 2 (by rfl) ⟨1486032, by rfl⟩ : syracuseStep 3962753 = 2972065) B2972065
theorem B2641835 : Blo 2085435 2641835 := bstep (se 1 (by rfl) ⟨1981376, by rfl⟩ : syracuseStep 2641835 = 3962753) B3962753
theorem B7044893 : Blo 2085435 7044893 := bstep (se 3 (by rfl) ⟨1320917, by rfl⟩ : syracuseStep 7044893 = 2641835) B2641835
theorem B4696595 : Blo 2085435 4696595 := bstep (se 1 (by rfl) ⟨3522446, by rfl⟩ : syracuseStep 4696595 = 7044893) B7044893
theorem B3131063 : Blo 2085435 3131063 := bstep (se 1 (by rfl) ⟨2348297, by rfl⟩ : syracuseStep 3131063 = 4696595) B4696595
theorem B2087375 : Blo 2085435 2087375 := bstep (se 1 (by rfl) ⟨1565531, by rfl⟩ : syracuseStep 2087375 = 3131063) B3131063
theorem B3131069 : Blo 2085435 3131069 := bbase (se 3 (by rfl) ⟨587075, by rfl⟩ : syracuseStep 3131069 = 1174151) (by norm_num)
theorem B2087379 : Blo 2085435 2087379 := bstep (se 1 (by rfl) ⟨1565534, by rfl⟩ : syracuseStep 2087379 = 3131069) B3131069
theorem B4696613 : Blo 2085435 4696613 := bbase (se 4 (by rfl) ⟨440307, by rfl⟩ : syracuseStep 4696613 = 880615) (by norm_num)
theorem B3131075 : Blo 2085435 3131075 := bstep (se 1 (by rfl) ⟨2348306, by rfl⟩ : syracuseStep 3131075 = 4696613) B4696613
theorem B2087383 : Blo 2085435 2087383 := bstep (se 1 (by rfl) ⟨1565537, by rfl⟩ : syracuseStep 2087383 = 3131075) B3131075
theorem B5283701 : Blo 2085435 5283701 := bbase (se 5 (by rfl) ⟨247673, by rfl⟩ : syracuseStep 5283701 = 495347) (by norm_num)
theorem B3522467 : Blo 2085435 3522467 := bstep (se 1 (by rfl) ⟨2641850, by rfl⟩ : syracuseStep 3522467 = 5283701) B5283701
theorem B2348311 : Blo 2085435 2348311 := bstep (se 1 (by rfl) ⟨1761233, by rfl⟩ : syracuseStep 2348311 = 3522467) B3522467
theorem B3131081 : Blo 2085435 3131081 := bstep (se 2 (by rfl) ⟨1174155, by rfl⟩ : syracuseStep 3131081 = 2348311) B2348311
theorem B2087387 : Blo 2085435 2087387 := bstep (se 1 (by rfl) ⟨1565540, by rfl⟩ : syracuseStep 2087387 = 3131081) B3131081
theorem B8033701 : Blo 2085435 8033701 := bbase (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) (by norm_num)
theorem B10711601 : Blo 2085435 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B7141067 : Blo 2085435 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B4760711 : Blo 2085435 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B3173807 : Blo 2085435 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B8463485 : Blo 2085435 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B22569293 : Blo 2085435 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B15046195 : Blo 2085435 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B20061593 : Blo 2085435 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B13374395 : Blo 2085435 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B8916263 : Blo 2085435 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B5944175 : Blo 2085435 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B3962783 : Blo 2085435 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B10567421 : Blo 2085435 10567421 := bstep (se 3 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 10567421 = 3962783) B3962783
theorem B7044947 : Blo 2085435 7044947 := bstep (se 1 (by rfl) ⟨5283710, by rfl⟩ : syracuseStep 7044947 = 10567421) B10567421
theorem B4696631 : Blo 2085435 4696631 := bstep (se 1 (by rfl) ⟨3522473, by rfl⟩ : syracuseStep 4696631 = 7044947) B7044947
theorem B3131087 : Blo 2085435 3131087 := bstep (se 1 (by rfl) ⟨2348315, by rfl⟩ : syracuseStep 3131087 = 4696631) B4696631
theorem B2087391 : Blo 2085435 2087391 := bstep (se 1 (by rfl) ⟨1565543, by rfl⟩ : syracuseStep 2087391 = 3131087) B3131087
theorem B3131093 : Blo 2085435 3131093 := bbase (se 7 (by rfl) ⟨36692, by rfl⟩ : syracuseStep 3131093 = 73385) (by norm_num)
theorem B2087395 : Blo 2085435 2087395 := bstep (se 1 (by rfl) ⟨1565546, by rfl⟩ : syracuseStep 2087395 = 3131093) B3131093
theorem B4458149 : Blo 2085435 4458149 := bbase (se 4 (by rfl) ⟨417951, by rfl⟩ : syracuseStep 4458149 = 835903) (by norm_num)
theorem B2972099 : Blo 2085435 2972099 := bstep (se 1 (by rfl) ⟨2229074, by rfl⟩ : syracuseStep 2972099 = 4458149) B4458149
theorem B7925597 : Blo 2085435 7925597 := bstep (se 3 (by rfl) ⟨1486049, by rfl⟩ : syracuseStep 7925597 = 2972099) B2972099
theorem B5283731 : Blo 2085435 5283731 := bstep (se 1 (by rfl) ⟨3962798, by rfl⟩ : syracuseStep 5283731 = 7925597) B7925597
theorem B3522487 : Blo 2085435 3522487 := bstep (se 1 (by rfl) ⟨2641865, by rfl⟩ : syracuseStep 3522487 = 5283731) B5283731
theorem B4696649 : Blo 2085435 4696649 := bstep (se 2 (by rfl) ⟨1761243, by rfl⟩ : syracuseStep 4696649 = 3522487) B3522487
theorem B3131099 : Blo 2085435 3131099 := bstep (se 1 (by rfl) ⟨2348324, by rfl⟩ : syracuseStep 3131099 = 4696649) B4696649
theorem B2087399 : Blo 2085435 2087399 := bstep (se 1 (by rfl) ⟨1565549, by rfl⟩ : syracuseStep 2087399 = 3131099) B3131099
theorem B2348329 : Blo 2085435 2348329 := bbase (se 2 (by rfl) ⟨880623, by rfl⟩ : syracuseStep 2348329 = 1761247) (by norm_num)
theorem B3131105 : Blo 2085435 3131105 := bstep (se 2 (by rfl) ⟨1174164, by rfl⟩ : syracuseStep 3131105 = 2348329) B2348329
theorem B2087403 : Blo 2085435 2087403 := bstep (se 1 (by rfl) ⟨1565552, by rfl⟩ : syracuseStep 2087403 = 3131105) B3131105
theorem B3012661 : Blo 2085435 3012661 := bbase (se 5 (by rfl) ⟨141218, by rfl⟩ : syracuseStep 3012661 = 282437) (by norm_num)
theorem B4016881 : Blo 2085435 4016881 := bstep (se 2 (by rfl) ⟨1506330, by rfl⟩ : syracuseStep 4016881 = 3012661) B3012661
theorem B21423365 : Blo 2085435 21423365 := bstep (se 4 (by rfl) ⟨2008440, by rfl⟩ : syracuseStep 21423365 = 4016881) B4016881
theorem B14282243 : Blo 2085435 14282243 := bstep (se 1 (by rfl) ⟨10711682, by rfl⟩ : syracuseStep 14282243 = 21423365) B21423365
theorem B9521495 : Blo 2085435 9521495 := bstep (se 1 (by rfl) ⟨7141121, by rfl⟩ : syracuseStep 9521495 = 14282243) B14282243
theorem B6347663 : Blo 2085435 6347663 := bstep (se 1 (by rfl) ⟨4760747, by rfl⟩ : syracuseStep 6347663 = 9521495) B9521495
theorem B4231775 : Blo 2085435 4231775 := bstep (se 1 (by rfl) ⟨3173831, by rfl⟩ : syracuseStep 4231775 = 6347663) B6347663
theorem B11284733 : Blo 2085435 11284733 := bstep (se 3 (by rfl) ⟨2115887, by rfl⟩ : syracuseStep 11284733 = 4231775) B4231775
theorem B7523155 : Blo 2085435 7523155 := bstep (se 1 (by rfl) ⟨5642366, by rfl⟩ : syracuseStep 7523155 = 11284733) B11284733
theorem B10030873 : Blo 2085435 10030873 := bstep (se 2 (by rfl) ⟨3761577, by rfl⟩ : syracuseStep 10030873 = 7523155) B7523155
theorem B13374497 : Blo 2085435 13374497 := bstep (se 2 (by rfl) ⟨5015436, by rfl⟩ : syracuseStep 13374497 = 10030873) B10030873
theorem B8916331 : Blo 2085435 8916331 := bstep (se 1 (by rfl) ⟨6687248, by rfl⟩ : syracuseStep 8916331 = 13374497) B13374497
theorem B11888441 : Blo 2085435 11888441 := bstep (se 2 (by rfl) ⟨4458165, by rfl⟩ : syracuseStep 11888441 = 8916331) B8916331
theorem B7925627 : Blo 2085435 7925627 := bstep (se 1 (by rfl) ⟨5944220, by rfl⟩ : syracuseStep 7925627 = 11888441) B11888441
theorem B5283751 : Blo 2085435 5283751 := bstep (se 1 (by rfl) ⟨3962813, by rfl⟩ : syracuseStep 5283751 = 7925627) B7925627
theorem B7045001 : Blo 2085435 7045001 := bstep (se 2 (by rfl) ⟨2641875, by rfl⟩ : syracuseStep 7045001 = 5283751) B5283751
theorem B4696667 : Blo 2085435 4696667 := bstep (se 1 (by rfl) ⟨3522500, by rfl⟩ : syracuseStep 4696667 = 7045001) B7045001
theorem B3131111 : Blo 2085435 3131111 := bstep (se 1 (by rfl) ⟨2348333, by rfl⟩ : syracuseStep 3131111 = 4696667) B4696667
theorem B2087407 : Blo 2085435 2087407 := bstep (se 1 (by rfl) ⟨1565555, by rfl⟩ : syracuseStep 2087407 = 3131111) B3131111
theorem B3131117 : Blo 2085435 3131117 := bbase (se 3 (by rfl) ⟨587084, by rfl⟩ : syracuseStep 3131117 = 1174169) (by norm_num)
theorem B2087411 : Blo 2085435 2087411 := bstep (se 1 (by rfl) ⟨1565558, by rfl⟩ : syracuseStep 2087411 = 3131117) B3131117
theorem B4696685 : Blo 2085435 4696685 := bbase (se 3 (by rfl) ⟨880628, by rfl⟩ : syracuseStep 4696685 = 1761257) (by norm_num)
theorem B3131123 : Blo 2085435 3131123 := bstep (se 1 (by rfl) ⟨2348342, by rfl⟩ : syracuseStep 3131123 = 4696685) B4696685
theorem B2087415 : Blo 2085435 2087415 := bstep (se 1 (by rfl) ⟨1565561, by rfl⟩ : syracuseStep 2087415 = 3131123) B3131123
theorem B3962837 : Blo 2085435 3962837 := bbase (se 7 (by rfl) ⟨46439, by rfl⟩ : syracuseStep 3962837 = 92879) (by norm_num)
theorem B2641891 : Blo 2085435 2641891 := bstep (se 1 (by rfl) ⟨1981418, by rfl⟩ : syracuseStep 2641891 = 3962837) B3962837
theorem B3522521 : Blo 2085435 3522521 := bstep (se 2 (by rfl) ⟨1320945, by rfl⟩ : syracuseStep 3522521 = 2641891) B2641891
theorem B2348347 : Blo 2085435 2348347 := bstep (se 1 (by rfl) ⟨1761260, by rfl⟩ : syracuseStep 2348347 = 3522521) B3522521
theorem B3131129 : Blo 2085435 3131129 := bstep (se 2 (by rfl) ⟨1174173, by rfl⟩ : syracuseStep 3131129 = 2348347) B2348347
theorem B2087419 : Blo 2085435 2087419 := bstep (se 1 (by rfl) ⟨1565564, by rfl⟩ : syracuseStep 2087419 = 3131129) B3131129
theorem B13557077 : Blo 2085435 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B9038051 : Blo 2085435 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B6025367 : Blo 2085435 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B16067645 : Blo 2085435 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B10711763 : Blo 2085435 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B7141175 : Blo 2085435 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B4760783 : Blo 2085435 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B3173855 : Blo 2085435 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B33854453 : Blo 2085435 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B22569635 : Blo 2085435 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B60185693 : Blo 2085435 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B40123795 : Blo 2085435 40123795 := bstep (se 1 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 40123795 = 60185693) B60185693
theorem B53498393 : Blo 2085435 53498393 := bstep (se 2 (by rfl) ⟨20061897, by rfl⟩ : syracuseStep 53498393 = 40123795) B40123795
theorem B35665595 : Blo 2085435 35665595 := bstep (se 1 (by rfl) ⟨26749196, by rfl⟩ : syracuseStep 35665595 = 53498393) B53498393
theorem B23777063 : Blo 2085435 23777063 := bstep (se 1 (by rfl) ⟨17832797, by rfl⟩ : syracuseStep 23777063 = 35665595) B35665595
theorem B15851375 : Blo 2085435 15851375 := bstep (se 1 (by rfl) ⟨11888531, by rfl⟩ : syracuseStep 15851375 = 23777063) B23777063
theorem B10567583 : Blo 2085435 10567583 := bstep (se 1 (by rfl) ⟨7925687, by rfl⟩ : syracuseStep 10567583 = 15851375) B15851375
theorem B7045055 : Blo 2085435 7045055 := bstep (se 1 (by rfl) ⟨5283791, by rfl⟩ : syracuseStep 7045055 = 10567583) B10567583
theorem B4696703 : Blo 2085435 4696703 := bstep (se 1 (by rfl) ⟨3522527, by rfl⟩ : syracuseStep 4696703 = 7045055) B7045055
theorem B3131135 : Blo 2085435 3131135 := bstep (se 1 (by rfl) ⟨2348351, by rfl⟩ : syracuseStep 3131135 = 4696703) B4696703
theorem B2087423 : Blo 2085435 2087423 := bstep (se 1 (by rfl) ⟨1565567, by rfl⟩ : syracuseStep 2087423 = 3131135) B3131135
theorem B3131141 : Blo 2085435 3131141 := bbase (se 4 (by rfl) ⟨293544, by rfl⟩ : syracuseStep 3131141 = 587089) (by norm_num)
theorem B2087427 : Blo 2085435 2087427 := bstep (se 1 (by rfl) ⟨1565570, by rfl⟩ : syracuseStep 2087427 = 3131141) B3131141
theorem B3522541 : Blo 2085435 3522541 := bbase (se 3 (by rfl) ⟨660476, by rfl⟩ : syracuseStep 3522541 = 1320953) (by norm_num)
theorem B4696721 : Blo 2085435 4696721 := bstep (se 2 (by rfl) ⟨1761270, by rfl⟩ : syracuseStep 4696721 = 3522541) B3522541
theorem B3131147 : Blo 2085435 3131147 := bstep (se 1 (by rfl) ⟨2348360, by rfl⟩ : syracuseStep 3131147 = 4696721) B4696721
theorem B2087431 : Blo 2085435 2087431 := bstep (se 1 (by rfl) ⟨1565573, by rfl⟩ : syracuseStep 2087431 = 3131147) B3131147
theorem B2348365 : Blo 2085435 2348365 := bbase (se 3 (by rfl) ⟨440318, by rfl⟩ : syracuseStep 2348365 = 880637) (by norm_num)
theorem B3131153 : Blo 2085435 3131153 := bstep (se 2 (by rfl) ⟨1174182, by rfl⟩ : syracuseStep 3131153 = 2348365) B2348365
theorem B2087435 : Blo 2085435 2087435 := bstep (se 1 (by rfl) ⟨1565576, by rfl⟩ : syracuseStep 2087435 = 3131153) B3131153
theorem C0 (j : ℕ) (h1 : 521358 ≤ j) (h2 : j ≤ 521858) : Blo 2085435 (4 * j + 3) := by
  interval_cases j
  · exact B2085435
  · exact B2085439
  · exact B2085443
  · exact B2085447
  · exact B2085451
  · exact B2085455
  · exact B2085459
  · exact B2085463
  · exact B2085467
  · exact B2085471
  · exact B2085475
  · exact B2085479
  · exact B2085483
  · exact B2085487
  · exact B2085491
  · exact B2085495
  · exact B2085499
  · exact B2085503
  · exact B2085507
  · exact B2085511
  · exact B2085515
  · exact B2085519
  · exact B2085523
  · exact B2085527
  · exact B2085531
  · exact B2085535
  · exact B2085539
  · exact B2085543
  · exact B2085547
  · exact B2085551
  · exact B2085555
  · exact B2085559
  · exact B2085563
  · exact B2085567
  · exact B2085571
  · exact B2085575
  · exact B2085579
  · exact B2085583
  · exact B2085587
  · exact B2085591
  · exact B2085595
  · exact B2085599
  · exact B2085603
  · exact B2085607
  · exact B2085611
  · exact B2085615
  · exact B2085619
  · exact B2085623
  · exact B2085627
  · exact B2085631
  · exact B2085635
  · exact B2085639
  · exact B2085643
  · exact B2085647
  · exact B2085651
  · exact B2085655
  · exact B2085659
  · exact B2085663
  · exact B2085667
  · exact B2085671
  · exact B2085675
  · exact B2085679
  · exact B2085683
  · exact B2085687
  · exact B2085691
  · exact B2085695
  · exact B2085699
  · exact B2085703
  · exact B2085707
  · exact B2085711
  · exact B2085715
  · exact B2085719
  · exact B2085723
  · exact B2085727
  · exact B2085731
  · exact B2085735
  · exact B2085739
  · exact B2085743
  · exact B2085747
  · exact B2085751
  · exact B2085755
  · exact B2085759
  · exact B2085763
  · exact B2085767
  · exact B2085771
  · exact B2085775
  · exact B2085779
  · exact B2085783
  · exact B2085787
  · exact B2085791
  · exact B2085795
  · exact B2085799
  · exact B2085803
  · exact B2085807
  · exact B2085811
  · exact B2085815
  · exact B2085819
  · exact B2085823
  · exact B2085827
  · exact B2085831
  · exact B2085835
  · exact B2085839
  · exact B2085843
  · exact B2085847
  · exact B2085851
  · exact B2085855
  · exact B2085859
  · exact B2085863
  · exact B2085867
  · exact B2085871
  · exact B2085875
  · exact B2085879
  · exact B2085883
  · exact B2085887
  · exact B2085891
  · exact B2085895
  · exact B2085899
  · exact B2085903
  · exact B2085907
  · exact B2085911
  · exact B2085915
  · exact B2085919
  · exact B2085923
  · exact B2085927
  · exact B2085931
  · exact B2085935
  · exact B2085939
  · exact B2085943
  · exact B2085947
  · exact B2085951
  · exact B2085955
  · exact B2085959
  · exact B2085963
  · exact B2085967
  · exact B2085971
  · exact B2085975
  · exact B2085979
  · exact B2085983
  · exact B2085987
  · exact B2085991
  · exact B2085995
  · exact B2085999
  · exact B2086003
  · exact B2086007
  · exact B2086011
  · exact B2086015
  · exact B2086019
  · exact B2086023
  · exact B2086027
  · exact B2086031
  · exact B2086035
  · exact B2086039
  · exact B2086043
  · exact B2086047
  · exact B2086051
  · exact B2086055
  · exact B2086059
  · exact B2086063
  · exact B2086067
  · exact B2086071
  · exact B2086075
  · exact B2086079
  · exact B2086083
  · exact B2086087
  · exact B2086091
  · exact B2086095
  · exact B2086099
  · exact B2086103
  · exact B2086107
  · exact B2086111
  · exact B2086115
  · exact B2086119
  · exact B2086123
  · exact B2086127
  · exact B2086131
  · exact B2086135
  · exact B2086139
  · exact B2086143
  · exact B2086147
  · exact B2086151
  · exact B2086155
  · exact B2086159
  · exact B2086163
  · exact B2086167
  · exact B2086171
  · exact B2086175
  · exact B2086179
  · exact B2086183
  · exact B2086187
  · exact B2086191
  · exact B2086195
  · exact B2086199
  · exact B2086203
  · exact B2086207
  · exact B2086211
  · exact B2086215
  · exact B2086219
  · exact B2086223
  · exact B2086227
  · exact B2086231
  · exact B2086235
  · exact B2086239
  · exact B2086243
  · exact B2086247
  · exact B2086251
  · exact B2086255
  · exact B2086259
  · exact B2086263
  · exact B2086267
  · exact B2086271
  · exact B2086275
  · exact B2086279
  · exact B2086283
  · exact B2086287
  · exact B2086291
  · exact B2086295
  · exact B2086299
  · exact B2086303
  · exact B2086307
  · exact B2086311
  · exact B2086315
  · exact B2086319
  · exact B2086323
  · exact B2086327
  · exact B2086331
  · exact B2086335
  · exact B2086339
  · exact B2086343
  · exact B2086347
  · exact B2086351
  · exact B2086355
  · exact B2086359
  · exact B2086363
  · exact B2086367
  · exact B2086371
  · exact B2086375
  · exact B2086379
  · exact B2086383
  · exact B2086387
  · exact B2086391
  · exact B2086395
  · exact B2086399
  · exact B2086403
  · exact B2086407
  · exact B2086411
  · exact B2086415
  · exact B2086419
  · exact B2086423
  · exact B2086427
  · exact B2086431
  · exact B2086435
  · exact B2086439
  · exact B2086443
  · exact B2086447
  · exact B2086451
  · exact B2086455
  · exact B2086459
  · exact B2086463
  · exact B2086467
  · exact B2086471
  · exact B2086475
  · exact B2086479
  · exact B2086483
  · exact B2086487
  · exact B2086491
  · exact B2086495
  · exact B2086499
  · exact B2086503
  · exact B2086507
  · exact B2086511
  · exact B2086515
  · exact B2086519
  · exact B2086523
  · exact B2086527
  · exact B2086531
  · exact B2086535
  · exact B2086539
  · exact B2086543
  · exact B2086547
  · exact B2086551
  · exact B2086555
  · exact B2086559
  · exact B2086563
  · exact B2086567
  · exact B2086571
  · exact B2086575
  · exact B2086579
  · exact B2086583
  · exact B2086587
  · exact B2086591
  · exact B2086595
  · exact B2086599
  · exact B2086603
  · exact B2086607
  · exact B2086611
  · exact B2086615
  · exact B2086619
  · exact B2086623
  · exact B2086627
  · exact B2086631
  · exact B2086635
  · exact B2086639
  · exact B2086643
  · exact B2086647
  · exact B2086651
  · exact B2086655
  · exact B2086659
  · exact B2086663
  · exact B2086667
  · exact B2086671
  · exact B2086675
  · exact B2086679
  · exact B2086683
  · exact B2086687
  · exact B2086691
  · exact B2086695
  · exact B2086699
  · exact B2086703
  · exact B2086707
  · exact B2086711
  · exact B2086715
  · exact B2086719
  · exact B2086723
  · exact B2086727
  · exact B2086731
  · exact B2086735
  · exact B2086739
  · exact B2086743
  · exact B2086747
  · exact B2086751
  · exact B2086755
  · exact B2086759
  · exact B2086763
  · exact B2086767
  · exact B2086771
  · exact B2086775
  · exact B2086779
  · exact B2086783
  · exact B2086787
  · exact B2086791
  · exact B2086795
  · exact B2086799
  · exact B2086803
  · exact B2086807
  · exact B2086811
  · exact B2086815
  · exact B2086819
  · exact B2086823
  · exact B2086827
  · exact B2086831
  · exact B2086835
  · exact B2086839
  · exact B2086843
  · exact B2086847
  · exact B2086851
  · exact B2086855
  · exact B2086859
  · exact B2086863
  · exact B2086867
  · exact B2086871
  · exact B2086875
  · exact B2086879
  · exact B2086883
  · exact B2086887
  · exact B2086891
  · exact B2086895
  · exact B2086899
  · exact B2086903
  · exact B2086907
  · exact B2086911
  · exact B2086915
  · exact B2086919
  · exact B2086923
  · exact B2086927
  · exact B2086931
  · exact B2086935
  · exact B2086939
  · exact B2086943
  · exact B2086947
  · exact B2086951
  · exact B2086955
  · exact B2086959
  · exact B2086963
  · exact B2086967
  · exact B2086971
  · exact B2086975
  · exact B2086979
  · exact B2086983
  · exact B2086987
  · exact B2086991
  · exact B2086995
  · exact B2086999
  · exact B2087003
  · exact B2087007
  · exact B2087011
  · exact B2087015
  · exact B2087019
  · exact B2087023
  · exact B2087027
  · exact B2087031
  · exact B2087035
  · exact B2087039
  · exact B2087043
  · exact B2087047
  · exact B2087051
  · exact B2087055
  · exact B2087059
  · exact B2087063
  · exact B2087067
  · exact B2087071
  · exact B2087075
  · exact B2087079
  · exact B2087083
  · exact B2087087
  · exact B2087091
  · exact B2087095
  · exact B2087099
  · exact B2087103
  · exact B2087107
  · exact B2087111
  · exact B2087115
  · exact B2087119
  · exact B2087123
  · exact B2087127
  · exact B2087131
  · exact B2087135
  · exact B2087139
  · exact B2087143
  · exact B2087147
  · exact B2087151
  · exact B2087155
  · exact B2087159
  · exact B2087163
  · exact B2087167
  · exact B2087171
  · exact B2087175
  · exact B2087179
  · exact B2087183
  · exact B2087187
  · exact B2087191
  · exact B2087195
  · exact B2087199
  · exact B2087203
  · exact B2087207
  · exact B2087211
  · exact B2087215
  · exact B2087219
  · exact B2087223
  · exact B2087227
  · exact B2087231
  · exact B2087235
  · exact B2087239
  · exact B2087243
  · exact B2087247
  · exact B2087251
  · exact B2087255
  · exact B2087259
  · exact B2087263
  · exact B2087267
  · exact B2087271
  · exact B2087275
  · exact B2087279
  · exact B2087283
  · exact B2087287
  · exact B2087291
  · exact B2087295
  · exact B2087299
  · exact B2087303
  · exact B2087307
  · exact B2087311
  · exact B2087315
  · exact B2087319
  · exact B2087323
  · exact B2087327
  · exact B2087331
  · exact B2087335
  · exact B2087339
  · exact B2087343
  · exact B2087347
  · exact B2087351
  · exact B2087355
  · exact B2087359
  · exact B2087363
  · exact B2087367
  · exact B2087371
  · exact B2087375
  · exact B2087379
  · exact B2087383
  · exact B2087387
  · exact B2087391
  · exact B2087395
  · exact B2087399
  · exact B2087403
  · exact B2087407
  · exact B2087411
  · exact B2087415
  · exact B2087419
  · exact B2087423
  · exact B2087427
  · exact B2087431
  · exact B2087435
theorem solution (m : ℕ) (hlo : 2085435 ≤ m) (hhi : m ≤ 2087435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 521358 ≤ j := by omega
    have hj2 : j ≤ 521858 := by omega
    have hb : Blo 2085435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
