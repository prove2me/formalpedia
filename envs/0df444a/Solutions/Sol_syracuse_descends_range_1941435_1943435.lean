-- Prove2me | solution 1 for syracuse_descends_range_1941435_1943435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:32.619822+00:00
-- url     : https://prove2.me/submissions/d3b1b0e6-1996-4f38-94c3-df76b60180b5

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

theorem B3276173 : Blo 1941435 3276173 := bbase (se 3 (by rfl) ⟨614282, by rfl⟩ : syracuseStep 3276173 = 1228565) (by norm_num)
theorem B2184115 : Blo 1941435 2184115 := bstep (se 1 (by rfl) ⟨1638086, by rfl⟩ : syracuseStep 2184115 = 3276173) B3276173
theorem B2912153 : Blo 1941435 2912153 := bstep (se 2 (by rfl) ⟨1092057, by rfl⟩ : syracuseStep 2912153 = 2184115) B2184115
theorem B1941435 : Blo 1941435 1941435 := bstep (se 1 (by rfl) ⟨1456076, by rfl⟩ : syracuseStep 1941435 = 2912153) B2912153
theorem B3594653 : Blo 1941435 3594653 := bbase (se 3 (by rfl) ⟨673997, by rfl⟩ : syracuseStep 3594653 = 1347995) (by norm_num)
theorem B38342965 : Blo 1941435 38342965 := bstep (se 5 (by rfl) ⟨1797326, by rfl⟩ : syracuseStep 38342965 = 3594653) B3594653
theorem B51123953 : Blo 1941435 51123953 := bstep (se 2 (by rfl) ⟨19171482, by rfl⟩ : syracuseStep 51123953 = 38342965) B38342965
theorem B136330541 : Blo 1941435 136330541 := bstep (se 3 (by rfl) ⟨25561976, by rfl⟩ : syracuseStep 136330541 = 51123953) B51123953
theorem B90887027 : Blo 1941435 90887027 := bstep (se 1 (by rfl) ⟨68165270, by rfl⟩ : syracuseStep 90887027 = 136330541) B136330541
theorem B242365405 : Blo 1941435 242365405 := bstep (se 3 (by rfl) ⟨45443513, by rfl⟩ : syracuseStep 242365405 = 90887027) B90887027
theorem B323153873 : Blo 1941435 323153873 := bstep (se 2 (by rfl) ⟨121182702, by rfl⟩ : syracuseStep 323153873 = 242365405) B242365405
theorem B215435915 : Blo 1941435 215435915 := bstep (se 1 (by rfl) ⟨161576936, by rfl⟩ : syracuseStep 215435915 = 323153873) B323153873
theorem B143623943 : Blo 1941435 143623943 := bstep (se 1 (by rfl) ⟨107717957, by rfl⟩ : syracuseStep 143623943 = 215435915) B215435915
theorem B95749295 : Blo 1941435 95749295 := bstep (se 1 (by rfl) ⟨71811971, by rfl⟩ : syracuseStep 95749295 = 143623943) B143623943
theorem B255331453 : Blo 1941435 255331453 := bstep (se 3 (by rfl) ⟨47874647, by rfl⟩ : syracuseStep 255331453 = 95749295) B95749295
theorem B340441937 : Blo 1941435 340441937 := bstep (se 2 (by rfl) ⟨127665726, by rfl⟩ : syracuseStep 340441937 = 255331453) B255331453
theorem B226961291 : Blo 1941435 226961291 := bstep (se 1 (by rfl) ⟨170220968, by rfl⟩ : syracuseStep 226961291 = 340441937) B340441937
theorem B151307527 : Blo 1941435 151307527 := bstep (se 1 (by rfl) ⟨113480645, by rfl⟩ : syracuseStep 151307527 = 226961291) B226961291
theorem B201743369 : Blo 1941435 201743369 := bstep (se 2 (by rfl) ⟨75653763, by rfl⟩ : syracuseStep 201743369 = 151307527) B151307527
theorem B134495579 : Blo 1941435 134495579 := bstep (se 1 (by rfl) ⟨100871684, by rfl⟩ : syracuseStep 134495579 = 201743369) B201743369
theorem B89663719 : Blo 1941435 89663719 := bstep (se 1 (by rfl) ⟨67247789, by rfl⟩ : syracuseStep 89663719 = 134495579) B134495579
theorem B119551625 : Blo 1941435 119551625 := bstep (se 2 (by rfl) ⟨44831859, by rfl⟩ : syracuseStep 119551625 = 89663719) B89663719
theorem B79701083 : Blo 1941435 79701083 := bstep (se 1 (by rfl) ⟨59775812, by rfl⟩ : syracuseStep 79701083 = 119551625) B119551625
theorem B53134055 : Blo 1941435 53134055 := bstep (se 1 (by rfl) ⟨39850541, by rfl⟩ : syracuseStep 53134055 = 79701083) B79701083
theorem B35422703 : Blo 1941435 35422703 := bstep (se 1 (by rfl) ⟨26567027, by rfl⟩ : syracuseStep 35422703 = 53134055) B53134055
theorem B23615135 : Blo 1941435 23615135 := bstep (se 1 (by rfl) ⟨17711351, by rfl⟩ : syracuseStep 23615135 = 35422703) B35422703
theorem B15743423 : Blo 1941435 15743423 := bstep (se 1 (by rfl) ⟨11807567, by rfl⟩ : syracuseStep 15743423 = 23615135) B23615135
theorem B10495615 : Blo 1941435 10495615 := bstep (se 1 (by rfl) ⟨7871711, by rfl⟩ : syracuseStep 10495615 = 15743423) B15743423
theorem B13994153 : Blo 1941435 13994153 := bstep (se 2 (by rfl) ⟨5247807, by rfl⟩ : syracuseStep 13994153 = 10495615) B10495615
theorem B9329435 : Blo 1941435 9329435 := bstep (se 1 (by rfl) ⟨6997076, by rfl⟩ : syracuseStep 9329435 = 13994153) B13994153
theorem B6219623 : Blo 1941435 6219623 := bstep (se 1 (by rfl) ⟨4664717, by rfl⟩ : syracuseStep 6219623 = 9329435) B9329435
theorem B16585661 : Blo 1941435 16585661 := bstep (se 3 (by rfl) ⟨3109811, by rfl⟩ : syracuseStep 16585661 = 6219623) B6219623
theorem B11057107 : Blo 1941435 11057107 := bstep (se 1 (by rfl) ⟨8292830, by rfl⟩ : syracuseStep 11057107 = 16585661) B16585661
theorem B14742809 : Blo 1941435 14742809 := bstep (se 2 (by rfl) ⟨5528553, by rfl⟩ : syracuseStep 14742809 = 11057107) B11057107
theorem B9828539 : Blo 1941435 9828539 := bstep (se 1 (by rfl) ⟨7371404, by rfl⟩ : syracuseStep 9828539 = 14742809) B14742809
theorem B6552359 : Blo 1941435 6552359 := bstep (se 1 (by rfl) ⟨4914269, by rfl⟩ : syracuseStep 6552359 = 9828539) B9828539
theorem B4368239 : Blo 1941435 4368239 := bstep (se 1 (by rfl) ⟨3276179, by rfl⟩ : syracuseStep 4368239 = 6552359) B6552359
theorem B2912159 : Blo 1941435 2912159 := bstep (se 1 (by rfl) ⟨2184119, by rfl⟩ : syracuseStep 2912159 = 4368239) B4368239
theorem B1941439 : Blo 1941435 1941439 := bstep (se 1 (by rfl) ⟨1456079, by rfl⟩ : syracuseStep 1941439 = 2912159) B2912159
theorem B2912165 : Blo 1941435 2912165 := bbase (se 4 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 2912165 = 546031) (by norm_num)
theorem B1941443 : Blo 1941435 1941443 := bstep (se 1 (by rfl) ⟨1456082, by rfl⟩ : syracuseStep 1941443 = 2912165) B2912165
theorem B2457145 : Blo 1941435 2457145 := bbase (se 2 (by rfl) ⟨921429, by rfl⟩ : syracuseStep 2457145 = 1842859) (by norm_num)
theorem B3276193 : Blo 1941435 3276193 := bstep (se 2 (by rfl) ⟨1228572, by rfl⟩ : syracuseStep 3276193 = 2457145) B2457145
theorem B4368257 : Blo 1941435 4368257 := bstep (se 2 (by rfl) ⟨1638096, by rfl⟩ : syracuseStep 4368257 = 3276193) B3276193
theorem B2912171 : Blo 1941435 2912171 := bstep (se 1 (by rfl) ⟨2184128, by rfl⟩ : syracuseStep 2912171 = 4368257) B4368257
theorem B1941447 : Blo 1941435 1941447 := bstep (se 1 (by rfl) ⟨1456085, by rfl⟩ : syracuseStep 1941447 = 2912171) B2912171
theorem B2184133 : Blo 1941435 2184133 := bbase (se 4 (by rfl) ⟨204762, by rfl⟩ : syracuseStep 2184133 = 409525) (by norm_num)
theorem B2912177 : Blo 1941435 2912177 := bstep (se 2 (by rfl) ⟨1092066, by rfl⟩ : syracuseStep 2912177 = 2184133) B2184133
theorem B1941451 : Blo 1941435 1941451 := bstep (se 1 (by rfl) ⟨1456088, by rfl⟩ : syracuseStep 1941451 = 2912177) B2912177
theorem B3685733 : Blo 1941435 3685733 := bbase (se 4 (by rfl) ⟨345537, by rfl⟩ : syracuseStep 3685733 = 691075) (by norm_num)
theorem B2457155 : Blo 1941435 2457155 := bstep (se 1 (by rfl) ⟨1842866, by rfl⟩ : syracuseStep 2457155 = 3685733) B3685733
theorem B6552413 : Blo 1941435 6552413 := bstep (se 3 (by rfl) ⟨1228577, by rfl⟩ : syracuseStep 6552413 = 2457155) B2457155
theorem B4368275 : Blo 1941435 4368275 := bstep (se 1 (by rfl) ⟨3276206, by rfl⟩ : syracuseStep 4368275 = 6552413) B6552413
theorem B2912183 : Blo 1941435 2912183 := bstep (se 1 (by rfl) ⟨2184137, by rfl⟩ : syracuseStep 2912183 = 4368275) B4368275
theorem B1941455 : Blo 1941435 1941455 := bstep (se 1 (by rfl) ⟨1456091, by rfl⟩ : syracuseStep 1941455 = 2912183) B2912183
theorem B2912189 : Blo 1941435 2912189 := bbase (se 3 (by rfl) ⟨546035, by rfl⟩ : syracuseStep 2912189 = 1092071) (by norm_num)
theorem B1941459 : Blo 1941435 1941459 := bstep (se 1 (by rfl) ⟨1456094, by rfl⟩ : syracuseStep 1941459 = 2912189) B2912189
theorem B4368293 : Blo 1941435 4368293 := bbase (se 4 (by rfl) ⟨409527, by rfl⟩ : syracuseStep 4368293 = 819055) (by norm_num)
theorem B2912195 : Blo 1941435 2912195 := bstep (se 1 (by rfl) ⟨2184146, by rfl⟩ : syracuseStep 2912195 = 4368293) B4368293
theorem B1941463 : Blo 1941435 1941463 := bstep (se 1 (by rfl) ⟨1456097, by rfl⟩ : syracuseStep 1941463 = 2912195) B2912195
theorem B4914341 : Blo 1941435 4914341 := bbase (se 4 (by rfl) ⟨460719, by rfl⟩ : syracuseStep 4914341 = 921439) (by norm_num)
theorem B3276227 : Blo 1941435 3276227 := bstep (se 1 (by rfl) ⟨2457170, by rfl⟩ : syracuseStep 3276227 = 4914341) B4914341
theorem B2184151 : Blo 1941435 2184151 := bstep (se 1 (by rfl) ⟨1638113, by rfl⟩ : syracuseStep 2184151 = 3276227) B3276227
theorem B2912201 : Blo 1941435 2912201 := bstep (se 2 (by rfl) ⟨1092075, by rfl⟩ : syracuseStep 2912201 = 2184151) B2184151
theorem B1941467 : Blo 1941435 1941467 := bstep (se 1 (by rfl) ⟨1456100, by rfl⟩ : syracuseStep 1941467 = 2912201) B2912201
theorem B5528645 : Blo 1941435 5528645 := bbase (se 4 (by rfl) ⟨518310, by rfl⟩ : syracuseStep 5528645 = 1036621) (by norm_num)
theorem B3685763 : Blo 1941435 3685763 := bstep (se 1 (by rfl) ⟨2764322, by rfl⟩ : syracuseStep 3685763 = 5528645) B5528645
theorem B9828701 : Blo 1941435 9828701 := bstep (se 3 (by rfl) ⟨1842881, by rfl⟩ : syracuseStep 9828701 = 3685763) B3685763
theorem B6552467 : Blo 1941435 6552467 := bstep (se 1 (by rfl) ⟨4914350, by rfl⟩ : syracuseStep 6552467 = 9828701) B9828701
theorem B4368311 : Blo 1941435 4368311 := bstep (se 1 (by rfl) ⟨3276233, by rfl⟩ : syracuseStep 4368311 = 6552467) B6552467
theorem B2912207 : Blo 1941435 2912207 := bstep (se 1 (by rfl) ⟨2184155, by rfl⟩ : syracuseStep 2912207 = 4368311) B4368311
theorem B1941471 : Blo 1941435 1941471 := bstep (se 1 (by rfl) ⟨1456103, by rfl⟩ : syracuseStep 1941471 = 2912207) B2912207
theorem B2912213 : Blo 1941435 2912213 := bbase (se 7 (by rfl) ⟨34127, by rfl⟩ : syracuseStep 2912213 = 68255) (by norm_num)
theorem B1941475 : Blo 1941435 1941475 := bstep (se 1 (by rfl) ⟨1456106, by rfl⟩ : syracuseStep 1941475 = 2912213) B2912213
theorem B7371557 : Blo 1941435 7371557 := bbase (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) (by norm_num)
theorem B4914371 : Blo 1941435 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B3276247 : Blo 1941435 3276247 := bstep (se 1 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 3276247 = 4914371) B4914371
theorem B4368329 : Blo 1941435 4368329 := bstep (se 2 (by rfl) ⟨1638123, by rfl⟩ : syracuseStep 4368329 = 3276247) B3276247
theorem B2912219 : Blo 1941435 2912219 := bstep (se 1 (by rfl) ⟨2184164, by rfl⟩ : syracuseStep 2912219 = 4368329) B4368329
theorem B1941479 : Blo 1941435 1941479 := bstep (se 1 (by rfl) ⟨1456109, by rfl⟩ : syracuseStep 1941479 = 2912219) B2912219
theorem B2184169 : Blo 1941435 2184169 := bbase (se 2 (by rfl) ⟨819063, by rfl⟩ : syracuseStep 2184169 = 1638127) (by norm_num)
theorem B2912225 : Blo 1941435 2912225 := bstep (se 2 (by rfl) ⟨1092084, by rfl⟩ : syracuseStep 2912225 = 2184169) B2184169
theorem B1941483 : Blo 1941435 1941483 := bstep (se 1 (by rfl) ⟨1456112, by rfl⟩ : syracuseStep 1941483 = 2912225) B2912225
theorem B2332417 : Blo 1941435 2332417 := bbase (se 2 (by rfl) ⟨874656, by rfl⟩ : syracuseStep 2332417 = 1749313) (by norm_num)
theorem B3109889 : Blo 1941435 3109889 := bstep (se 2 (by rfl) ⟨1166208, by rfl⟩ : syracuseStep 3109889 = 2332417) B2332417
theorem B2073259 : Blo 1941435 2073259 := bstep (se 1 (by rfl) ⟨1554944, by rfl⟩ : syracuseStep 2073259 = 3109889) B3109889
theorem B11057381 : Blo 1941435 11057381 := bstep (se 4 (by rfl) ⟨1036629, by rfl⟩ : syracuseStep 11057381 = 2073259) B2073259
theorem B7371587 : Blo 1941435 7371587 := bstep (se 1 (by rfl) ⟨5528690, by rfl⟩ : syracuseStep 7371587 = 11057381) B11057381
theorem B4914391 : Blo 1941435 4914391 := bstep (se 1 (by rfl) ⟨3685793, by rfl⟩ : syracuseStep 4914391 = 7371587) B7371587
theorem B6552521 : Blo 1941435 6552521 := bstep (se 2 (by rfl) ⟨2457195, by rfl⟩ : syracuseStep 6552521 = 4914391) B4914391
theorem B4368347 : Blo 1941435 4368347 := bstep (se 1 (by rfl) ⟨3276260, by rfl⟩ : syracuseStep 4368347 = 6552521) B6552521
theorem B2912231 : Blo 1941435 2912231 := bstep (se 1 (by rfl) ⟨2184173, by rfl⟩ : syracuseStep 2912231 = 4368347) B4368347
theorem B1941487 : Blo 1941435 1941487 := bstep (se 1 (by rfl) ⟨1456115, by rfl⟩ : syracuseStep 1941487 = 2912231) B2912231
theorem B2912237 : Blo 1941435 2912237 := bbase (se 3 (by rfl) ⟨546044, by rfl⟩ : syracuseStep 2912237 = 1092089) (by norm_num)
theorem B1941491 : Blo 1941435 1941491 := bstep (se 1 (by rfl) ⟨1456118, by rfl⟩ : syracuseStep 1941491 = 2912237) B2912237
theorem B4368365 : Blo 1941435 4368365 := bbase (se 3 (by rfl) ⟨819068, by rfl⟩ : syracuseStep 4368365 = 1638137) (by norm_num)
theorem B2912243 : Blo 1941435 2912243 := bstep (se 1 (by rfl) ⟨2184182, by rfl⟩ : syracuseStep 2912243 = 4368365) B4368365
theorem B1941495 : Blo 1941435 1941495 := bstep (se 1 (by rfl) ⟨1456121, by rfl⟩ : syracuseStep 1941495 = 2912243) B2912243
theorem B3109909 : Blo 1941435 3109909 := bbase (se 6 (by rfl) ⟨72888, by rfl⟩ : syracuseStep 3109909 = 145777) (by norm_num)
theorem B4146545 : Blo 1941435 4146545 := bstep (se 2 (by rfl) ⟨1554954, by rfl⟩ : syracuseStep 4146545 = 3109909) B3109909
theorem B2764363 : Blo 1941435 2764363 := bstep (se 1 (by rfl) ⟨2073272, by rfl⟩ : syracuseStep 2764363 = 4146545) B4146545
theorem B3685817 : Blo 1941435 3685817 := bstep (se 2 (by rfl) ⟨1382181, by rfl⟩ : syracuseStep 3685817 = 2764363) B2764363
theorem B2457211 : Blo 1941435 2457211 := bstep (se 1 (by rfl) ⟨1842908, by rfl⟩ : syracuseStep 2457211 = 3685817) B3685817
theorem B3276281 : Blo 1941435 3276281 := bstep (se 2 (by rfl) ⟨1228605, by rfl⟩ : syracuseStep 3276281 = 2457211) B2457211
theorem B2184187 : Blo 1941435 2184187 := bstep (se 1 (by rfl) ⟨1638140, by rfl⟩ : syracuseStep 2184187 = 3276281) B3276281
theorem B2912249 : Blo 1941435 2912249 := bstep (se 2 (by rfl) ⟨1092093, by rfl⟩ : syracuseStep 2912249 = 2184187) B2184187
theorem B1941499 : Blo 1941435 1941499 := bstep (se 1 (by rfl) ⟨1456124, by rfl⟩ : syracuseStep 1941499 = 2912249) B2912249
theorem B20197781 : Blo 1941435 20197781 := bbase (se 6 (by rfl) ⟨473385, by rfl⟩ : syracuseStep 20197781 = 946771) (by norm_num)
theorem B13465187 : Blo 1941435 13465187 := bstep (se 1 (by rfl) ⟨10098890, by rfl⟩ : syracuseStep 13465187 = 20197781) B20197781
theorem B8976791 : Blo 1941435 8976791 := bstep (se 1 (by rfl) ⟨6732593, by rfl⟩ : syracuseStep 8976791 = 13465187) B13465187
theorem B23938109 : Blo 1941435 23938109 := bstep (se 3 (by rfl) ⟨4488395, by rfl⟩ : syracuseStep 23938109 = 8976791) B8976791
theorem B15958739 : Blo 1941435 15958739 := bstep (se 1 (by rfl) ⟨11969054, by rfl⟩ : syracuseStep 15958739 = 23938109) B23938109
theorem B42556637 : Blo 1941435 42556637 := bstep (se 3 (by rfl) ⟨7979369, by rfl⟩ : syracuseStep 42556637 = 15958739) B15958739
theorem B113484365 : Blo 1941435 113484365 := bstep (se 3 (by rfl) ⟨21278318, by rfl⟩ : syracuseStep 113484365 = 42556637) B42556637
theorem B75656243 : Blo 1941435 75656243 := bstep (se 1 (by rfl) ⟨56742182, by rfl⟩ : syracuseStep 75656243 = 113484365) B113484365
theorem B50437495 : Blo 1941435 50437495 := bstep (se 1 (by rfl) ⟨37828121, by rfl⟩ : syracuseStep 50437495 = 75656243) B75656243
theorem B67249993 : Blo 1941435 67249993 := bstep (se 2 (by rfl) ⟨25218747, by rfl⟩ : syracuseStep 67249993 = 50437495) B50437495
theorem B89666657 : Blo 1941435 89666657 := bstep (se 2 (by rfl) ⟨33624996, by rfl⟩ : syracuseStep 89666657 = 67249993) B67249993
theorem B59777771 : Blo 1941435 59777771 := bstep (se 1 (by rfl) ⟨44833328, by rfl⟩ : syracuseStep 59777771 = 89666657) B89666657
theorem B159407389 : Blo 1941435 159407389 := bstep (se 3 (by rfl) ⟨29888885, by rfl⟩ : syracuseStep 159407389 = 59777771) B59777771
theorem B212543185 : Blo 1941435 212543185 := bstep (se 2 (by rfl) ⟨79703694, by rfl⟩ : syracuseStep 212543185 = 159407389) B159407389
theorem B283390913 : Blo 1941435 283390913 := bstep (se 2 (by rfl) ⟨106271592, by rfl⟩ : syracuseStep 283390913 = 212543185) B212543185
theorem B188927275 : Blo 1941435 188927275 := bstep (se 1 (by rfl) ⟨141695456, by rfl⟩ : syracuseStep 188927275 = 283390913) B283390913
theorem B251903033 : Blo 1941435 251903033 := bstep (se 2 (by rfl) ⟨94463637, by rfl⟩ : syracuseStep 251903033 = 188927275) B188927275
theorem B167935355 : Blo 1941435 167935355 := bstep (se 1 (by rfl) ⟨125951516, by rfl⟩ : syracuseStep 167935355 = 251903033) B251903033
theorem B111956903 : Blo 1941435 111956903 := bstep (se 1 (by rfl) ⟨83967677, by rfl⟩ : syracuseStep 111956903 = 167935355) B167935355
theorem B74637935 : Blo 1941435 74637935 := bstep (se 1 (by rfl) ⟨55978451, by rfl⟩ : syracuseStep 74637935 = 111956903) B111956903
theorem B49758623 : Blo 1941435 49758623 := bstep (se 1 (by rfl) ⟨37318967, by rfl⟩ : syracuseStep 49758623 = 74637935) B74637935
theorem B33172415 : Blo 1941435 33172415 := bstep (se 1 (by rfl) ⟨24879311, by rfl⟩ : syracuseStep 33172415 = 49758623) B49758623
theorem B22114943 : Blo 1941435 22114943 := bstep (se 1 (by rfl) ⟨16586207, by rfl⟩ : syracuseStep 22114943 = 33172415) B33172415
theorem B14743295 : Blo 1941435 14743295 := bstep (se 1 (by rfl) ⟨11057471, by rfl⟩ : syracuseStep 14743295 = 22114943) B22114943
theorem B9828863 : Blo 1941435 9828863 := bstep (se 1 (by rfl) ⟨7371647, by rfl⟩ : syracuseStep 9828863 = 14743295) B14743295
theorem B6552575 : Blo 1941435 6552575 := bstep (se 1 (by rfl) ⟨4914431, by rfl⟩ : syracuseStep 6552575 = 9828863) B9828863
theorem B4368383 : Blo 1941435 4368383 := bstep (se 1 (by rfl) ⟨3276287, by rfl⟩ : syracuseStep 4368383 = 6552575) B6552575
theorem B2912255 : Blo 1941435 2912255 := bstep (se 1 (by rfl) ⟨2184191, by rfl⟩ : syracuseStep 2912255 = 4368383) B4368383
theorem B1941503 : Blo 1941435 1941503 := bstep (se 1 (by rfl) ⟨1456127, by rfl⟩ : syracuseStep 1941503 = 2912255) B2912255
theorem B2912261 : Blo 1941435 2912261 := bbase (se 4 (by rfl) ⟨273024, by rfl⟩ : syracuseStep 2912261 = 546049) (by norm_num)
theorem B1941507 : Blo 1941435 1941507 := bstep (se 1 (by rfl) ⟨1456130, by rfl⟩ : syracuseStep 1941507 = 2912261) B2912261
theorem B3276301 : Blo 1941435 3276301 := bbase (se 3 (by rfl) ⟨614306, by rfl⟩ : syracuseStep 3276301 = 1228613) (by norm_num)
theorem B4368401 : Blo 1941435 4368401 := bstep (se 2 (by rfl) ⟨1638150, by rfl⟩ : syracuseStep 4368401 = 3276301) B3276301
theorem B2912267 : Blo 1941435 2912267 := bstep (se 1 (by rfl) ⟨2184200, by rfl⟩ : syracuseStep 2912267 = 4368401) B4368401
theorem B1941511 : Blo 1941435 1941511 := bstep (se 1 (by rfl) ⟨1456133, by rfl⟩ : syracuseStep 1941511 = 2912267) B2912267
theorem B2184205 : Blo 1941435 2184205 := bbase (se 3 (by rfl) ⟨409538, by rfl⟩ : syracuseStep 2184205 = 819077) (by norm_num)
theorem B2912273 : Blo 1941435 2912273 := bstep (se 2 (by rfl) ⟨1092102, by rfl⟩ : syracuseStep 2912273 = 2184205) B2184205
theorem B1941515 : Blo 1941435 1941515 := bstep (se 1 (by rfl) ⟨1456136, by rfl⟩ : syracuseStep 1941515 = 2912273) B2912273
theorem B6552629 : Blo 1941435 6552629 := bbase (se 5 (by rfl) ⟨307154, by rfl⟩ : syracuseStep 6552629 = 614309) (by norm_num)
theorem B4368419 : Blo 1941435 4368419 := bstep (se 1 (by rfl) ⟨3276314, by rfl⟩ : syracuseStep 4368419 = 6552629) B6552629
theorem B2912279 : Blo 1941435 2912279 := bstep (se 1 (by rfl) ⟨2184209, by rfl⟩ : syracuseStep 2912279 = 4368419) B4368419
theorem B1941519 : Blo 1941435 1941519 := bstep (se 1 (by rfl) ⟨1456139, by rfl⟩ : syracuseStep 1941519 = 2912279) B2912279
theorem B2912285 : Blo 1941435 2912285 := bbase (se 3 (by rfl) ⟨546053, by rfl⟩ : syracuseStep 2912285 = 1092107) (by norm_num)
theorem B1941523 : Blo 1941435 1941523 := bstep (se 1 (by rfl) ⟨1456142, by rfl⟩ : syracuseStep 1941523 = 2912285) B2912285
theorem B4368437 : Blo 1941435 4368437 := bbase (se 5 (by rfl) ⟨204770, by rfl⟩ : syracuseStep 4368437 = 409541) (by norm_num)
theorem B2912291 : Blo 1941435 2912291 := bstep (se 1 (by rfl) ⟨2184218, by rfl⟩ : syracuseStep 2912291 = 4368437) B4368437
theorem B1941527 : Blo 1941435 1941527 := bstep (se 1 (by rfl) ⟨1456145, by rfl⟩ : syracuseStep 1941527 = 2912291) B2912291
theorem B3321037 : Blo 1941435 3321037 := bbase (se 3 (by rfl) ⟨622694, by rfl⟩ : syracuseStep 3321037 = 1245389) (by norm_num)
theorem B4428049 : Blo 1941435 4428049 := bstep (se 2 (by rfl) ⟨1660518, by rfl⟩ : syracuseStep 4428049 = 3321037) B3321037
theorem B5904065 : Blo 1941435 5904065 := bstep (se 2 (by rfl) ⟨2214024, by rfl⟩ : syracuseStep 5904065 = 4428049) B4428049
theorem B3936043 : Blo 1941435 3936043 := bstep (se 1 (by rfl) ⟨2952032, by rfl⟩ : syracuseStep 3936043 = 5904065) B5904065
theorem B20992229 : Blo 1941435 20992229 := bstep (se 4 (by rfl) ⟨1968021, by rfl⟩ : syracuseStep 20992229 = 3936043) B3936043
theorem B13994819 : Blo 1941435 13994819 := bstep (se 1 (by rfl) ⟨10496114, by rfl⟩ : syracuseStep 13994819 = 20992229) B20992229
theorem B9329879 : Blo 1941435 9329879 := bstep (se 1 (by rfl) ⟨6997409, by rfl⟩ : syracuseStep 9329879 = 13994819) B13994819
theorem B6219919 : Blo 1941435 6219919 := bstep (se 1 (by rfl) ⟨4664939, by rfl⟩ : syracuseStep 6219919 = 9329879) B9329879
theorem B8293225 : Blo 1941435 8293225 := bstep (se 2 (by rfl) ⟨3109959, by rfl⟩ : syracuseStep 8293225 = 6219919) B6219919
theorem B11057633 : Blo 1941435 11057633 := bstep (se 2 (by rfl) ⟨4146612, by rfl⟩ : syracuseStep 11057633 = 8293225) B8293225
theorem B7371755 : Blo 1941435 7371755 := bstep (se 1 (by rfl) ⟨5528816, by rfl⟩ : syracuseStep 7371755 = 11057633) B11057633
theorem B4914503 : Blo 1941435 4914503 := bstep (se 1 (by rfl) ⟨3685877, by rfl⟩ : syracuseStep 4914503 = 7371755) B7371755
theorem B3276335 : Blo 1941435 3276335 := bstep (se 1 (by rfl) ⟨2457251, by rfl⟩ : syracuseStep 3276335 = 4914503) B4914503
theorem B2184223 : Blo 1941435 2184223 := bstep (se 1 (by rfl) ⟨1638167, by rfl⟩ : syracuseStep 2184223 = 3276335) B3276335
theorem B2912297 : Blo 1941435 2912297 := bstep (se 2 (by rfl) ⟨1092111, by rfl⟩ : syracuseStep 2912297 = 2184223) B2184223
theorem B1941531 : Blo 1941435 1941531 := bstep (se 1 (by rfl) ⟨1456148, by rfl⟩ : syracuseStep 1941531 = 2912297) B2912297
theorem B4981565 : Blo 1941435 4981565 := bbase (se 3 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 4981565 = 1868087) (by norm_num)
theorem B3321043 : Blo 1941435 3321043 := bstep (se 1 (by rfl) ⟨2490782, by rfl⟩ : syracuseStep 3321043 = 4981565) B4981565
theorem B17712229 : Blo 1941435 17712229 := bstep (se 4 (by rfl) ⟨1660521, by rfl⟩ : syracuseStep 17712229 = 3321043) B3321043
theorem B23616305 : Blo 1941435 23616305 := bstep (se 2 (by rfl) ⟨8856114, by rfl⟩ : syracuseStep 23616305 = 17712229) B17712229
theorem B15744203 : Blo 1941435 15744203 := bstep (se 1 (by rfl) ⟨11808152, by rfl⟩ : syracuseStep 15744203 = 23616305) B23616305
theorem B10496135 : Blo 1941435 10496135 := bstep (se 1 (by rfl) ⟨7872101, by rfl⟩ : syracuseStep 10496135 = 15744203) B15744203
theorem B6997423 : Blo 1941435 6997423 := bstep (se 1 (by rfl) ⟨5248067, by rfl⟩ : syracuseStep 6997423 = 10496135) B10496135
theorem B9329897 : Blo 1941435 9329897 := bstep (se 2 (by rfl) ⟨3498711, by rfl⟩ : syracuseStep 9329897 = 6997423) B6997423
theorem B6219931 : Blo 1941435 6219931 := bstep (se 1 (by rfl) ⟨4664948, by rfl⟩ : syracuseStep 6219931 = 9329897) B9329897
theorem B8293241 : Blo 1941435 8293241 := bstep (se 2 (by rfl) ⟨3109965, by rfl⟩ : syracuseStep 8293241 = 6219931) B6219931
theorem B5528827 : Blo 1941435 5528827 := bstep (se 1 (by rfl) ⟨4146620, by rfl⟩ : syracuseStep 5528827 = 8293241) B8293241
theorem B7371769 : Blo 1941435 7371769 := bstep (se 2 (by rfl) ⟨2764413, by rfl⟩ : syracuseStep 7371769 = 5528827) B5528827
theorem B9829025 : Blo 1941435 9829025 := bstep (se 2 (by rfl) ⟨3685884, by rfl⟩ : syracuseStep 9829025 = 7371769) B7371769
theorem B6552683 : Blo 1941435 6552683 := bstep (se 1 (by rfl) ⟨4914512, by rfl⟩ : syracuseStep 6552683 = 9829025) B9829025
theorem B4368455 : Blo 1941435 4368455 := bstep (se 1 (by rfl) ⟨3276341, by rfl⟩ : syracuseStep 4368455 = 6552683) B6552683
theorem B2912303 : Blo 1941435 2912303 := bstep (se 1 (by rfl) ⟨2184227, by rfl⟩ : syracuseStep 2912303 = 4368455) B4368455
theorem B1941535 : Blo 1941435 1941535 := bstep (se 1 (by rfl) ⟨1456151, by rfl⟩ : syracuseStep 1941535 = 2912303) B2912303
theorem B2912309 : Blo 1941435 2912309 := bbase (se 5 (by rfl) ⟨136514, by rfl⟩ : syracuseStep 2912309 = 273029) (by norm_num)
theorem B1941539 : Blo 1941435 1941539 := bstep (se 1 (by rfl) ⟨1456154, by rfl⟩ : syracuseStep 1941539 = 2912309) B2912309
theorem B4914533 : Blo 1941435 4914533 := bbase (se 4 (by rfl) ⟨460737, by rfl⟩ : syracuseStep 4914533 = 921475) (by norm_num)
theorem B3276355 : Blo 1941435 3276355 := bstep (se 1 (by rfl) ⟨2457266, by rfl⟩ : syracuseStep 3276355 = 4914533) B4914533
theorem B4368473 : Blo 1941435 4368473 := bstep (se 2 (by rfl) ⟨1638177, by rfl⟩ : syracuseStep 4368473 = 3276355) B3276355
theorem B2912315 : Blo 1941435 2912315 := bstep (se 1 (by rfl) ⟨2184236, by rfl⟩ : syracuseStep 2912315 = 4368473) B4368473
theorem B1941543 : Blo 1941435 1941543 := bstep (se 1 (by rfl) ⟨1456157, by rfl⟩ : syracuseStep 1941543 = 2912315) B2912315
theorem B2184241 : Blo 1941435 2184241 := bbase (se 2 (by rfl) ⟨819090, by rfl⟩ : syracuseStep 2184241 = 1638181) (by norm_num)
theorem B2912321 : Blo 1941435 2912321 := bstep (se 2 (by rfl) ⟨1092120, by rfl⟩ : syracuseStep 2912321 = 2184241) B2184241
theorem B1941547 : Blo 1941435 1941547 := bstep (se 1 (by rfl) ⟨1456160, by rfl⟩ : syracuseStep 1941547 = 2912321) B2912321
theorem B7979573 : Blo 1941435 7979573 := bbase (se 5 (by rfl) ⟨374042, by rfl⟩ : syracuseStep 7979573 = 748085) (by norm_num)
theorem B5319715 : Blo 1941435 5319715 := bstep (se 1 (by rfl) ⟨3989786, by rfl⟩ : syracuseStep 5319715 = 7979573) B7979573
theorem B7092953 : Blo 1941435 7092953 := bstep (se 2 (by rfl) ⟨2659857, by rfl⟩ : syracuseStep 7092953 = 5319715) B5319715
theorem B4728635 : Blo 1941435 4728635 := bstep (se 1 (by rfl) ⟨3546476, by rfl⟩ : syracuseStep 4728635 = 7092953) B7092953
theorem B3152423 : Blo 1941435 3152423 := bstep (se 1 (by rfl) ⟨2364317, by rfl⟩ : syracuseStep 3152423 = 4728635) B4728635
theorem B8406461 : Blo 1941435 8406461 := bstep (se 3 (by rfl) ⟨1576211, by rfl⟩ : syracuseStep 8406461 = 3152423) B3152423
theorem B22417229 : Blo 1941435 22417229 := bstep (se 3 (by rfl) ⟨4203230, by rfl⟩ : syracuseStep 22417229 = 8406461) B8406461
theorem B14944819 : Blo 1941435 14944819 := bstep (se 1 (by rfl) ⟨11208614, by rfl⟩ : syracuseStep 14944819 = 22417229) B22417229
theorem B19926425 : Blo 1941435 19926425 := bstep (se 2 (by rfl) ⟨7472409, by rfl⟩ : syracuseStep 19926425 = 14944819) B14944819
theorem B13284283 : Blo 1941435 13284283 := bstep (se 1 (by rfl) ⟨9963212, by rfl⟩ : syracuseStep 13284283 = 19926425) B19926425
theorem B17712377 : Blo 1941435 17712377 := bstep (se 2 (by rfl) ⟨6642141, by rfl⟩ : syracuseStep 17712377 = 13284283) B13284283
theorem B11808251 : Blo 1941435 11808251 := bstep (se 1 (by rfl) ⟨8856188, by rfl⟩ : syracuseStep 11808251 = 17712377) B17712377
theorem B7872167 : Blo 1941435 7872167 := bstep (se 1 (by rfl) ⟨5904125, by rfl⟩ : syracuseStep 7872167 = 11808251) B11808251
theorem B20992445 : Blo 1941435 20992445 := bstep (se 3 (by rfl) ⟨3936083, by rfl⟩ : syracuseStep 20992445 = 7872167) B7872167
theorem B13994963 : Blo 1941435 13994963 := bstep (se 1 (by rfl) ⟨10496222, by rfl⟩ : syracuseStep 13994963 = 20992445) B20992445
theorem B9329975 : Blo 1941435 9329975 := bstep (se 1 (by rfl) ⟨6997481, by rfl⟩ : syracuseStep 9329975 = 13994963) B13994963
theorem B6219983 : Blo 1941435 6219983 := bstep (se 1 (by rfl) ⟨4664987, by rfl⟩ : syracuseStep 6219983 = 9329975) B9329975
theorem B4146655 : Blo 1941435 4146655 := bstep (se 1 (by rfl) ⟨3109991, by rfl⟩ : syracuseStep 4146655 = 6219983) B6219983
theorem B5528873 : Blo 1941435 5528873 := bstep (se 2 (by rfl) ⟨2073327, by rfl⟩ : syracuseStep 5528873 = 4146655) B4146655
theorem B3685915 : Blo 1941435 3685915 := bstep (se 1 (by rfl) ⟨2764436, by rfl⟩ : syracuseStep 3685915 = 5528873) B5528873
theorem B4914553 : Blo 1941435 4914553 := bstep (se 2 (by rfl) ⟨1842957, by rfl⟩ : syracuseStep 4914553 = 3685915) B3685915
theorem B6552737 : Blo 1941435 6552737 := bstep (se 2 (by rfl) ⟨2457276, by rfl⟩ : syracuseStep 6552737 = 4914553) B4914553
theorem B4368491 : Blo 1941435 4368491 := bstep (se 1 (by rfl) ⟨3276368, by rfl⟩ : syracuseStep 4368491 = 6552737) B6552737
theorem B2912327 : Blo 1941435 2912327 := bstep (se 1 (by rfl) ⟨2184245, by rfl⟩ : syracuseStep 2912327 = 4368491) B4368491
theorem B1941551 : Blo 1941435 1941551 := bstep (se 1 (by rfl) ⟨1456163, by rfl⟩ : syracuseStep 1941551 = 2912327) B2912327
theorem B2912333 : Blo 1941435 2912333 := bbase (se 3 (by rfl) ⟨546062, by rfl⟩ : syracuseStep 2912333 = 1092125) (by norm_num)
theorem B1941555 : Blo 1941435 1941555 := bstep (se 1 (by rfl) ⟨1456166, by rfl⟩ : syracuseStep 1941555 = 2912333) B2912333
theorem B4368509 : Blo 1941435 4368509 := bbase (se 3 (by rfl) ⟨819095, by rfl⟩ : syracuseStep 4368509 = 1638191) (by norm_num)
theorem B2912339 : Blo 1941435 2912339 := bstep (se 1 (by rfl) ⟨2184254, by rfl⟩ : syracuseStep 2912339 = 4368509) B4368509
theorem B1941559 : Blo 1941435 1941559 := bstep (se 1 (by rfl) ⟨1456169, by rfl⟩ : syracuseStep 1941559 = 2912339) B2912339
theorem B3276389 : Blo 1941435 3276389 := bbase (se 4 (by rfl) ⟨307161, by rfl⟩ : syracuseStep 3276389 = 614323) (by norm_num)
theorem B2184259 : Blo 1941435 2184259 := bstep (se 1 (by rfl) ⟨1638194, by rfl⟩ : syracuseStep 2184259 = 3276389) B3276389
theorem B2912345 : Blo 1941435 2912345 := bstep (se 2 (by rfl) ⟨1092129, by rfl⟩ : syracuseStep 2912345 = 2184259) B2184259
theorem B1941563 : Blo 1941435 1941563 := bstep (se 1 (by rfl) ⟨1456172, by rfl⟩ : syracuseStep 1941563 = 2912345) B2912345
theorem B2332513 : Blo 1941435 2332513 := bbase (se 2 (by rfl) ⟨874692, by rfl⟩ : syracuseStep 2332513 = 1749385) (by norm_num)
theorem B3110017 : Blo 1941435 3110017 := bstep (se 2 (by rfl) ⟨1166256, by rfl⟩ : syracuseStep 3110017 = 2332513) B2332513
theorem B4146689 : Blo 1941435 4146689 := bstep (se 2 (by rfl) ⟨1555008, by rfl⟩ : syracuseStep 4146689 = 3110017) B3110017
theorem B2764459 : Blo 1941435 2764459 := bstep (se 1 (by rfl) ⟨2073344, by rfl⟩ : syracuseStep 2764459 = 4146689) B4146689
theorem B14743781 : Blo 1941435 14743781 := bstep (se 4 (by rfl) ⟨1382229, by rfl⟩ : syracuseStep 14743781 = 2764459) B2764459
theorem B9829187 : Blo 1941435 9829187 := bstep (se 1 (by rfl) ⟨7371890, by rfl⟩ : syracuseStep 9829187 = 14743781) B14743781
theorem B6552791 : Blo 1941435 6552791 := bstep (se 1 (by rfl) ⟨4914593, by rfl⟩ : syracuseStep 6552791 = 9829187) B9829187
theorem B4368527 : Blo 1941435 4368527 := bstep (se 1 (by rfl) ⟨3276395, by rfl⟩ : syracuseStep 4368527 = 6552791) B6552791
theorem B2912351 : Blo 1941435 2912351 := bstep (se 1 (by rfl) ⟨2184263, by rfl⟩ : syracuseStep 2912351 = 4368527) B4368527
theorem B1941567 : Blo 1941435 1941567 := bstep (se 1 (by rfl) ⟨1456175, by rfl⟩ : syracuseStep 1941567 = 2912351) B2912351
theorem B2912357 : Blo 1941435 2912357 := bbase (se 4 (by rfl) ⟨273033, by rfl⟩ : syracuseStep 2912357 = 546067) (by norm_num)
theorem B1941571 : Blo 1941435 1941571 := bstep (se 1 (by rfl) ⟨1456178, by rfl⟩ : syracuseStep 1941571 = 2912357) B2912357
theorem B2952101 : Blo 1941435 2952101 := bbase (se 4 (by rfl) ⟨276759, by rfl⟩ : syracuseStep 2952101 = 553519) (by norm_num)
theorem B1968067 : Blo 1941435 1968067 := bstep (se 1 (by rfl) ⟨1476050, by rfl⟩ : syracuseStep 1968067 = 2952101) B2952101
theorem B2624089 : Blo 1941435 2624089 := bstep (se 2 (by rfl) ⟨984033, by rfl⟩ : syracuseStep 2624089 = 1968067) B1968067
theorem B3498785 : Blo 1941435 3498785 := bstep (se 2 (by rfl) ⟨1312044, by rfl⟩ : syracuseStep 3498785 = 2624089) B2624089
theorem B2332523 : Blo 1941435 2332523 := bstep (se 1 (by rfl) ⟨1749392, by rfl⟩ : syracuseStep 2332523 = 3498785) B3498785
theorem B6220061 : Blo 1941435 6220061 := bstep (se 3 (by rfl) ⟨1166261, by rfl⟩ : syracuseStep 6220061 = 2332523) B2332523
theorem B4146707 : Blo 1941435 4146707 := bstep (se 1 (by rfl) ⟨3110030, by rfl⟩ : syracuseStep 4146707 = 6220061) B6220061
theorem B2764471 : Blo 1941435 2764471 := bstep (se 1 (by rfl) ⟨2073353, by rfl⟩ : syracuseStep 2764471 = 4146707) B4146707
theorem B3685961 : Blo 1941435 3685961 := bstep (se 2 (by rfl) ⟨1382235, by rfl⟩ : syracuseStep 3685961 = 2764471) B2764471
theorem B2457307 : Blo 1941435 2457307 := bstep (se 1 (by rfl) ⟨1842980, by rfl⟩ : syracuseStep 2457307 = 3685961) B3685961
theorem B3276409 : Blo 1941435 3276409 := bstep (se 2 (by rfl) ⟨1228653, by rfl⟩ : syracuseStep 3276409 = 2457307) B2457307
theorem B4368545 : Blo 1941435 4368545 := bstep (se 2 (by rfl) ⟨1638204, by rfl⟩ : syracuseStep 4368545 = 3276409) B3276409
theorem B2912363 : Blo 1941435 2912363 := bstep (se 1 (by rfl) ⟨2184272, by rfl⟩ : syracuseStep 2912363 = 4368545) B4368545
theorem B1941575 : Blo 1941435 1941575 := bstep (se 1 (by rfl) ⟨1456181, by rfl⟩ : syracuseStep 1941575 = 2912363) B2912363
theorem B2184277 : Blo 1941435 2184277 := bbase (se 8 (by rfl) ⟨12798, by rfl⟩ : syracuseStep 2184277 = 25597) (by norm_num)
theorem B2912369 : Blo 1941435 2912369 := bstep (se 2 (by rfl) ⟨1092138, by rfl⟩ : syracuseStep 2912369 = 2184277) B2184277
theorem B1941579 : Blo 1941435 1941579 := bstep (se 1 (by rfl) ⟨1456184, by rfl⟩ : syracuseStep 1941579 = 2912369) B2912369
theorem B2457317 : Blo 1941435 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B6552845 : Blo 1941435 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B4368563 : Blo 1941435 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B2912375 : Blo 1941435 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B1941583 : Blo 1941435 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B2912381 : Blo 1941435 2912381 := bbase (se 3 (by rfl) ⟨546071, by rfl⟩ : syracuseStep 2912381 = 1092143) (by norm_num)
theorem B1941587 : Blo 1941435 1941587 := bstep (se 1 (by rfl) ⟨1456190, by rfl⟩ : syracuseStep 1941587 = 2912381) B2912381
theorem B4368581 : Blo 1941435 4368581 := bbase (se 4 (by rfl) ⟨409554, by rfl⟩ : syracuseStep 4368581 = 819109) (by norm_num)
theorem B2912387 : Blo 1941435 2912387 := bstep (se 1 (by rfl) ⟨2184290, by rfl⟩ : syracuseStep 2912387 = 4368581) B4368581
theorem B1941591 : Blo 1941435 1941591 := bstep (se 1 (by rfl) ⟨1456193, by rfl⟩ : syracuseStep 1941591 = 2912387) B2912387
theorem B3936173 : Blo 1941435 3936173 := bbase (se 3 (by rfl) ⟨738032, by rfl⟩ : syracuseStep 3936173 = 1476065) (by norm_num)
theorem B10496461 : Blo 1941435 10496461 := bstep (se 3 (by rfl) ⟨1968086, by rfl⟩ : syracuseStep 10496461 = 3936173) B3936173
theorem B13995281 : Blo 1941435 13995281 := bstep (se 2 (by rfl) ⟨5248230, by rfl⟩ : syracuseStep 13995281 = 10496461) B10496461
theorem B9330187 : Blo 1941435 9330187 := bstep (se 1 (by rfl) ⟨6997640, by rfl⟩ : syracuseStep 9330187 = 13995281) B13995281
theorem B12440249 : Blo 1941435 12440249 := bstep (se 2 (by rfl) ⟨4665093, by rfl⟩ : syracuseStep 12440249 = 9330187) B9330187
theorem B8293499 : Blo 1941435 8293499 := bstep (se 1 (by rfl) ⟨6220124, by rfl⟩ : syracuseStep 8293499 = 12440249) B12440249
theorem B5528999 : Blo 1941435 5528999 := bstep (se 1 (by rfl) ⟨4146749, by rfl⟩ : syracuseStep 5528999 = 8293499) B8293499
theorem B3685999 : Blo 1941435 3685999 := bstep (se 1 (by rfl) ⟨2764499, by rfl⟩ : syracuseStep 3685999 = 5528999) B5528999
theorem B4914665 : Blo 1941435 4914665 := bstep (se 2 (by rfl) ⟨1842999, by rfl⟩ : syracuseStep 4914665 = 3685999) B3685999
theorem B3276443 : Blo 1941435 3276443 := bstep (se 1 (by rfl) ⟨2457332, by rfl⟩ : syracuseStep 3276443 = 4914665) B4914665
theorem B2184295 : Blo 1941435 2184295 := bstep (se 1 (by rfl) ⟨1638221, by rfl⟩ : syracuseStep 2184295 = 3276443) B3276443
theorem B2912393 : Blo 1941435 2912393 := bstep (se 2 (by rfl) ⟨1092147, by rfl⟩ : syracuseStep 2912393 = 2184295) B2184295
theorem B1941595 : Blo 1941435 1941595 := bstep (se 1 (by rfl) ⟨1456196, by rfl⟩ : syracuseStep 1941595 = 2912393) B2912393
theorem B9829349 : Blo 1941435 9829349 := bbase (se 4 (by rfl) ⟨921501, by rfl⟩ : syracuseStep 9829349 = 1843003) (by norm_num)
theorem B6552899 : Blo 1941435 6552899 := bstep (se 1 (by rfl) ⟨4914674, by rfl⟩ : syracuseStep 6552899 = 9829349) B9829349
theorem B4368599 : Blo 1941435 4368599 := bstep (se 1 (by rfl) ⟨3276449, by rfl⟩ : syracuseStep 4368599 = 6552899) B6552899
theorem B2912399 : Blo 1941435 2912399 := bstep (se 1 (by rfl) ⟨2184299, by rfl⟩ : syracuseStep 2912399 = 4368599) B4368599
theorem B1941599 : Blo 1941435 1941599 := bstep (se 1 (by rfl) ⟨1456199, by rfl⟩ : syracuseStep 1941599 = 2912399) B2912399
theorem B2912405 : Blo 1941435 2912405 := bbase (se 6 (by rfl) ⟨68259, by rfl⟩ : syracuseStep 2912405 = 136519) (by norm_num)
theorem B1941603 : Blo 1941435 1941603 := bstep (se 1 (by rfl) ⟨1456202, by rfl⟩ : syracuseStep 1941603 = 2912405) B2912405
theorem B2332561 : Blo 1941435 2332561 := bbase (se 2 (by rfl) ⟨874710, by rfl⟩ : syracuseStep 2332561 = 1749421) (by norm_num)
theorem B3110081 : Blo 1941435 3110081 := bstep (se 2 (by rfl) ⟨1166280, by rfl⟩ : syracuseStep 3110081 = 2332561) B2332561
theorem B8293549 : Blo 1941435 8293549 := bstep (se 3 (by rfl) ⟨1555040, by rfl⟩ : syracuseStep 8293549 = 3110081) B3110081
theorem B11058065 : Blo 1941435 11058065 := bstep (se 2 (by rfl) ⟨4146774, by rfl⟩ : syracuseStep 11058065 = 8293549) B8293549
theorem B7372043 : Blo 1941435 7372043 := bstep (se 1 (by rfl) ⟨5529032, by rfl⟩ : syracuseStep 7372043 = 11058065) B11058065
theorem B4914695 : Blo 1941435 4914695 := bstep (se 1 (by rfl) ⟨3686021, by rfl⟩ : syracuseStep 4914695 = 7372043) B7372043
theorem B3276463 : Blo 1941435 3276463 := bstep (se 1 (by rfl) ⟨2457347, by rfl⟩ : syracuseStep 3276463 = 4914695) B4914695
theorem B4368617 : Blo 1941435 4368617 := bstep (se 2 (by rfl) ⟨1638231, by rfl⟩ : syracuseStep 4368617 = 3276463) B3276463
theorem B2912411 : Blo 1941435 2912411 := bstep (se 1 (by rfl) ⟨2184308, by rfl⟩ : syracuseStep 2912411 = 4368617) B4368617
theorem B1941607 : Blo 1941435 1941607 := bstep (se 1 (by rfl) ⟨1456205, by rfl⟩ : syracuseStep 1941607 = 2912411) B2912411
theorem B2184313 : Blo 1941435 2184313 := bbase (se 2 (by rfl) ⟨819117, by rfl⟩ : syracuseStep 2184313 = 1638235) (by norm_num)
theorem B2912417 : Blo 1941435 2912417 := bstep (se 2 (by rfl) ⟨1092156, by rfl⟩ : syracuseStep 2912417 = 2184313) B2184313
theorem B1941611 : Blo 1941435 1941611 := bstep (se 1 (by rfl) ⟨1456208, by rfl⟩ : syracuseStep 1941611 = 2912417) B2912417
theorem B4793309 : Blo 1941435 4793309 := bbase (se 3 (by rfl) ⟨898745, by rfl⟩ : syracuseStep 4793309 = 1797491) (by norm_num)
theorem B3195539 : Blo 1941435 3195539 := bstep (se 1 (by rfl) ⟨2396654, by rfl⟩ : syracuseStep 3195539 = 4793309) B4793309
theorem B2130359 : Blo 1941435 2130359 := bstep (se 1 (by rfl) ⟨1597769, by rfl⟩ : syracuseStep 2130359 = 3195539) B3195539
theorem B5680957 : Blo 1941435 5680957 := bstep (se 3 (by rfl) ⟨1065179, by rfl⟩ : syracuseStep 5680957 = 2130359) B2130359
theorem B7574609 : Blo 1941435 7574609 := bstep (se 2 (by rfl) ⟨2840478, by rfl⟩ : syracuseStep 7574609 = 5680957) B5680957
theorem B5049739 : Blo 1941435 5049739 := bstep (se 1 (by rfl) ⟨3787304, by rfl⟩ : syracuseStep 5049739 = 7574609) B7574609
theorem B6732985 : Blo 1941435 6732985 := bstep (se 2 (by rfl) ⟨2524869, by rfl⟩ : syracuseStep 6732985 = 5049739) B5049739
theorem B8977313 : Blo 1941435 8977313 := bstep (se 2 (by rfl) ⟨3366492, by rfl⟩ : syracuseStep 8977313 = 6732985) B6732985
theorem B5984875 : Blo 1941435 5984875 := bstep (se 1 (by rfl) ⟨4488656, by rfl⟩ : syracuseStep 5984875 = 8977313) B8977313
theorem B7979833 : Blo 1941435 7979833 := bstep (se 2 (by rfl) ⟨2992437, by rfl⟩ : syracuseStep 7979833 = 5984875) B5984875
theorem B10639777 : Blo 1941435 10639777 := bstep (se 2 (by rfl) ⟨3989916, by rfl⟩ : syracuseStep 10639777 = 7979833) B7979833
theorem B14186369 : Blo 1941435 14186369 := bstep (se 2 (by rfl) ⟨5319888, by rfl⟩ : syracuseStep 14186369 = 10639777) B10639777
theorem B9457579 : Blo 1941435 9457579 := bstep (se 1 (by rfl) ⟨7093184, by rfl⟩ : syracuseStep 9457579 = 14186369) B14186369
theorem B50440421 : Blo 1941435 50440421 := bstep (se 4 (by rfl) ⟨4728789, by rfl⟩ : syracuseStep 50440421 = 9457579) B9457579
theorem B33626947 : Blo 1941435 33626947 := bstep (se 1 (by rfl) ⟨25220210, by rfl⟩ : syracuseStep 33626947 = 50440421) B50440421
theorem B44835929 : Blo 1941435 44835929 := bstep (se 2 (by rfl) ⟨16813473, by rfl⟩ : syracuseStep 44835929 = 33626947) B33626947
theorem B29890619 : Blo 1941435 29890619 := bstep (se 1 (by rfl) ⟨22417964, by rfl⟩ : syracuseStep 29890619 = 44835929) B44835929
theorem B19927079 : Blo 1941435 19927079 := bstep (se 1 (by rfl) ⟨14945309, by rfl⟩ : syracuseStep 19927079 = 29890619) B29890619
theorem B13284719 : Blo 1941435 13284719 := bstep (se 1 (by rfl) ⟨9963539, by rfl⟩ : syracuseStep 13284719 = 19927079) B19927079
theorem B8856479 : Blo 1941435 8856479 := bstep (se 1 (by rfl) ⟨6642359, by rfl⟩ : syracuseStep 8856479 = 13284719) B13284719
theorem B23617277 : Blo 1941435 23617277 := bstep (se 3 (by rfl) ⟨4428239, by rfl⟩ : syracuseStep 23617277 = 8856479) B8856479
theorem B15744851 : Blo 1941435 15744851 := bstep (se 1 (by rfl) ⟨11808638, by rfl⟩ : syracuseStep 15744851 = 23617277) B23617277
theorem B10496567 : Blo 1941435 10496567 := bstep (se 1 (by rfl) ⟨7872425, by rfl⟩ : syracuseStep 10496567 = 15744851) B15744851
theorem B27990845 : Blo 1941435 27990845 := bstep (se 3 (by rfl) ⟨5248283, by rfl⟩ : syracuseStep 27990845 = 10496567) B10496567
theorem B18660563 : Blo 1941435 18660563 := bstep (se 1 (by rfl) ⟨13995422, by rfl⟩ : syracuseStep 18660563 = 27990845) B27990845
theorem B12440375 : Blo 1941435 12440375 := bstep (se 1 (by rfl) ⟨9330281, by rfl⟩ : syracuseStep 12440375 = 18660563) B18660563
theorem B8293583 : Blo 1941435 8293583 := bstep (se 1 (by rfl) ⟨6220187, by rfl⟩ : syracuseStep 8293583 = 12440375) B12440375
theorem B5529055 : Blo 1941435 5529055 := bstep (se 1 (by rfl) ⟨4146791, by rfl⟩ : syracuseStep 5529055 = 8293583) B8293583
theorem B7372073 : Blo 1941435 7372073 := bstep (se 2 (by rfl) ⟨2764527, by rfl⟩ : syracuseStep 7372073 = 5529055) B5529055
theorem B4914715 : Blo 1941435 4914715 := bstep (se 1 (by rfl) ⟨3686036, by rfl⟩ : syracuseStep 4914715 = 7372073) B7372073
theorem B6552953 : Blo 1941435 6552953 := bstep (se 2 (by rfl) ⟨2457357, by rfl⟩ : syracuseStep 6552953 = 4914715) B4914715
theorem B4368635 : Blo 1941435 4368635 := bstep (se 1 (by rfl) ⟨3276476, by rfl⟩ : syracuseStep 4368635 = 6552953) B6552953
theorem B2912423 : Blo 1941435 2912423 := bstep (se 1 (by rfl) ⟨2184317, by rfl⟩ : syracuseStep 2912423 = 4368635) B4368635
theorem B1941615 : Blo 1941435 1941615 := bstep (se 1 (by rfl) ⟨1456211, by rfl⟩ : syracuseStep 1941615 = 2912423) B2912423
theorem B2912429 : Blo 1941435 2912429 := bbase (se 3 (by rfl) ⟨546080, by rfl⟩ : syracuseStep 2912429 = 1092161) (by norm_num)
theorem B1941619 : Blo 1941435 1941619 := bstep (se 1 (by rfl) ⟨1456214, by rfl⟩ : syracuseStep 1941619 = 2912429) B2912429
theorem B4368653 : Blo 1941435 4368653 := bbase (se 3 (by rfl) ⟨819122, by rfl⟩ : syracuseStep 4368653 = 1638245) (by norm_num)
theorem B2912435 : Blo 1941435 2912435 := bstep (se 1 (by rfl) ⟨2184326, by rfl⟩ : syracuseStep 2912435 = 4368653) B4368653
theorem B1941623 : Blo 1941435 1941623 := bstep (se 1 (by rfl) ⟨1456217, by rfl⟩ : syracuseStep 1941623 = 2912435) B2912435
theorem B2457373 : Blo 1941435 2457373 := bbase (se 3 (by rfl) ⟨460757, by rfl⟩ : syracuseStep 2457373 = 921515) (by norm_num)
theorem B3276497 : Blo 1941435 3276497 := bstep (se 2 (by rfl) ⟨1228686, by rfl⟩ : syracuseStep 3276497 = 2457373) B2457373
theorem B2184331 : Blo 1941435 2184331 := bstep (se 1 (by rfl) ⟨1638248, by rfl⟩ : syracuseStep 2184331 = 3276497) B3276497
theorem B2912441 : Blo 1941435 2912441 := bstep (se 2 (by rfl) ⟨1092165, by rfl⟩ : syracuseStep 2912441 = 2184331) B2184331
theorem B1941627 : Blo 1941435 1941627 := bstep (se 1 (by rfl) ⟨1456220, by rfl⟩ : syracuseStep 1941627 = 2912441) B2912441
theorem B2022193 : Blo 1941435 2022193 := bbase (se 2 (by rfl) ⟨758322, by rfl⟩ : syracuseStep 2022193 = 1516645) (by norm_num)
theorem B172560469 : Blo 1941435 172560469 := bstep (se 8 (by rfl) ⟨1011096, by rfl⟩ : syracuseStep 172560469 = 2022193) B2022193
theorem B230080625 : Blo 1941435 230080625 := bstep (se 2 (by rfl) ⟨86280234, by rfl⟩ : syracuseStep 230080625 = 172560469) B172560469
theorem B153387083 : Blo 1941435 153387083 := bstep (se 1 (by rfl) ⟨115040312, by rfl⟩ : syracuseStep 153387083 = 230080625) B230080625
theorem B102258055 : Blo 1941435 102258055 := bstep (se 1 (by rfl) ⟨76693541, by rfl⟩ : syracuseStep 102258055 = 153387083) B153387083
theorem B136344073 : Blo 1941435 136344073 := bstep (se 2 (by rfl) ⟨51129027, by rfl⟩ : syracuseStep 136344073 = 102258055) B102258055
theorem B181792097 : Blo 1941435 181792097 := bstep (se 2 (by rfl) ⟨68172036, by rfl⟩ : syracuseStep 181792097 = 136344073) B136344073
theorem B121194731 : Blo 1941435 121194731 := bstep (se 1 (by rfl) ⟨90896048, by rfl⟩ : syracuseStep 121194731 = 181792097) B181792097
theorem B80796487 : Blo 1941435 80796487 := bstep (se 1 (by rfl) ⟨60597365, by rfl⟩ : syracuseStep 80796487 = 121194731) B121194731
theorem B107728649 : Blo 1941435 107728649 := bstep (se 2 (by rfl) ⟨40398243, by rfl⟩ : syracuseStep 107728649 = 80796487) B80796487
theorem B71819099 : Blo 1941435 71819099 := bstep (se 1 (by rfl) ⟨53864324, by rfl⟩ : syracuseStep 71819099 = 107728649) B107728649
theorem B47879399 : Blo 1941435 47879399 := bstep (se 1 (by rfl) ⟨35909549, by rfl⟩ : syracuseStep 47879399 = 71819099) B71819099
theorem B31919599 : Blo 1941435 31919599 := bstep (se 1 (by rfl) ⟨23939699, by rfl⟩ : syracuseStep 31919599 = 47879399) B47879399
theorem B42559465 : Blo 1941435 42559465 := bstep (se 2 (by rfl) ⟨15959799, by rfl⟩ : syracuseStep 42559465 = 31919599) B31919599
theorem B56745953 : Blo 1941435 56745953 := bstep (se 2 (by rfl) ⟨21279732, by rfl⟩ : syracuseStep 56745953 = 42559465) B42559465
theorem B37830635 : Blo 1941435 37830635 := bstep (se 1 (by rfl) ⟨28372976, by rfl⟩ : syracuseStep 37830635 = 56745953) B56745953
theorem B25220423 : Blo 1941435 25220423 := bstep (se 1 (by rfl) ⟨18915317, by rfl⟩ : syracuseStep 25220423 = 37830635) B37830635
theorem B16813615 : Blo 1941435 16813615 := bstep (se 1 (by rfl) ⟨12610211, by rfl⟩ : syracuseStep 16813615 = 25220423) B25220423
theorem B22418153 : Blo 1941435 22418153 := bstep (se 2 (by rfl) ⟨8406807, by rfl⟩ : syracuseStep 22418153 = 16813615) B16813615
theorem B14945435 : Blo 1941435 14945435 := bstep (se 1 (by rfl) ⟨11209076, by rfl⟩ : syracuseStep 14945435 = 22418153) B22418153
theorem B9963623 : Blo 1941435 9963623 := bstep (se 1 (by rfl) ⟨7472717, by rfl⟩ : syracuseStep 9963623 = 14945435) B14945435
theorem B6642415 : Blo 1941435 6642415 := bstep (se 1 (by rfl) ⟨4981811, by rfl⟩ : syracuseStep 6642415 = 9963623) B9963623
theorem B8856553 : Blo 1941435 8856553 := bstep (se 2 (by rfl) ⟨3321207, by rfl⟩ : syracuseStep 8856553 = 6642415) B6642415
theorem B11808737 : Blo 1941435 11808737 := bstep (se 2 (by rfl) ⟨4428276, by rfl⟩ : syracuseStep 11808737 = 8856553) B8856553
theorem B7872491 : Blo 1941435 7872491 := bstep (se 1 (by rfl) ⟨5904368, by rfl⟩ : syracuseStep 7872491 = 11808737) B11808737
theorem B5248327 : Blo 1941435 5248327 := bstep (se 1 (by rfl) ⟨3936245, by rfl⟩ : syracuseStep 5248327 = 7872491) B7872491
theorem B6997769 : Blo 1941435 6997769 := bstep (se 2 (by rfl) ⟨2624163, by rfl⟩ : syracuseStep 6997769 = 5248327) B5248327
theorem B4665179 : Blo 1941435 4665179 := bstep (se 1 (by rfl) ⟨3498884, by rfl⟩ : syracuseStep 4665179 = 6997769) B6997769
theorem B3110119 : Blo 1941435 3110119 := bstep (se 1 (by rfl) ⟨2332589, by rfl⟩ : syracuseStep 3110119 = 4665179) B4665179
theorem B16587301 : Blo 1941435 16587301 := bstep (se 4 (by rfl) ⟨1555059, by rfl⟩ : syracuseStep 16587301 = 3110119) B3110119
theorem B22116401 : Blo 1941435 22116401 := bstep (se 2 (by rfl) ⟨8293650, by rfl⟩ : syracuseStep 22116401 = 16587301) B16587301
theorem B14744267 : Blo 1941435 14744267 := bstep (se 1 (by rfl) ⟨11058200, by rfl⟩ : syracuseStep 14744267 = 22116401) B22116401
theorem B9829511 : Blo 1941435 9829511 := bstep (se 1 (by rfl) ⟨7372133, by rfl⟩ : syracuseStep 9829511 = 14744267) B14744267
theorem B6553007 : Blo 1941435 6553007 := bstep (se 1 (by rfl) ⟨4914755, by rfl⟩ : syracuseStep 6553007 = 9829511) B9829511
theorem B4368671 : Blo 1941435 4368671 := bstep (se 1 (by rfl) ⟨3276503, by rfl⟩ : syracuseStep 4368671 = 6553007) B6553007
theorem B2912447 : Blo 1941435 2912447 := bstep (se 1 (by rfl) ⟨2184335, by rfl⟩ : syracuseStep 2912447 = 4368671) B4368671
theorem B1941631 : Blo 1941435 1941631 := bstep (se 1 (by rfl) ⟨1456223, by rfl⟩ : syracuseStep 1941631 = 2912447) B2912447
theorem B2912453 : Blo 1941435 2912453 := bbase (se 4 (by rfl) ⟨273042, by rfl⟩ : syracuseStep 2912453 = 546085) (by norm_num)
theorem B1941635 : Blo 1941435 1941635 := bstep (se 1 (by rfl) ⟨1456226, by rfl⟩ : syracuseStep 1941635 = 2912453) B2912453
theorem B3276517 : Blo 1941435 3276517 := bbase (se 4 (by rfl) ⟨307173, by rfl⟩ : syracuseStep 3276517 = 614347) (by norm_num)
theorem B4368689 : Blo 1941435 4368689 := bstep (se 2 (by rfl) ⟨1638258, by rfl⟩ : syracuseStep 4368689 = 3276517) B3276517
theorem B2912459 : Blo 1941435 2912459 := bstep (se 1 (by rfl) ⟨2184344, by rfl⟩ : syracuseStep 2912459 = 4368689) B4368689
theorem B1941639 : Blo 1941435 1941639 := bstep (se 1 (by rfl) ⟨1456229, by rfl⟩ : syracuseStep 1941639 = 2912459) B2912459
theorem B2184349 : Blo 1941435 2184349 := bbase (se 3 (by rfl) ⟨409565, by rfl⟩ : syracuseStep 2184349 = 819131) (by norm_num)
theorem B2912465 : Blo 1941435 2912465 := bstep (se 2 (by rfl) ⟨1092174, by rfl⟩ : syracuseStep 2912465 = 2184349) B2184349
theorem B1941643 : Blo 1941435 1941643 := bstep (se 1 (by rfl) ⟨1456232, by rfl⟩ : syracuseStep 1941643 = 2912465) B2912465
theorem B6553061 : Blo 1941435 6553061 := bbase (se 4 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 6553061 = 1228699) (by norm_num)
theorem B4368707 : Blo 1941435 4368707 := bstep (se 1 (by rfl) ⟨3276530, by rfl⟩ : syracuseStep 4368707 = 6553061) B6553061
theorem B2912471 : Blo 1941435 2912471 := bstep (se 1 (by rfl) ⟨2184353, by rfl⟩ : syracuseStep 2912471 = 4368707) B4368707
theorem B1941647 : Blo 1941435 1941647 := bstep (se 1 (by rfl) ⟨1456235, by rfl⟩ : syracuseStep 1941647 = 2912471) B2912471
theorem B2912477 : Blo 1941435 2912477 := bbase (se 3 (by rfl) ⟨546089, by rfl⟩ : syracuseStep 2912477 = 1092179) (by norm_num)
theorem B1941651 : Blo 1941435 1941651 := bstep (se 1 (by rfl) ⟨1456238, by rfl⟩ : syracuseStep 1941651 = 2912477) B2912477
theorem B4368725 : Blo 1941435 4368725 := bbase (se 10 (by rfl) ⟨6399, by rfl⟩ : syracuseStep 4368725 = 12799) (by norm_num)
theorem B2912483 : Blo 1941435 2912483 := bstep (se 1 (by rfl) ⟨2184362, by rfl⟩ : syracuseStep 2912483 = 4368725) B4368725
theorem B1941655 : Blo 1941435 1941655 := bstep (se 1 (by rfl) ⟨1456241, by rfl⟩ : syracuseStep 1941655 = 2912483) B2912483
theorem B3110165 : Blo 1941435 3110165 := bbase (se 6 (by rfl) ⟨72894, by rfl⟩ : syracuseStep 3110165 = 145789) (by norm_num)
theorem B2073443 : Blo 1941435 2073443 := bstep (se 1 (by rfl) ⟨1555082, by rfl⟩ : syracuseStep 2073443 = 3110165) B3110165
theorem B5529181 : Blo 1941435 5529181 := bstep (se 3 (by rfl) ⟨1036721, by rfl⟩ : syracuseStep 5529181 = 2073443) B2073443
theorem B7372241 : Blo 1941435 7372241 := bstep (se 2 (by rfl) ⟨2764590, by rfl⟩ : syracuseStep 7372241 = 5529181) B5529181
theorem B4914827 : Blo 1941435 4914827 := bstep (se 1 (by rfl) ⟨3686120, by rfl⟩ : syracuseStep 4914827 = 7372241) B7372241
theorem B3276551 : Blo 1941435 3276551 := bstep (se 1 (by rfl) ⟨2457413, by rfl⟩ : syracuseStep 3276551 = 4914827) B4914827
theorem B2184367 : Blo 1941435 2184367 := bstep (se 1 (by rfl) ⟨1638275, by rfl⟩ : syracuseStep 2184367 = 3276551) B3276551
theorem B2912489 : Blo 1941435 2912489 := bstep (se 2 (by rfl) ⟨1092183, by rfl⟩ : syracuseStep 2912489 = 2184367) B2184367
theorem B1941659 : Blo 1941435 1941659 := bstep (se 1 (by rfl) ⟨1456244, by rfl⟩ : syracuseStep 1941659 = 2912489) B2912489
theorem B9457813 : Blo 1941435 9457813 := bbase (se 6 (by rfl) ⟨221667, by rfl⟩ : syracuseStep 9457813 = 443335) (by norm_num)
theorem B12610417 : Blo 1941435 12610417 := bstep (se 2 (by rfl) ⟨4728906, by rfl⟩ : syracuseStep 12610417 = 9457813) B9457813
theorem B16813889 : Blo 1941435 16813889 := bstep (se 2 (by rfl) ⟨6305208, by rfl⟩ : syracuseStep 16813889 = 12610417) B12610417
theorem B11209259 : Blo 1941435 11209259 := bstep (se 1 (by rfl) ⟨8406944, by rfl⟩ : syracuseStep 11209259 = 16813889) B16813889
theorem B7472839 : Blo 1941435 7472839 := bstep (se 1 (by rfl) ⟨5604629, by rfl⟩ : syracuseStep 7472839 = 11209259) B11209259
theorem B9963785 : Blo 1941435 9963785 := bstep (se 2 (by rfl) ⟨3736419, by rfl⟩ : syracuseStep 9963785 = 7472839) B7472839
theorem B6642523 : Blo 1941435 6642523 := bstep (se 1 (by rfl) ⟨4981892, by rfl⟩ : syracuseStep 6642523 = 9963785) B9963785
theorem B8856697 : Blo 1941435 8856697 := bstep (se 2 (by rfl) ⟨3321261, by rfl⟩ : syracuseStep 8856697 = 6642523) B6642523
theorem B11808929 : Blo 1941435 11808929 := bstep (se 2 (by rfl) ⟨4428348, by rfl⟩ : syracuseStep 11808929 = 8856697) B8856697
theorem B31490477 : Blo 1941435 31490477 := bstep (se 3 (by rfl) ⟨5904464, by rfl⟩ : syracuseStep 31490477 = 11808929) B11808929
theorem B20993651 : Blo 1941435 20993651 := bstep (se 1 (by rfl) ⟨15745238, by rfl⟩ : syracuseStep 20993651 = 31490477) B31490477
theorem B13995767 : Blo 1941435 13995767 := bstep (se 1 (by rfl) ⟨10496825, by rfl⟩ : syracuseStep 13995767 = 20993651) B20993651
theorem B37322045 : Blo 1941435 37322045 := bstep (se 3 (by rfl) ⟨6997883, by rfl⟩ : syracuseStep 37322045 = 13995767) B13995767
theorem B24881363 : Blo 1941435 24881363 := bstep (se 1 (by rfl) ⟨18661022, by rfl⟩ : syracuseStep 24881363 = 37322045) B37322045
theorem B16587575 : Blo 1941435 16587575 := bstep (se 1 (by rfl) ⟨12440681, by rfl⟩ : syracuseStep 16587575 = 24881363) B24881363
theorem B11058383 : Blo 1941435 11058383 := bstep (se 1 (by rfl) ⟨8293787, by rfl⟩ : syracuseStep 11058383 = 16587575) B16587575
theorem B7372255 : Blo 1941435 7372255 := bstep (se 1 (by rfl) ⟨5529191, by rfl⟩ : syracuseStep 7372255 = 11058383) B11058383
theorem B9829673 : Blo 1941435 9829673 := bstep (se 2 (by rfl) ⟨3686127, by rfl⟩ : syracuseStep 9829673 = 7372255) B7372255
theorem B6553115 : Blo 1941435 6553115 := bstep (se 1 (by rfl) ⟨4914836, by rfl⟩ : syracuseStep 6553115 = 9829673) B9829673
theorem B4368743 : Blo 1941435 4368743 := bstep (se 1 (by rfl) ⟨3276557, by rfl⟩ : syracuseStep 4368743 = 6553115) B6553115
theorem B2912495 : Blo 1941435 2912495 := bstep (se 1 (by rfl) ⟨2184371, by rfl⟩ : syracuseStep 2912495 = 4368743) B4368743
theorem B1941663 : Blo 1941435 1941663 := bstep (se 1 (by rfl) ⟨1456247, by rfl⟩ : syracuseStep 1941663 = 2912495) B2912495
theorem B2912501 : Blo 1941435 2912501 := bbase (se 5 (by rfl) ⟨136523, by rfl⟩ : syracuseStep 2912501 = 273047) (by norm_num)
theorem B1941667 : Blo 1941435 1941667 := bstep (se 1 (by rfl) ⟨1456250, by rfl⟩ : syracuseStep 1941667 = 2912501) B2912501
theorem B8521685 : Blo 1941435 8521685 := bbase (se 7 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 8521685 = 199727) (by norm_num)
theorem B5681123 : Blo 1941435 5681123 := bstep (se 1 (by rfl) ⟨4260842, by rfl⟩ : syracuseStep 5681123 = 8521685) B8521685
theorem B3787415 : Blo 1941435 3787415 := bstep (se 1 (by rfl) ⟨2840561, by rfl⟩ : syracuseStep 3787415 = 5681123) B5681123
theorem B2524943 : Blo 1941435 2524943 := bstep (se 1 (by rfl) ⟨1893707, by rfl⟩ : syracuseStep 2524943 = 3787415) B3787415
theorem B6733181 : Blo 1941435 6733181 := bstep (se 3 (by rfl) ⟨1262471, by rfl⟩ : syracuseStep 6733181 = 2524943) B2524943
theorem B4488787 : Blo 1941435 4488787 := bstep (se 1 (by rfl) ⟨3366590, by rfl⟩ : syracuseStep 4488787 = 6733181) B6733181
theorem B5985049 : Blo 1941435 5985049 := bstep (se 2 (by rfl) ⟨2244393, by rfl⟩ : syracuseStep 5985049 = 4488787) B4488787
theorem B7980065 : Blo 1941435 7980065 := bstep (se 2 (by rfl) ⟨2992524, by rfl⟩ : syracuseStep 7980065 = 5985049) B5985049
theorem B5320043 : Blo 1941435 5320043 := bstep (se 1 (by rfl) ⟨3990032, by rfl⟩ : syracuseStep 5320043 = 7980065) B7980065
theorem B3546695 : Blo 1941435 3546695 := bstep (se 1 (by rfl) ⟨2660021, by rfl⟩ : syracuseStep 3546695 = 5320043) B5320043
theorem B2364463 : Blo 1941435 2364463 := bstep (se 1 (by rfl) ⟨1773347, by rfl⟩ : syracuseStep 2364463 = 3546695) B3546695
theorem B12610469 : Blo 1941435 12610469 := bstep (se 4 (by rfl) ⟨1182231, by rfl⟩ : syracuseStep 12610469 = 2364463) B2364463
theorem B8406979 : Blo 1941435 8406979 := bstep (se 1 (by rfl) ⟨6305234, by rfl⟩ : syracuseStep 8406979 = 12610469) B12610469
theorem B44837221 : Blo 1941435 44837221 := bstep (se 4 (by rfl) ⟨4203489, by rfl⟩ : syracuseStep 44837221 = 8406979) B8406979
theorem B59782961 : Blo 1941435 59782961 := bstep (se 2 (by rfl) ⟨22418610, by rfl⟩ : syracuseStep 59782961 = 44837221) B44837221
theorem B159421229 : Blo 1941435 159421229 := bstep (se 3 (by rfl) ⟨29891480, by rfl⟩ : syracuseStep 159421229 = 59782961) B59782961
theorem B106280819 : Blo 1941435 106280819 := bstep (se 1 (by rfl) ⟨79710614, by rfl⟩ : syracuseStep 106280819 = 159421229) B159421229
theorem B70853879 : Blo 1941435 70853879 := bstep (se 1 (by rfl) ⟨53140409, by rfl⟩ : syracuseStep 70853879 = 106280819) B106280819
theorem B47235919 : Blo 1941435 47235919 := bstep (se 1 (by rfl) ⟨35426939, by rfl⟩ : syracuseStep 47235919 = 70853879) B70853879
theorem B62981225 : Blo 1941435 62981225 := bstep (se 2 (by rfl) ⟨23617959, by rfl⟩ : syracuseStep 62981225 = 47235919) B47235919
theorem B41987483 : Blo 1941435 41987483 := bstep (se 1 (by rfl) ⟨31490612, by rfl⟩ : syracuseStep 41987483 = 62981225) B62981225
theorem B27991655 : Blo 1941435 27991655 := bstep (se 1 (by rfl) ⟨20993741, by rfl⟩ : syracuseStep 27991655 = 41987483) B41987483
theorem B18661103 : Blo 1941435 18661103 := bstep (se 1 (by rfl) ⟨13995827, by rfl⟩ : syracuseStep 18661103 = 27991655) B27991655
theorem B12440735 : Blo 1941435 12440735 := bstep (se 1 (by rfl) ⟨9330551, by rfl⟩ : syracuseStep 12440735 = 18661103) B18661103
theorem B8293823 : Blo 1941435 8293823 := bstep (se 1 (by rfl) ⟨6220367, by rfl⟩ : syracuseStep 8293823 = 12440735) B12440735
theorem B5529215 : Blo 1941435 5529215 := bstep (se 1 (by rfl) ⟨4146911, by rfl⟩ : syracuseStep 5529215 = 8293823) B8293823
theorem B3686143 : Blo 1941435 3686143 := bstep (se 1 (by rfl) ⟨2764607, by rfl⟩ : syracuseStep 3686143 = 5529215) B5529215
theorem B4914857 : Blo 1941435 4914857 := bstep (se 2 (by rfl) ⟨1843071, by rfl⟩ : syracuseStep 4914857 = 3686143) B3686143
theorem B3276571 : Blo 1941435 3276571 := bstep (se 1 (by rfl) ⟨2457428, by rfl⟩ : syracuseStep 3276571 = 4914857) B4914857
theorem B4368761 : Blo 1941435 4368761 := bstep (se 2 (by rfl) ⟨1638285, by rfl⟩ : syracuseStep 4368761 = 3276571) B3276571
theorem B2912507 : Blo 1941435 2912507 := bstep (se 1 (by rfl) ⟨2184380, by rfl⟩ : syracuseStep 2912507 = 4368761) B4368761
theorem B1941671 : Blo 1941435 1941671 := bstep (se 1 (by rfl) ⟨1456253, by rfl⟩ : syracuseStep 1941671 = 2912507) B2912507
theorem B2184385 : Blo 1941435 2184385 := bbase (se 2 (by rfl) ⟨819144, by rfl⟩ : syracuseStep 2184385 = 1638289) (by norm_num)
theorem B2912513 : Blo 1941435 2912513 := bstep (se 2 (by rfl) ⟨1092192, by rfl⟩ : syracuseStep 2912513 = 2184385) B2184385
theorem B1941675 : Blo 1941435 1941675 := bstep (se 1 (by rfl) ⟨1456256, by rfl⟩ : syracuseStep 1941675 = 2912513) B2912513
theorem B4914877 : Blo 1941435 4914877 := bbase (se 3 (by rfl) ⟨921539, by rfl⟩ : syracuseStep 4914877 = 1843079) (by norm_num)
theorem B6553169 : Blo 1941435 6553169 := bstep (se 2 (by rfl) ⟨2457438, by rfl⟩ : syracuseStep 6553169 = 4914877) B4914877
theorem B4368779 : Blo 1941435 4368779 := bstep (se 1 (by rfl) ⟨3276584, by rfl⟩ : syracuseStep 4368779 = 6553169) B6553169
theorem B2912519 : Blo 1941435 2912519 := bstep (se 1 (by rfl) ⟨2184389, by rfl⟩ : syracuseStep 2912519 = 4368779) B4368779
theorem B1941679 : Blo 1941435 1941679 := bstep (se 1 (by rfl) ⟨1456259, by rfl⟩ : syracuseStep 1941679 = 2912519) B2912519
theorem B2912525 : Blo 1941435 2912525 := bbase (se 3 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 2912525 = 1092197) (by norm_num)
theorem B1941683 : Blo 1941435 1941683 := bstep (se 1 (by rfl) ⟨1456262, by rfl⟩ : syracuseStep 1941683 = 2912525) B2912525
theorem B4368797 : Blo 1941435 4368797 := bbase (se 3 (by rfl) ⟨819149, by rfl⟩ : syracuseStep 4368797 = 1638299) (by norm_num)
theorem B2912531 : Blo 1941435 2912531 := bstep (se 1 (by rfl) ⟨2184398, by rfl⟩ : syracuseStep 2912531 = 4368797) B4368797
theorem B1941687 : Blo 1941435 1941687 := bstep (se 1 (by rfl) ⟨1456265, by rfl⟩ : syracuseStep 1941687 = 2912531) B2912531
theorem B3276605 : Blo 1941435 3276605 := bbase (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) (by norm_num)
theorem B2184403 : Blo 1941435 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B2912537 : Blo 1941435 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B1941691 : Blo 1941435 1941691 := bstep (se 1 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 1941691 = 2912537) B2912537
theorem B2073481 : Blo 1941435 2073481 := bbase (se 2 (by rfl) ⟨777555, by rfl⟩ : syracuseStep 2073481 = 1555111) (by norm_num)
theorem B11058565 : Blo 1941435 11058565 := bstep (se 4 (by rfl) ⟨1036740, by rfl⟩ : syracuseStep 11058565 = 2073481) B2073481
theorem B14744753 : Blo 1941435 14744753 := bstep (se 2 (by rfl) ⟨5529282, by rfl⟩ : syracuseStep 14744753 = 11058565) B11058565
theorem B9829835 : Blo 1941435 9829835 := bstep (se 1 (by rfl) ⟨7372376, by rfl⟩ : syracuseStep 9829835 = 14744753) B14744753
theorem B6553223 : Blo 1941435 6553223 := bstep (se 1 (by rfl) ⟨4914917, by rfl⟩ : syracuseStep 6553223 = 9829835) B9829835
theorem B4368815 : Blo 1941435 4368815 := bstep (se 1 (by rfl) ⟨3276611, by rfl⟩ : syracuseStep 4368815 = 6553223) B6553223
theorem B2912543 : Blo 1941435 2912543 := bstep (se 1 (by rfl) ⟨2184407, by rfl⟩ : syracuseStep 2912543 = 4368815) B4368815
theorem B1941695 : Blo 1941435 1941695 := bstep (se 1 (by rfl) ⟨1456271, by rfl⟩ : syracuseStep 1941695 = 2912543) B2912543
theorem B2912549 : Blo 1941435 2912549 := bbase (se 4 (by rfl) ⟨273051, by rfl⟩ : syracuseStep 2912549 = 546103) (by norm_num)
theorem B1941699 : Blo 1941435 1941699 := bstep (se 1 (by rfl) ⟨1456274, by rfl⟩ : syracuseStep 1941699 = 2912549) B2912549
theorem B2457469 : Blo 1941435 2457469 := bbase (se 3 (by rfl) ⟨460775, by rfl⟩ : syracuseStep 2457469 = 921551) (by norm_num)
theorem B3276625 : Blo 1941435 3276625 := bstep (se 2 (by rfl) ⟨1228734, by rfl⟩ : syracuseStep 3276625 = 2457469) B2457469
theorem B4368833 : Blo 1941435 4368833 := bstep (se 2 (by rfl) ⟨1638312, by rfl⟩ : syracuseStep 4368833 = 3276625) B3276625
theorem B2912555 : Blo 1941435 2912555 := bstep (se 1 (by rfl) ⟨2184416, by rfl⟩ : syracuseStep 2912555 = 4368833) B4368833
theorem B1941703 : Blo 1941435 1941703 := bstep (se 1 (by rfl) ⟨1456277, by rfl⟩ : syracuseStep 1941703 = 2912555) B2912555
theorem B2184421 : Blo 1941435 2184421 := bbase (se 4 (by rfl) ⟨204789, by rfl⟩ : syracuseStep 2184421 = 409579) (by norm_num)
theorem B2912561 : Blo 1941435 2912561 := bstep (se 2 (by rfl) ⟨1092210, by rfl⟩ : syracuseStep 2912561 = 2184421) B2184421
theorem B1941707 : Blo 1941435 1941707 := bstep (se 1 (by rfl) ⟨1456280, by rfl⟩ : syracuseStep 1941707 = 2912561) B2912561
theorem B4146997 : Blo 1941435 4146997 := bbase (se 5 (by rfl) ⟨194390, by rfl⟩ : syracuseStep 4146997 = 388781) (by norm_num)
theorem B5529329 : Blo 1941435 5529329 := bstep (se 2 (by rfl) ⟨2073498, by rfl⟩ : syracuseStep 5529329 = 4146997) B4146997
theorem B3686219 : Blo 1941435 3686219 := bstep (se 1 (by rfl) ⟨2764664, by rfl⟩ : syracuseStep 3686219 = 5529329) B5529329
theorem B2457479 : Blo 1941435 2457479 := bstep (se 1 (by rfl) ⟨1843109, by rfl⟩ : syracuseStep 2457479 = 3686219) B3686219
theorem B6553277 : Blo 1941435 6553277 := bstep (se 3 (by rfl) ⟨1228739, by rfl⟩ : syracuseStep 6553277 = 2457479) B2457479
theorem B4368851 : Blo 1941435 4368851 := bstep (se 1 (by rfl) ⟨3276638, by rfl⟩ : syracuseStep 4368851 = 6553277) B6553277
theorem B2912567 : Blo 1941435 2912567 := bstep (se 1 (by rfl) ⟨2184425, by rfl⟩ : syracuseStep 2912567 = 4368851) B4368851
theorem B1941711 : Blo 1941435 1941711 := bstep (se 1 (by rfl) ⟨1456283, by rfl⟩ : syracuseStep 1941711 = 2912567) B2912567
theorem B2912573 : Blo 1941435 2912573 := bbase (se 3 (by rfl) ⟨546107, by rfl⟩ : syracuseStep 2912573 = 1092215) (by norm_num)
theorem B1941715 : Blo 1941435 1941715 := bstep (se 1 (by rfl) ⟨1456286, by rfl⟩ : syracuseStep 1941715 = 2912573) B2912573
theorem B4368869 : Blo 1941435 4368869 := bbase (se 4 (by rfl) ⟨409581, by rfl⟩ : syracuseStep 4368869 = 819163) (by norm_num)
theorem B2912579 : Blo 1941435 2912579 := bstep (se 1 (by rfl) ⟨2184434, by rfl⟩ : syracuseStep 2912579 = 4368869) B4368869
theorem B1941719 : Blo 1941435 1941719 := bstep (se 1 (by rfl) ⟨1456289, by rfl⟩ : syracuseStep 1941719 = 2912579) B2912579
theorem B4914989 : Blo 1941435 4914989 := bbase (se 3 (by rfl) ⟨921560, by rfl⟩ : syracuseStep 4914989 = 1843121) (by norm_num)
theorem B3276659 : Blo 1941435 3276659 := bstep (se 1 (by rfl) ⟨2457494, by rfl⟩ : syracuseStep 3276659 = 4914989) B4914989
theorem B2184439 : Blo 1941435 2184439 := bstep (se 1 (by rfl) ⟨1638329, by rfl⟩ : syracuseStep 2184439 = 3276659) B3276659
theorem B2912585 : Blo 1941435 2912585 := bstep (se 2 (by rfl) ⟨1092219, by rfl⟩ : syracuseStep 2912585 = 2184439) B2184439
theorem B1941723 : Blo 1941435 1941723 := bstep (se 1 (by rfl) ⟨1456292, by rfl⟩ : syracuseStep 1941723 = 2912585) B2912585
theorem B9330821 : Blo 1941435 9330821 := bbase (se 4 (by rfl) ⟨874764, by rfl⟩ : syracuseStep 9330821 = 1749529) (by norm_num)
theorem B6220547 : Blo 1941435 6220547 := bstep (se 1 (by rfl) ⟨4665410, by rfl⟩ : syracuseStep 6220547 = 9330821) B9330821
theorem B4147031 : Blo 1941435 4147031 := bstep (se 1 (by rfl) ⟨3110273, by rfl⟩ : syracuseStep 4147031 = 6220547) B6220547
theorem B2764687 : Blo 1941435 2764687 := bstep (se 1 (by rfl) ⟨2073515, by rfl⟩ : syracuseStep 2764687 = 4147031) B4147031
theorem B3686249 : Blo 1941435 3686249 := bstep (se 2 (by rfl) ⟨1382343, by rfl⟩ : syracuseStep 3686249 = 2764687) B2764687
theorem B9829997 : Blo 1941435 9829997 := bstep (se 3 (by rfl) ⟨1843124, by rfl⟩ : syracuseStep 9829997 = 3686249) B3686249
theorem B6553331 : Blo 1941435 6553331 := bstep (se 1 (by rfl) ⟨4914998, by rfl⟩ : syracuseStep 6553331 = 9829997) B9829997
theorem B4368887 : Blo 1941435 4368887 := bstep (se 1 (by rfl) ⟨3276665, by rfl⟩ : syracuseStep 4368887 = 6553331) B6553331
theorem B2912591 : Blo 1941435 2912591 := bstep (se 1 (by rfl) ⟨2184443, by rfl⟩ : syracuseStep 2912591 = 4368887) B4368887
theorem B1941727 : Blo 1941435 1941727 := bstep (se 1 (by rfl) ⟨1456295, by rfl⟩ : syracuseStep 1941727 = 2912591) B2912591
theorem B2912597 : Blo 1941435 2912597 := bbase (se 10 (by rfl) ⟨4266, by rfl⟩ : syracuseStep 2912597 = 8533) (by norm_num)
theorem B1941731 : Blo 1941435 1941731 := bstep (se 1 (by rfl) ⟨1456298, by rfl⟩ : syracuseStep 1941731 = 2912597) B2912597
theorem B5529397 : Blo 1941435 5529397 := bbase (se 5 (by rfl) ⟨259190, by rfl⟩ : syracuseStep 5529397 = 518381) (by norm_num)
theorem B7372529 : Blo 1941435 7372529 := bstep (se 2 (by rfl) ⟨2764698, by rfl⟩ : syracuseStep 7372529 = 5529397) B5529397
theorem B4915019 : Blo 1941435 4915019 := bstep (se 1 (by rfl) ⟨3686264, by rfl⟩ : syracuseStep 4915019 = 7372529) B7372529
theorem B3276679 : Blo 1941435 3276679 := bstep (se 1 (by rfl) ⟨2457509, by rfl⟩ : syracuseStep 3276679 = 4915019) B4915019
theorem B4368905 : Blo 1941435 4368905 := bstep (se 2 (by rfl) ⟨1638339, by rfl⟩ : syracuseStep 4368905 = 3276679) B3276679
theorem B2912603 : Blo 1941435 2912603 := bstep (se 1 (by rfl) ⟨2184452, by rfl⟩ : syracuseStep 2912603 = 4368905) B4368905
theorem B1941735 : Blo 1941435 1941735 := bstep (se 1 (by rfl) ⟨1456301, by rfl⟩ : syracuseStep 1941735 = 2912603) B2912603
theorem B2184457 : Blo 1941435 2184457 := bbase (se 2 (by rfl) ⟨819171, by rfl⟩ : syracuseStep 2184457 = 1638343) (by norm_num)
theorem B2912609 : Blo 1941435 2912609 := bstep (se 2 (by rfl) ⟨1092228, by rfl⟩ : syracuseStep 2912609 = 2184457) B2184457
theorem B1941739 : Blo 1941435 1941739 := bstep (se 1 (by rfl) ⟨1456304, by rfl⟩ : syracuseStep 1941739 = 2912609) B2912609
theorem B24882389 : Blo 1941435 24882389 := bbase (se 7 (by rfl) ⟨291590, by rfl⟩ : syracuseStep 24882389 = 583181) (by norm_num)
theorem B16588259 : Blo 1941435 16588259 := bstep (se 1 (by rfl) ⟨12441194, by rfl⟩ : syracuseStep 16588259 = 24882389) B24882389
theorem B11058839 : Blo 1941435 11058839 := bstep (se 1 (by rfl) ⟨8294129, by rfl⟩ : syracuseStep 11058839 = 16588259) B16588259
theorem B7372559 : Blo 1941435 7372559 := bstep (se 1 (by rfl) ⟨5529419, by rfl⟩ : syracuseStep 7372559 = 11058839) B11058839
theorem B4915039 : Blo 1941435 4915039 := bstep (se 1 (by rfl) ⟨3686279, by rfl⟩ : syracuseStep 4915039 = 7372559) B7372559
theorem B6553385 : Blo 1941435 6553385 := bstep (se 2 (by rfl) ⟨2457519, by rfl⟩ : syracuseStep 6553385 = 4915039) B4915039
theorem B4368923 : Blo 1941435 4368923 := bstep (se 1 (by rfl) ⟨3276692, by rfl⟩ : syracuseStep 4368923 = 6553385) B6553385
theorem B2912615 : Blo 1941435 2912615 := bstep (se 1 (by rfl) ⟨2184461, by rfl⟩ : syracuseStep 2912615 = 4368923) B4368923
theorem B1941743 : Blo 1941435 1941743 := bstep (se 1 (by rfl) ⟨1456307, by rfl⟩ : syracuseStep 1941743 = 2912615) B2912615
theorem B2912621 : Blo 1941435 2912621 := bbase (se 3 (by rfl) ⟨546116, by rfl⟩ : syracuseStep 2912621 = 1092233) (by norm_num)
theorem B1941747 : Blo 1941435 1941747 := bstep (se 1 (by rfl) ⟨1456310, by rfl⟩ : syracuseStep 1941747 = 2912621) B2912621
theorem B4368941 : Blo 1941435 4368941 := bbase (se 3 (by rfl) ⟨819176, by rfl⟩ : syracuseStep 4368941 = 1638353) (by norm_num)
theorem B2912627 : Blo 1941435 2912627 := bstep (se 1 (by rfl) ⟨2184470, by rfl⟩ : syracuseStep 2912627 = 4368941) B4368941
theorem B1941751 : Blo 1941435 1941751 := bstep (se 1 (by rfl) ⟨1456313, by rfl⟩ : syracuseStep 1941751 = 2912627) B2912627
theorem B11809493 : Blo 1941435 11809493 := bbase (se 7 (by rfl) ⟨138392, by rfl⟩ : syracuseStep 11809493 = 276785) (by norm_num)
theorem B7872995 : Blo 1941435 7872995 := bstep (se 1 (by rfl) ⟨5904746, by rfl⟩ : syracuseStep 7872995 = 11809493) B11809493
theorem B20994653 : Blo 1941435 20994653 := bstep (se 3 (by rfl) ⟨3936497, by rfl⟩ : syracuseStep 20994653 = 7872995) B7872995
theorem B13996435 : Blo 1941435 13996435 := bstep (se 1 (by rfl) ⟨10497326, by rfl⟩ : syracuseStep 13996435 = 20994653) B20994653
theorem B18661913 : Blo 1941435 18661913 := bstep (se 2 (by rfl) ⟨6998217, by rfl⟩ : syracuseStep 18661913 = 13996435) B13996435
theorem B12441275 : Blo 1941435 12441275 := bstep (se 1 (by rfl) ⟨9330956, by rfl⟩ : syracuseStep 12441275 = 18661913) B18661913
theorem B8294183 : Blo 1941435 8294183 := bstep (se 1 (by rfl) ⟨6220637, by rfl⟩ : syracuseStep 8294183 = 12441275) B12441275
theorem B5529455 : Blo 1941435 5529455 := bstep (se 1 (by rfl) ⟨4147091, by rfl⟩ : syracuseStep 5529455 = 8294183) B8294183
theorem B3686303 : Blo 1941435 3686303 := bstep (se 1 (by rfl) ⟨2764727, by rfl⟩ : syracuseStep 3686303 = 5529455) B5529455
theorem B2457535 : Blo 1941435 2457535 := bstep (se 1 (by rfl) ⟨1843151, by rfl⟩ : syracuseStep 2457535 = 3686303) B3686303
theorem B3276713 : Blo 1941435 3276713 := bstep (se 2 (by rfl) ⟨1228767, by rfl⟩ : syracuseStep 3276713 = 2457535) B2457535
theorem B2184475 : Blo 1941435 2184475 := bstep (se 1 (by rfl) ⟨1638356, by rfl⟩ : syracuseStep 2184475 = 3276713) B3276713
theorem B2912633 : Blo 1941435 2912633 := bstep (se 2 (by rfl) ⟨1092237, by rfl⟩ : syracuseStep 2912633 = 2184475) B2184475
theorem B1941755 : Blo 1941435 1941755 := bstep (se 1 (by rfl) ⟨1456316, by rfl⟩ : syracuseStep 1941755 = 2912633) B2912633
theorem B33176789 : Blo 1941435 33176789 := bbase (se 7 (by rfl) ⟨388790, by rfl⟩ : syracuseStep 33176789 = 777581) (by norm_num)
theorem B22117859 : Blo 1941435 22117859 := bstep (se 1 (by rfl) ⟨16588394, by rfl⟩ : syracuseStep 22117859 = 33176789) B33176789
theorem B14745239 : Blo 1941435 14745239 := bstep (se 1 (by rfl) ⟨11058929, by rfl⟩ : syracuseStep 14745239 = 22117859) B22117859
theorem B9830159 : Blo 1941435 9830159 := bstep (se 1 (by rfl) ⟨7372619, by rfl⟩ : syracuseStep 9830159 = 14745239) B14745239
theorem B6553439 : Blo 1941435 6553439 := bstep (se 1 (by rfl) ⟨4915079, by rfl⟩ : syracuseStep 6553439 = 9830159) B9830159
theorem B4368959 : Blo 1941435 4368959 := bstep (se 1 (by rfl) ⟨3276719, by rfl⟩ : syracuseStep 4368959 = 6553439) B6553439
theorem B2912639 : Blo 1941435 2912639 := bstep (se 1 (by rfl) ⟨2184479, by rfl⟩ : syracuseStep 2912639 = 4368959) B4368959
theorem B1941759 : Blo 1941435 1941759 := bstep (se 1 (by rfl) ⟨1456319, by rfl⟩ : syracuseStep 1941759 = 2912639) B2912639
theorem B2912645 : Blo 1941435 2912645 := bbase (se 4 (by rfl) ⟨273060, by rfl⟩ : syracuseStep 2912645 = 546121) (by norm_num)
theorem B1941763 : Blo 1941435 1941763 := bstep (se 1 (by rfl) ⟨1456322, by rfl⟩ : syracuseStep 1941763 = 2912645) B2912645
theorem B3276733 : Blo 1941435 3276733 := bbase (se 3 (by rfl) ⟨614387, by rfl⟩ : syracuseStep 3276733 = 1228775) (by norm_num)
theorem B4368977 : Blo 1941435 4368977 := bstep (se 2 (by rfl) ⟨1638366, by rfl⟩ : syracuseStep 4368977 = 3276733) B3276733
theorem B2912651 : Blo 1941435 2912651 := bstep (se 1 (by rfl) ⟨2184488, by rfl⟩ : syracuseStep 2912651 = 4368977) B4368977
theorem B1941767 : Blo 1941435 1941767 := bstep (se 1 (by rfl) ⟨1456325, by rfl⟩ : syracuseStep 1941767 = 2912651) B2912651
theorem B2184493 : Blo 1941435 2184493 := bbase (se 3 (by rfl) ⟨409592, by rfl⟩ : syracuseStep 2184493 = 819185) (by norm_num)
theorem B2912657 : Blo 1941435 2912657 := bstep (se 2 (by rfl) ⟨1092246, by rfl⟩ : syracuseStep 2912657 = 2184493) B2184493
theorem B1941771 : Blo 1941435 1941771 := bstep (se 1 (by rfl) ⟨1456328, by rfl⟩ : syracuseStep 1941771 = 2912657) B2912657
theorem B6553493 : Blo 1941435 6553493 := bbase (se 6 (by rfl) ⟨153597, by rfl⟩ : syracuseStep 6553493 = 307195) (by norm_num)
theorem B4368995 : Blo 1941435 4368995 := bstep (se 1 (by rfl) ⟨3276746, by rfl⟩ : syracuseStep 4368995 = 6553493) B6553493
theorem B2912663 : Blo 1941435 2912663 := bstep (se 1 (by rfl) ⟨2184497, by rfl⟩ : syracuseStep 2912663 = 4368995) B4368995
theorem B1941775 : Blo 1941435 1941775 := bstep (se 1 (by rfl) ⟨1456331, by rfl⟩ : syracuseStep 1941775 = 2912663) B2912663
theorem B2912669 : Blo 1941435 2912669 := bbase (se 3 (by rfl) ⟨546125, by rfl⟩ : syracuseStep 2912669 = 1092251) (by norm_num)
theorem B1941779 : Blo 1941435 1941779 := bstep (se 1 (by rfl) ⟨1456334, by rfl⟩ : syracuseStep 1941779 = 2912669) B2912669
theorem B4369013 : Blo 1941435 4369013 := bbase (se 5 (by rfl) ⟨204797, by rfl⟩ : syracuseStep 4369013 = 409595) (by norm_num)
theorem B2912675 : Blo 1941435 2912675 := bstep (se 1 (by rfl) ⟨2184506, by rfl⟩ : syracuseStep 2912675 = 4369013) B4369013
theorem B1941783 : Blo 1941435 1941783 := bstep (se 1 (by rfl) ⟨1456337, by rfl⟩ : syracuseStep 1941783 = 2912675) B2912675
theorem B9331109 : Blo 1941435 9331109 := bbase (se 4 (by rfl) ⟨874791, by rfl⟩ : syracuseStep 9331109 = 1749583) (by norm_num)
theorem B6220739 : Blo 1941435 6220739 := bstep (se 1 (by rfl) ⟨4665554, by rfl⟩ : syracuseStep 6220739 = 9331109) B9331109
theorem B16588637 : Blo 1941435 16588637 := bstep (se 3 (by rfl) ⟨3110369, by rfl⟩ : syracuseStep 16588637 = 6220739) B6220739
theorem B11059091 : Blo 1941435 11059091 := bstep (se 1 (by rfl) ⟨8294318, by rfl⟩ : syracuseStep 11059091 = 16588637) B16588637
theorem B7372727 : Blo 1941435 7372727 := bstep (se 1 (by rfl) ⟨5529545, by rfl⟩ : syracuseStep 7372727 = 11059091) B11059091
theorem B4915151 : Blo 1941435 4915151 := bstep (se 1 (by rfl) ⟨3686363, by rfl⟩ : syracuseStep 4915151 = 7372727) B7372727
theorem B3276767 : Blo 1941435 3276767 := bstep (se 1 (by rfl) ⟨2457575, by rfl⟩ : syracuseStep 3276767 = 4915151) B4915151
theorem B2184511 : Blo 1941435 2184511 := bstep (se 1 (by rfl) ⟨1638383, by rfl⟩ : syracuseStep 2184511 = 3276767) B3276767
theorem B2912681 : Blo 1941435 2912681 := bstep (se 2 (by rfl) ⟨1092255, by rfl⟩ : syracuseStep 2912681 = 2184511) B2184511
theorem B1941787 : Blo 1941435 1941787 := bstep (se 1 (by rfl) ⟨1456340, by rfl⟩ : syracuseStep 1941787 = 2912681) B2912681
theorem B7372741 : Blo 1941435 7372741 := bbase (se 4 (by rfl) ⟨691194, by rfl⟩ : syracuseStep 7372741 = 1382389) (by norm_num)
theorem B9830321 : Blo 1941435 9830321 := bstep (se 2 (by rfl) ⟨3686370, by rfl⟩ : syracuseStep 9830321 = 7372741) B7372741
theorem B6553547 : Blo 1941435 6553547 := bstep (se 1 (by rfl) ⟨4915160, by rfl⟩ : syracuseStep 6553547 = 9830321) B9830321
theorem B4369031 : Blo 1941435 4369031 := bstep (se 1 (by rfl) ⟨3276773, by rfl⟩ : syracuseStep 4369031 = 6553547) B6553547
theorem B2912687 : Blo 1941435 2912687 := bstep (se 1 (by rfl) ⟨2184515, by rfl⟩ : syracuseStep 2912687 = 4369031) B4369031
theorem B1941791 : Blo 1941435 1941791 := bstep (se 1 (by rfl) ⟨1456343, by rfl⟩ : syracuseStep 1941791 = 2912687) B2912687
theorem B2912693 : Blo 1941435 2912693 := bbase (se 5 (by rfl) ⟨136532, by rfl⟩ : syracuseStep 2912693 = 273065) (by norm_num)
theorem B1941795 : Blo 1941435 1941795 := bstep (se 1 (by rfl) ⟨1456346, by rfl⟩ : syracuseStep 1941795 = 2912693) B2912693
theorem B4915181 : Blo 1941435 4915181 := bbase (se 3 (by rfl) ⟨921596, by rfl⟩ : syracuseStep 4915181 = 1843193) (by norm_num)
theorem B3276787 : Blo 1941435 3276787 := bstep (se 1 (by rfl) ⟨2457590, by rfl⟩ : syracuseStep 3276787 = 4915181) B4915181
theorem B4369049 : Blo 1941435 4369049 := bstep (se 2 (by rfl) ⟨1638393, by rfl⟩ : syracuseStep 4369049 = 3276787) B3276787
theorem B2912699 : Blo 1941435 2912699 := bstep (se 1 (by rfl) ⟨2184524, by rfl⟩ : syracuseStep 2912699 = 4369049) B4369049
theorem B1941799 : Blo 1941435 1941799 := bstep (se 1 (by rfl) ⟨1456349, by rfl⟩ : syracuseStep 1941799 = 2912699) B2912699
theorem B2184529 : Blo 1941435 2184529 := bbase (se 2 (by rfl) ⟨819198, by rfl⟩ : syracuseStep 2184529 = 1638397) (by norm_num)
theorem B2912705 : Blo 1941435 2912705 := bstep (se 2 (by rfl) ⟨1092264, by rfl⟩ : syracuseStep 2912705 = 2184529) B2184529
theorem B1941803 : Blo 1941435 1941803 := bstep (se 1 (by rfl) ⟨1456352, by rfl⟩ : syracuseStep 1941803 = 2912705) B2912705
theorem B2073601 : Blo 1941435 2073601 := bbase (se 2 (by rfl) ⟨777600, by rfl⟩ : syracuseStep 2073601 = 1555201) (by norm_num)
theorem B2764801 : Blo 1941435 2764801 := bstep (se 2 (by rfl) ⟨1036800, by rfl⟩ : syracuseStep 2764801 = 2073601) B2073601
theorem B3686401 : Blo 1941435 3686401 := bstep (se 2 (by rfl) ⟨1382400, by rfl⟩ : syracuseStep 3686401 = 2764801) B2764801
theorem B4915201 : Blo 1941435 4915201 := bstep (se 2 (by rfl) ⟨1843200, by rfl⟩ : syracuseStep 4915201 = 3686401) B3686401
theorem B6553601 : Blo 1941435 6553601 := bstep (se 2 (by rfl) ⟨2457600, by rfl⟩ : syracuseStep 6553601 = 4915201) B4915201
theorem B4369067 : Blo 1941435 4369067 := bstep (se 1 (by rfl) ⟨3276800, by rfl⟩ : syracuseStep 4369067 = 6553601) B6553601
theorem B2912711 : Blo 1941435 2912711 := bstep (se 1 (by rfl) ⟨2184533, by rfl⟩ : syracuseStep 2912711 = 4369067) B4369067
theorem B1941807 : Blo 1941435 1941807 := bstep (se 1 (by rfl) ⟨1456355, by rfl⟩ : syracuseStep 1941807 = 2912711) B2912711
theorem B2912717 : Blo 1941435 2912717 := bbase (se 3 (by rfl) ⟨546134, by rfl⟩ : syracuseStep 2912717 = 1092269) (by norm_num)
theorem B1941811 : Blo 1941435 1941811 := bstep (se 1 (by rfl) ⟨1456358, by rfl⟩ : syracuseStep 1941811 = 2912717) B2912717
theorem B4369085 : Blo 1941435 4369085 := bbase (se 3 (by rfl) ⟨819203, by rfl⟩ : syracuseStep 4369085 = 1638407) (by norm_num)
theorem B2912723 : Blo 1941435 2912723 := bstep (se 1 (by rfl) ⟨2184542, by rfl⟩ : syracuseStep 2912723 = 4369085) B4369085
theorem B1941815 : Blo 1941435 1941815 := bstep (se 1 (by rfl) ⟨1456361, by rfl⟩ : syracuseStep 1941815 = 2912723) B2912723
theorem B3276821 : Blo 1941435 3276821 := bbase (se 6 (by rfl) ⟨76800, by rfl⟩ : syracuseStep 3276821 = 153601) (by norm_num)
theorem B2184547 : Blo 1941435 2184547 := bstep (se 1 (by rfl) ⟨1638410, by rfl⟩ : syracuseStep 2184547 = 3276821) B3276821
theorem B2912729 : Blo 1941435 2912729 := bstep (se 2 (by rfl) ⟨1092273, by rfl⟩ : syracuseStep 2912729 = 2184547) B2184547
theorem B1941819 : Blo 1941435 1941819 := bstep (se 1 (by rfl) ⟨1456364, by rfl⟩ : syracuseStep 1941819 = 2912729) B2912729
theorem B3787709 : Blo 1941435 3787709 := bbase (se 3 (by rfl) ⟨710195, by rfl⟩ : syracuseStep 3787709 = 1420391) (by norm_num)
theorem B10100557 : Blo 1941435 10100557 := bstep (se 3 (by rfl) ⟨1893854, by rfl⟩ : syracuseStep 10100557 = 3787709) B3787709
theorem B53869637 : Blo 1941435 53869637 := bstep (se 4 (by rfl) ⟨5050278, by rfl⟩ : syracuseStep 53869637 = 10100557) B10100557
theorem B143652365 : Blo 1941435 143652365 := bstep (se 3 (by rfl) ⟨26934818, by rfl⟩ : syracuseStep 143652365 = 53869637) B53869637
theorem B95768243 : Blo 1941435 95768243 := bstep (se 1 (by rfl) ⟨71826182, by rfl⟩ : syracuseStep 95768243 = 143652365) B143652365
theorem B63845495 : Blo 1941435 63845495 := bstep (se 1 (by rfl) ⟨47884121, by rfl⟩ : syracuseStep 63845495 = 95768243) B95768243
theorem B42563663 : Blo 1941435 42563663 := bstep (se 1 (by rfl) ⟨31922747, by rfl⟩ : syracuseStep 42563663 = 63845495) B63845495
theorem B28375775 : Blo 1941435 28375775 := bstep (se 1 (by rfl) ⟨21281831, by rfl⟩ : syracuseStep 28375775 = 42563663) B42563663
theorem B18917183 : Blo 1941435 18917183 := bstep (se 1 (by rfl) ⟨14187887, by rfl⟩ : syracuseStep 18917183 = 28375775) B28375775
theorem B50445821 : Blo 1941435 50445821 := bstep (se 3 (by rfl) ⟨9458591, by rfl⟩ : syracuseStep 50445821 = 18917183) B18917183
theorem B33630547 : Blo 1941435 33630547 := bstep (se 1 (by rfl) ⟨25222910, by rfl⟩ : syracuseStep 33630547 = 50445821) B50445821
theorem B44840729 : Blo 1941435 44840729 := bstep (se 2 (by rfl) ⟨16815273, by rfl⟩ : syracuseStep 44840729 = 33630547) B33630547
theorem B29893819 : Blo 1941435 29893819 := bstep (se 1 (by rfl) ⟨22420364, by rfl⟩ : syracuseStep 29893819 = 44840729) B44840729
theorem B39858425 : Blo 1941435 39858425 := bstep (se 2 (by rfl) ⟨14946909, by rfl⟩ : syracuseStep 39858425 = 29893819) B29893819
theorem B26572283 : Blo 1941435 26572283 := bstep (se 1 (by rfl) ⟨19929212, by rfl⟩ : syracuseStep 26572283 = 39858425) B39858425
theorem B17714855 : Blo 1941435 17714855 := bstep (se 1 (by rfl) ⟨13286141, by rfl⟩ : syracuseStep 17714855 = 26572283) B26572283
theorem B11809903 : Blo 1941435 11809903 := bstep (se 1 (by rfl) ⟨8857427, by rfl⟩ : syracuseStep 11809903 = 17714855) B17714855
theorem B15746537 : Blo 1941435 15746537 := bstep (se 2 (by rfl) ⟨5904951, by rfl⟩ : syracuseStep 15746537 = 11809903) B11809903
theorem B10497691 : Blo 1941435 10497691 := bstep (se 1 (by rfl) ⟨7873268, by rfl⟩ : syracuseStep 10497691 = 15746537) B15746537
theorem B13996921 : Blo 1941435 13996921 := bstep (se 2 (by rfl) ⟨5248845, by rfl⟩ : syracuseStep 13996921 = 10497691) B10497691
theorem B18662561 : Blo 1941435 18662561 := bstep (se 2 (by rfl) ⟨6998460, by rfl⟩ : syracuseStep 18662561 = 13996921) B13996921
theorem B12441707 : Blo 1941435 12441707 := bstep (se 1 (by rfl) ⟨9331280, by rfl⟩ : syracuseStep 12441707 = 18662561) B18662561
theorem B8294471 : Blo 1941435 8294471 := bstep (se 1 (by rfl) ⟨6220853, by rfl⟩ : syracuseStep 8294471 = 12441707) B12441707
theorem B5529647 : Blo 1941435 5529647 := bstep (se 1 (by rfl) ⟨4147235, by rfl⟩ : syracuseStep 5529647 = 8294471) B8294471
theorem B14745725 : Blo 1941435 14745725 := bstep (se 3 (by rfl) ⟨2764823, by rfl⟩ : syracuseStep 14745725 = 5529647) B5529647
theorem B9830483 : Blo 1941435 9830483 := bstep (se 1 (by rfl) ⟨7372862, by rfl⟩ : syracuseStep 9830483 = 14745725) B14745725
theorem B6553655 : Blo 1941435 6553655 := bstep (se 1 (by rfl) ⟨4915241, by rfl⟩ : syracuseStep 6553655 = 9830483) B9830483
theorem B4369103 : Blo 1941435 4369103 := bstep (se 1 (by rfl) ⟨3276827, by rfl⟩ : syracuseStep 4369103 = 6553655) B6553655
theorem B2912735 : Blo 1941435 2912735 := bstep (se 1 (by rfl) ⟨2184551, by rfl⟩ : syracuseStep 2912735 = 4369103) B4369103
theorem B1941823 : Blo 1941435 1941823 := bstep (se 1 (by rfl) ⟨1456367, by rfl⟩ : syracuseStep 1941823 = 2912735) B2912735
theorem B2912741 : Blo 1941435 2912741 := bbase (se 4 (by rfl) ⟨273069, by rfl⟩ : syracuseStep 2912741 = 546139) (by norm_num)
theorem B1941827 : Blo 1941435 1941827 := bstep (se 1 (by rfl) ⟨1456370, by rfl⟩ : syracuseStep 1941827 = 2912741) B2912741
theorem B17714933 : Blo 1941435 17714933 := bbase (se 5 (by rfl) ⟨830387, by rfl⟩ : syracuseStep 17714933 = 1660775) (by norm_num)
theorem B11809955 : Blo 1941435 11809955 := bstep (se 1 (by rfl) ⟨8857466, by rfl⟩ : syracuseStep 11809955 = 17714933) B17714933
theorem B7873303 : Blo 1941435 7873303 := bstep (se 1 (by rfl) ⟨5904977, by rfl⟩ : syracuseStep 7873303 = 11809955) B11809955
theorem B10497737 : Blo 1941435 10497737 := bstep (se 2 (by rfl) ⟨3936651, by rfl⟩ : syracuseStep 10497737 = 7873303) B7873303
theorem B6998491 : Blo 1941435 6998491 := bstep (se 1 (by rfl) ⟨5248868, by rfl⟩ : syracuseStep 6998491 = 10497737) B10497737
theorem B9331321 : Blo 1941435 9331321 := bstep (se 2 (by rfl) ⟨3499245, by rfl⟩ : syracuseStep 9331321 = 6998491) B6998491
theorem B12441761 : Blo 1941435 12441761 := bstep (se 2 (by rfl) ⟨4665660, by rfl⟩ : syracuseStep 12441761 = 9331321) B9331321
theorem B8294507 : Blo 1941435 8294507 := bstep (se 1 (by rfl) ⟨6220880, by rfl⟩ : syracuseStep 8294507 = 12441761) B12441761
theorem B5529671 : Blo 1941435 5529671 := bstep (se 1 (by rfl) ⟨4147253, by rfl⟩ : syracuseStep 5529671 = 8294507) B8294507
theorem B3686447 : Blo 1941435 3686447 := bstep (se 1 (by rfl) ⟨2764835, by rfl⟩ : syracuseStep 3686447 = 5529671) B5529671
theorem B2457631 : Blo 1941435 2457631 := bstep (se 1 (by rfl) ⟨1843223, by rfl⟩ : syracuseStep 2457631 = 3686447) B3686447
theorem B3276841 : Blo 1941435 3276841 := bstep (se 2 (by rfl) ⟨1228815, by rfl⟩ : syracuseStep 3276841 = 2457631) B2457631
theorem B4369121 : Blo 1941435 4369121 := bstep (se 2 (by rfl) ⟨1638420, by rfl⟩ : syracuseStep 4369121 = 3276841) B3276841
theorem B2912747 : Blo 1941435 2912747 := bstep (se 1 (by rfl) ⟨2184560, by rfl⟩ : syracuseStep 2912747 = 4369121) B4369121
theorem B1941831 : Blo 1941435 1941831 := bstep (se 1 (by rfl) ⟨1456373, by rfl⟩ : syracuseStep 1941831 = 2912747) B2912747
theorem B2184565 : Blo 1941435 2184565 := bbase (se 5 (by rfl) ⟨102401, by rfl⟩ : syracuseStep 2184565 = 204803) (by norm_num)
theorem B2912753 : Blo 1941435 2912753 := bstep (se 2 (by rfl) ⟨1092282, by rfl⟩ : syracuseStep 2912753 = 2184565) B2184565
theorem B1941835 : Blo 1941435 1941835 := bstep (se 1 (by rfl) ⟨1456376, by rfl⟩ : syracuseStep 1941835 = 2912753) B2912753
theorem B2457641 : Blo 1941435 2457641 := bbase (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) (by norm_num)
theorem B6553709 : Blo 1941435 6553709 := bstep (se 3 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 6553709 = 2457641) B2457641
theorem B4369139 : Blo 1941435 4369139 := bstep (se 1 (by rfl) ⟨3276854, by rfl⟩ : syracuseStep 4369139 = 6553709) B6553709
theorem B2912759 : Blo 1941435 2912759 := bstep (se 1 (by rfl) ⟨2184569, by rfl⟩ : syracuseStep 2912759 = 4369139) B4369139
theorem B1941839 : Blo 1941435 1941839 := bstep (se 1 (by rfl) ⟨1456379, by rfl⟩ : syracuseStep 1941839 = 2912759) B2912759
theorem B2912765 : Blo 1941435 2912765 := bbase (se 3 (by rfl) ⟨546143, by rfl⟩ : syracuseStep 2912765 = 1092287) (by norm_num)
theorem B1941843 : Blo 1941435 1941843 := bstep (se 1 (by rfl) ⟨1456382, by rfl⟩ : syracuseStep 1941843 = 2912765) B2912765
theorem B4369157 : Blo 1941435 4369157 := bbase (se 4 (by rfl) ⟨409608, by rfl⟩ : syracuseStep 4369157 = 819217) (by norm_num)
theorem B2912771 : Blo 1941435 2912771 := bstep (se 1 (by rfl) ⟨2184578, by rfl⟩ : syracuseStep 2912771 = 4369157) B4369157
theorem B1941847 : Blo 1941435 1941847 := bstep (se 1 (by rfl) ⟨1456385, by rfl⟩ : syracuseStep 1941847 = 2912771) B2912771
theorem B3686485 : Blo 1941435 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B4915313 : Blo 1941435 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B3276875 : Blo 1941435 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B2184583 : Blo 1941435 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B2912777 : Blo 1941435 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B1941851 : Blo 1941435 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B9830645 : Blo 1941435 9830645 := bbase (se 5 (by rfl) ⟨460811, by rfl⟩ : syracuseStep 9830645 = 921623) (by norm_num)
theorem B6553763 : Blo 1941435 6553763 := bstep (se 1 (by rfl) ⟨4915322, by rfl⟩ : syracuseStep 6553763 = 9830645) B9830645
theorem B4369175 : Blo 1941435 4369175 := bstep (se 1 (by rfl) ⟨3276881, by rfl⟩ : syracuseStep 4369175 = 6553763) B6553763
theorem B2912783 : Blo 1941435 2912783 := bstep (se 1 (by rfl) ⟨2184587, by rfl⟩ : syracuseStep 2912783 = 4369175) B4369175
theorem B1941855 : Blo 1941435 1941855 := bstep (se 1 (by rfl) ⟨1456391, by rfl⟩ : syracuseStep 1941855 = 2912783) B2912783
theorem B2912789 : Blo 1941435 2912789 := bbase (se 6 (by rfl) ⟨68268, by rfl⟩ : syracuseStep 2912789 = 136537) (by norm_num)
theorem B1941859 : Blo 1941435 1941859 := bstep (se 1 (by rfl) ⟨1456394, by rfl⟩ : syracuseStep 1941859 = 2912789) B2912789
theorem B3321605 : Blo 1941435 3321605 := bbase (se 4 (by rfl) ⟨311400, by rfl⟩ : syracuseStep 3321605 = 622801) (by norm_num)
theorem B8857613 : Blo 1941435 8857613 := bstep (se 3 (by rfl) ⟨1660802, by rfl⟩ : syracuseStep 8857613 = 3321605) B3321605
theorem B5905075 : Blo 1941435 5905075 := bstep (se 1 (by rfl) ⟨4428806, by rfl⟩ : syracuseStep 5905075 = 8857613) B8857613
theorem B7873433 : Blo 1941435 7873433 := bstep (se 2 (by rfl) ⟨2952537, by rfl⟩ : syracuseStep 7873433 = 5905075) B5905075
theorem B5248955 : Blo 1941435 5248955 := bstep (se 1 (by rfl) ⟨3936716, by rfl⟩ : syracuseStep 5248955 = 7873433) B7873433
theorem B3499303 : Blo 1941435 3499303 := bstep (se 1 (by rfl) ⟨2624477, by rfl⟩ : syracuseStep 3499303 = 5248955) B5248955
theorem B4665737 : Blo 1941435 4665737 := bstep (se 2 (by rfl) ⟨1749651, by rfl⟩ : syracuseStep 4665737 = 3499303) B3499303
theorem B3110491 : Blo 1941435 3110491 := bstep (se 1 (by rfl) ⟨2332868, by rfl⟩ : syracuseStep 3110491 = 4665737) B4665737
theorem B16589285 : Blo 1941435 16589285 := bstep (se 4 (by rfl) ⟨1555245, by rfl⟩ : syracuseStep 16589285 = 3110491) B3110491
theorem B11059523 : Blo 1941435 11059523 := bstep (se 1 (by rfl) ⟨8294642, by rfl⟩ : syracuseStep 11059523 = 16589285) B16589285
theorem B7373015 : Blo 1941435 7373015 := bstep (se 1 (by rfl) ⟨5529761, by rfl⟩ : syracuseStep 7373015 = 11059523) B11059523
theorem B4915343 : Blo 1941435 4915343 := bstep (se 1 (by rfl) ⟨3686507, by rfl⟩ : syracuseStep 4915343 = 7373015) B7373015
theorem B3276895 : Blo 1941435 3276895 := bstep (se 1 (by rfl) ⟨2457671, by rfl⟩ : syracuseStep 3276895 = 4915343) B4915343
theorem B4369193 : Blo 1941435 4369193 := bstep (se 2 (by rfl) ⟨1638447, by rfl⟩ : syracuseStep 4369193 = 3276895) B3276895
theorem B2912795 : Blo 1941435 2912795 := bstep (se 1 (by rfl) ⟨2184596, by rfl⟩ : syracuseStep 2912795 = 4369193) B4369193
theorem B1941863 : Blo 1941435 1941863 := bstep (se 1 (by rfl) ⟨1456397, by rfl⟩ : syracuseStep 1941863 = 2912795) B2912795
theorem B2184601 : Blo 1941435 2184601 := bbase (se 2 (by rfl) ⟨819225, by rfl⟩ : syracuseStep 2184601 = 1638451) (by norm_num)
theorem B2912801 : Blo 1941435 2912801 := bstep (se 2 (by rfl) ⟨1092300, by rfl⟩ : syracuseStep 2912801 = 2184601) B2184601
theorem B1941867 : Blo 1941435 1941867 := bstep (se 1 (by rfl) ⟨1456400, by rfl⟩ : syracuseStep 1941867 = 2912801) B2912801
theorem B7373045 : Blo 1941435 7373045 := bbase (se 5 (by rfl) ⟨345611, by rfl⟩ : syracuseStep 7373045 = 691223) (by norm_num)
theorem B4915363 : Blo 1941435 4915363 := bstep (se 1 (by rfl) ⟨3686522, by rfl⟩ : syracuseStep 4915363 = 7373045) B7373045
theorem B6553817 : Blo 1941435 6553817 := bstep (se 2 (by rfl) ⟨2457681, by rfl⟩ : syracuseStep 6553817 = 4915363) B4915363
theorem B4369211 : Blo 1941435 4369211 := bstep (se 1 (by rfl) ⟨3276908, by rfl⟩ : syracuseStep 4369211 = 6553817) B6553817
theorem B2912807 : Blo 1941435 2912807 := bstep (se 1 (by rfl) ⟨2184605, by rfl⟩ : syracuseStep 2912807 = 4369211) B4369211
theorem B1941871 : Blo 1941435 1941871 := bstep (se 1 (by rfl) ⟨1456403, by rfl⟩ : syracuseStep 1941871 = 2912807) B2912807
theorem B2912813 : Blo 1941435 2912813 := bbase (se 3 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 2912813 = 1092305) (by norm_num)
theorem B1941875 : Blo 1941435 1941875 := bstep (se 1 (by rfl) ⟨1456406, by rfl⟩ : syracuseStep 1941875 = 2912813) B2912813
theorem B4369229 : Blo 1941435 4369229 := bbase (se 3 (by rfl) ⟨819230, by rfl⟩ : syracuseStep 4369229 = 1638461) (by norm_num)
theorem B2912819 : Blo 1941435 2912819 := bstep (se 1 (by rfl) ⟨2184614, by rfl⟩ : syracuseStep 2912819 = 4369229) B4369229
theorem B1941879 : Blo 1941435 1941879 := bstep (se 1 (by rfl) ⟨1456409, by rfl⟩ : syracuseStep 1941879 = 2912819) B2912819
theorem B2457697 : Blo 1941435 2457697 := bbase (se 2 (by rfl) ⟨921636, by rfl⟩ : syracuseStep 2457697 = 1843273) (by norm_num)
theorem B3276929 : Blo 1941435 3276929 := bstep (se 2 (by rfl) ⟨1228848, by rfl⟩ : syracuseStep 3276929 = 2457697) B2457697
theorem B2184619 : Blo 1941435 2184619 := bstep (se 1 (by rfl) ⟨1638464, by rfl⟩ : syracuseStep 2184619 = 3276929) B3276929
theorem B2912825 : Blo 1941435 2912825 := bstep (se 2 (by rfl) ⟨1092309, by rfl⟩ : syracuseStep 2912825 = 2184619) B2184619
theorem B1941883 : Blo 1941435 1941883 := bstep (se 1 (by rfl) ⟨1456412, by rfl⟩ : syracuseStep 1941883 = 2912825) B2912825
theorem B22119317 : Blo 1941435 22119317 := bbase (se 6 (by rfl) ⟨518421, by rfl⟩ : syracuseStep 22119317 = 1036843) (by norm_num)
theorem B14746211 : Blo 1941435 14746211 := bstep (se 1 (by rfl) ⟨11059658, by rfl⟩ : syracuseStep 14746211 = 22119317) B22119317
theorem B9830807 : Blo 1941435 9830807 := bstep (se 1 (by rfl) ⟨7373105, by rfl⟩ : syracuseStep 9830807 = 14746211) B14746211
theorem B6553871 : Blo 1941435 6553871 := bstep (se 1 (by rfl) ⟨4915403, by rfl⟩ : syracuseStep 6553871 = 9830807) B9830807
theorem B4369247 : Blo 1941435 4369247 := bstep (se 1 (by rfl) ⟨3276935, by rfl⟩ : syracuseStep 4369247 = 6553871) B6553871
theorem B2912831 : Blo 1941435 2912831 := bstep (se 1 (by rfl) ⟨2184623, by rfl⟩ : syracuseStep 2912831 = 4369247) B4369247
theorem B1941887 : Blo 1941435 1941887 := bstep (se 1 (by rfl) ⟨1456415, by rfl⟩ : syracuseStep 1941887 = 2912831) B2912831
theorem B2912837 : Blo 1941435 2912837 := bbase (se 4 (by rfl) ⟨273078, by rfl⟩ : syracuseStep 2912837 = 546157) (by norm_num)
theorem B1941891 : Blo 1941435 1941891 := bstep (se 1 (by rfl) ⟨1456418, by rfl⟩ : syracuseStep 1941891 = 2912837) B2912837
theorem B3276949 : Blo 1941435 3276949 := bbase (se 6 (by rfl) ⟨76803, by rfl⟩ : syracuseStep 3276949 = 153607) (by norm_num)
theorem B4369265 : Blo 1941435 4369265 := bstep (se 2 (by rfl) ⟨1638474, by rfl⟩ : syracuseStep 4369265 = 3276949) B3276949
theorem B2912843 : Blo 1941435 2912843 := bstep (se 1 (by rfl) ⟨2184632, by rfl⟩ : syracuseStep 2912843 = 4369265) B4369265
theorem B1941895 : Blo 1941435 1941895 := bstep (se 1 (by rfl) ⟨1456421, by rfl⟩ : syracuseStep 1941895 = 2912843) B2912843
theorem B2184637 : Blo 1941435 2184637 := bbase (se 3 (by rfl) ⟨409619, by rfl⟩ : syracuseStep 2184637 = 819239) (by norm_num)
theorem B2912849 : Blo 1941435 2912849 := bstep (se 2 (by rfl) ⟨1092318, by rfl⟩ : syracuseStep 2912849 = 2184637) B2184637
theorem B1941899 : Blo 1941435 1941899 := bstep (se 1 (by rfl) ⟨1456424, by rfl⟩ : syracuseStep 1941899 = 2912849) B2912849
theorem B6553925 : Blo 1941435 6553925 := bbase (se 4 (by rfl) ⟨614430, by rfl⟩ : syracuseStep 6553925 = 1228861) (by norm_num)
theorem B4369283 : Blo 1941435 4369283 := bstep (se 1 (by rfl) ⟨3276962, by rfl⟩ : syracuseStep 4369283 = 6553925) B6553925
theorem B2912855 : Blo 1941435 2912855 := bstep (se 1 (by rfl) ⟨2184641, by rfl⟩ : syracuseStep 2912855 = 4369283) B4369283
theorem B1941903 : Blo 1941435 1941903 := bstep (se 1 (by rfl) ⟨1456427, by rfl⟩ : syracuseStep 1941903 = 2912855) B2912855
theorem B2912861 : Blo 1941435 2912861 := bbase (se 3 (by rfl) ⟨546161, by rfl⟩ : syracuseStep 2912861 = 1092323) (by norm_num)
theorem B1941907 : Blo 1941435 1941907 := bstep (se 1 (by rfl) ⟨1456430, by rfl⟩ : syracuseStep 1941907 = 2912861) B2912861
theorem B4369301 : Blo 1941435 4369301 := bbase (se 6 (by rfl) ⟨102405, by rfl⟩ : syracuseStep 4369301 = 204811) (by norm_num)
theorem B2912867 : Blo 1941435 2912867 := bstep (se 1 (by rfl) ⟨2184650, by rfl⟩ : syracuseStep 2912867 = 4369301) B4369301
theorem B1941911 : Blo 1941435 1941911 := bstep (se 1 (by rfl) ⟨1456433, by rfl⟩ : syracuseStep 1941911 = 2912867) B2912867
theorem B16816085 : Blo 1941435 16816085 := bbase (se 7 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 16816085 = 394127) (by norm_num)
theorem B11210723 : Blo 1941435 11210723 := bstep (se 1 (by rfl) ⟨8408042, by rfl⟩ : syracuseStep 11210723 = 16816085) B16816085
theorem B7473815 : Blo 1941435 7473815 := bstep (se 1 (by rfl) ⟨5605361, by rfl⟩ : syracuseStep 7473815 = 11210723) B11210723
theorem B4982543 : Blo 1941435 4982543 := bstep (se 1 (by rfl) ⟨3736907, by rfl⟩ : syracuseStep 4982543 = 7473815) B7473815
theorem B3321695 : Blo 1941435 3321695 := bstep (se 1 (by rfl) ⟨2491271, by rfl⟩ : syracuseStep 3321695 = 4982543) B4982543
theorem B2214463 : Blo 1941435 2214463 := bstep (se 1 (by rfl) ⟨1660847, by rfl⟩ : syracuseStep 2214463 = 3321695) B3321695
theorem B2952617 : Blo 1941435 2952617 := bstep (se 2 (by rfl) ⟨1107231, by rfl⟩ : syracuseStep 2952617 = 2214463) B2214463
theorem B7873645 : Blo 1941435 7873645 := bstep (se 3 (by rfl) ⟨1476308, by rfl⟩ : syracuseStep 7873645 = 2952617) B2952617
theorem B10498193 : Blo 1941435 10498193 := bstep (se 2 (by rfl) ⟨3936822, by rfl⟩ : syracuseStep 10498193 = 7873645) B7873645
theorem B6998795 : Blo 1941435 6998795 := bstep (se 1 (by rfl) ⟨5249096, by rfl⟩ : syracuseStep 6998795 = 10498193) B10498193
theorem B4665863 : Blo 1941435 4665863 := bstep (se 1 (by rfl) ⟨3499397, by rfl⟩ : syracuseStep 4665863 = 6998795) B6998795
theorem B3110575 : Blo 1941435 3110575 := bstep (se 1 (by rfl) ⟨2332931, by rfl⟩ : syracuseStep 3110575 = 4665863) B4665863
theorem B4147433 : Blo 1941435 4147433 := bstep (se 2 (by rfl) ⟨1555287, by rfl⟩ : syracuseStep 4147433 = 3110575) B3110575
theorem B2764955 : Blo 1941435 2764955 := bstep (se 1 (by rfl) ⟨2073716, by rfl⟩ : syracuseStep 2764955 = 4147433) B4147433
theorem B7373213 : Blo 1941435 7373213 := bstep (se 3 (by rfl) ⟨1382477, by rfl⟩ : syracuseStep 7373213 = 2764955) B2764955
theorem B4915475 : Blo 1941435 4915475 := bstep (se 1 (by rfl) ⟨3686606, by rfl⟩ : syracuseStep 4915475 = 7373213) B7373213
theorem B3276983 : Blo 1941435 3276983 := bstep (se 1 (by rfl) ⟨2457737, by rfl⟩ : syracuseStep 3276983 = 4915475) B4915475
theorem B2184655 : Blo 1941435 2184655 := bstep (se 1 (by rfl) ⟨1638491, by rfl⟩ : syracuseStep 2184655 = 3276983) B3276983
theorem B2912873 : Blo 1941435 2912873 := bstep (se 2 (by rfl) ⟨1092327, by rfl⟩ : syracuseStep 2912873 = 2184655) B2184655
theorem B1941915 : Blo 1941435 1941915 := bstep (se 1 (by rfl) ⟨1456436, by rfl⟩ : syracuseStep 1941915 = 2912873) B2912873
theorem B15747317 : Blo 1941435 15747317 := bbase (se 5 (by rfl) ⟨738155, by rfl⟩ : syracuseStep 15747317 = 1476311) (by norm_num)
theorem B10498211 : Blo 1941435 10498211 := bstep (se 1 (by rfl) ⟨7873658, by rfl⟩ : syracuseStep 10498211 = 15747317) B15747317
theorem B6998807 : Blo 1941435 6998807 := bstep (se 1 (by rfl) ⟨5249105, by rfl⟩ : syracuseStep 6998807 = 10498211) B10498211
theorem B4665871 : Blo 1941435 4665871 := bstep (se 1 (by rfl) ⟨3499403, by rfl⟩ : syracuseStep 4665871 = 6998807) B6998807
theorem B6221161 : Blo 1941435 6221161 := bstep (se 2 (by rfl) ⟨2332935, by rfl⟩ : syracuseStep 6221161 = 4665871) B4665871
theorem B8294881 : Blo 1941435 8294881 := bstep (se 2 (by rfl) ⟨3110580, by rfl⟩ : syracuseStep 8294881 = 6221161) B6221161
theorem B11059841 : Blo 1941435 11059841 := bstep (se 2 (by rfl) ⟨4147440, by rfl⟩ : syracuseStep 11059841 = 8294881) B8294881
theorem B7373227 : Blo 1941435 7373227 := bstep (se 1 (by rfl) ⟨5529920, by rfl⟩ : syracuseStep 7373227 = 11059841) B11059841
theorem B9830969 : Blo 1941435 9830969 := bstep (se 2 (by rfl) ⟨3686613, by rfl⟩ : syracuseStep 9830969 = 7373227) B7373227
theorem B6553979 : Blo 1941435 6553979 := bstep (se 1 (by rfl) ⟨4915484, by rfl⟩ : syracuseStep 6553979 = 9830969) B9830969
theorem B4369319 : Blo 1941435 4369319 := bstep (se 1 (by rfl) ⟨3276989, by rfl⟩ : syracuseStep 4369319 = 6553979) B6553979
theorem B2912879 : Blo 1941435 2912879 := bstep (se 1 (by rfl) ⟨2184659, by rfl⟩ : syracuseStep 2912879 = 4369319) B4369319
theorem B1941919 : Blo 1941435 1941919 := bstep (se 1 (by rfl) ⟨1456439, by rfl⟩ : syracuseStep 1941919 = 2912879) B2912879
theorem B2912885 : Blo 1941435 2912885 := bbase (se 5 (by rfl) ⟨136541, by rfl⟩ : syracuseStep 2912885 = 273083) (by norm_num)
theorem B1941923 : Blo 1941435 1941923 := bstep (se 1 (by rfl) ⟨1456442, by rfl⟩ : syracuseStep 1941923 = 2912885) B2912885
theorem B3686629 : Blo 1941435 3686629 := bbase (se 4 (by rfl) ⟨345621, by rfl⟩ : syracuseStep 3686629 = 691243) (by norm_num)
theorem B4915505 : Blo 1941435 4915505 := bstep (se 2 (by rfl) ⟨1843314, by rfl⟩ : syracuseStep 4915505 = 3686629) B3686629
theorem B3277003 : Blo 1941435 3277003 := bstep (se 1 (by rfl) ⟨2457752, by rfl⟩ : syracuseStep 3277003 = 4915505) B4915505
theorem B4369337 : Blo 1941435 4369337 := bstep (se 2 (by rfl) ⟨1638501, by rfl⟩ : syracuseStep 4369337 = 3277003) B3277003
theorem B2912891 : Blo 1941435 2912891 := bstep (se 1 (by rfl) ⟨2184668, by rfl⟩ : syracuseStep 2912891 = 4369337) B4369337
theorem B1941927 : Blo 1941435 1941927 := bstep (se 1 (by rfl) ⟨1456445, by rfl⟩ : syracuseStep 1941927 = 2912891) B2912891
theorem B2184673 : Blo 1941435 2184673 := bbase (se 2 (by rfl) ⟨819252, by rfl⟩ : syracuseStep 2184673 = 1638505) (by norm_num)
theorem B2912897 : Blo 1941435 2912897 := bstep (se 2 (by rfl) ⟨1092336, by rfl⟩ : syracuseStep 2912897 = 2184673) B2184673
theorem B1941931 : Blo 1941435 1941931 := bstep (se 1 (by rfl) ⟨1456448, by rfl⟩ : syracuseStep 1941931 = 2912897) B2912897
theorem B4915525 : Blo 1941435 4915525 := bbase (se 4 (by rfl) ⟨460830, by rfl⟩ : syracuseStep 4915525 = 921661) (by norm_num)
theorem B6554033 : Blo 1941435 6554033 := bstep (se 2 (by rfl) ⟨2457762, by rfl⟩ : syracuseStep 6554033 = 4915525) B4915525
theorem B4369355 : Blo 1941435 4369355 := bstep (se 1 (by rfl) ⟨3277016, by rfl⟩ : syracuseStep 4369355 = 6554033) B6554033
theorem B2912903 : Blo 1941435 2912903 := bstep (se 1 (by rfl) ⟨2184677, by rfl⟩ : syracuseStep 2912903 = 4369355) B4369355
theorem B1941935 : Blo 1941435 1941935 := bstep (se 1 (by rfl) ⟨1456451, by rfl⟩ : syracuseStep 1941935 = 2912903) B2912903
theorem B2912909 : Blo 1941435 2912909 := bbase (se 3 (by rfl) ⟨546170, by rfl⟩ : syracuseStep 2912909 = 1092341) (by norm_num)
theorem B1941939 : Blo 1941435 1941939 := bstep (se 1 (by rfl) ⟨1456454, by rfl⟩ : syracuseStep 1941939 = 2912909) B2912909
theorem B4369373 : Blo 1941435 4369373 := bbase (se 3 (by rfl) ⟨819257, by rfl⟩ : syracuseStep 4369373 = 1638515) (by norm_num)
theorem B2912915 : Blo 1941435 2912915 := bstep (se 1 (by rfl) ⟨2184686, by rfl⟩ : syracuseStep 2912915 = 4369373) B4369373
theorem B1941943 : Blo 1941435 1941943 := bstep (se 1 (by rfl) ⟨1456457, by rfl⟩ : syracuseStep 1941943 = 2912915) B2912915
theorem B3277037 : Blo 1941435 3277037 := bbase (se 3 (by rfl) ⟨614444, by rfl⟩ : syracuseStep 3277037 = 1228889) (by norm_num)
theorem B2184691 : Blo 1941435 2184691 := bstep (se 1 (by rfl) ⟨1638518, by rfl⟩ : syracuseStep 2184691 = 3277037) B3277037
theorem B2912921 : Blo 1941435 2912921 := bstep (se 2 (by rfl) ⟨1092345, by rfl⟩ : syracuseStep 2912921 = 2184691) B2184691
theorem B1941947 : Blo 1941435 1941947 := bstep (se 1 (by rfl) ⟨1456460, by rfl⟩ : syracuseStep 1941947 = 2912921) B2912921
theorem B2164313 : Blo 1941435 2164313 := bbase (se 2 (by rfl) ⟨811617, by rfl⟩ : syracuseStep 2164313 = 1623235) (by norm_num)
theorem B5771501 : Blo 1941435 5771501 := bstep (se 3 (by rfl) ⟨1082156, by rfl⟩ : syracuseStep 5771501 = 2164313) B2164313
theorem B3847667 : Blo 1941435 3847667 := bstep (se 1 (by rfl) ⟨2885750, by rfl⟩ : syracuseStep 3847667 = 5771501) B5771501
theorem B10260445 : Blo 1941435 10260445 := bstep (se 3 (by rfl) ⟨1923833, by rfl⟩ : syracuseStep 10260445 = 3847667) B3847667
theorem B13680593 : Blo 1941435 13680593 := bstep (se 2 (by rfl) ⟨5130222, by rfl⟩ : syracuseStep 13680593 = 10260445) B10260445
theorem B9120395 : Blo 1941435 9120395 := bstep (se 1 (by rfl) ⟨6840296, by rfl⟩ : syracuseStep 9120395 = 13680593) B13680593
theorem B24321053 : Blo 1941435 24321053 := bstep (se 3 (by rfl) ⟨4560197, by rfl⟩ : syracuseStep 24321053 = 9120395) B9120395
theorem B16214035 : Blo 1941435 16214035 := bstep (se 1 (by rfl) ⟨12160526, by rfl⟩ : syracuseStep 16214035 = 24321053) B24321053
theorem B21618713 : Blo 1941435 21618713 := bstep (se 2 (by rfl) ⟨8107017, by rfl⟩ : syracuseStep 21618713 = 16214035) B16214035
theorem B14412475 : Blo 1941435 14412475 := bstep (se 1 (by rfl) ⟨10809356, by rfl⟩ : syracuseStep 14412475 = 21618713) B21618713
theorem B19216633 : Blo 1941435 19216633 := bstep (se 2 (by rfl) ⟨7206237, by rfl⟩ : syracuseStep 19216633 = 14412475) B14412475
theorem B25622177 : Blo 1941435 25622177 := bstep (se 2 (by rfl) ⟨9608316, by rfl⟩ : syracuseStep 25622177 = 19216633) B19216633
theorem B68325805 : Blo 1941435 68325805 := bstep (se 3 (by rfl) ⟨12811088, by rfl⟩ : syracuseStep 68325805 = 25622177) B25622177
theorem B91101073 : Blo 1941435 91101073 := bstep (se 2 (by rfl) ⟨34162902, by rfl⟩ : syracuseStep 91101073 = 68325805) B68325805
theorem B121468097 : Blo 1941435 121468097 := bstep (se 2 (by rfl) ⟨45550536, by rfl⟩ : syracuseStep 121468097 = 91101073) B91101073
theorem B323914925 : Blo 1941435 323914925 := bstep (se 3 (by rfl) ⟨60734048, by rfl⟩ : syracuseStep 323914925 = 121468097) B121468097
theorem B215943283 : Blo 1941435 215943283 := bstep (se 1 (by rfl) ⟨161957462, by rfl⟩ : syracuseStep 215943283 = 323914925) B323914925
theorem B287924377 : Blo 1941435 287924377 := bstep (se 2 (by rfl) ⟨107971641, by rfl⟩ : syracuseStep 287924377 = 215943283) B215943283
theorem B383899169 : Blo 1941435 383899169 := bstep (se 2 (by rfl) ⟨143962188, by rfl⟩ : syracuseStep 383899169 = 287924377) B287924377
theorem B255932779 : Blo 1941435 255932779 := bstep (se 1 (by rfl) ⟨191949584, by rfl⟩ : syracuseStep 255932779 = 383899169) B383899169
theorem B341243705 : Blo 1941435 341243705 := bstep (se 2 (by rfl) ⟨127966389, by rfl⟩ : syracuseStep 341243705 = 255932779) B255932779
theorem B227495803 : Blo 1941435 227495803 := bstep (se 1 (by rfl) ⟨170621852, by rfl⟩ : syracuseStep 227495803 = 341243705) B341243705
theorem B303327737 : Blo 1941435 303327737 := bstep (se 2 (by rfl) ⟨113747901, by rfl⟩ : syracuseStep 303327737 = 227495803) B227495803
theorem B202218491 : Blo 1941435 202218491 := bstep (se 1 (by rfl) ⟨151663868, by rfl⟩ : syracuseStep 202218491 = 303327737) B303327737
theorem B539249309 : Blo 1941435 539249309 := bstep (se 3 (by rfl) ⟨101109245, by rfl⟩ : syracuseStep 539249309 = 202218491) B202218491
theorem B359499539 : Blo 1941435 359499539 := bstep (se 1 (by rfl) ⟨269624654, by rfl⟩ : syracuseStep 359499539 = 539249309) B539249309
theorem B239666359 : Blo 1941435 239666359 := bstep (se 1 (by rfl) ⟨179749769, by rfl⟩ : syracuseStep 239666359 = 359499539) B359499539
theorem B319555145 : Blo 1941435 319555145 := bstep (se 2 (by rfl) ⟨119833179, by rfl⟩ : syracuseStep 319555145 = 239666359) B239666359
theorem B213036763 : Blo 1941435 213036763 := bstep (se 1 (by rfl) ⟨159777572, by rfl⟩ : syracuseStep 213036763 = 319555145) B319555145
theorem B284049017 : Blo 1941435 284049017 := bstep (se 2 (by rfl) ⟨106518381, by rfl⟩ : syracuseStep 284049017 = 213036763) B213036763
theorem B189366011 : Blo 1941435 189366011 := bstep (se 1 (by rfl) ⟨142024508, by rfl⟩ : syracuseStep 189366011 = 284049017) B284049017
theorem B126244007 : Blo 1941435 126244007 := bstep (se 1 (by rfl) ⟨94683005, by rfl⟩ : syracuseStep 126244007 = 189366011) B189366011
theorem B84162671 : Blo 1941435 84162671 := bstep (se 1 (by rfl) ⟨63122003, by rfl⟩ : syracuseStep 84162671 = 126244007) B126244007
theorem B56108447 : Blo 1941435 56108447 := bstep (se 1 (by rfl) ⟨42081335, by rfl⟩ : syracuseStep 56108447 = 84162671) B84162671
theorem B37405631 : Blo 1941435 37405631 := bstep (se 1 (by rfl) ⟨28054223, by rfl⟩ : syracuseStep 37405631 = 56108447) B56108447
theorem B24937087 : Blo 1941435 24937087 := bstep (se 1 (by rfl) ⟨18702815, by rfl⟩ : syracuseStep 24937087 = 37405631) B37405631
theorem B33249449 : Blo 1941435 33249449 := bstep (se 2 (by rfl) ⟨12468543, by rfl⟩ : syracuseStep 33249449 = 24937087) B24937087
theorem B22166299 : Blo 1941435 22166299 := bstep (se 1 (by rfl) ⟨16624724, by rfl⟩ : syracuseStep 22166299 = 33249449) B33249449
theorem B29555065 : Blo 1941435 29555065 := bstep (se 2 (by rfl) ⟨11083149, by rfl⟩ : syracuseStep 29555065 = 22166299) B22166299
theorem B39406753 : Blo 1941435 39406753 := bstep (se 2 (by rfl) ⟨14777532, by rfl⟩ : syracuseStep 39406753 = 29555065) B29555065
theorem B210169349 : Blo 1941435 210169349 := bstep (se 4 (by rfl) ⟨19703376, by rfl⟩ : syracuseStep 210169349 = 39406753) B39406753
theorem B140112899 : Blo 1941435 140112899 := bstep (se 1 (by rfl) ⟨105084674, by rfl⟩ : syracuseStep 140112899 = 210169349) B210169349
theorem B93408599 : Blo 1941435 93408599 := bstep (se 1 (by rfl) ⟨70056449, by rfl⟩ : syracuseStep 93408599 = 140112899) B140112899
theorem B62272399 : Blo 1941435 62272399 := bstep (se 1 (by rfl) ⟨46704299, by rfl⟩ : syracuseStep 62272399 = 93408599) B93408599
theorem B83029865 : Blo 1941435 83029865 := bstep (se 2 (by rfl) ⟨31136199, by rfl⟩ : syracuseStep 83029865 = 62272399) B62272399
theorem B885651893 : Blo 1941435 885651893 := bstep (se 5 (by rfl) ⟨41514932, by rfl⟩ : syracuseStep 885651893 = 83029865) B83029865
theorem B590434595 : Blo 1941435 590434595 := bstep (se 1 (by rfl) ⟨442825946, by rfl⟩ : syracuseStep 590434595 = 885651893) B885651893
theorem B393623063 : Blo 1941435 393623063 := bstep (se 1 (by rfl) ⟨295217297, by rfl⟩ : syracuseStep 393623063 = 590434595) B590434595
theorem B262415375 : Blo 1941435 262415375 := bstep (se 1 (by rfl) ⟨196811531, by rfl⟩ : syracuseStep 262415375 = 393623063) B393623063
theorem B174943583 : Blo 1941435 174943583 := bstep (se 1 (by rfl) ⟨131207687, by rfl⟩ : syracuseStep 174943583 = 262415375) B262415375
theorem B116629055 : Blo 1941435 116629055 := bstep (se 1 (by rfl) ⟨87471791, by rfl⟩ : syracuseStep 116629055 = 174943583) B174943583
theorem B77752703 : Blo 1941435 77752703 := bstep (se 1 (by rfl) ⟨58314527, by rfl⟩ : syracuseStep 77752703 = 116629055) B116629055
theorem B51835135 : Blo 1941435 51835135 := bstep (se 1 (by rfl) ⟨38876351, by rfl⟩ : syracuseStep 51835135 = 77752703) B77752703
theorem B69113513 : Blo 1941435 69113513 := bstep (se 2 (by rfl) ⟨25917567, by rfl⟩ : syracuseStep 69113513 = 51835135) B51835135
theorem B46075675 : Blo 1941435 46075675 := bstep (se 1 (by rfl) ⟨34556756, by rfl⟩ : syracuseStep 46075675 = 69113513) B69113513
theorem B61434233 : Blo 1941435 61434233 := bstep (se 2 (by rfl) ⟨23037837, by rfl⟩ : syracuseStep 61434233 = 46075675) B46075675
theorem B40956155 : Blo 1941435 40956155 := bstep (se 1 (by rfl) ⟨30717116, by rfl⟩ : syracuseStep 40956155 = 61434233) B61434233
theorem B27304103 : Blo 1941435 27304103 := bstep (se 1 (by rfl) ⟨20478077, by rfl⟩ : syracuseStep 27304103 = 40956155) B40956155
theorem B18202735 : Blo 1941435 18202735 := bstep (se 1 (by rfl) ⟨13652051, by rfl⟩ : syracuseStep 18202735 = 27304103) B27304103
theorem B24270313 : Blo 1941435 24270313 := bstep (se 2 (by rfl) ⟨9101367, by rfl⟩ : syracuseStep 24270313 = 18202735) B18202735
theorem B32360417 : Blo 1941435 32360417 := bstep (se 2 (by rfl) ⟨12135156, by rfl⟩ : syracuseStep 32360417 = 24270313) B24270313
theorem B21573611 : Blo 1941435 21573611 := bstep (se 1 (by rfl) ⟨16180208, by rfl⟩ : syracuseStep 21573611 = 32360417) B32360417
theorem B14382407 : Blo 1941435 14382407 := bstep (se 1 (by rfl) ⟨10786805, by rfl⟩ : syracuseStep 14382407 = 21573611) B21573611
theorem B9588271 : Blo 1941435 9588271 := bstep (se 1 (by rfl) ⟨7191203, by rfl⟩ : syracuseStep 9588271 = 14382407) B14382407
theorem B12784361 : Blo 1941435 12784361 := bstep (se 2 (by rfl) ⟨4794135, by rfl⟩ : syracuseStep 12784361 = 9588271) B9588271
theorem B136366517 : Blo 1941435 136366517 := bstep (se 5 (by rfl) ⟨6392180, by rfl⟩ : syracuseStep 136366517 = 12784361) B12784361
theorem B90911011 : Blo 1941435 90911011 := bstep (se 1 (by rfl) ⟨68183258, by rfl⟩ : syracuseStep 90911011 = 136366517) B136366517
theorem B121214681 : Blo 1941435 121214681 := bstep (se 2 (by rfl) ⟨45455505, by rfl⟩ : syracuseStep 121214681 = 90911011) B90911011
theorem B80809787 : Blo 1941435 80809787 := bstep (se 1 (by rfl) ⟨60607340, by rfl⟩ : syracuseStep 80809787 = 121214681) B121214681
theorem B53873191 : Blo 1941435 53873191 := bstep (se 1 (by rfl) ⟨40404893, by rfl⟩ : syracuseStep 53873191 = 80809787) B80809787
theorem B71830921 : Blo 1941435 71830921 := bstep (se 2 (by rfl) ⟨26936595, by rfl⟩ : syracuseStep 71830921 = 53873191) B53873191
theorem B95774561 : Blo 1941435 95774561 := bstep (se 2 (by rfl) ⟨35915460, by rfl⟩ : syracuseStep 95774561 = 71830921) B71830921
theorem B63849707 : Blo 1941435 63849707 := bstep (se 1 (by rfl) ⟨47887280, by rfl⟩ : syracuseStep 63849707 = 95774561) B95774561
theorem B42566471 : Blo 1941435 42566471 := bstep (se 1 (by rfl) ⟨31924853, by rfl⟩ : syracuseStep 42566471 = 63849707) B63849707
theorem B28377647 : Blo 1941435 28377647 := bstep (se 1 (by rfl) ⟨21283235, by rfl⟩ : syracuseStep 28377647 = 42566471) B42566471
theorem B18918431 : Blo 1941435 18918431 := bstep (se 1 (by rfl) ⟨14188823, by rfl⟩ : syracuseStep 18918431 = 28377647) B28377647
theorem B12612287 : Blo 1941435 12612287 := bstep (se 1 (by rfl) ⟨9459215, by rfl⟩ : syracuseStep 12612287 = 18918431) B18918431
theorem B33632765 : Blo 1941435 33632765 := bstep (se 3 (by rfl) ⟨6306143, by rfl⟩ : syracuseStep 33632765 = 12612287) B12612287
theorem B22421843 : Blo 1941435 22421843 := bstep (se 1 (by rfl) ⟨16816382, by rfl⟩ : syracuseStep 22421843 = 33632765) B33632765
theorem B14947895 : Blo 1941435 14947895 := bstep (se 1 (by rfl) ⟨11210921, by rfl⟩ : syracuseStep 14947895 = 22421843) B22421843
theorem B9965263 : Blo 1941435 9965263 := bstep (se 1 (by rfl) ⟨7473947, by rfl⟩ : syracuseStep 9965263 = 14947895) B14947895
theorem B13287017 : Blo 1941435 13287017 := bstep (se 2 (by rfl) ⟨4982631, by rfl⟩ : syracuseStep 13287017 = 9965263) B9965263
theorem B8858011 : Blo 1941435 8858011 := bstep (se 1 (by rfl) ⟨6643508, by rfl⟩ : syracuseStep 8858011 = 13287017) B13287017
theorem B11810681 : Blo 1941435 11810681 := bstep (se 2 (by rfl) ⟨4429005, by rfl⟩ : syracuseStep 11810681 = 8858011) B8858011
theorem B7873787 : Blo 1941435 7873787 := bstep (se 1 (by rfl) ⟨5905340, by rfl⟩ : syracuseStep 7873787 = 11810681) B11810681
theorem B20996765 : Blo 1941435 20996765 := bstep (se 3 (by rfl) ⟨3936893, by rfl⟩ : syracuseStep 20996765 = 7873787) B7873787
theorem B13997843 : Blo 1941435 13997843 := bstep (se 1 (by rfl) ⟨10498382, by rfl⟩ : syracuseStep 13997843 = 20996765) B20996765
theorem B9331895 : Blo 1941435 9331895 := bstep (se 1 (by rfl) ⟨6998921, by rfl⟩ : syracuseStep 9331895 = 13997843) B13997843
theorem B24885053 : Blo 1941435 24885053 := bstep (se 3 (by rfl) ⟨4665947, by rfl⟩ : syracuseStep 24885053 = 9331895) B9331895
theorem B16590035 : Blo 1941435 16590035 := bstep (se 1 (by rfl) ⟨12442526, by rfl⟩ : syracuseStep 16590035 = 24885053) B24885053
theorem B11060023 : Blo 1941435 11060023 := bstep (se 1 (by rfl) ⟨8295017, by rfl⟩ : syracuseStep 11060023 = 16590035) B16590035
theorem B14746697 : Blo 1941435 14746697 := bstep (se 2 (by rfl) ⟨5530011, by rfl⟩ : syracuseStep 14746697 = 11060023) B11060023
theorem B9831131 : Blo 1941435 9831131 := bstep (se 1 (by rfl) ⟨7373348, by rfl⟩ : syracuseStep 9831131 = 14746697) B14746697
theorem B6554087 : Blo 1941435 6554087 := bstep (se 1 (by rfl) ⟨4915565, by rfl⟩ : syracuseStep 6554087 = 9831131) B9831131
theorem B4369391 : Blo 1941435 4369391 := bstep (se 1 (by rfl) ⟨3277043, by rfl⟩ : syracuseStep 4369391 = 6554087) B6554087
theorem B2912927 : Blo 1941435 2912927 := bstep (se 1 (by rfl) ⟨2184695, by rfl⟩ : syracuseStep 2912927 = 4369391) B4369391
theorem B1941951 : Blo 1941435 1941951 := bstep (se 1 (by rfl) ⟨1456463, by rfl⟩ : syracuseStep 1941951 = 2912927) B2912927
theorem B2912933 : Blo 1941435 2912933 := bbase (se 4 (by rfl) ⟨273087, by rfl⟩ : syracuseStep 2912933 = 546175) (by norm_num)
theorem B1941955 : Blo 1941435 1941955 := bstep (se 1 (by rfl) ⟨1456466, by rfl⟩ : syracuseStep 1941955 = 2912933) B2912933
theorem B2457793 : Blo 1941435 2457793 := bbase (se 2 (by rfl) ⟨921672, by rfl⟩ : syracuseStep 2457793 = 1843345) (by norm_num)
theorem B3277057 : Blo 1941435 3277057 := bstep (se 2 (by rfl) ⟨1228896, by rfl⟩ : syracuseStep 3277057 = 2457793) B2457793
theorem B4369409 : Blo 1941435 4369409 := bstep (se 2 (by rfl) ⟨1638528, by rfl⟩ : syracuseStep 4369409 = 3277057) B3277057
theorem B2912939 : Blo 1941435 2912939 := bstep (se 1 (by rfl) ⟨2184704, by rfl⟩ : syracuseStep 2912939 = 4369409) B4369409
theorem B1941959 : Blo 1941435 1941959 := bstep (se 1 (by rfl) ⟨1456469, by rfl⟩ : syracuseStep 1941959 = 2912939) B2912939
theorem B2184709 : Blo 1941435 2184709 := bbase (se 4 (by rfl) ⟨204816, by rfl⟩ : syracuseStep 2184709 = 409633) (by norm_num)
theorem B2912945 : Blo 1941435 2912945 := bstep (se 2 (by rfl) ⟨1092354, by rfl⟩ : syracuseStep 2912945 = 2184709) B2184709
theorem B1941963 : Blo 1941435 1941963 := bstep (se 1 (by rfl) ⟨1456472, by rfl⟩ : syracuseStep 1941963 = 2912945) B2912945
theorem B2765029 : Blo 1941435 2765029 := bbase (se 4 (by rfl) ⟨259221, by rfl⟩ : syracuseStep 2765029 = 518443) (by norm_num)
theorem B3686705 : Blo 1941435 3686705 := bstep (se 2 (by rfl) ⟨1382514, by rfl⟩ : syracuseStep 3686705 = 2765029) B2765029
theorem B2457803 : Blo 1941435 2457803 := bstep (se 1 (by rfl) ⟨1843352, by rfl⟩ : syracuseStep 2457803 = 3686705) B3686705
theorem B6554141 : Blo 1941435 6554141 := bstep (se 3 (by rfl) ⟨1228901, by rfl⟩ : syracuseStep 6554141 = 2457803) B2457803
theorem B4369427 : Blo 1941435 4369427 := bstep (se 1 (by rfl) ⟨3277070, by rfl⟩ : syracuseStep 4369427 = 6554141) B6554141
theorem B2912951 : Blo 1941435 2912951 := bstep (se 1 (by rfl) ⟨2184713, by rfl⟩ : syracuseStep 2912951 = 4369427) B4369427
theorem B1941967 : Blo 1941435 1941967 := bstep (se 1 (by rfl) ⟨1456475, by rfl⟩ : syracuseStep 1941967 = 2912951) B2912951
theorem B2912957 : Blo 1941435 2912957 := bbase (se 3 (by rfl) ⟨546179, by rfl⟩ : syracuseStep 2912957 = 1092359) (by norm_num)
theorem B1941971 : Blo 1941435 1941971 := bstep (se 1 (by rfl) ⟨1456478, by rfl⟩ : syracuseStep 1941971 = 2912957) B2912957
theorem B4369445 : Blo 1941435 4369445 := bbase (se 4 (by rfl) ⟨409635, by rfl⟩ : syracuseStep 4369445 = 819271) (by norm_num)
theorem B2912963 : Blo 1941435 2912963 := bstep (se 1 (by rfl) ⟨2184722, by rfl⟩ : syracuseStep 2912963 = 4369445) B4369445
theorem B1941975 : Blo 1941435 1941975 := bstep (se 1 (by rfl) ⟨1456481, by rfl⟩ : syracuseStep 1941975 = 2912963) B2912963
theorem B4915637 : Blo 1941435 4915637 := bbase (se 5 (by rfl) ⟨230420, by rfl⟩ : syracuseStep 4915637 = 460841) (by norm_num)
theorem B3277091 : Blo 1941435 3277091 := bstep (se 1 (by rfl) ⟨2457818, by rfl⟩ : syracuseStep 3277091 = 4915637) B4915637
theorem B2184727 : Blo 1941435 2184727 := bstep (se 1 (by rfl) ⟨1638545, by rfl⟩ : syracuseStep 2184727 = 3277091) B3277091
theorem B2912969 : Blo 1941435 2912969 := bstep (se 2 (by rfl) ⟨1092363, by rfl⟩ : syracuseStep 2912969 = 2184727) B2184727
theorem B1941979 : Blo 1941435 1941979 := bstep (se 1 (by rfl) ⟨1456484, by rfl⟩ : syracuseStep 1941979 = 2912969) B2912969
theorem B1995337 : Blo 1941435 1995337 := bbase (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) (by norm_num)
theorem B2660449 : Blo 1941435 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B3547265 : Blo 1941435 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B37837493 : Blo 1941435 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B25224995 : Blo 1941435 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B16816663 : Blo 1941435 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B89688869 : Blo 1941435 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B59792579 : Blo 1941435 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B39861719 : Blo 1941435 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B26574479 : Blo 1941435 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B17716319 : Blo 1941435 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B11810879 : Blo 1941435 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B7873919 : Blo 1941435 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B5249279 : Blo 1941435 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B3499519 : Blo 1941435 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B4666025 : Blo 1941435 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B12442733 : Blo 1941435 12442733 := bstep (se 3 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 12442733 = 4666025) B4666025
theorem B8295155 : Blo 1941435 8295155 := bstep (se 1 (by rfl) ⟨6221366, by rfl⟩ : syracuseStep 8295155 = 12442733) B12442733
theorem B5530103 : Blo 1941435 5530103 := bstep (se 1 (by rfl) ⟨4147577, by rfl⟩ : syracuseStep 5530103 = 8295155) B8295155
theorem B3686735 : Blo 1941435 3686735 := bstep (se 1 (by rfl) ⟨2765051, by rfl⟩ : syracuseStep 3686735 = 5530103) B5530103
theorem B9831293 : Blo 1941435 9831293 := bstep (se 3 (by rfl) ⟨1843367, by rfl⟩ : syracuseStep 9831293 = 3686735) B3686735
theorem B6554195 : Blo 1941435 6554195 := bstep (se 1 (by rfl) ⟨4915646, by rfl⟩ : syracuseStep 6554195 = 9831293) B9831293
theorem B4369463 : Blo 1941435 4369463 := bstep (se 1 (by rfl) ⟨3277097, by rfl⟩ : syracuseStep 4369463 = 6554195) B6554195
theorem B2912975 : Blo 1941435 2912975 := bstep (se 1 (by rfl) ⟨2184731, by rfl⟩ : syracuseStep 2912975 = 4369463) B4369463
theorem B1941983 : Blo 1941435 1941983 := bstep (se 1 (by rfl) ⟨1456487, by rfl⟩ : syracuseStep 1941983 = 2912975) B2912975
theorem B2912981 : Blo 1941435 2912981 := bbase (se 7 (by rfl) ⟨34136, by rfl⟩ : syracuseStep 2912981 = 68273) (by norm_num)
theorem B1941987 : Blo 1941435 1941987 := bstep (se 1 (by rfl) ⟨1456490, by rfl⟩ : syracuseStep 1941987 = 2912981) B2912981
theorem B4666045 : Blo 1941435 4666045 := bbase (se 3 (by rfl) ⟨874883, by rfl⟩ : syracuseStep 4666045 = 1749767) (by norm_num)
theorem B6221393 : Blo 1941435 6221393 := bstep (se 2 (by rfl) ⟨2333022, by rfl⟩ : syracuseStep 6221393 = 4666045) B4666045
theorem B4147595 : Blo 1941435 4147595 := bstep (se 1 (by rfl) ⟨3110696, by rfl⟩ : syracuseStep 4147595 = 6221393) B6221393
theorem B2765063 : Blo 1941435 2765063 := bstep (se 1 (by rfl) ⟨2073797, by rfl⟩ : syracuseStep 2765063 = 4147595) B4147595
theorem B7373501 : Blo 1941435 7373501 := bstep (se 3 (by rfl) ⟨1382531, by rfl⟩ : syracuseStep 7373501 = 2765063) B2765063
theorem B4915667 : Blo 1941435 4915667 := bstep (se 1 (by rfl) ⟨3686750, by rfl⟩ : syracuseStep 4915667 = 7373501) B7373501
theorem B3277111 : Blo 1941435 3277111 := bstep (se 1 (by rfl) ⟨2457833, by rfl⟩ : syracuseStep 3277111 = 4915667) B4915667
theorem B4369481 : Blo 1941435 4369481 := bstep (se 2 (by rfl) ⟨1638555, by rfl⟩ : syracuseStep 4369481 = 3277111) B3277111
theorem B2912987 : Blo 1941435 2912987 := bstep (se 1 (by rfl) ⟨2184740, by rfl⟩ : syracuseStep 2912987 = 4369481) B4369481
theorem B1941991 : Blo 1941435 1941991 := bstep (se 1 (by rfl) ⟨1456493, by rfl⟩ : syracuseStep 1941991 = 2912987) B2912987
theorem B2184745 : Blo 1941435 2184745 := bbase (se 2 (by rfl) ⟨819279, by rfl⟩ : syracuseStep 2184745 = 1638559) (by norm_num)
theorem B2912993 : Blo 1941435 2912993 := bstep (se 2 (by rfl) ⟨1092372, by rfl⟩ : syracuseStep 2912993 = 2184745) B2184745
theorem B1941995 : Blo 1941435 1941995 := bstep (se 1 (by rfl) ⟨1456496, by rfl⟩ : syracuseStep 1941995 = 2912993) B2912993
theorem B7474133 : Blo 1941435 7474133 := bbase (se 7 (by rfl) ⟨87587, by rfl⟩ : syracuseStep 7474133 = 175175) (by norm_num)
theorem B19931021 : Blo 1941435 19931021 := bstep (se 3 (by rfl) ⟨3737066, by rfl⟩ : syracuseStep 19931021 = 7474133) B7474133
theorem B13287347 : Blo 1941435 13287347 := bstep (se 1 (by rfl) ⟨9965510, by rfl⟩ : syracuseStep 13287347 = 19931021) B19931021
theorem B8858231 : Blo 1941435 8858231 := bstep (se 1 (by rfl) ⟨6643673, by rfl⟩ : syracuseStep 8858231 = 13287347) B13287347
theorem B5905487 : Blo 1941435 5905487 := bstep (se 1 (by rfl) ⟨4429115, by rfl⟩ : syracuseStep 5905487 = 8858231) B8858231
theorem B15747965 : Blo 1941435 15747965 := bstep (se 3 (by rfl) ⟨2952743, by rfl⟩ : syracuseStep 15747965 = 5905487) B5905487
theorem B10498643 : Blo 1941435 10498643 := bstep (se 1 (by rfl) ⟨7873982, by rfl⟩ : syracuseStep 10498643 = 15747965) B15747965
theorem B6999095 : Blo 1941435 6999095 := bstep (se 1 (by rfl) ⟨5249321, by rfl⟩ : syracuseStep 6999095 = 10498643) B10498643
theorem B18664253 : Blo 1941435 18664253 := bstep (se 3 (by rfl) ⟨3499547, by rfl⟩ : syracuseStep 18664253 = 6999095) B6999095
theorem B12442835 : Blo 1941435 12442835 := bstep (se 1 (by rfl) ⟨9332126, by rfl⟩ : syracuseStep 12442835 = 18664253) B18664253
theorem B8295223 : Blo 1941435 8295223 := bstep (se 1 (by rfl) ⟨6221417, by rfl⟩ : syracuseStep 8295223 = 12442835) B12442835
theorem B11060297 : Blo 1941435 11060297 := bstep (se 2 (by rfl) ⟨4147611, by rfl⟩ : syracuseStep 11060297 = 8295223) B8295223
theorem B7373531 : Blo 1941435 7373531 := bstep (se 1 (by rfl) ⟨5530148, by rfl⟩ : syracuseStep 7373531 = 11060297) B11060297
theorem B4915687 : Blo 1941435 4915687 := bstep (se 1 (by rfl) ⟨3686765, by rfl⟩ : syracuseStep 4915687 = 7373531) B7373531
theorem B6554249 : Blo 1941435 6554249 := bstep (se 2 (by rfl) ⟨2457843, by rfl⟩ : syracuseStep 6554249 = 4915687) B4915687
theorem B4369499 : Blo 1941435 4369499 := bstep (se 1 (by rfl) ⟨3277124, by rfl⟩ : syracuseStep 4369499 = 6554249) B6554249
theorem B2912999 : Blo 1941435 2912999 := bstep (se 1 (by rfl) ⟨2184749, by rfl⟩ : syracuseStep 2912999 = 4369499) B4369499
theorem B1941999 : Blo 1941435 1941999 := bstep (se 1 (by rfl) ⟨1456499, by rfl⟩ : syracuseStep 1941999 = 2912999) B2912999
theorem B2913005 : Blo 1941435 2913005 := bbase (se 3 (by rfl) ⟨546188, by rfl⟩ : syracuseStep 2913005 = 1092377) (by norm_num)
theorem B1942003 : Blo 1941435 1942003 := bstep (se 1 (by rfl) ⟨1456502, by rfl⟩ : syracuseStep 1942003 = 2913005) B2913005
theorem B4369517 : Blo 1941435 4369517 := bbase (se 3 (by rfl) ⟨819284, by rfl⟩ : syracuseStep 4369517 = 1638569) (by norm_num)
theorem B2913011 : Blo 1941435 2913011 := bstep (se 1 (by rfl) ⟨2184758, by rfl⟩ : syracuseStep 2913011 = 4369517) B4369517
theorem B1942007 : Blo 1941435 1942007 := bstep (se 1 (by rfl) ⟨1456505, by rfl⟩ : syracuseStep 1942007 = 2913011) B2913011
theorem B3686789 : Blo 1941435 3686789 := bbase (se 4 (by rfl) ⟨345636, by rfl⟩ : syracuseStep 3686789 = 691273) (by norm_num)
theorem B2457859 : Blo 1941435 2457859 := bstep (se 1 (by rfl) ⟨1843394, by rfl⟩ : syracuseStep 2457859 = 3686789) B3686789
theorem B3277145 : Blo 1941435 3277145 := bstep (se 2 (by rfl) ⟨1228929, by rfl⟩ : syracuseStep 3277145 = 2457859) B2457859
theorem B2184763 : Blo 1941435 2184763 := bstep (se 1 (by rfl) ⟨1638572, by rfl⟩ : syracuseStep 2184763 = 3277145) B3277145
theorem B2913017 : Blo 1941435 2913017 := bstep (se 2 (by rfl) ⟨1092381, by rfl⟩ : syracuseStep 2913017 = 2184763) B2184763
theorem B1942011 : Blo 1941435 1942011 := bstep (se 1 (by rfl) ⟨1456508, by rfl⟩ : syracuseStep 1942011 = 2913017) B2913017
theorem B3413125 : Blo 1941435 3413125 := bbase (se 4 (by rfl) ⟨319980, by rfl⟩ : syracuseStep 3413125 = 639961) (by norm_num)
theorem B4550833 : Blo 1941435 4550833 := bstep (se 2 (by rfl) ⟨1706562, by rfl⟩ : syracuseStep 4550833 = 3413125) B3413125
theorem B6067777 : Blo 1941435 6067777 := bstep (se 2 (by rfl) ⟨2275416, by rfl⟩ : syracuseStep 6067777 = 4550833) B4550833
theorem B8090369 : Blo 1941435 8090369 := bstep (se 2 (by rfl) ⟨3033888, by rfl⟩ : syracuseStep 8090369 = 6067777) B6067777
theorem B5393579 : Blo 1941435 5393579 := bstep (se 1 (by rfl) ⟨4045184, by rfl⟩ : syracuseStep 5393579 = 8090369) B8090369
theorem B14382877 : Blo 1941435 14382877 := bstep (se 3 (by rfl) ⟨2696789, by rfl⟩ : syracuseStep 14382877 = 5393579) B5393579
theorem B19177169 : Blo 1941435 19177169 := bstep (se 2 (by rfl) ⟨7191438, by rfl⟩ : syracuseStep 19177169 = 14382877) B14382877
theorem B51139117 : Blo 1941435 51139117 := bstep (se 3 (by rfl) ⟨9588584, by rfl⟩ : syracuseStep 51139117 = 19177169) B19177169
theorem B68185489 : Blo 1941435 68185489 := bstep (se 2 (by rfl) ⟨25569558, by rfl⟩ : syracuseStep 68185489 = 51139117) B51139117
theorem B90913985 : Blo 1941435 90913985 := bstep (se 2 (by rfl) ⟨34092744, by rfl⟩ : syracuseStep 90913985 = 68185489) B68185489
theorem B60609323 : Blo 1941435 60609323 := bstep (se 1 (by rfl) ⟨45456992, by rfl⟩ : syracuseStep 60609323 = 90913985) B90913985
theorem B40406215 : Blo 1941435 40406215 := bstep (se 1 (by rfl) ⟨30304661, by rfl⟩ : syracuseStep 40406215 = 60609323) B60609323
theorem B53874953 : Blo 1941435 53874953 := bstep (se 2 (by rfl) ⟨20203107, by rfl⟩ : syracuseStep 53874953 = 40406215) B40406215
theorem B35916635 : Blo 1941435 35916635 := bstep (se 1 (by rfl) ⟨26937476, by rfl⟩ : syracuseStep 35916635 = 53874953) B53874953
theorem B23944423 : Blo 1941435 23944423 := bstep (se 1 (by rfl) ⟨17958317, by rfl⟩ : syracuseStep 23944423 = 35916635) B35916635
theorem B31925897 : Blo 1941435 31925897 := bstep (se 2 (by rfl) ⟨11972211, by rfl⟩ : syracuseStep 31925897 = 23944423) B23944423
theorem B21283931 : Blo 1941435 21283931 := bstep (se 1 (by rfl) ⟨15962948, by rfl⟩ : syracuseStep 21283931 = 31925897) B31925897
theorem B14189287 : Blo 1941435 14189287 := bstep (se 1 (by rfl) ⟨10641965, by rfl⟩ : syracuseStep 14189287 = 21283931) B21283931
theorem B18919049 : Blo 1941435 18919049 := bstep (se 2 (by rfl) ⟨7094643, by rfl⟩ : syracuseStep 18919049 = 14189287) B14189287
theorem B50450797 : Blo 1941435 50450797 := bstep (se 3 (by rfl) ⟨9459524, by rfl⟩ : syracuseStep 50450797 = 18919049) B18919049
theorem B67267729 : Blo 1941435 67267729 := bstep (se 2 (by rfl) ⟨25225398, by rfl⟩ : syracuseStep 67267729 = 50450797) B50450797
theorem B358761221 : Blo 1941435 358761221 := bstep (se 4 (by rfl) ⟨33633864, by rfl⟩ : syracuseStep 358761221 = 67267729) B67267729
theorem B239174147 : Blo 1941435 239174147 := bstep (se 1 (by rfl) ⟨179380610, by rfl⟩ : syracuseStep 239174147 = 358761221) B358761221
theorem B159449431 : Blo 1941435 159449431 := bstep (se 1 (by rfl) ⟨119587073, by rfl⟩ : syracuseStep 159449431 = 239174147) B239174147
theorem B212599241 : Blo 1941435 212599241 := bstep (se 2 (by rfl) ⟨79724715, by rfl⟩ : syracuseStep 212599241 = 159449431) B159449431
theorem B141732827 : Blo 1941435 141732827 := bstep (se 1 (by rfl) ⟨106299620, by rfl⟩ : syracuseStep 141732827 = 212599241) B212599241
theorem B94488551 : Blo 1941435 94488551 := bstep (se 1 (by rfl) ⟨70866413, by rfl⟩ : syracuseStep 94488551 = 141732827) B141732827
theorem B62992367 : Blo 1941435 62992367 := bstep (se 1 (by rfl) ⟨47244275, by rfl⟩ : syracuseStep 62992367 = 94488551) B94488551
theorem B41994911 : Blo 1941435 41994911 := bstep (se 1 (by rfl) ⟨31496183, by rfl⟩ : syracuseStep 41994911 = 62992367) B62992367
theorem B27996607 : Blo 1941435 27996607 := bstep (se 1 (by rfl) ⟨20997455, by rfl⟩ : syracuseStep 27996607 = 41994911) B41994911
theorem B37328809 : Blo 1941435 37328809 := bstep (se 2 (by rfl) ⟨13998303, by rfl⟩ : syracuseStep 37328809 = 27996607) B27996607
theorem B49771745 : Blo 1941435 49771745 := bstep (se 2 (by rfl) ⟨18664404, by rfl⟩ : syracuseStep 49771745 = 37328809) B37328809
theorem B33181163 : Blo 1941435 33181163 := bstep (se 1 (by rfl) ⟨24885872, by rfl⟩ : syracuseStep 33181163 = 49771745) B49771745
theorem B22120775 : Blo 1941435 22120775 := bstep (se 1 (by rfl) ⟨16590581, by rfl⟩ : syracuseStep 22120775 = 33181163) B33181163
theorem B14747183 : Blo 1941435 14747183 := bstep (se 1 (by rfl) ⟨11060387, by rfl⟩ : syracuseStep 14747183 = 22120775) B22120775
theorem B9831455 : Blo 1941435 9831455 := bstep (se 1 (by rfl) ⟨7373591, by rfl⟩ : syracuseStep 9831455 = 14747183) B14747183
theorem B6554303 : Blo 1941435 6554303 := bstep (se 1 (by rfl) ⟨4915727, by rfl⟩ : syracuseStep 6554303 = 9831455) B9831455
theorem B4369535 : Blo 1941435 4369535 := bstep (se 1 (by rfl) ⟨3277151, by rfl⟩ : syracuseStep 4369535 = 6554303) B6554303
theorem B2913023 : Blo 1941435 2913023 := bstep (se 1 (by rfl) ⟨2184767, by rfl⟩ : syracuseStep 2913023 = 4369535) B4369535
theorem B1942015 : Blo 1941435 1942015 := bstep (se 1 (by rfl) ⟨1456511, by rfl⟩ : syracuseStep 1942015 = 2913023) B2913023
theorem B2913029 : Blo 1941435 2913029 := bbase (se 4 (by rfl) ⟨273096, by rfl⟩ : syracuseStep 2913029 = 546193) (by norm_num)
theorem B1942019 : Blo 1941435 1942019 := bstep (se 1 (by rfl) ⟨1456514, by rfl⟩ : syracuseStep 1942019 = 2913029) B2913029
theorem B3277165 : Blo 1941435 3277165 := bbase (se 3 (by rfl) ⟨614468, by rfl⟩ : syracuseStep 3277165 = 1228937) (by norm_num)
theorem B4369553 : Blo 1941435 4369553 := bstep (se 2 (by rfl) ⟨1638582, by rfl⟩ : syracuseStep 4369553 = 3277165) B3277165
theorem B2913035 : Blo 1941435 2913035 := bstep (se 1 (by rfl) ⟨2184776, by rfl⟩ : syracuseStep 2913035 = 4369553) B4369553
theorem B1942023 : Blo 1941435 1942023 := bstep (se 1 (by rfl) ⟨1456517, by rfl⟩ : syracuseStep 1942023 = 2913035) B2913035
theorem B2184781 : Blo 1941435 2184781 := bbase (se 3 (by rfl) ⟨409646, by rfl⟩ : syracuseStep 2184781 = 819293) (by norm_num)
theorem B2913041 : Blo 1941435 2913041 := bstep (se 2 (by rfl) ⟨1092390, by rfl⟩ : syracuseStep 2913041 = 2184781) B2184781
theorem B1942027 : Blo 1941435 1942027 := bstep (se 1 (by rfl) ⟨1456520, by rfl⟩ : syracuseStep 1942027 = 2913041) B2913041
theorem B6554357 : Blo 1941435 6554357 := bbase (se 5 (by rfl) ⟨307235, by rfl⟩ : syracuseStep 6554357 = 614471) (by norm_num)
theorem B4369571 : Blo 1941435 4369571 := bstep (se 1 (by rfl) ⟨3277178, by rfl⟩ : syracuseStep 4369571 = 6554357) B6554357
theorem B2913047 : Blo 1941435 2913047 := bstep (se 1 (by rfl) ⟨2184785, by rfl⟩ : syracuseStep 2913047 = 4369571) B4369571
theorem B1942031 : Blo 1941435 1942031 := bstep (se 1 (by rfl) ⟨1456523, by rfl⟩ : syracuseStep 1942031 = 2913047) B2913047
theorem B2913053 : Blo 1941435 2913053 := bbase (se 3 (by rfl) ⟨546197, by rfl⟩ : syracuseStep 2913053 = 1092395) (by norm_num)
theorem B1942035 : Blo 1941435 1942035 := bstep (se 1 (by rfl) ⟨1456526, by rfl⟩ : syracuseStep 1942035 = 2913053) B2913053
theorem B4369589 : Blo 1941435 4369589 := bbase (se 5 (by rfl) ⟨204824, by rfl⟩ : syracuseStep 4369589 = 409649) (by norm_num)
theorem B2913059 : Blo 1941435 2913059 := bstep (se 1 (by rfl) ⟨2184794, by rfl⟩ : syracuseStep 2913059 = 4369589) B4369589
theorem B1942039 : Blo 1941435 1942039 := bstep (se 1 (by rfl) ⟨1456529, by rfl⟩ : syracuseStep 1942039 = 2913059) B2913059
theorem B2073853 : Blo 1941435 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B11060549 : Blo 1941435 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B7373699 : Blo 1941435 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B4915799 : Blo 1941435 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B3277199 : Blo 1941435 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B2184799 : Blo 1941435 2184799 := bstep (se 1 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 2184799 = 3277199) B3277199
theorem B2913065 : Blo 1941435 2913065 := bstep (se 2 (by rfl) ⟨1092399, by rfl⟩ : syracuseStep 2913065 = 2184799) B2184799
theorem B1942043 : Blo 1941435 1942043 := bstep (se 1 (by rfl) ⟨1456532, by rfl⟩ : syracuseStep 1942043 = 2913065) B2913065
theorem B2073857 : Blo 1941435 2073857 := bbase (se 2 (by rfl) ⟨777696, by rfl⟩ : syracuseStep 2073857 = 1555393) (by norm_num)
theorem B5530285 : Blo 1941435 5530285 := bstep (se 3 (by rfl) ⟨1036928, by rfl⟩ : syracuseStep 5530285 = 2073857) B2073857
theorem B7373713 : Blo 1941435 7373713 := bstep (se 2 (by rfl) ⟨2765142, by rfl⟩ : syracuseStep 7373713 = 5530285) B5530285
theorem B9831617 : Blo 1941435 9831617 := bstep (se 2 (by rfl) ⟨3686856, by rfl⟩ : syracuseStep 9831617 = 7373713) B7373713
theorem B6554411 : Blo 1941435 6554411 := bstep (se 1 (by rfl) ⟨4915808, by rfl⟩ : syracuseStep 6554411 = 9831617) B9831617
theorem B4369607 : Blo 1941435 4369607 := bstep (se 1 (by rfl) ⟨3277205, by rfl⟩ : syracuseStep 4369607 = 6554411) B6554411
theorem B2913071 : Blo 1941435 2913071 := bstep (se 1 (by rfl) ⟨2184803, by rfl⟩ : syracuseStep 2913071 = 4369607) B4369607
theorem B1942047 : Blo 1941435 1942047 := bstep (se 1 (by rfl) ⟨1456535, by rfl⟩ : syracuseStep 1942047 = 2913071) B2913071
theorem B2913077 : Blo 1941435 2913077 := bbase (se 5 (by rfl) ⟨136550, by rfl⟩ : syracuseStep 2913077 = 273101) (by norm_num)
theorem B1942051 : Blo 1941435 1942051 := bstep (se 1 (by rfl) ⟨1456538, by rfl⟩ : syracuseStep 1942051 = 2913077) B2913077
theorem B4915829 : Blo 1941435 4915829 := bbase (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) (by norm_num)
theorem B3277219 : Blo 1941435 3277219 := bstep (se 1 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 3277219 = 4915829) B4915829
theorem B4369625 : Blo 1941435 4369625 := bstep (se 2 (by rfl) ⟨1638609, by rfl⟩ : syracuseStep 4369625 = 3277219) B3277219
theorem B2913083 : Blo 1941435 2913083 := bstep (se 1 (by rfl) ⟨2184812, by rfl⟩ : syracuseStep 2913083 = 4369625) B4369625
theorem B1942055 : Blo 1941435 1942055 := bstep (se 1 (by rfl) ⟨1456541, by rfl⟩ : syracuseStep 1942055 = 2913083) B2913083
theorem B2184817 : Blo 1941435 2184817 := bbase (se 2 (by rfl) ⟨819306, by rfl⟩ : syracuseStep 2184817 = 1638613) (by norm_num)
theorem B2913089 : Blo 1941435 2913089 := bstep (se 2 (by rfl) ⟨1092408, by rfl⟩ : syracuseStep 2913089 = 2184817) B2184817
theorem B1942059 : Blo 1941435 1942059 := bstep (se 1 (by rfl) ⟨1456544, by rfl⟩ : syracuseStep 1942059 = 2913089) B2913089
theorem B44335189 : Blo 1941435 44335189 := bbase (se 8 (by rfl) ⟨259776, by rfl⟩ : syracuseStep 44335189 = 519553) (by norm_num)
theorem B59113585 : Blo 1941435 59113585 := bstep (se 2 (by rfl) ⟨22167594, by rfl⟩ : syracuseStep 59113585 = 44335189) B44335189
theorem B78818113 : Blo 1941435 78818113 := bstep (se 2 (by rfl) ⟨29556792, by rfl⟩ : syracuseStep 78818113 = 59113585) B59113585
theorem B420363269 : Blo 1941435 420363269 := bstep (se 4 (by rfl) ⟨39409056, by rfl⟩ : syracuseStep 420363269 = 78818113) B78818113
theorem B280242179 : Blo 1941435 280242179 := bstep (se 1 (by rfl) ⟨210181634, by rfl⟩ : syracuseStep 280242179 = 420363269) B420363269
theorem B186828119 : Blo 1941435 186828119 := bstep (se 1 (by rfl) ⟨140121089, by rfl⟩ : syracuseStep 186828119 = 280242179) B280242179
theorem B124552079 : Blo 1941435 124552079 := bstep (se 1 (by rfl) ⟨93414059, by rfl⟩ : syracuseStep 124552079 = 186828119) B186828119
theorem B83034719 : Blo 1941435 83034719 := bstep (se 1 (by rfl) ⟨62276039, by rfl⟩ : syracuseStep 83034719 = 124552079) B124552079
theorem B55356479 : Blo 1941435 55356479 := bstep (se 1 (by rfl) ⟨41517359, by rfl⟩ : syracuseStep 55356479 = 83034719) B83034719
theorem B36904319 : Blo 1941435 36904319 := bstep (se 1 (by rfl) ⟨27678239, by rfl⟩ : syracuseStep 36904319 = 55356479) B55356479
theorem B24602879 : Blo 1941435 24602879 := bstep (se 1 (by rfl) ⟨18452159, by rfl⟩ : syracuseStep 24602879 = 36904319) B36904319
theorem B65607677 : Blo 1941435 65607677 := bstep (se 3 (by rfl) ⟨12301439, by rfl⟩ : syracuseStep 65607677 = 24602879) B24602879
theorem B43738451 : Blo 1941435 43738451 := bstep (se 1 (by rfl) ⟨32803838, by rfl⟩ : syracuseStep 43738451 = 65607677) B65607677
theorem B29158967 : Blo 1941435 29158967 := bstep (se 1 (by rfl) ⟨21869225, by rfl⟩ : syracuseStep 29158967 = 43738451) B43738451
theorem B77757245 : Blo 1941435 77757245 := bstep (se 3 (by rfl) ⟨14579483, by rfl⟩ : syracuseStep 77757245 = 29158967) B29158967
theorem B51838163 : Blo 1941435 51838163 := bstep (se 1 (by rfl) ⟨38878622, by rfl⟩ : syracuseStep 51838163 = 77757245) B77757245
theorem B34558775 : Blo 1941435 34558775 := bstep (se 1 (by rfl) ⟨25919081, by rfl⟩ : syracuseStep 34558775 = 51838163) B51838163
theorem B23039183 : Blo 1941435 23039183 := bstep (se 1 (by rfl) ⟨17279387, by rfl⟩ : syracuseStep 23039183 = 34558775) B34558775
theorem B15359455 : Blo 1941435 15359455 := bstep (se 1 (by rfl) ⟨11519591, by rfl⟩ : syracuseStep 15359455 = 23039183) B23039183
theorem B20479273 : Blo 1941435 20479273 := bstep (se 2 (by rfl) ⟨7679727, by rfl⟩ : syracuseStep 20479273 = 15359455) B15359455
theorem B109222789 : Blo 1941435 109222789 := bstep (se 4 (by rfl) ⟨10239636, by rfl⟩ : syracuseStep 109222789 = 20479273) B20479273
theorem B145630385 : Blo 1941435 145630385 := bstep (se 2 (by rfl) ⟨54611394, by rfl⟩ : syracuseStep 145630385 = 109222789) B109222789
theorem B97086923 : Blo 1941435 97086923 := bstep (se 1 (by rfl) ⟨72815192, by rfl⟩ : syracuseStep 97086923 = 145630385) B145630385
theorem B64724615 : Blo 1941435 64724615 := bstep (se 1 (by rfl) ⟨48543461, by rfl⟩ : syracuseStep 64724615 = 97086923) B97086923
theorem B43149743 : Blo 1941435 43149743 := bstep (se 1 (by rfl) ⟨32362307, by rfl⟩ : syracuseStep 43149743 = 64724615) B64724615
theorem B28766495 : Blo 1941435 28766495 := bstep (se 1 (by rfl) ⟨21574871, by rfl⟩ : syracuseStep 28766495 = 43149743) B43149743
theorem B19177663 : Blo 1941435 19177663 := bstep (se 1 (by rfl) ⟨14383247, by rfl⟩ : syracuseStep 19177663 = 28766495) B28766495
theorem B25570217 : Blo 1941435 25570217 := bstep (se 2 (by rfl) ⟨9588831, by rfl⟩ : syracuseStep 25570217 = 19177663) B19177663
theorem B17046811 : Blo 1941435 17046811 := bstep (se 1 (by rfl) ⟨12785108, by rfl⟩ : syracuseStep 17046811 = 25570217) B25570217
theorem B22729081 : Blo 1941435 22729081 := bstep (se 2 (by rfl) ⟨8523405, by rfl⟩ : syracuseStep 22729081 = 17046811) B17046811
theorem B30305441 : Blo 1941435 30305441 := bstep (se 2 (by rfl) ⟨11364540, by rfl⟩ : syracuseStep 30305441 = 22729081) B22729081
theorem B20203627 : Blo 1941435 20203627 := bstep (se 1 (by rfl) ⟨15152720, by rfl⟩ : syracuseStep 20203627 = 30305441) B30305441
theorem B26938169 : Blo 1941435 26938169 := bstep (se 2 (by rfl) ⟨10101813, by rfl⟩ : syracuseStep 26938169 = 20203627) B20203627
theorem B17958779 : Blo 1941435 17958779 := bstep (se 1 (by rfl) ⟨13469084, by rfl⟩ : syracuseStep 17958779 = 26938169) B26938169
theorem B11972519 : Blo 1941435 11972519 := bstep (se 1 (by rfl) ⟨8979389, by rfl⟩ : syracuseStep 11972519 = 17958779) B17958779
theorem B7981679 : Blo 1941435 7981679 := bstep (se 1 (by rfl) ⟨5986259, by rfl⟩ : syracuseStep 7981679 = 11972519) B11972519
theorem B21284477 : Blo 1941435 21284477 := bstep (se 3 (by rfl) ⟨3990839, by rfl⟩ : syracuseStep 21284477 = 7981679) B7981679
theorem B14189651 : Blo 1941435 14189651 := bstep (se 1 (by rfl) ⟨10642238, by rfl⟩ : syracuseStep 14189651 = 21284477) B21284477
theorem B9459767 : Blo 1941435 9459767 := bstep (se 1 (by rfl) ⟨7094825, by rfl⟩ : syracuseStep 9459767 = 14189651) B14189651
theorem B6306511 : Blo 1941435 6306511 := bstep (se 1 (by rfl) ⟨4729883, by rfl⟩ : syracuseStep 6306511 = 9459767) B9459767
theorem B8408681 : Blo 1941435 8408681 := bstep (se 2 (by rfl) ⟨3153255, by rfl⟩ : syracuseStep 8408681 = 6306511) B6306511
theorem B5605787 : Blo 1941435 5605787 := bstep (se 1 (by rfl) ⟨4204340, by rfl⟩ : syracuseStep 5605787 = 8408681) B8408681
theorem B3737191 : Blo 1941435 3737191 := bstep (se 1 (by rfl) ⟨2802893, by rfl⟩ : syracuseStep 3737191 = 5605787) B5605787
theorem B4982921 : Blo 1941435 4982921 := bstep (se 2 (by rfl) ⟨1868595, by rfl⟩ : syracuseStep 4982921 = 3737191) B3737191
theorem B3321947 : Blo 1941435 3321947 := bstep (se 1 (by rfl) ⟨2491460, by rfl⟩ : syracuseStep 3321947 = 4982921) B4982921
theorem B2214631 : Blo 1941435 2214631 := bstep (se 1 (by rfl) ⟨1660973, by rfl⟩ : syracuseStep 2214631 = 3321947) B3321947
theorem B11811365 : Blo 1941435 11811365 := bstep (se 4 (by rfl) ⟨1107315, by rfl⟩ : syracuseStep 11811365 = 2214631) B2214631
theorem B7874243 : Blo 1941435 7874243 := bstep (se 1 (by rfl) ⟨5905682, by rfl⟩ : syracuseStep 7874243 = 11811365) B11811365
theorem B5249495 : Blo 1941435 5249495 := bstep (se 1 (by rfl) ⟨3937121, by rfl⟩ : syracuseStep 5249495 = 7874243) B7874243
theorem B13998653 : Blo 1941435 13998653 := bstep (se 3 (by rfl) ⟨2624747, by rfl⟩ : syracuseStep 13998653 = 5249495) B5249495
theorem B9332435 : Blo 1941435 9332435 := bstep (se 1 (by rfl) ⟨6999326, by rfl⟩ : syracuseStep 9332435 = 13998653) B13998653
theorem B6221623 : Blo 1941435 6221623 := bstep (se 1 (by rfl) ⟨4666217, by rfl⟩ : syracuseStep 6221623 = 9332435) B9332435
theorem B8295497 : Blo 1941435 8295497 := bstep (se 2 (by rfl) ⟨3110811, by rfl⟩ : syracuseStep 8295497 = 6221623) B6221623
theorem B5530331 : Blo 1941435 5530331 := bstep (se 1 (by rfl) ⟨4147748, by rfl⟩ : syracuseStep 5530331 = 8295497) B8295497
theorem B3686887 : Blo 1941435 3686887 := bstep (se 1 (by rfl) ⟨2765165, by rfl⟩ : syracuseStep 3686887 = 5530331) B5530331
theorem B4915849 : Blo 1941435 4915849 := bstep (se 2 (by rfl) ⟨1843443, by rfl⟩ : syracuseStep 4915849 = 3686887) B3686887
theorem B6554465 : Blo 1941435 6554465 := bstep (se 2 (by rfl) ⟨2457924, by rfl⟩ : syracuseStep 6554465 = 4915849) B4915849
theorem B4369643 : Blo 1941435 4369643 := bstep (se 1 (by rfl) ⟨3277232, by rfl⟩ : syracuseStep 4369643 = 6554465) B6554465
theorem B2913095 : Blo 1941435 2913095 := bstep (se 1 (by rfl) ⟨2184821, by rfl⟩ : syracuseStep 2913095 = 4369643) B4369643
theorem B1942063 : Blo 1941435 1942063 := bstep (se 1 (by rfl) ⟨1456547, by rfl⟩ : syracuseStep 1942063 = 2913095) B2913095
theorem B2913101 : Blo 1941435 2913101 := bbase (se 3 (by rfl) ⟨546206, by rfl⟩ : syracuseStep 2913101 = 1092413) (by norm_num)
theorem B1942067 : Blo 1941435 1942067 := bstep (se 1 (by rfl) ⟨1456550, by rfl⟩ : syracuseStep 1942067 = 2913101) B2913101
theorem B4369661 : Blo 1941435 4369661 := bbase (se 3 (by rfl) ⟨819311, by rfl⟩ : syracuseStep 4369661 = 1638623) (by norm_num)
theorem B2913107 : Blo 1941435 2913107 := bstep (se 1 (by rfl) ⟨2184830, by rfl⟩ : syracuseStep 2913107 = 4369661) B4369661
theorem B1942071 : Blo 1941435 1942071 := bstep (se 1 (by rfl) ⟨1456553, by rfl⟩ : syracuseStep 1942071 = 2913107) B2913107
theorem B3277253 : Blo 1941435 3277253 := bbase (se 4 (by rfl) ⟨307242, by rfl⟩ : syracuseStep 3277253 = 614485) (by norm_num)
theorem B2184835 : Blo 1941435 2184835 := bstep (se 1 (by rfl) ⟨1638626, by rfl⟩ : syracuseStep 2184835 = 3277253) B3277253
theorem B2913113 : Blo 1941435 2913113 := bstep (se 2 (by rfl) ⟨1092417, by rfl⟩ : syracuseStep 2913113 = 2184835) B2184835
theorem B1942075 : Blo 1941435 1942075 := bstep (se 1 (by rfl) ⟨1456556, by rfl⟩ : syracuseStep 1942075 = 2913113) B2913113
theorem B14747669 : Blo 1941435 14747669 := bbase (se 6 (by rfl) ⟨345648, by rfl⟩ : syracuseStep 14747669 = 691297) (by norm_num)
theorem B9831779 : Blo 1941435 9831779 := bstep (se 1 (by rfl) ⟨7373834, by rfl⟩ : syracuseStep 9831779 = 14747669) B14747669
theorem B6554519 : Blo 1941435 6554519 := bstep (se 1 (by rfl) ⟨4915889, by rfl⟩ : syracuseStep 6554519 = 9831779) B9831779
theorem B4369679 : Blo 1941435 4369679 := bstep (se 1 (by rfl) ⟨3277259, by rfl⟩ : syracuseStep 4369679 = 6554519) B6554519
theorem B2913119 : Blo 1941435 2913119 := bstep (se 1 (by rfl) ⟨2184839, by rfl⟩ : syracuseStep 2913119 = 4369679) B4369679
theorem B1942079 : Blo 1941435 1942079 := bstep (se 1 (by rfl) ⟨1456559, by rfl⟩ : syracuseStep 1942079 = 2913119) B2913119
theorem B2913125 : Blo 1941435 2913125 := bbase (se 4 (by rfl) ⟨273105, by rfl⟩ : syracuseStep 2913125 = 546211) (by norm_num)
theorem B1942083 : Blo 1941435 1942083 := bstep (se 1 (by rfl) ⟨1456562, by rfl⟩ : syracuseStep 1942083 = 2913125) B2913125
theorem B3686933 : Blo 1941435 3686933 := bbase (se 6 (by rfl) ⟨86412, by rfl⟩ : syracuseStep 3686933 = 172825) (by norm_num)
theorem B2457955 : Blo 1941435 2457955 := bstep (se 1 (by rfl) ⟨1843466, by rfl⟩ : syracuseStep 2457955 = 3686933) B3686933
theorem B3277273 : Blo 1941435 3277273 := bstep (se 2 (by rfl) ⟨1228977, by rfl⟩ : syracuseStep 3277273 = 2457955) B2457955
theorem B4369697 : Blo 1941435 4369697 := bstep (se 2 (by rfl) ⟨1638636, by rfl⟩ : syracuseStep 4369697 = 3277273) B3277273
theorem B2913131 : Blo 1941435 2913131 := bstep (se 1 (by rfl) ⟨2184848, by rfl⟩ : syracuseStep 2913131 = 4369697) B4369697
theorem B1942087 : Blo 1941435 1942087 := bstep (se 1 (by rfl) ⟨1456565, by rfl⟩ : syracuseStep 1942087 = 2913131) B2913131
theorem B2184853 : Blo 1941435 2184853 := bbase (se 6 (by rfl) ⟨51207, by rfl⟩ : syracuseStep 2184853 = 102415) (by norm_num)
theorem B2913137 : Blo 1941435 2913137 := bstep (se 2 (by rfl) ⟨1092426, by rfl⟩ : syracuseStep 2913137 = 2184853) B2184853
theorem B1942091 : Blo 1941435 1942091 := bstep (se 1 (by rfl) ⟨1456568, by rfl⟩ : syracuseStep 1942091 = 2913137) B2913137
theorem B2457965 : Blo 1941435 2457965 := bbase (se 3 (by rfl) ⟨460868, by rfl⟩ : syracuseStep 2457965 = 921737) (by norm_num)
theorem B6554573 : Blo 1941435 6554573 := bstep (se 3 (by rfl) ⟨1228982, by rfl⟩ : syracuseStep 6554573 = 2457965) B2457965
theorem B4369715 : Blo 1941435 4369715 := bstep (se 1 (by rfl) ⟨3277286, by rfl⟩ : syracuseStep 4369715 = 6554573) B6554573
theorem B2913143 : Blo 1941435 2913143 := bstep (se 1 (by rfl) ⟨2184857, by rfl⟩ : syracuseStep 2913143 = 4369715) B4369715
theorem B1942095 : Blo 1941435 1942095 := bstep (se 1 (by rfl) ⟨1456571, by rfl⟩ : syracuseStep 1942095 = 2913143) B2913143
theorem B2913149 : Blo 1941435 2913149 := bbase (se 3 (by rfl) ⟨546215, by rfl⟩ : syracuseStep 2913149 = 1092431) (by norm_num)
theorem B1942099 : Blo 1941435 1942099 := bstep (se 1 (by rfl) ⟨1456574, by rfl⟩ : syracuseStep 1942099 = 2913149) B2913149
theorem B4369733 : Blo 1941435 4369733 := bbase (se 4 (by rfl) ⟨409662, by rfl⟩ : syracuseStep 4369733 = 819325) (by norm_num)
theorem B2913155 : Blo 1941435 2913155 := bstep (se 1 (by rfl) ⟨2184866, by rfl⟩ : syracuseStep 2913155 = 4369733) B4369733
theorem B1942103 : Blo 1941435 1942103 := bstep (se 1 (by rfl) ⟨1456577, by rfl⟩ : syracuseStep 1942103 = 2913155) B2913155
theorem B6221765 : Blo 1941435 6221765 := bbase (se 4 (by rfl) ⟨583290, by rfl⟩ : syracuseStep 6221765 = 1166581) (by norm_num)
theorem B4147843 : Blo 1941435 4147843 := bstep (se 1 (by rfl) ⟨3110882, by rfl⟩ : syracuseStep 4147843 = 6221765) B6221765
theorem B5530457 : Blo 1941435 5530457 := bstep (se 2 (by rfl) ⟨2073921, by rfl⟩ : syracuseStep 5530457 = 4147843) B4147843
theorem B3686971 : Blo 1941435 3686971 := bstep (se 1 (by rfl) ⟨2765228, by rfl⟩ : syracuseStep 3686971 = 5530457) B5530457
theorem B4915961 : Blo 1941435 4915961 := bstep (se 2 (by rfl) ⟨1843485, by rfl⟩ : syracuseStep 4915961 = 3686971) B3686971
theorem B3277307 : Blo 1941435 3277307 := bstep (se 1 (by rfl) ⟨2457980, by rfl⟩ : syracuseStep 3277307 = 4915961) B4915961
theorem B2184871 : Blo 1941435 2184871 := bstep (se 1 (by rfl) ⟨1638653, by rfl⟩ : syracuseStep 2184871 = 3277307) B3277307
theorem B2913161 : Blo 1941435 2913161 := bstep (se 2 (by rfl) ⟨1092435, by rfl⟩ : syracuseStep 2913161 = 2184871) B2184871
theorem B1942107 : Blo 1941435 1942107 := bstep (se 1 (by rfl) ⟨1456580, by rfl⟩ : syracuseStep 1942107 = 2913161) B2913161
theorem B9831941 : Blo 1941435 9831941 := bbase (se 4 (by rfl) ⟨921744, by rfl⟩ : syracuseStep 9831941 = 1843489) (by norm_num)
theorem B6554627 : Blo 1941435 6554627 := bstep (se 1 (by rfl) ⟨4915970, by rfl⟩ : syracuseStep 6554627 = 9831941) B9831941
theorem B4369751 : Blo 1941435 4369751 := bstep (se 1 (by rfl) ⟨3277313, by rfl⟩ : syracuseStep 4369751 = 6554627) B6554627
theorem B2913167 : Blo 1941435 2913167 := bstep (se 1 (by rfl) ⟨2184875, by rfl⟩ : syracuseStep 2913167 = 4369751) B4369751
theorem B1942111 : Blo 1941435 1942111 := bstep (se 1 (by rfl) ⟨1456583, by rfl⟩ : syracuseStep 1942111 = 2913167) B2913167
theorem B2913173 : Blo 1941435 2913173 := bbase (se 6 (by rfl) ⟨68277, by rfl⟩ : syracuseStep 2913173 = 136555) (by norm_num)
theorem B1942115 : Blo 1941435 1942115 := bstep (se 1 (by rfl) ⟨1456586, by rfl⟩ : syracuseStep 1942115 = 2913173) B2913173
theorem B11060981 : Blo 1941435 11060981 := bbase (se 5 (by rfl) ⟨518483, by rfl⟩ : syracuseStep 11060981 = 1036967) (by norm_num)
theorem B7373987 : Blo 1941435 7373987 := bstep (se 1 (by rfl) ⟨5530490, by rfl⟩ : syracuseStep 7373987 = 11060981) B11060981
theorem B4915991 : Blo 1941435 4915991 := bstep (se 1 (by rfl) ⟨3686993, by rfl⟩ : syracuseStep 4915991 = 7373987) B7373987
theorem B3277327 : Blo 1941435 3277327 := bstep (se 1 (by rfl) ⟨2457995, by rfl⟩ : syracuseStep 3277327 = 4915991) B4915991
theorem B4369769 : Blo 1941435 4369769 := bstep (se 2 (by rfl) ⟨1638663, by rfl⟩ : syracuseStep 4369769 = 3277327) B3277327
theorem B2913179 : Blo 1941435 2913179 := bstep (se 1 (by rfl) ⟨2184884, by rfl⟩ : syracuseStep 2913179 = 4369769) B4369769
theorem B1942119 : Blo 1941435 1942119 := bstep (se 1 (by rfl) ⟨1456589, by rfl⟩ : syracuseStep 1942119 = 2913179) B2913179
theorem B2184889 : Blo 1941435 2184889 := bbase (se 2 (by rfl) ⟨819333, by rfl⟩ : syracuseStep 2184889 = 1638667) (by norm_num)
theorem B2913185 : Blo 1941435 2913185 := bstep (se 2 (by rfl) ⟨1092444, by rfl⟩ : syracuseStep 2913185 = 2184889) B2184889
theorem B1942123 : Blo 1941435 1942123 := bstep (se 1 (by rfl) ⟨1456592, by rfl⟩ : syracuseStep 1942123 = 2913185) B2913185
theorem B4147885 : Blo 1941435 4147885 := bbase (se 3 (by rfl) ⟨777728, by rfl⟩ : syracuseStep 4147885 = 1555457) (by norm_num)
theorem B5530513 : Blo 1941435 5530513 := bstep (se 2 (by rfl) ⟨2073942, by rfl⟩ : syracuseStep 5530513 = 4147885) B4147885
theorem B7374017 : Blo 1941435 7374017 := bstep (se 2 (by rfl) ⟨2765256, by rfl⟩ : syracuseStep 7374017 = 5530513) B5530513
theorem B4916011 : Blo 1941435 4916011 := bstep (se 1 (by rfl) ⟨3687008, by rfl⟩ : syracuseStep 4916011 = 7374017) B7374017
theorem B6554681 : Blo 1941435 6554681 := bstep (se 2 (by rfl) ⟨2458005, by rfl⟩ : syracuseStep 6554681 = 4916011) B4916011
theorem B4369787 : Blo 1941435 4369787 := bstep (se 1 (by rfl) ⟨3277340, by rfl⟩ : syracuseStep 4369787 = 6554681) B6554681
theorem B2913191 : Blo 1941435 2913191 := bstep (se 1 (by rfl) ⟨2184893, by rfl⟩ : syracuseStep 2913191 = 4369787) B4369787
theorem B1942127 : Blo 1941435 1942127 := bstep (se 1 (by rfl) ⟨1456595, by rfl⟩ : syracuseStep 1942127 = 2913191) B2913191
theorem B2913197 : Blo 1941435 2913197 := bbase (se 3 (by rfl) ⟨546224, by rfl⟩ : syracuseStep 2913197 = 1092449) (by norm_num)
theorem B1942131 : Blo 1941435 1942131 := bstep (se 1 (by rfl) ⟨1456598, by rfl⟩ : syracuseStep 1942131 = 2913197) B2913197
theorem B4369805 : Blo 1941435 4369805 := bbase (se 3 (by rfl) ⟨819338, by rfl⟩ : syracuseStep 4369805 = 1638677) (by norm_num)
theorem B2913203 : Blo 1941435 2913203 := bstep (se 1 (by rfl) ⟨2184902, by rfl⟩ : syracuseStep 2913203 = 4369805) B4369805
theorem B1942135 : Blo 1941435 1942135 := bstep (se 1 (by rfl) ⟨1456601, by rfl⟩ : syracuseStep 1942135 = 2913203) B2913203
theorem B2458021 : Blo 1941435 2458021 := bbase (se 4 (by rfl) ⟨230439, by rfl⟩ : syracuseStep 2458021 = 460879) (by norm_num)
theorem B3277361 : Blo 1941435 3277361 := bstep (se 2 (by rfl) ⟨1229010, by rfl⟩ : syracuseStep 3277361 = 2458021) B2458021
theorem B2184907 : Blo 1941435 2184907 := bstep (se 1 (by rfl) ⟨1638680, by rfl⟩ : syracuseStep 2184907 = 3277361) B3277361
theorem B2913209 : Blo 1941435 2913209 := bstep (se 2 (by rfl) ⟨1092453, by rfl⟩ : syracuseStep 2913209 = 2184907) B2184907
theorem B1942139 : Blo 1941435 1942139 := bstep (se 1 (by rfl) ⟨1456604, by rfl⟩ : syracuseStep 1942139 = 2913209) B2913209
theorem B5905925 : Blo 1941435 5905925 := bbase (se 4 (by rfl) ⟨553680, by rfl⟩ : syracuseStep 5905925 = 1107361) (by norm_num)
theorem B3937283 : Blo 1941435 3937283 := bstep (se 1 (by rfl) ⟨2952962, by rfl⟩ : syracuseStep 3937283 = 5905925) B5905925
theorem B2624855 : Blo 1941435 2624855 := bstep (se 1 (by rfl) ⟨1968641, by rfl⟩ : syracuseStep 2624855 = 3937283) B3937283
theorem B27998453 : Blo 1941435 27998453 := bstep (se 5 (by rfl) ⟨1312427, by rfl⟩ : syracuseStep 27998453 = 2624855) B2624855
theorem B18665635 : Blo 1941435 18665635 := bstep (se 1 (by rfl) ⟨13999226, by rfl⟩ : syracuseStep 18665635 = 27998453) B27998453
theorem B24887513 : Blo 1941435 24887513 := bstep (se 2 (by rfl) ⟨9332817, by rfl⟩ : syracuseStep 24887513 = 18665635) B18665635
theorem B16591675 : Blo 1941435 16591675 := bstep (se 1 (by rfl) ⟨12443756, by rfl⟩ : syracuseStep 16591675 = 24887513) B24887513
theorem B22122233 : Blo 1941435 22122233 := bstep (se 2 (by rfl) ⟨8295837, by rfl⟩ : syracuseStep 22122233 = 16591675) B16591675
theorem B14748155 : Blo 1941435 14748155 := bstep (se 1 (by rfl) ⟨11061116, by rfl⟩ : syracuseStep 14748155 = 22122233) B22122233
theorem B9832103 : Blo 1941435 9832103 := bstep (se 1 (by rfl) ⟨7374077, by rfl⟩ : syracuseStep 9832103 = 14748155) B14748155
theorem B6554735 : Blo 1941435 6554735 := bstep (se 1 (by rfl) ⟨4916051, by rfl⟩ : syracuseStep 6554735 = 9832103) B9832103
theorem B4369823 : Blo 1941435 4369823 := bstep (se 1 (by rfl) ⟨3277367, by rfl⟩ : syracuseStep 4369823 = 6554735) B6554735
theorem B2913215 : Blo 1941435 2913215 := bstep (se 1 (by rfl) ⟨2184911, by rfl⟩ : syracuseStep 2913215 = 4369823) B4369823
theorem B1942143 : Blo 1941435 1942143 := bstep (se 1 (by rfl) ⟨1456607, by rfl⟩ : syracuseStep 1942143 = 2913215) B2913215
theorem B2913221 : Blo 1941435 2913221 := bbase (se 4 (by rfl) ⟨273114, by rfl⟩ : syracuseStep 2913221 = 546229) (by norm_num)
theorem B1942147 : Blo 1941435 1942147 := bstep (se 1 (by rfl) ⟨1456610, by rfl⟩ : syracuseStep 1942147 = 2913221) B2913221
theorem B3277381 : Blo 1941435 3277381 := bbase (se 4 (by rfl) ⟨307254, by rfl⟩ : syracuseStep 3277381 = 614509) (by norm_num)
theorem B4369841 : Blo 1941435 4369841 := bstep (se 2 (by rfl) ⟨1638690, by rfl⟩ : syracuseStep 4369841 = 3277381) B3277381
theorem B2913227 : Blo 1941435 2913227 := bstep (se 1 (by rfl) ⟨2184920, by rfl⟩ : syracuseStep 2913227 = 4369841) B4369841
theorem B1942151 : Blo 1941435 1942151 := bstep (se 1 (by rfl) ⟨1456613, by rfl⟩ : syracuseStep 1942151 = 2913227) B2913227
theorem B2184925 : Blo 1941435 2184925 := bbase (se 3 (by rfl) ⟨409673, by rfl⟩ : syracuseStep 2184925 = 819347) (by norm_num)
theorem B2913233 : Blo 1941435 2913233 := bstep (se 2 (by rfl) ⟨1092462, by rfl⟩ : syracuseStep 2913233 = 2184925) B2184925
theorem B1942155 : Blo 1941435 1942155 := bstep (se 1 (by rfl) ⟨1456616, by rfl⟩ : syracuseStep 1942155 = 2913233) B2913233
theorem B6554789 : Blo 1941435 6554789 := bbase (se 4 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 6554789 = 1229023) (by norm_num)
theorem B4369859 : Blo 1941435 4369859 := bstep (se 1 (by rfl) ⟨3277394, by rfl⟩ : syracuseStep 4369859 = 6554789) B6554789
theorem B2913239 : Blo 1941435 2913239 := bstep (se 1 (by rfl) ⟨2184929, by rfl⟩ : syracuseStep 2913239 = 4369859) B4369859
theorem B1942159 : Blo 1941435 1942159 := bstep (se 1 (by rfl) ⟨1456619, by rfl⟩ : syracuseStep 1942159 = 2913239) B2913239
theorem B2913245 : Blo 1941435 2913245 := bbase (se 3 (by rfl) ⟨546233, by rfl⟩ : syracuseStep 2913245 = 1092467) (by norm_num)
theorem B1942163 : Blo 1941435 1942163 := bstep (se 1 (by rfl) ⟨1456622, by rfl⟩ : syracuseStep 1942163 = 2913245) B2913245
theorem B4369877 : Blo 1941435 4369877 := bbase (se 7 (by rfl) ⟨51209, by rfl⟩ : syracuseStep 4369877 = 102419) (by norm_num)
theorem B2913251 : Blo 1941435 2913251 := bstep (se 1 (by rfl) ⟨2184938, by rfl⟩ : syracuseStep 2913251 = 4369877) B4369877
theorem B1942167 : Blo 1941435 1942167 := bstep (se 1 (by rfl) ⟨1456625, by rfl⟩ : syracuseStep 1942167 = 2913251) B2913251
theorem B18665909 : Blo 1941435 18665909 := bbase (se 5 (by rfl) ⟨874964, by rfl⟩ : syracuseStep 18665909 = 1749929) (by norm_num)
theorem B12443939 : Blo 1941435 12443939 := bstep (se 1 (by rfl) ⟨9332954, by rfl⟩ : syracuseStep 12443939 = 18665909) B18665909
theorem B8295959 : Blo 1941435 8295959 := bstep (se 1 (by rfl) ⟨6221969, by rfl⟩ : syracuseStep 8295959 = 12443939) B12443939
theorem B5530639 : Blo 1941435 5530639 := bstep (se 1 (by rfl) ⟨4147979, by rfl⟩ : syracuseStep 5530639 = 8295959) B8295959
theorem B7374185 : Blo 1941435 7374185 := bstep (se 2 (by rfl) ⟨2765319, by rfl⟩ : syracuseStep 7374185 = 5530639) B5530639
theorem B4916123 : Blo 1941435 4916123 := bstep (se 1 (by rfl) ⟨3687092, by rfl⟩ : syracuseStep 4916123 = 7374185) B7374185
theorem B3277415 : Blo 1941435 3277415 := bstep (se 1 (by rfl) ⟨2458061, by rfl⟩ : syracuseStep 3277415 = 4916123) B4916123
theorem B2184943 : Blo 1941435 2184943 := bstep (se 1 (by rfl) ⟨1638707, by rfl⟩ : syracuseStep 2184943 = 3277415) B3277415
theorem B2913257 : Blo 1941435 2913257 := bstep (se 2 (by rfl) ⟨1092471, by rfl⟩ : syracuseStep 2913257 = 2184943) B2184943
theorem B1942171 : Blo 1941435 1942171 := bstep (se 1 (by rfl) ⟨1456628, by rfl⟩ : syracuseStep 1942171 = 2913257) B2913257
theorem B3937349 : Blo 1941435 3937349 := bbase (se 4 (by rfl) ⟨369126, by rfl⟩ : syracuseStep 3937349 = 738253) (by norm_num)
theorem B2624899 : Blo 1941435 2624899 := bstep (se 1 (by rfl) ⟨1968674, by rfl⟩ : syracuseStep 2624899 = 3937349) B3937349
theorem B3499865 : Blo 1941435 3499865 := bstep (se 2 (by rfl) ⟨1312449, by rfl⟩ : syracuseStep 3499865 = 2624899) B2624899
theorem B2333243 : Blo 1941435 2333243 := bstep (se 1 (by rfl) ⟨1749932, by rfl⟩ : syracuseStep 2333243 = 3499865) B3499865
theorem B6221981 : Blo 1941435 6221981 := bstep (se 3 (by rfl) ⟨1166621, by rfl⟩ : syracuseStep 6221981 = 2333243) B2333243
theorem B16591949 : Blo 1941435 16591949 := bstep (se 3 (by rfl) ⟨3110990, by rfl⟩ : syracuseStep 16591949 = 6221981) B6221981
theorem B11061299 : Blo 1941435 11061299 := bstep (se 1 (by rfl) ⟨8295974, by rfl⟩ : syracuseStep 11061299 = 16591949) B16591949
theorem B7374199 : Blo 1941435 7374199 := bstep (se 1 (by rfl) ⟨5530649, by rfl⟩ : syracuseStep 7374199 = 11061299) B11061299
theorem B9832265 : Blo 1941435 9832265 := bstep (se 2 (by rfl) ⟨3687099, by rfl⟩ : syracuseStep 9832265 = 7374199) B7374199
theorem B6554843 : Blo 1941435 6554843 := bstep (se 1 (by rfl) ⟨4916132, by rfl⟩ : syracuseStep 6554843 = 9832265) B9832265
theorem B4369895 : Blo 1941435 4369895 := bstep (se 1 (by rfl) ⟨3277421, by rfl⟩ : syracuseStep 4369895 = 6554843) B6554843
theorem B2913263 : Blo 1941435 2913263 := bstep (se 1 (by rfl) ⟨2184947, by rfl⟩ : syracuseStep 2913263 = 4369895) B4369895
theorem B1942175 : Blo 1941435 1942175 := bstep (se 1 (by rfl) ⟨1456631, by rfl⟩ : syracuseStep 1942175 = 2913263) B2913263
theorem B2913269 : Blo 1941435 2913269 := bbase (se 5 (by rfl) ⟨136559, by rfl⟩ : syracuseStep 2913269 = 273119) (by norm_num)
theorem B1942179 : Blo 1941435 1942179 := bstep (se 1 (by rfl) ⟨1456634, by rfl⟩ : syracuseStep 1942179 = 2913269) B2913269
theorem B4148005 : Blo 1941435 4148005 := bbase (se 4 (by rfl) ⟨388875, by rfl⟩ : syracuseStep 4148005 = 777751) (by norm_num)
theorem B5530673 : Blo 1941435 5530673 := bstep (se 2 (by rfl) ⟨2074002, by rfl⟩ : syracuseStep 5530673 = 4148005) B4148005
theorem B3687115 : Blo 1941435 3687115 := bstep (se 1 (by rfl) ⟨2765336, by rfl⟩ : syracuseStep 3687115 = 5530673) B5530673
theorem B4916153 : Blo 1941435 4916153 := bstep (se 2 (by rfl) ⟨1843557, by rfl⟩ : syracuseStep 4916153 = 3687115) B3687115
theorem B3277435 : Blo 1941435 3277435 := bstep (se 1 (by rfl) ⟨2458076, by rfl⟩ : syracuseStep 3277435 = 4916153) B4916153
theorem B4369913 : Blo 1941435 4369913 := bstep (se 2 (by rfl) ⟨1638717, by rfl⟩ : syracuseStep 4369913 = 3277435) B3277435
theorem B2913275 : Blo 1941435 2913275 := bstep (se 1 (by rfl) ⟨2184956, by rfl⟩ : syracuseStep 2913275 = 4369913) B4369913
theorem B1942183 : Blo 1941435 1942183 := bstep (se 1 (by rfl) ⟨1456637, by rfl⟩ : syracuseStep 1942183 = 2913275) B2913275
theorem B2184961 : Blo 1941435 2184961 := bbase (se 2 (by rfl) ⟨819360, by rfl⟩ : syracuseStep 2184961 = 1638721) (by norm_num)
theorem B2913281 : Blo 1941435 2913281 := bstep (se 2 (by rfl) ⟨1092480, by rfl⟩ : syracuseStep 2913281 = 2184961) B2184961
theorem B1942187 : Blo 1941435 1942187 := bstep (se 1 (by rfl) ⟨1456640, by rfl⟩ : syracuseStep 1942187 = 2913281) B2913281
theorem B4916173 : Blo 1941435 4916173 := bbase (se 3 (by rfl) ⟨921782, by rfl⟩ : syracuseStep 4916173 = 1843565) (by norm_num)
theorem B6554897 : Blo 1941435 6554897 := bstep (se 2 (by rfl) ⟨2458086, by rfl⟩ : syracuseStep 6554897 = 4916173) B4916173
theorem B4369931 : Blo 1941435 4369931 := bstep (se 1 (by rfl) ⟨3277448, by rfl⟩ : syracuseStep 4369931 = 6554897) B6554897
theorem B2913287 : Blo 1941435 2913287 := bstep (se 1 (by rfl) ⟨2184965, by rfl⟩ : syracuseStep 2913287 = 4369931) B4369931
theorem B1942191 : Blo 1941435 1942191 := bstep (se 1 (by rfl) ⟨1456643, by rfl⟩ : syracuseStep 1942191 = 2913287) B2913287
theorem B2913293 : Blo 1941435 2913293 := bbase (se 3 (by rfl) ⟨546242, by rfl⟩ : syracuseStep 2913293 = 1092485) (by norm_num)
theorem B1942195 : Blo 1941435 1942195 := bstep (se 1 (by rfl) ⟨1456646, by rfl⟩ : syracuseStep 1942195 = 2913293) B2913293
theorem B4369949 : Blo 1941435 4369949 := bbase (se 3 (by rfl) ⟨819365, by rfl⟩ : syracuseStep 4369949 = 1638731) (by norm_num)
theorem B2913299 : Blo 1941435 2913299 := bstep (se 1 (by rfl) ⟨2184974, by rfl⟩ : syracuseStep 2913299 = 4369949) B4369949
theorem B1942199 : Blo 1941435 1942199 := bstep (se 1 (by rfl) ⟨1456649, by rfl⟩ : syracuseStep 1942199 = 2913299) B2913299
theorem B3277469 : Blo 1941435 3277469 := bbase (se 3 (by rfl) ⟨614525, by rfl⟩ : syracuseStep 3277469 = 1229051) (by norm_num)
theorem B2184979 : Blo 1941435 2184979 := bstep (se 1 (by rfl) ⟨1638734, by rfl⟩ : syracuseStep 2184979 = 3277469) B3277469
theorem B2913305 : Blo 1941435 2913305 := bstep (se 2 (by rfl) ⟨1092489, by rfl⟩ : syracuseStep 2913305 = 2184979) B2184979
theorem B1942203 : Blo 1941435 1942203 := bstep (se 1 (by rfl) ⟨1456652, by rfl⟩ : syracuseStep 1942203 = 2913305) B2913305
theorem B7474933 : Blo 1941435 7474933 := bbase (se 5 (by rfl) ⟨350387, by rfl⟩ : syracuseStep 7474933 = 700775) (by norm_num)
theorem B9966577 : Blo 1941435 9966577 := bstep (se 2 (by rfl) ⟨3737466, by rfl⟩ : syracuseStep 9966577 = 7474933) B7474933
theorem B13288769 : Blo 1941435 13288769 := bstep (se 2 (by rfl) ⟨4983288, by rfl⟩ : syracuseStep 13288769 = 9966577) B9966577
theorem B8859179 : Blo 1941435 8859179 := bstep (se 1 (by rfl) ⟨6644384, by rfl⟩ : syracuseStep 8859179 = 13288769) B13288769
theorem B5906119 : Blo 1941435 5906119 := bstep (se 1 (by rfl) ⟨4429589, by rfl⟩ : syracuseStep 5906119 = 8859179) B8859179
theorem B7874825 : Blo 1941435 7874825 := bstep (se 2 (by rfl) ⟨2953059, by rfl⟩ : syracuseStep 7874825 = 5906119) B5906119
theorem B20999533 : Blo 1941435 20999533 := bstep (se 3 (by rfl) ⟨3937412, by rfl⟩ : syracuseStep 20999533 = 7874825) B7874825
theorem B27999377 : Blo 1941435 27999377 := bstep (se 2 (by rfl) ⟨10499766, by rfl⟩ : syracuseStep 27999377 = 20999533) B20999533
theorem B18666251 : Blo 1941435 18666251 := bstep (se 1 (by rfl) ⟨13999688, by rfl⟩ : syracuseStep 18666251 = 27999377) B27999377
theorem B12444167 : Blo 1941435 12444167 := bstep (se 1 (by rfl) ⟨9333125, by rfl⟩ : syracuseStep 12444167 = 18666251) B18666251
theorem B8296111 : Blo 1941435 8296111 := bstep (se 1 (by rfl) ⟨6222083, by rfl⟩ : syracuseStep 8296111 = 12444167) B12444167
theorem B11061481 : Blo 1941435 11061481 := bstep (se 2 (by rfl) ⟨4148055, by rfl⟩ : syracuseStep 11061481 = 8296111) B8296111
theorem B14748641 : Blo 1941435 14748641 := bstep (se 2 (by rfl) ⟨5530740, by rfl⟩ : syracuseStep 14748641 = 11061481) B11061481
theorem B9832427 : Blo 1941435 9832427 := bstep (se 1 (by rfl) ⟨7374320, by rfl⟩ : syracuseStep 9832427 = 14748641) B14748641
theorem B6554951 : Blo 1941435 6554951 := bstep (se 1 (by rfl) ⟨4916213, by rfl⟩ : syracuseStep 6554951 = 9832427) B9832427
theorem B4369967 : Blo 1941435 4369967 := bstep (se 1 (by rfl) ⟨3277475, by rfl⟩ : syracuseStep 4369967 = 6554951) B6554951
theorem B2913311 : Blo 1941435 2913311 := bstep (se 1 (by rfl) ⟨2184983, by rfl⟩ : syracuseStep 2913311 = 4369967) B4369967
theorem B1942207 : Blo 1941435 1942207 := bstep (se 1 (by rfl) ⟨1456655, by rfl⟩ : syracuseStep 1942207 = 2913311) B2913311
theorem B2913317 : Blo 1941435 2913317 := bbase (se 4 (by rfl) ⟨273123, by rfl⟩ : syracuseStep 2913317 = 546247) (by norm_num)
theorem B1942211 : Blo 1941435 1942211 := bstep (se 1 (by rfl) ⟨1456658, by rfl⟩ : syracuseStep 1942211 = 2913317) B2913317
theorem B2458117 : Blo 1941435 2458117 := bbase (se 4 (by rfl) ⟨230448, by rfl⟩ : syracuseStep 2458117 = 460897) (by norm_num)
theorem B3277489 : Blo 1941435 3277489 := bstep (se 2 (by rfl) ⟨1229058, by rfl⟩ : syracuseStep 3277489 = 2458117) B2458117
theorem B4369985 : Blo 1941435 4369985 := bstep (se 2 (by rfl) ⟨1638744, by rfl⟩ : syracuseStep 4369985 = 3277489) B3277489
theorem B2913323 : Blo 1941435 2913323 := bstep (se 1 (by rfl) ⟨2184992, by rfl⟩ : syracuseStep 2913323 = 4369985) B4369985
theorem B1942215 : Blo 1941435 1942215 := bstep (se 1 (by rfl) ⟨1456661, by rfl⟩ : syracuseStep 1942215 = 2913323) B2913323
theorem B2184997 : Blo 1941435 2184997 := bbase (se 4 (by rfl) ⟨204843, by rfl⟩ : syracuseStep 2184997 = 409687) (by norm_num)
theorem B2913329 : Blo 1941435 2913329 := bstep (se 2 (by rfl) ⟨1092498, by rfl⟩ : syracuseStep 2913329 = 2184997) B2184997
theorem B1942219 : Blo 1941435 1942219 := bstep (se 1 (by rfl) ⟨1456664, by rfl⟩ : syracuseStep 1942219 = 2913329) B2913329
theorem B8296181 : Blo 1941435 8296181 := bbase (se 5 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 8296181 = 777767) (by norm_num)
theorem B5530787 : Blo 1941435 5530787 := bstep (se 1 (by rfl) ⟨4148090, by rfl⟩ : syracuseStep 5530787 = 8296181) B8296181
theorem B3687191 : Blo 1941435 3687191 := bstep (se 1 (by rfl) ⟨2765393, by rfl⟩ : syracuseStep 3687191 = 5530787) B5530787
theorem B2458127 : Blo 1941435 2458127 := bstep (se 1 (by rfl) ⟨1843595, by rfl⟩ : syracuseStep 2458127 = 3687191) B3687191
theorem B6555005 : Blo 1941435 6555005 := bstep (se 3 (by rfl) ⟨1229063, by rfl⟩ : syracuseStep 6555005 = 2458127) B2458127
theorem B4370003 : Blo 1941435 4370003 := bstep (se 1 (by rfl) ⟨3277502, by rfl⟩ : syracuseStep 4370003 = 6555005) B6555005
theorem B2913335 : Blo 1941435 2913335 := bstep (se 1 (by rfl) ⟨2185001, by rfl⟩ : syracuseStep 2913335 = 4370003) B4370003
theorem B1942223 : Blo 1941435 1942223 := bstep (se 1 (by rfl) ⟨1456667, by rfl⟩ : syracuseStep 1942223 = 2913335) B2913335
theorem B2913341 : Blo 1941435 2913341 := bbase (se 3 (by rfl) ⟨546251, by rfl⟩ : syracuseStep 2913341 = 1092503) (by norm_num)
theorem B1942227 : Blo 1941435 1942227 := bstep (se 1 (by rfl) ⟨1456670, by rfl⟩ : syracuseStep 1942227 = 2913341) B2913341
theorem B4370021 : Blo 1941435 4370021 := bbase (se 4 (by rfl) ⟨409689, by rfl⟩ : syracuseStep 4370021 = 819379) (by norm_num)
theorem B2913347 : Blo 1941435 2913347 := bstep (se 1 (by rfl) ⟨2185010, by rfl⟩ : syracuseStep 2913347 = 4370021) B4370021
theorem B1942231 : Blo 1941435 1942231 := bstep (se 1 (by rfl) ⟨1456673, by rfl⟩ : syracuseStep 1942231 = 2913347) B2913347
theorem B4916285 : Blo 1941435 4916285 := bbase (se 3 (by rfl) ⟨921803, by rfl⟩ : syracuseStep 4916285 = 1843607) (by norm_num)
theorem B3277523 : Blo 1941435 3277523 := bstep (se 1 (by rfl) ⟨2458142, by rfl⟩ : syracuseStep 3277523 = 4916285) B4916285
theorem B2185015 : Blo 1941435 2185015 := bstep (se 1 (by rfl) ⟨1638761, by rfl⟩ : syracuseStep 2185015 = 3277523) B3277523
theorem B2913353 : Blo 1941435 2913353 := bstep (se 2 (by rfl) ⟨1092507, by rfl⟩ : syracuseStep 2913353 = 2185015) B2185015
theorem B1942235 : Blo 1941435 1942235 := bstep (se 1 (by rfl) ⟨1456676, by rfl⟩ : syracuseStep 1942235 = 2913353) B2913353
theorem B3687221 : Blo 1941435 3687221 := bbase (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) (by norm_num)
theorem B9832589 : Blo 1941435 9832589 := bstep (se 3 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 9832589 = 3687221) B3687221
theorem B6555059 : Blo 1941435 6555059 := bstep (se 1 (by rfl) ⟨4916294, by rfl⟩ : syracuseStep 6555059 = 9832589) B9832589
theorem B4370039 : Blo 1941435 4370039 := bstep (se 1 (by rfl) ⟨3277529, by rfl⟩ : syracuseStep 4370039 = 6555059) B6555059
theorem B2913359 : Blo 1941435 2913359 := bstep (se 1 (by rfl) ⟨2185019, by rfl⟩ : syracuseStep 2913359 = 4370039) B4370039
theorem B1942239 : Blo 1941435 1942239 := bstep (se 1 (by rfl) ⟨1456679, by rfl⟩ : syracuseStep 1942239 = 2913359) B2913359
theorem B2913365 : Blo 1941435 2913365 := bbase (se 8 (by rfl) ⟨17070, by rfl⟩ : syracuseStep 2913365 = 34141) (by norm_num)
theorem B1942243 : Blo 1941435 1942243 := bstep (se 1 (by rfl) ⟨1456682, by rfl⟩ : syracuseStep 1942243 = 2913365) B2913365
theorem B3322261 : Blo 1941435 3322261 := bbase (se 6 (by rfl) ⟨77865, by rfl⟩ : syracuseStep 3322261 = 155731) (by norm_num)
theorem B17718725 : Blo 1941435 17718725 := bstep (se 4 (by rfl) ⟨1661130, by rfl⟩ : syracuseStep 17718725 = 3322261) B3322261
theorem B11812483 : Blo 1941435 11812483 := bstep (se 1 (by rfl) ⟨8859362, by rfl⟩ : syracuseStep 11812483 = 17718725) B17718725
theorem B15749977 : Blo 1941435 15749977 := bstep (se 2 (by rfl) ⟨5906241, by rfl⟩ : syracuseStep 15749977 = 11812483) B11812483
theorem B20999969 : Blo 1941435 20999969 := bstep (se 2 (by rfl) ⟨7874988, by rfl⟩ : syracuseStep 20999969 = 15749977) B15749977
theorem B13999979 : Blo 1941435 13999979 := bstep (se 1 (by rfl) ⟨10499984, by rfl⟩ : syracuseStep 13999979 = 20999969) B20999969
theorem B9333319 : Blo 1941435 9333319 := bstep (se 1 (by rfl) ⟨6999989, by rfl⟩ : syracuseStep 9333319 = 13999979) B13999979
theorem B12444425 : Blo 1941435 12444425 := bstep (se 2 (by rfl) ⟨4666659, by rfl⟩ : syracuseStep 12444425 = 9333319) B9333319
theorem B8296283 : Blo 1941435 8296283 := bstep (se 1 (by rfl) ⟨6222212, by rfl⟩ : syracuseStep 8296283 = 12444425) B12444425
theorem B5530855 : Blo 1941435 5530855 := bstep (se 1 (by rfl) ⟨4148141, by rfl⟩ : syracuseStep 5530855 = 8296283) B8296283
theorem B7374473 : Blo 1941435 7374473 := bstep (se 2 (by rfl) ⟨2765427, by rfl⟩ : syracuseStep 7374473 = 5530855) B5530855
theorem B4916315 : Blo 1941435 4916315 := bstep (se 1 (by rfl) ⟨3687236, by rfl⟩ : syracuseStep 4916315 = 7374473) B7374473
theorem B3277543 : Blo 1941435 3277543 := bstep (se 1 (by rfl) ⟨2458157, by rfl⟩ : syracuseStep 3277543 = 4916315) B4916315
theorem B4370057 : Blo 1941435 4370057 := bstep (se 2 (by rfl) ⟨1638771, by rfl⟩ : syracuseStep 4370057 = 3277543) B3277543
theorem B2913371 : Blo 1941435 2913371 := bstep (se 1 (by rfl) ⟨2185028, by rfl⟩ : syracuseStep 2913371 = 4370057) B4370057
theorem B1942247 : Blo 1941435 1942247 := bstep (se 1 (by rfl) ⟨1456685, by rfl⟩ : syracuseStep 1942247 = 2913371) B2913371
theorem B2185033 : Blo 1941435 2185033 := bbase (se 2 (by rfl) ⟨819387, by rfl⟩ : syracuseStep 2185033 = 1638775) (by norm_num)
theorem B2913377 : Blo 1941435 2913377 := bstep (se 2 (by rfl) ⟨1092516, by rfl⟩ : syracuseStep 2913377 = 2185033) B2185033
theorem B1942251 : Blo 1941435 1942251 := bstep (se 1 (by rfl) ⟨1456688, by rfl⟩ : syracuseStep 1942251 = 2913377) B2913377
theorem B2953133 : Blo 1941435 2953133 := bbase (se 3 (by rfl) ⟨553712, by rfl⟩ : syracuseStep 2953133 = 1107425) (by norm_num)
theorem B1968755 : Blo 1941435 1968755 := bstep (se 1 (by rfl) ⟨1476566, by rfl⟩ : syracuseStep 1968755 = 2953133) B2953133
theorem B21000053 : Blo 1941435 21000053 := bstep (se 5 (by rfl) ⟨984377, by rfl⟩ : syracuseStep 21000053 = 1968755) B1968755
theorem B14000035 : Blo 1941435 14000035 := bstep (se 1 (by rfl) ⟨10500026, by rfl⟩ : syracuseStep 14000035 = 21000053) B21000053
theorem B18666713 : Blo 1941435 18666713 := bstep (se 2 (by rfl) ⟨7000017, by rfl⟩ : syracuseStep 18666713 = 14000035) B14000035
theorem B12444475 : Blo 1941435 12444475 := bstep (se 1 (by rfl) ⟨9333356, by rfl⟩ : syracuseStep 12444475 = 18666713) B18666713
theorem B16592633 : Blo 1941435 16592633 := bstep (se 2 (by rfl) ⟨6222237, by rfl⟩ : syracuseStep 16592633 = 12444475) B12444475
theorem B11061755 : Blo 1941435 11061755 := bstep (se 1 (by rfl) ⟨8296316, by rfl⟩ : syracuseStep 11061755 = 16592633) B16592633
theorem B7374503 : Blo 1941435 7374503 := bstep (se 1 (by rfl) ⟨5530877, by rfl⟩ : syracuseStep 7374503 = 11061755) B11061755
theorem B4916335 : Blo 1941435 4916335 := bstep (se 1 (by rfl) ⟨3687251, by rfl⟩ : syracuseStep 4916335 = 7374503) B7374503
theorem B6555113 : Blo 1941435 6555113 := bstep (se 2 (by rfl) ⟨2458167, by rfl⟩ : syracuseStep 6555113 = 4916335) B4916335
theorem B4370075 : Blo 1941435 4370075 := bstep (se 1 (by rfl) ⟨3277556, by rfl⟩ : syracuseStep 4370075 = 6555113) B6555113
theorem B2913383 : Blo 1941435 2913383 := bstep (se 1 (by rfl) ⟨2185037, by rfl⟩ : syracuseStep 2913383 = 4370075) B4370075
theorem B1942255 : Blo 1941435 1942255 := bstep (se 1 (by rfl) ⟨1456691, by rfl⟩ : syracuseStep 1942255 = 2913383) B2913383
theorem B2913389 : Blo 1941435 2913389 := bbase (se 3 (by rfl) ⟨546260, by rfl⟩ : syracuseStep 2913389 = 1092521) (by norm_num)
theorem B1942259 : Blo 1941435 1942259 := bstep (se 1 (by rfl) ⟨1456694, by rfl⟩ : syracuseStep 1942259 = 2913389) B2913389
theorem B4370093 : Blo 1941435 4370093 := bbase (se 3 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 4370093 = 1638785) (by norm_num)
theorem B2913395 : Blo 1941435 2913395 := bstep (se 1 (by rfl) ⟨2185046, by rfl⟩ : syracuseStep 2913395 = 4370093) B4370093
theorem B1942263 : Blo 1941435 1942263 := bstep (se 1 (by rfl) ⟨1456697, by rfl⟩ : syracuseStep 1942263 = 2913395) B2913395
theorem B4666709 : Blo 1941435 4666709 := bbase (se 13 (by rfl) ⟨854, by rfl⟩ : syracuseStep 4666709 = 1709) (by norm_num)
theorem B3111139 : Blo 1941435 3111139 := bstep (se 1 (by rfl) ⟨2333354, by rfl⟩ : syracuseStep 3111139 = 4666709) B4666709
theorem B4148185 : Blo 1941435 4148185 := bstep (se 2 (by rfl) ⟨1555569, by rfl⟩ : syracuseStep 4148185 = 3111139) B3111139
theorem B5530913 : Blo 1941435 5530913 := bstep (se 2 (by rfl) ⟨2074092, by rfl⟩ : syracuseStep 5530913 = 4148185) B4148185
theorem B3687275 : Blo 1941435 3687275 := bstep (se 1 (by rfl) ⟨2765456, by rfl⟩ : syracuseStep 3687275 = 5530913) B5530913
theorem B2458183 : Blo 1941435 2458183 := bstep (se 1 (by rfl) ⟨1843637, by rfl⟩ : syracuseStep 2458183 = 3687275) B3687275
theorem B3277577 : Blo 1941435 3277577 := bstep (se 2 (by rfl) ⟨1229091, by rfl⟩ : syracuseStep 3277577 = 2458183) B2458183
theorem B2185051 : Blo 1941435 2185051 := bstep (se 1 (by rfl) ⟨1638788, by rfl⟩ : syracuseStep 2185051 = 3277577) B3277577
theorem B2913401 : Blo 1941435 2913401 := bstep (se 2 (by rfl) ⟨1092525, by rfl⟩ : syracuseStep 2913401 = 2185051) B2185051
theorem B1942267 : Blo 1941435 1942267 := bstep (se 1 (by rfl) ⟨1456700, by rfl⟩ : syracuseStep 1942267 = 2913401) B2913401
theorem B14000149 : Blo 1941435 14000149 := bbase (se 6 (by rfl) ⟨328128, by rfl⟩ : syracuseStep 14000149 = 656257) (by norm_num)
theorem B18666865 : Blo 1941435 18666865 := bstep (se 2 (by rfl) ⟨7000074, by rfl⟩ : syracuseStep 18666865 = 14000149) B14000149
theorem B24889153 : Blo 1941435 24889153 := bstep (se 2 (by rfl) ⟨9333432, by rfl⟩ : syracuseStep 24889153 = 18666865) B18666865
theorem B33185537 : Blo 1941435 33185537 := bstep (se 2 (by rfl) ⟨12444576, by rfl⟩ : syracuseStep 33185537 = 24889153) B24889153
theorem B22123691 : Blo 1941435 22123691 := bstep (se 1 (by rfl) ⟨16592768, by rfl⟩ : syracuseStep 22123691 = 33185537) B33185537
theorem B14749127 : Blo 1941435 14749127 := bstep (se 1 (by rfl) ⟨11061845, by rfl⟩ : syracuseStep 14749127 = 22123691) B22123691
theorem B9832751 : Blo 1941435 9832751 := bstep (se 1 (by rfl) ⟨7374563, by rfl⟩ : syracuseStep 9832751 = 14749127) B14749127
theorem B6555167 : Blo 1941435 6555167 := bstep (se 1 (by rfl) ⟨4916375, by rfl⟩ : syracuseStep 6555167 = 9832751) B9832751
theorem B4370111 : Blo 1941435 4370111 := bstep (se 1 (by rfl) ⟨3277583, by rfl⟩ : syracuseStep 4370111 = 6555167) B6555167
theorem B2913407 : Blo 1941435 2913407 := bstep (se 1 (by rfl) ⟨2185055, by rfl⟩ : syracuseStep 2913407 = 4370111) B4370111
theorem B1942271 : Blo 1941435 1942271 := bstep (se 1 (by rfl) ⟨1456703, by rfl⟩ : syracuseStep 1942271 = 2913407) B2913407
theorem B2913413 : Blo 1941435 2913413 := bbase (se 4 (by rfl) ⟨273132, by rfl⟩ : syracuseStep 2913413 = 546265) (by norm_num)
theorem B1942275 : Blo 1941435 1942275 := bstep (se 1 (by rfl) ⟨1456706, by rfl⟩ : syracuseStep 1942275 = 2913413) B2913413
theorem B3277597 : Blo 1941435 3277597 := bbase (se 3 (by rfl) ⟨614549, by rfl⟩ : syracuseStep 3277597 = 1229099) (by norm_num)
theorem B4370129 : Blo 1941435 4370129 := bstep (se 2 (by rfl) ⟨1638798, by rfl⟩ : syracuseStep 4370129 = 3277597) B3277597
theorem B2913419 : Blo 1941435 2913419 := bstep (se 1 (by rfl) ⟨2185064, by rfl⟩ : syracuseStep 2913419 = 4370129) B4370129
theorem B1942279 : Blo 1941435 1942279 := bstep (se 1 (by rfl) ⟨1456709, by rfl⟩ : syracuseStep 1942279 = 2913419) B2913419
theorem B2185069 : Blo 1941435 2185069 := bbase (se 3 (by rfl) ⟨409700, by rfl⟩ : syracuseStep 2185069 = 819401) (by norm_num)
theorem B2913425 : Blo 1941435 2913425 := bstep (se 2 (by rfl) ⟨1092534, by rfl⟩ : syracuseStep 2913425 = 2185069) B2185069
theorem B1942283 : Blo 1941435 1942283 := bstep (se 1 (by rfl) ⟨1456712, by rfl⟩ : syracuseStep 1942283 = 2913425) B2913425
theorem B6555221 : Blo 1941435 6555221 := bbase (se 8 (by rfl) ⟨38409, by rfl⟩ : syracuseStep 6555221 = 76819) (by norm_num)
theorem B4370147 : Blo 1941435 4370147 := bstep (se 1 (by rfl) ⟨3277610, by rfl⟩ : syracuseStep 4370147 = 6555221) B6555221
theorem B2913431 : Blo 1941435 2913431 := bstep (se 1 (by rfl) ⟨2185073, by rfl⟩ : syracuseStep 2913431 = 4370147) B4370147
theorem B1942287 : Blo 1941435 1942287 := bstep (se 1 (by rfl) ⟨1456715, by rfl⟩ : syracuseStep 1942287 = 2913431) B2913431
theorem B2913437 : Blo 1941435 2913437 := bbase (se 3 (by rfl) ⟨546269, by rfl⟩ : syracuseStep 2913437 = 1092539) (by norm_num)
theorem B1942291 : Blo 1941435 1942291 := bstep (se 1 (by rfl) ⟨1456718, by rfl⟩ : syracuseStep 1942291 = 2913437) B2913437
theorem B4370165 : Blo 1941435 4370165 := bbase (se 5 (by rfl) ⟨204851, by rfl⟩ : syracuseStep 4370165 = 409703) (by norm_num)
theorem B2913443 : Blo 1941435 2913443 := bstep (se 1 (by rfl) ⟨2185082, by rfl⟩ : syracuseStep 2913443 = 4370165) B4370165
theorem B1942295 : Blo 1941435 1942295 := bstep (se 1 (by rfl) ⟨1456721, by rfl⟩ : syracuseStep 1942295 = 2913443) B2913443
theorem B5250133 : Blo 1941435 5250133 := bbase (se 8 (by rfl) ⟨30762, by rfl⟩ : syracuseStep 5250133 = 61525) (by norm_num)
theorem B7000177 : Blo 1941435 7000177 := bstep (se 2 (by rfl) ⟨2625066, by rfl⟩ : syracuseStep 7000177 = 5250133) B5250133
theorem B9333569 : Blo 1941435 9333569 := bstep (se 2 (by rfl) ⟨3500088, by rfl⟩ : syracuseStep 9333569 = 7000177) B7000177
theorem B24889517 : Blo 1941435 24889517 := bstep (se 3 (by rfl) ⟨4666784, by rfl⟩ : syracuseStep 24889517 = 9333569) B9333569
theorem B16593011 : Blo 1941435 16593011 := bstep (se 1 (by rfl) ⟨12444758, by rfl⟩ : syracuseStep 16593011 = 24889517) B24889517
theorem B11062007 : Blo 1941435 11062007 := bstep (se 1 (by rfl) ⟨8296505, by rfl⟩ : syracuseStep 11062007 = 16593011) B16593011
theorem B7374671 : Blo 1941435 7374671 := bstep (se 1 (by rfl) ⟨5531003, by rfl⟩ : syracuseStep 7374671 = 11062007) B11062007
theorem B4916447 : Blo 1941435 4916447 := bstep (se 1 (by rfl) ⟨3687335, by rfl⟩ : syracuseStep 4916447 = 7374671) B7374671
theorem B3277631 : Blo 1941435 3277631 := bstep (se 1 (by rfl) ⟨2458223, by rfl⟩ : syracuseStep 3277631 = 4916447) B4916447
theorem B2185087 : Blo 1941435 2185087 := bstep (se 1 (by rfl) ⟨1638815, by rfl⟩ : syracuseStep 2185087 = 3277631) B3277631
theorem B2913449 : Blo 1941435 2913449 := bstep (se 2 (by rfl) ⟨1092543, by rfl⟩ : syracuseStep 2913449 = 2185087) B2185087
theorem B1942299 : Blo 1941435 1942299 := bstep (se 1 (by rfl) ⟨1456724, by rfl⟩ : syracuseStep 1942299 = 2913449) B2913449
theorem B4148261 : Blo 1941435 4148261 := bbase (se 4 (by rfl) ⟨388899, by rfl⟩ : syracuseStep 4148261 = 777799) (by norm_num)
theorem B2765507 : Blo 1941435 2765507 := bstep (se 1 (by rfl) ⟨2074130, by rfl⟩ : syracuseStep 2765507 = 4148261) B4148261
theorem B7374685 : Blo 1941435 7374685 := bstep (se 3 (by rfl) ⟨1382753, by rfl⟩ : syracuseStep 7374685 = 2765507) B2765507
theorem B9832913 : Blo 1941435 9832913 := bstep (se 2 (by rfl) ⟨3687342, by rfl⟩ : syracuseStep 9832913 = 7374685) B7374685
theorem B6555275 : Blo 1941435 6555275 := bstep (se 1 (by rfl) ⟨4916456, by rfl⟩ : syracuseStep 6555275 = 9832913) B9832913
theorem B4370183 : Blo 1941435 4370183 := bstep (se 1 (by rfl) ⟨3277637, by rfl⟩ : syracuseStep 4370183 = 6555275) B6555275
theorem B2913455 : Blo 1941435 2913455 := bstep (se 1 (by rfl) ⟨2185091, by rfl⟩ : syracuseStep 2913455 = 4370183) B4370183
theorem B1942303 : Blo 1941435 1942303 := bstep (se 1 (by rfl) ⟨1456727, by rfl⟩ : syracuseStep 1942303 = 2913455) B2913455
theorem B2913461 : Blo 1941435 2913461 := bbase (se 5 (by rfl) ⟨136568, by rfl⟩ : syracuseStep 2913461 = 273137) (by norm_num)
theorem B1942307 : Blo 1941435 1942307 := bstep (se 1 (by rfl) ⟨1456730, by rfl⟩ : syracuseStep 1942307 = 2913461) B2913461
theorem B4916477 : Blo 1941435 4916477 := bbase (se 3 (by rfl) ⟨921839, by rfl⟩ : syracuseStep 4916477 = 1843679) (by norm_num)
theorem B3277651 : Blo 1941435 3277651 := bstep (se 1 (by rfl) ⟨2458238, by rfl⟩ : syracuseStep 3277651 = 4916477) B4916477
theorem B4370201 : Blo 1941435 4370201 := bstep (se 2 (by rfl) ⟨1638825, by rfl⟩ : syracuseStep 4370201 = 3277651) B3277651
theorem B2913467 : Blo 1941435 2913467 := bstep (se 1 (by rfl) ⟨2185100, by rfl⟩ : syracuseStep 2913467 = 4370201) B4370201
theorem B1942311 : Blo 1941435 1942311 := bstep (se 1 (by rfl) ⟨1456733, by rfl⟩ : syracuseStep 1942311 = 2913467) B2913467
theorem B2185105 : Blo 1941435 2185105 := bbase (se 2 (by rfl) ⟨819414, by rfl⟩ : syracuseStep 2185105 = 1638829) (by norm_num)
theorem B2913473 : Blo 1941435 2913473 := bstep (se 2 (by rfl) ⟨1092552, by rfl⟩ : syracuseStep 2913473 = 2185105) B2185105
theorem B1942315 : Blo 1941435 1942315 := bstep (se 1 (by rfl) ⟨1456736, by rfl⟩ : syracuseStep 1942315 = 2913473) B2913473
theorem B3687373 : Blo 1941435 3687373 := bbase (se 3 (by rfl) ⟨691382, by rfl⟩ : syracuseStep 3687373 = 1382765) (by norm_num)
theorem B4916497 : Blo 1941435 4916497 := bstep (se 2 (by rfl) ⟨1843686, by rfl⟩ : syracuseStep 4916497 = 3687373) B3687373
theorem B6555329 : Blo 1941435 6555329 := bstep (se 2 (by rfl) ⟨2458248, by rfl⟩ : syracuseStep 6555329 = 4916497) B4916497
theorem B4370219 : Blo 1941435 4370219 := bstep (se 1 (by rfl) ⟨3277664, by rfl⟩ : syracuseStep 4370219 = 6555329) B6555329
theorem B2913479 : Blo 1941435 2913479 := bstep (se 1 (by rfl) ⟨2185109, by rfl⟩ : syracuseStep 2913479 = 4370219) B4370219
theorem B1942319 : Blo 1941435 1942319 := bstep (se 1 (by rfl) ⟨1456739, by rfl⟩ : syracuseStep 1942319 = 2913479) B2913479
theorem B2913485 : Blo 1941435 2913485 := bbase (se 3 (by rfl) ⟨546278, by rfl⟩ : syracuseStep 2913485 = 1092557) (by norm_num)
theorem B1942323 : Blo 1941435 1942323 := bstep (se 1 (by rfl) ⟨1456742, by rfl⟩ : syracuseStep 1942323 = 2913485) B2913485
theorem B4370237 : Blo 1941435 4370237 := bbase (se 3 (by rfl) ⟨819419, by rfl⟩ : syracuseStep 4370237 = 1638839) (by norm_num)
theorem B2913491 : Blo 1941435 2913491 := bstep (se 1 (by rfl) ⟨2185118, by rfl⟩ : syracuseStep 2913491 = 4370237) B4370237
theorem B1942327 : Blo 1941435 1942327 := bstep (se 1 (by rfl) ⟨1456745, by rfl⟩ : syracuseStep 1942327 = 2913491) B2913491
theorem B3277685 : Blo 1941435 3277685 := bbase (se 5 (by rfl) ⟨153641, by rfl⟩ : syracuseStep 3277685 = 307283) (by norm_num)
theorem B2185123 : Blo 1941435 2185123 := bstep (se 1 (by rfl) ⟨1638842, by rfl⟩ : syracuseStep 2185123 = 3277685) B3277685
theorem B2913497 : Blo 1941435 2913497 := bstep (se 2 (by rfl) ⟨1092561, by rfl⟩ : syracuseStep 2913497 = 2185123) B2185123
theorem B1942331 : Blo 1941435 1942331 := bstep (se 1 (by rfl) ⟨1456748, by rfl⟩ : syracuseStep 1942331 = 2913497) B2913497
theorem B7475429 : Blo 1941435 7475429 := bbase (se 4 (by rfl) ⟨700821, by rfl⟩ : syracuseStep 7475429 = 1401643) (by norm_num)
theorem B4983619 : Blo 1941435 4983619 := bstep (se 1 (by rfl) ⟨3737714, by rfl⟩ : syracuseStep 4983619 = 7475429) B7475429
theorem B6644825 : Blo 1941435 6644825 := bstep (se 2 (by rfl) ⟨2491809, by rfl⟩ : syracuseStep 6644825 = 4983619) B4983619
theorem B4429883 : Blo 1941435 4429883 := bstep (se 1 (by rfl) ⟨3322412, by rfl⟩ : syracuseStep 4429883 = 6644825) B6644825
theorem B2953255 : Blo 1941435 2953255 := bstep (se 1 (by rfl) ⟨2214941, by rfl⟩ : syracuseStep 2953255 = 4429883) B4429883
theorem B3937673 : Blo 1941435 3937673 := bstep (se 2 (by rfl) ⟨1476627, by rfl⟩ : syracuseStep 3937673 = 2953255) B2953255
theorem B10500461 : Blo 1941435 10500461 := bstep (se 3 (by rfl) ⟨1968836, by rfl⟩ : syracuseStep 10500461 = 3937673) B3937673
theorem B7000307 : Blo 1941435 7000307 := bstep (se 1 (by rfl) ⟨5250230, by rfl⟩ : syracuseStep 7000307 = 10500461) B10500461
theorem B4666871 : Blo 1941435 4666871 := bstep (se 1 (by rfl) ⟨3500153, by rfl⟩ : syracuseStep 4666871 = 7000307) B7000307
theorem B3111247 : Blo 1941435 3111247 := bstep (se 1 (by rfl) ⟨2333435, by rfl⟩ : syracuseStep 3111247 = 4666871) B4666871
theorem B4148329 : Blo 1941435 4148329 := bstep (se 2 (by rfl) ⟨1555623, by rfl⟩ : syracuseStep 4148329 = 3111247) B3111247
theorem B5531105 : Blo 1941435 5531105 := bstep (se 2 (by rfl) ⟨2074164, by rfl⟩ : syracuseStep 5531105 = 4148329) B4148329
theorem B14749613 : Blo 1941435 14749613 := bstep (se 3 (by rfl) ⟨2765552, by rfl⟩ : syracuseStep 14749613 = 5531105) B5531105
theorem B9833075 : Blo 1941435 9833075 := bstep (se 1 (by rfl) ⟨7374806, by rfl⟩ : syracuseStep 9833075 = 14749613) B14749613
theorem B6555383 : Blo 1941435 6555383 := bstep (se 1 (by rfl) ⟨4916537, by rfl⟩ : syracuseStep 6555383 = 9833075) B9833075
theorem B4370255 : Blo 1941435 4370255 := bstep (se 1 (by rfl) ⟨3277691, by rfl⟩ : syracuseStep 4370255 = 6555383) B6555383
theorem B2913503 : Blo 1941435 2913503 := bstep (se 1 (by rfl) ⟨2185127, by rfl⟩ : syracuseStep 2913503 = 4370255) B4370255
theorem B1942335 : Blo 1941435 1942335 := bstep (se 1 (by rfl) ⟨1456751, by rfl⟩ : syracuseStep 1942335 = 2913503) B2913503
theorem B2913509 : Blo 1941435 2913509 := bbase (se 4 (by rfl) ⟨273141, by rfl⟩ : syracuseStep 2913509 = 546283) (by norm_num)
theorem B1942339 : Blo 1941435 1942339 := bstep (se 1 (by rfl) ⟨1456754, by rfl⟩ : syracuseStep 1942339 = 2913509) B2913509
theorem B1968845 : Blo 1941435 1968845 := bbase (se 3 (by rfl) ⟨369158, by rfl⟩ : syracuseStep 1968845 = 738317) (by norm_num)
theorem B5250253 : Blo 1941435 5250253 := bstep (se 3 (by rfl) ⟨984422, by rfl⟩ : syracuseStep 5250253 = 1968845) B1968845
theorem B7000337 : Blo 1941435 7000337 := bstep (se 2 (by rfl) ⟨2625126, by rfl⟩ : syracuseStep 7000337 = 5250253) B5250253
theorem B4666891 : Blo 1941435 4666891 := bstep (se 1 (by rfl) ⟨3500168, by rfl⟩ : syracuseStep 4666891 = 7000337) B7000337
theorem B6222521 : Blo 1941435 6222521 := bstep (se 2 (by rfl) ⟨2333445, by rfl⟩ : syracuseStep 6222521 = 4666891) B4666891
theorem B4148347 : Blo 1941435 4148347 := bstep (se 1 (by rfl) ⟨3111260, by rfl⟩ : syracuseStep 4148347 = 6222521) B6222521
theorem B5531129 : Blo 1941435 5531129 := bstep (se 2 (by rfl) ⟨2074173, by rfl⟩ : syracuseStep 5531129 = 4148347) B4148347
theorem B3687419 : Blo 1941435 3687419 := bstep (se 1 (by rfl) ⟨2765564, by rfl⟩ : syracuseStep 3687419 = 5531129) B5531129
theorem B2458279 : Blo 1941435 2458279 := bstep (se 1 (by rfl) ⟨1843709, by rfl⟩ : syracuseStep 2458279 = 3687419) B3687419
theorem B3277705 : Blo 1941435 3277705 := bstep (se 2 (by rfl) ⟨1229139, by rfl⟩ : syracuseStep 3277705 = 2458279) B2458279
theorem B4370273 : Blo 1941435 4370273 := bstep (se 2 (by rfl) ⟨1638852, by rfl⟩ : syracuseStep 4370273 = 3277705) B3277705
theorem B2913515 : Blo 1941435 2913515 := bstep (se 1 (by rfl) ⟨2185136, by rfl⟩ : syracuseStep 2913515 = 4370273) B4370273
theorem B1942343 : Blo 1941435 1942343 := bstep (se 1 (by rfl) ⟨1456757, by rfl⟩ : syracuseStep 1942343 = 2913515) B2913515
theorem B2185141 : Blo 1941435 2185141 := bbase (se 5 (by rfl) ⟨102428, by rfl⟩ : syracuseStep 2185141 = 204857) (by norm_num)
theorem B2913521 : Blo 1941435 2913521 := bstep (se 2 (by rfl) ⟨1092570, by rfl⟩ : syracuseStep 2913521 = 2185141) B2185141
theorem B1942347 : Blo 1941435 1942347 := bstep (se 1 (by rfl) ⟨1456760, by rfl⟩ : syracuseStep 1942347 = 2913521) B2913521
theorem B2458289 : Blo 1941435 2458289 := bbase (se 2 (by rfl) ⟨921858, by rfl⟩ : syracuseStep 2458289 = 1843717) (by norm_num)
theorem B6555437 : Blo 1941435 6555437 := bstep (se 3 (by rfl) ⟨1229144, by rfl⟩ : syracuseStep 6555437 = 2458289) B2458289
theorem B4370291 : Blo 1941435 4370291 := bstep (se 1 (by rfl) ⟨3277718, by rfl⟩ : syracuseStep 4370291 = 6555437) B6555437
theorem B2913527 : Blo 1941435 2913527 := bstep (se 1 (by rfl) ⟨2185145, by rfl⟩ : syracuseStep 2913527 = 4370291) B4370291
theorem B1942351 : Blo 1941435 1942351 := bstep (se 1 (by rfl) ⟨1456763, by rfl⟩ : syracuseStep 1942351 = 2913527) B2913527
theorem B2913533 : Blo 1941435 2913533 := bbase (se 3 (by rfl) ⟨546287, by rfl⟩ : syracuseStep 2913533 = 1092575) (by norm_num)
theorem B1942355 : Blo 1941435 1942355 := bstep (se 1 (by rfl) ⟨1456766, by rfl⟩ : syracuseStep 1942355 = 2913533) B2913533
theorem B4370309 : Blo 1941435 4370309 := bbase (se 4 (by rfl) ⟨409716, by rfl⟩ : syracuseStep 4370309 = 819433) (by norm_num)
theorem B2913539 : Blo 1941435 2913539 := bstep (se 1 (by rfl) ⟨2185154, by rfl⟩ : syracuseStep 2913539 = 4370309) B4370309
theorem B1942359 : Blo 1941435 1942359 := bstep (se 1 (by rfl) ⟨1456769, by rfl⟩ : syracuseStep 1942359 = 2913539) B2913539
theorem B3111293 : Blo 1941435 3111293 := bbase (se 3 (by rfl) ⟨583367, by rfl⟩ : syracuseStep 3111293 = 1166735) (by norm_num)
theorem B2074195 : Blo 1941435 2074195 := bstep (se 1 (by rfl) ⟨1555646, by rfl⟩ : syracuseStep 2074195 = 3111293) B3111293
theorem B2765593 : Blo 1941435 2765593 := bstep (se 2 (by rfl) ⟨1037097, by rfl⟩ : syracuseStep 2765593 = 2074195) B2074195
theorem B3687457 : Blo 1941435 3687457 := bstep (se 2 (by rfl) ⟨1382796, by rfl⟩ : syracuseStep 3687457 = 2765593) B2765593
theorem B4916609 : Blo 1941435 4916609 := bstep (se 2 (by rfl) ⟨1843728, by rfl⟩ : syracuseStep 4916609 = 3687457) B3687457
theorem B3277739 : Blo 1941435 3277739 := bstep (se 1 (by rfl) ⟨2458304, by rfl⟩ : syracuseStep 3277739 = 4916609) B4916609
theorem B2185159 : Blo 1941435 2185159 := bstep (se 1 (by rfl) ⟨1638869, by rfl⟩ : syracuseStep 2185159 = 3277739) B3277739
theorem B2913545 : Blo 1941435 2913545 := bstep (se 2 (by rfl) ⟨1092579, by rfl⟩ : syracuseStep 2913545 = 2185159) B2185159
theorem B1942363 : Blo 1941435 1942363 := bstep (se 1 (by rfl) ⟨1456772, by rfl⟩ : syracuseStep 1942363 = 2913545) B2913545
theorem B9833237 : Blo 1941435 9833237 := bbase (se 6 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 9833237 = 460933) (by norm_num)
theorem B6555491 : Blo 1941435 6555491 := bstep (se 1 (by rfl) ⟨4916618, by rfl⟩ : syracuseStep 6555491 = 9833237) B9833237
theorem B4370327 : Blo 1941435 4370327 := bstep (se 1 (by rfl) ⟨3277745, by rfl⟩ : syracuseStep 4370327 = 6555491) B6555491
theorem B2913551 : Blo 1941435 2913551 := bstep (se 1 (by rfl) ⟨2185163, by rfl⟩ : syracuseStep 2913551 = 4370327) B4370327
theorem B1942367 : Blo 1941435 1942367 := bstep (se 1 (by rfl) ⟨1456775, by rfl⟩ : syracuseStep 1942367 = 2913551) B2913551
theorem B2913557 : Blo 1941435 2913557 := bbase (se 6 (by rfl) ⟨68286, by rfl⟩ : syracuseStep 2913557 = 136573) (by norm_num)
theorem B1942371 : Blo 1941435 1942371 := bstep (se 1 (by rfl) ⟨1456778, by rfl⟩ : syracuseStep 1942371 = 2913557) B2913557
theorem B5051717 : Blo 1941435 5051717 := bbase (se 4 (by rfl) ⟨473598, by rfl⟩ : syracuseStep 5051717 = 947197) (by norm_num)
theorem B3367811 : Blo 1941435 3367811 := bstep (se 1 (by rfl) ⟨2525858, by rfl⟩ : syracuseStep 3367811 = 5051717) B5051717
theorem B2245207 : Blo 1941435 2245207 := bstep (se 1 (by rfl) ⟨1683905, by rfl⟩ : syracuseStep 2245207 = 3367811) B3367811
theorem B2993609 : Blo 1941435 2993609 := bstep (se 2 (by rfl) ⟨1122603, by rfl⟩ : syracuseStep 2993609 = 2245207) B2245207
theorem B7982957 : Blo 1941435 7982957 := bstep (se 3 (by rfl) ⟨1496804, by rfl⟩ : syracuseStep 7982957 = 2993609) B2993609
theorem B5321971 : Blo 1941435 5321971 := bstep (se 1 (by rfl) ⟨3991478, by rfl⟩ : syracuseStep 5321971 = 7982957) B7982957
theorem B7095961 : Blo 1941435 7095961 := bstep (se 2 (by rfl) ⟨2660985, by rfl⟩ : syracuseStep 7095961 = 5321971) B5321971
theorem B9461281 : Blo 1941435 9461281 := bstep (se 2 (by rfl) ⟨3547980, by rfl⟩ : syracuseStep 9461281 = 7095961) B7095961
theorem B12615041 : Blo 1941435 12615041 := bstep (se 2 (by rfl) ⟨4730640, by rfl⟩ : syracuseStep 12615041 = 9461281) B9461281
theorem B33640109 : Blo 1941435 33640109 := bstep (se 3 (by rfl) ⟨6307520, by rfl⟩ : syracuseStep 33640109 = 12615041) B12615041
theorem B22426739 : Blo 1941435 22426739 := bstep (se 1 (by rfl) ⟨16820054, by rfl⟩ : syracuseStep 22426739 = 33640109) B33640109
theorem B14951159 : Blo 1941435 14951159 := bstep (se 1 (by rfl) ⟨11213369, by rfl⟩ : syracuseStep 14951159 = 22426739) B22426739
theorem B9967439 : Blo 1941435 9967439 := bstep (se 1 (by rfl) ⟨7475579, by rfl⟩ : syracuseStep 9967439 = 14951159) B14951159
theorem B6644959 : Blo 1941435 6644959 := bstep (se 1 (by rfl) ⟨4983719, by rfl⟩ : syracuseStep 6644959 = 9967439) B9967439
theorem B35439781 : Blo 1941435 35439781 := bstep (se 4 (by rfl) ⟨3322479, by rfl⟩ : syracuseStep 35439781 = 6644959) B6644959
theorem B47253041 : Blo 1941435 47253041 := bstep (se 2 (by rfl) ⟨17719890, by rfl⟩ : syracuseStep 47253041 = 35439781) B35439781
theorem B31502027 : Blo 1941435 31502027 := bstep (se 1 (by rfl) ⟨23626520, by rfl⟩ : syracuseStep 31502027 = 47253041) B47253041
theorem B21001351 : Blo 1941435 21001351 := bstep (se 1 (by rfl) ⟨15751013, by rfl⟩ : syracuseStep 21001351 = 31502027) B31502027
theorem B28001801 : Blo 1941435 28001801 := bstep (se 2 (by rfl) ⟨10500675, by rfl⟩ : syracuseStep 28001801 = 21001351) B21001351
theorem B18667867 : Blo 1941435 18667867 := bstep (se 1 (by rfl) ⟨14000900, by rfl⟩ : syracuseStep 18667867 = 28001801) B28001801
theorem B24890489 : Blo 1941435 24890489 := bstep (se 2 (by rfl) ⟨9333933, by rfl⟩ : syracuseStep 24890489 = 18667867) B18667867
theorem B16593659 : Blo 1941435 16593659 := bstep (se 1 (by rfl) ⟨12445244, by rfl⟩ : syracuseStep 16593659 = 24890489) B24890489
theorem B11062439 : Blo 1941435 11062439 := bstep (se 1 (by rfl) ⟨8296829, by rfl⟩ : syracuseStep 11062439 = 16593659) B16593659
theorem B7374959 : Blo 1941435 7374959 := bstep (se 1 (by rfl) ⟨5531219, by rfl⟩ : syracuseStep 7374959 = 11062439) B11062439
theorem B4916639 : Blo 1941435 4916639 := bstep (se 1 (by rfl) ⟨3687479, by rfl⟩ : syracuseStep 4916639 = 7374959) B7374959
theorem B3277759 : Blo 1941435 3277759 := bstep (se 1 (by rfl) ⟨2458319, by rfl⟩ : syracuseStep 3277759 = 4916639) B4916639
theorem B4370345 : Blo 1941435 4370345 := bstep (se 2 (by rfl) ⟨1638879, by rfl⟩ : syracuseStep 4370345 = 3277759) B3277759
theorem B2913563 : Blo 1941435 2913563 := bstep (se 1 (by rfl) ⟨2185172, by rfl⟩ : syracuseStep 2913563 = 4370345) B4370345
theorem B1942375 : Blo 1941435 1942375 := bstep (se 1 (by rfl) ⟨1456781, by rfl⟩ : syracuseStep 1942375 = 2913563) B2913563
theorem B2185177 : Blo 1941435 2185177 := bbase (se 2 (by rfl) ⟨819441, by rfl⟩ : syracuseStep 2185177 = 1638883) (by norm_num)
theorem B2913569 : Blo 1941435 2913569 := bstep (se 2 (by rfl) ⟨1092588, by rfl⟩ : syracuseStep 2913569 = 2185177) B2185177
theorem B1942379 : Blo 1941435 1942379 := bstep (se 1 (by rfl) ⟨1456784, by rfl⟩ : syracuseStep 1942379 = 2913569) B2913569
theorem B2765621 : Blo 1941435 2765621 := bbase (se 5 (by rfl) ⟨129638, by rfl⟩ : syracuseStep 2765621 = 259277) (by norm_num)
theorem B7374989 : Blo 1941435 7374989 := bstep (se 3 (by rfl) ⟨1382810, by rfl⟩ : syracuseStep 7374989 = 2765621) B2765621
theorem B4916659 : Blo 1941435 4916659 := bstep (se 1 (by rfl) ⟨3687494, by rfl⟩ : syracuseStep 4916659 = 7374989) B7374989
theorem B6555545 : Blo 1941435 6555545 := bstep (se 2 (by rfl) ⟨2458329, by rfl⟩ : syracuseStep 6555545 = 4916659) B4916659
theorem B4370363 : Blo 1941435 4370363 := bstep (se 1 (by rfl) ⟨3277772, by rfl⟩ : syracuseStep 4370363 = 6555545) B6555545
theorem B2913575 : Blo 1941435 2913575 := bstep (se 1 (by rfl) ⟨2185181, by rfl⟩ : syracuseStep 2913575 = 4370363) B4370363
theorem B1942383 : Blo 1941435 1942383 := bstep (se 1 (by rfl) ⟨1456787, by rfl⟩ : syracuseStep 1942383 = 2913575) B2913575
theorem B2913581 : Blo 1941435 2913581 := bbase (se 3 (by rfl) ⟨546296, by rfl⟩ : syracuseStep 2913581 = 1092593) (by norm_num)
theorem B1942387 : Blo 1941435 1942387 := bstep (se 1 (by rfl) ⟨1456790, by rfl⟩ : syracuseStep 1942387 = 2913581) B2913581
theorem B4370381 : Blo 1941435 4370381 := bbase (se 3 (by rfl) ⟨819446, by rfl⟩ : syracuseStep 4370381 = 1638893) (by norm_num)
theorem B2913587 : Blo 1941435 2913587 := bstep (se 1 (by rfl) ⟨2185190, by rfl⟩ : syracuseStep 2913587 = 4370381) B4370381
theorem B1942391 : Blo 1941435 1942391 := bstep (se 1 (by rfl) ⟨1456793, by rfl⟩ : syracuseStep 1942391 = 2913587) B2913587
theorem B2458345 : Blo 1941435 2458345 := bbase (se 2 (by rfl) ⟨921879, by rfl⟩ : syracuseStep 2458345 = 1843759) (by norm_num)
theorem B3277793 : Blo 1941435 3277793 := bstep (se 2 (by rfl) ⟨1229172, by rfl⟩ : syracuseStep 3277793 = 2458345) B2458345
theorem B2185195 : Blo 1941435 2185195 := bstep (se 1 (by rfl) ⟨1638896, by rfl⟩ : syracuseStep 2185195 = 3277793) B3277793
theorem B2913593 : Blo 1941435 2913593 := bstep (se 2 (by rfl) ⟨1092597, by rfl⟩ : syracuseStep 2913593 = 2185195) B2185195
theorem B1942395 : Blo 1941435 1942395 := bstep (se 1 (by rfl) ⟨1456796, by rfl⟩ : syracuseStep 1942395 = 2913593) B2913593
theorem B12445397 : Blo 1941435 12445397 := bbase (se 7 (by rfl) ⟨145844, by rfl⟩ : syracuseStep 12445397 = 291689) (by norm_num)
theorem B8296931 : Blo 1941435 8296931 := bstep (se 1 (by rfl) ⟨6222698, by rfl⟩ : syracuseStep 8296931 = 12445397) B12445397
theorem B22125149 : Blo 1941435 22125149 := bstep (se 3 (by rfl) ⟨4148465, by rfl⟩ : syracuseStep 22125149 = 8296931) B8296931
theorem B14750099 : Blo 1941435 14750099 := bstep (se 1 (by rfl) ⟨11062574, by rfl⟩ : syracuseStep 14750099 = 22125149) B22125149
theorem B9833399 : Blo 1941435 9833399 := bstep (se 1 (by rfl) ⟨7375049, by rfl⟩ : syracuseStep 9833399 = 14750099) B14750099
theorem B6555599 : Blo 1941435 6555599 := bstep (se 1 (by rfl) ⟨4916699, by rfl⟩ : syracuseStep 6555599 = 9833399) B9833399
theorem B4370399 : Blo 1941435 4370399 := bstep (se 1 (by rfl) ⟨3277799, by rfl⟩ : syracuseStep 4370399 = 6555599) B6555599
theorem B2913599 : Blo 1941435 2913599 := bstep (se 1 (by rfl) ⟨2185199, by rfl⟩ : syracuseStep 2913599 = 4370399) B4370399
theorem B1942399 : Blo 1941435 1942399 := bstep (se 1 (by rfl) ⟨1456799, by rfl⟩ : syracuseStep 1942399 = 2913599) B2913599
theorem B2913605 : Blo 1941435 2913605 := bbase (se 4 (by rfl) ⟨273150, by rfl⟩ : syracuseStep 2913605 = 546301) (by norm_num)
theorem B1942403 : Blo 1941435 1942403 := bstep (se 1 (by rfl) ⟨1456802, by rfl⟩ : syracuseStep 1942403 = 2913605) B2913605
theorem B3277813 : Blo 1941435 3277813 := bbase (se 5 (by rfl) ⟨153647, by rfl⟩ : syracuseStep 3277813 = 307295) (by norm_num)
theorem B4370417 : Blo 1941435 4370417 := bstep (se 2 (by rfl) ⟨1638906, by rfl⟩ : syracuseStep 4370417 = 3277813) B3277813
theorem B2913611 : Blo 1941435 2913611 := bstep (se 1 (by rfl) ⟨2185208, by rfl⟩ : syracuseStep 2913611 = 4370417) B4370417
theorem B1942407 : Blo 1941435 1942407 := bstep (se 1 (by rfl) ⟨1456805, by rfl⟩ : syracuseStep 1942407 = 2913611) B2913611
theorem B2185213 : Blo 1941435 2185213 := bbase (se 3 (by rfl) ⟨409727, by rfl⟩ : syracuseStep 2185213 = 819455) (by norm_num)
theorem B2913617 : Blo 1941435 2913617 := bstep (se 2 (by rfl) ⟨1092606, by rfl⟩ : syracuseStep 2913617 = 2185213) B2185213
theorem B1942411 : Blo 1941435 1942411 := bstep (se 1 (by rfl) ⟨1456808, by rfl⟩ : syracuseStep 1942411 = 2913617) B2913617
theorem B6555653 : Blo 1941435 6555653 := bbase (se 4 (by rfl) ⟨614592, by rfl⟩ : syracuseStep 6555653 = 1229185) (by norm_num)
theorem B4370435 : Blo 1941435 4370435 := bstep (se 1 (by rfl) ⟨3277826, by rfl⟩ : syracuseStep 4370435 = 6555653) B6555653
theorem B2913623 : Blo 1941435 2913623 := bstep (se 1 (by rfl) ⟨2185217, by rfl⟩ : syracuseStep 2913623 = 4370435) B4370435
theorem B1942415 : Blo 1941435 1942415 := bstep (se 1 (by rfl) ⟨1456811, by rfl⟩ : syracuseStep 1942415 = 2913623) B2913623
theorem B2913629 : Blo 1941435 2913629 := bbase (se 3 (by rfl) ⟨546305, by rfl⟩ : syracuseStep 2913629 = 1092611) (by norm_num)
theorem B1942419 : Blo 1941435 1942419 := bstep (se 1 (by rfl) ⟨1456814, by rfl⟩ : syracuseStep 1942419 = 2913629) B2913629
theorem B4370453 : Blo 1941435 4370453 := bbase (se 6 (by rfl) ⟨102432, by rfl⟩ : syracuseStep 4370453 = 204865) (by norm_num)
theorem B2913635 : Blo 1941435 2913635 := bstep (se 1 (by rfl) ⟨2185226, by rfl⟩ : syracuseStep 2913635 = 4370453) B4370453
theorem B1942423 : Blo 1941435 1942423 := bstep (se 1 (by rfl) ⟨1456817, by rfl⟩ : syracuseStep 1942423 = 2913635) B2913635
theorem B7375157 : Blo 1941435 7375157 := bbase (se 5 (by rfl) ⟨345710, by rfl⟩ : syracuseStep 7375157 = 691421) (by norm_num)
theorem B4916771 : Blo 1941435 4916771 := bstep (se 1 (by rfl) ⟨3687578, by rfl⟩ : syracuseStep 4916771 = 7375157) B7375157
theorem B3277847 : Blo 1941435 3277847 := bstep (se 1 (by rfl) ⟨2458385, by rfl⟩ : syracuseStep 3277847 = 4916771) B4916771
theorem B2185231 : Blo 1941435 2185231 := bstep (se 1 (by rfl) ⟨1638923, by rfl⟩ : syracuseStep 2185231 = 3277847) B3277847
theorem B2913641 : Blo 1941435 2913641 := bstep (se 2 (by rfl) ⟨1092615, by rfl⟩ : syracuseStep 2913641 = 2185231) B2185231
theorem B1942427 : Blo 1941435 1942427 := bstep (se 1 (by rfl) ⟨1456820, by rfl⟩ : syracuseStep 1942427 = 2913641) B2913641
theorem B2491933 : Blo 1941435 2491933 := bbase (se 3 (by rfl) ⟨467237, by rfl⟩ : syracuseStep 2491933 = 934475) (by norm_num)
theorem B3322577 : Blo 1941435 3322577 := bstep (se 2 (by rfl) ⟨1245966, by rfl⟩ : syracuseStep 3322577 = 2491933) B2491933
theorem B8860205 : Blo 1941435 8860205 := bstep (se 3 (by rfl) ⟨1661288, by rfl⟩ : syracuseStep 8860205 = 3322577) B3322577
theorem B5906803 : Blo 1941435 5906803 := bstep (se 1 (by rfl) ⟨4430102, by rfl⟩ : syracuseStep 5906803 = 8860205) B8860205
theorem B7875737 : Blo 1941435 7875737 := bstep (se 2 (by rfl) ⟨2953401, by rfl⟩ : syracuseStep 7875737 = 5906803) B5906803
theorem B5250491 : Blo 1941435 5250491 := bstep (se 1 (by rfl) ⟨3937868, by rfl⟩ : syracuseStep 5250491 = 7875737) B7875737
theorem B3500327 : Blo 1941435 3500327 := bstep (se 1 (by rfl) ⟨2625245, by rfl⟩ : syracuseStep 3500327 = 5250491) B5250491
theorem B2333551 : Blo 1941435 2333551 := bstep (se 1 (by rfl) ⟨1750163, by rfl⟩ : syracuseStep 2333551 = 3500327) B3500327
theorem B3111401 : Blo 1941435 3111401 := bstep (se 2 (by rfl) ⟨1166775, by rfl⟩ : syracuseStep 3111401 = 2333551) B2333551
theorem B2074267 : Blo 1941435 2074267 := bstep (se 1 (by rfl) ⟨1555700, by rfl⟩ : syracuseStep 2074267 = 3111401) B3111401
theorem B11062757 : Blo 1941435 11062757 := bstep (se 4 (by rfl) ⟨1037133, by rfl⟩ : syracuseStep 11062757 = 2074267) B2074267
theorem B7375171 : Blo 1941435 7375171 := bstep (se 1 (by rfl) ⟨5531378, by rfl⟩ : syracuseStep 7375171 = 11062757) B11062757
theorem B9833561 : Blo 1941435 9833561 := bstep (se 2 (by rfl) ⟨3687585, by rfl⟩ : syracuseStep 9833561 = 7375171) B7375171
theorem B6555707 : Blo 1941435 6555707 := bstep (se 1 (by rfl) ⟨4916780, by rfl⟩ : syracuseStep 6555707 = 9833561) B9833561
theorem B4370471 : Blo 1941435 4370471 := bstep (se 1 (by rfl) ⟨3277853, by rfl⟩ : syracuseStep 4370471 = 6555707) B6555707
theorem B2913647 : Blo 1941435 2913647 := bstep (se 1 (by rfl) ⟨2185235, by rfl⟩ : syracuseStep 2913647 = 4370471) B4370471
theorem B1942431 : Blo 1941435 1942431 := bstep (se 1 (by rfl) ⟨1456823, by rfl⟩ : syracuseStep 1942431 = 2913647) B2913647
theorem B2913653 : Blo 1941435 2913653 := bbase (se 5 (by rfl) ⟨136577, by rfl⟩ : syracuseStep 2913653 = 273155) (by norm_num)
theorem B1942435 : Blo 1941435 1942435 := bstep (se 1 (by rfl) ⟨1456826, by rfl⟩ : syracuseStep 1942435 = 2913653) B2913653
theorem B2765701 : Blo 1941435 2765701 := bbase (se 4 (by rfl) ⟨259284, by rfl⟩ : syracuseStep 2765701 = 518569) (by norm_num)
theorem B3687601 : Blo 1941435 3687601 := bstep (se 2 (by rfl) ⟨1382850, by rfl⟩ : syracuseStep 3687601 = 2765701) B2765701
theorem B4916801 : Blo 1941435 4916801 := bstep (se 2 (by rfl) ⟨1843800, by rfl⟩ : syracuseStep 4916801 = 3687601) B3687601
theorem B3277867 : Blo 1941435 3277867 := bstep (se 1 (by rfl) ⟨2458400, by rfl⟩ : syracuseStep 3277867 = 4916801) B4916801
theorem B4370489 : Blo 1941435 4370489 := bstep (se 2 (by rfl) ⟨1638933, by rfl⟩ : syracuseStep 4370489 = 3277867) B3277867
theorem B2913659 : Blo 1941435 2913659 := bstep (se 1 (by rfl) ⟨2185244, by rfl⟩ : syracuseStep 2913659 = 4370489) B4370489
theorem B1942439 : Blo 1941435 1942439 := bstep (se 1 (by rfl) ⟨1456829, by rfl⟩ : syracuseStep 1942439 = 2913659) B2913659
theorem B2185249 : Blo 1941435 2185249 := bbase (se 2 (by rfl) ⟨819468, by rfl⟩ : syracuseStep 2185249 = 1638937) (by norm_num)
theorem B2913665 : Blo 1941435 2913665 := bstep (se 2 (by rfl) ⟨1092624, by rfl⟩ : syracuseStep 2913665 = 2185249) B2185249
theorem B1942443 : Blo 1941435 1942443 := bstep (se 1 (by rfl) ⟨1456832, by rfl⟩ : syracuseStep 1942443 = 2913665) B2913665
theorem B4916821 : Blo 1941435 4916821 := bbase (se 8 (by rfl) ⟨28809, by rfl⟩ : syracuseStep 4916821 = 57619) (by norm_num)
theorem B6555761 : Blo 1941435 6555761 := bstep (se 2 (by rfl) ⟨2458410, by rfl⟩ : syracuseStep 6555761 = 4916821) B4916821
theorem B4370507 : Blo 1941435 4370507 := bstep (se 1 (by rfl) ⟨3277880, by rfl⟩ : syracuseStep 4370507 = 6555761) B6555761
theorem B2913671 : Blo 1941435 2913671 := bstep (se 1 (by rfl) ⟨2185253, by rfl⟩ : syracuseStep 2913671 = 4370507) B4370507
theorem B1942447 : Blo 1941435 1942447 := bstep (se 1 (by rfl) ⟨1456835, by rfl⟩ : syracuseStep 1942447 = 2913671) B2913671
theorem B2913677 : Blo 1941435 2913677 := bbase (se 3 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 2913677 = 1092629) (by norm_num)
theorem B1942451 : Blo 1941435 1942451 := bstep (se 1 (by rfl) ⟨1456838, by rfl⟩ : syracuseStep 1942451 = 2913677) B2913677
theorem B4370525 : Blo 1941435 4370525 := bbase (se 3 (by rfl) ⟨819473, by rfl⟩ : syracuseStep 4370525 = 1638947) (by norm_num)
theorem B2913683 : Blo 1941435 2913683 := bstep (se 1 (by rfl) ⟨2185262, by rfl⟩ : syracuseStep 2913683 = 4370525) B4370525
theorem B1942455 : Blo 1941435 1942455 := bstep (se 1 (by rfl) ⟨1456841, by rfl⟩ : syracuseStep 1942455 = 2913683) B2913683
theorem B3277901 : Blo 1941435 3277901 := bbase (se 3 (by rfl) ⟨614606, by rfl⟩ : syracuseStep 3277901 = 1229213) (by norm_num)
theorem B2185267 : Blo 1941435 2185267 := bstep (se 1 (by rfl) ⟨1638950, by rfl⟩ : syracuseStep 2185267 = 3277901) B3277901
theorem B2913689 : Blo 1941435 2913689 := bstep (se 2 (by rfl) ⟨1092633, by rfl⟩ : syracuseStep 2913689 = 2185267) B2185267
theorem B1942459 : Blo 1941435 1942459 := bstep (se 1 (by rfl) ⟨1456844, by rfl⟩ : syracuseStep 1942459 = 2913689) B2913689
theorem B3788957 : Blo 1941435 3788957 := bbase (se 3 (by rfl) ⟨710429, by rfl⟩ : syracuseStep 3788957 = 1420859) (by norm_num)
theorem B2525971 : Blo 1941435 2525971 := bstep (se 1 (by rfl) ⟨1894478, by rfl⟩ : syracuseStep 2525971 = 3788957) B3788957
theorem B215549525 : Blo 1941435 215549525 := bstep (se 8 (by rfl) ⟨1262985, by rfl⟩ : syracuseStep 215549525 = 2525971) B2525971
theorem B143699683 : Blo 1941435 143699683 := bstep (se 1 (by rfl) ⟨107774762, by rfl⟩ : syracuseStep 143699683 = 215549525) B215549525
theorem B191599577 : Blo 1941435 191599577 := bstep (se 2 (by rfl) ⟨71849841, by rfl⟩ : syracuseStep 191599577 = 143699683) B143699683
theorem B127733051 : Blo 1941435 127733051 := bstep (se 1 (by rfl) ⟨95799788, by rfl⟩ : syracuseStep 127733051 = 191599577) B191599577
theorem B340621469 : Blo 1941435 340621469 := bstep (se 3 (by rfl) ⟨63866525, by rfl⟩ : syracuseStep 340621469 = 127733051) B127733051
theorem B227080979 : Blo 1941435 227080979 := bstep (se 1 (by rfl) ⟨170310734, by rfl⟩ : syracuseStep 227080979 = 340621469) B340621469
theorem B151387319 : Blo 1941435 151387319 := bstep (se 1 (by rfl) ⟨113540489, by rfl⟩ : syracuseStep 151387319 = 227080979) B227080979
theorem B100924879 : Blo 1941435 100924879 := bstep (se 1 (by rfl) ⟨75693659, by rfl⟩ : syracuseStep 100924879 = 151387319) B151387319
theorem B134566505 : Blo 1941435 134566505 := bstep (se 2 (by rfl) ⟨50462439, by rfl⟩ : syracuseStep 134566505 = 100924879) B100924879
theorem B89711003 : Blo 1941435 89711003 := bstep (se 1 (by rfl) ⟨67283252, by rfl⟩ : syracuseStep 89711003 = 134566505) B134566505
theorem B59807335 : Blo 1941435 59807335 := bstep (se 1 (by rfl) ⟨44855501, by rfl⟩ : syracuseStep 59807335 = 89711003) B89711003
theorem B79743113 : Blo 1941435 79743113 := bstep (se 2 (by rfl) ⟨29903667, by rfl⟩ : syracuseStep 79743113 = 59807335) B59807335
theorem B53162075 : Blo 1941435 53162075 := bstep (se 1 (by rfl) ⟨39871556, by rfl⟩ : syracuseStep 53162075 = 79743113) B79743113
theorem B35441383 : Blo 1941435 35441383 := bstep (se 1 (by rfl) ⟨26581037, by rfl⟩ : syracuseStep 35441383 = 53162075) B53162075
theorem B47255177 : Blo 1941435 47255177 := bstep (se 2 (by rfl) ⟨17720691, by rfl⟩ : syracuseStep 47255177 = 35441383) B35441383
theorem B31503451 : Blo 1941435 31503451 := bstep (se 1 (by rfl) ⟨23627588, by rfl⟩ : syracuseStep 31503451 = 47255177) B47255177
theorem B42004601 : Blo 1941435 42004601 := bstep (se 2 (by rfl) ⟨15751725, by rfl⟩ : syracuseStep 42004601 = 31503451) B31503451
theorem B28003067 : Blo 1941435 28003067 := bstep (se 1 (by rfl) ⟨21002300, by rfl⟩ : syracuseStep 28003067 = 42004601) B42004601
theorem B18668711 : Blo 1941435 18668711 := bstep (se 1 (by rfl) ⟨14001533, by rfl⟩ : syracuseStep 18668711 = 28003067) B28003067
theorem B12445807 : Blo 1941435 12445807 := bstep (se 1 (by rfl) ⟨9334355, by rfl⟩ : syracuseStep 12445807 = 18668711) B18668711
theorem B16594409 : Blo 1941435 16594409 := bstep (se 2 (by rfl) ⟨6222903, by rfl⟩ : syracuseStep 16594409 = 12445807) B12445807
theorem B11062939 : Blo 1941435 11062939 := bstep (se 1 (by rfl) ⟨8297204, by rfl⟩ : syracuseStep 11062939 = 16594409) B16594409
theorem B14750585 : Blo 1941435 14750585 := bstep (se 2 (by rfl) ⟨5531469, by rfl⟩ : syracuseStep 14750585 = 11062939) B11062939
theorem B9833723 : Blo 1941435 9833723 := bstep (se 1 (by rfl) ⟨7375292, by rfl⟩ : syracuseStep 9833723 = 14750585) B14750585
theorem B6555815 : Blo 1941435 6555815 := bstep (se 1 (by rfl) ⟨4916861, by rfl⟩ : syracuseStep 6555815 = 9833723) B9833723
theorem B4370543 : Blo 1941435 4370543 := bstep (se 1 (by rfl) ⟨3277907, by rfl⟩ : syracuseStep 4370543 = 6555815) B6555815
theorem B2913695 : Blo 1941435 2913695 := bstep (se 1 (by rfl) ⟨2185271, by rfl⟩ : syracuseStep 2913695 = 4370543) B4370543
theorem B1942463 : Blo 1941435 1942463 := bstep (se 1 (by rfl) ⟨1456847, by rfl⟩ : syracuseStep 1942463 = 2913695) B2913695
theorem B2913701 : Blo 1941435 2913701 := bbase (se 4 (by rfl) ⟨273159, by rfl⟩ : syracuseStep 2913701 = 546319) (by norm_num)
theorem B1942467 : Blo 1941435 1942467 := bstep (se 1 (by rfl) ⟨1456850, by rfl⟩ : syracuseStep 1942467 = 2913701) B2913701
theorem B2458441 : Blo 1941435 2458441 := bbase (se 2 (by rfl) ⟨921915, by rfl⟩ : syracuseStep 2458441 = 1843831) (by norm_num)
theorem B3277921 : Blo 1941435 3277921 := bstep (se 2 (by rfl) ⟨1229220, by rfl⟩ : syracuseStep 3277921 = 2458441) B2458441
theorem B4370561 : Blo 1941435 4370561 := bstep (se 2 (by rfl) ⟨1638960, by rfl⟩ : syracuseStep 4370561 = 3277921) B3277921
theorem B2913707 : Blo 1941435 2913707 := bstep (se 1 (by rfl) ⟨2185280, by rfl⟩ : syracuseStep 2913707 = 4370561) B4370561
theorem B1942471 : Blo 1941435 1942471 := bstep (se 1 (by rfl) ⟨1456853, by rfl⟩ : syracuseStep 1942471 = 2913707) B2913707
theorem B2185285 : Blo 1941435 2185285 := bbase (se 4 (by rfl) ⟨204870, by rfl⟩ : syracuseStep 2185285 = 409741) (by norm_num)
theorem B2913713 : Blo 1941435 2913713 := bstep (se 2 (by rfl) ⟨1092642, by rfl⟩ : syracuseStep 2913713 = 2185285) B2185285
theorem B1942475 : Blo 1941435 1942475 := bstep (se 1 (by rfl) ⟨1456856, by rfl⟩ : syracuseStep 1942475 = 2913713) B2913713
theorem B3687677 : Blo 1941435 3687677 := bbase (se 3 (by rfl) ⟨691439, by rfl⟩ : syracuseStep 3687677 = 1382879) (by norm_num)
theorem B2458451 : Blo 1941435 2458451 := bstep (se 1 (by rfl) ⟨1843838, by rfl⟩ : syracuseStep 2458451 = 3687677) B3687677
theorem B6555869 : Blo 1941435 6555869 := bstep (se 3 (by rfl) ⟨1229225, by rfl⟩ : syracuseStep 6555869 = 2458451) B2458451
theorem B4370579 : Blo 1941435 4370579 := bstep (se 1 (by rfl) ⟨3277934, by rfl⟩ : syracuseStep 4370579 = 6555869) B6555869
theorem B2913719 : Blo 1941435 2913719 := bstep (se 1 (by rfl) ⟨2185289, by rfl⟩ : syracuseStep 2913719 = 4370579) B4370579
theorem B1942479 : Blo 1941435 1942479 := bstep (se 1 (by rfl) ⟨1456859, by rfl⟩ : syracuseStep 1942479 = 2913719) B2913719
theorem B2913725 : Blo 1941435 2913725 := bbase (se 3 (by rfl) ⟨546323, by rfl⟩ : syracuseStep 2913725 = 1092647) (by norm_num)
theorem B1942483 : Blo 1941435 1942483 := bstep (se 1 (by rfl) ⟨1456862, by rfl⟩ : syracuseStep 1942483 = 2913725) B2913725
theorem B4370597 : Blo 1941435 4370597 := bbase (se 4 (by rfl) ⟨409743, by rfl⟩ : syracuseStep 4370597 = 819487) (by norm_num)
theorem B2913731 : Blo 1941435 2913731 := bstep (se 1 (by rfl) ⟨2185298, by rfl⟩ : syracuseStep 2913731 = 4370597) B4370597
theorem B1942487 : Blo 1941435 1942487 := bstep (se 1 (by rfl) ⟨1456865, by rfl⟩ : syracuseStep 1942487 = 2913731) B2913731
theorem B4916933 : Blo 1941435 4916933 := bbase (se 4 (by rfl) ⟨460962, by rfl⟩ : syracuseStep 4916933 = 921925) (by norm_num)
theorem B3277955 : Blo 1941435 3277955 := bstep (se 1 (by rfl) ⟨2458466, by rfl⟩ : syracuseStep 3277955 = 4916933) B4916933
theorem B2185303 : Blo 1941435 2185303 := bstep (se 1 (by rfl) ⟨1638977, by rfl⟩ : syracuseStep 2185303 = 3277955) B3277955
theorem B2913737 : Blo 1941435 2913737 := bstep (se 2 (by rfl) ⟨1092651, by rfl⟩ : syracuseStep 2913737 = 2185303) B2185303
theorem B1942491 : Blo 1941435 1942491 := bstep (se 1 (by rfl) ⟨1456868, by rfl⟩ : syracuseStep 1942491 = 2913737) B2913737
theorem B8981381 : Blo 1941435 8981381 := bbase (se 4 (by rfl) ⟨842004, by rfl⟩ : syracuseStep 8981381 = 1684009) (by norm_num)
theorem B23950349 : Blo 1941435 23950349 := bstep (se 3 (by rfl) ⟨4490690, by rfl⟩ : syracuseStep 23950349 = 8981381) B8981381
theorem B15966899 : Blo 1941435 15966899 := bstep (se 1 (by rfl) ⟨11975174, by rfl⟩ : syracuseStep 15966899 = 23950349) B23950349
theorem B10644599 : Blo 1941435 10644599 := bstep (se 1 (by rfl) ⟨7983449, by rfl⟩ : syracuseStep 10644599 = 15966899) B15966899
theorem B28385597 : Blo 1941435 28385597 := bstep (se 3 (by rfl) ⟨5322299, by rfl⟩ : syracuseStep 28385597 = 10644599) B10644599
theorem B75694925 : Blo 1941435 75694925 := bstep (se 3 (by rfl) ⟨14192798, by rfl⟩ : syracuseStep 75694925 = 28385597) B28385597
theorem B50463283 : Blo 1941435 50463283 := bstep (se 1 (by rfl) ⟨37847462, by rfl⟩ : syracuseStep 50463283 = 75694925) B75694925
theorem B67284377 : Blo 1941435 67284377 := bstep (se 2 (by rfl) ⟨25231641, by rfl⟩ : syracuseStep 67284377 = 50463283) B50463283
theorem B44856251 : Blo 1941435 44856251 := bstep (se 1 (by rfl) ⟨33642188, by rfl⟩ : syracuseStep 44856251 = 67284377) B67284377
theorem B29904167 : Blo 1941435 29904167 := bstep (se 1 (by rfl) ⟨22428125, by rfl⟩ : syracuseStep 29904167 = 44856251) B44856251
theorem B79744445 : Blo 1941435 79744445 := bstep (se 3 (by rfl) ⟨14952083, by rfl⟩ : syracuseStep 79744445 = 29904167) B29904167
theorem B53162963 : Blo 1941435 53162963 := bstep (se 1 (by rfl) ⟨39872222, by rfl⟩ : syracuseStep 53162963 = 79744445) B79744445
theorem B35441975 : Blo 1941435 35441975 := bstep (se 1 (by rfl) ⟨26581481, by rfl⟩ : syracuseStep 35441975 = 53162963) B53162963
theorem B23627983 : Blo 1941435 23627983 := bstep (se 1 (by rfl) ⟨17720987, by rfl⟩ : syracuseStep 23627983 = 35441975) B35441975
theorem B31503977 : Blo 1941435 31503977 := bstep (se 2 (by rfl) ⟨11813991, by rfl⟩ : syracuseStep 31503977 = 23627983) B23627983
theorem B21002651 : Blo 1941435 21002651 := bstep (se 1 (by rfl) ⟨15751988, by rfl⟩ : syracuseStep 21002651 = 31503977) B31503977
theorem B14001767 : Blo 1941435 14001767 := bstep (se 1 (by rfl) ⟨10501325, by rfl⟩ : syracuseStep 14001767 = 21002651) B21002651
theorem B9334511 : Blo 1941435 9334511 := bstep (se 1 (by rfl) ⟨7000883, by rfl⟩ : syracuseStep 9334511 = 14001767) B14001767
theorem B6223007 : Blo 1941435 6223007 := bstep (se 1 (by rfl) ⟨4667255, by rfl⟩ : syracuseStep 6223007 = 9334511) B9334511
theorem B4148671 : Blo 1941435 4148671 := bstep (se 1 (by rfl) ⟨3111503, by rfl⟩ : syracuseStep 4148671 = 6223007) B6223007
theorem B5531561 : Blo 1941435 5531561 := bstep (se 2 (by rfl) ⟨2074335, by rfl⟩ : syracuseStep 5531561 = 4148671) B4148671
theorem B3687707 : Blo 1941435 3687707 := bstep (se 1 (by rfl) ⟨2765780, by rfl⟩ : syracuseStep 3687707 = 5531561) B5531561
theorem B9833885 : Blo 1941435 9833885 := bstep (se 3 (by rfl) ⟨1843853, by rfl⟩ : syracuseStep 9833885 = 3687707) B3687707
theorem B6555923 : Blo 1941435 6555923 := bstep (se 1 (by rfl) ⟨4916942, by rfl⟩ : syracuseStep 6555923 = 9833885) B9833885
theorem B4370615 : Blo 1941435 4370615 := bstep (se 1 (by rfl) ⟨3277961, by rfl⟩ : syracuseStep 4370615 = 6555923) B6555923
theorem B2913743 : Blo 1941435 2913743 := bstep (se 1 (by rfl) ⟨2185307, by rfl⟩ : syracuseStep 2913743 = 4370615) B4370615
theorem B1942495 : Blo 1941435 1942495 := bstep (se 1 (by rfl) ⟨1456871, by rfl⟩ : syracuseStep 1942495 = 2913743) B2913743
theorem B2913749 : Blo 1941435 2913749 := bbase (se 7 (by rfl) ⟨34145, by rfl⟩ : syracuseStep 2913749 = 68291) (by norm_num)
theorem B1942499 : Blo 1941435 1942499 := bstep (se 1 (by rfl) ⟨1456874, by rfl⟩ : syracuseStep 1942499 = 2913749) B2913749
theorem B7375445 : Blo 1941435 7375445 := bbase (se 8 (by rfl) ⟨43215, by rfl⟩ : syracuseStep 7375445 = 86431) (by norm_num)
theorem B4916963 : Blo 1941435 4916963 := bstep (se 1 (by rfl) ⟨3687722, by rfl⟩ : syracuseStep 4916963 = 7375445) B7375445
theorem B3277975 : Blo 1941435 3277975 := bstep (se 1 (by rfl) ⟨2458481, by rfl⟩ : syracuseStep 3277975 = 4916963) B4916963
theorem B4370633 : Blo 1941435 4370633 := bstep (se 2 (by rfl) ⟨1638987, by rfl⟩ : syracuseStep 4370633 = 3277975) B3277975
theorem B2913755 : Blo 1941435 2913755 := bstep (se 1 (by rfl) ⟨2185316, by rfl⟩ : syracuseStep 2913755 = 4370633) B4370633
theorem B1942503 : Blo 1941435 1942503 := bstep (se 1 (by rfl) ⟨1456877, by rfl⟩ : syracuseStep 1942503 = 2913755) B2913755
theorem B2185321 : Blo 1941435 2185321 := bbase (se 2 (by rfl) ⟨819495, by rfl⟩ : syracuseStep 2185321 = 1638991) (by norm_num)
theorem B2913761 : Blo 1941435 2913761 := bstep (se 2 (by rfl) ⟨1092660, by rfl⟩ : syracuseStep 2913761 = 2185321) B2185321
theorem B1942507 : Blo 1941435 1942507 := bstep (se 1 (by rfl) ⟨1456880, by rfl⟩ : syracuseStep 1942507 = 2913761) B2913761
theorem B4430285 : Blo 1941435 4430285 := bbase (se 3 (by rfl) ⟨830678, by rfl⟩ : syracuseStep 4430285 = 1661357) (by norm_num)
theorem B2953523 : Blo 1941435 2953523 := bstep (se 1 (by rfl) ⟨2215142, by rfl⟩ : syracuseStep 2953523 = 4430285) B4430285
theorem B7876061 : Blo 1941435 7876061 := bstep (se 3 (by rfl) ⟨1476761, by rfl⟩ : syracuseStep 7876061 = 2953523) B2953523
theorem B5250707 : Blo 1941435 5250707 := bstep (se 1 (by rfl) ⟨3938030, by rfl⟩ : syracuseStep 5250707 = 7876061) B7876061
theorem B3500471 : Blo 1941435 3500471 := bstep (se 1 (by rfl) ⟨2625353, by rfl⟩ : syracuseStep 3500471 = 5250707) B5250707
theorem B2333647 : Blo 1941435 2333647 := bstep (se 1 (by rfl) ⟨1750235, by rfl⟩ : syracuseStep 2333647 = 3500471) B3500471
theorem B3111529 : Blo 1941435 3111529 := bstep (se 2 (by rfl) ⟨1166823, by rfl⟩ : syracuseStep 3111529 = 2333647) B2333647
theorem B4148705 : Blo 1941435 4148705 := bstep (se 2 (by rfl) ⟨1555764, by rfl⟩ : syracuseStep 4148705 = 3111529) B3111529
theorem B11063213 : Blo 1941435 11063213 := bstep (se 3 (by rfl) ⟨2074352, by rfl⟩ : syracuseStep 11063213 = 4148705) B4148705
theorem B7375475 : Blo 1941435 7375475 := bstep (se 1 (by rfl) ⟨5531606, by rfl⟩ : syracuseStep 7375475 = 11063213) B11063213
theorem B4916983 : Blo 1941435 4916983 := bstep (se 1 (by rfl) ⟨3687737, by rfl⟩ : syracuseStep 4916983 = 7375475) B7375475
theorem B6555977 : Blo 1941435 6555977 := bstep (se 2 (by rfl) ⟨2458491, by rfl⟩ : syracuseStep 6555977 = 4916983) B4916983
theorem B4370651 : Blo 1941435 4370651 := bstep (se 1 (by rfl) ⟨3277988, by rfl⟩ : syracuseStep 4370651 = 6555977) B6555977
theorem B2913767 : Blo 1941435 2913767 := bstep (se 1 (by rfl) ⟨2185325, by rfl⟩ : syracuseStep 2913767 = 4370651) B4370651
theorem B1942511 : Blo 1941435 1942511 := bstep (se 1 (by rfl) ⟨1456883, by rfl⟩ : syracuseStep 1942511 = 2913767) B2913767
theorem B2913773 : Blo 1941435 2913773 := bbase (se 3 (by rfl) ⟨546332, by rfl⟩ : syracuseStep 2913773 = 1092665) (by norm_num)
theorem B1942515 : Blo 1941435 1942515 := bstep (se 1 (by rfl) ⟨1456886, by rfl⟩ : syracuseStep 1942515 = 2913773) B2913773
theorem B4370669 : Blo 1941435 4370669 := bbase (se 3 (by rfl) ⟨819500, by rfl⟩ : syracuseStep 4370669 = 1639001) (by norm_num)
theorem B2913779 : Blo 1941435 2913779 := bstep (se 1 (by rfl) ⟨2185334, by rfl⟩ : syracuseStep 2913779 = 4370669) B4370669
theorem B1942519 : Blo 1941435 1942519 := bstep (se 1 (by rfl) ⟨1456889, by rfl⟩ : syracuseStep 1942519 = 2913779) B2913779
theorem B2765821 : Blo 1941435 2765821 := bbase (se 3 (by rfl) ⟨518591, by rfl⟩ : syracuseStep 2765821 = 1037183) (by norm_num)
theorem B3687761 : Blo 1941435 3687761 := bstep (se 2 (by rfl) ⟨1382910, by rfl⟩ : syracuseStep 3687761 = 2765821) B2765821
theorem B2458507 : Blo 1941435 2458507 := bstep (se 1 (by rfl) ⟨1843880, by rfl⟩ : syracuseStep 2458507 = 3687761) B3687761
theorem B3278009 : Blo 1941435 3278009 := bstep (se 2 (by rfl) ⟨1229253, by rfl⟩ : syracuseStep 3278009 = 2458507) B2458507
theorem B2185339 : Blo 1941435 2185339 := bstep (se 1 (by rfl) ⟨1639004, by rfl⟩ : syracuseStep 2185339 = 3278009) B3278009
theorem B2913785 : Blo 1941435 2913785 := bstep (se 2 (by rfl) ⟨1092669, by rfl⟩ : syracuseStep 2913785 = 2185339) B2185339
theorem B1942523 : Blo 1941435 1942523 := bstep (se 1 (by rfl) ⟨1456892, by rfl⟩ : syracuseStep 1942523 = 2913785) B2913785
theorem B7000997 : Blo 1941435 7000997 := bbase (se 4 (by rfl) ⟨656343, by rfl⟩ : syracuseStep 7000997 = 1312687) (by norm_num)
theorem B74677301 : Blo 1941435 74677301 := bstep (se 5 (by rfl) ⟨3500498, by rfl⟩ : syracuseStep 74677301 = 7000997) B7000997
theorem B49784867 : Blo 1941435 49784867 := bstep (se 1 (by rfl) ⟨37338650, by rfl⟩ : syracuseStep 49784867 = 74677301) B74677301
theorem B33189911 : Blo 1941435 33189911 := bstep (se 1 (by rfl) ⟨24892433, by rfl⟩ : syracuseStep 33189911 = 49784867) B49784867
theorem B22126607 : Blo 1941435 22126607 := bstep (se 1 (by rfl) ⟨16594955, by rfl⟩ : syracuseStep 22126607 = 33189911) B33189911
theorem B14751071 : Blo 1941435 14751071 := bstep (se 1 (by rfl) ⟨11063303, by rfl⟩ : syracuseStep 14751071 = 22126607) B22126607
theorem B9834047 : Blo 1941435 9834047 := bstep (se 1 (by rfl) ⟨7375535, by rfl⟩ : syracuseStep 9834047 = 14751071) B14751071
theorem B6556031 : Blo 1941435 6556031 := bstep (se 1 (by rfl) ⟨4917023, by rfl⟩ : syracuseStep 6556031 = 9834047) B9834047
theorem B4370687 : Blo 1941435 4370687 := bstep (se 1 (by rfl) ⟨3278015, by rfl⟩ : syracuseStep 4370687 = 6556031) B6556031
theorem B2913791 : Blo 1941435 2913791 := bstep (se 1 (by rfl) ⟨2185343, by rfl⟩ : syracuseStep 2913791 = 4370687) B4370687
theorem B1942527 : Blo 1941435 1942527 := bstep (se 1 (by rfl) ⟨1456895, by rfl⟩ : syracuseStep 1942527 = 2913791) B2913791
theorem B2913797 : Blo 1941435 2913797 := bbase (se 4 (by rfl) ⟨273168, by rfl⟩ : syracuseStep 2913797 = 546337) (by norm_num)
theorem B1942531 : Blo 1941435 1942531 := bstep (se 1 (by rfl) ⟨1456898, by rfl⟩ : syracuseStep 1942531 = 2913797) B2913797
theorem B3278029 : Blo 1941435 3278029 := bbase (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) (by norm_num)
theorem B4370705 : Blo 1941435 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B2913803 : Blo 1941435 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B1942535 : Blo 1941435 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B2185357 : Blo 1941435 2185357 := bbase (se 3 (by rfl) ⟨409754, by rfl⟩ : syracuseStep 2185357 = 819509) (by norm_num)
theorem B2913809 : Blo 1941435 2913809 := bstep (se 2 (by rfl) ⟨1092678, by rfl⟩ : syracuseStep 2913809 = 2185357) B2185357
theorem B1942539 : Blo 1941435 1942539 := bstep (se 1 (by rfl) ⟨1456904, by rfl⟩ : syracuseStep 1942539 = 2913809) B2913809
theorem B6556085 : Blo 1941435 6556085 := bbase (se 5 (by rfl) ⟨307316, by rfl⟩ : syracuseStep 6556085 = 614633) (by norm_num)
theorem B4370723 : Blo 1941435 4370723 := bstep (se 1 (by rfl) ⟨3278042, by rfl⟩ : syracuseStep 4370723 = 6556085) B6556085
theorem B2913815 : Blo 1941435 2913815 := bstep (se 1 (by rfl) ⟨2185361, by rfl⟩ : syracuseStep 2913815 = 4370723) B4370723
theorem B1942543 : Blo 1941435 1942543 := bstep (se 1 (by rfl) ⟨1456907, by rfl⟩ : syracuseStep 1942543 = 2913815) B2913815
theorem B2913821 : Blo 1941435 2913821 := bbase (se 3 (by rfl) ⟨546341, by rfl⟩ : syracuseStep 2913821 = 1092683) (by norm_num)
theorem B1942547 : Blo 1941435 1942547 := bstep (se 1 (by rfl) ⟨1456910, by rfl⟩ : syracuseStep 1942547 = 2913821) B2913821
theorem B4370741 : Blo 1941435 4370741 := bbase (se 5 (by rfl) ⟨204878, by rfl⟩ : syracuseStep 4370741 = 409757) (by norm_num)
theorem B2913827 : Blo 1941435 2913827 := bstep (se 1 (by rfl) ⟨2185370, by rfl⟩ : syracuseStep 2913827 = 4370741) B4370741
theorem B1942551 : Blo 1941435 1942551 := bstep (se 1 (by rfl) ⟨1456913, by rfl⟩ : syracuseStep 1942551 = 2913827) B2913827
theorem B35517205 : Blo 1941435 35517205 := bbase (se 6 (by rfl) ⟨832434, by rfl⟩ : syracuseStep 35517205 = 1664869) (by norm_num)
theorem B47356273 : Blo 1941435 47356273 := bstep (se 2 (by rfl) ⟨17758602, by rfl⟩ : syracuseStep 47356273 = 35517205) B35517205
theorem B63141697 : Blo 1941435 63141697 := bstep (se 2 (by rfl) ⟨23678136, by rfl⟩ : syracuseStep 63141697 = 47356273) B47356273
theorem B84188929 : Blo 1941435 84188929 := bstep (se 2 (by rfl) ⟨31570848, by rfl⟩ : syracuseStep 84188929 = 63141697) B63141697
theorem B112251905 : Blo 1941435 112251905 := bstep (se 2 (by rfl) ⟨42094464, by rfl⟩ : syracuseStep 112251905 = 84188929) B84188929
theorem B74834603 : Blo 1941435 74834603 := bstep (se 1 (by rfl) ⟨56125952, by rfl⟩ : syracuseStep 74834603 = 112251905) B112251905
theorem B49889735 : Blo 1941435 49889735 := bstep (se 1 (by rfl) ⟨37417301, by rfl⟩ : syracuseStep 49889735 = 74834603) B74834603
theorem B33259823 : Blo 1941435 33259823 := bstep (se 1 (by rfl) ⟨24944867, by rfl⟩ : syracuseStep 33259823 = 49889735) B49889735
theorem B22173215 : Blo 1941435 22173215 := bstep (se 1 (by rfl) ⟨16629911, by rfl⟩ : syracuseStep 22173215 = 33259823) B33259823
theorem B59128573 : Blo 1941435 59128573 := bstep (se 3 (by rfl) ⟨11086607, by rfl⟩ : syracuseStep 59128573 = 22173215) B22173215
theorem B1261409557 : Blo 1941435 1261409557 := bstep (se 6 (by rfl) ⟨29564286, by rfl⟩ : syracuseStep 1261409557 = 59128573) B59128573
theorem B1681879409 : Blo 1941435 1681879409 := bstep (se 2 (by rfl) ⟨630704778, by rfl⟩ : syracuseStep 1681879409 = 1261409557) B1261409557
theorem B1121252939 : Blo 1941435 1121252939 := bstep (se 1 (by rfl) ⟨840939704, by rfl⟩ : syracuseStep 1121252939 = 1681879409) B1681879409
theorem B747501959 : Blo 1941435 747501959 := bstep (se 1 (by rfl) ⟨560626469, by rfl⟩ : syracuseStep 747501959 = 1121252939) B1121252939
theorem B498334639 : Blo 1941435 498334639 := bstep (se 1 (by rfl) ⟨373750979, by rfl⟩ : syracuseStep 498334639 = 747501959) B747501959
theorem B664446185 : Blo 1941435 664446185 := bstep (se 2 (by rfl) ⟨249167319, by rfl⟩ : syracuseStep 664446185 = 498334639) B498334639
theorem B442964123 : Blo 1941435 442964123 := bstep (se 1 (by rfl) ⟨332223092, by rfl⟩ : syracuseStep 442964123 = 664446185) B664446185
theorem B295309415 : Blo 1941435 295309415 := bstep (se 1 (by rfl) ⟨221482061, by rfl⟩ : syracuseStep 295309415 = 442964123) B442964123
theorem B196872943 : Blo 1941435 196872943 := bstep (se 1 (by rfl) ⟨147654707, by rfl⟩ : syracuseStep 196872943 = 295309415) B295309415
theorem B262497257 : Blo 1941435 262497257 := bstep (se 2 (by rfl) ⟨98436471, by rfl⟩ : syracuseStep 262497257 = 196872943) B196872943
theorem B174998171 : Blo 1941435 174998171 := bstep (se 1 (by rfl) ⟨131248628, by rfl⟩ : syracuseStep 174998171 = 262497257) B262497257
theorem B116665447 : Blo 1941435 116665447 := bstep (se 1 (by rfl) ⟨87499085, by rfl⟩ : syracuseStep 116665447 = 174998171) B174998171
theorem B155553929 : Blo 1941435 155553929 := bstep (se 2 (by rfl) ⟨58332723, by rfl⟩ : syracuseStep 155553929 = 116665447) B116665447
theorem B103702619 : Blo 1941435 103702619 := bstep (se 1 (by rfl) ⟨77776964, by rfl⟩ : syracuseStep 103702619 = 155553929) B155553929
theorem B69135079 : Blo 1941435 69135079 := bstep (se 1 (by rfl) ⟨51851309, by rfl⟩ : syracuseStep 69135079 = 103702619) B103702619
theorem B92180105 : Blo 1941435 92180105 := bstep (se 2 (by rfl) ⟨34567539, by rfl⟩ : syracuseStep 92180105 = 69135079) B69135079
theorem B61453403 : Blo 1941435 61453403 := bstep (se 1 (by rfl) ⟨46090052, by rfl⟩ : syracuseStep 61453403 = 92180105) B92180105
theorem B40968935 : Blo 1941435 40968935 := bstep (se 1 (by rfl) ⟨30726701, by rfl⟩ : syracuseStep 40968935 = 61453403) B61453403
theorem B27312623 : Blo 1941435 27312623 := bstep (se 1 (by rfl) ⟨20484467, by rfl⟩ : syracuseStep 27312623 = 40968935) B40968935
theorem B18208415 : Blo 1941435 18208415 := bstep (se 1 (by rfl) ⟨13656311, by rfl⟩ : syracuseStep 18208415 = 27312623) B27312623
theorem B12138943 : Blo 1941435 12138943 := bstep (se 1 (by rfl) ⟨9104207, by rfl⟩ : syracuseStep 12138943 = 18208415) B18208415
theorem B16185257 : Blo 1941435 16185257 := bstep (se 2 (by rfl) ⟨6069471, by rfl⟩ : syracuseStep 16185257 = 12138943) B12138943
theorem B10790171 : Blo 1941435 10790171 := bstep (se 1 (by rfl) ⟨8092628, by rfl⟩ : syracuseStep 10790171 = 16185257) B16185257
theorem B7193447 : Blo 1941435 7193447 := bstep (se 1 (by rfl) ⟨5395085, by rfl⟩ : syracuseStep 7193447 = 10790171) B10790171
theorem B4795631 : Blo 1941435 4795631 := bstep (se 1 (by rfl) ⟨3596723, by rfl⟩ : syracuseStep 4795631 = 7193447) B7193447
theorem B3197087 : Blo 1941435 3197087 := bstep (se 1 (by rfl) ⟨2397815, by rfl⟩ : syracuseStep 3197087 = 4795631) B4795631
theorem B2131391 : Blo 1941435 2131391 := bstep (se 1 (by rfl) ⟨1598543, by rfl⟩ : syracuseStep 2131391 = 3197087) B3197087
theorem B5683709 : Blo 1941435 5683709 := bstep (se 3 (by rfl) ⟨1065695, by rfl⟩ : syracuseStep 5683709 = 2131391) B2131391
theorem B3789139 : Blo 1941435 3789139 := bstep (se 1 (by rfl) ⟨2841854, by rfl⟩ : syracuseStep 3789139 = 5683709) B5683709
theorem B5052185 : Blo 1941435 5052185 := bstep (se 2 (by rfl) ⟨1894569, by rfl⟩ : syracuseStep 5052185 = 3789139) B3789139
theorem B3368123 : Blo 1941435 3368123 := bstep (se 1 (by rfl) ⟨2526092, by rfl⟩ : syracuseStep 3368123 = 5052185) B5052185
theorem B2245415 : Blo 1941435 2245415 := bstep (se 1 (by rfl) ⟨1684061, by rfl⟩ : syracuseStep 2245415 = 3368123) B3368123
theorem B5987773 : Blo 1941435 5987773 := bstep (se 3 (by rfl) ⟨1122707, by rfl⟩ : syracuseStep 5987773 = 2245415) B2245415
theorem B7983697 : Blo 1941435 7983697 := bstep (se 2 (by rfl) ⟨2993886, by rfl⟩ : syracuseStep 7983697 = 5987773) B5987773
theorem B10644929 : Blo 1941435 10644929 := bstep (se 2 (by rfl) ⟨3991848, by rfl⟩ : syracuseStep 10644929 = 7983697) B7983697
theorem B7096619 : Blo 1941435 7096619 := bstep (se 1 (by rfl) ⟨5322464, by rfl⟩ : syracuseStep 7096619 = 10644929) B10644929
theorem B4731079 : Blo 1941435 4731079 := bstep (se 1 (by rfl) ⟨3548309, by rfl⟩ : syracuseStep 4731079 = 7096619) B7096619
theorem B6308105 : Blo 1941435 6308105 := bstep (se 2 (by rfl) ⟨2365539, by rfl⟩ : syracuseStep 6308105 = 4731079) B4731079
theorem B16821613 : Blo 1941435 16821613 := bstep (se 3 (by rfl) ⟨3154052, by rfl⟩ : syracuseStep 16821613 = 6308105) B6308105
theorem B89715269 : Blo 1941435 89715269 := bstep (se 4 (by rfl) ⟨8410806, by rfl⟩ : syracuseStep 89715269 = 16821613) B16821613
theorem B59810179 : Blo 1941435 59810179 := bstep (se 1 (by rfl) ⟨44857634, by rfl⟩ : syracuseStep 59810179 = 89715269) B89715269
theorem B79746905 : Blo 1941435 79746905 := bstep (se 2 (by rfl) ⟨29905089, by rfl⟩ : syracuseStep 79746905 = 59810179) B59810179
theorem B53164603 : Blo 1941435 53164603 := bstep (se 1 (by rfl) ⟨39873452, by rfl⟩ : syracuseStep 53164603 = 79746905) B79746905
theorem B70886137 : Blo 1941435 70886137 := bstep (se 2 (by rfl) ⟨26582301, by rfl⟩ : syracuseStep 70886137 = 53164603) B53164603
theorem B94514849 : Blo 1941435 94514849 := bstep (se 2 (by rfl) ⟨35443068, by rfl⟩ : syracuseStep 94514849 = 70886137) B70886137
theorem B63009899 : Blo 1941435 63009899 := bstep (se 1 (by rfl) ⟨47257424, by rfl⟩ : syracuseStep 63009899 = 94514849) B94514849
theorem B42006599 : Blo 1941435 42006599 := bstep (se 1 (by rfl) ⟨31504949, by rfl⟩ : syracuseStep 42006599 = 63009899) B63009899
theorem B28004399 : Blo 1941435 28004399 := bstep (se 1 (by rfl) ⟨21003299, by rfl⟩ : syracuseStep 28004399 = 42006599) B42006599
theorem B18669599 : Blo 1941435 18669599 := bstep (se 1 (by rfl) ⟨14002199, by rfl⟩ : syracuseStep 18669599 = 28004399) B28004399
theorem B12446399 : Blo 1941435 12446399 := bstep (se 1 (by rfl) ⟨9334799, by rfl⟩ : syracuseStep 12446399 = 18669599) B18669599
theorem B8297599 : Blo 1941435 8297599 := bstep (se 1 (by rfl) ⟨6223199, by rfl⟩ : syracuseStep 8297599 = 12446399) B12446399
theorem B11063465 : Blo 1941435 11063465 := bstep (se 2 (by rfl) ⟨4148799, by rfl⟩ : syracuseStep 11063465 = 8297599) B8297599
theorem B7375643 : Blo 1941435 7375643 := bstep (se 1 (by rfl) ⟨5531732, by rfl⟩ : syracuseStep 7375643 = 11063465) B11063465
theorem B4917095 : Blo 1941435 4917095 := bstep (se 1 (by rfl) ⟨3687821, by rfl⟩ : syracuseStep 4917095 = 7375643) B7375643
theorem B3278063 : Blo 1941435 3278063 := bstep (se 1 (by rfl) ⟨2458547, by rfl⟩ : syracuseStep 3278063 = 4917095) B4917095
theorem B2185375 : Blo 1941435 2185375 := bstep (se 1 (by rfl) ⟨1639031, by rfl⟩ : syracuseStep 2185375 = 3278063) B3278063
theorem B2913833 : Blo 1941435 2913833 := bstep (se 2 (by rfl) ⟨1092687, by rfl⟩ : syracuseStep 2913833 = 2185375) B2185375
theorem B1942555 : Blo 1941435 1942555 := bstep (se 1 (by rfl) ⟨1456916, by rfl⟩ : syracuseStep 1942555 = 2913833) B2913833
theorem B3154061 : Blo 1941435 3154061 := bbase (se 3 (by rfl) ⟨591386, by rfl⟩ : syracuseStep 3154061 = 1182773) (by norm_num)
theorem B2102707 : Blo 1941435 2102707 := bstep (se 1 (by rfl) ⟨1577030, by rfl⟩ : syracuseStep 2102707 = 3154061) B3154061
theorem B2803609 : Blo 1941435 2803609 := bstep (se 2 (by rfl) ⟨1051353, by rfl⟩ : syracuseStep 2803609 = 2102707) B2102707
theorem B3738145 : Blo 1941435 3738145 := bstep (se 2 (by rfl) ⟨1401804, by rfl⟩ : syracuseStep 3738145 = 2803609) B2803609
theorem B4984193 : Blo 1941435 4984193 := bstep (se 2 (by rfl) ⟨1869072, by rfl⟩ : syracuseStep 4984193 = 3738145) B3738145
theorem B3322795 : Blo 1941435 3322795 := bstep (se 1 (by rfl) ⟨2492096, by rfl⟩ : syracuseStep 3322795 = 4984193) B4984193
theorem B4430393 : Blo 1941435 4430393 := bstep (se 2 (by rfl) ⟨1661397, by rfl⟩ : syracuseStep 4430393 = 3322795) B3322795
theorem B2953595 : Blo 1941435 2953595 := bstep (se 1 (by rfl) ⟨2215196, by rfl⟩ : syracuseStep 2953595 = 4430393) B4430393
theorem B7876253 : Blo 1941435 7876253 := bstep (se 3 (by rfl) ⟨1476797, by rfl⟩ : syracuseStep 7876253 = 2953595) B2953595
theorem B5250835 : Blo 1941435 5250835 := bstep (se 1 (by rfl) ⟨3938126, by rfl⟩ : syracuseStep 5250835 = 7876253) B7876253
theorem B28004453 : Blo 1941435 28004453 := bstep (se 4 (by rfl) ⟨2625417, by rfl⟩ : syracuseStep 28004453 = 5250835) B5250835
theorem B18669635 : Blo 1941435 18669635 := bstep (se 1 (by rfl) ⟨14002226, by rfl⟩ : syracuseStep 18669635 = 28004453) B28004453
theorem B12446423 : Blo 1941435 12446423 := bstep (se 1 (by rfl) ⟨9334817, by rfl⟩ : syracuseStep 12446423 = 18669635) B18669635
theorem B8297615 : Blo 1941435 8297615 := bstep (se 1 (by rfl) ⟨6223211, by rfl⟩ : syracuseStep 8297615 = 12446423) B12446423
theorem B5531743 : Blo 1941435 5531743 := bstep (se 1 (by rfl) ⟨4148807, by rfl⟩ : syracuseStep 5531743 = 8297615) B8297615
theorem B7375657 : Blo 1941435 7375657 := bstep (se 2 (by rfl) ⟨2765871, by rfl⟩ : syracuseStep 7375657 = 5531743) B5531743
theorem B9834209 : Blo 1941435 9834209 := bstep (se 2 (by rfl) ⟨3687828, by rfl⟩ : syracuseStep 9834209 = 7375657) B7375657
theorem B6556139 : Blo 1941435 6556139 := bstep (se 1 (by rfl) ⟨4917104, by rfl⟩ : syracuseStep 6556139 = 9834209) B9834209
theorem B4370759 : Blo 1941435 4370759 := bstep (se 1 (by rfl) ⟨3278069, by rfl⟩ : syracuseStep 4370759 = 6556139) B6556139
theorem B2913839 : Blo 1941435 2913839 := bstep (se 1 (by rfl) ⟨2185379, by rfl⟩ : syracuseStep 2913839 = 4370759) B4370759
theorem B1942559 : Blo 1941435 1942559 := bstep (se 1 (by rfl) ⟨1456919, by rfl⟩ : syracuseStep 1942559 = 2913839) B2913839
theorem B2913845 : Blo 1941435 2913845 := bbase (se 5 (by rfl) ⟨136586, by rfl⟩ : syracuseStep 2913845 = 273173) (by norm_num)
theorem B1942563 : Blo 1941435 1942563 := bstep (se 1 (by rfl) ⟨1456922, by rfl⟩ : syracuseStep 1942563 = 2913845) B2913845
theorem B4917125 : Blo 1941435 4917125 := bbase (se 4 (by rfl) ⟨460980, by rfl⟩ : syracuseStep 4917125 = 921961) (by norm_num)
theorem B3278083 : Blo 1941435 3278083 := bstep (se 1 (by rfl) ⟨2458562, by rfl⟩ : syracuseStep 3278083 = 4917125) B4917125
theorem B4370777 : Blo 1941435 4370777 := bstep (se 2 (by rfl) ⟨1639041, by rfl⟩ : syracuseStep 4370777 = 3278083) B3278083
theorem B2913851 : Blo 1941435 2913851 := bstep (se 1 (by rfl) ⟨2185388, by rfl⟩ : syracuseStep 2913851 = 4370777) B4370777
theorem B1942567 : Blo 1941435 1942567 := bstep (se 1 (by rfl) ⟨1456925, by rfl⟩ : syracuseStep 1942567 = 2913851) B2913851
theorem B2185393 : Blo 1941435 2185393 := bbase (se 2 (by rfl) ⟨819522, by rfl⟩ : syracuseStep 2185393 = 1639045) (by norm_num)
theorem B2913857 : Blo 1941435 2913857 := bstep (se 2 (by rfl) ⟨1092696, by rfl⟩ : syracuseStep 2913857 = 2185393) B2185393
theorem B1942571 : Blo 1941435 1942571 := bstep (se 1 (by rfl) ⟨1456928, by rfl⟩ : syracuseStep 1942571 = 2913857) B2913857
theorem B2074421 : Blo 1941435 2074421 := bbase (se 5 (by rfl) ⟨97238, by rfl⟩ : syracuseStep 2074421 = 194477) (by norm_num)
theorem B5531789 : Blo 1941435 5531789 := bstep (se 3 (by rfl) ⟨1037210, by rfl⟩ : syracuseStep 5531789 = 2074421) B2074421
theorem B3687859 : Blo 1941435 3687859 := bstep (se 1 (by rfl) ⟨2765894, by rfl⟩ : syracuseStep 3687859 = 5531789) B5531789
theorem B4917145 : Blo 1941435 4917145 := bstep (se 2 (by rfl) ⟨1843929, by rfl⟩ : syracuseStep 4917145 = 3687859) B3687859
theorem B6556193 : Blo 1941435 6556193 := bstep (se 2 (by rfl) ⟨2458572, by rfl⟩ : syracuseStep 6556193 = 4917145) B4917145
theorem B4370795 : Blo 1941435 4370795 := bstep (se 1 (by rfl) ⟨3278096, by rfl⟩ : syracuseStep 4370795 = 6556193) B6556193
theorem B2913863 : Blo 1941435 2913863 := bstep (se 1 (by rfl) ⟨2185397, by rfl⟩ : syracuseStep 2913863 = 4370795) B4370795
theorem B1942575 : Blo 1941435 1942575 := bstep (se 1 (by rfl) ⟨1456931, by rfl⟩ : syracuseStep 1942575 = 2913863) B2913863
theorem B2913869 : Blo 1941435 2913869 := bbase (se 3 (by rfl) ⟨546350, by rfl⟩ : syracuseStep 2913869 = 1092701) (by norm_num)
theorem B1942579 : Blo 1941435 1942579 := bstep (se 1 (by rfl) ⟨1456934, by rfl⟩ : syracuseStep 1942579 = 2913869) B2913869
theorem B4370813 : Blo 1941435 4370813 := bbase (se 3 (by rfl) ⟨819527, by rfl⟩ : syracuseStep 4370813 = 1639055) (by norm_num)
theorem B2913875 : Blo 1941435 2913875 := bstep (se 1 (by rfl) ⟨2185406, by rfl⟩ : syracuseStep 2913875 = 4370813) B4370813
theorem B1942583 : Blo 1941435 1942583 := bstep (se 1 (by rfl) ⟨1456937, by rfl⟩ : syracuseStep 1942583 = 2913875) B2913875
theorem B3278117 : Blo 1941435 3278117 := bbase (se 4 (by rfl) ⟨307323, by rfl⟩ : syracuseStep 3278117 = 614647) (by norm_num)
theorem B2185411 : Blo 1941435 2185411 := bstep (se 1 (by rfl) ⟨1639058, by rfl⟩ : syracuseStep 2185411 = 3278117) B3278117
theorem B2913881 : Blo 1941435 2913881 := bstep (se 2 (by rfl) ⟨1092705, by rfl⟩ : syracuseStep 2913881 = 2185411) B2185411
theorem B1942587 : Blo 1941435 1942587 := bstep (se 1 (by rfl) ⟨1456940, by rfl⟩ : syracuseStep 1942587 = 2913881) B2913881
theorem B2765917 : Blo 1941435 2765917 := bbase (se 3 (by rfl) ⟨518609, by rfl⟩ : syracuseStep 2765917 = 1037219) (by norm_num)
theorem B14751557 : Blo 1941435 14751557 := bstep (se 4 (by rfl) ⟨1382958, by rfl⟩ : syracuseStep 14751557 = 2765917) B2765917
theorem B9834371 : Blo 1941435 9834371 := bstep (se 1 (by rfl) ⟨7375778, by rfl⟩ : syracuseStep 9834371 = 14751557) B14751557
theorem B6556247 : Blo 1941435 6556247 := bstep (se 1 (by rfl) ⟨4917185, by rfl⟩ : syracuseStep 6556247 = 9834371) B9834371
theorem B4370831 : Blo 1941435 4370831 := bstep (se 1 (by rfl) ⟨3278123, by rfl⟩ : syracuseStep 4370831 = 6556247) B6556247
theorem B2913887 : Blo 1941435 2913887 := bstep (se 1 (by rfl) ⟨2185415, by rfl⟩ : syracuseStep 2913887 = 4370831) B4370831
theorem B1942591 : Blo 1941435 1942591 := bstep (se 1 (by rfl) ⟨1456943, by rfl⟩ : syracuseStep 1942591 = 2913887) B2913887
theorem B2913893 : Blo 1941435 2913893 := bbase (se 4 (by rfl) ⟨273177, by rfl⟩ : syracuseStep 2913893 = 546355) (by norm_num)
theorem B1942595 : Blo 1941435 1942595 := bstep (se 1 (by rfl) ⟨1456946, by rfl⟩ : syracuseStep 1942595 = 2913893) B2913893
theorem B1969105 : Blo 1941435 1969105 := bbase (se 2 (by rfl) ⟨738414, by rfl⟩ : syracuseStep 1969105 = 1476829) (by norm_num)
theorem B2625473 : Blo 1941435 2625473 := bstep (se 2 (by rfl) ⟨984552, by rfl⟩ : syracuseStep 2625473 = 1969105) B1969105
theorem B7001261 : Blo 1941435 7001261 := bstep (se 3 (by rfl) ⟨1312736, by rfl⟩ : syracuseStep 7001261 = 2625473) B2625473
theorem B4667507 : Blo 1941435 4667507 := bstep (se 1 (by rfl) ⟨3500630, by rfl⟩ : syracuseStep 4667507 = 7001261) B7001261
theorem B3111671 : Blo 1941435 3111671 := bstep (se 1 (by rfl) ⟨2333753, by rfl⟩ : syracuseStep 3111671 = 4667507) B4667507
theorem B2074447 : Blo 1941435 2074447 := bstep (se 1 (by rfl) ⟨1555835, by rfl⟩ : syracuseStep 2074447 = 3111671) B3111671
theorem B2765929 : Blo 1941435 2765929 := bstep (se 2 (by rfl) ⟨1037223, by rfl⟩ : syracuseStep 2765929 = 2074447) B2074447
theorem B3687905 : Blo 1941435 3687905 := bstep (se 2 (by rfl) ⟨1382964, by rfl⟩ : syracuseStep 3687905 = 2765929) B2765929
theorem B2458603 : Blo 1941435 2458603 := bstep (se 1 (by rfl) ⟨1843952, by rfl⟩ : syracuseStep 2458603 = 3687905) B3687905
theorem B3278137 : Blo 1941435 3278137 := bstep (se 2 (by rfl) ⟨1229301, by rfl⟩ : syracuseStep 3278137 = 2458603) B2458603
theorem B4370849 : Blo 1941435 4370849 := bstep (se 2 (by rfl) ⟨1639068, by rfl⟩ : syracuseStep 4370849 = 3278137) B3278137
theorem B2913899 : Blo 1941435 2913899 := bstep (se 1 (by rfl) ⟨2185424, by rfl⟩ : syracuseStep 2913899 = 4370849) B4370849
theorem B1942599 : Blo 1941435 1942599 := bstep (se 1 (by rfl) ⟨1456949, by rfl⟩ : syracuseStep 1942599 = 2913899) B2913899
theorem B2185429 : Blo 1941435 2185429 := bbase (se 7 (by rfl) ⟨25610, by rfl⟩ : syracuseStep 2185429 = 51221) (by norm_num)
theorem B2913905 : Blo 1941435 2913905 := bstep (se 2 (by rfl) ⟨1092714, by rfl⟩ : syracuseStep 2913905 = 2185429) B2185429
theorem B1942603 : Blo 1941435 1942603 := bstep (se 1 (by rfl) ⟨1456952, by rfl⟩ : syracuseStep 1942603 = 2913905) B2913905
theorem B2458613 : Blo 1941435 2458613 := bbase (se 5 (by rfl) ⟨115247, by rfl⟩ : syracuseStep 2458613 = 230495) (by norm_num)
theorem B6556301 : Blo 1941435 6556301 := bstep (se 3 (by rfl) ⟨1229306, by rfl⟩ : syracuseStep 6556301 = 2458613) B2458613
theorem B4370867 : Blo 1941435 4370867 := bstep (se 1 (by rfl) ⟨3278150, by rfl⟩ : syracuseStep 4370867 = 6556301) B6556301
theorem B2913911 : Blo 1941435 2913911 := bstep (se 1 (by rfl) ⟨2185433, by rfl⟩ : syracuseStep 2913911 = 4370867) B4370867
theorem B1942607 : Blo 1941435 1942607 := bstep (se 1 (by rfl) ⟨1456955, by rfl⟩ : syracuseStep 1942607 = 2913911) B2913911
theorem B2913917 : Blo 1941435 2913917 := bbase (se 3 (by rfl) ⟨546359, by rfl⟩ : syracuseStep 2913917 = 1092719) (by norm_num)
theorem B1942611 : Blo 1941435 1942611 := bstep (se 1 (by rfl) ⟨1456958, by rfl⟩ : syracuseStep 1942611 = 2913917) B2913917
theorem B4370885 : Blo 1941435 4370885 := bbase (se 4 (by rfl) ⟨409770, by rfl⟩ : syracuseStep 4370885 = 819541) (by norm_num)
theorem B2913923 : Blo 1941435 2913923 := bstep (se 1 (by rfl) ⟨2185442, by rfl⟩ : syracuseStep 2913923 = 4370885) B4370885
theorem B1942615 : Blo 1941435 1942615 := bstep (se 1 (by rfl) ⟨1456961, by rfl⟩ : syracuseStep 1942615 = 2913923) B2913923
theorem B2333777 : Blo 1941435 2333777 := bbase (se 2 (by rfl) ⟨875166, by rfl⟩ : syracuseStep 2333777 = 1750333) (by norm_num)
theorem B6223405 : Blo 1941435 6223405 := bstep (se 3 (by rfl) ⟨1166888, by rfl⟩ : syracuseStep 6223405 = 2333777) B2333777
theorem B8297873 : Blo 1941435 8297873 := bstep (se 2 (by rfl) ⟨3111702, by rfl⟩ : syracuseStep 8297873 = 6223405) B6223405
theorem B5531915 : Blo 1941435 5531915 := bstep (se 1 (by rfl) ⟨4148936, by rfl⟩ : syracuseStep 5531915 = 8297873) B8297873
theorem B3687943 : Blo 1941435 3687943 := bstep (se 1 (by rfl) ⟨2765957, by rfl⟩ : syracuseStep 3687943 = 5531915) B5531915
theorem B4917257 : Blo 1941435 4917257 := bstep (se 2 (by rfl) ⟨1843971, by rfl⟩ : syracuseStep 4917257 = 3687943) B3687943
theorem B3278171 : Blo 1941435 3278171 := bstep (se 1 (by rfl) ⟨2458628, by rfl⟩ : syracuseStep 3278171 = 4917257) B4917257
theorem B2185447 : Blo 1941435 2185447 := bstep (se 1 (by rfl) ⟨1639085, by rfl⟩ : syracuseStep 2185447 = 3278171) B3278171
theorem B2913929 : Blo 1941435 2913929 := bstep (se 2 (by rfl) ⟨1092723, by rfl⟩ : syracuseStep 2913929 = 2185447) B2185447
theorem B1942619 : Blo 1941435 1942619 := bstep (se 1 (by rfl) ⟨1456964, by rfl⟩ : syracuseStep 1942619 = 2913929) B2913929
theorem B9834533 : Blo 1941435 9834533 := bbase (se 4 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 9834533 = 1843975) (by norm_num)
theorem B6556355 : Blo 1941435 6556355 := bstep (se 1 (by rfl) ⟨4917266, by rfl⟩ : syracuseStep 6556355 = 9834533) B9834533
theorem B4370903 : Blo 1941435 4370903 := bstep (se 1 (by rfl) ⟨3278177, by rfl⟩ : syracuseStep 4370903 = 6556355) B6556355
theorem B2913935 : Blo 1941435 2913935 := bstep (se 1 (by rfl) ⟨2185451, by rfl⟩ : syracuseStep 2913935 = 4370903) B4370903
theorem B1942623 : Blo 1941435 1942623 := bstep (se 1 (by rfl) ⟨1456967, by rfl⟩ : syracuseStep 1942623 = 2913935) B2913935
theorem B2913941 : Blo 1941435 2913941 := bbase (se 6 (by rfl) ⟨68295, by rfl⟩ : syracuseStep 2913941 = 136591) (by norm_num)
theorem B1942627 : Blo 1941435 1942627 := bstep (se 1 (by rfl) ⟨1456970, by rfl⟩ : syracuseStep 1942627 = 2913941) B2913941
theorem B8411141 : Blo 1941435 8411141 := bbase (se 4 (by rfl) ⟨788544, by rfl⟩ : syracuseStep 8411141 = 1577089) (by norm_num)
theorem B5607427 : Blo 1941435 5607427 := bstep (se 1 (by rfl) ⟨4205570, by rfl⟩ : syracuseStep 5607427 = 8411141) B8411141
theorem B7476569 : Blo 1941435 7476569 := bstep (se 2 (by rfl) ⟨2803713, by rfl⟩ : syracuseStep 7476569 = 5607427) B5607427
theorem B4984379 : Blo 1941435 4984379 := bstep (se 1 (by rfl) ⟨3738284, by rfl⟩ : syracuseStep 4984379 = 7476569) B7476569
theorem B3322919 : Blo 1941435 3322919 := bstep (se 1 (by rfl) ⟨2492189, by rfl⟩ : syracuseStep 3322919 = 4984379) B4984379
theorem B2215279 : Blo 1941435 2215279 := bstep (se 1 (by rfl) ⟨1661459, by rfl⟩ : syracuseStep 2215279 = 3322919) B3322919
theorem B11814821 : Blo 1941435 11814821 := bstep (se 4 (by rfl) ⟨1107639, by rfl⟩ : syracuseStep 11814821 = 2215279) B2215279
theorem B7876547 : Blo 1941435 7876547 := bstep (se 1 (by rfl) ⟨5907410, by rfl⟩ : syracuseStep 7876547 = 11814821) B11814821
theorem B5251031 : Blo 1941435 5251031 := bstep (se 1 (by rfl) ⟨3938273, by rfl⟩ : syracuseStep 5251031 = 7876547) B7876547
theorem B3500687 : Blo 1941435 3500687 := bstep (se 1 (by rfl) ⟨2625515, by rfl⟩ : syracuseStep 3500687 = 5251031) B5251031
theorem B2333791 : Blo 1941435 2333791 := bstep (se 1 (by rfl) ⟨1750343, by rfl⟩ : syracuseStep 2333791 = 3500687) B3500687
theorem B12446885 : Blo 1941435 12446885 := bstep (se 4 (by rfl) ⟨1166895, by rfl⟩ : syracuseStep 12446885 = 2333791) B2333791
theorem B8297923 : Blo 1941435 8297923 := bstep (se 1 (by rfl) ⟨6223442, by rfl⟩ : syracuseStep 8297923 = 12446885) B12446885
theorem B11063897 : Blo 1941435 11063897 := bstep (se 2 (by rfl) ⟨4148961, by rfl⟩ : syracuseStep 11063897 = 8297923) B8297923
theorem B7375931 : Blo 1941435 7375931 := bstep (se 1 (by rfl) ⟨5531948, by rfl⟩ : syracuseStep 7375931 = 11063897) B11063897
theorem B4917287 : Blo 1941435 4917287 := bstep (se 1 (by rfl) ⟨3687965, by rfl⟩ : syracuseStep 4917287 = 7375931) B7375931
theorem B3278191 : Blo 1941435 3278191 := bstep (se 1 (by rfl) ⟨2458643, by rfl⟩ : syracuseStep 3278191 = 4917287) B4917287
theorem B4370921 : Blo 1941435 4370921 := bstep (se 2 (by rfl) ⟨1639095, by rfl⟩ : syracuseStep 4370921 = 3278191) B3278191
theorem B2913947 : Blo 1941435 2913947 := bstep (se 1 (by rfl) ⟨2185460, by rfl⟩ : syracuseStep 2913947 = 4370921) B4370921
theorem B1942631 : Blo 1941435 1942631 := bstep (se 1 (by rfl) ⟨1456973, by rfl⟩ : syracuseStep 1942631 = 2913947) B2913947
theorem B2185465 : Blo 1941435 2185465 := bbase (se 2 (by rfl) ⟨819549, by rfl⟩ : syracuseStep 2185465 = 1639099) (by norm_num)
theorem B2913953 : Blo 1941435 2913953 := bstep (se 2 (by rfl) ⟨1092732, by rfl⟩ : syracuseStep 2913953 = 2185465) B2185465
theorem B1942635 : Blo 1941435 1942635 := bstep (se 1 (by rfl) ⟨1456976, by rfl⟩ : syracuseStep 1942635 = 2913953) B2913953
theorem B8297957 : Blo 1941435 8297957 := bbase (se 4 (by rfl) ⟨777933, by rfl⟩ : syracuseStep 8297957 = 1555867) (by norm_num)
theorem B5531971 : Blo 1941435 5531971 := bstep (se 1 (by rfl) ⟨4148978, by rfl⟩ : syracuseStep 5531971 = 8297957) B8297957
theorem B7375961 : Blo 1941435 7375961 := bstep (se 2 (by rfl) ⟨2765985, by rfl⟩ : syracuseStep 7375961 = 5531971) B5531971
theorem B4917307 : Blo 1941435 4917307 := bstep (se 1 (by rfl) ⟨3687980, by rfl⟩ : syracuseStep 4917307 = 7375961) B7375961
theorem B6556409 : Blo 1941435 6556409 := bstep (se 2 (by rfl) ⟨2458653, by rfl⟩ : syracuseStep 6556409 = 4917307) B4917307
theorem B4370939 : Blo 1941435 4370939 := bstep (se 1 (by rfl) ⟨3278204, by rfl⟩ : syracuseStep 4370939 = 6556409) B6556409
theorem B2913959 : Blo 1941435 2913959 := bstep (se 1 (by rfl) ⟨2185469, by rfl⟩ : syracuseStep 2913959 = 4370939) B4370939
theorem B1942639 : Blo 1941435 1942639 := bstep (se 1 (by rfl) ⟨1456979, by rfl⟩ : syracuseStep 1942639 = 2913959) B2913959
theorem B2913965 : Blo 1941435 2913965 := bbase (se 3 (by rfl) ⟨546368, by rfl⟩ : syracuseStep 2913965 = 1092737) (by norm_num)
theorem B1942643 : Blo 1941435 1942643 := bstep (se 1 (by rfl) ⟨1456982, by rfl⟩ : syracuseStep 1942643 = 2913965) B2913965
theorem B4370957 : Blo 1941435 4370957 := bbase (se 3 (by rfl) ⟨819554, by rfl⟩ : syracuseStep 4370957 = 1639109) (by norm_num)
theorem B2913971 : Blo 1941435 2913971 := bstep (se 1 (by rfl) ⟨2185478, by rfl⟩ : syracuseStep 2913971 = 4370957) B4370957
theorem B1942647 : Blo 1941435 1942647 := bstep (se 1 (by rfl) ⟨1456985, by rfl⟩ : syracuseStep 1942647 = 2913971) B2913971
theorem B2458669 : Blo 1941435 2458669 := bbase (se 3 (by rfl) ⟨461000, by rfl⟩ : syracuseStep 2458669 = 922001) (by norm_num)
theorem B3278225 : Blo 1941435 3278225 := bstep (se 2 (by rfl) ⟨1229334, by rfl⟩ : syracuseStep 3278225 = 2458669) B2458669
theorem B2185483 : Blo 1941435 2185483 := bstep (se 1 (by rfl) ⟨1639112, by rfl⟩ : syracuseStep 2185483 = 3278225) B3278225
theorem B2913977 : Blo 1941435 2913977 := bstep (se 2 (by rfl) ⟨1092741, by rfl⟩ : syracuseStep 2913977 = 2185483) B2185483
theorem B1942651 : Blo 1941435 1942651 := bstep (se 1 (by rfl) ⟨1456988, by rfl⟩ : syracuseStep 1942651 = 2913977) B2913977
theorem B2953741 : Blo 1941435 2953741 := bbase (se 3 (by rfl) ⟨553826, by rfl⟩ : syracuseStep 2953741 = 1107653) (by norm_num)
theorem B3938321 : Blo 1941435 3938321 := bstep (se 2 (by rfl) ⟨1476870, by rfl⟩ : syracuseStep 3938321 = 2953741) B2953741
theorem B10502189 : Blo 1941435 10502189 := bstep (se 3 (by rfl) ⟨1969160, by rfl⟩ : syracuseStep 10502189 = 3938321) B3938321
theorem B7001459 : Blo 1941435 7001459 := bstep (se 1 (by rfl) ⟨5251094, by rfl⟩ : syracuseStep 7001459 = 10502189) B10502189
theorem B4667639 : Blo 1941435 4667639 := bstep (se 1 (by rfl) ⟨3500729, by rfl⟩ : syracuseStep 4667639 = 7001459) B7001459
theorem B12447037 : Blo 1941435 12447037 := bstep (se 3 (by rfl) ⟨2333819, by rfl⟩ : syracuseStep 12447037 = 4667639) B4667639
theorem B16596049 : Blo 1941435 16596049 := bstep (se 2 (by rfl) ⟨6223518, by rfl⟩ : syracuseStep 16596049 = 12447037) B12447037
theorem B22128065 : Blo 1941435 22128065 := bstep (se 2 (by rfl) ⟨8298024, by rfl⟩ : syracuseStep 22128065 = 16596049) B16596049
theorem B14752043 : Blo 1941435 14752043 := bstep (se 1 (by rfl) ⟨11064032, by rfl⟩ : syracuseStep 14752043 = 22128065) B22128065
theorem B9834695 : Blo 1941435 9834695 := bstep (se 1 (by rfl) ⟨7376021, by rfl⟩ : syracuseStep 9834695 = 14752043) B14752043
theorem B6556463 : Blo 1941435 6556463 := bstep (se 1 (by rfl) ⟨4917347, by rfl⟩ : syracuseStep 6556463 = 9834695) B9834695
theorem B4370975 : Blo 1941435 4370975 := bstep (se 1 (by rfl) ⟨3278231, by rfl⟩ : syracuseStep 4370975 = 6556463) B6556463
theorem B2913983 : Blo 1941435 2913983 := bstep (se 1 (by rfl) ⟨2185487, by rfl⟩ : syracuseStep 2913983 = 4370975) B4370975
theorem B1942655 : Blo 1941435 1942655 := bstep (se 1 (by rfl) ⟨1456991, by rfl⟩ : syracuseStep 1942655 = 2913983) B2913983
theorem B2913989 : Blo 1941435 2913989 := bbase (se 4 (by rfl) ⟨273186, by rfl⟩ : syracuseStep 2913989 = 546373) (by norm_num)
theorem B1942659 : Blo 1941435 1942659 := bstep (se 1 (by rfl) ⟨1456994, by rfl⟩ : syracuseStep 1942659 = 2913989) B2913989
theorem B3278245 : Blo 1941435 3278245 := bbase (se 4 (by rfl) ⟨307335, by rfl⟩ : syracuseStep 3278245 = 614671) (by norm_num)
theorem B4370993 : Blo 1941435 4370993 := bstep (se 2 (by rfl) ⟨1639122, by rfl⟩ : syracuseStep 4370993 = 3278245) B3278245
theorem B2913995 : Blo 1941435 2913995 := bstep (se 1 (by rfl) ⟨2185496, by rfl⟩ : syracuseStep 2913995 = 4370993) B4370993
theorem B1942663 : Blo 1941435 1942663 := bstep (se 1 (by rfl) ⟨1456997, by rfl⟩ : syracuseStep 1942663 = 2913995) B2913995
theorem B2185501 : Blo 1941435 2185501 := bbase (se 3 (by rfl) ⟨409781, by rfl⟩ : syracuseStep 2185501 = 819563) (by norm_num)
theorem B2914001 : Blo 1941435 2914001 := bstep (se 2 (by rfl) ⟨1092750, by rfl⟩ : syracuseStep 2914001 = 2185501) B2185501
theorem B1942667 : Blo 1941435 1942667 := bstep (se 1 (by rfl) ⟨1457000, by rfl⟩ : syracuseStep 1942667 = 2914001) B2914001
theorem B6556517 : Blo 1941435 6556517 := bbase (se 4 (by rfl) ⟨614673, by rfl⟩ : syracuseStep 6556517 = 1229347) (by norm_num)
theorem B4371011 : Blo 1941435 4371011 := bstep (se 1 (by rfl) ⟨3278258, by rfl⟩ : syracuseStep 4371011 = 6556517) B6556517
theorem B2914007 : Blo 1941435 2914007 := bstep (se 1 (by rfl) ⟨2185505, by rfl⟩ : syracuseStep 2914007 = 4371011) B4371011
theorem B1942671 : Blo 1941435 1942671 := bstep (se 1 (by rfl) ⟨1457003, by rfl⟩ : syracuseStep 1942671 = 2914007) B2914007
theorem B2914013 : Blo 1941435 2914013 := bbase (se 3 (by rfl) ⟨546377, by rfl⟩ : syracuseStep 2914013 = 1092755) (by norm_num)
theorem B1942675 : Blo 1941435 1942675 := bstep (se 1 (by rfl) ⟨1457006, by rfl⟩ : syracuseStep 1942675 = 2914013) B2914013
theorem B4371029 : Blo 1941435 4371029 := bbase (se 8 (by rfl) ⟨25611, by rfl⟩ : syracuseStep 4371029 = 51223) (by norm_num)
theorem B2914019 : Blo 1941435 2914019 := bstep (se 1 (by rfl) ⟨2185514, by rfl⟩ : syracuseStep 2914019 = 4371029) B4371029
theorem B1942679 : Blo 1941435 1942679 := bstep (se 1 (by rfl) ⟨1457009, by rfl⟩ : syracuseStep 1942679 = 2914019) B2914019
theorem B3111805 : Blo 1941435 3111805 := bbase (se 3 (by rfl) ⟨583463, by rfl⟩ : syracuseStep 3111805 = 1166927) (by norm_num)
theorem B4149073 : Blo 1941435 4149073 := bstep (se 2 (by rfl) ⟨1555902, by rfl⟩ : syracuseStep 4149073 = 3111805) B3111805
theorem B5532097 : Blo 1941435 5532097 := bstep (se 2 (by rfl) ⟨2074536, by rfl⟩ : syracuseStep 5532097 = 4149073) B4149073
theorem B7376129 : Blo 1941435 7376129 := bstep (se 2 (by rfl) ⟨2766048, by rfl⟩ : syracuseStep 7376129 = 5532097) B5532097
theorem B4917419 : Blo 1941435 4917419 := bstep (se 1 (by rfl) ⟨3688064, by rfl⟩ : syracuseStep 4917419 = 7376129) B7376129
theorem B3278279 : Blo 1941435 3278279 := bstep (se 1 (by rfl) ⟨2458709, by rfl⟩ : syracuseStep 3278279 = 4917419) B4917419
theorem B2185519 : Blo 1941435 2185519 := bstep (se 1 (by rfl) ⟨1639139, by rfl⟩ : syracuseStep 2185519 = 3278279) B3278279
theorem B2914025 : Blo 1941435 2914025 := bstep (se 2 (by rfl) ⟨1092759, by rfl⟩ : syracuseStep 2914025 = 2185519) B2185519
theorem B1942683 : Blo 1941435 1942683 := bstep (se 1 (by rfl) ⟨1457012, by rfl⟩ : syracuseStep 1942683 = 2914025) B2914025
theorem B24894485 : Blo 1941435 24894485 := bbase (se 6 (by rfl) ⟨583464, by rfl⟩ : syracuseStep 24894485 = 1166929) (by norm_num)
theorem B16596323 : Blo 1941435 16596323 := bstep (se 1 (by rfl) ⟨12447242, by rfl⟩ : syracuseStep 16596323 = 24894485) B24894485
theorem B11064215 : Blo 1941435 11064215 := bstep (se 1 (by rfl) ⟨8298161, by rfl⟩ : syracuseStep 11064215 = 16596323) B16596323
theorem B7376143 : Blo 1941435 7376143 := bstep (se 1 (by rfl) ⟨5532107, by rfl⟩ : syracuseStep 7376143 = 11064215) B11064215
theorem B9834857 : Blo 1941435 9834857 := bstep (se 2 (by rfl) ⟨3688071, by rfl⟩ : syracuseStep 9834857 = 7376143) B7376143
theorem B6556571 : Blo 1941435 6556571 := bstep (se 1 (by rfl) ⟨4917428, by rfl⟩ : syracuseStep 6556571 = 9834857) B9834857
theorem B4371047 : Blo 1941435 4371047 := bstep (se 1 (by rfl) ⟨3278285, by rfl⟩ : syracuseStep 4371047 = 6556571) B6556571
theorem B2914031 : Blo 1941435 2914031 := bstep (se 1 (by rfl) ⟨2185523, by rfl⟩ : syracuseStep 2914031 = 4371047) B4371047
theorem B1942687 : Blo 1941435 1942687 := bstep (se 1 (by rfl) ⟨1457015, by rfl⟩ : syracuseStep 1942687 = 2914031) B2914031
theorem B2914037 : Blo 1941435 2914037 := bbase (se 5 (by rfl) ⟨136595, by rfl⟩ : syracuseStep 2914037 = 273191) (by norm_num)
theorem B1942691 : Blo 1941435 1942691 := bstep (se 1 (by rfl) ⟨1457018, by rfl⟩ : syracuseStep 1942691 = 2914037) B2914037
theorem B8298197 : Blo 1941435 8298197 := bbase (se 7 (by rfl) ⟨97244, by rfl⟩ : syracuseStep 8298197 = 194489) (by norm_num)
theorem B5532131 : Blo 1941435 5532131 := bstep (se 1 (by rfl) ⟨4149098, by rfl⟩ : syracuseStep 5532131 = 8298197) B8298197
theorem B3688087 : Blo 1941435 3688087 := bstep (se 1 (by rfl) ⟨2766065, by rfl⟩ : syracuseStep 3688087 = 5532131) B5532131
theorem B4917449 : Blo 1941435 4917449 := bstep (se 2 (by rfl) ⟨1844043, by rfl⟩ : syracuseStep 4917449 = 3688087) B3688087
theorem B3278299 : Blo 1941435 3278299 := bstep (se 1 (by rfl) ⟨2458724, by rfl⟩ : syracuseStep 3278299 = 4917449) B4917449
theorem B4371065 : Blo 1941435 4371065 := bstep (se 2 (by rfl) ⟨1639149, by rfl⟩ : syracuseStep 4371065 = 3278299) B3278299
theorem B2914043 : Blo 1941435 2914043 := bstep (se 1 (by rfl) ⟨2185532, by rfl⟩ : syracuseStep 2914043 = 4371065) B4371065
theorem B1942695 : Blo 1941435 1942695 := bstep (se 1 (by rfl) ⟨1457021, by rfl⟩ : syracuseStep 1942695 = 2914043) B2914043
theorem B2185537 : Blo 1941435 2185537 := bbase (se 2 (by rfl) ⟨819576, by rfl⟩ : syracuseStep 2185537 = 1639153) (by norm_num)
theorem B2914049 : Blo 1941435 2914049 := bstep (se 2 (by rfl) ⟨1092768, by rfl⟩ : syracuseStep 2914049 = 2185537) B2185537
theorem B1942699 : Blo 1941435 1942699 := bstep (se 1 (by rfl) ⟨1457024, by rfl⟩ : syracuseStep 1942699 = 2914049) B2914049
theorem B4917469 : Blo 1941435 4917469 := bbase (se 3 (by rfl) ⟨922025, by rfl⟩ : syracuseStep 4917469 = 1844051) (by norm_num)
theorem B6556625 : Blo 1941435 6556625 := bstep (se 2 (by rfl) ⟨2458734, by rfl⟩ : syracuseStep 6556625 = 4917469) B4917469
theorem B4371083 : Blo 1941435 4371083 := bstep (se 1 (by rfl) ⟨3278312, by rfl⟩ : syracuseStep 4371083 = 6556625) B6556625
theorem B2914055 : Blo 1941435 2914055 := bstep (se 1 (by rfl) ⟨2185541, by rfl⟩ : syracuseStep 2914055 = 4371083) B4371083
theorem B1942703 : Blo 1941435 1942703 := bstep (se 1 (by rfl) ⟨1457027, by rfl⟩ : syracuseStep 1942703 = 2914055) B2914055
theorem B2914061 : Blo 1941435 2914061 := bbase (se 3 (by rfl) ⟨546386, by rfl⟩ : syracuseStep 2914061 = 1092773) (by norm_num)
theorem B1942707 : Blo 1941435 1942707 := bstep (se 1 (by rfl) ⟨1457030, by rfl⟩ : syracuseStep 1942707 = 2914061) B2914061
theorem B4371101 : Blo 1941435 4371101 := bbase (se 3 (by rfl) ⟨819581, by rfl⟩ : syracuseStep 4371101 = 1639163) (by norm_num)
theorem B2914067 : Blo 1941435 2914067 := bstep (se 1 (by rfl) ⟨2185550, by rfl⟩ : syracuseStep 2914067 = 4371101) B4371101
theorem B1942711 : Blo 1941435 1942711 := bstep (se 1 (by rfl) ⟨1457033, by rfl⟩ : syracuseStep 1942711 = 2914067) B2914067
theorem B3278333 : Blo 1941435 3278333 := bbase (se 3 (by rfl) ⟨614687, by rfl⟩ : syracuseStep 3278333 = 1229375) (by norm_num)
theorem B2185555 : Blo 1941435 2185555 := bstep (se 1 (by rfl) ⟨1639166, by rfl⟩ : syracuseStep 2185555 = 3278333) B3278333
theorem B2914073 : Blo 1941435 2914073 := bstep (se 2 (by rfl) ⟨1092777, by rfl⟩ : syracuseStep 2914073 = 2185555) B2185555
theorem B1942715 : Blo 1941435 1942715 := bstep (se 1 (by rfl) ⟨1457036, by rfl⟩ : syracuseStep 1942715 = 2914073) B2914073
theorem B4149149 : Blo 1941435 4149149 := bbase (se 3 (by rfl) ⟨777965, by rfl⟩ : syracuseStep 4149149 = 1555931) (by norm_num)
theorem B11064397 : Blo 1941435 11064397 := bstep (se 3 (by rfl) ⟨2074574, by rfl⟩ : syracuseStep 11064397 = 4149149) B4149149
theorem B14752529 : Blo 1941435 14752529 := bstep (se 2 (by rfl) ⟨5532198, by rfl⟩ : syracuseStep 14752529 = 11064397) B11064397
theorem B9835019 : Blo 1941435 9835019 := bstep (se 1 (by rfl) ⟨7376264, by rfl⟩ : syracuseStep 9835019 = 14752529) B14752529
theorem B6556679 : Blo 1941435 6556679 := bstep (se 1 (by rfl) ⟨4917509, by rfl⟩ : syracuseStep 6556679 = 9835019) B9835019
theorem B4371119 : Blo 1941435 4371119 := bstep (se 1 (by rfl) ⟨3278339, by rfl⟩ : syracuseStep 4371119 = 6556679) B6556679
theorem B2914079 : Blo 1941435 2914079 := bstep (se 1 (by rfl) ⟨2185559, by rfl⟩ : syracuseStep 2914079 = 4371119) B4371119
theorem B1942719 : Blo 1941435 1942719 := bstep (se 1 (by rfl) ⟨1457039, by rfl⟩ : syracuseStep 1942719 = 2914079) B2914079
theorem B2914085 : Blo 1941435 2914085 := bbase (se 4 (by rfl) ⟨273195, by rfl⟩ : syracuseStep 2914085 = 546391) (by norm_num)
theorem B1942723 : Blo 1941435 1942723 := bstep (se 1 (by rfl) ⟨1457042, by rfl⟩ : syracuseStep 1942723 = 2914085) B2914085
theorem B2458765 : Blo 1941435 2458765 := bbase (se 3 (by rfl) ⟨461018, by rfl⟩ : syracuseStep 2458765 = 922037) (by norm_num)
theorem B3278353 : Blo 1941435 3278353 := bstep (se 2 (by rfl) ⟨1229382, by rfl⟩ : syracuseStep 3278353 = 2458765) B2458765
theorem B4371137 : Blo 1941435 4371137 := bstep (se 2 (by rfl) ⟨1639176, by rfl⟩ : syracuseStep 4371137 = 3278353) B3278353
theorem B2914091 : Blo 1941435 2914091 := bstep (se 1 (by rfl) ⟨2185568, by rfl⟩ : syracuseStep 2914091 = 4371137) B4371137
theorem B1942727 : Blo 1941435 1942727 := bstep (se 1 (by rfl) ⟨1457045, by rfl⟩ : syracuseStep 1942727 = 2914091) B2914091
theorem B2185573 : Blo 1941435 2185573 := bbase (se 4 (by rfl) ⟨204897, by rfl⟩ : syracuseStep 2185573 = 409795) (by norm_num)
theorem B2914097 : Blo 1941435 2914097 := bstep (se 2 (by rfl) ⟨1092786, by rfl⟩ : syracuseStep 2914097 = 2185573) B2185573
theorem B1942731 : Blo 1941435 1942731 := bstep (se 1 (by rfl) ⟨1457048, by rfl⟩ : syracuseStep 1942731 = 2914097) B2914097
theorem B5532245 : Blo 1941435 5532245 := bbase (se 8 (by rfl) ⟨32415, by rfl⟩ : syracuseStep 5532245 = 64831) (by norm_num)
theorem B3688163 : Blo 1941435 3688163 := bstep (se 1 (by rfl) ⟨2766122, by rfl⟩ : syracuseStep 3688163 = 5532245) B5532245
theorem B2458775 : Blo 1941435 2458775 := bstep (se 1 (by rfl) ⟨1844081, by rfl⟩ : syracuseStep 2458775 = 3688163) B3688163
theorem B6556733 : Blo 1941435 6556733 := bstep (se 3 (by rfl) ⟨1229387, by rfl⟩ : syracuseStep 6556733 = 2458775) B2458775
theorem B4371155 : Blo 1941435 4371155 := bstep (se 1 (by rfl) ⟨3278366, by rfl⟩ : syracuseStep 4371155 = 6556733) B6556733
theorem B2914103 : Blo 1941435 2914103 := bstep (se 1 (by rfl) ⟨2185577, by rfl⟩ : syracuseStep 2914103 = 4371155) B4371155
theorem B1942735 : Blo 1941435 1942735 := bstep (se 1 (by rfl) ⟨1457051, by rfl⟩ : syracuseStep 1942735 = 2914103) B2914103
theorem B2914109 : Blo 1941435 2914109 := bbase (se 3 (by rfl) ⟨546395, by rfl⟩ : syracuseStep 2914109 = 1092791) (by norm_num)
theorem B1942739 : Blo 1941435 1942739 := bstep (se 1 (by rfl) ⟨1457054, by rfl⟩ : syracuseStep 1942739 = 2914109) B2914109
theorem B4371173 : Blo 1941435 4371173 := bbase (se 4 (by rfl) ⟨409797, by rfl⟩ : syracuseStep 4371173 = 819595) (by norm_num)
theorem B2914115 : Blo 1941435 2914115 := bstep (se 1 (by rfl) ⟨2185586, by rfl⟩ : syracuseStep 2914115 = 4371173) B4371173
theorem B1942743 : Blo 1941435 1942743 := bstep (se 1 (by rfl) ⟨1457057, by rfl⟩ : syracuseStep 1942743 = 2914115) B2914115
theorem B4917581 : Blo 1941435 4917581 := bbase (se 3 (by rfl) ⟨922046, by rfl⟩ : syracuseStep 4917581 = 1844093) (by norm_num)
theorem B3278387 : Blo 1941435 3278387 := bstep (se 1 (by rfl) ⟨2458790, by rfl⟩ : syracuseStep 3278387 = 4917581) B4917581
theorem B2185591 : Blo 1941435 2185591 := bstep (se 1 (by rfl) ⟨1639193, by rfl⟩ : syracuseStep 2185591 = 3278387) B3278387
theorem B2914121 : Blo 1941435 2914121 := bstep (se 2 (by rfl) ⟨1092795, by rfl⟩ : syracuseStep 2914121 = 2185591) B2185591
theorem B1942747 : Blo 1941435 1942747 := bstep (se 1 (by rfl) ⟨1457060, by rfl⟩ : syracuseStep 1942747 = 2914121) B2914121
theorem B2074609 : Blo 1941435 2074609 := bbase (se 2 (by rfl) ⟨777978, by rfl⟩ : syracuseStep 2074609 = 1555957) (by norm_num)
theorem B2766145 : Blo 1941435 2766145 := bstep (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) B2074609
theorem B3688193 : Blo 1941435 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B9835181 : Blo 1941435 9835181 := bstep (se 3 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 9835181 = 3688193) B3688193
theorem B6556787 : Blo 1941435 6556787 := bstep (se 1 (by rfl) ⟨4917590, by rfl⟩ : syracuseStep 6556787 = 9835181) B9835181
theorem B4371191 : Blo 1941435 4371191 := bstep (se 1 (by rfl) ⟨3278393, by rfl⟩ : syracuseStep 4371191 = 6556787) B6556787
theorem B2914127 : Blo 1941435 2914127 := bstep (se 1 (by rfl) ⟨2185595, by rfl⟩ : syracuseStep 2914127 = 4371191) B4371191
theorem B1942751 : Blo 1941435 1942751 := bstep (se 1 (by rfl) ⟨1457063, by rfl⟩ : syracuseStep 1942751 = 2914127) B2914127
theorem B2914133 : Blo 1941435 2914133 := bbase (se 9 (by rfl) ⟨8537, by rfl⟩ : syracuseStep 2914133 = 17075) (by norm_num)
theorem B1942755 : Blo 1941435 1942755 := bstep (se 1 (by rfl) ⟨1457066, by rfl⟩ : syracuseStep 1942755 = 2914133) B2914133
theorem B2333945 : Blo 1941435 2333945 := bbase (se 2 (by rfl) ⟨875229, by rfl⟩ : syracuseStep 2333945 = 1750459) (by norm_num)
theorem B6223853 : Blo 1941435 6223853 := bstep (se 3 (by rfl) ⟨1166972, by rfl⟩ : syracuseStep 6223853 = 2333945) B2333945
theorem B4149235 : Blo 1941435 4149235 := bstep (se 1 (by rfl) ⟨3111926, by rfl⟩ : syracuseStep 4149235 = 6223853) B6223853
theorem B5532313 : Blo 1941435 5532313 := bstep (se 2 (by rfl) ⟨2074617, by rfl⟩ : syracuseStep 5532313 = 4149235) B4149235
theorem B7376417 : Blo 1941435 7376417 := bstep (se 2 (by rfl) ⟨2766156, by rfl⟩ : syracuseStep 7376417 = 5532313) B5532313
theorem B4917611 : Blo 1941435 4917611 := bstep (se 1 (by rfl) ⟨3688208, by rfl⟩ : syracuseStep 4917611 = 7376417) B7376417
theorem B3278407 : Blo 1941435 3278407 := bstep (se 1 (by rfl) ⟨2458805, by rfl⟩ : syracuseStep 3278407 = 4917611) B4917611
theorem B4371209 : Blo 1941435 4371209 := bstep (se 2 (by rfl) ⟨1639203, by rfl⟩ : syracuseStep 4371209 = 3278407) B3278407
theorem B2914139 : Blo 1941435 2914139 := bstep (se 1 (by rfl) ⟨2185604, by rfl⟩ : syracuseStep 2914139 = 4371209) B4371209
theorem B1942759 : Blo 1941435 1942759 := bstep (se 1 (by rfl) ⟨1457069, by rfl⟩ : syracuseStep 1942759 = 2914139) B2914139
theorem B2185609 : Blo 1941435 2185609 := bbase (se 2 (by rfl) ⟨819603, by rfl⟩ : syracuseStep 2185609 = 1639207) (by norm_num)
theorem B2914145 : Blo 1941435 2914145 := bstep (se 2 (by rfl) ⟨1092804, by rfl⟩ : syracuseStep 2914145 = 2185609) B2185609
theorem B1942763 : Blo 1941435 1942763 := bstep (se 1 (by rfl) ⟨1457072, by rfl⟩ : syracuseStep 1942763 = 2914145) B2914145
theorem B5251397 : Blo 1941435 5251397 := bbase (se 4 (by rfl) ⟨492318, by rfl⟩ : syracuseStep 5251397 = 984637) (by norm_num)
theorem B56014901 : Blo 1941435 56014901 := bstep (se 5 (by rfl) ⟨2625698, by rfl⟩ : syracuseStep 56014901 = 5251397) B5251397
theorem B37343267 : Blo 1941435 37343267 := bstep (se 1 (by rfl) ⟨28007450, by rfl⟩ : syracuseStep 37343267 = 56014901) B56014901
theorem B24895511 : Blo 1941435 24895511 := bstep (se 1 (by rfl) ⟨18671633, by rfl⟩ : syracuseStep 24895511 = 37343267) B37343267
theorem B16597007 : Blo 1941435 16597007 := bstep (se 1 (by rfl) ⟨12447755, by rfl⟩ : syracuseStep 16597007 = 24895511) B24895511
theorem B11064671 : Blo 1941435 11064671 := bstep (se 1 (by rfl) ⟨8298503, by rfl⟩ : syracuseStep 11064671 = 16597007) B16597007
theorem B7376447 : Blo 1941435 7376447 := bstep (se 1 (by rfl) ⟨5532335, by rfl⟩ : syracuseStep 7376447 = 11064671) B11064671
theorem B4917631 : Blo 1941435 4917631 := bstep (se 1 (by rfl) ⟨3688223, by rfl⟩ : syracuseStep 4917631 = 7376447) B7376447
theorem B6556841 : Blo 1941435 6556841 := bstep (se 2 (by rfl) ⟨2458815, by rfl⟩ : syracuseStep 6556841 = 4917631) B4917631
theorem B4371227 : Blo 1941435 4371227 := bstep (se 1 (by rfl) ⟨3278420, by rfl⟩ : syracuseStep 4371227 = 6556841) B6556841
theorem B2914151 : Blo 1941435 2914151 := bstep (se 1 (by rfl) ⟨2185613, by rfl⟩ : syracuseStep 2914151 = 4371227) B4371227
theorem B1942767 : Blo 1941435 1942767 := bstep (se 1 (by rfl) ⟨1457075, by rfl⟩ : syracuseStep 1942767 = 2914151) B2914151
theorem B2914157 : Blo 1941435 2914157 := bbase (se 3 (by rfl) ⟨546404, by rfl⟩ : syracuseStep 2914157 = 1092809) (by norm_num)
theorem B1942771 : Blo 1941435 1942771 := bstep (se 1 (by rfl) ⟨1457078, by rfl⟩ : syracuseStep 1942771 = 2914157) B2914157
theorem B4371245 : Blo 1941435 4371245 := bbase (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) (by norm_num)
theorem B2914163 : Blo 1941435 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B1942775 : Blo 1941435 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B7001909 : Blo 1941435 7001909 := bbase (se 5 (by rfl) ⟨328214, by rfl⟩ : syracuseStep 7001909 = 656429) (by norm_num)
theorem B4667939 : Blo 1941435 4667939 := bstep (se 1 (by rfl) ⟨3500954, by rfl⟩ : syracuseStep 4667939 = 7001909) B7001909
theorem B3111959 : Blo 1941435 3111959 := bstep (se 1 (by rfl) ⟨2333969, by rfl⟩ : syracuseStep 3111959 = 4667939) B4667939
theorem B8298557 : Blo 1941435 8298557 := bstep (se 3 (by rfl) ⟨1555979, by rfl⟩ : syracuseStep 8298557 = 3111959) B3111959
theorem B5532371 : Blo 1941435 5532371 := bstep (se 1 (by rfl) ⟨4149278, by rfl⟩ : syracuseStep 5532371 = 8298557) B8298557
theorem B3688247 : Blo 1941435 3688247 := bstep (se 1 (by rfl) ⟨2766185, by rfl⟩ : syracuseStep 3688247 = 5532371) B5532371
theorem B2458831 : Blo 1941435 2458831 := bstep (se 1 (by rfl) ⟨1844123, by rfl⟩ : syracuseStep 2458831 = 3688247) B3688247
theorem B3278441 : Blo 1941435 3278441 := bstep (se 2 (by rfl) ⟨1229415, by rfl⟩ : syracuseStep 3278441 = 2458831) B2458831
theorem B2185627 : Blo 1941435 2185627 := bstep (se 1 (by rfl) ⟨1639220, by rfl⟩ : syracuseStep 2185627 = 3278441) B3278441
theorem B2914169 : Blo 1941435 2914169 := bstep (se 2 (by rfl) ⟨1092813, by rfl⟩ : syracuseStep 2914169 = 2185627) B2185627
theorem B1942779 : Blo 1941435 1942779 := bstep (se 1 (by rfl) ⟨1457084, by rfl⟩ : syracuseStep 1942779 = 2914169) B2914169
theorem B9335893 : Blo 1941435 9335893 := bbase (se 8 (by rfl) ⟨54702, by rfl⟩ : syracuseStep 9335893 = 109405) (by norm_num)
theorem B12447857 : Blo 1941435 12447857 := bstep (se 2 (by rfl) ⟨4667946, by rfl⟩ : syracuseStep 12447857 = 9335893) B9335893
theorem B33194285 : Blo 1941435 33194285 := bstep (se 3 (by rfl) ⟨6223928, by rfl⟩ : syracuseStep 33194285 = 12447857) B12447857
theorem B22129523 : Blo 1941435 22129523 := bstep (se 1 (by rfl) ⟨16597142, by rfl⟩ : syracuseStep 22129523 = 33194285) B33194285
theorem B14753015 : Blo 1941435 14753015 := bstep (se 1 (by rfl) ⟨11064761, by rfl⟩ : syracuseStep 14753015 = 22129523) B22129523
theorem B9835343 : Blo 1941435 9835343 := bstep (se 1 (by rfl) ⟨7376507, by rfl⟩ : syracuseStep 9835343 = 14753015) B14753015
theorem B6556895 : Blo 1941435 6556895 := bstep (se 1 (by rfl) ⟨4917671, by rfl⟩ : syracuseStep 6556895 = 9835343) B9835343
theorem B4371263 : Blo 1941435 4371263 := bstep (se 1 (by rfl) ⟨3278447, by rfl⟩ : syracuseStep 4371263 = 6556895) B6556895
theorem B2914175 : Blo 1941435 2914175 := bstep (se 1 (by rfl) ⟨2185631, by rfl⟩ : syracuseStep 2914175 = 4371263) B4371263
theorem B1942783 : Blo 1941435 1942783 := bstep (se 1 (by rfl) ⟨1457087, by rfl⟩ : syracuseStep 1942783 = 2914175) B2914175
theorem B2914181 : Blo 1941435 2914181 := bbase (se 4 (by rfl) ⟨273204, by rfl⟩ : syracuseStep 2914181 = 546409) (by norm_num)
theorem B1942787 : Blo 1941435 1942787 := bstep (se 1 (by rfl) ⟨1457090, by rfl⟩ : syracuseStep 1942787 = 2914181) B2914181
theorem B3278461 : Blo 1941435 3278461 := bbase (se 3 (by rfl) ⟨614711, by rfl⟩ : syracuseStep 3278461 = 1229423) (by norm_num)
theorem B4371281 : Blo 1941435 4371281 := bstep (se 2 (by rfl) ⟨1639230, by rfl⟩ : syracuseStep 4371281 = 3278461) B3278461
theorem B2914187 : Blo 1941435 2914187 := bstep (se 1 (by rfl) ⟨2185640, by rfl⟩ : syracuseStep 2914187 = 4371281) B4371281
theorem B1942791 : Blo 1941435 1942791 := bstep (se 1 (by rfl) ⟨1457093, by rfl⟩ : syracuseStep 1942791 = 2914187) B2914187
theorem B2185645 : Blo 1941435 2185645 := bbase (se 3 (by rfl) ⟨409808, by rfl⟩ : syracuseStep 2185645 = 819617) (by norm_num)
theorem B2914193 : Blo 1941435 2914193 := bstep (se 2 (by rfl) ⟨1092822, by rfl⟩ : syracuseStep 2914193 = 2185645) B2185645
theorem B1942795 : Blo 1941435 1942795 := bstep (se 1 (by rfl) ⟨1457096, by rfl⟩ : syracuseStep 1942795 = 2914193) B2914193
theorem B6556949 : Blo 1941435 6556949 := bbase (se 6 (by rfl) ⟨153678, by rfl⟩ : syracuseStep 6556949 = 307357) (by norm_num)
theorem B4371299 : Blo 1941435 4371299 := bstep (se 1 (by rfl) ⟨3278474, by rfl⟩ : syracuseStep 4371299 = 6556949) B6556949
theorem B2914199 : Blo 1941435 2914199 := bstep (se 1 (by rfl) ⟨2185649, by rfl⟩ : syracuseStep 2914199 = 4371299) B4371299
theorem B1942799 : Blo 1941435 1942799 := bstep (se 1 (by rfl) ⟨1457099, by rfl⟩ : syracuseStep 1942799 = 2914199) B2914199
theorem B2914205 : Blo 1941435 2914205 := bbase (se 3 (by rfl) ⟨546413, by rfl⟩ : syracuseStep 2914205 = 1092827) (by norm_num)
theorem B1942803 : Blo 1941435 1942803 := bstep (se 1 (by rfl) ⟨1457102, by rfl⟩ : syracuseStep 1942803 = 2914205) B2914205
theorem B4371317 : Blo 1941435 4371317 := bbase (se 5 (by rfl) ⟨204905, by rfl⟩ : syracuseStep 4371317 = 409811) (by norm_num)
theorem B2914211 : Blo 1941435 2914211 := bstep (se 1 (by rfl) ⟨2185658, by rfl⟩ : syracuseStep 2914211 = 4371317) B4371317
theorem B1942807 : Blo 1941435 1942807 := bstep (se 1 (by rfl) ⟨1457105, by rfl⟩ : syracuseStep 1942807 = 2914211) B2914211
theorem B4491421 : Blo 1941435 4491421 := bbase (se 3 (by rfl) ⟨842141, by rfl⟩ : syracuseStep 4491421 = 1684283) (by norm_num)
theorem B95816981 : Blo 1941435 95816981 := bstep (se 6 (by rfl) ⟨2245710, by rfl⟩ : syracuseStep 95816981 = 4491421) B4491421
theorem B63877987 : Blo 1941435 63877987 := bstep (se 1 (by rfl) ⟨47908490, by rfl⟩ : syracuseStep 63877987 = 95816981) B95816981
theorem B85170649 : Blo 1941435 85170649 := bstep (se 2 (by rfl) ⟨31938993, by rfl⟩ : syracuseStep 85170649 = 63877987) B63877987
theorem B113560865 : Blo 1941435 113560865 := bstep (se 2 (by rfl) ⟨42585324, by rfl⟩ : syracuseStep 113560865 = 85170649) B85170649
theorem B75707243 : Blo 1941435 75707243 := bstep (se 1 (by rfl) ⟨56780432, by rfl⟩ : syracuseStep 75707243 = 113560865) B113560865
theorem B50471495 : Blo 1941435 50471495 := bstep (se 1 (by rfl) ⟨37853621, by rfl⟩ : syracuseStep 50471495 = 75707243) B75707243
theorem B33647663 : Blo 1941435 33647663 := bstep (se 1 (by rfl) ⟨25235747, by rfl⟩ : syracuseStep 33647663 = 50471495) B50471495
theorem B22431775 : Blo 1941435 22431775 := bstep (se 1 (by rfl) ⟨16823831, by rfl⟩ : syracuseStep 22431775 = 33647663) B33647663
theorem B29909033 : Blo 1941435 29909033 := bstep (se 2 (by rfl) ⟨11215887, by rfl⟩ : syracuseStep 29909033 = 22431775) B22431775
theorem B19939355 : Blo 1941435 19939355 := bstep (se 1 (by rfl) ⟨14954516, by rfl⟩ : syracuseStep 19939355 = 29909033) B29909033
theorem B13292903 : Blo 1941435 13292903 := bstep (se 1 (by rfl) ⟨9969677, by rfl⟩ : syracuseStep 13292903 = 19939355) B19939355
theorem B8861935 : Blo 1941435 8861935 := bstep (se 1 (by rfl) ⟨6646451, by rfl⟩ : syracuseStep 8861935 = 13292903) B13292903
theorem B11815913 : Blo 1941435 11815913 := bstep (se 2 (by rfl) ⟨4430967, by rfl⟩ : syracuseStep 11815913 = 8861935) B8861935
theorem B31509101 : Blo 1941435 31509101 := bstep (se 3 (by rfl) ⟨5907956, by rfl⟩ : syracuseStep 31509101 = 11815913) B11815913
theorem B21006067 : Blo 1941435 21006067 := bstep (se 1 (by rfl) ⟨15754550, by rfl⟩ : syracuseStep 21006067 = 31509101) B31509101
theorem B28008089 : Blo 1941435 28008089 := bstep (se 2 (by rfl) ⟨10503033, by rfl⟩ : syracuseStep 28008089 = 21006067) B21006067
theorem B18672059 : Blo 1941435 18672059 := bstep (se 1 (by rfl) ⟨14004044, by rfl⟩ : syracuseStep 18672059 = 28008089) B28008089
theorem B12448039 : Blo 1941435 12448039 := bstep (se 1 (by rfl) ⟨9336029, by rfl⟩ : syracuseStep 12448039 = 18672059) B18672059
theorem B16597385 : Blo 1941435 16597385 := bstep (se 2 (by rfl) ⟨6224019, by rfl⟩ : syracuseStep 16597385 = 12448039) B12448039
theorem B11064923 : Blo 1941435 11064923 := bstep (se 1 (by rfl) ⟨8298692, by rfl⟩ : syracuseStep 11064923 = 16597385) B16597385
theorem B7376615 : Blo 1941435 7376615 := bstep (se 1 (by rfl) ⟨5532461, by rfl⟩ : syracuseStep 7376615 = 11064923) B11064923
theorem B4917743 : Blo 1941435 4917743 := bstep (se 1 (by rfl) ⟨3688307, by rfl⟩ : syracuseStep 4917743 = 7376615) B7376615
theorem B3278495 : Blo 1941435 3278495 := bstep (se 1 (by rfl) ⟨2458871, by rfl⟩ : syracuseStep 3278495 = 4917743) B4917743
theorem B2185663 : Blo 1941435 2185663 := bstep (se 1 (by rfl) ⟨1639247, by rfl⟩ : syracuseStep 2185663 = 3278495) B3278495
theorem B2914217 : Blo 1941435 2914217 := bstep (se 2 (by rfl) ⟨1092831, by rfl⟩ : syracuseStep 2914217 = 2185663) B2185663
theorem B1942811 : Blo 1941435 1942811 := bstep (se 1 (by rfl) ⟨1457108, by rfl⟩ : syracuseStep 1942811 = 2914217) B2914217
theorem B7376629 : Blo 1941435 7376629 := bbase (se 5 (by rfl) ⟨345779, by rfl⟩ : syracuseStep 7376629 = 691559) (by norm_num)
theorem B9835505 : Blo 1941435 9835505 := bstep (se 2 (by rfl) ⟨3688314, by rfl⟩ : syracuseStep 9835505 = 7376629) B7376629
theorem B6557003 : Blo 1941435 6557003 := bstep (se 1 (by rfl) ⟨4917752, by rfl⟩ : syracuseStep 6557003 = 9835505) B9835505
theorem B4371335 : Blo 1941435 4371335 := bstep (se 1 (by rfl) ⟨3278501, by rfl⟩ : syracuseStep 4371335 = 6557003) B6557003
theorem B2914223 : Blo 1941435 2914223 := bstep (se 1 (by rfl) ⟨2185667, by rfl⟩ : syracuseStep 2914223 = 4371335) B4371335
theorem B1942815 : Blo 1941435 1942815 := bstep (se 1 (by rfl) ⟨1457111, by rfl⟩ : syracuseStep 1942815 = 2914223) B2914223
theorem B2914229 : Blo 1941435 2914229 := bbase (se 5 (by rfl) ⟨136604, by rfl⟩ : syracuseStep 2914229 = 273209) (by norm_num)
theorem B1942819 : Blo 1941435 1942819 := bstep (se 1 (by rfl) ⟨1457114, by rfl⟩ : syracuseStep 1942819 = 2914229) B2914229
theorem B4917773 : Blo 1941435 4917773 := bbase (se 3 (by rfl) ⟨922082, by rfl⟩ : syracuseStep 4917773 = 1844165) (by norm_num)
theorem B3278515 : Blo 1941435 3278515 := bstep (se 1 (by rfl) ⟨2458886, by rfl⟩ : syracuseStep 3278515 = 4917773) B4917773
theorem B4371353 : Blo 1941435 4371353 := bstep (se 2 (by rfl) ⟨1639257, by rfl⟩ : syracuseStep 4371353 = 3278515) B3278515
theorem B2914235 : Blo 1941435 2914235 := bstep (se 1 (by rfl) ⟨2185676, by rfl⟩ : syracuseStep 2914235 = 4371353) B4371353
theorem B1942823 : Blo 1941435 1942823 := bstep (se 1 (by rfl) ⟨1457117, by rfl⟩ : syracuseStep 1942823 = 2914235) B2914235
theorem B2185681 : Blo 1941435 2185681 := bbase (se 2 (by rfl) ⟨819630, by rfl⟩ : syracuseStep 2185681 = 1639261) (by norm_num)
theorem B2914241 : Blo 1941435 2914241 := bstep (se 2 (by rfl) ⟨1092840, by rfl⟩ : syracuseStep 2914241 = 2185681) B2185681
theorem B1942827 : Blo 1941435 1942827 := bstep (se 1 (by rfl) ⟨1457120, by rfl⟩ : syracuseStep 1942827 = 2914241) B2914241
theorem B4149389 : Blo 1941435 4149389 := bbase (se 3 (by rfl) ⟨778010, by rfl⟩ : syracuseStep 4149389 = 1556021) (by norm_num)
theorem B2766259 : Blo 1941435 2766259 := bstep (se 1 (by rfl) ⟨2074694, by rfl⟩ : syracuseStep 2766259 = 4149389) B4149389
theorem B3688345 : Blo 1941435 3688345 := bstep (se 2 (by rfl) ⟨1383129, by rfl⟩ : syracuseStep 3688345 = 2766259) B2766259
theorem B4917793 : Blo 1941435 4917793 := bstep (se 2 (by rfl) ⟨1844172, by rfl⟩ : syracuseStep 4917793 = 3688345) B3688345
theorem B6557057 : Blo 1941435 6557057 := bstep (se 2 (by rfl) ⟨2458896, by rfl⟩ : syracuseStep 6557057 = 4917793) B4917793
theorem B4371371 : Blo 1941435 4371371 := bstep (se 1 (by rfl) ⟨3278528, by rfl⟩ : syracuseStep 4371371 = 6557057) B6557057
theorem B2914247 : Blo 1941435 2914247 := bstep (se 1 (by rfl) ⟨2185685, by rfl⟩ : syracuseStep 2914247 = 4371371) B4371371
theorem B1942831 : Blo 1941435 1942831 := bstep (se 1 (by rfl) ⟨1457123, by rfl⟩ : syracuseStep 1942831 = 2914247) B2914247
theorem B2914253 : Blo 1941435 2914253 := bbase (se 3 (by rfl) ⟨546422, by rfl⟩ : syracuseStep 2914253 = 1092845) (by norm_num)
theorem B1942835 : Blo 1941435 1942835 := bstep (se 1 (by rfl) ⟨1457126, by rfl⟩ : syracuseStep 1942835 = 2914253) B2914253
theorem B4371389 : Blo 1941435 4371389 := bbase (se 3 (by rfl) ⟨819635, by rfl⟩ : syracuseStep 4371389 = 1639271) (by norm_num)
theorem B2914259 : Blo 1941435 2914259 := bstep (se 1 (by rfl) ⟨2185694, by rfl⟩ : syracuseStep 2914259 = 4371389) B4371389
theorem B1942839 : Blo 1941435 1942839 := bstep (se 1 (by rfl) ⟨1457129, by rfl⟩ : syracuseStep 1942839 = 2914259) B2914259
theorem B3278549 : Blo 1941435 3278549 := bbase (se 7 (by rfl) ⟨38420, by rfl⟩ : syracuseStep 3278549 = 76841) (by norm_num)
theorem B2185699 : Blo 1941435 2185699 := bstep (se 1 (by rfl) ⟨1639274, by rfl⟩ : syracuseStep 2185699 = 3278549) B3278549
theorem B2914265 : Blo 1941435 2914265 := bstep (se 2 (by rfl) ⟨1092849, by rfl⟩ : syracuseStep 2914265 = 2185699) B2185699
theorem B1942843 : Blo 1941435 1942843 := bstep (se 1 (by rfl) ⟨1457132, by rfl⟩ : syracuseStep 1942843 = 2914265) B2914265
theorem B4668101 : Blo 1941435 4668101 := bbase (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) (by norm_num)
theorem B3112067 : Blo 1941435 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B8298845 : Blo 1941435 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B5532563 : Blo 1941435 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B14753501 : Blo 1941435 14753501 := bstep (se 3 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 14753501 = 5532563) B5532563
theorem B9835667 : Blo 1941435 9835667 := bstep (se 1 (by rfl) ⟨7376750, by rfl⟩ : syracuseStep 9835667 = 14753501) B14753501
theorem B6557111 : Blo 1941435 6557111 := bstep (se 1 (by rfl) ⟨4917833, by rfl⟩ : syracuseStep 6557111 = 9835667) B9835667
theorem B4371407 : Blo 1941435 4371407 := bstep (se 1 (by rfl) ⟨3278555, by rfl⟩ : syracuseStep 4371407 = 6557111) B6557111
theorem B2914271 : Blo 1941435 2914271 := bstep (se 1 (by rfl) ⟨2185703, by rfl⟩ : syracuseStep 2914271 = 4371407) B4371407
theorem B1942847 : Blo 1941435 1942847 := bstep (se 1 (by rfl) ⟨1457135, by rfl⟩ : syracuseStep 1942847 = 2914271) B2914271
theorem B2914277 : Blo 1941435 2914277 := bbase (se 4 (by rfl) ⟨273213, by rfl⟩ : syracuseStep 2914277 = 546427) (by norm_num)
theorem B1942851 : Blo 1941435 1942851 := bstep (se 1 (by rfl) ⟨1457138, by rfl⟩ : syracuseStep 1942851 = 2914277) B2914277
theorem B5251637 : Blo 1941435 5251637 := bbase (se 5 (by rfl) ⟨246170, by rfl⟩ : syracuseStep 5251637 = 492341) (by norm_num)
theorem B3501091 : Blo 1941435 3501091 := bstep (se 1 (by rfl) ⟨2625818, by rfl⟩ : syracuseStep 3501091 = 5251637) B5251637
theorem B4668121 : Blo 1941435 4668121 := bstep (se 2 (by rfl) ⟨1750545, by rfl⟩ : syracuseStep 4668121 = 3501091) B3501091
theorem B6224161 : Blo 1941435 6224161 := bstep (se 2 (by rfl) ⟨2334060, by rfl⟩ : syracuseStep 6224161 = 4668121) B4668121
theorem B8298881 : Blo 1941435 8298881 := bstep (se 2 (by rfl) ⟨3112080, by rfl⟩ : syracuseStep 8298881 = 6224161) B6224161
theorem B5532587 : Blo 1941435 5532587 := bstep (se 1 (by rfl) ⟨4149440, by rfl⟩ : syracuseStep 5532587 = 8298881) B8298881
theorem B3688391 : Blo 1941435 3688391 := bstep (se 1 (by rfl) ⟨2766293, by rfl⟩ : syracuseStep 3688391 = 5532587) B5532587
theorem B2458927 : Blo 1941435 2458927 := bstep (se 1 (by rfl) ⟨1844195, by rfl⟩ : syracuseStep 2458927 = 3688391) B3688391
theorem B3278569 : Blo 1941435 3278569 := bstep (se 2 (by rfl) ⟨1229463, by rfl⟩ : syracuseStep 3278569 = 2458927) B2458927
theorem B4371425 : Blo 1941435 4371425 := bstep (se 2 (by rfl) ⟨1639284, by rfl⟩ : syracuseStep 4371425 = 3278569) B3278569
theorem B2914283 : Blo 1941435 2914283 := bstep (se 1 (by rfl) ⟨2185712, by rfl⟩ : syracuseStep 2914283 = 4371425) B4371425
theorem B1942855 : Blo 1941435 1942855 := bstep (se 1 (by rfl) ⟨1457141, by rfl⟩ : syracuseStep 1942855 = 2914283) B2914283
theorem B2185717 : Blo 1941435 2185717 := bbase (se 5 (by rfl) ⟨102455, by rfl⟩ : syracuseStep 2185717 = 204911) (by norm_num)
theorem B2914289 : Blo 1941435 2914289 := bstep (se 2 (by rfl) ⟨1092858, by rfl⟩ : syracuseStep 2914289 = 2185717) B2185717
theorem B1942859 : Blo 1941435 1942859 := bstep (se 1 (by rfl) ⟨1457144, by rfl⟩ : syracuseStep 1942859 = 2914289) B2914289
theorem B2458937 : Blo 1941435 2458937 := bbase (se 2 (by rfl) ⟨922101, by rfl⟩ : syracuseStep 2458937 = 1844203) (by norm_num)
theorem B6557165 : Blo 1941435 6557165 := bstep (se 3 (by rfl) ⟨1229468, by rfl⟩ : syracuseStep 6557165 = 2458937) B2458937
theorem B4371443 : Blo 1941435 4371443 := bstep (se 1 (by rfl) ⟨3278582, by rfl⟩ : syracuseStep 4371443 = 6557165) B6557165
theorem B2914295 : Blo 1941435 2914295 := bstep (se 1 (by rfl) ⟨2185721, by rfl⟩ : syracuseStep 2914295 = 4371443) B4371443
theorem B1942863 : Blo 1941435 1942863 := bstep (se 1 (by rfl) ⟨1457147, by rfl⟩ : syracuseStep 1942863 = 2914295) B2914295
theorem B2914301 : Blo 1941435 2914301 := bbase (se 3 (by rfl) ⟨546431, by rfl⟩ : syracuseStep 2914301 = 1092863) (by norm_num)
theorem B1942867 : Blo 1941435 1942867 := bstep (se 1 (by rfl) ⟨1457150, by rfl⟩ : syracuseStep 1942867 = 2914301) B2914301
theorem B4371461 : Blo 1941435 4371461 := bbase (se 4 (by rfl) ⟨409824, by rfl⟩ : syracuseStep 4371461 = 819649) (by norm_num)
theorem B2914307 : Blo 1941435 2914307 := bstep (se 1 (by rfl) ⟨2185730, by rfl⟩ : syracuseStep 2914307 = 4371461) B4371461
theorem B1942871 : Blo 1941435 1942871 := bstep (se 1 (by rfl) ⟨1457153, by rfl⟩ : syracuseStep 1942871 = 2914307) B2914307
theorem B3688429 : Blo 1941435 3688429 := bbase (se 3 (by rfl) ⟨691580, by rfl⟩ : syracuseStep 3688429 = 1383161) (by norm_num)
theorem B4917905 : Blo 1941435 4917905 := bstep (se 2 (by rfl) ⟨1844214, by rfl⟩ : syracuseStep 4917905 = 3688429) B3688429
theorem B3278603 : Blo 1941435 3278603 := bstep (se 1 (by rfl) ⟨2458952, by rfl⟩ : syracuseStep 3278603 = 4917905) B4917905
theorem B2185735 : Blo 1941435 2185735 := bstep (se 1 (by rfl) ⟨1639301, by rfl⟩ : syracuseStep 2185735 = 3278603) B3278603
theorem B2914313 : Blo 1941435 2914313 := bstep (se 2 (by rfl) ⟨1092867, by rfl⟩ : syracuseStep 2914313 = 2185735) B2185735
theorem B1942875 : Blo 1941435 1942875 := bstep (se 1 (by rfl) ⟨1457156, by rfl⟩ : syracuseStep 1942875 = 2914313) B2914313
theorem B9835829 : Blo 1941435 9835829 := bbase (se 5 (by rfl) ⟨461054, by rfl⟩ : syracuseStep 9835829 = 922109) (by norm_num)
theorem B6557219 : Blo 1941435 6557219 := bstep (se 1 (by rfl) ⟨4917914, by rfl⟩ : syracuseStep 6557219 = 9835829) B9835829
theorem B4371479 : Blo 1941435 4371479 := bstep (se 1 (by rfl) ⟨3278609, by rfl⟩ : syracuseStep 4371479 = 6557219) B6557219
theorem B2914319 : Blo 1941435 2914319 := bstep (se 1 (by rfl) ⟨2185739, by rfl⟩ : syracuseStep 2914319 = 4371479) B4371479
theorem B1942879 : Blo 1941435 1942879 := bstep (se 1 (by rfl) ⟨1457159, by rfl⟩ : syracuseStep 1942879 = 2914319) B2914319
theorem B2914325 : Blo 1941435 2914325 := bbase (se 6 (by rfl) ⟨68304, by rfl⟩ : syracuseStep 2914325 = 136609) (by norm_num)
theorem B1942883 : Blo 1941435 1942883 := bstep (se 1 (by rfl) ⟨1457162, by rfl⟩ : syracuseStep 1942883 = 2914325) B2914325
theorem B4668197 : Blo 1941435 4668197 := bbase (se 4 (by rfl) ⟨437643, by rfl⟩ : syracuseStep 4668197 = 875287) (by norm_num)
theorem B12448525 : Blo 1941435 12448525 := bstep (se 3 (by rfl) ⟨2334098, by rfl⟩ : syracuseStep 12448525 = 4668197) B4668197
theorem B16598033 : Blo 1941435 16598033 := bstep (se 2 (by rfl) ⟨6224262, by rfl⟩ : syracuseStep 16598033 = 12448525) B12448525
theorem B11065355 : Blo 1941435 11065355 := bstep (se 1 (by rfl) ⟨8299016, by rfl⟩ : syracuseStep 11065355 = 16598033) B16598033
theorem B7376903 : Blo 1941435 7376903 := bstep (se 1 (by rfl) ⟨5532677, by rfl⟩ : syracuseStep 7376903 = 11065355) B11065355
theorem B4917935 : Blo 1941435 4917935 := bstep (se 1 (by rfl) ⟨3688451, by rfl⟩ : syracuseStep 4917935 = 7376903) B7376903
theorem B3278623 : Blo 1941435 3278623 := bstep (se 1 (by rfl) ⟨2458967, by rfl⟩ : syracuseStep 3278623 = 4917935) B4917935
theorem B4371497 : Blo 1941435 4371497 := bstep (se 2 (by rfl) ⟨1639311, by rfl⟩ : syracuseStep 4371497 = 3278623) B3278623
theorem B2914331 : Blo 1941435 2914331 := bstep (se 1 (by rfl) ⟨2185748, by rfl⟩ : syracuseStep 2914331 = 4371497) B4371497
theorem B1942887 : Blo 1941435 1942887 := bstep (se 1 (by rfl) ⟨1457165, by rfl⟩ : syracuseStep 1942887 = 2914331) B2914331
theorem B2185753 : Blo 1941435 2185753 := bbase (se 2 (by rfl) ⟨819657, by rfl⟩ : syracuseStep 2185753 = 1639315) (by norm_num)
theorem B2914337 : Blo 1941435 2914337 := bstep (se 2 (by rfl) ⟨1092876, by rfl⟩ : syracuseStep 2914337 = 2185753) B2185753
theorem B1942891 : Blo 1941435 1942891 := bstep (se 1 (by rfl) ⟨1457168, by rfl⟩ : syracuseStep 1942891 = 2914337) B2914337
theorem B7376933 : Blo 1941435 7376933 := bbase (se 4 (by rfl) ⟨691587, by rfl⟩ : syracuseStep 7376933 = 1383175) (by norm_num)
theorem B4917955 : Blo 1941435 4917955 := bstep (se 1 (by rfl) ⟨3688466, by rfl⟩ : syracuseStep 4917955 = 7376933) B7376933
theorem B6557273 : Blo 1941435 6557273 := bstep (se 2 (by rfl) ⟨2458977, by rfl⟩ : syracuseStep 6557273 = 4917955) B4917955
theorem B4371515 : Blo 1941435 4371515 := bstep (se 1 (by rfl) ⟨3278636, by rfl⟩ : syracuseStep 4371515 = 6557273) B6557273
theorem B2914343 : Blo 1941435 2914343 := bstep (se 1 (by rfl) ⟨2185757, by rfl⟩ : syracuseStep 2914343 = 4371515) B4371515
theorem B1942895 : Blo 1941435 1942895 := bstep (se 1 (by rfl) ⟨1457171, by rfl⟩ : syracuseStep 1942895 = 2914343) B2914343
theorem B2914349 : Blo 1941435 2914349 := bbase (se 3 (by rfl) ⟨546440, by rfl⟩ : syracuseStep 2914349 = 1092881) (by norm_num)
theorem B1942899 : Blo 1941435 1942899 := bstep (se 1 (by rfl) ⟨1457174, by rfl⟩ : syracuseStep 1942899 = 2914349) B2914349
theorem B4371533 : Blo 1941435 4371533 := bbase (se 3 (by rfl) ⟨819662, by rfl⟩ : syracuseStep 4371533 = 1639325) (by norm_num)
theorem B2914355 : Blo 1941435 2914355 := bstep (se 1 (by rfl) ⟨2185766, by rfl⟩ : syracuseStep 2914355 = 4371533) B4371533
theorem B1942903 : Blo 1941435 1942903 := bstep (se 1 (by rfl) ⟨1457177, by rfl⟩ : syracuseStep 1942903 = 2914355) B2914355
theorem B2458993 : Blo 1941435 2458993 := bbase (se 2 (by rfl) ⟨922122, by rfl⟩ : syracuseStep 2458993 = 1844245) (by norm_num)
theorem B3278657 : Blo 1941435 3278657 := bstep (se 2 (by rfl) ⟨1229496, by rfl⟩ : syracuseStep 3278657 = 2458993) B2458993
theorem B2185771 : Blo 1941435 2185771 := bstep (se 1 (by rfl) ⟨1639328, by rfl⟩ : syracuseStep 2185771 = 3278657) B3278657
theorem B2914361 : Blo 1941435 2914361 := bstep (se 2 (by rfl) ⟨1092885, by rfl⟩ : syracuseStep 2914361 = 2185771) B2185771
theorem B1942907 : Blo 1941435 1942907 := bstep (se 1 (by rfl) ⟨1457180, by rfl⟩ : syracuseStep 1942907 = 2914361) B2914361
theorem B5908261 : Blo 1941435 5908261 := bbase (se 4 (by rfl) ⟨553899, by rfl⟩ : syracuseStep 5908261 = 1107799) (by norm_num)
theorem B7877681 : Blo 1941435 7877681 := bstep (se 2 (by rfl) ⟨2954130, by rfl⟩ : syracuseStep 7877681 = 5908261) B5908261
theorem B5251787 : Blo 1941435 5251787 := bstep (se 1 (by rfl) ⟨3938840, by rfl⟩ : syracuseStep 5251787 = 7877681) B7877681
theorem B3501191 : Blo 1941435 3501191 := bstep (se 1 (by rfl) ⟨2625893, by rfl⟩ : syracuseStep 3501191 = 5251787) B5251787
theorem B9336509 : Blo 1941435 9336509 := bstep (se 3 (by rfl) ⟨1750595, by rfl⟩ : syracuseStep 9336509 = 3501191) B3501191
theorem B6224339 : Blo 1941435 6224339 := bstep (se 1 (by rfl) ⟨4668254, by rfl⟩ : syracuseStep 6224339 = 9336509) B9336509
theorem B4149559 : Blo 1941435 4149559 := bstep (se 1 (by rfl) ⟨3112169, by rfl⟩ : syracuseStep 4149559 = 6224339) B6224339
theorem B22130981 : Blo 1941435 22130981 := bstep (se 4 (by rfl) ⟨2074779, by rfl⟩ : syracuseStep 22130981 = 4149559) B4149559
theorem B14753987 : Blo 1941435 14753987 := bstep (se 1 (by rfl) ⟨11065490, by rfl⟩ : syracuseStep 14753987 = 22130981) B22130981
theorem B9835991 : Blo 1941435 9835991 := bstep (se 1 (by rfl) ⟨7376993, by rfl⟩ : syracuseStep 9835991 = 14753987) B14753987
theorem B6557327 : Blo 1941435 6557327 := bstep (se 1 (by rfl) ⟨4917995, by rfl⟩ : syracuseStep 6557327 = 9835991) B9835991
theorem B4371551 : Blo 1941435 4371551 := bstep (se 1 (by rfl) ⟨3278663, by rfl⟩ : syracuseStep 4371551 = 6557327) B6557327
theorem B2914367 : Blo 1941435 2914367 := bstep (se 1 (by rfl) ⟨2185775, by rfl⟩ : syracuseStep 2914367 = 4371551) B4371551
theorem B1942911 : Blo 1941435 1942911 := bstep (se 1 (by rfl) ⟨1457183, by rfl⟩ : syracuseStep 1942911 = 2914367) B2914367
theorem B2914373 : Blo 1941435 2914373 := bbase (se 4 (by rfl) ⟨273222, by rfl⟩ : syracuseStep 2914373 = 546445) (by norm_num)
theorem B1942915 : Blo 1941435 1942915 := bstep (se 1 (by rfl) ⟨1457186, by rfl⟩ : syracuseStep 1942915 = 2914373) B2914373
theorem B3278677 : Blo 1941435 3278677 := bbase (se 9 (by rfl) ⟨9605, by rfl⟩ : syracuseStep 3278677 = 19211) (by norm_num)
theorem B4371569 : Blo 1941435 4371569 := bstep (se 2 (by rfl) ⟨1639338, by rfl⟩ : syracuseStep 4371569 = 3278677) B3278677
theorem B2914379 : Blo 1941435 2914379 := bstep (se 1 (by rfl) ⟨2185784, by rfl⟩ : syracuseStep 2914379 = 4371569) B4371569
theorem B1942919 : Blo 1941435 1942919 := bstep (se 1 (by rfl) ⟨1457189, by rfl⟩ : syracuseStep 1942919 = 2914379) B2914379
theorem B2185789 : Blo 1941435 2185789 := bbase (se 3 (by rfl) ⟨409835, by rfl⟩ : syracuseStep 2185789 = 819671) (by norm_num)
theorem B2914385 : Blo 1941435 2914385 := bstep (se 2 (by rfl) ⟨1092894, by rfl⟩ : syracuseStep 2914385 = 2185789) B2185789
theorem B1942923 : Blo 1941435 1942923 := bstep (se 1 (by rfl) ⟨1457192, by rfl⟩ : syracuseStep 1942923 = 2914385) B2914385
theorem B6557381 : Blo 1941435 6557381 := bbase (se 4 (by rfl) ⟨614754, by rfl⟩ : syracuseStep 6557381 = 1229509) (by norm_num)
theorem B4371587 : Blo 1941435 4371587 := bstep (se 1 (by rfl) ⟨3278690, by rfl⟩ : syracuseStep 4371587 = 6557381) B6557381
theorem B2914391 : Blo 1941435 2914391 := bstep (se 1 (by rfl) ⟨2185793, by rfl⟩ : syracuseStep 2914391 = 4371587) B4371587
theorem B1942927 : Blo 1941435 1942927 := bstep (se 1 (by rfl) ⟨1457195, by rfl⟩ : syracuseStep 1942927 = 2914391) B2914391
theorem B2914397 : Blo 1941435 2914397 := bbase (se 3 (by rfl) ⟨546449, by rfl⟩ : syracuseStep 2914397 = 1092899) (by norm_num)
theorem B1942931 : Blo 1941435 1942931 := bstep (se 1 (by rfl) ⟨1457198, by rfl⟩ : syracuseStep 1942931 = 2914397) B2914397
theorem B4371605 : Blo 1941435 4371605 := bbase (se 6 (by rfl) ⟨102459, by rfl⟩ : syracuseStep 4371605 = 204919) (by norm_num)
theorem B2914403 : Blo 1941435 2914403 := bstep (se 1 (by rfl) ⟨2185802, by rfl⟩ : syracuseStep 2914403 = 4371605) B4371605
theorem B1942935 : Blo 1941435 1942935 := bstep (se 1 (by rfl) ⟨1457201, by rfl⟩ : syracuseStep 1942935 = 2914403) B2914403
theorem B2766413 : Blo 1941435 2766413 := bbase (se 3 (by rfl) ⟨518702, by rfl⟩ : syracuseStep 2766413 = 1037405) (by norm_num)
theorem B7377101 : Blo 1941435 7377101 := bstep (se 3 (by rfl) ⟨1383206, by rfl⟩ : syracuseStep 7377101 = 2766413) B2766413
theorem B4918067 : Blo 1941435 4918067 := bstep (se 1 (by rfl) ⟨3688550, by rfl⟩ : syracuseStep 4918067 = 7377101) B7377101
theorem B3278711 : Blo 1941435 3278711 := bstep (se 1 (by rfl) ⟨2459033, by rfl⟩ : syracuseStep 3278711 = 4918067) B4918067
theorem B2185807 : Blo 1941435 2185807 := bstep (se 1 (by rfl) ⟨1639355, by rfl⟩ : syracuseStep 2185807 = 3278711) B3278711
theorem B2914409 : Blo 1941435 2914409 := bstep (se 2 (by rfl) ⟨1092903, by rfl⟩ : syracuseStep 2914409 = 2185807) B2185807
theorem B1942939 : Blo 1941435 1942939 := bstep (se 1 (by rfl) ⟨1457204, by rfl⟩ : syracuseStep 1942939 = 2914409) B2914409
theorem B4431269 : Blo 1941435 4431269 := bbase (se 4 (by rfl) ⟨415431, by rfl⟩ : syracuseStep 4431269 = 830863) (by norm_num)
theorem B2954179 : Blo 1941435 2954179 := bstep (se 1 (by rfl) ⟨2215634, by rfl⟩ : syracuseStep 2954179 = 4431269) B4431269
theorem B3938905 : Blo 1941435 3938905 := bstep (se 2 (by rfl) ⟨1477089, by rfl⟩ : syracuseStep 3938905 = 2954179) B2954179
theorem B5251873 : Blo 1941435 5251873 := bstep (se 2 (by rfl) ⟨1969452, by rfl⟩ : syracuseStep 5251873 = 3938905) B3938905
theorem B7002497 : Blo 1941435 7002497 := bstep (se 2 (by rfl) ⟨2625936, by rfl⟩ : syracuseStep 7002497 = 5251873) B5251873
theorem B18673325 : Blo 1941435 18673325 := bstep (se 3 (by rfl) ⟨3501248, by rfl⟩ : syracuseStep 18673325 = 7002497) B7002497
theorem B12448883 : Blo 1941435 12448883 := bstep (se 1 (by rfl) ⟨9336662, by rfl⟩ : syracuseStep 12448883 = 18673325) B18673325
theorem B8299255 : Blo 1941435 8299255 := bstep (se 1 (by rfl) ⟨6224441, by rfl⟩ : syracuseStep 8299255 = 12448883) B12448883
theorem B11065673 : Blo 1941435 11065673 := bstep (se 2 (by rfl) ⟨4149627, by rfl⟩ : syracuseStep 11065673 = 8299255) B8299255
theorem B7377115 : Blo 1941435 7377115 := bstep (se 1 (by rfl) ⟨5532836, by rfl⟩ : syracuseStep 7377115 = 11065673) B11065673
theorem B9836153 : Blo 1941435 9836153 := bstep (se 2 (by rfl) ⟨3688557, by rfl⟩ : syracuseStep 9836153 = 7377115) B7377115
theorem B6557435 : Blo 1941435 6557435 := bstep (se 1 (by rfl) ⟨4918076, by rfl⟩ : syracuseStep 6557435 = 9836153) B9836153
theorem B4371623 : Blo 1941435 4371623 := bstep (se 1 (by rfl) ⟨3278717, by rfl⟩ : syracuseStep 4371623 = 6557435) B6557435
theorem B2914415 : Blo 1941435 2914415 := bstep (se 1 (by rfl) ⟨2185811, by rfl⟩ : syracuseStep 2914415 = 4371623) B4371623
theorem B1942943 : Blo 1941435 1942943 := bstep (se 1 (by rfl) ⟨1457207, by rfl⟩ : syracuseStep 1942943 = 2914415) B2914415
theorem B2914421 : Blo 1941435 2914421 := bbase (se 5 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 2914421 = 273227) (by norm_num)
theorem B1942947 : Blo 1941435 1942947 := bstep (se 1 (by rfl) ⟨1457210, by rfl⟩ : syracuseStep 1942947 = 2914421) B2914421
theorem B3688573 : Blo 1941435 3688573 := bbase (se 3 (by rfl) ⟨691607, by rfl⟩ : syracuseStep 3688573 = 1383215) (by norm_num)
theorem B4918097 : Blo 1941435 4918097 := bstep (se 2 (by rfl) ⟨1844286, by rfl⟩ : syracuseStep 4918097 = 3688573) B3688573
theorem B3278731 : Blo 1941435 3278731 := bstep (se 1 (by rfl) ⟨2459048, by rfl⟩ : syracuseStep 3278731 = 4918097) B4918097
theorem B4371641 : Blo 1941435 4371641 := bstep (se 2 (by rfl) ⟨1639365, by rfl⟩ : syracuseStep 4371641 = 3278731) B3278731
theorem B2914427 : Blo 1941435 2914427 := bstep (se 1 (by rfl) ⟨2185820, by rfl⟩ : syracuseStep 2914427 = 4371641) B4371641
theorem B1942951 : Blo 1941435 1942951 := bstep (se 1 (by rfl) ⟨1457213, by rfl⟩ : syracuseStep 1942951 = 2914427) B2914427
theorem B2185825 : Blo 1941435 2185825 := bbase (se 2 (by rfl) ⟨819684, by rfl⟩ : syracuseStep 2185825 = 1639369) (by norm_num)
theorem B2914433 : Blo 1941435 2914433 := bstep (se 2 (by rfl) ⟨1092912, by rfl⟩ : syracuseStep 2914433 = 2185825) B2185825
theorem B1942955 : Blo 1941435 1942955 := bstep (se 1 (by rfl) ⟨1457216, by rfl⟩ : syracuseStep 1942955 = 2914433) B2914433
theorem B4918117 : Blo 1941435 4918117 := bbase (se 4 (by rfl) ⟨461073, by rfl⟩ : syracuseStep 4918117 = 922147) (by norm_num)
theorem B6557489 : Blo 1941435 6557489 := bstep (se 2 (by rfl) ⟨2459058, by rfl⟩ : syracuseStep 6557489 = 4918117) B4918117
theorem B4371659 : Blo 1941435 4371659 := bstep (se 1 (by rfl) ⟨3278744, by rfl⟩ : syracuseStep 4371659 = 6557489) B6557489
theorem B2914439 : Blo 1941435 2914439 := bstep (se 1 (by rfl) ⟨2185829, by rfl⟩ : syracuseStep 2914439 = 4371659) B4371659
theorem B1942959 : Blo 1941435 1942959 := bstep (se 1 (by rfl) ⟨1457219, by rfl⟩ : syracuseStep 1942959 = 2914439) B2914439
theorem B2914445 : Blo 1941435 2914445 := bbase (se 3 (by rfl) ⟨546458, by rfl⟩ : syracuseStep 2914445 = 1092917) (by norm_num)
theorem B1942963 : Blo 1941435 1942963 := bstep (se 1 (by rfl) ⟨1457222, by rfl⟩ : syracuseStep 1942963 = 2914445) B2914445
theorem B4371677 : Blo 1941435 4371677 := bbase (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) (by norm_num)
theorem B2914451 : Blo 1941435 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B1942967 : Blo 1941435 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B3278765 : Blo 1941435 3278765 := bbase (se 3 (by rfl) ⟨614768, by rfl⟩ : syracuseStep 3278765 = 1229537) (by norm_num)
theorem B2185843 : Blo 1941435 2185843 := bstep (se 1 (by rfl) ⟨1639382, by rfl⟩ : syracuseStep 2185843 = 3278765) B3278765
theorem B2914457 : Blo 1941435 2914457 := bstep (se 2 (by rfl) ⟨1092921, by rfl⟩ : syracuseStep 2914457 = 2185843) B2185843
theorem B1942971 : Blo 1941435 1942971 := bstep (se 1 (by rfl) ⟨1457228, by rfl⟩ : syracuseStep 1942971 = 2914457) B2914457
theorem B2051201 : Blo 1941435 2051201 := bbase (se 2 (by rfl) ⟨769200, by rfl⟩ : syracuseStep 2051201 = 1538401) (by norm_num)
theorem B5469869 : Blo 1941435 5469869 := bstep (se 3 (by rfl) ⟨1025600, by rfl⟩ : syracuseStep 5469869 = 2051201) B2051201
theorem B14586317 : Blo 1941435 14586317 := bstep (se 3 (by rfl) ⟨2734934, by rfl⟩ : syracuseStep 14586317 = 5469869) B5469869
theorem B9724211 : Blo 1941435 9724211 := bstep (se 1 (by rfl) ⟨7293158, by rfl⟩ : syracuseStep 9724211 = 14586317) B14586317
theorem B6482807 : Blo 1941435 6482807 := bstep (se 1 (by rfl) ⟨4862105, by rfl⟩ : syracuseStep 6482807 = 9724211) B9724211
theorem B4321871 : Blo 1941435 4321871 := bstep (se 1 (by rfl) ⟨3241403, by rfl⟩ : syracuseStep 4321871 = 6482807) B6482807
theorem B2881247 : Blo 1941435 2881247 := bstep (se 1 (by rfl) ⟨2160935, by rfl⟩ : syracuseStep 2881247 = 4321871) B4321871
theorem B7683325 : Blo 1941435 7683325 := bstep (se 3 (by rfl) ⟨1440623, by rfl⟩ : syracuseStep 7683325 = 2881247) B2881247
theorem B40977733 : Blo 1941435 40977733 := bstep (se 4 (by rfl) ⟨3841662, by rfl⟩ : syracuseStep 40977733 = 7683325) B7683325
theorem B54636977 : Blo 1941435 54636977 := bstep (se 2 (by rfl) ⟨20488866, by rfl⟩ : syracuseStep 54636977 = 40977733) B40977733
theorem B36424651 : Blo 1941435 36424651 := bstep (se 1 (by rfl) ⟨27318488, by rfl⟩ : syracuseStep 36424651 = 54636977) B54636977
theorem B48566201 : Blo 1941435 48566201 := bstep (se 2 (by rfl) ⟨18212325, by rfl⟩ : syracuseStep 48566201 = 36424651) B36424651
theorem B129509869 : Blo 1941435 129509869 := bstep (se 3 (by rfl) ⟨24283100, by rfl⟩ : syracuseStep 129509869 = 48566201) B48566201
theorem B172679825 : Blo 1941435 172679825 := bstep (se 2 (by rfl) ⟨64754934, by rfl⟩ : syracuseStep 172679825 = 129509869) B129509869
theorem B115119883 : Blo 1941435 115119883 := bstep (se 1 (by rfl) ⟨86339912, by rfl⟩ : syracuseStep 115119883 = 172679825) B172679825
theorem B613972709 : Blo 1941435 613972709 := bstep (se 4 (by rfl) ⟨57559941, by rfl⟩ : syracuseStep 613972709 = 115119883) B115119883
theorem B409315139 : Blo 1941435 409315139 := bstep (se 1 (by rfl) ⟨306986354, by rfl⟩ : syracuseStep 409315139 = 613972709) B613972709
theorem B272876759 : Blo 1941435 272876759 := bstep (se 1 (by rfl) ⟨204657569, by rfl⟩ : syracuseStep 272876759 = 409315139) B409315139
theorem B181917839 : Blo 1941435 181917839 := bstep (se 1 (by rfl) ⟨136438379, by rfl⟩ : syracuseStep 181917839 = 272876759) B272876759
theorem B121278559 : Blo 1941435 121278559 := bstep (se 1 (by rfl) ⟨90958919, by rfl⟩ : syracuseStep 121278559 = 181917839) B181917839
theorem B161704745 : Blo 1941435 161704745 := bstep (se 2 (by rfl) ⟨60639279, by rfl⟩ : syracuseStep 161704745 = 121278559) B121278559
theorem B107803163 : Blo 1941435 107803163 := bstep (se 1 (by rfl) ⟨80852372, by rfl⟩ : syracuseStep 107803163 = 161704745) B161704745
theorem B71868775 : Blo 1941435 71868775 := bstep (se 1 (by rfl) ⟨53901581, by rfl⟩ : syracuseStep 71868775 = 107803163) B107803163
theorem B95825033 : Blo 1941435 95825033 := bstep (se 2 (by rfl) ⟨35934387, by rfl⟩ : syracuseStep 95825033 = 71868775) B71868775
theorem B63883355 : Blo 1941435 63883355 := bstep (se 1 (by rfl) ⟨47912516, by rfl⟩ : syracuseStep 63883355 = 95825033) B95825033
theorem B681422453 : Blo 1941435 681422453 := bstep (se 5 (by rfl) ⟨31941677, by rfl⟩ : syracuseStep 681422453 = 63883355) B63883355
theorem B454281635 : Blo 1941435 454281635 := bstep (se 1 (by rfl) ⟨340711226, by rfl⟩ : syracuseStep 454281635 = 681422453) B681422453
theorem B302854423 : Blo 1941435 302854423 := bstep (se 1 (by rfl) ⟨227140817, by rfl⟩ : syracuseStep 302854423 = 454281635) B454281635
theorem B403805897 : Blo 1941435 403805897 := bstep (se 2 (by rfl) ⟨151427211, by rfl⟩ : syracuseStep 403805897 = 302854423) B302854423
theorem B269203931 : Blo 1941435 269203931 := bstep (se 1 (by rfl) ⟨201902948, by rfl⟩ : syracuseStep 269203931 = 403805897) B403805897
theorem B179469287 : Blo 1941435 179469287 := bstep (se 1 (by rfl) ⟨134601965, by rfl⟩ : syracuseStep 179469287 = 269203931) B269203931
theorem B119646191 : Blo 1941435 119646191 := bstep (se 1 (by rfl) ⟨89734643, by rfl⟩ : syracuseStep 119646191 = 179469287) B179469287
theorem B319056509 : Blo 1941435 319056509 := bstep (se 3 (by rfl) ⟨59823095, by rfl⟩ : syracuseStep 319056509 = 119646191) B119646191
theorem B212704339 : Blo 1941435 212704339 := bstep (se 1 (by rfl) ⟨159528254, by rfl⟩ : syracuseStep 212704339 = 319056509) B319056509
theorem B283605785 : Blo 1941435 283605785 := bstep (se 2 (by rfl) ⟨106352169, by rfl⟩ : syracuseStep 283605785 = 212704339) B212704339
theorem B189070523 : Blo 1941435 189070523 := bstep (se 1 (by rfl) ⟨141802892, by rfl⟩ : syracuseStep 189070523 = 283605785) B283605785
theorem B126047015 : Blo 1941435 126047015 := bstep (se 1 (by rfl) ⟨94535261, by rfl⟩ : syracuseStep 126047015 = 189070523) B189070523
theorem B84031343 : Blo 1941435 84031343 := bstep (se 1 (by rfl) ⟨63023507, by rfl⟩ : syracuseStep 84031343 = 126047015) B126047015
theorem B56020895 : Blo 1941435 56020895 := bstep (se 1 (by rfl) ⟨42015671, by rfl⟩ : syracuseStep 56020895 = 84031343) B84031343
theorem B37347263 : Blo 1941435 37347263 := bstep (se 1 (by rfl) ⟨28010447, by rfl⟩ : syracuseStep 37347263 = 56020895) B56020895
theorem B24898175 : Blo 1941435 24898175 := bstep (se 1 (by rfl) ⟨18673631, by rfl⟩ : syracuseStep 24898175 = 37347263) B37347263
theorem B16598783 : Blo 1941435 16598783 := bstep (se 1 (by rfl) ⟨12449087, by rfl⟩ : syracuseStep 16598783 = 24898175) B24898175
theorem B11065855 : Blo 1941435 11065855 := bstep (se 1 (by rfl) ⟨8299391, by rfl⟩ : syracuseStep 11065855 = 16598783) B16598783
theorem B14754473 : Blo 1941435 14754473 := bstep (se 2 (by rfl) ⟨5532927, by rfl⟩ : syracuseStep 14754473 = 11065855) B11065855
theorem B9836315 : Blo 1941435 9836315 := bstep (se 1 (by rfl) ⟨7377236, by rfl⟩ : syracuseStep 9836315 = 14754473) B14754473
theorem B6557543 : Blo 1941435 6557543 := bstep (se 1 (by rfl) ⟨4918157, by rfl⟩ : syracuseStep 6557543 = 9836315) B9836315
theorem B4371695 : Blo 1941435 4371695 := bstep (se 1 (by rfl) ⟨3278771, by rfl⟩ : syracuseStep 4371695 = 6557543) B6557543
theorem B2914463 : Blo 1941435 2914463 := bstep (se 1 (by rfl) ⟨2185847, by rfl⟩ : syracuseStep 2914463 = 4371695) B4371695
theorem B1942975 : Blo 1941435 1942975 := bstep (se 1 (by rfl) ⟨1457231, by rfl⟩ : syracuseStep 1942975 = 2914463) B2914463
theorem B2914469 : Blo 1941435 2914469 := bbase (se 4 (by rfl) ⟨273231, by rfl⟩ : syracuseStep 2914469 = 546463) (by norm_num)
theorem B1942979 : Blo 1941435 1942979 := bstep (se 1 (by rfl) ⟨1457234, by rfl⟩ : syracuseStep 1942979 = 2914469) B2914469
theorem B2459089 : Blo 1941435 2459089 := bbase (se 2 (by rfl) ⟨922158, by rfl⟩ : syracuseStep 2459089 = 1844317) (by norm_num)
theorem B3278785 : Blo 1941435 3278785 := bstep (se 2 (by rfl) ⟨1229544, by rfl⟩ : syracuseStep 3278785 = 2459089) B2459089
theorem B4371713 : Blo 1941435 4371713 := bstep (se 2 (by rfl) ⟨1639392, by rfl⟩ : syracuseStep 4371713 = 3278785) B3278785
theorem B2914475 : Blo 1941435 2914475 := bstep (se 1 (by rfl) ⟨2185856, by rfl⟩ : syracuseStep 2914475 = 4371713) B4371713
theorem B1942983 : Blo 1941435 1942983 := bstep (se 1 (by rfl) ⟨1457237, by rfl⟩ : syracuseStep 1942983 = 2914475) B2914475
theorem B2185861 : Blo 1941435 2185861 := bbase (se 4 (by rfl) ⟨204924, by rfl⟩ : syracuseStep 2185861 = 409849) (by norm_num)
theorem B2914481 : Blo 1941435 2914481 := bstep (se 2 (by rfl) ⟨1092930, by rfl⟩ : syracuseStep 2914481 = 2185861) B2185861
theorem B1942987 : Blo 1941435 1942987 := bstep (se 1 (by rfl) ⟨1457240, by rfl⟩ : syracuseStep 1942987 = 2914481) B2914481
theorem B6224597 : Blo 1941435 6224597 := bbase (se 7 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 6224597 = 145889) (by norm_num)
theorem B4149731 : Blo 1941435 4149731 := bstep (se 1 (by rfl) ⟨3112298, by rfl⟩ : syracuseStep 4149731 = 6224597) B6224597
theorem B2766487 : Blo 1941435 2766487 := bstep (se 1 (by rfl) ⟨2074865, by rfl⟩ : syracuseStep 2766487 = 4149731) B4149731
theorem B3688649 : Blo 1941435 3688649 := bstep (se 2 (by rfl) ⟨1383243, by rfl⟩ : syracuseStep 3688649 = 2766487) B2766487
theorem B2459099 : Blo 1941435 2459099 := bstep (se 1 (by rfl) ⟨1844324, by rfl⟩ : syracuseStep 2459099 = 3688649) B3688649
theorem B6557597 : Blo 1941435 6557597 := bstep (se 3 (by rfl) ⟨1229549, by rfl⟩ : syracuseStep 6557597 = 2459099) B2459099
theorem B4371731 : Blo 1941435 4371731 := bstep (se 1 (by rfl) ⟨3278798, by rfl⟩ : syracuseStep 4371731 = 6557597) B6557597
theorem B2914487 : Blo 1941435 2914487 := bstep (se 1 (by rfl) ⟨2185865, by rfl⟩ : syracuseStep 2914487 = 4371731) B4371731
theorem B1942991 : Blo 1941435 1942991 := bstep (se 1 (by rfl) ⟨1457243, by rfl⟩ : syracuseStep 1942991 = 2914487) B2914487
theorem B2914493 : Blo 1941435 2914493 := bbase (se 3 (by rfl) ⟨546467, by rfl⟩ : syracuseStep 2914493 = 1092935) (by norm_num)
theorem B1942995 : Blo 1941435 1942995 := bstep (se 1 (by rfl) ⟨1457246, by rfl⟩ : syracuseStep 1942995 = 2914493) B2914493
theorem B4371749 : Blo 1941435 4371749 := bbase (se 4 (by rfl) ⟨409851, by rfl⟩ : syracuseStep 4371749 = 819703) (by norm_num)
theorem B2914499 : Blo 1941435 2914499 := bstep (se 1 (by rfl) ⟨2185874, by rfl⟩ : syracuseStep 2914499 = 4371749) B4371749
theorem B1942999 : Blo 1941435 1942999 := bstep (se 1 (by rfl) ⟨1457249, by rfl⟩ : syracuseStep 1942999 = 2914499) B2914499
theorem B4918229 : Blo 1941435 4918229 := bbase (se 7 (by rfl) ⟨57635, by rfl⟩ : syracuseStep 4918229 = 115271) (by norm_num)
theorem B3278819 : Blo 1941435 3278819 := bstep (se 1 (by rfl) ⟨2459114, by rfl⟩ : syracuseStep 3278819 = 4918229) B4918229
theorem B2185879 : Blo 1941435 2185879 := bstep (se 1 (by rfl) ⟨1639409, by rfl⟩ : syracuseStep 2185879 = 3278819) B3278819
theorem B2914505 : Blo 1941435 2914505 := bstep (se 2 (by rfl) ⟨1092939, by rfl⟩ : syracuseStep 2914505 = 2185879) B2185879
theorem B1943003 : Blo 1941435 1943003 := bstep (se 1 (by rfl) ⟨1457252, by rfl⟩ : syracuseStep 1943003 = 2914505) B2914505
theorem B7985557 : Blo 1941435 7985557 := bbase (se 6 (by rfl) ⟨187161, by rfl⟩ : syracuseStep 7985557 = 374323) (by norm_num)
theorem B42589637 : Blo 1941435 42589637 := bstep (se 4 (by rfl) ⟨3992778, by rfl⟩ : syracuseStep 42589637 = 7985557) B7985557
theorem B28393091 : Blo 1941435 28393091 := bstep (se 1 (by rfl) ⟨21294818, by rfl⟩ : syracuseStep 28393091 = 42589637) B42589637
theorem B18928727 : Blo 1941435 18928727 := bstep (se 1 (by rfl) ⟨14196545, by rfl⟩ : syracuseStep 18928727 = 28393091) B28393091
theorem B12619151 : Blo 1941435 12619151 := bstep (se 1 (by rfl) ⟨9464363, by rfl⟩ : syracuseStep 12619151 = 18928727) B18928727
theorem B8412767 : Blo 1941435 8412767 := bstep (se 1 (by rfl) ⟨6309575, by rfl⟩ : syracuseStep 8412767 = 12619151) B12619151
theorem B5608511 : Blo 1941435 5608511 := bstep (se 1 (by rfl) ⟨4206383, by rfl⟩ : syracuseStep 5608511 = 8412767) B8412767
theorem B3739007 : Blo 1941435 3739007 := bstep (se 1 (by rfl) ⟨2804255, by rfl⟩ : syracuseStep 3739007 = 5608511) B5608511
theorem B9970685 : Blo 1941435 9970685 := bstep (se 3 (by rfl) ⟨1869503, by rfl⟩ : syracuseStep 9970685 = 3739007) B3739007
theorem B6647123 : Blo 1941435 6647123 := bstep (se 1 (by rfl) ⟨4985342, by rfl⟩ : syracuseStep 6647123 = 9970685) B9970685
theorem B4431415 : Blo 1941435 4431415 := bstep (se 1 (by rfl) ⟨3323561, by rfl⟩ : syracuseStep 4431415 = 6647123) B6647123
theorem B5908553 : Blo 1941435 5908553 := bstep (se 2 (by rfl) ⟨2215707, by rfl⟩ : syracuseStep 5908553 = 4431415) B4431415
theorem B3939035 : Blo 1941435 3939035 := bstep (se 1 (by rfl) ⟨2954276, by rfl⟩ : syracuseStep 3939035 = 5908553) B5908553
theorem B10504093 : Blo 1941435 10504093 := bstep (se 3 (by rfl) ⟨1969517, by rfl⟩ : syracuseStep 10504093 = 3939035) B3939035
theorem B14005457 : Blo 1941435 14005457 := bstep (se 2 (by rfl) ⟨5252046, by rfl⟩ : syracuseStep 14005457 = 10504093) B10504093
theorem B9336971 : Blo 1941435 9336971 := bstep (se 1 (by rfl) ⟨7002728, by rfl⟩ : syracuseStep 9336971 = 14005457) B14005457
theorem B6224647 : Blo 1941435 6224647 := bstep (se 1 (by rfl) ⟨4668485, by rfl⟩ : syracuseStep 6224647 = 9336971) B9336971
theorem B8299529 : Blo 1941435 8299529 := bstep (se 2 (by rfl) ⟨3112323, by rfl⟩ : syracuseStep 8299529 = 6224647) B6224647
theorem B5533019 : Blo 1941435 5533019 := bstep (se 1 (by rfl) ⟨4149764, by rfl⟩ : syracuseStep 5533019 = 8299529) B8299529
theorem B3688679 : Blo 1941435 3688679 := bstep (se 1 (by rfl) ⟨2766509, by rfl⟩ : syracuseStep 3688679 = 5533019) B5533019
theorem B9836477 : Blo 1941435 9836477 := bstep (se 3 (by rfl) ⟨1844339, by rfl⟩ : syracuseStep 9836477 = 3688679) B3688679
theorem B6557651 : Blo 1941435 6557651 := bstep (se 1 (by rfl) ⟨4918238, by rfl⟩ : syracuseStep 6557651 = 9836477) B9836477
theorem B4371767 : Blo 1941435 4371767 := bstep (se 1 (by rfl) ⟨3278825, by rfl⟩ : syracuseStep 4371767 = 6557651) B6557651
theorem B2914511 : Blo 1941435 2914511 := bstep (se 1 (by rfl) ⟨2185883, by rfl⟩ : syracuseStep 2914511 = 4371767) B4371767
theorem B1943007 : Blo 1941435 1943007 := bstep (se 1 (by rfl) ⟨1457255, by rfl⟩ : syracuseStep 1943007 = 2914511) B2914511
theorem B2914517 : Blo 1941435 2914517 := bbase (se 7 (by rfl) ⟨34154, by rfl⟩ : syracuseStep 2914517 = 68309) (by norm_num)
theorem B1943011 : Blo 1941435 1943011 := bstep (se 1 (by rfl) ⟨1457258, by rfl⟩ : syracuseStep 1943011 = 2914517) B2914517
theorem B2334253 : Blo 1941435 2334253 := bbase (se 3 (by rfl) ⟨437672, by rfl⟩ : syracuseStep 2334253 = 875345) (by norm_num)
theorem B3112337 : Blo 1941435 3112337 := bstep (se 2 (by rfl) ⟨1167126, by rfl⟩ : syracuseStep 3112337 = 2334253) B2334253
theorem B2074891 : Blo 1941435 2074891 := bstep (se 1 (by rfl) ⟨1556168, by rfl⟩ : syracuseStep 2074891 = 3112337) B3112337
theorem B2766521 : Blo 1941435 2766521 := bstep (se 2 (by rfl) ⟨1037445, by rfl⟩ : syracuseStep 2766521 = 2074891) B2074891
theorem B7377389 : Blo 1941435 7377389 := bstep (se 3 (by rfl) ⟨1383260, by rfl⟩ : syracuseStep 7377389 = 2766521) B2766521
theorem B4918259 : Blo 1941435 4918259 := bstep (se 1 (by rfl) ⟨3688694, by rfl⟩ : syracuseStep 4918259 = 7377389) B7377389
theorem B3278839 : Blo 1941435 3278839 := bstep (se 1 (by rfl) ⟨2459129, by rfl⟩ : syracuseStep 3278839 = 4918259) B4918259
theorem B4371785 : Blo 1941435 4371785 := bstep (se 2 (by rfl) ⟨1639419, by rfl⟩ : syracuseStep 4371785 = 3278839) B3278839
theorem B2914523 : Blo 1941435 2914523 := bstep (se 1 (by rfl) ⟨2185892, by rfl⟩ : syracuseStep 2914523 = 4371785) B4371785
theorem B1943015 : Blo 1941435 1943015 := bstep (se 1 (by rfl) ⟨1457261, by rfl⟩ : syracuseStep 1943015 = 2914523) B2914523
theorem B2185897 : Blo 1941435 2185897 := bbase (se 2 (by rfl) ⟨819711, by rfl⟩ : syracuseStep 2185897 = 1639423) (by norm_num)
theorem B2914529 : Blo 1941435 2914529 := bstep (se 2 (by rfl) ⟨1092948, by rfl⟩ : syracuseStep 2914529 = 2185897) B2185897
theorem B1943019 : Blo 1941435 1943019 := bstep (se 1 (by rfl) ⟨1457264, by rfl⟩ : syracuseStep 1943019 = 2914529) B2914529
theorem B3112349 : Blo 1941435 3112349 := bbase (se 3 (by rfl) ⟨583565, by rfl⟩ : syracuseStep 3112349 = 1167131) (by norm_num)
theorem B8299597 : Blo 1941435 8299597 := bstep (se 3 (by rfl) ⟨1556174, by rfl⟩ : syracuseStep 8299597 = 3112349) B3112349
theorem B11066129 : Blo 1941435 11066129 := bstep (se 2 (by rfl) ⟨4149798, by rfl⟩ : syracuseStep 11066129 = 8299597) B8299597
theorem B7377419 : Blo 1941435 7377419 := bstep (se 1 (by rfl) ⟨5533064, by rfl⟩ : syracuseStep 7377419 = 11066129) B11066129
theorem B4918279 : Blo 1941435 4918279 := bstep (se 1 (by rfl) ⟨3688709, by rfl⟩ : syracuseStep 4918279 = 7377419) B7377419
theorem B6557705 : Blo 1941435 6557705 := bstep (se 2 (by rfl) ⟨2459139, by rfl⟩ : syracuseStep 6557705 = 4918279) B4918279
theorem B4371803 : Blo 1941435 4371803 := bstep (se 1 (by rfl) ⟨3278852, by rfl⟩ : syracuseStep 4371803 = 6557705) B6557705
theorem B2914535 : Blo 1941435 2914535 := bstep (se 1 (by rfl) ⟨2185901, by rfl⟩ : syracuseStep 2914535 = 4371803) B4371803
theorem B1943023 : Blo 1941435 1943023 := bstep (se 1 (by rfl) ⟨1457267, by rfl⟩ : syracuseStep 1943023 = 2914535) B2914535
theorem B2914541 : Blo 1941435 2914541 := bbase (se 3 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 2914541 = 1092953) (by norm_num)
theorem B1943027 : Blo 1941435 1943027 := bstep (se 1 (by rfl) ⟨1457270, by rfl⟩ : syracuseStep 1943027 = 2914541) B2914541
theorem B4371821 : Blo 1941435 4371821 := bbase (se 3 (by rfl) ⟨819716, by rfl⟩ : syracuseStep 4371821 = 1639433) (by norm_num)
theorem B2914547 : Blo 1941435 2914547 := bstep (se 1 (by rfl) ⟨2185910, by rfl⟩ : syracuseStep 2914547 = 4371821) B4371821
theorem B1943031 : Blo 1941435 1943031 := bstep (se 1 (by rfl) ⟨1457273, by rfl⟩ : syracuseStep 1943031 = 2914547) B2914547
theorem B3688733 : Blo 1941435 3688733 := bbase (se 3 (by rfl) ⟨691637, by rfl⟩ : syracuseStep 3688733 = 1383275) (by norm_num)
theorem B2459155 : Blo 1941435 2459155 := bstep (se 1 (by rfl) ⟨1844366, by rfl⟩ : syracuseStep 2459155 = 3688733) B3688733
theorem B3278873 : Blo 1941435 3278873 := bstep (se 2 (by rfl) ⟨1229577, by rfl⟩ : syracuseStep 3278873 = 2459155) B2459155
theorem B2185915 : Blo 1941435 2185915 := bstep (se 1 (by rfl) ⟨1639436, by rfl⟩ : syracuseStep 2185915 = 3278873) B3278873
theorem B2914553 : Blo 1941435 2914553 := bstep (se 2 (by rfl) ⟨1092957, by rfl⟩ : syracuseStep 2914553 = 2185915) B2185915
theorem B1943035 : Blo 1941435 1943035 := bstep (se 1 (by rfl) ⟨1457276, by rfl⟩ : syracuseStep 1943035 = 2914553) B2914553
theorem B14005685 : Blo 1941435 14005685 := bbase (se 5 (by rfl) ⟨656516, by rfl⟩ : syracuseStep 14005685 = 1313033) (by norm_num)
theorem B9337123 : Blo 1941435 9337123 := bstep (se 1 (by rfl) ⟨7002842, by rfl⟩ : syracuseStep 9337123 = 14005685) B14005685
theorem B49797989 : Blo 1941435 49797989 := bstep (se 4 (by rfl) ⟨4668561, by rfl⟩ : syracuseStep 49797989 = 9337123) B9337123
theorem B33198659 : Blo 1941435 33198659 := bstep (se 1 (by rfl) ⟨24898994, by rfl⟩ : syracuseStep 33198659 = 49797989) B49797989
theorem B22132439 : Blo 1941435 22132439 := bstep (se 1 (by rfl) ⟨16599329, by rfl⟩ : syracuseStep 22132439 = 33198659) B33198659
theorem B14754959 : Blo 1941435 14754959 := bstep (se 1 (by rfl) ⟨11066219, by rfl⟩ : syracuseStep 14754959 = 22132439) B22132439
theorem B9836639 : Blo 1941435 9836639 := bstep (se 1 (by rfl) ⟨7377479, by rfl⟩ : syracuseStep 9836639 = 14754959) B14754959
theorem B6557759 : Blo 1941435 6557759 := bstep (se 1 (by rfl) ⟨4918319, by rfl⟩ : syracuseStep 6557759 = 9836639) B9836639
theorem B4371839 : Blo 1941435 4371839 := bstep (se 1 (by rfl) ⟨3278879, by rfl⟩ : syracuseStep 4371839 = 6557759) B6557759
theorem B2914559 : Blo 1941435 2914559 := bstep (se 1 (by rfl) ⟨2185919, by rfl⟩ : syracuseStep 2914559 = 4371839) B4371839
theorem B1943039 : Blo 1941435 1943039 := bstep (se 1 (by rfl) ⟨1457279, by rfl⟩ : syracuseStep 1943039 = 2914559) B2914559
theorem B2914565 : Blo 1941435 2914565 := bbase (se 4 (by rfl) ⟨273240, by rfl⟩ : syracuseStep 2914565 = 546481) (by norm_num)
theorem B1943043 : Blo 1941435 1943043 := bstep (se 1 (by rfl) ⟨1457282, by rfl⟩ : syracuseStep 1943043 = 2914565) B2914565
theorem B3278893 : Blo 1941435 3278893 := bbase (se 3 (by rfl) ⟨614792, by rfl⟩ : syracuseStep 3278893 = 1229585) (by norm_num)
theorem B4371857 : Blo 1941435 4371857 := bstep (se 2 (by rfl) ⟨1639446, by rfl⟩ : syracuseStep 4371857 = 3278893) B3278893
theorem B2914571 : Blo 1941435 2914571 := bstep (se 1 (by rfl) ⟨2185928, by rfl⟩ : syracuseStep 2914571 = 4371857) B4371857
theorem B1943047 : Blo 1941435 1943047 := bstep (se 1 (by rfl) ⟨1457285, by rfl⟩ : syracuseStep 1943047 = 2914571) B2914571
theorem B2185933 : Blo 1941435 2185933 := bbase (se 3 (by rfl) ⟨409862, by rfl⟩ : syracuseStep 2185933 = 819725) (by norm_num)
theorem B2914577 : Blo 1941435 2914577 := bstep (se 2 (by rfl) ⟨1092966, by rfl⟩ : syracuseStep 2914577 = 2185933) B2185933
theorem B1943051 : Blo 1941435 1943051 := bstep (se 1 (by rfl) ⟨1457288, by rfl⟩ : syracuseStep 1943051 = 2914577) B2914577
theorem B6557813 : Blo 1941435 6557813 := bbase (se 5 (by rfl) ⟨307397, by rfl⟩ : syracuseStep 6557813 = 614795) (by norm_num)
theorem B4371875 : Blo 1941435 4371875 := bstep (se 1 (by rfl) ⟨3278906, by rfl⟩ : syracuseStep 4371875 = 6557813) B6557813
theorem B2914583 : Blo 1941435 2914583 := bstep (se 1 (by rfl) ⟨2185937, by rfl⟩ : syracuseStep 2914583 = 4371875) B4371875
theorem B1943055 : Blo 1941435 1943055 := bstep (se 1 (by rfl) ⟨1457291, by rfl⟩ : syracuseStep 1943055 = 2914583) B2914583
theorem B2914589 : Blo 1941435 2914589 := bbase (se 3 (by rfl) ⟨546485, by rfl⟩ : syracuseStep 2914589 = 1092971) (by norm_num)
theorem B1943059 : Blo 1941435 1943059 := bstep (se 1 (by rfl) ⟨1457294, by rfl⟩ : syracuseStep 1943059 = 2914589) B2914589
theorem B4371893 : Blo 1941435 4371893 := bbase (se 5 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 4371893 = 409865) (by norm_num)
theorem B2914595 : Blo 1941435 2914595 := bstep (se 1 (by rfl) ⟨2185946, by rfl⟩ : syracuseStep 2914595 = 4371893) B4371893
theorem B1943063 : Blo 1941435 1943063 := bstep (se 1 (by rfl) ⟨1457297, by rfl⟩ : syracuseStep 1943063 = 2914595) B2914595
theorem B4149893 : Blo 1941435 4149893 := bbase (se 4 (by rfl) ⟨389052, by rfl⟩ : syracuseStep 4149893 = 778105) (by norm_num)
theorem B11066381 : Blo 1941435 11066381 := bstep (se 3 (by rfl) ⟨2074946, by rfl⟩ : syracuseStep 11066381 = 4149893) B4149893
theorem B7377587 : Blo 1941435 7377587 := bstep (se 1 (by rfl) ⟨5533190, by rfl⟩ : syracuseStep 7377587 = 11066381) B11066381
theorem B4918391 : Blo 1941435 4918391 := bstep (se 1 (by rfl) ⟨3688793, by rfl⟩ : syracuseStep 4918391 = 7377587) B7377587
theorem B3278927 : Blo 1941435 3278927 := bstep (se 1 (by rfl) ⟨2459195, by rfl⟩ : syracuseStep 3278927 = 4918391) B4918391
theorem B2185951 : Blo 1941435 2185951 := bstep (se 1 (by rfl) ⟨1639463, by rfl⟩ : syracuseStep 2185951 = 3278927) B3278927
theorem B2914601 : Blo 1941435 2914601 := bstep (se 2 (by rfl) ⟨1092975, by rfl⟩ : syracuseStep 2914601 = 2185951) B2185951
theorem B1943067 : Blo 1941435 1943067 := bstep (se 1 (by rfl) ⟨1457300, by rfl⟩ : syracuseStep 1943067 = 2914601) B2914601
theorem B4149901 : Blo 1941435 4149901 := bbase (se 3 (by rfl) ⟨778106, by rfl⟩ : syracuseStep 4149901 = 1556213) (by norm_num)
theorem B5533201 : Blo 1941435 5533201 := bstep (se 2 (by rfl) ⟨2074950, by rfl⟩ : syracuseStep 5533201 = 4149901) B4149901
theorem B7377601 : Blo 1941435 7377601 := bstep (se 2 (by rfl) ⟨2766600, by rfl⟩ : syracuseStep 7377601 = 5533201) B5533201
theorem B9836801 : Blo 1941435 9836801 := bstep (se 2 (by rfl) ⟨3688800, by rfl⟩ : syracuseStep 9836801 = 7377601) B7377601
theorem B6557867 : Blo 1941435 6557867 := bstep (se 1 (by rfl) ⟨4918400, by rfl⟩ : syracuseStep 6557867 = 9836801) B9836801
theorem B4371911 : Blo 1941435 4371911 := bstep (se 1 (by rfl) ⟨3278933, by rfl⟩ : syracuseStep 4371911 = 6557867) B6557867
theorem B2914607 : Blo 1941435 2914607 := bstep (se 1 (by rfl) ⟨2185955, by rfl⟩ : syracuseStep 2914607 = 4371911) B4371911
theorem B1943071 : Blo 1941435 1943071 := bstep (se 1 (by rfl) ⟨1457303, by rfl⟩ : syracuseStep 1943071 = 2914607) B2914607
theorem B2914613 : Blo 1941435 2914613 := bbase (se 5 (by rfl) ⟨136622, by rfl⟩ : syracuseStep 2914613 = 273245) (by norm_num)
theorem B1943075 : Blo 1941435 1943075 := bstep (se 1 (by rfl) ⟨1457306, by rfl⟩ : syracuseStep 1943075 = 2914613) B2914613
theorem B4918421 : Blo 1941435 4918421 := bbase (se 6 (by rfl) ⟨115275, by rfl⟩ : syracuseStep 4918421 = 230551) (by norm_num)
theorem B3278947 : Blo 1941435 3278947 := bstep (se 1 (by rfl) ⟨2459210, by rfl⟩ : syracuseStep 3278947 = 4918421) B4918421
theorem B4371929 : Blo 1941435 4371929 := bstep (se 2 (by rfl) ⟨1639473, by rfl⟩ : syracuseStep 4371929 = 3278947) B3278947
theorem B2914619 : Blo 1941435 2914619 := bstep (se 1 (by rfl) ⟨2185964, by rfl⟩ : syracuseStep 2914619 = 4371929) B4371929
theorem B1943079 : Blo 1941435 1943079 := bstep (se 1 (by rfl) ⟨1457309, by rfl⟩ : syracuseStep 1943079 = 2914619) B2914619
theorem B2185969 : Blo 1941435 2185969 := bbase (se 2 (by rfl) ⟨819738, by rfl⟩ : syracuseStep 2185969 = 1639477) (by norm_num)
theorem B2914625 : Blo 1941435 2914625 := bstep (se 2 (by rfl) ⟨1092984, by rfl⟩ : syracuseStep 2914625 = 2185969) B2185969
theorem B1943083 : Blo 1941435 1943083 := bstep (se 1 (by rfl) ⟨1457312, by rfl⟩ : syracuseStep 1943083 = 2914625) B2914625
theorem B3939197 : Blo 1941435 3939197 := bbase (se 3 (by rfl) ⟨738599, by rfl⟩ : syracuseStep 3939197 = 1477199) (by norm_num)
theorem B42018101 : Blo 1941435 42018101 := bstep (se 5 (by rfl) ⟨1969598, by rfl⟩ : syracuseStep 42018101 = 3939197) B3939197
theorem B28012067 : Blo 1941435 28012067 := bstep (se 1 (by rfl) ⟨21009050, by rfl⟩ : syracuseStep 28012067 = 42018101) B42018101
theorem B18674711 : Blo 1941435 18674711 := bstep (se 1 (by rfl) ⟨14006033, by rfl⟩ : syracuseStep 18674711 = 28012067) B28012067
theorem B12449807 : Blo 1941435 12449807 := bstep (se 1 (by rfl) ⟨9337355, by rfl⟩ : syracuseStep 12449807 = 18674711) B18674711
theorem B8299871 : Blo 1941435 8299871 := bstep (se 1 (by rfl) ⟨6224903, by rfl⟩ : syracuseStep 8299871 = 12449807) B12449807
theorem B5533247 : Blo 1941435 5533247 := bstep (se 1 (by rfl) ⟨4149935, by rfl⟩ : syracuseStep 5533247 = 8299871) B8299871
theorem B3688831 : Blo 1941435 3688831 := bstep (se 1 (by rfl) ⟨2766623, by rfl⟩ : syracuseStep 3688831 = 5533247) B5533247
theorem B4918441 : Blo 1941435 4918441 := bstep (se 2 (by rfl) ⟨1844415, by rfl⟩ : syracuseStep 4918441 = 3688831) B3688831
theorem B6557921 : Blo 1941435 6557921 := bstep (se 2 (by rfl) ⟨2459220, by rfl⟩ : syracuseStep 6557921 = 4918441) B4918441
theorem B4371947 : Blo 1941435 4371947 := bstep (se 1 (by rfl) ⟨3278960, by rfl⟩ : syracuseStep 4371947 = 6557921) B6557921
theorem B2914631 : Blo 1941435 2914631 := bstep (se 1 (by rfl) ⟨2185973, by rfl⟩ : syracuseStep 2914631 = 4371947) B4371947
theorem B1943087 : Blo 1941435 1943087 := bstep (se 1 (by rfl) ⟨1457315, by rfl⟩ : syracuseStep 1943087 = 2914631) B2914631
theorem B2914637 : Blo 1941435 2914637 := bbase (se 3 (by rfl) ⟨546494, by rfl⟩ : syracuseStep 2914637 = 1092989) (by norm_num)
theorem B1943091 : Blo 1941435 1943091 := bstep (se 1 (by rfl) ⟨1457318, by rfl⟩ : syracuseStep 1943091 = 2914637) B2914637
theorem B4371965 : Blo 1941435 4371965 := bbase (se 3 (by rfl) ⟨819743, by rfl⟩ : syracuseStep 4371965 = 1639487) (by norm_num)
theorem B2914643 : Blo 1941435 2914643 := bstep (se 1 (by rfl) ⟨2185982, by rfl⟩ : syracuseStep 2914643 = 4371965) B4371965
theorem B1943095 : Blo 1941435 1943095 := bstep (se 1 (by rfl) ⟨1457321, by rfl⟩ : syracuseStep 1943095 = 2914643) B2914643
theorem B3278981 : Blo 1941435 3278981 := bbase (se 4 (by rfl) ⟨307404, by rfl⟩ : syracuseStep 3278981 = 614809) (by norm_num)
theorem B2185987 : Blo 1941435 2185987 := bstep (se 1 (by rfl) ⟨1639490, by rfl⟩ : syracuseStep 2185987 = 3278981) B3278981
theorem B2914649 : Blo 1941435 2914649 := bstep (se 2 (by rfl) ⟨1092993, by rfl⟩ : syracuseStep 2914649 = 2185987) B2185987
theorem B1943099 : Blo 1941435 1943099 := bstep (se 1 (by rfl) ⟨1457324, by rfl⟩ : syracuseStep 1943099 = 2914649) B2914649
theorem B14755445 : Blo 1941435 14755445 := bbase (se 5 (by rfl) ⟨691661, by rfl⟩ : syracuseStep 14755445 = 1383323) (by norm_num)
theorem B9836963 : Blo 1941435 9836963 := bstep (se 1 (by rfl) ⟨7377722, by rfl⟩ : syracuseStep 9836963 = 14755445) B14755445
theorem B6557975 : Blo 1941435 6557975 := bstep (se 1 (by rfl) ⟨4918481, by rfl⟩ : syracuseStep 6557975 = 9836963) B9836963
theorem B4371983 : Blo 1941435 4371983 := bstep (se 1 (by rfl) ⟨3278987, by rfl⟩ : syracuseStep 4371983 = 6557975) B6557975
theorem B2914655 : Blo 1941435 2914655 := bstep (se 1 (by rfl) ⟨2185991, by rfl⟩ : syracuseStep 2914655 = 4371983) B4371983
theorem B1943103 : Blo 1941435 1943103 := bstep (se 1 (by rfl) ⟨1457327, by rfl⟩ : syracuseStep 1943103 = 2914655) B2914655
theorem B2914661 : Blo 1941435 2914661 := bbase (se 4 (by rfl) ⟨273249, by rfl⟩ : syracuseStep 2914661 = 546499) (by norm_num)
theorem B1943107 : Blo 1941435 1943107 := bstep (se 1 (by rfl) ⟨1457330, by rfl⟩ : syracuseStep 1943107 = 2914661) B2914661
theorem B3688877 : Blo 1941435 3688877 := bbase (se 3 (by rfl) ⟨691664, by rfl⟩ : syracuseStep 3688877 = 1383329) (by norm_num)
theorem B2459251 : Blo 1941435 2459251 := bstep (se 1 (by rfl) ⟨1844438, by rfl⟩ : syracuseStep 2459251 = 3688877) B3688877
theorem B3279001 : Blo 1941435 3279001 := bstep (se 2 (by rfl) ⟨1229625, by rfl⟩ : syracuseStep 3279001 = 2459251) B2459251
theorem B4372001 : Blo 1941435 4372001 := bstep (se 2 (by rfl) ⟨1639500, by rfl⟩ : syracuseStep 4372001 = 3279001) B3279001
theorem B2914667 : Blo 1941435 2914667 := bstep (se 1 (by rfl) ⟨2186000, by rfl⟩ : syracuseStep 2914667 = 4372001) B4372001
theorem B1943111 : Blo 1941435 1943111 := bstep (se 1 (by rfl) ⟨1457333, by rfl⟩ : syracuseStep 1943111 = 2914667) B2914667
theorem B2186005 : Blo 1941435 2186005 := bbase (se 6 (by rfl) ⟨51234, by rfl⟩ : syracuseStep 2186005 = 102469) (by norm_num)
theorem B2914673 : Blo 1941435 2914673 := bstep (se 2 (by rfl) ⟨1093002, by rfl⟩ : syracuseStep 2914673 = 2186005) B2186005
theorem B1943115 : Blo 1941435 1943115 := bstep (se 1 (by rfl) ⟨1457336, by rfl⟩ : syracuseStep 1943115 = 2914673) B2914673
theorem B2459261 : Blo 1941435 2459261 := bbase (se 3 (by rfl) ⟨461111, by rfl⟩ : syracuseStep 2459261 = 922223) (by norm_num)
theorem B6558029 : Blo 1941435 6558029 := bstep (se 3 (by rfl) ⟨1229630, by rfl⟩ : syracuseStep 6558029 = 2459261) B2459261
theorem B4372019 : Blo 1941435 4372019 := bstep (se 1 (by rfl) ⟨3279014, by rfl⟩ : syracuseStep 4372019 = 6558029) B6558029
theorem B2914679 : Blo 1941435 2914679 := bstep (se 1 (by rfl) ⟨2186009, by rfl⟩ : syracuseStep 2914679 = 4372019) B4372019
theorem B1943119 : Blo 1941435 1943119 := bstep (se 1 (by rfl) ⟨1457339, by rfl⟩ : syracuseStep 1943119 = 2914679) B2914679
theorem B2914685 : Blo 1941435 2914685 := bbase (se 3 (by rfl) ⟨546503, by rfl⟩ : syracuseStep 2914685 = 1093007) (by norm_num)
theorem B1943123 : Blo 1941435 1943123 := bstep (se 1 (by rfl) ⟨1457342, by rfl⟩ : syracuseStep 1943123 = 2914685) B2914685
theorem B4372037 : Blo 1941435 4372037 := bbase (se 4 (by rfl) ⟨409878, by rfl⟩ : syracuseStep 4372037 = 819757) (by norm_num)
theorem B2914691 : Blo 1941435 2914691 := bstep (se 1 (by rfl) ⟨2186018, by rfl⟩ : syracuseStep 2914691 = 4372037) B4372037
theorem B1943127 : Blo 1941435 1943127 := bstep (se 1 (by rfl) ⟨1457345, by rfl⟩ : syracuseStep 1943127 = 2914691) B2914691
theorem B3501589 : Blo 1941435 3501589 := bbase (se 6 (by rfl) ⟨82068, by rfl⟩ : syracuseStep 3501589 = 164137) (by norm_num)
theorem B4668785 : Blo 1941435 4668785 := bstep (se 2 (by rfl) ⟨1750794, by rfl⟩ : syracuseStep 4668785 = 3501589) B3501589
theorem B3112523 : Blo 1941435 3112523 := bstep (se 1 (by rfl) ⟨2334392, by rfl⟩ : syracuseStep 3112523 = 4668785) B4668785
theorem B2075015 : Blo 1941435 2075015 := bstep (se 1 (by rfl) ⟨1556261, by rfl⟩ : syracuseStep 2075015 = 3112523) B3112523
theorem B5533373 : Blo 1941435 5533373 := bstep (se 3 (by rfl) ⟨1037507, by rfl⟩ : syracuseStep 5533373 = 2075015) B2075015
theorem B3688915 : Blo 1941435 3688915 := bstep (se 1 (by rfl) ⟨2766686, by rfl⟩ : syracuseStep 3688915 = 5533373) B5533373
theorem B4918553 : Blo 1941435 4918553 := bstep (se 2 (by rfl) ⟨1844457, by rfl⟩ : syracuseStep 4918553 = 3688915) B3688915
theorem B3279035 : Blo 1941435 3279035 := bstep (se 1 (by rfl) ⟨2459276, by rfl⟩ : syracuseStep 3279035 = 4918553) B4918553
theorem B2186023 : Blo 1941435 2186023 := bstep (se 1 (by rfl) ⟨1639517, by rfl⟩ : syracuseStep 2186023 = 3279035) B3279035
theorem B2914697 : Blo 1941435 2914697 := bstep (se 2 (by rfl) ⟨1093011, by rfl⟩ : syracuseStep 2914697 = 2186023) B2186023
theorem B1943131 : Blo 1941435 1943131 := bstep (se 1 (by rfl) ⟨1457348, by rfl⟩ : syracuseStep 1943131 = 2914697) B2914697
theorem B9837125 : Blo 1941435 9837125 := bbase (se 4 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 9837125 = 1844461) (by norm_num)
theorem B6558083 : Blo 1941435 6558083 := bstep (se 1 (by rfl) ⟨4918562, by rfl⟩ : syracuseStep 6558083 = 9837125) B9837125
theorem B4372055 : Blo 1941435 4372055 := bstep (se 1 (by rfl) ⟨3279041, by rfl⟩ : syracuseStep 4372055 = 6558083) B6558083
theorem B2914703 : Blo 1941435 2914703 := bstep (se 1 (by rfl) ⟨2186027, by rfl⟩ : syracuseStep 2914703 = 4372055) B4372055
theorem B1943135 : Blo 1941435 1943135 := bstep (se 1 (by rfl) ⟨1457351, by rfl⟩ : syracuseStep 1943135 = 2914703) B2914703
theorem B2914709 : Blo 1941435 2914709 := bbase (se 6 (by rfl) ⟨68313, by rfl⟩ : syracuseStep 2914709 = 136627) (by norm_num)
theorem B1943139 : Blo 1941435 1943139 := bstep (se 1 (by rfl) ⟨1457354, by rfl⟩ : syracuseStep 1943139 = 2914709) B2914709
theorem B1996529 : Blo 1941435 1996529 := bbase (se 2 (by rfl) ⟨748698, by rfl⟩ : syracuseStep 1996529 = 1497397) (by norm_num)
theorem B5324077 : Blo 1941435 5324077 := bstep (se 3 (by rfl) ⟨998264, by rfl⟩ : syracuseStep 5324077 = 1996529) B1996529
theorem B7098769 : Blo 1941435 7098769 := bstep (se 2 (by rfl) ⟨2662038, by rfl⟩ : syracuseStep 7098769 = 5324077) B5324077
theorem B9465025 : Blo 1941435 9465025 := bstep (se 2 (by rfl) ⟨3549384, by rfl⟩ : syracuseStep 9465025 = 7098769) B7098769
theorem B12620033 : Blo 1941435 12620033 := bstep (se 2 (by rfl) ⟨4732512, by rfl⟩ : syracuseStep 12620033 = 9465025) B9465025
theorem B8413355 : Blo 1941435 8413355 := bstep (se 1 (by rfl) ⟨6310016, by rfl⟩ : syracuseStep 8413355 = 12620033) B12620033
theorem B22435613 : Blo 1941435 22435613 := bstep (se 3 (by rfl) ⟨4206677, by rfl⟩ : syracuseStep 22435613 = 8413355) B8413355
theorem B14957075 : Blo 1941435 14957075 := bstep (se 1 (by rfl) ⟨11217806, by rfl⟩ : syracuseStep 14957075 = 22435613) B22435613
theorem B9971383 : Blo 1941435 9971383 := bstep (se 1 (by rfl) ⟨7478537, by rfl⟩ : syracuseStep 9971383 = 14957075) B14957075
theorem B13295177 : Blo 1941435 13295177 := bstep (se 2 (by rfl) ⟨4985691, by rfl⟩ : syracuseStep 13295177 = 9971383) B9971383
theorem B8863451 : Blo 1941435 8863451 := bstep (se 1 (by rfl) ⟨6647588, by rfl⟩ : syracuseStep 8863451 = 13295177) B13295177
theorem B5908967 : Blo 1941435 5908967 := bstep (se 1 (by rfl) ⟨4431725, by rfl⟩ : syracuseStep 5908967 = 8863451) B8863451
theorem B3939311 : Blo 1941435 3939311 := bstep (se 1 (by rfl) ⟨2954483, by rfl⟩ : syracuseStep 3939311 = 5908967) B5908967
theorem B10504829 : Blo 1941435 10504829 := bstep (se 3 (by rfl) ⟨1969655, by rfl⟩ : syracuseStep 10504829 = 3939311) B3939311
theorem B7003219 : Blo 1941435 7003219 := bstep (se 1 (by rfl) ⟨5252414, by rfl⟩ : syracuseStep 7003219 = 10504829) B10504829
theorem B9337625 : Blo 1941435 9337625 := bstep (se 2 (by rfl) ⟨3501609, by rfl⟩ : syracuseStep 9337625 = 7003219) B7003219
theorem B6225083 : Blo 1941435 6225083 := bstep (se 1 (by rfl) ⟨4668812, by rfl⟩ : syracuseStep 6225083 = 9337625) B9337625
theorem B4150055 : Blo 1941435 4150055 := bstep (se 1 (by rfl) ⟨3112541, by rfl⟩ : syracuseStep 4150055 = 6225083) B6225083
theorem B11066813 : Blo 1941435 11066813 := bstep (se 3 (by rfl) ⟨2075027, by rfl⟩ : syracuseStep 11066813 = 4150055) B4150055
theorem B7377875 : Blo 1941435 7377875 := bstep (se 1 (by rfl) ⟨5533406, by rfl⟩ : syracuseStep 7377875 = 11066813) B11066813
theorem B4918583 : Blo 1941435 4918583 := bstep (se 1 (by rfl) ⟨3688937, by rfl⟩ : syracuseStep 4918583 = 7377875) B7377875
theorem B3279055 : Blo 1941435 3279055 := bstep (se 1 (by rfl) ⟨2459291, by rfl⟩ : syracuseStep 3279055 = 4918583) B4918583
theorem B4372073 : Blo 1941435 4372073 := bstep (se 2 (by rfl) ⟨1639527, by rfl⟩ : syracuseStep 4372073 = 3279055) B3279055
theorem B2914715 : Blo 1941435 2914715 := bstep (se 1 (by rfl) ⟨2186036, by rfl⟩ : syracuseStep 2914715 = 4372073) B4372073
theorem B1943143 : Blo 1941435 1943143 := bstep (se 1 (by rfl) ⟨1457357, by rfl⟩ : syracuseStep 1943143 = 2914715) B2914715
theorem B2186041 : Blo 1941435 2186041 := bbase (se 2 (by rfl) ⟨819765, by rfl⟩ : syracuseStep 2186041 = 1639531) (by norm_num)
theorem B2914721 : Blo 1941435 2914721 := bstep (se 2 (by rfl) ⟨1093020, by rfl⟩ : syracuseStep 2914721 = 2186041) B2186041
theorem B1943147 : Blo 1941435 1943147 := bstep (se 1 (by rfl) ⟨1457360, by rfl⟩ : syracuseStep 1943147 = 2914721) B2914721
theorem B5533429 : Blo 1941435 5533429 := bbase (se 5 (by rfl) ⟨259379, by rfl⟩ : syracuseStep 5533429 = 518759) (by norm_num)
theorem B7377905 : Blo 1941435 7377905 := bstep (se 2 (by rfl) ⟨2766714, by rfl⟩ : syracuseStep 7377905 = 5533429) B5533429
theorem B4918603 : Blo 1941435 4918603 := bstep (se 1 (by rfl) ⟨3688952, by rfl⟩ : syracuseStep 4918603 = 7377905) B7377905
theorem B6558137 : Blo 1941435 6558137 := bstep (se 2 (by rfl) ⟨2459301, by rfl⟩ : syracuseStep 6558137 = 4918603) B4918603
theorem B4372091 : Blo 1941435 4372091 := bstep (se 1 (by rfl) ⟨3279068, by rfl⟩ : syracuseStep 4372091 = 6558137) B6558137
theorem B2914727 : Blo 1941435 2914727 := bstep (se 1 (by rfl) ⟨2186045, by rfl⟩ : syracuseStep 2914727 = 4372091) B4372091
theorem B1943151 : Blo 1941435 1943151 := bstep (se 1 (by rfl) ⟨1457363, by rfl⟩ : syracuseStep 1943151 = 2914727) B2914727
theorem B2914733 : Blo 1941435 2914733 := bbase (se 3 (by rfl) ⟨546512, by rfl⟩ : syracuseStep 2914733 = 1093025) (by norm_num)
theorem B1943155 : Blo 1941435 1943155 := bstep (se 1 (by rfl) ⟨1457366, by rfl⟩ : syracuseStep 1943155 = 2914733) B2914733
theorem B4372109 : Blo 1941435 4372109 := bbase (se 3 (by rfl) ⟨819770, by rfl⟩ : syracuseStep 4372109 = 1639541) (by norm_num)
theorem B2914739 : Blo 1941435 2914739 := bstep (se 1 (by rfl) ⟨2186054, by rfl⟩ : syracuseStep 2914739 = 4372109) B4372109
theorem B1943159 : Blo 1941435 1943159 := bstep (se 1 (by rfl) ⟨1457369, by rfl⟩ : syracuseStep 1943159 = 2914739) B2914739
theorem B2459317 : Blo 1941435 2459317 := bbase (se 5 (by rfl) ⟨115280, by rfl⟩ : syracuseStep 2459317 = 230561) (by norm_num)
theorem B3279089 : Blo 1941435 3279089 := bstep (se 2 (by rfl) ⟨1229658, by rfl⟩ : syracuseStep 3279089 = 2459317) B2459317
theorem B2186059 : Blo 1941435 2186059 := bstep (se 1 (by rfl) ⟨1639544, by rfl⟩ : syracuseStep 2186059 = 3279089) B3279089
theorem B2914745 : Blo 1941435 2914745 := bstep (se 2 (by rfl) ⟨1093029, by rfl⟩ : syracuseStep 2914745 = 2186059) B2186059
theorem B1943163 : Blo 1941435 1943163 := bstep (se 1 (by rfl) ⟨1457372, by rfl⟩ : syracuseStep 1943163 = 2914745) B2914745
theorem B201922901 : Blo 1941435 201922901 := bbase (se 10 (by rfl) ⟨295785, by rfl⟩ : syracuseStep 201922901 = 591571) (by norm_num)
theorem B134615267 : Blo 1941435 134615267 := bstep (se 1 (by rfl) ⟨100961450, by rfl⟩ : syracuseStep 134615267 = 201922901) B201922901
theorem B89743511 : Blo 1941435 89743511 := bstep (se 1 (by rfl) ⟨67307633, by rfl⟩ : syracuseStep 89743511 = 134615267) B134615267
theorem B239316029 : Blo 1941435 239316029 := bstep (se 3 (by rfl) ⟨44871755, by rfl⟩ : syracuseStep 239316029 = 89743511) B89743511
theorem B159544019 : Blo 1941435 159544019 := bstep (se 1 (by rfl) ⟨119658014, by rfl⟩ : syracuseStep 159544019 = 239316029) B239316029
theorem B106362679 : Blo 1941435 106362679 := bstep (se 1 (by rfl) ⟨79772009, by rfl⟩ : syracuseStep 106362679 = 159544019) B159544019
theorem B141816905 : Blo 1941435 141816905 := bstep (se 2 (by rfl) ⟨53181339, by rfl⟩ : syracuseStep 141816905 = 106362679) B106362679
theorem B94544603 : Blo 1941435 94544603 := bstep (se 1 (by rfl) ⟨70908452, by rfl⟩ : syracuseStep 94544603 = 141816905) B141816905
theorem B63029735 : Blo 1941435 63029735 := bstep (se 1 (by rfl) ⟨47272301, by rfl⟩ : syracuseStep 63029735 = 94544603) B94544603
theorem B42019823 : Blo 1941435 42019823 := bstep (se 1 (by rfl) ⟨31514867, by rfl⟩ : syracuseStep 42019823 = 63029735) B63029735
theorem B28013215 : Blo 1941435 28013215 := bstep (se 1 (by rfl) ⟨21009911, by rfl⟩ : syracuseStep 28013215 = 42019823) B42019823
theorem B37350953 : Blo 1941435 37350953 := bstep (se 2 (by rfl) ⟨14006607, by rfl⟩ : syracuseStep 37350953 = 28013215) B28013215
theorem B24900635 : Blo 1941435 24900635 := bstep (se 1 (by rfl) ⟨18675476, by rfl⟩ : syracuseStep 24900635 = 37350953) B37350953
theorem B16600423 : Blo 1941435 16600423 := bstep (se 1 (by rfl) ⟨12450317, by rfl⟩ : syracuseStep 16600423 = 24900635) B24900635
theorem B22133897 : Blo 1941435 22133897 := bstep (se 2 (by rfl) ⟨8300211, by rfl⟩ : syracuseStep 22133897 = 16600423) B16600423
theorem B14755931 : Blo 1941435 14755931 := bstep (se 1 (by rfl) ⟨11066948, by rfl⟩ : syracuseStep 14755931 = 22133897) B22133897
theorem B9837287 : Blo 1941435 9837287 := bstep (se 1 (by rfl) ⟨7377965, by rfl⟩ : syracuseStep 9837287 = 14755931) B14755931
theorem B6558191 : Blo 1941435 6558191 := bstep (se 1 (by rfl) ⟨4918643, by rfl⟩ : syracuseStep 6558191 = 9837287) B9837287
theorem B4372127 : Blo 1941435 4372127 := bstep (se 1 (by rfl) ⟨3279095, by rfl⟩ : syracuseStep 4372127 = 6558191) B6558191
theorem B2914751 : Blo 1941435 2914751 := bstep (se 1 (by rfl) ⟨2186063, by rfl⟩ : syracuseStep 2914751 = 4372127) B4372127
theorem B1943167 : Blo 1941435 1943167 := bstep (se 1 (by rfl) ⟨1457375, by rfl⟩ : syracuseStep 1943167 = 2914751) B2914751
theorem B2914757 : Blo 1941435 2914757 := bbase (se 4 (by rfl) ⟨273258, by rfl⟩ : syracuseStep 2914757 = 546517) (by norm_num)
theorem B1943171 : Blo 1941435 1943171 := bstep (se 1 (by rfl) ⟨1457378, by rfl⟩ : syracuseStep 1943171 = 2914757) B2914757
theorem B3279109 : Blo 1941435 3279109 := bbase (se 4 (by rfl) ⟨307416, by rfl⟩ : syracuseStep 3279109 = 614833) (by norm_num)
theorem B4372145 : Blo 1941435 4372145 := bstep (se 2 (by rfl) ⟨1639554, by rfl⟩ : syracuseStep 4372145 = 3279109) B3279109
theorem B2914763 : Blo 1941435 2914763 := bstep (se 1 (by rfl) ⟨2186072, by rfl⟩ : syracuseStep 2914763 = 4372145) B4372145
theorem B1943175 : Blo 1941435 1943175 := bstep (se 1 (by rfl) ⟨1457381, by rfl⟩ : syracuseStep 1943175 = 2914763) B2914763
theorem B2186077 : Blo 1941435 2186077 := bbase (se 3 (by rfl) ⟨409889, by rfl⟩ : syracuseStep 2186077 = 819779) (by norm_num)
theorem B2914769 : Blo 1941435 2914769 := bstep (se 2 (by rfl) ⟨1093038, by rfl⟩ : syracuseStep 2914769 = 2186077) B2186077
theorem B1943179 : Blo 1941435 1943179 := bstep (se 1 (by rfl) ⟨1457384, by rfl⟩ : syracuseStep 1943179 = 2914769) B2914769
theorem B6558245 : Blo 1941435 6558245 := bbase (se 4 (by rfl) ⟨614835, by rfl⟩ : syracuseStep 6558245 = 1229671) (by norm_num)
theorem B4372163 : Blo 1941435 4372163 := bstep (se 1 (by rfl) ⟨3279122, by rfl⟩ : syracuseStep 4372163 = 6558245) B6558245
theorem B2914775 : Blo 1941435 2914775 := bstep (se 1 (by rfl) ⟨2186081, by rfl⟩ : syracuseStep 2914775 = 4372163) B4372163
theorem B1943183 : Blo 1941435 1943183 := bstep (se 1 (by rfl) ⟨1457387, by rfl⟩ : syracuseStep 1943183 = 2914775) B2914775
theorem B2914781 : Blo 1941435 2914781 := bbase (se 3 (by rfl) ⟨546521, by rfl⟩ : syracuseStep 2914781 = 1093043) (by norm_num)
theorem B1943187 : Blo 1941435 1943187 := bstep (se 1 (by rfl) ⟨1457390, by rfl⟩ : syracuseStep 1943187 = 2914781) B2914781
theorem B4372181 : Blo 1941435 4372181 := bbase (se 7 (by rfl) ⟨51236, by rfl⟩ : syracuseStep 4372181 = 102473) (by norm_num)
theorem B2914787 : Blo 1941435 2914787 := bstep (se 1 (by rfl) ⟨2186090, by rfl⟩ : syracuseStep 2914787 = 4372181) B4372181
theorem B1943191 : Blo 1941435 1943191 := bstep (se 1 (by rfl) ⟨1457393, by rfl⟩ : syracuseStep 1943191 = 2914787) B2914787
theorem B2334469 : Blo 1941435 2334469 := bbase (se 4 (by rfl) ⟨218856, by rfl⟩ : syracuseStep 2334469 = 437713) (by norm_num)
theorem B3112625 : Blo 1941435 3112625 := bstep (se 2 (by rfl) ⟨1167234, by rfl⟩ : syracuseStep 3112625 = 2334469) B2334469
theorem B8300333 : Blo 1941435 8300333 := bstep (se 3 (by rfl) ⟨1556312, by rfl⟩ : syracuseStep 8300333 = 3112625) B3112625
theorem B5533555 : Blo 1941435 5533555 := bstep (se 1 (by rfl) ⟨4150166, by rfl⟩ : syracuseStep 5533555 = 8300333) B8300333
theorem B7378073 : Blo 1941435 7378073 := bstep (se 2 (by rfl) ⟨2766777, by rfl⟩ : syracuseStep 7378073 = 5533555) B5533555
theorem B4918715 : Blo 1941435 4918715 := bstep (se 1 (by rfl) ⟨3689036, by rfl⟩ : syracuseStep 4918715 = 7378073) B7378073
theorem B3279143 : Blo 1941435 3279143 := bstep (se 1 (by rfl) ⟨2459357, by rfl⟩ : syracuseStep 3279143 = 4918715) B4918715
theorem B2186095 : Blo 1941435 2186095 := bstep (se 1 (by rfl) ⟨1639571, by rfl⟩ : syracuseStep 2186095 = 3279143) B3279143
theorem B2914793 : Blo 1941435 2914793 := bstep (se 2 (by rfl) ⟨1093047, by rfl⟩ : syracuseStep 2914793 = 2186095) B2186095
theorem B1943195 : Blo 1941435 1943195 := bstep (se 1 (by rfl) ⟨1457396, by rfl⟩ : syracuseStep 1943195 = 2914793) B2914793
theorem B4206797 : Blo 1941435 4206797 := bbase (se 3 (by rfl) ⟨788774, by rfl⟩ : syracuseStep 4206797 = 1577549) (by norm_num)
theorem B44872501 : Blo 1941435 44872501 := bstep (se 5 (by rfl) ⟨2103398, by rfl⟩ : syracuseStep 44872501 = 4206797) B4206797
theorem B59830001 : Blo 1941435 59830001 := bstep (se 2 (by rfl) ⟨22436250, by rfl⟩ : syracuseStep 59830001 = 44872501) B44872501
theorem B39886667 : Blo 1941435 39886667 := bstep (se 1 (by rfl) ⟨29915000, by rfl⟩ : syracuseStep 39886667 = 59830001) B59830001
theorem B26591111 : Blo 1941435 26591111 := bstep (se 1 (by rfl) ⟨19943333, by rfl⟩ : syracuseStep 26591111 = 39886667) B39886667
theorem B17727407 : Blo 1941435 17727407 := bstep (se 1 (by rfl) ⟨13295555, by rfl⟩ : syracuseStep 17727407 = 26591111) B26591111
theorem B11818271 : Blo 1941435 11818271 := bstep (se 1 (by rfl) ⟨8863703, by rfl⟩ : syracuseStep 11818271 = 17727407) B17727407
theorem B31515389 : Blo 1941435 31515389 := bstep (se 3 (by rfl) ⟨5909135, by rfl⟩ : syracuseStep 31515389 = 11818271) B11818271
theorem B21010259 : Blo 1941435 21010259 := bstep (se 1 (by rfl) ⟨15757694, by rfl⟩ : syracuseStep 21010259 = 31515389) B31515389
theorem B14006839 : Blo 1941435 14006839 := bstep (se 1 (by rfl) ⟨10505129, by rfl⟩ : syracuseStep 14006839 = 21010259) B21010259
theorem B18675785 : Blo 1941435 18675785 := bstep (se 2 (by rfl) ⟨7003419, by rfl⟩ : syracuseStep 18675785 = 14006839) B14006839
theorem B12450523 : Blo 1941435 12450523 := bstep (se 1 (by rfl) ⟨9337892, by rfl⟩ : syracuseStep 12450523 = 18675785) B18675785
theorem B16600697 : Blo 1941435 16600697 := bstep (se 2 (by rfl) ⟨6225261, by rfl⟩ : syracuseStep 16600697 = 12450523) B12450523
theorem B11067131 : Blo 1941435 11067131 := bstep (se 1 (by rfl) ⟨8300348, by rfl⟩ : syracuseStep 11067131 = 16600697) B16600697
theorem B7378087 : Blo 1941435 7378087 := bstep (se 1 (by rfl) ⟨5533565, by rfl⟩ : syracuseStep 7378087 = 11067131) B11067131
theorem B9837449 : Blo 1941435 9837449 := bstep (se 2 (by rfl) ⟨3689043, by rfl⟩ : syracuseStep 9837449 = 7378087) B7378087
theorem B6558299 : Blo 1941435 6558299 := bstep (se 1 (by rfl) ⟨4918724, by rfl⟩ : syracuseStep 6558299 = 9837449) B9837449
theorem B4372199 : Blo 1941435 4372199 := bstep (se 1 (by rfl) ⟨3279149, by rfl⟩ : syracuseStep 4372199 = 6558299) B6558299
theorem B2914799 : Blo 1941435 2914799 := bstep (se 1 (by rfl) ⟨2186099, by rfl⟩ : syracuseStep 2914799 = 4372199) B4372199
theorem B1943199 : Blo 1941435 1943199 := bstep (se 1 (by rfl) ⟨1457399, by rfl⟩ : syracuseStep 1943199 = 2914799) B2914799
theorem B2914805 : Blo 1941435 2914805 := bbase (se 5 (by rfl) ⟨136631, by rfl⟩ : syracuseStep 2914805 = 273263) (by norm_num)
theorem B1943203 : Blo 1941435 1943203 := bstep (se 1 (by rfl) ⟨1457402, by rfl⟩ : syracuseStep 1943203 = 2914805) B2914805
theorem B5533589 : Blo 1941435 5533589 := bbase (se 6 (by rfl) ⟨129693, by rfl⟩ : syracuseStep 5533589 = 259387) (by norm_num)
theorem B3689059 : Blo 1941435 3689059 := bstep (se 1 (by rfl) ⟨2766794, by rfl⟩ : syracuseStep 3689059 = 5533589) B5533589
theorem B4918745 : Blo 1941435 4918745 := bstep (se 2 (by rfl) ⟨1844529, by rfl⟩ : syracuseStep 4918745 = 3689059) B3689059
theorem B3279163 : Blo 1941435 3279163 := bstep (se 1 (by rfl) ⟨2459372, by rfl⟩ : syracuseStep 3279163 = 4918745) B4918745
theorem B4372217 : Blo 1941435 4372217 := bstep (se 2 (by rfl) ⟨1639581, by rfl⟩ : syracuseStep 4372217 = 3279163) B3279163
theorem B2914811 : Blo 1941435 2914811 := bstep (se 1 (by rfl) ⟨2186108, by rfl⟩ : syracuseStep 2914811 = 4372217) B4372217
theorem B1943207 : Blo 1941435 1943207 := bstep (se 1 (by rfl) ⟨1457405, by rfl⟩ : syracuseStep 1943207 = 2914811) B2914811
theorem B2186113 : Blo 1941435 2186113 := bbase (se 2 (by rfl) ⟨819792, by rfl⟩ : syracuseStep 2186113 = 1639585) (by norm_num)
theorem B2914817 : Blo 1941435 2914817 := bstep (se 2 (by rfl) ⟨1093056, by rfl⟩ : syracuseStep 2914817 = 2186113) B2186113
theorem B1943211 : Blo 1941435 1943211 := bstep (se 1 (by rfl) ⟨1457408, by rfl⟩ : syracuseStep 1943211 = 2914817) B2914817
theorem B4918765 : Blo 1941435 4918765 := bbase (se 3 (by rfl) ⟨922268, by rfl⟩ : syracuseStep 4918765 = 1844537) (by norm_num)
theorem B6558353 : Blo 1941435 6558353 := bstep (se 2 (by rfl) ⟨2459382, by rfl⟩ : syracuseStep 6558353 = 4918765) B4918765
theorem B4372235 : Blo 1941435 4372235 := bstep (se 1 (by rfl) ⟨3279176, by rfl⟩ : syracuseStep 4372235 = 6558353) B6558353
theorem B2914823 : Blo 1941435 2914823 := bstep (se 1 (by rfl) ⟨2186117, by rfl⟩ : syracuseStep 2914823 = 4372235) B4372235
theorem B1943215 : Blo 1941435 1943215 := bstep (se 1 (by rfl) ⟨1457411, by rfl⟩ : syracuseStep 1943215 = 2914823) B2914823
theorem B2914829 : Blo 1941435 2914829 := bbase (se 3 (by rfl) ⟨546530, by rfl⟩ : syracuseStep 2914829 = 1093061) (by norm_num)
theorem B1943219 : Blo 1941435 1943219 := bstep (se 1 (by rfl) ⟨1457414, by rfl⟩ : syracuseStep 1943219 = 2914829) B2914829
theorem B4372253 : Blo 1941435 4372253 := bbase (se 3 (by rfl) ⟨819797, by rfl⟩ : syracuseStep 4372253 = 1639595) (by norm_num)
theorem B2914835 : Blo 1941435 2914835 := bstep (se 1 (by rfl) ⟨2186126, by rfl⟩ : syracuseStep 2914835 = 4372253) B4372253
theorem B1943223 : Blo 1941435 1943223 := bstep (se 1 (by rfl) ⟨1457417, by rfl⟩ : syracuseStep 1943223 = 2914835) B2914835
theorem B3279197 : Blo 1941435 3279197 := bbase (se 3 (by rfl) ⟨614849, by rfl⟩ : syracuseStep 3279197 = 1229699) (by norm_num)
theorem B2186131 : Blo 1941435 2186131 := bstep (se 1 (by rfl) ⟨1639598, by rfl⟩ : syracuseStep 2186131 = 3279197) B3279197
theorem B2914841 : Blo 1941435 2914841 := bstep (se 2 (by rfl) ⟨1093065, by rfl⟩ : syracuseStep 2914841 = 2186131) B2186131
theorem B1943227 : Blo 1941435 1943227 := bstep (se 1 (by rfl) ⟨1457420, by rfl⟩ : syracuseStep 1943227 = 2914841) B2914841
theorem B8300485 : Blo 1941435 8300485 := bbase (se 4 (by rfl) ⟨778170, by rfl⟩ : syracuseStep 8300485 = 1556341) (by norm_num)
theorem B11067313 : Blo 1941435 11067313 := bstep (se 2 (by rfl) ⟨4150242, by rfl⟩ : syracuseStep 11067313 = 8300485) B8300485
theorem B14756417 : Blo 1941435 14756417 := bstep (se 2 (by rfl) ⟨5533656, by rfl⟩ : syracuseStep 14756417 = 11067313) B11067313
theorem B9837611 : Blo 1941435 9837611 := bstep (se 1 (by rfl) ⟨7378208, by rfl⟩ : syracuseStep 9837611 = 14756417) B14756417
theorem B6558407 : Blo 1941435 6558407 := bstep (se 1 (by rfl) ⟨4918805, by rfl⟩ : syracuseStep 6558407 = 9837611) B9837611
theorem B4372271 : Blo 1941435 4372271 := bstep (se 1 (by rfl) ⟨3279203, by rfl⟩ : syracuseStep 4372271 = 6558407) B6558407
theorem B2914847 : Blo 1941435 2914847 := bstep (se 1 (by rfl) ⟨2186135, by rfl⟩ : syracuseStep 2914847 = 4372271) B4372271
theorem B1943231 : Blo 1941435 1943231 := bstep (se 1 (by rfl) ⟨1457423, by rfl⟩ : syracuseStep 1943231 = 2914847) B2914847
theorem B2914853 : Blo 1941435 2914853 := bbase (se 4 (by rfl) ⟨273267, by rfl⟩ : syracuseStep 2914853 = 546535) (by norm_num)
theorem B1943235 : Blo 1941435 1943235 := bstep (se 1 (by rfl) ⟨1457426, by rfl⟩ : syracuseStep 1943235 = 2914853) B2914853
theorem B2459413 : Blo 1941435 2459413 := bbase (se 6 (by rfl) ⟨57642, by rfl⟩ : syracuseStep 2459413 = 115285) (by norm_num)
theorem B3279217 : Blo 1941435 3279217 := bstep (se 2 (by rfl) ⟨1229706, by rfl⟩ : syracuseStep 3279217 = 2459413) B2459413
theorem B4372289 : Blo 1941435 4372289 := bstep (se 2 (by rfl) ⟨1639608, by rfl⟩ : syracuseStep 4372289 = 3279217) B3279217
theorem B2914859 : Blo 1941435 2914859 := bstep (se 1 (by rfl) ⟨2186144, by rfl⟩ : syracuseStep 2914859 = 4372289) B4372289
theorem B1943239 : Blo 1941435 1943239 := bstep (se 1 (by rfl) ⟨1457429, by rfl⟩ : syracuseStep 1943239 = 2914859) B2914859
theorem B2186149 : Blo 1941435 2186149 := bbase (se 4 (by rfl) ⟨204951, by rfl⟩ : syracuseStep 2186149 = 409903) (by norm_num)
theorem B2914865 : Blo 1941435 2914865 := bstep (se 2 (by rfl) ⟨1093074, by rfl⟩ : syracuseStep 2914865 = 2186149) B2186149
theorem B1943243 : Blo 1941435 1943243 := bstep (se 1 (by rfl) ⟨1457432, by rfl⟩ : syracuseStep 1943243 = 2914865) B2914865
theorem B3501797 : Blo 1941435 3501797 := bbase (se 4 (by rfl) ⟨328293, by rfl⟩ : syracuseStep 3501797 = 656587) (by norm_num)
theorem B9338125 : Blo 1941435 9338125 := bstep (se 3 (by rfl) ⟨1750898, by rfl⟩ : syracuseStep 9338125 = 3501797) B3501797
theorem B12450833 : Blo 1941435 12450833 := bstep (se 2 (by rfl) ⟨4669062, by rfl⟩ : syracuseStep 12450833 = 9338125) B9338125
theorem B8300555 : Blo 1941435 8300555 := bstep (se 1 (by rfl) ⟨6225416, by rfl⟩ : syracuseStep 8300555 = 12450833) B12450833
theorem B5533703 : Blo 1941435 5533703 := bstep (se 1 (by rfl) ⟨4150277, by rfl⟩ : syracuseStep 5533703 = 8300555) B8300555
theorem B3689135 : Blo 1941435 3689135 := bstep (se 1 (by rfl) ⟨2766851, by rfl⟩ : syracuseStep 3689135 = 5533703) B5533703
theorem B2459423 : Blo 1941435 2459423 := bstep (se 1 (by rfl) ⟨1844567, by rfl⟩ : syracuseStep 2459423 = 3689135) B3689135
theorem B6558461 : Blo 1941435 6558461 := bstep (se 3 (by rfl) ⟨1229711, by rfl⟩ : syracuseStep 6558461 = 2459423) B2459423
theorem B4372307 : Blo 1941435 4372307 := bstep (se 1 (by rfl) ⟨3279230, by rfl⟩ : syracuseStep 4372307 = 6558461) B6558461
theorem B2914871 : Blo 1941435 2914871 := bstep (se 1 (by rfl) ⟨2186153, by rfl⟩ : syracuseStep 2914871 = 4372307) B4372307
theorem B1943247 : Blo 1941435 1943247 := bstep (se 1 (by rfl) ⟨1457435, by rfl⟩ : syracuseStep 1943247 = 2914871) B2914871
theorem B2914877 : Blo 1941435 2914877 := bbase (se 3 (by rfl) ⟨546539, by rfl⟩ : syracuseStep 2914877 = 1093079) (by norm_num)
theorem B1943251 : Blo 1941435 1943251 := bstep (se 1 (by rfl) ⟨1457438, by rfl⟩ : syracuseStep 1943251 = 2914877) B2914877
theorem B4372325 : Blo 1941435 4372325 := bbase (se 4 (by rfl) ⟨409905, by rfl⟩ : syracuseStep 4372325 = 819811) (by norm_num)
theorem B2914883 : Blo 1941435 2914883 := bstep (se 1 (by rfl) ⟨2186162, by rfl⟩ : syracuseStep 2914883 = 4372325) B4372325
theorem B1943255 : Blo 1941435 1943255 := bstep (se 1 (by rfl) ⟨1457441, by rfl⟩ : syracuseStep 1943255 = 2914883) B2914883
theorem B4918877 : Blo 1941435 4918877 := bbase (se 3 (by rfl) ⟨922289, by rfl⟩ : syracuseStep 4918877 = 1844579) (by norm_num)
theorem B3279251 : Blo 1941435 3279251 := bstep (se 1 (by rfl) ⟨2459438, by rfl⟩ : syracuseStep 3279251 = 4918877) B4918877
theorem B2186167 : Blo 1941435 2186167 := bstep (se 1 (by rfl) ⟨1639625, by rfl⟩ : syracuseStep 2186167 = 3279251) B3279251
theorem B2914889 : Blo 1941435 2914889 := bstep (se 2 (by rfl) ⟨1093083, by rfl⟩ : syracuseStep 2914889 = 2186167) B2186167
theorem B1943259 : Blo 1941435 1943259 := bstep (se 1 (by rfl) ⟨1457444, by rfl⟩ : syracuseStep 1943259 = 2914889) B2914889
theorem B3689165 : Blo 1941435 3689165 := bbase (se 3 (by rfl) ⟨691718, by rfl⟩ : syracuseStep 3689165 = 1383437) (by norm_num)
theorem B9837773 : Blo 1941435 9837773 := bstep (se 3 (by rfl) ⟨1844582, by rfl⟩ : syracuseStep 9837773 = 3689165) B3689165
theorem B6558515 : Blo 1941435 6558515 := bstep (se 1 (by rfl) ⟨4918886, by rfl⟩ : syracuseStep 6558515 = 9837773) B9837773
theorem B4372343 : Blo 1941435 4372343 := bstep (se 1 (by rfl) ⟨3279257, by rfl⟩ : syracuseStep 4372343 = 6558515) B6558515
theorem B2914895 : Blo 1941435 2914895 := bstep (se 1 (by rfl) ⟨2186171, by rfl⟩ : syracuseStep 2914895 = 4372343) B4372343
theorem B1943263 : Blo 1941435 1943263 := bstep (se 1 (by rfl) ⟨1457447, by rfl⟩ : syracuseStep 1943263 = 2914895) B2914895
theorem B2914901 : Blo 1941435 2914901 := bbase (se 8 (by rfl) ⟨17079, by rfl⟩ : syracuseStep 2914901 = 34159) (by norm_num)
theorem B1943267 : Blo 1941435 1943267 := bstep (se 1 (by rfl) ⟨1457450, by rfl⟩ : syracuseStep 1943267 = 2914901) B2914901
theorem B6225493 : Blo 1941435 6225493 := bbase (se 8 (by rfl) ⟨36477, by rfl⟩ : syracuseStep 6225493 = 72955) (by norm_num)
theorem B8300657 : Blo 1941435 8300657 := bstep (se 2 (by rfl) ⟨3112746, by rfl⟩ : syracuseStep 8300657 = 6225493) B6225493
theorem B5533771 : Blo 1941435 5533771 := bstep (se 1 (by rfl) ⟨4150328, by rfl⟩ : syracuseStep 5533771 = 8300657) B8300657
theorem B7378361 : Blo 1941435 7378361 := bstep (se 2 (by rfl) ⟨2766885, by rfl⟩ : syracuseStep 7378361 = 5533771) B5533771
theorem B4918907 : Blo 1941435 4918907 := bstep (se 1 (by rfl) ⟨3689180, by rfl⟩ : syracuseStep 4918907 = 7378361) B7378361
theorem B3279271 : Blo 1941435 3279271 := bstep (se 1 (by rfl) ⟨2459453, by rfl⟩ : syracuseStep 3279271 = 4918907) B4918907
theorem B4372361 : Blo 1941435 4372361 := bstep (se 2 (by rfl) ⟨1639635, by rfl⟩ : syracuseStep 4372361 = 3279271) B3279271
theorem B2914907 : Blo 1941435 2914907 := bstep (se 1 (by rfl) ⟨2186180, by rfl⟩ : syracuseStep 2914907 = 4372361) B4372361
theorem B1943271 : Blo 1941435 1943271 := bstep (se 1 (by rfl) ⟨1457453, by rfl⟩ : syracuseStep 1943271 = 2914907) B2914907
theorem B2186185 : Blo 1941435 2186185 := bbase (se 2 (by rfl) ⟨819819, by rfl⟩ : syracuseStep 2186185 = 1639639) (by norm_num)
theorem B2914913 : Blo 1941435 2914913 := bstep (se 2 (by rfl) ⟨1093092, by rfl⟩ : syracuseStep 2914913 = 2186185) B2186185
theorem B1943275 : Blo 1941435 1943275 := bstep (se 1 (by rfl) ⟨1457456, by rfl⟩ : syracuseStep 1943275 = 2914913) B2914913
theorem B5909381 : Blo 1941435 5909381 := bbase (se 4 (by rfl) ⟨554004, by rfl⟩ : syracuseStep 5909381 = 1108009) (by norm_num)
theorem B3939587 : Blo 1941435 3939587 := bstep (se 1 (by rfl) ⟨2954690, by rfl⟩ : syracuseStep 3939587 = 5909381) B5909381
theorem B2626391 : Blo 1941435 2626391 := bstep (se 1 (by rfl) ⟨1969793, by rfl⟩ : syracuseStep 2626391 = 3939587) B3939587
theorem B7003709 : Blo 1941435 7003709 := bstep (se 3 (by rfl) ⟨1313195, by rfl⟩ : syracuseStep 7003709 = 2626391) B2626391
theorem B4669139 : Blo 1941435 4669139 := bstep (se 1 (by rfl) ⟨3501854, by rfl⟩ : syracuseStep 4669139 = 7003709) B7003709
theorem B3112759 : Blo 1941435 3112759 := bstep (se 1 (by rfl) ⟨2334569, by rfl⟩ : syracuseStep 3112759 = 4669139) B4669139
theorem B16601381 : Blo 1941435 16601381 := bstep (se 4 (by rfl) ⟨1556379, by rfl⟩ : syracuseStep 16601381 = 3112759) B3112759
theorem B11067587 : Blo 1941435 11067587 := bstep (se 1 (by rfl) ⟨8300690, by rfl⟩ : syracuseStep 11067587 = 16601381) B16601381
theorem B7378391 : Blo 1941435 7378391 := bstep (se 1 (by rfl) ⟨5533793, by rfl⟩ : syracuseStep 7378391 = 11067587) B11067587
theorem B4918927 : Blo 1941435 4918927 := bstep (se 1 (by rfl) ⟨3689195, by rfl⟩ : syracuseStep 4918927 = 7378391) B7378391
theorem B6558569 : Blo 1941435 6558569 := bstep (se 2 (by rfl) ⟨2459463, by rfl⟩ : syracuseStep 6558569 = 4918927) B4918927
theorem B4372379 : Blo 1941435 4372379 := bstep (se 1 (by rfl) ⟨3279284, by rfl⟩ : syracuseStep 4372379 = 6558569) B6558569
theorem B2914919 : Blo 1941435 2914919 := bstep (se 1 (by rfl) ⟨2186189, by rfl⟩ : syracuseStep 2914919 = 4372379) B4372379
theorem B1943279 : Blo 1941435 1943279 := bstep (se 1 (by rfl) ⟨1457459, by rfl⟩ : syracuseStep 1943279 = 2914919) B2914919
theorem B2914925 : Blo 1941435 2914925 := bbase (se 3 (by rfl) ⟨546548, by rfl⟩ : syracuseStep 2914925 = 1093097) (by norm_num)
theorem B1943283 : Blo 1941435 1943283 := bstep (se 1 (by rfl) ⟨1457462, by rfl⟩ : syracuseStep 1943283 = 2914925) B2914925
theorem B4372397 : Blo 1941435 4372397 := bbase (se 3 (by rfl) ⟨819824, by rfl⟩ : syracuseStep 4372397 = 1639649) (by norm_num)
theorem B2914931 : Blo 1941435 2914931 := bstep (se 1 (by rfl) ⟨2186198, by rfl⟩ : syracuseStep 2914931 = 4372397) B4372397
theorem B1943287 : Blo 1941435 1943287 := bstep (se 1 (by rfl) ⟨1457465, by rfl⟩ : syracuseStep 1943287 = 2914931) B2914931
theorem B5533829 : Blo 1941435 5533829 := bbase (se 4 (by rfl) ⟨518796, by rfl⟩ : syracuseStep 5533829 = 1037593) (by norm_num)
theorem B3689219 : Blo 1941435 3689219 := bstep (se 1 (by rfl) ⟨2766914, by rfl⟩ : syracuseStep 3689219 = 5533829) B5533829
theorem B2459479 : Blo 1941435 2459479 := bstep (se 1 (by rfl) ⟨1844609, by rfl⟩ : syracuseStep 2459479 = 3689219) B3689219
theorem B3279305 : Blo 1941435 3279305 := bstep (se 2 (by rfl) ⟨1229739, by rfl⟩ : syracuseStep 3279305 = 2459479) B2459479
theorem B2186203 : Blo 1941435 2186203 := bstep (se 1 (by rfl) ⟨1639652, by rfl⟩ : syracuseStep 2186203 = 3279305) B3279305
theorem B2914937 : Blo 1941435 2914937 := bstep (se 2 (by rfl) ⟨1093101, by rfl⟩ : syracuseStep 2914937 = 2186203) B2186203
theorem B1943291 : Blo 1941435 1943291 := bstep (se 1 (by rfl) ⟨1457468, by rfl⟩ : syracuseStep 1943291 = 2914937) B2914937
theorem B7003765 : Blo 1941435 7003765 := bbase (se 5 (by rfl) ⟨328301, by rfl⟩ : syracuseStep 7003765 = 656603) (by norm_num)
theorem B37353413 : Blo 1941435 37353413 := bstep (se 4 (by rfl) ⟨3501882, by rfl⟩ : syracuseStep 37353413 = 7003765) B7003765
theorem B24902275 : Blo 1941435 24902275 := bstep (se 1 (by rfl) ⟨18676706, by rfl⟩ : syracuseStep 24902275 = 37353413) B37353413
theorem B33203033 : Blo 1941435 33203033 := bstep (se 2 (by rfl) ⟨12451137, by rfl⟩ : syracuseStep 33203033 = 24902275) B24902275
theorem B22135355 : Blo 1941435 22135355 := bstep (se 1 (by rfl) ⟨16601516, by rfl⟩ : syracuseStep 22135355 = 33203033) B33203033
theorem B14756903 : Blo 1941435 14756903 := bstep (se 1 (by rfl) ⟨11067677, by rfl⟩ : syracuseStep 14756903 = 22135355) B22135355
theorem B9837935 : Blo 1941435 9837935 := bstep (se 1 (by rfl) ⟨7378451, by rfl⟩ : syracuseStep 9837935 = 14756903) B14756903
theorem B6558623 : Blo 1941435 6558623 := bstep (se 1 (by rfl) ⟨4918967, by rfl⟩ : syracuseStep 6558623 = 9837935) B9837935
theorem B4372415 : Blo 1941435 4372415 := bstep (se 1 (by rfl) ⟨3279311, by rfl⟩ : syracuseStep 4372415 = 6558623) B6558623
theorem B2914943 : Blo 1941435 2914943 := bstep (se 1 (by rfl) ⟨2186207, by rfl⟩ : syracuseStep 2914943 = 4372415) B4372415
theorem B1943295 : Blo 1941435 1943295 := bstep (se 1 (by rfl) ⟨1457471, by rfl⟩ : syracuseStep 1943295 = 2914943) B2914943
theorem B2914949 : Blo 1941435 2914949 := bbase (se 4 (by rfl) ⟨273276, by rfl⟩ : syracuseStep 2914949 = 546553) (by norm_num)
theorem B1943299 : Blo 1941435 1943299 := bstep (se 1 (by rfl) ⟨1457474, by rfl⟩ : syracuseStep 1943299 = 2914949) B2914949
theorem B3279325 : Blo 1941435 3279325 := bbase (se 3 (by rfl) ⟨614873, by rfl⟩ : syracuseStep 3279325 = 1229747) (by norm_num)
theorem B4372433 : Blo 1941435 4372433 := bstep (se 2 (by rfl) ⟨1639662, by rfl⟩ : syracuseStep 4372433 = 3279325) B3279325
theorem B2914955 : Blo 1941435 2914955 := bstep (se 1 (by rfl) ⟨2186216, by rfl⟩ : syracuseStep 2914955 = 4372433) B4372433
theorem B1943303 : Blo 1941435 1943303 := bstep (se 1 (by rfl) ⟨1457477, by rfl⟩ : syracuseStep 1943303 = 2914955) B2914955
theorem B2186221 : Blo 1941435 2186221 := bbase (se 3 (by rfl) ⟨409916, by rfl⟩ : syracuseStep 2186221 = 819833) (by norm_num)
theorem B2914961 : Blo 1941435 2914961 := bstep (se 2 (by rfl) ⟨1093110, by rfl⟩ : syracuseStep 2914961 = 2186221) B2186221
theorem B1943307 : Blo 1941435 1943307 := bstep (se 1 (by rfl) ⟨1457480, by rfl⟩ : syracuseStep 1943307 = 2914961) B2914961
theorem B6558677 : Blo 1941435 6558677 := bbase (se 7 (by rfl) ⟨76859, by rfl⟩ : syracuseStep 6558677 = 153719) (by norm_num)
theorem B4372451 : Blo 1941435 4372451 := bstep (se 1 (by rfl) ⟨3279338, by rfl⟩ : syracuseStep 4372451 = 6558677) B6558677
theorem B2914967 : Blo 1941435 2914967 := bstep (se 1 (by rfl) ⟨2186225, by rfl⟩ : syracuseStep 2914967 = 4372451) B4372451
theorem B1943311 : Blo 1941435 1943311 := bstep (se 1 (by rfl) ⟨1457483, by rfl⟩ : syracuseStep 1943311 = 2914967) B2914967
theorem B2914973 : Blo 1941435 2914973 := bbase (se 3 (by rfl) ⟨546557, by rfl⟩ : syracuseStep 2914973 = 1093115) (by norm_num)
theorem B1943315 : Blo 1941435 1943315 := bstep (se 1 (by rfl) ⟨1457486, by rfl⟩ : syracuseStep 1943315 = 2914973) B2914973
theorem B4372469 : Blo 1941435 4372469 := bbase (se 5 (by rfl) ⟨204959, by rfl⟩ : syracuseStep 4372469 = 409919) (by norm_num)
theorem B2914979 : Blo 1941435 2914979 := bstep (se 1 (by rfl) ⟨2186234, by rfl⟩ : syracuseStep 2914979 = 4372469) B4372469
theorem B1943319 : Blo 1941435 1943319 := bstep (se 1 (by rfl) ⟨1457489, by rfl⟩ : syracuseStep 1943319 = 2914979) B2914979
theorem B2220701 : Blo 1941435 2220701 := bbase (se 3 (by rfl) ⟨416381, by rfl⟩ : syracuseStep 2220701 = 832763) (by norm_num)
theorem B5921869 : Blo 1941435 5921869 := bstep (se 3 (by rfl) ⟨1110350, by rfl⟩ : syracuseStep 5921869 = 2220701) B2220701
theorem B7895825 : Blo 1941435 7895825 := bstep (se 2 (by rfl) ⟨2960934, by rfl⟩ : syracuseStep 7895825 = 5921869) B5921869
theorem B5263883 : Blo 1941435 5263883 := bstep (se 1 (by rfl) ⟨3947912, by rfl⟩ : syracuseStep 5263883 = 7895825) B7895825
theorem B3509255 : Blo 1941435 3509255 := bstep (se 1 (by rfl) ⟨2631941, by rfl⟩ : syracuseStep 3509255 = 5263883) B5263883
theorem B2339503 : Blo 1941435 2339503 := bstep (se 1 (by rfl) ⟨1754627, by rfl⟩ : syracuseStep 2339503 = 3509255) B3509255
theorem B12477349 : Blo 1941435 12477349 := bstep (se 4 (by rfl) ⟨1169751, by rfl⟩ : syracuseStep 12477349 = 2339503) B2339503
theorem B16636465 : Blo 1941435 16636465 := bstep (se 2 (by rfl) ⟨6238674, by rfl⟩ : syracuseStep 16636465 = 12477349) B12477349
theorem B22181953 : Blo 1941435 22181953 := bstep (se 2 (by rfl) ⟨8318232, by rfl⟩ : syracuseStep 22181953 = 16636465) B16636465
theorem B29575937 : Blo 1941435 29575937 := bstep (se 2 (by rfl) ⟨11090976, by rfl⟩ : syracuseStep 29575937 = 22181953) B22181953
theorem B78869165 : Blo 1941435 78869165 := bstep (se 3 (by rfl) ⟨14787968, by rfl⟩ : syracuseStep 78869165 = 29575937) B29575937
theorem B841271093 : Blo 1941435 841271093 := bstep (se 5 (by rfl) ⟨39434582, by rfl⟩ : syracuseStep 841271093 = 78869165) B78869165
theorem B560847395 : Blo 1941435 560847395 := bstep (se 1 (by rfl) ⟨420635546, by rfl⟩ : syracuseStep 560847395 = 841271093) B841271093
theorem B373898263 : Blo 1941435 373898263 := bstep (se 1 (by rfl) ⟨280423697, by rfl⟩ : syracuseStep 373898263 = 560847395) B560847395
theorem B498531017 : Blo 1941435 498531017 := bstep (se 2 (by rfl) ⟨186949131, by rfl⟩ : syracuseStep 498531017 = 373898263) B373898263
theorem B332354011 : Blo 1941435 332354011 := bstep (se 1 (by rfl) ⟨249265508, by rfl⟩ : syracuseStep 332354011 = 498531017) B498531017
theorem B443138681 : Blo 1941435 443138681 := bstep (se 2 (by rfl) ⟨166177005, by rfl⟩ : syracuseStep 443138681 = 332354011) B332354011
theorem B295425787 : Blo 1941435 295425787 := bstep (se 1 (by rfl) ⟨221569340, by rfl⟩ : syracuseStep 295425787 = 443138681) B443138681
theorem B393901049 : Blo 1941435 393901049 := bstep (se 2 (by rfl) ⟨147712893, by rfl⟩ : syracuseStep 393901049 = 295425787) B295425787
theorem B262600699 : Blo 1941435 262600699 := bstep (se 1 (by rfl) ⟨196950524, by rfl⟩ : syracuseStep 262600699 = 393901049) B393901049
theorem B350134265 : Blo 1941435 350134265 := bstep (se 2 (by rfl) ⟨131300349, by rfl⟩ : syracuseStep 350134265 = 262600699) B262600699
theorem B233422843 : Blo 1941435 233422843 := bstep (se 1 (by rfl) ⟨175067132, by rfl⟩ : syracuseStep 233422843 = 350134265) B350134265
theorem B311230457 : Blo 1941435 311230457 := bstep (se 2 (by rfl) ⟨116711421, by rfl⟩ : syracuseStep 311230457 = 233422843) B233422843
theorem B207486971 : Blo 1941435 207486971 := bstep (se 1 (by rfl) ⟨155615228, by rfl⟩ : syracuseStep 207486971 = 311230457) B311230457
theorem B138324647 : Blo 1941435 138324647 := bstep (se 1 (by rfl) ⟨103743485, by rfl⟩ : syracuseStep 138324647 = 207486971) B207486971
theorem B92216431 : Blo 1941435 92216431 := bstep (se 1 (by rfl) ⟨69162323, by rfl⟩ : syracuseStep 92216431 = 138324647) B138324647
theorem B122955241 : Blo 1941435 122955241 := bstep (se 2 (by rfl) ⟨46108215, by rfl⟩ : syracuseStep 122955241 = 92216431) B92216431
theorem B163940321 : Blo 1941435 163940321 := bstep (se 2 (by rfl) ⟨61477620, by rfl⟩ : syracuseStep 163940321 = 122955241) B122955241
theorem B437174189 : Blo 1941435 437174189 := bstep (se 3 (by rfl) ⟨81970160, by rfl⟩ : syracuseStep 437174189 = 163940321) B163940321
theorem B291449459 : Blo 1941435 291449459 := bstep (se 1 (by rfl) ⟨218587094, by rfl⟩ : syracuseStep 291449459 = 437174189) B437174189
theorem B777198557 : Blo 1941435 777198557 := bstep (se 3 (by rfl) ⟨145724729, by rfl⟩ : syracuseStep 777198557 = 291449459) B291449459
theorem B518132371 : Blo 1941435 518132371 := bstep (se 1 (by rfl) ⟨388599278, by rfl⟩ : syracuseStep 518132371 = 777198557) B777198557
theorem B690843161 : Blo 1941435 690843161 := bstep (se 2 (by rfl) ⟨259066185, by rfl⟩ : syracuseStep 690843161 = 518132371) B518132371
theorem B460562107 : Blo 1941435 460562107 := bstep (se 1 (by rfl) ⟨345421580, by rfl⟩ : syracuseStep 460562107 = 690843161) B690843161
theorem B614082809 : Blo 1941435 614082809 := bstep (se 2 (by rfl) ⟨230281053, by rfl⟩ : syracuseStep 614082809 = 460562107) B460562107
theorem B409388539 : Blo 1941435 409388539 := bstep (se 1 (by rfl) ⟨307041404, by rfl⟩ : syracuseStep 409388539 = 614082809) B614082809
theorem B545851385 : Blo 1941435 545851385 := bstep (se 2 (by rfl) ⟨204694269, by rfl⟩ : syracuseStep 545851385 = 409388539) B409388539
theorem B363900923 : Blo 1941435 363900923 := bstep (se 1 (by rfl) ⟨272925692, by rfl⟩ : syracuseStep 363900923 = 545851385) B545851385
theorem B242600615 : Blo 1941435 242600615 := bstep (se 1 (by rfl) ⟨181950461, by rfl⟩ : syracuseStep 242600615 = 363900923) B363900923
theorem B161733743 : Blo 1941435 161733743 := bstep (se 1 (by rfl) ⟨121300307, by rfl⟩ : syracuseStep 161733743 = 242600615) B242600615
theorem B107822495 : Blo 1941435 107822495 := bstep (se 1 (by rfl) ⟨80866871, by rfl⟩ : syracuseStep 107822495 = 161733743) B161733743
theorem B71881663 : Blo 1941435 71881663 := bstep (se 1 (by rfl) ⟨53911247, by rfl⟩ : syracuseStep 71881663 = 107822495) B107822495
theorem B95842217 : Blo 1941435 95842217 := bstep (se 2 (by rfl) ⟨35940831, by rfl⟩ : syracuseStep 95842217 = 71881663) B71881663
theorem B255579245 : Blo 1941435 255579245 := bstep (se 3 (by rfl) ⟨47921108, by rfl⟩ : syracuseStep 255579245 = 95842217) B95842217
theorem B170386163 : Blo 1941435 170386163 := bstep (se 1 (by rfl) ⟨127789622, by rfl⟩ : syracuseStep 170386163 = 255579245) B255579245
theorem B113590775 : Blo 1941435 113590775 := bstep (se 1 (by rfl) ⟨85193081, by rfl⟩ : syracuseStep 113590775 = 170386163) B170386163
theorem B75727183 : Blo 1941435 75727183 := bstep (se 1 (by rfl) ⟨56795387, by rfl⟩ : syracuseStep 75727183 = 113590775) B113590775
theorem B100969577 : Blo 1941435 100969577 := bstep (se 2 (by rfl) ⟨37863591, by rfl⟩ : syracuseStep 100969577 = 75727183) B75727183
theorem B67313051 : Blo 1941435 67313051 := bstep (se 1 (by rfl) ⟨50484788, by rfl⟩ : syracuseStep 67313051 = 100969577) B100969577
theorem B44875367 : Blo 1941435 44875367 := bstep (se 1 (by rfl) ⟨33656525, by rfl⟩ : syracuseStep 44875367 = 67313051) B67313051
theorem B29916911 : Blo 1941435 29916911 := bstep (se 1 (by rfl) ⟨22437683, by rfl⟩ : syracuseStep 29916911 = 44875367) B44875367
theorem B79778429 : Blo 1941435 79778429 := bstep (se 3 (by rfl) ⟨14958455, by rfl⟩ : syracuseStep 79778429 = 29916911) B29916911
theorem B53185619 : Blo 1941435 53185619 := bstep (se 1 (by rfl) ⟨39889214, by rfl⟩ : syracuseStep 53185619 = 79778429) B79778429
theorem B141828317 : Blo 1941435 141828317 := bstep (se 3 (by rfl) ⟨26592809, by rfl⟩ : syracuseStep 141828317 = 53185619) B53185619
theorem B94552211 : Blo 1941435 94552211 := bstep (se 1 (by rfl) ⟨70914158, by rfl⟩ : syracuseStep 94552211 = 141828317) B141828317
theorem B63034807 : Blo 1941435 63034807 := bstep (se 1 (by rfl) ⟨47276105, by rfl⟩ : syracuseStep 63034807 = 94552211) B94552211
theorem B84046409 : Blo 1941435 84046409 := bstep (se 2 (by rfl) ⟨31517403, by rfl⟩ : syracuseStep 84046409 = 63034807) B63034807
theorem B56030939 : Blo 1941435 56030939 := bstep (se 1 (by rfl) ⟨42023204, by rfl⟩ : syracuseStep 56030939 = 84046409) B84046409
theorem B37353959 : Blo 1941435 37353959 := bstep (se 1 (by rfl) ⟨28015469, by rfl⟩ : syracuseStep 37353959 = 56030939) B56030939
theorem B24902639 : Blo 1941435 24902639 := bstep (se 1 (by rfl) ⟨18676979, by rfl⟩ : syracuseStep 24902639 = 37353959) B37353959
theorem B16601759 : Blo 1941435 16601759 := bstep (se 1 (by rfl) ⟨12451319, by rfl⟩ : syracuseStep 16601759 = 24902639) B24902639
theorem B11067839 : Blo 1941435 11067839 := bstep (se 1 (by rfl) ⟨8300879, by rfl⟩ : syracuseStep 11067839 = 16601759) B16601759
theorem B7378559 : Blo 1941435 7378559 := bstep (se 1 (by rfl) ⟨5533919, by rfl⟩ : syracuseStep 7378559 = 11067839) B11067839
theorem B4919039 : Blo 1941435 4919039 := bstep (se 1 (by rfl) ⟨3689279, by rfl⟩ : syracuseStep 4919039 = 7378559) B7378559
theorem B3279359 : Blo 1941435 3279359 := bstep (se 1 (by rfl) ⟨2459519, by rfl⟩ : syracuseStep 3279359 = 4919039) B4919039
theorem B2186239 : Blo 1941435 2186239 := bstep (se 1 (by rfl) ⟨1639679, by rfl⟩ : syracuseStep 2186239 = 3279359) B3279359
theorem B2914985 : Blo 1941435 2914985 := bstep (se 2 (by rfl) ⟨1093119, by rfl⟩ : syracuseStep 2914985 = 2186239) B2186239
theorem B1943323 : Blo 1941435 1943323 := bstep (se 1 (by rfl) ⟨1457492, by rfl⟩ : syracuseStep 1943323 = 2914985) B2914985
theorem B2766965 : Blo 1941435 2766965 := bbase (se 5 (by rfl) ⟨129701, by rfl⟩ : syracuseStep 2766965 = 259403) (by norm_num)
theorem B7378573 : Blo 1941435 7378573 := bstep (se 3 (by rfl) ⟨1383482, by rfl⟩ : syracuseStep 7378573 = 2766965) B2766965
theorem B9838097 : Blo 1941435 9838097 := bstep (se 2 (by rfl) ⟨3689286, by rfl⟩ : syracuseStep 9838097 = 7378573) B7378573
theorem B6558731 : Blo 1941435 6558731 := bstep (se 1 (by rfl) ⟨4919048, by rfl⟩ : syracuseStep 6558731 = 9838097) B9838097
theorem B4372487 : Blo 1941435 4372487 := bstep (se 1 (by rfl) ⟨3279365, by rfl⟩ : syracuseStep 4372487 = 6558731) B6558731
theorem B2914991 : Blo 1941435 2914991 := bstep (se 1 (by rfl) ⟨2186243, by rfl⟩ : syracuseStep 2914991 = 4372487) B4372487
theorem B1943327 : Blo 1941435 1943327 := bstep (se 1 (by rfl) ⟨1457495, by rfl⟩ : syracuseStep 1943327 = 2914991) B2914991
theorem B2914997 : Blo 1941435 2914997 := bbase (se 5 (by rfl) ⟨136640, by rfl⟩ : syracuseStep 2914997 = 273281) (by norm_num)
theorem B1943331 : Blo 1941435 1943331 := bstep (se 1 (by rfl) ⟨1457498, by rfl⟩ : syracuseStep 1943331 = 2914997) B2914997
theorem B4919069 : Blo 1941435 4919069 := bbase (se 3 (by rfl) ⟨922325, by rfl⟩ : syracuseStep 4919069 = 1844651) (by norm_num)
theorem B3279379 : Blo 1941435 3279379 := bstep (se 1 (by rfl) ⟨2459534, by rfl⟩ : syracuseStep 3279379 = 4919069) B4919069
theorem B4372505 : Blo 1941435 4372505 := bstep (se 2 (by rfl) ⟨1639689, by rfl⟩ : syracuseStep 4372505 = 3279379) B3279379
theorem B2915003 : Blo 1941435 2915003 := bstep (se 1 (by rfl) ⟨2186252, by rfl⟩ : syracuseStep 2915003 = 4372505) B4372505
theorem B1943335 : Blo 1941435 1943335 := bstep (se 1 (by rfl) ⟨1457501, by rfl⟩ : syracuseStep 1943335 = 2915003) B2915003
theorem B2186257 : Blo 1941435 2186257 := bbase (se 2 (by rfl) ⟨819846, by rfl⟩ : syracuseStep 2186257 = 1639693) (by norm_num)
theorem B2915009 : Blo 1941435 2915009 := bstep (se 2 (by rfl) ⟨1093128, by rfl⟩ : syracuseStep 2915009 = 2186257) B2186257
theorem B1943339 : Blo 1941435 1943339 := bstep (se 1 (by rfl) ⟨1457504, by rfl⟩ : syracuseStep 1943339 = 2915009) B2915009
theorem B3689317 : Blo 1941435 3689317 := bbase (se 4 (by rfl) ⟨345873, by rfl⟩ : syracuseStep 3689317 = 691747) (by norm_num)
theorem B4919089 : Blo 1941435 4919089 := bstep (se 2 (by rfl) ⟨1844658, by rfl⟩ : syracuseStep 4919089 = 3689317) B3689317
theorem B6558785 : Blo 1941435 6558785 := bstep (se 2 (by rfl) ⟨2459544, by rfl⟩ : syracuseStep 6558785 = 4919089) B4919089
theorem B4372523 : Blo 1941435 4372523 := bstep (se 1 (by rfl) ⟨3279392, by rfl⟩ : syracuseStep 4372523 = 6558785) B6558785
theorem B2915015 : Blo 1941435 2915015 := bstep (se 1 (by rfl) ⟨2186261, by rfl⟩ : syracuseStep 2915015 = 4372523) B4372523
theorem B1943343 : Blo 1941435 1943343 := bstep (se 1 (by rfl) ⟨1457507, by rfl⟩ : syracuseStep 1943343 = 2915015) B2915015
theorem B2915021 : Blo 1941435 2915021 := bbase (se 3 (by rfl) ⟨546566, by rfl⟩ : syracuseStep 2915021 = 1093133) (by norm_num)
theorem B1943347 : Blo 1941435 1943347 := bstep (se 1 (by rfl) ⟨1457510, by rfl⟩ : syracuseStep 1943347 = 2915021) B2915021
theorem B4372541 : Blo 1941435 4372541 := bbase (se 3 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 4372541 = 1639703) (by norm_num)
theorem B2915027 : Blo 1941435 2915027 := bstep (se 1 (by rfl) ⟨2186270, by rfl⟩ : syracuseStep 2915027 = 4372541) B4372541
theorem B1943351 : Blo 1941435 1943351 := bstep (se 1 (by rfl) ⟨1457513, by rfl⟩ : syracuseStep 1943351 = 2915027) B2915027
theorem B3279413 : Blo 1941435 3279413 := bbase (se 5 (by rfl) ⟨153722, by rfl⟩ : syracuseStep 3279413 = 307445) (by norm_num)
theorem B2186275 : Blo 1941435 2186275 := bstep (se 1 (by rfl) ⟨1639706, by rfl⟩ : syracuseStep 2186275 = 3279413) B3279413
theorem B2915033 : Blo 1941435 2915033 := bstep (se 2 (by rfl) ⟨1093137, by rfl⟩ : syracuseStep 2915033 = 2186275) B2186275
theorem B1943355 : Blo 1941435 1943355 := bstep (se 1 (by rfl) ⟨1457516, by rfl⟩ : syracuseStep 1943355 = 2915033) B2915033
theorem B5534021 : Blo 1941435 5534021 := bbase (se 4 (by rfl) ⟨518814, by rfl⟩ : syracuseStep 5534021 = 1037629) (by norm_num)
theorem B14757389 : Blo 1941435 14757389 := bstep (se 3 (by rfl) ⟨2767010, by rfl⟩ : syracuseStep 14757389 = 5534021) B5534021
theorem B9838259 : Blo 1941435 9838259 := bstep (se 1 (by rfl) ⟨7378694, by rfl⟩ : syracuseStep 9838259 = 14757389) B14757389
theorem B6558839 : Blo 1941435 6558839 := bstep (se 1 (by rfl) ⟨4919129, by rfl⟩ : syracuseStep 6558839 = 9838259) B9838259
theorem B4372559 : Blo 1941435 4372559 := bstep (se 1 (by rfl) ⟨3279419, by rfl⟩ : syracuseStep 4372559 = 6558839) B6558839
theorem B2915039 : Blo 1941435 2915039 := bstep (se 1 (by rfl) ⟨2186279, by rfl⟩ : syracuseStep 2915039 = 4372559) B4372559
theorem B1943359 : Blo 1941435 1943359 := bstep (se 1 (by rfl) ⟨1457519, by rfl⟩ : syracuseStep 1943359 = 2915039) B2915039
theorem B2915045 : Blo 1941435 2915045 := bbase (se 4 (by rfl) ⟨273285, by rfl⟩ : syracuseStep 2915045 = 546571) (by norm_num)
theorem B1943363 : Blo 1941435 1943363 := bstep (se 1 (by rfl) ⟨1457522, by rfl⟩ : syracuseStep 1943363 = 2915045) B2915045
theorem B3112901 : Blo 1941435 3112901 := bbase (se 4 (by rfl) ⟨291834, by rfl⟩ : syracuseStep 3112901 = 583669) (by norm_num)
theorem B2075267 : Blo 1941435 2075267 := bstep (se 1 (by rfl) ⟨1556450, by rfl⟩ : syracuseStep 2075267 = 3112901) B3112901
theorem B5534045 : Blo 1941435 5534045 := bstep (se 3 (by rfl) ⟨1037633, by rfl⟩ : syracuseStep 5534045 = 2075267) B2075267
theorem B3689363 : Blo 1941435 3689363 := bstep (se 1 (by rfl) ⟨2767022, by rfl⟩ : syracuseStep 3689363 = 5534045) B5534045
theorem B2459575 : Blo 1941435 2459575 := bstep (se 1 (by rfl) ⟨1844681, by rfl⟩ : syracuseStep 2459575 = 3689363) B3689363
theorem B3279433 : Blo 1941435 3279433 := bstep (se 2 (by rfl) ⟨1229787, by rfl⟩ : syracuseStep 3279433 = 2459575) B2459575
theorem B4372577 : Blo 1941435 4372577 := bstep (se 2 (by rfl) ⟨1639716, by rfl⟩ : syracuseStep 4372577 = 3279433) B3279433
theorem B2915051 : Blo 1941435 2915051 := bstep (se 1 (by rfl) ⟨2186288, by rfl⟩ : syracuseStep 2915051 = 4372577) B4372577
theorem B1943367 : Blo 1941435 1943367 := bstep (se 1 (by rfl) ⟨1457525, by rfl⟩ : syracuseStep 1943367 = 2915051) B2915051
theorem B2186293 : Blo 1941435 2186293 := bbase (se 5 (by rfl) ⟨102482, by rfl⟩ : syracuseStep 2186293 = 204965) (by norm_num)
theorem B2915057 : Blo 1941435 2915057 := bstep (se 2 (by rfl) ⟨1093146, by rfl⟩ : syracuseStep 2915057 = 2186293) B2186293
theorem B1943371 : Blo 1941435 1943371 := bstep (se 1 (by rfl) ⟨1457528, by rfl⟩ : syracuseStep 1943371 = 2915057) B2915057
theorem B2459585 : Blo 1941435 2459585 := bbase (se 2 (by rfl) ⟨922344, by rfl⟩ : syracuseStep 2459585 = 1844689) (by norm_num)
theorem B6558893 : Blo 1941435 6558893 := bstep (se 3 (by rfl) ⟨1229792, by rfl⟩ : syracuseStep 6558893 = 2459585) B2459585
theorem B4372595 : Blo 1941435 4372595 := bstep (se 1 (by rfl) ⟨3279446, by rfl⟩ : syracuseStep 4372595 = 6558893) B6558893
theorem B2915063 : Blo 1941435 2915063 := bstep (se 1 (by rfl) ⟨2186297, by rfl⟩ : syracuseStep 2915063 = 4372595) B4372595
theorem B1943375 : Blo 1941435 1943375 := bstep (se 1 (by rfl) ⟨1457531, by rfl⟩ : syracuseStep 1943375 = 2915063) B2915063
theorem B2915069 : Blo 1941435 2915069 := bbase (se 3 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 2915069 = 1093151) (by norm_num)
theorem B1943379 : Blo 1941435 1943379 := bstep (se 1 (by rfl) ⟨1457534, by rfl⟩ : syracuseStep 1943379 = 2915069) B2915069
theorem B4372613 : Blo 1941435 4372613 := bbase (se 4 (by rfl) ⟨409932, by rfl⟩ : syracuseStep 4372613 = 819865) (by norm_num)
theorem B2915075 : Blo 1941435 2915075 := bstep (se 1 (by rfl) ⟨2186306, by rfl⟩ : syracuseStep 2915075 = 4372613) B4372613
theorem B1943383 : Blo 1941435 1943383 := bstep (se 1 (by rfl) ⟨1457537, by rfl⟩ : syracuseStep 1943383 = 2915075) B2915075
theorem B3112933 : Blo 1941435 3112933 := bbase (se 4 (by rfl) ⟨291837, by rfl⟩ : syracuseStep 3112933 = 583675) (by norm_num)
theorem B4150577 : Blo 1941435 4150577 := bstep (se 2 (by rfl) ⟨1556466, by rfl⟩ : syracuseStep 4150577 = 3112933) B3112933
theorem B2767051 : Blo 1941435 2767051 := bstep (se 1 (by rfl) ⟨2075288, by rfl⟩ : syracuseStep 2767051 = 4150577) B4150577
theorem B3689401 : Blo 1941435 3689401 := bstep (se 2 (by rfl) ⟨1383525, by rfl⟩ : syracuseStep 3689401 = 2767051) B2767051
theorem B4919201 : Blo 1941435 4919201 := bstep (se 2 (by rfl) ⟨1844700, by rfl⟩ : syracuseStep 4919201 = 3689401) B3689401
theorem B3279467 : Blo 1941435 3279467 := bstep (se 1 (by rfl) ⟨2459600, by rfl⟩ : syracuseStep 3279467 = 4919201) B4919201
theorem B2186311 : Blo 1941435 2186311 := bstep (se 1 (by rfl) ⟨1639733, by rfl⟩ : syracuseStep 2186311 = 3279467) B3279467
theorem B2915081 : Blo 1941435 2915081 := bstep (se 2 (by rfl) ⟨1093155, by rfl⟩ : syracuseStep 2915081 = 2186311) B2186311
theorem B1943387 : Blo 1941435 1943387 := bstep (se 1 (by rfl) ⟨1457540, by rfl⟩ : syracuseStep 1943387 = 2915081) B2915081
theorem B9838421 : Blo 1941435 9838421 := bbase (se 9 (by rfl) ⟨28823, by rfl⟩ : syracuseStep 9838421 = 57647) (by norm_num)
theorem B6558947 : Blo 1941435 6558947 := bstep (se 1 (by rfl) ⟨4919210, by rfl⟩ : syracuseStep 6558947 = 9838421) B9838421
theorem B4372631 : Blo 1941435 4372631 := bstep (se 1 (by rfl) ⟨3279473, by rfl⟩ : syracuseStep 4372631 = 6558947) B6558947
theorem B2915087 : Blo 1941435 2915087 := bstep (se 1 (by rfl) ⟨2186315, by rfl⟩ : syracuseStep 2915087 = 4372631) B4372631
theorem B1943391 : Blo 1941435 1943391 := bstep (se 1 (by rfl) ⟨1457543, by rfl⟩ : syracuseStep 1943391 = 2915087) B2915087
theorem B2915093 : Blo 1941435 2915093 := bbase (se 6 (by rfl) ⟨68322, by rfl⟩ : syracuseStep 2915093 = 136645) (by norm_num)
theorem B1943395 : Blo 1941435 1943395 := bstep (se 1 (by rfl) ⟨1457546, by rfl⟩ : syracuseStep 1943395 = 2915093) B2915093
theorem B15759317 : Blo 1941435 15759317 := bbase (se 7 (by rfl) ⟨184679, by rfl⟩ : syracuseStep 15759317 = 369359) (by norm_num)
theorem B42024845 : Blo 1941435 42024845 := bstep (se 3 (by rfl) ⟨7879658, by rfl⟩ : syracuseStep 42024845 = 15759317) B15759317
theorem B28016563 : Blo 1941435 28016563 := bstep (se 1 (by rfl) ⟨21012422, by rfl⟩ : syracuseStep 28016563 = 42024845) B42024845
theorem B37355417 : Blo 1941435 37355417 := bstep (se 2 (by rfl) ⟨14008281, by rfl⟩ : syracuseStep 37355417 = 28016563) B28016563
theorem B24903611 : Blo 1941435 24903611 := bstep (se 1 (by rfl) ⟨18677708, by rfl⟩ : syracuseStep 24903611 = 37355417) B37355417
theorem B16602407 : Blo 1941435 16602407 := bstep (se 1 (by rfl) ⟨12451805, by rfl⟩ : syracuseStep 16602407 = 24903611) B24903611
theorem B11068271 : Blo 1941435 11068271 := bstep (se 1 (by rfl) ⟨8301203, by rfl⟩ : syracuseStep 11068271 = 16602407) B16602407
theorem B7378847 : Blo 1941435 7378847 := bstep (se 1 (by rfl) ⟨5534135, by rfl⟩ : syracuseStep 7378847 = 11068271) B11068271
theorem B4919231 : Blo 1941435 4919231 := bstep (se 1 (by rfl) ⟨3689423, by rfl⟩ : syracuseStep 4919231 = 7378847) B7378847
theorem B3279487 : Blo 1941435 3279487 := bstep (se 1 (by rfl) ⟨2459615, by rfl⟩ : syracuseStep 3279487 = 4919231) B4919231
theorem B4372649 : Blo 1941435 4372649 := bstep (se 2 (by rfl) ⟨1639743, by rfl⟩ : syracuseStep 4372649 = 3279487) B3279487
theorem B2915099 : Blo 1941435 2915099 := bstep (se 1 (by rfl) ⟨2186324, by rfl⟩ : syracuseStep 2915099 = 4372649) B4372649
theorem B1943399 : Blo 1941435 1943399 := bstep (se 1 (by rfl) ⟨1457549, by rfl⟩ : syracuseStep 1943399 = 2915099) B2915099
theorem B2186329 : Blo 1941435 2186329 := bbase (se 2 (by rfl) ⟨819873, by rfl⟩ : syracuseStep 2186329 = 1639747) (by norm_num)
theorem B2915105 : Blo 1941435 2915105 := bstep (se 2 (by rfl) ⟨1093164, by rfl⟩ : syracuseStep 2915105 = 2186329) B2186329
theorem B1943403 : Blo 1941435 1943403 := bstep (se 1 (by rfl) ⟨1457552, by rfl⟩ : syracuseStep 1943403 = 2915105) B2915105
theorem B2954885 : Blo 1941435 2954885 := bbase (se 4 (by rfl) ⟨277020, by rfl⟩ : syracuseStep 2954885 = 554041) (by norm_num)
theorem B7879693 : Blo 1941435 7879693 := bstep (se 3 (by rfl) ⟨1477442, by rfl⟩ : syracuseStep 7879693 = 2954885) B2954885
theorem B10506257 : Blo 1941435 10506257 := bstep (se 2 (by rfl) ⟨3939846, by rfl⟩ : syracuseStep 10506257 = 7879693) B7879693
theorem B7004171 : Blo 1941435 7004171 := bstep (se 1 (by rfl) ⟨5253128, by rfl⟩ : syracuseStep 7004171 = 10506257) B10506257
theorem B4669447 : Blo 1941435 4669447 := bstep (se 1 (by rfl) ⟨3502085, by rfl⟩ : syracuseStep 4669447 = 7004171) B7004171
theorem B6225929 : Blo 1941435 6225929 := bstep (se 2 (by rfl) ⟨2334723, by rfl⟩ : syracuseStep 6225929 = 4669447) B4669447
theorem B4150619 : Blo 1941435 4150619 := bstep (se 1 (by rfl) ⟨3112964, by rfl⟩ : syracuseStep 4150619 = 6225929) B6225929
theorem B2767079 : Blo 1941435 2767079 := bstep (se 1 (by rfl) ⟨2075309, by rfl⟩ : syracuseStep 2767079 = 4150619) B4150619
theorem B7378877 : Blo 1941435 7378877 := bstep (se 3 (by rfl) ⟨1383539, by rfl⟩ : syracuseStep 7378877 = 2767079) B2767079
theorem B4919251 : Blo 1941435 4919251 := bstep (se 1 (by rfl) ⟨3689438, by rfl⟩ : syracuseStep 4919251 = 7378877) B7378877
theorem B6559001 : Blo 1941435 6559001 := bstep (se 2 (by rfl) ⟨2459625, by rfl⟩ : syracuseStep 6559001 = 4919251) B4919251
theorem B4372667 : Blo 1941435 4372667 := bstep (se 1 (by rfl) ⟨3279500, by rfl⟩ : syracuseStep 4372667 = 6559001) B6559001
theorem B2915111 : Blo 1941435 2915111 := bstep (se 1 (by rfl) ⟨2186333, by rfl⟩ : syracuseStep 2915111 = 4372667) B4372667
theorem B1943407 : Blo 1941435 1943407 := bstep (se 1 (by rfl) ⟨1457555, by rfl⟩ : syracuseStep 1943407 = 2915111) B2915111
theorem B2915117 : Blo 1941435 2915117 := bbase (se 3 (by rfl) ⟨546584, by rfl⟩ : syracuseStep 2915117 = 1093169) (by norm_num)
theorem B1943411 : Blo 1941435 1943411 := bstep (se 1 (by rfl) ⟨1457558, by rfl⟩ : syracuseStep 1943411 = 2915117) B2915117
theorem B4372685 : Blo 1941435 4372685 := bbase (se 3 (by rfl) ⟨819878, by rfl⟩ : syracuseStep 4372685 = 1639757) (by norm_num)
theorem B2915123 : Blo 1941435 2915123 := bstep (se 1 (by rfl) ⟨2186342, by rfl⟩ : syracuseStep 2915123 = 4372685) B4372685
theorem B1943415 : Blo 1941435 1943415 := bstep (se 1 (by rfl) ⟨1457561, by rfl⟩ : syracuseStep 1943415 = 2915123) B2915123
theorem B2459641 : Blo 1941435 2459641 := bbase (se 2 (by rfl) ⟨922365, by rfl⟩ : syracuseStep 2459641 = 1844731) (by norm_num)
theorem B3279521 : Blo 1941435 3279521 := bstep (se 2 (by rfl) ⟨1229820, by rfl⟩ : syracuseStep 3279521 = 2459641) B2459641
theorem B2186347 : Blo 1941435 2186347 := bstep (se 1 (by rfl) ⟨1639760, by rfl⟩ : syracuseStep 2186347 = 3279521) B3279521
theorem B2915129 : Blo 1941435 2915129 := bstep (se 2 (by rfl) ⟨1093173, by rfl⟩ : syracuseStep 2915129 = 2186347) B2186347
theorem B1943419 : Blo 1941435 1943419 := bstep (se 1 (by rfl) ⟨1457564, by rfl⟩ : syracuseStep 1943419 = 2915129) B2915129
theorem B2954909 : Blo 1941435 2954909 := bbase (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) (by norm_num)
theorem B1969939 : Blo 1941435 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B10506341 : Blo 1941435 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B7004227 : Blo 1941435 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B9338969 : Blo 1941435 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B6225979 : Blo 1941435 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B8301305 : Blo 1941435 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B22136813 : Blo 1941435 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B14757875 : Blo 1941435 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B9838583 : Blo 1941435 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B6559055 : Blo 1941435 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B4372703 : Blo 1941435 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B2915135 : Blo 1941435 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B1943423 : Blo 1941435 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B2915141 : Blo 1941435 2915141 := bbase (se 4 (by rfl) ⟨273294, by rfl⟩ : syracuseStep 2915141 = 546589) (by norm_num)
theorem B1943427 : Blo 1941435 1943427 := bstep (se 1 (by rfl) ⟨1457570, by rfl⟩ : syracuseStep 1943427 = 2915141) B2915141
theorem B3279541 : Blo 1941435 3279541 := bbase (se 5 (by rfl) ⟨153728, by rfl⟩ : syracuseStep 3279541 = 307457) (by norm_num)
theorem B4372721 : Blo 1941435 4372721 := bstep (se 2 (by rfl) ⟨1639770, by rfl⟩ : syracuseStep 4372721 = 3279541) B3279541
theorem B2915147 : Blo 1941435 2915147 := bstep (se 1 (by rfl) ⟨2186360, by rfl⟩ : syracuseStep 2915147 = 4372721) B4372721
theorem B1943431 : Blo 1941435 1943431 := bstep (se 1 (by rfl) ⟨1457573, by rfl⟩ : syracuseStep 1943431 = 2915147) B2915147
theorem B2186365 : Blo 1941435 2186365 := bbase (se 3 (by rfl) ⟨409943, by rfl⟩ : syracuseStep 2186365 = 819887) (by norm_num)
theorem B2915153 : Blo 1941435 2915153 := bstep (se 2 (by rfl) ⟨1093182, by rfl⟩ : syracuseStep 2915153 = 2186365) B2186365
theorem B1943435 : Blo 1941435 1943435 := bstep (se 1 (by rfl) ⟨1457576, by rfl⟩ : syracuseStep 1943435 = 2915153) B2915153
theorem C0 (j : ℕ) (h1 : 485358 ≤ j) (h2 : j ≤ 485858) : Blo 1941435 (4 * j + 3) := by
  interval_cases j
  · exact B1941435
  · exact B1941439
  · exact B1941443
  · exact B1941447
  · exact B1941451
  · exact B1941455
  · exact B1941459
  · exact B1941463
  · exact B1941467
  · exact B1941471
  · exact B1941475
  · exact B1941479
  · exact B1941483
  · exact B1941487
  · exact B1941491
  · exact B1941495
  · exact B1941499
  · exact B1941503
  · exact B1941507
  · exact B1941511
  · exact B1941515
  · exact B1941519
  · exact B1941523
  · exact B1941527
  · exact B1941531
  · exact B1941535
  · exact B1941539
  · exact B1941543
  · exact B1941547
  · exact B1941551
  · exact B1941555
  · exact B1941559
  · exact B1941563
  · exact B1941567
  · exact B1941571
  · exact B1941575
  · exact B1941579
  · exact B1941583
  · exact B1941587
  · exact B1941591
  · exact B1941595
  · exact B1941599
  · exact B1941603
  · exact B1941607
  · exact B1941611
  · exact B1941615
  · exact B1941619
  · exact B1941623
  · exact B1941627
  · exact B1941631
  · exact B1941635
  · exact B1941639
  · exact B1941643
  · exact B1941647
  · exact B1941651
  · exact B1941655
  · exact B1941659
  · exact B1941663
  · exact B1941667
  · exact B1941671
  · exact B1941675
  · exact B1941679
  · exact B1941683
  · exact B1941687
  · exact B1941691
  · exact B1941695
  · exact B1941699
  · exact B1941703
  · exact B1941707
  · exact B1941711
  · exact B1941715
  · exact B1941719
  · exact B1941723
  · exact B1941727
  · exact B1941731
  · exact B1941735
  · exact B1941739
  · exact B1941743
  · exact B1941747
  · exact B1941751
  · exact B1941755
  · exact B1941759
  · exact B1941763
  · exact B1941767
  · exact B1941771
  · exact B1941775
  · exact B1941779
  · exact B1941783
  · exact B1941787
  · exact B1941791
  · exact B1941795
  · exact B1941799
  · exact B1941803
  · exact B1941807
  · exact B1941811
  · exact B1941815
  · exact B1941819
  · exact B1941823
  · exact B1941827
  · exact B1941831
  · exact B1941835
  · exact B1941839
  · exact B1941843
  · exact B1941847
  · exact B1941851
  · exact B1941855
  · exact B1941859
  · exact B1941863
  · exact B1941867
  · exact B1941871
  · exact B1941875
  · exact B1941879
  · exact B1941883
  · exact B1941887
  · exact B1941891
  · exact B1941895
  · exact B1941899
  · exact B1941903
  · exact B1941907
  · exact B1941911
  · exact B1941915
  · exact B1941919
  · exact B1941923
  · exact B1941927
  · exact B1941931
  · exact B1941935
  · exact B1941939
  · exact B1941943
  · exact B1941947
  · exact B1941951
  · exact B1941955
  · exact B1941959
  · exact B1941963
  · exact B1941967
  · exact B1941971
  · exact B1941975
  · exact B1941979
  · exact B1941983
  · exact B1941987
  · exact B1941991
  · exact B1941995
  · exact B1941999
  · exact B1942003
  · exact B1942007
  · exact B1942011
  · exact B1942015
  · exact B1942019
  · exact B1942023
  · exact B1942027
  · exact B1942031
  · exact B1942035
  · exact B1942039
  · exact B1942043
  · exact B1942047
  · exact B1942051
  · exact B1942055
  · exact B1942059
  · exact B1942063
  · exact B1942067
  · exact B1942071
  · exact B1942075
  · exact B1942079
  · exact B1942083
  · exact B1942087
  · exact B1942091
  · exact B1942095
  · exact B1942099
  · exact B1942103
  · exact B1942107
  · exact B1942111
  · exact B1942115
  · exact B1942119
  · exact B1942123
  · exact B1942127
  · exact B1942131
  · exact B1942135
  · exact B1942139
  · exact B1942143
  · exact B1942147
  · exact B1942151
  · exact B1942155
  · exact B1942159
  · exact B1942163
  · exact B1942167
  · exact B1942171
  · exact B1942175
  · exact B1942179
  · exact B1942183
  · exact B1942187
  · exact B1942191
  · exact B1942195
  · exact B1942199
  · exact B1942203
  · exact B1942207
  · exact B1942211
  · exact B1942215
  · exact B1942219
  · exact B1942223
  · exact B1942227
  · exact B1942231
  · exact B1942235
  · exact B1942239
  · exact B1942243
  · exact B1942247
  · exact B1942251
  · exact B1942255
  · exact B1942259
  · exact B1942263
  · exact B1942267
  · exact B1942271
  · exact B1942275
  · exact B1942279
  · exact B1942283
  · exact B1942287
  · exact B1942291
  · exact B1942295
  · exact B1942299
  · exact B1942303
  · exact B1942307
  · exact B1942311
  · exact B1942315
  · exact B1942319
  · exact B1942323
  · exact B1942327
  · exact B1942331
  · exact B1942335
  · exact B1942339
  · exact B1942343
  · exact B1942347
  · exact B1942351
  · exact B1942355
  · exact B1942359
  · exact B1942363
  · exact B1942367
  · exact B1942371
  · exact B1942375
  · exact B1942379
  · exact B1942383
  · exact B1942387
  · exact B1942391
  · exact B1942395
  · exact B1942399
  · exact B1942403
  · exact B1942407
  · exact B1942411
  · exact B1942415
  · exact B1942419
  · exact B1942423
  · exact B1942427
  · exact B1942431
  · exact B1942435
  · exact B1942439
  · exact B1942443
  · exact B1942447
  · exact B1942451
  · exact B1942455
  · exact B1942459
  · exact B1942463
  · exact B1942467
  · exact B1942471
  · exact B1942475
  · exact B1942479
  · exact B1942483
  · exact B1942487
  · exact B1942491
  · exact B1942495
  · exact B1942499
  · exact B1942503
  · exact B1942507
  · exact B1942511
  · exact B1942515
  · exact B1942519
  · exact B1942523
  · exact B1942527
  · exact B1942531
  · exact B1942535
  · exact B1942539
  · exact B1942543
  · exact B1942547
  · exact B1942551
  · exact B1942555
  · exact B1942559
  · exact B1942563
  · exact B1942567
  · exact B1942571
  · exact B1942575
  · exact B1942579
  · exact B1942583
  · exact B1942587
  · exact B1942591
  · exact B1942595
  · exact B1942599
  · exact B1942603
  · exact B1942607
  · exact B1942611
  · exact B1942615
  · exact B1942619
  · exact B1942623
  · exact B1942627
  · exact B1942631
  · exact B1942635
  · exact B1942639
  · exact B1942643
  · exact B1942647
  · exact B1942651
  · exact B1942655
  · exact B1942659
  · exact B1942663
  · exact B1942667
  · exact B1942671
  · exact B1942675
  · exact B1942679
  · exact B1942683
  · exact B1942687
  · exact B1942691
  · exact B1942695
  · exact B1942699
  · exact B1942703
  · exact B1942707
  · exact B1942711
  · exact B1942715
  · exact B1942719
  · exact B1942723
  · exact B1942727
  · exact B1942731
  · exact B1942735
  · exact B1942739
  · exact B1942743
  · exact B1942747
  · exact B1942751
  · exact B1942755
  · exact B1942759
  · exact B1942763
  · exact B1942767
  · exact B1942771
  · exact B1942775
  · exact B1942779
  · exact B1942783
  · exact B1942787
  · exact B1942791
  · exact B1942795
  · exact B1942799
  · exact B1942803
  · exact B1942807
  · exact B1942811
  · exact B1942815
  · exact B1942819
  · exact B1942823
  · exact B1942827
  · exact B1942831
  · exact B1942835
  · exact B1942839
  · exact B1942843
  · exact B1942847
  · exact B1942851
  · exact B1942855
  · exact B1942859
  · exact B1942863
  · exact B1942867
  · exact B1942871
  · exact B1942875
  · exact B1942879
  · exact B1942883
  · exact B1942887
  · exact B1942891
  · exact B1942895
  · exact B1942899
  · exact B1942903
  · exact B1942907
  · exact B1942911
  · exact B1942915
  · exact B1942919
  · exact B1942923
  · exact B1942927
  · exact B1942931
  · exact B1942935
  · exact B1942939
  · exact B1942943
  · exact B1942947
  · exact B1942951
  · exact B1942955
  · exact B1942959
  · exact B1942963
  · exact B1942967
  · exact B1942971
  · exact B1942975
  · exact B1942979
  · exact B1942983
  · exact B1942987
  · exact B1942991
  · exact B1942995
  · exact B1942999
  · exact B1943003
  · exact B1943007
  · exact B1943011
  · exact B1943015
  · exact B1943019
  · exact B1943023
  · exact B1943027
  · exact B1943031
  · exact B1943035
  · exact B1943039
  · exact B1943043
  · exact B1943047
  · exact B1943051
  · exact B1943055
  · exact B1943059
  · exact B1943063
  · exact B1943067
  · exact B1943071
  · exact B1943075
  · exact B1943079
  · exact B1943083
  · exact B1943087
  · exact B1943091
  · exact B1943095
  · exact B1943099
  · exact B1943103
  · exact B1943107
  · exact B1943111
  · exact B1943115
  · exact B1943119
  · exact B1943123
  · exact B1943127
  · exact B1943131
  · exact B1943135
  · exact B1943139
  · exact B1943143
  · exact B1943147
  · exact B1943151
  · exact B1943155
  · exact B1943159
  · exact B1943163
  · exact B1943167
  · exact B1943171
  · exact B1943175
  · exact B1943179
  · exact B1943183
  · exact B1943187
  · exact B1943191
  · exact B1943195
  · exact B1943199
  · exact B1943203
  · exact B1943207
  · exact B1943211
  · exact B1943215
  · exact B1943219
  · exact B1943223
  · exact B1943227
  · exact B1943231
  · exact B1943235
  · exact B1943239
  · exact B1943243
  · exact B1943247
  · exact B1943251
  · exact B1943255
  · exact B1943259
  · exact B1943263
  · exact B1943267
  · exact B1943271
  · exact B1943275
  · exact B1943279
  · exact B1943283
  · exact B1943287
  · exact B1943291
  · exact B1943295
  · exact B1943299
  · exact B1943303
  · exact B1943307
  · exact B1943311
  · exact B1943315
  · exact B1943319
  · exact B1943323
  · exact B1943327
  · exact B1943331
  · exact B1943335
  · exact B1943339
  · exact B1943343
  · exact B1943347
  · exact B1943351
  · exact B1943355
  · exact B1943359
  · exact B1943363
  · exact B1943367
  · exact B1943371
  · exact B1943375
  · exact B1943379
  · exact B1943383
  · exact B1943387
  · exact B1943391
  · exact B1943395
  · exact B1943399
  · exact B1943403
  · exact B1943407
  · exact B1943411
  · exact B1943415
  · exact B1943419
  · exact B1943423
  · exact B1943427
  · exact B1943431
  · exact B1943435
theorem solution (m : ℕ) (hlo : 1941435 ≤ m) (hhi : m ≤ 1943435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 485358 ≤ j := by omega
    have hj2 : j ≤ 485858 := by omega
    have hb : Blo 1941435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
