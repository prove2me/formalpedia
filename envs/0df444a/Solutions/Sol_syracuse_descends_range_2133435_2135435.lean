-- Prove2me | solution 1 for syracuse_descends_range_2133435_2135435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:09.970925+00:00
-- url     : https://prove2.me/submissions/e6144685-7d6f-479f-b6c2-d34a504d4f9d

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

theorem B3600173 : Blo 2133435 3600173 := bbase (se 3 (by rfl) ⟨675032, by rfl⟩ : syracuseStep 3600173 = 1350065) (by norm_num)
theorem B2400115 : Blo 2133435 2400115 := bstep (se 1 (by rfl) ⟨1800086, by rfl⟩ : syracuseStep 2400115 = 3600173) B3600173
theorem B3200153 : Blo 2133435 3200153 := bstep (se 2 (by rfl) ⟨1200057, by rfl⟩ : syracuseStep 3200153 = 2400115) B2400115
theorem B2133435 : Blo 2133435 2133435 := bstep (se 1 (by rfl) ⟨1600076, by rfl⟩ : syracuseStep 2133435 = 3200153) B3200153
theorem B3243821 : Blo 2133435 3243821 := bbase (se 3 (by rfl) ⟨608216, by rfl⟩ : syracuseStep 3243821 = 1216433) (by norm_num)
theorem B8650189 : Blo 2133435 8650189 := bstep (se 3 (by rfl) ⟨1621910, by rfl⟩ : syracuseStep 8650189 = 3243821) B3243821
theorem B11533585 : Blo 2133435 11533585 := bstep (se 2 (by rfl) ⟨4325094, by rfl⟩ : syracuseStep 11533585 = 8650189) B8650189
theorem B15378113 : Blo 2133435 15378113 := bstep (se 2 (by rfl) ⟨5766792, by rfl⟩ : syracuseStep 15378113 = 11533585) B11533585
theorem B41008301 : Blo 2133435 41008301 := bstep (se 3 (by rfl) ⟨7689056, by rfl⟩ : syracuseStep 41008301 = 15378113) B15378113
theorem B27338867 : Blo 2133435 27338867 := bstep (se 1 (by rfl) ⟨20504150, by rfl⟩ : syracuseStep 27338867 = 41008301) B41008301
theorem B18225911 : Blo 2133435 18225911 := bstep (se 1 (by rfl) ⟨13669433, by rfl⟩ : syracuseStep 18225911 = 27338867) B27338867
theorem B12150607 : Blo 2133435 12150607 := bstep (se 1 (by rfl) ⟨9112955, by rfl⟩ : syracuseStep 12150607 = 18225911) B18225911
theorem B16200809 : Blo 2133435 16200809 := bstep (se 2 (by rfl) ⟨6075303, by rfl⟩ : syracuseStep 16200809 = 12150607) B12150607
theorem B10800539 : Blo 2133435 10800539 := bstep (se 1 (by rfl) ⟨8100404, by rfl⟩ : syracuseStep 10800539 = 16200809) B16200809
theorem B7200359 : Blo 2133435 7200359 := bstep (se 1 (by rfl) ⟨5400269, by rfl⟩ : syracuseStep 7200359 = 10800539) B10800539
theorem B4800239 : Blo 2133435 4800239 := bstep (se 1 (by rfl) ⟨3600179, by rfl⟩ : syracuseStep 4800239 = 7200359) B7200359
theorem B3200159 : Blo 2133435 3200159 := bstep (se 1 (by rfl) ⟨2400119, by rfl⟩ : syracuseStep 3200159 = 4800239) B4800239
theorem B2133439 : Blo 2133435 2133439 := bstep (se 1 (by rfl) ⟨1600079, by rfl⟩ : syracuseStep 2133439 = 3200159) B3200159
theorem B3200165 : Blo 2133435 3200165 := bbase (se 4 (by rfl) ⟨300015, by rfl⟩ : syracuseStep 3200165 = 600031) (by norm_num)
theorem B2133443 : Blo 2133435 2133443 := bstep (se 1 (by rfl) ⟨1600082, by rfl⟩ : syracuseStep 2133443 = 3200165) B3200165
theorem B2700145 : Blo 2133435 2700145 := bbase (se 2 (by rfl) ⟨1012554, by rfl⟩ : syracuseStep 2700145 = 2025109) (by norm_num)
theorem B3600193 : Blo 2133435 3600193 := bstep (se 2 (by rfl) ⟨1350072, by rfl⟩ : syracuseStep 3600193 = 2700145) B2700145
theorem B4800257 : Blo 2133435 4800257 := bstep (se 2 (by rfl) ⟨1800096, by rfl⟩ : syracuseStep 4800257 = 3600193) B3600193
theorem B3200171 : Blo 2133435 3200171 := bstep (se 1 (by rfl) ⟨2400128, by rfl⟩ : syracuseStep 3200171 = 4800257) B4800257
theorem B2133447 : Blo 2133435 2133447 := bstep (se 1 (by rfl) ⟨1600085, by rfl⟩ : syracuseStep 2133447 = 3200171) B3200171
theorem B2400133 : Blo 2133435 2400133 := bbase (se 4 (by rfl) ⟨225012, by rfl⟩ : syracuseStep 2400133 = 450025) (by norm_num)
theorem B3200177 : Blo 2133435 3200177 := bstep (se 2 (by rfl) ⟨1200066, by rfl⟩ : syracuseStep 3200177 = 2400133) B2400133
theorem B2133451 : Blo 2133435 2133451 := bstep (se 1 (by rfl) ⟨1600088, by rfl⟩ : syracuseStep 2133451 = 3200177) B3200177
theorem B9237365 : Blo 2133435 9237365 := bbase (se 5 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 9237365 = 866003) (by norm_num)
theorem B6158243 : Blo 2133435 6158243 := bstep (se 1 (by rfl) ⟨4618682, by rfl⟩ : syracuseStep 6158243 = 9237365) B9237365
theorem B4105495 : Blo 2133435 4105495 := bstep (se 1 (by rfl) ⟨3079121, by rfl⟩ : syracuseStep 4105495 = 6158243) B6158243
theorem B5473993 : Blo 2133435 5473993 := bstep (se 2 (by rfl) ⟨2052747, by rfl⟩ : syracuseStep 5473993 = 4105495) B4105495
theorem B7298657 : Blo 2133435 7298657 := bstep (se 2 (by rfl) ⟨2736996, by rfl⟩ : syracuseStep 7298657 = 5473993) B5473993
theorem B4865771 : Blo 2133435 4865771 := bstep (se 1 (by rfl) ⟨3649328, by rfl⟩ : syracuseStep 4865771 = 7298657) B7298657
theorem B12975389 : Blo 2133435 12975389 := bstep (se 3 (by rfl) ⟨2432885, by rfl⟩ : syracuseStep 12975389 = 4865771) B4865771
theorem B8650259 : Blo 2133435 8650259 := bstep (se 1 (by rfl) ⟨6487694, by rfl⟩ : syracuseStep 8650259 = 12975389) B12975389
theorem B5766839 : Blo 2133435 5766839 := bstep (se 1 (by rfl) ⟨4325129, by rfl⟩ : syracuseStep 5766839 = 8650259) B8650259
theorem B3844559 : Blo 2133435 3844559 := bstep (se 1 (by rfl) ⟨2883419, by rfl⟩ : syracuseStep 3844559 = 5766839) B5766839
theorem B2563039 : Blo 2133435 2563039 := bstep (se 1 (by rfl) ⟨1922279, by rfl⟩ : syracuseStep 2563039 = 3844559) B3844559
theorem B3417385 : Blo 2133435 3417385 := bstep (se 2 (by rfl) ⟨1281519, by rfl⟩ : syracuseStep 3417385 = 2563039) B2563039
theorem B4556513 : Blo 2133435 4556513 := bstep (se 2 (by rfl) ⟨1708692, by rfl⟩ : syracuseStep 4556513 = 3417385) B3417385
theorem B3037675 : Blo 2133435 3037675 := bstep (se 1 (by rfl) ⟨2278256, by rfl⟩ : syracuseStep 3037675 = 4556513) B4556513
theorem B4050233 : Blo 2133435 4050233 := bstep (se 2 (by rfl) ⟨1518837, by rfl⟩ : syracuseStep 4050233 = 3037675) B3037675
theorem B2700155 : Blo 2133435 2700155 := bstep (se 1 (by rfl) ⟨2025116, by rfl⟩ : syracuseStep 2700155 = 4050233) B4050233
theorem B7200413 : Blo 2133435 7200413 := bstep (se 3 (by rfl) ⟨1350077, by rfl⟩ : syracuseStep 7200413 = 2700155) B2700155
theorem B4800275 : Blo 2133435 4800275 := bstep (se 1 (by rfl) ⟨3600206, by rfl⟩ : syracuseStep 4800275 = 7200413) B7200413
theorem B3200183 : Blo 2133435 3200183 := bstep (se 1 (by rfl) ⟨2400137, by rfl⟩ : syracuseStep 3200183 = 4800275) B4800275
theorem B2133455 : Blo 2133435 2133455 := bstep (se 1 (by rfl) ⟨1600091, by rfl⟩ : syracuseStep 2133455 = 3200183) B3200183
theorem B3200189 : Blo 2133435 3200189 := bbase (se 3 (by rfl) ⟨600035, by rfl⟩ : syracuseStep 3200189 = 1200071) (by norm_num)
theorem B2133459 : Blo 2133435 2133459 := bstep (se 1 (by rfl) ⟨1600094, by rfl⟩ : syracuseStep 2133459 = 3200189) B3200189
theorem B4800293 : Blo 2133435 4800293 := bbase (se 4 (by rfl) ⟨450027, by rfl⟩ : syracuseStep 4800293 = 900055) (by norm_num)
theorem B3200195 : Blo 2133435 3200195 := bstep (se 1 (by rfl) ⟨2400146, by rfl⟩ : syracuseStep 3200195 = 4800293) B4800293
theorem B2133463 : Blo 2133435 2133463 := bstep (se 1 (by rfl) ⟨1600097, by rfl⟩ : syracuseStep 2133463 = 3200195) B3200195
theorem B5400341 : Blo 2133435 5400341 := bbase (se 6 (by rfl) ⟨126570, by rfl⟩ : syracuseStep 5400341 = 253141) (by norm_num)
theorem B3600227 : Blo 2133435 3600227 := bstep (se 1 (by rfl) ⟨2700170, by rfl⟩ : syracuseStep 3600227 = 5400341) B5400341
theorem B2400151 : Blo 2133435 2400151 := bstep (se 1 (by rfl) ⟨1800113, by rfl⟩ : syracuseStep 2400151 = 3600227) B3600227
theorem B3200201 : Blo 2133435 3200201 := bstep (se 2 (by rfl) ⟨1200075, by rfl⟩ : syracuseStep 3200201 = 2400151) B2400151
theorem B2133467 : Blo 2133435 2133467 := bstep (se 1 (by rfl) ⟨1600100, by rfl⟩ : syracuseStep 2133467 = 3200201) B3200201
theorem B9113093 : Blo 2133435 9113093 := bbase (se 4 (by rfl) ⟨854352, by rfl⟩ : syracuseStep 9113093 = 1708705) (by norm_num)
theorem B6075395 : Blo 2133435 6075395 := bstep (se 1 (by rfl) ⟨4556546, by rfl⟩ : syracuseStep 6075395 = 9113093) B9113093
theorem B4050263 : Blo 2133435 4050263 := bstep (se 1 (by rfl) ⟨3037697, by rfl⟩ : syracuseStep 4050263 = 6075395) B6075395
theorem B10800701 : Blo 2133435 10800701 := bstep (se 3 (by rfl) ⟨2025131, by rfl⟩ : syracuseStep 10800701 = 4050263) B4050263
theorem B7200467 : Blo 2133435 7200467 := bstep (se 1 (by rfl) ⟨5400350, by rfl⟩ : syracuseStep 7200467 = 10800701) B10800701
theorem B4800311 : Blo 2133435 4800311 := bstep (se 1 (by rfl) ⟨3600233, by rfl⟩ : syracuseStep 4800311 = 7200467) B7200467
theorem B3200207 : Blo 2133435 3200207 := bstep (se 1 (by rfl) ⟨2400155, by rfl⟩ : syracuseStep 3200207 = 4800311) B4800311
theorem B2133471 : Blo 2133435 2133471 := bstep (se 1 (by rfl) ⟨1600103, by rfl⟩ : syracuseStep 2133471 = 3200207) B3200207
theorem B3200213 : Blo 2133435 3200213 := bbase (se 7 (by rfl) ⟨37502, by rfl⟩ : syracuseStep 3200213 = 75005) (by norm_num)
theorem B2133475 : Blo 2133435 2133475 := bstep (se 1 (by rfl) ⟨1600106, by rfl⟩ : syracuseStep 2133475 = 3200213) B3200213
theorem B3037709 : Blo 2133435 3037709 := bbase (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) (by norm_num)
theorem B8100557 : Blo 2133435 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B5400371 : Blo 2133435 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B3600247 : Blo 2133435 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B4800329 : Blo 2133435 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B3200219 : Blo 2133435 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B2133479 : Blo 2133435 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B2400169 : Blo 2133435 2400169 := bbase (se 2 (by rfl) ⟨900063, by rfl⟩ : syracuseStep 2400169 = 1800127) (by norm_num)
theorem B3200225 : Blo 2133435 3200225 := bstep (se 2 (by rfl) ⟨1200084, by rfl⟩ : syracuseStep 3200225 = 2400169) B2400169
theorem B2133483 : Blo 2133435 2133483 := bstep (se 1 (by rfl) ⟨1600112, by rfl⟩ : syracuseStep 2133483 = 3200225) B3200225
theorem B2432921 : Blo 2133435 2432921 := bbase (se 2 (by rfl) ⟨912345, by rfl⟩ : syracuseStep 2432921 = 1824691) (by norm_num)
theorem B6487789 : Blo 2133435 6487789 := bstep (se 3 (by rfl) ⟨1216460, by rfl⟩ : syracuseStep 6487789 = 2432921) B2432921
theorem B8650385 : Blo 2133435 8650385 := bstep (se 2 (by rfl) ⟨3243894, by rfl⟩ : syracuseStep 8650385 = 6487789) B6487789
theorem B5766923 : Blo 2133435 5766923 := bstep (se 1 (by rfl) ⟨4325192, by rfl⟩ : syracuseStep 5766923 = 8650385) B8650385
theorem B15378461 : Blo 2133435 15378461 := bstep (se 3 (by rfl) ⟨2883461, by rfl⟩ : syracuseStep 15378461 = 5766923) B5766923
theorem B10252307 : Blo 2133435 10252307 := bstep (se 1 (by rfl) ⟨7689230, by rfl⟩ : syracuseStep 10252307 = 15378461) B15378461
theorem B6834871 : Blo 2133435 6834871 := bstep (se 1 (by rfl) ⟨5126153, by rfl⟩ : syracuseStep 6834871 = 10252307) B10252307
theorem B9113161 : Blo 2133435 9113161 := bstep (se 2 (by rfl) ⟨3417435, by rfl⟩ : syracuseStep 9113161 = 6834871) B6834871
theorem B12150881 : Blo 2133435 12150881 := bstep (se 2 (by rfl) ⟨4556580, by rfl⟩ : syracuseStep 12150881 = 9113161) B9113161
theorem B8100587 : Blo 2133435 8100587 := bstep (se 1 (by rfl) ⟨6075440, by rfl⟩ : syracuseStep 8100587 = 12150881) B12150881
theorem B5400391 : Blo 2133435 5400391 := bstep (se 1 (by rfl) ⟨4050293, by rfl⟩ : syracuseStep 5400391 = 8100587) B8100587
theorem B7200521 : Blo 2133435 7200521 := bstep (se 2 (by rfl) ⟨2700195, by rfl⟩ : syracuseStep 7200521 = 5400391) B5400391
theorem B4800347 : Blo 2133435 4800347 := bstep (se 1 (by rfl) ⟨3600260, by rfl⟩ : syracuseStep 4800347 = 7200521) B7200521
theorem B3200231 : Blo 2133435 3200231 := bstep (se 1 (by rfl) ⟨2400173, by rfl⟩ : syracuseStep 3200231 = 4800347) B4800347
theorem B2133487 : Blo 2133435 2133487 := bstep (se 1 (by rfl) ⟨1600115, by rfl⟩ : syracuseStep 2133487 = 3200231) B3200231
theorem B3200237 : Blo 2133435 3200237 := bbase (se 3 (by rfl) ⟨600044, by rfl⟩ : syracuseStep 3200237 = 1200089) (by norm_num)
theorem B2133491 : Blo 2133435 2133491 := bstep (se 1 (by rfl) ⟨1600118, by rfl⟩ : syracuseStep 2133491 = 3200237) B3200237
theorem B4800365 : Blo 2133435 4800365 := bbase (se 3 (by rfl) ⟨900068, by rfl⟩ : syracuseStep 4800365 = 1800137) (by norm_num)
theorem B3200243 : Blo 2133435 3200243 := bstep (se 1 (by rfl) ⟨2400182, by rfl⟩ : syracuseStep 3200243 = 4800365) B4800365
theorem B2133495 : Blo 2133435 2133495 := bstep (se 1 (by rfl) ⟨1600121, by rfl⟩ : syracuseStep 2133495 = 3200243) B3200243
theorem B4050317 : Blo 2133435 4050317 := bbase (se 3 (by rfl) ⟨759434, by rfl⟩ : syracuseStep 4050317 = 1518869) (by norm_num)
theorem B2700211 : Blo 2133435 2700211 := bstep (se 1 (by rfl) ⟨2025158, by rfl⟩ : syracuseStep 2700211 = 4050317) B4050317
theorem B3600281 : Blo 2133435 3600281 := bstep (se 2 (by rfl) ⟨1350105, by rfl⟩ : syracuseStep 3600281 = 2700211) B2700211
theorem B2400187 : Blo 2133435 2400187 := bstep (se 1 (by rfl) ⟨1800140, by rfl⟩ : syracuseStep 2400187 = 3600281) B3600281
theorem B3200249 : Blo 2133435 3200249 := bstep (se 2 (by rfl) ⟨1200093, by rfl⟩ : syracuseStep 3200249 = 2400187) B2400187
theorem B2133499 : Blo 2133435 2133499 := bstep (se 1 (by rfl) ⟨1600124, by rfl⟩ : syracuseStep 2133499 = 3200249) B3200249
theorem B2466133 : Blo 2133435 2466133 := bbase (se 10 (by rfl) ⟨3612, by rfl⟩ : syracuseStep 2466133 = 7225) (by norm_num)
theorem B13152709 : Blo 2133435 13152709 := bstep (se 4 (by rfl) ⟨1233066, by rfl⟩ : syracuseStep 13152709 = 2466133) B2466133
theorem B17536945 : Blo 2133435 17536945 := bstep (se 2 (by rfl) ⟨6576354, by rfl⟩ : syracuseStep 17536945 = 13152709) B13152709
theorem B23382593 : Blo 2133435 23382593 := bstep (se 2 (by rfl) ⟨8768472, by rfl⟩ : syracuseStep 23382593 = 17536945) B17536945
theorem B15588395 : Blo 2133435 15588395 := bstep (se 1 (by rfl) ⟨11691296, by rfl⟩ : syracuseStep 15588395 = 23382593) B23382593
theorem B10392263 : Blo 2133435 10392263 := bstep (se 1 (by rfl) ⟨7794197, by rfl⟩ : syracuseStep 10392263 = 15588395) B15588395
theorem B6928175 : Blo 2133435 6928175 := bstep (se 1 (by rfl) ⟨5196131, by rfl⟩ : syracuseStep 6928175 = 10392263) B10392263
theorem B4618783 : Blo 2133435 4618783 := bstep (se 1 (by rfl) ⟨3464087, by rfl⟩ : syracuseStep 4618783 = 6928175) B6928175
theorem B6158377 : Blo 2133435 6158377 := bstep (se 2 (by rfl) ⟨2309391, by rfl⟩ : syracuseStep 6158377 = 4618783) B4618783
theorem B8211169 : Blo 2133435 8211169 := bstep (se 2 (by rfl) ⟨3079188, by rfl⟩ : syracuseStep 8211169 = 6158377) B6158377
theorem B10948225 : Blo 2133435 10948225 := bstep (se 2 (by rfl) ⟨4105584, by rfl⟩ : syracuseStep 10948225 = 8211169) B8211169
theorem B14597633 : Blo 2133435 14597633 := bstep (se 2 (by rfl) ⟨5474112, by rfl⟩ : syracuseStep 14597633 = 10948225) B10948225
theorem B9731755 : Blo 2133435 9731755 := bstep (se 1 (by rfl) ⟨7298816, by rfl⟩ : syracuseStep 9731755 = 14597633) B14597633
theorem B12975673 : Blo 2133435 12975673 := bstep (se 2 (by rfl) ⟨4865877, by rfl⟩ : syracuseStep 12975673 = 9731755) B9731755
theorem B17300897 : Blo 2133435 17300897 := bstep (se 2 (by rfl) ⟨6487836, by rfl⟩ : syracuseStep 17300897 = 12975673) B12975673
theorem B11533931 : Blo 2133435 11533931 := bstep (se 1 (by rfl) ⟨8650448, by rfl⟩ : syracuseStep 11533931 = 17300897) B17300897
theorem B7689287 : Blo 2133435 7689287 := bstep (se 1 (by rfl) ⟨5766965, by rfl⟩ : syracuseStep 7689287 = 11533931) B11533931
theorem B20504765 : Blo 2133435 20504765 := bstep (se 3 (by rfl) ⟨3844643, by rfl⟩ : syracuseStep 20504765 = 7689287) B7689287
theorem B54679373 : Blo 2133435 54679373 := bstep (se 3 (by rfl) ⟨10252382, by rfl⟩ : syracuseStep 54679373 = 20504765) B20504765
theorem B36452915 : Blo 2133435 36452915 := bstep (se 1 (by rfl) ⟨27339686, by rfl⟩ : syracuseStep 36452915 = 54679373) B54679373
theorem B24301943 : Blo 2133435 24301943 := bstep (se 1 (by rfl) ⟨18226457, by rfl⟩ : syracuseStep 24301943 = 36452915) B36452915
theorem B16201295 : Blo 2133435 16201295 := bstep (se 1 (by rfl) ⟨12150971, by rfl⟩ : syracuseStep 16201295 = 24301943) B24301943
theorem B10800863 : Blo 2133435 10800863 := bstep (se 1 (by rfl) ⟨8100647, by rfl⟩ : syracuseStep 10800863 = 16201295) B16201295
theorem B7200575 : Blo 2133435 7200575 := bstep (se 1 (by rfl) ⟨5400431, by rfl⟩ : syracuseStep 7200575 = 10800863) B10800863
theorem B4800383 : Blo 2133435 4800383 := bstep (se 1 (by rfl) ⟨3600287, by rfl⟩ : syracuseStep 4800383 = 7200575) B7200575
theorem B3200255 : Blo 2133435 3200255 := bstep (se 1 (by rfl) ⟨2400191, by rfl⟩ : syracuseStep 3200255 = 4800383) B4800383
theorem B2133503 : Blo 2133435 2133503 := bstep (se 1 (by rfl) ⟨1600127, by rfl⟩ : syracuseStep 2133503 = 3200255) B3200255
theorem B3200261 : Blo 2133435 3200261 := bbase (se 4 (by rfl) ⟨300024, by rfl⟩ : syracuseStep 3200261 = 600049) (by norm_num)
theorem B2133507 : Blo 2133435 2133507 := bstep (se 1 (by rfl) ⟨1600130, by rfl⟩ : syracuseStep 2133507 = 3200261) B3200261
theorem B3600301 : Blo 2133435 3600301 := bbase (se 3 (by rfl) ⟨675056, by rfl⟩ : syracuseStep 3600301 = 1350113) (by norm_num)
theorem B4800401 : Blo 2133435 4800401 := bstep (se 2 (by rfl) ⟨1800150, by rfl⟩ : syracuseStep 4800401 = 3600301) B3600301
theorem B3200267 : Blo 2133435 3200267 := bstep (se 1 (by rfl) ⟨2400200, by rfl⟩ : syracuseStep 3200267 = 4800401) B4800401
theorem B2133511 : Blo 2133435 2133511 := bstep (se 1 (by rfl) ⟨1600133, by rfl⟩ : syracuseStep 2133511 = 3200267) B3200267
theorem B2400205 : Blo 2133435 2400205 := bbase (se 3 (by rfl) ⟨450038, by rfl⟩ : syracuseStep 2400205 = 900077) (by norm_num)
theorem B3200273 : Blo 2133435 3200273 := bstep (se 2 (by rfl) ⟨1200102, by rfl⟩ : syracuseStep 3200273 = 2400205) B2400205
theorem B2133515 : Blo 2133435 2133515 := bstep (se 1 (by rfl) ⟨1600136, by rfl⟩ : syracuseStep 2133515 = 3200273) B3200273
theorem B7200629 : Blo 2133435 7200629 := bbase (se 5 (by rfl) ⟨337529, by rfl⟩ : syracuseStep 7200629 = 675059) (by norm_num)
theorem B4800419 : Blo 2133435 4800419 := bstep (se 1 (by rfl) ⟨3600314, by rfl⟩ : syracuseStep 4800419 = 7200629) B7200629
theorem B3200279 : Blo 2133435 3200279 := bstep (se 1 (by rfl) ⟨2400209, by rfl⟩ : syracuseStep 3200279 = 4800419) B4800419
theorem B2133519 : Blo 2133435 2133519 := bstep (se 1 (by rfl) ⟨1600139, by rfl⟩ : syracuseStep 2133519 = 3200279) B3200279
theorem B3200285 : Blo 2133435 3200285 := bbase (se 3 (by rfl) ⟨600053, by rfl⟩ : syracuseStep 3200285 = 1200107) (by norm_num)
theorem B2133523 : Blo 2133435 2133523 := bstep (se 1 (by rfl) ⟨1600142, by rfl⟩ : syracuseStep 2133523 = 3200285) B3200285
theorem B4800437 : Blo 2133435 4800437 := bbase (se 5 (by rfl) ⟨225020, by rfl⟩ : syracuseStep 4800437 = 450041) (by norm_num)
theorem B3200291 : Blo 2133435 3200291 := bstep (se 1 (by rfl) ⟨2400218, by rfl⟩ : syracuseStep 3200291 = 4800437) B4800437
theorem B2133527 : Blo 2133435 2133527 := bstep (se 1 (by rfl) ⟨1600145, by rfl⟩ : syracuseStep 2133527 = 3200291) B3200291
theorem B6835013 : Blo 2133435 6835013 := bbase (se 4 (by rfl) ⟨640782, by rfl⟩ : syracuseStep 6835013 = 1281565) (by norm_num)
theorem B4556675 : Blo 2133435 4556675 := bstep (se 1 (by rfl) ⟨3417506, by rfl⟩ : syracuseStep 4556675 = 6835013) B6835013
theorem B12151133 : Blo 2133435 12151133 := bstep (se 3 (by rfl) ⟨2278337, by rfl⟩ : syracuseStep 12151133 = 4556675) B4556675
theorem B8100755 : Blo 2133435 8100755 := bstep (se 1 (by rfl) ⟨6075566, by rfl⟩ : syracuseStep 8100755 = 12151133) B12151133
theorem B5400503 : Blo 2133435 5400503 := bstep (se 1 (by rfl) ⟨4050377, by rfl⟩ : syracuseStep 5400503 = 8100755) B8100755
theorem B3600335 : Blo 2133435 3600335 := bstep (se 1 (by rfl) ⟨2700251, by rfl⟩ : syracuseStep 3600335 = 5400503) B5400503
theorem B2400223 : Blo 2133435 2400223 := bstep (se 1 (by rfl) ⟨1800167, by rfl⟩ : syracuseStep 2400223 = 3600335) B3600335
theorem B3200297 : Blo 2133435 3200297 := bstep (se 2 (by rfl) ⟨1200111, by rfl⟩ : syracuseStep 3200297 = 2400223) B2400223
theorem B2133531 : Blo 2133435 2133531 := bstep (se 1 (by rfl) ⟨1600148, by rfl⟩ : syracuseStep 2133531 = 3200297) B3200297
theorem B5126269 : Blo 2133435 5126269 := bbase (se 3 (by rfl) ⟨961175, by rfl⟩ : syracuseStep 5126269 = 1922351) (by norm_num)
theorem B6835025 : Blo 2133435 6835025 := bstep (se 2 (by rfl) ⟨2563134, by rfl⟩ : syracuseStep 6835025 = 5126269) B5126269
theorem B4556683 : Blo 2133435 4556683 := bstep (se 1 (by rfl) ⟨3417512, by rfl⟩ : syracuseStep 4556683 = 6835025) B6835025
theorem B6075577 : Blo 2133435 6075577 := bstep (se 2 (by rfl) ⟨2278341, by rfl⟩ : syracuseStep 6075577 = 4556683) B4556683
theorem B8100769 : Blo 2133435 8100769 := bstep (se 2 (by rfl) ⟨3037788, by rfl⟩ : syracuseStep 8100769 = 6075577) B6075577
theorem B10801025 : Blo 2133435 10801025 := bstep (se 2 (by rfl) ⟨4050384, by rfl⟩ : syracuseStep 10801025 = 8100769) B8100769
theorem B7200683 : Blo 2133435 7200683 := bstep (se 1 (by rfl) ⟨5400512, by rfl⟩ : syracuseStep 7200683 = 10801025) B10801025
theorem B4800455 : Blo 2133435 4800455 := bstep (se 1 (by rfl) ⟨3600341, by rfl⟩ : syracuseStep 4800455 = 7200683) B7200683
theorem B3200303 : Blo 2133435 3200303 := bstep (se 1 (by rfl) ⟨2400227, by rfl⟩ : syracuseStep 3200303 = 4800455) B4800455
theorem B2133535 : Blo 2133435 2133535 := bstep (se 1 (by rfl) ⟨1600151, by rfl⟩ : syracuseStep 2133535 = 3200303) B3200303
theorem B3200309 : Blo 2133435 3200309 := bbase (se 5 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 3200309 = 300029) (by norm_num)
theorem B2133539 : Blo 2133435 2133539 := bstep (se 1 (by rfl) ⟨1600154, by rfl⟩ : syracuseStep 2133539 = 3200309) B3200309
theorem B5400533 : Blo 2133435 5400533 := bbase (se 7 (by rfl) ⟨63287, by rfl⟩ : syracuseStep 5400533 = 126575) (by norm_num)
theorem B3600355 : Blo 2133435 3600355 := bstep (se 1 (by rfl) ⟨2700266, by rfl⟩ : syracuseStep 3600355 = 5400533) B5400533
theorem B4800473 : Blo 2133435 4800473 := bstep (se 2 (by rfl) ⟨1800177, by rfl⟩ : syracuseStep 4800473 = 3600355) B3600355
theorem B3200315 : Blo 2133435 3200315 := bstep (se 1 (by rfl) ⟨2400236, by rfl⟩ : syracuseStep 3200315 = 4800473) B4800473
theorem B2133543 : Blo 2133435 2133543 := bstep (se 1 (by rfl) ⟨1600157, by rfl⟩ : syracuseStep 2133543 = 3200315) B3200315
theorem B2400241 : Blo 2133435 2400241 := bbase (se 2 (by rfl) ⟨900090, by rfl⟩ : syracuseStep 2400241 = 1800181) (by norm_num)
theorem B3200321 : Blo 2133435 3200321 := bstep (se 2 (by rfl) ⟨1200120, by rfl⟩ : syracuseStep 3200321 = 2400241) B2400241
theorem B2133547 : Blo 2133435 2133547 := bstep (se 1 (by rfl) ⟨1600160, by rfl⟩ : syracuseStep 2133547 = 3200321) B3200321
theorem B65690837 : Blo 2133435 65690837 := bbase (se 7 (by rfl) ⟨769814, by rfl⟩ : syracuseStep 65690837 = 1539629) (by norm_num)
theorem B43793891 : Blo 2133435 43793891 := bstep (se 1 (by rfl) ⟨32845418, by rfl⟩ : syracuseStep 43793891 = 65690837) B65690837
theorem B29195927 : Blo 2133435 29195927 := bstep (se 1 (by rfl) ⟨21896945, by rfl⟩ : syracuseStep 29195927 = 43793891) B43793891
theorem B19463951 : Blo 2133435 19463951 := bstep (se 1 (by rfl) ⟨14597963, by rfl⟩ : syracuseStep 19463951 = 29195927) B29195927
theorem B12975967 : Blo 2133435 12975967 := bstep (se 1 (by rfl) ⟨9731975, by rfl⟩ : syracuseStep 12975967 = 19463951) B19463951
theorem B17301289 : Blo 2133435 17301289 := bstep (se 2 (by rfl) ⟨6487983, by rfl⟩ : syracuseStep 17301289 = 12975967) B12975967
theorem B23068385 : Blo 2133435 23068385 := bstep (se 2 (by rfl) ⟨8650644, by rfl⟩ : syracuseStep 23068385 = 17301289) B17301289
theorem B15378923 : Blo 2133435 15378923 := bstep (se 1 (by rfl) ⟨11534192, by rfl⟩ : syracuseStep 15378923 = 23068385) B23068385
theorem B10252615 : Blo 2133435 10252615 := bstep (se 1 (by rfl) ⟨7689461, by rfl⟩ : syracuseStep 10252615 = 15378923) B15378923
theorem B13670153 : Blo 2133435 13670153 := bstep (se 2 (by rfl) ⟨5126307, by rfl⟩ : syracuseStep 13670153 = 10252615) B10252615
theorem B9113435 : Blo 2133435 9113435 := bstep (se 1 (by rfl) ⟨6835076, by rfl⟩ : syracuseStep 9113435 = 13670153) B13670153
theorem B6075623 : Blo 2133435 6075623 := bstep (se 1 (by rfl) ⟨4556717, by rfl⟩ : syracuseStep 6075623 = 9113435) B9113435
theorem B4050415 : Blo 2133435 4050415 := bstep (se 1 (by rfl) ⟨3037811, by rfl⟩ : syracuseStep 4050415 = 6075623) B6075623
theorem B5400553 : Blo 2133435 5400553 := bstep (se 2 (by rfl) ⟨2025207, by rfl⟩ : syracuseStep 5400553 = 4050415) B4050415
theorem B7200737 : Blo 2133435 7200737 := bstep (se 2 (by rfl) ⟨2700276, by rfl⟩ : syracuseStep 7200737 = 5400553) B5400553
theorem B4800491 : Blo 2133435 4800491 := bstep (se 1 (by rfl) ⟨3600368, by rfl⟩ : syracuseStep 4800491 = 7200737) B7200737
theorem B3200327 : Blo 2133435 3200327 := bstep (se 1 (by rfl) ⟨2400245, by rfl⟩ : syracuseStep 3200327 = 4800491) B4800491
theorem B2133551 : Blo 2133435 2133551 := bstep (se 1 (by rfl) ⟨1600163, by rfl⟩ : syracuseStep 2133551 = 3200327) B3200327
theorem B3200333 : Blo 2133435 3200333 := bbase (se 3 (by rfl) ⟨600062, by rfl⟩ : syracuseStep 3200333 = 1200125) (by norm_num)
theorem B2133555 : Blo 2133435 2133555 := bstep (se 1 (by rfl) ⟨1600166, by rfl⟩ : syracuseStep 2133555 = 3200333) B3200333
theorem B4800509 : Blo 2133435 4800509 := bbase (se 3 (by rfl) ⟨900095, by rfl⟩ : syracuseStep 4800509 = 1800191) (by norm_num)
theorem B3200339 : Blo 2133435 3200339 := bstep (se 1 (by rfl) ⟨2400254, by rfl⟩ : syracuseStep 3200339 = 4800509) B4800509
theorem B2133559 : Blo 2133435 2133559 := bstep (se 1 (by rfl) ⟨1600169, by rfl⟩ : syracuseStep 2133559 = 3200339) B3200339
theorem B3600389 : Blo 2133435 3600389 := bbase (se 4 (by rfl) ⟨337536, by rfl⟩ : syracuseStep 3600389 = 675073) (by norm_num)
theorem B2400259 : Blo 2133435 2400259 := bstep (se 1 (by rfl) ⟨1800194, by rfl⟩ : syracuseStep 2400259 = 3600389) B3600389
theorem B3200345 : Blo 2133435 3200345 := bstep (se 2 (by rfl) ⟨1200129, by rfl⟩ : syracuseStep 3200345 = 2400259) B2400259
theorem B2133563 : Blo 2133435 2133563 := bstep (se 1 (by rfl) ⟨1600172, by rfl⟩ : syracuseStep 2133563 = 3200345) B3200345
theorem B16201781 : Blo 2133435 16201781 := bbase (se 5 (by rfl) ⟨759458, by rfl⟩ : syracuseStep 16201781 = 1518917) (by norm_num)
theorem B10801187 : Blo 2133435 10801187 := bstep (se 1 (by rfl) ⟨8100890, by rfl⟩ : syracuseStep 10801187 = 16201781) B16201781
theorem B7200791 : Blo 2133435 7200791 := bstep (se 1 (by rfl) ⟨5400593, by rfl⟩ : syracuseStep 7200791 = 10801187) B10801187
theorem B4800527 : Blo 2133435 4800527 := bstep (se 1 (by rfl) ⟨3600395, by rfl⟩ : syracuseStep 4800527 = 7200791) B7200791
theorem B3200351 : Blo 2133435 3200351 := bstep (se 1 (by rfl) ⟨2400263, by rfl⟩ : syracuseStep 3200351 = 4800527) B4800527
theorem B2133567 : Blo 2133435 2133567 := bstep (se 1 (by rfl) ⟨1600175, by rfl⟩ : syracuseStep 2133567 = 3200351) B3200351
theorem B3200357 : Blo 2133435 3200357 := bbase (se 4 (by rfl) ⟨300033, by rfl⟩ : syracuseStep 3200357 = 600067) (by norm_num)
theorem B2133571 : Blo 2133435 2133571 := bstep (se 1 (by rfl) ⟨1600178, by rfl⟩ : syracuseStep 2133571 = 3200357) B3200357
theorem B4050461 : Blo 2133435 4050461 := bbase (se 3 (by rfl) ⟨759461, by rfl⟩ : syracuseStep 4050461 = 1518923) (by norm_num)
theorem B2700307 : Blo 2133435 2700307 := bstep (se 1 (by rfl) ⟨2025230, by rfl⟩ : syracuseStep 2700307 = 4050461) B4050461
theorem B3600409 : Blo 2133435 3600409 := bstep (se 2 (by rfl) ⟨1350153, by rfl⟩ : syracuseStep 3600409 = 2700307) B2700307
theorem B4800545 : Blo 2133435 4800545 := bstep (se 2 (by rfl) ⟨1800204, by rfl⟩ : syracuseStep 4800545 = 3600409) B3600409
theorem B3200363 : Blo 2133435 3200363 := bstep (se 1 (by rfl) ⟨2400272, by rfl⟩ : syracuseStep 3200363 = 4800545) B4800545
theorem B2133575 : Blo 2133435 2133575 := bstep (se 1 (by rfl) ⟨1600181, by rfl⟩ : syracuseStep 2133575 = 3200363) B3200363
theorem B2400277 : Blo 2133435 2400277 := bbase (se 6 (by rfl) ⟨56256, by rfl⟩ : syracuseStep 2400277 = 112513) (by norm_num)
theorem B3200369 : Blo 2133435 3200369 := bstep (se 2 (by rfl) ⟨1200138, by rfl⟩ : syracuseStep 3200369 = 2400277) B2400277
theorem B2133579 : Blo 2133435 2133579 := bstep (se 1 (by rfl) ⟨1600184, by rfl⟩ : syracuseStep 2133579 = 3200369) B3200369
theorem B2700317 : Blo 2133435 2700317 := bbase (se 3 (by rfl) ⟨506309, by rfl⟩ : syracuseStep 2700317 = 1012619) (by norm_num)
theorem B7200845 : Blo 2133435 7200845 := bstep (se 3 (by rfl) ⟨1350158, by rfl⟩ : syracuseStep 7200845 = 2700317) B2700317
theorem B4800563 : Blo 2133435 4800563 := bstep (se 1 (by rfl) ⟨3600422, by rfl⟩ : syracuseStep 4800563 = 7200845) B7200845
theorem B3200375 : Blo 2133435 3200375 := bstep (se 1 (by rfl) ⟨2400281, by rfl⟩ : syracuseStep 3200375 = 4800563) B4800563
theorem B2133583 : Blo 2133435 2133583 := bstep (se 1 (by rfl) ⟨1600187, by rfl⟩ : syracuseStep 2133583 = 3200375) B3200375
theorem B3200381 : Blo 2133435 3200381 := bbase (se 3 (by rfl) ⟨600071, by rfl⟩ : syracuseStep 3200381 = 1200143) (by norm_num)
theorem B2133587 : Blo 2133435 2133587 := bstep (se 1 (by rfl) ⟨1600190, by rfl⟩ : syracuseStep 2133587 = 3200381) B3200381
theorem B4800581 : Blo 2133435 4800581 := bbase (se 4 (by rfl) ⟨450054, by rfl⟩ : syracuseStep 4800581 = 900109) (by norm_num)
theorem B3200387 : Blo 2133435 3200387 := bstep (se 1 (by rfl) ⟨2400290, by rfl⟩ : syracuseStep 3200387 = 4800581) B4800581
theorem B2133591 : Blo 2133435 2133591 := bstep (se 1 (by rfl) ⟨1600193, by rfl⟩ : syracuseStep 2133591 = 3200387) B3200387
theorem B6075749 : Blo 2133435 6075749 := bbase (se 4 (by rfl) ⟨569601, by rfl⟩ : syracuseStep 6075749 = 1139203) (by norm_num)
theorem B4050499 : Blo 2133435 4050499 := bstep (se 1 (by rfl) ⟨3037874, by rfl⟩ : syracuseStep 4050499 = 6075749) B6075749
theorem B5400665 : Blo 2133435 5400665 := bstep (se 2 (by rfl) ⟨2025249, by rfl⟩ : syracuseStep 5400665 = 4050499) B4050499
theorem B3600443 : Blo 2133435 3600443 := bstep (se 1 (by rfl) ⟨2700332, by rfl⟩ : syracuseStep 3600443 = 5400665) B5400665
theorem B2400295 : Blo 2133435 2400295 := bstep (se 1 (by rfl) ⟨1800221, by rfl⟩ : syracuseStep 2400295 = 3600443) B3600443
theorem B3200393 : Blo 2133435 3200393 := bstep (se 2 (by rfl) ⟨1200147, by rfl⟩ : syracuseStep 3200393 = 2400295) B2400295
theorem B2133595 : Blo 2133435 2133595 := bstep (se 1 (by rfl) ⟨1600196, by rfl⟩ : syracuseStep 2133595 = 3200393) B3200393
theorem B10801349 : Blo 2133435 10801349 := bbase (se 4 (by rfl) ⟨1012626, by rfl⟩ : syracuseStep 10801349 = 2025253) (by norm_num)
theorem B7200899 : Blo 2133435 7200899 := bstep (se 1 (by rfl) ⟨5400674, by rfl⟩ : syracuseStep 7200899 = 10801349) B10801349
theorem B4800599 : Blo 2133435 4800599 := bstep (se 1 (by rfl) ⟨3600449, by rfl⟩ : syracuseStep 4800599 = 7200899) B7200899
theorem B3200399 : Blo 2133435 3200399 := bstep (se 1 (by rfl) ⟨2400299, by rfl⟩ : syracuseStep 3200399 = 4800599) B4800599
theorem B2133599 : Blo 2133435 2133599 := bstep (se 1 (by rfl) ⟨1600199, by rfl⟩ : syracuseStep 2133599 = 3200399) B3200399
theorem B3200405 : Blo 2133435 3200405 := bbase (se 6 (by rfl) ⟨75009, by rfl⟩ : syracuseStep 3200405 = 150019) (by norm_num)
theorem B2133603 : Blo 2133435 2133603 := bstep (se 1 (by rfl) ⟨1600202, by rfl⟩ : syracuseStep 2133603 = 3200405) B3200405
theorem B4556837 : Blo 2133435 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B12151565 : Blo 2133435 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B8101043 : Blo 2133435 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B5400695 : Blo 2133435 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B3600463 : Blo 2133435 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B4800617 : Blo 2133435 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B3200411 : Blo 2133435 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B2133607 : Blo 2133435 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B2400313 : Blo 2133435 2400313 := bbase (se 2 (by rfl) ⟨900117, by rfl⟩ : syracuseStep 2400313 = 1800235) (by norm_num)
theorem B3200417 : Blo 2133435 3200417 := bstep (se 2 (by rfl) ⟨1200156, by rfl⟩ : syracuseStep 3200417 = 2400313) B2400313
theorem B2133611 : Blo 2133435 2133611 := bstep (se 1 (by rfl) ⟨1600208, by rfl⟩ : syracuseStep 2133611 = 3200417) B3200417
theorem B23383829 : Blo 2133435 23383829 := bbase (se 6 (by rfl) ⟨548058, by rfl⟩ : syracuseStep 23383829 = 1096117) (by norm_num)
theorem B15589219 : Blo 2133435 15589219 := bstep (se 1 (by rfl) ⟨11691914, by rfl⟩ : syracuseStep 15589219 = 23383829) B23383829
theorem B20785625 : Blo 2133435 20785625 := bstep (se 2 (by rfl) ⟨7794609, by rfl⟩ : syracuseStep 20785625 = 15589219) B15589219
theorem B13857083 : Blo 2133435 13857083 := bstep (se 1 (by rfl) ⟨10392812, by rfl⟩ : syracuseStep 13857083 = 20785625) B20785625
theorem B9238055 : Blo 2133435 9238055 := bstep (se 1 (by rfl) ⟨6928541, by rfl⟩ : syracuseStep 9238055 = 13857083) B13857083
theorem B24634813 : Blo 2133435 24634813 := bstep (se 3 (by rfl) ⟨4619027, by rfl⟩ : syracuseStep 24634813 = 9238055) B9238055
theorem B32846417 : Blo 2133435 32846417 := bstep (se 2 (by rfl) ⟨12317406, by rfl⟩ : syracuseStep 32846417 = 24634813) B24634813
theorem B21897611 : Blo 2133435 21897611 := bstep (se 1 (by rfl) ⟨16423208, by rfl⟩ : syracuseStep 21897611 = 32846417) B32846417
theorem B14598407 : Blo 2133435 14598407 := bstep (se 1 (by rfl) ⟨10948805, by rfl⟩ : syracuseStep 14598407 = 21897611) B21897611
theorem B9732271 : Blo 2133435 9732271 := bstep (se 1 (by rfl) ⟨7299203, by rfl⟩ : syracuseStep 9732271 = 14598407) B14598407
theorem B12976361 : Blo 2133435 12976361 := bstep (se 2 (by rfl) ⟨4866135, by rfl⟩ : syracuseStep 12976361 = 9732271) B9732271
theorem B8650907 : Blo 2133435 8650907 := bstep (se 1 (by rfl) ⟨6488180, by rfl⟩ : syracuseStep 8650907 = 12976361) B12976361
theorem B5767271 : Blo 2133435 5767271 := bstep (se 1 (by rfl) ⟨4325453, by rfl⟩ : syracuseStep 5767271 = 8650907) B8650907
theorem B3844847 : Blo 2133435 3844847 := bstep (se 1 (by rfl) ⟨2883635, by rfl⟩ : syracuseStep 3844847 = 5767271) B5767271
theorem B2563231 : Blo 2133435 2563231 := bstep (se 1 (by rfl) ⟨1922423, by rfl⟩ : syracuseStep 2563231 = 3844847) B3844847
theorem B3417641 : Blo 2133435 3417641 := bstep (se 2 (by rfl) ⟨1281615, by rfl⟩ : syracuseStep 3417641 = 2563231) B2563231
theorem B2278427 : Blo 2133435 2278427 := bstep (se 1 (by rfl) ⟨1708820, by rfl⟩ : syracuseStep 2278427 = 3417641) B3417641
theorem B6075805 : Blo 2133435 6075805 := bstep (se 3 (by rfl) ⟨1139213, by rfl⟩ : syracuseStep 6075805 = 2278427) B2278427
theorem B8101073 : Blo 2133435 8101073 := bstep (se 2 (by rfl) ⟨3037902, by rfl⟩ : syracuseStep 8101073 = 6075805) B6075805
theorem B5400715 : Blo 2133435 5400715 := bstep (se 1 (by rfl) ⟨4050536, by rfl⟩ : syracuseStep 5400715 = 8101073) B8101073
theorem B7200953 : Blo 2133435 7200953 := bstep (se 2 (by rfl) ⟨2700357, by rfl⟩ : syracuseStep 7200953 = 5400715) B5400715
theorem B4800635 : Blo 2133435 4800635 := bstep (se 1 (by rfl) ⟨3600476, by rfl⟩ : syracuseStep 4800635 = 7200953) B7200953
theorem B3200423 : Blo 2133435 3200423 := bstep (se 1 (by rfl) ⟨2400317, by rfl⟩ : syracuseStep 3200423 = 4800635) B4800635
theorem B2133615 : Blo 2133435 2133615 := bstep (se 1 (by rfl) ⟨1600211, by rfl⟩ : syracuseStep 2133615 = 3200423) B3200423
theorem B3200429 : Blo 2133435 3200429 := bbase (se 3 (by rfl) ⟨600080, by rfl⟩ : syracuseStep 3200429 = 1200161) (by norm_num)
theorem B2133619 : Blo 2133435 2133619 := bstep (se 1 (by rfl) ⟨1600214, by rfl⟩ : syracuseStep 2133619 = 3200429) B3200429
theorem B4800653 : Blo 2133435 4800653 := bbase (se 3 (by rfl) ⟨900122, by rfl⟩ : syracuseStep 4800653 = 1800245) (by norm_num)
theorem B3200435 : Blo 2133435 3200435 := bstep (se 1 (by rfl) ⟨2400326, by rfl⟩ : syracuseStep 3200435 = 4800653) B4800653
theorem B2133623 : Blo 2133435 2133623 := bstep (se 1 (by rfl) ⟨1600217, by rfl⟩ : syracuseStep 2133623 = 3200435) B3200435
theorem B2700373 : Blo 2133435 2700373 := bbase (se 8 (by rfl) ⟨15822, by rfl⟩ : syracuseStep 2700373 = 31645) (by norm_num)
theorem B3600497 : Blo 2133435 3600497 := bstep (se 2 (by rfl) ⟨1350186, by rfl⟩ : syracuseStep 3600497 = 2700373) B2700373
theorem B2400331 : Blo 2133435 2400331 := bstep (se 1 (by rfl) ⟨1800248, by rfl⟩ : syracuseStep 2400331 = 3600497) B3600497
theorem B3200441 : Blo 2133435 3200441 := bstep (se 2 (by rfl) ⟨1200165, by rfl⟩ : syracuseStep 3200441 = 2400331) B2400331
theorem B2133627 : Blo 2133435 2133627 := bstep (se 1 (by rfl) ⟨1600220, by rfl⟩ : syracuseStep 2133627 = 3200441) B3200441
theorem B4745965 : Blo 2133435 4745965 := bbase (se 3 (by rfl) ⟨889868, by rfl⟩ : syracuseStep 4745965 = 1779737) (by norm_num)
theorem B6327953 : Blo 2133435 6327953 := bstep (se 2 (by rfl) ⟨2372982, by rfl⟩ : syracuseStep 6327953 = 4745965) B4745965
theorem B4218635 : Blo 2133435 4218635 := bstep (se 1 (by rfl) ⟨3163976, by rfl⟩ : syracuseStep 4218635 = 6327953) B6327953
theorem B2812423 : Blo 2133435 2812423 := bstep (se 1 (by rfl) ⟨2109317, by rfl⟩ : syracuseStep 2812423 = 4218635) B4218635
theorem B3749897 : Blo 2133435 3749897 := bstep (se 2 (by rfl) ⟨1406211, by rfl⟩ : syracuseStep 3749897 = 2812423) B2812423
theorem B2499931 : Blo 2133435 2499931 := bstep (se 1 (by rfl) ⟨1874948, by rfl⟩ : syracuseStep 2499931 = 3749897) B3749897
theorem B3333241 : Blo 2133435 3333241 := bstep (se 2 (by rfl) ⟨1249965, by rfl⟩ : syracuseStep 3333241 = 2499931) B2499931
theorem B4444321 : Blo 2133435 4444321 := bstep (se 2 (by rfl) ⟨1666620, by rfl⟩ : syracuseStep 4444321 = 3333241) B3333241
theorem B5925761 : Blo 2133435 5925761 := bstep (se 2 (by rfl) ⟨2222160, by rfl⟩ : syracuseStep 5925761 = 4444321) B4444321
theorem B3950507 : Blo 2133435 3950507 := bstep (se 1 (by rfl) ⟨2962880, by rfl⟩ : syracuseStep 3950507 = 5925761) B5925761
theorem B2633671 : Blo 2133435 2633671 := bstep (se 1 (by rfl) ⟨1975253, by rfl⟩ : syracuseStep 2633671 = 3950507) B3950507
theorem B3511561 : Blo 2133435 3511561 := bstep (se 2 (by rfl) ⟨1316835, by rfl⟩ : syracuseStep 3511561 = 2633671) B2633671
theorem B4682081 : Blo 2133435 4682081 := bstep (se 2 (by rfl) ⟨1755780, by rfl⟩ : syracuseStep 4682081 = 3511561) B3511561
theorem B12485549 : Blo 2133435 12485549 := bstep (se 3 (by rfl) ⟨2341040, by rfl⟩ : syracuseStep 12485549 = 4682081) B4682081
theorem B33294797 : Blo 2133435 33294797 := bstep (se 3 (by rfl) ⟨6242774, by rfl⟩ : syracuseStep 33294797 = 12485549) B12485549
theorem B22196531 : Blo 2133435 22196531 := bstep (se 1 (by rfl) ⟨16647398, by rfl⟩ : syracuseStep 22196531 = 33294797) B33294797
theorem B14797687 : Blo 2133435 14797687 := bstep (se 1 (by rfl) ⟨11098265, by rfl⟩ : syracuseStep 14797687 = 22196531) B22196531
theorem B19730249 : Blo 2133435 19730249 := bstep (se 2 (by rfl) ⟨7398843, by rfl⟩ : syracuseStep 19730249 = 14797687) B14797687
theorem B13153499 : Blo 2133435 13153499 := bstep (se 1 (by rfl) ⟨9865124, by rfl⟩ : syracuseStep 13153499 = 19730249) B19730249
theorem B8768999 : Blo 2133435 8768999 := bstep (se 1 (by rfl) ⟨6576749, by rfl⟩ : syracuseStep 8768999 = 13153499) B13153499
theorem B23383997 : Blo 2133435 23383997 := bstep (se 3 (by rfl) ⟨4384499, by rfl⟩ : syracuseStep 23383997 = 8768999) B8768999
theorem B15589331 : Blo 2133435 15589331 := bstep (se 1 (by rfl) ⟨11691998, by rfl⟩ : syracuseStep 15589331 = 23383997) B23383997
theorem B10392887 : Blo 2133435 10392887 := bstep (se 1 (by rfl) ⟨7794665, by rfl⟩ : syracuseStep 10392887 = 15589331) B15589331
theorem B6928591 : Blo 2133435 6928591 := bstep (se 1 (by rfl) ⟨5196443, by rfl⟩ : syracuseStep 6928591 = 10392887) B10392887
theorem B9238121 : Blo 2133435 9238121 := bstep (se 2 (by rfl) ⟨3464295, by rfl⟩ : syracuseStep 9238121 = 6928591) B6928591
theorem B6158747 : Blo 2133435 6158747 := bstep (se 1 (by rfl) ⟨4619060, by rfl⟩ : syracuseStep 6158747 = 9238121) B9238121
theorem B4105831 : Blo 2133435 4105831 := bstep (se 1 (by rfl) ⟨3079373, by rfl⟩ : syracuseStep 4105831 = 6158747) B6158747
theorem B5474441 : Blo 2133435 5474441 := bstep (se 2 (by rfl) ⟨2052915, by rfl⟩ : syracuseStep 5474441 = 4105831) B4105831
theorem B3649627 : Blo 2133435 3649627 := bstep (se 1 (by rfl) ⟨2737220, by rfl⟩ : syracuseStep 3649627 = 5474441) B5474441
theorem B19464677 : Blo 2133435 19464677 := bstep (se 4 (by rfl) ⟨1824813, by rfl⟩ : syracuseStep 19464677 = 3649627) B3649627
theorem B12976451 : Blo 2133435 12976451 := bstep (se 1 (by rfl) ⟨9732338, by rfl⟩ : syracuseStep 12976451 = 19464677) B19464677
theorem B8650967 : Blo 2133435 8650967 := bstep (se 1 (by rfl) ⟨6488225, by rfl⟩ : syracuseStep 8650967 = 12976451) B12976451
theorem B92276981 : Blo 2133435 92276981 := bstep (se 5 (by rfl) ⟨4325483, by rfl⟩ : syracuseStep 92276981 = 8650967) B8650967
theorem B61517987 : Blo 2133435 61517987 := bstep (se 1 (by rfl) ⟨46138490, by rfl⟩ : syracuseStep 61517987 = 92276981) B92276981
theorem B41011991 : Blo 2133435 41011991 := bstep (se 1 (by rfl) ⟨30758993, by rfl⟩ : syracuseStep 41011991 = 61517987) B61517987
theorem B27341327 : Blo 2133435 27341327 := bstep (se 1 (by rfl) ⟨20505995, by rfl⟩ : syracuseStep 27341327 = 41011991) B41011991
theorem B18227551 : Blo 2133435 18227551 := bstep (se 1 (by rfl) ⟨13670663, by rfl⟩ : syracuseStep 18227551 = 27341327) B27341327
theorem B24303401 : Blo 2133435 24303401 := bstep (se 2 (by rfl) ⟨9113775, by rfl⟩ : syracuseStep 24303401 = 18227551) B18227551
theorem B16202267 : Blo 2133435 16202267 := bstep (se 1 (by rfl) ⟨12151700, by rfl⟩ : syracuseStep 16202267 = 24303401) B24303401
theorem B10801511 : Blo 2133435 10801511 := bstep (se 1 (by rfl) ⟨8101133, by rfl⟩ : syracuseStep 10801511 = 16202267) B16202267
theorem B7201007 : Blo 2133435 7201007 := bstep (se 1 (by rfl) ⟨5400755, by rfl⟩ : syracuseStep 7201007 = 10801511) B10801511
theorem B4800671 : Blo 2133435 4800671 := bstep (se 1 (by rfl) ⟨3600503, by rfl⟩ : syracuseStep 4800671 = 7201007) B7201007
theorem B3200447 : Blo 2133435 3200447 := bstep (se 1 (by rfl) ⟨2400335, by rfl⟩ : syracuseStep 3200447 = 4800671) B4800671
theorem B2133631 : Blo 2133435 2133631 := bstep (se 1 (by rfl) ⟨1600223, by rfl⟩ : syracuseStep 2133631 = 3200447) B3200447
theorem B3200453 : Blo 2133435 3200453 := bbase (se 4 (by rfl) ⟨300042, by rfl⟩ : syracuseStep 3200453 = 600085) (by norm_num)
theorem B2133635 : Blo 2133435 2133635 := bstep (se 1 (by rfl) ⟨1600226, by rfl⟩ : syracuseStep 2133635 = 3200453) B3200453
theorem B3600517 : Blo 2133435 3600517 := bbase (se 4 (by rfl) ⟨337548, by rfl⟩ : syracuseStep 3600517 = 675097) (by norm_num)
theorem B4800689 : Blo 2133435 4800689 := bstep (se 2 (by rfl) ⟨1800258, by rfl⟩ : syracuseStep 4800689 = 3600517) B3600517
theorem B3200459 : Blo 2133435 3200459 := bstep (se 1 (by rfl) ⟨2400344, by rfl⟩ : syracuseStep 3200459 = 4800689) B4800689
theorem B2133639 : Blo 2133435 2133639 := bstep (se 1 (by rfl) ⟨1600229, by rfl⟩ : syracuseStep 2133639 = 3200459) B3200459
theorem B2400349 : Blo 2133435 2400349 := bbase (se 3 (by rfl) ⟨450065, by rfl⟩ : syracuseStep 2400349 = 900131) (by norm_num)
theorem B3200465 : Blo 2133435 3200465 := bstep (se 2 (by rfl) ⟨1200174, by rfl⟩ : syracuseStep 3200465 = 2400349) B2400349
theorem B2133643 : Blo 2133435 2133643 := bstep (se 1 (by rfl) ⟨1600232, by rfl⟩ : syracuseStep 2133643 = 3200465) B3200465
theorem B7201061 : Blo 2133435 7201061 := bbase (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) (by norm_num)
theorem B4800707 : Blo 2133435 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B3200471 : Blo 2133435 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B2133647 : Blo 2133435 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B3200477 : Blo 2133435 3200477 := bbase (se 3 (by rfl) ⟨600089, by rfl⟩ : syracuseStep 3200477 = 1200179) (by norm_num)
theorem B2133651 : Blo 2133435 2133651 := bstep (se 1 (by rfl) ⟨1600238, by rfl⟩ : syracuseStep 2133651 = 3200477) B3200477
theorem B4800725 : Blo 2133435 4800725 := bbase (se 7 (by rfl) ⟨56258, by rfl⟩ : syracuseStep 4800725 = 112517) (by norm_num)
theorem B3200483 : Blo 2133435 3200483 := bstep (se 1 (by rfl) ⟨2400362, by rfl⟩ : syracuseStep 3200483 = 4800725) B4800725
theorem B2133655 : Blo 2133435 2133655 := bstep (se 1 (by rfl) ⟨1600241, by rfl⟩ : syracuseStep 2133655 = 3200483) B3200483
theorem B9732469 : Blo 2133435 9732469 := bbase (se 5 (by rfl) ⟨456209, by rfl⟩ : syracuseStep 9732469 = 912419) (by norm_num)
theorem B12976625 : Blo 2133435 12976625 := bstep (se 2 (by rfl) ⟨4866234, by rfl⟩ : syracuseStep 12976625 = 9732469) B9732469
theorem B34604333 : Blo 2133435 34604333 := bstep (se 3 (by rfl) ⟨6488312, by rfl⟩ : syracuseStep 34604333 = 12976625) B12976625
theorem B23069555 : Blo 2133435 23069555 := bstep (se 1 (by rfl) ⟨17302166, by rfl⟩ : syracuseStep 23069555 = 34604333) B34604333
theorem B15379703 : Blo 2133435 15379703 := bstep (se 1 (by rfl) ⟨11534777, by rfl⟩ : syracuseStep 15379703 = 23069555) B23069555
theorem B10253135 : Blo 2133435 10253135 := bstep (se 1 (by rfl) ⟨7689851, by rfl⟩ : syracuseStep 10253135 = 15379703) B15379703
theorem B6835423 : Blo 2133435 6835423 := bstep (se 1 (by rfl) ⟨5126567, by rfl⟩ : syracuseStep 6835423 = 10253135) B10253135
theorem B9113897 : Blo 2133435 9113897 := bstep (se 2 (by rfl) ⟨3417711, by rfl⟩ : syracuseStep 9113897 = 6835423) B6835423
theorem B6075931 : Blo 2133435 6075931 := bstep (se 1 (by rfl) ⟨4556948, by rfl⟩ : syracuseStep 6075931 = 9113897) B9113897
theorem B8101241 : Blo 2133435 8101241 := bstep (se 2 (by rfl) ⟨3037965, by rfl⟩ : syracuseStep 8101241 = 6075931) B6075931
theorem B5400827 : Blo 2133435 5400827 := bstep (se 1 (by rfl) ⟨4050620, by rfl⟩ : syracuseStep 5400827 = 8101241) B8101241
theorem B3600551 : Blo 2133435 3600551 := bstep (se 1 (by rfl) ⟨2700413, by rfl⟩ : syracuseStep 3600551 = 5400827) B5400827
theorem B2400367 : Blo 2133435 2400367 := bstep (se 1 (by rfl) ⟨1800275, by rfl⟩ : syracuseStep 2400367 = 3600551) B3600551
theorem B3200489 : Blo 2133435 3200489 := bstep (se 2 (by rfl) ⟨1200183, by rfl⟩ : syracuseStep 3200489 = 2400367) B2400367
theorem B2133659 : Blo 2133435 2133659 := bstep (se 1 (by rfl) ⟨1600244, by rfl⟩ : syracuseStep 2133659 = 3200489) B3200489
theorem B13670869 : Blo 2133435 13670869 := bbase (se 7 (by rfl) ⟨160205, by rfl⟩ : syracuseStep 13670869 = 320411) (by norm_num)
theorem B18227825 : Blo 2133435 18227825 := bstep (se 2 (by rfl) ⟨6835434, by rfl⟩ : syracuseStep 18227825 = 13670869) B13670869
theorem B12151883 : Blo 2133435 12151883 := bstep (se 1 (by rfl) ⟨9113912, by rfl⟩ : syracuseStep 12151883 = 18227825) B18227825
theorem B8101255 : Blo 2133435 8101255 := bstep (se 1 (by rfl) ⟨6075941, by rfl⟩ : syracuseStep 8101255 = 12151883) B12151883
theorem B10801673 : Blo 2133435 10801673 := bstep (se 2 (by rfl) ⟨4050627, by rfl⟩ : syracuseStep 10801673 = 8101255) B8101255
theorem B7201115 : Blo 2133435 7201115 := bstep (se 1 (by rfl) ⟨5400836, by rfl⟩ : syracuseStep 7201115 = 10801673) B10801673
theorem B4800743 : Blo 2133435 4800743 := bstep (se 1 (by rfl) ⟨3600557, by rfl⟩ : syracuseStep 4800743 = 7201115) B7201115
theorem B3200495 : Blo 2133435 3200495 := bstep (se 1 (by rfl) ⟨2400371, by rfl⟩ : syracuseStep 3200495 = 4800743) B4800743
theorem B2133663 : Blo 2133435 2133663 := bstep (se 1 (by rfl) ⟨1600247, by rfl⟩ : syracuseStep 2133663 = 3200495) B3200495
theorem B3200501 : Blo 2133435 3200501 := bbase (se 5 (by rfl) ⟨150023, by rfl⟩ : syracuseStep 3200501 = 300047) (by norm_num)
theorem B2133667 : Blo 2133435 2133667 := bstep (se 1 (by rfl) ⟨1600250, by rfl⟩ : syracuseStep 2133667 = 3200501) B3200501
theorem B5126597 : Blo 2133435 5126597 := bbase (se 4 (by rfl) ⟨480618, by rfl⟩ : syracuseStep 5126597 = 961237) (by norm_num)
theorem B3417731 : Blo 2133435 3417731 := bstep (se 1 (by rfl) ⟨2563298, by rfl⟩ : syracuseStep 3417731 = 5126597) B5126597
theorem B2278487 : Blo 2133435 2278487 := bstep (se 1 (by rfl) ⟨1708865, by rfl⟩ : syracuseStep 2278487 = 3417731) B3417731
theorem B6075965 : Blo 2133435 6075965 := bstep (se 3 (by rfl) ⟨1139243, by rfl⟩ : syracuseStep 6075965 = 2278487) B2278487
theorem B4050643 : Blo 2133435 4050643 := bstep (se 1 (by rfl) ⟨3037982, by rfl⟩ : syracuseStep 4050643 = 6075965) B6075965
theorem B5400857 : Blo 2133435 5400857 := bstep (se 2 (by rfl) ⟨2025321, by rfl⟩ : syracuseStep 5400857 = 4050643) B4050643
theorem B3600571 : Blo 2133435 3600571 := bstep (se 1 (by rfl) ⟨2700428, by rfl⟩ : syracuseStep 3600571 = 5400857) B5400857
theorem B4800761 : Blo 2133435 4800761 := bstep (se 2 (by rfl) ⟨1800285, by rfl⟩ : syracuseStep 4800761 = 3600571) B3600571
theorem B3200507 : Blo 2133435 3200507 := bstep (se 1 (by rfl) ⟨2400380, by rfl⟩ : syracuseStep 3200507 = 4800761) B4800761
theorem B2133671 : Blo 2133435 2133671 := bstep (se 1 (by rfl) ⟨1600253, by rfl⟩ : syracuseStep 2133671 = 3200507) B3200507
theorem B2400385 : Blo 2133435 2400385 := bbase (se 2 (by rfl) ⟨900144, by rfl⟩ : syracuseStep 2400385 = 1800289) (by norm_num)
theorem B3200513 : Blo 2133435 3200513 := bstep (se 2 (by rfl) ⟨1200192, by rfl⟩ : syracuseStep 3200513 = 2400385) B2400385
theorem B2133675 : Blo 2133435 2133675 := bstep (se 1 (by rfl) ⟨1600256, by rfl⟩ : syracuseStep 2133675 = 3200513) B3200513
theorem B5400877 : Blo 2133435 5400877 := bbase (se 3 (by rfl) ⟨1012664, by rfl⟩ : syracuseStep 5400877 = 2025329) (by norm_num)
theorem B7201169 : Blo 2133435 7201169 := bstep (se 2 (by rfl) ⟨2700438, by rfl⟩ : syracuseStep 7201169 = 5400877) B5400877
theorem B4800779 : Blo 2133435 4800779 := bstep (se 1 (by rfl) ⟨3600584, by rfl⟩ : syracuseStep 4800779 = 7201169) B7201169
theorem B3200519 : Blo 2133435 3200519 := bstep (se 1 (by rfl) ⟨2400389, by rfl⟩ : syracuseStep 3200519 = 4800779) B4800779
theorem B2133679 : Blo 2133435 2133679 := bstep (se 1 (by rfl) ⟨1600259, by rfl⟩ : syracuseStep 2133679 = 3200519) B3200519
theorem B3200525 : Blo 2133435 3200525 := bbase (se 3 (by rfl) ⟨600098, by rfl⟩ : syracuseStep 3200525 = 1200197) (by norm_num)
theorem B2133683 : Blo 2133435 2133683 := bstep (se 1 (by rfl) ⟨1600262, by rfl⟩ : syracuseStep 2133683 = 3200525) B3200525
theorem B4800797 : Blo 2133435 4800797 := bbase (se 3 (by rfl) ⟨900149, by rfl⟩ : syracuseStep 4800797 = 1800299) (by norm_num)
theorem B3200531 : Blo 2133435 3200531 := bstep (se 1 (by rfl) ⟨2400398, by rfl⟩ : syracuseStep 3200531 = 4800797) B4800797
theorem B2133687 : Blo 2133435 2133687 := bstep (se 1 (by rfl) ⟨1600265, by rfl⟩ : syracuseStep 2133687 = 3200531) B3200531
theorem B3600605 : Blo 2133435 3600605 := bbase (se 3 (by rfl) ⟨675113, by rfl⟩ : syracuseStep 3600605 = 1350227) (by norm_num)
theorem B2400403 : Blo 2133435 2400403 := bstep (se 1 (by rfl) ⟨1800302, by rfl⟩ : syracuseStep 2400403 = 3600605) B3600605
theorem B3200537 : Blo 2133435 3200537 := bstep (se 2 (by rfl) ⟨1200201, by rfl⟩ : syracuseStep 3200537 = 2400403) B2400403
theorem B2133691 : Blo 2133435 2133691 := bstep (se 1 (by rfl) ⟨1600268, by rfl⟩ : syracuseStep 2133691 = 3200537) B3200537
theorem B5126653 : Blo 2133435 5126653 := bbase (se 3 (by rfl) ⟨961247, by rfl⟩ : syracuseStep 5126653 = 1922495) (by norm_num)
theorem B6835537 : Blo 2133435 6835537 := bstep (se 2 (by rfl) ⟨2563326, by rfl⟩ : syracuseStep 6835537 = 5126653) B5126653
theorem B9114049 : Blo 2133435 9114049 := bstep (se 2 (by rfl) ⟨3417768, by rfl⟩ : syracuseStep 9114049 = 6835537) B6835537
theorem B12152065 : Blo 2133435 12152065 := bstep (se 2 (by rfl) ⟨4557024, by rfl⟩ : syracuseStep 12152065 = 9114049) B9114049
theorem B16202753 : Blo 2133435 16202753 := bstep (se 2 (by rfl) ⟨6076032, by rfl⟩ : syracuseStep 16202753 = 12152065) B12152065
theorem B10801835 : Blo 2133435 10801835 := bstep (se 1 (by rfl) ⟨8101376, by rfl⟩ : syracuseStep 10801835 = 16202753) B16202753
theorem B7201223 : Blo 2133435 7201223 := bstep (se 1 (by rfl) ⟨5400917, by rfl⟩ : syracuseStep 7201223 = 10801835) B10801835
theorem B4800815 : Blo 2133435 4800815 := bstep (se 1 (by rfl) ⟨3600611, by rfl⟩ : syracuseStep 4800815 = 7201223) B7201223
theorem B3200543 : Blo 2133435 3200543 := bstep (se 1 (by rfl) ⟨2400407, by rfl⟩ : syracuseStep 3200543 = 4800815) B4800815
theorem B2133695 : Blo 2133435 2133695 := bstep (se 1 (by rfl) ⟨1600271, by rfl⟩ : syracuseStep 2133695 = 3200543) B3200543
theorem B3200549 : Blo 2133435 3200549 := bbase (se 4 (by rfl) ⟨300051, by rfl⟩ : syracuseStep 3200549 = 600103) (by norm_num)
theorem B2133699 : Blo 2133435 2133699 := bstep (se 1 (by rfl) ⟨1600274, by rfl⟩ : syracuseStep 2133699 = 3200549) B3200549
theorem B2700469 : Blo 2133435 2700469 := bbase (se 5 (by rfl) ⟨126584, by rfl⟩ : syracuseStep 2700469 = 253169) (by norm_num)
theorem B3600625 : Blo 2133435 3600625 := bstep (se 2 (by rfl) ⟨1350234, by rfl⟩ : syracuseStep 3600625 = 2700469) B2700469
theorem B4800833 : Blo 2133435 4800833 := bstep (se 2 (by rfl) ⟨1800312, by rfl⟩ : syracuseStep 4800833 = 3600625) B3600625
theorem B3200555 : Blo 2133435 3200555 := bstep (se 1 (by rfl) ⟨2400416, by rfl⟩ : syracuseStep 3200555 = 4800833) B4800833
theorem B2133703 : Blo 2133435 2133703 := bstep (se 1 (by rfl) ⟨1600277, by rfl⟩ : syracuseStep 2133703 = 3200555) B3200555
theorem B2400421 : Blo 2133435 2400421 := bbase (se 4 (by rfl) ⟨225039, by rfl⟩ : syracuseStep 2400421 = 450079) (by norm_num)
theorem B3200561 : Blo 2133435 3200561 := bstep (se 2 (by rfl) ⟨1200210, by rfl⟩ : syracuseStep 3200561 = 2400421) B2400421
theorem B2133707 : Blo 2133435 2133707 := bstep (se 1 (by rfl) ⟨1600280, by rfl⟩ : syracuseStep 2133707 = 3200561) B3200561
theorem B14599061 : Blo 2133435 14599061 := bbase (se 6 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 14599061 = 684331) (by norm_num)
theorem B9732707 : Blo 2133435 9732707 := bstep (se 1 (by rfl) ⟨7299530, by rfl⟩ : syracuseStep 9732707 = 14599061) B14599061
theorem B6488471 : Blo 2133435 6488471 := bstep (se 1 (by rfl) ⟨4866353, by rfl⟩ : syracuseStep 6488471 = 9732707) B9732707
theorem B4325647 : Blo 2133435 4325647 := bstep (se 1 (by rfl) ⟨3244235, by rfl⟩ : syracuseStep 4325647 = 6488471) B6488471
theorem B5767529 : Blo 2133435 5767529 := bstep (se 2 (by rfl) ⟨2162823, by rfl⟩ : syracuseStep 5767529 = 4325647) B4325647
theorem B15380077 : Blo 2133435 15380077 := bstep (se 3 (by rfl) ⟨2883764, by rfl⟩ : syracuseStep 15380077 = 5767529) B5767529
theorem B20506769 : Blo 2133435 20506769 := bstep (se 2 (by rfl) ⟨7690038, by rfl⟩ : syracuseStep 20506769 = 15380077) B15380077
theorem B13671179 : Blo 2133435 13671179 := bstep (se 1 (by rfl) ⟨10253384, by rfl⟩ : syracuseStep 13671179 = 20506769) B20506769
theorem B9114119 : Blo 2133435 9114119 := bstep (se 1 (by rfl) ⟨6835589, by rfl⟩ : syracuseStep 9114119 = 13671179) B13671179
theorem B6076079 : Blo 2133435 6076079 := bstep (se 1 (by rfl) ⟨4557059, by rfl⟩ : syracuseStep 6076079 = 9114119) B9114119
theorem B4050719 : Blo 2133435 4050719 := bstep (se 1 (by rfl) ⟨3038039, by rfl⟩ : syracuseStep 4050719 = 6076079) B6076079
theorem B2700479 : Blo 2133435 2700479 := bstep (se 1 (by rfl) ⟨2025359, by rfl⟩ : syracuseStep 2700479 = 4050719) B4050719
theorem B7201277 : Blo 2133435 7201277 := bstep (se 3 (by rfl) ⟨1350239, by rfl⟩ : syracuseStep 7201277 = 2700479) B2700479
theorem B4800851 : Blo 2133435 4800851 := bstep (se 1 (by rfl) ⟨3600638, by rfl⟩ : syracuseStep 4800851 = 7201277) B7201277
theorem B3200567 : Blo 2133435 3200567 := bstep (se 1 (by rfl) ⟨2400425, by rfl⟩ : syracuseStep 3200567 = 4800851) B4800851
theorem B2133711 : Blo 2133435 2133711 := bstep (se 1 (by rfl) ⟨1600283, by rfl⟩ : syracuseStep 2133711 = 3200567) B3200567
theorem B3200573 : Blo 2133435 3200573 := bbase (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) (by norm_num)
theorem B2133715 : Blo 2133435 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B4800869 : Blo 2133435 4800869 := bbase (se 4 (by rfl) ⟨450081, by rfl⟩ : syracuseStep 4800869 = 900163) (by norm_num)
theorem B3200579 : Blo 2133435 3200579 := bstep (se 1 (by rfl) ⟨2400434, by rfl⟩ : syracuseStep 3200579 = 4800869) B4800869
theorem B2133719 : Blo 2133435 2133719 := bstep (se 1 (by rfl) ⟨1600289, by rfl⟩ : syracuseStep 2133719 = 3200579) B3200579
theorem B5400989 : Blo 2133435 5400989 := bbase (se 3 (by rfl) ⟨1012685, by rfl⟩ : syracuseStep 5400989 = 2025371) (by norm_num)
theorem B3600659 : Blo 2133435 3600659 := bstep (se 1 (by rfl) ⟨2700494, by rfl⟩ : syracuseStep 3600659 = 5400989) B5400989
theorem B2400439 : Blo 2133435 2400439 := bstep (se 1 (by rfl) ⟨1800329, by rfl⟩ : syracuseStep 2400439 = 3600659) B3600659
theorem B3200585 : Blo 2133435 3200585 := bstep (se 2 (by rfl) ⟨1200219, by rfl⟩ : syracuseStep 3200585 = 2400439) B2400439
theorem B2133723 : Blo 2133435 2133723 := bstep (se 1 (by rfl) ⟨1600292, by rfl⟩ : syracuseStep 2133723 = 3200585) B3200585
theorem B4050749 : Blo 2133435 4050749 := bbase (se 3 (by rfl) ⟨759515, by rfl⟩ : syracuseStep 4050749 = 1519031) (by norm_num)
theorem B10801997 : Blo 2133435 10801997 := bstep (se 3 (by rfl) ⟨2025374, by rfl⟩ : syracuseStep 10801997 = 4050749) B4050749
theorem B7201331 : Blo 2133435 7201331 := bstep (se 1 (by rfl) ⟨5400998, by rfl⟩ : syracuseStep 7201331 = 10801997) B10801997
theorem B4800887 : Blo 2133435 4800887 := bstep (se 1 (by rfl) ⟨3600665, by rfl⟩ : syracuseStep 4800887 = 7201331) B7201331
theorem B3200591 : Blo 2133435 3200591 := bstep (se 1 (by rfl) ⟨2400443, by rfl⟩ : syracuseStep 3200591 = 4800887) B4800887
theorem B2133727 : Blo 2133435 2133727 := bstep (se 1 (by rfl) ⟨1600295, by rfl⟩ : syracuseStep 2133727 = 3200591) B3200591
theorem B3200597 : Blo 2133435 3200597 := bbase (se 8 (by rfl) ⟨18753, by rfl⟩ : syracuseStep 3200597 = 37507) (by norm_num)
theorem B2133731 : Blo 2133435 2133731 := bstep (se 1 (by rfl) ⟨1600298, by rfl⟩ : syracuseStep 2133731 = 3200597) B3200597
theorem B12318101 : Blo 2133435 12318101 := bbase (se 6 (by rfl) ⟨288705, by rfl⟩ : syracuseStep 12318101 = 577411) (by norm_num)
theorem B8212067 : Blo 2133435 8212067 := bstep (se 1 (by rfl) ⟨6159050, by rfl⟩ : syracuseStep 8212067 = 12318101) B12318101
theorem B5474711 : Blo 2133435 5474711 := bstep (se 1 (by rfl) ⟨4106033, by rfl⟩ : syracuseStep 5474711 = 8212067) B8212067
theorem B3649807 : Blo 2133435 3649807 := bstep (se 1 (by rfl) ⟨2737355, by rfl⟩ : syracuseStep 3649807 = 5474711) B5474711
theorem B4866409 : Blo 2133435 4866409 := bstep (se 2 (by rfl) ⟨1824903, by rfl⟩ : syracuseStep 4866409 = 3649807) B3649807
theorem B6488545 : Blo 2133435 6488545 := bstep (se 2 (by rfl) ⟨2433204, by rfl⟩ : syracuseStep 6488545 = 4866409) B4866409
theorem B8651393 : Blo 2133435 8651393 := bstep (se 2 (by rfl) ⟨3244272, by rfl⟩ : syracuseStep 8651393 = 6488545) B6488545
theorem B5767595 : Blo 2133435 5767595 := bstep (se 1 (by rfl) ⟨4325696, by rfl⟩ : syracuseStep 5767595 = 8651393) B8651393
theorem B3845063 : Blo 2133435 3845063 := bstep (se 1 (by rfl) ⟨2883797, by rfl⟩ : syracuseStep 3845063 = 5767595) B5767595
theorem B2563375 : Blo 2133435 2563375 := bstep (se 1 (by rfl) ⟨1922531, by rfl⟩ : syracuseStep 2563375 = 3845063) B3845063
theorem B3417833 : Blo 2133435 3417833 := bstep (se 2 (by rfl) ⟨1281687, by rfl⟩ : syracuseStep 3417833 = 2563375) B2563375
theorem B9114221 : Blo 2133435 9114221 := bstep (se 3 (by rfl) ⟨1708916, by rfl⟩ : syracuseStep 9114221 = 3417833) B3417833
theorem B6076147 : Blo 2133435 6076147 := bstep (se 1 (by rfl) ⟨4557110, by rfl⟩ : syracuseStep 6076147 = 9114221) B9114221
theorem B8101529 : Blo 2133435 8101529 := bstep (se 2 (by rfl) ⟨3038073, by rfl⟩ : syracuseStep 8101529 = 6076147) B6076147
theorem B5401019 : Blo 2133435 5401019 := bstep (se 1 (by rfl) ⟨4050764, by rfl⟩ : syracuseStep 5401019 = 8101529) B8101529
theorem B3600679 : Blo 2133435 3600679 := bstep (se 1 (by rfl) ⟨2700509, by rfl⟩ : syracuseStep 3600679 = 5401019) B5401019
theorem B4800905 : Blo 2133435 4800905 := bstep (se 2 (by rfl) ⟨1800339, by rfl⟩ : syracuseStep 4800905 = 3600679) B3600679
theorem B3200603 : Blo 2133435 3200603 := bstep (se 1 (by rfl) ⟨2400452, by rfl⟩ : syracuseStep 3200603 = 4800905) B4800905
theorem B2133735 : Blo 2133435 2133735 := bstep (se 1 (by rfl) ⟨1600301, by rfl⟩ : syracuseStep 2133735 = 3200603) B3200603
theorem B2400457 : Blo 2133435 2400457 := bbase (se 2 (by rfl) ⟨900171, by rfl⟩ : syracuseStep 2400457 = 1800343) (by norm_num)
theorem B3200609 : Blo 2133435 3200609 := bstep (se 2 (by rfl) ⟨1200228, by rfl⟩ : syracuseStep 3200609 = 2400457) B2400457
theorem B2133739 : Blo 2133435 2133739 := bstep (se 1 (by rfl) ⟨1600304, by rfl⟩ : syracuseStep 2133739 = 3200609) B3200609
theorem B3164141 : Blo 2133435 3164141 := bbase (se 3 (by rfl) ⟨593276, by rfl⟩ : syracuseStep 3164141 = 1186553) (by norm_num)
theorem B8437709 : Blo 2133435 8437709 := bstep (se 3 (by rfl) ⟨1582070, by rfl⟩ : syracuseStep 8437709 = 3164141) B3164141
theorem B5625139 : Blo 2133435 5625139 := bstep (se 1 (by rfl) ⟨4218854, by rfl⟩ : syracuseStep 5625139 = 8437709) B8437709
theorem B7500185 : Blo 2133435 7500185 := bstep (se 2 (by rfl) ⟨2812569, by rfl⟩ : syracuseStep 7500185 = 5625139) B5625139
theorem B5000123 : Blo 2133435 5000123 := bstep (se 1 (by rfl) ⟨3750092, by rfl⟩ : syracuseStep 5000123 = 7500185) B7500185
theorem B3333415 : Blo 2133435 3333415 := bstep (se 1 (by rfl) ⟨2500061, by rfl⟩ : syracuseStep 3333415 = 5000123) B5000123
theorem B4444553 : Blo 2133435 4444553 := bstep (se 2 (by rfl) ⟨1666707, by rfl⟩ : syracuseStep 4444553 = 3333415) B3333415
theorem B2963035 : Blo 2133435 2963035 := bstep (se 1 (by rfl) ⟨2222276, by rfl⟩ : syracuseStep 2963035 = 4444553) B4444553
theorem B3950713 : Blo 2133435 3950713 := bstep (se 2 (by rfl) ⟨1481517, by rfl⟩ : syracuseStep 3950713 = 2963035) B2963035
theorem B21070469 : Blo 2133435 21070469 := bstep (se 4 (by rfl) ⟨1975356, by rfl⟩ : syracuseStep 21070469 = 3950713) B3950713
theorem B14046979 : Blo 2133435 14046979 := bstep (se 1 (by rfl) ⟨10535234, by rfl⟩ : syracuseStep 14046979 = 21070469) B21070469
theorem B18729305 : Blo 2133435 18729305 := bstep (se 2 (by rfl) ⟨7023489, by rfl⟩ : syracuseStep 18729305 = 14046979) B14046979
theorem B12486203 : Blo 2133435 12486203 := bstep (se 1 (by rfl) ⟨9364652, by rfl⟩ : syracuseStep 12486203 = 18729305) B18729305
theorem B8324135 : Blo 2133435 8324135 := bstep (se 1 (by rfl) ⟨6243101, by rfl⟩ : syracuseStep 8324135 = 12486203) B12486203
theorem B5549423 : Blo 2133435 5549423 := bstep (se 1 (by rfl) ⟨4162067, by rfl⟩ : syracuseStep 5549423 = 8324135) B8324135
theorem B14798461 : Blo 2133435 14798461 := bstep (se 3 (by rfl) ⟨2774711, by rfl⟩ : syracuseStep 14798461 = 5549423) B5549423
theorem B19731281 : Blo 2133435 19731281 := bstep (se 2 (by rfl) ⟨7399230, by rfl⟩ : syracuseStep 19731281 = 14798461) B14798461
theorem B52616749 : Blo 2133435 52616749 := bstep (se 3 (by rfl) ⟨9865640, by rfl⟩ : syracuseStep 52616749 = 19731281) B19731281
theorem B70155665 : Blo 2133435 70155665 := bstep (se 2 (by rfl) ⟨26308374, by rfl⟩ : syracuseStep 70155665 = 52616749) B52616749
theorem B46770443 : Blo 2133435 46770443 := bstep (se 1 (by rfl) ⟨35077832, by rfl⟩ : syracuseStep 46770443 = 70155665) B70155665
theorem B31180295 : Blo 2133435 31180295 := bstep (se 1 (by rfl) ⟨23385221, by rfl⟩ : syracuseStep 31180295 = 46770443) B46770443
theorem B20786863 : Blo 2133435 20786863 := bstep (se 1 (by rfl) ⟨15590147, by rfl⟩ : syracuseStep 20786863 = 31180295) B31180295
theorem B27715817 : Blo 2133435 27715817 := bstep (se 2 (by rfl) ⟨10393431, by rfl⟩ : syracuseStep 27715817 = 20786863) B20786863
theorem B73908845 : Blo 2133435 73908845 := bstep (se 3 (by rfl) ⟨13857908, by rfl⟩ : syracuseStep 73908845 = 27715817) B27715817
theorem B49272563 : Blo 2133435 49272563 := bstep (se 1 (by rfl) ⟨36954422, by rfl⟩ : syracuseStep 49272563 = 73908845) B73908845
theorem B32848375 : Blo 2133435 32848375 := bstep (se 1 (by rfl) ⟨24636281, by rfl⟩ : syracuseStep 32848375 = 49272563) B49272563
theorem B43797833 : Blo 2133435 43797833 := bstep (se 2 (by rfl) ⟨16424187, by rfl⟩ : syracuseStep 43797833 = 32848375) B32848375
theorem B29198555 : Blo 2133435 29198555 := bstep (se 1 (by rfl) ⟨21898916, by rfl⟩ : syracuseStep 29198555 = 43797833) B43797833
theorem B19465703 : Blo 2133435 19465703 := bstep (se 1 (by rfl) ⟨14599277, by rfl⟩ : syracuseStep 19465703 = 29198555) B29198555
theorem B12977135 : Blo 2133435 12977135 := bstep (se 1 (by rfl) ⟨9732851, by rfl⟩ : syracuseStep 12977135 = 19465703) B19465703
theorem B8651423 : Blo 2133435 8651423 := bstep (se 1 (by rfl) ⟨6488567, by rfl⟩ : syracuseStep 8651423 = 12977135) B12977135
theorem B5767615 : Blo 2133435 5767615 := bstep (se 1 (by rfl) ⟨4325711, by rfl⟩ : syracuseStep 5767615 = 8651423) B8651423
theorem B7690153 : Blo 2133435 7690153 := bstep (se 2 (by rfl) ⟨2883807, by rfl⟩ : syracuseStep 7690153 = 5767615) B5767615
theorem B10253537 : Blo 2133435 10253537 := bstep (se 2 (by rfl) ⟨3845076, by rfl⟩ : syracuseStep 10253537 = 7690153) B7690153
theorem B6835691 : Blo 2133435 6835691 := bstep (se 1 (by rfl) ⟨5126768, by rfl⟩ : syracuseStep 6835691 = 10253537) B10253537
theorem B18228509 : Blo 2133435 18228509 := bstep (se 3 (by rfl) ⟨3417845, by rfl⟩ : syracuseStep 18228509 = 6835691) B6835691
theorem B12152339 : Blo 2133435 12152339 := bstep (se 1 (by rfl) ⟨9114254, by rfl⟩ : syracuseStep 12152339 = 18228509) B18228509
theorem B8101559 : Blo 2133435 8101559 := bstep (se 1 (by rfl) ⟨6076169, by rfl⟩ : syracuseStep 8101559 = 12152339) B12152339
theorem B5401039 : Blo 2133435 5401039 := bstep (se 1 (by rfl) ⟨4050779, by rfl⟩ : syracuseStep 5401039 = 8101559) B8101559
theorem B7201385 : Blo 2133435 7201385 := bstep (se 2 (by rfl) ⟨2700519, by rfl⟩ : syracuseStep 7201385 = 5401039) B5401039
theorem B4800923 : Blo 2133435 4800923 := bstep (se 1 (by rfl) ⟨3600692, by rfl⟩ : syracuseStep 4800923 = 7201385) B7201385
theorem B3200615 : Blo 2133435 3200615 := bstep (se 1 (by rfl) ⟨2400461, by rfl⟩ : syracuseStep 3200615 = 4800923) B4800923
theorem B2133743 : Blo 2133435 2133743 := bstep (se 1 (by rfl) ⟨1600307, by rfl⟩ : syracuseStep 2133743 = 3200615) B3200615
theorem B3200621 : Blo 2133435 3200621 := bbase (se 3 (by rfl) ⟨600116, by rfl⟩ : syracuseStep 3200621 = 1200233) (by norm_num)
theorem B2133747 : Blo 2133435 2133747 := bstep (se 1 (by rfl) ⟨1600310, by rfl⟩ : syracuseStep 2133747 = 3200621) B3200621
theorem B4800941 : Blo 2133435 4800941 := bbase (se 3 (by rfl) ⟨900176, by rfl⟩ : syracuseStep 4800941 = 1800353) (by norm_num)
theorem B3200627 : Blo 2133435 3200627 := bstep (se 1 (by rfl) ⟨2400470, by rfl⟩ : syracuseStep 3200627 = 4800941) B4800941
theorem B2133751 : Blo 2133435 2133751 := bstep (se 1 (by rfl) ⟨1600313, by rfl⟩ : syracuseStep 2133751 = 3200627) B3200627
theorem B2278577 : Blo 2133435 2278577 := bbase (se 2 (by rfl) ⟨854466, by rfl⟩ : syracuseStep 2278577 = 1708933) (by norm_num)
theorem B6076205 : Blo 2133435 6076205 := bstep (se 3 (by rfl) ⟨1139288, by rfl⟩ : syracuseStep 6076205 = 2278577) B2278577
theorem B4050803 : Blo 2133435 4050803 := bstep (se 1 (by rfl) ⟨3038102, by rfl⟩ : syracuseStep 4050803 = 6076205) B6076205
theorem B2700535 : Blo 2133435 2700535 := bstep (se 1 (by rfl) ⟨2025401, by rfl⟩ : syracuseStep 2700535 = 4050803) B4050803
theorem B3600713 : Blo 2133435 3600713 := bstep (se 2 (by rfl) ⟨1350267, by rfl⟩ : syracuseStep 3600713 = 2700535) B2700535
theorem B2400475 : Blo 2133435 2400475 := bstep (se 1 (by rfl) ⟨1800356, by rfl⟩ : syracuseStep 2400475 = 3600713) B3600713
theorem B3200633 : Blo 2133435 3200633 := bstep (se 2 (by rfl) ⟨1200237, by rfl⟩ : syracuseStep 3200633 = 2400475) B2400475
theorem B2133755 : Blo 2133435 2133755 := bstep (se 1 (by rfl) ⟨1600316, by rfl⟩ : syracuseStep 2133755 = 3200633) B3200633
theorem B16424309 : Blo 2133435 16424309 := bbase (se 5 (by rfl) ⟨769889, by rfl⟩ : syracuseStep 16424309 = 1539779) (by norm_num)
theorem B10949539 : Blo 2133435 10949539 := bstep (se 1 (by rfl) ⟨8212154, by rfl⟩ : syracuseStep 10949539 = 16424309) B16424309
theorem B14599385 : Blo 2133435 14599385 := bstep (se 2 (by rfl) ⟨5474769, by rfl⟩ : syracuseStep 14599385 = 10949539) B10949539
theorem B9732923 : Blo 2133435 9732923 := bstep (se 1 (by rfl) ⟨7299692, by rfl⟩ : syracuseStep 9732923 = 14599385) B14599385
theorem B6488615 : Blo 2133435 6488615 := bstep (se 1 (by rfl) ⟨4866461, by rfl⟩ : syracuseStep 6488615 = 9732923) B9732923
theorem B4325743 : Blo 2133435 4325743 := bstep (se 1 (by rfl) ⟨3244307, by rfl⟩ : syracuseStep 4325743 = 6488615) B6488615
theorem B23070629 : Blo 2133435 23070629 := bstep (se 4 (by rfl) ⟨2162871, by rfl⟩ : syracuseStep 23070629 = 4325743) B4325743
theorem B61521677 : Blo 2133435 61521677 := bstep (se 3 (by rfl) ⟨11535314, by rfl⟩ : syracuseStep 61521677 = 23070629) B23070629
theorem B41014451 : Blo 2133435 41014451 := bstep (se 1 (by rfl) ⟨30760838, by rfl⟩ : syracuseStep 41014451 = 61521677) B61521677
theorem B27342967 : Blo 2133435 27342967 := bstep (se 1 (by rfl) ⟨20507225, by rfl⟩ : syracuseStep 27342967 = 41014451) B41014451
theorem B36457289 : Blo 2133435 36457289 := bstep (se 2 (by rfl) ⟨13671483, by rfl⟩ : syracuseStep 36457289 = 27342967) B27342967
theorem B24304859 : Blo 2133435 24304859 := bstep (se 1 (by rfl) ⟨18228644, by rfl⟩ : syracuseStep 24304859 = 36457289) B36457289
theorem B16203239 : Blo 2133435 16203239 := bstep (se 1 (by rfl) ⟨12152429, by rfl⟩ : syracuseStep 16203239 = 24304859) B24304859
theorem B10802159 : Blo 2133435 10802159 := bstep (se 1 (by rfl) ⟨8101619, by rfl⟩ : syracuseStep 10802159 = 16203239) B16203239
theorem B7201439 : Blo 2133435 7201439 := bstep (se 1 (by rfl) ⟨5401079, by rfl⟩ : syracuseStep 7201439 = 10802159) B10802159
theorem B4800959 : Blo 2133435 4800959 := bstep (se 1 (by rfl) ⟨3600719, by rfl⟩ : syracuseStep 4800959 = 7201439) B7201439
theorem B3200639 : Blo 2133435 3200639 := bstep (se 1 (by rfl) ⟨2400479, by rfl⟩ : syracuseStep 3200639 = 4800959) B4800959
theorem B2133759 : Blo 2133435 2133759 := bstep (se 1 (by rfl) ⟨1600319, by rfl⟩ : syracuseStep 2133759 = 3200639) B3200639
theorem B3200645 : Blo 2133435 3200645 := bbase (se 4 (by rfl) ⟨300060, by rfl⟩ : syracuseStep 3200645 = 600121) (by norm_num)
theorem B2133763 : Blo 2133435 2133763 := bstep (se 1 (by rfl) ⟨1600322, by rfl⟩ : syracuseStep 2133763 = 3200645) B3200645
theorem B3600733 : Blo 2133435 3600733 := bbase (se 3 (by rfl) ⟨675137, by rfl⟩ : syracuseStep 3600733 = 1350275) (by norm_num)
theorem B4800977 : Blo 2133435 4800977 := bstep (se 2 (by rfl) ⟨1800366, by rfl⟩ : syracuseStep 4800977 = 3600733) B3600733
theorem B3200651 : Blo 2133435 3200651 := bstep (se 1 (by rfl) ⟨2400488, by rfl⟩ : syracuseStep 3200651 = 4800977) B4800977
theorem B2133767 : Blo 2133435 2133767 := bstep (se 1 (by rfl) ⟨1600325, by rfl⟩ : syracuseStep 2133767 = 3200651) B3200651
theorem B2400493 : Blo 2133435 2400493 := bbase (se 3 (by rfl) ⟨450092, by rfl⟩ : syracuseStep 2400493 = 900185) (by norm_num)
theorem B3200657 : Blo 2133435 3200657 := bstep (se 2 (by rfl) ⟨1200246, by rfl⟩ : syracuseStep 3200657 = 2400493) B2400493
theorem B2133771 : Blo 2133435 2133771 := bstep (se 1 (by rfl) ⟨1600328, by rfl⟩ : syracuseStep 2133771 = 3200657) B3200657
theorem B7201493 : Blo 2133435 7201493 := bbase (se 7 (by rfl) ⟨84392, by rfl⟩ : syracuseStep 7201493 = 168785) (by norm_num)
theorem B4800995 : Blo 2133435 4800995 := bstep (se 1 (by rfl) ⟨3600746, by rfl⟩ : syracuseStep 4800995 = 7201493) B7201493
theorem B3200663 : Blo 2133435 3200663 := bstep (se 1 (by rfl) ⟨2400497, by rfl⟩ : syracuseStep 3200663 = 4800995) B4800995
theorem B2133775 : Blo 2133435 2133775 := bstep (se 1 (by rfl) ⟨1600331, by rfl⟩ : syracuseStep 2133775 = 3200663) B3200663
theorem B3200669 : Blo 2133435 3200669 := bbase (se 3 (by rfl) ⟨600125, by rfl⟩ : syracuseStep 3200669 = 1200251) (by norm_num)
theorem B2133779 : Blo 2133435 2133779 := bstep (se 1 (by rfl) ⟨1600334, by rfl⟩ : syracuseStep 2133779 = 3200669) B3200669
theorem B4801013 : Blo 2133435 4801013 := bbase (se 5 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 4801013 = 450095) (by norm_num)
theorem B3200675 : Blo 2133435 3200675 := bstep (se 1 (by rfl) ⟨2400506, by rfl⟩ : syracuseStep 3200675 = 4801013) B4801013
theorem B2133783 : Blo 2133435 2133783 := bstep (se 1 (by rfl) ⟨1600337, by rfl⟩ : syracuseStep 2133783 = 3200675) B3200675
theorem B41014997 : Blo 2133435 41014997 := bbase (se 7 (by rfl) ⟨480644, by rfl⟩ : syracuseStep 41014997 = 961289) (by norm_num)
theorem B27343331 : Blo 2133435 27343331 := bstep (se 1 (by rfl) ⟨20507498, by rfl⟩ : syracuseStep 27343331 = 41014997) B41014997
theorem B18228887 : Blo 2133435 18228887 := bstep (se 1 (by rfl) ⟨13671665, by rfl⟩ : syracuseStep 18228887 = 27343331) B27343331
theorem B12152591 : Blo 2133435 12152591 := bstep (se 1 (by rfl) ⟨9114443, by rfl⟩ : syracuseStep 12152591 = 18228887) B18228887
theorem B8101727 : Blo 2133435 8101727 := bstep (se 1 (by rfl) ⟨6076295, by rfl⟩ : syracuseStep 8101727 = 12152591) B12152591
theorem B5401151 : Blo 2133435 5401151 := bstep (se 1 (by rfl) ⟨4050863, by rfl⟩ : syracuseStep 5401151 = 8101727) B8101727
theorem B3600767 : Blo 2133435 3600767 := bstep (se 1 (by rfl) ⟨2700575, by rfl⟩ : syracuseStep 3600767 = 5401151) B5401151
theorem B2400511 : Blo 2133435 2400511 := bstep (se 1 (by rfl) ⟨1800383, by rfl⟩ : syracuseStep 2400511 = 3600767) B3600767
theorem B3200681 : Blo 2133435 3200681 := bstep (se 2 (by rfl) ⟨1200255, by rfl⟩ : syracuseStep 3200681 = 2400511) B2400511
theorem B2133787 : Blo 2133435 2133787 := bstep (se 1 (by rfl) ⟨1600340, by rfl⟩ : syracuseStep 2133787 = 3200681) B3200681
theorem B5126885 : Blo 2133435 5126885 := bbase (se 4 (by rfl) ⟨480645, by rfl⟩ : syracuseStep 5126885 = 961291) (by norm_num)
theorem B3417923 : Blo 2133435 3417923 := bstep (se 1 (by rfl) ⟨2563442, by rfl⟩ : syracuseStep 3417923 = 5126885) B5126885
theorem B2278615 : Blo 2133435 2278615 := bstep (se 1 (by rfl) ⟨1708961, by rfl⟩ : syracuseStep 2278615 = 3417923) B3417923
theorem B3038153 : Blo 2133435 3038153 := bstep (se 2 (by rfl) ⟨1139307, by rfl⟩ : syracuseStep 3038153 = 2278615) B2278615
theorem B8101741 : Blo 2133435 8101741 := bstep (se 3 (by rfl) ⟨1519076, by rfl⟩ : syracuseStep 8101741 = 3038153) B3038153
theorem B10802321 : Blo 2133435 10802321 := bstep (se 2 (by rfl) ⟨4050870, by rfl⟩ : syracuseStep 10802321 = 8101741) B8101741
theorem B7201547 : Blo 2133435 7201547 := bstep (se 1 (by rfl) ⟨5401160, by rfl⟩ : syracuseStep 7201547 = 10802321) B10802321
theorem B4801031 : Blo 2133435 4801031 := bstep (se 1 (by rfl) ⟨3600773, by rfl⟩ : syracuseStep 4801031 = 7201547) B7201547
theorem B3200687 : Blo 2133435 3200687 := bstep (se 1 (by rfl) ⟨2400515, by rfl⟩ : syracuseStep 3200687 = 4801031) B4801031
theorem B2133791 : Blo 2133435 2133791 := bstep (se 1 (by rfl) ⟨1600343, by rfl⟩ : syracuseStep 2133791 = 3200687) B3200687
theorem B3200693 : Blo 2133435 3200693 := bbase (se 5 (by rfl) ⟨150032, by rfl⟩ : syracuseStep 3200693 = 300065) (by norm_num)
theorem B2133795 : Blo 2133435 2133795 := bstep (se 1 (by rfl) ⟨1600346, by rfl⟩ : syracuseStep 2133795 = 3200693) B3200693
theorem B5401181 : Blo 2133435 5401181 := bbase (se 3 (by rfl) ⟨1012721, by rfl⟩ : syracuseStep 5401181 = 2025443) (by norm_num)
theorem B3600787 : Blo 2133435 3600787 := bstep (se 1 (by rfl) ⟨2700590, by rfl⟩ : syracuseStep 3600787 = 5401181) B5401181
theorem B4801049 : Blo 2133435 4801049 := bstep (se 2 (by rfl) ⟨1800393, by rfl⟩ : syracuseStep 4801049 = 3600787) B3600787
theorem B3200699 : Blo 2133435 3200699 := bstep (se 1 (by rfl) ⟨2400524, by rfl⟩ : syracuseStep 3200699 = 4801049) B4801049
theorem B2133799 : Blo 2133435 2133799 := bstep (se 1 (by rfl) ⟨1600349, by rfl⟩ : syracuseStep 2133799 = 3200699) B3200699
theorem B2400529 : Blo 2133435 2400529 := bbase (se 2 (by rfl) ⟨900198, by rfl⟩ : syracuseStep 2400529 = 1800397) (by norm_num)
theorem B3200705 : Blo 2133435 3200705 := bstep (se 2 (by rfl) ⟨1200264, by rfl⟩ : syracuseStep 3200705 = 2400529) B2400529
theorem B2133803 : Blo 2133435 2133803 := bstep (se 1 (by rfl) ⟨1600352, by rfl⟩ : syracuseStep 2133803 = 3200705) B3200705
theorem B4050901 : Blo 2133435 4050901 := bbase (se 7 (by rfl) ⟨47471, by rfl⟩ : syracuseStep 4050901 = 94943) (by norm_num)
theorem B5401201 : Blo 2133435 5401201 := bstep (se 2 (by rfl) ⟨2025450, by rfl⟩ : syracuseStep 5401201 = 4050901) B4050901
theorem B7201601 : Blo 2133435 7201601 := bstep (se 2 (by rfl) ⟨2700600, by rfl⟩ : syracuseStep 7201601 = 5401201) B5401201
theorem B4801067 : Blo 2133435 4801067 := bstep (se 1 (by rfl) ⟨3600800, by rfl⟩ : syracuseStep 4801067 = 7201601) B7201601
theorem B3200711 : Blo 2133435 3200711 := bstep (se 1 (by rfl) ⟨2400533, by rfl⟩ : syracuseStep 3200711 = 4801067) B4801067
theorem B2133807 : Blo 2133435 2133807 := bstep (se 1 (by rfl) ⟨1600355, by rfl⟩ : syracuseStep 2133807 = 3200711) B3200711
theorem B3200717 : Blo 2133435 3200717 := bbase (se 3 (by rfl) ⟨600134, by rfl⟩ : syracuseStep 3200717 = 1200269) (by norm_num)
theorem B2133811 : Blo 2133435 2133811 := bstep (se 1 (by rfl) ⟨1600358, by rfl⟩ : syracuseStep 2133811 = 3200717) B3200717
theorem B4801085 : Blo 2133435 4801085 := bbase (se 3 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 4801085 = 1800407) (by norm_num)
theorem B3200723 : Blo 2133435 3200723 := bstep (se 1 (by rfl) ⟨2400542, by rfl⟩ : syracuseStep 3200723 = 4801085) B4801085
theorem B2133815 : Blo 2133435 2133815 := bstep (se 1 (by rfl) ⟨1600361, by rfl⟩ : syracuseStep 2133815 = 3200723) B3200723
theorem B3600821 : Blo 2133435 3600821 := bbase (se 5 (by rfl) ⟨168788, by rfl⟩ : syracuseStep 3600821 = 337577) (by norm_num)
theorem B2400547 : Blo 2133435 2400547 := bstep (se 1 (by rfl) ⟨1800410, by rfl⟩ : syracuseStep 2400547 = 3600821) B3600821
theorem B3200729 : Blo 2133435 3200729 := bstep (se 2 (by rfl) ⟨1200273, by rfl⟩ : syracuseStep 3200729 = 2400547) B2400547
theorem B2133819 : Blo 2133435 2133819 := bstep (se 1 (by rfl) ⟨1600364, by rfl⟩ : syracuseStep 2133819 = 3200729) B3200729
theorem B2278649 : Blo 2133435 2278649 := bbase (se 2 (by rfl) ⟨854493, by rfl⟩ : syracuseStep 2278649 = 1708987) (by norm_num)
theorem B6076397 : Blo 2133435 6076397 := bstep (se 3 (by rfl) ⟨1139324, by rfl⟩ : syracuseStep 6076397 = 2278649) B2278649
theorem B16203725 : Blo 2133435 16203725 := bstep (se 3 (by rfl) ⟨3038198, by rfl⟩ : syracuseStep 16203725 = 6076397) B6076397
theorem B10802483 : Blo 2133435 10802483 := bstep (se 1 (by rfl) ⟨8101862, by rfl⟩ : syracuseStep 10802483 = 16203725) B16203725
theorem B7201655 : Blo 2133435 7201655 := bstep (se 1 (by rfl) ⟨5401241, by rfl⟩ : syracuseStep 7201655 = 10802483) B10802483
theorem B4801103 : Blo 2133435 4801103 := bstep (se 1 (by rfl) ⟨3600827, by rfl⟩ : syracuseStep 4801103 = 7201655) B7201655
theorem B3200735 : Blo 2133435 3200735 := bstep (se 1 (by rfl) ⟨2400551, by rfl⟩ : syracuseStep 3200735 = 4801103) B4801103
theorem B2133823 : Blo 2133435 2133823 := bstep (se 1 (by rfl) ⟨1600367, by rfl⟩ : syracuseStep 2133823 = 3200735) B3200735
theorem B3200741 : Blo 2133435 3200741 := bbase (se 4 (by rfl) ⟨300069, by rfl⟩ : syracuseStep 3200741 = 600139) (by norm_num)
theorem B2133827 : Blo 2133435 2133827 := bstep (se 1 (by rfl) ⟨1600370, by rfl⟩ : syracuseStep 2133827 = 3200741) B3200741
theorem B6076421 : Blo 2133435 6076421 := bbase (se 4 (by rfl) ⟨569664, by rfl⟩ : syracuseStep 6076421 = 1139329) (by norm_num)
theorem B4050947 : Blo 2133435 4050947 := bstep (se 1 (by rfl) ⟨3038210, by rfl⟩ : syracuseStep 4050947 = 6076421) B6076421
theorem B2700631 : Blo 2133435 2700631 := bstep (se 1 (by rfl) ⟨2025473, by rfl⟩ : syracuseStep 2700631 = 4050947) B4050947
theorem B3600841 : Blo 2133435 3600841 := bstep (se 2 (by rfl) ⟨1350315, by rfl⟩ : syracuseStep 3600841 = 2700631) B2700631
theorem B4801121 : Blo 2133435 4801121 := bstep (se 2 (by rfl) ⟨1800420, by rfl⟩ : syracuseStep 4801121 = 3600841) B3600841
theorem B3200747 : Blo 2133435 3200747 := bstep (se 1 (by rfl) ⟨2400560, by rfl⟩ : syracuseStep 3200747 = 4801121) B4801121
theorem B2133831 : Blo 2133435 2133831 := bstep (se 1 (by rfl) ⟨1600373, by rfl⟩ : syracuseStep 2133831 = 3200747) B3200747
theorem B2400565 : Blo 2133435 2400565 := bbase (se 5 (by rfl) ⟨112526, by rfl⟩ : syracuseStep 2400565 = 225053) (by norm_num)
theorem B3200753 : Blo 2133435 3200753 := bstep (se 2 (by rfl) ⟨1200282, by rfl⟩ : syracuseStep 3200753 = 2400565) B2400565
theorem B2133835 : Blo 2133435 2133835 := bstep (se 1 (by rfl) ⟨1600376, by rfl⟩ : syracuseStep 2133835 = 3200753) B3200753
theorem B2700641 : Blo 2133435 2700641 := bbase (se 2 (by rfl) ⟨1012740, by rfl⟩ : syracuseStep 2700641 = 2025481) (by norm_num)
theorem B7201709 : Blo 2133435 7201709 := bstep (se 3 (by rfl) ⟨1350320, by rfl⟩ : syracuseStep 7201709 = 2700641) B2700641
theorem B4801139 : Blo 2133435 4801139 := bstep (se 1 (by rfl) ⟨3600854, by rfl⟩ : syracuseStep 4801139 = 7201709) B7201709
theorem B3200759 : Blo 2133435 3200759 := bstep (se 1 (by rfl) ⟨2400569, by rfl⟩ : syracuseStep 3200759 = 4801139) B4801139
theorem B2133839 : Blo 2133435 2133839 := bstep (se 1 (by rfl) ⟨1600379, by rfl⟩ : syracuseStep 2133839 = 3200759) B3200759
theorem B3200765 : Blo 2133435 3200765 := bbase (se 3 (by rfl) ⟨600143, by rfl⟩ : syracuseStep 3200765 = 1200287) (by norm_num)
theorem B2133843 : Blo 2133435 2133843 := bstep (se 1 (by rfl) ⟨1600382, by rfl⟩ : syracuseStep 2133843 = 3200765) B3200765
theorem B4801157 : Blo 2133435 4801157 := bbase (se 4 (by rfl) ⟨450108, by rfl⟩ : syracuseStep 4801157 = 900217) (by norm_num)
theorem B3200771 : Blo 2133435 3200771 := bstep (se 1 (by rfl) ⟨2400578, by rfl⟩ : syracuseStep 3200771 = 4801157) B4801157
theorem B2133847 : Blo 2133435 2133847 := bstep (se 1 (by rfl) ⟨1600385, by rfl⟩ : syracuseStep 2133847 = 3200771) B3200771
theorem B3650005 : Blo 2133435 3650005 := bbase (se 7 (by rfl) ⟨42773, by rfl⟩ : syracuseStep 3650005 = 85547) (by norm_num)
theorem B19466693 : Blo 2133435 19466693 := bstep (se 4 (by rfl) ⟨1825002, by rfl⟩ : syracuseStep 19466693 = 3650005) B3650005
theorem B12977795 : Blo 2133435 12977795 := bstep (se 1 (by rfl) ⟨9733346, by rfl⟩ : syracuseStep 12977795 = 19466693) B19466693
theorem B8651863 : Blo 2133435 8651863 := bstep (se 1 (by rfl) ⟨6488897, by rfl⟩ : syracuseStep 8651863 = 12977795) B12977795
theorem B11535817 : Blo 2133435 11535817 := bstep (se 2 (by rfl) ⟨4325931, by rfl⟩ : syracuseStep 11535817 = 8651863) B8651863
theorem B15381089 : Blo 2133435 15381089 := bstep (se 2 (by rfl) ⟨5767908, by rfl⟩ : syracuseStep 15381089 = 11535817) B11535817
theorem B10254059 : Blo 2133435 10254059 := bstep (se 1 (by rfl) ⟨7690544, by rfl⟩ : syracuseStep 10254059 = 15381089) B15381089
theorem B6836039 : Blo 2133435 6836039 := bstep (se 1 (by rfl) ⟨5127029, by rfl⟩ : syracuseStep 6836039 = 10254059) B10254059
theorem B4557359 : Blo 2133435 4557359 := bstep (se 1 (by rfl) ⟨3418019, by rfl⟩ : syracuseStep 4557359 = 6836039) B6836039
theorem B3038239 : Blo 2133435 3038239 := bstep (se 1 (by rfl) ⟨2278679, by rfl⟩ : syracuseStep 3038239 = 4557359) B4557359
theorem B4050985 : Blo 2133435 4050985 := bstep (se 2 (by rfl) ⟨1519119, by rfl⟩ : syracuseStep 4050985 = 3038239) B3038239
theorem B5401313 : Blo 2133435 5401313 := bstep (se 2 (by rfl) ⟨2025492, by rfl⟩ : syracuseStep 5401313 = 4050985) B4050985
theorem B3600875 : Blo 2133435 3600875 := bstep (se 1 (by rfl) ⟨2700656, by rfl⟩ : syracuseStep 3600875 = 5401313) B5401313
theorem B2400583 : Blo 2133435 2400583 := bstep (se 1 (by rfl) ⟨1800437, by rfl⟩ : syracuseStep 2400583 = 3600875) B3600875
theorem B3200777 : Blo 2133435 3200777 := bstep (se 2 (by rfl) ⟨1200291, by rfl⟩ : syracuseStep 3200777 = 2400583) B2400583
theorem B2133851 : Blo 2133435 2133851 := bstep (se 1 (by rfl) ⟨1600388, by rfl⟩ : syracuseStep 2133851 = 3200777) B3200777
theorem B10802645 : Blo 2133435 10802645 := bbase (se 7 (by rfl) ⟨126593, by rfl⟩ : syracuseStep 10802645 = 253187) (by norm_num)
theorem B7201763 : Blo 2133435 7201763 := bstep (se 1 (by rfl) ⟨5401322, by rfl⟩ : syracuseStep 7201763 = 10802645) B10802645
theorem B4801175 : Blo 2133435 4801175 := bstep (se 1 (by rfl) ⟨3600881, by rfl⟩ : syracuseStep 4801175 = 7201763) B7201763
theorem B3200783 : Blo 2133435 3200783 := bstep (se 1 (by rfl) ⟨2400587, by rfl⟩ : syracuseStep 3200783 = 4801175) B4801175
theorem B2133855 : Blo 2133435 2133855 := bstep (se 1 (by rfl) ⟨1600391, by rfl⟩ : syracuseStep 2133855 = 3200783) B3200783
theorem B3200789 : Blo 2133435 3200789 := bbase (se 6 (by rfl) ⟨75018, by rfl⟩ : syracuseStep 3200789 = 150037) (by norm_num)
theorem B2133859 : Blo 2133435 2133859 := bstep (se 1 (by rfl) ⟨1600394, by rfl⟩ : syracuseStep 2133859 = 3200789) B3200789
theorem B16425109 : Blo 2133435 16425109 := bbase (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) (by norm_num)
theorem B21900145 : Blo 2133435 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B29200193 : Blo 2133435 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B19466795 : Blo 2133435 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B12977863 : Blo 2133435 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B69215269 : Blo 2133435 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B92287025 : Blo 2133435 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B61524683 : Blo 2133435 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B41016455 : Blo 2133435 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B27344303 : Blo 2133435 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B18229535 : Blo 2133435 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B12153023 : Blo 2133435 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B8102015 : Blo 2133435 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B5401343 : Blo 2133435 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B3600895 : Blo 2133435 3600895 := bstep (se 1 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 3600895 = 5401343) B5401343
theorem B4801193 : Blo 2133435 4801193 := bstep (se 2 (by rfl) ⟨1800447, by rfl⟩ : syracuseStep 4801193 = 3600895) B3600895
theorem B3200795 : Blo 2133435 3200795 := bstep (se 1 (by rfl) ⟨2400596, by rfl⟩ : syracuseStep 3200795 = 4801193) B4801193
theorem B2133863 : Blo 2133435 2133863 := bstep (se 1 (by rfl) ⟨1600397, by rfl⟩ : syracuseStep 2133863 = 3200795) B3200795
theorem B2400601 : Blo 2133435 2400601 := bbase (se 2 (by rfl) ⟨900225, by rfl⟩ : syracuseStep 2400601 = 1800451) (by norm_num)
theorem B3200801 : Blo 2133435 3200801 := bstep (se 2 (by rfl) ⟨1200300, by rfl⟩ : syracuseStep 3200801 = 2400601) B2400601
theorem B2133867 : Blo 2133435 2133867 := bstep (se 1 (by rfl) ⟨1600400, by rfl⟩ : syracuseStep 2133867 = 3200801) B3200801
theorem B5127077 : Blo 2133435 5127077 := bbase (se 4 (by rfl) ⟨480663, by rfl⟩ : syracuseStep 5127077 = 961327) (by norm_num)
theorem B3418051 : Blo 2133435 3418051 := bstep (se 1 (by rfl) ⟨2563538, by rfl⟩ : syracuseStep 3418051 = 5127077) B5127077
theorem B4557401 : Blo 2133435 4557401 := bstep (se 2 (by rfl) ⟨1709025, by rfl⟩ : syracuseStep 4557401 = 3418051) B3418051
theorem B3038267 : Blo 2133435 3038267 := bstep (se 1 (by rfl) ⟨2278700, by rfl⟩ : syracuseStep 3038267 = 4557401) B4557401
theorem B8102045 : Blo 2133435 8102045 := bstep (se 3 (by rfl) ⟨1519133, by rfl⟩ : syracuseStep 8102045 = 3038267) B3038267
theorem B5401363 : Blo 2133435 5401363 := bstep (se 1 (by rfl) ⟨4051022, by rfl⟩ : syracuseStep 5401363 = 8102045) B8102045
theorem B7201817 : Blo 2133435 7201817 := bstep (se 2 (by rfl) ⟨2700681, by rfl⟩ : syracuseStep 7201817 = 5401363) B5401363
theorem B4801211 : Blo 2133435 4801211 := bstep (se 1 (by rfl) ⟨3600908, by rfl⟩ : syracuseStep 4801211 = 7201817) B7201817
theorem B3200807 : Blo 2133435 3200807 := bstep (se 1 (by rfl) ⟨2400605, by rfl⟩ : syracuseStep 3200807 = 4801211) B4801211
theorem B2133871 : Blo 2133435 2133871 := bstep (se 1 (by rfl) ⟨1600403, by rfl⟩ : syracuseStep 2133871 = 3200807) B3200807
theorem B3200813 : Blo 2133435 3200813 := bbase (se 3 (by rfl) ⟨600152, by rfl⟩ : syracuseStep 3200813 = 1200305) (by norm_num)
theorem B2133875 : Blo 2133435 2133875 := bstep (se 1 (by rfl) ⟨1600406, by rfl⟩ : syracuseStep 2133875 = 3200813) B3200813
theorem B4801229 : Blo 2133435 4801229 := bbase (se 3 (by rfl) ⟨900230, by rfl⟩ : syracuseStep 4801229 = 1800461) (by norm_num)
theorem B3200819 : Blo 2133435 3200819 := bstep (se 1 (by rfl) ⟨2400614, by rfl⟩ : syracuseStep 3200819 = 4801229) B4801229
theorem B2133879 : Blo 2133435 2133879 := bstep (se 1 (by rfl) ⟨1600409, by rfl⟩ : syracuseStep 2133879 = 3200819) B3200819
theorem B2700697 : Blo 2133435 2700697 := bbase (se 2 (by rfl) ⟨1012761, by rfl⟩ : syracuseStep 2700697 = 2025523) (by norm_num)
theorem B3600929 : Blo 2133435 3600929 := bstep (se 2 (by rfl) ⟨1350348, by rfl⟩ : syracuseStep 3600929 = 2700697) B2700697
theorem B2400619 : Blo 2133435 2400619 := bstep (se 1 (by rfl) ⟨1800464, by rfl⟩ : syracuseStep 2400619 = 3600929) B3600929
theorem B3200825 : Blo 2133435 3200825 := bstep (se 2 (by rfl) ⟨1200309, by rfl⟩ : syracuseStep 3200825 = 2400619) B2400619
theorem B2133883 : Blo 2133435 2133883 := bstep (se 1 (by rfl) ⟨1600412, by rfl⟩ : syracuseStep 2133883 = 3200825) B3200825
theorem B9114869 : Blo 2133435 9114869 := bbase (se 5 (by rfl) ⟨427259, by rfl⟩ : syracuseStep 9114869 = 854519) (by norm_num)
theorem B24306317 : Blo 2133435 24306317 := bstep (se 3 (by rfl) ⟨4557434, by rfl⟩ : syracuseStep 24306317 = 9114869) B9114869
theorem B16204211 : Blo 2133435 16204211 := bstep (se 1 (by rfl) ⟨12153158, by rfl⟩ : syracuseStep 16204211 = 24306317) B24306317
theorem B10802807 : Blo 2133435 10802807 := bstep (se 1 (by rfl) ⟨8102105, by rfl⟩ : syracuseStep 10802807 = 16204211) B16204211
theorem B7201871 : Blo 2133435 7201871 := bstep (se 1 (by rfl) ⟨5401403, by rfl⟩ : syracuseStep 7201871 = 10802807) B10802807
theorem B4801247 : Blo 2133435 4801247 := bstep (se 1 (by rfl) ⟨3600935, by rfl⟩ : syracuseStep 4801247 = 7201871) B7201871
theorem B3200831 : Blo 2133435 3200831 := bstep (se 1 (by rfl) ⟨2400623, by rfl⟩ : syracuseStep 3200831 = 4801247) B4801247
theorem B2133887 : Blo 2133435 2133887 := bstep (se 1 (by rfl) ⟨1600415, by rfl⟩ : syracuseStep 2133887 = 3200831) B3200831
theorem B3200837 : Blo 2133435 3200837 := bbase (se 4 (by rfl) ⟨300078, by rfl⟩ : syracuseStep 3200837 = 600157) (by norm_num)
theorem B2133891 : Blo 2133435 2133891 := bstep (se 1 (by rfl) ⟨1600418, by rfl⟩ : syracuseStep 2133891 = 3200837) B3200837
theorem B3600949 : Blo 2133435 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B4801265 : Blo 2133435 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B3200843 : Blo 2133435 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B2133895 : Blo 2133435 2133895 := bstep (se 1 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 2133895 = 3200843) B3200843
theorem B2400637 : Blo 2133435 2400637 := bbase (se 3 (by rfl) ⟨450119, by rfl⟩ : syracuseStep 2400637 = 900239) (by norm_num)
theorem B3200849 : Blo 2133435 3200849 := bstep (se 2 (by rfl) ⟨1200318, by rfl⟩ : syracuseStep 3200849 = 2400637) B2400637
theorem B2133899 : Blo 2133435 2133899 := bstep (se 1 (by rfl) ⟨1600424, by rfl⟩ : syracuseStep 2133899 = 3200849) B3200849
theorem B7201925 : Blo 2133435 7201925 := bbase (se 4 (by rfl) ⟨675180, by rfl⟩ : syracuseStep 7201925 = 1350361) (by norm_num)
theorem B4801283 : Blo 2133435 4801283 := bstep (se 1 (by rfl) ⟨3600962, by rfl⟩ : syracuseStep 4801283 = 7201925) B7201925
theorem B3200855 : Blo 2133435 3200855 := bstep (se 1 (by rfl) ⟨2400641, by rfl⟩ : syracuseStep 3200855 = 4801283) B4801283
theorem B2133903 : Blo 2133435 2133903 := bstep (se 1 (by rfl) ⟨1600427, by rfl⟩ : syracuseStep 2133903 = 3200855) B3200855
theorem B3200861 : Blo 2133435 3200861 := bbase (se 3 (by rfl) ⟨600161, by rfl⟩ : syracuseStep 3200861 = 1200323) (by norm_num)
theorem B2133907 : Blo 2133435 2133907 := bstep (se 1 (by rfl) ⟨1600430, by rfl⟩ : syracuseStep 2133907 = 3200861) B3200861
theorem B4801301 : Blo 2133435 4801301 := bbase (se 6 (by rfl) ⟨112530, by rfl⟩ : syracuseStep 4801301 = 225061) (by norm_num)
theorem B3200867 : Blo 2133435 3200867 := bstep (se 1 (by rfl) ⟨2400650, by rfl⟩ : syracuseStep 3200867 = 4801301) B4801301
theorem B2133911 : Blo 2133435 2133911 := bstep (se 1 (by rfl) ⟨1600433, by rfl⟩ : syracuseStep 2133911 = 3200867) B3200867
theorem B8102213 : Blo 2133435 8102213 := bbase (se 4 (by rfl) ⟨759582, by rfl⟩ : syracuseStep 8102213 = 1519165) (by norm_num)
theorem B5401475 : Blo 2133435 5401475 := bstep (se 1 (by rfl) ⟨4051106, by rfl⟩ : syracuseStep 5401475 = 8102213) B8102213
theorem B3600983 : Blo 2133435 3600983 := bstep (se 1 (by rfl) ⟨2700737, by rfl⟩ : syracuseStep 3600983 = 5401475) B5401475
theorem B2400655 : Blo 2133435 2400655 := bstep (se 1 (by rfl) ⟨1800491, by rfl⟩ : syracuseStep 2400655 = 3600983) B3600983
theorem B3200873 : Blo 2133435 3200873 := bstep (se 2 (by rfl) ⟨1200327, by rfl⟩ : syracuseStep 3200873 = 2400655) B2400655
theorem B2133915 : Blo 2133435 2133915 := bstep (se 1 (by rfl) ⟨1600436, by rfl⟩ : syracuseStep 2133915 = 3200873) B3200873
theorem B3079789 : Blo 2133435 3079789 := bbase (se 3 (by rfl) ⟨577460, by rfl⟩ : syracuseStep 3079789 = 1154921) (by norm_num)
theorem B16425541 : Blo 2133435 16425541 := bstep (se 4 (by rfl) ⟨1539894, by rfl⟩ : syracuseStep 16425541 = 3079789) B3079789
theorem B21900721 : Blo 2133435 21900721 := bstep (se 2 (by rfl) ⟨8212770, by rfl⟩ : syracuseStep 21900721 = 16425541) B16425541
theorem B29200961 : Blo 2133435 29200961 := bstep (se 2 (by rfl) ⟨10950360, by rfl⟩ : syracuseStep 29200961 = 21900721) B21900721
theorem B19467307 : Blo 2133435 19467307 := bstep (se 1 (by rfl) ⟨14600480, by rfl⟩ : syracuseStep 19467307 = 29200961) B29200961
theorem B25956409 : Blo 2133435 25956409 := bstep (se 2 (by rfl) ⟨9733653, by rfl⟩ : syracuseStep 25956409 = 19467307) B19467307
theorem B34608545 : Blo 2133435 34608545 := bstep (se 2 (by rfl) ⟨12978204, by rfl⟩ : syracuseStep 34608545 = 25956409) B25956409
theorem B23072363 : Blo 2133435 23072363 := bstep (se 1 (by rfl) ⟨17304272, by rfl⟩ : syracuseStep 23072363 = 34608545) B34608545
theorem B15381575 : Blo 2133435 15381575 := bstep (se 1 (by rfl) ⟨11536181, by rfl⟩ : syracuseStep 15381575 = 23072363) B23072363
theorem B10254383 : Blo 2133435 10254383 := bstep (se 1 (by rfl) ⟨7690787, by rfl⟩ : syracuseStep 10254383 = 15381575) B15381575
theorem B6836255 : Blo 2133435 6836255 := bstep (se 1 (by rfl) ⟨5127191, by rfl⟩ : syracuseStep 6836255 = 10254383) B10254383
theorem B4557503 : Blo 2133435 4557503 := bstep (se 1 (by rfl) ⟨3418127, by rfl⟩ : syracuseStep 4557503 = 6836255) B6836255
theorem B12153341 : Blo 2133435 12153341 := bstep (se 3 (by rfl) ⟨2278751, by rfl⟩ : syracuseStep 12153341 = 4557503) B4557503
theorem B8102227 : Blo 2133435 8102227 := bstep (se 1 (by rfl) ⟨6076670, by rfl⟩ : syracuseStep 8102227 = 12153341) B12153341
theorem B10802969 : Blo 2133435 10802969 := bstep (se 2 (by rfl) ⟨4051113, by rfl⟩ : syracuseStep 10802969 = 8102227) B8102227
theorem B7201979 : Blo 2133435 7201979 := bstep (se 1 (by rfl) ⟨5401484, by rfl⟩ : syracuseStep 7201979 = 10802969) B10802969
theorem B4801319 : Blo 2133435 4801319 := bstep (se 1 (by rfl) ⟨3600989, by rfl⟩ : syracuseStep 4801319 = 7201979) B7201979
theorem B3200879 : Blo 2133435 3200879 := bstep (se 1 (by rfl) ⟨2400659, by rfl⟩ : syracuseStep 3200879 = 4801319) B4801319
theorem B2133919 : Blo 2133435 2133919 := bstep (se 1 (by rfl) ⟨1600439, by rfl⟩ : syracuseStep 2133919 = 3200879) B3200879
theorem B3200885 : Blo 2133435 3200885 := bbase (se 5 (by rfl) ⟨150041, by rfl⟩ : syracuseStep 3200885 = 300083) (by norm_num)
theorem B2133923 : Blo 2133435 2133923 := bstep (se 1 (by rfl) ⟨1600442, by rfl⟩ : syracuseStep 2133923 = 3200885) B3200885
theorem B3418141 : Blo 2133435 3418141 := bbase (se 3 (by rfl) ⟨640901, by rfl⟩ : syracuseStep 3418141 = 1281803) (by norm_num)
theorem B4557521 : Blo 2133435 4557521 := bstep (se 2 (by rfl) ⟨1709070, by rfl⟩ : syracuseStep 4557521 = 3418141) B3418141
theorem B3038347 : Blo 2133435 3038347 := bstep (se 1 (by rfl) ⟨2278760, by rfl⟩ : syracuseStep 3038347 = 4557521) B4557521
theorem B4051129 : Blo 2133435 4051129 := bstep (se 2 (by rfl) ⟨1519173, by rfl⟩ : syracuseStep 4051129 = 3038347) B3038347
theorem B5401505 : Blo 2133435 5401505 := bstep (se 2 (by rfl) ⟨2025564, by rfl⟩ : syracuseStep 5401505 = 4051129) B4051129
theorem B3601003 : Blo 2133435 3601003 := bstep (se 1 (by rfl) ⟨2700752, by rfl⟩ : syracuseStep 3601003 = 5401505) B5401505
theorem B4801337 : Blo 2133435 4801337 := bstep (se 2 (by rfl) ⟨1800501, by rfl⟩ : syracuseStep 4801337 = 3601003) B3601003
theorem B3200891 : Blo 2133435 3200891 := bstep (se 1 (by rfl) ⟨2400668, by rfl⟩ : syracuseStep 3200891 = 4801337) B4801337
theorem B2133927 : Blo 2133435 2133927 := bstep (se 1 (by rfl) ⟨1600445, by rfl⟩ : syracuseStep 2133927 = 3200891) B3200891
theorem B2400673 : Blo 2133435 2400673 := bbase (se 2 (by rfl) ⟨900252, by rfl⟩ : syracuseStep 2400673 = 1800505) (by norm_num)
theorem B3200897 : Blo 2133435 3200897 := bstep (se 2 (by rfl) ⟨1200336, by rfl⟩ : syracuseStep 3200897 = 2400673) B2400673
theorem B2133931 : Blo 2133435 2133931 := bstep (se 1 (by rfl) ⟨1600448, by rfl⟩ : syracuseStep 2133931 = 3200897) B3200897
theorem B5401525 : Blo 2133435 5401525 := bbase (se 5 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 5401525 = 506393) (by norm_num)
theorem B7202033 : Blo 2133435 7202033 := bstep (se 2 (by rfl) ⟨2700762, by rfl⟩ : syracuseStep 7202033 = 5401525) B5401525
theorem B4801355 : Blo 2133435 4801355 := bstep (se 1 (by rfl) ⟨3601016, by rfl⟩ : syracuseStep 4801355 = 7202033) B7202033
theorem B3200903 : Blo 2133435 3200903 := bstep (se 1 (by rfl) ⟨2400677, by rfl⟩ : syracuseStep 3200903 = 4801355) B4801355
theorem B2133935 : Blo 2133435 2133935 := bstep (se 1 (by rfl) ⟨1600451, by rfl⟩ : syracuseStep 2133935 = 3200903) B3200903
theorem B3200909 : Blo 2133435 3200909 := bbase (se 3 (by rfl) ⟨600170, by rfl⟩ : syracuseStep 3200909 = 1200341) (by norm_num)
theorem B2133939 : Blo 2133435 2133939 := bstep (se 1 (by rfl) ⟨1600454, by rfl⟩ : syracuseStep 2133939 = 3200909) B3200909
theorem B4801373 : Blo 2133435 4801373 := bbase (se 3 (by rfl) ⟨900257, by rfl⟩ : syracuseStep 4801373 = 1800515) (by norm_num)
theorem B3200915 : Blo 2133435 3200915 := bstep (se 1 (by rfl) ⟨2400686, by rfl⟩ : syracuseStep 3200915 = 4801373) B4801373
theorem B2133943 : Blo 2133435 2133943 := bstep (se 1 (by rfl) ⟨1600457, by rfl⟩ : syracuseStep 2133943 = 3200915) B3200915
theorem B3601037 : Blo 2133435 3601037 := bbase (se 3 (by rfl) ⟨675194, by rfl⟩ : syracuseStep 3601037 = 1350389) (by norm_num)
theorem B2400691 : Blo 2133435 2400691 := bstep (se 1 (by rfl) ⟨1800518, by rfl⟩ : syracuseStep 2400691 = 3601037) B3601037
theorem B3200921 : Blo 2133435 3200921 := bstep (se 2 (by rfl) ⟨1200345, by rfl⟩ : syracuseStep 3200921 = 2400691) B2400691
theorem B2133947 : Blo 2133435 2133947 := bstep (se 1 (by rfl) ⟨1600460, by rfl⟩ : syracuseStep 2133947 = 3200921) B3200921
theorem B6836357 : Blo 2133435 6836357 := bbase (se 4 (by rfl) ⟨640908, by rfl⟩ : syracuseStep 6836357 = 1281817) (by norm_num)
theorem B18230285 : Blo 2133435 18230285 := bstep (se 3 (by rfl) ⟨3418178, by rfl⟩ : syracuseStep 18230285 = 6836357) B6836357
theorem B12153523 : Blo 2133435 12153523 := bstep (se 1 (by rfl) ⟨9115142, by rfl⟩ : syracuseStep 12153523 = 18230285) B18230285
theorem B16204697 : Blo 2133435 16204697 := bstep (se 2 (by rfl) ⟨6076761, by rfl⟩ : syracuseStep 16204697 = 12153523) B12153523
theorem B10803131 : Blo 2133435 10803131 := bstep (se 1 (by rfl) ⟨8102348, by rfl⟩ : syracuseStep 10803131 = 16204697) B16204697
theorem B7202087 : Blo 2133435 7202087 := bstep (se 1 (by rfl) ⟨5401565, by rfl⟩ : syracuseStep 7202087 = 10803131) B10803131
theorem B4801391 : Blo 2133435 4801391 := bstep (se 1 (by rfl) ⟨3601043, by rfl⟩ : syracuseStep 4801391 = 7202087) B7202087
theorem B3200927 : Blo 2133435 3200927 := bstep (se 1 (by rfl) ⟨2400695, by rfl⟩ : syracuseStep 3200927 = 4801391) B4801391
theorem B2133951 : Blo 2133435 2133951 := bstep (se 1 (by rfl) ⟨1600463, by rfl⟩ : syracuseStep 2133951 = 3200927) B3200927
theorem B3200933 : Blo 2133435 3200933 := bbase (se 4 (by rfl) ⟨300087, by rfl⟩ : syracuseStep 3200933 = 600175) (by norm_num)
theorem B2133955 : Blo 2133435 2133955 := bstep (se 1 (by rfl) ⟨1600466, by rfl⟩ : syracuseStep 2133955 = 3200933) B3200933
theorem B2700793 : Blo 2133435 2700793 := bbase (se 2 (by rfl) ⟨1012797, by rfl⟩ : syracuseStep 2700793 = 2025595) (by norm_num)
theorem B3601057 : Blo 2133435 3601057 := bstep (se 2 (by rfl) ⟨1350396, by rfl⟩ : syracuseStep 3601057 = 2700793) B2700793
theorem B4801409 : Blo 2133435 4801409 := bstep (se 2 (by rfl) ⟨1800528, by rfl⟩ : syracuseStep 4801409 = 3601057) B3601057
theorem B3200939 : Blo 2133435 3200939 := bstep (se 1 (by rfl) ⟨2400704, by rfl⟩ : syracuseStep 3200939 = 4801409) B4801409
theorem B2133959 : Blo 2133435 2133959 := bstep (se 1 (by rfl) ⟨1600469, by rfl⟩ : syracuseStep 2133959 = 3200939) B3200939
theorem B2400709 : Blo 2133435 2400709 := bbase (se 4 (by rfl) ⟨225066, by rfl⟩ : syracuseStep 2400709 = 450133) (by norm_num)
theorem B3200945 : Blo 2133435 3200945 := bstep (se 2 (by rfl) ⟨1200354, by rfl⟩ : syracuseStep 3200945 = 2400709) B2400709
theorem B2133963 : Blo 2133435 2133963 := bstep (se 1 (by rfl) ⟨1600472, by rfl⟩ : syracuseStep 2133963 = 3200945) B3200945
theorem B4051205 : Blo 2133435 4051205 := bbase (se 4 (by rfl) ⟨379800, by rfl⟩ : syracuseStep 4051205 = 759601) (by norm_num)
theorem B2700803 : Blo 2133435 2700803 := bstep (se 1 (by rfl) ⟨2025602, by rfl⟩ : syracuseStep 2700803 = 4051205) B4051205
theorem B7202141 : Blo 2133435 7202141 := bstep (se 3 (by rfl) ⟨1350401, by rfl⟩ : syracuseStep 7202141 = 2700803) B2700803
theorem B4801427 : Blo 2133435 4801427 := bstep (se 1 (by rfl) ⟨3601070, by rfl⟩ : syracuseStep 4801427 = 7202141) B7202141
theorem B3200951 : Blo 2133435 3200951 := bstep (se 1 (by rfl) ⟨2400713, by rfl⟩ : syracuseStep 3200951 = 4801427) B4801427
theorem B2133967 : Blo 2133435 2133967 := bstep (se 1 (by rfl) ⟨1600475, by rfl⟩ : syracuseStep 2133967 = 3200951) B3200951
theorem B3200957 : Blo 2133435 3200957 := bbase (se 3 (by rfl) ⟨600179, by rfl⟩ : syracuseStep 3200957 = 1200359) (by norm_num)
theorem B2133971 : Blo 2133435 2133971 := bstep (se 1 (by rfl) ⟨1600478, by rfl⟩ : syracuseStep 2133971 = 3200957) B3200957
theorem B4801445 : Blo 2133435 4801445 := bbase (se 4 (by rfl) ⟨450135, by rfl⟩ : syracuseStep 4801445 = 900271) (by norm_num)
theorem B3200963 : Blo 2133435 3200963 := bstep (se 1 (by rfl) ⟨2400722, by rfl⟩ : syracuseStep 3200963 = 4801445) B4801445
theorem B2133975 : Blo 2133435 2133975 := bstep (se 1 (by rfl) ⟨1600481, by rfl⟩ : syracuseStep 2133975 = 3200963) B3200963
theorem B5401637 : Blo 2133435 5401637 := bbase (se 4 (by rfl) ⟨506403, by rfl⟩ : syracuseStep 5401637 = 1012807) (by norm_num)
theorem B3601091 : Blo 2133435 3601091 := bstep (se 1 (by rfl) ⟨2700818, by rfl⟩ : syracuseStep 3601091 = 5401637) B5401637
theorem B2400727 : Blo 2133435 2400727 := bstep (se 1 (by rfl) ⟨1800545, by rfl⟩ : syracuseStep 2400727 = 3601091) B3601091
theorem B3200969 : Blo 2133435 3200969 := bstep (se 2 (by rfl) ⟨1200363, by rfl⟩ : syracuseStep 3200969 = 2400727) B2400727
theorem B2133979 : Blo 2133435 2133979 := bstep (se 1 (by rfl) ⟨1600484, by rfl⟩ : syracuseStep 2133979 = 3200969) B3200969
theorem B6076853 : Blo 2133435 6076853 := bbase (se 5 (by rfl) ⟨284852, by rfl⟩ : syracuseStep 6076853 = 569705) (by norm_num)
theorem B4051235 : Blo 2133435 4051235 := bstep (se 1 (by rfl) ⟨3038426, by rfl⟩ : syracuseStep 4051235 = 6076853) B6076853
theorem B10803293 : Blo 2133435 10803293 := bstep (se 3 (by rfl) ⟨2025617, by rfl⟩ : syracuseStep 10803293 = 4051235) B4051235
theorem B7202195 : Blo 2133435 7202195 := bstep (se 1 (by rfl) ⟨5401646, by rfl⟩ : syracuseStep 7202195 = 10803293) B10803293
theorem B4801463 : Blo 2133435 4801463 := bstep (se 1 (by rfl) ⟨3601097, by rfl⟩ : syracuseStep 4801463 = 7202195) B7202195
theorem B3200975 : Blo 2133435 3200975 := bstep (se 1 (by rfl) ⟨2400731, by rfl⟩ : syracuseStep 3200975 = 4801463) B4801463
theorem B2133983 : Blo 2133435 2133983 := bstep (se 1 (by rfl) ⟨1600487, by rfl⟩ : syracuseStep 2133983 = 3200975) B3200975
theorem B3200981 : Blo 2133435 3200981 := bbase (se 7 (by rfl) ⟨37511, by rfl⟩ : syracuseStep 3200981 = 75023) (by norm_num)
theorem B2133987 : Blo 2133435 2133987 := bstep (se 1 (by rfl) ⟨1600490, by rfl⟩ : syracuseStep 2133987 = 3200981) B3200981
theorem B8102501 : Blo 2133435 8102501 := bbase (se 4 (by rfl) ⟨759609, by rfl⟩ : syracuseStep 8102501 = 1519219) (by norm_num)
theorem B5401667 : Blo 2133435 5401667 := bstep (se 1 (by rfl) ⟨4051250, by rfl⟩ : syracuseStep 5401667 = 8102501) B8102501
theorem B3601111 : Blo 2133435 3601111 := bstep (se 1 (by rfl) ⟨2700833, by rfl⟩ : syracuseStep 3601111 = 5401667) B5401667
theorem B4801481 : Blo 2133435 4801481 := bstep (se 2 (by rfl) ⟨1800555, by rfl⟩ : syracuseStep 4801481 = 3601111) B3601111
theorem B3200987 : Blo 2133435 3200987 := bstep (se 1 (by rfl) ⟨2400740, by rfl⟩ : syracuseStep 3200987 = 4801481) B4801481
theorem B2133991 : Blo 2133435 2133991 := bstep (se 1 (by rfl) ⟨1600493, by rfl⟩ : syracuseStep 2133991 = 3200987) B3200987
theorem B2400745 : Blo 2133435 2400745 := bbase (se 2 (by rfl) ⟨900279, by rfl⟩ : syracuseStep 2400745 = 1800559) (by norm_num)
theorem B3200993 : Blo 2133435 3200993 := bstep (se 2 (by rfl) ⟨1200372, by rfl⟩ : syracuseStep 3200993 = 2400745) B2400745
theorem B2133995 : Blo 2133435 2133995 := bstep (se 1 (by rfl) ⟨1600496, by rfl⟩ : syracuseStep 2133995 = 3200993) B3200993
theorem B2278837 : Blo 2133435 2278837 := bbase (se 5 (by rfl) ⟨106820, by rfl⟩ : syracuseStep 2278837 = 213641) (by norm_num)
theorem B12153797 : Blo 2133435 12153797 := bstep (se 4 (by rfl) ⟨1139418, by rfl⟩ : syracuseStep 12153797 = 2278837) B2278837
theorem B8102531 : Blo 2133435 8102531 := bstep (se 1 (by rfl) ⟨6076898, by rfl⟩ : syracuseStep 8102531 = 12153797) B12153797
theorem B5401687 : Blo 2133435 5401687 := bstep (se 1 (by rfl) ⟨4051265, by rfl⟩ : syracuseStep 5401687 = 8102531) B8102531
theorem B7202249 : Blo 2133435 7202249 := bstep (se 2 (by rfl) ⟨2700843, by rfl⟩ : syracuseStep 7202249 = 5401687) B5401687
theorem B4801499 : Blo 2133435 4801499 := bstep (se 1 (by rfl) ⟨3601124, by rfl⟩ : syracuseStep 4801499 = 7202249) B7202249
theorem B3200999 : Blo 2133435 3200999 := bstep (se 1 (by rfl) ⟨2400749, by rfl⟩ : syracuseStep 3200999 = 4801499) B4801499
theorem B2133999 : Blo 2133435 2133999 := bstep (se 1 (by rfl) ⟨1600499, by rfl⟩ : syracuseStep 2133999 = 3200999) B3200999
theorem B3201005 : Blo 2133435 3201005 := bbase (se 3 (by rfl) ⟨600188, by rfl⟩ : syracuseStep 3201005 = 1200377) (by norm_num)
theorem B2134003 : Blo 2133435 2134003 := bstep (se 1 (by rfl) ⟨1600502, by rfl⟩ : syracuseStep 2134003 = 3201005) B3201005
theorem B4801517 : Blo 2133435 4801517 := bbase (se 3 (by rfl) ⟨900284, by rfl⟩ : syracuseStep 4801517 = 1800569) (by norm_num)
theorem B3201011 : Blo 2133435 3201011 := bstep (se 1 (by rfl) ⟨2400758, by rfl⟩ : syracuseStep 3201011 = 4801517) B4801517
theorem B2134007 : Blo 2133435 2134007 := bstep (se 1 (by rfl) ⟨1600505, by rfl⟩ : syracuseStep 2134007 = 3201011) B3201011
theorem B4557701 : Blo 2133435 4557701 := bbase (se 4 (by rfl) ⟨427284, by rfl⟩ : syracuseStep 4557701 = 854569) (by norm_num)
theorem B3038467 : Blo 2133435 3038467 := bstep (se 1 (by rfl) ⟨2278850, by rfl⟩ : syracuseStep 3038467 = 4557701) B4557701
theorem B4051289 : Blo 2133435 4051289 := bstep (se 2 (by rfl) ⟨1519233, by rfl⟩ : syracuseStep 4051289 = 3038467) B3038467
theorem B2700859 : Blo 2133435 2700859 := bstep (se 1 (by rfl) ⟨2025644, by rfl⟩ : syracuseStep 2700859 = 4051289) B4051289
theorem B3601145 : Blo 2133435 3601145 := bstep (se 2 (by rfl) ⟨1350429, by rfl⟩ : syracuseStep 3601145 = 2700859) B2700859
theorem B2400763 : Blo 2133435 2400763 := bstep (se 1 (by rfl) ⟨1800572, by rfl⟩ : syracuseStep 2400763 = 3601145) B3601145
theorem B3201017 : Blo 2133435 3201017 := bstep (se 2 (by rfl) ⟨1200381, by rfl⟩ : syracuseStep 3201017 = 2400763) B2400763
theorem B2134011 : Blo 2133435 2134011 := bstep (se 1 (by rfl) ⟨1600508, by rfl⟩ : syracuseStep 2134011 = 3201017) B3201017
theorem B2598689 : Blo 2133435 2598689 := bbase (se 2 (by rfl) ⟨974508, by rfl⟩ : syracuseStep 2598689 = 1949017) (by norm_num)
theorem B6929837 : Blo 2133435 6929837 := bstep (se 3 (by rfl) ⟨1299344, by rfl⟩ : syracuseStep 6929837 = 2598689) B2598689
theorem B4619891 : Blo 2133435 4619891 := bstep (se 1 (by rfl) ⟨3464918, by rfl⟩ : syracuseStep 4619891 = 6929837) B6929837
theorem B3079927 : Blo 2133435 3079927 := bstep (se 1 (by rfl) ⟨2309945, by rfl⟩ : syracuseStep 3079927 = 4619891) B4619891
theorem B4106569 : Blo 2133435 4106569 := bstep (se 2 (by rfl) ⟨1539963, by rfl⟩ : syracuseStep 4106569 = 3079927) B3079927
theorem B87606805 : Blo 2133435 87606805 := bstep (se 6 (by rfl) ⟨2053284, by rfl⟩ : syracuseStep 87606805 = 4106569) B4106569
theorem B116809073 : Blo 2133435 116809073 := bstep (se 2 (by rfl) ⟨43803402, by rfl⟩ : syracuseStep 116809073 = 87606805) B87606805
theorem B77872715 : Blo 2133435 77872715 := bstep (se 1 (by rfl) ⟨58404536, by rfl⟩ : syracuseStep 77872715 = 116809073) B116809073
theorem B51915143 : Blo 2133435 51915143 := bstep (se 1 (by rfl) ⟨38936357, by rfl⟩ : syracuseStep 51915143 = 77872715) B77872715
theorem B34610095 : Blo 2133435 34610095 := bstep (se 1 (by rfl) ⟨25957571, by rfl⟩ : syracuseStep 34610095 = 51915143) B51915143
theorem B184587173 : Blo 2133435 184587173 := bstep (se 4 (by rfl) ⟨17305047, by rfl⟩ : syracuseStep 184587173 = 34610095) B34610095
theorem B123058115 : Blo 2133435 123058115 := bstep (se 1 (by rfl) ⟨92293586, by rfl⟩ : syracuseStep 123058115 = 184587173) B184587173
theorem B82038743 : Blo 2133435 82038743 := bstep (se 1 (by rfl) ⟨61529057, by rfl⟩ : syracuseStep 82038743 = 123058115) B123058115
theorem B54692495 : Blo 2133435 54692495 := bstep (se 1 (by rfl) ⟨41019371, by rfl⟩ : syracuseStep 54692495 = 82038743) B82038743
theorem B36461663 : Blo 2133435 36461663 := bstep (se 1 (by rfl) ⟨27346247, by rfl⟩ : syracuseStep 36461663 = 54692495) B54692495
theorem B24307775 : Blo 2133435 24307775 := bstep (se 1 (by rfl) ⟨18230831, by rfl⟩ : syracuseStep 24307775 = 36461663) B36461663
theorem B16205183 : Blo 2133435 16205183 := bstep (se 1 (by rfl) ⟨12153887, by rfl⟩ : syracuseStep 16205183 = 24307775) B24307775
theorem B10803455 : Blo 2133435 10803455 := bstep (se 1 (by rfl) ⟨8102591, by rfl⟩ : syracuseStep 10803455 = 16205183) B16205183
theorem B7202303 : Blo 2133435 7202303 := bstep (se 1 (by rfl) ⟨5401727, by rfl⟩ : syracuseStep 7202303 = 10803455) B10803455
theorem B4801535 : Blo 2133435 4801535 := bstep (se 1 (by rfl) ⟨3601151, by rfl⟩ : syracuseStep 4801535 = 7202303) B7202303
theorem B3201023 : Blo 2133435 3201023 := bstep (se 1 (by rfl) ⟨2400767, by rfl⟩ : syracuseStep 3201023 = 4801535) B4801535
theorem B2134015 : Blo 2133435 2134015 := bstep (se 1 (by rfl) ⟨1600511, by rfl⟩ : syracuseStep 2134015 = 3201023) B3201023
theorem B3201029 : Blo 2133435 3201029 := bbase (se 4 (by rfl) ⟨300096, by rfl⟩ : syracuseStep 3201029 = 600193) (by norm_num)
theorem B2134019 : Blo 2133435 2134019 := bstep (se 1 (by rfl) ⟨1600514, by rfl⟩ : syracuseStep 2134019 = 3201029) B3201029
theorem B3601165 : Blo 2133435 3601165 := bbase (se 3 (by rfl) ⟨675218, by rfl⟩ : syracuseStep 3601165 = 1350437) (by norm_num)
theorem B4801553 : Blo 2133435 4801553 := bstep (se 2 (by rfl) ⟨1800582, by rfl⟩ : syracuseStep 4801553 = 3601165) B3601165
theorem B3201035 : Blo 2133435 3201035 := bstep (se 1 (by rfl) ⟨2400776, by rfl⟩ : syracuseStep 3201035 = 4801553) B4801553
theorem B2134023 : Blo 2133435 2134023 := bstep (se 1 (by rfl) ⟨1600517, by rfl⟩ : syracuseStep 2134023 = 3201035) B3201035
theorem B2400781 : Blo 2133435 2400781 := bbase (se 3 (by rfl) ⟨450146, by rfl⟩ : syracuseStep 2400781 = 900293) (by norm_num)
theorem B3201041 : Blo 2133435 3201041 := bstep (se 2 (by rfl) ⟨1200390, by rfl⟩ : syracuseStep 3201041 = 2400781) B2400781
theorem B2134027 : Blo 2133435 2134027 := bstep (se 1 (by rfl) ⟨1600520, by rfl⟩ : syracuseStep 2134027 = 3201041) B3201041
theorem B7202357 : Blo 2133435 7202357 := bbase (se 5 (by rfl) ⟨337610, by rfl⟩ : syracuseStep 7202357 = 675221) (by norm_num)
theorem B4801571 : Blo 2133435 4801571 := bstep (se 1 (by rfl) ⟨3601178, by rfl⟩ : syracuseStep 4801571 = 7202357) B7202357
theorem B3201047 : Blo 2133435 3201047 := bstep (se 1 (by rfl) ⟨2400785, by rfl⟩ : syracuseStep 3201047 = 4801571) B4801571
theorem B2134031 : Blo 2133435 2134031 := bstep (se 1 (by rfl) ⟨1600523, by rfl⟩ : syracuseStep 2134031 = 3201047) B3201047
theorem B3201053 : Blo 2133435 3201053 := bbase (se 3 (by rfl) ⟨600197, by rfl⟩ : syracuseStep 3201053 = 1200395) (by norm_num)
theorem B2134035 : Blo 2133435 2134035 := bstep (se 1 (by rfl) ⟨1600526, by rfl⟩ : syracuseStep 2134035 = 3201053) B3201053
theorem B4801589 : Blo 2133435 4801589 := bbase (se 5 (by rfl) ⟨225074, by rfl⟩ : syracuseStep 4801589 = 450149) (by norm_num)
theorem B3201059 : Blo 2133435 3201059 := bstep (se 1 (by rfl) ⟨2400794, by rfl⟩ : syracuseStep 3201059 = 4801589) B4801589
theorem B2134039 : Blo 2133435 2134039 := bstep (se 1 (by rfl) ⟨1600529, by rfl⟩ : syracuseStep 2134039 = 3201059) B3201059
theorem B2563745 : Blo 2133435 2563745 := bbase (se 2 (by rfl) ⟨961404, by rfl⟩ : syracuseStep 2563745 = 1922809) (by norm_num)
theorem B6836653 : Blo 2133435 6836653 := bstep (se 3 (by rfl) ⟨1281872, by rfl⟩ : syracuseStep 6836653 = 2563745) B2563745
theorem B9115537 : Blo 2133435 9115537 := bstep (se 2 (by rfl) ⟨3418326, by rfl⟩ : syracuseStep 9115537 = 6836653) B6836653
theorem B12154049 : Blo 2133435 12154049 := bstep (se 2 (by rfl) ⟨4557768, by rfl⟩ : syracuseStep 12154049 = 9115537) B9115537
theorem B8102699 : Blo 2133435 8102699 := bstep (se 1 (by rfl) ⟨6077024, by rfl⟩ : syracuseStep 8102699 = 12154049) B12154049
theorem B5401799 : Blo 2133435 5401799 := bstep (se 1 (by rfl) ⟨4051349, by rfl⟩ : syracuseStep 5401799 = 8102699) B8102699
theorem B3601199 : Blo 2133435 3601199 := bstep (se 1 (by rfl) ⟨2700899, by rfl⟩ : syracuseStep 3601199 = 5401799) B5401799
theorem B2400799 : Blo 2133435 2400799 := bstep (se 1 (by rfl) ⟨1800599, by rfl⟩ : syracuseStep 2400799 = 3601199) B3601199
theorem B3201065 : Blo 2133435 3201065 := bstep (se 2 (by rfl) ⟨1200399, by rfl⟩ : syracuseStep 3201065 = 2400799) B2400799
theorem B2134043 : Blo 2133435 2134043 := bstep (se 1 (by rfl) ⟨1600532, by rfl⟩ : syracuseStep 2134043 = 3201065) B3201065
theorem B5768437 : Blo 2133435 5768437 := bbase (se 5 (by rfl) ⟨270395, by rfl⟩ : syracuseStep 5768437 = 540791) (by norm_num)
theorem B7691249 : Blo 2133435 7691249 := bstep (se 2 (by rfl) ⟨2884218, by rfl⟩ : syracuseStep 7691249 = 5768437) B5768437
theorem B5127499 : Blo 2133435 5127499 := bstep (se 1 (by rfl) ⟨3845624, by rfl⟩ : syracuseStep 5127499 = 7691249) B7691249
theorem B6836665 : Blo 2133435 6836665 := bstep (se 2 (by rfl) ⟨2563749, by rfl⟩ : syracuseStep 6836665 = 5127499) B5127499
theorem B9115553 : Blo 2133435 9115553 := bstep (se 2 (by rfl) ⟨3418332, by rfl⟩ : syracuseStep 9115553 = 6836665) B6836665
theorem B6077035 : Blo 2133435 6077035 := bstep (se 1 (by rfl) ⟨4557776, by rfl⟩ : syracuseStep 6077035 = 9115553) B9115553
theorem B8102713 : Blo 2133435 8102713 := bstep (se 2 (by rfl) ⟨3038517, by rfl⟩ : syracuseStep 8102713 = 6077035) B6077035
theorem B10803617 : Blo 2133435 10803617 := bstep (se 2 (by rfl) ⟨4051356, by rfl⟩ : syracuseStep 10803617 = 8102713) B8102713
theorem B7202411 : Blo 2133435 7202411 := bstep (se 1 (by rfl) ⟨5401808, by rfl⟩ : syracuseStep 7202411 = 10803617) B10803617
theorem B4801607 : Blo 2133435 4801607 := bstep (se 1 (by rfl) ⟨3601205, by rfl⟩ : syracuseStep 4801607 = 7202411) B7202411
theorem B3201071 : Blo 2133435 3201071 := bstep (se 1 (by rfl) ⟨2400803, by rfl⟩ : syracuseStep 3201071 = 4801607) B4801607
theorem B2134047 : Blo 2133435 2134047 := bstep (se 1 (by rfl) ⟨1600535, by rfl⟩ : syracuseStep 2134047 = 3201071) B3201071
theorem B3201077 : Blo 2133435 3201077 := bbase (se 5 (by rfl) ⟨150050, by rfl⟩ : syracuseStep 3201077 = 300101) (by norm_num)
theorem B2134051 : Blo 2133435 2134051 := bstep (se 1 (by rfl) ⟨1600538, by rfl⟩ : syracuseStep 2134051 = 3201077) B3201077
theorem B5401829 : Blo 2133435 5401829 := bbase (se 4 (by rfl) ⟨506421, by rfl⟩ : syracuseStep 5401829 = 1012843) (by norm_num)
theorem B3601219 : Blo 2133435 3601219 := bstep (se 1 (by rfl) ⟨2700914, by rfl⟩ : syracuseStep 3601219 = 5401829) B5401829
theorem B4801625 : Blo 2133435 4801625 := bstep (se 2 (by rfl) ⟨1800609, by rfl⟩ : syracuseStep 4801625 = 3601219) B3601219
theorem B3201083 : Blo 2133435 3201083 := bstep (se 1 (by rfl) ⟨2400812, by rfl⟩ : syracuseStep 3201083 = 4801625) B4801625
theorem B2134055 : Blo 2133435 2134055 := bstep (se 1 (by rfl) ⟨1600541, by rfl⟩ : syracuseStep 2134055 = 3201083) B3201083
theorem B2400817 : Blo 2133435 2400817 := bbase (se 2 (by rfl) ⟨900306, by rfl⟩ : syracuseStep 2400817 = 1800613) (by norm_num)
theorem B3201089 : Blo 2133435 3201089 := bstep (se 2 (by rfl) ⟨1200408, by rfl⟩ : syracuseStep 3201089 = 2400817) B2400817
theorem B2134059 : Blo 2133435 2134059 := bstep (se 1 (by rfl) ⟨1600544, by rfl⟩ : syracuseStep 2134059 = 3201089) B3201089
theorem B2563769 : Blo 2133435 2563769 := bbase (se 2 (by rfl) ⟨961413, by rfl⟩ : syracuseStep 2563769 = 1922827) (by norm_num)
theorem B6836717 : Blo 2133435 6836717 := bstep (se 3 (by rfl) ⟨1281884, by rfl⟩ : syracuseStep 6836717 = 2563769) B2563769
theorem B4557811 : Blo 2133435 4557811 := bstep (se 1 (by rfl) ⟨3418358, by rfl⟩ : syracuseStep 4557811 = 6836717) B6836717
theorem B6077081 : Blo 2133435 6077081 := bstep (se 2 (by rfl) ⟨2278905, by rfl⟩ : syracuseStep 6077081 = 4557811) B4557811
theorem B4051387 : Blo 2133435 4051387 := bstep (se 1 (by rfl) ⟨3038540, by rfl⟩ : syracuseStep 4051387 = 6077081) B6077081
theorem B5401849 : Blo 2133435 5401849 := bstep (se 2 (by rfl) ⟨2025693, by rfl⟩ : syracuseStep 5401849 = 4051387) B4051387
theorem B7202465 : Blo 2133435 7202465 := bstep (se 2 (by rfl) ⟨2700924, by rfl⟩ : syracuseStep 7202465 = 5401849) B5401849
theorem B4801643 : Blo 2133435 4801643 := bstep (se 1 (by rfl) ⟨3601232, by rfl⟩ : syracuseStep 4801643 = 7202465) B7202465
theorem B3201095 : Blo 2133435 3201095 := bstep (se 1 (by rfl) ⟨2400821, by rfl⟩ : syracuseStep 3201095 = 4801643) B4801643
theorem B2134063 : Blo 2133435 2134063 := bstep (se 1 (by rfl) ⟨1600547, by rfl⟩ : syracuseStep 2134063 = 3201095) B3201095
theorem B3201101 : Blo 2133435 3201101 := bbase (se 3 (by rfl) ⟨600206, by rfl⟩ : syracuseStep 3201101 = 1200413) (by norm_num)
theorem B2134067 : Blo 2133435 2134067 := bstep (se 1 (by rfl) ⟨1600550, by rfl⟩ : syracuseStep 2134067 = 3201101) B3201101
theorem B4801661 : Blo 2133435 4801661 := bbase (se 3 (by rfl) ⟨900311, by rfl⟩ : syracuseStep 4801661 = 1800623) (by norm_num)
theorem B3201107 : Blo 2133435 3201107 := bstep (se 1 (by rfl) ⟨2400830, by rfl⟩ : syracuseStep 3201107 = 4801661) B4801661
theorem B2134071 : Blo 2133435 2134071 := bstep (se 1 (by rfl) ⟨1600553, by rfl⟩ : syracuseStep 2134071 = 3201107) B3201107
theorem B3601253 : Blo 2133435 3601253 := bbase (se 4 (by rfl) ⟨337617, by rfl⟩ : syracuseStep 3601253 = 675235) (by norm_num)
theorem B2400835 : Blo 2133435 2400835 := bstep (se 1 (by rfl) ⟨1800626, by rfl⟩ : syracuseStep 2400835 = 3601253) B3601253
theorem B3201113 : Blo 2133435 3201113 := bstep (se 2 (by rfl) ⟨1200417, by rfl⟩ : syracuseStep 3201113 = 2400835) B2400835
theorem B2134075 : Blo 2133435 2134075 := bstep (se 1 (by rfl) ⟨1600556, by rfl⟩ : syracuseStep 2134075 = 3201113) B3201113
theorem B4557845 : Blo 2133435 4557845 := bbase (se 6 (by rfl) ⟨106824, by rfl⟩ : syracuseStep 4557845 = 213649) (by norm_num)
theorem B3038563 : Blo 2133435 3038563 := bstep (se 1 (by rfl) ⟨2278922, by rfl⟩ : syracuseStep 3038563 = 4557845) B4557845
theorem B16205669 : Blo 2133435 16205669 := bstep (se 4 (by rfl) ⟨1519281, by rfl⟩ : syracuseStep 16205669 = 3038563) B3038563
theorem B10803779 : Blo 2133435 10803779 := bstep (se 1 (by rfl) ⟨8102834, by rfl⟩ : syracuseStep 10803779 = 16205669) B16205669
theorem B7202519 : Blo 2133435 7202519 := bstep (se 1 (by rfl) ⟨5401889, by rfl⟩ : syracuseStep 7202519 = 10803779) B10803779
theorem B4801679 : Blo 2133435 4801679 := bstep (se 1 (by rfl) ⟨3601259, by rfl⟩ : syracuseStep 4801679 = 7202519) B7202519
theorem B3201119 : Blo 2133435 3201119 := bstep (se 1 (by rfl) ⟨2400839, by rfl⟩ : syracuseStep 3201119 = 4801679) B4801679
theorem B2134079 : Blo 2133435 2134079 := bstep (se 1 (by rfl) ⟨1600559, by rfl⟩ : syracuseStep 2134079 = 3201119) B3201119
theorem B3201125 : Blo 2133435 3201125 := bbase (se 4 (by rfl) ⟨300105, by rfl⟩ : syracuseStep 3201125 = 600211) (by norm_num)
theorem B2134083 : Blo 2133435 2134083 := bstep (se 1 (by rfl) ⟨1600562, by rfl⟩ : syracuseStep 2134083 = 3201125) B3201125
theorem B2163205 : Blo 2133435 2163205 := bbase (se 4 (by rfl) ⟨202800, by rfl⟩ : syracuseStep 2163205 = 405601) (by norm_num)
theorem B11537093 : Blo 2133435 11537093 := bstep (se 4 (by rfl) ⟨1081602, by rfl⟩ : syracuseStep 11537093 = 2163205) B2163205
theorem B7691395 : Blo 2133435 7691395 := bstep (se 1 (by rfl) ⟨5768546, by rfl⟩ : syracuseStep 7691395 = 11537093) B11537093
theorem B10255193 : Blo 2133435 10255193 := bstep (se 2 (by rfl) ⟨3845697, by rfl⟩ : syracuseStep 10255193 = 7691395) B7691395
theorem B6836795 : Blo 2133435 6836795 := bstep (se 1 (by rfl) ⟨5127596, by rfl⟩ : syracuseStep 6836795 = 10255193) B10255193
theorem B4557863 : Blo 2133435 4557863 := bstep (se 1 (by rfl) ⟨3418397, by rfl⟩ : syracuseStep 4557863 = 6836795) B6836795
theorem B3038575 : Blo 2133435 3038575 := bstep (se 1 (by rfl) ⟨2278931, by rfl⟩ : syracuseStep 3038575 = 4557863) B4557863
theorem B4051433 : Blo 2133435 4051433 := bstep (se 2 (by rfl) ⟨1519287, by rfl⟩ : syracuseStep 4051433 = 3038575) B3038575
theorem B2700955 : Blo 2133435 2700955 := bstep (se 1 (by rfl) ⟨2025716, by rfl⟩ : syracuseStep 2700955 = 4051433) B4051433
theorem B3601273 : Blo 2133435 3601273 := bstep (se 2 (by rfl) ⟨1350477, by rfl⟩ : syracuseStep 3601273 = 2700955) B2700955
theorem B4801697 : Blo 2133435 4801697 := bstep (se 2 (by rfl) ⟨1800636, by rfl⟩ : syracuseStep 4801697 = 3601273) B3601273
theorem B3201131 : Blo 2133435 3201131 := bstep (se 1 (by rfl) ⟨2400848, by rfl⟩ : syracuseStep 3201131 = 4801697) B4801697
theorem B2134087 : Blo 2133435 2134087 := bstep (se 1 (by rfl) ⟨1600565, by rfl⟩ : syracuseStep 2134087 = 3201131) B3201131
theorem B2400853 : Blo 2133435 2400853 := bbase (se 8 (by rfl) ⟨14067, by rfl⟩ : syracuseStep 2400853 = 28135) (by norm_num)
theorem B3201137 : Blo 2133435 3201137 := bstep (se 2 (by rfl) ⟨1200426, by rfl⟩ : syracuseStep 3201137 = 2400853) B2400853
theorem B2134091 : Blo 2133435 2134091 := bstep (se 1 (by rfl) ⟨1600568, by rfl⟩ : syracuseStep 2134091 = 3201137) B3201137
theorem B2700965 : Blo 2133435 2700965 := bbase (se 4 (by rfl) ⟨253215, by rfl⟩ : syracuseStep 2700965 = 506431) (by norm_num)
theorem B7202573 : Blo 2133435 7202573 := bstep (se 3 (by rfl) ⟨1350482, by rfl⟩ : syracuseStep 7202573 = 2700965) B2700965
theorem B4801715 : Blo 2133435 4801715 := bstep (se 1 (by rfl) ⟨3601286, by rfl⟩ : syracuseStep 4801715 = 7202573) B7202573
theorem B3201143 : Blo 2133435 3201143 := bstep (se 1 (by rfl) ⟨2400857, by rfl⟩ : syracuseStep 3201143 = 4801715) B4801715
theorem B2134095 : Blo 2133435 2134095 := bstep (se 1 (by rfl) ⟨1600571, by rfl⟩ : syracuseStep 2134095 = 3201143) B3201143
theorem B3201149 : Blo 2133435 3201149 := bbase (se 3 (by rfl) ⟨600215, by rfl⟩ : syracuseStep 3201149 = 1200431) (by norm_num)
theorem B2134099 : Blo 2133435 2134099 := bstep (se 1 (by rfl) ⟨1600574, by rfl⟩ : syracuseStep 2134099 = 3201149) B3201149
theorem B4801733 : Blo 2133435 4801733 := bbase (se 4 (by rfl) ⟨450162, by rfl⟩ : syracuseStep 4801733 = 900325) (by norm_num)
theorem B3201155 : Blo 2133435 3201155 := bstep (se 1 (by rfl) ⟨2400866, by rfl⟩ : syracuseStep 3201155 = 4801733) B4801733
theorem B2134103 : Blo 2133435 2134103 := bstep (se 1 (by rfl) ⟨1600577, by rfl⟩ : syracuseStep 2134103 = 3201155) B3201155
theorem B13673717 : Blo 2133435 13673717 := bbase (se 5 (by rfl) ⟨640955, by rfl⟩ : syracuseStep 13673717 = 1281911) (by norm_num)
theorem B9115811 : Blo 2133435 9115811 := bstep (se 1 (by rfl) ⟨6836858, by rfl⟩ : syracuseStep 9115811 = 13673717) B13673717
theorem B6077207 : Blo 2133435 6077207 := bstep (se 1 (by rfl) ⟨4557905, by rfl⟩ : syracuseStep 6077207 = 9115811) B9115811
theorem B4051471 : Blo 2133435 4051471 := bstep (se 1 (by rfl) ⟨3038603, by rfl⟩ : syracuseStep 4051471 = 6077207) B6077207
theorem B5401961 : Blo 2133435 5401961 := bstep (se 2 (by rfl) ⟨2025735, by rfl⟩ : syracuseStep 5401961 = 4051471) B4051471
theorem B3601307 : Blo 2133435 3601307 := bstep (se 1 (by rfl) ⟨2700980, by rfl⟩ : syracuseStep 3601307 = 5401961) B5401961
theorem B2400871 : Blo 2133435 2400871 := bstep (se 1 (by rfl) ⟨1800653, by rfl⟩ : syracuseStep 2400871 = 3601307) B3601307
theorem B3201161 : Blo 2133435 3201161 := bstep (se 2 (by rfl) ⟨1200435, by rfl⟩ : syracuseStep 3201161 = 2400871) B2400871
theorem B2134107 : Blo 2133435 2134107 := bstep (se 1 (by rfl) ⟨1600580, by rfl⟩ : syracuseStep 2134107 = 3201161) B3201161
theorem B10803941 : Blo 2133435 10803941 := bbase (se 4 (by rfl) ⟨1012869, by rfl⟩ : syracuseStep 10803941 = 2025739) (by norm_num)
theorem B7202627 : Blo 2133435 7202627 := bstep (se 1 (by rfl) ⟨5401970, by rfl⟩ : syracuseStep 7202627 = 10803941) B10803941
theorem B4801751 : Blo 2133435 4801751 := bstep (se 1 (by rfl) ⟨3601313, by rfl⟩ : syracuseStep 4801751 = 7202627) B7202627
theorem B3201167 : Blo 2133435 3201167 := bstep (se 1 (by rfl) ⟨2400875, by rfl⟩ : syracuseStep 3201167 = 4801751) B4801751
theorem B2134111 : Blo 2133435 2134111 := bstep (se 1 (by rfl) ⟨1600583, by rfl⟩ : syracuseStep 2134111 = 3201167) B3201167
theorem B3201173 : Blo 2133435 3201173 := bbase (se 6 (by rfl) ⟨75027, by rfl⟩ : syracuseStep 3201173 = 150055) (by norm_num)
theorem B2134115 : Blo 2133435 2134115 := bstep (se 1 (by rfl) ⟨1600586, by rfl⟩ : syracuseStep 2134115 = 3201173) B3201173
theorem B9115861 : Blo 2133435 9115861 := bbase (se 7 (by rfl) ⟨106826, by rfl⟩ : syracuseStep 9115861 = 213653) (by norm_num)
theorem B12154481 : Blo 2133435 12154481 := bstep (se 2 (by rfl) ⟨4557930, by rfl⟩ : syracuseStep 12154481 = 9115861) B9115861
theorem B8102987 : Blo 2133435 8102987 := bstep (se 1 (by rfl) ⟨6077240, by rfl⟩ : syracuseStep 8102987 = 12154481) B12154481
theorem B5401991 : Blo 2133435 5401991 := bstep (se 1 (by rfl) ⟨4051493, by rfl⟩ : syracuseStep 5401991 = 8102987) B8102987
theorem B3601327 : Blo 2133435 3601327 := bstep (se 1 (by rfl) ⟨2700995, by rfl⟩ : syracuseStep 3601327 = 5401991) B5401991
theorem B4801769 : Blo 2133435 4801769 := bstep (se 2 (by rfl) ⟨1800663, by rfl⟩ : syracuseStep 4801769 = 3601327) B3601327
theorem B3201179 : Blo 2133435 3201179 := bstep (se 1 (by rfl) ⟨2400884, by rfl⟩ : syracuseStep 3201179 = 4801769) B4801769
theorem B2134119 : Blo 2133435 2134119 := bstep (se 1 (by rfl) ⟨1600589, by rfl⟩ : syracuseStep 2134119 = 3201179) B3201179
theorem B2400889 : Blo 2133435 2400889 := bbase (se 2 (by rfl) ⟨900333, by rfl⟩ : syracuseStep 2400889 = 1800667) (by norm_num)
theorem B3201185 : Blo 2133435 3201185 := bstep (se 2 (by rfl) ⟨1200444, by rfl⟩ : syracuseStep 3201185 = 2400889) B2400889
theorem B2134123 : Blo 2133435 2134123 := bstep (se 1 (by rfl) ⟨1600592, by rfl⟩ : syracuseStep 2134123 = 3201185) B3201185
theorem B2163245 : Blo 2133435 2163245 := bbase (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) (by norm_num)
theorem B5768653 : Blo 2133435 5768653 := bstep (se 3 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 5768653 = 2163245) B2163245
theorem B7691537 : Blo 2133435 7691537 := bstep (se 2 (by rfl) ⟨2884326, by rfl⟩ : syracuseStep 7691537 = 5768653) B5768653
theorem B20510765 : Blo 2133435 20510765 := bstep (se 3 (by rfl) ⟨3845768, by rfl⟩ : syracuseStep 20510765 = 7691537) B7691537
theorem B13673843 : Blo 2133435 13673843 := bstep (se 1 (by rfl) ⟨10255382, by rfl⟩ : syracuseStep 13673843 = 20510765) B20510765
theorem B9115895 : Blo 2133435 9115895 := bstep (se 1 (by rfl) ⟨6836921, by rfl⟩ : syracuseStep 9115895 = 13673843) B13673843
theorem B6077263 : Blo 2133435 6077263 := bstep (se 1 (by rfl) ⟨4557947, by rfl⟩ : syracuseStep 6077263 = 9115895) B9115895
theorem B8103017 : Blo 2133435 8103017 := bstep (se 2 (by rfl) ⟨3038631, by rfl⟩ : syracuseStep 8103017 = 6077263) B6077263
theorem B5402011 : Blo 2133435 5402011 := bstep (se 1 (by rfl) ⟨4051508, by rfl⟩ : syracuseStep 5402011 = 8103017) B8103017
theorem B7202681 : Blo 2133435 7202681 := bstep (se 2 (by rfl) ⟨2701005, by rfl⟩ : syracuseStep 7202681 = 5402011) B5402011
theorem B4801787 : Blo 2133435 4801787 := bstep (se 1 (by rfl) ⟨3601340, by rfl⟩ : syracuseStep 4801787 = 7202681) B7202681
theorem B3201191 : Blo 2133435 3201191 := bstep (se 1 (by rfl) ⟨2400893, by rfl⟩ : syracuseStep 3201191 = 4801787) B4801787
theorem B2134127 : Blo 2133435 2134127 := bstep (se 1 (by rfl) ⟨1600595, by rfl⟩ : syracuseStep 2134127 = 3201191) B3201191
theorem B3201197 : Blo 2133435 3201197 := bbase (se 3 (by rfl) ⟨600224, by rfl⟩ : syracuseStep 3201197 = 1200449) (by norm_num)
theorem B2134131 : Blo 2133435 2134131 := bstep (se 1 (by rfl) ⟨1600598, by rfl⟩ : syracuseStep 2134131 = 3201197) B3201197
theorem B4801805 : Blo 2133435 4801805 := bbase (se 3 (by rfl) ⟨900338, by rfl⟩ : syracuseStep 4801805 = 1800677) (by norm_num)
theorem B3201203 : Blo 2133435 3201203 := bstep (se 1 (by rfl) ⟨2400902, by rfl⟩ : syracuseStep 3201203 = 4801805) B4801805
theorem B2134135 : Blo 2133435 2134135 := bstep (se 1 (by rfl) ⟨1600601, by rfl⟩ : syracuseStep 2134135 = 3201203) B3201203
theorem B2701021 : Blo 2133435 2701021 := bbase (se 3 (by rfl) ⟨506441, by rfl⟩ : syracuseStep 2701021 = 1012883) (by norm_num)
theorem B3601361 : Blo 2133435 3601361 := bstep (se 2 (by rfl) ⟨1350510, by rfl⟩ : syracuseStep 3601361 = 2701021) B2701021
theorem B2400907 : Blo 2133435 2400907 := bstep (se 1 (by rfl) ⟨1800680, by rfl⟩ : syracuseStep 2400907 = 3601361) B3601361
theorem B3201209 : Blo 2133435 3201209 := bstep (se 2 (by rfl) ⟨1200453, by rfl⟩ : syracuseStep 3201209 = 2400907) B2400907
theorem B2134139 : Blo 2133435 2134139 := bstep (se 1 (by rfl) ⟨1600604, by rfl⟩ : syracuseStep 2134139 = 3201209) B3201209
theorem B18231925 : Blo 2133435 18231925 := bbase (se 5 (by rfl) ⟨854621, by rfl⟩ : syracuseStep 18231925 = 1709243) (by norm_num)
theorem B24309233 : Blo 2133435 24309233 := bstep (se 2 (by rfl) ⟨9115962, by rfl⟩ : syracuseStep 24309233 = 18231925) B18231925
theorem B16206155 : Blo 2133435 16206155 := bstep (se 1 (by rfl) ⟨12154616, by rfl⟩ : syracuseStep 16206155 = 24309233) B24309233
theorem B10804103 : Blo 2133435 10804103 := bstep (se 1 (by rfl) ⟨8103077, by rfl⟩ : syracuseStep 10804103 = 16206155) B16206155
theorem B7202735 : Blo 2133435 7202735 := bstep (se 1 (by rfl) ⟨5402051, by rfl⟩ : syracuseStep 7202735 = 10804103) B10804103
theorem B4801823 : Blo 2133435 4801823 := bstep (se 1 (by rfl) ⟨3601367, by rfl⟩ : syracuseStep 4801823 = 7202735) B7202735
theorem B3201215 : Blo 2133435 3201215 := bstep (se 1 (by rfl) ⟨2400911, by rfl⟩ : syracuseStep 3201215 = 4801823) B4801823
theorem B2134143 : Blo 2133435 2134143 := bstep (se 1 (by rfl) ⟨1600607, by rfl⟩ : syracuseStep 2134143 = 3201215) B3201215
theorem B3201221 : Blo 2133435 3201221 := bbase (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) (by norm_num)
theorem B2134147 : Blo 2133435 2134147 := bstep (se 1 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 2134147 = 3201221) B3201221
theorem B3601381 : Blo 2133435 3601381 := bbase (se 4 (by rfl) ⟨337629, by rfl⟩ : syracuseStep 3601381 = 675259) (by norm_num)
theorem B4801841 : Blo 2133435 4801841 := bstep (se 2 (by rfl) ⟨1800690, by rfl⟩ : syracuseStep 4801841 = 3601381) B3601381
theorem B3201227 : Blo 2133435 3201227 := bstep (se 1 (by rfl) ⟨2400920, by rfl⟩ : syracuseStep 3201227 = 4801841) B4801841
theorem B2134151 : Blo 2133435 2134151 := bstep (se 1 (by rfl) ⟨1600613, by rfl⟩ : syracuseStep 2134151 = 3201227) B3201227
theorem B2400925 : Blo 2133435 2400925 := bbase (se 3 (by rfl) ⟨450173, by rfl⟩ : syracuseStep 2400925 = 900347) (by norm_num)
theorem B3201233 : Blo 2133435 3201233 := bstep (se 2 (by rfl) ⟨1200462, by rfl⟩ : syracuseStep 3201233 = 2400925) B2400925
theorem B2134155 : Blo 2133435 2134155 := bstep (se 1 (by rfl) ⟨1600616, by rfl⟩ : syracuseStep 2134155 = 3201233) B3201233
theorem B7202789 : Blo 2133435 7202789 := bbase (se 4 (by rfl) ⟨675261, by rfl⟩ : syracuseStep 7202789 = 1350523) (by norm_num)
theorem B4801859 : Blo 2133435 4801859 := bstep (se 1 (by rfl) ⟨3601394, by rfl⟩ : syracuseStep 4801859 = 7202789) B7202789
theorem B3201239 : Blo 2133435 3201239 := bstep (se 1 (by rfl) ⟨2400929, by rfl⟩ : syracuseStep 3201239 = 4801859) B4801859
theorem B2134159 : Blo 2133435 2134159 := bstep (se 1 (by rfl) ⟨1600619, by rfl⟩ : syracuseStep 2134159 = 3201239) B3201239
theorem B3201245 : Blo 2133435 3201245 := bbase (se 3 (by rfl) ⟨600233, by rfl⟩ : syracuseStep 3201245 = 1200467) (by norm_num)
theorem B2134163 : Blo 2133435 2134163 := bstep (se 1 (by rfl) ⟨1600622, by rfl⟩ : syracuseStep 2134163 = 3201245) B3201245
theorem B4801877 : Blo 2133435 4801877 := bbase (se 12 (by rfl) ⟨1758, by rfl⟩ : syracuseStep 4801877 = 3517) (by norm_num)
theorem B3201251 : Blo 2133435 3201251 := bstep (se 1 (by rfl) ⟨2400938, by rfl⟩ : syracuseStep 3201251 = 4801877) B4801877
theorem B2134167 : Blo 2133435 2134167 := bstep (se 1 (by rfl) ⟨1600625, by rfl⟩ : syracuseStep 2134167 = 3201251) B3201251
theorem B2279021 : Blo 2133435 2279021 := bbase (se 3 (by rfl) ⟨427316, by rfl⟩ : syracuseStep 2279021 = 854633) (by norm_num)
theorem B6077389 : Blo 2133435 6077389 := bstep (se 3 (by rfl) ⟨1139510, by rfl⟩ : syracuseStep 6077389 = 2279021) B2279021
theorem B8103185 : Blo 2133435 8103185 := bstep (se 2 (by rfl) ⟨3038694, by rfl⟩ : syracuseStep 8103185 = 6077389) B6077389
theorem B5402123 : Blo 2133435 5402123 := bstep (se 1 (by rfl) ⟨4051592, by rfl⟩ : syracuseStep 5402123 = 8103185) B8103185
theorem B3601415 : Blo 2133435 3601415 := bstep (se 1 (by rfl) ⟨2701061, by rfl⟩ : syracuseStep 3601415 = 5402123) B5402123
theorem B2400943 : Blo 2133435 2400943 := bstep (se 1 (by rfl) ⟨1800707, by rfl⟩ : syracuseStep 2400943 = 3601415) B3601415
theorem B3201257 : Blo 2133435 3201257 := bstep (se 2 (by rfl) ⟨1200471, by rfl⟩ : syracuseStep 3201257 = 2400943) B2400943
theorem B2134171 : Blo 2133435 2134171 := bstep (se 1 (by rfl) ⟨1600628, by rfl⟩ : syracuseStep 2134171 = 3201257) B3201257
theorem B7217909 : Blo 2133435 7217909 := bbase (se 5 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 7217909 = 676679) (by norm_num)
theorem B4811939 : Blo 2133435 4811939 := bstep (se 1 (by rfl) ⟨3608954, by rfl⟩ : syracuseStep 4811939 = 7217909) B7217909
theorem B3207959 : Blo 2133435 3207959 := bstep (se 1 (by rfl) ⟨2405969, by rfl⟩ : syracuseStep 3207959 = 4811939) B4811939
theorem B136872917 : Blo 2133435 136872917 := bstep (se 7 (by rfl) ⟨1603979, by rfl⟩ : syracuseStep 136872917 = 3207959) B3207959
theorem B91248611 : Blo 2133435 91248611 := bstep (se 1 (by rfl) ⟨68436458, by rfl⟩ : syracuseStep 91248611 = 136872917) B136872917
theorem B243329629 : Blo 2133435 243329629 := bstep (se 3 (by rfl) ⟨45624305, by rfl⟩ : syracuseStep 243329629 = 91248611) B91248611
theorem B324439505 : Blo 2133435 324439505 := bstep (se 2 (by rfl) ⟨121664814, by rfl⟩ : syracuseStep 324439505 = 243329629) B243329629
theorem B216293003 : Blo 2133435 216293003 := bstep (se 1 (by rfl) ⟨162219752, by rfl⟩ : syracuseStep 216293003 = 324439505) B324439505
theorem B144195335 : Blo 2133435 144195335 := bstep (se 1 (by rfl) ⟨108146501, by rfl⟩ : syracuseStep 144195335 = 216293003) B216293003
theorem B96130223 : Blo 2133435 96130223 := bstep (se 1 (by rfl) ⟨72097667, by rfl⟩ : syracuseStep 96130223 = 144195335) B144195335
theorem B64086815 : Blo 2133435 64086815 := bstep (se 1 (by rfl) ⟨48065111, by rfl⟩ : syracuseStep 64086815 = 96130223) B96130223
theorem B170898173 : Blo 2133435 170898173 := bstep (se 3 (by rfl) ⟨32043407, by rfl⟩ : syracuseStep 170898173 = 64086815) B64086815
theorem B113932115 : Blo 2133435 113932115 := bstep (se 1 (by rfl) ⟨85449086, by rfl⟩ : syracuseStep 113932115 = 170898173) B170898173
theorem B75954743 : Blo 2133435 75954743 := bstep (se 1 (by rfl) ⟨56966057, by rfl⟩ : syracuseStep 75954743 = 113932115) B113932115
theorem B50636495 : Blo 2133435 50636495 := bstep (se 1 (by rfl) ⟨37977371, by rfl⟩ : syracuseStep 50636495 = 75954743) B75954743
theorem B33757663 : Blo 2133435 33757663 := bstep (se 1 (by rfl) ⟨25318247, by rfl⟩ : syracuseStep 33757663 = 50636495) B50636495
theorem B45010217 : Blo 2133435 45010217 := bstep (se 2 (by rfl) ⟨16878831, by rfl⟩ : syracuseStep 45010217 = 33757663) B33757663
theorem B30006811 : Blo 2133435 30006811 := bstep (se 1 (by rfl) ⟨22505108, by rfl⟩ : syracuseStep 30006811 = 45010217) B45010217
theorem B40009081 : Blo 2133435 40009081 := bstep (se 2 (by rfl) ⟨15003405, by rfl⟩ : syracuseStep 40009081 = 30006811) B30006811
theorem B53345441 : Blo 2133435 53345441 := bstep (se 2 (by rfl) ⟨20004540, by rfl⟩ : syracuseStep 53345441 = 40009081) B40009081
theorem B35563627 : Blo 2133435 35563627 := bstep (se 1 (by rfl) ⟨26672720, by rfl⟩ : syracuseStep 35563627 = 53345441) B53345441
theorem B47418169 : Blo 2133435 47418169 := bstep (se 2 (by rfl) ⟨17781813, by rfl⟩ : syracuseStep 47418169 = 35563627) B35563627
theorem B63224225 : Blo 2133435 63224225 := bstep (se 2 (by rfl) ⟨23709084, by rfl⟩ : syracuseStep 63224225 = 47418169) B47418169
theorem B42149483 : Blo 2133435 42149483 := bstep (se 1 (by rfl) ⟨31612112, by rfl⟩ : syracuseStep 42149483 = 63224225) B63224225
theorem B28099655 : Blo 2133435 28099655 := bstep (se 1 (by rfl) ⟨21074741, by rfl⟩ : syracuseStep 28099655 = 42149483) B42149483
theorem B18733103 : Blo 2133435 18733103 := bstep (se 1 (by rfl) ⟨14049827, by rfl⟩ : syracuseStep 18733103 = 28099655) B28099655
theorem B12488735 : Blo 2133435 12488735 := bstep (se 1 (by rfl) ⟨9366551, by rfl⟩ : syracuseStep 12488735 = 18733103) B18733103
theorem B8325823 : Blo 2133435 8325823 := bstep (se 1 (by rfl) ⟨6244367, by rfl⟩ : syracuseStep 8325823 = 12488735) B12488735
theorem B11101097 : Blo 2133435 11101097 := bstep (se 2 (by rfl) ⟨4162911, by rfl⟩ : syracuseStep 11101097 = 8325823) B8325823
theorem B29602925 : Blo 2133435 29602925 := bstep (se 3 (by rfl) ⟨5550548, by rfl⟩ : syracuseStep 29602925 = 11101097) B11101097
theorem B19735283 : Blo 2133435 19735283 := bstep (se 1 (by rfl) ⟨14801462, by rfl⟩ : syracuseStep 19735283 = 29602925) B29602925
theorem B52627421 : Blo 2133435 52627421 := bstep (se 3 (by rfl) ⟨9867641, by rfl⟩ : syracuseStep 52627421 = 19735283) B19735283
theorem B35084947 : Blo 2133435 35084947 := bstep (se 1 (by rfl) ⟨26313710, by rfl⟩ : syracuseStep 35084947 = 52627421) B52627421
theorem B46779929 : Blo 2133435 46779929 := bstep (se 2 (by rfl) ⟨17542473, by rfl⟩ : syracuseStep 46779929 = 35084947) B35084947
theorem B31186619 : Blo 2133435 31186619 := bstep (se 1 (by rfl) ⟨23389964, by rfl⟩ : syracuseStep 31186619 = 46779929) B46779929
theorem B20791079 : Blo 2133435 20791079 := bstep (se 1 (by rfl) ⟨15593309, by rfl⟩ : syracuseStep 20791079 = 31186619) B31186619
theorem B13860719 : Blo 2133435 13860719 := bstep (se 1 (by rfl) ⟨10395539, by rfl⟩ : syracuseStep 13860719 = 20791079) B20791079
theorem B9240479 : Blo 2133435 9240479 := bstep (se 1 (by rfl) ⟨6930359, by rfl⟩ : syracuseStep 9240479 = 13860719) B13860719
theorem B6160319 : Blo 2133435 6160319 := bstep (se 1 (by rfl) ⟨4620239, by rfl⟩ : syracuseStep 6160319 = 9240479) B9240479
theorem B4106879 : Blo 2133435 4106879 := bstep (se 1 (by rfl) ⟨3080159, by rfl⟩ : syracuseStep 4106879 = 6160319) B6160319
theorem B2737919 : Blo 2133435 2737919 := bstep (se 1 (by rfl) ⟨2053439, by rfl⟩ : syracuseStep 2737919 = 4106879) B4106879
theorem B7301117 : Blo 2133435 7301117 := bstep (se 3 (by rfl) ⟨1368959, by rfl⟩ : syracuseStep 7301117 = 2737919) B2737919
theorem B4867411 : Blo 2133435 4867411 := bstep (se 1 (by rfl) ⟨3650558, by rfl⟩ : syracuseStep 4867411 = 7301117) B7301117
theorem B6489881 : Blo 2133435 6489881 := bstep (se 2 (by rfl) ⟨2433705, by rfl⟩ : syracuseStep 6489881 = 4867411) B4867411
theorem B4326587 : Blo 2133435 4326587 := bstep (se 1 (by rfl) ⟨3244940, by rfl⟩ : syracuseStep 4326587 = 6489881) B6489881
theorem B2884391 : Blo 2133435 2884391 := bstep (se 1 (by rfl) ⟨2163293, by rfl⟩ : syracuseStep 2884391 = 4326587) B4326587
theorem B30766837 : Blo 2133435 30766837 := bstep (se 5 (by rfl) ⟨1442195, by rfl⟩ : syracuseStep 30766837 = 2884391) B2884391
theorem B41022449 : Blo 2133435 41022449 := bstep (se 2 (by rfl) ⟨15383418, by rfl⟩ : syracuseStep 41022449 = 30766837) B30766837
theorem B27348299 : Blo 2133435 27348299 := bstep (se 1 (by rfl) ⟨20511224, by rfl⟩ : syracuseStep 27348299 = 41022449) B41022449
theorem B18232199 : Blo 2133435 18232199 := bstep (se 1 (by rfl) ⟨13674149, by rfl⟩ : syracuseStep 18232199 = 27348299) B27348299
theorem B12154799 : Blo 2133435 12154799 := bstep (se 1 (by rfl) ⟨9116099, by rfl⟩ : syracuseStep 12154799 = 18232199) B18232199
theorem B8103199 : Blo 2133435 8103199 := bstep (se 1 (by rfl) ⟨6077399, by rfl⟩ : syracuseStep 8103199 = 12154799) B12154799
theorem B10804265 : Blo 2133435 10804265 := bstep (se 2 (by rfl) ⟨4051599, by rfl⟩ : syracuseStep 10804265 = 8103199) B8103199
theorem B7202843 : Blo 2133435 7202843 := bstep (se 1 (by rfl) ⟨5402132, by rfl⟩ : syracuseStep 7202843 = 10804265) B10804265
theorem B4801895 : Blo 2133435 4801895 := bstep (se 1 (by rfl) ⟨3601421, by rfl⟩ : syracuseStep 4801895 = 7202843) B7202843
theorem B3201263 : Blo 2133435 3201263 := bstep (se 1 (by rfl) ⟨2400947, by rfl⟩ : syracuseStep 3201263 = 4801895) B4801895
theorem B2134175 : Blo 2133435 2134175 := bstep (se 1 (by rfl) ⟨1600631, by rfl⟩ : syracuseStep 2134175 = 3201263) B3201263
theorem B3201269 : Blo 2133435 3201269 := bbase (se 5 (by rfl) ⟨150059, by rfl⟩ : syracuseStep 3201269 = 300119) (by norm_num)
theorem B2134179 : Blo 2133435 2134179 := bstep (se 1 (by rfl) ⟨1600634, by rfl⟩ : syracuseStep 2134179 = 3201269) B3201269
theorem B19469717 : Blo 2133435 19469717 := bbase (se 6 (by rfl) ⟨456321, by rfl⟩ : syracuseStep 19469717 = 912643) (by norm_num)
theorem B12979811 : Blo 2133435 12979811 := bstep (se 1 (by rfl) ⟨9734858, by rfl⟩ : syracuseStep 12979811 = 19469717) B19469717
theorem B34612829 : Blo 2133435 34612829 := bstep (se 3 (by rfl) ⟨6489905, by rfl⟩ : syracuseStep 34612829 = 12979811) B12979811
theorem B23075219 : Blo 2133435 23075219 := bstep (se 1 (by rfl) ⟨17306414, by rfl⟩ : syracuseStep 23075219 = 34612829) B34612829
theorem B15383479 : Blo 2133435 15383479 := bstep (se 1 (by rfl) ⟨11537609, by rfl⟩ : syracuseStep 15383479 = 23075219) B23075219
theorem B20511305 : Blo 2133435 20511305 := bstep (se 2 (by rfl) ⟨7691739, by rfl⟩ : syracuseStep 20511305 = 15383479) B15383479
theorem B13674203 : Blo 2133435 13674203 := bstep (se 1 (by rfl) ⟨10255652, by rfl⟩ : syracuseStep 13674203 = 20511305) B20511305
theorem B9116135 : Blo 2133435 9116135 := bstep (se 1 (by rfl) ⟨6837101, by rfl⟩ : syracuseStep 9116135 = 13674203) B13674203
theorem B6077423 : Blo 2133435 6077423 := bstep (se 1 (by rfl) ⟨4558067, by rfl⟩ : syracuseStep 6077423 = 9116135) B9116135
theorem B4051615 : Blo 2133435 4051615 := bstep (se 1 (by rfl) ⟨3038711, by rfl⟩ : syracuseStep 4051615 = 6077423) B6077423
theorem B5402153 : Blo 2133435 5402153 := bstep (se 2 (by rfl) ⟨2025807, by rfl⟩ : syracuseStep 5402153 = 4051615) B4051615
theorem B3601435 : Blo 2133435 3601435 := bstep (se 1 (by rfl) ⟨2701076, by rfl⟩ : syracuseStep 3601435 = 5402153) B5402153
theorem B4801913 : Blo 2133435 4801913 := bstep (se 2 (by rfl) ⟨1800717, by rfl⟩ : syracuseStep 4801913 = 3601435) B3601435
theorem B3201275 : Blo 2133435 3201275 := bstep (se 1 (by rfl) ⟨2400956, by rfl⟩ : syracuseStep 3201275 = 4801913) B4801913
theorem B2134183 : Blo 2133435 2134183 := bstep (se 1 (by rfl) ⟨1600637, by rfl⟩ : syracuseStep 2134183 = 3201275) B3201275
theorem B2400961 : Blo 2133435 2400961 := bbase (se 2 (by rfl) ⟨900360, by rfl⟩ : syracuseStep 2400961 = 1800721) (by norm_num)
theorem B3201281 : Blo 2133435 3201281 := bstep (se 2 (by rfl) ⟨1200480, by rfl⟩ : syracuseStep 3201281 = 2400961) B2400961
theorem B2134187 : Blo 2133435 2134187 := bstep (se 1 (by rfl) ⟨1600640, by rfl⟩ : syracuseStep 2134187 = 3201281) B3201281
theorem B5402173 : Blo 2133435 5402173 := bbase (se 3 (by rfl) ⟨1012907, by rfl⟩ : syracuseStep 5402173 = 2025815) (by norm_num)
theorem B7202897 : Blo 2133435 7202897 := bstep (se 2 (by rfl) ⟨2701086, by rfl⟩ : syracuseStep 7202897 = 5402173) B5402173
theorem B4801931 : Blo 2133435 4801931 := bstep (se 1 (by rfl) ⟨3601448, by rfl⟩ : syracuseStep 4801931 = 7202897) B7202897
theorem B3201287 : Blo 2133435 3201287 := bstep (se 1 (by rfl) ⟨2400965, by rfl⟩ : syracuseStep 3201287 = 4801931) B4801931
theorem B2134191 : Blo 2133435 2134191 := bstep (se 1 (by rfl) ⟨1600643, by rfl⟩ : syracuseStep 2134191 = 3201287) B3201287
theorem B3201293 : Blo 2133435 3201293 := bbase (se 3 (by rfl) ⟨600242, by rfl⟩ : syracuseStep 3201293 = 1200485) (by norm_num)
theorem B2134195 : Blo 2133435 2134195 := bstep (se 1 (by rfl) ⟨1600646, by rfl⟩ : syracuseStep 2134195 = 3201293) B3201293
theorem B4801949 : Blo 2133435 4801949 := bbase (se 3 (by rfl) ⟨900365, by rfl⟩ : syracuseStep 4801949 = 1800731) (by norm_num)
theorem B3201299 : Blo 2133435 3201299 := bstep (se 1 (by rfl) ⟨2400974, by rfl⟩ : syracuseStep 3201299 = 4801949) B4801949
theorem B2134199 : Blo 2133435 2134199 := bstep (se 1 (by rfl) ⟨1600649, by rfl⟩ : syracuseStep 2134199 = 3201299) B3201299
theorem B3601469 : Blo 2133435 3601469 := bbase (se 3 (by rfl) ⟨675275, by rfl⟩ : syracuseStep 3601469 = 1350551) (by norm_num)
theorem B2400979 : Blo 2133435 2400979 := bstep (se 1 (by rfl) ⟨1800734, by rfl⟩ : syracuseStep 2400979 = 3601469) B3601469
theorem B3201305 : Blo 2133435 3201305 := bstep (se 2 (by rfl) ⟨1200489, by rfl⟩ : syracuseStep 3201305 = 2400979) B2400979
theorem B2134203 : Blo 2133435 2134203 := bstep (se 1 (by rfl) ⟨1600652, by rfl⟩ : syracuseStep 2134203 = 3201305) B3201305
theorem B3418589 : Blo 2133435 3418589 := bbase (se 3 (by rfl) ⟨640985, by rfl⟩ : syracuseStep 3418589 = 1281971) (by norm_num)
theorem B2279059 : Blo 2133435 2279059 := bstep (se 1 (by rfl) ⟨1709294, by rfl⟩ : syracuseStep 2279059 = 3418589) B3418589
theorem B12154981 : Blo 2133435 12154981 := bstep (se 4 (by rfl) ⟨1139529, by rfl⟩ : syracuseStep 12154981 = 2279059) B2279059
theorem B16206641 : Blo 2133435 16206641 := bstep (se 2 (by rfl) ⟨6077490, by rfl⟩ : syracuseStep 16206641 = 12154981) B12154981
theorem B10804427 : Blo 2133435 10804427 := bstep (se 1 (by rfl) ⟨8103320, by rfl⟩ : syracuseStep 10804427 = 16206641) B16206641
theorem B7202951 : Blo 2133435 7202951 := bstep (se 1 (by rfl) ⟨5402213, by rfl⟩ : syracuseStep 7202951 = 10804427) B10804427
theorem B4801967 : Blo 2133435 4801967 := bstep (se 1 (by rfl) ⟨3601475, by rfl⟩ : syracuseStep 4801967 = 7202951) B7202951
theorem B3201311 : Blo 2133435 3201311 := bstep (se 1 (by rfl) ⟨2400983, by rfl⟩ : syracuseStep 3201311 = 4801967) B4801967
theorem B2134207 : Blo 2133435 2134207 := bstep (se 1 (by rfl) ⟨1600655, by rfl⟩ : syracuseStep 2134207 = 3201311) B3201311
theorem B3201317 : Blo 2133435 3201317 := bbase (se 4 (by rfl) ⟨300123, by rfl⟩ : syracuseStep 3201317 = 600247) (by norm_num)
theorem B2134211 : Blo 2133435 2134211 := bstep (se 1 (by rfl) ⟨1600658, by rfl⟩ : syracuseStep 2134211 = 3201317) B3201317
theorem B2701117 : Blo 2133435 2701117 := bbase (se 3 (by rfl) ⟨506459, by rfl⟩ : syracuseStep 2701117 = 1012919) (by norm_num)
theorem B3601489 : Blo 2133435 3601489 := bstep (se 2 (by rfl) ⟨1350558, by rfl⟩ : syracuseStep 3601489 = 2701117) B2701117
theorem B4801985 : Blo 2133435 4801985 := bstep (se 2 (by rfl) ⟨1800744, by rfl⟩ : syracuseStep 4801985 = 3601489) B3601489
theorem B3201323 : Blo 2133435 3201323 := bstep (se 1 (by rfl) ⟨2400992, by rfl⟩ : syracuseStep 3201323 = 4801985) B4801985
theorem B2134215 : Blo 2133435 2134215 := bstep (se 1 (by rfl) ⟨1600661, by rfl⟩ : syracuseStep 2134215 = 3201323) B3201323
theorem B2400997 : Blo 2133435 2400997 := bbase (se 4 (by rfl) ⟨225093, by rfl⟩ : syracuseStep 2400997 = 450187) (by norm_num)
theorem B3201329 : Blo 2133435 3201329 := bstep (se 2 (by rfl) ⟨1200498, by rfl⟩ : syracuseStep 3201329 = 2400997) B2400997
theorem B2134219 : Blo 2133435 2134219 := bstep (se 1 (by rfl) ⟨1600664, by rfl⟩ : syracuseStep 2134219 = 3201329) B3201329
theorem B7301285 : Blo 2133435 7301285 := bbase (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) (by norm_num)
theorem B4867523 : Blo 2133435 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B3245015 : Blo 2133435 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B2163343 : Blo 2133435 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B2884457 : Blo 2133435 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B7691885 : Blo 2133435 7691885 := bstep (se 3 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 7691885 = 2884457) B2884457
theorem B5127923 : Blo 2133435 5127923 := bstep (se 1 (by rfl) ⟨3845942, by rfl⟩ : syracuseStep 5127923 = 7691885) B7691885
theorem B3418615 : Blo 2133435 3418615 := bstep (se 1 (by rfl) ⟨2563961, by rfl⟩ : syracuseStep 3418615 = 5127923) B5127923
theorem B4558153 : Blo 2133435 4558153 := bstep (se 2 (by rfl) ⟨1709307, by rfl⟩ : syracuseStep 4558153 = 3418615) B3418615
theorem B6077537 : Blo 2133435 6077537 := bstep (se 2 (by rfl) ⟨2279076, by rfl⟩ : syracuseStep 6077537 = 4558153) B4558153
theorem B4051691 : Blo 2133435 4051691 := bstep (se 1 (by rfl) ⟨3038768, by rfl⟩ : syracuseStep 4051691 = 6077537) B6077537
theorem B2701127 : Blo 2133435 2701127 := bstep (se 1 (by rfl) ⟨2025845, by rfl⟩ : syracuseStep 2701127 = 4051691) B4051691
theorem B7203005 : Blo 2133435 7203005 := bstep (se 3 (by rfl) ⟨1350563, by rfl⟩ : syracuseStep 7203005 = 2701127) B2701127
theorem B4802003 : Blo 2133435 4802003 := bstep (se 1 (by rfl) ⟨3601502, by rfl⟩ : syracuseStep 4802003 = 7203005) B7203005
theorem B3201335 : Blo 2133435 3201335 := bstep (se 1 (by rfl) ⟨2401001, by rfl⟩ : syracuseStep 3201335 = 4802003) B4802003
theorem B2134223 : Blo 2133435 2134223 := bstep (se 1 (by rfl) ⟨1600667, by rfl⟩ : syracuseStep 2134223 = 3201335) B3201335
theorem B3201341 : Blo 2133435 3201341 := bbase (se 3 (by rfl) ⟨600251, by rfl⟩ : syracuseStep 3201341 = 1200503) (by norm_num)
theorem B2134227 : Blo 2133435 2134227 := bstep (se 1 (by rfl) ⟨1600670, by rfl⟩ : syracuseStep 2134227 = 3201341) B3201341
theorem B4802021 : Blo 2133435 4802021 := bbase (se 4 (by rfl) ⟨450189, by rfl⟩ : syracuseStep 4802021 = 900379) (by norm_num)
theorem B3201347 : Blo 2133435 3201347 := bstep (se 1 (by rfl) ⟨2401010, by rfl⟩ : syracuseStep 3201347 = 4802021) B4802021
theorem B2134231 : Blo 2133435 2134231 := bstep (se 1 (by rfl) ⟨1600673, by rfl⟩ : syracuseStep 2134231 = 3201347) B3201347
theorem B5402285 : Blo 2133435 5402285 := bbase (se 3 (by rfl) ⟨1012928, by rfl⟩ : syracuseStep 5402285 = 2025857) (by norm_num)
theorem B3601523 : Blo 2133435 3601523 := bstep (se 1 (by rfl) ⟨2701142, by rfl⟩ : syracuseStep 3601523 = 5402285) B5402285
theorem B2401015 : Blo 2133435 2401015 := bstep (se 1 (by rfl) ⟨1800761, by rfl⟩ : syracuseStep 2401015 = 3601523) B3601523
theorem B3201353 : Blo 2133435 3201353 := bstep (se 2 (by rfl) ⟨1200507, by rfl⟩ : syracuseStep 3201353 = 2401015) B2401015
theorem B2134235 : Blo 2133435 2134235 := bstep (se 1 (by rfl) ⟨1600676, by rfl⟩ : syracuseStep 2134235 = 3201353) B3201353
theorem B22202869 : Blo 2133435 22202869 := bbase (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) (by norm_num)
theorem B29603825 : Blo 2133435 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B19735883 : Blo 2133435 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B13157255 : Blo 2133435 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B8771503 : Blo 2133435 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B11695337 : Blo 2133435 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B7796891 : Blo 2133435 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B5197927 : Blo 2133435 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B6930569 : Blo 2133435 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B18481517 : Blo 2133435 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B12321011 : Blo 2133435 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B8214007 : Blo 2133435 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B10952009 : Blo 2133435 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B7301339 : Blo 2133435 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B4867559 : Blo 2133435 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B3245039 : Blo 2133435 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B2163359 : Blo 2133435 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B5768957 : Blo 2133435 5768957 := bstep (se 3 (by rfl) ⟨1081679, by rfl⟩ : syracuseStep 5768957 = 2163359) B2163359
theorem B3845971 : Blo 2133435 3845971 := bstep (se 1 (by rfl) ⟨2884478, by rfl⟩ : syracuseStep 3845971 = 5768957) B5768957
theorem B5127961 : Blo 2133435 5127961 := bstep (se 2 (by rfl) ⟨1922985, by rfl⟩ : syracuseStep 5127961 = 3845971) B3845971
theorem B6837281 : Blo 2133435 6837281 := bstep (se 2 (by rfl) ⟨2563980, by rfl⟩ : syracuseStep 6837281 = 5127961) B5127961
theorem B4558187 : Blo 2133435 4558187 := bstep (se 1 (by rfl) ⟨3418640, by rfl⟩ : syracuseStep 4558187 = 6837281) B6837281
theorem B3038791 : Blo 2133435 3038791 := bstep (se 1 (by rfl) ⟨2279093, by rfl⟩ : syracuseStep 3038791 = 4558187) B4558187
theorem B4051721 : Blo 2133435 4051721 := bstep (se 2 (by rfl) ⟨1519395, by rfl⟩ : syracuseStep 4051721 = 3038791) B3038791
theorem B10804589 : Blo 2133435 10804589 := bstep (se 3 (by rfl) ⟨2025860, by rfl⟩ : syracuseStep 10804589 = 4051721) B4051721
theorem B7203059 : Blo 2133435 7203059 := bstep (se 1 (by rfl) ⟨5402294, by rfl⟩ : syracuseStep 7203059 = 10804589) B10804589
theorem B4802039 : Blo 2133435 4802039 := bstep (se 1 (by rfl) ⟨3601529, by rfl⟩ : syracuseStep 4802039 = 7203059) B7203059
theorem B3201359 : Blo 2133435 3201359 := bstep (se 1 (by rfl) ⟨2401019, by rfl⟩ : syracuseStep 3201359 = 4802039) B4802039
theorem B2134239 : Blo 2133435 2134239 := bstep (se 1 (by rfl) ⟨1600679, by rfl⟩ : syracuseStep 2134239 = 3201359) B3201359
theorem B3201365 : Blo 2133435 3201365 := bbase (se 10 (by rfl) ⟨4689, by rfl⟩ : syracuseStep 3201365 = 9379) (by norm_num)
theorem B2134243 : Blo 2133435 2134243 := bstep (se 1 (by rfl) ⟨1600682, by rfl⟩ : syracuseStep 2134243 = 3201365) B3201365
theorem B6077605 : Blo 2133435 6077605 := bbase (se 4 (by rfl) ⟨569775, by rfl⟩ : syracuseStep 6077605 = 1139551) (by norm_num)
theorem B8103473 : Blo 2133435 8103473 := bstep (se 2 (by rfl) ⟨3038802, by rfl⟩ : syracuseStep 8103473 = 6077605) B6077605
theorem B5402315 : Blo 2133435 5402315 := bstep (se 1 (by rfl) ⟨4051736, by rfl⟩ : syracuseStep 5402315 = 8103473) B8103473
theorem B3601543 : Blo 2133435 3601543 := bstep (se 1 (by rfl) ⟨2701157, by rfl⟩ : syracuseStep 3601543 = 5402315) B5402315
theorem B4802057 : Blo 2133435 4802057 := bstep (se 2 (by rfl) ⟨1800771, by rfl⟩ : syracuseStep 4802057 = 3601543) B3601543
theorem B3201371 : Blo 2133435 3201371 := bstep (se 1 (by rfl) ⟨2401028, by rfl⟩ : syracuseStep 3201371 = 4802057) B4802057
theorem B2134247 : Blo 2133435 2134247 := bstep (se 1 (by rfl) ⟨1600685, by rfl⟩ : syracuseStep 2134247 = 3201371) B3201371
theorem B2401033 : Blo 2133435 2401033 := bbase (se 2 (by rfl) ⟨900387, by rfl⟩ : syracuseStep 2401033 = 1800775) (by norm_num)
theorem B3201377 : Blo 2133435 3201377 := bstep (se 2 (by rfl) ⟨1200516, by rfl⟩ : syracuseStep 3201377 = 2401033) B2401033
theorem B2134251 : Blo 2133435 2134251 := bstep (se 1 (by rfl) ⟨1600688, by rfl⟩ : syracuseStep 2134251 = 3201377) B3201377
theorem B6160549 : Blo 2133435 6160549 := bbase (se 4 (by rfl) ⟨577551, by rfl⟩ : syracuseStep 6160549 = 1155103) (by norm_num)
theorem B8214065 : Blo 2133435 8214065 := bstep (se 2 (by rfl) ⟨3080274, by rfl⟩ : syracuseStep 8214065 = 6160549) B6160549
theorem B5476043 : Blo 2133435 5476043 := bstep (se 1 (by rfl) ⟨4107032, by rfl⟩ : syracuseStep 5476043 = 8214065) B8214065
theorem B14602781 : Blo 2133435 14602781 := bstep (se 3 (by rfl) ⟨2738021, by rfl⟩ : syracuseStep 14602781 = 5476043) B5476043
theorem B9735187 : Blo 2133435 9735187 := bstep (se 1 (by rfl) ⟨7301390, by rfl⟩ : syracuseStep 9735187 = 14602781) B14602781
theorem B12980249 : Blo 2133435 12980249 := bstep (se 2 (by rfl) ⟨4867593, by rfl⟩ : syracuseStep 12980249 = 9735187) B9735187
theorem B8653499 : Blo 2133435 8653499 := bstep (se 1 (by rfl) ⟨6490124, by rfl⟩ : syracuseStep 8653499 = 12980249) B12980249
theorem B5768999 : Blo 2133435 5768999 := bstep (se 1 (by rfl) ⟨4326749, by rfl⟩ : syracuseStep 5768999 = 8653499) B8653499
theorem B3845999 : Blo 2133435 3845999 := bstep (se 1 (by rfl) ⟨2884499, by rfl⟩ : syracuseStep 3845999 = 5768999) B5768999
theorem B10255997 : Blo 2133435 10255997 := bstep (se 3 (by rfl) ⟨1922999, by rfl⟩ : syracuseStep 10255997 = 3845999) B3845999
theorem B27349325 : Blo 2133435 27349325 := bstep (se 3 (by rfl) ⟨5127998, by rfl⟩ : syracuseStep 27349325 = 10255997) B10255997
theorem B18232883 : Blo 2133435 18232883 := bstep (se 1 (by rfl) ⟨13674662, by rfl⟩ : syracuseStep 18232883 = 27349325) B27349325
theorem B12155255 : Blo 2133435 12155255 := bstep (se 1 (by rfl) ⟨9116441, by rfl⟩ : syracuseStep 12155255 = 18232883) B18232883
theorem B8103503 : Blo 2133435 8103503 := bstep (se 1 (by rfl) ⟨6077627, by rfl⟩ : syracuseStep 8103503 = 12155255) B12155255
theorem B5402335 : Blo 2133435 5402335 := bstep (se 1 (by rfl) ⟨4051751, by rfl⟩ : syracuseStep 5402335 = 8103503) B8103503
theorem B7203113 : Blo 2133435 7203113 := bstep (se 2 (by rfl) ⟨2701167, by rfl⟩ : syracuseStep 7203113 = 5402335) B5402335
theorem B4802075 : Blo 2133435 4802075 := bstep (se 1 (by rfl) ⟨3601556, by rfl⟩ : syracuseStep 4802075 = 7203113) B7203113
theorem B3201383 : Blo 2133435 3201383 := bstep (se 1 (by rfl) ⟨2401037, by rfl⟩ : syracuseStep 3201383 = 4802075) B4802075
theorem B2134255 : Blo 2133435 2134255 := bstep (se 1 (by rfl) ⟨1600691, by rfl⟩ : syracuseStep 2134255 = 3201383) B3201383
theorem B3201389 : Blo 2133435 3201389 := bbase (se 3 (by rfl) ⟨600260, by rfl⟩ : syracuseStep 3201389 = 1200521) (by norm_num)
theorem B2134259 : Blo 2133435 2134259 := bstep (se 1 (by rfl) ⟨1600694, by rfl⟩ : syracuseStep 2134259 = 3201389) B3201389
theorem B4802093 : Blo 2133435 4802093 := bbase (se 3 (by rfl) ⟨900392, by rfl⟩ : syracuseStep 4802093 = 1800785) (by norm_num)
theorem B3201395 : Blo 2133435 3201395 := bstep (se 1 (by rfl) ⟨2401046, by rfl⟩ : syracuseStep 3201395 = 4802093) B4802093
theorem B2134263 : Blo 2133435 2134263 := bstep (se 1 (by rfl) ⟨1600697, by rfl⟩ : syracuseStep 2134263 = 3201395) B3201395
theorem B3650717 : Blo 2133435 3650717 := bbase (se 3 (by rfl) ⟨684509, by rfl⟩ : syracuseStep 3650717 = 1369019) (by norm_num)
theorem B2433811 : Blo 2133435 2433811 := bstep (se 1 (by rfl) ⟨1825358, by rfl⟩ : syracuseStep 2433811 = 3650717) B3650717
theorem B3245081 : Blo 2133435 3245081 := bstep (se 2 (by rfl) ⟨1216905, by rfl⟩ : syracuseStep 3245081 = 2433811) B2433811
theorem B8653549 : Blo 2133435 8653549 := bstep (se 3 (by rfl) ⟨1622540, by rfl⟩ : syracuseStep 8653549 = 3245081) B3245081
theorem B11538065 : Blo 2133435 11538065 := bstep (se 2 (by rfl) ⟨4326774, by rfl⟩ : syracuseStep 11538065 = 8653549) B8653549
theorem B30768173 : Blo 2133435 30768173 := bstep (se 3 (by rfl) ⟨5769032, by rfl⟩ : syracuseStep 30768173 = 11538065) B11538065
theorem B20512115 : Blo 2133435 20512115 := bstep (se 1 (by rfl) ⟨15384086, by rfl⟩ : syracuseStep 20512115 = 30768173) B30768173
theorem B13674743 : Blo 2133435 13674743 := bstep (se 1 (by rfl) ⟨10256057, by rfl⟩ : syracuseStep 13674743 = 20512115) B20512115
theorem B9116495 : Blo 2133435 9116495 := bstep (se 1 (by rfl) ⟨6837371, by rfl⟩ : syracuseStep 9116495 = 13674743) B13674743
theorem B6077663 : Blo 2133435 6077663 := bstep (se 1 (by rfl) ⟨4558247, by rfl⟩ : syracuseStep 6077663 = 9116495) B9116495
theorem B4051775 : Blo 2133435 4051775 := bstep (se 1 (by rfl) ⟨3038831, by rfl⟩ : syracuseStep 4051775 = 6077663) B6077663
theorem B2701183 : Blo 2133435 2701183 := bstep (se 1 (by rfl) ⟨2025887, by rfl⟩ : syracuseStep 2701183 = 4051775) B4051775
theorem B3601577 : Blo 2133435 3601577 := bstep (se 2 (by rfl) ⟨1350591, by rfl⟩ : syracuseStep 3601577 = 2701183) B2701183
theorem B2401051 : Blo 2133435 2401051 := bstep (se 1 (by rfl) ⟨1800788, by rfl⟩ : syracuseStep 2401051 = 3601577) B3601577
theorem B3201401 : Blo 2133435 3201401 := bstep (se 2 (by rfl) ⟨1200525, by rfl⟩ : syracuseStep 3201401 = 2401051) B2401051
theorem B2134267 : Blo 2133435 2134267 := bstep (se 1 (by rfl) ⟨1600700, by rfl⟩ : syracuseStep 2134267 = 3201401) B3201401
theorem B5128037 : Blo 2133435 5128037 := bbase (se 4 (by rfl) ⟨480753, by rfl⟩ : syracuseStep 5128037 = 961507) (by norm_num)
theorem B3418691 : Blo 2133435 3418691 := bstep (se 1 (by rfl) ⟨2564018, by rfl⟩ : syracuseStep 3418691 = 5128037) B5128037
theorem B36466037 : Blo 2133435 36466037 := bstep (se 5 (by rfl) ⟨1709345, by rfl⟩ : syracuseStep 36466037 = 3418691) B3418691
theorem B24310691 : Blo 2133435 24310691 := bstep (se 1 (by rfl) ⟨18233018, by rfl⟩ : syracuseStep 24310691 = 36466037) B36466037
theorem B16207127 : Blo 2133435 16207127 := bstep (se 1 (by rfl) ⟨12155345, by rfl⟩ : syracuseStep 16207127 = 24310691) B24310691
theorem B10804751 : Blo 2133435 10804751 := bstep (se 1 (by rfl) ⟨8103563, by rfl⟩ : syracuseStep 10804751 = 16207127) B16207127
theorem B7203167 : Blo 2133435 7203167 := bstep (se 1 (by rfl) ⟨5402375, by rfl⟩ : syracuseStep 7203167 = 10804751) B10804751
theorem B4802111 : Blo 2133435 4802111 := bstep (se 1 (by rfl) ⟨3601583, by rfl⟩ : syracuseStep 4802111 = 7203167) B7203167
theorem B3201407 : Blo 2133435 3201407 := bstep (se 1 (by rfl) ⟨2401055, by rfl⟩ : syracuseStep 3201407 = 4802111) B4802111
theorem B2134271 : Blo 2133435 2134271 := bstep (se 1 (by rfl) ⟨1600703, by rfl⟩ : syracuseStep 2134271 = 3201407) B3201407
theorem B3201413 : Blo 2133435 3201413 := bbase (se 4 (by rfl) ⟨300132, by rfl⟩ : syracuseStep 3201413 = 600265) (by norm_num)
theorem B2134275 : Blo 2133435 2134275 := bstep (se 1 (by rfl) ⟨1600706, by rfl⟩ : syracuseStep 2134275 = 3201413) B3201413
theorem B3601597 : Blo 2133435 3601597 := bbase (se 3 (by rfl) ⟨675299, by rfl⟩ : syracuseStep 3601597 = 1350599) (by norm_num)
theorem B4802129 : Blo 2133435 4802129 := bstep (se 2 (by rfl) ⟨1800798, by rfl⟩ : syracuseStep 4802129 = 3601597) B3601597
theorem B3201419 : Blo 2133435 3201419 := bstep (se 1 (by rfl) ⟨2401064, by rfl⟩ : syracuseStep 3201419 = 4802129) B4802129
theorem B2134279 : Blo 2133435 2134279 := bstep (se 1 (by rfl) ⟨1600709, by rfl⟩ : syracuseStep 2134279 = 3201419) B3201419
theorem B2401069 : Blo 2133435 2401069 := bbase (se 3 (by rfl) ⟨450200, by rfl⟩ : syracuseStep 2401069 = 900401) (by norm_num)
theorem B3201425 : Blo 2133435 3201425 := bstep (se 2 (by rfl) ⟨1200534, by rfl⟩ : syracuseStep 3201425 = 2401069) B2401069
theorem B2134283 : Blo 2133435 2134283 := bstep (se 1 (by rfl) ⟨1600712, by rfl⟩ : syracuseStep 2134283 = 3201425) B3201425
theorem B7203221 : Blo 2133435 7203221 := bbase (se 6 (by rfl) ⟨168825, by rfl⟩ : syracuseStep 7203221 = 337651) (by norm_num)
theorem B4802147 : Blo 2133435 4802147 := bstep (se 1 (by rfl) ⟨3601610, by rfl⟩ : syracuseStep 4802147 = 7203221) B7203221
theorem B3201431 : Blo 2133435 3201431 := bstep (se 1 (by rfl) ⟨2401073, by rfl⟩ : syracuseStep 3201431 = 4802147) B4802147
theorem B2134287 : Blo 2133435 2134287 := bstep (se 1 (by rfl) ⟨1600715, by rfl⟩ : syracuseStep 2134287 = 3201431) B3201431
theorem B3201437 : Blo 2133435 3201437 := bbase (se 3 (by rfl) ⟨600269, by rfl⟩ : syracuseStep 3201437 = 1200539) (by norm_num)
theorem B2134291 : Blo 2133435 2134291 := bstep (se 1 (by rfl) ⟨1600718, by rfl⟩ : syracuseStep 2134291 = 3201437) B3201437
theorem B4802165 : Blo 2133435 4802165 := bbase (se 5 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 4802165 = 450203) (by norm_num)
theorem B3201443 : Blo 2133435 3201443 := bstep (se 1 (by rfl) ⟨2401082, by rfl⟩ : syracuseStep 3201443 = 4802165) B4802165
theorem B2134295 : Blo 2133435 2134295 := bstep (se 1 (by rfl) ⟨1600721, by rfl⟩ : syracuseStep 2134295 = 3201443) B3201443
theorem B3289405 : Blo 2133435 3289405 := bbase (se 3 (by rfl) ⟨616763, by rfl⟩ : syracuseStep 3289405 = 1233527) (by norm_num)
theorem B4385873 : Blo 2133435 4385873 := bstep (se 2 (by rfl) ⟨1644702, by rfl⟩ : syracuseStep 4385873 = 3289405) B3289405
theorem B11695661 : Blo 2133435 11695661 := bstep (se 3 (by rfl) ⟨2192936, by rfl⟩ : syracuseStep 11695661 = 4385873) B4385873
theorem B7797107 : Blo 2133435 7797107 := bstep (se 1 (by rfl) ⟨5847830, by rfl⟩ : syracuseStep 7797107 = 11695661) B11695661
theorem B20792285 : Blo 2133435 20792285 := bstep (se 3 (by rfl) ⟨3898553, by rfl⟩ : syracuseStep 20792285 = 7797107) B7797107
theorem B13861523 : Blo 2133435 13861523 := bstep (se 1 (by rfl) ⟨10396142, by rfl⟩ : syracuseStep 13861523 = 20792285) B20792285
theorem B9241015 : Blo 2133435 9241015 := bstep (se 1 (by rfl) ⟨6930761, by rfl⟩ : syracuseStep 9241015 = 13861523) B13861523
theorem B12321353 : Blo 2133435 12321353 := bstep (se 2 (by rfl) ⟨4620507, by rfl⟩ : syracuseStep 12321353 = 9241015) B9241015
theorem B32856941 : Blo 2133435 32856941 := bstep (se 3 (by rfl) ⟨6160676, by rfl⟩ : syracuseStep 32856941 = 12321353) B12321353
theorem B21904627 : Blo 2133435 21904627 := bstep (se 1 (by rfl) ⟨16428470, by rfl⟩ : syracuseStep 21904627 = 32856941) B32856941
theorem B29206169 : Blo 2133435 29206169 := bstep (se 2 (by rfl) ⟨10952313, by rfl⟩ : syracuseStep 29206169 = 21904627) B21904627
theorem B19470779 : Blo 2133435 19470779 := bstep (se 1 (by rfl) ⟨14603084, by rfl⟩ : syracuseStep 19470779 = 29206169) B29206169
theorem B12980519 : Blo 2133435 12980519 := bstep (se 1 (by rfl) ⟨9735389, by rfl⟩ : syracuseStep 12980519 = 19470779) B19470779
theorem B8653679 : Blo 2133435 8653679 := bstep (se 1 (by rfl) ⟨6490259, by rfl⟩ : syracuseStep 8653679 = 12980519) B12980519
theorem B5769119 : Blo 2133435 5769119 := bstep (se 1 (by rfl) ⟨4326839, by rfl⟩ : syracuseStep 5769119 = 8653679) B8653679
theorem B3846079 : Blo 2133435 3846079 := bstep (se 1 (by rfl) ⟨2884559, by rfl⟩ : syracuseStep 3846079 = 5769119) B5769119
theorem B5128105 : Blo 2133435 5128105 := bstep (se 2 (by rfl) ⟨1923039, by rfl⟩ : syracuseStep 5128105 = 3846079) B3846079
theorem B6837473 : Blo 2133435 6837473 := bstep (se 2 (by rfl) ⟨2564052, by rfl⟩ : syracuseStep 6837473 = 5128105) B5128105
theorem B18233261 : Blo 2133435 18233261 := bstep (se 3 (by rfl) ⟨3418736, by rfl⟩ : syracuseStep 18233261 = 6837473) B6837473
theorem B12155507 : Blo 2133435 12155507 := bstep (se 1 (by rfl) ⟨9116630, by rfl⟩ : syracuseStep 12155507 = 18233261) B18233261
theorem B8103671 : Blo 2133435 8103671 := bstep (se 1 (by rfl) ⟨6077753, by rfl⟩ : syracuseStep 8103671 = 12155507) B12155507
theorem B5402447 : Blo 2133435 5402447 := bstep (se 1 (by rfl) ⟨4051835, by rfl⟩ : syracuseStep 5402447 = 8103671) B8103671
theorem B3601631 : Blo 2133435 3601631 := bstep (se 1 (by rfl) ⟨2701223, by rfl⟩ : syracuseStep 3601631 = 5402447) B5402447
theorem B2401087 : Blo 2133435 2401087 := bstep (se 1 (by rfl) ⟨1800815, by rfl⟩ : syracuseStep 2401087 = 3601631) B3601631
theorem B3201449 : Blo 2133435 3201449 := bstep (se 2 (by rfl) ⟨1200543, by rfl⟩ : syracuseStep 3201449 = 2401087) B2401087
theorem B2134299 : Blo 2133435 2134299 := bstep (se 1 (by rfl) ⟨1600724, by rfl⟩ : syracuseStep 2134299 = 3201449) B3201449
theorem B8103685 : Blo 2133435 8103685 := bbase (se 4 (by rfl) ⟨759720, by rfl⟩ : syracuseStep 8103685 = 1519441) (by norm_num)
theorem B10804913 : Blo 2133435 10804913 := bstep (se 2 (by rfl) ⟨4051842, by rfl⟩ : syracuseStep 10804913 = 8103685) B8103685
theorem B7203275 : Blo 2133435 7203275 := bstep (se 1 (by rfl) ⟨5402456, by rfl⟩ : syracuseStep 7203275 = 10804913) B10804913
theorem B4802183 : Blo 2133435 4802183 := bstep (se 1 (by rfl) ⟨3601637, by rfl⟩ : syracuseStep 4802183 = 7203275) B7203275
theorem B3201455 : Blo 2133435 3201455 := bstep (se 1 (by rfl) ⟨2401091, by rfl⟩ : syracuseStep 3201455 = 4802183) B4802183
theorem B2134303 : Blo 2133435 2134303 := bstep (se 1 (by rfl) ⟨1600727, by rfl⟩ : syracuseStep 2134303 = 3201455) B3201455
theorem B3201461 : Blo 2133435 3201461 := bbase (se 5 (by rfl) ⟨150068, by rfl⟩ : syracuseStep 3201461 = 300137) (by norm_num)
theorem B2134307 : Blo 2133435 2134307 := bstep (se 1 (by rfl) ⟨1600730, by rfl⟩ : syracuseStep 2134307 = 3201461) B3201461
theorem B5402477 : Blo 2133435 5402477 := bbase (se 3 (by rfl) ⟨1012964, by rfl⟩ : syracuseStep 5402477 = 2025929) (by norm_num)
theorem B3601651 : Blo 2133435 3601651 := bstep (se 1 (by rfl) ⟨2701238, by rfl⟩ : syracuseStep 3601651 = 5402477) B5402477
theorem B4802201 : Blo 2133435 4802201 := bstep (se 2 (by rfl) ⟨1800825, by rfl⟩ : syracuseStep 4802201 = 3601651) B3601651
theorem B3201467 : Blo 2133435 3201467 := bstep (se 1 (by rfl) ⟨2401100, by rfl⟩ : syracuseStep 3201467 = 4802201) B4802201
theorem B2134311 : Blo 2133435 2134311 := bstep (se 1 (by rfl) ⟨1600733, by rfl⟩ : syracuseStep 2134311 = 3201467) B3201467
theorem B2401105 : Blo 2133435 2401105 := bbase (se 2 (by rfl) ⟨900414, by rfl⟩ : syracuseStep 2401105 = 1800829) (by norm_num)
theorem B3201473 : Blo 2133435 3201473 := bstep (se 2 (by rfl) ⟨1200552, by rfl⟩ : syracuseStep 3201473 = 2401105) B2401105
theorem B2134315 : Blo 2133435 2134315 := bstep (se 1 (by rfl) ⟨1600736, by rfl⟩ : syracuseStep 2134315 = 3201473) B3201473
theorem B2564077 : Blo 2133435 2564077 := bbase (se 3 (by rfl) ⟨480764, by rfl⟩ : syracuseStep 2564077 = 961529) (by norm_num)
theorem B3418769 : Blo 2133435 3418769 := bstep (se 2 (by rfl) ⟨1282038, by rfl⟩ : syracuseStep 3418769 = 2564077) B2564077
theorem B2279179 : Blo 2133435 2279179 := bstep (se 1 (by rfl) ⟨1709384, by rfl⟩ : syracuseStep 2279179 = 3418769) B3418769
theorem B3038905 : Blo 2133435 3038905 := bstep (se 2 (by rfl) ⟨1139589, by rfl⟩ : syracuseStep 3038905 = 2279179) B2279179
theorem B4051873 : Blo 2133435 4051873 := bstep (se 2 (by rfl) ⟨1519452, by rfl⟩ : syracuseStep 4051873 = 3038905) B3038905
theorem B5402497 : Blo 2133435 5402497 := bstep (se 2 (by rfl) ⟨2025936, by rfl⟩ : syracuseStep 5402497 = 4051873) B4051873
theorem B7203329 : Blo 2133435 7203329 := bstep (se 2 (by rfl) ⟨2701248, by rfl⟩ : syracuseStep 7203329 = 5402497) B5402497
theorem B4802219 : Blo 2133435 4802219 := bstep (se 1 (by rfl) ⟨3601664, by rfl⟩ : syracuseStep 4802219 = 7203329) B7203329
theorem B3201479 : Blo 2133435 3201479 := bstep (se 1 (by rfl) ⟨2401109, by rfl⟩ : syracuseStep 3201479 = 4802219) B4802219
theorem B2134319 : Blo 2133435 2134319 := bstep (se 1 (by rfl) ⟨1600739, by rfl⟩ : syracuseStep 2134319 = 3201479) B3201479
theorem B3201485 : Blo 2133435 3201485 := bbase (se 3 (by rfl) ⟨600278, by rfl⟩ : syracuseStep 3201485 = 1200557) (by norm_num)
theorem B2134323 : Blo 2133435 2134323 := bstep (se 1 (by rfl) ⟨1600742, by rfl⟩ : syracuseStep 2134323 = 3201485) B3201485
theorem B4802237 : Blo 2133435 4802237 := bbase (se 3 (by rfl) ⟨900419, by rfl⟩ : syracuseStep 4802237 = 1800839) (by norm_num)
theorem B3201491 : Blo 2133435 3201491 := bstep (se 1 (by rfl) ⟨2401118, by rfl⟩ : syracuseStep 3201491 = 4802237) B4802237
theorem B2134327 : Blo 2133435 2134327 := bstep (se 1 (by rfl) ⟨1600745, by rfl⟩ : syracuseStep 2134327 = 3201491) B3201491
theorem B3601685 : Blo 2133435 3601685 := bbase (se 6 (by rfl) ⟨84414, by rfl⟩ : syracuseStep 3601685 = 168829) (by norm_num)
theorem B2401123 : Blo 2133435 2401123 := bstep (se 1 (by rfl) ⟨1800842, by rfl⟩ : syracuseStep 2401123 = 3601685) B3601685
theorem B3201497 : Blo 2133435 3201497 := bstep (se 2 (by rfl) ⟨1200561, by rfl⟩ : syracuseStep 3201497 = 2401123) B2401123
theorem B2134331 : Blo 2133435 2134331 := bstep (se 1 (by rfl) ⟨1600748, by rfl⟩ : syracuseStep 2134331 = 3201497) B3201497
theorem B4934189 : Blo 2133435 4934189 := bbase (se 3 (by rfl) ⟨925160, by rfl⟩ : syracuseStep 4934189 = 1850321) (by norm_num)
theorem B3289459 : Blo 2133435 3289459 := bstep (se 1 (by rfl) ⟨2467094, by rfl⟩ : syracuseStep 3289459 = 4934189) B4934189
theorem B4385945 : Blo 2133435 4385945 := bstep (se 2 (by rfl) ⟨1644729, by rfl⟩ : syracuseStep 4385945 = 3289459) B3289459
theorem B11695853 : Blo 2133435 11695853 := bstep (se 3 (by rfl) ⟨2192972, by rfl⟩ : syracuseStep 11695853 = 4385945) B4385945
theorem B31188941 : Blo 2133435 31188941 := bstep (se 3 (by rfl) ⟨5847926, by rfl⟩ : syracuseStep 31188941 = 11695853) B11695853
theorem B20792627 : Blo 2133435 20792627 := bstep (se 1 (by rfl) ⟨15594470, by rfl⟩ : syracuseStep 20792627 = 31188941) B31188941
theorem B13861751 : Blo 2133435 13861751 := bstep (se 1 (by rfl) ⟨10396313, by rfl⟩ : syracuseStep 13861751 = 20792627) B20792627
theorem B36964669 : Blo 2133435 36964669 := bstep (se 3 (by rfl) ⟨6930875, by rfl⟩ : syracuseStep 36964669 = 13861751) B13861751
theorem B49286225 : Blo 2133435 49286225 := bstep (se 2 (by rfl) ⟨18482334, by rfl⟩ : syracuseStep 49286225 = 36964669) B36964669
theorem B32857483 : Blo 2133435 32857483 := bstep (se 1 (by rfl) ⟨24643112, by rfl⟩ : syracuseStep 32857483 = 49286225) B49286225
theorem B43809977 : Blo 2133435 43809977 := bstep (se 2 (by rfl) ⟨16428741, by rfl⟩ : syracuseStep 43809977 = 32857483) B32857483
theorem B29206651 : Blo 2133435 29206651 := bstep (se 1 (by rfl) ⟨21904988, by rfl⟩ : syracuseStep 29206651 = 43809977) B43809977
theorem B38942201 : Blo 2133435 38942201 := bstep (se 2 (by rfl) ⟨14603325, by rfl⟩ : syracuseStep 38942201 = 29206651) B29206651
theorem B25961467 : Blo 2133435 25961467 := bstep (se 1 (by rfl) ⟨19471100, by rfl⟩ : syracuseStep 25961467 = 38942201) B38942201
theorem B34615289 : Blo 2133435 34615289 := bstep (se 2 (by rfl) ⟨12980733, by rfl⟩ : syracuseStep 34615289 = 25961467) B25961467
theorem B23076859 : Blo 2133435 23076859 := bstep (se 1 (by rfl) ⟨17307644, by rfl⟩ : syracuseStep 23076859 = 34615289) B34615289
theorem B30769145 : Blo 2133435 30769145 := bstep (se 2 (by rfl) ⟨11538429, by rfl⟩ : syracuseStep 30769145 = 23076859) B23076859
theorem B20512763 : Blo 2133435 20512763 := bstep (se 1 (by rfl) ⟨15384572, by rfl⟩ : syracuseStep 20512763 = 30769145) B30769145
theorem B13675175 : Blo 2133435 13675175 := bstep (se 1 (by rfl) ⟨10256381, by rfl⟩ : syracuseStep 13675175 = 20512763) B20512763
theorem B9116783 : Blo 2133435 9116783 := bstep (se 1 (by rfl) ⟨6837587, by rfl⟩ : syracuseStep 9116783 = 13675175) B13675175
theorem B6077855 : Blo 2133435 6077855 := bstep (se 1 (by rfl) ⟨4558391, by rfl⟩ : syracuseStep 6077855 = 9116783) B9116783
theorem B16207613 : Blo 2133435 16207613 := bstep (se 3 (by rfl) ⟨3038927, by rfl⟩ : syracuseStep 16207613 = 6077855) B6077855
theorem B10805075 : Blo 2133435 10805075 := bstep (se 1 (by rfl) ⟨8103806, by rfl⟩ : syracuseStep 10805075 = 16207613) B16207613
theorem B7203383 : Blo 2133435 7203383 := bstep (se 1 (by rfl) ⟨5402537, by rfl⟩ : syracuseStep 7203383 = 10805075) B10805075
theorem B4802255 : Blo 2133435 4802255 := bstep (se 1 (by rfl) ⟨3601691, by rfl⟩ : syracuseStep 4802255 = 7203383) B7203383
theorem B3201503 : Blo 2133435 3201503 := bstep (se 1 (by rfl) ⟨2401127, by rfl⟩ : syracuseStep 3201503 = 4802255) B4802255
theorem B2134335 : Blo 2133435 2134335 := bstep (se 1 (by rfl) ⟨1600751, by rfl⟩ : syracuseStep 2134335 = 3201503) B3201503
theorem B3201509 : Blo 2133435 3201509 := bbase (se 4 (by rfl) ⟨300141, by rfl⟩ : syracuseStep 3201509 = 600283) (by norm_num)
theorem B2134339 : Blo 2133435 2134339 := bstep (se 1 (by rfl) ⟨1600754, by rfl⟩ : syracuseStep 2134339 = 3201509) B3201509
theorem B3245197 : Blo 2133435 3245197 := bbase (se 3 (by rfl) ⟨608474, by rfl⟩ : syracuseStep 3245197 = 1216949) (by norm_num)
theorem B4326929 : Blo 2133435 4326929 := bstep (se 2 (by rfl) ⟨1622598, by rfl⟩ : syracuseStep 4326929 = 3245197) B3245197
theorem B2884619 : Blo 2133435 2884619 := bstep (se 1 (by rfl) ⟨2163464, by rfl⟩ : syracuseStep 2884619 = 4326929) B4326929
theorem B7692317 : Blo 2133435 7692317 := bstep (se 3 (by rfl) ⟨1442309, by rfl⟩ : syracuseStep 7692317 = 2884619) B2884619
theorem B5128211 : Blo 2133435 5128211 := bstep (se 1 (by rfl) ⟨3846158, by rfl⟩ : syracuseStep 5128211 = 7692317) B7692317
theorem B13675229 : Blo 2133435 13675229 := bstep (se 3 (by rfl) ⟨2564105, by rfl⟩ : syracuseStep 13675229 = 5128211) B5128211
theorem B9116819 : Blo 2133435 9116819 := bstep (se 1 (by rfl) ⟨6837614, by rfl⟩ : syracuseStep 9116819 = 13675229) B13675229
theorem B6077879 : Blo 2133435 6077879 := bstep (se 1 (by rfl) ⟨4558409, by rfl⟩ : syracuseStep 6077879 = 9116819) B9116819
theorem B4051919 : Blo 2133435 4051919 := bstep (se 1 (by rfl) ⟨3038939, by rfl⟩ : syracuseStep 4051919 = 6077879) B6077879
theorem B2701279 : Blo 2133435 2701279 := bstep (se 1 (by rfl) ⟨2025959, by rfl⟩ : syracuseStep 2701279 = 4051919) B4051919
theorem B3601705 : Blo 2133435 3601705 := bstep (se 2 (by rfl) ⟨1350639, by rfl⟩ : syracuseStep 3601705 = 2701279) B2701279
theorem B4802273 : Blo 2133435 4802273 := bstep (se 2 (by rfl) ⟨1800852, by rfl⟩ : syracuseStep 4802273 = 3601705) B3601705
theorem B3201515 : Blo 2133435 3201515 := bstep (se 1 (by rfl) ⟨2401136, by rfl⟩ : syracuseStep 3201515 = 4802273) B4802273
theorem B2134343 : Blo 2133435 2134343 := bstep (se 1 (by rfl) ⟨1600757, by rfl⟩ : syracuseStep 2134343 = 3201515) B3201515
theorem B2401141 : Blo 2133435 2401141 := bbase (se 5 (by rfl) ⟨112553, by rfl⟩ : syracuseStep 2401141 = 225107) (by norm_num)
theorem B3201521 : Blo 2133435 3201521 := bstep (se 2 (by rfl) ⟨1200570, by rfl⟩ : syracuseStep 3201521 = 2401141) B2401141
theorem B2134347 : Blo 2133435 2134347 := bstep (se 1 (by rfl) ⟨1600760, by rfl⟩ : syracuseStep 2134347 = 3201521) B3201521
theorem B2701289 : Blo 2133435 2701289 := bbase (se 2 (by rfl) ⟨1012983, by rfl⟩ : syracuseStep 2701289 = 2025967) (by norm_num)
theorem B7203437 : Blo 2133435 7203437 := bstep (se 3 (by rfl) ⟨1350644, by rfl⟩ : syracuseStep 7203437 = 2701289) B2701289
theorem B4802291 : Blo 2133435 4802291 := bstep (se 1 (by rfl) ⟨3601718, by rfl⟩ : syracuseStep 4802291 = 7203437) B7203437
theorem B3201527 : Blo 2133435 3201527 := bstep (se 1 (by rfl) ⟨2401145, by rfl⟩ : syracuseStep 3201527 = 4802291) B4802291
theorem B2134351 : Blo 2133435 2134351 := bstep (se 1 (by rfl) ⟨1600763, by rfl⟩ : syracuseStep 2134351 = 3201527) B3201527
theorem B3201533 : Blo 2133435 3201533 := bbase (se 3 (by rfl) ⟨600287, by rfl⟩ : syracuseStep 3201533 = 1200575) (by norm_num)
theorem B2134355 : Blo 2133435 2134355 := bstep (se 1 (by rfl) ⟨1600766, by rfl⟩ : syracuseStep 2134355 = 3201533) B3201533
theorem B4802309 : Blo 2133435 4802309 := bbase (se 4 (by rfl) ⟨450216, by rfl⟩ : syracuseStep 4802309 = 900433) (by norm_num)
theorem B3201539 : Blo 2133435 3201539 := bstep (se 1 (by rfl) ⟨2401154, by rfl⟩ : syracuseStep 3201539 = 4802309) B4802309
theorem B2134359 : Blo 2133435 2134359 := bstep (se 1 (by rfl) ⟨1600769, by rfl⟩ : syracuseStep 2134359 = 3201539) B3201539
theorem B4051957 : Blo 2133435 4051957 := bbase (se 5 (by rfl) ⟨189935, by rfl⟩ : syracuseStep 4051957 = 379871) (by norm_num)
theorem B5402609 : Blo 2133435 5402609 := bstep (se 2 (by rfl) ⟨2025978, by rfl⟩ : syracuseStep 5402609 = 4051957) B4051957
theorem B3601739 : Blo 2133435 3601739 := bstep (se 1 (by rfl) ⟨2701304, by rfl⟩ : syracuseStep 3601739 = 5402609) B5402609
theorem B2401159 : Blo 2133435 2401159 := bstep (se 1 (by rfl) ⟨1800869, by rfl⟩ : syracuseStep 2401159 = 3601739) B3601739
theorem B3201545 : Blo 2133435 3201545 := bstep (se 2 (by rfl) ⟨1200579, by rfl⟩ : syracuseStep 3201545 = 2401159) B2401159
theorem B2134363 : Blo 2133435 2134363 := bstep (se 1 (by rfl) ⟨1600772, by rfl⟩ : syracuseStep 2134363 = 3201545) B3201545
theorem B10805237 : Blo 2133435 10805237 := bbase (se 5 (by rfl) ⟨506495, by rfl⟩ : syracuseStep 10805237 = 1012991) (by norm_num)
theorem B7203491 : Blo 2133435 7203491 := bstep (se 1 (by rfl) ⟨5402618, by rfl⟩ : syracuseStep 7203491 = 10805237) B10805237
theorem B4802327 : Blo 2133435 4802327 := bstep (se 1 (by rfl) ⟨3601745, by rfl⟩ : syracuseStep 4802327 = 7203491) B7203491
theorem B3201551 : Blo 2133435 3201551 := bstep (se 1 (by rfl) ⟨2401163, by rfl⟩ : syracuseStep 3201551 = 4802327) B4802327
theorem B2134367 : Blo 2133435 2134367 := bstep (se 1 (by rfl) ⟨1600775, by rfl⟩ : syracuseStep 2134367 = 3201551) B3201551
theorem B3201557 : Blo 2133435 3201557 := bbase (se 6 (by rfl) ⟨75036, by rfl⟩ : syracuseStep 3201557 = 150073) (by norm_num)
theorem B2134371 : Blo 2133435 2134371 := bstep (se 1 (by rfl) ⟨1600778, by rfl⟩ : syracuseStep 2134371 = 3201557) B3201557
theorem B18233909 : Blo 2133435 18233909 := bbase (se 5 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 18233909 = 1709429) (by norm_num)
theorem B12155939 : Blo 2133435 12155939 := bstep (se 1 (by rfl) ⟨9116954, by rfl⟩ : syracuseStep 12155939 = 18233909) B18233909
theorem B8103959 : Blo 2133435 8103959 := bstep (se 1 (by rfl) ⟨6077969, by rfl⟩ : syracuseStep 8103959 = 12155939) B12155939
theorem B5402639 : Blo 2133435 5402639 := bstep (se 1 (by rfl) ⟨4051979, by rfl⟩ : syracuseStep 5402639 = 8103959) B8103959
theorem B3601759 : Blo 2133435 3601759 := bstep (se 1 (by rfl) ⟨2701319, by rfl⟩ : syracuseStep 3601759 = 5402639) B5402639
theorem B4802345 : Blo 2133435 4802345 := bstep (se 2 (by rfl) ⟨1800879, by rfl⟩ : syracuseStep 4802345 = 3601759) B3601759
theorem B3201563 : Blo 2133435 3201563 := bstep (se 1 (by rfl) ⟨2401172, by rfl⟩ : syracuseStep 3201563 = 4802345) B4802345
theorem B2134375 : Blo 2133435 2134375 := bstep (se 1 (by rfl) ⟨1600781, by rfl⟩ : syracuseStep 2134375 = 3201563) B3201563
theorem B2401177 : Blo 2133435 2401177 := bbase (se 2 (by rfl) ⟨900441, by rfl⟩ : syracuseStep 2401177 = 1800883) (by norm_num)
theorem B3201569 : Blo 2133435 3201569 := bstep (se 2 (by rfl) ⟨1200588, by rfl⟩ : syracuseStep 3201569 = 2401177) B2401177
theorem B2134379 : Blo 2133435 2134379 := bstep (se 1 (by rfl) ⟨1600784, by rfl⟩ : syracuseStep 2134379 = 3201569) B3201569
theorem B8103989 : Blo 2133435 8103989 := bbase (se 5 (by rfl) ⟨379874, by rfl⟩ : syracuseStep 8103989 = 759749) (by norm_num)
theorem B5402659 : Blo 2133435 5402659 := bstep (se 1 (by rfl) ⟨4051994, by rfl⟩ : syracuseStep 5402659 = 8103989) B8103989
theorem B7203545 : Blo 2133435 7203545 := bstep (se 2 (by rfl) ⟨2701329, by rfl⟩ : syracuseStep 7203545 = 5402659) B5402659
theorem B4802363 : Blo 2133435 4802363 := bstep (se 1 (by rfl) ⟨3601772, by rfl⟩ : syracuseStep 4802363 = 7203545) B7203545
theorem B3201575 : Blo 2133435 3201575 := bstep (se 1 (by rfl) ⟨2401181, by rfl⟩ : syracuseStep 3201575 = 4802363) B4802363
theorem B2134383 : Blo 2133435 2134383 := bstep (se 1 (by rfl) ⟨1600787, by rfl⟩ : syracuseStep 2134383 = 3201575) B3201575
theorem B3201581 : Blo 2133435 3201581 := bbase (se 3 (by rfl) ⟨600296, by rfl⟩ : syracuseStep 3201581 = 1200593) (by norm_num)
theorem B2134387 : Blo 2133435 2134387 := bstep (se 1 (by rfl) ⟨1600790, by rfl⟩ : syracuseStep 2134387 = 3201581) B3201581
theorem B4802381 : Blo 2133435 4802381 := bbase (se 3 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 4802381 = 1800893) (by norm_num)
theorem B3201587 : Blo 2133435 3201587 := bstep (se 1 (by rfl) ⟨2401190, by rfl⟩ : syracuseStep 3201587 = 4802381) B4802381
theorem B2134391 : Blo 2133435 2134391 := bstep (se 1 (by rfl) ⟨1600793, by rfl⟩ : syracuseStep 2134391 = 3201587) B3201587
theorem B2701345 : Blo 2133435 2701345 := bbase (se 2 (by rfl) ⟨1013004, by rfl⟩ : syracuseStep 2701345 = 2026009) (by norm_num)
theorem B3601793 : Blo 2133435 3601793 := bstep (se 2 (by rfl) ⟨1350672, by rfl⟩ : syracuseStep 3601793 = 2701345) B2701345
theorem B2401195 : Blo 2133435 2401195 := bstep (se 1 (by rfl) ⟨1800896, by rfl⟩ : syracuseStep 2401195 = 3601793) B3601793
theorem B3201593 : Blo 2133435 3201593 := bstep (se 2 (by rfl) ⟨1200597, by rfl⟩ : syracuseStep 3201593 = 2401195) B2401195
theorem B2134395 : Blo 2133435 2134395 := bstep (se 1 (by rfl) ⟨1600796, by rfl⟩ : syracuseStep 2134395 = 3201593) B3201593
theorem B24312149 : Blo 2133435 24312149 := bbase (se 10 (by rfl) ⟨35613, by rfl⟩ : syracuseStep 24312149 = 71227) (by norm_num)
theorem B16208099 : Blo 2133435 16208099 := bstep (se 1 (by rfl) ⟨12156074, by rfl⟩ : syracuseStep 16208099 = 24312149) B24312149
theorem B10805399 : Blo 2133435 10805399 := bstep (se 1 (by rfl) ⟨8104049, by rfl⟩ : syracuseStep 10805399 = 16208099) B16208099
theorem B7203599 : Blo 2133435 7203599 := bstep (se 1 (by rfl) ⟨5402699, by rfl⟩ : syracuseStep 7203599 = 10805399) B10805399
theorem B4802399 : Blo 2133435 4802399 := bstep (se 1 (by rfl) ⟨3601799, by rfl⟩ : syracuseStep 4802399 = 7203599) B7203599
theorem B3201599 : Blo 2133435 3201599 := bstep (se 1 (by rfl) ⟨2401199, by rfl⟩ : syracuseStep 3201599 = 4802399) B4802399
theorem B2134399 : Blo 2133435 2134399 := bstep (se 1 (by rfl) ⟨1600799, by rfl⟩ : syracuseStep 2134399 = 3201599) B3201599
theorem B3201605 : Blo 2133435 3201605 := bbase (se 4 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 3201605 = 600301) (by norm_num)
theorem B2134403 : Blo 2133435 2134403 := bstep (se 1 (by rfl) ⟨1600802, by rfl⟩ : syracuseStep 2134403 = 3201605) B3201605
theorem B3601813 : Blo 2133435 3601813 := bbase (se 6 (by rfl) ⟨84417, by rfl⟩ : syracuseStep 3601813 = 168835) (by norm_num)
theorem B4802417 : Blo 2133435 4802417 := bstep (se 2 (by rfl) ⟨1800906, by rfl⟩ : syracuseStep 4802417 = 3601813) B3601813
theorem B3201611 : Blo 2133435 3201611 := bstep (se 1 (by rfl) ⟨2401208, by rfl⟩ : syracuseStep 3201611 = 4802417) B4802417
theorem B2134407 : Blo 2133435 2134407 := bstep (se 1 (by rfl) ⟨1600805, by rfl⟩ : syracuseStep 2134407 = 3201611) B3201611
theorem B2401213 : Blo 2133435 2401213 := bbase (se 3 (by rfl) ⟨450227, by rfl⟩ : syracuseStep 2401213 = 900455) (by norm_num)
theorem B3201617 : Blo 2133435 3201617 := bstep (se 2 (by rfl) ⟨1200606, by rfl⟩ : syracuseStep 3201617 = 2401213) B2401213
theorem B2134411 : Blo 2133435 2134411 := bstep (se 1 (by rfl) ⟨1600808, by rfl⟩ : syracuseStep 2134411 = 3201617) B3201617
theorem B7203653 : Blo 2133435 7203653 := bbase (se 4 (by rfl) ⟨675342, by rfl⟩ : syracuseStep 7203653 = 1350685) (by norm_num)
theorem B4802435 : Blo 2133435 4802435 := bstep (se 1 (by rfl) ⟨3601826, by rfl⟩ : syracuseStep 4802435 = 7203653) B7203653
theorem B3201623 : Blo 2133435 3201623 := bstep (se 1 (by rfl) ⟨2401217, by rfl⟩ : syracuseStep 3201623 = 4802435) B4802435
theorem B2134415 : Blo 2133435 2134415 := bstep (se 1 (by rfl) ⟨1600811, by rfl⟩ : syracuseStep 2134415 = 3201623) B3201623
theorem B3201629 : Blo 2133435 3201629 := bbase (se 3 (by rfl) ⟨600305, by rfl⟩ : syracuseStep 3201629 = 1200611) (by norm_num)
theorem B2134419 : Blo 2133435 2134419 := bstep (se 1 (by rfl) ⟨1600814, by rfl⟩ : syracuseStep 2134419 = 3201629) B3201629
theorem B4802453 : Blo 2133435 4802453 := bbase (se 6 (by rfl) ⟨112557, by rfl⟩ : syracuseStep 4802453 = 225115) (by norm_num)
theorem B3201635 : Blo 2133435 3201635 := bstep (se 1 (by rfl) ⟨2401226, by rfl⟩ : syracuseStep 3201635 = 4802453) B4802453
theorem B2134423 : Blo 2133435 2134423 := bstep (se 1 (by rfl) ⟨1600817, by rfl⟩ : syracuseStep 2134423 = 3201635) B3201635
theorem B4558589 : Blo 2133435 4558589 := bbase (se 3 (by rfl) ⟨854735, by rfl⟩ : syracuseStep 4558589 = 1709471) (by norm_num)
theorem B3039059 : Blo 2133435 3039059 := bstep (se 1 (by rfl) ⟨2279294, by rfl⟩ : syracuseStep 3039059 = 4558589) B4558589
theorem B8104157 : Blo 2133435 8104157 := bstep (se 3 (by rfl) ⟨1519529, by rfl⟩ : syracuseStep 8104157 = 3039059) B3039059
theorem B5402771 : Blo 2133435 5402771 := bstep (se 1 (by rfl) ⟨4052078, by rfl⟩ : syracuseStep 5402771 = 8104157) B8104157
theorem B3601847 : Blo 2133435 3601847 := bstep (se 1 (by rfl) ⟨2701385, by rfl⟩ : syracuseStep 3601847 = 5402771) B5402771
theorem B2401231 : Blo 2133435 2401231 := bstep (se 1 (by rfl) ⟨1800923, by rfl⟩ : syracuseStep 2401231 = 3601847) B3601847
theorem B3201641 : Blo 2133435 3201641 := bstep (se 2 (by rfl) ⟨1200615, by rfl⟩ : syracuseStep 3201641 = 2401231) B2401231
theorem B2134427 : Blo 2133435 2134427 := bstep (se 1 (by rfl) ⟨1600820, by rfl⟩ : syracuseStep 2134427 = 3201641) B3201641
theorem B2163553 : Blo 2133435 2163553 := bbase (se 2 (by rfl) ⟨811332, by rfl⟩ : syracuseStep 2163553 = 1622665) (by norm_num)
theorem B11538949 : Blo 2133435 11538949 := bstep (se 4 (by rfl) ⟨1081776, by rfl⟩ : syracuseStep 11538949 = 2163553) B2163553
theorem B15385265 : Blo 2133435 15385265 := bstep (se 2 (by rfl) ⟨5769474, by rfl⟩ : syracuseStep 15385265 = 11538949) B11538949
theorem B10256843 : Blo 2133435 10256843 := bstep (se 1 (by rfl) ⟨7692632, by rfl⟩ : syracuseStep 10256843 = 15385265) B15385265
theorem B6837895 : Blo 2133435 6837895 := bstep (se 1 (by rfl) ⟨5128421, by rfl⟩ : syracuseStep 6837895 = 10256843) B10256843
theorem B9117193 : Blo 2133435 9117193 := bstep (se 2 (by rfl) ⟨3418947, by rfl⟩ : syracuseStep 9117193 = 6837895) B6837895
theorem B12156257 : Blo 2133435 12156257 := bstep (se 2 (by rfl) ⟨4558596, by rfl⟩ : syracuseStep 12156257 = 9117193) B9117193
theorem B8104171 : Blo 2133435 8104171 := bstep (se 1 (by rfl) ⟨6078128, by rfl⟩ : syracuseStep 8104171 = 12156257) B12156257
theorem B10805561 : Blo 2133435 10805561 := bstep (se 2 (by rfl) ⟨4052085, by rfl⟩ : syracuseStep 10805561 = 8104171) B8104171
theorem B7203707 : Blo 2133435 7203707 := bstep (se 1 (by rfl) ⟨5402780, by rfl⟩ : syracuseStep 7203707 = 10805561) B10805561
theorem B4802471 : Blo 2133435 4802471 := bstep (se 1 (by rfl) ⟨3601853, by rfl⟩ : syracuseStep 4802471 = 7203707) B7203707
theorem B3201647 : Blo 2133435 3201647 := bstep (se 1 (by rfl) ⟨2401235, by rfl⟩ : syracuseStep 3201647 = 4802471) B4802471
theorem B2134431 : Blo 2133435 2134431 := bstep (se 1 (by rfl) ⟨1600823, by rfl⟩ : syracuseStep 2134431 = 3201647) B3201647
theorem B3201653 : Blo 2133435 3201653 := bbase (se 5 (by rfl) ⟨150077, by rfl⟩ : syracuseStep 3201653 = 300155) (by norm_num)
theorem B2134435 : Blo 2133435 2134435 := bstep (se 1 (by rfl) ⟨1600826, by rfl⟩ : syracuseStep 2134435 = 3201653) B3201653
theorem B4052101 : Blo 2133435 4052101 := bbase (se 4 (by rfl) ⟨379884, by rfl⟩ : syracuseStep 4052101 = 759769) (by norm_num)
theorem B5402801 : Blo 2133435 5402801 := bstep (se 2 (by rfl) ⟨2026050, by rfl⟩ : syracuseStep 5402801 = 4052101) B4052101
theorem B3601867 : Blo 2133435 3601867 := bstep (se 1 (by rfl) ⟨2701400, by rfl⟩ : syracuseStep 3601867 = 5402801) B5402801
theorem B4802489 : Blo 2133435 4802489 := bstep (se 2 (by rfl) ⟨1800933, by rfl⟩ : syracuseStep 4802489 = 3601867) B3601867
theorem B3201659 : Blo 2133435 3201659 := bstep (se 1 (by rfl) ⟨2401244, by rfl⟩ : syracuseStep 3201659 = 4802489) B4802489
theorem B2134439 : Blo 2133435 2134439 := bstep (se 1 (by rfl) ⟨1600829, by rfl⟩ : syracuseStep 2134439 = 3201659) B3201659
theorem B2401249 : Blo 2133435 2401249 := bbase (se 2 (by rfl) ⟨900468, by rfl⟩ : syracuseStep 2401249 = 1800937) (by norm_num)
theorem B3201665 : Blo 2133435 3201665 := bstep (se 2 (by rfl) ⟨1200624, by rfl⟩ : syracuseStep 3201665 = 2401249) B2401249
theorem B2134443 : Blo 2133435 2134443 := bstep (se 1 (by rfl) ⟨1600832, by rfl⟩ : syracuseStep 2134443 = 3201665) B3201665
theorem B5402821 : Blo 2133435 5402821 := bbase (se 4 (by rfl) ⟨506514, by rfl⟩ : syracuseStep 5402821 = 1013029) (by norm_num)
theorem B7203761 : Blo 2133435 7203761 := bstep (se 2 (by rfl) ⟨2701410, by rfl⟩ : syracuseStep 7203761 = 5402821) B5402821
theorem B4802507 : Blo 2133435 4802507 := bstep (se 1 (by rfl) ⟨3601880, by rfl⟩ : syracuseStep 4802507 = 7203761) B7203761
theorem B3201671 : Blo 2133435 3201671 := bstep (se 1 (by rfl) ⟨2401253, by rfl⟩ : syracuseStep 3201671 = 4802507) B4802507
theorem B2134447 : Blo 2133435 2134447 := bstep (se 1 (by rfl) ⟨1600835, by rfl⟩ : syracuseStep 2134447 = 3201671) B3201671
theorem B3201677 : Blo 2133435 3201677 := bbase (se 3 (by rfl) ⟨600314, by rfl⟩ : syracuseStep 3201677 = 1200629) (by norm_num)
theorem B2134451 : Blo 2133435 2134451 := bstep (se 1 (by rfl) ⟨1600838, by rfl⟩ : syracuseStep 2134451 = 3201677) B3201677
theorem B4802525 : Blo 2133435 4802525 := bbase (se 3 (by rfl) ⟨900473, by rfl⟩ : syracuseStep 4802525 = 1800947) (by norm_num)
theorem B3201683 : Blo 2133435 3201683 := bstep (se 1 (by rfl) ⟨2401262, by rfl⟩ : syracuseStep 3201683 = 4802525) B4802525
theorem B2134455 : Blo 2133435 2134455 := bstep (se 1 (by rfl) ⟨1600841, by rfl⟩ : syracuseStep 2134455 = 3201683) B3201683
theorem B3601901 : Blo 2133435 3601901 := bbase (se 3 (by rfl) ⟨675356, by rfl⟩ : syracuseStep 3601901 = 1350713) (by norm_num)
theorem B2401267 : Blo 2133435 2401267 := bstep (se 1 (by rfl) ⟨1800950, by rfl⟩ : syracuseStep 2401267 = 3601901) B3601901
theorem B3201689 : Blo 2133435 3201689 := bstep (se 2 (by rfl) ⟨1200633, by rfl⟩ : syracuseStep 3201689 = 2401267) B2401267
theorem B2134459 : Blo 2133435 2134459 := bstep (se 1 (by rfl) ⟨1600844, by rfl⟩ : syracuseStep 2134459 = 3201689) B3201689
theorem B2564249 : Blo 2133435 2564249 := bbase (se 2 (by rfl) ⟨961593, by rfl⟩ : syracuseStep 2564249 = 1923187) (by norm_num)
theorem B27351989 : Blo 2133435 27351989 := bstep (se 5 (by rfl) ⟨1282124, by rfl⟩ : syracuseStep 27351989 = 2564249) B2564249
theorem B18234659 : Blo 2133435 18234659 := bstep (se 1 (by rfl) ⟨13675994, by rfl⟩ : syracuseStep 18234659 = 27351989) B27351989
theorem B12156439 : Blo 2133435 12156439 := bstep (se 1 (by rfl) ⟨9117329, by rfl⟩ : syracuseStep 12156439 = 18234659) B18234659
theorem B16208585 : Blo 2133435 16208585 := bstep (se 2 (by rfl) ⟨6078219, by rfl⟩ : syracuseStep 16208585 = 12156439) B12156439
theorem B10805723 : Blo 2133435 10805723 := bstep (se 1 (by rfl) ⟨8104292, by rfl⟩ : syracuseStep 10805723 = 16208585) B16208585
theorem B7203815 : Blo 2133435 7203815 := bstep (se 1 (by rfl) ⟨5402861, by rfl⟩ : syracuseStep 7203815 = 10805723) B10805723
theorem B4802543 : Blo 2133435 4802543 := bstep (se 1 (by rfl) ⟨3601907, by rfl⟩ : syracuseStep 4802543 = 7203815) B7203815
theorem B3201695 : Blo 2133435 3201695 := bstep (se 1 (by rfl) ⟨2401271, by rfl⟩ : syracuseStep 3201695 = 4802543) B4802543
theorem B2134463 : Blo 2133435 2134463 := bstep (se 1 (by rfl) ⟨1600847, by rfl⟩ : syracuseStep 2134463 = 3201695) B3201695
theorem B3201701 : Blo 2133435 3201701 := bbase (se 4 (by rfl) ⟨300159, by rfl⟩ : syracuseStep 3201701 = 600319) (by norm_num)
theorem B2134467 : Blo 2133435 2134467 := bstep (se 1 (by rfl) ⟨1600850, by rfl⟩ : syracuseStep 2134467 = 3201701) B3201701
theorem B2701441 : Blo 2133435 2701441 := bbase (se 2 (by rfl) ⟨1013040, by rfl⟩ : syracuseStep 2701441 = 2026081) (by norm_num)
theorem B3601921 : Blo 2133435 3601921 := bstep (se 2 (by rfl) ⟨1350720, by rfl⟩ : syracuseStep 3601921 = 2701441) B2701441
theorem B4802561 : Blo 2133435 4802561 := bstep (se 2 (by rfl) ⟨1800960, by rfl⟩ : syracuseStep 4802561 = 3601921) B3601921
theorem B3201707 : Blo 2133435 3201707 := bstep (se 1 (by rfl) ⟨2401280, by rfl⟩ : syracuseStep 3201707 = 4802561) B4802561
theorem B2134471 : Blo 2133435 2134471 := bstep (se 1 (by rfl) ⟨1600853, by rfl⟩ : syracuseStep 2134471 = 3201707) B3201707
theorem B2401285 : Blo 2133435 2401285 := bbase (se 4 (by rfl) ⟨225120, by rfl⟩ : syracuseStep 2401285 = 450241) (by norm_num)
theorem B3201713 : Blo 2133435 3201713 := bstep (se 2 (by rfl) ⟨1200642, by rfl⟩ : syracuseStep 3201713 = 2401285) B2401285
theorem B2134475 : Blo 2133435 2134475 := bstep (se 1 (by rfl) ⟨1600856, by rfl⟩ : syracuseStep 2134475 = 3201713) B3201713
theorem B3039133 : Blo 2133435 3039133 := bbase (se 3 (by rfl) ⟨569837, by rfl⟩ : syracuseStep 3039133 = 1139675) (by norm_num)
theorem B4052177 : Blo 2133435 4052177 := bstep (se 2 (by rfl) ⟨1519566, by rfl⟩ : syracuseStep 4052177 = 3039133) B3039133
theorem B2701451 : Blo 2133435 2701451 := bstep (se 1 (by rfl) ⟨2026088, by rfl⟩ : syracuseStep 2701451 = 4052177) B4052177
theorem B7203869 : Blo 2133435 7203869 := bstep (se 3 (by rfl) ⟨1350725, by rfl⟩ : syracuseStep 7203869 = 2701451) B2701451
theorem B4802579 : Blo 2133435 4802579 := bstep (se 1 (by rfl) ⟨3601934, by rfl⟩ : syracuseStep 4802579 = 7203869) B7203869
theorem B3201719 : Blo 2133435 3201719 := bstep (se 1 (by rfl) ⟨2401289, by rfl⟩ : syracuseStep 3201719 = 4802579) B4802579
theorem B2134479 : Blo 2133435 2134479 := bstep (se 1 (by rfl) ⟨1600859, by rfl⟩ : syracuseStep 2134479 = 3201719) B3201719
theorem B3201725 : Blo 2133435 3201725 := bbase (se 3 (by rfl) ⟨600323, by rfl⟩ : syracuseStep 3201725 = 1200647) (by norm_num)
theorem B2134483 : Blo 2133435 2134483 := bstep (se 1 (by rfl) ⟨1600862, by rfl⟩ : syracuseStep 2134483 = 3201725) B3201725
theorem B4802597 : Blo 2133435 4802597 := bbase (se 4 (by rfl) ⟨450243, by rfl⟩ : syracuseStep 4802597 = 900487) (by norm_num)
theorem B3201731 : Blo 2133435 3201731 := bstep (se 1 (by rfl) ⟨2401298, by rfl⟩ : syracuseStep 3201731 = 4802597) B4802597
theorem B2134487 : Blo 2133435 2134487 := bstep (se 1 (by rfl) ⟨1600865, by rfl⟩ : syracuseStep 2134487 = 3201731) B3201731
theorem B5402933 : Blo 2133435 5402933 := bbase (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) (by norm_num)
theorem B3601955 : Blo 2133435 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B2401303 : Blo 2133435 2401303 := bstep (se 1 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 2401303 = 3601955) B3601955
theorem B3201737 : Blo 2133435 3201737 := bstep (se 2 (by rfl) ⟨1200651, by rfl⟩ : syracuseStep 3201737 = 2401303) B2401303
theorem B2134491 : Blo 2133435 2134491 := bstep (se 1 (by rfl) ⟨1600868, by rfl⟩ : syracuseStep 2134491 = 3201737) B3201737
theorem B2193137 : Blo 2133435 2193137 := bbase (se 2 (by rfl) ⟨822426, by rfl⟩ : syracuseStep 2193137 = 1644853) (by norm_num)
theorem B23393461 : Blo 2133435 23393461 := bstep (se 5 (by rfl) ⟨1096568, by rfl⟩ : syracuseStep 23393461 = 2193137) B2193137
theorem B31191281 : Blo 2133435 31191281 := bstep (se 2 (by rfl) ⟨11696730, by rfl⟩ : syracuseStep 31191281 = 23393461) B23393461
theorem B20794187 : Blo 2133435 20794187 := bstep (se 1 (by rfl) ⟨15595640, by rfl⟩ : syracuseStep 20794187 = 31191281) B31191281
theorem B13862791 : Blo 2133435 13862791 := bstep (se 1 (by rfl) ⟨10397093, by rfl⟩ : syracuseStep 13862791 = 20794187) B20794187
theorem B18483721 : Blo 2133435 18483721 := bstep (se 2 (by rfl) ⟨6931395, by rfl⟩ : syracuseStep 18483721 = 13862791) B13862791
theorem B98579845 : Blo 2133435 98579845 := bstep (se 4 (by rfl) ⟨9241860, by rfl⟩ : syracuseStep 98579845 = 18483721) B18483721
theorem B131439793 : Blo 2133435 131439793 := bstep (se 2 (by rfl) ⟨49289922, by rfl⟩ : syracuseStep 131439793 = 98579845) B98579845
theorem B175253057 : Blo 2133435 175253057 := bstep (se 2 (by rfl) ⟨65719896, by rfl⟩ : syracuseStep 175253057 = 131439793) B131439793
theorem B116835371 : Blo 2133435 116835371 := bstep (se 1 (by rfl) ⟨87626528, by rfl⟩ : syracuseStep 116835371 = 175253057) B175253057
theorem B77890247 : Blo 2133435 77890247 := bstep (se 1 (by rfl) ⟨58417685, by rfl⟩ : syracuseStep 77890247 = 116835371) B116835371
theorem B51926831 : Blo 2133435 51926831 := bstep (se 1 (by rfl) ⟨38945123, by rfl⟩ : syracuseStep 51926831 = 77890247) B77890247
theorem B34617887 : Blo 2133435 34617887 := bstep (se 1 (by rfl) ⟨25963415, by rfl⟩ : syracuseStep 34617887 = 51926831) B51926831
theorem B23078591 : Blo 2133435 23078591 := bstep (se 1 (by rfl) ⟨17308943, by rfl⟩ : syracuseStep 23078591 = 34617887) B34617887
theorem B15385727 : Blo 2133435 15385727 := bstep (se 1 (by rfl) ⟨11539295, by rfl⟩ : syracuseStep 15385727 = 23078591) B23078591
theorem B10257151 : Blo 2133435 10257151 := bstep (se 1 (by rfl) ⟨7692863, by rfl⟩ : syracuseStep 10257151 = 15385727) B15385727
theorem B13676201 : Blo 2133435 13676201 := bstep (se 2 (by rfl) ⟨5128575, by rfl⟩ : syracuseStep 13676201 = 10257151) B10257151
theorem B9117467 : Blo 2133435 9117467 := bstep (se 1 (by rfl) ⟨6838100, by rfl⟩ : syracuseStep 9117467 = 13676201) B13676201
theorem B6078311 : Blo 2133435 6078311 := bstep (se 1 (by rfl) ⟨4558733, by rfl⟩ : syracuseStep 6078311 = 9117467) B9117467
theorem B4052207 : Blo 2133435 4052207 := bstep (se 1 (by rfl) ⟨3039155, by rfl⟩ : syracuseStep 4052207 = 6078311) B6078311
theorem B10805885 : Blo 2133435 10805885 := bstep (se 3 (by rfl) ⟨2026103, by rfl⟩ : syracuseStep 10805885 = 4052207) B4052207
theorem B7203923 : Blo 2133435 7203923 := bstep (se 1 (by rfl) ⟨5402942, by rfl⟩ : syracuseStep 7203923 = 10805885) B10805885
theorem B4802615 : Blo 2133435 4802615 := bstep (se 1 (by rfl) ⟨3601961, by rfl⟩ : syracuseStep 4802615 = 7203923) B7203923
theorem B3201743 : Blo 2133435 3201743 := bstep (se 1 (by rfl) ⟨2401307, by rfl⟩ : syracuseStep 3201743 = 4802615) B4802615
theorem B2134495 : Blo 2133435 2134495 := bstep (se 1 (by rfl) ⟨1600871, by rfl⟩ : syracuseStep 2134495 = 3201743) B3201743
theorem B3201749 : Blo 2133435 3201749 := bbase (se 7 (by rfl) ⟨37520, by rfl⟩ : syracuseStep 3201749 = 75041) (by norm_num)
theorem B2134499 : Blo 2133435 2134499 := bstep (se 1 (by rfl) ⟨1600874, by rfl⟩ : syracuseStep 2134499 = 3201749) B3201749
theorem B3751429 : Blo 2133435 3751429 := bbase (se 4 (by rfl) ⟨351696, by rfl⟩ : syracuseStep 3751429 = 703393) (by norm_num)
theorem B5001905 : Blo 2133435 5001905 := bstep (se 2 (by rfl) ⟨1875714, by rfl⟩ : syracuseStep 5001905 = 3751429) B3751429
theorem B3334603 : Blo 2133435 3334603 := bstep (se 1 (by rfl) ⟨2500952, by rfl⟩ : syracuseStep 3334603 = 5001905) B5001905
theorem B4446137 : Blo 2133435 4446137 := bstep (se 2 (by rfl) ⟨1667301, by rfl⟩ : syracuseStep 4446137 = 3334603) B3334603
theorem B11856365 : Blo 2133435 11856365 := bstep (se 3 (by rfl) ⟨2223068, by rfl⟩ : syracuseStep 11856365 = 4446137) B4446137
theorem B7904243 : Blo 2133435 7904243 := bstep (se 1 (by rfl) ⟨5928182, by rfl⟩ : syracuseStep 7904243 = 11856365) B11856365
theorem B5269495 : Blo 2133435 5269495 := bstep (se 1 (by rfl) ⟨3952121, by rfl⟩ : syracuseStep 5269495 = 7904243) B7904243
theorem B7025993 : Blo 2133435 7025993 := bstep (se 2 (by rfl) ⟨2634747, by rfl⟩ : syracuseStep 7025993 = 5269495) B5269495
theorem B4683995 : Blo 2133435 4683995 := bstep (se 1 (by rfl) ⟨3512996, by rfl⟩ : syracuseStep 4683995 = 7025993) B7025993
theorem B3122663 : Blo 2133435 3122663 := bstep (se 1 (by rfl) ⟨2341997, by rfl⟩ : syracuseStep 3122663 = 4683995) B4683995
theorem B33308405 : Blo 2133435 33308405 := bstep (se 5 (by rfl) ⟨1561331, by rfl⟩ : syracuseStep 33308405 = 3122663) B3122663
theorem B22205603 : Blo 2133435 22205603 := bstep (se 1 (by rfl) ⟨16654202, by rfl⟩ : syracuseStep 22205603 = 33308405) B33308405
theorem B14803735 : Blo 2133435 14803735 := bstep (se 1 (by rfl) ⟨11102801, by rfl⟩ : syracuseStep 14803735 = 22205603) B22205603
theorem B19738313 : Blo 2133435 19738313 := bstep (se 2 (by rfl) ⟨7401867, by rfl⟩ : syracuseStep 19738313 = 14803735) B14803735
theorem B13158875 : Blo 2133435 13158875 := bstep (se 1 (by rfl) ⟨9869156, by rfl⟩ : syracuseStep 13158875 = 19738313) B19738313
theorem B8772583 : Blo 2133435 8772583 := bstep (se 1 (by rfl) ⟨6579437, by rfl⟩ : syracuseStep 8772583 = 13158875) B13158875
theorem B11696777 : Blo 2133435 11696777 := bstep (se 2 (by rfl) ⟨4386291, by rfl⟩ : syracuseStep 11696777 = 8772583) B8772583
theorem B7797851 : Blo 2133435 7797851 := bstep (se 1 (by rfl) ⟨5848388, by rfl⟩ : syracuseStep 7797851 = 11696777) B11696777
theorem B83177077 : Blo 2133435 83177077 := bstep (se 5 (by rfl) ⟨3898925, by rfl⟩ : syracuseStep 83177077 = 7797851) B7797851
theorem B110902769 : Blo 2133435 110902769 := bstep (se 2 (by rfl) ⟨41588538, by rfl⟩ : syracuseStep 110902769 = 83177077) B83177077
theorem B73935179 : Blo 2133435 73935179 := bstep (se 1 (by rfl) ⟨55451384, by rfl⟩ : syracuseStep 73935179 = 110902769) B110902769
theorem B49290119 : Blo 2133435 49290119 := bstep (se 1 (by rfl) ⟨36967589, by rfl⟩ : syracuseStep 49290119 = 73935179) B73935179
theorem B32860079 : Blo 2133435 32860079 := bstep (se 1 (by rfl) ⟨24645059, by rfl⟩ : syracuseStep 32860079 = 49290119) B49290119
theorem B21906719 : Blo 2133435 21906719 := bstep (se 1 (by rfl) ⟨16430039, by rfl⟩ : syracuseStep 21906719 = 32860079) B32860079
theorem B14604479 : Blo 2133435 14604479 := bstep (se 1 (by rfl) ⟨10953359, by rfl⟩ : syracuseStep 14604479 = 21906719) B21906719
theorem B9736319 : Blo 2133435 9736319 := bstep (se 1 (by rfl) ⟨7302239, by rfl⟩ : syracuseStep 9736319 = 14604479) B14604479
theorem B25963517 : Blo 2133435 25963517 := bstep (se 3 (by rfl) ⟨4868159, by rfl⟩ : syracuseStep 25963517 = 9736319) B9736319
theorem B17309011 : Blo 2133435 17309011 := bstep (se 1 (by rfl) ⟨12981758, by rfl⟩ : syracuseStep 17309011 = 25963517) B25963517
theorem B23078681 : Blo 2133435 23078681 := bstep (se 2 (by rfl) ⟨8654505, by rfl⟩ : syracuseStep 23078681 = 17309011) B17309011
theorem B15385787 : Blo 2133435 15385787 := bstep (se 1 (by rfl) ⟨11539340, by rfl⟩ : syracuseStep 15385787 = 23078681) B23078681
theorem B10257191 : Blo 2133435 10257191 := bstep (se 1 (by rfl) ⟨7692893, by rfl⟩ : syracuseStep 10257191 = 15385787) B15385787
theorem B6838127 : Blo 2133435 6838127 := bstep (se 1 (by rfl) ⟨5128595, by rfl⟩ : syracuseStep 6838127 = 10257191) B10257191
theorem B4558751 : Blo 2133435 4558751 := bstep (se 1 (by rfl) ⟨3419063, by rfl⟩ : syracuseStep 4558751 = 6838127) B6838127
theorem B3039167 : Blo 2133435 3039167 := bstep (se 1 (by rfl) ⟨2279375, by rfl⟩ : syracuseStep 3039167 = 4558751) B4558751
theorem B8104445 : Blo 2133435 8104445 := bstep (se 3 (by rfl) ⟨1519583, by rfl⟩ : syracuseStep 8104445 = 3039167) B3039167
theorem B5402963 : Blo 2133435 5402963 := bstep (se 1 (by rfl) ⟨4052222, by rfl⟩ : syracuseStep 5402963 = 8104445) B8104445
theorem B3601975 : Blo 2133435 3601975 := bstep (se 1 (by rfl) ⟨2701481, by rfl⟩ : syracuseStep 3601975 = 5402963) B5402963
theorem B4802633 : Blo 2133435 4802633 := bstep (se 2 (by rfl) ⟨1800987, by rfl⟩ : syracuseStep 4802633 = 3601975) B3601975
theorem B3201755 : Blo 2133435 3201755 := bstep (se 1 (by rfl) ⟨2401316, by rfl⟩ : syracuseStep 3201755 = 4802633) B4802633
theorem B2134503 : Blo 2133435 2134503 := bstep (se 1 (by rfl) ⟨1600877, by rfl⟩ : syracuseStep 2134503 = 3201755) B3201755
theorem B2401321 : Blo 2133435 2401321 := bbase (se 2 (by rfl) ⟨900495, by rfl⟩ : syracuseStep 2401321 = 1800991) (by norm_num)
theorem B3201761 : Blo 2133435 3201761 := bstep (se 2 (by rfl) ⟨1200660, by rfl⟩ : syracuseStep 3201761 = 2401321) B2401321
theorem B2134507 : Blo 2133435 2134507 := bstep (se 1 (by rfl) ⟨1600880, by rfl⟩ : syracuseStep 2134507 = 3201761) B3201761
theorem B46157525 : Blo 2133435 46157525 := bbase (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) (by norm_num)
theorem B30771683 : Blo 2133435 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B20514455 : Blo 2133435 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B13676303 : Blo 2133435 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B9117535 : Blo 2133435 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B12156713 : Blo 2133435 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B8104475 : Blo 2133435 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B5402983 : Blo 2133435 5402983 := bstep (se 1 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 5402983 = 8104475) B8104475
theorem B7203977 : Blo 2133435 7203977 := bstep (se 2 (by rfl) ⟨2701491, by rfl⟩ : syracuseStep 7203977 = 5402983) B5402983
theorem B4802651 : Blo 2133435 4802651 := bstep (se 1 (by rfl) ⟨3601988, by rfl⟩ : syracuseStep 4802651 = 7203977) B7203977
theorem B3201767 : Blo 2133435 3201767 := bstep (se 1 (by rfl) ⟨2401325, by rfl⟩ : syracuseStep 3201767 = 4802651) B4802651
theorem B2134511 : Blo 2133435 2134511 := bstep (se 1 (by rfl) ⟨1600883, by rfl⟩ : syracuseStep 2134511 = 3201767) B3201767
theorem B3201773 : Blo 2133435 3201773 := bbase (se 3 (by rfl) ⟨600332, by rfl⟩ : syracuseStep 3201773 = 1200665) (by norm_num)
theorem B2134515 : Blo 2133435 2134515 := bstep (se 1 (by rfl) ⟨1600886, by rfl⟩ : syracuseStep 2134515 = 3201773) B3201773
theorem B4802669 : Blo 2133435 4802669 := bbase (se 3 (by rfl) ⟨900500, by rfl⟩ : syracuseStep 4802669 = 1801001) (by norm_num)
theorem B3201779 : Blo 2133435 3201779 := bstep (se 1 (by rfl) ⟨2401334, by rfl⟩ : syracuseStep 3201779 = 4802669) B4802669
theorem B2134519 : Blo 2133435 2134519 := bstep (se 1 (by rfl) ⟨1600889, by rfl⟩ : syracuseStep 2134519 = 3201779) B3201779
theorem B4052261 : Blo 2133435 4052261 := bbase (se 4 (by rfl) ⟨379899, by rfl⟩ : syracuseStep 4052261 = 759799) (by norm_num)
theorem B2701507 : Blo 2133435 2701507 := bstep (se 1 (by rfl) ⟨2026130, by rfl⟩ : syracuseStep 2701507 = 4052261) B4052261
theorem B3602009 : Blo 2133435 3602009 := bstep (se 2 (by rfl) ⟨1350753, by rfl⟩ : syracuseStep 3602009 = 2701507) B2701507
theorem B2401339 : Blo 2133435 2401339 := bstep (se 1 (by rfl) ⟨1801004, by rfl⟩ : syracuseStep 2401339 = 3602009) B3602009
theorem B3201785 : Blo 2133435 3201785 := bstep (se 2 (by rfl) ⟨1200669, by rfl⟩ : syracuseStep 3201785 = 2401339) B2401339
theorem B2134523 : Blo 2133435 2134523 := bstep (se 1 (by rfl) ⟨1600892, by rfl⟩ : syracuseStep 2134523 = 3201785) B3201785
theorem B23078933 : Blo 2133435 23078933 := bbase (se 6 (by rfl) ⟨540912, by rfl⟩ : syracuseStep 23078933 = 1081825) (by norm_num)
theorem B15385955 : Blo 2133435 15385955 := bstep (se 1 (by rfl) ⟨11539466, by rfl⟩ : syracuseStep 15385955 = 23078933) B23078933
theorem B41029213 : Blo 2133435 41029213 := bstep (se 3 (by rfl) ⟨7692977, by rfl⟩ : syracuseStep 41029213 = 15385955) B15385955
theorem B54705617 : Blo 2133435 54705617 := bstep (se 2 (by rfl) ⟨20514606, by rfl⟩ : syracuseStep 54705617 = 41029213) B41029213
theorem B36470411 : Blo 2133435 36470411 := bstep (se 1 (by rfl) ⟨27352808, by rfl⟩ : syracuseStep 36470411 = 54705617) B54705617
theorem B24313607 : Blo 2133435 24313607 := bstep (se 1 (by rfl) ⟨18235205, by rfl⟩ : syracuseStep 24313607 = 36470411) B36470411
theorem B16209071 : Blo 2133435 16209071 := bstep (se 1 (by rfl) ⟨12156803, by rfl⟩ : syracuseStep 16209071 = 24313607) B24313607
theorem B10806047 : Blo 2133435 10806047 := bstep (se 1 (by rfl) ⟨8104535, by rfl⟩ : syracuseStep 10806047 = 16209071) B16209071
theorem B7204031 : Blo 2133435 7204031 := bstep (se 1 (by rfl) ⟨5403023, by rfl⟩ : syracuseStep 7204031 = 10806047) B10806047
theorem B4802687 : Blo 2133435 4802687 := bstep (se 1 (by rfl) ⟨3602015, by rfl⟩ : syracuseStep 4802687 = 7204031) B7204031
theorem B3201791 : Blo 2133435 3201791 := bstep (se 1 (by rfl) ⟨2401343, by rfl⟩ : syracuseStep 3201791 = 4802687) B4802687
theorem B2134527 : Blo 2133435 2134527 := bstep (se 1 (by rfl) ⟨1600895, by rfl⟩ : syracuseStep 2134527 = 3201791) B3201791
theorem B3201797 : Blo 2133435 3201797 := bbase (se 4 (by rfl) ⟨300168, by rfl⟩ : syracuseStep 3201797 = 600337) (by norm_num)
theorem B2134531 : Blo 2133435 2134531 := bstep (se 1 (by rfl) ⟨1600898, by rfl⟩ : syracuseStep 2134531 = 3201797) B3201797
theorem B3602029 : Blo 2133435 3602029 := bbase (se 3 (by rfl) ⟨675380, by rfl⟩ : syracuseStep 3602029 = 1350761) (by norm_num)
theorem B4802705 : Blo 2133435 4802705 := bstep (se 2 (by rfl) ⟨1801014, by rfl⟩ : syracuseStep 4802705 = 3602029) B3602029
theorem B3201803 : Blo 2133435 3201803 := bstep (se 1 (by rfl) ⟨2401352, by rfl⟩ : syracuseStep 3201803 = 4802705) B4802705
theorem B2134535 : Blo 2133435 2134535 := bstep (se 1 (by rfl) ⟨1600901, by rfl⟩ : syracuseStep 2134535 = 3201803) B3201803
theorem B2401357 : Blo 2133435 2401357 := bbase (se 3 (by rfl) ⟨450254, by rfl⟩ : syracuseStep 2401357 = 900509) (by norm_num)
theorem B3201809 : Blo 2133435 3201809 := bstep (se 2 (by rfl) ⟨1200678, by rfl⟩ : syracuseStep 3201809 = 2401357) B2401357
theorem B2134539 : Blo 2133435 2134539 := bstep (se 1 (by rfl) ⟨1600904, by rfl⟩ : syracuseStep 2134539 = 3201809) B3201809
theorem B7204085 : Blo 2133435 7204085 := bbase (se 5 (by rfl) ⟨337691, by rfl⟩ : syracuseStep 7204085 = 675383) (by norm_num)
theorem B4802723 : Blo 2133435 4802723 := bstep (se 1 (by rfl) ⟨3602042, by rfl⟩ : syracuseStep 4802723 = 7204085) B7204085
theorem B3201815 : Blo 2133435 3201815 := bstep (se 1 (by rfl) ⟨2401361, by rfl⟩ : syracuseStep 3201815 = 4802723) B4802723
theorem B2134543 : Blo 2133435 2134543 := bstep (se 1 (by rfl) ⟨1600907, by rfl⟩ : syracuseStep 2134543 = 3201815) B3201815
theorem B3201821 : Blo 2133435 3201821 := bbase (se 3 (by rfl) ⟨600341, by rfl⟩ : syracuseStep 3201821 = 1200683) (by norm_num)
theorem B2134547 : Blo 2133435 2134547 := bstep (se 1 (by rfl) ⟨1600910, by rfl⟩ : syracuseStep 2134547 = 3201821) B3201821
theorem B4802741 : Blo 2133435 4802741 := bbase (se 5 (by rfl) ⟨225128, by rfl⟩ : syracuseStep 4802741 = 450257) (by norm_num)
theorem B3201827 : Blo 2133435 3201827 := bstep (se 1 (by rfl) ⟨2401370, by rfl⟩ : syracuseStep 3201827 = 4802741) B4802741
theorem B2134551 : Blo 2133435 2134551 := bstep (se 1 (by rfl) ⟨1600913, by rfl⟩ : syracuseStep 2134551 = 3201827) B3201827
theorem B3846541 : Blo 2133435 3846541 := bbase (se 3 (by rfl) ⟨721226, by rfl⟩ : syracuseStep 3846541 = 1442453) (by norm_num)
theorem B5128721 : Blo 2133435 5128721 := bstep (se 2 (by rfl) ⟨1923270, by rfl⟩ : syracuseStep 5128721 = 3846541) B3846541
theorem B3419147 : Blo 2133435 3419147 := bstep (se 1 (by rfl) ⟨2564360, by rfl⟩ : syracuseStep 3419147 = 5128721) B5128721
theorem B2279431 : Blo 2133435 2279431 := bstep (se 1 (by rfl) ⟨1709573, by rfl⟩ : syracuseStep 2279431 = 3419147) B3419147
theorem B12156965 : Blo 2133435 12156965 := bstep (se 4 (by rfl) ⟨1139715, by rfl⟩ : syracuseStep 12156965 = 2279431) B2279431
theorem B8104643 : Blo 2133435 8104643 := bstep (se 1 (by rfl) ⟨6078482, by rfl⟩ : syracuseStep 8104643 = 12156965) B12156965
theorem B5403095 : Blo 2133435 5403095 := bstep (se 1 (by rfl) ⟨4052321, by rfl⟩ : syracuseStep 5403095 = 8104643) B8104643
theorem B3602063 : Blo 2133435 3602063 := bstep (se 1 (by rfl) ⟨2701547, by rfl⟩ : syracuseStep 3602063 = 5403095) B5403095
theorem B2401375 : Blo 2133435 2401375 := bstep (se 1 (by rfl) ⟨1801031, by rfl⟩ : syracuseStep 2401375 = 3602063) B3602063
theorem B3201833 : Blo 2133435 3201833 := bstep (se 2 (by rfl) ⟨1200687, by rfl⟩ : syracuseStep 3201833 = 2401375) B2401375
theorem B2134555 : Blo 2133435 2134555 := bstep (se 1 (by rfl) ⟨1600916, by rfl⟩ : syracuseStep 2134555 = 3201833) B3201833
theorem B2564365 : Blo 2133435 2564365 := bbase (se 3 (by rfl) ⟨480818, by rfl⟩ : syracuseStep 2564365 = 961637) (by norm_num)
theorem B3419153 : Blo 2133435 3419153 := bstep (se 2 (by rfl) ⟨1282182, by rfl⟩ : syracuseStep 3419153 = 2564365) B2564365
theorem B2279435 : Blo 2133435 2279435 := bstep (se 1 (by rfl) ⟨1709576, by rfl⟩ : syracuseStep 2279435 = 3419153) B3419153
theorem B6078493 : Blo 2133435 6078493 := bstep (se 3 (by rfl) ⟨1139717, by rfl⟩ : syracuseStep 6078493 = 2279435) B2279435
theorem B8104657 : Blo 2133435 8104657 := bstep (se 2 (by rfl) ⟨3039246, by rfl⟩ : syracuseStep 8104657 = 6078493) B6078493
theorem B10806209 : Blo 2133435 10806209 := bstep (se 2 (by rfl) ⟨4052328, by rfl⟩ : syracuseStep 10806209 = 8104657) B8104657
theorem B7204139 : Blo 2133435 7204139 := bstep (se 1 (by rfl) ⟨5403104, by rfl⟩ : syracuseStep 7204139 = 10806209) B10806209
theorem B4802759 : Blo 2133435 4802759 := bstep (se 1 (by rfl) ⟨3602069, by rfl⟩ : syracuseStep 4802759 = 7204139) B7204139
theorem B3201839 : Blo 2133435 3201839 := bstep (se 1 (by rfl) ⟨2401379, by rfl⟩ : syracuseStep 3201839 = 4802759) B4802759
theorem B2134559 : Blo 2133435 2134559 := bstep (se 1 (by rfl) ⟨1600919, by rfl⟩ : syracuseStep 2134559 = 3201839) B3201839
theorem B3201845 : Blo 2133435 3201845 := bbase (se 5 (by rfl) ⟨150086, by rfl⟩ : syracuseStep 3201845 = 300173) (by norm_num)
theorem B2134563 : Blo 2133435 2134563 := bstep (se 1 (by rfl) ⟨1600922, by rfl⟩ : syracuseStep 2134563 = 3201845) B3201845
theorem B5403125 : Blo 2133435 5403125 := bbase (se 5 (by rfl) ⟨253271, by rfl⟩ : syracuseStep 5403125 = 506543) (by norm_num)
theorem B3602083 : Blo 2133435 3602083 := bstep (se 1 (by rfl) ⟨2701562, by rfl⟩ : syracuseStep 3602083 = 5403125) B5403125
theorem B4802777 : Blo 2133435 4802777 := bstep (se 2 (by rfl) ⟨1801041, by rfl⟩ : syracuseStep 4802777 = 3602083) B3602083
theorem B3201851 : Blo 2133435 3201851 := bstep (se 1 (by rfl) ⟨2401388, by rfl⟩ : syracuseStep 3201851 = 4802777) B4802777
theorem B2134567 : Blo 2133435 2134567 := bstep (se 1 (by rfl) ⟨1600925, by rfl⟩ : syracuseStep 2134567 = 3201851) B3201851
theorem B2401393 : Blo 2133435 2401393 := bbase (se 2 (by rfl) ⟨900522, by rfl⟩ : syracuseStep 2401393 = 1801045) (by norm_num)
theorem B3201857 : Blo 2133435 3201857 := bstep (se 2 (by rfl) ⟨1200696, by rfl⟩ : syracuseStep 3201857 = 2401393) B2401393
theorem B2134571 : Blo 2133435 2134571 := bstep (se 1 (by rfl) ⟨1600928, by rfl⟩ : syracuseStep 2134571 = 3201857) B3201857
theorem B6838357 : Blo 2133435 6838357 := bbase (se 8 (by rfl) ⟨40068, by rfl⟩ : syracuseStep 6838357 = 80137) (by norm_num)
theorem B9117809 : Blo 2133435 9117809 := bstep (se 2 (by rfl) ⟨3419178, by rfl⟩ : syracuseStep 9117809 = 6838357) B6838357
theorem B6078539 : Blo 2133435 6078539 := bstep (se 1 (by rfl) ⟨4558904, by rfl⟩ : syracuseStep 6078539 = 9117809) B9117809
theorem B4052359 : Blo 2133435 4052359 := bstep (se 1 (by rfl) ⟨3039269, by rfl⟩ : syracuseStep 4052359 = 6078539) B6078539
theorem B5403145 : Blo 2133435 5403145 := bstep (se 2 (by rfl) ⟨2026179, by rfl⟩ : syracuseStep 5403145 = 4052359) B4052359
theorem B7204193 : Blo 2133435 7204193 := bstep (se 2 (by rfl) ⟨2701572, by rfl⟩ : syracuseStep 7204193 = 5403145) B5403145
theorem B4802795 : Blo 2133435 4802795 := bstep (se 1 (by rfl) ⟨3602096, by rfl⟩ : syracuseStep 4802795 = 7204193) B7204193
theorem B3201863 : Blo 2133435 3201863 := bstep (se 1 (by rfl) ⟨2401397, by rfl⟩ : syracuseStep 3201863 = 4802795) B4802795
theorem B2134575 : Blo 2133435 2134575 := bstep (se 1 (by rfl) ⟨1600931, by rfl⟩ : syracuseStep 2134575 = 3201863) B3201863
theorem B3201869 : Blo 2133435 3201869 := bbase (se 3 (by rfl) ⟨600350, by rfl⟩ : syracuseStep 3201869 = 1200701) (by norm_num)
theorem B2134579 : Blo 2133435 2134579 := bstep (se 1 (by rfl) ⟨1600934, by rfl⟩ : syracuseStep 2134579 = 3201869) B3201869
theorem B4802813 : Blo 2133435 4802813 := bbase (se 3 (by rfl) ⟨900527, by rfl⟩ : syracuseStep 4802813 = 1801055) (by norm_num)
theorem B3201875 : Blo 2133435 3201875 := bstep (se 1 (by rfl) ⟨2401406, by rfl⟩ : syracuseStep 3201875 = 4802813) B4802813
theorem B2134583 : Blo 2133435 2134583 := bstep (se 1 (by rfl) ⟨1600937, by rfl⟩ : syracuseStep 2134583 = 3201875) B3201875
theorem B3602117 : Blo 2133435 3602117 := bbase (se 4 (by rfl) ⟨337698, by rfl⟩ : syracuseStep 3602117 = 675397) (by norm_num)
theorem B2401411 : Blo 2133435 2401411 := bstep (se 1 (by rfl) ⟨1801058, by rfl⟩ : syracuseStep 2401411 = 3602117) B3602117
theorem B3201881 : Blo 2133435 3201881 := bstep (se 2 (by rfl) ⟨1200705, by rfl⟩ : syracuseStep 3201881 = 2401411) B2401411
theorem B2134587 : Blo 2133435 2134587 := bstep (se 1 (by rfl) ⟨1600940, by rfl⟩ : syracuseStep 2134587 = 3201881) B3201881
theorem B16209557 : Blo 2133435 16209557 := bbase (se 6 (by rfl) ⟨379911, by rfl⟩ : syracuseStep 16209557 = 759823) (by norm_num)
theorem B10806371 : Blo 2133435 10806371 := bstep (se 1 (by rfl) ⟨8104778, by rfl⟩ : syracuseStep 10806371 = 16209557) B16209557
theorem B7204247 : Blo 2133435 7204247 := bstep (se 1 (by rfl) ⟨5403185, by rfl⟩ : syracuseStep 7204247 = 10806371) B10806371
theorem B4802831 : Blo 2133435 4802831 := bstep (se 1 (by rfl) ⟨3602123, by rfl⟩ : syracuseStep 4802831 = 7204247) B7204247
theorem B3201887 : Blo 2133435 3201887 := bstep (se 1 (by rfl) ⟨2401415, by rfl⟩ : syracuseStep 3201887 = 4802831) B4802831
theorem B2134591 : Blo 2133435 2134591 := bstep (se 1 (by rfl) ⟨1600943, by rfl⟩ : syracuseStep 2134591 = 3201887) B3201887
theorem B3201893 : Blo 2133435 3201893 := bbase (se 4 (by rfl) ⟨300177, by rfl⟩ : syracuseStep 3201893 = 600355) (by norm_num)
theorem B2134595 : Blo 2133435 2134595 := bstep (se 1 (by rfl) ⟨1600946, by rfl⟩ : syracuseStep 2134595 = 3201893) B3201893
theorem B4052405 : Blo 2133435 4052405 := bbase (se 5 (by rfl) ⟨189956, by rfl⟩ : syracuseStep 4052405 = 379913) (by norm_num)
theorem B2701603 : Blo 2133435 2701603 := bstep (se 1 (by rfl) ⟨2026202, by rfl⟩ : syracuseStep 2701603 = 4052405) B4052405
theorem B3602137 : Blo 2133435 3602137 := bstep (se 2 (by rfl) ⟨1350801, by rfl⟩ : syracuseStep 3602137 = 2701603) B2701603
theorem B4802849 : Blo 2133435 4802849 := bstep (se 2 (by rfl) ⟨1801068, by rfl⟩ : syracuseStep 4802849 = 3602137) B3602137
theorem B3201899 : Blo 2133435 3201899 := bstep (se 1 (by rfl) ⟨2401424, by rfl⟩ : syracuseStep 3201899 = 4802849) B4802849
theorem B2134599 : Blo 2133435 2134599 := bstep (se 1 (by rfl) ⟨1600949, by rfl⟩ : syracuseStep 2134599 = 3201899) B3201899
theorem B2401429 : Blo 2133435 2401429 := bbase (se 6 (by rfl) ⟨56283, by rfl⟩ : syracuseStep 2401429 = 112567) (by norm_num)
theorem B3201905 : Blo 2133435 3201905 := bstep (se 2 (by rfl) ⟨1200714, by rfl⟩ : syracuseStep 3201905 = 2401429) B2401429
theorem B2134603 : Blo 2133435 2134603 := bstep (se 1 (by rfl) ⟨1600952, by rfl⟩ : syracuseStep 2134603 = 3201905) B3201905
theorem B2701613 : Blo 2133435 2701613 := bbase (se 3 (by rfl) ⟨506552, by rfl⟩ : syracuseStep 2701613 = 1013105) (by norm_num)
theorem B7204301 : Blo 2133435 7204301 := bstep (se 3 (by rfl) ⟨1350806, by rfl⟩ : syracuseStep 7204301 = 2701613) B2701613
theorem B4802867 : Blo 2133435 4802867 := bstep (se 1 (by rfl) ⟨3602150, by rfl⟩ : syracuseStep 4802867 = 7204301) B7204301
theorem B3201911 : Blo 2133435 3201911 := bstep (se 1 (by rfl) ⟨2401433, by rfl⟩ : syracuseStep 3201911 = 4802867) B4802867
theorem B2134607 : Blo 2133435 2134607 := bstep (se 1 (by rfl) ⟨1600955, by rfl⟩ : syracuseStep 2134607 = 3201911) B3201911
theorem B3201917 : Blo 2133435 3201917 := bbase (se 3 (by rfl) ⟨600359, by rfl⟩ : syracuseStep 3201917 = 1200719) (by norm_num)
theorem B2134611 : Blo 2133435 2134611 := bstep (se 1 (by rfl) ⟨1600958, by rfl⟩ : syracuseStep 2134611 = 3201917) B3201917
theorem B4802885 : Blo 2133435 4802885 := bbase (se 4 (by rfl) ⟨450270, by rfl⟩ : syracuseStep 4802885 = 900541) (by norm_num)
theorem B3201923 : Blo 2133435 3201923 := bstep (se 1 (by rfl) ⟨2401442, by rfl⟩ : syracuseStep 3201923 = 4802885) B4802885
theorem B2134615 : Blo 2133435 2134615 := bstep (se 1 (by rfl) ⟨1600961, by rfl⟩ : syracuseStep 2134615 = 3201923) B3201923
theorem B10257749 : Blo 2133435 10257749 := bbase (se 12 (by rfl) ⟨3756, by rfl⟩ : syracuseStep 10257749 = 7513) (by norm_num)
theorem B6838499 : Blo 2133435 6838499 := bstep (se 1 (by rfl) ⟨5128874, by rfl⟩ : syracuseStep 6838499 = 10257749) B10257749
theorem B4558999 : Blo 2133435 4558999 := bstep (se 1 (by rfl) ⟨3419249, by rfl⟩ : syracuseStep 4558999 = 6838499) B6838499
theorem B6078665 : Blo 2133435 6078665 := bstep (se 2 (by rfl) ⟨2279499, by rfl⟩ : syracuseStep 6078665 = 4558999) B4558999
theorem B4052443 : Blo 2133435 4052443 := bstep (se 1 (by rfl) ⟨3039332, by rfl⟩ : syracuseStep 4052443 = 6078665) B6078665
theorem B5403257 : Blo 2133435 5403257 := bstep (se 2 (by rfl) ⟨2026221, by rfl⟩ : syracuseStep 5403257 = 4052443) B4052443
theorem B3602171 : Blo 2133435 3602171 := bstep (se 1 (by rfl) ⟨2701628, by rfl⟩ : syracuseStep 3602171 = 5403257) B5403257
theorem B2401447 : Blo 2133435 2401447 := bstep (se 1 (by rfl) ⟨1801085, by rfl⟩ : syracuseStep 2401447 = 3602171) B3602171
theorem B3201929 : Blo 2133435 3201929 := bstep (se 2 (by rfl) ⟨1200723, by rfl⟩ : syracuseStep 3201929 = 2401447) B2401447
theorem B2134619 : Blo 2133435 2134619 := bstep (se 1 (by rfl) ⟨1600964, by rfl⟩ : syracuseStep 2134619 = 3201929) B3201929
theorem B10806533 : Blo 2133435 10806533 := bbase (se 4 (by rfl) ⟨1013112, by rfl⟩ : syracuseStep 10806533 = 2026225) (by norm_num)
theorem B7204355 : Blo 2133435 7204355 := bstep (se 1 (by rfl) ⟨5403266, by rfl⟩ : syracuseStep 7204355 = 10806533) B10806533
theorem B4802903 : Blo 2133435 4802903 := bstep (se 1 (by rfl) ⟨3602177, by rfl⟩ : syracuseStep 4802903 = 7204355) B7204355
theorem B3201935 : Blo 2133435 3201935 := bstep (se 1 (by rfl) ⟨2401451, by rfl⟩ : syracuseStep 3201935 = 4802903) B4802903
theorem B2134623 : Blo 2133435 2134623 := bstep (se 1 (by rfl) ⟨1600967, by rfl⟩ : syracuseStep 2134623 = 3201935) B3201935
theorem B3201941 : Blo 2133435 3201941 := bbase (se 6 (by rfl) ⟨75045, by rfl⟩ : syracuseStep 3201941 = 150091) (by norm_num)
theorem B2134627 : Blo 2133435 2134627 := bstep (se 1 (by rfl) ⟨1600970, by rfl⟩ : syracuseStep 2134627 = 3201941) B3201941
theorem B12157397 : Blo 2133435 12157397 := bbase (se 7 (by rfl) ⟨142469, by rfl⟩ : syracuseStep 12157397 = 284939) (by norm_num)
theorem B8104931 : Blo 2133435 8104931 := bstep (se 1 (by rfl) ⟨6078698, by rfl⟩ : syracuseStep 8104931 = 12157397) B12157397
theorem B5403287 : Blo 2133435 5403287 := bstep (se 1 (by rfl) ⟨4052465, by rfl⟩ : syracuseStep 5403287 = 8104931) B8104931
theorem B3602191 : Blo 2133435 3602191 := bstep (se 1 (by rfl) ⟨2701643, by rfl⟩ : syracuseStep 3602191 = 5403287) B5403287
theorem B4802921 : Blo 2133435 4802921 := bstep (se 2 (by rfl) ⟨1801095, by rfl⟩ : syracuseStep 4802921 = 3602191) B3602191
theorem B3201947 : Blo 2133435 3201947 := bstep (se 1 (by rfl) ⟨2401460, by rfl⟩ : syracuseStep 3201947 = 4802921) B4802921
theorem B2134631 : Blo 2133435 2134631 := bstep (se 1 (by rfl) ⟨1600973, by rfl⟩ : syracuseStep 2134631 = 3201947) B3201947
theorem B2401465 : Blo 2133435 2401465 := bbase (se 2 (by rfl) ⟨900549, by rfl⟩ : syracuseStep 2401465 = 1801099) (by norm_num)
theorem B3201953 : Blo 2133435 3201953 := bstep (se 2 (by rfl) ⟨1200732, by rfl⟩ : syracuseStep 3201953 = 2401465) B2401465
theorem B2134635 : Blo 2133435 2134635 := bstep (se 1 (by rfl) ⟨1600976, by rfl⟩ : syracuseStep 2134635 = 3201953) B3201953
theorem B2564461 : Blo 2133435 2564461 := bbase (se 3 (by rfl) ⟨480836, by rfl⟩ : syracuseStep 2564461 = 961673) (by norm_num)
theorem B3419281 : Blo 2133435 3419281 := bstep (se 2 (by rfl) ⟨1282230, by rfl⟩ : syracuseStep 3419281 = 2564461) B2564461
theorem B4559041 : Blo 2133435 4559041 := bstep (se 2 (by rfl) ⟨1709640, by rfl⟩ : syracuseStep 4559041 = 3419281) B3419281
theorem B6078721 : Blo 2133435 6078721 := bstep (se 2 (by rfl) ⟨2279520, by rfl⟩ : syracuseStep 6078721 = 4559041) B4559041
theorem B8104961 : Blo 2133435 8104961 := bstep (se 2 (by rfl) ⟨3039360, by rfl⟩ : syracuseStep 8104961 = 6078721) B6078721
theorem B5403307 : Blo 2133435 5403307 := bstep (se 1 (by rfl) ⟨4052480, by rfl⟩ : syracuseStep 5403307 = 8104961) B8104961
theorem B7204409 : Blo 2133435 7204409 := bstep (se 2 (by rfl) ⟨2701653, by rfl⟩ : syracuseStep 7204409 = 5403307) B5403307
theorem B4802939 : Blo 2133435 4802939 := bstep (se 1 (by rfl) ⟨3602204, by rfl⟩ : syracuseStep 4802939 = 7204409) B7204409
theorem B3201959 : Blo 2133435 3201959 := bstep (se 1 (by rfl) ⟨2401469, by rfl⟩ : syracuseStep 3201959 = 4802939) B4802939
theorem B2134639 : Blo 2133435 2134639 := bstep (se 1 (by rfl) ⟨1600979, by rfl⟩ : syracuseStep 2134639 = 3201959) B3201959
theorem B3201965 : Blo 2133435 3201965 := bbase (se 3 (by rfl) ⟨600368, by rfl⟩ : syracuseStep 3201965 = 1200737) (by norm_num)
theorem B2134643 : Blo 2133435 2134643 := bstep (se 1 (by rfl) ⟨1600982, by rfl⟩ : syracuseStep 2134643 = 3201965) B3201965
theorem B4802957 : Blo 2133435 4802957 := bbase (se 3 (by rfl) ⟨900554, by rfl⟩ : syracuseStep 4802957 = 1801109) (by norm_num)
theorem B3201971 : Blo 2133435 3201971 := bstep (se 1 (by rfl) ⟨2401478, by rfl⟩ : syracuseStep 3201971 = 4802957) B4802957
theorem B2134647 : Blo 2133435 2134647 := bstep (se 1 (by rfl) ⟨1600985, by rfl⟩ : syracuseStep 2134647 = 3201971) B3201971
theorem B2701669 : Blo 2133435 2701669 := bbase (se 4 (by rfl) ⟨253281, by rfl⟩ : syracuseStep 2701669 = 506563) (by norm_num)
theorem B3602225 : Blo 2133435 3602225 := bstep (se 2 (by rfl) ⟨1350834, by rfl⟩ : syracuseStep 3602225 = 2701669) B2701669
theorem B2401483 : Blo 2133435 2401483 := bstep (se 1 (by rfl) ⟨1801112, by rfl⟩ : syracuseStep 2401483 = 3602225) B3602225
theorem B3201977 : Blo 2133435 3201977 := bstep (se 2 (by rfl) ⟨1200741, by rfl⟩ : syracuseStep 3201977 = 2401483) B2401483
theorem B2134651 : Blo 2133435 2134651 := bstep (se 1 (by rfl) ⟨1600988, by rfl⟩ : syracuseStep 2134651 = 3201977) B3201977
theorem B13863829 : Blo 2133435 13863829 := bbase (se 6 (by rfl) ⟨324933, by rfl⟩ : syracuseStep 13863829 = 649867) (by norm_num)
theorem B18485105 : Blo 2133435 18485105 := bstep (se 2 (by rfl) ⟨6931914, by rfl⟩ : syracuseStep 18485105 = 13863829) B13863829
theorem B49293613 : Blo 2133435 49293613 := bstep (se 3 (by rfl) ⟨9242552, by rfl⟩ : syracuseStep 49293613 = 18485105) B18485105
theorem B65724817 : Blo 2133435 65724817 := bstep (se 2 (by rfl) ⟨24646806, by rfl⟩ : syracuseStep 65724817 = 49293613) B49293613
theorem B87633089 : Blo 2133435 87633089 := bstep (se 2 (by rfl) ⟨32862408, by rfl⟩ : syracuseStep 87633089 = 65724817) B65724817
theorem B58422059 : Blo 2133435 58422059 := bstep (se 1 (by rfl) ⟨43816544, by rfl⟩ : syracuseStep 58422059 = 87633089) B87633089
theorem B38948039 : Blo 2133435 38948039 := bstep (se 1 (by rfl) ⟨29211029, by rfl⟩ : syracuseStep 38948039 = 58422059) B58422059
theorem B25965359 : Blo 2133435 25965359 := bstep (se 1 (by rfl) ⟨19474019, by rfl⟩ : syracuseStep 25965359 = 38948039) B38948039
theorem B17310239 : Blo 2133435 17310239 := bstep (se 1 (by rfl) ⟨12982679, by rfl⟩ : syracuseStep 17310239 = 25965359) B25965359
theorem B11540159 : Blo 2133435 11540159 := bstep (se 1 (by rfl) ⟨8655119, by rfl⟩ : syracuseStep 11540159 = 17310239) B17310239
theorem B7693439 : Blo 2133435 7693439 := bstep (se 1 (by rfl) ⟨5770079, by rfl⟩ : syracuseStep 7693439 = 11540159) B11540159
theorem B20515837 : Blo 2133435 20515837 := bstep (se 3 (by rfl) ⟨3846719, by rfl⟩ : syracuseStep 20515837 = 7693439) B7693439
theorem B27354449 : Blo 2133435 27354449 := bstep (se 2 (by rfl) ⟨10257918, by rfl⟩ : syracuseStep 27354449 = 20515837) B20515837
theorem B18236299 : Blo 2133435 18236299 := bstep (se 1 (by rfl) ⟨13677224, by rfl⟩ : syracuseStep 18236299 = 27354449) B27354449
theorem B24315065 : Blo 2133435 24315065 := bstep (se 2 (by rfl) ⟨9118149, by rfl⟩ : syracuseStep 24315065 = 18236299) B18236299
theorem B16210043 : Blo 2133435 16210043 := bstep (se 1 (by rfl) ⟨12157532, by rfl⟩ : syracuseStep 16210043 = 24315065) B24315065
theorem B10806695 : Blo 2133435 10806695 := bstep (se 1 (by rfl) ⟨8105021, by rfl⟩ : syracuseStep 10806695 = 16210043) B16210043
theorem B7204463 : Blo 2133435 7204463 := bstep (se 1 (by rfl) ⟨5403347, by rfl⟩ : syracuseStep 7204463 = 10806695) B10806695
theorem B4802975 : Blo 2133435 4802975 := bstep (se 1 (by rfl) ⟨3602231, by rfl⟩ : syracuseStep 4802975 = 7204463) B7204463
theorem B3201983 : Blo 2133435 3201983 := bstep (se 1 (by rfl) ⟨2401487, by rfl⟩ : syracuseStep 3201983 = 4802975) B4802975
theorem B2134655 : Blo 2133435 2134655 := bstep (se 1 (by rfl) ⟨1600991, by rfl⟩ : syracuseStep 2134655 = 3201983) B3201983
theorem B3201989 : Blo 2133435 3201989 := bbase (se 4 (by rfl) ⟨300186, by rfl⟩ : syracuseStep 3201989 = 600373) (by norm_num)
theorem B2134659 : Blo 2133435 2134659 := bstep (se 1 (by rfl) ⟨1600994, by rfl⟩ : syracuseStep 2134659 = 3201989) B3201989
theorem B3602245 : Blo 2133435 3602245 := bbase (se 4 (by rfl) ⟨337710, by rfl⟩ : syracuseStep 3602245 = 675421) (by norm_num)
theorem B4802993 : Blo 2133435 4802993 := bstep (se 2 (by rfl) ⟨1801122, by rfl⟩ : syracuseStep 4802993 = 3602245) B3602245
theorem B3201995 : Blo 2133435 3201995 := bstep (se 1 (by rfl) ⟨2401496, by rfl⟩ : syracuseStep 3201995 = 4802993) B4802993
theorem B2134663 : Blo 2133435 2134663 := bstep (se 1 (by rfl) ⟨1600997, by rfl⟩ : syracuseStep 2134663 = 3201995) B3201995
theorem B2401501 : Blo 2133435 2401501 := bbase (se 3 (by rfl) ⟨450281, by rfl⟩ : syracuseStep 2401501 = 900563) (by norm_num)
theorem B3202001 : Blo 2133435 3202001 := bstep (se 2 (by rfl) ⟨1200750, by rfl⟩ : syracuseStep 3202001 = 2401501) B2401501
theorem B2134667 : Blo 2133435 2134667 := bstep (se 1 (by rfl) ⟨1601000, by rfl⟩ : syracuseStep 2134667 = 3202001) B3202001
theorem B7204517 : Blo 2133435 7204517 := bbase (se 4 (by rfl) ⟨675423, by rfl⟩ : syracuseStep 7204517 = 1350847) (by norm_num)
theorem B4803011 : Blo 2133435 4803011 := bstep (se 1 (by rfl) ⟨3602258, by rfl⟩ : syracuseStep 4803011 = 7204517) B7204517
theorem B3202007 : Blo 2133435 3202007 := bstep (se 1 (by rfl) ⟨2401505, by rfl⟩ : syracuseStep 3202007 = 4803011) B4803011
theorem B2134671 : Blo 2133435 2134671 := bstep (se 1 (by rfl) ⟨1601003, by rfl⟩ : syracuseStep 2134671 = 3202007) B3202007
theorem B3202013 : Blo 2133435 3202013 := bbase (se 3 (by rfl) ⟨600377, by rfl⟩ : syracuseStep 3202013 = 1200755) (by norm_num)
theorem B2134675 : Blo 2133435 2134675 := bstep (se 1 (by rfl) ⟨1601006, by rfl⟩ : syracuseStep 2134675 = 3202013) B3202013
theorem B4803029 : Blo 2133435 4803029 := bbase (se 7 (by rfl) ⟨56285, by rfl⟩ : syracuseStep 4803029 = 112571) (by norm_num)
theorem B3202019 : Blo 2133435 3202019 := bstep (se 1 (by rfl) ⟨2401514, by rfl⟩ : syracuseStep 3202019 = 4803029) B4803029
theorem B2134679 : Blo 2133435 2134679 := bstep (se 1 (by rfl) ⟨1601009, by rfl⟩ : syracuseStep 2134679 = 3202019) B3202019
theorem B2434285 : Blo 2133435 2434285 := bbase (se 3 (by rfl) ⟨456428, by rfl⟩ : syracuseStep 2434285 = 912857) (by norm_num)
theorem B3245713 : Blo 2133435 3245713 := bstep (se 2 (by rfl) ⟨1217142, by rfl⟩ : syracuseStep 3245713 = 2434285) B2434285
theorem B69241877 : Blo 2133435 69241877 := bstep (se 6 (by rfl) ⟨1622856, by rfl⟩ : syracuseStep 69241877 = 3245713) B3245713
theorem B46161251 : Blo 2133435 46161251 := bstep (se 1 (by rfl) ⟨34620938, by rfl⟩ : syracuseStep 46161251 = 69241877) B69241877
theorem B30774167 : Blo 2133435 30774167 := bstep (se 1 (by rfl) ⟨23080625, by rfl⟩ : syracuseStep 30774167 = 46161251) B46161251
theorem B20516111 : Blo 2133435 20516111 := bstep (se 1 (by rfl) ⟨15387083, by rfl⟩ : syracuseStep 20516111 = 30774167) B30774167
theorem B13677407 : Blo 2133435 13677407 := bstep (se 1 (by rfl) ⟨10258055, by rfl⟩ : syracuseStep 13677407 = 20516111) B20516111
theorem B9118271 : Blo 2133435 9118271 := bstep (se 1 (by rfl) ⟨6838703, by rfl⟩ : syracuseStep 9118271 = 13677407) B13677407
theorem B6078847 : Blo 2133435 6078847 := bstep (se 1 (by rfl) ⟨4559135, by rfl⟩ : syracuseStep 6078847 = 9118271) B9118271
theorem B8105129 : Blo 2133435 8105129 := bstep (se 2 (by rfl) ⟨3039423, by rfl⟩ : syracuseStep 8105129 = 6078847) B6078847
theorem B5403419 : Blo 2133435 5403419 := bstep (se 1 (by rfl) ⟨4052564, by rfl⟩ : syracuseStep 5403419 = 8105129) B8105129
theorem B3602279 : Blo 2133435 3602279 := bstep (se 1 (by rfl) ⟨2701709, by rfl⟩ : syracuseStep 3602279 = 5403419) B5403419
theorem B2401519 : Blo 2133435 2401519 := bstep (se 1 (by rfl) ⟨1801139, by rfl⟩ : syracuseStep 2401519 = 3602279) B3602279
theorem B3202025 : Blo 2133435 3202025 := bstep (se 2 (by rfl) ⟨1200759, by rfl⟩ : syracuseStep 3202025 = 2401519) B2401519
theorem B2134683 : Blo 2133435 2134683 := bstep (se 1 (by rfl) ⟨1601012, by rfl⟩ : syracuseStep 2134683 = 3202025) B3202025
theorem B7302869 : Blo 2133435 7302869 := bbase (se 7 (by rfl) ⟨85580, by rfl⟩ : syracuseStep 7302869 = 171161) (by norm_num)
theorem B4868579 : Blo 2133435 4868579 := bstep (se 1 (by rfl) ⟨3651434, by rfl⟩ : syracuseStep 4868579 = 7302869) B7302869
theorem B3245719 : Blo 2133435 3245719 := bstep (se 1 (by rfl) ⟨2434289, by rfl⟩ : syracuseStep 3245719 = 4868579) B4868579
theorem B4327625 : Blo 2133435 4327625 := bstep (se 2 (by rfl) ⟨1622859, by rfl⟩ : syracuseStep 4327625 = 3245719) B3245719
theorem B11540333 : Blo 2133435 11540333 := bstep (se 3 (by rfl) ⟨2163812, by rfl⟩ : syracuseStep 11540333 = 4327625) B4327625
theorem B7693555 : Blo 2133435 7693555 := bstep (se 1 (by rfl) ⟨5770166, by rfl⟩ : syracuseStep 7693555 = 11540333) B11540333
theorem B10258073 : Blo 2133435 10258073 := bstep (se 2 (by rfl) ⟨3846777, by rfl⟩ : syracuseStep 10258073 = 7693555) B7693555
theorem B6838715 : Blo 2133435 6838715 := bstep (se 1 (by rfl) ⟨5129036, by rfl⟩ : syracuseStep 6838715 = 10258073) B10258073
theorem B18236573 : Blo 2133435 18236573 := bstep (se 3 (by rfl) ⟨3419357, by rfl⟩ : syracuseStep 18236573 = 6838715) B6838715
theorem B12157715 : Blo 2133435 12157715 := bstep (se 1 (by rfl) ⟨9118286, by rfl⟩ : syracuseStep 12157715 = 18236573) B18236573
theorem B8105143 : Blo 2133435 8105143 := bstep (se 1 (by rfl) ⟨6078857, by rfl⟩ : syracuseStep 8105143 = 12157715) B12157715
theorem B10806857 : Blo 2133435 10806857 := bstep (se 2 (by rfl) ⟨4052571, by rfl⟩ : syracuseStep 10806857 = 8105143) B8105143
theorem B7204571 : Blo 2133435 7204571 := bstep (se 1 (by rfl) ⟨5403428, by rfl⟩ : syracuseStep 7204571 = 10806857) B10806857
theorem B4803047 : Blo 2133435 4803047 := bstep (se 1 (by rfl) ⟨3602285, by rfl⟩ : syracuseStep 4803047 = 7204571) B7204571
theorem B3202031 : Blo 2133435 3202031 := bstep (se 1 (by rfl) ⟨2401523, by rfl⟩ : syracuseStep 3202031 = 4803047) B4803047
theorem B2134687 : Blo 2133435 2134687 := bstep (se 1 (by rfl) ⟨1601015, by rfl⟩ : syracuseStep 2134687 = 3202031) B3202031
theorem B3202037 : Blo 2133435 3202037 := bbase (se 5 (by rfl) ⟨150095, by rfl⟩ : syracuseStep 3202037 = 300191) (by norm_num)
theorem B2134691 : Blo 2133435 2134691 := bstep (se 1 (by rfl) ⟨1601018, by rfl⟩ : syracuseStep 2134691 = 3202037) B3202037
theorem B2467513 : Blo 2133435 2467513 := bbase (se 2 (by rfl) ⟨925317, by rfl⟩ : syracuseStep 2467513 = 1850635) (by norm_num)
theorem B13160069 : Blo 2133435 13160069 := bstep (se 4 (by rfl) ⟨1233756, by rfl⟩ : syracuseStep 13160069 = 2467513) B2467513
theorem B8773379 : Blo 2133435 8773379 := bstep (se 1 (by rfl) ⟨6580034, by rfl⟩ : syracuseStep 8773379 = 13160069) B13160069
theorem B5848919 : Blo 2133435 5848919 := bstep (se 1 (by rfl) ⟨4386689, by rfl⟩ : syracuseStep 5848919 = 8773379) B8773379
theorem B3899279 : Blo 2133435 3899279 := bstep (se 1 (by rfl) ⟨2924459, by rfl⟩ : syracuseStep 3899279 = 5848919) B5848919
theorem B10398077 : Blo 2133435 10398077 := bstep (se 3 (by rfl) ⟨1949639, by rfl⟩ : syracuseStep 10398077 = 3899279) B3899279
theorem B6932051 : Blo 2133435 6932051 := bstep (se 1 (by rfl) ⟨5199038, by rfl⟩ : syracuseStep 6932051 = 10398077) B10398077
theorem B4621367 : Blo 2133435 4621367 := bstep (se 1 (by rfl) ⟨3466025, by rfl⟩ : syracuseStep 4621367 = 6932051) B6932051
theorem B3080911 : Blo 2133435 3080911 := bstep (se 1 (by rfl) ⟨2310683, by rfl⟩ : syracuseStep 3080911 = 4621367) B4621367
theorem B4107881 : Blo 2133435 4107881 := bstep (se 2 (by rfl) ⟨1540455, by rfl⟩ : syracuseStep 4107881 = 3080911) B3080911
theorem B10954349 : Blo 2133435 10954349 := bstep (se 3 (by rfl) ⟨2053940, by rfl⟩ : syracuseStep 10954349 = 4107881) B4107881
theorem B7302899 : Blo 2133435 7302899 := bstep (se 1 (by rfl) ⟨5477174, by rfl⟩ : syracuseStep 7302899 = 10954349) B10954349
theorem B4868599 : Blo 2133435 4868599 := bstep (se 1 (by rfl) ⟨3651449, by rfl⟩ : syracuseStep 4868599 = 7302899) B7302899
theorem B6491465 : Blo 2133435 6491465 := bstep (se 2 (by rfl) ⟨2434299, by rfl⟩ : syracuseStep 6491465 = 4868599) B4868599
theorem B4327643 : Blo 2133435 4327643 := bstep (se 1 (by rfl) ⟨3245732, by rfl⟩ : syracuseStep 4327643 = 6491465) B6491465
theorem B2885095 : Blo 2133435 2885095 := bstep (se 1 (by rfl) ⟨2163821, by rfl⟩ : syracuseStep 2885095 = 4327643) B4327643
theorem B3846793 : Blo 2133435 3846793 := bstep (se 2 (by rfl) ⟨1442547, by rfl⟩ : syracuseStep 3846793 = 2885095) B2885095
theorem B5129057 : Blo 2133435 5129057 := bstep (se 2 (by rfl) ⟨1923396, by rfl⟩ : syracuseStep 5129057 = 3846793) B3846793
theorem B3419371 : Blo 2133435 3419371 := bstep (se 1 (by rfl) ⟨2564528, by rfl⟩ : syracuseStep 3419371 = 5129057) B5129057
theorem B4559161 : Blo 2133435 4559161 := bstep (se 2 (by rfl) ⟨1709685, by rfl⟩ : syracuseStep 4559161 = 3419371) B3419371
theorem B6078881 : Blo 2133435 6078881 := bstep (se 2 (by rfl) ⟨2279580, by rfl⟩ : syracuseStep 6078881 = 4559161) B4559161
theorem B4052587 : Blo 2133435 4052587 := bstep (se 1 (by rfl) ⟨3039440, by rfl⟩ : syracuseStep 4052587 = 6078881) B6078881
theorem B5403449 : Blo 2133435 5403449 := bstep (se 2 (by rfl) ⟨2026293, by rfl⟩ : syracuseStep 5403449 = 4052587) B4052587
theorem B3602299 : Blo 2133435 3602299 := bstep (se 1 (by rfl) ⟨2701724, by rfl⟩ : syracuseStep 3602299 = 5403449) B5403449
theorem B4803065 : Blo 2133435 4803065 := bstep (se 2 (by rfl) ⟨1801149, by rfl⟩ : syracuseStep 4803065 = 3602299) B3602299
theorem B3202043 : Blo 2133435 3202043 := bstep (se 1 (by rfl) ⟨2401532, by rfl⟩ : syracuseStep 3202043 = 4803065) B4803065
theorem B2134695 : Blo 2133435 2134695 := bstep (se 1 (by rfl) ⟨1601021, by rfl⟩ : syracuseStep 2134695 = 3202043) B3202043
theorem B2401537 : Blo 2133435 2401537 := bbase (se 2 (by rfl) ⟨900576, by rfl⟩ : syracuseStep 2401537 = 1801153) (by norm_num)
theorem B3202049 : Blo 2133435 3202049 := bstep (se 2 (by rfl) ⟨1200768, by rfl⟩ : syracuseStep 3202049 = 2401537) B2401537
theorem B2134699 : Blo 2133435 2134699 := bstep (se 1 (by rfl) ⟨1601024, by rfl⟩ : syracuseStep 2134699 = 3202049) B3202049
theorem B5403469 : Blo 2133435 5403469 := bbase (se 3 (by rfl) ⟨1013150, by rfl⟩ : syracuseStep 5403469 = 2026301) (by norm_num)
theorem B7204625 : Blo 2133435 7204625 := bstep (se 2 (by rfl) ⟨2701734, by rfl⟩ : syracuseStep 7204625 = 5403469) B5403469
theorem B4803083 : Blo 2133435 4803083 := bstep (se 1 (by rfl) ⟨3602312, by rfl⟩ : syracuseStep 4803083 = 7204625) B7204625
theorem B3202055 : Blo 2133435 3202055 := bstep (se 1 (by rfl) ⟨2401541, by rfl⟩ : syracuseStep 3202055 = 4803083) B4803083
theorem B2134703 : Blo 2133435 2134703 := bstep (se 1 (by rfl) ⟨1601027, by rfl⟩ : syracuseStep 2134703 = 3202055) B3202055
theorem B3202061 : Blo 2133435 3202061 := bbase (se 3 (by rfl) ⟨600386, by rfl⟩ : syracuseStep 3202061 = 1200773) (by norm_num)
theorem B2134707 : Blo 2133435 2134707 := bstep (se 1 (by rfl) ⟨1601030, by rfl⟩ : syracuseStep 2134707 = 3202061) B3202061
theorem B4803101 : Blo 2133435 4803101 := bbase (se 3 (by rfl) ⟨900581, by rfl⟩ : syracuseStep 4803101 = 1801163) (by norm_num)
theorem B3202067 : Blo 2133435 3202067 := bstep (se 1 (by rfl) ⟨2401550, by rfl⟩ : syracuseStep 3202067 = 4803101) B4803101
theorem B2134711 : Blo 2133435 2134711 := bstep (se 1 (by rfl) ⟨1601033, by rfl⟩ : syracuseStep 2134711 = 3202067) B3202067
theorem B3602333 : Blo 2133435 3602333 := bbase (se 3 (by rfl) ⟨675437, by rfl⟩ : syracuseStep 3602333 = 1350875) (by norm_num)
theorem B2401555 : Blo 2133435 2401555 := bstep (se 1 (by rfl) ⟨1801166, by rfl⟩ : syracuseStep 2401555 = 3602333) B3602333
theorem B3202073 : Blo 2133435 3202073 := bstep (se 2 (by rfl) ⟨1200777, by rfl⟩ : syracuseStep 3202073 = 2401555) B2401555
theorem B2134715 : Blo 2133435 2134715 := bstep (se 1 (by rfl) ⟨1601036, by rfl⟩ : syracuseStep 2134715 = 3202073) B3202073
theorem B2163845 : Blo 2133435 2163845 := bbase (se 4 (by rfl) ⟨202860, by rfl⟩ : syracuseStep 2163845 = 405721) (by norm_num)
theorem B5770253 : Blo 2133435 5770253 := bstep (se 3 (by rfl) ⟨1081922, by rfl⟩ : syracuseStep 5770253 = 2163845) B2163845
theorem B3846835 : Blo 2133435 3846835 := bstep (se 1 (by rfl) ⟨2885126, by rfl⟩ : syracuseStep 3846835 = 5770253) B5770253
theorem B20516453 : Blo 2133435 20516453 := bstep (se 4 (by rfl) ⟨1923417, by rfl⟩ : syracuseStep 20516453 = 3846835) B3846835
theorem B13677635 : Blo 2133435 13677635 := bstep (se 1 (by rfl) ⟨10258226, by rfl⟩ : syracuseStep 13677635 = 20516453) B20516453
theorem B9118423 : Blo 2133435 9118423 := bstep (se 1 (by rfl) ⟨6838817, by rfl⟩ : syracuseStep 9118423 = 13677635) B13677635
theorem B12157897 : Blo 2133435 12157897 := bstep (se 2 (by rfl) ⟨4559211, by rfl⟩ : syracuseStep 12157897 = 9118423) B9118423
theorem B16210529 : Blo 2133435 16210529 := bstep (se 2 (by rfl) ⟨6078948, by rfl⟩ : syracuseStep 16210529 = 12157897) B12157897
theorem B10807019 : Blo 2133435 10807019 := bstep (se 1 (by rfl) ⟨8105264, by rfl⟩ : syracuseStep 10807019 = 16210529) B16210529
theorem B7204679 : Blo 2133435 7204679 := bstep (se 1 (by rfl) ⟨5403509, by rfl⟩ : syracuseStep 7204679 = 10807019) B10807019
theorem B4803119 : Blo 2133435 4803119 := bstep (se 1 (by rfl) ⟨3602339, by rfl⟩ : syracuseStep 4803119 = 7204679) B7204679
theorem B3202079 : Blo 2133435 3202079 := bstep (se 1 (by rfl) ⟨2401559, by rfl⟩ : syracuseStep 3202079 = 4803119) B4803119
theorem B2134719 : Blo 2133435 2134719 := bstep (se 1 (by rfl) ⟨1601039, by rfl⟩ : syracuseStep 2134719 = 3202079) B3202079
theorem B3202085 : Blo 2133435 3202085 := bbase (se 4 (by rfl) ⟨300195, by rfl⟩ : syracuseStep 3202085 = 600391) (by norm_num)
theorem B2134723 : Blo 2133435 2134723 := bstep (se 1 (by rfl) ⟨1601042, by rfl⟩ : syracuseStep 2134723 = 3202085) B3202085
theorem B2701765 : Blo 2133435 2701765 := bbase (se 4 (by rfl) ⟨253290, by rfl⟩ : syracuseStep 2701765 = 506581) (by norm_num)
theorem B3602353 : Blo 2133435 3602353 := bstep (se 2 (by rfl) ⟨1350882, by rfl⟩ : syracuseStep 3602353 = 2701765) B2701765
theorem B4803137 : Blo 2133435 4803137 := bstep (se 2 (by rfl) ⟨1801176, by rfl⟩ : syracuseStep 4803137 = 3602353) B3602353
theorem B3202091 : Blo 2133435 3202091 := bstep (se 1 (by rfl) ⟨2401568, by rfl⟩ : syracuseStep 3202091 = 4803137) B4803137
theorem B2134727 : Blo 2133435 2134727 := bstep (se 1 (by rfl) ⟨1601045, by rfl⟩ : syracuseStep 2134727 = 3202091) B3202091
theorem B2401573 : Blo 2133435 2401573 := bbase (se 4 (by rfl) ⟨225147, by rfl⟩ : syracuseStep 2401573 = 450295) (by norm_num)
theorem B3202097 : Blo 2133435 3202097 := bstep (se 2 (by rfl) ⟨1200786, by rfl⟩ : syracuseStep 3202097 = 2401573) B2401573
theorem B2134731 : Blo 2133435 2134731 := bstep (se 1 (by rfl) ⟨1601048, by rfl⟩ : syracuseStep 2134731 = 3202097) B3202097
theorem B2885149 : Blo 2133435 2885149 := bbase (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) (by norm_num)
theorem B3846865 : Blo 2133435 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B5129153 : Blo 2133435 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B3419435 : Blo 2133435 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B9118493 : Blo 2133435 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B6078995 : Blo 2133435 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B4052663 : Blo 2133435 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B2701775 : Blo 2133435 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B7204733 : Blo 2133435 7204733 := bstep (se 3 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 7204733 = 2701775) B2701775
theorem B4803155 : Blo 2133435 4803155 := bstep (se 1 (by rfl) ⟨3602366, by rfl⟩ : syracuseStep 4803155 = 7204733) B7204733
theorem B3202103 : Blo 2133435 3202103 := bstep (se 1 (by rfl) ⟨2401577, by rfl⟩ : syracuseStep 3202103 = 4803155) B4803155
theorem B2134735 : Blo 2133435 2134735 := bstep (se 1 (by rfl) ⟨1601051, by rfl⟩ : syracuseStep 2134735 = 3202103) B3202103
theorem B3202109 : Blo 2133435 3202109 := bbase (se 3 (by rfl) ⟨600395, by rfl⟩ : syracuseStep 3202109 = 1200791) (by norm_num)
theorem B2134739 : Blo 2133435 2134739 := bstep (se 1 (by rfl) ⟨1601054, by rfl⟩ : syracuseStep 2134739 = 3202109) B3202109
theorem B4803173 : Blo 2133435 4803173 := bbase (se 4 (by rfl) ⟨450297, by rfl⟩ : syracuseStep 4803173 = 900595) (by norm_num)
theorem B3202115 : Blo 2133435 3202115 := bstep (se 1 (by rfl) ⟨2401586, by rfl⟩ : syracuseStep 3202115 = 4803173) B4803173
theorem B2134743 : Blo 2133435 2134743 := bstep (se 1 (by rfl) ⟨1601057, by rfl⟩ : syracuseStep 2134743 = 3202115) B3202115
theorem B5403581 : Blo 2133435 5403581 := bbase (se 3 (by rfl) ⟨1013171, by rfl⟩ : syracuseStep 5403581 = 2026343) (by norm_num)
theorem B3602387 : Blo 2133435 3602387 := bstep (se 1 (by rfl) ⟨2701790, by rfl⟩ : syracuseStep 3602387 = 5403581) B5403581
theorem B2401591 : Blo 2133435 2401591 := bstep (se 1 (by rfl) ⟨1801193, by rfl⟩ : syracuseStep 2401591 = 3602387) B3602387
theorem B3202121 : Blo 2133435 3202121 := bstep (se 2 (by rfl) ⟨1200795, by rfl⟩ : syracuseStep 3202121 = 2401591) B2401591
theorem B2134747 : Blo 2133435 2134747 := bstep (se 1 (by rfl) ⟨1601060, by rfl⟩ : syracuseStep 2134747 = 3202121) B3202121
theorem B4052693 : Blo 2133435 4052693 := bbase (se 7 (by rfl) ⟨47492, by rfl⟩ : syracuseStep 4052693 = 94985) (by norm_num)
theorem B10807181 : Blo 2133435 10807181 := bstep (se 3 (by rfl) ⟨2026346, by rfl⟩ : syracuseStep 10807181 = 4052693) B4052693
theorem B7204787 : Blo 2133435 7204787 := bstep (se 1 (by rfl) ⟨5403590, by rfl⟩ : syracuseStep 7204787 = 10807181) B10807181
theorem B4803191 : Blo 2133435 4803191 := bstep (se 1 (by rfl) ⟨3602393, by rfl⟩ : syracuseStep 4803191 = 7204787) B7204787
theorem B3202127 : Blo 2133435 3202127 := bstep (se 1 (by rfl) ⟨2401595, by rfl⟩ : syracuseStep 3202127 = 4803191) B4803191
theorem B2134751 : Blo 2133435 2134751 := bstep (se 1 (by rfl) ⟨1601063, by rfl⟩ : syracuseStep 2134751 = 3202127) B3202127
theorem B3202133 : Blo 2133435 3202133 := bbase (se 8 (by rfl) ⟨18762, by rfl⟩ : syracuseStep 3202133 = 37525) (by norm_num)
theorem B2134755 : Blo 2133435 2134755 := bstep (se 1 (by rfl) ⟨1601066, by rfl⟩ : syracuseStep 2134755 = 3202133) B3202133
theorem B2564605 : Blo 2133435 2564605 := bbase (se 3 (by rfl) ⟨480863, by rfl⟩ : syracuseStep 2564605 = 961727) (by norm_num)
theorem B13677893 : Blo 2133435 13677893 := bstep (se 4 (by rfl) ⟨1282302, by rfl⟩ : syracuseStep 13677893 = 2564605) B2564605
theorem B9118595 : Blo 2133435 9118595 := bstep (se 1 (by rfl) ⟨6838946, by rfl⟩ : syracuseStep 9118595 = 13677893) B13677893
theorem B6079063 : Blo 2133435 6079063 := bstep (se 1 (by rfl) ⟨4559297, by rfl⟩ : syracuseStep 6079063 = 9118595) B9118595
theorem B8105417 : Blo 2133435 8105417 := bstep (se 2 (by rfl) ⟨3039531, by rfl⟩ : syracuseStep 8105417 = 6079063) B6079063
theorem B5403611 : Blo 2133435 5403611 := bstep (se 1 (by rfl) ⟨4052708, by rfl⟩ : syracuseStep 5403611 = 8105417) B8105417
theorem B3602407 : Blo 2133435 3602407 := bstep (se 1 (by rfl) ⟨2701805, by rfl⟩ : syracuseStep 3602407 = 5403611) B5403611
theorem B4803209 : Blo 2133435 4803209 := bstep (se 2 (by rfl) ⟨1801203, by rfl⟩ : syracuseStep 4803209 = 3602407) B3602407
theorem B3202139 : Blo 2133435 3202139 := bstep (se 1 (by rfl) ⟨2401604, by rfl⟩ : syracuseStep 3202139 = 4803209) B4803209
theorem B2134759 : Blo 2133435 2134759 := bstep (se 1 (by rfl) ⟨1601069, by rfl⟩ : syracuseStep 2134759 = 3202139) B3202139
theorem B2401609 : Blo 2133435 2401609 := bbase (se 2 (by rfl) ⟨900603, by rfl⟩ : syracuseStep 2401609 = 1801207) (by norm_num)
theorem B3202145 : Blo 2133435 3202145 := bstep (se 2 (by rfl) ⟨1200804, by rfl⟩ : syracuseStep 3202145 = 2401609) B2401609
theorem B2134763 : Blo 2133435 2134763 := bstep (se 1 (by rfl) ⟨1601072, by rfl⟩ : syracuseStep 2134763 = 3202145) B3202145
theorem B5477357 : Blo 2133435 5477357 := bbase (se 3 (by rfl) ⟨1027004, by rfl⟩ : syracuseStep 5477357 = 2054009) (by norm_num)
theorem B3651571 : Blo 2133435 3651571 := bstep (se 1 (by rfl) ⟨2738678, by rfl⟩ : syracuseStep 3651571 = 5477357) B5477357
theorem B4868761 : Blo 2133435 4868761 := bstep (se 2 (by rfl) ⟨1825785, by rfl⟩ : syracuseStep 4868761 = 3651571) B3651571
theorem B6491681 : Blo 2133435 6491681 := bstep (se 2 (by rfl) ⟨2434380, by rfl⟩ : syracuseStep 6491681 = 4868761) B4868761
theorem B4327787 : Blo 2133435 4327787 := bstep (se 1 (by rfl) ⟨3245840, by rfl⟩ : syracuseStep 4327787 = 6491681) B6491681
theorem B11540765 : Blo 2133435 11540765 := bstep (se 3 (by rfl) ⟨2163893, by rfl⟩ : syracuseStep 11540765 = 4327787) B4327787
theorem B30775373 : Blo 2133435 30775373 := bstep (se 3 (by rfl) ⟨5770382, by rfl⟩ : syracuseStep 30775373 = 11540765) B11540765
theorem B20516915 : Blo 2133435 20516915 := bstep (se 1 (by rfl) ⟨15387686, by rfl⟩ : syracuseStep 20516915 = 30775373) B30775373
theorem B13677943 : Blo 2133435 13677943 := bstep (se 1 (by rfl) ⟨10258457, by rfl⟩ : syracuseStep 13677943 = 20516915) B20516915
theorem B18237257 : Blo 2133435 18237257 := bstep (se 2 (by rfl) ⟨6838971, by rfl⟩ : syracuseStep 18237257 = 13677943) B13677943
theorem B12158171 : Blo 2133435 12158171 := bstep (se 1 (by rfl) ⟨9118628, by rfl⟩ : syracuseStep 12158171 = 18237257) B18237257
theorem B8105447 : Blo 2133435 8105447 := bstep (se 1 (by rfl) ⟨6079085, by rfl⟩ : syracuseStep 8105447 = 12158171) B12158171
theorem B5403631 : Blo 2133435 5403631 := bstep (se 1 (by rfl) ⟨4052723, by rfl⟩ : syracuseStep 5403631 = 8105447) B8105447
theorem B7204841 : Blo 2133435 7204841 := bstep (se 2 (by rfl) ⟨2701815, by rfl⟩ : syracuseStep 7204841 = 5403631) B5403631
theorem B4803227 : Blo 2133435 4803227 := bstep (se 1 (by rfl) ⟨3602420, by rfl⟩ : syracuseStep 4803227 = 7204841) B7204841
theorem B3202151 : Blo 2133435 3202151 := bstep (se 1 (by rfl) ⟨2401613, by rfl⟩ : syracuseStep 3202151 = 4803227) B4803227
theorem B2134767 : Blo 2133435 2134767 := bstep (se 1 (by rfl) ⟨1601075, by rfl⟩ : syracuseStep 2134767 = 3202151) B3202151
theorem B3202157 : Blo 2133435 3202157 := bbase (se 3 (by rfl) ⟨600404, by rfl⟩ : syracuseStep 3202157 = 1200809) (by norm_num)
theorem B2134771 : Blo 2133435 2134771 := bstep (se 1 (by rfl) ⟨1601078, by rfl⟩ : syracuseStep 2134771 = 3202157) B3202157
theorem B4803245 : Blo 2133435 4803245 := bbase (se 3 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 4803245 = 1801217) (by norm_num)
theorem B3202163 : Blo 2133435 3202163 := bstep (se 1 (by rfl) ⟨2401622, by rfl⟩ : syracuseStep 3202163 = 4803245) B4803245
theorem B2134775 : Blo 2133435 2134775 := bstep (se 1 (by rfl) ⟨1601081, by rfl⟩ : syracuseStep 2134775 = 3202163) B3202163
theorem B4559341 : Blo 2133435 4559341 := bbase (se 3 (by rfl) ⟨854876, by rfl⟩ : syracuseStep 4559341 = 1709753) (by norm_num)
theorem B6079121 : Blo 2133435 6079121 := bstep (se 2 (by rfl) ⟨2279670, by rfl⟩ : syracuseStep 6079121 = 4559341) B4559341
theorem B4052747 : Blo 2133435 4052747 := bstep (se 1 (by rfl) ⟨3039560, by rfl⟩ : syracuseStep 4052747 = 6079121) B6079121
theorem B2701831 : Blo 2133435 2701831 := bstep (se 1 (by rfl) ⟨2026373, by rfl⟩ : syracuseStep 2701831 = 4052747) B4052747
theorem B3602441 : Blo 2133435 3602441 := bstep (se 2 (by rfl) ⟨1350915, by rfl⟩ : syracuseStep 3602441 = 2701831) B2701831
theorem B2401627 : Blo 2133435 2401627 := bstep (se 1 (by rfl) ⟨1801220, by rfl⟩ : syracuseStep 2401627 = 3602441) B3602441
theorem B3202169 : Blo 2133435 3202169 := bstep (se 2 (by rfl) ⟨1200813, by rfl⟩ : syracuseStep 3202169 = 2401627) B2401627
theorem B2134779 : Blo 2133435 2134779 := bstep (se 1 (by rfl) ⟨1601084, by rfl⟩ : syracuseStep 2134779 = 3202169) B3202169
theorem B4868797 : Blo 2133435 4868797 := bbase (se 3 (by rfl) ⟨912899, by rfl⟩ : syracuseStep 4868797 = 1825799) (by norm_num)
theorem B6491729 : Blo 2133435 6491729 := bstep (se 2 (by rfl) ⟨2434398, by rfl⟩ : syracuseStep 6491729 = 4868797) B4868797
theorem B4327819 : Blo 2133435 4327819 := bstep (se 1 (by rfl) ⟨3245864, by rfl⟩ : syracuseStep 4327819 = 6491729) B6491729
theorem B23081701 : Blo 2133435 23081701 := bstep (se 4 (by rfl) ⟨2163909, by rfl⟩ : syracuseStep 23081701 = 4327819) B4327819
theorem B30775601 : Blo 2133435 30775601 := bstep (se 2 (by rfl) ⟨11540850, by rfl⟩ : syracuseStep 30775601 = 23081701) B23081701
theorem B20517067 : Blo 2133435 20517067 := bstep (se 1 (by rfl) ⟨15387800, by rfl⟩ : syracuseStep 20517067 = 30775601) B30775601
theorem B27356089 : Blo 2133435 27356089 := bstep (se 2 (by rfl) ⟨10258533, by rfl⟩ : syracuseStep 27356089 = 20517067) B20517067
theorem B36474785 : Blo 2133435 36474785 := bstep (se 2 (by rfl) ⟨13678044, by rfl⟩ : syracuseStep 36474785 = 27356089) B27356089
theorem B24316523 : Blo 2133435 24316523 := bstep (se 1 (by rfl) ⟨18237392, by rfl⟩ : syracuseStep 24316523 = 36474785) B36474785
theorem B16211015 : Blo 2133435 16211015 := bstep (se 1 (by rfl) ⟨12158261, by rfl⟩ : syracuseStep 16211015 = 24316523) B24316523
theorem B10807343 : Blo 2133435 10807343 := bstep (se 1 (by rfl) ⟨8105507, by rfl⟩ : syracuseStep 10807343 = 16211015) B16211015
theorem B7204895 : Blo 2133435 7204895 := bstep (se 1 (by rfl) ⟨5403671, by rfl⟩ : syracuseStep 7204895 = 10807343) B10807343
theorem B4803263 : Blo 2133435 4803263 := bstep (se 1 (by rfl) ⟨3602447, by rfl⟩ : syracuseStep 4803263 = 7204895) B7204895
theorem B3202175 : Blo 2133435 3202175 := bstep (se 1 (by rfl) ⟨2401631, by rfl⟩ : syracuseStep 3202175 = 4803263) B4803263
theorem B2134783 : Blo 2133435 2134783 := bstep (se 1 (by rfl) ⟨1601087, by rfl⟩ : syracuseStep 2134783 = 3202175) B3202175
theorem B3202181 : Blo 2133435 3202181 := bbase (se 4 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 3202181 = 600409) (by norm_num)
theorem B2134787 : Blo 2133435 2134787 := bstep (se 1 (by rfl) ⟨1601090, by rfl⟩ : syracuseStep 2134787 = 3202181) B3202181
theorem B3602461 : Blo 2133435 3602461 := bbase (se 3 (by rfl) ⟨675461, by rfl⟩ : syracuseStep 3602461 = 1350923) (by norm_num)
theorem B4803281 : Blo 2133435 4803281 := bstep (se 2 (by rfl) ⟨1801230, by rfl⟩ : syracuseStep 4803281 = 3602461) B3602461
theorem B3202187 : Blo 2133435 3202187 := bstep (se 1 (by rfl) ⟨2401640, by rfl⟩ : syracuseStep 3202187 = 4803281) B4803281
theorem B2134791 : Blo 2133435 2134791 := bstep (se 1 (by rfl) ⟨1601093, by rfl⟩ : syracuseStep 2134791 = 3202187) B3202187
theorem B2401645 : Blo 2133435 2401645 := bbase (se 3 (by rfl) ⟨450308, by rfl⟩ : syracuseStep 2401645 = 900617) (by norm_num)
theorem B3202193 : Blo 2133435 3202193 := bstep (se 2 (by rfl) ⟨1200822, by rfl⟩ : syracuseStep 3202193 = 2401645) B2401645
theorem B2134795 : Blo 2133435 2134795 := bstep (se 1 (by rfl) ⟨1601096, by rfl⟩ : syracuseStep 2134795 = 3202193) B3202193
theorem B7204949 : Blo 2133435 7204949 := bbase (se 8 (by rfl) ⟨42216, by rfl⟩ : syracuseStep 7204949 = 84433) (by norm_num)
theorem B4803299 : Blo 2133435 4803299 := bstep (se 1 (by rfl) ⟨3602474, by rfl⟩ : syracuseStep 4803299 = 7204949) B7204949
theorem B3202199 : Blo 2133435 3202199 := bstep (se 1 (by rfl) ⟨2401649, by rfl⟩ : syracuseStep 3202199 = 4803299) B4803299
theorem B2134799 : Blo 2133435 2134799 := bstep (se 1 (by rfl) ⟨1601099, by rfl⟩ : syracuseStep 2134799 = 3202199) B3202199
theorem B3202205 : Blo 2133435 3202205 := bbase (se 3 (by rfl) ⟨600413, by rfl⟩ : syracuseStep 3202205 = 1200827) (by norm_num)
theorem B2134803 : Blo 2133435 2134803 := bstep (se 1 (by rfl) ⟨1601102, by rfl⟩ : syracuseStep 2134803 = 3202205) B3202205
theorem B4803317 : Blo 2133435 4803317 := bbase (se 5 (by rfl) ⟨225155, by rfl⟩ : syracuseStep 4803317 = 450311) (by norm_num)
theorem B3202211 : Blo 2133435 3202211 := bstep (se 1 (by rfl) ⟨2401658, by rfl⟩ : syracuseStep 3202211 = 4803317) B4803317
theorem B2134807 : Blo 2133435 2134807 := bstep (se 1 (by rfl) ⟨1601105, by rfl⟩ : syracuseStep 2134807 = 3202211) B3202211
theorem B4327877 : Blo 2133435 4327877 := bbase (se 4 (by rfl) ⟨405738, by rfl⟩ : syracuseStep 4327877 = 811477) (by norm_num)
theorem B11541005 : Blo 2133435 11541005 := bstep (se 3 (by rfl) ⟨2163938, by rfl⟩ : syracuseStep 11541005 = 4327877) B4327877
theorem B7694003 : Blo 2133435 7694003 := bstep (se 1 (by rfl) ⟨5770502, by rfl⟩ : syracuseStep 7694003 = 11541005) B11541005
theorem B5129335 : Blo 2133435 5129335 := bstep (se 1 (by rfl) ⟨3847001, by rfl⟩ : syracuseStep 5129335 = 7694003) B7694003
theorem B27356453 : Blo 2133435 27356453 := bstep (se 4 (by rfl) ⟨2564667, by rfl⟩ : syracuseStep 27356453 = 5129335) B5129335
theorem B18237635 : Blo 2133435 18237635 := bstep (se 1 (by rfl) ⟨13678226, by rfl⟩ : syracuseStep 18237635 = 27356453) B27356453
theorem B12158423 : Blo 2133435 12158423 := bstep (se 1 (by rfl) ⟨9118817, by rfl⟩ : syracuseStep 12158423 = 18237635) B18237635
theorem B8105615 : Blo 2133435 8105615 := bstep (se 1 (by rfl) ⟨6079211, by rfl⟩ : syracuseStep 8105615 = 12158423) B12158423
theorem B5403743 : Blo 2133435 5403743 := bstep (se 1 (by rfl) ⟨4052807, by rfl⟩ : syracuseStep 5403743 = 8105615) B8105615
theorem B3602495 : Blo 2133435 3602495 := bstep (se 1 (by rfl) ⟨2701871, by rfl⟩ : syracuseStep 3602495 = 5403743) B5403743
theorem B2401663 : Blo 2133435 2401663 := bstep (se 1 (by rfl) ⟨1801247, by rfl⟩ : syracuseStep 2401663 = 3602495) B3602495
theorem B3202217 : Blo 2133435 3202217 := bstep (se 2 (by rfl) ⟨1200831, by rfl⟩ : syracuseStep 3202217 = 2401663) B2401663
theorem B2134811 : Blo 2133435 2134811 := bstep (se 1 (by rfl) ⟨1601108, by rfl⟩ : syracuseStep 2134811 = 3202217) B3202217
theorem B7798997 : Blo 2133435 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B5199331 : Blo 2133435 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B6932441 : Blo 2133435 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B4621627 : Blo 2133435 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B6162169 : Blo 2133435 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B8216225 : Blo 2133435 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B5477483 : Blo 2133435 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B3651655 : Blo 2133435 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B4868873 : Blo 2133435 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B3245915 : Blo 2133435 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B2163943 : Blo 2133435 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B2885257 : Blo 2133435 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B3847009 : Blo 2133435 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B5129345 : Blo 2133435 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B3419563 : Blo 2133435 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B4559417 : Blo 2133435 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B3039611 : Blo 2133435 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B8105629 : Blo 2133435 8105629 := bstep (se 3 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 8105629 = 3039611) B3039611
theorem B10807505 : Blo 2133435 10807505 := bstep (se 2 (by rfl) ⟨4052814, by rfl⟩ : syracuseStep 10807505 = 8105629) B8105629
theorem B7205003 : Blo 2133435 7205003 := bstep (se 1 (by rfl) ⟨5403752, by rfl⟩ : syracuseStep 7205003 = 10807505) B10807505
theorem B4803335 : Blo 2133435 4803335 := bstep (se 1 (by rfl) ⟨3602501, by rfl⟩ : syracuseStep 4803335 = 7205003) B7205003
theorem B3202223 : Blo 2133435 3202223 := bstep (se 1 (by rfl) ⟨2401667, by rfl⟩ : syracuseStep 3202223 = 4803335) B4803335
theorem B2134815 : Blo 2133435 2134815 := bstep (se 1 (by rfl) ⟨1601111, by rfl⟩ : syracuseStep 2134815 = 3202223) B3202223
theorem B3202229 : Blo 2133435 3202229 := bbase (se 5 (by rfl) ⟨150104, by rfl⟩ : syracuseStep 3202229 = 300209) (by norm_num)
theorem B2134819 : Blo 2133435 2134819 := bstep (se 1 (by rfl) ⟨1601114, by rfl⟩ : syracuseStep 2134819 = 3202229) B3202229
theorem B5403773 : Blo 2133435 5403773 := bbase (se 3 (by rfl) ⟨1013207, by rfl⟩ : syracuseStep 5403773 = 2026415) (by norm_num)
theorem B3602515 : Blo 2133435 3602515 := bstep (se 1 (by rfl) ⟨2701886, by rfl⟩ : syracuseStep 3602515 = 5403773) B5403773
theorem B4803353 : Blo 2133435 4803353 := bstep (se 2 (by rfl) ⟨1801257, by rfl⟩ : syracuseStep 4803353 = 3602515) B3602515
theorem B3202235 : Blo 2133435 3202235 := bstep (se 1 (by rfl) ⟨2401676, by rfl⟩ : syracuseStep 3202235 = 4803353) B4803353
theorem B2134823 : Blo 2133435 2134823 := bstep (se 1 (by rfl) ⟨1601117, by rfl⟩ : syracuseStep 2134823 = 3202235) B3202235
theorem B2401681 : Blo 2133435 2401681 := bbase (se 2 (by rfl) ⟨900630, by rfl⟩ : syracuseStep 2401681 = 1801261) (by norm_num)
theorem B3202241 : Blo 2133435 3202241 := bstep (se 2 (by rfl) ⟨1200840, by rfl⟩ : syracuseStep 3202241 = 2401681) B2401681
theorem B2134827 : Blo 2133435 2134827 := bstep (se 1 (by rfl) ⟨1601120, by rfl⟩ : syracuseStep 2134827 = 3202241) B3202241
theorem B4052845 : Blo 2133435 4052845 := bbase (se 3 (by rfl) ⟨759908, by rfl⟩ : syracuseStep 4052845 = 1519817) (by norm_num)
theorem B5403793 : Blo 2133435 5403793 := bstep (se 2 (by rfl) ⟨2026422, by rfl⟩ : syracuseStep 5403793 = 4052845) B4052845
theorem B7205057 : Blo 2133435 7205057 := bstep (se 2 (by rfl) ⟨2701896, by rfl⟩ : syracuseStep 7205057 = 5403793) B5403793
theorem B4803371 : Blo 2133435 4803371 := bstep (se 1 (by rfl) ⟨3602528, by rfl⟩ : syracuseStep 4803371 = 7205057) B7205057
theorem B3202247 : Blo 2133435 3202247 := bstep (se 1 (by rfl) ⟨2401685, by rfl⟩ : syracuseStep 3202247 = 4803371) B4803371
theorem B2134831 : Blo 2133435 2134831 := bstep (se 1 (by rfl) ⟨1601123, by rfl⟩ : syracuseStep 2134831 = 3202247) B3202247
theorem B3202253 : Blo 2133435 3202253 := bbase (se 3 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 3202253 = 1200845) (by norm_num)
theorem B2134835 : Blo 2133435 2134835 := bstep (se 1 (by rfl) ⟨1601126, by rfl⟩ : syracuseStep 2134835 = 3202253) B3202253
theorem B4803389 : Blo 2133435 4803389 := bbase (se 3 (by rfl) ⟨900635, by rfl⟩ : syracuseStep 4803389 = 1801271) (by norm_num)
theorem B3202259 : Blo 2133435 3202259 := bstep (se 1 (by rfl) ⟨2401694, by rfl⟩ : syracuseStep 3202259 = 4803389) B4803389
theorem B2134839 : Blo 2133435 2134839 := bstep (se 1 (by rfl) ⟨1601129, by rfl⟩ : syracuseStep 2134839 = 3202259) B3202259
theorem B3602549 : Blo 2133435 3602549 := bbase (se 5 (by rfl) ⟨168869, by rfl⟩ : syracuseStep 3602549 = 337739) (by norm_num)
theorem B2401699 : Blo 2133435 2401699 := bstep (se 1 (by rfl) ⟨1801274, by rfl⟩ : syracuseStep 2401699 = 3602549) B3602549
theorem B3202265 : Blo 2133435 3202265 := bstep (se 2 (by rfl) ⟨1200849, by rfl⟩ : syracuseStep 3202265 = 2401699) B2401699
theorem B2134843 : Blo 2133435 2134843 := bstep (se 1 (by rfl) ⟨1601132, by rfl⟩ : syracuseStep 2134843 = 3202265) B3202265
theorem B4559485 : Blo 2133435 4559485 := bbase (se 3 (by rfl) ⟨854903, by rfl⟩ : syracuseStep 4559485 = 1709807) (by norm_num)
theorem B6079313 : Blo 2133435 6079313 := bstep (se 2 (by rfl) ⟨2279742, by rfl⟩ : syracuseStep 6079313 = 4559485) B4559485
theorem B16211501 : Blo 2133435 16211501 := bstep (se 3 (by rfl) ⟨3039656, by rfl⟩ : syracuseStep 16211501 = 6079313) B6079313
theorem B10807667 : Blo 2133435 10807667 := bstep (se 1 (by rfl) ⟨8105750, by rfl⟩ : syracuseStep 10807667 = 16211501) B16211501
theorem B7205111 : Blo 2133435 7205111 := bstep (se 1 (by rfl) ⟨5403833, by rfl⟩ : syracuseStep 7205111 = 10807667) B10807667
theorem B4803407 : Blo 2133435 4803407 := bstep (se 1 (by rfl) ⟨3602555, by rfl⟩ : syracuseStep 4803407 = 7205111) B7205111
theorem B3202271 : Blo 2133435 3202271 := bstep (se 1 (by rfl) ⟨2401703, by rfl⟩ : syracuseStep 3202271 = 4803407) B4803407
theorem B2134847 : Blo 2133435 2134847 := bstep (se 1 (by rfl) ⟨1601135, by rfl⟩ : syracuseStep 2134847 = 3202271) B3202271
theorem B3202277 : Blo 2133435 3202277 := bbase (se 4 (by rfl) ⟨300213, by rfl⟩ : syracuseStep 3202277 = 600427) (by norm_num)
theorem B2134851 : Blo 2133435 2134851 := bstep (se 1 (by rfl) ⟨1601138, by rfl⟩ : syracuseStep 2134851 = 3202277) B3202277
theorem B12324565 : Blo 2133435 12324565 := bbase (se 7 (by rfl) ⟨144428, by rfl⟩ : syracuseStep 12324565 = 288857) (by norm_num)
theorem B16432753 : Blo 2133435 16432753 := bstep (se 2 (by rfl) ⟨6162282, by rfl⟩ : syracuseStep 16432753 = 12324565) B12324565
theorem B21910337 : Blo 2133435 21910337 := bstep (se 2 (by rfl) ⟨8216376, by rfl⟩ : syracuseStep 21910337 = 16432753) B16432753
theorem B14606891 : Blo 2133435 14606891 := bstep (se 1 (by rfl) ⟨10955168, by rfl⟩ : syracuseStep 14606891 = 21910337) B21910337
theorem B9737927 : Blo 2133435 9737927 := bstep (se 1 (by rfl) ⟨7303445, by rfl⟩ : syracuseStep 9737927 = 14606891) B14606891
theorem B6491951 : Blo 2133435 6491951 := bstep (se 1 (by rfl) ⟨4868963, by rfl⟩ : syracuseStep 6491951 = 9737927) B9737927
theorem B4327967 : Blo 2133435 4327967 := bstep (se 1 (by rfl) ⟨3245975, by rfl⟩ : syracuseStep 4327967 = 6491951) B6491951
theorem B2885311 : Blo 2133435 2885311 := bstep (se 1 (by rfl) ⟨2163983, by rfl⟩ : syracuseStep 2885311 = 4327967) B4327967
theorem B15388325 : Blo 2133435 15388325 := bstep (se 4 (by rfl) ⟨1442655, by rfl⟩ : syracuseStep 15388325 = 2885311) B2885311
theorem B10258883 : Blo 2133435 10258883 := bstep (se 1 (by rfl) ⟨7694162, by rfl⟩ : syracuseStep 10258883 = 15388325) B15388325
theorem B6839255 : Blo 2133435 6839255 := bstep (se 1 (by rfl) ⟨5129441, by rfl⟩ : syracuseStep 6839255 = 10258883) B10258883
theorem B4559503 : Blo 2133435 4559503 := bstep (se 1 (by rfl) ⟨3419627, by rfl⟩ : syracuseStep 4559503 = 6839255) B6839255
theorem B6079337 : Blo 2133435 6079337 := bstep (se 2 (by rfl) ⟨2279751, by rfl⟩ : syracuseStep 6079337 = 4559503) B4559503
theorem B4052891 : Blo 2133435 4052891 := bstep (se 1 (by rfl) ⟨3039668, by rfl⟩ : syracuseStep 4052891 = 6079337) B6079337
theorem B2701927 : Blo 2133435 2701927 := bstep (se 1 (by rfl) ⟨2026445, by rfl⟩ : syracuseStep 2701927 = 4052891) B4052891
theorem B3602569 : Blo 2133435 3602569 := bstep (se 2 (by rfl) ⟨1350963, by rfl⟩ : syracuseStep 3602569 = 2701927) B2701927
theorem B4803425 : Blo 2133435 4803425 := bstep (se 2 (by rfl) ⟨1801284, by rfl⟩ : syracuseStep 4803425 = 3602569) B3602569
theorem B3202283 : Blo 2133435 3202283 := bstep (se 1 (by rfl) ⟨2401712, by rfl⟩ : syracuseStep 3202283 = 4803425) B4803425
theorem B2134855 : Blo 2133435 2134855 := bstep (se 1 (by rfl) ⟨1601141, by rfl⟩ : syracuseStep 2134855 = 3202283) B3202283
theorem B2401717 : Blo 2133435 2401717 := bbase (se 5 (by rfl) ⟨112580, by rfl⟩ : syracuseStep 2401717 = 225161) (by norm_num)
theorem B3202289 : Blo 2133435 3202289 := bstep (se 2 (by rfl) ⟨1200858, by rfl⟩ : syracuseStep 3202289 = 2401717) B2401717
theorem B2134859 : Blo 2133435 2134859 := bstep (se 1 (by rfl) ⟨1601144, by rfl⟩ : syracuseStep 2134859 = 3202289) B3202289
theorem B2701937 : Blo 2133435 2701937 := bbase (se 2 (by rfl) ⟨1013226, by rfl⟩ : syracuseStep 2701937 = 2026453) (by norm_num)
theorem B7205165 : Blo 2133435 7205165 := bstep (se 3 (by rfl) ⟨1350968, by rfl⟩ : syracuseStep 7205165 = 2701937) B2701937
theorem B4803443 : Blo 2133435 4803443 := bstep (se 1 (by rfl) ⟨3602582, by rfl⟩ : syracuseStep 4803443 = 7205165) B7205165
theorem B3202295 : Blo 2133435 3202295 := bstep (se 1 (by rfl) ⟨2401721, by rfl⟩ : syracuseStep 3202295 = 4803443) B4803443
theorem B2134863 : Blo 2133435 2134863 := bstep (se 1 (by rfl) ⟨1601147, by rfl⟩ : syracuseStep 2134863 = 3202295) B3202295
theorem B3202301 : Blo 2133435 3202301 := bbase (se 3 (by rfl) ⟨600431, by rfl⟩ : syracuseStep 3202301 = 1200863) (by norm_num)
theorem B2134867 : Blo 2133435 2134867 := bstep (se 1 (by rfl) ⟨1601150, by rfl⟩ : syracuseStep 2134867 = 3202301) B3202301
theorem B4803461 : Blo 2133435 4803461 := bbase (se 4 (by rfl) ⟨450324, by rfl⟩ : syracuseStep 4803461 = 900649) (by norm_num)
theorem B3202307 : Blo 2133435 3202307 := bstep (se 1 (by rfl) ⟨2401730, by rfl⟩ : syracuseStep 3202307 = 4803461) B4803461
theorem B2134871 : Blo 2133435 2134871 := bstep (se 1 (by rfl) ⟨1601153, by rfl⟩ : syracuseStep 2134871 = 3202307) B3202307
theorem B2279773 : Blo 2133435 2279773 := bbase (se 3 (by rfl) ⟨427457, by rfl⟩ : syracuseStep 2279773 = 854915) (by norm_num)
theorem B3039697 : Blo 2133435 3039697 := bstep (se 2 (by rfl) ⟨1139886, by rfl⟩ : syracuseStep 3039697 = 2279773) B2279773
theorem B4052929 : Blo 2133435 4052929 := bstep (se 2 (by rfl) ⟨1519848, by rfl⟩ : syracuseStep 4052929 = 3039697) B3039697
theorem B5403905 : Blo 2133435 5403905 := bstep (se 2 (by rfl) ⟨2026464, by rfl⟩ : syracuseStep 5403905 = 4052929) B4052929
theorem B3602603 : Blo 2133435 3602603 := bstep (se 1 (by rfl) ⟨2701952, by rfl⟩ : syracuseStep 3602603 = 5403905) B5403905
theorem B2401735 : Blo 2133435 2401735 := bstep (se 1 (by rfl) ⟨1801301, by rfl⟩ : syracuseStep 2401735 = 3602603) B3602603
theorem B3202313 : Blo 2133435 3202313 := bstep (se 2 (by rfl) ⟨1200867, by rfl⟩ : syracuseStep 3202313 = 2401735) B2401735
theorem B2134875 : Blo 2133435 2134875 := bstep (se 1 (by rfl) ⟨1601156, by rfl⟩ : syracuseStep 2134875 = 3202313) B3202313
theorem B10807829 : Blo 2133435 10807829 := bbase (se 6 (by rfl) ⟨253308, by rfl⟩ : syracuseStep 10807829 = 506617) (by norm_num)
theorem B7205219 : Blo 2133435 7205219 := bstep (se 1 (by rfl) ⟨5403914, by rfl⟩ : syracuseStep 7205219 = 10807829) B10807829
theorem B4803479 : Blo 2133435 4803479 := bstep (se 1 (by rfl) ⟨3602609, by rfl⟩ : syracuseStep 4803479 = 7205219) B7205219
theorem B3202319 : Blo 2133435 3202319 := bstep (se 1 (by rfl) ⟨2401739, by rfl⟩ : syracuseStep 3202319 = 4803479) B4803479
theorem B2134879 : Blo 2133435 2134879 := bstep (se 1 (by rfl) ⟨1601159, by rfl⟩ : syracuseStep 2134879 = 3202319) B3202319
theorem B3202325 : Blo 2133435 3202325 := bbase (se 6 (by rfl) ⟨75054, by rfl⟩ : syracuseStep 3202325 = 150109) (by norm_num)
theorem B2134883 : Blo 2133435 2134883 := bstep (se 1 (by rfl) ⟨1601162, by rfl⟩ : syracuseStep 2134883 = 3202325) B3202325
theorem B20518069 : Blo 2133435 20518069 := bbase (se 5 (by rfl) ⟨961784, by rfl⟩ : syracuseStep 20518069 = 1923569) (by norm_num)
theorem B27357425 : Blo 2133435 27357425 := bstep (se 2 (by rfl) ⟨10259034, by rfl⟩ : syracuseStep 27357425 = 20518069) B20518069
theorem B18238283 : Blo 2133435 18238283 := bstep (se 1 (by rfl) ⟨13678712, by rfl⟩ : syracuseStep 18238283 = 27357425) B27357425
theorem B12158855 : Blo 2133435 12158855 := bstep (se 1 (by rfl) ⟨9119141, by rfl⟩ : syracuseStep 12158855 = 18238283) B18238283
theorem B8105903 : Blo 2133435 8105903 := bstep (se 1 (by rfl) ⟨6079427, by rfl⟩ : syracuseStep 8105903 = 12158855) B12158855
theorem B5403935 : Blo 2133435 5403935 := bstep (se 1 (by rfl) ⟨4052951, by rfl⟩ : syracuseStep 5403935 = 8105903) B8105903
theorem B3602623 : Blo 2133435 3602623 := bstep (se 1 (by rfl) ⟨2701967, by rfl⟩ : syracuseStep 3602623 = 5403935) B5403935
theorem B4803497 : Blo 2133435 4803497 := bstep (se 2 (by rfl) ⟨1801311, by rfl⟩ : syracuseStep 4803497 = 3602623) B3602623
theorem B3202331 : Blo 2133435 3202331 := bstep (se 1 (by rfl) ⟨2401748, by rfl⟩ : syracuseStep 3202331 = 4803497) B4803497
theorem B2134887 : Blo 2133435 2134887 := bstep (se 1 (by rfl) ⟨1601165, by rfl⟩ : syracuseStep 2134887 = 3202331) B3202331
theorem B2401753 : Blo 2133435 2401753 := bbase (se 2 (by rfl) ⟨900657, by rfl⟩ : syracuseStep 2401753 = 1801315) (by norm_num)
theorem B3202337 : Blo 2133435 3202337 := bstep (se 2 (by rfl) ⟨1200876, by rfl⟩ : syracuseStep 3202337 = 2401753) B2401753
theorem B2134891 : Blo 2133435 2134891 := bstep (se 1 (by rfl) ⟨1601168, by rfl⟩ : syracuseStep 2134891 = 3202337) B3202337
theorem B3039725 : Blo 2133435 3039725 := bbase (se 3 (by rfl) ⟨569948, by rfl⟩ : syracuseStep 3039725 = 1139897) (by norm_num)
theorem B8105933 : Blo 2133435 8105933 := bstep (se 3 (by rfl) ⟨1519862, by rfl⟩ : syracuseStep 8105933 = 3039725) B3039725
theorem B5403955 : Blo 2133435 5403955 := bstep (se 1 (by rfl) ⟨4052966, by rfl⟩ : syracuseStep 5403955 = 8105933) B8105933
theorem B7205273 : Blo 2133435 7205273 := bstep (se 2 (by rfl) ⟨2701977, by rfl⟩ : syracuseStep 7205273 = 5403955) B5403955
theorem B4803515 : Blo 2133435 4803515 := bstep (se 1 (by rfl) ⟨3602636, by rfl⟩ : syracuseStep 4803515 = 7205273) B7205273
theorem B3202343 : Blo 2133435 3202343 := bstep (se 1 (by rfl) ⟨2401757, by rfl⟩ : syracuseStep 3202343 = 4803515) B4803515
theorem B2134895 : Blo 2133435 2134895 := bstep (se 1 (by rfl) ⟨1601171, by rfl⟩ : syracuseStep 2134895 = 3202343) B3202343
theorem B3202349 : Blo 2133435 3202349 := bbase (se 3 (by rfl) ⟨600440, by rfl⟩ : syracuseStep 3202349 = 1200881) (by norm_num)
theorem B2134899 : Blo 2133435 2134899 := bstep (se 1 (by rfl) ⟨1601174, by rfl⟩ : syracuseStep 2134899 = 3202349) B3202349
theorem B4803533 : Blo 2133435 4803533 := bbase (se 3 (by rfl) ⟨900662, by rfl⟩ : syracuseStep 4803533 = 1801325) (by norm_num)
theorem B3202355 : Blo 2133435 3202355 := bstep (se 1 (by rfl) ⟨2401766, by rfl⟩ : syracuseStep 3202355 = 4803533) B4803533
theorem B2134903 : Blo 2133435 2134903 := bstep (se 1 (by rfl) ⟨1601177, by rfl⟩ : syracuseStep 2134903 = 3202355) B3202355
theorem B2701993 : Blo 2133435 2701993 := bbase (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) (by norm_num)
theorem B3602657 : Blo 2133435 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B2401771 : Blo 2133435 2401771 := bstep (se 1 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 2401771 = 3602657) B3602657
theorem B3202361 : Blo 2133435 3202361 := bstep (se 2 (by rfl) ⟨1200885, by rfl⟩ : syracuseStep 3202361 = 2401771) B2401771
theorem B2134907 : Blo 2133435 2134907 := bstep (se 1 (by rfl) ⟨1601180, by rfl⟩ : syracuseStep 2134907 = 3202361) B3202361
theorem B3847181 : Blo 2133435 3847181 := bbase (se 3 (by rfl) ⟨721346, by rfl⟩ : syracuseStep 3847181 = 1442693) (by norm_num)
theorem B10259149 : Blo 2133435 10259149 := bstep (se 3 (by rfl) ⟨1923590, by rfl⟩ : syracuseStep 10259149 = 3847181) B3847181
theorem B13678865 : Blo 2133435 13678865 := bstep (se 2 (by rfl) ⟨5129574, by rfl⟩ : syracuseStep 13678865 = 10259149) B10259149
theorem B9119243 : Blo 2133435 9119243 := bstep (se 1 (by rfl) ⟨6839432, by rfl⟩ : syracuseStep 9119243 = 13678865) B13678865
theorem B24317981 : Blo 2133435 24317981 := bstep (se 3 (by rfl) ⟨4559621, by rfl⟩ : syracuseStep 24317981 = 9119243) B9119243
theorem B16211987 : Blo 2133435 16211987 := bstep (se 1 (by rfl) ⟨12158990, by rfl⟩ : syracuseStep 16211987 = 24317981) B24317981
theorem B10807991 : Blo 2133435 10807991 := bstep (se 1 (by rfl) ⟨8105993, by rfl⟩ : syracuseStep 10807991 = 16211987) B16211987
theorem B7205327 : Blo 2133435 7205327 := bstep (se 1 (by rfl) ⟨5403995, by rfl⟩ : syracuseStep 7205327 = 10807991) B10807991
theorem B4803551 : Blo 2133435 4803551 := bstep (se 1 (by rfl) ⟨3602663, by rfl⟩ : syracuseStep 4803551 = 7205327) B7205327
theorem B3202367 : Blo 2133435 3202367 := bstep (se 1 (by rfl) ⟨2401775, by rfl⟩ : syracuseStep 3202367 = 4803551) B4803551
theorem B2134911 : Blo 2133435 2134911 := bstep (se 1 (by rfl) ⟨1601183, by rfl⟩ : syracuseStep 2134911 = 3202367) B3202367
theorem B3202373 : Blo 2133435 3202373 := bbase (se 4 (by rfl) ⟨300222, by rfl⟩ : syracuseStep 3202373 = 600445) (by norm_num)
theorem B2134915 : Blo 2133435 2134915 := bstep (se 1 (by rfl) ⟨1601186, by rfl⟩ : syracuseStep 2134915 = 3202373) B3202373
theorem B3602677 : Blo 2133435 3602677 := bbase (se 5 (by rfl) ⟨168875, by rfl⟩ : syracuseStep 3602677 = 337751) (by norm_num)
theorem B4803569 : Blo 2133435 4803569 := bstep (se 2 (by rfl) ⟨1801338, by rfl⟩ : syracuseStep 4803569 = 3602677) B3602677
theorem B3202379 : Blo 2133435 3202379 := bstep (se 1 (by rfl) ⟨2401784, by rfl⟩ : syracuseStep 3202379 = 4803569) B4803569
theorem B2134919 : Blo 2133435 2134919 := bstep (se 1 (by rfl) ⟨1601189, by rfl⟩ : syracuseStep 2134919 = 3202379) B3202379
theorem B2401789 : Blo 2133435 2401789 := bbase (se 3 (by rfl) ⟨450335, by rfl⟩ : syracuseStep 2401789 = 900671) (by norm_num)
theorem B3202385 : Blo 2133435 3202385 := bstep (se 2 (by rfl) ⟨1200894, by rfl⟩ : syracuseStep 3202385 = 2401789) B2401789
theorem B2134923 : Blo 2133435 2134923 := bstep (se 1 (by rfl) ⟨1601192, by rfl⟩ : syracuseStep 2134923 = 3202385) B3202385
theorem B7205381 : Blo 2133435 7205381 := bbase (se 4 (by rfl) ⟨675504, by rfl⟩ : syracuseStep 7205381 = 1351009) (by norm_num)
theorem B4803587 : Blo 2133435 4803587 := bstep (se 1 (by rfl) ⟨3602690, by rfl⟩ : syracuseStep 4803587 = 7205381) B7205381
theorem B3202391 : Blo 2133435 3202391 := bstep (se 1 (by rfl) ⟨2401793, by rfl⟩ : syracuseStep 3202391 = 4803587) B4803587
theorem B2134927 : Blo 2133435 2134927 := bstep (se 1 (by rfl) ⟨1601195, by rfl⟩ : syracuseStep 2134927 = 3202391) B3202391
theorem B3202397 : Blo 2133435 3202397 := bbase (se 3 (by rfl) ⟨600449, by rfl⟩ : syracuseStep 3202397 = 1200899) (by norm_num)
theorem B2134931 : Blo 2133435 2134931 := bstep (se 1 (by rfl) ⟨1601198, by rfl⟩ : syracuseStep 2134931 = 3202397) B3202397
theorem B4803605 : Blo 2133435 4803605 := bbase (se 6 (by rfl) ⟨112584, by rfl⟩ : syracuseStep 4803605 = 225169) (by norm_num)
theorem B3202403 : Blo 2133435 3202403 := bstep (se 1 (by rfl) ⟨2401802, by rfl⟩ : syracuseStep 3202403 = 4803605) B4803605
theorem B2134935 : Blo 2133435 2134935 := bstep (se 1 (by rfl) ⟨1601201, by rfl⟩ : syracuseStep 2134935 = 3202403) B3202403
theorem B8106101 : Blo 2133435 8106101 := bbase (se 5 (by rfl) ⟨379973, by rfl⟩ : syracuseStep 8106101 = 759947) (by norm_num)
theorem B5404067 : Blo 2133435 5404067 := bstep (se 1 (by rfl) ⟨4053050, by rfl⟩ : syracuseStep 5404067 = 8106101) B8106101
theorem B3602711 : Blo 2133435 3602711 := bstep (se 1 (by rfl) ⟨2702033, by rfl⟩ : syracuseStep 3602711 = 5404067) B5404067
theorem B2401807 : Blo 2133435 2401807 := bstep (se 1 (by rfl) ⟨1801355, by rfl⟩ : syracuseStep 2401807 = 3602711) B3602711
theorem B3202409 : Blo 2133435 3202409 := bstep (se 2 (by rfl) ⟨1200903, by rfl⟩ : syracuseStep 3202409 = 2401807) B2401807
theorem B2134939 : Blo 2133435 2134939 := bstep (se 1 (by rfl) ⟨1601204, by rfl⟩ : syracuseStep 2134939 = 3202409) B3202409
theorem B2279845 : Blo 2133435 2279845 := bbase (se 4 (by rfl) ⟨213735, by rfl⟩ : syracuseStep 2279845 = 427471) (by norm_num)
theorem B12159173 : Blo 2133435 12159173 := bstep (se 4 (by rfl) ⟨1139922, by rfl⟩ : syracuseStep 12159173 = 2279845) B2279845
theorem B8106115 : Blo 2133435 8106115 := bstep (se 1 (by rfl) ⟨6079586, by rfl⟩ : syracuseStep 8106115 = 12159173) B12159173
theorem B10808153 : Blo 2133435 10808153 := bstep (se 2 (by rfl) ⟨4053057, by rfl⟩ : syracuseStep 10808153 = 8106115) B8106115
theorem B7205435 : Blo 2133435 7205435 := bstep (se 1 (by rfl) ⟨5404076, by rfl⟩ : syracuseStep 7205435 = 10808153) B10808153
theorem B4803623 : Blo 2133435 4803623 := bstep (se 1 (by rfl) ⟨3602717, by rfl⟩ : syracuseStep 4803623 = 7205435) B7205435
theorem B3202415 : Blo 2133435 3202415 := bstep (se 1 (by rfl) ⟨2401811, by rfl⟩ : syracuseStep 3202415 = 4803623) B4803623
theorem B2134943 : Blo 2133435 2134943 := bstep (se 1 (by rfl) ⟨1601207, by rfl⟩ : syracuseStep 2134943 = 3202415) B3202415
theorem B3202421 : Blo 2133435 3202421 := bbase (se 5 (by rfl) ⟨150113, by rfl⟩ : syracuseStep 3202421 = 300227) (by norm_num)
theorem B2134947 : Blo 2133435 2134947 := bstep (se 1 (by rfl) ⟨1601210, by rfl⟩ : syracuseStep 2134947 = 3202421) B3202421
theorem B3039805 : Blo 2133435 3039805 := bbase (se 3 (by rfl) ⟨569963, by rfl⟩ : syracuseStep 3039805 = 1139927) (by norm_num)
theorem B4053073 : Blo 2133435 4053073 := bstep (se 2 (by rfl) ⟨1519902, by rfl⟩ : syracuseStep 4053073 = 3039805) B3039805
theorem B5404097 : Blo 2133435 5404097 := bstep (se 2 (by rfl) ⟨2026536, by rfl⟩ : syracuseStep 5404097 = 4053073) B4053073
theorem B3602731 : Blo 2133435 3602731 := bstep (se 1 (by rfl) ⟨2702048, by rfl⟩ : syracuseStep 3602731 = 5404097) B5404097
theorem B4803641 : Blo 2133435 4803641 := bstep (se 2 (by rfl) ⟨1801365, by rfl⟩ : syracuseStep 4803641 = 3602731) B3602731
theorem B3202427 : Blo 2133435 3202427 := bstep (se 1 (by rfl) ⟨2401820, by rfl⟩ : syracuseStep 3202427 = 4803641) B4803641
theorem B2134951 : Blo 2133435 2134951 := bstep (se 1 (by rfl) ⟨1601213, by rfl⟩ : syracuseStep 2134951 = 3202427) B3202427
theorem B2401825 : Blo 2133435 2401825 := bbase (se 2 (by rfl) ⟨900684, by rfl⟩ : syracuseStep 2401825 = 1801369) (by norm_num)
theorem B3202433 : Blo 2133435 3202433 := bstep (se 2 (by rfl) ⟨1200912, by rfl⟩ : syracuseStep 3202433 = 2401825) B2401825
theorem B2134955 : Blo 2133435 2134955 := bstep (se 1 (by rfl) ⟨1601216, by rfl⟩ : syracuseStep 2134955 = 3202433) B3202433
theorem B5404117 : Blo 2133435 5404117 := bbase (se 7 (by rfl) ⟨63329, by rfl⟩ : syracuseStep 5404117 = 126659) (by norm_num)
theorem B7205489 : Blo 2133435 7205489 := bstep (se 2 (by rfl) ⟨2702058, by rfl⟩ : syracuseStep 7205489 = 5404117) B5404117
theorem B4803659 : Blo 2133435 4803659 := bstep (se 1 (by rfl) ⟨3602744, by rfl⟩ : syracuseStep 4803659 = 7205489) B7205489
theorem B3202439 : Blo 2133435 3202439 := bstep (se 1 (by rfl) ⟨2401829, by rfl⟩ : syracuseStep 3202439 = 4803659) B4803659
theorem B2134959 : Blo 2133435 2134959 := bstep (se 1 (by rfl) ⟨1601219, by rfl⟩ : syracuseStep 2134959 = 3202439) B3202439
theorem B3202445 : Blo 2133435 3202445 := bbase (se 3 (by rfl) ⟨600458, by rfl⟩ : syracuseStep 3202445 = 1200917) (by norm_num)
theorem B2134963 : Blo 2133435 2134963 := bstep (se 1 (by rfl) ⟨1601222, by rfl⟩ : syracuseStep 2134963 = 3202445) B3202445
theorem B4803677 : Blo 2133435 4803677 := bbase (se 3 (by rfl) ⟨900689, by rfl⟩ : syracuseStep 4803677 = 1801379) (by norm_num)
theorem B3202451 : Blo 2133435 3202451 := bstep (se 1 (by rfl) ⟨2401838, by rfl⟩ : syracuseStep 3202451 = 4803677) B4803677
theorem B2134967 : Blo 2133435 2134967 := bstep (se 1 (by rfl) ⟨1601225, by rfl⟩ : syracuseStep 2134967 = 3202451) B3202451
theorem B3602765 : Blo 2133435 3602765 := bbase (se 3 (by rfl) ⟨675518, by rfl⟩ : syracuseStep 3602765 = 1351037) (by norm_num)
theorem B2401843 : Blo 2133435 2401843 := bstep (se 1 (by rfl) ⟨1801382, by rfl⟩ : syracuseStep 2401843 = 3602765) B3602765
theorem B3202457 : Blo 2133435 3202457 := bstep (se 2 (by rfl) ⟨1200921, by rfl⟩ : syracuseStep 3202457 = 2401843) B2401843
theorem B2134971 : Blo 2133435 2134971 := bstep (se 1 (by rfl) ⟨1601228, by rfl⟩ : syracuseStep 2134971 = 3202457) B3202457
theorem B2738945 : Blo 2133435 2738945 := bbase (se 2 (by rfl) ⟨1027104, by rfl⟩ : syracuseStep 2738945 = 2054209) (by norm_num)
theorem B7303853 : Blo 2133435 7303853 := bstep (se 3 (by rfl) ⟨1369472, by rfl⟩ : syracuseStep 7303853 = 2738945) B2738945
theorem B4869235 : Blo 2133435 4869235 := bstep (se 1 (by rfl) ⟨3651926, by rfl⟩ : syracuseStep 4869235 = 7303853) B7303853
theorem B6492313 : Blo 2133435 6492313 := bstep (se 2 (by rfl) ⟨2434617, by rfl⟩ : syracuseStep 6492313 = 4869235) B4869235
theorem B8656417 : Blo 2133435 8656417 := bstep (se 2 (by rfl) ⟨3246156, by rfl⟩ : syracuseStep 8656417 = 6492313) B6492313
theorem B11541889 : Blo 2133435 11541889 := bstep (se 2 (by rfl) ⟨4328208, by rfl⟩ : syracuseStep 11541889 = 8656417) B8656417
theorem B15389185 : Blo 2133435 15389185 := bstep (se 2 (by rfl) ⟨5770944, by rfl⟩ : syracuseStep 15389185 = 11541889) B11541889
theorem B20518913 : Blo 2133435 20518913 := bstep (se 2 (by rfl) ⟨7694592, by rfl⟩ : syracuseStep 20518913 = 15389185) B15389185
theorem B13679275 : Blo 2133435 13679275 := bstep (se 1 (by rfl) ⟨10259456, by rfl⟩ : syracuseStep 13679275 = 20518913) B20518913
theorem B18239033 : Blo 2133435 18239033 := bstep (se 2 (by rfl) ⟨6839637, by rfl⟩ : syracuseStep 18239033 = 13679275) B13679275
theorem B12159355 : Blo 2133435 12159355 := bstep (se 1 (by rfl) ⟨9119516, by rfl⟩ : syracuseStep 12159355 = 18239033) B18239033
theorem B16212473 : Blo 2133435 16212473 := bstep (se 2 (by rfl) ⟨6079677, by rfl⟩ : syracuseStep 16212473 = 12159355) B12159355
theorem B10808315 : Blo 2133435 10808315 := bstep (se 1 (by rfl) ⟨8106236, by rfl⟩ : syracuseStep 10808315 = 16212473) B16212473
theorem B7205543 : Blo 2133435 7205543 := bstep (se 1 (by rfl) ⟨5404157, by rfl⟩ : syracuseStep 7205543 = 10808315) B10808315
theorem B4803695 : Blo 2133435 4803695 := bstep (se 1 (by rfl) ⟨3602771, by rfl⟩ : syracuseStep 4803695 = 7205543) B7205543
theorem B3202463 : Blo 2133435 3202463 := bstep (se 1 (by rfl) ⟨2401847, by rfl⟩ : syracuseStep 3202463 = 4803695) B4803695
theorem B2134975 : Blo 2133435 2134975 := bstep (se 1 (by rfl) ⟨1601231, by rfl⟩ : syracuseStep 2134975 = 3202463) B3202463
theorem B3202469 : Blo 2133435 3202469 := bbase (se 4 (by rfl) ⟨300231, by rfl⟩ : syracuseStep 3202469 = 600463) (by norm_num)
theorem B2134979 : Blo 2133435 2134979 := bstep (se 1 (by rfl) ⟨1601234, by rfl⟩ : syracuseStep 2134979 = 3202469) B3202469
theorem B2702089 : Blo 2133435 2702089 := bbase (se 2 (by rfl) ⟨1013283, by rfl⟩ : syracuseStep 2702089 = 2026567) (by norm_num)
theorem B3602785 : Blo 2133435 3602785 := bstep (se 2 (by rfl) ⟨1351044, by rfl⟩ : syracuseStep 3602785 = 2702089) B2702089
theorem B4803713 : Blo 2133435 4803713 := bstep (se 2 (by rfl) ⟨1801392, by rfl⟩ : syracuseStep 4803713 = 3602785) B3602785
theorem B3202475 : Blo 2133435 3202475 := bstep (se 1 (by rfl) ⟨2401856, by rfl⟩ : syracuseStep 3202475 = 4803713) B4803713
theorem B2134983 : Blo 2133435 2134983 := bstep (se 1 (by rfl) ⟨1601237, by rfl⟩ : syracuseStep 2134983 = 3202475) B3202475
theorem B2401861 : Blo 2133435 2401861 := bbase (se 4 (by rfl) ⟨225174, by rfl⟩ : syracuseStep 2401861 = 450349) (by norm_num)
theorem B3202481 : Blo 2133435 3202481 := bstep (se 2 (by rfl) ⟨1200930, by rfl⟩ : syracuseStep 3202481 = 2401861) B2401861
theorem B2134987 : Blo 2133435 2134987 := bstep (se 1 (by rfl) ⟨1601240, by rfl⟩ : syracuseStep 2134987 = 3202481) B3202481
theorem B4053149 : Blo 2133435 4053149 := bbase (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) (by norm_num)
theorem B2702099 : Blo 2133435 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B7205597 : Blo 2133435 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B4803731 : Blo 2133435 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B3202487 : Blo 2133435 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B2134991 : Blo 2133435 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B3202493 : Blo 2133435 3202493 := bbase (se 3 (by rfl) ⟨600467, by rfl⟩ : syracuseStep 3202493 = 1200935) (by norm_num)
theorem B2134995 : Blo 2133435 2134995 := bstep (se 1 (by rfl) ⟨1601246, by rfl⟩ : syracuseStep 2134995 = 3202493) B3202493
theorem B4803749 : Blo 2133435 4803749 := bbase (se 4 (by rfl) ⟨450351, by rfl⟩ : syracuseStep 4803749 = 900703) (by norm_num)
theorem B3202499 : Blo 2133435 3202499 := bstep (se 1 (by rfl) ⟨2401874, by rfl⟩ : syracuseStep 3202499 = 4803749) B4803749
theorem B2134999 : Blo 2133435 2134999 := bstep (se 1 (by rfl) ⟨1601249, by rfl⟩ : syracuseStep 2134999 = 3202499) B3202499
theorem B5404229 : Blo 2133435 5404229 := bbase (se 4 (by rfl) ⟨506646, by rfl⟩ : syracuseStep 5404229 = 1013293) (by norm_num)
theorem B3602819 : Blo 2133435 3602819 := bstep (se 1 (by rfl) ⟨2702114, by rfl⟩ : syracuseStep 3602819 = 5404229) B5404229
theorem B2401879 : Blo 2133435 2401879 := bstep (se 1 (by rfl) ⟨1801409, by rfl⟩ : syracuseStep 2401879 = 3602819) B3602819
theorem B3202505 : Blo 2133435 3202505 := bstep (se 2 (by rfl) ⟨1200939, by rfl⟩ : syracuseStep 3202505 = 2401879) B2401879
theorem B2135003 : Blo 2133435 2135003 := bstep (se 1 (by rfl) ⟨1601252, by rfl⟩ : syracuseStep 2135003 = 3202505) B3202505
theorem B2311021 : Blo 2133435 2311021 := bbase (se 3 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 2311021 = 866633) (by norm_num)
theorem B12325445 : Blo 2133435 12325445 := bstep (se 4 (by rfl) ⟨1155510, by rfl⟩ : syracuseStep 12325445 = 2311021) B2311021
theorem B8216963 : Blo 2133435 8216963 := bstep (se 1 (by rfl) ⟨6162722, by rfl⟩ : syracuseStep 8216963 = 12325445) B12325445
theorem B5477975 : Blo 2133435 5477975 := bstep (se 1 (by rfl) ⟨4108481, by rfl⟩ : syracuseStep 5477975 = 8216963) B8216963
theorem B3651983 : Blo 2133435 3651983 := bstep (se 1 (by rfl) ⟨2738987, by rfl⟩ : syracuseStep 3651983 = 5477975) B5477975
theorem B2434655 : Blo 2133435 2434655 := bstep (se 1 (by rfl) ⟨1825991, by rfl⟩ : syracuseStep 2434655 = 3651983) B3651983
theorem B6492413 : Blo 2133435 6492413 := bstep (se 3 (by rfl) ⟨1217327, by rfl⟩ : syracuseStep 6492413 = 2434655) B2434655
theorem B4328275 : Blo 2133435 4328275 := bstep (se 1 (by rfl) ⟨3246206, by rfl⟩ : syracuseStep 4328275 = 6492413) B6492413
theorem B5771033 : Blo 2133435 5771033 := bstep (se 2 (by rfl) ⟨2164137, by rfl⟩ : syracuseStep 5771033 = 4328275) B4328275
theorem B3847355 : Blo 2133435 3847355 := bstep (se 1 (by rfl) ⟨2885516, by rfl⟩ : syracuseStep 3847355 = 5771033) B5771033
theorem B2564903 : Blo 2133435 2564903 := bstep (se 1 (by rfl) ⟨1923677, by rfl⟩ : syracuseStep 2564903 = 3847355) B3847355
theorem B6839741 : Blo 2133435 6839741 := bstep (se 3 (by rfl) ⟨1282451, by rfl⟩ : syracuseStep 6839741 = 2564903) B2564903
theorem B4559827 : Blo 2133435 4559827 := bstep (se 1 (by rfl) ⟨3419870, by rfl⟩ : syracuseStep 4559827 = 6839741) B6839741
theorem B6079769 : Blo 2133435 6079769 := bstep (se 2 (by rfl) ⟨2279913, by rfl⟩ : syracuseStep 6079769 = 4559827) B4559827
theorem B4053179 : Blo 2133435 4053179 := bstep (se 1 (by rfl) ⟨3039884, by rfl⟩ : syracuseStep 4053179 = 6079769) B6079769
theorem B10808477 : Blo 2133435 10808477 := bstep (se 3 (by rfl) ⟨2026589, by rfl⟩ : syracuseStep 10808477 = 4053179) B4053179
theorem B7205651 : Blo 2133435 7205651 := bstep (se 1 (by rfl) ⟨5404238, by rfl⟩ : syracuseStep 7205651 = 10808477) B10808477
theorem B4803767 : Blo 2133435 4803767 := bstep (se 1 (by rfl) ⟨3602825, by rfl⟩ : syracuseStep 4803767 = 7205651) B7205651
theorem B3202511 : Blo 2133435 3202511 := bstep (se 1 (by rfl) ⟨2401883, by rfl⟩ : syracuseStep 3202511 = 4803767) B4803767
theorem B2135007 : Blo 2133435 2135007 := bstep (se 1 (by rfl) ⟨1601255, by rfl⟩ : syracuseStep 2135007 = 3202511) B3202511
theorem B3202517 : Blo 2133435 3202517 := bbase (se 7 (by rfl) ⟨37529, by rfl⟩ : syracuseStep 3202517 = 75059) (by norm_num)
theorem B2135011 : Blo 2133435 2135011 := bstep (se 1 (by rfl) ⟨1601258, by rfl⟩ : syracuseStep 2135011 = 3202517) B3202517
theorem B8106389 : Blo 2133435 8106389 := bbase (se 6 (by rfl) ⟨189993, by rfl⟩ : syracuseStep 8106389 = 379987) (by norm_num)
theorem B5404259 : Blo 2133435 5404259 := bstep (se 1 (by rfl) ⟨4053194, by rfl⟩ : syracuseStep 5404259 = 8106389) B8106389
theorem B3602839 : Blo 2133435 3602839 := bstep (se 1 (by rfl) ⟨2702129, by rfl⟩ : syracuseStep 3602839 = 5404259) B5404259
theorem B4803785 : Blo 2133435 4803785 := bstep (se 2 (by rfl) ⟨1801419, by rfl⟩ : syracuseStep 4803785 = 3602839) B3602839
theorem B3202523 : Blo 2133435 3202523 := bstep (se 1 (by rfl) ⟨2401892, by rfl⟩ : syracuseStep 3202523 = 4803785) B4803785
theorem B2135015 : Blo 2133435 2135015 := bstep (se 1 (by rfl) ⟨1601261, by rfl⟩ : syracuseStep 2135015 = 3202523) B3202523
theorem B2401897 : Blo 2133435 2401897 := bbase (se 2 (by rfl) ⟨900711, by rfl⟩ : syracuseStep 2401897 = 1801423) (by norm_num)
theorem B3202529 : Blo 2133435 3202529 := bstep (se 2 (by rfl) ⟨1200948, by rfl⟩ : syracuseStep 3202529 = 2401897) B2401897
theorem B2135019 : Blo 2133435 2135019 := bstep (se 1 (by rfl) ⟨1601264, by rfl⟩ : syracuseStep 2135019 = 3202529) B3202529
theorem B4559861 : Blo 2133435 4559861 := bbase (se 5 (by rfl) ⟨213743, by rfl⟩ : syracuseStep 4559861 = 427487) (by norm_num)
theorem B12159629 : Blo 2133435 12159629 := bstep (se 3 (by rfl) ⟨2279930, by rfl⟩ : syracuseStep 12159629 = 4559861) B4559861
theorem B8106419 : Blo 2133435 8106419 := bstep (se 1 (by rfl) ⟨6079814, by rfl⟩ : syracuseStep 8106419 = 12159629) B12159629
theorem B5404279 : Blo 2133435 5404279 := bstep (se 1 (by rfl) ⟨4053209, by rfl⟩ : syracuseStep 5404279 = 8106419) B8106419
theorem B7205705 : Blo 2133435 7205705 := bstep (se 2 (by rfl) ⟨2702139, by rfl⟩ : syracuseStep 7205705 = 5404279) B5404279
theorem B4803803 : Blo 2133435 4803803 := bstep (se 1 (by rfl) ⟨3602852, by rfl⟩ : syracuseStep 4803803 = 7205705) B7205705
theorem B3202535 : Blo 2133435 3202535 := bstep (se 1 (by rfl) ⟨2401901, by rfl⟩ : syracuseStep 3202535 = 4803803) B4803803
theorem B2135023 : Blo 2133435 2135023 := bstep (se 1 (by rfl) ⟨1601267, by rfl⟩ : syracuseStep 2135023 = 3202535) B3202535
theorem B3202541 : Blo 2133435 3202541 := bbase (se 3 (by rfl) ⟨600476, by rfl⟩ : syracuseStep 3202541 = 1200953) (by norm_num)
theorem B2135027 : Blo 2133435 2135027 := bstep (se 1 (by rfl) ⟨1601270, by rfl⟩ : syracuseStep 2135027 = 3202541) B3202541
theorem B4803821 : Blo 2133435 4803821 := bbase (se 3 (by rfl) ⟨900716, by rfl⟩ : syracuseStep 4803821 = 1801433) (by norm_num)
theorem B3202547 : Blo 2133435 3202547 := bstep (se 1 (by rfl) ⟨2401910, by rfl⟩ : syracuseStep 3202547 = 4803821) B4803821
theorem B2135031 : Blo 2133435 2135031 := bstep (se 1 (by rfl) ⟨1601273, by rfl⟩ : syracuseStep 2135031 = 3202547) B3202547
theorem B3039925 : Blo 2133435 3039925 := bbase (se 5 (by rfl) ⟨142496, by rfl⟩ : syracuseStep 3039925 = 284993) (by norm_num)
theorem B4053233 : Blo 2133435 4053233 := bstep (se 2 (by rfl) ⟨1519962, by rfl⟩ : syracuseStep 4053233 = 3039925) B3039925
theorem B2702155 : Blo 2133435 2702155 := bstep (se 1 (by rfl) ⟨2026616, by rfl⟩ : syracuseStep 2702155 = 4053233) B4053233
theorem B3602873 : Blo 2133435 3602873 := bstep (se 2 (by rfl) ⟨1351077, by rfl⟩ : syracuseStep 3602873 = 2702155) B2702155
theorem B2401915 : Blo 2133435 2401915 := bstep (se 1 (by rfl) ⟨1801436, by rfl⟩ : syracuseStep 2401915 = 3602873) B3602873
theorem B3202553 : Blo 2133435 3202553 := bstep (se 2 (by rfl) ⟨1200957, by rfl⟩ : syracuseStep 3202553 = 2401915) B2401915
theorem B2135035 : Blo 2133435 2135035 := bstep (se 1 (by rfl) ⟨1601276, by rfl⟩ : syracuseStep 2135035 = 3202553) B3202553
theorem B20012629 : Blo 2133435 20012629 := bbase (se 8 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 20012629 = 234523) (by norm_num)
theorem B26683505 : Blo 2133435 26683505 := bstep (se 2 (by rfl) ⟨10006314, by rfl⟩ : syracuseStep 26683505 = 20012629) B20012629
theorem B17789003 : Blo 2133435 17789003 := bstep (se 1 (by rfl) ⟨13341752, by rfl⟩ : syracuseStep 17789003 = 26683505) B26683505
theorem B11859335 : Blo 2133435 11859335 := bstep (se 1 (by rfl) ⟨8894501, by rfl⟩ : syracuseStep 11859335 = 17789003) B17789003
theorem B7906223 : Blo 2133435 7906223 := bstep (se 1 (by rfl) ⟨5929667, by rfl⟩ : syracuseStep 7906223 = 11859335) B11859335
theorem B21083261 : Blo 2133435 21083261 := bstep (se 3 (by rfl) ⟨3953111, by rfl⟩ : syracuseStep 21083261 = 7906223) B7906223
theorem B56222029 : Blo 2133435 56222029 := bstep (se 3 (by rfl) ⟨10541630, by rfl⟩ : syracuseStep 56222029 = 21083261) B21083261
theorem B299850821 : Blo 2133435 299850821 := bstep (se 4 (by rfl) ⟨28111014, by rfl⟩ : syracuseStep 299850821 = 56222029) B56222029
theorem B199900547 : Blo 2133435 199900547 := bstep (se 1 (by rfl) ⟨149925410, by rfl⟩ : syracuseStep 199900547 = 299850821) B299850821
theorem B133267031 : Blo 2133435 133267031 := bstep (se 1 (by rfl) ⟨99950273, by rfl⟩ : syracuseStep 133267031 = 199900547) B199900547
theorem B88844687 : Blo 2133435 88844687 := bstep (se 1 (by rfl) ⟨66633515, by rfl⟩ : syracuseStep 88844687 = 133267031) B133267031
theorem B59229791 : Blo 2133435 59229791 := bstep (se 1 (by rfl) ⟨44422343, by rfl⟩ : syracuseStep 59229791 = 88844687) B88844687
theorem B39486527 : Blo 2133435 39486527 := bstep (se 1 (by rfl) ⟨29614895, by rfl⟩ : syracuseStep 39486527 = 59229791) B59229791
theorem B26324351 : Blo 2133435 26324351 := bstep (se 1 (by rfl) ⟨19743263, by rfl⟩ : syracuseStep 26324351 = 39486527) B39486527
theorem B17549567 : Blo 2133435 17549567 := bstep (se 1 (by rfl) ⟨13162175, by rfl⟩ : syracuseStep 17549567 = 26324351) B26324351
theorem B11699711 : Blo 2133435 11699711 := bstep (se 1 (by rfl) ⟨8774783, by rfl⟩ : syracuseStep 11699711 = 17549567) B17549567
theorem B7799807 : Blo 2133435 7799807 := bstep (se 1 (by rfl) ⟨5849855, by rfl⟩ : syracuseStep 7799807 = 11699711) B11699711
theorem B5199871 : Blo 2133435 5199871 := bstep (se 1 (by rfl) ⟨3899903, by rfl⟩ : syracuseStep 5199871 = 7799807) B7799807
theorem B6933161 : Blo 2133435 6933161 := bstep (se 2 (by rfl) ⟨2599935, by rfl⟩ : syracuseStep 6933161 = 5199871) B5199871
theorem B18488429 : Blo 2133435 18488429 := bstep (se 3 (by rfl) ⟨3466580, by rfl⟩ : syracuseStep 18488429 = 6933161) B6933161
theorem B12325619 : Blo 2133435 12325619 := bstep (se 1 (by rfl) ⟨9244214, by rfl⟩ : syracuseStep 12325619 = 18488429) B18488429
theorem B32868317 : Blo 2133435 32868317 := bstep (se 3 (by rfl) ⟨6162809, by rfl⟩ : syracuseStep 32868317 = 12325619) B12325619
theorem B21912211 : Blo 2133435 21912211 := bstep (se 1 (by rfl) ⟨16434158, by rfl⟩ : syracuseStep 21912211 = 32868317) B32868317
theorem B116865125 : Blo 2133435 116865125 := bstep (se 4 (by rfl) ⟨10956105, by rfl⟩ : syracuseStep 116865125 = 21912211) B21912211
theorem B77910083 : Blo 2133435 77910083 := bstep (se 1 (by rfl) ⟨58432562, by rfl⟩ : syracuseStep 77910083 = 116865125) B116865125
theorem B51940055 : Blo 2133435 51940055 := bstep (se 1 (by rfl) ⟨38955041, by rfl⟩ : syracuseStep 51940055 = 77910083) B77910083
theorem B34626703 : Blo 2133435 34626703 := bstep (se 1 (by rfl) ⟨25970027, by rfl⟩ : syracuseStep 34626703 = 51940055) B51940055
theorem B46168937 : Blo 2133435 46168937 := bstep (se 2 (by rfl) ⟨17313351, by rfl⟩ : syracuseStep 46168937 = 34626703) B34626703
theorem B30779291 : Blo 2133435 30779291 := bstep (se 1 (by rfl) ⟨23084468, by rfl⟩ : syracuseStep 30779291 = 46168937) B46168937
theorem B82078109 : Blo 2133435 82078109 := bstep (se 3 (by rfl) ⟨15389645, by rfl⟩ : syracuseStep 82078109 = 30779291) B30779291
theorem B54718739 : Blo 2133435 54718739 := bstep (se 1 (by rfl) ⟨41039054, by rfl⟩ : syracuseStep 54718739 = 82078109) B82078109
theorem B36479159 : Blo 2133435 36479159 := bstep (se 1 (by rfl) ⟨27359369, by rfl⟩ : syracuseStep 36479159 = 54718739) B54718739
theorem B24319439 : Blo 2133435 24319439 := bstep (se 1 (by rfl) ⟨18239579, by rfl⟩ : syracuseStep 24319439 = 36479159) B36479159
theorem B16212959 : Blo 2133435 16212959 := bstep (se 1 (by rfl) ⟨12159719, by rfl⟩ : syracuseStep 16212959 = 24319439) B24319439
theorem B10808639 : Blo 2133435 10808639 := bstep (se 1 (by rfl) ⟨8106479, by rfl⟩ : syracuseStep 10808639 = 16212959) B16212959
theorem B7205759 : Blo 2133435 7205759 := bstep (se 1 (by rfl) ⟨5404319, by rfl⟩ : syracuseStep 7205759 = 10808639) B10808639
theorem B4803839 : Blo 2133435 4803839 := bstep (se 1 (by rfl) ⟨3602879, by rfl⟩ : syracuseStep 4803839 = 7205759) B7205759
theorem B3202559 : Blo 2133435 3202559 := bstep (se 1 (by rfl) ⟨2401919, by rfl⟩ : syracuseStep 3202559 = 4803839) B4803839
theorem B2135039 : Blo 2133435 2135039 := bstep (se 1 (by rfl) ⟨1601279, by rfl⟩ : syracuseStep 2135039 = 3202559) B3202559
theorem B3202565 : Blo 2133435 3202565 := bbase (se 4 (by rfl) ⟨300240, by rfl⟩ : syracuseStep 3202565 = 600481) (by norm_num)
theorem B2135043 : Blo 2133435 2135043 := bstep (se 1 (by rfl) ⟨1601282, by rfl⟩ : syracuseStep 2135043 = 3202565) B3202565
theorem B3602893 : Blo 2133435 3602893 := bbase (se 3 (by rfl) ⟨675542, by rfl⟩ : syracuseStep 3602893 = 1351085) (by norm_num)
theorem B4803857 : Blo 2133435 4803857 := bstep (se 2 (by rfl) ⟨1801446, by rfl⟩ : syracuseStep 4803857 = 3602893) B3602893
theorem B3202571 : Blo 2133435 3202571 := bstep (se 1 (by rfl) ⟨2401928, by rfl⟩ : syracuseStep 3202571 = 4803857) B4803857
theorem B2135047 : Blo 2133435 2135047 := bstep (se 1 (by rfl) ⟨1601285, by rfl⟩ : syracuseStep 2135047 = 3202571) B3202571
theorem B2401933 : Blo 2133435 2401933 := bbase (se 3 (by rfl) ⟨450362, by rfl⟩ : syracuseStep 2401933 = 900725) (by norm_num)
theorem B3202577 : Blo 2133435 3202577 := bstep (se 2 (by rfl) ⟨1200966, by rfl⟩ : syracuseStep 3202577 = 2401933) B2401933
theorem B2135051 : Blo 2133435 2135051 := bstep (se 1 (by rfl) ⟨1601288, by rfl⟩ : syracuseStep 2135051 = 3202577) B3202577
theorem B7205813 : Blo 2133435 7205813 := bbase (se 5 (by rfl) ⟨337772, by rfl⟩ : syracuseStep 7205813 = 675545) (by norm_num)
theorem B4803875 : Blo 2133435 4803875 := bstep (se 1 (by rfl) ⟨3602906, by rfl⟩ : syracuseStep 4803875 = 7205813) B7205813
theorem B3202583 : Blo 2133435 3202583 := bstep (se 1 (by rfl) ⟨2401937, by rfl⟩ : syracuseStep 3202583 = 4803875) B4803875
theorem B2135055 : Blo 2133435 2135055 := bstep (se 1 (by rfl) ⟨1601291, by rfl⟩ : syracuseStep 2135055 = 3202583) B3202583
theorem B3202589 : Blo 2133435 3202589 := bbase (se 3 (by rfl) ⟨600485, by rfl⟩ : syracuseStep 3202589 = 1200971) (by norm_num)
theorem B2135059 : Blo 2133435 2135059 := bstep (se 1 (by rfl) ⟨1601294, by rfl⟩ : syracuseStep 2135059 = 3202589) B3202589
theorem B4803893 : Blo 2133435 4803893 := bbase (se 5 (by rfl) ⟨225182, by rfl⟩ : syracuseStep 4803893 = 450365) (by norm_num)
theorem B3202595 : Blo 2133435 3202595 := bstep (se 1 (by rfl) ⟨2401946, by rfl⟩ : syracuseStep 3202595 = 4803893) B4803893
theorem B2135063 : Blo 2133435 2135063 := bstep (se 1 (by rfl) ⟨1601297, by rfl⟩ : syracuseStep 2135063 = 3202595) B3202595
theorem B32868757 : Blo 2133435 32868757 := bbase (se 6 (by rfl) ⟨770361, by rfl⟩ : syracuseStep 32868757 = 1540723) (by norm_num)
theorem B43825009 : Blo 2133435 43825009 := bstep (se 2 (by rfl) ⟨16434378, by rfl⟩ : syracuseStep 43825009 = 32868757) B32868757
theorem B58433345 : Blo 2133435 58433345 := bstep (se 2 (by rfl) ⟨21912504, by rfl⟩ : syracuseStep 58433345 = 43825009) B43825009
theorem B38955563 : Blo 2133435 38955563 := bstep (se 1 (by rfl) ⟨29216672, by rfl⟩ : syracuseStep 38955563 = 58433345) B58433345
theorem B25970375 : Blo 2133435 25970375 := bstep (se 1 (by rfl) ⟨19477781, by rfl⟩ : syracuseStep 25970375 = 38955563) B38955563
theorem B17313583 : Blo 2133435 17313583 := bstep (se 1 (by rfl) ⟨12985187, by rfl⟩ : syracuseStep 17313583 = 25970375) B25970375
theorem B23084777 : Blo 2133435 23084777 := bstep (se 2 (by rfl) ⟨8656791, by rfl⟩ : syracuseStep 23084777 = 17313583) B17313583
theorem B15389851 : Blo 2133435 15389851 := bstep (se 1 (by rfl) ⟨11542388, by rfl⟩ : syracuseStep 15389851 = 23084777) B23084777
theorem B20519801 : Blo 2133435 20519801 := bstep (se 2 (by rfl) ⟨7694925, by rfl⟩ : syracuseStep 20519801 = 15389851) B15389851
theorem B13679867 : Blo 2133435 13679867 := bstep (se 1 (by rfl) ⟨10259900, by rfl⟩ : syracuseStep 13679867 = 20519801) B20519801
theorem B9119911 : Blo 2133435 9119911 := bstep (se 1 (by rfl) ⟨6839933, by rfl⟩ : syracuseStep 9119911 = 13679867) B13679867
theorem B12159881 : Blo 2133435 12159881 := bstep (se 2 (by rfl) ⟨4559955, by rfl⟩ : syracuseStep 12159881 = 9119911) B9119911
theorem B8106587 : Blo 2133435 8106587 := bstep (se 1 (by rfl) ⟨6079940, by rfl⟩ : syracuseStep 8106587 = 12159881) B12159881
theorem B5404391 : Blo 2133435 5404391 := bstep (se 1 (by rfl) ⟨4053293, by rfl⟩ : syracuseStep 5404391 = 8106587) B8106587
theorem B3602927 : Blo 2133435 3602927 := bstep (se 1 (by rfl) ⟨2702195, by rfl⟩ : syracuseStep 3602927 = 5404391) B5404391
theorem B2401951 : Blo 2133435 2401951 := bstep (se 1 (by rfl) ⟨1801463, by rfl⟩ : syracuseStep 2401951 = 3602927) B3602927
theorem B3202601 : Blo 2133435 3202601 := bstep (se 2 (by rfl) ⟨1200975, by rfl⟩ : syracuseStep 3202601 = 2401951) B2401951
theorem B2135067 : Blo 2133435 2135067 := bstep (se 1 (by rfl) ⟨1601300, by rfl⟩ : syracuseStep 2135067 = 3202601) B3202601
theorem B31199701 : Blo 2133435 31199701 := bbase (se 7 (by rfl) ⟨365621, by rfl⟩ : syracuseStep 31199701 = 731243) (by norm_num)
theorem B41599601 : Blo 2133435 41599601 := bstep (se 2 (by rfl) ⟨15599850, by rfl⟩ : syracuseStep 41599601 = 31199701) B31199701
theorem B27733067 : Blo 2133435 27733067 := bstep (se 1 (by rfl) ⟨20799800, by rfl⟩ : syracuseStep 27733067 = 41599601) B41599601
theorem B18488711 : Blo 2133435 18488711 := bstep (se 1 (by rfl) ⟨13866533, by rfl⟩ : syracuseStep 18488711 = 27733067) B27733067
theorem B12325807 : Blo 2133435 12325807 := bstep (se 1 (by rfl) ⟨9244355, by rfl⟩ : syracuseStep 12325807 = 18488711) B18488711
theorem B16434409 : Blo 2133435 16434409 := bstep (se 2 (by rfl) ⟨6162903, by rfl⟩ : syracuseStep 16434409 = 12325807) B12325807
theorem B21912545 : Blo 2133435 21912545 := bstep (se 2 (by rfl) ⟨8217204, by rfl⟩ : syracuseStep 21912545 = 16434409) B16434409
theorem B14608363 : Blo 2133435 14608363 := bstep (se 1 (by rfl) ⟨10956272, by rfl⟩ : syracuseStep 14608363 = 21912545) B21912545
theorem B19477817 : Blo 2133435 19477817 := bstep (se 2 (by rfl) ⟨7304181, by rfl⟩ : syracuseStep 19477817 = 14608363) B14608363
theorem B12985211 : Blo 2133435 12985211 := bstep (se 1 (by rfl) ⟨9738908, by rfl⟩ : syracuseStep 12985211 = 19477817) B19477817
theorem B8656807 : Blo 2133435 8656807 := bstep (se 1 (by rfl) ⟨6492605, by rfl⟩ : syracuseStep 8656807 = 12985211) B12985211
theorem B11542409 : Blo 2133435 11542409 := bstep (se 2 (by rfl) ⟨4328403, by rfl⟩ : syracuseStep 11542409 = 8656807) B8656807
theorem B7694939 : Blo 2133435 7694939 := bstep (se 1 (by rfl) ⟨5771204, by rfl⟩ : syracuseStep 7694939 = 11542409) B11542409
theorem B20519837 : Blo 2133435 20519837 := bstep (se 3 (by rfl) ⟨3847469, by rfl⟩ : syracuseStep 20519837 = 7694939) B7694939
theorem B13679891 : Blo 2133435 13679891 := bstep (se 1 (by rfl) ⟨10259918, by rfl⟩ : syracuseStep 13679891 = 20519837) B20519837
theorem B9119927 : Blo 2133435 9119927 := bstep (se 1 (by rfl) ⟨6839945, by rfl⟩ : syracuseStep 9119927 = 13679891) B13679891
theorem B6079951 : Blo 2133435 6079951 := bstep (se 1 (by rfl) ⟨4559963, by rfl⟩ : syracuseStep 6079951 = 9119927) B9119927
theorem B8106601 : Blo 2133435 8106601 := bstep (se 2 (by rfl) ⟨3039975, by rfl⟩ : syracuseStep 8106601 = 6079951) B6079951
theorem B10808801 : Blo 2133435 10808801 := bstep (se 2 (by rfl) ⟨4053300, by rfl⟩ : syracuseStep 10808801 = 8106601) B8106601
theorem B7205867 : Blo 2133435 7205867 := bstep (se 1 (by rfl) ⟨5404400, by rfl⟩ : syracuseStep 7205867 = 10808801) B10808801
theorem B4803911 : Blo 2133435 4803911 := bstep (se 1 (by rfl) ⟨3602933, by rfl⟩ : syracuseStep 4803911 = 7205867) B7205867
theorem B3202607 : Blo 2133435 3202607 := bstep (se 1 (by rfl) ⟨2401955, by rfl⟩ : syracuseStep 3202607 = 4803911) B4803911
theorem B2135071 : Blo 2133435 2135071 := bstep (se 1 (by rfl) ⟨1601303, by rfl⟩ : syracuseStep 2135071 = 3202607) B3202607
theorem B3202613 : Blo 2133435 3202613 := bbase (se 5 (by rfl) ⟨150122, by rfl⟩ : syracuseStep 3202613 = 300245) (by norm_num)
theorem B2135075 : Blo 2133435 2135075 := bstep (se 1 (by rfl) ⟨1601306, by rfl⟩ : syracuseStep 2135075 = 3202613) B3202613
theorem B5404421 : Blo 2133435 5404421 := bbase (se 4 (by rfl) ⟨506664, by rfl⟩ : syracuseStep 5404421 = 1013329) (by norm_num)
theorem B3602947 : Blo 2133435 3602947 := bstep (se 1 (by rfl) ⟨2702210, by rfl⟩ : syracuseStep 3602947 = 5404421) B5404421
theorem B4803929 : Blo 2133435 4803929 := bstep (se 2 (by rfl) ⟨1801473, by rfl⟩ : syracuseStep 4803929 = 3602947) B3602947
theorem B3202619 : Blo 2133435 3202619 := bstep (se 1 (by rfl) ⟨2401964, by rfl⟩ : syracuseStep 3202619 = 4803929) B4803929
theorem B2135079 : Blo 2133435 2135079 := bstep (se 1 (by rfl) ⟨1601309, by rfl⟩ : syracuseStep 2135079 = 3202619) B3202619
theorem B2401969 : Blo 2133435 2401969 := bbase (se 2 (by rfl) ⟨900738, by rfl⟩ : syracuseStep 2401969 = 1801477) (by norm_num)
theorem B3202625 : Blo 2133435 3202625 := bstep (se 2 (by rfl) ⟨1200984, by rfl⟩ : syracuseStep 3202625 = 2401969) B2401969
theorem B2135083 : Blo 2133435 2135083 := bstep (se 1 (by rfl) ⟨1601312, by rfl⟩ : syracuseStep 2135083 = 3202625) B3202625
theorem B17313749 : Blo 2133435 17313749 := bbase (se 7 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 17313749 = 405791) (by norm_num)
theorem B11542499 : Blo 2133435 11542499 := bstep (se 1 (by rfl) ⟨8656874, by rfl⟩ : syracuseStep 11542499 = 17313749) B17313749
theorem B7694999 : Blo 2133435 7694999 := bstep (se 1 (by rfl) ⟨5771249, by rfl⟩ : syracuseStep 7694999 = 11542499) B11542499
theorem B5129999 : Blo 2133435 5129999 := bstep (se 1 (by rfl) ⟨3847499, by rfl⟩ : syracuseStep 5129999 = 7694999) B7694999
theorem B3419999 : Blo 2133435 3419999 := bstep (se 1 (by rfl) ⟨2564999, by rfl⟩ : syracuseStep 3419999 = 5129999) B5129999
theorem B2279999 : Blo 2133435 2279999 := bstep (se 1 (by rfl) ⟨1709999, by rfl⟩ : syracuseStep 2279999 = 3419999) B3419999
theorem B6079997 : Blo 2133435 6079997 := bstep (se 3 (by rfl) ⟨1139999, by rfl⟩ : syracuseStep 6079997 = 2279999) B2279999
theorem B4053331 : Blo 2133435 4053331 := bstep (se 1 (by rfl) ⟨3039998, by rfl⟩ : syracuseStep 4053331 = 6079997) B6079997
theorem B5404441 : Blo 2133435 5404441 := bstep (se 2 (by rfl) ⟨2026665, by rfl⟩ : syracuseStep 5404441 = 4053331) B4053331
theorem B7205921 : Blo 2133435 7205921 := bstep (se 2 (by rfl) ⟨2702220, by rfl⟩ : syracuseStep 7205921 = 5404441) B5404441
theorem B4803947 : Blo 2133435 4803947 := bstep (se 1 (by rfl) ⟨3602960, by rfl⟩ : syracuseStep 4803947 = 7205921) B7205921
theorem B3202631 : Blo 2133435 3202631 := bstep (se 1 (by rfl) ⟨2401973, by rfl⟩ : syracuseStep 3202631 = 4803947) B4803947
theorem B2135087 : Blo 2133435 2135087 := bstep (se 1 (by rfl) ⟨1601315, by rfl⟩ : syracuseStep 2135087 = 3202631) B3202631
theorem B3202637 : Blo 2133435 3202637 := bbase (se 3 (by rfl) ⟨600494, by rfl⟩ : syracuseStep 3202637 = 1200989) (by norm_num)
theorem B2135091 : Blo 2133435 2135091 := bstep (se 1 (by rfl) ⟨1601318, by rfl⟩ : syracuseStep 2135091 = 3202637) B3202637
theorem B4803965 : Blo 2133435 4803965 := bbase (se 3 (by rfl) ⟨900743, by rfl⟩ : syracuseStep 4803965 = 1801487) (by norm_num)
theorem B3202643 : Blo 2133435 3202643 := bstep (se 1 (by rfl) ⟨2401982, by rfl⟩ : syracuseStep 3202643 = 4803965) B4803965
theorem B2135095 : Blo 2133435 2135095 := bstep (se 1 (by rfl) ⟨1601321, by rfl⟩ : syracuseStep 2135095 = 3202643) B3202643
theorem B3602981 : Blo 2133435 3602981 := bbase (se 4 (by rfl) ⟨337779, by rfl⟩ : syracuseStep 3602981 = 675559) (by norm_num)
theorem B2401987 : Blo 2133435 2401987 := bstep (se 1 (by rfl) ⟨1801490, by rfl⟩ : syracuseStep 2401987 = 3602981) B3602981
theorem B3202649 : Blo 2133435 3202649 := bstep (se 2 (by rfl) ⟨1200993, by rfl⟩ : syracuseStep 3202649 = 2401987) B2401987
theorem B2135099 : Blo 2133435 2135099 := bstep (se 1 (by rfl) ⟨1601324, by rfl⟩ : syracuseStep 2135099 = 3202649) B3202649
theorem B3040021 : Blo 2133435 3040021 := bbase (se 6 (by rfl) ⟨71250, by rfl⟩ : syracuseStep 3040021 = 142501) (by norm_num)
theorem B16213445 : Blo 2133435 16213445 := bstep (se 4 (by rfl) ⟨1520010, by rfl⟩ : syracuseStep 16213445 = 3040021) B3040021
theorem B10808963 : Blo 2133435 10808963 := bstep (se 1 (by rfl) ⟨8106722, by rfl⟩ : syracuseStep 10808963 = 16213445) B16213445
theorem B7205975 : Blo 2133435 7205975 := bstep (se 1 (by rfl) ⟨5404481, by rfl⟩ : syracuseStep 7205975 = 10808963) B10808963
theorem B4803983 : Blo 2133435 4803983 := bstep (se 1 (by rfl) ⟨3602987, by rfl⟩ : syracuseStep 4803983 = 7205975) B7205975
theorem B3202655 : Blo 2133435 3202655 := bstep (se 1 (by rfl) ⟨2401991, by rfl⟩ : syracuseStep 3202655 = 4803983) B4803983
theorem B2135103 : Blo 2133435 2135103 := bstep (se 1 (by rfl) ⟨1601327, by rfl⟩ : syracuseStep 2135103 = 3202655) B3202655
theorem B3202661 : Blo 2133435 3202661 := bbase (se 4 (by rfl) ⟨300249, by rfl⟩ : syracuseStep 3202661 = 600499) (by norm_num)
theorem B2135107 : Blo 2133435 2135107 := bstep (se 1 (by rfl) ⟨1601330, by rfl⟩ : syracuseStep 2135107 = 3202661) B3202661
theorem B2280025 : Blo 2133435 2280025 := bbase (se 2 (by rfl) ⟨855009, by rfl⟩ : syracuseStep 2280025 = 1710019) (by norm_num)
theorem B3040033 : Blo 2133435 3040033 := bstep (se 2 (by rfl) ⟨1140012, by rfl⟩ : syracuseStep 3040033 = 2280025) B2280025
theorem B4053377 : Blo 2133435 4053377 := bstep (se 2 (by rfl) ⟨1520016, by rfl⟩ : syracuseStep 4053377 = 3040033) B3040033
theorem B2702251 : Blo 2133435 2702251 := bstep (se 1 (by rfl) ⟨2026688, by rfl⟩ : syracuseStep 2702251 = 4053377) B4053377
theorem B3603001 : Blo 2133435 3603001 := bstep (se 2 (by rfl) ⟨1351125, by rfl⟩ : syracuseStep 3603001 = 2702251) B2702251
theorem B4804001 : Blo 2133435 4804001 := bstep (se 2 (by rfl) ⟨1801500, by rfl⟩ : syracuseStep 4804001 = 3603001) B3603001
theorem B3202667 : Blo 2133435 3202667 := bstep (se 1 (by rfl) ⟨2402000, by rfl⟩ : syracuseStep 3202667 = 4804001) B4804001
theorem B2135111 : Blo 2133435 2135111 := bstep (se 1 (by rfl) ⟨1601333, by rfl⟩ : syracuseStep 2135111 = 3202667) B3202667
theorem B2402005 : Blo 2133435 2402005 := bbase (se 7 (by rfl) ⟨28148, by rfl⟩ : syracuseStep 2402005 = 56297) (by norm_num)
theorem B3202673 : Blo 2133435 3202673 := bstep (se 2 (by rfl) ⟨1201002, by rfl⟩ : syracuseStep 3202673 = 2402005) B2402005
theorem B2135115 : Blo 2133435 2135115 := bstep (se 1 (by rfl) ⟨1601336, by rfl⟩ : syracuseStep 2135115 = 3202673) B3202673
theorem B2702261 : Blo 2133435 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B7206029 : Blo 2133435 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B4804019 : Blo 2133435 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B3202679 : Blo 2133435 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B2135119 : Blo 2133435 2135119 := bstep (se 1 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 2135119 = 3202679) B3202679
theorem B3202685 : Blo 2133435 3202685 := bbase (se 3 (by rfl) ⟨600503, by rfl⟩ : syracuseStep 3202685 = 1201007) (by norm_num)
theorem B2135123 : Blo 2133435 2135123 := bstep (se 1 (by rfl) ⟨1601342, by rfl⟩ : syracuseStep 2135123 = 3202685) B3202685
theorem B4804037 : Blo 2133435 4804037 := bbase (se 4 (by rfl) ⟨450378, by rfl⟩ : syracuseStep 4804037 = 900757) (by norm_num)
theorem B3202691 : Blo 2133435 3202691 := bstep (se 1 (by rfl) ⟨2402018, by rfl⟩ : syracuseStep 3202691 = 4804037) B4804037
theorem B2135127 : Blo 2133435 2135127 := bstep (se 1 (by rfl) ⟨1601345, by rfl⟩ : syracuseStep 2135127 = 3202691) B3202691
theorem B7695157 : Blo 2133435 7695157 := bbase (se 5 (by rfl) ⟨360710, by rfl⟩ : syracuseStep 7695157 = 721421) (by norm_num)
theorem B10260209 : Blo 2133435 10260209 := bstep (se 2 (by rfl) ⟨3847578, by rfl⟩ : syracuseStep 10260209 = 7695157) B7695157
theorem B6840139 : Blo 2133435 6840139 := bstep (se 1 (by rfl) ⟨5130104, by rfl⟩ : syracuseStep 6840139 = 10260209) B10260209
theorem B9120185 : Blo 2133435 9120185 := bstep (se 2 (by rfl) ⟨3420069, by rfl⟩ : syracuseStep 9120185 = 6840139) B6840139
theorem B6080123 : Blo 2133435 6080123 := bstep (se 1 (by rfl) ⟨4560092, by rfl⟩ : syracuseStep 6080123 = 9120185) B9120185
theorem B4053415 : Blo 2133435 4053415 := bstep (se 1 (by rfl) ⟨3040061, by rfl⟩ : syracuseStep 4053415 = 6080123) B6080123
theorem B5404553 : Blo 2133435 5404553 := bstep (se 2 (by rfl) ⟨2026707, by rfl⟩ : syracuseStep 5404553 = 4053415) B4053415
theorem B3603035 : Blo 2133435 3603035 := bstep (se 1 (by rfl) ⟨2702276, by rfl⟩ : syracuseStep 3603035 = 5404553) B5404553
theorem B2402023 : Blo 2133435 2402023 := bstep (se 1 (by rfl) ⟨1801517, by rfl⟩ : syracuseStep 2402023 = 3603035) B3603035
theorem B3202697 : Blo 2133435 3202697 := bstep (se 2 (by rfl) ⟨1201011, by rfl⟩ : syracuseStep 3202697 = 2402023) B2402023
theorem B2135131 : Blo 2133435 2135131 := bstep (se 1 (by rfl) ⟨1601348, by rfl⟩ : syracuseStep 2135131 = 3202697) B3202697
theorem B10809125 : Blo 2133435 10809125 := bbase (se 4 (by rfl) ⟨1013355, by rfl⟩ : syracuseStep 10809125 = 2026711) (by norm_num)
theorem B7206083 : Blo 2133435 7206083 := bstep (se 1 (by rfl) ⟨5404562, by rfl⟩ : syracuseStep 7206083 = 10809125) B10809125
theorem B4804055 : Blo 2133435 4804055 := bstep (se 1 (by rfl) ⟨3603041, by rfl⟩ : syracuseStep 4804055 = 7206083) B7206083
theorem B3202703 : Blo 2133435 3202703 := bstep (se 1 (by rfl) ⟨2402027, by rfl⟩ : syracuseStep 3202703 = 4804055) B4804055
theorem B2135135 : Blo 2133435 2135135 := bstep (se 1 (by rfl) ⟨1601351, by rfl⟩ : syracuseStep 2135135 = 3202703) B3202703
theorem B3202709 : Blo 2133435 3202709 := bbase (se 6 (by rfl) ⟨75063, by rfl⟩ : syracuseStep 3202709 = 150127) (by norm_num)
theorem B2135139 : Blo 2133435 2135139 := bstep (se 1 (by rfl) ⟨1601354, by rfl⟩ : syracuseStep 2135139 = 3202709) B3202709
theorem B38956949 : Blo 2133435 38956949 := bbase (se 6 (by rfl) ⟨913053, by rfl⟩ : syracuseStep 38956949 = 1826107) (by norm_num)
theorem B25971299 : Blo 2133435 25971299 := bstep (se 1 (by rfl) ⟨19478474, by rfl⟩ : syracuseStep 25971299 = 38956949) B38956949
theorem B17314199 : Blo 2133435 17314199 := bstep (se 1 (by rfl) ⟨12985649, by rfl⟩ : syracuseStep 17314199 = 25971299) B25971299
theorem B11542799 : Blo 2133435 11542799 := bstep (se 1 (by rfl) ⟨8657099, by rfl⟩ : syracuseStep 11542799 = 17314199) B17314199
theorem B7695199 : Blo 2133435 7695199 := bstep (se 1 (by rfl) ⟨5771399, by rfl⟩ : syracuseStep 7695199 = 11542799) B11542799
theorem B10260265 : Blo 2133435 10260265 := bstep (se 2 (by rfl) ⟨3847599, by rfl⟩ : syracuseStep 10260265 = 7695199) B7695199
theorem B13680353 : Blo 2133435 13680353 := bstep (se 2 (by rfl) ⟨5130132, by rfl⟩ : syracuseStep 13680353 = 10260265) B10260265
theorem B9120235 : Blo 2133435 9120235 := bstep (se 1 (by rfl) ⟨6840176, by rfl⟩ : syracuseStep 9120235 = 13680353) B13680353
theorem B12160313 : Blo 2133435 12160313 := bstep (se 2 (by rfl) ⟨4560117, by rfl⟩ : syracuseStep 12160313 = 9120235) B9120235
theorem B8106875 : Blo 2133435 8106875 := bstep (se 1 (by rfl) ⟨6080156, by rfl⟩ : syracuseStep 8106875 = 12160313) B12160313
theorem B5404583 : Blo 2133435 5404583 := bstep (se 1 (by rfl) ⟨4053437, by rfl⟩ : syracuseStep 5404583 = 8106875) B8106875
theorem B3603055 : Blo 2133435 3603055 := bstep (se 1 (by rfl) ⟨2702291, by rfl⟩ : syracuseStep 3603055 = 5404583) B5404583
theorem B4804073 : Blo 2133435 4804073 := bstep (se 2 (by rfl) ⟨1801527, by rfl⟩ : syracuseStep 4804073 = 3603055) B3603055
theorem B3202715 : Blo 2133435 3202715 := bstep (se 1 (by rfl) ⟨2402036, by rfl⟩ : syracuseStep 3202715 = 4804073) B4804073
theorem B2135143 : Blo 2133435 2135143 := bstep (se 1 (by rfl) ⟨1601357, by rfl⟩ : syracuseStep 2135143 = 3202715) B3202715
theorem B2402041 : Blo 2133435 2402041 := bbase (se 2 (by rfl) ⟨900765, by rfl⟩ : syracuseStep 2402041 = 1801531) (by norm_num)
theorem B3202721 : Blo 2133435 3202721 := bstep (se 2 (by rfl) ⟨1201020, by rfl⟩ : syracuseStep 3202721 = 2402041) B2402041
theorem B2135147 : Blo 2133435 2135147 := bstep (se 1 (by rfl) ⟨1601360, by rfl⟩ : syracuseStep 2135147 = 3202721) B3202721
theorem B3420101 : Blo 2133435 3420101 := bbase (se 4 (by rfl) ⟨320634, by rfl⟩ : syracuseStep 3420101 = 641269) (by norm_num)
theorem B9120269 : Blo 2133435 9120269 := bstep (se 3 (by rfl) ⟨1710050, by rfl⟩ : syracuseStep 9120269 = 3420101) B3420101
theorem B6080179 : Blo 2133435 6080179 := bstep (se 1 (by rfl) ⟨4560134, by rfl⟩ : syracuseStep 6080179 = 9120269) B9120269
theorem B8106905 : Blo 2133435 8106905 := bstep (se 2 (by rfl) ⟨3040089, by rfl⟩ : syracuseStep 8106905 = 6080179) B6080179
theorem B5404603 : Blo 2133435 5404603 := bstep (se 1 (by rfl) ⟨4053452, by rfl⟩ : syracuseStep 5404603 = 8106905) B8106905
theorem B7206137 : Blo 2133435 7206137 := bstep (se 2 (by rfl) ⟨2702301, by rfl⟩ : syracuseStep 7206137 = 5404603) B5404603
theorem B4804091 : Blo 2133435 4804091 := bstep (se 1 (by rfl) ⟨3603068, by rfl⟩ : syracuseStep 4804091 = 7206137) B7206137
theorem B3202727 : Blo 2133435 3202727 := bstep (se 1 (by rfl) ⟨2402045, by rfl⟩ : syracuseStep 3202727 = 4804091) B4804091
theorem B2135151 : Blo 2133435 2135151 := bstep (se 1 (by rfl) ⟨1601363, by rfl⟩ : syracuseStep 2135151 = 3202727) B3202727
theorem B3202733 : Blo 2133435 3202733 := bbase (se 3 (by rfl) ⟨600512, by rfl⟩ : syracuseStep 3202733 = 1201025) (by norm_num)
theorem B2135155 : Blo 2133435 2135155 := bstep (se 1 (by rfl) ⟨1601366, by rfl⟩ : syracuseStep 2135155 = 3202733) B3202733
theorem B4804109 : Blo 2133435 4804109 := bbase (se 3 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 4804109 = 1801541) (by norm_num)
theorem B3202739 : Blo 2133435 3202739 := bstep (se 1 (by rfl) ⟨2402054, by rfl⟩ : syracuseStep 3202739 = 4804109) B4804109
theorem B2135159 : Blo 2133435 2135159 := bstep (se 1 (by rfl) ⟨1601369, by rfl⟩ : syracuseStep 2135159 = 3202739) B3202739
theorem B2702317 : Blo 2133435 2702317 := bbase (se 3 (by rfl) ⟨506684, by rfl⟩ : syracuseStep 2702317 = 1013369) (by norm_num)
theorem B3603089 : Blo 2133435 3603089 := bstep (se 2 (by rfl) ⟨1351158, by rfl⟩ : syracuseStep 3603089 = 2702317) B2702317
theorem B2402059 : Blo 2133435 2402059 := bstep (se 1 (by rfl) ⟨1801544, by rfl⟩ : syracuseStep 2402059 = 3603089) B3603089
theorem B3202745 : Blo 2133435 3202745 := bstep (se 2 (by rfl) ⟨1201029, by rfl⟩ : syracuseStep 3202745 = 2402059) B2402059
theorem B2135163 : Blo 2133435 2135163 := bstep (se 1 (by rfl) ⟨1601372, by rfl⟩ : syracuseStep 2135163 = 3202745) B3202745
theorem B2311193 : Blo 2133435 2311193 := bbase (se 2 (by rfl) ⟨866697, by rfl⟩ : syracuseStep 2311193 = 1733395) (by norm_num)
theorem B6163181 : Blo 2133435 6163181 := bstep (se 3 (by rfl) ⟨1155596, by rfl⟩ : syracuseStep 6163181 = 2311193) B2311193
theorem B4108787 : Blo 2133435 4108787 := bstep (se 1 (by rfl) ⟨3081590, by rfl⟩ : syracuseStep 4108787 = 6163181) B6163181
theorem B2739191 : Blo 2133435 2739191 := bstep (se 1 (by rfl) ⟨2054393, by rfl⟩ : syracuseStep 2739191 = 4108787) B4108787
theorem B7304509 : Blo 2133435 7304509 := bstep (se 3 (by rfl) ⟨1369595, by rfl⟩ : syracuseStep 7304509 = 2739191) B2739191
theorem B38957381 : Blo 2133435 38957381 := bstep (se 4 (by rfl) ⟨3652254, by rfl⟩ : syracuseStep 38957381 = 7304509) B7304509
theorem B25971587 : Blo 2133435 25971587 := bstep (se 1 (by rfl) ⟨19478690, by rfl⟩ : syracuseStep 25971587 = 38957381) B38957381
theorem B17314391 : Blo 2133435 17314391 := bstep (se 1 (by rfl) ⟨12985793, by rfl⟩ : syracuseStep 17314391 = 25971587) B25971587
theorem B11542927 : Blo 2133435 11542927 := bstep (se 1 (by rfl) ⟨8657195, by rfl⟩ : syracuseStep 11542927 = 17314391) B17314391
theorem B15390569 : Blo 2133435 15390569 := bstep (se 2 (by rfl) ⟨5771463, by rfl⟩ : syracuseStep 15390569 = 11542927) B11542927
theorem B10260379 : Blo 2133435 10260379 := bstep (se 1 (by rfl) ⟨7695284, by rfl⟩ : syracuseStep 10260379 = 15390569) B15390569
theorem B13680505 : Blo 2133435 13680505 := bstep (se 2 (by rfl) ⟨5130189, by rfl⟩ : syracuseStep 13680505 = 10260379) B10260379
theorem B18240673 : Blo 2133435 18240673 := bstep (se 2 (by rfl) ⟨6840252, by rfl⟩ : syracuseStep 18240673 = 13680505) B13680505
theorem B24320897 : Blo 2133435 24320897 := bstep (se 2 (by rfl) ⟨9120336, by rfl⟩ : syracuseStep 24320897 = 18240673) B18240673
theorem B16213931 : Blo 2133435 16213931 := bstep (se 1 (by rfl) ⟨12160448, by rfl⟩ : syracuseStep 16213931 = 24320897) B24320897
theorem B10809287 : Blo 2133435 10809287 := bstep (se 1 (by rfl) ⟨8106965, by rfl⟩ : syracuseStep 10809287 = 16213931) B16213931
theorem B7206191 : Blo 2133435 7206191 := bstep (se 1 (by rfl) ⟨5404643, by rfl⟩ : syracuseStep 7206191 = 10809287) B10809287
theorem B4804127 : Blo 2133435 4804127 := bstep (se 1 (by rfl) ⟨3603095, by rfl⟩ : syracuseStep 4804127 = 7206191) B7206191
theorem B3202751 : Blo 2133435 3202751 := bstep (se 1 (by rfl) ⟨2402063, by rfl⟩ : syracuseStep 3202751 = 4804127) B4804127
theorem B2135167 : Blo 2133435 2135167 := bstep (se 1 (by rfl) ⟨1601375, by rfl⟩ : syracuseStep 2135167 = 3202751) B3202751
theorem B3202757 : Blo 2133435 3202757 := bbase (se 4 (by rfl) ⟨300258, by rfl⟩ : syracuseStep 3202757 = 600517) (by norm_num)
theorem B2135171 : Blo 2133435 2135171 := bstep (se 1 (by rfl) ⟨1601378, by rfl⟩ : syracuseStep 2135171 = 3202757) B3202757
theorem B3603109 : Blo 2133435 3603109 := bbase (se 4 (by rfl) ⟨337791, by rfl⟩ : syracuseStep 3603109 = 675583) (by norm_num)
theorem B4804145 : Blo 2133435 4804145 := bstep (se 2 (by rfl) ⟨1801554, by rfl⟩ : syracuseStep 4804145 = 3603109) B3603109
theorem B3202763 : Blo 2133435 3202763 := bstep (se 1 (by rfl) ⟨2402072, by rfl⟩ : syracuseStep 3202763 = 4804145) B4804145
theorem B2135175 : Blo 2133435 2135175 := bstep (se 1 (by rfl) ⟨1601381, by rfl⟩ : syracuseStep 2135175 = 3202763) B3202763
theorem B2402077 : Blo 2133435 2402077 := bbase (se 3 (by rfl) ⟨450389, by rfl⟩ : syracuseStep 2402077 = 900779) (by norm_num)
theorem B3202769 : Blo 2133435 3202769 := bstep (se 2 (by rfl) ⟨1201038, by rfl⟩ : syracuseStep 3202769 = 2402077) B2402077
theorem B2135179 : Blo 2133435 2135179 := bstep (se 1 (by rfl) ⟨1601384, by rfl⟩ : syracuseStep 2135179 = 3202769) B3202769
theorem B7206245 : Blo 2133435 7206245 := bbase (se 4 (by rfl) ⟨675585, by rfl⟩ : syracuseStep 7206245 = 1351171) (by norm_num)
theorem B4804163 : Blo 2133435 4804163 := bstep (se 1 (by rfl) ⟨3603122, by rfl⟩ : syracuseStep 4804163 = 7206245) B7206245
theorem B3202775 : Blo 2133435 3202775 := bstep (se 1 (by rfl) ⟨2402081, by rfl⟩ : syracuseStep 3202775 = 4804163) B4804163
theorem B2135183 : Blo 2133435 2135183 := bstep (se 1 (by rfl) ⟨1601387, by rfl⟩ : syracuseStep 2135183 = 3202775) B3202775
theorem B3202781 : Blo 2133435 3202781 := bbase (se 3 (by rfl) ⟨600521, by rfl⟩ : syracuseStep 3202781 = 1201043) (by norm_num)
theorem B2135187 : Blo 2133435 2135187 := bstep (se 1 (by rfl) ⟨1601390, by rfl⟩ : syracuseStep 2135187 = 3202781) B3202781
theorem B4804181 : Blo 2133435 4804181 := bbase (se 8 (by rfl) ⟨28149, by rfl⟩ : syracuseStep 4804181 = 56299) (by norm_num)
theorem B3202787 : Blo 2133435 3202787 := bstep (se 1 (by rfl) ⟨2402090, by rfl⟩ : syracuseStep 3202787 = 4804181) B4804181
theorem B2135191 : Blo 2133435 2135191 := bstep (se 1 (by rfl) ⟨1601393, by rfl⟩ : syracuseStep 2135191 = 3202787) B3202787
theorem B4560229 : Blo 2133435 4560229 := bbase (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) (by norm_num)
theorem B6080305 : Blo 2133435 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B8107073 : Blo 2133435 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B5404715 : Blo 2133435 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B3603143 : Blo 2133435 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B2402095 : Blo 2133435 2402095 := bstep (se 1 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 2402095 = 3603143) B3603143
theorem B3202793 : Blo 2133435 3202793 := bstep (se 2 (by rfl) ⟨1201047, by rfl⟩ : syracuseStep 3202793 = 2402095) B2402095
theorem B2135195 : Blo 2133435 2135195 := bstep (se 1 (by rfl) ⟨1601396, by rfl⟩ : syracuseStep 2135195 = 3202793) B3202793
theorem B10260533 : Blo 2133435 10260533 := bbase (se 5 (by rfl) ⟨480962, by rfl⟩ : syracuseStep 10260533 = 961925) (by norm_num)
theorem B27361421 : Blo 2133435 27361421 := bstep (se 3 (by rfl) ⟨5130266, by rfl⟩ : syracuseStep 27361421 = 10260533) B10260533
theorem B18240947 : Blo 2133435 18240947 := bstep (se 1 (by rfl) ⟨13680710, by rfl⟩ : syracuseStep 18240947 = 27361421) B27361421
theorem B12160631 : Blo 2133435 12160631 := bstep (se 1 (by rfl) ⟨9120473, by rfl⟩ : syracuseStep 12160631 = 18240947) B18240947
theorem B8107087 : Blo 2133435 8107087 := bstep (se 1 (by rfl) ⟨6080315, by rfl⟩ : syracuseStep 8107087 = 12160631) B12160631
theorem B10809449 : Blo 2133435 10809449 := bstep (se 2 (by rfl) ⟨4053543, by rfl⟩ : syracuseStep 10809449 = 8107087) B8107087
theorem B7206299 : Blo 2133435 7206299 := bstep (se 1 (by rfl) ⟨5404724, by rfl⟩ : syracuseStep 7206299 = 10809449) B10809449
theorem B4804199 : Blo 2133435 4804199 := bstep (se 1 (by rfl) ⟨3603149, by rfl⟩ : syracuseStep 4804199 = 7206299) B7206299
theorem B3202799 : Blo 2133435 3202799 := bstep (se 1 (by rfl) ⟨2402099, by rfl⟩ : syracuseStep 3202799 = 4804199) B4804199
theorem B2135199 : Blo 2133435 2135199 := bstep (se 1 (by rfl) ⟨1601399, by rfl⟩ : syracuseStep 2135199 = 3202799) B3202799
theorem B3202805 : Blo 2133435 3202805 := bbase (se 5 (by rfl) ⟨150131, by rfl⟩ : syracuseStep 3202805 = 300263) (by norm_num)
theorem B2135203 : Blo 2133435 2135203 := bstep (se 1 (by rfl) ⟨1601402, by rfl⟩ : syracuseStep 2135203 = 3202805) B3202805
theorem B2311237 : Blo 2133435 2311237 := bbase (se 4 (by rfl) ⟨216678, by rfl⟩ : syracuseStep 2311237 = 433357) (by norm_num)
theorem B3081649 : Blo 2133435 3081649 := bstep (se 2 (by rfl) ⟨1155618, by rfl⟩ : syracuseStep 3081649 = 2311237) B2311237
theorem B4108865 : Blo 2133435 4108865 := bstep (se 2 (by rfl) ⟨1540824, by rfl⟩ : syracuseStep 4108865 = 3081649) B3081649
theorem B10956973 : Blo 2133435 10956973 := bstep (se 3 (by rfl) ⟨2054432, by rfl⟩ : syracuseStep 10956973 = 4108865) B4108865
theorem B14609297 : Blo 2133435 14609297 := bstep (se 2 (by rfl) ⟨5478486, by rfl⟩ : syracuseStep 14609297 = 10956973) B10956973
theorem B9739531 : Blo 2133435 9739531 := bstep (se 1 (by rfl) ⟨7304648, by rfl⟩ : syracuseStep 9739531 = 14609297) B14609297
theorem B12986041 : Blo 2133435 12986041 := bstep (se 2 (by rfl) ⟨4869765, by rfl⟩ : syracuseStep 12986041 = 9739531) B9739531
theorem B17314721 : Blo 2133435 17314721 := bstep (se 2 (by rfl) ⟨6493020, by rfl⟩ : syracuseStep 17314721 = 12986041) B12986041
theorem B11543147 : Blo 2133435 11543147 := bstep (se 1 (by rfl) ⟨8657360, by rfl⟩ : syracuseStep 11543147 = 17314721) B17314721
theorem B7695431 : Blo 2133435 7695431 := bstep (se 1 (by rfl) ⟨5771573, by rfl⟩ : syracuseStep 7695431 = 11543147) B11543147
theorem B5130287 : Blo 2133435 5130287 := bstep (se 1 (by rfl) ⟨3847715, by rfl⟩ : syracuseStep 5130287 = 7695431) B7695431
theorem B3420191 : Blo 2133435 3420191 := bstep (se 1 (by rfl) ⟨2565143, by rfl⟩ : syracuseStep 3420191 = 5130287) B5130287
theorem B9120509 : Blo 2133435 9120509 := bstep (se 3 (by rfl) ⟨1710095, by rfl⟩ : syracuseStep 9120509 = 3420191) B3420191
theorem B6080339 : Blo 2133435 6080339 := bstep (se 1 (by rfl) ⟨4560254, by rfl⟩ : syracuseStep 6080339 = 9120509) B9120509
theorem B4053559 : Blo 2133435 4053559 := bstep (se 1 (by rfl) ⟨3040169, by rfl⟩ : syracuseStep 4053559 = 6080339) B6080339
theorem B5404745 : Blo 2133435 5404745 := bstep (se 2 (by rfl) ⟨2026779, by rfl⟩ : syracuseStep 5404745 = 4053559) B4053559
theorem B3603163 : Blo 2133435 3603163 := bstep (se 1 (by rfl) ⟨2702372, by rfl⟩ : syracuseStep 3603163 = 5404745) B5404745
theorem B4804217 : Blo 2133435 4804217 := bstep (se 2 (by rfl) ⟨1801581, by rfl⟩ : syracuseStep 4804217 = 3603163) B3603163
theorem B3202811 : Blo 2133435 3202811 := bstep (se 1 (by rfl) ⟨2402108, by rfl⟩ : syracuseStep 3202811 = 4804217) B4804217
theorem B2135207 : Blo 2133435 2135207 := bstep (se 1 (by rfl) ⟨1601405, by rfl⟩ : syracuseStep 2135207 = 3202811) B3202811
theorem B2402113 : Blo 2133435 2402113 := bbase (se 2 (by rfl) ⟨900792, by rfl⟩ : syracuseStep 2402113 = 1801585) (by norm_num)
theorem B3202817 : Blo 2133435 3202817 := bstep (se 2 (by rfl) ⟨1201056, by rfl⟩ : syracuseStep 3202817 = 2402113) B2402113
theorem B2135211 : Blo 2133435 2135211 := bstep (se 1 (by rfl) ⟨1601408, by rfl⟩ : syracuseStep 2135211 = 3202817) B3202817
theorem B5404765 : Blo 2133435 5404765 := bbase (se 3 (by rfl) ⟨1013393, by rfl⟩ : syracuseStep 5404765 = 2026787) (by norm_num)
theorem B7206353 : Blo 2133435 7206353 := bstep (se 2 (by rfl) ⟨2702382, by rfl⟩ : syracuseStep 7206353 = 5404765) B5404765
theorem B4804235 : Blo 2133435 4804235 := bstep (se 1 (by rfl) ⟨3603176, by rfl⟩ : syracuseStep 4804235 = 7206353) B7206353
theorem B3202823 : Blo 2133435 3202823 := bstep (se 1 (by rfl) ⟨2402117, by rfl⟩ : syracuseStep 3202823 = 4804235) B4804235
theorem B2135215 : Blo 2133435 2135215 := bstep (se 1 (by rfl) ⟨1601411, by rfl⟩ : syracuseStep 2135215 = 3202823) B3202823
theorem B3202829 : Blo 2133435 3202829 := bbase (se 3 (by rfl) ⟨600530, by rfl⟩ : syracuseStep 3202829 = 1201061) (by norm_num)
theorem B2135219 : Blo 2133435 2135219 := bstep (se 1 (by rfl) ⟨1601414, by rfl⟩ : syracuseStep 2135219 = 3202829) B3202829
theorem B4804253 : Blo 2133435 4804253 := bbase (se 3 (by rfl) ⟨900797, by rfl⟩ : syracuseStep 4804253 = 1801595) (by norm_num)
theorem B3202835 : Blo 2133435 3202835 := bstep (se 1 (by rfl) ⟨2402126, by rfl⟩ : syracuseStep 3202835 = 4804253) B4804253
theorem B2135223 : Blo 2133435 2135223 := bstep (se 1 (by rfl) ⟨1601417, by rfl⟩ : syracuseStep 2135223 = 3202835) B3202835
theorem B3603197 : Blo 2133435 3603197 := bbase (se 3 (by rfl) ⟨675599, by rfl⟩ : syracuseStep 3603197 = 1351199) (by norm_num)
theorem B2402131 : Blo 2133435 2402131 := bstep (se 1 (by rfl) ⟨1801598, by rfl⟩ : syracuseStep 2402131 = 3603197) B3603197
theorem B3202841 : Blo 2133435 3202841 := bstep (se 2 (by rfl) ⟨1201065, by rfl⟩ : syracuseStep 3202841 = 2402131) B2402131
theorem B2135227 : Blo 2133435 2135227 := bstep (se 1 (by rfl) ⟨1601420, by rfl⟩ : syracuseStep 2135227 = 3202841) B3202841
theorem B3420229 : Blo 2133435 3420229 := bbase (se 4 (by rfl) ⟨320646, by rfl⟩ : syracuseStep 3420229 = 641293) (by norm_num)
theorem B4560305 : Blo 2133435 4560305 := bstep (se 2 (by rfl) ⟨1710114, by rfl⟩ : syracuseStep 4560305 = 3420229) B3420229
theorem B12160813 : Blo 2133435 12160813 := bstep (se 3 (by rfl) ⟨2280152, by rfl⟩ : syracuseStep 12160813 = 4560305) B4560305
theorem B16214417 : Blo 2133435 16214417 := bstep (se 2 (by rfl) ⟨6080406, by rfl⟩ : syracuseStep 16214417 = 12160813) B12160813
theorem B10809611 : Blo 2133435 10809611 := bstep (se 1 (by rfl) ⟨8107208, by rfl⟩ : syracuseStep 10809611 = 16214417) B16214417
theorem B7206407 : Blo 2133435 7206407 := bstep (se 1 (by rfl) ⟨5404805, by rfl⟩ : syracuseStep 7206407 = 10809611) B10809611
theorem B4804271 : Blo 2133435 4804271 := bstep (se 1 (by rfl) ⟨3603203, by rfl⟩ : syracuseStep 4804271 = 7206407) B7206407
theorem B3202847 : Blo 2133435 3202847 := bstep (se 1 (by rfl) ⟨2402135, by rfl⟩ : syracuseStep 3202847 = 4804271) B4804271
theorem B2135231 : Blo 2133435 2135231 := bstep (se 1 (by rfl) ⟨1601423, by rfl⟩ : syracuseStep 2135231 = 3202847) B3202847
theorem B3202853 : Blo 2133435 3202853 := bbase (se 4 (by rfl) ⟨300267, by rfl⟩ : syracuseStep 3202853 = 600535) (by norm_num)
theorem B2135235 : Blo 2133435 2135235 := bstep (se 1 (by rfl) ⟨1601426, by rfl⟩ : syracuseStep 2135235 = 3202853) B3202853
theorem B2702413 : Blo 2133435 2702413 := bbase (se 3 (by rfl) ⟨506702, by rfl⟩ : syracuseStep 2702413 = 1013405) (by norm_num)
theorem B3603217 : Blo 2133435 3603217 := bstep (se 2 (by rfl) ⟨1351206, by rfl⟩ : syracuseStep 3603217 = 2702413) B2702413
theorem B4804289 : Blo 2133435 4804289 := bstep (se 2 (by rfl) ⟨1801608, by rfl⟩ : syracuseStep 4804289 = 3603217) B3603217
theorem B3202859 : Blo 2133435 3202859 := bstep (se 1 (by rfl) ⟨2402144, by rfl⟩ : syracuseStep 3202859 = 4804289) B4804289
theorem B2135239 : Blo 2133435 2135239 := bstep (se 1 (by rfl) ⟨1601429, by rfl⟩ : syracuseStep 2135239 = 3202859) B3202859
theorem B2402149 : Blo 2133435 2402149 := bbase (se 4 (by rfl) ⟨225201, by rfl⟩ : syracuseStep 2402149 = 450403) (by norm_num)
theorem B3202865 : Blo 2133435 3202865 := bstep (se 2 (by rfl) ⟨1201074, by rfl⟩ : syracuseStep 3202865 = 2402149) B2402149
theorem B2135243 : Blo 2133435 2135243 := bstep (se 1 (by rfl) ⟨1601432, by rfl⟩ : syracuseStep 2135243 = 3202865) B3202865
theorem B6080453 : Blo 2133435 6080453 := bbase (se 4 (by rfl) ⟨570042, by rfl⟩ : syracuseStep 6080453 = 1140085) (by norm_num)
theorem B4053635 : Blo 2133435 4053635 := bstep (se 1 (by rfl) ⟨3040226, by rfl⟩ : syracuseStep 4053635 = 6080453) B6080453
theorem B2702423 : Blo 2133435 2702423 := bstep (se 1 (by rfl) ⟨2026817, by rfl⟩ : syracuseStep 2702423 = 4053635) B4053635
theorem B7206461 : Blo 2133435 7206461 := bstep (se 3 (by rfl) ⟨1351211, by rfl⟩ : syracuseStep 7206461 = 2702423) B2702423
theorem B4804307 : Blo 2133435 4804307 := bstep (se 1 (by rfl) ⟨3603230, by rfl⟩ : syracuseStep 4804307 = 7206461) B7206461
theorem B3202871 : Blo 2133435 3202871 := bstep (se 1 (by rfl) ⟨2402153, by rfl⟩ : syracuseStep 3202871 = 4804307) B4804307
theorem B2135247 : Blo 2133435 2135247 := bstep (se 1 (by rfl) ⟨1601435, by rfl⟩ : syracuseStep 2135247 = 3202871) B3202871
theorem B3202877 : Blo 2133435 3202877 := bbase (se 3 (by rfl) ⟨600539, by rfl⟩ : syracuseStep 3202877 = 1201079) (by norm_num)
theorem B2135251 : Blo 2133435 2135251 := bstep (se 1 (by rfl) ⟨1601438, by rfl⟩ : syracuseStep 2135251 = 3202877) B3202877
theorem B4804325 : Blo 2133435 4804325 := bbase (se 4 (by rfl) ⟨450405, by rfl⟩ : syracuseStep 4804325 = 900811) (by norm_num)
theorem B3202883 : Blo 2133435 3202883 := bstep (se 1 (by rfl) ⟨2402162, by rfl⟩ : syracuseStep 3202883 = 4804325) B4804325
theorem B2135255 : Blo 2133435 2135255 := bstep (se 1 (by rfl) ⟨1601441, by rfl⟩ : syracuseStep 2135255 = 3202883) B3202883
theorem B5404877 : Blo 2133435 5404877 := bbase (se 3 (by rfl) ⟨1013414, by rfl⟩ : syracuseStep 5404877 = 2026829) (by norm_num)
theorem B3603251 : Blo 2133435 3603251 := bstep (se 1 (by rfl) ⟨2702438, by rfl⟩ : syracuseStep 3603251 = 5404877) B5404877
theorem B2402167 : Blo 2133435 2402167 := bstep (se 1 (by rfl) ⟨1801625, by rfl⟩ : syracuseStep 2402167 = 3603251) B3603251
theorem B3202889 : Blo 2133435 3202889 := bstep (se 2 (by rfl) ⟨1201083, by rfl⟩ : syracuseStep 3202889 = 2402167) B2402167
theorem B2135259 : Blo 2133435 2135259 := bstep (se 1 (by rfl) ⟨1601444, by rfl⟩ : syracuseStep 2135259 = 3202889) B3202889
theorem B4622597 : Blo 2133435 4622597 := bbase (se 4 (by rfl) ⟨433368, by rfl⟩ : syracuseStep 4622597 = 866737) (by norm_num)
theorem B3081731 : Blo 2133435 3081731 := bstep (se 1 (by rfl) ⟨2311298, by rfl⟩ : syracuseStep 3081731 = 4622597) B4622597
theorem B8217949 : Blo 2133435 8217949 := bstep (se 3 (by rfl) ⟨1540865, by rfl⟩ : syracuseStep 8217949 = 3081731) B3081731
theorem B10957265 : Blo 2133435 10957265 := bstep (se 2 (by rfl) ⟨4108974, by rfl⟩ : syracuseStep 10957265 = 8217949) B8217949
theorem B7304843 : Blo 2133435 7304843 := bstep (se 1 (by rfl) ⟨5478632, by rfl⟩ : syracuseStep 7304843 = 10957265) B10957265
theorem B4869895 : Blo 2133435 4869895 := bstep (se 1 (by rfl) ⟨3652421, by rfl⟩ : syracuseStep 4869895 = 7304843) B7304843
theorem B6493193 : Blo 2133435 6493193 := bstep (se 2 (by rfl) ⟨2434947, by rfl⟩ : syracuseStep 6493193 = 4869895) B4869895
theorem B4328795 : Blo 2133435 4328795 := bstep (se 1 (by rfl) ⟨3246596, by rfl⟩ : syracuseStep 4328795 = 6493193) B6493193
theorem B2885863 : Blo 2133435 2885863 := bstep (se 1 (by rfl) ⟨2164397, by rfl⟩ : syracuseStep 2885863 = 4328795) B4328795
theorem B3847817 : Blo 2133435 3847817 := bstep (se 2 (by rfl) ⟨1442931, by rfl⟩ : syracuseStep 3847817 = 2885863) B2885863
theorem B2565211 : Blo 2133435 2565211 := bstep (se 1 (by rfl) ⟨1923908, by rfl⟩ : syracuseStep 2565211 = 3847817) B3847817
theorem B3420281 : Blo 2133435 3420281 := bstep (se 2 (by rfl) ⟨1282605, by rfl⟩ : syracuseStep 3420281 = 2565211) B2565211
theorem B2280187 : Blo 2133435 2280187 := bstep (se 1 (by rfl) ⟨1710140, by rfl⟩ : syracuseStep 2280187 = 3420281) B3420281
theorem B3040249 : Blo 2133435 3040249 := bstep (se 2 (by rfl) ⟨1140093, by rfl⟩ : syracuseStep 3040249 = 2280187) B2280187
theorem B4053665 : Blo 2133435 4053665 := bstep (se 2 (by rfl) ⟨1520124, by rfl⟩ : syracuseStep 4053665 = 3040249) B3040249
theorem B10809773 : Blo 2133435 10809773 := bstep (se 3 (by rfl) ⟨2026832, by rfl⟩ : syracuseStep 10809773 = 4053665) B4053665
theorem B7206515 : Blo 2133435 7206515 := bstep (se 1 (by rfl) ⟨5404886, by rfl⟩ : syracuseStep 7206515 = 10809773) B10809773
theorem B4804343 : Blo 2133435 4804343 := bstep (se 1 (by rfl) ⟨3603257, by rfl⟩ : syracuseStep 4804343 = 7206515) B7206515
theorem B3202895 : Blo 2133435 3202895 := bstep (se 1 (by rfl) ⟨2402171, by rfl⟩ : syracuseStep 3202895 = 4804343) B4804343
theorem B2135263 : Blo 2133435 2135263 := bstep (se 1 (by rfl) ⟨1601447, by rfl⟩ : syracuseStep 2135263 = 3202895) B3202895
theorem B3202901 : Blo 2133435 3202901 := bbase (se 9 (by rfl) ⟨9383, by rfl⟩ : syracuseStep 3202901 = 18767) (by norm_num)
theorem B2135267 : Blo 2133435 2135267 := bstep (se 1 (by rfl) ⟨1601450, by rfl⟩ : syracuseStep 2135267 = 3202901) B3202901
theorem B2164405 : Blo 2133435 2164405 := bbase (se 5 (by rfl) ⟨101456, by rfl⟩ : syracuseStep 2164405 = 202913) (by norm_num)
theorem B2885873 : Blo 2133435 2885873 := bstep (se 2 (by rfl) ⟨1082202, by rfl⟩ : syracuseStep 2885873 = 2164405) B2164405
theorem B7695661 : Blo 2133435 7695661 := bstep (se 3 (by rfl) ⟨1442936, by rfl⟩ : syracuseStep 7695661 = 2885873) B2885873
theorem B10260881 : Blo 2133435 10260881 := bstep (se 2 (by rfl) ⟨3847830, by rfl⟩ : syracuseStep 10260881 = 7695661) B7695661
theorem B6840587 : Blo 2133435 6840587 := bstep (se 1 (by rfl) ⟨5130440, by rfl⟩ : syracuseStep 6840587 = 10260881) B10260881
theorem B4560391 : Blo 2133435 4560391 := bstep (se 1 (by rfl) ⟨3420293, by rfl⟩ : syracuseStep 4560391 = 6840587) B6840587
theorem B6080521 : Blo 2133435 6080521 := bstep (se 2 (by rfl) ⟨2280195, by rfl⟩ : syracuseStep 6080521 = 4560391) B4560391
theorem B8107361 : Blo 2133435 8107361 := bstep (se 2 (by rfl) ⟨3040260, by rfl⟩ : syracuseStep 8107361 = 6080521) B6080521
theorem B5404907 : Blo 2133435 5404907 := bstep (se 1 (by rfl) ⟨4053680, by rfl⟩ : syracuseStep 5404907 = 8107361) B8107361
theorem B3603271 : Blo 2133435 3603271 := bstep (se 1 (by rfl) ⟨2702453, by rfl⟩ : syracuseStep 3603271 = 5404907) B5404907
theorem B4804361 : Blo 2133435 4804361 := bstep (se 2 (by rfl) ⟨1801635, by rfl⟩ : syracuseStep 4804361 = 3603271) B3603271
theorem B3202907 : Blo 2133435 3202907 := bstep (se 1 (by rfl) ⟨2402180, by rfl⟩ : syracuseStep 3202907 = 4804361) B4804361
theorem B2135271 : Blo 2133435 2135271 := bstep (se 1 (by rfl) ⟨1601453, by rfl⟩ : syracuseStep 2135271 = 3202907) B3202907
theorem B2402185 : Blo 2133435 2402185 := bbase (se 2 (by rfl) ⟨900819, by rfl⟩ : syracuseStep 2402185 = 1801639) (by norm_num)
theorem B3202913 : Blo 2133435 3202913 := bstep (se 2 (by rfl) ⟨1201092, by rfl⟩ : syracuseStep 3202913 = 2402185) B2402185
theorem B2135275 : Blo 2133435 2135275 := bstep (se 1 (by rfl) ⟨1601456, by rfl⟩ : syracuseStep 2135275 = 3202913) B3202913
theorem B25972949 : Blo 2133435 25972949 := bbase (se 7 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 25972949 = 608741) (by norm_num)
theorem B17315299 : Blo 2133435 17315299 := bstep (se 1 (by rfl) ⟨12986474, by rfl⟩ : syracuseStep 17315299 = 25972949) B25972949
theorem B92348261 : Blo 2133435 92348261 := bstep (se 4 (by rfl) ⟨8657649, by rfl⟩ : syracuseStep 92348261 = 17315299) B17315299
theorem B61565507 : Blo 2133435 61565507 := bstep (se 1 (by rfl) ⟨46174130, by rfl⟩ : syracuseStep 61565507 = 92348261) B92348261
theorem B41043671 : Blo 2133435 41043671 := bstep (se 1 (by rfl) ⟨30782753, by rfl⟩ : syracuseStep 41043671 = 61565507) B61565507
theorem B27362447 : Blo 2133435 27362447 := bstep (se 1 (by rfl) ⟨20521835, by rfl⟩ : syracuseStep 27362447 = 41043671) B41043671
theorem B18241631 : Blo 2133435 18241631 := bstep (se 1 (by rfl) ⟨13681223, by rfl⟩ : syracuseStep 18241631 = 27362447) B27362447
theorem B12161087 : Blo 2133435 12161087 := bstep (se 1 (by rfl) ⟨9120815, by rfl⟩ : syracuseStep 12161087 = 18241631) B18241631
theorem B8107391 : Blo 2133435 8107391 := bstep (se 1 (by rfl) ⟨6080543, by rfl⟩ : syracuseStep 8107391 = 12161087) B12161087
theorem B5404927 : Blo 2133435 5404927 := bstep (se 1 (by rfl) ⟨4053695, by rfl⟩ : syracuseStep 5404927 = 8107391) B8107391
theorem B7206569 : Blo 2133435 7206569 := bstep (se 2 (by rfl) ⟨2702463, by rfl⟩ : syracuseStep 7206569 = 5404927) B5404927
theorem B4804379 : Blo 2133435 4804379 := bstep (se 1 (by rfl) ⟨3603284, by rfl⟩ : syracuseStep 4804379 = 7206569) B7206569
theorem B3202919 : Blo 2133435 3202919 := bstep (se 1 (by rfl) ⟨2402189, by rfl⟩ : syracuseStep 3202919 = 4804379) B4804379
theorem B2135279 : Blo 2133435 2135279 := bstep (se 1 (by rfl) ⟨1601459, by rfl⟩ : syracuseStep 2135279 = 3202919) B3202919
theorem B3202925 : Blo 2133435 3202925 := bbase (se 3 (by rfl) ⟨600548, by rfl⟩ : syracuseStep 3202925 = 1201097) (by norm_num)
theorem B2135283 : Blo 2133435 2135283 := bstep (se 1 (by rfl) ⟨1601462, by rfl⟩ : syracuseStep 2135283 = 3202925) B3202925
theorem B4804397 : Blo 2133435 4804397 := bbase (se 3 (by rfl) ⟨900824, by rfl⟩ : syracuseStep 4804397 = 1801649) (by norm_num)
theorem B3202931 : Blo 2133435 3202931 := bstep (se 1 (by rfl) ⟨2402198, by rfl⟩ : syracuseStep 3202931 = 4804397) B4804397
theorem B2135287 : Blo 2133435 2135287 := bstep (se 1 (by rfl) ⟨1601465, by rfl⟩ : syracuseStep 2135287 = 3202931) B3202931
theorem B9120869 : Blo 2133435 9120869 := bbase (se 4 (by rfl) ⟨855081, by rfl⟩ : syracuseStep 9120869 = 1710163) (by norm_num)
theorem B6080579 : Blo 2133435 6080579 := bstep (se 1 (by rfl) ⟨4560434, by rfl⟩ : syracuseStep 6080579 = 9120869) B9120869
theorem B4053719 : Blo 2133435 4053719 := bstep (se 1 (by rfl) ⟨3040289, by rfl⟩ : syracuseStep 4053719 = 6080579) B6080579
theorem B2702479 : Blo 2133435 2702479 := bstep (se 1 (by rfl) ⟨2026859, by rfl⟩ : syracuseStep 2702479 = 4053719) B4053719
theorem B3603305 : Blo 2133435 3603305 := bstep (se 2 (by rfl) ⟨1351239, by rfl⟩ : syracuseStep 3603305 = 2702479) B2702479
theorem B2402203 : Blo 2133435 2402203 := bstep (se 1 (by rfl) ⟨1801652, by rfl⟩ : syracuseStep 2402203 = 3603305) B3603305
theorem B3202937 : Blo 2133435 3202937 := bstep (se 2 (by rfl) ⟨1201101, by rfl⟩ : syracuseStep 3202937 = 2402203) B2402203
theorem B2135291 : Blo 2133435 2135291 := bstep (se 1 (by rfl) ⟨1601468, by rfl⟩ : syracuseStep 2135291 = 3202937) B3202937
theorem B2164429 : Blo 2133435 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B2885905 : Blo 2133435 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B3847873 : Blo 2133435 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B5130497 : Blo 2133435 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B13681325 : Blo 2133435 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B36483533 : Blo 2133435 36483533 := bstep (se 3 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 36483533 = 13681325) B13681325
theorem B24322355 : Blo 2133435 24322355 := bstep (se 1 (by rfl) ⟨18241766, by rfl⟩ : syracuseStep 24322355 = 36483533) B36483533
theorem B16214903 : Blo 2133435 16214903 := bstep (se 1 (by rfl) ⟨12161177, by rfl⟩ : syracuseStep 16214903 = 24322355) B24322355
theorem B10809935 : Blo 2133435 10809935 := bstep (se 1 (by rfl) ⟨8107451, by rfl⟩ : syracuseStep 10809935 = 16214903) B16214903
theorem B7206623 : Blo 2133435 7206623 := bstep (se 1 (by rfl) ⟨5404967, by rfl⟩ : syracuseStep 7206623 = 10809935) B10809935
theorem B4804415 : Blo 2133435 4804415 := bstep (se 1 (by rfl) ⟨3603311, by rfl⟩ : syracuseStep 4804415 = 7206623) B7206623
theorem B3202943 : Blo 2133435 3202943 := bstep (se 1 (by rfl) ⟨2402207, by rfl⟩ : syracuseStep 3202943 = 4804415) B4804415
theorem B2135295 : Blo 2133435 2135295 := bstep (se 1 (by rfl) ⟨1601471, by rfl⟩ : syracuseStep 2135295 = 3202943) B3202943
theorem B3202949 : Blo 2133435 3202949 := bbase (se 4 (by rfl) ⟨300276, by rfl⟩ : syracuseStep 3202949 = 600553) (by norm_num)
theorem B2135299 : Blo 2133435 2135299 := bstep (se 1 (by rfl) ⟨1601474, by rfl⟩ : syracuseStep 2135299 = 3202949) B3202949
theorem B3603325 : Blo 2133435 3603325 := bbase (se 3 (by rfl) ⟨675623, by rfl⟩ : syracuseStep 3603325 = 1351247) (by norm_num)
theorem B4804433 : Blo 2133435 4804433 := bstep (se 2 (by rfl) ⟨1801662, by rfl⟩ : syracuseStep 4804433 = 3603325) B3603325
theorem B3202955 : Blo 2133435 3202955 := bstep (se 1 (by rfl) ⟨2402216, by rfl⟩ : syracuseStep 3202955 = 4804433) B4804433
theorem B2135303 : Blo 2133435 2135303 := bstep (se 1 (by rfl) ⟨1601477, by rfl⟩ : syracuseStep 2135303 = 3202955) B3202955
theorem B2402221 : Blo 2133435 2402221 := bbase (se 3 (by rfl) ⟨450416, by rfl⟩ : syracuseStep 2402221 = 900833) (by norm_num)
theorem B3202961 : Blo 2133435 3202961 := bstep (se 2 (by rfl) ⟨1201110, by rfl⟩ : syracuseStep 3202961 = 2402221) B2402221
theorem B2135307 : Blo 2133435 2135307 := bstep (se 1 (by rfl) ⟨1601480, by rfl⟩ : syracuseStep 2135307 = 3202961) B3202961
theorem B7206677 : Blo 2133435 7206677 := bbase (se 6 (by rfl) ⟨168906, by rfl⟩ : syracuseStep 7206677 = 337813) (by norm_num)
theorem B4804451 : Blo 2133435 4804451 := bstep (se 1 (by rfl) ⟨3603338, by rfl⟩ : syracuseStep 4804451 = 7206677) B7206677
theorem B3202967 : Blo 2133435 3202967 := bstep (se 1 (by rfl) ⟨2402225, by rfl⟩ : syracuseStep 3202967 = 4804451) B4804451
theorem B2135311 : Blo 2133435 2135311 := bstep (se 1 (by rfl) ⟨1601483, by rfl⟩ : syracuseStep 2135311 = 3202967) B3202967
theorem B3202973 : Blo 2133435 3202973 := bbase (se 3 (by rfl) ⟨600557, by rfl⟩ : syracuseStep 3202973 = 1201115) (by norm_num)
theorem B2135315 : Blo 2133435 2135315 := bstep (se 1 (by rfl) ⟨1601486, by rfl⟩ : syracuseStep 2135315 = 3202973) B3202973
theorem B4804469 : Blo 2133435 4804469 := bbase (se 5 (by rfl) ⟨225209, by rfl⟩ : syracuseStep 4804469 = 450419) (by norm_num)
theorem B3202979 : Blo 2133435 3202979 := bstep (se 1 (by rfl) ⟨2402234, by rfl⟩ : syracuseStep 3202979 = 4804469) B4804469
theorem B2135319 : Blo 2133435 2135319 := bstep (se 1 (by rfl) ⟨1601489, by rfl⟩ : syracuseStep 2135319 = 3202979) B3202979
theorem B20522261 : Blo 2133435 20522261 := bbase (se 6 (by rfl) ⟨480990, by rfl⟩ : syracuseStep 20522261 = 961981) (by norm_num)
theorem B13681507 : Blo 2133435 13681507 := bstep (se 1 (by rfl) ⟨10261130, by rfl⟩ : syracuseStep 13681507 = 20522261) B20522261
theorem B18242009 : Blo 2133435 18242009 := bstep (se 2 (by rfl) ⟨6840753, by rfl⟩ : syracuseStep 18242009 = 13681507) B13681507
theorem B12161339 : Blo 2133435 12161339 := bstep (se 1 (by rfl) ⟨9121004, by rfl⟩ : syracuseStep 12161339 = 18242009) B18242009
theorem B8107559 : Blo 2133435 8107559 := bstep (se 1 (by rfl) ⟨6080669, by rfl⟩ : syracuseStep 8107559 = 12161339) B12161339
theorem B5405039 : Blo 2133435 5405039 := bstep (se 1 (by rfl) ⟨4053779, by rfl⟩ : syracuseStep 5405039 = 8107559) B8107559
theorem B3603359 : Blo 2133435 3603359 := bstep (se 1 (by rfl) ⟨2702519, by rfl⟩ : syracuseStep 3603359 = 5405039) B5405039
theorem B2402239 : Blo 2133435 2402239 := bstep (se 1 (by rfl) ⟨1801679, by rfl⟩ : syracuseStep 2402239 = 3603359) B3603359
theorem B3202985 : Blo 2133435 3202985 := bstep (se 2 (by rfl) ⟨1201119, by rfl⟩ : syracuseStep 3202985 = 2402239) B2402239
theorem B2135323 : Blo 2133435 2135323 := bstep (se 1 (by rfl) ⟨1601492, by rfl⟩ : syracuseStep 2135323 = 3202985) B3202985
theorem B8107573 : Blo 2133435 8107573 := bbase (se 5 (by rfl) ⟨380042, by rfl⟩ : syracuseStep 8107573 = 760085) (by norm_num)
theorem B10810097 : Blo 2133435 10810097 := bstep (se 2 (by rfl) ⟨4053786, by rfl⟩ : syracuseStep 10810097 = 8107573) B8107573
theorem B7206731 : Blo 2133435 7206731 := bstep (se 1 (by rfl) ⟨5405048, by rfl⟩ : syracuseStep 7206731 = 10810097) B10810097
theorem B4804487 : Blo 2133435 4804487 := bstep (se 1 (by rfl) ⟨3603365, by rfl⟩ : syracuseStep 4804487 = 7206731) B7206731
theorem B3202991 : Blo 2133435 3202991 := bstep (se 1 (by rfl) ⟨2402243, by rfl⟩ : syracuseStep 3202991 = 4804487) B4804487
theorem B2135327 : Blo 2133435 2135327 := bstep (se 1 (by rfl) ⟨1601495, by rfl⟩ : syracuseStep 2135327 = 3202991) B3202991
theorem B3202997 : Blo 2133435 3202997 := bbase (se 5 (by rfl) ⟨150140, by rfl⟩ : syracuseStep 3202997 = 300281) (by norm_num)
theorem B2135331 : Blo 2133435 2135331 := bstep (se 1 (by rfl) ⟨1601498, by rfl⟩ : syracuseStep 2135331 = 3202997) B3202997
theorem B5405069 : Blo 2133435 5405069 := bbase (se 3 (by rfl) ⟨1013450, by rfl⟩ : syracuseStep 5405069 = 2026901) (by norm_num)
theorem B3603379 : Blo 2133435 3603379 := bstep (se 1 (by rfl) ⟨2702534, by rfl⟩ : syracuseStep 3603379 = 5405069) B5405069
theorem B4804505 : Blo 2133435 4804505 := bstep (se 2 (by rfl) ⟨1801689, by rfl⟩ : syracuseStep 4804505 = 3603379) B3603379
theorem B3203003 : Blo 2133435 3203003 := bstep (se 1 (by rfl) ⟨2402252, by rfl⟩ : syracuseStep 3203003 = 4804505) B4804505
theorem B2135335 : Blo 2133435 2135335 := bstep (se 1 (by rfl) ⟨1601501, by rfl⟩ : syracuseStep 2135335 = 3203003) B3203003
theorem B2402257 : Blo 2133435 2402257 := bbase (se 2 (by rfl) ⟨900846, by rfl⟩ : syracuseStep 2402257 = 1801693) (by norm_num)
theorem B3203009 : Blo 2133435 3203009 := bstep (se 2 (by rfl) ⟨1201128, by rfl⟩ : syracuseStep 3203009 = 2402257) B2402257
theorem B2135339 : Blo 2133435 2135339 := bstep (se 1 (by rfl) ⟨1601504, by rfl⟩ : syracuseStep 2135339 = 3203009) B3203009
theorem B4328957 : Blo 2133435 4328957 := bbase (se 3 (by rfl) ⟨811679, by rfl⟩ : syracuseStep 4328957 = 1623359) (by norm_num)
theorem B2885971 : Blo 2133435 2885971 := bstep (se 1 (by rfl) ⟨2164478, by rfl⟩ : syracuseStep 2885971 = 4328957) B4328957
theorem B3847961 : Blo 2133435 3847961 := bstep (se 2 (by rfl) ⟨1442985, by rfl⟩ : syracuseStep 3847961 = 2885971) B2885971
theorem B2565307 : Blo 2133435 2565307 := bstep (se 1 (by rfl) ⟨1923980, by rfl⟩ : syracuseStep 2565307 = 3847961) B3847961
theorem B3420409 : Blo 2133435 3420409 := bstep (se 2 (by rfl) ⟨1282653, by rfl⟩ : syracuseStep 3420409 = 2565307) B2565307
theorem B4560545 : Blo 2133435 4560545 := bstep (se 2 (by rfl) ⟨1710204, by rfl⟩ : syracuseStep 4560545 = 3420409) B3420409
theorem B3040363 : Blo 2133435 3040363 := bstep (se 1 (by rfl) ⟨2280272, by rfl⟩ : syracuseStep 3040363 = 4560545) B4560545
theorem B4053817 : Blo 2133435 4053817 := bstep (se 2 (by rfl) ⟨1520181, by rfl⟩ : syracuseStep 4053817 = 3040363) B3040363
theorem B5405089 : Blo 2133435 5405089 := bstep (se 2 (by rfl) ⟨2026908, by rfl⟩ : syracuseStep 5405089 = 4053817) B4053817
theorem B7206785 : Blo 2133435 7206785 := bstep (se 2 (by rfl) ⟨2702544, by rfl⟩ : syracuseStep 7206785 = 5405089) B5405089
theorem B4804523 : Blo 2133435 4804523 := bstep (se 1 (by rfl) ⟨3603392, by rfl⟩ : syracuseStep 4804523 = 7206785) B7206785
theorem B3203015 : Blo 2133435 3203015 := bstep (se 1 (by rfl) ⟨2402261, by rfl⟩ : syracuseStep 3203015 = 4804523) B4804523
theorem B2135343 : Blo 2133435 2135343 := bstep (se 1 (by rfl) ⟨1601507, by rfl⟩ : syracuseStep 2135343 = 3203015) B3203015
theorem B3203021 : Blo 2133435 3203021 := bbase (se 3 (by rfl) ⟨600566, by rfl⟩ : syracuseStep 3203021 = 1201133) (by norm_num)
theorem B2135347 : Blo 2133435 2135347 := bstep (se 1 (by rfl) ⟨1601510, by rfl⟩ : syracuseStep 2135347 = 3203021) B3203021
theorem B4804541 : Blo 2133435 4804541 := bbase (se 3 (by rfl) ⟨900851, by rfl⟩ : syracuseStep 4804541 = 1801703) (by norm_num)
theorem B3203027 : Blo 2133435 3203027 := bstep (se 1 (by rfl) ⟨2402270, by rfl⟩ : syracuseStep 3203027 = 4804541) B4804541
theorem B2135351 : Blo 2133435 2135351 := bstep (se 1 (by rfl) ⟨1601513, by rfl⟩ : syracuseStep 2135351 = 3203027) B3203027
theorem B3603413 : Blo 2133435 3603413 := bbase (se 7 (by rfl) ⟨42227, by rfl⟩ : syracuseStep 3603413 = 84455) (by norm_num)
theorem B2402275 : Blo 2133435 2402275 := bstep (se 1 (by rfl) ⟨1801706, by rfl⟩ : syracuseStep 2402275 = 3603413) B3603413
theorem B3203033 : Blo 2133435 3203033 := bstep (se 2 (by rfl) ⟨1201137, by rfl⟩ : syracuseStep 3203033 = 2402275) B2402275
theorem B2135355 : Blo 2133435 2135355 := bstep (se 1 (by rfl) ⟨1601516, by rfl⟩ : syracuseStep 2135355 = 3203033) B3203033
theorem B9121157 : Blo 2133435 9121157 := bbase (se 4 (by rfl) ⟨855108, by rfl⟩ : syracuseStep 9121157 = 1710217) (by norm_num)
theorem B6080771 : Blo 2133435 6080771 := bstep (se 1 (by rfl) ⟨4560578, by rfl⟩ : syracuseStep 6080771 = 9121157) B9121157
theorem B16215389 : Blo 2133435 16215389 := bstep (se 3 (by rfl) ⟨3040385, by rfl⟩ : syracuseStep 16215389 = 6080771) B6080771
theorem B10810259 : Blo 2133435 10810259 := bstep (se 1 (by rfl) ⟨8107694, by rfl⟩ : syracuseStep 10810259 = 16215389) B16215389
theorem B7206839 : Blo 2133435 7206839 := bstep (se 1 (by rfl) ⟨5405129, by rfl⟩ : syracuseStep 7206839 = 10810259) B10810259
theorem B4804559 : Blo 2133435 4804559 := bstep (se 1 (by rfl) ⟨3603419, by rfl⟩ : syracuseStep 4804559 = 7206839) B7206839
theorem B3203039 : Blo 2133435 3203039 := bstep (se 1 (by rfl) ⟨2402279, by rfl⟩ : syracuseStep 3203039 = 4804559) B4804559
theorem B2135359 : Blo 2133435 2135359 := bstep (se 1 (by rfl) ⟨1601519, by rfl⟩ : syracuseStep 2135359 = 3203039) B3203039
theorem B3203045 : Blo 2133435 3203045 := bbase (se 4 (by rfl) ⟨300285, by rfl⟩ : syracuseStep 3203045 = 600571) (by norm_num)
theorem B2135363 : Blo 2133435 2135363 := bstep (se 1 (by rfl) ⟨1601522, by rfl⟩ : syracuseStep 2135363 = 3203045) B3203045
theorem B2435065 : Blo 2133435 2435065 := bbase (se 2 (by rfl) ⟨913149, by rfl⟩ : syracuseStep 2435065 = 1826299) (by norm_num)
theorem B51948053 : Blo 2133435 51948053 := bstep (se 6 (by rfl) ⟨1217532, by rfl⟩ : syracuseStep 51948053 = 2435065) B2435065
theorem B34632035 : Blo 2133435 34632035 := bstep (se 1 (by rfl) ⟨25974026, by rfl⟩ : syracuseStep 34632035 = 51948053) B51948053
theorem B23088023 : Blo 2133435 23088023 := bstep (se 1 (by rfl) ⟨17316017, by rfl⟩ : syracuseStep 23088023 = 34632035) B34632035
theorem B15392015 : Blo 2133435 15392015 := bstep (se 1 (by rfl) ⟨11544011, by rfl⟩ : syracuseStep 15392015 = 23088023) B23088023
theorem B10261343 : Blo 2133435 10261343 := bstep (se 1 (by rfl) ⟨7696007, by rfl⟩ : syracuseStep 10261343 = 15392015) B15392015
theorem B6840895 : Blo 2133435 6840895 := bstep (se 1 (by rfl) ⟨5130671, by rfl⟩ : syracuseStep 6840895 = 10261343) B10261343
theorem B9121193 : Blo 2133435 9121193 := bstep (se 2 (by rfl) ⟨3420447, by rfl⟩ : syracuseStep 9121193 = 6840895) B6840895
theorem B6080795 : Blo 2133435 6080795 := bstep (se 1 (by rfl) ⟨4560596, by rfl⟩ : syracuseStep 6080795 = 9121193) B9121193
theorem B4053863 : Blo 2133435 4053863 := bstep (se 1 (by rfl) ⟨3040397, by rfl⟩ : syracuseStep 4053863 = 6080795) B6080795
theorem B2702575 : Blo 2133435 2702575 := bstep (se 1 (by rfl) ⟨2026931, by rfl⟩ : syracuseStep 2702575 = 4053863) B4053863
theorem B3603433 : Blo 2133435 3603433 := bstep (se 2 (by rfl) ⟨1351287, by rfl⟩ : syracuseStep 3603433 = 2702575) B2702575
theorem B4804577 : Blo 2133435 4804577 := bstep (se 2 (by rfl) ⟨1801716, by rfl⟩ : syracuseStep 4804577 = 3603433) B3603433
theorem B3203051 : Blo 2133435 3203051 := bstep (se 1 (by rfl) ⟨2402288, by rfl⟩ : syracuseStep 3203051 = 4804577) B4804577
theorem B2135367 : Blo 2133435 2135367 := bstep (se 1 (by rfl) ⟨1601525, by rfl⟩ : syracuseStep 2135367 = 3203051) B3203051
theorem B2402293 : Blo 2133435 2402293 := bbase (se 5 (by rfl) ⟨112607, by rfl⟩ : syracuseStep 2402293 = 225215) (by norm_num)
theorem B3203057 : Blo 2133435 3203057 := bstep (se 2 (by rfl) ⟨1201146, by rfl⟩ : syracuseStep 3203057 = 2402293) B2402293
theorem B2135371 : Blo 2133435 2135371 := bstep (se 1 (by rfl) ⟨1601528, by rfl⟩ : syracuseStep 2135371 = 3203057) B3203057
theorem B2702585 : Blo 2133435 2702585 := bbase (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) (by norm_num)
theorem B7206893 : Blo 2133435 7206893 := bstep (se 3 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 7206893 = 2702585) B2702585
theorem B4804595 : Blo 2133435 4804595 := bstep (se 1 (by rfl) ⟨3603446, by rfl⟩ : syracuseStep 4804595 = 7206893) B7206893
theorem B3203063 : Blo 2133435 3203063 := bstep (se 1 (by rfl) ⟨2402297, by rfl⟩ : syracuseStep 3203063 = 4804595) B4804595
theorem B2135375 : Blo 2133435 2135375 := bstep (se 1 (by rfl) ⟨1601531, by rfl⟩ : syracuseStep 2135375 = 3203063) B3203063
theorem B3203069 : Blo 2133435 3203069 := bbase (se 3 (by rfl) ⟨600575, by rfl⟩ : syracuseStep 3203069 = 1201151) (by norm_num)
theorem B2135379 : Blo 2133435 2135379 := bstep (se 1 (by rfl) ⟨1601534, by rfl⟩ : syracuseStep 2135379 = 3203069) B3203069
theorem B4804613 : Blo 2133435 4804613 := bbase (se 4 (by rfl) ⟨450432, by rfl⟩ : syracuseStep 4804613 = 900865) (by norm_num)
theorem B3203075 : Blo 2133435 3203075 := bstep (se 1 (by rfl) ⟨2402306, by rfl⟩ : syracuseStep 3203075 = 4804613) B4804613
theorem B2135383 : Blo 2133435 2135383 := bstep (se 1 (by rfl) ⟨1601537, by rfl⟩ : syracuseStep 2135383 = 3203075) B3203075
theorem B4053901 : Blo 2133435 4053901 := bbase (se 3 (by rfl) ⟨760106, by rfl⟩ : syracuseStep 4053901 = 1520213) (by norm_num)
theorem B5405201 : Blo 2133435 5405201 := bstep (se 2 (by rfl) ⟨2026950, by rfl⟩ : syracuseStep 5405201 = 4053901) B4053901
theorem B3603467 : Blo 2133435 3603467 := bstep (se 1 (by rfl) ⟨2702600, by rfl⟩ : syracuseStep 3603467 = 5405201) B5405201
theorem B2402311 : Blo 2133435 2402311 := bstep (se 1 (by rfl) ⟨1801733, by rfl⟩ : syracuseStep 2402311 = 3603467) B3603467
theorem B3203081 : Blo 2133435 3203081 := bstep (se 2 (by rfl) ⟨1201155, by rfl⟩ : syracuseStep 3203081 = 2402311) B2402311
theorem B2135387 : Blo 2133435 2135387 := bstep (se 1 (by rfl) ⟨1601540, by rfl⟩ : syracuseStep 2135387 = 3203081) B3203081
theorem B10810421 : Blo 2133435 10810421 := bbase (se 5 (by rfl) ⟨506738, by rfl⟩ : syracuseStep 10810421 = 1013477) (by norm_num)
theorem B7206947 : Blo 2133435 7206947 := bstep (se 1 (by rfl) ⟨5405210, by rfl⟩ : syracuseStep 7206947 = 10810421) B10810421
theorem B4804631 : Blo 2133435 4804631 := bstep (se 1 (by rfl) ⟨3603473, by rfl⟩ : syracuseStep 4804631 = 7206947) B7206947
theorem B3203087 : Blo 2133435 3203087 := bstep (se 1 (by rfl) ⟨2402315, by rfl⟩ : syracuseStep 3203087 = 4804631) B4804631
theorem B2135391 : Blo 2133435 2135391 := bstep (se 1 (by rfl) ⟨1601543, by rfl⟩ : syracuseStep 2135391 = 3203087) B3203087
theorem B3203093 : Blo 2133435 3203093 := bbase (se 6 (by rfl) ⟨75072, by rfl⟩ : syracuseStep 3203093 = 150145) (by norm_num)
theorem B2135395 : Blo 2133435 2135395 := bstep (se 1 (by rfl) ⟨1601546, by rfl⟩ : syracuseStep 2135395 = 3203093) B3203093
theorem B9740405 : Blo 2133435 9740405 := bbase (se 5 (by rfl) ⟨456581, by rfl⟩ : syracuseStep 9740405 = 913163) (by norm_num)
theorem B6493603 : Blo 2133435 6493603 := bstep (se 1 (by rfl) ⟨4870202, by rfl⟩ : syracuseStep 6493603 = 9740405) B9740405
theorem B8658137 : Blo 2133435 8658137 := bstep (se 2 (by rfl) ⟨3246801, by rfl⟩ : syracuseStep 8658137 = 6493603) B6493603
theorem B23088365 : Blo 2133435 23088365 := bstep (se 3 (by rfl) ⟨4329068, by rfl⟩ : syracuseStep 23088365 = 8658137) B8658137
theorem B15392243 : Blo 2133435 15392243 := bstep (se 1 (by rfl) ⟨11544182, by rfl⟩ : syracuseStep 15392243 = 23088365) B23088365
theorem B10261495 : Blo 2133435 10261495 := bstep (se 1 (by rfl) ⟨7696121, by rfl⟩ : syracuseStep 10261495 = 15392243) B15392243
theorem B13681993 : Blo 2133435 13681993 := bstep (se 2 (by rfl) ⟨5130747, by rfl⟩ : syracuseStep 13681993 = 10261495) B10261495
theorem B18242657 : Blo 2133435 18242657 := bstep (se 2 (by rfl) ⟨6840996, by rfl⟩ : syracuseStep 18242657 = 13681993) B13681993
theorem B12161771 : Blo 2133435 12161771 := bstep (se 1 (by rfl) ⟨9121328, by rfl⟩ : syracuseStep 12161771 = 18242657) B18242657
theorem B8107847 : Blo 2133435 8107847 := bstep (se 1 (by rfl) ⟨6080885, by rfl⟩ : syracuseStep 8107847 = 12161771) B12161771
theorem B5405231 : Blo 2133435 5405231 := bstep (se 1 (by rfl) ⟨4053923, by rfl⟩ : syracuseStep 5405231 = 8107847) B8107847
theorem B3603487 : Blo 2133435 3603487 := bstep (se 1 (by rfl) ⟨2702615, by rfl⟩ : syracuseStep 3603487 = 5405231) B5405231
theorem B4804649 : Blo 2133435 4804649 := bstep (se 2 (by rfl) ⟨1801743, by rfl⟩ : syracuseStep 4804649 = 3603487) B3603487
theorem B3203099 : Blo 2133435 3203099 := bstep (se 1 (by rfl) ⟨2402324, by rfl⟩ : syracuseStep 3203099 = 4804649) B4804649
theorem B2135399 : Blo 2133435 2135399 := bstep (se 1 (by rfl) ⟨1601549, by rfl⟩ : syracuseStep 2135399 = 3203099) B3203099
theorem B2402329 : Blo 2133435 2402329 := bbase (se 2 (by rfl) ⟨900873, by rfl⟩ : syracuseStep 2402329 = 1801747) (by norm_num)
theorem B3203105 : Blo 2133435 3203105 := bstep (se 2 (by rfl) ⟨1201164, by rfl⟩ : syracuseStep 3203105 = 2402329) B2402329
theorem B2135403 : Blo 2133435 2135403 := bstep (se 1 (by rfl) ⟨1601552, by rfl⟩ : syracuseStep 2135403 = 3203105) B3203105
theorem B8107877 : Blo 2133435 8107877 := bbase (se 4 (by rfl) ⟨760113, by rfl⟩ : syracuseStep 8107877 = 1520227) (by norm_num)
theorem B5405251 : Blo 2133435 5405251 := bstep (se 1 (by rfl) ⟨4053938, by rfl⟩ : syracuseStep 5405251 = 8107877) B8107877
theorem B7207001 : Blo 2133435 7207001 := bstep (se 2 (by rfl) ⟨2702625, by rfl⟩ : syracuseStep 7207001 = 5405251) B5405251
theorem B4804667 : Blo 2133435 4804667 := bstep (se 1 (by rfl) ⟨3603500, by rfl⟩ : syracuseStep 4804667 = 7207001) B7207001
theorem B3203111 : Blo 2133435 3203111 := bstep (se 1 (by rfl) ⟨2402333, by rfl⟩ : syracuseStep 3203111 = 4804667) B4804667
theorem B2135407 : Blo 2133435 2135407 := bstep (se 1 (by rfl) ⟨1601555, by rfl⟩ : syracuseStep 2135407 = 3203111) B3203111
theorem B3203117 : Blo 2133435 3203117 := bbase (se 3 (by rfl) ⟨600584, by rfl⟩ : syracuseStep 3203117 = 1201169) (by norm_num)
theorem B2135411 : Blo 2133435 2135411 := bstep (se 1 (by rfl) ⟨1601558, by rfl⟩ : syracuseStep 2135411 = 3203117) B3203117
theorem B4804685 : Blo 2133435 4804685 := bbase (se 3 (by rfl) ⟨900878, by rfl⟩ : syracuseStep 4804685 = 1801757) (by norm_num)
theorem B3203123 : Blo 2133435 3203123 := bstep (se 1 (by rfl) ⟨2402342, by rfl⟩ : syracuseStep 3203123 = 4804685) B4804685
theorem B2135415 : Blo 2133435 2135415 := bstep (se 1 (by rfl) ⟨1601561, by rfl⟩ : syracuseStep 2135415 = 3203123) B3203123
theorem B2702641 : Blo 2133435 2702641 := bbase (se 2 (by rfl) ⟨1013490, by rfl⟩ : syracuseStep 2702641 = 2026981) (by norm_num)
theorem B3603521 : Blo 2133435 3603521 := bstep (se 2 (by rfl) ⟨1351320, by rfl⟩ : syracuseStep 3603521 = 2702641) B2702641
theorem B2402347 : Blo 2133435 2402347 := bstep (se 1 (by rfl) ⟨1801760, by rfl⟩ : syracuseStep 2402347 = 3603521) B3603521
theorem B3203129 : Blo 2133435 3203129 := bstep (se 2 (by rfl) ⟨1201173, by rfl⟩ : syracuseStep 3203129 = 2402347) B2402347
theorem B2135419 : Blo 2133435 2135419 := bstep (se 1 (by rfl) ⟨1601564, by rfl⟩ : syracuseStep 2135419 = 3203129) B3203129
theorem B5130805 : Blo 2133435 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B6841073 : Blo 2133435 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B4560715 : Blo 2133435 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B24323813 : Blo 2133435 24323813 := bstep (se 4 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 24323813 = 4560715) B4560715
theorem B16215875 : Blo 2133435 16215875 := bstep (se 1 (by rfl) ⟨12161906, by rfl⟩ : syracuseStep 16215875 = 24323813) B24323813
theorem B10810583 : Blo 2133435 10810583 := bstep (se 1 (by rfl) ⟨8107937, by rfl⟩ : syracuseStep 10810583 = 16215875) B16215875
theorem B7207055 : Blo 2133435 7207055 := bstep (se 1 (by rfl) ⟨5405291, by rfl⟩ : syracuseStep 7207055 = 10810583) B10810583
theorem B4804703 : Blo 2133435 4804703 := bstep (se 1 (by rfl) ⟨3603527, by rfl⟩ : syracuseStep 4804703 = 7207055) B7207055
theorem B3203135 : Blo 2133435 3203135 := bstep (se 1 (by rfl) ⟨2402351, by rfl⟩ : syracuseStep 3203135 = 4804703) B4804703
theorem B2135423 : Blo 2133435 2135423 := bstep (se 1 (by rfl) ⟨1601567, by rfl⟩ : syracuseStep 2135423 = 3203135) B3203135
theorem B3203141 : Blo 2133435 3203141 := bbase (se 4 (by rfl) ⟨300294, by rfl⟩ : syracuseStep 3203141 = 600589) (by norm_num)
theorem B2135427 : Blo 2133435 2135427 := bstep (se 1 (by rfl) ⟨1601570, by rfl⟩ : syracuseStep 2135427 = 3203141) B3203141
theorem B3603541 : Blo 2133435 3603541 := bbase (se 8 (by rfl) ⟨21114, by rfl⟩ : syracuseStep 3603541 = 42229) (by norm_num)
theorem B4804721 : Blo 2133435 4804721 := bstep (se 2 (by rfl) ⟨1801770, by rfl⟩ : syracuseStep 4804721 = 3603541) B3603541
theorem B3203147 : Blo 2133435 3203147 := bstep (se 1 (by rfl) ⟨2402360, by rfl⟩ : syracuseStep 3203147 = 4804721) B4804721
theorem B2135431 : Blo 2133435 2135431 := bstep (se 1 (by rfl) ⟨1601573, by rfl⟩ : syracuseStep 2135431 = 3203147) B3203147
theorem B2402365 : Blo 2133435 2402365 := bbase (se 3 (by rfl) ⟨450443, by rfl⟩ : syracuseStep 2402365 = 900887) (by norm_num)
theorem B3203153 : Blo 2133435 3203153 := bstep (se 2 (by rfl) ⟨1201182, by rfl⟩ : syracuseStep 3203153 = 2402365) B2402365
theorem B2135435 : Blo 2133435 2135435 := bstep (se 1 (by rfl) ⟨1601576, by rfl⟩ : syracuseStep 2135435 = 3203153) B3203153
theorem C0 (j : ℕ) (h1 : 533358 ≤ j) (h2 : j ≤ 533858) : Blo 2133435 (4 * j + 3) := by
  interval_cases j
  · exact B2133435
  · exact B2133439
  · exact B2133443
  · exact B2133447
  · exact B2133451
  · exact B2133455
  · exact B2133459
  · exact B2133463
  · exact B2133467
  · exact B2133471
  · exact B2133475
  · exact B2133479
  · exact B2133483
  · exact B2133487
  · exact B2133491
  · exact B2133495
  · exact B2133499
  · exact B2133503
  · exact B2133507
  · exact B2133511
  · exact B2133515
  · exact B2133519
  · exact B2133523
  · exact B2133527
  · exact B2133531
  · exact B2133535
  · exact B2133539
  · exact B2133543
  · exact B2133547
  · exact B2133551
  · exact B2133555
  · exact B2133559
  · exact B2133563
  · exact B2133567
  · exact B2133571
  · exact B2133575
  · exact B2133579
  · exact B2133583
  · exact B2133587
  · exact B2133591
  · exact B2133595
  · exact B2133599
  · exact B2133603
  · exact B2133607
  · exact B2133611
  · exact B2133615
  · exact B2133619
  · exact B2133623
  · exact B2133627
  · exact B2133631
  · exact B2133635
  · exact B2133639
  · exact B2133643
  · exact B2133647
  · exact B2133651
  · exact B2133655
  · exact B2133659
  · exact B2133663
  · exact B2133667
  · exact B2133671
  · exact B2133675
  · exact B2133679
  · exact B2133683
  · exact B2133687
  · exact B2133691
  · exact B2133695
  · exact B2133699
  · exact B2133703
  · exact B2133707
  · exact B2133711
  · exact B2133715
  · exact B2133719
  · exact B2133723
  · exact B2133727
  · exact B2133731
  · exact B2133735
  · exact B2133739
  · exact B2133743
  · exact B2133747
  · exact B2133751
  · exact B2133755
  · exact B2133759
  · exact B2133763
  · exact B2133767
  · exact B2133771
  · exact B2133775
  · exact B2133779
  · exact B2133783
  · exact B2133787
  · exact B2133791
  · exact B2133795
  · exact B2133799
  · exact B2133803
  · exact B2133807
  · exact B2133811
  · exact B2133815
  · exact B2133819
  · exact B2133823
  · exact B2133827
  · exact B2133831
  · exact B2133835
  · exact B2133839
  · exact B2133843
  · exact B2133847
  · exact B2133851
  · exact B2133855
  · exact B2133859
  · exact B2133863
  · exact B2133867
  · exact B2133871
  · exact B2133875
  · exact B2133879
  · exact B2133883
  · exact B2133887
  · exact B2133891
  · exact B2133895
  · exact B2133899
  · exact B2133903
  · exact B2133907
  · exact B2133911
  · exact B2133915
  · exact B2133919
  · exact B2133923
  · exact B2133927
  · exact B2133931
  · exact B2133935
  · exact B2133939
  · exact B2133943
  · exact B2133947
  · exact B2133951
  · exact B2133955
  · exact B2133959
  · exact B2133963
  · exact B2133967
  · exact B2133971
  · exact B2133975
  · exact B2133979
  · exact B2133983
  · exact B2133987
  · exact B2133991
  · exact B2133995
  · exact B2133999
  · exact B2134003
  · exact B2134007
  · exact B2134011
  · exact B2134015
  · exact B2134019
  · exact B2134023
  · exact B2134027
  · exact B2134031
  · exact B2134035
  · exact B2134039
  · exact B2134043
  · exact B2134047
  · exact B2134051
  · exact B2134055
  · exact B2134059
  · exact B2134063
  · exact B2134067
  · exact B2134071
  · exact B2134075
  · exact B2134079
  · exact B2134083
  · exact B2134087
  · exact B2134091
  · exact B2134095
  · exact B2134099
  · exact B2134103
  · exact B2134107
  · exact B2134111
  · exact B2134115
  · exact B2134119
  · exact B2134123
  · exact B2134127
  · exact B2134131
  · exact B2134135
  · exact B2134139
  · exact B2134143
  · exact B2134147
  · exact B2134151
  · exact B2134155
  · exact B2134159
  · exact B2134163
  · exact B2134167
  · exact B2134171
  · exact B2134175
  · exact B2134179
  · exact B2134183
  · exact B2134187
  · exact B2134191
  · exact B2134195
  · exact B2134199
  · exact B2134203
  · exact B2134207
  · exact B2134211
  · exact B2134215
  · exact B2134219
  · exact B2134223
  · exact B2134227
  · exact B2134231
  · exact B2134235
  · exact B2134239
  · exact B2134243
  · exact B2134247
  · exact B2134251
  · exact B2134255
  · exact B2134259
  · exact B2134263
  · exact B2134267
  · exact B2134271
  · exact B2134275
  · exact B2134279
  · exact B2134283
  · exact B2134287
  · exact B2134291
  · exact B2134295
  · exact B2134299
  · exact B2134303
  · exact B2134307
  · exact B2134311
  · exact B2134315
  · exact B2134319
  · exact B2134323
  · exact B2134327
  · exact B2134331
  · exact B2134335
  · exact B2134339
  · exact B2134343
  · exact B2134347
  · exact B2134351
  · exact B2134355
  · exact B2134359
  · exact B2134363
  · exact B2134367
  · exact B2134371
  · exact B2134375
  · exact B2134379
  · exact B2134383
  · exact B2134387
  · exact B2134391
  · exact B2134395
  · exact B2134399
  · exact B2134403
  · exact B2134407
  · exact B2134411
  · exact B2134415
  · exact B2134419
  · exact B2134423
  · exact B2134427
  · exact B2134431
  · exact B2134435
  · exact B2134439
  · exact B2134443
  · exact B2134447
  · exact B2134451
  · exact B2134455
  · exact B2134459
  · exact B2134463
  · exact B2134467
  · exact B2134471
  · exact B2134475
  · exact B2134479
  · exact B2134483
  · exact B2134487
  · exact B2134491
  · exact B2134495
  · exact B2134499
  · exact B2134503
  · exact B2134507
  · exact B2134511
  · exact B2134515
  · exact B2134519
  · exact B2134523
  · exact B2134527
  · exact B2134531
  · exact B2134535
  · exact B2134539
  · exact B2134543
  · exact B2134547
  · exact B2134551
  · exact B2134555
  · exact B2134559
  · exact B2134563
  · exact B2134567
  · exact B2134571
  · exact B2134575
  · exact B2134579
  · exact B2134583
  · exact B2134587
  · exact B2134591
  · exact B2134595
  · exact B2134599
  · exact B2134603
  · exact B2134607
  · exact B2134611
  · exact B2134615
  · exact B2134619
  · exact B2134623
  · exact B2134627
  · exact B2134631
  · exact B2134635
  · exact B2134639
  · exact B2134643
  · exact B2134647
  · exact B2134651
  · exact B2134655
  · exact B2134659
  · exact B2134663
  · exact B2134667
  · exact B2134671
  · exact B2134675
  · exact B2134679
  · exact B2134683
  · exact B2134687
  · exact B2134691
  · exact B2134695
  · exact B2134699
  · exact B2134703
  · exact B2134707
  · exact B2134711
  · exact B2134715
  · exact B2134719
  · exact B2134723
  · exact B2134727
  · exact B2134731
  · exact B2134735
  · exact B2134739
  · exact B2134743
  · exact B2134747
  · exact B2134751
  · exact B2134755
  · exact B2134759
  · exact B2134763
  · exact B2134767
  · exact B2134771
  · exact B2134775
  · exact B2134779
  · exact B2134783
  · exact B2134787
  · exact B2134791
  · exact B2134795
  · exact B2134799
  · exact B2134803
  · exact B2134807
  · exact B2134811
  · exact B2134815
  · exact B2134819
  · exact B2134823
  · exact B2134827
  · exact B2134831
  · exact B2134835
  · exact B2134839
  · exact B2134843
  · exact B2134847
  · exact B2134851
  · exact B2134855
  · exact B2134859
  · exact B2134863
  · exact B2134867
  · exact B2134871
  · exact B2134875
  · exact B2134879
  · exact B2134883
  · exact B2134887
  · exact B2134891
  · exact B2134895
  · exact B2134899
  · exact B2134903
  · exact B2134907
  · exact B2134911
  · exact B2134915
  · exact B2134919
  · exact B2134923
  · exact B2134927
  · exact B2134931
  · exact B2134935
  · exact B2134939
  · exact B2134943
  · exact B2134947
  · exact B2134951
  · exact B2134955
  · exact B2134959
  · exact B2134963
  · exact B2134967
  · exact B2134971
  · exact B2134975
  · exact B2134979
  · exact B2134983
  · exact B2134987
  · exact B2134991
  · exact B2134995
  · exact B2134999
  · exact B2135003
  · exact B2135007
  · exact B2135011
  · exact B2135015
  · exact B2135019
  · exact B2135023
  · exact B2135027
  · exact B2135031
  · exact B2135035
  · exact B2135039
  · exact B2135043
  · exact B2135047
  · exact B2135051
  · exact B2135055
  · exact B2135059
  · exact B2135063
  · exact B2135067
  · exact B2135071
  · exact B2135075
  · exact B2135079
  · exact B2135083
  · exact B2135087
  · exact B2135091
  · exact B2135095
  · exact B2135099
  · exact B2135103
  · exact B2135107
  · exact B2135111
  · exact B2135115
  · exact B2135119
  · exact B2135123
  · exact B2135127
  · exact B2135131
  · exact B2135135
  · exact B2135139
  · exact B2135143
  · exact B2135147
  · exact B2135151
  · exact B2135155
  · exact B2135159
  · exact B2135163
  · exact B2135167
  · exact B2135171
  · exact B2135175
  · exact B2135179
  · exact B2135183
  · exact B2135187
  · exact B2135191
  · exact B2135195
  · exact B2135199
  · exact B2135203
  · exact B2135207
  · exact B2135211
  · exact B2135215
  · exact B2135219
  · exact B2135223
  · exact B2135227
  · exact B2135231
  · exact B2135235
  · exact B2135239
  · exact B2135243
  · exact B2135247
  · exact B2135251
  · exact B2135255
  · exact B2135259
  · exact B2135263
  · exact B2135267
  · exact B2135271
  · exact B2135275
  · exact B2135279
  · exact B2135283
  · exact B2135287
  · exact B2135291
  · exact B2135295
  · exact B2135299
  · exact B2135303
  · exact B2135307
  · exact B2135311
  · exact B2135315
  · exact B2135319
  · exact B2135323
  · exact B2135327
  · exact B2135331
  · exact B2135335
  · exact B2135339
  · exact B2135343
  · exact B2135347
  · exact B2135351
  · exact B2135355
  · exact B2135359
  · exact B2135363
  · exact B2135367
  · exact B2135371
  · exact B2135375
  · exact B2135379
  · exact B2135383
  · exact B2135387
  · exact B2135391
  · exact B2135395
  · exact B2135399
  · exact B2135403
  · exact B2135407
  · exact B2135411
  · exact B2135415
  · exact B2135419
  · exact B2135423
  · exact B2135427
  · exact B2135431
  · exact B2135435
theorem solution (m : ℕ) (hlo : 2133435 ≤ m) (hhi : m ≤ 2135435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 533358 ≤ j := by omega
    have hj2 : j ≤ 533858 := by omega
    have hb : Blo 2133435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
