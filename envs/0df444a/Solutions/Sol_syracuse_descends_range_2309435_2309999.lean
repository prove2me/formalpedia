-- Prove2me | solution 1 for syracuse_descends_range_2309435_2309999
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:50:09.95195+00:00
-- url     : https://prove2.me/submissions/ac71caf2-fceb-4e36-b66c-b5ab94ab1999

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

theorem B3897173 : Blo 2309435 3897173 := bbase (se 9 (by rfl) ⟨11417, by rfl⟩ : syracuseStep 3897173 = 22835) (by norm_num)
theorem B2598115 : Blo 2309435 2598115 := bstep (se 1 (by rfl) ⟨1948586, by rfl⟩ : syracuseStep 2598115 = 3897173) B3897173
theorem B3464153 : Blo 2309435 3464153 := bstep (se 2 (by rfl) ⟨1299057, by rfl⟩ : syracuseStep 3464153 = 2598115) B2598115
theorem B2309435 : Blo 2309435 2309435 := bstep (se 1 (by rfl) ⟨1732076, by rfl⟩ : syracuseStep 2309435 = 3464153) B3464153
theorem B2340949 : Blo 2309435 2340949 := bbase (se 8 (by rfl) ⟨13716, by rfl⟩ : syracuseStep 2340949 = 27433) (by norm_num)
theorem B3121265 : Blo 2309435 3121265 := bstep (se 2 (by rfl) ⟨1170474, by rfl⟩ : syracuseStep 3121265 = 2340949) B2340949
theorem B8323373 : Blo 2309435 8323373 := bstep (se 3 (by rfl) ⟨1560632, by rfl⟩ : syracuseStep 8323373 = 3121265) B3121265
theorem B5548915 : Blo 2309435 5548915 := bstep (se 1 (by rfl) ⟨4161686, by rfl⟩ : syracuseStep 5548915 = 8323373) B8323373
theorem B7398553 : Blo 2309435 7398553 := bstep (se 2 (by rfl) ⟨2774457, by rfl⟩ : syracuseStep 7398553 = 5548915) B5548915
theorem B9864737 : Blo 2309435 9864737 := bstep (se 2 (by rfl) ⟨3699276, by rfl⟩ : syracuseStep 9864737 = 7398553) B7398553
theorem B6576491 : Blo 2309435 6576491 := bstep (se 1 (by rfl) ⟨4932368, by rfl⟩ : syracuseStep 6576491 = 9864737) B9864737
theorem B17537309 : Blo 2309435 17537309 := bstep (se 3 (by rfl) ⟨3288245, by rfl⟩ : syracuseStep 17537309 = 6576491) B6576491
theorem B11691539 : Blo 2309435 11691539 := bstep (se 1 (by rfl) ⟨8768654, by rfl⟩ : syracuseStep 11691539 = 17537309) B17537309
theorem B7794359 : Blo 2309435 7794359 := bstep (se 1 (by rfl) ⟨5845769, by rfl⟩ : syracuseStep 7794359 = 11691539) B11691539
theorem B5196239 : Blo 2309435 5196239 := bstep (se 1 (by rfl) ⟨3897179, by rfl⟩ : syracuseStep 5196239 = 7794359) B7794359
theorem B3464159 : Blo 2309435 3464159 := bstep (se 1 (by rfl) ⟨2598119, by rfl⟩ : syracuseStep 3464159 = 5196239) B5196239
theorem B2309439 : Blo 2309435 2309439 := bstep (se 1 (by rfl) ⟨1732079, by rfl⟩ : syracuseStep 2309439 = 3464159) B3464159
theorem B3464165 : Blo 2309435 3464165 := bbase (se 4 (by rfl) ⟨324765, by rfl⟩ : syracuseStep 3464165 = 649531) (by norm_num)
theorem B2309443 : Blo 2309435 2309443 := bstep (se 1 (by rfl) ⟨1732082, by rfl⟩ : syracuseStep 2309443 = 3464165) B3464165
theorem B9864773 : Blo 2309435 9864773 := bbase (se 4 (by rfl) ⟨924822, by rfl⟩ : syracuseStep 9864773 = 1849645) (by norm_num)
theorem B6576515 : Blo 2309435 6576515 := bstep (se 1 (by rfl) ⟨4932386, by rfl⟩ : syracuseStep 6576515 = 9864773) B9864773
theorem B4384343 : Blo 2309435 4384343 := bstep (se 1 (by rfl) ⟨3288257, by rfl⟩ : syracuseStep 4384343 = 6576515) B6576515
theorem B2922895 : Blo 2309435 2922895 := bstep (se 1 (by rfl) ⟨2192171, by rfl⟩ : syracuseStep 2922895 = 4384343) B4384343
theorem B3897193 : Blo 2309435 3897193 := bstep (se 2 (by rfl) ⟨1461447, by rfl⟩ : syracuseStep 3897193 = 2922895) B2922895
theorem B5196257 : Blo 2309435 5196257 := bstep (se 2 (by rfl) ⟨1948596, by rfl⟩ : syracuseStep 5196257 = 3897193) B3897193
theorem B3464171 : Blo 2309435 3464171 := bstep (se 1 (by rfl) ⟨2598128, by rfl⟩ : syracuseStep 3464171 = 5196257) B5196257
theorem B2309447 : Blo 2309435 2309447 := bstep (se 1 (by rfl) ⟨1732085, by rfl⟩ : syracuseStep 2309447 = 3464171) B3464171
theorem B2598133 : Blo 2309435 2598133 := bbase (se 5 (by rfl) ⟨121787, by rfl⟩ : syracuseStep 2598133 = 243575) (by norm_num)
theorem B3464177 : Blo 2309435 3464177 := bstep (se 2 (by rfl) ⟨1299066, by rfl⟩ : syracuseStep 3464177 = 2598133) B2598133
theorem B2309451 : Blo 2309435 2309451 := bstep (se 1 (by rfl) ⟨1732088, by rfl⟩ : syracuseStep 2309451 = 3464177) B3464177
theorem B2922905 : Blo 2309435 2922905 := bbase (se 2 (by rfl) ⟨1096089, by rfl⟩ : syracuseStep 2922905 = 2192179) (by norm_num)
theorem B7794413 : Blo 2309435 7794413 := bstep (se 3 (by rfl) ⟨1461452, by rfl⟩ : syracuseStep 7794413 = 2922905) B2922905
theorem B5196275 : Blo 2309435 5196275 := bstep (se 1 (by rfl) ⟨3897206, by rfl⟩ : syracuseStep 5196275 = 7794413) B7794413
theorem B3464183 : Blo 2309435 3464183 := bstep (se 1 (by rfl) ⟨2598137, by rfl⟩ : syracuseStep 3464183 = 5196275) B5196275
theorem B2309455 : Blo 2309435 2309455 := bstep (se 1 (by rfl) ⟨1732091, by rfl⟩ : syracuseStep 2309455 = 3464183) B3464183
theorem B3464189 : Blo 2309435 3464189 := bbase (se 3 (by rfl) ⟨649535, by rfl⟩ : syracuseStep 3464189 = 1299071) (by norm_num)
theorem B2309459 : Blo 2309435 2309459 := bstep (se 1 (by rfl) ⟨1732094, by rfl⟩ : syracuseStep 2309459 = 3464189) B3464189
theorem B5196293 : Blo 2309435 5196293 := bbase (se 4 (by rfl) ⟨487152, by rfl⟩ : syracuseStep 5196293 = 974305) (by norm_num)
theorem B3464195 : Blo 2309435 3464195 := bstep (se 1 (by rfl) ⟨2598146, by rfl⟩ : syracuseStep 3464195 = 5196293) B5196293
theorem B2309463 : Blo 2309435 2309463 := bstep (se 1 (by rfl) ⟨1732097, by rfl⟩ : syracuseStep 2309463 = 3464195) B3464195
theorem B4384381 : Blo 2309435 4384381 := bbase (se 3 (by rfl) ⟨822071, by rfl⟩ : syracuseStep 4384381 = 1644143) (by norm_num)
theorem B5845841 : Blo 2309435 5845841 := bstep (se 2 (by rfl) ⟨2192190, by rfl⟩ : syracuseStep 5845841 = 4384381) B4384381
theorem B3897227 : Blo 2309435 3897227 := bstep (se 1 (by rfl) ⟨2922920, by rfl⟩ : syracuseStep 3897227 = 5845841) B5845841
theorem B2598151 : Blo 2309435 2598151 := bstep (se 1 (by rfl) ⟨1948613, by rfl⟩ : syracuseStep 2598151 = 3897227) B3897227
theorem B3464201 : Blo 2309435 3464201 := bstep (se 2 (by rfl) ⟨1299075, by rfl⟩ : syracuseStep 3464201 = 2598151) B2598151
theorem B2309467 : Blo 2309435 2309467 := bstep (se 1 (by rfl) ⟨1732100, by rfl⟩ : syracuseStep 2309467 = 3464201) B3464201
theorem B11691701 : Blo 2309435 11691701 := bbase (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) (by norm_num)
theorem B7794467 : Blo 2309435 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B5196311 : Blo 2309435 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B3464207 : Blo 2309435 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B2309471 : Blo 2309435 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B3464213 : Blo 2309435 3464213 := bbase (se 6 (by rfl) ⟨81192, by rfl⟩ : syracuseStep 3464213 = 162385) (by norm_num)
theorem B2309475 : Blo 2309435 2309475 := bstep (se 1 (by rfl) ⟨1732106, by rfl⟩ : syracuseStep 2309475 = 3464213) B3464213
theorem B24025909 : Blo 2309435 24025909 := bbase (se 5 (by rfl) ⟨1126214, by rfl⟩ : syracuseStep 24025909 = 2252429) (by norm_num)
theorem B32034545 : Blo 2309435 32034545 := bstep (se 2 (by rfl) ⟨12012954, by rfl⟩ : syracuseStep 32034545 = 24025909) B24025909
theorem B21356363 : Blo 2309435 21356363 := bstep (se 1 (by rfl) ⟨16017272, by rfl⟩ : syracuseStep 21356363 = 32034545) B32034545
theorem B14237575 : Blo 2309435 14237575 := bstep (se 1 (by rfl) ⟨10678181, by rfl⟩ : syracuseStep 14237575 = 21356363) B21356363
theorem B75933733 : Blo 2309435 75933733 := bstep (se 4 (by rfl) ⟨7118787, by rfl⟩ : syracuseStep 75933733 = 14237575) B14237575
theorem B101244977 : Blo 2309435 101244977 := bstep (se 2 (by rfl) ⟨37966866, by rfl⟩ : syracuseStep 101244977 = 75933733) B75933733
theorem B67496651 : Blo 2309435 67496651 := bstep (se 1 (by rfl) ⟨50622488, by rfl⟩ : syracuseStep 67496651 = 101244977) B101244977
theorem B44997767 : Blo 2309435 44997767 := bstep (se 1 (by rfl) ⟨33748325, by rfl⟩ : syracuseStep 44997767 = 67496651) B67496651
theorem B29998511 : Blo 2309435 29998511 := bstep (se 1 (by rfl) ⟨22498883, by rfl⟩ : syracuseStep 29998511 = 44997767) B44997767
theorem B19999007 : Blo 2309435 19999007 := bstep (se 1 (by rfl) ⟨14999255, by rfl⟩ : syracuseStep 19999007 = 29998511) B29998511
theorem B13332671 : Blo 2309435 13332671 := bstep (se 1 (by rfl) ⟨9999503, by rfl⟩ : syracuseStep 13332671 = 19999007) B19999007
theorem B8888447 : Blo 2309435 8888447 := bstep (se 1 (by rfl) ⟨6666335, by rfl⟩ : syracuseStep 8888447 = 13332671) B13332671
theorem B5925631 : Blo 2309435 5925631 := bstep (se 1 (by rfl) ⟨4444223, by rfl⟩ : syracuseStep 5925631 = 8888447) B8888447
theorem B7900841 : Blo 2309435 7900841 := bstep (se 2 (by rfl) ⟨2962815, by rfl⟩ : syracuseStep 7900841 = 5925631) B5925631
theorem B5267227 : Blo 2309435 5267227 := bstep (se 1 (by rfl) ⟨3950420, by rfl⟩ : syracuseStep 5267227 = 7900841) B7900841
theorem B7022969 : Blo 2309435 7022969 := bstep (se 2 (by rfl) ⟨2633613, by rfl⟩ : syracuseStep 7022969 = 5267227) B5267227
theorem B4681979 : Blo 2309435 4681979 := bstep (se 1 (by rfl) ⟨3511484, by rfl⟩ : syracuseStep 4681979 = 7022969) B7022969
theorem B3121319 : Blo 2309435 3121319 := bstep (se 1 (by rfl) ⟨2340989, by rfl⟩ : syracuseStep 3121319 = 4681979) B4681979
theorem B8323517 : Blo 2309435 8323517 := bstep (se 3 (by rfl) ⟨1560659, by rfl⟩ : syracuseStep 8323517 = 3121319) B3121319
theorem B22196045 : Blo 2309435 22196045 := bstep (se 3 (by rfl) ⟨4161758, by rfl⟩ : syracuseStep 22196045 = 8323517) B8323517
theorem B14797363 : Blo 2309435 14797363 := bstep (se 1 (by rfl) ⟨11098022, by rfl⟩ : syracuseStep 14797363 = 22196045) B22196045
theorem B19729817 : Blo 2309435 19729817 := bstep (se 2 (by rfl) ⟨7398681, by rfl⟩ : syracuseStep 19729817 = 14797363) B14797363
theorem B13153211 : Blo 2309435 13153211 := bstep (se 1 (by rfl) ⟨9864908, by rfl⟩ : syracuseStep 13153211 = 19729817) B19729817
theorem B8768807 : Blo 2309435 8768807 := bstep (se 1 (by rfl) ⟨6576605, by rfl⟩ : syracuseStep 8768807 = 13153211) B13153211
theorem B5845871 : Blo 2309435 5845871 := bstep (se 1 (by rfl) ⟨4384403, by rfl⟩ : syracuseStep 5845871 = 8768807) B8768807
theorem B3897247 : Blo 2309435 3897247 := bstep (se 1 (by rfl) ⟨2922935, by rfl⟩ : syracuseStep 3897247 = 5845871) B5845871
theorem B5196329 : Blo 2309435 5196329 := bstep (se 2 (by rfl) ⟨1948623, by rfl⟩ : syracuseStep 5196329 = 3897247) B3897247
theorem B3464219 : Blo 2309435 3464219 := bstep (se 1 (by rfl) ⟨2598164, by rfl⟩ : syracuseStep 3464219 = 5196329) B5196329
theorem B2309479 : Blo 2309435 2309479 := bstep (se 1 (by rfl) ⟨1732109, by rfl⟩ : syracuseStep 2309479 = 3464219) B3464219
theorem B2598169 : Blo 2309435 2598169 := bbase (se 2 (by rfl) ⟨974313, by rfl⟩ : syracuseStep 2598169 = 1948627) (by norm_num)
theorem B3464225 : Blo 2309435 3464225 := bstep (se 2 (by rfl) ⟨1299084, by rfl⟩ : syracuseStep 3464225 = 2598169) B2598169
theorem B2309483 : Blo 2309435 2309483 := bstep (se 1 (by rfl) ⟨1732112, by rfl⟩ : syracuseStep 2309483 = 3464225) B3464225
theorem B8768837 : Blo 2309435 8768837 := bbase (se 4 (by rfl) ⟨822078, by rfl⟩ : syracuseStep 8768837 = 1644157) (by norm_num)
theorem B5845891 : Blo 2309435 5845891 := bstep (se 1 (by rfl) ⟨4384418, by rfl⟩ : syracuseStep 5845891 = 8768837) B8768837
theorem B7794521 : Blo 2309435 7794521 := bstep (se 2 (by rfl) ⟨2922945, by rfl⟩ : syracuseStep 7794521 = 5845891) B5845891
theorem B5196347 : Blo 2309435 5196347 := bstep (se 1 (by rfl) ⟨3897260, by rfl⟩ : syracuseStep 5196347 = 7794521) B7794521
theorem B3464231 : Blo 2309435 3464231 := bstep (se 1 (by rfl) ⟨2598173, by rfl⟩ : syracuseStep 3464231 = 5196347) B5196347
theorem B2309487 : Blo 2309435 2309487 := bstep (se 1 (by rfl) ⟨1732115, by rfl⟩ : syracuseStep 2309487 = 3464231) B3464231
theorem B3464237 : Blo 2309435 3464237 := bbase (se 3 (by rfl) ⟨649544, by rfl⟩ : syracuseStep 3464237 = 1299089) (by norm_num)
theorem B2309491 : Blo 2309435 2309491 := bstep (se 1 (by rfl) ⟨1732118, by rfl⟩ : syracuseStep 2309491 = 3464237) B3464237
theorem B5196365 : Blo 2309435 5196365 := bbase (se 3 (by rfl) ⟨974318, by rfl⟩ : syracuseStep 5196365 = 1948637) (by norm_num)
theorem B3464243 : Blo 2309435 3464243 := bstep (se 1 (by rfl) ⟨2598182, by rfl⟩ : syracuseStep 3464243 = 5196365) B5196365
theorem B2309495 : Blo 2309435 2309495 := bstep (se 1 (by rfl) ⟨1732121, by rfl⟩ : syracuseStep 2309495 = 3464243) B3464243
theorem B2922961 : Blo 2309435 2922961 := bbase (se 2 (by rfl) ⟨1096110, by rfl⟩ : syracuseStep 2922961 = 2192221) (by norm_num)
theorem B3897281 : Blo 2309435 3897281 := bstep (se 2 (by rfl) ⟨1461480, by rfl⟩ : syracuseStep 3897281 = 2922961) B2922961
theorem B2598187 : Blo 2309435 2598187 := bstep (se 1 (by rfl) ⟨1948640, by rfl⟩ : syracuseStep 2598187 = 3897281) B3897281
theorem B3464249 : Blo 2309435 3464249 := bstep (se 2 (by rfl) ⟨1299093, by rfl⟩ : syracuseStep 3464249 = 2598187) B2598187
theorem B2309499 : Blo 2309435 2309499 := bstep (se 1 (by rfl) ⟨1732124, by rfl⟩ : syracuseStep 2309499 = 3464249) B3464249
theorem B5549069 : Blo 2309435 5549069 := bbase (se 3 (by rfl) ⟨1040450, by rfl⟩ : syracuseStep 5549069 = 2080901) (by norm_num)
theorem B3699379 : Blo 2309435 3699379 := bstep (se 1 (by rfl) ⟨2774534, by rfl⟩ : syracuseStep 3699379 = 5549069) B5549069
theorem B4932505 : Blo 2309435 4932505 := bstep (se 2 (by rfl) ⟨1849689, by rfl⟩ : syracuseStep 4932505 = 3699379) B3699379
theorem B26306693 : Blo 2309435 26306693 := bstep (se 4 (by rfl) ⟨2466252, by rfl⟩ : syracuseStep 26306693 = 4932505) B4932505
theorem B17537795 : Blo 2309435 17537795 := bstep (se 1 (by rfl) ⟨13153346, by rfl⟩ : syracuseStep 17537795 = 26306693) B26306693
theorem B11691863 : Blo 2309435 11691863 := bstep (se 1 (by rfl) ⟨8768897, by rfl⟩ : syracuseStep 11691863 = 17537795) B17537795
theorem B7794575 : Blo 2309435 7794575 := bstep (se 1 (by rfl) ⟨5845931, by rfl⟩ : syracuseStep 7794575 = 11691863) B11691863
theorem B5196383 : Blo 2309435 5196383 := bstep (se 1 (by rfl) ⟨3897287, by rfl⟩ : syracuseStep 5196383 = 7794575) B7794575
theorem B3464255 : Blo 2309435 3464255 := bstep (se 1 (by rfl) ⟨2598191, by rfl⟩ : syracuseStep 3464255 = 5196383) B5196383
theorem B2309503 : Blo 2309435 2309503 := bstep (se 1 (by rfl) ⟨1732127, by rfl⟩ : syracuseStep 2309503 = 3464255) B3464255
theorem B3464261 : Blo 2309435 3464261 := bbase (se 4 (by rfl) ⟨324774, by rfl⟩ : syracuseStep 3464261 = 649549) (by norm_num)
theorem B2309507 : Blo 2309435 2309507 := bstep (se 1 (by rfl) ⟨1732130, by rfl⟩ : syracuseStep 2309507 = 3464261) B3464261
theorem B3897301 : Blo 2309435 3897301 := bbase (se 7 (by rfl) ⟨45671, by rfl⟩ : syracuseStep 3897301 = 91343) (by norm_num)
theorem B5196401 : Blo 2309435 5196401 := bstep (se 2 (by rfl) ⟨1948650, by rfl⟩ : syracuseStep 5196401 = 3897301) B3897301
theorem B3464267 : Blo 2309435 3464267 := bstep (se 1 (by rfl) ⟨2598200, by rfl⟩ : syracuseStep 3464267 = 5196401) B5196401
theorem B2309511 : Blo 2309435 2309511 := bstep (se 1 (by rfl) ⟨1732133, by rfl⟩ : syracuseStep 2309511 = 3464267) B3464267
theorem B2598205 : Blo 2309435 2598205 := bbase (se 3 (by rfl) ⟨487163, by rfl⟩ : syracuseStep 2598205 = 974327) (by norm_num)
theorem B3464273 : Blo 2309435 3464273 := bstep (se 2 (by rfl) ⟨1299102, by rfl⟩ : syracuseStep 3464273 = 2598205) B2598205
theorem B2309515 : Blo 2309435 2309515 := bstep (se 1 (by rfl) ⟨1732136, by rfl⟩ : syracuseStep 2309515 = 3464273) B3464273
theorem B7794629 : Blo 2309435 7794629 := bbase (se 4 (by rfl) ⟨730746, by rfl⟩ : syracuseStep 7794629 = 1461493) (by norm_num)
theorem B5196419 : Blo 2309435 5196419 := bstep (se 1 (by rfl) ⟨3897314, by rfl⟩ : syracuseStep 5196419 = 7794629) B7794629
theorem B3464279 : Blo 2309435 3464279 := bstep (se 1 (by rfl) ⟨2598209, by rfl⟩ : syracuseStep 3464279 = 5196419) B5196419
theorem B2309519 : Blo 2309435 2309519 := bstep (se 1 (by rfl) ⟨1732139, by rfl⟩ : syracuseStep 2309519 = 3464279) B3464279
theorem B3464285 : Blo 2309435 3464285 := bbase (se 3 (by rfl) ⟨649553, by rfl⟩ : syracuseStep 3464285 = 1299107) (by norm_num)
theorem B2309523 : Blo 2309435 2309523 := bstep (se 1 (by rfl) ⟨1732142, by rfl⟩ : syracuseStep 2309523 = 3464285) B3464285
theorem B5196437 : Blo 2309435 5196437 := bbase (se 6 (by rfl) ⟨121791, by rfl⟩ : syracuseStep 5196437 = 243583) (by norm_num)
theorem B3464291 : Blo 2309435 3464291 := bstep (se 1 (by rfl) ⟨2598218, by rfl⟩ : syracuseStep 3464291 = 5196437) B5196437
theorem B2309527 : Blo 2309435 2309527 := bstep (se 1 (by rfl) ⟨1732145, by rfl⟩ : syracuseStep 2309527 = 3464291) B3464291
theorem B2774569 : Blo 2309435 2774569 := bbase (se 2 (by rfl) ⟨1040463, by rfl⟩ : syracuseStep 2774569 = 2080927) (by norm_num)
theorem B3699425 : Blo 2309435 3699425 := bstep (se 2 (by rfl) ⟨1387284, by rfl⟩ : syracuseStep 3699425 = 2774569) B2774569
theorem B2466283 : Blo 2309435 2466283 := bstep (se 1 (by rfl) ⟨1849712, by rfl⟩ : syracuseStep 2466283 = 3699425) B3699425
theorem B3288377 : Blo 2309435 3288377 := bstep (se 2 (by rfl) ⟨1233141, by rfl⟩ : syracuseStep 3288377 = 2466283) B2466283
theorem B8769005 : Blo 2309435 8769005 := bstep (se 3 (by rfl) ⟨1644188, by rfl⟩ : syracuseStep 8769005 = 3288377) B3288377
theorem B5846003 : Blo 2309435 5846003 := bstep (se 1 (by rfl) ⟨4384502, by rfl⟩ : syracuseStep 5846003 = 8769005) B8769005
theorem B3897335 : Blo 2309435 3897335 := bstep (se 1 (by rfl) ⟨2923001, by rfl⟩ : syracuseStep 3897335 = 5846003) B5846003
theorem B2598223 : Blo 2309435 2598223 := bstep (se 1 (by rfl) ⟨1948667, by rfl⟩ : syracuseStep 2598223 = 3897335) B3897335
theorem B3464297 : Blo 2309435 3464297 := bstep (se 2 (by rfl) ⟨1299111, by rfl⟩ : syracuseStep 3464297 = 2598223) B2598223
theorem B2309531 : Blo 2309435 2309531 := bstep (se 1 (by rfl) ⟨1732148, by rfl⟩ : syracuseStep 2309531 = 3464297) B3464297
theorem B6242789 : Blo 2309435 6242789 := bbase (se 4 (by rfl) ⟨585261, by rfl⟩ : syracuseStep 6242789 = 1170523) (by norm_num)
theorem B16647437 : Blo 2309435 16647437 := bstep (se 3 (by rfl) ⟨3121394, by rfl⟩ : syracuseStep 16647437 = 6242789) B6242789
theorem B11098291 : Blo 2309435 11098291 := bstep (se 1 (by rfl) ⟨8323718, by rfl⟩ : syracuseStep 11098291 = 16647437) B16647437
theorem B14797721 : Blo 2309435 14797721 := bstep (se 2 (by rfl) ⟨5549145, by rfl⟩ : syracuseStep 14797721 = 11098291) B11098291
theorem B9865147 : Blo 2309435 9865147 := bstep (se 1 (by rfl) ⟨7398860, by rfl⟩ : syracuseStep 9865147 = 14797721) B14797721
theorem B13153529 : Blo 2309435 13153529 := bstep (se 2 (by rfl) ⟨4932573, by rfl⟩ : syracuseStep 13153529 = 9865147) B9865147
theorem B8769019 : Blo 2309435 8769019 := bstep (se 1 (by rfl) ⟨6576764, by rfl⟩ : syracuseStep 8769019 = 13153529) B13153529
theorem B11692025 : Blo 2309435 11692025 := bstep (se 2 (by rfl) ⟨4384509, by rfl⟩ : syracuseStep 11692025 = 8769019) B8769019
theorem B7794683 : Blo 2309435 7794683 := bstep (se 1 (by rfl) ⟨5846012, by rfl⟩ : syracuseStep 7794683 = 11692025) B11692025
theorem B5196455 : Blo 2309435 5196455 := bstep (se 1 (by rfl) ⟨3897341, by rfl⟩ : syracuseStep 5196455 = 7794683) B7794683
theorem B3464303 : Blo 2309435 3464303 := bstep (se 1 (by rfl) ⟨2598227, by rfl⟩ : syracuseStep 3464303 = 5196455) B5196455
theorem B2309535 : Blo 2309435 2309535 := bstep (se 1 (by rfl) ⟨1732151, by rfl⟩ : syracuseStep 2309535 = 3464303) B3464303
theorem B3464309 : Blo 2309435 3464309 := bbase (se 5 (by rfl) ⟨162389, by rfl⟩ : syracuseStep 3464309 = 324779) (by norm_num)
theorem B2309539 : Blo 2309435 2309539 := bstep (se 1 (by rfl) ⟨1732154, by rfl⟩ : syracuseStep 2309539 = 3464309) B3464309
theorem B4384525 : Blo 2309435 4384525 := bbase (se 3 (by rfl) ⟨822098, by rfl⟩ : syracuseStep 4384525 = 1644197) (by norm_num)
theorem B5846033 : Blo 2309435 5846033 := bstep (se 2 (by rfl) ⟨2192262, by rfl⟩ : syracuseStep 5846033 = 4384525) B4384525
theorem B3897355 : Blo 2309435 3897355 := bstep (se 1 (by rfl) ⟨2923016, by rfl⟩ : syracuseStep 3897355 = 5846033) B5846033
theorem B5196473 : Blo 2309435 5196473 := bstep (se 2 (by rfl) ⟨1948677, by rfl⟩ : syracuseStep 5196473 = 3897355) B3897355
theorem B3464315 : Blo 2309435 3464315 := bstep (se 1 (by rfl) ⟨2598236, by rfl⟩ : syracuseStep 3464315 = 5196473) B5196473
theorem B2309543 : Blo 2309435 2309543 := bstep (se 1 (by rfl) ⟨1732157, by rfl⟩ : syracuseStep 2309543 = 3464315) B3464315
theorem B2598241 : Blo 2309435 2598241 := bbase (se 2 (by rfl) ⟨974340, by rfl⟩ : syracuseStep 2598241 = 1948681) (by norm_num)
theorem B3464321 : Blo 2309435 3464321 := bstep (se 2 (by rfl) ⟨1299120, by rfl⟩ : syracuseStep 3464321 = 2598241) B2598241
theorem B2309547 : Blo 2309435 2309547 := bstep (se 1 (by rfl) ⟨1732160, by rfl⟩ : syracuseStep 2309547 = 3464321) B3464321
theorem B5846053 : Blo 2309435 5846053 := bbase (se 4 (by rfl) ⟨548067, by rfl⟩ : syracuseStep 5846053 = 1096135) (by norm_num)
theorem B7794737 : Blo 2309435 7794737 := bstep (se 2 (by rfl) ⟨2923026, by rfl⟩ : syracuseStep 7794737 = 5846053) B5846053
theorem B5196491 : Blo 2309435 5196491 := bstep (se 1 (by rfl) ⟨3897368, by rfl⟩ : syracuseStep 5196491 = 7794737) B7794737
theorem B3464327 : Blo 2309435 3464327 := bstep (se 1 (by rfl) ⟨2598245, by rfl⟩ : syracuseStep 3464327 = 5196491) B5196491
theorem B2309551 : Blo 2309435 2309551 := bstep (se 1 (by rfl) ⟨1732163, by rfl⟩ : syracuseStep 2309551 = 3464327) B3464327
theorem B3464333 : Blo 2309435 3464333 := bbase (se 3 (by rfl) ⟨649562, by rfl⟩ : syracuseStep 3464333 = 1299125) (by norm_num)
theorem B2309555 : Blo 2309435 2309555 := bstep (se 1 (by rfl) ⟨1732166, by rfl⟩ : syracuseStep 2309555 = 3464333) B3464333
theorem B5196509 : Blo 2309435 5196509 := bbase (se 3 (by rfl) ⟨974345, by rfl⟩ : syracuseStep 5196509 = 1948691) (by norm_num)
theorem B3464339 : Blo 2309435 3464339 := bstep (se 1 (by rfl) ⟨2598254, by rfl⟩ : syracuseStep 3464339 = 5196509) B5196509
theorem B2309559 : Blo 2309435 2309559 := bstep (se 1 (by rfl) ⟨1732169, by rfl⟩ : syracuseStep 2309559 = 3464339) B3464339
theorem B3897389 : Blo 2309435 3897389 := bbase (se 3 (by rfl) ⟨730760, by rfl⟩ : syracuseStep 3897389 = 1461521) (by norm_num)
theorem B2598259 : Blo 2309435 2598259 := bstep (se 1 (by rfl) ⟨1948694, by rfl⟩ : syracuseStep 2598259 = 3897389) B3897389
theorem B3464345 : Blo 2309435 3464345 := bstep (se 2 (by rfl) ⟨1299129, by rfl⟩ : syracuseStep 3464345 = 2598259) B2598259
theorem B2309563 : Blo 2309435 2309563 := bstep (se 1 (by rfl) ⟨1732172, by rfl⟩ : syracuseStep 2309563 = 3464345) B3464345
theorem B10534853 : Blo 2309435 10534853 := bbase (se 4 (by rfl) ⟨987642, by rfl⟩ : syracuseStep 10534853 = 1975285) (by norm_num)
theorem B7023235 : Blo 2309435 7023235 := bstep (se 1 (by rfl) ⟨5267426, by rfl⟩ : syracuseStep 7023235 = 10534853) B10534853
theorem B9364313 : Blo 2309435 9364313 := bstep (se 2 (by rfl) ⟨3511617, by rfl⟩ : syracuseStep 9364313 = 7023235) B7023235
theorem B6242875 : Blo 2309435 6242875 := bstep (se 1 (by rfl) ⟨4682156, by rfl⟩ : syracuseStep 6242875 = 9364313) B9364313
theorem B33295333 : Blo 2309435 33295333 := bstep (se 4 (by rfl) ⟨3121437, by rfl⟩ : syracuseStep 33295333 = 6242875) B6242875
theorem B44393777 : Blo 2309435 44393777 := bstep (se 2 (by rfl) ⟨16647666, by rfl⟩ : syracuseStep 44393777 = 33295333) B33295333
theorem B29595851 : Blo 2309435 29595851 := bstep (se 1 (by rfl) ⟨22196888, by rfl⟩ : syracuseStep 29595851 = 44393777) B44393777
theorem B19730567 : Blo 2309435 19730567 := bstep (se 1 (by rfl) ⟨14797925, by rfl⟩ : syracuseStep 19730567 = 29595851) B29595851
theorem B13153711 : Blo 2309435 13153711 := bstep (se 1 (by rfl) ⟨9865283, by rfl⟩ : syracuseStep 13153711 = 19730567) B19730567
theorem B17538281 : Blo 2309435 17538281 := bstep (se 2 (by rfl) ⟨6576855, by rfl⟩ : syracuseStep 17538281 = 13153711) B13153711
theorem B11692187 : Blo 2309435 11692187 := bstep (se 1 (by rfl) ⟨8769140, by rfl⟩ : syracuseStep 11692187 = 17538281) B17538281
theorem B7794791 : Blo 2309435 7794791 := bstep (se 1 (by rfl) ⟨5846093, by rfl⟩ : syracuseStep 7794791 = 11692187) B11692187
theorem B5196527 : Blo 2309435 5196527 := bstep (se 1 (by rfl) ⟨3897395, by rfl⟩ : syracuseStep 5196527 = 7794791) B7794791
theorem B3464351 : Blo 2309435 3464351 := bstep (se 1 (by rfl) ⟨2598263, by rfl⟩ : syracuseStep 3464351 = 5196527) B5196527
theorem B2309567 : Blo 2309435 2309567 := bstep (se 1 (by rfl) ⟨1732175, by rfl⟩ : syracuseStep 2309567 = 3464351) B3464351
theorem B3464357 : Blo 2309435 3464357 := bbase (se 4 (by rfl) ⟨324783, by rfl⟩ : syracuseStep 3464357 = 649567) (by norm_num)
theorem B2309571 : Blo 2309435 2309571 := bstep (se 1 (by rfl) ⟨1732178, by rfl⟩ : syracuseStep 2309571 = 3464357) B3464357
theorem B2923057 : Blo 2309435 2923057 := bbase (se 2 (by rfl) ⟨1096146, by rfl⟩ : syracuseStep 2923057 = 2192293) (by norm_num)
theorem B3897409 : Blo 2309435 3897409 := bstep (se 2 (by rfl) ⟨1461528, by rfl⟩ : syracuseStep 3897409 = 2923057) B2923057
theorem B5196545 : Blo 2309435 5196545 := bstep (se 2 (by rfl) ⟨1948704, by rfl⟩ : syracuseStep 5196545 = 3897409) B3897409
theorem B3464363 : Blo 2309435 3464363 := bstep (se 1 (by rfl) ⟨2598272, by rfl⟩ : syracuseStep 3464363 = 5196545) B5196545
theorem B2309575 : Blo 2309435 2309575 := bstep (se 1 (by rfl) ⟨1732181, by rfl⟩ : syracuseStep 2309575 = 3464363) B3464363
theorem B2598277 : Blo 2309435 2598277 := bbase (se 4 (by rfl) ⟨243588, by rfl⟩ : syracuseStep 2598277 = 487177) (by norm_num)
theorem B3464369 : Blo 2309435 3464369 := bstep (se 2 (by rfl) ⟨1299138, by rfl⟩ : syracuseStep 3464369 = 2598277) B2598277
theorem B2309579 : Blo 2309435 2309579 := bstep (se 1 (by rfl) ⟨1732184, by rfl⟩ : syracuseStep 2309579 = 3464369) B3464369
theorem B4932677 : Blo 2309435 4932677 := bbase (se 4 (by rfl) ⟨462438, by rfl⟩ : syracuseStep 4932677 = 924877) (by norm_num)
theorem B3288451 : Blo 2309435 3288451 := bstep (se 1 (by rfl) ⟨2466338, by rfl⟩ : syracuseStep 3288451 = 4932677) B4932677
theorem B4384601 : Blo 2309435 4384601 := bstep (se 2 (by rfl) ⟨1644225, by rfl⟩ : syracuseStep 4384601 = 3288451) B3288451
theorem B2923067 : Blo 2309435 2923067 := bstep (se 1 (by rfl) ⟨2192300, by rfl⟩ : syracuseStep 2923067 = 4384601) B4384601
theorem B7794845 : Blo 2309435 7794845 := bstep (se 3 (by rfl) ⟨1461533, by rfl⟩ : syracuseStep 7794845 = 2923067) B2923067
theorem B5196563 : Blo 2309435 5196563 := bstep (se 1 (by rfl) ⟨3897422, by rfl⟩ : syracuseStep 5196563 = 7794845) B7794845
theorem B3464375 : Blo 2309435 3464375 := bstep (se 1 (by rfl) ⟨2598281, by rfl⟩ : syracuseStep 3464375 = 5196563) B5196563
theorem B2309583 : Blo 2309435 2309583 := bstep (se 1 (by rfl) ⟨1732187, by rfl⟩ : syracuseStep 2309583 = 3464375) B3464375
theorem B3464381 : Blo 2309435 3464381 := bbase (se 3 (by rfl) ⟨649571, by rfl⟩ : syracuseStep 3464381 = 1299143) (by norm_num)
theorem B2309587 : Blo 2309435 2309587 := bstep (se 1 (by rfl) ⟨1732190, by rfl⟩ : syracuseStep 2309587 = 3464381) B3464381
theorem B5196581 : Blo 2309435 5196581 := bbase (se 4 (by rfl) ⟨487179, by rfl⟩ : syracuseStep 5196581 = 974359) (by norm_num)
theorem B3464387 : Blo 2309435 3464387 := bstep (se 1 (by rfl) ⟨2598290, by rfl⟩ : syracuseStep 3464387 = 5196581) B5196581
theorem B2309591 : Blo 2309435 2309591 := bstep (se 1 (by rfl) ⟨1732193, by rfl⟩ : syracuseStep 2309591 = 3464387) B3464387
theorem B5846165 : Blo 2309435 5846165 := bbase (se 6 (by rfl) ⟨137019, by rfl⟩ : syracuseStep 5846165 = 274039) (by norm_num)
theorem B3897443 : Blo 2309435 3897443 := bstep (se 1 (by rfl) ⟨2923082, by rfl⟩ : syracuseStep 3897443 = 5846165) B5846165
theorem B2598295 : Blo 2309435 2598295 := bstep (se 1 (by rfl) ⟨1948721, by rfl⟩ : syracuseStep 2598295 = 3897443) B3897443
theorem B3464393 : Blo 2309435 3464393 := bstep (se 2 (by rfl) ⟨1299147, by rfl⟩ : syracuseStep 3464393 = 2598295) B2598295
theorem B2309595 : Blo 2309435 2309595 := bstep (se 1 (by rfl) ⟨1732196, by rfl⟩ : syracuseStep 2309595 = 3464393) B3464393
theorem B3699533 : Blo 2309435 3699533 := bbase (se 3 (by rfl) ⟨693662, by rfl⟩ : syracuseStep 3699533 = 1387325) (by norm_num)
theorem B9865421 : Blo 2309435 9865421 := bstep (se 3 (by rfl) ⟨1849766, by rfl⟩ : syracuseStep 9865421 = 3699533) B3699533
theorem B6576947 : Blo 2309435 6576947 := bstep (se 1 (by rfl) ⟨4932710, by rfl⟩ : syracuseStep 6576947 = 9865421) B9865421
theorem B4384631 : Blo 2309435 4384631 := bstep (se 1 (by rfl) ⟨3288473, by rfl⟩ : syracuseStep 4384631 = 6576947) B6576947
theorem B11692349 : Blo 2309435 11692349 := bstep (se 3 (by rfl) ⟨2192315, by rfl⟩ : syracuseStep 11692349 = 4384631) B4384631
theorem B7794899 : Blo 2309435 7794899 := bstep (se 1 (by rfl) ⟨5846174, by rfl⟩ : syracuseStep 7794899 = 11692349) B11692349
theorem B5196599 : Blo 2309435 5196599 := bstep (se 1 (by rfl) ⟨3897449, by rfl⟩ : syracuseStep 5196599 = 7794899) B7794899
theorem B3464399 : Blo 2309435 3464399 := bstep (se 1 (by rfl) ⟨2598299, by rfl⟩ : syracuseStep 3464399 = 5196599) B5196599
theorem B2309599 : Blo 2309435 2309599 := bstep (se 1 (by rfl) ⟨1732199, by rfl⟩ : syracuseStep 2309599 = 3464399) B3464399
theorem B3464405 : Blo 2309435 3464405 := bbase (se 7 (by rfl) ⟨40598, by rfl⟩ : syracuseStep 3464405 = 81197) (by norm_num)
theorem B2309603 : Blo 2309435 2309603 := bstep (se 1 (by rfl) ⟨1732202, by rfl⟩ : syracuseStep 2309603 = 3464405) B3464405
theorem B3288485 : Blo 2309435 3288485 := bbase (se 4 (by rfl) ⟨308295, by rfl⟩ : syracuseStep 3288485 = 616591) (by norm_num)
theorem B8769293 : Blo 2309435 8769293 := bstep (se 3 (by rfl) ⟨1644242, by rfl⟩ : syracuseStep 8769293 = 3288485) B3288485
theorem B5846195 : Blo 2309435 5846195 := bstep (se 1 (by rfl) ⟨4384646, by rfl⟩ : syracuseStep 5846195 = 8769293) B8769293
theorem B3897463 : Blo 2309435 3897463 := bstep (se 1 (by rfl) ⟨2923097, by rfl⟩ : syracuseStep 3897463 = 5846195) B5846195
theorem B5196617 : Blo 2309435 5196617 := bstep (se 2 (by rfl) ⟨1948731, by rfl⟩ : syracuseStep 5196617 = 3897463) B3897463
theorem B3464411 : Blo 2309435 3464411 := bstep (se 1 (by rfl) ⟨2598308, by rfl⟩ : syracuseStep 3464411 = 5196617) B5196617
theorem B2309607 : Blo 2309435 2309607 := bstep (se 1 (by rfl) ⟨1732205, by rfl⟩ : syracuseStep 2309607 = 3464411) B3464411
theorem B2598313 : Blo 2309435 2598313 := bbase (se 2 (by rfl) ⟨974367, by rfl⟩ : syracuseStep 2598313 = 1948735) (by norm_num)
theorem B3464417 : Blo 2309435 3464417 := bstep (se 2 (by rfl) ⟨1299156, by rfl⟩ : syracuseStep 3464417 = 2598313) B2598313
theorem B2309611 : Blo 2309435 2309611 := bstep (se 1 (by rfl) ⟨1732208, by rfl⟩ : syracuseStep 2309611 = 3464417) B3464417
theorem B2774669 : Blo 2309435 2774669 := bbase (se 3 (by rfl) ⟨520250, by rfl⟩ : syracuseStep 2774669 = 1040501) (by norm_num)
theorem B7399117 : Blo 2309435 7399117 := bstep (se 3 (by rfl) ⟨1387334, by rfl⟩ : syracuseStep 7399117 = 2774669) B2774669
theorem B9865489 : Blo 2309435 9865489 := bstep (se 2 (by rfl) ⟨3699558, by rfl⟩ : syracuseStep 9865489 = 7399117) B7399117
theorem B13153985 : Blo 2309435 13153985 := bstep (se 2 (by rfl) ⟨4932744, by rfl⟩ : syracuseStep 13153985 = 9865489) B9865489
theorem B8769323 : Blo 2309435 8769323 := bstep (se 1 (by rfl) ⟨6576992, by rfl⟩ : syracuseStep 8769323 = 13153985) B13153985
theorem B5846215 : Blo 2309435 5846215 := bstep (se 1 (by rfl) ⟨4384661, by rfl⟩ : syracuseStep 5846215 = 8769323) B8769323
theorem B7794953 : Blo 2309435 7794953 := bstep (se 2 (by rfl) ⟨2923107, by rfl⟩ : syracuseStep 7794953 = 5846215) B5846215
theorem B5196635 : Blo 2309435 5196635 := bstep (se 1 (by rfl) ⟨3897476, by rfl⟩ : syracuseStep 5196635 = 7794953) B7794953
theorem B3464423 : Blo 2309435 3464423 := bstep (se 1 (by rfl) ⟨2598317, by rfl⟩ : syracuseStep 3464423 = 5196635) B5196635
theorem B2309615 : Blo 2309435 2309615 := bstep (se 1 (by rfl) ⟨1732211, by rfl⟩ : syracuseStep 2309615 = 3464423) B3464423
theorem B3464429 : Blo 2309435 3464429 := bbase (se 3 (by rfl) ⟨649580, by rfl⟩ : syracuseStep 3464429 = 1299161) (by norm_num)
theorem B2309619 : Blo 2309435 2309619 := bstep (se 1 (by rfl) ⟨1732214, by rfl⟩ : syracuseStep 2309619 = 3464429) B3464429
theorem B5196653 : Blo 2309435 5196653 := bbase (se 3 (by rfl) ⟨974372, by rfl⟩ : syracuseStep 5196653 = 1948745) (by norm_num)
theorem B3464435 : Blo 2309435 3464435 := bstep (se 1 (by rfl) ⟨2598326, by rfl⟩ : syracuseStep 3464435 = 5196653) B5196653
theorem B2309623 : Blo 2309435 2309623 := bstep (se 1 (by rfl) ⟨1732217, by rfl⟩ : syracuseStep 2309623 = 3464435) B3464435
theorem B4384685 : Blo 2309435 4384685 := bbase (se 3 (by rfl) ⟨822128, by rfl⟩ : syracuseStep 4384685 = 1644257) (by norm_num)
theorem B2923123 : Blo 2309435 2923123 := bstep (se 1 (by rfl) ⟨2192342, by rfl⟩ : syracuseStep 2923123 = 4384685) B4384685
theorem B3897497 : Blo 2309435 3897497 := bstep (se 2 (by rfl) ⟨1461561, by rfl⟩ : syracuseStep 3897497 = 2923123) B2923123
theorem B2598331 : Blo 2309435 2598331 := bstep (se 1 (by rfl) ⟨1948748, by rfl⟩ : syracuseStep 2598331 = 3897497) B3897497
theorem B3464441 : Blo 2309435 3464441 := bstep (se 2 (by rfl) ⟨1299165, by rfl⟩ : syracuseStep 3464441 = 2598331) B2598331
theorem B2309627 : Blo 2309435 2309627 := bstep (se 1 (by rfl) ⟨1732220, by rfl⟩ : syracuseStep 2309627 = 3464441) B3464441
theorem B2373085 : Blo 2309435 2373085 := bbase (se 3 (by rfl) ⟨444953, by rfl⟩ : syracuseStep 2373085 = 889907) (by norm_num)
theorem B3164113 : Blo 2309435 3164113 := bstep (se 2 (by rfl) ⟨1186542, by rfl⟩ : syracuseStep 3164113 = 2373085) B2373085
theorem B4218817 : Blo 2309435 4218817 := bstep (se 2 (by rfl) ⟨1582056, by rfl⟩ : syracuseStep 4218817 = 3164113) B3164113
theorem B5625089 : Blo 2309435 5625089 := bstep (se 2 (by rfl) ⟨2109408, by rfl⟩ : syracuseStep 5625089 = 4218817) B4218817
theorem B3750059 : Blo 2309435 3750059 := bstep (se 1 (by rfl) ⟨2812544, by rfl⟩ : syracuseStep 3750059 = 5625089) B5625089
theorem B2500039 : Blo 2309435 2500039 := bstep (se 1 (by rfl) ⟨1875029, by rfl⟩ : syracuseStep 2500039 = 3750059) B3750059
theorem B13333541 : Blo 2309435 13333541 := bstep (se 4 (by rfl) ⟨1250019, by rfl⟩ : syracuseStep 13333541 = 2500039) B2500039
theorem B142224437 : Blo 2309435 142224437 := bstep (se 5 (by rfl) ⟨6666770, by rfl⟩ : syracuseStep 142224437 = 13333541) B13333541
theorem B379265165 : Blo 2309435 379265165 := bstep (se 3 (by rfl) ⟨71112218, by rfl⟩ : syracuseStep 379265165 = 142224437) B142224437
theorem B252843443 : Blo 2309435 252843443 := bstep (se 1 (by rfl) ⟨189632582, by rfl⟩ : syracuseStep 252843443 = 379265165) B379265165
theorem B168562295 : Blo 2309435 168562295 := bstep (se 1 (by rfl) ⟨126421721, by rfl⟩ : syracuseStep 168562295 = 252843443) B252843443
theorem B112374863 : Blo 2309435 112374863 := bstep (se 1 (by rfl) ⟨84281147, by rfl⟩ : syracuseStep 112374863 = 168562295) B168562295
theorem B74916575 : Blo 2309435 74916575 := bstep (se 1 (by rfl) ⟨56187431, by rfl⟩ : syracuseStep 74916575 = 112374863) B112374863
theorem B49944383 : Blo 2309435 49944383 := bstep (se 1 (by rfl) ⟨37458287, by rfl⟩ : syracuseStep 49944383 = 74916575) B74916575
theorem B33296255 : Blo 2309435 33296255 := bstep (se 1 (by rfl) ⟨24972191, by rfl⟩ : syracuseStep 33296255 = 49944383) B49944383
theorem B22197503 : Blo 2309435 22197503 := bstep (se 1 (by rfl) ⟨16648127, by rfl⟩ : syracuseStep 22197503 = 33296255) B33296255
theorem B59193341 : Blo 2309435 59193341 := bstep (se 3 (by rfl) ⟨11098751, by rfl⟩ : syracuseStep 59193341 = 22197503) B22197503
theorem B39462227 : Blo 2309435 39462227 := bstep (se 1 (by rfl) ⟨29596670, by rfl⟩ : syracuseStep 39462227 = 59193341) B59193341
theorem B26308151 : Blo 2309435 26308151 := bstep (se 1 (by rfl) ⟨19731113, by rfl⟩ : syracuseStep 26308151 = 39462227) B39462227
theorem B17538767 : Blo 2309435 17538767 := bstep (se 1 (by rfl) ⟨13154075, by rfl⟩ : syracuseStep 17538767 = 26308151) B26308151
theorem B11692511 : Blo 2309435 11692511 := bstep (se 1 (by rfl) ⟨8769383, by rfl⟩ : syracuseStep 11692511 = 17538767) B17538767
theorem B7795007 : Blo 2309435 7795007 := bstep (se 1 (by rfl) ⟨5846255, by rfl⟩ : syracuseStep 7795007 = 11692511) B11692511
theorem B5196671 : Blo 2309435 5196671 := bstep (se 1 (by rfl) ⟨3897503, by rfl⟩ : syracuseStep 5196671 = 7795007) B7795007
theorem B3464447 : Blo 2309435 3464447 := bstep (se 1 (by rfl) ⟨2598335, by rfl⟩ : syracuseStep 3464447 = 5196671) B5196671
theorem B2309631 : Blo 2309435 2309631 := bstep (se 1 (by rfl) ⟨1732223, by rfl⟩ : syracuseStep 2309631 = 3464447) B3464447
theorem B3464453 : Blo 2309435 3464453 := bbase (se 4 (by rfl) ⟨324792, by rfl⟩ : syracuseStep 3464453 = 649585) (by norm_num)
theorem B2309635 : Blo 2309435 2309635 := bstep (se 1 (by rfl) ⟨1732226, by rfl⟩ : syracuseStep 2309635 = 3464453) B3464453
theorem B3897517 : Blo 2309435 3897517 := bbase (se 3 (by rfl) ⟨730784, by rfl⟩ : syracuseStep 3897517 = 1461569) (by norm_num)
theorem B5196689 : Blo 2309435 5196689 := bstep (se 2 (by rfl) ⟨1948758, by rfl⟩ : syracuseStep 5196689 = 3897517) B3897517
theorem B3464459 : Blo 2309435 3464459 := bstep (se 1 (by rfl) ⟨2598344, by rfl⟩ : syracuseStep 3464459 = 5196689) B5196689
theorem B2309639 : Blo 2309435 2309639 := bstep (se 1 (by rfl) ⟨1732229, by rfl⟩ : syracuseStep 2309639 = 3464459) B3464459
theorem B2598349 : Blo 2309435 2598349 := bbase (se 3 (by rfl) ⟨487190, by rfl⟩ : syracuseStep 2598349 = 974381) (by norm_num)
theorem B3464465 : Blo 2309435 3464465 := bstep (se 2 (by rfl) ⟨1299174, by rfl⟩ : syracuseStep 3464465 = 2598349) B2598349
theorem B2309643 : Blo 2309435 2309643 := bstep (se 1 (by rfl) ⟨1732232, by rfl⟩ : syracuseStep 2309643 = 3464465) B3464465
theorem B7795061 : Blo 2309435 7795061 := bbase (se 5 (by rfl) ⟨365393, by rfl⟩ : syracuseStep 7795061 = 730787) (by norm_num)
theorem B5196707 : Blo 2309435 5196707 := bstep (se 1 (by rfl) ⟨3897530, by rfl⟩ : syracuseStep 5196707 = 7795061) B7795061
theorem B3464471 : Blo 2309435 3464471 := bstep (se 1 (by rfl) ⟨2598353, by rfl⟩ : syracuseStep 3464471 = 5196707) B5196707
theorem B2309647 : Blo 2309435 2309647 := bstep (se 1 (by rfl) ⟨1732235, by rfl⟩ : syracuseStep 2309647 = 3464471) B3464471
theorem B3464477 : Blo 2309435 3464477 := bbase (se 3 (by rfl) ⟨649589, by rfl⟩ : syracuseStep 3464477 = 1299179) (by norm_num)
theorem B2309651 : Blo 2309435 2309651 := bstep (se 1 (by rfl) ⟨1732238, by rfl⟩ : syracuseStep 2309651 = 3464477) B3464477
theorem B5196725 : Blo 2309435 5196725 := bbase (se 5 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 5196725 = 487193) (by norm_num)
theorem B3464483 : Blo 2309435 3464483 := bstep (se 1 (by rfl) ⟨2598362, by rfl⟩ : syracuseStep 3464483 = 5196725) B5196725
theorem B2309655 : Blo 2309435 2309655 := bstep (se 1 (by rfl) ⟨1732241, by rfl⟩ : syracuseStep 2309655 = 3464483) B3464483
theorem B5000141 : Blo 2309435 5000141 := bbase (se 3 (by rfl) ⟨937526, by rfl⟩ : syracuseStep 5000141 = 1875053) (by norm_num)
theorem B13333709 : Blo 2309435 13333709 := bstep (se 3 (by rfl) ⟨2500070, by rfl⟩ : syracuseStep 13333709 = 5000141) B5000141
theorem B8889139 : Blo 2309435 8889139 := bstep (se 1 (by rfl) ⟨6666854, by rfl⟩ : syracuseStep 8889139 = 13333709) B13333709
theorem B11852185 : Blo 2309435 11852185 := bstep (se 2 (by rfl) ⟨4444569, by rfl⟩ : syracuseStep 11852185 = 8889139) B8889139
theorem B15802913 : Blo 2309435 15802913 := bstep (se 2 (by rfl) ⟨5926092, by rfl⟩ : syracuseStep 15802913 = 11852185) B11852185
theorem B10535275 : Blo 2309435 10535275 := bstep (se 1 (by rfl) ⟨7901456, by rfl⟩ : syracuseStep 10535275 = 15802913) B15802913
theorem B14047033 : Blo 2309435 14047033 := bstep (se 2 (by rfl) ⟨5267637, by rfl⟩ : syracuseStep 14047033 = 10535275) B10535275
theorem B18729377 : Blo 2309435 18729377 := bstep (se 2 (by rfl) ⟨7023516, by rfl⟩ : syracuseStep 18729377 = 14047033) B14047033
theorem B12486251 : Blo 2309435 12486251 := bstep (se 1 (by rfl) ⟨9364688, by rfl⟩ : syracuseStep 12486251 = 18729377) B18729377
theorem B8324167 : Blo 2309435 8324167 := bstep (se 1 (by rfl) ⟨6243125, by rfl⟩ : syracuseStep 8324167 = 12486251) B12486251
theorem B11098889 : Blo 2309435 11098889 := bstep (se 2 (by rfl) ⟨4162083, by rfl⟩ : syracuseStep 11098889 = 8324167) B8324167
theorem B7399259 : Blo 2309435 7399259 := bstep (se 1 (by rfl) ⟨5549444, by rfl⟩ : syracuseStep 7399259 = 11098889) B11098889
theorem B4932839 : Blo 2309435 4932839 := bstep (se 1 (by rfl) ⟨3699629, by rfl⟩ : syracuseStep 4932839 = 7399259) B7399259
theorem B13154237 : Blo 2309435 13154237 := bstep (se 3 (by rfl) ⟨2466419, by rfl⟩ : syracuseStep 13154237 = 4932839) B4932839
theorem B8769491 : Blo 2309435 8769491 := bstep (se 1 (by rfl) ⟨6577118, by rfl⟩ : syracuseStep 8769491 = 13154237) B13154237
theorem B5846327 : Blo 2309435 5846327 := bstep (se 1 (by rfl) ⟨4384745, by rfl⟩ : syracuseStep 5846327 = 8769491) B8769491
theorem B3897551 : Blo 2309435 3897551 := bstep (se 1 (by rfl) ⟨2923163, by rfl⟩ : syracuseStep 3897551 = 5846327) B5846327
theorem B2598367 : Blo 2309435 2598367 := bstep (se 1 (by rfl) ⟨1948775, by rfl⟩ : syracuseStep 2598367 = 3897551) B3897551
theorem B3464489 : Blo 2309435 3464489 := bstep (se 2 (by rfl) ⟨1299183, by rfl⟩ : syracuseStep 3464489 = 2598367) B2598367
theorem B2309659 : Blo 2309435 2309659 := bstep (se 1 (by rfl) ⟨1732244, by rfl⟩ : syracuseStep 2309659 = 3464489) B3464489
theorem B37969877 : Blo 2309435 37969877 := bbase (se 7 (by rfl) ⟨444959, by rfl⟩ : syracuseStep 37969877 = 889919) (by norm_num)
theorem B101253005 : Blo 2309435 101253005 := bstep (se 3 (by rfl) ⟨18984938, by rfl⟩ : syracuseStep 101253005 = 37969877) B37969877
theorem B67502003 : Blo 2309435 67502003 := bstep (se 1 (by rfl) ⟨50626502, by rfl⟩ : syracuseStep 67502003 = 101253005) B101253005
theorem B180005341 : Blo 2309435 180005341 := bstep (se 3 (by rfl) ⟨33751001, by rfl⟩ : syracuseStep 180005341 = 67502003) B67502003
theorem B240007121 : Blo 2309435 240007121 := bstep (se 2 (by rfl) ⟨90002670, by rfl⟩ : syracuseStep 240007121 = 180005341) B180005341
theorem B160004747 : Blo 2309435 160004747 := bstep (se 1 (by rfl) ⟨120003560, by rfl⟩ : syracuseStep 160004747 = 240007121) B240007121
theorem B106669831 : Blo 2309435 106669831 := bstep (se 1 (by rfl) ⟨80002373, by rfl⟩ : syracuseStep 106669831 = 160004747) B160004747
theorem B142226441 : Blo 2309435 142226441 := bstep (se 2 (by rfl) ⟨53334915, by rfl⟩ : syracuseStep 142226441 = 106669831) B106669831
theorem B94817627 : Blo 2309435 94817627 := bstep (se 1 (by rfl) ⟨71113220, by rfl⟩ : syracuseStep 94817627 = 142226441) B142226441
theorem B63211751 : Blo 2309435 63211751 := bstep (se 1 (by rfl) ⟨47408813, by rfl⟩ : syracuseStep 63211751 = 94817627) B94817627
theorem B42141167 : Blo 2309435 42141167 := bstep (se 1 (by rfl) ⟨31605875, by rfl⟩ : syracuseStep 42141167 = 63211751) B63211751
theorem B28094111 : Blo 2309435 28094111 := bstep (se 1 (by rfl) ⟨21070583, by rfl⟩ : syracuseStep 28094111 = 42141167) B42141167
theorem B18729407 : Blo 2309435 18729407 := bstep (se 1 (by rfl) ⟨14047055, by rfl⟩ : syracuseStep 18729407 = 28094111) B28094111
theorem B12486271 : Blo 2309435 12486271 := bstep (se 1 (by rfl) ⟨9364703, by rfl⟩ : syracuseStep 12486271 = 18729407) B18729407
theorem B16648361 : Blo 2309435 16648361 := bstep (se 2 (by rfl) ⟨6243135, by rfl⟩ : syracuseStep 16648361 = 12486271) B12486271
theorem B11098907 : Blo 2309435 11098907 := bstep (se 1 (by rfl) ⟨8324180, by rfl⟩ : syracuseStep 11098907 = 16648361) B16648361
theorem B7399271 : Blo 2309435 7399271 := bstep (se 1 (by rfl) ⟨5549453, by rfl⟩ : syracuseStep 7399271 = 11098907) B11098907
theorem B4932847 : Blo 2309435 4932847 := bstep (se 1 (by rfl) ⟨3699635, by rfl⟩ : syracuseStep 4932847 = 7399271) B7399271
theorem B6577129 : Blo 2309435 6577129 := bstep (se 2 (by rfl) ⟨2466423, by rfl⟩ : syracuseStep 6577129 = 4932847) B4932847
theorem B8769505 : Blo 2309435 8769505 := bstep (se 2 (by rfl) ⟨3288564, by rfl⟩ : syracuseStep 8769505 = 6577129) B6577129
theorem B11692673 : Blo 2309435 11692673 := bstep (se 2 (by rfl) ⟨4384752, by rfl⟩ : syracuseStep 11692673 = 8769505) B8769505
theorem B7795115 : Blo 2309435 7795115 := bstep (se 1 (by rfl) ⟨5846336, by rfl⟩ : syracuseStep 7795115 = 11692673) B11692673
theorem B5196743 : Blo 2309435 5196743 := bstep (se 1 (by rfl) ⟨3897557, by rfl⟩ : syracuseStep 5196743 = 7795115) B7795115
theorem B3464495 : Blo 2309435 3464495 := bstep (se 1 (by rfl) ⟨2598371, by rfl⟩ : syracuseStep 3464495 = 5196743) B5196743
theorem B2309663 : Blo 2309435 2309663 := bstep (se 1 (by rfl) ⟨1732247, by rfl⟩ : syracuseStep 2309663 = 3464495) B3464495
theorem B3464501 : Blo 2309435 3464501 := bbase (se 5 (by rfl) ⟨162398, by rfl⟩ : syracuseStep 3464501 = 324797) (by norm_num)
theorem B2309667 : Blo 2309435 2309667 := bstep (se 1 (by rfl) ⟨1732250, by rfl⟩ : syracuseStep 2309667 = 3464501) B3464501
theorem B5846357 : Blo 2309435 5846357 := bbase (se 13 (by rfl) ⟨1070, by rfl⟩ : syracuseStep 5846357 = 2141) (by norm_num)
theorem B3897571 : Blo 2309435 3897571 := bstep (se 1 (by rfl) ⟨2923178, by rfl⟩ : syracuseStep 3897571 = 5846357) B5846357
theorem B5196761 : Blo 2309435 5196761 := bstep (se 2 (by rfl) ⟨1948785, by rfl⟩ : syracuseStep 5196761 = 3897571) B3897571
theorem B3464507 : Blo 2309435 3464507 := bstep (se 1 (by rfl) ⟨2598380, by rfl⟩ : syracuseStep 3464507 = 5196761) B5196761
theorem B2309671 : Blo 2309435 2309671 := bstep (se 1 (by rfl) ⟨1732253, by rfl⟩ : syracuseStep 2309671 = 3464507) B3464507
theorem B2598385 : Blo 2309435 2598385 := bbase (se 2 (by rfl) ⟨974394, by rfl⟩ : syracuseStep 2598385 = 1948789) (by norm_num)
theorem B3464513 : Blo 2309435 3464513 := bstep (se 2 (by rfl) ⟨1299192, by rfl⟩ : syracuseStep 3464513 = 2598385) B2598385
theorem B2309675 : Blo 2309435 2309675 := bstep (se 1 (by rfl) ⟨1732256, by rfl⟩ : syracuseStep 2309675 = 3464513) B3464513
theorem B14798645 : Blo 2309435 14798645 := bbase (se 5 (by rfl) ⟨693686, by rfl⟩ : syracuseStep 14798645 = 1387373) (by norm_num)
theorem B9865763 : Blo 2309435 9865763 := bstep (se 1 (by rfl) ⟨7399322, by rfl⟩ : syracuseStep 9865763 = 14798645) B14798645
theorem B6577175 : Blo 2309435 6577175 := bstep (se 1 (by rfl) ⟨4932881, by rfl⟩ : syracuseStep 6577175 = 9865763) B9865763
theorem B4384783 : Blo 2309435 4384783 := bstep (se 1 (by rfl) ⟨3288587, by rfl⟩ : syracuseStep 4384783 = 6577175) B6577175
theorem B5846377 : Blo 2309435 5846377 := bstep (se 2 (by rfl) ⟨2192391, by rfl⟩ : syracuseStep 5846377 = 4384783) B4384783
theorem B7795169 : Blo 2309435 7795169 := bstep (se 2 (by rfl) ⟨2923188, by rfl⟩ : syracuseStep 7795169 = 5846377) B5846377
theorem B5196779 : Blo 2309435 5196779 := bstep (se 1 (by rfl) ⟨3897584, by rfl⟩ : syracuseStep 5196779 = 7795169) B7795169
theorem B3464519 : Blo 2309435 3464519 := bstep (se 1 (by rfl) ⟨2598389, by rfl⟩ : syracuseStep 3464519 = 5196779) B5196779
theorem B2309679 : Blo 2309435 2309679 := bstep (se 1 (by rfl) ⟨1732259, by rfl⟩ : syracuseStep 2309679 = 3464519) B3464519
theorem B3464525 : Blo 2309435 3464525 := bbase (se 3 (by rfl) ⟨649598, by rfl⟩ : syracuseStep 3464525 = 1299197) (by norm_num)
theorem B2309683 : Blo 2309435 2309683 := bstep (se 1 (by rfl) ⟨1732262, by rfl⟩ : syracuseStep 2309683 = 3464525) B3464525
theorem B5196797 : Blo 2309435 5196797 := bbase (se 3 (by rfl) ⟨974399, by rfl⟩ : syracuseStep 5196797 = 1948799) (by norm_num)
theorem B3464531 : Blo 2309435 3464531 := bstep (se 1 (by rfl) ⟨2598398, by rfl⟩ : syracuseStep 3464531 = 5196797) B5196797
theorem B2309687 : Blo 2309435 2309687 := bstep (se 1 (by rfl) ⟨1732265, by rfl⟩ : syracuseStep 2309687 = 3464531) B3464531
theorem B3897605 : Blo 2309435 3897605 := bbase (se 4 (by rfl) ⟨365400, by rfl⟩ : syracuseStep 3897605 = 730801) (by norm_num)
theorem B2598403 : Blo 2309435 2598403 := bstep (se 1 (by rfl) ⟨1948802, by rfl⟩ : syracuseStep 2598403 = 3897605) B3897605
theorem B3464537 : Blo 2309435 3464537 := bstep (se 2 (by rfl) ⟨1299201, by rfl⟩ : syracuseStep 3464537 = 2598403) B2598403
theorem B2309691 : Blo 2309435 2309691 := bstep (se 1 (by rfl) ⟨1732268, by rfl⟩ : syracuseStep 2309691 = 3464537) B3464537
theorem B17539253 : Blo 2309435 17539253 := bbase (se 5 (by rfl) ⟨822152, by rfl⟩ : syracuseStep 17539253 = 1644305) (by norm_num)
theorem B11692835 : Blo 2309435 11692835 := bstep (se 1 (by rfl) ⟨8769626, by rfl⟩ : syracuseStep 11692835 = 17539253) B17539253
theorem B7795223 : Blo 2309435 7795223 := bstep (se 1 (by rfl) ⟨5846417, by rfl⟩ : syracuseStep 7795223 = 11692835) B11692835
theorem B5196815 : Blo 2309435 5196815 := bstep (se 1 (by rfl) ⟨3897611, by rfl⟩ : syracuseStep 5196815 = 7795223) B7795223
theorem B3464543 : Blo 2309435 3464543 := bstep (se 1 (by rfl) ⟨2598407, by rfl⟩ : syracuseStep 3464543 = 5196815) B5196815
theorem B2309695 : Blo 2309435 2309695 := bstep (se 1 (by rfl) ⟨1732271, by rfl⟩ : syracuseStep 2309695 = 3464543) B3464543
theorem B3464549 : Blo 2309435 3464549 := bbase (se 4 (by rfl) ⟨324801, by rfl⟩ : syracuseStep 3464549 = 649603) (by norm_num)
theorem B2309699 : Blo 2309435 2309699 := bstep (se 1 (by rfl) ⟨1732274, by rfl⟩ : syracuseStep 2309699 = 3464549) B3464549
theorem B4384829 : Blo 2309435 4384829 := bbase (se 3 (by rfl) ⟨822155, by rfl⟩ : syracuseStep 4384829 = 1644311) (by norm_num)
theorem B2923219 : Blo 2309435 2923219 := bstep (se 1 (by rfl) ⟨2192414, by rfl⟩ : syracuseStep 2923219 = 4384829) B4384829
theorem B3897625 : Blo 2309435 3897625 := bstep (se 2 (by rfl) ⟨1461609, by rfl⟩ : syracuseStep 3897625 = 2923219) B2923219
theorem B5196833 : Blo 2309435 5196833 := bstep (se 2 (by rfl) ⟨1948812, by rfl⟩ : syracuseStep 5196833 = 3897625) B3897625
theorem B3464555 : Blo 2309435 3464555 := bstep (se 1 (by rfl) ⟨2598416, by rfl⟩ : syracuseStep 3464555 = 5196833) B5196833
theorem B2309703 : Blo 2309435 2309703 := bstep (se 1 (by rfl) ⟨1732277, by rfl⟩ : syracuseStep 2309703 = 3464555) B3464555
theorem B2598421 : Blo 2309435 2598421 := bbase (se 6 (by rfl) ⟨60900, by rfl⟩ : syracuseStep 2598421 = 121801) (by norm_num)
theorem B3464561 : Blo 2309435 3464561 := bstep (se 2 (by rfl) ⟨1299210, by rfl⟩ : syracuseStep 3464561 = 2598421) B2598421
theorem B2309707 : Blo 2309435 2309707 := bstep (se 1 (by rfl) ⟨1732280, by rfl⟩ : syracuseStep 2309707 = 3464561) B3464561
theorem B2923229 : Blo 2309435 2923229 := bbase (se 3 (by rfl) ⟨548105, by rfl⟩ : syracuseStep 2923229 = 1096211) (by norm_num)
theorem B7795277 : Blo 2309435 7795277 := bstep (se 3 (by rfl) ⟨1461614, by rfl⟩ : syracuseStep 7795277 = 2923229) B2923229
theorem B5196851 : Blo 2309435 5196851 := bstep (se 1 (by rfl) ⟨3897638, by rfl⟩ : syracuseStep 5196851 = 7795277) B7795277
theorem B3464567 : Blo 2309435 3464567 := bstep (se 1 (by rfl) ⟨2598425, by rfl⟩ : syracuseStep 3464567 = 5196851) B5196851
theorem B2309711 : Blo 2309435 2309711 := bstep (se 1 (by rfl) ⟨1732283, by rfl⟩ : syracuseStep 2309711 = 3464567) B3464567
theorem B3464573 : Blo 2309435 3464573 := bbase (se 3 (by rfl) ⟨649607, by rfl⟩ : syracuseStep 3464573 = 1299215) (by norm_num)
theorem B2309715 : Blo 2309435 2309715 := bstep (se 1 (by rfl) ⟨1732286, by rfl⟩ : syracuseStep 2309715 = 3464573) B3464573
theorem B5196869 : Blo 2309435 5196869 := bbase (se 4 (by rfl) ⟨487206, by rfl⟩ : syracuseStep 5196869 = 974413) (by norm_num)
theorem B3464579 : Blo 2309435 3464579 := bstep (se 1 (by rfl) ⟨2598434, by rfl⟩ : syracuseStep 3464579 = 5196869) B5196869
theorem B2309719 : Blo 2309435 2309719 := bstep (se 1 (by rfl) ⟨1732289, by rfl⟩ : syracuseStep 2309719 = 3464579) B3464579
theorem B6577301 : Blo 2309435 6577301 := bbase (se 6 (by rfl) ⟨154155, by rfl⟩ : syracuseStep 6577301 = 308311) (by norm_num)
theorem B4384867 : Blo 2309435 4384867 := bstep (se 1 (by rfl) ⟨3288650, by rfl⟩ : syracuseStep 4384867 = 6577301) B6577301
theorem B5846489 : Blo 2309435 5846489 := bstep (se 2 (by rfl) ⟨2192433, by rfl⟩ : syracuseStep 5846489 = 4384867) B4384867
theorem B3897659 : Blo 2309435 3897659 := bstep (se 1 (by rfl) ⟨2923244, by rfl⟩ : syracuseStep 3897659 = 5846489) B5846489
theorem B2598439 : Blo 2309435 2598439 := bstep (se 1 (by rfl) ⟨1948829, by rfl⟩ : syracuseStep 2598439 = 3897659) B3897659
theorem B3464585 : Blo 2309435 3464585 := bstep (se 2 (by rfl) ⟨1299219, by rfl⟩ : syracuseStep 3464585 = 2598439) B2598439
theorem B2309723 : Blo 2309435 2309723 := bstep (se 1 (by rfl) ⟨1732292, by rfl⟩ : syracuseStep 2309723 = 3464585) B3464585
theorem B11692997 : Blo 2309435 11692997 := bbase (se 4 (by rfl) ⟨1096218, by rfl⟩ : syracuseStep 11692997 = 2192437) (by norm_num)
theorem B7795331 : Blo 2309435 7795331 := bstep (se 1 (by rfl) ⟨5846498, by rfl⟩ : syracuseStep 7795331 = 11692997) B11692997
theorem B5196887 : Blo 2309435 5196887 := bstep (se 1 (by rfl) ⟨3897665, by rfl⟩ : syracuseStep 5196887 = 7795331) B7795331
theorem B3464591 : Blo 2309435 3464591 := bstep (se 1 (by rfl) ⟨2598443, by rfl⟩ : syracuseStep 3464591 = 5196887) B5196887
theorem B2309727 : Blo 2309435 2309727 := bstep (se 1 (by rfl) ⟨1732295, by rfl⟩ : syracuseStep 2309727 = 3464591) B3464591
theorem B3464597 : Blo 2309435 3464597 := bbase (se 6 (by rfl) ⟨81201, by rfl⟩ : syracuseStep 3464597 = 162403) (by norm_num)
theorem B2309731 : Blo 2309435 2309731 := bstep (se 1 (by rfl) ⟨1732298, by rfl⟩ : syracuseStep 2309731 = 3464597) B3464597
theorem B9364997 : Blo 2309435 9364997 := bbase (se 4 (by rfl) ⟨877968, by rfl⟩ : syracuseStep 9364997 = 1755937) (by norm_num)
theorem B6243331 : Blo 2309435 6243331 := bstep (se 1 (by rfl) ⟨4682498, by rfl⟩ : syracuseStep 6243331 = 9364997) B9364997
theorem B8324441 : Blo 2309435 8324441 := bstep (se 2 (by rfl) ⟨3121665, by rfl⟩ : syracuseStep 8324441 = 6243331) B6243331
theorem B5549627 : Blo 2309435 5549627 := bstep (se 1 (by rfl) ⟨4162220, by rfl⟩ : syracuseStep 5549627 = 8324441) B8324441
theorem B3699751 : Blo 2309435 3699751 := bstep (se 1 (by rfl) ⟨2774813, by rfl⟩ : syracuseStep 3699751 = 5549627) B5549627
theorem B4933001 : Blo 2309435 4933001 := bstep (se 2 (by rfl) ⟨1849875, by rfl⟩ : syracuseStep 4933001 = 3699751) B3699751
theorem B13154669 : Blo 2309435 13154669 := bstep (se 3 (by rfl) ⟨2466500, by rfl⟩ : syracuseStep 13154669 = 4933001) B4933001
theorem B8769779 : Blo 2309435 8769779 := bstep (se 1 (by rfl) ⟨6577334, by rfl⟩ : syracuseStep 8769779 = 13154669) B13154669
theorem B5846519 : Blo 2309435 5846519 := bstep (se 1 (by rfl) ⟨4384889, by rfl⟩ : syracuseStep 5846519 = 8769779) B8769779
theorem B3897679 : Blo 2309435 3897679 := bstep (se 1 (by rfl) ⟨2923259, by rfl⟩ : syracuseStep 3897679 = 5846519) B5846519
theorem B5196905 : Blo 2309435 5196905 := bstep (se 2 (by rfl) ⟨1948839, by rfl⟩ : syracuseStep 5196905 = 3897679) B3897679
theorem B3464603 : Blo 2309435 3464603 := bstep (se 1 (by rfl) ⟨2598452, by rfl⟩ : syracuseStep 3464603 = 5196905) B5196905
theorem B2309735 : Blo 2309435 2309735 := bstep (se 1 (by rfl) ⟨1732301, by rfl⟩ : syracuseStep 2309735 = 3464603) B3464603
theorem B2598457 : Blo 2309435 2598457 := bbase (se 2 (by rfl) ⟨974421, by rfl⟩ : syracuseStep 2598457 = 1948843) (by norm_num)
theorem B3464609 : Blo 2309435 3464609 := bstep (se 2 (by rfl) ⟨1299228, by rfl⟩ : syracuseStep 3464609 = 2598457) B2598457
theorem B2309739 : Blo 2309435 2309739 := bstep (se 1 (by rfl) ⟨1732304, by rfl⟩ : syracuseStep 2309739 = 3464609) B3464609
theorem B2466509 : Blo 2309435 2466509 := bbase (se 3 (by rfl) ⟨462470, by rfl⟩ : syracuseStep 2466509 = 924941) (by norm_num)
theorem B6577357 : Blo 2309435 6577357 := bstep (se 3 (by rfl) ⟨1233254, by rfl⟩ : syracuseStep 6577357 = 2466509) B2466509
theorem B8769809 : Blo 2309435 8769809 := bstep (se 2 (by rfl) ⟨3288678, by rfl⟩ : syracuseStep 8769809 = 6577357) B6577357
theorem B5846539 : Blo 2309435 5846539 := bstep (se 1 (by rfl) ⟨4384904, by rfl⟩ : syracuseStep 5846539 = 8769809) B8769809
theorem B7795385 : Blo 2309435 7795385 := bstep (se 2 (by rfl) ⟨2923269, by rfl⟩ : syracuseStep 7795385 = 5846539) B5846539
theorem B5196923 : Blo 2309435 5196923 := bstep (se 1 (by rfl) ⟨3897692, by rfl⟩ : syracuseStep 5196923 = 7795385) B7795385
theorem B3464615 : Blo 2309435 3464615 := bstep (se 1 (by rfl) ⟨2598461, by rfl⟩ : syracuseStep 3464615 = 5196923) B5196923
theorem B2309743 : Blo 2309435 2309743 := bstep (se 1 (by rfl) ⟨1732307, by rfl⟩ : syracuseStep 2309743 = 3464615) B3464615
theorem B3464621 : Blo 2309435 3464621 := bbase (se 3 (by rfl) ⟨649616, by rfl⟩ : syracuseStep 3464621 = 1299233) (by norm_num)
theorem B2309747 : Blo 2309435 2309747 := bstep (se 1 (by rfl) ⟨1732310, by rfl⟩ : syracuseStep 2309747 = 3464621) B3464621
theorem B5196941 : Blo 2309435 5196941 := bbase (se 3 (by rfl) ⟨974426, by rfl⟩ : syracuseStep 5196941 = 1948853) (by norm_num)
theorem B3464627 : Blo 2309435 3464627 := bstep (se 1 (by rfl) ⟨2598470, by rfl⟩ : syracuseStep 3464627 = 5196941) B5196941
theorem B2309751 : Blo 2309435 2309751 := bstep (se 1 (by rfl) ⟨1732313, by rfl⟩ : syracuseStep 2309751 = 3464627) B3464627
theorem B2923285 : Blo 2309435 2923285 := bbase (se 6 (by rfl) ⟨68514, by rfl⟩ : syracuseStep 2923285 = 137029) (by norm_num)
theorem B3897713 : Blo 2309435 3897713 := bstep (se 2 (by rfl) ⟨1461642, by rfl⟩ : syracuseStep 3897713 = 2923285) B2923285
theorem B2598475 : Blo 2309435 2598475 := bstep (se 1 (by rfl) ⟨1948856, by rfl⟩ : syracuseStep 2598475 = 3897713) B3897713
theorem B3464633 : Blo 2309435 3464633 := bstep (se 2 (by rfl) ⟨1299237, by rfl⟩ : syracuseStep 3464633 = 2598475) B2598475
theorem B2309755 : Blo 2309435 2309755 := bstep (se 1 (by rfl) ⟨1732316, by rfl⟩ : syracuseStep 2309755 = 3464633) B3464633
theorem B7500533 : Blo 2309435 7500533 := bbase (se 5 (by rfl) ⟨351587, by rfl⟩ : syracuseStep 7500533 = 703175) (by norm_num)
theorem B20001421 : Blo 2309435 20001421 := bstep (se 3 (by rfl) ⟨3750266, by rfl⟩ : syracuseStep 20001421 = 7500533) B7500533
theorem B26668561 : Blo 2309435 26668561 := bstep (se 2 (by rfl) ⟨10000710, by rfl⟩ : syracuseStep 26668561 = 20001421) B20001421
theorem B35558081 : Blo 2309435 35558081 := bstep (se 2 (by rfl) ⟨13334280, by rfl⟩ : syracuseStep 35558081 = 26668561) B26668561
theorem B23705387 : Blo 2309435 23705387 := bstep (se 1 (by rfl) ⟨17779040, by rfl⟩ : syracuseStep 23705387 = 35558081) B35558081
theorem B15803591 : Blo 2309435 15803591 := bstep (se 1 (by rfl) ⟨11852693, by rfl⟩ : syracuseStep 15803591 = 23705387) B23705387
theorem B168571637 : Blo 2309435 168571637 := bstep (se 5 (by rfl) ⟨7901795, by rfl⟩ : syracuseStep 168571637 = 15803591) B15803591
theorem B112381091 : Blo 2309435 112381091 := bstep (se 1 (by rfl) ⟨84285818, by rfl⟩ : syracuseStep 112381091 = 168571637) B168571637
theorem B74920727 : Blo 2309435 74920727 := bstep (se 1 (by rfl) ⟨56190545, by rfl⟩ : syracuseStep 74920727 = 112381091) B112381091
theorem B49947151 : Blo 2309435 49947151 := bstep (se 1 (by rfl) ⟨37460363, by rfl⟩ : syracuseStep 49947151 = 74920727) B74920727
theorem B66596201 : Blo 2309435 66596201 := bstep (se 2 (by rfl) ⟨24973575, by rfl⟩ : syracuseStep 66596201 = 49947151) B49947151
theorem B44397467 : Blo 2309435 44397467 := bstep (se 1 (by rfl) ⟨33298100, by rfl⟩ : syracuseStep 44397467 = 66596201) B66596201
theorem B29598311 : Blo 2309435 29598311 := bstep (se 1 (by rfl) ⟨22198733, by rfl⟩ : syracuseStep 29598311 = 44397467) B44397467
theorem B19732207 : Blo 2309435 19732207 := bstep (se 1 (by rfl) ⟨14799155, by rfl⟩ : syracuseStep 19732207 = 29598311) B29598311
theorem B26309609 : Blo 2309435 26309609 := bstep (se 2 (by rfl) ⟨9866103, by rfl⟩ : syracuseStep 26309609 = 19732207) B19732207
theorem B17539739 : Blo 2309435 17539739 := bstep (se 1 (by rfl) ⟨13154804, by rfl⟩ : syracuseStep 17539739 = 26309609) B26309609
theorem B11693159 : Blo 2309435 11693159 := bstep (se 1 (by rfl) ⟨8769869, by rfl⟩ : syracuseStep 11693159 = 17539739) B17539739
theorem B7795439 : Blo 2309435 7795439 := bstep (se 1 (by rfl) ⟨5846579, by rfl⟩ : syracuseStep 7795439 = 11693159) B11693159
theorem B5196959 : Blo 2309435 5196959 := bstep (se 1 (by rfl) ⟨3897719, by rfl⟩ : syracuseStep 5196959 = 7795439) B7795439
theorem B3464639 : Blo 2309435 3464639 := bstep (se 1 (by rfl) ⟨2598479, by rfl⟩ : syracuseStep 3464639 = 5196959) B5196959
theorem B2309759 : Blo 2309435 2309759 := bstep (se 1 (by rfl) ⟨1732319, by rfl⟩ : syracuseStep 2309759 = 3464639) B3464639
theorem B3464645 : Blo 2309435 3464645 := bbase (se 4 (by rfl) ⟨324810, by rfl⟩ : syracuseStep 3464645 = 649621) (by norm_num)
theorem B2309763 : Blo 2309435 2309763 := bstep (se 1 (by rfl) ⟨1732322, by rfl⟩ : syracuseStep 2309763 = 3464645) B3464645
theorem B3897733 : Blo 2309435 3897733 := bbase (se 4 (by rfl) ⟨365412, by rfl⟩ : syracuseStep 3897733 = 730825) (by norm_num)
theorem B5196977 : Blo 2309435 5196977 := bstep (se 2 (by rfl) ⟨1948866, by rfl⟩ : syracuseStep 5196977 = 3897733) B3897733
theorem B3464651 : Blo 2309435 3464651 := bstep (se 1 (by rfl) ⟨2598488, by rfl⟩ : syracuseStep 3464651 = 5196977) B5196977
theorem B2309767 : Blo 2309435 2309767 := bstep (se 1 (by rfl) ⟨1732325, by rfl⟩ : syracuseStep 2309767 = 3464651) B3464651
theorem B2598493 : Blo 2309435 2598493 := bbase (se 3 (by rfl) ⟨487217, by rfl⟩ : syracuseStep 2598493 = 974435) (by norm_num)
theorem B3464657 : Blo 2309435 3464657 := bstep (se 2 (by rfl) ⟨1299246, by rfl⟩ : syracuseStep 3464657 = 2598493) B2598493
theorem B2309771 : Blo 2309435 2309771 := bstep (se 1 (by rfl) ⟨1732328, by rfl⟩ : syracuseStep 2309771 = 3464657) B3464657
theorem B7795493 : Blo 2309435 7795493 := bbase (se 4 (by rfl) ⟨730827, by rfl⟩ : syracuseStep 7795493 = 1461655) (by norm_num)
theorem B5196995 : Blo 2309435 5196995 := bstep (se 1 (by rfl) ⟨3897746, by rfl⟩ : syracuseStep 5196995 = 7795493) B7795493
theorem B3464663 : Blo 2309435 3464663 := bstep (se 1 (by rfl) ⟨2598497, by rfl⟩ : syracuseStep 3464663 = 5196995) B5196995
theorem B2309775 : Blo 2309435 2309775 := bstep (se 1 (by rfl) ⟨1732331, by rfl⟩ : syracuseStep 2309775 = 3464663) B3464663
theorem B3464669 : Blo 2309435 3464669 := bbase (se 3 (by rfl) ⟨649625, by rfl⟩ : syracuseStep 3464669 = 1299251) (by norm_num)
theorem B2309779 : Blo 2309435 2309779 := bstep (se 1 (by rfl) ⟨1732334, by rfl⟩ : syracuseStep 2309779 = 3464669) B3464669
theorem B5197013 : Blo 2309435 5197013 := bbase (se 7 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 5197013 = 121805) (by norm_num)
theorem B3464675 : Blo 2309435 3464675 := bstep (se 1 (by rfl) ⟨2598506, by rfl⟩ : syracuseStep 3464675 = 5197013) B5197013
theorem B2309783 : Blo 2309435 2309783 := bstep (se 1 (by rfl) ⟨1732337, by rfl⟩ : syracuseStep 2309783 = 3464675) B3464675
theorem B7399669 : Blo 2309435 7399669 := bbase (se 5 (by rfl) ⟨346859, by rfl⟩ : syracuseStep 7399669 = 693719) (by norm_num)
theorem B9866225 : Blo 2309435 9866225 := bstep (se 2 (by rfl) ⟨3699834, by rfl⟩ : syracuseStep 9866225 = 7399669) B7399669
theorem B6577483 : Blo 2309435 6577483 := bstep (se 1 (by rfl) ⟨4933112, by rfl⟩ : syracuseStep 6577483 = 9866225) B9866225
theorem B8769977 : Blo 2309435 8769977 := bstep (se 2 (by rfl) ⟨3288741, by rfl⟩ : syracuseStep 8769977 = 6577483) B6577483
theorem B5846651 : Blo 2309435 5846651 := bstep (se 1 (by rfl) ⟨4384988, by rfl⟩ : syracuseStep 5846651 = 8769977) B8769977
theorem B3897767 : Blo 2309435 3897767 := bstep (se 1 (by rfl) ⟨2923325, by rfl⟩ : syracuseStep 3897767 = 5846651) B5846651
theorem B2598511 : Blo 2309435 2598511 := bstep (se 1 (by rfl) ⟨1948883, by rfl⟩ : syracuseStep 2598511 = 3897767) B3897767
theorem B3464681 : Blo 2309435 3464681 := bstep (se 2 (by rfl) ⟨1299255, by rfl⟩ : syracuseStep 3464681 = 2598511) B2598511
theorem B2309787 : Blo 2309435 2309787 := bstep (se 1 (by rfl) ⟨1732340, by rfl⟩ : syracuseStep 2309787 = 3464681) B3464681
theorem B2633969 : Blo 2309435 2633969 := bbase (se 2 (by rfl) ⟨987738, by rfl⟩ : syracuseStep 2633969 = 1975477) (by norm_num)
theorem B7023917 : Blo 2309435 7023917 := bstep (se 3 (by rfl) ⟨1316984, by rfl⟩ : syracuseStep 7023917 = 2633969) B2633969
theorem B4682611 : Blo 2309435 4682611 := bstep (se 1 (by rfl) ⟨3511958, by rfl⟩ : syracuseStep 4682611 = 7023917) B7023917
theorem B6243481 : Blo 2309435 6243481 := bstep (se 2 (by rfl) ⟨2341305, by rfl⟩ : syracuseStep 6243481 = 4682611) B4682611
theorem B8324641 : Blo 2309435 8324641 := bstep (se 2 (by rfl) ⟨3121740, by rfl⟩ : syracuseStep 8324641 = 6243481) B6243481
theorem B11099521 : Blo 2309435 11099521 := bstep (se 2 (by rfl) ⟨4162320, by rfl⟩ : syracuseStep 11099521 = 8324641) B8324641
theorem B14799361 : Blo 2309435 14799361 := bstep (se 2 (by rfl) ⟨5549760, by rfl⟩ : syracuseStep 14799361 = 11099521) B11099521
theorem B19732481 : Blo 2309435 19732481 := bstep (se 2 (by rfl) ⟨7399680, by rfl⟩ : syracuseStep 19732481 = 14799361) B14799361
theorem B13154987 : Blo 2309435 13154987 := bstep (se 1 (by rfl) ⟨9866240, by rfl⟩ : syracuseStep 13154987 = 19732481) B19732481
theorem B8769991 : Blo 2309435 8769991 := bstep (se 1 (by rfl) ⟨6577493, by rfl⟩ : syracuseStep 8769991 = 13154987) B13154987
theorem B11693321 : Blo 2309435 11693321 := bstep (se 2 (by rfl) ⟨4384995, by rfl⟩ : syracuseStep 11693321 = 8769991) B8769991
theorem B7795547 : Blo 2309435 7795547 := bstep (se 1 (by rfl) ⟨5846660, by rfl⟩ : syracuseStep 7795547 = 11693321) B11693321
theorem B5197031 : Blo 2309435 5197031 := bstep (se 1 (by rfl) ⟨3897773, by rfl⟩ : syracuseStep 5197031 = 7795547) B7795547
theorem B3464687 : Blo 2309435 3464687 := bstep (se 1 (by rfl) ⟨2598515, by rfl⟩ : syracuseStep 3464687 = 5197031) B5197031
theorem B2309791 : Blo 2309435 2309791 := bstep (se 1 (by rfl) ⟨1732343, by rfl⟩ : syracuseStep 2309791 = 3464687) B3464687
theorem B3464693 : Blo 2309435 3464693 := bbase (se 5 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 3464693 = 324815) (by norm_num)
theorem B2309795 : Blo 2309435 2309795 := bstep (se 1 (by rfl) ⟨1732346, by rfl⟩ : syracuseStep 2309795 = 3464693) B3464693
theorem B2466569 : Blo 2309435 2466569 := bbase (se 2 (by rfl) ⟨924963, by rfl⟩ : syracuseStep 2466569 = 1849927) (by norm_num)
theorem B6577517 : Blo 2309435 6577517 := bstep (se 3 (by rfl) ⟨1233284, by rfl⟩ : syracuseStep 6577517 = 2466569) B2466569
theorem B4385011 : Blo 2309435 4385011 := bstep (se 1 (by rfl) ⟨3288758, by rfl⟩ : syracuseStep 4385011 = 6577517) B6577517
theorem B5846681 : Blo 2309435 5846681 := bstep (se 2 (by rfl) ⟨2192505, by rfl⟩ : syracuseStep 5846681 = 4385011) B4385011
theorem B3897787 : Blo 2309435 3897787 := bstep (se 1 (by rfl) ⟨2923340, by rfl⟩ : syracuseStep 3897787 = 5846681) B5846681
theorem B5197049 : Blo 2309435 5197049 := bstep (se 2 (by rfl) ⟨1948893, by rfl⟩ : syracuseStep 5197049 = 3897787) B3897787
theorem B3464699 : Blo 2309435 3464699 := bstep (se 1 (by rfl) ⟨2598524, by rfl⟩ : syracuseStep 3464699 = 5197049) B5197049
theorem B2309799 : Blo 2309435 2309799 := bstep (se 1 (by rfl) ⟨1732349, by rfl⟩ : syracuseStep 2309799 = 3464699) B3464699
theorem B2598529 : Blo 2309435 2598529 := bbase (se 2 (by rfl) ⟨974448, by rfl⟩ : syracuseStep 2598529 = 1948897) (by norm_num)
theorem B3464705 : Blo 2309435 3464705 := bstep (se 2 (by rfl) ⟨1299264, by rfl⟩ : syracuseStep 3464705 = 2598529) B2598529
theorem B2309803 : Blo 2309435 2309803 := bstep (se 1 (by rfl) ⟨1732352, by rfl⟩ : syracuseStep 2309803 = 3464705) B3464705
theorem B5846701 : Blo 2309435 5846701 := bbase (se 3 (by rfl) ⟨1096256, by rfl⟩ : syracuseStep 5846701 = 2192513) (by norm_num)
theorem B7795601 : Blo 2309435 7795601 := bstep (se 2 (by rfl) ⟨2923350, by rfl⟩ : syracuseStep 7795601 = 5846701) B5846701
theorem B5197067 : Blo 2309435 5197067 := bstep (se 1 (by rfl) ⟨3897800, by rfl⟩ : syracuseStep 5197067 = 7795601) B7795601
theorem B3464711 : Blo 2309435 3464711 := bstep (se 1 (by rfl) ⟨2598533, by rfl⟩ : syracuseStep 3464711 = 5197067) B5197067
theorem B2309807 : Blo 2309435 2309807 := bstep (se 1 (by rfl) ⟨1732355, by rfl⟩ : syracuseStep 2309807 = 3464711) B3464711
theorem B3464717 : Blo 2309435 3464717 := bbase (se 3 (by rfl) ⟨649634, by rfl⟩ : syracuseStep 3464717 = 1299269) (by norm_num)
theorem B2309811 : Blo 2309435 2309811 := bstep (se 1 (by rfl) ⟨1732358, by rfl⟩ : syracuseStep 2309811 = 3464717) B3464717
theorem B5197085 : Blo 2309435 5197085 := bbase (se 3 (by rfl) ⟨974453, by rfl⟩ : syracuseStep 5197085 = 1948907) (by norm_num)
theorem B3464723 : Blo 2309435 3464723 := bstep (se 1 (by rfl) ⟨2598542, by rfl⟩ : syracuseStep 3464723 = 5197085) B5197085
theorem B2309815 : Blo 2309435 2309815 := bstep (se 1 (by rfl) ⟨1732361, by rfl⟩ : syracuseStep 2309815 = 3464723) B3464723
theorem B3897821 : Blo 2309435 3897821 := bbase (se 3 (by rfl) ⟨730841, by rfl⟩ : syracuseStep 3897821 = 1461683) (by norm_num)
theorem B2598547 : Blo 2309435 2598547 := bstep (se 1 (by rfl) ⟨1948910, by rfl⟩ : syracuseStep 2598547 = 3897821) B3897821
theorem B3464729 : Blo 2309435 3464729 := bstep (se 2 (by rfl) ⟨1299273, by rfl⟩ : syracuseStep 3464729 = 2598547) B2598547
theorem B2309819 : Blo 2309435 2309819 := bstep (se 1 (by rfl) ⟨1732364, by rfl⟩ : syracuseStep 2309819 = 3464729) B3464729
theorem B5702309 : Blo 2309435 5702309 := bbase (se 4 (by rfl) ⟨534591, by rfl⟩ : syracuseStep 5702309 = 1069183) (by norm_num)
theorem B3801539 : Blo 2309435 3801539 := bstep (se 1 (by rfl) ⟨2851154, by rfl⟩ : syracuseStep 3801539 = 5702309) B5702309
theorem B10137437 : Blo 2309435 10137437 := bstep (se 3 (by rfl) ⟨1900769, by rfl⟩ : syracuseStep 10137437 = 3801539) B3801539
theorem B6758291 : Blo 2309435 6758291 := bstep (se 1 (by rfl) ⟨5068718, by rfl⟩ : syracuseStep 6758291 = 10137437) B10137437
theorem B4505527 : Blo 2309435 4505527 := bstep (se 1 (by rfl) ⟨3379145, by rfl⟩ : syracuseStep 4505527 = 6758291) B6758291
theorem B6007369 : Blo 2309435 6007369 := bstep (se 2 (by rfl) ⟨2252763, by rfl⟩ : syracuseStep 6007369 = 4505527) B4505527
theorem B512628821 : Blo 2309435 512628821 := bstep (se 8 (by rfl) ⟨3003684, by rfl⟩ : syracuseStep 512628821 = 6007369) B6007369
theorem B341752547 : Blo 2309435 341752547 := bstep (se 1 (by rfl) ⟨256314410, by rfl⟩ : syracuseStep 341752547 = 512628821) B512628821
theorem B227835031 : Blo 2309435 227835031 := bstep (se 1 (by rfl) ⟨170876273, by rfl⟩ : syracuseStep 227835031 = 341752547) B341752547
theorem B303780041 : Blo 2309435 303780041 := bstep (se 2 (by rfl) ⟨113917515, by rfl⟩ : syracuseStep 303780041 = 227835031) B227835031
theorem B202520027 : Blo 2309435 202520027 := bstep (se 1 (by rfl) ⟨151890020, by rfl⟩ : syracuseStep 202520027 = 303780041) B303780041
theorem B135013351 : Blo 2309435 135013351 := bstep (se 1 (by rfl) ⟨101260013, by rfl⟩ : syracuseStep 135013351 = 202520027) B202520027
theorem B180017801 : Blo 2309435 180017801 := bstep (se 2 (by rfl) ⟨67506675, by rfl⟩ : syracuseStep 180017801 = 135013351) B135013351
theorem B120011867 : Blo 2309435 120011867 := bstep (se 1 (by rfl) ⟨90008900, by rfl⟩ : syracuseStep 120011867 = 180017801) B180017801
theorem B80007911 : Blo 2309435 80007911 := bstep (se 1 (by rfl) ⟨60005933, by rfl⟩ : syracuseStep 80007911 = 120011867) B120011867
theorem B53338607 : Blo 2309435 53338607 := bstep (se 1 (by rfl) ⟨40003955, by rfl⟩ : syracuseStep 53338607 = 80007911) B80007911
theorem B35559071 : Blo 2309435 35559071 := bstep (se 1 (by rfl) ⟨26669303, by rfl⟩ : syracuseStep 35559071 = 53338607) B53338607
theorem B23706047 : Blo 2309435 23706047 := bstep (se 1 (by rfl) ⟨17779535, by rfl⟩ : syracuseStep 23706047 = 35559071) B35559071
theorem B63216125 : Blo 2309435 63216125 := bstep (se 3 (by rfl) ⟨11853023, by rfl⟩ : syracuseStep 63216125 = 23706047) B23706047
theorem B42144083 : Blo 2309435 42144083 := bstep (se 1 (by rfl) ⟨31608062, by rfl⟩ : syracuseStep 42144083 = 63216125) B63216125
theorem B28096055 : Blo 2309435 28096055 := bstep (se 1 (by rfl) ⟨21072041, by rfl⟩ : syracuseStep 28096055 = 42144083) B42144083
theorem B18730703 : Blo 2309435 18730703 := bstep (se 1 (by rfl) ⟨14048027, by rfl⟩ : syracuseStep 18730703 = 28096055) B28096055
theorem B12487135 : Blo 2309435 12487135 := bstep (se 1 (by rfl) ⟨9365351, by rfl⟩ : syracuseStep 12487135 = 18730703) B18730703
theorem B16649513 : Blo 2309435 16649513 := bstep (se 2 (by rfl) ⟨6243567, by rfl⟩ : syracuseStep 16649513 = 12487135) B12487135
theorem B11099675 : Blo 2309435 11099675 := bstep (se 1 (by rfl) ⟨8324756, by rfl⟩ : syracuseStep 11099675 = 16649513) B16649513
theorem B7399783 : Blo 2309435 7399783 := bstep (se 1 (by rfl) ⟨5549837, by rfl⟩ : syracuseStep 7399783 = 11099675) B11099675
theorem B9866377 : Blo 2309435 9866377 := bstep (se 2 (by rfl) ⟨3699891, by rfl⟩ : syracuseStep 9866377 = 7399783) B7399783
theorem B13155169 : Blo 2309435 13155169 := bstep (se 2 (by rfl) ⟨4933188, by rfl⟩ : syracuseStep 13155169 = 9866377) B9866377
theorem B17540225 : Blo 2309435 17540225 := bstep (se 2 (by rfl) ⟨6577584, by rfl⟩ : syracuseStep 17540225 = 13155169) B13155169
theorem B11693483 : Blo 2309435 11693483 := bstep (se 1 (by rfl) ⟨8770112, by rfl⟩ : syracuseStep 11693483 = 17540225) B17540225
theorem B7795655 : Blo 2309435 7795655 := bstep (se 1 (by rfl) ⟨5846741, by rfl⟩ : syracuseStep 7795655 = 11693483) B11693483
theorem B5197103 : Blo 2309435 5197103 := bstep (se 1 (by rfl) ⟨3897827, by rfl⟩ : syracuseStep 5197103 = 7795655) B7795655
theorem B3464735 : Blo 2309435 3464735 := bstep (se 1 (by rfl) ⟨2598551, by rfl⟩ : syracuseStep 3464735 = 5197103) B5197103
theorem B2309823 : Blo 2309435 2309823 := bstep (se 1 (by rfl) ⟨1732367, by rfl⟩ : syracuseStep 2309823 = 3464735) B3464735
theorem B3464741 : Blo 2309435 3464741 := bbase (se 4 (by rfl) ⟨324819, by rfl⟩ : syracuseStep 3464741 = 649639) (by norm_num)
theorem B2309827 : Blo 2309435 2309827 := bstep (se 1 (by rfl) ⟨1732370, by rfl⟩ : syracuseStep 2309827 = 3464741) B3464741
theorem B2923381 : Blo 2309435 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B3897841 : Blo 2309435 3897841 := bstep (se 2 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 3897841 = 2923381) B2923381
theorem B5197121 : Blo 2309435 5197121 := bstep (se 2 (by rfl) ⟨1948920, by rfl⟩ : syracuseStep 5197121 = 3897841) B3897841
theorem B3464747 : Blo 2309435 3464747 := bstep (se 1 (by rfl) ⟨2598560, by rfl⟩ : syracuseStep 3464747 = 5197121) B5197121
theorem B2309831 : Blo 2309435 2309831 := bstep (se 1 (by rfl) ⟨1732373, by rfl⟩ : syracuseStep 2309831 = 3464747) B3464747
theorem B2598565 : Blo 2309435 2598565 := bbase (se 4 (by rfl) ⟨243615, by rfl⟩ : syracuseStep 2598565 = 487231) (by norm_num)
theorem B3464753 : Blo 2309435 3464753 := bstep (se 2 (by rfl) ⟨1299282, by rfl⟩ : syracuseStep 3464753 = 2598565) B2598565
theorem B2309835 : Blo 2309435 2309835 := bstep (se 1 (by rfl) ⟨1732376, by rfl⟩ : syracuseStep 2309835 = 3464753) B3464753
theorem B57736277 : Blo 2309435 57736277 := bbase (se 8 (by rfl) ⟨338298, by rfl⟩ : syracuseStep 57736277 = 676597) (by norm_num)
theorem B38490851 : Blo 2309435 38490851 := bstep (se 1 (by rfl) ⟨28868138, by rfl⟩ : syracuseStep 38490851 = 57736277) B57736277
theorem B25660567 : Blo 2309435 25660567 := bstep (se 1 (by rfl) ⟨19245425, by rfl⟩ : syracuseStep 25660567 = 38490851) B38490851
theorem B34214089 : Blo 2309435 34214089 := bstep (se 2 (by rfl) ⟨12830283, by rfl⟩ : syracuseStep 34214089 = 25660567) B25660567
theorem B45618785 : Blo 2309435 45618785 := bstep (se 2 (by rfl) ⟨17107044, by rfl⟩ : syracuseStep 45618785 = 34214089) B34214089
theorem B30412523 : Blo 2309435 30412523 := bstep (se 1 (by rfl) ⟨22809392, by rfl⟩ : syracuseStep 30412523 = 45618785) B45618785
theorem B81100061 : Blo 2309435 81100061 := bstep (se 3 (by rfl) ⟨15206261, by rfl⟩ : syracuseStep 81100061 = 30412523) B30412523
theorem B54066707 : Blo 2309435 54066707 := bstep (se 1 (by rfl) ⟨40550030, by rfl⟩ : syracuseStep 54066707 = 81100061) B81100061
theorem B36044471 : Blo 2309435 36044471 := bstep (se 1 (by rfl) ⟨27033353, by rfl⟩ : syracuseStep 36044471 = 54066707) B54066707
theorem B96118589 : Blo 2309435 96118589 := bstep (se 3 (by rfl) ⟨18022235, by rfl⟩ : syracuseStep 96118589 = 36044471) B36044471
theorem B64079059 : Blo 2309435 64079059 := bstep (se 1 (by rfl) ⟨48059294, by rfl⟩ : syracuseStep 64079059 = 96118589) B96118589
theorem B85438745 : Blo 2309435 85438745 := bstep (se 2 (by rfl) ⟨32039529, by rfl⟩ : syracuseStep 85438745 = 64079059) B64079059
theorem B56959163 : Blo 2309435 56959163 := bstep (se 1 (by rfl) ⟨42719372, by rfl⟩ : syracuseStep 56959163 = 85438745) B85438745
theorem B37972775 : Blo 2309435 37972775 := bstep (se 1 (by rfl) ⟨28479581, by rfl⟩ : syracuseStep 37972775 = 56959163) B56959163
theorem B25315183 : Blo 2309435 25315183 := bstep (se 1 (by rfl) ⟨18986387, by rfl⟩ : syracuseStep 25315183 = 37972775) B37972775
theorem B135014309 : Blo 2309435 135014309 := bstep (se 4 (by rfl) ⟨12657591, by rfl⟩ : syracuseStep 135014309 = 25315183) B25315183
theorem B90009539 : Blo 2309435 90009539 := bstep (se 1 (by rfl) ⟨67507154, by rfl⟩ : syracuseStep 90009539 = 135014309) B135014309
theorem B60006359 : Blo 2309435 60006359 := bstep (se 1 (by rfl) ⟨45004769, by rfl⟩ : syracuseStep 60006359 = 90009539) B90009539
theorem B40004239 : Blo 2309435 40004239 := bstep (se 1 (by rfl) ⟨30003179, by rfl⟩ : syracuseStep 40004239 = 60006359) B60006359
theorem B53338985 : Blo 2309435 53338985 := bstep (se 2 (by rfl) ⟨20002119, by rfl⟩ : syracuseStep 53338985 = 40004239) B40004239
theorem B35559323 : Blo 2309435 35559323 := bstep (se 1 (by rfl) ⟨26669492, by rfl⟩ : syracuseStep 35559323 = 53338985) B53338985
theorem B23706215 : Blo 2309435 23706215 := bstep (se 1 (by rfl) ⟨17779661, by rfl⟩ : syracuseStep 23706215 = 35559323) B35559323
theorem B15804143 : Blo 2309435 15804143 := bstep (se 1 (by rfl) ⟨11853107, by rfl⟩ : syracuseStep 15804143 = 23706215) B23706215
theorem B10536095 : Blo 2309435 10536095 := bstep (se 1 (by rfl) ⟨7902071, by rfl⟩ : syracuseStep 10536095 = 15804143) B15804143
theorem B28096253 : Blo 2309435 28096253 := bstep (se 3 (by rfl) ⟨5268047, by rfl⟩ : syracuseStep 28096253 = 10536095) B10536095
theorem B18730835 : Blo 2309435 18730835 := bstep (se 1 (by rfl) ⟨14048126, by rfl⟩ : syracuseStep 18730835 = 28096253) B28096253
theorem B12487223 : Blo 2309435 12487223 := bstep (se 1 (by rfl) ⟨9365417, by rfl⟩ : syracuseStep 12487223 = 18730835) B18730835
theorem B33299261 : Blo 2309435 33299261 := bstep (se 3 (by rfl) ⟨6243611, by rfl⟩ : syracuseStep 33299261 = 12487223) B12487223
theorem B22199507 : Blo 2309435 22199507 := bstep (se 1 (by rfl) ⟨16649630, by rfl⟩ : syracuseStep 22199507 = 33299261) B33299261
theorem B14799671 : Blo 2309435 14799671 := bstep (se 1 (by rfl) ⟨11099753, by rfl⟩ : syracuseStep 14799671 = 22199507) B22199507
theorem B9866447 : Blo 2309435 9866447 := bstep (se 1 (by rfl) ⟨7399835, by rfl⟩ : syracuseStep 9866447 = 14799671) B14799671
theorem B6577631 : Blo 2309435 6577631 := bstep (se 1 (by rfl) ⟨4933223, by rfl⟩ : syracuseStep 6577631 = 9866447) B9866447
theorem B4385087 : Blo 2309435 4385087 := bstep (se 1 (by rfl) ⟨3288815, by rfl⟩ : syracuseStep 4385087 = 6577631) B6577631
theorem B2923391 : Blo 2309435 2923391 := bstep (se 1 (by rfl) ⟨2192543, by rfl⟩ : syracuseStep 2923391 = 4385087) B4385087
theorem B7795709 : Blo 2309435 7795709 := bstep (se 3 (by rfl) ⟨1461695, by rfl⟩ : syracuseStep 7795709 = 2923391) B2923391
theorem B5197139 : Blo 2309435 5197139 := bstep (se 1 (by rfl) ⟨3897854, by rfl⟩ : syracuseStep 5197139 = 7795709) B7795709
theorem B3464759 : Blo 2309435 3464759 := bstep (se 1 (by rfl) ⟨2598569, by rfl⟩ : syracuseStep 3464759 = 5197139) B5197139
theorem B2309839 : Blo 2309435 2309839 := bstep (se 1 (by rfl) ⟨1732379, by rfl⟩ : syracuseStep 2309839 = 3464759) B3464759
theorem B3464765 : Blo 2309435 3464765 := bbase (se 3 (by rfl) ⟨649643, by rfl⟩ : syracuseStep 3464765 = 1299287) (by norm_num)
theorem B2309843 : Blo 2309435 2309843 := bstep (se 1 (by rfl) ⟨1732382, by rfl⟩ : syracuseStep 2309843 = 3464765) B3464765
theorem B5197157 : Blo 2309435 5197157 := bbase (se 4 (by rfl) ⟨487233, by rfl⟩ : syracuseStep 5197157 = 974467) (by norm_num)
theorem B3464771 : Blo 2309435 3464771 := bstep (se 1 (by rfl) ⟨2598578, by rfl⟩ : syracuseStep 3464771 = 5197157) B5197157
theorem B2309847 : Blo 2309435 2309847 := bstep (se 1 (by rfl) ⟨1732385, by rfl⟩ : syracuseStep 2309847 = 3464771) B3464771
theorem B5846813 : Blo 2309435 5846813 := bbase (se 3 (by rfl) ⟨1096277, by rfl⟩ : syracuseStep 5846813 = 2192555) (by norm_num)
theorem B3897875 : Blo 2309435 3897875 := bstep (se 1 (by rfl) ⟨2923406, by rfl⟩ : syracuseStep 3897875 = 5846813) B5846813
theorem B2598583 : Blo 2309435 2598583 := bstep (se 1 (by rfl) ⟨1948937, by rfl⟩ : syracuseStep 2598583 = 3897875) B3897875
theorem B3464777 : Blo 2309435 3464777 := bstep (se 2 (by rfl) ⟨1299291, by rfl⟩ : syracuseStep 3464777 = 2598583) B2598583
theorem B2309851 : Blo 2309435 2309851 := bstep (se 1 (by rfl) ⟨1732388, by rfl⟩ : syracuseStep 2309851 = 3464777) B3464777
theorem B4385117 : Blo 2309435 4385117 := bbase (se 3 (by rfl) ⟨822209, by rfl⟩ : syracuseStep 4385117 = 1644419) (by norm_num)
theorem B11693645 : Blo 2309435 11693645 := bstep (se 3 (by rfl) ⟨2192558, by rfl⟩ : syracuseStep 11693645 = 4385117) B4385117
theorem B7795763 : Blo 2309435 7795763 := bstep (se 1 (by rfl) ⟨5846822, by rfl⟩ : syracuseStep 7795763 = 11693645) B11693645
theorem B5197175 : Blo 2309435 5197175 := bstep (se 1 (by rfl) ⟨3897881, by rfl⟩ : syracuseStep 5197175 = 7795763) B7795763
theorem B3464783 : Blo 2309435 3464783 := bstep (se 1 (by rfl) ⟨2598587, by rfl⟩ : syracuseStep 3464783 = 5197175) B5197175
theorem B2309855 : Blo 2309435 2309855 := bstep (se 1 (by rfl) ⟨1732391, by rfl⟩ : syracuseStep 2309855 = 3464783) B3464783
theorem B3464789 : Blo 2309435 3464789 := bbase (se 8 (by rfl) ⟨20301, by rfl⟩ : syracuseStep 3464789 = 40603) (by norm_num)
theorem B2309859 : Blo 2309435 2309859 := bstep (se 1 (by rfl) ⟨1732394, by rfl⟩ : syracuseStep 2309859 = 3464789) B3464789
theorem B9866549 : Blo 2309435 9866549 := bbase (se 5 (by rfl) ⟨462494, by rfl⟩ : syracuseStep 9866549 = 924989) (by norm_num)
theorem B6577699 : Blo 2309435 6577699 := bstep (se 1 (by rfl) ⟨4933274, by rfl⟩ : syracuseStep 6577699 = 9866549) B9866549
theorem B8770265 : Blo 2309435 8770265 := bstep (se 2 (by rfl) ⟨3288849, by rfl⟩ : syracuseStep 8770265 = 6577699) B6577699
theorem B5846843 : Blo 2309435 5846843 := bstep (se 1 (by rfl) ⟨4385132, by rfl⟩ : syracuseStep 5846843 = 8770265) B8770265
theorem B3897895 : Blo 2309435 3897895 := bstep (se 1 (by rfl) ⟨2923421, by rfl⟩ : syracuseStep 3897895 = 5846843) B5846843
theorem B5197193 : Blo 2309435 5197193 := bstep (se 2 (by rfl) ⟨1948947, by rfl⟩ : syracuseStep 5197193 = 3897895) B3897895
theorem B3464795 : Blo 2309435 3464795 := bstep (se 1 (by rfl) ⟨2598596, by rfl⟩ : syracuseStep 3464795 = 5197193) B5197193
theorem B2309863 : Blo 2309435 2309863 := bstep (se 1 (by rfl) ⟨1732397, by rfl⟩ : syracuseStep 2309863 = 3464795) B3464795
theorem B2598601 : Blo 2309435 2598601 := bbase (se 2 (by rfl) ⟨974475, by rfl⟩ : syracuseStep 2598601 = 1948951) (by norm_num)
theorem B3464801 : Blo 2309435 3464801 := bstep (se 2 (by rfl) ⟨1299300, by rfl⟩ : syracuseStep 3464801 = 2598601) B2598601
theorem B2309867 : Blo 2309435 2309867 := bstep (se 1 (by rfl) ⟨1732400, by rfl⟩ : syracuseStep 2309867 = 3464801) B3464801
theorem B2634061 : Blo 2309435 2634061 := bbase (se 3 (by rfl) ⟨493886, by rfl⟩ : syracuseStep 2634061 = 987773) (by norm_num)
theorem B3512081 : Blo 2309435 3512081 := bstep (se 2 (by rfl) ⟨1317030, by rfl⟩ : syracuseStep 3512081 = 2634061) B2634061
theorem B2341387 : Blo 2309435 2341387 := bstep (se 1 (by rfl) ⟨1756040, by rfl⟩ : syracuseStep 2341387 = 3512081) B3512081
theorem B3121849 : Blo 2309435 3121849 := bstep (se 2 (by rfl) ⟨1170693, by rfl⟩ : syracuseStep 3121849 = 2341387) B2341387
theorem B4162465 : Blo 2309435 4162465 := bstep (se 2 (by rfl) ⟨1560924, by rfl⟩ : syracuseStep 4162465 = 3121849) B3121849
theorem B5549953 : Blo 2309435 5549953 := bstep (se 2 (by rfl) ⟨2081232, by rfl⟩ : syracuseStep 5549953 = 4162465) B4162465
theorem B7399937 : Blo 2309435 7399937 := bstep (se 2 (by rfl) ⟨2774976, by rfl⟩ : syracuseStep 7399937 = 5549953) B5549953
theorem B19733165 : Blo 2309435 19733165 := bstep (se 3 (by rfl) ⟨3699968, by rfl⟩ : syracuseStep 19733165 = 7399937) B7399937
theorem B13155443 : Blo 2309435 13155443 := bstep (se 1 (by rfl) ⟨9866582, by rfl⟩ : syracuseStep 13155443 = 19733165) B19733165
theorem B8770295 : Blo 2309435 8770295 := bstep (se 1 (by rfl) ⟨6577721, by rfl⟩ : syracuseStep 8770295 = 13155443) B13155443
theorem B5846863 : Blo 2309435 5846863 := bstep (se 1 (by rfl) ⟨4385147, by rfl⟩ : syracuseStep 5846863 = 8770295) B8770295
theorem B7795817 : Blo 2309435 7795817 := bstep (se 2 (by rfl) ⟨2923431, by rfl⟩ : syracuseStep 7795817 = 5846863) B5846863
theorem B5197211 : Blo 2309435 5197211 := bstep (se 1 (by rfl) ⟨3897908, by rfl⟩ : syracuseStep 5197211 = 7795817) B7795817
theorem B3464807 : Blo 2309435 3464807 := bstep (se 1 (by rfl) ⟨2598605, by rfl⟩ : syracuseStep 3464807 = 5197211) B5197211
theorem B2309871 : Blo 2309435 2309871 := bstep (se 1 (by rfl) ⟨1732403, by rfl⟩ : syracuseStep 2309871 = 3464807) B3464807
theorem B3464813 : Blo 2309435 3464813 := bbase (se 3 (by rfl) ⟨649652, by rfl⟩ : syracuseStep 3464813 = 1299305) (by norm_num)
theorem B2309875 : Blo 2309435 2309875 := bstep (se 1 (by rfl) ⟨1732406, by rfl⟩ : syracuseStep 2309875 = 3464813) B3464813
theorem B5197229 : Blo 2309435 5197229 := bbase (se 3 (by rfl) ⟨974480, by rfl⟩ : syracuseStep 5197229 = 1948961) (by norm_num)
theorem B3464819 : Blo 2309435 3464819 := bstep (se 1 (by rfl) ⟨2598614, by rfl⟩ : syracuseStep 3464819 = 5197229) B5197229
theorem B2309879 : Blo 2309435 2309879 := bstep (se 1 (by rfl) ⟨1732409, by rfl⟩ : syracuseStep 2309879 = 3464819) B3464819
theorem B3699989 : Blo 2309435 3699989 := bbase (se 6 (by rfl) ⟨86718, by rfl⟩ : syracuseStep 3699989 = 173437) (by norm_num)
theorem B2466659 : Blo 2309435 2466659 := bstep (se 1 (by rfl) ⟨1849994, by rfl⟩ : syracuseStep 2466659 = 3699989) B3699989
theorem B6577757 : Blo 2309435 6577757 := bstep (se 3 (by rfl) ⟨1233329, by rfl⟩ : syracuseStep 6577757 = 2466659) B2466659
theorem B4385171 : Blo 2309435 4385171 := bstep (se 1 (by rfl) ⟨3288878, by rfl⟩ : syracuseStep 4385171 = 6577757) B6577757
theorem B2923447 : Blo 2309435 2923447 := bstep (se 1 (by rfl) ⟨2192585, by rfl⟩ : syracuseStep 2923447 = 4385171) B4385171
theorem B3897929 : Blo 2309435 3897929 := bstep (se 2 (by rfl) ⟨1461723, by rfl⟩ : syracuseStep 3897929 = 2923447) B2923447
theorem B2598619 : Blo 2309435 2598619 := bstep (se 1 (by rfl) ⟨1948964, by rfl⟩ : syracuseStep 2598619 = 3897929) B3897929
theorem B3464825 : Blo 2309435 3464825 := bstep (se 2 (by rfl) ⟨1299309, by rfl⟩ : syracuseStep 3464825 = 2598619) B2598619
theorem B2309883 : Blo 2309435 2309883 := bstep (se 1 (by rfl) ⟨1732412, by rfl⟩ : syracuseStep 2309883 = 3464825) B3464825
theorem B2743369 : Blo 2309435 2743369 := bbase (se 2 (by rfl) ⟨1028763, by rfl⟩ : syracuseStep 2743369 = 2057527) (by norm_num)
theorem B14631301 : Blo 2309435 14631301 := bstep (se 4 (by rfl) ⟨1371684, by rfl⟩ : syracuseStep 14631301 = 2743369) B2743369
theorem B19508401 : Blo 2309435 19508401 := bstep (se 2 (by rfl) ⟨7315650, by rfl⟩ : syracuseStep 19508401 = 14631301) B14631301
theorem B26011201 : Blo 2309435 26011201 := bstep (se 2 (by rfl) ⟨9754200, by rfl⟩ : syracuseStep 26011201 = 19508401) B19508401
theorem B34681601 : Blo 2309435 34681601 := bstep (se 2 (by rfl) ⟨13005600, by rfl⟩ : syracuseStep 34681601 = 26011201) B26011201
theorem B23121067 : Blo 2309435 23121067 := bstep (se 1 (by rfl) ⟨17340800, by rfl⟩ : syracuseStep 23121067 = 34681601) B34681601
theorem B30828089 : Blo 2309435 30828089 := bstep (se 2 (by rfl) ⟨11560533, by rfl⟩ : syracuseStep 30828089 = 23121067) B23121067
theorem B20552059 : Blo 2309435 20552059 := bstep (se 1 (by rfl) ⟨15414044, by rfl⟩ : syracuseStep 20552059 = 30828089) B30828089
theorem B109610981 : Blo 2309435 109610981 := bstep (se 4 (by rfl) ⟨10276029, by rfl⟩ : syracuseStep 109610981 = 20552059) B20552059
theorem B73073987 : Blo 2309435 73073987 := bstep (se 1 (by rfl) ⟨54805490, by rfl⟩ : syracuseStep 73073987 = 109610981) B109610981
theorem B48715991 : Blo 2309435 48715991 := bstep (se 1 (by rfl) ⟨36536993, by rfl⟩ : syracuseStep 48715991 = 73073987) B73073987
theorem B32477327 : Blo 2309435 32477327 := bstep (se 1 (by rfl) ⟨24357995, by rfl⟩ : syracuseStep 32477327 = 48715991) B48715991
theorem B21651551 : Blo 2309435 21651551 := bstep (se 1 (by rfl) ⟨16238663, by rfl⟩ : syracuseStep 21651551 = 32477327) B32477327
theorem B14434367 : Blo 2309435 14434367 := bstep (se 1 (by rfl) ⟨10825775, by rfl⟩ : syracuseStep 14434367 = 21651551) B21651551
theorem B38491645 : Blo 2309435 38491645 := bstep (se 3 (by rfl) ⟨7217183, by rfl⟩ : syracuseStep 38491645 = 14434367) B14434367
theorem B51322193 : Blo 2309435 51322193 := bstep (se 2 (by rfl) ⟨19245822, by rfl⟩ : syracuseStep 51322193 = 38491645) B38491645
theorem B34214795 : Blo 2309435 34214795 := bstep (se 1 (by rfl) ⟨25661096, by rfl⟩ : syracuseStep 34214795 = 51322193) B51322193
theorem B22809863 : Blo 2309435 22809863 := bstep (se 1 (by rfl) ⟨17107397, by rfl⟩ : syracuseStep 22809863 = 34214795) B34214795
theorem B60826301 : Blo 2309435 60826301 := bstep (se 3 (by rfl) ⟨11404931, by rfl⟩ : syracuseStep 60826301 = 22809863) B22809863
theorem B40550867 : Blo 2309435 40550867 := bstep (se 1 (by rfl) ⟨30413150, by rfl⟩ : syracuseStep 40550867 = 60826301) B60826301
theorem B27033911 : Blo 2309435 27033911 := bstep (se 1 (by rfl) ⟨20275433, by rfl⟩ : syracuseStep 27033911 = 40550867) B40550867
theorem B18022607 : Blo 2309435 18022607 := bstep (se 1 (by rfl) ⟨13516955, by rfl⟩ : syracuseStep 18022607 = 27033911) B27033911
theorem B12015071 : Blo 2309435 12015071 := bstep (se 1 (by rfl) ⟨9011303, by rfl⟩ : syracuseStep 12015071 = 18022607) B18022607
theorem B8010047 : Blo 2309435 8010047 := bstep (se 1 (by rfl) ⟨6007535, by rfl⟩ : syracuseStep 8010047 = 12015071) B12015071
theorem B21360125 : Blo 2309435 21360125 := bstep (se 3 (by rfl) ⟨4005023, by rfl⟩ : syracuseStep 21360125 = 8010047) B8010047
theorem B56960333 : Blo 2309435 56960333 := bstep (se 3 (by rfl) ⟨10680062, by rfl⟩ : syracuseStep 56960333 = 21360125) B21360125
theorem B37973555 : Blo 2309435 37973555 := bstep (se 1 (by rfl) ⟨28480166, by rfl⟩ : syracuseStep 37973555 = 56960333) B56960333
theorem B25315703 : Blo 2309435 25315703 := bstep (se 1 (by rfl) ⟨18986777, by rfl⟩ : syracuseStep 25315703 = 37973555) B37973555
theorem B16877135 : Blo 2309435 16877135 := bstep (se 1 (by rfl) ⟨12657851, by rfl⟩ : syracuseStep 16877135 = 25315703) B25315703
theorem B11251423 : Blo 2309435 11251423 := bstep (se 1 (by rfl) ⟨8438567, by rfl⟩ : syracuseStep 11251423 = 16877135) B16877135
theorem B15001897 : Blo 2309435 15001897 := bstep (se 2 (by rfl) ⟨5625711, by rfl⟩ : syracuseStep 15001897 = 11251423) B11251423
theorem B20002529 : Blo 2309435 20002529 := bstep (se 2 (by rfl) ⟨7500948, by rfl⟩ : syracuseStep 20002529 = 15001897) B15001897
theorem B13335019 : Blo 2309435 13335019 := bstep (se 1 (by rfl) ⟨10001264, by rfl⟩ : syracuseStep 13335019 = 20002529) B20002529
theorem B71120101 : Blo 2309435 71120101 := bstep (se 4 (by rfl) ⟨6667509, by rfl⟩ : syracuseStep 71120101 = 13335019) B13335019
theorem B94826801 : Blo 2309435 94826801 := bstep (se 2 (by rfl) ⟨35560050, by rfl⟩ : syracuseStep 94826801 = 71120101) B71120101
theorem B63217867 : Blo 2309435 63217867 := bstep (se 1 (by rfl) ⟨47413400, by rfl⟩ : syracuseStep 63217867 = 94826801) B94826801
theorem B84290489 : Blo 2309435 84290489 := bstep (se 2 (by rfl) ⟨31608933, by rfl⟩ : syracuseStep 84290489 = 63217867) B63217867
theorem B56193659 : Blo 2309435 56193659 := bstep (se 1 (by rfl) ⟨42145244, by rfl⟩ : syracuseStep 56193659 = 84290489) B84290489
theorem B37462439 : Blo 2309435 37462439 := bstep (se 1 (by rfl) ⟨28096829, by rfl⟩ : syracuseStep 37462439 = 56193659) B56193659
theorem B99899837 : Blo 2309435 99899837 := bstep (se 3 (by rfl) ⟨18731219, by rfl⟩ : syracuseStep 99899837 = 37462439) B37462439
theorem B66599891 : Blo 2309435 66599891 := bstep (se 1 (by rfl) ⟨49949918, by rfl⟩ : syracuseStep 66599891 = 99899837) B99899837
theorem B44399927 : Blo 2309435 44399927 := bstep (se 1 (by rfl) ⟨33299945, by rfl⟩ : syracuseStep 44399927 = 66599891) B66599891
theorem B29599951 : Blo 2309435 29599951 := bstep (se 1 (by rfl) ⟨22199963, by rfl⟩ : syracuseStep 29599951 = 44399927) B44399927
theorem B39466601 : Blo 2309435 39466601 := bstep (se 2 (by rfl) ⟨14799975, by rfl⟩ : syracuseStep 39466601 = 29599951) B29599951
theorem B26311067 : Blo 2309435 26311067 := bstep (se 1 (by rfl) ⟨19733300, by rfl⟩ : syracuseStep 26311067 = 39466601) B39466601
theorem B17540711 : Blo 2309435 17540711 := bstep (se 1 (by rfl) ⟨13155533, by rfl⟩ : syracuseStep 17540711 = 26311067) B26311067
theorem B11693807 : Blo 2309435 11693807 := bstep (se 1 (by rfl) ⟨8770355, by rfl⟩ : syracuseStep 11693807 = 17540711) B17540711
theorem B7795871 : Blo 2309435 7795871 := bstep (se 1 (by rfl) ⟨5846903, by rfl⟩ : syracuseStep 7795871 = 11693807) B11693807
theorem B5197247 : Blo 2309435 5197247 := bstep (se 1 (by rfl) ⟨3897935, by rfl⟩ : syracuseStep 5197247 = 7795871) B7795871
theorem B3464831 : Blo 2309435 3464831 := bstep (se 1 (by rfl) ⟨2598623, by rfl⟩ : syracuseStep 3464831 = 5197247) B5197247
theorem B2309887 : Blo 2309435 2309887 := bstep (se 1 (by rfl) ⟨1732415, by rfl⟩ : syracuseStep 2309887 = 3464831) B3464831
theorem B3464837 : Blo 2309435 3464837 := bbase (se 4 (by rfl) ⟨324828, by rfl⟩ : syracuseStep 3464837 = 649657) (by norm_num)
theorem B2309891 : Blo 2309435 2309891 := bstep (se 1 (by rfl) ⟨1732418, by rfl⟩ : syracuseStep 2309891 = 3464837) B3464837
theorem B3897949 : Blo 2309435 3897949 := bbase (se 3 (by rfl) ⟨730865, by rfl⟩ : syracuseStep 3897949 = 1461731) (by norm_num)
theorem B5197265 : Blo 2309435 5197265 := bstep (se 2 (by rfl) ⟨1948974, by rfl⟩ : syracuseStep 5197265 = 3897949) B3897949
theorem B3464843 : Blo 2309435 3464843 := bstep (se 1 (by rfl) ⟨2598632, by rfl⟩ : syracuseStep 3464843 = 5197265) B5197265
theorem B2309895 : Blo 2309435 2309895 := bstep (se 1 (by rfl) ⟨1732421, by rfl⟩ : syracuseStep 2309895 = 3464843) B3464843
theorem B2598637 : Blo 2309435 2598637 := bbase (se 3 (by rfl) ⟨487244, by rfl⟩ : syracuseStep 2598637 = 974489) (by norm_num)
theorem B3464849 : Blo 2309435 3464849 := bstep (se 2 (by rfl) ⟨1299318, by rfl⟩ : syracuseStep 3464849 = 2598637) B2598637
theorem B2309899 : Blo 2309435 2309899 := bstep (se 1 (by rfl) ⟨1732424, by rfl⟩ : syracuseStep 2309899 = 3464849) B3464849
theorem B7795925 : Blo 2309435 7795925 := bbase (se 7 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 7795925 = 182717) (by norm_num)
theorem B5197283 : Blo 2309435 5197283 := bstep (se 1 (by rfl) ⟨3897962, by rfl⟩ : syracuseStep 5197283 = 7795925) B7795925
theorem B3464855 : Blo 2309435 3464855 := bstep (se 1 (by rfl) ⟨2598641, by rfl⟩ : syracuseStep 3464855 = 5197283) B5197283
theorem B2309903 : Blo 2309435 2309903 := bstep (se 1 (by rfl) ⟨1732427, by rfl⟩ : syracuseStep 2309903 = 3464855) B3464855
theorem B3464861 : Blo 2309435 3464861 := bbase (se 3 (by rfl) ⟨649661, by rfl⟩ : syracuseStep 3464861 = 1299323) (by norm_num)
theorem B2309907 : Blo 2309435 2309907 := bstep (se 1 (by rfl) ⟨1732430, by rfl⟩ : syracuseStep 2309907 = 3464861) B3464861
theorem B5197301 : Blo 2309435 5197301 := bbase (se 5 (by rfl) ⟨243623, by rfl⟩ : syracuseStep 5197301 = 487247) (by norm_num)
theorem B3464867 : Blo 2309435 3464867 := bstep (se 1 (by rfl) ⟨2598650, by rfl⟩ : syracuseStep 3464867 = 5197301) B5197301
theorem B2309911 : Blo 2309435 2309911 := bstep (se 1 (by rfl) ⟨1732433, by rfl⟩ : syracuseStep 2309911 = 3464867) B3464867
theorem B5268221 : Blo 2309435 5268221 := bbase (se 3 (by rfl) ⟨987791, by rfl⟩ : syracuseStep 5268221 = 1975583) (by norm_num)
theorem B3512147 : Blo 2309435 3512147 := bstep (se 1 (by rfl) ⟨2634110, by rfl⟩ : syracuseStep 3512147 = 5268221) B5268221
theorem B9365725 : Blo 2309435 9365725 := bstep (se 3 (by rfl) ⟨1756073, by rfl⟩ : syracuseStep 9365725 = 3512147) B3512147
theorem B49950533 : Blo 2309435 49950533 := bstep (se 4 (by rfl) ⟨4682862, by rfl⟩ : syracuseStep 49950533 = 9365725) B9365725
theorem B33300355 : Blo 2309435 33300355 := bstep (se 1 (by rfl) ⟨24975266, by rfl⟩ : syracuseStep 33300355 = 49950533) B49950533
theorem B44400473 : Blo 2309435 44400473 := bstep (se 2 (by rfl) ⟨16650177, by rfl⟩ : syracuseStep 44400473 = 33300355) B33300355
theorem B29600315 : Blo 2309435 29600315 := bstep (se 1 (by rfl) ⟨22200236, by rfl⟩ : syracuseStep 29600315 = 44400473) B44400473
theorem B19733543 : Blo 2309435 19733543 := bstep (se 1 (by rfl) ⟨14800157, by rfl⟩ : syracuseStep 19733543 = 29600315) B29600315
theorem B13155695 : Blo 2309435 13155695 := bstep (se 1 (by rfl) ⟨9866771, by rfl⟩ : syracuseStep 13155695 = 19733543) B19733543
theorem B8770463 : Blo 2309435 8770463 := bstep (se 1 (by rfl) ⟨6577847, by rfl⟩ : syracuseStep 8770463 = 13155695) B13155695
theorem B5846975 : Blo 2309435 5846975 := bstep (se 1 (by rfl) ⟨4385231, by rfl⟩ : syracuseStep 5846975 = 8770463) B8770463
theorem B3897983 : Blo 2309435 3897983 := bstep (se 1 (by rfl) ⟨2923487, by rfl⟩ : syracuseStep 3897983 = 5846975) B5846975
theorem B2598655 : Blo 2309435 2598655 := bstep (se 1 (by rfl) ⟨1948991, by rfl⟩ : syracuseStep 2598655 = 3897983) B3897983
theorem B3464873 : Blo 2309435 3464873 := bstep (se 2 (by rfl) ⟨1299327, by rfl⟩ : syracuseStep 3464873 = 2598655) B2598655
theorem B2309915 : Blo 2309435 2309915 := bstep (se 1 (by rfl) ⟨1732436, by rfl⟩ : syracuseStep 2309915 = 3464873) B3464873
theorem B2466697 : Blo 2309435 2466697 := bbase (se 2 (by rfl) ⟨925011, by rfl⟩ : syracuseStep 2466697 = 1850023) (by norm_num)
theorem B3288929 : Blo 2309435 3288929 := bstep (se 2 (by rfl) ⟨1233348, by rfl⟩ : syracuseStep 3288929 = 2466697) B2466697
theorem B8770477 : Blo 2309435 8770477 := bstep (se 3 (by rfl) ⟨1644464, by rfl⟩ : syracuseStep 8770477 = 3288929) B3288929
theorem B11693969 : Blo 2309435 11693969 := bstep (se 2 (by rfl) ⟨4385238, by rfl⟩ : syracuseStep 11693969 = 8770477) B8770477
theorem B7795979 : Blo 2309435 7795979 := bstep (se 1 (by rfl) ⟨5846984, by rfl⟩ : syracuseStep 7795979 = 11693969) B11693969
theorem B5197319 : Blo 2309435 5197319 := bstep (se 1 (by rfl) ⟨3897989, by rfl⟩ : syracuseStep 5197319 = 7795979) B7795979
theorem B3464879 : Blo 2309435 3464879 := bstep (se 1 (by rfl) ⟨2598659, by rfl⟩ : syracuseStep 3464879 = 5197319) B5197319
theorem B2309919 : Blo 2309435 2309919 := bstep (se 1 (by rfl) ⟨1732439, by rfl⟩ : syracuseStep 2309919 = 3464879) B3464879
theorem B3464885 : Blo 2309435 3464885 := bbase (se 5 (by rfl) ⟨162416, by rfl⟩ : syracuseStep 3464885 = 324833) (by norm_num)
theorem B2309923 : Blo 2309435 2309923 := bstep (se 1 (by rfl) ⟨1732442, by rfl⟩ : syracuseStep 2309923 = 3464885) B3464885
theorem B5847005 : Blo 2309435 5847005 := bbase (se 3 (by rfl) ⟨1096313, by rfl⟩ : syracuseStep 5847005 = 2192627) (by norm_num)
theorem B3898003 : Blo 2309435 3898003 := bstep (se 1 (by rfl) ⟨2923502, by rfl⟩ : syracuseStep 3898003 = 5847005) B5847005
theorem B5197337 : Blo 2309435 5197337 := bstep (se 2 (by rfl) ⟨1949001, by rfl⟩ : syracuseStep 5197337 = 3898003) B3898003
theorem B3464891 : Blo 2309435 3464891 := bstep (se 1 (by rfl) ⟨2598668, by rfl⟩ : syracuseStep 3464891 = 5197337) B5197337
theorem B2309927 : Blo 2309435 2309927 := bstep (se 1 (by rfl) ⟨1732445, by rfl⟩ : syracuseStep 2309927 = 3464891) B3464891
theorem B2598673 : Blo 2309435 2598673 := bbase (se 2 (by rfl) ⟨974502, by rfl⟩ : syracuseStep 2598673 = 1949005) (by norm_num)
theorem B3464897 : Blo 2309435 3464897 := bstep (se 2 (by rfl) ⟨1299336, by rfl⟩ : syracuseStep 3464897 = 2598673) B2598673
theorem B2309931 : Blo 2309435 2309931 := bstep (se 1 (by rfl) ⟨1732448, by rfl⟩ : syracuseStep 2309931 = 3464897) B3464897
theorem B4385269 : Blo 2309435 4385269 := bbase (se 5 (by rfl) ⟨205559, by rfl⟩ : syracuseStep 4385269 = 411119) (by norm_num)
theorem B5847025 : Blo 2309435 5847025 := bstep (se 2 (by rfl) ⟨2192634, by rfl⟩ : syracuseStep 5847025 = 4385269) B4385269
theorem B7796033 : Blo 2309435 7796033 := bstep (se 2 (by rfl) ⟨2923512, by rfl⟩ : syracuseStep 7796033 = 5847025) B5847025
theorem B5197355 : Blo 2309435 5197355 := bstep (se 1 (by rfl) ⟨3898016, by rfl⟩ : syracuseStep 5197355 = 7796033) B7796033
theorem B3464903 : Blo 2309435 3464903 := bstep (se 1 (by rfl) ⟨2598677, by rfl⟩ : syracuseStep 3464903 = 5197355) B5197355
theorem B2309935 : Blo 2309435 2309935 := bstep (se 1 (by rfl) ⟨1732451, by rfl⟩ : syracuseStep 2309935 = 3464903) B3464903
theorem B3464909 : Blo 2309435 3464909 := bbase (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) (by norm_num)
theorem B2309939 : Blo 2309435 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B5197373 : Blo 2309435 5197373 := bbase (se 3 (by rfl) ⟨974507, by rfl⟩ : syracuseStep 5197373 = 1949015) (by norm_num)
theorem B3464915 : Blo 2309435 3464915 := bstep (se 1 (by rfl) ⟨2598686, by rfl⟩ : syracuseStep 3464915 = 5197373) B5197373
theorem B2309943 : Blo 2309435 2309943 := bstep (se 1 (by rfl) ⟨1732457, by rfl⟩ : syracuseStep 2309943 = 3464915) B3464915
theorem B3898037 : Blo 2309435 3898037 := bbase (se 5 (by rfl) ⟨182720, by rfl⟩ : syracuseStep 3898037 = 365441) (by norm_num)
theorem B2598691 : Blo 2309435 2598691 := bstep (se 1 (by rfl) ⟨1949018, by rfl⟩ : syracuseStep 2598691 = 3898037) B3898037
theorem B3464921 : Blo 2309435 3464921 := bstep (se 2 (by rfl) ⟨1299345, by rfl⟩ : syracuseStep 3464921 = 2598691) B2598691
theorem B2309947 : Blo 2309435 2309947 := bstep (se 1 (by rfl) ⟨1732460, by rfl⟩ : syracuseStep 2309947 = 3464921) B3464921
theorem B2775073 : Blo 2309435 2775073 := bbase (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) (by norm_num)
theorem B3700097 : Blo 2309435 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B2466731 : Blo 2309435 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B6577949 : Blo 2309435 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B17541197 : Blo 2309435 17541197 := bstep (se 3 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 17541197 = 6577949) B6577949
theorem B11694131 : Blo 2309435 11694131 := bstep (se 1 (by rfl) ⟨8770598, by rfl⟩ : syracuseStep 11694131 = 17541197) B17541197
theorem B7796087 : Blo 2309435 7796087 := bstep (se 1 (by rfl) ⟨5847065, by rfl⟩ : syracuseStep 7796087 = 11694131) B11694131
theorem B5197391 : Blo 2309435 5197391 := bstep (se 1 (by rfl) ⟨3898043, by rfl⟩ : syracuseStep 5197391 = 7796087) B7796087
theorem B3464927 : Blo 2309435 3464927 := bstep (se 1 (by rfl) ⟨2598695, by rfl⟩ : syracuseStep 3464927 = 5197391) B5197391
theorem B2309951 : Blo 2309435 2309951 := bstep (se 1 (by rfl) ⟨1732463, by rfl⟩ : syracuseStep 2309951 = 3464927) B3464927
theorem B3464933 : Blo 2309435 3464933 := bbase (se 4 (by rfl) ⟨324837, by rfl⟩ : syracuseStep 3464933 = 649675) (by norm_num)
theorem B2309955 : Blo 2309435 2309955 := bstep (se 1 (by rfl) ⟨1732466, by rfl⟩ : syracuseStep 2309955 = 3464933) B3464933
theorem B6577973 : Blo 2309435 6577973 := bbase (se 5 (by rfl) ⟨308342, by rfl⟩ : syracuseStep 6577973 = 616685) (by norm_num)
theorem B4385315 : Blo 2309435 4385315 := bstep (se 1 (by rfl) ⟨3288986, by rfl⟩ : syracuseStep 4385315 = 6577973) B6577973
theorem B2923543 : Blo 2309435 2923543 := bstep (se 1 (by rfl) ⟨2192657, by rfl⟩ : syracuseStep 2923543 = 4385315) B4385315
theorem B3898057 : Blo 2309435 3898057 := bstep (se 2 (by rfl) ⟨1461771, by rfl⟩ : syracuseStep 3898057 = 2923543) B2923543
theorem B5197409 : Blo 2309435 5197409 := bstep (se 2 (by rfl) ⟨1949028, by rfl⟩ : syracuseStep 5197409 = 3898057) B3898057
theorem B3464939 : Blo 2309435 3464939 := bstep (se 1 (by rfl) ⟨2598704, by rfl⟩ : syracuseStep 3464939 = 5197409) B5197409
theorem B2309959 : Blo 2309435 2309959 := bstep (se 1 (by rfl) ⟨1732469, by rfl⟩ : syracuseStep 2309959 = 3464939) B3464939
theorem B2598709 : Blo 2309435 2598709 := bbase (se 5 (by rfl) ⟨121814, by rfl⟩ : syracuseStep 2598709 = 243629) (by norm_num)
theorem B3464945 : Blo 2309435 3464945 := bstep (se 2 (by rfl) ⟨1299354, by rfl⟩ : syracuseStep 3464945 = 2598709) B2598709
theorem B2309963 : Blo 2309435 2309963 := bstep (se 1 (by rfl) ⟨1732472, by rfl⟩ : syracuseStep 2309963 = 3464945) B3464945
theorem B2923553 : Blo 2309435 2923553 := bbase (se 2 (by rfl) ⟨1096332, by rfl⟩ : syracuseStep 2923553 = 2192665) (by norm_num)
theorem B7796141 : Blo 2309435 7796141 := bstep (se 3 (by rfl) ⟨1461776, by rfl⟩ : syracuseStep 7796141 = 2923553) B2923553
theorem B5197427 : Blo 2309435 5197427 := bstep (se 1 (by rfl) ⟨3898070, by rfl⟩ : syracuseStep 5197427 = 7796141) B7796141
theorem B3464951 : Blo 2309435 3464951 := bstep (se 1 (by rfl) ⟨2598713, by rfl⟩ : syracuseStep 3464951 = 5197427) B5197427
theorem B2309967 : Blo 2309435 2309967 := bstep (se 1 (by rfl) ⟨1732475, by rfl⟩ : syracuseStep 2309967 = 3464951) B3464951
theorem B3464957 : Blo 2309435 3464957 := bbase (se 3 (by rfl) ⟨649679, by rfl⟩ : syracuseStep 3464957 = 1299359) (by norm_num)
theorem B2309971 : Blo 2309435 2309971 := bstep (se 1 (by rfl) ⟨1732478, by rfl⟩ : syracuseStep 2309971 = 3464957) B3464957
theorem B5197445 : Blo 2309435 5197445 := bbase (se 4 (by rfl) ⟨487260, by rfl⟩ : syracuseStep 5197445 = 974521) (by norm_num)
theorem B3464963 : Blo 2309435 3464963 := bstep (se 1 (by rfl) ⟨2598722, by rfl⟩ : syracuseStep 3464963 = 5197445) B5197445
theorem B2309975 : Blo 2309435 2309975 := bstep (se 1 (by rfl) ⟨1732481, by rfl⟩ : syracuseStep 2309975 = 3464963) B3464963
theorem B4162661 : Blo 2309435 4162661 := bbase (se 4 (by rfl) ⟨390249, by rfl⟩ : syracuseStep 4162661 = 780499) (by norm_num)
theorem B2775107 : Blo 2309435 2775107 := bstep (se 1 (by rfl) ⟨2081330, by rfl⟩ : syracuseStep 2775107 = 4162661) B4162661
theorem B7400285 : Blo 2309435 7400285 := bstep (se 3 (by rfl) ⟨1387553, by rfl⟩ : syracuseStep 7400285 = 2775107) B2775107
theorem B4933523 : Blo 2309435 4933523 := bstep (se 1 (by rfl) ⟨3700142, by rfl⟩ : syracuseStep 4933523 = 7400285) B7400285
theorem B3289015 : Blo 2309435 3289015 := bstep (se 1 (by rfl) ⟨2466761, by rfl⟩ : syracuseStep 3289015 = 4933523) B4933523
theorem B4385353 : Blo 2309435 4385353 := bstep (se 2 (by rfl) ⟨1644507, by rfl⟩ : syracuseStep 4385353 = 3289015) B3289015
theorem B5847137 : Blo 2309435 5847137 := bstep (se 2 (by rfl) ⟨2192676, by rfl⟩ : syracuseStep 5847137 = 4385353) B4385353
theorem B3898091 : Blo 2309435 3898091 := bstep (se 1 (by rfl) ⟨2923568, by rfl⟩ : syracuseStep 3898091 = 5847137) B5847137
theorem B2598727 : Blo 2309435 2598727 := bstep (se 1 (by rfl) ⟨1949045, by rfl⟩ : syracuseStep 2598727 = 3898091) B3898091
theorem B3464969 : Blo 2309435 3464969 := bstep (se 2 (by rfl) ⟨1299363, by rfl⟩ : syracuseStep 3464969 = 2598727) B2598727
theorem B2309979 : Blo 2309435 2309979 := bstep (se 1 (by rfl) ⟨1732484, by rfl⟩ : syracuseStep 2309979 = 3464969) B3464969
theorem B11694293 : Blo 2309435 11694293 := bbase (se 7 (by rfl) ⟨137042, by rfl⟩ : syracuseStep 11694293 = 274085) (by norm_num)
theorem B7796195 : Blo 2309435 7796195 := bstep (se 1 (by rfl) ⟨5847146, by rfl⟩ : syracuseStep 7796195 = 11694293) B11694293
theorem B5197463 : Blo 2309435 5197463 := bstep (se 1 (by rfl) ⟨3898097, by rfl⟩ : syracuseStep 5197463 = 7796195) B7796195
theorem B3464975 : Blo 2309435 3464975 := bstep (se 1 (by rfl) ⟨2598731, by rfl⟩ : syracuseStep 3464975 = 5197463) B5197463
theorem B2309983 : Blo 2309435 2309983 := bstep (se 1 (by rfl) ⟨1732487, by rfl⟩ : syracuseStep 2309983 = 3464975) B3464975
theorem B3464981 : Blo 2309435 3464981 := bbase (se 6 (by rfl) ⟨81210, by rfl⟩ : syracuseStep 3464981 = 162421) (by norm_num)
theorem B2309987 : Blo 2309435 2309987 := bstep (se 1 (by rfl) ⟨1732490, by rfl⟩ : syracuseStep 2309987 = 3464981) B3464981
theorem B18987637 : Blo 2309435 18987637 := bbase (se 5 (by rfl) ⟨890045, by rfl⟩ : syracuseStep 18987637 = 1780091) (by norm_num)
theorem B25316849 : Blo 2309435 25316849 := bstep (se 2 (by rfl) ⟨9493818, by rfl⟩ : syracuseStep 25316849 = 18987637) B18987637
theorem B16877899 : Blo 2309435 16877899 := bstep (se 1 (by rfl) ⟨12658424, by rfl⟩ : syracuseStep 16877899 = 25316849) B25316849
theorem B22503865 : Blo 2309435 22503865 := bstep (se 2 (by rfl) ⟨8438949, by rfl⟩ : syracuseStep 22503865 = 16877899) B16877899
theorem B30005153 : Blo 2309435 30005153 := bstep (se 2 (by rfl) ⟨11251932, by rfl⟩ : syracuseStep 30005153 = 22503865) B22503865
theorem B20003435 : Blo 2309435 20003435 := bstep (se 1 (by rfl) ⟨15002576, by rfl⟩ : syracuseStep 20003435 = 30005153) B30005153
theorem B13335623 : Blo 2309435 13335623 := bstep (se 1 (by rfl) ⟨10001717, by rfl⟩ : syracuseStep 13335623 = 20003435) B20003435
theorem B8890415 : Blo 2309435 8890415 := bstep (se 1 (by rfl) ⟨6667811, by rfl⟩ : syracuseStep 8890415 = 13335623) B13335623
theorem B5926943 : Blo 2309435 5926943 := bstep (se 1 (by rfl) ⟨4445207, by rfl⟩ : syracuseStep 5926943 = 8890415) B8890415
theorem B15805181 : Blo 2309435 15805181 := bstep (se 3 (by rfl) ⟨2963471, by rfl⟩ : syracuseStep 15805181 = 5926943) B5926943
theorem B10536787 : Blo 2309435 10536787 := bstep (se 1 (by rfl) ⟨7902590, by rfl⟩ : syracuseStep 10536787 = 15805181) B15805181
theorem B14049049 : Blo 2309435 14049049 := bstep (se 2 (by rfl) ⟨5268393, by rfl⟩ : syracuseStep 14049049 = 10536787) B10536787
theorem B18732065 : Blo 2309435 18732065 := bstep (se 2 (by rfl) ⟨7024524, by rfl⟩ : syracuseStep 18732065 = 14049049) B14049049
theorem B49952173 : Blo 2309435 49952173 := bstep (se 3 (by rfl) ⟨9366032, by rfl⟩ : syracuseStep 49952173 = 18732065) B18732065
theorem B66602897 : Blo 2309435 66602897 := bstep (se 2 (by rfl) ⟨24976086, by rfl⟩ : syracuseStep 66602897 = 49952173) B49952173
theorem B44401931 : Blo 2309435 44401931 := bstep (se 1 (by rfl) ⟨33301448, by rfl⟩ : syracuseStep 44401931 = 66602897) B66602897
theorem B29601287 : Blo 2309435 29601287 := bstep (se 1 (by rfl) ⟨22200965, by rfl⟩ : syracuseStep 29601287 = 44401931) B44401931
theorem B19734191 : Blo 2309435 19734191 := bstep (se 1 (by rfl) ⟨14800643, by rfl⟩ : syracuseStep 19734191 = 29601287) B29601287
theorem B13156127 : Blo 2309435 13156127 := bstep (se 1 (by rfl) ⟨9867095, by rfl⟩ : syracuseStep 13156127 = 19734191) B19734191
theorem B8770751 : Blo 2309435 8770751 := bstep (se 1 (by rfl) ⟨6578063, by rfl⟩ : syracuseStep 8770751 = 13156127) B13156127
theorem B5847167 : Blo 2309435 5847167 := bstep (se 1 (by rfl) ⟨4385375, by rfl⟩ : syracuseStep 5847167 = 8770751) B8770751
theorem B3898111 : Blo 2309435 3898111 := bstep (se 1 (by rfl) ⟨2923583, by rfl⟩ : syracuseStep 3898111 = 5847167) B5847167
theorem B5197481 : Blo 2309435 5197481 := bstep (se 2 (by rfl) ⟨1949055, by rfl⟩ : syracuseStep 5197481 = 3898111) B3898111
theorem B3464987 : Blo 2309435 3464987 := bstep (se 1 (by rfl) ⟨2598740, by rfl⟩ : syracuseStep 3464987 = 5197481) B5197481
theorem B2309991 : Blo 2309435 2309991 := bstep (se 1 (by rfl) ⟨1732493, by rfl⟩ : syracuseStep 2309991 = 3464987) B3464987
theorem B2598745 : Blo 2309435 2598745 := bbase (se 2 (by rfl) ⟨974529, by rfl⟩ : syracuseStep 2598745 = 1949059) (by norm_num)
theorem B3464993 : Blo 2309435 3464993 := bstep (se 2 (by rfl) ⟨1299372, by rfl⟩ : syracuseStep 3464993 = 2598745) B2598745
theorem B2309995 : Blo 2309435 2309995 := bstep (se 1 (by rfl) ⟨1732496, by rfl⟩ : syracuseStep 2309995 = 3464993) B3464993
theorem B4933565 : Blo 2309435 4933565 := bbase (se 3 (by rfl) ⟨925043, by rfl⟩ : syracuseStep 4933565 = 1850087) (by norm_num)
theorem B3289043 : Blo 2309435 3289043 := bstep (se 1 (by rfl) ⟨2466782, by rfl⟩ : syracuseStep 3289043 = 4933565) B4933565
theorem B8770781 : Blo 2309435 8770781 := bstep (se 3 (by rfl) ⟨1644521, by rfl⟩ : syracuseStep 8770781 = 3289043) B3289043
theorem B5847187 : Blo 2309435 5847187 := bstep (se 1 (by rfl) ⟨4385390, by rfl⟩ : syracuseStep 5847187 = 8770781) B8770781
theorem B7796249 : Blo 2309435 7796249 := bstep (se 2 (by rfl) ⟨2923593, by rfl⟩ : syracuseStep 7796249 = 5847187) B5847187
theorem B5197499 : Blo 2309435 5197499 := bstep (se 1 (by rfl) ⟨3898124, by rfl⟩ : syracuseStep 5197499 = 7796249) B7796249
theorem B3464999 : Blo 2309435 3464999 := bstep (se 1 (by rfl) ⟨2598749, by rfl⟩ : syracuseStep 3464999 = 5197499) B5197499
theorem B2309999 : Blo 2309435 2309999 := bstep (se 1 (by rfl) ⟨1732499, by rfl⟩ : syracuseStep 2309999 = 3464999) B3464999
theorem C0 (j : ℕ) (h1 : 577358 ≤ j) (h2 : j ≤ 577499) : Blo 2309435 (4 * j + 3) := by
  interval_cases j
  · exact B2309435
  · exact B2309439
  · exact B2309443
  · exact B2309447
  · exact B2309451
  · exact B2309455
  · exact B2309459
  · exact B2309463
  · exact B2309467
  · exact B2309471
  · exact B2309475
  · exact B2309479
  · exact B2309483
  · exact B2309487
  · exact B2309491
  · exact B2309495
  · exact B2309499
  · exact B2309503
  · exact B2309507
  · exact B2309511
  · exact B2309515
  · exact B2309519
  · exact B2309523
  · exact B2309527
  · exact B2309531
  · exact B2309535
  · exact B2309539
  · exact B2309543
  · exact B2309547
  · exact B2309551
  · exact B2309555
  · exact B2309559
  · exact B2309563
  · exact B2309567
  · exact B2309571
  · exact B2309575
  · exact B2309579
  · exact B2309583
  · exact B2309587
  · exact B2309591
  · exact B2309595
  · exact B2309599
  · exact B2309603
  · exact B2309607
  · exact B2309611
  · exact B2309615
  · exact B2309619
  · exact B2309623
  · exact B2309627
  · exact B2309631
  · exact B2309635
  · exact B2309639
  · exact B2309643
  · exact B2309647
  · exact B2309651
  · exact B2309655
  · exact B2309659
  · exact B2309663
  · exact B2309667
  · exact B2309671
  · exact B2309675
  · exact B2309679
  · exact B2309683
  · exact B2309687
  · exact B2309691
  · exact B2309695
  · exact B2309699
  · exact B2309703
  · exact B2309707
  · exact B2309711
  · exact B2309715
  · exact B2309719
  · exact B2309723
  · exact B2309727
  · exact B2309731
  · exact B2309735
  · exact B2309739
  · exact B2309743
  · exact B2309747
  · exact B2309751
  · exact B2309755
  · exact B2309759
  · exact B2309763
  · exact B2309767
  · exact B2309771
  · exact B2309775
  · exact B2309779
  · exact B2309783
  · exact B2309787
  · exact B2309791
  · exact B2309795
  · exact B2309799
  · exact B2309803
  · exact B2309807
  · exact B2309811
  · exact B2309815
  · exact B2309819
  · exact B2309823
  · exact B2309827
  · exact B2309831
  · exact B2309835
  · exact B2309839
  · exact B2309843
  · exact B2309847
  · exact B2309851
  · exact B2309855
  · exact B2309859
  · exact B2309863
  · exact B2309867
  · exact B2309871
  · exact B2309875
  · exact B2309879
  · exact B2309883
  · exact B2309887
  · exact B2309891
  · exact B2309895
  · exact B2309899
  · exact B2309903
  · exact B2309907
  · exact B2309911
  · exact B2309915
  · exact B2309919
  · exact B2309923
  · exact B2309927
  · exact B2309931
  · exact B2309935
  · exact B2309939
  · exact B2309943
  · exact B2309947
  · exact B2309951
  · exact B2309955
  · exact B2309959
  · exact B2309963
  · exact B2309967
  · exact B2309971
  · exact B2309975
  · exact B2309979
  · exact B2309983
  · exact B2309987
  · exact B2309991
  · exact B2309995
  · exact B2309999
theorem solution (m : ℕ) (hlo : 2309435 ≤ m) (hhi : m ≤ 2309999) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 577358 ≤ j := by omega
    have hj2 : j ≤ 577499 := by omega
    have hb : Blo 2309435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
