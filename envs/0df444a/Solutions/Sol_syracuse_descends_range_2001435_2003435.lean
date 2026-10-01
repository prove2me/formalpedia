-- Prove2me | solution 1 for syracuse_descends_range_2001435_2003435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:34.000916+00:00
-- url     : https://prove2.me/submissions/3415ded7-3e97-445c-a38e-b14b98bcc9c9

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

theorem B11398805 : Blo 2001435 11398805 := bbase (se 6 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 11398805 = 534319) (by norm_num)
theorem B7599203 : Blo 2001435 7599203 := bstep (se 1 (by rfl) ⟨5699402, by rfl⟩ : syracuseStep 7599203 = 11398805) B11398805
theorem B5066135 : Blo 2001435 5066135 := bstep (se 1 (by rfl) ⟨3799601, by rfl⟩ : syracuseStep 5066135 = 7599203) B7599203
theorem B3377423 : Blo 2001435 3377423 := bstep (se 1 (by rfl) ⟨2533067, by rfl⟩ : syracuseStep 3377423 = 5066135) B5066135
theorem B2251615 : Blo 2001435 2251615 := bstep (se 1 (by rfl) ⟨1688711, by rfl⟩ : syracuseStep 2251615 = 3377423) B3377423
theorem B3002153 : Blo 2001435 3002153 := bstep (se 2 (by rfl) ⟨1125807, by rfl⟩ : syracuseStep 3002153 = 2251615) B2251615
theorem B2001435 : Blo 2001435 2001435 := bstep (se 1 (by rfl) ⟨1501076, by rfl⟩ : syracuseStep 2001435 = 3002153) B3002153
theorem B5699413 : Blo 2001435 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B7599217 : Blo 2001435 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B10132289 : Blo 2001435 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B6754859 : Blo 2001435 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B4503239 : Blo 2001435 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B3002159 : Blo 2001435 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B2001439 : Blo 2001435 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B3002165 : Blo 2001435 3002165 := bbase (se 5 (by rfl) ⟨140726, by rfl⟩ : syracuseStep 3002165 = 281453) (by norm_num)
theorem B2001443 : Blo 2001435 2001443 := bstep (se 1 (by rfl) ⟨1501082, by rfl⟩ : syracuseStep 2001443 = 3002165) B3002165
theorem B5066165 : Blo 2001435 5066165 := bbase (se 5 (by rfl) ⟨237476, by rfl⟩ : syracuseStep 5066165 = 474953) (by norm_num)
theorem B3377443 : Blo 2001435 3377443 := bstep (se 1 (by rfl) ⟨2533082, by rfl⟩ : syracuseStep 3377443 = 5066165) B5066165
theorem B4503257 : Blo 2001435 4503257 := bstep (se 2 (by rfl) ⟨1688721, by rfl⟩ : syracuseStep 4503257 = 3377443) B3377443
theorem B3002171 : Blo 2001435 3002171 := bstep (se 1 (by rfl) ⟨2251628, by rfl⟩ : syracuseStep 3002171 = 4503257) B4503257
theorem B2001447 : Blo 2001435 2001447 := bstep (se 1 (by rfl) ⟨1501085, by rfl⟩ : syracuseStep 2001447 = 3002171) B3002171
theorem B2251633 : Blo 2001435 2251633 := bbase (se 2 (by rfl) ⟨844362, by rfl⟩ : syracuseStep 2251633 = 1688725) (by norm_num)
theorem B3002177 : Blo 2001435 3002177 := bstep (se 2 (by rfl) ⟨1125816, by rfl⟩ : syracuseStep 3002177 = 2251633) B2251633
theorem B2001451 : Blo 2001435 2001451 := bstep (se 1 (by rfl) ⟨1501088, by rfl⟩ : syracuseStep 2001451 = 3002177) B3002177
theorem B8549189 : Blo 2001435 8549189 := bbase (se 4 (by rfl) ⟨801486, by rfl⟩ : syracuseStep 8549189 = 1602973) (by norm_num)
theorem B5699459 : Blo 2001435 5699459 := bstep (se 1 (by rfl) ⟨4274594, by rfl⟩ : syracuseStep 5699459 = 8549189) B8549189
theorem B3799639 : Blo 2001435 3799639 := bstep (se 1 (by rfl) ⟨2849729, by rfl⟩ : syracuseStep 3799639 = 5699459) B5699459
theorem B5066185 : Blo 2001435 5066185 := bstep (se 2 (by rfl) ⟨1899819, by rfl⟩ : syracuseStep 5066185 = 3799639) B3799639
theorem B6754913 : Blo 2001435 6754913 := bstep (se 2 (by rfl) ⟨2533092, by rfl⟩ : syracuseStep 6754913 = 5066185) B5066185
theorem B4503275 : Blo 2001435 4503275 := bstep (se 1 (by rfl) ⟨3377456, by rfl⟩ : syracuseStep 4503275 = 6754913) B6754913
theorem B3002183 : Blo 2001435 3002183 := bstep (se 1 (by rfl) ⟨2251637, by rfl⟩ : syracuseStep 3002183 = 4503275) B4503275
theorem B2001455 : Blo 2001435 2001455 := bstep (se 1 (by rfl) ⟨1501091, by rfl⟩ : syracuseStep 2001455 = 3002183) B3002183
theorem B3002189 : Blo 2001435 3002189 := bbase (se 3 (by rfl) ⟨562910, by rfl⟩ : syracuseStep 3002189 = 1125821) (by norm_num)
theorem B2001459 : Blo 2001435 2001459 := bstep (se 1 (by rfl) ⟨1501094, by rfl⟩ : syracuseStep 2001459 = 3002189) B3002189
theorem B4503293 : Blo 2001435 4503293 := bbase (se 3 (by rfl) ⟨844367, by rfl⟩ : syracuseStep 4503293 = 1688735) (by norm_num)
theorem B3002195 : Blo 2001435 3002195 := bstep (se 1 (by rfl) ⟨2251646, by rfl⟩ : syracuseStep 3002195 = 4503293) B4503293
theorem B2001463 : Blo 2001435 2001463 := bstep (se 1 (by rfl) ⟨1501097, by rfl⟩ : syracuseStep 2001463 = 3002195) B3002195
theorem B3377477 : Blo 2001435 3377477 := bbase (se 4 (by rfl) ⟨316638, by rfl⟩ : syracuseStep 3377477 = 633277) (by norm_num)
theorem B2251651 : Blo 2001435 2251651 := bstep (se 1 (by rfl) ⟨1688738, by rfl⟩ : syracuseStep 2251651 = 3377477) B3377477
theorem B3002201 : Blo 2001435 3002201 := bstep (se 2 (by rfl) ⟨1125825, by rfl⟩ : syracuseStep 3002201 = 2251651) B2251651
theorem B2001467 : Blo 2001435 2001467 := bstep (se 1 (by rfl) ⟨1501100, by rfl⟩ : syracuseStep 2001467 = 3002201) B3002201
theorem B15198677 : Blo 2001435 15198677 := bbase (se 7 (by rfl) ⟨178109, by rfl⟩ : syracuseStep 15198677 = 356219) (by norm_num)
theorem B10132451 : Blo 2001435 10132451 := bstep (se 1 (by rfl) ⟨7599338, by rfl⟩ : syracuseStep 10132451 = 15198677) B15198677
theorem B6754967 : Blo 2001435 6754967 := bstep (se 1 (by rfl) ⟨5066225, by rfl⟩ : syracuseStep 6754967 = 10132451) B10132451
theorem B4503311 : Blo 2001435 4503311 := bstep (se 1 (by rfl) ⟨3377483, by rfl⟩ : syracuseStep 4503311 = 6754967) B6754967
theorem B3002207 : Blo 2001435 3002207 := bstep (se 1 (by rfl) ⟨2251655, by rfl⟩ : syracuseStep 3002207 = 4503311) B4503311
theorem B2001471 : Blo 2001435 2001471 := bstep (se 1 (by rfl) ⟨1501103, by rfl⟩ : syracuseStep 2001471 = 3002207) B3002207
theorem B3002213 : Blo 2001435 3002213 := bbase (se 4 (by rfl) ⟨281457, by rfl⟩ : syracuseStep 3002213 = 562915) (by norm_num)
theorem B2001475 : Blo 2001435 2001475 := bstep (se 1 (by rfl) ⟨1501106, by rfl⟩ : syracuseStep 2001475 = 3002213) B3002213
theorem B3799685 : Blo 2001435 3799685 := bbase (se 4 (by rfl) ⟨356220, by rfl⟩ : syracuseStep 3799685 = 712441) (by norm_num)
theorem B2533123 : Blo 2001435 2533123 := bstep (se 1 (by rfl) ⟨1899842, by rfl⟩ : syracuseStep 2533123 = 3799685) B3799685
theorem B3377497 : Blo 2001435 3377497 := bstep (se 2 (by rfl) ⟨1266561, by rfl⟩ : syracuseStep 3377497 = 2533123) B2533123
theorem B4503329 : Blo 2001435 4503329 := bstep (se 2 (by rfl) ⟨1688748, by rfl⟩ : syracuseStep 4503329 = 3377497) B3377497
theorem B3002219 : Blo 2001435 3002219 := bstep (se 1 (by rfl) ⟨2251664, by rfl⟩ : syracuseStep 3002219 = 4503329) B4503329
theorem B2001479 : Blo 2001435 2001479 := bstep (se 1 (by rfl) ⟨1501109, by rfl⟩ : syracuseStep 2001479 = 3002219) B3002219
theorem B2251669 : Blo 2001435 2251669 := bbase (se 6 (by rfl) ⟨52773, by rfl⟩ : syracuseStep 2251669 = 105547) (by norm_num)
theorem B3002225 : Blo 2001435 3002225 := bstep (se 2 (by rfl) ⟨1125834, by rfl⟩ : syracuseStep 3002225 = 2251669) B2251669
theorem B2001483 : Blo 2001435 2001483 := bstep (se 1 (by rfl) ⟨1501112, by rfl⟩ : syracuseStep 2001483 = 3002225) B3002225
theorem B2533133 : Blo 2001435 2533133 := bbase (se 3 (by rfl) ⟨474962, by rfl⟩ : syracuseStep 2533133 = 949925) (by norm_num)
theorem B6755021 : Blo 2001435 6755021 := bstep (se 3 (by rfl) ⟨1266566, by rfl⟩ : syracuseStep 6755021 = 2533133) B2533133
theorem B4503347 : Blo 2001435 4503347 := bstep (se 1 (by rfl) ⟨3377510, by rfl⟩ : syracuseStep 4503347 = 6755021) B6755021
theorem B3002231 : Blo 2001435 3002231 := bstep (se 1 (by rfl) ⟨2251673, by rfl⟩ : syracuseStep 3002231 = 4503347) B4503347
theorem B2001487 : Blo 2001435 2001487 := bstep (se 1 (by rfl) ⟨1501115, by rfl⟩ : syracuseStep 2001487 = 3002231) B3002231
theorem B3002237 : Blo 2001435 3002237 := bbase (se 3 (by rfl) ⟨562919, by rfl⟩ : syracuseStep 3002237 = 1125839) (by norm_num)
theorem B2001491 : Blo 2001435 2001491 := bstep (se 1 (by rfl) ⟨1501118, by rfl⟩ : syracuseStep 2001491 = 3002237) B3002237
theorem B4503365 : Blo 2001435 4503365 := bbase (se 4 (by rfl) ⟨422190, by rfl⟩ : syracuseStep 4503365 = 844381) (by norm_num)
theorem B3002243 : Blo 2001435 3002243 := bstep (se 1 (by rfl) ⟨2251682, by rfl⟩ : syracuseStep 3002243 = 4503365) B4503365
theorem B2001495 : Blo 2001435 2001495 := bstep (se 1 (by rfl) ⟨1501121, by rfl⟩ : syracuseStep 2001495 = 3002243) B3002243
theorem B2404513 : Blo 2001435 2404513 := bbase (se 2 (by rfl) ⟨901692, by rfl⟩ : syracuseStep 2404513 = 1803385) (by norm_num)
theorem B3206017 : Blo 2001435 3206017 := bstep (se 2 (by rfl) ⟨1202256, by rfl⟩ : syracuseStep 3206017 = 2404513) B2404513
theorem B4274689 : Blo 2001435 4274689 := bstep (se 2 (by rfl) ⟨1603008, by rfl⟩ : syracuseStep 4274689 = 3206017) B3206017
theorem B5699585 : Blo 2001435 5699585 := bstep (se 2 (by rfl) ⟨2137344, by rfl⟩ : syracuseStep 5699585 = 4274689) B4274689
theorem B3799723 : Blo 2001435 3799723 := bstep (se 1 (by rfl) ⟨2849792, by rfl⟩ : syracuseStep 3799723 = 5699585) B5699585
theorem B5066297 : Blo 2001435 5066297 := bstep (se 2 (by rfl) ⟨1899861, by rfl⟩ : syracuseStep 5066297 = 3799723) B3799723
theorem B3377531 : Blo 2001435 3377531 := bstep (se 1 (by rfl) ⟨2533148, by rfl⟩ : syracuseStep 3377531 = 5066297) B5066297
theorem B2251687 : Blo 2001435 2251687 := bstep (se 1 (by rfl) ⟨1688765, by rfl⟩ : syracuseStep 2251687 = 3377531) B3377531
theorem B3002249 : Blo 2001435 3002249 := bstep (se 2 (by rfl) ⟨1125843, by rfl⟩ : syracuseStep 3002249 = 2251687) B2251687
theorem B2001499 : Blo 2001435 2001499 := bstep (se 1 (by rfl) ⟨1501124, by rfl⟩ : syracuseStep 2001499 = 3002249) B3002249
theorem B10132613 : Blo 2001435 10132613 := bbase (se 4 (by rfl) ⟨949932, by rfl⟩ : syracuseStep 10132613 = 1899865) (by norm_num)
theorem B6755075 : Blo 2001435 6755075 := bstep (se 1 (by rfl) ⟨5066306, by rfl⟩ : syracuseStep 6755075 = 10132613) B10132613
theorem B4503383 : Blo 2001435 4503383 := bstep (se 1 (by rfl) ⟨3377537, by rfl⟩ : syracuseStep 4503383 = 6755075) B6755075
theorem B3002255 : Blo 2001435 3002255 := bstep (se 1 (by rfl) ⟨2251691, by rfl⟩ : syracuseStep 3002255 = 4503383) B4503383
theorem B2001503 : Blo 2001435 2001503 := bstep (se 1 (by rfl) ⟨1501127, by rfl⟩ : syracuseStep 2001503 = 3002255) B3002255
theorem B3002261 : Blo 2001435 3002261 := bbase (se 6 (by rfl) ⟨70365, by rfl⟩ : syracuseStep 3002261 = 140731) (by norm_num)
theorem B2001507 : Blo 2001435 2001507 := bstep (se 1 (by rfl) ⟨1501130, by rfl⟩ : syracuseStep 2001507 = 3002261) B3002261
theorem B2137357 : Blo 2001435 2137357 := bbase (se 3 (by rfl) ⟨400754, by rfl⟩ : syracuseStep 2137357 = 801509) (by norm_num)
theorem B11399237 : Blo 2001435 11399237 := bstep (se 4 (by rfl) ⟨1068678, by rfl⟩ : syracuseStep 11399237 = 2137357) B2137357
theorem B7599491 : Blo 2001435 7599491 := bstep (se 1 (by rfl) ⟨5699618, by rfl⟩ : syracuseStep 7599491 = 11399237) B11399237
theorem B5066327 : Blo 2001435 5066327 := bstep (se 1 (by rfl) ⟨3799745, by rfl⟩ : syracuseStep 5066327 = 7599491) B7599491
theorem B3377551 : Blo 2001435 3377551 := bstep (se 1 (by rfl) ⟨2533163, by rfl⟩ : syracuseStep 3377551 = 5066327) B5066327
theorem B4503401 : Blo 2001435 4503401 := bstep (se 2 (by rfl) ⟨1688775, by rfl⟩ : syracuseStep 4503401 = 3377551) B3377551
theorem B3002267 : Blo 2001435 3002267 := bstep (se 1 (by rfl) ⟨2251700, by rfl⟩ : syracuseStep 3002267 = 4503401) B4503401
theorem B2001511 : Blo 2001435 2001511 := bstep (se 1 (by rfl) ⟨1501133, by rfl⟩ : syracuseStep 2001511 = 3002267) B3002267
theorem B2251705 : Blo 2001435 2251705 := bbase (se 2 (by rfl) ⟨844389, by rfl⟩ : syracuseStep 2251705 = 1688779) (by norm_num)
theorem B3002273 : Blo 2001435 3002273 := bstep (se 2 (by rfl) ⟨1125852, by rfl⟩ : syracuseStep 3002273 = 2251705) B2251705
theorem B2001515 : Blo 2001435 2001515 := bstep (se 1 (by rfl) ⟨1501136, by rfl⟩ : syracuseStep 2001515 = 3002273) B3002273
theorem B3606805 : Blo 2001435 3606805 := bbase (se 6 (by rfl) ⟨84534, by rfl⟩ : syracuseStep 3606805 = 169069) (by norm_num)
theorem B4809073 : Blo 2001435 4809073 := bstep (se 2 (by rfl) ⟨1803402, by rfl⟩ : syracuseStep 4809073 = 3606805) B3606805
theorem B6412097 : Blo 2001435 6412097 := bstep (se 2 (by rfl) ⟨2404536, by rfl⟩ : syracuseStep 6412097 = 4809073) B4809073
theorem B4274731 : Blo 2001435 4274731 := bstep (se 1 (by rfl) ⟨3206048, by rfl⟩ : syracuseStep 4274731 = 6412097) B6412097
theorem B5699641 : Blo 2001435 5699641 := bstep (se 2 (by rfl) ⟨2137365, by rfl⟩ : syracuseStep 5699641 = 4274731) B4274731
theorem B7599521 : Blo 2001435 7599521 := bstep (se 2 (by rfl) ⟨2849820, by rfl⟩ : syracuseStep 7599521 = 5699641) B5699641
theorem B5066347 : Blo 2001435 5066347 := bstep (se 1 (by rfl) ⟨3799760, by rfl⟩ : syracuseStep 5066347 = 7599521) B7599521
theorem B6755129 : Blo 2001435 6755129 := bstep (se 2 (by rfl) ⟨2533173, by rfl⟩ : syracuseStep 6755129 = 5066347) B5066347
theorem B4503419 : Blo 2001435 4503419 := bstep (se 1 (by rfl) ⟨3377564, by rfl⟩ : syracuseStep 4503419 = 6755129) B6755129
theorem B3002279 : Blo 2001435 3002279 := bstep (se 1 (by rfl) ⟨2251709, by rfl⟩ : syracuseStep 3002279 = 4503419) B4503419
theorem B2001519 : Blo 2001435 2001519 := bstep (se 1 (by rfl) ⟨1501139, by rfl⟩ : syracuseStep 2001519 = 3002279) B3002279
theorem B3002285 : Blo 2001435 3002285 := bbase (se 3 (by rfl) ⟨562928, by rfl⟩ : syracuseStep 3002285 = 1125857) (by norm_num)
theorem B2001523 : Blo 2001435 2001523 := bstep (se 1 (by rfl) ⟨1501142, by rfl⟩ : syracuseStep 2001523 = 3002285) B3002285
theorem B4503437 : Blo 2001435 4503437 := bbase (se 3 (by rfl) ⟨844394, by rfl⟩ : syracuseStep 4503437 = 1688789) (by norm_num)
theorem B3002291 : Blo 2001435 3002291 := bstep (se 1 (by rfl) ⟨2251718, by rfl⟩ : syracuseStep 3002291 = 4503437) B4503437
theorem B2001527 : Blo 2001435 2001527 := bstep (se 1 (by rfl) ⟨1501145, by rfl⟩ : syracuseStep 2001527 = 3002291) B3002291
theorem B2533189 : Blo 2001435 2533189 := bbase (se 4 (by rfl) ⟨237486, by rfl⟩ : syracuseStep 2533189 = 474973) (by norm_num)
theorem B3377585 : Blo 2001435 3377585 := bstep (se 2 (by rfl) ⟨1266594, by rfl⟩ : syracuseStep 3377585 = 2533189) B2533189
theorem B2251723 : Blo 2001435 2251723 := bstep (se 1 (by rfl) ⟨1688792, by rfl⟩ : syracuseStep 2251723 = 3377585) B3377585
theorem B3002297 : Blo 2001435 3002297 := bstep (se 2 (by rfl) ⟨1125861, by rfl⟩ : syracuseStep 3002297 = 2251723) B2251723
theorem B2001531 : Blo 2001435 2001531 := bstep (se 1 (by rfl) ⟨1501148, by rfl⟩ : syracuseStep 2001531 = 3002297) B3002297
theorem B2705125 : Blo 2001435 2705125 := bbase (se 4 (by rfl) ⟨253605, by rfl⟩ : syracuseStep 2705125 = 507211) (by norm_num)
theorem B3606833 : Blo 2001435 3606833 := bstep (se 2 (by rfl) ⟨1352562, by rfl⟩ : syracuseStep 3606833 = 2705125) B2705125
theorem B9618221 : Blo 2001435 9618221 := bstep (se 3 (by rfl) ⟨1803416, by rfl⟩ : syracuseStep 9618221 = 3606833) B3606833
theorem B25648589 : Blo 2001435 25648589 := bstep (se 3 (by rfl) ⟨4809110, by rfl⟩ : syracuseStep 25648589 = 9618221) B9618221
theorem B17099059 : Blo 2001435 17099059 := bstep (se 1 (by rfl) ⟨12824294, by rfl⟩ : syracuseStep 17099059 = 25648589) B25648589
theorem B22798745 : Blo 2001435 22798745 := bstep (se 2 (by rfl) ⟨8549529, by rfl⟩ : syracuseStep 22798745 = 17099059) B17099059
theorem B15199163 : Blo 2001435 15199163 := bstep (se 1 (by rfl) ⟨11399372, by rfl⟩ : syracuseStep 15199163 = 22798745) B22798745
theorem B10132775 : Blo 2001435 10132775 := bstep (se 1 (by rfl) ⟨7599581, by rfl⟩ : syracuseStep 10132775 = 15199163) B15199163
theorem B6755183 : Blo 2001435 6755183 := bstep (se 1 (by rfl) ⟨5066387, by rfl⟩ : syracuseStep 6755183 = 10132775) B10132775
theorem B4503455 : Blo 2001435 4503455 := bstep (se 1 (by rfl) ⟨3377591, by rfl⟩ : syracuseStep 4503455 = 6755183) B6755183
theorem B3002303 : Blo 2001435 3002303 := bstep (se 1 (by rfl) ⟨2251727, by rfl⟩ : syracuseStep 3002303 = 4503455) B4503455
theorem B2001535 : Blo 2001435 2001535 := bstep (se 1 (by rfl) ⟨1501151, by rfl⟩ : syracuseStep 2001535 = 3002303) B3002303
theorem B3002309 : Blo 2001435 3002309 := bbase (se 4 (by rfl) ⟨281466, by rfl⟩ : syracuseStep 3002309 = 562933) (by norm_num)
theorem B2001539 : Blo 2001435 2001539 := bstep (se 1 (by rfl) ⟨1501154, by rfl⟩ : syracuseStep 2001539 = 3002309) B3002309
theorem B3377605 : Blo 2001435 3377605 := bbase (se 4 (by rfl) ⟨316650, by rfl⟩ : syracuseStep 3377605 = 633301) (by norm_num)
theorem B4503473 : Blo 2001435 4503473 := bstep (se 2 (by rfl) ⟨1688802, by rfl⟩ : syracuseStep 4503473 = 3377605) B3377605
theorem B3002315 : Blo 2001435 3002315 := bstep (se 1 (by rfl) ⟨2251736, by rfl⟩ : syracuseStep 3002315 = 4503473) B4503473
theorem B2001543 : Blo 2001435 2001543 := bstep (se 1 (by rfl) ⟨1501157, by rfl⟩ : syracuseStep 2001543 = 3002315) B3002315
theorem B2251741 : Blo 2001435 2251741 := bbase (se 3 (by rfl) ⟨422201, by rfl⟩ : syracuseStep 2251741 = 844403) (by norm_num)
theorem B3002321 : Blo 2001435 3002321 := bstep (se 2 (by rfl) ⟨1125870, by rfl⟩ : syracuseStep 3002321 = 2251741) B2251741
theorem B2001547 : Blo 2001435 2001547 := bstep (se 1 (by rfl) ⟨1501160, by rfl⟩ : syracuseStep 2001547 = 3002321) B3002321
theorem B6755237 : Blo 2001435 6755237 := bbase (se 4 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 6755237 = 1266607) (by norm_num)
theorem B4503491 : Blo 2001435 4503491 := bstep (se 1 (by rfl) ⟨3377618, by rfl⟩ : syracuseStep 4503491 = 6755237) B6755237
theorem B3002327 : Blo 2001435 3002327 := bstep (se 1 (by rfl) ⟨2251745, by rfl⟩ : syracuseStep 3002327 = 4503491) B4503491
theorem B2001551 : Blo 2001435 2001551 := bstep (se 1 (by rfl) ⟨1501163, by rfl⟩ : syracuseStep 2001551 = 3002327) B3002327
theorem B3002333 : Blo 2001435 3002333 := bbase (se 3 (by rfl) ⟨562937, by rfl⟩ : syracuseStep 3002333 = 1125875) (by norm_num)
theorem B2001555 : Blo 2001435 2001555 := bstep (se 1 (by rfl) ⟨1501166, by rfl⟩ : syracuseStep 2001555 = 3002333) B3002333
theorem B4503509 : Blo 2001435 4503509 := bbase (se 7 (by rfl) ⟨52775, by rfl⟩ : syracuseStep 4503509 = 105551) (by norm_num)
theorem B3002339 : Blo 2001435 3002339 := bstep (se 1 (by rfl) ⟨2251754, by rfl⟩ : syracuseStep 3002339 = 4503509) B4503509
theorem B2001559 : Blo 2001435 2001559 := bstep (se 1 (by rfl) ⟨1501169, by rfl⟩ : syracuseStep 2001559 = 3002339) B3002339
theorem B12173237 : Blo 2001435 12173237 := bbase (se 5 (by rfl) ⟨570620, by rfl⟩ : syracuseStep 12173237 = 1141241) (by norm_num)
theorem B8115491 : Blo 2001435 8115491 := bstep (se 1 (by rfl) ⟨6086618, by rfl⟩ : syracuseStep 8115491 = 12173237) B12173237
theorem B5410327 : Blo 2001435 5410327 := bstep (se 1 (by rfl) ⟨4057745, by rfl⟩ : syracuseStep 5410327 = 8115491) B8115491
theorem B7213769 : Blo 2001435 7213769 := bstep (se 2 (by rfl) ⟨2705163, by rfl⟩ : syracuseStep 7213769 = 5410327) B5410327
theorem B4809179 : Blo 2001435 4809179 := bstep (se 1 (by rfl) ⟨3606884, by rfl⟩ : syracuseStep 4809179 = 7213769) B7213769
theorem B12824477 : Blo 2001435 12824477 := bstep (se 3 (by rfl) ⟨2404589, by rfl⟩ : syracuseStep 12824477 = 4809179) B4809179
theorem B8549651 : Blo 2001435 8549651 := bstep (se 1 (by rfl) ⟨6412238, by rfl⟩ : syracuseStep 8549651 = 12824477) B12824477
theorem B5699767 : Blo 2001435 5699767 := bstep (se 1 (by rfl) ⟨4274825, by rfl⟩ : syracuseStep 5699767 = 8549651) B8549651
theorem B7599689 : Blo 2001435 7599689 := bstep (se 2 (by rfl) ⟨2849883, by rfl⟩ : syracuseStep 7599689 = 5699767) B5699767
theorem B5066459 : Blo 2001435 5066459 := bstep (se 1 (by rfl) ⟨3799844, by rfl⟩ : syracuseStep 5066459 = 7599689) B7599689
theorem B3377639 : Blo 2001435 3377639 := bstep (se 1 (by rfl) ⟨2533229, by rfl⟩ : syracuseStep 3377639 = 5066459) B5066459
theorem B2251759 : Blo 2001435 2251759 := bstep (se 1 (by rfl) ⟨1688819, by rfl⟩ : syracuseStep 2251759 = 3377639) B3377639
theorem B3002345 : Blo 2001435 3002345 := bstep (se 2 (by rfl) ⟨1125879, by rfl⟩ : syracuseStep 3002345 = 2251759) B2251759
theorem B2001563 : Blo 2001435 2001563 := bstep (se 1 (by rfl) ⟨1501172, by rfl⟩ : syracuseStep 2001563 = 3002345) B3002345
theorem B3206125 : Blo 2001435 3206125 := bbase (se 3 (by rfl) ⟨601148, by rfl⟩ : syracuseStep 3206125 = 1202297) (by norm_num)
theorem B17099333 : Blo 2001435 17099333 := bstep (se 4 (by rfl) ⟨1603062, by rfl⟩ : syracuseStep 17099333 = 3206125) B3206125
theorem B11399555 : Blo 2001435 11399555 := bstep (se 1 (by rfl) ⟨8549666, by rfl⟩ : syracuseStep 11399555 = 17099333) B17099333
theorem B7599703 : Blo 2001435 7599703 := bstep (se 1 (by rfl) ⟨5699777, by rfl⟩ : syracuseStep 7599703 = 11399555) B11399555
theorem B10132937 : Blo 2001435 10132937 := bstep (se 2 (by rfl) ⟨3799851, by rfl⟩ : syracuseStep 10132937 = 7599703) B7599703
theorem B6755291 : Blo 2001435 6755291 := bstep (se 1 (by rfl) ⟨5066468, by rfl⟩ : syracuseStep 6755291 = 10132937) B10132937
theorem B4503527 : Blo 2001435 4503527 := bstep (se 1 (by rfl) ⟨3377645, by rfl⟩ : syracuseStep 4503527 = 6755291) B6755291
theorem B3002351 : Blo 2001435 3002351 := bstep (se 1 (by rfl) ⟨2251763, by rfl⟩ : syracuseStep 3002351 = 4503527) B4503527
theorem B2001567 : Blo 2001435 2001567 := bstep (se 1 (by rfl) ⟨1501175, by rfl⟩ : syracuseStep 2001567 = 3002351) B3002351
theorem B3002357 : Blo 2001435 3002357 := bbase (se 5 (by rfl) ⟨140735, by rfl⟩ : syracuseStep 3002357 = 281471) (by norm_num)
theorem B2001571 : Blo 2001435 2001571 := bstep (se 1 (by rfl) ⟨1501178, by rfl⟩ : syracuseStep 2001571 = 3002357) B3002357
theorem B6412277 : Blo 2001435 6412277 := bbase (se 5 (by rfl) ⟨300575, by rfl⟩ : syracuseStep 6412277 = 601151) (by norm_num)
theorem B4274851 : Blo 2001435 4274851 := bstep (se 1 (by rfl) ⟨3206138, by rfl⟩ : syracuseStep 4274851 = 6412277) B6412277
theorem B5699801 : Blo 2001435 5699801 := bstep (se 2 (by rfl) ⟨2137425, by rfl⟩ : syracuseStep 5699801 = 4274851) B4274851
theorem B3799867 : Blo 2001435 3799867 := bstep (se 1 (by rfl) ⟨2849900, by rfl⟩ : syracuseStep 3799867 = 5699801) B5699801
theorem B5066489 : Blo 2001435 5066489 := bstep (se 2 (by rfl) ⟨1899933, by rfl⟩ : syracuseStep 5066489 = 3799867) B3799867
theorem B3377659 : Blo 2001435 3377659 := bstep (se 1 (by rfl) ⟨2533244, by rfl⟩ : syracuseStep 3377659 = 5066489) B5066489
theorem B4503545 : Blo 2001435 4503545 := bstep (se 2 (by rfl) ⟨1688829, by rfl⟩ : syracuseStep 4503545 = 3377659) B3377659
theorem B3002363 : Blo 2001435 3002363 := bstep (se 1 (by rfl) ⟨2251772, by rfl⟩ : syracuseStep 3002363 = 4503545) B4503545
theorem B2001575 : Blo 2001435 2001575 := bstep (se 1 (by rfl) ⟨1501181, by rfl⟩ : syracuseStep 2001575 = 3002363) B3002363
theorem B2251777 : Blo 2001435 2251777 := bbase (se 2 (by rfl) ⟨844416, by rfl⟩ : syracuseStep 2251777 = 1688833) (by norm_num)
theorem B3002369 : Blo 2001435 3002369 := bstep (se 2 (by rfl) ⟨1125888, by rfl⟩ : syracuseStep 3002369 = 2251777) B2251777
theorem B2001579 : Blo 2001435 2001579 := bstep (se 1 (by rfl) ⟨1501184, by rfl⟩ : syracuseStep 2001579 = 3002369) B3002369
theorem B5066509 : Blo 2001435 5066509 := bbase (se 3 (by rfl) ⟨949970, by rfl⟩ : syracuseStep 5066509 = 1899941) (by norm_num)
theorem B6755345 : Blo 2001435 6755345 := bstep (se 2 (by rfl) ⟨2533254, by rfl⟩ : syracuseStep 6755345 = 5066509) B5066509
theorem B4503563 : Blo 2001435 4503563 := bstep (se 1 (by rfl) ⟨3377672, by rfl⟩ : syracuseStep 4503563 = 6755345) B6755345
theorem B3002375 : Blo 2001435 3002375 := bstep (se 1 (by rfl) ⟨2251781, by rfl⟩ : syracuseStep 3002375 = 4503563) B4503563
theorem B2001583 : Blo 2001435 2001583 := bstep (se 1 (by rfl) ⟨1501187, by rfl⟩ : syracuseStep 2001583 = 3002375) B3002375
theorem B3002381 : Blo 2001435 3002381 := bbase (se 3 (by rfl) ⟨562946, by rfl⟩ : syracuseStep 3002381 = 1125893) (by norm_num)
theorem B2001587 : Blo 2001435 2001587 := bstep (se 1 (by rfl) ⟨1501190, by rfl⟩ : syracuseStep 2001587 = 3002381) B3002381
theorem B4503581 : Blo 2001435 4503581 := bbase (se 3 (by rfl) ⟨844421, by rfl⟩ : syracuseStep 4503581 = 1688843) (by norm_num)
theorem B3002387 : Blo 2001435 3002387 := bstep (se 1 (by rfl) ⟨2251790, by rfl⟩ : syracuseStep 3002387 = 4503581) B4503581
theorem B2001591 : Blo 2001435 2001591 := bstep (se 1 (by rfl) ⟨1501193, by rfl⟩ : syracuseStep 2001591 = 3002387) B3002387
theorem B3377693 : Blo 2001435 3377693 := bbase (se 3 (by rfl) ⟨633317, by rfl⟩ : syracuseStep 3377693 = 1266635) (by norm_num)
theorem B2251795 : Blo 2001435 2251795 := bstep (se 1 (by rfl) ⟨1688846, by rfl⟩ : syracuseStep 2251795 = 3377693) B3377693
theorem B3002393 : Blo 2001435 3002393 := bstep (se 2 (by rfl) ⟨1125897, by rfl⟩ : syracuseStep 3002393 = 2251795) B2251795
theorem B2001595 : Blo 2001435 2001595 := bstep (se 1 (by rfl) ⟨1501196, by rfl⟩ : syracuseStep 2001595 = 3002393) B3002393
theorem B4565045 : Blo 2001435 4565045 := bbase (se 5 (by rfl) ⟨213986, by rfl⟩ : syracuseStep 4565045 = 427973) (by norm_num)
theorem B12173453 : Blo 2001435 12173453 := bstep (se 3 (by rfl) ⟨2282522, by rfl⟩ : syracuseStep 12173453 = 4565045) B4565045
theorem B8115635 : Blo 2001435 8115635 := bstep (se 1 (by rfl) ⟨6086726, by rfl⟩ : syracuseStep 8115635 = 12173453) B12173453
theorem B5410423 : Blo 2001435 5410423 := bstep (se 1 (by rfl) ⟨4057817, by rfl⟩ : syracuseStep 5410423 = 8115635) B8115635
theorem B7213897 : Blo 2001435 7213897 := bstep (se 2 (by rfl) ⟨2705211, by rfl⟩ : syracuseStep 7213897 = 5410423) B5410423
theorem B9618529 : Blo 2001435 9618529 := bstep (se 2 (by rfl) ⟨3606948, by rfl⟩ : syracuseStep 9618529 = 7213897) B7213897
theorem B12824705 : Blo 2001435 12824705 := bstep (se 2 (by rfl) ⟨4809264, by rfl⟩ : syracuseStep 12824705 = 9618529) B9618529
theorem B8549803 : Blo 2001435 8549803 := bstep (se 1 (by rfl) ⟨6412352, by rfl⟩ : syracuseStep 8549803 = 12824705) B12824705
theorem B11399737 : Blo 2001435 11399737 := bstep (se 2 (by rfl) ⟨4274901, by rfl⟩ : syracuseStep 11399737 = 8549803) B8549803
theorem B15199649 : Blo 2001435 15199649 := bstep (se 2 (by rfl) ⟨5699868, by rfl⟩ : syracuseStep 15199649 = 11399737) B11399737
theorem B10133099 : Blo 2001435 10133099 := bstep (se 1 (by rfl) ⟨7599824, by rfl⟩ : syracuseStep 10133099 = 15199649) B15199649
theorem B6755399 : Blo 2001435 6755399 := bstep (se 1 (by rfl) ⟨5066549, by rfl⟩ : syracuseStep 6755399 = 10133099) B10133099
theorem B4503599 : Blo 2001435 4503599 := bstep (se 1 (by rfl) ⟨3377699, by rfl⟩ : syracuseStep 4503599 = 6755399) B6755399
theorem B3002399 : Blo 2001435 3002399 := bstep (se 1 (by rfl) ⟨2251799, by rfl⟩ : syracuseStep 3002399 = 4503599) B4503599
theorem B2001599 : Blo 2001435 2001599 := bstep (se 1 (by rfl) ⟨1501199, by rfl⟩ : syracuseStep 2001599 = 3002399) B3002399
theorem B3002405 : Blo 2001435 3002405 := bbase (se 4 (by rfl) ⟨281475, by rfl⟩ : syracuseStep 3002405 = 562951) (by norm_num)
theorem B2001603 : Blo 2001435 2001603 := bstep (se 1 (by rfl) ⟨1501202, by rfl⟩ : syracuseStep 2001603 = 3002405) B3002405
theorem B2533285 : Blo 2001435 2533285 := bbase (se 4 (by rfl) ⟨237495, by rfl⟩ : syracuseStep 2533285 = 474991) (by norm_num)
theorem B3377713 : Blo 2001435 3377713 := bstep (se 2 (by rfl) ⟨1266642, by rfl⟩ : syracuseStep 3377713 = 2533285) B2533285
theorem B4503617 : Blo 2001435 4503617 := bstep (se 2 (by rfl) ⟨1688856, by rfl⟩ : syracuseStep 4503617 = 3377713) B3377713
theorem B3002411 : Blo 2001435 3002411 := bstep (se 1 (by rfl) ⟨2251808, by rfl⟩ : syracuseStep 3002411 = 4503617) B4503617
theorem B2001607 : Blo 2001435 2001607 := bstep (se 1 (by rfl) ⟨1501205, by rfl⟩ : syracuseStep 2001607 = 3002411) B3002411
theorem B2251813 : Blo 2001435 2251813 := bbase (se 4 (by rfl) ⟨211107, by rfl⟩ : syracuseStep 2251813 = 422215) (by norm_num)
theorem B3002417 : Blo 2001435 3002417 := bstep (se 2 (by rfl) ⟨1125906, by rfl⟩ : syracuseStep 3002417 = 2251813) B2251813
theorem B2001611 : Blo 2001435 2001611 := bstep (se 1 (by rfl) ⟨1501208, by rfl⟩ : syracuseStep 2001611 = 3002417) B3002417
theorem B6412405 : Blo 2001435 6412405 := bbase (se 5 (by rfl) ⟨300581, by rfl⟩ : syracuseStep 6412405 = 601163) (by norm_num)
theorem B8549873 : Blo 2001435 8549873 := bstep (se 2 (by rfl) ⟨3206202, by rfl⟩ : syracuseStep 8549873 = 6412405) B6412405
theorem B5699915 : Blo 2001435 5699915 := bstep (se 1 (by rfl) ⟨4274936, by rfl⟩ : syracuseStep 5699915 = 8549873) B8549873
theorem B3799943 : Blo 2001435 3799943 := bstep (se 1 (by rfl) ⟨2849957, by rfl⟩ : syracuseStep 3799943 = 5699915) B5699915
theorem B2533295 : Blo 2001435 2533295 := bstep (se 1 (by rfl) ⟨1899971, by rfl⟩ : syracuseStep 2533295 = 3799943) B3799943
theorem B6755453 : Blo 2001435 6755453 := bstep (se 3 (by rfl) ⟨1266647, by rfl⟩ : syracuseStep 6755453 = 2533295) B2533295
theorem B4503635 : Blo 2001435 4503635 := bstep (se 1 (by rfl) ⟨3377726, by rfl⟩ : syracuseStep 4503635 = 6755453) B6755453
theorem B3002423 : Blo 2001435 3002423 := bstep (se 1 (by rfl) ⟨2251817, by rfl⟩ : syracuseStep 3002423 = 4503635) B4503635
theorem B2001615 : Blo 2001435 2001615 := bstep (se 1 (by rfl) ⟨1501211, by rfl⟩ : syracuseStep 2001615 = 3002423) B3002423
theorem B3002429 : Blo 2001435 3002429 := bbase (se 3 (by rfl) ⟨562955, by rfl⟩ : syracuseStep 3002429 = 1125911) (by norm_num)
theorem B2001619 : Blo 2001435 2001619 := bstep (se 1 (by rfl) ⟨1501214, by rfl⟩ : syracuseStep 2001619 = 3002429) B3002429
theorem B4503653 : Blo 2001435 4503653 := bbase (se 4 (by rfl) ⟨422217, by rfl⟩ : syracuseStep 4503653 = 844435) (by norm_num)
theorem B3002435 : Blo 2001435 3002435 := bstep (se 1 (by rfl) ⟨2251826, by rfl⟩ : syracuseStep 3002435 = 4503653) B4503653
theorem B2001623 : Blo 2001435 2001623 := bstep (se 1 (by rfl) ⟨1501217, by rfl⟩ : syracuseStep 2001623 = 3002435) B3002435
theorem B5066621 : Blo 2001435 5066621 := bbase (se 3 (by rfl) ⟨949991, by rfl⟩ : syracuseStep 5066621 = 1899983) (by norm_num)
theorem B3377747 : Blo 2001435 3377747 := bstep (se 1 (by rfl) ⟨2533310, by rfl⟩ : syracuseStep 3377747 = 5066621) B5066621
theorem B2251831 : Blo 2001435 2251831 := bstep (se 1 (by rfl) ⟨1688873, by rfl⟩ : syracuseStep 2251831 = 3377747) B3377747
theorem B3002441 : Blo 2001435 3002441 := bstep (se 2 (by rfl) ⟨1125915, by rfl⟩ : syracuseStep 3002441 = 2251831) B2251831
theorem B2001627 : Blo 2001435 2001627 := bstep (se 1 (by rfl) ⟨1501220, by rfl⟩ : syracuseStep 2001627 = 3002441) B3002441
theorem B3799973 : Blo 2001435 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B10133261 : Blo 2001435 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B6755507 : Blo 2001435 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B4503671 : Blo 2001435 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B3002447 : Blo 2001435 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B2001631 : Blo 2001435 2001631 := bstep (se 1 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 2001631 = 3002447) B3002447
theorem B3002453 : Blo 2001435 3002453 := bbase (se 8 (by rfl) ⟨17592, by rfl⟩ : syracuseStep 3002453 = 35185) (by norm_num)
theorem B2001635 : Blo 2001435 2001635 := bstep (se 1 (by rfl) ⟨1501226, by rfl⟩ : syracuseStep 2001635 = 3002453) B3002453
theorem B3607021 : Blo 2001435 3607021 := bbase (se 3 (by rfl) ⟨676316, by rfl⟩ : syracuseStep 3607021 = 1352633) (by norm_num)
theorem B19237445 : Blo 2001435 19237445 := bstep (se 4 (by rfl) ⟨1803510, by rfl⟩ : syracuseStep 19237445 = 3607021) B3607021
theorem B12824963 : Blo 2001435 12824963 := bstep (se 1 (by rfl) ⟨9618722, by rfl⟩ : syracuseStep 12824963 = 19237445) B19237445
theorem B8549975 : Blo 2001435 8549975 := bstep (se 1 (by rfl) ⟨6412481, by rfl⟩ : syracuseStep 8549975 = 12824963) B12824963
theorem B5699983 : Blo 2001435 5699983 := bstep (se 1 (by rfl) ⟨4274987, by rfl⟩ : syracuseStep 5699983 = 8549975) B8549975
theorem B7599977 : Blo 2001435 7599977 := bstep (se 2 (by rfl) ⟨2849991, by rfl⟩ : syracuseStep 7599977 = 5699983) B5699983
theorem B5066651 : Blo 2001435 5066651 := bstep (se 1 (by rfl) ⟨3799988, by rfl⟩ : syracuseStep 5066651 = 7599977) B7599977
theorem B3377767 : Blo 2001435 3377767 := bstep (se 1 (by rfl) ⟨2533325, by rfl⟩ : syracuseStep 3377767 = 5066651) B5066651
theorem B4503689 : Blo 2001435 4503689 := bstep (se 2 (by rfl) ⟨1688883, by rfl⟩ : syracuseStep 4503689 = 3377767) B3377767
theorem B3002459 : Blo 2001435 3002459 := bstep (se 1 (by rfl) ⟨2251844, by rfl⟩ : syracuseStep 3002459 = 4503689) B4503689
theorem B2001639 : Blo 2001435 2001639 := bstep (se 1 (by rfl) ⟨1501229, by rfl⟩ : syracuseStep 2001639 = 3002459) B3002459
theorem B2251849 : Blo 2001435 2251849 := bbase (se 2 (by rfl) ⟨844443, by rfl⟩ : syracuseStep 2251849 = 1688887) (by norm_num)
theorem B3002465 : Blo 2001435 3002465 := bstep (se 2 (by rfl) ⟨1125924, by rfl⟩ : syracuseStep 3002465 = 2251849) B2251849
theorem B2001643 : Blo 2001435 2001643 := bstep (se 1 (by rfl) ⟨1501232, by rfl⟩ : syracuseStep 2001643 = 3002465) B3002465
theorem B12825013 : Blo 2001435 12825013 := bbase (se 5 (by rfl) ⟨601172, by rfl⟩ : syracuseStep 12825013 = 1202345) (by norm_num)
theorem B17100017 : Blo 2001435 17100017 := bstep (se 2 (by rfl) ⟨6412506, by rfl⟩ : syracuseStep 17100017 = 12825013) B12825013
theorem B11400011 : Blo 2001435 11400011 := bstep (se 1 (by rfl) ⟨8550008, by rfl⟩ : syracuseStep 11400011 = 17100017) B17100017
theorem B7600007 : Blo 2001435 7600007 := bstep (se 1 (by rfl) ⟨5700005, by rfl⟩ : syracuseStep 7600007 = 11400011) B11400011
theorem B5066671 : Blo 2001435 5066671 := bstep (se 1 (by rfl) ⟨3800003, by rfl⟩ : syracuseStep 5066671 = 7600007) B7600007
theorem B6755561 : Blo 2001435 6755561 := bstep (se 2 (by rfl) ⟨2533335, by rfl⟩ : syracuseStep 6755561 = 5066671) B5066671
theorem B4503707 : Blo 2001435 4503707 := bstep (se 1 (by rfl) ⟨3377780, by rfl⟩ : syracuseStep 4503707 = 6755561) B6755561
theorem B3002471 : Blo 2001435 3002471 := bstep (se 1 (by rfl) ⟨2251853, by rfl⟩ : syracuseStep 3002471 = 4503707) B4503707
theorem B2001647 : Blo 2001435 2001647 := bstep (se 1 (by rfl) ⟨1501235, by rfl⟩ : syracuseStep 2001647 = 3002471) B3002471
theorem B3002477 : Blo 2001435 3002477 := bbase (se 3 (by rfl) ⟨562964, by rfl⟩ : syracuseStep 3002477 = 1125929) (by norm_num)
theorem B2001651 : Blo 2001435 2001651 := bstep (se 1 (by rfl) ⟨1501238, by rfl⟩ : syracuseStep 2001651 = 3002477) B3002477
theorem B4503725 : Blo 2001435 4503725 := bbase (se 3 (by rfl) ⟨844448, by rfl⟩ : syracuseStep 4503725 = 1688897) (by norm_num)
theorem B3002483 : Blo 2001435 3002483 := bstep (se 1 (by rfl) ⟨2251862, by rfl⟩ : syracuseStep 3002483 = 4503725) B4503725
theorem B2001655 : Blo 2001435 2001655 := bstep (se 1 (by rfl) ⟨1501241, by rfl⟩ : syracuseStep 2001655 = 3002483) B3002483
theorem B9618821 : Blo 2001435 9618821 := bbase (se 4 (by rfl) ⟨901764, by rfl⟩ : syracuseStep 9618821 = 1803529) (by norm_num)
theorem B6412547 : Blo 2001435 6412547 := bstep (se 1 (by rfl) ⟨4809410, by rfl⟩ : syracuseStep 6412547 = 9618821) B9618821
theorem B4275031 : Blo 2001435 4275031 := bstep (se 1 (by rfl) ⟨3206273, by rfl⟩ : syracuseStep 4275031 = 6412547) B6412547
theorem B5700041 : Blo 2001435 5700041 := bstep (se 2 (by rfl) ⟨2137515, by rfl⟩ : syracuseStep 5700041 = 4275031) B4275031
theorem B3800027 : Blo 2001435 3800027 := bstep (se 1 (by rfl) ⟨2850020, by rfl⟩ : syracuseStep 3800027 = 5700041) B5700041
theorem B2533351 : Blo 2001435 2533351 := bstep (se 1 (by rfl) ⟨1900013, by rfl⟩ : syracuseStep 2533351 = 3800027) B3800027
theorem B3377801 : Blo 2001435 3377801 := bstep (se 2 (by rfl) ⟨1266675, by rfl⟩ : syracuseStep 3377801 = 2533351) B2533351
theorem B2251867 : Blo 2001435 2251867 := bstep (se 1 (by rfl) ⟨1688900, by rfl⟩ : syracuseStep 2251867 = 3377801) B3377801
theorem B3002489 : Blo 2001435 3002489 := bstep (se 2 (by rfl) ⟨1125933, by rfl⟩ : syracuseStep 3002489 = 2251867) B2251867
theorem B2001659 : Blo 2001435 2001659 := bstep (se 1 (by rfl) ⟨1501244, by rfl⟩ : syracuseStep 2001659 = 3002489) B3002489
theorem B2404709 : Blo 2001435 2404709 := bbase (se 4 (by rfl) ⟨225441, by rfl⟩ : syracuseStep 2404709 = 450883) (by norm_num)
theorem B25650229 : Blo 2001435 25650229 := bstep (se 5 (by rfl) ⟨1202354, by rfl⟩ : syracuseStep 25650229 = 2404709) B2404709
theorem B34200305 : Blo 2001435 34200305 := bstep (se 2 (by rfl) ⟨12825114, by rfl⟩ : syracuseStep 34200305 = 25650229) B25650229
theorem B22800203 : Blo 2001435 22800203 := bstep (se 1 (by rfl) ⟨17100152, by rfl⟩ : syracuseStep 22800203 = 34200305) B34200305
theorem B15200135 : Blo 2001435 15200135 := bstep (se 1 (by rfl) ⟨11400101, by rfl⟩ : syracuseStep 15200135 = 22800203) B22800203
theorem B10133423 : Blo 2001435 10133423 := bstep (se 1 (by rfl) ⟨7600067, by rfl⟩ : syracuseStep 10133423 = 15200135) B15200135
theorem B6755615 : Blo 2001435 6755615 := bstep (se 1 (by rfl) ⟨5066711, by rfl⟩ : syracuseStep 6755615 = 10133423) B10133423
theorem B4503743 : Blo 2001435 4503743 := bstep (se 1 (by rfl) ⟨3377807, by rfl⟩ : syracuseStep 4503743 = 6755615) B6755615
theorem B3002495 : Blo 2001435 3002495 := bstep (se 1 (by rfl) ⟨2251871, by rfl⟩ : syracuseStep 3002495 = 4503743) B4503743
theorem B2001663 : Blo 2001435 2001663 := bstep (se 1 (by rfl) ⟨1501247, by rfl⟩ : syracuseStep 2001663 = 3002495) B3002495
theorem B3002501 : Blo 2001435 3002501 := bbase (se 4 (by rfl) ⟨281484, by rfl⟩ : syracuseStep 3002501 = 562969) (by norm_num)
theorem B2001667 : Blo 2001435 2001667 := bstep (se 1 (by rfl) ⟨1501250, by rfl⟩ : syracuseStep 2001667 = 3002501) B3002501
theorem B3377821 : Blo 2001435 3377821 := bbase (se 3 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 3377821 = 1266683) (by norm_num)
theorem B4503761 : Blo 2001435 4503761 := bstep (se 2 (by rfl) ⟨1688910, by rfl⟩ : syracuseStep 4503761 = 3377821) B3377821
theorem B3002507 : Blo 2001435 3002507 := bstep (se 1 (by rfl) ⟨2251880, by rfl⟩ : syracuseStep 3002507 = 4503761) B4503761
theorem B2001671 : Blo 2001435 2001671 := bstep (se 1 (by rfl) ⟨1501253, by rfl⟩ : syracuseStep 2001671 = 3002507) B3002507
theorem B2251885 : Blo 2001435 2251885 := bbase (se 3 (by rfl) ⟨422228, by rfl⟩ : syracuseStep 2251885 = 844457) (by norm_num)
theorem B3002513 : Blo 2001435 3002513 := bstep (se 2 (by rfl) ⟨1125942, by rfl⟩ : syracuseStep 3002513 = 2251885) B2251885
theorem B2001675 : Blo 2001435 2001675 := bstep (se 1 (by rfl) ⟨1501256, by rfl⟩ : syracuseStep 2001675 = 3002513) B3002513
theorem B6755669 : Blo 2001435 6755669 := bbase (se 14 (by rfl) ⟨618, by rfl⟩ : syracuseStep 6755669 = 1237) (by norm_num)
theorem B4503779 : Blo 2001435 4503779 := bstep (se 1 (by rfl) ⟨3377834, by rfl⟩ : syracuseStep 4503779 = 6755669) B6755669
theorem B3002519 : Blo 2001435 3002519 := bstep (se 1 (by rfl) ⟨2251889, by rfl⟩ : syracuseStep 3002519 = 4503779) B4503779
theorem B2001679 : Blo 2001435 2001679 := bstep (se 1 (by rfl) ⟨1501259, by rfl⟩ : syracuseStep 2001679 = 3002519) B3002519
theorem B3002525 : Blo 2001435 3002525 := bbase (se 3 (by rfl) ⟨562973, by rfl⟩ : syracuseStep 3002525 = 1125947) (by norm_num)
theorem B2001683 : Blo 2001435 2001683 := bstep (se 1 (by rfl) ⟨1501262, by rfl⟩ : syracuseStep 2001683 = 3002525) B3002525
theorem B4503797 : Blo 2001435 4503797 := bbase (se 5 (by rfl) ⟨211115, by rfl⟩ : syracuseStep 4503797 = 422231) (by norm_num)
theorem B3002531 : Blo 2001435 3002531 := bstep (se 1 (by rfl) ⟨2251898, by rfl⟩ : syracuseStep 3002531 = 4503797) B4503797
theorem B2001687 : Blo 2001435 2001687 := bstep (se 1 (by rfl) ⟨1501265, by rfl⟩ : syracuseStep 2001687 = 3002531) B3002531
theorem B2437553 : Blo 2001435 2437553 := bbase (se 2 (by rfl) ⟨914082, by rfl⟩ : syracuseStep 2437553 = 1828165) (by norm_num)
theorem B6500141 : Blo 2001435 6500141 := bstep (se 3 (by rfl) ⟨1218776, by rfl⟩ : syracuseStep 6500141 = 2437553) B2437553
theorem B4333427 : Blo 2001435 4333427 := bstep (se 1 (by rfl) ⟨3250070, by rfl⟩ : syracuseStep 4333427 = 6500141) B6500141
theorem B2888951 : Blo 2001435 2888951 := bstep (se 1 (by rfl) ⟨2166713, by rfl⟩ : syracuseStep 2888951 = 4333427) B4333427
theorem B7703869 : Blo 2001435 7703869 := bstep (se 3 (by rfl) ⟨1444475, by rfl⟩ : syracuseStep 7703869 = 2888951) B2888951
theorem B10271825 : Blo 2001435 10271825 := bstep (se 2 (by rfl) ⟨3851934, by rfl⟩ : syracuseStep 10271825 = 7703869) B7703869
theorem B6847883 : Blo 2001435 6847883 := bstep (se 1 (by rfl) ⟨5135912, by rfl⟩ : syracuseStep 6847883 = 10271825) B10271825
theorem B4565255 : Blo 2001435 4565255 := bstep (se 1 (by rfl) ⟨3423941, by rfl⟩ : syracuseStep 4565255 = 6847883) B6847883
theorem B12174013 : Blo 2001435 12174013 := bstep (se 3 (by rfl) ⟨2282627, by rfl⟩ : syracuseStep 12174013 = 4565255) B4565255
theorem B16232017 : Blo 2001435 16232017 := bstep (se 2 (by rfl) ⟨6087006, by rfl⟩ : syracuseStep 16232017 = 12174013) B12174013
theorem B21642689 : Blo 2001435 21642689 := bstep (se 2 (by rfl) ⟨8116008, by rfl⟩ : syracuseStep 21642689 = 16232017) B16232017
theorem B14428459 : Blo 2001435 14428459 := bstep (se 1 (by rfl) ⟨10821344, by rfl⟩ : syracuseStep 14428459 = 21642689) B21642689
theorem B19237945 : Blo 2001435 19237945 := bstep (se 2 (by rfl) ⟨7214229, by rfl⟩ : syracuseStep 19237945 = 14428459) B14428459
theorem B25650593 : Blo 2001435 25650593 := bstep (se 2 (by rfl) ⟨9618972, by rfl⟩ : syracuseStep 25650593 = 19237945) B19237945
theorem B17100395 : Blo 2001435 17100395 := bstep (se 1 (by rfl) ⟨12825296, by rfl⟩ : syracuseStep 17100395 = 25650593) B25650593
theorem B11400263 : Blo 2001435 11400263 := bstep (se 1 (by rfl) ⟨8550197, by rfl⟩ : syracuseStep 11400263 = 17100395) B17100395
theorem B7600175 : Blo 2001435 7600175 := bstep (se 1 (by rfl) ⟨5700131, by rfl⟩ : syracuseStep 7600175 = 11400263) B11400263
theorem B5066783 : Blo 2001435 5066783 := bstep (se 1 (by rfl) ⟨3800087, by rfl⟩ : syracuseStep 5066783 = 7600175) B7600175
theorem B3377855 : Blo 2001435 3377855 := bstep (se 1 (by rfl) ⟨2533391, by rfl⟩ : syracuseStep 3377855 = 5066783) B5066783
theorem B2251903 : Blo 2001435 2251903 := bstep (se 1 (by rfl) ⟨1688927, by rfl⟩ : syracuseStep 2251903 = 3377855) B3377855
theorem B3002537 : Blo 2001435 3002537 := bstep (se 2 (by rfl) ⟨1125951, by rfl⟩ : syracuseStep 3002537 = 2251903) B2251903
theorem B2001691 : Blo 2001435 2001691 := bstep (se 1 (by rfl) ⟨1501268, by rfl⟩ : syracuseStep 2001691 = 3002537) B3002537
theorem B6412661 : Blo 2001435 6412661 := bbase (se 5 (by rfl) ⟨300593, by rfl⟩ : syracuseStep 6412661 = 601187) (by norm_num)
theorem B4275107 : Blo 2001435 4275107 := bstep (se 1 (by rfl) ⟨3206330, by rfl⟩ : syracuseStep 4275107 = 6412661) B6412661
theorem B2850071 : Blo 2001435 2850071 := bstep (se 1 (by rfl) ⟨2137553, by rfl⟩ : syracuseStep 2850071 = 4275107) B4275107
theorem B7600189 : Blo 2001435 7600189 := bstep (se 3 (by rfl) ⟨1425035, by rfl⟩ : syracuseStep 7600189 = 2850071) B2850071
theorem B10133585 : Blo 2001435 10133585 := bstep (se 2 (by rfl) ⟨3800094, by rfl⟩ : syracuseStep 10133585 = 7600189) B7600189
theorem B6755723 : Blo 2001435 6755723 := bstep (se 1 (by rfl) ⟨5066792, by rfl⟩ : syracuseStep 6755723 = 10133585) B10133585
theorem B4503815 : Blo 2001435 4503815 := bstep (se 1 (by rfl) ⟨3377861, by rfl⟩ : syracuseStep 4503815 = 6755723) B6755723
theorem B3002543 : Blo 2001435 3002543 := bstep (se 1 (by rfl) ⟨2251907, by rfl⟩ : syracuseStep 3002543 = 4503815) B4503815
theorem B2001695 : Blo 2001435 2001695 := bstep (se 1 (by rfl) ⟨1501271, by rfl⟩ : syracuseStep 2001695 = 3002543) B3002543
theorem B3002549 : Blo 2001435 3002549 := bbase (se 5 (by rfl) ⟨140744, by rfl⟩ : syracuseStep 3002549 = 281489) (by norm_num)
theorem B2001699 : Blo 2001435 2001699 := bstep (se 1 (by rfl) ⟨1501274, by rfl⟩ : syracuseStep 2001699 = 3002549) B3002549
theorem B5066813 : Blo 2001435 5066813 := bbase (se 3 (by rfl) ⟨950027, by rfl⟩ : syracuseStep 5066813 = 1900055) (by norm_num)
theorem B3377875 : Blo 2001435 3377875 := bstep (se 1 (by rfl) ⟨2533406, by rfl⟩ : syracuseStep 3377875 = 5066813) B5066813
theorem B4503833 : Blo 2001435 4503833 := bstep (se 2 (by rfl) ⟨1688937, by rfl⟩ : syracuseStep 4503833 = 3377875) B3377875
theorem B3002555 : Blo 2001435 3002555 := bstep (se 1 (by rfl) ⟨2251916, by rfl⟩ : syracuseStep 3002555 = 4503833) B4503833
theorem B2001703 : Blo 2001435 2001703 := bstep (se 1 (by rfl) ⟨1501277, by rfl⟩ : syracuseStep 2001703 = 3002555) B3002555
theorem B2251921 : Blo 2001435 2251921 := bbase (se 2 (by rfl) ⟨844470, by rfl⟩ : syracuseStep 2251921 = 1688941) (by norm_num)
theorem B3002561 : Blo 2001435 3002561 := bstep (se 2 (by rfl) ⟨1125960, by rfl⟩ : syracuseStep 3002561 = 2251921) B2251921
theorem B2001707 : Blo 2001435 2001707 := bstep (se 1 (by rfl) ⟨1501280, by rfl⟩ : syracuseStep 2001707 = 3002561) B3002561
theorem B3800125 : Blo 2001435 3800125 := bbase (se 3 (by rfl) ⟨712523, by rfl⟩ : syracuseStep 3800125 = 1425047) (by norm_num)
theorem B5066833 : Blo 2001435 5066833 := bstep (se 2 (by rfl) ⟨1900062, by rfl⟩ : syracuseStep 5066833 = 3800125) B3800125
theorem B6755777 : Blo 2001435 6755777 := bstep (se 2 (by rfl) ⟨2533416, by rfl⟩ : syracuseStep 6755777 = 5066833) B5066833
theorem B4503851 : Blo 2001435 4503851 := bstep (se 1 (by rfl) ⟨3377888, by rfl⟩ : syracuseStep 4503851 = 6755777) B6755777
theorem B3002567 : Blo 2001435 3002567 := bstep (se 1 (by rfl) ⟨2251925, by rfl⟩ : syracuseStep 3002567 = 4503851) B4503851
theorem B2001711 : Blo 2001435 2001711 := bstep (se 1 (by rfl) ⟨1501283, by rfl⟩ : syracuseStep 2001711 = 3002567) B3002567
theorem B3002573 : Blo 2001435 3002573 := bbase (se 3 (by rfl) ⟨562982, by rfl⟩ : syracuseStep 3002573 = 1125965) (by norm_num)
theorem B2001715 : Blo 2001435 2001715 := bstep (se 1 (by rfl) ⟨1501286, by rfl⟩ : syracuseStep 2001715 = 3002573) B3002573
theorem B4503869 : Blo 2001435 4503869 := bbase (se 3 (by rfl) ⟨844475, by rfl⟩ : syracuseStep 4503869 = 1688951) (by norm_num)
theorem B3002579 : Blo 2001435 3002579 := bstep (se 1 (by rfl) ⟨2251934, by rfl⟩ : syracuseStep 3002579 = 4503869) B4503869
theorem B2001719 : Blo 2001435 2001719 := bstep (se 1 (by rfl) ⟨1501289, by rfl⟩ : syracuseStep 2001719 = 3002579) B3002579
theorem B3377909 : Blo 2001435 3377909 := bbase (se 5 (by rfl) ⟨158339, by rfl⟩ : syracuseStep 3377909 = 316679) (by norm_num)
theorem B2251939 : Blo 2001435 2251939 := bstep (se 1 (by rfl) ⟨1688954, by rfl⟩ : syracuseStep 2251939 = 3377909) B3377909
theorem B3002585 : Blo 2001435 3002585 := bstep (se 2 (by rfl) ⟨1125969, by rfl⟩ : syracuseStep 3002585 = 2251939) B2251939
theorem B2001723 : Blo 2001435 2001723 := bstep (se 1 (by rfl) ⟨1501292, by rfl⟩ : syracuseStep 2001723 = 3002585) B3002585
theorem B16232309 : Blo 2001435 16232309 := bbase (se 5 (by rfl) ⟨760889, by rfl⟩ : syracuseStep 16232309 = 1521779) (by norm_num)
theorem B10821539 : Blo 2001435 10821539 := bstep (se 1 (by rfl) ⟨8116154, by rfl⟩ : syracuseStep 10821539 = 16232309) B16232309
theorem B7214359 : Blo 2001435 7214359 := bstep (se 1 (by rfl) ⟨5410769, by rfl⟩ : syracuseStep 7214359 = 10821539) B10821539
theorem B9619145 : Blo 2001435 9619145 := bstep (se 2 (by rfl) ⟨3607179, by rfl⟩ : syracuseStep 9619145 = 7214359) B7214359
theorem B6412763 : Blo 2001435 6412763 := bstep (se 1 (by rfl) ⟨4809572, by rfl⟩ : syracuseStep 6412763 = 9619145) B9619145
theorem B4275175 : Blo 2001435 4275175 := bstep (se 1 (by rfl) ⟨3206381, by rfl⟩ : syracuseStep 4275175 = 6412763) B6412763
theorem B5700233 : Blo 2001435 5700233 := bstep (se 2 (by rfl) ⟨2137587, by rfl⟩ : syracuseStep 5700233 = 4275175) B4275175
theorem B15200621 : Blo 2001435 15200621 := bstep (se 3 (by rfl) ⟨2850116, by rfl⟩ : syracuseStep 15200621 = 5700233) B5700233
theorem B10133747 : Blo 2001435 10133747 := bstep (se 1 (by rfl) ⟨7600310, by rfl⟩ : syracuseStep 10133747 = 15200621) B15200621
theorem B6755831 : Blo 2001435 6755831 := bstep (se 1 (by rfl) ⟨5066873, by rfl⟩ : syracuseStep 6755831 = 10133747) B10133747
theorem B4503887 : Blo 2001435 4503887 := bstep (se 1 (by rfl) ⟨3377915, by rfl⟩ : syracuseStep 4503887 = 6755831) B6755831
theorem B3002591 : Blo 2001435 3002591 := bstep (se 1 (by rfl) ⟨2251943, by rfl⟩ : syracuseStep 3002591 = 4503887) B4503887
theorem B2001727 : Blo 2001435 2001727 := bstep (se 1 (by rfl) ⟨1501295, by rfl⟩ : syracuseStep 2001727 = 3002591) B3002591
theorem B3002597 : Blo 2001435 3002597 := bbase (se 4 (by rfl) ⟨281493, by rfl⟩ : syracuseStep 3002597 = 562987) (by norm_num)
theorem B2001731 : Blo 2001435 2001731 := bstep (se 1 (by rfl) ⟨1501298, by rfl⟩ : syracuseStep 2001731 = 3002597) B3002597
theorem B18510581 : Blo 2001435 18510581 := bbase (se 5 (by rfl) ⟨867683, by rfl⟩ : syracuseStep 18510581 = 1735367) (by norm_num)
theorem B12340387 : Blo 2001435 12340387 := bstep (se 1 (by rfl) ⟨9255290, by rfl⟩ : syracuseStep 12340387 = 18510581) B18510581
theorem B16453849 : Blo 2001435 16453849 := bstep (se 2 (by rfl) ⟨6170193, by rfl⟩ : syracuseStep 16453849 = 12340387) B12340387
theorem B21938465 : Blo 2001435 21938465 := bstep (se 2 (by rfl) ⟨8226924, by rfl⟩ : syracuseStep 21938465 = 16453849) B16453849
theorem B14625643 : Blo 2001435 14625643 := bstep (se 1 (by rfl) ⟨10969232, by rfl⟩ : syracuseStep 14625643 = 21938465) B21938465
theorem B19500857 : Blo 2001435 19500857 := bstep (se 2 (by rfl) ⟨7312821, by rfl⟩ : syracuseStep 19500857 = 14625643) B14625643
theorem B13000571 : Blo 2001435 13000571 := bstep (se 1 (by rfl) ⟨9750428, by rfl⟩ : syracuseStep 13000571 = 19500857) B19500857
theorem B8667047 : Blo 2001435 8667047 := bstep (se 1 (by rfl) ⟨6500285, by rfl⟩ : syracuseStep 8667047 = 13000571) B13000571
theorem B23112125 : Blo 2001435 23112125 := bstep (se 3 (by rfl) ⟨4333523, by rfl⟩ : syracuseStep 23112125 = 8667047) B8667047
theorem B15408083 : Blo 2001435 15408083 := bstep (se 1 (by rfl) ⟨11556062, by rfl⟩ : syracuseStep 15408083 = 23112125) B23112125
theorem B10272055 : Blo 2001435 10272055 := bstep (se 1 (by rfl) ⟨7704041, by rfl⟩ : syracuseStep 10272055 = 15408083) B15408083
theorem B13696073 : Blo 2001435 13696073 := bstep (se 2 (by rfl) ⟨5136027, by rfl⟩ : syracuseStep 13696073 = 10272055) B10272055
theorem B9130715 : Blo 2001435 9130715 := bstep (se 1 (by rfl) ⟨6848036, by rfl⟩ : syracuseStep 9130715 = 13696073) B13696073
theorem B6087143 : Blo 2001435 6087143 := bstep (se 1 (by rfl) ⟨4565357, by rfl⟩ : syracuseStep 6087143 = 9130715) B9130715
theorem B4058095 : Blo 2001435 4058095 := bstep (se 1 (by rfl) ⟨3043571, by rfl⟩ : syracuseStep 4058095 = 6087143) B6087143
theorem B5410793 : Blo 2001435 5410793 := bstep (se 2 (by rfl) ⟨2029047, by rfl⟩ : syracuseStep 5410793 = 4058095) B4058095
theorem B3607195 : Blo 2001435 3607195 := bstep (se 1 (by rfl) ⟨2705396, by rfl⟩ : syracuseStep 3607195 = 5410793) B5410793
theorem B4809593 : Blo 2001435 4809593 := bstep (se 2 (by rfl) ⟨1803597, by rfl⟩ : syracuseStep 4809593 = 3607195) B3607195
theorem B3206395 : Blo 2001435 3206395 := bstep (se 1 (by rfl) ⟨2404796, by rfl⟩ : syracuseStep 3206395 = 4809593) B4809593
theorem B4275193 : Blo 2001435 4275193 := bstep (se 2 (by rfl) ⟨1603197, by rfl⟩ : syracuseStep 4275193 = 3206395) B3206395
theorem B5700257 : Blo 2001435 5700257 := bstep (se 2 (by rfl) ⟨2137596, by rfl⟩ : syracuseStep 5700257 = 4275193) B4275193
theorem B3800171 : Blo 2001435 3800171 := bstep (se 1 (by rfl) ⟨2850128, by rfl⟩ : syracuseStep 3800171 = 5700257) B5700257
theorem B2533447 : Blo 2001435 2533447 := bstep (se 1 (by rfl) ⟨1900085, by rfl⟩ : syracuseStep 2533447 = 3800171) B3800171
theorem B3377929 : Blo 2001435 3377929 := bstep (se 2 (by rfl) ⟨1266723, by rfl⟩ : syracuseStep 3377929 = 2533447) B2533447
theorem B4503905 : Blo 2001435 4503905 := bstep (se 2 (by rfl) ⟨1688964, by rfl⟩ : syracuseStep 4503905 = 3377929) B3377929
theorem B3002603 : Blo 2001435 3002603 := bstep (se 1 (by rfl) ⟨2251952, by rfl⟩ : syracuseStep 3002603 = 4503905) B4503905
theorem B2001735 : Blo 2001435 2001735 := bstep (se 1 (by rfl) ⟨1501301, by rfl⟩ : syracuseStep 2001735 = 3002603) B3002603
theorem B2251957 : Blo 2001435 2251957 := bbase (se 5 (by rfl) ⟨105560, by rfl⟩ : syracuseStep 2251957 = 211121) (by norm_num)
theorem B3002609 : Blo 2001435 3002609 := bstep (se 2 (by rfl) ⟨1125978, by rfl⟩ : syracuseStep 3002609 = 2251957) B2251957
theorem B2001739 : Blo 2001435 2001739 := bstep (se 1 (by rfl) ⟨1501304, by rfl⟩ : syracuseStep 2001739 = 3002609) B3002609
theorem B2533457 : Blo 2001435 2533457 := bbase (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) (by norm_num)
theorem B6755885 : Blo 2001435 6755885 := bstep (se 3 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 6755885 = 2533457) B2533457
theorem B4503923 : Blo 2001435 4503923 := bstep (se 1 (by rfl) ⟨3377942, by rfl⟩ : syracuseStep 4503923 = 6755885) B6755885
theorem B3002615 : Blo 2001435 3002615 := bstep (se 1 (by rfl) ⟨2251961, by rfl⟩ : syracuseStep 3002615 = 4503923) B4503923
theorem B2001743 : Blo 2001435 2001743 := bstep (se 1 (by rfl) ⟨1501307, by rfl⟩ : syracuseStep 2001743 = 3002615) B3002615
theorem B3002621 : Blo 2001435 3002621 := bbase (se 3 (by rfl) ⟨562991, by rfl⟩ : syracuseStep 3002621 = 1125983) (by norm_num)
theorem B2001747 : Blo 2001435 2001747 := bstep (se 1 (by rfl) ⟨1501310, by rfl⟩ : syracuseStep 2001747 = 3002621) B3002621
theorem B4503941 : Blo 2001435 4503941 := bbase (se 4 (by rfl) ⟨422244, by rfl⟩ : syracuseStep 4503941 = 844489) (by norm_num)
theorem B3002627 : Blo 2001435 3002627 := bstep (se 1 (by rfl) ⟨2251970, by rfl⟩ : syracuseStep 3002627 = 4503941) B4503941
theorem B2001751 : Blo 2001435 2001751 := bstep (se 1 (by rfl) ⟨1501313, by rfl⟩ : syracuseStep 2001751 = 3002627) B3002627
theorem B2850157 : Blo 2001435 2850157 := bbase (se 3 (by rfl) ⟨534404, by rfl⟩ : syracuseStep 2850157 = 1068809) (by norm_num)
theorem B3800209 : Blo 2001435 3800209 := bstep (se 2 (by rfl) ⟨1425078, by rfl⟩ : syracuseStep 3800209 = 2850157) B2850157
theorem B5066945 : Blo 2001435 5066945 := bstep (se 2 (by rfl) ⟨1900104, by rfl⟩ : syracuseStep 5066945 = 3800209) B3800209
theorem B3377963 : Blo 2001435 3377963 := bstep (se 1 (by rfl) ⟨2533472, by rfl⟩ : syracuseStep 3377963 = 5066945) B5066945
theorem B2251975 : Blo 2001435 2251975 := bstep (se 1 (by rfl) ⟨1688981, by rfl⟩ : syracuseStep 2251975 = 3377963) B3377963
theorem B3002633 : Blo 2001435 3002633 := bstep (se 2 (by rfl) ⟨1125987, by rfl⟩ : syracuseStep 3002633 = 2251975) B2251975
theorem B2001755 : Blo 2001435 2001755 := bstep (se 1 (by rfl) ⟨1501316, by rfl⟩ : syracuseStep 2001755 = 3002633) B3002633
theorem B10133909 : Blo 2001435 10133909 := bbase (se 6 (by rfl) ⟨237513, by rfl⟩ : syracuseStep 10133909 = 475027) (by norm_num)
theorem B6755939 : Blo 2001435 6755939 := bstep (se 1 (by rfl) ⟨5066954, by rfl⟩ : syracuseStep 6755939 = 10133909) B10133909
theorem B4503959 : Blo 2001435 4503959 := bstep (se 1 (by rfl) ⟨3377969, by rfl⟩ : syracuseStep 4503959 = 6755939) B6755939
theorem B3002639 : Blo 2001435 3002639 := bstep (se 1 (by rfl) ⟨2251979, by rfl⟩ : syracuseStep 3002639 = 4503959) B4503959
theorem B2001759 : Blo 2001435 2001759 := bstep (se 1 (by rfl) ⟨1501319, by rfl⟩ : syracuseStep 2001759 = 3002639) B3002639
theorem B3002645 : Blo 2001435 3002645 := bbase (se 6 (by rfl) ⟨70374, by rfl⟩ : syracuseStep 3002645 = 140749) (by norm_num)
theorem B2001763 : Blo 2001435 2001763 := bstep (se 1 (by rfl) ⟨1501322, by rfl⟩ : syracuseStep 2001763 = 3002645) B3002645
theorem B9750581 : Blo 2001435 9750581 := bbase (se 5 (by rfl) ⟨457058, by rfl⟩ : syracuseStep 9750581 = 914117) (by norm_num)
theorem B6500387 : Blo 2001435 6500387 := bstep (se 1 (by rfl) ⟨4875290, by rfl⟩ : syracuseStep 6500387 = 9750581) B9750581
theorem B4333591 : Blo 2001435 4333591 := bstep (se 1 (by rfl) ⟨3250193, by rfl⟩ : syracuseStep 4333591 = 6500387) B6500387
theorem B5778121 : Blo 2001435 5778121 := bstep (se 2 (by rfl) ⟨2166795, by rfl⟩ : syracuseStep 5778121 = 4333591) B4333591
theorem B7704161 : Blo 2001435 7704161 := bstep (se 2 (by rfl) ⟨2889060, by rfl⟩ : syracuseStep 7704161 = 5778121) B5778121
theorem B5136107 : Blo 2001435 5136107 := bstep (se 1 (by rfl) ⟨3852080, by rfl⟩ : syracuseStep 5136107 = 7704161) B7704161
theorem B13696285 : Blo 2001435 13696285 := bstep (se 3 (by rfl) ⟨2568053, by rfl⟩ : syracuseStep 13696285 = 5136107) B5136107
theorem B18261713 : Blo 2001435 18261713 := bstep (se 2 (by rfl) ⟨6848142, by rfl⟩ : syracuseStep 18261713 = 13696285) B13696285
theorem B12174475 : Blo 2001435 12174475 := bstep (se 1 (by rfl) ⟨9130856, by rfl⟩ : syracuseStep 12174475 = 18261713) B18261713
theorem B16232633 : Blo 2001435 16232633 := bstep (se 2 (by rfl) ⟨6087237, by rfl⟩ : syracuseStep 16232633 = 12174475) B12174475
theorem B10821755 : Blo 2001435 10821755 := bstep (se 1 (by rfl) ⟨8116316, by rfl⟩ : syracuseStep 10821755 = 16232633) B16232633
theorem B7214503 : Blo 2001435 7214503 := bstep (se 1 (by rfl) ⟨5410877, by rfl⟩ : syracuseStep 7214503 = 10821755) B10821755
theorem B9619337 : Blo 2001435 9619337 := bstep (se 2 (by rfl) ⟨3607251, by rfl⟩ : syracuseStep 9619337 = 7214503) B7214503
theorem B25651565 : Blo 2001435 25651565 := bstep (se 3 (by rfl) ⟨4809668, by rfl⟩ : syracuseStep 25651565 = 9619337) B9619337
theorem B17101043 : Blo 2001435 17101043 := bstep (se 1 (by rfl) ⟨12825782, by rfl⟩ : syracuseStep 17101043 = 25651565) B25651565
theorem B11400695 : Blo 2001435 11400695 := bstep (se 1 (by rfl) ⟨8550521, by rfl⟩ : syracuseStep 11400695 = 17101043) B17101043
theorem B7600463 : Blo 2001435 7600463 := bstep (se 1 (by rfl) ⟨5700347, by rfl⟩ : syracuseStep 7600463 = 11400695) B11400695
theorem B5066975 : Blo 2001435 5066975 := bstep (se 1 (by rfl) ⟨3800231, by rfl⟩ : syracuseStep 5066975 = 7600463) B7600463
theorem B3377983 : Blo 2001435 3377983 := bstep (se 1 (by rfl) ⟨2533487, by rfl⟩ : syracuseStep 3377983 = 5066975) B5066975
theorem B4503977 : Blo 2001435 4503977 := bstep (se 2 (by rfl) ⟨1688991, by rfl⟩ : syracuseStep 4503977 = 3377983) B3377983
theorem B3002651 : Blo 2001435 3002651 := bstep (se 1 (by rfl) ⟨2251988, by rfl⟩ : syracuseStep 3002651 = 4503977) B4503977
theorem B2001767 : Blo 2001435 2001767 := bstep (se 1 (by rfl) ⟨1501325, by rfl⟩ : syracuseStep 2001767 = 3002651) B3002651
theorem B2251993 : Blo 2001435 2251993 := bbase (se 2 (by rfl) ⟨844497, by rfl⟩ : syracuseStep 2251993 = 1688995) (by norm_num)
theorem B3002657 : Blo 2001435 3002657 := bstep (se 2 (by rfl) ⟨1125996, by rfl⟩ : syracuseStep 3002657 = 2251993) B2251993
theorem B2001771 : Blo 2001435 2001771 := bstep (se 1 (by rfl) ⟨1501328, by rfl⟩ : syracuseStep 2001771 = 3002657) B3002657
theorem B5410901 : Blo 2001435 5410901 := bbase (se 8 (by rfl) ⟨31704, by rfl⟩ : syracuseStep 5410901 = 63409) (by norm_num)
theorem B3607267 : Blo 2001435 3607267 := bstep (se 1 (by rfl) ⟨2705450, by rfl⟩ : syracuseStep 3607267 = 5410901) B5410901
theorem B4809689 : Blo 2001435 4809689 := bstep (se 2 (by rfl) ⟨1803633, by rfl⟩ : syracuseStep 4809689 = 3607267) B3607267
theorem B3206459 : Blo 2001435 3206459 := bstep (se 1 (by rfl) ⟨2404844, by rfl⟩ : syracuseStep 3206459 = 4809689) B4809689
theorem B2137639 : Blo 2001435 2137639 := bstep (se 1 (by rfl) ⟨1603229, by rfl⟩ : syracuseStep 2137639 = 3206459) B3206459
theorem B2850185 : Blo 2001435 2850185 := bstep (se 2 (by rfl) ⟨1068819, by rfl⟩ : syracuseStep 2850185 = 2137639) B2137639
theorem B7600493 : Blo 2001435 7600493 := bstep (se 3 (by rfl) ⟨1425092, by rfl⟩ : syracuseStep 7600493 = 2850185) B2850185
theorem B5066995 : Blo 2001435 5066995 := bstep (se 1 (by rfl) ⟨3800246, by rfl⟩ : syracuseStep 5066995 = 7600493) B7600493
theorem B6755993 : Blo 2001435 6755993 := bstep (se 2 (by rfl) ⟨2533497, by rfl⟩ : syracuseStep 6755993 = 5066995) B5066995
theorem B4503995 : Blo 2001435 4503995 := bstep (se 1 (by rfl) ⟨3377996, by rfl⟩ : syracuseStep 4503995 = 6755993) B6755993
theorem B3002663 : Blo 2001435 3002663 := bstep (se 1 (by rfl) ⟨2251997, by rfl⟩ : syracuseStep 3002663 = 4503995) B4503995
theorem B2001775 : Blo 2001435 2001775 := bstep (se 1 (by rfl) ⟨1501331, by rfl⟩ : syracuseStep 2001775 = 3002663) B3002663
theorem B3002669 : Blo 2001435 3002669 := bbase (se 3 (by rfl) ⟨563000, by rfl⟩ : syracuseStep 3002669 = 1126001) (by norm_num)
theorem B2001779 : Blo 2001435 2001779 := bstep (se 1 (by rfl) ⟨1501334, by rfl⟩ : syracuseStep 2001779 = 3002669) B3002669
theorem B4504013 : Blo 2001435 4504013 := bbase (se 3 (by rfl) ⟨844502, by rfl⟩ : syracuseStep 4504013 = 1689005) (by norm_num)
theorem B3002675 : Blo 2001435 3002675 := bstep (se 1 (by rfl) ⟨2252006, by rfl⟩ : syracuseStep 3002675 = 4504013) B4504013
theorem B2001783 : Blo 2001435 2001783 := bstep (se 1 (by rfl) ⟨1501337, by rfl⟩ : syracuseStep 2001783 = 3002675) B3002675
theorem B2533513 : Blo 2001435 2533513 := bbase (se 2 (by rfl) ⟨950067, by rfl⟩ : syracuseStep 2533513 = 1900135) (by norm_num)
theorem B3378017 : Blo 2001435 3378017 := bstep (se 2 (by rfl) ⟨1266756, by rfl⟩ : syracuseStep 3378017 = 2533513) B2533513
theorem B2252011 : Blo 2001435 2252011 := bstep (se 1 (by rfl) ⟨1689008, by rfl⟩ : syracuseStep 2252011 = 3378017) B3378017
theorem B3002681 : Blo 2001435 3002681 := bstep (se 2 (by rfl) ⟨1126005, by rfl⟩ : syracuseStep 3002681 = 2252011) B2252011
theorem B2001787 : Blo 2001435 2001787 := bstep (se 1 (by rfl) ⟨1501340, by rfl⟩ : syracuseStep 2001787 = 3002681) B3002681
theorem B5077637 : Blo 2001435 5077637 := bbase (se 4 (by rfl) ⟨476028, by rfl⟩ : syracuseStep 5077637 = 952057) (by norm_num)
theorem B3385091 : Blo 2001435 3385091 := bstep (se 1 (by rfl) ⟨2538818, by rfl⟩ : syracuseStep 3385091 = 5077637) B5077637
theorem B2256727 : Blo 2001435 2256727 := bstep (se 1 (by rfl) ⟨1692545, by rfl⟩ : syracuseStep 2256727 = 3385091) B3385091
theorem B3008969 : Blo 2001435 3008969 := bstep (se 2 (by rfl) ⟨1128363, by rfl⟩ : syracuseStep 3008969 = 2256727) B2256727
theorem B2005979 : Blo 2001435 2005979 := bstep (se 1 (by rfl) ⟨1504484, by rfl⟩ : syracuseStep 2005979 = 3008969) B3008969
theorem B5349277 : Blo 2001435 5349277 := bstep (se 3 (by rfl) ⟨1002989, by rfl⟩ : syracuseStep 5349277 = 2005979) B2005979
theorem B7132369 : Blo 2001435 7132369 := bstep (se 2 (by rfl) ⟨2674638, by rfl⟩ : syracuseStep 7132369 = 5349277) B5349277
theorem B9509825 : Blo 2001435 9509825 := bstep (se 2 (by rfl) ⟨3566184, by rfl⟩ : syracuseStep 9509825 = 7132369) B7132369
theorem B6339883 : Blo 2001435 6339883 := bstep (se 1 (by rfl) ⟨4754912, by rfl⟩ : syracuseStep 6339883 = 9509825) B9509825
theorem B8453177 : Blo 2001435 8453177 := bstep (se 2 (by rfl) ⟨3169941, by rfl⟩ : syracuseStep 8453177 = 6339883) B6339883
theorem B5635451 : Blo 2001435 5635451 := bstep (se 1 (by rfl) ⟨4226588, by rfl⟩ : syracuseStep 5635451 = 8453177) B8453177
theorem B15027869 : Blo 2001435 15027869 := bstep (se 3 (by rfl) ⟨2817725, by rfl⟩ : syracuseStep 15027869 = 5635451) B5635451
theorem B10018579 : Blo 2001435 10018579 := bstep (se 1 (by rfl) ⟨7513934, by rfl⟩ : syracuseStep 10018579 = 15027869) B15027869
theorem B13358105 : Blo 2001435 13358105 := bstep (se 2 (by rfl) ⟨5009289, by rfl⟩ : syracuseStep 13358105 = 10018579) B10018579
theorem B8905403 : Blo 2001435 8905403 := bstep (se 1 (by rfl) ⟨6679052, by rfl⟩ : syracuseStep 8905403 = 13358105) B13358105
theorem B5936935 : Blo 2001435 5936935 := bstep (se 1 (by rfl) ⟨4452701, by rfl⟩ : syracuseStep 5936935 = 8905403) B8905403
theorem B7915913 : Blo 2001435 7915913 := bstep (se 2 (by rfl) ⟨2968467, by rfl⟩ : syracuseStep 7915913 = 5936935) B5936935
theorem B5277275 : Blo 2001435 5277275 := bstep (se 1 (by rfl) ⟨3957956, by rfl⟩ : syracuseStep 5277275 = 7915913) B7915913
theorem B3518183 : Blo 2001435 3518183 := bstep (se 1 (by rfl) ⟨2638637, by rfl⟩ : syracuseStep 3518183 = 5277275) B5277275
theorem B2345455 : Blo 2001435 2345455 := bstep (se 1 (by rfl) ⟨1759091, by rfl⟩ : syracuseStep 2345455 = 3518183) B3518183
theorem B12509093 : Blo 2001435 12509093 := bstep (se 4 (by rfl) ⟨1172727, by rfl⟩ : syracuseStep 12509093 = 2345455) B2345455
theorem B33357581 : Blo 2001435 33357581 := bstep (se 3 (by rfl) ⟨6254546, by rfl⟩ : syracuseStep 33357581 = 12509093) B12509093
theorem B22238387 : Blo 2001435 22238387 := bstep (se 1 (by rfl) ⟨16678790, by rfl⟩ : syracuseStep 22238387 = 33357581) B33357581
theorem B14825591 : Blo 2001435 14825591 := bstep (se 1 (by rfl) ⟨11119193, by rfl⟩ : syracuseStep 14825591 = 22238387) B22238387
theorem B9883727 : Blo 2001435 9883727 := bstep (se 1 (by rfl) ⟨7412795, by rfl⟩ : syracuseStep 9883727 = 14825591) B14825591
theorem B6589151 : Blo 2001435 6589151 := bstep (se 1 (by rfl) ⟨4941863, by rfl⟩ : syracuseStep 6589151 = 9883727) B9883727
theorem B4392767 : Blo 2001435 4392767 := bstep (se 1 (by rfl) ⟨3294575, by rfl⟩ : syracuseStep 4392767 = 6589151) B6589151
theorem B11714045 : Blo 2001435 11714045 := bstep (se 3 (by rfl) ⟨2196383, by rfl⟩ : syracuseStep 11714045 = 4392767) B4392767
theorem B31237453 : Blo 2001435 31237453 := bstep (se 3 (by rfl) ⟨5857022, by rfl⟩ : syracuseStep 31237453 = 11714045) B11714045
theorem B166599749 : Blo 2001435 166599749 := bstep (se 4 (by rfl) ⟨15618726, by rfl⟩ : syracuseStep 166599749 = 31237453) B31237453
theorem B111066499 : Blo 2001435 111066499 := bstep (se 1 (by rfl) ⟨83299874, by rfl⟩ : syracuseStep 111066499 = 166599749) B166599749
theorem B148088665 : Blo 2001435 148088665 := bstep (se 2 (by rfl) ⟨55533249, by rfl⟩ : syracuseStep 148088665 = 111066499) B111066499
theorem B197451553 : Blo 2001435 197451553 := bstep (se 2 (by rfl) ⟨74044332, by rfl⟩ : syracuseStep 197451553 = 148088665) B148088665
theorem B263268737 : Blo 2001435 263268737 := bstep (se 2 (by rfl) ⟨98725776, by rfl⟩ : syracuseStep 263268737 = 197451553) B197451553
theorem B175512491 : Blo 2001435 175512491 := bstep (se 1 (by rfl) ⟨131634368, by rfl⟩ : syracuseStep 175512491 = 263268737) B263268737
theorem B117008327 : Blo 2001435 117008327 := bstep (se 1 (by rfl) ⟨87756245, by rfl⟩ : syracuseStep 117008327 = 175512491) B175512491
theorem B78005551 : Blo 2001435 78005551 := bstep (se 1 (by rfl) ⟨58504163, by rfl⟩ : syracuseStep 78005551 = 117008327) B117008327
theorem B104007401 : Blo 2001435 104007401 := bstep (se 2 (by rfl) ⟨39002775, by rfl⟩ : syracuseStep 104007401 = 78005551) B78005551
theorem B69338267 : Blo 2001435 69338267 := bstep (se 1 (by rfl) ⟨52003700, by rfl⟩ : syracuseStep 69338267 = 104007401) B104007401
theorem B46225511 : Blo 2001435 46225511 := bstep (se 1 (by rfl) ⟨34669133, by rfl⟩ : syracuseStep 46225511 = 69338267) B69338267
theorem B30817007 : Blo 2001435 30817007 := bstep (se 1 (by rfl) ⟨23112755, by rfl⟩ : syracuseStep 30817007 = 46225511) B46225511
theorem B20544671 : Blo 2001435 20544671 := bstep (se 1 (by rfl) ⟨15408503, by rfl⟩ : syracuseStep 20544671 = 30817007) B30817007
theorem B13696447 : Blo 2001435 13696447 := bstep (se 1 (by rfl) ⟨10272335, by rfl⟩ : syracuseStep 13696447 = 20544671) B20544671
theorem B18261929 : Blo 2001435 18261929 := bstep (se 2 (by rfl) ⟨6848223, by rfl⟩ : syracuseStep 18261929 = 13696447) B13696447
theorem B12174619 : Blo 2001435 12174619 := bstep (se 1 (by rfl) ⟨9130964, by rfl⟩ : syracuseStep 12174619 = 18261929) B18261929
theorem B16232825 : Blo 2001435 16232825 := bstep (se 2 (by rfl) ⟨6087309, by rfl⟩ : syracuseStep 16232825 = 12174619) B12174619
theorem B43287533 : Blo 2001435 43287533 := bstep (se 3 (by rfl) ⟨8116412, by rfl⟩ : syracuseStep 43287533 = 16232825) B16232825
theorem B28858355 : Blo 2001435 28858355 := bstep (se 1 (by rfl) ⟨21643766, by rfl⟩ : syracuseStep 28858355 = 43287533) B43287533
theorem B19238903 : Blo 2001435 19238903 := bstep (se 1 (by rfl) ⟨14429177, by rfl⟩ : syracuseStep 19238903 = 28858355) B28858355
theorem B12825935 : Blo 2001435 12825935 := bstep (se 1 (by rfl) ⟨9619451, by rfl⟩ : syracuseStep 12825935 = 19238903) B19238903
theorem B8550623 : Blo 2001435 8550623 := bstep (se 1 (by rfl) ⟨6412967, by rfl⟩ : syracuseStep 8550623 = 12825935) B12825935
theorem B22801661 : Blo 2001435 22801661 := bstep (se 3 (by rfl) ⟨4275311, by rfl⟩ : syracuseStep 22801661 = 8550623) B8550623
theorem B15201107 : Blo 2001435 15201107 := bstep (se 1 (by rfl) ⟨11400830, by rfl⟩ : syracuseStep 15201107 = 22801661) B22801661
theorem B10134071 : Blo 2001435 10134071 := bstep (se 1 (by rfl) ⟨7600553, by rfl⟩ : syracuseStep 10134071 = 15201107) B15201107
theorem B6756047 : Blo 2001435 6756047 := bstep (se 1 (by rfl) ⟨5067035, by rfl⟩ : syracuseStep 6756047 = 10134071) B10134071
theorem B4504031 : Blo 2001435 4504031 := bstep (se 1 (by rfl) ⟨3378023, by rfl⟩ : syracuseStep 4504031 = 6756047) B6756047
theorem B3002687 : Blo 2001435 3002687 := bstep (se 1 (by rfl) ⟨2252015, by rfl⟩ : syracuseStep 3002687 = 4504031) B4504031
theorem B2001791 : Blo 2001435 2001791 := bstep (se 1 (by rfl) ⟨1501343, by rfl⟩ : syracuseStep 2001791 = 3002687) B3002687
theorem B3002693 : Blo 2001435 3002693 := bbase (se 4 (by rfl) ⟨281502, by rfl⟩ : syracuseStep 3002693 = 563005) (by norm_num)
theorem B2001795 : Blo 2001435 2001795 := bstep (se 1 (by rfl) ⟨1501346, by rfl⟩ : syracuseStep 2001795 = 3002693) B3002693
theorem B3378037 : Blo 2001435 3378037 := bbase (se 5 (by rfl) ⟨158345, by rfl⟩ : syracuseStep 3378037 = 316691) (by norm_num)
theorem B4504049 : Blo 2001435 4504049 := bstep (se 2 (by rfl) ⟨1689018, by rfl⟩ : syracuseStep 4504049 = 3378037) B3378037
theorem B3002699 : Blo 2001435 3002699 := bstep (se 1 (by rfl) ⟨2252024, by rfl⟩ : syracuseStep 3002699 = 4504049) B4504049
theorem B2001799 : Blo 2001435 2001799 := bstep (se 1 (by rfl) ⟨1501349, by rfl⟩ : syracuseStep 2001799 = 3002699) B3002699
theorem B2252029 : Blo 2001435 2252029 := bbase (se 3 (by rfl) ⟨422255, by rfl⟩ : syracuseStep 2252029 = 844511) (by norm_num)
theorem B3002705 : Blo 2001435 3002705 := bstep (se 2 (by rfl) ⟨1126014, by rfl⟩ : syracuseStep 3002705 = 2252029) B2252029
theorem B2001803 : Blo 2001435 2001803 := bstep (se 1 (by rfl) ⟨1501352, by rfl⟩ : syracuseStep 2001803 = 3002705) B3002705
theorem B6756101 : Blo 2001435 6756101 := bbase (se 4 (by rfl) ⟨633384, by rfl⟩ : syracuseStep 6756101 = 1266769) (by norm_num)
theorem B4504067 : Blo 2001435 4504067 := bstep (se 1 (by rfl) ⟨3378050, by rfl⟩ : syracuseStep 4504067 = 6756101) B6756101
theorem B3002711 : Blo 2001435 3002711 := bstep (se 1 (by rfl) ⟨2252033, by rfl⟩ : syracuseStep 3002711 = 4504067) B4504067
theorem B2001807 : Blo 2001435 2001807 := bstep (se 1 (by rfl) ⟨1501355, by rfl⟩ : syracuseStep 2001807 = 3002711) B3002711
theorem B3002717 : Blo 2001435 3002717 := bbase (se 3 (by rfl) ⟨563009, by rfl⟩ : syracuseStep 3002717 = 1126019) (by norm_num)
theorem B2001811 : Blo 2001435 2001811 := bstep (se 1 (by rfl) ⟨1501358, by rfl⟩ : syracuseStep 2001811 = 3002717) B3002717
theorem B4504085 : Blo 2001435 4504085 := bbase (se 6 (by rfl) ⟨105564, by rfl⟩ : syracuseStep 4504085 = 211129) (by norm_num)
theorem B3002723 : Blo 2001435 3002723 := bstep (se 1 (by rfl) ⟨2252042, by rfl⟩ : syracuseStep 3002723 = 4504085) B4504085
theorem B2001815 : Blo 2001435 2001815 := bstep (se 1 (by rfl) ⟨1501361, by rfl⟩ : syracuseStep 2001815 = 3002723) B3002723
theorem B7600661 : Blo 2001435 7600661 := bbase (se 6 (by rfl) ⟨178140, by rfl⟩ : syracuseStep 7600661 = 356281) (by norm_num)
theorem B5067107 : Blo 2001435 5067107 := bstep (se 1 (by rfl) ⟨3800330, by rfl⟩ : syracuseStep 5067107 = 7600661) B7600661
theorem B3378071 : Blo 2001435 3378071 := bstep (se 1 (by rfl) ⟨2533553, by rfl⟩ : syracuseStep 3378071 = 5067107) B5067107
theorem B2252047 : Blo 2001435 2252047 := bstep (se 1 (by rfl) ⟨1689035, by rfl⟩ : syracuseStep 2252047 = 3378071) B3378071
theorem B3002729 : Blo 2001435 3002729 := bstep (se 2 (by rfl) ⟨1126023, by rfl⟩ : syracuseStep 3002729 = 2252047) B2252047
theorem B2001819 : Blo 2001435 2001819 := bstep (se 1 (by rfl) ⟨1501364, by rfl⟩ : syracuseStep 2001819 = 3002729) B3002729
theorem B11401013 : Blo 2001435 11401013 := bbase (se 5 (by rfl) ⟨534422, by rfl⟩ : syracuseStep 11401013 = 1068845) (by norm_num)
theorem B7600675 : Blo 2001435 7600675 := bstep (se 1 (by rfl) ⟨5700506, by rfl⟩ : syracuseStep 7600675 = 11401013) B11401013
theorem B10134233 : Blo 2001435 10134233 := bstep (se 2 (by rfl) ⟨3800337, by rfl⟩ : syracuseStep 10134233 = 7600675) B7600675
theorem B6756155 : Blo 2001435 6756155 := bstep (se 1 (by rfl) ⟨5067116, by rfl⟩ : syracuseStep 6756155 = 10134233) B10134233
theorem B4504103 : Blo 2001435 4504103 := bstep (se 1 (by rfl) ⟨3378077, by rfl⟩ : syracuseStep 4504103 = 6756155) B6756155
theorem B3002735 : Blo 2001435 3002735 := bstep (se 1 (by rfl) ⟨2252051, by rfl⟩ : syracuseStep 3002735 = 4504103) B4504103
theorem B2001823 : Blo 2001435 2001823 := bstep (se 1 (by rfl) ⟨1501367, by rfl⟩ : syracuseStep 2001823 = 3002735) B3002735
theorem B3002741 : Blo 2001435 3002741 := bbase (se 5 (by rfl) ⟨140753, by rfl⟩ : syracuseStep 3002741 = 281507) (by norm_num)
theorem B2001827 : Blo 2001435 2001827 := bstep (se 1 (by rfl) ⟨1501370, by rfl⟩ : syracuseStep 2001827 = 3002741) B3002741
theorem B3206549 : Blo 2001435 3206549 := bbase (se 6 (by rfl) ⟨75153, by rfl⟩ : syracuseStep 3206549 = 150307) (by norm_num)
theorem B2137699 : Blo 2001435 2137699 := bstep (se 1 (by rfl) ⟨1603274, by rfl⟩ : syracuseStep 2137699 = 3206549) B3206549
theorem B2850265 : Blo 2001435 2850265 := bstep (se 2 (by rfl) ⟨1068849, by rfl⟩ : syracuseStep 2850265 = 2137699) B2137699
theorem B3800353 : Blo 2001435 3800353 := bstep (se 2 (by rfl) ⟨1425132, by rfl⟩ : syracuseStep 3800353 = 2850265) B2850265
theorem B5067137 : Blo 2001435 5067137 := bstep (se 2 (by rfl) ⟨1900176, by rfl⟩ : syracuseStep 5067137 = 3800353) B3800353
theorem B3378091 : Blo 2001435 3378091 := bstep (se 1 (by rfl) ⟨2533568, by rfl⟩ : syracuseStep 3378091 = 5067137) B5067137
theorem B4504121 : Blo 2001435 4504121 := bstep (se 2 (by rfl) ⟨1689045, by rfl⟩ : syracuseStep 4504121 = 3378091) B3378091
theorem B3002747 : Blo 2001435 3002747 := bstep (se 1 (by rfl) ⟨2252060, by rfl⟩ : syracuseStep 3002747 = 4504121) B4504121
theorem B2001831 : Blo 2001435 2001831 := bstep (se 1 (by rfl) ⟨1501373, by rfl⟩ : syracuseStep 2001831 = 3002747) B3002747
theorem B2252065 : Blo 2001435 2252065 := bbase (se 2 (by rfl) ⟨844524, by rfl⟩ : syracuseStep 2252065 = 1689049) (by norm_num)
theorem B3002753 : Blo 2001435 3002753 := bstep (se 2 (by rfl) ⟨1126032, by rfl⟩ : syracuseStep 3002753 = 2252065) B2252065
theorem B2001835 : Blo 2001435 2001835 := bstep (se 1 (by rfl) ⟨1501376, by rfl⟩ : syracuseStep 2001835 = 3002753) B3002753
theorem B5067157 : Blo 2001435 5067157 := bbase (se 6 (by rfl) ⟨118761, by rfl⟩ : syracuseStep 5067157 = 237523) (by norm_num)
theorem B6756209 : Blo 2001435 6756209 := bstep (se 2 (by rfl) ⟨2533578, by rfl⟩ : syracuseStep 6756209 = 5067157) B5067157
theorem B4504139 : Blo 2001435 4504139 := bstep (se 1 (by rfl) ⟨3378104, by rfl⟩ : syracuseStep 4504139 = 6756209) B6756209
theorem B3002759 : Blo 2001435 3002759 := bstep (se 1 (by rfl) ⟨2252069, by rfl⟩ : syracuseStep 3002759 = 4504139) B4504139
theorem B2001839 : Blo 2001435 2001839 := bstep (se 1 (by rfl) ⟨1501379, by rfl⟩ : syracuseStep 2001839 = 3002759) B3002759
theorem B3002765 : Blo 2001435 3002765 := bbase (se 3 (by rfl) ⟨563018, by rfl⟩ : syracuseStep 3002765 = 1126037) (by norm_num)
theorem B2001843 : Blo 2001435 2001843 := bstep (se 1 (by rfl) ⟨1501382, by rfl⟩ : syracuseStep 2001843 = 3002765) B3002765
theorem B4504157 : Blo 2001435 4504157 := bbase (se 3 (by rfl) ⟨844529, by rfl⟩ : syracuseStep 4504157 = 1689059) (by norm_num)
theorem B3002771 : Blo 2001435 3002771 := bstep (se 1 (by rfl) ⟨2252078, by rfl⟩ : syracuseStep 3002771 = 4504157) B4504157
theorem B2001847 : Blo 2001435 2001847 := bstep (se 1 (by rfl) ⟨1501385, by rfl⟩ : syracuseStep 2001847 = 3002771) B3002771
theorem B3378125 : Blo 2001435 3378125 := bbase (se 3 (by rfl) ⟨633398, by rfl⟩ : syracuseStep 3378125 = 1266797) (by norm_num)
theorem B2252083 : Blo 2001435 2252083 := bstep (se 1 (by rfl) ⟨1689062, by rfl⟩ : syracuseStep 2252083 = 3378125) B3378125
theorem B3002777 : Blo 2001435 3002777 := bstep (se 2 (by rfl) ⟨1126041, by rfl⟩ : syracuseStep 3002777 = 2252083) B2252083
theorem B2001851 : Blo 2001435 2001851 := bstep (se 1 (by rfl) ⟨1501388, by rfl⟩ : syracuseStep 2001851 = 3002777) B3002777
theorem B13696885 : Blo 2001435 13696885 := bbase (se 5 (by rfl) ⟨642041, by rfl⟩ : syracuseStep 13696885 = 1284083) (by norm_num)
theorem B18262513 : Blo 2001435 18262513 := bstep (se 2 (by rfl) ⟨6848442, by rfl⟩ : syracuseStep 18262513 = 13696885) B13696885
theorem B24350017 : Blo 2001435 24350017 := bstep (se 2 (by rfl) ⟨9131256, by rfl⟩ : syracuseStep 24350017 = 18262513) B18262513
theorem B32466689 : Blo 2001435 32466689 := bstep (se 2 (by rfl) ⟨12175008, by rfl⟩ : syracuseStep 32466689 = 24350017) B24350017
theorem B21644459 : Blo 2001435 21644459 := bstep (se 1 (by rfl) ⟨16233344, by rfl⟩ : syracuseStep 21644459 = 32466689) B32466689
theorem B14429639 : Blo 2001435 14429639 := bstep (se 1 (by rfl) ⟨10822229, by rfl⟩ : syracuseStep 14429639 = 21644459) B21644459
theorem B9619759 : Blo 2001435 9619759 := bstep (se 1 (by rfl) ⟨7214819, by rfl⟩ : syracuseStep 9619759 = 14429639) B14429639
theorem B12826345 : Blo 2001435 12826345 := bstep (se 2 (by rfl) ⟨4809879, by rfl⟩ : syracuseStep 12826345 = 9619759) B9619759
theorem B17101793 : Blo 2001435 17101793 := bstep (se 2 (by rfl) ⟨6413172, by rfl⟩ : syracuseStep 17101793 = 12826345) B12826345
theorem B11401195 : Blo 2001435 11401195 := bstep (se 1 (by rfl) ⟨8550896, by rfl⟩ : syracuseStep 11401195 = 17101793) B17101793
theorem B15201593 : Blo 2001435 15201593 := bstep (se 2 (by rfl) ⟨5700597, by rfl⟩ : syracuseStep 15201593 = 11401195) B11401195
theorem B10134395 : Blo 2001435 10134395 := bstep (se 1 (by rfl) ⟨7600796, by rfl⟩ : syracuseStep 10134395 = 15201593) B15201593
theorem B6756263 : Blo 2001435 6756263 := bstep (se 1 (by rfl) ⟨5067197, by rfl⟩ : syracuseStep 6756263 = 10134395) B10134395
theorem B4504175 : Blo 2001435 4504175 := bstep (se 1 (by rfl) ⟨3378131, by rfl⟩ : syracuseStep 4504175 = 6756263) B6756263
theorem B3002783 : Blo 2001435 3002783 := bstep (se 1 (by rfl) ⟨2252087, by rfl⟩ : syracuseStep 3002783 = 4504175) B4504175
theorem B2001855 : Blo 2001435 2001855 := bstep (se 1 (by rfl) ⟨1501391, by rfl⟩ : syracuseStep 2001855 = 3002783) B3002783
theorem B3002789 : Blo 2001435 3002789 := bbase (se 4 (by rfl) ⟨281511, by rfl⟩ : syracuseStep 3002789 = 563023) (by norm_num)
theorem B2001859 : Blo 2001435 2001859 := bstep (se 1 (by rfl) ⟨1501394, by rfl⟩ : syracuseStep 2001859 = 3002789) B3002789
theorem B2533609 : Blo 2001435 2533609 := bbase (se 2 (by rfl) ⟨950103, by rfl⟩ : syracuseStep 2533609 = 1900207) (by norm_num)
theorem B3378145 : Blo 2001435 3378145 := bstep (se 2 (by rfl) ⟨1266804, by rfl⟩ : syracuseStep 3378145 = 2533609) B2533609
theorem B4504193 : Blo 2001435 4504193 := bstep (se 2 (by rfl) ⟨1689072, by rfl⟩ : syracuseStep 4504193 = 3378145) B3378145
theorem B3002795 : Blo 2001435 3002795 := bstep (se 1 (by rfl) ⟨2252096, by rfl⟩ : syracuseStep 3002795 = 4504193) B4504193
theorem B2001863 : Blo 2001435 2001863 := bstep (se 1 (by rfl) ⟨1501397, by rfl⟩ : syracuseStep 2001863 = 3002795) B3002795
theorem B2252101 : Blo 2001435 2252101 := bbase (se 4 (by rfl) ⟨211134, by rfl⟩ : syracuseStep 2252101 = 422269) (by norm_num)
theorem B3002801 : Blo 2001435 3002801 := bstep (se 2 (by rfl) ⟨1126050, by rfl⟩ : syracuseStep 3002801 = 2252101) B2252101
theorem B2001867 : Blo 2001435 2001867 := bstep (se 1 (by rfl) ⟨1501400, by rfl⟩ : syracuseStep 2001867 = 3002801) B3002801
theorem B3800429 : Blo 2001435 3800429 := bbase (se 3 (by rfl) ⟨712580, by rfl⟩ : syracuseStep 3800429 = 1425161) (by norm_num)
theorem B2533619 : Blo 2001435 2533619 := bstep (se 1 (by rfl) ⟨1900214, by rfl⟩ : syracuseStep 2533619 = 3800429) B3800429
theorem B6756317 : Blo 2001435 6756317 := bstep (se 3 (by rfl) ⟨1266809, by rfl⟩ : syracuseStep 6756317 = 2533619) B2533619
theorem B4504211 : Blo 2001435 4504211 := bstep (se 1 (by rfl) ⟨3378158, by rfl⟩ : syracuseStep 4504211 = 6756317) B6756317
theorem B3002807 : Blo 2001435 3002807 := bstep (se 1 (by rfl) ⟨2252105, by rfl⟩ : syracuseStep 3002807 = 4504211) B4504211
theorem B2001871 : Blo 2001435 2001871 := bstep (se 1 (by rfl) ⟨1501403, by rfl⟩ : syracuseStep 2001871 = 3002807) B3002807
theorem B3002813 : Blo 2001435 3002813 := bbase (se 3 (by rfl) ⟨563027, by rfl⟩ : syracuseStep 3002813 = 1126055) (by norm_num)
theorem B2001875 : Blo 2001435 2001875 := bstep (se 1 (by rfl) ⟨1501406, by rfl⟩ : syracuseStep 2001875 = 3002813) B3002813
theorem B4504229 : Blo 2001435 4504229 := bbase (se 4 (by rfl) ⟨422271, by rfl⟩ : syracuseStep 4504229 = 844543) (by norm_num)
theorem B3002819 : Blo 2001435 3002819 := bstep (se 1 (by rfl) ⟨2252114, by rfl⟩ : syracuseStep 3002819 = 4504229) B4504229
theorem B2001879 : Blo 2001435 2001879 := bstep (se 1 (by rfl) ⟨1501409, by rfl⟩ : syracuseStep 2001879 = 3002819) B3002819
theorem B5067269 : Blo 2001435 5067269 := bbase (se 4 (by rfl) ⟨475056, by rfl⟩ : syracuseStep 5067269 = 950113) (by norm_num)
theorem B3378179 : Blo 2001435 3378179 := bstep (se 1 (by rfl) ⟨2533634, by rfl⟩ : syracuseStep 3378179 = 5067269) B5067269
theorem B2252119 : Blo 2001435 2252119 := bstep (se 1 (by rfl) ⟨1689089, by rfl⟩ : syracuseStep 2252119 = 3378179) B3378179
theorem B3002825 : Blo 2001435 3002825 := bstep (se 2 (by rfl) ⟨1126059, by rfl⟩ : syracuseStep 3002825 = 2252119) B2252119
theorem B2001883 : Blo 2001435 2001883 := bstep (se 1 (by rfl) ⟨1501412, by rfl⟩ : syracuseStep 2001883 = 3002825) B3002825
theorem B4275517 : Blo 2001435 4275517 := bbase (se 3 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 4275517 = 1603319) (by norm_num)
theorem B5700689 : Blo 2001435 5700689 := bstep (se 2 (by rfl) ⟨2137758, by rfl⟩ : syracuseStep 5700689 = 4275517) B4275517
theorem B3800459 : Blo 2001435 3800459 := bstep (se 1 (by rfl) ⟨2850344, by rfl⟩ : syracuseStep 3800459 = 5700689) B5700689
theorem B10134557 : Blo 2001435 10134557 := bstep (se 3 (by rfl) ⟨1900229, by rfl⟩ : syracuseStep 10134557 = 3800459) B3800459
theorem B6756371 : Blo 2001435 6756371 := bstep (se 1 (by rfl) ⟨5067278, by rfl⟩ : syracuseStep 6756371 = 10134557) B10134557
theorem B4504247 : Blo 2001435 4504247 := bstep (se 1 (by rfl) ⟨3378185, by rfl⟩ : syracuseStep 4504247 = 6756371) B6756371
theorem B3002831 : Blo 2001435 3002831 := bstep (se 1 (by rfl) ⟨2252123, by rfl⟩ : syracuseStep 3002831 = 4504247) B4504247
theorem B2001887 : Blo 2001435 2001887 := bstep (se 1 (by rfl) ⟨1501415, by rfl⟩ : syracuseStep 2001887 = 3002831) B3002831
theorem B3002837 : Blo 2001435 3002837 := bbase (se 7 (by rfl) ⟨35189, by rfl⟩ : syracuseStep 3002837 = 70379) (by norm_num)
theorem B2001891 : Blo 2001435 2001891 := bstep (se 1 (by rfl) ⟨1501418, by rfl⟩ : syracuseStep 2001891 = 3002837) B3002837
theorem B7600949 : Blo 2001435 7600949 := bbase (se 5 (by rfl) ⟨356294, by rfl⟩ : syracuseStep 7600949 = 712589) (by norm_num)
theorem B5067299 : Blo 2001435 5067299 := bstep (se 1 (by rfl) ⟨3800474, by rfl⟩ : syracuseStep 5067299 = 7600949) B7600949
theorem B3378199 : Blo 2001435 3378199 := bstep (se 1 (by rfl) ⟨2533649, by rfl⟩ : syracuseStep 3378199 = 5067299) B5067299
theorem B4504265 : Blo 2001435 4504265 := bstep (se 2 (by rfl) ⟨1689099, by rfl⟩ : syracuseStep 4504265 = 3378199) B3378199
theorem B3002843 : Blo 2001435 3002843 := bstep (se 1 (by rfl) ⟨2252132, by rfl⟩ : syracuseStep 3002843 = 4504265) B4504265
theorem B2001895 : Blo 2001435 2001895 := bstep (se 1 (by rfl) ⟨1501421, by rfl⟩ : syracuseStep 2001895 = 3002843) B3002843
theorem B2252137 : Blo 2001435 2252137 := bbase (se 2 (by rfl) ⟨844551, by rfl⟩ : syracuseStep 2252137 = 1689103) (by norm_num)
theorem B3002849 : Blo 2001435 3002849 := bstep (se 2 (by rfl) ⟨1126068, by rfl⟩ : syracuseStep 3002849 = 2252137) B2252137
theorem B2001899 : Blo 2001435 2001899 := bstep (se 1 (by rfl) ⟨1501424, by rfl⟩ : syracuseStep 2001899 = 3002849) B3002849
theorem B2029217 : Blo 2001435 2029217 := bbase (se 2 (by rfl) ⟨760956, by rfl⟩ : syracuseStep 2029217 = 1521913) (by norm_num)
theorem B21644981 : Blo 2001435 21644981 := bstep (se 5 (by rfl) ⟨1014608, by rfl⟩ : syracuseStep 21644981 = 2029217) B2029217
theorem B14429987 : Blo 2001435 14429987 := bstep (se 1 (by rfl) ⟨10822490, by rfl⟩ : syracuseStep 14429987 = 21644981) B21644981
theorem B9619991 : Blo 2001435 9619991 := bstep (se 1 (by rfl) ⟨7214993, by rfl⟩ : syracuseStep 9619991 = 14429987) B14429987
theorem B6413327 : Blo 2001435 6413327 := bstep (se 1 (by rfl) ⟨4809995, by rfl⟩ : syracuseStep 6413327 = 9619991) B9619991
theorem B4275551 : Blo 2001435 4275551 := bstep (se 1 (by rfl) ⟨3206663, by rfl⟩ : syracuseStep 4275551 = 6413327) B6413327
theorem B11401469 : Blo 2001435 11401469 := bstep (se 3 (by rfl) ⟨2137775, by rfl⟩ : syracuseStep 11401469 = 4275551) B4275551
theorem B7600979 : Blo 2001435 7600979 := bstep (se 1 (by rfl) ⟨5700734, by rfl⟩ : syracuseStep 7600979 = 11401469) B11401469
theorem B5067319 : Blo 2001435 5067319 := bstep (se 1 (by rfl) ⟨3800489, by rfl⟩ : syracuseStep 5067319 = 7600979) B7600979
theorem B6756425 : Blo 2001435 6756425 := bstep (se 2 (by rfl) ⟨2533659, by rfl⟩ : syracuseStep 6756425 = 5067319) B5067319
theorem B4504283 : Blo 2001435 4504283 := bstep (se 1 (by rfl) ⟨3378212, by rfl⟩ : syracuseStep 4504283 = 6756425) B6756425
theorem B3002855 : Blo 2001435 3002855 := bstep (se 1 (by rfl) ⟨2252141, by rfl⟩ : syracuseStep 3002855 = 4504283) B4504283
theorem B2001903 : Blo 2001435 2001903 := bstep (se 1 (by rfl) ⟨1501427, by rfl⟩ : syracuseStep 2001903 = 3002855) B3002855
theorem B3002861 : Blo 2001435 3002861 := bbase (se 3 (by rfl) ⟨563036, by rfl⟩ : syracuseStep 3002861 = 1126073) (by norm_num)
theorem B2001907 : Blo 2001435 2001907 := bstep (se 1 (by rfl) ⟨1501430, by rfl⟩ : syracuseStep 2001907 = 3002861) B3002861
theorem B4504301 : Blo 2001435 4504301 := bbase (se 3 (by rfl) ⟨844556, by rfl⟩ : syracuseStep 4504301 = 1689113) (by norm_num)
theorem B3002867 : Blo 2001435 3002867 := bstep (se 1 (by rfl) ⟨2252150, by rfl⟩ : syracuseStep 3002867 = 4504301) B4504301
theorem B2001911 : Blo 2001435 2001911 := bstep (se 1 (by rfl) ⟨1501433, by rfl⟩ : syracuseStep 2001911 = 3002867) B3002867
theorem B2137789 : Blo 2001435 2137789 := bbase (se 3 (by rfl) ⟨400835, by rfl⟩ : syracuseStep 2137789 = 801671) (by norm_num)
theorem B2850385 : Blo 2001435 2850385 := bstep (se 2 (by rfl) ⟨1068894, by rfl⟩ : syracuseStep 2850385 = 2137789) B2137789
theorem B3800513 : Blo 2001435 3800513 := bstep (se 2 (by rfl) ⟨1425192, by rfl⟩ : syracuseStep 3800513 = 2850385) B2850385
theorem B2533675 : Blo 2001435 2533675 := bstep (se 1 (by rfl) ⟨1900256, by rfl⟩ : syracuseStep 2533675 = 3800513) B3800513
theorem B3378233 : Blo 2001435 3378233 := bstep (se 2 (by rfl) ⟨1266837, by rfl⟩ : syracuseStep 3378233 = 2533675) B2533675
theorem B2252155 : Blo 2001435 2252155 := bstep (se 1 (by rfl) ⟨1689116, by rfl⟩ : syracuseStep 2252155 = 3378233) B3378233
theorem B3002873 : Blo 2001435 3002873 := bstep (se 2 (by rfl) ⟨1126077, by rfl⟩ : syracuseStep 3002873 = 2252155) B2252155
theorem B2001915 : Blo 2001435 2001915 := bstep (se 1 (by rfl) ⟨1501436, by rfl⟩ : syracuseStep 2001915 = 3002873) B3002873
theorem B3852373 : Blo 2001435 3852373 := bbase (se 8 (by rfl) ⟨22572, by rfl⟩ : syracuseStep 3852373 = 45145) (by norm_num)
theorem B5136497 : Blo 2001435 5136497 := bstep (se 2 (by rfl) ⟨1926186, by rfl⟩ : syracuseStep 5136497 = 3852373) B3852373
theorem B3424331 : Blo 2001435 3424331 := bstep (se 1 (by rfl) ⟨2568248, by rfl⟩ : syracuseStep 3424331 = 5136497) B5136497
theorem B2282887 : Blo 2001435 2282887 := bstep (se 1 (by rfl) ⟨1712165, by rfl⟩ : syracuseStep 2282887 = 3424331) B3424331
theorem B12175397 : Blo 2001435 12175397 := bstep (se 4 (by rfl) ⟨1141443, by rfl⟩ : syracuseStep 12175397 = 2282887) B2282887
theorem B8116931 : Blo 2001435 8116931 := bstep (se 1 (by rfl) ⟨6087698, by rfl⟩ : syracuseStep 8116931 = 12175397) B12175397
theorem B21645149 : Blo 2001435 21645149 := bstep (se 3 (by rfl) ⟨4058465, by rfl⟩ : syracuseStep 21645149 = 8116931) B8116931
theorem B57720397 : Blo 2001435 57720397 := bstep (se 3 (by rfl) ⟨10822574, by rfl⟩ : syracuseStep 57720397 = 21645149) B21645149
theorem B76960529 : Blo 2001435 76960529 := bstep (se 2 (by rfl) ⟨28860198, by rfl⟩ : syracuseStep 76960529 = 57720397) B57720397
theorem B51307019 : Blo 2001435 51307019 := bstep (se 1 (by rfl) ⟨38480264, by rfl⟩ : syracuseStep 51307019 = 76960529) B76960529
theorem B34204679 : Blo 2001435 34204679 := bstep (se 1 (by rfl) ⟨25653509, by rfl⟩ : syracuseStep 34204679 = 51307019) B51307019
theorem B22803119 : Blo 2001435 22803119 := bstep (se 1 (by rfl) ⟨17102339, by rfl⟩ : syracuseStep 22803119 = 34204679) B34204679
theorem B15202079 : Blo 2001435 15202079 := bstep (se 1 (by rfl) ⟨11401559, by rfl⟩ : syracuseStep 15202079 = 22803119) B22803119
theorem B10134719 : Blo 2001435 10134719 := bstep (se 1 (by rfl) ⟨7601039, by rfl⟩ : syracuseStep 10134719 = 15202079) B15202079
theorem B6756479 : Blo 2001435 6756479 := bstep (se 1 (by rfl) ⟨5067359, by rfl⟩ : syracuseStep 6756479 = 10134719) B10134719
theorem B4504319 : Blo 2001435 4504319 := bstep (se 1 (by rfl) ⟨3378239, by rfl⟩ : syracuseStep 4504319 = 6756479) B6756479
theorem B3002879 : Blo 2001435 3002879 := bstep (se 1 (by rfl) ⟨2252159, by rfl⟩ : syracuseStep 3002879 = 4504319) B4504319
theorem B2001919 : Blo 2001435 2001919 := bstep (se 1 (by rfl) ⟨1501439, by rfl⟩ : syracuseStep 2001919 = 3002879) B3002879
theorem B3002885 : Blo 2001435 3002885 := bbase (se 4 (by rfl) ⟨281520, by rfl⟩ : syracuseStep 3002885 = 563041) (by norm_num)
theorem B2001923 : Blo 2001435 2001923 := bstep (se 1 (by rfl) ⟨1501442, by rfl⟩ : syracuseStep 2001923 = 3002885) B3002885
theorem B3378253 : Blo 2001435 3378253 := bbase (se 3 (by rfl) ⟨633422, by rfl⟩ : syracuseStep 3378253 = 1266845) (by norm_num)
theorem B4504337 : Blo 2001435 4504337 := bstep (se 2 (by rfl) ⟨1689126, by rfl⟩ : syracuseStep 4504337 = 3378253) B3378253
theorem B3002891 : Blo 2001435 3002891 := bstep (se 1 (by rfl) ⟨2252168, by rfl⟩ : syracuseStep 3002891 = 4504337) B4504337
theorem B2001927 : Blo 2001435 2001927 := bstep (se 1 (by rfl) ⟨1501445, by rfl⟩ : syracuseStep 2001927 = 3002891) B3002891
theorem B2252173 : Blo 2001435 2252173 := bbase (se 3 (by rfl) ⟨422282, by rfl⟩ : syracuseStep 2252173 = 844565) (by norm_num)
theorem B3002897 : Blo 2001435 3002897 := bstep (se 2 (by rfl) ⟨1126086, by rfl⟩ : syracuseStep 3002897 = 2252173) B2252173
theorem B2001931 : Blo 2001435 2001931 := bstep (se 1 (by rfl) ⟨1501448, by rfl⟩ : syracuseStep 2001931 = 3002897) B3002897
theorem B6756533 : Blo 2001435 6756533 := bbase (se 5 (by rfl) ⟨316712, by rfl⟩ : syracuseStep 6756533 = 633425) (by norm_num)
theorem B4504355 : Blo 2001435 4504355 := bstep (se 1 (by rfl) ⟨3378266, by rfl⟩ : syracuseStep 4504355 = 6756533) B6756533
theorem B3002903 : Blo 2001435 3002903 := bstep (se 1 (by rfl) ⟨2252177, by rfl⟩ : syracuseStep 3002903 = 4504355) B4504355
theorem B2001935 : Blo 2001435 2001935 := bstep (se 1 (by rfl) ⟨1501451, by rfl⟩ : syracuseStep 2001935 = 3002903) B3002903
theorem B3002909 : Blo 2001435 3002909 := bbase (se 3 (by rfl) ⟨563045, by rfl⟩ : syracuseStep 3002909 = 1126091) (by norm_num)
theorem B2001939 : Blo 2001435 2001939 := bstep (se 1 (by rfl) ⟨1501454, by rfl⟩ : syracuseStep 2001939 = 3002909) B3002909
theorem B4504373 : Blo 2001435 4504373 := bbase (se 5 (by rfl) ⟨211142, by rfl⟩ : syracuseStep 4504373 = 422285) (by norm_num)
theorem B3002915 : Blo 2001435 3002915 := bstep (se 1 (by rfl) ⟨2252186, by rfl⟩ : syracuseStep 3002915 = 4504373) B4504373
theorem B2001943 : Blo 2001435 2001943 := bstep (se 1 (by rfl) ⟨1501457, by rfl⟩ : syracuseStep 2001943 = 3002915) B3002915
theorem B4333981 : Blo 2001435 4333981 := bbase (se 3 (by rfl) ⟨812621, by rfl⟩ : syracuseStep 4333981 = 1625243) (by norm_num)
theorem B5778641 : Blo 2001435 5778641 := bstep (se 2 (by rfl) ⟨2166990, by rfl⟩ : syracuseStep 5778641 = 4333981) B4333981
theorem B15409709 : Blo 2001435 15409709 := bstep (se 3 (by rfl) ⟨2889320, by rfl⟩ : syracuseStep 15409709 = 5778641) B5778641
theorem B10273139 : Blo 2001435 10273139 := bstep (se 1 (by rfl) ⟨7704854, by rfl⟩ : syracuseStep 10273139 = 15409709) B15409709
theorem B6848759 : Blo 2001435 6848759 := bstep (se 1 (by rfl) ⟨5136569, by rfl⟩ : syracuseStep 6848759 = 10273139) B10273139
theorem B18263357 : Blo 2001435 18263357 := bstep (se 3 (by rfl) ⟨3424379, by rfl⟩ : syracuseStep 18263357 = 6848759) B6848759
theorem B12175571 : Blo 2001435 12175571 := bstep (se 1 (by rfl) ⟨9131678, by rfl⟩ : syracuseStep 12175571 = 18263357) B18263357
theorem B8117047 : Blo 2001435 8117047 := bstep (se 1 (by rfl) ⟨6087785, by rfl⟩ : syracuseStep 8117047 = 12175571) B12175571
theorem B10822729 : Blo 2001435 10822729 := bstep (se 2 (by rfl) ⟨4058523, by rfl⟩ : syracuseStep 10822729 = 8117047) B8117047
theorem B14430305 : Blo 2001435 14430305 := bstep (se 2 (by rfl) ⟨5411364, by rfl⟩ : syracuseStep 14430305 = 10822729) B10822729
theorem B9620203 : Blo 2001435 9620203 := bstep (se 1 (by rfl) ⟨7215152, by rfl⟩ : syracuseStep 9620203 = 14430305) B14430305
theorem B12826937 : Blo 2001435 12826937 := bstep (se 2 (by rfl) ⟨4810101, by rfl⟩ : syracuseStep 12826937 = 9620203) B9620203
theorem B8551291 : Blo 2001435 8551291 := bstep (se 1 (by rfl) ⟨6413468, by rfl⟩ : syracuseStep 8551291 = 12826937) B12826937
theorem B11401721 : Blo 2001435 11401721 := bstep (se 2 (by rfl) ⟨4275645, by rfl⟩ : syracuseStep 11401721 = 8551291) B8551291
theorem B7601147 : Blo 2001435 7601147 := bstep (se 1 (by rfl) ⟨5700860, by rfl⟩ : syracuseStep 7601147 = 11401721) B11401721
theorem B5067431 : Blo 2001435 5067431 := bstep (se 1 (by rfl) ⟨3800573, by rfl⟩ : syracuseStep 5067431 = 7601147) B7601147
theorem B3378287 : Blo 2001435 3378287 := bstep (se 1 (by rfl) ⟨2533715, by rfl⟩ : syracuseStep 3378287 = 5067431) B5067431
theorem B2252191 : Blo 2001435 2252191 := bstep (se 1 (by rfl) ⟨1689143, by rfl⟩ : syracuseStep 2252191 = 3378287) B3378287
theorem B3002921 : Blo 2001435 3002921 := bstep (se 2 (by rfl) ⟨1126095, by rfl⟩ : syracuseStep 3002921 = 2252191) B2252191
theorem B2001947 : Blo 2001435 2001947 := bstep (se 1 (by rfl) ⟨1501460, by rfl⟩ : syracuseStep 2001947 = 3002921) B3002921
theorem B17335957 : Blo 2001435 17335957 := bbase (se 6 (by rfl) ⟨406311, by rfl⟩ : syracuseStep 17335957 = 812623) (by norm_num)
theorem B23114609 : Blo 2001435 23114609 := bstep (se 2 (by rfl) ⟨8667978, by rfl⟩ : syracuseStep 23114609 = 17335957) B17335957
theorem B15409739 : Blo 2001435 15409739 := bstep (se 1 (by rfl) ⟨11557304, by rfl⟩ : syracuseStep 15409739 = 23114609) B23114609
theorem B10273159 : Blo 2001435 10273159 := bstep (se 1 (by rfl) ⟨7704869, by rfl⟩ : syracuseStep 10273159 = 15409739) B15409739
theorem B13697545 : Blo 2001435 13697545 := bstep (se 2 (by rfl) ⟨5136579, by rfl⟩ : syracuseStep 13697545 = 10273159) B10273159
theorem B18263393 : Blo 2001435 18263393 := bstep (se 2 (by rfl) ⟨6848772, by rfl⟩ : syracuseStep 18263393 = 13697545) B13697545
theorem B12175595 : Blo 2001435 12175595 := bstep (se 1 (by rfl) ⟨9131696, by rfl⟩ : syracuseStep 12175595 = 18263393) B18263393
theorem B8117063 : Blo 2001435 8117063 := bstep (se 1 (by rfl) ⟨6087797, by rfl⟩ : syracuseStep 8117063 = 12175595) B12175595
theorem B5411375 : Blo 2001435 5411375 := bstep (se 1 (by rfl) ⟨4058531, by rfl⟩ : syracuseStep 5411375 = 8117063) B8117063
theorem B3607583 : Blo 2001435 3607583 := bstep (se 1 (by rfl) ⟨2705687, by rfl⟩ : syracuseStep 3607583 = 5411375) B5411375
theorem B9620221 : Blo 2001435 9620221 := bstep (se 3 (by rfl) ⟨1803791, by rfl⟩ : syracuseStep 9620221 = 3607583) B3607583
theorem B12826961 : Blo 2001435 12826961 := bstep (se 2 (by rfl) ⟨4810110, by rfl⟩ : syracuseStep 12826961 = 9620221) B9620221
theorem B8551307 : Blo 2001435 8551307 := bstep (se 1 (by rfl) ⟨6413480, by rfl⟩ : syracuseStep 8551307 = 12826961) B12826961
theorem B5700871 : Blo 2001435 5700871 := bstep (se 1 (by rfl) ⟨4275653, by rfl⟩ : syracuseStep 5700871 = 8551307) B8551307
theorem B7601161 : Blo 2001435 7601161 := bstep (se 2 (by rfl) ⟨2850435, by rfl⟩ : syracuseStep 7601161 = 5700871) B5700871
theorem B10134881 : Blo 2001435 10134881 := bstep (se 2 (by rfl) ⟨3800580, by rfl⟩ : syracuseStep 10134881 = 7601161) B7601161
theorem B6756587 : Blo 2001435 6756587 := bstep (se 1 (by rfl) ⟨5067440, by rfl⟩ : syracuseStep 6756587 = 10134881) B10134881
theorem B4504391 : Blo 2001435 4504391 := bstep (se 1 (by rfl) ⟨3378293, by rfl⟩ : syracuseStep 4504391 = 6756587) B6756587
theorem B3002927 : Blo 2001435 3002927 := bstep (se 1 (by rfl) ⟨2252195, by rfl⟩ : syracuseStep 3002927 = 4504391) B4504391
theorem B2001951 : Blo 2001435 2001951 := bstep (se 1 (by rfl) ⟨1501463, by rfl⟩ : syracuseStep 2001951 = 3002927) B3002927
theorem B3002933 : Blo 2001435 3002933 := bbase (se 5 (by rfl) ⟨140762, by rfl⟩ : syracuseStep 3002933 = 281525) (by norm_num)
theorem B2001955 : Blo 2001435 2001955 := bstep (se 1 (by rfl) ⟨1501466, by rfl⟩ : syracuseStep 2001955 = 3002933) B3002933
theorem B5067461 : Blo 2001435 5067461 := bbase (se 4 (by rfl) ⟨475074, by rfl⟩ : syracuseStep 5067461 = 950149) (by norm_num)
theorem B3378307 : Blo 2001435 3378307 := bstep (se 1 (by rfl) ⟨2533730, by rfl⟩ : syracuseStep 3378307 = 5067461) B5067461
theorem B4504409 : Blo 2001435 4504409 := bstep (se 2 (by rfl) ⟨1689153, by rfl⟩ : syracuseStep 4504409 = 3378307) B3378307
theorem B3002939 : Blo 2001435 3002939 := bstep (se 1 (by rfl) ⟨2252204, by rfl⟩ : syracuseStep 3002939 = 4504409) B4504409
theorem B2001959 : Blo 2001435 2001959 := bstep (se 1 (by rfl) ⟨1501469, by rfl⟩ : syracuseStep 2001959 = 3002939) B3002939
theorem B2252209 : Blo 2001435 2252209 := bbase (se 2 (by rfl) ⟨844578, by rfl⟩ : syracuseStep 2252209 = 1689157) (by norm_num)
theorem B3002945 : Blo 2001435 3002945 := bstep (se 2 (by rfl) ⟨1126104, by rfl⟩ : syracuseStep 3002945 = 2252209) B2252209
theorem B2001963 : Blo 2001435 2001963 := bstep (se 1 (by rfl) ⟨1501472, by rfl⟩ : syracuseStep 2001963 = 3002945) B3002945
theorem B5700917 : Blo 2001435 5700917 := bbase (se 5 (by rfl) ⟨267230, by rfl⟩ : syracuseStep 5700917 = 534461) (by norm_num)
theorem B3800611 : Blo 2001435 3800611 := bstep (se 1 (by rfl) ⟨2850458, by rfl⟩ : syracuseStep 3800611 = 5700917) B5700917
theorem B5067481 : Blo 2001435 5067481 := bstep (se 2 (by rfl) ⟨1900305, by rfl⟩ : syracuseStep 5067481 = 3800611) B3800611
theorem B6756641 : Blo 2001435 6756641 := bstep (se 2 (by rfl) ⟨2533740, by rfl⟩ : syracuseStep 6756641 = 5067481) B5067481
theorem B4504427 : Blo 2001435 4504427 := bstep (se 1 (by rfl) ⟨3378320, by rfl⟩ : syracuseStep 4504427 = 6756641) B6756641
theorem B3002951 : Blo 2001435 3002951 := bstep (se 1 (by rfl) ⟨2252213, by rfl⟩ : syracuseStep 3002951 = 4504427) B4504427
theorem B2001967 : Blo 2001435 2001967 := bstep (se 1 (by rfl) ⟨1501475, by rfl⟩ : syracuseStep 2001967 = 3002951) B3002951
theorem B3002957 : Blo 2001435 3002957 := bbase (se 3 (by rfl) ⟨563054, by rfl⟩ : syracuseStep 3002957 = 1126109) (by norm_num)
theorem B2001971 : Blo 2001435 2001971 := bstep (se 1 (by rfl) ⟨1501478, by rfl⟩ : syracuseStep 2001971 = 3002957) B3002957
theorem B4504445 : Blo 2001435 4504445 := bbase (se 3 (by rfl) ⟨844583, by rfl⟩ : syracuseStep 4504445 = 1689167) (by norm_num)
theorem B3002963 : Blo 2001435 3002963 := bstep (se 1 (by rfl) ⟨2252222, by rfl⟩ : syracuseStep 3002963 = 4504445) B4504445
theorem B2001975 : Blo 2001435 2001975 := bstep (se 1 (by rfl) ⟨1501481, by rfl⟩ : syracuseStep 2001975 = 3002963) B3002963
theorem B3378341 : Blo 2001435 3378341 := bbase (se 4 (by rfl) ⟨316719, by rfl⟩ : syracuseStep 3378341 = 633439) (by norm_num)
theorem B2252227 : Blo 2001435 2252227 := bstep (se 1 (by rfl) ⟨1689170, by rfl⟩ : syracuseStep 2252227 = 3378341) B3378341
theorem B3002969 : Blo 2001435 3002969 := bstep (se 2 (by rfl) ⟨1126113, by rfl⟩ : syracuseStep 3002969 = 2252227) B2252227
theorem B2001979 : Blo 2001435 2001979 := bstep (se 1 (by rfl) ⟨1501484, by rfl⟩ : syracuseStep 2001979 = 3002969) B3002969
theorem B2137861 : Blo 2001435 2137861 := bbase (se 4 (by rfl) ⟨200424, by rfl⟩ : syracuseStep 2137861 = 400849) (by norm_num)
theorem B2850481 : Blo 2001435 2850481 := bstep (se 2 (by rfl) ⟨1068930, by rfl⟩ : syracuseStep 2850481 = 2137861) B2137861
theorem B15202565 : Blo 2001435 15202565 := bstep (se 4 (by rfl) ⟨1425240, by rfl⟩ : syracuseStep 15202565 = 2850481) B2850481
theorem B10135043 : Blo 2001435 10135043 := bstep (se 1 (by rfl) ⟨7601282, by rfl⟩ : syracuseStep 10135043 = 15202565) B15202565
theorem B6756695 : Blo 2001435 6756695 := bstep (se 1 (by rfl) ⟨5067521, by rfl⟩ : syracuseStep 6756695 = 10135043) B10135043
theorem B4504463 : Blo 2001435 4504463 := bstep (se 1 (by rfl) ⟨3378347, by rfl⟩ : syracuseStep 4504463 = 6756695) B6756695
theorem B3002975 : Blo 2001435 3002975 := bstep (se 1 (by rfl) ⟨2252231, by rfl⟩ : syracuseStep 3002975 = 4504463) B4504463
theorem B2001983 : Blo 2001435 2001983 := bstep (se 1 (by rfl) ⟨1501487, by rfl⟩ : syracuseStep 2001983 = 3002975) B3002975
theorem B3002981 : Blo 2001435 3002981 := bbase (se 4 (by rfl) ⟨281529, by rfl⟩ : syracuseStep 3002981 = 563059) (by norm_num)
theorem B2001987 : Blo 2001435 2001987 := bstep (se 1 (by rfl) ⟨1501490, by rfl⟩ : syracuseStep 2001987 = 3002981) B3002981
theorem B2850493 : Blo 2001435 2850493 := bbase (se 3 (by rfl) ⟨534467, by rfl⟩ : syracuseStep 2850493 = 1068935) (by norm_num)
theorem B3800657 : Blo 2001435 3800657 := bstep (se 2 (by rfl) ⟨1425246, by rfl⟩ : syracuseStep 3800657 = 2850493) B2850493
theorem B2533771 : Blo 2001435 2533771 := bstep (se 1 (by rfl) ⟨1900328, by rfl⟩ : syracuseStep 2533771 = 3800657) B3800657
theorem B3378361 : Blo 2001435 3378361 := bstep (se 2 (by rfl) ⟨1266885, by rfl⟩ : syracuseStep 3378361 = 2533771) B2533771
theorem B4504481 : Blo 2001435 4504481 := bstep (se 2 (by rfl) ⟨1689180, by rfl⟩ : syracuseStep 4504481 = 3378361) B3378361
theorem B3002987 : Blo 2001435 3002987 := bstep (se 1 (by rfl) ⟨2252240, by rfl⟩ : syracuseStep 3002987 = 4504481) B4504481
theorem B2001991 : Blo 2001435 2001991 := bstep (se 1 (by rfl) ⟨1501493, by rfl⟩ : syracuseStep 2001991 = 3002987) B3002987
theorem B2252245 : Blo 2001435 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B3002993 : Blo 2001435 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B2001995 : Blo 2001435 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B2533781 : Blo 2001435 2533781 := bbase (se 6 (by rfl) ⟨59385, by rfl⟩ : syracuseStep 2533781 = 118771) (by norm_num)
theorem B6756749 : Blo 2001435 6756749 := bstep (se 3 (by rfl) ⟨1266890, by rfl⟩ : syracuseStep 6756749 = 2533781) B2533781
theorem B4504499 : Blo 2001435 4504499 := bstep (se 1 (by rfl) ⟨3378374, by rfl⟩ : syracuseStep 4504499 = 6756749) B6756749
theorem B3002999 : Blo 2001435 3002999 := bstep (se 1 (by rfl) ⟨2252249, by rfl⟩ : syracuseStep 3002999 = 4504499) B4504499
theorem B2001999 : Blo 2001435 2001999 := bstep (se 1 (by rfl) ⟨1501499, by rfl⟩ : syracuseStep 2001999 = 3002999) B3002999
theorem B3003005 : Blo 2001435 3003005 := bbase (se 3 (by rfl) ⟨563063, by rfl⟩ : syracuseStep 3003005 = 1126127) (by norm_num)
theorem B2002003 : Blo 2001435 2002003 := bstep (se 1 (by rfl) ⟨1501502, by rfl⟩ : syracuseStep 2002003 = 3003005) B3003005
theorem B4504517 : Blo 2001435 4504517 := bbase (se 4 (by rfl) ⟨422298, by rfl⟩ : syracuseStep 4504517 = 844597) (by norm_num)
theorem B3003011 : Blo 2001435 3003011 := bstep (se 1 (by rfl) ⟨2252258, by rfl⟩ : syracuseStep 3003011 = 4504517) B4504517
theorem B2002007 : Blo 2001435 2002007 := bstep (se 1 (by rfl) ⟨1501505, by rfl⟩ : syracuseStep 2002007 = 3003011) B3003011
theorem B3206837 : Blo 2001435 3206837 := bbase (se 5 (by rfl) ⟨150320, by rfl⟩ : syracuseStep 3206837 = 300641) (by norm_num)
theorem B8551565 : Blo 2001435 8551565 := bstep (se 3 (by rfl) ⟨1603418, by rfl⟩ : syracuseStep 8551565 = 3206837) B3206837
theorem B5701043 : Blo 2001435 5701043 := bstep (se 1 (by rfl) ⟨4275782, by rfl⟩ : syracuseStep 5701043 = 8551565) B8551565
theorem B3800695 : Blo 2001435 3800695 := bstep (se 1 (by rfl) ⟨2850521, by rfl⟩ : syracuseStep 3800695 = 5701043) B5701043
theorem B5067593 : Blo 2001435 5067593 := bstep (se 2 (by rfl) ⟨1900347, by rfl⟩ : syracuseStep 5067593 = 3800695) B3800695
theorem B3378395 : Blo 2001435 3378395 := bstep (se 1 (by rfl) ⟨2533796, by rfl⟩ : syracuseStep 3378395 = 5067593) B5067593
theorem B2252263 : Blo 2001435 2252263 := bstep (se 1 (by rfl) ⟨1689197, by rfl⟩ : syracuseStep 2252263 = 3378395) B3378395
theorem B3003017 : Blo 2001435 3003017 := bstep (se 2 (by rfl) ⟨1126131, by rfl⟩ : syracuseStep 3003017 = 2252263) B2252263
theorem B2002011 : Blo 2001435 2002011 := bstep (se 1 (by rfl) ⟨1501508, by rfl⟩ : syracuseStep 2002011 = 3003017) B3003017
theorem B10135205 : Blo 2001435 10135205 := bbase (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) (by norm_num)
theorem B6756803 : Blo 2001435 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B4504535 : Blo 2001435 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B3003023 : Blo 2001435 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B2002015 : Blo 2001435 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B3003029 : Blo 2001435 3003029 := bbase (se 6 (by rfl) ⟨70383, by rfl⟩ : syracuseStep 3003029 = 140767) (by norm_num)
theorem B2002019 : Blo 2001435 2002019 := bstep (se 1 (by rfl) ⟨1501514, by rfl⟩ : syracuseStep 2002019 = 3003029) B3003029
theorem B6171077 : Blo 2001435 6171077 := bbase (se 4 (by rfl) ⟨578538, by rfl⟩ : syracuseStep 6171077 = 1157077) (by norm_num)
theorem B16456205 : Blo 2001435 16456205 := bstep (se 3 (by rfl) ⟨3085538, by rfl⟩ : syracuseStep 16456205 = 6171077) B6171077
theorem B10970803 : Blo 2001435 10970803 := bstep (se 1 (by rfl) ⟨8228102, by rfl⟩ : syracuseStep 10970803 = 16456205) B16456205
theorem B14627737 : Blo 2001435 14627737 := bstep (se 2 (by rfl) ⟨5485401, by rfl⟩ : syracuseStep 14627737 = 10970803) B10970803
theorem B19503649 : Blo 2001435 19503649 := bstep (se 2 (by rfl) ⟨7313868, by rfl⟩ : syracuseStep 19503649 = 14627737) B14627737
theorem B104019461 : Blo 2001435 104019461 := bstep (se 4 (by rfl) ⟨9751824, by rfl⟩ : syracuseStep 104019461 = 19503649) B19503649
theorem B69346307 : Blo 2001435 69346307 := bstep (se 1 (by rfl) ⟨52009730, by rfl⟩ : syracuseStep 69346307 = 104019461) B104019461
theorem B46230871 : Blo 2001435 46230871 := bstep (se 1 (by rfl) ⟨34673153, by rfl⟩ : syracuseStep 46230871 = 69346307) B69346307
theorem B61641161 : Blo 2001435 61641161 := bstep (se 2 (by rfl) ⟨23115435, by rfl⟩ : syracuseStep 61641161 = 46230871) B46230871
theorem B41094107 : Blo 2001435 41094107 := bstep (se 1 (by rfl) ⟨30820580, by rfl⟩ : syracuseStep 41094107 = 61641161) B61641161
theorem B27396071 : Blo 2001435 27396071 := bstep (se 1 (by rfl) ⟨20547053, by rfl⟩ : syracuseStep 27396071 = 41094107) B41094107
theorem B18264047 : Blo 2001435 18264047 := bstep (se 1 (by rfl) ⟨13698035, by rfl⟩ : syracuseStep 18264047 = 27396071) B27396071
theorem B48704125 : Blo 2001435 48704125 := bstep (se 3 (by rfl) ⟨9132023, by rfl⟩ : syracuseStep 48704125 = 18264047) B18264047
theorem B64938833 : Blo 2001435 64938833 := bstep (se 2 (by rfl) ⟨24352062, by rfl⟩ : syracuseStep 64938833 = 48704125) B48704125
theorem B43292555 : Blo 2001435 43292555 := bstep (se 1 (by rfl) ⟨32469416, by rfl⟩ : syracuseStep 43292555 = 64938833) B64938833
theorem B28861703 : Blo 2001435 28861703 := bstep (se 1 (by rfl) ⟨21646277, by rfl⟩ : syracuseStep 28861703 = 43292555) B43292555
theorem B19241135 : Blo 2001435 19241135 := bstep (se 1 (by rfl) ⟨14430851, by rfl⟩ : syracuseStep 19241135 = 28861703) B28861703
theorem B12827423 : Blo 2001435 12827423 := bstep (se 1 (by rfl) ⟨9620567, by rfl⟩ : syracuseStep 12827423 = 19241135) B19241135
theorem B8551615 : Blo 2001435 8551615 := bstep (se 1 (by rfl) ⟨6413711, by rfl⟩ : syracuseStep 8551615 = 12827423) B12827423
theorem B11402153 : Blo 2001435 11402153 := bstep (se 2 (by rfl) ⟨4275807, by rfl⟩ : syracuseStep 11402153 = 8551615) B8551615
theorem B7601435 : Blo 2001435 7601435 := bstep (se 1 (by rfl) ⟨5701076, by rfl⟩ : syracuseStep 7601435 = 11402153) B11402153
theorem B5067623 : Blo 2001435 5067623 := bstep (se 1 (by rfl) ⟨3800717, by rfl⟩ : syracuseStep 5067623 = 7601435) B7601435
theorem B3378415 : Blo 2001435 3378415 := bstep (se 1 (by rfl) ⟨2533811, by rfl⟩ : syracuseStep 3378415 = 5067623) B5067623
theorem B4504553 : Blo 2001435 4504553 := bstep (se 2 (by rfl) ⟨1689207, by rfl⟩ : syracuseStep 4504553 = 3378415) B3378415
theorem B3003035 : Blo 2001435 3003035 := bstep (se 1 (by rfl) ⟨2252276, by rfl⟩ : syracuseStep 3003035 = 4504553) B4504553
theorem B2002023 : Blo 2001435 2002023 := bstep (se 1 (by rfl) ⟨1501517, by rfl⟩ : syracuseStep 2002023 = 3003035) B3003035
theorem B2252281 : Blo 2001435 2252281 := bbase (se 2 (by rfl) ⟨844605, by rfl⟩ : syracuseStep 2252281 = 1689211) (by norm_num)
theorem B3003041 : Blo 2001435 3003041 := bstep (se 2 (by rfl) ⟨1126140, by rfl⟩ : syracuseStep 3003041 = 2252281) B2252281
theorem B2002027 : Blo 2001435 2002027 := bstep (se 1 (by rfl) ⟨1501520, by rfl⟩ : syracuseStep 2002027 = 3003041) B3003041
theorem B3852589 : Blo 2001435 3852589 := bbase (se 3 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 3852589 = 1444721) (by norm_num)
theorem B5136785 : Blo 2001435 5136785 := bstep (se 2 (by rfl) ⟨1926294, by rfl⟩ : syracuseStep 5136785 = 3852589) B3852589
theorem B3424523 : Blo 2001435 3424523 := bstep (se 1 (by rfl) ⟨2568392, by rfl⟩ : syracuseStep 3424523 = 5136785) B5136785
theorem B36528245 : Blo 2001435 36528245 := bstep (se 5 (by rfl) ⟨1712261, by rfl⟩ : syracuseStep 36528245 = 3424523) B3424523
theorem B24352163 : Blo 2001435 24352163 := bstep (se 1 (by rfl) ⟨18264122, by rfl⟩ : syracuseStep 24352163 = 36528245) B36528245
theorem B16234775 : Blo 2001435 16234775 := bstep (se 1 (by rfl) ⟨12176081, by rfl⟩ : syracuseStep 16234775 = 24352163) B24352163
theorem B10823183 : Blo 2001435 10823183 := bstep (se 1 (by rfl) ⟨8117387, by rfl⟩ : syracuseStep 10823183 = 16234775) B16234775
theorem B7215455 : Blo 2001435 7215455 := bstep (se 1 (by rfl) ⟨5411591, by rfl⟩ : syracuseStep 7215455 = 10823183) B10823183
theorem B4810303 : Blo 2001435 4810303 := bstep (se 1 (by rfl) ⟨3607727, by rfl⟩ : syracuseStep 4810303 = 7215455) B7215455
theorem B6413737 : Blo 2001435 6413737 := bstep (se 2 (by rfl) ⟨2405151, by rfl⟩ : syracuseStep 6413737 = 4810303) B4810303
theorem B8551649 : Blo 2001435 8551649 := bstep (se 2 (by rfl) ⟨3206868, by rfl⟩ : syracuseStep 8551649 = 6413737) B6413737
theorem B5701099 : Blo 2001435 5701099 := bstep (se 1 (by rfl) ⟨4275824, by rfl⟩ : syracuseStep 5701099 = 8551649) B8551649
theorem B7601465 : Blo 2001435 7601465 := bstep (se 2 (by rfl) ⟨2850549, by rfl⟩ : syracuseStep 7601465 = 5701099) B5701099
theorem B5067643 : Blo 2001435 5067643 := bstep (se 1 (by rfl) ⟨3800732, by rfl⟩ : syracuseStep 5067643 = 7601465) B7601465
theorem B6756857 : Blo 2001435 6756857 := bstep (se 2 (by rfl) ⟨2533821, by rfl⟩ : syracuseStep 6756857 = 5067643) B5067643
theorem B4504571 : Blo 2001435 4504571 := bstep (se 1 (by rfl) ⟨3378428, by rfl⟩ : syracuseStep 4504571 = 6756857) B6756857
theorem B3003047 : Blo 2001435 3003047 := bstep (se 1 (by rfl) ⟨2252285, by rfl⟩ : syracuseStep 3003047 = 4504571) B4504571
theorem B2002031 : Blo 2001435 2002031 := bstep (se 1 (by rfl) ⟨1501523, by rfl⟩ : syracuseStep 2002031 = 3003047) B3003047
theorem B3003053 : Blo 2001435 3003053 := bbase (se 3 (by rfl) ⟨563072, by rfl⟩ : syracuseStep 3003053 = 1126145) (by norm_num)
theorem B2002035 : Blo 2001435 2002035 := bstep (se 1 (by rfl) ⟨1501526, by rfl⟩ : syracuseStep 2002035 = 3003053) B3003053
theorem B4504589 : Blo 2001435 4504589 := bbase (se 3 (by rfl) ⟨844610, by rfl⟩ : syracuseStep 4504589 = 1689221) (by norm_num)
theorem B3003059 : Blo 2001435 3003059 := bstep (se 1 (by rfl) ⟨2252294, by rfl⟩ : syracuseStep 3003059 = 4504589) B4504589
theorem B2002039 : Blo 2001435 2002039 := bstep (se 1 (by rfl) ⟨1501529, by rfl⟩ : syracuseStep 2002039 = 3003059) B3003059
theorem B2533837 : Blo 2001435 2533837 := bbase (se 3 (by rfl) ⟨475094, by rfl⟩ : syracuseStep 2533837 = 950189) (by norm_num)
theorem B3378449 : Blo 2001435 3378449 := bstep (se 2 (by rfl) ⟨1266918, by rfl⟩ : syracuseStep 3378449 = 2533837) B2533837
theorem B2252299 : Blo 2001435 2252299 := bstep (se 1 (by rfl) ⟨1689224, by rfl⟩ : syracuseStep 2252299 = 3378449) B3378449
theorem B3003065 : Blo 2001435 3003065 := bstep (se 2 (by rfl) ⟨1126149, by rfl⟩ : syracuseStep 3003065 = 2252299) B2252299
theorem B2002043 : Blo 2001435 2002043 := bstep (se 1 (by rfl) ⟨1501532, by rfl⟩ : syracuseStep 2002043 = 3003065) B3003065
theorem B16234901 : Blo 2001435 16234901 := bbase (se 6 (by rfl) ⟨380505, by rfl⟩ : syracuseStep 16234901 = 761011) (by norm_num)
theorem B10823267 : Blo 2001435 10823267 := bstep (se 1 (by rfl) ⟨8117450, by rfl⟩ : syracuseStep 10823267 = 16234901) B16234901
theorem B28862045 : Blo 2001435 28862045 := bstep (se 3 (by rfl) ⟨5411633, by rfl⟩ : syracuseStep 28862045 = 10823267) B10823267
theorem B19241363 : Blo 2001435 19241363 := bstep (se 1 (by rfl) ⟨14431022, by rfl⟩ : syracuseStep 19241363 = 28862045) B28862045
theorem B12827575 : Blo 2001435 12827575 := bstep (se 1 (by rfl) ⟨9620681, by rfl⟩ : syracuseStep 12827575 = 19241363) B19241363
theorem B17103433 : Blo 2001435 17103433 := bstep (se 2 (by rfl) ⟨6413787, by rfl⟩ : syracuseStep 17103433 = 12827575) B12827575
theorem B22804577 : Blo 2001435 22804577 := bstep (se 2 (by rfl) ⟨8551716, by rfl⟩ : syracuseStep 22804577 = 17103433) B17103433
theorem B15203051 : Blo 2001435 15203051 := bstep (se 1 (by rfl) ⟨11402288, by rfl⟩ : syracuseStep 15203051 = 22804577) B22804577
theorem B10135367 : Blo 2001435 10135367 := bstep (se 1 (by rfl) ⟨7601525, by rfl⟩ : syracuseStep 10135367 = 15203051) B15203051
theorem B6756911 : Blo 2001435 6756911 := bstep (se 1 (by rfl) ⟨5067683, by rfl⟩ : syracuseStep 6756911 = 10135367) B10135367
theorem B4504607 : Blo 2001435 4504607 := bstep (se 1 (by rfl) ⟨3378455, by rfl⟩ : syracuseStep 4504607 = 6756911) B6756911
theorem B3003071 : Blo 2001435 3003071 := bstep (se 1 (by rfl) ⟨2252303, by rfl⟩ : syracuseStep 3003071 = 4504607) B4504607
theorem B2002047 : Blo 2001435 2002047 := bstep (se 1 (by rfl) ⟨1501535, by rfl⟩ : syracuseStep 2002047 = 3003071) B3003071
theorem B3003077 : Blo 2001435 3003077 := bbase (se 4 (by rfl) ⟨281538, by rfl⟩ : syracuseStep 3003077 = 563077) (by norm_num)
theorem B2002051 : Blo 2001435 2002051 := bstep (se 1 (by rfl) ⟨1501538, by rfl⟩ : syracuseStep 2002051 = 3003077) B3003077
theorem B3378469 : Blo 2001435 3378469 := bbase (se 4 (by rfl) ⟨316731, by rfl⟩ : syracuseStep 3378469 = 633463) (by norm_num)
theorem B4504625 : Blo 2001435 4504625 := bstep (se 2 (by rfl) ⟨1689234, by rfl⟩ : syracuseStep 4504625 = 3378469) B3378469
theorem B3003083 : Blo 2001435 3003083 := bstep (se 1 (by rfl) ⟨2252312, by rfl⟩ : syracuseStep 3003083 = 4504625) B4504625
theorem B2002055 : Blo 2001435 2002055 := bstep (se 1 (by rfl) ⟨1501541, by rfl⟩ : syracuseStep 2002055 = 3003083) B3003083
theorem B2252317 : Blo 2001435 2252317 := bbase (se 3 (by rfl) ⟨422309, by rfl⟩ : syracuseStep 2252317 = 844619) (by norm_num)
theorem B3003089 : Blo 2001435 3003089 := bstep (se 2 (by rfl) ⟨1126158, by rfl⟩ : syracuseStep 3003089 = 2252317) B2252317
theorem B2002059 : Blo 2001435 2002059 := bstep (se 1 (by rfl) ⟨1501544, by rfl⟩ : syracuseStep 2002059 = 3003089) B3003089
theorem B6756965 : Blo 2001435 6756965 := bbase (se 4 (by rfl) ⟨633465, by rfl⟩ : syracuseStep 6756965 = 1266931) (by norm_num)
theorem B4504643 : Blo 2001435 4504643 := bstep (se 1 (by rfl) ⟨3378482, by rfl⟩ : syracuseStep 4504643 = 6756965) B6756965
theorem B3003095 : Blo 2001435 3003095 := bstep (se 1 (by rfl) ⟨2252321, by rfl⟩ : syracuseStep 3003095 = 4504643) B4504643
theorem B2002063 : Blo 2001435 2002063 := bstep (se 1 (by rfl) ⟨1501547, by rfl⟩ : syracuseStep 2002063 = 3003095) B3003095
theorem B3003101 : Blo 2001435 3003101 := bbase (se 3 (by rfl) ⟨563081, by rfl⟩ : syracuseStep 3003101 = 1126163) (by norm_num)
theorem B2002067 : Blo 2001435 2002067 := bstep (se 1 (by rfl) ⟨1501550, by rfl⟩ : syracuseStep 2002067 = 3003101) B3003101
theorem B4504661 : Blo 2001435 4504661 := bbase (se 8 (by rfl) ⟨26394, by rfl⟩ : syracuseStep 4504661 = 52789) (by norm_num)
theorem B3003107 : Blo 2001435 3003107 := bstep (se 1 (by rfl) ⟨2252330, by rfl⟩ : syracuseStep 3003107 = 4504661) B4504661
theorem B2002071 : Blo 2001435 2002071 := bstep (se 1 (by rfl) ⟨1501553, by rfl⟩ : syracuseStep 2002071 = 3003107) B3003107
theorem B2742773 : Blo 2001435 2742773 := bbase (se 5 (by rfl) ⟨128567, by rfl⟩ : syracuseStep 2742773 = 257135) (by norm_num)
theorem B7314061 : Blo 2001435 7314061 := bstep (se 3 (by rfl) ⟨1371386, by rfl⟩ : syracuseStep 7314061 = 2742773) B2742773
theorem B9752081 : Blo 2001435 9752081 := bstep (se 2 (by rfl) ⟨3657030, by rfl⟩ : syracuseStep 9752081 = 7314061) B7314061
theorem B26005549 : Blo 2001435 26005549 := bstep (se 3 (by rfl) ⟨4876040, by rfl⟩ : syracuseStep 26005549 = 9752081) B9752081
theorem B34674065 : Blo 2001435 34674065 := bstep (se 2 (by rfl) ⟨13002774, by rfl⟩ : syracuseStep 34674065 = 26005549) B26005549
theorem B23116043 : Blo 2001435 23116043 := bstep (se 1 (by rfl) ⟨17337032, by rfl⟩ : syracuseStep 23116043 = 34674065) B34674065
theorem B61642781 : Blo 2001435 61642781 := bstep (se 3 (by rfl) ⟨11558021, by rfl⟩ : syracuseStep 61642781 = 23116043) B23116043
theorem B41095187 : Blo 2001435 41095187 := bstep (se 1 (by rfl) ⟨30821390, by rfl⟩ : syracuseStep 41095187 = 61642781) B61642781
theorem B27396791 : Blo 2001435 27396791 := bstep (se 1 (by rfl) ⟨20547593, by rfl⟩ : syracuseStep 27396791 = 41095187) B41095187
theorem B18264527 : Blo 2001435 18264527 := bstep (se 1 (by rfl) ⟨13698395, by rfl⟩ : syracuseStep 18264527 = 27396791) B27396791
theorem B12176351 : Blo 2001435 12176351 := bstep (se 1 (by rfl) ⟨9132263, by rfl⟩ : syracuseStep 12176351 = 18264527) B18264527
theorem B8117567 : Blo 2001435 8117567 := bstep (se 1 (by rfl) ⟨6088175, by rfl⟩ : syracuseStep 8117567 = 12176351) B12176351
theorem B5411711 : Blo 2001435 5411711 := bstep (se 1 (by rfl) ⟨4058783, by rfl⟩ : syracuseStep 5411711 = 8117567) B8117567
theorem B14431229 : Blo 2001435 14431229 := bstep (se 3 (by rfl) ⟨2705855, by rfl⟩ : syracuseStep 14431229 = 5411711) B5411711
theorem B9620819 : Blo 2001435 9620819 := bstep (se 1 (by rfl) ⟨7215614, by rfl⟩ : syracuseStep 9620819 = 14431229) B14431229
theorem B6413879 : Blo 2001435 6413879 := bstep (se 1 (by rfl) ⟨4810409, by rfl⟩ : syracuseStep 6413879 = 9620819) B9620819
theorem B4275919 : Blo 2001435 4275919 := bstep (se 1 (by rfl) ⟨3206939, by rfl⟩ : syracuseStep 4275919 = 6413879) B6413879
theorem B5701225 : Blo 2001435 5701225 := bstep (se 2 (by rfl) ⟨2137959, by rfl⟩ : syracuseStep 5701225 = 4275919) B4275919
theorem B7601633 : Blo 2001435 7601633 := bstep (se 2 (by rfl) ⟨2850612, by rfl⟩ : syracuseStep 7601633 = 5701225) B5701225
theorem B5067755 : Blo 2001435 5067755 := bstep (se 1 (by rfl) ⟨3800816, by rfl⟩ : syracuseStep 5067755 = 7601633) B7601633
theorem B3378503 : Blo 2001435 3378503 := bstep (se 1 (by rfl) ⟨2533877, by rfl⟩ : syracuseStep 3378503 = 5067755) B5067755
theorem B2252335 : Blo 2001435 2252335 := bstep (se 1 (by rfl) ⟨1689251, by rfl⟩ : syracuseStep 2252335 = 3378503) B3378503
theorem B3003113 : Blo 2001435 3003113 := bstep (se 2 (by rfl) ⟨1126167, by rfl⟩ : syracuseStep 3003113 = 2252335) B2252335
theorem B2002075 : Blo 2001435 2002075 := bstep (se 1 (by rfl) ⟨1501556, by rfl⟩ : syracuseStep 2002075 = 3003113) B3003113
theorem B2167133 : Blo 2001435 2167133 := bbase (se 3 (by rfl) ⟨406337, by rfl⟩ : syracuseStep 2167133 = 812675) (by norm_num)
theorem B5779021 : Blo 2001435 5779021 := bstep (se 3 (by rfl) ⟨1083566, by rfl⟩ : syracuseStep 5779021 = 2167133) B2167133
theorem B7705361 : Blo 2001435 7705361 := bstep (se 2 (by rfl) ⟨2889510, by rfl⟩ : syracuseStep 7705361 = 5779021) B5779021
theorem B5136907 : Blo 2001435 5136907 := bstep (se 1 (by rfl) ⟨3852680, by rfl⟩ : syracuseStep 5136907 = 7705361) B7705361
theorem B6849209 : Blo 2001435 6849209 := bstep (se 2 (by rfl) ⟨2568453, by rfl⟩ : syracuseStep 6849209 = 5136907) B5136907
theorem B4566139 : Blo 2001435 4566139 := bstep (se 1 (by rfl) ⟨3424604, by rfl⟩ : syracuseStep 4566139 = 6849209) B6849209
theorem B24352741 : Blo 2001435 24352741 := bstep (se 4 (by rfl) ⟨2283069, by rfl⟩ : syracuseStep 24352741 = 4566139) B4566139
theorem B32470321 : Blo 2001435 32470321 := bstep (se 2 (by rfl) ⟨12176370, by rfl⟩ : syracuseStep 32470321 = 24352741) B24352741
theorem B43293761 : Blo 2001435 43293761 := bstep (se 2 (by rfl) ⟨16235160, by rfl⟩ : syracuseStep 43293761 = 32470321) B32470321
theorem B28862507 : Blo 2001435 28862507 := bstep (se 1 (by rfl) ⟨21646880, by rfl⟩ : syracuseStep 28862507 = 43293761) B43293761
theorem B19241671 : Blo 2001435 19241671 := bstep (se 1 (by rfl) ⟨14431253, by rfl⟩ : syracuseStep 19241671 = 28862507) B28862507
theorem B25655561 : Blo 2001435 25655561 := bstep (se 2 (by rfl) ⟨9620835, by rfl⟩ : syracuseStep 25655561 = 19241671) B19241671
theorem B17103707 : Blo 2001435 17103707 := bstep (se 1 (by rfl) ⟨12827780, by rfl⟩ : syracuseStep 17103707 = 25655561) B25655561
theorem B11402471 : Blo 2001435 11402471 := bstep (se 1 (by rfl) ⟨8551853, by rfl⟩ : syracuseStep 11402471 = 17103707) B17103707
theorem B7601647 : Blo 2001435 7601647 := bstep (se 1 (by rfl) ⟨5701235, by rfl⟩ : syracuseStep 7601647 = 11402471) B11402471
theorem B10135529 : Blo 2001435 10135529 := bstep (se 2 (by rfl) ⟨3800823, by rfl⟩ : syracuseStep 10135529 = 7601647) B7601647
theorem B6757019 : Blo 2001435 6757019 := bstep (se 1 (by rfl) ⟨5067764, by rfl⟩ : syracuseStep 6757019 = 10135529) B10135529
theorem B4504679 : Blo 2001435 4504679 := bstep (se 1 (by rfl) ⟨3378509, by rfl⟩ : syracuseStep 4504679 = 6757019) B6757019
theorem B3003119 : Blo 2001435 3003119 := bstep (se 1 (by rfl) ⟨2252339, by rfl⟩ : syracuseStep 3003119 = 4504679) B4504679
theorem B2002079 : Blo 2001435 2002079 := bstep (se 1 (by rfl) ⟨1501559, by rfl⟩ : syracuseStep 2002079 = 3003119) B3003119
theorem B3003125 : Blo 2001435 3003125 := bbase (se 5 (by rfl) ⟨140771, by rfl⟩ : syracuseStep 3003125 = 281543) (by norm_num)
theorem B2002083 : Blo 2001435 2002083 := bstep (se 1 (by rfl) ⟨1501562, by rfl⟩ : syracuseStep 2002083 = 3003125) B3003125
theorem B3607829 : Blo 2001435 3607829 := bbase (se 6 (by rfl) ⟨84558, by rfl⟩ : syracuseStep 3607829 = 169117) (by norm_num)
theorem B2405219 : Blo 2001435 2405219 := bstep (se 1 (by rfl) ⟨1803914, by rfl⟩ : syracuseStep 2405219 = 3607829) B3607829
theorem B6413917 : Blo 2001435 6413917 := bstep (se 3 (by rfl) ⟨1202609, by rfl⟩ : syracuseStep 6413917 = 2405219) B2405219
theorem B8551889 : Blo 2001435 8551889 := bstep (se 2 (by rfl) ⟨3206958, by rfl⟩ : syracuseStep 8551889 = 6413917) B6413917
theorem B5701259 : Blo 2001435 5701259 := bstep (se 1 (by rfl) ⟨4275944, by rfl⟩ : syracuseStep 5701259 = 8551889) B8551889
theorem B3800839 : Blo 2001435 3800839 := bstep (se 1 (by rfl) ⟨2850629, by rfl⟩ : syracuseStep 3800839 = 5701259) B5701259
theorem B5067785 : Blo 2001435 5067785 := bstep (se 2 (by rfl) ⟨1900419, by rfl⟩ : syracuseStep 5067785 = 3800839) B3800839
theorem B3378523 : Blo 2001435 3378523 := bstep (se 1 (by rfl) ⟨2533892, by rfl⟩ : syracuseStep 3378523 = 5067785) B5067785
theorem B4504697 : Blo 2001435 4504697 := bstep (se 2 (by rfl) ⟨1689261, by rfl⟩ : syracuseStep 4504697 = 3378523) B3378523
theorem B3003131 : Blo 2001435 3003131 := bstep (se 1 (by rfl) ⟨2252348, by rfl⟩ : syracuseStep 3003131 = 4504697) B4504697
theorem B2002087 : Blo 2001435 2002087 := bstep (se 1 (by rfl) ⟨1501565, by rfl⟩ : syracuseStep 2002087 = 3003131) B3003131
theorem B2252353 : Blo 2001435 2252353 := bbase (se 2 (by rfl) ⟨844632, by rfl⟩ : syracuseStep 2252353 = 1689265) (by norm_num)
theorem B3003137 : Blo 2001435 3003137 := bstep (se 2 (by rfl) ⟨1126176, by rfl⟩ : syracuseStep 3003137 = 2252353) B2252353
theorem B2002091 : Blo 2001435 2002091 := bstep (se 1 (by rfl) ⟨1501568, by rfl⟩ : syracuseStep 2002091 = 3003137) B3003137
theorem B5067805 : Blo 2001435 5067805 := bbase (se 3 (by rfl) ⟨950213, by rfl⟩ : syracuseStep 5067805 = 1900427) (by norm_num)
theorem B6757073 : Blo 2001435 6757073 := bstep (se 2 (by rfl) ⟨2533902, by rfl⟩ : syracuseStep 6757073 = 5067805) B5067805
theorem B4504715 : Blo 2001435 4504715 := bstep (se 1 (by rfl) ⟨3378536, by rfl⟩ : syracuseStep 4504715 = 6757073) B6757073
theorem B3003143 : Blo 2001435 3003143 := bstep (se 1 (by rfl) ⟨2252357, by rfl⟩ : syracuseStep 3003143 = 4504715) B4504715
theorem B2002095 : Blo 2001435 2002095 := bstep (se 1 (by rfl) ⟨1501571, by rfl⟩ : syracuseStep 2002095 = 3003143) B3003143
theorem B3003149 : Blo 2001435 3003149 := bbase (se 3 (by rfl) ⟨563090, by rfl⟩ : syracuseStep 3003149 = 1126181) (by norm_num)
theorem B2002099 : Blo 2001435 2002099 := bstep (se 1 (by rfl) ⟨1501574, by rfl⟩ : syracuseStep 2002099 = 3003149) B3003149
theorem B4504733 : Blo 2001435 4504733 := bbase (se 3 (by rfl) ⟨844637, by rfl⟩ : syracuseStep 4504733 = 1689275) (by norm_num)
theorem B3003155 : Blo 2001435 3003155 := bstep (se 1 (by rfl) ⟨2252366, by rfl⟩ : syracuseStep 3003155 = 4504733) B4504733
theorem B2002103 : Blo 2001435 2002103 := bstep (se 1 (by rfl) ⟨1501577, by rfl⟩ : syracuseStep 2002103 = 3003155) B3003155
theorem B3378557 : Blo 2001435 3378557 := bbase (se 3 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 3378557 = 1266959) (by norm_num)
theorem B2252371 : Blo 2001435 2252371 := bstep (se 1 (by rfl) ⟨1689278, by rfl⟩ : syracuseStep 2252371 = 3378557) B3378557
theorem B3003161 : Blo 2001435 3003161 := bstep (se 2 (by rfl) ⟨1126185, by rfl⟩ : syracuseStep 3003161 = 2252371) B2252371
theorem B2002107 : Blo 2001435 2002107 := bstep (se 1 (by rfl) ⟨1501580, by rfl⟩ : syracuseStep 2002107 = 3003161) B3003161
theorem B10020181 : Blo 2001435 10020181 := bbase (se 12 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 10020181 = 7339) (by norm_num)
theorem B13360241 : Blo 2001435 13360241 := bstep (se 2 (by rfl) ⟨5010090, by rfl⟩ : syracuseStep 13360241 = 10020181) B10020181
theorem B35627309 : Blo 2001435 35627309 := bstep (se 3 (by rfl) ⟨6680120, by rfl⟩ : syracuseStep 35627309 = 13360241) B13360241
theorem B23751539 : Blo 2001435 23751539 := bstep (se 1 (by rfl) ⟨17813654, by rfl⟩ : syracuseStep 23751539 = 35627309) B35627309
theorem B15834359 : Blo 2001435 15834359 := bstep (se 1 (by rfl) ⟨11875769, by rfl⟩ : syracuseStep 15834359 = 23751539) B23751539
theorem B10556239 : Blo 2001435 10556239 := bstep (se 1 (by rfl) ⟨7917179, by rfl⟩ : syracuseStep 10556239 = 15834359) B15834359
theorem B14074985 : Blo 2001435 14074985 := bstep (se 2 (by rfl) ⟨5278119, by rfl⟩ : syracuseStep 14074985 = 10556239) B10556239
theorem B37533293 : Blo 2001435 37533293 := bstep (se 3 (by rfl) ⟨7037492, by rfl⟩ : syracuseStep 37533293 = 14074985) B14074985
theorem B25022195 : Blo 2001435 25022195 := bstep (se 1 (by rfl) ⟨18766646, by rfl⟩ : syracuseStep 25022195 = 37533293) B37533293
theorem B16681463 : Blo 2001435 16681463 := bstep (se 1 (by rfl) ⟨12511097, by rfl⟩ : syracuseStep 16681463 = 25022195) B25022195
theorem B11120975 : Blo 2001435 11120975 := bstep (se 1 (by rfl) ⟨8340731, by rfl⟩ : syracuseStep 11120975 = 16681463) B16681463
theorem B7413983 : Blo 2001435 7413983 := bstep (se 1 (by rfl) ⟨5560487, by rfl⟩ : syracuseStep 7413983 = 11120975) B11120975
theorem B4942655 : Blo 2001435 4942655 := bstep (se 1 (by rfl) ⟨3706991, by rfl⟩ : syracuseStep 4942655 = 7413983) B7413983
theorem B3295103 : Blo 2001435 3295103 := bstep (se 1 (by rfl) ⟨2471327, by rfl⟩ : syracuseStep 3295103 = 4942655) B4942655
theorem B35147765 : Blo 2001435 35147765 := bstep (se 5 (by rfl) ⟨1647551, by rfl⟩ : syracuseStep 35147765 = 3295103) B3295103
theorem B23431843 : Blo 2001435 23431843 := bstep (se 1 (by rfl) ⟨17573882, by rfl⟩ : syracuseStep 23431843 = 35147765) B35147765
theorem B31242457 : Blo 2001435 31242457 := bstep (se 2 (by rfl) ⟨11715921, by rfl⟩ : syracuseStep 31242457 = 23431843) B23431843
theorem B41656609 : Blo 2001435 41656609 := bstep (se 2 (by rfl) ⟨15621228, by rfl⟩ : syracuseStep 41656609 = 31242457) B31242457
theorem B55542145 : Blo 2001435 55542145 := bstep (se 2 (by rfl) ⟨20828304, by rfl⟩ : syracuseStep 55542145 = 41656609) B41656609
theorem B74056193 : Blo 2001435 74056193 := bstep (se 2 (by rfl) ⟨27771072, by rfl⟩ : syracuseStep 74056193 = 55542145) B55542145
theorem B49370795 : Blo 2001435 49370795 := bstep (se 1 (by rfl) ⟨37028096, by rfl⟩ : syracuseStep 49370795 = 74056193) B74056193
theorem B32913863 : Blo 2001435 32913863 := bstep (se 1 (by rfl) ⟨24685397, by rfl⟩ : syracuseStep 32913863 = 49370795) B49370795
theorem B21942575 : Blo 2001435 21942575 := bstep (se 1 (by rfl) ⟨16456931, by rfl⟩ : syracuseStep 21942575 = 32913863) B32913863
theorem B14628383 : Blo 2001435 14628383 := bstep (se 1 (by rfl) ⟨10971287, by rfl⟩ : syracuseStep 14628383 = 21942575) B21942575
theorem B9752255 : Blo 2001435 9752255 := bstep (se 1 (by rfl) ⟨7314191, by rfl⟩ : syracuseStep 9752255 = 14628383) B14628383
theorem B6501503 : Blo 2001435 6501503 := bstep (se 1 (by rfl) ⟨4876127, by rfl⟩ : syracuseStep 6501503 = 9752255) B9752255
theorem B4334335 : Blo 2001435 4334335 := bstep (se 1 (by rfl) ⟨3250751, by rfl⟩ : syracuseStep 4334335 = 6501503) B6501503
theorem B92465813 : Blo 2001435 92465813 := bstep (se 6 (by rfl) ⟨2167167, by rfl⟩ : syracuseStep 92465813 = 4334335) B4334335
theorem B61643875 : Blo 2001435 61643875 := bstep (se 1 (by rfl) ⟨46232906, by rfl⟩ : syracuseStep 61643875 = 92465813) B92465813
theorem B82191833 : Blo 2001435 82191833 := bstep (se 2 (by rfl) ⟨30821937, by rfl⟩ : syracuseStep 82191833 = 61643875) B61643875
theorem B54794555 : Blo 2001435 54794555 := bstep (se 1 (by rfl) ⟨41095916, by rfl⟩ : syracuseStep 54794555 = 82191833) B82191833
theorem B36529703 : Blo 2001435 36529703 := bstep (se 1 (by rfl) ⟨27397277, by rfl⟩ : syracuseStep 36529703 = 54794555) B54794555
theorem B24353135 : Blo 2001435 24353135 := bstep (se 1 (by rfl) ⟨18264851, by rfl⟩ : syracuseStep 24353135 = 36529703) B36529703
theorem B16235423 : Blo 2001435 16235423 := bstep (se 1 (by rfl) ⟨12176567, by rfl⟩ : syracuseStep 16235423 = 24353135) B24353135
theorem B10823615 : Blo 2001435 10823615 := bstep (se 1 (by rfl) ⟨8117711, by rfl⟩ : syracuseStep 10823615 = 16235423) B16235423
theorem B7215743 : Blo 2001435 7215743 := bstep (se 1 (by rfl) ⟨5411807, by rfl⟩ : syracuseStep 7215743 = 10823615) B10823615
theorem B4810495 : Blo 2001435 4810495 := bstep (se 1 (by rfl) ⟨3607871, by rfl⟩ : syracuseStep 4810495 = 7215743) B7215743
theorem B6413993 : Blo 2001435 6413993 := bstep (se 2 (by rfl) ⟨2405247, by rfl⟩ : syracuseStep 6413993 = 4810495) B4810495
theorem B4275995 : Blo 2001435 4275995 := bstep (se 1 (by rfl) ⟨3206996, by rfl⟩ : syracuseStep 4275995 = 6413993) B6413993
theorem B11402653 : Blo 2001435 11402653 := bstep (se 3 (by rfl) ⟨2137997, by rfl⟩ : syracuseStep 11402653 = 4275995) B4275995
theorem B15203537 : Blo 2001435 15203537 := bstep (se 2 (by rfl) ⟨5701326, by rfl⟩ : syracuseStep 15203537 = 11402653) B11402653
theorem B10135691 : Blo 2001435 10135691 := bstep (se 1 (by rfl) ⟨7601768, by rfl⟩ : syracuseStep 10135691 = 15203537) B15203537
theorem B6757127 : Blo 2001435 6757127 := bstep (se 1 (by rfl) ⟨5067845, by rfl⟩ : syracuseStep 6757127 = 10135691) B10135691
theorem B4504751 : Blo 2001435 4504751 := bstep (se 1 (by rfl) ⟨3378563, by rfl⟩ : syracuseStep 4504751 = 6757127) B6757127
theorem B3003167 : Blo 2001435 3003167 := bstep (se 1 (by rfl) ⟨2252375, by rfl⟩ : syracuseStep 3003167 = 4504751) B4504751
theorem B2002111 : Blo 2001435 2002111 := bstep (se 1 (by rfl) ⟨1501583, by rfl⟩ : syracuseStep 2002111 = 3003167) B3003167
theorem B3003173 : Blo 2001435 3003173 := bbase (se 4 (by rfl) ⟨281547, by rfl⟩ : syracuseStep 3003173 = 563095) (by norm_num)
theorem B2002115 : Blo 2001435 2002115 := bstep (se 1 (by rfl) ⟨1501586, by rfl⟩ : syracuseStep 2002115 = 3003173) B3003173
theorem B2533933 : Blo 2001435 2533933 := bbase (se 3 (by rfl) ⟨475112, by rfl⟩ : syracuseStep 2533933 = 950225) (by norm_num)
theorem B3378577 : Blo 2001435 3378577 := bstep (se 2 (by rfl) ⟨1266966, by rfl⟩ : syracuseStep 3378577 = 2533933) B2533933
theorem B4504769 : Blo 2001435 4504769 := bstep (se 2 (by rfl) ⟨1689288, by rfl⟩ : syracuseStep 4504769 = 3378577) B3378577
theorem B3003179 : Blo 2001435 3003179 := bstep (se 1 (by rfl) ⟨2252384, by rfl⟩ : syracuseStep 3003179 = 4504769) B4504769
theorem B2002119 : Blo 2001435 2002119 := bstep (se 1 (by rfl) ⟨1501589, by rfl⟩ : syracuseStep 2002119 = 3003179) B3003179
theorem B2252389 : Blo 2001435 2252389 := bbase (se 4 (by rfl) ⟨211161, by rfl⟩ : syracuseStep 2252389 = 422323) (by norm_num)
theorem B3003185 : Blo 2001435 3003185 := bstep (se 2 (by rfl) ⟨1126194, by rfl⟩ : syracuseStep 3003185 = 2252389) B2252389
theorem B2002123 : Blo 2001435 2002123 := bstep (se 1 (by rfl) ⟨1501592, by rfl⟩ : syracuseStep 2002123 = 3003185) B3003185
theorem B2603561 : Blo 2001435 2603561 := bbase (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) (by norm_num)
theorem B6942829 : Blo 2001435 6942829 := bstep (se 3 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 6942829 = 2603561) B2603561
theorem B9257105 : Blo 2001435 9257105 := bstep (se 2 (by rfl) ⟨3471414, by rfl⟩ : syracuseStep 9257105 = 6942829) B6942829
theorem B6171403 : Blo 2001435 6171403 := bstep (se 1 (by rfl) ⟨4628552, by rfl⟩ : syracuseStep 6171403 = 9257105) B9257105
theorem B8228537 : Blo 2001435 8228537 := bstep (se 2 (by rfl) ⟨3085701, by rfl⟩ : syracuseStep 8228537 = 6171403) B6171403
theorem B5485691 : Blo 2001435 5485691 := bstep (se 1 (by rfl) ⟨4114268, by rfl⟩ : syracuseStep 5485691 = 8228537) B8228537
theorem B14628509 : Blo 2001435 14628509 := bstep (se 3 (by rfl) ⟨2742845, by rfl⟩ : syracuseStep 14628509 = 5485691) B5485691
theorem B9752339 : Blo 2001435 9752339 := bstep (se 1 (by rfl) ⟨7314254, by rfl⟩ : syracuseStep 9752339 = 14628509) B14628509
theorem B6501559 : Blo 2001435 6501559 := bstep (se 1 (by rfl) ⟨4876169, by rfl⟩ : syracuseStep 6501559 = 9752339) B9752339
theorem B8668745 : Blo 2001435 8668745 := bstep (se 2 (by rfl) ⟨3250779, by rfl⟩ : syracuseStep 8668745 = 6501559) B6501559
theorem B5779163 : Blo 2001435 5779163 := bstep (se 1 (by rfl) ⟨4334372, by rfl⟩ : syracuseStep 5779163 = 8668745) B8668745
theorem B3852775 : Blo 2001435 3852775 := bstep (se 1 (by rfl) ⟨2889581, by rfl⟩ : syracuseStep 3852775 = 5779163) B5779163
theorem B5137033 : Blo 2001435 5137033 := bstep (se 2 (by rfl) ⟨1926387, by rfl⟩ : syracuseStep 5137033 = 3852775) B3852775
theorem B6849377 : Blo 2001435 6849377 := bstep (se 2 (by rfl) ⟨2568516, by rfl⟩ : syracuseStep 6849377 = 5137033) B5137033
theorem B4566251 : Blo 2001435 4566251 := bstep (se 1 (by rfl) ⟨3424688, by rfl⟩ : syracuseStep 4566251 = 6849377) B6849377
theorem B12176669 : Blo 2001435 12176669 := bstep (se 3 (by rfl) ⟨2283125, by rfl⟩ : syracuseStep 12176669 = 4566251) B4566251
theorem B8117779 : Blo 2001435 8117779 := bstep (se 1 (by rfl) ⟨6088334, by rfl⟩ : syracuseStep 8117779 = 12176669) B12176669
theorem B10823705 : Blo 2001435 10823705 := bstep (se 2 (by rfl) ⟨4058889, by rfl⟩ : syracuseStep 10823705 = 8117779) B8117779
theorem B7215803 : Blo 2001435 7215803 := bstep (se 1 (by rfl) ⟨5411852, by rfl⟩ : syracuseStep 7215803 = 10823705) B10823705
theorem B4810535 : Blo 2001435 4810535 := bstep (se 1 (by rfl) ⟨3607901, by rfl⟩ : syracuseStep 4810535 = 7215803) B7215803
theorem B3207023 : Blo 2001435 3207023 := bstep (se 1 (by rfl) ⟨2405267, by rfl⟩ : syracuseStep 3207023 = 4810535) B4810535
theorem B2138015 : Blo 2001435 2138015 := bstep (se 1 (by rfl) ⟨1603511, by rfl⟩ : syracuseStep 2138015 = 3207023) B3207023
theorem B5701373 : Blo 2001435 5701373 := bstep (se 3 (by rfl) ⟨1069007, by rfl⟩ : syracuseStep 5701373 = 2138015) B2138015
theorem B3800915 : Blo 2001435 3800915 := bstep (se 1 (by rfl) ⟨2850686, by rfl⟩ : syracuseStep 3800915 = 5701373) B5701373
theorem B2533943 : Blo 2001435 2533943 := bstep (se 1 (by rfl) ⟨1900457, by rfl⟩ : syracuseStep 2533943 = 3800915) B3800915
theorem B6757181 : Blo 2001435 6757181 := bstep (se 3 (by rfl) ⟨1266971, by rfl⟩ : syracuseStep 6757181 = 2533943) B2533943
theorem B4504787 : Blo 2001435 4504787 := bstep (se 1 (by rfl) ⟨3378590, by rfl⟩ : syracuseStep 4504787 = 6757181) B6757181
theorem B3003191 : Blo 2001435 3003191 := bstep (se 1 (by rfl) ⟨2252393, by rfl⟩ : syracuseStep 3003191 = 4504787) B4504787
theorem B2002127 : Blo 2001435 2002127 := bstep (se 1 (by rfl) ⟨1501595, by rfl⟩ : syracuseStep 2002127 = 3003191) B3003191
theorem B3003197 : Blo 2001435 3003197 := bbase (se 3 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 3003197 = 1126199) (by norm_num)
theorem B2002131 : Blo 2001435 2002131 := bstep (se 1 (by rfl) ⟨1501598, by rfl⟩ : syracuseStep 2002131 = 3003197) B3003197
theorem B4504805 : Blo 2001435 4504805 := bbase (se 4 (by rfl) ⟨422325, by rfl⟩ : syracuseStep 4504805 = 844651) (by norm_num)
theorem B3003203 : Blo 2001435 3003203 := bstep (se 1 (by rfl) ⟨2252402, by rfl⟩ : syracuseStep 3003203 = 4504805) B4504805
theorem B2002135 : Blo 2001435 2002135 := bstep (se 1 (by rfl) ⟨1501601, by rfl⟩ : syracuseStep 2002135 = 3003203) B3003203
theorem B5067917 : Blo 2001435 5067917 := bbase (se 3 (by rfl) ⟨950234, by rfl⟩ : syracuseStep 5067917 = 1900469) (by norm_num)
theorem B3378611 : Blo 2001435 3378611 := bstep (se 1 (by rfl) ⟨2533958, by rfl⟩ : syracuseStep 3378611 = 5067917) B5067917
theorem B2252407 : Blo 2001435 2252407 := bstep (se 1 (by rfl) ⟨1689305, by rfl⟩ : syracuseStep 2252407 = 3378611) B3378611
theorem B3003209 : Blo 2001435 3003209 := bstep (se 2 (by rfl) ⟨1126203, by rfl⟩ : syracuseStep 3003209 = 2252407) B2252407
theorem B2002139 : Blo 2001435 2002139 := bstep (se 1 (by rfl) ⟨1501604, by rfl⟩ : syracuseStep 2002139 = 3003209) B3003209
theorem B2850709 : Blo 2001435 2850709 := bbase (se 6 (by rfl) ⟨66813, by rfl⟩ : syracuseStep 2850709 = 133627) (by norm_num)
theorem B3800945 : Blo 2001435 3800945 := bstep (se 2 (by rfl) ⟨1425354, by rfl⟩ : syracuseStep 3800945 = 2850709) B2850709
theorem B10135853 : Blo 2001435 10135853 := bstep (se 3 (by rfl) ⟨1900472, by rfl⟩ : syracuseStep 10135853 = 3800945) B3800945
theorem B6757235 : Blo 2001435 6757235 := bstep (se 1 (by rfl) ⟨5067926, by rfl⟩ : syracuseStep 6757235 = 10135853) B10135853
theorem B4504823 : Blo 2001435 4504823 := bstep (se 1 (by rfl) ⟨3378617, by rfl⟩ : syracuseStep 4504823 = 6757235) B6757235
theorem B3003215 : Blo 2001435 3003215 := bstep (se 1 (by rfl) ⟨2252411, by rfl⟩ : syracuseStep 3003215 = 4504823) B4504823
theorem B2002143 : Blo 2001435 2002143 := bstep (se 1 (by rfl) ⟨1501607, by rfl⟩ : syracuseStep 2002143 = 3003215) B3003215
theorem B3003221 : Blo 2001435 3003221 := bbase (se 9 (by rfl) ⟨8798, by rfl⟩ : syracuseStep 3003221 = 17597) (by norm_num)
theorem B2002147 : Blo 2001435 2002147 := bstep (se 1 (by rfl) ⟨1501610, by rfl⟩ : syracuseStep 2002147 = 3003221) B3003221
theorem B3207061 : Blo 2001435 3207061 := bbase (se 6 (by rfl) ⟨75165, by rfl⟩ : syracuseStep 3207061 = 150331) (by norm_num)
theorem B4276081 : Blo 2001435 4276081 := bstep (se 2 (by rfl) ⟨1603530, by rfl⟩ : syracuseStep 4276081 = 3207061) B3207061
theorem B5701441 : Blo 2001435 5701441 := bstep (se 2 (by rfl) ⟨2138040, by rfl⟩ : syracuseStep 5701441 = 4276081) B4276081
theorem B7601921 : Blo 2001435 7601921 := bstep (se 2 (by rfl) ⟨2850720, by rfl⟩ : syracuseStep 7601921 = 5701441) B5701441
theorem B5067947 : Blo 2001435 5067947 := bstep (se 1 (by rfl) ⟨3800960, by rfl⟩ : syracuseStep 5067947 = 7601921) B7601921
theorem B3378631 : Blo 2001435 3378631 := bstep (se 1 (by rfl) ⟨2533973, by rfl⟩ : syracuseStep 3378631 = 5067947) B5067947
theorem B4504841 : Blo 2001435 4504841 := bstep (se 2 (by rfl) ⟨1689315, by rfl⟩ : syracuseStep 4504841 = 3378631) B3378631
theorem B3003227 : Blo 2001435 3003227 := bstep (se 1 (by rfl) ⟨2252420, by rfl⟩ : syracuseStep 3003227 = 4504841) B4504841
theorem B2002151 : Blo 2001435 2002151 := bstep (se 1 (by rfl) ⟨1501613, by rfl⟩ : syracuseStep 2002151 = 3003227) B3003227
theorem B2252425 : Blo 2001435 2252425 := bbase (se 2 (by rfl) ⟨844659, by rfl⟩ : syracuseStep 2252425 = 1689319) (by norm_num)
theorem B3003233 : Blo 2001435 3003233 := bstep (se 2 (by rfl) ⟨1126212, by rfl⟩ : syracuseStep 3003233 = 2252425) B2252425
theorem B2002155 : Blo 2001435 2002155 := bstep (se 1 (by rfl) ⟨1501616, by rfl⟩ : syracuseStep 2002155 = 3003233) B3003233
theorem B2283161 : Blo 2001435 2283161 := bbase (se 2 (by rfl) ⟨856185, by rfl⟩ : syracuseStep 2283161 = 1712371) (by norm_num)
theorem B6088429 : Blo 2001435 6088429 := bstep (se 3 (by rfl) ⟨1141580, by rfl⟩ : syracuseStep 6088429 = 2283161) B2283161
theorem B8117905 : Blo 2001435 8117905 := bstep (se 2 (by rfl) ⟨3044214, by rfl⟩ : syracuseStep 8117905 = 6088429) B6088429
theorem B10823873 : Blo 2001435 10823873 := bstep (se 2 (by rfl) ⟨4058952, by rfl⟩ : syracuseStep 10823873 = 8117905) B8117905
theorem B28863661 : Blo 2001435 28863661 := bstep (se 3 (by rfl) ⟨5411936, by rfl⟩ : syracuseStep 28863661 = 10823873) B10823873
theorem B38484881 : Blo 2001435 38484881 := bstep (se 2 (by rfl) ⟨14431830, by rfl⟩ : syracuseStep 38484881 = 28863661) B28863661
theorem B25656587 : Blo 2001435 25656587 := bstep (se 1 (by rfl) ⟨19242440, by rfl⟩ : syracuseStep 25656587 = 38484881) B38484881
theorem B17104391 : Blo 2001435 17104391 := bstep (se 1 (by rfl) ⟨12828293, by rfl⟩ : syracuseStep 17104391 = 25656587) B25656587
theorem B11402927 : Blo 2001435 11402927 := bstep (se 1 (by rfl) ⟨8552195, by rfl⟩ : syracuseStep 11402927 = 17104391) B17104391
theorem B7601951 : Blo 2001435 7601951 := bstep (se 1 (by rfl) ⟨5701463, by rfl⟩ : syracuseStep 7601951 = 11402927) B11402927
theorem B5067967 : Blo 2001435 5067967 := bstep (se 1 (by rfl) ⟨3800975, by rfl⟩ : syracuseStep 5067967 = 7601951) B7601951
theorem B6757289 : Blo 2001435 6757289 := bstep (se 2 (by rfl) ⟨2533983, by rfl⟩ : syracuseStep 6757289 = 5067967) B5067967
theorem B4504859 : Blo 2001435 4504859 := bstep (se 1 (by rfl) ⟨3378644, by rfl⟩ : syracuseStep 4504859 = 6757289) B6757289
theorem B3003239 : Blo 2001435 3003239 := bstep (se 1 (by rfl) ⟨2252429, by rfl⟩ : syracuseStep 3003239 = 4504859) B4504859
theorem B2002159 : Blo 2001435 2002159 := bstep (se 1 (by rfl) ⟨1501619, by rfl⟩ : syracuseStep 2002159 = 3003239) B3003239
theorem B3003245 : Blo 2001435 3003245 := bbase (se 3 (by rfl) ⟨563108, by rfl⟩ : syracuseStep 3003245 = 1126217) (by norm_num)
theorem B2002163 : Blo 2001435 2002163 := bstep (se 1 (by rfl) ⟨1501622, by rfl⟩ : syracuseStep 2002163 = 3003245) B3003245
theorem B4504877 : Blo 2001435 4504877 := bbase (se 3 (by rfl) ⟨844664, by rfl⟩ : syracuseStep 4504877 = 1689329) (by norm_num)
theorem B3003251 : Blo 2001435 3003251 := bstep (se 1 (by rfl) ⟨2252438, by rfl⟩ : syracuseStep 3003251 = 4504877) B4504877
theorem B2002167 : Blo 2001435 2002167 := bstep (se 1 (by rfl) ⟨1501625, by rfl⟩ : syracuseStep 2002167 = 3003251) B3003251
theorem B8117957 : Blo 2001435 8117957 := bbase (se 4 (by rfl) ⟨761058, by rfl⟩ : syracuseStep 8117957 = 1522117) (by norm_num)
theorem B5411971 : Blo 2001435 5411971 := bstep (se 1 (by rfl) ⟨4058978, by rfl⟩ : syracuseStep 5411971 = 8117957) B8117957
theorem B7215961 : Blo 2001435 7215961 := bstep (se 2 (by rfl) ⟨2705985, by rfl⟩ : syracuseStep 7215961 = 5411971) B5411971
theorem B9621281 : Blo 2001435 9621281 := bstep (se 2 (by rfl) ⟨3607980, by rfl⟩ : syracuseStep 9621281 = 7215961) B7215961
theorem B6414187 : Blo 2001435 6414187 := bstep (se 1 (by rfl) ⟨4810640, by rfl⟩ : syracuseStep 6414187 = 9621281) B9621281
theorem B8552249 : Blo 2001435 8552249 := bstep (se 2 (by rfl) ⟨3207093, by rfl⟩ : syracuseStep 8552249 = 6414187) B6414187
theorem B5701499 : Blo 2001435 5701499 := bstep (se 1 (by rfl) ⟨4276124, by rfl⟩ : syracuseStep 5701499 = 8552249) B8552249
theorem B3800999 : Blo 2001435 3800999 := bstep (se 1 (by rfl) ⟨2850749, by rfl⟩ : syracuseStep 3800999 = 5701499) B5701499
theorem B2533999 : Blo 2001435 2533999 := bstep (se 1 (by rfl) ⟨1900499, by rfl⟩ : syracuseStep 2533999 = 3800999) B3800999
theorem B3378665 : Blo 2001435 3378665 := bstep (se 2 (by rfl) ⟨1266999, by rfl⟩ : syracuseStep 3378665 = 2533999) B2533999
theorem B2252443 : Blo 2001435 2252443 := bstep (se 1 (by rfl) ⟨1689332, by rfl⟩ : syracuseStep 2252443 = 3378665) B3378665
theorem B3003257 : Blo 2001435 3003257 := bstep (se 2 (by rfl) ⟨1126221, by rfl⟩ : syracuseStep 3003257 = 2252443) B2252443
theorem B2002171 : Blo 2001435 2002171 := bstep (se 1 (by rfl) ⟨1501628, by rfl⟩ : syracuseStep 2002171 = 3003257) B3003257
theorem B2568577 : Blo 2001435 2568577 := bbase (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) (by norm_num)
theorem B3424769 : Blo 2001435 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B2283179 : Blo 2001435 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B24353909 : Blo 2001435 24353909 := bstep (se 5 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 24353909 = 2283179) B2283179
theorem B16235939 : Blo 2001435 16235939 := bstep (se 1 (by rfl) ⟨12176954, by rfl⟩ : syracuseStep 16235939 = 24353909) B24353909
theorem B10823959 : Blo 2001435 10823959 := bstep (se 1 (by rfl) ⟨8117969, by rfl⟩ : syracuseStep 10823959 = 16235939) B16235939
theorem B14431945 : Blo 2001435 14431945 := bstep (se 2 (by rfl) ⟨5411979, by rfl⟩ : syracuseStep 14431945 = 10823959) B10823959
theorem B19242593 : Blo 2001435 19242593 := bstep (se 2 (by rfl) ⟨7215972, by rfl⟩ : syracuseStep 19242593 = 14431945) B14431945
theorem B12828395 : Blo 2001435 12828395 := bstep (se 1 (by rfl) ⟨9621296, by rfl⟩ : syracuseStep 12828395 = 19242593) B19242593
theorem B34209053 : Blo 2001435 34209053 := bstep (se 3 (by rfl) ⟨6414197, by rfl⟩ : syracuseStep 34209053 = 12828395) B12828395
theorem B22806035 : Blo 2001435 22806035 := bstep (se 1 (by rfl) ⟨17104526, by rfl⟩ : syracuseStep 22806035 = 34209053) B34209053
theorem B15204023 : Blo 2001435 15204023 := bstep (se 1 (by rfl) ⟨11403017, by rfl⟩ : syracuseStep 15204023 = 22806035) B22806035
theorem B10136015 : Blo 2001435 10136015 := bstep (se 1 (by rfl) ⟨7602011, by rfl⟩ : syracuseStep 10136015 = 15204023) B15204023
theorem B6757343 : Blo 2001435 6757343 := bstep (se 1 (by rfl) ⟨5068007, by rfl⟩ : syracuseStep 6757343 = 10136015) B10136015
theorem B4504895 : Blo 2001435 4504895 := bstep (se 1 (by rfl) ⟨3378671, by rfl⟩ : syracuseStep 4504895 = 6757343) B6757343
theorem B3003263 : Blo 2001435 3003263 := bstep (se 1 (by rfl) ⟨2252447, by rfl⟩ : syracuseStep 3003263 = 4504895) B4504895
theorem B2002175 : Blo 2001435 2002175 := bstep (se 1 (by rfl) ⟨1501631, by rfl⟩ : syracuseStep 2002175 = 3003263) B3003263
theorem B3003269 : Blo 2001435 3003269 := bbase (se 4 (by rfl) ⟨281556, by rfl⟩ : syracuseStep 3003269 = 563113) (by norm_num)
theorem B2002179 : Blo 2001435 2002179 := bstep (se 1 (by rfl) ⟨1501634, by rfl⟩ : syracuseStep 2002179 = 3003269) B3003269
theorem B3378685 : Blo 2001435 3378685 := bbase (se 3 (by rfl) ⟨633503, by rfl⟩ : syracuseStep 3378685 = 1267007) (by norm_num)
theorem B4504913 : Blo 2001435 4504913 := bstep (se 2 (by rfl) ⟨1689342, by rfl⟩ : syracuseStep 4504913 = 3378685) B3378685
theorem B3003275 : Blo 2001435 3003275 := bstep (se 1 (by rfl) ⟨2252456, by rfl⟩ : syracuseStep 3003275 = 4504913) B4504913
theorem B2002183 : Blo 2001435 2002183 := bstep (se 1 (by rfl) ⟨1501637, by rfl⟩ : syracuseStep 2002183 = 3003275) B3003275
theorem B2252461 : Blo 2001435 2252461 := bbase (se 3 (by rfl) ⟨422336, by rfl⟩ : syracuseStep 2252461 = 844673) (by norm_num)
theorem B3003281 : Blo 2001435 3003281 := bstep (se 2 (by rfl) ⟨1126230, by rfl⟩ : syracuseStep 3003281 = 2252461) B2252461
theorem B2002187 : Blo 2001435 2002187 := bstep (se 1 (by rfl) ⟨1501640, by rfl⟩ : syracuseStep 2002187 = 3003281) B3003281
theorem B6757397 : Blo 2001435 6757397 := bbase (se 6 (by rfl) ⟨158376, by rfl⟩ : syracuseStep 6757397 = 316753) (by norm_num)
theorem B4504931 : Blo 2001435 4504931 := bstep (se 1 (by rfl) ⟨3378698, by rfl⟩ : syracuseStep 4504931 = 6757397) B6757397
theorem B3003287 : Blo 2001435 3003287 := bstep (se 1 (by rfl) ⟨2252465, by rfl⟩ : syracuseStep 3003287 = 4504931) B4504931
theorem B2002191 : Blo 2001435 2002191 := bstep (se 1 (by rfl) ⟨1501643, by rfl⟩ : syracuseStep 2002191 = 3003287) B3003287
theorem B3003293 : Blo 2001435 3003293 := bbase (se 3 (by rfl) ⟨563117, by rfl⟩ : syracuseStep 3003293 = 1126235) (by norm_num)
theorem B2002195 : Blo 2001435 2002195 := bstep (se 1 (by rfl) ⟨1501646, by rfl⟩ : syracuseStep 2002195 = 3003293) B3003293
theorem B4504949 : Blo 2001435 4504949 := bbase (se 5 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 4504949 = 422339) (by norm_num)
theorem B3003299 : Blo 2001435 3003299 := bstep (se 1 (by rfl) ⟨2252474, by rfl⟩ : syracuseStep 3003299 = 4504949) B4504949
theorem B2002199 : Blo 2001435 2002199 := bstep (se 1 (by rfl) ⟨1501649, by rfl⟩ : syracuseStep 2002199 = 3003299) B3003299
theorem B8118085 : Blo 2001435 8118085 := bbase (se 4 (by rfl) ⟨761070, by rfl⟩ : syracuseStep 8118085 = 1522141) (by norm_num)
theorem B10824113 : Blo 2001435 10824113 := bstep (se 2 (by rfl) ⟨4059042, by rfl⟩ : syracuseStep 10824113 = 8118085) B8118085
theorem B7216075 : Blo 2001435 7216075 := bstep (se 1 (by rfl) ⟨5412056, by rfl⟩ : syracuseStep 7216075 = 10824113) B10824113
theorem B9621433 : Blo 2001435 9621433 := bstep (se 2 (by rfl) ⟨3608037, by rfl⟩ : syracuseStep 9621433 = 7216075) B7216075
theorem B12828577 : Blo 2001435 12828577 := bstep (se 2 (by rfl) ⟨4810716, by rfl⟩ : syracuseStep 12828577 = 9621433) B9621433
theorem B17104769 : Blo 2001435 17104769 := bstep (se 2 (by rfl) ⟨6414288, by rfl⟩ : syracuseStep 17104769 = 12828577) B12828577
theorem B11403179 : Blo 2001435 11403179 := bstep (se 1 (by rfl) ⟨8552384, by rfl⟩ : syracuseStep 11403179 = 17104769) B17104769
theorem B7602119 : Blo 2001435 7602119 := bstep (se 1 (by rfl) ⟨5701589, by rfl⟩ : syracuseStep 7602119 = 11403179) B11403179
theorem B5068079 : Blo 2001435 5068079 := bstep (se 1 (by rfl) ⟨3801059, by rfl⟩ : syracuseStep 5068079 = 7602119) B7602119
theorem B3378719 : Blo 2001435 3378719 := bstep (se 1 (by rfl) ⟨2534039, by rfl⟩ : syracuseStep 3378719 = 5068079) B5068079
theorem B2252479 : Blo 2001435 2252479 := bstep (se 1 (by rfl) ⟨1689359, by rfl⟩ : syracuseStep 2252479 = 3378719) B3378719
theorem B3003305 : Blo 2001435 3003305 := bstep (se 2 (by rfl) ⟨1126239, by rfl⟩ : syracuseStep 3003305 = 2252479) B2252479
theorem B2002203 : Blo 2001435 2002203 := bstep (se 1 (by rfl) ⟨1501652, by rfl⟩ : syracuseStep 2002203 = 3003305) B3003305
theorem B7602133 : Blo 2001435 7602133 := bbase (se 7 (by rfl) ⟨89087, by rfl⟩ : syracuseStep 7602133 = 178175) (by norm_num)
theorem B10136177 : Blo 2001435 10136177 := bstep (se 2 (by rfl) ⟨3801066, by rfl⟩ : syracuseStep 10136177 = 7602133) B7602133
theorem B6757451 : Blo 2001435 6757451 := bstep (se 1 (by rfl) ⟨5068088, by rfl⟩ : syracuseStep 6757451 = 10136177) B10136177
theorem B4504967 : Blo 2001435 4504967 := bstep (se 1 (by rfl) ⟨3378725, by rfl⟩ : syracuseStep 4504967 = 6757451) B6757451
theorem B3003311 : Blo 2001435 3003311 := bstep (se 1 (by rfl) ⟨2252483, by rfl⟩ : syracuseStep 3003311 = 4504967) B4504967
theorem B2002207 : Blo 2001435 2002207 := bstep (se 1 (by rfl) ⟨1501655, by rfl⟩ : syracuseStep 2002207 = 3003311) B3003311
theorem B3003317 : Blo 2001435 3003317 := bbase (se 5 (by rfl) ⟨140780, by rfl⟩ : syracuseStep 3003317 = 281561) (by norm_num)
theorem B2002211 : Blo 2001435 2002211 := bstep (se 1 (by rfl) ⟨1501658, by rfl⟩ : syracuseStep 2002211 = 3003317) B3003317
theorem B5068109 : Blo 2001435 5068109 := bbase (se 3 (by rfl) ⟨950270, by rfl⟩ : syracuseStep 5068109 = 1900541) (by norm_num)
theorem B3378739 : Blo 2001435 3378739 := bstep (se 1 (by rfl) ⟨2534054, by rfl⟩ : syracuseStep 3378739 = 5068109) B5068109
theorem B4504985 : Blo 2001435 4504985 := bstep (se 2 (by rfl) ⟨1689369, by rfl⟩ : syracuseStep 4504985 = 3378739) B3378739
theorem B3003323 : Blo 2001435 3003323 := bstep (se 1 (by rfl) ⟨2252492, by rfl⟩ : syracuseStep 3003323 = 4504985) B4504985
theorem B2002215 : Blo 2001435 2002215 := bstep (se 1 (by rfl) ⟨1501661, by rfl⟩ : syracuseStep 2002215 = 3003323) B3003323
theorem B2252497 : Blo 2001435 2252497 := bbase (se 2 (by rfl) ⟨844686, by rfl⟩ : syracuseStep 2252497 = 1689373) (by norm_num)
theorem B3003329 : Blo 2001435 3003329 := bstep (se 2 (by rfl) ⟨1126248, by rfl⟩ : syracuseStep 3003329 = 2252497) B2252497
theorem B2002219 : Blo 2001435 2002219 := bstep (se 1 (by rfl) ⟨1501664, by rfl⟩ : syracuseStep 2002219 = 3003329) B3003329
theorem B4810765 : Blo 2001435 4810765 := bbase (se 3 (by rfl) ⟨902018, by rfl⟩ : syracuseStep 4810765 = 1804037) (by norm_num)
theorem B6414353 : Blo 2001435 6414353 := bstep (se 2 (by rfl) ⟨2405382, by rfl⟩ : syracuseStep 6414353 = 4810765) B4810765
theorem B4276235 : Blo 2001435 4276235 := bstep (se 1 (by rfl) ⟨3207176, by rfl⟩ : syracuseStep 4276235 = 6414353) B6414353
theorem B2850823 : Blo 2001435 2850823 := bstep (se 1 (by rfl) ⟨2138117, by rfl⟩ : syracuseStep 2850823 = 4276235) B4276235
theorem B3801097 : Blo 2001435 3801097 := bstep (se 2 (by rfl) ⟨1425411, by rfl⟩ : syracuseStep 3801097 = 2850823) B2850823
theorem B5068129 : Blo 2001435 5068129 := bstep (se 2 (by rfl) ⟨1900548, by rfl⟩ : syracuseStep 5068129 = 3801097) B3801097
theorem B6757505 : Blo 2001435 6757505 := bstep (se 2 (by rfl) ⟨2534064, by rfl⟩ : syracuseStep 6757505 = 5068129) B5068129
theorem B4505003 : Blo 2001435 4505003 := bstep (se 1 (by rfl) ⟨3378752, by rfl⟩ : syracuseStep 4505003 = 6757505) B6757505
theorem B3003335 : Blo 2001435 3003335 := bstep (se 1 (by rfl) ⟨2252501, by rfl⟩ : syracuseStep 3003335 = 4505003) B4505003
theorem B2002223 : Blo 2001435 2002223 := bstep (se 1 (by rfl) ⟨1501667, by rfl⟩ : syracuseStep 2002223 = 3003335) B3003335
theorem B3003341 : Blo 2001435 3003341 := bbase (se 3 (by rfl) ⟨563126, by rfl⟩ : syracuseStep 3003341 = 1126253) (by norm_num)
theorem B2002227 : Blo 2001435 2002227 := bstep (se 1 (by rfl) ⟨1501670, by rfl⟩ : syracuseStep 2002227 = 3003341) B3003341
theorem B4505021 : Blo 2001435 4505021 := bbase (se 3 (by rfl) ⟨844691, by rfl⟩ : syracuseStep 4505021 = 1689383) (by norm_num)
theorem B3003347 : Blo 2001435 3003347 := bstep (se 1 (by rfl) ⟨2252510, by rfl⟩ : syracuseStep 3003347 = 4505021) B4505021
theorem B2002231 : Blo 2001435 2002231 := bstep (se 1 (by rfl) ⟨1501673, by rfl⟩ : syracuseStep 2002231 = 3003347) B3003347
theorem B3378773 : Blo 2001435 3378773 := bbase (se 8 (by rfl) ⟨19797, by rfl⟩ : syracuseStep 3378773 = 39595) (by norm_num)
theorem B2252515 : Blo 2001435 2252515 := bstep (se 1 (by rfl) ⟨1689386, by rfl⟩ : syracuseStep 2252515 = 3378773) B3378773
theorem B3003353 : Blo 2001435 3003353 := bstep (se 2 (by rfl) ⟨1126257, by rfl⟩ : syracuseStep 3003353 = 2252515) B2252515
theorem B2002235 : Blo 2001435 2002235 := bstep (se 1 (by rfl) ⟨1501676, by rfl⟩ : syracuseStep 2002235 = 3003353) B3003353
theorem B9621605 : Blo 2001435 9621605 := bbase (se 4 (by rfl) ⟨902025, by rfl⟩ : syracuseStep 9621605 = 1804051) (by norm_num)
theorem B6414403 : Blo 2001435 6414403 := bstep (se 1 (by rfl) ⟨4810802, by rfl⟩ : syracuseStep 6414403 = 9621605) B9621605
theorem B8552537 : Blo 2001435 8552537 := bstep (se 2 (by rfl) ⟨3207201, by rfl⟩ : syracuseStep 8552537 = 6414403) B6414403
theorem B5701691 : Blo 2001435 5701691 := bstep (se 1 (by rfl) ⟨4276268, by rfl⟩ : syracuseStep 5701691 = 8552537) B8552537
theorem B15204509 : Blo 2001435 15204509 := bstep (se 3 (by rfl) ⟨2850845, by rfl⟩ : syracuseStep 15204509 = 5701691) B5701691
theorem B10136339 : Blo 2001435 10136339 := bstep (se 1 (by rfl) ⟨7602254, by rfl⟩ : syracuseStep 10136339 = 15204509) B15204509
theorem B6757559 : Blo 2001435 6757559 := bstep (se 1 (by rfl) ⟨5068169, by rfl⟩ : syracuseStep 6757559 = 10136339) B10136339
theorem B4505039 : Blo 2001435 4505039 := bstep (se 1 (by rfl) ⟨3378779, by rfl⟩ : syracuseStep 4505039 = 6757559) B6757559
theorem B3003359 : Blo 2001435 3003359 := bstep (se 1 (by rfl) ⟨2252519, by rfl⟩ : syracuseStep 3003359 = 4505039) B4505039
theorem B2002239 : Blo 2001435 2002239 := bstep (se 1 (by rfl) ⟨1501679, by rfl⟩ : syracuseStep 2002239 = 3003359) B3003359
theorem B3003365 : Blo 2001435 3003365 := bbase (se 4 (by rfl) ⟨281565, by rfl⟩ : syracuseStep 3003365 = 563131) (by norm_num)
theorem B2002243 : Blo 2001435 2002243 := bstep (se 1 (by rfl) ⟨1501682, by rfl⟩ : syracuseStep 2002243 = 3003365) B3003365
theorem B2057257 : Blo 2001435 2057257 := bbase (se 2 (by rfl) ⟨771471, by rfl⟩ : syracuseStep 2057257 = 1542943) (by norm_num)
theorem B10972037 : Blo 2001435 10972037 := bstep (se 4 (by rfl) ⟨1028628, by rfl⟩ : syracuseStep 10972037 = 2057257) B2057257
theorem B29258765 : Blo 2001435 29258765 := bstep (se 3 (by rfl) ⟨5486018, by rfl⟩ : syracuseStep 29258765 = 10972037) B10972037
theorem B19505843 : Blo 2001435 19505843 := bstep (se 1 (by rfl) ⟨14629382, by rfl⟩ : syracuseStep 19505843 = 29258765) B29258765
theorem B13003895 : Blo 2001435 13003895 := bstep (se 1 (by rfl) ⟨9752921, by rfl⟩ : syracuseStep 13003895 = 19505843) B19505843
theorem B8669263 : Blo 2001435 8669263 := bstep (se 1 (by rfl) ⟨6501947, by rfl⟩ : syracuseStep 8669263 = 13003895) B13003895
theorem B11559017 : Blo 2001435 11559017 := bstep (se 2 (by rfl) ⟨4334631, by rfl⟩ : syracuseStep 11559017 = 8669263) B8669263
theorem B7706011 : Blo 2001435 7706011 := bstep (se 1 (by rfl) ⟨5779508, by rfl⟩ : syracuseStep 7706011 = 11559017) B11559017
theorem B10274681 : Blo 2001435 10274681 := bstep (se 2 (by rfl) ⟨3853005, by rfl⟩ : syracuseStep 10274681 = 7706011) B7706011
theorem B6849787 : Blo 2001435 6849787 := bstep (se 1 (by rfl) ⟨5137340, by rfl⟩ : syracuseStep 6849787 = 10274681) B10274681
theorem B9133049 : Blo 2001435 9133049 := bstep (se 2 (by rfl) ⟨3424893, by rfl⟩ : syracuseStep 9133049 = 6849787) B6849787
theorem B6088699 : Blo 2001435 6088699 := bstep (se 1 (by rfl) ⟨4566524, by rfl⟩ : syracuseStep 6088699 = 9133049) B9133049
theorem B8118265 : Blo 2001435 8118265 := bstep (se 2 (by rfl) ⟨3044349, by rfl⟩ : syracuseStep 8118265 = 6088699) B6088699
theorem B10824353 : Blo 2001435 10824353 := bstep (se 2 (by rfl) ⟨4059132, by rfl⟩ : syracuseStep 10824353 = 8118265) B8118265
theorem B7216235 : Blo 2001435 7216235 := bstep (se 1 (by rfl) ⟨5412176, by rfl⟩ : syracuseStep 7216235 = 10824353) B10824353
theorem B4810823 : Blo 2001435 4810823 := bstep (se 1 (by rfl) ⟨3608117, by rfl⟩ : syracuseStep 4810823 = 7216235) B7216235
theorem B3207215 : Blo 2001435 3207215 := bstep (se 1 (by rfl) ⟨2405411, by rfl⟩ : syracuseStep 3207215 = 4810823) B4810823
theorem B8552573 : Blo 2001435 8552573 := bstep (se 3 (by rfl) ⟨1603607, by rfl⟩ : syracuseStep 8552573 = 3207215) B3207215
theorem B5701715 : Blo 2001435 5701715 := bstep (se 1 (by rfl) ⟨4276286, by rfl⟩ : syracuseStep 5701715 = 8552573) B8552573
theorem B3801143 : Blo 2001435 3801143 := bstep (se 1 (by rfl) ⟨2850857, by rfl⟩ : syracuseStep 3801143 = 5701715) B5701715
theorem B2534095 : Blo 2001435 2534095 := bstep (se 1 (by rfl) ⟨1900571, by rfl⟩ : syracuseStep 2534095 = 3801143) B3801143
theorem B3378793 : Blo 2001435 3378793 := bstep (se 2 (by rfl) ⟨1267047, by rfl⟩ : syracuseStep 3378793 = 2534095) B2534095
theorem B4505057 : Blo 2001435 4505057 := bstep (se 2 (by rfl) ⟨1689396, by rfl⟩ : syracuseStep 4505057 = 3378793) B3378793
theorem B3003371 : Blo 2001435 3003371 := bstep (se 1 (by rfl) ⟨2252528, by rfl⟩ : syracuseStep 3003371 = 4505057) B4505057
theorem B2002247 : Blo 2001435 2002247 := bstep (se 1 (by rfl) ⟨1501685, by rfl⟩ : syracuseStep 2002247 = 3003371) B3003371
theorem B2252533 : Blo 2001435 2252533 := bbase (se 5 (by rfl) ⟨105587, by rfl⟩ : syracuseStep 2252533 = 211175) (by norm_num)
theorem B3003377 : Blo 2001435 3003377 := bstep (se 2 (by rfl) ⟨1126266, by rfl⟩ : syracuseStep 3003377 = 2252533) B2252533
theorem B2002251 : Blo 2001435 2002251 := bstep (se 1 (by rfl) ⟨1501688, by rfl⟩ : syracuseStep 2002251 = 3003377) B3003377
theorem B2534105 : Blo 2001435 2534105 := bbase (se 2 (by rfl) ⟨950289, by rfl⟩ : syracuseStep 2534105 = 1900579) (by norm_num)
theorem B6757613 : Blo 2001435 6757613 := bstep (se 3 (by rfl) ⟨1267052, by rfl⟩ : syracuseStep 6757613 = 2534105) B2534105
theorem B4505075 : Blo 2001435 4505075 := bstep (se 1 (by rfl) ⟨3378806, by rfl⟩ : syracuseStep 4505075 = 6757613) B6757613
theorem B3003383 : Blo 2001435 3003383 := bstep (se 1 (by rfl) ⟨2252537, by rfl⟩ : syracuseStep 3003383 = 4505075) B4505075
theorem B2002255 : Blo 2001435 2002255 := bstep (se 1 (by rfl) ⟨1501691, by rfl⟩ : syracuseStep 2002255 = 3003383) B3003383
theorem B3003389 : Blo 2001435 3003389 := bbase (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) (by norm_num)
theorem B2002259 : Blo 2001435 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B4505093 : Blo 2001435 4505093 := bbase (se 4 (by rfl) ⟨422352, by rfl⟩ : syracuseStep 4505093 = 844705) (by norm_num)
theorem B3003395 : Blo 2001435 3003395 := bstep (se 1 (by rfl) ⟨2252546, by rfl⟩ : syracuseStep 3003395 = 4505093) B4505093
theorem B2002263 : Blo 2001435 2002263 := bstep (se 1 (by rfl) ⟨1501697, by rfl⟩ : syracuseStep 2002263 = 3003395) B3003395
theorem B3801181 : Blo 2001435 3801181 := bbase (se 3 (by rfl) ⟨712721, by rfl⟩ : syracuseStep 3801181 = 1425443) (by norm_num)
theorem B5068241 : Blo 2001435 5068241 := bstep (se 2 (by rfl) ⟨1900590, by rfl⟩ : syracuseStep 5068241 = 3801181) B3801181
theorem B3378827 : Blo 2001435 3378827 := bstep (se 1 (by rfl) ⟨2534120, by rfl⟩ : syracuseStep 3378827 = 5068241) B5068241
theorem B2252551 : Blo 2001435 2252551 := bstep (se 1 (by rfl) ⟨1689413, by rfl⟩ : syracuseStep 2252551 = 3378827) B3378827
theorem B3003401 : Blo 2001435 3003401 := bstep (se 2 (by rfl) ⟨1126275, by rfl⟩ : syracuseStep 3003401 = 2252551) B2252551
theorem B2002267 : Blo 2001435 2002267 := bstep (se 1 (by rfl) ⟨1501700, by rfl⟩ : syracuseStep 2002267 = 3003401) B3003401
theorem B10136501 : Blo 2001435 10136501 := bbase (se 5 (by rfl) ⟨475148, by rfl⟩ : syracuseStep 10136501 = 950297) (by norm_num)
theorem B6757667 : Blo 2001435 6757667 := bstep (se 1 (by rfl) ⟨5068250, by rfl⟩ : syracuseStep 6757667 = 10136501) B10136501
theorem B4505111 : Blo 2001435 4505111 := bstep (se 1 (by rfl) ⟨3378833, by rfl⟩ : syracuseStep 4505111 = 6757667) B6757667
theorem B3003407 : Blo 2001435 3003407 := bstep (se 1 (by rfl) ⟨2252555, by rfl⟩ : syracuseStep 3003407 = 4505111) B4505111
theorem B2002271 : Blo 2001435 2002271 := bstep (se 1 (by rfl) ⟨1501703, by rfl⟩ : syracuseStep 2002271 = 3003407) B3003407
theorem B3003413 : Blo 2001435 3003413 := bbase (se 6 (by rfl) ⟨70392, by rfl⟩ : syracuseStep 3003413 = 140785) (by norm_num)
theorem B2002275 : Blo 2001435 2002275 := bstep (se 1 (by rfl) ⟨1501706, by rfl⟩ : syracuseStep 2002275 = 3003413) B3003413
theorem B21649045 : Blo 2001435 21649045 := bbase (se 6 (by rfl) ⟨507399, by rfl⟩ : syracuseStep 21649045 = 1014799) (by norm_num)
theorem B28865393 : Blo 2001435 28865393 := bstep (se 2 (by rfl) ⟨10824522, by rfl⟩ : syracuseStep 28865393 = 21649045) B21649045
theorem B19243595 : Blo 2001435 19243595 := bstep (se 1 (by rfl) ⟨14432696, by rfl⟩ : syracuseStep 19243595 = 28865393) B28865393
theorem B12829063 : Blo 2001435 12829063 := bstep (se 1 (by rfl) ⟨9621797, by rfl⟩ : syracuseStep 12829063 = 19243595) B19243595
theorem B17105417 : Blo 2001435 17105417 := bstep (se 2 (by rfl) ⟨6414531, by rfl⟩ : syracuseStep 17105417 = 12829063) B12829063
theorem B11403611 : Blo 2001435 11403611 := bstep (se 1 (by rfl) ⟨8552708, by rfl⟩ : syracuseStep 11403611 = 17105417) B17105417
theorem B7602407 : Blo 2001435 7602407 := bstep (se 1 (by rfl) ⟨5701805, by rfl⟩ : syracuseStep 7602407 = 11403611) B11403611
theorem B5068271 : Blo 2001435 5068271 := bstep (se 1 (by rfl) ⟨3801203, by rfl⟩ : syracuseStep 5068271 = 7602407) B7602407
theorem B3378847 : Blo 2001435 3378847 := bstep (se 1 (by rfl) ⟨2534135, by rfl⟩ : syracuseStep 3378847 = 5068271) B5068271
theorem B4505129 : Blo 2001435 4505129 := bstep (se 2 (by rfl) ⟨1689423, by rfl⟩ : syracuseStep 4505129 = 3378847) B3378847
theorem B3003419 : Blo 2001435 3003419 := bstep (se 1 (by rfl) ⟨2252564, by rfl⟩ : syracuseStep 3003419 = 4505129) B4505129
theorem B2002279 : Blo 2001435 2002279 := bstep (se 1 (by rfl) ⟨1501709, by rfl⟩ : syracuseStep 2002279 = 3003419) B3003419
theorem B2252569 : Blo 2001435 2252569 := bbase (se 2 (by rfl) ⟨844713, by rfl⟩ : syracuseStep 2252569 = 1689427) (by norm_num)
theorem B3003425 : Blo 2001435 3003425 := bstep (se 2 (by rfl) ⟨1126284, by rfl⟩ : syracuseStep 3003425 = 2252569) B2252569
theorem B2002283 : Blo 2001435 2002283 := bstep (se 1 (by rfl) ⟨1501712, by rfl⟩ : syracuseStep 2002283 = 3003425) B3003425
theorem B7602437 : Blo 2001435 7602437 := bbase (se 4 (by rfl) ⟨712728, by rfl⟩ : syracuseStep 7602437 = 1425457) (by norm_num)
theorem B5068291 : Blo 2001435 5068291 := bstep (se 1 (by rfl) ⟨3801218, by rfl⟩ : syracuseStep 5068291 = 7602437) B7602437
theorem B6757721 : Blo 2001435 6757721 := bstep (se 2 (by rfl) ⟨2534145, by rfl⟩ : syracuseStep 6757721 = 5068291) B5068291
theorem B4505147 : Blo 2001435 4505147 := bstep (se 1 (by rfl) ⟨3378860, by rfl⟩ : syracuseStep 4505147 = 6757721) B6757721
theorem B3003431 : Blo 2001435 3003431 := bstep (se 1 (by rfl) ⟨2252573, by rfl⟩ : syracuseStep 3003431 = 4505147) B4505147
theorem B2002287 : Blo 2001435 2002287 := bstep (se 1 (by rfl) ⟨1501715, by rfl⟩ : syracuseStep 2002287 = 3003431) B3003431
theorem B3003437 : Blo 2001435 3003437 := bbase (se 3 (by rfl) ⟨563144, by rfl⟩ : syracuseStep 3003437 = 1126289) (by norm_num)
theorem B2002291 : Blo 2001435 2002291 := bstep (se 1 (by rfl) ⟨1501718, by rfl⟩ : syracuseStep 2002291 = 3003437) B3003437
theorem B4505165 : Blo 2001435 4505165 := bbase (se 3 (by rfl) ⟨844718, by rfl⟩ : syracuseStep 4505165 = 1689437) (by norm_num)
theorem B3003443 : Blo 2001435 3003443 := bstep (se 1 (by rfl) ⟨2252582, by rfl⟩ : syracuseStep 3003443 = 4505165) B4505165
theorem B2002295 : Blo 2001435 2002295 := bstep (se 1 (by rfl) ⟨1501721, by rfl⟩ : syracuseStep 2002295 = 3003443) B3003443
theorem B2534161 : Blo 2001435 2534161 := bbase (se 2 (by rfl) ⟨950310, by rfl⟩ : syracuseStep 2534161 = 1900621) (by norm_num)
theorem B3378881 : Blo 2001435 3378881 := bstep (se 2 (by rfl) ⟨1267080, by rfl⟩ : syracuseStep 3378881 = 2534161) B2534161
theorem B2252587 : Blo 2001435 2252587 := bstep (se 1 (by rfl) ⟨1689440, by rfl⟩ : syracuseStep 2252587 = 3378881) B3378881
theorem B3003449 : Blo 2001435 3003449 := bstep (se 2 (by rfl) ⟨1126293, by rfl⟩ : syracuseStep 3003449 = 2252587) B2252587
theorem B2002299 : Blo 2001435 2002299 := bstep (se 1 (by rfl) ⟨1501724, by rfl⟩ : syracuseStep 2002299 = 3003449) B3003449
theorem B4276405 : Blo 2001435 4276405 := bbase (se 5 (by rfl) ⟨200456, by rfl⟩ : syracuseStep 4276405 = 400913) (by norm_num)
theorem B22807493 : Blo 2001435 22807493 := bstep (se 4 (by rfl) ⟨2138202, by rfl⟩ : syracuseStep 22807493 = 4276405) B4276405
theorem B15204995 : Blo 2001435 15204995 := bstep (se 1 (by rfl) ⟨11403746, by rfl⟩ : syracuseStep 15204995 = 22807493) B22807493
theorem B10136663 : Blo 2001435 10136663 := bstep (se 1 (by rfl) ⟨7602497, by rfl⟩ : syracuseStep 10136663 = 15204995) B15204995
theorem B6757775 : Blo 2001435 6757775 := bstep (se 1 (by rfl) ⟨5068331, by rfl⟩ : syracuseStep 6757775 = 10136663) B10136663
theorem B4505183 : Blo 2001435 4505183 := bstep (se 1 (by rfl) ⟨3378887, by rfl⟩ : syracuseStep 4505183 = 6757775) B6757775
theorem B3003455 : Blo 2001435 3003455 := bstep (se 1 (by rfl) ⟨2252591, by rfl⟩ : syracuseStep 3003455 = 4505183) B4505183
theorem B2002303 : Blo 2001435 2002303 := bstep (se 1 (by rfl) ⟨1501727, by rfl⟩ : syracuseStep 2002303 = 3003455) B3003455
theorem B3003461 : Blo 2001435 3003461 := bbase (se 4 (by rfl) ⟨281574, by rfl⟩ : syracuseStep 3003461 = 563149) (by norm_num)
theorem B2002307 : Blo 2001435 2002307 := bstep (se 1 (by rfl) ⟨1501730, by rfl⟩ : syracuseStep 2002307 = 3003461) B3003461
theorem B3378901 : Blo 2001435 3378901 := bbase (se 7 (by rfl) ⟨39596, by rfl⟩ : syracuseStep 3378901 = 79193) (by norm_num)
theorem B4505201 : Blo 2001435 4505201 := bstep (se 2 (by rfl) ⟨1689450, by rfl⟩ : syracuseStep 4505201 = 3378901) B3378901
theorem B3003467 : Blo 2001435 3003467 := bstep (se 1 (by rfl) ⟨2252600, by rfl⟩ : syracuseStep 3003467 = 4505201) B4505201
theorem B2002311 : Blo 2001435 2002311 := bstep (se 1 (by rfl) ⟨1501733, by rfl⟩ : syracuseStep 2002311 = 3003467) B3003467
theorem B2252605 : Blo 2001435 2252605 := bbase (se 3 (by rfl) ⟨422363, by rfl⟩ : syracuseStep 2252605 = 844727) (by norm_num)
theorem B3003473 : Blo 2001435 3003473 := bstep (se 2 (by rfl) ⟨1126302, by rfl⟩ : syracuseStep 3003473 = 2252605) B2252605
theorem B2002315 : Blo 2001435 2002315 := bstep (se 1 (by rfl) ⟨1501736, by rfl⟩ : syracuseStep 2002315 = 3003473) B3003473
theorem B6757829 : Blo 2001435 6757829 := bbase (se 4 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 6757829 = 1267093) (by norm_num)
theorem B4505219 : Blo 2001435 4505219 := bstep (se 1 (by rfl) ⟨3378914, by rfl⟩ : syracuseStep 4505219 = 6757829) B6757829
theorem B3003479 : Blo 2001435 3003479 := bstep (se 1 (by rfl) ⟨2252609, by rfl⟩ : syracuseStep 3003479 = 4505219) B4505219
theorem B2002319 : Blo 2001435 2002319 := bstep (se 1 (by rfl) ⟨1501739, by rfl⟩ : syracuseStep 2002319 = 3003479) B3003479
theorem B3003485 : Blo 2001435 3003485 := bbase (se 3 (by rfl) ⟨563153, by rfl⟩ : syracuseStep 3003485 = 1126307) (by norm_num)
theorem B2002323 : Blo 2001435 2002323 := bstep (se 1 (by rfl) ⟨1501742, by rfl⟩ : syracuseStep 2002323 = 3003485) B3003485
theorem B4505237 : Blo 2001435 4505237 := bbase (se 6 (by rfl) ⟨105591, by rfl⟩ : syracuseStep 4505237 = 211183) (by norm_num)
theorem B3003491 : Blo 2001435 3003491 := bstep (se 1 (by rfl) ⟨2252618, by rfl⟩ : syracuseStep 3003491 = 4505237) B4505237
theorem B2002327 : Blo 2001435 2002327 := bstep (se 1 (by rfl) ⟨1501745, by rfl⟩ : syracuseStep 2002327 = 3003491) B3003491
theorem B2138233 : Blo 2001435 2138233 := bbase (se 2 (by rfl) ⟨801837, by rfl⟩ : syracuseStep 2138233 = 1603675) (by norm_num)
theorem B2850977 : Blo 2001435 2850977 := bstep (se 2 (by rfl) ⟨1069116, by rfl⟩ : syracuseStep 2850977 = 2138233) B2138233
theorem B7602605 : Blo 2001435 7602605 := bstep (se 3 (by rfl) ⟨1425488, by rfl⟩ : syracuseStep 7602605 = 2850977) B2850977
theorem B5068403 : Blo 2001435 5068403 := bstep (se 1 (by rfl) ⟨3801302, by rfl⟩ : syracuseStep 5068403 = 7602605) B7602605
theorem B3378935 : Blo 2001435 3378935 := bstep (se 1 (by rfl) ⟨2534201, by rfl⟩ : syracuseStep 3378935 = 5068403) B5068403
theorem B2252623 : Blo 2001435 2252623 := bstep (se 1 (by rfl) ⟨1689467, by rfl⟩ : syracuseStep 2252623 = 3378935) B3378935
theorem B3003497 : Blo 2001435 3003497 := bstep (se 2 (by rfl) ⟨1126311, by rfl⟩ : syracuseStep 3003497 = 2252623) B2252623
theorem B2002331 : Blo 2001435 2002331 := bstep (se 1 (by rfl) ⟨1501748, by rfl⟩ : syracuseStep 2002331 = 3003497) B3003497
theorem B4566725 : Blo 2001435 4566725 := bbase (se 4 (by rfl) ⟨428130, by rfl⟩ : syracuseStep 4566725 = 856261) (by norm_num)
theorem B3044483 : Blo 2001435 3044483 := bstep (se 1 (by rfl) ⟨2283362, by rfl⟩ : syracuseStep 3044483 = 4566725) B4566725
theorem B2029655 : Blo 2001435 2029655 := bstep (se 1 (by rfl) ⟨1522241, by rfl⟩ : syracuseStep 2029655 = 3044483) B3044483
theorem B5412413 : Blo 2001435 5412413 := bstep (se 3 (by rfl) ⟨1014827, by rfl⟩ : syracuseStep 5412413 = 2029655) B2029655
theorem B3608275 : Blo 2001435 3608275 := bstep (se 1 (by rfl) ⟨2706206, by rfl⟩ : syracuseStep 3608275 = 5412413) B5412413
theorem B4811033 : Blo 2001435 4811033 := bstep (se 2 (by rfl) ⟨1804137, by rfl⟩ : syracuseStep 4811033 = 3608275) B3608275
theorem B12829421 : Blo 2001435 12829421 := bstep (se 3 (by rfl) ⟨2405516, by rfl⟩ : syracuseStep 12829421 = 4811033) B4811033
theorem B8552947 : Blo 2001435 8552947 := bstep (se 1 (by rfl) ⟨6414710, by rfl⟩ : syracuseStep 8552947 = 12829421) B12829421
theorem B11403929 : Blo 2001435 11403929 := bstep (se 2 (by rfl) ⟨4276473, by rfl⟩ : syracuseStep 11403929 = 8552947) B8552947
theorem B7602619 : Blo 2001435 7602619 := bstep (se 1 (by rfl) ⟨5701964, by rfl⟩ : syracuseStep 7602619 = 11403929) B11403929
theorem B10136825 : Blo 2001435 10136825 := bstep (se 2 (by rfl) ⟨3801309, by rfl⟩ : syracuseStep 10136825 = 7602619) B7602619
theorem B6757883 : Blo 2001435 6757883 := bstep (se 1 (by rfl) ⟨5068412, by rfl⟩ : syracuseStep 6757883 = 10136825) B10136825
theorem B4505255 : Blo 2001435 4505255 := bstep (se 1 (by rfl) ⟨3378941, by rfl⟩ : syracuseStep 4505255 = 6757883) B6757883
theorem B3003503 : Blo 2001435 3003503 := bstep (se 1 (by rfl) ⟨2252627, by rfl⟩ : syracuseStep 3003503 = 4505255) B4505255
theorem B2002335 : Blo 2001435 2002335 := bstep (se 1 (by rfl) ⟨1501751, by rfl⟩ : syracuseStep 2002335 = 3003503) B3003503
theorem B3003509 : Blo 2001435 3003509 := bbase (se 5 (by rfl) ⟨140789, by rfl⟩ : syracuseStep 3003509 = 281579) (by norm_num)
theorem B2002339 : Blo 2001435 2002339 := bstep (se 1 (by rfl) ⟨1501754, by rfl⟩ : syracuseStep 2002339 = 3003509) B3003509
theorem B3801325 : Blo 2001435 3801325 := bbase (se 3 (by rfl) ⟨712748, by rfl⟩ : syracuseStep 3801325 = 1425497) (by norm_num)
theorem B5068433 : Blo 2001435 5068433 := bstep (se 2 (by rfl) ⟨1900662, by rfl⟩ : syracuseStep 5068433 = 3801325) B3801325
theorem B3378955 : Blo 2001435 3378955 := bstep (se 1 (by rfl) ⟨2534216, by rfl⟩ : syracuseStep 3378955 = 5068433) B5068433
theorem B4505273 : Blo 2001435 4505273 := bstep (se 2 (by rfl) ⟨1689477, by rfl⟩ : syracuseStep 4505273 = 3378955) B3378955
theorem B3003515 : Blo 2001435 3003515 := bstep (se 1 (by rfl) ⟨2252636, by rfl⟩ : syracuseStep 3003515 = 4505273) B4505273
theorem B2002343 : Blo 2001435 2002343 := bstep (se 1 (by rfl) ⟨1501757, by rfl⟩ : syracuseStep 2002343 = 3003515) B3003515
theorem B2252641 : Blo 2001435 2252641 := bbase (se 2 (by rfl) ⟨844740, by rfl⟩ : syracuseStep 2252641 = 1689481) (by norm_num)
theorem B3003521 : Blo 2001435 3003521 := bstep (se 2 (by rfl) ⟨1126320, by rfl⟩ : syracuseStep 3003521 = 2252641) B2252641
theorem B2002347 : Blo 2001435 2002347 := bstep (se 1 (by rfl) ⟨1501760, by rfl⟩ : syracuseStep 2002347 = 3003521) B3003521
theorem B5068453 : Blo 2001435 5068453 := bbase (se 4 (by rfl) ⟨475167, by rfl⟩ : syracuseStep 5068453 = 950335) (by norm_num)
theorem B6757937 : Blo 2001435 6757937 := bstep (se 2 (by rfl) ⟨2534226, by rfl⟩ : syracuseStep 6757937 = 5068453) B5068453
theorem B4505291 : Blo 2001435 4505291 := bstep (se 1 (by rfl) ⟨3378968, by rfl⟩ : syracuseStep 4505291 = 6757937) B6757937
theorem B3003527 : Blo 2001435 3003527 := bstep (se 1 (by rfl) ⟨2252645, by rfl⟩ : syracuseStep 3003527 = 4505291) B4505291
theorem B2002351 : Blo 2001435 2002351 := bstep (se 1 (by rfl) ⟨1501763, by rfl⟩ : syracuseStep 2002351 = 3003527) B3003527
theorem B3003533 : Blo 2001435 3003533 := bbase (se 3 (by rfl) ⟨563162, by rfl⟩ : syracuseStep 3003533 = 1126325) (by norm_num)
theorem B2002355 : Blo 2001435 2002355 := bstep (se 1 (by rfl) ⟨1501766, by rfl⟩ : syracuseStep 2002355 = 3003533) B3003533
theorem B4505309 : Blo 2001435 4505309 := bbase (se 3 (by rfl) ⟨844745, by rfl⟩ : syracuseStep 4505309 = 1689491) (by norm_num)
theorem B3003539 : Blo 2001435 3003539 := bstep (se 1 (by rfl) ⟨2252654, by rfl⟩ : syracuseStep 3003539 = 4505309) B4505309
theorem B2002359 : Blo 2001435 2002359 := bstep (se 1 (by rfl) ⟨1501769, by rfl⟩ : syracuseStep 2002359 = 3003539) B3003539
theorem B3378989 : Blo 2001435 3378989 := bbase (se 3 (by rfl) ⟨633560, by rfl⟩ : syracuseStep 3378989 = 1267121) (by norm_num)
theorem B2252659 : Blo 2001435 2252659 := bstep (se 1 (by rfl) ⟨1689494, by rfl⟩ : syracuseStep 2252659 = 3378989) B3378989
theorem B3003545 : Blo 2001435 3003545 := bstep (se 2 (by rfl) ⟨1126329, by rfl⟩ : syracuseStep 3003545 = 2252659) B2252659
theorem B2002363 : Blo 2001435 2002363 := bstep (se 1 (by rfl) ⟨1501772, by rfl⟩ : syracuseStep 2002363 = 3003545) B3003545
theorem B4566797 : Blo 2001435 4566797 := bbase (se 3 (by rfl) ⟨856274, by rfl⟩ : syracuseStep 4566797 = 1712549) (by norm_num)
theorem B3044531 : Blo 2001435 3044531 := bstep (se 1 (by rfl) ⟨2283398, by rfl⟩ : syracuseStep 3044531 = 4566797) B4566797
theorem B2029687 : Blo 2001435 2029687 := bstep (se 1 (by rfl) ⟨1522265, by rfl⟩ : syracuseStep 2029687 = 3044531) B3044531
theorem B10824997 : Blo 2001435 10824997 := bstep (se 4 (by rfl) ⟨1014843, by rfl⟩ : syracuseStep 10824997 = 2029687) B2029687
theorem B14433329 : Blo 2001435 14433329 := bstep (se 2 (by rfl) ⟨5412498, by rfl⟩ : syracuseStep 14433329 = 10824997) B10824997
theorem B38488877 : Blo 2001435 38488877 := bstep (se 3 (by rfl) ⟨7216664, by rfl⟩ : syracuseStep 38488877 = 14433329) B14433329
theorem B25659251 : Blo 2001435 25659251 := bstep (se 1 (by rfl) ⟨19244438, by rfl⟩ : syracuseStep 25659251 = 38488877) B38488877
theorem B17106167 : Blo 2001435 17106167 := bstep (se 1 (by rfl) ⟨12829625, by rfl⟩ : syracuseStep 17106167 = 25659251) B25659251
theorem B11404111 : Blo 2001435 11404111 := bstep (se 1 (by rfl) ⟨8553083, by rfl⟩ : syracuseStep 11404111 = 17106167) B17106167
theorem B15205481 : Blo 2001435 15205481 := bstep (se 2 (by rfl) ⟨5702055, by rfl⟩ : syracuseStep 15205481 = 11404111) B11404111
theorem B10136987 : Blo 2001435 10136987 := bstep (se 1 (by rfl) ⟨7602740, by rfl⟩ : syracuseStep 10136987 = 15205481) B15205481
theorem B6757991 : Blo 2001435 6757991 := bstep (se 1 (by rfl) ⟨5068493, by rfl⟩ : syracuseStep 6757991 = 10136987) B10136987
theorem B4505327 : Blo 2001435 4505327 := bstep (se 1 (by rfl) ⟨3378995, by rfl⟩ : syracuseStep 4505327 = 6757991) B6757991
theorem B3003551 : Blo 2001435 3003551 := bstep (se 1 (by rfl) ⟨2252663, by rfl⟩ : syracuseStep 3003551 = 4505327) B4505327
theorem B2002367 : Blo 2001435 2002367 := bstep (se 1 (by rfl) ⟨1501775, by rfl⟩ : syracuseStep 2002367 = 3003551) B3003551
theorem B3003557 : Blo 2001435 3003557 := bbase (se 4 (by rfl) ⟨281583, by rfl⟩ : syracuseStep 3003557 = 563167) (by norm_num)
theorem B2002371 : Blo 2001435 2002371 := bstep (se 1 (by rfl) ⟨1501778, by rfl⟩ : syracuseStep 2002371 = 3003557) B3003557
theorem B2534257 : Blo 2001435 2534257 := bbase (se 2 (by rfl) ⟨950346, by rfl⟩ : syracuseStep 2534257 = 1900693) (by norm_num)
theorem B3379009 : Blo 2001435 3379009 := bstep (se 2 (by rfl) ⟨1267128, by rfl⟩ : syracuseStep 3379009 = 2534257) B2534257
theorem B4505345 : Blo 2001435 4505345 := bstep (se 2 (by rfl) ⟨1689504, by rfl⟩ : syracuseStep 4505345 = 3379009) B3379009
theorem B3003563 : Blo 2001435 3003563 := bstep (se 1 (by rfl) ⟨2252672, by rfl⟩ : syracuseStep 3003563 = 4505345) B4505345
theorem B2002375 : Blo 2001435 2002375 := bstep (se 1 (by rfl) ⟨1501781, by rfl⟩ : syracuseStep 2002375 = 3003563) B3003563
theorem B2252677 : Blo 2001435 2252677 := bbase (se 4 (by rfl) ⟨211188, by rfl⟩ : syracuseStep 2252677 = 422377) (by norm_num)
theorem B3003569 : Blo 2001435 3003569 := bstep (se 2 (by rfl) ⟨1126338, by rfl⟩ : syracuseStep 3003569 = 2252677) B2252677
theorem B2002379 : Blo 2001435 2002379 := bstep (se 1 (by rfl) ⟨1501784, by rfl⟩ : syracuseStep 2002379 = 3003569) B3003569
theorem B3044557 : Blo 2001435 3044557 := bbase (se 3 (by rfl) ⟨570854, by rfl⟩ : syracuseStep 3044557 = 1141709) (by norm_num)
theorem B4059409 : Blo 2001435 4059409 := bstep (se 2 (by rfl) ⟨1522278, by rfl⟩ : syracuseStep 4059409 = 3044557) B3044557
theorem B5412545 : Blo 2001435 5412545 := bstep (se 2 (by rfl) ⟨2029704, by rfl⟩ : syracuseStep 5412545 = 4059409) B4059409
theorem B3608363 : Blo 2001435 3608363 := bstep (se 1 (by rfl) ⟨2706272, by rfl⟩ : syracuseStep 3608363 = 5412545) B5412545
theorem B2405575 : Blo 2001435 2405575 := bstep (se 1 (by rfl) ⟨1804181, by rfl⟩ : syracuseStep 2405575 = 3608363) B3608363
theorem B3207433 : Blo 2001435 3207433 := bstep (se 2 (by rfl) ⟨1202787, by rfl⟩ : syracuseStep 3207433 = 2405575) B2405575
theorem B4276577 : Blo 2001435 4276577 := bstep (se 2 (by rfl) ⟨1603716, by rfl⟩ : syracuseStep 4276577 = 3207433) B3207433
theorem B2851051 : Blo 2001435 2851051 := bstep (se 1 (by rfl) ⟨2138288, by rfl⟩ : syracuseStep 2851051 = 4276577) B4276577
theorem B3801401 : Blo 2001435 3801401 := bstep (se 2 (by rfl) ⟨1425525, by rfl⟩ : syracuseStep 3801401 = 2851051) B2851051
theorem B2534267 : Blo 2001435 2534267 := bstep (se 1 (by rfl) ⟨1900700, by rfl⟩ : syracuseStep 2534267 = 3801401) B3801401
theorem B6758045 : Blo 2001435 6758045 := bstep (se 3 (by rfl) ⟨1267133, by rfl⟩ : syracuseStep 6758045 = 2534267) B2534267
theorem B4505363 : Blo 2001435 4505363 := bstep (se 1 (by rfl) ⟨3379022, by rfl⟩ : syracuseStep 4505363 = 6758045) B6758045
theorem B3003575 : Blo 2001435 3003575 := bstep (se 1 (by rfl) ⟨2252681, by rfl⟩ : syracuseStep 3003575 = 4505363) B4505363
theorem B2002383 : Blo 2001435 2002383 := bstep (se 1 (by rfl) ⟨1501787, by rfl⟩ : syracuseStep 2002383 = 3003575) B3003575
theorem B3003581 : Blo 2001435 3003581 := bbase (se 3 (by rfl) ⟨563171, by rfl⟩ : syracuseStep 3003581 = 1126343) (by norm_num)
theorem B2002387 : Blo 2001435 2002387 := bstep (se 1 (by rfl) ⟨1501790, by rfl⟩ : syracuseStep 2002387 = 3003581) B3003581
theorem B4505381 : Blo 2001435 4505381 := bbase (se 4 (by rfl) ⟨422379, by rfl⟩ : syracuseStep 4505381 = 844759) (by norm_num)
theorem B3003587 : Blo 2001435 3003587 := bstep (se 1 (by rfl) ⟨2252690, by rfl⟩ : syracuseStep 3003587 = 4505381) B4505381
theorem B2002391 : Blo 2001435 2002391 := bstep (se 1 (by rfl) ⟨1501793, by rfl⟩ : syracuseStep 2002391 = 3003587) B3003587
theorem B5068565 : Blo 2001435 5068565 := bbase (se 6 (by rfl) ⟨118794, by rfl⟩ : syracuseStep 5068565 = 237589) (by norm_num)
theorem B3379043 : Blo 2001435 3379043 := bstep (se 1 (by rfl) ⟨2534282, by rfl⟩ : syracuseStep 3379043 = 5068565) B5068565
theorem B2252695 : Blo 2001435 2252695 := bstep (se 1 (by rfl) ⟨1689521, by rfl⟩ : syracuseStep 2252695 = 3379043) B3379043
theorem B3003593 : Blo 2001435 3003593 := bstep (se 2 (by rfl) ⟨1126347, by rfl⟩ : syracuseStep 3003593 = 2252695) B2252695
theorem B2002395 : Blo 2001435 2002395 := bstep (se 1 (by rfl) ⟨1501796, by rfl⟩ : syracuseStep 2002395 = 3003593) B3003593
theorem B8553221 : Blo 2001435 8553221 := bbase (se 4 (by rfl) ⟨801864, by rfl⟩ : syracuseStep 8553221 = 1603729) (by norm_num)
theorem B5702147 : Blo 2001435 5702147 := bstep (se 1 (by rfl) ⟨4276610, by rfl⟩ : syracuseStep 5702147 = 8553221) B8553221
theorem B3801431 : Blo 2001435 3801431 := bstep (se 1 (by rfl) ⟨2851073, by rfl⟩ : syracuseStep 3801431 = 5702147) B5702147
theorem B10137149 : Blo 2001435 10137149 := bstep (se 3 (by rfl) ⟨1900715, by rfl⟩ : syracuseStep 10137149 = 3801431) B3801431
theorem B6758099 : Blo 2001435 6758099 := bstep (se 1 (by rfl) ⟨5068574, by rfl⟩ : syracuseStep 6758099 = 10137149) B10137149
theorem B4505399 : Blo 2001435 4505399 := bstep (se 1 (by rfl) ⟨3379049, by rfl⟩ : syracuseStep 4505399 = 6758099) B6758099
theorem B3003599 : Blo 2001435 3003599 := bstep (se 1 (by rfl) ⟨2252699, by rfl⟩ : syracuseStep 3003599 = 4505399) B4505399
theorem B2002399 : Blo 2001435 2002399 := bstep (se 1 (by rfl) ⟨1501799, by rfl⟩ : syracuseStep 2002399 = 3003599) B3003599
theorem B3003605 : Blo 2001435 3003605 := bbase (se 7 (by rfl) ⟨35198, by rfl⟩ : syracuseStep 3003605 = 70397) (by norm_num)
theorem B2002403 : Blo 2001435 2002403 := bstep (se 1 (by rfl) ⟨1501802, by rfl⟩ : syracuseStep 2002403 = 3003605) B3003605
theorem B2851085 : Blo 2001435 2851085 := bbase (se 3 (by rfl) ⟨534578, by rfl⟩ : syracuseStep 2851085 = 1069157) (by norm_num)
theorem B7602893 : Blo 2001435 7602893 := bstep (se 3 (by rfl) ⟨1425542, by rfl⟩ : syracuseStep 7602893 = 2851085) B2851085
theorem B5068595 : Blo 2001435 5068595 := bstep (se 1 (by rfl) ⟨3801446, by rfl⟩ : syracuseStep 5068595 = 7602893) B7602893
theorem B3379063 : Blo 2001435 3379063 := bstep (se 1 (by rfl) ⟨2534297, by rfl⟩ : syracuseStep 3379063 = 5068595) B5068595
theorem B4505417 : Blo 2001435 4505417 := bstep (se 2 (by rfl) ⟨1689531, by rfl⟩ : syracuseStep 4505417 = 3379063) B3379063
theorem B3003611 : Blo 2001435 3003611 := bstep (se 1 (by rfl) ⟨2252708, by rfl⟩ : syracuseStep 3003611 = 4505417) B4505417
theorem B2002407 : Blo 2001435 2002407 := bstep (se 1 (by rfl) ⟨1501805, by rfl⟩ : syracuseStep 2002407 = 3003611) B3003611
theorem B2252713 : Blo 2001435 2252713 := bbase (se 2 (by rfl) ⟨844767, by rfl⟩ : syracuseStep 2252713 = 1689535) (by norm_num)
theorem B3003617 : Blo 2001435 3003617 := bstep (se 2 (by rfl) ⟨1126356, by rfl⟩ : syracuseStep 3003617 = 2252713) B2252713
theorem B2002411 : Blo 2001435 2002411 := bstep (se 1 (by rfl) ⟨1501808, by rfl⟩ : syracuseStep 2002411 = 3003617) B3003617
theorem B5412629 : Blo 2001435 5412629 := bbase (se 6 (by rfl) ⟨126858, by rfl⟩ : syracuseStep 5412629 = 253717) (by norm_num)
theorem B14433677 : Blo 2001435 14433677 := bstep (se 3 (by rfl) ⟨2706314, by rfl⟩ : syracuseStep 14433677 = 5412629) B5412629
theorem B9622451 : Blo 2001435 9622451 := bstep (se 1 (by rfl) ⟨7216838, by rfl⟩ : syracuseStep 9622451 = 14433677) B14433677
theorem B6414967 : Blo 2001435 6414967 := bstep (se 1 (by rfl) ⟨4811225, by rfl⟩ : syracuseStep 6414967 = 9622451) B9622451
theorem B8553289 : Blo 2001435 8553289 := bstep (se 2 (by rfl) ⟨3207483, by rfl⟩ : syracuseStep 8553289 = 6414967) B6414967
theorem B11404385 : Blo 2001435 11404385 := bstep (se 2 (by rfl) ⟨4276644, by rfl⟩ : syracuseStep 11404385 = 8553289) B8553289
theorem B7602923 : Blo 2001435 7602923 := bstep (se 1 (by rfl) ⟨5702192, by rfl⟩ : syracuseStep 7602923 = 11404385) B11404385
theorem B5068615 : Blo 2001435 5068615 := bstep (se 1 (by rfl) ⟨3801461, by rfl⟩ : syracuseStep 5068615 = 7602923) B7602923
theorem B6758153 : Blo 2001435 6758153 := bstep (se 2 (by rfl) ⟨2534307, by rfl⟩ : syracuseStep 6758153 = 5068615) B5068615
theorem B4505435 : Blo 2001435 4505435 := bstep (se 1 (by rfl) ⟨3379076, by rfl⟩ : syracuseStep 4505435 = 6758153) B6758153
theorem B3003623 : Blo 2001435 3003623 := bstep (se 1 (by rfl) ⟨2252717, by rfl⟩ : syracuseStep 3003623 = 4505435) B4505435
theorem B2002415 : Blo 2001435 2002415 := bstep (se 1 (by rfl) ⟨1501811, by rfl⟩ : syracuseStep 2002415 = 3003623) B3003623
theorem B3003629 : Blo 2001435 3003629 := bbase (se 3 (by rfl) ⟨563180, by rfl⟩ : syracuseStep 3003629 = 1126361) (by norm_num)
theorem B2002419 : Blo 2001435 2002419 := bstep (se 1 (by rfl) ⟨1501814, by rfl⟩ : syracuseStep 2002419 = 3003629) B3003629
theorem B4505453 : Blo 2001435 4505453 := bbase (se 3 (by rfl) ⟨844772, by rfl⟩ : syracuseStep 4505453 = 1689545) (by norm_num)
theorem B3003635 : Blo 2001435 3003635 := bstep (se 1 (by rfl) ⟨2252726, by rfl⟩ : syracuseStep 3003635 = 4505453) B4505453
theorem B2002423 : Blo 2001435 2002423 := bstep (se 1 (by rfl) ⟨1501817, by rfl⟩ : syracuseStep 2002423 = 3003635) B3003635
theorem B3801485 : Blo 2001435 3801485 := bbase (se 3 (by rfl) ⟨712778, by rfl⟩ : syracuseStep 3801485 = 1425557) (by norm_num)
theorem B2534323 : Blo 2001435 2534323 := bstep (se 1 (by rfl) ⟨1900742, by rfl⟩ : syracuseStep 2534323 = 3801485) B3801485
theorem B3379097 : Blo 2001435 3379097 := bstep (se 2 (by rfl) ⟨1267161, by rfl⟩ : syracuseStep 3379097 = 2534323) B2534323
theorem B2252731 : Blo 2001435 2252731 := bstep (se 1 (by rfl) ⟨1689548, by rfl⟩ : syracuseStep 2252731 = 3379097) B3379097
theorem B3003641 : Blo 2001435 3003641 := bstep (se 2 (by rfl) ⟨1126365, by rfl⟩ : syracuseStep 3003641 = 2252731) B2252731
theorem B2002427 : Blo 2001435 2002427 := bstep (se 1 (by rfl) ⟨1501820, by rfl⟩ : syracuseStep 2002427 = 3003641) B3003641
theorem B39547541 : Blo 2001435 39547541 := bbase (se 6 (by rfl) ⟨926895, by rfl⟩ : syracuseStep 39547541 = 1853791) (by norm_num)
theorem B26365027 : Blo 2001435 26365027 := bstep (se 1 (by rfl) ⟨19773770, by rfl⟩ : syracuseStep 26365027 = 39547541) B39547541
theorem B35153369 : Blo 2001435 35153369 := bstep (se 2 (by rfl) ⟨13182513, by rfl⟩ : syracuseStep 35153369 = 26365027) B26365027
theorem B23435579 : Blo 2001435 23435579 := bstep (se 1 (by rfl) ⟨17576684, by rfl⟩ : syracuseStep 23435579 = 35153369) B35153369
theorem B62494877 : Blo 2001435 62494877 := bstep (se 3 (by rfl) ⟨11717789, by rfl⟩ : syracuseStep 62494877 = 23435579) B23435579
theorem B41663251 : Blo 2001435 41663251 := bstep (se 1 (by rfl) ⟨31247438, by rfl⟩ : syracuseStep 41663251 = 62494877) B62494877
theorem B55551001 : Blo 2001435 55551001 := bstep (se 2 (by rfl) ⟨20831625, by rfl⟩ : syracuseStep 55551001 = 41663251) B41663251
theorem B74068001 : Blo 2001435 74068001 := bstep (se 2 (by rfl) ⟨27775500, by rfl⟩ : syracuseStep 74068001 = 55551001) B55551001
theorem B49378667 : Blo 2001435 49378667 := bstep (se 1 (by rfl) ⟨37034000, by rfl⟩ : syracuseStep 49378667 = 74068001) B74068001
theorem B131676445 : Blo 2001435 131676445 := bstep (se 3 (by rfl) ⟨24689333, by rfl⟩ : syracuseStep 131676445 = 49378667) B49378667
theorem B702274373 : Blo 2001435 702274373 := bstep (se 4 (by rfl) ⟨65838222, by rfl⟩ : syracuseStep 702274373 = 131676445) B131676445
theorem B468182915 : Blo 2001435 468182915 := bstep (se 1 (by rfl) ⟨351137186, by rfl⟩ : syracuseStep 468182915 = 702274373) B702274373
theorem B312121943 : Blo 2001435 312121943 := bstep (se 1 (by rfl) ⟨234091457, by rfl⟩ : syracuseStep 312121943 = 468182915) B468182915
theorem B208081295 : Blo 2001435 208081295 := bstep (se 1 (by rfl) ⟨156060971, by rfl⟩ : syracuseStep 208081295 = 312121943) B312121943
theorem B138720863 : Blo 2001435 138720863 := bstep (se 1 (by rfl) ⟨104040647, by rfl⟩ : syracuseStep 138720863 = 208081295) B208081295
theorem B92480575 : Blo 2001435 92480575 := bstep (se 1 (by rfl) ⟨69360431, by rfl⟩ : syracuseStep 92480575 = 138720863) B138720863
theorem B123307433 : Blo 2001435 123307433 := bstep (se 2 (by rfl) ⟨46240287, by rfl⟩ : syracuseStep 123307433 = 92480575) B92480575
theorem B82204955 : Blo 2001435 82204955 := bstep (se 1 (by rfl) ⟨61653716, by rfl⟩ : syracuseStep 82204955 = 123307433) B123307433
theorem B54803303 : Blo 2001435 54803303 := bstep (se 1 (by rfl) ⟨41102477, by rfl⟩ : syracuseStep 54803303 = 82204955) B82204955
theorem B36535535 : Blo 2001435 36535535 := bstep (se 1 (by rfl) ⟨27401651, by rfl⟩ : syracuseStep 36535535 = 54803303) B54803303
theorem B24357023 : Blo 2001435 24357023 := bstep (se 1 (by rfl) ⟨18267767, by rfl⟩ : syracuseStep 24357023 = 36535535) B36535535
theorem B16238015 : Blo 2001435 16238015 := bstep (se 1 (by rfl) ⟨12178511, by rfl⟩ : syracuseStep 16238015 = 24357023) B24357023
theorem B10825343 : Blo 2001435 10825343 := bstep (se 1 (by rfl) ⟨8119007, by rfl⟩ : syracuseStep 10825343 = 16238015) B16238015
theorem B7216895 : Blo 2001435 7216895 := bstep (se 1 (by rfl) ⟨5412671, by rfl⟩ : syracuseStep 7216895 = 10825343) B10825343
theorem B19245053 : Blo 2001435 19245053 := bstep (se 3 (by rfl) ⟨3608447, by rfl⟩ : syracuseStep 19245053 = 7216895) B7216895
theorem B51320141 : Blo 2001435 51320141 := bstep (se 3 (by rfl) ⟨9622526, by rfl⟩ : syracuseStep 51320141 = 19245053) B19245053
theorem B34213427 : Blo 2001435 34213427 := bstep (se 1 (by rfl) ⟨25660070, by rfl⟩ : syracuseStep 34213427 = 51320141) B51320141
theorem B22808951 : Blo 2001435 22808951 := bstep (se 1 (by rfl) ⟨17106713, by rfl⟩ : syracuseStep 22808951 = 34213427) B34213427
theorem B15205967 : Blo 2001435 15205967 := bstep (se 1 (by rfl) ⟨11404475, by rfl⟩ : syracuseStep 15205967 = 22808951) B22808951
theorem B10137311 : Blo 2001435 10137311 := bstep (se 1 (by rfl) ⟨7602983, by rfl⟩ : syracuseStep 10137311 = 15205967) B15205967
theorem B6758207 : Blo 2001435 6758207 := bstep (se 1 (by rfl) ⟨5068655, by rfl⟩ : syracuseStep 6758207 = 10137311) B10137311
theorem B4505471 : Blo 2001435 4505471 := bstep (se 1 (by rfl) ⟨3379103, by rfl⟩ : syracuseStep 4505471 = 6758207) B6758207
theorem B3003647 : Blo 2001435 3003647 := bstep (se 1 (by rfl) ⟨2252735, by rfl⟩ : syracuseStep 3003647 = 4505471) B4505471
theorem B2002431 : Blo 2001435 2002431 := bstep (se 1 (by rfl) ⟨1501823, by rfl⟩ : syracuseStep 2002431 = 3003647) B3003647
theorem B3003653 : Blo 2001435 3003653 := bbase (se 4 (by rfl) ⟨281592, by rfl⟩ : syracuseStep 3003653 = 563185) (by norm_num)
theorem B2002435 : Blo 2001435 2002435 := bstep (se 1 (by rfl) ⟨1501826, by rfl⟩ : syracuseStep 2002435 = 3003653) B3003653
theorem B3379117 : Blo 2001435 3379117 := bbase (se 3 (by rfl) ⟨633584, by rfl⟩ : syracuseStep 3379117 = 1267169) (by norm_num)
theorem B4505489 : Blo 2001435 4505489 := bstep (se 2 (by rfl) ⟨1689558, by rfl⟩ : syracuseStep 4505489 = 3379117) B3379117
theorem B3003659 : Blo 2001435 3003659 := bstep (se 1 (by rfl) ⟨2252744, by rfl⟩ : syracuseStep 3003659 = 4505489) B4505489
theorem B2002439 : Blo 2001435 2002439 := bstep (se 1 (by rfl) ⟨1501829, by rfl⟩ : syracuseStep 2002439 = 3003659) B3003659
theorem B2252749 : Blo 2001435 2252749 := bbase (se 3 (by rfl) ⟨422390, by rfl⟩ : syracuseStep 2252749 = 844781) (by norm_num)
theorem B3003665 : Blo 2001435 3003665 := bstep (se 2 (by rfl) ⟨1126374, by rfl⟩ : syracuseStep 3003665 = 2252749) B2252749
theorem B2002443 : Blo 2001435 2002443 := bstep (se 1 (by rfl) ⟨1501832, by rfl⟩ : syracuseStep 2002443 = 3003665) B3003665
theorem B6758261 : Blo 2001435 6758261 := bbase (se 5 (by rfl) ⟨316793, by rfl⟩ : syracuseStep 6758261 = 633587) (by norm_num)
theorem B4505507 : Blo 2001435 4505507 := bstep (se 1 (by rfl) ⟨3379130, by rfl⟩ : syracuseStep 4505507 = 6758261) B6758261
theorem B3003671 : Blo 2001435 3003671 := bstep (se 1 (by rfl) ⟨2252753, by rfl⟩ : syracuseStep 3003671 = 4505507) B4505507
theorem B2002447 : Blo 2001435 2002447 := bstep (se 1 (by rfl) ⟨1501835, by rfl⟩ : syracuseStep 2002447 = 3003671) B3003671
theorem B3003677 : Blo 2001435 3003677 := bbase (se 3 (by rfl) ⟨563189, by rfl⟩ : syracuseStep 3003677 = 1126379) (by norm_num)
theorem B2002451 : Blo 2001435 2002451 := bstep (se 1 (by rfl) ⟨1501838, by rfl⟩ : syracuseStep 2002451 = 3003677) B3003677
theorem B4505525 : Blo 2001435 4505525 := bbase (se 5 (by rfl) ⟨211196, by rfl⟩ : syracuseStep 4505525 = 422393) (by norm_num)
theorem B3003683 : Blo 2001435 3003683 := bstep (se 1 (by rfl) ⟨2252762, by rfl⟩ : syracuseStep 3003683 = 4505525) B4505525
theorem B2002455 : Blo 2001435 2002455 := bstep (se 1 (by rfl) ⟨1501841, by rfl⟩ : syracuseStep 2002455 = 3003683) B3003683
theorem B6415109 : Blo 2001435 6415109 := bbase (se 4 (by rfl) ⟨601416, by rfl⟩ : syracuseStep 6415109 = 1202833) (by norm_num)
theorem B4276739 : Blo 2001435 4276739 := bstep (se 1 (by rfl) ⟨3207554, by rfl⟩ : syracuseStep 4276739 = 6415109) B6415109
theorem B11404637 : Blo 2001435 11404637 := bstep (se 3 (by rfl) ⟨2138369, by rfl⟩ : syracuseStep 11404637 = 4276739) B4276739
theorem B7603091 : Blo 2001435 7603091 := bstep (se 1 (by rfl) ⟨5702318, by rfl⟩ : syracuseStep 7603091 = 11404637) B11404637
theorem B5068727 : Blo 2001435 5068727 := bstep (se 1 (by rfl) ⟨3801545, by rfl⟩ : syracuseStep 5068727 = 7603091) B7603091
theorem B3379151 : Blo 2001435 3379151 := bstep (se 1 (by rfl) ⟨2534363, by rfl⟩ : syracuseStep 3379151 = 5068727) B5068727
theorem B2252767 : Blo 2001435 2252767 := bstep (se 1 (by rfl) ⟨1689575, by rfl⟩ : syracuseStep 2252767 = 3379151) B3379151
theorem B3003689 : Blo 2001435 3003689 := bstep (se 2 (by rfl) ⟨1126383, by rfl⟩ : syracuseStep 3003689 = 2252767) B2252767
theorem B2002459 : Blo 2001435 2002459 := bstep (se 1 (by rfl) ⟨1501844, by rfl⟩ : syracuseStep 2002459 = 3003689) B3003689
theorem B4811341 : Blo 2001435 4811341 := bbase (se 3 (by rfl) ⟨902126, by rfl⟩ : syracuseStep 4811341 = 1804253) (by norm_num)
theorem B6415121 : Blo 2001435 6415121 := bstep (se 2 (by rfl) ⟨2405670, by rfl⟩ : syracuseStep 6415121 = 4811341) B4811341
theorem B4276747 : Blo 2001435 4276747 := bstep (se 1 (by rfl) ⟨3207560, by rfl⟩ : syracuseStep 4276747 = 6415121) B6415121
theorem B5702329 : Blo 2001435 5702329 := bstep (se 2 (by rfl) ⟨2138373, by rfl⟩ : syracuseStep 5702329 = 4276747) B4276747
theorem B7603105 : Blo 2001435 7603105 := bstep (se 2 (by rfl) ⟨2851164, by rfl⟩ : syracuseStep 7603105 = 5702329) B5702329
theorem B10137473 : Blo 2001435 10137473 := bstep (se 2 (by rfl) ⟨3801552, by rfl⟩ : syracuseStep 10137473 = 7603105) B7603105
theorem B6758315 : Blo 2001435 6758315 := bstep (se 1 (by rfl) ⟨5068736, by rfl⟩ : syracuseStep 6758315 = 10137473) B10137473
theorem B4505543 : Blo 2001435 4505543 := bstep (se 1 (by rfl) ⟨3379157, by rfl⟩ : syracuseStep 4505543 = 6758315) B6758315
theorem B3003695 : Blo 2001435 3003695 := bstep (se 1 (by rfl) ⟨2252771, by rfl⟩ : syracuseStep 3003695 = 4505543) B4505543
theorem B2002463 : Blo 2001435 2002463 := bstep (se 1 (by rfl) ⟨1501847, by rfl⟩ : syracuseStep 2002463 = 3003695) B3003695
theorem B3003701 : Blo 2001435 3003701 := bbase (se 5 (by rfl) ⟨140798, by rfl⟩ : syracuseStep 3003701 = 281597) (by norm_num)
theorem B2002467 : Blo 2001435 2002467 := bstep (se 1 (by rfl) ⟨1501850, by rfl⟩ : syracuseStep 2002467 = 3003701) B3003701
theorem B5068757 : Blo 2001435 5068757 := bbase (se 7 (by rfl) ⟨59399, by rfl⟩ : syracuseStep 5068757 = 118799) (by norm_num)
theorem B3379171 : Blo 2001435 3379171 := bstep (se 1 (by rfl) ⟨2534378, by rfl⟩ : syracuseStep 3379171 = 5068757) B5068757
theorem B4505561 : Blo 2001435 4505561 := bstep (se 2 (by rfl) ⟨1689585, by rfl⟩ : syracuseStep 4505561 = 3379171) B3379171
theorem B3003707 : Blo 2001435 3003707 := bstep (se 1 (by rfl) ⟨2252780, by rfl⟩ : syracuseStep 3003707 = 4505561) B4505561
theorem B2002471 : Blo 2001435 2002471 := bstep (se 1 (by rfl) ⟨1501853, by rfl⟩ : syracuseStep 2002471 = 3003707) B3003707
theorem B2252785 : Blo 2001435 2252785 := bbase (se 2 (by rfl) ⟨844794, by rfl⟩ : syracuseStep 2252785 = 1689589) (by norm_num)
theorem B3003713 : Blo 2001435 3003713 := bstep (se 2 (by rfl) ⟨1126392, by rfl⟩ : syracuseStep 3003713 = 2252785) B2252785
theorem B2002475 : Blo 2001435 2002475 := bstep (se 1 (by rfl) ⟨1501856, by rfl⟩ : syracuseStep 2002475 = 3003713) B3003713
theorem B3295709 : Blo 2001435 3295709 := bbase (se 3 (by rfl) ⟨617945, by rfl⟩ : syracuseStep 3295709 = 1235891) (by norm_num)
theorem B2197139 : Blo 2001435 2197139 := bstep (se 1 (by rfl) ⟨1647854, by rfl⟩ : syracuseStep 2197139 = 3295709) B3295709
theorem B5859037 : Blo 2001435 5859037 := bstep (se 3 (by rfl) ⟨1098569, by rfl⟩ : syracuseStep 5859037 = 2197139) B2197139
theorem B7812049 : Blo 2001435 7812049 := bstep (se 2 (by rfl) ⟨2929518, by rfl⟩ : syracuseStep 7812049 = 5859037) B5859037
theorem B10416065 : Blo 2001435 10416065 := bstep (se 2 (by rfl) ⟨3906024, by rfl⟩ : syracuseStep 10416065 = 7812049) B7812049
theorem B111104693 : Blo 2001435 111104693 := bstep (se 5 (by rfl) ⟨5208032, by rfl⟩ : syracuseStep 111104693 = 10416065) B10416065
theorem B74069795 : Blo 2001435 74069795 := bstep (se 1 (by rfl) ⟨55552346, by rfl⟩ : syracuseStep 74069795 = 111104693) B111104693
theorem B49379863 : Blo 2001435 49379863 := bstep (se 1 (by rfl) ⟨37034897, by rfl⟩ : syracuseStep 49379863 = 74069795) B74069795
theorem B65839817 : Blo 2001435 65839817 := bstep (se 2 (by rfl) ⟨24689931, by rfl⟩ : syracuseStep 65839817 = 49379863) B49379863
theorem B43893211 : Blo 2001435 43893211 := bstep (se 1 (by rfl) ⟨32919908, by rfl⟩ : syracuseStep 43893211 = 65839817) B65839817
theorem B58524281 : Blo 2001435 58524281 := bstep (se 2 (by rfl) ⟨21946605, by rfl⟩ : syracuseStep 58524281 = 43893211) B43893211
theorem B39016187 : Blo 2001435 39016187 := bstep (se 1 (by rfl) ⟨29262140, by rfl⟩ : syracuseStep 39016187 = 58524281) B58524281
theorem B26010791 : Blo 2001435 26010791 := bstep (se 1 (by rfl) ⟨19508093, by rfl⟩ : syracuseStep 26010791 = 39016187) B39016187
theorem B17340527 : Blo 2001435 17340527 := bstep (se 1 (by rfl) ⟨13005395, by rfl⟩ : syracuseStep 17340527 = 26010791) B26010791
theorem B46241405 : Blo 2001435 46241405 := bstep (se 3 (by rfl) ⟨8670263, by rfl⟩ : syracuseStep 46241405 = 17340527) B17340527
theorem B30827603 : Blo 2001435 30827603 := bstep (se 1 (by rfl) ⟨23120702, by rfl⟩ : syracuseStep 30827603 = 46241405) B46241405
theorem B20551735 : Blo 2001435 20551735 := bstep (se 1 (by rfl) ⟨15413801, by rfl⟩ : syracuseStep 20551735 = 30827603) B30827603
theorem B27402313 : Blo 2001435 27402313 := bstep (se 2 (by rfl) ⟨10275867, by rfl⟩ : syracuseStep 27402313 = 20551735) B20551735
theorem B36536417 : Blo 2001435 36536417 := bstep (se 2 (by rfl) ⟨13701156, by rfl⟩ : syracuseStep 36536417 = 27402313) B27402313
theorem B24357611 : Blo 2001435 24357611 := bstep (se 1 (by rfl) ⟨18268208, by rfl⟩ : syracuseStep 24357611 = 36536417) B36536417
theorem B16238407 : Blo 2001435 16238407 := bstep (se 1 (by rfl) ⟨12178805, by rfl⟩ : syracuseStep 16238407 = 24357611) B24357611
theorem B21651209 : Blo 2001435 21651209 := bstep (se 2 (by rfl) ⟨8119203, by rfl⟩ : syracuseStep 21651209 = 16238407) B16238407
theorem B14434139 : Blo 2001435 14434139 := bstep (se 1 (by rfl) ⟨10825604, by rfl⟩ : syracuseStep 14434139 = 21651209) B21651209
theorem B9622759 : Blo 2001435 9622759 := bstep (se 1 (by rfl) ⟨7217069, by rfl⟩ : syracuseStep 9622759 = 14434139) B14434139
theorem B12830345 : Blo 2001435 12830345 := bstep (se 2 (by rfl) ⟨4811379, by rfl⟩ : syracuseStep 12830345 = 9622759) B9622759
theorem B8553563 : Blo 2001435 8553563 := bstep (se 1 (by rfl) ⟨6415172, by rfl⟩ : syracuseStep 8553563 = 12830345) B12830345
theorem B5702375 : Blo 2001435 5702375 := bstep (se 1 (by rfl) ⟨4276781, by rfl⟩ : syracuseStep 5702375 = 8553563) B8553563
theorem B3801583 : Blo 2001435 3801583 := bstep (se 1 (by rfl) ⟨2851187, by rfl⟩ : syracuseStep 3801583 = 5702375) B5702375
theorem B5068777 : Blo 2001435 5068777 := bstep (se 2 (by rfl) ⟨1900791, by rfl⟩ : syracuseStep 5068777 = 3801583) B3801583
theorem B6758369 : Blo 2001435 6758369 := bstep (se 2 (by rfl) ⟨2534388, by rfl⟩ : syracuseStep 6758369 = 5068777) B5068777
theorem B4505579 : Blo 2001435 4505579 := bstep (se 1 (by rfl) ⟨3379184, by rfl⟩ : syracuseStep 4505579 = 6758369) B6758369
theorem B3003719 : Blo 2001435 3003719 := bstep (se 1 (by rfl) ⟨2252789, by rfl⟩ : syracuseStep 3003719 = 4505579) B4505579
theorem B2002479 : Blo 2001435 2002479 := bstep (se 1 (by rfl) ⟨1501859, by rfl⟩ : syracuseStep 2002479 = 3003719) B3003719
theorem B3003725 : Blo 2001435 3003725 := bbase (se 3 (by rfl) ⟨563198, by rfl⟩ : syracuseStep 3003725 = 1126397) (by norm_num)
theorem B2002483 : Blo 2001435 2002483 := bstep (se 1 (by rfl) ⟨1501862, by rfl⟩ : syracuseStep 2002483 = 3003725) B3003725
theorem B4505597 : Blo 2001435 4505597 := bbase (se 3 (by rfl) ⟨844799, by rfl⟩ : syracuseStep 4505597 = 1689599) (by norm_num)
theorem B3003731 : Blo 2001435 3003731 := bstep (se 1 (by rfl) ⟨2252798, by rfl⟩ : syracuseStep 3003731 = 4505597) B4505597
theorem B2002487 : Blo 2001435 2002487 := bstep (se 1 (by rfl) ⟨1501865, by rfl⟩ : syracuseStep 2002487 = 3003731) B3003731
theorem B3379205 : Blo 2001435 3379205 := bbase (se 4 (by rfl) ⟨316800, by rfl⟩ : syracuseStep 3379205 = 633601) (by norm_num)
theorem B2252803 : Blo 2001435 2252803 := bstep (se 1 (by rfl) ⟨1689602, by rfl⟩ : syracuseStep 2252803 = 3379205) B3379205
theorem B3003737 : Blo 2001435 3003737 := bstep (se 2 (by rfl) ⟨1126401, by rfl⟩ : syracuseStep 3003737 = 2252803) B2252803
theorem B2002491 : Blo 2001435 2002491 := bstep (se 1 (by rfl) ⟨1501868, by rfl⟩ : syracuseStep 2002491 = 3003737) B3003737
theorem B15206453 : Blo 2001435 15206453 := bbase (se 5 (by rfl) ⟨712802, by rfl⟩ : syracuseStep 15206453 = 1425605) (by norm_num)
theorem B10137635 : Blo 2001435 10137635 := bstep (se 1 (by rfl) ⟨7603226, by rfl⟩ : syracuseStep 10137635 = 15206453) B15206453
theorem B6758423 : Blo 2001435 6758423 := bstep (se 1 (by rfl) ⟨5068817, by rfl⟩ : syracuseStep 6758423 = 10137635) B10137635
theorem B4505615 : Blo 2001435 4505615 := bstep (se 1 (by rfl) ⟨3379211, by rfl⟩ : syracuseStep 4505615 = 6758423) B6758423
theorem B3003743 : Blo 2001435 3003743 := bstep (se 1 (by rfl) ⟨2252807, by rfl⟩ : syracuseStep 3003743 = 4505615) B4505615
theorem B2002495 : Blo 2001435 2002495 := bstep (se 1 (by rfl) ⟨1501871, by rfl⟩ : syracuseStep 2002495 = 3003743) B3003743
theorem B3003749 : Blo 2001435 3003749 := bbase (se 4 (by rfl) ⟨281601, by rfl⟩ : syracuseStep 3003749 = 563203) (by norm_num)
theorem B2002499 : Blo 2001435 2002499 := bstep (se 1 (by rfl) ⟨1501874, by rfl⟩ : syracuseStep 2002499 = 3003749) B3003749
theorem B3801629 : Blo 2001435 3801629 := bbase (se 3 (by rfl) ⟨712805, by rfl⟩ : syracuseStep 3801629 = 1425611) (by norm_num)
theorem B2534419 : Blo 2001435 2534419 := bstep (se 1 (by rfl) ⟨1900814, by rfl⟩ : syracuseStep 2534419 = 3801629) B3801629
theorem B3379225 : Blo 2001435 3379225 := bstep (se 2 (by rfl) ⟨1267209, by rfl⟩ : syracuseStep 3379225 = 2534419) B2534419
theorem B4505633 : Blo 2001435 4505633 := bstep (se 2 (by rfl) ⟨1689612, by rfl⟩ : syracuseStep 4505633 = 3379225) B3379225
theorem B3003755 : Blo 2001435 3003755 := bstep (se 1 (by rfl) ⟨2252816, by rfl⟩ : syracuseStep 3003755 = 4505633) B4505633
theorem B2002503 : Blo 2001435 2002503 := bstep (se 1 (by rfl) ⟨1501877, by rfl⟩ : syracuseStep 2002503 = 3003755) B3003755
theorem B2252821 : Blo 2001435 2252821 := bbase (se 6 (by rfl) ⟨52800, by rfl⟩ : syracuseStep 2252821 = 105601) (by norm_num)
theorem B3003761 : Blo 2001435 3003761 := bstep (se 2 (by rfl) ⟨1126410, by rfl⟩ : syracuseStep 3003761 = 2252821) B2252821
theorem B2002507 : Blo 2001435 2002507 := bstep (se 1 (by rfl) ⟨1501880, by rfl⟩ : syracuseStep 2002507 = 3003761) B3003761
theorem B2534429 : Blo 2001435 2534429 := bbase (se 3 (by rfl) ⟨475205, by rfl⟩ : syracuseStep 2534429 = 950411) (by norm_num)
theorem B6758477 : Blo 2001435 6758477 := bstep (se 3 (by rfl) ⟨1267214, by rfl⟩ : syracuseStep 6758477 = 2534429) B2534429
theorem B4505651 : Blo 2001435 4505651 := bstep (se 1 (by rfl) ⟨3379238, by rfl⟩ : syracuseStep 4505651 = 6758477) B6758477
theorem B3003767 : Blo 2001435 3003767 := bstep (se 1 (by rfl) ⟨2252825, by rfl⟩ : syracuseStep 3003767 = 4505651) B4505651
theorem B2002511 : Blo 2001435 2002511 := bstep (se 1 (by rfl) ⟨1501883, by rfl⟩ : syracuseStep 2002511 = 3003767) B3003767
theorem B3003773 : Blo 2001435 3003773 := bbase (se 3 (by rfl) ⟨563207, by rfl⟩ : syracuseStep 3003773 = 1126415) (by norm_num)
theorem B2002515 : Blo 2001435 2002515 := bstep (se 1 (by rfl) ⟨1501886, by rfl⟩ : syracuseStep 2002515 = 3003773) B3003773
theorem B4505669 : Blo 2001435 4505669 := bbase (se 4 (by rfl) ⟨422406, by rfl⟩ : syracuseStep 4505669 = 844813) (by norm_num)
theorem B3003779 : Blo 2001435 3003779 := bstep (se 1 (by rfl) ⟨2252834, by rfl⟩ : syracuseStep 3003779 = 4505669) B4505669
theorem B2002519 : Blo 2001435 2002519 := bstep (se 1 (by rfl) ⟨1501889, by rfl⟩ : syracuseStep 2002519 = 3003779) B3003779
theorem B5702501 : Blo 2001435 5702501 := bbase (se 4 (by rfl) ⟨534609, by rfl⟩ : syracuseStep 5702501 = 1069219) (by norm_num)
theorem B3801667 : Blo 2001435 3801667 := bstep (se 1 (by rfl) ⟨2851250, by rfl⟩ : syracuseStep 3801667 = 5702501) B5702501
theorem B5068889 : Blo 2001435 5068889 := bstep (se 2 (by rfl) ⟨1900833, by rfl⟩ : syracuseStep 5068889 = 3801667) B3801667
theorem B3379259 : Blo 2001435 3379259 := bstep (se 1 (by rfl) ⟨2534444, by rfl⟩ : syracuseStep 3379259 = 5068889) B5068889
theorem B2252839 : Blo 2001435 2252839 := bstep (se 1 (by rfl) ⟨1689629, by rfl⟩ : syracuseStep 2252839 = 3379259) B3379259
theorem B3003785 : Blo 2001435 3003785 := bstep (se 2 (by rfl) ⟨1126419, by rfl⟩ : syracuseStep 3003785 = 2252839) B2252839
theorem B2002523 : Blo 2001435 2002523 := bstep (se 1 (by rfl) ⟨1501892, by rfl⟩ : syracuseStep 2002523 = 3003785) B3003785
theorem B10137797 : Blo 2001435 10137797 := bbase (se 4 (by rfl) ⟨950418, by rfl⟩ : syracuseStep 10137797 = 1900837) (by norm_num)
theorem B6758531 : Blo 2001435 6758531 := bstep (se 1 (by rfl) ⟨5068898, by rfl⟩ : syracuseStep 6758531 = 10137797) B10137797
theorem B4505687 : Blo 2001435 4505687 := bstep (se 1 (by rfl) ⟨3379265, by rfl⟩ : syracuseStep 4505687 = 6758531) B6758531
theorem B3003791 : Blo 2001435 3003791 := bstep (se 1 (by rfl) ⟨2252843, by rfl⟩ : syracuseStep 3003791 = 4505687) B4505687
theorem B2002527 : Blo 2001435 2002527 := bstep (se 1 (by rfl) ⟨1501895, by rfl⟩ : syracuseStep 2002527 = 3003791) B3003791
theorem B3003797 : Blo 2001435 3003797 := bbase (se 6 (by rfl) ⟨70401, by rfl⟩ : syracuseStep 3003797 = 140803) (by norm_num)
theorem B2002531 : Blo 2001435 2002531 := bstep (se 1 (by rfl) ⟨1501898, by rfl⟩ : syracuseStep 2002531 = 3003797) B3003797
theorem B4276901 : Blo 2001435 4276901 := bbase (se 4 (by rfl) ⟨400959, by rfl⟩ : syracuseStep 4276901 = 801919) (by norm_num)
theorem B11405069 : Blo 2001435 11405069 := bstep (se 3 (by rfl) ⟨2138450, by rfl⟩ : syracuseStep 11405069 = 4276901) B4276901
theorem B7603379 : Blo 2001435 7603379 := bstep (se 1 (by rfl) ⟨5702534, by rfl⟩ : syracuseStep 7603379 = 11405069) B11405069
theorem B5068919 : Blo 2001435 5068919 := bstep (se 1 (by rfl) ⟨3801689, by rfl⟩ : syracuseStep 5068919 = 7603379) B7603379
theorem B3379279 : Blo 2001435 3379279 := bstep (se 1 (by rfl) ⟨2534459, by rfl⟩ : syracuseStep 3379279 = 5068919) B5068919
theorem B4505705 : Blo 2001435 4505705 := bstep (se 2 (by rfl) ⟨1689639, by rfl⟩ : syracuseStep 4505705 = 3379279) B3379279
theorem B3003803 : Blo 2001435 3003803 := bstep (se 1 (by rfl) ⟨2252852, by rfl⟩ : syracuseStep 3003803 = 4505705) B4505705
theorem B2002535 : Blo 2001435 2002535 := bstep (se 1 (by rfl) ⟨1501901, by rfl⟩ : syracuseStep 2002535 = 3003803) B3003803
theorem B2252857 : Blo 2001435 2252857 := bbase (se 2 (by rfl) ⟨844821, by rfl⟩ : syracuseStep 2252857 = 1689643) (by norm_num)
theorem B3003809 : Blo 2001435 3003809 := bstep (se 2 (by rfl) ⟨1126428, by rfl⟩ : syracuseStep 3003809 = 2252857) B2252857
theorem B2002539 : Blo 2001435 2002539 := bstep (se 1 (by rfl) ⟨1501904, by rfl⟩ : syracuseStep 2002539 = 3003809) B3003809
theorem B4059733 : Blo 2001435 4059733 := bbase (se 8 (by rfl) ⟨23787, by rfl⟩ : syracuseStep 4059733 = 47575) (by norm_num)
theorem B5412977 : Blo 2001435 5412977 := bstep (se 2 (by rfl) ⟨2029866, by rfl⟩ : syracuseStep 5412977 = 4059733) B4059733
theorem B3608651 : Blo 2001435 3608651 := bstep (se 1 (by rfl) ⟨2706488, by rfl⟩ : syracuseStep 3608651 = 5412977) B5412977
theorem B2405767 : Blo 2001435 2405767 := bstep (se 1 (by rfl) ⟨1804325, by rfl⟩ : syracuseStep 2405767 = 3608651) B3608651
theorem B3207689 : Blo 2001435 3207689 := bstep (se 2 (by rfl) ⟨1202883, by rfl⟩ : syracuseStep 3207689 = 2405767) B2405767
theorem B2138459 : Blo 2001435 2138459 := bstep (se 1 (by rfl) ⟨1603844, by rfl⟩ : syracuseStep 2138459 = 3207689) B3207689
theorem B5702557 : Blo 2001435 5702557 := bstep (se 3 (by rfl) ⟨1069229, by rfl⟩ : syracuseStep 5702557 = 2138459) B2138459
theorem B7603409 : Blo 2001435 7603409 := bstep (se 2 (by rfl) ⟨2851278, by rfl⟩ : syracuseStep 7603409 = 5702557) B5702557
theorem B5068939 : Blo 2001435 5068939 := bstep (se 1 (by rfl) ⟨3801704, by rfl⟩ : syracuseStep 5068939 = 7603409) B7603409
theorem B6758585 : Blo 2001435 6758585 := bstep (se 2 (by rfl) ⟨2534469, by rfl⟩ : syracuseStep 6758585 = 5068939) B5068939
theorem B4505723 : Blo 2001435 4505723 := bstep (se 1 (by rfl) ⟨3379292, by rfl⟩ : syracuseStep 4505723 = 6758585) B6758585
theorem B3003815 : Blo 2001435 3003815 := bstep (se 1 (by rfl) ⟨2252861, by rfl⟩ : syracuseStep 3003815 = 4505723) B4505723
theorem B2002543 : Blo 2001435 2002543 := bstep (se 1 (by rfl) ⟨1501907, by rfl⟩ : syracuseStep 2002543 = 3003815) B3003815
theorem B3003821 : Blo 2001435 3003821 := bbase (se 3 (by rfl) ⟨563216, by rfl⟩ : syracuseStep 3003821 = 1126433) (by norm_num)
theorem B2002547 : Blo 2001435 2002547 := bstep (se 1 (by rfl) ⟨1501910, by rfl⟩ : syracuseStep 2002547 = 3003821) B3003821
theorem B4505741 : Blo 2001435 4505741 := bbase (se 3 (by rfl) ⟨844826, by rfl⟩ : syracuseStep 4505741 = 1689653) (by norm_num)
theorem B3003827 : Blo 2001435 3003827 := bstep (se 1 (by rfl) ⟨2252870, by rfl⟩ : syracuseStep 3003827 = 4505741) B4505741
theorem B2002551 : Blo 2001435 2002551 := bstep (se 1 (by rfl) ⟨1501913, by rfl⟩ : syracuseStep 2002551 = 3003827) B3003827
theorem B2534485 : Blo 2001435 2534485 := bbase (se 8 (by rfl) ⟨14850, by rfl⟩ : syracuseStep 2534485 = 29701) (by norm_num)
theorem B3379313 : Blo 2001435 3379313 := bstep (se 2 (by rfl) ⟨1267242, by rfl⟩ : syracuseStep 3379313 = 2534485) B2534485
theorem B2252875 : Blo 2001435 2252875 := bstep (se 1 (by rfl) ⟨1689656, by rfl⟩ : syracuseStep 2252875 = 3379313) B3379313
theorem B3003833 : Blo 2001435 3003833 := bstep (se 2 (by rfl) ⟨1126437, by rfl⟩ : syracuseStep 3003833 = 2252875) B2252875
theorem B2002555 : Blo 2001435 2002555 := bstep (se 1 (by rfl) ⟨1501916, by rfl⟩ : syracuseStep 2002555 = 3003833) B3003833
theorem B2283617 : Blo 2001435 2283617 := bbase (se 2 (by rfl) ⟨856356, by rfl⟩ : syracuseStep 2283617 = 1712713) (by norm_num)
theorem B6089645 : Blo 2001435 6089645 := bstep (se 3 (by rfl) ⟨1141808, by rfl⟩ : syracuseStep 6089645 = 2283617) B2283617
theorem B4059763 : Blo 2001435 4059763 := bstep (se 1 (by rfl) ⟨3044822, by rfl⟩ : syracuseStep 4059763 = 6089645) B6089645
theorem B86608277 : Blo 2001435 86608277 := bstep (se 6 (by rfl) ⟨2029881, by rfl⟩ : syracuseStep 86608277 = 4059763) B4059763
theorem B57738851 : Blo 2001435 57738851 := bstep (se 1 (by rfl) ⟨43304138, by rfl⟩ : syracuseStep 57738851 = 86608277) B86608277
theorem B38492567 : Blo 2001435 38492567 := bstep (se 1 (by rfl) ⟨28869425, by rfl⟩ : syracuseStep 38492567 = 57738851) B57738851
theorem B25661711 : Blo 2001435 25661711 := bstep (se 1 (by rfl) ⟨19246283, by rfl⟩ : syracuseStep 25661711 = 38492567) B38492567
theorem B17107807 : Blo 2001435 17107807 := bstep (se 1 (by rfl) ⟨12830855, by rfl⟩ : syracuseStep 17107807 = 25661711) B25661711
theorem B22810409 : Blo 2001435 22810409 := bstep (se 2 (by rfl) ⟨8553903, by rfl⟩ : syracuseStep 22810409 = 17107807) B17107807
theorem B15206939 : Blo 2001435 15206939 := bstep (se 1 (by rfl) ⟨11405204, by rfl⟩ : syracuseStep 15206939 = 22810409) B22810409
theorem B10137959 : Blo 2001435 10137959 := bstep (se 1 (by rfl) ⟨7603469, by rfl⟩ : syracuseStep 10137959 = 15206939) B15206939
theorem B6758639 : Blo 2001435 6758639 := bstep (se 1 (by rfl) ⟨5068979, by rfl⟩ : syracuseStep 6758639 = 10137959) B10137959
theorem B4505759 : Blo 2001435 4505759 := bstep (se 1 (by rfl) ⟨3379319, by rfl⟩ : syracuseStep 4505759 = 6758639) B6758639
theorem B3003839 : Blo 2001435 3003839 := bstep (se 1 (by rfl) ⟨2252879, by rfl⟩ : syracuseStep 3003839 = 4505759) B4505759
theorem B2002559 : Blo 2001435 2002559 := bstep (se 1 (by rfl) ⟨1501919, by rfl⟩ : syracuseStep 2002559 = 3003839) B3003839
theorem B3003845 : Blo 2001435 3003845 := bbase (se 4 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 3003845 = 563221) (by norm_num)
theorem B2002563 : Blo 2001435 2002563 := bstep (se 1 (by rfl) ⟨1501922, by rfl⟩ : syracuseStep 2002563 = 3003845) B3003845
theorem B3379333 : Blo 2001435 3379333 := bbase (se 4 (by rfl) ⟨316812, by rfl⟩ : syracuseStep 3379333 = 633625) (by norm_num)
theorem B4505777 : Blo 2001435 4505777 := bstep (se 2 (by rfl) ⟨1689666, by rfl⟩ : syracuseStep 4505777 = 3379333) B3379333
theorem B3003851 : Blo 2001435 3003851 := bstep (se 1 (by rfl) ⟨2252888, by rfl⟩ : syracuseStep 3003851 = 4505777) B4505777
theorem B2002567 : Blo 2001435 2002567 := bstep (se 1 (by rfl) ⟨1501925, by rfl⟩ : syracuseStep 2002567 = 3003851) B3003851
theorem B2252893 : Blo 2001435 2252893 := bbase (se 3 (by rfl) ⟨422417, by rfl⟩ : syracuseStep 2252893 = 844835) (by norm_num)
theorem B3003857 : Blo 2001435 3003857 := bstep (se 2 (by rfl) ⟨1126446, by rfl⟩ : syracuseStep 3003857 = 2252893) B2252893
theorem B2002571 : Blo 2001435 2002571 := bstep (se 1 (by rfl) ⟨1501928, by rfl⟩ : syracuseStep 2002571 = 3003857) B3003857
theorem B6758693 : Blo 2001435 6758693 := bbase (se 4 (by rfl) ⟨633627, by rfl⟩ : syracuseStep 6758693 = 1267255) (by norm_num)
theorem B4505795 : Blo 2001435 4505795 := bstep (se 1 (by rfl) ⟨3379346, by rfl⟩ : syracuseStep 4505795 = 6758693) B6758693
theorem B3003863 : Blo 2001435 3003863 := bstep (se 1 (by rfl) ⟨2252897, by rfl⟩ : syracuseStep 3003863 = 4505795) B4505795
theorem B2002575 : Blo 2001435 2002575 := bstep (se 1 (by rfl) ⟨1501931, by rfl⟩ : syracuseStep 2002575 = 3003863) B3003863
theorem B3003869 : Blo 2001435 3003869 := bbase (se 3 (by rfl) ⟨563225, by rfl⟩ : syracuseStep 3003869 = 1126451) (by norm_num)
theorem B2002579 : Blo 2001435 2002579 := bstep (se 1 (by rfl) ⟨1501934, by rfl⟩ : syracuseStep 2002579 = 3003869) B3003869
theorem B4505813 : Blo 2001435 4505813 := bbase (se 7 (by rfl) ⟨52802, by rfl⟩ : syracuseStep 4505813 = 105605) (by norm_num)
theorem B3003875 : Blo 2001435 3003875 := bstep (se 1 (by rfl) ⟨2252906, by rfl⟩ : syracuseStep 3003875 = 4505813) B4505813
theorem B2002583 : Blo 2001435 2002583 := bstep (se 1 (by rfl) ⟨1501937, by rfl⟩ : syracuseStep 2002583 = 3003875) B3003875
theorem B7707317 : Blo 2001435 7707317 := bbase (se 5 (by rfl) ⟨361280, by rfl⟩ : syracuseStep 7707317 = 722561) (by norm_num)
theorem B82211381 : Blo 2001435 82211381 := bstep (se 5 (by rfl) ⟨3853658, by rfl⟩ : syracuseStep 82211381 = 7707317) B7707317
theorem B54807587 : Blo 2001435 54807587 := bstep (se 1 (by rfl) ⟨41105690, by rfl⟩ : syracuseStep 54807587 = 82211381) B82211381
theorem B36538391 : Blo 2001435 36538391 := bstep (se 1 (by rfl) ⟨27403793, by rfl⟩ : syracuseStep 36538391 = 54807587) B54807587
theorem B24358927 : Blo 2001435 24358927 := bstep (se 1 (by rfl) ⟨18269195, by rfl⟩ : syracuseStep 24358927 = 36538391) B36538391
theorem B32478569 : Blo 2001435 32478569 := bstep (se 2 (by rfl) ⟨12179463, by rfl⟩ : syracuseStep 32478569 = 24358927) B24358927
theorem B21652379 : Blo 2001435 21652379 := bstep (se 1 (by rfl) ⟨16239284, by rfl⟩ : syracuseStep 21652379 = 32478569) B32478569
theorem B14434919 : Blo 2001435 14434919 := bstep (se 1 (by rfl) ⟨10826189, by rfl⟩ : syracuseStep 14434919 = 21652379) B21652379
theorem B9623279 : Blo 2001435 9623279 := bstep (se 1 (by rfl) ⟨7217459, by rfl⟩ : syracuseStep 9623279 = 14434919) B14434919
theorem B6415519 : Blo 2001435 6415519 := bstep (se 1 (by rfl) ⟨4811639, by rfl⟩ : syracuseStep 6415519 = 9623279) B9623279
theorem B8554025 : Blo 2001435 8554025 := bstep (se 2 (by rfl) ⟨3207759, by rfl⟩ : syracuseStep 8554025 = 6415519) B6415519
theorem B5702683 : Blo 2001435 5702683 := bstep (se 1 (by rfl) ⟨4277012, by rfl⟩ : syracuseStep 5702683 = 8554025) B8554025
theorem B7603577 : Blo 2001435 7603577 := bstep (se 2 (by rfl) ⟨2851341, by rfl⟩ : syracuseStep 7603577 = 5702683) B5702683
theorem B5069051 : Blo 2001435 5069051 := bstep (se 1 (by rfl) ⟨3801788, by rfl⟩ : syracuseStep 5069051 = 7603577) B7603577
theorem B3379367 : Blo 2001435 3379367 := bstep (se 1 (by rfl) ⟨2534525, by rfl⟩ : syracuseStep 3379367 = 5069051) B5069051
theorem B2252911 : Blo 2001435 2252911 := bstep (se 1 (by rfl) ⟨1689683, by rfl⟩ : syracuseStep 2252911 = 3379367) B3379367
theorem B3003881 : Blo 2001435 3003881 := bstep (se 2 (by rfl) ⟨1126455, by rfl⟩ : syracuseStep 3003881 = 2252911) B2252911
theorem B2002587 : Blo 2001435 2002587 := bstep (se 1 (by rfl) ⟨1501940, by rfl⟩ : syracuseStep 2002587 = 3003881) B3003881
theorem B12831061 : Blo 2001435 12831061 := bbase (se 10 (by rfl) ⟨18795, by rfl⟩ : syracuseStep 12831061 = 37591) (by norm_num)
theorem B17108081 : Blo 2001435 17108081 := bstep (se 2 (by rfl) ⟨6415530, by rfl⟩ : syracuseStep 17108081 = 12831061) B12831061
theorem B11405387 : Blo 2001435 11405387 := bstep (se 1 (by rfl) ⟨8554040, by rfl⟩ : syracuseStep 11405387 = 17108081) B17108081
theorem B7603591 : Blo 2001435 7603591 := bstep (se 1 (by rfl) ⟨5702693, by rfl⟩ : syracuseStep 7603591 = 11405387) B11405387
theorem B10138121 : Blo 2001435 10138121 := bstep (se 2 (by rfl) ⟨3801795, by rfl⟩ : syracuseStep 10138121 = 7603591) B7603591
theorem B6758747 : Blo 2001435 6758747 := bstep (se 1 (by rfl) ⟨5069060, by rfl⟩ : syracuseStep 6758747 = 10138121) B10138121
theorem B4505831 : Blo 2001435 4505831 := bstep (se 1 (by rfl) ⟨3379373, by rfl⟩ : syracuseStep 4505831 = 6758747) B6758747
theorem B3003887 : Blo 2001435 3003887 := bstep (se 1 (by rfl) ⟨2252915, by rfl⟩ : syracuseStep 3003887 = 4505831) B4505831
theorem B2002591 : Blo 2001435 2002591 := bstep (se 1 (by rfl) ⟨1501943, by rfl⟩ : syracuseStep 2002591 = 3003887) B3003887
theorem B3003893 : Blo 2001435 3003893 := bbase (se 5 (by rfl) ⟨140807, by rfl⟩ : syracuseStep 3003893 = 281615) (by norm_num)
theorem B2002595 : Blo 2001435 2002595 := bstep (se 1 (by rfl) ⟨1501946, by rfl⟩ : syracuseStep 2002595 = 3003893) B3003893
theorem B4811669 : Blo 2001435 4811669 := bbase (se 6 (by rfl) ⟨112773, by rfl⟩ : syracuseStep 4811669 = 225547) (by norm_num)
theorem B3207779 : Blo 2001435 3207779 := bstep (se 1 (by rfl) ⟨2405834, by rfl⟩ : syracuseStep 3207779 = 4811669) B4811669
theorem B2138519 : Blo 2001435 2138519 := bstep (se 1 (by rfl) ⟨1603889, by rfl⟩ : syracuseStep 2138519 = 3207779) B3207779
theorem B5702717 : Blo 2001435 5702717 := bstep (se 3 (by rfl) ⟨1069259, by rfl⟩ : syracuseStep 5702717 = 2138519) B2138519
theorem B3801811 : Blo 2001435 3801811 := bstep (se 1 (by rfl) ⟨2851358, by rfl⟩ : syracuseStep 3801811 = 5702717) B5702717
theorem B5069081 : Blo 2001435 5069081 := bstep (se 2 (by rfl) ⟨1900905, by rfl⟩ : syracuseStep 5069081 = 3801811) B3801811
theorem B3379387 : Blo 2001435 3379387 := bstep (se 1 (by rfl) ⟨2534540, by rfl⟩ : syracuseStep 3379387 = 5069081) B5069081
theorem B4505849 : Blo 2001435 4505849 := bstep (se 2 (by rfl) ⟨1689693, by rfl⟩ : syracuseStep 4505849 = 3379387) B3379387
theorem B3003899 : Blo 2001435 3003899 := bstep (se 1 (by rfl) ⟨2252924, by rfl⟩ : syracuseStep 3003899 = 4505849) B4505849
theorem B2002599 : Blo 2001435 2002599 := bstep (se 1 (by rfl) ⟨1501949, by rfl⟩ : syracuseStep 2002599 = 3003899) B3003899
theorem B2252929 : Blo 2001435 2252929 := bbase (se 2 (by rfl) ⟨844848, by rfl⟩ : syracuseStep 2252929 = 1689697) (by norm_num)
theorem B3003905 : Blo 2001435 3003905 := bstep (se 2 (by rfl) ⟨1126464, by rfl⟩ : syracuseStep 3003905 = 2252929) B2252929
theorem B2002603 : Blo 2001435 2002603 := bstep (se 1 (by rfl) ⟨1501952, by rfl⟩ : syracuseStep 2002603 = 3003905) B3003905
theorem B5069101 : Blo 2001435 5069101 := bbase (se 3 (by rfl) ⟨950456, by rfl⟩ : syracuseStep 5069101 = 1900913) (by norm_num)
theorem B6758801 : Blo 2001435 6758801 := bstep (se 2 (by rfl) ⟨2534550, by rfl⟩ : syracuseStep 6758801 = 5069101) B5069101
theorem B4505867 : Blo 2001435 4505867 := bstep (se 1 (by rfl) ⟨3379400, by rfl⟩ : syracuseStep 4505867 = 6758801) B6758801
theorem B3003911 : Blo 2001435 3003911 := bstep (se 1 (by rfl) ⟨2252933, by rfl⟩ : syracuseStep 3003911 = 4505867) B4505867
theorem B2002607 : Blo 2001435 2002607 := bstep (se 1 (by rfl) ⟨1501955, by rfl⟩ : syracuseStep 2002607 = 3003911) B3003911
theorem B3003917 : Blo 2001435 3003917 := bbase (se 3 (by rfl) ⟨563234, by rfl⟩ : syracuseStep 3003917 = 1126469) (by norm_num)
theorem B2002611 : Blo 2001435 2002611 := bstep (se 1 (by rfl) ⟨1501958, by rfl⟩ : syracuseStep 2002611 = 3003917) B3003917
theorem B4505885 : Blo 2001435 4505885 := bbase (se 3 (by rfl) ⟨844853, by rfl⟩ : syracuseStep 4505885 = 1689707) (by norm_num)
theorem B3003923 : Blo 2001435 3003923 := bstep (se 1 (by rfl) ⟨2252942, by rfl⟩ : syracuseStep 3003923 = 4505885) B4505885
theorem B2002615 : Blo 2001435 2002615 := bstep (se 1 (by rfl) ⟨1501961, by rfl⟩ : syracuseStep 2002615 = 3003923) B3003923
theorem B3379421 : Blo 2001435 3379421 := bbase (se 3 (by rfl) ⟨633641, by rfl⟩ : syracuseStep 3379421 = 1267283) (by norm_num)
theorem B2252947 : Blo 2001435 2252947 := bstep (se 1 (by rfl) ⟨1689710, by rfl⟩ : syracuseStep 2252947 = 3379421) B3379421
theorem B3003929 : Blo 2001435 3003929 := bstep (se 2 (by rfl) ⟨1126473, by rfl⟩ : syracuseStep 3003929 = 2252947) B2252947
theorem B2002619 : Blo 2001435 2002619 := bstep (se 1 (by rfl) ⟨1501964, by rfl⟩ : syracuseStep 2002619 = 3003929) B3003929
theorem B4811725 : Blo 2001435 4811725 := bbase (se 3 (by rfl) ⟨902198, by rfl⟩ : syracuseStep 4811725 = 1804397) (by norm_num)
theorem B6415633 : Blo 2001435 6415633 := bstep (se 2 (by rfl) ⟨2405862, by rfl⟩ : syracuseStep 6415633 = 4811725) B4811725
theorem B8554177 : Blo 2001435 8554177 := bstep (se 2 (by rfl) ⟨3207816, by rfl⟩ : syracuseStep 8554177 = 6415633) B6415633
theorem B11405569 : Blo 2001435 11405569 := bstep (se 2 (by rfl) ⟨4277088, by rfl⟩ : syracuseStep 11405569 = 8554177) B8554177
theorem B15207425 : Blo 2001435 15207425 := bstep (se 2 (by rfl) ⟨5702784, by rfl⟩ : syracuseStep 15207425 = 11405569) B11405569
theorem B10138283 : Blo 2001435 10138283 := bstep (se 1 (by rfl) ⟨7603712, by rfl⟩ : syracuseStep 10138283 = 15207425) B15207425
theorem B6758855 : Blo 2001435 6758855 := bstep (se 1 (by rfl) ⟨5069141, by rfl⟩ : syracuseStep 6758855 = 10138283) B10138283
theorem B4505903 : Blo 2001435 4505903 := bstep (se 1 (by rfl) ⟨3379427, by rfl⟩ : syracuseStep 4505903 = 6758855) B6758855
theorem B3003935 : Blo 2001435 3003935 := bstep (se 1 (by rfl) ⟨2252951, by rfl⟩ : syracuseStep 3003935 = 4505903) B4505903
theorem B2002623 : Blo 2001435 2002623 := bstep (se 1 (by rfl) ⟨1501967, by rfl⟩ : syracuseStep 2002623 = 3003935) B3003935
theorem B3003941 : Blo 2001435 3003941 := bbase (se 4 (by rfl) ⟨281619, by rfl⟩ : syracuseStep 3003941 = 563239) (by norm_num)
theorem B2002627 : Blo 2001435 2002627 := bstep (se 1 (by rfl) ⟨1501970, by rfl⟩ : syracuseStep 2002627 = 3003941) B3003941
theorem B2534581 : Blo 2001435 2534581 := bbase (se 5 (by rfl) ⟨118808, by rfl⟩ : syracuseStep 2534581 = 237617) (by norm_num)
theorem B3379441 : Blo 2001435 3379441 := bstep (se 2 (by rfl) ⟨1267290, by rfl⟩ : syracuseStep 3379441 = 2534581) B2534581
theorem B4505921 : Blo 2001435 4505921 := bstep (se 2 (by rfl) ⟨1689720, by rfl⟩ : syracuseStep 4505921 = 3379441) B3379441
theorem B3003947 : Blo 2001435 3003947 := bstep (se 1 (by rfl) ⟨2252960, by rfl⟩ : syracuseStep 3003947 = 4505921) B4505921
theorem B2002631 : Blo 2001435 2002631 := bstep (se 1 (by rfl) ⟨1501973, by rfl⟩ : syracuseStep 2002631 = 3003947) B3003947
theorem B2252965 : Blo 2001435 2252965 := bbase (se 4 (by rfl) ⟨211215, by rfl⟩ : syracuseStep 2252965 = 422431) (by norm_num)
theorem B3003953 : Blo 2001435 3003953 := bstep (se 2 (by rfl) ⟨1126482, by rfl⟩ : syracuseStep 3003953 = 2252965) B2252965
theorem B2002635 : Blo 2001435 2002635 := bstep (se 1 (by rfl) ⟨1501976, by rfl⟩ : syracuseStep 2002635 = 3003953) B3003953
theorem B2283709 : Blo 2001435 2283709 := bbase (se 3 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 2283709 = 856391) (by norm_num)
theorem B3044945 : Blo 2001435 3044945 := bstep (se 2 (by rfl) ⟨1141854, by rfl⟩ : syracuseStep 3044945 = 2283709) B2283709
theorem B8119853 : Blo 2001435 8119853 := bstep (se 3 (by rfl) ⟨1522472, by rfl⟩ : syracuseStep 8119853 = 3044945) B3044945
theorem B5413235 : Blo 2001435 5413235 := bstep (se 1 (by rfl) ⟨4059926, by rfl⟩ : syracuseStep 5413235 = 8119853) B8119853
theorem B14435293 : Blo 2001435 14435293 := bstep (se 3 (by rfl) ⟨2706617, by rfl⟩ : syracuseStep 14435293 = 5413235) B5413235
theorem B19247057 : Blo 2001435 19247057 := bstep (se 2 (by rfl) ⟨7217646, by rfl⟩ : syracuseStep 19247057 = 14435293) B14435293
theorem B12831371 : Blo 2001435 12831371 := bstep (se 1 (by rfl) ⟨9623528, by rfl⟩ : syracuseStep 12831371 = 19247057) B19247057
theorem B8554247 : Blo 2001435 8554247 := bstep (se 1 (by rfl) ⟨6415685, by rfl⟩ : syracuseStep 8554247 = 12831371) B12831371
theorem B5702831 : Blo 2001435 5702831 := bstep (se 1 (by rfl) ⟨4277123, by rfl⟩ : syracuseStep 5702831 = 8554247) B8554247
theorem B3801887 : Blo 2001435 3801887 := bstep (se 1 (by rfl) ⟨2851415, by rfl⟩ : syracuseStep 3801887 = 5702831) B5702831
theorem B2534591 : Blo 2001435 2534591 := bstep (se 1 (by rfl) ⟨1900943, by rfl⟩ : syracuseStep 2534591 = 3801887) B3801887
theorem B6758909 : Blo 2001435 6758909 := bstep (se 3 (by rfl) ⟨1267295, by rfl⟩ : syracuseStep 6758909 = 2534591) B2534591
theorem B4505939 : Blo 2001435 4505939 := bstep (se 1 (by rfl) ⟨3379454, by rfl⟩ : syracuseStep 4505939 = 6758909) B6758909
theorem B3003959 : Blo 2001435 3003959 := bstep (se 1 (by rfl) ⟨2252969, by rfl⟩ : syracuseStep 3003959 = 4505939) B4505939
theorem B2002639 : Blo 2001435 2002639 := bstep (se 1 (by rfl) ⟨1501979, by rfl⟩ : syracuseStep 2002639 = 3003959) B3003959
theorem B3003965 : Blo 2001435 3003965 := bbase (se 3 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 3003965 = 1126487) (by norm_num)
theorem B2002643 : Blo 2001435 2002643 := bstep (se 1 (by rfl) ⟨1501982, by rfl⟩ : syracuseStep 2002643 = 3003965) B3003965
theorem B4505957 : Blo 2001435 4505957 := bbase (se 4 (by rfl) ⟨422433, by rfl⟩ : syracuseStep 4505957 = 844867) (by norm_num)
theorem B3003971 : Blo 2001435 3003971 := bstep (se 1 (by rfl) ⟨2252978, by rfl⟩ : syracuseStep 3003971 = 4505957) B4505957
theorem B2002647 : Blo 2001435 2002647 := bstep (se 1 (by rfl) ⟨1501985, by rfl⟩ : syracuseStep 2002647 = 3003971) B3003971
theorem B5069213 : Blo 2001435 5069213 := bbase (se 3 (by rfl) ⟨950477, by rfl⟩ : syracuseStep 5069213 = 1900955) (by norm_num)
theorem B3379475 : Blo 2001435 3379475 := bstep (se 1 (by rfl) ⟨2534606, by rfl⟩ : syracuseStep 3379475 = 5069213) B5069213
theorem B2252983 : Blo 2001435 2252983 := bstep (se 1 (by rfl) ⟨1689737, by rfl⟩ : syracuseStep 2252983 = 3379475) B3379475
theorem B3003977 : Blo 2001435 3003977 := bstep (se 2 (by rfl) ⟨1126491, by rfl⟩ : syracuseStep 3003977 = 2252983) B2252983
theorem B2002651 : Blo 2001435 2002651 := bstep (se 1 (by rfl) ⟨1501988, by rfl⟩ : syracuseStep 2002651 = 3003977) B3003977
theorem B3801917 : Blo 2001435 3801917 := bbase (se 3 (by rfl) ⟨712859, by rfl⟩ : syracuseStep 3801917 = 1425719) (by norm_num)
theorem B10138445 : Blo 2001435 10138445 := bstep (se 3 (by rfl) ⟨1900958, by rfl⟩ : syracuseStep 10138445 = 3801917) B3801917
theorem B6758963 : Blo 2001435 6758963 := bstep (se 1 (by rfl) ⟨5069222, by rfl⟩ : syracuseStep 6758963 = 10138445) B10138445
theorem B4505975 : Blo 2001435 4505975 := bstep (se 1 (by rfl) ⟨3379481, by rfl⟩ : syracuseStep 4505975 = 6758963) B6758963
theorem B3003983 : Blo 2001435 3003983 := bstep (se 1 (by rfl) ⟨2252987, by rfl⟩ : syracuseStep 3003983 = 4505975) B4505975
theorem B2002655 : Blo 2001435 2002655 := bstep (se 1 (by rfl) ⟨1501991, by rfl⟩ : syracuseStep 2002655 = 3003983) B3003983
theorem B3003989 : Blo 2001435 3003989 := bbase (se 8 (by rfl) ⟨17601, by rfl⟩ : syracuseStep 3003989 = 35203) (by norm_num)
theorem B2002659 : Blo 2001435 2002659 := bstep (se 1 (by rfl) ⟨1501994, by rfl⟩ : syracuseStep 2002659 = 3003989) B3003989
theorem B5413301 : Blo 2001435 5413301 := bbase (se 5 (by rfl) ⟨253748, by rfl⟩ : syracuseStep 5413301 = 507497) (by norm_num)
theorem B3608867 : Blo 2001435 3608867 := bstep (se 1 (by rfl) ⟨2706650, by rfl⟩ : syracuseStep 3608867 = 5413301) B5413301
theorem B2405911 : Blo 2001435 2405911 := bstep (se 1 (by rfl) ⟨1804433, by rfl⟩ : syracuseStep 2405911 = 3608867) B3608867
theorem B3207881 : Blo 2001435 3207881 := bstep (se 2 (by rfl) ⟨1202955, by rfl⟩ : syracuseStep 3207881 = 2405911) B2405911
theorem B8554349 : Blo 2001435 8554349 := bstep (se 3 (by rfl) ⟨1603940, by rfl⟩ : syracuseStep 8554349 = 3207881) B3207881
theorem B5702899 : Blo 2001435 5702899 := bstep (se 1 (by rfl) ⟨4277174, by rfl⟩ : syracuseStep 5702899 = 8554349) B8554349
theorem B7603865 : Blo 2001435 7603865 := bstep (se 2 (by rfl) ⟨2851449, by rfl⟩ : syracuseStep 7603865 = 5702899) B5702899
theorem B5069243 : Blo 2001435 5069243 := bstep (se 1 (by rfl) ⟨3801932, by rfl⟩ : syracuseStep 5069243 = 7603865) B7603865
theorem B3379495 : Blo 2001435 3379495 := bstep (se 1 (by rfl) ⟨2534621, by rfl⟩ : syracuseStep 3379495 = 5069243) B5069243
theorem B4505993 : Blo 2001435 4505993 := bstep (se 2 (by rfl) ⟨1689747, by rfl⟩ : syracuseStep 4505993 = 3379495) B3379495
theorem B3003995 : Blo 2001435 3003995 := bstep (se 1 (by rfl) ⟨2252996, by rfl⟩ : syracuseStep 3003995 = 4505993) B4505993
theorem B2002663 : Blo 2001435 2002663 := bstep (se 1 (by rfl) ⟨1501997, by rfl⟩ : syracuseStep 2002663 = 3003995) B3003995
theorem B2253001 : Blo 2001435 2253001 := bbase (se 2 (by rfl) ⟨844875, by rfl⟩ : syracuseStep 2253001 = 1689751) (by norm_num)
theorem B3004001 : Blo 2001435 3004001 := bstep (se 2 (by rfl) ⟨1126500, by rfl⟩ : syracuseStep 3004001 = 2253001) B2253001
theorem B2002667 : Blo 2001435 2002667 := bstep (se 1 (by rfl) ⟨1502000, by rfl⟩ : syracuseStep 2002667 = 3004001) B3004001
theorem B9134981 : Blo 2001435 9134981 := bbase (se 4 (by rfl) ⟨856404, by rfl⟩ : syracuseStep 9134981 = 1712809) (by norm_num)
theorem B6089987 : Blo 2001435 6089987 := bstep (se 1 (by rfl) ⟨4567490, by rfl⟩ : syracuseStep 6089987 = 9134981) B9134981
theorem B4059991 : Blo 2001435 4059991 := bstep (se 1 (by rfl) ⟨3044993, by rfl⟩ : syracuseStep 4059991 = 6089987) B6089987
theorem B5413321 : Blo 2001435 5413321 := bstep (se 2 (by rfl) ⟨2029995, by rfl⟩ : syracuseStep 5413321 = 4059991) B4059991
theorem B7217761 : Blo 2001435 7217761 := bstep (se 2 (by rfl) ⟨2706660, by rfl⟩ : syracuseStep 7217761 = 5413321) B5413321
theorem B9623681 : Blo 2001435 9623681 := bstep (se 2 (by rfl) ⟨3608880, by rfl⟩ : syracuseStep 9623681 = 7217761) B7217761
theorem B6415787 : Blo 2001435 6415787 := bstep (se 1 (by rfl) ⟨4811840, by rfl⟩ : syracuseStep 6415787 = 9623681) B9623681
theorem B17108765 : Blo 2001435 17108765 := bstep (se 3 (by rfl) ⟨3207893, by rfl⟩ : syracuseStep 17108765 = 6415787) B6415787
theorem B11405843 : Blo 2001435 11405843 := bstep (se 1 (by rfl) ⟨8554382, by rfl⟩ : syracuseStep 11405843 = 17108765) B17108765
theorem B7603895 : Blo 2001435 7603895 := bstep (se 1 (by rfl) ⟨5702921, by rfl⟩ : syracuseStep 7603895 = 11405843) B11405843
theorem B5069263 : Blo 2001435 5069263 := bstep (se 1 (by rfl) ⟨3801947, by rfl⟩ : syracuseStep 5069263 = 7603895) B7603895
theorem B6759017 : Blo 2001435 6759017 := bstep (se 2 (by rfl) ⟨2534631, by rfl⟩ : syracuseStep 6759017 = 5069263) B5069263
theorem B4506011 : Blo 2001435 4506011 := bstep (se 1 (by rfl) ⟨3379508, by rfl⟩ : syracuseStep 4506011 = 6759017) B6759017
theorem B3004007 : Blo 2001435 3004007 := bstep (se 1 (by rfl) ⟨2253005, by rfl⟩ : syracuseStep 3004007 = 4506011) B4506011
theorem B2002671 : Blo 2001435 2002671 := bstep (se 1 (by rfl) ⟨1502003, by rfl⟩ : syracuseStep 2002671 = 3004007) B3004007
theorem B3004013 : Blo 2001435 3004013 := bbase (se 3 (by rfl) ⟨563252, by rfl⟩ : syracuseStep 3004013 = 1126505) (by norm_num)
theorem B2002675 : Blo 2001435 2002675 := bstep (se 1 (by rfl) ⟨1502006, by rfl⟩ : syracuseStep 2002675 = 3004013) B3004013
theorem B4506029 : Blo 2001435 4506029 := bbase (se 3 (by rfl) ⟨844880, by rfl⟩ : syracuseStep 4506029 = 1689761) (by norm_num)
theorem B3004019 : Blo 2001435 3004019 := bstep (se 1 (by rfl) ⟨2253014, by rfl⟩ : syracuseStep 3004019 = 4506029) B4506029
theorem B2002679 : Blo 2001435 2002679 := bstep (se 1 (by rfl) ⟨1502009, by rfl⟩ : syracuseStep 2002679 = 3004019) B3004019
theorem B2138609 : Blo 2001435 2138609 := bbase (se 2 (by rfl) ⟨801978, by rfl⟩ : syracuseStep 2138609 = 1603957) (by norm_num)
theorem B5702957 : Blo 2001435 5702957 := bstep (se 3 (by rfl) ⟨1069304, by rfl⟩ : syracuseStep 5702957 = 2138609) B2138609
theorem B3801971 : Blo 2001435 3801971 := bstep (se 1 (by rfl) ⟨2851478, by rfl⟩ : syracuseStep 3801971 = 5702957) B5702957
theorem B2534647 : Blo 2001435 2534647 := bstep (se 1 (by rfl) ⟨1900985, by rfl⟩ : syracuseStep 2534647 = 3801971) B3801971
theorem B3379529 : Blo 2001435 3379529 := bstep (se 2 (by rfl) ⟨1267323, by rfl⟩ : syracuseStep 3379529 = 2534647) B2534647
theorem B2253019 : Blo 2001435 2253019 := bstep (se 1 (by rfl) ⟨1689764, by rfl⟩ : syracuseStep 2253019 = 3379529) B3379529
theorem B3004025 : Blo 2001435 3004025 := bstep (se 2 (by rfl) ⟨1126509, by rfl⟩ : syracuseStep 3004025 = 2253019) B2253019
theorem B2002683 : Blo 2001435 2002683 := bstep (se 1 (by rfl) ⟨1502012, by rfl⟩ : syracuseStep 2002683 = 3004025) B3004025
theorem B3425645 : Blo 2001435 3425645 := bbase (se 3 (by rfl) ⟨642308, by rfl⟩ : syracuseStep 3425645 = 1284617) (by norm_num)
theorem B2283763 : Blo 2001435 2283763 := bstep (se 1 (by rfl) ⟨1712822, by rfl⟩ : syracuseStep 2283763 = 3425645) B3425645
theorem B3045017 : Blo 2001435 3045017 := bstep (se 2 (by rfl) ⟨1141881, by rfl⟩ : syracuseStep 3045017 = 2283763) B2283763
theorem B8120045 : Blo 2001435 8120045 := bstep (se 3 (by rfl) ⟨1522508, by rfl⟩ : syracuseStep 8120045 = 3045017) B3045017
theorem B21653453 : Blo 2001435 21653453 := bstep (se 3 (by rfl) ⟨4060022, by rfl⟩ : syracuseStep 21653453 = 8120045) B8120045
theorem B57742541 : Blo 2001435 57742541 := bstep (se 3 (by rfl) ⟨10826726, by rfl⟩ : syracuseStep 57742541 = 21653453) B21653453
theorem B38495027 : Blo 2001435 38495027 := bstep (se 1 (by rfl) ⟨28871270, by rfl⟩ : syracuseStep 38495027 = 57742541) B57742541
theorem B25663351 : Blo 2001435 25663351 := bstep (se 1 (by rfl) ⟨19247513, by rfl⟩ : syracuseStep 25663351 = 38495027) B38495027
theorem B34217801 : Blo 2001435 34217801 := bstep (se 2 (by rfl) ⟨12831675, by rfl⟩ : syracuseStep 34217801 = 25663351) B25663351
theorem B22811867 : Blo 2001435 22811867 := bstep (se 1 (by rfl) ⟨17108900, by rfl⟩ : syracuseStep 22811867 = 34217801) B34217801
theorem B15207911 : Blo 2001435 15207911 := bstep (se 1 (by rfl) ⟨11405933, by rfl⟩ : syracuseStep 15207911 = 22811867) B22811867
theorem B10138607 : Blo 2001435 10138607 := bstep (se 1 (by rfl) ⟨7603955, by rfl⟩ : syracuseStep 10138607 = 15207911) B15207911
theorem B6759071 : Blo 2001435 6759071 := bstep (se 1 (by rfl) ⟨5069303, by rfl⟩ : syracuseStep 6759071 = 10138607) B10138607
theorem B4506047 : Blo 2001435 4506047 := bstep (se 1 (by rfl) ⟨3379535, by rfl⟩ : syracuseStep 4506047 = 6759071) B6759071
theorem B3004031 : Blo 2001435 3004031 := bstep (se 1 (by rfl) ⟨2253023, by rfl⟩ : syracuseStep 3004031 = 4506047) B4506047
theorem B2002687 : Blo 2001435 2002687 := bstep (se 1 (by rfl) ⟨1502015, by rfl⟩ : syracuseStep 2002687 = 3004031) B3004031
theorem B3004037 : Blo 2001435 3004037 := bbase (se 4 (by rfl) ⟨281628, by rfl⟩ : syracuseStep 3004037 = 563257) (by norm_num)
theorem B2002691 : Blo 2001435 2002691 := bstep (se 1 (by rfl) ⟨1502018, by rfl⟩ : syracuseStep 2002691 = 3004037) B3004037
theorem B3379549 : Blo 2001435 3379549 := bbase (se 3 (by rfl) ⟨633665, by rfl⟩ : syracuseStep 3379549 = 1267331) (by norm_num)
theorem B4506065 : Blo 2001435 4506065 := bstep (se 2 (by rfl) ⟨1689774, by rfl⟩ : syracuseStep 4506065 = 3379549) B3379549
theorem B3004043 : Blo 2001435 3004043 := bstep (se 1 (by rfl) ⟨2253032, by rfl⟩ : syracuseStep 3004043 = 4506065) B4506065
theorem B2002695 : Blo 2001435 2002695 := bstep (se 1 (by rfl) ⟨1502021, by rfl⟩ : syracuseStep 2002695 = 3004043) B3004043
theorem B2253037 : Blo 2001435 2253037 := bbase (se 3 (by rfl) ⟨422444, by rfl⟩ : syracuseStep 2253037 = 844889) (by norm_num)
theorem B3004049 : Blo 2001435 3004049 := bstep (se 2 (by rfl) ⟨1126518, by rfl⟩ : syracuseStep 3004049 = 2253037) B2253037
theorem B2002699 : Blo 2001435 2002699 := bstep (se 1 (by rfl) ⟨1502024, by rfl⟩ : syracuseStep 2002699 = 3004049) B3004049
theorem B6759125 : Blo 2001435 6759125 := bbase (se 7 (by rfl) ⟨79208, by rfl⟩ : syracuseStep 6759125 = 158417) (by norm_num)
theorem B4506083 : Blo 2001435 4506083 := bstep (se 1 (by rfl) ⟨3379562, by rfl⟩ : syracuseStep 4506083 = 6759125) B6759125
theorem B3004055 : Blo 2001435 3004055 := bstep (se 1 (by rfl) ⟨2253041, by rfl⟩ : syracuseStep 3004055 = 4506083) B4506083
theorem B2002703 : Blo 2001435 2002703 := bstep (se 1 (by rfl) ⟨1502027, by rfl⟩ : syracuseStep 2002703 = 3004055) B3004055
theorem B3004061 : Blo 2001435 3004061 := bbase (se 3 (by rfl) ⟨563261, by rfl⟩ : syracuseStep 3004061 = 1126523) (by norm_num)
theorem B2002707 : Blo 2001435 2002707 := bstep (se 1 (by rfl) ⟨1502030, by rfl⟩ : syracuseStep 2002707 = 3004061) B3004061
theorem B4506101 : Blo 2001435 4506101 := bbase (se 5 (by rfl) ⟨211223, by rfl⟩ : syracuseStep 4506101 = 422447) (by norm_num)
theorem B3004067 : Blo 2001435 3004067 := bstep (se 1 (by rfl) ⟨2253050, by rfl⟩ : syracuseStep 3004067 = 4506101) B4506101
theorem B2002711 : Blo 2001435 2002711 := bstep (se 1 (by rfl) ⟨1502033, by rfl⟩ : syracuseStep 2002711 = 3004067) B3004067
theorem B38495573 : Blo 2001435 38495573 := bbase (se 12 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 38495573 = 28195) (by norm_num)
theorem B25663715 : Blo 2001435 25663715 := bstep (se 1 (by rfl) ⟨19247786, by rfl⟩ : syracuseStep 25663715 = 38495573) B38495573
theorem B17109143 : Blo 2001435 17109143 := bstep (se 1 (by rfl) ⟨12831857, by rfl⟩ : syracuseStep 17109143 = 25663715) B25663715
theorem B11406095 : Blo 2001435 11406095 := bstep (se 1 (by rfl) ⟨8554571, by rfl⟩ : syracuseStep 11406095 = 17109143) B17109143
theorem B7604063 : Blo 2001435 7604063 := bstep (se 1 (by rfl) ⟨5703047, by rfl⟩ : syracuseStep 7604063 = 11406095) B11406095
theorem B5069375 : Blo 2001435 5069375 := bstep (se 1 (by rfl) ⟨3802031, by rfl⟩ : syracuseStep 5069375 = 7604063) B7604063
theorem B3379583 : Blo 2001435 3379583 := bstep (se 1 (by rfl) ⟨2534687, by rfl⟩ : syracuseStep 3379583 = 5069375) B5069375
theorem B2253055 : Blo 2001435 2253055 := bstep (se 1 (by rfl) ⟨1689791, by rfl⟩ : syracuseStep 2253055 = 3379583) B3379583
theorem B3004073 : Blo 2001435 3004073 := bstep (se 2 (by rfl) ⟨1126527, by rfl⟩ : syracuseStep 3004073 = 2253055) B2253055
theorem B2002715 : Blo 2001435 2002715 := bstep (se 1 (by rfl) ⟨1502036, by rfl⟩ : syracuseStep 2002715 = 3004073) B3004073
theorem B4811957 : Blo 2001435 4811957 := bbase (se 5 (by rfl) ⟨225560, by rfl⟩ : syracuseStep 4811957 = 451121) (by norm_num)
theorem B3207971 : Blo 2001435 3207971 := bstep (se 1 (by rfl) ⟨2405978, by rfl⟩ : syracuseStep 3207971 = 4811957) B4811957
theorem B2138647 : Blo 2001435 2138647 := bstep (se 1 (by rfl) ⟨1603985, by rfl⟩ : syracuseStep 2138647 = 3207971) B3207971
theorem B2851529 : Blo 2001435 2851529 := bstep (se 2 (by rfl) ⟨1069323, by rfl⟩ : syracuseStep 2851529 = 2138647) B2138647
theorem B7604077 : Blo 2001435 7604077 := bstep (se 3 (by rfl) ⟨1425764, by rfl⟩ : syracuseStep 7604077 = 2851529) B2851529
theorem B10138769 : Blo 2001435 10138769 := bstep (se 2 (by rfl) ⟨3802038, by rfl⟩ : syracuseStep 10138769 = 7604077) B7604077
theorem B6759179 : Blo 2001435 6759179 := bstep (se 1 (by rfl) ⟨5069384, by rfl⟩ : syracuseStep 6759179 = 10138769) B10138769
theorem B4506119 : Blo 2001435 4506119 := bstep (se 1 (by rfl) ⟨3379589, by rfl⟩ : syracuseStep 4506119 = 6759179) B6759179
theorem B3004079 : Blo 2001435 3004079 := bstep (se 1 (by rfl) ⟨2253059, by rfl⟩ : syracuseStep 3004079 = 4506119) B4506119
theorem B2002719 : Blo 2001435 2002719 := bstep (se 1 (by rfl) ⟨1502039, by rfl⟩ : syracuseStep 2002719 = 3004079) B3004079
theorem B3004085 : Blo 2001435 3004085 := bbase (se 5 (by rfl) ⟨140816, by rfl⟩ : syracuseStep 3004085 = 281633) (by norm_num)
theorem B2002723 : Blo 2001435 2002723 := bstep (se 1 (by rfl) ⟨1502042, by rfl⟩ : syracuseStep 2002723 = 3004085) B3004085
theorem B5069405 : Blo 2001435 5069405 := bbase (se 3 (by rfl) ⟨950513, by rfl⟩ : syracuseStep 5069405 = 1901027) (by norm_num)
theorem B3379603 : Blo 2001435 3379603 := bstep (se 1 (by rfl) ⟨2534702, by rfl⟩ : syracuseStep 3379603 = 5069405) B5069405
theorem B4506137 : Blo 2001435 4506137 := bstep (se 2 (by rfl) ⟨1689801, by rfl⟩ : syracuseStep 4506137 = 3379603) B3379603
theorem B3004091 : Blo 2001435 3004091 := bstep (se 1 (by rfl) ⟨2253068, by rfl⟩ : syracuseStep 3004091 = 4506137) B4506137
theorem B2002727 : Blo 2001435 2002727 := bstep (se 1 (by rfl) ⟨1502045, by rfl⟩ : syracuseStep 2002727 = 3004091) B3004091
theorem B2253073 : Blo 2001435 2253073 := bbase (se 2 (by rfl) ⟨844902, by rfl⟩ : syracuseStep 2253073 = 1689805) (by norm_num)
theorem B3004097 : Blo 2001435 3004097 := bstep (se 2 (by rfl) ⟨1126536, by rfl⟩ : syracuseStep 3004097 = 2253073) B2253073
theorem B2002731 : Blo 2001435 2002731 := bstep (se 1 (by rfl) ⟨1502048, by rfl⟩ : syracuseStep 2002731 = 3004097) B3004097
theorem B3802069 : Blo 2001435 3802069 := bbase (se 7 (by rfl) ⟨44555, by rfl⟩ : syracuseStep 3802069 = 89111) (by norm_num)
theorem B5069425 : Blo 2001435 5069425 := bstep (se 2 (by rfl) ⟨1901034, by rfl⟩ : syracuseStep 5069425 = 3802069) B3802069
theorem B6759233 : Blo 2001435 6759233 := bstep (se 2 (by rfl) ⟨2534712, by rfl⟩ : syracuseStep 6759233 = 5069425) B5069425
theorem B4506155 : Blo 2001435 4506155 := bstep (se 1 (by rfl) ⟨3379616, by rfl⟩ : syracuseStep 4506155 = 6759233) B6759233
theorem B3004103 : Blo 2001435 3004103 := bstep (se 1 (by rfl) ⟨2253077, by rfl⟩ : syracuseStep 3004103 = 4506155) B4506155
theorem B2002735 : Blo 2001435 2002735 := bstep (se 1 (by rfl) ⟨1502051, by rfl⟩ : syracuseStep 2002735 = 3004103) B3004103
theorem B3004109 : Blo 2001435 3004109 := bbase (se 3 (by rfl) ⟨563270, by rfl⟩ : syracuseStep 3004109 = 1126541) (by norm_num)
theorem B2002739 : Blo 2001435 2002739 := bstep (se 1 (by rfl) ⟨1502054, by rfl⟩ : syracuseStep 2002739 = 3004109) B3004109
theorem B4506173 : Blo 2001435 4506173 := bbase (se 3 (by rfl) ⟨844907, by rfl⟩ : syracuseStep 4506173 = 1689815) (by norm_num)
theorem B3004115 : Blo 2001435 3004115 := bstep (se 1 (by rfl) ⟨2253086, by rfl⟩ : syracuseStep 3004115 = 4506173) B4506173
theorem B2002743 : Blo 2001435 2002743 := bstep (se 1 (by rfl) ⟨1502057, by rfl⟩ : syracuseStep 2002743 = 3004115) B3004115
theorem B3379637 : Blo 2001435 3379637 := bbase (se 5 (by rfl) ⟨158420, by rfl⟩ : syracuseStep 3379637 = 316841) (by norm_num)
theorem B2253091 : Blo 2001435 2253091 := bstep (se 1 (by rfl) ⟨1689818, by rfl⟩ : syracuseStep 2253091 = 3379637) B3379637
theorem B3004121 : Blo 2001435 3004121 := bstep (se 2 (by rfl) ⟨1126545, by rfl⟩ : syracuseStep 3004121 = 2253091) B2253091
theorem B2002747 : Blo 2001435 2002747 := bstep (se 1 (by rfl) ⟨1502060, by rfl⟩ : syracuseStep 2002747 = 3004121) B3004121
theorem B2138681 : Blo 2001435 2138681 := bbase (se 2 (by rfl) ⟨802005, by rfl⟩ : syracuseStep 2138681 = 1604011) (by norm_num)
theorem B5703149 : Blo 2001435 5703149 := bstep (se 3 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 5703149 = 2138681) B2138681
theorem B15208397 : Blo 2001435 15208397 := bstep (se 3 (by rfl) ⟨2851574, by rfl⟩ : syracuseStep 15208397 = 5703149) B5703149
theorem B10138931 : Blo 2001435 10138931 := bstep (se 1 (by rfl) ⟨7604198, by rfl⟩ : syracuseStep 10138931 = 15208397) B15208397
theorem B6759287 : Blo 2001435 6759287 := bstep (se 1 (by rfl) ⟨5069465, by rfl⟩ : syracuseStep 6759287 = 10138931) B10138931
theorem B4506191 : Blo 2001435 4506191 := bstep (se 1 (by rfl) ⟨3379643, by rfl⟩ : syracuseStep 4506191 = 6759287) B6759287
theorem B3004127 : Blo 2001435 3004127 := bstep (se 1 (by rfl) ⟨2253095, by rfl⟩ : syracuseStep 3004127 = 4506191) B4506191
theorem B2002751 : Blo 2001435 2002751 := bstep (se 1 (by rfl) ⟨1502063, by rfl⟩ : syracuseStep 2002751 = 3004127) B3004127
theorem B3004133 : Blo 2001435 3004133 := bbase (se 4 (by rfl) ⟨281637, by rfl⟩ : syracuseStep 3004133 = 563275) (by norm_num)
theorem B2002755 : Blo 2001435 2002755 := bstep (se 1 (by rfl) ⟨1502066, by rfl⟩ : syracuseStep 2002755 = 3004133) B3004133
theorem B5703173 : Blo 2001435 5703173 := bbase (se 4 (by rfl) ⟨534672, by rfl⟩ : syracuseStep 5703173 = 1069345) (by norm_num)
theorem B3802115 : Blo 2001435 3802115 := bstep (se 1 (by rfl) ⟨2851586, by rfl⟩ : syracuseStep 3802115 = 5703173) B5703173
theorem B2534743 : Blo 2001435 2534743 := bstep (se 1 (by rfl) ⟨1901057, by rfl⟩ : syracuseStep 2534743 = 3802115) B3802115
theorem B3379657 : Blo 2001435 3379657 := bstep (se 2 (by rfl) ⟨1267371, by rfl⟩ : syracuseStep 3379657 = 2534743) B2534743
theorem B4506209 : Blo 2001435 4506209 := bstep (se 2 (by rfl) ⟨1689828, by rfl⟩ : syracuseStep 4506209 = 3379657) B3379657
theorem B3004139 : Blo 2001435 3004139 := bstep (se 1 (by rfl) ⟨2253104, by rfl⟩ : syracuseStep 3004139 = 4506209) B4506209
theorem B2002759 : Blo 2001435 2002759 := bstep (se 1 (by rfl) ⟨1502069, by rfl⟩ : syracuseStep 2002759 = 3004139) B3004139
theorem B2253109 : Blo 2001435 2253109 := bbase (se 5 (by rfl) ⟨105614, by rfl⟩ : syracuseStep 2253109 = 211229) (by norm_num)
theorem B3004145 : Blo 2001435 3004145 := bstep (se 2 (by rfl) ⟨1126554, by rfl⟩ : syracuseStep 3004145 = 2253109) B2253109
theorem B2002763 : Blo 2001435 2002763 := bstep (se 1 (by rfl) ⟨1502072, by rfl⟩ : syracuseStep 2002763 = 3004145) B3004145
theorem B2534753 : Blo 2001435 2534753 := bbase (se 2 (by rfl) ⟨950532, by rfl⟩ : syracuseStep 2534753 = 1901065) (by norm_num)
theorem B6759341 : Blo 2001435 6759341 := bstep (se 3 (by rfl) ⟨1267376, by rfl⟩ : syracuseStep 6759341 = 2534753) B2534753
theorem B4506227 : Blo 2001435 4506227 := bstep (se 1 (by rfl) ⟨3379670, by rfl⟩ : syracuseStep 4506227 = 6759341) B6759341
theorem B3004151 : Blo 2001435 3004151 := bstep (se 1 (by rfl) ⟨2253113, by rfl⟩ : syracuseStep 3004151 = 4506227) B4506227
theorem B2002767 : Blo 2001435 2002767 := bstep (se 1 (by rfl) ⟨1502075, by rfl⟩ : syracuseStep 2002767 = 3004151) B3004151
theorem B3004157 : Blo 2001435 3004157 := bbase (se 3 (by rfl) ⟨563279, by rfl⟩ : syracuseStep 3004157 = 1126559) (by norm_num)
theorem B2002771 : Blo 2001435 2002771 := bstep (se 1 (by rfl) ⟨1502078, by rfl⟩ : syracuseStep 2002771 = 3004157) B3004157
theorem B4506245 : Blo 2001435 4506245 := bbase (se 4 (by rfl) ⟨422460, by rfl⟩ : syracuseStep 4506245 = 844921) (by norm_num)
theorem B3004163 : Blo 2001435 3004163 := bstep (se 1 (by rfl) ⟨2253122, by rfl⟩ : syracuseStep 3004163 = 4506245) B4506245
theorem B2002775 : Blo 2001435 2002775 := bstep (se 1 (by rfl) ⟨1502081, by rfl⟩ : syracuseStep 2002775 = 3004163) B3004163
theorem B2283869 : Blo 2001435 2283869 := bbase (se 3 (by rfl) ⟨428225, by rfl⟩ : syracuseStep 2283869 = 856451) (by norm_num)
theorem B6090317 : Blo 2001435 6090317 := bstep (se 3 (by rfl) ⟨1141934, by rfl⟩ : syracuseStep 6090317 = 2283869) B2283869
theorem B4060211 : Blo 2001435 4060211 := bstep (se 1 (by rfl) ⟨3045158, by rfl⟩ : syracuseStep 4060211 = 6090317) B6090317
theorem B10827229 : Blo 2001435 10827229 := bstep (se 3 (by rfl) ⟨2030105, by rfl⟩ : syracuseStep 10827229 = 4060211) B4060211
theorem B14436305 : Blo 2001435 14436305 := bstep (se 2 (by rfl) ⟨5413614, by rfl⟩ : syracuseStep 14436305 = 10827229) B10827229
theorem B9624203 : Blo 2001435 9624203 := bstep (se 1 (by rfl) ⟨7218152, by rfl⟩ : syracuseStep 9624203 = 14436305) B14436305
theorem B6416135 : Blo 2001435 6416135 := bstep (se 1 (by rfl) ⟨4812101, by rfl⟩ : syracuseStep 6416135 = 9624203) B9624203
theorem B4277423 : Blo 2001435 4277423 := bstep (se 1 (by rfl) ⟨3208067, by rfl⟩ : syracuseStep 4277423 = 6416135) B6416135
theorem B2851615 : Blo 2001435 2851615 := bstep (se 1 (by rfl) ⟨2138711, by rfl⟩ : syracuseStep 2851615 = 4277423) B4277423
theorem B3802153 : Blo 2001435 3802153 := bstep (se 2 (by rfl) ⟨1425807, by rfl⟩ : syracuseStep 3802153 = 2851615) B2851615
theorem B5069537 : Blo 2001435 5069537 := bstep (se 2 (by rfl) ⟨1901076, by rfl⟩ : syracuseStep 5069537 = 3802153) B3802153
theorem B3379691 : Blo 2001435 3379691 := bstep (se 1 (by rfl) ⟨2534768, by rfl⟩ : syracuseStep 3379691 = 5069537) B5069537
theorem B2253127 : Blo 2001435 2253127 := bstep (se 1 (by rfl) ⟨1689845, by rfl⟩ : syracuseStep 2253127 = 3379691) B3379691
theorem B3004169 : Blo 2001435 3004169 := bstep (se 2 (by rfl) ⟨1126563, by rfl⟩ : syracuseStep 3004169 = 2253127) B2253127
theorem B2002779 : Blo 2001435 2002779 := bstep (se 1 (by rfl) ⟨1502084, by rfl⟩ : syracuseStep 2002779 = 3004169) B3004169
theorem B10139093 : Blo 2001435 10139093 := bbase (se 7 (by rfl) ⟨118817, by rfl⟩ : syracuseStep 10139093 = 237635) (by norm_num)
theorem B6759395 : Blo 2001435 6759395 := bstep (se 1 (by rfl) ⟨5069546, by rfl⟩ : syracuseStep 6759395 = 10139093) B10139093
theorem B4506263 : Blo 2001435 4506263 := bstep (se 1 (by rfl) ⟨3379697, by rfl⟩ : syracuseStep 4506263 = 6759395) B6759395
theorem B3004175 : Blo 2001435 3004175 := bstep (se 1 (by rfl) ⟨2253131, by rfl⟩ : syracuseStep 3004175 = 4506263) B4506263
theorem B2002783 : Blo 2001435 2002783 := bstep (se 1 (by rfl) ⟨1502087, by rfl⟩ : syracuseStep 2002783 = 3004175) B3004175
theorem B3004181 : Blo 2001435 3004181 := bbase (se 6 (by rfl) ⟨70410, by rfl⟩ : syracuseStep 3004181 = 140821) (by norm_num)
theorem B2002787 : Blo 2001435 2002787 := bstep (se 1 (by rfl) ⟨1502090, by rfl⟩ : syracuseStep 2002787 = 3004181) B3004181
theorem B2197481 : Blo 2001435 2197481 := bbase (se 2 (by rfl) ⟨824055, by rfl⟩ : syracuseStep 2197481 = 1648111) (by norm_num)
theorem B23439797 : Blo 2001435 23439797 := bstep (se 5 (by rfl) ⟨1098740, by rfl⟩ : syracuseStep 23439797 = 2197481) B2197481
theorem B15626531 : Blo 2001435 15626531 := bstep (se 1 (by rfl) ⟨11719898, by rfl⟩ : syracuseStep 15626531 = 23439797) B23439797
theorem B41670749 : Blo 2001435 41670749 := bstep (se 3 (by rfl) ⟨7813265, by rfl⟩ : syracuseStep 41670749 = 15626531) B15626531
theorem B27780499 : Blo 2001435 27780499 := bstep (se 1 (by rfl) ⟨20835374, by rfl⟩ : syracuseStep 27780499 = 41670749) B41670749
theorem B37040665 : Blo 2001435 37040665 := bstep (se 2 (by rfl) ⟨13890249, by rfl⟩ : syracuseStep 37040665 = 27780499) B27780499
theorem B49387553 : Blo 2001435 49387553 := bstep (se 2 (by rfl) ⟨18520332, by rfl⟩ : syracuseStep 49387553 = 37040665) B37040665
theorem B32925035 : Blo 2001435 32925035 := bstep (se 1 (by rfl) ⟨24693776, by rfl⟩ : syracuseStep 32925035 = 49387553) B49387553
theorem B21950023 : Blo 2001435 21950023 := bstep (se 1 (by rfl) ⟨16462517, by rfl⟩ : syracuseStep 21950023 = 32925035) B32925035
theorem B29266697 : Blo 2001435 29266697 := bstep (se 2 (by rfl) ⟨10975011, by rfl⟩ : syracuseStep 29266697 = 21950023) B21950023
theorem B19511131 : Blo 2001435 19511131 := bstep (se 1 (by rfl) ⟨14633348, by rfl⟩ : syracuseStep 19511131 = 29266697) B29266697
theorem B26014841 : Blo 2001435 26014841 := bstep (se 2 (by rfl) ⟨9755565, by rfl⟩ : syracuseStep 26014841 = 19511131) B19511131
theorem B17343227 : Blo 2001435 17343227 := bstep (se 1 (by rfl) ⟨13007420, by rfl⟩ : syracuseStep 17343227 = 26014841) B26014841
theorem B11562151 : Blo 2001435 11562151 := bstep (se 1 (by rfl) ⟨8671613, by rfl⟩ : syracuseStep 11562151 = 17343227) B17343227
theorem B15416201 : Blo 2001435 15416201 := bstep (se 2 (by rfl) ⟨5781075, by rfl⟩ : syracuseStep 15416201 = 11562151) B11562151
theorem B41109869 : Blo 2001435 41109869 := bstep (se 3 (by rfl) ⟨7708100, by rfl⟩ : syracuseStep 41109869 = 15416201) B15416201
theorem B27406579 : Blo 2001435 27406579 := bstep (se 1 (by rfl) ⟨20554934, by rfl⟩ : syracuseStep 27406579 = 41109869) B41109869
theorem B36542105 : Blo 2001435 36542105 := bstep (se 2 (by rfl) ⟨13703289, by rfl⟩ : syracuseStep 36542105 = 27406579) B27406579
theorem B24361403 : Blo 2001435 24361403 := bstep (se 1 (by rfl) ⟨18271052, by rfl⟩ : syracuseStep 24361403 = 36542105) B36542105
theorem B64963741 : Blo 2001435 64963741 := bstep (se 3 (by rfl) ⟨12180701, by rfl⟩ : syracuseStep 64963741 = 24361403) B24361403
theorem B86618321 : Blo 2001435 86618321 := bstep (se 2 (by rfl) ⟨32481870, by rfl⟩ : syracuseStep 86618321 = 64963741) B64963741
theorem B57745547 : Blo 2001435 57745547 := bstep (se 1 (by rfl) ⟨43309160, by rfl⟩ : syracuseStep 57745547 = 86618321) B86618321
theorem B38497031 : Blo 2001435 38497031 := bstep (se 1 (by rfl) ⟨28872773, by rfl⟩ : syracuseStep 38497031 = 57745547) B57745547
theorem B25664687 : Blo 2001435 25664687 := bstep (se 1 (by rfl) ⟨19248515, by rfl⟩ : syracuseStep 25664687 = 38497031) B38497031
theorem B17109791 : Blo 2001435 17109791 := bstep (se 1 (by rfl) ⟨12832343, by rfl⟩ : syracuseStep 17109791 = 25664687) B25664687
theorem B11406527 : Blo 2001435 11406527 := bstep (se 1 (by rfl) ⟨8554895, by rfl⟩ : syracuseStep 11406527 = 17109791) B17109791
theorem B7604351 : Blo 2001435 7604351 := bstep (se 1 (by rfl) ⟨5703263, by rfl⟩ : syracuseStep 7604351 = 11406527) B11406527
theorem B5069567 : Blo 2001435 5069567 := bstep (se 1 (by rfl) ⟨3802175, by rfl⟩ : syracuseStep 5069567 = 7604351) B7604351
theorem B3379711 : Blo 2001435 3379711 := bstep (se 1 (by rfl) ⟨2534783, by rfl⟩ : syracuseStep 3379711 = 5069567) B5069567
theorem B4506281 : Blo 2001435 4506281 := bstep (se 2 (by rfl) ⟨1689855, by rfl⟩ : syracuseStep 4506281 = 3379711) B3379711
theorem B3004187 : Blo 2001435 3004187 := bstep (se 1 (by rfl) ⟨2253140, by rfl⟩ : syracuseStep 3004187 = 4506281) B4506281
theorem B2002791 : Blo 2001435 2002791 := bstep (se 1 (by rfl) ⟨1502093, by rfl⟩ : syracuseStep 2002791 = 3004187) B3004187
theorem B2253145 : Blo 2001435 2253145 := bbase (se 2 (by rfl) ⟨844929, by rfl⟩ : syracuseStep 2253145 = 1689859) (by norm_num)
theorem B3004193 : Blo 2001435 3004193 := bstep (se 2 (by rfl) ⟨1126572, by rfl⟩ : syracuseStep 3004193 = 2253145) B2253145
theorem B2002795 : Blo 2001435 2002795 := bstep (se 1 (by rfl) ⟨1502096, by rfl⟩ : syracuseStep 2002795 = 3004193) B3004193
theorem B4812149 : Blo 2001435 4812149 := bbase (se 5 (by rfl) ⟨225569, by rfl⟩ : syracuseStep 4812149 = 451139) (by norm_num)
theorem B3208099 : Blo 2001435 3208099 := bstep (se 1 (by rfl) ⟨2406074, by rfl⟩ : syracuseStep 3208099 = 4812149) B4812149
theorem B4277465 : Blo 2001435 4277465 := bstep (se 2 (by rfl) ⟨1604049, by rfl⟩ : syracuseStep 4277465 = 3208099) B3208099
theorem B2851643 : Blo 2001435 2851643 := bstep (se 1 (by rfl) ⟨2138732, by rfl⟩ : syracuseStep 2851643 = 4277465) B4277465
theorem B7604381 : Blo 2001435 7604381 := bstep (se 3 (by rfl) ⟨1425821, by rfl⟩ : syracuseStep 7604381 = 2851643) B2851643
theorem B5069587 : Blo 2001435 5069587 := bstep (se 1 (by rfl) ⟨3802190, by rfl⟩ : syracuseStep 5069587 = 7604381) B7604381
theorem B6759449 : Blo 2001435 6759449 := bstep (se 2 (by rfl) ⟨2534793, by rfl⟩ : syracuseStep 6759449 = 5069587) B5069587
theorem B4506299 : Blo 2001435 4506299 := bstep (se 1 (by rfl) ⟨3379724, by rfl⟩ : syracuseStep 4506299 = 6759449) B6759449
theorem B3004199 : Blo 2001435 3004199 := bstep (se 1 (by rfl) ⟨2253149, by rfl⟩ : syracuseStep 3004199 = 4506299) B4506299
theorem B2002799 : Blo 2001435 2002799 := bstep (se 1 (by rfl) ⟨1502099, by rfl⟩ : syracuseStep 2002799 = 3004199) B3004199
theorem B3004205 : Blo 2001435 3004205 := bbase (se 3 (by rfl) ⟨563288, by rfl⟩ : syracuseStep 3004205 = 1126577) (by norm_num)
theorem B2002803 : Blo 2001435 2002803 := bstep (se 1 (by rfl) ⟨1502102, by rfl⟩ : syracuseStep 2002803 = 3004205) B3004205
theorem B4506317 : Blo 2001435 4506317 := bbase (se 3 (by rfl) ⟨844934, by rfl⟩ : syracuseStep 4506317 = 1689869) (by norm_num)
theorem B3004211 : Blo 2001435 3004211 := bstep (se 1 (by rfl) ⟨2253158, by rfl⟩ : syracuseStep 3004211 = 4506317) B4506317
theorem B2002807 : Blo 2001435 2002807 := bstep (se 1 (by rfl) ⟨1502105, by rfl⟩ : syracuseStep 2002807 = 3004211) B3004211
theorem B2534809 : Blo 2001435 2534809 := bbase (se 2 (by rfl) ⟨950553, by rfl⟩ : syracuseStep 2534809 = 1901107) (by norm_num)
theorem B3379745 : Blo 2001435 3379745 := bstep (se 2 (by rfl) ⟨1267404, by rfl⟩ : syracuseStep 3379745 = 2534809) B2534809
theorem B2253163 : Blo 2001435 2253163 := bstep (se 1 (by rfl) ⟨1689872, by rfl⟩ : syracuseStep 2253163 = 3379745) B3379745
theorem B3004217 : Blo 2001435 3004217 := bstep (se 2 (by rfl) ⟨1126581, by rfl⟩ : syracuseStep 3004217 = 2253163) B2253163
theorem B2002811 : Blo 2001435 2002811 := bstep (se 1 (by rfl) ⟨1502108, by rfl⟩ : syracuseStep 2002811 = 3004217) B3004217
theorem B8554997 : Blo 2001435 8554997 := bbase (se 5 (by rfl) ⟨401015, by rfl⟩ : syracuseStep 8554997 = 802031) (by norm_num)
theorem B22813325 : Blo 2001435 22813325 := bstep (se 3 (by rfl) ⟨4277498, by rfl⟩ : syracuseStep 22813325 = 8554997) B8554997
theorem B15208883 : Blo 2001435 15208883 := bstep (se 1 (by rfl) ⟨11406662, by rfl⟩ : syracuseStep 15208883 = 22813325) B22813325
theorem B10139255 : Blo 2001435 10139255 := bstep (se 1 (by rfl) ⟨7604441, by rfl⟩ : syracuseStep 10139255 = 15208883) B15208883
theorem B6759503 : Blo 2001435 6759503 := bstep (se 1 (by rfl) ⟨5069627, by rfl⟩ : syracuseStep 6759503 = 10139255) B10139255
theorem B4506335 : Blo 2001435 4506335 := bstep (se 1 (by rfl) ⟨3379751, by rfl⟩ : syracuseStep 4506335 = 6759503) B6759503
theorem B3004223 : Blo 2001435 3004223 := bstep (se 1 (by rfl) ⟨2253167, by rfl⟩ : syracuseStep 3004223 = 4506335) B4506335
theorem B2002815 : Blo 2001435 2002815 := bstep (se 1 (by rfl) ⟨1502111, by rfl⟩ : syracuseStep 2002815 = 3004223) B3004223
theorem B3004229 : Blo 2001435 3004229 := bbase (se 4 (by rfl) ⟨281646, by rfl⟩ : syracuseStep 3004229 = 563293) (by norm_num)
theorem B2002819 : Blo 2001435 2002819 := bstep (se 1 (by rfl) ⟨1502114, by rfl⟩ : syracuseStep 2002819 = 3004229) B3004229
theorem B3379765 : Blo 2001435 3379765 := bbase (se 5 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 3379765 = 316853) (by norm_num)
theorem B4506353 : Blo 2001435 4506353 := bstep (se 2 (by rfl) ⟨1689882, by rfl⟩ : syracuseStep 4506353 = 3379765) B3379765
theorem B3004235 : Blo 2001435 3004235 := bstep (se 1 (by rfl) ⟨2253176, by rfl⟩ : syracuseStep 3004235 = 4506353) B4506353
theorem B2002823 : Blo 2001435 2002823 := bstep (se 1 (by rfl) ⟨1502117, by rfl⟩ : syracuseStep 2002823 = 3004235) B3004235
theorem B2253181 : Blo 2001435 2253181 := bbase (se 3 (by rfl) ⟨422471, by rfl⟩ : syracuseStep 2253181 = 844943) (by norm_num)
theorem B3004241 : Blo 2001435 3004241 := bstep (se 2 (by rfl) ⟨1126590, by rfl⟩ : syracuseStep 3004241 = 2253181) B2253181
theorem B2002827 : Blo 2001435 2002827 := bstep (se 1 (by rfl) ⟨1502120, by rfl⟩ : syracuseStep 2002827 = 3004241) B3004241
theorem B6759557 : Blo 2001435 6759557 := bbase (se 4 (by rfl) ⟨633708, by rfl⟩ : syracuseStep 6759557 = 1267417) (by norm_num)
theorem B4506371 : Blo 2001435 4506371 := bstep (se 1 (by rfl) ⟨3379778, by rfl⟩ : syracuseStep 4506371 = 6759557) B6759557
theorem B3004247 : Blo 2001435 3004247 := bstep (se 1 (by rfl) ⟨2253185, by rfl⟩ : syracuseStep 3004247 = 4506371) B4506371
theorem B2002831 : Blo 2001435 2002831 := bstep (se 1 (by rfl) ⟨1502123, by rfl⟩ : syracuseStep 2002831 = 3004247) B3004247
theorem B3004253 : Blo 2001435 3004253 := bbase (se 3 (by rfl) ⟨563297, by rfl⟩ : syracuseStep 3004253 = 1126595) (by norm_num)
theorem B2002835 : Blo 2001435 2002835 := bstep (se 1 (by rfl) ⟨1502126, by rfl⟩ : syracuseStep 2002835 = 3004253) B3004253
theorem B4506389 : Blo 2001435 4506389 := bbase (se 6 (by rfl) ⟨105618, by rfl⟩ : syracuseStep 4506389 = 211237) (by norm_num)
theorem B3004259 : Blo 2001435 3004259 := bstep (se 1 (by rfl) ⟨2253194, by rfl⟩ : syracuseStep 3004259 = 4506389) B4506389
theorem B2002839 : Blo 2001435 2002839 := bstep (se 1 (by rfl) ⟨1502129, by rfl⟩ : syracuseStep 2002839 = 3004259) B3004259
theorem B7604549 : Blo 2001435 7604549 := bbase (se 4 (by rfl) ⟨712926, by rfl⟩ : syracuseStep 7604549 = 1425853) (by norm_num)
theorem B5069699 : Blo 2001435 5069699 := bstep (se 1 (by rfl) ⟨3802274, by rfl⟩ : syracuseStep 5069699 = 7604549) B7604549
theorem B3379799 : Blo 2001435 3379799 := bstep (se 1 (by rfl) ⟨2534849, by rfl⟩ : syracuseStep 3379799 = 5069699) B5069699
theorem B2253199 : Blo 2001435 2253199 := bstep (se 1 (by rfl) ⟨1689899, by rfl⟩ : syracuseStep 2253199 = 3379799) B3379799
theorem B3004265 : Blo 2001435 3004265 := bstep (se 2 (by rfl) ⟨1126599, by rfl⟩ : syracuseStep 3004265 = 2253199) B2253199
theorem B2002843 : Blo 2001435 2002843 := bstep (se 1 (by rfl) ⟨1502132, by rfl⟩ : syracuseStep 2002843 = 3004265) B3004265
theorem B6173621 : Blo 2001435 6173621 := bbase (se 5 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 6173621 = 578777) (by norm_num)
theorem B4115747 : Blo 2001435 4115747 := bstep (se 1 (by rfl) ⟨3086810, by rfl⟩ : syracuseStep 4115747 = 6173621) B6173621
theorem B2743831 : Blo 2001435 2743831 := bstep (se 1 (by rfl) ⟨2057873, by rfl⟩ : syracuseStep 2743831 = 4115747) B4115747
theorem B3658441 : Blo 2001435 3658441 := bstep (se 2 (by rfl) ⟨1371915, by rfl⟩ : syracuseStep 3658441 = 2743831) B2743831
theorem B4877921 : Blo 2001435 4877921 := bstep (se 2 (by rfl) ⟨1829220, by rfl⟩ : syracuseStep 4877921 = 3658441) B3658441
theorem B13007789 : Blo 2001435 13007789 := bstep (se 3 (by rfl) ⟨2438960, by rfl⟩ : syracuseStep 13007789 = 4877921) B4877921
theorem B8671859 : Blo 2001435 8671859 := bstep (se 1 (by rfl) ⟨6503894, by rfl⟩ : syracuseStep 8671859 = 13007789) B13007789
theorem B5781239 : Blo 2001435 5781239 := bstep (se 1 (by rfl) ⟨4335929, by rfl⟩ : syracuseStep 5781239 = 8671859) B8671859
theorem B3854159 : Blo 2001435 3854159 := bstep (se 1 (by rfl) ⟨2890619, by rfl⟩ : syracuseStep 3854159 = 5781239) B5781239
theorem B2569439 : Blo 2001435 2569439 := bstep (se 1 (by rfl) ⟨1927079, by rfl⟩ : syracuseStep 2569439 = 3854159) B3854159
theorem B6851837 : Blo 2001435 6851837 := bstep (se 3 (by rfl) ⟨1284719, by rfl⟩ : syracuseStep 6851837 = 2569439) B2569439
theorem B18271565 : Blo 2001435 18271565 := bstep (se 3 (by rfl) ⟨3425918, by rfl⟩ : syracuseStep 18271565 = 6851837) B6851837
theorem B12181043 : Blo 2001435 12181043 := bstep (se 1 (by rfl) ⟨9135782, by rfl⟩ : syracuseStep 12181043 = 18271565) B18271565
theorem B32482781 : Blo 2001435 32482781 := bstep (se 3 (by rfl) ⟨6090521, by rfl⟩ : syracuseStep 32482781 = 12181043) B12181043
theorem B21655187 : Blo 2001435 21655187 := bstep (se 1 (by rfl) ⟨16241390, by rfl⟩ : syracuseStep 21655187 = 32482781) B32482781
theorem B14436791 : Blo 2001435 14436791 := bstep (se 1 (by rfl) ⟨10827593, by rfl⟩ : syracuseStep 14436791 = 21655187) B21655187
theorem B9624527 : Blo 2001435 9624527 := bstep (se 1 (by rfl) ⟨7218395, by rfl⟩ : syracuseStep 9624527 = 14436791) B14436791
theorem B6416351 : Blo 2001435 6416351 := bstep (se 1 (by rfl) ⟨4812263, by rfl⟩ : syracuseStep 6416351 = 9624527) B9624527
theorem B4277567 : Blo 2001435 4277567 := bstep (se 1 (by rfl) ⟨3208175, by rfl⟩ : syracuseStep 4277567 = 6416351) B6416351
theorem B11406845 : Blo 2001435 11406845 := bstep (se 3 (by rfl) ⟨2138783, by rfl⟩ : syracuseStep 11406845 = 4277567) B4277567
theorem B7604563 : Blo 2001435 7604563 := bstep (se 1 (by rfl) ⟨5703422, by rfl⟩ : syracuseStep 7604563 = 11406845) B11406845
theorem B10139417 : Blo 2001435 10139417 := bstep (se 2 (by rfl) ⟨3802281, by rfl⟩ : syracuseStep 10139417 = 7604563) B7604563
theorem B6759611 : Blo 2001435 6759611 := bstep (se 1 (by rfl) ⟨5069708, by rfl⟩ : syracuseStep 6759611 = 10139417) B10139417
theorem B4506407 : Blo 2001435 4506407 := bstep (se 1 (by rfl) ⟨3379805, by rfl⟩ : syracuseStep 4506407 = 6759611) B6759611
theorem B3004271 : Blo 2001435 3004271 := bstep (se 1 (by rfl) ⟨2253203, by rfl⟩ : syracuseStep 3004271 = 4506407) B4506407
theorem B2002847 : Blo 2001435 2002847 := bstep (se 1 (by rfl) ⟨1502135, by rfl⟩ : syracuseStep 2002847 = 3004271) B3004271
theorem B3004277 : Blo 2001435 3004277 := bbase (se 5 (by rfl) ⟨140825, by rfl⟩ : syracuseStep 3004277 = 281651) (by norm_num)
theorem B2002851 : Blo 2001435 2002851 := bstep (se 1 (by rfl) ⟨1502138, by rfl⟩ : syracuseStep 2002851 = 3004277) B3004277
theorem B3208189 : Blo 2001435 3208189 := bbase (se 3 (by rfl) ⟨601535, by rfl⟩ : syracuseStep 3208189 = 1203071) (by norm_num)
theorem B4277585 : Blo 2001435 4277585 := bstep (se 2 (by rfl) ⟨1604094, by rfl⟩ : syracuseStep 4277585 = 3208189) B3208189
theorem B2851723 : Blo 2001435 2851723 := bstep (se 1 (by rfl) ⟨2138792, by rfl⟩ : syracuseStep 2851723 = 4277585) B4277585
theorem B3802297 : Blo 2001435 3802297 := bstep (se 2 (by rfl) ⟨1425861, by rfl⟩ : syracuseStep 3802297 = 2851723) B2851723
theorem B5069729 : Blo 2001435 5069729 := bstep (se 2 (by rfl) ⟨1901148, by rfl⟩ : syracuseStep 5069729 = 3802297) B3802297
theorem B3379819 : Blo 2001435 3379819 := bstep (se 1 (by rfl) ⟨2534864, by rfl⟩ : syracuseStep 3379819 = 5069729) B5069729
theorem B4506425 : Blo 2001435 4506425 := bstep (se 2 (by rfl) ⟨1689909, by rfl⟩ : syracuseStep 4506425 = 3379819) B3379819
theorem B3004283 : Blo 2001435 3004283 := bstep (se 1 (by rfl) ⟨2253212, by rfl⟩ : syracuseStep 3004283 = 4506425) B4506425
theorem B2002855 : Blo 2001435 2002855 := bstep (se 1 (by rfl) ⟨1502141, by rfl⟩ : syracuseStep 2002855 = 3004283) B3004283
theorem B2253217 : Blo 2001435 2253217 := bbase (se 2 (by rfl) ⟨844956, by rfl⟩ : syracuseStep 2253217 = 1689913) (by norm_num)
theorem B3004289 : Blo 2001435 3004289 := bstep (se 2 (by rfl) ⟨1126608, by rfl⟩ : syracuseStep 3004289 = 2253217) B2253217
theorem B2002859 : Blo 2001435 2002859 := bstep (se 1 (by rfl) ⟨1502144, by rfl⟩ : syracuseStep 2002859 = 3004289) B3004289
theorem B5069749 : Blo 2001435 5069749 := bbase (se 5 (by rfl) ⟨237644, by rfl⟩ : syracuseStep 5069749 = 475289) (by norm_num)
theorem B6759665 : Blo 2001435 6759665 := bstep (se 2 (by rfl) ⟨2534874, by rfl⟩ : syracuseStep 6759665 = 5069749) B5069749
theorem B4506443 : Blo 2001435 4506443 := bstep (se 1 (by rfl) ⟨3379832, by rfl⟩ : syracuseStep 4506443 = 6759665) B6759665
theorem B3004295 : Blo 2001435 3004295 := bstep (se 1 (by rfl) ⟨2253221, by rfl⟩ : syracuseStep 3004295 = 4506443) B4506443
theorem B2002863 : Blo 2001435 2002863 := bstep (se 1 (by rfl) ⟨1502147, by rfl⟩ : syracuseStep 2002863 = 3004295) B3004295
theorem B3004301 : Blo 2001435 3004301 := bbase (se 3 (by rfl) ⟨563306, by rfl⟩ : syracuseStep 3004301 = 1126613) (by norm_num)
theorem B2002867 : Blo 2001435 2002867 := bstep (se 1 (by rfl) ⟨1502150, by rfl⟩ : syracuseStep 2002867 = 3004301) B3004301
theorem B4506461 : Blo 2001435 4506461 := bbase (se 3 (by rfl) ⟨844961, by rfl⟩ : syracuseStep 4506461 = 1689923) (by norm_num)
theorem B3004307 : Blo 2001435 3004307 := bstep (se 1 (by rfl) ⟨2253230, by rfl⟩ : syracuseStep 3004307 = 4506461) B4506461
theorem B2002871 : Blo 2001435 2002871 := bstep (se 1 (by rfl) ⟨1502153, by rfl⟩ : syracuseStep 2002871 = 3004307) B3004307
theorem B3379853 : Blo 2001435 3379853 := bbase (se 3 (by rfl) ⟨633722, by rfl⟩ : syracuseStep 3379853 = 1267445) (by norm_num)
theorem B2253235 : Blo 2001435 2253235 := bstep (se 1 (by rfl) ⟨1689926, by rfl⟩ : syracuseStep 2253235 = 3379853) B3379853
theorem B3004313 : Blo 2001435 3004313 := bstep (se 2 (by rfl) ⟨1126617, by rfl⟩ : syracuseStep 3004313 = 2253235) B2253235
theorem B2002875 : Blo 2001435 2002875 := bstep (se 1 (by rfl) ⟨1502156, by rfl⟩ : syracuseStep 2002875 = 3004313) B3004313
theorem B6416453 : Blo 2001435 6416453 := bbase (se 4 (by rfl) ⟨601542, by rfl⟩ : syracuseStep 6416453 = 1203085) (by norm_num)
theorem B17110541 : Blo 2001435 17110541 := bstep (se 3 (by rfl) ⟨3208226, by rfl⟩ : syracuseStep 17110541 = 6416453) B6416453
theorem B11407027 : Blo 2001435 11407027 := bstep (se 1 (by rfl) ⟨8555270, by rfl⟩ : syracuseStep 11407027 = 17110541) B17110541
theorem B15209369 : Blo 2001435 15209369 := bstep (se 2 (by rfl) ⟨5703513, by rfl⟩ : syracuseStep 15209369 = 11407027) B11407027
theorem B10139579 : Blo 2001435 10139579 := bstep (se 1 (by rfl) ⟨7604684, by rfl⟩ : syracuseStep 10139579 = 15209369) B15209369
theorem B6759719 : Blo 2001435 6759719 := bstep (se 1 (by rfl) ⟨5069789, by rfl⟩ : syracuseStep 6759719 = 10139579) B10139579
theorem B4506479 : Blo 2001435 4506479 := bstep (se 1 (by rfl) ⟨3379859, by rfl⟩ : syracuseStep 4506479 = 6759719) B6759719
theorem B3004319 : Blo 2001435 3004319 := bstep (se 1 (by rfl) ⟨2253239, by rfl⟩ : syracuseStep 3004319 = 4506479) B4506479
theorem B2002879 : Blo 2001435 2002879 := bstep (se 1 (by rfl) ⟨1502159, by rfl⟩ : syracuseStep 2002879 = 3004319) B3004319
theorem B3004325 : Blo 2001435 3004325 := bbase (se 4 (by rfl) ⟨281655, by rfl⟩ : syracuseStep 3004325 = 563311) (by norm_num)
theorem B2002883 : Blo 2001435 2002883 := bstep (se 1 (by rfl) ⟨1502162, by rfl⟩ : syracuseStep 2002883 = 3004325) B3004325
theorem B2534905 : Blo 2001435 2534905 := bbase (se 2 (by rfl) ⟨950589, by rfl⟩ : syracuseStep 2534905 = 1901179) (by norm_num)
theorem B3379873 : Blo 2001435 3379873 := bstep (se 2 (by rfl) ⟨1267452, by rfl⟩ : syracuseStep 3379873 = 2534905) B2534905
theorem B4506497 : Blo 2001435 4506497 := bstep (se 2 (by rfl) ⟨1689936, by rfl⟩ : syracuseStep 4506497 = 3379873) B3379873
theorem B3004331 : Blo 2001435 3004331 := bstep (se 1 (by rfl) ⟨2253248, by rfl⟩ : syracuseStep 3004331 = 4506497) B4506497
theorem B2002887 : Blo 2001435 2002887 := bstep (se 1 (by rfl) ⟨1502165, by rfl⟩ : syracuseStep 2002887 = 3004331) B3004331
theorem B2253253 : Blo 2001435 2253253 := bbase (se 4 (by rfl) ⟨211242, by rfl⟩ : syracuseStep 2253253 = 422485) (by norm_num)
theorem B3004337 : Blo 2001435 3004337 := bstep (se 2 (by rfl) ⟨1126626, by rfl⟩ : syracuseStep 3004337 = 2253253) B2253253
theorem B2002891 : Blo 2001435 2002891 := bstep (se 1 (by rfl) ⟨1502168, by rfl⟩ : syracuseStep 2002891 = 3004337) B3004337
theorem B3802373 : Blo 2001435 3802373 := bbase (se 4 (by rfl) ⟨356472, by rfl⟩ : syracuseStep 3802373 = 712945) (by norm_num)
theorem B2534915 : Blo 2001435 2534915 := bstep (se 1 (by rfl) ⟨1901186, by rfl⟩ : syracuseStep 2534915 = 3802373) B3802373
theorem B6759773 : Blo 2001435 6759773 := bstep (se 3 (by rfl) ⟨1267457, by rfl⟩ : syracuseStep 6759773 = 2534915) B2534915
theorem B4506515 : Blo 2001435 4506515 := bstep (se 1 (by rfl) ⟨3379886, by rfl⟩ : syracuseStep 4506515 = 6759773) B6759773
theorem B3004343 : Blo 2001435 3004343 := bstep (se 1 (by rfl) ⟨2253257, by rfl⟩ : syracuseStep 3004343 = 4506515) B4506515
theorem B2002895 : Blo 2001435 2002895 := bstep (se 1 (by rfl) ⟨1502171, by rfl⟩ : syracuseStep 2002895 = 3004343) B3004343
theorem B3004349 : Blo 2001435 3004349 := bbase (se 3 (by rfl) ⟨563315, by rfl⟩ : syracuseStep 3004349 = 1126631) (by norm_num)
theorem B2002899 : Blo 2001435 2002899 := bstep (se 1 (by rfl) ⟨1502174, by rfl⟩ : syracuseStep 2002899 = 3004349) B3004349
theorem B4506533 : Blo 2001435 4506533 := bbase (se 4 (by rfl) ⟨422487, by rfl⟩ : syracuseStep 4506533 = 844975) (by norm_num)
theorem B3004355 : Blo 2001435 3004355 := bstep (se 1 (by rfl) ⟨2253266, by rfl⟩ : syracuseStep 3004355 = 4506533) B4506533
theorem B2002903 : Blo 2001435 2002903 := bstep (se 1 (by rfl) ⟨1502177, by rfl⟩ : syracuseStep 2002903 = 3004355) B3004355
theorem B5069861 : Blo 2001435 5069861 := bbase (se 4 (by rfl) ⟨475299, by rfl⟩ : syracuseStep 5069861 = 950599) (by norm_num)
theorem B3379907 : Blo 2001435 3379907 := bstep (se 1 (by rfl) ⟨2534930, by rfl⟩ : syracuseStep 3379907 = 5069861) B5069861
theorem B2253271 : Blo 2001435 2253271 := bstep (se 1 (by rfl) ⟨1689953, by rfl⟩ : syracuseStep 2253271 = 3379907) B3379907
theorem B3004361 : Blo 2001435 3004361 := bstep (se 2 (by rfl) ⟨1126635, by rfl⟩ : syracuseStep 3004361 = 2253271) B2253271
theorem B2002907 : Blo 2001435 2002907 := bstep (se 1 (by rfl) ⟨1502180, by rfl⟩ : syracuseStep 2002907 = 3004361) B3004361
theorem B5703605 : Blo 2001435 5703605 := bbase (se 5 (by rfl) ⟨267356, by rfl⟩ : syracuseStep 5703605 = 534713) (by norm_num)
theorem B3802403 : Blo 2001435 3802403 := bstep (se 1 (by rfl) ⟨2851802, by rfl⟩ : syracuseStep 3802403 = 5703605) B5703605
theorem B10139741 : Blo 2001435 10139741 := bstep (se 3 (by rfl) ⟨1901201, by rfl⟩ : syracuseStep 10139741 = 3802403) B3802403
theorem B6759827 : Blo 2001435 6759827 := bstep (se 1 (by rfl) ⟨5069870, by rfl⟩ : syracuseStep 6759827 = 10139741) B10139741
theorem B4506551 : Blo 2001435 4506551 := bstep (se 1 (by rfl) ⟨3379913, by rfl⟩ : syracuseStep 4506551 = 6759827) B6759827
theorem B3004367 : Blo 2001435 3004367 := bstep (se 1 (by rfl) ⟨2253275, by rfl⟩ : syracuseStep 3004367 = 4506551) B4506551
theorem B2002911 : Blo 2001435 2002911 := bstep (se 1 (by rfl) ⟨1502183, by rfl⟩ : syracuseStep 2002911 = 3004367) B3004367
theorem B3004373 : Blo 2001435 3004373 := bbase (se 7 (by rfl) ⟨35207, by rfl⟩ : syracuseStep 3004373 = 70415) (by norm_num)
theorem B2002915 : Blo 2001435 2002915 := bstep (se 1 (by rfl) ⟨1502186, by rfl⟩ : syracuseStep 2002915 = 3004373) B3004373
theorem B7604837 : Blo 2001435 7604837 := bbase (se 4 (by rfl) ⟨712953, by rfl⟩ : syracuseStep 7604837 = 1425907) (by norm_num)
theorem B5069891 : Blo 2001435 5069891 := bstep (se 1 (by rfl) ⟨3802418, by rfl⟩ : syracuseStep 5069891 = 7604837) B7604837
theorem B3379927 : Blo 2001435 3379927 := bstep (se 1 (by rfl) ⟨2534945, by rfl⟩ : syracuseStep 3379927 = 5069891) B5069891
theorem B4506569 : Blo 2001435 4506569 := bstep (se 2 (by rfl) ⟨1689963, by rfl⟩ : syracuseStep 4506569 = 3379927) B3379927
theorem B3004379 : Blo 2001435 3004379 := bstep (se 1 (by rfl) ⟨2253284, by rfl⟩ : syracuseStep 3004379 = 4506569) B4506569
theorem B2002919 : Blo 2001435 2002919 := bstep (se 1 (by rfl) ⟨1502189, by rfl⟩ : syracuseStep 2002919 = 3004379) B3004379
theorem B2253289 : Blo 2001435 2253289 := bbase (se 2 (by rfl) ⟨844983, by rfl⟩ : syracuseStep 2253289 = 1689967) (by norm_num)
theorem B3004385 : Blo 2001435 3004385 := bstep (se 2 (by rfl) ⟨1126644, by rfl⟩ : syracuseStep 3004385 = 2253289) B2253289
theorem B2002923 : Blo 2001435 2002923 := bstep (se 1 (by rfl) ⟨1502192, by rfl⟩ : syracuseStep 2002923 = 3004385) B3004385
theorem B2138869 : Blo 2001435 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B11407301 : Blo 2001435 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B7604867 : Blo 2001435 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B5069911 : Blo 2001435 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B6759881 : Blo 2001435 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B4506587 : Blo 2001435 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B3004391 : Blo 2001435 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B2002927 : Blo 2001435 2002927 := bstep (se 1 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 2002927 = 3004391) B3004391
theorem B3004397 : Blo 2001435 3004397 := bbase (se 3 (by rfl) ⟨563324, by rfl⟩ : syracuseStep 3004397 = 1126649) (by norm_num)
theorem B2002931 : Blo 2001435 2002931 := bstep (se 1 (by rfl) ⟨1502198, by rfl⟩ : syracuseStep 2002931 = 3004397) B3004397
theorem B4506605 : Blo 2001435 4506605 := bbase (se 3 (by rfl) ⟨844988, by rfl⟩ : syracuseStep 4506605 = 1689977) (by norm_num)
theorem B3004403 : Blo 2001435 3004403 := bstep (se 1 (by rfl) ⟨2253302, by rfl⟩ : syracuseStep 3004403 = 4506605) B4506605
theorem B2002935 : Blo 2001435 2002935 := bstep (se 1 (by rfl) ⟨1502201, by rfl⟩ : syracuseStep 2002935 = 3004403) B3004403
theorem B4277765 : Blo 2001435 4277765 := bbase (se 4 (by rfl) ⟨401040, by rfl⟩ : syracuseStep 4277765 = 802081) (by norm_num)
theorem B2851843 : Blo 2001435 2851843 := bstep (se 1 (by rfl) ⟨2138882, by rfl⟩ : syracuseStep 2851843 = 4277765) B4277765
theorem B3802457 : Blo 2001435 3802457 := bstep (se 2 (by rfl) ⟨1425921, by rfl⟩ : syracuseStep 3802457 = 2851843) B2851843
theorem B2534971 : Blo 2001435 2534971 := bstep (se 1 (by rfl) ⟨1901228, by rfl⟩ : syracuseStep 2534971 = 3802457) B3802457
theorem B3379961 : Blo 2001435 3379961 := bstep (se 2 (by rfl) ⟨1267485, by rfl⟩ : syracuseStep 3379961 = 2534971) B2534971
theorem B2253307 : Blo 2001435 2253307 := bstep (se 1 (by rfl) ⟨1689980, by rfl⟩ : syracuseStep 2253307 = 3379961) B3379961
theorem B3004409 : Blo 2001435 3004409 := bstep (se 2 (by rfl) ⟨1126653, by rfl⟩ : syracuseStep 3004409 = 2253307) B2253307
theorem B2002939 : Blo 2001435 2002939 := bstep (se 1 (by rfl) ⟨1502204, by rfl⟩ : syracuseStep 2002939 = 3004409) B3004409
theorem B3086957 : Blo 2001435 3086957 := bbase (se 3 (by rfl) ⟨578804, by rfl⟩ : syracuseStep 3086957 = 1157609) (by norm_num)
theorem B2057971 : Blo 2001435 2057971 := bstep (se 1 (by rfl) ⟨1543478, by rfl⟩ : syracuseStep 2057971 = 3086957) B3086957
theorem B2743961 : Blo 2001435 2743961 := bstep (se 2 (by rfl) ⟨1028985, by rfl⟩ : syracuseStep 2743961 = 2057971) B2057971
theorem B7317229 : Blo 2001435 7317229 := bstep (se 3 (by rfl) ⟨1371980, by rfl⟩ : syracuseStep 7317229 = 2743961) B2743961
theorem B9756305 : Blo 2001435 9756305 := bstep (se 2 (by rfl) ⟨3658614, by rfl⟩ : syracuseStep 9756305 = 7317229) B7317229
theorem B6504203 : Blo 2001435 6504203 := bstep (se 1 (by rfl) ⟨4878152, by rfl⟩ : syracuseStep 6504203 = 9756305) B9756305
theorem B4336135 : Blo 2001435 4336135 := bstep (se 1 (by rfl) ⟨3252101, by rfl⟩ : syracuseStep 4336135 = 6504203) B6504203
theorem B92504213 : Blo 2001435 92504213 := bstep (se 6 (by rfl) ⟨2168067, by rfl⟩ : syracuseStep 92504213 = 4336135) B4336135
theorem B61669475 : Blo 2001435 61669475 := bstep (se 1 (by rfl) ⟨46252106, by rfl⟩ : syracuseStep 61669475 = 92504213) B92504213
theorem B41112983 : Blo 2001435 41112983 := bstep (se 1 (by rfl) ⟨30834737, by rfl⟩ : syracuseStep 41112983 = 61669475) B61669475
theorem B27408655 : Blo 2001435 27408655 := bstep (se 1 (by rfl) ⟨20556491, by rfl⟩ : syracuseStep 27408655 = 41112983) B41112983
theorem B36544873 : Blo 2001435 36544873 := bstep (se 2 (by rfl) ⟨13704327, by rfl⟩ : syracuseStep 36544873 = 27408655) B27408655
theorem B48726497 : Blo 2001435 48726497 := bstep (se 2 (by rfl) ⟨18272436, by rfl⟩ : syracuseStep 48726497 = 36544873) B36544873
theorem B32484331 : Blo 2001435 32484331 := bstep (se 1 (by rfl) ⟨24363248, by rfl⟩ : syracuseStep 32484331 = 48726497) B48726497
theorem B173249765 : Blo 2001435 173249765 := bstep (se 4 (by rfl) ⟨16242165, by rfl⟩ : syracuseStep 173249765 = 32484331) B32484331
theorem B115499843 : Blo 2001435 115499843 := bstep (se 1 (by rfl) ⟨86624882, by rfl⟩ : syracuseStep 115499843 = 173249765) B173249765
theorem B76999895 : Blo 2001435 76999895 := bstep (se 1 (by rfl) ⟨57749921, by rfl⟩ : syracuseStep 76999895 = 115499843) B115499843
theorem B51333263 : Blo 2001435 51333263 := bstep (se 1 (by rfl) ⟨38499947, by rfl⟩ : syracuseStep 51333263 = 76999895) B76999895
theorem B34222175 : Blo 2001435 34222175 := bstep (se 1 (by rfl) ⟨25666631, by rfl⟩ : syracuseStep 34222175 = 51333263) B51333263
theorem B22814783 : Blo 2001435 22814783 := bstep (se 1 (by rfl) ⟨17111087, by rfl⟩ : syracuseStep 22814783 = 34222175) B34222175
theorem B15209855 : Blo 2001435 15209855 := bstep (se 1 (by rfl) ⟨11407391, by rfl⟩ : syracuseStep 15209855 = 22814783) B22814783
theorem B10139903 : Blo 2001435 10139903 := bstep (se 1 (by rfl) ⟨7604927, by rfl⟩ : syracuseStep 10139903 = 15209855) B15209855
theorem B6759935 : Blo 2001435 6759935 := bstep (se 1 (by rfl) ⟨5069951, by rfl⟩ : syracuseStep 6759935 = 10139903) B10139903
theorem B4506623 : Blo 2001435 4506623 := bstep (se 1 (by rfl) ⟨3379967, by rfl⟩ : syracuseStep 4506623 = 6759935) B6759935
theorem B3004415 : Blo 2001435 3004415 := bstep (se 1 (by rfl) ⟨2253311, by rfl⟩ : syracuseStep 3004415 = 4506623) B4506623
theorem B2002943 : Blo 2001435 2002943 := bstep (se 1 (by rfl) ⟨1502207, by rfl⟩ : syracuseStep 2002943 = 3004415) B3004415
theorem B3004421 : Blo 2001435 3004421 := bbase (se 4 (by rfl) ⟨281664, by rfl⟩ : syracuseStep 3004421 = 563329) (by norm_num)
theorem B2002947 : Blo 2001435 2002947 := bstep (se 1 (by rfl) ⟨1502210, by rfl⟩ : syracuseStep 2002947 = 3004421) B3004421
theorem B3379981 : Blo 2001435 3379981 := bbase (se 3 (by rfl) ⟨633746, by rfl⟩ : syracuseStep 3379981 = 1267493) (by norm_num)
theorem B4506641 : Blo 2001435 4506641 := bstep (se 2 (by rfl) ⟨1689990, by rfl⟩ : syracuseStep 4506641 = 3379981) B3379981
theorem B3004427 : Blo 2001435 3004427 := bstep (se 1 (by rfl) ⟨2253320, by rfl⟩ : syracuseStep 3004427 = 4506641) B4506641
theorem B2002951 : Blo 2001435 2002951 := bstep (se 1 (by rfl) ⟨1502213, by rfl⟩ : syracuseStep 2002951 = 3004427) B3004427
theorem B2253325 : Blo 2001435 2253325 := bbase (se 3 (by rfl) ⟨422498, by rfl⟩ : syracuseStep 2253325 = 844997) (by norm_num)
theorem B3004433 : Blo 2001435 3004433 := bstep (se 2 (by rfl) ⟨1126662, by rfl⟩ : syracuseStep 3004433 = 2253325) B2253325
theorem B2002955 : Blo 2001435 2002955 := bstep (se 1 (by rfl) ⟨1502216, by rfl⟩ : syracuseStep 2002955 = 3004433) B3004433
theorem B6759989 : Blo 2001435 6759989 := bbase (se 5 (by rfl) ⟨316874, by rfl⟩ : syracuseStep 6759989 = 633749) (by norm_num)
theorem B4506659 : Blo 2001435 4506659 := bstep (se 1 (by rfl) ⟨3379994, by rfl⟩ : syracuseStep 4506659 = 6759989) B6759989
theorem B3004439 : Blo 2001435 3004439 := bstep (se 1 (by rfl) ⟨2253329, by rfl⟩ : syracuseStep 3004439 = 4506659) B4506659
theorem B2002959 : Blo 2001435 2002959 := bstep (se 1 (by rfl) ⟨1502219, by rfl⟩ : syracuseStep 2002959 = 3004439) B3004439
theorem B3004445 : Blo 2001435 3004445 := bbase (se 3 (by rfl) ⟨563333, by rfl⟩ : syracuseStep 3004445 = 1126667) (by norm_num)
theorem B2002963 : Blo 2001435 2002963 := bstep (se 1 (by rfl) ⟨1502222, by rfl⟩ : syracuseStep 2002963 = 3004445) B3004445
theorem B4506677 : Blo 2001435 4506677 := bbase (se 5 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 4506677 = 422501) (by norm_num)
theorem B3004451 : Blo 2001435 3004451 := bstep (se 1 (by rfl) ⟨2253338, by rfl⟩ : syracuseStep 3004451 = 4506677) B4506677
theorem B2002967 : Blo 2001435 2002967 := bstep (se 1 (by rfl) ⟨1502225, by rfl⟩ : syracuseStep 2002967 = 3004451) B3004451
theorem B2406281 : Blo 2001435 2406281 := bbase (se 2 (by rfl) ⟨902355, by rfl⟩ : syracuseStep 2406281 = 1804711) (by norm_num)
theorem B6416749 : Blo 2001435 6416749 := bstep (se 3 (by rfl) ⟨1203140, by rfl⟩ : syracuseStep 6416749 = 2406281) B2406281
theorem B8555665 : Blo 2001435 8555665 := bstep (se 2 (by rfl) ⟨3208374, by rfl⟩ : syracuseStep 8555665 = 6416749) B6416749
theorem B11407553 : Blo 2001435 11407553 := bstep (se 2 (by rfl) ⟨4277832, by rfl⟩ : syracuseStep 11407553 = 8555665) B8555665
theorem B7605035 : Blo 2001435 7605035 := bstep (se 1 (by rfl) ⟨5703776, by rfl⟩ : syracuseStep 7605035 = 11407553) B11407553
theorem B5070023 : Blo 2001435 5070023 := bstep (se 1 (by rfl) ⟨3802517, by rfl⟩ : syracuseStep 5070023 = 7605035) B7605035
theorem B3380015 : Blo 2001435 3380015 := bstep (se 1 (by rfl) ⟨2535011, by rfl⟩ : syracuseStep 3380015 = 5070023) B5070023
theorem B2253343 : Blo 2001435 2253343 := bstep (se 1 (by rfl) ⟨1690007, by rfl⟩ : syracuseStep 2253343 = 3380015) B3380015
theorem B3004457 : Blo 2001435 3004457 := bstep (se 2 (by rfl) ⟨1126671, by rfl⟩ : syracuseStep 3004457 = 2253343) B2253343
theorem B2002971 : Blo 2001435 2002971 := bstep (se 1 (by rfl) ⟨1502228, by rfl⟩ : syracuseStep 2002971 = 3004457) B3004457
theorem B4172165 : Blo 2001435 4172165 := bbase (se 4 (by rfl) ⟨391140, by rfl⟩ : syracuseStep 4172165 = 782281) (by norm_num)
theorem B2781443 : Blo 2001435 2781443 := bstep (se 1 (by rfl) ⟨2086082, by rfl⟩ : syracuseStep 2781443 = 4172165) B4172165
theorem B7417181 : Blo 2001435 7417181 := bstep (se 3 (by rfl) ⟨1390721, by rfl⟩ : syracuseStep 7417181 = 2781443) B2781443
theorem B19779149 : Blo 2001435 19779149 := bstep (se 3 (by rfl) ⟨3708590, by rfl⟩ : syracuseStep 19779149 = 7417181) B7417181
theorem B13186099 : Blo 2001435 13186099 := bstep (se 1 (by rfl) ⟨9889574, by rfl⟩ : syracuseStep 13186099 = 19779149) B19779149
theorem B17581465 : Blo 2001435 17581465 := bstep (se 2 (by rfl) ⟨6593049, by rfl⟩ : syracuseStep 17581465 = 13186099) B13186099
theorem B23441953 : Blo 2001435 23441953 := bstep (se 2 (by rfl) ⟨8790732, by rfl⟩ : syracuseStep 23441953 = 17581465) B17581465
theorem B31255937 : Blo 2001435 31255937 := bstep (se 2 (by rfl) ⟨11720976, by rfl⟩ : syracuseStep 31255937 = 23441953) B23441953
theorem B20837291 : Blo 2001435 20837291 := bstep (se 1 (by rfl) ⟨15627968, by rfl⟩ : syracuseStep 20837291 = 31255937) B31255937
theorem B55566109 : Blo 2001435 55566109 := bstep (se 3 (by rfl) ⟨10418645, by rfl⟩ : syracuseStep 55566109 = 20837291) B20837291
theorem B74088145 : Blo 2001435 74088145 := bstep (se 2 (by rfl) ⟨27783054, by rfl⟩ : syracuseStep 74088145 = 55566109) B55566109
theorem B98784193 : Blo 2001435 98784193 := bstep (se 2 (by rfl) ⟨37044072, by rfl⟩ : syracuseStep 98784193 = 74088145) B74088145
theorem B131712257 : Blo 2001435 131712257 := bstep (se 2 (by rfl) ⟨49392096, by rfl⟩ : syracuseStep 131712257 = 98784193) B98784193
theorem B87808171 : Blo 2001435 87808171 := bstep (se 1 (by rfl) ⟨65856128, by rfl⟩ : syracuseStep 87808171 = 131712257) B131712257
theorem B117077561 : Blo 2001435 117077561 := bstep (se 2 (by rfl) ⟨43904085, by rfl⟩ : syracuseStep 117077561 = 87808171) B87808171
theorem B78051707 : Blo 2001435 78051707 := bstep (se 1 (by rfl) ⟨58538780, by rfl⟩ : syracuseStep 78051707 = 117077561) B117077561
theorem B52034471 : Blo 2001435 52034471 := bstep (se 1 (by rfl) ⟨39025853, by rfl⟩ : syracuseStep 52034471 = 78051707) B78051707
theorem B34689647 : Blo 2001435 34689647 := bstep (se 1 (by rfl) ⟨26017235, by rfl⟩ : syracuseStep 34689647 = 52034471) B52034471
theorem B92505725 : Blo 2001435 92505725 := bstep (se 3 (by rfl) ⟨17344823, by rfl⟩ : syracuseStep 92505725 = 34689647) B34689647
theorem B61670483 : Blo 2001435 61670483 := bstep (se 1 (by rfl) ⟨46252862, by rfl⟩ : syracuseStep 61670483 = 92505725) B92505725
theorem B41113655 : Blo 2001435 41113655 := bstep (se 1 (by rfl) ⟨30835241, by rfl⟩ : syracuseStep 41113655 = 61670483) B61670483
theorem B27409103 : Blo 2001435 27409103 := bstep (se 1 (by rfl) ⟨20556827, by rfl⟩ : syracuseStep 27409103 = 41113655) B41113655
theorem B18272735 : Blo 2001435 18272735 := bstep (se 1 (by rfl) ⟨13704551, by rfl⟩ : syracuseStep 18272735 = 27409103) B27409103
theorem B12181823 : Blo 2001435 12181823 := bstep (se 1 (by rfl) ⟨9136367, by rfl⟩ : syracuseStep 12181823 = 18272735) B18272735
theorem B8121215 : Blo 2001435 8121215 := bstep (se 1 (by rfl) ⟨6090911, by rfl⟩ : syracuseStep 8121215 = 12181823) B12181823
theorem B5414143 : Blo 2001435 5414143 := bstep (se 1 (by rfl) ⟨4060607, by rfl⟩ : syracuseStep 5414143 = 8121215) B8121215
theorem B7218857 : Blo 2001435 7218857 := bstep (se 2 (by rfl) ⟨2707071, by rfl⟩ : syracuseStep 7218857 = 5414143) B5414143
theorem B4812571 : Blo 2001435 4812571 := bstep (se 1 (by rfl) ⟨3609428, by rfl⟩ : syracuseStep 4812571 = 7218857) B7218857
theorem B6416761 : Blo 2001435 6416761 := bstep (se 2 (by rfl) ⟨2406285, by rfl⟩ : syracuseStep 6416761 = 4812571) B4812571
theorem B8555681 : Blo 2001435 8555681 := bstep (se 2 (by rfl) ⟨3208380, by rfl⟩ : syracuseStep 8555681 = 6416761) B6416761
theorem B5703787 : Blo 2001435 5703787 := bstep (se 1 (by rfl) ⟨4277840, by rfl⟩ : syracuseStep 5703787 = 8555681) B8555681
theorem B7605049 : Blo 2001435 7605049 := bstep (se 2 (by rfl) ⟨2851893, by rfl⟩ : syracuseStep 7605049 = 5703787) B5703787
theorem B10140065 : Blo 2001435 10140065 := bstep (se 2 (by rfl) ⟨3802524, by rfl⟩ : syracuseStep 10140065 = 7605049) B7605049
theorem B6760043 : Blo 2001435 6760043 := bstep (se 1 (by rfl) ⟨5070032, by rfl⟩ : syracuseStep 6760043 = 10140065) B10140065
theorem B4506695 : Blo 2001435 4506695 := bstep (se 1 (by rfl) ⟨3380021, by rfl⟩ : syracuseStep 4506695 = 6760043) B6760043
theorem B3004463 : Blo 2001435 3004463 := bstep (se 1 (by rfl) ⟨2253347, by rfl⟩ : syracuseStep 3004463 = 4506695) B4506695
theorem B2002975 : Blo 2001435 2002975 := bstep (se 1 (by rfl) ⟨1502231, by rfl⟩ : syracuseStep 2002975 = 3004463) B3004463
theorem B3004469 : Blo 2001435 3004469 := bbase (se 5 (by rfl) ⟨140834, by rfl⟩ : syracuseStep 3004469 = 281669) (by norm_num)
theorem B2002979 : Blo 2001435 2002979 := bstep (se 1 (by rfl) ⟨1502234, by rfl⟩ : syracuseStep 2002979 = 3004469) B3004469
theorem B5070053 : Blo 2001435 5070053 := bbase (se 4 (by rfl) ⟨475317, by rfl⟩ : syracuseStep 5070053 = 950635) (by norm_num)
theorem B3380035 : Blo 2001435 3380035 := bstep (se 1 (by rfl) ⟨2535026, by rfl⟩ : syracuseStep 3380035 = 5070053) B5070053
theorem B4506713 : Blo 2001435 4506713 := bstep (se 2 (by rfl) ⟨1690017, by rfl⟩ : syracuseStep 4506713 = 3380035) B3380035
theorem B3004475 : Blo 2001435 3004475 := bstep (se 1 (by rfl) ⟨2253356, by rfl⟩ : syracuseStep 3004475 = 4506713) B4506713
theorem B2002983 : Blo 2001435 2002983 := bstep (se 1 (by rfl) ⟨1502237, by rfl⟩ : syracuseStep 2002983 = 3004475) B3004475
theorem B2253361 : Blo 2001435 2253361 := bbase (se 2 (by rfl) ⟨845010, by rfl⟩ : syracuseStep 2253361 = 1690021) (by norm_num)
theorem B3004481 : Blo 2001435 3004481 := bstep (se 2 (by rfl) ⟨1126680, by rfl⟩ : syracuseStep 3004481 = 2253361) B2253361
theorem B2002987 : Blo 2001435 2002987 := bstep (se 1 (by rfl) ⟨1502240, by rfl⟩ : syracuseStep 2002987 = 3004481) B3004481
theorem B2406305 : Blo 2001435 2406305 := bbase (se 2 (by rfl) ⟨902364, by rfl⟩ : syracuseStep 2406305 = 1804729) (by norm_num)
theorem B6416813 : Blo 2001435 6416813 := bstep (se 3 (by rfl) ⟨1203152, by rfl⟩ : syracuseStep 6416813 = 2406305) B2406305
theorem B4277875 : Blo 2001435 4277875 := bstep (se 1 (by rfl) ⟨3208406, by rfl⟩ : syracuseStep 4277875 = 6416813) B6416813
theorem B5703833 : Blo 2001435 5703833 := bstep (se 2 (by rfl) ⟨2138937, by rfl⟩ : syracuseStep 5703833 = 4277875) B4277875
theorem B3802555 : Blo 2001435 3802555 := bstep (se 1 (by rfl) ⟨2851916, by rfl⟩ : syracuseStep 3802555 = 5703833) B5703833
theorem B5070073 : Blo 2001435 5070073 := bstep (se 2 (by rfl) ⟨1901277, by rfl⟩ : syracuseStep 5070073 = 3802555) B3802555
theorem B6760097 : Blo 2001435 6760097 := bstep (se 2 (by rfl) ⟨2535036, by rfl⟩ : syracuseStep 6760097 = 5070073) B5070073
theorem B4506731 : Blo 2001435 4506731 := bstep (se 1 (by rfl) ⟨3380048, by rfl⟩ : syracuseStep 4506731 = 6760097) B6760097
theorem B3004487 : Blo 2001435 3004487 := bstep (se 1 (by rfl) ⟨2253365, by rfl⟩ : syracuseStep 3004487 = 4506731) B4506731
theorem B2002991 : Blo 2001435 2002991 := bstep (se 1 (by rfl) ⟨1502243, by rfl⟩ : syracuseStep 2002991 = 3004487) B3004487
theorem B3004493 : Blo 2001435 3004493 := bbase (se 3 (by rfl) ⟨563342, by rfl⟩ : syracuseStep 3004493 = 1126685) (by norm_num)
theorem B2002995 : Blo 2001435 2002995 := bstep (se 1 (by rfl) ⟨1502246, by rfl⟩ : syracuseStep 2002995 = 3004493) B3004493
theorem B4506749 : Blo 2001435 4506749 := bbase (se 3 (by rfl) ⟨845015, by rfl⟩ : syracuseStep 4506749 = 1690031) (by norm_num)
theorem B3004499 : Blo 2001435 3004499 := bstep (se 1 (by rfl) ⟨2253374, by rfl⟩ : syracuseStep 3004499 = 4506749) B4506749
theorem B2002999 : Blo 2001435 2002999 := bstep (se 1 (by rfl) ⟨1502249, by rfl⟩ : syracuseStep 2002999 = 3004499) B3004499
theorem B3380069 : Blo 2001435 3380069 := bbase (se 4 (by rfl) ⟨316881, by rfl⟩ : syracuseStep 3380069 = 633763) (by norm_num)
theorem B2253379 : Blo 2001435 2253379 := bstep (se 1 (by rfl) ⟨1690034, by rfl⟩ : syracuseStep 2253379 = 3380069) B3380069
theorem B3004505 : Blo 2001435 3004505 := bstep (se 2 (by rfl) ⟨1126689, by rfl⟩ : syracuseStep 3004505 = 2253379) B2253379
theorem B2003003 : Blo 2001435 2003003 := bstep (se 1 (by rfl) ⟨1502252, by rfl⟩ : syracuseStep 2003003 = 3004505) B3004505
theorem B4277909 : Blo 2001435 4277909 := bbase (se 6 (by rfl) ⟨100263, by rfl⟩ : syracuseStep 4277909 = 200527) (by norm_num)
theorem B2851939 : Blo 2001435 2851939 := bstep (se 1 (by rfl) ⟨2138954, by rfl⟩ : syracuseStep 2851939 = 4277909) B4277909
theorem B15210341 : Blo 2001435 15210341 := bstep (se 4 (by rfl) ⟨1425969, by rfl⟩ : syracuseStep 15210341 = 2851939) B2851939
theorem B10140227 : Blo 2001435 10140227 := bstep (se 1 (by rfl) ⟨7605170, by rfl⟩ : syracuseStep 10140227 = 15210341) B15210341
theorem B6760151 : Blo 2001435 6760151 := bstep (se 1 (by rfl) ⟨5070113, by rfl⟩ : syracuseStep 6760151 = 10140227) B10140227
theorem B4506767 : Blo 2001435 4506767 := bstep (se 1 (by rfl) ⟨3380075, by rfl⟩ : syracuseStep 4506767 = 6760151) B6760151
theorem B3004511 : Blo 2001435 3004511 := bstep (se 1 (by rfl) ⟨2253383, by rfl⟩ : syracuseStep 3004511 = 4506767) B4506767
theorem B2003007 : Blo 2001435 2003007 := bstep (se 1 (by rfl) ⟨1502255, by rfl⟩ : syracuseStep 2003007 = 3004511) B3004511
theorem B3004517 : Blo 2001435 3004517 := bbase (se 4 (by rfl) ⟨281673, by rfl⟩ : syracuseStep 3004517 = 563347) (by norm_num)
theorem B2003011 : Blo 2001435 2003011 := bstep (se 1 (by rfl) ⟨1502258, by rfl⟩ : syracuseStep 2003011 = 3004517) B3004517
theorem B12182069 : Blo 2001435 12182069 := bbase (se 5 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 12182069 = 1142069) (by norm_num)
theorem B8121379 : Blo 2001435 8121379 := bstep (se 1 (by rfl) ⟨6091034, by rfl⟩ : syracuseStep 8121379 = 12182069) B12182069
theorem B10828505 : Blo 2001435 10828505 := bstep (se 2 (by rfl) ⟨4060689, by rfl⟩ : syracuseStep 10828505 = 8121379) B8121379
theorem B7219003 : Blo 2001435 7219003 := bstep (se 1 (by rfl) ⟨5414252, by rfl⟩ : syracuseStep 7219003 = 10828505) B10828505
theorem B9625337 : Blo 2001435 9625337 := bstep (se 2 (by rfl) ⟨3609501, by rfl⟩ : syracuseStep 9625337 = 7219003) B7219003
theorem B6416891 : Blo 2001435 6416891 := bstep (se 1 (by rfl) ⟨4812668, by rfl⟩ : syracuseStep 6416891 = 9625337) B9625337
theorem B4277927 : Blo 2001435 4277927 := bstep (se 1 (by rfl) ⟨3208445, by rfl⟩ : syracuseStep 4277927 = 6416891) B6416891
theorem B2851951 : Blo 2001435 2851951 := bstep (se 1 (by rfl) ⟨2138963, by rfl⟩ : syracuseStep 2851951 = 4277927) B4277927
theorem B3802601 : Blo 2001435 3802601 := bstep (se 2 (by rfl) ⟨1425975, by rfl⟩ : syracuseStep 3802601 = 2851951) B2851951
theorem B2535067 : Blo 2001435 2535067 := bstep (se 1 (by rfl) ⟨1901300, by rfl⟩ : syracuseStep 2535067 = 3802601) B3802601
theorem B3380089 : Blo 2001435 3380089 := bstep (se 2 (by rfl) ⟨1267533, by rfl⟩ : syracuseStep 3380089 = 2535067) B2535067
theorem B4506785 : Blo 2001435 4506785 := bstep (se 2 (by rfl) ⟨1690044, by rfl⟩ : syracuseStep 4506785 = 3380089) B3380089
theorem B3004523 : Blo 2001435 3004523 := bstep (se 1 (by rfl) ⟨2253392, by rfl⟩ : syracuseStep 3004523 = 4506785) B4506785
theorem B2003015 : Blo 2001435 2003015 := bstep (se 1 (by rfl) ⟨1502261, by rfl⟩ : syracuseStep 2003015 = 3004523) B3004523
theorem B2253397 : Blo 2001435 2253397 := bbase (se 8 (by rfl) ⟨13203, by rfl⟩ : syracuseStep 2253397 = 26407) (by norm_num)
theorem B3004529 : Blo 2001435 3004529 := bstep (se 2 (by rfl) ⟨1126698, by rfl⟩ : syracuseStep 3004529 = 2253397) B2253397
theorem B2003019 : Blo 2001435 2003019 := bstep (se 1 (by rfl) ⟨1502264, by rfl⟩ : syracuseStep 2003019 = 3004529) B3004529
theorem B2535077 : Blo 2001435 2535077 := bbase (se 4 (by rfl) ⟨237663, by rfl⟩ : syracuseStep 2535077 = 475327) (by norm_num)
theorem B6760205 : Blo 2001435 6760205 := bstep (se 3 (by rfl) ⟨1267538, by rfl⟩ : syracuseStep 6760205 = 2535077) B2535077
theorem B4506803 : Blo 2001435 4506803 := bstep (se 1 (by rfl) ⟨3380102, by rfl⟩ : syracuseStep 4506803 = 6760205) B6760205
theorem B3004535 : Blo 2001435 3004535 := bstep (se 1 (by rfl) ⟨2253401, by rfl⟩ : syracuseStep 3004535 = 4506803) B4506803
theorem B2003023 : Blo 2001435 2003023 := bstep (se 1 (by rfl) ⟨1502267, by rfl⟩ : syracuseStep 2003023 = 3004535) B3004535
theorem B3004541 : Blo 2001435 3004541 := bbase (se 3 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 3004541 = 1126703) (by norm_num)
theorem B2003027 : Blo 2001435 2003027 := bstep (se 1 (by rfl) ⟨1502270, by rfl⟩ : syracuseStep 2003027 = 3004541) B3004541
theorem B4506821 : Blo 2001435 4506821 := bbase (se 4 (by rfl) ⟨422514, by rfl⟩ : syracuseStep 4506821 = 845029) (by norm_num)
theorem B3004547 : Blo 2001435 3004547 := bstep (se 1 (by rfl) ⟨2253410, by rfl⟩ : syracuseStep 3004547 = 4506821) B4506821
theorem B2003031 : Blo 2001435 2003031 := bstep (se 1 (by rfl) ⟨1502273, by rfl⟩ : syracuseStep 2003031 = 3004547) B3004547
theorem B12833909 : Blo 2001435 12833909 := bbase (se 5 (by rfl) ⟨601589, by rfl⟩ : syracuseStep 12833909 = 1203179) (by norm_num)
theorem B8555939 : Blo 2001435 8555939 := bstep (se 1 (by rfl) ⟨6416954, by rfl⟩ : syracuseStep 8555939 = 12833909) B12833909
theorem B5703959 : Blo 2001435 5703959 := bstep (se 1 (by rfl) ⟨4277969, by rfl⟩ : syracuseStep 5703959 = 8555939) B8555939
theorem B3802639 : Blo 2001435 3802639 := bstep (se 1 (by rfl) ⟨2851979, by rfl⟩ : syracuseStep 3802639 = 5703959) B5703959
theorem B5070185 : Blo 2001435 5070185 := bstep (se 2 (by rfl) ⟨1901319, by rfl⟩ : syracuseStep 5070185 = 3802639) B3802639
theorem B3380123 : Blo 2001435 3380123 := bstep (se 1 (by rfl) ⟨2535092, by rfl⟩ : syracuseStep 3380123 = 5070185) B5070185
theorem B2253415 : Blo 2001435 2253415 := bstep (se 1 (by rfl) ⟨1690061, by rfl⟩ : syracuseStep 2253415 = 3380123) B3380123
theorem B3004553 : Blo 2001435 3004553 := bstep (se 2 (by rfl) ⟨1126707, by rfl⟩ : syracuseStep 3004553 = 2253415) B2253415
theorem B2003035 : Blo 2001435 2003035 := bstep (se 1 (by rfl) ⟨1502276, by rfl⟩ : syracuseStep 2003035 = 3004553) B3004553
theorem B10140389 : Blo 2001435 10140389 := bbase (se 4 (by rfl) ⟨950661, by rfl⟩ : syracuseStep 10140389 = 1901323) (by norm_num)
theorem B6760259 : Blo 2001435 6760259 := bstep (se 1 (by rfl) ⟨5070194, by rfl⟩ : syracuseStep 6760259 = 10140389) B10140389
theorem B4506839 : Blo 2001435 4506839 := bstep (se 1 (by rfl) ⟨3380129, by rfl⟩ : syracuseStep 4506839 = 6760259) B6760259
theorem B3004559 : Blo 2001435 3004559 := bstep (se 1 (by rfl) ⟨2253419, by rfl⟩ : syracuseStep 3004559 = 4506839) B4506839
theorem B2003039 : Blo 2001435 2003039 := bstep (se 1 (by rfl) ⟨1502279, by rfl⟩ : syracuseStep 2003039 = 3004559) B3004559
theorem B3004565 : Blo 2001435 3004565 := bbase (se 6 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 3004565 = 140839) (by norm_num)
theorem B2003043 : Blo 2001435 2003043 := bstep (se 1 (by rfl) ⟨1502282, by rfl⟩ : syracuseStep 2003043 = 3004565) B3004565
theorem B8555989 : Blo 2001435 8555989 := bbase (se 7 (by rfl) ⟨100265, by rfl⟩ : syracuseStep 8555989 = 200531) (by norm_num)
theorem B11407985 : Blo 2001435 11407985 := bstep (se 2 (by rfl) ⟨4277994, by rfl⟩ : syracuseStep 11407985 = 8555989) B8555989
theorem B7605323 : Blo 2001435 7605323 := bstep (se 1 (by rfl) ⟨5703992, by rfl⟩ : syracuseStep 7605323 = 11407985) B11407985
theorem B5070215 : Blo 2001435 5070215 := bstep (se 1 (by rfl) ⟨3802661, by rfl⟩ : syracuseStep 5070215 = 7605323) B7605323
theorem B3380143 : Blo 2001435 3380143 := bstep (se 1 (by rfl) ⟨2535107, by rfl⟩ : syracuseStep 3380143 = 5070215) B5070215
theorem B4506857 : Blo 2001435 4506857 := bstep (se 2 (by rfl) ⟨1690071, by rfl⟩ : syracuseStep 4506857 = 3380143) B3380143
theorem B3004571 : Blo 2001435 3004571 := bstep (se 1 (by rfl) ⟨2253428, by rfl⟩ : syracuseStep 3004571 = 4506857) B4506857
theorem B2003047 : Blo 2001435 2003047 := bstep (se 1 (by rfl) ⟨1502285, by rfl⟩ : syracuseStep 2003047 = 3004571) B3004571
theorem B2253433 : Blo 2001435 2253433 := bbase (se 2 (by rfl) ⟨845037, by rfl⟩ : syracuseStep 2253433 = 1690075) (by norm_num)
theorem B3004577 : Blo 2001435 3004577 := bstep (se 2 (by rfl) ⟨1126716, by rfl⟩ : syracuseStep 3004577 = 2253433) B2253433
theorem B2003051 : Blo 2001435 2003051 := bstep (se 1 (by rfl) ⟨1502288, by rfl⟩ : syracuseStep 2003051 = 3004577) B3004577
theorem B5139413 : Blo 2001435 5139413 := bbase (se 7 (by rfl) ⟨60227, by rfl⟩ : syracuseStep 5139413 = 120455) (by norm_num)
theorem B3426275 : Blo 2001435 3426275 := bstep (se 1 (by rfl) ⟨2569706, by rfl⟩ : syracuseStep 3426275 = 5139413) B5139413
theorem B2284183 : Blo 2001435 2284183 := bstep (se 1 (by rfl) ⟨1713137, by rfl⟩ : syracuseStep 2284183 = 3426275) B3426275
theorem B12182309 : Blo 2001435 12182309 := bstep (se 4 (by rfl) ⟨1142091, by rfl⟩ : syracuseStep 12182309 = 2284183) B2284183
theorem B8121539 : Blo 2001435 8121539 := bstep (se 1 (by rfl) ⟨6091154, by rfl⟩ : syracuseStep 8121539 = 12182309) B12182309
theorem B5414359 : Blo 2001435 5414359 := bstep (se 1 (by rfl) ⟨4060769, by rfl⟩ : syracuseStep 5414359 = 8121539) B8121539
theorem B7219145 : Blo 2001435 7219145 := bstep (se 2 (by rfl) ⟨2707179, by rfl⟩ : syracuseStep 7219145 = 5414359) B5414359
theorem B19251053 : Blo 2001435 19251053 := bstep (se 3 (by rfl) ⟨3609572, by rfl⟩ : syracuseStep 19251053 = 7219145) B7219145
theorem B12834035 : Blo 2001435 12834035 := bstep (se 1 (by rfl) ⟨9625526, by rfl⟩ : syracuseStep 12834035 = 19251053) B19251053
theorem B8556023 : Blo 2001435 8556023 := bstep (se 1 (by rfl) ⟨6417017, by rfl⟩ : syracuseStep 8556023 = 12834035) B12834035
theorem B5704015 : Blo 2001435 5704015 := bstep (se 1 (by rfl) ⟨4278011, by rfl⟩ : syracuseStep 5704015 = 8556023) B8556023
theorem B7605353 : Blo 2001435 7605353 := bstep (se 2 (by rfl) ⟨2852007, by rfl⟩ : syracuseStep 7605353 = 5704015) B5704015
theorem B5070235 : Blo 2001435 5070235 := bstep (se 1 (by rfl) ⟨3802676, by rfl⟩ : syracuseStep 5070235 = 7605353) B7605353
theorem B6760313 : Blo 2001435 6760313 := bstep (se 2 (by rfl) ⟨2535117, by rfl⟩ : syracuseStep 6760313 = 5070235) B5070235
theorem B4506875 : Blo 2001435 4506875 := bstep (se 1 (by rfl) ⟨3380156, by rfl⟩ : syracuseStep 4506875 = 6760313) B6760313
theorem B3004583 : Blo 2001435 3004583 := bstep (se 1 (by rfl) ⟨2253437, by rfl⟩ : syracuseStep 3004583 = 4506875) B4506875
theorem B2003055 : Blo 2001435 2003055 := bstep (se 1 (by rfl) ⟨1502291, by rfl⟩ : syracuseStep 2003055 = 3004583) B3004583
theorem B3004589 : Blo 2001435 3004589 := bbase (se 3 (by rfl) ⟨563360, by rfl⟩ : syracuseStep 3004589 = 1126721) (by norm_num)
theorem B2003059 : Blo 2001435 2003059 := bstep (se 1 (by rfl) ⟨1502294, by rfl⟩ : syracuseStep 2003059 = 3004589) B3004589
theorem B4506893 : Blo 2001435 4506893 := bbase (se 3 (by rfl) ⟨845042, by rfl⟩ : syracuseStep 4506893 = 1690085) (by norm_num)
theorem B3004595 : Blo 2001435 3004595 := bstep (se 1 (by rfl) ⟨2253446, by rfl⟩ : syracuseStep 3004595 = 4506893) B4506893
theorem B2003063 : Blo 2001435 2003063 := bstep (se 1 (by rfl) ⟨1502297, by rfl⟩ : syracuseStep 2003063 = 3004595) B3004595
theorem B2535133 : Blo 2001435 2535133 := bbase (se 3 (by rfl) ⟨475337, by rfl⟩ : syracuseStep 2535133 = 950675) (by norm_num)
theorem B3380177 : Blo 2001435 3380177 := bstep (se 2 (by rfl) ⟨1267566, by rfl⟩ : syracuseStep 3380177 = 2535133) B2535133
theorem B2253451 : Blo 2001435 2253451 := bstep (se 1 (by rfl) ⟨1690088, by rfl⟩ : syracuseStep 2253451 = 3380177) B3380177
theorem B3004601 : Blo 2001435 3004601 := bstep (se 2 (by rfl) ⟨1126725, by rfl⟩ : syracuseStep 3004601 = 2253451) B2253451
theorem B2003067 : Blo 2001435 2003067 := bstep (se 1 (by rfl) ⟨1502300, by rfl⟩ : syracuseStep 2003067 = 3004601) B3004601
theorem B17112181 : Blo 2001435 17112181 := bbase (se 5 (by rfl) ⟨802133, by rfl⟩ : syracuseStep 17112181 = 1604267) (by norm_num)
theorem B22816241 : Blo 2001435 22816241 := bstep (se 2 (by rfl) ⟨8556090, by rfl⟩ : syracuseStep 22816241 = 17112181) B17112181
theorem B15210827 : Blo 2001435 15210827 := bstep (se 1 (by rfl) ⟨11408120, by rfl⟩ : syracuseStep 15210827 = 22816241) B22816241
theorem B10140551 : Blo 2001435 10140551 := bstep (se 1 (by rfl) ⟨7605413, by rfl⟩ : syracuseStep 10140551 = 15210827) B15210827
theorem B6760367 : Blo 2001435 6760367 := bstep (se 1 (by rfl) ⟨5070275, by rfl⟩ : syracuseStep 6760367 = 10140551) B10140551
theorem B4506911 : Blo 2001435 4506911 := bstep (se 1 (by rfl) ⟨3380183, by rfl⟩ : syracuseStep 4506911 = 6760367) B6760367
theorem B3004607 : Blo 2001435 3004607 := bstep (se 1 (by rfl) ⟨2253455, by rfl⟩ : syracuseStep 3004607 = 4506911) B4506911
theorem B2003071 : Blo 2001435 2003071 := bstep (se 1 (by rfl) ⟨1502303, by rfl⟩ : syracuseStep 2003071 = 3004607) B3004607
theorem B3004613 : Blo 2001435 3004613 := bbase (se 4 (by rfl) ⟨281682, by rfl⟩ : syracuseStep 3004613 = 563365) (by norm_num)
theorem B2003075 : Blo 2001435 2003075 := bstep (se 1 (by rfl) ⟨1502306, by rfl⟩ : syracuseStep 2003075 = 3004613) B3004613
theorem B3380197 : Blo 2001435 3380197 := bbase (se 4 (by rfl) ⟨316893, by rfl⟩ : syracuseStep 3380197 = 633787) (by norm_num)
theorem B4506929 : Blo 2001435 4506929 := bstep (se 2 (by rfl) ⟨1690098, by rfl⟩ : syracuseStep 4506929 = 3380197) B3380197
theorem B3004619 : Blo 2001435 3004619 := bstep (se 1 (by rfl) ⟨2253464, by rfl⟩ : syracuseStep 3004619 = 4506929) B4506929
theorem B2003079 : Blo 2001435 2003079 := bstep (se 1 (by rfl) ⟨1502309, by rfl⟩ : syracuseStep 2003079 = 3004619) B3004619
theorem B2253469 : Blo 2001435 2253469 := bbase (se 3 (by rfl) ⟨422525, by rfl⟩ : syracuseStep 2253469 = 845051) (by norm_num)
theorem B3004625 : Blo 2001435 3004625 := bstep (se 2 (by rfl) ⟨1126734, by rfl⟩ : syracuseStep 3004625 = 2253469) B2253469
theorem B2003083 : Blo 2001435 2003083 := bstep (se 1 (by rfl) ⟨1502312, by rfl⟩ : syracuseStep 2003083 = 3004625) B3004625
theorem B6760421 : Blo 2001435 6760421 := bbase (se 4 (by rfl) ⟨633789, by rfl⟩ : syracuseStep 6760421 = 1267579) (by norm_num)
theorem B4506947 : Blo 2001435 4506947 := bstep (se 1 (by rfl) ⟨3380210, by rfl⟩ : syracuseStep 4506947 = 6760421) B6760421
theorem B3004631 : Blo 2001435 3004631 := bstep (se 1 (by rfl) ⟨2253473, by rfl⟩ : syracuseStep 3004631 = 4506947) B4506947
theorem B2003087 : Blo 2001435 2003087 := bstep (se 1 (by rfl) ⟨1502315, by rfl⟩ : syracuseStep 2003087 = 3004631) B3004631
theorem B3004637 : Blo 2001435 3004637 := bbase (se 3 (by rfl) ⟨563369, by rfl⟩ : syracuseStep 3004637 = 1126739) (by norm_num)
theorem B2003091 : Blo 2001435 2003091 := bstep (se 1 (by rfl) ⟨1502318, by rfl⟩ : syracuseStep 2003091 = 3004637) B3004637
theorem B4506965 : Blo 2001435 4506965 := bbase (se 12 (by rfl) ⟨1650, by rfl⟩ : syracuseStep 4506965 = 3301) (by norm_num)
theorem B3004643 : Blo 2001435 3004643 := bstep (se 1 (by rfl) ⟨2253482, by rfl⟩ : syracuseStep 3004643 = 4506965) B4506965
theorem B2003095 : Blo 2001435 2003095 := bstep (se 1 (by rfl) ⟨1502321, by rfl⟩ : syracuseStep 2003095 = 3004643) B3004643
theorem B2139053 : Blo 2001435 2139053 := bbase (se 3 (by rfl) ⟨401072, by rfl⟩ : syracuseStep 2139053 = 802145) (by norm_num)
theorem B5704141 : Blo 2001435 5704141 := bstep (se 3 (by rfl) ⟨1069526, by rfl⟩ : syracuseStep 5704141 = 2139053) B2139053
theorem B7605521 : Blo 2001435 7605521 := bstep (se 2 (by rfl) ⟨2852070, by rfl⟩ : syracuseStep 7605521 = 5704141) B5704141
theorem B5070347 : Blo 2001435 5070347 := bstep (se 1 (by rfl) ⟨3802760, by rfl⟩ : syracuseStep 5070347 = 7605521) B7605521
theorem B3380231 : Blo 2001435 3380231 := bstep (se 1 (by rfl) ⟨2535173, by rfl⟩ : syracuseStep 3380231 = 5070347) B5070347
theorem B2253487 : Blo 2001435 2253487 := bstep (se 1 (by rfl) ⟨1690115, by rfl⟩ : syracuseStep 2253487 = 3380231) B3380231
theorem B3004649 : Blo 2001435 3004649 := bstep (se 2 (by rfl) ⟨1126743, by rfl⟩ : syracuseStep 3004649 = 2253487) B2253487
theorem B2003099 : Blo 2001435 2003099 := bstep (se 1 (by rfl) ⟨1502324, by rfl⟩ : syracuseStep 2003099 = 3004649) B3004649
theorem B28877269 : Blo 2001435 28877269 := bbase (se 7 (by rfl) ⟨338405, by rfl⟩ : syracuseStep 28877269 = 676811) (by norm_num)
theorem B38503025 : Blo 2001435 38503025 := bstep (se 2 (by rfl) ⟨14438634, by rfl⟩ : syracuseStep 38503025 = 28877269) B28877269
theorem B25668683 : Blo 2001435 25668683 := bstep (se 1 (by rfl) ⟨19251512, by rfl⟩ : syracuseStep 25668683 = 38503025) B38503025
theorem B17112455 : Blo 2001435 17112455 := bstep (se 1 (by rfl) ⟨12834341, by rfl⟩ : syracuseStep 17112455 = 25668683) B25668683
theorem B11408303 : Blo 2001435 11408303 := bstep (se 1 (by rfl) ⟨8556227, by rfl⟩ : syracuseStep 11408303 = 17112455) B17112455
theorem B7605535 : Blo 2001435 7605535 := bstep (se 1 (by rfl) ⟨5704151, by rfl⟩ : syracuseStep 7605535 = 11408303) B11408303
theorem B10140713 : Blo 2001435 10140713 := bstep (se 2 (by rfl) ⟨3802767, by rfl⟩ : syracuseStep 10140713 = 7605535) B7605535
theorem B6760475 : Blo 2001435 6760475 := bstep (se 1 (by rfl) ⟨5070356, by rfl⟩ : syracuseStep 6760475 = 10140713) B10140713
theorem B4506983 : Blo 2001435 4506983 := bstep (se 1 (by rfl) ⟨3380237, by rfl⟩ : syracuseStep 4506983 = 6760475) B6760475
theorem B3004655 : Blo 2001435 3004655 := bstep (se 1 (by rfl) ⟨2253491, by rfl⟩ : syracuseStep 3004655 = 4506983) B4506983
theorem B2003103 : Blo 2001435 2003103 := bstep (se 1 (by rfl) ⟨1502327, by rfl⟩ : syracuseStep 2003103 = 3004655) B3004655
theorem B3004661 : Blo 2001435 3004661 := bbase (se 5 (by rfl) ⟨140843, by rfl⟩ : syracuseStep 3004661 = 281687) (by norm_num)
theorem B2003107 : Blo 2001435 2003107 := bstep (se 1 (by rfl) ⟨1502330, by rfl⟩ : syracuseStep 2003107 = 3004661) B3004661
theorem B7317845 : Blo 2001435 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B4878563 : Blo 2001435 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B13009501 : Blo 2001435 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B17346001 : Blo 2001435 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B23128001 : Blo 2001435 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B15418667 : Blo 2001435 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B10279111 : Blo 2001435 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B13705481 : Blo 2001435 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B36547949 : Blo 2001435 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B24365299 : Blo 2001435 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B32487065 : Blo 2001435 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B21658043 : Blo 2001435 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B14438695 : Blo 2001435 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B19251593 : Blo 2001435 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B12834395 : Blo 2001435 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B8556263 : Blo 2001435 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B5704175 : Blo 2001435 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B3802783 : Blo 2001435 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B5070377 : Blo 2001435 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B3380251 : Blo 2001435 3380251 := bstep (se 1 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 3380251 = 5070377) B5070377
theorem B4507001 : Blo 2001435 4507001 := bstep (se 2 (by rfl) ⟨1690125, by rfl⟩ : syracuseStep 4507001 = 3380251) B3380251
theorem B3004667 : Blo 2001435 3004667 := bstep (se 1 (by rfl) ⟨2253500, by rfl⟩ : syracuseStep 3004667 = 4507001) B4507001
theorem B2003111 : Blo 2001435 2003111 := bstep (se 1 (by rfl) ⟨1502333, by rfl⟩ : syracuseStep 2003111 = 3004667) B3004667
theorem B2253505 : Blo 2001435 2253505 := bbase (se 2 (by rfl) ⟨845064, by rfl⟩ : syracuseStep 2253505 = 1690129) (by norm_num)
theorem B3004673 : Blo 2001435 3004673 := bstep (se 2 (by rfl) ⟨1126752, by rfl⟩ : syracuseStep 3004673 = 2253505) B2253505
theorem B2003115 : Blo 2001435 2003115 := bstep (se 1 (by rfl) ⟨1502336, by rfl⟩ : syracuseStep 2003115 = 3004673) B3004673
theorem B5070397 : Blo 2001435 5070397 := bbase (se 3 (by rfl) ⟨950699, by rfl⟩ : syracuseStep 5070397 = 1901399) (by norm_num)
theorem B6760529 : Blo 2001435 6760529 := bstep (se 2 (by rfl) ⟨2535198, by rfl⟩ : syracuseStep 6760529 = 5070397) B5070397
theorem B4507019 : Blo 2001435 4507019 := bstep (se 1 (by rfl) ⟨3380264, by rfl⟩ : syracuseStep 4507019 = 6760529) B6760529
theorem B3004679 : Blo 2001435 3004679 := bstep (se 1 (by rfl) ⟨2253509, by rfl⟩ : syracuseStep 3004679 = 4507019) B4507019
theorem B2003119 : Blo 2001435 2003119 := bstep (se 1 (by rfl) ⟨1502339, by rfl⟩ : syracuseStep 2003119 = 3004679) B3004679
theorem B3004685 : Blo 2001435 3004685 := bbase (se 3 (by rfl) ⟨563378, by rfl⟩ : syracuseStep 3004685 = 1126757) (by norm_num)
theorem B2003123 : Blo 2001435 2003123 := bstep (se 1 (by rfl) ⟨1502342, by rfl⟩ : syracuseStep 2003123 = 3004685) B3004685
theorem B4507037 : Blo 2001435 4507037 := bbase (se 3 (by rfl) ⟨845069, by rfl⟩ : syracuseStep 4507037 = 1690139) (by norm_num)
theorem B3004691 : Blo 2001435 3004691 := bstep (se 1 (by rfl) ⟨2253518, by rfl⟩ : syracuseStep 3004691 = 4507037) B4507037
theorem B2003127 : Blo 2001435 2003127 := bstep (se 1 (by rfl) ⟨1502345, by rfl⟩ : syracuseStep 2003127 = 3004691) B3004691
theorem B3380285 : Blo 2001435 3380285 := bbase (se 3 (by rfl) ⟨633803, by rfl⟩ : syracuseStep 3380285 = 1267607) (by norm_num)
theorem B2253523 : Blo 2001435 2253523 := bstep (se 1 (by rfl) ⟨1690142, by rfl⟩ : syracuseStep 2253523 = 3380285) B3380285
theorem B3004697 : Blo 2001435 3004697 := bstep (se 2 (by rfl) ⟨1126761, by rfl⟩ : syracuseStep 3004697 = 2253523) B2253523
theorem B2003131 : Blo 2001435 2003131 := bstep (se 1 (by rfl) ⟨1502348, by rfl⟩ : syracuseStep 2003131 = 3004697) B3004697
theorem B3208637 : Blo 2001435 3208637 := bbase (se 3 (by rfl) ⟨601619, by rfl⟩ : syracuseStep 3208637 = 1203239) (by norm_num)
theorem B2139091 : Blo 2001435 2139091 := bstep (se 1 (by rfl) ⟨1604318, by rfl⟩ : syracuseStep 2139091 = 3208637) B3208637
theorem B11408485 : Blo 2001435 11408485 := bstep (se 4 (by rfl) ⟨1069545, by rfl⟩ : syracuseStep 11408485 = 2139091) B2139091
theorem B15211313 : Blo 2001435 15211313 := bstep (se 2 (by rfl) ⟨5704242, by rfl⟩ : syracuseStep 15211313 = 11408485) B11408485
theorem B10140875 : Blo 2001435 10140875 := bstep (se 1 (by rfl) ⟨7605656, by rfl⟩ : syracuseStep 10140875 = 15211313) B15211313
theorem B6760583 : Blo 2001435 6760583 := bstep (se 1 (by rfl) ⟨5070437, by rfl⟩ : syracuseStep 6760583 = 10140875) B10140875
theorem B4507055 : Blo 2001435 4507055 := bstep (se 1 (by rfl) ⟨3380291, by rfl⟩ : syracuseStep 4507055 = 6760583) B6760583
theorem B3004703 : Blo 2001435 3004703 := bstep (se 1 (by rfl) ⟨2253527, by rfl⟩ : syracuseStep 3004703 = 4507055) B4507055
theorem B2003135 : Blo 2001435 2003135 := bstep (se 1 (by rfl) ⟨1502351, by rfl⟩ : syracuseStep 2003135 = 3004703) B3004703
theorem B3004709 : Blo 2001435 3004709 := bbase (se 4 (by rfl) ⟨281691, by rfl⟩ : syracuseStep 3004709 = 563383) (by norm_num)
theorem B2003139 : Blo 2001435 2003139 := bstep (se 1 (by rfl) ⟨1502354, by rfl⟩ : syracuseStep 2003139 = 3004709) B3004709
theorem B2535229 : Blo 2001435 2535229 := bbase (se 3 (by rfl) ⟨475355, by rfl⟩ : syracuseStep 2535229 = 950711) (by norm_num)
theorem B3380305 : Blo 2001435 3380305 := bstep (se 2 (by rfl) ⟨1267614, by rfl⟩ : syracuseStep 3380305 = 2535229) B2535229
theorem B4507073 : Blo 2001435 4507073 := bstep (se 2 (by rfl) ⟨1690152, by rfl⟩ : syracuseStep 4507073 = 3380305) B3380305
theorem B3004715 : Blo 2001435 3004715 := bstep (se 1 (by rfl) ⟨2253536, by rfl⟩ : syracuseStep 3004715 = 4507073) B4507073
theorem B2003143 : Blo 2001435 2003143 := bstep (se 1 (by rfl) ⟨1502357, by rfl⟩ : syracuseStep 2003143 = 3004715) B3004715
theorem B2253541 : Blo 2001435 2253541 := bbase (se 4 (by rfl) ⟨211269, by rfl⟩ : syracuseStep 2253541 = 422539) (by norm_num)
theorem B3004721 : Blo 2001435 3004721 := bstep (se 2 (by rfl) ⟨1126770, by rfl⟩ : syracuseStep 3004721 = 2253541) B2253541
theorem B2003147 : Blo 2001435 2003147 := bstep (se 1 (by rfl) ⟨1502360, by rfl⟩ : syracuseStep 2003147 = 3004721) B3004721
theorem B7219493 : Blo 2001435 7219493 := bbase (se 4 (by rfl) ⟨676827, by rfl⟩ : syracuseStep 7219493 = 1353655) (by norm_num)
theorem B4812995 : Blo 2001435 4812995 := bstep (se 1 (by rfl) ⟨3609746, by rfl⟩ : syracuseStep 4812995 = 7219493) B7219493
theorem B3208663 : Blo 2001435 3208663 := bstep (se 1 (by rfl) ⟨2406497, by rfl⟩ : syracuseStep 3208663 = 4812995) B4812995
theorem B4278217 : Blo 2001435 4278217 := bstep (se 2 (by rfl) ⟨1604331, by rfl⟩ : syracuseStep 4278217 = 3208663) B3208663
theorem B5704289 : Blo 2001435 5704289 := bstep (se 2 (by rfl) ⟨2139108, by rfl⟩ : syracuseStep 5704289 = 4278217) B4278217
theorem B3802859 : Blo 2001435 3802859 := bstep (se 1 (by rfl) ⟨2852144, by rfl⟩ : syracuseStep 3802859 = 5704289) B5704289
theorem B2535239 : Blo 2001435 2535239 := bstep (se 1 (by rfl) ⟨1901429, by rfl⟩ : syracuseStep 2535239 = 3802859) B3802859
theorem B6760637 : Blo 2001435 6760637 := bstep (se 3 (by rfl) ⟨1267619, by rfl⟩ : syracuseStep 6760637 = 2535239) B2535239
theorem B4507091 : Blo 2001435 4507091 := bstep (se 1 (by rfl) ⟨3380318, by rfl⟩ : syracuseStep 4507091 = 6760637) B6760637
theorem B3004727 : Blo 2001435 3004727 := bstep (se 1 (by rfl) ⟨2253545, by rfl⟩ : syracuseStep 3004727 = 4507091) B4507091
theorem B2003151 : Blo 2001435 2003151 := bstep (se 1 (by rfl) ⟨1502363, by rfl⟩ : syracuseStep 2003151 = 3004727) B3004727
theorem B3004733 : Blo 2001435 3004733 := bbase (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) (by norm_num)
theorem B2003155 : Blo 2001435 2003155 := bstep (se 1 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 2003155 = 3004733) B3004733
theorem B4507109 : Blo 2001435 4507109 := bbase (se 4 (by rfl) ⟨422541, by rfl⟩ : syracuseStep 4507109 = 845083) (by norm_num)
theorem B3004739 : Blo 2001435 3004739 := bstep (se 1 (by rfl) ⟨2253554, by rfl⟩ : syracuseStep 3004739 = 4507109) B4507109
theorem B2003159 : Blo 2001435 2003159 := bstep (se 1 (by rfl) ⟨1502369, by rfl⟩ : syracuseStep 2003159 = 3004739) B3004739
theorem B5070509 : Blo 2001435 5070509 := bbase (se 3 (by rfl) ⟨950720, by rfl⟩ : syracuseStep 5070509 = 1901441) (by norm_num)
theorem B3380339 : Blo 2001435 3380339 := bstep (se 1 (by rfl) ⟨2535254, by rfl⟩ : syracuseStep 3380339 = 5070509) B5070509
theorem B2253559 : Blo 2001435 2253559 := bstep (se 1 (by rfl) ⟨1690169, by rfl⟩ : syracuseStep 2253559 = 3380339) B3380339
theorem B3004745 : Blo 2001435 3004745 := bstep (se 2 (by rfl) ⟨1126779, by rfl⟩ : syracuseStep 3004745 = 2253559) B2253559
theorem B2003163 : Blo 2001435 2003163 := bstep (se 1 (by rfl) ⟨1502372, by rfl⟩ : syracuseStep 2003163 = 3004745) B3004745
theorem B5139701 : Blo 2001435 5139701 := bbase (se 5 (by rfl) ⟨240923, by rfl⟩ : syracuseStep 5139701 = 481847) (by norm_num)
theorem B3426467 : Blo 2001435 3426467 := bstep (se 1 (by rfl) ⟨2569850, by rfl⟩ : syracuseStep 3426467 = 5139701) B5139701
theorem B9137245 : Blo 2001435 9137245 := bstep (se 3 (by rfl) ⟨1713233, by rfl⟩ : syracuseStep 9137245 = 3426467) B3426467
theorem B12182993 : Blo 2001435 12182993 := bstep (se 2 (by rfl) ⟨4568622, by rfl⟩ : syracuseStep 12182993 = 9137245) B9137245
theorem B8121995 : Blo 2001435 8121995 := bstep (se 1 (by rfl) ⟨6091496, by rfl⟩ : syracuseStep 8121995 = 12182993) B12182993
theorem B5414663 : Blo 2001435 5414663 := bstep (se 1 (by rfl) ⟨4060997, by rfl⟩ : syracuseStep 5414663 = 8121995) B8121995
theorem B3609775 : Blo 2001435 3609775 := bstep (se 1 (by rfl) ⟨2707331, by rfl⟩ : syracuseStep 3609775 = 5414663) B5414663
theorem B4813033 : Blo 2001435 4813033 := bstep (se 2 (by rfl) ⟨1804887, by rfl⟩ : syracuseStep 4813033 = 3609775) B3609775
theorem B6417377 : Blo 2001435 6417377 := bstep (se 2 (by rfl) ⟨2406516, by rfl⟩ : syracuseStep 6417377 = 4813033) B4813033
theorem B4278251 : Blo 2001435 4278251 := bstep (se 1 (by rfl) ⟨3208688, by rfl⟩ : syracuseStep 4278251 = 6417377) B6417377
theorem B2852167 : Blo 2001435 2852167 := bstep (se 1 (by rfl) ⟨2139125, by rfl⟩ : syracuseStep 2852167 = 4278251) B4278251
theorem B3802889 : Blo 2001435 3802889 := bstep (se 2 (by rfl) ⟨1426083, by rfl⟩ : syracuseStep 3802889 = 2852167) B2852167
theorem B10141037 : Blo 2001435 10141037 := bstep (se 3 (by rfl) ⟨1901444, by rfl⟩ : syracuseStep 10141037 = 3802889) B3802889
theorem B6760691 : Blo 2001435 6760691 := bstep (se 1 (by rfl) ⟨5070518, by rfl⟩ : syracuseStep 6760691 = 10141037) B10141037
theorem B4507127 : Blo 2001435 4507127 := bstep (se 1 (by rfl) ⟨3380345, by rfl⟩ : syracuseStep 4507127 = 6760691) B6760691
theorem B3004751 : Blo 2001435 3004751 := bstep (se 1 (by rfl) ⟨2253563, by rfl⟩ : syracuseStep 3004751 = 4507127) B4507127
theorem B2003167 : Blo 2001435 2003167 := bstep (se 1 (by rfl) ⟨1502375, by rfl⟩ : syracuseStep 2003167 = 3004751) B3004751
theorem B3004757 : Blo 2001435 3004757 := bbase (se 10 (by rfl) ⟨4401, by rfl⟩ : syracuseStep 3004757 = 8803) (by norm_num)
theorem B2003171 : Blo 2001435 2003171 := bstep (se 1 (by rfl) ⟨1502378, by rfl⟩ : syracuseStep 2003171 = 3004757) B3004757
theorem B5704357 : Blo 2001435 5704357 := bbase (se 4 (by rfl) ⟨534783, by rfl⟩ : syracuseStep 5704357 = 1069567) (by norm_num)
theorem B7605809 : Blo 2001435 7605809 := bstep (se 2 (by rfl) ⟨2852178, by rfl⟩ : syracuseStep 7605809 = 5704357) B5704357
theorem B5070539 : Blo 2001435 5070539 := bstep (se 1 (by rfl) ⟨3802904, by rfl⟩ : syracuseStep 5070539 = 7605809) B7605809
theorem B3380359 : Blo 2001435 3380359 := bstep (se 1 (by rfl) ⟨2535269, by rfl⟩ : syracuseStep 3380359 = 5070539) B5070539
theorem B4507145 : Blo 2001435 4507145 := bstep (se 2 (by rfl) ⟨1690179, by rfl⟩ : syracuseStep 4507145 = 3380359) B3380359
theorem B3004763 : Blo 2001435 3004763 := bstep (se 1 (by rfl) ⟨2253572, by rfl⟩ : syracuseStep 3004763 = 4507145) B4507145
theorem B2003175 : Blo 2001435 2003175 := bstep (se 1 (by rfl) ⟨1502381, by rfl⟩ : syracuseStep 2003175 = 3004763) B3004763
theorem B2253577 : Blo 2001435 2253577 := bbase (se 2 (by rfl) ⟨845091, by rfl⟩ : syracuseStep 2253577 = 1690183) (by norm_num)
theorem B3004769 : Blo 2001435 3004769 := bstep (se 2 (by rfl) ⟨1126788, by rfl⟩ : syracuseStep 3004769 = 2253577) B2253577
theorem B2003179 : Blo 2001435 2003179 := bstep (se 1 (by rfl) ⟨1502384, by rfl⟩ : syracuseStep 2003179 = 3004769) B3004769
theorem B4061029 : Blo 2001435 4061029 := bbase (se 4 (by rfl) ⟨380721, by rfl⟩ : syracuseStep 4061029 = 761443) (by norm_num)
theorem B5414705 : Blo 2001435 5414705 := bstep (se 2 (by rfl) ⟨2030514, by rfl⟩ : syracuseStep 5414705 = 4061029) B4061029
theorem B3609803 : Blo 2001435 3609803 := bstep (se 1 (by rfl) ⟨2707352, by rfl⟩ : syracuseStep 3609803 = 5414705) B5414705
theorem B9626141 : Blo 2001435 9626141 := bstep (se 3 (by rfl) ⟨1804901, by rfl⟩ : syracuseStep 9626141 = 3609803) B3609803
theorem B25669709 : Blo 2001435 25669709 := bstep (se 3 (by rfl) ⟨4813070, by rfl⟩ : syracuseStep 25669709 = 9626141) B9626141
theorem B17113139 : Blo 2001435 17113139 := bstep (se 1 (by rfl) ⟨12834854, by rfl⟩ : syracuseStep 17113139 = 25669709) B25669709
theorem B11408759 : Blo 2001435 11408759 := bstep (se 1 (by rfl) ⟨8556569, by rfl⟩ : syracuseStep 11408759 = 17113139) B17113139
theorem B7605839 : Blo 2001435 7605839 := bstep (se 1 (by rfl) ⟨5704379, by rfl⟩ : syracuseStep 7605839 = 11408759) B11408759
theorem B5070559 : Blo 2001435 5070559 := bstep (se 1 (by rfl) ⟨3802919, by rfl⟩ : syracuseStep 5070559 = 7605839) B7605839
theorem B6760745 : Blo 2001435 6760745 := bstep (se 2 (by rfl) ⟨2535279, by rfl⟩ : syracuseStep 6760745 = 5070559) B5070559
theorem B4507163 : Blo 2001435 4507163 := bstep (se 1 (by rfl) ⟨3380372, by rfl⟩ : syracuseStep 4507163 = 6760745) B6760745
theorem B3004775 : Blo 2001435 3004775 := bstep (se 1 (by rfl) ⟨2253581, by rfl⟩ : syracuseStep 3004775 = 4507163) B4507163
theorem B2003183 : Blo 2001435 2003183 := bstep (se 1 (by rfl) ⟨1502387, by rfl⟩ : syracuseStep 2003183 = 3004775) B3004775
theorem B3004781 : Blo 2001435 3004781 := bbase (se 3 (by rfl) ⟨563396, by rfl⟩ : syracuseStep 3004781 = 1126793) (by norm_num)
theorem B2003187 : Blo 2001435 2003187 := bstep (se 1 (by rfl) ⟨1502390, by rfl⟩ : syracuseStep 2003187 = 3004781) B3004781
theorem B4507181 : Blo 2001435 4507181 := bbase (se 3 (by rfl) ⟨845096, by rfl⟩ : syracuseStep 4507181 = 1690193) (by norm_num)
theorem B3004787 : Blo 2001435 3004787 := bstep (se 1 (by rfl) ⟨2253590, by rfl⟩ : syracuseStep 3004787 = 4507181) B4507181
theorem B2003191 : Blo 2001435 2003191 := bstep (se 1 (by rfl) ⟨1502393, by rfl⟩ : syracuseStep 2003191 = 3004787) B3004787
theorem B2439385 : Blo 2001435 2439385 := bbase (se 2 (by rfl) ⟨914769, by rfl⟩ : syracuseStep 2439385 = 1829539) (by norm_num)
theorem B13010053 : Blo 2001435 13010053 := bstep (se 4 (by rfl) ⟨1219692, by rfl⟩ : syracuseStep 13010053 = 2439385) B2439385
theorem B17346737 : Blo 2001435 17346737 := bstep (se 2 (by rfl) ⟨6505026, by rfl⟩ : syracuseStep 17346737 = 13010053) B13010053
theorem B11564491 : Blo 2001435 11564491 := bstep (se 1 (by rfl) ⟨8673368, by rfl⟩ : syracuseStep 11564491 = 17346737) B17346737
theorem B15419321 : Blo 2001435 15419321 := bstep (se 2 (by rfl) ⟨5782245, by rfl⟩ : syracuseStep 15419321 = 11564491) B11564491
theorem B10279547 : Blo 2001435 10279547 := bstep (se 1 (by rfl) ⟨7709660, by rfl⟩ : syracuseStep 10279547 = 15419321) B15419321
theorem B6853031 : Blo 2001435 6853031 := bstep (se 1 (by rfl) ⟨5139773, by rfl⟩ : syracuseStep 6853031 = 10279547) B10279547
theorem B4568687 : Blo 2001435 4568687 := bstep (se 1 (by rfl) ⟨3426515, by rfl⟩ : syracuseStep 4568687 = 6853031) B6853031
theorem B3045791 : Blo 2001435 3045791 := bstep (se 1 (by rfl) ⟨2284343, by rfl⟩ : syracuseStep 3045791 = 4568687) B4568687
theorem B2030527 : Blo 2001435 2030527 := bstep (se 1 (by rfl) ⟨1522895, by rfl⟩ : syracuseStep 2030527 = 3045791) B3045791
theorem B10829477 : Blo 2001435 10829477 := bstep (se 4 (by rfl) ⟨1015263, by rfl⟩ : syracuseStep 10829477 = 2030527) B2030527
theorem B28878605 : Blo 2001435 28878605 := bstep (se 3 (by rfl) ⟨5414738, by rfl⟩ : syracuseStep 28878605 = 10829477) B10829477
theorem B19252403 : Blo 2001435 19252403 := bstep (se 1 (by rfl) ⟨14439302, by rfl⟩ : syracuseStep 19252403 = 28878605) B28878605
theorem B12834935 : Blo 2001435 12834935 := bstep (se 1 (by rfl) ⟨9626201, by rfl⟩ : syracuseStep 12834935 = 19252403) B19252403
theorem B8556623 : Blo 2001435 8556623 := bstep (se 1 (by rfl) ⟨6417467, by rfl⟩ : syracuseStep 8556623 = 12834935) B12834935
theorem B5704415 : Blo 2001435 5704415 := bstep (se 1 (by rfl) ⟨4278311, by rfl⟩ : syracuseStep 5704415 = 8556623) B8556623
theorem B3802943 : Blo 2001435 3802943 := bstep (se 1 (by rfl) ⟨2852207, by rfl⟩ : syracuseStep 3802943 = 5704415) B5704415
theorem B2535295 : Blo 2001435 2535295 := bstep (se 1 (by rfl) ⟨1901471, by rfl⟩ : syracuseStep 2535295 = 3802943) B3802943
theorem B3380393 : Blo 2001435 3380393 := bstep (se 2 (by rfl) ⟨1267647, by rfl⟩ : syracuseStep 3380393 = 2535295) B2535295
theorem B2253595 : Blo 2001435 2253595 := bstep (se 1 (by rfl) ⟨1690196, by rfl⟩ : syracuseStep 2253595 = 3380393) B3380393
theorem B3004793 : Blo 2001435 3004793 := bstep (se 2 (by rfl) ⟨1126797, by rfl⟩ : syracuseStep 3004793 = 2253595) B2253595
theorem B2003195 : Blo 2001435 2003195 := bstep (se 1 (by rfl) ⟨1502396, by rfl⟩ : syracuseStep 2003195 = 3004793) B3004793
theorem B4813109 : Blo 2001435 4813109 := bbase (se 5 (by rfl) ⟨225614, by rfl⟩ : syracuseStep 4813109 = 451229) (by norm_num)
theorem B3208739 : Blo 2001435 3208739 := bstep (se 1 (by rfl) ⟨2406554, by rfl⟩ : syracuseStep 3208739 = 4813109) B4813109
theorem B34226549 : Blo 2001435 34226549 := bstep (se 5 (by rfl) ⟨1604369, by rfl⟩ : syracuseStep 34226549 = 3208739) B3208739
theorem B22817699 : Blo 2001435 22817699 := bstep (se 1 (by rfl) ⟨17113274, by rfl⟩ : syracuseStep 22817699 = 34226549) B34226549
theorem B15211799 : Blo 2001435 15211799 := bstep (se 1 (by rfl) ⟨11408849, by rfl⟩ : syracuseStep 15211799 = 22817699) B22817699
theorem B10141199 : Blo 2001435 10141199 := bstep (se 1 (by rfl) ⟨7605899, by rfl⟩ : syracuseStep 10141199 = 15211799) B15211799
theorem B6760799 : Blo 2001435 6760799 := bstep (se 1 (by rfl) ⟨5070599, by rfl⟩ : syracuseStep 6760799 = 10141199) B10141199
theorem B4507199 : Blo 2001435 4507199 := bstep (se 1 (by rfl) ⟨3380399, by rfl⟩ : syracuseStep 4507199 = 6760799) B6760799
theorem B3004799 : Blo 2001435 3004799 := bstep (se 1 (by rfl) ⟨2253599, by rfl⟩ : syracuseStep 3004799 = 4507199) B4507199
theorem B2003199 : Blo 2001435 2003199 := bstep (se 1 (by rfl) ⟨1502399, by rfl⟩ : syracuseStep 2003199 = 3004799) B3004799
theorem B3004805 : Blo 2001435 3004805 := bbase (se 4 (by rfl) ⟨281700, by rfl⟩ : syracuseStep 3004805 = 563401) (by norm_num)
theorem B2003203 : Blo 2001435 2003203 := bstep (se 1 (by rfl) ⟨1502402, by rfl⟩ : syracuseStep 2003203 = 3004805) B3004805
theorem B3380413 : Blo 2001435 3380413 := bbase (se 3 (by rfl) ⟨633827, by rfl⟩ : syracuseStep 3380413 = 1267655) (by norm_num)
theorem B4507217 : Blo 2001435 4507217 := bstep (se 2 (by rfl) ⟨1690206, by rfl⟩ : syracuseStep 4507217 = 3380413) B3380413
theorem B3004811 : Blo 2001435 3004811 := bstep (se 1 (by rfl) ⟨2253608, by rfl⟩ : syracuseStep 3004811 = 4507217) B4507217
theorem B2003207 : Blo 2001435 2003207 := bstep (se 1 (by rfl) ⟨1502405, by rfl⟩ : syracuseStep 2003207 = 3004811) B3004811
theorem B2253613 : Blo 2001435 2253613 := bbase (se 3 (by rfl) ⟨422552, by rfl⟩ : syracuseStep 2253613 = 845105) (by norm_num)
theorem B3004817 : Blo 2001435 3004817 := bstep (se 2 (by rfl) ⟨1126806, by rfl⟩ : syracuseStep 3004817 = 2253613) B2253613
theorem B2003211 : Blo 2001435 2003211 := bstep (se 1 (by rfl) ⟨1502408, by rfl⟩ : syracuseStep 2003211 = 3004817) B3004817
theorem B6760853 : Blo 2001435 6760853 := bbase (se 6 (by rfl) ⟨158457, by rfl⟩ : syracuseStep 6760853 = 316915) (by norm_num)
theorem B4507235 : Blo 2001435 4507235 := bstep (se 1 (by rfl) ⟨3380426, by rfl⟩ : syracuseStep 4507235 = 6760853) B6760853
theorem B3004823 : Blo 2001435 3004823 := bstep (se 1 (by rfl) ⟨2253617, by rfl⟩ : syracuseStep 3004823 = 4507235) B4507235
theorem B2003215 : Blo 2001435 2003215 := bstep (se 1 (by rfl) ⟨1502411, by rfl⟩ : syracuseStep 2003215 = 3004823) B3004823
theorem B3004829 : Blo 2001435 3004829 := bbase (se 3 (by rfl) ⟨563405, by rfl⟩ : syracuseStep 3004829 = 1126811) (by norm_num)
theorem B2003219 : Blo 2001435 2003219 := bstep (se 1 (by rfl) ⟨1502414, by rfl⟩ : syracuseStep 2003219 = 3004829) B3004829
theorem B4507253 : Blo 2001435 4507253 := bbase (se 5 (by rfl) ⟨211277, by rfl⟩ : syracuseStep 4507253 = 422555) (by norm_num)
theorem B3004835 : Blo 2001435 3004835 := bstep (se 1 (by rfl) ⟨2253626, by rfl⟩ : syracuseStep 3004835 = 4507253) B4507253
theorem B2003223 : Blo 2001435 2003223 := bstep (se 1 (by rfl) ⟨1502417, by rfl⟩ : syracuseStep 2003223 = 3004835) B3004835
theorem B3296941 : Blo 2001435 3296941 := bbase (se 3 (by rfl) ⟨618176, by rfl⟩ : syracuseStep 3296941 = 1236353) (by norm_num)
theorem B17583685 : Blo 2001435 17583685 := bstep (se 4 (by rfl) ⟨1648470, by rfl⟩ : syracuseStep 17583685 = 3296941) B3296941
theorem B93779653 : Blo 2001435 93779653 := bstep (se 4 (by rfl) ⟨8791842, by rfl⟩ : syracuseStep 93779653 = 17583685) B17583685
theorem B125039537 : Blo 2001435 125039537 := bstep (se 2 (by rfl) ⟨46889826, by rfl⟩ : syracuseStep 125039537 = 93779653) B93779653
theorem B83359691 : Blo 2001435 83359691 := bstep (se 1 (by rfl) ⟨62519768, by rfl⟩ : syracuseStep 83359691 = 125039537) B125039537
theorem B55573127 : Blo 2001435 55573127 := bstep (se 1 (by rfl) ⟨41679845, by rfl⟩ : syracuseStep 55573127 = 83359691) B83359691
theorem B37048751 : Blo 2001435 37048751 := bstep (se 1 (by rfl) ⟨27786563, by rfl⟩ : syracuseStep 37048751 = 55573127) B55573127
theorem B24699167 : Blo 2001435 24699167 := bstep (se 1 (by rfl) ⟨18524375, by rfl⟩ : syracuseStep 24699167 = 37048751) B37048751
theorem B16466111 : Blo 2001435 16466111 := bstep (se 1 (by rfl) ⟨12349583, by rfl⟩ : syracuseStep 16466111 = 24699167) B24699167
theorem B10977407 : Blo 2001435 10977407 := bstep (se 1 (by rfl) ⟨8233055, by rfl⟩ : syracuseStep 10977407 = 16466111) B16466111
theorem B7318271 : Blo 2001435 7318271 := bstep (se 1 (by rfl) ⟨5488703, by rfl⟩ : syracuseStep 7318271 = 10977407) B10977407
theorem B4878847 : Blo 2001435 4878847 := bstep (se 1 (by rfl) ⟨3659135, by rfl⟩ : syracuseStep 4878847 = 7318271) B7318271
theorem B6505129 : Blo 2001435 6505129 := bstep (se 2 (by rfl) ⟨2439423, by rfl⟩ : syracuseStep 6505129 = 4878847) B4878847
theorem B34694021 : Blo 2001435 34694021 := bstep (se 4 (by rfl) ⟨3252564, by rfl⟩ : syracuseStep 34694021 = 6505129) B6505129
theorem B23129347 : Blo 2001435 23129347 := bstep (se 1 (by rfl) ⟨17347010, by rfl⟩ : syracuseStep 23129347 = 34694021) B34694021
theorem B30839129 : Blo 2001435 30839129 := bstep (se 2 (by rfl) ⟨11564673, by rfl⟩ : syracuseStep 30839129 = 23129347) B23129347
theorem B20559419 : Blo 2001435 20559419 := bstep (se 1 (by rfl) ⟨15419564, by rfl⟩ : syracuseStep 20559419 = 30839129) B30839129
theorem B13706279 : Blo 2001435 13706279 := bstep (se 1 (by rfl) ⟨10279709, by rfl⟩ : syracuseStep 13706279 = 20559419) B20559419
theorem B9137519 : Blo 2001435 9137519 := bstep (se 1 (by rfl) ⟨6853139, by rfl⟩ : syracuseStep 9137519 = 13706279) B13706279
theorem B6091679 : Blo 2001435 6091679 := bstep (se 1 (by rfl) ⟨4568759, by rfl⟩ : syracuseStep 6091679 = 9137519) B9137519
theorem B4061119 : Blo 2001435 4061119 := bstep (se 1 (by rfl) ⟨3045839, by rfl⟩ : syracuseStep 4061119 = 6091679) B6091679
theorem B5414825 : Blo 2001435 5414825 := bstep (se 2 (by rfl) ⟨2030559, by rfl⟩ : syracuseStep 5414825 = 4061119) B4061119
theorem B3609883 : Blo 2001435 3609883 := bstep (se 1 (by rfl) ⟨2707412, by rfl⟩ : syracuseStep 3609883 = 5414825) B5414825
theorem B4813177 : Blo 2001435 4813177 := bstep (se 2 (by rfl) ⟨1804941, by rfl⟩ : syracuseStep 4813177 = 3609883) B3609883
theorem B6417569 : Blo 2001435 6417569 := bstep (se 2 (by rfl) ⟨2406588, by rfl⟩ : syracuseStep 6417569 = 4813177) B4813177
theorem B17113517 : Blo 2001435 17113517 := bstep (se 3 (by rfl) ⟨3208784, by rfl⟩ : syracuseStep 17113517 = 6417569) B6417569
theorem B11409011 : Blo 2001435 11409011 := bstep (se 1 (by rfl) ⟨8556758, by rfl⟩ : syracuseStep 11409011 = 17113517) B17113517
theorem B7606007 : Blo 2001435 7606007 := bstep (se 1 (by rfl) ⟨5704505, by rfl⟩ : syracuseStep 7606007 = 11409011) B11409011
theorem B5070671 : Blo 2001435 5070671 := bstep (se 1 (by rfl) ⟨3803003, by rfl⟩ : syracuseStep 5070671 = 7606007) B7606007
theorem B3380447 : Blo 2001435 3380447 := bstep (se 1 (by rfl) ⟨2535335, by rfl⟩ : syracuseStep 3380447 = 5070671) B5070671
theorem B2253631 : Blo 2001435 2253631 := bstep (se 1 (by rfl) ⟨1690223, by rfl⟩ : syracuseStep 2253631 = 3380447) B3380447
theorem B3004841 : Blo 2001435 3004841 := bstep (se 2 (by rfl) ⟨1126815, by rfl⟩ : syracuseStep 3004841 = 2253631) B2253631
theorem B2003227 : Blo 2001435 2003227 := bstep (se 1 (by rfl) ⟨1502420, by rfl⟩ : syracuseStep 2003227 = 3004841) B3004841
theorem B7606021 : Blo 2001435 7606021 := bbase (se 4 (by rfl) ⟨713064, by rfl⟩ : syracuseStep 7606021 = 1426129) (by norm_num)
theorem B10141361 : Blo 2001435 10141361 := bstep (se 2 (by rfl) ⟨3803010, by rfl⟩ : syracuseStep 10141361 = 7606021) B7606021
theorem B6760907 : Blo 2001435 6760907 := bstep (se 1 (by rfl) ⟨5070680, by rfl⟩ : syracuseStep 6760907 = 10141361) B10141361
theorem B4507271 : Blo 2001435 4507271 := bstep (se 1 (by rfl) ⟨3380453, by rfl⟩ : syracuseStep 4507271 = 6760907) B6760907
theorem B3004847 : Blo 2001435 3004847 := bstep (se 1 (by rfl) ⟨2253635, by rfl⟩ : syracuseStep 3004847 = 4507271) B4507271
theorem B2003231 : Blo 2001435 2003231 := bstep (se 1 (by rfl) ⟨1502423, by rfl⟩ : syracuseStep 2003231 = 3004847) B3004847
theorem B3004853 : Blo 2001435 3004853 := bbase (se 5 (by rfl) ⟨140852, by rfl⟩ : syracuseStep 3004853 = 281705) (by norm_num)
theorem B2003235 : Blo 2001435 2003235 := bstep (se 1 (by rfl) ⟨1502426, by rfl⟩ : syracuseStep 2003235 = 3004853) B3004853
theorem B5070701 : Blo 2001435 5070701 := bbase (se 3 (by rfl) ⟨950756, by rfl⟩ : syracuseStep 5070701 = 1901513) (by norm_num)
theorem B3380467 : Blo 2001435 3380467 := bstep (se 1 (by rfl) ⟨2535350, by rfl⟩ : syracuseStep 3380467 = 5070701) B5070701
theorem B4507289 : Blo 2001435 4507289 := bstep (se 2 (by rfl) ⟨1690233, by rfl⟩ : syracuseStep 4507289 = 3380467) B3380467
theorem B3004859 : Blo 2001435 3004859 := bstep (se 1 (by rfl) ⟨2253644, by rfl⟩ : syracuseStep 3004859 = 4507289) B4507289
theorem B2003239 : Blo 2001435 2003239 := bstep (se 1 (by rfl) ⟨1502429, by rfl⟩ : syracuseStep 2003239 = 3004859) B3004859
theorem B2253649 : Blo 2001435 2253649 := bbase (se 2 (by rfl) ⟨845118, by rfl⟩ : syracuseStep 2253649 = 1690237) (by norm_num)
theorem B3004865 : Blo 2001435 3004865 := bstep (se 2 (by rfl) ⟨1126824, by rfl⟩ : syracuseStep 3004865 = 2253649) B2253649
theorem B2003243 : Blo 2001435 2003243 := bstep (se 1 (by rfl) ⟨1502432, by rfl⟩ : syracuseStep 2003243 = 3004865) B3004865
theorem B2406613 : Blo 2001435 2406613 := bbase (se 7 (by rfl) ⟨28202, by rfl⟩ : syracuseStep 2406613 = 56405) (by norm_num)
theorem B3208817 : Blo 2001435 3208817 := bstep (se 2 (by rfl) ⟨1203306, by rfl⟩ : syracuseStep 3208817 = 2406613) B2406613
theorem B2139211 : Blo 2001435 2139211 := bstep (se 1 (by rfl) ⟨1604408, by rfl⟩ : syracuseStep 2139211 = 3208817) B3208817
theorem B2852281 : Blo 2001435 2852281 := bstep (se 2 (by rfl) ⟨1069605, by rfl⟩ : syracuseStep 2852281 = 2139211) B2139211
theorem B3803041 : Blo 2001435 3803041 := bstep (se 2 (by rfl) ⟨1426140, by rfl⟩ : syracuseStep 3803041 = 2852281) B2852281
theorem B5070721 : Blo 2001435 5070721 := bstep (se 2 (by rfl) ⟨1901520, by rfl⟩ : syracuseStep 5070721 = 3803041) B3803041
theorem B6760961 : Blo 2001435 6760961 := bstep (se 2 (by rfl) ⟨2535360, by rfl⟩ : syracuseStep 6760961 = 5070721) B5070721
theorem B4507307 : Blo 2001435 4507307 := bstep (se 1 (by rfl) ⟨3380480, by rfl⟩ : syracuseStep 4507307 = 6760961) B6760961
theorem B3004871 : Blo 2001435 3004871 := bstep (se 1 (by rfl) ⟨2253653, by rfl⟩ : syracuseStep 3004871 = 4507307) B4507307
theorem B2003247 : Blo 2001435 2003247 := bstep (se 1 (by rfl) ⟨1502435, by rfl⟩ : syracuseStep 2003247 = 3004871) B3004871
theorem B3004877 : Blo 2001435 3004877 := bbase (se 3 (by rfl) ⟨563414, by rfl⟩ : syracuseStep 3004877 = 1126829) (by norm_num)
theorem B2003251 : Blo 2001435 2003251 := bstep (se 1 (by rfl) ⟨1502438, by rfl⟩ : syracuseStep 2003251 = 3004877) B3004877
theorem B4507325 : Blo 2001435 4507325 := bbase (se 3 (by rfl) ⟨845123, by rfl⟩ : syracuseStep 4507325 = 1690247) (by norm_num)
theorem B3004883 : Blo 2001435 3004883 := bstep (se 1 (by rfl) ⟨2253662, by rfl⟩ : syracuseStep 3004883 = 4507325) B4507325
theorem B2003255 : Blo 2001435 2003255 := bstep (se 1 (by rfl) ⟨1502441, by rfl⟩ : syracuseStep 2003255 = 3004883) B3004883
theorem B3380501 : Blo 2001435 3380501 := bbase (se 6 (by rfl) ⟨79230, by rfl⟩ : syracuseStep 3380501 = 158461) (by norm_num)
theorem B2253667 : Blo 2001435 2253667 := bstep (se 1 (by rfl) ⟨1690250, by rfl⟩ : syracuseStep 2253667 = 3380501) B3380501
theorem B3004889 : Blo 2001435 3004889 := bstep (se 2 (by rfl) ⟨1126833, by rfl⟩ : syracuseStep 3004889 = 2253667) B2253667
theorem B2003259 : Blo 2001435 2003259 := bstep (se 1 (by rfl) ⟨1502444, by rfl⟩ : syracuseStep 2003259 = 3004889) B3004889
theorem B3045893 : Blo 2001435 3045893 := bbase (se 4 (by rfl) ⟨285552, by rfl⟩ : syracuseStep 3045893 = 571105) (by norm_num)
theorem B32489525 : Blo 2001435 32489525 := bstep (se 5 (by rfl) ⟨1522946, by rfl⟩ : syracuseStep 32489525 = 3045893) B3045893
theorem B21659683 : Blo 2001435 21659683 := bstep (se 1 (by rfl) ⟨16244762, by rfl⟩ : syracuseStep 21659683 = 32489525) B32489525
theorem B28879577 : Blo 2001435 28879577 := bstep (se 2 (by rfl) ⟨10829841, by rfl⟩ : syracuseStep 28879577 = 21659683) B21659683
theorem B19253051 : Blo 2001435 19253051 := bstep (se 1 (by rfl) ⟨14439788, by rfl⟩ : syracuseStep 19253051 = 28879577) B28879577
theorem B12835367 : Blo 2001435 12835367 := bstep (se 1 (by rfl) ⟨9626525, by rfl⟩ : syracuseStep 12835367 = 19253051) B19253051
theorem B8556911 : Blo 2001435 8556911 := bstep (se 1 (by rfl) ⟨6417683, by rfl⟩ : syracuseStep 8556911 = 12835367) B12835367
theorem B5704607 : Blo 2001435 5704607 := bstep (se 1 (by rfl) ⟨4278455, by rfl⟩ : syracuseStep 5704607 = 8556911) B8556911
theorem B15212285 : Blo 2001435 15212285 := bstep (se 3 (by rfl) ⟨2852303, by rfl⟩ : syracuseStep 15212285 = 5704607) B5704607
theorem B10141523 : Blo 2001435 10141523 := bstep (se 1 (by rfl) ⟨7606142, by rfl⟩ : syracuseStep 10141523 = 15212285) B15212285
theorem B6761015 : Blo 2001435 6761015 := bstep (se 1 (by rfl) ⟨5070761, by rfl⟩ : syracuseStep 6761015 = 10141523) B10141523
theorem B4507343 : Blo 2001435 4507343 := bstep (se 1 (by rfl) ⟨3380507, by rfl⟩ : syracuseStep 4507343 = 6761015) B6761015
theorem B3004895 : Blo 2001435 3004895 := bstep (se 1 (by rfl) ⟨2253671, by rfl⟩ : syracuseStep 3004895 = 4507343) B4507343
theorem B2003263 : Blo 2001435 2003263 := bstep (se 1 (by rfl) ⟨1502447, by rfl⟩ : syracuseStep 2003263 = 3004895) B3004895
theorem B3004901 : Blo 2001435 3004901 := bbase (se 4 (by rfl) ⟨281709, by rfl⟩ : syracuseStep 3004901 = 563419) (by norm_num)
theorem B2003267 : Blo 2001435 2003267 := bstep (se 1 (by rfl) ⟨1502450, by rfl⟩ : syracuseStep 2003267 = 3004901) B3004901
theorem B7219925 : Blo 2001435 7219925 := bbase (se 7 (by rfl) ⟨84608, by rfl⟩ : syracuseStep 7219925 = 169217) (by norm_num)
theorem B4813283 : Blo 2001435 4813283 := bstep (se 1 (by rfl) ⟨3609962, by rfl⟩ : syracuseStep 4813283 = 7219925) B7219925
theorem B12835421 : Blo 2001435 12835421 := bstep (se 3 (by rfl) ⟨2406641, by rfl⟩ : syracuseStep 12835421 = 4813283) B4813283
theorem B8556947 : Blo 2001435 8556947 := bstep (se 1 (by rfl) ⟨6417710, by rfl⟩ : syracuseStep 8556947 = 12835421) B12835421
theorem B5704631 : Blo 2001435 5704631 := bstep (se 1 (by rfl) ⟨4278473, by rfl⟩ : syracuseStep 5704631 = 8556947) B8556947
theorem B3803087 : Blo 2001435 3803087 := bstep (se 1 (by rfl) ⟨2852315, by rfl⟩ : syracuseStep 3803087 = 5704631) B5704631
theorem B2535391 : Blo 2001435 2535391 := bstep (se 1 (by rfl) ⟨1901543, by rfl⟩ : syracuseStep 2535391 = 3803087) B3803087
theorem B3380521 : Blo 2001435 3380521 := bstep (se 2 (by rfl) ⟨1267695, by rfl⟩ : syracuseStep 3380521 = 2535391) B2535391
theorem B4507361 : Blo 2001435 4507361 := bstep (se 2 (by rfl) ⟨1690260, by rfl⟩ : syracuseStep 4507361 = 3380521) B3380521
theorem B3004907 : Blo 2001435 3004907 := bstep (se 1 (by rfl) ⟨2253680, by rfl⟩ : syracuseStep 3004907 = 4507361) B4507361
theorem B2003271 : Blo 2001435 2003271 := bstep (se 1 (by rfl) ⟨1502453, by rfl⟩ : syracuseStep 2003271 = 3004907) B3004907
theorem B2253685 : Blo 2001435 2253685 := bbase (se 5 (by rfl) ⟨105641, by rfl⟩ : syracuseStep 2253685 = 211283) (by norm_num)
theorem B3004913 : Blo 2001435 3004913 := bstep (se 2 (by rfl) ⟨1126842, by rfl⟩ : syracuseStep 3004913 = 2253685) B2253685
theorem B2003275 : Blo 2001435 2003275 := bstep (se 1 (by rfl) ⟨1502456, by rfl⟩ : syracuseStep 2003275 = 3004913) B3004913
theorem B2535401 : Blo 2001435 2535401 := bbase (se 2 (by rfl) ⟨950775, by rfl⟩ : syracuseStep 2535401 = 1901551) (by norm_num)
theorem B6761069 : Blo 2001435 6761069 := bstep (se 3 (by rfl) ⟨1267700, by rfl⟩ : syracuseStep 6761069 = 2535401) B2535401
theorem B4507379 : Blo 2001435 4507379 := bstep (se 1 (by rfl) ⟨3380534, by rfl⟩ : syracuseStep 4507379 = 6761069) B6761069
theorem B3004919 : Blo 2001435 3004919 := bstep (se 1 (by rfl) ⟨2253689, by rfl⟩ : syracuseStep 3004919 = 4507379) B4507379
theorem B2003279 : Blo 2001435 2003279 := bstep (se 1 (by rfl) ⟨1502459, by rfl⟩ : syracuseStep 2003279 = 3004919) B3004919
theorem B3004925 : Blo 2001435 3004925 := bbase (se 3 (by rfl) ⟨563423, by rfl⟩ : syracuseStep 3004925 = 1126847) (by norm_num)
theorem B2003283 : Blo 2001435 2003283 := bstep (se 1 (by rfl) ⟨1502462, by rfl⟩ : syracuseStep 2003283 = 3004925) B3004925
theorem B4507397 : Blo 2001435 4507397 := bbase (se 4 (by rfl) ⟨422568, by rfl⟩ : syracuseStep 4507397 = 845137) (by norm_num)
theorem B3004931 : Blo 2001435 3004931 := bstep (se 1 (by rfl) ⟨2253698, by rfl⟩ : syracuseStep 3004931 = 4507397) B4507397
theorem B2003287 : Blo 2001435 2003287 := bstep (se 1 (by rfl) ⟨1502465, by rfl⟩ : syracuseStep 2003287 = 3004931) B3004931
theorem B3803125 : Blo 2001435 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B5070833 : Blo 2001435 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B3380555 : Blo 2001435 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B2253703 : Blo 2001435 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B3004937 : Blo 2001435 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B2003291 : Blo 2001435 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B10141685 : Blo 2001435 10141685 := bbase (se 5 (by rfl) ⟨475391, by rfl⟩ : syracuseStep 10141685 = 950783) (by norm_num)
theorem B6761123 : Blo 2001435 6761123 := bstep (se 1 (by rfl) ⟨5070842, by rfl⟩ : syracuseStep 6761123 = 10141685) B10141685
theorem B4507415 : Blo 2001435 4507415 := bstep (se 1 (by rfl) ⟨3380561, by rfl⟩ : syracuseStep 4507415 = 6761123) B6761123
theorem B3004943 : Blo 2001435 3004943 := bstep (se 1 (by rfl) ⟨2253707, by rfl⟩ : syracuseStep 3004943 = 4507415) B4507415
theorem B2003295 : Blo 2001435 2003295 := bstep (se 1 (by rfl) ⟨1502471, by rfl⟩ : syracuseStep 2003295 = 3004943) B3004943
theorem B3004949 : Blo 2001435 3004949 := bbase (se 6 (by rfl) ⟨70428, by rfl⟩ : syracuseStep 3004949 = 140857) (by norm_num)
theorem B2003299 : Blo 2001435 2003299 := bstep (se 1 (by rfl) ⟨1502474, by rfl⟩ : syracuseStep 2003299 = 3004949) B3004949
theorem B17114165 : Blo 2001435 17114165 := bbase (se 5 (by rfl) ⟨802226, by rfl⟩ : syracuseStep 17114165 = 1604453) (by norm_num)
theorem B11409443 : Blo 2001435 11409443 := bstep (se 1 (by rfl) ⟨8557082, by rfl⟩ : syracuseStep 11409443 = 17114165) B17114165
theorem B7606295 : Blo 2001435 7606295 := bstep (se 1 (by rfl) ⟨5704721, by rfl⟩ : syracuseStep 7606295 = 11409443) B11409443
theorem B5070863 : Blo 2001435 5070863 := bstep (se 1 (by rfl) ⟨3803147, by rfl⟩ : syracuseStep 5070863 = 7606295) B7606295
theorem B3380575 : Blo 2001435 3380575 := bstep (se 1 (by rfl) ⟨2535431, by rfl⟩ : syracuseStep 3380575 = 5070863) B5070863
theorem B4507433 : Blo 2001435 4507433 := bstep (se 2 (by rfl) ⟨1690287, by rfl⟩ : syracuseStep 4507433 = 3380575) B3380575
theorem B3004955 : Blo 2001435 3004955 := bstep (se 1 (by rfl) ⟨2253716, by rfl⟩ : syracuseStep 3004955 = 4507433) B4507433
theorem B2003303 : Blo 2001435 2003303 := bstep (se 1 (by rfl) ⟨1502477, by rfl⟩ : syracuseStep 2003303 = 3004955) B3004955
theorem B2253721 : Blo 2001435 2253721 := bbase (se 2 (by rfl) ⟨845145, by rfl⟩ : syracuseStep 2253721 = 1690291) (by norm_num)
theorem B3004961 : Blo 2001435 3004961 := bstep (se 2 (by rfl) ⟨1126860, by rfl⟩ : syracuseStep 3004961 = 2253721) B2253721
theorem B2003307 : Blo 2001435 2003307 := bstep (se 1 (by rfl) ⟨1502480, by rfl⟩ : syracuseStep 2003307 = 3004961) B3004961
theorem B7606325 : Blo 2001435 7606325 := bbase (se 5 (by rfl) ⟨356546, by rfl⟩ : syracuseStep 7606325 = 713093) (by norm_num)
theorem B5070883 : Blo 2001435 5070883 := bstep (se 1 (by rfl) ⟨3803162, by rfl⟩ : syracuseStep 5070883 = 7606325) B7606325
theorem B6761177 : Blo 2001435 6761177 := bstep (se 2 (by rfl) ⟨2535441, by rfl⟩ : syracuseStep 6761177 = 5070883) B5070883
theorem B4507451 : Blo 2001435 4507451 := bstep (se 1 (by rfl) ⟨3380588, by rfl⟩ : syracuseStep 4507451 = 6761177) B6761177
theorem B3004967 : Blo 2001435 3004967 := bstep (se 1 (by rfl) ⟨2253725, by rfl⟩ : syracuseStep 3004967 = 4507451) B4507451
theorem B2003311 : Blo 2001435 2003311 := bstep (se 1 (by rfl) ⟨1502483, by rfl⟩ : syracuseStep 2003311 = 3004967) B3004967
theorem B3004973 : Blo 2001435 3004973 := bbase (se 3 (by rfl) ⟨563432, by rfl⟩ : syracuseStep 3004973 = 1126865) (by norm_num)
theorem B2003315 : Blo 2001435 2003315 := bstep (se 1 (by rfl) ⟨1502486, by rfl⟩ : syracuseStep 2003315 = 3004973) B3004973
theorem B4507469 : Blo 2001435 4507469 := bbase (se 3 (by rfl) ⟨845150, by rfl⟩ : syracuseStep 4507469 = 1690301) (by norm_num)
theorem B3004979 : Blo 2001435 3004979 := bstep (se 1 (by rfl) ⟨2253734, by rfl⟩ : syracuseStep 3004979 = 4507469) B4507469
theorem B2003319 : Blo 2001435 2003319 := bstep (se 1 (by rfl) ⟨1502489, by rfl⟩ : syracuseStep 2003319 = 3004979) B3004979
theorem B2535457 : Blo 2001435 2535457 := bbase (se 2 (by rfl) ⟨950796, by rfl⟩ : syracuseStep 2535457 = 1901593) (by norm_num)
theorem B3380609 : Blo 2001435 3380609 := bstep (se 2 (by rfl) ⟨1267728, by rfl⟩ : syracuseStep 3380609 = 2535457) B2535457
theorem B2253739 : Blo 2001435 2253739 := bstep (se 1 (by rfl) ⟨1690304, by rfl⟩ : syracuseStep 2253739 = 3380609) B3380609
theorem B3004985 : Blo 2001435 3004985 := bstep (se 2 (by rfl) ⟨1126869, by rfl⟩ : syracuseStep 3004985 = 2253739) B2253739
theorem B2003323 : Blo 2001435 2003323 := bstep (se 1 (by rfl) ⟨1502492, by rfl⟩ : syracuseStep 2003323 = 3004985) B3004985
theorem B22819157 : Blo 2001435 22819157 := bbase (se 10 (by rfl) ⟨33426, by rfl⟩ : syracuseStep 22819157 = 66853) (by norm_num)
theorem B15212771 : Blo 2001435 15212771 := bstep (se 1 (by rfl) ⟨11409578, by rfl⟩ : syracuseStep 15212771 = 22819157) B22819157
theorem B10141847 : Blo 2001435 10141847 := bstep (se 1 (by rfl) ⟨7606385, by rfl⟩ : syracuseStep 10141847 = 15212771) B15212771
theorem B6761231 : Blo 2001435 6761231 := bstep (se 1 (by rfl) ⟨5070923, by rfl⟩ : syracuseStep 6761231 = 10141847) B10141847
theorem B4507487 : Blo 2001435 4507487 := bstep (se 1 (by rfl) ⟨3380615, by rfl⟩ : syracuseStep 4507487 = 6761231) B6761231
theorem B3004991 : Blo 2001435 3004991 := bstep (se 1 (by rfl) ⟨2253743, by rfl⟩ : syracuseStep 3004991 = 4507487) B4507487
theorem B2003327 : Blo 2001435 2003327 := bstep (se 1 (by rfl) ⟨1502495, by rfl⟩ : syracuseStep 2003327 = 3004991) B3004991
theorem B3004997 : Blo 2001435 3004997 := bbase (se 4 (by rfl) ⟨281718, by rfl⟩ : syracuseStep 3004997 = 563437) (by norm_num)
theorem B2003331 : Blo 2001435 2003331 := bstep (se 1 (by rfl) ⟨1502498, by rfl⟩ : syracuseStep 2003331 = 3004997) B3004997
theorem B3380629 : Blo 2001435 3380629 := bbase (se 6 (by rfl) ⟨79233, by rfl⟩ : syracuseStep 3380629 = 158467) (by norm_num)
theorem B4507505 : Blo 2001435 4507505 := bstep (se 2 (by rfl) ⟨1690314, by rfl⟩ : syracuseStep 4507505 = 3380629) B3380629
theorem B3005003 : Blo 2001435 3005003 := bstep (se 1 (by rfl) ⟨2253752, by rfl⟩ : syracuseStep 3005003 = 4507505) B4507505
theorem B2003335 : Blo 2001435 2003335 := bstep (se 1 (by rfl) ⟨1502501, by rfl⟩ : syracuseStep 2003335 = 3005003) B3005003
theorem B2253757 : Blo 2001435 2253757 := bbase (se 3 (by rfl) ⟨422579, by rfl⟩ : syracuseStep 2253757 = 845159) (by norm_num)
theorem B3005009 : Blo 2001435 3005009 := bstep (se 2 (by rfl) ⟨1126878, by rfl⟩ : syracuseStep 3005009 = 2253757) B2253757
theorem B2003339 : Blo 2001435 2003339 := bstep (se 1 (by rfl) ⟨1502504, by rfl⟩ : syracuseStep 2003339 = 3005009) B3005009
theorem B6761285 : Blo 2001435 6761285 := bbase (se 4 (by rfl) ⟨633870, by rfl⟩ : syracuseStep 6761285 = 1267741) (by norm_num)
theorem B4507523 : Blo 2001435 4507523 := bstep (se 1 (by rfl) ⟨3380642, by rfl⟩ : syracuseStep 4507523 = 6761285) B6761285
theorem B3005015 : Blo 2001435 3005015 := bstep (se 1 (by rfl) ⟨2253761, by rfl⟩ : syracuseStep 3005015 = 4507523) B4507523
theorem B2003343 : Blo 2001435 2003343 := bstep (se 1 (by rfl) ⟨1502507, by rfl⟩ : syracuseStep 2003343 = 3005015) B3005015
theorem B3005021 : Blo 2001435 3005021 := bbase (se 3 (by rfl) ⟨563441, by rfl⟩ : syracuseStep 3005021 = 1126883) (by norm_num)
theorem B2003347 : Blo 2001435 2003347 := bstep (se 1 (by rfl) ⟨1502510, by rfl⟩ : syracuseStep 2003347 = 3005021) B3005021
theorem B4507541 : Blo 2001435 4507541 := bbase (se 6 (by rfl) ⟨105645, by rfl⟩ : syracuseStep 4507541 = 211291) (by norm_num)
theorem B3005027 : Blo 2001435 3005027 := bstep (se 1 (by rfl) ⟨2253770, by rfl⟩ : syracuseStep 3005027 = 4507541) B4507541
theorem B2003351 : Blo 2001435 2003351 := bstep (se 1 (by rfl) ⟨1502513, by rfl⟩ : syracuseStep 2003351 = 3005027) B3005027
theorem B4278653 : Blo 2001435 4278653 := bbase (se 3 (by rfl) ⟨802247, by rfl⟩ : syracuseStep 4278653 = 1604495) (by norm_num)
theorem B2852435 : Blo 2001435 2852435 := bstep (se 1 (by rfl) ⟨2139326, by rfl⟩ : syracuseStep 2852435 = 4278653) B4278653
theorem B7606493 : Blo 2001435 7606493 := bstep (se 3 (by rfl) ⟨1426217, by rfl⟩ : syracuseStep 7606493 = 2852435) B2852435
theorem B5070995 : Blo 2001435 5070995 := bstep (se 1 (by rfl) ⟨3803246, by rfl⟩ : syracuseStep 5070995 = 7606493) B7606493
theorem B3380663 : Blo 2001435 3380663 := bstep (se 1 (by rfl) ⟨2535497, by rfl⟩ : syracuseStep 3380663 = 5070995) B5070995
theorem B2253775 : Blo 2001435 2253775 := bstep (se 1 (by rfl) ⟨1690331, by rfl⟩ : syracuseStep 2253775 = 3380663) B3380663
theorem B3005033 : Blo 2001435 3005033 := bstep (se 2 (by rfl) ⟨1126887, by rfl⟩ : syracuseStep 3005033 = 2253775) B2253775
theorem B2003355 : Blo 2001435 2003355 := bstep (se 1 (by rfl) ⟨1502516, by rfl⟩ : syracuseStep 2003355 = 3005033) B3005033
theorem B6853589 : Blo 2001435 6853589 := bbase (se 7 (by rfl) ⟨80315, by rfl⟩ : syracuseStep 6853589 = 160631) (by norm_num)
theorem B4569059 : Blo 2001435 4569059 := bstep (se 1 (by rfl) ⟨3426794, by rfl⟩ : syracuseStep 4569059 = 6853589) B6853589
theorem B12184157 : Blo 2001435 12184157 := bstep (se 3 (by rfl) ⟨2284529, by rfl⟩ : syracuseStep 12184157 = 4569059) B4569059
theorem B8122771 : Blo 2001435 8122771 := bstep (se 1 (by rfl) ⟨6092078, by rfl⟩ : syracuseStep 8122771 = 12184157) B12184157
theorem B10830361 : Blo 2001435 10830361 := bstep (se 2 (by rfl) ⟨4061385, by rfl⟩ : syracuseStep 10830361 = 8122771) B8122771
theorem B14440481 : Blo 2001435 14440481 := bstep (se 2 (by rfl) ⟨5415180, by rfl⟩ : syracuseStep 14440481 = 10830361) B10830361
theorem B9626987 : Blo 2001435 9626987 := bstep (se 1 (by rfl) ⟨7220240, by rfl⟩ : syracuseStep 9626987 = 14440481) B14440481
theorem B6417991 : Blo 2001435 6417991 := bstep (se 1 (by rfl) ⟨4813493, by rfl⟩ : syracuseStep 6417991 = 9626987) B9626987
theorem B8557321 : Blo 2001435 8557321 := bstep (se 2 (by rfl) ⟨3208995, by rfl⟩ : syracuseStep 8557321 = 6417991) B6417991
theorem B11409761 : Blo 2001435 11409761 := bstep (se 2 (by rfl) ⟨4278660, by rfl⟩ : syracuseStep 11409761 = 8557321) B8557321
theorem B7606507 : Blo 2001435 7606507 := bstep (se 1 (by rfl) ⟨5704880, by rfl⟩ : syracuseStep 7606507 = 11409761) B11409761
theorem B10142009 : Blo 2001435 10142009 := bstep (se 2 (by rfl) ⟨3803253, by rfl⟩ : syracuseStep 10142009 = 7606507) B7606507
theorem B6761339 : Blo 2001435 6761339 := bstep (se 1 (by rfl) ⟨5071004, by rfl⟩ : syracuseStep 6761339 = 10142009) B10142009
theorem B4507559 : Blo 2001435 4507559 := bstep (se 1 (by rfl) ⟨3380669, by rfl⟩ : syracuseStep 4507559 = 6761339) B6761339
theorem B3005039 : Blo 2001435 3005039 := bstep (se 1 (by rfl) ⟨2253779, by rfl⟩ : syracuseStep 3005039 = 4507559) B4507559
theorem B2003359 : Blo 2001435 2003359 := bstep (se 1 (by rfl) ⟨1502519, by rfl⟩ : syracuseStep 2003359 = 3005039) B3005039
theorem B3005045 : Blo 2001435 3005045 := bbase (se 5 (by rfl) ⟨140861, by rfl⟩ : syracuseStep 3005045 = 281723) (by norm_num)
theorem B2003363 : Blo 2001435 2003363 := bstep (se 1 (by rfl) ⟨1502522, by rfl⟩ : syracuseStep 2003363 = 3005045) B3005045
theorem B3803269 : Blo 2001435 3803269 := bbase (se 4 (by rfl) ⟨356556, by rfl⟩ : syracuseStep 3803269 = 713113) (by norm_num)
theorem B5071025 : Blo 2001435 5071025 := bstep (se 2 (by rfl) ⟨1901634, by rfl⟩ : syracuseStep 5071025 = 3803269) B3803269
theorem B3380683 : Blo 2001435 3380683 := bstep (se 1 (by rfl) ⟨2535512, by rfl⟩ : syracuseStep 3380683 = 5071025) B5071025
theorem B4507577 : Blo 2001435 4507577 := bstep (se 2 (by rfl) ⟨1690341, by rfl⟩ : syracuseStep 4507577 = 3380683) B3380683
theorem B3005051 : Blo 2001435 3005051 := bstep (se 1 (by rfl) ⟨2253788, by rfl⟩ : syracuseStep 3005051 = 4507577) B4507577
theorem B2003367 : Blo 2001435 2003367 := bstep (se 1 (by rfl) ⟨1502525, by rfl⟩ : syracuseStep 2003367 = 3005051) B3005051
theorem B2253793 : Blo 2001435 2253793 := bbase (se 2 (by rfl) ⟨845172, by rfl⟩ : syracuseStep 2253793 = 1690345) (by norm_num)
theorem B3005057 : Blo 2001435 3005057 := bstep (se 2 (by rfl) ⟨1126896, by rfl⟩ : syracuseStep 3005057 = 2253793) B2253793
theorem B2003371 : Blo 2001435 2003371 := bstep (se 1 (by rfl) ⟨1502528, by rfl⟩ : syracuseStep 2003371 = 3005057) B3005057
theorem B5071045 : Blo 2001435 5071045 := bbase (se 4 (by rfl) ⟨475410, by rfl⟩ : syracuseStep 5071045 = 950821) (by norm_num)
theorem B6761393 : Blo 2001435 6761393 := bstep (se 2 (by rfl) ⟨2535522, by rfl⟩ : syracuseStep 6761393 = 5071045) B5071045
theorem B4507595 : Blo 2001435 4507595 := bstep (se 1 (by rfl) ⟨3380696, by rfl⟩ : syracuseStep 4507595 = 6761393) B6761393
theorem B3005063 : Blo 2001435 3005063 := bstep (se 1 (by rfl) ⟨2253797, by rfl⟩ : syracuseStep 3005063 = 4507595) B4507595
theorem B2003375 : Blo 2001435 2003375 := bstep (se 1 (by rfl) ⟨1502531, by rfl⟩ : syracuseStep 2003375 = 3005063) B3005063
theorem B3005069 : Blo 2001435 3005069 := bbase (se 3 (by rfl) ⟨563450, by rfl⟩ : syracuseStep 3005069 = 1126901) (by norm_num)
theorem B2003379 : Blo 2001435 2003379 := bstep (se 1 (by rfl) ⟨1502534, by rfl⟩ : syracuseStep 2003379 = 3005069) B3005069
theorem B4507613 : Blo 2001435 4507613 := bbase (se 3 (by rfl) ⟨845177, by rfl⟩ : syracuseStep 4507613 = 1690355) (by norm_num)
theorem B3005075 : Blo 2001435 3005075 := bstep (se 1 (by rfl) ⟨2253806, by rfl⟩ : syracuseStep 3005075 = 4507613) B4507613
theorem B2003383 : Blo 2001435 2003383 := bstep (se 1 (by rfl) ⟨1502537, by rfl⟩ : syracuseStep 2003383 = 3005075) B3005075
theorem B3380717 : Blo 2001435 3380717 := bbase (se 3 (by rfl) ⟨633884, by rfl⟩ : syracuseStep 3380717 = 1267769) (by norm_num)
theorem B2253811 : Blo 2001435 2253811 := bstep (se 1 (by rfl) ⟨1690358, by rfl⟩ : syracuseStep 2253811 = 3380717) B3380717
theorem B3005081 : Blo 2001435 3005081 := bstep (se 2 (by rfl) ⟨1126905, by rfl⟩ : syracuseStep 3005081 = 2253811) B2253811
theorem B2003387 : Blo 2001435 2003387 := bstep (se 1 (by rfl) ⟨1502540, by rfl⟩ : syracuseStep 2003387 = 3005081) B3005081
theorem B2406785 : Blo 2001435 2406785 := bbase (se 2 (by rfl) ⟨902544, by rfl⟩ : syracuseStep 2406785 = 1805089) (by norm_num)
theorem B25672373 : Blo 2001435 25672373 := bstep (se 5 (by rfl) ⟨1203392, by rfl⟩ : syracuseStep 25672373 = 2406785) B2406785
theorem B17114915 : Blo 2001435 17114915 := bstep (se 1 (by rfl) ⟨12836186, by rfl⟩ : syracuseStep 17114915 = 25672373) B25672373
theorem B11409943 : Blo 2001435 11409943 := bstep (se 1 (by rfl) ⟨8557457, by rfl⟩ : syracuseStep 11409943 = 17114915) B17114915
theorem B15213257 : Blo 2001435 15213257 := bstep (se 2 (by rfl) ⟨5704971, by rfl⟩ : syracuseStep 15213257 = 11409943) B11409943
theorem B10142171 : Blo 2001435 10142171 := bstep (se 1 (by rfl) ⟨7606628, by rfl⟩ : syracuseStep 10142171 = 15213257) B15213257
theorem B6761447 : Blo 2001435 6761447 := bstep (se 1 (by rfl) ⟨5071085, by rfl⟩ : syracuseStep 6761447 = 10142171) B10142171
theorem B4507631 : Blo 2001435 4507631 := bstep (se 1 (by rfl) ⟨3380723, by rfl⟩ : syracuseStep 4507631 = 6761447) B6761447
theorem B3005087 : Blo 2001435 3005087 := bstep (se 1 (by rfl) ⟨2253815, by rfl⟩ : syracuseStep 3005087 = 4507631) B4507631
theorem B2003391 : Blo 2001435 2003391 := bstep (se 1 (by rfl) ⟨1502543, by rfl⟩ : syracuseStep 2003391 = 3005087) B3005087
theorem B3005093 : Blo 2001435 3005093 := bbase (se 4 (by rfl) ⟨281727, by rfl⟩ : syracuseStep 3005093 = 563455) (by norm_num)
theorem B2003395 : Blo 2001435 2003395 := bstep (se 1 (by rfl) ⟨1502546, by rfl⟩ : syracuseStep 2003395 = 3005093) B3005093
theorem B2535553 : Blo 2001435 2535553 := bbase (se 2 (by rfl) ⟨950832, by rfl⟩ : syracuseStep 2535553 = 1901665) (by norm_num)
theorem B3380737 : Blo 2001435 3380737 := bstep (se 2 (by rfl) ⟨1267776, by rfl⟩ : syracuseStep 3380737 = 2535553) B2535553
theorem B4507649 : Blo 2001435 4507649 := bstep (se 2 (by rfl) ⟨1690368, by rfl⟩ : syracuseStep 4507649 = 3380737) B3380737
theorem B3005099 : Blo 2001435 3005099 := bstep (se 1 (by rfl) ⟨2253824, by rfl⟩ : syracuseStep 3005099 = 4507649) B4507649
theorem B2003399 : Blo 2001435 2003399 := bstep (se 1 (by rfl) ⟨1502549, by rfl⟩ : syracuseStep 2003399 = 3005099) B3005099
theorem B2253829 : Blo 2001435 2253829 := bbase (se 4 (by rfl) ⟨211296, by rfl⟩ : syracuseStep 2253829 = 422593) (by norm_num)
theorem B3005105 : Blo 2001435 3005105 := bstep (se 2 (by rfl) ⟨1126914, by rfl⟩ : syracuseStep 3005105 = 2253829) B2253829
theorem B2003403 : Blo 2001435 2003403 := bstep (se 1 (by rfl) ⟨1502552, by rfl⟩ : syracuseStep 2003403 = 3005105) B3005105
theorem B2852509 : Blo 2001435 2852509 := bbase (se 3 (by rfl) ⟨534845, by rfl⟩ : syracuseStep 2852509 = 1069691) (by norm_num)
theorem B3803345 : Blo 2001435 3803345 := bstep (se 2 (by rfl) ⟨1426254, by rfl⟩ : syracuseStep 3803345 = 2852509) B2852509
theorem B2535563 : Blo 2001435 2535563 := bstep (se 1 (by rfl) ⟨1901672, by rfl⟩ : syracuseStep 2535563 = 3803345) B3803345
theorem B6761501 : Blo 2001435 6761501 := bstep (se 3 (by rfl) ⟨1267781, by rfl⟩ : syracuseStep 6761501 = 2535563) B2535563
theorem B4507667 : Blo 2001435 4507667 := bstep (se 1 (by rfl) ⟨3380750, by rfl⟩ : syracuseStep 4507667 = 6761501) B6761501
theorem B3005111 : Blo 2001435 3005111 := bstep (se 1 (by rfl) ⟨2253833, by rfl⟩ : syracuseStep 3005111 = 4507667) B4507667
theorem B2003407 : Blo 2001435 2003407 := bstep (se 1 (by rfl) ⟨1502555, by rfl⟩ : syracuseStep 2003407 = 3005111) B3005111
theorem B3005117 : Blo 2001435 3005117 := bbase (se 3 (by rfl) ⟨563459, by rfl⟩ : syracuseStep 3005117 = 1126919) (by norm_num)
theorem B2003411 : Blo 2001435 2003411 := bstep (se 1 (by rfl) ⟨1502558, by rfl⟩ : syracuseStep 2003411 = 3005117) B3005117
theorem B4507685 : Blo 2001435 4507685 := bbase (se 4 (by rfl) ⟨422595, by rfl⟩ : syracuseStep 4507685 = 845191) (by norm_num)
theorem B3005123 : Blo 2001435 3005123 := bstep (se 1 (by rfl) ⟨2253842, by rfl⟩ : syracuseStep 3005123 = 4507685) B4507685
theorem B2003415 : Blo 2001435 2003415 := bstep (se 1 (by rfl) ⟨1502561, by rfl⟩ : syracuseStep 2003415 = 3005123) B3005123
theorem B5071157 : Blo 2001435 5071157 := bbase (se 5 (by rfl) ⟨237710, by rfl⟩ : syracuseStep 5071157 = 475421) (by norm_num)
theorem B3380771 : Blo 2001435 3380771 := bstep (se 1 (by rfl) ⟨2535578, by rfl⟩ : syracuseStep 3380771 = 5071157) B5071157
theorem B2253847 : Blo 2001435 2253847 := bstep (se 1 (by rfl) ⟨1690385, by rfl⟩ : syracuseStep 2253847 = 3380771) B3380771
theorem B3005129 : Blo 2001435 3005129 := bstep (se 2 (by rfl) ⟨1126923, by rfl⟩ : syracuseStep 3005129 = 2253847) B2253847
theorem B2003419 : Blo 2001435 2003419 := bstep (se 1 (by rfl) ⟨1502564, by rfl⟩ : syracuseStep 2003419 = 3005129) B3005129
theorem B2439661 : Blo 2001435 2439661 := bbase (se 3 (by rfl) ⟨457436, by rfl⟩ : syracuseStep 2439661 = 914873) (by norm_num)
theorem B52046101 : Blo 2001435 52046101 := bstep (se 6 (by rfl) ⟨1219830, by rfl⟩ : syracuseStep 52046101 = 2439661) B2439661
theorem B69394801 : Blo 2001435 69394801 := bstep (se 2 (by rfl) ⟨26023050, by rfl⟩ : syracuseStep 69394801 = 52046101) B52046101
theorem B92526401 : Blo 2001435 92526401 := bstep (se 2 (by rfl) ⟨34697400, by rfl⟩ : syracuseStep 92526401 = 69394801) B69394801
theorem B61684267 : Blo 2001435 61684267 := bstep (se 1 (by rfl) ⟨46263200, by rfl⟩ : syracuseStep 61684267 = 92526401) B92526401
theorem B82245689 : Blo 2001435 82245689 := bstep (se 2 (by rfl) ⟨30842133, by rfl⟩ : syracuseStep 82245689 = 61684267) B61684267
theorem B54830459 : Blo 2001435 54830459 := bstep (se 1 (by rfl) ⟨41122844, by rfl⟩ : syracuseStep 54830459 = 82245689) B82245689
theorem B36553639 : Blo 2001435 36553639 := bstep (se 1 (by rfl) ⟨27415229, by rfl⟩ : syracuseStep 36553639 = 54830459) B54830459
theorem B48738185 : Blo 2001435 48738185 := bstep (se 2 (by rfl) ⟨18276819, by rfl⟩ : syracuseStep 48738185 = 36553639) B36553639
theorem B32492123 : Blo 2001435 32492123 := bstep (se 1 (by rfl) ⟨24369092, by rfl⟩ : syracuseStep 32492123 = 48738185) B48738185
theorem B21661415 : Blo 2001435 21661415 := bstep (se 1 (by rfl) ⟨16246061, by rfl⟩ : syracuseStep 21661415 = 32492123) B32492123
theorem B14440943 : Blo 2001435 14440943 := bstep (se 1 (by rfl) ⟨10830707, by rfl⟩ : syracuseStep 14440943 = 21661415) B21661415
theorem B9627295 : Blo 2001435 9627295 := bstep (se 1 (by rfl) ⟨7220471, by rfl⟩ : syracuseStep 9627295 = 14440943) B14440943
theorem B12836393 : Blo 2001435 12836393 := bstep (se 2 (by rfl) ⟨4813647, by rfl⟩ : syracuseStep 12836393 = 9627295) B9627295
theorem B8557595 : Blo 2001435 8557595 := bstep (se 1 (by rfl) ⟨6418196, by rfl⟩ : syracuseStep 8557595 = 12836393) B12836393
theorem B5705063 : Blo 2001435 5705063 := bstep (se 1 (by rfl) ⟨4278797, by rfl⟩ : syracuseStep 5705063 = 8557595) B8557595
theorem B3803375 : Blo 2001435 3803375 := bstep (se 1 (by rfl) ⟨2852531, by rfl⟩ : syracuseStep 3803375 = 5705063) B5705063
theorem B10142333 : Blo 2001435 10142333 := bstep (se 3 (by rfl) ⟨1901687, by rfl⟩ : syracuseStep 10142333 = 3803375) B3803375
theorem B6761555 : Blo 2001435 6761555 := bstep (se 1 (by rfl) ⟨5071166, by rfl⟩ : syracuseStep 6761555 = 10142333) B10142333
theorem B4507703 : Blo 2001435 4507703 := bstep (se 1 (by rfl) ⟨3380777, by rfl⟩ : syracuseStep 4507703 = 6761555) B6761555
theorem B3005135 : Blo 2001435 3005135 := bstep (se 1 (by rfl) ⟨2253851, by rfl⟩ : syracuseStep 3005135 = 4507703) B4507703
theorem B2003423 : Blo 2001435 2003423 := bstep (se 1 (by rfl) ⟨1502567, by rfl⟩ : syracuseStep 2003423 = 3005135) B3005135
theorem B3005141 : Blo 2001435 3005141 := bbase (se 7 (by rfl) ⟨35216, by rfl⟩ : syracuseStep 3005141 = 70433) (by norm_num)
theorem B2003427 : Blo 2001435 2003427 := bstep (se 1 (by rfl) ⟨1502570, by rfl⟩ : syracuseStep 2003427 = 3005141) B3005141
theorem B12184597 : Blo 2001435 12184597 := bbase (se 6 (by rfl) ⟨285576, by rfl⟩ : syracuseStep 12184597 = 571153) (by norm_num)
theorem B16246129 : Blo 2001435 16246129 := bstep (se 2 (by rfl) ⟨6092298, by rfl⟩ : syracuseStep 16246129 = 12184597) B12184597
theorem B21661505 : Blo 2001435 21661505 := bstep (se 2 (by rfl) ⟨8123064, by rfl⟩ : syracuseStep 21661505 = 16246129) B16246129
theorem B14441003 : Blo 2001435 14441003 := bstep (se 1 (by rfl) ⟨10830752, by rfl⟩ : syracuseStep 14441003 = 21661505) B21661505
theorem B9627335 : Blo 2001435 9627335 := bstep (se 1 (by rfl) ⟨7220501, by rfl⟩ : syracuseStep 9627335 = 14441003) B14441003
theorem B6418223 : Blo 2001435 6418223 := bstep (se 1 (by rfl) ⟨4813667, by rfl⟩ : syracuseStep 6418223 = 9627335) B9627335
theorem B4278815 : Blo 2001435 4278815 := bstep (se 1 (by rfl) ⟨3209111, by rfl⟩ : syracuseStep 4278815 = 6418223) B6418223
theorem B2852543 : Blo 2001435 2852543 := bstep (se 1 (by rfl) ⟨2139407, by rfl⟩ : syracuseStep 2852543 = 4278815) B4278815
theorem B7606781 : Blo 2001435 7606781 := bstep (se 3 (by rfl) ⟨1426271, by rfl⟩ : syracuseStep 7606781 = 2852543) B2852543
theorem B5071187 : Blo 2001435 5071187 := bstep (se 1 (by rfl) ⟨3803390, by rfl⟩ : syracuseStep 5071187 = 7606781) B7606781
theorem B3380791 : Blo 2001435 3380791 := bstep (se 1 (by rfl) ⟨2535593, by rfl⟩ : syracuseStep 3380791 = 5071187) B5071187
theorem B4507721 : Blo 2001435 4507721 := bstep (se 2 (by rfl) ⟨1690395, by rfl⟩ : syracuseStep 4507721 = 3380791) B3380791
theorem B3005147 : Blo 2001435 3005147 := bstep (se 1 (by rfl) ⟨2253860, by rfl⟩ : syracuseStep 3005147 = 4507721) B4507721
theorem B2003431 : Blo 2001435 2003431 := bstep (se 1 (by rfl) ⟨1502573, by rfl⟩ : syracuseStep 2003431 = 3005147) B3005147
theorem B2253865 : Blo 2001435 2253865 := bbase (se 2 (by rfl) ⟨845199, by rfl⟩ : syracuseStep 2253865 = 1690399) (by norm_num)
theorem B3005153 : Blo 2001435 3005153 := bstep (se 2 (by rfl) ⟨1126932, by rfl⟩ : syracuseStep 3005153 = 2253865) B2253865
theorem B2003435 : Blo 2001435 2003435 := bstep (se 1 (by rfl) ⟨1502576, by rfl⟩ : syracuseStep 2003435 = 3005153) B3005153
theorem C0 (j : ℕ) (h1 : 500358 ≤ j) (h2 : j ≤ 500858) : Blo 2001435 (4 * j + 3) := by
  interval_cases j
  · exact B2001435
  · exact B2001439
  · exact B2001443
  · exact B2001447
  · exact B2001451
  · exact B2001455
  · exact B2001459
  · exact B2001463
  · exact B2001467
  · exact B2001471
  · exact B2001475
  · exact B2001479
  · exact B2001483
  · exact B2001487
  · exact B2001491
  · exact B2001495
  · exact B2001499
  · exact B2001503
  · exact B2001507
  · exact B2001511
  · exact B2001515
  · exact B2001519
  · exact B2001523
  · exact B2001527
  · exact B2001531
  · exact B2001535
  · exact B2001539
  · exact B2001543
  · exact B2001547
  · exact B2001551
  · exact B2001555
  · exact B2001559
  · exact B2001563
  · exact B2001567
  · exact B2001571
  · exact B2001575
  · exact B2001579
  · exact B2001583
  · exact B2001587
  · exact B2001591
  · exact B2001595
  · exact B2001599
  · exact B2001603
  · exact B2001607
  · exact B2001611
  · exact B2001615
  · exact B2001619
  · exact B2001623
  · exact B2001627
  · exact B2001631
  · exact B2001635
  · exact B2001639
  · exact B2001643
  · exact B2001647
  · exact B2001651
  · exact B2001655
  · exact B2001659
  · exact B2001663
  · exact B2001667
  · exact B2001671
  · exact B2001675
  · exact B2001679
  · exact B2001683
  · exact B2001687
  · exact B2001691
  · exact B2001695
  · exact B2001699
  · exact B2001703
  · exact B2001707
  · exact B2001711
  · exact B2001715
  · exact B2001719
  · exact B2001723
  · exact B2001727
  · exact B2001731
  · exact B2001735
  · exact B2001739
  · exact B2001743
  · exact B2001747
  · exact B2001751
  · exact B2001755
  · exact B2001759
  · exact B2001763
  · exact B2001767
  · exact B2001771
  · exact B2001775
  · exact B2001779
  · exact B2001783
  · exact B2001787
  · exact B2001791
  · exact B2001795
  · exact B2001799
  · exact B2001803
  · exact B2001807
  · exact B2001811
  · exact B2001815
  · exact B2001819
  · exact B2001823
  · exact B2001827
  · exact B2001831
  · exact B2001835
  · exact B2001839
  · exact B2001843
  · exact B2001847
  · exact B2001851
  · exact B2001855
  · exact B2001859
  · exact B2001863
  · exact B2001867
  · exact B2001871
  · exact B2001875
  · exact B2001879
  · exact B2001883
  · exact B2001887
  · exact B2001891
  · exact B2001895
  · exact B2001899
  · exact B2001903
  · exact B2001907
  · exact B2001911
  · exact B2001915
  · exact B2001919
  · exact B2001923
  · exact B2001927
  · exact B2001931
  · exact B2001935
  · exact B2001939
  · exact B2001943
  · exact B2001947
  · exact B2001951
  · exact B2001955
  · exact B2001959
  · exact B2001963
  · exact B2001967
  · exact B2001971
  · exact B2001975
  · exact B2001979
  · exact B2001983
  · exact B2001987
  · exact B2001991
  · exact B2001995
  · exact B2001999
  · exact B2002003
  · exact B2002007
  · exact B2002011
  · exact B2002015
  · exact B2002019
  · exact B2002023
  · exact B2002027
  · exact B2002031
  · exact B2002035
  · exact B2002039
  · exact B2002043
  · exact B2002047
  · exact B2002051
  · exact B2002055
  · exact B2002059
  · exact B2002063
  · exact B2002067
  · exact B2002071
  · exact B2002075
  · exact B2002079
  · exact B2002083
  · exact B2002087
  · exact B2002091
  · exact B2002095
  · exact B2002099
  · exact B2002103
  · exact B2002107
  · exact B2002111
  · exact B2002115
  · exact B2002119
  · exact B2002123
  · exact B2002127
  · exact B2002131
  · exact B2002135
  · exact B2002139
  · exact B2002143
  · exact B2002147
  · exact B2002151
  · exact B2002155
  · exact B2002159
  · exact B2002163
  · exact B2002167
  · exact B2002171
  · exact B2002175
  · exact B2002179
  · exact B2002183
  · exact B2002187
  · exact B2002191
  · exact B2002195
  · exact B2002199
  · exact B2002203
  · exact B2002207
  · exact B2002211
  · exact B2002215
  · exact B2002219
  · exact B2002223
  · exact B2002227
  · exact B2002231
  · exact B2002235
  · exact B2002239
  · exact B2002243
  · exact B2002247
  · exact B2002251
  · exact B2002255
  · exact B2002259
  · exact B2002263
  · exact B2002267
  · exact B2002271
  · exact B2002275
  · exact B2002279
  · exact B2002283
  · exact B2002287
  · exact B2002291
  · exact B2002295
  · exact B2002299
  · exact B2002303
  · exact B2002307
  · exact B2002311
  · exact B2002315
  · exact B2002319
  · exact B2002323
  · exact B2002327
  · exact B2002331
  · exact B2002335
  · exact B2002339
  · exact B2002343
  · exact B2002347
  · exact B2002351
  · exact B2002355
  · exact B2002359
  · exact B2002363
  · exact B2002367
  · exact B2002371
  · exact B2002375
  · exact B2002379
  · exact B2002383
  · exact B2002387
  · exact B2002391
  · exact B2002395
  · exact B2002399
  · exact B2002403
  · exact B2002407
  · exact B2002411
  · exact B2002415
  · exact B2002419
  · exact B2002423
  · exact B2002427
  · exact B2002431
  · exact B2002435
  · exact B2002439
  · exact B2002443
  · exact B2002447
  · exact B2002451
  · exact B2002455
  · exact B2002459
  · exact B2002463
  · exact B2002467
  · exact B2002471
  · exact B2002475
  · exact B2002479
  · exact B2002483
  · exact B2002487
  · exact B2002491
  · exact B2002495
  · exact B2002499
  · exact B2002503
  · exact B2002507
  · exact B2002511
  · exact B2002515
  · exact B2002519
  · exact B2002523
  · exact B2002527
  · exact B2002531
  · exact B2002535
  · exact B2002539
  · exact B2002543
  · exact B2002547
  · exact B2002551
  · exact B2002555
  · exact B2002559
  · exact B2002563
  · exact B2002567
  · exact B2002571
  · exact B2002575
  · exact B2002579
  · exact B2002583
  · exact B2002587
  · exact B2002591
  · exact B2002595
  · exact B2002599
  · exact B2002603
  · exact B2002607
  · exact B2002611
  · exact B2002615
  · exact B2002619
  · exact B2002623
  · exact B2002627
  · exact B2002631
  · exact B2002635
  · exact B2002639
  · exact B2002643
  · exact B2002647
  · exact B2002651
  · exact B2002655
  · exact B2002659
  · exact B2002663
  · exact B2002667
  · exact B2002671
  · exact B2002675
  · exact B2002679
  · exact B2002683
  · exact B2002687
  · exact B2002691
  · exact B2002695
  · exact B2002699
  · exact B2002703
  · exact B2002707
  · exact B2002711
  · exact B2002715
  · exact B2002719
  · exact B2002723
  · exact B2002727
  · exact B2002731
  · exact B2002735
  · exact B2002739
  · exact B2002743
  · exact B2002747
  · exact B2002751
  · exact B2002755
  · exact B2002759
  · exact B2002763
  · exact B2002767
  · exact B2002771
  · exact B2002775
  · exact B2002779
  · exact B2002783
  · exact B2002787
  · exact B2002791
  · exact B2002795
  · exact B2002799
  · exact B2002803
  · exact B2002807
  · exact B2002811
  · exact B2002815
  · exact B2002819
  · exact B2002823
  · exact B2002827
  · exact B2002831
  · exact B2002835
  · exact B2002839
  · exact B2002843
  · exact B2002847
  · exact B2002851
  · exact B2002855
  · exact B2002859
  · exact B2002863
  · exact B2002867
  · exact B2002871
  · exact B2002875
  · exact B2002879
  · exact B2002883
  · exact B2002887
  · exact B2002891
  · exact B2002895
  · exact B2002899
  · exact B2002903
  · exact B2002907
  · exact B2002911
  · exact B2002915
  · exact B2002919
  · exact B2002923
  · exact B2002927
  · exact B2002931
  · exact B2002935
  · exact B2002939
  · exact B2002943
  · exact B2002947
  · exact B2002951
  · exact B2002955
  · exact B2002959
  · exact B2002963
  · exact B2002967
  · exact B2002971
  · exact B2002975
  · exact B2002979
  · exact B2002983
  · exact B2002987
  · exact B2002991
  · exact B2002995
  · exact B2002999
  · exact B2003003
  · exact B2003007
  · exact B2003011
  · exact B2003015
  · exact B2003019
  · exact B2003023
  · exact B2003027
  · exact B2003031
  · exact B2003035
  · exact B2003039
  · exact B2003043
  · exact B2003047
  · exact B2003051
  · exact B2003055
  · exact B2003059
  · exact B2003063
  · exact B2003067
  · exact B2003071
  · exact B2003075
  · exact B2003079
  · exact B2003083
  · exact B2003087
  · exact B2003091
  · exact B2003095
  · exact B2003099
  · exact B2003103
  · exact B2003107
  · exact B2003111
  · exact B2003115
  · exact B2003119
  · exact B2003123
  · exact B2003127
  · exact B2003131
  · exact B2003135
  · exact B2003139
  · exact B2003143
  · exact B2003147
  · exact B2003151
  · exact B2003155
  · exact B2003159
  · exact B2003163
  · exact B2003167
  · exact B2003171
  · exact B2003175
  · exact B2003179
  · exact B2003183
  · exact B2003187
  · exact B2003191
  · exact B2003195
  · exact B2003199
  · exact B2003203
  · exact B2003207
  · exact B2003211
  · exact B2003215
  · exact B2003219
  · exact B2003223
  · exact B2003227
  · exact B2003231
  · exact B2003235
  · exact B2003239
  · exact B2003243
  · exact B2003247
  · exact B2003251
  · exact B2003255
  · exact B2003259
  · exact B2003263
  · exact B2003267
  · exact B2003271
  · exact B2003275
  · exact B2003279
  · exact B2003283
  · exact B2003287
  · exact B2003291
  · exact B2003295
  · exact B2003299
  · exact B2003303
  · exact B2003307
  · exact B2003311
  · exact B2003315
  · exact B2003319
  · exact B2003323
  · exact B2003327
  · exact B2003331
  · exact B2003335
  · exact B2003339
  · exact B2003343
  · exact B2003347
  · exact B2003351
  · exact B2003355
  · exact B2003359
  · exact B2003363
  · exact B2003367
  · exact B2003371
  · exact B2003375
  · exact B2003379
  · exact B2003383
  · exact B2003387
  · exact B2003391
  · exact B2003395
  · exact B2003399
  · exact B2003403
  · exact B2003407
  · exact B2003411
  · exact B2003415
  · exact B2003419
  · exact B2003423
  · exact B2003427
  · exact B2003431
  · exact B2003435
theorem solution (m : ℕ) (hlo : 2001435 ≤ m) (hhi : m ≤ 2003435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 500358 ≤ j := by omega
    have hj2 : j ≤ 500858 := by omega
    have hb : Blo 2001435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
