-- Prove2me | solution 1 for syracuse_descends_range_2093435_2095435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:28.446986+00:00
-- url     : https://prove2.me/submissions/d6be9208-b1ea-4de8-869f-148246f16b24

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

theorem B2649505 : Blo 2093435 2649505 := bbase (se 2 (by rfl) ⟨993564, by rfl⟩ : syracuseStep 2649505 = 1987129) (by norm_num)
theorem B3532673 : Blo 2093435 3532673 := bstep (se 2 (by rfl) ⟨1324752, by rfl⟩ : syracuseStep 3532673 = 2649505) B2649505
theorem B2355115 : Blo 2093435 2355115 := bstep (se 1 (by rfl) ⟨1766336, by rfl⟩ : syracuseStep 2355115 = 3532673) B3532673
theorem B3140153 : Blo 2093435 3140153 := bstep (se 2 (by rfl) ⟨1177557, by rfl⟩ : syracuseStep 3140153 = 2355115) B2355115
theorem B2093435 : Blo 2093435 2093435 := bstep (se 1 (by rfl) ⟨1570076, by rfl⟩ : syracuseStep 2093435 = 3140153) B3140153
theorem B23845589 : Blo 2093435 23845589 := bbase (se 7 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 23845589 = 558881) (by norm_num)
theorem B15897059 : Blo 2093435 15897059 := bstep (se 1 (by rfl) ⟨11922794, by rfl⟩ : syracuseStep 15897059 = 23845589) B23845589
theorem B10598039 : Blo 2093435 10598039 := bstep (se 1 (by rfl) ⟨7948529, by rfl⟩ : syracuseStep 10598039 = 15897059) B15897059
theorem B7065359 : Blo 2093435 7065359 := bstep (se 1 (by rfl) ⟨5299019, by rfl⟩ : syracuseStep 7065359 = 10598039) B10598039
theorem B4710239 : Blo 2093435 4710239 := bstep (se 1 (by rfl) ⟨3532679, by rfl⟩ : syracuseStep 4710239 = 7065359) B7065359
theorem B3140159 : Blo 2093435 3140159 := bstep (se 1 (by rfl) ⟨2355119, by rfl⟩ : syracuseStep 3140159 = 4710239) B4710239
theorem B2093439 : Blo 2093435 2093439 := bstep (se 1 (by rfl) ⟨1570079, by rfl⟩ : syracuseStep 2093439 = 3140159) B3140159
theorem B3140165 : Blo 2093435 3140165 := bbase (se 4 (by rfl) ⟨294390, by rfl⟩ : syracuseStep 3140165 = 588781) (by norm_num)
theorem B2093443 : Blo 2093435 2093443 := bstep (se 1 (by rfl) ⟨1570082, by rfl⟩ : syracuseStep 2093443 = 3140165) B3140165
theorem B3532693 : Blo 2093435 3532693 := bbase (se 6 (by rfl) ⟨82797, by rfl⟩ : syracuseStep 3532693 = 165595) (by norm_num)
theorem B4710257 : Blo 2093435 4710257 := bstep (se 2 (by rfl) ⟨1766346, by rfl⟩ : syracuseStep 4710257 = 3532693) B3532693
theorem B3140171 : Blo 2093435 3140171 := bstep (se 1 (by rfl) ⟨2355128, by rfl⟩ : syracuseStep 3140171 = 4710257) B4710257
theorem B2093447 : Blo 2093435 2093447 := bstep (se 1 (by rfl) ⟨1570085, by rfl⟩ : syracuseStep 2093447 = 3140171) B3140171
theorem B2355133 : Blo 2093435 2355133 := bbase (se 3 (by rfl) ⟨441587, by rfl⟩ : syracuseStep 2355133 = 883175) (by norm_num)
theorem B3140177 : Blo 2093435 3140177 := bstep (se 2 (by rfl) ⟨1177566, by rfl⟩ : syracuseStep 3140177 = 2355133) B2355133
theorem B2093451 : Blo 2093435 2093451 := bstep (se 1 (by rfl) ⟨1570088, by rfl⟩ : syracuseStep 2093451 = 3140177) B3140177
theorem B7065413 : Blo 2093435 7065413 := bbase (se 4 (by rfl) ⟨662382, by rfl⟩ : syracuseStep 7065413 = 1324765) (by norm_num)
theorem B4710275 : Blo 2093435 4710275 := bstep (se 1 (by rfl) ⟨3532706, by rfl⟩ : syracuseStep 4710275 = 7065413) B7065413
theorem B3140183 : Blo 2093435 3140183 := bstep (se 1 (by rfl) ⟨2355137, by rfl⟩ : syracuseStep 3140183 = 4710275) B4710275
theorem B2093455 : Blo 2093435 2093455 := bstep (se 1 (by rfl) ⟨1570091, by rfl⟩ : syracuseStep 2093455 = 3140183) B3140183
theorem B3140189 : Blo 2093435 3140189 := bbase (se 3 (by rfl) ⟨588785, by rfl⟩ : syracuseStep 3140189 = 1177571) (by norm_num)
theorem B2093459 : Blo 2093435 2093459 := bstep (se 1 (by rfl) ⟨1570094, by rfl⟩ : syracuseStep 2093459 = 3140189) B3140189
theorem B4710293 : Blo 2093435 4710293 := bbase (se 6 (by rfl) ⟨110397, by rfl⟩ : syracuseStep 4710293 = 220795) (by norm_num)
theorem B3140195 : Blo 2093435 3140195 := bstep (se 1 (by rfl) ⟨2355146, by rfl⟩ : syracuseStep 3140195 = 4710293) B4710293
theorem B2093463 : Blo 2093435 2093463 := bstep (se 1 (by rfl) ⟨1570097, by rfl⟩ : syracuseStep 2093463 = 3140195) B3140195
theorem B4471109 : Blo 2093435 4471109 := bbase (se 4 (by rfl) ⟨419166, by rfl⟩ : syracuseStep 4471109 = 838333) (by norm_num)
theorem B2980739 : Blo 2093435 2980739 := bstep (se 1 (by rfl) ⟨2235554, by rfl⟩ : syracuseStep 2980739 = 4471109) B4471109
theorem B7948637 : Blo 2093435 7948637 := bstep (se 3 (by rfl) ⟨1490369, by rfl⟩ : syracuseStep 7948637 = 2980739) B2980739
theorem B5299091 : Blo 2093435 5299091 := bstep (se 1 (by rfl) ⟨3974318, by rfl⟩ : syracuseStep 5299091 = 7948637) B7948637
theorem B3532727 : Blo 2093435 3532727 := bstep (se 1 (by rfl) ⟨2649545, by rfl⟩ : syracuseStep 3532727 = 5299091) B5299091
theorem B2355151 : Blo 2093435 2355151 := bstep (se 1 (by rfl) ⟨1766363, by rfl⟩ : syracuseStep 2355151 = 3532727) B3532727
theorem B3140201 : Blo 2093435 3140201 := bstep (se 2 (by rfl) ⟨1177575, by rfl⟩ : syracuseStep 3140201 = 2355151) B2355151
theorem B2093467 : Blo 2093435 2093467 := bstep (se 1 (by rfl) ⟨1570100, by rfl⟩ : syracuseStep 2093467 = 3140201) B3140201
theorem B4244069 : Blo 2093435 4244069 := bbase (se 4 (by rfl) ⟨397881, by rfl⟩ : syracuseStep 4244069 = 795763) (by norm_num)
theorem B2829379 : Blo 2093435 2829379 := bstep (se 1 (by rfl) ⟨2122034, by rfl⟩ : syracuseStep 2829379 = 4244069) B4244069
theorem B3772505 : Blo 2093435 3772505 := bstep (se 2 (by rfl) ⟨1414689, by rfl⟩ : syracuseStep 3772505 = 2829379) B2829379
theorem B10060013 : Blo 2093435 10060013 := bstep (se 3 (by rfl) ⟨1886252, by rfl⟩ : syracuseStep 10060013 = 3772505) B3772505
theorem B6706675 : Blo 2093435 6706675 := bstep (se 1 (by rfl) ⟨5030006, by rfl⟩ : syracuseStep 6706675 = 10060013) B10060013
theorem B8942233 : Blo 2093435 8942233 := bstep (se 2 (by rfl) ⟨3353337, by rfl⟩ : syracuseStep 8942233 = 6706675) B6706675
theorem B11922977 : Blo 2093435 11922977 := bstep (se 2 (by rfl) ⟨4471116, by rfl⟩ : syracuseStep 11922977 = 8942233) B8942233
theorem B7948651 : Blo 2093435 7948651 := bstep (se 1 (by rfl) ⟨5961488, by rfl⟩ : syracuseStep 7948651 = 11922977) B11922977
theorem B10598201 : Blo 2093435 10598201 := bstep (se 2 (by rfl) ⟨3974325, by rfl⟩ : syracuseStep 10598201 = 7948651) B7948651
theorem B7065467 : Blo 2093435 7065467 := bstep (se 1 (by rfl) ⟨5299100, by rfl⟩ : syracuseStep 7065467 = 10598201) B10598201
theorem B4710311 : Blo 2093435 4710311 := bstep (se 1 (by rfl) ⟨3532733, by rfl⟩ : syracuseStep 4710311 = 7065467) B7065467
theorem B3140207 : Blo 2093435 3140207 := bstep (se 1 (by rfl) ⟨2355155, by rfl⟩ : syracuseStep 3140207 = 4710311) B4710311
theorem B2093471 : Blo 2093435 2093471 := bstep (se 1 (by rfl) ⟨1570103, by rfl⟩ : syracuseStep 2093471 = 3140207) B3140207
theorem B3140213 : Blo 2093435 3140213 := bbase (se 5 (by rfl) ⟨147197, by rfl⟩ : syracuseStep 3140213 = 294395) (by norm_num)
theorem B2093475 : Blo 2093435 2093475 := bstep (se 1 (by rfl) ⟨1570106, by rfl⟩ : syracuseStep 2093475 = 3140213) B3140213
theorem B3974341 : Blo 2093435 3974341 := bbase (se 4 (by rfl) ⟨372594, by rfl⟩ : syracuseStep 3974341 = 745189) (by norm_num)
theorem B5299121 : Blo 2093435 5299121 := bstep (se 2 (by rfl) ⟨1987170, by rfl⟩ : syracuseStep 5299121 = 3974341) B3974341
theorem B3532747 : Blo 2093435 3532747 := bstep (se 1 (by rfl) ⟨2649560, by rfl⟩ : syracuseStep 3532747 = 5299121) B5299121
theorem B4710329 : Blo 2093435 4710329 := bstep (se 2 (by rfl) ⟨1766373, by rfl⟩ : syracuseStep 4710329 = 3532747) B3532747
theorem B3140219 : Blo 2093435 3140219 := bstep (se 1 (by rfl) ⟨2355164, by rfl⟩ : syracuseStep 3140219 = 4710329) B4710329
theorem B2093479 : Blo 2093435 2093479 := bstep (se 1 (by rfl) ⟨1570109, by rfl⟩ : syracuseStep 2093479 = 3140219) B3140219
theorem B2355169 : Blo 2093435 2355169 := bbase (se 2 (by rfl) ⟨883188, by rfl⟩ : syracuseStep 2355169 = 1766377) (by norm_num)
theorem B3140225 : Blo 2093435 3140225 := bstep (se 2 (by rfl) ⟨1177584, by rfl⟩ : syracuseStep 3140225 = 2355169) B2355169
theorem B2093483 : Blo 2093435 2093483 := bstep (se 1 (by rfl) ⟨1570112, by rfl⟩ : syracuseStep 2093483 = 3140225) B3140225
theorem B5299141 : Blo 2093435 5299141 := bbase (se 4 (by rfl) ⟨496794, by rfl⟩ : syracuseStep 5299141 = 993589) (by norm_num)
theorem B7065521 : Blo 2093435 7065521 := bstep (se 2 (by rfl) ⟨2649570, by rfl⟩ : syracuseStep 7065521 = 5299141) B5299141
theorem B4710347 : Blo 2093435 4710347 := bstep (se 1 (by rfl) ⟨3532760, by rfl⟩ : syracuseStep 4710347 = 7065521) B7065521
theorem B3140231 : Blo 2093435 3140231 := bstep (se 1 (by rfl) ⟨2355173, by rfl⟩ : syracuseStep 3140231 = 4710347) B4710347
theorem B2093487 : Blo 2093435 2093487 := bstep (se 1 (by rfl) ⟨1570115, by rfl⟩ : syracuseStep 2093487 = 3140231) B3140231
theorem B3140237 : Blo 2093435 3140237 := bbase (se 3 (by rfl) ⟨588794, by rfl⟩ : syracuseStep 3140237 = 1177589) (by norm_num)
theorem B2093491 : Blo 2093435 2093491 := bstep (se 1 (by rfl) ⟨1570118, by rfl⟩ : syracuseStep 2093491 = 3140237) B3140237
theorem B4710365 : Blo 2093435 4710365 := bbase (se 3 (by rfl) ⟨883193, by rfl⟩ : syracuseStep 4710365 = 1766387) (by norm_num)
theorem B3140243 : Blo 2093435 3140243 := bstep (se 1 (by rfl) ⟨2355182, by rfl⟩ : syracuseStep 3140243 = 4710365) B4710365
theorem B2093495 : Blo 2093435 2093495 := bstep (se 1 (by rfl) ⟨1570121, by rfl⟩ : syracuseStep 2093495 = 3140243) B3140243
theorem B3532781 : Blo 2093435 3532781 := bbase (se 3 (by rfl) ⟨662396, by rfl⟩ : syracuseStep 3532781 = 1324793) (by norm_num)
theorem B2355187 : Blo 2093435 2355187 := bstep (se 1 (by rfl) ⟨1766390, by rfl⟩ : syracuseStep 2355187 = 3532781) B3532781
theorem B3140249 : Blo 2093435 3140249 := bstep (se 2 (by rfl) ⟨1177593, by rfl⟩ : syracuseStep 3140249 = 2355187) B2355187
theorem B2093499 : Blo 2093435 2093499 := bstep (se 1 (by rfl) ⟨1570124, by rfl⟩ : syracuseStep 2093499 = 3140249) B3140249
theorem B7545125 : Blo 2093435 7545125 := bbase (se 4 (by rfl) ⟨707355, by rfl⟩ : syracuseStep 7545125 = 1414711) (by norm_num)
theorem B5030083 : Blo 2093435 5030083 := bstep (se 1 (by rfl) ⟨3772562, by rfl⟩ : syracuseStep 5030083 = 7545125) B7545125
theorem B26827109 : Blo 2093435 26827109 := bstep (se 4 (by rfl) ⟨2515041, by rfl⟩ : syracuseStep 26827109 = 5030083) B5030083
theorem B17884739 : Blo 2093435 17884739 := bstep (se 1 (by rfl) ⟨13413554, by rfl⟩ : syracuseStep 17884739 = 26827109) B26827109
theorem B11923159 : Blo 2093435 11923159 := bstep (se 1 (by rfl) ⟨8942369, by rfl⟩ : syracuseStep 11923159 = 17884739) B17884739
theorem B15897545 : Blo 2093435 15897545 := bstep (se 2 (by rfl) ⟨5961579, by rfl⟩ : syracuseStep 15897545 = 11923159) B11923159
theorem B10598363 : Blo 2093435 10598363 := bstep (se 1 (by rfl) ⟨7948772, by rfl⟩ : syracuseStep 10598363 = 15897545) B15897545
theorem B7065575 : Blo 2093435 7065575 := bstep (se 1 (by rfl) ⟨5299181, by rfl⟩ : syracuseStep 7065575 = 10598363) B10598363
theorem B4710383 : Blo 2093435 4710383 := bstep (se 1 (by rfl) ⟨3532787, by rfl⟩ : syracuseStep 4710383 = 7065575) B7065575
theorem B3140255 : Blo 2093435 3140255 := bstep (se 1 (by rfl) ⟨2355191, by rfl⟩ : syracuseStep 3140255 = 4710383) B4710383
theorem B2093503 : Blo 2093435 2093503 := bstep (se 1 (by rfl) ⟨1570127, by rfl⟩ : syracuseStep 2093503 = 3140255) B3140255
theorem B3140261 : Blo 2093435 3140261 := bbase (se 4 (by rfl) ⟨294399, by rfl⟩ : syracuseStep 3140261 = 588799) (by norm_num)
theorem B2093507 : Blo 2093435 2093507 := bstep (se 1 (by rfl) ⟨1570130, by rfl⟩ : syracuseStep 2093507 = 3140261) B3140261
theorem B2649601 : Blo 2093435 2649601 := bbase (se 2 (by rfl) ⟨993600, by rfl⟩ : syracuseStep 2649601 = 1987201) (by norm_num)
theorem B3532801 : Blo 2093435 3532801 := bstep (se 2 (by rfl) ⟨1324800, by rfl⟩ : syracuseStep 3532801 = 2649601) B2649601
theorem B4710401 : Blo 2093435 4710401 := bstep (se 2 (by rfl) ⟨1766400, by rfl⟩ : syracuseStep 4710401 = 3532801) B3532801
theorem B3140267 : Blo 2093435 3140267 := bstep (se 1 (by rfl) ⟨2355200, by rfl⟩ : syracuseStep 3140267 = 4710401) B4710401
theorem B2093511 : Blo 2093435 2093511 := bstep (se 1 (by rfl) ⟨1570133, by rfl⟩ : syracuseStep 2093511 = 3140267) B3140267
theorem B2355205 : Blo 2093435 2355205 := bbase (se 4 (by rfl) ⟨220800, by rfl⟩ : syracuseStep 2355205 = 441601) (by norm_num)
theorem B3140273 : Blo 2093435 3140273 := bstep (se 2 (by rfl) ⟨1177602, by rfl⟩ : syracuseStep 3140273 = 2355205) B2355205
theorem B2093515 : Blo 2093435 2093515 := bstep (se 1 (by rfl) ⟨1570136, by rfl⟩ : syracuseStep 2093515 = 3140273) B3140273
theorem B2980813 : Blo 2093435 2980813 := bbase (se 3 (by rfl) ⟨558902, by rfl⟩ : syracuseStep 2980813 = 1117805) (by norm_num)
theorem B3974417 : Blo 2093435 3974417 := bstep (se 2 (by rfl) ⟨1490406, by rfl⟩ : syracuseStep 3974417 = 2980813) B2980813
theorem B2649611 : Blo 2093435 2649611 := bstep (se 1 (by rfl) ⟨1987208, by rfl⟩ : syracuseStep 2649611 = 3974417) B3974417
theorem B7065629 : Blo 2093435 7065629 := bstep (se 3 (by rfl) ⟨1324805, by rfl⟩ : syracuseStep 7065629 = 2649611) B2649611
theorem B4710419 : Blo 2093435 4710419 := bstep (se 1 (by rfl) ⟨3532814, by rfl⟩ : syracuseStep 4710419 = 7065629) B7065629
theorem B3140279 : Blo 2093435 3140279 := bstep (se 1 (by rfl) ⟨2355209, by rfl⟩ : syracuseStep 3140279 = 4710419) B4710419
theorem B2093519 : Blo 2093435 2093519 := bstep (se 1 (by rfl) ⟨1570139, by rfl⟩ : syracuseStep 2093519 = 3140279) B3140279
theorem B3140285 : Blo 2093435 3140285 := bbase (se 3 (by rfl) ⟨588803, by rfl⟩ : syracuseStep 3140285 = 1177607) (by norm_num)
theorem B2093523 : Blo 2093435 2093523 := bstep (se 1 (by rfl) ⟨1570142, by rfl⟩ : syracuseStep 2093523 = 3140285) B3140285
theorem B4710437 : Blo 2093435 4710437 := bbase (se 4 (by rfl) ⟨441603, by rfl⟩ : syracuseStep 4710437 = 883207) (by norm_num)
theorem B3140291 : Blo 2093435 3140291 := bstep (se 1 (by rfl) ⟨2355218, by rfl⟩ : syracuseStep 3140291 = 4710437) B4710437
theorem B2093527 : Blo 2093435 2093527 := bstep (se 1 (by rfl) ⟨1570145, by rfl⟩ : syracuseStep 2093527 = 3140291) B3140291
theorem B5299253 : Blo 2093435 5299253 := bbase (se 5 (by rfl) ⟨248402, by rfl⟩ : syracuseStep 5299253 = 496805) (by norm_num)
theorem B3532835 : Blo 2093435 3532835 := bstep (se 1 (by rfl) ⟨2649626, by rfl⟩ : syracuseStep 3532835 = 5299253) B5299253
theorem B2355223 : Blo 2093435 2355223 := bstep (se 1 (by rfl) ⟨1766417, by rfl⟩ : syracuseStep 2355223 = 3532835) B3532835
theorem B3140297 : Blo 2093435 3140297 := bstep (se 2 (by rfl) ⟨1177611, by rfl⟩ : syracuseStep 3140297 = 2355223) B2355223
theorem B2093531 : Blo 2093435 2093531 := bstep (se 1 (by rfl) ⟨1570148, by rfl⟩ : syracuseStep 2093531 = 3140297) B3140297
theorem B3183149 : Blo 2093435 3183149 := bbase (se 3 (by rfl) ⟨596840, by rfl⟩ : syracuseStep 3183149 = 1193681) (by norm_num)
theorem B8488397 : Blo 2093435 8488397 := bstep (se 3 (by rfl) ⟨1591574, by rfl⟩ : syracuseStep 8488397 = 3183149) B3183149
theorem B5658931 : Blo 2093435 5658931 := bstep (se 1 (by rfl) ⟨4244198, by rfl⟩ : syracuseStep 5658931 = 8488397) B8488397
theorem B7545241 : Blo 2093435 7545241 := bstep (se 2 (by rfl) ⟨2829465, by rfl⟩ : syracuseStep 7545241 = 5658931) B5658931
theorem B10060321 : Blo 2093435 10060321 := bstep (se 2 (by rfl) ⟨3772620, by rfl⟩ : syracuseStep 10060321 = 7545241) B7545241
theorem B13413761 : Blo 2093435 13413761 := bstep (se 2 (by rfl) ⟨5030160, by rfl⟩ : syracuseStep 13413761 = 10060321) B10060321
theorem B8942507 : Blo 2093435 8942507 := bstep (se 1 (by rfl) ⟨6706880, by rfl⟩ : syracuseStep 8942507 = 13413761) B13413761
theorem B5961671 : Blo 2093435 5961671 := bstep (se 1 (by rfl) ⟨4471253, by rfl⟩ : syracuseStep 5961671 = 8942507) B8942507
theorem B3974447 : Blo 2093435 3974447 := bstep (se 1 (by rfl) ⟨2980835, by rfl⟩ : syracuseStep 3974447 = 5961671) B5961671
theorem B10598525 : Blo 2093435 10598525 := bstep (se 3 (by rfl) ⟨1987223, by rfl⟩ : syracuseStep 10598525 = 3974447) B3974447
theorem B7065683 : Blo 2093435 7065683 := bstep (se 1 (by rfl) ⟨5299262, by rfl⟩ : syracuseStep 7065683 = 10598525) B10598525
theorem B4710455 : Blo 2093435 4710455 := bstep (se 1 (by rfl) ⟨3532841, by rfl⟩ : syracuseStep 4710455 = 7065683) B7065683
theorem B3140303 : Blo 2093435 3140303 := bstep (se 1 (by rfl) ⟨2355227, by rfl⟩ : syracuseStep 3140303 = 4710455) B4710455
theorem B2093535 : Blo 2093435 2093535 := bstep (se 1 (by rfl) ⟨1570151, by rfl⟩ : syracuseStep 2093535 = 3140303) B3140303
theorem B3140309 : Blo 2093435 3140309 := bbase (se 7 (by rfl) ⟨36800, by rfl⟩ : syracuseStep 3140309 = 73601) (by norm_num)
theorem B2093539 : Blo 2093435 2093539 := bstep (se 1 (by rfl) ⟨1570154, by rfl⟩ : syracuseStep 2093539 = 3140309) B3140309
theorem B2685793 : Blo 2093435 2685793 := bbase (se 2 (by rfl) ⟨1007172, by rfl⟩ : syracuseStep 2685793 = 2014345) (by norm_num)
theorem B3581057 : Blo 2093435 3581057 := bstep (se 2 (by rfl) ⟨1342896, by rfl⟩ : syracuseStep 3581057 = 2685793) B2685793
theorem B9549485 : Blo 2093435 9549485 := bstep (se 3 (by rfl) ⟨1790528, by rfl⟩ : syracuseStep 9549485 = 3581057) B3581057
theorem B6366323 : Blo 2093435 6366323 := bstep (se 1 (by rfl) ⟨4774742, by rfl⟩ : syracuseStep 6366323 = 9549485) B9549485
theorem B16976861 : Blo 2093435 16976861 := bstep (se 3 (by rfl) ⟨3183161, by rfl⟩ : syracuseStep 16976861 = 6366323) B6366323
theorem B11317907 : Blo 2093435 11317907 := bstep (se 1 (by rfl) ⟨8488430, by rfl⟩ : syracuseStep 11317907 = 16976861) B16976861
theorem B7545271 : Blo 2093435 7545271 := bstep (se 1 (by rfl) ⟨5658953, by rfl⟩ : syracuseStep 7545271 = 11317907) B11317907
theorem B10060361 : Blo 2093435 10060361 := bstep (se 2 (by rfl) ⟨3772635, by rfl⟩ : syracuseStep 10060361 = 7545271) B7545271
theorem B6706907 : Blo 2093435 6706907 := bstep (se 1 (by rfl) ⟨5030180, by rfl⟩ : syracuseStep 6706907 = 10060361) B10060361
theorem B4471271 : Blo 2093435 4471271 := bstep (se 1 (by rfl) ⟨3353453, by rfl⟩ : syracuseStep 4471271 = 6706907) B6706907
theorem B2980847 : Blo 2093435 2980847 := bstep (se 1 (by rfl) ⟨2235635, by rfl⟩ : syracuseStep 2980847 = 4471271) B4471271
theorem B7948925 : Blo 2093435 7948925 := bstep (se 3 (by rfl) ⟨1490423, by rfl⟩ : syracuseStep 7948925 = 2980847) B2980847
theorem B5299283 : Blo 2093435 5299283 := bstep (se 1 (by rfl) ⟨3974462, by rfl⟩ : syracuseStep 5299283 = 7948925) B7948925
theorem B3532855 : Blo 2093435 3532855 := bstep (se 1 (by rfl) ⟨2649641, by rfl⟩ : syracuseStep 3532855 = 5299283) B5299283
theorem B4710473 : Blo 2093435 4710473 := bstep (se 2 (by rfl) ⟨1766427, by rfl⟩ : syracuseStep 4710473 = 3532855) B3532855
theorem B3140315 : Blo 2093435 3140315 := bstep (se 1 (by rfl) ⟨2355236, by rfl⟩ : syracuseStep 3140315 = 4710473) B4710473
theorem B2093543 : Blo 2093435 2093543 := bstep (se 1 (by rfl) ⟨1570157, by rfl⟩ : syracuseStep 2093543 = 3140315) B3140315
theorem B2355241 : Blo 2093435 2355241 := bbase (se 2 (by rfl) ⟨883215, by rfl⟩ : syracuseStep 2355241 = 1766431) (by norm_num)
theorem B3140321 : Blo 2093435 3140321 := bstep (se 2 (by rfl) ⟨1177620, by rfl⟩ : syracuseStep 3140321 = 2355241) B2355241
theorem B2093547 : Blo 2093435 2093547 := bstep (se 1 (by rfl) ⟨1570160, by rfl⟩ : syracuseStep 2093547 = 3140321) B3140321
theorem B9188261 : Blo 2093435 9188261 := bbase (se 4 (by rfl) ⟨861399, by rfl⟩ : syracuseStep 9188261 = 1722799) (by norm_num)
theorem B6125507 : Blo 2093435 6125507 := bstep (se 1 (by rfl) ⟨4594130, by rfl⟩ : syracuseStep 6125507 = 9188261) B9188261
theorem B4083671 : Blo 2093435 4083671 := bstep (se 1 (by rfl) ⟨3062753, by rfl⟩ : syracuseStep 4083671 = 6125507) B6125507
theorem B2722447 : Blo 2093435 2722447 := bstep (se 1 (by rfl) ⟨2041835, by rfl⟩ : syracuseStep 2722447 = 4083671) B4083671
theorem B3629929 : Blo 2093435 3629929 := bstep (se 2 (by rfl) ⟨1361223, by rfl⟩ : syracuseStep 3629929 = 2722447) B2722447
theorem B4839905 : Blo 2093435 4839905 := bstep (se 2 (by rfl) ⟨1814964, by rfl⟩ : syracuseStep 4839905 = 3629929) B3629929
theorem B3226603 : Blo 2093435 3226603 := bstep (se 1 (by rfl) ⟨2419952, by rfl⟩ : syracuseStep 3226603 = 4839905) B4839905
theorem B4302137 : Blo 2093435 4302137 := bstep (se 2 (by rfl) ⟨1613301, by rfl⟩ : syracuseStep 4302137 = 3226603) B3226603
theorem B2868091 : Blo 2093435 2868091 := bstep (se 1 (by rfl) ⟨2151068, by rfl⟩ : syracuseStep 2868091 = 4302137) B4302137
theorem B61185941 : Blo 2093435 61185941 := bstep (se 6 (by rfl) ⟨1434045, by rfl⟩ : syracuseStep 61185941 = 2868091) B2868091
theorem B40790627 : Blo 2093435 40790627 := bstep (se 1 (by rfl) ⟨30592970, by rfl⟩ : syracuseStep 40790627 = 61185941) B61185941
theorem B27193751 : Blo 2093435 27193751 := bstep (se 1 (by rfl) ⟨20395313, by rfl⟩ : syracuseStep 27193751 = 40790627) B40790627
theorem B18129167 : Blo 2093435 18129167 := bstep (se 1 (by rfl) ⟨13596875, by rfl⟩ : syracuseStep 18129167 = 27193751) B27193751
theorem B12086111 : Blo 2093435 12086111 := bstep (se 1 (by rfl) ⟨9064583, by rfl⟩ : syracuseStep 12086111 = 18129167) B18129167
theorem B8057407 : Blo 2093435 8057407 := bstep (se 1 (by rfl) ⟨6043055, by rfl⟩ : syracuseStep 8057407 = 12086111) B12086111
theorem B10743209 : Blo 2093435 10743209 := bstep (se 2 (by rfl) ⟨4028703, by rfl⟩ : syracuseStep 10743209 = 8057407) B8057407
theorem B7162139 : Blo 2093435 7162139 := bstep (se 1 (by rfl) ⟨5371604, by rfl⟩ : syracuseStep 7162139 = 10743209) B10743209
theorem B19099037 : Blo 2093435 19099037 := bstep (se 3 (by rfl) ⟨3581069, by rfl⟩ : syracuseStep 19099037 = 7162139) B7162139
theorem B50930765 : Blo 2093435 50930765 := bstep (se 3 (by rfl) ⟨9549518, by rfl⟩ : syracuseStep 50930765 = 19099037) B19099037
theorem B33953843 : Blo 2093435 33953843 := bstep (se 1 (by rfl) ⟨25465382, by rfl⟩ : syracuseStep 33953843 = 50930765) B50930765
theorem B22635895 : Blo 2093435 22635895 := bstep (se 1 (by rfl) ⟨16976921, by rfl⟩ : syracuseStep 22635895 = 33953843) B33953843
theorem B30181193 : Blo 2093435 30181193 := bstep (se 2 (by rfl) ⟨11317947, by rfl⟩ : syracuseStep 30181193 = 22635895) B22635895
theorem B20120795 : Blo 2093435 20120795 := bstep (se 1 (by rfl) ⟨15090596, by rfl⟩ : syracuseStep 20120795 = 30181193) B30181193
theorem B13413863 : Blo 2093435 13413863 := bstep (se 1 (by rfl) ⟨10060397, by rfl⟩ : syracuseStep 13413863 = 20120795) B20120795
theorem B8942575 : Blo 2093435 8942575 := bstep (se 1 (by rfl) ⟨6706931, by rfl⟩ : syracuseStep 8942575 = 13413863) B13413863
theorem B11923433 : Blo 2093435 11923433 := bstep (se 2 (by rfl) ⟨4471287, by rfl⟩ : syracuseStep 11923433 = 8942575) B8942575
theorem B7948955 : Blo 2093435 7948955 := bstep (se 1 (by rfl) ⟨5961716, by rfl⟩ : syracuseStep 7948955 = 11923433) B11923433
theorem B5299303 : Blo 2093435 5299303 := bstep (se 1 (by rfl) ⟨3974477, by rfl⟩ : syracuseStep 5299303 = 7948955) B7948955
theorem B7065737 : Blo 2093435 7065737 := bstep (se 2 (by rfl) ⟨2649651, by rfl⟩ : syracuseStep 7065737 = 5299303) B5299303
theorem B4710491 : Blo 2093435 4710491 := bstep (se 1 (by rfl) ⟨3532868, by rfl⟩ : syracuseStep 4710491 = 7065737) B7065737
theorem B3140327 : Blo 2093435 3140327 := bstep (se 1 (by rfl) ⟨2355245, by rfl⟩ : syracuseStep 3140327 = 4710491) B4710491
theorem B2093551 : Blo 2093435 2093551 := bstep (se 1 (by rfl) ⟨1570163, by rfl⟩ : syracuseStep 2093551 = 3140327) B3140327
theorem B3140333 : Blo 2093435 3140333 := bbase (se 3 (by rfl) ⟨588812, by rfl⟩ : syracuseStep 3140333 = 1177625) (by norm_num)
theorem B2093555 : Blo 2093435 2093555 := bstep (se 1 (by rfl) ⟨1570166, by rfl⟩ : syracuseStep 2093555 = 3140333) B3140333
theorem B4710509 : Blo 2093435 4710509 := bbase (se 3 (by rfl) ⟨883220, by rfl⟩ : syracuseStep 4710509 = 1766441) (by norm_num)
theorem B3140339 : Blo 2093435 3140339 := bstep (se 1 (by rfl) ⟨2355254, by rfl⟩ : syracuseStep 3140339 = 4710509) B4710509
theorem B2093559 : Blo 2093435 2093559 := bstep (se 1 (by rfl) ⟨1570169, by rfl⟩ : syracuseStep 2093559 = 3140339) B3140339
theorem B3974501 : Blo 2093435 3974501 := bbase (se 4 (by rfl) ⟨372609, by rfl⟩ : syracuseStep 3974501 = 745219) (by norm_num)
theorem B2649667 : Blo 2093435 2649667 := bstep (se 1 (by rfl) ⟨1987250, by rfl⟩ : syracuseStep 2649667 = 3974501) B3974501
theorem B3532889 : Blo 2093435 3532889 := bstep (se 2 (by rfl) ⟨1324833, by rfl⟩ : syracuseStep 3532889 = 2649667) B2649667
theorem B2355259 : Blo 2093435 2355259 := bstep (se 1 (by rfl) ⟨1766444, by rfl⟩ : syracuseStep 2355259 = 3532889) B3532889
theorem B3140345 : Blo 2093435 3140345 := bstep (se 2 (by rfl) ⟨1177629, by rfl⟩ : syracuseStep 3140345 = 2355259) B2355259
theorem B2093563 : Blo 2093435 2093563 := bstep (se 1 (by rfl) ⟨1570172, by rfl⟩ : syracuseStep 2093563 = 3140345) B3140345
theorem B3183197 : Blo 2093435 3183197 := bbase (se 3 (by rfl) ⟨596849, by rfl⟩ : syracuseStep 3183197 = 1193699) (by norm_num)
theorem B8488525 : Blo 2093435 8488525 := bstep (se 3 (by rfl) ⟨1591598, by rfl⟩ : syracuseStep 8488525 = 3183197) B3183197
theorem B11318033 : Blo 2093435 11318033 := bstep (se 2 (by rfl) ⟨4244262, by rfl⟩ : syracuseStep 11318033 = 8488525) B8488525
theorem B7545355 : Blo 2093435 7545355 := bstep (se 1 (by rfl) ⟨5659016, by rfl⟩ : syracuseStep 7545355 = 11318033) B11318033
theorem B40241893 : Blo 2093435 40241893 := bstep (se 4 (by rfl) ⟨3772677, by rfl⟩ : syracuseStep 40241893 = 7545355) B7545355
theorem B53655857 : Blo 2093435 53655857 := bstep (se 2 (by rfl) ⟨20120946, by rfl⟩ : syracuseStep 53655857 = 40241893) B40241893
theorem B35770571 : Blo 2093435 35770571 := bstep (se 1 (by rfl) ⟨26827928, by rfl⟩ : syracuseStep 35770571 = 53655857) B53655857
theorem B23847047 : Blo 2093435 23847047 := bstep (se 1 (by rfl) ⟨17885285, by rfl⟩ : syracuseStep 23847047 = 35770571) B35770571
theorem B15898031 : Blo 2093435 15898031 := bstep (se 1 (by rfl) ⟨11923523, by rfl⟩ : syracuseStep 15898031 = 23847047) B23847047
theorem B10598687 : Blo 2093435 10598687 := bstep (se 1 (by rfl) ⟨7949015, by rfl⟩ : syracuseStep 10598687 = 15898031) B15898031
theorem B7065791 : Blo 2093435 7065791 := bstep (se 1 (by rfl) ⟨5299343, by rfl⟩ : syracuseStep 7065791 = 10598687) B10598687
theorem B4710527 : Blo 2093435 4710527 := bstep (se 1 (by rfl) ⟨3532895, by rfl⟩ : syracuseStep 4710527 = 7065791) B7065791
theorem B3140351 : Blo 2093435 3140351 := bstep (se 1 (by rfl) ⟨2355263, by rfl⟩ : syracuseStep 3140351 = 4710527) B4710527
theorem B2093567 : Blo 2093435 2093567 := bstep (se 1 (by rfl) ⟨1570175, by rfl⟩ : syracuseStep 2093567 = 3140351) B3140351
theorem B3140357 : Blo 2093435 3140357 := bbase (se 4 (by rfl) ⟨294408, by rfl⟩ : syracuseStep 3140357 = 588817) (by norm_num)
theorem B2093571 : Blo 2093435 2093571 := bstep (se 1 (by rfl) ⟨1570178, by rfl⟩ : syracuseStep 2093571 = 3140357) B3140357
theorem B3532909 : Blo 2093435 3532909 := bbase (se 3 (by rfl) ⟨662420, by rfl⟩ : syracuseStep 3532909 = 1324841) (by norm_num)
theorem B4710545 : Blo 2093435 4710545 := bstep (se 2 (by rfl) ⟨1766454, by rfl⟩ : syracuseStep 4710545 = 3532909) B3532909
theorem B3140363 : Blo 2093435 3140363 := bstep (se 1 (by rfl) ⟨2355272, by rfl⟩ : syracuseStep 3140363 = 4710545) B4710545
theorem B2093575 : Blo 2093435 2093575 := bstep (se 1 (by rfl) ⟨1570181, by rfl⟩ : syracuseStep 2093575 = 3140363) B3140363
theorem B2355277 : Blo 2093435 2355277 := bbase (se 3 (by rfl) ⟨441614, by rfl⟩ : syracuseStep 2355277 = 883229) (by norm_num)
theorem B3140369 : Blo 2093435 3140369 := bstep (se 2 (by rfl) ⟨1177638, by rfl⟩ : syracuseStep 3140369 = 2355277) B2355277
theorem B2093579 : Blo 2093435 2093579 := bstep (se 1 (by rfl) ⟨1570184, by rfl⟩ : syracuseStep 2093579 = 3140369) B3140369
theorem B7065845 : Blo 2093435 7065845 := bbase (se 5 (by rfl) ⟨331211, by rfl⟩ : syracuseStep 7065845 = 662423) (by norm_num)
theorem B4710563 : Blo 2093435 4710563 := bstep (se 1 (by rfl) ⟨3532922, by rfl⟩ : syracuseStep 4710563 = 7065845) B7065845
theorem B3140375 : Blo 2093435 3140375 := bstep (se 1 (by rfl) ⟨2355281, by rfl⟩ : syracuseStep 3140375 = 4710563) B4710563
theorem B2093583 : Blo 2093435 2093583 := bstep (se 1 (by rfl) ⟨1570187, by rfl⟩ : syracuseStep 2093583 = 3140375) B3140375
theorem B3140381 : Blo 2093435 3140381 := bbase (se 3 (by rfl) ⟨588821, by rfl⟩ : syracuseStep 3140381 = 1177643) (by norm_num)
theorem B2093587 : Blo 2093435 2093587 := bstep (se 1 (by rfl) ⟨1570190, by rfl⟩ : syracuseStep 2093587 = 3140381) B3140381
theorem B4710581 : Blo 2093435 4710581 := bbase (se 5 (by rfl) ⟨220808, by rfl⟩ : syracuseStep 4710581 = 441617) (by norm_num)
theorem B3140387 : Blo 2093435 3140387 := bstep (se 1 (by rfl) ⟨2355290, by rfl⟩ : syracuseStep 3140387 = 4710581) B4710581
theorem B2093591 : Blo 2093435 2093591 := bstep (se 1 (by rfl) ⟨1570193, by rfl⟩ : syracuseStep 2093591 = 3140387) B3140387
theorem B2515153 : Blo 2093435 2515153 := bbase (se 2 (by rfl) ⟨943182, by rfl⟩ : syracuseStep 2515153 = 1886365) (by norm_num)
theorem B3353537 : Blo 2093435 3353537 := bstep (se 2 (by rfl) ⟨1257576, by rfl⟩ : syracuseStep 3353537 = 2515153) B2515153
theorem B2235691 : Blo 2093435 2235691 := bstep (se 1 (by rfl) ⟨1676768, by rfl⟩ : syracuseStep 2235691 = 3353537) B3353537
theorem B11923685 : Blo 2093435 11923685 := bstep (se 4 (by rfl) ⟨1117845, by rfl⟩ : syracuseStep 11923685 = 2235691) B2235691
theorem B7949123 : Blo 2093435 7949123 := bstep (se 1 (by rfl) ⟨5961842, by rfl⟩ : syracuseStep 7949123 = 11923685) B11923685
theorem B5299415 : Blo 2093435 5299415 := bstep (se 1 (by rfl) ⟨3974561, by rfl⟩ : syracuseStep 5299415 = 7949123) B7949123
theorem B3532943 : Blo 2093435 3532943 := bstep (se 1 (by rfl) ⟨2649707, by rfl⟩ : syracuseStep 3532943 = 5299415) B5299415
theorem B2355295 : Blo 2093435 2355295 := bstep (se 1 (by rfl) ⟨1766471, by rfl⟩ : syracuseStep 2355295 = 3532943) B3532943
theorem B3140393 : Blo 2093435 3140393 := bstep (se 2 (by rfl) ⟨1177647, by rfl⟩ : syracuseStep 3140393 = 2355295) B2355295
theorem B2093595 : Blo 2093435 2093595 := bstep (se 1 (by rfl) ⟨1570196, by rfl⟩ : syracuseStep 2093595 = 3140393) B3140393
theorem B10743461 : Blo 2093435 10743461 := bbase (se 4 (by rfl) ⟨1007199, by rfl⟩ : syracuseStep 10743461 = 2014399) (by norm_num)
theorem B7162307 : Blo 2093435 7162307 := bstep (se 1 (by rfl) ⟨5371730, by rfl⟩ : syracuseStep 7162307 = 10743461) B10743461
theorem B4774871 : Blo 2093435 4774871 := bstep (se 1 (by rfl) ⟨3581153, by rfl⟩ : syracuseStep 4774871 = 7162307) B7162307
theorem B3183247 : Blo 2093435 3183247 := bstep (se 1 (by rfl) ⟨2387435, by rfl⟩ : syracuseStep 3183247 = 4774871) B4774871
theorem B4244329 : Blo 2093435 4244329 := bstep (se 2 (by rfl) ⟨1591623, by rfl⟩ : syracuseStep 4244329 = 3183247) B3183247
theorem B5659105 : Blo 2093435 5659105 := bstep (se 2 (by rfl) ⟨2122164, by rfl⟩ : syracuseStep 5659105 = 4244329) B4244329
theorem B7545473 : Blo 2093435 7545473 := bstep (se 2 (by rfl) ⟨2829552, by rfl⟩ : syracuseStep 7545473 = 5659105) B5659105
theorem B5030315 : Blo 2093435 5030315 := bstep (se 1 (by rfl) ⟨3772736, by rfl⟩ : syracuseStep 5030315 = 7545473) B7545473
theorem B3353543 : Blo 2093435 3353543 := bstep (se 1 (by rfl) ⟨2515157, by rfl⟩ : syracuseStep 3353543 = 5030315) B5030315
theorem B2235695 : Blo 2093435 2235695 := bstep (se 1 (by rfl) ⟨1676771, by rfl⟩ : syracuseStep 2235695 = 3353543) B3353543
theorem B5961853 : Blo 2093435 5961853 := bstep (se 3 (by rfl) ⟨1117847, by rfl⟩ : syracuseStep 5961853 = 2235695) B2235695
theorem B7949137 : Blo 2093435 7949137 := bstep (se 2 (by rfl) ⟨2980926, by rfl⟩ : syracuseStep 7949137 = 5961853) B5961853
theorem B10598849 : Blo 2093435 10598849 := bstep (se 2 (by rfl) ⟨3974568, by rfl⟩ : syracuseStep 10598849 = 7949137) B7949137
theorem B7065899 : Blo 2093435 7065899 := bstep (se 1 (by rfl) ⟨5299424, by rfl⟩ : syracuseStep 7065899 = 10598849) B10598849
theorem B4710599 : Blo 2093435 4710599 := bstep (se 1 (by rfl) ⟨3532949, by rfl⟩ : syracuseStep 4710599 = 7065899) B7065899
theorem B3140399 : Blo 2093435 3140399 := bstep (se 1 (by rfl) ⟨2355299, by rfl⟩ : syracuseStep 3140399 = 4710599) B4710599
theorem B2093599 : Blo 2093435 2093599 := bstep (se 1 (by rfl) ⟨1570199, by rfl⟩ : syracuseStep 2093599 = 3140399) B3140399
theorem B3140405 : Blo 2093435 3140405 := bbase (se 5 (by rfl) ⟨147206, by rfl⟩ : syracuseStep 3140405 = 294413) (by norm_num)
theorem B2093603 : Blo 2093435 2093603 := bstep (se 1 (by rfl) ⟨1570202, by rfl⟩ : syracuseStep 2093603 = 3140405) B3140405
theorem B5299445 : Blo 2093435 5299445 := bbase (se 5 (by rfl) ⟨248411, by rfl⟩ : syracuseStep 5299445 = 496823) (by norm_num)
theorem B3532963 : Blo 2093435 3532963 := bstep (se 1 (by rfl) ⟨2649722, by rfl⟩ : syracuseStep 3532963 = 5299445) B5299445
theorem B4710617 : Blo 2093435 4710617 := bstep (se 2 (by rfl) ⟨1766481, by rfl⟩ : syracuseStep 4710617 = 3532963) B3532963
theorem B3140411 : Blo 2093435 3140411 := bstep (se 1 (by rfl) ⟨2355308, by rfl⟩ : syracuseStep 3140411 = 4710617) B4710617
theorem B2093607 : Blo 2093435 2093607 := bstep (se 1 (by rfl) ⟨1570205, by rfl⟩ : syracuseStep 2093607 = 3140411) B3140411
theorem B2355313 : Blo 2093435 2355313 := bbase (se 2 (by rfl) ⟨883242, by rfl⟩ : syracuseStep 2355313 = 1766485) (by norm_num)
theorem B3140417 : Blo 2093435 3140417 := bstep (se 2 (by rfl) ⟨1177656, by rfl⟩ : syracuseStep 3140417 = 2355313) B2355313
theorem B2093611 : Blo 2093435 2093611 := bstep (se 1 (by rfl) ⟨1570208, by rfl⟩ : syracuseStep 2093611 = 3140417) B3140417
theorem B3772765 : Blo 2093435 3772765 := bbase (se 3 (by rfl) ⟨707393, by rfl⟩ : syracuseStep 3772765 = 1414787) (by norm_num)
theorem B5030353 : Blo 2093435 5030353 := bstep (se 2 (by rfl) ⟨1886382, by rfl⟩ : syracuseStep 5030353 = 3772765) B3772765
theorem B6707137 : Blo 2093435 6707137 := bstep (se 2 (by rfl) ⟨2515176, by rfl⟩ : syracuseStep 6707137 = 5030353) B5030353
theorem B8942849 : Blo 2093435 8942849 := bstep (se 2 (by rfl) ⟨3353568, by rfl⟩ : syracuseStep 8942849 = 6707137) B6707137
theorem B5961899 : Blo 2093435 5961899 := bstep (se 1 (by rfl) ⟨4471424, by rfl⟩ : syracuseStep 5961899 = 8942849) B8942849
theorem B3974599 : Blo 2093435 3974599 := bstep (se 1 (by rfl) ⟨2980949, by rfl⟩ : syracuseStep 3974599 = 5961899) B5961899
theorem B5299465 : Blo 2093435 5299465 := bstep (se 2 (by rfl) ⟨1987299, by rfl⟩ : syracuseStep 5299465 = 3974599) B3974599
theorem B7065953 : Blo 2093435 7065953 := bstep (se 2 (by rfl) ⟨2649732, by rfl⟩ : syracuseStep 7065953 = 5299465) B5299465
theorem B4710635 : Blo 2093435 4710635 := bstep (se 1 (by rfl) ⟨3532976, by rfl⟩ : syracuseStep 4710635 = 7065953) B7065953
theorem B3140423 : Blo 2093435 3140423 := bstep (se 1 (by rfl) ⟨2355317, by rfl⟩ : syracuseStep 3140423 = 4710635) B4710635
theorem B2093615 : Blo 2093435 2093615 := bstep (se 1 (by rfl) ⟨1570211, by rfl⟩ : syracuseStep 2093615 = 3140423) B3140423
theorem B3140429 : Blo 2093435 3140429 := bbase (se 3 (by rfl) ⟨588830, by rfl⟩ : syracuseStep 3140429 = 1177661) (by norm_num)
theorem B2093619 : Blo 2093435 2093619 := bstep (se 1 (by rfl) ⟨1570214, by rfl⟩ : syracuseStep 2093619 = 3140429) B3140429
theorem B4710653 : Blo 2093435 4710653 := bbase (se 3 (by rfl) ⟨883247, by rfl⟩ : syracuseStep 4710653 = 1766495) (by norm_num)
theorem B3140435 : Blo 2093435 3140435 := bstep (se 1 (by rfl) ⟨2355326, by rfl⟩ : syracuseStep 3140435 = 4710653) B4710653
theorem B2093623 : Blo 2093435 2093623 := bstep (se 1 (by rfl) ⟨1570217, by rfl⟩ : syracuseStep 2093623 = 3140435) B3140435
theorem B3532997 : Blo 2093435 3532997 := bbase (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) (by norm_num)
theorem B2355331 : Blo 2093435 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B3140441 : Blo 2093435 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B2093627 : Blo 2093435 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B15898517 : Blo 2093435 15898517 := bbase (se 6 (by rfl) ⟨372621, by rfl⟩ : syracuseStep 15898517 = 745243) (by norm_num)
theorem B10599011 : Blo 2093435 10599011 := bstep (se 1 (by rfl) ⟨7949258, by rfl⟩ : syracuseStep 10599011 = 15898517) B15898517
theorem B7066007 : Blo 2093435 7066007 := bstep (se 1 (by rfl) ⟨5299505, by rfl⟩ : syracuseStep 7066007 = 10599011) B10599011
theorem B4710671 : Blo 2093435 4710671 := bstep (se 1 (by rfl) ⟨3533003, by rfl⟩ : syracuseStep 4710671 = 7066007) B7066007
theorem B3140447 : Blo 2093435 3140447 := bstep (se 1 (by rfl) ⟨2355335, by rfl⟩ : syracuseStep 3140447 = 4710671) B4710671
theorem B2093631 : Blo 2093435 2093631 := bstep (se 1 (by rfl) ⟨1570223, by rfl⟩ : syracuseStep 2093631 = 3140447) B3140447
theorem B3140453 : Blo 2093435 3140453 := bbase (se 4 (by rfl) ⟨294417, by rfl⟩ : syracuseStep 3140453 = 588835) (by norm_num)
theorem B2093635 : Blo 2093435 2093635 := bstep (se 1 (by rfl) ⟨1570226, by rfl⟩ : syracuseStep 2093635 = 3140453) B3140453
theorem B3974645 : Blo 2093435 3974645 := bbase (se 5 (by rfl) ⟨186311, by rfl⟩ : syracuseStep 3974645 = 372623) (by norm_num)
theorem B2649763 : Blo 2093435 2649763 := bstep (se 1 (by rfl) ⟨1987322, by rfl⟩ : syracuseStep 2649763 = 3974645) B3974645
theorem B3533017 : Blo 2093435 3533017 := bstep (se 2 (by rfl) ⟨1324881, by rfl⟩ : syracuseStep 3533017 = 2649763) B2649763
theorem B4710689 : Blo 2093435 4710689 := bstep (se 2 (by rfl) ⟨1766508, by rfl⟩ : syracuseStep 4710689 = 3533017) B3533017
theorem B3140459 : Blo 2093435 3140459 := bstep (se 1 (by rfl) ⟨2355344, by rfl⟩ : syracuseStep 3140459 = 4710689) B4710689
theorem B2093639 : Blo 2093435 2093639 := bstep (se 1 (by rfl) ⟨1570229, by rfl⟩ : syracuseStep 2093639 = 3140459) B3140459
theorem B2355349 : Blo 2093435 2355349 := bbase (se 6 (by rfl) ⟨55203, by rfl⟩ : syracuseStep 2355349 = 110407) (by norm_num)
theorem B3140465 : Blo 2093435 3140465 := bstep (se 2 (by rfl) ⟨1177674, by rfl⟩ : syracuseStep 3140465 = 2355349) B2355349
theorem B2093643 : Blo 2093435 2093643 := bstep (se 1 (by rfl) ⟨1570232, by rfl⟩ : syracuseStep 2093643 = 3140465) B3140465
theorem B2649773 : Blo 2093435 2649773 := bbase (se 3 (by rfl) ⟨496832, by rfl⟩ : syracuseStep 2649773 = 993665) (by norm_num)
theorem B7066061 : Blo 2093435 7066061 := bstep (se 3 (by rfl) ⟨1324886, by rfl⟩ : syracuseStep 7066061 = 2649773) B2649773
theorem B4710707 : Blo 2093435 4710707 := bstep (se 1 (by rfl) ⟨3533030, by rfl⟩ : syracuseStep 4710707 = 7066061) B7066061
theorem B3140471 : Blo 2093435 3140471 := bstep (se 1 (by rfl) ⟨2355353, by rfl⟩ : syracuseStep 3140471 = 4710707) B4710707
theorem B2093647 : Blo 2093435 2093647 := bstep (se 1 (by rfl) ⟨1570235, by rfl⟩ : syracuseStep 2093647 = 3140471) B3140471
theorem B3140477 : Blo 2093435 3140477 := bbase (se 3 (by rfl) ⟨588839, by rfl⟩ : syracuseStep 3140477 = 1177679) (by norm_num)
theorem B2093651 : Blo 2093435 2093651 := bstep (se 1 (by rfl) ⟨1570238, by rfl⟩ : syracuseStep 2093651 = 3140477) B3140477
theorem B4710725 : Blo 2093435 4710725 := bbase (se 4 (by rfl) ⟨441630, by rfl⟩ : syracuseStep 4710725 = 883261) (by norm_num)
theorem B3140483 : Blo 2093435 3140483 := bstep (se 1 (by rfl) ⟨2355362, by rfl⟩ : syracuseStep 3140483 = 4710725) B4710725
theorem B2093655 : Blo 2093435 2093655 := bstep (se 1 (by rfl) ⟨1570241, by rfl⟩ : syracuseStep 2093655 = 3140483) B3140483
theorem B8488901 : Blo 2093435 8488901 := bbase (se 4 (by rfl) ⟨795834, by rfl⟩ : syracuseStep 8488901 = 1591669) (by norm_num)
theorem B22637069 : Blo 2093435 22637069 := bstep (se 3 (by rfl) ⟨4244450, by rfl⟩ : syracuseStep 22637069 = 8488901) B8488901
theorem B15091379 : Blo 2093435 15091379 := bstep (se 1 (by rfl) ⟨11318534, by rfl⟩ : syracuseStep 15091379 = 22637069) B22637069
theorem B10060919 : Blo 2093435 10060919 := bstep (se 1 (by rfl) ⟨7545689, by rfl⟩ : syracuseStep 10060919 = 15091379) B15091379
theorem B6707279 : Blo 2093435 6707279 := bstep (se 1 (by rfl) ⟨5030459, by rfl⟩ : syracuseStep 6707279 = 10060919) B10060919
theorem B4471519 : Blo 2093435 4471519 := bstep (se 1 (by rfl) ⟨3353639, by rfl⟩ : syracuseStep 4471519 = 6707279) B6707279
theorem B5962025 : Blo 2093435 5962025 := bstep (se 2 (by rfl) ⟨2235759, by rfl⟩ : syracuseStep 5962025 = 4471519) B4471519
theorem B3974683 : Blo 2093435 3974683 := bstep (se 1 (by rfl) ⟨2981012, by rfl⟩ : syracuseStep 3974683 = 5962025) B5962025
theorem B5299577 : Blo 2093435 5299577 := bstep (se 2 (by rfl) ⟨1987341, by rfl⟩ : syracuseStep 5299577 = 3974683) B3974683
theorem B3533051 : Blo 2093435 3533051 := bstep (se 1 (by rfl) ⟨2649788, by rfl⟩ : syracuseStep 3533051 = 5299577) B5299577
theorem B2355367 : Blo 2093435 2355367 := bstep (se 1 (by rfl) ⟨1766525, by rfl⟩ : syracuseStep 2355367 = 3533051) B3533051
theorem B3140489 : Blo 2093435 3140489 := bstep (se 2 (by rfl) ⟨1177683, by rfl⟩ : syracuseStep 3140489 = 2355367) B2355367
theorem B2093659 : Blo 2093435 2093659 := bstep (se 1 (by rfl) ⟨1570244, by rfl⟩ : syracuseStep 2093659 = 3140489) B3140489
theorem B10599173 : Blo 2093435 10599173 := bbase (se 4 (by rfl) ⟨993672, by rfl⟩ : syracuseStep 10599173 = 1987345) (by norm_num)
theorem B7066115 : Blo 2093435 7066115 := bstep (se 1 (by rfl) ⟨5299586, by rfl⟩ : syracuseStep 7066115 = 10599173) B10599173
theorem B4710743 : Blo 2093435 4710743 := bstep (se 1 (by rfl) ⟨3533057, by rfl⟩ : syracuseStep 4710743 = 7066115) B7066115
theorem B3140495 : Blo 2093435 3140495 := bstep (se 1 (by rfl) ⟨2355371, by rfl⟩ : syracuseStep 3140495 = 4710743) B4710743
theorem B2093663 : Blo 2093435 2093663 := bstep (se 1 (by rfl) ⟨1570247, by rfl⟩ : syracuseStep 2093663 = 3140495) B3140495
theorem B3140501 : Blo 2093435 3140501 := bbase (se 6 (by rfl) ⟨73605, by rfl⟩ : syracuseStep 3140501 = 147211) (by norm_num)
theorem B2093667 : Blo 2093435 2093667 := bstep (se 1 (by rfl) ⟨1570250, by rfl⟩ : syracuseStep 2093667 = 3140501) B3140501
theorem B11924117 : Blo 2093435 11924117 := bbase (se 6 (by rfl) ⟨279471, by rfl⟩ : syracuseStep 11924117 = 558943) (by norm_num)
theorem B7949411 : Blo 2093435 7949411 := bstep (se 1 (by rfl) ⟨5962058, by rfl⟩ : syracuseStep 7949411 = 11924117) B11924117
theorem B5299607 : Blo 2093435 5299607 := bstep (se 1 (by rfl) ⟨3974705, by rfl⟩ : syracuseStep 5299607 = 7949411) B7949411
theorem B3533071 : Blo 2093435 3533071 := bstep (se 1 (by rfl) ⟨2649803, by rfl⟩ : syracuseStep 3533071 = 5299607) B5299607
theorem B4710761 : Blo 2093435 4710761 := bstep (se 2 (by rfl) ⟨1766535, by rfl⟩ : syracuseStep 4710761 = 3533071) B3533071
theorem B3140507 : Blo 2093435 3140507 := bstep (se 1 (by rfl) ⟨2355380, by rfl⟩ : syracuseStep 3140507 = 4710761) B4710761
theorem B2093671 : Blo 2093435 2093671 := bstep (se 1 (by rfl) ⟨1570253, by rfl⟩ : syracuseStep 2093671 = 3140507) B3140507
theorem B2355385 : Blo 2093435 2355385 := bbase (se 2 (by rfl) ⟨883269, by rfl⟩ : syracuseStep 2355385 = 1766539) (by norm_num)
theorem B3140513 : Blo 2093435 3140513 := bstep (se 2 (by rfl) ⟨1177692, by rfl⟩ : syracuseStep 3140513 = 2355385) B2355385
theorem B2093675 : Blo 2093435 2093675 := bstep (se 1 (by rfl) ⟨1570256, by rfl⟩ : syracuseStep 2093675 = 3140513) B3140513
theorem B4775053 : Blo 2093435 4775053 := bbase (se 3 (by rfl) ⟨895322, by rfl⟩ : syracuseStep 4775053 = 1790645) (by norm_num)
theorem B6366737 : Blo 2093435 6366737 := bstep (se 2 (by rfl) ⟨2387526, by rfl⟩ : syracuseStep 6366737 = 4775053) B4775053
theorem B4244491 : Blo 2093435 4244491 := bstep (se 1 (by rfl) ⟨3183368, by rfl⟩ : syracuseStep 4244491 = 6366737) B6366737
theorem B5659321 : Blo 2093435 5659321 := bstep (se 2 (by rfl) ⟨2122245, by rfl⟩ : syracuseStep 5659321 = 4244491) B4244491
theorem B7545761 : Blo 2093435 7545761 := bstep (se 2 (by rfl) ⟨2829660, by rfl⟩ : syracuseStep 7545761 = 5659321) B5659321
theorem B5030507 : Blo 2093435 5030507 := bstep (se 1 (by rfl) ⟨3772880, by rfl⟩ : syracuseStep 5030507 = 7545761) B7545761
theorem B3353671 : Blo 2093435 3353671 := bstep (se 1 (by rfl) ⟨2515253, by rfl⟩ : syracuseStep 3353671 = 5030507) B5030507
theorem B4471561 : Blo 2093435 4471561 := bstep (se 2 (by rfl) ⟨1676835, by rfl⟩ : syracuseStep 4471561 = 3353671) B3353671
theorem B5962081 : Blo 2093435 5962081 := bstep (se 2 (by rfl) ⟨2235780, by rfl⟩ : syracuseStep 5962081 = 4471561) B4471561
theorem B7949441 : Blo 2093435 7949441 := bstep (se 2 (by rfl) ⟨2981040, by rfl⟩ : syracuseStep 7949441 = 5962081) B5962081
theorem B5299627 : Blo 2093435 5299627 := bstep (se 1 (by rfl) ⟨3974720, by rfl⟩ : syracuseStep 5299627 = 7949441) B7949441
theorem B7066169 : Blo 2093435 7066169 := bstep (se 2 (by rfl) ⟨2649813, by rfl⟩ : syracuseStep 7066169 = 5299627) B5299627
theorem B4710779 : Blo 2093435 4710779 := bstep (se 1 (by rfl) ⟨3533084, by rfl⟩ : syracuseStep 4710779 = 7066169) B7066169
theorem B3140519 : Blo 2093435 3140519 := bstep (se 1 (by rfl) ⟨2355389, by rfl⟩ : syracuseStep 3140519 = 4710779) B4710779
theorem B2093679 : Blo 2093435 2093679 := bstep (se 1 (by rfl) ⟨1570259, by rfl⟩ : syracuseStep 2093679 = 3140519) B3140519
theorem B3140525 : Blo 2093435 3140525 := bbase (se 3 (by rfl) ⟨588848, by rfl⟩ : syracuseStep 3140525 = 1177697) (by norm_num)
theorem B2093683 : Blo 2093435 2093683 := bstep (se 1 (by rfl) ⟨1570262, by rfl⟩ : syracuseStep 2093683 = 3140525) B3140525
theorem B4710797 : Blo 2093435 4710797 := bbase (se 3 (by rfl) ⟨883274, by rfl⟩ : syracuseStep 4710797 = 1766549) (by norm_num)
theorem B3140531 : Blo 2093435 3140531 := bstep (se 1 (by rfl) ⟨2355398, by rfl⟩ : syracuseStep 3140531 = 4710797) B4710797
theorem B2093687 : Blo 2093435 2093687 := bstep (se 1 (by rfl) ⟨1570265, by rfl⟩ : syracuseStep 2093687 = 3140531) B3140531
theorem B2649829 : Blo 2093435 2649829 := bbase (se 4 (by rfl) ⟨248421, by rfl⟩ : syracuseStep 2649829 = 496843) (by norm_num)
theorem B3533105 : Blo 2093435 3533105 := bstep (se 2 (by rfl) ⟨1324914, by rfl⟩ : syracuseStep 3533105 = 2649829) B2649829
theorem B2355403 : Blo 2093435 2355403 := bstep (se 1 (by rfl) ⟨1766552, by rfl⟩ : syracuseStep 2355403 = 3533105) B3533105
theorem B3140537 : Blo 2093435 3140537 := bstep (se 2 (by rfl) ⟨1177701, by rfl⟩ : syracuseStep 3140537 = 2355403) B2355403
theorem B2093691 : Blo 2093435 2093691 := bstep (se 1 (by rfl) ⟨1570268, by rfl⟩ : syracuseStep 2093691 = 3140537) B3140537
theorem B2122261 : Blo 2093435 2122261 := bbase (se 6 (by rfl) ⟨49740, by rfl⟩ : syracuseStep 2122261 = 99481) (by norm_num)
theorem B11318725 : Blo 2093435 11318725 := bstep (se 4 (by rfl) ⟨1061130, by rfl⟩ : syracuseStep 11318725 = 2122261) B2122261
theorem B15091633 : Blo 2093435 15091633 := bstep (se 2 (by rfl) ⟨5659362, by rfl⟩ : syracuseStep 15091633 = 11318725) B11318725
theorem B20122177 : Blo 2093435 20122177 := bstep (se 2 (by rfl) ⟨7545816, by rfl⟩ : syracuseStep 20122177 = 15091633) B15091633
theorem B26829569 : Blo 2093435 26829569 := bstep (se 2 (by rfl) ⟨10061088, by rfl⟩ : syracuseStep 26829569 = 20122177) B20122177
theorem B17886379 : Blo 2093435 17886379 := bstep (se 1 (by rfl) ⟨13414784, by rfl⟩ : syracuseStep 17886379 = 26829569) B26829569
theorem B23848505 : Blo 2093435 23848505 := bstep (se 2 (by rfl) ⟨8943189, by rfl⟩ : syracuseStep 23848505 = 17886379) B17886379
theorem B15899003 : Blo 2093435 15899003 := bstep (se 1 (by rfl) ⟨11924252, by rfl⟩ : syracuseStep 15899003 = 23848505) B23848505
theorem B10599335 : Blo 2093435 10599335 := bstep (se 1 (by rfl) ⟨7949501, by rfl⟩ : syracuseStep 10599335 = 15899003) B15899003
theorem B7066223 : Blo 2093435 7066223 := bstep (se 1 (by rfl) ⟨5299667, by rfl⟩ : syracuseStep 7066223 = 10599335) B10599335
theorem B4710815 : Blo 2093435 4710815 := bstep (se 1 (by rfl) ⟨3533111, by rfl⟩ : syracuseStep 4710815 = 7066223) B7066223
theorem B3140543 : Blo 2093435 3140543 := bstep (se 1 (by rfl) ⟨2355407, by rfl⟩ : syracuseStep 3140543 = 4710815) B4710815
theorem B2093695 : Blo 2093435 2093695 := bstep (se 1 (by rfl) ⟨1570271, by rfl⟩ : syracuseStep 2093695 = 3140543) B3140543
theorem B3140549 : Blo 2093435 3140549 := bbase (se 4 (by rfl) ⟨294426, by rfl⟩ : syracuseStep 3140549 = 588853) (by norm_num)
theorem B2093699 : Blo 2093435 2093699 := bstep (se 1 (by rfl) ⟨1570274, by rfl⟩ : syracuseStep 2093699 = 3140549) B3140549
theorem B3533125 : Blo 2093435 3533125 := bbase (se 4 (by rfl) ⟨331230, by rfl⟩ : syracuseStep 3533125 = 662461) (by norm_num)
theorem B4710833 : Blo 2093435 4710833 := bstep (se 2 (by rfl) ⟨1766562, by rfl⟩ : syracuseStep 4710833 = 3533125) B3533125
theorem B3140555 : Blo 2093435 3140555 := bstep (se 1 (by rfl) ⟨2355416, by rfl⟩ : syracuseStep 3140555 = 4710833) B4710833
theorem B2093703 : Blo 2093435 2093703 := bstep (se 1 (by rfl) ⟨1570277, by rfl⟩ : syracuseStep 2093703 = 3140555) B3140555
theorem B2355421 : Blo 2093435 2355421 := bbase (se 3 (by rfl) ⟨441641, by rfl⟩ : syracuseStep 2355421 = 883283) (by norm_num)
theorem B3140561 : Blo 2093435 3140561 := bstep (se 2 (by rfl) ⟨1177710, by rfl⟩ : syracuseStep 3140561 = 2355421) B2355421
theorem B2093707 : Blo 2093435 2093707 := bstep (se 1 (by rfl) ⟨1570280, by rfl⟩ : syracuseStep 2093707 = 3140561) B3140561
theorem B7066277 : Blo 2093435 7066277 := bbase (se 4 (by rfl) ⟨662463, by rfl⟩ : syracuseStep 7066277 = 1324927) (by norm_num)
theorem B4710851 : Blo 2093435 4710851 := bstep (se 1 (by rfl) ⟨3533138, by rfl⟩ : syracuseStep 4710851 = 7066277) B7066277
theorem B3140567 : Blo 2093435 3140567 := bstep (se 1 (by rfl) ⟨2355425, by rfl⟩ : syracuseStep 3140567 = 4710851) B4710851
theorem B2093711 : Blo 2093435 2093711 := bstep (se 1 (by rfl) ⟨1570283, by rfl⟩ : syracuseStep 2093711 = 3140567) B3140567
theorem B3140573 : Blo 2093435 3140573 := bbase (se 3 (by rfl) ⟨588857, by rfl⟩ : syracuseStep 3140573 = 1177715) (by norm_num)
theorem B2093715 : Blo 2093435 2093715 := bstep (se 1 (by rfl) ⟨1570286, by rfl⟩ : syracuseStep 2093715 = 3140573) B3140573
theorem B4710869 : Blo 2093435 4710869 := bbase (se 7 (by rfl) ⟨55205, by rfl⟩ : syracuseStep 4710869 = 110411) (by norm_num)
theorem B3140579 : Blo 2093435 3140579 := bstep (se 1 (by rfl) ⟨2355434, by rfl⟩ : syracuseStep 3140579 = 4710869) B4710869
theorem B2093719 : Blo 2093435 2093719 := bstep (se 1 (by rfl) ⟨1570289, by rfl⟩ : syracuseStep 2093719 = 3140579) B3140579
theorem B3824437 : Blo 2093435 3824437 := bbase (se 5 (by rfl) ⟨179270, by rfl⟩ : syracuseStep 3824437 = 358541) (by norm_num)
theorem B5099249 : Blo 2093435 5099249 := bstep (se 2 (by rfl) ⟨1912218, by rfl⟩ : syracuseStep 5099249 = 3824437) B3824437
theorem B3399499 : Blo 2093435 3399499 := bstep (se 1 (by rfl) ⟨2549624, by rfl⟩ : syracuseStep 3399499 = 5099249) B5099249
theorem B4532665 : Blo 2093435 4532665 := bstep (se 2 (by rfl) ⟨1699749, by rfl⟩ : syracuseStep 4532665 = 3399499) B3399499
theorem B6043553 : Blo 2093435 6043553 := bstep (se 2 (by rfl) ⟨2266332, by rfl⟩ : syracuseStep 6043553 = 4532665) B4532665
theorem B4029035 : Blo 2093435 4029035 := bstep (se 1 (by rfl) ⟨3021776, by rfl⟩ : syracuseStep 4029035 = 6043553) B6043553
theorem B10744093 : Blo 2093435 10744093 := bstep (se 3 (by rfl) ⟨2014517, by rfl⟩ : syracuseStep 10744093 = 4029035) B4029035
theorem B57301829 : Blo 2093435 57301829 := bstep (se 4 (by rfl) ⟨5372046, by rfl⟩ : syracuseStep 57301829 = 10744093) B10744093
theorem B38201219 : Blo 2093435 38201219 := bstep (se 1 (by rfl) ⟨28650914, by rfl⟩ : syracuseStep 38201219 = 57301829) B57301829
theorem B25467479 : Blo 2093435 25467479 := bstep (se 1 (by rfl) ⟨19100609, by rfl⟩ : syracuseStep 25467479 = 38201219) B38201219
theorem B16978319 : Blo 2093435 16978319 := bstep (se 1 (by rfl) ⟨12733739, by rfl⟩ : syracuseStep 16978319 = 25467479) B25467479
theorem B11318879 : Blo 2093435 11318879 := bstep (se 1 (by rfl) ⟨8489159, by rfl⟩ : syracuseStep 11318879 = 16978319) B16978319
theorem B30183677 : Blo 2093435 30183677 := bstep (se 3 (by rfl) ⟨5659439, by rfl⟩ : syracuseStep 30183677 = 11318879) B11318879
theorem B20122451 : Blo 2093435 20122451 := bstep (se 1 (by rfl) ⟨15091838, by rfl⟩ : syracuseStep 20122451 = 30183677) B30183677
theorem B13414967 : Blo 2093435 13414967 := bstep (se 1 (by rfl) ⟨10061225, by rfl⟩ : syracuseStep 13414967 = 20122451) B20122451
theorem B8943311 : Blo 2093435 8943311 := bstep (se 1 (by rfl) ⟨6707483, by rfl⟩ : syracuseStep 8943311 = 13414967) B13414967
theorem B5962207 : Blo 2093435 5962207 := bstep (se 1 (by rfl) ⟨4471655, by rfl⟩ : syracuseStep 5962207 = 8943311) B8943311
theorem B7949609 : Blo 2093435 7949609 := bstep (se 2 (by rfl) ⟨2981103, by rfl⟩ : syracuseStep 7949609 = 5962207) B5962207
theorem B5299739 : Blo 2093435 5299739 := bstep (se 1 (by rfl) ⟨3974804, by rfl⟩ : syracuseStep 5299739 = 7949609) B7949609
theorem B3533159 : Blo 2093435 3533159 := bstep (se 1 (by rfl) ⟨2649869, by rfl⟩ : syracuseStep 3533159 = 5299739) B5299739
theorem B2355439 : Blo 2093435 2355439 := bstep (se 1 (by rfl) ⟨1766579, by rfl⟩ : syracuseStep 2355439 = 3533159) B3533159
theorem B3140585 : Blo 2093435 3140585 := bstep (se 2 (by rfl) ⟨1177719, by rfl⟩ : syracuseStep 3140585 = 2355439) B2355439
theorem B2093723 : Blo 2093435 2093723 := bstep (se 1 (by rfl) ⟨1570292, by rfl⟩ : syracuseStep 2093723 = 3140585) B3140585
theorem B2266337 : Blo 2093435 2266337 := bbase (se 2 (by rfl) ⟨849876, by rfl⟩ : syracuseStep 2266337 = 1699753) (by norm_num)
theorem B6043565 : Blo 2093435 6043565 := bstep (se 3 (by rfl) ⟨1133168, by rfl⟩ : syracuseStep 6043565 = 2266337) B2266337
theorem B4029043 : Blo 2093435 4029043 := bstep (se 1 (by rfl) ⟨3021782, by rfl⟩ : syracuseStep 4029043 = 6043565) B6043565
theorem B5372057 : Blo 2093435 5372057 := bstep (se 2 (by rfl) ⟨2014521, by rfl⟩ : syracuseStep 5372057 = 4029043) B4029043
theorem B3581371 : Blo 2093435 3581371 := bstep (se 1 (by rfl) ⟨2686028, by rfl⟩ : syracuseStep 3581371 = 5372057) B5372057
theorem B4775161 : Blo 2093435 4775161 := bstep (se 2 (by rfl) ⟨1790685, by rfl⟩ : syracuseStep 4775161 = 3581371) B3581371
theorem B6366881 : Blo 2093435 6366881 := bstep (se 2 (by rfl) ⟨2387580, by rfl⟩ : syracuseStep 6366881 = 4775161) B4775161
theorem B16978349 : Blo 2093435 16978349 := bstep (se 3 (by rfl) ⟨3183440, by rfl⟩ : syracuseStep 16978349 = 6366881) B6366881
theorem B11318899 : Blo 2093435 11318899 := bstep (se 1 (by rfl) ⟨8489174, by rfl⟩ : syracuseStep 11318899 = 16978349) B16978349
theorem B15091865 : Blo 2093435 15091865 := bstep (se 2 (by rfl) ⟨5659449, by rfl⟩ : syracuseStep 15091865 = 11318899) B11318899
theorem B10061243 : Blo 2093435 10061243 := bstep (se 1 (by rfl) ⟨7545932, by rfl⟩ : syracuseStep 10061243 = 15091865) B15091865
theorem B6707495 : Blo 2093435 6707495 := bstep (se 1 (by rfl) ⟨5030621, by rfl⟩ : syracuseStep 6707495 = 10061243) B10061243
theorem B17886653 : Blo 2093435 17886653 := bstep (se 3 (by rfl) ⟨3353747, by rfl⟩ : syracuseStep 17886653 = 6707495) B6707495
theorem B11924435 : Blo 2093435 11924435 := bstep (se 1 (by rfl) ⟨8943326, by rfl⟩ : syracuseStep 11924435 = 17886653) B17886653
theorem B7949623 : Blo 2093435 7949623 := bstep (se 1 (by rfl) ⟨5962217, by rfl⟩ : syracuseStep 7949623 = 11924435) B11924435
theorem B10599497 : Blo 2093435 10599497 := bstep (se 2 (by rfl) ⟨3974811, by rfl⟩ : syracuseStep 10599497 = 7949623) B7949623
theorem B7066331 : Blo 2093435 7066331 := bstep (se 1 (by rfl) ⟨5299748, by rfl⟩ : syracuseStep 7066331 = 10599497) B10599497
theorem B4710887 : Blo 2093435 4710887 := bstep (se 1 (by rfl) ⟨3533165, by rfl⟩ : syracuseStep 4710887 = 7066331) B7066331
theorem B3140591 : Blo 2093435 3140591 := bstep (se 1 (by rfl) ⟨2355443, by rfl⟩ : syracuseStep 3140591 = 4710887) B4710887
theorem B2093727 : Blo 2093435 2093727 := bstep (se 1 (by rfl) ⟨1570295, by rfl⟩ : syracuseStep 2093727 = 3140591) B3140591
theorem B3140597 : Blo 2093435 3140597 := bbase (se 5 (by rfl) ⟨147215, by rfl⟩ : syracuseStep 3140597 = 294431) (by norm_num)
theorem B2093731 : Blo 2093435 2093731 := bstep (se 1 (by rfl) ⟨1570298, by rfl⟩ : syracuseStep 2093731 = 3140597) B3140597
theorem B2515321 : Blo 2093435 2515321 := bbase (se 2 (by rfl) ⟨943245, by rfl⟩ : syracuseStep 2515321 = 1886491) (by norm_num)
theorem B3353761 : Blo 2093435 3353761 := bstep (se 2 (by rfl) ⟨1257660, by rfl⟩ : syracuseStep 3353761 = 2515321) B2515321
theorem B4471681 : Blo 2093435 4471681 := bstep (se 2 (by rfl) ⟨1676880, by rfl⟩ : syracuseStep 4471681 = 3353761) B3353761
theorem B5962241 : Blo 2093435 5962241 := bstep (se 2 (by rfl) ⟨2235840, by rfl⟩ : syracuseStep 5962241 = 4471681) B4471681
theorem B3974827 : Blo 2093435 3974827 := bstep (se 1 (by rfl) ⟨2981120, by rfl⟩ : syracuseStep 3974827 = 5962241) B5962241
theorem B5299769 : Blo 2093435 5299769 := bstep (se 2 (by rfl) ⟨1987413, by rfl⟩ : syracuseStep 5299769 = 3974827) B3974827
theorem B3533179 : Blo 2093435 3533179 := bstep (se 1 (by rfl) ⟨2649884, by rfl⟩ : syracuseStep 3533179 = 5299769) B5299769
theorem B4710905 : Blo 2093435 4710905 := bstep (se 2 (by rfl) ⟨1766589, by rfl⟩ : syracuseStep 4710905 = 3533179) B3533179
theorem B3140603 : Blo 2093435 3140603 := bstep (se 1 (by rfl) ⟨2355452, by rfl⟩ : syracuseStep 3140603 = 4710905) B4710905
theorem B2093735 : Blo 2093435 2093735 := bstep (se 1 (by rfl) ⟨1570301, by rfl⟩ : syracuseStep 2093735 = 3140603) B3140603
theorem B2355457 : Blo 2093435 2355457 := bbase (se 2 (by rfl) ⟨883296, by rfl⟩ : syracuseStep 2355457 = 1766593) (by norm_num)
theorem B3140609 : Blo 2093435 3140609 := bstep (se 2 (by rfl) ⟨1177728, by rfl⟩ : syracuseStep 3140609 = 2355457) B2355457
theorem B2093739 : Blo 2093435 2093739 := bstep (se 1 (by rfl) ⟨1570304, by rfl⟩ : syracuseStep 2093739 = 3140609) B3140609
theorem B5299789 : Blo 2093435 5299789 := bbase (se 3 (by rfl) ⟨993710, by rfl⟩ : syracuseStep 5299789 = 1987421) (by norm_num)
theorem B7066385 : Blo 2093435 7066385 := bstep (se 2 (by rfl) ⟨2649894, by rfl⟩ : syracuseStep 7066385 = 5299789) B5299789
theorem B4710923 : Blo 2093435 4710923 := bstep (se 1 (by rfl) ⟨3533192, by rfl⟩ : syracuseStep 4710923 = 7066385) B7066385
theorem B3140615 : Blo 2093435 3140615 := bstep (se 1 (by rfl) ⟨2355461, by rfl⟩ : syracuseStep 3140615 = 4710923) B4710923
theorem B2093743 : Blo 2093435 2093743 := bstep (se 1 (by rfl) ⟨1570307, by rfl⟩ : syracuseStep 2093743 = 3140615) B3140615
theorem B3140621 : Blo 2093435 3140621 := bbase (se 3 (by rfl) ⟨588866, by rfl⟩ : syracuseStep 3140621 = 1177733) (by norm_num)
theorem B2093747 : Blo 2093435 2093747 := bstep (se 1 (by rfl) ⟨1570310, by rfl⟩ : syracuseStep 2093747 = 3140621) B3140621
theorem B4710941 : Blo 2093435 4710941 := bbase (se 3 (by rfl) ⟨883301, by rfl⟩ : syracuseStep 4710941 = 1766603) (by norm_num)
theorem B3140627 : Blo 2093435 3140627 := bstep (se 1 (by rfl) ⟨2355470, by rfl⟩ : syracuseStep 3140627 = 4710941) B4710941
theorem B2093751 : Blo 2093435 2093751 := bstep (se 1 (by rfl) ⟨1570313, by rfl⟩ : syracuseStep 2093751 = 3140627) B3140627
theorem B3533213 : Blo 2093435 3533213 := bbase (se 3 (by rfl) ⟨662477, by rfl⟩ : syracuseStep 3533213 = 1324955) (by norm_num)
theorem B2355475 : Blo 2093435 2355475 := bstep (se 1 (by rfl) ⟨1766606, by rfl⟩ : syracuseStep 2355475 = 3533213) B3533213
theorem B3140633 : Blo 2093435 3140633 := bstep (se 2 (by rfl) ⟨1177737, by rfl⟩ : syracuseStep 3140633 = 2355475) B2355475
theorem B2093755 : Blo 2093435 2093755 := bstep (se 1 (by rfl) ⟨1570316, by rfl⟩ : syracuseStep 2093755 = 3140633) B3140633
theorem B3824501 : Blo 2093435 3824501 := bbase (se 5 (by rfl) ⟨179273, by rfl⟩ : syracuseStep 3824501 = 358547) (by norm_num)
theorem B10198669 : Blo 2093435 10198669 := bstep (se 3 (by rfl) ⟨1912250, by rfl⟩ : syracuseStep 10198669 = 3824501) B3824501
theorem B13598225 : Blo 2093435 13598225 := bstep (se 2 (by rfl) ⟨5099334, by rfl⟩ : syracuseStep 13598225 = 10198669) B10198669
theorem B9065483 : Blo 2093435 9065483 := bstep (se 1 (by rfl) ⟨6799112, by rfl⟩ : syracuseStep 9065483 = 13598225) B13598225
theorem B6043655 : Blo 2093435 6043655 := bstep (se 1 (by rfl) ⟨4532741, by rfl⟩ : syracuseStep 6043655 = 9065483) B9065483
theorem B16116413 : Blo 2093435 16116413 := bstep (se 3 (by rfl) ⟨3021827, by rfl⟩ : syracuseStep 16116413 = 6043655) B6043655
theorem B171908405 : Blo 2093435 171908405 := bstep (se 5 (by rfl) ⟨8058206, by rfl⟩ : syracuseStep 171908405 = 16116413) B16116413
theorem B114605603 : Blo 2093435 114605603 := bstep (se 1 (by rfl) ⟨85954202, by rfl⟩ : syracuseStep 114605603 = 171908405) B171908405
theorem B76403735 : Blo 2093435 76403735 := bstep (se 1 (by rfl) ⟨57302801, by rfl⟩ : syracuseStep 76403735 = 114605603) B114605603
theorem B50935823 : Blo 2093435 50935823 := bstep (se 1 (by rfl) ⟨38201867, by rfl⟩ : syracuseStep 50935823 = 76403735) B76403735
theorem B33957215 : Blo 2093435 33957215 := bstep (se 1 (by rfl) ⟨25467911, by rfl⟩ : syracuseStep 33957215 = 50935823) B50935823
theorem B22638143 : Blo 2093435 22638143 := bstep (se 1 (by rfl) ⟨16978607, by rfl⟩ : syracuseStep 22638143 = 33957215) B33957215
theorem B15092095 : Blo 2093435 15092095 := bstep (se 1 (by rfl) ⟨11319071, by rfl⟩ : syracuseStep 15092095 = 22638143) B22638143
theorem B20122793 : Blo 2093435 20122793 := bstep (se 2 (by rfl) ⟨7546047, by rfl⟩ : syracuseStep 20122793 = 15092095) B15092095
theorem B13415195 : Blo 2093435 13415195 := bstep (se 1 (by rfl) ⟨10061396, by rfl⟩ : syracuseStep 13415195 = 20122793) B20122793
theorem B8943463 : Blo 2093435 8943463 := bstep (se 1 (by rfl) ⟨6707597, by rfl⟩ : syracuseStep 8943463 = 13415195) B13415195
theorem B11924617 : Blo 2093435 11924617 := bstep (se 2 (by rfl) ⟨4471731, by rfl⟩ : syracuseStep 11924617 = 8943463) B8943463
theorem B15899489 : Blo 2093435 15899489 := bstep (se 2 (by rfl) ⟨5962308, by rfl⟩ : syracuseStep 15899489 = 11924617) B11924617
theorem B10599659 : Blo 2093435 10599659 := bstep (se 1 (by rfl) ⟨7949744, by rfl⟩ : syracuseStep 10599659 = 15899489) B15899489
theorem B7066439 : Blo 2093435 7066439 := bstep (se 1 (by rfl) ⟨5299829, by rfl⟩ : syracuseStep 7066439 = 10599659) B10599659
theorem B4710959 : Blo 2093435 4710959 := bstep (se 1 (by rfl) ⟨3533219, by rfl⟩ : syracuseStep 4710959 = 7066439) B7066439
theorem B3140639 : Blo 2093435 3140639 := bstep (se 1 (by rfl) ⟨2355479, by rfl⟩ : syracuseStep 3140639 = 4710959) B4710959
theorem B2093759 : Blo 2093435 2093759 := bstep (se 1 (by rfl) ⟨1570319, by rfl⟩ : syracuseStep 2093759 = 3140639) B3140639
theorem B3140645 : Blo 2093435 3140645 := bbase (se 4 (by rfl) ⟨294435, by rfl⟩ : syracuseStep 3140645 = 588871) (by norm_num)
theorem B2093763 : Blo 2093435 2093763 := bstep (se 1 (by rfl) ⟨1570322, by rfl⟩ : syracuseStep 2093763 = 3140645) B3140645
theorem B2649925 : Blo 2093435 2649925 := bbase (se 4 (by rfl) ⟨248430, by rfl⟩ : syracuseStep 2649925 = 496861) (by norm_num)
theorem B3533233 : Blo 2093435 3533233 := bstep (se 2 (by rfl) ⟨1324962, by rfl⟩ : syracuseStep 3533233 = 2649925) B2649925
theorem B4710977 : Blo 2093435 4710977 := bstep (se 2 (by rfl) ⟨1766616, by rfl⟩ : syracuseStep 4710977 = 3533233) B3533233
theorem B3140651 : Blo 2093435 3140651 := bstep (se 1 (by rfl) ⟨2355488, by rfl⟩ : syracuseStep 3140651 = 4710977) B4710977
theorem B2093767 : Blo 2093435 2093767 := bstep (se 1 (by rfl) ⟨1570325, by rfl⟩ : syracuseStep 2093767 = 3140651) B3140651
theorem B2355493 : Blo 2093435 2355493 := bbase (se 4 (by rfl) ⟨220827, by rfl⟩ : syracuseStep 2355493 = 441655) (by norm_num)
theorem B3140657 : Blo 2093435 3140657 := bstep (se 2 (by rfl) ⟨1177746, by rfl⟩ : syracuseStep 3140657 = 2355493) B2355493
theorem B2093771 : Blo 2093435 2093771 := bstep (se 1 (by rfl) ⟨1570328, by rfl⟩ : syracuseStep 2093771 = 3140657) B3140657
theorem B2515369 : Blo 2093435 2515369 := bbase (se 2 (by rfl) ⟨943263, by rfl⟩ : syracuseStep 2515369 = 1886527) (by norm_num)
theorem B3353825 : Blo 2093435 3353825 := bstep (se 2 (by rfl) ⟨1257684, by rfl⟩ : syracuseStep 3353825 = 2515369) B2515369
theorem B8943533 : Blo 2093435 8943533 := bstep (se 3 (by rfl) ⟨1676912, by rfl⟩ : syracuseStep 8943533 = 3353825) B3353825
theorem B5962355 : Blo 2093435 5962355 := bstep (se 1 (by rfl) ⟨4471766, by rfl⟩ : syracuseStep 5962355 = 8943533) B8943533
theorem B3974903 : Blo 2093435 3974903 := bstep (se 1 (by rfl) ⟨2981177, by rfl⟩ : syracuseStep 3974903 = 5962355) B5962355
theorem B2649935 : Blo 2093435 2649935 := bstep (se 1 (by rfl) ⟨1987451, by rfl⟩ : syracuseStep 2649935 = 3974903) B3974903
theorem B7066493 : Blo 2093435 7066493 := bstep (se 3 (by rfl) ⟨1324967, by rfl⟩ : syracuseStep 7066493 = 2649935) B2649935
theorem B4710995 : Blo 2093435 4710995 := bstep (se 1 (by rfl) ⟨3533246, by rfl⟩ : syracuseStep 4710995 = 7066493) B7066493
theorem B3140663 : Blo 2093435 3140663 := bstep (se 1 (by rfl) ⟨2355497, by rfl⟩ : syracuseStep 3140663 = 4710995) B4710995
theorem B2093775 : Blo 2093435 2093775 := bstep (se 1 (by rfl) ⟨1570331, by rfl⟩ : syracuseStep 2093775 = 3140663) B3140663
theorem B3140669 : Blo 2093435 3140669 := bbase (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) (by norm_num)
theorem B2093779 : Blo 2093435 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B4711013 : Blo 2093435 4711013 := bbase (se 4 (by rfl) ⟨441657, by rfl⟩ : syracuseStep 4711013 = 883315) (by norm_num)
theorem B3140675 : Blo 2093435 3140675 := bstep (se 1 (by rfl) ⟨2355506, by rfl⟩ : syracuseStep 3140675 = 4711013) B4711013
theorem B2093783 : Blo 2093435 2093783 := bstep (se 1 (by rfl) ⟨1570337, by rfl⟩ : syracuseStep 2093783 = 3140675) B3140675
theorem B5299901 : Blo 2093435 5299901 := bbase (se 3 (by rfl) ⟨993731, by rfl⟩ : syracuseStep 5299901 = 1987463) (by norm_num)
theorem B3533267 : Blo 2093435 3533267 := bstep (se 1 (by rfl) ⟨2649950, by rfl⟩ : syracuseStep 3533267 = 5299901) B5299901
theorem B2355511 : Blo 2093435 2355511 := bstep (se 1 (by rfl) ⟨1766633, by rfl⟩ : syracuseStep 2355511 = 3533267) B3533267
theorem B3140681 : Blo 2093435 3140681 := bstep (se 2 (by rfl) ⟨1177755, by rfl⟩ : syracuseStep 3140681 = 2355511) B2355511
theorem B2093787 : Blo 2093435 2093787 := bstep (se 1 (by rfl) ⟨1570340, by rfl⟩ : syracuseStep 2093787 = 3140681) B3140681
theorem B3974933 : Blo 2093435 3974933 := bbase (se 6 (by rfl) ⟨93162, by rfl⟩ : syracuseStep 3974933 = 186325) (by norm_num)
theorem B10599821 : Blo 2093435 10599821 := bstep (se 3 (by rfl) ⟨1987466, by rfl⟩ : syracuseStep 10599821 = 3974933) B3974933
theorem B7066547 : Blo 2093435 7066547 := bstep (se 1 (by rfl) ⟨5299910, by rfl⟩ : syracuseStep 7066547 = 10599821) B10599821
theorem B4711031 : Blo 2093435 4711031 := bstep (se 1 (by rfl) ⟨3533273, by rfl⟩ : syracuseStep 4711031 = 7066547) B7066547
theorem B3140687 : Blo 2093435 3140687 := bstep (se 1 (by rfl) ⟨2355515, by rfl⟩ : syracuseStep 3140687 = 4711031) B4711031
theorem B2093791 : Blo 2093435 2093791 := bstep (se 1 (by rfl) ⟨1570343, by rfl⟩ : syracuseStep 2093791 = 3140687) B3140687
theorem B3140693 : Blo 2093435 3140693 := bbase (se 8 (by rfl) ⟨18402, by rfl⟩ : syracuseStep 3140693 = 36805) (by norm_num)
theorem B2093795 : Blo 2093435 2093795 := bstep (se 1 (by rfl) ⟨1570346, by rfl⟩ : syracuseStep 2093795 = 3140693) B3140693
theorem B29439125 : Blo 2093435 29439125 := bbase (se 6 (by rfl) ⟨689979, by rfl⟩ : syracuseStep 29439125 = 1379959) (by norm_num)
theorem B19626083 : Blo 2093435 19626083 := bstep (se 1 (by rfl) ⟨14719562, by rfl⟩ : syracuseStep 19626083 = 29439125) B29439125
theorem B13084055 : Blo 2093435 13084055 := bstep (se 1 (by rfl) ⟨9813041, by rfl⟩ : syracuseStep 13084055 = 19626083) B19626083
theorem B8722703 : Blo 2093435 8722703 := bstep (se 1 (by rfl) ⟨6542027, by rfl⟩ : syracuseStep 8722703 = 13084055) B13084055
theorem B5815135 : Blo 2093435 5815135 := bstep (se 1 (by rfl) ⟨4361351, by rfl⟩ : syracuseStep 5815135 = 8722703) B8722703
theorem B31014053 : Blo 2093435 31014053 := bstep (se 4 (by rfl) ⟨2907567, by rfl⟩ : syracuseStep 31014053 = 5815135) B5815135
theorem B20676035 : Blo 2093435 20676035 := bstep (se 1 (by rfl) ⟨15507026, by rfl⟩ : syracuseStep 20676035 = 31014053) B31014053
theorem B13784023 : Blo 2093435 13784023 := bstep (se 1 (by rfl) ⟨10338017, by rfl⟩ : syracuseStep 13784023 = 20676035) B20676035
theorem B73514789 : Blo 2093435 73514789 := bstep (se 4 (by rfl) ⟨6892011, by rfl⟩ : syracuseStep 73514789 = 13784023) B13784023
theorem B49009859 : Blo 2093435 49009859 := bstep (se 1 (by rfl) ⟨36757394, by rfl⟩ : syracuseStep 49009859 = 73514789) B73514789
theorem B32673239 : Blo 2093435 32673239 := bstep (se 1 (by rfl) ⟨24504929, by rfl⟩ : syracuseStep 32673239 = 49009859) B49009859
theorem B21782159 : Blo 2093435 21782159 := bstep (se 1 (by rfl) ⟨16336619, by rfl⟩ : syracuseStep 21782159 = 32673239) B32673239
theorem B14521439 : Blo 2093435 14521439 := bstep (se 1 (by rfl) ⟨10891079, by rfl⟩ : syracuseStep 14521439 = 21782159) B21782159
theorem B9680959 : Blo 2093435 9680959 := bstep (se 1 (by rfl) ⟨7260719, by rfl⟩ : syracuseStep 9680959 = 14521439) B14521439
theorem B12907945 : Blo 2093435 12907945 := bstep (se 2 (by rfl) ⟨4840479, by rfl⟩ : syracuseStep 12907945 = 9680959) B9680959
theorem B17210593 : Blo 2093435 17210593 := bstep (se 2 (by rfl) ⟨6453972, by rfl⟩ : syracuseStep 17210593 = 12907945) B12907945
theorem B22947457 : Blo 2093435 22947457 := bstep (se 2 (by rfl) ⟨8605296, by rfl⟩ : syracuseStep 22947457 = 17210593) B17210593
theorem B30596609 : Blo 2093435 30596609 := bstep (se 2 (by rfl) ⟨11473728, by rfl⟩ : syracuseStep 30596609 = 22947457) B22947457
theorem B20397739 : Blo 2093435 20397739 := bstep (se 1 (by rfl) ⟨15298304, by rfl⟩ : syracuseStep 20397739 = 30596609) B30596609
theorem B27196985 : Blo 2093435 27196985 := bstep (se 2 (by rfl) ⟨10198869, by rfl⟩ : syracuseStep 27196985 = 20397739) B20397739
theorem B18131323 : Blo 2093435 18131323 := bstep (se 1 (by rfl) ⟨13598492, by rfl⟩ : syracuseStep 18131323 = 27196985) B27196985
theorem B24175097 : Blo 2093435 24175097 := bstep (se 2 (by rfl) ⟨9065661, by rfl⟩ : syracuseStep 24175097 = 18131323) B18131323
theorem B16116731 : Blo 2093435 16116731 := bstep (se 1 (by rfl) ⟨12087548, by rfl⟩ : syracuseStep 16116731 = 24175097) B24175097
theorem B10744487 : Blo 2093435 10744487 := bstep (se 1 (by rfl) ⟨8058365, by rfl⟩ : syracuseStep 10744487 = 16116731) B16116731
theorem B7162991 : Blo 2093435 7162991 := bstep (se 1 (by rfl) ⟨5372243, by rfl⟩ : syracuseStep 7162991 = 10744487) B10744487
theorem B4775327 : Blo 2093435 4775327 := bstep (se 1 (by rfl) ⟨3581495, by rfl⟩ : syracuseStep 4775327 = 7162991) B7162991
theorem B3183551 : Blo 2093435 3183551 := bstep (se 1 (by rfl) ⟨2387663, by rfl⟩ : syracuseStep 3183551 = 4775327) B4775327
theorem B2122367 : Blo 2093435 2122367 := bstep (se 1 (by rfl) ⟨1591775, by rfl⟩ : syracuseStep 2122367 = 3183551) B3183551
theorem B5659645 : Blo 2093435 5659645 := bstep (se 3 (by rfl) ⟨1061183, by rfl⟩ : syracuseStep 5659645 = 2122367) B2122367
theorem B7546193 : Blo 2093435 7546193 := bstep (se 2 (by rfl) ⟨2829822, by rfl⟩ : syracuseStep 7546193 = 5659645) B5659645
theorem B5030795 : Blo 2093435 5030795 := bstep (se 1 (by rfl) ⟨3773096, by rfl⟩ : syracuseStep 5030795 = 7546193) B7546193
theorem B13415453 : Blo 2093435 13415453 := bstep (se 3 (by rfl) ⟨2515397, by rfl⟩ : syracuseStep 13415453 = 5030795) B5030795
theorem B8943635 : Blo 2093435 8943635 := bstep (se 1 (by rfl) ⟨6707726, by rfl⟩ : syracuseStep 8943635 = 13415453) B13415453
theorem B5962423 : Blo 2093435 5962423 := bstep (se 1 (by rfl) ⟨4471817, by rfl⟩ : syracuseStep 5962423 = 8943635) B8943635
theorem B7949897 : Blo 2093435 7949897 := bstep (se 2 (by rfl) ⟨2981211, by rfl⟩ : syracuseStep 7949897 = 5962423) B5962423
theorem B5299931 : Blo 2093435 5299931 := bstep (se 1 (by rfl) ⟨3974948, by rfl⟩ : syracuseStep 5299931 = 7949897) B7949897
theorem B3533287 : Blo 2093435 3533287 := bstep (se 1 (by rfl) ⟨2649965, by rfl⟩ : syracuseStep 3533287 = 5299931) B5299931
theorem B4711049 : Blo 2093435 4711049 := bstep (se 2 (by rfl) ⟨1766643, by rfl⟩ : syracuseStep 4711049 = 3533287) B3533287
theorem B3140699 : Blo 2093435 3140699 := bstep (se 1 (by rfl) ⟨2355524, by rfl⟩ : syracuseStep 3140699 = 4711049) B4711049
theorem B2093799 : Blo 2093435 2093799 := bstep (se 1 (by rfl) ⟨1570349, by rfl⟩ : syracuseStep 2093799 = 3140699) B3140699
theorem B2355529 : Blo 2093435 2355529 := bbase (se 2 (by rfl) ⟨883323, by rfl⟩ : syracuseStep 2355529 = 1766647) (by norm_num)
theorem B3140705 : Blo 2093435 3140705 := bstep (se 2 (by rfl) ⟨1177764, by rfl⟩ : syracuseStep 3140705 = 2355529) B2355529
theorem B2093803 : Blo 2093435 2093803 := bstep (se 1 (by rfl) ⟨1570352, by rfl⟩ : syracuseStep 2093803 = 3140705) B3140705
theorem B16978997 : Blo 2093435 16978997 := bbase (se 5 (by rfl) ⟨795890, by rfl⟩ : syracuseStep 16978997 = 1591781) (by norm_num)
theorem B45277325 : Blo 2093435 45277325 := bstep (se 3 (by rfl) ⟨8489498, by rfl⟩ : syracuseStep 45277325 = 16978997) B16978997
theorem B30184883 : Blo 2093435 30184883 := bstep (se 1 (by rfl) ⟨22638662, by rfl⟩ : syracuseStep 30184883 = 45277325) B45277325
theorem B20123255 : Blo 2093435 20123255 := bstep (se 1 (by rfl) ⟨15092441, by rfl⟩ : syracuseStep 20123255 = 30184883) B30184883
theorem B13415503 : Blo 2093435 13415503 := bstep (se 1 (by rfl) ⟨10061627, by rfl⟩ : syracuseStep 13415503 = 20123255) B20123255
theorem B17887337 : Blo 2093435 17887337 := bstep (se 2 (by rfl) ⟨6707751, by rfl⟩ : syracuseStep 17887337 = 13415503) B13415503
theorem B11924891 : Blo 2093435 11924891 := bstep (se 1 (by rfl) ⟨8943668, by rfl⟩ : syracuseStep 11924891 = 17887337) B17887337
theorem B7949927 : Blo 2093435 7949927 := bstep (se 1 (by rfl) ⟨5962445, by rfl⟩ : syracuseStep 7949927 = 11924891) B11924891
theorem B5299951 : Blo 2093435 5299951 := bstep (se 1 (by rfl) ⟨3974963, by rfl⟩ : syracuseStep 5299951 = 7949927) B7949927
theorem B7066601 : Blo 2093435 7066601 := bstep (se 2 (by rfl) ⟨2649975, by rfl⟩ : syracuseStep 7066601 = 5299951) B5299951
theorem B4711067 : Blo 2093435 4711067 := bstep (se 1 (by rfl) ⟨3533300, by rfl⟩ : syracuseStep 4711067 = 7066601) B7066601
theorem B3140711 : Blo 2093435 3140711 := bstep (se 1 (by rfl) ⟨2355533, by rfl⟩ : syracuseStep 3140711 = 4711067) B4711067
theorem B2093807 : Blo 2093435 2093807 := bstep (se 1 (by rfl) ⟨1570355, by rfl⟩ : syracuseStep 2093807 = 3140711) B3140711
theorem B3140717 : Blo 2093435 3140717 := bbase (se 3 (by rfl) ⟨588884, by rfl⟩ : syracuseStep 3140717 = 1177769) (by norm_num)
theorem B2093811 : Blo 2093435 2093811 := bstep (se 1 (by rfl) ⟨1570358, by rfl⟩ : syracuseStep 2093811 = 3140717) B3140717
theorem B4711085 : Blo 2093435 4711085 := bbase (se 3 (by rfl) ⟨883328, by rfl⟩ : syracuseStep 4711085 = 1766657) (by norm_num)
theorem B3140723 : Blo 2093435 3140723 := bstep (se 1 (by rfl) ⟨2355542, by rfl⟩ : syracuseStep 3140723 = 4711085) B4711085
theorem B2093815 : Blo 2093435 2093815 := bstep (se 1 (by rfl) ⟨1570361, by rfl⟩ : syracuseStep 2093815 = 3140723) B3140723
theorem B4471861 : Blo 2093435 4471861 := bbase (se 5 (by rfl) ⟨209618, by rfl⟩ : syracuseStep 4471861 = 419237) (by norm_num)
theorem B5962481 : Blo 2093435 5962481 := bstep (se 2 (by rfl) ⟨2235930, by rfl⟩ : syracuseStep 5962481 = 4471861) B4471861
theorem B3974987 : Blo 2093435 3974987 := bstep (se 1 (by rfl) ⟨2981240, by rfl⟩ : syracuseStep 3974987 = 5962481) B5962481
theorem B2649991 : Blo 2093435 2649991 := bstep (se 1 (by rfl) ⟨1987493, by rfl⟩ : syracuseStep 2649991 = 3974987) B3974987
theorem B3533321 : Blo 2093435 3533321 := bstep (se 2 (by rfl) ⟨1324995, by rfl⟩ : syracuseStep 3533321 = 2649991) B2649991
theorem B2355547 : Blo 2093435 2355547 := bstep (se 1 (by rfl) ⟨1766660, by rfl⟩ : syracuseStep 2355547 = 3533321) B3533321
theorem B3140729 : Blo 2093435 3140729 := bstep (se 2 (by rfl) ⟨1177773, by rfl⟩ : syracuseStep 3140729 = 2355547) B2355547
theorem B2093819 : Blo 2093435 2093819 := bstep (se 1 (by rfl) ⟨1570364, by rfl⟩ : syracuseStep 2093819 = 3140729) B3140729
theorem B67916501 : Blo 2093435 67916501 := bbase (se 7 (by rfl) ⟨795896, by rfl⟩ : syracuseStep 67916501 = 1591793) (by norm_num)
theorem B45277667 : Blo 2093435 45277667 := bstep (se 1 (by rfl) ⟨33958250, by rfl⟩ : syracuseStep 45277667 = 67916501) B67916501
theorem B30185111 : Blo 2093435 30185111 := bstep (se 1 (by rfl) ⟨22638833, by rfl⟩ : syracuseStep 30185111 = 45277667) B45277667
theorem B20123407 : Blo 2093435 20123407 := bstep (se 1 (by rfl) ⟨15092555, by rfl⟩ : syracuseStep 20123407 = 30185111) B30185111
theorem B26831209 : Blo 2093435 26831209 := bstep (se 2 (by rfl) ⟨10061703, by rfl⟩ : syracuseStep 26831209 = 20123407) B20123407
theorem B35774945 : Blo 2093435 35774945 := bstep (se 2 (by rfl) ⟨13415604, by rfl⟩ : syracuseStep 35774945 = 26831209) B26831209
theorem B23849963 : Blo 2093435 23849963 := bstep (se 1 (by rfl) ⟨17887472, by rfl⟩ : syracuseStep 23849963 = 35774945) B35774945
theorem B15899975 : Blo 2093435 15899975 := bstep (se 1 (by rfl) ⟨11924981, by rfl⟩ : syracuseStep 15899975 = 23849963) B23849963
theorem B10599983 : Blo 2093435 10599983 := bstep (se 1 (by rfl) ⟨7949987, by rfl⟩ : syracuseStep 10599983 = 15899975) B15899975
theorem B7066655 : Blo 2093435 7066655 := bstep (se 1 (by rfl) ⟨5299991, by rfl⟩ : syracuseStep 7066655 = 10599983) B10599983
theorem B4711103 : Blo 2093435 4711103 := bstep (se 1 (by rfl) ⟨3533327, by rfl⟩ : syracuseStep 4711103 = 7066655) B7066655
theorem B3140735 : Blo 2093435 3140735 := bstep (se 1 (by rfl) ⟨2355551, by rfl⟩ : syracuseStep 3140735 = 4711103) B4711103
theorem B2093823 : Blo 2093435 2093823 := bstep (se 1 (by rfl) ⟨1570367, by rfl⟩ : syracuseStep 2093823 = 3140735) B3140735
theorem B3140741 : Blo 2093435 3140741 := bbase (se 4 (by rfl) ⟨294444, by rfl⟩ : syracuseStep 3140741 = 588889) (by norm_num)
theorem B2093827 : Blo 2093435 2093827 := bstep (se 1 (by rfl) ⟨1570370, by rfl⟩ : syracuseStep 2093827 = 3140741) B3140741
theorem B3533341 : Blo 2093435 3533341 := bbase (se 3 (by rfl) ⟨662501, by rfl⟩ : syracuseStep 3533341 = 1325003) (by norm_num)
theorem B4711121 : Blo 2093435 4711121 := bstep (se 2 (by rfl) ⟨1766670, by rfl⟩ : syracuseStep 4711121 = 3533341) B3533341
theorem B3140747 : Blo 2093435 3140747 := bstep (se 1 (by rfl) ⟨2355560, by rfl⟩ : syracuseStep 3140747 = 4711121) B4711121
theorem B2093831 : Blo 2093435 2093831 := bstep (se 1 (by rfl) ⟨1570373, by rfl⟩ : syracuseStep 2093831 = 3140747) B3140747
theorem B2355565 : Blo 2093435 2355565 := bbase (se 3 (by rfl) ⟨441668, by rfl⟩ : syracuseStep 2355565 = 883337) (by norm_num)
theorem B3140753 : Blo 2093435 3140753 := bstep (se 2 (by rfl) ⟨1177782, by rfl⟩ : syracuseStep 3140753 = 2355565) B2355565
theorem B2093835 : Blo 2093435 2093835 := bstep (se 1 (by rfl) ⟨1570376, by rfl⟩ : syracuseStep 2093835 = 3140753) B3140753
theorem B7066709 : Blo 2093435 7066709 := bbase (se 8 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 7066709 = 82813) (by norm_num)
theorem B4711139 : Blo 2093435 4711139 := bstep (se 1 (by rfl) ⟨3533354, by rfl⟩ : syracuseStep 4711139 = 7066709) B7066709
theorem B3140759 : Blo 2093435 3140759 := bstep (se 1 (by rfl) ⟨2355569, by rfl⟩ : syracuseStep 3140759 = 4711139) B4711139
theorem B2093839 : Blo 2093435 2093839 := bstep (se 1 (by rfl) ⟨1570379, by rfl⟩ : syracuseStep 2093839 = 3140759) B3140759
theorem B3140765 : Blo 2093435 3140765 := bbase (se 3 (by rfl) ⟨588893, by rfl⟩ : syracuseStep 3140765 = 1177787) (by norm_num)
theorem B2093843 : Blo 2093435 2093843 := bstep (se 1 (by rfl) ⟨1570382, by rfl⟩ : syracuseStep 2093843 = 3140765) B3140765
theorem B4711157 : Blo 2093435 4711157 := bbase (se 5 (by rfl) ⟨220835, by rfl⟩ : syracuseStep 4711157 = 441671) (by norm_num)
theorem B3140771 : Blo 2093435 3140771 := bstep (se 1 (by rfl) ⟨2355578, by rfl⟩ : syracuseStep 3140771 = 4711157) B4711157
theorem B2093847 : Blo 2093435 2093847 := bstep (se 1 (by rfl) ⟨1570385, by rfl⟩ : syracuseStep 2093847 = 3140771) B3140771
theorem B26831573 : Blo 2093435 26831573 := bbase (se 7 (by rfl) ⟨314432, by rfl⟩ : syracuseStep 26831573 = 628865) (by norm_num)
theorem B17887715 : Blo 2093435 17887715 := bstep (se 1 (by rfl) ⟨13415786, by rfl⟩ : syracuseStep 17887715 = 26831573) B26831573
theorem B11925143 : Blo 2093435 11925143 := bstep (se 1 (by rfl) ⟨8943857, by rfl⟩ : syracuseStep 11925143 = 17887715) B17887715
theorem B7950095 : Blo 2093435 7950095 := bstep (se 1 (by rfl) ⟨5962571, by rfl⟩ : syracuseStep 7950095 = 11925143) B11925143
theorem B5300063 : Blo 2093435 5300063 := bstep (se 1 (by rfl) ⟨3975047, by rfl⟩ : syracuseStep 5300063 = 7950095) B7950095
theorem B3533375 : Blo 2093435 3533375 := bstep (se 1 (by rfl) ⟨2650031, by rfl⟩ : syracuseStep 3533375 = 5300063) B5300063
theorem B2355583 : Blo 2093435 2355583 := bstep (se 1 (by rfl) ⟨1766687, by rfl⟩ : syracuseStep 2355583 = 3533375) B3533375
theorem B3140777 : Blo 2093435 3140777 := bstep (se 2 (by rfl) ⟨1177791, by rfl⟩ : syracuseStep 3140777 = 2355583) B2355583
theorem B2093851 : Blo 2093435 2093851 := bstep (se 1 (by rfl) ⟨1570388, by rfl⟩ : syracuseStep 2093851 = 3140777) B3140777
theorem B2515465 : Blo 2093435 2515465 := bbase (se 2 (by rfl) ⟨943299, by rfl⟩ : syracuseStep 2515465 = 1886599) (by norm_num)
theorem B3353953 : Blo 2093435 3353953 := bstep (se 2 (by rfl) ⟨1257732, by rfl⟩ : syracuseStep 3353953 = 2515465) B2515465
theorem B4471937 : Blo 2093435 4471937 := bstep (se 2 (by rfl) ⟨1676976, by rfl⟩ : syracuseStep 4471937 = 3353953) B3353953
theorem B2981291 : Blo 2093435 2981291 := bstep (se 1 (by rfl) ⟨2235968, by rfl⟩ : syracuseStep 2981291 = 4471937) B4471937
theorem B7950109 : Blo 2093435 7950109 := bstep (se 3 (by rfl) ⟨1490645, by rfl⟩ : syracuseStep 7950109 = 2981291) B2981291
theorem B10600145 : Blo 2093435 10600145 := bstep (se 2 (by rfl) ⟨3975054, by rfl⟩ : syracuseStep 10600145 = 7950109) B7950109
theorem B7066763 : Blo 2093435 7066763 := bstep (se 1 (by rfl) ⟨5300072, by rfl⟩ : syracuseStep 7066763 = 10600145) B10600145
theorem B4711175 : Blo 2093435 4711175 := bstep (se 1 (by rfl) ⟨3533381, by rfl⟩ : syracuseStep 4711175 = 7066763) B7066763
theorem B3140783 : Blo 2093435 3140783 := bstep (se 1 (by rfl) ⟨2355587, by rfl⟩ : syracuseStep 3140783 = 4711175) B4711175
theorem B2093855 : Blo 2093435 2093855 := bstep (se 1 (by rfl) ⟨1570391, by rfl⟩ : syracuseStep 2093855 = 3140783) B3140783
theorem B3140789 : Blo 2093435 3140789 := bbase (se 5 (by rfl) ⟨147224, by rfl⟩ : syracuseStep 3140789 = 294449) (by norm_num)
theorem B2093859 : Blo 2093435 2093859 := bstep (se 1 (by rfl) ⟨1570394, by rfl⟩ : syracuseStep 2093859 = 3140789) B3140789
theorem B5300093 : Blo 2093435 5300093 := bbase (se 3 (by rfl) ⟨993767, by rfl⟩ : syracuseStep 5300093 = 1987535) (by norm_num)
theorem B3533395 : Blo 2093435 3533395 := bstep (se 1 (by rfl) ⟨2650046, by rfl⟩ : syracuseStep 3533395 = 5300093) B5300093
theorem B4711193 : Blo 2093435 4711193 := bstep (se 2 (by rfl) ⟨1766697, by rfl⟩ : syracuseStep 4711193 = 3533395) B3533395
theorem B3140795 : Blo 2093435 3140795 := bstep (se 1 (by rfl) ⟨2355596, by rfl⟩ : syracuseStep 3140795 = 4711193) B4711193
theorem B2093863 : Blo 2093435 2093863 := bstep (se 1 (by rfl) ⟨1570397, by rfl⟩ : syracuseStep 2093863 = 3140795) B3140795
theorem B2355601 : Blo 2093435 2355601 := bbase (se 2 (by rfl) ⟨883350, by rfl⟩ : syracuseStep 2355601 = 1766701) (by norm_num)
theorem B3140801 : Blo 2093435 3140801 := bstep (se 2 (by rfl) ⟨1177800, by rfl⟩ : syracuseStep 3140801 = 2355601) B2355601
theorem B2093867 : Blo 2093435 2093867 := bstep (se 1 (by rfl) ⟨1570400, by rfl⟩ : syracuseStep 2093867 = 3140801) B3140801
theorem B3975085 : Blo 2093435 3975085 := bbase (se 3 (by rfl) ⟨745328, by rfl⟩ : syracuseStep 3975085 = 1490657) (by norm_num)
theorem B5300113 : Blo 2093435 5300113 := bstep (se 2 (by rfl) ⟨1987542, by rfl⟩ : syracuseStep 5300113 = 3975085) B3975085
theorem B7066817 : Blo 2093435 7066817 := bstep (se 2 (by rfl) ⟨2650056, by rfl⟩ : syracuseStep 7066817 = 5300113) B5300113
theorem B4711211 : Blo 2093435 4711211 := bstep (se 1 (by rfl) ⟨3533408, by rfl⟩ : syracuseStep 4711211 = 7066817) B7066817
theorem B3140807 : Blo 2093435 3140807 := bstep (se 1 (by rfl) ⟨2355605, by rfl⟩ : syracuseStep 3140807 = 4711211) B4711211
theorem B2093871 : Blo 2093435 2093871 := bstep (se 1 (by rfl) ⟨1570403, by rfl⟩ : syracuseStep 2093871 = 3140807) B3140807
theorem B3140813 : Blo 2093435 3140813 := bbase (se 3 (by rfl) ⟨588902, by rfl⟩ : syracuseStep 3140813 = 1177805) (by norm_num)
theorem B2093875 : Blo 2093435 2093875 := bstep (se 1 (by rfl) ⟨1570406, by rfl⟩ : syracuseStep 2093875 = 3140813) B3140813
theorem B4711229 : Blo 2093435 4711229 := bbase (se 3 (by rfl) ⟨883355, by rfl⟩ : syracuseStep 4711229 = 1766711) (by norm_num)
theorem B3140819 : Blo 2093435 3140819 := bstep (se 1 (by rfl) ⟨2355614, by rfl⟩ : syracuseStep 3140819 = 4711229) B4711229
theorem B2093879 : Blo 2093435 2093879 := bstep (se 1 (by rfl) ⟨1570409, by rfl⟩ : syracuseStep 2093879 = 3140819) B3140819
theorem B3533429 : Blo 2093435 3533429 := bbase (se 5 (by rfl) ⟨165629, by rfl⟩ : syracuseStep 3533429 = 331259) (by norm_num)
theorem B2355619 : Blo 2093435 2355619 := bstep (se 1 (by rfl) ⟨1766714, by rfl⟩ : syracuseStep 2355619 = 3533429) B3533429
theorem B3140825 : Blo 2093435 3140825 := bstep (se 2 (by rfl) ⟨1177809, by rfl⟩ : syracuseStep 3140825 = 2355619) B2355619
theorem B2093883 : Blo 2093435 2093883 := bstep (se 1 (by rfl) ⟨1570412, by rfl⟩ : syracuseStep 2093883 = 3140825) B3140825
theorem B4472005 : Blo 2093435 4472005 := bbase (se 4 (by rfl) ⟨419250, by rfl⟩ : syracuseStep 4472005 = 838501) (by norm_num)
theorem B5962673 : Blo 2093435 5962673 := bstep (se 2 (by rfl) ⟨2236002, by rfl⟩ : syracuseStep 5962673 = 4472005) B4472005
theorem B15900461 : Blo 2093435 15900461 := bstep (se 3 (by rfl) ⟨2981336, by rfl⟩ : syracuseStep 15900461 = 5962673) B5962673
theorem B10600307 : Blo 2093435 10600307 := bstep (se 1 (by rfl) ⟨7950230, by rfl⟩ : syracuseStep 10600307 = 15900461) B15900461
theorem B7066871 : Blo 2093435 7066871 := bstep (se 1 (by rfl) ⟨5300153, by rfl⟩ : syracuseStep 7066871 = 10600307) B10600307
theorem B4711247 : Blo 2093435 4711247 := bstep (se 1 (by rfl) ⟨3533435, by rfl⟩ : syracuseStep 4711247 = 7066871) B7066871
theorem B3140831 : Blo 2093435 3140831 := bstep (se 1 (by rfl) ⟨2355623, by rfl⟩ : syracuseStep 3140831 = 4711247) B4711247
theorem B2093887 : Blo 2093435 2093887 := bstep (se 1 (by rfl) ⟨1570415, by rfl⟩ : syracuseStep 2093887 = 3140831) B3140831
theorem B3140837 : Blo 2093435 3140837 := bbase (se 4 (by rfl) ⟨294453, by rfl⟩ : syracuseStep 3140837 = 588907) (by norm_num)
theorem B2093891 : Blo 2093435 2093891 := bstep (se 1 (by rfl) ⟨1570418, by rfl⟩ : syracuseStep 2093891 = 3140837) B3140837
theorem B10062053 : Blo 2093435 10062053 := bbase (se 4 (by rfl) ⟨943317, by rfl⟩ : syracuseStep 10062053 = 1886635) (by norm_num)
theorem B6708035 : Blo 2093435 6708035 := bstep (se 1 (by rfl) ⟨5031026, by rfl⟩ : syracuseStep 6708035 = 10062053) B10062053
theorem B4472023 : Blo 2093435 4472023 := bstep (se 1 (by rfl) ⟨3354017, by rfl⟩ : syracuseStep 4472023 = 6708035) B6708035
theorem B5962697 : Blo 2093435 5962697 := bstep (se 2 (by rfl) ⟨2236011, by rfl⟩ : syracuseStep 5962697 = 4472023) B4472023
theorem B3975131 : Blo 2093435 3975131 := bstep (se 1 (by rfl) ⟨2981348, by rfl⟩ : syracuseStep 3975131 = 5962697) B5962697
theorem B2650087 : Blo 2093435 2650087 := bstep (se 1 (by rfl) ⟨1987565, by rfl⟩ : syracuseStep 2650087 = 3975131) B3975131
theorem B3533449 : Blo 2093435 3533449 := bstep (se 2 (by rfl) ⟨1325043, by rfl⟩ : syracuseStep 3533449 = 2650087) B2650087
theorem B4711265 : Blo 2093435 4711265 := bstep (se 2 (by rfl) ⟨1766724, by rfl⟩ : syracuseStep 4711265 = 3533449) B3533449
theorem B3140843 : Blo 2093435 3140843 := bstep (se 1 (by rfl) ⟨2355632, by rfl⟩ : syracuseStep 3140843 = 4711265) B4711265
theorem B2093895 : Blo 2093435 2093895 := bstep (se 1 (by rfl) ⟨1570421, by rfl⟩ : syracuseStep 2093895 = 3140843) B3140843
theorem B2355637 : Blo 2093435 2355637 := bbase (se 5 (by rfl) ⟨110420, by rfl⟩ : syracuseStep 2355637 = 220841) (by norm_num)
theorem B3140849 : Blo 2093435 3140849 := bstep (se 2 (by rfl) ⟨1177818, by rfl⟩ : syracuseStep 3140849 = 2355637) B2355637
theorem B2093899 : Blo 2093435 2093899 := bstep (se 1 (by rfl) ⟨1570424, by rfl⟩ : syracuseStep 2093899 = 3140849) B3140849
theorem B2650097 : Blo 2093435 2650097 := bbase (se 2 (by rfl) ⟨993786, by rfl⟩ : syracuseStep 2650097 = 1987573) (by norm_num)
theorem B7066925 : Blo 2093435 7066925 := bstep (se 3 (by rfl) ⟨1325048, by rfl⟩ : syracuseStep 7066925 = 2650097) B2650097
theorem B4711283 : Blo 2093435 4711283 := bstep (se 1 (by rfl) ⟨3533462, by rfl⟩ : syracuseStep 4711283 = 7066925) B7066925
theorem B3140855 : Blo 2093435 3140855 := bstep (se 1 (by rfl) ⟨2355641, by rfl⟩ : syracuseStep 3140855 = 4711283) B4711283
theorem B2093903 : Blo 2093435 2093903 := bstep (se 1 (by rfl) ⟨1570427, by rfl⟩ : syracuseStep 2093903 = 3140855) B3140855
theorem B3140861 : Blo 2093435 3140861 := bbase (se 3 (by rfl) ⟨588911, by rfl⟩ : syracuseStep 3140861 = 1177823) (by norm_num)
theorem B2093907 : Blo 2093435 2093907 := bstep (se 1 (by rfl) ⟨1570430, by rfl⟩ : syracuseStep 2093907 = 3140861) B3140861
theorem B4711301 : Blo 2093435 4711301 := bbase (se 4 (by rfl) ⟨441684, by rfl⟩ : syracuseStep 4711301 = 883369) (by norm_num)
theorem B3140867 : Blo 2093435 3140867 := bstep (se 1 (by rfl) ⟨2355650, by rfl⟩ : syracuseStep 3140867 = 4711301) B4711301
theorem B2093911 : Blo 2093435 2093911 := bstep (se 1 (by rfl) ⟨1570433, by rfl⟩ : syracuseStep 2093911 = 3140867) B3140867
theorem B2236033 : Blo 2093435 2236033 := bbase (se 2 (by rfl) ⟨838512, by rfl⟩ : syracuseStep 2236033 = 1677025) (by norm_num)
theorem B2981377 : Blo 2093435 2981377 := bstep (se 2 (by rfl) ⟨1118016, by rfl⟩ : syracuseStep 2981377 = 2236033) B2236033
theorem B3975169 : Blo 2093435 3975169 := bstep (se 2 (by rfl) ⟨1490688, by rfl⟩ : syracuseStep 3975169 = 2981377) B2981377
theorem B5300225 : Blo 2093435 5300225 := bstep (se 2 (by rfl) ⟨1987584, by rfl⟩ : syracuseStep 5300225 = 3975169) B3975169
theorem B3533483 : Blo 2093435 3533483 := bstep (se 1 (by rfl) ⟨2650112, by rfl⟩ : syracuseStep 3533483 = 5300225) B5300225
theorem B2355655 : Blo 2093435 2355655 := bstep (se 1 (by rfl) ⟨1766741, by rfl⟩ : syracuseStep 2355655 = 3533483) B3533483
theorem B3140873 : Blo 2093435 3140873 := bstep (se 2 (by rfl) ⟨1177827, by rfl⟩ : syracuseStep 3140873 = 2355655) B2355655
theorem B2093915 : Blo 2093435 2093915 := bstep (se 1 (by rfl) ⟨1570436, by rfl⟩ : syracuseStep 2093915 = 3140873) B3140873
theorem B10600469 : Blo 2093435 10600469 := bbase (se 6 (by rfl) ⟨248448, by rfl⟩ : syracuseStep 10600469 = 496897) (by norm_num)
theorem B7066979 : Blo 2093435 7066979 := bstep (se 1 (by rfl) ⟨5300234, by rfl⟩ : syracuseStep 7066979 = 10600469) B10600469
theorem B4711319 : Blo 2093435 4711319 := bstep (se 1 (by rfl) ⟨3533489, by rfl⟩ : syracuseStep 4711319 = 7066979) B7066979
theorem B3140879 : Blo 2093435 3140879 := bstep (se 1 (by rfl) ⟨2355659, by rfl⟩ : syracuseStep 3140879 = 4711319) B4711319
theorem B2093919 : Blo 2093435 2093919 := bstep (se 1 (by rfl) ⟨1570439, by rfl⟩ : syracuseStep 2093919 = 3140879) B3140879
theorem B3140885 : Blo 2093435 3140885 := bbase (se 6 (by rfl) ⟨73614, by rfl⟩ : syracuseStep 3140885 = 147229) (by norm_num)
theorem B2093923 : Blo 2093435 2093923 := bstep (se 1 (by rfl) ⟨1570442, by rfl⟩ : syracuseStep 2093923 = 3140885) B3140885
theorem B2686285 : Blo 2093435 2686285 := bbase (se 3 (by rfl) ⟨503678, by rfl⟩ : syracuseStep 2686285 = 1007357) (by norm_num)
theorem B3581713 : Blo 2093435 3581713 := bstep (se 2 (by rfl) ⟨1343142, by rfl⟩ : syracuseStep 3581713 = 2686285) B2686285
theorem B4775617 : Blo 2093435 4775617 := bstep (se 2 (by rfl) ⟨1790856, by rfl⟩ : syracuseStep 4775617 = 3581713) B3581713
theorem B25469957 : Blo 2093435 25469957 := bstep (se 4 (by rfl) ⟨2387808, by rfl⟩ : syracuseStep 25469957 = 4775617) B4775617
theorem B16979971 : Blo 2093435 16979971 := bstep (se 1 (by rfl) ⟨12734978, by rfl⟩ : syracuseStep 16979971 = 25469957) B25469957
theorem B22639961 : Blo 2093435 22639961 := bstep (se 2 (by rfl) ⟨8489985, by rfl⟩ : syracuseStep 22639961 = 16979971) B16979971
theorem B15093307 : Blo 2093435 15093307 := bstep (se 1 (by rfl) ⟨11319980, by rfl⟩ : syracuseStep 15093307 = 22639961) B22639961
theorem B20124409 : Blo 2093435 20124409 := bstep (se 2 (by rfl) ⟨7546653, by rfl⟩ : syracuseStep 20124409 = 15093307) B15093307
theorem B26832545 : Blo 2093435 26832545 := bstep (se 2 (by rfl) ⟨10062204, by rfl⟩ : syracuseStep 26832545 = 20124409) B20124409
theorem B17888363 : Blo 2093435 17888363 := bstep (se 1 (by rfl) ⟨13416272, by rfl⟩ : syracuseStep 17888363 = 26832545) B26832545
theorem B11925575 : Blo 2093435 11925575 := bstep (se 1 (by rfl) ⟨8944181, by rfl⟩ : syracuseStep 11925575 = 17888363) B17888363
theorem B7950383 : Blo 2093435 7950383 := bstep (se 1 (by rfl) ⟨5962787, by rfl⟩ : syracuseStep 7950383 = 11925575) B11925575
theorem B5300255 : Blo 2093435 5300255 := bstep (se 1 (by rfl) ⟨3975191, by rfl⟩ : syracuseStep 5300255 = 7950383) B7950383
theorem B3533503 : Blo 2093435 3533503 := bstep (se 1 (by rfl) ⟨2650127, by rfl⟩ : syracuseStep 3533503 = 5300255) B5300255
theorem B4711337 : Blo 2093435 4711337 := bstep (se 2 (by rfl) ⟨1766751, by rfl⟩ : syracuseStep 4711337 = 3533503) B3533503
theorem B3140891 : Blo 2093435 3140891 := bstep (se 1 (by rfl) ⟨2355668, by rfl⟩ : syracuseStep 3140891 = 4711337) B4711337
theorem B2093927 : Blo 2093435 2093927 := bstep (se 1 (by rfl) ⟨1570445, by rfl⟩ : syracuseStep 2093927 = 3140891) B3140891
theorem B2355673 : Blo 2093435 2355673 := bbase (se 2 (by rfl) ⟨883377, by rfl⟩ : syracuseStep 2355673 = 1766755) (by norm_num)
theorem B3140897 : Blo 2093435 3140897 := bstep (se 2 (by rfl) ⟨1177836, by rfl⟩ : syracuseStep 3140897 = 2355673) B2355673
theorem B2093931 : Blo 2093435 2093931 := bstep (se 1 (by rfl) ⟨1570448, by rfl⟩ : syracuseStep 2093931 = 3140897) B3140897
theorem B2981405 : Blo 2093435 2981405 := bbase (se 3 (by rfl) ⟨559013, by rfl⟩ : syracuseStep 2981405 = 1118027) (by norm_num)
theorem B7950413 : Blo 2093435 7950413 := bstep (se 3 (by rfl) ⟨1490702, by rfl⟩ : syracuseStep 7950413 = 2981405) B2981405
theorem B5300275 : Blo 2093435 5300275 := bstep (se 1 (by rfl) ⟨3975206, by rfl⟩ : syracuseStep 5300275 = 7950413) B7950413
theorem B7067033 : Blo 2093435 7067033 := bstep (se 2 (by rfl) ⟨2650137, by rfl⟩ : syracuseStep 7067033 = 5300275) B5300275
theorem B4711355 : Blo 2093435 4711355 := bstep (se 1 (by rfl) ⟨3533516, by rfl⟩ : syracuseStep 4711355 = 7067033) B7067033
theorem B3140903 : Blo 2093435 3140903 := bstep (se 1 (by rfl) ⟨2355677, by rfl⟩ : syracuseStep 3140903 = 4711355) B4711355
theorem B2093935 : Blo 2093435 2093935 := bstep (se 1 (by rfl) ⟨1570451, by rfl⟩ : syracuseStep 2093935 = 3140903) B3140903
theorem B3140909 : Blo 2093435 3140909 := bbase (se 3 (by rfl) ⟨588920, by rfl⟩ : syracuseStep 3140909 = 1177841) (by norm_num)
theorem B2093939 : Blo 2093435 2093939 := bstep (se 1 (by rfl) ⟨1570454, by rfl⟩ : syracuseStep 2093939 = 3140909) B3140909
theorem B4711373 : Blo 2093435 4711373 := bbase (se 3 (by rfl) ⟨883382, by rfl⟩ : syracuseStep 4711373 = 1766765) (by norm_num)
theorem B3140915 : Blo 2093435 3140915 := bstep (se 1 (by rfl) ⟨2355686, by rfl⟩ : syracuseStep 3140915 = 4711373) B4711373
theorem B2093943 : Blo 2093435 2093943 := bstep (se 1 (by rfl) ⟨1570457, by rfl⟩ : syracuseStep 2093943 = 3140915) B3140915
theorem B2650153 : Blo 2093435 2650153 := bbase (se 2 (by rfl) ⟨993807, by rfl⟩ : syracuseStep 2650153 = 1987615) (by norm_num)
theorem B3533537 : Blo 2093435 3533537 := bstep (se 2 (by rfl) ⟨1325076, by rfl⟩ : syracuseStep 3533537 = 2650153) B2650153
theorem B2355691 : Blo 2093435 2355691 := bstep (se 1 (by rfl) ⟨1766768, by rfl⟩ : syracuseStep 2355691 = 3533537) B3533537
theorem B3140921 : Blo 2093435 3140921 := bstep (se 2 (by rfl) ⟨1177845, by rfl⟩ : syracuseStep 3140921 = 2355691) B2355691
theorem B2093947 : Blo 2093435 2093947 := bstep (se 1 (by rfl) ⟨1570460, by rfl⟩ : syracuseStep 2093947 = 3140921) B3140921
theorem B4533157 : Blo 2093435 4533157 := bbase (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) (by norm_num)
theorem B24176837 : Blo 2093435 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B64471565 : Blo 2093435 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B42981043 : Blo 2093435 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B57308057 : Blo 2093435 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B38205371 : Blo 2093435 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B25470247 : Blo 2093435 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B33960329 : Blo 2093435 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B22640219 : Blo 2093435 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B15093479 : Blo 2093435 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B10062319 : Blo 2093435 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B13416425 : Blo 2093435 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B8944283 : Blo 2093435 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B23851421 : Blo 2093435 23851421 := bstep (se 3 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 23851421 = 8944283) B8944283
theorem B15900947 : Blo 2093435 15900947 := bstep (se 1 (by rfl) ⟨11925710, by rfl⟩ : syracuseStep 15900947 = 23851421) B23851421
theorem B10600631 : Blo 2093435 10600631 := bstep (se 1 (by rfl) ⟨7950473, by rfl⟩ : syracuseStep 10600631 = 15900947) B15900947
theorem B7067087 : Blo 2093435 7067087 := bstep (se 1 (by rfl) ⟨5300315, by rfl⟩ : syracuseStep 7067087 = 10600631) B10600631
theorem B4711391 : Blo 2093435 4711391 := bstep (se 1 (by rfl) ⟨3533543, by rfl⟩ : syracuseStep 4711391 = 7067087) B7067087
theorem B3140927 : Blo 2093435 3140927 := bstep (se 1 (by rfl) ⟨2355695, by rfl⟩ : syracuseStep 3140927 = 4711391) B4711391
theorem B2093951 : Blo 2093435 2093951 := bstep (se 1 (by rfl) ⟨1570463, by rfl⟩ : syracuseStep 2093951 = 3140927) B3140927
theorem B3140933 : Blo 2093435 3140933 := bbase (se 4 (by rfl) ⟨294462, by rfl⟩ : syracuseStep 3140933 = 588925) (by norm_num)
theorem B2093955 : Blo 2093435 2093955 := bstep (se 1 (by rfl) ⟨1570466, by rfl⟩ : syracuseStep 2093955 = 3140933) B3140933
theorem B3533557 : Blo 2093435 3533557 := bbase (se 5 (by rfl) ⟨165635, by rfl⟩ : syracuseStep 3533557 = 331271) (by norm_num)
theorem B4711409 : Blo 2093435 4711409 := bstep (se 2 (by rfl) ⟨1766778, by rfl⟩ : syracuseStep 4711409 = 3533557) B3533557
theorem B3140939 : Blo 2093435 3140939 := bstep (se 1 (by rfl) ⟨2355704, by rfl⟩ : syracuseStep 3140939 = 4711409) B4711409
theorem B2093959 : Blo 2093435 2093959 := bstep (se 1 (by rfl) ⟨1570469, by rfl⟩ : syracuseStep 2093959 = 3140939) B3140939
theorem B2355709 : Blo 2093435 2355709 := bbase (se 3 (by rfl) ⟨441695, by rfl⟩ : syracuseStep 2355709 = 883391) (by norm_num)
theorem B3140945 : Blo 2093435 3140945 := bstep (se 2 (by rfl) ⟨1177854, by rfl⟩ : syracuseStep 3140945 = 2355709) B2355709
theorem B2093963 : Blo 2093435 2093963 := bstep (se 1 (by rfl) ⟨1570472, by rfl⟩ : syracuseStep 2093963 = 3140945) B3140945
theorem B7067141 : Blo 2093435 7067141 := bbase (se 4 (by rfl) ⟨662544, by rfl⟩ : syracuseStep 7067141 = 1325089) (by norm_num)
theorem B4711427 : Blo 2093435 4711427 := bstep (se 1 (by rfl) ⟨3533570, by rfl⟩ : syracuseStep 4711427 = 7067141) B7067141
theorem B3140951 : Blo 2093435 3140951 := bstep (se 1 (by rfl) ⟨2355713, by rfl⟩ : syracuseStep 3140951 = 4711427) B4711427
theorem B2093967 : Blo 2093435 2093967 := bstep (se 1 (by rfl) ⟨1570475, by rfl⟩ : syracuseStep 2093967 = 3140951) B3140951
theorem B3140957 : Blo 2093435 3140957 := bbase (se 3 (by rfl) ⟨588929, by rfl⟩ : syracuseStep 3140957 = 1177859) (by norm_num)
theorem B2093971 : Blo 2093435 2093971 := bstep (se 1 (by rfl) ⟨1570478, by rfl⟩ : syracuseStep 2093971 = 3140957) B3140957
theorem B4711445 : Blo 2093435 4711445 := bbase (se 6 (by rfl) ⟨110424, by rfl⟩ : syracuseStep 4711445 = 220849) (by norm_num)
theorem B3140963 : Blo 2093435 3140963 := bstep (se 1 (by rfl) ⟨2355722, by rfl⟩ : syracuseStep 3140963 = 4711445) B4711445
theorem B2093975 : Blo 2093435 2093975 := bstep (se 1 (by rfl) ⟨1570481, by rfl⟩ : syracuseStep 2093975 = 3140963) B3140963
theorem B7950581 : Blo 2093435 7950581 := bbase (se 5 (by rfl) ⟨372683, by rfl⟩ : syracuseStep 7950581 = 745367) (by norm_num)
theorem B5300387 : Blo 2093435 5300387 := bstep (se 1 (by rfl) ⟨3975290, by rfl⟩ : syracuseStep 5300387 = 7950581) B7950581
theorem B3533591 : Blo 2093435 3533591 := bstep (se 1 (by rfl) ⟨2650193, by rfl⟩ : syracuseStep 3533591 = 5300387) B5300387
theorem B2355727 : Blo 2093435 2355727 := bstep (se 1 (by rfl) ⟨1766795, by rfl⟩ : syracuseStep 2355727 = 3533591) B3533591
theorem B3140969 : Blo 2093435 3140969 := bstep (se 2 (by rfl) ⟨1177863, by rfl⟩ : syracuseStep 3140969 = 2355727) B2355727
theorem B2093979 : Blo 2093435 2093979 := bstep (se 1 (by rfl) ⟨1570484, by rfl⟩ : syracuseStep 2093979 = 3140969) B3140969
theorem B2236105 : Blo 2093435 2236105 := bbase (se 2 (by rfl) ⟨838539, by rfl⟩ : syracuseStep 2236105 = 1677079) (by norm_num)
theorem B11925893 : Blo 2093435 11925893 := bstep (se 4 (by rfl) ⟨1118052, by rfl⟩ : syracuseStep 11925893 = 2236105) B2236105
theorem B7950595 : Blo 2093435 7950595 := bstep (se 1 (by rfl) ⟨5962946, by rfl⟩ : syracuseStep 7950595 = 11925893) B11925893
theorem B10600793 : Blo 2093435 10600793 := bstep (se 2 (by rfl) ⟨3975297, by rfl⟩ : syracuseStep 10600793 = 7950595) B7950595
theorem B7067195 : Blo 2093435 7067195 := bstep (se 1 (by rfl) ⟨5300396, by rfl⟩ : syracuseStep 7067195 = 10600793) B10600793
theorem B4711463 : Blo 2093435 4711463 := bstep (se 1 (by rfl) ⟨3533597, by rfl⟩ : syracuseStep 4711463 = 7067195) B7067195
theorem B3140975 : Blo 2093435 3140975 := bstep (se 1 (by rfl) ⟨2355731, by rfl⟩ : syracuseStep 3140975 = 4711463) B4711463
theorem B2093983 : Blo 2093435 2093983 := bstep (se 1 (by rfl) ⟨1570487, by rfl⟩ : syracuseStep 2093983 = 3140975) B3140975
theorem B3140981 : Blo 2093435 3140981 := bbase (se 5 (by rfl) ⟨147233, by rfl⟩ : syracuseStep 3140981 = 294467) (by norm_num)
theorem B2093987 : Blo 2093435 2093987 := bstep (se 1 (by rfl) ⟨1570490, by rfl⟩ : syracuseStep 2093987 = 3140981) B3140981
theorem B2981485 : Blo 2093435 2981485 := bbase (se 3 (by rfl) ⟨559028, by rfl⟩ : syracuseStep 2981485 = 1118057) (by norm_num)
theorem B3975313 : Blo 2093435 3975313 := bstep (se 2 (by rfl) ⟨1490742, by rfl⟩ : syracuseStep 3975313 = 2981485) B2981485
theorem B5300417 : Blo 2093435 5300417 := bstep (se 2 (by rfl) ⟨1987656, by rfl⟩ : syracuseStep 5300417 = 3975313) B3975313
theorem B3533611 : Blo 2093435 3533611 := bstep (se 1 (by rfl) ⟨2650208, by rfl⟩ : syracuseStep 3533611 = 5300417) B5300417
theorem B4711481 : Blo 2093435 4711481 := bstep (se 2 (by rfl) ⟨1766805, by rfl⟩ : syracuseStep 4711481 = 3533611) B3533611
theorem B3140987 : Blo 2093435 3140987 := bstep (se 1 (by rfl) ⟨2355740, by rfl⟩ : syracuseStep 3140987 = 4711481) B4711481
theorem B2093991 : Blo 2093435 2093991 := bstep (se 1 (by rfl) ⟨1570493, by rfl⟩ : syracuseStep 2093991 = 3140987) B3140987
theorem B2355745 : Blo 2093435 2355745 := bbase (se 2 (by rfl) ⟨883404, by rfl⟩ : syracuseStep 2355745 = 1766809) (by norm_num)
theorem B3140993 : Blo 2093435 3140993 := bstep (se 2 (by rfl) ⟨1177872, by rfl⟩ : syracuseStep 3140993 = 2355745) B2355745
theorem B2093995 : Blo 2093435 2093995 := bstep (se 1 (by rfl) ⟨1570496, by rfl⟩ : syracuseStep 2093995 = 3140993) B3140993
theorem B5300437 : Blo 2093435 5300437 := bbase (se 7 (by rfl) ⟨62114, by rfl⟩ : syracuseStep 5300437 = 124229) (by norm_num)
theorem B7067249 : Blo 2093435 7067249 := bstep (se 2 (by rfl) ⟨2650218, by rfl⟩ : syracuseStep 7067249 = 5300437) B5300437
theorem B4711499 : Blo 2093435 4711499 := bstep (se 1 (by rfl) ⟨3533624, by rfl⟩ : syracuseStep 4711499 = 7067249) B7067249
theorem B3140999 : Blo 2093435 3140999 := bstep (se 1 (by rfl) ⟨2355749, by rfl⟩ : syracuseStep 3140999 = 4711499) B4711499
theorem B2093999 : Blo 2093435 2093999 := bstep (se 1 (by rfl) ⟨1570499, by rfl⟩ : syracuseStep 2093999 = 3140999) B3140999
theorem B3141005 : Blo 2093435 3141005 := bbase (se 3 (by rfl) ⟨588938, by rfl⟩ : syracuseStep 3141005 = 1177877) (by norm_num)
theorem B2094003 : Blo 2093435 2094003 := bstep (se 1 (by rfl) ⟨1570502, by rfl⟩ : syracuseStep 2094003 = 3141005) B3141005
theorem B4711517 : Blo 2093435 4711517 := bbase (se 3 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 4711517 = 1766819) (by norm_num)
theorem B3141011 : Blo 2093435 3141011 := bstep (se 1 (by rfl) ⟨2355758, by rfl⟩ : syracuseStep 3141011 = 4711517) B4711517
theorem B2094007 : Blo 2093435 2094007 := bstep (se 1 (by rfl) ⟨1570505, by rfl⟩ : syracuseStep 2094007 = 3141011) B3141011
theorem B3533645 : Blo 2093435 3533645 := bbase (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) (by norm_num)
theorem B2355763 : Blo 2093435 2355763 := bstep (se 1 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 2355763 = 3533645) B3533645
theorem B3141017 : Blo 2093435 3141017 := bstep (se 2 (by rfl) ⟨1177881, by rfl⟩ : syracuseStep 3141017 = 2355763) B2355763
theorem B2094011 : Blo 2093435 2094011 := bstep (se 1 (by rfl) ⟨1570508, by rfl⟩ : syracuseStep 2094011 = 3141017) B3141017
theorem B3773485 : Blo 2093435 3773485 := bbase (se 3 (by rfl) ⟨707528, by rfl⟩ : syracuseStep 3773485 = 1415057) (by norm_num)
theorem B20125253 : Blo 2093435 20125253 := bstep (se 4 (by rfl) ⟨1886742, by rfl⟩ : syracuseStep 20125253 = 3773485) B3773485
theorem B13416835 : Blo 2093435 13416835 := bstep (se 1 (by rfl) ⟨10062626, by rfl⟩ : syracuseStep 13416835 = 20125253) B20125253
theorem B17889113 : Blo 2093435 17889113 := bstep (se 2 (by rfl) ⟨6708417, by rfl⟩ : syracuseStep 17889113 = 13416835) B13416835
theorem B11926075 : Blo 2093435 11926075 := bstep (se 1 (by rfl) ⟨8944556, by rfl⟩ : syracuseStep 11926075 = 17889113) B17889113
theorem B15901433 : Blo 2093435 15901433 := bstep (se 2 (by rfl) ⟨5963037, by rfl⟩ : syracuseStep 15901433 = 11926075) B11926075
theorem B10600955 : Blo 2093435 10600955 := bstep (se 1 (by rfl) ⟨7950716, by rfl⟩ : syracuseStep 10600955 = 15901433) B15901433
theorem B7067303 : Blo 2093435 7067303 := bstep (se 1 (by rfl) ⟨5300477, by rfl⟩ : syracuseStep 7067303 = 10600955) B10600955
theorem B4711535 : Blo 2093435 4711535 := bstep (se 1 (by rfl) ⟨3533651, by rfl⟩ : syracuseStep 4711535 = 7067303) B7067303
theorem B3141023 : Blo 2093435 3141023 := bstep (se 1 (by rfl) ⟨2355767, by rfl⟩ : syracuseStep 3141023 = 4711535) B4711535
theorem B2094015 : Blo 2093435 2094015 := bstep (se 1 (by rfl) ⟨1570511, by rfl⟩ : syracuseStep 2094015 = 3141023) B3141023
theorem B3141029 : Blo 2093435 3141029 := bbase (se 4 (by rfl) ⟨294471, by rfl⟩ : syracuseStep 3141029 = 588943) (by norm_num)
theorem B2094019 : Blo 2093435 2094019 := bstep (se 1 (by rfl) ⟨1570514, by rfl⟩ : syracuseStep 2094019 = 3141029) B3141029
theorem B2650249 : Blo 2093435 2650249 := bbase (se 2 (by rfl) ⟨993843, by rfl⟩ : syracuseStep 2650249 = 1987687) (by norm_num)
theorem B3533665 : Blo 2093435 3533665 := bstep (se 2 (by rfl) ⟨1325124, by rfl⟩ : syracuseStep 3533665 = 2650249) B2650249
theorem B4711553 : Blo 2093435 4711553 := bstep (se 2 (by rfl) ⟨1766832, by rfl⟩ : syracuseStep 4711553 = 3533665) B3533665
theorem B3141035 : Blo 2093435 3141035 := bstep (se 1 (by rfl) ⟨2355776, by rfl⟩ : syracuseStep 3141035 = 4711553) B4711553
theorem B2094023 : Blo 2093435 2094023 := bstep (se 1 (by rfl) ⟨1570517, by rfl⟩ : syracuseStep 2094023 = 3141035) B3141035
theorem B2355781 : Blo 2093435 2355781 := bbase (se 4 (by rfl) ⟨220854, by rfl⟩ : syracuseStep 2355781 = 441709) (by norm_num)
theorem B3141041 : Blo 2093435 3141041 := bstep (se 2 (by rfl) ⟨1177890, by rfl⟩ : syracuseStep 3141041 = 2355781) B2355781
theorem B2094027 : Blo 2093435 2094027 := bstep (se 1 (by rfl) ⟨1570520, by rfl⟩ : syracuseStep 2094027 = 3141041) B3141041
theorem B3975389 : Blo 2093435 3975389 := bbase (se 3 (by rfl) ⟨745385, by rfl⟩ : syracuseStep 3975389 = 1490771) (by norm_num)
theorem B2650259 : Blo 2093435 2650259 := bstep (se 1 (by rfl) ⟨1987694, by rfl⟩ : syracuseStep 2650259 = 3975389) B3975389
theorem B7067357 : Blo 2093435 7067357 := bstep (se 3 (by rfl) ⟨1325129, by rfl⟩ : syracuseStep 7067357 = 2650259) B2650259
theorem B4711571 : Blo 2093435 4711571 := bstep (se 1 (by rfl) ⟨3533678, by rfl⟩ : syracuseStep 4711571 = 7067357) B7067357
theorem B3141047 : Blo 2093435 3141047 := bstep (se 1 (by rfl) ⟨2355785, by rfl⟩ : syracuseStep 3141047 = 4711571) B4711571
theorem B2094031 : Blo 2093435 2094031 := bstep (se 1 (by rfl) ⟨1570523, by rfl⟩ : syracuseStep 2094031 = 3141047) B3141047
theorem B3141053 : Blo 2093435 3141053 := bbase (se 3 (by rfl) ⟨588947, by rfl⟩ : syracuseStep 3141053 = 1177895) (by norm_num)
theorem B2094035 : Blo 2093435 2094035 := bstep (se 1 (by rfl) ⟨1570526, by rfl⟩ : syracuseStep 2094035 = 3141053) B3141053
theorem B4711589 : Blo 2093435 4711589 := bbase (se 4 (by rfl) ⟨441711, by rfl⟩ : syracuseStep 4711589 = 883423) (by norm_num)
theorem B3141059 : Blo 2093435 3141059 := bstep (se 1 (by rfl) ⟨2355794, by rfl⟩ : syracuseStep 3141059 = 4711589) B4711589
theorem B2094039 : Blo 2093435 2094039 := bstep (se 1 (by rfl) ⟨1570529, by rfl⟩ : syracuseStep 2094039 = 3141059) B3141059
theorem B5300549 : Blo 2093435 5300549 := bbase (se 4 (by rfl) ⟨496926, by rfl⟩ : syracuseStep 5300549 = 993853) (by norm_num)
theorem B3533699 : Blo 2093435 3533699 := bstep (se 1 (by rfl) ⟨2650274, by rfl⟩ : syracuseStep 3533699 = 5300549) B5300549
theorem B2355799 : Blo 2093435 2355799 := bstep (se 1 (by rfl) ⟨1766849, by rfl⟩ : syracuseStep 2355799 = 3533699) B3533699
theorem B3141065 : Blo 2093435 3141065 := bstep (se 2 (by rfl) ⟨1177899, by rfl⟩ : syracuseStep 3141065 = 2355799) B2355799
theorem B2094043 : Blo 2093435 2094043 := bstep (se 1 (by rfl) ⟨1570532, by rfl⟩ : syracuseStep 2094043 = 3141065) B3141065
theorem B20400149 : Blo 2093435 20400149 := bbase (se 6 (by rfl) ⟨478128, by rfl⟩ : syracuseStep 20400149 = 956257) (by norm_num)
theorem B13600099 : Blo 2093435 13600099 := bstep (se 1 (by rfl) ⟨10200074, by rfl⟩ : syracuseStep 13600099 = 20400149) B20400149
theorem B18133465 : Blo 2093435 18133465 := bstep (se 2 (by rfl) ⟨6800049, by rfl⟩ : syracuseStep 18133465 = 13600099) B13600099
theorem B24177953 : Blo 2093435 24177953 := bstep (se 2 (by rfl) ⟨9066732, by rfl⟩ : syracuseStep 24177953 = 18133465) B18133465
theorem B16118635 : Blo 2093435 16118635 := bstep (se 1 (by rfl) ⟨12088976, by rfl⟩ : syracuseStep 16118635 = 24177953) B24177953
theorem B21491513 : Blo 2093435 21491513 := bstep (se 2 (by rfl) ⟨8059317, by rfl⟩ : syracuseStep 21491513 = 16118635) B16118635
theorem B14327675 : Blo 2093435 14327675 := bstep (se 1 (by rfl) ⟨10745756, by rfl⟩ : syracuseStep 14327675 = 21491513) B21491513
theorem B9551783 : Blo 2093435 9551783 := bstep (se 1 (by rfl) ⟨7163837, by rfl⟩ : syracuseStep 9551783 = 14327675) B14327675
theorem B25471421 : Blo 2093435 25471421 := bstep (se 3 (by rfl) ⟨4775891, by rfl⟩ : syracuseStep 25471421 = 9551783) B9551783
theorem B16980947 : Blo 2093435 16980947 := bstep (se 1 (by rfl) ⟨12735710, by rfl⟩ : syracuseStep 16980947 = 25471421) B25471421
theorem B11320631 : Blo 2093435 11320631 := bstep (se 1 (by rfl) ⟨8490473, by rfl⟩ : syracuseStep 11320631 = 16980947) B16980947
theorem B7547087 : Blo 2093435 7547087 := bstep (se 1 (by rfl) ⟨5660315, by rfl⟩ : syracuseStep 7547087 = 11320631) B11320631
theorem B5031391 : Blo 2093435 5031391 := bstep (se 1 (by rfl) ⟨3773543, by rfl⟩ : syracuseStep 5031391 = 7547087) B7547087
theorem B6708521 : Blo 2093435 6708521 := bstep (se 2 (by rfl) ⟨2515695, by rfl⟩ : syracuseStep 6708521 = 5031391) B5031391
theorem B4472347 : Blo 2093435 4472347 := bstep (se 1 (by rfl) ⟨3354260, by rfl⟩ : syracuseStep 4472347 = 6708521) B6708521
theorem B5963129 : Blo 2093435 5963129 := bstep (se 2 (by rfl) ⟨2236173, by rfl⟩ : syracuseStep 5963129 = 4472347) B4472347
theorem B3975419 : Blo 2093435 3975419 := bstep (se 1 (by rfl) ⟨2981564, by rfl⟩ : syracuseStep 3975419 = 5963129) B5963129
theorem B10601117 : Blo 2093435 10601117 := bstep (se 3 (by rfl) ⟨1987709, by rfl⟩ : syracuseStep 10601117 = 3975419) B3975419
theorem B7067411 : Blo 2093435 7067411 := bstep (se 1 (by rfl) ⟨5300558, by rfl⟩ : syracuseStep 7067411 = 10601117) B10601117
theorem B4711607 : Blo 2093435 4711607 := bstep (se 1 (by rfl) ⟨3533705, by rfl⟩ : syracuseStep 4711607 = 7067411) B7067411
theorem B3141071 : Blo 2093435 3141071 := bstep (se 1 (by rfl) ⟨2355803, by rfl⟩ : syracuseStep 3141071 = 4711607) B4711607
theorem B2094047 : Blo 2093435 2094047 := bstep (se 1 (by rfl) ⟨1570535, by rfl⟩ : syracuseStep 2094047 = 3141071) B3141071
theorem B3141077 : Blo 2093435 3141077 := bbase (se 7 (by rfl) ⟨36809, by rfl⟩ : syracuseStep 3141077 = 73619) (by norm_num)
theorem B2094051 : Blo 2093435 2094051 := bstep (se 1 (by rfl) ⟨1570538, by rfl⟩ : syracuseStep 2094051 = 3141077) B3141077
theorem B7950869 : Blo 2093435 7950869 := bbase (se 6 (by rfl) ⟨186348, by rfl⟩ : syracuseStep 7950869 = 372697) (by norm_num)
theorem B5300579 : Blo 2093435 5300579 := bstep (se 1 (by rfl) ⟨3975434, by rfl⟩ : syracuseStep 5300579 = 7950869) B7950869
theorem B3533719 : Blo 2093435 3533719 := bstep (se 1 (by rfl) ⟨2650289, by rfl⟩ : syracuseStep 3533719 = 5300579) B5300579
theorem B4711625 : Blo 2093435 4711625 := bstep (se 2 (by rfl) ⟨1766859, by rfl⟩ : syracuseStep 4711625 = 3533719) B3533719
theorem B3141083 : Blo 2093435 3141083 := bstep (se 1 (by rfl) ⟨2355812, by rfl⟩ : syracuseStep 3141083 = 4711625) B4711625
theorem B2094055 : Blo 2093435 2094055 := bstep (se 1 (by rfl) ⟨1570541, by rfl⟩ : syracuseStep 2094055 = 3141083) B3141083
theorem B2355817 : Blo 2093435 2355817 := bbase (se 2 (by rfl) ⟨883431, by rfl⟩ : syracuseStep 2355817 = 1766863) (by norm_num)
theorem B3141089 : Blo 2093435 3141089 := bstep (se 2 (by rfl) ⟨1177908, by rfl⟩ : syracuseStep 3141089 = 2355817) B2355817
theorem B2094059 : Blo 2093435 2094059 := bstep (se 1 (by rfl) ⟨1570544, by rfl⟩ : syracuseStep 2094059 = 3141089) B3141089
theorem B4472381 : Blo 2093435 4472381 := bbase (se 3 (by rfl) ⟨838571, by rfl⟩ : syracuseStep 4472381 = 1677143) (by norm_num)
theorem B11926349 : Blo 2093435 11926349 := bstep (se 3 (by rfl) ⟨2236190, by rfl⟩ : syracuseStep 11926349 = 4472381) B4472381
theorem B7950899 : Blo 2093435 7950899 := bstep (se 1 (by rfl) ⟨5963174, by rfl⟩ : syracuseStep 7950899 = 11926349) B11926349
theorem B5300599 : Blo 2093435 5300599 := bstep (se 1 (by rfl) ⟨3975449, by rfl⟩ : syracuseStep 5300599 = 7950899) B7950899
theorem B7067465 : Blo 2093435 7067465 := bstep (se 2 (by rfl) ⟨2650299, by rfl⟩ : syracuseStep 7067465 = 5300599) B5300599
theorem B4711643 : Blo 2093435 4711643 := bstep (se 1 (by rfl) ⟨3533732, by rfl⟩ : syracuseStep 4711643 = 7067465) B7067465
theorem B3141095 : Blo 2093435 3141095 := bstep (se 1 (by rfl) ⟨2355821, by rfl⟩ : syracuseStep 3141095 = 4711643) B4711643
theorem B2094063 : Blo 2093435 2094063 := bstep (se 1 (by rfl) ⟨1570547, by rfl⟩ : syracuseStep 2094063 = 3141095) B3141095
theorem B3141101 : Blo 2093435 3141101 := bbase (se 3 (by rfl) ⟨588956, by rfl⟩ : syracuseStep 3141101 = 1177913) (by norm_num)
theorem B2094067 : Blo 2093435 2094067 := bstep (se 1 (by rfl) ⟨1570550, by rfl⟩ : syracuseStep 2094067 = 3141101) B3141101
theorem B4711661 : Blo 2093435 4711661 := bbase (se 3 (by rfl) ⟨883436, by rfl⟩ : syracuseStep 4711661 = 1766873) (by norm_num)
theorem B3141107 : Blo 2093435 3141107 := bstep (se 1 (by rfl) ⟨2355830, by rfl⟩ : syracuseStep 3141107 = 4711661) B4711661
theorem B2094071 : Blo 2093435 2094071 := bstep (se 1 (by rfl) ⟨1570553, by rfl⟩ : syracuseStep 2094071 = 3141107) B3141107
theorem B2981605 : Blo 2093435 2981605 := bbase (se 4 (by rfl) ⟨279525, by rfl⟩ : syracuseStep 2981605 = 559051) (by norm_num)
theorem B3975473 : Blo 2093435 3975473 := bstep (se 2 (by rfl) ⟨1490802, by rfl⟩ : syracuseStep 3975473 = 2981605) B2981605
theorem B2650315 : Blo 2093435 2650315 := bstep (se 1 (by rfl) ⟨1987736, by rfl⟩ : syracuseStep 2650315 = 3975473) B3975473
theorem B3533753 : Blo 2093435 3533753 := bstep (se 2 (by rfl) ⟨1325157, by rfl⟩ : syracuseStep 3533753 = 2650315) B2650315
theorem B2355835 : Blo 2093435 2355835 := bstep (se 1 (by rfl) ⟨1766876, by rfl⟩ : syracuseStep 2355835 = 3533753) B3533753
theorem B3141113 : Blo 2093435 3141113 := bstep (se 2 (by rfl) ⟨1177917, by rfl⟩ : syracuseStep 3141113 = 2355835) B2355835
theorem B2094075 : Blo 2093435 2094075 := bstep (se 1 (by rfl) ⟨1570556, by rfl⟩ : syracuseStep 2094075 = 3141113) B3141113
theorem B10339397 : Blo 2093435 10339397 := bbase (se 4 (by rfl) ⟨969318, by rfl⟩ : syracuseStep 10339397 = 1938637) (by norm_num)
theorem B6892931 : Blo 2093435 6892931 := bstep (se 1 (by rfl) ⟨5169698, by rfl⟩ : syracuseStep 6892931 = 10339397) B10339397
theorem B4595287 : Blo 2093435 4595287 := bstep (se 1 (by rfl) ⟨3446465, by rfl⟩ : syracuseStep 4595287 = 6892931) B6892931
theorem B6127049 : Blo 2093435 6127049 := bstep (se 2 (by rfl) ⟨2297643, by rfl⟩ : syracuseStep 6127049 = 4595287) B4595287
theorem B16338797 : Blo 2093435 16338797 := bstep (se 3 (by rfl) ⟨3063524, by rfl⟩ : syracuseStep 16338797 = 6127049) B6127049
theorem B10892531 : Blo 2093435 10892531 := bstep (se 1 (by rfl) ⟨8169398, by rfl⟩ : syracuseStep 10892531 = 16338797) B16338797
theorem B7261687 : Blo 2093435 7261687 := bstep (se 1 (by rfl) ⟨5446265, by rfl⟩ : syracuseStep 7261687 = 10892531) B10892531
theorem B9682249 : Blo 2093435 9682249 := bstep (se 2 (by rfl) ⟨3630843, by rfl⟩ : syracuseStep 9682249 = 7261687) B7261687
theorem B12909665 : Blo 2093435 12909665 := bstep (se 2 (by rfl) ⟨4841124, by rfl⟩ : syracuseStep 12909665 = 9682249) B9682249
theorem B34425773 : Blo 2093435 34425773 := bstep (se 3 (by rfl) ⟨6454832, by rfl⟩ : syracuseStep 34425773 = 12909665) B12909665
theorem B22950515 : Blo 2093435 22950515 := bstep (se 1 (by rfl) ⟨17212886, by rfl⟩ : syracuseStep 22950515 = 34425773) B34425773
theorem B15300343 : Blo 2093435 15300343 := bstep (se 1 (by rfl) ⟨11475257, by rfl⟩ : syracuseStep 15300343 = 22950515) B22950515
theorem B20400457 : Blo 2093435 20400457 := bstep (se 2 (by rfl) ⟨7650171, by rfl⟩ : syracuseStep 20400457 = 15300343) B15300343
theorem B27200609 : Blo 2093435 27200609 := bstep (se 2 (by rfl) ⟨10200228, by rfl⟩ : syracuseStep 27200609 = 20400457) B20400457
theorem B18133739 : Blo 2093435 18133739 := bstep (se 1 (by rfl) ⟨13600304, by rfl⟩ : syracuseStep 18133739 = 27200609) B27200609
theorem B12089159 : Blo 2093435 12089159 := bstep (se 1 (by rfl) ⟨9066869, by rfl⟩ : syracuseStep 12089159 = 18133739) B18133739
theorem B8059439 : Blo 2093435 8059439 := bstep (se 1 (by rfl) ⟨6044579, by rfl⟩ : syracuseStep 8059439 = 12089159) B12089159
theorem B5372959 : Blo 2093435 5372959 := bstep (se 1 (by rfl) ⟨4029719, by rfl⟩ : syracuseStep 5372959 = 8059439) B8059439
theorem B7163945 : Blo 2093435 7163945 := bstep (se 2 (by rfl) ⟨2686479, by rfl⟩ : syracuseStep 7163945 = 5372959) B5372959
theorem B4775963 : Blo 2093435 4775963 := bstep (se 1 (by rfl) ⟨3581972, by rfl⟩ : syracuseStep 4775963 = 7163945) B7163945
theorem B12735901 : Blo 2093435 12735901 := bstep (se 3 (by rfl) ⟨2387981, by rfl⟩ : syracuseStep 12735901 = 4775963) B4775963
theorem B16981201 : Blo 2093435 16981201 := bstep (se 2 (by rfl) ⟨6367950, by rfl⟩ : syracuseStep 16981201 = 12735901) B12735901
theorem B22641601 : Blo 2093435 22641601 := bstep (se 2 (by rfl) ⟨8490600, by rfl⟩ : syracuseStep 22641601 = 16981201) B16981201
theorem B30188801 : Blo 2093435 30188801 := bstep (se 2 (by rfl) ⟨11320800, by rfl⟩ : syracuseStep 30188801 = 22641601) B22641601
theorem B80503469 : Blo 2093435 80503469 := bstep (se 3 (by rfl) ⟨15094400, by rfl⟩ : syracuseStep 80503469 = 30188801) B30188801
theorem B53668979 : Blo 2093435 53668979 := bstep (se 1 (by rfl) ⟨40251734, by rfl⟩ : syracuseStep 53668979 = 80503469) B80503469
theorem B35779319 : Blo 2093435 35779319 := bstep (se 1 (by rfl) ⟨26834489, by rfl⟩ : syracuseStep 35779319 = 53668979) B53668979
theorem B23852879 : Blo 2093435 23852879 := bstep (se 1 (by rfl) ⟨17889659, by rfl⟩ : syracuseStep 23852879 = 35779319) B35779319
theorem B15901919 : Blo 2093435 15901919 := bstep (se 1 (by rfl) ⟨11926439, by rfl⟩ : syracuseStep 15901919 = 23852879) B23852879
theorem B10601279 : Blo 2093435 10601279 := bstep (se 1 (by rfl) ⟨7950959, by rfl⟩ : syracuseStep 10601279 = 15901919) B15901919
theorem B7067519 : Blo 2093435 7067519 := bstep (se 1 (by rfl) ⟨5300639, by rfl⟩ : syracuseStep 7067519 = 10601279) B10601279
theorem B4711679 : Blo 2093435 4711679 := bstep (se 1 (by rfl) ⟨3533759, by rfl⟩ : syracuseStep 4711679 = 7067519) B7067519
theorem B3141119 : Blo 2093435 3141119 := bstep (se 1 (by rfl) ⟨2355839, by rfl⟩ : syracuseStep 3141119 = 4711679) B4711679
theorem B2094079 : Blo 2093435 2094079 := bstep (se 1 (by rfl) ⟨1570559, by rfl⟩ : syracuseStep 2094079 = 3141119) B3141119
theorem B3141125 : Blo 2093435 3141125 := bbase (se 4 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 3141125 = 588961) (by norm_num)
theorem B2094083 : Blo 2093435 2094083 := bstep (se 1 (by rfl) ⟨1570562, by rfl⟩ : syracuseStep 2094083 = 3141125) B3141125
theorem B3533773 : Blo 2093435 3533773 := bbase (se 3 (by rfl) ⟨662582, by rfl⟩ : syracuseStep 3533773 = 1325165) (by norm_num)
theorem B4711697 : Blo 2093435 4711697 := bstep (se 2 (by rfl) ⟨1766886, by rfl⟩ : syracuseStep 4711697 = 3533773) B3533773
theorem B3141131 : Blo 2093435 3141131 := bstep (se 1 (by rfl) ⟨2355848, by rfl⟩ : syracuseStep 3141131 = 4711697) B4711697
theorem B2094087 : Blo 2093435 2094087 := bstep (se 1 (by rfl) ⟨1570565, by rfl⟩ : syracuseStep 2094087 = 3141131) B3141131
theorem B2355853 : Blo 2093435 2355853 := bbase (se 3 (by rfl) ⟨441722, by rfl⟩ : syracuseStep 2355853 = 883445) (by norm_num)
theorem B3141137 : Blo 2093435 3141137 := bstep (se 2 (by rfl) ⟨1177926, by rfl⟩ : syracuseStep 3141137 = 2355853) B2355853
theorem B2094091 : Blo 2093435 2094091 := bstep (se 1 (by rfl) ⟨1570568, by rfl⟩ : syracuseStep 2094091 = 3141137) B3141137
theorem B7067573 : Blo 2093435 7067573 := bbase (se 5 (by rfl) ⟨331292, by rfl⟩ : syracuseStep 7067573 = 662585) (by norm_num)
theorem B4711715 : Blo 2093435 4711715 := bstep (se 1 (by rfl) ⟨3533786, by rfl⟩ : syracuseStep 4711715 = 7067573) B7067573
theorem B3141143 : Blo 2093435 3141143 := bstep (se 1 (by rfl) ⟨2355857, by rfl⟩ : syracuseStep 3141143 = 4711715) B4711715
theorem B2094095 : Blo 2093435 2094095 := bstep (se 1 (by rfl) ⟨1570571, by rfl⟩ : syracuseStep 2094095 = 3141143) B3141143
theorem B3141149 : Blo 2093435 3141149 := bbase (se 3 (by rfl) ⟨588965, by rfl⟩ : syracuseStep 3141149 = 1177931) (by norm_num)
theorem B2094099 : Blo 2093435 2094099 := bstep (se 1 (by rfl) ⟨1570574, by rfl⟩ : syracuseStep 2094099 = 3141149) B3141149
theorem B4711733 : Blo 2093435 4711733 := bbase (se 5 (by rfl) ⟨220862, by rfl⟩ : syracuseStep 4711733 = 441725) (by norm_num)
theorem B3141155 : Blo 2093435 3141155 := bstep (se 1 (by rfl) ⟨2355866, by rfl⟩ : syracuseStep 3141155 = 4711733) B4711733
theorem B2094103 : Blo 2093435 2094103 := bstep (se 1 (by rfl) ⟨1570577, by rfl⟩ : syracuseStep 2094103 = 3141155) B3141155
theorem B14328085 : Blo 2093435 14328085 := bbase (se 6 (by rfl) ⟨335814, by rfl⟩ : syracuseStep 14328085 = 671629) (by norm_num)
theorem B19104113 : Blo 2093435 19104113 := bstep (se 2 (by rfl) ⟨7164042, by rfl⟩ : syracuseStep 19104113 = 14328085) B14328085
theorem B12736075 : Blo 2093435 12736075 := bstep (se 1 (by rfl) ⟨9552056, by rfl⟩ : syracuseStep 12736075 = 19104113) B19104113
theorem B16981433 : Blo 2093435 16981433 := bstep (se 2 (by rfl) ⟨6368037, by rfl⟩ : syracuseStep 16981433 = 12736075) B12736075
theorem B11320955 : Blo 2093435 11320955 := bstep (se 1 (by rfl) ⟨8490716, by rfl⟩ : syracuseStep 11320955 = 16981433) B16981433
theorem B7547303 : Blo 2093435 7547303 := bstep (se 1 (by rfl) ⟨5660477, by rfl⟩ : syracuseStep 7547303 = 11320955) B11320955
theorem B20126141 : Blo 2093435 20126141 := bstep (se 3 (by rfl) ⟨3773651, by rfl⟩ : syracuseStep 20126141 = 7547303) B7547303
theorem B13417427 : Blo 2093435 13417427 := bstep (se 1 (by rfl) ⟨10063070, by rfl⟩ : syracuseStep 13417427 = 20126141) B20126141
theorem B8944951 : Blo 2093435 8944951 := bstep (se 1 (by rfl) ⟨6708713, by rfl⟩ : syracuseStep 8944951 = 13417427) B13417427
theorem B11926601 : Blo 2093435 11926601 := bstep (se 2 (by rfl) ⟨4472475, by rfl⟩ : syracuseStep 11926601 = 8944951) B8944951
theorem B7951067 : Blo 2093435 7951067 := bstep (se 1 (by rfl) ⟨5963300, by rfl⟩ : syracuseStep 7951067 = 11926601) B11926601
theorem B5300711 : Blo 2093435 5300711 := bstep (se 1 (by rfl) ⟨3975533, by rfl⟩ : syracuseStep 5300711 = 7951067) B7951067
theorem B3533807 : Blo 2093435 3533807 := bstep (se 1 (by rfl) ⟨2650355, by rfl⟩ : syracuseStep 3533807 = 5300711) B5300711
theorem B2355871 : Blo 2093435 2355871 := bstep (se 1 (by rfl) ⟨1766903, by rfl⟩ : syracuseStep 2355871 = 3533807) B3533807
theorem B3141161 : Blo 2093435 3141161 := bstep (se 2 (by rfl) ⟨1177935, by rfl⟩ : syracuseStep 3141161 = 2355871) B2355871
theorem B2094107 : Blo 2093435 2094107 := bstep (se 1 (by rfl) ⟨1570580, by rfl⟩ : syracuseStep 2094107 = 3141161) B3141161
theorem B16119125 : Blo 2093435 16119125 := bbase (se 13 (by rfl) ⟨2951, by rfl⟩ : syracuseStep 16119125 = 5903) (by norm_num)
theorem B10746083 : Blo 2093435 10746083 := bstep (se 1 (by rfl) ⟨8059562, by rfl⟩ : syracuseStep 10746083 = 16119125) B16119125
theorem B7164055 : Blo 2093435 7164055 := bstep (se 1 (by rfl) ⟨5373041, by rfl⟩ : syracuseStep 7164055 = 10746083) B10746083
theorem B38208293 : Blo 2093435 38208293 := bstep (se 4 (by rfl) ⟨3582027, by rfl⟩ : syracuseStep 38208293 = 7164055) B7164055
theorem B25472195 : Blo 2093435 25472195 := bstep (se 1 (by rfl) ⟨19104146, by rfl⟩ : syracuseStep 25472195 = 38208293) B38208293
theorem B16981463 : Blo 2093435 16981463 := bstep (se 1 (by rfl) ⟨12736097, by rfl⟩ : syracuseStep 16981463 = 25472195) B25472195
theorem B11320975 : Blo 2093435 11320975 := bstep (se 1 (by rfl) ⟨8490731, by rfl⟩ : syracuseStep 11320975 = 16981463) B16981463
theorem B15094633 : Blo 2093435 15094633 := bstep (se 2 (by rfl) ⟨5660487, by rfl⟩ : syracuseStep 15094633 = 11320975) B11320975
theorem B20126177 : Blo 2093435 20126177 := bstep (se 2 (by rfl) ⟨7547316, by rfl⟩ : syracuseStep 20126177 = 15094633) B15094633
theorem B13417451 : Blo 2093435 13417451 := bstep (se 1 (by rfl) ⟨10063088, by rfl⟩ : syracuseStep 13417451 = 20126177) B20126177
theorem B8944967 : Blo 2093435 8944967 := bstep (se 1 (by rfl) ⟨6708725, by rfl⟩ : syracuseStep 8944967 = 13417451) B13417451
theorem B5963311 : Blo 2093435 5963311 := bstep (se 1 (by rfl) ⟨4472483, by rfl⟩ : syracuseStep 5963311 = 8944967) B8944967
theorem B7951081 : Blo 2093435 7951081 := bstep (se 2 (by rfl) ⟨2981655, by rfl⟩ : syracuseStep 7951081 = 5963311) B5963311
theorem B10601441 : Blo 2093435 10601441 := bstep (se 2 (by rfl) ⟨3975540, by rfl⟩ : syracuseStep 10601441 = 7951081) B7951081
theorem B7067627 : Blo 2093435 7067627 := bstep (se 1 (by rfl) ⟨5300720, by rfl⟩ : syracuseStep 7067627 = 10601441) B10601441
theorem B4711751 : Blo 2093435 4711751 := bstep (se 1 (by rfl) ⟨3533813, by rfl⟩ : syracuseStep 4711751 = 7067627) B7067627
theorem B3141167 : Blo 2093435 3141167 := bstep (se 1 (by rfl) ⟨2355875, by rfl⟩ : syracuseStep 3141167 = 4711751) B4711751
theorem B2094111 : Blo 2093435 2094111 := bstep (se 1 (by rfl) ⟨1570583, by rfl⟩ : syracuseStep 2094111 = 3141167) B3141167
theorem B3141173 : Blo 2093435 3141173 := bbase (se 5 (by rfl) ⟨147242, by rfl⟩ : syracuseStep 3141173 = 294485) (by norm_num)
theorem B2094115 : Blo 2093435 2094115 := bstep (se 1 (by rfl) ⟨1570586, by rfl⟩ : syracuseStep 2094115 = 3141173) B3141173
theorem B5300741 : Blo 2093435 5300741 := bbase (se 4 (by rfl) ⟨496944, by rfl⟩ : syracuseStep 5300741 = 993889) (by norm_num)
theorem B3533827 : Blo 2093435 3533827 := bstep (se 1 (by rfl) ⟨2650370, by rfl⟩ : syracuseStep 3533827 = 5300741) B5300741
theorem B4711769 : Blo 2093435 4711769 := bstep (se 2 (by rfl) ⟨1766913, by rfl⟩ : syracuseStep 4711769 = 3533827) B3533827
theorem B3141179 : Blo 2093435 3141179 := bstep (se 1 (by rfl) ⟨2355884, by rfl⟩ : syracuseStep 3141179 = 4711769) B4711769
theorem B2094119 : Blo 2093435 2094119 := bstep (se 1 (by rfl) ⟨1570589, by rfl⟩ : syracuseStep 2094119 = 3141179) B3141179
theorem B2355889 : Blo 2093435 2355889 := bbase (se 2 (by rfl) ⟨883458, by rfl⟩ : syracuseStep 2355889 = 1766917) (by norm_num)
theorem B3141185 : Blo 2093435 3141185 := bstep (se 2 (by rfl) ⟨1177944, by rfl⟩ : syracuseStep 3141185 = 2355889) B2355889
theorem B2094123 : Blo 2093435 2094123 := bstep (se 1 (by rfl) ⟨1570592, by rfl⟩ : syracuseStep 2094123 = 3141185) B3141185
theorem B3354389 : Blo 2093435 3354389 := bbase (se 6 (by rfl) ⟨78618, by rfl⟩ : syracuseStep 3354389 = 157237) (by norm_num)
theorem B2236259 : Blo 2093435 2236259 := bstep (se 1 (by rfl) ⟨1677194, by rfl⟩ : syracuseStep 2236259 = 3354389) B3354389
theorem B5963357 : Blo 2093435 5963357 := bstep (se 3 (by rfl) ⟨1118129, by rfl⟩ : syracuseStep 5963357 = 2236259) B2236259
theorem B3975571 : Blo 2093435 3975571 := bstep (se 1 (by rfl) ⟨2981678, by rfl⟩ : syracuseStep 3975571 = 5963357) B5963357
theorem B5300761 : Blo 2093435 5300761 := bstep (se 2 (by rfl) ⟨1987785, by rfl⟩ : syracuseStep 5300761 = 3975571) B3975571
theorem B7067681 : Blo 2093435 7067681 := bstep (se 2 (by rfl) ⟨2650380, by rfl⟩ : syracuseStep 7067681 = 5300761) B5300761
theorem B4711787 : Blo 2093435 4711787 := bstep (se 1 (by rfl) ⟨3533840, by rfl⟩ : syracuseStep 4711787 = 7067681) B7067681
theorem B3141191 : Blo 2093435 3141191 := bstep (se 1 (by rfl) ⟨2355893, by rfl⟩ : syracuseStep 3141191 = 4711787) B4711787
theorem B2094127 : Blo 2093435 2094127 := bstep (se 1 (by rfl) ⟨1570595, by rfl⟩ : syracuseStep 2094127 = 3141191) B3141191
theorem B3141197 : Blo 2093435 3141197 := bbase (se 3 (by rfl) ⟨588974, by rfl⟩ : syracuseStep 3141197 = 1177949) (by norm_num)
theorem B2094131 : Blo 2093435 2094131 := bstep (se 1 (by rfl) ⟨1570598, by rfl⟩ : syracuseStep 2094131 = 3141197) B3141197
theorem B4711805 : Blo 2093435 4711805 := bbase (se 3 (by rfl) ⟨883463, by rfl⟩ : syracuseStep 4711805 = 1766927) (by norm_num)
theorem B3141203 : Blo 2093435 3141203 := bstep (se 1 (by rfl) ⟨2355902, by rfl⟩ : syracuseStep 3141203 = 4711805) B4711805
theorem B2094135 : Blo 2093435 2094135 := bstep (se 1 (by rfl) ⟨1570601, by rfl⟩ : syracuseStep 2094135 = 3141203) B3141203
theorem B3533861 : Blo 2093435 3533861 := bbase (se 4 (by rfl) ⟨331299, by rfl⟩ : syracuseStep 3533861 = 662599) (by norm_num)
theorem B2355907 : Blo 2093435 2355907 := bstep (se 1 (by rfl) ⟨1766930, by rfl⟩ : syracuseStep 2355907 = 3533861) B3533861
theorem B3141209 : Blo 2093435 3141209 := bstep (se 2 (by rfl) ⟨1177953, by rfl⟩ : syracuseStep 3141209 = 2355907) B2355907
theorem B2094139 : Blo 2093435 2094139 := bstep (se 1 (by rfl) ⟨1570604, by rfl⟩ : syracuseStep 2094139 = 3141209) B3141209
theorem B2981701 : Blo 2093435 2981701 := bbase (se 4 (by rfl) ⟨279534, by rfl⟩ : syracuseStep 2981701 = 559069) (by norm_num)
theorem B15902405 : Blo 2093435 15902405 := bstep (se 4 (by rfl) ⟨1490850, by rfl⟩ : syracuseStep 15902405 = 2981701) B2981701
theorem B10601603 : Blo 2093435 10601603 := bstep (se 1 (by rfl) ⟨7951202, by rfl⟩ : syracuseStep 10601603 = 15902405) B15902405
theorem B7067735 : Blo 2093435 7067735 := bstep (se 1 (by rfl) ⟨5300801, by rfl⟩ : syracuseStep 7067735 = 10601603) B10601603
theorem B4711823 : Blo 2093435 4711823 := bstep (se 1 (by rfl) ⟨3533867, by rfl⟩ : syracuseStep 4711823 = 7067735) B7067735
theorem B3141215 : Blo 2093435 3141215 := bstep (se 1 (by rfl) ⟨2355911, by rfl⟩ : syracuseStep 3141215 = 4711823) B4711823
theorem B2094143 : Blo 2093435 2094143 := bstep (se 1 (by rfl) ⟨1570607, by rfl⟩ : syracuseStep 2094143 = 3141215) B3141215
theorem B3141221 : Blo 2093435 3141221 := bbase (se 4 (by rfl) ⟨294489, by rfl⟩ : syracuseStep 3141221 = 588979) (by norm_num)
theorem B2094147 : Blo 2093435 2094147 := bstep (se 1 (by rfl) ⟨1570610, by rfl⟩ : syracuseStep 2094147 = 3141221) B3141221
theorem B2236285 : Blo 2093435 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B2981713 : Blo 2093435 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B3975617 : Blo 2093435 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B2650411 : Blo 2093435 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B3533881 : Blo 2093435 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B4711841 : Blo 2093435 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B3141227 : Blo 2093435 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B2094151 : Blo 2093435 2094151 := bstep (se 1 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 2094151 = 3141227) B3141227
theorem B2355925 : Blo 2093435 2355925 := bbase (se 7 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 2355925 = 55217) (by norm_num)
theorem B3141233 : Blo 2093435 3141233 := bstep (se 2 (by rfl) ⟨1177962, by rfl⟩ : syracuseStep 3141233 = 2355925) B2355925
theorem B2094155 : Blo 2093435 2094155 := bstep (se 1 (by rfl) ⟨1570616, by rfl⟩ : syracuseStep 2094155 = 3141233) B3141233
theorem B2650421 : Blo 2093435 2650421 := bbase (se 5 (by rfl) ⟨124238, by rfl⟩ : syracuseStep 2650421 = 248477) (by norm_num)
theorem B7067789 : Blo 2093435 7067789 := bstep (se 3 (by rfl) ⟨1325210, by rfl⟩ : syracuseStep 7067789 = 2650421) B2650421
theorem B4711859 : Blo 2093435 4711859 := bstep (se 1 (by rfl) ⟨3533894, by rfl⟩ : syracuseStep 4711859 = 7067789) B7067789
theorem B3141239 : Blo 2093435 3141239 := bstep (se 1 (by rfl) ⟨2355929, by rfl⟩ : syracuseStep 3141239 = 4711859) B4711859
theorem B2094159 : Blo 2093435 2094159 := bstep (se 1 (by rfl) ⟨1570619, by rfl⟩ : syracuseStep 2094159 = 3141239) B3141239
theorem B3141245 : Blo 2093435 3141245 := bbase (se 3 (by rfl) ⟨588983, by rfl⟩ : syracuseStep 3141245 = 1177967) (by norm_num)
theorem B2094163 : Blo 2093435 2094163 := bstep (se 1 (by rfl) ⟨1570622, by rfl⟩ : syracuseStep 2094163 = 3141245) B3141245
theorem B4711877 : Blo 2093435 4711877 := bbase (se 4 (by rfl) ⟨441738, by rfl⟩ : syracuseStep 4711877 = 883477) (by norm_num)
theorem B3141251 : Blo 2093435 3141251 := bstep (se 1 (by rfl) ⟨2355938, by rfl⟩ : syracuseStep 3141251 = 4711877) B4711877
theorem B2094167 : Blo 2093435 2094167 := bstep (se 1 (by rfl) ⟨1570625, by rfl⟩ : syracuseStep 2094167 = 3141251) B3141251
theorem B6893237 : Blo 2093435 6893237 := bbase (se 5 (by rfl) ⟨323120, by rfl⟩ : syracuseStep 6893237 = 646241) (by norm_num)
theorem B4595491 : Blo 2093435 4595491 := bstep (se 1 (by rfl) ⟨3446618, by rfl⟩ : syracuseStep 4595491 = 6893237) B6893237
theorem B6127321 : Blo 2093435 6127321 := bstep (se 2 (by rfl) ⟨2297745, by rfl⟩ : syracuseStep 6127321 = 4595491) B4595491
theorem B8169761 : Blo 2093435 8169761 := bstep (se 2 (by rfl) ⟨3063660, by rfl⟩ : syracuseStep 8169761 = 6127321) B6127321
theorem B21786029 : Blo 2093435 21786029 := bstep (se 3 (by rfl) ⟨4084880, by rfl⟩ : syracuseStep 21786029 = 8169761) B8169761
theorem B14524019 : Blo 2093435 14524019 := bstep (se 1 (by rfl) ⟨10893014, by rfl⟩ : syracuseStep 14524019 = 21786029) B21786029
theorem B9682679 : Blo 2093435 9682679 := bstep (se 1 (by rfl) ⟨7262009, by rfl⟩ : syracuseStep 9682679 = 14524019) B14524019
theorem B6455119 : Blo 2093435 6455119 := bstep (se 1 (by rfl) ⟨4841339, by rfl⟩ : syracuseStep 6455119 = 9682679) B9682679
theorem B8606825 : Blo 2093435 8606825 := bstep (se 2 (by rfl) ⟨3227559, by rfl⟩ : syracuseStep 8606825 = 6455119) B6455119
theorem B5737883 : Blo 2093435 5737883 := bstep (se 1 (by rfl) ⟨4303412, by rfl⟩ : syracuseStep 5737883 = 8606825) B8606825
theorem B61204085 : Blo 2093435 61204085 := bstep (se 5 (by rfl) ⟨2868941, by rfl⟩ : syracuseStep 61204085 = 5737883) B5737883
theorem B40802723 : Blo 2093435 40802723 := bstep (se 1 (by rfl) ⟨30602042, by rfl⟩ : syracuseStep 40802723 = 61204085) B61204085
theorem B27201815 : Blo 2093435 27201815 := bstep (se 1 (by rfl) ⟨20401361, by rfl⟩ : syracuseStep 27201815 = 40802723) B40802723
theorem B18134543 : Blo 2093435 18134543 := bstep (se 1 (by rfl) ⟨13600907, by rfl⟩ : syracuseStep 18134543 = 27201815) B27201815
theorem B12089695 : Blo 2093435 12089695 := bstep (se 1 (by rfl) ⟨9067271, by rfl⟩ : syracuseStep 12089695 = 18134543) B18134543
theorem B16119593 : Blo 2093435 16119593 := bstep (se 2 (by rfl) ⟨6044847, by rfl⟩ : syracuseStep 16119593 = 12089695) B12089695
theorem B10746395 : Blo 2093435 10746395 := bstep (se 1 (by rfl) ⟨8059796, by rfl⟩ : syracuseStep 10746395 = 16119593) B16119593
theorem B7164263 : Blo 2093435 7164263 := bstep (se 1 (by rfl) ⟨5373197, by rfl⟩ : syracuseStep 7164263 = 10746395) B10746395
theorem B4776175 : Blo 2093435 4776175 := bstep (se 1 (by rfl) ⟨3582131, by rfl⟩ : syracuseStep 4776175 = 7164263) B7164263
theorem B6368233 : Blo 2093435 6368233 := bstep (se 2 (by rfl) ⟨2388087, by rfl⟩ : syracuseStep 6368233 = 4776175) B4776175
theorem B8490977 : Blo 2093435 8490977 := bstep (se 2 (by rfl) ⟨3184116, by rfl⟩ : syracuseStep 8490977 = 6368233) B6368233
theorem B5660651 : Blo 2093435 5660651 := bstep (se 1 (by rfl) ⟨4245488, by rfl⟩ : syracuseStep 5660651 = 8490977) B8490977
theorem B15095069 : Blo 2093435 15095069 := bstep (se 3 (by rfl) ⟨2830325, by rfl⟩ : syracuseStep 15095069 = 5660651) B5660651
theorem B10063379 : Blo 2093435 10063379 := bstep (se 1 (by rfl) ⟨7547534, by rfl⟩ : syracuseStep 10063379 = 15095069) B15095069
theorem B6708919 : Blo 2093435 6708919 := bstep (se 1 (by rfl) ⟨5031689, by rfl⟩ : syracuseStep 6708919 = 10063379) B10063379
theorem B8945225 : Blo 2093435 8945225 := bstep (se 2 (by rfl) ⟨3354459, by rfl⟩ : syracuseStep 8945225 = 6708919) B6708919
theorem B5963483 : Blo 2093435 5963483 := bstep (se 1 (by rfl) ⟨4472612, by rfl⟩ : syracuseStep 5963483 = 8945225) B8945225
theorem B3975655 : Blo 2093435 3975655 := bstep (se 1 (by rfl) ⟨2981741, by rfl⟩ : syracuseStep 3975655 = 5963483) B5963483
theorem B5300873 : Blo 2093435 5300873 := bstep (se 2 (by rfl) ⟨1987827, by rfl⟩ : syracuseStep 5300873 = 3975655) B3975655
theorem B3533915 : Blo 2093435 3533915 := bstep (se 1 (by rfl) ⟨2650436, by rfl⟩ : syracuseStep 3533915 = 5300873) B5300873
theorem B2355943 : Blo 2093435 2355943 := bstep (se 1 (by rfl) ⟨1766957, by rfl⟩ : syracuseStep 2355943 = 3533915) B3533915
theorem B3141257 : Blo 2093435 3141257 := bstep (se 2 (by rfl) ⟨1177971, by rfl⟩ : syracuseStep 3141257 = 2355943) B2355943
theorem B2094171 : Blo 2093435 2094171 := bstep (se 1 (by rfl) ⟨1570628, by rfl⟩ : syracuseStep 2094171 = 3141257) B3141257
theorem B10601765 : Blo 2093435 10601765 := bbase (se 4 (by rfl) ⟨993915, by rfl⟩ : syracuseStep 10601765 = 1987831) (by norm_num)
theorem B7067843 : Blo 2093435 7067843 := bstep (se 1 (by rfl) ⟨5300882, by rfl⟩ : syracuseStep 7067843 = 10601765) B10601765
theorem B4711895 : Blo 2093435 4711895 := bstep (se 1 (by rfl) ⟨3533921, by rfl⟩ : syracuseStep 4711895 = 7067843) B7067843
theorem B3141263 : Blo 2093435 3141263 := bstep (se 1 (by rfl) ⟨2355947, by rfl⟩ : syracuseStep 3141263 = 4711895) B4711895
theorem B2094175 : Blo 2093435 2094175 := bstep (se 1 (by rfl) ⟨1570631, by rfl⟩ : syracuseStep 2094175 = 3141263) B3141263
theorem B3141269 : Blo 2093435 3141269 := bbase (se 6 (by rfl) ⟨73623, by rfl⟩ : syracuseStep 3141269 = 147247) (by norm_num)
theorem B2094179 : Blo 2093435 2094179 := bstep (se 1 (by rfl) ⟨1570634, by rfl⟩ : syracuseStep 2094179 = 3141269) B3141269
theorem B11321365 : Blo 2093435 11321365 := bbase (se 6 (by rfl) ⟨265344, by rfl⟩ : syracuseStep 11321365 = 530689) (by norm_num)
theorem B15095153 : Blo 2093435 15095153 := bstep (se 2 (by rfl) ⟨5660682, by rfl⟩ : syracuseStep 15095153 = 11321365) B11321365
theorem B10063435 : Blo 2093435 10063435 := bstep (se 1 (by rfl) ⟨7547576, by rfl⟩ : syracuseStep 10063435 = 15095153) B15095153
theorem B13417913 : Blo 2093435 13417913 := bstep (se 2 (by rfl) ⟨5031717, by rfl⟩ : syracuseStep 13417913 = 10063435) B10063435
theorem B8945275 : Blo 2093435 8945275 := bstep (se 1 (by rfl) ⟨6708956, by rfl⟩ : syracuseStep 8945275 = 13417913) B13417913
theorem B11927033 : Blo 2093435 11927033 := bstep (se 2 (by rfl) ⟨4472637, by rfl⟩ : syracuseStep 11927033 = 8945275) B8945275
theorem B7951355 : Blo 2093435 7951355 := bstep (se 1 (by rfl) ⟨5963516, by rfl⟩ : syracuseStep 7951355 = 11927033) B11927033
theorem B5300903 : Blo 2093435 5300903 := bstep (se 1 (by rfl) ⟨3975677, by rfl⟩ : syracuseStep 5300903 = 7951355) B7951355
theorem B3533935 : Blo 2093435 3533935 := bstep (se 1 (by rfl) ⟨2650451, by rfl⟩ : syracuseStep 3533935 = 5300903) B5300903
theorem B4711913 : Blo 2093435 4711913 := bstep (se 2 (by rfl) ⟨1766967, by rfl⟩ : syracuseStep 4711913 = 3533935) B3533935
theorem B3141275 : Blo 2093435 3141275 := bstep (se 1 (by rfl) ⟨2355956, by rfl⟩ : syracuseStep 3141275 = 4711913) B4711913
theorem B2094183 : Blo 2093435 2094183 := bstep (se 1 (by rfl) ⟨1570637, by rfl⟩ : syracuseStep 2094183 = 3141275) B3141275
theorem B2355961 : Blo 2093435 2355961 := bbase (se 2 (by rfl) ⟨883485, by rfl⟩ : syracuseStep 2355961 = 1766971) (by norm_num)
theorem B3141281 : Blo 2093435 3141281 := bstep (se 2 (by rfl) ⟨1177980, by rfl⟩ : syracuseStep 3141281 = 2355961) B2355961
theorem B2094187 : Blo 2093435 2094187 := bstep (se 1 (by rfl) ⟨1570640, by rfl⟩ : syracuseStep 2094187 = 3141281) B3141281
theorem B4776221 : Blo 2093435 4776221 := bbase (se 3 (by rfl) ⟨895541, by rfl⟩ : syracuseStep 4776221 = 1791083) (by norm_num)
theorem B3184147 : Blo 2093435 3184147 := bstep (se 1 (by rfl) ⟨2388110, by rfl⟩ : syracuseStep 3184147 = 4776221) B4776221
theorem B4245529 : Blo 2093435 4245529 := bstep (se 2 (by rfl) ⟨1592073, by rfl⟩ : syracuseStep 4245529 = 3184147) B3184147
theorem B5660705 : Blo 2093435 5660705 := bstep (se 2 (by rfl) ⟨2122764, by rfl⟩ : syracuseStep 5660705 = 4245529) B4245529
theorem B3773803 : Blo 2093435 3773803 := bstep (se 1 (by rfl) ⟨2830352, by rfl⟩ : syracuseStep 3773803 = 5660705) B5660705
theorem B5031737 : Blo 2093435 5031737 := bstep (se 2 (by rfl) ⟨1886901, by rfl⟩ : syracuseStep 5031737 = 3773803) B3773803
theorem B3354491 : Blo 2093435 3354491 := bstep (se 1 (by rfl) ⟨2515868, by rfl⟩ : syracuseStep 3354491 = 5031737) B5031737
theorem B8945309 : Blo 2093435 8945309 := bstep (se 3 (by rfl) ⟨1677245, by rfl⟩ : syracuseStep 8945309 = 3354491) B3354491
theorem B5963539 : Blo 2093435 5963539 := bstep (se 1 (by rfl) ⟨4472654, by rfl⟩ : syracuseStep 5963539 = 8945309) B8945309
theorem B7951385 : Blo 2093435 7951385 := bstep (se 2 (by rfl) ⟨2981769, by rfl⟩ : syracuseStep 7951385 = 5963539) B5963539
theorem B5300923 : Blo 2093435 5300923 := bstep (se 1 (by rfl) ⟨3975692, by rfl⟩ : syracuseStep 5300923 = 7951385) B7951385
theorem B7067897 : Blo 2093435 7067897 := bstep (se 2 (by rfl) ⟨2650461, by rfl⟩ : syracuseStep 7067897 = 5300923) B5300923
theorem B4711931 : Blo 2093435 4711931 := bstep (se 1 (by rfl) ⟨3533948, by rfl⟩ : syracuseStep 4711931 = 7067897) B7067897
theorem B3141287 : Blo 2093435 3141287 := bstep (se 1 (by rfl) ⟨2355965, by rfl⟩ : syracuseStep 3141287 = 4711931) B4711931
theorem B2094191 : Blo 2093435 2094191 := bstep (se 1 (by rfl) ⟨1570643, by rfl⟩ : syracuseStep 2094191 = 3141287) B3141287
theorem B3141293 : Blo 2093435 3141293 := bbase (se 3 (by rfl) ⟨588992, by rfl⟩ : syracuseStep 3141293 = 1177985) (by norm_num)
theorem B2094195 : Blo 2093435 2094195 := bstep (se 1 (by rfl) ⟨1570646, by rfl⟩ : syracuseStep 2094195 = 3141293) B3141293
theorem B4711949 : Blo 2093435 4711949 := bbase (se 3 (by rfl) ⟨883490, by rfl⟩ : syracuseStep 4711949 = 1766981) (by norm_num)
theorem B3141299 : Blo 2093435 3141299 := bstep (se 1 (by rfl) ⟨2355974, by rfl⟩ : syracuseStep 3141299 = 4711949) B4711949
theorem B2094199 : Blo 2093435 2094199 := bstep (se 1 (by rfl) ⟨1570649, by rfl⟩ : syracuseStep 2094199 = 3141299) B3141299
theorem B2650477 : Blo 2093435 2650477 := bbase (se 3 (by rfl) ⟨496964, by rfl⟩ : syracuseStep 2650477 = 993929) (by norm_num)
theorem B3533969 : Blo 2093435 3533969 := bstep (se 2 (by rfl) ⟨1325238, by rfl⟩ : syracuseStep 3533969 = 2650477) B2650477
theorem B2355979 : Blo 2093435 2355979 := bstep (se 1 (by rfl) ⟨1766984, by rfl⟩ : syracuseStep 2355979 = 3533969) B3533969
theorem B3141305 : Blo 2093435 3141305 := bstep (se 2 (by rfl) ⟨1177989, by rfl⟩ : syracuseStep 3141305 = 2355979) B2355979
theorem B2094203 : Blo 2093435 2094203 := bstep (se 1 (by rfl) ⟨1570652, by rfl⟩ : syracuseStep 2094203 = 3141305) B3141305
theorem B6368341 : Blo 2093435 6368341 := bbase (se 8 (by rfl) ⟨37314, by rfl⟩ : syracuseStep 6368341 = 74629) (by norm_num)
theorem B8491121 : Blo 2093435 8491121 := bstep (se 2 (by rfl) ⟨3184170, by rfl⟩ : syracuseStep 8491121 = 6368341) B6368341
theorem B5660747 : Blo 2093435 5660747 := bstep (se 1 (by rfl) ⟨4245560, by rfl⟩ : syracuseStep 5660747 = 8491121) B8491121
theorem B3773831 : Blo 2093435 3773831 := bstep (se 1 (by rfl) ⟨2830373, by rfl⟩ : syracuseStep 3773831 = 5660747) B5660747
theorem B10063549 : Blo 2093435 10063549 := bstep (se 3 (by rfl) ⟨1886915, by rfl⟩ : syracuseStep 10063549 = 3773831) B3773831
theorem B13418065 : Blo 2093435 13418065 := bstep (se 2 (by rfl) ⟨5031774, by rfl⟩ : syracuseStep 13418065 = 10063549) B10063549
theorem B17890753 : Blo 2093435 17890753 := bstep (se 2 (by rfl) ⟨6709032, by rfl⟩ : syracuseStep 17890753 = 13418065) B13418065
theorem B23854337 : Blo 2093435 23854337 := bstep (se 2 (by rfl) ⟨8945376, by rfl⟩ : syracuseStep 23854337 = 17890753) B17890753
theorem B15902891 : Blo 2093435 15902891 := bstep (se 1 (by rfl) ⟨11927168, by rfl⟩ : syracuseStep 15902891 = 23854337) B23854337
theorem B10601927 : Blo 2093435 10601927 := bstep (se 1 (by rfl) ⟨7951445, by rfl⟩ : syracuseStep 10601927 = 15902891) B15902891
theorem B7067951 : Blo 2093435 7067951 := bstep (se 1 (by rfl) ⟨5300963, by rfl⟩ : syracuseStep 7067951 = 10601927) B10601927
theorem B4711967 : Blo 2093435 4711967 := bstep (se 1 (by rfl) ⟨3533975, by rfl⟩ : syracuseStep 4711967 = 7067951) B7067951
theorem B3141311 : Blo 2093435 3141311 := bstep (se 1 (by rfl) ⟨2355983, by rfl⟩ : syracuseStep 3141311 = 4711967) B4711967
theorem B2094207 : Blo 2093435 2094207 := bstep (se 1 (by rfl) ⟨1570655, by rfl⟩ : syracuseStep 2094207 = 3141311) B3141311
theorem B3141317 : Blo 2093435 3141317 := bbase (se 4 (by rfl) ⟨294498, by rfl⟩ : syracuseStep 3141317 = 588997) (by norm_num)
theorem B2094211 : Blo 2093435 2094211 := bstep (se 1 (by rfl) ⟨1570658, by rfl⟩ : syracuseStep 2094211 = 3141317) B3141317
theorem B3533989 : Blo 2093435 3533989 := bbase (se 4 (by rfl) ⟨331311, by rfl⟩ : syracuseStep 3533989 = 662623) (by norm_num)
theorem B4711985 : Blo 2093435 4711985 := bstep (se 2 (by rfl) ⟨1766994, by rfl⟩ : syracuseStep 4711985 = 3533989) B3533989
theorem B3141323 : Blo 2093435 3141323 := bstep (se 1 (by rfl) ⟨2355992, by rfl⟩ : syracuseStep 3141323 = 4711985) B4711985
theorem B2094215 : Blo 2093435 2094215 := bstep (se 1 (by rfl) ⟨1570661, by rfl⟩ : syracuseStep 2094215 = 3141323) B3141323
theorem B2355997 : Blo 2093435 2355997 := bbase (se 3 (by rfl) ⟨441749, by rfl⟩ : syracuseStep 2355997 = 883499) (by norm_num)
theorem B3141329 : Blo 2093435 3141329 := bstep (se 2 (by rfl) ⟨1177998, by rfl⟩ : syracuseStep 3141329 = 2355997) B2355997
theorem B2094219 : Blo 2093435 2094219 := bstep (se 1 (by rfl) ⟨1570664, by rfl⟩ : syracuseStep 2094219 = 3141329) B3141329
theorem B7068005 : Blo 2093435 7068005 := bbase (se 4 (by rfl) ⟨662625, by rfl⟩ : syracuseStep 7068005 = 1325251) (by norm_num)
theorem B4712003 : Blo 2093435 4712003 := bstep (se 1 (by rfl) ⟨3534002, by rfl⟩ : syracuseStep 4712003 = 7068005) B7068005
theorem B3141335 : Blo 2093435 3141335 := bstep (se 1 (by rfl) ⟨2356001, by rfl⟩ : syracuseStep 3141335 = 4712003) B4712003
theorem B2094223 : Blo 2093435 2094223 := bstep (se 1 (by rfl) ⟨1570667, by rfl⟩ : syracuseStep 2094223 = 3141335) B3141335
theorem B3141341 : Blo 2093435 3141341 := bbase (se 3 (by rfl) ⟨589001, by rfl⟩ : syracuseStep 3141341 = 1178003) (by norm_num)
theorem B2094227 : Blo 2093435 2094227 := bstep (se 1 (by rfl) ⟨1570670, by rfl⟩ : syracuseStep 2094227 = 3141341) B3141341
theorem B4712021 : Blo 2093435 4712021 := bbase (se 8 (by rfl) ⟨27609, by rfl⟩ : syracuseStep 4712021 = 55219) (by norm_num)
theorem B3141347 : Blo 2093435 3141347 := bstep (se 1 (by rfl) ⟨2356010, by rfl⟩ : syracuseStep 3141347 = 4712021) B4712021
theorem B2094231 : Blo 2093435 2094231 := bstep (se 1 (by rfl) ⟨1570673, by rfl⟩ : syracuseStep 2094231 = 3141347) B3141347
theorem B4472749 : Blo 2093435 4472749 := bbase (se 3 (by rfl) ⟨838640, by rfl⟩ : syracuseStep 4472749 = 1677281) (by norm_num)
theorem B5963665 : Blo 2093435 5963665 := bstep (se 2 (by rfl) ⟨2236374, by rfl⟩ : syracuseStep 5963665 = 4472749) B4472749
theorem B7951553 : Blo 2093435 7951553 := bstep (se 2 (by rfl) ⟨2981832, by rfl⟩ : syracuseStep 7951553 = 5963665) B5963665
theorem B5301035 : Blo 2093435 5301035 := bstep (se 1 (by rfl) ⟨3975776, by rfl⟩ : syracuseStep 5301035 = 7951553) B7951553
theorem B3534023 : Blo 2093435 3534023 := bstep (se 1 (by rfl) ⟨2650517, by rfl⟩ : syracuseStep 3534023 = 5301035) B5301035
theorem B2356015 : Blo 2093435 2356015 := bstep (se 1 (by rfl) ⟨1767011, by rfl⟩ : syracuseStep 2356015 = 3534023) B3534023
theorem B3141353 : Blo 2093435 3141353 := bstep (se 2 (by rfl) ⟨1178007, by rfl⟩ : syracuseStep 3141353 = 2356015) B2356015
theorem B2094235 : Blo 2093435 2094235 := bstep (se 1 (by rfl) ⟨1570676, by rfl⟩ : syracuseStep 2094235 = 3141353) B3141353
theorem B2550253 : Blo 2093435 2550253 := bbase (se 3 (by rfl) ⟨478172, by rfl⟩ : syracuseStep 2550253 = 956345) (by norm_num)
theorem B3400337 : Blo 2093435 3400337 := bstep (se 2 (by rfl) ⟨1275126, by rfl⟩ : syracuseStep 3400337 = 2550253) B2550253
theorem B9067565 : Blo 2093435 9067565 := bstep (se 3 (by rfl) ⟨1700168, by rfl⟩ : syracuseStep 9067565 = 3400337) B3400337
theorem B6045043 : Blo 2093435 6045043 := bstep (se 1 (by rfl) ⟨4533782, by rfl⟩ : syracuseStep 6045043 = 9067565) B9067565
theorem B8060057 : Blo 2093435 8060057 := bstep (se 2 (by rfl) ⟨3022521, by rfl⟩ : syracuseStep 8060057 = 6045043) B6045043
theorem B5373371 : Blo 2093435 5373371 := bstep (se 1 (by rfl) ⟨4030028, by rfl⟩ : syracuseStep 5373371 = 8060057) B8060057
theorem B3582247 : Blo 2093435 3582247 := bstep (se 1 (by rfl) ⟨2686685, by rfl⟩ : syracuseStep 3582247 = 5373371) B5373371
theorem B4776329 : Blo 2093435 4776329 := bstep (se 2 (by rfl) ⟨1791123, by rfl⟩ : syracuseStep 4776329 = 3582247) B3582247
theorem B3184219 : Blo 2093435 3184219 := bstep (se 1 (by rfl) ⟨2388164, by rfl⟩ : syracuseStep 3184219 = 4776329) B4776329
theorem B4245625 : Blo 2093435 4245625 := bstep (se 2 (by rfl) ⟨1592109, by rfl⟩ : syracuseStep 4245625 = 3184219) B3184219
theorem B22643333 : Blo 2093435 22643333 := bstep (se 4 (by rfl) ⟨2122812, by rfl⟩ : syracuseStep 22643333 = 4245625) B4245625
theorem B15095555 : Blo 2093435 15095555 := bstep (se 1 (by rfl) ⟨11321666, by rfl⟩ : syracuseStep 15095555 = 22643333) B22643333
theorem B10063703 : Blo 2093435 10063703 := bstep (se 1 (by rfl) ⟨7547777, by rfl⟩ : syracuseStep 10063703 = 15095555) B15095555
theorem B26836541 : Blo 2093435 26836541 := bstep (se 3 (by rfl) ⟨5031851, by rfl⟩ : syracuseStep 26836541 = 10063703) B10063703
theorem B17891027 : Blo 2093435 17891027 := bstep (se 1 (by rfl) ⟨13418270, by rfl⟩ : syracuseStep 17891027 = 26836541) B26836541
theorem B11927351 : Blo 2093435 11927351 := bstep (se 1 (by rfl) ⟨8945513, by rfl⟩ : syracuseStep 11927351 = 17891027) B17891027
theorem B7951567 : Blo 2093435 7951567 := bstep (se 1 (by rfl) ⟨5963675, by rfl⟩ : syracuseStep 7951567 = 11927351) B11927351
theorem B10602089 : Blo 2093435 10602089 := bstep (se 2 (by rfl) ⟨3975783, by rfl⟩ : syracuseStep 10602089 = 7951567) B7951567
theorem B7068059 : Blo 2093435 7068059 := bstep (se 1 (by rfl) ⟨5301044, by rfl⟩ : syracuseStep 7068059 = 10602089) B10602089
theorem B4712039 : Blo 2093435 4712039 := bstep (se 1 (by rfl) ⟨3534029, by rfl⟩ : syracuseStep 4712039 = 7068059) B7068059
theorem B3141359 : Blo 2093435 3141359 := bstep (se 1 (by rfl) ⟨2356019, by rfl⟩ : syracuseStep 3141359 = 4712039) B4712039
theorem B2094239 : Blo 2093435 2094239 := bstep (se 1 (by rfl) ⟨1570679, by rfl⟩ : syracuseStep 2094239 = 3141359) B3141359
theorem B3141365 : Blo 2093435 3141365 := bbase (se 5 (by rfl) ⟨147251, by rfl⟩ : syracuseStep 3141365 = 294503) (by norm_num)
theorem B2094243 : Blo 2093435 2094243 := bstep (se 1 (by rfl) ⟨1570682, by rfl⟩ : syracuseStep 2094243 = 3141365) B3141365
theorem B3354581 : Blo 2093435 3354581 := bbase (se 7 (by rfl) ⟨39311, by rfl⟩ : syracuseStep 3354581 = 78623) (by norm_num)
theorem B8945549 : Blo 2093435 8945549 := bstep (se 3 (by rfl) ⟨1677290, by rfl⟩ : syracuseStep 8945549 = 3354581) B3354581
theorem B5963699 : Blo 2093435 5963699 := bstep (se 1 (by rfl) ⟨4472774, by rfl⟩ : syracuseStep 5963699 = 8945549) B8945549
theorem B3975799 : Blo 2093435 3975799 := bstep (se 1 (by rfl) ⟨2981849, by rfl⟩ : syracuseStep 3975799 = 5963699) B5963699
theorem B5301065 : Blo 2093435 5301065 := bstep (se 2 (by rfl) ⟨1987899, by rfl⟩ : syracuseStep 5301065 = 3975799) B3975799
theorem B3534043 : Blo 2093435 3534043 := bstep (se 1 (by rfl) ⟨2650532, by rfl⟩ : syracuseStep 3534043 = 5301065) B5301065
theorem B4712057 : Blo 2093435 4712057 := bstep (se 2 (by rfl) ⟨1767021, by rfl⟩ : syracuseStep 4712057 = 3534043) B3534043
theorem B3141371 : Blo 2093435 3141371 := bstep (se 1 (by rfl) ⟨2356028, by rfl⟩ : syracuseStep 3141371 = 4712057) B4712057
theorem B2094247 : Blo 2093435 2094247 := bstep (se 1 (by rfl) ⟨1570685, by rfl⟩ : syracuseStep 2094247 = 3141371) B3141371
theorem B2356033 : Blo 2093435 2356033 := bbase (se 2 (by rfl) ⟨883512, by rfl⟩ : syracuseStep 2356033 = 1767025) (by norm_num)
theorem B3141377 : Blo 2093435 3141377 := bstep (se 2 (by rfl) ⟨1178016, by rfl⟩ : syracuseStep 3141377 = 2356033) B2356033
theorem B2094251 : Blo 2093435 2094251 := bstep (se 1 (by rfl) ⟨1570688, by rfl⟩ : syracuseStep 2094251 = 3141377) B3141377
theorem B5301085 : Blo 2093435 5301085 := bbase (se 3 (by rfl) ⟨993953, by rfl⟩ : syracuseStep 5301085 = 1987907) (by norm_num)
theorem B7068113 : Blo 2093435 7068113 := bstep (se 2 (by rfl) ⟨2650542, by rfl⟩ : syracuseStep 7068113 = 5301085) B5301085
theorem B4712075 : Blo 2093435 4712075 := bstep (se 1 (by rfl) ⟨3534056, by rfl⟩ : syracuseStep 4712075 = 7068113) B7068113
theorem B3141383 : Blo 2093435 3141383 := bstep (se 1 (by rfl) ⟨2356037, by rfl⟩ : syracuseStep 3141383 = 4712075) B4712075
theorem B2094255 : Blo 2093435 2094255 := bstep (se 1 (by rfl) ⟨1570691, by rfl⟩ : syracuseStep 2094255 = 3141383) B3141383
theorem B3141389 : Blo 2093435 3141389 := bbase (se 3 (by rfl) ⟨589010, by rfl⟩ : syracuseStep 3141389 = 1178021) (by norm_num)
theorem B2094259 : Blo 2093435 2094259 := bstep (se 1 (by rfl) ⟨1570694, by rfl⟩ : syracuseStep 2094259 = 3141389) B3141389
theorem B4712093 : Blo 2093435 4712093 := bbase (se 3 (by rfl) ⟨883517, by rfl⟩ : syracuseStep 4712093 = 1767035) (by norm_num)
theorem B3141395 : Blo 2093435 3141395 := bstep (se 1 (by rfl) ⟨2356046, by rfl⟩ : syracuseStep 3141395 = 4712093) B4712093
theorem B2094263 : Blo 2093435 2094263 := bstep (se 1 (by rfl) ⟨1570697, by rfl⟩ : syracuseStep 2094263 = 3141395) B3141395
theorem B3534077 : Blo 2093435 3534077 := bbase (se 3 (by rfl) ⟨662639, by rfl⟩ : syracuseStep 3534077 = 1325279) (by norm_num)
theorem B2356051 : Blo 2093435 2356051 := bstep (se 1 (by rfl) ⟨1767038, by rfl⟩ : syracuseStep 2356051 = 3534077) B3534077
theorem B3141401 : Blo 2093435 3141401 := bstep (se 2 (by rfl) ⟨1178025, by rfl⟩ : syracuseStep 3141401 = 2356051) B2356051
theorem B2094267 : Blo 2093435 2094267 := bstep (se 1 (by rfl) ⟨1570700, by rfl⟩ : syracuseStep 2094267 = 3141401) B3141401
theorem B4533853 : Blo 2093435 4533853 := bbase (se 3 (by rfl) ⟨850097, by rfl⟩ : syracuseStep 4533853 = 1700195) (by norm_num)
theorem B6045137 : Blo 2093435 6045137 := bstep (se 2 (by rfl) ⟨2266926, by rfl⟩ : syracuseStep 6045137 = 4533853) B4533853
theorem B4030091 : Blo 2093435 4030091 := bstep (se 1 (by rfl) ⟨3022568, by rfl⟩ : syracuseStep 4030091 = 6045137) B6045137
theorem B2686727 : Blo 2093435 2686727 := bstep (se 1 (by rfl) ⟨2015045, by rfl⟩ : syracuseStep 2686727 = 4030091) B4030091
theorem B7164605 : Blo 2093435 7164605 := bstep (se 3 (by rfl) ⟨1343363, by rfl⟩ : syracuseStep 7164605 = 2686727) B2686727
theorem B4776403 : Blo 2093435 4776403 := bstep (se 1 (by rfl) ⟨3582302, by rfl⟩ : syracuseStep 4776403 = 7164605) B7164605
theorem B6368537 : Blo 2093435 6368537 := bstep (se 2 (by rfl) ⟨2388201, by rfl⟩ : syracuseStep 6368537 = 4776403) B4776403
theorem B4245691 : Blo 2093435 4245691 := bstep (se 1 (by rfl) ⟨3184268, by rfl⟩ : syracuseStep 4245691 = 6368537) B6368537
theorem B5660921 : Blo 2093435 5660921 := bstep (se 2 (by rfl) ⟨2122845, by rfl⟩ : syracuseStep 5660921 = 4245691) B4245691
theorem B3773947 : Blo 2093435 3773947 := bstep (se 1 (by rfl) ⟨2830460, by rfl⟩ : syracuseStep 3773947 = 5660921) B5660921
theorem B5031929 : Blo 2093435 5031929 := bstep (se 2 (by rfl) ⟨1886973, by rfl⟩ : syracuseStep 5031929 = 3773947) B3773947
theorem B3354619 : Blo 2093435 3354619 := bstep (se 1 (by rfl) ⟨2515964, by rfl⟩ : syracuseStep 3354619 = 5031929) B5031929
theorem B4472825 : Blo 2093435 4472825 := bstep (se 2 (by rfl) ⟨1677309, by rfl⟩ : syracuseStep 4472825 = 3354619) B3354619
theorem B11927533 : Blo 2093435 11927533 := bstep (se 3 (by rfl) ⟨2236412, by rfl⟩ : syracuseStep 11927533 = 4472825) B4472825
theorem B15903377 : Blo 2093435 15903377 := bstep (se 2 (by rfl) ⟨5963766, by rfl⟩ : syracuseStep 15903377 = 11927533) B11927533
theorem B10602251 : Blo 2093435 10602251 := bstep (se 1 (by rfl) ⟨7951688, by rfl⟩ : syracuseStep 10602251 = 15903377) B15903377
theorem B7068167 : Blo 2093435 7068167 := bstep (se 1 (by rfl) ⟨5301125, by rfl⟩ : syracuseStep 7068167 = 10602251) B10602251
theorem B4712111 : Blo 2093435 4712111 := bstep (se 1 (by rfl) ⟨3534083, by rfl⟩ : syracuseStep 4712111 = 7068167) B7068167
theorem B3141407 : Blo 2093435 3141407 := bstep (se 1 (by rfl) ⟨2356055, by rfl⟩ : syracuseStep 3141407 = 4712111) B4712111
theorem B2094271 : Blo 2093435 2094271 := bstep (se 1 (by rfl) ⟨1570703, by rfl⟩ : syracuseStep 2094271 = 3141407) B3141407
theorem B3141413 : Blo 2093435 3141413 := bbase (se 4 (by rfl) ⟨294507, by rfl⟩ : syracuseStep 3141413 = 589015) (by norm_num)
theorem B2094275 : Blo 2093435 2094275 := bstep (se 1 (by rfl) ⟨1570706, by rfl⟩ : syracuseStep 2094275 = 3141413) B3141413
theorem B2650573 : Blo 2093435 2650573 := bbase (se 3 (by rfl) ⟨496982, by rfl⟩ : syracuseStep 2650573 = 993965) (by norm_num)
theorem B3534097 : Blo 2093435 3534097 := bstep (se 2 (by rfl) ⟨1325286, by rfl⟩ : syracuseStep 3534097 = 2650573) B2650573
theorem B4712129 : Blo 2093435 4712129 := bstep (se 2 (by rfl) ⟨1767048, by rfl⟩ : syracuseStep 4712129 = 3534097) B3534097
theorem B3141419 : Blo 2093435 3141419 := bstep (se 1 (by rfl) ⟨2356064, by rfl⟩ : syracuseStep 3141419 = 4712129) B4712129
theorem B2094279 : Blo 2093435 2094279 := bstep (se 1 (by rfl) ⟨1570709, by rfl⟩ : syracuseStep 2094279 = 3141419) B3141419
theorem B2356069 : Blo 2093435 2356069 := bbase (se 4 (by rfl) ⟨220881, by rfl⟩ : syracuseStep 2356069 = 441763) (by norm_num)
theorem B3141425 : Blo 2093435 3141425 := bstep (se 2 (by rfl) ⟨1178034, by rfl⟩ : syracuseStep 3141425 = 2356069) B2356069
theorem B2094283 : Blo 2093435 2094283 := bstep (se 1 (by rfl) ⟨1570712, by rfl⟩ : syracuseStep 2094283 = 3141425) B3141425
theorem B5963813 : Blo 2093435 5963813 := bbase (se 4 (by rfl) ⟨559107, by rfl⟩ : syracuseStep 5963813 = 1118215) (by norm_num)
theorem B3975875 : Blo 2093435 3975875 := bstep (se 1 (by rfl) ⟨2981906, by rfl⟩ : syracuseStep 3975875 = 5963813) B5963813
theorem B2650583 : Blo 2093435 2650583 := bstep (se 1 (by rfl) ⟨1987937, by rfl⟩ : syracuseStep 2650583 = 3975875) B3975875
theorem B7068221 : Blo 2093435 7068221 := bstep (se 3 (by rfl) ⟨1325291, by rfl⟩ : syracuseStep 7068221 = 2650583) B2650583
theorem B4712147 : Blo 2093435 4712147 := bstep (se 1 (by rfl) ⟨3534110, by rfl⟩ : syracuseStep 4712147 = 7068221) B7068221
theorem B3141431 : Blo 2093435 3141431 := bstep (se 1 (by rfl) ⟨2356073, by rfl⟩ : syracuseStep 3141431 = 4712147) B4712147
theorem B2094287 : Blo 2093435 2094287 := bstep (se 1 (by rfl) ⟨1570715, by rfl⟩ : syracuseStep 2094287 = 3141431) B3141431
theorem B3141437 : Blo 2093435 3141437 := bbase (se 3 (by rfl) ⟨589019, by rfl⟩ : syracuseStep 3141437 = 1178039) (by norm_num)
theorem B2094291 : Blo 2093435 2094291 := bstep (se 1 (by rfl) ⟨1570718, by rfl⟩ : syracuseStep 2094291 = 3141437) B3141437
theorem B4712165 : Blo 2093435 4712165 := bbase (se 4 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 4712165 = 883531) (by norm_num)
theorem B3141443 : Blo 2093435 3141443 := bstep (se 1 (by rfl) ⟨2356082, by rfl⟩ : syracuseStep 3141443 = 4712165) B4712165
theorem B2094295 : Blo 2093435 2094295 := bstep (se 1 (by rfl) ⟨1570721, by rfl⟩ : syracuseStep 2094295 = 3141443) B3141443
theorem B5301197 : Blo 2093435 5301197 := bbase (se 3 (by rfl) ⟨993974, by rfl⟩ : syracuseStep 5301197 = 1987949) (by norm_num)
theorem B3534131 : Blo 2093435 3534131 := bstep (se 1 (by rfl) ⟨2650598, by rfl⟩ : syracuseStep 3534131 = 5301197) B5301197
theorem B2356087 : Blo 2093435 2356087 := bstep (se 1 (by rfl) ⟨1767065, by rfl⟩ : syracuseStep 2356087 = 3534131) B3534131
theorem B3141449 : Blo 2093435 3141449 := bstep (se 2 (by rfl) ⟨1178043, by rfl⟩ : syracuseStep 3141449 = 2356087) B2356087
theorem B2094299 : Blo 2093435 2094299 := bstep (se 1 (by rfl) ⟨1570724, by rfl⟩ : syracuseStep 2094299 = 3141449) B3141449
theorem B2266961 : Blo 2093435 2266961 := bbase (se 2 (by rfl) ⟨850110, by rfl⟩ : syracuseStep 2266961 = 1700221) (by norm_num)
theorem B6045229 : Blo 2093435 6045229 := bstep (se 3 (by rfl) ⟨1133480, by rfl⟩ : syracuseStep 6045229 = 2266961) B2266961
theorem B8060305 : Blo 2093435 8060305 := bstep (se 2 (by rfl) ⟨3022614, by rfl⟩ : syracuseStep 8060305 = 6045229) B6045229
theorem B10747073 : Blo 2093435 10747073 := bstep (se 2 (by rfl) ⟨4030152, by rfl⟩ : syracuseStep 10747073 = 8060305) B8060305
theorem B7164715 : Blo 2093435 7164715 := bstep (se 1 (by rfl) ⟨5373536, by rfl⟩ : syracuseStep 7164715 = 10747073) B10747073
theorem B9552953 : Blo 2093435 9552953 := bstep (se 2 (by rfl) ⟨3582357, by rfl⟩ : syracuseStep 9552953 = 7164715) B7164715
theorem B6368635 : Blo 2093435 6368635 := bstep (se 1 (by rfl) ⟨4776476, by rfl⟩ : syracuseStep 6368635 = 9552953) B9552953
theorem B8491513 : Blo 2093435 8491513 := bstep (se 2 (by rfl) ⟨3184317, by rfl⟩ : syracuseStep 8491513 = 6368635) B6368635
theorem B11322017 : Blo 2093435 11322017 := bstep (se 2 (by rfl) ⟨4245756, by rfl⟩ : syracuseStep 11322017 = 8491513) B8491513
theorem B7548011 : Blo 2093435 7548011 := bstep (se 1 (by rfl) ⟨5661008, by rfl⟩ : syracuseStep 7548011 = 11322017) B11322017
theorem B5032007 : Blo 2093435 5032007 := bstep (se 1 (by rfl) ⟨3774005, by rfl⟩ : syracuseStep 5032007 = 7548011) B7548011
theorem B3354671 : Blo 2093435 3354671 := bstep (se 1 (by rfl) ⟨2516003, by rfl⟩ : syracuseStep 3354671 = 5032007) B5032007
theorem B2236447 : Blo 2093435 2236447 := bstep (se 1 (by rfl) ⟨1677335, by rfl⟩ : syracuseStep 2236447 = 3354671) B3354671
theorem B2981929 : Blo 2093435 2981929 := bstep (se 2 (by rfl) ⟨1118223, by rfl⟩ : syracuseStep 2981929 = 2236447) B2236447
theorem B3975905 : Blo 2093435 3975905 := bstep (se 2 (by rfl) ⟨1490964, by rfl⟩ : syracuseStep 3975905 = 2981929) B2981929
theorem B10602413 : Blo 2093435 10602413 := bstep (se 3 (by rfl) ⟨1987952, by rfl⟩ : syracuseStep 10602413 = 3975905) B3975905
theorem B7068275 : Blo 2093435 7068275 := bstep (se 1 (by rfl) ⟨5301206, by rfl⟩ : syracuseStep 7068275 = 10602413) B10602413
theorem B4712183 : Blo 2093435 4712183 := bstep (se 1 (by rfl) ⟨3534137, by rfl⟩ : syracuseStep 4712183 = 7068275) B7068275
theorem B3141455 : Blo 2093435 3141455 := bstep (se 1 (by rfl) ⟨2356091, by rfl⟩ : syracuseStep 3141455 = 4712183) B4712183
theorem B2094303 : Blo 2093435 2094303 := bstep (se 1 (by rfl) ⟨1570727, by rfl⟩ : syracuseStep 2094303 = 3141455) B3141455
theorem B3141461 : Blo 2093435 3141461 := bbase (se 9 (by rfl) ⟨9203, by rfl⟩ : syracuseStep 3141461 = 18407) (by norm_num)
theorem B2094307 : Blo 2093435 2094307 := bstep (se 1 (by rfl) ⟨1570730, by rfl⟩ : syracuseStep 2094307 = 3141461) B3141461
theorem B5661029 : Blo 2093435 5661029 := bbase (se 4 (by rfl) ⟨530721, by rfl⟩ : syracuseStep 5661029 = 1061443) (by norm_num)
theorem B15096077 : Blo 2093435 15096077 := bstep (se 3 (by rfl) ⟨2830514, by rfl⟩ : syracuseStep 15096077 = 5661029) B5661029
theorem B10064051 : Blo 2093435 10064051 := bstep (se 1 (by rfl) ⟨7548038, by rfl⟩ : syracuseStep 10064051 = 15096077) B15096077
theorem B6709367 : Blo 2093435 6709367 := bstep (se 1 (by rfl) ⟨5032025, by rfl⟩ : syracuseStep 6709367 = 10064051) B10064051
theorem B4472911 : Blo 2093435 4472911 := bstep (se 1 (by rfl) ⟨3354683, by rfl⟩ : syracuseStep 4472911 = 6709367) B6709367
theorem B5963881 : Blo 2093435 5963881 := bstep (se 2 (by rfl) ⟨2236455, by rfl⟩ : syracuseStep 5963881 = 4472911) B4472911
theorem B7951841 : Blo 2093435 7951841 := bstep (se 2 (by rfl) ⟨2981940, by rfl⟩ : syracuseStep 7951841 = 5963881) B5963881
theorem B5301227 : Blo 2093435 5301227 := bstep (se 1 (by rfl) ⟨3975920, by rfl⟩ : syracuseStep 5301227 = 7951841) B7951841
theorem B3534151 : Blo 2093435 3534151 := bstep (se 1 (by rfl) ⟨2650613, by rfl⟩ : syracuseStep 3534151 = 5301227) B5301227
theorem B4712201 : Blo 2093435 4712201 := bstep (se 2 (by rfl) ⟨1767075, by rfl⟩ : syracuseStep 4712201 = 3534151) B3534151
theorem B3141467 : Blo 2093435 3141467 := bstep (se 1 (by rfl) ⟨2356100, by rfl⟩ : syracuseStep 3141467 = 4712201) B4712201
theorem B2094311 : Blo 2093435 2094311 := bstep (se 1 (by rfl) ⟨1570733, by rfl⟩ : syracuseStep 2094311 = 3141467) B3141467
theorem B2356105 : Blo 2093435 2356105 := bbase (se 2 (by rfl) ⟨883539, by rfl⟩ : syracuseStep 2356105 = 1767079) (by norm_num)
theorem B3141473 : Blo 2093435 3141473 := bstep (se 2 (by rfl) ⟨1178052, by rfl⟩ : syracuseStep 3141473 = 2356105) B2356105
theorem B2094315 : Blo 2093435 2094315 := bstep (se 1 (by rfl) ⟨1570736, by rfl⟩ : syracuseStep 2094315 = 3141473) B3141473
theorem B9067909 : Blo 2093435 9067909 := bbase (se 4 (by rfl) ⟨850116, by rfl⟩ : syracuseStep 9067909 = 1700233) (by norm_num)
theorem B12090545 : Blo 2093435 12090545 := bstep (se 2 (by rfl) ⟨4533954, by rfl⟩ : syracuseStep 12090545 = 9067909) B9067909
theorem B8060363 : Blo 2093435 8060363 := bstep (se 1 (by rfl) ⟨6045272, by rfl⟩ : syracuseStep 8060363 = 12090545) B12090545
theorem B5373575 : Blo 2093435 5373575 := bstep (se 1 (by rfl) ⟨4030181, by rfl⟩ : syracuseStep 5373575 = 8060363) B8060363
theorem B3582383 : Blo 2093435 3582383 := bstep (se 1 (by rfl) ⟨2686787, by rfl⟩ : syracuseStep 3582383 = 5373575) B5373575
theorem B9553021 : Blo 2093435 9553021 := bstep (se 3 (by rfl) ⟨1791191, by rfl⟩ : syracuseStep 9553021 = 3582383) B3582383
theorem B203797781 : Blo 2093435 203797781 := bstep (se 6 (by rfl) ⟨4776510, by rfl⟩ : syracuseStep 203797781 = 9553021) B9553021
theorem B135865187 : Blo 2093435 135865187 := bstep (se 1 (by rfl) ⟨101898890, by rfl⟩ : syracuseStep 135865187 = 203797781) B203797781
theorem B90576791 : Blo 2093435 90576791 := bstep (se 1 (by rfl) ⟨67932593, by rfl⟩ : syracuseStep 90576791 = 135865187) B135865187
theorem B60384527 : Blo 2093435 60384527 := bstep (se 1 (by rfl) ⟨45288395, by rfl⟩ : syracuseStep 60384527 = 90576791) B90576791
theorem B40256351 : Blo 2093435 40256351 := bstep (se 1 (by rfl) ⟨30192263, by rfl⟩ : syracuseStep 40256351 = 60384527) B60384527
theorem B26837567 : Blo 2093435 26837567 := bstep (se 1 (by rfl) ⟨20128175, by rfl⟩ : syracuseStep 26837567 = 40256351) B40256351
theorem B17891711 : Blo 2093435 17891711 := bstep (se 1 (by rfl) ⟨13418783, by rfl⟩ : syracuseStep 17891711 = 26837567) B26837567
theorem B11927807 : Blo 2093435 11927807 := bstep (se 1 (by rfl) ⟨8945855, by rfl⟩ : syracuseStep 11927807 = 17891711) B17891711
theorem B7951871 : Blo 2093435 7951871 := bstep (se 1 (by rfl) ⟨5963903, by rfl⟩ : syracuseStep 7951871 = 11927807) B11927807
theorem B5301247 : Blo 2093435 5301247 := bstep (se 1 (by rfl) ⟨3975935, by rfl⟩ : syracuseStep 5301247 = 7951871) B7951871
theorem B7068329 : Blo 2093435 7068329 := bstep (se 2 (by rfl) ⟨2650623, by rfl⟩ : syracuseStep 7068329 = 5301247) B5301247
theorem B4712219 : Blo 2093435 4712219 := bstep (se 1 (by rfl) ⟨3534164, by rfl⟩ : syracuseStep 4712219 = 7068329) B7068329
theorem B3141479 : Blo 2093435 3141479 := bstep (se 1 (by rfl) ⟨2356109, by rfl⟩ : syracuseStep 3141479 = 4712219) B4712219
theorem B2094319 : Blo 2093435 2094319 := bstep (se 1 (by rfl) ⟨1570739, by rfl⟩ : syracuseStep 2094319 = 3141479) B3141479
theorem B3141485 : Blo 2093435 3141485 := bbase (se 3 (by rfl) ⟨589028, by rfl⟩ : syracuseStep 3141485 = 1178057) (by norm_num)
theorem B2094323 : Blo 2093435 2094323 := bstep (se 1 (by rfl) ⟨1570742, by rfl⟩ : syracuseStep 2094323 = 3141485) B3141485
theorem B4712237 : Blo 2093435 4712237 := bbase (se 3 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 4712237 = 1767089) (by norm_num)
theorem B3141491 : Blo 2093435 3141491 := bstep (se 1 (by rfl) ⟨2356118, by rfl⟩ : syracuseStep 3141491 = 4712237) B4712237
theorem B2094327 : Blo 2093435 2094327 := bstep (se 1 (by rfl) ⟨1570745, by rfl⟩ : syracuseStep 2094327 = 3141491) B3141491
theorem B8945909 : Blo 2093435 8945909 := bbase (se 5 (by rfl) ⟨419339, by rfl⟩ : syracuseStep 8945909 = 838679) (by norm_num)
theorem B5963939 : Blo 2093435 5963939 := bstep (se 1 (by rfl) ⟨4472954, by rfl⟩ : syracuseStep 5963939 = 8945909) B8945909
theorem B3975959 : Blo 2093435 3975959 := bstep (se 1 (by rfl) ⟨2981969, by rfl⟩ : syracuseStep 3975959 = 5963939) B5963939
theorem B2650639 : Blo 2093435 2650639 := bstep (se 1 (by rfl) ⟨1987979, by rfl⟩ : syracuseStep 2650639 = 3975959) B3975959
theorem B3534185 : Blo 2093435 3534185 := bstep (se 2 (by rfl) ⟨1325319, by rfl⟩ : syracuseStep 3534185 = 2650639) B2650639
theorem B2356123 : Blo 2093435 2356123 := bstep (se 1 (by rfl) ⟨1767092, by rfl⟩ : syracuseStep 2356123 = 3534185) B3534185
theorem B3141497 : Blo 2093435 3141497 := bstep (se 2 (by rfl) ⟨1178061, by rfl⟩ : syracuseStep 3141497 = 2356123) B2356123
theorem B2094331 : Blo 2093435 2094331 := bstep (se 1 (by rfl) ⟨1570748, by rfl⟩ : syracuseStep 2094331 = 3141497) B3141497
theorem B2516041 : Blo 2093435 2516041 := bbase (se 2 (by rfl) ⟨943515, by rfl⟩ : syracuseStep 2516041 = 1887031) (by norm_num)
theorem B13418885 : Blo 2093435 13418885 := bstep (se 4 (by rfl) ⟨1258020, by rfl⟩ : syracuseStep 13418885 = 2516041) B2516041
theorem B35783693 : Blo 2093435 35783693 := bstep (se 3 (by rfl) ⟨6709442, by rfl⟩ : syracuseStep 35783693 = 13418885) B13418885
theorem B23855795 : Blo 2093435 23855795 := bstep (se 1 (by rfl) ⟨17891846, by rfl⟩ : syracuseStep 23855795 = 35783693) B35783693
theorem B15903863 : Blo 2093435 15903863 := bstep (se 1 (by rfl) ⟨11927897, by rfl⟩ : syracuseStep 15903863 = 23855795) B23855795
theorem B10602575 : Blo 2093435 10602575 := bstep (se 1 (by rfl) ⟨7951931, by rfl⟩ : syracuseStep 10602575 = 15903863) B15903863
theorem B7068383 : Blo 2093435 7068383 := bstep (se 1 (by rfl) ⟨5301287, by rfl⟩ : syracuseStep 7068383 = 10602575) B10602575
theorem B4712255 : Blo 2093435 4712255 := bstep (se 1 (by rfl) ⟨3534191, by rfl⟩ : syracuseStep 4712255 = 7068383) B7068383
theorem B3141503 : Blo 2093435 3141503 := bstep (se 1 (by rfl) ⟨2356127, by rfl⟩ : syracuseStep 3141503 = 4712255) B4712255
theorem B2094335 : Blo 2093435 2094335 := bstep (se 1 (by rfl) ⟨1570751, by rfl⟩ : syracuseStep 2094335 = 3141503) B3141503
theorem B3141509 : Blo 2093435 3141509 := bbase (se 4 (by rfl) ⟨294516, by rfl⟩ : syracuseStep 3141509 = 589033) (by norm_num)
theorem B2094339 : Blo 2093435 2094339 := bstep (se 1 (by rfl) ⟨1570754, by rfl⟩ : syracuseStep 2094339 = 3141509) B3141509
theorem B3534205 : Blo 2093435 3534205 := bbase (se 3 (by rfl) ⟨662663, by rfl⟩ : syracuseStep 3534205 = 1325327) (by norm_num)
theorem B4712273 : Blo 2093435 4712273 := bstep (se 2 (by rfl) ⟨1767102, by rfl⟩ : syracuseStep 4712273 = 3534205) B3534205
theorem B3141515 : Blo 2093435 3141515 := bstep (se 1 (by rfl) ⟨2356136, by rfl⟩ : syracuseStep 3141515 = 4712273) B4712273
theorem B2094343 : Blo 2093435 2094343 := bstep (se 1 (by rfl) ⟨1570757, by rfl⟩ : syracuseStep 2094343 = 3141515) B3141515
theorem B2356141 : Blo 2093435 2356141 := bbase (se 3 (by rfl) ⟨441776, by rfl⟩ : syracuseStep 2356141 = 883553) (by norm_num)
theorem B3141521 : Blo 2093435 3141521 := bstep (se 2 (by rfl) ⟨1178070, by rfl⟩ : syracuseStep 3141521 = 2356141) B2356141
theorem B2094347 : Blo 2093435 2094347 := bstep (se 1 (by rfl) ⟨1570760, by rfl⟩ : syracuseStep 2094347 = 3141521) B3141521
theorem B7068437 : Blo 2093435 7068437 := bbase (se 6 (by rfl) ⟨165666, by rfl⟩ : syracuseStep 7068437 = 331333) (by norm_num)
theorem B4712291 : Blo 2093435 4712291 := bstep (se 1 (by rfl) ⟨3534218, by rfl⟩ : syracuseStep 4712291 = 7068437) B7068437
theorem B3141527 : Blo 2093435 3141527 := bstep (se 1 (by rfl) ⟨2356145, by rfl⟩ : syracuseStep 3141527 = 4712291) B4712291
theorem B2094351 : Blo 2093435 2094351 := bstep (se 1 (by rfl) ⟨1570763, by rfl⟩ : syracuseStep 2094351 = 3141527) B3141527
theorem B3141533 : Blo 2093435 3141533 := bbase (se 3 (by rfl) ⟨589037, by rfl⟩ : syracuseStep 3141533 = 1178075) (by norm_num)
theorem B2094355 : Blo 2093435 2094355 := bstep (se 1 (by rfl) ⟨1570766, by rfl⟩ : syracuseStep 2094355 = 3141533) B3141533
theorem B4712309 : Blo 2093435 4712309 := bbase (se 5 (by rfl) ⟨220889, by rfl⟩ : syracuseStep 4712309 = 441779) (by norm_num)
theorem B3141539 : Blo 2093435 3141539 := bstep (se 1 (by rfl) ⟨2356154, by rfl⟩ : syracuseStep 3141539 = 4712309) B4712309
theorem B2094359 : Blo 2093435 2094359 := bstep (se 1 (by rfl) ⟨1570769, by rfl⟩ : syracuseStep 2094359 = 3141539) B3141539
theorem B4245877 : Blo 2093435 4245877 := bbase (se 5 (by rfl) ⟨199025, by rfl⟩ : syracuseStep 4245877 = 398051) (by norm_num)
theorem B22644677 : Blo 2093435 22644677 := bstep (se 4 (by rfl) ⟨2122938, by rfl⟩ : syracuseStep 22644677 = 4245877) B4245877
theorem B15096451 : Blo 2093435 15096451 := bstep (se 1 (by rfl) ⟨11322338, by rfl⟩ : syracuseStep 15096451 = 22644677) B22644677
theorem B20128601 : Blo 2093435 20128601 := bstep (se 2 (by rfl) ⟨7548225, by rfl⟩ : syracuseStep 20128601 = 15096451) B15096451
theorem B13419067 : Blo 2093435 13419067 := bstep (se 1 (by rfl) ⟨10064300, by rfl⟩ : syracuseStep 13419067 = 20128601) B20128601
theorem B17892089 : Blo 2093435 17892089 := bstep (se 2 (by rfl) ⟨6709533, by rfl⟩ : syracuseStep 17892089 = 13419067) B13419067
theorem B11928059 : Blo 2093435 11928059 := bstep (se 1 (by rfl) ⟨8946044, by rfl⟩ : syracuseStep 11928059 = 17892089) B17892089
theorem B7952039 : Blo 2093435 7952039 := bstep (se 1 (by rfl) ⟨5964029, by rfl⟩ : syracuseStep 7952039 = 11928059) B11928059
theorem B5301359 : Blo 2093435 5301359 := bstep (se 1 (by rfl) ⟨3976019, by rfl⟩ : syracuseStep 5301359 = 7952039) B7952039
theorem B3534239 : Blo 2093435 3534239 := bstep (se 1 (by rfl) ⟨2650679, by rfl⟩ : syracuseStep 3534239 = 5301359) B5301359
theorem B2356159 : Blo 2093435 2356159 := bstep (se 1 (by rfl) ⟨1767119, by rfl⟩ : syracuseStep 2356159 = 3534239) B3534239
theorem B3141545 : Blo 2093435 3141545 := bstep (se 2 (by rfl) ⟨1178079, by rfl⟩ : syracuseStep 3141545 = 2356159) B2356159
theorem B2094363 : Blo 2093435 2094363 := bstep (se 1 (by rfl) ⟨1570772, by rfl⟩ : syracuseStep 2094363 = 3141545) B3141545
theorem B7952053 : Blo 2093435 7952053 := bbase (se 5 (by rfl) ⟨372752, by rfl⟩ : syracuseStep 7952053 = 745505) (by norm_num)
theorem B10602737 : Blo 2093435 10602737 := bstep (se 2 (by rfl) ⟨3976026, by rfl⟩ : syracuseStep 10602737 = 7952053) B7952053
theorem B7068491 : Blo 2093435 7068491 := bstep (se 1 (by rfl) ⟨5301368, by rfl⟩ : syracuseStep 7068491 = 10602737) B10602737
theorem B4712327 : Blo 2093435 4712327 := bstep (se 1 (by rfl) ⟨3534245, by rfl⟩ : syracuseStep 4712327 = 7068491) B7068491
theorem B3141551 : Blo 2093435 3141551 := bstep (se 1 (by rfl) ⟨2356163, by rfl⟩ : syracuseStep 3141551 = 4712327) B4712327
theorem B2094367 : Blo 2093435 2094367 := bstep (se 1 (by rfl) ⟨1570775, by rfl⟩ : syracuseStep 2094367 = 3141551) B3141551
theorem B3141557 : Blo 2093435 3141557 := bbase (se 5 (by rfl) ⟨147260, by rfl⟩ : syracuseStep 3141557 = 294521) (by norm_num)
theorem B2094371 : Blo 2093435 2094371 := bstep (se 1 (by rfl) ⟨1570778, by rfl⟩ : syracuseStep 2094371 = 3141557) B3141557
theorem B5301389 : Blo 2093435 5301389 := bbase (se 3 (by rfl) ⟨994010, by rfl⟩ : syracuseStep 5301389 = 1988021) (by norm_num)
theorem B3534259 : Blo 2093435 3534259 := bstep (se 1 (by rfl) ⟨2650694, by rfl⟩ : syracuseStep 3534259 = 5301389) B5301389
theorem B4712345 : Blo 2093435 4712345 := bstep (se 2 (by rfl) ⟨1767129, by rfl⟩ : syracuseStep 4712345 = 3534259) B3534259
theorem B3141563 : Blo 2093435 3141563 := bstep (se 1 (by rfl) ⟨2356172, by rfl⟩ : syracuseStep 3141563 = 4712345) B4712345
theorem B2094375 : Blo 2093435 2094375 := bstep (se 1 (by rfl) ⟨1570781, by rfl⟩ : syracuseStep 2094375 = 3141563) B3141563
theorem B2356177 : Blo 2093435 2356177 := bbase (se 2 (by rfl) ⟨883566, by rfl⟩ : syracuseStep 2356177 = 1767133) (by norm_num)
theorem B3141569 : Blo 2093435 3141569 := bstep (se 2 (by rfl) ⟨1178088, by rfl⟩ : syracuseStep 3141569 = 2356177) B2356177
theorem B2094379 : Blo 2093435 2094379 := bstep (se 1 (by rfl) ⟨1570784, by rfl⟩ : syracuseStep 2094379 = 3141569) B3141569
theorem B6045461 : Blo 2093435 6045461 := bbase (se 6 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 6045461 = 283381) (by norm_num)
theorem B4030307 : Blo 2093435 4030307 := bstep (se 1 (by rfl) ⟨3022730, by rfl⟩ : syracuseStep 4030307 = 6045461) B6045461
theorem B2686871 : Blo 2093435 2686871 := bstep (se 1 (by rfl) ⟨2015153, by rfl⟩ : syracuseStep 2686871 = 4030307) B4030307
theorem B7164989 : Blo 2093435 7164989 := bstep (se 3 (by rfl) ⟨1343435, by rfl⟩ : syracuseStep 7164989 = 2686871) B2686871
theorem B4776659 : Blo 2093435 4776659 := bstep (se 1 (by rfl) ⟨3582494, by rfl⟩ : syracuseStep 4776659 = 7164989) B7164989
theorem B3184439 : Blo 2093435 3184439 := bstep (se 1 (by rfl) ⟨2388329, by rfl⟩ : syracuseStep 3184439 = 4776659) B4776659
theorem B8491837 : Blo 2093435 8491837 := bstep (se 3 (by rfl) ⟨1592219, by rfl⟩ : syracuseStep 8491837 = 3184439) B3184439
theorem B11322449 : Blo 2093435 11322449 := bstep (se 2 (by rfl) ⟨4245918, by rfl⟩ : syracuseStep 11322449 = 8491837) B8491837
theorem B7548299 : Blo 2093435 7548299 := bstep (se 1 (by rfl) ⟨5661224, by rfl⟩ : syracuseStep 7548299 = 11322449) B11322449
theorem B5032199 : Blo 2093435 5032199 := bstep (se 1 (by rfl) ⟨3774149, by rfl⟩ : syracuseStep 5032199 = 7548299) B7548299
theorem B3354799 : Blo 2093435 3354799 := bstep (se 1 (by rfl) ⟨2516099, by rfl⟩ : syracuseStep 3354799 = 5032199) B5032199
theorem B4473065 : Blo 2093435 4473065 := bstep (se 2 (by rfl) ⟨1677399, by rfl⟩ : syracuseStep 4473065 = 3354799) B3354799
theorem B2982043 : Blo 2093435 2982043 := bstep (se 1 (by rfl) ⟨2236532, by rfl⟩ : syracuseStep 2982043 = 4473065) B4473065
theorem B3976057 : Blo 2093435 3976057 := bstep (se 2 (by rfl) ⟨1491021, by rfl⟩ : syracuseStep 3976057 = 2982043) B2982043
theorem B5301409 : Blo 2093435 5301409 := bstep (se 2 (by rfl) ⟨1988028, by rfl⟩ : syracuseStep 5301409 = 3976057) B3976057
theorem B7068545 : Blo 2093435 7068545 := bstep (se 2 (by rfl) ⟨2650704, by rfl⟩ : syracuseStep 7068545 = 5301409) B5301409
theorem B4712363 : Blo 2093435 4712363 := bstep (se 1 (by rfl) ⟨3534272, by rfl⟩ : syracuseStep 4712363 = 7068545) B7068545
theorem B3141575 : Blo 2093435 3141575 := bstep (se 1 (by rfl) ⟨2356181, by rfl⟩ : syracuseStep 3141575 = 4712363) B4712363
theorem B2094383 : Blo 2093435 2094383 := bstep (se 1 (by rfl) ⟨1570787, by rfl⟩ : syracuseStep 2094383 = 3141575) B3141575
theorem B3141581 : Blo 2093435 3141581 := bbase (se 3 (by rfl) ⟨589046, by rfl⟩ : syracuseStep 3141581 = 1178093) (by norm_num)
theorem B2094387 : Blo 2093435 2094387 := bstep (se 1 (by rfl) ⟨1570790, by rfl⟩ : syracuseStep 2094387 = 3141581) B3141581
theorem B4712381 : Blo 2093435 4712381 := bbase (se 3 (by rfl) ⟨883571, by rfl⟩ : syracuseStep 4712381 = 1767143) (by norm_num)
theorem B3141587 : Blo 2093435 3141587 := bstep (se 1 (by rfl) ⟨2356190, by rfl⟩ : syracuseStep 3141587 = 4712381) B4712381
theorem B2094391 : Blo 2093435 2094391 := bstep (se 1 (by rfl) ⟨1570793, by rfl⟩ : syracuseStep 2094391 = 3141587) B3141587
theorem B3534293 : Blo 2093435 3534293 := bbase (se 7 (by rfl) ⟨41417, by rfl⟩ : syracuseStep 3534293 = 82835) (by norm_num)
theorem B2356195 : Blo 2093435 2356195 := bstep (se 1 (by rfl) ⟨1767146, by rfl⟩ : syracuseStep 2356195 = 3534293) B3534293
theorem B3141593 : Blo 2093435 3141593 := bstep (se 2 (by rfl) ⟨1178097, by rfl⟩ : syracuseStep 3141593 = 2356195) B2356195
theorem B2094395 : Blo 2093435 2094395 := bstep (se 1 (by rfl) ⟨1570796, by rfl⟩ : syracuseStep 2094395 = 3141593) B3141593
theorem B8946197 : Blo 2093435 8946197 := bbase (se 6 (by rfl) ⟨209676, by rfl⟩ : syracuseStep 8946197 = 419353) (by norm_num)
theorem B5964131 : Blo 2093435 5964131 := bstep (se 1 (by rfl) ⟨4473098, by rfl⟩ : syracuseStep 5964131 = 8946197) B8946197
theorem B15904349 : Blo 2093435 15904349 := bstep (se 3 (by rfl) ⟨2982065, by rfl⟩ : syracuseStep 15904349 = 5964131) B5964131
theorem B10602899 : Blo 2093435 10602899 := bstep (se 1 (by rfl) ⟨7952174, by rfl⟩ : syracuseStep 10602899 = 15904349) B15904349
theorem B7068599 : Blo 2093435 7068599 := bstep (se 1 (by rfl) ⟨5301449, by rfl⟩ : syracuseStep 7068599 = 10602899) B10602899
theorem B4712399 : Blo 2093435 4712399 := bstep (se 1 (by rfl) ⟨3534299, by rfl⟩ : syracuseStep 4712399 = 7068599) B7068599
theorem B3141599 : Blo 2093435 3141599 := bstep (se 1 (by rfl) ⟨2356199, by rfl⟩ : syracuseStep 3141599 = 4712399) B4712399
theorem B2094399 : Blo 2093435 2094399 := bstep (se 1 (by rfl) ⟨1570799, by rfl⟩ : syracuseStep 2094399 = 3141599) B3141599
theorem B3141605 : Blo 2093435 3141605 := bbase (se 4 (by rfl) ⟨294525, by rfl⟩ : syracuseStep 3141605 = 589051) (by norm_num)
theorem B2094403 : Blo 2093435 2094403 := bstep (se 1 (by rfl) ⟨1570802, by rfl⟩ : syracuseStep 2094403 = 3141605) B3141605
theorem B6801221 : Blo 2093435 6801221 := bbase (se 4 (by rfl) ⟨637614, by rfl⟩ : syracuseStep 6801221 = 1275229) (by norm_num)
theorem B4534147 : Blo 2093435 4534147 := bstep (se 1 (by rfl) ⟨3400610, by rfl⟩ : syracuseStep 4534147 = 6801221) B6801221
theorem B6045529 : Blo 2093435 6045529 := bstep (se 2 (by rfl) ⟨2267073, by rfl⟩ : syracuseStep 6045529 = 4534147) B4534147
theorem B8060705 : Blo 2093435 8060705 := bstep (se 2 (by rfl) ⟨3022764, by rfl⟩ : syracuseStep 8060705 = 6045529) B6045529
theorem B5373803 : Blo 2093435 5373803 := bstep (se 1 (by rfl) ⟨4030352, by rfl⟩ : syracuseStep 5373803 = 8060705) B8060705
theorem B14330141 : Blo 2093435 14330141 := bstep (se 3 (by rfl) ⟨2686901, by rfl⟩ : syracuseStep 14330141 = 5373803) B5373803
theorem B9553427 : Blo 2093435 9553427 := bstep (se 1 (by rfl) ⟨7165070, by rfl⟩ : syracuseStep 9553427 = 14330141) B14330141
theorem B6368951 : Blo 2093435 6368951 := bstep (se 1 (by rfl) ⟨4776713, by rfl⟩ : syracuseStep 6368951 = 9553427) B9553427
theorem B4245967 : Blo 2093435 4245967 := bstep (se 1 (by rfl) ⟨3184475, by rfl⟩ : syracuseStep 4245967 = 6368951) B6368951
theorem B5661289 : Blo 2093435 5661289 := bstep (se 2 (by rfl) ⟨2122983, by rfl⟩ : syracuseStep 5661289 = 4245967) B4245967
theorem B7548385 : Blo 2093435 7548385 := bstep (se 2 (by rfl) ⟨2830644, by rfl⟩ : syracuseStep 7548385 = 5661289) B5661289
theorem B10064513 : Blo 2093435 10064513 := bstep (se 2 (by rfl) ⟨3774192, by rfl⟩ : syracuseStep 10064513 = 7548385) B7548385
theorem B6709675 : Blo 2093435 6709675 := bstep (se 1 (by rfl) ⟨5032256, by rfl⟩ : syracuseStep 6709675 = 10064513) B10064513
theorem B8946233 : Blo 2093435 8946233 := bstep (se 2 (by rfl) ⟨3354837, by rfl⟩ : syracuseStep 8946233 = 6709675) B6709675
theorem B5964155 : Blo 2093435 5964155 := bstep (se 1 (by rfl) ⟨4473116, by rfl⟩ : syracuseStep 5964155 = 8946233) B8946233
theorem B3976103 : Blo 2093435 3976103 := bstep (se 1 (by rfl) ⟨2982077, by rfl⟩ : syracuseStep 3976103 = 5964155) B5964155
theorem B2650735 : Blo 2093435 2650735 := bstep (se 1 (by rfl) ⟨1988051, by rfl⟩ : syracuseStep 2650735 = 3976103) B3976103
theorem B3534313 : Blo 2093435 3534313 := bstep (se 2 (by rfl) ⟨1325367, by rfl⟩ : syracuseStep 3534313 = 2650735) B2650735
theorem B4712417 : Blo 2093435 4712417 := bstep (se 2 (by rfl) ⟨1767156, by rfl⟩ : syracuseStep 4712417 = 3534313) B3534313
theorem B3141611 : Blo 2093435 3141611 := bstep (se 1 (by rfl) ⟨2356208, by rfl⟩ : syracuseStep 3141611 = 4712417) B4712417
theorem B2094407 : Blo 2093435 2094407 := bstep (se 1 (by rfl) ⟨1570805, by rfl⟩ : syracuseStep 2094407 = 3141611) B3141611
theorem B2356213 : Blo 2093435 2356213 := bbase (se 5 (by rfl) ⟨110447, by rfl⟩ : syracuseStep 2356213 = 220895) (by norm_num)
theorem B3141617 : Blo 2093435 3141617 := bstep (se 2 (by rfl) ⟨1178106, by rfl⟩ : syracuseStep 3141617 = 2356213) B2356213
theorem B2094411 : Blo 2093435 2094411 := bstep (se 1 (by rfl) ⟨1570808, by rfl⟩ : syracuseStep 2094411 = 3141617) B3141617
theorem B2650745 : Blo 2093435 2650745 := bbase (se 2 (by rfl) ⟨994029, by rfl⟩ : syracuseStep 2650745 = 1988059) (by norm_num)
theorem B7068653 : Blo 2093435 7068653 := bstep (se 3 (by rfl) ⟨1325372, by rfl⟩ : syracuseStep 7068653 = 2650745) B2650745
theorem B4712435 : Blo 2093435 4712435 := bstep (se 1 (by rfl) ⟨3534326, by rfl⟩ : syracuseStep 4712435 = 7068653) B7068653
theorem B3141623 : Blo 2093435 3141623 := bstep (se 1 (by rfl) ⟨2356217, by rfl⟩ : syracuseStep 3141623 = 4712435) B4712435
theorem B2094415 : Blo 2093435 2094415 := bstep (se 1 (by rfl) ⟨1570811, by rfl⟩ : syracuseStep 2094415 = 3141623) B3141623
theorem B3141629 : Blo 2093435 3141629 := bbase (se 3 (by rfl) ⟨589055, by rfl⟩ : syracuseStep 3141629 = 1178111) (by norm_num)
theorem B2094419 : Blo 2093435 2094419 := bstep (se 1 (by rfl) ⟨1570814, by rfl⟩ : syracuseStep 2094419 = 3141629) B3141629
theorem B4712453 : Blo 2093435 4712453 := bbase (se 4 (by rfl) ⟨441792, by rfl⟩ : syracuseStep 4712453 = 883585) (by norm_num)
theorem B3141635 : Blo 2093435 3141635 := bstep (se 1 (by rfl) ⟨2356226, by rfl⟩ : syracuseStep 3141635 = 4712453) B4712453
theorem B2094423 : Blo 2093435 2094423 := bstep (se 1 (by rfl) ⟨1570817, by rfl⟩ : syracuseStep 2094423 = 3141635) B3141635
theorem B3976141 : Blo 2093435 3976141 := bbase (se 3 (by rfl) ⟨745526, by rfl⟩ : syracuseStep 3976141 = 1491053) (by norm_num)
theorem B5301521 : Blo 2093435 5301521 := bstep (se 2 (by rfl) ⟨1988070, by rfl⟩ : syracuseStep 5301521 = 3976141) B3976141
theorem B3534347 : Blo 2093435 3534347 := bstep (se 1 (by rfl) ⟨2650760, by rfl⟩ : syracuseStep 3534347 = 5301521) B5301521
theorem B2356231 : Blo 2093435 2356231 := bstep (se 1 (by rfl) ⟨1767173, by rfl⟩ : syracuseStep 2356231 = 3534347) B3534347
theorem B3141641 : Blo 2093435 3141641 := bstep (se 2 (by rfl) ⟨1178115, by rfl⟩ : syracuseStep 3141641 = 2356231) B2356231
theorem B2094427 : Blo 2093435 2094427 := bstep (se 1 (by rfl) ⟨1570820, by rfl⟩ : syracuseStep 2094427 = 3141641) B3141641
theorem B10603061 : Blo 2093435 10603061 := bbase (se 5 (by rfl) ⟨497018, by rfl⟩ : syracuseStep 10603061 = 994037) (by norm_num)
theorem B7068707 : Blo 2093435 7068707 := bstep (se 1 (by rfl) ⟨5301530, by rfl⟩ : syracuseStep 7068707 = 10603061) B10603061
theorem B4712471 : Blo 2093435 4712471 := bstep (se 1 (by rfl) ⟨3534353, by rfl⟩ : syracuseStep 4712471 = 7068707) B7068707
theorem B3141647 : Blo 2093435 3141647 := bstep (se 1 (by rfl) ⟨2356235, by rfl⟩ : syracuseStep 3141647 = 4712471) B4712471
theorem B2094431 : Blo 2093435 2094431 := bstep (se 1 (by rfl) ⟨1570823, by rfl⟩ : syracuseStep 2094431 = 3141647) B3141647
theorem B3141653 : Blo 2093435 3141653 := bbase (se 6 (by rfl) ⟨73632, by rfl⟩ : syracuseStep 3141653 = 147265) (by norm_num)
theorem B2094435 : Blo 2093435 2094435 := bstep (se 1 (by rfl) ⟨1570826, by rfl⟩ : syracuseStep 2094435 = 3141653) B3141653
theorem B14330357 : Blo 2093435 14330357 := bbase (se 5 (by rfl) ⟨671735, by rfl⟩ : syracuseStep 14330357 = 1343471) (by norm_num)
theorem B9553571 : Blo 2093435 9553571 := bstep (se 1 (by rfl) ⟨7165178, by rfl⟩ : syracuseStep 9553571 = 14330357) B14330357
theorem B6369047 : Blo 2093435 6369047 := bstep (se 1 (by rfl) ⟨4776785, by rfl⟩ : syracuseStep 6369047 = 9553571) B9553571
theorem B4246031 : Blo 2093435 4246031 := bstep (se 1 (by rfl) ⟨3184523, by rfl⟩ : syracuseStep 4246031 = 6369047) B6369047
theorem B11322749 : Blo 2093435 11322749 := bstep (se 3 (by rfl) ⟨2123015, by rfl⟩ : syracuseStep 11322749 = 4246031) B4246031
theorem B7548499 : Blo 2093435 7548499 := bstep (se 1 (by rfl) ⟨5661374, by rfl⟩ : syracuseStep 7548499 = 11322749) B11322749
theorem B10064665 : Blo 2093435 10064665 := bstep (se 2 (by rfl) ⟨3774249, by rfl⟩ : syracuseStep 10064665 = 7548499) B7548499
theorem B13419553 : Blo 2093435 13419553 := bstep (se 2 (by rfl) ⟨5032332, by rfl⟩ : syracuseStep 13419553 = 10064665) B10064665
theorem B17892737 : Blo 2093435 17892737 := bstep (se 2 (by rfl) ⟨6709776, by rfl⟩ : syracuseStep 17892737 = 13419553) B13419553
theorem B11928491 : Blo 2093435 11928491 := bstep (se 1 (by rfl) ⟨8946368, by rfl⟩ : syracuseStep 11928491 = 17892737) B17892737
theorem B7952327 : Blo 2093435 7952327 := bstep (se 1 (by rfl) ⟨5964245, by rfl⟩ : syracuseStep 7952327 = 11928491) B11928491
theorem B5301551 : Blo 2093435 5301551 := bstep (se 1 (by rfl) ⟨3976163, by rfl⟩ : syracuseStep 5301551 = 7952327) B7952327
theorem B3534367 : Blo 2093435 3534367 := bstep (se 1 (by rfl) ⟨2650775, by rfl⟩ : syracuseStep 3534367 = 5301551) B5301551
theorem B4712489 : Blo 2093435 4712489 := bstep (se 2 (by rfl) ⟨1767183, by rfl⟩ : syracuseStep 4712489 = 3534367) B3534367
theorem B3141659 : Blo 2093435 3141659 := bstep (se 1 (by rfl) ⟨2356244, by rfl⟩ : syracuseStep 3141659 = 4712489) B4712489
theorem B2094439 : Blo 2093435 2094439 := bstep (se 1 (by rfl) ⟨1570829, by rfl⟩ : syracuseStep 2094439 = 3141659) B3141659
theorem B2356249 : Blo 2093435 2356249 := bbase (se 2 (by rfl) ⟨883593, by rfl⟩ : syracuseStep 2356249 = 1767187) (by norm_num)
theorem B3141665 : Blo 2093435 3141665 := bstep (se 2 (by rfl) ⟨1178124, by rfl⟩ : syracuseStep 3141665 = 2356249) B2356249
theorem B2094443 : Blo 2093435 2094443 := bstep (se 1 (by rfl) ⟨1570832, by rfl⟩ : syracuseStep 2094443 = 3141665) B3141665
theorem B7952357 : Blo 2093435 7952357 := bbase (se 4 (by rfl) ⟨745533, by rfl⟩ : syracuseStep 7952357 = 1491067) (by norm_num)
theorem B5301571 : Blo 2093435 5301571 := bstep (se 1 (by rfl) ⟨3976178, by rfl⟩ : syracuseStep 5301571 = 7952357) B7952357
theorem B7068761 : Blo 2093435 7068761 := bstep (se 2 (by rfl) ⟨2650785, by rfl⟩ : syracuseStep 7068761 = 5301571) B5301571
theorem B4712507 : Blo 2093435 4712507 := bstep (se 1 (by rfl) ⟨3534380, by rfl⟩ : syracuseStep 4712507 = 7068761) B7068761
theorem B3141671 : Blo 2093435 3141671 := bstep (se 1 (by rfl) ⟨2356253, by rfl⟩ : syracuseStep 3141671 = 4712507) B4712507
theorem B2094447 : Blo 2093435 2094447 := bstep (se 1 (by rfl) ⟨1570835, by rfl⟩ : syracuseStep 2094447 = 3141671) B3141671
theorem B3141677 : Blo 2093435 3141677 := bbase (se 3 (by rfl) ⟨589064, by rfl⟩ : syracuseStep 3141677 = 1178129) (by norm_num)
theorem B2094451 : Blo 2093435 2094451 := bstep (se 1 (by rfl) ⟨1570838, by rfl⟩ : syracuseStep 2094451 = 3141677) B3141677
theorem B4712525 : Blo 2093435 4712525 := bbase (se 3 (by rfl) ⟨883598, by rfl⟩ : syracuseStep 4712525 = 1767197) (by norm_num)
theorem B3141683 : Blo 2093435 3141683 := bstep (se 1 (by rfl) ⟨2356262, by rfl⟩ : syracuseStep 3141683 = 4712525) B4712525
theorem B2094455 : Blo 2093435 2094455 := bstep (se 1 (by rfl) ⟨1570841, by rfl⟩ : syracuseStep 2094455 = 3141683) B3141683
theorem B2650801 : Blo 2093435 2650801 := bbase (se 2 (by rfl) ⟨994050, by rfl⟩ : syracuseStep 2650801 = 1988101) (by norm_num)
theorem B3534401 : Blo 2093435 3534401 := bstep (se 2 (by rfl) ⟨1325400, by rfl⟩ : syracuseStep 3534401 = 2650801) B2650801
theorem B2356267 : Blo 2093435 2356267 := bstep (se 1 (by rfl) ⟨1767200, by rfl⟩ : syracuseStep 2356267 = 3534401) B3534401
theorem B3141689 : Blo 2093435 3141689 := bstep (se 2 (by rfl) ⟨1178133, by rfl⟩ : syracuseStep 3141689 = 2356267) B2356267
theorem B2094459 : Blo 2093435 2094459 := bstep (se 1 (by rfl) ⟨1570844, by rfl⟩ : syracuseStep 2094459 = 3141689) B3141689
theorem B3774293 : Blo 2093435 3774293 := bbase (se 9 (by rfl) ⟨11057, by rfl⟩ : syracuseStep 3774293 = 22115) (by norm_num)
theorem B2516195 : Blo 2093435 2516195 := bstep (se 1 (by rfl) ⟨1887146, by rfl⟩ : syracuseStep 2516195 = 3774293) B3774293
theorem B6709853 : Blo 2093435 6709853 := bstep (se 3 (by rfl) ⟨1258097, by rfl⟩ : syracuseStep 6709853 = 2516195) B2516195
theorem B4473235 : Blo 2093435 4473235 := bstep (se 1 (by rfl) ⟨3354926, by rfl⟩ : syracuseStep 4473235 = 6709853) B6709853
theorem B23857253 : Blo 2093435 23857253 := bstep (se 4 (by rfl) ⟨2236617, by rfl⟩ : syracuseStep 23857253 = 4473235) B4473235
theorem B15904835 : Blo 2093435 15904835 := bstep (se 1 (by rfl) ⟨11928626, by rfl⟩ : syracuseStep 15904835 = 23857253) B23857253
theorem B10603223 : Blo 2093435 10603223 := bstep (se 1 (by rfl) ⟨7952417, by rfl⟩ : syracuseStep 10603223 = 15904835) B15904835
theorem B7068815 : Blo 2093435 7068815 := bstep (se 1 (by rfl) ⟨5301611, by rfl⟩ : syracuseStep 7068815 = 10603223) B10603223
theorem B4712543 : Blo 2093435 4712543 := bstep (se 1 (by rfl) ⟨3534407, by rfl⟩ : syracuseStep 4712543 = 7068815) B7068815
theorem B3141695 : Blo 2093435 3141695 := bstep (se 1 (by rfl) ⟨2356271, by rfl⟩ : syracuseStep 3141695 = 4712543) B4712543
theorem B2094463 : Blo 2093435 2094463 := bstep (se 1 (by rfl) ⟨1570847, by rfl⟩ : syracuseStep 2094463 = 3141695) B3141695
theorem B3141701 : Blo 2093435 3141701 := bbase (se 4 (by rfl) ⟨294534, by rfl⟩ : syracuseStep 3141701 = 589069) (by norm_num)
theorem B2094467 : Blo 2093435 2094467 := bstep (se 1 (by rfl) ⟨1570850, by rfl⟩ : syracuseStep 2094467 = 3141701) B3141701
theorem B3534421 : Blo 2093435 3534421 := bbase (se 8 (by rfl) ⟨20709, by rfl⟩ : syracuseStep 3534421 = 41419) (by norm_num)
theorem B4712561 : Blo 2093435 4712561 := bstep (se 2 (by rfl) ⟨1767210, by rfl⟩ : syracuseStep 4712561 = 3534421) B3534421
theorem B3141707 : Blo 2093435 3141707 := bstep (se 1 (by rfl) ⟨2356280, by rfl⟩ : syracuseStep 3141707 = 4712561) B4712561
theorem B2094471 : Blo 2093435 2094471 := bstep (se 1 (by rfl) ⟨1570853, by rfl⟩ : syracuseStep 2094471 = 3141707) B3141707
theorem B2356285 : Blo 2093435 2356285 := bbase (se 3 (by rfl) ⟨441803, by rfl⟩ : syracuseStep 2356285 = 883607) (by norm_num)
theorem B3141713 : Blo 2093435 3141713 := bstep (se 2 (by rfl) ⟨1178142, by rfl⟩ : syracuseStep 3141713 = 2356285) B2356285
theorem B2094475 : Blo 2093435 2094475 := bstep (se 1 (by rfl) ⟨1570856, by rfl⟩ : syracuseStep 2094475 = 3141713) B3141713
theorem B7068869 : Blo 2093435 7068869 := bbase (se 4 (by rfl) ⟨662706, by rfl⟩ : syracuseStep 7068869 = 1325413) (by norm_num)
theorem B4712579 : Blo 2093435 4712579 := bstep (se 1 (by rfl) ⟨3534434, by rfl⟩ : syracuseStep 4712579 = 7068869) B7068869
theorem B3141719 : Blo 2093435 3141719 := bstep (se 1 (by rfl) ⟨2356289, by rfl⟩ : syracuseStep 3141719 = 4712579) B4712579
theorem B2094479 : Blo 2093435 2094479 := bstep (se 1 (by rfl) ⟨1570859, by rfl⟩ : syracuseStep 2094479 = 3141719) B3141719
theorem B3141725 : Blo 2093435 3141725 := bbase (se 3 (by rfl) ⟨589073, by rfl⟩ : syracuseStep 3141725 = 1178147) (by norm_num)
theorem B2094483 : Blo 2093435 2094483 := bstep (se 1 (by rfl) ⟨1570862, by rfl⟩ : syracuseStep 2094483 = 3141725) B3141725
theorem B4712597 : Blo 2093435 4712597 := bbase (se 6 (by rfl) ⟨110451, by rfl⟩ : syracuseStep 4712597 = 220903) (by norm_num)
theorem B3141731 : Blo 2093435 3141731 := bstep (se 1 (by rfl) ⟨2356298, by rfl⟩ : syracuseStep 3141731 = 4712597) B4712597
theorem B2094487 : Blo 2093435 2094487 := bstep (se 1 (by rfl) ⟨1570865, by rfl⟩ : syracuseStep 2094487 = 3141731) B3141731
theorem B2982197 : Blo 2093435 2982197 := bbase (se 5 (by rfl) ⟨139790, by rfl⟩ : syracuseStep 2982197 = 279581) (by norm_num)
theorem B7952525 : Blo 2093435 7952525 := bstep (se 3 (by rfl) ⟨1491098, by rfl⟩ : syracuseStep 7952525 = 2982197) B2982197
theorem B5301683 : Blo 2093435 5301683 := bstep (se 1 (by rfl) ⟨3976262, by rfl⟩ : syracuseStep 5301683 = 7952525) B7952525
theorem B3534455 : Blo 2093435 3534455 := bstep (se 1 (by rfl) ⟨2650841, by rfl⟩ : syracuseStep 3534455 = 5301683) B5301683
theorem B2356303 : Blo 2093435 2356303 := bstep (se 1 (by rfl) ⟨1767227, by rfl⟩ : syracuseStep 2356303 = 3534455) B3534455
theorem B3141737 : Blo 2093435 3141737 := bstep (se 2 (by rfl) ⟨1178151, by rfl⟩ : syracuseStep 3141737 = 2356303) B2356303
theorem B2094491 : Blo 2093435 2094491 := bstep (se 1 (by rfl) ⟨1570868, by rfl⟩ : syracuseStep 2094491 = 3141737) B3141737
theorem B22646101 : Blo 2093435 22646101 := bbase (se 11 (by rfl) ⟨16586, by rfl⟩ : syracuseStep 22646101 = 33173) (by norm_num)
theorem B30194801 : Blo 2093435 30194801 := bstep (se 2 (by rfl) ⟨11323050, by rfl⟩ : syracuseStep 30194801 = 22646101) B22646101
theorem B20129867 : Blo 2093435 20129867 := bstep (se 1 (by rfl) ⟨15097400, by rfl⟩ : syracuseStep 20129867 = 30194801) B30194801
theorem B13419911 : Blo 2093435 13419911 := bstep (se 1 (by rfl) ⟨10064933, by rfl⟩ : syracuseStep 13419911 = 20129867) B20129867
theorem B8946607 : Blo 2093435 8946607 := bstep (se 1 (by rfl) ⟨6709955, by rfl⟩ : syracuseStep 8946607 = 13419911) B13419911
theorem B11928809 : Blo 2093435 11928809 := bstep (se 2 (by rfl) ⟨4473303, by rfl⟩ : syracuseStep 11928809 = 8946607) B8946607
theorem B7952539 : Blo 2093435 7952539 := bstep (se 1 (by rfl) ⟨5964404, by rfl⟩ : syracuseStep 7952539 = 11928809) B11928809
theorem B10603385 : Blo 2093435 10603385 := bstep (se 2 (by rfl) ⟨3976269, by rfl⟩ : syracuseStep 10603385 = 7952539) B7952539
theorem B7068923 : Blo 2093435 7068923 := bstep (se 1 (by rfl) ⟨5301692, by rfl⟩ : syracuseStep 7068923 = 10603385) B10603385
theorem B4712615 : Blo 2093435 4712615 := bstep (se 1 (by rfl) ⟨3534461, by rfl⟩ : syracuseStep 4712615 = 7068923) B7068923
theorem B3141743 : Blo 2093435 3141743 := bstep (se 1 (by rfl) ⟨2356307, by rfl⟩ : syracuseStep 3141743 = 4712615) B4712615
theorem B2094495 : Blo 2093435 2094495 := bstep (se 1 (by rfl) ⟨1570871, by rfl⟩ : syracuseStep 2094495 = 3141743) B3141743
theorem B3141749 : Blo 2093435 3141749 := bbase (se 5 (by rfl) ⟨147269, by rfl⟩ : syracuseStep 3141749 = 294539) (by norm_num)
theorem B2094499 : Blo 2093435 2094499 := bstep (se 1 (by rfl) ⟨1570874, by rfl⟩ : syracuseStep 2094499 = 3141749) B3141749
theorem B3976285 : Blo 2093435 3976285 := bbase (se 3 (by rfl) ⟨745553, by rfl⟩ : syracuseStep 3976285 = 1491107) (by norm_num)
theorem B5301713 : Blo 2093435 5301713 := bstep (se 2 (by rfl) ⟨1988142, by rfl⟩ : syracuseStep 5301713 = 3976285) B3976285
theorem B3534475 : Blo 2093435 3534475 := bstep (se 1 (by rfl) ⟨2650856, by rfl⟩ : syracuseStep 3534475 = 5301713) B5301713
theorem B4712633 : Blo 2093435 4712633 := bstep (se 2 (by rfl) ⟨1767237, by rfl⟩ : syracuseStep 4712633 = 3534475) B3534475
theorem B3141755 : Blo 2093435 3141755 := bstep (se 1 (by rfl) ⟨2356316, by rfl⟩ : syracuseStep 3141755 = 4712633) B4712633
theorem B2094503 : Blo 2093435 2094503 := bstep (se 1 (by rfl) ⟨1570877, by rfl⟩ : syracuseStep 2094503 = 3141755) B3141755
theorem B2356321 : Blo 2093435 2356321 := bbase (se 2 (by rfl) ⟨883620, by rfl⟩ : syracuseStep 2356321 = 1767241) (by norm_num)
theorem B3141761 : Blo 2093435 3141761 := bstep (se 2 (by rfl) ⟨1178160, by rfl⟩ : syracuseStep 3141761 = 2356321) B2356321
theorem B2094507 : Blo 2093435 2094507 := bstep (se 1 (by rfl) ⟨1570880, by rfl⟩ : syracuseStep 2094507 = 3141761) B3141761
theorem B5301733 : Blo 2093435 5301733 := bbase (se 4 (by rfl) ⟨497037, by rfl⟩ : syracuseStep 5301733 = 994075) (by norm_num)
theorem B7068977 : Blo 2093435 7068977 := bstep (se 2 (by rfl) ⟨2650866, by rfl⟩ : syracuseStep 7068977 = 5301733) B5301733
theorem B4712651 : Blo 2093435 4712651 := bstep (se 1 (by rfl) ⟨3534488, by rfl⟩ : syracuseStep 4712651 = 7068977) B7068977
theorem B3141767 : Blo 2093435 3141767 := bstep (se 1 (by rfl) ⟨2356325, by rfl⟩ : syracuseStep 3141767 = 4712651) B4712651
theorem B2094511 : Blo 2093435 2094511 := bstep (se 1 (by rfl) ⟨1570883, by rfl⟩ : syracuseStep 2094511 = 3141767) B3141767
theorem B3141773 : Blo 2093435 3141773 := bbase (se 3 (by rfl) ⟨589082, by rfl⟩ : syracuseStep 3141773 = 1178165) (by norm_num)
theorem B2094515 : Blo 2093435 2094515 := bstep (se 1 (by rfl) ⟨1570886, by rfl⟩ : syracuseStep 2094515 = 3141773) B3141773
theorem B4712669 : Blo 2093435 4712669 := bbase (se 3 (by rfl) ⟨883625, by rfl⟩ : syracuseStep 4712669 = 1767251) (by norm_num)
theorem B3141779 : Blo 2093435 3141779 := bstep (se 1 (by rfl) ⟨2356334, by rfl⟩ : syracuseStep 3141779 = 4712669) B4712669
theorem B2094519 : Blo 2093435 2094519 := bstep (se 1 (by rfl) ⟨1570889, by rfl⟩ : syracuseStep 2094519 = 3141779) B3141779
theorem B3534509 : Blo 2093435 3534509 := bbase (se 3 (by rfl) ⟨662720, by rfl⟩ : syracuseStep 3534509 = 1325441) (by norm_num)
theorem B2356339 : Blo 2093435 2356339 := bstep (se 1 (by rfl) ⟨1767254, by rfl⟩ : syracuseStep 2356339 = 3534509) B3534509
theorem B3141785 : Blo 2093435 3141785 := bstep (se 2 (by rfl) ⟨1178169, by rfl⟩ : syracuseStep 3141785 = 2356339) B2356339
theorem B2094523 : Blo 2093435 2094523 := bstep (se 1 (by rfl) ⟨1570892, by rfl⟩ : syracuseStep 2094523 = 3141785) B3141785
theorem B4304141 : Blo 2093435 4304141 := bbase (se 3 (by rfl) ⟨807026, by rfl⟩ : syracuseStep 4304141 = 1614053) (by norm_num)
theorem B45910837 : Blo 2093435 45910837 := bstep (se 5 (by rfl) ⟨2152070, by rfl⟩ : syracuseStep 45910837 = 4304141) B4304141
theorem B61214449 : Blo 2093435 61214449 := bstep (se 2 (by rfl) ⟨22955418, by rfl⟩ : syracuseStep 61214449 = 45910837) B45910837
theorem B81619265 : Blo 2093435 81619265 := bstep (se 2 (by rfl) ⟨30607224, by rfl⟩ : syracuseStep 81619265 = 61214449) B61214449
theorem B54412843 : Blo 2093435 54412843 := bstep (se 1 (by rfl) ⟨40809632, by rfl⟩ : syracuseStep 54412843 = 81619265) B81619265
theorem B72550457 : Blo 2093435 72550457 := bstep (se 2 (by rfl) ⟨27206421, by rfl⟩ : syracuseStep 72550457 = 54412843) B54412843
theorem B48366971 : Blo 2093435 48366971 := bstep (se 1 (by rfl) ⟨36275228, by rfl⟩ : syracuseStep 48366971 = 72550457) B72550457
theorem B32244647 : Blo 2093435 32244647 := bstep (se 1 (by rfl) ⟨24183485, by rfl⟩ : syracuseStep 32244647 = 48366971) B48366971
theorem B85985725 : Blo 2093435 85985725 := bstep (se 3 (by rfl) ⟨16122323, by rfl⟩ : syracuseStep 85985725 = 32244647) B32244647
theorem B114647633 : Blo 2093435 114647633 := bstep (se 2 (by rfl) ⟨42992862, by rfl⟩ : syracuseStep 114647633 = 85985725) B85985725
theorem B76431755 : Blo 2093435 76431755 := bstep (se 1 (by rfl) ⟨57323816, by rfl⟩ : syracuseStep 76431755 = 114647633) B114647633
theorem B50954503 : Blo 2093435 50954503 := bstep (se 1 (by rfl) ⟨38215877, by rfl⟩ : syracuseStep 50954503 = 76431755) B76431755
theorem B67939337 : Blo 2093435 67939337 := bstep (se 2 (by rfl) ⟨25477251, by rfl⟩ : syracuseStep 67939337 = 50954503) B50954503
theorem B45292891 : Blo 2093435 45292891 := bstep (se 1 (by rfl) ⟨33969668, by rfl⟩ : syracuseStep 45292891 = 67939337) B67939337
theorem B60390521 : Blo 2093435 60390521 := bstep (se 2 (by rfl) ⟨22646445, by rfl⟩ : syracuseStep 60390521 = 45292891) B45292891
theorem B40260347 : Blo 2093435 40260347 := bstep (se 1 (by rfl) ⟨30195260, by rfl⟩ : syracuseStep 40260347 = 60390521) B60390521
theorem B26840231 : Blo 2093435 26840231 := bstep (se 1 (by rfl) ⟨20130173, by rfl⟩ : syracuseStep 26840231 = 40260347) B40260347
theorem B17893487 : Blo 2093435 17893487 := bstep (se 1 (by rfl) ⟨13420115, by rfl⟩ : syracuseStep 17893487 = 26840231) B26840231
theorem B11928991 : Blo 2093435 11928991 := bstep (se 1 (by rfl) ⟨8946743, by rfl⟩ : syracuseStep 11928991 = 17893487) B17893487
theorem B15905321 : Blo 2093435 15905321 := bstep (se 2 (by rfl) ⟨5964495, by rfl⟩ : syracuseStep 15905321 = 11928991) B11928991
theorem B10603547 : Blo 2093435 10603547 := bstep (se 1 (by rfl) ⟨7952660, by rfl⟩ : syracuseStep 10603547 = 15905321) B15905321
theorem B7069031 : Blo 2093435 7069031 := bstep (se 1 (by rfl) ⟨5301773, by rfl⟩ : syracuseStep 7069031 = 10603547) B10603547
theorem B4712687 : Blo 2093435 4712687 := bstep (se 1 (by rfl) ⟨3534515, by rfl⟩ : syracuseStep 4712687 = 7069031) B7069031
theorem B3141791 : Blo 2093435 3141791 := bstep (se 1 (by rfl) ⟨2356343, by rfl⟩ : syracuseStep 3141791 = 4712687) B4712687
theorem B2094527 : Blo 2093435 2094527 := bstep (se 1 (by rfl) ⟨1570895, by rfl⟩ : syracuseStep 2094527 = 3141791) B3141791
theorem B3141797 : Blo 2093435 3141797 := bbase (se 4 (by rfl) ⟨294543, by rfl⟩ : syracuseStep 3141797 = 589087) (by norm_num)
theorem B2094531 : Blo 2093435 2094531 := bstep (se 1 (by rfl) ⟨1570898, by rfl⟩ : syracuseStep 2094531 = 3141797) B3141797
theorem B2650897 : Blo 2093435 2650897 := bbase (se 2 (by rfl) ⟨994086, by rfl⟩ : syracuseStep 2650897 = 1988173) (by norm_num)
theorem B3534529 : Blo 2093435 3534529 := bstep (se 2 (by rfl) ⟨1325448, by rfl⟩ : syracuseStep 3534529 = 2650897) B2650897
theorem B4712705 : Blo 2093435 4712705 := bstep (se 2 (by rfl) ⟨1767264, by rfl⟩ : syracuseStep 4712705 = 3534529) B3534529
theorem B3141803 : Blo 2093435 3141803 := bstep (se 1 (by rfl) ⟨2356352, by rfl⟩ : syracuseStep 3141803 = 4712705) B4712705
theorem B2094535 : Blo 2093435 2094535 := bstep (se 1 (by rfl) ⟨1570901, by rfl⟩ : syracuseStep 2094535 = 3141803) B3141803
theorem B2356357 : Blo 2093435 2356357 := bbase (se 4 (by rfl) ⟨220908, by rfl⟩ : syracuseStep 2356357 = 441817) (by norm_num)
theorem B3141809 : Blo 2093435 3141809 := bstep (se 2 (by rfl) ⟨1178178, by rfl⟩ : syracuseStep 3141809 = 2356357) B2356357
theorem B2094539 : Blo 2093435 2094539 := bstep (se 1 (by rfl) ⟨1570904, by rfl⟩ : syracuseStep 2094539 = 3141809) B3141809
theorem B33969941 : Blo 2093435 33969941 := bbase (se 6 (by rfl) ⟨796170, by rfl⟩ : syracuseStep 33969941 = 1592341) (by norm_num)
theorem B22646627 : Blo 2093435 22646627 := bstep (se 1 (by rfl) ⟨16984970, by rfl⟩ : syracuseStep 22646627 = 33969941) B33969941
theorem B15097751 : Blo 2093435 15097751 := bstep (se 1 (by rfl) ⟨11323313, by rfl⟩ : syracuseStep 15097751 = 22646627) B22646627
theorem B10065167 : Blo 2093435 10065167 := bstep (se 1 (by rfl) ⟨7548875, by rfl⟩ : syracuseStep 10065167 = 15097751) B15097751
theorem B6710111 : Blo 2093435 6710111 := bstep (se 1 (by rfl) ⟨5032583, by rfl⟩ : syracuseStep 6710111 = 10065167) B10065167
theorem B4473407 : Blo 2093435 4473407 := bstep (se 1 (by rfl) ⟨3355055, by rfl⟩ : syracuseStep 4473407 = 6710111) B6710111
theorem B2982271 : Blo 2093435 2982271 := bstep (se 1 (by rfl) ⟨2236703, by rfl⟩ : syracuseStep 2982271 = 4473407) B4473407
theorem B3976361 : Blo 2093435 3976361 := bstep (se 2 (by rfl) ⟨1491135, by rfl⟩ : syracuseStep 3976361 = 2982271) B2982271
theorem B2650907 : Blo 2093435 2650907 := bstep (se 1 (by rfl) ⟨1988180, by rfl⟩ : syracuseStep 2650907 = 3976361) B3976361
theorem B7069085 : Blo 2093435 7069085 := bstep (se 3 (by rfl) ⟨1325453, by rfl⟩ : syracuseStep 7069085 = 2650907) B2650907
theorem B4712723 : Blo 2093435 4712723 := bstep (se 1 (by rfl) ⟨3534542, by rfl⟩ : syracuseStep 4712723 = 7069085) B7069085
theorem B3141815 : Blo 2093435 3141815 := bstep (se 1 (by rfl) ⟨2356361, by rfl⟩ : syracuseStep 3141815 = 4712723) B4712723
theorem B2094543 : Blo 2093435 2094543 := bstep (se 1 (by rfl) ⟨1570907, by rfl⟩ : syracuseStep 2094543 = 3141815) B3141815
theorem B3141821 : Blo 2093435 3141821 := bbase (se 3 (by rfl) ⟨589091, by rfl⟩ : syracuseStep 3141821 = 1178183) (by norm_num)
theorem B2094547 : Blo 2093435 2094547 := bstep (se 1 (by rfl) ⟨1570910, by rfl⟩ : syracuseStep 2094547 = 3141821) B3141821
theorem B4712741 : Blo 2093435 4712741 := bbase (se 4 (by rfl) ⟨441819, by rfl⟩ : syracuseStep 4712741 = 883639) (by norm_num)
theorem B3141827 : Blo 2093435 3141827 := bstep (se 1 (by rfl) ⟨2356370, by rfl⟩ : syracuseStep 3141827 = 4712741) B4712741
theorem B2094551 : Blo 2093435 2094551 := bstep (se 1 (by rfl) ⟨1570913, by rfl⟩ : syracuseStep 2094551 = 3141827) B3141827
theorem B5301845 : Blo 2093435 5301845 := bbase (se 8 (by rfl) ⟨31065, by rfl⟩ : syracuseStep 5301845 = 62131) (by norm_num)
theorem B3534563 : Blo 2093435 3534563 := bstep (se 1 (by rfl) ⟨2650922, by rfl⟩ : syracuseStep 3534563 = 5301845) B5301845
theorem B2356375 : Blo 2093435 2356375 := bstep (se 1 (by rfl) ⟨1767281, by rfl⟩ : syracuseStep 2356375 = 3534563) B3534563
theorem B3141833 : Blo 2093435 3141833 := bstep (se 2 (by rfl) ⟨1178187, by rfl⟩ : syracuseStep 3141833 = 2356375) B2356375
theorem B2094555 : Blo 2093435 2094555 := bstep (se 1 (by rfl) ⟨1570916, by rfl⟩ : syracuseStep 2094555 = 3141833) B3141833
theorem B5032621 : Blo 2093435 5032621 := bbase (se 3 (by rfl) ⟨943616, by rfl⟩ : syracuseStep 5032621 = 1887233) (by norm_num)
theorem B6710161 : Blo 2093435 6710161 := bstep (se 2 (by rfl) ⟨2516310, by rfl⟩ : syracuseStep 6710161 = 5032621) B5032621
theorem B8946881 : Blo 2093435 8946881 := bstep (se 2 (by rfl) ⟨3355080, by rfl⟩ : syracuseStep 8946881 = 6710161) B6710161
theorem B5964587 : Blo 2093435 5964587 := bstep (se 1 (by rfl) ⟨4473440, by rfl⟩ : syracuseStep 5964587 = 8946881) B8946881
theorem B3976391 : Blo 2093435 3976391 := bstep (se 1 (by rfl) ⟨2982293, by rfl⟩ : syracuseStep 3976391 = 5964587) B5964587
theorem B10603709 : Blo 2093435 10603709 := bstep (se 3 (by rfl) ⟨1988195, by rfl⟩ : syracuseStep 10603709 = 3976391) B3976391
theorem B7069139 : Blo 2093435 7069139 := bstep (se 1 (by rfl) ⟨5301854, by rfl⟩ : syracuseStep 7069139 = 10603709) B10603709
theorem B4712759 : Blo 2093435 4712759 := bstep (se 1 (by rfl) ⟨3534569, by rfl⟩ : syracuseStep 4712759 = 7069139) B7069139
theorem B3141839 : Blo 2093435 3141839 := bstep (se 1 (by rfl) ⟨2356379, by rfl⟩ : syracuseStep 3141839 = 4712759) B4712759
theorem B2094559 : Blo 2093435 2094559 := bstep (se 1 (by rfl) ⟨1570919, by rfl⟩ : syracuseStep 2094559 = 3141839) B3141839
theorem B3141845 : Blo 2093435 3141845 := bbase (se 7 (by rfl) ⟨36818, by rfl⟩ : syracuseStep 3141845 = 73637) (by norm_num)
theorem B2094563 : Blo 2093435 2094563 := bstep (se 1 (by rfl) ⟨1570922, by rfl⟩ : syracuseStep 2094563 = 3141845) B3141845
theorem B2236729 : Blo 2093435 2236729 := bbase (se 2 (by rfl) ⟨838773, by rfl⟩ : syracuseStep 2236729 = 1677547) (by norm_num)
theorem B2982305 : Blo 2093435 2982305 := bstep (se 2 (by rfl) ⟨1118364, by rfl⟩ : syracuseStep 2982305 = 2236729) B2236729
theorem B7952813 : Blo 2093435 7952813 := bstep (se 3 (by rfl) ⟨1491152, by rfl⟩ : syracuseStep 7952813 = 2982305) B2982305
theorem B5301875 : Blo 2093435 5301875 := bstep (se 1 (by rfl) ⟨3976406, by rfl⟩ : syracuseStep 5301875 = 7952813) B7952813
theorem B3534583 : Blo 2093435 3534583 := bstep (se 1 (by rfl) ⟨2650937, by rfl⟩ : syracuseStep 3534583 = 5301875) B5301875
theorem B4712777 : Blo 2093435 4712777 := bstep (se 2 (by rfl) ⟨1767291, by rfl⟩ : syracuseStep 4712777 = 3534583) B3534583
theorem B3141851 : Blo 2093435 3141851 := bstep (se 1 (by rfl) ⟨2356388, by rfl⟩ : syracuseStep 3141851 = 4712777) B4712777
theorem B2094567 : Blo 2093435 2094567 := bstep (se 1 (by rfl) ⟨1570925, by rfl⟩ : syracuseStep 2094567 = 3141851) B3141851
theorem B2356393 : Blo 2093435 2356393 := bbase (se 2 (by rfl) ⟨883647, by rfl⟩ : syracuseStep 2356393 = 1767295) (by norm_num)
theorem B3141857 : Blo 2093435 3141857 := bstep (se 2 (by rfl) ⟨1178196, by rfl⟩ : syracuseStep 3141857 = 2356393) B2356393
theorem B2094571 : Blo 2093435 2094571 := bstep (se 1 (by rfl) ⟨1570928, by rfl⟩ : syracuseStep 2094571 = 3141857) B3141857
theorem B8946949 : Blo 2093435 8946949 := bbase (se 4 (by rfl) ⟨838776, by rfl⟩ : syracuseStep 8946949 = 1677553) (by norm_num)
theorem B11929265 : Blo 2093435 11929265 := bstep (se 2 (by rfl) ⟨4473474, by rfl⟩ : syracuseStep 11929265 = 8946949) B8946949
theorem B7952843 : Blo 2093435 7952843 := bstep (se 1 (by rfl) ⟨5964632, by rfl⟩ : syracuseStep 7952843 = 11929265) B11929265
theorem B5301895 : Blo 2093435 5301895 := bstep (se 1 (by rfl) ⟨3976421, by rfl⟩ : syracuseStep 5301895 = 7952843) B7952843
theorem B7069193 : Blo 2093435 7069193 := bstep (se 2 (by rfl) ⟨2650947, by rfl⟩ : syracuseStep 7069193 = 5301895) B5301895
theorem B4712795 : Blo 2093435 4712795 := bstep (se 1 (by rfl) ⟨3534596, by rfl⟩ : syracuseStep 4712795 = 7069193) B7069193
theorem B3141863 : Blo 2093435 3141863 := bstep (se 1 (by rfl) ⟨2356397, by rfl⟩ : syracuseStep 3141863 = 4712795) B4712795
theorem B2094575 : Blo 2093435 2094575 := bstep (se 1 (by rfl) ⟨1570931, by rfl⟩ : syracuseStep 2094575 = 3141863) B3141863
theorem B3141869 : Blo 2093435 3141869 := bbase (se 3 (by rfl) ⟨589100, by rfl⟩ : syracuseStep 3141869 = 1178201) (by norm_num)
theorem B2094579 : Blo 2093435 2094579 := bstep (se 1 (by rfl) ⟨1570934, by rfl⟩ : syracuseStep 2094579 = 3141869) B3141869
theorem B4712813 : Blo 2093435 4712813 := bbase (se 3 (by rfl) ⟨883652, by rfl⟩ : syracuseStep 4712813 = 1767305) (by norm_num)
theorem B3141875 : Blo 2093435 3141875 := bstep (se 1 (by rfl) ⟨2356406, by rfl⟩ : syracuseStep 3141875 = 4712813) B4712813
theorem B2094583 : Blo 2093435 2094583 := bstep (se 1 (by rfl) ⟨1570937, by rfl⟩ : syracuseStep 2094583 = 3141875) B3141875
theorem B3976445 : Blo 2093435 3976445 := bbase (se 3 (by rfl) ⟨745583, by rfl⟩ : syracuseStep 3976445 = 1491167) (by norm_num)
theorem B2650963 : Blo 2093435 2650963 := bstep (se 1 (by rfl) ⟨1988222, by rfl⟩ : syracuseStep 2650963 = 3976445) B3976445
theorem B3534617 : Blo 2093435 3534617 := bstep (se 2 (by rfl) ⟨1325481, by rfl⟩ : syracuseStep 3534617 = 2650963) B2650963
theorem B2356411 : Blo 2093435 2356411 := bstep (se 1 (by rfl) ⟨1767308, by rfl⟩ : syracuseStep 2356411 = 3534617) B3534617
theorem B3141881 : Blo 2093435 3141881 := bstep (se 2 (by rfl) ⟨1178205, by rfl⟩ : syracuseStep 3141881 = 2356411) B2356411
theorem B2094587 : Blo 2093435 2094587 := bstep (se 1 (by rfl) ⟨1570940, by rfl⟩ : syracuseStep 2094587 = 3141881) B3141881
theorem B6369509 : Blo 2093435 6369509 := bbase (se 4 (by rfl) ⟨597141, by rfl⟩ : syracuseStep 6369509 = 1194283) (by norm_num)
theorem B4246339 : Blo 2093435 4246339 := bstep (se 1 (by rfl) ⟨3184754, by rfl⟩ : syracuseStep 4246339 = 6369509) B6369509
theorem B5661785 : Blo 2093435 5661785 := bstep (se 2 (by rfl) ⟨2123169, by rfl⟩ : syracuseStep 5661785 = 4246339) B4246339
theorem B3774523 : Blo 2093435 3774523 := bstep (se 1 (by rfl) ⟨2830892, by rfl⟩ : syracuseStep 3774523 = 5661785) B5661785
theorem B5032697 : Blo 2093435 5032697 := bstep (se 2 (by rfl) ⟨1887261, by rfl⟩ : syracuseStep 5032697 = 3774523) B3774523
theorem B53682101 : Blo 2093435 53682101 := bstep (se 5 (by rfl) ⟨2516348, by rfl⟩ : syracuseStep 53682101 = 5032697) B5032697
theorem B35788067 : Blo 2093435 35788067 := bstep (se 1 (by rfl) ⟨26841050, by rfl⟩ : syracuseStep 35788067 = 53682101) B53682101
theorem B23858711 : Blo 2093435 23858711 := bstep (se 1 (by rfl) ⟨17894033, by rfl⟩ : syracuseStep 23858711 = 35788067) B35788067
theorem B15905807 : Blo 2093435 15905807 := bstep (se 1 (by rfl) ⟨11929355, by rfl⟩ : syracuseStep 15905807 = 23858711) B23858711
theorem B10603871 : Blo 2093435 10603871 := bstep (se 1 (by rfl) ⟨7952903, by rfl⟩ : syracuseStep 10603871 = 15905807) B15905807
theorem B7069247 : Blo 2093435 7069247 := bstep (se 1 (by rfl) ⟨5301935, by rfl⟩ : syracuseStep 7069247 = 10603871) B10603871
theorem B4712831 : Blo 2093435 4712831 := bstep (se 1 (by rfl) ⟨3534623, by rfl⟩ : syracuseStep 4712831 = 7069247) B7069247
theorem B3141887 : Blo 2093435 3141887 := bstep (se 1 (by rfl) ⟨2356415, by rfl⟩ : syracuseStep 3141887 = 4712831) B4712831
theorem B2094591 : Blo 2093435 2094591 := bstep (se 1 (by rfl) ⟨1570943, by rfl⟩ : syracuseStep 2094591 = 3141887) B3141887
theorem B3141893 : Blo 2093435 3141893 := bbase (se 4 (by rfl) ⟨294552, by rfl⟩ : syracuseStep 3141893 = 589105) (by norm_num)
theorem B2094595 : Blo 2093435 2094595 := bstep (se 1 (by rfl) ⟨1570946, by rfl⟩ : syracuseStep 2094595 = 3141893) B3141893
theorem B3534637 : Blo 2093435 3534637 := bbase (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) (by norm_num)
theorem B4712849 : Blo 2093435 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B3141899 : Blo 2093435 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B2094599 : Blo 2093435 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B2356429 : Blo 2093435 2356429 := bbase (se 3 (by rfl) ⟨441830, by rfl⟩ : syracuseStep 2356429 = 883661) (by norm_num)
theorem B3141905 : Blo 2093435 3141905 := bstep (se 2 (by rfl) ⟨1178214, by rfl⟩ : syracuseStep 3141905 = 2356429) B2356429
theorem B2094603 : Blo 2093435 2094603 := bstep (se 1 (by rfl) ⟨1570952, by rfl⟩ : syracuseStep 2094603 = 3141905) B3141905
theorem B7069301 : Blo 2093435 7069301 := bbase (se 5 (by rfl) ⟨331373, by rfl⟩ : syracuseStep 7069301 = 662747) (by norm_num)
theorem B4712867 : Blo 2093435 4712867 := bstep (se 1 (by rfl) ⟨3534650, by rfl⟩ : syracuseStep 4712867 = 7069301) B7069301
theorem B3141911 : Blo 2093435 3141911 := bstep (se 1 (by rfl) ⟨2356433, by rfl⟩ : syracuseStep 3141911 = 4712867) B4712867
theorem B2094607 : Blo 2093435 2094607 := bstep (se 1 (by rfl) ⟨1570955, by rfl⟩ : syracuseStep 2094607 = 3141911) B3141911
theorem B3141917 : Blo 2093435 3141917 := bbase (se 3 (by rfl) ⟨589109, by rfl⟩ : syracuseStep 3141917 = 1178219) (by norm_num)
theorem B2094611 : Blo 2093435 2094611 := bstep (se 1 (by rfl) ⟨1570958, by rfl⟩ : syracuseStep 2094611 = 3141917) B3141917
theorem B4712885 : Blo 2093435 4712885 := bbase (se 5 (by rfl) ⟨220916, by rfl⟩ : syracuseStep 4712885 = 441833) (by norm_num)
theorem B3141923 : Blo 2093435 3141923 := bstep (se 1 (by rfl) ⟨2356442, by rfl⟩ : syracuseStep 3141923 = 4712885) B4712885
theorem B2094615 : Blo 2093435 2094615 := bstep (se 1 (by rfl) ⟨1570961, by rfl⟩ : syracuseStep 2094615 = 3141923) B3141923
theorem B2487709 : Blo 2093435 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B3316945 : Blo 2093435 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B4422593 : Blo 2093435 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2948395 : Blo 2093435 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B3931193 : Blo 2093435 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B10483181 : Blo 2093435 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B6988787 : Blo 2093435 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B4659191 : Blo 2093435 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B3106127 : Blo 2093435 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B8283005 : Blo 2093435 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B5522003 : Blo 2093435 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B3681335 : Blo 2093435 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B2454223 : Blo 2093435 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B3272297 : Blo 2093435 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B8726125 : Blo 2093435 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B11634833 : Blo 2093435 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B7756555 : Blo 2093435 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B10342073 : Blo 2093435 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B6894715 : Blo 2093435 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B9192953 : Blo 2093435 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B6128635 : Blo 2093435 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B8171513 : Blo 2093435 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B5447675 : Blo 2093435 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B14527133 : Blo 2093435 14527133 := bstep (se 3 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 14527133 = 5447675) B5447675
theorem B9684755 : Blo 2093435 9684755 := bstep (se 1 (by rfl) ⟨7263566, by rfl⟩ : syracuseStep 9684755 = 14527133) B14527133
theorem B6456503 : Blo 2093435 6456503 := bstep (se 1 (by rfl) ⟨4842377, by rfl⟩ : syracuseStep 6456503 = 9684755) B9684755
theorem B4304335 : Blo 2093435 4304335 := bstep (se 1 (by rfl) ⟨3228251, by rfl⟩ : syracuseStep 4304335 = 6456503) B6456503
theorem B5739113 : Blo 2093435 5739113 := bstep (se 2 (by rfl) ⟨2152167, by rfl⟩ : syracuseStep 5739113 = 4304335) B4304335
theorem B3826075 : Blo 2093435 3826075 := bstep (se 1 (by rfl) ⟨2869556, by rfl⟩ : syracuseStep 3826075 = 5739113) B5739113
theorem B5101433 : Blo 2093435 5101433 := bstep (se 2 (by rfl) ⟨1913037, by rfl⟩ : syracuseStep 5101433 = 3826075) B3826075
theorem B3400955 : Blo 2093435 3400955 := bstep (se 1 (by rfl) ⟨2550716, by rfl⟩ : syracuseStep 3400955 = 5101433) B5101433
theorem B2267303 : Blo 2093435 2267303 := bstep (se 1 (by rfl) ⟨1700477, by rfl⟩ : syracuseStep 2267303 = 3400955) B3400955
theorem B24184565 : Blo 2093435 24184565 := bstep (se 5 (by rfl) ⟨1133651, by rfl⟩ : syracuseStep 24184565 = 2267303) B2267303
theorem B16123043 : Blo 2093435 16123043 := bstep (se 1 (by rfl) ⟨12092282, by rfl⟩ : syracuseStep 16123043 = 24184565) B24184565
theorem B10748695 : Blo 2093435 10748695 := bstep (se 1 (by rfl) ⟨8061521, by rfl⟩ : syracuseStep 10748695 = 16123043) B16123043
theorem B14331593 : Blo 2093435 14331593 := bstep (se 2 (by rfl) ⟨5374347, by rfl⟩ : syracuseStep 14331593 = 10748695) B10748695
theorem B9554395 : Blo 2093435 9554395 := bstep (se 1 (by rfl) ⟨7165796, by rfl⟩ : syracuseStep 9554395 = 14331593) B14331593
theorem B12739193 : Blo 2093435 12739193 := bstep (se 2 (by rfl) ⟨4777197, by rfl⟩ : syracuseStep 12739193 = 9554395) B9554395
theorem B8492795 : Blo 2093435 8492795 := bstep (se 1 (by rfl) ⟨6369596, by rfl⟩ : syracuseStep 8492795 = 12739193) B12739193
theorem B5661863 : Blo 2093435 5661863 := bstep (se 1 (by rfl) ⟨4246397, by rfl⟩ : syracuseStep 5661863 = 8492795) B8492795
theorem B3774575 : Blo 2093435 3774575 := bstep (se 1 (by rfl) ⟨2830931, by rfl⟩ : syracuseStep 3774575 = 5661863) B5661863
theorem B2516383 : Blo 2093435 2516383 := bstep (se 1 (by rfl) ⟨1887287, by rfl⟩ : syracuseStep 2516383 = 3774575) B3774575
theorem B3355177 : Blo 2093435 3355177 := bstep (se 2 (by rfl) ⟨1258191, by rfl⟩ : syracuseStep 3355177 = 2516383) B2516383
theorem B4473569 : Blo 2093435 4473569 := bstep (se 2 (by rfl) ⟨1677588, by rfl⟩ : syracuseStep 4473569 = 3355177) B3355177
theorem B11929517 : Blo 2093435 11929517 := bstep (se 3 (by rfl) ⟨2236784, by rfl⟩ : syracuseStep 11929517 = 4473569) B4473569
theorem B7953011 : Blo 2093435 7953011 := bstep (se 1 (by rfl) ⟨5964758, by rfl⟩ : syracuseStep 7953011 = 11929517) B11929517
theorem B5302007 : Blo 2093435 5302007 := bstep (se 1 (by rfl) ⟨3976505, by rfl⟩ : syracuseStep 5302007 = 7953011) B7953011
theorem B3534671 : Blo 2093435 3534671 := bstep (se 1 (by rfl) ⟨2651003, by rfl⟩ : syracuseStep 3534671 = 5302007) B5302007
theorem B2356447 : Blo 2093435 2356447 := bstep (se 1 (by rfl) ⟨1767335, by rfl⟩ : syracuseStep 2356447 = 3534671) B3534671
theorem B3141929 : Blo 2093435 3141929 := bstep (se 2 (by rfl) ⟨1178223, by rfl⟩ : syracuseStep 3141929 = 2356447) B2356447
theorem B2094619 : Blo 2093435 2094619 := bstep (se 1 (by rfl) ⟨1570964, by rfl⟩ : syracuseStep 2094619 = 3141929) B3141929
theorem B4304341 : Blo 2093435 4304341 := bbase (se 7 (by rfl) ⟨50441, by rfl⟩ : syracuseStep 4304341 = 100883) (by norm_num)
theorem B5739121 : Blo 2093435 5739121 := bstep (se 2 (by rfl) ⟨2152170, by rfl⟩ : syracuseStep 5739121 = 4304341) B4304341
theorem B7652161 : Blo 2093435 7652161 := bstep (se 2 (by rfl) ⟨2869560, by rfl⟩ : syracuseStep 7652161 = 5739121) B5739121
theorem B40811525 : Blo 2093435 40811525 := bstep (se 4 (by rfl) ⟨3826080, by rfl⟩ : syracuseStep 40811525 = 7652161) B7652161
theorem B27207683 : Blo 2093435 27207683 := bstep (se 1 (by rfl) ⟨20405762, by rfl⟩ : syracuseStep 27207683 = 40811525) B40811525
theorem B18138455 : Blo 2093435 18138455 := bstep (se 1 (by rfl) ⟨13603841, by rfl⟩ : syracuseStep 18138455 = 27207683) B27207683
theorem B12092303 : Blo 2093435 12092303 := bstep (se 1 (by rfl) ⟨9069227, by rfl⟩ : syracuseStep 12092303 = 18138455) B18138455
theorem B8061535 : Blo 2093435 8061535 := bstep (se 1 (by rfl) ⟨6046151, by rfl⟩ : syracuseStep 8061535 = 12092303) B12092303
theorem B10748713 : Blo 2093435 10748713 := bstep (se 2 (by rfl) ⟨4030767, by rfl⟩ : syracuseStep 10748713 = 8061535) B8061535
theorem B14331617 : Blo 2093435 14331617 := bstep (se 2 (by rfl) ⟨5374356, by rfl⟩ : syracuseStep 14331617 = 10748713) B10748713
theorem B9554411 : Blo 2093435 9554411 := bstep (se 1 (by rfl) ⟨7165808, by rfl⟩ : syracuseStep 9554411 = 14331617) B14331617
theorem B6369607 : Blo 2093435 6369607 := bstep (se 1 (by rfl) ⟨4777205, by rfl⟩ : syracuseStep 6369607 = 9554411) B9554411
theorem B8492809 : Blo 2093435 8492809 := bstep (se 2 (by rfl) ⟨3184803, by rfl⟩ : syracuseStep 8492809 = 6369607) B6369607
theorem B11323745 : Blo 2093435 11323745 := bstep (se 2 (by rfl) ⟨4246404, by rfl⟩ : syracuseStep 11323745 = 8492809) B8492809
theorem B7549163 : Blo 2093435 7549163 := bstep (se 1 (by rfl) ⟨5661872, by rfl⟩ : syracuseStep 7549163 = 11323745) B11323745
theorem B5032775 : Blo 2093435 5032775 := bstep (se 1 (by rfl) ⟨3774581, by rfl⟩ : syracuseStep 5032775 = 7549163) B7549163
theorem B3355183 : Blo 2093435 3355183 := bstep (se 1 (by rfl) ⟨2516387, by rfl⟩ : syracuseStep 3355183 = 5032775) B5032775
theorem B4473577 : Blo 2093435 4473577 := bstep (se 2 (by rfl) ⟨1677591, by rfl⟩ : syracuseStep 4473577 = 3355183) B3355183
theorem B5964769 : Blo 2093435 5964769 := bstep (se 2 (by rfl) ⟨2236788, by rfl⟩ : syracuseStep 5964769 = 4473577) B4473577
theorem B7953025 : Blo 2093435 7953025 := bstep (se 2 (by rfl) ⟨2982384, by rfl⟩ : syracuseStep 7953025 = 5964769) B5964769
theorem B10604033 : Blo 2093435 10604033 := bstep (se 2 (by rfl) ⟨3976512, by rfl⟩ : syracuseStep 10604033 = 7953025) B7953025
theorem B7069355 : Blo 2093435 7069355 := bstep (se 1 (by rfl) ⟨5302016, by rfl⟩ : syracuseStep 7069355 = 10604033) B10604033
theorem B4712903 : Blo 2093435 4712903 := bstep (se 1 (by rfl) ⟨3534677, by rfl⟩ : syracuseStep 4712903 = 7069355) B7069355
theorem B3141935 : Blo 2093435 3141935 := bstep (se 1 (by rfl) ⟨2356451, by rfl⟩ : syracuseStep 3141935 = 4712903) B4712903
theorem B2094623 : Blo 2093435 2094623 := bstep (se 1 (by rfl) ⟨1570967, by rfl⟩ : syracuseStep 2094623 = 3141935) B3141935
theorem B3141941 : Blo 2093435 3141941 := bbase (se 5 (by rfl) ⟨147278, by rfl⟩ : syracuseStep 3141941 = 294557) (by norm_num)
theorem B2094627 : Blo 2093435 2094627 := bstep (se 1 (by rfl) ⟨1570970, by rfl⟩ : syracuseStep 2094627 = 3141941) B3141941
theorem B5302037 : Blo 2093435 5302037 := bbase (se 6 (by rfl) ⟨124266, by rfl⟩ : syracuseStep 5302037 = 248533) (by norm_num)
theorem B3534691 : Blo 2093435 3534691 := bstep (se 1 (by rfl) ⟨2651018, by rfl⟩ : syracuseStep 3534691 = 5302037) B5302037
theorem B4712921 : Blo 2093435 4712921 := bstep (se 2 (by rfl) ⟨1767345, by rfl⟩ : syracuseStep 4712921 = 3534691) B3534691
theorem B3141947 : Blo 2093435 3141947 := bstep (se 1 (by rfl) ⟨2356460, by rfl⟩ : syracuseStep 3141947 = 4712921) B4712921
theorem B2094631 : Blo 2093435 2094631 := bstep (se 1 (by rfl) ⟨1570973, by rfl⟩ : syracuseStep 2094631 = 3141947) B3141947
theorem B2356465 : Blo 2093435 2356465 := bbase (se 2 (by rfl) ⟨883674, by rfl⟩ : syracuseStep 2356465 = 1767349) (by norm_num)
theorem B3141953 : Blo 2093435 3141953 := bstep (se 2 (by rfl) ⟨1178232, by rfl⟩ : syracuseStep 3141953 = 2356465) B2356465
theorem B2094635 : Blo 2093435 2094635 := bstep (se 1 (by rfl) ⟨1570976, by rfl⟩ : syracuseStep 2094635 = 3141953) B3141953
theorem B20131253 : Blo 2093435 20131253 := bbase (se 5 (by rfl) ⟨943652, by rfl⟩ : syracuseStep 20131253 = 1887305) (by norm_num)
theorem B13420835 : Blo 2093435 13420835 := bstep (se 1 (by rfl) ⟨10065626, by rfl⟩ : syracuseStep 13420835 = 20131253) B20131253
theorem B8947223 : Blo 2093435 8947223 := bstep (se 1 (by rfl) ⟨6710417, by rfl⟩ : syracuseStep 8947223 = 13420835) B13420835
theorem B5964815 : Blo 2093435 5964815 := bstep (se 1 (by rfl) ⟨4473611, by rfl⟩ : syracuseStep 5964815 = 8947223) B8947223
theorem B3976543 : Blo 2093435 3976543 := bstep (se 1 (by rfl) ⟨2982407, by rfl⟩ : syracuseStep 3976543 = 5964815) B5964815
theorem B5302057 : Blo 2093435 5302057 := bstep (se 2 (by rfl) ⟨1988271, by rfl⟩ : syracuseStep 5302057 = 3976543) B3976543
theorem B7069409 : Blo 2093435 7069409 := bstep (se 2 (by rfl) ⟨2651028, by rfl⟩ : syracuseStep 7069409 = 5302057) B5302057
theorem B4712939 : Blo 2093435 4712939 := bstep (se 1 (by rfl) ⟨3534704, by rfl⟩ : syracuseStep 4712939 = 7069409) B7069409
theorem B3141959 : Blo 2093435 3141959 := bstep (se 1 (by rfl) ⟨2356469, by rfl⟩ : syracuseStep 3141959 = 4712939) B4712939
theorem B2094639 : Blo 2093435 2094639 := bstep (se 1 (by rfl) ⟨1570979, by rfl⟩ : syracuseStep 2094639 = 3141959) B3141959
theorem B3141965 : Blo 2093435 3141965 := bbase (se 3 (by rfl) ⟨589118, by rfl⟩ : syracuseStep 3141965 = 1178237) (by norm_num)
theorem B2094643 : Blo 2093435 2094643 := bstep (se 1 (by rfl) ⟨1570982, by rfl⟩ : syracuseStep 2094643 = 3141965) B3141965
theorem B4712957 : Blo 2093435 4712957 := bbase (se 3 (by rfl) ⟨883679, by rfl⟩ : syracuseStep 4712957 = 1767359) (by norm_num)
theorem B3141971 : Blo 2093435 3141971 := bstep (se 1 (by rfl) ⟨2356478, by rfl⟩ : syracuseStep 3141971 = 4712957) B4712957
theorem B2094647 : Blo 2093435 2094647 := bstep (se 1 (by rfl) ⟨1570985, by rfl⟩ : syracuseStep 2094647 = 3141971) B3141971
theorem B3534725 : Blo 2093435 3534725 := bbase (se 4 (by rfl) ⟨331380, by rfl⟩ : syracuseStep 3534725 = 662761) (by norm_num)
theorem B2356483 : Blo 2093435 2356483 := bstep (se 1 (by rfl) ⟨1767362, by rfl⟩ : syracuseStep 2356483 = 3534725) B3534725
theorem B3141977 : Blo 2093435 3141977 := bstep (se 2 (by rfl) ⟨1178241, by rfl⟩ : syracuseStep 3141977 = 2356483) B2356483
theorem B2094651 : Blo 2093435 2094651 := bstep (se 1 (by rfl) ⟨1570988, by rfl⟩ : syracuseStep 2094651 = 3141977) B3141977
theorem B15906293 : Blo 2093435 15906293 := bbase (se 5 (by rfl) ⟨745607, by rfl⟩ : syracuseStep 15906293 = 1491215) (by norm_num)
theorem B10604195 : Blo 2093435 10604195 := bstep (se 1 (by rfl) ⟨7953146, by rfl⟩ : syracuseStep 10604195 = 15906293) B15906293
theorem B7069463 : Blo 2093435 7069463 := bstep (se 1 (by rfl) ⟨5302097, by rfl⟩ : syracuseStep 7069463 = 10604195) B10604195
theorem B4712975 : Blo 2093435 4712975 := bstep (se 1 (by rfl) ⟨3534731, by rfl⟩ : syracuseStep 4712975 = 7069463) B7069463
theorem B3141983 : Blo 2093435 3141983 := bstep (se 1 (by rfl) ⟨2356487, by rfl⟩ : syracuseStep 3141983 = 4712975) B4712975
theorem B2094655 : Blo 2093435 2094655 := bstep (se 1 (by rfl) ⟨1570991, by rfl⟩ : syracuseStep 2094655 = 3141983) B3141983
theorem B3141989 : Blo 2093435 3141989 := bbase (se 4 (by rfl) ⟨294561, by rfl⟩ : syracuseStep 3141989 = 589123) (by norm_num)
theorem B2094659 : Blo 2093435 2094659 := bstep (se 1 (by rfl) ⟨1570994, by rfl⟩ : syracuseStep 2094659 = 3141989) B3141989
theorem B3976589 : Blo 2093435 3976589 := bbase (se 3 (by rfl) ⟨745610, by rfl⟩ : syracuseStep 3976589 = 1491221) (by norm_num)
theorem B2651059 : Blo 2093435 2651059 := bstep (se 1 (by rfl) ⟨1988294, by rfl⟩ : syracuseStep 2651059 = 3976589) B3976589
theorem B3534745 : Blo 2093435 3534745 := bstep (se 2 (by rfl) ⟨1325529, by rfl⟩ : syracuseStep 3534745 = 2651059) B2651059
theorem B4712993 : Blo 2093435 4712993 := bstep (se 2 (by rfl) ⟨1767372, by rfl⟩ : syracuseStep 4712993 = 3534745) B3534745
theorem B3141995 : Blo 2093435 3141995 := bstep (se 1 (by rfl) ⟨2356496, by rfl⟩ : syracuseStep 3141995 = 4712993) B4712993
theorem B2094663 : Blo 2093435 2094663 := bstep (se 1 (by rfl) ⟨1570997, by rfl⟩ : syracuseStep 2094663 = 3141995) B3141995
theorem B2356501 : Blo 2093435 2356501 := bbase (se 6 (by rfl) ⟨55230, by rfl⟩ : syracuseStep 2356501 = 110461) (by norm_num)
theorem B3142001 : Blo 2093435 3142001 := bstep (se 2 (by rfl) ⟨1178250, by rfl⟩ : syracuseStep 3142001 = 2356501) B2356501
theorem B2094667 : Blo 2093435 2094667 := bstep (se 1 (by rfl) ⟨1571000, by rfl⟩ : syracuseStep 2094667 = 3142001) B3142001
theorem B2651069 : Blo 2093435 2651069 := bbase (se 3 (by rfl) ⟨497075, by rfl⟩ : syracuseStep 2651069 = 994151) (by norm_num)
theorem B7069517 : Blo 2093435 7069517 := bstep (se 3 (by rfl) ⟨1325534, by rfl⟩ : syracuseStep 7069517 = 2651069) B2651069
theorem B4713011 : Blo 2093435 4713011 := bstep (se 1 (by rfl) ⟨3534758, by rfl⟩ : syracuseStep 4713011 = 7069517) B7069517
theorem B3142007 : Blo 2093435 3142007 := bstep (se 1 (by rfl) ⟨2356505, by rfl⟩ : syracuseStep 3142007 = 4713011) B4713011
theorem B2094671 : Blo 2093435 2094671 := bstep (se 1 (by rfl) ⟨1571003, by rfl⟩ : syracuseStep 2094671 = 3142007) B3142007
theorem B3142013 : Blo 2093435 3142013 := bbase (se 3 (by rfl) ⟨589127, by rfl⟩ : syracuseStep 3142013 = 1178255) (by norm_num)
theorem B2094675 : Blo 2093435 2094675 := bstep (se 1 (by rfl) ⟨1571006, by rfl⟩ : syracuseStep 2094675 = 3142013) B3142013
theorem B4713029 : Blo 2093435 4713029 := bbase (se 4 (by rfl) ⟨441846, by rfl⟩ : syracuseStep 4713029 = 883693) (by norm_num)
theorem B3142019 : Blo 2093435 3142019 := bstep (se 1 (by rfl) ⟨2356514, by rfl⟩ : syracuseStep 3142019 = 4713029) B4713029
theorem B2094679 : Blo 2093435 2094679 := bstep (se 1 (by rfl) ⟨1571009, by rfl⟩ : syracuseStep 2094679 = 3142019) B3142019
theorem B2236853 : Blo 2093435 2236853 := bbase (se 5 (by rfl) ⟨104852, by rfl⟩ : syracuseStep 2236853 = 209705) (by norm_num)
theorem B5964941 : Blo 2093435 5964941 := bstep (se 3 (by rfl) ⟨1118426, by rfl⟩ : syracuseStep 5964941 = 2236853) B2236853
theorem B3976627 : Blo 2093435 3976627 := bstep (se 1 (by rfl) ⟨2982470, by rfl⟩ : syracuseStep 3976627 = 5964941) B5964941
theorem B5302169 : Blo 2093435 5302169 := bstep (se 2 (by rfl) ⟨1988313, by rfl⟩ : syracuseStep 5302169 = 3976627) B3976627
theorem B3534779 : Blo 2093435 3534779 := bstep (se 1 (by rfl) ⟨2651084, by rfl⟩ : syracuseStep 3534779 = 5302169) B5302169
theorem B2356519 : Blo 2093435 2356519 := bstep (se 1 (by rfl) ⟨1767389, by rfl⟩ : syracuseStep 2356519 = 3534779) B3534779
theorem B3142025 : Blo 2093435 3142025 := bstep (se 2 (by rfl) ⟨1178259, by rfl⟩ : syracuseStep 3142025 = 2356519) B2356519
theorem B2094683 : Blo 2093435 2094683 := bstep (se 1 (by rfl) ⟨1571012, by rfl⟩ : syracuseStep 2094683 = 3142025) B3142025
theorem B10604357 : Blo 2093435 10604357 := bbase (se 4 (by rfl) ⟨994158, by rfl⟩ : syracuseStep 10604357 = 1988317) (by norm_num)
theorem B7069571 : Blo 2093435 7069571 := bstep (se 1 (by rfl) ⟨5302178, by rfl⟩ : syracuseStep 7069571 = 10604357) B10604357
theorem B4713047 : Blo 2093435 4713047 := bstep (se 1 (by rfl) ⟨3534785, by rfl⟩ : syracuseStep 4713047 = 7069571) B7069571
theorem B3142031 : Blo 2093435 3142031 := bstep (se 1 (by rfl) ⟨2356523, by rfl⟩ : syracuseStep 3142031 = 4713047) B4713047
theorem B2094687 : Blo 2093435 2094687 := bstep (se 1 (by rfl) ⟨1571015, by rfl⟩ : syracuseStep 2094687 = 3142031) B3142031
theorem B3142037 : Blo 2093435 3142037 := bbase (se 6 (by rfl) ⟨73641, by rfl⟩ : syracuseStep 3142037 = 147283) (by norm_num)
theorem B2094691 : Blo 2093435 2094691 := bstep (se 1 (by rfl) ⟨1571018, by rfl⟩ : syracuseStep 2094691 = 3142037) B3142037
theorem B6710597 : Blo 2093435 6710597 := bbase (se 4 (by rfl) ⟨629118, by rfl⟩ : syracuseStep 6710597 = 1258237) (by norm_num)
theorem B4473731 : Blo 2093435 4473731 := bstep (se 1 (by rfl) ⟨3355298, by rfl⟩ : syracuseStep 4473731 = 6710597) B6710597
theorem B11929949 : Blo 2093435 11929949 := bstep (se 3 (by rfl) ⟨2236865, by rfl⟩ : syracuseStep 11929949 = 4473731) B4473731
theorem B7953299 : Blo 2093435 7953299 := bstep (se 1 (by rfl) ⟨5964974, by rfl⟩ : syracuseStep 7953299 = 11929949) B11929949
theorem B5302199 : Blo 2093435 5302199 := bstep (se 1 (by rfl) ⟨3976649, by rfl⟩ : syracuseStep 5302199 = 7953299) B7953299
theorem B3534799 : Blo 2093435 3534799 := bstep (se 1 (by rfl) ⟨2651099, by rfl⟩ : syracuseStep 3534799 = 5302199) B5302199
theorem B4713065 : Blo 2093435 4713065 := bstep (se 2 (by rfl) ⟨1767399, by rfl⟩ : syracuseStep 4713065 = 3534799) B3534799
theorem B3142043 : Blo 2093435 3142043 := bstep (se 1 (by rfl) ⟨2356532, by rfl⟩ : syracuseStep 3142043 = 4713065) B4713065
theorem B2094695 : Blo 2093435 2094695 := bstep (se 1 (by rfl) ⟨1571021, by rfl⟩ : syracuseStep 2094695 = 3142043) B3142043
theorem B2356537 : Blo 2093435 2356537 := bbase (se 2 (by rfl) ⟨883701, by rfl⟩ : syracuseStep 2356537 = 1767403) (by norm_num)
theorem B3142049 : Blo 2093435 3142049 := bstep (se 2 (by rfl) ⟨1178268, by rfl⟩ : syracuseStep 3142049 = 2356537) B2356537
theorem B2094699 : Blo 2093435 2094699 := bstep (se 1 (by rfl) ⟨1571024, by rfl⟩ : syracuseStep 2094699 = 3142049) B3142049
theorem B5964997 : Blo 2093435 5964997 := bbase (se 4 (by rfl) ⟨559218, by rfl⟩ : syracuseStep 5964997 = 1118437) (by norm_num)
theorem B7953329 : Blo 2093435 7953329 := bstep (se 2 (by rfl) ⟨2982498, by rfl⟩ : syracuseStep 7953329 = 5964997) B5964997
theorem B5302219 : Blo 2093435 5302219 := bstep (se 1 (by rfl) ⟨3976664, by rfl⟩ : syracuseStep 5302219 = 7953329) B7953329
theorem B7069625 : Blo 2093435 7069625 := bstep (se 2 (by rfl) ⟨2651109, by rfl⟩ : syracuseStep 7069625 = 5302219) B5302219
theorem B4713083 : Blo 2093435 4713083 := bstep (se 1 (by rfl) ⟨3534812, by rfl⟩ : syracuseStep 4713083 = 7069625) B7069625
theorem B3142055 : Blo 2093435 3142055 := bstep (se 1 (by rfl) ⟨2356541, by rfl⟩ : syracuseStep 3142055 = 4713083) B4713083
theorem B2094703 : Blo 2093435 2094703 := bstep (se 1 (by rfl) ⟨1571027, by rfl⟩ : syracuseStep 2094703 = 3142055) B3142055
theorem B3142061 : Blo 2093435 3142061 := bbase (se 3 (by rfl) ⟨589136, by rfl⟩ : syracuseStep 3142061 = 1178273) (by norm_num)
theorem B2094707 : Blo 2093435 2094707 := bstep (se 1 (by rfl) ⟨1571030, by rfl⟩ : syracuseStep 2094707 = 3142061) B3142061
theorem B4713101 : Blo 2093435 4713101 := bbase (se 3 (by rfl) ⟨883706, by rfl⟩ : syracuseStep 4713101 = 1767413) (by norm_num)
theorem B3142067 : Blo 2093435 3142067 := bstep (se 1 (by rfl) ⟨2356550, by rfl⟩ : syracuseStep 3142067 = 4713101) B4713101
theorem B2094711 : Blo 2093435 2094711 := bstep (se 1 (by rfl) ⟨1571033, by rfl⟩ : syracuseStep 2094711 = 3142067) B3142067
theorem B2651125 : Blo 2093435 2651125 := bbase (se 5 (by rfl) ⟨124271, by rfl⟩ : syracuseStep 2651125 = 248543) (by norm_num)
theorem B3534833 : Blo 2093435 3534833 := bstep (se 2 (by rfl) ⟨1325562, by rfl⟩ : syracuseStep 3534833 = 2651125) B2651125
theorem B2356555 : Blo 2093435 2356555 := bstep (se 1 (by rfl) ⟨1767416, by rfl⟩ : syracuseStep 2356555 = 3534833) B3534833
theorem B3142073 : Blo 2093435 3142073 := bstep (se 2 (by rfl) ⟨1178277, by rfl⟩ : syracuseStep 3142073 = 2356555) B2356555
theorem B2094715 : Blo 2093435 2094715 := bstep (se 1 (by rfl) ⟨1571036, by rfl⟩ : syracuseStep 2094715 = 3142073) B3142073
theorem B3184949 : Blo 2093435 3184949 := bbase (se 5 (by rfl) ⟨149294, by rfl⟩ : syracuseStep 3184949 = 298589) (by norm_num)
theorem B2123299 : Blo 2093435 2123299 := bstep (se 1 (by rfl) ⟨1592474, by rfl⟩ : syracuseStep 2123299 = 3184949) B3184949
theorem B11324261 : Blo 2093435 11324261 := bstep (se 4 (by rfl) ⟨1061649, by rfl⟩ : syracuseStep 11324261 = 2123299) B2123299
theorem B7549507 : Blo 2093435 7549507 := bstep (se 1 (by rfl) ⟨5662130, by rfl⟩ : syracuseStep 7549507 = 11324261) B11324261
theorem B40264037 : Blo 2093435 40264037 := bstep (se 4 (by rfl) ⟨3774753, by rfl⟩ : syracuseStep 40264037 = 7549507) B7549507
theorem B26842691 : Blo 2093435 26842691 := bstep (se 1 (by rfl) ⟨20132018, by rfl⟩ : syracuseStep 26842691 = 40264037) B40264037
theorem B17895127 : Blo 2093435 17895127 := bstep (se 1 (by rfl) ⟨13421345, by rfl⟩ : syracuseStep 17895127 = 26842691) B26842691
theorem B23860169 : Blo 2093435 23860169 := bstep (se 2 (by rfl) ⟨8947563, by rfl⟩ : syracuseStep 23860169 = 17895127) B17895127
theorem B15906779 : Blo 2093435 15906779 := bstep (se 1 (by rfl) ⟨11930084, by rfl⟩ : syracuseStep 15906779 = 23860169) B23860169
theorem B10604519 : Blo 2093435 10604519 := bstep (se 1 (by rfl) ⟨7953389, by rfl⟩ : syracuseStep 10604519 = 15906779) B15906779
theorem B7069679 : Blo 2093435 7069679 := bstep (se 1 (by rfl) ⟨5302259, by rfl⟩ : syracuseStep 7069679 = 10604519) B10604519
theorem B4713119 : Blo 2093435 4713119 := bstep (se 1 (by rfl) ⟨3534839, by rfl⟩ : syracuseStep 4713119 = 7069679) B7069679
theorem B3142079 : Blo 2093435 3142079 := bstep (se 1 (by rfl) ⟨2356559, by rfl⟩ : syracuseStep 3142079 = 4713119) B4713119
theorem B2094719 : Blo 2093435 2094719 := bstep (se 1 (by rfl) ⟨1571039, by rfl⟩ : syracuseStep 2094719 = 3142079) B3142079
theorem B3142085 : Blo 2093435 3142085 := bbase (se 4 (by rfl) ⟨294570, by rfl⟩ : syracuseStep 3142085 = 589141) (by norm_num)
theorem B2094723 : Blo 2093435 2094723 := bstep (se 1 (by rfl) ⟨1571042, by rfl⟩ : syracuseStep 2094723 = 3142085) B3142085
theorem B3534853 : Blo 2093435 3534853 := bbase (se 4 (by rfl) ⟨331392, by rfl⟩ : syracuseStep 3534853 = 662785) (by norm_num)
theorem B4713137 : Blo 2093435 4713137 := bstep (se 2 (by rfl) ⟨1767426, by rfl⟩ : syracuseStep 4713137 = 3534853) B3534853
theorem B3142091 : Blo 2093435 3142091 := bstep (se 1 (by rfl) ⟨2356568, by rfl⟩ : syracuseStep 3142091 = 4713137) B4713137
theorem B2094727 : Blo 2093435 2094727 := bstep (se 1 (by rfl) ⟨1571045, by rfl⟩ : syracuseStep 2094727 = 3142091) B3142091
theorem B2356573 : Blo 2093435 2356573 := bbase (se 3 (by rfl) ⟨441857, by rfl⟩ : syracuseStep 2356573 = 883715) (by norm_num)
theorem B3142097 : Blo 2093435 3142097 := bstep (se 2 (by rfl) ⟨1178286, by rfl⟩ : syracuseStep 3142097 = 2356573) B2356573
theorem B2094731 : Blo 2093435 2094731 := bstep (se 1 (by rfl) ⟨1571048, by rfl⟩ : syracuseStep 2094731 = 3142097) B3142097
theorem B7069733 : Blo 2093435 7069733 := bbase (se 4 (by rfl) ⟨662787, by rfl⟩ : syracuseStep 7069733 = 1325575) (by norm_num)
theorem B4713155 : Blo 2093435 4713155 := bstep (se 1 (by rfl) ⟨3534866, by rfl⟩ : syracuseStep 4713155 = 7069733) B7069733
theorem B3142103 : Blo 2093435 3142103 := bstep (se 1 (by rfl) ⟨2356577, by rfl⟩ : syracuseStep 3142103 = 4713155) B4713155
theorem B2094735 : Blo 2093435 2094735 := bstep (se 1 (by rfl) ⟨1571051, by rfl⟩ : syracuseStep 2094735 = 3142103) B3142103
theorem B3142109 : Blo 2093435 3142109 := bbase (se 3 (by rfl) ⟨589145, by rfl⟩ : syracuseStep 3142109 = 1178291) (by norm_num)
theorem B2094739 : Blo 2093435 2094739 := bstep (se 1 (by rfl) ⟨1571054, by rfl⟩ : syracuseStep 2094739 = 3142109) B3142109
theorem B4713173 : Blo 2093435 4713173 := bbase (se 7 (by rfl) ⟨55232, by rfl⟩ : syracuseStep 4713173 = 110465) (by norm_num)
theorem B3142115 : Blo 2093435 3142115 := bstep (se 1 (by rfl) ⟨2356586, by rfl⟩ : syracuseStep 3142115 = 4713173) B4713173
theorem B2094743 : Blo 2093435 2094743 := bstep (se 1 (by rfl) ⟨1571057, by rfl⟩ : syracuseStep 2094743 = 3142115) B3142115
theorem B8947685 : Blo 2093435 8947685 := bbase (se 4 (by rfl) ⟨838845, by rfl⟩ : syracuseStep 8947685 = 1677691) (by norm_num)
theorem B5965123 : Blo 2093435 5965123 := bstep (se 1 (by rfl) ⟨4473842, by rfl⟩ : syracuseStep 5965123 = 8947685) B8947685
theorem B7953497 : Blo 2093435 7953497 := bstep (se 2 (by rfl) ⟨2982561, by rfl⟩ : syracuseStep 7953497 = 5965123) B5965123
theorem B5302331 : Blo 2093435 5302331 := bstep (se 1 (by rfl) ⟨3976748, by rfl⟩ : syracuseStep 5302331 = 7953497) B7953497
theorem B3534887 : Blo 2093435 3534887 := bstep (se 1 (by rfl) ⟨2651165, by rfl⟩ : syracuseStep 3534887 = 5302331) B5302331
theorem B2356591 : Blo 2093435 2356591 := bstep (se 1 (by rfl) ⟨1767443, by rfl⟩ : syracuseStep 2356591 = 3534887) B3534887
theorem B3142121 : Blo 2093435 3142121 := bstep (se 2 (by rfl) ⟨1178295, by rfl⟩ : syracuseStep 3142121 = 2356591) B2356591
theorem B2094747 : Blo 2093435 2094747 := bstep (se 1 (by rfl) ⟨1571060, by rfl⟩ : syracuseStep 2094747 = 3142121) B3142121
theorem B2241605 : Blo 2093435 2241605 := bbase (se 4 (by rfl) ⟨210150, by rfl⟩ : syracuseStep 2241605 = 420301) (by norm_num)
theorem B5977613 : Blo 2093435 5977613 := bstep (se 3 (by rfl) ⟨1120802, by rfl⟩ : syracuseStep 5977613 = 2241605) B2241605
theorem B3985075 : Blo 2093435 3985075 := bstep (se 1 (by rfl) ⟨2988806, by rfl⟩ : syracuseStep 3985075 = 5977613) B5977613
theorem B5313433 : Blo 2093435 5313433 := bstep (se 2 (by rfl) ⟨1992537, by rfl⟩ : syracuseStep 5313433 = 3985075) B3985075
theorem B7084577 : Blo 2093435 7084577 := bstep (se 2 (by rfl) ⟨2656716, by rfl⟩ : syracuseStep 7084577 = 5313433) B5313433
theorem B4723051 : Blo 2093435 4723051 := bstep (se 1 (by rfl) ⟨3542288, by rfl⟩ : syracuseStep 4723051 = 7084577) B7084577
theorem B6297401 : Blo 2093435 6297401 := bstep (se 2 (by rfl) ⟨2361525, by rfl⟩ : syracuseStep 6297401 = 4723051) B4723051
theorem B4198267 : Blo 2093435 4198267 := bstep (se 1 (by rfl) ⟨3148700, by rfl⟩ : syracuseStep 4198267 = 6297401) B6297401
theorem B22390757 : Blo 2093435 22390757 := bstep (se 4 (by rfl) ⟨2099133, by rfl⟩ : syracuseStep 22390757 = 4198267) B4198267
theorem B14927171 : Blo 2093435 14927171 := bstep (se 1 (by rfl) ⟨11195378, by rfl⟩ : syracuseStep 14927171 = 22390757) B22390757
theorem B39805789 : Blo 2093435 39805789 := bstep (se 3 (by rfl) ⟨7463585, by rfl⟩ : syracuseStep 39805789 = 14927171) B14927171
theorem B53074385 : Blo 2093435 53074385 := bstep (se 2 (by rfl) ⟨19902894, by rfl⟩ : syracuseStep 53074385 = 39805789) B39805789
theorem B35382923 : Blo 2093435 35382923 := bstep (se 1 (by rfl) ⟨26537192, by rfl⟩ : syracuseStep 35382923 = 53074385) B53074385
theorem B23588615 : Blo 2093435 23588615 := bstep (se 1 (by rfl) ⟨17691461, by rfl⟩ : syracuseStep 23588615 = 35382923) B35382923
theorem B62902973 : Blo 2093435 62902973 := bstep (se 3 (by rfl) ⟨11794307, by rfl⟩ : syracuseStep 62902973 = 23588615) B23588615
theorem B41935315 : Blo 2093435 41935315 := bstep (se 1 (by rfl) ⟨31451486, by rfl⟩ : syracuseStep 41935315 = 62902973) B62902973
theorem B55913753 : Blo 2093435 55913753 := bstep (se 2 (by rfl) ⟨20967657, by rfl⟩ : syracuseStep 55913753 = 41935315) B41935315
theorem B149103341 : Blo 2093435 149103341 := bstep (se 3 (by rfl) ⟨27956876, by rfl⟩ : syracuseStep 149103341 = 55913753) B55913753
theorem B99402227 : Blo 2093435 99402227 := bstep (se 1 (by rfl) ⟨74551670, by rfl⟩ : syracuseStep 99402227 = 149103341) B149103341
theorem B66268151 : Blo 2093435 66268151 := bstep (se 1 (by rfl) ⟨49701113, by rfl⟩ : syracuseStep 66268151 = 99402227) B99402227
theorem B44178767 : Blo 2093435 44178767 := bstep (se 1 (by rfl) ⟨33134075, by rfl⟩ : syracuseStep 44178767 = 66268151) B66268151
theorem B29452511 : Blo 2093435 29452511 := bstep (se 1 (by rfl) ⟨22089383, by rfl⟩ : syracuseStep 29452511 = 44178767) B44178767
theorem B19635007 : Blo 2093435 19635007 := bstep (se 1 (by rfl) ⟨14726255, by rfl⟩ : syracuseStep 19635007 = 29452511) B29452511
theorem B26180009 : Blo 2093435 26180009 := bstep (se 2 (by rfl) ⟨9817503, by rfl⟩ : syracuseStep 26180009 = 19635007) B19635007
theorem B17453339 : Blo 2093435 17453339 := bstep (se 1 (by rfl) ⟨13090004, by rfl⟩ : syracuseStep 17453339 = 26180009) B26180009
theorem B11635559 : Blo 2093435 11635559 := bstep (se 1 (by rfl) ⟨8726669, by rfl⟩ : syracuseStep 11635559 = 17453339) B17453339
theorem B7757039 : Blo 2093435 7757039 := bstep (se 1 (by rfl) ⟨5817779, by rfl⟩ : syracuseStep 7757039 = 11635559) B11635559
theorem B5171359 : Blo 2093435 5171359 := bstep (se 1 (by rfl) ⟨3878519, by rfl⟩ : syracuseStep 5171359 = 7757039) B7757039
theorem B6895145 : Blo 2093435 6895145 := bstep (se 2 (by rfl) ⟨2585679, by rfl⟩ : syracuseStep 6895145 = 5171359) B5171359
theorem B4596763 : Blo 2093435 4596763 := bstep (se 1 (by rfl) ⟨3447572, by rfl⟩ : syracuseStep 4596763 = 6895145) B6895145
theorem B6129017 : Blo 2093435 6129017 := bstep (se 2 (by rfl) ⟨2298381, by rfl⟩ : syracuseStep 6129017 = 4596763) B4596763
theorem B4086011 : Blo 2093435 4086011 := bstep (se 1 (by rfl) ⟨3064508, by rfl⟩ : syracuseStep 4086011 = 6129017) B6129017
theorem B10896029 : Blo 2093435 10896029 := bstep (se 3 (by rfl) ⟨2043005, by rfl⟩ : syracuseStep 10896029 = 4086011) B4086011
theorem B7264019 : Blo 2093435 7264019 := bstep (se 1 (by rfl) ⟨5448014, by rfl⟩ : syracuseStep 7264019 = 10896029) B10896029
theorem B4842679 : Blo 2093435 4842679 := bstep (se 1 (by rfl) ⟨3632009, by rfl⟩ : syracuseStep 4842679 = 7264019) B7264019
theorem B6456905 : Blo 2093435 6456905 := bstep (se 2 (by rfl) ⟨2421339, by rfl⟩ : syracuseStep 6456905 = 4842679) B4842679
theorem B4304603 : Blo 2093435 4304603 := bstep (se 1 (by rfl) ⟨3228452, by rfl⟩ : syracuseStep 4304603 = 6456905) B6456905
theorem B2869735 : Blo 2093435 2869735 := bstep (se 1 (by rfl) ⟨2152301, by rfl⟩ : syracuseStep 2869735 = 4304603) B4304603
theorem B3826313 : Blo 2093435 3826313 := bstep (se 2 (by rfl) ⟨1434867, by rfl⟩ : syracuseStep 3826313 = 2869735) B2869735
theorem B2550875 : Blo 2093435 2550875 := bstep (se 1 (by rfl) ⟨1913156, by rfl⟩ : syracuseStep 2550875 = 3826313) B3826313
theorem B27209333 : Blo 2093435 27209333 := bstep (se 5 (by rfl) ⟨1275437, by rfl⟩ : syracuseStep 27209333 = 2550875) B2550875
theorem B18139555 : Blo 2093435 18139555 := bstep (se 1 (by rfl) ⟨13604666, by rfl⟩ : syracuseStep 18139555 = 27209333) B27209333
theorem B96744293 : Blo 2093435 96744293 := bstep (se 4 (by rfl) ⟨9069777, by rfl⟩ : syracuseStep 96744293 = 18139555) B18139555
theorem B64496195 : Blo 2093435 64496195 := bstep (se 1 (by rfl) ⟨48372146, by rfl⟩ : syracuseStep 64496195 = 96744293) B96744293
theorem B42997463 : Blo 2093435 42997463 := bstep (se 1 (by rfl) ⟨32248097, by rfl⟩ : syracuseStep 42997463 = 64496195) B64496195
theorem B28664975 : Blo 2093435 28664975 := bstep (se 1 (by rfl) ⟨21498731, by rfl⟩ : syracuseStep 28664975 = 42997463) B42997463
theorem B76439933 : Blo 2093435 76439933 := bstep (se 3 (by rfl) ⟨14332487, by rfl⟩ : syracuseStep 76439933 = 28664975) B28664975
theorem B50959955 : Blo 2093435 50959955 := bstep (se 1 (by rfl) ⟨38219966, by rfl⟩ : syracuseStep 50959955 = 76439933) B76439933
theorem B33973303 : Blo 2093435 33973303 := bstep (se 1 (by rfl) ⟨25479977, by rfl⟩ : syracuseStep 33973303 = 50959955) B50959955
theorem B45297737 : Blo 2093435 45297737 := bstep (se 2 (by rfl) ⟨16986651, by rfl⟩ : syracuseStep 45297737 = 33973303) B33973303
theorem B30198491 : Blo 2093435 30198491 := bstep (se 1 (by rfl) ⟨22648868, by rfl⟩ : syracuseStep 30198491 = 45297737) B45297737
theorem B20132327 : Blo 2093435 20132327 := bstep (se 1 (by rfl) ⟨15099245, by rfl⟩ : syracuseStep 20132327 = 30198491) B30198491
theorem B13421551 : Blo 2093435 13421551 := bstep (se 1 (by rfl) ⟨10066163, by rfl⟩ : syracuseStep 13421551 = 20132327) B20132327
theorem B17895401 : Blo 2093435 17895401 := bstep (se 2 (by rfl) ⟨6710775, by rfl⟩ : syracuseStep 17895401 = 13421551) B13421551
theorem B11930267 : Blo 2093435 11930267 := bstep (se 1 (by rfl) ⟨8947700, by rfl⟩ : syracuseStep 11930267 = 17895401) B17895401
theorem B7953511 : Blo 2093435 7953511 := bstep (se 1 (by rfl) ⟨5965133, by rfl⟩ : syracuseStep 7953511 = 11930267) B11930267
theorem B10604681 : Blo 2093435 10604681 := bstep (se 2 (by rfl) ⟨3976755, by rfl⟩ : syracuseStep 10604681 = 7953511) B7953511
theorem B7069787 : Blo 2093435 7069787 := bstep (se 1 (by rfl) ⟨5302340, by rfl⟩ : syracuseStep 7069787 = 10604681) B10604681
theorem B4713191 : Blo 2093435 4713191 := bstep (se 1 (by rfl) ⟨3534893, by rfl⟩ : syracuseStep 4713191 = 7069787) B7069787
theorem B3142127 : Blo 2093435 3142127 := bstep (se 1 (by rfl) ⟨2356595, by rfl⟩ : syracuseStep 3142127 = 4713191) B4713191
theorem B2094751 : Blo 2093435 2094751 := bstep (se 1 (by rfl) ⟨1571063, by rfl⟩ : syracuseStep 2094751 = 3142127) B3142127
theorem B3142133 : Blo 2093435 3142133 := bbase (se 5 (by rfl) ⟨147287, by rfl⟩ : syracuseStep 3142133 = 294575) (by norm_num)
theorem B2094755 : Blo 2093435 2094755 := bstep (se 1 (by rfl) ⟨1571066, by rfl⟩ : syracuseStep 2094755 = 3142133) B3142133
theorem B5965157 : Blo 2093435 5965157 := bbase (se 4 (by rfl) ⟨559233, by rfl⟩ : syracuseStep 5965157 = 1118467) (by norm_num)
theorem B3976771 : Blo 2093435 3976771 := bstep (se 1 (by rfl) ⟨2982578, by rfl⟩ : syracuseStep 3976771 = 5965157) B5965157
theorem B5302361 : Blo 2093435 5302361 := bstep (se 2 (by rfl) ⟨1988385, by rfl⟩ : syracuseStep 5302361 = 3976771) B3976771
theorem B3534907 : Blo 2093435 3534907 := bstep (se 1 (by rfl) ⟨2651180, by rfl⟩ : syracuseStep 3534907 = 5302361) B5302361
theorem B4713209 : Blo 2093435 4713209 := bstep (se 2 (by rfl) ⟨1767453, by rfl⟩ : syracuseStep 4713209 = 3534907) B3534907
theorem B3142139 : Blo 2093435 3142139 := bstep (se 1 (by rfl) ⟨2356604, by rfl⟩ : syracuseStep 3142139 = 4713209) B4713209
theorem B2094759 : Blo 2093435 2094759 := bstep (se 1 (by rfl) ⟨1571069, by rfl⟩ : syracuseStep 2094759 = 3142139) B3142139
theorem B2356609 : Blo 2093435 2356609 := bbase (se 2 (by rfl) ⟨883728, by rfl⟩ : syracuseStep 2356609 = 1767457) (by norm_num)
theorem B3142145 : Blo 2093435 3142145 := bstep (se 2 (by rfl) ⟨1178304, by rfl⟩ : syracuseStep 3142145 = 2356609) B2356609
theorem B2094763 : Blo 2093435 2094763 := bstep (se 1 (by rfl) ⟨1571072, by rfl⟩ : syracuseStep 2094763 = 3142145) B3142145
theorem B5302381 : Blo 2093435 5302381 := bbase (se 3 (by rfl) ⟨994196, by rfl⟩ : syracuseStep 5302381 = 1988393) (by norm_num)
theorem B7069841 : Blo 2093435 7069841 := bstep (se 2 (by rfl) ⟨2651190, by rfl⟩ : syracuseStep 7069841 = 5302381) B5302381
theorem B4713227 : Blo 2093435 4713227 := bstep (se 1 (by rfl) ⟨3534920, by rfl⟩ : syracuseStep 4713227 = 7069841) B7069841
theorem B3142151 : Blo 2093435 3142151 := bstep (se 1 (by rfl) ⟨2356613, by rfl⟩ : syracuseStep 3142151 = 4713227) B4713227
theorem B2094767 : Blo 2093435 2094767 := bstep (se 1 (by rfl) ⟨1571075, by rfl⟩ : syracuseStep 2094767 = 3142151) B3142151
theorem B3142157 : Blo 2093435 3142157 := bbase (se 3 (by rfl) ⟨589154, by rfl⟩ : syracuseStep 3142157 = 1178309) (by norm_num)
theorem B2094771 : Blo 2093435 2094771 := bstep (se 1 (by rfl) ⟨1571078, by rfl⟩ : syracuseStep 2094771 = 3142157) B3142157
theorem B4713245 : Blo 2093435 4713245 := bbase (se 3 (by rfl) ⟨883733, by rfl⟩ : syracuseStep 4713245 = 1767467) (by norm_num)
theorem B3142163 : Blo 2093435 3142163 := bstep (se 1 (by rfl) ⟨2356622, by rfl⟩ : syracuseStep 3142163 = 4713245) B4713245
theorem B2094775 : Blo 2093435 2094775 := bstep (se 1 (by rfl) ⟨1571081, by rfl⟩ : syracuseStep 2094775 = 3142163) B3142163
theorem B3534941 : Blo 2093435 3534941 := bbase (se 3 (by rfl) ⟨662801, by rfl⟩ : syracuseStep 3534941 = 1325603) (by norm_num)
theorem B2356627 : Blo 2093435 2356627 := bstep (se 1 (by rfl) ⟨1767470, by rfl⟩ : syracuseStep 2356627 = 3534941) B3534941
theorem B3142169 : Blo 2093435 3142169 := bstep (se 2 (by rfl) ⟨1178313, by rfl⟩ : syracuseStep 3142169 = 2356627) B2356627
theorem B2094779 : Blo 2093435 2094779 := bstep (se 1 (by rfl) ⟨1571084, by rfl⟩ : syracuseStep 2094779 = 3142169) B3142169
theorem B2388785 : Blo 2093435 2388785 := bbase (se 2 (by rfl) ⟨895794, by rfl⟩ : syracuseStep 2388785 = 1791589) (by norm_num)
theorem B6370093 : Blo 2093435 6370093 := bstep (se 3 (by rfl) ⟨1194392, by rfl⟩ : syracuseStep 6370093 = 2388785) B2388785
theorem B8493457 : Blo 2093435 8493457 := bstep (se 2 (by rfl) ⟨3185046, by rfl⟩ : syracuseStep 8493457 = 6370093) B6370093
theorem B11324609 : Blo 2093435 11324609 := bstep (se 2 (by rfl) ⟨4246728, by rfl⟩ : syracuseStep 11324609 = 8493457) B8493457
theorem B7549739 : Blo 2093435 7549739 := bstep (se 1 (by rfl) ⟨5662304, by rfl⟩ : syracuseStep 7549739 = 11324609) B11324609
theorem B5033159 : Blo 2093435 5033159 := bstep (se 1 (by rfl) ⟨3774869, by rfl⟩ : syracuseStep 5033159 = 7549739) B7549739
theorem B3355439 : Blo 2093435 3355439 := bstep (se 1 (by rfl) ⟨2516579, by rfl⟩ : syracuseStep 3355439 = 5033159) B5033159
theorem B8947837 : Blo 2093435 8947837 := bstep (se 3 (by rfl) ⟨1677719, by rfl⟩ : syracuseStep 8947837 = 3355439) B3355439
theorem B11930449 : Blo 2093435 11930449 := bstep (se 2 (by rfl) ⟨4473918, by rfl⟩ : syracuseStep 11930449 = 8947837) B8947837
theorem B15907265 : Blo 2093435 15907265 := bstep (se 2 (by rfl) ⟨5965224, by rfl⟩ : syracuseStep 15907265 = 11930449) B11930449
theorem B10604843 : Blo 2093435 10604843 := bstep (se 1 (by rfl) ⟨7953632, by rfl⟩ : syracuseStep 10604843 = 15907265) B15907265
theorem B7069895 : Blo 2093435 7069895 := bstep (se 1 (by rfl) ⟨5302421, by rfl⟩ : syracuseStep 7069895 = 10604843) B10604843
theorem B4713263 : Blo 2093435 4713263 := bstep (se 1 (by rfl) ⟨3534947, by rfl⟩ : syracuseStep 4713263 = 7069895) B7069895
theorem B3142175 : Blo 2093435 3142175 := bstep (se 1 (by rfl) ⟨2356631, by rfl⟩ : syracuseStep 3142175 = 4713263) B4713263
theorem B2094783 : Blo 2093435 2094783 := bstep (se 1 (by rfl) ⟨1571087, by rfl⟩ : syracuseStep 2094783 = 3142175) B3142175
theorem B3142181 : Blo 2093435 3142181 := bbase (se 4 (by rfl) ⟨294579, by rfl⟩ : syracuseStep 3142181 = 589159) (by norm_num)
theorem B2094787 : Blo 2093435 2094787 := bstep (se 1 (by rfl) ⟨1571090, by rfl⟩ : syracuseStep 2094787 = 3142181) B3142181
theorem B2651221 : Blo 2093435 2651221 := bbase (se 8 (by rfl) ⟨15534, by rfl⟩ : syracuseStep 2651221 = 31069) (by norm_num)
theorem B3534961 : Blo 2093435 3534961 := bstep (se 2 (by rfl) ⟨1325610, by rfl⟩ : syracuseStep 3534961 = 2651221) B2651221
theorem B4713281 : Blo 2093435 4713281 := bstep (se 2 (by rfl) ⟨1767480, by rfl⟩ : syracuseStep 4713281 = 3534961) B3534961
theorem B3142187 : Blo 2093435 3142187 := bstep (se 1 (by rfl) ⟨2356640, by rfl⟩ : syracuseStep 3142187 = 4713281) B4713281
theorem B2094791 : Blo 2093435 2094791 := bstep (se 1 (by rfl) ⟨1571093, by rfl⟩ : syracuseStep 2094791 = 3142187) B3142187
theorem B2356645 : Blo 2093435 2356645 := bbase (se 4 (by rfl) ⟨220935, by rfl⟩ : syracuseStep 2356645 = 441871) (by norm_num)
theorem B3142193 : Blo 2093435 3142193 := bstep (se 2 (by rfl) ⟨1178322, by rfl⟩ : syracuseStep 3142193 = 2356645) B2356645
theorem B2094795 : Blo 2093435 2094795 := bstep (se 1 (by rfl) ⟨1571096, by rfl⟩ : syracuseStep 2094795 = 3142193) B3142193
theorem B2123381 : Blo 2093435 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B5662349 : Blo 2093435 5662349 := bstep (se 3 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 5662349 = 2123381) B2123381
theorem B3774899 : Blo 2093435 3774899 := bstep (se 1 (by rfl) ⟨2831174, by rfl⟩ : syracuseStep 3774899 = 5662349) B5662349
theorem B2516599 : Blo 2093435 2516599 := bstep (se 1 (by rfl) ⟨1887449, by rfl⟩ : syracuseStep 2516599 = 3774899) B3774899
theorem B13421861 : Blo 2093435 13421861 := bstep (se 4 (by rfl) ⟨1258299, by rfl⟩ : syracuseStep 13421861 = 2516599) B2516599
theorem B8947907 : Blo 2093435 8947907 := bstep (se 1 (by rfl) ⟨6710930, by rfl⟩ : syracuseStep 8947907 = 13421861) B13421861
theorem B5965271 : Blo 2093435 5965271 := bstep (se 1 (by rfl) ⟨4473953, by rfl⟩ : syracuseStep 5965271 = 8947907) B8947907
theorem B3976847 : Blo 2093435 3976847 := bstep (se 1 (by rfl) ⟨2982635, by rfl⟩ : syracuseStep 3976847 = 5965271) B5965271
theorem B2651231 : Blo 2093435 2651231 := bstep (se 1 (by rfl) ⟨1988423, by rfl⟩ : syracuseStep 2651231 = 3976847) B3976847
theorem B7069949 : Blo 2093435 7069949 := bstep (se 3 (by rfl) ⟨1325615, by rfl⟩ : syracuseStep 7069949 = 2651231) B2651231
theorem B4713299 : Blo 2093435 4713299 := bstep (se 1 (by rfl) ⟨3534974, by rfl⟩ : syracuseStep 4713299 = 7069949) B7069949
theorem B3142199 : Blo 2093435 3142199 := bstep (se 1 (by rfl) ⟨2356649, by rfl⟩ : syracuseStep 3142199 = 4713299) B4713299
theorem B2094799 : Blo 2093435 2094799 := bstep (se 1 (by rfl) ⟨1571099, by rfl⟩ : syracuseStep 2094799 = 3142199) B3142199
theorem B3142205 : Blo 2093435 3142205 := bbase (se 3 (by rfl) ⟨589163, by rfl⟩ : syracuseStep 3142205 = 1178327) (by norm_num)
theorem B2094803 : Blo 2093435 2094803 := bstep (se 1 (by rfl) ⟨1571102, by rfl⟩ : syracuseStep 2094803 = 3142205) B3142205
theorem B4713317 : Blo 2093435 4713317 := bbase (se 4 (by rfl) ⟨441873, by rfl⟩ : syracuseStep 4713317 = 883747) (by norm_num)
theorem B3142211 : Blo 2093435 3142211 := bstep (se 1 (by rfl) ⟨2356658, by rfl⟩ : syracuseStep 3142211 = 4713317) B4713317
theorem B2094807 : Blo 2093435 2094807 := bstep (se 1 (by rfl) ⟨1571105, by rfl⟩ : syracuseStep 2094807 = 3142211) B3142211
theorem B5302493 : Blo 2093435 5302493 := bbase (se 3 (by rfl) ⟨994217, by rfl⟩ : syracuseStep 5302493 = 1988435) (by norm_num)
theorem B3534995 : Blo 2093435 3534995 := bstep (se 1 (by rfl) ⟨2651246, by rfl⟩ : syracuseStep 3534995 = 5302493) B5302493
theorem B2356663 : Blo 2093435 2356663 := bstep (se 1 (by rfl) ⟨1767497, by rfl⟩ : syracuseStep 2356663 = 3534995) B3534995
theorem B3142217 : Blo 2093435 3142217 := bstep (se 2 (by rfl) ⟨1178331, by rfl⟩ : syracuseStep 3142217 = 2356663) B2356663
theorem B2094811 : Blo 2093435 2094811 := bstep (se 1 (by rfl) ⟨1571108, by rfl⟩ : syracuseStep 2094811 = 3142217) B3142217
theorem B3976877 : Blo 2093435 3976877 := bbase (se 3 (by rfl) ⟨745664, by rfl⟩ : syracuseStep 3976877 = 1491329) (by norm_num)
theorem B10605005 : Blo 2093435 10605005 := bstep (se 3 (by rfl) ⟨1988438, by rfl⟩ : syracuseStep 10605005 = 3976877) B3976877
theorem B7070003 : Blo 2093435 7070003 := bstep (se 1 (by rfl) ⟨5302502, by rfl⟩ : syracuseStep 7070003 = 10605005) B10605005
theorem B4713335 : Blo 2093435 4713335 := bstep (se 1 (by rfl) ⟨3535001, by rfl⟩ : syracuseStep 4713335 = 7070003) B7070003
theorem B3142223 : Blo 2093435 3142223 := bstep (se 1 (by rfl) ⟨2356667, by rfl⟩ : syracuseStep 3142223 = 4713335) B4713335
theorem B2094815 : Blo 2093435 2094815 := bstep (se 1 (by rfl) ⟨1571111, by rfl⟩ : syracuseStep 2094815 = 3142223) B3142223
theorem B3142229 : Blo 2093435 3142229 := bbase (se 8 (by rfl) ⟨18411, by rfl⟩ : syracuseStep 3142229 = 36823) (by norm_num)
theorem B2094819 : Blo 2093435 2094819 := bstep (se 1 (by rfl) ⟨1571114, by rfl⟩ : syracuseStep 2094819 = 3142229) B3142229
theorem B4777661 : Blo 2093435 4777661 := bbase (se 3 (by rfl) ⟨895811, by rfl⟩ : syracuseStep 4777661 = 1791623) (by norm_num)
theorem B12740429 : Blo 2093435 12740429 := bstep (se 3 (by rfl) ⟨2388830, by rfl⟩ : syracuseStep 12740429 = 4777661) B4777661
theorem B33974477 : Blo 2093435 33974477 := bstep (se 3 (by rfl) ⟨6370214, by rfl⟩ : syracuseStep 33974477 = 12740429) B12740429
theorem B22649651 : Blo 2093435 22649651 := bstep (se 1 (by rfl) ⟨16987238, by rfl⟩ : syracuseStep 22649651 = 33974477) B33974477
theorem B15099767 : Blo 2093435 15099767 := bstep (se 1 (by rfl) ⟨11324825, by rfl⟩ : syracuseStep 15099767 = 22649651) B22649651
theorem B10066511 : Blo 2093435 10066511 := bstep (se 1 (by rfl) ⟨7549883, by rfl⟩ : syracuseStep 10066511 = 15099767) B15099767
theorem B6711007 : Blo 2093435 6711007 := bstep (se 1 (by rfl) ⟨5033255, by rfl⟩ : syracuseStep 6711007 = 10066511) B10066511
theorem B8948009 : Blo 2093435 8948009 := bstep (se 2 (by rfl) ⟨3355503, by rfl⟩ : syracuseStep 8948009 = 6711007) B6711007
theorem B5965339 : Blo 2093435 5965339 := bstep (se 1 (by rfl) ⟨4474004, by rfl⟩ : syracuseStep 5965339 = 8948009) B8948009
theorem B7953785 : Blo 2093435 7953785 := bstep (se 2 (by rfl) ⟨2982669, by rfl⟩ : syracuseStep 7953785 = 5965339) B5965339
theorem B5302523 : Blo 2093435 5302523 := bstep (se 1 (by rfl) ⟨3976892, by rfl⟩ : syracuseStep 5302523 = 7953785) B7953785
theorem B3535015 : Blo 2093435 3535015 := bstep (se 1 (by rfl) ⟨2651261, by rfl⟩ : syracuseStep 3535015 = 5302523) B5302523
theorem B4713353 : Blo 2093435 4713353 := bstep (se 2 (by rfl) ⟨1767507, by rfl⟩ : syracuseStep 4713353 = 3535015) B3535015
theorem B3142235 : Blo 2093435 3142235 := bstep (se 1 (by rfl) ⟨2356676, by rfl⟩ : syracuseStep 3142235 = 4713353) B4713353
theorem B2094823 : Blo 2093435 2094823 := bstep (se 1 (by rfl) ⟨1571117, by rfl⟩ : syracuseStep 2094823 = 3142235) B3142235
theorem B2356681 : Blo 2093435 2356681 := bbase (se 2 (by rfl) ⟨883755, by rfl⟩ : syracuseStep 2356681 = 1767511) (by norm_num)
theorem B3142241 : Blo 2093435 3142241 := bstep (se 2 (by rfl) ⟨1178340, by rfl⟩ : syracuseStep 3142241 = 2356681) B2356681
theorem B2094827 : Blo 2093435 2094827 := bstep (se 1 (by rfl) ⟨1571120, by rfl⟩ : syracuseStep 2094827 = 3142241) B3142241
theorem B17896085 : Blo 2093435 17896085 := bbase (se 6 (by rfl) ⟨419439, by rfl⟩ : syracuseStep 17896085 = 838879) (by norm_num)
theorem B11930723 : Blo 2093435 11930723 := bstep (se 1 (by rfl) ⟨8948042, by rfl⟩ : syracuseStep 11930723 = 17896085) B17896085
theorem B7953815 : Blo 2093435 7953815 := bstep (se 1 (by rfl) ⟨5965361, by rfl⟩ : syracuseStep 7953815 = 11930723) B11930723
theorem B5302543 : Blo 2093435 5302543 := bstep (se 1 (by rfl) ⟨3976907, by rfl⟩ : syracuseStep 5302543 = 7953815) B7953815
theorem B7070057 : Blo 2093435 7070057 := bstep (se 2 (by rfl) ⟨2651271, by rfl⟩ : syracuseStep 7070057 = 5302543) B5302543
theorem B4713371 : Blo 2093435 4713371 := bstep (se 1 (by rfl) ⟨3535028, by rfl⟩ : syracuseStep 4713371 = 7070057) B7070057
theorem B3142247 : Blo 2093435 3142247 := bstep (se 1 (by rfl) ⟨2356685, by rfl⟩ : syracuseStep 3142247 = 4713371) B4713371
theorem B2094831 : Blo 2093435 2094831 := bstep (se 1 (by rfl) ⟨1571123, by rfl⟩ : syracuseStep 2094831 = 3142247) B3142247
theorem B3142253 : Blo 2093435 3142253 := bbase (se 3 (by rfl) ⟨589172, by rfl⟩ : syracuseStep 3142253 = 1178345) (by norm_num)
theorem B2094835 : Blo 2093435 2094835 := bstep (se 1 (by rfl) ⟨1571126, by rfl⟩ : syracuseStep 2094835 = 3142253) B3142253
theorem B4713389 : Blo 2093435 4713389 := bbase (se 3 (by rfl) ⟨883760, by rfl⟩ : syracuseStep 4713389 = 1767521) (by norm_num)
theorem B3142259 : Blo 2093435 3142259 := bstep (se 1 (by rfl) ⟨2356694, by rfl⟩ : syracuseStep 3142259 = 4713389) B4713389
theorem B2094839 : Blo 2093435 2094839 := bstep (se 1 (by rfl) ⟨1571129, by rfl⟩ : syracuseStep 2094839 = 3142259) B3142259
theorem B5965397 : Blo 2093435 5965397 := bbase (se 8 (by rfl) ⟨34953, by rfl⟩ : syracuseStep 5965397 = 69907) (by norm_num)
theorem B3976931 : Blo 2093435 3976931 := bstep (se 1 (by rfl) ⟨2982698, by rfl⟩ : syracuseStep 3976931 = 5965397) B5965397
theorem B2651287 : Blo 2093435 2651287 := bstep (se 1 (by rfl) ⟨1988465, by rfl⟩ : syracuseStep 2651287 = 3976931) B3976931
theorem B3535049 : Blo 2093435 3535049 := bstep (se 2 (by rfl) ⟨1325643, by rfl⟩ : syracuseStep 3535049 = 2651287) B2651287
theorem B2356699 : Blo 2093435 2356699 := bstep (se 1 (by rfl) ⟨1767524, by rfl⟩ : syracuseStep 2356699 = 3535049) B3535049
theorem B3142265 : Blo 2093435 3142265 := bstep (se 2 (by rfl) ⟨1178349, by rfl⟩ : syracuseStep 3142265 = 2356699) B2356699
theorem B2094843 : Blo 2093435 2094843 := bstep (se 1 (by rfl) ⟨1571132, by rfl⟩ : syracuseStep 2094843 = 3142265) B3142265
theorem B2687465 : Blo 2093435 2687465 := bbase (se 2 (by rfl) ⟨1007799, by rfl⟩ : syracuseStep 2687465 = 2015599) (by norm_num)
theorem B7166573 : Blo 2093435 7166573 := bstep (se 3 (by rfl) ⟨1343732, by rfl⟩ : syracuseStep 7166573 = 2687465) B2687465
theorem B4777715 : Blo 2093435 4777715 := bstep (se 1 (by rfl) ⟨3583286, by rfl⟩ : syracuseStep 4777715 = 7166573) B7166573
theorem B3185143 : Blo 2093435 3185143 := bstep (se 1 (by rfl) ⟨2388857, by rfl⟩ : syracuseStep 3185143 = 4777715) B4777715
theorem B16987429 : Blo 2093435 16987429 := bstep (se 4 (by rfl) ⟨1592571, by rfl⟩ : syracuseStep 16987429 = 3185143) B3185143
theorem B22649905 : Blo 2093435 22649905 := bstep (se 2 (by rfl) ⟨8493714, by rfl⟩ : syracuseStep 22649905 = 16987429) B16987429
theorem B30199873 : Blo 2093435 30199873 := bstep (se 2 (by rfl) ⟨11324952, by rfl⟩ : syracuseStep 30199873 = 22649905) B22649905
theorem B40266497 : Blo 2093435 40266497 := bstep (se 2 (by rfl) ⟨15099936, by rfl⟩ : syracuseStep 40266497 = 30199873) B30199873
theorem B26844331 : Blo 2093435 26844331 := bstep (se 1 (by rfl) ⟨20133248, by rfl⟩ : syracuseStep 26844331 = 40266497) B40266497
theorem B35792441 : Blo 2093435 35792441 := bstep (se 2 (by rfl) ⟨13422165, by rfl⟩ : syracuseStep 35792441 = 26844331) B26844331
theorem B23861627 : Blo 2093435 23861627 := bstep (se 1 (by rfl) ⟨17896220, by rfl⟩ : syracuseStep 23861627 = 35792441) B35792441
theorem B15907751 : Blo 2093435 15907751 := bstep (se 1 (by rfl) ⟨11930813, by rfl⟩ : syracuseStep 15907751 = 23861627) B23861627
theorem B10605167 : Blo 2093435 10605167 := bstep (se 1 (by rfl) ⟨7953875, by rfl⟩ : syracuseStep 10605167 = 15907751) B15907751
theorem B7070111 : Blo 2093435 7070111 := bstep (se 1 (by rfl) ⟨5302583, by rfl⟩ : syracuseStep 7070111 = 10605167) B10605167
theorem B4713407 : Blo 2093435 4713407 := bstep (se 1 (by rfl) ⟨3535055, by rfl⟩ : syracuseStep 4713407 = 7070111) B7070111
theorem B3142271 : Blo 2093435 3142271 := bstep (se 1 (by rfl) ⟨2356703, by rfl⟩ : syracuseStep 3142271 = 4713407) B4713407
theorem B2094847 : Blo 2093435 2094847 := bstep (se 1 (by rfl) ⟨1571135, by rfl⟩ : syracuseStep 2094847 = 3142271) B3142271
theorem B3142277 : Blo 2093435 3142277 := bbase (se 4 (by rfl) ⟨294588, by rfl⟩ : syracuseStep 3142277 = 589177) (by norm_num)
theorem B2094851 : Blo 2093435 2094851 := bstep (se 1 (by rfl) ⟨1571138, by rfl⟩ : syracuseStep 2094851 = 3142277) B3142277
theorem B3535069 : Blo 2093435 3535069 := bbase (se 3 (by rfl) ⟨662825, by rfl⟩ : syracuseStep 3535069 = 1325651) (by norm_num)
theorem B4713425 : Blo 2093435 4713425 := bstep (se 2 (by rfl) ⟨1767534, by rfl⟩ : syracuseStep 4713425 = 3535069) B3535069
theorem B3142283 : Blo 2093435 3142283 := bstep (se 1 (by rfl) ⟨2356712, by rfl⟩ : syracuseStep 3142283 = 4713425) B4713425
theorem B2094855 : Blo 2093435 2094855 := bstep (se 1 (by rfl) ⟨1571141, by rfl⟩ : syracuseStep 2094855 = 3142283) B3142283
theorem B2356717 : Blo 2093435 2356717 := bbase (se 3 (by rfl) ⟨441884, by rfl⟩ : syracuseStep 2356717 = 883769) (by norm_num)
theorem B3142289 : Blo 2093435 3142289 := bstep (se 2 (by rfl) ⟨1178358, by rfl⟩ : syracuseStep 3142289 = 2356717) B2356717
theorem B2094859 : Blo 2093435 2094859 := bstep (se 1 (by rfl) ⟨1571144, by rfl⟩ : syracuseStep 2094859 = 3142289) B3142289
theorem B7070165 : Blo 2093435 7070165 := bbase (se 7 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 7070165 = 165707) (by norm_num)
theorem B4713443 : Blo 2093435 4713443 := bstep (se 1 (by rfl) ⟨3535082, by rfl⟩ : syracuseStep 4713443 = 7070165) B7070165
theorem B3142295 : Blo 2093435 3142295 := bstep (se 1 (by rfl) ⟨2356721, by rfl⟩ : syracuseStep 3142295 = 4713443) B4713443
theorem B2094863 : Blo 2093435 2094863 := bstep (se 1 (by rfl) ⟨1571147, by rfl⟩ : syracuseStep 2094863 = 3142295) B3142295
theorem B3142301 : Blo 2093435 3142301 := bbase (se 3 (by rfl) ⟨589181, by rfl⟩ : syracuseStep 3142301 = 1178363) (by norm_num)
theorem B2094867 : Blo 2093435 2094867 := bstep (se 1 (by rfl) ⟨1571150, by rfl⟩ : syracuseStep 2094867 = 3142301) B3142301
theorem B4713461 : Blo 2093435 4713461 := bbase (se 5 (by rfl) ⟨220943, by rfl⟩ : syracuseStep 4713461 = 441887) (by norm_num)
theorem B3142307 : Blo 2093435 3142307 := bstep (se 1 (by rfl) ⟨2356730, by rfl⟩ : syracuseStep 3142307 = 4713461) B4713461
theorem B2094871 : Blo 2093435 2094871 := bstep (se 1 (by rfl) ⟨1571153, by rfl⟩ : syracuseStep 2094871 = 3142307) B3142307
theorem B6370373 : Blo 2093435 6370373 := bbase (se 4 (by rfl) ⟨597222, by rfl⟩ : syracuseStep 6370373 = 1194445) (by norm_num)
theorem B4246915 : Blo 2093435 4246915 := bstep (se 1 (by rfl) ⟨3185186, by rfl⟩ : syracuseStep 4246915 = 6370373) B6370373
theorem B5662553 : Blo 2093435 5662553 := bstep (se 2 (by rfl) ⟨2123457, by rfl⟩ : syracuseStep 5662553 = 4246915) B4246915
theorem B60400565 : Blo 2093435 60400565 := bstep (se 5 (by rfl) ⟨2831276, by rfl⟩ : syracuseStep 60400565 = 5662553) B5662553
theorem B40267043 : Blo 2093435 40267043 := bstep (se 1 (by rfl) ⟨30200282, by rfl⟩ : syracuseStep 40267043 = 60400565) B60400565
theorem B26844695 : Blo 2093435 26844695 := bstep (se 1 (by rfl) ⟨20133521, by rfl⟩ : syracuseStep 26844695 = 40267043) B40267043
theorem B17896463 : Blo 2093435 17896463 := bstep (se 1 (by rfl) ⟨13422347, by rfl⟩ : syracuseStep 17896463 = 26844695) B26844695
theorem B11930975 : Blo 2093435 11930975 := bstep (se 1 (by rfl) ⟨8948231, by rfl⟩ : syracuseStep 11930975 = 17896463) B17896463
theorem B7953983 : Blo 2093435 7953983 := bstep (se 1 (by rfl) ⟨5965487, by rfl⟩ : syracuseStep 7953983 = 11930975) B11930975
theorem B5302655 : Blo 2093435 5302655 := bstep (se 1 (by rfl) ⟨3976991, by rfl⟩ : syracuseStep 5302655 = 7953983) B7953983
theorem B3535103 : Blo 2093435 3535103 := bstep (se 1 (by rfl) ⟨2651327, by rfl⟩ : syracuseStep 3535103 = 5302655) B5302655
theorem B2356735 : Blo 2093435 2356735 := bstep (se 1 (by rfl) ⟨1767551, by rfl⟩ : syracuseStep 2356735 = 3535103) B3535103
theorem B3142313 : Blo 2093435 3142313 := bstep (se 2 (by rfl) ⟨1178367, by rfl⟩ : syracuseStep 3142313 = 2356735) B2356735
theorem B2094875 : Blo 2093435 2094875 := bstep (se 1 (by rfl) ⟨1571156, by rfl⟩ : syracuseStep 2094875 = 3142313) B3142313
theorem B2982749 : Blo 2093435 2982749 := bbase (se 3 (by rfl) ⟨559265, by rfl⟩ : syracuseStep 2982749 = 1118531) (by norm_num)
theorem B7953997 : Blo 2093435 7953997 := bstep (se 3 (by rfl) ⟨1491374, by rfl⟩ : syracuseStep 7953997 = 2982749) B2982749
theorem B10605329 : Blo 2093435 10605329 := bstep (se 2 (by rfl) ⟨3976998, by rfl⟩ : syracuseStep 10605329 = 7953997) B7953997
theorem B7070219 : Blo 2093435 7070219 := bstep (se 1 (by rfl) ⟨5302664, by rfl⟩ : syracuseStep 7070219 = 10605329) B10605329
theorem B4713479 : Blo 2093435 4713479 := bstep (se 1 (by rfl) ⟨3535109, by rfl⟩ : syracuseStep 4713479 = 7070219) B7070219
theorem B3142319 : Blo 2093435 3142319 := bstep (se 1 (by rfl) ⟨2356739, by rfl⟩ : syracuseStep 3142319 = 4713479) B4713479
theorem B2094879 : Blo 2093435 2094879 := bstep (se 1 (by rfl) ⟨1571159, by rfl⟩ : syracuseStep 2094879 = 3142319) B3142319
theorem B3142325 : Blo 2093435 3142325 := bbase (se 5 (by rfl) ⟨147296, by rfl⟩ : syracuseStep 3142325 = 294593) (by norm_num)
theorem B2094883 : Blo 2093435 2094883 := bstep (se 1 (by rfl) ⟨1571162, by rfl⟩ : syracuseStep 2094883 = 3142325) B3142325
theorem B5302685 : Blo 2093435 5302685 := bbase (se 3 (by rfl) ⟨994253, by rfl⟩ : syracuseStep 5302685 = 1988507) (by norm_num)
theorem B3535123 : Blo 2093435 3535123 := bstep (se 1 (by rfl) ⟨2651342, by rfl⟩ : syracuseStep 3535123 = 5302685) B5302685
theorem B4713497 : Blo 2093435 4713497 := bstep (se 2 (by rfl) ⟨1767561, by rfl⟩ : syracuseStep 4713497 = 3535123) B3535123
theorem B3142331 : Blo 2093435 3142331 := bstep (se 1 (by rfl) ⟨2356748, by rfl⟩ : syracuseStep 3142331 = 4713497) B4713497
theorem B2094887 : Blo 2093435 2094887 := bstep (se 1 (by rfl) ⟨1571165, by rfl⟩ : syracuseStep 2094887 = 3142331) B3142331
theorem B2356753 : Blo 2093435 2356753 := bbase (se 2 (by rfl) ⟨883782, by rfl⟩ : syracuseStep 2356753 = 1767565) (by norm_num)
theorem B3142337 : Blo 2093435 3142337 := bstep (se 2 (by rfl) ⟨1178376, by rfl⟩ : syracuseStep 3142337 = 2356753) B2356753
theorem B2094891 : Blo 2093435 2094891 := bstep (se 1 (by rfl) ⟨1571168, by rfl⟩ : syracuseStep 2094891 = 3142337) B3142337
theorem B3977029 : Blo 2093435 3977029 := bbase (se 4 (by rfl) ⟨372846, by rfl⟩ : syracuseStep 3977029 = 745693) (by norm_num)
theorem B5302705 : Blo 2093435 5302705 := bstep (se 2 (by rfl) ⟨1988514, by rfl⟩ : syracuseStep 5302705 = 3977029) B3977029
theorem B7070273 : Blo 2093435 7070273 := bstep (se 2 (by rfl) ⟨2651352, by rfl⟩ : syracuseStep 7070273 = 5302705) B5302705
theorem B4713515 : Blo 2093435 4713515 := bstep (se 1 (by rfl) ⟨3535136, by rfl⟩ : syracuseStep 4713515 = 7070273) B7070273
theorem B3142343 : Blo 2093435 3142343 := bstep (se 1 (by rfl) ⟨2356757, by rfl⟩ : syracuseStep 3142343 = 4713515) B4713515
theorem B2094895 : Blo 2093435 2094895 := bstep (se 1 (by rfl) ⟨1571171, by rfl⟩ : syracuseStep 2094895 = 3142343) B3142343
theorem B3142349 : Blo 2093435 3142349 := bbase (se 3 (by rfl) ⟨589190, by rfl⟩ : syracuseStep 3142349 = 1178381) (by norm_num)
theorem B2094899 : Blo 2093435 2094899 := bstep (se 1 (by rfl) ⟨1571174, by rfl⟩ : syracuseStep 2094899 = 3142349) B3142349
theorem B4713533 : Blo 2093435 4713533 := bbase (se 3 (by rfl) ⟨883787, by rfl⟩ : syracuseStep 4713533 = 1767575) (by norm_num)
theorem B3142355 : Blo 2093435 3142355 := bstep (se 1 (by rfl) ⟨2356766, by rfl⟩ : syracuseStep 3142355 = 4713533) B4713533
theorem B2094903 : Blo 2093435 2094903 := bstep (se 1 (by rfl) ⟨1571177, by rfl⟩ : syracuseStep 2094903 = 3142355) B3142355
theorem B3535157 : Blo 2093435 3535157 := bbase (se 5 (by rfl) ⟨165710, by rfl⟩ : syracuseStep 3535157 = 331421) (by norm_num)
theorem B2356771 : Blo 2093435 2356771 := bstep (se 1 (by rfl) ⟨1767578, by rfl⟩ : syracuseStep 2356771 = 3535157) B3535157
theorem B3142361 : Blo 2093435 3142361 := bstep (se 2 (by rfl) ⟨1178385, by rfl⟩ : syracuseStep 3142361 = 2356771) B2356771
theorem B2094907 : Blo 2093435 2094907 := bstep (se 1 (by rfl) ⟨1571180, by rfl⟩ : syracuseStep 2094907 = 3142361) B3142361
theorem B5965589 : Blo 2093435 5965589 := bbase (se 6 (by rfl) ⟨139818, by rfl⟩ : syracuseStep 5965589 = 279637) (by norm_num)
theorem B15908237 : Blo 2093435 15908237 := bstep (se 3 (by rfl) ⟨2982794, by rfl⟩ : syracuseStep 15908237 = 5965589) B5965589
theorem B10605491 : Blo 2093435 10605491 := bstep (se 1 (by rfl) ⟨7954118, by rfl⟩ : syracuseStep 10605491 = 15908237) B15908237
theorem B7070327 : Blo 2093435 7070327 := bstep (se 1 (by rfl) ⟨5302745, by rfl⟩ : syracuseStep 7070327 = 10605491) B10605491
theorem B4713551 : Blo 2093435 4713551 := bstep (se 1 (by rfl) ⟨3535163, by rfl⟩ : syracuseStep 4713551 = 7070327) B7070327
theorem B3142367 : Blo 2093435 3142367 := bstep (se 1 (by rfl) ⟨2356775, by rfl⟩ : syracuseStep 3142367 = 4713551) B4713551
theorem B2094911 : Blo 2093435 2094911 := bstep (se 1 (by rfl) ⟨1571183, by rfl⟩ : syracuseStep 2094911 = 3142367) B3142367
theorem B3142373 : Blo 2093435 3142373 := bbase (se 4 (by rfl) ⟨294597, by rfl⟩ : syracuseStep 3142373 = 589195) (by norm_num)
theorem B2094915 : Blo 2093435 2094915 := bstep (se 1 (by rfl) ⟨1571186, by rfl⟩ : syracuseStep 2094915 = 3142373) B3142373
theorem B2237105 : Blo 2093435 2237105 := bbase (se 2 (by rfl) ⟨838914, by rfl⟩ : syracuseStep 2237105 = 1677829) (by norm_num)
theorem B5965613 : Blo 2093435 5965613 := bstep (se 3 (by rfl) ⟨1118552, by rfl⟩ : syracuseStep 5965613 = 2237105) B2237105
theorem B3977075 : Blo 2093435 3977075 := bstep (se 1 (by rfl) ⟨2982806, by rfl⟩ : syracuseStep 3977075 = 5965613) B5965613
theorem B2651383 : Blo 2093435 2651383 := bstep (se 1 (by rfl) ⟨1988537, by rfl⟩ : syracuseStep 2651383 = 3977075) B3977075
theorem B3535177 : Blo 2093435 3535177 := bstep (se 2 (by rfl) ⟨1325691, by rfl⟩ : syracuseStep 3535177 = 2651383) B2651383
theorem B4713569 : Blo 2093435 4713569 := bstep (se 2 (by rfl) ⟨1767588, by rfl⟩ : syracuseStep 4713569 = 3535177) B3535177
theorem B3142379 : Blo 2093435 3142379 := bstep (se 1 (by rfl) ⟨2356784, by rfl⟩ : syracuseStep 3142379 = 4713569) B4713569
theorem B2094919 : Blo 2093435 2094919 := bstep (se 1 (by rfl) ⟨1571189, by rfl⟩ : syracuseStep 2094919 = 3142379) B3142379
theorem B2356789 : Blo 2093435 2356789 := bbase (se 5 (by rfl) ⟨110474, by rfl⟩ : syracuseStep 2356789 = 220949) (by norm_num)
theorem B3142385 : Blo 2093435 3142385 := bstep (se 2 (by rfl) ⟨1178394, by rfl⟩ : syracuseStep 3142385 = 2356789) B2356789
theorem B2094923 : Blo 2093435 2094923 := bstep (se 1 (by rfl) ⟨1571192, by rfl⟩ : syracuseStep 2094923 = 3142385) B3142385
theorem B2651393 : Blo 2093435 2651393 := bbase (se 2 (by rfl) ⟨994272, by rfl⟩ : syracuseStep 2651393 = 1988545) (by norm_num)
theorem B7070381 : Blo 2093435 7070381 := bstep (se 3 (by rfl) ⟨1325696, by rfl⟩ : syracuseStep 7070381 = 2651393) B2651393
theorem B4713587 : Blo 2093435 4713587 := bstep (se 1 (by rfl) ⟨3535190, by rfl⟩ : syracuseStep 4713587 = 7070381) B7070381
theorem B3142391 : Blo 2093435 3142391 := bstep (se 1 (by rfl) ⟨2356793, by rfl⟩ : syracuseStep 3142391 = 4713587) B4713587
theorem B2094927 : Blo 2093435 2094927 := bstep (se 1 (by rfl) ⟨1571195, by rfl⟩ : syracuseStep 2094927 = 3142391) B3142391
theorem B3142397 : Blo 2093435 3142397 := bbase (se 3 (by rfl) ⟨589199, by rfl⟩ : syracuseStep 3142397 = 1178399) (by norm_num)
theorem B2094931 : Blo 2093435 2094931 := bstep (se 1 (by rfl) ⟨1571198, by rfl⟩ : syracuseStep 2094931 = 3142397) B3142397
theorem B4713605 : Blo 2093435 4713605 := bbase (se 4 (by rfl) ⟨441900, by rfl⟩ : syracuseStep 4713605 = 883801) (by norm_num)
theorem B3142403 : Blo 2093435 3142403 := bstep (se 1 (by rfl) ⟨2356802, by rfl⟩ : syracuseStep 3142403 = 4713605) B4713605
theorem B2094935 : Blo 2093435 2094935 := bstep (se 1 (by rfl) ⟨1571201, by rfl⟩ : syracuseStep 2094935 = 3142403) B3142403
theorem B4474253 : Blo 2093435 4474253 := bbase (se 3 (by rfl) ⟨838922, by rfl⟩ : syracuseStep 4474253 = 1677845) (by norm_num)
theorem B2982835 : Blo 2093435 2982835 := bstep (se 1 (by rfl) ⟨2237126, by rfl⟩ : syracuseStep 2982835 = 4474253) B4474253
theorem B3977113 : Blo 2093435 3977113 := bstep (se 2 (by rfl) ⟨1491417, by rfl⟩ : syracuseStep 3977113 = 2982835) B2982835
theorem B5302817 : Blo 2093435 5302817 := bstep (se 2 (by rfl) ⟨1988556, by rfl⟩ : syracuseStep 5302817 = 3977113) B3977113
theorem B3535211 : Blo 2093435 3535211 := bstep (se 1 (by rfl) ⟨2651408, by rfl⟩ : syracuseStep 3535211 = 5302817) B5302817
theorem B2356807 : Blo 2093435 2356807 := bstep (se 1 (by rfl) ⟨1767605, by rfl⟩ : syracuseStep 2356807 = 3535211) B3535211
theorem B3142409 : Blo 2093435 3142409 := bstep (se 2 (by rfl) ⟨1178403, by rfl⟩ : syracuseStep 3142409 = 2356807) B2356807
theorem B2094939 : Blo 2093435 2094939 := bstep (se 1 (by rfl) ⟨1571204, by rfl⟩ : syracuseStep 2094939 = 3142409) B3142409
theorem B10605653 : Blo 2093435 10605653 := bbase (se 8 (by rfl) ⟨62142, by rfl⟩ : syracuseStep 10605653 = 124285) (by norm_num)
theorem B7070435 : Blo 2093435 7070435 := bstep (se 1 (by rfl) ⟨5302826, by rfl⟩ : syracuseStep 7070435 = 10605653) B10605653
theorem B4713623 : Blo 2093435 4713623 := bstep (se 1 (by rfl) ⟨3535217, by rfl⟩ : syracuseStep 4713623 = 7070435) B7070435
theorem B3142415 : Blo 2093435 3142415 := bstep (se 1 (by rfl) ⟨2356811, by rfl⟩ : syracuseStep 3142415 = 4713623) B4713623
theorem B2094943 : Blo 2093435 2094943 := bstep (se 1 (by rfl) ⟨1571207, by rfl⟩ : syracuseStep 2094943 = 3142415) B3142415
theorem B3142421 : Blo 2093435 3142421 := bbase (se 6 (by rfl) ⟨73650, by rfl⟩ : syracuseStep 3142421 = 147301) (by norm_num)
theorem B2094947 : Blo 2093435 2094947 := bstep (se 1 (by rfl) ⟨1571210, by rfl⟩ : syracuseStep 2094947 = 3142421) B3142421
theorem B40268501 : Blo 2093435 40268501 := bbase (se 7 (by rfl) ⟨471896, by rfl⟩ : syracuseStep 40268501 = 943793) (by norm_num)
theorem B26845667 : Blo 2093435 26845667 := bstep (se 1 (by rfl) ⟨20134250, by rfl⟩ : syracuseStep 26845667 = 40268501) B40268501
theorem B17897111 : Blo 2093435 17897111 := bstep (se 1 (by rfl) ⟨13422833, by rfl⟩ : syracuseStep 17897111 = 26845667) B26845667
theorem B11931407 : Blo 2093435 11931407 := bstep (se 1 (by rfl) ⟨8948555, by rfl⟩ : syracuseStep 11931407 = 17897111) B17897111
theorem B7954271 : Blo 2093435 7954271 := bstep (se 1 (by rfl) ⟨5965703, by rfl⟩ : syracuseStep 7954271 = 11931407) B11931407
theorem B5302847 : Blo 2093435 5302847 := bstep (se 1 (by rfl) ⟨3977135, by rfl⟩ : syracuseStep 5302847 = 7954271) B7954271
theorem B3535231 : Blo 2093435 3535231 := bstep (se 1 (by rfl) ⟨2651423, by rfl⟩ : syracuseStep 3535231 = 5302847) B5302847
theorem B4713641 : Blo 2093435 4713641 := bstep (se 2 (by rfl) ⟨1767615, by rfl⟩ : syracuseStep 4713641 = 3535231) B3535231
theorem B3142427 : Blo 2093435 3142427 := bstep (se 1 (by rfl) ⟨2356820, by rfl⟩ : syracuseStep 3142427 = 4713641) B4713641
theorem B2094951 : Blo 2093435 2094951 := bstep (se 1 (by rfl) ⟨1571213, by rfl⟩ : syracuseStep 2094951 = 3142427) B3142427
theorem B2356825 : Blo 2093435 2356825 := bbase (se 2 (by rfl) ⟨883809, by rfl⟩ : syracuseStep 2356825 = 1767619) (by norm_num)
theorem B3142433 : Blo 2093435 3142433 := bstep (se 2 (by rfl) ⟨1178412, by rfl⟩ : syracuseStep 3142433 = 2356825) B2356825
theorem B2094955 : Blo 2093435 2094955 := bstep (se 1 (by rfl) ⟨1571216, by rfl⟩ : syracuseStep 2094955 = 3142433) B3142433
theorem B4777973 : Blo 2093435 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B3185315 : Blo 2093435 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B2123543 : Blo 2093435 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B5662781 : Blo 2093435 5662781 := bstep (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) B2123543
theorem B3775187 : Blo 2093435 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B10067165 : Blo 2093435 10067165 := bstep (se 3 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 10067165 = 3775187) B3775187
theorem B6711443 : Blo 2093435 6711443 := bstep (se 1 (by rfl) ⟨5033582, by rfl⟩ : syracuseStep 6711443 = 10067165) B10067165
theorem B4474295 : Blo 2093435 4474295 := bstep (se 1 (by rfl) ⟨3355721, by rfl⟩ : syracuseStep 4474295 = 6711443) B6711443
theorem B2982863 : Blo 2093435 2982863 := bstep (se 1 (by rfl) ⟨2237147, by rfl⟩ : syracuseStep 2982863 = 4474295) B4474295
theorem B7954301 : Blo 2093435 7954301 := bstep (se 3 (by rfl) ⟨1491431, by rfl⟩ : syracuseStep 7954301 = 2982863) B2982863
theorem B5302867 : Blo 2093435 5302867 := bstep (se 1 (by rfl) ⟨3977150, by rfl⟩ : syracuseStep 5302867 = 7954301) B7954301
theorem B7070489 : Blo 2093435 7070489 := bstep (se 2 (by rfl) ⟨2651433, by rfl⟩ : syracuseStep 7070489 = 5302867) B5302867
theorem B4713659 : Blo 2093435 4713659 := bstep (se 1 (by rfl) ⟨3535244, by rfl⟩ : syracuseStep 4713659 = 7070489) B7070489
theorem B3142439 : Blo 2093435 3142439 := bstep (se 1 (by rfl) ⟨2356829, by rfl⟩ : syracuseStep 3142439 = 4713659) B4713659
theorem B2094959 : Blo 2093435 2094959 := bstep (se 1 (by rfl) ⟨1571219, by rfl⟩ : syracuseStep 2094959 = 3142439) B3142439
theorem B3142445 : Blo 2093435 3142445 := bbase (se 3 (by rfl) ⟨589208, by rfl⟩ : syracuseStep 3142445 = 1178417) (by norm_num)
theorem B2094963 : Blo 2093435 2094963 := bstep (se 1 (by rfl) ⟨1571222, by rfl⟩ : syracuseStep 2094963 = 3142445) B3142445
theorem B4713677 : Blo 2093435 4713677 := bbase (se 3 (by rfl) ⟨883814, by rfl⟩ : syracuseStep 4713677 = 1767629) (by norm_num)
theorem B3142451 : Blo 2093435 3142451 := bstep (se 1 (by rfl) ⟨2356838, by rfl⟩ : syracuseStep 3142451 = 4713677) B4713677
theorem B2094967 : Blo 2093435 2094967 := bstep (se 1 (by rfl) ⟨1571225, by rfl⟩ : syracuseStep 2094967 = 3142451) B3142451
theorem B2651449 : Blo 2093435 2651449 := bbase (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) (by norm_num)
theorem B3535265 : Blo 2093435 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B2356843 : Blo 2093435 2356843 := bstep (se 1 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 2356843 = 3535265) B3535265
theorem B3142457 : Blo 2093435 3142457 := bstep (se 2 (by rfl) ⟨1178421, by rfl⟩ : syracuseStep 3142457 = 2356843) B2356843
theorem B2094971 : Blo 2093435 2094971 := bstep (se 1 (by rfl) ⟨1571228, by rfl⟩ : syracuseStep 2094971 = 3142457) B3142457
theorem B6711493 : Blo 2093435 6711493 := bbase (se 4 (by rfl) ⟨629202, by rfl⟩ : syracuseStep 6711493 = 1258405) (by norm_num)
theorem B8948657 : Blo 2093435 8948657 := bstep (se 2 (by rfl) ⟨3355746, by rfl⟩ : syracuseStep 8948657 = 6711493) B6711493
theorem B23863085 : Blo 2093435 23863085 := bstep (se 3 (by rfl) ⟨4474328, by rfl⟩ : syracuseStep 23863085 = 8948657) B8948657
theorem B15908723 : Blo 2093435 15908723 := bstep (se 1 (by rfl) ⟨11931542, by rfl⟩ : syracuseStep 15908723 = 23863085) B23863085
theorem B10605815 : Blo 2093435 10605815 := bstep (se 1 (by rfl) ⟨7954361, by rfl⟩ : syracuseStep 10605815 = 15908723) B15908723
theorem B7070543 : Blo 2093435 7070543 := bstep (se 1 (by rfl) ⟨5302907, by rfl⟩ : syracuseStep 7070543 = 10605815) B10605815
theorem B4713695 : Blo 2093435 4713695 := bstep (se 1 (by rfl) ⟨3535271, by rfl⟩ : syracuseStep 4713695 = 7070543) B7070543
theorem B3142463 : Blo 2093435 3142463 := bstep (se 1 (by rfl) ⟨2356847, by rfl⟩ : syracuseStep 3142463 = 4713695) B4713695
theorem B2094975 : Blo 2093435 2094975 := bstep (se 1 (by rfl) ⟨1571231, by rfl⟩ : syracuseStep 2094975 = 3142463) B3142463
theorem B3142469 : Blo 2093435 3142469 := bbase (se 4 (by rfl) ⟨294606, by rfl⟩ : syracuseStep 3142469 = 589213) (by norm_num)
theorem B2094979 : Blo 2093435 2094979 := bstep (se 1 (by rfl) ⟨1571234, by rfl⟩ : syracuseStep 2094979 = 3142469) B3142469
theorem B3535285 : Blo 2093435 3535285 := bbase (se 5 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 3535285 = 331433) (by norm_num)
theorem B4713713 : Blo 2093435 4713713 := bstep (se 2 (by rfl) ⟨1767642, by rfl⟩ : syracuseStep 4713713 = 3535285) B3535285
theorem B3142475 : Blo 2093435 3142475 := bstep (se 1 (by rfl) ⟨2356856, by rfl⟩ : syracuseStep 3142475 = 4713713) B4713713
theorem B2094983 : Blo 2093435 2094983 := bstep (se 1 (by rfl) ⟨1571237, by rfl⟩ : syracuseStep 2094983 = 3142475) B3142475
theorem B2356861 : Blo 2093435 2356861 := bbase (se 3 (by rfl) ⟨441911, by rfl⟩ : syracuseStep 2356861 = 883823) (by norm_num)
theorem B3142481 : Blo 2093435 3142481 := bstep (se 2 (by rfl) ⟨1178430, by rfl⟩ : syracuseStep 3142481 = 2356861) B2356861
theorem B2094987 : Blo 2093435 2094987 := bstep (se 1 (by rfl) ⟨1571240, by rfl⟩ : syracuseStep 2094987 = 3142481) B3142481
theorem B7070597 : Blo 2093435 7070597 := bbase (se 4 (by rfl) ⟨662868, by rfl⟩ : syracuseStep 7070597 = 1325737) (by norm_num)
theorem B4713731 : Blo 2093435 4713731 := bstep (se 1 (by rfl) ⟨3535298, by rfl⟩ : syracuseStep 4713731 = 7070597) B7070597
theorem B3142487 : Blo 2093435 3142487 := bstep (se 1 (by rfl) ⟨2356865, by rfl⟩ : syracuseStep 3142487 = 4713731) B4713731
theorem B2094991 : Blo 2093435 2094991 := bstep (se 1 (by rfl) ⟨1571243, by rfl⟩ : syracuseStep 2094991 = 3142487) B3142487
theorem B3142493 : Blo 2093435 3142493 := bbase (se 3 (by rfl) ⟨589217, by rfl⟩ : syracuseStep 3142493 = 1178435) (by norm_num)
theorem B2094995 : Blo 2093435 2094995 := bstep (se 1 (by rfl) ⟨1571246, by rfl⟩ : syracuseStep 2094995 = 3142493) B3142493
theorem B4713749 : Blo 2093435 4713749 := bbase (se 6 (by rfl) ⟨110478, by rfl⟩ : syracuseStep 4713749 = 220957) (by norm_num)
theorem B3142499 : Blo 2093435 3142499 := bstep (se 1 (by rfl) ⟨2356874, by rfl⟩ : syracuseStep 3142499 = 4713749) B4713749
theorem B2094999 : Blo 2093435 2094999 := bstep (se 1 (by rfl) ⟨1571249, by rfl⟩ : syracuseStep 2094999 = 3142499) B3142499
theorem B7954469 : Blo 2093435 7954469 := bbase (se 4 (by rfl) ⟨745731, by rfl⟩ : syracuseStep 7954469 = 1491463) (by norm_num)
theorem B5302979 : Blo 2093435 5302979 := bstep (se 1 (by rfl) ⟨3977234, by rfl⟩ : syracuseStep 5302979 = 7954469) B7954469
theorem B3535319 : Blo 2093435 3535319 := bstep (se 1 (by rfl) ⟨2651489, by rfl⟩ : syracuseStep 3535319 = 5302979) B5302979
theorem B2356879 : Blo 2093435 2356879 := bstep (se 1 (by rfl) ⟨1767659, by rfl⟩ : syracuseStep 2356879 = 3535319) B3535319
theorem B3142505 : Blo 2093435 3142505 := bstep (se 2 (by rfl) ⟨1178439, by rfl⟩ : syracuseStep 3142505 = 2356879) B2356879
theorem B2095003 : Blo 2093435 2095003 := bstep (se 1 (by rfl) ⟨1571252, by rfl⟩ : syracuseStep 2095003 = 3142505) B3142505
theorem B4474397 : Blo 2093435 4474397 := bbase (se 3 (by rfl) ⟨838949, by rfl⟩ : syracuseStep 4474397 = 1677899) (by norm_num)
theorem B11931725 : Blo 2093435 11931725 := bstep (se 3 (by rfl) ⟨2237198, by rfl⟩ : syracuseStep 11931725 = 4474397) B4474397
theorem B7954483 : Blo 2093435 7954483 := bstep (se 1 (by rfl) ⟨5965862, by rfl⟩ : syracuseStep 7954483 = 11931725) B11931725
theorem B10605977 : Blo 2093435 10605977 := bstep (se 2 (by rfl) ⟨3977241, by rfl⟩ : syracuseStep 10605977 = 7954483) B7954483
theorem B7070651 : Blo 2093435 7070651 := bstep (se 1 (by rfl) ⟨5302988, by rfl⟩ : syracuseStep 7070651 = 10605977) B10605977
theorem B4713767 : Blo 2093435 4713767 := bstep (se 1 (by rfl) ⟨3535325, by rfl⟩ : syracuseStep 4713767 = 7070651) B7070651
theorem B3142511 : Blo 2093435 3142511 := bstep (se 1 (by rfl) ⟨2356883, by rfl⟩ : syracuseStep 3142511 = 4713767) B4713767
theorem B2095007 : Blo 2093435 2095007 := bstep (se 1 (by rfl) ⟨1571255, by rfl⟩ : syracuseStep 2095007 = 3142511) B3142511
theorem B3142517 : Blo 2093435 3142517 := bbase (se 5 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 3142517 = 294611) (by norm_num)
theorem B2095011 : Blo 2093435 2095011 := bstep (se 1 (by rfl) ⟨1571258, by rfl⟩ : syracuseStep 2095011 = 3142517) B3142517
theorem B8610293 : Blo 2093435 8610293 := bbase (se 5 (by rfl) ⟨403607, by rfl⟩ : syracuseStep 8610293 = 807215) (by norm_num)
theorem B5740195 : Blo 2093435 5740195 := bstep (se 1 (by rfl) ⟨4305146, by rfl⟩ : syracuseStep 5740195 = 8610293) B8610293
theorem B7653593 : Blo 2093435 7653593 := bstep (se 2 (by rfl) ⟨2870097, by rfl⟩ : syracuseStep 7653593 = 5740195) B5740195
theorem B5102395 : Blo 2093435 5102395 := bstep (se 1 (by rfl) ⟨3826796, by rfl⟩ : syracuseStep 5102395 = 7653593) B7653593
theorem B27212773 : Blo 2093435 27212773 := bstep (se 4 (by rfl) ⟨2551197, by rfl⟩ : syracuseStep 27212773 = 5102395) B5102395
theorem B36283697 : Blo 2093435 36283697 := bstep (se 2 (by rfl) ⟨13606386, by rfl⟩ : syracuseStep 36283697 = 27212773) B27212773
theorem B24189131 : Blo 2093435 24189131 := bstep (se 1 (by rfl) ⟨18141848, by rfl⟩ : syracuseStep 24189131 = 36283697) B36283697
theorem B64504349 : Blo 2093435 64504349 := bstep (se 3 (by rfl) ⟨12094565, by rfl⟩ : syracuseStep 64504349 = 24189131) B24189131
theorem B43002899 : Blo 2093435 43002899 := bstep (se 1 (by rfl) ⟨32252174, by rfl⟩ : syracuseStep 43002899 = 64504349) B64504349
theorem B28668599 : Blo 2093435 28668599 := bstep (se 1 (by rfl) ⟨21501449, by rfl⟩ : syracuseStep 28668599 = 43002899) B43002899
theorem B19112399 : Blo 2093435 19112399 := bstep (se 1 (by rfl) ⟨14334299, by rfl⟩ : syracuseStep 19112399 = 28668599) B28668599
theorem B12741599 : Blo 2093435 12741599 := bstep (se 1 (by rfl) ⟨9556199, by rfl⟩ : syracuseStep 12741599 = 19112399) B19112399
theorem B8494399 : Blo 2093435 8494399 := bstep (se 1 (by rfl) ⟨6370799, by rfl⟩ : syracuseStep 8494399 = 12741599) B12741599
theorem B11325865 : Blo 2093435 11325865 := bstep (se 2 (by rfl) ⟨4247199, by rfl⟩ : syracuseStep 11325865 = 8494399) B8494399
theorem B15101153 : Blo 2093435 15101153 := bstep (se 2 (by rfl) ⟨5662932, by rfl⟩ : syracuseStep 15101153 = 11325865) B11325865
theorem B10067435 : Blo 2093435 10067435 := bstep (se 1 (by rfl) ⟨7550576, by rfl⟩ : syracuseStep 10067435 = 15101153) B15101153
theorem B6711623 : Blo 2093435 6711623 := bstep (se 1 (by rfl) ⟨5033717, by rfl⟩ : syracuseStep 6711623 = 10067435) B10067435
theorem B4474415 : Blo 2093435 4474415 := bstep (se 1 (by rfl) ⟨3355811, by rfl⟩ : syracuseStep 4474415 = 6711623) B6711623
theorem B2982943 : Blo 2093435 2982943 := bstep (se 1 (by rfl) ⟨2237207, by rfl⟩ : syracuseStep 2982943 = 4474415) B4474415
theorem B3977257 : Blo 2093435 3977257 := bstep (se 2 (by rfl) ⟨1491471, by rfl⟩ : syracuseStep 3977257 = 2982943) B2982943
theorem B5303009 : Blo 2093435 5303009 := bstep (se 2 (by rfl) ⟨1988628, by rfl⟩ : syracuseStep 5303009 = 3977257) B3977257
theorem B3535339 : Blo 2093435 3535339 := bstep (se 1 (by rfl) ⟨2651504, by rfl⟩ : syracuseStep 3535339 = 5303009) B5303009
theorem B4713785 : Blo 2093435 4713785 := bstep (se 2 (by rfl) ⟨1767669, by rfl⟩ : syracuseStep 4713785 = 3535339) B3535339
theorem B3142523 : Blo 2093435 3142523 := bstep (se 1 (by rfl) ⟨2356892, by rfl⟩ : syracuseStep 3142523 = 4713785) B4713785
theorem B2095015 : Blo 2093435 2095015 := bstep (se 1 (by rfl) ⟨1571261, by rfl⟩ : syracuseStep 2095015 = 3142523) B3142523
theorem B2356897 : Blo 2093435 2356897 := bbase (se 2 (by rfl) ⟨883836, by rfl⟩ : syracuseStep 2356897 = 1767673) (by norm_num)
theorem B3142529 : Blo 2093435 3142529 := bstep (se 2 (by rfl) ⟨1178448, by rfl⟩ : syracuseStep 3142529 = 2356897) B2356897
theorem B2095019 : Blo 2093435 2095019 := bstep (se 1 (by rfl) ⟨1571264, by rfl⟩ : syracuseStep 2095019 = 3142529) B3142529
theorem B5303029 : Blo 2093435 5303029 := bbase (se 5 (by rfl) ⟨248579, by rfl⟩ : syracuseStep 5303029 = 497159) (by norm_num)
theorem B7070705 : Blo 2093435 7070705 := bstep (se 2 (by rfl) ⟨2651514, by rfl⟩ : syracuseStep 7070705 = 5303029) B5303029
theorem B4713803 : Blo 2093435 4713803 := bstep (se 1 (by rfl) ⟨3535352, by rfl⟩ : syracuseStep 4713803 = 7070705) B7070705
theorem B3142535 : Blo 2093435 3142535 := bstep (se 1 (by rfl) ⟨2356901, by rfl⟩ : syracuseStep 3142535 = 4713803) B4713803
theorem B2095023 : Blo 2093435 2095023 := bstep (se 1 (by rfl) ⟨1571267, by rfl⟩ : syracuseStep 2095023 = 3142535) B3142535
theorem B3142541 : Blo 2093435 3142541 := bbase (se 3 (by rfl) ⟨589226, by rfl⟩ : syracuseStep 3142541 = 1178453) (by norm_num)
theorem B2095027 : Blo 2093435 2095027 := bstep (se 1 (by rfl) ⟨1571270, by rfl⟩ : syracuseStep 2095027 = 3142541) B3142541
theorem B4713821 : Blo 2093435 4713821 := bbase (se 3 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 4713821 = 1767683) (by norm_num)
theorem B3142547 : Blo 2093435 3142547 := bstep (se 1 (by rfl) ⟨2356910, by rfl⟩ : syracuseStep 3142547 = 4713821) B4713821
theorem B2095031 : Blo 2093435 2095031 := bstep (se 1 (by rfl) ⟨1571273, by rfl⟩ : syracuseStep 2095031 = 3142547) B3142547
theorem B3535373 : Blo 2093435 3535373 := bbase (se 3 (by rfl) ⟨662882, by rfl⟩ : syracuseStep 3535373 = 1325765) (by norm_num)
theorem B2356915 : Blo 2093435 2356915 := bstep (se 1 (by rfl) ⟨1767686, by rfl⟩ : syracuseStep 2356915 = 3535373) B3535373
theorem B3142553 : Blo 2093435 3142553 := bstep (se 2 (by rfl) ⟨1178457, by rfl⟩ : syracuseStep 3142553 = 2356915) B2356915
theorem B2095035 : Blo 2093435 2095035 := bstep (se 1 (by rfl) ⟨1571276, by rfl⟩ : syracuseStep 2095035 = 3142553) B3142553
theorem B5662997 : Blo 2093435 5662997 := bbase (se 6 (by rfl) ⟨132726, by rfl⟩ : syracuseStep 5662997 = 265453) (by norm_num)
theorem B3775331 : Blo 2093435 3775331 := bstep (se 1 (by rfl) ⟨2831498, by rfl⟩ : syracuseStep 3775331 = 5662997) B5662997
theorem B2516887 : Blo 2093435 2516887 := bstep (se 1 (by rfl) ⟨1887665, by rfl⟩ : syracuseStep 2516887 = 3775331) B3775331
theorem B3355849 : Blo 2093435 3355849 := bstep (se 2 (by rfl) ⟨1258443, by rfl⟩ : syracuseStep 3355849 = 2516887) B2516887
theorem B17897861 : Blo 2093435 17897861 := bstep (se 4 (by rfl) ⟨1677924, by rfl⟩ : syracuseStep 17897861 = 3355849) B3355849
theorem B11931907 : Blo 2093435 11931907 := bstep (se 1 (by rfl) ⟨8948930, by rfl⟩ : syracuseStep 11931907 = 17897861) B17897861
theorem B15909209 : Blo 2093435 15909209 := bstep (se 2 (by rfl) ⟨5965953, by rfl⟩ : syracuseStep 15909209 = 11931907) B11931907
theorem B10606139 : Blo 2093435 10606139 := bstep (se 1 (by rfl) ⟨7954604, by rfl⟩ : syracuseStep 10606139 = 15909209) B15909209
theorem B7070759 : Blo 2093435 7070759 := bstep (se 1 (by rfl) ⟨5303069, by rfl⟩ : syracuseStep 7070759 = 10606139) B10606139
theorem B4713839 : Blo 2093435 4713839 := bstep (se 1 (by rfl) ⟨3535379, by rfl⟩ : syracuseStep 4713839 = 7070759) B7070759
theorem B3142559 : Blo 2093435 3142559 := bstep (se 1 (by rfl) ⟨2356919, by rfl⟩ : syracuseStep 3142559 = 4713839) B4713839
theorem B2095039 : Blo 2093435 2095039 := bstep (se 1 (by rfl) ⟨1571279, by rfl⟩ : syracuseStep 2095039 = 3142559) B3142559
theorem B3142565 : Blo 2093435 3142565 := bbase (se 4 (by rfl) ⟨294615, by rfl⟩ : syracuseStep 3142565 = 589231) (by norm_num)
theorem B2095043 : Blo 2093435 2095043 := bstep (se 1 (by rfl) ⟨1571282, by rfl⟩ : syracuseStep 2095043 = 3142565) B3142565
theorem B2651545 : Blo 2093435 2651545 := bbase (se 2 (by rfl) ⟨994329, by rfl⟩ : syracuseStep 2651545 = 1988659) (by norm_num)
theorem B3535393 : Blo 2093435 3535393 := bstep (se 2 (by rfl) ⟨1325772, by rfl⟩ : syracuseStep 3535393 = 2651545) B2651545
theorem B4713857 : Blo 2093435 4713857 := bstep (se 2 (by rfl) ⟨1767696, by rfl⟩ : syracuseStep 4713857 = 3535393) B3535393
theorem B3142571 : Blo 2093435 3142571 := bstep (se 1 (by rfl) ⟨2356928, by rfl⟩ : syracuseStep 3142571 = 4713857) B4713857
theorem B2095047 : Blo 2093435 2095047 := bstep (se 1 (by rfl) ⟨1571285, by rfl⟩ : syracuseStep 2095047 = 3142571) B3142571
theorem B2356933 : Blo 2093435 2356933 := bbase (se 4 (by rfl) ⟨220962, by rfl⟩ : syracuseStep 2356933 = 441925) (by norm_num)
theorem B3142577 : Blo 2093435 3142577 := bstep (se 2 (by rfl) ⟨1178466, by rfl⟩ : syracuseStep 3142577 = 2356933) B2356933
theorem B2095051 : Blo 2093435 2095051 := bstep (se 1 (by rfl) ⟨1571288, by rfl⟩ : syracuseStep 2095051 = 3142577) B3142577
theorem B3977333 : Blo 2093435 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B2651555 : Blo 2093435 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B7070813 : Blo 2093435 7070813 := bstep (se 3 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 7070813 = 2651555) B2651555
theorem B4713875 : Blo 2093435 4713875 := bstep (se 1 (by rfl) ⟨3535406, by rfl⟩ : syracuseStep 4713875 = 7070813) B7070813
theorem B3142583 : Blo 2093435 3142583 := bstep (se 1 (by rfl) ⟨2356937, by rfl⟩ : syracuseStep 3142583 = 4713875) B4713875
theorem B2095055 : Blo 2093435 2095055 := bstep (se 1 (by rfl) ⟨1571291, by rfl⟩ : syracuseStep 2095055 = 3142583) B3142583
theorem B3142589 : Blo 2093435 3142589 := bbase (se 3 (by rfl) ⟨589235, by rfl⟩ : syracuseStep 3142589 = 1178471) (by norm_num)
theorem B2095059 : Blo 2093435 2095059 := bstep (se 1 (by rfl) ⟨1571294, by rfl⟩ : syracuseStep 2095059 = 3142589) B3142589
theorem B4713893 : Blo 2093435 4713893 := bbase (se 4 (by rfl) ⟨441927, by rfl⟩ : syracuseStep 4713893 = 883855) (by norm_num)
theorem B3142595 : Blo 2093435 3142595 := bstep (se 1 (by rfl) ⟨2356946, by rfl⟩ : syracuseStep 3142595 = 4713893) B4713893
theorem B2095063 : Blo 2093435 2095063 := bstep (se 1 (by rfl) ⟨1571297, by rfl⟩ : syracuseStep 2095063 = 3142595) B3142595
theorem B5303141 : Blo 2093435 5303141 := bbase (se 4 (by rfl) ⟨497169, by rfl⟩ : syracuseStep 5303141 = 994339) (by norm_num)
theorem B3535427 : Blo 2093435 3535427 := bstep (se 1 (by rfl) ⟨2651570, by rfl⟩ : syracuseStep 3535427 = 5303141) B5303141
theorem B2356951 : Blo 2093435 2356951 := bstep (se 1 (by rfl) ⟨1767713, by rfl⟩ : syracuseStep 2356951 = 3535427) B3535427
theorem B3142601 : Blo 2093435 3142601 := bstep (se 2 (by rfl) ⟨1178475, by rfl⟩ : syracuseStep 3142601 = 2356951) B2356951
theorem B2095067 : Blo 2093435 2095067 := bstep (se 1 (by rfl) ⟨1571300, by rfl⟩ : syracuseStep 2095067 = 3142601) B3142601
theorem B3355901 : Blo 2093435 3355901 := bbase (se 3 (by rfl) ⟨629231, by rfl⟩ : syracuseStep 3355901 = 1258463) (by norm_num)
theorem B2237267 : Blo 2093435 2237267 := bstep (se 1 (by rfl) ⟨1677950, by rfl⟩ : syracuseStep 2237267 = 3355901) B3355901
theorem B5966045 : Blo 2093435 5966045 := bstep (se 3 (by rfl) ⟨1118633, by rfl⟩ : syracuseStep 5966045 = 2237267) B2237267
theorem B3977363 : Blo 2093435 3977363 := bstep (se 1 (by rfl) ⟨2983022, by rfl⟩ : syracuseStep 3977363 = 5966045) B5966045
theorem B10606301 : Blo 2093435 10606301 := bstep (se 3 (by rfl) ⟨1988681, by rfl⟩ : syracuseStep 10606301 = 3977363) B3977363
theorem B7070867 : Blo 2093435 7070867 := bstep (se 1 (by rfl) ⟨5303150, by rfl⟩ : syracuseStep 7070867 = 10606301) B10606301
theorem B4713911 : Blo 2093435 4713911 := bstep (se 1 (by rfl) ⟨3535433, by rfl⟩ : syracuseStep 4713911 = 7070867) B7070867
theorem B3142607 : Blo 2093435 3142607 := bstep (se 1 (by rfl) ⟨2356955, by rfl⟩ : syracuseStep 3142607 = 4713911) B4713911
theorem B2095071 : Blo 2093435 2095071 := bstep (se 1 (by rfl) ⟨1571303, by rfl⟩ : syracuseStep 2095071 = 3142607) B3142607
theorem B3142613 : Blo 2093435 3142613 := bbase (se 7 (by rfl) ⟨36827, by rfl⟩ : syracuseStep 3142613 = 73655) (by norm_num)
theorem B2095075 : Blo 2093435 2095075 := bstep (se 1 (by rfl) ⟨1571306, by rfl⟩ : syracuseStep 2095075 = 3142613) B3142613
theorem B7954757 : Blo 2093435 7954757 := bbase (se 4 (by rfl) ⟨745758, by rfl⟩ : syracuseStep 7954757 = 1491517) (by norm_num)
theorem B5303171 : Blo 2093435 5303171 := bstep (se 1 (by rfl) ⟨3977378, by rfl⟩ : syracuseStep 5303171 = 7954757) B7954757
theorem B3535447 : Blo 2093435 3535447 := bstep (se 1 (by rfl) ⟨2651585, by rfl⟩ : syracuseStep 3535447 = 5303171) B5303171
theorem B4713929 : Blo 2093435 4713929 := bstep (se 2 (by rfl) ⟨1767723, by rfl⟩ : syracuseStep 4713929 = 3535447) B3535447
theorem B3142619 : Blo 2093435 3142619 := bstep (se 1 (by rfl) ⟨2356964, by rfl⟩ : syracuseStep 3142619 = 4713929) B4713929
theorem B2095079 : Blo 2093435 2095079 := bstep (se 1 (by rfl) ⟨1571309, by rfl⟩ : syracuseStep 2095079 = 3142619) B3142619
theorem B2356969 : Blo 2093435 2356969 := bbase (se 2 (by rfl) ⟨883863, by rfl⟩ : syracuseStep 2356969 = 1767727) (by norm_num)
theorem B3142625 : Blo 2093435 3142625 := bstep (se 2 (by rfl) ⟨1178484, by rfl⟩ : syracuseStep 3142625 = 2356969) B2356969
theorem B2095083 : Blo 2093435 2095083 := bstep (se 1 (by rfl) ⟨1571312, by rfl⟩ : syracuseStep 2095083 = 3142625) B3142625
theorem B11932181 : Blo 2093435 11932181 := bbase (se 6 (by rfl) ⟨279660, by rfl⟩ : syracuseStep 11932181 = 559321) (by norm_num)
theorem B7954787 : Blo 2093435 7954787 := bstep (se 1 (by rfl) ⟨5966090, by rfl⟩ : syracuseStep 7954787 = 11932181) B11932181
theorem B5303191 : Blo 2093435 5303191 := bstep (se 1 (by rfl) ⟨3977393, by rfl⟩ : syracuseStep 5303191 = 7954787) B7954787
theorem B7070921 : Blo 2093435 7070921 := bstep (se 2 (by rfl) ⟨2651595, by rfl⟩ : syracuseStep 7070921 = 5303191) B5303191
theorem B4713947 : Blo 2093435 4713947 := bstep (se 1 (by rfl) ⟨3535460, by rfl⟩ : syracuseStep 4713947 = 7070921) B7070921
theorem B3142631 : Blo 2093435 3142631 := bstep (se 1 (by rfl) ⟨2356973, by rfl⟩ : syracuseStep 3142631 = 4713947) B4713947
theorem B2095087 : Blo 2093435 2095087 := bstep (se 1 (by rfl) ⟨1571315, by rfl⟩ : syracuseStep 2095087 = 3142631) B3142631
theorem B3142637 : Blo 2093435 3142637 := bbase (se 3 (by rfl) ⟨589244, by rfl⟩ : syracuseStep 3142637 = 1178489) (by norm_num)
theorem B2095091 : Blo 2093435 2095091 := bstep (se 1 (by rfl) ⟨1571318, by rfl⟩ : syracuseStep 2095091 = 3142637) B3142637
theorem B4713965 : Blo 2093435 4713965 := bbase (se 3 (by rfl) ⟨883868, by rfl⟩ : syracuseStep 4713965 = 1767737) (by norm_num)
theorem B3142643 : Blo 2093435 3142643 := bstep (se 1 (by rfl) ⟨2356982, by rfl⟩ : syracuseStep 3142643 = 4713965) B4713965
theorem B2095095 : Blo 2093435 2095095 := bstep (se 1 (by rfl) ⟨1571321, by rfl⟩ : syracuseStep 2095095 = 3142643) B3142643
theorem B6711893 : Blo 2093435 6711893 := bbase (se 8 (by rfl) ⟨39327, by rfl⟩ : syracuseStep 6711893 = 78655) (by norm_num)
theorem B4474595 : Blo 2093435 4474595 := bstep (se 1 (by rfl) ⟨3355946, by rfl⟩ : syracuseStep 4474595 = 6711893) B6711893
theorem B2983063 : Blo 2093435 2983063 := bstep (se 1 (by rfl) ⟨2237297, by rfl⟩ : syracuseStep 2983063 = 4474595) B4474595
theorem B3977417 : Blo 2093435 3977417 := bstep (se 2 (by rfl) ⟨1491531, by rfl⟩ : syracuseStep 3977417 = 2983063) B2983063
theorem B2651611 : Blo 2093435 2651611 := bstep (se 1 (by rfl) ⟨1988708, by rfl⟩ : syracuseStep 2651611 = 3977417) B3977417
theorem B3535481 : Blo 2093435 3535481 := bstep (se 2 (by rfl) ⟨1325805, by rfl⟩ : syracuseStep 3535481 = 2651611) B2651611
theorem B2356987 : Blo 2093435 2356987 := bstep (se 1 (by rfl) ⟨1767740, by rfl⟩ : syracuseStep 2356987 = 3535481) B3535481
theorem B3142649 : Blo 2093435 3142649 := bstep (se 2 (by rfl) ⟨1178493, by rfl⟩ : syracuseStep 3142649 = 2356987) B2356987
theorem B2095099 : Blo 2093435 2095099 := bstep (se 1 (by rfl) ⟨1571324, by rfl⟩ : syracuseStep 2095099 = 3142649) B3142649
theorem B36285205 : Blo 2093435 36285205 := bbase (se 6 (by rfl) ⟨850434, by rfl⟩ : syracuseStep 36285205 = 1700869) (by norm_num)
theorem B48380273 : Blo 2093435 48380273 := bstep (se 2 (by rfl) ⟨18142602, by rfl⟩ : syracuseStep 48380273 = 36285205) B36285205
theorem B32253515 : Blo 2093435 32253515 := bstep (se 1 (by rfl) ⟨24190136, by rfl⟩ : syracuseStep 32253515 = 48380273) B48380273
theorem B21502343 : Blo 2093435 21502343 := bstep (se 1 (by rfl) ⟨16126757, by rfl⟩ : syracuseStep 21502343 = 32253515) B32253515
theorem B14334895 : Blo 2093435 14334895 := bstep (se 1 (by rfl) ⟨10751171, by rfl⟩ : syracuseStep 14334895 = 21502343) B21502343
theorem B19113193 : Blo 2093435 19113193 := bstep (se 2 (by rfl) ⟨7167447, by rfl⟩ : syracuseStep 19113193 = 14334895) B14334895
theorem B25484257 : Blo 2093435 25484257 := bstep (se 2 (by rfl) ⟨9556596, by rfl⟩ : syracuseStep 25484257 = 19113193) B19113193
theorem B33979009 : Blo 2093435 33979009 := bstep (se 2 (by rfl) ⟨12742128, by rfl⟩ : syracuseStep 33979009 = 25484257) B25484257
theorem B45305345 : Blo 2093435 45305345 := bstep (se 2 (by rfl) ⟨16989504, by rfl⟩ : syracuseStep 45305345 = 33979009) B33979009
theorem B120814253 : Blo 2093435 120814253 := bstep (se 3 (by rfl) ⟨22652672, by rfl⟩ : syracuseStep 120814253 = 45305345) B45305345
theorem B80542835 : Blo 2093435 80542835 := bstep (se 1 (by rfl) ⟨60407126, by rfl⟩ : syracuseStep 80542835 = 120814253) B120814253
theorem B53695223 : Blo 2093435 53695223 := bstep (se 1 (by rfl) ⟨40271417, by rfl⟩ : syracuseStep 53695223 = 80542835) B80542835
theorem B35796815 : Blo 2093435 35796815 := bstep (se 1 (by rfl) ⟨26847611, by rfl⟩ : syracuseStep 35796815 = 53695223) B53695223
theorem B23864543 : Blo 2093435 23864543 := bstep (se 1 (by rfl) ⟨17898407, by rfl⟩ : syracuseStep 23864543 = 35796815) B35796815
theorem B15909695 : Blo 2093435 15909695 := bstep (se 1 (by rfl) ⟨11932271, by rfl⟩ : syracuseStep 15909695 = 23864543) B23864543
theorem B10606463 : Blo 2093435 10606463 := bstep (se 1 (by rfl) ⟨7954847, by rfl⟩ : syracuseStep 10606463 = 15909695) B15909695
theorem B7070975 : Blo 2093435 7070975 := bstep (se 1 (by rfl) ⟨5303231, by rfl⟩ : syracuseStep 7070975 = 10606463) B10606463
theorem B4713983 : Blo 2093435 4713983 := bstep (se 1 (by rfl) ⟨3535487, by rfl⟩ : syracuseStep 4713983 = 7070975) B7070975
theorem B3142655 : Blo 2093435 3142655 := bstep (se 1 (by rfl) ⟨2356991, by rfl⟩ : syracuseStep 3142655 = 4713983) B4713983
theorem B2095103 : Blo 2093435 2095103 := bstep (se 1 (by rfl) ⟨1571327, by rfl⟩ : syracuseStep 2095103 = 3142655) B3142655
theorem B3142661 : Blo 2093435 3142661 := bbase (se 4 (by rfl) ⟨294624, by rfl⟩ : syracuseStep 3142661 = 589249) (by norm_num)
theorem B2095107 : Blo 2093435 2095107 := bstep (se 1 (by rfl) ⟨1571330, by rfl⟩ : syracuseStep 2095107 = 3142661) B3142661
theorem B3535501 : Blo 2093435 3535501 := bbase (se 3 (by rfl) ⟨662906, by rfl⟩ : syracuseStep 3535501 = 1325813) (by norm_num)
theorem B4714001 : Blo 2093435 4714001 := bstep (se 2 (by rfl) ⟨1767750, by rfl⟩ : syracuseStep 4714001 = 3535501) B3535501
theorem B3142667 : Blo 2093435 3142667 := bstep (se 1 (by rfl) ⟨2357000, by rfl⟩ : syracuseStep 3142667 = 4714001) B4714001
theorem B2095111 : Blo 2093435 2095111 := bstep (se 1 (by rfl) ⟨1571333, by rfl⟩ : syracuseStep 2095111 = 3142667) B3142667
theorem B2357005 : Blo 2093435 2357005 := bbase (se 3 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 2357005 = 883877) (by norm_num)
theorem B3142673 : Blo 2093435 3142673 := bstep (se 2 (by rfl) ⟨1178502, by rfl⟩ : syracuseStep 3142673 = 2357005) B2357005
theorem B2095115 : Blo 2093435 2095115 := bstep (se 1 (by rfl) ⟨1571336, by rfl⟩ : syracuseStep 2095115 = 3142673) B3142673
theorem B7071029 : Blo 2093435 7071029 := bbase (se 5 (by rfl) ⟨331454, by rfl⟩ : syracuseStep 7071029 = 662909) (by norm_num)
theorem B4714019 : Blo 2093435 4714019 := bstep (se 1 (by rfl) ⟨3535514, by rfl⟩ : syracuseStep 4714019 = 7071029) B7071029
theorem B3142679 : Blo 2093435 3142679 := bstep (se 1 (by rfl) ⟨2357009, by rfl⟩ : syracuseStep 3142679 = 4714019) B4714019
theorem B2095119 : Blo 2093435 2095119 := bstep (se 1 (by rfl) ⟨1571339, by rfl⟩ : syracuseStep 2095119 = 3142679) B3142679
theorem B3142685 : Blo 2093435 3142685 := bbase (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) (by norm_num)
theorem B2095123 : Blo 2093435 2095123 := bstep (se 1 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 2095123 = 3142685) B3142685
theorem B4714037 : Blo 2093435 4714037 := bbase (se 5 (by rfl) ⟨220970, by rfl⟩ : syracuseStep 4714037 = 441941) (by norm_num)
theorem B3142691 : Blo 2093435 3142691 := bstep (se 1 (by rfl) ⟨2357018, by rfl⟩ : syracuseStep 3142691 = 4714037) B4714037
theorem B2095127 : Blo 2093435 2095127 := bstep (se 1 (by rfl) ⟨1571345, by rfl⟩ : syracuseStep 2095127 = 3142691) B3142691
theorem B3355997 : Blo 2093435 3355997 := bbase (se 3 (by rfl) ⟨629249, by rfl⟩ : syracuseStep 3355997 = 1258499) (by norm_num)
theorem B8949325 : Blo 2093435 8949325 := bstep (se 3 (by rfl) ⟨1677998, by rfl⟩ : syracuseStep 8949325 = 3355997) B3355997
theorem B11932433 : Blo 2093435 11932433 := bstep (se 2 (by rfl) ⟨4474662, by rfl⟩ : syracuseStep 11932433 = 8949325) B8949325
theorem B7954955 : Blo 2093435 7954955 := bstep (se 1 (by rfl) ⟨5966216, by rfl⟩ : syracuseStep 7954955 = 11932433) B11932433
theorem B5303303 : Blo 2093435 5303303 := bstep (se 1 (by rfl) ⟨3977477, by rfl⟩ : syracuseStep 5303303 = 7954955) B7954955
theorem B3535535 : Blo 2093435 3535535 := bstep (se 1 (by rfl) ⟨2651651, by rfl⟩ : syracuseStep 3535535 = 5303303) B5303303
theorem B2357023 : Blo 2093435 2357023 := bstep (se 1 (by rfl) ⟨1767767, by rfl⟩ : syracuseStep 2357023 = 3535535) B3535535
theorem B3142697 : Blo 2093435 3142697 := bstep (se 2 (by rfl) ⟨1178511, by rfl⟩ : syracuseStep 3142697 = 2357023) B2357023
theorem B2095131 : Blo 2093435 2095131 := bstep (se 1 (by rfl) ⟨1571348, by rfl⟩ : syracuseStep 2095131 = 3142697) B3142697
theorem B5034005 : Blo 2093435 5034005 := bbase (se 6 (by rfl) ⟨117984, by rfl⟩ : syracuseStep 5034005 = 235969) (by norm_num)
theorem B3356003 : Blo 2093435 3356003 := bstep (se 1 (by rfl) ⟨2517002, by rfl⟩ : syracuseStep 3356003 = 5034005) B5034005
theorem B8949341 : Blo 2093435 8949341 := bstep (se 3 (by rfl) ⟨1678001, by rfl⟩ : syracuseStep 8949341 = 3356003) B3356003
theorem B5966227 : Blo 2093435 5966227 := bstep (se 1 (by rfl) ⟨4474670, by rfl⟩ : syracuseStep 5966227 = 8949341) B8949341
theorem B7954969 : Blo 2093435 7954969 := bstep (se 2 (by rfl) ⟨2983113, by rfl⟩ : syracuseStep 7954969 = 5966227) B5966227
theorem B10606625 : Blo 2093435 10606625 := bstep (se 2 (by rfl) ⟨3977484, by rfl⟩ : syracuseStep 10606625 = 7954969) B7954969
theorem B7071083 : Blo 2093435 7071083 := bstep (se 1 (by rfl) ⟨5303312, by rfl⟩ : syracuseStep 7071083 = 10606625) B10606625
theorem B4714055 : Blo 2093435 4714055 := bstep (se 1 (by rfl) ⟨3535541, by rfl⟩ : syracuseStep 4714055 = 7071083) B7071083
theorem B3142703 : Blo 2093435 3142703 := bstep (se 1 (by rfl) ⟨2357027, by rfl⟩ : syracuseStep 3142703 = 4714055) B4714055
theorem B2095135 : Blo 2093435 2095135 := bstep (se 1 (by rfl) ⟨1571351, by rfl⟩ : syracuseStep 2095135 = 3142703) B3142703
theorem B3142709 : Blo 2093435 3142709 := bbase (se 5 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 3142709 = 294629) (by norm_num)
theorem B2095139 : Blo 2093435 2095139 := bstep (se 1 (by rfl) ⟨1571354, by rfl⟩ : syracuseStep 2095139 = 3142709) B3142709
theorem B5303333 : Blo 2093435 5303333 := bbase (se 4 (by rfl) ⟨497187, by rfl⟩ : syracuseStep 5303333 = 994375) (by norm_num)
theorem B3535555 : Blo 2093435 3535555 := bstep (se 1 (by rfl) ⟨2651666, by rfl⟩ : syracuseStep 3535555 = 5303333) B5303333
theorem B4714073 : Blo 2093435 4714073 := bstep (se 2 (by rfl) ⟨1767777, by rfl⟩ : syracuseStep 4714073 = 3535555) B3535555
theorem B3142715 : Blo 2093435 3142715 := bstep (se 1 (by rfl) ⟨2357036, by rfl⟩ : syracuseStep 3142715 = 4714073) B4714073
theorem B2095143 : Blo 2093435 2095143 := bstep (se 1 (by rfl) ⟨1571357, by rfl⟩ : syracuseStep 2095143 = 3142715) B3142715
theorem B2357041 : Blo 2093435 2357041 := bbase (se 2 (by rfl) ⟨883890, by rfl⟩ : syracuseStep 2357041 = 1767781) (by norm_num)
theorem B3142721 : Blo 2093435 3142721 := bstep (se 2 (by rfl) ⟨1178520, by rfl⟩ : syracuseStep 3142721 = 2357041) B2357041
theorem B2095147 : Blo 2093435 2095147 := bstep (se 1 (by rfl) ⟨1571360, by rfl⟩ : syracuseStep 2095147 = 3142721) B3142721
theorem B3356029 : Blo 2093435 3356029 := bbase (se 3 (by rfl) ⟨629255, by rfl⟩ : syracuseStep 3356029 = 1258511) (by norm_num)
theorem B4474705 : Blo 2093435 4474705 := bstep (se 2 (by rfl) ⟨1678014, by rfl⟩ : syracuseStep 4474705 = 3356029) B3356029
theorem B5966273 : Blo 2093435 5966273 := bstep (se 2 (by rfl) ⟨2237352, by rfl⟩ : syracuseStep 5966273 = 4474705) B4474705
theorem B3977515 : Blo 2093435 3977515 := bstep (se 1 (by rfl) ⟨2983136, by rfl⟩ : syracuseStep 3977515 = 5966273) B5966273
theorem B5303353 : Blo 2093435 5303353 := bstep (se 2 (by rfl) ⟨1988757, by rfl⟩ : syracuseStep 5303353 = 3977515) B3977515
theorem B7071137 : Blo 2093435 7071137 := bstep (se 2 (by rfl) ⟨2651676, by rfl⟩ : syracuseStep 7071137 = 5303353) B5303353
theorem B4714091 : Blo 2093435 4714091 := bstep (se 1 (by rfl) ⟨3535568, by rfl⟩ : syracuseStep 4714091 = 7071137) B7071137
theorem B3142727 : Blo 2093435 3142727 := bstep (se 1 (by rfl) ⟨2357045, by rfl⟩ : syracuseStep 3142727 = 4714091) B4714091
theorem B2095151 : Blo 2093435 2095151 := bstep (se 1 (by rfl) ⟨1571363, by rfl⟩ : syracuseStep 2095151 = 3142727) B3142727
theorem B3142733 : Blo 2093435 3142733 := bbase (se 3 (by rfl) ⟨589262, by rfl⟩ : syracuseStep 3142733 = 1178525) (by norm_num)
theorem B2095155 : Blo 2093435 2095155 := bstep (se 1 (by rfl) ⟨1571366, by rfl⟩ : syracuseStep 2095155 = 3142733) B3142733
theorem B4714109 : Blo 2093435 4714109 := bbase (se 3 (by rfl) ⟨883895, by rfl⟩ : syracuseStep 4714109 = 1767791) (by norm_num)
theorem B3142739 : Blo 2093435 3142739 := bstep (se 1 (by rfl) ⟨2357054, by rfl⟩ : syracuseStep 3142739 = 4714109) B4714109
theorem B2095159 : Blo 2093435 2095159 := bstep (se 1 (by rfl) ⟨1571369, by rfl⟩ : syracuseStep 2095159 = 3142739) B3142739
theorem B3535589 : Blo 2093435 3535589 := bbase (se 4 (by rfl) ⟨331461, by rfl⟩ : syracuseStep 3535589 = 662923) (by norm_num)
theorem B2357059 : Blo 2093435 2357059 := bstep (se 1 (by rfl) ⟨1767794, by rfl⟩ : syracuseStep 2357059 = 3535589) B3535589
theorem B3142745 : Blo 2093435 3142745 := bstep (se 2 (by rfl) ⟨1178529, by rfl⟩ : syracuseStep 3142745 = 2357059) B2357059
theorem B2095163 : Blo 2093435 2095163 := bstep (se 1 (by rfl) ⟨1571372, by rfl⟩ : syracuseStep 2095163 = 3142745) B3142745
theorem B2517041 : Blo 2093435 2517041 := bbase (se 2 (by rfl) ⟨943890, by rfl⟩ : syracuseStep 2517041 = 1887781) (by norm_num)
theorem B6712109 : Blo 2093435 6712109 := bstep (se 3 (by rfl) ⟨1258520, by rfl⟩ : syracuseStep 6712109 = 2517041) B2517041
theorem B4474739 : Blo 2093435 4474739 := bstep (se 1 (by rfl) ⟨3356054, by rfl⟩ : syracuseStep 4474739 = 6712109) B6712109
theorem B2983159 : Blo 2093435 2983159 := bstep (se 1 (by rfl) ⟨2237369, by rfl⟩ : syracuseStep 2983159 = 4474739) B4474739
theorem B15910181 : Blo 2093435 15910181 := bstep (se 4 (by rfl) ⟨1491579, by rfl⟩ : syracuseStep 15910181 = 2983159) B2983159
theorem B10606787 : Blo 2093435 10606787 := bstep (se 1 (by rfl) ⟨7955090, by rfl⟩ : syracuseStep 10606787 = 15910181) B15910181
theorem B7071191 : Blo 2093435 7071191 := bstep (se 1 (by rfl) ⟨5303393, by rfl⟩ : syracuseStep 7071191 = 10606787) B10606787
theorem B4714127 : Blo 2093435 4714127 := bstep (se 1 (by rfl) ⟨3535595, by rfl⟩ : syracuseStep 4714127 = 7071191) B7071191
theorem B3142751 : Blo 2093435 3142751 := bstep (se 1 (by rfl) ⟨2357063, by rfl⟩ : syracuseStep 3142751 = 4714127) B4714127
theorem B2095167 : Blo 2093435 2095167 := bstep (se 1 (by rfl) ⟨1571375, by rfl⟩ : syracuseStep 2095167 = 3142751) B3142751
theorem B3142757 : Blo 2093435 3142757 := bbase (se 4 (by rfl) ⟨294633, by rfl⟩ : syracuseStep 3142757 = 589267) (by norm_num)
theorem B2095171 : Blo 2093435 2095171 := bstep (se 1 (by rfl) ⟨1571378, by rfl⟩ : syracuseStep 2095171 = 3142757) B3142757
theorem B4474757 : Blo 2093435 4474757 := bbase (se 4 (by rfl) ⟨419508, by rfl⟩ : syracuseStep 4474757 = 839017) (by norm_num)
theorem B2983171 : Blo 2093435 2983171 := bstep (se 1 (by rfl) ⟨2237378, by rfl⟩ : syracuseStep 2983171 = 4474757) B4474757
theorem B3977561 : Blo 2093435 3977561 := bstep (se 2 (by rfl) ⟨1491585, by rfl⟩ : syracuseStep 3977561 = 2983171) B2983171
theorem B2651707 : Blo 2093435 2651707 := bstep (se 1 (by rfl) ⟨1988780, by rfl⟩ : syracuseStep 2651707 = 3977561) B3977561
theorem B3535609 : Blo 2093435 3535609 := bstep (se 2 (by rfl) ⟨1325853, by rfl⟩ : syracuseStep 3535609 = 2651707) B2651707
theorem B4714145 : Blo 2093435 4714145 := bstep (se 2 (by rfl) ⟨1767804, by rfl⟩ : syracuseStep 4714145 = 3535609) B3535609
theorem B3142763 : Blo 2093435 3142763 := bstep (se 1 (by rfl) ⟨2357072, by rfl⟩ : syracuseStep 3142763 = 4714145) B4714145
theorem B2095175 : Blo 2093435 2095175 := bstep (se 1 (by rfl) ⟨1571381, by rfl⟩ : syracuseStep 2095175 = 3142763) B3142763
theorem B2357077 : Blo 2093435 2357077 := bbase (se 9 (by rfl) ⟨6905, by rfl⟩ : syracuseStep 2357077 = 13811) (by norm_num)
theorem B3142769 : Blo 2093435 3142769 := bstep (se 2 (by rfl) ⟨1178538, by rfl⟩ : syracuseStep 3142769 = 2357077) B2357077
theorem B2095179 : Blo 2093435 2095179 := bstep (se 1 (by rfl) ⟨1571384, by rfl⟩ : syracuseStep 2095179 = 3142769) B3142769
theorem B2651717 : Blo 2093435 2651717 := bbase (se 4 (by rfl) ⟨248598, by rfl⟩ : syracuseStep 2651717 = 497197) (by norm_num)
theorem B7071245 : Blo 2093435 7071245 := bstep (se 3 (by rfl) ⟨1325858, by rfl⟩ : syracuseStep 7071245 = 2651717) B2651717
theorem B4714163 : Blo 2093435 4714163 := bstep (se 1 (by rfl) ⟨3535622, by rfl⟩ : syracuseStep 4714163 = 7071245) B7071245
theorem B3142775 : Blo 2093435 3142775 := bstep (se 1 (by rfl) ⟨2357081, by rfl⟩ : syracuseStep 3142775 = 4714163) B4714163
theorem B2095183 : Blo 2093435 2095183 := bstep (se 1 (by rfl) ⟨1571387, by rfl⟩ : syracuseStep 2095183 = 3142775) B3142775
theorem B3142781 : Blo 2093435 3142781 := bbase (se 3 (by rfl) ⟨589271, by rfl⟩ : syracuseStep 3142781 = 1178543) (by norm_num)
theorem B2095187 : Blo 2093435 2095187 := bstep (se 1 (by rfl) ⟨1571390, by rfl⟩ : syracuseStep 2095187 = 3142781) B3142781
theorem B4714181 : Blo 2093435 4714181 := bbase (se 4 (by rfl) ⟨441954, by rfl⟩ : syracuseStep 4714181 = 883909) (by norm_num)
theorem B3142787 : Blo 2093435 3142787 := bstep (se 1 (by rfl) ⟨2357090, by rfl⟩ : syracuseStep 3142787 = 4714181) B4714181
theorem B2095191 : Blo 2093435 2095191 := bstep (se 1 (by rfl) ⟨1571393, by rfl⟩ : syracuseStep 2095191 = 3142787) B3142787
theorem B45307349 : Blo 2093435 45307349 := bbase (se 7 (by rfl) ⟨530945, by rfl⟩ : syracuseStep 45307349 = 1061891) (by norm_num)
theorem B30204899 : Blo 2093435 30204899 := bstep (se 1 (by rfl) ⟨22653674, by rfl⟩ : syracuseStep 30204899 = 45307349) B45307349
theorem B20136599 : Blo 2093435 20136599 := bstep (se 1 (by rfl) ⟨15102449, by rfl⟩ : syracuseStep 20136599 = 30204899) B30204899
theorem B13424399 : Blo 2093435 13424399 := bstep (se 1 (by rfl) ⟨10068299, by rfl⟩ : syracuseStep 13424399 = 20136599) B20136599
theorem B8949599 : Blo 2093435 8949599 := bstep (se 1 (by rfl) ⟨6712199, by rfl⟩ : syracuseStep 8949599 = 13424399) B13424399
theorem B5966399 : Blo 2093435 5966399 := bstep (se 1 (by rfl) ⟨4474799, by rfl⟩ : syracuseStep 5966399 = 8949599) B8949599
theorem B3977599 : Blo 2093435 3977599 := bstep (se 1 (by rfl) ⟨2983199, by rfl⟩ : syracuseStep 3977599 = 5966399) B5966399
theorem B5303465 : Blo 2093435 5303465 := bstep (se 2 (by rfl) ⟨1988799, by rfl⟩ : syracuseStep 5303465 = 3977599) B3977599
theorem B3535643 : Blo 2093435 3535643 := bstep (se 1 (by rfl) ⟨2651732, by rfl⟩ : syracuseStep 3535643 = 5303465) B5303465
theorem B2357095 : Blo 2093435 2357095 := bstep (se 1 (by rfl) ⟨1767821, by rfl⟩ : syracuseStep 2357095 = 3535643) B3535643
theorem B3142793 : Blo 2093435 3142793 := bstep (se 2 (by rfl) ⟨1178547, by rfl⟩ : syracuseStep 3142793 = 2357095) B2357095
theorem B2095195 : Blo 2093435 2095195 := bstep (se 1 (by rfl) ⟨1571396, by rfl⟩ : syracuseStep 2095195 = 3142793) B3142793
theorem B10606949 : Blo 2093435 10606949 := bbase (se 4 (by rfl) ⟨994401, by rfl⟩ : syracuseStep 10606949 = 1988803) (by norm_num)
theorem B7071299 : Blo 2093435 7071299 := bstep (se 1 (by rfl) ⟨5303474, by rfl⟩ : syracuseStep 7071299 = 10606949) B10606949
theorem B4714199 : Blo 2093435 4714199 := bstep (se 1 (by rfl) ⟨3535649, by rfl⟩ : syracuseStep 4714199 = 7071299) B7071299
theorem B3142799 : Blo 2093435 3142799 := bstep (se 1 (by rfl) ⟨2357099, by rfl⟩ : syracuseStep 3142799 = 4714199) B4714199
theorem B2095199 : Blo 2093435 2095199 := bstep (se 1 (by rfl) ⟨1571399, by rfl⟩ : syracuseStep 2095199 = 3142799) B3142799
theorem B3142805 : Blo 2093435 3142805 := bbase (se 6 (by rfl) ⟨73659, by rfl⟩ : syracuseStep 3142805 = 147319) (by norm_num)
theorem B2095203 : Blo 2093435 2095203 := bstep (se 1 (by rfl) ⟨1571402, by rfl⟩ : syracuseStep 2095203 = 3142805) B3142805
theorem B2517089 : Blo 2093435 2517089 := bbase (se 2 (by rfl) ⟨943908, by rfl⟩ : syracuseStep 2517089 = 1887817) (by norm_num)
theorem B6712237 : Blo 2093435 6712237 := bstep (se 3 (by rfl) ⟨1258544, by rfl⟩ : syracuseStep 6712237 = 2517089) B2517089
theorem B8949649 : Blo 2093435 8949649 := bstep (se 2 (by rfl) ⟨3356118, by rfl⟩ : syracuseStep 8949649 = 6712237) B6712237
theorem B11932865 : Blo 2093435 11932865 := bstep (se 2 (by rfl) ⟨4474824, by rfl⟩ : syracuseStep 11932865 = 8949649) B8949649
theorem B7955243 : Blo 2093435 7955243 := bstep (se 1 (by rfl) ⟨5966432, by rfl⟩ : syracuseStep 7955243 = 11932865) B11932865
theorem B5303495 : Blo 2093435 5303495 := bstep (se 1 (by rfl) ⟨3977621, by rfl⟩ : syracuseStep 5303495 = 7955243) B7955243
theorem B3535663 : Blo 2093435 3535663 := bstep (se 1 (by rfl) ⟨2651747, by rfl⟩ : syracuseStep 3535663 = 5303495) B5303495
theorem B4714217 : Blo 2093435 4714217 := bstep (se 2 (by rfl) ⟨1767831, by rfl⟩ : syracuseStep 4714217 = 3535663) B3535663
theorem B3142811 : Blo 2093435 3142811 := bstep (se 1 (by rfl) ⟨2357108, by rfl⟩ : syracuseStep 3142811 = 4714217) B4714217
theorem B2095207 : Blo 2093435 2095207 := bstep (se 1 (by rfl) ⟨1571405, by rfl⟩ : syracuseStep 2095207 = 3142811) B3142811
theorem B2357113 : Blo 2093435 2357113 := bbase (se 2 (by rfl) ⟨883917, by rfl⟩ : syracuseStep 2357113 = 1767835) (by norm_num)
theorem B3142817 : Blo 2093435 3142817 := bstep (se 2 (by rfl) ⟨1178556, by rfl⟩ : syracuseStep 3142817 = 2357113) B2357113
theorem B2095211 : Blo 2093435 2095211 := bstep (se 1 (by rfl) ⟨1571408, by rfl⟩ : syracuseStep 2095211 = 3142817) B3142817
theorem B5034197 : Blo 2093435 5034197 := bbase (se 7 (by rfl) ⟨58994, by rfl⟩ : syracuseStep 5034197 = 117989) (by norm_num)
theorem B13424525 : Blo 2093435 13424525 := bstep (se 3 (by rfl) ⟨2517098, by rfl⟩ : syracuseStep 13424525 = 5034197) B5034197
theorem B8949683 : Blo 2093435 8949683 := bstep (se 1 (by rfl) ⟨6712262, by rfl⟩ : syracuseStep 8949683 = 13424525) B13424525
theorem B5966455 : Blo 2093435 5966455 := bstep (se 1 (by rfl) ⟨4474841, by rfl⟩ : syracuseStep 5966455 = 8949683) B8949683
theorem B7955273 : Blo 2093435 7955273 := bstep (se 2 (by rfl) ⟨2983227, by rfl⟩ : syracuseStep 7955273 = 5966455) B5966455
theorem B5303515 : Blo 2093435 5303515 := bstep (se 1 (by rfl) ⟨3977636, by rfl⟩ : syracuseStep 5303515 = 7955273) B7955273
theorem B7071353 : Blo 2093435 7071353 := bstep (se 2 (by rfl) ⟨2651757, by rfl⟩ : syracuseStep 7071353 = 5303515) B5303515
theorem B4714235 : Blo 2093435 4714235 := bstep (se 1 (by rfl) ⟨3535676, by rfl⟩ : syracuseStep 4714235 = 7071353) B7071353
theorem B3142823 : Blo 2093435 3142823 := bstep (se 1 (by rfl) ⟨2357117, by rfl⟩ : syracuseStep 3142823 = 4714235) B4714235
theorem B2095215 : Blo 2093435 2095215 := bstep (se 1 (by rfl) ⟨1571411, by rfl⟩ : syracuseStep 2095215 = 3142823) B3142823
theorem B3142829 : Blo 2093435 3142829 := bbase (se 3 (by rfl) ⟨589280, by rfl⟩ : syracuseStep 3142829 = 1178561) (by norm_num)
theorem B2095219 : Blo 2093435 2095219 := bstep (se 1 (by rfl) ⟨1571414, by rfl⟩ : syracuseStep 2095219 = 3142829) B3142829
theorem B4714253 : Blo 2093435 4714253 := bbase (se 3 (by rfl) ⟨883922, by rfl⟩ : syracuseStep 4714253 = 1767845) (by norm_num)
theorem B3142835 : Blo 2093435 3142835 := bstep (se 1 (by rfl) ⟨2357126, by rfl⟩ : syracuseStep 3142835 = 4714253) B4714253
theorem B2095223 : Blo 2093435 2095223 := bstep (se 1 (by rfl) ⟨1571417, by rfl⟩ : syracuseStep 2095223 = 3142835) B3142835
theorem B2651773 : Blo 2093435 2651773 := bbase (se 3 (by rfl) ⟨497207, by rfl⟩ : syracuseStep 2651773 = 994415) (by norm_num)
theorem B3535697 : Blo 2093435 3535697 := bstep (se 2 (by rfl) ⟨1325886, by rfl⟩ : syracuseStep 3535697 = 2651773) B2651773
theorem B2357131 : Blo 2093435 2357131 := bstep (se 1 (by rfl) ⟨1767848, by rfl⟩ : syracuseStep 2357131 = 3535697) B3535697
theorem B3142841 : Blo 2093435 3142841 := bstep (se 2 (by rfl) ⟨1178565, by rfl⟩ : syracuseStep 3142841 = 2357131) B2357131
theorem B2095227 : Blo 2093435 2095227 := bstep (se 1 (by rfl) ⟨1571420, by rfl⟩ : syracuseStep 2095227 = 3142841) B3142841
theorem B17222357 : Blo 2093435 17222357 := bbase (se 7 (by rfl) ⟨201824, by rfl⟩ : syracuseStep 17222357 = 403649) (by norm_num)
theorem B11481571 : Blo 2093435 11481571 := bstep (se 1 (by rfl) ⟨8611178, by rfl⟩ : syracuseStep 11481571 = 17222357) B17222357
theorem B15308761 : Blo 2093435 15308761 := bstep (se 2 (by rfl) ⟨5740785, by rfl⟩ : syracuseStep 15308761 = 11481571) B11481571
theorem B20411681 : Blo 2093435 20411681 := bstep (se 2 (by rfl) ⟨7654380, by rfl⟩ : syracuseStep 20411681 = 15308761) B15308761
theorem B54431149 : Blo 2093435 54431149 := bstep (se 3 (by rfl) ⟨10205840, by rfl⟩ : syracuseStep 54431149 = 20411681) B20411681
theorem B72574865 : Blo 2093435 72574865 := bstep (se 2 (by rfl) ⟨27215574, by rfl⟩ : syracuseStep 72574865 = 54431149) B54431149
theorem B48383243 : Blo 2093435 48383243 := bstep (se 1 (by rfl) ⟨36287432, by rfl⟩ : syracuseStep 48383243 = 72574865) B72574865
theorem B32255495 : Blo 2093435 32255495 := bstep (se 1 (by rfl) ⟨24191621, by rfl⟩ : syracuseStep 32255495 = 48383243) B48383243
theorem B21503663 : Blo 2093435 21503663 := bstep (se 1 (by rfl) ⟨16127747, by rfl⟩ : syracuseStep 21503663 = 32255495) B32255495
theorem B14335775 : Blo 2093435 14335775 := bstep (se 1 (by rfl) ⟨10751831, by rfl⟩ : syracuseStep 14335775 = 21503663) B21503663
theorem B9557183 : Blo 2093435 9557183 := bstep (se 1 (by rfl) ⟨7167887, by rfl⟩ : syracuseStep 9557183 = 14335775) B14335775
theorem B6371455 : Blo 2093435 6371455 := bstep (se 1 (by rfl) ⟨4778591, by rfl⟩ : syracuseStep 6371455 = 9557183) B9557183
theorem B8495273 : Blo 2093435 8495273 := bstep (se 2 (by rfl) ⟨3185727, by rfl⟩ : syracuseStep 8495273 = 6371455) B6371455
theorem B5663515 : Blo 2093435 5663515 := bstep (se 1 (by rfl) ⟨4247636, by rfl⟩ : syracuseStep 5663515 = 8495273) B8495273
theorem B7551353 : Blo 2093435 7551353 := bstep (se 2 (by rfl) ⟨2831757, by rfl⟩ : syracuseStep 7551353 = 5663515) B5663515
theorem B5034235 : Blo 2093435 5034235 := bstep (se 1 (by rfl) ⟨3775676, by rfl⟩ : syracuseStep 5034235 = 7551353) B7551353
theorem B6712313 : Blo 2093435 6712313 := bstep (se 2 (by rfl) ⟨2517117, by rfl⟩ : syracuseStep 6712313 = 5034235) B5034235
theorem B17899501 : Blo 2093435 17899501 := bstep (se 3 (by rfl) ⟨3356156, by rfl⟩ : syracuseStep 17899501 = 6712313) B6712313
theorem B23866001 : Blo 2093435 23866001 := bstep (se 2 (by rfl) ⟨8949750, by rfl⟩ : syracuseStep 23866001 = 17899501) B17899501
theorem B15910667 : Blo 2093435 15910667 := bstep (se 1 (by rfl) ⟨11933000, by rfl⟩ : syracuseStep 15910667 = 23866001) B23866001
theorem B10607111 : Blo 2093435 10607111 := bstep (se 1 (by rfl) ⟨7955333, by rfl⟩ : syracuseStep 10607111 = 15910667) B15910667
theorem B7071407 : Blo 2093435 7071407 := bstep (se 1 (by rfl) ⟨5303555, by rfl⟩ : syracuseStep 7071407 = 10607111) B10607111
theorem B4714271 : Blo 2093435 4714271 := bstep (se 1 (by rfl) ⟨3535703, by rfl⟩ : syracuseStep 4714271 = 7071407) B7071407
theorem B3142847 : Blo 2093435 3142847 := bstep (se 1 (by rfl) ⟨2357135, by rfl⟩ : syracuseStep 3142847 = 4714271) B4714271
theorem B2095231 : Blo 2093435 2095231 := bstep (se 1 (by rfl) ⟨1571423, by rfl⟩ : syracuseStep 2095231 = 3142847) B3142847
theorem B3142853 : Blo 2093435 3142853 := bbase (se 4 (by rfl) ⟨294642, by rfl⟩ : syracuseStep 3142853 = 589285) (by norm_num)
theorem B2095235 : Blo 2093435 2095235 := bstep (se 1 (by rfl) ⟨1571426, by rfl⟩ : syracuseStep 2095235 = 3142853) B3142853
theorem B3535717 : Blo 2093435 3535717 := bbase (se 4 (by rfl) ⟨331473, by rfl⟩ : syracuseStep 3535717 = 662947) (by norm_num)
theorem B4714289 : Blo 2093435 4714289 := bstep (se 2 (by rfl) ⟨1767858, by rfl⟩ : syracuseStep 4714289 = 3535717) B3535717
theorem B3142859 : Blo 2093435 3142859 := bstep (se 1 (by rfl) ⟨2357144, by rfl⟩ : syracuseStep 3142859 = 4714289) B4714289
theorem B2095239 : Blo 2093435 2095239 := bstep (se 1 (by rfl) ⟨1571429, by rfl⟩ : syracuseStep 2095239 = 3142859) B3142859
theorem B2357149 : Blo 2093435 2357149 := bbase (se 3 (by rfl) ⟨441965, by rfl⟩ : syracuseStep 2357149 = 883931) (by norm_num)
theorem B3142865 : Blo 2093435 3142865 := bstep (se 2 (by rfl) ⟨1178574, by rfl⟩ : syracuseStep 3142865 = 2357149) B2357149
theorem B2095243 : Blo 2093435 2095243 := bstep (se 1 (by rfl) ⟨1571432, by rfl⟩ : syracuseStep 2095243 = 3142865) B3142865
theorem B7071461 : Blo 2093435 7071461 := bbase (se 4 (by rfl) ⟨662949, by rfl⟩ : syracuseStep 7071461 = 1325899) (by norm_num)
theorem B4714307 : Blo 2093435 4714307 := bstep (se 1 (by rfl) ⟨3535730, by rfl⟩ : syracuseStep 4714307 = 7071461) B7071461
theorem B3142871 : Blo 2093435 3142871 := bstep (se 1 (by rfl) ⟨2357153, by rfl⟩ : syracuseStep 3142871 = 4714307) B4714307
theorem B2095247 : Blo 2093435 2095247 := bstep (se 1 (by rfl) ⟨1571435, by rfl⟩ : syracuseStep 2095247 = 3142871) B3142871
theorem B3142877 : Blo 2093435 3142877 := bbase (se 3 (by rfl) ⟨589289, by rfl⟩ : syracuseStep 3142877 = 1178579) (by norm_num)
theorem B2095251 : Blo 2093435 2095251 := bstep (se 1 (by rfl) ⟨1571438, by rfl⟩ : syracuseStep 2095251 = 3142877) B3142877
theorem B4714325 : Blo 2093435 4714325 := bbase (se 9 (by rfl) ⟨13811, by rfl⟩ : syracuseStep 4714325 = 27623) (by norm_num)
theorem B3142883 : Blo 2093435 3142883 := bstep (se 1 (by rfl) ⟨2357162, by rfl⟩ : syracuseStep 3142883 = 4714325) B4714325
theorem B2095255 : Blo 2093435 2095255 := bstep (se 1 (by rfl) ⟨1571441, by rfl⟩ : syracuseStep 2095255 = 3142883) B3142883
theorem B5966581 : Blo 2093435 5966581 := bbase (se 5 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 5966581 = 559367) (by norm_num)
theorem B7955441 : Blo 2093435 7955441 := bstep (se 2 (by rfl) ⟨2983290, by rfl⟩ : syracuseStep 7955441 = 5966581) B5966581
theorem B5303627 : Blo 2093435 5303627 := bstep (se 1 (by rfl) ⟨3977720, by rfl⟩ : syracuseStep 5303627 = 7955441) B7955441
theorem B3535751 : Blo 2093435 3535751 := bstep (se 1 (by rfl) ⟨2651813, by rfl⟩ : syracuseStep 3535751 = 5303627) B5303627
theorem B2357167 : Blo 2093435 2357167 := bstep (se 1 (by rfl) ⟨1767875, by rfl⟩ : syracuseStep 2357167 = 3535751) B3535751
theorem B3142889 : Blo 2093435 3142889 := bstep (se 2 (by rfl) ⟨1178583, by rfl⟩ : syracuseStep 3142889 = 2357167) B2357167
theorem B2095259 : Blo 2093435 2095259 := bstep (se 1 (by rfl) ⟨1571444, by rfl⟩ : syracuseStep 2095259 = 3142889) B3142889
theorem B2724673 : Blo 2093435 2724673 := bbase (se 2 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 2724673 = 2043505) (by norm_num)
theorem B3632897 : Blo 2093435 3632897 := bstep (se 2 (by rfl) ⟨1362336, by rfl⟩ : syracuseStep 3632897 = 2724673) B2724673
theorem B2421931 : Blo 2093435 2421931 := bstep (se 1 (by rfl) ⟨1816448, by rfl⟩ : syracuseStep 2421931 = 3632897) B3632897
theorem B3229241 : Blo 2093435 3229241 := bstep (se 2 (by rfl) ⟨1210965, by rfl⟩ : syracuseStep 3229241 = 2421931) B2421931
theorem B8611309 : Blo 2093435 8611309 := bstep (se 3 (by rfl) ⟨1614620, by rfl⟩ : syracuseStep 8611309 = 3229241) B3229241
theorem B11481745 : Blo 2093435 11481745 := bstep (se 2 (by rfl) ⟨4305654, by rfl⟩ : syracuseStep 11481745 = 8611309) B8611309
theorem B15308993 : Blo 2093435 15308993 := bstep (se 2 (by rfl) ⟨5740872, by rfl⟩ : syracuseStep 15308993 = 11481745) B11481745
theorem B10205995 : Blo 2093435 10205995 := bstep (se 1 (by rfl) ⟨7654496, by rfl⟩ : syracuseStep 10205995 = 15308993) B15308993
theorem B13607993 : Blo 2093435 13607993 := bstep (se 2 (by rfl) ⟨5102997, by rfl⟩ : syracuseStep 13607993 = 10205995) B10205995
theorem B9071995 : Blo 2093435 9071995 := bstep (se 1 (by rfl) ⟨6803996, by rfl⟩ : syracuseStep 9071995 = 13607993) B13607993
theorem B12095993 : Blo 2093435 12095993 := bstep (se 2 (by rfl) ⟨4535997, by rfl⟩ : syracuseStep 12095993 = 9071995) B9071995
theorem B8063995 : Blo 2093435 8063995 := bstep (se 1 (by rfl) ⟨6047996, by rfl⟩ : syracuseStep 8063995 = 12095993) B12095993
theorem B10751993 : Blo 2093435 10751993 := bstep (se 2 (by rfl) ⟨4031997, by rfl⟩ : syracuseStep 10751993 = 8063995) B8063995
theorem B7167995 : Blo 2093435 7167995 := bstep (se 1 (by rfl) ⟨5375996, by rfl⟩ : syracuseStep 7167995 = 10751993) B10751993
theorem B305834453 : Blo 2093435 305834453 := bstep (se 7 (by rfl) ⟨3583997, by rfl⟩ : syracuseStep 305834453 = 7167995) B7167995
theorem B203889635 : Blo 2093435 203889635 := bstep (se 1 (by rfl) ⟨152917226, by rfl⟩ : syracuseStep 203889635 = 305834453) B305834453
theorem B135926423 : Blo 2093435 135926423 := bstep (se 1 (by rfl) ⟨101944817, by rfl⟩ : syracuseStep 135926423 = 203889635) B203889635
theorem B90617615 : Blo 2093435 90617615 := bstep (se 1 (by rfl) ⟨67963211, by rfl⟩ : syracuseStep 90617615 = 135926423) B135926423
theorem B60411743 : Blo 2093435 60411743 := bstep (se 1 (by rfl) ⟨45308807, by rfl⟩ : syracuseStep 60411743 = 90617615) B90617615
theorem B40274495 : Blo 2093435 40274495 := bstep (se 1 (by rfl) ⟨30205871, by rfl⟩ : syracuseStep 40274495 = 60411743) B60411743
theorem B26849663 : Blo 2093435 26849663 := bstep (se 1 (by rfl) ⟨20137247, by rfl⟩ : syracuseStep 26849663 = 40274495) B40274495
theorem B17899775 : Blo 2093435 17899775 := bstep (se 1 (by rfl) ⟨13424831, by rfl⟩ : syracuseStep 17899775 = 26849663) B26849663
theorem B11933183 : Blo 2093435 11933183 := bstep (se 1 (by rfl) ⟨8949887, by rfl⟩ : syracuseStep 11933183 = 17899775) B17899775
theorem B7955455 : Blo 2093435 7955455 := bstep (se 1 (by rfl) ⟨5966591, by rfl⟩ : syracuseStep 7955455 = 11933183) B11933183
theorem B10607273 : Blo 2093435 10607273 := bstep (se 2 (by rfl) ⟨3977727, by rfl⟩ : syracuseStep 10607273 = 7955455) B7955455
theorem B7071515 : Blo 2093435 7071515 := bstep (se 1 (by rfl) ⟨5303636, by rfl⟩ : syracuseStep 7071515 = 10607273) B10607273
theorem B4714343 : Blo 2093435 4714343 := bstep (se 1 (by rfl) ⟨3535757, by rfl⟩ : syracuseStep 4714343 = 7071515) B7071515
theorem B3142895 : Blo 2093435 3142895 := bstep (se 1 (by rfl) ⟨2357171, by rfl⟩ : syracuseStep 3142895 = 4714343) B4714343
theorem B2095263 : Blo 2093435 2095263 := bstep (se 1 (by rfl) ⟨1571447, by rfl⟩ : syracuseStep 2095263 = 3142895) B3142895
theorem B3142901 : Blo 2093435 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B2095267 : Blo 2093435 2095267 := bstep (se 1 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 2095267 = 3142901) B3142901
theorem B13424885 : Blo 2093435 13424885 := bbase (se 5 (by rfl) ⟨629291, by rfl⟩ : syracuseStep 13424885 = 1258583) (by norm_num)
theorem B8949923 : Blo 2093435 8949923 := bstep (se 1 (by rfl) ⟨6712442, by rfl⟩ : syracuseStep 8949923 = 13424885) B13424885
theorem B5966615 : Blo 2093435 5966615 := bstep (se 1 (by rfl) ⟨4474961, by rfl⟩ : syracuseStep 5966615 = 8949923) B8949923
theorem B3977743 : Blo 2093435 3977743 := bstep (se 1 (by rfl) ⟨2983307, by rfl⟩ : syracuseStep 3977743 = 5966615) B5966615
theorem B5303657 : Blo 2093435 5303657 := bstep (se 2 (by rfl) ⟨1988871, by rfl⟩ : syracuseStep 5303657 = 3977743) B3977743
theorem B3535771 : Blo 2093435 3535771 := bstep (se 1 (by rfl) ⟨2651828, by rfl⟩ : syracuseStep 3535771 = 5303657) B5303657
theorem B4714361 : Blo 2093435 4714361 := bstep (se 2 (by rfl) ⟨1767885, by rfl⟩ : syracuseStep 4714361 = 3535771) B3535771
theorem B3142907 : Blo 2093435 3142907 := bstep (se 1 (by rfl) ⟨2357180, by rfl⟩ : syracuseStep 3142907 = 4714361) B4714361
theorem B2095271 : Blo 2093435 2095271 := bstep (se 1 (by rfl) ⟨1571453, by rfl⟩ : syracuseStep 2095271 = 3142907) B3142907
theorem B2357185 : Blo 2093435 2357185 := bbase (se 2 (by rfl) ⟨883944, by rfl⟩ : syracuseStep 2357185 = 1767889) (by norm_num)
theorem B3142913 : Blo 2093435 3142913 := bstep (se 2 (by rfl) ⟨1178592, by rfl⟩ : syracuseStep 3142913 = 2357185) B2357185
theorem B2095275 : Blo 2093435 2095275 := bstep (se 1 (by rfl) ⟨1571456, by rfl⟩ : syracuseStep 2095275 = 3142913) B3142913
theorem B5303677 : Blo 2093435 5303677 := bbase (se 3 (by rfl) ⟨994439, by rfl⟩ : syracuseStep 5303677 = 1988879) (by norm_num)
theorem B7071569 : Blo 2093435 7071569 := bstep (se 2 (by rfl) ⟨2651838, by rfl⟩ : syracuseStep 7071569 = 5303677) B5303677
theorem B4714379 : Blo 2093435 4714379 := bstep (se 1 (by rfl) ⟨3535784, by rfl⟩ : syracuseStep 4714379 = 7071569) B7071569
theorem B3142919 : Blo 2093435 3142919 := bstep (se 1 (by rfl) ⟨2357189, by rfl⟩ : syracuseStep 3142919 = 4714379) B4714379
theorem B2095279 : Blo 2093435 2095279 := bstep (se 1 (by rfl) ⟨1571459, by rfl⟩ : syracuseStep 2095279 = 3142919) B3142919
theorem B3142925 : Blo 2093435 3142925 := bbase (se 3 (by rfl) ⟨589298, by rfl⟩ : syracuseStep 3142925 = 1178597) (by norm_num)
theorem B2095283 : Blo 2093435 2095283 := bstep (se 1 (by rfl) ⟨1571462, by rfl⟩ : syracuseStep 2095283 = 3142925) B3142925
theorem B4714397 : Blo 2093435 4714397 := bbase (se 3 (by rfl) ⟨883949, by rfl⟩ : syracuseStep 4714397 = 1767899) (by norm_num)
theorem B3142931 : Blo 2093435 3142931 := bstep (se 1 (by rfl) ⟨2357198, by rfl⟩ : syracuseStep 3142931 = 4714397) B4714397
theorem B2095287 : Blo 2093435 2095287 := bstep (se 1 (by rfl) ⟨1571465, by rfl⟩ : syracuseStep 2095287 = 3142931) B3142931
theorem B3535805 : Blo 2093435 3535805 := bbase (se 3 (by rfl) ⟨662963, by rfl⟩ : syracuseStep 3535805 = 1325927) (by norm_num)
theorem B2357203 : Blo 2093435 2357203 := bstep (se 1 (by rfl) ⟨1767902, by rfl⟩ : syracuseStep 2357203 = 3535805) B3535805
theorem B3142937 : Blo 2093435 3142937 := bstep (se 2 (by rfl) ⟨1178601, by rfl⟩ : syracuseStep 3142937 = 2357203) B2357203
theorem B2095291 : Blo 2093435 2095291 := bstep (se 1 (by rfl) ⟨1571468, by rfl⟩ : syracuseStep 2095291 = 3142937) B3142937
theorem B11933365 : Blo 2093435 11933365 := bbase (se 5 (by rfl) ⟨559376, by rfl⟩ : syracuseStep 11933365 = 1118753) (by norm_num)
theorem B15911153 : Blo 2093435 15911153 := bstep (se 2 (by rfl) ⟨5966682, by rfl⟩ : syracuseStep 15911153 = 11933365) B11933365
theorem B10607435 : Blo 2093435 10607435 := bstep (se 1 (by rfl) ⟨7955576, by rfl⟩ : syracuseStep 10607435 = 15911153) B15911153
theorem B7071623 : Blo 2093435 7071623 := bstep (se 1 (by rfl) ⟨5303717, by rfl⟩ : syracuseStep 7071623 = 10607435) B10607435
theorem B4714415 : Blo 2093435 4714415 := bstep (se 1 (by rfl) ⟨3535811, by rfl⟩ : syracuseStep 4714415 = 7071623) B7071623
theorem B3142943 : Blo 2093435 3142943 := bstep (se 1 (by rfl) ⟨2357207, by rfl⟩ : syracuseStep 3142943 = 4714415) B4714415
theorem B2095295 : Blo 2093435 2095295 := bstep (se 1 (by rfl) ⟨1571471, by rfl⟩ : syracuseStep 2095295 = 3142943) B3142943
theorem B3142949 : Blo 2093435 3142949 := bbase (se 4 (by rfl) ⟨294651, by rfl⟩ : syracuseStep 3142949 = 589303) (by norm_num)
theorem B2095299 : Blo 2093435 2095299 := bstep (se 1 (by rfl) ⟨1571474, by rfl⟩ : syracuseStep 2095299 = 3142949) B3142949
theorem B2651869 : Blo 2093435 2651869 := bbase (se 3 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 2651869 = 994451) (by norm_num)
theorem B3535825 : Blo 2093435 3535825 := bstep (se 2 (by rfl) ⟨1325934, by rfl⟩ : syracuseStep 3535825 = 2651869) B2651869
theorem B4714433 : Blo 2093435 4714433 := bstep (se 2 (by rfl) ⟨1767912, by rfl⟩ : syracuseStep 4714433 = 3535825) B3535825
theorem B3142955 : Blo 2093435 3142955 := bstep (se 1 (by rfl) ⟨2357216, by rfl⟩ : syracuseStep 3142955 = 4714433) B4714433
theorem B2095303 : Blo 2093435 2095303 := bstep (se 1 (by rfl) ⟨1571477, by rfl⟩ : syracuseStep 2095303 = 3142955) B3142955
theorem B2357221 : Blo 2093435 2357221 := bbase (se 4 (by rfl) ⟨220989, by rfl⟩ : syracuseStep 2357221 = 441979) (by norm_num)
theorem B3142961 : Blo 2093435 3142961 := bstep (se 2 (by rfl) ⟨1178610, by rfl⟩ : syracuseStep 3142961 = 2357221) B2357221
theorem B2095307 : Blo 2093435 2095307 := bstep (se 1 (by rfl) ⟨1571480, by rfl⟩ : syracuseStep 2095307 = 3142961) B3142961
theorem B3236069 : Blo 2093435 3236069 := bbase (se 4 (by rfl) ⟨303381, by rfl⟩ : syracuseStep 3236069 = 606763) (by norm_num)
theorem B8629517 : Blo 2093435 8629517 := bstep (se 3 (by rfl) ⟨1618034, by rfl⟩ : syracuseStep 8629517 = 3236069) B3236069
theorem B23012045 : Blo 2093435 23012045 := bstep (se 3 (by rfl) ⟨4314758, by rfl⟩ : syracuseStep 23012045 = 8629517) B8629517
theorem B15341363 : Blo 2093435 15341363 := bstep (se 1 (by rfl) ⟨11506022, by rfl⟩ : syracuseStep 15341363 = 23012045) B23012045
theorem B10227575 : Blo 2093435 10227575 := bstep (se 1 (by rfl) ⟨7670681, by rfl⟩ : syracuseStep 10227575 = 15341363) B15341363
theorem B6818383 : Blo 2093435 6818383 := bstep (se 1 (by rfl) ⟨5113787, by rfl⟩ : syracuseStep 6818383 = 10227575) B10227575
theorem B9091177 : Blo 2093435 9091177 := bstep (se 2 (by rfl) ⟨3409191, by rfl⟩ : syracuseStep 9091177 = 6818383) B6818383
theorem B48486277 : Blo 2093435 48486277 := bstep (se 4 (by rfl) ⟨4545588, by rfl⟩ : syracuseStep 48486277 = 9091177) B9091177
theorem B258593477 : Blo 2093435 258593477 := bstep (se 4 (by rfl) ⟨24243138, by rfl⟩ : syracuseStep 258593477 = 48486277) B48486277
theorem B689582605 : Blo 2093435 689582605 := bstep (se 3 (by rfl) ⟨129296738, by rfl⟩ : syracuseStep 689582605 = 258593477) B258593477
theorem B919443473 : Blo 2093435 919443473 := bstep (se 2 (by rfl) ⟨344791302, by rfl⟩ : syracuseStep 919443473 = 689582605) B689582605
theorem B612962315 : Blo 2093435 612962315 := bstep (se 1 (by rfl) ⟨459721736, by rfl⟩ : syracuseStep 612962315 = 919443473) B919443473
theorem B408641543 : Blo 2093435 408641543 := bstep (se 1 (by rfl) ⟨306481157, by rfl⟩ : syracuseStep 408641543 = 612962315) B612962315
theorem B272427695 : Blo 2093435 272427695 := bstep (se 1 (by rfl) ⟨204320771, by rfl⟩ : syracuseStep 272427695 = 408641543) B408641543
theorem B181618463 : Blo 2093435 181618463 := bstep (se 1 (by rfl) ⟨136213847, by rfl⟩ : syracuseStep 181618463 = 272427695) B272427695
theorem B484315901 : Blo 2093435 484315901 := bstep (se 3 (by rfl) ⟨90809231, by rfl⟩ : syracuseStep 484315901 = 181618463) B181618463
theorem B322877267 : Blo 2093435 322877267 := bstep (se 1 (by rfl) ⟨242157950, by rfl⟩ : syracuseStep 322877267 = 484315901) B484315901
theorem B215251511 : Blo 2093435 215251511 := bstep (se 1 (by rfl) ⟨161438633, by rfl⟩ : syracuseStep 215251511 = 322877267) B322877267
theorem B574004029 : Blo 2093435 574004029 := bstep (se 3 (by rfl) ⟨107625755, by rfl⟩ : syracuseStep 574004029 = 215251511) B215251511
theorem B765338705 : Blo 2093435 765338705 := bstep (se 2 (by rfl) ⟨287002014, by rfl⟩ : syracuseStep 765338705 = 574004029) B574004029
theorem B510225803 : Blo 2093435 510225803 := bstep (se 1 (by rfl) ⟨382669352, by rfl⟩ : syracuseStep 510225803 = 765338705) B765338705
theorem B340150535 : Blo 2093435 340150535 := bstep (se 1 (by rfl) ⟨255112901, by rfl⟩ : syracuseStep 340150535 = 510225803) B510225803
theorem B226767023 : Blo 2093435 226767023 := bstep (se 1 (by rfl) ⟨170075267, by rfl⟩ : syracuseStep 226767023 = 340150535) B340150535
theorem B151178015 : Blo 2093435 151178015 := bstep (se 1 (by rfl) ⟨113383511, by rfl⟩ : syracuseStep 151178015 = 226767023) B226767023
theorem B100785343 : Blo 2093435 100785343 := bstep (se 1 (by rfl) ⟨75589007, by rfl⟩ : syracuseStep 100785343 = 151178015) B151178015
theorem B134380457 : Blo 2093435 134380457 := bstep (se 2 (by rfl) ⟨50392671, by rfl⟩ : syracuseStep 134380457 = 100785343) B100785343
theorem B89586971 : Blo 2093435 89586971 := bstep (se 1 (by rfl) ⟨67190228, by rfl⟩ : syracuseStep 89586971 = 134380457) B134380457
theorem B59724647 : Blo 2093435 59724647 := bstep (se 1 (by rfl) ⟨44793485, by rfl⟩ : syracuseStep 59724647 = 89586971) B89586971
theorem B39816431 : Blo 2093435 39816431 := bstep (se 1 (by rfl) ⟨29862323, by rfl⟩ : syracuseStep 39816431 = 59724647) B59724647
theorem B26544287 : Blo 2093435 26544287 := bstep (se 1 (by rfl) ⟨19908215, by rfl⟩ : syracuseStep 26544287 = 39816431) B39816431
theorem B17696191 : Blo 2093435 17696191 := bstep (se 1 (by rfl) ⟨13272143, by rfl⟩ : syracuseStep 17696191 = 26544287) B26544287
theorem B23594921 : Blo 2093435 23594921 := bstep (se 2 (by rfl) ⟨8848095, by rfl⟩ : syracuseStep 23594921 = 17696191) B17696191
theorem B15729947 : Blo 2093435 15729947 := bstep (se 1 (by rfl) ⟨11797460, by rfl⟩ : syracuseStep 15729947 = 23594921) B23594921
theorem B10486631 : Blo 2093435 10486631 := bstep (se 1 (by rfl) ⟨7864973, by rfl⟩ : syracuseStep 10486631 = 15729947) B15729947
theorem B27964349 : Blo 2093435 27964349 := bstep (se 3 (by rfl) ⟨5243315, by rfl⟩ : syracuseStep 27964349 = 10486631) B10486631
theorem B18642899 : Blo 2093435 18642899 := bstep (se 1 (by rfl) ⟨13982174, by rfl⟩ : syracuseStep 18642899 = 27964349) B27964349
theorem B12428599 : Blo 2093435 12428599 := bstep (se 1 (by rfl) ⟨9321449, by rfl⟩ : syracuseStep 12428599 = 18642899) B18642899
theorem B16571465 : Blo 2093435 16571465 := bstep (se 2 (by rfl) ⟨6214299, by rfl⟩ : syracuseStep 16571465 = 12428599) B12428599
theorem B11047643 : Blo 2093435 11047643 := bstep (se 1 (by rfl) ⟨8285732, by rfl⟩ : syracuseStep 11047643 = 16571465) B16571465
theorem B7365095 : Blo 2093435 7365095 := bstep (se 1 (by rfl) ⟨5523821, by rfl⟩ : syracuseStep 7365095 = 11047643) B11047643
theorem B4910063 : Blo 2093435 4910063 := bstep (se 1 (by rfl) ⟨3682547, by rfl⟩ : syracuseStep 4910063 = 7365095) B7365095
theorem B13093501 : Blo 2093435 13093501 := bstep (se 3 (by rfl) ⟨2455031, by rfl⟩ : syracuseStep 13093501 = 4910063) B4910063
theorem B17458001 : Blo 2093435 17458001 := bstep (se 2 (by rfl) ⟨6546750, by rfl⟩ : syracuseStep 17458001 = 13093501) B13093501
theorem B11638667 : Blo 2093435 11638667 := bstep (se 1 (by rfl) ⟨8729000, by rfl⟩ : syracuseStep 11638667 = 17458001) B17458001
theorem B7759111 : Blo 2093435 7759111 := bstep (se 1 (by rfl) ⟨5819333, by rfl⟩ : syracuseStep 7759111 = 11638667) B11638667
theorem B10345481 : Blo 2093435 10345481 := bstep (se 2 (by rfl) ⟨3879555, by rfl⟩ : syracuseStep 10345481 = 7759111) B7759111
theorem B6896987 : Blo 2093435 6896987 := bstep (se 1 (by rfl) ⟨5172740, by rfl⟩ : syracuseStep 6896987 = 10345481) B10345481
theorem B4597991 : Blo 2093435 4597991 := bstep (se 1 (by rfl) ⟨3448493, by rfl⟩ : syracuseStep 4597991 = 6896987) B6896987
theorem B3065327 : Blo 2093435 3065327 := bstep (se 1 (by rfl) ⟨2298995, by rfl⟩ : syracuseStep 3065327 = 4597991) B4597991
theorem B32696821 : Blo 2093435 32696821 := bstep (se 5 (by rfl) ⟨1532663, by rfl⟩ : syracuseStep 32696821 = 3065327) B3065327
theorem B43595761 : Blo 2093435 43595761 := bstep (se 2 (by rfl) ⟨16348410, by rfl⟩ : syracuseStep 43595761 = 32696821) B32696821
theorem B58127681 : Blo 2093435 58127681 := bstep (se 2 (by rfl) ⟨21797880, by rfl⟩ : syracuseStep 58127681 = 43595761) B43595761
theorem B38751787 : Blo 2093435 38751787 := bstep (se 1 (by rfl) ⟨29063840, by rfl⟩ : syracuseStep 38751787 = 58127681) B58127681
theorem B51669049 : Blo 2093435 51669049 := bstep (se 2 (by rfl) ⟨19375893, by rfl⟩ : syracuseStep 51669049 = 38751787) B38751787
theorem B68892065 : Blo 2093435 68892065 := bstep (se 2 (by rfl) ⟨25834524, by rfl⟩ : syracuseStep 68892065 = 51669049) B51669049
theorem B45928043 : Blo 2093435 45928043 := bstep (se 1 (by rfl) ⟨34446032, by rfl⟩ : syracuseStep 45928043 = 68892065) B68892065
theorem B30618695 : Blo 2093435 30618695 := bstep (se 1 (by rfl) ⟨22964021, by rfl⟩ : syracuseStep 30618695 = 45928043) B45928043
theorem B81649853 : Blo 2093435 81649853 := bstep (se 3 (by rfl) ⟨15309347, by rfl⟩ : syracuseStep 81649853 = 30618695) B30618695
theorem B54433235 : Blo 2093435 54433235 := bstep (se 1 (by rfl) ⟨40824926, by rfl⟩ : syracuseStep 54433235 = 81649853) B81649853
theorem B36288823 : Blo 2093435 36288823 := bstep (se 1 (by rfl) ⟨27216617, by rfl⟩ : syracuseStep 36288823 = 54433235) B54433235
theorem B48385097 : Blo 2093435 48385097 := bstep (se 2 (by rfl) ⟨18144411, by rfl⟩ : syracuseStep 48385097 = 36288823) B36288823
theorem B32256731 : Blo 2093435 32256731 := bstep (se 1 (by rfl) ⟨24192548, by rfl⟩ : syracuseStep 32256731 = 48385097) B48385097
theorem B21504487 : Blo 2093435 21504487 := bstep (se 1 (by rfl) ⟨16128365, by rfl⟩ : syracuseStep 21504487 = 32256731) B32256731
theorem B28672649 : Blo 2093435 28672649 := bstep (se 2 (by rfl) ⟨10752243, by rfl⟩ : syracuseStep 28672649 = 21504487) B21504487
theorem B19115099 : Blo 2093435 19115099 := bstep (se 1 (by rfl) ⟨14336324, by rfl⟩ : syracuseStep 19115099 = 28672649) B28672649
theorem B12743399 : Blo 2093435 12743399 := bstep (se 1 (by rfl) ⟨9557549, by rfl⟩ : syracuseStep 12743399 = 19115099) B19115099
theorem B8495599 : Blo 2093435 8495599 := bstep (se 1 (by rfl) ⟨6371699, by rfl⟩ : syracuseStep 8495599 = 12743399) B12743399
theorem B11327465 : Blo 2093435 11327465 := bstep (se 2 (by rfl) ⟨4247799, by rfl⟩ : syracuseStep 11327465 = 8495599) B8495599
theorem B7551643 : Blo 2093435 7551643 := bstep (se 1 (by rfl) ⟨5663732, by rfl⟩ : syracuseStep 7551643 = 11327465) B11327465
theorem B10068857 : Blo 2093435 10068857 := bstep (se 2 (by rfl) ⟨3775821, by rfl⟩ : syracuseStep 10068857 = 7551643) B7551643
theorem B6712571 : Blo 2093435 6712571 := bstep (se 1 (by rfl) ⟨5034428, by rfl⟩ : syracuseStep 6712571 = 10068857) B10068857
theorem B4475047 : Blo 2093435 4475047 := bstep (se 1 (by rfl) ⟨3356285, by rfl⟩ : syracuseStep 4475047 = 6712571) B6712571
theorem B5966729 : Blo 2093435 5966729 := bstep (se 2 (by rfl) ⟨2237523, by rfl⟩ : syracuseStep 5966729 = 4475047) B4475047
theorem B3977819 : Blo 2093435 3977819 := bstep (se 1 (by rfl) ⟨2983364, by rfl⟩ : syracuseStep 3977819 = 5966729) B5966729
theorem B2651879 : Blo 2093435 2651879 := bstep (se 1 (by rfl) ⟨1988909, by rfl⟩ : syracuseStep 2651879 = 3977819) B3977819
theorem B7071677 : Blo 2093435 7071677 := bstep (se 3 (by rfl) ⟨1325939, by rfl⟩ : syracuseStep 7071677 = 2651879) B2651879
theorem B4714451 : Blo 2093435 4714451 := bstep (se 1 (by rfl) ⟨3535838, by rfl⟩ : syracuseStep 4714451 = 7071677) B7071677
theorem B3142967 : Blo 2093435 3142967 := bstep (se 1 (by rfl) ⟨2357225, by rfl⟩ : syracuseStep 3142967 = 4714451) B4714451
theorem B2095311 : Blo 2093435 2095311 := bstep (se 1 (by rfl) ⟨1571483, by rfl⟩ : syracuseStep 2095311 = 3142967) B3142967
theorem B3142973 : Blo 2093435 3142973 := bbase (se 3 (by rfl) ⟨589307, by rfl⟩ : syracuseStep 3142973 = 1178615) (by norm_num)
theorem B2095315 : Blo 2093435 2095315 := bstep (se 1 (by rfl) ⟨1571486, by rfl⟩ : syracuseStep 2095315 = 3142973) B3142973
theorem B4714469 : Blo 2093435 4714469 := bbase (se 4 (by rfl) ⟨441981, by rfl⟩ : syracuseStep 4714469 = 883963) (by norm_num)
theorem B3142979 : Blo 2093435 3142979 := bstep (se 1 (by rfl) ⟨2357234, by rfl⟩ : syracuseStep 3142979 = 4714469) B4714469
theorem B2095319 : Blo 2093435 2095319 := bstep (se 1 (by rfl) ⟨1571489, by rfl⟩ : syracuseStep 2095319 = 3142979) B3142979
theorem B5303789 : Blo 2093435 5303789 := bbase (se 3 (by rfl) ⟨994460, by rfl⟩ : syracuseStep 5303789 = 1988921) (by norm_num)
theorem B3535859 : Blo 2093435 3535859 := bstep (se 1 (by rfl) ⟨2651894, by rfl⟩ : syracuseStep 3535859 = 5303789) B5303789
theorem B2357239 : Blo 2093435 2357239 := bstep (se 1 (by rfl) ⟨1767929, by rfl⟩ : syracuseStep 2357239 = 3535859) B3535859
theorem B3142985 : Blo 2093435 3142985 := bstep (se 2 (by rfl) ⟨1178619, by rfl⟩ : syracuseStep 3142985 = 2357239) B2357239
theorem B2095323 : Blo 2093435 2095323 := bstep (se 1 (by rfl) ⟨1571492, by rfl⟩ : syracuseStep 2095323 = 3142985) B3142985
theorem B7551701 : Blo 2093435 7551701 := bbase (se 7 (by rfl) ⟨88496, by rfl⟩ : syracuseStep 7551701 = 176993) (by norm_num)
theorem B5034467 : Blo 2093435 5034467 := bstep (se 1 (by rfl) ⟨3775850, by rfl⟩ : syracuseStep 5034467 = 7551701) B7551701
theorem B3356311 : Blo 2093435 3356311 := bstep (se 1 (by rfl) ⟨2517233, by rfl⟩ : syracuseStep 3356311 = 5034467) B5034467
theorem B4475081 : Blo 2093435 4475081 := bstep (se 2 (by rfl) ⟨1678155, by rfl⟩ : syracuseStep 4475081 = 3356311) B3356311
theorem B2983387 : Blo 2093435 2983387 := bstep (se 1 (by rfl) ⟨2237540, by rfl⟩ : syracuseStep 2983387 = 4475081) B4475081
theorem B3977849 : Blo 2093435 3977849 := bstep (se 2 (by rfl) ⟨1491693, by rfl⟩ : syracuseStep 3977849 = 2983387) B2983387
theorem B10607597 : Blo 2093435 10607597 := bstep (se 3 (by rfl) ⟨1988924, by rfl⟩ : syracuseStep 10607597 = 3977849) B3977849
theorem B7071731 : Blo 2093435 7071731 := bstep (se 1 (by rfl) ⟨5303798, by rfl⟩ : syracuseStep 7071731 = 10607597) B10607597
theorem B4714487 : Blo 2093435 4714487 := bstep (se 1 (by rfl) ⟨3535865, by rfl⟩ : syracuseStep 4714487 = 7071731) B7071731
theorem B3142991 : Blo 2093435 3142991 := bstep (se 1 (by rfl) ⟨2357243, by rfl⟩ : syracuseStep 3142991 = 4714487) B4714487
theorem B2095327 : Blo 2093435 2095327 := bstep (se 1 (by rfl) ⟨1571495, by rfl⟩ : syracuseStep 2095327 = 3142991) B3142991
theorem B3142997 : Blo 2093435 3142997 := bbase (se 13 (by rfl) ⟨575, by rfl⟩ : syracuseStep 3142997 = 1151) (by norm_num)
theorem B2095331 : Blo 2093435 2095331 := bstep (se 1 (by rfl) ⟨1571498, by rfl⟩ : syracuseStep 2095331 = 3142997) B3142997
theorem B2237549 : Blo 2093435 2237549 := bbase (se 3 (by rfl) ⟨419540, by rfl⟩ : syracuseStep 2237549 = 839081) (by norm_num)
theorem B5966797 : Blo 2093435 5966797 := bstep (se 3 (by rfl) ⟨1118774, by rfl⟩ : syracuseStep 5966797 = 2237549) B2237549
theorem B7955729 : Blo 2093435 7955729 := bstep (se 2 (by rfl) ⟨2983398, by rfl⟩ : syracuseStep 7955729 = 5966797) B5966797
theorem B5303819 : Blo 2093435 5303819 := bstep (se 1 (by rfl) ⟨3977864, by rfl⟩ : syracuseStep 5303819 = 7955729) B7955729
theorem B3535879 : Blo 2093435 3535879 := bstep (se 1 (by rfl) ⟨2651909, by rfl⟩ : syracuseStep 3535879 = 5303819) B5303819
theorem B4714505 : Blo 2093435 4714505 := bstep (se 2 (by rfl) ⟨1767939, by rfl⟩ : syracuseStep 4714505 = 3535879) B3535879
theorem B3143003 : Blo 2093435 3143003 := bstep (se 1 (by rfl) ⟨2357252, by rfl⟩ : syracuseStep 3143003 = 4714505) B4714505
theorem B2095335 : Blo 2093435 2095335 := bstep (se 1 (by rfl) ⟨1571501, by rfl⟩ : syracuseStep 2095335 = 3143003) B3143003
theorem B2357257 : Blo 2093435 2357257 := bbase (se 2 (by rfl) ⟨883971, by rfl⟩ : syracuseStep 2357257 = 1767943) (by norm_num)
theorem B3143009 : Blo 2093435 3143009 := bstep (se 2 (by rfl) ⟨1178628, by rfl⟩ : syracuseStep 3143009 = 2357257) B2357257
theorem B2095339 : Blo 2093435 2095339 := bstep (se 1 (by rfl) ⟨1571504, by rfl⟩ : syracuseStep 2095339 = 3143009) B3143009
theorem B6048229 : Blo 2093435 6048229 := bbase (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) (by norm_num)
theorem B8064305 : Blo 2093435 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B5376203 : Blo 2093435 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B3584135 : Blo 2093435 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B9557693 : Blo 2093435 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B6371795 : Blo 2093435 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B16991453 : Blo 2093435 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B11327635 : Blo 2093435 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B15103513 : Blo 2093435 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B20138017 : Blo 2093435 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B26850689 : Blo 2093435 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B17900459 : Blo 2093435 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B11933639 : Blo 2093435 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B7955759 : Blo 2093435 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B5303839 : Blo 2093435 5303839 := bstep (se 1 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 5303839 = 7955759) B7955759
theorem B7071785 : Blo 2093435 7071785 := bstep (se 2 (by rfl) ⟨2651919, by rfl⟩ : syracuseStep 7071785 = 5303839) B5303839
theorem B4714523 : Blo 2093435 4714523 := bstep (se 1 (by rfl) ⟨3535892, by rfl⟩ : syracuseStep 4714523 = 7071785) B7071785
theorem B3143015 : Blo 2093435 3143015 := bstep (se 1 (by rfl) ⟨2357261, by rfl⟩ : syracuseStep 3143015 = 4714523) B4714523
theorem B2095343 : Blo 2093435 2095343 := bstep (se 1 (by rfl) ⟨1571507, by rfl⟩ : syracuseStep 2095343 = 3143015) B3143015
theorem B3143021 : Blo 2093435 3143021 := bbase (se 3 (by rfl) ⟨589316, by rfl⟩ : syracuseStep 3143021 = 1178633) (by norm_num)
theorem B2095347 : Blo 2093435 2095347 := bstep (se 1 (by rfl) ⟨1571510, by rfl⟩ : syracuseStep 2095347 = 3143021) B3143021
theorem B4714541 : Blo 2093435 4714541 := bbase (se 3 (by rfl) ⟨883976, by rfl⟩ : syracuseStep 4714541 = 1767953) (by norm_num)
theorem B3143027 : Blo 2093435 3143027 := bstep (se 1 (by rfl) ⟨2357270, by rfl⟩ : syracuseStep 3143027 = 4714541) B4714541
theorem B2095351 : Blo 2093435 2095351 := bstep (se 1 (by rfl) ⟨1571513, by rfl⟩ : syracuseStep 2095351 = 3143027) B3143027
theorem B3775901 : Blo 2093435 3775901 := bbase (se 3 (by rfl) ⟨707981, by rfl⟩ : syracuseStep 3775901 = 1415963) (by norm_num)
theorem B10069069 : Blo 2093435 10069069 := bstep (se 3 (by rfl) ⟨1887950, by rfl⟩ : syracuseStep 10069069 = 3775901) B3775901
theorem B13425425 : Blo 2093435 13425425 := bstep (se 2 (by rfl) ⟨5034534, by rfl⟩ : syracuseStep 13425425 = 10069069) B10069069
theorem B8950283 : Blo 2093435 8950283 := bstep (se 1 (by rfl) ⟨6712712, by rfl⟩ : syracuseStep 8950283 = 13425425) B13425425
theorem B5966855 : Blo 2093435 5966855 := bstep (se 1 (by rfl) ⟨4475141, by rfl⟩ : syracuseStep 5966855 = 8950283) B8950283
theorem B3977903 : Blo 2093435 3977903 := bstep (se 1 (by rfl) ⟨2983427, by rfl⟩ : syracuseStep 3977903 = 5966855) B5966855
theorem B2651935 : Blo 2093435 2651935 := bstep (se 1 (by rfl) ⟨1988951, by rfl⟩ : syracuseStep 2651935 = 3977903) B3977903
theorem B3535913 : Blo 2093435 3535913 := bstep (se 2 (by rfl) ⟨1325967, by rfl⟩ : syracuseStep 3535913 = 2651935) B2651935
theorem B2357275 : Blo 2093435 2357275 := bstep (se 1 (by rfl) ⟨1767956, by rfl⟩ : syracuseStep 2357275 = 3535913) B3535913
theorem B3143033 : Blo 2093435 3143033 := bstep (se 2 (by rfl) ⟨1178637, by rfl⟩ : syracuseStep 3143033 = 2357275) B2357275
theorem B2095355 : Blo 2093435 2095355 := bstep (se 1 (by rfl) ⟨1571516, by rfl⟩ : syracuseStep 2095355 = 3143033) B3143033
theorem B5663861 : Blo 2093435 5663861 := bbase (se 5 (by rfl) ⟨265493, by rfl⟩ : syracuseStep 5663861 = 530987) (by norm_num)
theorem B3775907 : Blo 2093435 3775907 := bstep (se 1 (by rfl) ⟨2831930, by rfl⟩ : syracuseStep 3775907 = 5663861) B5663861
theorem B10069085 : Blo 2093435 10069085 := bstep (se 3 (by rfl) ⟨1887953, by rfl⟩ : syracuseStep 10069085 = 3775907) B3775907
theorem B6712723 : Blo 2093435 6712723 := bstep (se 1 (by rfl) ⟨5034542, by rfl⟩ : syracuseStep 6712723 = 10069085) B10069085
theorem B35801189 : Blo 2093435 35801189 := bstep (se 4 (by rfl) ⟨3356361, by rfl⟩ : syracuseStep 35801189 = 6712723) B6712723
theorem B23867459 : Blo 2093435 23867459 := bstep (se 1 (by rfl) ⟨17900594, by rfl⟩ : syracuseStep 23867459 = 35801189) B35801189
theorem B15911639 : Blo 2093435 15911639 := bstep (se 1 (by rfl) ⟨11933729, by rfl⟩ : syracuseStep 15911639 = 23867459) B23867459
theorem B10607759 : Blo 2093435 10607759 := bstep (se 1 (by rfl) ⟨7955819, by rfl⟩ : syracuseStep 10607759 = 15911639) B15911639
theorem B7071839 : Blo 2093435 7071839 := bstep (se 1 (by rfl) ⟨5303879, by rfl⟩ : syracuseStep 7071839 = 10607759) B10607759
theorem B4714559 : Blo 2093435 4714559 := bstep (se 1 (by rfl) ⟨3535919, by rfl⟩ : syracuseStep 4714559 = 7071839) B7071839
theorem B3143039 : Blo 2093435 3143039 := bstep (se 1 (by rfl) ⟨2357279, by rfl⟩ : syracuseStep 3143039 = 4714559) B4714559
theorem B2095359 : Blo 2093435 2095359 := bstep (se 1 (by rfl) ⟨1571519, by rfl⟩ : syracuseStep 2095359 = 3143039) B3143039
theorem B3143045 : Blo 2093435 3143045 := bbase (se 4 (by rfl) ⟨294660, by rfl⟩ : syracuseStep 3143045 = 589321) (by norm_num)
theorem B2095363 : Blo 2093435 2095363 := bstep (se 1 (by rfl) ⟨1571522, by rfl⟩ : syracuseStep 2095363 = 3143045) B3143045
theorem B3535933 : Blo 2093435 3535933 := bbase (se 3 (by rfl) ⟨662987, by rfl⟩ : syracuseStep 3535933 = 1325975) (by norm_num)
theorem B4714577 : Blo 2093435 4714577 := bstep (se 2 (by rfl) ⟨1767966, by rfl⟩ : syracuseStep 4714577 = 3535933) B3535933
theorem B3143051 : Blo 2093435 3143051 := bstep (se 1 (by rfl) ⟨2357288, by rfl⟩ : syracuseStep 3143051 = 4714577) B4714577
theorem B2095367 : Blo 2093435 2095367 := bstep (se 1 (by rfl) ⟨1571525, by rfl⟩ : syracuseStep 2095367 = 3143051) B3143051
theorem B2357293 : Blo 2093435 2357293 := bbase (se 3 (by rfl) ⟨441992, by rfl⟩ : syracuseStep 2357293 = 883985) (by norm_num)
theorem B3143057 : Blo 2093435 3143057 := bstep (se 2 (by rfl) ⟨1178646, by rfl⟩ : syracuseStep 3143057 = 2357293) B2357293
theorem B2095371 : Blo 2093435 2095371 := bstep (se 1 (by rfl) ⟨1571528, by rfl⟩ : syracuseStep 2095371 = 3143057) B3143057
theorem B7071893 : Blo 2093435 7071893 := bbase (se 6 (by rfl) ⟨165747, by rfl⟩ : syracuseStep 7071893 = 331495) (by norm_num)
theorem B4714595 : Blo 2093435 4714595 := bstep (se 1 (by rfl) ⟨3535946, by rfl⟩ : syracuseStep 4714595 = 7071893) B7071893
theorem B3143063 : Blo 2093435 3143063 := bstep (se 1 (by rfl) ⟨2357297, by rfl⟩ : syracuseStep 3143063 = 4714595) B4714595
theorem B2095375 : Blo 2093435 2095375 := bstep (se 1 (by rfl) ⟨1571531, by rfl⟩ : syracuseStep 2095375 = 3143063) B3143063
theorem B3143069 : Blo 2093435 3143069 := bbase (se 3 (by rfl) ⟨589325, by rfl⟩ : syracuseStep 3143069 = 1178651) (by norm_num)
theorem B2095379 : Blo 2093435 2095379 := bstep (se 1 (by rfl) ⟨1571534, by rfl⟩ : syracuseStep 2095379 = 3143069) B3143069
theorem B4714613 : Blo 2093435 4714613 := bbase (se 5 (by rfl) ⟨220997, by rfl⟩ : syracuseStep 4714613 = 441995) (by norm_num)
theorem B3143075 : Blo 2093435 3143075 := bstep (se 1 (by rfl) ⟨2357306, by rfl⟩ : syracuseStep 3143075 = 4714613) B4714613
theorem B2095383 : Blo 2093435 2095383 := bstep (se 1 (by rfl) ⟨1571537, by rfl⟩ : syracuseStep 2095383 = 3143075) B3143075
theorem B2123977 : Blo 2093435 2123977 := bbase (se 2 (by rfl) ⟨796491, by rfl⟩ : syracuseStep 2123977 = 1592983) (by norm_num)
theorem B2831969 : Blo 2093435 2831969 := bstep (se 2 (by rfl) ⟨1061988, by rfl⟩ : syracuseStep 2831969 = 2123977) B2123977
theorem B7551917 : Blo 2093435 7551917 := bstep (se 3 (by rfl) ⟨1415984, by rfl⟩ : syracuseStep 7551917 = 2831969) B2831969
theorem B5034611 : Blo 2093435 5034611 := bstep (se 1 (by rfl) ⟨3775958, by rfl⟩ : syracuseStep 5034611 = 7551917) B7551917
theorem B3356407 : Blo 2093435 3356407 := bstep (se 1 (by rfl) ⟨2517305, by rfl⟩ : syracuseStep 3356407 = 5034611) B5034611
theorem B17900837 : Blo 2093435 17900837 := bstep (se 4 (by rfl) ⟨1678203, by rfl⟩ : syracuseStep 17900837 = 3356407) B3356407
theorem B11933891 : Blo 2093435 11933891 := bstep (se 1 (by rfl) ⟨8950418, by rfl⟩ : syracuseStep 11933891 = 17900837) B17900837
theorem B7955927 : Blo 2093435 7955927 := bstep (se 1 (by rfl) ⟨5966945, by rfl⟩ : syracuseStep 7955927 = 11933891) B11933891
theorem B5303951 : Blo 2093435 5303951 := bstep (se 1 (by rfl) ⟨3977963, by rfl⟩ : syracuseStep 5303951 = 7955927) B7955927
theorem B3535967 : Blo 2093435 3535967 := bstep (se 1 (by rfl) ⟨2651975, by rfl⟩ : syracuseStep 3535967 = 5303951) B5303951
theorem B2357311 : Blo 2093435 2357311 := bstep (se 1 (by rfl) ⟨1767983, by rfl⟩ : syracuseStep 2357311 = 3535967) B3535967
theorem B3143081 : Blo 2093435 3143081 := bstep (se 2 (by rfl) ⟨1178655, by rfl⟩ : syracuseStep 3143081 = 2357311) B2357311
theorem B2095387 : Blo 2093435 2095387 := bstep (se 1 (by rfl) ⟨1571540, by rfl⟩ : syracuseStep 2095387 = 3143081) B3143081
theorem B7955941 : Blo 2093435 7955941 := bbase (se 4 (by rfl) ⟨745869, by rfl⟩ : syracuseStep 7955941 = 1491739) (by norm_num)
theorem B10607921 : Blo 2093435 10607921 := bstep (se 2 (by rfl) ⟨3977970, by rfl⟩ : syracuseStep 10607921 = 7955941) B7955941
theorem B7071947 : Blo 2093435 7071947 := bstep (se 1 (by rfl) ⟨5303960, by rfl⟩ : syracuseStep 7071947 = 10607921) B10607921
theorem B4714631 : Blo 2093435 4714631 := bstep (se 1 (by rfl) ⟨3535973, by rfl⟩ : syracuseStep 4714631 = 7071947) B7071947
theorem B3143087 : Blo 2093435 3143087 := bstep (se 1 (by rfl) ⟨2357315, by rfl⟩ : syracuseStep 3143087 = 4714631) B4714631
theorem B2095391 : Blo 2093435 2095391 := bstep (se 1 (by rfl) ⟨1571543, by rfl⟩ : syracuseStep 2095391 = 3143087) B3143087
theorem B3143093 : Blo 2093435 3143093 := bbase (se 5 (by rfl) ⟨147332, by rfl⟩ : syracuseStep 3143093 = 294665) (by norm_num)
theorem B2095395 : Blo 2093435 2095395 := bstep (se 1 (by rfl) ⟨1571546, by rfl⟩ : syracuseStep 2095395 = 3143093) B3143093
theorem B5303981 : Blo 2093435 5303981 := bbase (se 3 (by rfl) ⟨994496, by rfl⟩ : syracuseStep 5303981 = 1988993) (by norm_num)
theorem B3535987 : Blo 2093435 3535987 := bstep (se 1 (by rfl) ⟨2651990, by rfl⟩ : syracuseStep 3535987 = 5303981) B5303981
theorem B4714649 : Blo 2093435 4714649 := bstep (se 2 (by rfl) ⟨1767993, by rfl⟩ : syracuseStep 4714649 = 3535987) B3535987
theorem B3143099 : Blo 2093435 3143099 := bstep (se 1 (by rfl) ⟨2357324, by rfl⟩ : syracuseStep 3143099 = 4714649) B4714649
theorem B2095399 : Blo 2093435 2095399 := bstep (se 1 (by rfl) ⟨1571549, by rfl⟩ : syracuseStep 2095399 = 3143099) B3143099
theorem B2357329 : Blo 2093435 2357329 := bbase (se 2 (by rfl) ⟨883998, by rfl⟩ : syracuseStep 2357329 = 1767997) (by norm_num)
theorem B3143105 : Blo 2093435 3143105 := bstep (se 2 (by rfl) ⟨1178664, by rfl⟩ : syracuseStep 3143105 = 2357329) B2357329
theorem B2095403 : Blo 2093435 2095403 := bstep (se 1 (by rfl) ⟨1571552, by rfl⟩ : syracuseStep 2095403 = 3143105) B3143105
theorem B2983501 : Blo 2093435 2983501 := bbase (se 3 (by rfl) ⟨559406, by rfl⟩ : syracuseStep 2983501 = 1118813) (by norm_num)
theorem B3978001 : Blo 2093435 3978001 := bstep (se 2 (by rfl) ⟨1491750, by rfl⟩ : syracuseStep 3978001 = 2983501) B2983501
theorem B5304001 : Blo 2093435 5304001 := bstep (se 2 (by rfl) ⟨1989000, by rfl⟩ : syracuseStep 5304001 = 3978001) B3978001
theorem B7072001 : Blo 2093435 7072001 := bstep (se 2 (by rfl) ⟨2652000, by rfl⟩ : syracuseStep 7072001 = 5304001) B5304001
theorem B4714667 : Blo 2093435 4714667 := bstep (se 1 (by rfl) ⟨3536000, by rfl⟩ : syracuseStep 4714667 = 7072001) B7072001
theorem B3143111 : Blo 2093435 3143111 := bstep (se 1 (by rfl) ⟨2357333, by rfl⟩ : syracuseStep 3143111 = 4714667) B4714667
theorem B2095407 : Blo 2093435 2095407 := bstep (se 1 (by rfl) ⟨1571555, by rfl⟩ : syracuseStep 2095407 = 3143111) B3143111
theorem B3143117 : Blo 2093435 3143117 := bbase (se 3 (by rfl) ⟨589334, by rfl⟩ : syracuseStep 3143117 = 1178669) (by norm_num)
theorem B2095411 : Blo 2093435 2095411 := bstep (se 1 (by rfl) ⟨1571558, by rfl⟩ : syracuseStep 2095411 = 3143117) B3143117
theorem B4714685 : Blo 2093435 4714685 := bbase (se 3 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 4714685 = 1768007) (by norm_num)
theorem B3143123 : Blo 2093435 3143123 := bstep (se 1 (by rfl) ⟨2357342, by rfl⟩ : syracuseStep 3143123 = 4714685) B4714685
theorem B2095415 : Blo 2093435 2095415 := bstep (se 1 (by rfl) ⟨1571561, by rfl⟩ : syracuseStep 2095415 = 3143123) B3143123
theorem B3536021 : Blo 2093435 3536021 := bbase (se 6 (by rfl) ⟨82875, by rfl⟩ : syracuseStep 3536021 = 165751) (by norm_num)
theorem B2357347 : Blo 2093435 2357347 := bstep (se 1 (by rfl) ⟨1768010, by rfl⟩ : syracuseStep 2357347 = 3536021) B3536021
theorem B3143129 : Blo 2093435 3143129 := bstep (se 2 (by rfl) ⟨1178673, by rfl⟩ : syracuseStep 3143129 = 2357347) B2357347
theorem B2095419 : Blo 2093435 2095419 := bstep (se 1 (by rfl) ⟨1571564, by rfl⟩ : syracuseStep 2095419 = 3143129) B3143129
theorem B2124013 : Blo 2093435 2124013 := bbase (se 3 (by rfl) ⟨398252, by rfl⟩ : syracuseStep 2124013 = 796505) (by norm_num)
theorem B2832017 : Blo 2093435 2832017 := bstep (se 2 (by rfl) ⟨1062006, by rfl⟩ : syracuseStep 2832017 = 2124013) B2124013
theorem B7552045 : Blo 2093435 7552045 := bstep (se 3 (by rfl) ⟨1416008, by rfl⟩ : syracuseStep 7552045 = 2832017) B2832017
theorem B10069393 : Blo 2093435 10069393 := bstep (se 2 (by rfl) ⟨3776022, by rfl⟩ : syracuseStep 10069393 = 7552045) B7552045
theorem B13425857 : Blo 2093435 13425857 := bstep (se 2 (by rfl) ⟨5034696, by rfl⟩ : syracuseStep 13425857 = 10069393) B10069393
theorem B8950571 : Blo 2093435 8950571 := bstep (se 1 (by rfl) ⟨6712928, by rfl⟩ : syracuseStep 8950571 = 13425857) B13425857
theorem B5967047 : Blo 2093435 5967047 := bstep (se 1 (by rfl) ⟨4475285, by rfl⟩ : syracuseStep 5967047 = 8950571) B8950571
theorem B15912125 : Blo 2093435 15912125 := bstep (se 3 (by rfl) ⟨2983523, by rfl⟩ : syracuseStep 15912125 = 5967047) B5967047
theorem B10608083 : Blo 2093435 10608083 := bstep (se 1 (by rfl) ⟨7956062, by rfl⟩ : syracuseStep 10608083 = 15912125) B15912125
theorem B7072055 : Blo 2093435 7072055 := bstep (se 1 (by rfl) ⟨5304041, by rfl⟩ : syracuseStep 7072055 = 10608083) B10608083
theorem B4714703 : Blo 2093435 4714703 := bstep (se 1 (by rfl) ⟨3536027, by rfl⟩ : syracuseStep 4714703 = 7072055) B7072055
theorem B3143135 : Blo 2093435 3143135 := bstep (se 1 (by rfl) ⟨2357351, by rfl⟩ : syracuseStep 3143135 = 4714703) B4714703
theorem B2095423 : Blo 2093435 2095423 := bstep (se 1 (by rfl) ⟨1571567, by rfl⟩ : syracuseStep 2095423 = 3143135) B3143135
theorem B3143141 : Blo 2093435 3143141 := bbase (se 4 (by rfl) ⟨294669, by rfl⟩ : syracuseStep 3143141 = 589339) (by norm_num)
theorem B2095427 : Blo 2093435 2095427 := bstep (se 1 (by rfl) ⟨1571570, by rfl⟩ : syracuseStep 2095427 = 3143141) B3143141
theorem B8496085 : Blo 2093435 8496085 := bbase (se 7 (by rfl) ⟨99563, by rfl⟩ : syracuseStep 8496085 = 199127) (by norm_num)
theorem B11328113 : Blo 2093435 11328113 := bstep (se 2 (by rfl) ⟨4248042, by rfl⟩ : syracuseStep 11328113 = 8496085) B8496085
theorem B30208301 : Blo 2093435 30208301 := bstep (se 3 (by rfl) ⟨5664056, by rfl⟩ : syracuseStep 30208301 = 11328113) B11328113
theorem B20138867 : Blo 2093435 20138867 := bstep (se 1 (by rfl) ⟨15104150, by rfl⟩ : syracuseStep 20138867 = 30208301) B30208301
theorem B13425911 : Blo 2093435 13425911 := bstep (se 1 (by rfl) ⟨10069433, by rfl⟩ : syracuseStep 13425911 = 20138867) B20138867
theorem B8950607 : Blo 2093435 8950607 := bstep (se 1 (by rfl) ⟨6712955, by rfl⟩ : syracuseStep 8950607 = 13425911) B13425911
theorem B5967071 : Blo 2093435 5967071 := bstep (se 1 (by rfl) ⟨4475303, by rfl⟩ : syracuseStep 5967071 = 8950607) B8950607
theorem B3978047 : Blo 2093435 3978047 := bstep (se 1 (by rfl) ⟨2983535, by rfl⟩ : syracuseStep 3978047 = 5967071) B5967071
theorem B2652031 : Blo 2093435 2652031 := bstep (se 1 (by rfl) ⟨1989023, by rfl⟩ : syracuseStep 2652031 = 3978047) B3978047
theorem B3536041 : Blo 2093435 3536041 := bstep (se 2 (by rfl) ⟨1326015, by rfl⟩ : syracuseStep 3536041 = 2652031) B2652031
theorem B4714721 : Blo 2093435 4714721 := bstep (se 2 (by rfl) ⟨1768020, by rfl⟩ : syracuseStep 4714721 = 3536041) B3536041
theorem B3143147 : Blo 2093435 3143147 := bstep (se 1 (by rfl) ⟨2357360, by rfl⟩ : syracuseStep 3143147 = 4714721) B4714721
theorem B2095431 : Blo 2093435 2095431 := bstep (se 1 (by rfl) ⟨1571573, by rfl⟩ : syracuseStep 2095431 = 3143147) B3143147
theorem B2357365 : Blo 2093435 2357365 := bbase (se 5 (by rfl) ⟨110501, by rfl⟩ : syracuseStep 2357365 = 221003) (by norm_num)
theorem B3143153 : Blo 2093435 3143153 := bstep (se 2 (by rfl) ⟨1178682, by rfl⟩ : syracuseStep 3143153 = 2357365) B2357365
theorem B2095435 : Blo 2093435 2095435 := bstep (se 1 (by rfl) ⟨1571576, by rfl⟩ : syracuseStep 2095435 = 3143153) B3143153
theorem C0 (j : ℕ) (h1 : 523358 ≤ j) (h2 : j ≤ 523858) : Blo 2093435 (4 * j + 3) := by
  interval_cases j
  · exact B2093435
  · exact B2093439
  · exact B2093443
  · exact B2093447
  · exact B2093451
  · exact B2093455
  · exact B2093459
  · exact B2093463
  · exact B2093467
  · exact B2093471
  · exact B2093475
  · exact B2093479
  · exact B2093483
  · exact B2093487
  · exact B2093491
  · exact B2093495
  · exact B2093499
  · exact B2093503
  · exact B2093507
  · exact B2093511
  · exact B2093515
  · exact B2093519
  · exact B2093523
  · exact B2093527
  · exact B2093531
  · exact B2093535
  · exact B2093539
  · exact B2093543
  · exact B2093547
  · exact B2093551
  · exact B2093555
  · exact B2093559
  · exact B2093563
  · exact B2093567
  · exact B2093571
  · exact B2093575
  · exact B2093579
  · exact B2093583
  · exact B2093587
  · exact B2093591
  · exact B2093595
  · exact B2093599
  · exact B2093603
  · exact B2093607
  · exact B2093611
  · exact B2093615
  · exact B2093619
  · exact B2093623
  · exact B2093627
  · exact B2093631
  · exact B2093635
  · exact B2093639
  · exact B2093643
  · exact B2093647
  · exact B2093651
  · exact B2093655
  · exact B2093659
  · exact B2093663
  · exact B2093667
  · exact B2093671
  · exact B2093675
  · exact B2093679
  · exact B2093683
  · exact B2093687
  · exact B2093691
  · exact B2093695
  · exact B2093699
  · exact B2093703
  · exact B2093707
  · exact B2093711
  · exact B2093715
  · exact B2093719
  · exact B2093723
  · exact B2093727
  · exact B2093731
  · exact B2093735
  · exact B2093739
  · exact B2093743
  · exact B2093747
  · exact B2093751
  · exact B2093755
  · exact B2093759
  · exact B2093763
  · exact B2093767
  · exact B2093771
  · exact B2093775
  · exact B2093779
  · exact B2093783
  · exact B2093787
  · exact B2093791
  · exact B2093795
  · exact B2093799
  · exact B2093803
  · exact B2093807
  · exact B2093811
  · exact B2093815
  · exact B2093819
  · exact B2093823
  · exact B2093827
  · exact B2093831
  · exact B2093835
  · exact B2093839
  · exact B2093843
  · exact B2093847
  · exact B2093851
  · exact B2093855
  · exact B2093859
  · exact B2093863
  · exact B2093867
  · exact B2093871
  · exact B2093875
  · exact B2093879
  · exact B2093883
  · exact B2093887
  · exact B2093891
  · exact B2093895
  · exact B2093899
  · exact B2093903
  · exact B2093907
  · exact B2093911
  · exact B2093915
  · exact B2093919
  · exact B2093923
  · exact B2093927
  · exact B2093931
  · exact B2093935
  · exact B2093939
  · exact B2093943
  · exact B2093947
  · exact B2093951
  · exact B2093955
  · exact B2093959
  · exact B2093963
  · exact B2093967
  · exact B2093971
  · exact B2093975
  · exact B2093979
  · exact B2093983
  · exact B2093987
  · exact B2093991
  · exact B2093995
  · exact B2093999
  · exact B2094003
  · exact B2094007
  · exact B2094011
  · exact B2094015
  · exact B2094019
  · exact B2094023
  · exact B2094027
  · exact B2094031
  · exact B2094035
  · exact B2094039
  · exact B2094043
  · exact B2094047
  · exact B2094051
  · exact B2094055
  · exact B2094059
  · exact B2094063
  · exact B2094067
  · exact B2094071
  · exact B2094075
  · exact B2094079
  · exact B2094083
  · exact B2094087
  · exact B2094091
  · exact B2094095
  · exact B2094099
  · exact B2094103
  · exact B2094107
  · exact B2094111
  · exact B2094115
  · exact B2094119
  · exact B2094123
  · exact B2094127
  · exact B2094131
  · exact B2094135
  · exact B2094139
  · exact B2094143
  · exact B2094147
  · exact B2094151
  · exact B2094155
  · exact B2094159
  · exact B2094163
  · exact B2094167
  · exact B2094171
  · exact B2094175
  · exact B2094179
  · exact B2094183
  · exact B2094187
  · exact B2094191
  · exact B2094195
  · exact B2094199
  · exact B2094203
  · exact B2094207
  · exact B2094211
  · exact B2094215
  · exact B2094219
  · exact B2094223
  · exact B2094227
  · exact B2094231
  · exact B2094235
  · exact B2094239
  · exact B2094243
  · exact B2094247
  · exact B2094251
  · exact B2094255
  · exact B2094259
  · exact B2094263
  · exact B2094267
  · exact B2094271
  · exact B2094275
  · exact B2094279
  · exact B2094283
  · exact B2094287
  · exact B2094291
  · exact B2094295
  · exact B2094299
  · exact B2094303
  · exact B2094307
  · exact B2094311
  · exact B2094315
  · exact B2094319
  · exact B2094323
  · exact B2094327
  · exact B2094331
  · exact B2094335
  · exact B2094339
  · exact B2094343
  · exact B2094347
  · exact B2094351
  · exact B2094355
  · exact B2094359
  · exact B2094363
  · exact B2094367
  · exact B2094371
  · exact B2094375
  · exact B2094379
  · exact B2094383
  · exact B2094387
  · exact B2094391
  · exact B2094395
  · exact B2094399
  · exact B2094403
  · exact B2094407
  · exact B2094411
  · exact B2094415
  · exact B2094419
  · exact B2094423
  · exact B2094427
  · exact B2094431
  · exact B2094435
  · exact B2094439
  · exact B2094443
  · exact B2094447
  · exact B2094451
  · exact B2094455
  · exact B2094459
  · exact B2094463
  · exact B2094467
  · exact B2094471
  · exact B2094475
  · exact B2094479
  · exact B2094483
  · exact B2094487
  · exact B2094491
  · exact B2094495
  · exact B2094499
  · exact B2094503
  · exact B2094507
  · exact B2094511
  · exact B2094515
  · exact B2094519
  · exact B2094523
  · exact B2094527
  · exact B2094531
  · exact B2094535
  · exact B2094539
  · exact B2094543
  · exact B2094547
  · exact B2094551
  · exact B2094555
  · exact B2094559
  · exact B2094563
  · exact B2094567
  · exact B2094571
  · exact B2094575
  · exact B2094579
  · exact B2094583
  · exact B2094587
  · exact B2094591
  · exact B2094595
  · exact B2094599
  · exact B2094603
  · exact B2094607
  · exact B2094611
  · exact B2094615
  · exact B2094619
  · exact B2094623
  · exact B2094627
  · exact B2094631
  · exact B2094635
  · exact B2094639
  · exact B2094643
  · exact B2094647
  · exact B2094651
  · exact B2094655
  · exact B2094659
  · exact B2094663
  · exact B2094667
  · exact B2094671
  · exact B2094675
  · exact B2094679
  · exact B2094683
  · exact B2094687
  · exact B2094691
  · exact B2094695
  · exact B2094699
  · exact B2094703
  · exact B2094707
  · exact B2094711
  · exact B2094715
  · exact B2094719
  · exact B2094723
  · exact B2094727
  · exact B2094731
  · exact B2094735
  · exact B2094739
  · exact B2094743
  · exact B2094747
  · exact B2094751
  · exact B2094755
  · exact B2094759
  · exact B2094763
  · exact B2094767
  · exact B2094771
  · exact B2094775
  · exact B2094779
  · exact B2094783
  · exact B2094787
  · exact B2094791
  · exact B2094795
  · exact B2094799
  · exact B2094803
  · exact B2094807
  · exact B2094811
  · exact B2094815
  · exact B2094819
  · exact B2094823
  · exact B2094827
  · exact B2094831
  · exact B2094835
  · exact B2094839
  · exact B2094843
  · exact B2094847
  · exact B2094851
  · exact B2094855
  · exact B2094859
  · exact B2094863
  · exact B2094867
  · exact B2094871
  · exact B2094875
  · exact B2094879
  · exact B2094883
  · exact B2094887
  · exact B2094891
  · exact B2094895
  · exact B2094899
  · exact B2094903
  · exact B2094907
  · exact B2094911
  · exact B2094915
  · exact B2094919
  · exact B2094923
  · exact B2094927
  · exact B2094931
  · exact B2094935
  · exact B2094939
  · exact B2094943
  · exact B2094947
  · exact B2094951
  · exact B2094955
  · exact B2094959
  · exact B2094963
  · exact B2094967
  · exact B2094971
  · exact B2094975
  · exact B2094979
  · exact B2094983
  · exact B2094987
  · exact B2094991
  · exact B2094995
  · exact B2094999
  · exact B2095003
  · exact B2095007
  · exact B2095011
  · exact B2095015
  · exact B2095019
  · exact B2095023
  · exact B2095027
  · exact B2095031
  · exact B2095035
  · exact B2095039
  · exact B2095043
  · exact B2095047
  · exact B2095051
  · exact B2095055
  · exact B2095059
  · exact B2095063
  · exact B2095067
  · exact B2095071
  · exact B2095075
  · exact B2095079
  · exact B2095083
  · exact B2095087
  · exact B2095091
  · exact B2095095
  · exact B2095099
  · exact B2095103
  · exact B2095107
  · exact B2095111
  · exact B2095115
  · exact B2095119
  · exact B2095123
  · exact B2095127
  · exact B2095131
  · exact B2095135
  · exact B2095139
  · exact B2095143
  · exact B2095147
  · exact B2095151
  · exact B2095155
  · exact B2095159
  · exact B2095163
  · exact B2095167
  · exact B2095171
  · exact B2095175
  · exact B2095179
  · exact B2095183
  · exact B2095187
  · exact B2095191
  · exact B2095195
  · exact B2095199
  · exact B2095203
  · exact B2095207
  · exact B2095211
  · exact B2095215
  · exact B2095219
  · exact B2095223
  · exact B2095227
  · exact B2095231
  · exact B2095235
  · exact B2095239
  · exact B2095243
  · exact B2095247
  · exact B2095251
  · exact B2095255
  · exact B2095259
  · exact B2095263
  · exact B2095267
  · exact B2095271
  · exact B2095275
  · exact B2095279
  · exact B2095283
  · exact B2095287
  · exact B2095291
  · exact B2095295
  · exact B2095299
  · exact B2095303
  · exact B2095307
  · exact B2095311
  · exact B2095315
  · exact B2095319
  · exact B2095323
  · exact B2095327
  · exact B2095331
  · exact B2095335
  · exact B2095339
  · exact B2095343
  · exact B2095347
  · exact B2095351
  · exact B2095355
  · exact B2095359
  · exact B2095363
  · exact B2095367
  · exact B2095371
  · exact B2095375
  · exact B2095379
  · exact B2095383
  · exact B2095387
  · exact B2095391
  · exact B2095395
  · exact B2095399
  · exact B2095403
  · exact B2095407
  · exact B2095411
  · exact B2095415
  · exact B2095419
  · exact B2095423
  · exact B2095427
  · exact B2095431
  · exact B2095435
theorem solution (m : ℕ) (hlo : 2093435 ≤ m) (hhi : m ≤ 2095435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 523358 ≤ j := by omega
    have hj2 : j ≤ 523858 := by omega
    have hb : Blo 2093435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
