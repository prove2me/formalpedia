-- Prove2me | solution 1 for syracuse_descends_range_2181435_2183435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:57.308972+00:00
-- url     : https://prove2.me/submissions/d07cf602-5cc6-46f4-ad37-ce893d4379cf

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

theorem B3681173 : Blo 2181435 3681173 := bbase (se 6 (by rfl) ⟨86277, by rfl⟩ : syracuseStep 3681173 = 172555) (by norm_num)
theorem B2454115 : Blo 2181435 2454115 := bstep (se 1 (by rfl) ⟨1840586, by rfl⟩ : syracuseStep 2454115 = 3681173) B3681173
theorem B3272153 : Blo 2181435 3272153 := bstep (se 2 (by rfl) ⟨1227057, by rfl⟩ : syracuseStep 3272153 = 2454115) B2454115
theorem B2181435 : Blo 2181435 2181435 := bstep (se 1 (by rfl) ⟨1636076, by rfl⟩ : syracuseStep 2181435 = 3272153) B3272153
theorem B13976981 : Blo 2181435 13976981 := bbase (se 6 (by rfl) ⟨327585, by rfl⟩ : syracuseStep 13976981 = 655171) (by norm_num)
theorem B9317987 : Blo 2181435 9317987 := bstep (se 1 (by rfl) ⟨6988490, by rfl⟩ : syracuseStep 9317987 = 13976981) B13976981
theorem B6211991 : Blo 2181435 6211991 := bstep (se 1 (by rfl) ⟨4658993, by rfl⟩ : syracuseStep 6211991 = 9317987) B9317987
theorem B16565309 : Blo 2181435 16565309 := bstep (se 3 (by rfl) ⟨3105995, by rfl⟩ : syracuseStep 16565309 = 6211991) B6211991
theorem B11043539 : Blo 2181435 11043539 := bstep (se 1 (by rfl) ⟨8282654, by rfl⟩ : syracuseStep 11043539 = 16565309) B16565309
theorem B7362359 : Blo 2181435 7362359 := bstep (se 1 (by rfl) ⟨5521769, by rfl⟩ : syracuseStep 7362359 = 11043539) B11043539
theorem B4908239 : Blo 2181435 4908239 := bstep (se 1 (by rfl) ⟨3681179, by rfl⟩ : syracuseStep 4908239 = 7362359) B7362359
theorem B3272159 : Blo 2181435 3272159 := bstep (se 1 (by rfl) ⟨2454119, by rfl⟩ : syracuseStep 3272159 = 4908239) B4908239
theorem B2181439 : Blo 2181435 2181439 := bstep (se 1 (by rfl) ⟨1636079, by rfl⟩ : syracuseStep 2181439 = 3272159) B3272159
theorem B3272165 : Blo 2181435 3272165 := bbase (se 4 (by rfl) ⟨306765, by rfl⟩ : syracuseStep 3272165 = 613531) (by norm_num)
theorem B2181443 : Blo 2181435 2181443 := bstep (se 1 (by rfl) ⟨1636082, by rfl⟩ : syracuseStep 2181443 = 3272165) B3272165
theorem B2487613 : Blo 2181435 2487613 := bbase (se 3 (by rfl) ⟨466427, by rfl⟩ : syracuseStep 2487613 = 932855) (by norm_num)
theorem B3316817 : Blo 2181435 3316817 := bstep (se 2 (by rfl) ⟨1243806, by rfl⟩ : syracuseStep 3316817 = 2487613) B2487613
theorem B2211211 : Blo 2181435 2211211 := bstep (se 1 (by rfl) ⟨1658408, by rfl⟩ : syracuseStep 2211211 = 3316817) B3316817
theorem B2948281 : Blo 2181435 2948281 := bstep (se 2 (by rfl) ⟨1105605, by rfl⟩ : syracuseStep 2948281 = 2211211) B2211211
theorem B15724165 : Blo 2181435 15724165 := bstep (se 4 (by rfl) ⟨1474140, by rfl⟩ : syracuseStep 15724165 = 2948281) B2948281
theorem B20965553 : Blo 2181435 20965553 := bstep (se 2 (by rfl) ⟨7862082, by rfl⟩ : syracuseStep 20965553 = 15724165) B15724165
theorem B13977035 : Blo 2181435 13977035 := bstep (se 1 (by rfl) ⟨10482776, by rfl⟩ : syracuseStep 13977035 = 20965553) B20965553
theorem B9318023 : Blo 2181435 9318023 := bstep (se 1 (by rfl) ⟨6988517, by rfl⟩ : syracuseStep 9318023 = 13977035) B13977035
theorem B6212015 : Blo 2181435 6212015 := bstep (se 1 (by rfl) ⟨4659011, by rfl⟩ : syracuseStep 6212015 = 9318023) B9318023
theorem B4141343 : Blo 2181435 4141343 := bstep (se 1 (by rfl) ⟨3106007, by rfl⟩ : syracuseStep 4141343 = 6212015) B6212015
theorem B2760895 : Blo 2181435 2760895 := bstep (se 1 (by rfl) ⟨2070671, by rfl⟩ : syracuseStep 2760895 = 4141343) B4141343
theorem B3681193 : Blo 2181435 3681193 := bstep (se 2 (by rfl) ⟨1380447, by rfl⟩ : syracuseStep 3681193 = 2760895) B2760895
theorem B4908257 : Blo 2181435 4908257 := bstep (se 2 (by rfl) ⟨1840596, by rfl⟩ : syracuseStep 4908257 = 3681193) B3681193
theorem B3272171 : Blo 2181435 3272171 := bstep (se 1 (by rfl) ⟨2454128, by rfl⟩ : syracuseStep 3272171 = 4908257) B4908257
theorem B2181447 : Blo 2181435 2181447 := bstep (se 1 (by rfl) ⟨1636085, by rfl⟩ : syracuseStep 2181447 = 3272171) B3272171
theorem B2454133 : Blo 2181435 2454133 := bbase (se 5 (by rfl) ⟨115037, by rfl⟩ : syracuseStep 2454133 = 230075) (by norm_num)
theorem B3272177 : Blo 2181435 3272177 := bstep (se 2 (by rfl) ⟨1227066, by rfl⟩ : syracuseStep 3272177 = 2454133) B2454133
theorem B2181451 : Blo 2181435 2181451 := bstep (se 1 (by rfl) ⟨1636088, by rfl⟩ : syracuseStep 2181451 = 3272177) B3272177
theorem B2760905 : Blo 2181435 2760905 := bbase (se 2 (by rfl) ⟨1035339, by rfl⟩ : syracuseStep 2760905 = 2070679) (by norm_num)
theorem B7362413 : Blo 2181435 7362413 := bstep (se 3 (by rfl) ⟨1380452, by rfl⟩ : syracuseStep 7362413 = 2760905) B2760905
theorem B4908275 : Blo 2181435 4908275 := bstep (se 1 (by rfl) ⟨3681206, by rfl⟩ : syracuseStep 4908275 = 7362413) B7362413
theorem B3272183 : Blo 2181435 3272183 := bstep (se 1 (by rfl) ⟨2454137, by rfl⟩ : syracuseStep 3272183 = 4908275) B4908275
theorem B2181455 : Blo 2181435 2181455 := bstep (se 1 (by rfl) ⟨1636091, by rfl⟩ : syracuseStep 2181455 = 3272183) B3272183
theorem B3272189 : Blo 2181435 3272189 := bbase (se 3 (by rfl) ⟨613535, by rfl⟩ : syracuseStep 3272189 = 1227071) (by norm_num)
theorem B2181459 : Blo 2181435 2181459 := bstep (se 1 (by rfl) ⟨1636094, by rfl⟩ : syracuseStep 2181459 = 3272189) B3272189
theorem B4908293 : Blo 2181435 4908293 := bbase (se 4 (by rfl) ⟨460152, by rfl⟩ : syracuseStep 4908293 = 920305) (by norm_num)
theorem B3272195 : Blo 2181435 3272195 := bstep (se 1 (by rfl) ⟨2454146, by rfl⟩ : syracuseStep 3272195 = 4908293) B4908293
theorem B2181463 : Blo 2181435 2181463 := bstep (se 1 (by rfl) ⟨1636097, by rfl⟩ : syracuseStep 2181463 = 3272195) B3272195
theorem B4141381 : Blo 2181435 4141381 := bbase (se 4 (by rfl) ⟨388254, by rfl⟩ : syracuseStep 4141381 = 776509) (by norm_num)
theorem B5521841 : Blo 2181435 5521841 := bstep (se 2 (by rfl) ⟨2070690, by rfl⟩ : syracuseStep 5521841 = 4141381) B4141381
theorem B3681227 : Blo 2181435 3681227 := bstep (se 1 (by rfl) ⟨2760920, by rfl⟩ : syracuseStep 3681227 = 5521841) B5521841
theorem B2454151 : Blo 2181435 2454151 := bstep (se 1 (by rfl) ⟨1840613, by rfl⟩ : syracuseStep 2454151 = 3681227) B3681227
theorem B3272201 : Blo 2181435 3272201 := bstep (se 2 (by rfl) ⟨1227075, by rfl⟩ : syracuseStep 3272201 = 2454151) B2454151
theorem B2181467 : Blo 2181435 2181467 := bstep (se 1 (by rfl) ⟨1636100, by rfl⟩ : syracuseStep 2181467 = 3272201) B3272201
theorem B11043701 : Blo 2181435 11043701 := bbase (se 5 (by rfl) ⟨517673, by rfl⟩ : syracuseStep 11043701 = 1035347) (by norm_num)
theorem B7362467 : Blo 2181435 7362467 := bstep (se 1 (by rfl) ⟨5521850, by rfl⟩ : syracuseStep 7362467 = 11043701) B11043701
theorem B4908311 : Blo 2181435 4908311 := bstep (se 1 (by rfl) ⟨3681233, by rfl⟩ : syracuseStep 4908311 = 7362467) B7362467
theorem B3272207 : Blo 2181435 3272207 := bstep (se 1 (by rfl) ⟨2454155, by rfl⟩ : syracuseStep 3272207 = 4908311) B4908311
theorem B2181471 : Blo 2181435 2181471 := bstep (se 1 (by rfl) ⟨1636103, by rfl⟩ : syracuseStep 2181471 = 3272207) B3272207
theorem B3272213 : Blo 2181435 3272213 := bbase (se 6 (by rfl) ⟨76692, by rfl⟩ : syracuseStep 3272213 = 153385) (by norm_num)
theorem B2181475 : Blo 2181435 2181475 := bstep (se 1 (by rfl) ⟨1636106, by rfl⟩ : syracuseStep 2181475 = 3272213) B3272213
theorem B7862197 : Blo 2181435 7862197 := bbase (se 5 (by rfl) ⟨368540, by rfl⟩ : syracuseStep 7862197 = 737081) (by norm_num)
theorem B10482929 : Blo 2181435 10482929 := bstep (se 2 (by rfl) ⟨3931098, by rfl⟩ : syracuseStep 10482929 = 7862197) B7862197
theorem B6988619 : Blo 2181435 6988619 := bstep (se 1 (by rfl) ⟨5241464, by rfl⟩ : syracuseStep 6988619 = 10482929) B10482929
theorem B18636317 : Blo 2181435 18636317 := bstep (se 3 (by rfl) ⟨3494309, by rfl⟩ : syracuseStep 18636317 = 6988619) B6988619
theorem B12424211 : Blo 2181435 12424211 := bstep (se 1 (by rfl) ⟨9318158, by rfl⟩ : syracuseStep 12424211 = 18636317) B18636317
theorem B8282807 : Blo 2181435 8282807 := bstep (se 1 (by rfl) ⟨6212105, by rfl⟩ : syracuseStep 8282807 = 12424211) B12424211
theorem B5521871 : Blo 2181435 5521871 := bstep (se 1 (by rfl) ⟨4141403, by rfl⟩ : syracuseStep 5521871 = 8282807) B8282807
theorem B3681247 : Blo 2181435 3681247 := bstep (se 1 (by rfl) ⟨2760935, by rfl⟩ : syracuseStep 3681247 = 5521871) B5521871
theorem B4908329 : Blo 2181435 4908329 := bstep (se 2 (by rfl) ⟨1840623, by rfl⟩ : syracuseStep 4908329 = 3681247) B3681247
theorem B3272219 : Blo 2181435 3272219 := bstep (se 1 (by rfl) ⟨2454164, by rfl⟩ : syracuseStep 3272219 = 4908329) B4908329
theorem B2181479 : Blo 2181435 2181479 := bstep (se 1 (by rfl) ⟨1636109, by rfl⟩ : syracuseStep 2181479 = 3272219) B3272219
theorem B2454169 : Blo 2181435 2454169 := bbase (se 2 (by rfl) ⟨920313, by rfl⟩ : syracuseStep 2454169 = 1840627) (by norm_num)
theorem B3272225 : Blo 2181435 3272225 := bstep (se 2 (by rfl) ⟨1227084, by rfl⟩ : syracuseStep 3272225 = 2454169) B2454169
theorem B2181483 : Blo 2181435 2181483 := bstep (se 1 (by rfl) ⟨1636112, by rfl⟩ : syracuseStep 2181483 = 3272225) B3272225
theorem B8282837 : Blo 2181435 8282837 := bbase (se 7 (by rfl) ⟨97064, by rfl⟩ : syracuseStep 8282837 = 194129) (by norm_num)
theorem B5521891 : Blo 2181435 5521891 := bstep (se 1 (by rfl) ⟨4141418, by rfl⟩ : syracuseStep 5521891 = 8282837) B8282837
theorem B7362521 : Blo 2181435 7362521 := bstep (se 2 (by rfl) ⟨2760945, by rfl⟩ : syracuseStep 7362521 = 5521891) B5521891
theorem B4908347 : Blo 2181435 4908347 := bstep (se 1 (by rfl) ⟨3681260, by rfl⟩ : syracuseStep 4908347 = 7362521) B7362521
theorem B3272231 : Blo 2181435 3272231 := bstep (se 1 (by rfl) ⟨2454173, by rfl⟩ : syracuseStep 3272231 = 4908347) B4908347
theorem B2181487 : Blo 2181435 2181487 := bstep (se 1 (by rfl) ⟨1636115, by rfl⟩ : syracuseStep 2181487 = 3272231) B3272231
theorem B3272237 : Blo 2181435 3272237 := bbase (se 3 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 3272237 = 1227089) (by norm_num)
theorem B2181491 : Blo 2181435 2181491 := bstep (se 1 (by rfl) ⟨1636118, by rfl⟩ : syracuseStep 2181491 = 3272237) B3272237
theorem B4908365 : Blo 2181435 4908365 := bbase (se 3 (by rfl) ⟨920318, by rfl⟩ : syracuseStep 4908365 = 1840637) (by norm_num)
theorem B3272243 : Blo 2181435 3272243 := bstep (se 1 (by rfl) ⟨2454182, by rfl⟩ : syracuseStep 3272243 = 4908365) B4908365
theorem B2181495 : Blo 2181435 2181495 := bstep (se 1 (by rfl) ⟨1636121, by rfl⟩ : syracuseStep 2181495 = 3272243) B3272243
theorem B2760961 : Blo 2181435 2760961 := bbase (se 2 (by rfl) ⟨1035360, by rfl⟩ : syracuseStep 2760961 = 2070721) (by norm_num)
theorem B3681281 : Blo 2181435 3681281 := bstep (se 2 (by rfl) ⟨1380480, by rfl⟩ : syracuseStep 3681281 = 2760961) B2760961
theorem B2454187 : Blo 2181435 2454187 := bstep (se 1 (by rfl) ⟨1840640, by rfl⟩ : syracuseStep 2454187 = 3681281) B3681281
theorem B3272249 : Blo 2181435 3272249 := bstep (se 2 (by rfl) ⟨1227093, by rfl⟩ : syracuseStep 3272249 = 2454187) B2454187
theorem B2181499 : Blo 2181435 2181499 := bstep (se 1 (by rfl) ⟨1636124, by rfl⟩ : syracuseStep 2181499 = 3272249) B3272249
theorem B2329565 : Blo 2181435 2329565 := bbase (se 3 (by rfl) ⟨436793, by rfl⟩ : syracuseStep 2329565 = 873587) (by norm_num)
theorem B24848693 : Blo 2181435 24848693 := bstep (se 5 (by rfl) ⟨1164782, by rfl⟩ : syracuseStep 24848693 = 2329565) B2329565
theorem B16565795 : Blo 2181435 16565795 := bstep (se 1 (by rfl) ⟨12424346, by rfl⟩ : syracuseStep 16565795 = 24848693) B24848693
theorem B11043863 : Blo 2181435 11043863 := bstep (se 1 (by rfl) ⟨8282897, by rfl⟩ : syracuseStep 11043863 = 16565795) B16565795
theorem B7362575 : Blo 2181435 7362575 := bstep (se 1 (by rfl) ⟨5521931, by rfl⟩ : syracuseStep 7362575 = 11043863) B11043863
theorem B4908383 : Blo 2181435 4908383 := bstep (se 1 (by rfl) ⟨3681287, by rfl⟩ : syracuseStep 4908383 = 7362575) B7362575
theorem B3272255 : Blo 2181435 3272255 := bstep (se 1 (by rfl) ⟨2454191, by rfl⟩ : syracuseStep 3272255 = 4908383) B4908383
theorem B2181503 : Blo 2181435 2181503 := bstep (se 1 (by rfl) ⟨1636127, by rfl⟩ : syracuseStep 2181503 = 3272255) B3272255
theorem B3272261 : Blo 2181435 3272261 := bbase (se 4 (by rfl) ⟨306774, by rfl⟩ : syracuseStep 3272261 = 613549) (by norm_num)
theorem B2181507 : Blo 2181435 2181507 := bstep (se 1 (by rfl) ⟨1636130, by rfl⟩ : syracuseStep 2181507 = 3272261) B3272261
theorem B3681301 : Blo 2181435 3681301 := bbase (se 6 (by rfl) ⟨86280, by rfl⟩ : syracuseStep 3681301 = 172561) (by norm_num)
theorem B4908401 : Blo 2181435 4908401 := bstep (se 2 (by rfl) ⟨1840650, by rfl⟩ : syracuseStep 4908401 = 3681301) B3681301
theorem B3272267 : Blo 2181435 3272267 := bstep (se 1 (by rfl) ⟨2454200, by rfl⟩ : syracuseStep 3272267 = 4908401) B4908401
theorem B2181511 : Blo 2181435 2181511 := bstep (se 1 (by rfl) ⟨1636133, by rfl⟩ : syracuseStep 2181511 = 3272267) B3272267
theorem B2454205 : Blo 2181435 2454205 := bbase (se 3 (by rfl) ⟨460163, by rfl⟩ : syracuseStep 2454205 = 920327) (by norm_num)
theorem B3272273 : Blo 2181435 3272273 := bstep (se 2 (by rfl) ⟨1227102, by rfl⟩ : syracuseStep 3272273 = 2454205) B2454205
theorem B2181515 : Blo 2181435 2181515 := bstep (se 1 (by rfl) ⟨1636136, by rfl⟩ : syracuseStep 2181515 = 3272273) B3272273
theorem B7362629 : Blo 2181435 7362629 := bbase (se 4 (by rfl) ⟨690246, by rfl⟩ : syracuseStep 7362629 = 1380493) (by norm_num)
theorem B4908419 : Blo 2181435 4908419 := bstep (se 1 (by rfl) ⟨3681314, by rfl⟩ : syracuseStep 4908419 = 7362629) B7362629
theorem B3272279 : Blo 2181435 3272279 := bstep (se 1 (by rfl) ⟨2454209, by rfl⟩ : syracuseStep 3272279 = 4908419) B4908419
theorem B2181519 : Blo 2181435 2181519 := bstep (se 1 (by rfl) ⟨1636139, by rfl⟩ : syracuseStep 2181519 = 3272279) B3272279
theorem B3272285 : Blo 2181435 3272285 := bbase (se 3 (by rfl) ⟨613553, by rfl⟩ : syracuseStep 3272285 = 1227107) (by norm_num)
theorem B2181523 : Blo 2181435 2181523 := bstep (se 1 (by rfl) ⟨1636142, by rfl⟩ : syracuseStep 2181523 = 3272285) B3272285
theorem B4908437 : Blo 2181435 4908437 := bbase (se 6 (by rfl) ⟨115041, by rfl⟩ : syracuseStep 4908437 = 230083) (by norm_num)
theorem B3272291 : Blo 2181435 3272291 := bstep (se 1 (by rfl) ⟨2454218, by rfl⟩ : syracuseStep 3272291 = 4908437) B4908437
theorem B2181527 : Blo 2181435 2181527 := bstep (se 1 (by rfl) ⟨1636145, by rfl⟩ : syracuseStep 2181527 = 3272291) B3272291
theorem B2487709 : Blo 2181435 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B3316945 : Blo 2181435 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B4422593 : Blo 2181435 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2948395 : Blo 2181435 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B3931193 : Blo 2181435 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B10483181 : Blo 2181435 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B6988787 : Blo 2181435 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B4659191 : Blo 2181435 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B3106127 : Blo 2181435 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B8283005 : Blo 2181435 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B5522003 : Blo 2181435 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B3681335 : Blo 2181435 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B2454223 : Blo 2181435 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B3272297 : Blo 2181435 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B2181531 : Blo 2181435 2181531 := bstep (se 1 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 2181531 = 3272297) B3272297
theorem B31878677 : Blo 2181435 31878677 := bbase (se 6 (by rfl) ⟨747156, by rfl⟩ : syracuseStep 31878677 = 1494313) (by norm_num)
theorem B21252451 : Blo 2181435 21252451 := bstep (se 1 (by rfl) ⟨15939338, by rfl⟩ : syracuseStep 21252451 = 31878677) B31878677
theorem B28336601 : Blo 2181435 28336601 := bstep (se 2 (by rfl) ⟨10626225, by rfl⟩ : syracuseStep 28336601 = 21252451) B21252451
theorem B18891067 : Blo 2181435 18891067 := bstep (se 1 (by rfl) ⟨14168300, by rfl⟩ : syracuseStep 18891067 = 28336601) B28336601
theorem B25188089 : Blo 2181435 25188089 := bstep (se 2 (by rfl) ⟨9445533, by rfl⟩ : syracuseStep 25188089 = 18891067) B18891067
theorem B67168237 : Blo 2181435 67168237 := bstep (se 3 (by rfl) ⟨12594044, by rfl⟩ : syracuseStep 67168237 = 25188089) B25188089
theorem B89557649 : Blo 2181435 89557649 := bstep (se 2 (by rfl) ⟨33584118, by rfl⟩ : syracuseStep 89557649 = 67168237) B67168237
theorem B59705099 : Blo 2181435 59705099 := bstep (se 1 (by rfl) ⟨44778824, by rfl⟩ : syracuseStep 59705099 = 89557649) B89557649
theorem B39803399 : Blo 2181435 39803399 := bstep (se 1 (by rfl) ⟨29852549, by rfl⟩ : syracuseStep 39803399 = 59705099) B59705099
theorem B26535599 : Blo 2181435 26535599 := bstep (se 1 (by rfl) ⟨19901699, by rfl⟩ : syracuseStep 26535599 = 39803399) B39803399
theorem B17690399 : Blo 2181435 17690399 := bstep (se 1 (by rfl) ⟨13267799, by rfl⟩ : syracuseStep 17690399 = 26535599) B26535599
theorem B11793599 : Blo 2181435 11793599 := bstep (se 1 (by rfl) ⟨8845199, by rfl⟩ : syracuseStep 11793599 = 17690399) B17690399
theorem B7862399 : Blo 2181435 7862399 := bstep (se 1 (by rfl) ⟨5896799, by rfl⟩ : syracuseStep 7862399 = 11793599) B11793599
theorem B5241599 : Blo 2181435 5241599 := bstep (se 1 (by rfl) ⟨3931199, by rfl⟩ : syracuseStep 5241599 = 7862399) B7862399
theorem B3494399 : Blo 2181435 3494399 := bstep (se 1 (by rfl) ⟨2620799, by rfl⟩ : syracuseStep 3494399 = 5241599) B5241599
theorem B9318397 : Blo 2181435 9318397 := bstep (se 3 (by rfl) ⟨1747199, by rfl⟩ : syracuseStep 9318397 = 3494399) B3494399
theorem B12424529 : Blo 2181435 12424529 := bstep (se 2 (by rfl) ⟨4659198, by rfl⟩ : syracuseStep 12424529 = 9318397) B9318397
theorem B8283019 : Blo 2181435 8283019 := bstep (se 1 (by rfl) ⟨6212264, by rfl⟩ : syracuseStep 8283019 = 12424529) B12424529
theorem B11044025 : Blo 2181435 11044025 := bstep (se 2 (by rfl) ⟨4141509, by rfl⟩ : syracuseStep 11044025 = 8283019) B8283019
theorem B7362683 : Blo 2181435 7362683 := bstep (se 1 (by rfl) ⟨5522012, by rfl⟩ : syracuseStep 7362683 = 11044025) B11044025
theorem B4908455 : Blo 2181435 4908455 := bstep (se 1 (by rfl) ⟨3681341, by rfl⟩ : syracuseStep 4908455 = 7362683) B7362683
theorem B3272303 : Blo 2181435 3272303 := bstep (se 1 (by rfl) ⟨2454227, by rfl⟩ : syracuseStep 3272303 = 4908455) B4908455
theorem B2181535 : Blo 2181435 2181535 := bstep (se 1 (by rfl) ⟨1636151, by rfl⟩ : syracuseStep 2181535 = 3272303) B3272303
theorem B3272309 : Blo 2181435 3272309 := bbase (se 5 (by rfl) ⟨153389, by rfl⟩ : syracuseStep 3272309 = 306779) (by norm_num)
theorem B2181539 : Blo 2181435 2181539 := bstep (se 1 (by rfl) ⟨1636154, by rfl⟩ : syracuseStep 2181539 = 3272309) B3272309
theorem B4141525 : Blo 2181435 4141525 := bbase (se 7 (by rfl) ⟨48533, by rfl⟩ : syracuseStep 4141525 = 97067) (by norm_num)
theorem B5522033 : Blo 2181435 5522033 := bstep (se 2 (by rfl) ⟨2070762, by rfl⟩ : syracuseStep 5522033 = 4141525) B4141525
theorem B3681355 : Blo 2181435 3681355 := bstep (se 1 (by rfl) ⟨2761016, by rfl⟩ : syracuseStep 3681355 = 5522033) B5522033
theorem B4908473 : Blo 2181435 4908473 := bstep (se 2 (by rfl) ⟨1840677, by rfl⟩ : syracuseStep 4908473 = 3681355) B3681355
theorem B3272315 : Blo 2181435 3272315 := bstep (se 1 (by rfl) ⟨2454236, by rfl⟩ : syracuseStep 3272315 = 4908473) B4908473
theorem B2181543 : Blo 2181435 2181543 := bstep (se 1 (by rfl) ⟨1636157, by rfl⟩ : syracuseStep 2181543 = 3272315) B3272315
theorem B2454241 : Blo 2181435 2454241 := bbase (se 2 (by rfl) ⟨920340, by rfl⟩ : syracuseStep 2454241 = 1840681) (by norm_num)
theorem B3272321 : Blo 2181435 3272321 := bstep (se 2 (by rfl) ⟨1227120, by rfl⟩ : syracuseStep 3272321 = 2454241) B2454241
theorem B2181547 : Blo 2181435 2181547 := bstep (se 1 (by rfl) ⟨1636160, by rfl⟩ : syracuseStep 2181547 = 3272321) B3272321
theorem B5522053 : Blo 2181435 5522053 := bbase (se 4 (by rfl) ⟨517692, by rfl⟩ : syracuseStep 5522053 = 1035385) (by norm_num)
theorem B7362737 : Blo 2181435 7362737 := bstep (se 2 (by rfl) ⟨2761026, by rfl⟩ : syracuseStep 7362737 = 5522053) B5522053
theorem B4908491 : Blo 2181435 4908491 := bstep (se 1 (by rfl) ⟨3681368, by rfl⟩ : syracuseStep 4908491 = 7362737) B7362737
theorem B3272327 : Blo 2181435 3272327 := bstep (se 1 (by rfl) ⟨2454245, by rfl⟩ : syracuseStep 3272327 = 4908491) B4908491
theorem B2181551 : Blo 2181435 2181551 := bstep (se 1 (by rfl) ⟨1636163, by rfl⟩ : syracuseStep 2181551 = 3272327) B3272327
theorem B3272333 : Blo 2181435 3272333 := bbase (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) (by norm_num)
theorem B2181555 : Blo 2181435 2181555 := bstep (se 1 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 2181555 = 3272333) B3272333
theorem B4908509 : Blo 2181435 4908509 := bbase (se 3 (by rfl) ⟨920345, by rfl⟩ : syracuseStep 4908509 = 1840691) (by norm_num)
theorem B3272339 : Blo 2181435 3272339 := bstep (se 1 (by rfl) ⟨2454254, by rfl⟩ : syracuseStep 3272339 = 4908509) B4908509
theorem B2181559 : Blo 2181435 2181559 := bstep (se 1 (by rfl) ⟨1636169, by rfl⟩ : syracuseStep 2181559 = 3272339) B3272339
theorem B3681389 : Blo 2181435 3681389 := bbase (se 3 (by rfl) ⟨690260, by rfl⟩ : syracuseStep 3681389 = 1380521) (by norm_num)
theorem B2454259 : Blo 2181435 2454259 := bstep (se 1 (by rfl) ⟨1840694, by rfl⟩ : syracuseStep 2454259 = 3681389) B3681389
theorem B3272345 : Blo 2181435 3272345 := bstep (se 2 (by rfl) ⟨1227129, by rfl⟩ : syracuseStep 3272345 = 2454259) B2454259
theorem B2181563 : Blo 2181435 2181563 := bstep (se 1 (by rfl) ⟨1636172, by rfl⟩ : syracuseStep 2181563 = 3272345) B3272345
theorem B5896885 : Blo 2181435 5896885 := bbase (se 5 (by rfl) ⟨276416, by rfl⟩ : syracuseStep 5896885 = 552833) (by norm_num)
theorem B7862513 : Blo 2181435 7862513 := bstep (se 2 (by rfl) ⟨2948442, by rfl⟩ : syracuseStep 7862513 = 5896885) B5896885
theorem B20966701 : Blo 2181435 20966701 := bstep (se 3 (by rfl) ⟨3931256, by rfl⟩ : syracuseStep 20966701 = 7862513) B7862513
theorem B27955601 : Blo 2181435 27955601 := bstep (se 2 (by rfl) ⟨10483350, by rfl⟩ : syracuseStep 27955601 = 20966701) B20966701
theorem B18637067 : Blo 2181435 18637067 := bstep (se 1 (by rfl) ⟨13977800, by rfl⟩ : syracuseStep 18637067 = 27955601) B27955601
theorem B12424711 : Blo 2181435 12424711 := bstep (se 1 (by rfl) ⟨9318533, by rfl⟩ : syracuseStep 12424711 = 18637067) B18637067
theorem B16566281 : Blo 2181435 16566281 := bstep (se 2 (by rfl) ⟨6212355, by rfl⟩ : syracuseStep 16566281 = 12424711) B12424711
theorem B11044187 : Blo 2181435 11044187 := bstep (se 1 (by rfl) ⟨8283140, by rfl⟩ : syracuseStep 11044187 = 16566281) B16566281
theorem B7362791 : Blo 2181435 7362791 := bstep (se 1 (by rfl) ⟨5522093, by rfl⟩ : syracuseStep 7362791 = 11044187) B11044187
theorem B4908527 : Blo 2181435 4908527 := bstep (se 1 (by rfl) ⟨3681395, by rfl⟩ : syracuseStep 4908527 = 7362791) B7362791
theorem B3272351 : Blo 2181435 3272351 := bstep (se 1 (by rfl) ⟨2454263, by rfl⟩ : syracuseStep 3272351 = 4908527) B4908527
theorem B2181567 : Blo 2181435 2181567 := bstep (se 1 (by rfl) ⟨1636175, by rfl⟩ : syracuseStep 2181567 = 3272351) B3272351
theorem B3272357 : Blo 2181435 3272357 := bbase (se 4 (by rfl) ⟨306783, by rfl⟩ : syracuseStep 3272357 = 613567) (by norm_num)
theorem B2181571 : Blo 2181435 2181571 := bstep (se 1 (by rfl) ⟨1636178, by rfl⟩ : syracuseStep 2181571 = 3272357) B3272357
theorem B2761057 : Blo 2181435 2761057 := bbase (se 2 (by rfl) ⟨1035396, by rfl⟩ : syracuseStep 2761057 = 2070793) (by norm_num)
theorem B3681409 : Blo 2181435 3681409 := bstep (se 2 (by rfl) ⟨1380528, by rfl⟩ : syracuseStep 3681409 = 2761057) B2761057
theorem B4908545 : Blo 2181435 4908545 := bstep (se 2 (by rfl) ⟨1840704, by rfl⟩ : syracuseStep 4908545 = 3681409) B3681409
theorem B3272363 : Blo 2181435 3272363 := bstep (se 1 (by rfl) ⟨2454272, by rfl⟩ : syracuseStep 3272363 = 4908545) B4908545
theorem B2181575 : Blo 2181435 2181575 := bstep (se 1 (by rfl) ⟨1636181, by rfl⟩ : syracuseStep 2181575 = 3272363) B3272363
theorem B2454277 : Blo 2181435 2454277 := bbase (se 4 (by rfl) ⟨230088, by rfl⟩ : syracuseStep 2454277 = 460177) (by norm_num)
theorem B3272369 : Blo 2181435 3272369 := bstep (se 2 (by rfl) ⟨1227138, by rfl⟩ : syracuseStep 3272369 = 2454277) B2454277
theorem B2181579 : Blo 2181435 2181579 := bstep (se 1 (by rfl) ⟨1636184, by rfl⟩ : syracuseStep 2181579 = 3272369) B3272369
theorem B3494477 : Blo 2181435 3494477 := bbase (se 3 (by rfl) ⟨655214, by rfl⟩ : syracuseStep 3494477 = 1310429) (by norm_num)
theorem B2329651 : Blo 2181435 2329651 := bstep (se 1 (by rfl) ⟨1747238, by rfl⟩ : syracuseStep 2329651 = 3494477) B3494477
theorem B3106201 : Blo 2181435 3106201 := bstep (se 2 (by rfl) ⟨1164825, by rfl⟩ : syracuseStep 3106201 = 2329651) B2329651
theorem B4141601 : Blo 2181435 4141601 := bstep (se 2 (by rfl) ⟨1553100, by rfl⟩ : syracuseStep 4141601 = 3106201) B3106201
theorem B2761067 : Blo 2181435 2761067 := bstep (se 1 (by rfl) ⟨2070800, by rfl⟩ : syracuseStep 2761067 = 4141601) B4141601
theorem B7362845 : Blo 2181435 7362845 := bstep (se 3 (by rfl) ⟨1380533, by rfl⟩ : syracuseStep 7362845 = 2761067) B2761067
theorem B4908563 : Blo 2181435 4908563 := bstep (se 1 (by rfl) ⟨3681422, by rfl⟩ : syracuseStep 4908563 = 7362845) B7362845
theorem B3272375 : Blo 2181435 3272375 := bstep (se 1 (by rfl) ⟨2454281, by rfl⟩ : syracuseStep 3272375 = 4908563) B4908563
theorem B2181583 : Blo 2181435 2181583 := bstep (se 1 (by rfl) ⟨1636187, by rfl⟩ : syracuseStep 2181583 = 3272375) B3272375
theorem B3272381 : Blo 2181435 3272381 := bbase (se 3 (by rfl) ⟨613571, by rfl⟩ : syracuseStep 3272381 = 1227143) (by norm_num)
theorem B2181587 : Blo 2181435 2181587 := bstep (se 1 (by rfl) ⟨1636190, by rfl⟩ : syracuseStep 2181587 = 3272381) B3272381
theorem B4908581 : Blo 2181435 4908581 := bbase (se 4 (by rfl) ⟨460179, by rfl⟩ : syracuseStep 4908581 = 920359) (by norm_num)
theorem B3272387 : Blo 2181435 3272387 := bstep (se 1 (by rfl) ⟨2454290, by rfl⟩ : syracuseStep 3272387 = 4908581) B4908581
theorem B2181591 : Blo 2181435 2181591 := bstep (se 1 (by rfl) ⟨1636193, by rfl⟩ : syracuseStep 2181591 = 3272387) B3272387
theorem B5522165 : Blo 2181435 5522165 := bbase (se 5 (by rfl) ⟨258851, by rfl⟩ : syracuseStep 5522165 = 517703) (by norm_num)
theorem B3681443 : Blo 2181435 3681443 := bstep (se 1 (by rfl) ⟨2761082, by rfl⟩ : syracuseStep 3681443 = 5522165) B5522165
theorem B2454295 : Blo 2181435 2454295 := bstep (se 1 (by rfl) ⟨1840721, by rfl⟩ : syracuseStep 2454295 = 3681443) B3681443
theorem B3272393 : Blo 2181435 3272393 := bstep (se 2 (by rfl) ⟨1227147, by rfl⟩ : syracuseStep 3272393 = 2454295) B2454295
theorem B2181595 : Blo 2181435 2181595 := bstep (se 1 (by rfl) ⟨1636196, by rfl⟩ : syracuseStep 2181595 = 3272393) B3272393
theorem B31450517 : Blo 2181435 31450517 := bbase (se 6 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 31450517 = 1474243) (by norm_num)
theorem B20967011 : Blo 2181435 20967011 := bstep (se 1 (by rfl) ⟨15725258, by rfl⟩ : syracuseStep 20967011 = 31450517) B31450517
theorem B13978007 : Blo 2181435 13978007 := bstep (se 1 (by rfl) ⟨10483505, by rfl⟩ : syracuseStep 13978007 = 20967011) B20967011
theorem B9318671 : Blo 2181435 9318671 := bstep (se 1 (by rfl) ⟨6989003, by rfl⟩ : syracuseStep 9318671 = 13978007) B13978007
theorem B6212447 : Blo 2181435 6212447 := bstep (se 1 (by rfl) ⟨4659335, by rfl⟩ : syracuseStep 6212447 = 9318671) B9318671
theorem B4141631 : Blo 2181435 4141631 := bstep (se 1 (by rfl) ⟨3106223, by rfl⟩ : syracuseStep 4141631 = 6212447) B6212447
theorem B11044349 : Blo 2181435 11044349 := bstep (se 3 (by rfl) ⟨2070815, by rfl⟩ : syracuseStep 11044349 = 4141631) B4141631
theorem B7362899 : Blo 2181435 7362899 := bstep (se 1 (by rfl) ⟨5522174, by rfl⟩ : syracuseStep 7362899 = 11044349) B11044349
theorem B4908599 : Blo 2181435 4908599 := bstep (se 1 (by rfl) ⟨3681449, by rfl⟩ : syracuseStep 4908599 = 7362899) B7362899
theorem B3272399 : Blo 2181435 3272399 := bstep (se 1 (by rfl) ⟨2454299, by rfl⟩ : syracuseStep 3272399 = 4908599) B4908599
theorem B2181599 : Blo 2181435 2181599 := bstep (se 1 (by rfl) ⟨1636199, by rfl⟩ : syracuseStep 2181599 = 3272399) B3272399
theorem B3272405 : Blo 2181435 3272405 := bbase (se 7 (by rfl) ⟨38348, by rfl⟩ : syracuseStep 3272405 = 76697) (by norm_num)
theorem B2181603 : Blo 2181435 2181603 := bstep (se 1 (by rfl) ⟨1636202, by rfl⟩ : syracuseStep 2181603 = 3272405) B3272405
theorem B5241773 : Blo 2181435 5241773 := bbase (se 3 (by rfl) ⟨982832, by rfl⟩ : syracuseStep 5241773 = 1965665) (by norm_num)
theorem B3494515 : Blo 2181435 3494515 := bstep (se 1 (by rfl) ⟨2620886, by rfl⟩ : syracuseStep 3494515 = 5241773) B5241773
theorem B4659353 : Blo 2181435 4659353 := bstep (se 2 (by rfl) ⟨1747257, by rfl⟩ : syracuseStep 4659353 = 3494515) B3494515
theorem B3106235 : Blo 2181435 3106235 := bstep (se 1 (by rfl) ⟨2329676, by rfl⟩ : syracuseStep 3106235 = 4659353) B4659353
theorem B8283293 : Blo 2181435 8283293 := bstep (se 3 (by rfl) ⟨1553117, by rfl⟩ : syracuseStep 8283293 = 3106235) B3106235
theorem B5522195 : Blo 2181435 5522195 := bstep (se 1 (by rfl) ⟨4141646, by rfl⟩ : syracuseStep 5522195 = 8283293) B8283293
theorem B3681463 : Blo 2181435 3681463 := bstep (se 1 (by rfl) ⟨2761097, by rfl⟩ : syracuseStep 3681463 = 5522195) B5522195
theorem B4908617 : Blo 2181435 4908617 := bstep (se 2 (by rfl) ⟨1840731, by rfl⟩ : syracuseStep 4908617 = 3681463) B3681463
theorem B3272411 : Blo 2181435 3272411 := bstep (se 1 (by rfl) ⟨2454308, by rfl⟩ : syracuseStep 3272411 = 4908617) B4908617
theorem B2181607 : Blo 2181435 2181607 := bstep (se 1 (by rfl) ⟨1636205, by rfl⟩ : syracuseStep 2181607 = 3272411) B3272411
theorem B2454313 : Blo 2181435 2454313 := bbase (se 2 (by rfl) ⟨920367, by rfl⟩ : syracuseStep 2454313 = 1840735) (by norm_num)
theorem B3272417 : Blo 2181435 3272417 := bstep (se 2 (by rfl) ⟨1227156, by rfl⟩ : syracuseStep 3272417 = 2454313) B2454313
theorem B2181611 : Blo 2181435 2181611 := bstep (se 1 (by rfl) ⟨1636208, by rfl⟩ : syracuseStep 2181611 = 3272417) B3272417
theorem B6297253 : Blo 2181435 6297253 := bbase (se 4 (by rfl) ⟨590367, by rfl⟩ : syracuseStep 6297253 = 1180735) (by norm_num)
theorem B33585349 : Blo 2181435 33585349 := bstep (se 4 (by rfl) ⟨3148626, by rfl⟩ : syracuseStep 33585349 = 6297253) B6297253
theorem B44780465 : Blo 2181435 44780465 := bstep (se 2 (by rfl) ⟨16792674, by rfl⟩ : syracuseStep 44780465 = 33585349) B33585349
theorem B29853643 : Blo 2181435 29853643 := bstep (se 1 (by rfl) ⟨22390232, by rfl⟩ : syracuseStep 29853643 = 44780465) B44780465
theorem B39804857 : Blo 2181435 39804857 := bstep (se 2 (by rfl) ⟨14926821, by rfl⟩ : syracuseStep 39804857 = 29853643) B29853643
theorem B26536571 : Blo 2181435 26536571 := bstep (se 1 (by rfl) ⟨19902428, by rfl⟩ : syracuseStep 26536571 = 39804857) B39804857
theorem B17691047 : Blo 2181435 17691047 := bstep (se 1 (by rfl) ⟨13268285, by rfl⟩ : syracuseStep 17691047 = 26536571) B26536571
theorem B11794031 : Blo 2181435 11794031 := bstep (se 1 (by rfl) ⟨8845523, by rfl⟩ : syracuseStep 11794031 = 17691047) B17691047
theorem B7862687 : Blo 2181435 7862687 := bstep (se 1 (by rfl) ⟨5897015, by rfl⟩ : syracuseStep 7862687 = 11794031) B11794031
theorem B5241791 : Blo 2181435 5241791 := bstep (se 1 (by rfl) ⟨3931343, by rfl⟩ : syracuseStep 5241791 = 7862687) B7862687
theorem B13978109 : Blo 2181435 13978109 := bstep (se 3 (by rfl) ⟨2620895, by rfl⟩ : syracuseStep 13978109 = 5241791) B5241791
theorem B9318739 : Blo 2181435 9318739 := bstep (se 1 (by rfl) ⟨6989054, by rfl⟩ : syracuseStep 9318739 = 13978109) B13978109
theorem B12424985 : Blo 2181435 12424985 := bstep (se 2 (by rfl) ⟨4659369, by rfl⟩ : syracuseStep 12424985 = 9318739) B9318739
theorem B8283323 : Blo 2181435 8283323 := bstep (se 1 (by rfl) ⟨6212492, by rfl⟩ : syracuseStep 8283323 = 12424985) B12424985
theorem B5522215 : Blo 2181435 5522215 := bstep (se 1 (by rfl) ⟨4141661, by rfl⟩ : syracuseStep 5522215 = 8283323) B8283323
theorem B7362953 : Blo 2181435 7362953 := bstep (se 2 (by rfl) ⟨2761107, by rfl⟩ : syracuseStep 7362953 = 5522215) B5522215
theorem B4908635 : Blo 2181435 4908635 := bstep (se 1 (by rfl) ⟨3681476, by rfl⟩ : syracuseStep 4908635 = 7362953) B7362953
theorem B3272423 : Blo 2181435 3272423 := bstep (se 1 (by rfl) ⟨2454317, by rfl⟩ : syracuseStep 3272423 = 4908635) B4908635
theorem B2181615 : Blo 2181435 2181615 := bstep (se 1 (by rfl) ⟨1636211, by rfl⟩ : syracuseStep 2181615 = 3272423) B3272423
theorem B3272429 : Blo 2181435 3272429 := bbase (se 3 (by rfl) ⟨613580, by rfl⟩ : syracuseStep 3272429 = 1227161) (by norm_num)
theorem B2181619 : Blo 2181435 2181619 := bstep (se 1 (by rfl) ⟨1636214, by rfl⟩ : syracuseStep 2181619 = 3272429) B3272429
theorem B4908653 : Blo 2181435 4908653 := bbase (se 3 (by rfl) ⟨920372, by rfl⟩ : syracuseStep 4908653 = 1840745) (by norm_num)
theorem B3272435 : Blo 2181435 3272435 := bstep (se 1 (by rfl) ⟨2454326, by rfl⟩ : syracuseStep 3272435 = 4908653) B4908653
theorem B2181623 : Blo 2181435 2181623 := bstep (se 1 (by rfl) ⟨1636217, by rfl⟩ : syracuseStep 2181623 = 3272435) B3272435
theorem B4141685 : Blo 2181435 4141685 := bbase (se 5 (by rfl) ⟨194141, by rfl⟩ : syracuseStep 4141685 = 388283) (by norm_num)
theorem B2761123 : Blo 2181435 2761123 := bstep (se 1 (by rfl) ⟨2070842, by rfl⟩ : syracuseStep 2761123 = 4141685) B4141685
theorem B3681497 : Blo 2181435 3681497 := bstep (se 2 (by rfl) ⟨1380561, by rfl⟩ : syracuseStep 3681497 = 2761123) B2761123
theorem B2454331 : Blo 2181435 2454331 := bstep (se 1 (by rfl) ⟨1840748, by rfl⟩ : syracuseStep 2454331 = 3681497) B3681497
theorem B3272441 : Blo 2181435 3272441 := bstep (se 2 (by rfl) ⟨1227165, by rfl⟩ : syracuseStep 3272441 = 2454331) B2454331
theorem B2181627 : Blo 2181435 2181627 := bstep (se 1 (by rfl) ⟨1636220, by rfl⟩ : syracuseStep 2181627 = 3272441) B3272441
theorem B18891893 : Blo 2181435 18891893 := bbase (se 5 (by rfl) ⟨885557, by rfl⟩ : syracuseStep 18891893 = 1771115) (by norm_num)
theorem B50378381 : Blo 2181435 50378381 := bstep (se 3 (by rfl) ⟨9445946, by rfl⟩ : syracuseStep 50378381 = 18891893) B18891893
theorem B33585587 : Blo 2181435 33585587 := bstep (se 1 (by rfl) ⟨25189190, by rfl⟩ : syracuseStep 33585587 = 50378381) B50378381
theorem B22390391 : Blo 2181435 22390391 := bstep (se 1 (by rfl) ⟨16792793, by rfl⟩ : syracuseStep 22390391 = 33585587) B33585587
theorem B59707709 : Blo 2181435 59707709 := bstep (se 3 (by rfl) ⟨11195195, by rfl⟩ : syracuseStep 59707709 = 22390391) B22390391
theorem B39805139 : Blo 2181435 39805139 := bstep (se 1 (by rfl) ⟨29853854, by rfl⟩ : syracuseStep 39805139 = 59707709) B59707709
theorem B106147037 : Blo 2181435 106147037 := bstep (se 3 (by rfl) ⟨19902569, by rfl⟩ : syracuseStep 106147037 = 39805139) B39805139
theorem B70764691 : Blo 2181435 70764691 := bstep (se 1 (by rfl) ⟨53073518, by rfl⟩ : syracuseStep 70764691 = 106147037) B106147037
theorem B94352921 : Blo 2181435 94352921 := bstep (se 2 (by rfl) ⟨35382345, by rfl⟩ : syracuseStep 94352921 = 70764691) B70764691
theorem B62901947 : Blo 2181435 62901947 := bstep (se 1 (by rfl) ⟨47176460, by rfl⟩ : syracuseStep 62901947 = 94352921) B94352921
theorem B41934631 : Blo 2181435 41934631 := bstep (se 1 (by rfl) ⟨31450973, by rfl⟩ : syracuseStep 41934631 = 62901947) B62901947
theorem B55912841 : Blo 2181435 55912841 := bstep (se 2 (by rfl) ⟨20967315, by rfl⟩ : syracuseStep 55912841 = 41934631) B41934631
theorem B37275227 : Blo 2181435 37275227 := bstep (se 1 (by rfl) ⟨27956420, by rfl⟩ : syracuseStep 37275227 = 55912841) B55912841
theorem B24850151 : Blo 2181435 24850151 := bstep (se 1 (by rfl) ⟨18637613, by rfl⟩ : syracuseStep 24850151 = 37275227) B37275227
theorem B16566767 : Blo 2181435 16566767 := bstep (se 1 (by rfl) ⟨12425075, by rfl⟩ : syracuseStep 16566767 = 24850151) B24850151
theorem B11044511 : Blo 2181435 11044511 := bstep (se 1 (by rfl) ⟨8283383, by rfl⟩ : syracuseStep 11044511 = 16566767) B16566767
theorem B7363007 : Blo 2181435 7363007 := bstep (se 1 (by rfl) ⟨5522255, by rfl⟩ : syracuseStep 7363007 = 11044511) B11044511
theorem B4908671 : Blo 2181435 4908671 := bstep (se 1 (by rfl) ⟨3681503, by rfl⟩ : syracuseStep 4908671 = 7363007) B7363007
theorem B3272447 : Blo 2181435 3272447 := bstep (se 1 (by rfl) ⟨2454335, by rfl⟩ : syracuseStep 3272447 = 4908671) B4908671
theorem B2181631 : Blo 2181435 2181631 := bstep (se 1 (by rfl) ⟨1636223, by rfl⟩ : syracuseStep 2181631 = 3272447) B3272447
theorem B3272453 : Blo 2181435 3272453 := bbase (se 4 (by rfl) ⟨306792, by rfl⟩ : syracuseStep 3272453 = 613585) (by norm_num)
theorem B2181635 : Blo 2181435 2181635 := bstep (se 1 (by rfl) ⟨1636226, by rfl⟩ : syracuseStep 2181635 = 3272453) B3272453
theorem B3681517 : Blo 2181435 3681517 := bbase (se 3 (by rfl) ⟨690284, by rfl⟩ : syracuseStep 3681517 = 1380569) (by norm_num)
theorem B4908689 : Blo 2181435 4908689 := bstep (se 2 (by rfl) ⟨1840758, by rfl⟩ : syracuseStep 4908689 = 3681517) B3681517
theorem B3272459 : Blo 2181435 3272459 := bstep (se 1 (by rfl) ⟨2454344, by rfl⟩ : syracuseStep 3272459 = 4908689) B4908689
theorem B2181639 : Blo 2181435 2181639 := bstep (se 1 (by rfl) ⟨1636229, by rfl⟩ : syracuseStep 2181639 = 3272459) B3272459
theorem B2454349 : Blo 2181435 2454349 := bbase (se 3 (by rfl) ⟨460190, by rfl⟩ : syracuseStep 2454349 = 920381) (by norm_num)
theorem B3272465 : Blo 2181435 3272465 := bstep (se 2 (by rfl) ⟨1227174, by rfl⟩ : syracuseStep 3272465 = 2454349) B2454349
theorem B2181643 : Blo 2181435 2181643 := bstep (se 1 (by rfl) ⟨1636232, by rfl⟩ : syracuseStep 2181643 = 3272465) B3272465
theorem B7363061 : Blo 2181435 7363061 := bbase (se 5 (by rfl) ⟨345143, by rfl⟩ : syracuseStep 7363061 = 690287) (by norm_num)
theorem B4908707 : Blo 2181435 4908707 := bstep (se 1 (by rfl) ⟨3681530, by rfl⟩ : syracuseStep 4908707 = 7363061) B7363061
theorem B3272471 : Blo 2181435 3272471 := bstep (se 1 (by rfl) ⟨2454353, by rfl⟩ : syracuseStep 3272471 = 4908707) B4908707
theorem B2181647 : Blo 2181435 2181647 := bstep (se 1 (by rfl) ⟨1636235, by rfl⟩ : syracuseStep 2181647 = 3272471) B3272471
theorem B3272477 : Blo 2181435 3272477 := bbase (se 3 (by rfl) ⟨613589, by rfl⟩ : syracuseStep 3272477 = 1227179) (by norm_num)
theorem B2181651 : Blo 2181435 2181651 := bstep (se 1 (by rfl) ⟨1636238, by rfl⟩ : syracuseStep 2181651 = 3272477) B3272477
theorem B4908725 : Blo 2181435 4908725 := bbase (se 5 (by rfl) ⟨230096, by rfl⟩ : syracuseStep 4908725 = 460193) (by norm_num)
theorem B3272483 : Blo 2181435 3272483 := bstep (se 1 (by rfl) ⟨2454362, by rfl⟩ : syracuseStep 3272483 = 4908725) B4908725
theorem B2181655 : Blo 2181435 2181655 := bstep (se 1 (by rfl) ⟨1636241, by rfl⟩ : syracuseStep 2181655 = 3272483) B3272483
theorem B12425237 : Blo 2181435 12425237 := bbase (se 6 (by rfl) ⟨291216, by rfl⟩ : syracuseStep 12425237 = 582433) (by norm_num)
theorem B8283491 : Blo 2181435 8283491 := bstep (se 1 (by rfl) ⟨6212618, by rfl⟩ : syracuseStep 8283491 = 12425237) B12425237
theorem B5522327 : Blo 2181435 5522327 := bstep (se 1 (by rfl) ⟨4141745, by rfl⟩ : syracuseStep 5522327 = 8283491) B8283491
theorem B3681551 : Blo 2181435 3681551 := bstep (se 1 (by rfl) ⟨2761163, by rfl⟩ : syracuseStep 3681551 = 5522327) B5522327
theorem B2454367 : Blo 2181435 2454367 := bstep (se 1 (by rfl) ⟨1840775, by rfl⟩ : syracuseStep 2454367 = 3681551) B3681551
theorem B3272489 : Blo 2181435 3272489 := bstep (se 2 (by rfl) ⟨1227183, by rfl⟩ : syracuseStep 3272489 = 2454367) B2454367
theorem B2181659 : Blo 2181435 2181659 := bstep (se 1 (by rfl) ⟨1636244, by rfl⟩ : syracuseStep 2181659 = 3272489) B3272489
theorem B6212629 : Blo 2181435 6212629 := bbase (se 6 (by rfl) ⟨145608, by rfl⟩ : syracuseStep 6212629 = 291217) (by norm_num)
theorem B8283505 : Blo 2181435 8283505 := bstep (se 2 (by rfl) ⟨3106314, by rfl⟩ : syracuseStep 8283505 = 6212629) B6212629
theorem B11044673 : Blo 2181435 11044673 := bstep (se 2 (by rfl) ⟨4141752, by rfl⟩ : syracuseStep 11044673 = 8283505) B8283505
theorem B7363115 : Blo 2181435 7363115 := bstep (se 1 (by rfl) ⟨5522336, by rfl⟩ : syracuseStep 7363115 = 11044673) B11044673
theorem B4908743 : Blo 2181435 4908743 := bstep (se 1 (by rfl) ⟨3681557, by rfl⟩ : syracuseStep 4908743 = 7363115) B7363115
theorem B3272495 : Blo 2181435 3272495 := bstep (se 1 (by rfl) ⟨2454371, by rfl⟩ : syracuseStep 3272495 = 4908743) B4908743
theorem B2181663 : Blo 2181435 2181663 := bstep (se 1 (by rfl) ⟨1636247, by rfl⟩ : syracuseStep 2181663 = 3272495) B3272495
theorem B3272501 : Blo 2181435 3272501 := bbase (se 5 (by rfl) ⟨153398, by rfl⟩ : syracuseStep 3272501 = 306797) (by norm_num)
theorem B2181667 : Blo 2181435 2181667 := bstep (se 1 (by rfl) ⟨1636250, by rfl⟩ : syracuseStep 2181667 = 3272501) B3272501
theorem B5522357 : Blo 2181435 5522357 := bbase (se 5 (by rfl) ⟨258860, by rfl⟩ : syracuseStep 5522357 = 517721) (by norm_num)
theorem B3681571 : Blo 2181435 3681571 := bstep (se 1 (by rfl) ⟨2761178, by rfl⟩ : syracuseStep 3681571 = 5522357) B5522357
theorem B4908761 : Blo 2181435 4908761 := bstep (se 2 (by rfl) ⟨1840785, by rfl⟩ : syracuseStep 4908761 = 3681571) B3681571
theorem B3272507 : Blo 2181435 3272507 := bstep (se 1 (by rfl) ⟨2454380, by rfl⟩ : syracuseStep 3272507 = 4908761) B4908761
theorem B2181671 : Blo 2181435 2181671 := bstep (se 1 (by rfl) ⟨1636253, by rfl⟩ : syracuseStep 2181671 = 3272507) B3272507
theorem B2454385 : Blo 2181435 2454385 := bbase (se 2 (by rfl) ⟨920394, by rfl⟩ : syracuseStep 2454385 = 1840789) (by norm_num)
theorem B3272513 : Blo 2181435 3272513 := bstep (se 2 (by rfl) ⟨1227192, by rfl⟩ : syracuseStep 3272513 = 2454385) B2454385
theorem B2181675 : Blo 2181435 2181675 := bstep (se 1 (by rfl) ⟨1636256, by rfl⟩ : syracuseStep 2181675 = 3272513) B3272513
theorem B9319013 : Blo 2181435 9319013 := bbase (se 4 (by rfl) ⟨873657, by rfl⟩ : syracuseStep 9319013 = 1747315) (by norm_num)
theorem B6212675 : Blo 2181435 6212675 := bstep (se 1 (by rfl) ⟨4659506, by rfl⟩ : syracuseStep 6212675 = 9319013) B9319013
theorem B4141783 : Blo 2181435 4141783 := bstep (se 1 (by rfl) ⟨3106337, by rfl⟩ : syracuseStep 4141783 = 6212675) B6212675
theorem B5522377 : Blo 2181435 5522377 := bstep (se 2 (by rfl) ⟨2070891, by rfl⟩ : syracuseStep 5522377 = 4141783) B4141783
theorem B7363169 : Blo 2181435 7363169 := bstep (se 2 (by rfl) ⟨2761188, by rfl⟩ : syracuseStep 7363169 = 5522377) B5522377
theorem B4908779 : Blo 2181435 4908779 := bstep (se 1 (by rfl) ⟨3681584, by rfl⟩ : syracuseStep 4908779 = 7363169) B7363169
theorem B3272519 : Blo 2181435 3272519 := bstep (se 1 (by rfl) ⟨2454389, by rfl⟩ : syracuseStep 3272519 = 4908779) B4908779
theorem B2181679 : Blo 2181435 2181679 := bstep (se 1 (by rfl) ⟨1636259, by rfl⟩ : syracuseStep 2181679 = 3272519) B3272519
theorem B3272525 : Blo 2181435 3272525 := bbase (se 3 (by rfl) ⟨613598, by rfl⟩ : syracuseStep 3272525 = 1227197) (by norm_num)
theorem B2181683 : Blo 2181435 2181683 := bstep (se 1 (by rfl) ⟨1636262, by rfl⟩ : syracuseStep 2181683 = 3272525) B3272525
theorem B4908797 : Blo 2181435 4908797 := bbase (se 3 (by rfl) ⟨920399, by rfl⟩ : syracuseStep 4908797 = 1840799) (by norm_num)
theorem B3272531 : Blo 2181435 3272531 := bstep (se 1 (by rfl) ⟨2454398, by rfl⟩ : syracuseStep 3272531 = 4908797) B4908797
theorem B2181687 : Blo 2181435 2181687 := bstep (se 1 (by rfl) ⟨1636265, by rfl⟩ : syracuseStep 2181687 = 3272531) B3272531
theorem B3681605 : Blo 2181435 3681605 := bbase (se 4 (by rfl) ⟨345150, by rfl⟩ : syracuseStep 3681605 = 690301) (by norm_num)
theorem B2454403 : Blo 2181435 2454403 := bstep (se 1 (by rfl) ⟨1840802, by rfl⟩ : syracuseStep 2454403 = 3681605) B3681605
theorem B3272537 : Blo 2181435 3272537 := bstep (se 2 (by rfl) ⟨1227201, by rfl⟩ : syracuseStep 3272537 = 2454403) B2454403
theorem B2181691 : Blo 2181435 2181691 := bstep (se 1 (by rfl) ⟨1636268, by rfl⟩ : syracuseStep 2181691 = 3272537) B3272537
theorem B16567253 : Blo 2181435 16567253 := bbase (se 7 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 16567253 = 388295) (by norm_num)
theorem B11044835 : Blo 2181435 11044835 := bstep (se 1 (by rfl) ⟨8283626, by rfl⟩ : syracuseStep 11044835 = 16567253) B16567253
theorem B7363223 : Blo 2181435 7363223 := bstep (se 1 (by rfl) ⟨5522417, by rfl⟩ : syracuseStep 7363223 = 11044835) B11044835
theorem B4908815 : Blo 2181435 4908815 := bstep (se 1 (by rfl) ⟨3681611, by rfl⟩ : syracuseStep 4908815 = 7363223) B7363223
theorem B3272543 : Blo 2181435 3272543 := bstep (se 1 (by rfl) ⟨2454407, by rfl⟩ : syracuseStep 3272543 = 4908815) B4908815
theorem B2181695 : Blo 2181435 2181695 := bstep (se 1 (by rfl) ⟨1636271, by rfl⟩ : syracuseStep 2181695 = 3272543) B3272543
theorem B3272549 : Blo 2181435 3272549 := bbase (se 4 (by rfl) ⟨306801, by rfl⟩ : syracuseStep 3272549 = 613603) (by norm_num)
theorem B2181699 : Blo 2181435 2181699 := bstep (se 1 (by rfl) ⟨1636274, by rfl⟩ : syracuseStep 2181699 = 3272549) B3272549
theorem B4141829 : Blo 2181435 4141829 := bbase (se 4 (by rfl) ⟨388296, by rfl⟩ : syracuseStep 4141829 = 776593) (by norm_num)
theorem B2761219 : Blo 2181435 2761219 := bstep (se 1 (by rfl) ⟨2070914, by rfl⟩ : syracuseStep 2761219 = 4141829) B4141829
theorem B3681625 : Blo 2181435 3681625 := bstep (se 2 (by rfl) ⟨1380609, by rfl⟩ : syracuseStep 3681625 = 2761219) B2761219
theorem B4908833 : Blo 2181435 4908833 := bstep (se 2 (by rfl) ⟨1840812, by rfl⟩ : syracuseStep 4908833 = 3681625) B3681625
theorem B3272555 : Blo 2181435 3272555 := bstep (se 1 (by rfl) ⟨2454416, by rfl⟩ : syracuseStep 3272555 = 4908833) B4908833
theorem B2181703 : Blo 2181435 2181703 := bstep (se 1 (by rfl) ⟨1636277, by rfl⟩ : syracuseStep 2181703 = 3272555) B3272555
theorem B2454421 : Blo 2181435 2454421 := bbase (se 6 (by rfl) ⟨57525, by rfl⟩ : syracuseStep 2454421 = 115051) (by norm_num)
theorem B3272561 : Blo 2181435 3272561 := bstep (se 2 (by rfl) ⟨1227210, by rfl⟩ : syracuseStep 3272561 = 2454421) B2454421
theorem B2181707 : Blo 2181435 2181707 := bstep (se 1 (by rfl) ⟨1636280, by rfl⟩ : syracuseStep 2181707 = 3272561) B3272561
theorem B2761229 : Blo 2181435 2761229 := bbase (se 3 (by rfl) ⟨517730, by rfl⟩ : syracuseStep 2761229 = 1035461) (by norm_num)
theorem B7363277 : Blo 2181435 7363277 := bstep (se 3 (by rfl) ⟨1380614, by rfl⟩ : syracuseStep 7363277 = 2761229) B2761229
theorem B4908851 : Blo 2181435 4908851 := bstep (se 1 (by rfl) ⟨3681638, by rfl⟩ : syracuseStep 4908851 = 7363277) B7363277
theorem B3272567 : Blo 2181435 3272567 := bstep (se 1 (by rfl) ⟨2454425, by rfl⟩ : syracuseStep 3272567 = 4908851) B4908851
theorem B2181711 : Blo 2181435 2181711 := bstep (se 1 (by rfl) ⟨1636283, by rfl⟩ : syracuseStep 2181711 = 3272567) B3272567
theorem B3272573 : Blo 2181435 3272573 := bbase (se 3 (by rfl) ⟨613607, by rfl⟩ : syracuseStep 3272573 = 1227215) (by norm_num)
theorem B2181715 : Blo 2181435 2181715 := bstep (se 1 (by rfl) ⟨1636286, by rfl⟩ : syracuseStep 2181715 = 3272573) B3272573
theorem B4908869 : Blo 2181435 4908869 := bbase (se 4 (by rfl) ⟨460206, by rfl⟩ : syracuseStep 4908869 = 920413) (by norm_num)
theorem B3272579 : Blo 2181435 3272579 := bstep (se 1 (by rfl) ⟨2454434, by rfl⟩ : syracuseStep 3272579 = 4908869) B4908869
theorem B2181719 : Blo 2181435 2181719 := bstep (se 1 (by rfl) ⟨1636289, by rfl⟩ : syracuseStep 2181719 = 3272579) B3272579
theorem B3494701 : Blo 2181435 3494701 := bbase (se 3 (by rfl) ⟨655256, by rfl⟩ : syracuseStep 3494701 = 1310513) (by norm_num)
theorem B4659601 : Blo 2181435 4659601 := bstep (se 2 (by rfl) ⟨1747350, by rfl⟩ : syracuseStep 4659601 = 3494701) B3494701
theorem B6212801 : Blo 2181435 6212801 := bstep (se 2 (by rfl) ⟨2329800, by rfl⟩ : syracuseStep 6212801 = 4659601) B4659601
theorem B4141867 : Blo 2181435 4141867 := bstep (se 1 (by rfl) ⟨3106400, by rfl⟩ : syracuseStep 4141867 = 6212801) B6212801
theorem B5522489 : Blo 2181435 5522489 := bstep (se 2 (by rfl) ⟨2070933, by rfl⟩ : syracuseStep 5522489 = 4141867) B4141867
theorem B3681659 : Blo 2181435 3681659 := bstep (se 1 (by rfl) ⟨2761244, by rfl⟩ : syracuseStep 3681659 = 5522489) B5522489
theorem B2454439 : Blo 2181435 2454439 := bstep (se 1 (by rfl) ⟨1840829, by rfl⟩ : syracuseStep 2454439 = 3681659) B3681659
theorem B3272585 : Blo 2181435 3272585 := bstep (se 2 (by rfl) ⟨1227219, by rfl⟩ : syracuseStep 3272585 = 2454439) B2454439
theorem B2181723 : Blo 2181435 2181723 := bstep (se 1 (by rfl) ⟨1636292, by rfl⟩ : syracuseStep 2181723 = 3272585) B3272585
theorem B11044997 : Blo 2181435 11044997 := bbase (se 4 (by rfl) ⟨1035468, by rfl⟩ : syracuseStep 11044997 = 2070937) (by norm_num)
theorem B7363331 : Blo 2181435 7363331 := bstep (se 1 (by rfl) ⟨5522498, by rfl⟩ : syracuseStep 7363331 = 11044997) B11044997
theorem B4908887 : Blo 2181435 4908887 := bstep (se 1 (by rfl) ⟨3681665, by rfl⟩ : syracuseStep 4908887 = 7363331) B7363331
theorem B3272591 : Blo 2181435 3272591 := bstep (se 1 (by rfl) ⟨2454443, by rfl⟩ : syracuseStep 3272591 = 4908887) B4908887
theorem B2181727 : Blo 2181435 2181727 := bstep (se 1 (by rfl) ⟨1636295, by rfl⟩ : syracuseStep 2181727 = 3272591) B3272591
theorem B3272597 : Blo 2181435 3272597 := bbase (se 6 (by rfl) ⟨76701, by rfl⟩ : syracuseStep 3272597 = 153403) (by norm_num)
theorem B2181731 : Blo 2181435 2181731 := bstep (se 1 (by rfl) ⟨1636298, by rfl⟩ : syracuseStep 2181731 = 3272597) B3272597
theorem B2329813 : Blo 2181435 2329813 := bbase (se 7 (by rfl) ⟨27302, by rfl⟩ : syracuseStep 2329813 = 54605) (by norm_num)
theorem B12425669 : Blo 2181435 12425669 := bstep (se 4 (by rfl) ⟨1164906, by rfl⟩ : syracuseStep 12425669 = 2329813) B2329813
theorem B8283779 : Blo 2181435 8283779 := bstep (se 1 (by rfl) ⟨6212834, by rfl⟩ : syracuseStep 8283779 = 12425669) B12425669
theorem B5522519 : Blo 2181435 5522519 := bstep (se 1 (by rfl) ⟨4141889, by rfl⟩ : syracuseStep 5522519 = 8283779) B8283779
theorem B3681679 : Blo 2181435 3681679 := bstep (se 1 (by rfl) ⟨2761259, by rfl⟩ : syracuseStep 3681679 = 5522519) B5522519
theorem B4908905 : Blo 2181435 4908905 := bstep (se 2 (by rfl) ⟨1840839, by rfl⟩ : syracuseStep 4908905 = 3681679) B3681679
theorem B3272603 : Blo 2181435 3272603 := bstep (se 1 (by rfl) ⟨2454452, by rfl⟩ : syracuseStep 3272603 = 4908905) B4908905
theorem B2181735 : Blo 2181435 2181735 := bstep (se 1 (by rfl) ⟨1636301, by rfl⟩ : syracuseStep 2181735 = 3272603) B3272603
theorem B2454457 : Blo 2181435 2454457 := bbase (se 2 (by rfl) ⟨920421, by rfl⟩ : syracuseStep 2454457 = 1840843) (by norm_num)
theorem B3272609 : Blo 2181435 3272609 := bstep (se 2 (by rfl) ⟨1227228, by rfl⟩ : syracuseStep 3272609 = 2454457) B2454457
theorem B2181739 : Blo 2181435 2181739 := bstep (se 1 (by rfl) ⟨1636304, by rfl⟩ : syracuseStep 2181739 = 3272609) B3272609
theorem B4975901 : Blo 2181435 4975901 := bbase (se 3 (by rfl) ⟨932981, by rfl⟩ : syracuseStep 4975901 = 1865963) (by norm_num)
theorem B3317267 : Blo 2181435 3317267 := bstep (se 1 (by rfl) ⟨2487950, by rfl⟩ : syracuseStep 3317267 = 4975901) B4975901
theorem B2211511 : Blo 2181435 2211511 := bstep (se 1 (by rfl) ⟨1658633, by rfl⟩ : syracuseStep 2211511 = 3317267) B3317267
theorem B2948681 : Blo 2181435 2948681 := bstep (se 2 (by rfl) ⟨1105755, by rfl⟩ : syracuseStep 2948681 = 2211511) B2211511
theorem B7863149 : Blo 2181435 7863149 := bstep (se 3 (by rfl) ⟨1474340, by rfl⟩ : syracuseStep 7863149 = 2948681) B2948681
theorem B5242099 : Blo 2181435 5242099 := bstep (se 1 (by rfl) ⟨3931574, by rfl⟩ : syracuseStep 5242099 = 7863149) B7863149
theorem B6989465 : Blo 2181435 6989465 := bstep (se 2 (by rfl) ⟨2621049, by rfl⟩ : syracuseStep 6989465 = 5242099) B5242099
theorem B4659643 : Blo 2181435 4659643 := bstep (se 1 (by rfl) ⟨3494732, by rfl⟩ : syracuseStep 4659643 = 6989465) B6989465
theorem B6212857 : Blo 2181435 6212857 := bstep (se 2 (by rfl) ⟨2329821, by rfl⟩ : syracuseStep 6212857 = 4659643) B4659643
theorem B8283809 : Blo 2181435 8283809 := bstep (se 2 (by rfl) ⟨3106428, by rfl⟩ : syracuseStep 8283809 = 6212857) B6212857
theorem B5522539 : Blo 2181435 5522539 := bstep (se 1 (by rfl) ⟨4141904, by rfl⟩ : syracuseStep 5522539 = 8283809) B8283809
theorem B7363385 : Blo 2181435 7363385 := bstep (se 2 (by rfl) ⟨2761269, by rfl⟩ : syracuseStep 7363385 = 5522539) B5522539
theorem B4908923 : Blo 2181435 4908923 := bstep (se 1 (by rfl) ⟨3681692, by rfl⟩ : syracuseStep 4908923 = 7363385) B7363385
theorem B3272615 : Blo 2181435 3272615 := bstep (se 1 (by rfl) ⟨2454461, by rfl⟩ : syracuseStep 3272615 = 4908923) B4908923
theorem B2181743 : Blo 2181435 2181743 := bstep (se 1 (by rfl) ⟨1636307, by rfl⟩ : syracuseStep 2181743 = 3272615) B3272615
theorem B3272621 : Blo 2181435 3272621 := bbase (se 3 (by rfl) ⟨613616, by rfl⟩ : syracuseStep 3272621 = 1227233) (by norm_num)
theorem B2181747 : Blo 2181435 2181747 := bstep (se 1 (by rfl) ⟨1636310, by rfl⟩ : syracuseStep 2181747 = 3272621) B3272621
theorem B4908941 : Blo 2181435 4908941 := bbase (se 3 (by rfl) ⟨920426, by rfl⟩ : syracuseStep 4908941 = 1840853) (by norm_num)
theorem B3272627 : Blo 2181435 3272627 := bstep (se 1 (by rfl) ⟨2454470, by rfl⟩ : syracuseStep 3272627 = 4908941) B4908941
theorem B2181751 : Blo 2181435 2181751 := bstep (se 1 (by rfl) ⟨1636313, by rfl⟩ : syracuseStep 2181751 = 3272627) B3272627
theorem B2761285 : Blo 2181435 2761285 := bbase (se 4 (by rfl) ⟨258870, by rfl⟩ : syracuseStep 2761285 = 517741) (by norm_num)
theorem B3681713 : Blo 2181435 3681713 := bstep (se 2 (by rfl) ⟨1380642, by rfl⟩ : syracuseStep 3681713 = 2761285) B2761285
theorem B2454475 : Blo 2181435 2454475 := bstep (se 1 (by rfl) ⟨1840856, by rfl⟩ : syracuseStep 2454475 = 3681713) B3681713
theorem B3272633 : Blo 2181435 3272633 := bstep (se 2 (by rfl) ⟨1227237, by rfl⟩ : syracuseStep 3272633 = 2454475) B2454475
theorem B2181755 : Blo 2181435 2181755 := bstep (se 1 (by rfl) ⟨1636316, by rfl⟩ : syracuseStep 2181755 = 3272633) B3272633
theorem B7863205 : Blo 2181435 7863205 := bbase (se 4 (by rfl) ⟨737175, by rfl⟩ : syracuseStep 7863205 = 1474351) (by norm_num)
theorem B10484273 : Blo 2181435 10484273 := bstep (se 2 (by rfl) ⟨3931602, by rfl⟩ : syracuseStep 10484273 = 7863205) B7863205
theorem B27958061 : Blo 2181435 27958061 := bstep (se 3 (by rfl) ⟨5242136, by rfl⟩ : syracuseStep 27958061 = 10484273) B10484273
theorem B18638707 : Blo 2181435 18638707 := bstep (se 1 (by rfl) ⟨13979030, by rfl⟩ : syracuseStep 18638707 = 27958061) B27958061
theorem B24851609 : Blo 2181435 24851609 := bstep (se 2 (by rfl) ⟨9319353, by rfl⟩ : syracuseStep 24851609 = 18638707) B18638707
theorem B16567739 : Blo 2181435 16567739 := bstep (se 1 (by rfl) ⟨12425804, by rfl⟩ : syracuseStep 16567739 = 24851609) B24851609
theorem B11045159 : Blo 2181435 11045159 := bstep (se 1 (by rfl) ⟨8283869, by rfl⟩ : syracuseStep 11045159 = 16567739) B16567739
theorem B7363439 : Blo 2181435 7363439 := bstep (se 1 (by rfl) ⟨5522579, by rfl⟩ : syracuseStep 7363439 = 11045159) B11045159
theorem B4908959 : Blo 2181435 4908959 := bstep (se 1 (by rfl) ⟨3681719, by rfl⟩ : syracuseStep 4908959 = 7363439) B7363439
theorem B3272639 : Blo 2181435 3272639 := bstep (se 1 (by rfl) ⟨2454479, by rfl⟩ : syracuseStep 3272639 = 4908959) B4908959
theorem B2181759 : Blo 2181435 2181759 := bstep (se 1 (by rfl) ⟨1636319, by rfl⟩ : syracuseStep 2181759 = 3272639) B3272639
theorem B3272645 : Blo 2181435 3272645 := bbase (se 4 (by rfl) ⟨306810, by rfl⟩ : syracuseStep 3272645 = 613621) (by norm_num)
theorem B2181763 : Blo 2181435 2181763 := bstep (se 1 (by rfl) ⟨1636322, by rfl⟩ : syracuseStep 2181763 = 3272645) B3272645
theorem B3681733 : Blo 2181435 3681733 := bbase (se 4 (by rfl) ⟨345162, by rfl⟩ : syracuseStep 3681733 = 690325) (by norm_num)
theorem B4908977 : Blo 2181435 4908977 := bstep (se 2 (by rfl) ⟨1840866, by rfl⟩ : syracuseStep 4908977 = 3681733) B3681733
theorem B3272651 : Blo 2181435 3272651 := bstep (se 1 (by rfl) ⟨2454488, by rfl⟩ : syracuseStep 3272651 = 4908977) B4908977
theorem B2181767 : Blo 2181435 2181767 := bstep (se 1 (by rfl) ⟨1636325, by rfl⟩ : syracuseStep 2181767 = 3272651) B3272651
theorem B2454493 : Blo 2181435 2454493 := bbase (se 3 (by rfl) ⟨460217, by rfl⟩ : syracuseStep 2454493 = 920435) (by norm_num)
theorem B3272657 : Blo 2181435 3272657 := bstep (se 2 (by rfl) ⟨1227246, by rfl⟩ : syracuseStep 3272657 = 2454493) B2454493
theorem B2181771 : Blo 2181435 2181771 := bstep (se 1 (by rfl) ⟨1636328, by rfl⟩ : syracuseStep 2181771 = 3272657) B3272657
theorem B7363493 : Blo 2181435 7363493 := bbase (se 4 (by rfl) ⟨690327, by rfl⟩ : syracuseStep 7363493 = 1380655) (by norm_num)
theorem B4908995 : Blo 2181435 4908995 := bstep (se 1 (by rfl) ⟨3681746, by rfl⟩ : syracuseStep 4908995 = 7363493) B7363493
theorem B3272663 : Blo 2181435 3272663 := bstep (se 1 (by rfl) ⟨2454497, by rfl⟩ : syracuseStep 3272663 = 4908995) B4908995
theorem B2181775 : Blo 2181435 2181775 := bstep (se 1 (by rfl) ⟨1636331, by rfl⟩ : syracuseStep 2181775 = 3272663) B3272663
theorem B3272669 : Blo 2181435 3272669 := bbase (se 3 (by rfl) ⟨613625, by rfl⟩ : syracuseStep 3272669 = 1227251) (by norm_num)
theorem B2181779 : Blo 2181435 2181779 := bstep (se 1 (by rfl) ⟨1636334, by rfl⟩ : syracuseStep 2181779 = 3272669) B3272669
theorem B4909013 : Blo 2181435 4909013 := bbase (se 7 (by rfl) ⟨57527, by rfl⟩ : syracuseStep 4909013 = 115055) (by norm_num)
theorem B3272675 : Blo 2181435 3272675 := bstep (se 1 (by rfl) ⟨2454506, by rfl⟩ : syracuseStep 3272675 = 4909013) B4909013
theorem B2181783 : Blo 2181435 2181783 := bstep (se 1 (by rfl) ⟨1636337, by rfl⟩ : syracuseStep 2181783 = 3272675) B3272675
theorem B5242205 : Blo 2181435 5242205 := bbase (se 3 (by rfl) ⟨982913, by rfl⟩ : syracuseStep 5242205 = 1965827) (by norm_num)
theorem B13979213 : Blo 2181435 13979213 := bstep (se 3 (by rfl) ⟨2621102, by rfl⟩ : syracuseStep 13979213 = 5242205) B5242205
theorem B9319475 : Blo 2181435 9319475 := bstep (se 1 (by rfl) ⟨6989606, by rfl⟩ : syracuseStep 9319475 = 13979213) B13979213
theorem B6212983 : Blo 2181435 6212983 := bstep (se 1 (by rfl) ⟨4659737, by rfl⟩ : syracuseStep 6212983 = 9319475) B9319475
theorem B8283977 : Blo 2181435 8283977 := bstep (se 2 (by rfl) ⟨3106491, by rfl⟩ : syracuseStep 8283977 = 6212983) B6212983
theorem B5522651 : Blo 2181435 5522651 := bstep (se 1 (by rfl) ⟨4141988, by rfl⟩ : syracuseStep 5522651 = 8283977) B8283977
theorem B3681767 : Blo 2181435 3681767 := bstep (se 1 (by rfl) ⟨2761325, by rfl⟩ : syracuseStep 3681767 = 5522651) B5522651
theorem B2454511 : Blo 2181435 2454511 := bstep (se 1 (by rfl) ⟨1840883, by rfl⟩ : syracuseStep 2454511 = 3681767) B3681767
theorem B3272681 : Blo 2181435 3272681 := bstep (se 2 (by rfl) ⟨1227255, by rfl⟩ : syracuseStep 3272681 = 2454511) B2454511
theorem B2181787 : Blo 2181435 2181787 := bstep (se 1 (by rfl) ⟨1636340, by rfl⟩ : syracuseStep 2181787 = 3272681) B3272681
theorem B3931661 : Blo 2181435 3931661 := bbase (se 3 (by rfl) ⟨737186, by rfl⟩ : syracuseStep 3931661 = 1474373) (by norm_num)
theorem B2621107 : Blo 2181435 2621107 := bstep (se 1 (by rfl) ⟨1965830, by rfl⟩ : syracuseStep 2621107 = 3931661) B3931661
theorem B3494809 : Blo 2181435 3494809 := bstep (se 2 (by rfl) ⟨1310553, by rfl⟩ : syracuseStep 3494809 = 2621107) B2621107
theorem B18638981 : Blo 2181435 18638981 := bstep (se 4 (by rfl) ⟨1747404, by rfl⟩ : syracuseStep 18638981 = 3494809) B3494809
theorem B12425987 : Blo 2181435 12425987 := bstep (se 1 (by rfl) ⟨9319490, by rfl⟩ : syracuseStep 12425987 = 18638981) B18638981
theorem B8283991 : Blo 2181435 8283991 := bstep (se 1 (by rfl) ⟨6212993, by rfl⟩ : syracuseStep 8283991 = 12425987) B12425987
theorem B11045321 : Blo 2181435 11045321 := bstep (se 2 (by rfl) ⟨4141995, by rfl⟩ : syracuseStep 11045321 = 8283991) B8283991
theorem B7363547 : Blo 2181435 7363547 := bstep (se 1 (by rfl) ⟨5522660, by rfl⟩ : syracuseStep 7363547 = 11045321) B11045321
theorem B4909031 : Blo 2181435 4909031 := bstep (se 1 (by rfl) ⟨3681773, by rfl⟩ : syracuseStep 4909031 = 7363547) B7363547
theorem B3272687 : Blo 2181435 3272687 := bstep (se 1 (by rfl) ⟨2454515, by rfl⟩ : syracuseStep 3272687 = 4909031) B4909031
theorem B2181791 : Blo 2181435 2181791 := bstep (se 1 (by rfl) ⟨1636343, by rfl⟩ : syracuseStep 2181791 = 3272687) B3272687
theorem B3272693 : Blo 2181435 3272693 := bbase (se 5 (by rfl) ⟨153407, by rfl⟩ : syracuseStep 3272693 = 306815) (by norm_num)
theorem B2181795 : Blo 2181435 2181795 := bstep (se 1 (by rfl) ⟨1636346, by rfl⟩ : syracuseStep 2181795 = 3272693) B3272693
theorem B2621117 : Blo 2181435 2621117 := bbase (se 3 (by rfl) ⟨491459, by rfl⟩ : syracuseStep 2621117 = 982919) (by norm_num)
theorem B6989645 : Blo 2181435 6989645 := bstep (se 3 (by rfl) ⟨1310558, by rfl⟩ : syracuseStep 6989645 = 2621117) B2621117
theorem B4659763 : Blo 2181435 4659763 := bstep (se 1 (by rfl) ⟨3494822, by rfl⟩ : syracuseStep 4659763 = 6989645) B6989645
theorem B6213017 : Blo 2181435 6213017 := bstep (se 2 (by rfl) ⟨2329881, by rfl⟩ : syracuseStep 6213017 = 4659763) B4659763
theorem B4142011 : Blo 2181435 4142011 := bstep (se 1 (by rfl) ⟨3106508, by rfl⟩ : syracuseStep 4142011 = 6213017) B6213017
theorem B5522681 : Blo 2181435 5522681 := bstep (se 2 (by rfl) ⟨2071005, by rfl⟩ : syracuseStep 5522681 = 4142011) B4142011
theorem B3681787 : Blo 2181435 3681787 := bstep (se 1 (by rfl) ⟨2761340, by rfl⟩ : syracuseStep 3681787 = 5522681) B5522681
theorem B4909049 : Blo 2181435 4909049 := bstep (se 2 (by rfl) ⟨1840893, by rfl⟩ : syracuseStep 4909049 = 3681787) B3681787
theorem B3272699 : Blo 2181435 3272699 := bstep (se 1 (by rfl) ⟨2454524, by rfl⟩ : syracuseStep 3272699 = 4909049) B4909049
theorem B2181799 : Blo 2181435 2181799 := bstep (se 1 (by rfl) ⟨1636349, by rfl⟩ : syracuseStep 2181799 = 3272699) B3272699
theorem B2454529 : Blo 2181435 2454529 := bbase (se 2 (by rfl) ⟨920448, by rfl⟩ : syracuseStep 2454529 = 1840897) (by norm_num)
theorem B3272705 : Blo 2181435 3272705 := bstep (se 2 (by rfl) ⟨1227264, by rfl⟩ : syracuseStep 3272705 = 2454529) B2454529
theorem B2181803 : Blo 2181435 2181803 := bstep (se 1 (by rfl) ⟨1636352, by rfl⟩ : syracuseStep 2181803 = 3272705) B3272705
theorem B5522701 : Blo 2181435 5522701 := bbase (se 3 (by rfl) ⟨1035506, by rfl⟩ : syracuseStep 5522701 = 2071013) (by norm_num)
theorem B7363601 : Blo 2181435 7363601 := bstep (se 2 (by rfl) ⟨2761350, by rfl⟩ : syracuseStep 7363601 = 5522701) B5522701
theorem B4909067 : Blo 2181435 4909067 := bstep (se 1 (by rfl) ⟨3681800, by rfl⟩ : syracuseStep 4909067 = 7363601) B7363601
theorem B3272711 : Blo 2181435 3272711 := bstep (se 1 (by rfl) ⟨2454533, by rfl⟩ : syracuseStep 3272711 = 4909067) B4909067
theorem B2181807 : Blo 2181435 2181807 := bstep (se 1 (by rfl) ⟨1636355, by rfl⟩ : syracuseStep 2181807 = 3272711) B3272711
theorem B3272717 : Blo 2181435 3272717 := bbase (se 3 (by rfl) ⟨613634, by rfl⟩ : syracuseStep 3272717 = 1227269) (by norm_num)
theorem B2181811 : Blo 2181435 2181811 := bstep (se 1 (by rfl) ⟨1636358, by rfl⟩ : syracuseStep 2181811 = 3272717) B3272717
theorem B4909085 : Blo 2181435 4909085 := bbase (se 3 (by rfl) ⟨920453, by rfl⟩ : syracuseStep 4909085 = 1840907) (by norm_num)
theorem B3272723 : Blo 2181435 3272723 := bstep (se 1 (by rfl) ⟨2454542, by rfl⟩ : syracuseStep 3272723 = 4909085) B4909085
theorem B2181815 : Blo 2181435 2181815 := bstep (se 1 (by rfl) ⟨1636361, by rfl⟩ : syracuseStep 2181815 = 3272723) B3272723
theorem B3681821 : Blo 2181435 3681821 := bbase (se 3 (by rfl) ⟨690341, by rfl⟩ : syracuseStep 3681821 = 1380683) (by norm_num)
theorem B2454547 : Blo 2181435 2454547 := bstep (se 1 (by rfl) ⟨1840910, by rfl⟩ : syracuseStep 2454547 = 3681821) B3681821
theorem B3272729 : Blo 2181435 3272729 := bstep (se 2 (by rfl) ⟨1227273, by rfl⟩ : syracuseStep 3272729 = 2454547) B2454547
theorem B2181819 : Blo 2181435 2181819 := bstep (se 1 (by rfl) ⟨1636364, by rfl⟩ : syracuseStep 2181819 = 3272729) B3272729
theorem B10484581 : Blo 2181435 10484581 := bbase (se 4 (by rfl) ⟨982929, by rfl⟩ : syracuseStep 10484581 = 1965859) (by norm_num)
theorem B13979441 : Blo 2181435 13979441 := bstep (se 2 (by rfl) ⟨5242290, by rfl⟩ : syracuseStep 13979441 = 10484581) B10484581
theorem B9319627 : Blo 2181435 9319627 := bstep (se 1 (by rfl) ⟨6989720, by rfl⟩ : syracuseStep 9319627 = 13979441) B13979441
theorem B12426169 : Blo 2181435 12426169 := bstep (se 2 (by rfl) ⟨4659813, by rfl⟩ : syracuseStep 12426169 = 9319627) B9319627
theorem B16568225 : Blo 2181435 16568225 := bstep (se 2 (by rfl) ⟨6213084, by rfl⟩ : syracuseStep 16568225 = 12426169) B12426169
theorem B11045483 : Blo 2181435 11045483 := bstep (se 1 (by rfl) ⟨8284112, by rfl⟩ : syracuseStep 11045483 = 16568225) B16568225
theorem B7363655 : Blo 2181435 7363655 := bstep (se 1 (by rfl) ⟨5522741, by rfl⟩ : syracuseStep 7363655 = 11045483) B11045483
theorem B4909103 : Blo 2181435 4909103 := bstep (se 1 (by rfl) ⟨3681827, by rfl⟩ : syracuseStep 4909103 = 7363655) B7363655
theorem B3272735 : Blo 2181435 3272735 := bstep (se 1 (by rfl) ⟨2454551, by rfl⟩ : syracuseStep 3272735 = 4909103) B4909103
theorem B2181823 : Blo 2181435 2181823 := bstep (se 1 (by rfl) ⟨1636367, by rfl⟩ : syracuseStep 2181823 = 3272735) B3272735
theorem B3272741 : Blo 2181435 3272741 := bbase (se 4 (by rfl) ⟨306819, by rfl⟩ : syracuseStep 3272741 = 613639) (by norm_num)
theorem B2181827 : Blo 2181435 2181827 := bstep (se 1 (by rfl) ⟨1636370, by rfl⟩ : syracuseStep 2181827 = 3272741) B3272741
theorem B2761381 : Blo 2181435 2761381 := bbase (se 4 (by rfl) ⟨258879, by rfl⟩ : syracuseStep 2761381 = 517759) (by norm_num)
theorem B3681841 : Blo 2181435 3681841 := bstep (se 2 (by rfl) ⟨1380690, by rfl⟩ : syracuseStep 3681841 = 2761381) B2761381
theorem B4909121 : Blo 2181435 4909121 := bstep (se 2 (by rfl) ⟨1840920, by rfl⟩ : syracuseStep 4909121 = 3681841) B3681841
theorem B3272747 : Blo 2181435 3272747 := bstep (se 1 (by rfl) ⟨2454560, by rfl⟩ : syracuseStep 3272747 = 4909121) B4909121
theorem B2181831 : Blo 2181435 2181831 := bstep (se 1 (by rfl) ⟨1636373, by rfl⟩ : syracuseStep 2181831 = 3272747) B3272747
theorem B2454565 : Blo 2181435 2454565 := bbase (se 4 (by rfl) ⟨230115, by rfl⟩ : syracuseStep 2454565 = 460231) (by norm_num)
theorem B3272753 : Blo 2181435 3272753 := bstep (se 2 (by rfl) ⟨1227282, by rfl⟩ : syracuseStep 3272753 = 2454565) B2454565
theorem B2181835 : Blo 2181435 2181835 := bstep (se 1 (by rfl) ⟨1636376, by rfl⟩ : syracuseStep 2181835 = 3272753) B3272753
theorem B2621165 : Blo 2181435 2621165 := bbase (se 3 (by rfl) ⟨491468, by rfl⟩ : syracuseStep 2621165 = 982937) (by norm_num)
theorem B6989773 : Blo 2181435 6989773 := bstep (se 3 (by rfl) ⟨1310582, by rfl⟩ : syracuseStep 6989773 = 2621165) B2621165
theorem B9319697 : Blo 2181435 9319697 := bstep (se 2 (by rfl) ⟨3494886, by rfl⟩ : syracuseStep 9319697 = 6989773) B6989773
theorem B6213131 : Blo 2181435 6213131 := bstep (se 1 (by rfl) ⟨4659848, by rfl⟩ : syracuseStep 6213131 = 9319697) B9319697
theorem B4142087 : Blo 2181435 4142087 := bstep (se 1 (by rfl) ⟨3106565, by rfl⟩ : syracuseStep 4142087 = 6213131) B6213131
theorem B2761391 : Blo 2181435 2761391 := bstep (se 1 (by rfl) ⟨2071043, by rfl⟩ : syracuseStep 2761391 = 4142087) B4142087
theorem B7363709 : Blo 2181435 7363709 := bstep (se 3 (by rfl) ⟨1380695, by rfl⟩ : syracuseStep 7363709 = 2761391) B2761391
theorem B4909139 : Blo 2181435 4909139 := bstep (se 1 (by rfl) ⟨3681854, by rfl⟩ : syracuseStep 4909139 = 7363709) B7363709
theorem B3272759 : Blo 2181435 3272759 := bstep (se 1 (by rfl) ⟨2454569, by rfl⟩ : syracuseStep 3272759 = 4909139) B4909139
theorem B2181839 : Blo 2181435 2181839 := bstep (se 1 (by rfl) ⟨1636379, by rfl⟩ : syracuseStep 2181839 = 3272759) B3272759
theorem B3272765 : Blo 2181435 3272765 := bbase (se 3 (by rfl) ⟨613643, by rfl⟩ : syracuseStep 3272765 = 1227287) (by norm_num)
theorem B2181843 : Blo 2181435 2181843 := bstep (se 1 (by rfl) ⟨1636382, by rfl⟩ : syracuseStep 2181843 = 3272765) B3272765
theorem B4909157 : Blo 2181435 4909157 := bbase (se 4 (by rfl) ⟨460233, by rfl⟩ : syracuseStep 4909157 = 920467) (by norm_num)
theorem B3272771 : Blo 2181435 3272771 := bstep (se 1 (by rfl) ⟨2454578, by rfl⟩ : syracuseStep 3272771 = 4909157) B4909157
theorem B2181847 : Blo 2181435 2181847 := bstep (se 1 (by rfl) ⟨1636385, by rfl⟩ : syracuseStep 2181847 = 3272771) B3272771
theorem B5522813 : Blo 2181435 5522813 := bbase (se 3 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 5522813 = 2071055) (by norm_num)
theorem B3681875 : Blo 2181435 3681875 := bstep (se 1 (by rfl) ⟨2761406, by rfl⟩ : syracuseStep 3681875 = 5522813) B5522813
theorem B2454583 : Blo 2181435 2454583 := bstep (se 1 (by rfl) ⟨1840937, by rfl⟩ : syracuseStep 2454583 = 3681875) B3681875
theorem B3272777 : Blo 2181435 3272777 := bstep (se 2 (by rfl) ⟨1227291, by rfl⟩ : syracuseStep 3272777 = 2454583) B2454583
theorem B2181851 : Blo 2181435 2181851 := bstep (se 1 (by rfl) ⟨1636388, by rfl⟩ : syracuseStep 2181851 = 3272777) B3272777
theorem B4142117 : Blo 2181435 4142117 := bbase (se 4 (by rfl) ⟨388323, by rfl⟩ : syracuseStep 4142117 = 776647) (by norm_num)
theorem B11045645 : Blo 2181435 11045645 := bstep (se 3 (by rfl) ⟨2071058, by rfl⟩ : syracuseStep 11045645 = 4142117) B4142117
theorem B7363763 : Blo 2181435 7363763 := bstep (se 1 (by rfl) ⟨5522822, by rfl⟩ : syracuseStep 7363763 = 11045645) B11045645
theorem B4909175 : Blo 2181435 4909175 := bstep (se 1 (by rfl) ⟨3681881, by rfl⟩ : syracuseStep 4909175 = 7363763) B7363763
theorem B3272783 : Blo 2181435 3272783 := bstep (se 1 (by rfl) ⟨2454587, by rfl⟩ : syracuseStep 3272783 = 4909175) B4909175
theorem B2181855 : Blo 2181435 2181855 := bstep (se 1 (by rfl) ⟨1636391, by rfl⟩ : syracuseStep 2181855 = 3272783) B3272783
theorem B3272789 : Blo 2181435 3272789 := bbase (se 8 (by rfl) ⟨19176, by rfl⟩ : syracuseStep 3272789 = 38353) (by norm_num)
theorem B2181859 : Blo 2181435 2181859 := bstep (se 1 (by rfl) ⟨1636394, by rfl⟩ : syracuseStep 2181859 = 3272789) B3272789
theorem B5598197 : Blo 2181435 5598197 := bbase (se 5 (by rfl) ⟨262415, by rfl⟩ : syracuseStep 5598197 = 524831) (by norm_num)
theorem B3732131 : Blo 2181435 3732131 := bstep (se 1 (by rfl) ⟨2799098, by rfl⟩ : syracuseStep 3732131 = 5598197) B5598197
theorem B2488087 : Blo 2181435 2488087 := bstep (se 1 (by rfl) ⟨1866065, by rfl⟩ : syracuseStep 2488087 = 3732131) B3732131
theorem B3317449 : Blo 2181435 3317449 := bstep (se 2 (by rfl) ⟨1244043, by rfl⟩ : syracuseStep 3317449 = 2488087) B2488087
theorem B4423265 : Blo 2181435 4423265 := bstep (se 2 (by rfl) ⟨1658724, by rfl⟩ : syracuseStep 4423265 = 3317449) B3317449
theorem B2948843 : Blo 2181435 2948843 := bstep (se 1 (by rfl) ⟨2211632, by rfl⟩ : syracuseStep 2948843 = 4423265) B4423265
theorem B7863581 : Blo 2181435 7863581 := bstep (se 3 (by rfl) ⟨1474421, by rfl⟩ : syracuseStep 7863581 = 2948843) B2948843
theorem B20969549 : Blo 2181435 20969549 := bstep (se 3 (by rfl) ⟨3931790, by rfl⟩ : syracuseStep 20969549 = 7863581) B7863581
theorem B13979699 : Blo 2181435 13979699 := bstep (se 1 (by rfl) ⟨10484774, by rfl⟩ : syracuseStep 13979699 = 20969549) B20969549
theorem B9319799 : Blo 2181435 9319799 := bstep (se 1 (by rfl) ⟨6989849, by rfl⟩ : syracuseStep 9319799 = 13979699) B13979699
theorem B6213199 : Blo 2181435 6213199 := bstep (se 1 (by rfl) ⟨4659899, by rfl⟩ : syracuseStep 6213199 = 9319799) B9319799
theorem B8284265 : Blo 2181435 8284265 := bstep (se 2 (by rfl) ⟨3106599, by rfl⟩ : syracuseStep 8284265 = 6213199) B6213199
theorem B5522843 : Blo 2181435 5522843 := bstep (se 1 (by rfl) ⟨4142132, by rfl⟩ : syracuseStep 5522843 = 8284265) B8284265
theorem B3681895 : Blo 2181435 3681895 := bstep (se 1 (by rfl) ⟨2761421, by rfl⟩ : syracuseStep 3681895 = 5522843) B5522843
theorem B4909193 : Blo 2181435 4909193 := bstep (se 2 (by rfl) ⟨1840947, by rfl⟩ : syracuseStep 4909193 = 3681895) B3681895
theorem B3272795 : Blo 2181435 3272795 := bstep (se 1 (by rfl) ⟨2454596, by rfl⟩ : syracuseStep 3272795 = 4909193) B4909193
theorem B2181863 : Blo 2181435 2181863 := bstep (se 1 (by rfl) ⟨1636397, by rfl⟩ : syracuseStep 2181863 = 3272795) B3272795
theorem B2454601 : Blo 2181435 2454601 := bbase (se 2 (by rfl) ⟨920475, by rfl⟩ : syracuseStep 2454601 = 1840951) (by norm_num)
theorem B3272801 : Blo 2181435 3272801 := bstep (se 2 (by rfl) ⟨1227300, by rfl⟩ : syracuseStep 3272801 = 2454601) B2454601
theorem B2181867 : Blo 2181435 2181867 := bstep (se 1 (by rfl) ⟨1636400, by rfl⟩ : syracuseStep 2181867 = 3272801) B3272801
theorem B3931805 : Blo 2181435 3931805 := bbase (se 3 (by rfl) ⟨737213, by rfl⟩ : syracuseStep 3931805 = 1474427) (by norm_num)
theorem B2621203 : Blo 2181435 2621203 := bstep (se 1 (by rfl) ⟨1965902, by rfl⟩ : syracuseStep 2621203 = 3931805) B3931805
theorem B13979749 : Blo 2181435 13979749 := bstep (se 4 (by rfl) ⟨1310601, by rfl⟩ : syracuseStep 13979749 = 2621203) B2621203
theorem B18639665 : Blo 2181435 18639665 := bstep (se 2 (by rfl) ⟨6989874, by rfl⟩ : syracuseStep 18639665 = 13979749) B13979749
theorem B12426443 : Blo 2181435 12426443 := bstep (se 1 (by rfl) ⟨9319832, by rfl⟩ : syracuseStep 12426443 = 18639665) B18639665
theorem B8284295 : Blo 2181435 8284295 := bstep (se 1 (by rfl) ⟨6213221, by rfl⟩ : syracuseStep 8284295 = 12426443) B12426443
theorem B5522863 : Blo 2181435 5522863 := bstep (se 1 (by rfl) ⟨4142147, by rfl⟩ : syracuseStep 5522863 = 8284295) B8284295
theorem B7363817 : Blo 2181435 7363817 := bstep (se 2 (by rfl) ⟨2761431, by rfl⟩ : syracuseStep 7363817 = 5522863) B5522863
theorem B4909211 : Blo 2181435 4909211 := bstep (se 1 (by rfl) ⟨3681908, by rfl⟩ : syracuseStep 4909211 = 7363817) B7363817
theorem B3272807 : Blo 2181435 3272807 := bstep (se 1 (by rfl) ⟨2454605, by rfl⟩ : syracuseStep 3272807 = 4909211) B4909211
theorem B2181871 : Blo 2181435 2181871 := bstep (se 1 (by rfl) ⟨1636403, by rfl⟩ : syracuseStep 2181871 = 3272807) B3272807
theorem B3272813 : Blo 2181435 3272813 := bbase (se 3 (by rfl) ⟨613652, by rfl⟩ : syracuseStep 3272813 = 1227305) (by norm_num)
theorem B2181875 : Blo 2181435 2181875 := bstep (se 1 (by rfl) ⟨1636406, by rfl⟩ : syracuseStep 2181875 = 3272813) B3272813
theorem B4909229 : Blo 2181435 4909229 := bbase (se 3 (by rfl) ⟨920480, by rfl⟩ : syracuseStep 4909229 = 1840961) (by norm_num)
theorem B3272819 : Blo 2181435 3272819 := bstep (se 1 (by rfl) ⟨2454614, by rfl⟩ : syracuseStep 3272819 = 4909229) B4909229
theorem B2181879 : Blo 2181435 2181879 := bstep (se 1 (by rfl) ⟨1636409, by rfl⟩ : syracuseStep 2181879 = 3272819) B3272819
theorem B2656981 : Blo 2181435 2656981 := bbase (se 7 (by rfl) ⟨31136, by rfl⟩ : syracuseStep 2656981 = 62273) (by norm_num)
theorem B3542641 : Blo 2181435 3542641 := bstep (se 2 (by rfl) ⟨1328490, by rfl⟩ : syracuseStep 3542641 = 2656981) B2656981
theorem B75576341 : Blo 2181435 75576341 := bstep (se 6 (by rfl) ⟨1771320, by rfl⟩ : syracuseStep 75576341 = 3542641) B3542641
theorem B50384227 : Blo 2181435 50384227 := bstep (se 1 (by rfl) ⟨37788170, by rfl⟩ : syracuseStep 50384227 = 75576341) B75576341
theorem B67178969 : Blo 2181435 67178969 := bstep (se 2 (by rfl) ⟨25192113, by rfl⟩ : syracuseStep 67178969 = 50384227) B50384227
theorem B44785979 : Blo 2181435 44785979 := bstep (se 1 (by rfl) ⟨33589484, by rfl⟩ : syracuseStep 44785979 = 67178969) B67178969
theorem B29857319 : Blo 2181435 29857319 := bstep (se 1 (by rfl) ⟨22392989, by rfl⟩ : syracuseStep 29857319 = 44785979) B44785979
theorem B19904879 : Blo 2181435 19904879 := bstep (se 1 (by rfl) ⟨14928659, by rfl⟩ : syracuseStep 19904879 = 29857319) B29857319
theorem B13269919 : Blo 2181435 13269919 := bstep (se 1 (by rfl) ⟨9952439, by rfl⟩ : syracuseStep 13269919 = 19904879) B19904879
theorem B17693225 : Blo 2181435 17693225 := bstep (se 2 (by rfl) ⟨6634959, by rfl⟩ : syracuseStep 17693225 = 13269919) B13269919
theorem B11795483 : Blo 2181435 11795483 := bstep (se 1 (by rfl) ⟨8846612, by rfl⟩ : syracuseStep 11795483 = 17693225) B17693225
theorem B7863655 : Blo 2181435 7863655 := bstep (se 1 (by rfl) ⟨5897741, by rfl⟩ : syracuseStep 7863655 = 11795483) B11795483
theorem B10484873 : Blo 2181435 10484873 := bstep (se 2 (by rfl) ⟨3931827, by rfl⟩ : syracuseStep 10484873 = 7863655) B7863655
theorem B6989915 : Blo 2181435 6989915 := bstep (se 1 (by rfl) ⟨5242436, by rfl⟩ : syracuseStep 6989915 = 10484873) B10484873
theorem B4659943 : Blo 2181435 4659943 := bstep (se 1 (by rfl) ⟨3494957, by rfl⟩ : syracuseStep 4659943 = 6989915) B6989915
theorem B6213257 : Blo 2181435 6213257 := bstep (se 2 (by rfl) ⟨2329971, by rfl⟩ : syracuseStep 6213257 = 4659943) B4659943
theorem B4142171 : Blo 2181435 4142171 := bstep (se 1 (by rfl) ⟨3106628, by rfl⟩ : syracuseStep 4142171 = 6213257) B6213257
theorem B2761447 : Blo 2181435 2761447 := bstep (se 1 (by rfl) ⟨2071085, by rfl⟩ : syracuseStep 2761447 = 4142171) B4142171
theorem B3681929 : Blo 2181435 3681929 := bstep (se 2 (by rfl) ⟨1380723, by rfl⟩ : syracuseStep 3681929 = 2761447) B2761447
theorem B2454619 : Blo 2181435 2454619 := bstep (se 1 (by rfl) ⟨1840964, by rfl⟩ : syracuseStep 2454619 = 3681929) B3681929
theorem B3272825 : Blo 2181435 3272825 := bstep (se 2 (by rfl) ⟨1227309, by rfl⟩ : syracuseStep 3272825 = 2454619) B2454619
theorem B2181883 : Blo 2181435 2181883 := bstep (se 1 (by rfl) ⟨1636412, by rfl⟩ : syracuseStep 2181883 = 3272825) B3272825
theorem B27959701 : Blo 2181435 27959701 := bbase (se 6 (by rfl) ⟨655305, by rfl⟩ : syracuseStep 27959701 = 1310611) (by norm_num)
theorem B37279601 : Blo 2181435 37279601 := bstep (se 2 (by rfl) ⟨13979850, by rfl⟩ : syracuseStep 37279601 = 27959701) B27959701
theorem B24853067 : Blo 2181435 24853067 := bstep (se 1 (by rfl) ⟨18639800, by rfl⟩ : syracuseStep 24853067 = 37279601) B37279601
theorem B16568711 : Blo 2181435 16568711 := bstep (se 1 (by rfl) ⟨12426533, by rfl⟩ : syracuseStep 16568711 = 24853067) B24853067
theorem B11045807 : Blo 2181435 11045807 := bstep (se 1 (by rfl) ⟨8284355, by rfl⟩ : syracuseStep 11045807 = 16568711) B16568711
theorem B7363871 : Blo 2181435 7363871 := bstep (se 1 (by rfl) ⟨5522903, by rfl⟩ : syracuseStep 7363871 = 11045807) B11045807
theorem B4909247 : Blo 2181435 4909247 := bstep (se 1 (by rfl) ⟨3681935, by rfl⟩ : syracuseStep 4909247 = 7363871) B7363871
theorem B3272831 : Blo 2181435 3272831 := bstep (se 1 (by rfl) ⟨2454623, by rfl⟩ : syracuseStep 3272831 = 4909247) B4909247
theorem B2181887 : Blo 2181435 2181887 := bstep (se 1 (by rfl) ⟨1636415, by rfl⟩ : syracuseStep 2181887 = 3272831) B3272831
theorem B3272837 : Blo 2181435 3272837 := bbase (se 4 (by rfl) ⟨306828, by rfl⟩ : syracuseStep 3272837 = 613657) (by norm_num)
theorem B2181891 : Blo 2181435 2181891 := bstep (se 1 (by rfl) ⟨1636418, by rfl⟩ : syracuseStep 2181891 = 3272837) B3272837
theorem B3681949 : Blo 2181435 3681949 := bbase (se 3 (by rfl) ⟨690365, by rfl⟩ : syracuseStep 3681949 = 1380731) (by norm_num)
theorem B4909265 : Blo 2181435 4909265 := bstep (se 2 (by rfl) ⟨1840974, by rfl⟩ : syracuseStep 4909265 = 3681949) B3681949
theorem B3272843 : Blo 2181435 3272843 := bstep (se 1 (by rfl) ⟨2454632, by rfl⟩ : syracuseStep 3272843 = 4909265) B4909265
theorem B2181895 : Blo 2181435 2181895 := bstep (se 1 (by rfl) ⟨1636421, by rfl⟩ : syracuseStep 2181895 = 3272843) B3272843
theorem B2454637 : Blo 2181435 2454637 := bbase (se 3 (by rfl) ⟨460244, by rfl⟩ : syracuseStep 2454637 = 920489) (by norm_num)
theorem B3272849 : Blo 2181435 3272849 := bstep (se 2 (by rfl) ⟨1227318, by rfl⟩ : syracuseStep 3272849 = 2454637) B2454637
theorem B2181899 : Blo 2181435 2181899 := bstep (se 1 (by rfl) ⟨1636424, by rfl⟩ : syracuseStep 2181899 = 3272849) B3272849
theorem B7363925 : Blo 2181435 7363925 := bbase (se 11 (by rfl) ⟨5393, by rfl⟩ : syracuseStep 7363925 = 10787) (by norm_num)
theorem B4909283 : Blo 2181435 4909283 := bstep (se 1 (by rfl) ⟨3681962, by rfl⟩ : syracuseStep 4909283 = 7363925) B7363925
theorem B3272855 : Blo 2181435 3272855 := bstep (se 1 (by rfl) ⟨2454641, by rfl⟩ : syracuseStep 3272855 = 4909283) B4909283
theorem B2181903 : Blo 2181435 2181903 := bstep (se 1 (by rfl) ⟨1636427, by rfl⟩ : syracuseStep 2181903 = 3272855) B3272855
theorem B3272861 : Blo 2181435 3272861 := bbase (se 3 (by rfl) ⟨613661, by rfl⟩ : syracuseStep 3272861 = 1227323) (by norm_num)
theorem B2181907 : Blo 2181435 2181907 := bstep (se 1 (by rfl) ⟨1636430, by rfl⟩ : syracuseStep 2181907 = 3272861) B3272861
theorem B4909301 : Blo 2181435 4909301 := bbase (se 5 (by rfl) ⟨230123, by rfl⟩ : syracuseStep 4909301 = 460247) (by norm_num)
theorem B3272867 : Blo 2181435 3272867 := bstep (se 1 (by rfl) ⟨2454650, by rfl⟩ : syracuseStep 3272867 = 4909301) B4909301
theorem B2181911 : Blo 2181435 2181911 := bstep (se 1 (by rfl) ⟨1636433, by rfl⟩ : syracuseStep 2181911 = 3272867) B3272867
theorem B2211685 : Blo 2181435 2211685 := bbase (se 4 (by rfl) ⟨207345, by rfl⟩ : syracuseStep 2211685 = 414691) (by norm_num)
theorem B11795653 : Blo 2181435 11795653 := bstep (se 4 (by rfl) ⟨1105842, by rfl⟩ : syracuseStep 11795653 = 2211685) B2211685
theorem B15727537 : Blo 2181435 15727537 := bstep (se 2 (by rfl) ⟨5897826, by rfl⟩ : syracuseStep 15727537 = 11795653) B11795653
theorem B20970049 : Blo 2181435 20970049 := bstep (se 2 (by rfl) ⟨7863768, by rfl⟩ : syracuseStep 20970049 = 15727537) B15727537
theorem B27960065 : Blo 2181435 27960065 := bstep (se 2 (by rfl) ⟨10485024, by rfl⟩ : syracuseStep 27960065 = 20970049) B20970049
theorem B18640043 : Blo 2181435 18640043 := bstep (se 1 (by rfl) ⟨13980032, by rfl⟩ : syracuseStep 18640043 = 27960065) B27960065
theorem B12426695 : Blo 2181435 12426695 := bstep (se 1 (by rfl) ⟨9320021, by rfl⟩ : syracuseStep 12426695 = 18640043) B18640043
theorem B8284463 : Blo 2181435 8284463 := bstep (se 1 (by rfl) ⟨6213347, by rfl⟩ : syracuseStep 8284463 = 12426695) B12426695
theorem B5522975 : Blo 2181435 5522975 := bstep (se 1 (by rfl) ⟨4142231, by rfl⟩ : syracuseStep 5522975 = 8284463) B8284463
theorem B3681983 : Blo 2181435 3681983 := bstep (se 1 (by rfl) ⟨2761487, by rfl⟩ : syracuseStep 3681983 = 5522975) B5522975
theorem B2454655 : Blo 2181435 2454655 := bstep (se 1 (by rfl) ⟨1840991, by rfl⟩ : syracuseStep 2454655 = 3681983) B3681983
theorem B3272873 : Blo 2181435 3272873 := bstep (se 2 (by rfl) ⟨1227327, by rfl⟩ : syracuseStep 3272873 = 2454655) B2454655
theorem B2181915 : Blo 2181435 2181915 := bstep (se 1 (by rfl) ⟨1636436, by rfl⟩ : syracuseStep 2181915 = 3272873) B3272873
theorem B2621261 : Blo 2181435 2621261 := bbase (se 3 (by rfl) ⟨491486, by rfl⟩ : syracuseStep 2621261 = 982973) (by norm_num)
theorem B6990029 : Blo 2181435 6990029 := bstep (se 3 (by rfl) ⟨1310630, by rfl⟩ : syracuseStep 6990029 = 2621261) B2621261
theorem B4660019 : Blo 2181435 4660019 := bstep (se 1 (by rfl) ⟨3495014, by rfl⟩ : syracuseStep 4660019 = 6990029) B6990029
theorem B3106679 : Blo 2181435 3106679 := bstep (se 1 (by rfl) ⟨2330009, by rfl⟩ : syracuseStep 3106679 = 4660019) B4660019
theorem B8284477 : Blo 2181435 8284477 := bstep (se 3 (by rfl) ⟨1553339, by rfl⟩ : syracuseStep 8284477 = 3106679) B3106679
theorem B11045969 : Blo 2181435 11045969 := bstep (se 2 (by rfl) ⟨4142238, by rfl⟩ : syracuseStep 11045969 = 8284477) B8284477
theorem B7363979 : Blo 2181435 7363979 := bstep (se 1 (by rfl) ⟨5522984, by rfl⟩ : syracuseStep 7363979 = 11045969) B11045969
theorem B4909319 : Blo 2181435 4909319 := bstep (se 1 (by rfl) ⟨3681989, by rfl⟩ : syracuseStep 4909319 = 7363979) B7363979
theorem B3272879 : Blo 2181435 3272879 := bstep (se 1 (by rfl) ⟨2454659, by rfl⟩ : syracuseStep 3272879 = 4909319) B4909319
theorem B2181919 : Blo 2181435 2181919 := bstep (se 1 (by rfl) ⟨1636439, by rfl⟩ : syracuseStep 2181919 = 3272879) B3272879
theorem B3272885 : Blo 2181435 3272885 := bbase (se 5 (by rfl) ⟨153416, by rfl⟩ : syracuseStep 3272885 = 306833) (by norm_num)
theorem B2181923 : Blo 2181435 2181923 := bstep (se 1 (by rfl) ⟨1636442, by rfl⟩ : syracuseStep 2181923 = 3272885) B3272885
theorem B5523005 : Blo 2181435 5523005 := bbase (se 3 (by rfl) ⟨1035563, by rfl⟩ : syracuseStep 5523005 = 2071127) (by norm_num)
theorem B3682003 : Blo 2181435 3682003 := bstep (se 1 (by rfl) ⟨2761502, by rfl⟩ : syracuseStep 3682003 = 5523005) B5523005
theorem B4909337 : Blo 2181435 4909337 := bstep (se 2 (by rfl) ⟨1841001, by rfl⟩ : syracuseStep 4909337 = 3682003) B3682003
theorem B3272891 : Blo 2181435 3272891 := bstep (se 1 (by rfl) ⟨2454668, by rfl⟩ : syracuseStep 3272891 = 4909337) B4909337
theorem B2181927 : Blo 2181435 2181927 := bstep (se 1 (by rfl) ⟨1636445, by rfl⟩ : syracuseStep 2181927 = 3272891) B3272891
theorem B2454673 : Blo 2181435 2454673 := bbase (se 2 (by rfl) ⟨920502, by rfl⟩ : syracuseStep 2454673 = 1841005) (by norm_num)
theorem B3272897 : Blo 2181435 3272897 := bstep (se 2 (by rfl) ⟨1227336, by rfl⟩ : syracuseStep 3272897 = 2454673) B2454673
theorem B2181931 : Blo 2181435 2181931 := bstep (se 1 (by rfl) ⟨1636448, by rfl⟩ : syracuseStep 2181931 = 3272897) B3272897
theorem B4142269 : Blo 2181435 4142269 := bbase (se 3 (by rfl) ⟨776675, by rfl⟩ : syracuseStep 4142269 = 1553351) (by norm_num)
theorem B5523025 : Blo 2181435 5523025 := bstep (se 2 (by rfl) ⟨2071134, by rfl⟩ : syracuseStep 5523025 = 4142269) B4142269
theorem B7364033 : Blo 2181435 7364033 := bstep (se 2 (by rfl) ⟨2761512, by rfl⟩ : syracuseStep 7364033 = 5523025) B5523025
theorem B4909355 : Blo 2181435 4909355 := bstep (se 1 (by rfl) ⟨3682016, by rfl⟩ : syracuseStep 4909355 = 7364033) B7364033
theorem B3272903 : Blo 2181435 3272903 := bstep (se 1 (by rfl) ⟨2454677, by rfl⟩ : syracuseStep 3272903 = 4909355) B4909355
theorem B2181935 : Blo 2181435 2181935 := bstep (se 1 (by rfl) ⟨1636451, by rfl⟩ : syracuseStep 2181935 = 3272903) B3272903
theorem B3272909 : Blo 2181435 3272909 := bbase (se 3 (by rfl) ⟨613670, by rfl⟩ : syracuseStep 3272909 = 1227341) (by norm_num)
theorem B2181939 : Blo 2181435 2181939 := bstep (se 1 (by rfl) ⟨1636454, by rfl⟩ : syracuseStep 2181939 = 3272909) B3272909
theorem B4909373 : Blo 2181435 4909373 := bbase (se 3 (by rfl) ⟨920507, by rfl⟩ : syracuseStep 4909373 = 1841015) (by norm_num)
theorem B3272915 : Blo 2181435 3272915 := bstep (se 1 (by rfl) ⟨2454686, by rfl⟩ : syracuseStep 3272915 = 4909373) B4909373
theorem B2181943 : Blo 2181435 2181943 := bstep (se 1 (by rfl) ⟨1636457, by rfl⟩ : syracuseStep 2181943 = 3272915) B3272915
theorem B3682037 : Blo 2181435 3682037 := bbase (se 5 (by rfl) ⟨172595, by rfl⟩ : syracuseStep 3682037 = 345191) (by norm_num)
theorem B2454691 : Blo 2181435 2454691 := bstep (se 1 (by rfl) ⟨1841018, by rfl⟩ : syracuseStep 2454691 = 3682037) B3682037
theorem B3272921 : Blo 2181435 3272921 := bstep (se 2 (by rfl) ⟨1227345, by rfl⟩ : syracuseStep 3272921 = 2454691) B2454691
theorem B2181947 : Blo 2181435 2181947 := bstep (se 1 (by rfl) ⟨1636460, by rfl⟩ : syracuseStep 2181947 = 3272921) B3272921
theorem B3931949 : Blo 2181435 3931949 := bbase (se 3 (by rfl) ⟨737240, by rfl⟩ : syracuseStep 3931949 = 1474481) (by norm_num)
theorem B10485197 : Blo 2181435 10485197 := bstep (se 3 (by rfl) ⟨1965974, by rfl⟩ : syracuseStep 10485197 = 3931949) B3931949
theorem B6990131 : Blo 2181435 6990131 := bstep (se 1 (by rfl) ⟨5242598, by rfl⟩ : syracuseStep 6990131 = 10485197) B10485197
theorem B4660087 : Blo 2181435 4660087 := bstep (se 1 (by rfl) ⟨3495065, by rfl⟩ : syracuseStep 4660087 = 6990131) B6990131
theorem B6213449 : Blo 2181435 6213449 := bstep (se 2 (by rfl) ⟨2330043, by rfl⟩ : syracuseStep 6213449 = 4660087) B4660087
theorem B16569197 : Blo 2181435 16569197 := bstep (se 3 (by rfl) ⟨3106724, by rfl⟩ : syracuseStep 16569197 = 6213449) B6213449
theorem B11046131 : Blo 2181435 11046131 := bstep (se 1 (by rfl) ⟨8284598, by rfl⟩ : syracuseStep 11046131 = 16569197) B16569197
theorem B7364087 : Blo 2181435 7364087 := bstep (se 1 (by rfl) ⟨5523065, by rfl⟩ : syracuseStep 7364087 = 11046131) B11046131
theorem B4909391 : Blo 2181435 4909391 := bstep (se 1 (by rfl) ⟨3682043, by rfl⟩ : syracuseStep 4909391 = 7364087) B7364087
theorem B3272927 : Blo 2181435 3272927 := bstep (se 1 (by rfl) ⟨2454695, by rfl⟩ : syracuseStep 3272927 = 4909391) B4909391
theorem B2181951 : Blo 2181435 2181951 := bstep (se 1 (by rfl) ⟨1636463, by rfl⟩ : syracuseStep 2181951 = 3272927) B3272927
theorem B3272933 : Blo 2181435 3272933 := bbase (se 4 (by rfl) ⟨306837, by rfl⟩ : syracuseStep 3272933 = 613675) (by norm_num)
theorem B2181955 : Blo 2181435 2181955 := bstep (se 1 (by rfl) ⟨1636466, by rfl⟩ : syracuseStep 2181955 = 3272933) B3272933
theorem B17935253 : Blo 2181435 17935253 := bbase (se 6 (by rfl) ⟨420357, by rfl⟩ : syracuseStep 17935253 = 840715) (by norm_num)
theorem B11956835 : Blo 2181435 11956835 := bstep (se 1 (by rfl) ⟨8967626, by rfl⟩ : syracuseStep 11956835 = 17935253) B17935253
theorem B7971223 : Blo 2181435 7971223 := bstep (se 1 (by rfl) ⟨5978417, by rfl⟩ : syracuseStep 7971223 = 11956835) B11956835
theorem B10628297 : Blo 2181435 10628297 := bstep (se 2 (by rfl) ⟨3985611, by rfl⟩ : syracuseStep 10628297 = 7971223) B7971223
theorem B7085531 : Blo 2181435 7085531 := bstep (se 1 (by rfl) ⟨5314148, by rfl⟩ : syracuseStep 7085531 = 10628297) B10628297
theorem B4723687 : Blo 2181435 4723687 := bstep (se 1 (by rfl) ⟨3542765, by rfl⟩ : syracuseStep 4723687 = 7085531) B7085531
theorem B6298249 : Blo 2181435 6298249 := bstep (se 2 (by rfl) ⟨2361843, by rfl⟩ : syracuseStep 6298249 = 4723687) B4723687
theorem B8397665 : Blo 2181435 8397665 := bstep (se 2 (by rfl) ⟨3149124, by rfl⟩ : syracuseStep 8397665 = 6298249) B6298249
theorem B5598443 : Blo 2181435 5598443 := bstep (se 1 (by rfl) ⟨4198832, by rfl⟩ : syracuseStep 5598443 = 8397665) B8397665
theorem B14929181 : Blo 2181435 14929181 := bstep (se 3 (by rfl) ⟨2799221, by rfl⟩ : syracuseStep 14929181 = 5598443) B5598443
theorem B9952787 : Blo 2181435 9952787 := bstep (se 1 (by rfl) ⟨7464590, by rfl⟩ : syracuseStep 9952787 = 14929181) B14929181
theorem B6635191 : Blo 2181435 6635191 := bstep (se 1 (by rfl) ⟨4976393, by rfl⟩ : syracuseStep 6635191 = 9952787) B9952787
theorem B8846921 : Blo 2181435 8846921 := bstep (se 2 (by rfl) ⟨3317595, by rfl⟩ : syracuseStep 8846921 = 6635191) B6635191
theorem B5897947 : Blo 2181435 5897947 := bstep (se 1 (by rfl) ⟨4423460, by rfl⟩ : syracuseStep 5897947 = 8846921) B8846921
theorem B7863929 : Blo 2181435 7863929 := bstep (se 2 (by rfl) ⟨2948973, by rfl⟩ : syracuseStep 7863929 = 5897947) B5897947
theorem B5242619 : Blo 2181435 5242619 := bstep (se 1 (by rfl) ⟨3931964, by rfl⟩ : syracuseStep 5242619 = 7863929) B7863929
theorem B3495079 : Blo 2181435 3495079 := bstep (se 1 (by rfl) ⟨2621309, by rfl⟩ : syracuseStep 3495079 = 5242619) B5242619
theorem B4660105 : Blo 2181435 4660105 := bstep (se 2 (by rfl) ⟨1747539, by rfl⟩ : syracuseStep 4660105 = 3495079) B3495079
theorem B6213473 : Blo 2181435 6213473 := bstep (se 2 (by rfl) ⟨2330052, by rfl⟩ : syracuseStep 6213473 = 4660105) B4660105
theorem B4142315 : Blo 2181435 4142315 := bstep (se 1 (by rfl) ⟨3106736, by rfl⟩ : syracuseStep 4142315 = 6213473) B6213473
theorem B2761543 : Blo 2181435 2761543 := bstep (se 1 (by rfl) ⟨2071157, by rfl⟩ : syracuseStep 2761543 = 4142315) B4142315
theorem B3682057 : Blo 2181435 3682057 := bstep (se 2 (by rfl) ⟨1380771, by rfl⟩ : syracuseStep 3682057 = 2761543) B2761543
theorem B4909409 : Blo 2181435 4909409 := bstep (se 2 (by rfl) ⟨1841028, by rfl⟩ : syracuseStep 4909409 = 3682057) B3682057
theorem B3272939 : Blo 2181435 3272939 := bstep (se 1 (by rfl) ⟨2454704, by rfl⟩ : syracuseStep 3272939 = 4909409) B4909409
theorem B2181959 : Blo 2181435 2181959 := bstep (se 1 (by rfl) ⟨1636469, by rfl⟩ : syracuseStep 2181959 = 3272939) B3272939
theorem B2454709 : Blo 2181435 2454709 := bbase (se 5 (by rfl) ⟨115064, by rfl⟩ : syracuseStep 2454709 = 230129) (by norm_num)
theorem B3272945 : Blo 2181435 3272945 := bstep (se 2 (by rfl) ⟨1227354, by rfl⟩ : syracuseStep 3272945 = 2454709) B2454709
theorem B2181963 : Blo 2181435 2181963 := bstep (se 1 (by rfl) ⟨1636472, by rfl⟩ : syracuseStep 2181963 = 3272945) B3272945
theorem B2761553 : Blo 2181435 2761553 := bbase (se 2 (by rfl) ⟨1035582, by rfl⟩ : syracuseStep 2761553 = 2071165) (by norm_num)
theorem B7364141 : Blo 2181435 7364141 := bstep (se 3 (by rfl) ⟨1380776, by rfl⟩ : syracuseStep 7364141 = 2761553) B2761553
theorem B4909427 : Blo 2181435 4909427 := bstep (se 1 (by rfl) ⟨3682070, by rfl⟩ : syracuseStep 4909427 = 7364141) B7364141
theorem B3272951 : Blo 2181435 3272951 := bstep (se 1 (by rfl) ⟨2454713, by rfl⟩ : syracuseStep 3272951 = 4909427) B4909427
theorem B2181967 : Blo 2181435 2181967 := bstep (se 1 (by rfl) ⟨1636475, by rfl⟩ : syracuseStep 2181967 = 3272951) B3272951
theorem B3272957 : Blo 2181435 3272957 := bbase (se 3 (by rfl) ⟨613679, by rfl⟩ : syracuseStep 3272957 = 1227359) (by norm_num)
theorem B2181971 : Blo 2181435 2181971 := bstep (se 1 (by rfl) ⟨1636478, by rfl⟩ : syracuseStep 2181971 = 3272957) B3272957
theorem B4909445 : Blo 2181435 4909445 := bbase (se 4 (by rfl) ⟨460260, by rfl⟩ : syracuseStep 4909445 = 920521) (by norm_num)
theorem B3272963 : Blo 2181435 3272963 := bstep (se 1 (by rfl) ⟨2454722, by rfl⟩ : syracuseStep 3272963 = 4909445) B4909445
theorem B2181975 : Blo 2181435 2181975 := bstep (se 1 (by rfl) ⟨1636481, by rfl⟩ : syracuseStep 2181975 = 3272963) B3272963
theorem B3106765 : Blo 2181435 3106765 := bbase (se 3 (by rfl) ⟨582518, by rfl⟩ : syracuseStep 3106765 = 1165037) (by norm_num)
theorem B4142353 : Blo 2181435 4142353 := bstep (se 2 (by rfl) ⟨1553382, by rfl⟩ : syracuseStep 4142353 = 3106765) B3106765
theorem B5523137 : Blo 2181435 5523137 := bstep (se 2 (by rfl) ⟨2071176, by rfl⟩ : syracuseStep 5523137 = 4142353) B4142353
theorem B3682091 : Blo 2181435 3682091 := bstep (se 1 (by rfl) ⟨2761568, by rfl⟩ : syracuseStep 3682091 = 5523137) B5523137
theorem B2454727 : Blo 2181435 2454727 := bstep (se 1 (by rfl) ⟨1841045, by rfl⟩ : syracuseStep 2454727 = 3682091) B3682091
theorem B3272969 : Blo 2181435 3272969 := bstep (se 2 (by rfl) ⟨1227363, by rfl⟩ : syracuseStep 3272969 = 2454727) B2454727
theorem B2181979 : Blo 2181435 2181979 := bstep (se 1 (by rfl) ⟨1636484, by rfl⟩ : syracuseStep 2181979 = 3272969) B3272969
theorem B11046293 : Blo 2181435 11046293 := bbase (se 6 (by rfl) ⟨258897, by rfl⟩ : syracuseStep 11046293 = 517795) (by norm_num)
theorem B7364195 : Blo 2181435 7364195 := bstep (se 1 (by rfl) ⟨5523146, by rfl⟩ : syracuseStep 7364195 = 11046293) B11046293
theorem B4909463 : Blo 2181435 4909463 := bstep (se 1 (by rfl) ⟨3682097, by rfl⟩ : syracuseStep 4909463 = 7364195) B7364195
theorem B3272975 : Blo 2181435 3272975 := bstep (se 1 (by rfl) ⟨2454731, by rfl⟩ : syracuseStep 3272975 = 4909463) B4909463
theorem B2181983 : Blo 2181435 2181983 := bstep (se 1 (by rfl) ⟨1636487, by rfl⟩ : syracuseStep 2181983 = 3272975) B3272975
theorem B3272981 : Blo 2181435 3272981 := bbase (se 6 (by rfl) ⟨76710, by rfl⟩ : syracuseStep 3272981 = 153421) (by norm_num)
theorem B2181987 : Blo 2181435 2181987 := bstep (se 1 (by rfl) ⟨1636490, by rfl⟩ : syracuseStep 2181987 = 3272981) B3272981
theorem B3932021 : Blo 2181435 3932021 := bbase (se 5 (by rfl) ⟨184313, by rfl⟩ : syracuseStep 3932021 = 368627) (by norm_num)
theorem B10485389 : Blo 2181435 10485389 := bstep (se 3 (by rfl) ⟨1966010, by rfl⟩ : syracuseStep 10485389 = 3932021) B3932021
theorem B27961037 : Blo 2181435 27961037 := bstep (se 3 (by rfl) ⟨5242694, by rfl⟩ : syracuseStep 27961037 = 10485389) B10485389
theorem B18640691 : Blo 2181435 18640691 := bstep (se 1 (by rfl) ⟨13980518, by rfl⟩ : syracuseStep 18640691 = 27961037) B27961037
theorem B12427127 : Blo 2181435 12427127 := bstep (se 1 (by rfl) ⟨9320345, by rfl⟩ : syracuseStep 12427127 = 18640691) B18640691
theorem B8284751 : Blo 2181435 8284751 := bstep (se 1 (by rfl) ⟨6213563, by rfl⟩ : syracuseStep 8284751 = 12427127) B12427127
theorem B5523167 : Blo 2181435 5523167 := bstep (se 1 (by rfl) ⟨4142375, by rfl⟩ : syracuseStep 5523167 = 8284751) B8284751
theorem B3682111 : Blo 2181435 3682111 := bstep (se 1 (by rfl) ⟨2761583, by rfl⟩ : syracuseStep 3682111 = 5523167) B5523167
theorem B4909481 : Blo 2181435 4909481 := bstep (se 2 (by rfl) ⟨1841055, by rfl⟩ : syracuseStep 4909481 = 3682111) B3682111
theorem B3272987 : Blo 2181435 3272987 := bstep (se 1 (by rfl) ⟨2454740, by rfl⟩ : syracuseStep 3272987 = 4909481) B4909481
theorem B2181991 : Blo 2181435 2181991 := bstep (se 1 (by rfl) ⟨1636493, by rfl⟩ : syracuseStep 2181991 = 3272987) B3272987
theorem B2454745 : Blo 2181435 2454745 := bbase (se 2 (by rfl) ⟨920529, by rfl⟩ : syracuseStep 2454745 = 1841059) (by norm_num)
theorem B3272993 : Blo 2181435 3272993 := bstep (se 2 (by rfl) ⟨1227372, by rfl⟩ : syracuseStep 3272993 = 2454745) B2454745
theorem B2181995 : Blo 2181435 2181995 := bstep (se 1 (by rfl) ⟨1636496, by rfl⟩ : syracuseStep 2181995 = 3272993) B3272993
theorem B16795637 : Blo 2181435 16795637 := bbase (se 5 (by rfl) ⟨787295, by rfl⟩ : syracuseStep 16795637 = 1574591) (by norm_num)
theorem B11197091 : Blo 2181435 11197091 := bstep (se 1 (by rfl) ⟨8397818, by rfl⟩ : syracuseStep 11197091 = 16795637) B16795637
theorem B7464727 : Blo 2181435 7464727 := bstep (se 1 (by rfl) ⟨5598545, by rfl⟩ : syracuseStep 7464727 = 11197091) B11197091
theorem B9952969 : Blo 2181435 9952969 := bstep (se 2 (by rfl) ⟨3732363, by rfl⟩ : syracuseStep 9952969 = 7464727) B7464727
theorem B13270625 : Blo 2181435 13270625 := bstep (se 2 (by rfl) ⟨4976484, by rfl⟩ : syracuseStep 13270625 = 9952969) B9952969
theorem B8847083 : Blo 2181435 8847083 := bstep (se 1 (by rfl) ⟨6635312, by rfl⟩ : syracuseStep 8847083 = 13270625) B13270625
theorem B5898055 : Blo 2181435 5898055 := bstep (se 1 (by rfl) ⟨4423541, by rfl⟩ : syracuseStep 5898055 = 8847083) B8847083
theorem B7864073 : Blo 2181435 7864073 := bstep (se 2 (by rfl) ⟨2949027, by rfl⟩ : syracuseStep 7864073 = 5898055) B5898055
theorem B5242715 : Blo 2181435 5242715 := bstep (se 1 (by rfl) ⟨3932036, by rfl⟩ : syracuseStep 5242715 = 7864073) B7864073
theorem B3495143 : Blo 2181435 3495143 := bstep (se 1 (by rfl) ⟨2621357, by rfl⟩ : syracuseStep 3495143 = 5242715) B5242715
theorem B2330095 : Blo 2181435 2330095 := bstep (se 1 (by rfl) ⟨1747571, by rfl⟩ : syracuseStep 2330095 = 3495143) B3495143
theorem B3106793 : Blo 2181435 3106793 := bstep (se 2 (by rfl) ⟨1165047, by rfl⟩ : syracuseStep 3106793 = 2330095) B2330095
theorem B8284781 : Blo 2181435 8284781 := bstep (se 3 (by rfl) ⟨1553396, by rfl⟩ : syracuseStep 8284781 = 3106793) B3106793
theorem B5523187 : Blo 2181435 5523187 := bstep (se 1 (by rfl) ⟨4142390, by rfl⟩ : syracuseStep 5523187 = 8284781) B8284781
theorem B7364249 : Blo 2181435 7364249 := bstep (se 2 (by rfl) ⟨2761593, by rfl⟩ : syracuseStep 7364249 = 5523187) B5523187
theorem B4909499 : Blo 2181435 4909499 := bstep (se 1 (by rfl) ⟨3682124, by rfl⟩ : syracuseStep 4909499 = 7364249) B7364249
theorem B3272999 : Blo 2181435 3272999 := bstep (se 1 (by rfl) ⟨2454749, by rfl⟩ : syracuseStep 3272999 = 4909499) B4909499
theorem B2181999 : Blo 2181435 2181999 := bstep (se 1 (by rfl) ⟨1636499, by rfl⟩ : syracuseStep 2181999 = 3272999) B3272999
theorem B3273005 : Blo 2181435 3273005 := bbase (se 3 (by rfl) ⟨613688, by rfl⟩ : syracuseStep 3273005 = 1227377) (by norm_num)
theorem B2182003 : Blo 2181435 2182003 := bstep (se 1 (by rfl) ⟨1636502, by rfl⟩ : syracuseStep 2182003 = 3273005) B3273005
theorem B4909517 : Blo 2181435 4909517 := bbase (se 3 (by rfl) ⟨920534, by rfl⟩ : syracuseStep 4909517 = 1841069) (by norm_num)
theorem B3273011 : Blo 2181435 3273011 := bstep (se 1 (by rfl) ⟨2454758, by rfl⟩ : syracuseStep 3273011 = 4909517) B4909517
theorem B2182007 : Blo 2181435 2182007 := bstep (se 1 (by rfl) ⟨1636505, by rfl⟩ : syracuseStep 2182007 = 3273011) B3273011
theorem B2761609 : Blo 2181435 2761609 := bbase (se 2 (by rfl) ⟨1035603, by rfl⟩ : syracuseStep 2761609 = 2071207) (by norm_num)
theorem B3682145 : Blo 2181435 3682145 := bstep (se 2 (by rfl) ⟨1380804, by rfl⟩ : syracuseStep 3682145 = 2761609) B2761609
theorem B2454763 : Blo 2181435 2454763 := bstep (se 1 (by rfl) ⟨1841072, by rfl⟩ : syracuseStep 2454763 = 3682145) B3682145
theorem B3273017 : Blo 2181435 3273017 := bstep (se 2 (by rfl) ⟨1227381, by rfl⟩ : syracuseStep 3273017 = 2454763) B2454763
theorem B2182011 : Blo 2181435 2182011 := bstep (se 1 (by rfl) ⟨1636508, by rfl⟩ : syracuseStep 2182011 = 3273017) B3273017
theorem B95657045 : Blo 2181435 95657045 := bbase (se 8 (by rfl) ⟨560490, by rfl⟩ : syracuseStep 95657045 = 1120981) (by norm_num)
theorem B255085453 : Blo 2181435 255085453 := bstep (se 3 (by rfl) ⟨47828522, by rfl⟩ : syracuseStep 255085453 = 95657045) B95657045
theorem B340113937 : Blo 2181435 340113937 := bstep (se 2 (by rfl) ⟨127542726, by rfl⟩ : syracuseStep 340113937 = 255085453) B255085453
theorem B453485249 : Blo 2181435 453485249 := bstep (se 2 (by rfl) ⟨170056968, by rfl⟩ : syracuseStep 453485249 = 340113937) B340113937
theorem B302323499 : Blo 2181435 302323499 := bstep (se 1 (by rfl) ⟨226742624, by rfl⟩ : syracuseStep 302323499 = 453485249) B453485249
theorem B201548999 : Blo 2181435 201548999 := bstep (se 1 (by rfl) ⟨151161749, by rfl⟩ : syracuseStep 201548999 = 302323499) B302323499
theorem B537463997 : Blo 2181435 537463997 := bstep (se 3 (by rfl) ⟨100774499, by rfl⟩ : syracuseStep 537463997 = 201548999) B201548999
theorem B358309331 : Blo 2181435 358309331 := bstep (se 1 (by rfl) ⟨268731998, by rfl⟩ : syracuseStep 358309331 = 537463997) B537463997
theorem B238872887 : Blo 2181435 238872887 := bstep (se 1 (by rfl) ⟨179154665, by rfl⟩ : syracuseStep 238872887 = 358309331) B358309331
theorem B159248591 : Blo 2181435 159248591 := bstep (se 1 (by rfl) ⟨119436443, by rfl⟩ : syracuseStep 159248591 = 238872887) B238872887
theorem B106165727 : Blo 2181435 106165727 := bstep (se 1 (by rfl) ⟨79624295, by rfl⟩ : syracuseStep 106165727 = 159248591) B159248591
theorem B70777151 : Blo 2181435 70777151 := bstep (se 1 (by rfl) ⟨53082863, by rfl⟩ : syracuseStep 70777151 = 106165727) B106165727
theorem B47184767 : Blo 2181435 47184767 := bstep (se 1 (by rfl) ⟨35388575, by rfl⟩ : syracuseStep 47184767 = 70777151) B70777151
theorem B31456511 : Blo 2181435 31456511 := bstep (se 1 (by rfl) ⟨23592383, by rfl⟩ : syracuseStep 31456511 = 47184767) B47184767
theorem B20971007 : Blo 2181435 20971007 := bstep (se 1 (by rfl) ⟨15728255, by rfl⟩ : syracuseStep 20971007 = 31456511) B31456511
theorem B13980671 : Blo 2181435 13980671 := bstep (se 1 (by rfl) ⟨10485503, by rfl⟩ : syracuseStep 13980671 = 20971007) B20971007
theorem B9320447 : Blo 2181435 9320447 := bstep (se 1 (by rfl) ⟨6990335, by rfl⟩ : syracuseStep 9320447 = 13980671) B13980671
theorem B24854525 : Blo 2181435 24854525 := bstep (se 3 (by rfl) ⟨4660223, by rfl⟩ : syracuseStep 24854525 = 9320447) B9320447
theorem B16569683 : Blo 2181435 16569683 := bstep (se 1 (by rfl) ⟨12427262, by rfl⟩ : syracuseStep 16569683 = 24854525) B24854525
theorem B11046455 : Blo 2181435 11046455 := bstep (se 1 (by rfl) ⟨8284841, by rfl⟩ : syracuseStep 11046455 = 16569683) B16569683
theorem B7364303 : Blo 2181435 7364303 := bstep (se 1 (by rfl) ⟨5523227, by rfl⟩ : syracuseStep 7364303 = 11046455) B11046455
theorem B4909535 : Blo 2181435 4909535 := bstep (se 1 (by rfl) ⟨3682151, by rfl⟩ : syracuseStep 4909535 = 7364303) B7364303
theorem B3273023 : Blo 2181435 3273023 := bstep (se 1 (by rfl) ⟨2454767, by rfl⟩ : syracuseStep 3273023 = 4909535) B4909535
theorem B2182015 : Blo 2181435 2182015 := bstep (se 1 (by rfl) ⟨1636511, by rfl⟩ : syracuseStep 2182015 = 3273023) B3273023
theorem B3273029 : Blo 2181435 3273029 := bbase (se 4 (by rfl) ⟨306846, by rfl⟩ : syracuseStep 3273029 = 613693) (by norm_num)
theorem B2182019 : Blo 2181435 2182019 := bstep (se 1 (by rfl) ⟨1636514, by rfl⟩ : syracuseStep 2182019 = 3273029) B3273029
theorem B3682165 : Blo 2181435 3682165 := bbase (se 5 (by rfl) ⟨172601, by rfl⟩ : syracuseStep 3682165 = 345203) (by norm_num)
theorem B4909553 : Blo 2181435 4909553 := bstep (se 2 (by rfl) ⟨1841082, by rfl⟩ : syracuseStep 4909553 = 3682165) B3682165
theorem B3273035 : Blo 2181435 3273035 := bstep (se 1 (by rfl) ⟨2454776, by rfl⟩ : syracuseStep 3273035 = 4909553) B4909553
theorem B2182023 : Blo 2181435 2182023 := bstep (se 1 (by rfl) ⟨1636517, by rfl⟩ : syracuseStep 2182023 = 3273035) B3273035
theorem B2454781 : Blo 2181435 2454781 := bbase (se 3 (by rfl) ⟨460271, by rfl⟩ : syracuseStep 2454781 = 920543) (by norm_num)
theorem B3273041 : Blo 2181435 3273041 := bstep (se 2 (by rfl) ⟨1227390, by rfl⟩ : syracuseStep 3273041 = 2454781) B2454781
theorem B2182027 : Blo 2181435 2182027 := bstep (se 1 (by rfl) ⟨1636520, by rfl⟩ : syracuseStep 2182027 = 3273041) B3273041
theorem B7364357 : Blo 2181435 7364357 := bbase (se 4 (by rfl) ⟨690408, by rfl⟩ : syracuseStep 7364357 = 1380817) (by norm_num)
theorem B4909571 : Blo 2181435 4909571 := bstep (se 1 (by rfl) ⟨3682178, by rfl⟩ : syracuseStep 4909571 = 7364357) B7364357
theorem B3273047 : Blo 2181435 3273047 := bstep (se 1 (by rfl) ⟨2454785, by rfl⟩ : syracuseStep 3273047 = 4909571) B4909571
theorem B2182031 : Blo 2181435 2182031 := bstep (se 1 (by rfl) ⟨1636523, by rfl⟩ : syracuseStep 2182031 = 3273047) B3273047
theorem B3273053 : Blo 2181435 3273053 := bbase (se 3 (by rfl) ⟨613697, by rfl⟩ : syracuseStep 3273053 = 1227395) (by norm_num)
theorem B2182035 : Blo 2181435 2182035 := bstep (se 1 (by rfl) ⟨1636526, by rfl⟩ : syracuseStep 2182035 = 3273053) B3273053
theorem B4909589 : Blo 2181435 4909589 := bbase (se 6 (by rfl) ⟨115068, by rfl⟩ : syracuseStep 4909589 = 230137) (by norm_num)
theorem B3273059 : Blo 2181435 3273059 := bstep (se 1 (by rfl) ⟨2454794, by rfl⟩ : syracuseStep 3273059 = 4909589) B4909589
theorem B2182039 : Blo 2181435 2182039 := bstep (se 1 (by rfl) ⟨1636529, by rfl⟩ : syracuseStep 2182039 = 3273059) B3273059
theorem B8284949 : Blo 2181435 8284949 := bbase (se 6 (by rfl) ⟨194178, by rfl⟩ : syracuseStep 8284949 = 388357) (by norm_num)
theorem B5523299 : Blo 2181435 5523299 := bstep (se 1 (by rfl) ⟨4142474, by rfl⟩ : syracuseStep 5523299 = 8284949) B8284949
theorem B3682199 : Blo 2181435 3682199 := bstep (se 1 (by rfl) ⟨2761649, by rfl⟩ : syracuseStep 3682199 = 5523299) B5523299
theorem B2454799 : Blo 2181435 2454799 := bstep (se 1 (by rfl) ⟨1841099, by rfl⟩ : syracuseStep 2454799 = 3682199) B3682199
theorem B3273065 : Blo 2181435 3273065 := bstep (se 2 (by rfl) ⟨1227399, by rfl⟩ : syracuseStep 3273065 = 2454799) B2454799
theorem B2182043 : Blo 2181435 2182043 := bstep (se 1 (by rfl) ⟨1636532, by rfl⟩ : syracuseStep 2182043 = 3273065) B3273065
theorem B12427445 : Blo 2181435 12427445 := bbase (se 5 (by rfl) ⟨582536, by rfl⟩ : syracuseStep 12427445 = 1165073) (by norm_num)
theorem B8284963 : Blo 2181435 8284963 := bstep (se 1 (by rfl) ⟨6213722, by rfl⟩ : syracuseStep 8284963 = 12427445) B12427445
theorem B11046617 : Blo 2181435 11046617 := bstep (se 2 (by rfl) ⟨4142481, by rfl⟩ : syracuseStep 11046617 = 8284963) B8284963
theorem B7364411 : Blo 2181435 7364411 := bstep (se 1 (by rfl) ⟨5523308, by rfl⟩ : syracuseStep 7364411 = 11046617) B11046617
theorem B4909607 : Blo 2181435 4909607 := bstep (se 1 (by rfl) ⟨3682205, by rfl⟩ : syracuseStep 4909607 = 7364411) B7364411
theorem B3273071 : Blo 2181435 3273071 := bstep (se 1 (by rfl) ⟨2454803, by rfl⟩ : syracuseStep 3273071 = 4909607) B4909607
theorem B2182047 : Blo 2181435 2182047 := bstep (se 1 (by rfl) ⟨1636535, by rfl⟩ : syracuseStep 2182047 = 3273071) B3273071
theorem B3273077 : Blo 2181435 3273077 := bbase (se 5 (by rfl) ⟨153425, by rfl⟩ : syracuseStep 3273077 = 306851) (by norm_num)
theorem B2182051 : Blo 2181435 2182051 := bstep (se 1 (by rfl) ⟨1636538, by rfl⟩ : syracuseStep 2182051 = 3273077) B3273077
theorem B2621425 : Blo 2181435 2621425 := bbase (se 2 (by rfl) ⟨983034, by rfl⟩ : syracuseStep 2621425 = 1966069) (by norm_num)
theorem B3495233 : Blo 2181435 3495233 := bstep (se 2 (by rfl) ⟨1310712, by rfl⟩ : syracuseStep 3495233 = 2621425) B2621425
theorem B2330155 : Blo 2181435 2330155 := bstep (se 1 (by rfl) ⟨1747616, by rfl⟩ : syracuseStep 2330155 = 3495233) B3495233
theorem B3106873 : Blo 2181435 3106873 := bstep (se 2 (by rfl) ⟨1165077, by rfl⟩ : syracuseStep 3106873 = 2330155) B2330155
theorem B4142497 : Blo 2181435 4142497 := bstep (se 2 (by rfl) ⟨1553436, by rfl⟩ : syracuseStep 4142497 = 3106873) B3106873
theorem B5523329 : Blo 2181435 5523329 := bstep (se 2 (by rfl) ⟨2071248, by rfl⟩ : syracuseStep 5523329 = 4142497) B4142497
theorem B3682219 : Blo 2181435 3682219 := bstep (se 1 (by rfl) ⟨2761664, by rfl⟩ : syracuseStep 3682219 = 5523329) B5523329
theorem B4909625 : Blo 2181435 4909625 := bstep (se 2 (by rfl) ⟨1841109, by rfl⟩ : syracuseStep 4909625 = 3682219) B3682219
theorem B3273083 : Blo 2181435 3273083 := bstep (se 1 (by rfl) ⟨2454812, by rfl⟩ : syracuseStep 3273083 = 4909625) B4909625
theorem B2182055 : Blo 2181435 2182055 := bstep (se 1 (by rfl) ⟨1636541, by rfl⟩ : syracuseStep 2182055 = 3273083) B3273083
theorem B2454817 : Blo 2181435 2454817 := bbase (se 2 (by rfl) ⟨920556, by rfl⟩ : syracuseStep 2454817 = 1841113) (by norm_num)
theorem B3273089 : Blo 2181435 3273089 := bstep (se 2 (by rfl) ⟨1227408, by rfl⟩ : syracuseStep 3273089 = 2454817) B2454817
theorem B2182059 : Blo 2181435 2182059 := bstep (se 1 (by rfl) ⟨1636544, by rfl⟩ : syracuseStep 2182059 = 3273089) B3273089
theorem B5523349 : Blo 2181435 5523349 := bbase (se 6 (by rfl) ⟨129453, by rfl⟩ : syracuseStep 5523349 = 258907) (by norm_num)
theorem B7364465 : Blo 2181435 7364465 := bstep (se 2 (by rfl) ⟨2761674, by rfl⟩ : syracuseStep 7364465 = 5523349) B5523349
theorem B4909643 : Blo 2181435 4909643 := bstep (se 1 (by rfl) ⟨3682232, by rfl⟩ : syracuseStep 4909643 = 7364465) B7364465
theorem B3273095 : Blo 2181435 3273095 := bstep (se 1 (by rfl) ⟨2454821, by rfl⟩ : syracuseStep 3273095 = 4909643) B4909643
theorem B2182063 : Blo 2181435 2182063 := bstep (se 1 (by rfl) ⟨1636547, by rfl⟩ : syracuseStep 2182063 = 3273095) B3273095
theorem B3273101 : Blo 2181435 3273101 := bbase (se 3 (by rfl) ⟨613706, by rfl⟩ : syracuseStep 3273101 = 1227413) (by norm_num)
theorem B2182067 : Blo 2181435 2182067 := bstep (se 1 (by rfl) ⟨1636550, by rfl⟩ : syracuseStep 2182067 = 3273101) B3273101
theorem B4909661 : Blo 2181435 4909661 := bbase (se 3 (by rfl) ⟨920561, by rfl⟩ : syracuseStep 4909661 = 1841123) (by norm_num)
theorem B3273107 : Blo 2181435 3273107 := bstep (se 1 (by rfl) ⟨2454830, by rfl⟩ : syracuseStep 3273107 = 4909661) B4909661
theorem B2182071 : Blo 2181435 2182071 := bstep (se 1 (by rfl) ⟨1636553, by rfl⟩ : syracuseStep 2182071 = 3273107) B3273107
theorem B3682253 : Blo 2181435 3682253 := bbase (se 3 (by rfl) ⟨690422, by rfl⟩ : syracuseStep 3682253 = 1380845) (by norm_num)
theorem B2454835 : Blo 2181435 2454835 := bstep (se 1 (by rfl) ⟨1841126, by rfl⟩ : syracuseStep 2454835 = 3682253) B3682253
theorem B3273113 : Blo 2181435 3273113 := bstep (se 2 (by rfl) ⟨1227417, by rfl⟩ : syracuseStep 3273113 = 2454835) B2454835
theorem B2182075 : Blo 2181435 2182075 := bstep (se 1 (by rfl) ⟨1636556, by rfl⟩ : syracuseStep 2182075 = 3273113) B3273113
theorem B2488333 : Blo 2181435 2488333 := bbase (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) (by norm_num)
theorem B3317777 : Blo 2181435 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B2211851 : Blo 2181435 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B5898269 : Blo 2181435 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B15728717 : Blo 2181435 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B10485811 : Blo 2181435 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B13981081 : Blo 2181435 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B18641441 : Blo 2181435 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B12427627 : Blo 2181435 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B16570169 : Blo 2181435 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B11046779 : Blo 2181435 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B7364519 : Blo 2181435 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B4909679 : Blo 2181435 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B3273119 : Blo 2181435 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B2182079 : Blo 2181435 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B3273125 : Blo 2181435 3273125 := bbase (se 4 (by rfl) ⟨306855, by rfl⟩ : syracuseStep 3273125 = 613711) (by norm_num)
theorem B2182083 : Blo 2181435 2182083 := bstep (se 1 (by rfl) ⟨1636562, by rfl⟩ : syracuseStep 2182083 = 3273125) B3273125
theorem B2761705 : Blo 2181435 2761705 := bbase (se 2 (by rfl) ⟨1035639, by rfl⟩ : syracuseStep 2761705 = 2071279) (by norm_num)
theorem B3682273 : Blo 2181435 3682273 := bstep (se 2 (by rfl) ⟨1380852, by rfl⟩ : syracuseStep 3682273 = 2761705) B2761705
theorem B4909697 : Blo 2181435 4909697 := bstep (se 2 (by rfl) ⟨1841136, by rfl⟩ : syracuseStep 4909697 = 3682273) B3682273
theorem B3273131 : Blo 2181435 3273131 := bstep (se 1 (by rfl) ⟨2454848, by rfl⟩ : syracuseStep 3273131 = 4909697) B4909697
theorem B2182087 : Blo 2181435 2182087 := bstep (se 1 (by rfl) ⟨1636565, by rfl⟩ : syracuseStep 2182087 = 3273131) B3273131
theorem B2454853 : Blo 2181435 2454853 := bbase (se 4 (by rfl) ⟨230142, by rfl⟩ : syracuseStep 2454853 = 460285) (by norm_num)
theorem B3273137 : Blo 2181435 3273137 := bstep (se 2 (by rfl) ⟨1227426, by rfl⟩ : syracuseStep 3273137 = 2454853) B2454853
theorem B2182091 : Blo 2181435 2182091 := bstep (se 1 (by rfl) ⟨1636568, by rfl⟩ : syracuseStep 2182091 = 3273137) B3273137
theorem B4142573 : Blo 2181435 4142573 := bbase (se 3 (by rfl) ⟨776732, by rfl⟩ : syracuseStep 4142573 = 1553465) (by norm_num)
theorem B2761715 : Blo 2181435 2761715 := bstep (se 1 (by rfl) ⟨2071286, by rfl⟩ : syracuseStep 2761715 = 4142573) B4142573
theorem B7364573 : Blo 2181435 7364573 := bstep (se 3 (by rfl) ⟨1380857, by rfl⟩ : syracuseStep 7364573 = 2761715) B2761715
theorem B4909715 : Blo 2181435 4909715 := bstep (se 1 (by rfl) ⟨3682286, by rfl⟩ : syracuseStep 4909715 = 7364573) B7364573
theorem B3273143 : Blo 2181435 3273143 := bstep (se 1 (by rfl) ⟨2454857, by rfl⟩ : syracuseStep 3273143 = 4909715) B4909715
theorem B2182095 : Blo 2181435 2182095 := bstep (se 1 (by rfl) ⟨1636571, by rfl⟩ : syracuseStep 2182095 = 3273143) B3273143
theorem B3273149 : Blo 2181435 3273149 := bbase (se 3 (by rfl) ⟨613715, by rfl⟩ : syracuseStep 3273149 = 1227431) (by norm_num)
theorem B2182099 : Blo 2181435 2182099 := bstep (se 1 (by rfl) ⟨1636574, by rfl⟩ : syracuseStep 2182099 = 3273149) B3273149
theorem B4909733 : Blo 2181435 4909733 := bbase (se 4 (by rfl) ⟨460287, by rfl⟩ : syracuseStep 4909733 = 920575) (by norm_num)
theorem B3273155 : Blo 2181435 3273155 := bstep (se 1 (by rfl) ⟨2454866, by rfl⟩ : syracuseStep 3273155 = 4909733) B4909733
theorem B2182103 : Blo 2181435 2182103 := bstep (se 1 (by rfl) ⟨1636577, by rfl⟩ : syracuseStep 2182103 = 3273155) B3273155
theorem B5523461 : Blo 2181435 5523461 := bbase (se 4 (by rfl) ⟨517824, by rfl⟩ : syracuseStep 5523461 = 1035649) (by norm_num)
theorem B3682307 : Blo 2181435 3682307 := bstep (se 1 (by rfl) ⟨2761730, by rfl⟩ : syracuseStep 3682307 = 5523461) B5523461
theorem B2454871 : Blo 2181435 2454871 := bstep (se 1 (by rfl) ⟨1841153, by rfl⟩ : syracuseStep 2454871 = 3682307) B3682307
theorem B3273161 : Blo 2181435 3273161 := bstep (se 2 (by rfl) ⟨1227435, by rfl⟩ : syracuseStep 3273161 = 2454871) B2454871
theorem B2182107 : Blo 2181435 2182107 := bstep (se 1 (by rfl) ⟨1636580, by rfl⟩ : syracuseStep 2182107 = 3273161) B3273161
theorem B4660429 : Blo 2181435 4660429 := bbase (se 3 (by rfl) ⟨873830, by rfl⟩ : syracuseStep 4660429 = 1747661) (by norm_num)
theorem B6213905 : Blo 2181435 6213905 := bstep (se 2 (by rfl) ⟨2330214, by rfl⟩ : syracuseStep 6213905 = 4660429) B4660429
theorem B4142603 : Blo 2181435 4142603 := bstep (se 1 (by rfl) ⟨3106952, by rfl⟩ : syracuseStep 4142603 = 6213905) B6213905
theorem B11046941 : Blo 2181435 11046941 := bstep (se 3 (by rfl) ⟨2071301, by rfl⟩ : syracuseStep 11046941 = 4142603) B4142603
theorem B7364627 : Blo 2181435 7364627 := bstep (se 1 (by rfl) ⟨5523470, by rfl⟩ : syracuseStep 7364627 = 11046941) B11046941
theorem B4909751 : Blo 2181435 4909751 := bstep (se 1 (by rfl) ⟨3682313, by rfl⟩ : syracuseStep 4909751 = 7364627) B7364627
theorem B3273167 : Blo 2181435 3273167 := bstep (se 1 (by rfl) ⟨2454875, by rfl⟩ : syracuseStep 3273167 = 4909751) B4909751
theorem B2182111 : Blo 2181435 2182111 := bstep (se 1 (by rfl) ⟨1636583, by rfl⟩ : syracuseStep 2182111 = 3273167) B3273167
theorem B3273173 : Blo 2181435 3273173 := bbase (se 7 (by rfl) ⟨38357, by rfl⟩ : syracuseStep 3273173 = 76715) (by norm_num)
theorem B2182115 : Blo 2181435 2182115 := bstep (se 1 (by rfl) ⟨1636586, by rfl⟩ : syracuseStep 2182115 = 3273173) B3273173
theorem B8285237 : Blo 2181435 8285237 := bbase (se 5 (by rfl) ⟨388370, by rfl⟩ : syracuseStep 8285237 = 776741) (by norm_num)
theorem B5523491 : Blo 2181435 5523491 := bstep (se 1 (by rfl) ⟨4142618, by rfl⟩ : syracuseStep 5523491 = 8285237) B8285237
theorem B3682327 : Blo 2181435 3682327 := bstep (se 1 (by rfl) ⟨2761745, by rfl⟩ : syracuseStep 3682327 = 5523491) B5523491
theorem B4909769 : Blo 2181435 4909769 := bstep (se 2 (by rfl) ⟨1841163, by rfl⟩ : syracuseStep 4909769 = 3682327) B3682327
theorem B3273179 : Blo 2181435 3273179 := bstep (se 1 (by rfl) ⟨2454884, by rfl⟩ : syracuseStep 3273179 = 4909769) B4909769
theorem B2182119 : Blo 2181435 2182119 := bstep (se 1 (by rfl) ⟨1636589, by rfl⟩ : syracuseStep 2182119 = 3273179) B3273179
theorem B2454889 : Blo 2181435 2454889 := bbase (se 2 (by rfl) ⟨920583, by rfl⟩ : syracuseStep 2454889 = 1841167) (by norm_num)
theorem B3273185 : Blo 2181435 3273185 := bstep (se 2 (by rfl) ⟨1227444, by rfl⟩ : syracuseStep 3273185 = 2454889) B2454889
theorem B2182123 : Blo 2181435 2182123 := bstep (se 1 (by rfl) ⟨1636592, by rfl⟩ : syracuseStep 2182123 = 3273185) B3273185
theorem B2876345 : Blo 2181435 2876345 := bbase (se 2 (by rfl) ⟨1078629, by rfl⟩ : syracuseStep 2876345 = 2157259) (by norm_num)
theorem B30681013 : Blo 2181435 30681013 := bstep (se 5 (by rfl) ⟨1438172, by rfl⟩ : syracuseStep 30681013 = 2876345) B2876345
theorem B40908017 : Blo 2181435 40908017 := bstep (se 2 (by rfl) ⟨15340506, by rfl⟩ : syracuseStep 40908017 = 30681013) B30681013
theorem B27272011 : Blo 2181435 27272011 := bstep (se 1 (by rfl) ⟨20454008, by rfl⟩ : syracuseStep 27272011 = 40908017) B40908017
theorem B36362681 : Blo 2181435 36362681 := bstep (se 2 (by rfl) ⟨13636005, by rfl⟩ : syracuseStep 36362681 = 27272011) B27272011
theorem B24241787 : Blo 2181435 24241787 := bstep (se 1 (by rfl) ⟨18181340, by rfl⟩ : syracuseStep 24241787 = 36362681) B36362681
theorem B16161191 : Blo 2181435 16161191 := bstep (se 1 (by rfl) ⟨12120893, by rfl⟩ : syracuseStep 16161191 = 24241787) B24241787
theorem B10774127 : Blo 2181435 10774127 := bstep (se 1 (by rfl) ⟨8080595, by rfl⟩ : syracuseStep 10774127 = 16161191) B16161191
theorem B7182751 : Blo 2181435 7182751 := bstep (se 1 (by rfl) ⟨5387063, by rfl⟩ : syracuseStep 7182751 = 10774127) B10774127
theorem B9577001 : Blo 2181435 9577001 := bstep (se 2 (by rfl) ⟨3591375, by rfl⟩ : syracuseStep 9577001 = 7182751) B7182751
theorem B6384667 : Blo 2181435 6384667 := bstep (se 1 (by rfl) ⟨4788500, by rfl⟩ : syracuseStep 6384667 = 9577001) B9577001
theorem B8512889 : Blo 2181435 8512889 := bstep (se 2 (by rfl) ⟨3192333, by rfl⟩ : syracuseStep 8512889 = 6384667) B6384667
theorem B90804149 : Blo 2181435 90804149 := bstep (se 5 (by rfl) ⟨4256444, by rfl⟩ : syracuseStep 90804149 = 8512889) B8512889
theorem B60536099 : Blo 2181435 60536099 := bstep (se 1 (by rfl) ⟨45402074, by rfl⟩ : syracuseStep 60536099 = 90804149) B90804149
theorem B40357399 : Blo 2181435 40357399 := bstep (se 1 (by rfl) ⟨30268049, by rfl⟩ : syracuseStep 40357399 = 60536099) B60536099
theorem B53809865 : Blo 2181435 53809865 := bstep (se 2 (by rfl) ⟨20178699, by rfl⟩ : syracuseStep 53809865 = 40357399) B40357399
theorem B35873243 : Blo 2181435 35873243 := bstep (se 1 (by rfl) ⟨26904932, by rfl⟩ : syracuseStep 35873243 = 53809865) B53809865
theorem B23915495 : Blo 2181435 23915495 := bstep (se 1 (by rfl) ⟨17936621, by rfl⟩ : syracuseStep 23915495 = 35873243) B35873243
theorem B15943663 : Blo 2181435 15943663 := bstep (se 1 (by rfl) ⟨11957747, by rfl⟩ : syracuseStep 15943663 = 23915495) B23915495
theorem B21258217 : Blo 2181435 21258217 := bstep (se 2 (by rfl) ⟨7971831, by rfl⟩ : syracuseStep 21258217 = 15943663) B15943663
theorem B113377157 : Blo 2181435 113377157 := bstep (se 4 (by rfl) ⟨10629108, by rfl⟩ : syracuseStep 113377157 = 21258217) B21258217
theorem B75584771 : Blo 2181435 75584771 := bstep (se 1 (by rfl) ⟨56688578, by rfl⟩ : syracuseStep 75584771 = 113377157) B113377157
theorem B50389847 : Blo 2181435 50389847 := bstep (se 1 (by rfl) ⟨37792385, by rfl⟩ : syracuseStep 50389847 = 75584771) B75584771
theorem B33593231 : Blo 2181435 33593231 := bstep (se 1 (by rfl) ⟨25194923, by rfl⟩ : syracuseStep 33593231 = 50389847) B50389847
theorem B89581949 : Blo 2181435 89581949 := bstep (se 3 (by rfl) ⟨16796615, by rfl⟩ : syracuseStep 89581949 = 33593231) B33593231
theorem B59721299 : Blo 2181435 59721299 := bstep (se 1 (by rfl) ⟨44790974, by rfl⟩ : syracuseStep 59721299 = 89581949) B89581949
theorem B39814199 : Blo 2181435 39814199 := bstep (se 1 (by rfl) ⟨29860649, by rfl⟩ : syracuseStep 39814199 = 59721299) B59721299
theorem B26542799 : Blo 2181435 26542799 := bstep (se 1 (by rfl) ⟨19907099, by rfl⟩ : syracuseStep 26542799 = 39814199) B39814199
theorem B17695199 : Blo 2181435 17695199 := bstep (se 1 (by rfl) ⟨13271399, by rfl⟩ : syracuseStep 17695199 = 26542799) B26542799
theorem B11796799 : Blo 2181435 11796799 := bstep (se 1 (by rfl) ⟨8847599, by rfl⟩ : syracuseStep 11796799 = 17695199) B17695199
theorem B15729065 : Blo 2181435 15729065 := bstep (se 2 (by rfl) ⟨5898399, by rfl⟩ : syracuseStep 15729065 = 11796799) B11796799
theorem B10486043 : Blo 2181435 10486043 := bstep (se 1 (by rfl) ⟨7864532, by rfl⟩ : syracuseStep 10486043 = 15729065) B15729065
theorem B6990695 : Blo 2181435 6990695 := bstep (se 1 (by rfl) ⟨5243021, by rfl⟩ : syracuseStep 6990695 = 10486043) B10486043
theorem B4660463 : Blo 2181435 4660463 := bstep (se 1 (by rfl) ⟨3495347, by rfl⟩ : syracuseStep 4660463 = 6990695) B6990695
theorem B12427901 : Blo 2181435 12427901 := bstep (se 3 (by rfl) ⟨2330231, by rfl⟩ : syracuseStep 12427901 = 4660463) B4660463
theorem B8285267 : Blo 2181435 8285267 := bstep (se 1 (by rfl) ⟨6213950, by rfl⟩ : syracuseStep 8285267 = 12427901) B12427901
theorem B5523511 : Blo 2181435 5523511 := bstep (se 1 (by rfl) ⟨4142633, by rfl⟩ : syracuseStep 5523511 = 8285267) B8285267
theorem B7364681 : Blo 2181435 7364681 := bstep (se 2 (by rfl) ⟨2761755, by rfl⟩ : syracuseStep 7364681 = 5523511) B5523511
theorem B4909787 : Blo 2181435 4909787 := bstep (se 1 (by rfl) ⟨3682340, by rfl⟩ : syracuseStep 4909787 = 7364681) B7364681
theorem B3273191 : Blo 2181435 3273191 := bstep (se 1 (by rfl) ⟨2454893, by rfl⟩ : syracuseStep 3273191 = 4909787) B4909787
theorem B2182127 : Blo 2181435 2182127 := bstep (se 1 (by rfl) ⟨1636595, by rfl⟩ : syracuseStep 2182127 = 3273191) B3273191
theorem B3273197 : Blo 2181435 3273197 := bbase (se 3 (by rfl) ⟨613724, by rfl⟩ : syracuseStep 3273197 = 1227449) (by norm_num)
theorem B2182131 : Blo 2181435 2182131 := bstep (se 1 (by rfl) ⟨1636598, by rfl⟩ : syracuseStep 2182131 = 3273197) B3273197
theorem B4909805 : Blo 2181435 4909805 := bbase (se 3 (by rfl) ⟨920588, by rfl⟩ : syracuseStep 4909805 = 1841177) (by norm_num)
theorem B3273203 : Blo 2181435 3273203 := bstep (se 1 (by rfl) ⟨2454902, by rfl⟩ : syracuseStep 3273203 = 4909805) B4909805
theorem B2182135 : Blo 2181435 2182135 := bstep (se 1 (by rfl) ⟨1636601, by rfl⟩ : syracuseStep 2182135 = 3273203) B3273203
theorem B2330245 : Blo 2181435 2330245 := bbase (se 4 (by rfl) ⟨218460, by rfl⟩ : syracuseStep 2330245 = 436921) (by norm_num)
theorem B3106993 : Blo 2181435 3106993 := bstep (se 2 (by rfl) ⟨1165122, by rfl⟩ : syracuseStep 3106993 = 2330245) B2330245
theorem B4142657 : Blo 2181435 4142657 := bstep (se 2 (by rfl) ⟨1553496, by rfl⟩ : syracuseStep 4142657 = 3106993) B3106993
theorem B2761771 : Blo 2181435 2761771 := bstep (se 1 (by rfl) ⟨2071328, by rfl⟩ : syracuseStep 2761771 = 4142657) B4142657
theorem B3682361 : Blo 2181435 3682361 := bstep (se 2 (by rfl) ⟨1380885, by rfl⟩ : syracuseStep 3682361 = 2761771) B2761771
theorem B2454907 : Blo 2181435 2454907 := bstep (se 1 (by rfl) ⟨1841180, by rfl⟩ : syracuseStep 2454907 = 3682361) B3682361
theorem B3273209 : Blo 2181435 3273209 := bstep (se 2 (by rfl) ⟨1227453, by rfl⟩ : syracuseStep 3273209 = 2454907) B2454907
theorem B2182139 : Blo 2181435 2182139 := bstep (se 1 (by rfl) ⟨1636604, by rfl⟩ : syracuseStep 2182139 = 3273209) B3273209
theorem B9953621 : Blo 2181435 9953621 := bbase (se 10 (by rfl) ⟨14580, by rfl⟩ : syracuseStep 9953621 = 29161) (by norm_num)
theorem B6635747 : Blo 2181435 6635747 := bstep (se 1 (by rfl) ⟨4976810, by rfl⟩ : syracuseStep 6635747 = 9953621) B9953621
theorem B17695325 : Blo 2181435 17695325 := bstep (se 3 (by rfl) ⟨3317873, by rfl⟩ : syracuseStep 17695325 = 6635747) B6635747
theorem B11796883 : Blo 2181435 11796883 := bstep (se 1 (by rfl) ⟨8847662, by rfl⟩ : syracuseStep 11796883 = 17695325) B17695325
theorem B62916709 : Blo 2181435 62916709 := bstep (se 4 (by rfl) ⟨5898441, by rfl⟩ : syracuseStep 62916709 = 11796883) B11796883
theorem B83888945 : Blo 2181435 83888945 := bstep (se 2 (by rfl) ⟨31458354, by rfl⟩ : syracuseStep 83888945 = 62916709) B62916709
theorem B55925963 : Blo 2181435 55925963 := bstep (se 1 (by rfl) ⟨41944472, by rfl⟩ : syracuseStep 55925963 = 83888945) B83888945
theorem B37283975 : Blo 2181435 37283975 := bstep (se 1 (by rfl) ⟨27962981, by rfl⟩ : syracuseStep 37283975 = 55925963) B55925963
theorem B24855983 : Blo 2181435 24855983 := bstep (se 1 (by rfl) ⟨18641987, by rfl⟩ : syracuseStep 24855983 = 37283975) B37283975
theorem B16570655 : Blo 2181435 16570655 := bstep (se 1 (by rfl) ⟨12427991, by rfl⟩ : syracuseStep 16570655 = 24855983) B24855983
theorem B11047103 : Blo 2181435 11047103 := bstep (se 1 (by rfl) ⟨8285327, by rfl⟩ : syracuseStep 11047103 = 16570655) B16570655
theorem B7364735 : Blo 2181435 7364735 := bstep (se 1 (by rfl) ⟨5523551, by rfl⟩ : syracuseStep 7364735 = 11047103) B11047103
theorem B4909823 : Blo 2181435 4909823 := bstep (se 1 (by rfl) ⟨3682367, by rfl⟩ : syracuseStep 4909823 = 7364735) B7364735
theorem B3273215 : Blo 2181435 3273215 := bstep (se 1 (by rfl) ⟨2454911, by rfl⟩ : syracuseStep 3273215 = 4909823) B4909823
theorem B2182143 : Blo 2181435 2182143 := bstep (se 1 (by rfl) ⟨1636607, by rfl⟩ : syracuseStep 2182143 = 3273215) B3273215
theorem B3273221 : Blo 2181435 3273221 := bbase (se 4 (by rfl) ⟨306864, by rfl⟩ : syracuseStep 3273221 = 613729) (by norm_num)
theorem B2182147 : Blo 2181435 2182147 := bstep (se 1 (by rfl) ⟨1636610, by rfl⟩ : syracuseStep 2182147 = 3273221) B3273221
theorem B3682381 : Blo 2181435 3682381 := bbase (se 3 (by rfl) ⟨690446, by rfl⟩ : syracuseStep 3682381 = 1380893) (by norm_num)
theorem B4909841 : Blo 2181435 4909841 := bstep (se 2 (by rfl) ⟨1841190, by rfl⟩ : syracuseStep 4909841 = 3682381) B3682381
theorem B3273227 : Blo 2181435 3273227 := bstep (se 1 (by rfl) ⟨2454920, by rfl⟩ : syracuseStep 3273227 = 4909841) B4909841
theorem B2182151 : Blo 2181435 2182151 := bstep (se 1 (by rfl) ⟨1636613, by rfl⟩ : syracuseStep 2182151 = 3273227) B3273227
theorem B2454925 : Blo 2181435 2454925 := bbase (se 3 (by rfl) ⟨460298, by rfl⟩ : syracuseStep 2454925 = 920597) (by norm_num)
theorem B3273233 : Blo 2181435 3273233 := bstep (se 2 (by rfl) ⟨1227462, by rfl⟩ : syracuseStep 3273233 = 2454925) B2454925
theorem B2182155 : Blo 2181435 2182155 := bstep (se 1 (by rfl) ⟨1636616, by rfl⟩ : syracuseStep 2182155 = 3273233) B3273233
theorem B7364789 : Blo 2181435 7364789 := bbase (se 5 (by rfl) ⟨345224, by rfl⟩ : syracuseStep 7364789 = 690449) (by norm_num)
theorem B4909859 : Blo 2181435 4909859 := bstep (se 1 (by rfl) ⟨3682394, by rfl⟩ : syracuseStep 4909859 = 7364789) B7364789
theorem B3273239 : Blo 2181435 3273239 := bstep (se 1 (by rfl) ⟨2454929, by rfl⟩ : syracuseStep 3273239 = 4909859) B4909859
theorem B2182159 : Blo 2181435 2182159 := bstep (se 1 (by rfl) ⟨1636619, by rfl⟩ : syracuseStep 2182159 = 3273239) B3273239
theorem B3273245 : Blo 2181435 3273245 := bbase (se 3 (by rfl) ⟨613733, by rfl⟩ : syracuseStep 3273245 = 1227467) (by norm_num)
theorem B2182163 : Blo 2181435 2182163 := bstep (se 1 (by rfl) ⟨1636622, by rfl⟩ : syracuseStep 2182163 = 3273245) B3273245
theorem B4909877 : Blo 2181435 4909877 := bbase (se 5 (by rfl) ⟨230150, by rfl⟩ : syracuseStep 4909877 = 460301) (by norm_num)
theorem B3273251 : Blo 2181435 3273251 := bstep (se 1 (by rfl) ⟨2454938, by rfl⟩ : syracuseStep 3273251 = 4909877) B4909877
theorem B2182167 : Blo 2181435 2182167 := bstep (se 1 (by rfl) ⟨1636625, by rfl⟩ : syracuseStep 2182167 = 3273251) B3273251
theorem B4040381 : Blo 2181435 4040381 := bbase (se 3 (by rfl) ⟨757571, by rfl⟩ : syracuseStep 4040381 = 1515143) (by norm_num)
theorem B2693587 : Blo 2181435 2693587 := bstep (se 1 (by rfl) ⟨2020190, by rfl⟩ : syracuseStep 2693587 = 4040381) B4040381
theorem B3591449 : Blo 2181435 3591449 := bstep (se 2 (by rfl) ⟨1346793, by rfl⟩ : syracuseStep 3591449 = 2693587) B2693587
theorem B2394299 : Blo 2181435 2394299 := bstep (se 1 (by rfl) ⟨1795724, by rfl⟩ : syracuseStep 2394299 = 3591449) B3591449
theorem B6384797 : Blo 2181435 6384797 := bstep (se 3 (by rfl) ⟨1197149, by rfl⟩ : syracuseStep 6384797 = 2394299) B2394299
theorem B4256531 : Blo 2181435 4256531 := bstep (se 1 (by rfl) ⟨3192398, by rfl⟩ : syracuseStep 4256531 = 6384797) B6384797
theorem B2837687 : Blo 2181435 2837687 := bstep (se 1 (by rfl) ⟨2128265, by rfl⟩ : syracuseStep 2837687 = 4256531) B4256531
theorem B7567165 : Blo 2181435 7567165 := bstep (se 3 (by rfl) ⟨1418843, by rfl⟩ : syracuseStep 7567165 = 2837687) B2837687
theorem B40358213 : Blo 2181435 40358213 := bstep (se 4 (by rfl) ⟨3783582, by rfl⟩ : syracuseStep 40358213 = 7567165) B7567165
theorem B26905475 : Blo 2181435 26905475 := bstep (se 1 (by rfl) ⟨20179106, by rfl⟩ : syracuseStep 26905475 = 40358213) B40358213
theorem B17936983 : Blo 2181435 17936983 := bstep (se 1 (by rfl) ⟨13452737, by rfl⟩ : syracuseStep 17936983 = 26905475) B26905475
theorem B95663909 : Blo 2181435 95663909 := bstep (se 4 (by rfl) ⟨8968491, by rfl⟩ : syracuseStep 95663909 = 17936983) B17936983
theorem B63775939 : Blo 2181435 63775939 := bstep (se 1 (by rfl) ⟨47831954, by rfl⟩ : syracuseStep 63775939 = 95663909) B95663909
theorem B85034585 : Blo 2181435 85034585 := bstep (se 2 (by rfl) ⟨31887969, by rfl⟩ : syracuseStep 85034585 = 63775939) B63775939
theorem B56689723 : Blo 2181435 56689723 := bstep (se 1 (by rfl) ⟨42517292, by rfl⟩ : syracuseStep 56689723 = 85034585) B85034585
theorem B75586297 : Blo 2181435 75586297 := bstep (se 2 (by rfl) ⟨28344861, by rfl⟩ : syracuseStep 75586297 = 56689723) B56689723
theorem B100781729 : Blo 2181435 100781729 := bstep (se 2 (by rfl) ⟨37793148, by rfl⟩ : syracuseStep 100781729 = 75586297) B75586297
theorem B67187819 : Blo 2181435 67187819 := bstep (se 1 (by rfl) ⟨50390864, by rfl⟩ : syracuseStep 67187819 = 100781729) B100781729
theorem B44791879 : Blo 2181435 44791879 := bstep (se 1 (by rfl) ⟨33593909, by rfl⟩ : syracuseStep 44791879 = 67187819) B67187819
theorem B59722505 : Blo 2181435 59722505 := bstep (se 2 (by rfl) ⟨22395939, by rfl⟩ : syracuseStep 59722505 = 44791879) B44791879
theorem B39815003 : Blo 2181435 39815003 := bstep (se 1 (by rfl) ⟨29861252, by rfl⟩ : syracuseStep 39815003 = 59722505) B59722505
theorem B26543335 : Blo 2181435 26543335 := bstep (se 1 (by rfl) ⟨19907501, by rfl⟩ : syracuseStep 26543335 = 39815003) B39815003
theorem B35391113 : Blo 2181435 35391113 := bstep (se 2 (by rfl) ⟨13271667, by rfl⟩ : syracuseStep 35391113 = 26543335) B26543335
theorem B23594075 : Blo 2181435 23594075 := bstep (se 1 (by rfl) ⟨17695556, by rfl⟩ : syracuseStep 23594075 = 35391113) B35391113
theorem B15729383 : Blo 2181435 15729383 := bstep (se 1 (by rfl) ⟨11797037, by rfl⟩ : syracuseStep 15729383 = 23594075) B23594075
theorem B10486255 : Blo 2181435 10486255 := bstep (se 1 (by rfl) ⟨7864691, by rfl⟩ : syracuseStep 10486255 = 15729383) B15729383
theorem B13981673 : Blo 2181435 13981673 := bstep (se 2 (by rfl) ⟨5243127, by rfl⟩ : syracuseStep 13981673 = 10486255) B10486255
theorem B9321115 : Blo 2181435 9321115 := bstep (se 1 (by rfl) ⟨6990836, by rfl⟩ : syracuseStep 9321115 = 13981673) B13981673
theorem B12428153 : Blo 2181435 12428153 := bstep (se 2 (by rfl) ⟨4660557, by rfl⟩ : syracuseStep 12428153 = 9321115) B9321115
theorem B8285435 : Blo 2181435 8285435 := bstep (se 1 (by rfl) ⟨6214076, by rfl⟩ : syracuseStep 8285435 = 12428153) B12428153
theorem B5523623 : Blo 2181435 5523623 := bstep (se 1 (by rfl) ⟨4142717, by rfl⟩ : syracuseStep 5523623 = 8285435) B8285435
theorem B3682415 : Blo 2181435 3682415 := bstep (se 1 (by rfl) ⟨2761811, by rfl⟩ : syracuseStep 3682415 = 5523623) B5523623
theorem B2454943 : Blo 2181435 2454943 := bstep (se 1 (by rfl) ⟨1841207, by rfl⟩ : syracuseStep 2454943 = 3682415) B3682415
theorem B3273257 : Blo 2181435 3273257 := bstep (se 2 (by rfl) ⟨1227471, by rfl⟩ : syracuseStep 3273257 = 2454943) B2454943
theorem B2182171 : Blo 2181435 2182171 := bstep (se 1 (by rfl) ⟨1636628, by rfl⟩ : syracuseStep 2182171 = 3273257) B3273257
theorem B4976885 : Blo 2181435 4976885 := bbase (se 5 (by rfl) ⟨233291, by rfl⟩ : syracuseStep 4976885 = 466583) (by norm_num)
theorem B3317923 : Blo 2181435 3317923 := bstep (se 1 (by rfl) ⟨2488442, by rfl⟩ : syracuseStep 3317923 = 4976885) B4976885
theorem B4423897 : Blo 2181435 4423897 := bstep (se 2 (by rfl) ⟨1658961, by rfl⟩ : syracuseStep 4423897 = 3317923) B3317923
theorem B5898529 : Blo 2181435 5898529 := bstep (se 2 (by rfl) ⟨2211948, by rfl⟩ : syracuseStep 5898529 = 4423897) B4423897
theorem B7864705 : Blo 2181435 7864705 := bstep (se 2 (by rfl) ⟨2949264, by rfl⟩ : syracuseStep 7864705 = 5898529) B5898529
theorem B10486273 : Blo 2181435 10486273 := bstep (se 2 (by rfl) ⟨3932352, by rfl⟩ : syracuseStep 10486273 = 7864705) B7864705
theorem B13981697 : Blo 2181435 13981697 := bstep (se 2 (by rfl) ⟨5243136, by rfl⟩ : syracuseStep 13981697 = 10486273) B10486273
theorem B9321131 : Blo 2181435 9321131 := bstep (se 1 (by rfl) ⟨6990848, by rfl⟩ : syracuseStep 9321131 = 13981697) B13981697
theorem B6214087 : Blo 2181435 6214087 := bstep (se 1 (by rfl) ⟨4660565, by rfl⟩ : syracuseStep 6214087 = 9321131) B9321131
theorem B8285449 : Blo 2181435 8285449 := bstep (se 2 (by rfl) ⟨3107043, by rfl⟩ : syracuseStep 8285449 = 6214087) B6214087
theorem B11047265 : Blo 2181435 11047265 := bstep (se 2 (by rfl) ⟨4142724, by rfl⟩ : syracuseStep 11047265 = 8285449) B8285449
theorem B7364843 : Blo 2181435 7364843 := bstep (se 1 (by rfl) ⟨5523632, by rfl⟩ : syracuseStep 7364843 = 11047265) B11047265
theorem B4909895 : Blo 2181435 4909895 := bstep (se 1 (by rfl) ⟨3682421, by rfl⟩ : syracuseStep 4909895 = 7364843) B7364843
theorem B3273263 : Blo 2181435 3273263 := bstep (se 1 (by rfl) ⟨2454947, by rfl⟩ : syracuseStep 3273263 = 4909895) B4909895
theorem B2182175 : Blo 2181435 2182175 := bstep (se 1 (by rfl) ⟨1636631, by rfl⟩ : syracuseStep 2182175 = 3273263) B3273263
theorem B3273269 : Blo 2181435 3273269 := bbase (se 5 (by rfl) ⟨153434, by rfl⟩ : syracuseStep 3273269 = 306869) (by norm_num)
theorem B2182179 : Blo 2181435 2182179 := bstep (se 1 (by rfl) ⟨1636634, by rfl⟩ : syracuseStep 2182179 = 3273269) B3273269
theorem B5523653 : Blo 2181435 5523653 := bbase (se 4 (by rfl) ⟨517842, by rfl⟩ : syracuseStep 5523653 = 1035685) (by norm_num)
theorem B3682435 : Blo 2181435 3682435 := bstep (se 1 (by rfl) ⟨2761826, by rfl⟩ : syracuseStep 3682435 = 5523653) B5523653
theorem B4909913 : Blo 2181435 4909913 := bstep (se 2 (by rfl) ⟨1841217, by rfl⟩ : syracuseStep 4909913 = 3682435) B3682435
theorem B3273275 : Blo 2181435 3273275 := bstep (se 1 (by rfl) ⟨2454956, by rfl⟩ : syracuseStep 3273275 = 4909913) B4909913
theorem B2182183 : Blo 2181435 2182183 := bstep (se 1 (by rfl) ⟨1636637, by rfl⟩ : syracuseStep 2182183 = 3273275) B3273275
theorem B2454961 : Blo 2181435 2454961 := bbase (se 2 (by rfl) ⟨920610, by rfl⟩ : syracuseStep 2454961 = 1841221) (by norm_num)
theorem B3273281 : Blo 2181435 3273281 := bstep (se 2 (by rfl) ⟨1227480, by rfl⟩ : syracuseStep 3273281 = 2454961) B2454961
theorem B2182187 : Blo 2181435 2182187 := bstep (se 1 (by rfl) ⟨1636640, by rfl⟩ : syracuseStep 2182187 = 3273281) B3273281
theorem B6214133 : Blo 2181435 6214133 := bbase (se 5 (by rfl) ⟨291287, by rfl⟩ : syracuseStep 6214133 = 582575) (by norm_num)
theorem B4142755 : Blo 2181435 4142755 := bstep (se 1 (by rfl) ⟨3107066, by rfl⟩ : syracuseStep 4142755 = 6214133) B6214133
theorem B5523673 : Blo 2181435 5523673 := bstep (se 2 (by rfl) ⟨2071377, by rfl⟩ : syracuseStep 5523673 = 4142755) B4142755
theorem B7364897 : Blo 2181435 7364897 := bstep (se 2 (by rfl) ⟨2761836, by rfl⟩ : syracuseStep 7364897 = 5523673) B5523673
theorem B4909931 : Blo 2181435 4909931 := bstep (se 1 (by rfl) ⟨3682448, by rfl⟩ : syracuseStep 4909931 = 7364897) B7364897
theorem B3273287 : Blo 2181435 3273287 := bstep (se 1 (by rfl) ⟨2454965, by rfl⟩ : syracuseStep 3273287 = 4909931) B4909931
theorem B2182191 : Blo 2181435 2182191 := bstep (se 1 (by rfl) ⟨1636643, by rfl⟩ : syracuseStep 2182191 = 3273287) B3273287
theorem B3273293 : Blo 2181435 3273293 := bbase (se 3 (by rfl) ⟨613742, by rfl⟩ : syracuseStep 3273293 = 1227485) (by norm_num)
theorem B2182195 : Blo 2181435 2182195 := bstep (se 1 (by rfl) ⟨1636646, by rfl⟩ : syracuseStep 2182195 = 3273293) B3273293
theorem B4909949 : Blo 2181435 4909949 := bbase (se 3 (by rfl) ⟨920615, by rfl⟩ : syracuseStep 4909949 = 1841231) (by norm_num)
theorem B3273299 : Blo 2181435 3273299 := bstep (se 1 (by rfl) ⟨2454974, by rfl⟩ : syracuseStep 3273299 = 4909949) B4909949
theorem B2182199 : Blo 2181435 2182199 := bstep (se 1 (by rfl) ⟨1636649, by rfl⟩ : syracuseStep 2182199 = 3273299) B3273299
theorem B3682469 : Blo 2181435 3682469 := bbase (se 4 (by rfl) ⟨345231, by rfl⟩ : syracuseStep 3682469 = 690463) (by norm_num)
theorem B2454979 : Blo 2181435 2454979 := bstep (se 1 (by rfl) ⟨1841234, by rfl⟩ : syracuseStep 2454979 = 3682469) B3682469
theorem B3273305 : Blo 2181435 3273305 := bstep (se 2 (by rfl) ⟨1227489, by rfl⟩ : syracuseStep 3273305 = 2454979) B2454979
theorem B2182203 : Blo 2181435 2182203 := bstep (se 1 (by rfl) ⟨1636652, by rfl⟩ : syracuseStep 2182203 = 3273305) B3273305
theorem B2330317 : Blo 2181435 2330317 := bbase (se 3 (by rfl) ⟨436934, by rfl⟩ : syracuseStep 2330317 = 873869) (by norm_num)
theorem B3107089 : Blo 2181435 3107089 := bstep (se 2 (by rfl) ⟨1165158, by rfl⟩ : syracuseStep 3107089 = 2330317) B2330317
theorem B16571141 : Blo 2181435 16571141 := bstep (se 4 (by rfl) ⟨1553544, by rfl⟩ : syracuseStep 16571141 = 3107089) B3107089
theorem B11047427 : Blo 2181435 11047427 := bstep (se 1 (by rfl) ⟨8285570, by rfl⟩ : syracuseStep 11047427 = 16571141) B16571141
theorem B7364951 : Blo 2181435 7364951 := bstep (se 1 (by rfl) ⟨5523713, by rfl⟩ : syracuseStep 7364951 = 11047427) B11047427
theorem B4909967 : Blo 2181435 4909967 := bstep (se 1 (by rfl) ⟨3682475, by rfl⟩ : syracuseStep 4909967 = 7364951) B7364951
theorem B3273311 : Blo 2181435 3273311 := bstep (se 1 (by rfl) ⟨2454983, by rfl⟩ : syracuseStep 3273311 = 4909967) B4909967
theorem B2182207 : Blo 2181435 2182207 := bstep (se 1 (by rfl) ⟨1636655, by rfl⟩ : syracuseStep 2182207 = 3273311) B3273311
theorem B3273317 : Blo 2181435 3273317 := bbase (se 4 (by rfl) ⟨306873, by rfl⟩ : syracuseStep 3273317 = 613747) (by norm_num)
theorem B2182211 : Blo 2181435 2182211 := bstep (se 1 (by rfl) ⟨1636658, by rfl⟩ : syracuseStep 2182211 = 3273317) B3273317
theorem B3107101 : Blo 2181435 3107101 := bbase (se 3 (by rfl) ⟨582581, by rfl⟩ : syracuseStep 3107101 = 1165163) (by norm_num)
theorem B4142801 : Blo 2181435 4142801 := bstep (se 2 (by rfl) ⟨1553550, by rfl⟩ : syracuseStep 4142801 = 3107101) B3107101
theorem B2761867 : Blo 2181435 2761867 := bstep (se 1 (by rfl) ⟨2071400, by rfl⟩ : syracuseStep 2761867 = 4142801) B4142801
theorem B3682489 : Blo 2181435 3682489 := bstep (se 2 (by rfl) ⟨1380933, by rfl⟩ : syracuseStep 3682489 = 2761867) B2761867
theorem B4909985 : Blo 2181435 4909985 := bstep (se 2 (by rfl) ⟨1841244, by rfl⟩ : syracuseStep 4909985 = 3682489) B3682489
theorem B3273323 : Blo 2181435 3273323 := bstep (se 1 (by rfl) ⟨2454992, by rfl⟩ : syracuseStep 3273323 = 4909985) B4909985
theorem B2182215 : Blo 2181435 2182215 := bstep (se 1 (by rfl) ⟨1636661, by rfl⟩ : syracuseStep 2182215 = 3273323) B3273323
theorem B2454997 : Blo 2181435 2454997 := bbase (se 7 (by rfl) ⟨28769, by rfl⟩ : syracuseStep 2454997 = 57539) (by norm_num)
theorem B3273329 : Blo 2181435 3273329 := bstep (se 2 (by rfl) ⟨1227498, by rfl⟩ : syracuseStep 3273329 = 2454997) B2454997
theorem B2182219 : Blo 2181435 2182219 := bstep (se 1 (by rfl) ⟨1636664, by rfl⟩ : syracuseStep 2182219 = 3273329) B3273329
theorem B2761877 : Blo 2181435 2761877 := bbase (se 6 (by rfl) ⟨64731, by rfl⟩ : syracuseStep 2761877 = 129463) (by norm_num)
theorem B7365005 : Blo 2181435 7365005 := bstep (se 3 (by rfl) ⟨1380938, by rfl⟩ : syracuseStep 7365005 = 2761877) B2761877
theorem B4910003 : Blo 2181435 4910003 := bstep (se 1 (by rfl) ⟨3682502, by rfl⟩ : syracuseStep 4910003 = 7365005) B7365005
theorem B3273335 : Blo 2181435 3273335 := bstep (se 1 (by rfl) ⟨2455001, by rfl⟩ : syracuseStep 3273335 = 4910003) B4910003
theorem B2182223 : Blo 2181435 2182223 := bstep (se 1 (by rfl) ⟨1636667, by rfl⟩ : syracuseStep 2182223 = 3273335) B3273335
theorem B3273341 : Blo 2181435 3273341 := bbase (se 3 (by rfl) ⟨613751, by rfl⟩ : syracuseStep 3273341 = 1227503) (by norm_num)
theorem B2182227 : Blo 2181435 2182227 := bstep (se 1 (by rfl) ⟨1636670, by rfl⟩ : syracuseStep 2182227 = 3273341) B3273341
theorem B4910021 : Blo 2181435 4910021 := bbase (se 4 (by rfl) ⟨460314, by rfl⟩ : syracuseStep 4910021 = 920629) (by norm_num)
theorem B3273347 : Blo 2181435 3273347 := bstep (se 1 (by rfl) ⟨2455010, by rfl⟩ : syracuseStep 3273347 = 4910021) B4910021
theorem B2182231 : Blo 2181435 2182231 := bstep (se 1 (by rfl) ⟨1636673, by rfl⟩ : syracuseStep 2182231 = 3273347) B3273347
theorem B2621641 : Blo 2181435 2621641 := bbase (se 2 (by rfl) ⟨983115, by rfl⟩ : syracuseStep 2621641 = 1966231) (by norm_num)
theorem B3495521 : Blo 2181435 3495521 := bstep (se 2 (by rfl) ⟨1310820, by rfl⟩ : syracuseStep 3495521 = 2621641) B2621641
theorem B9321389 : Blo 2181435 9321389 := bstep (se 3 (by rfl) ⟨1747760, by rfl⟩ : syracuseStep 9321389 = 3495521) B3495521
theorem B6214259 : Blo 2181435 6214259 := bstep (se 1 (by rfl) ⟨4660694, by rfl⟩ : syracuseStep 6214259 = 9321389) B9321389
theorem B4142839 : Blo 2181435 4142839 := bstep (se 1 (by rfl) ⟨3107129, by rfl⟩ : syracuseStep 4142839 = 6214259) B6214259
theorem B5523785 : Blo 2181435 5523785 := bstep (se 2 (by rfl) ⟨2071419, by rfl⟩ : syracuseStep 5523785 = 4142839) B4142839
theorem B3682523 : Blo 2181435 3682523 := bstep (se 1 (by rfl) ⟨2761892, by rfl⟩ : syracuseStep 3682523 = 5523785) B5523785
theorem B2455015 : Blo 2181435 2455015 := bstep (se 1 (by rfl) ⟨1841261, by rfl⟩ : syracuseStep 2455015 = 3682523) B3682523
theorem B3273353 : Blo 2181435 3273353 := bstep (se 2 (by rfl) ⟨1227507, by rfl⟩ : syracuseStep 3273353 = 2455015) B2455015
theorem B2182235 : Blo 2181435 2182235 := bstep (se 1 (by rfl) ⟨1636676, by rfl⟩ : syracuseStep 2182235 = 3273353) B3273353
theorem B11047589 : Blo 2181435 11047589 := bbase (se 4 (by rfl) ⟨1035711, by rfl⟩ : syracuseStep 11047589 = 2071423) (by norm_num)
theorem B7365059 : Blo 2181435 7365059 := bstep (se 1 (by rfl) ⟨5523794, by rfl⟩ : syracuseStep 7365059 = 11047589) B11047589
theorem B4910039 : Blo 2181435 4910039 := bstep (se 1 (by rfl) ⟨3682529, by rfl⟩ : syracuseStep 4910039 = 7365059) B7365059
theorem B3273359 : Blo 2181435 3273359 := bstep (se 1 (by rfl) ⟨2455019, by rfl⟩ : syracuseStep 3273359 = 4910039) B4910039
theorem B2182239 : Blo 2181435 2182239 := bstep (se 1 (by rfl) ⟨1636679, by rfl⟩ : syracuseStep 2182239 = 3273359) B3273359
theorem B3273365 : Blo 2181435 3273365 := bbase (se 6 (by rfl) ⟨76719, by rfl⟩ : syracuseStep 3273365 = 153439) (by norm_num)
theorem B2182243 : Blo 2181435 2182243 := bstep (se 1 (by rfl) ⟨1636682, by rfl⟩ : syracuseStep 2182243 = 3273365) B3273365
theorem B25196309 : Blo 2181435 25196309 := bbase (se 6 (by rfl) ⟨590538, by rfl⟩ : syracuseStep 25196309 = 1181077) (by norm_num)
theorem B16797539 : Blo 2181435 16797539 := bstep (se 1 (by rfl) ⟨12598154, by rfl⟩ : syracuseStep 16797539 = 25196309) B25196309
theorem B11198359 : Blo 2181435 11198359 := bstep (se 1 (by rfl) ⟨8398769, by rfl⟩ : syracuseStep 11198359 = 16797539) B16797539
theorem B14931145 : Blo 2181435 14931145 := bstep (se 2 (by rfl) ⟨5599179, by rfl⟩ : syracuseStep 14931145 = 11198359) B11198359
theorem B19908193 : Blo 2181435 19908193 := bstep (se 2 (by rfl) ⟨7465572, by rfl⟩ : syracuseStep 19908193 = 14931145) B14931145
theorem B26544257 : Blo 2181435 26544257 := bstep (se 2 (by rfl) ⟨9954096, by rfl⟩ : syracuseStep 26544257 = 19908193) B19908193
theorem B17696171 : Blo 2181435 17696171 := bstep (se 1 (by rfl) ⟨13272128, by rfl⟩ : syracuseStep 17696171 = 26544257) B26544257
theorem B47189789 : Blo 2181435 47189789 := bstep (se 3 (by rfl) ⟨8848085, by rfl⟩ : syracuseStep 47189789 = 17696171) B17696171
theorem B31459859 : Blo 2181435 31459859 := bstep (se 1 (by rfl) ⟨23594894, by rfl⟩ : syracuseStep 31459859 = 47189789) B47189789
theorem B20973239 : Blo 2181435 20973239 := bstep (se 1 (by rfl) ⟨15729929, by rfl⟩ : syracuseStep 20973239 = 31459859) B31459859
theorem B13982159 : Blo 2181435 13982159 := bstep (se 1 (by rfl) ⟨10486619, by rfl⟩ : syracuseStep 13982159 = 20973239) B20973239
theorem B9321439 : Blo 2181435 9321439 := bstep (se 1 (by rfl) ⟨6991079, by rfl⟩ : syracuseStep 9321439 = 13982159) B13982159
theorem B12428585 : Blo 2181435 12428585 := bstep (se 2 (by rfl) ⟨4660719, by rfl⟩ : syracuseStep 12428585 = 9321439) B9321439
theorem B8285723 : Blo 2181435 8285723 := bstep (se 1 (by rfl) ⟨6214292, by rfl⟩ : syracuseStep 8285723 = 12428585) B12428585
theorem B5523815 : Blo 2181435 5523815 := bstep (se 1 (by rfl) ⟨4142861, by rfl⟩ : syracuseStep 5523815 = 8285723) B8285723
theorem B3682543 : Blo 2181435 3682543 := bstep (se 1 (by rfl) ⟨2761907, by rfl⟩ : syracuseStep 3682543 = 5523815) B5523815
theorem B4910057 : Blo 2181435 4910057 := bstep (se 2 (by rfl) ⟨1841271, by rfl⟩ : syracuseStep 4910057 = 3682543) B3682543
theorem B3273371 : Blo 2181435 3273371 := bstep (se 1 (by rfl) ⟨2455028, by rfl⟩ : syracuseStep 3273371 = 4910057) B4910057
theorem B2182247 : Blo 2181435 2182247 := bstep (se 1 (by rfl) ⟨1636685, by rfl⟩ : syracuseStep 2182247 = 3273371) B3273371
theorem B2455033 : Blo 2181435 2455033 := bbase (se 2 (by rfl) ⟨920637, by rfl⟩ : syracuseStep 2455033 = 1841275) (by norm_num)
theorem B3273377 : Blo 2181435 3273377 := bstep (se 2 (by rfl) ⟨1227516, by rfl⟩ : syracuseStep 3273377 = 2455033) B2455033
theorem B2182251 : Blo 2181435 2182251 := bstep (se 1 (by rfl) ⟨1636688, by rfl⟩ : syracuseStep 2182251 = 3273377) B3273377
theorem B2949373 : Blo 2181435 2949373 := bbase (se 3 (by rfl) ⟨553007, by rfl⟩ : syracuseStep 2949373 = 1106015) (by norm_num)
theorem B3932497 : Blo 2181435 3932497 := bstep (se 2 (by rfl) ⟨1474686, by rfl⟩ : syracuseStep 3932497 = 2949373) B2949373
theorem B5243329 : Blo 2181435 5243329 := bstep (se 2 (by rfl) ⟨1966248, by rfl⟩ : syracuseStep 5243329 = 3932497) B3932497
theorem B6991105 : Blo 2181435 6991105 := bstep (se 2 (by rfl) ⟨2621664, by rfl⟩ : syracuseStep 6991105 = 5243329) B5243329
theorem B9321473 : Blo 2181435 9321473 := bstep (se 2 (by rfl) ⟨3495552, by rfl⟩ : syracuseStep 9321473 = 6991105) B6991105
theorem B6214315 : Blo 2181435 6214315 := bstep (se 1 (by rfl) ⟨4660736, by rfl⟩ : syracuseStep 6214315 = 9321473) B9321473
theorem B8285753 : Blo 2181435 8285753 := bstep (se 2 (by rfl) ⟨3107157, by rfl⟩ : syracuseStep 8285753 = 6214315) B6214315
theorem B5523835 : Blo 2181435 5523835 := bstep (se 1 (by rfl) ⟨4142876, by rfl⟩ : syracuseStep 5523835 = 8285753) B8285753
theorem B7365113 : Blo 2181435 7365113 := bstep (se 2 (by rfl) ⟨2761917, by rfl⟩ : syracuseStep 7365113 = 5523835) B5523835
theorem B4910075 : Blo 2181435 4910075 := bstep (se 1 (by rfl) ⟨3682556, by rfl⟩ : syracuseStep 4910075 = 7365113) B7365113
theorem B3273383 : Blo 2181435 3273383 := bstep (se 1 (by rfl) ⟨2455037, by rfl⟩ : syracuseStep 3273383 = 4910075) B4910075
theorem B2182255 : Blo 2181435 2182255 := bstep (se 1 (by rfl) ⟨1636691, by rfl⟩ : syracuseStep 2182255 = 3273383) B3273383
theorem B3273389 : Blo 2181435 3273389 := bbase (se 3 (by rfl) ⟨613760, by rfl⟩ : syracuseStep 3273389 = 1227521) (by norm_num)
theorem B2182259 : Blo 2181435 2182259 := bstep (se 1 (by rfl) ⟨1636694, by rfl⟩ : syracuseStep 2182259 = 3273389) B3273389
theorem B4910093 : Blo 2181435 4910093 := bbase (se 3 (by rfl) ⟨920642, by rfl⟩ : syracuseStep 4910093 = 1841285) (by norm_num)
theorem B3273395 : Blo 2181435 3273395 := bstep (se 1 (by rfl) ⟨2455046, by rfl⟩ : syracuseStep 3273395 = 4910093) B4910093
theorem B2182263 : Blo 2181435 2182263 := bstep (se 1 (by rfl) ⟨1636697, by rfl⟩ : syracuseStep 2182263 = 3273395) B3273395
theorem B2761933 : Blo 2181435 2761933 := bbase (se 3 (by rfl) ⟨517862, by rfl⟩ : syracuseStep 2761933 = 1035725) (by norm_num)
theorem B3682577 : Blo 2181435 3682577 := bstep (se 2 (by rfl) ⟨1380966, by rfl⟩ : syracuseStep 3682577 = 2761933) B2761933
theorem B2455051 : Blo 2181435 2455051 := bstep (se 1 (by rfl) ⟨1841288, by rfl⟩ : syracuseStep 2455051 = 3682577) B3682577
theorem B3273401 : Blo 2181435 3273401 := bstep (se 2 (by rfl) ⟨1227525, by rfl⟩ : syracuseStep 3273401 = 2455051) B2455051
theorem B2182267 : Blo 2181435 2182267 := bstep (se 1 (by rfl) ⟨1636700, by rfl⟩ : syracuseStep 2182267 = 3273401) B3273401
theorem B7972357 : Blo 2181435 7972357 := bbase (se 4 (by rfl) ⟨747408, by rfl⟩ : syracuseStep 7972357 = 1494817) (by norm_num)
theorem B10629809 : Blo 2181435 10629809 := bstep (se 2 (by rfl) ⟨3986178, by rfl⟩ : syracuseStep 10629809 = 7972357) B7972357
theorem B7086539 : Blo 2181435 7086539 := bstep (se 1 (by rfl) ⟨5314904, by rfl⟩ : syracuseStep 7086539 = 10629809) B10629809
theorem B18897437 : Blo 2181435 18897437 := bstep (se 3 (by rfl) ⟨3543269, by rfl⟩ : syracuseStep 18897437 = 7086539) B7086539
theorem B12598291 : Blo 2181435 12598291 := bstep (se 1 (by rfl) ⟨9448718, by rfl⟩ : syracuseStep 12598291 = 18897437) B18897437
theorem B16797721 : Blo 2181435 16797721 := bstep (se 2 (by rfl) ⟨6299145, by rfl⟩ : syracuseStep 16797721 = 12598291) B12598291
theorem B22396961 : Blo 2181435 22396961 := bstep (se 2 (by rfl) ⟨8398860, by rfl⟩ : syracuseStep 22396961 = 16797721) B16797721
theorem B14931307 : Blo 2181435 14931307 := bstep (se 1 (by rfl) ⟨11198480, by rfl⟩ : syracuseStep 14931307 = 22396961) B22396961
theorem B79633637 : Blo 2181435 79633637 := bstep (se 4 (by rfl) ⟨7465653, by rfl⟩ : syracuseStep 79633637 = 14931307) B14931307
theorem B53089091 : Blo 2181435 53089091 := bstep (se 1 (by rfl) ⟨39816818, by rfl⟩ : syracuseStep 53089091 = 79633637) B79633637
theorem B35392727 : Blo 2181435 35392727 := bstep (se 1 (by rfl) ⟨26544545, by rfl⟩ : syracuseStep 35392727 = 53089091) B53089091
theorem B23595151 : Blo 2181435 23595151 := bstep (se 1 (by rfl) ⟨17696363, by rfl⟩ : syracuseStep 23595151 = 35392727) B35392727
theorem B31460201 : Blo 2181435 31460201 := bstep (se 2 (by rfl) ⟨11797575, by rfl⟩ : syracuseStep 31460201 = 23595151) B23595151
theorem B20973467 : Blo 2181435 20973467 := bstep (se 1 (by rfl) ⟨15730100, by rfl⟩ : syracuseStep 20973467 = 31460201) B31460201
theorem B13982311 : Blo 2181435 13982311 := bstep (se 1 (by rfl) ⟨10486733, by rfl⟩ : syracuseStep 13982311 = 20973467) B20973467
theorem B18643081 : Blo 2181435 18643081 := bstep (se 2 (by rfl) ⟨6991155, by rfl⟩ : syracuseStep 18643081 = 13982311) B13982311
theorem B24857441 : Blo 2181435 24857441 := bstep (se 2 (by rfl) ⟨9321540, by rfl⟩ : syracuseStep 24857441 = 18643081) B18643081
theorem B16571627 : Blo 2181435 16571627 := bstep (se 1 (by rfl) ⟨12428720, by rfl⟩ : syracuseStep 16571627 = 24857441) B24857441
theorem B11047751 : Blo 2181435 11047751 := bstep (se 1 (by rfl) ⟨8285813, by rfl⟩ : syracuseStep 11047751 = 16571627) B16571627
theorem B7365167 : Blo 2181435 7365167 := bstep (se 1 (by rfl) ⟨5523875, by rfl⟩ : syracuseStep 7365167 = 11047751) B11047751
theorem B4910111 : Blo 2181435 4910111 := bstep (se 1 (by rfl) ⟨3682583, by rfl⟩ : syracuseStep 4910111 = 7365167) B7365167
theorem B3273407 : Blo 2181435 3273407 := bstep (se 1 (by rfl) ⟨2455055, by rfl⟩ : syracuseStep 3273407 = 4910111) B4910111
theorem B2182271 : Blo 2181435 2182271 := bstep (se 1 (by rfl) ⟨1636703, by rfl⟩ : syracuseStep 2182271 = 3273407) B3273407
theorem B3273413 : Blo 2181435 3273413 := bbase (se 4 (by rfl) ⟨306882, by rfl⟩ : syracuseStep 3273413 = 613765) (by norm_num)
theorem B2182275 : Blo 2181435 2182275 := bstep (se 1 (by rfl) ⟨1636706, by rfl⟩ : syracuseStep 2182275 = 3273413) B3273413
theorem B3682597 : Blo 2181435 3682597 := bbase (se 4 (by rfl) ⟨345243, by rfl⟩ : syracuseStep 3682597 = 690487) (by norm_num)
theorem B4910129 : Blo 2181435 4910129 := bstep (se 2 (by rfl) ⟨1841298, by rfl⟩ : syracuseStep 4910129 = 3682597) B3682597
theorem B3273419 : Blo 2181435 3273419 := bstep (se 1 (by rfl) ⟨2455064, by rfl⟩ : syracuseStep 3273419 = 4910129) B4910129
theorem B2182279 : Blo 2181435 2182279 := bstep (se 1 (by rfl) ⟨1636709, by rfl⟩ : syracuseStep 2182279 = 3273419) B3273419
theorem B2455069 : Blo 2181435 2455069 := bbase (se 3 (by rfl) ⟨460325, by rfl⟩ : syracuseStep 2455069 = 920651) (by norm_num)
theorem B3273425 : Blo 2181435 3273425 := bstep (se 2 (by rfl) ⟨1227534, by rfl⟩ : syracuseStep 3273425 = 2455069) B2455069
theorem B2182283 : Blo 2181435 2182283 := bstep (se 1 (by rfl) ⟨1636712, by rfl⟩ : syracuseStep 2182283 = 3273425) B3273425
theorem B7365221 : Blo 2181435 7365221 := bbase (se 4 (by rfl) ⟨690489, by rfl⟩ : syracuseStep 7365221 = 1380979) (by norm_num)
theorem B4910147 : Blo 2181435 4910147 := bstep (se 1 (by rfl) ⟨3682610, by rfl⟩ : syracuseStep 4910147 = 7365221) B7365221
theorem B3273431 : Blo 2181435 3273431 := bstep (se 1 (by rfl) ⟨2455073, by rfl⟩ : syracuseStep 3273431 = 4910147) B4910147
theorem B2182287 : Blo 2181435 2182287 := bstep (se 1 (by rfl) ⟨1636715, by rfl⟩ : syracuseStep 2182287 = 3273431) B3273431
theorem B3273437 : Blo 2181435 3273437 := bbase (se 3 (by rfl) ⟨613769, by rfl⟩ : syracuseStep 3273437 = 1227539) (by norm_num)
theorem B2182291 : Blo 2181435 2182291 := bstep (se 1 (by rfl) ⟨1636718, by rfl⟩ : syracuseStep 2182291 = 3273437) B3273437
theorem B4910165 : Blo 2181435 4910165 := bbase (se 8 (by rfl) ⟨28770, by rfl⟩ : syracuseStep 4910165 = 57541) (by norm_num)
theorem B3273443 : Blo 2181435 3273443 := bstep (se 1 (by rfl) ⟨2455082, by rfl⟩ : syracuseStep 3273443 = 4910165) B4910165
theorem B2182295 : Blo 2181435 2182295 := bstep (se 1 (by rfl) ⟨1636721, by rfl⟩ : syracuseStep 2182295 = 3273443) B3273443
theorem B4424149 : Blo 2181435 4424149 := bbase (se 7 (by rfl) ⟨51845, by rfl⟩ : syracuseStep 4424149 = 103691) (by norm_num)
theorem B23595461 : Blo 2181435 23595461 := bstep (se 4 (by rfl) ⟨2212074, by rfl⟩ : syracuseStep 23595461 = 4424149) B4424149
theorem B15730307 : Blo 2181435 15730307 := bstep (se 1 (by rfl) ⟨11797730, by rfl⟩ : syracuseStep 15730307 = 23595461) B23595461
theorem B10486871 : Blo 2181435 10486871 := bstep (se 1 (by rfl) ⟨7865153, by rfl⟩ : syracuseStep 10486871 = 15730307) B15730307
theorem B6991247 : Blo 2181435 6991247 := bstep (se 1 (by rfl) ⟨5243435, by rfl⟩ : syracuseStep 6991247 = 10486871) B10486871
theorem B4660831 : Blo 2181435 4660831 := bstep (se 1 (by rfl) ⟨3495623, by rfl⟩ : syracuseStep 4660831 = 6991247) B6991247
theorem B6214441 : Blo 2181435 6214441 := bstep (se 2 (by rfl) ⟨2330415, by rfl⟩ : syracuseStep 6214441 = 4660831) B4660831
theorem B8285921 : Blo 2181435 8285921 := bstep (se 2 (by rfl) ⟨3107220, by rfl⟩ : syracuseStep 8285921 = 6214441) B6214441
theorem B5523947 : Blo 2181435 5523947 := bstep (se 1 (by rfl) ⟨4142960, by rfl⟩ : syracuseStep 5523947 = 8285921) B8285921
theorem B3682631 : Blo 2181435 3682631 := bstep (se 1 (by rfl) ⟨2761973, by rfl⟩ : syracuseStep 3682631 = 5523947) B5523947
theorem B2455087 : Blo 2181435 2455087 := bstep (se 1 (by rfl) ⟨1841315, by rfl⟩ : syracuseStep 2455087 = 3682631) B3682631
theorem B3273449 : Blo 2181435 3273449 := bstep (se 2 (by rfl) ⟨1227543, by rfl⟩ : syracuseStep 3273449 = 2455087) B2455087
theorem B2182299 : Blo 2181435 2182299 := bstep (se 1 (by rfl) ⟨1636724, by rfl⟩ : syracuseStep 2182299 = 3273449) B3273449
theorem B3986237 : Blo 2181435 3986237 := bbase (se 3 (by rfl) ⟨747419, by rfl⟩ : syracuseStep 3986237 = 1494839) (by norm_num)
theorem B2657491 : Blo 2181435 2657491 := bstep (se 1 (by rfl) ⟨1993118, by rfl⟩ : syracuseStep 2657491 = 3986237) B3986237
theorem B56693141 : Blo 2181435 56693141 := bstep (se 6 (by rfl) ⟨1328745, by rfl⟩ : syracuseStep 56693141 = 2657491) B2657491
theorem B37795427 : Blo 2181435 37795427 := bstep (se 1 (by rfl) ⟨28346570, by rfl⟩ : syracuseStep 37795427 = 56693141) B56693141
theorem B25196951 : Blo 2181435 25196951 := bstep (se 1 (by rfl) ⟨18897713, by rfl⟩ : syracuseStep 25196951 = 37795427) B37795427
theorem B67191869 : Blo 2181435 67191869 := bstep (se 3 (by rfl) ⟨12598475, by rfl⟩ : syracuseStep 67191869 = 25196951) B25196951
theorem B44794579 : Blo 2181435 44794579 := bstep (se 1 (by rfl) ⟨33595934, by rfl⟩ : syracuseStep 44794579 = 67191869) B67191869
theorem B59726105 : Blo 2181435 59726105 := bstep (se 2 (by rfl) ⟨22397289, by rfl⟩ : syracuseStep 59726105 = 44794579) B44794579
theorem B39817403 : Blo 2181435 39817403 := bstep (se 1 (by rfl) ⟨29863052, by rfl⟩ : syracuseStep 39817403 = 59726105) B59726105
theorem B26544935 : Blo 2181435 26544935 := bstep (se 1 (by rfl) ⟨19908701, by rfl⟩ : syracuseStep 26544935 = 39817403) B39817403
theorem B70786493 : Blo 2181435 70786493 := bstep (se 3 (by rfl) ⟨13272467, by rfl⟩ : syracuseStep 70786493 = 26544935) B26544935
theorem B47190995 : Blo 2181435 47190995 := bstep (se 1 (by rfl) ⟨35393246, by rfl⟩ : syracuseStep 47190995 = 70786493) B70786493
theorem B31460663 : Blo 2181435 31460663 := bstep (se 1 (by rfl) ⟨23595497, by rfl⟩ : syracuseStep 31460663 = 47190995) B47190995
theorem B20973775 : Blo 2181435 20973775 := bstep (se 1 (by rfl) ⟨15730331, by rfl⟩ : syracuseStep 20973775 = 31460663) B31460663
theorem B27965033 : Blo 2181435 27965033 := bstep (se 2 (by rfl) ⟨10486887, by rfl⟩ : syracuseStep 27965033 = 20973775) B20973775
theorem B18643355 : Blo 2181435 18643355 := bstep (se 1 (by rfl) ⟨13982516, by rfl⟩ : syracuseStep 18643355 = 27965033) B27965033
theorem B12428903 : Blo 2181435 12428903 := bstep (se 1 (by rfl) ⟨9321677, by rfl⟩ : syracuseStep 12428903 = 18643355) B18643355
theorem B8285935 : Blo 2181435 8285935 := bstep (se 1 (by rfl) ⟨6214451, by rfl⟩ : syracuseStep 8285935 = 12428903) B12428903
theorem B11047913 : Blo 2181435 11047913 := bstep (se 2 (by rfl) ⟨4142967, by rfl⟩ : syracuseStep 11047913 = 8285935) B8285935
theorem B7365275 : Blo 2181435 7365275 := bstep (se 1 (by rfl) ⟨5523956, by rfl⟩ : syracuseStep 7365275 = 11047913) B11047913
theorem B4910183 : Blo 2181435 4910183 := bstep (se 1 (by rfl) ⟨3682637, by rfl⟩ : syracuseStep 4910183 = 7365275) B7365275
theorem B3273455 : Blo 2181435 3273455 := bstep (se 1 (by rfl) ⟨2455091, by rfl⟩ : syracuseStep 3273455 = 4910183) B4910183
theorem B2182303 : Blo 2181435 2182303 := bstep (se 1 (by rfl) ⟨1636727, by rfl⟩ : syracuseStep 2182303 = 3273455) B3273455
theorem B3273461 : Blo 2181435 3273461 := bbase (se 5 (by rfl) ⟨153443, by rfl⟩ : syracuseStep 3273461 = 306887) (by norm_num)
theorem B2182307 : Blo 2181435 2182307 := bstep (se 1 (by rfl) ⟨1636730, by rfl⟩ : syracuseStep 2182307 = 3273461) B3273461
theorem B6991285 : Blo 2181435 6991285 := bbase (se 5 (by rfl) ⟨327716, by rfl⟩ : syracuseStep 6991285 = 655433) (by norm_num)
theorem B9321713 : Blo 2181435 9321713 := bstep (se 2 (by rfl) ⟨3495642, by rfl⟩ : syracuseStep 9321713 = 6991285) B6991285
theorem B6214475 : Blo 2181435 6214475 := bstep (se 1 (by rfl) ⟨4660856, by rfl⟩ : syracuseStep 6214475 = 9321713) B9321713
theorem B4142983 : Blo 2181435 4142983 := bstep (se 1 (by rfl) ⟨3107237, by rfl⟩ : syracuseStep 4142983 = 6214475) B6214475
theorem B5523977 : Blo 2181435 5523977 := bstep (se 2 (by rfl) ⟨2071491, by rfl⟩ : syracuseStep 5523977 = 4142983) B4142983
theorem B3682651 : Blo 2181435 3682651 := bstep (se 1 (by rfl) ⟨2761988, by rfl⟩ : syracuseStep 3682651 = 5523977) B5523977
theorem B4910201 : Blo 2181435 4910201 := bstep (se 2 (by rfl) ⟨1841325, by rfl⟩ : syracuseStep 4910201 = 3682651) B3682651
theorem B3273467 : Blo 2181435 3273467 := bstep (se 1 (by rfl) ⟨2455100, by rfl⟩ : syracuseStep 3273467 = 4910201) B4910201
theorem B2182311 : Blo 2181435 2182311 := bstep (se 1 (by rfl) ⟨1636733, by rfl⟩ : syracuseStep 2182311 = 3273467) B3273467
theorem B2455105 : Blo 2181435 2455105 := bbase (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) (by norm_num)
theorem B3273473 : Blo 2181435 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B2182315 : Blo 2181435 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B5523997 : Blo 2181435 5523997 := bbase (se 3 (by rfl) ⟨1035749, by rfl⟩ : syracuseStep 5523997 = 2071499) (by norm_num)
theorem B7365329 : Blo 2181435 7365329 := bstep (se 2 (by rfl) ⟨2761998, by rfl⟩ : syracuseStep 7365329 = 5523997) B5523997
theorem B4910219 : Blo 2181435 4910219 := bstep (se 1 (by rfl) ⟨3682664, by rfl⟩ : syracuseStep 4910219 = 7365329) B7365329
theorem B3273479 : Blo 2181435 3273479 := bstep (se 1 (by rfl) ⟨2455109, by rfl⟩ : syracuseStep 3273479 = 4910219) B4910219
theorem B2182319 : Blo 2181435 2182319 := bstep (se 1 (by rfl) ⟨1636739, by rfl⟩ : syracuseStep 2182319 = 3273479) B3273479
theorem B3273485 : Blo 2181435 3273485 := bbase (se 3 (by rfl) ⟨613778, by rfl⟩ : syracuseStep 3273485 = 1227557) (by norm_num)
theorem B2182323 : Blo 2181435 2182323 := bstep (se 1 (by rfl) ⟨1636742, by rfl⟩ : syracuseStep 2182323 = 3273485) B3273485
theorem B4910237 : Blo 2181435 4910237 := bbase (se 3 (by rfl) ⟨920669, by rfl⟩ : syracuseStep 4910237 = 1841339) (by norm_num)
theorem B3273491 : Blo 2181435 3273491 := bstep (se 1 (by rfl) ⟨2455118, by rfl⟩ : syracuseStep 3273491 = 4910237) B4910237
theorem B2182327 : Blo 2181435 2182327 := bstep (se 1 (by rfl) ⟨1636745, by rfl⟩ : syracuseStep 2182327 = 3273491) B3273491
theorem B3682685 : Blo 2181435 3682685 := bbase (se 3 (by rfl) ⟨690503, by rfl⟩ : syracuseStep 3682685 = 1381007) (by norm_num)
theorem B2455123 : Blo 2181435 2455123 := bstep (se 1 (by rfl) ⟨1841342, by rfl⟩ : syracuseStep 2455123 = 3682685) B3682685
theorem B3273497 : Blo 2181435 3273497 := bstep (se 2 (by rfl) ⟨1227561, by rfl⟩ : syracuseStep 3273497 = 2455123) B2455123
theorem B2182331 : Blo 2181435 2182331 := bstep (se 1 (by rfl) ⟨1636748, by rfl⟩ : syracuseStep 2182331 = 3273497) B3273497
theorem B7465877 : Blo 2181435 7465877 := bbase (se 6 (by rfl) ⟨174981, by rfl⟩ : syracuseStep 7465877 = 349963) (by norm_num)
theorem B4977251 : Blo 2181435 4977251 := bstep (se 1 (by rfl) ⟨3732938, by rfl⟩ : syracuseStep 4977251 = 7465877) B7465877
theorem B3318167 : Blo 2181435 3318167 := bstep (se 1 (by rfl) ⟨2488625, by rfl⟩ : syracuseStep 3318167 = 4977251) B4977251
theorem B2212111 : Blo 2181435 2212111 := bstep (se 1 (by rfl) ⟨1659083, by rfl⟩ : syracuseStep 2212111 = 3318167) B3318167
theorem B2949481 : Blo 2181435 2949481 := bstep (se 2 (by rfl) ⟨1106055, by rfl⟩ : syracuseStep 2949481 = 2212111) B2212111
theorem B3932641 : Blo 2181435 3932641 := bstep (se 2 (by rfl) ⟨1474740, by rfl⟩ : syracuseStep 3932641 = 2949481) B2949481
theorem B5243521 : Blo 2181435 5243521 := bstep (se 2 (by rfl) ⟨1966320, by rfl⟩ : syracuseStep 5243521 = 3932641) B3932641
theorem B6991361 : Blo 2181435 6991361 := bstep (se 2 (by rfl) ⟨2621760, by rfl⟩ : syracuseStep 6991361 = 5243521) B5243521
theorem B4660907 : Blo 2181435 4660907 := bstep (se 1 (by rfl) ⟨3495680, by rfl⟩ : syracuseStep 4660907 = 6991361) B6991361
theorem B12429085 : Blo 2181435 12429085 := bstep (se 3 (by rfl) ⟨2330453, by rfl⟩ : syracuseStep 12429085 = 4660907) B4660907
theorem B16572113 : Blo 2181435 16572113 := bstep (se 2 (by rfl) ⟨6214542, by rfl⟩ : syracuseStep 16572113 = 12429085) B12429085
theorem B11048075 : Blo 2181435 11048075 := bstep (se 1 (by rfl) ⟨8286056, by rfl⟩ : syracuseStep 11048075 = 16572113) B16572113
theorem B7365383 : Blo 2181435 7365383 := bstep (se 1 (by rfl) ⟨5524037, by rfl⟩ : syracuseStep 7365383 = 11048075) B11048075
theorem B4910255 : Blo 2181435 4910255 := bstep (se 1 (by rfl) ⟨3682691, by rfl⟩ : syracuseStep 4910255 = 7365383) B7365383
theorem B3273503 : Blo 2181435 3273503 := bstep (se 1 (by rfl) ⟨2455127, by rfl⟩ : syracuseStep 3273503 = 4910255) B4910255
theorem B2182335 : Blo 2181435 2182335 := bstep (se 1 (by rfl) ⟨1636751, by rfl⟩ : syracuseStep 2182335 = 3273503) B3273503
theorem B3273509 : Blo 2181435 3273509 := bbase (se 4 (by rfl) ⟨306891, by rfl⟩ : syracuseStep 3273509 = 613783) (by norm_num)
theorem B2182339 : Blo 2181435 2182339 := bstep (se 1 (by rfl) ⟨1636754, by rfl⟩ : syracuseStep 2182339 = 3273509) B3273509
theorem B2762029 : Blo 2181435 2762029 := bbase (se 3 (by rfl) ⟨517880, by rfl⟩ : syracuseStep 2762029 = 1035761) (by norm_num)
theorem B3682705 : Blo 2181435 3682705 := bstep (se 2 (by rfl) ⟨1381014, by rfl⟩ : syracuseStep 3682705 = 2762029) B2762029
theorem B4910273 : Blo 2181435 4910273 := bstep (se 2 (by rfl) ⟨1841352, by rfl⟩ : syracuseStep 4910273 = 3682705) B3682705
theorem B3273515 : Blo 2181435 3273515 := bstep (se 1 (by rfl) ⟨2455136, by rfl⟩ : syracuseStep 3273515 = 4910273) B4910273
theorem B2182343 : Blo 2181435 2182343 := bstep (se 1 (by rfl) ⟨1636757, by rfl⟩ : syracuseStep 2182343 = 3273515) B3273515
theorem B2455141 : Blo 2181435 2455141 := bbase (se 4 (by rfl) ⟨230169, by rfl⟩ : syracuseStep 2455141 = 460339) (by norm_num)
theorem B3273521 : Blo 2181435 3273521 := bstep (se 2 (by rfl) ⟨1227570, by rfl⟩ : syracuseStep 3273521 = 2455141) B2455141
theorem B2182347 : Blo 2181435 2182347 := bstep (se 1 (by rfl) ⟨1636760, by rfl⟩ : syracuseStep 2182347 = 3273521) B3273521
theorem B8969237 : Blo 2181435 8969237 := bbase (se 6 (by rfl) ⟨210216, by rfl⟩ : syracuseStep 8969237 = 420433) (by norm_num)
theorem B5979491 : Blo 2181435 5979491 := bstep (se 1 (by rfl) ⟨4484618, by rfl⟩ : syracuseStep 5979491 = 8969237) B8969237
theorem B3986327 : Blo 2181435 3986327 := bstep (se 1 (by rfl) ⟨2989745, by rfl⟩ : syracuseStep 3986327 = 5979491) B5979491
theorem B2657551 : Blo 2181435 2657551 := bstep (se 1 (by rfl) ⟨1993163, by rfl⟩ : syracuseStep 2657551 = 3986327) B3986327
theorem B56694421 : Blo 2181435 56694421 := bstep (se 6 (by rfl) ⟨1328775, by rfl⟩ : syracuseStep 56694421 = 2657551) B2657551
theorem B75592561 : Blo 2181435 75592561 := bstep (se 2 (by rfl) ⟨28347210, by rfl⟩ : syracuseStep 75592561 = 56694421) B56694421
theorem B100790081 : Blo 2181435 100790081 := bstep (se 2 (by rfl) ⟨37796280, by rfl⟩ : syracuseStep 100790081 = 75592561) B75592561
theorem B67193387 : Blo 2181435 67193387 := bstep (se 1 (by rfl) ⟨50395040, by rfl⟩ : syracuseStep 67193387 = 100790081) B100790081
theorem B44795591 : Blo 2181435 44795591 := bstep (se 1 (by rfl) ⟨33596693, by rfl⟩ : syracuseStep 44795591 = 67193387) B67193387
theorem B29863727 : Blo 2181435 29863727 := bstep (se 1 (by rfl) ⟨22397795, by rfl⟩ : syracuseStep 29863727 = 44795591) B44795591
theorem B19909151 : Blo 2181435 19909151 := bstep (se 1 (by rfl) ⟨14931863, by rfl⟩ : syracuseStep 19909151 = 29863727) B29863727
theorem B13272767 : Blo 2181435 13272767 := bstep (se 1 (by rfl) ⟨9954575, by rfl⟩ : syracuseStep 13272767 = 19909151) B19909151
theorem B8848511 : Blo 2181435 8848511 := bstep (se 1 (by rfl) ⟨6636383, by rfl⟩ : syracuseStep 8848511 = 13272767) B13272767
theorem B5899007 : Blo 2181435 5899007 := bstep (se 1 (by rfl) ⟨4424255, by rfl⟩ : syracuseStep 5899007 = 8848511) B8848511
theorem B3932671 : Blo 2181435 3932671 := bstep (se 1 (by rfl) ⟨2949503, by rfl⟩ : syracuseStep 3932671 = 5899007) B5899007
theorem B5243561 : Blo 2181435 5243561 := bstep (se 2 (by rfl) ⟨1966335, by rfl⟩ : syracuseStep 5243561 = 3932671) B3932671
theorem B3495707 : Blo 2181435 3495707 := bstep (se 1 (by rfl) ⟨2621780, by rfl⟩ : syracuseStep 3495707 = 5243561) B5243561
theorem B2330471 : Blo 2181435 2330471 := bstep (se 1 (by rfl) ⟨1747853, by rfl⟩ : syracuseStep 2330471 = 3495707) B3495707
theorem B6214589 : Blo 2181435 6214589 := bstep (se 3 (by rfl) ⟨1165235, by rfl⟩ : syracuseStep 6214589 = 2330471) B2330471
theorem B4143059 : Blo 2181435 4143059 := bstep (se 1 (by rfl) ⟨3107294, by rfl⟩ : syracuseStep 4143059 = 6214589) B6214589
theorem B2762039 : Blo 2181435 2762039 := bstep (se 1 (by rfl) ⟨2071529, by rfl⟩ : syracuseStep 2762039 = 4143059) B4143059
theorem B7365437 : Blo 2181435 7365437 := bstep (se 3 (by rfl) ⟨1381019, by rfl⟩ : syracuseStep 7365437 = 2762039) B2762039
theorem B4910291 : Blo 2181435 4910291 := bstep (se 1 (by rfl) ⟨3682718, by rfl⟩ : syracuseStep 4910291 = 7365437) B7365437
theorem B3273527 : Blo 2181435 3273527 := bstep (se 1 (by rfl) ⟨2455145, by rfl⟩ : syracuseStep 3273527 = 4910291) B4910291
theorem B2182351 : Blo 2181435 2182351 := bstep (se 1 (by rfl) ⟨1636763, by rfl⟩ : syracuseStep 2182351 = 3273527) B3273527
theorem B3273533 : Blo 2181435 3273533 := bbase (se 3 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 3273533 = 1227575) (by norm_num)
theorem B2182355 : Blo 2181435 2182355 := bstep (se 1 (by rfl) ⟨1636766, by rfl⟩ : syracuseStep 2182355 = 3273533) B3273533
theorem B4910309 : Blo 2181435 4910309 := bbase (se 4 (by rfl) ⟨460341, by rfl⟩ : syracuseStep 4910309 = 920683) (by norm_num)
theorem B3273539 : Blo 2181435 3273539 := bstep (se 1 (by rfl) ⟨2455154, by rfl⟩ : syracuseStep 3273539 = 4910309) B4910309
theorem B2182359 : Blo 2181435 2182359 := bstep (se 1 (by rfl) ⟨1636769, by rfl⟩ : syracuseStep 2182359 = 3273539) B3273539
theorem B5524109 : Blo 2181435 5524109 := bbase (se 3 (by rfl) ⟨1035770, by rfl⟩ : syracuseStep 5524109 = 2071541) (by norm_num)
theorem B3682739 : Blo 2181435 3682739 := bstep (se 1 (by rfl) ⟨2762054, by rfl⟩ : syracuseStep 3682739 = 5524109) B5524109
theorem B2455159 : Blo 2181435 2455159 := bstep (se 1 (by rfl) ⟨1841369, by rfl⟩ : syracuseStep 2455159 = 3682739) B3682739
theorem B3273545 : Blo 2181435 3273545 := bstep (se 2 (by rfl) ⟨1227579, by rfl⟩ : syracuseStep 3273545 = 2455159) B2455159
theorem B2182363 : Blo 2181435 2182363 := bstep (se 1 (by rfl) ⟨1636772, by rfl⟩ : syracuseStep 2182363 = 3273545) B3273545
theorem B3107317 : Blo 2181435 3107317 := bbase (se 5 (by rfl) ⟨145655, by rfl⟩ : syracuseStep 3107317 = 291311) (by norm_num)
theorem B4143089 : Blo 2181435 4143089 := bstep (se 2 (by rfl) ⟨1553658, by rfl⟩ : syracuseStep 4143089 = 3107317) B3107317
theorem B11048237 : Blo 2181435 11048237 := bstep (se 3 (by rfl) ⟨2071544, by rfl⟩ : syracuseStep 11048237 = 4143089) B4143089
theorem B7365491 : Blo 2181435 7365491 := bstep (se 1 (by rfl) ⟨5524118, by rfl⟩ : syracuseStep 7365491 = 11048237) B11048237
theorem B4910327 : Blo 2181435 4910327 := bstep (se 1 (by rfl) ⟨3682745, by rfl⟩ : syracuseStep 4910327 = 7365491) B7365491
theorem B3273551 : Blo 2181435 3273551 := bstep (se 1 (by rfl) ⟨2455163, by rfl⟩ : syracuseStep 3273551 = 4910327) B4910327
theorem B2182367 : Blo 2181435 2182367 := bstep (se 1 (by rfl) ⟨1636775, by rfl⟩ : syracuseStep 2182367 = 3273551) B3273551
theorem B3273557 : Blo 2181435 3273557 := bbase (se 9 (by rfl) ⟨9590, by rfl⟩ : syracuseStep 3273557 = 19181) (by norm_num)
theorem B2182371 : Blo 2181435 2182371 := bstep (se 1 (by rfl) ⟨1636778, by rfl⟩ : syracuseStep 2182371 = 3273557) B3273557
theorem B2621809 : Blo 2181435 2621809 := bbase (se 2 (by rfl) ⟨983178, by rfl⟩ : syracuseStep 2621809 = 1966357) (by norm_num)
theorem B3495745 : Blo 2181435 3495745 := bstep (se 2 (by rfl) ⟨1310904, by rfl⟩ : syracuseStep 3495745 = 2621809) B2621809
theorem B4660993 : Blo 2181435 4660993 := bstep (se 2 (by rfl) ⟨1747872, by rfl⟩ : syracuseStep 4660993 = 3495745) B3495745
theorem B6214657 : Blo 2181435 6214657 := bstep (se 2 (by rfl) ⟨2330496, by rfl⟩ : syracuseStep 6214657 = 4660993) B4660993
theorem B8286209 : Blo 2181435 8286209 := bstep (se 2 (by rfl) ⟨3107328, by rfl⟩ : syracuseStep 8286209 = 6214657) B6214657
theorem B5524139 : Blo 2181435 5524139 := bstep (se 1 (by rfl) ⟨4143104, by rfl⟩ : syracuseStep 5524139 = 8286209) B8286209
theorem B3682759 : Blo 2181435 3682759 := bstep (se 1 (by rfl) ⟨2762069, by rfl⟩ : syracuseStep 3682759 = 5524139) B5524139
theorem B4910345 : Blo 2181435 4910345 := bstep (se 2 (by rfl) ⟨1841379, by rfl⟩ : syracuseStep 4910345 = 3682759) B3682759
theorem B3273563 : Blo 2181435 3273563 := bstep (se 1 (by rfl) ⟨2455172, by rfl⟩ : syracuseStep 3273563 = 4910345) B4910345
theorem B2182375 : Blo 2181435 2182375 := bstep (se 1 (by rfl) ⟨1636781, by rfl⟩ : syracuseStep 2182375 = 3273563) B3273563
theorem B2455177 : Blo 2181435 2455177 := bbase (se 2 (by rfl) ⟨920691, by rfl⟩ : syracuseStep 2455177 = 1841383) (by norm_num)
theorem B3273569 : Blo 2181435 3273569 := bstep (se 2 (by rfl) ⟨1227588, by rfl⟩ : syracuseStep 3273569 = 2455177) B2455177
theorem B2182379 : Blo 2181435 2182379 := bstep (se 1 (by rfl) ⟨1636784, by rfl⟩ : syracuseStep 2182379 = 3273569) B3273569
theorem B5045269 : Blo 2181435 5045269 := bbase (se 6 (by rfl) ⟨118248, by rfl⟩ : syracuseStep 5045269 = 236497) (by norm_num)
theorem B6727025 : Blo 2181435 6727025 := bstep (se 2 (by rfl) ⟨2522634, by rfl⟩ : syracuseStep 6727025 = 5045269) B5045269
theorem B4484683 : Blo 2181435 4484683 := bstep (se 1 (by rfl) ⟨3363512, by rfl⟩ : syracuseStep 4484683 = 6727025) B6727025
theorem B5979577 : Blo 2181435 5979577 := bstep (se 2 (by rfl) ⟨2242341, by rfl⟩ : syracuseStep 5979577 = 4484683) B4484683
theorem B7972769 : Blo 2181435 7972769 := bstep (se 2 (by rfl) ⟨2989788, by rfl⟩ : syracuseStep 7972769 = 5979577) B5979577
theorem B21260717 : Blo 2181435 21260717 := bstep (se 3 (by rfl) ⟨3986384, by rfl⟩ : syracuseStep 21260717 = 7972769) B7972769
theorem B14173811 : Blo 2181435 14173811 := bstep (se 1 (by rfl) ⟨10630358, by rfl⟩ : syracuseStep 14173811 = 21260717) B21260717
theorem B9449207 : Blo 2181435 9449207 := bstep (se 1 (by rfl) ⟨7086905, by rfl⟩ : syracuseStep 9449207 = 14173811) B14173811
theorem B6299471 : Blo 2181435 6299471 := bstep (se 1 (by rfl) ⟨4724603, by rfl⟩ : syracuseStep 6299471 = 9449207) B9449207
theorem B4199647 : Blo 2181435 4199647 := bstep (se 1 (by rfl) ⟨3149735, by rfl⟩ : syracuseStep 4199647 = 6299471) B6299471
theorem B5599529 : Blo 2181435 5599529 := bstep (se 2 (by rfl) ⟨2099823, by rfl⟩ : syracuseStep 5599529 = 4199647) B4199647
theorem B3733019 : Blo 2181435 3733019 := bstep (se 1 (by rfl) ⟨2799764, by rfl⟩ : syracuseStep 3733019 = 5599529) B5599529
theorem B2488679 : Blo 2181435 2488679 := bstep (se 1 (by rfl) ⟨1866509, by rfl⟩ : syracuseStep 2488679 = 3733019) B3733019
theorem B26545909 : Blo 2181435 26545909 := bstep (se 5 (by rfl) ⟨1244339, by rfl⟩ : syracuseStep 26545909 = 2488679) B2488679
theorem B35394545 : Blo 2181435 35394545 := bstep (se 2 (by rfl) ⟨13272954, by rfl⟩ : syracuseStep 35394545 = 26545909) B26545909
theorem B23596363 : Blo 2181435 23596363 := bstep (se 1 (by rfl) ⟨17697272, by rfl⟩ : syracuseStep 23596363 = 35394545) B35394545
theorem B31461817 : Blo 2181435 31461817 := bstep (se 2 (by rfl) ⟨11798181, by rfl⟩ : syracuseStep 31461817 = 23596363) B23596363
theorem B41949089 : Blo 2181435 41949089 := bstep (se 2 (by rfl) ⟨15730908, by rfl⟩ : syracuseStep 41949089 = 31461817) B31461817
theorem B27966059 : Blo 2181435 27966059 := bstep (se 1 (by rfl) ⟨20974544, by rfl⟩ : syracuseStep 27966059 = 41949089) B41949089
theorem B18644039 : Blo 2181435 18644039 := bstep (se 1 (by rfl) ⟨13983029, by rfl⟩ : syracuseStep 18644039 = 27966059) B27966059
theorem B12429359 : Blo 2181435 12429359 := bstep (se 1 (by rfl) ⟨9322019, by rfl⟩ : syracuseStep 12429359 = 18644039) B18644039
theorem B8286239 : Blo 2181435 8286239 := bstep (se 1 (by rfl) ⟨6214679, by rfl⟩ : syracuseStep 8286239 = 12429359) B12429359
theorem B5524159 : Blo 2181435 5524159 := bstep (se 1 (by rfl) ⟨4143119, by rfl⟩ : syracuseStep 5524159 = 8286239) B8286239
theorem B7365545 : Blo 2181435 7365545 := bstep (se 2 (by rfl) ⟨2762079, by rfl⟩ : syracuseStep 7365545 = 5524159) B5524159
theorem B4910363 : Blo 2181435 4910363 := bstep (se 1 (by rfl) ⟨3682772, by rfl⟩ : syracuseStep 4910363 = 7365545) B7365545
theorem B3273575 : Blo 2181435 3273575 := bstep (se 1 (by rfl) ⟨2455181, by rfl⟩ : syracuseStep 3273575 = 4910363) B4910363
theorem B2182383 : Blo 2181435 2182383 := bstep (se 1 (by rfl) ⟨1636787, by rfl⟩ : syracuseStep 2182383 = 3273575) B3273575
theorem B3273581 : Blo 2181435 3273581 := bbase (se 3 (by rfl) ⟨613796, by rfl⟩ : syracuseStep 3273581 = 1227593) (by norm_num)
theorem B2182387 : Blo 2181435 2182387 := bstep (se 1 (by rfl) ⟨1636790, by rfl⟩ : syracuseStep 2182387 = 3273581) B3273581
theorem B4910381 : Blo 2181435 4910381 := bbase (se 3 (by rfl) ⟨920696, by rfl⟩ : syracuseStep 4910381 = 1841393) (by norm_num)
theorem B3273587 : Blo 2181435 3273587 := bstep (se 1 (by rfl) ⟨2455190, by rfl⟩ : syracuseStep 3273587 = 4910381) B4910381
theorem B2182391 : Blo 2181435 2182391 := bstep (se 1 (by rfl) ⟨1636793, by rfl⟩ : syracuseStep 2182391 = 3273587) B3273587
theorem B10487333 : Blo 2181435 10487333 := bbase (se 4 (by rfl) ⟨983187, by rfl⟩ : syracuseStep 10487333 = 1966375) (by norm_num)
theorem B6991555 : Blo 2181435 6991555 := bstep (se 1 (by rfl) ⟨5243666, by rfl⟩ : syracuseStep 6991555 = 10487333) B10487333
theorem B9322073 : Blo 2181435 9322073 := bstep (se 2 (by rfl) ⟨3495777, by rfl⟩ : syracuseStep 9322073 = 6991555) B6991555
theorem B6214715 : Blo 2181435 6214715 := bstep (se 1 (by rfl) ⟨4661036, by rfl⟩ : syracuseStep 6214715 = 9322073) B9322073
theorem B4143143 : Blo 2181435 4143143 := bstep (se 1 (by rfl) ⟨3107357, by rfl⟩ : syracuseStep 4143143 = 6214715) B6214715
theorem B2762095 : Blo 2181435 2762095 := bstep (se 1 (by rfl) ⟨2071571, by rfl⟩ : syracuseStep 2762095 = 4143143) B4143143
theorem B3682793 : Blo 2181435 3682793 := bstep (se 2 (by rfl) ⟨1381047, by rfl⟩ : syracuseStep 3682793 = 2762095) B2762095
theorem B2455195 : Blo 2181435 2455195 := bstep (se 1 (by rfl) ⟨1841396, by rfl⟩ : syracuseStep 2455195 = 3682793) B3682793
theorem B3273593 : Blo 2181435 3273593 := bstep (se 2 (by rfl) ⟨1227597, by rfl⟩ : syracuseStep 3273593 = 2455195) B2455195
theorem B2182395 : Blo 2181435 2182395 := bstep (se 1 (by rfl) ⟨1636796, by rfl⟩ : syracuseStep 2182395 = 3273593) B3273593
theorem B8969429 : Blo 2181435 8969429 := bbase (se 7 (by rfl) ⟨105110, by rfl⟩ : syracuseStep 8969429 = 210221) (by norm_num)
theorem B5979619 : Blo 2181435 5979619 := bstep (se 1 (by rfl) ⟨4484714, by rfl⟩ : syracuseStep 5979619 = 8969429) B8969429
theorem B7972825 : Blo 2181435 7972825 := bstep (se 2 (by rfl) ⟨2989809, by rfl⟩ : syracuseStep 7972825 = 5979619) B5979619
theorem B10630433 : Blo 2181435 10630433 := bstep (se 2 (by rfl) ⟨3986412, by rfl⟩ : syracuseStep 10630433 = 7972825) B7972825
theorem B7086955 : Blo 2181435 7086955 := bstep (se 1 (by rfl) ⟨5315216, by rfl⟩ : syracuseStep 7086955 = 10630433) B10630433
theorem B9449273 : Blo 2181435 9449273 := bstep (se 2 (by rfl) ⟨3543477, by rfl⟩ : syracuseStep 9449273 = 7086955) B7086955
theorem B6299515 : Blo 2181435 6299515 := bstep (se 1 (by rfl) ⟨4724636, by rfl⟩ : syracuseStep 6299515 = 9449273) B9449273
theorem B33597413 : Blo 2181435 33597413 := bstep (se 4 (by rfl) ⟨3149757, by rfl⟩ : syracuseStep 33597413 = 6299515) B6299515
theorem B22398275 : Blo 2181435 22398275 := bstep (se 1 (by rfl) ⟨16798706, by rfl⟩ : syracuseStep 22398275 = 33597413) B33597413
theorem B14932183 : Blo 2181435 14932183 := bstep (se 1 (by rfl) ⟨11199137, by rfl⟩ : syracuseStep 14932183 = 22398275) B22398275
theorem B19909577 : Blo 2181435 19909577 := bstep (se 2 (by rfl) ⟨7466091, by rfl⟩ : syracuseStep 19909577 = 14932183) B14932183
theorem B53092205 : Blo 2181435 53092205 := bstep (se 3 (by rfl) ⟨9954788, by rfl⟩ : syracuseStep 53092205 = 19909577) B19909577
theorem B35394803 : Blo 2181435 35394803 := bstep (se 1 (by rfl) ⟨26546102, by rfl⟩ : syracuseStep 35394803 = 53092205) B53092205
theorem B23596535 : Blo 2181435 23596535 := bstep (se 1 (by rfl) ⟨17697401, by rfl⟩ : syracuseStep 23596535 = 35394803) B35394803
theorem B15731023 : Blo 2181435 15731023 := bstep (se 1 (by rfl) ⟨11798267, by rfl⟩ : syracuseStep 15731023 = 23596535) B23596535
theorem B20974697 : Blo 2181435 20974697 := bstep (se 2 (by rfl) ⟨7865511, by rfl⟩ : syracuseStep 20974697 = 15731023) B15731023
theorem B13983131 : Blo 2181435 13983131 := bstep (se 1 (by rfl) ⟨10487348, by rfl⟩ : syracuseStep 13983131 = 20974697) B20974697
theorem B37288349 : Blo 2181435 37288349 := bstep (se 3 (by rfl) ⟨6991565, by rfl⟩ : syracuseStep 37288349 = 13983131) B13983131
theorem B24858899 : Blo 2181435 24858899 := bstep (se 1 (by rfl) ⟨18644174, by rfl⟩ : syracuseStep 24858899 = 37288349) B37288349
theorem B16572599 : Blo 2181435 16572599 := bstep (se 1 (by rfl) ⟨12429449, by rfl⟩ : syracuseStep 16572599 = 24858899) B24858899
theorem B11048399 : Blo 2181435 11048399 := bstep (se 1 (by rfl) ⟨8286299, by rfl⟩ : syracuseStep 11048399 = 16572599) B16572599
theorem B7365599 : Blo 2181435 7365599 := bstep (se 1 (by rfl) ⟨5524199, by rfl⟩ : syracuseStep 7365599 = 11048399) B11048399
theorem B4910399 : Blo 2181435 4910399 := bstep (se 1 (by rfl) ⟨3682799, by rfl⟩ : syracuseStep 4910399 = 7365599) B7365599
theorem B3273599 : Blo 2181435 3273599 := bstep (se 1 (by rfl) ⟨2455199, by rfl⟩ : syracuseStep 3273599 = 4910399) B4910399
theorem B2182399 : Blo 2181435 2182399 := bstep (se 1 (by rfl) ⟨1636799, by rfl⟩ : syracuseStep 2182399 = 3273599) B3273599
theorem B3273605 : Blo 2181435 3273605 := bbase (se 4 (by rfl) ⟨306900, by rfl⟩ : syracuseStep 3273605 = 613801) (by norm_num)
theorem B2182403 : Blo 2181435 2182403 := bstep (se 1 (by rfl) ⟨1636802, by rfl⟩ : syracuseStep 2182403 = 3273605) B3273605
theorem B3682813 : Blo 2181435 3682813 := bbase (se 3 (by rfl) ⟨690527, by rfl⟩ : syracuseStep 3682813 = 1381055) (by norm_num)
theorem B4910417 : Blo 2181435 4910417 := bstep (se 2 (by rfl) ⟨1841406, by rfl⟩ : syracuseStep 4910417 = 3682813) B3682813
theorem B3273611 : Blo 2181435 3273611 := bstep (se 1 (by rfl) ⟨2455208, by rfl⟩ : syracuseStep 3273611 = 4910417) B4910417
theorem B2182407 : Blo 2181435 2182407 := bstep (se 1 (by rfl) ⟨1636805, by rfl⟩ : syracuseStep 2182407 = 3273611) B3273611
theorem B2455213 : Blo 2181435 2455213 := bbase (se 3 (by rfl) ⟨460352, by rfl⟩ : syracuseStep 2455213 = 920705) (by norm_num)
theorem B3273617 : Blo 2181435 3273617 := bstep (se 2 (by rfl) ⟨1227606, by rfl⟩ : syracuseStep 3273617 = 2455213) B2455213
theorem B2182411 : Blo 2181435 2182411 := bstep (se 1 (by rfl) ⟨1636808, by rfl⟩ : syracuseStep 2182411 = 3273617) B3273617
theorem B7365653 : Blo 2181435 7365653 := bbase (se 6 (by rfl) ⟨172632, by rfl⟩ : syracuseStep 7365653 = 345265) (by norm_num)
theorem B4910435 : Blo 2181435 4910435 := bstep (se 1 (by rfl) ⟨3682826, by rfl⟩ : syracuseStep 4910435 = 7365653) B7365653
theorem B3273623 : Blo 2181435 3273623 := bstep (se 1 (by rfl) ⟨2455217, by rfl⟩ : syracuseStep 3273623 = 4910435) B4910435
theorem B2182415 : Blo 2181435 2182415 := bstep (se 1 (by rfl) ⟨1636811, by rfl⟩ : syracuseStep 2182415 = 3273623) B3273623
theorem B3273629 : Blo 2181435 3273629 := bbase (se 3 (by rfl) ⟨613805, by rfl⟩ : syracuseStep 3273629 = 1227611) (by norm_num)
theorem B2182419 : Blo 2181435 2182419 := bstep (se 1 (by rfl) ⟨1636814, by rfl⟩ : syracuseStep 2182419 = 3273629) B3273629
theorem B4910453 : Blo 2181435 4910453 := bbase (se 5 (by rfl) ⟨230177, by rfl⟩ : syracuseStep 4910453 = 460355) (by norm_num)
theorem B3273635 : Blo 2181435 3273635 := bstep (se 1 (by rfl) ⟨2455226, by rfl⟩ : syracuseStep 3273635 = 4910453) B4910453
theorem B2182423 : Blo 2181435 2182423 := bstep (se 1 (by rfl) ⟨1636817, by rfl⟩ : syracuseStep 2182423 = 3273635) B3273635
theorem B6636613 : Blo 2181435 6636613 := bbase (se 4 (by rfl) ⟨622182, by rfl⟩ : syracuseStep 6636613 = 1244365) (by norm_num)
theorem B8848817 : Blo 2181435 8848817 := bstep (se 2 (by rfl) ⟨3318306, by rfl⟩ : syracuseStep 8848817 = 6636613) B6636613
theorem B5899211 : Blo 2181435 5899211 := bstep (se 1 (by rfl) ⟨4424408, by rfl⟩ : syracuseStep 5899211 = 8848817) B8848817
theorem B3932807 : Blo 2181435 3932807 := bstep (se 1 (by rfl) ⟨2949605, by rfl⟩ : syracuseStep 3932807 = 5899211) B5899211
theorem B10487485 : Blo 2181435 10487485 := bstep (se 3 (by rfl) ⟨1966403, by rfl⟩ : syracuseStep 10487485 = 3932807) B3932807
theorem B13983313 : Blo 2181435 13983313 := bstep (se 2 (by rfl) ⟨5243742, by rfl⟩ : syracuseStep 13983313 = 10487485) B10487485
theorem B18644417 : Blo 2181435 18644417 := bstep (se 2 (by rfl) ⟨6991656, by rfl⟩ : syracuseStep 18644417 = 13983313) B13983313
theorem B12429611 : Blo 2181435 12429611 := bstep (se 1 (by rfl) ⟨9322208, by rfl⟩ : syracuseStep 12429611 = 18644417) B18644417
theorem B8286407 : Blo 2181435 8286407 := bstep (se 1 (by rfl) ⟨6214805, by rfl⟩ : syracuseStep 8286407 = 12429611) B12429611
theorem B5524271 : Blo 2181435 5524271 := bstep (se 1 (by rfl) ⟨4143203, by rfl⟩ : syracuseStep 5524271 = 8286407) B8286407
theorem B3682847 : Blo 2181435 3682847 := bstep (se 1 (by rfl) ⟨2762135, by rfl⟩ : syracuseStep 3682847 = 5524271) B5524271
theorem B2455231 : Blo 2181435 2455231 := bstep (se 1 (by rfl) ⟨1841423, by rfl⟩ : syracuseStep 2455231 = 3682847) B3682847
theorem B3273641 : Blo 2181435 3273641 := bstep (se 2 (by rfl) ⟨1227615, by rfl⟩ : syracuseStep 3273641 = 2455231) B2455231
theorem B2182427 : Blo 2181435 2182427 := bstep (se 1 (by rfl) ⟨1636820, by rfl⟩ : syracuseStep 2182427 = 3273641) B3273641
theorem B8286421 : Blo 2181435 8286421 := bbase (se 7 (by rfl) ⟨97106, by rfl⟩ : syracuseStep 8286421 = 194213) (by norm_num)
theorem B11048561 : Blo 2181435 11048561 := bstep (se 2 (by rfl) ⟨4143210, by rfl⟩ : syracuseStep 11048561 = 8286421) B8286421
theorem B7365707 : Blo 2181435 7365707 := bstep (se 1 (by rfl) ⟨5524280, by rfl⟩ : syracuseStep 7365707 = 11048561) B11048561
theorem B4910471 : Blo 2181435 4910471 := bstep (se 1 (by rfl) ⟨3682853, by rfl⟩ : syracuseStep 4910471 = 7365707) B7365707
theorem B3273647 : Blo 2181435 3273647 := bstep (se 1 (by rfl) ⟨2455235, by rfl⟩ : syracuseStep 3273647 = 4910471) B4910471
theorem B2182431 : Blo 2181435 2182431 := bstep (se 1 (by rfl) ⟨1636823, by rfl⟩ : syracuseStep 2182431 = 3273647) B3273647
theorem B3273653 : Blo 2181435 3273653 := bbase (se 5 (by rfl) ⟨153452, by rfl⟩ : syracuseStep 3273653 = 306905) (by norm_num)
theorem B2182435 : Blo 2181435 2182435 := bstep (se 1 (by rfl) ⟨1636826, by rfl⟩ : syracuseStep 2182435 = 3273653) B3273653
theorem B5524301 : Blo 2181435 5524301 := bbase (se 3 (by rfl) ⟨1035806, by rfl⟩ : syracuseStep 5524301 = 2071613) (by norm_num)
theorem B3682867 : Blo 2181435 3682867 := bstep (se 1 (by rfl) ⟨2762150, by rfl⟩ : syracuseStep 3682867 = 5524301) B5524301
theorem B4910489 : Blo 2181435 4910489 := bstep (se 2 (by rfl) ⟨1841433, by rfl⟩ : syracuseStep 4910489 = 3682867) B3682867
theorem B3273659 : Blo 2181435 3273659 := bstep (se 1 (by rfl) ⟨2455244, by rfl⟩ : syracuseStep 3273659 = 4910489) B4910489
theorem B2182439 : Blo 2181435 2182439 := bstep (se 1 (by rfl) ⟨1636829, by rfl⟩ : syracuseStep 2182439 = 3273659) B3273659
theorem B2455249 : Blo 2181435 2455249 := bbase (se 2 (by rfl) ⟨920718, by rfl⟩ : syracuseStep 2455249 = 1841437) (by norm_num)
theorem B3273665 : Blo 2181435 3273665 := bstep (se 2 (by rfl) ⟨1227624, by rfl⟩ : syracuseStep 3273665 = 2455249) B2455249
theorem B2182443 : Blo 2181435 2182443 := bstep (se 1 (by rfl) ⟨1636832, by rfl⟩ : syracuseStep 2182443 = 3273665) B3273665
theorem B2488753 : Blo 2181435 2488753 := bbase (se 2 (by rfl) ⟨933282, by rfl⟩ : syracuseStep 2488753 = 1866565) (by norm_num)
theorem B3318337 : Blo 2181435 3318337 := bstep (se 2 (by rfl) ⟨1244376, by rfl⟩ : syracuseStep 3318337 = 2488753) B2488753
theorem B17697797 : Blo 2181435 17697797 := bstep (se 4 (by rfl) ⟨1659168, by rfl⟩ : syracuseStep 17697797 = 3318337) B3318337
theorem B11798531 : Blo 2181435 11798531 := bstep (se 1 (by rfl) ⟨8848898, by rfl⟩ : syracuseStep 11798531 = 17697797) B17697797
theorem B7865687 : Blo 2181435 7865687 := bstep (se 1 (by rfl) ⟨5899265, by rfl⟩ : syracuseStep 7865687 = 11798531) B11798531
theorem B5243791 : Blo 2181435 5243791 := bstep (se 1 (by rfl) ⟨3932843, by rfl⟩ : syracuseStep 5243791 = 7865687) B7865687
theorem B6991721 : Blo 2181435 6991721 := bstep (se 2 (by rfl) ⟨2621895, by rfl⟩ : syracuseStep 6991721 = 5243791) B5243791
theorem B4661147 : Blo 2181435 4661147 := bstep (se 1 (by rfl) ⟨3495860, by rfl⟩ : syracuseStep 4661147 = 6991721) B6991721
theorem B3107431 : Blo 2181435 3107431 := bstep (se 1 (by rfl) ⟨2330573, by rfl⟩ : syracuseStep 3107431 = 4661147) B4661147
theorem B4143241 : Blo 2181435 4143241 := bstep (se 2 (by rfl) ⟨1553715, by rfl⟩ : syracuseStep 4143241 = 3107431) B3107431
theorem B5524321 : Blo 2181435 5524321 := bstep (se 2 (by rfl) ⟨2071620, by rfl⟩ : syracuseStep 5524321 = 4143241) B4143241
theorem B7365761 : Blo 2181435 7365761 := bstep (se 2 (by rfl) ⟨2762160, by rfl⟩ : syracuseStep 7365761 = 5524321) B5524321
theorem B4910507 : Blo 2181435 4910507 := bstep (se 1 (by rfl) ⟨3682880, by rfl⟩ : syracuseStep 4910507 = 7365761) B7365761
theorem B3273671 : Blo 2181435 3273671 := bstep (se 1 (by rfl) ⟨2455253, by rfl⟩ : syracuseStep 3273671 = 4910507) B4910507
theorem B2182447 : Blo 2181435 2182447 := bstep (se 1 (by rfl) ⟨1636835, by rfl⟩ : syracuseStep 2182447 = 3273671) B3273671
theorem B3273677 : Blo 2181435 3273677 := bbase (se 3 (by rfl) ⟨613814, by rfl⟩ : syracuseStep 3273677 = 1227629) (by norm_num)
theorem B2182451 : Blo 2181435 2182451 := bstep (se 1 (by rfl) ⟨1636838, by rfl⟩ : syracuseStep 2182451 = 3273677) B3273677
theorem B4910525 : Blo 2181435 4910525 := bbase (se 3 (by rfl) ⟨920723, by rfl⟩ : syracuseStep 4910525 = 1841447) (by norm_num)
theorem B3273683 : Blo 2181435 3273683 := bstep (se 1 (by rfl) ⟨2455262, by rfl⟩ : syracuseStep 3273683 = 4910525) B4910525
theorem B2182455 : Blo 2181435 2182455 := bstep (se 1 (by rfl) ⟨1636841, by rfl⟩ : syracuseStep 2182455 = 3273683) B3273683
theorem B3682901 : Blo 2181435 3682901 := bbase (se 8 (by rfl) ⟨21579, by rfl⟩ : syracuseStep 3682901 = 43159) (by norm_num)
theorem B2455267 : Blo 2181435 2455267 := bstep (se 1 (by rfl) ⟨1841450, by rfl⟩ : syracuseStep 2455267 = 3682901) B3682901
theorem B3273689 : Blo 2181435 3273689 := bstep (se 2 (by rfl) ⟨1227633, by rfl⟩ : syracuseStep 3273689 = 2455267) B2455267
theorem B2182459 : Blo 2181435 2182459 := bstep (se 1 (by rfl) ⟨1636844, by rfl⟩ : syracuseStep 2182459 = 3273689) B3273689
theorem B4977541 : Blo 2181435 4977541 := bbase (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) (by norm_num)
theorem B26546885 : Blo 2181435 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B17697923 : Blo 2181435 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B11798615 : Blo 2181435 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B7865743 : Blo 2181435 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B10487657 : Blo 2181435 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B6991771 : Blo 2181435 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B9322361 : Blo 2181435 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B6214907 : Blo 2181435 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B16573085 : Blo 2181435 16573085 := bstep (se 3 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 16573085 = 6214907) B6214907
theorem B11048723 : Blo 2181435 11048723 := bstep (se 1 (by rfl) ⟨8286542, by rfl⟩ : syracuseStep 11048723 = 16573085) B16573085
theorem B7365815 : Blo 2181435 7365815 := bstep (se 1 (by rfl) ⟨5524361, by rfl⟩ : syracuseStep 7365815 = 11048723) B11048723
theorem B4910543 : Blo 2181435 4910543 := bstep (se 1 (by rfl) ⟨3682907, by rfl⟩ : syracuseStep 4910543 = 7365815) B7365815
theorem B3273695 : Blo 2181435 3273695 := bstep (se 1 (by rfl) ⟨2455271, by rfl⟩ : syracuseStep 3273695 = 4910543) B4910543
theorem B2182463 : Blo 2181435 2182463 := bstep (se 1 (by rfl) ⟨1636847, by rfl⟩ : syracuseStep 2182463 = 3273695) B3273695
theorem B3273701 : Blo 2181435 3273701 := bbase (se 4 (by rfl) ⟨306909, by rfl⟩ : syracuseStep 3273701 = 613819) (by norm_num)
theorem B2182467 : Blo 2181435 2182467 := bstep (se 1 (by rfl) ⟨1636850, by rfl⟩ : syracuseStep 2182467 = 3273701) B3273701
theorem B8848997 : Blo 2181435 8848997 := bbase (se 4 (by rfl) ⟨829593, by rfl⟩ : syracuseStep 8848997 = 1659187) (by norm_num)
theorem B5899331 : Blo 2181435 5899331 := bstep (se 1 (by rfl) ⟨4424498, by rfl⟩ : syracuseStep 5899331 = 8848997) B8848997
theorem B3932887 : Blo 2181435 3932887 := bstep (se 1 (by rfl) ⟨2949665, by rfl⟩ : syracuseStep 3932887 = 5899331) B5899331
theorem B5243849 : Blo 2181435 5243849 := bstep (se 2 (by rfl) ⟨1966443, by rfl⟩ : syracuseStep 5243849 = 3932887) B3932887
theorem B3495899 : Blo 2181435 3495899 := bstep (se 1 (by rfl) ⟨2621924, by rfl⟩ : syracuseStep 3495899 = 5243849) B5243849
theorem B9322397 : Blo 2181435 9322397 := bstep (se 3 (by rfl) ⟨1747949, by rfl⟩ : syracuseStep 9322397 = 3495899) B3495899
theorem B6214931 : Blo 2181435 6214931 := bstep (se 1 (by rfl) ⟨4661198, by rfl⟩ : syracuseStep 6214931 = 9322397) B9322397
theorem B4143287 : Blo 2181435 4143287 := bstep (se 1 (by rfl) ⟨3107465, by rfl⟩ : syracuseStep 4143287 = 6214931) B6214931
theorem B2762191 : Blo 2181435 2762191 := bstep (se 1 (by rfl) ⟨2071643, by rfl⟩ : syracuseStep 2762191 = 4143287) B4143287
theorem B3682921 : Blo 2181435 3682921 := bstep (se 2 (by rfl) ⟨1381095, by rfl⟩ : syracuseStep 3682921 = 2762191) B2762191
theorem B4910561 : Blo 2181435 4910561 := bstep (se 2 (by rfl) ⟨1841460, by rfl⟩ : syracuseStep 4910561 = 3682921) B3682921
theorem B3273707 : Blo 2181435 3273707 := bstep (se 1 (by rfl) ⟨2455280, by rfl⟩ : syracuseStep 3273707 = 4910561) B4910561
theorem B2182471 : Blo 2181435 2182471 := bstep (se 1 (by rfl) ⟨1636853, by rfl⟩ : syracuseStep 2182471 = 3273707) B3273707
theorem B2455285 : Blo 2181435 2455285 := bbase (se 5 (by rfl) ⟨115091, by rfl⟩ : syracuseStep 2455285 = 230183) (by norm_num)
theorem B3273713 : Blo 2181435 3273713 := bstep (se 2 (by rfl) ⟨1227642, by rfl⟩ : syracuseStep 3273713 = 2455285) B2455285
theorem B2182475 : Blo 2181435 2182475 := bstep (se 1 (by rfl) ⟨1636856, by rfl⟩ : syracuseStep 2182475 = 3273713) B3273713
theorem B2762201 : Blo 2181435 2762201 := bbase (se 2 (by rfl) ⟨1035825, by rfl⟩ : syracuseStep 2762201 = 2071651) (by norm_num)
theorem B7365869 : Blo 2181435 7365869 := bstep (se 3 (by rfl) ⟨1381100, by rfl⟩ : syracuseStep 7365869 = 2762201) B2762201
theorem B4910579 : Blo 2181435 4910579 := bstep (se 1 (by rfl) ⟨3682934, by rfl⟩ : syracuseStep 4910579 = 7365869) B7365869
theorem B3273719 : Blo 2181435 3273719 := bstep (se 1 (by rfl) ⟨2455289, by rfl⟩ : syracuseStep 3273719 = 4910579) B4910579
theorem B2182479 : Blo 2181435 2182479 := bstep (se 1 (by rfl) ⟨1636859, by rfl⟩ : syracuseStep 2182479 = 3273719) B3273719
theorem B3273725 : Blo 2181435 3273725 := bbase (se 3 (by rfl) ⟨613823, by rfl⟩ : syracuseStep 3273725 = 1227647) (by norm_num)
theorem B2182483 : Blo 2181435 2182483 := bstep (se 1 (by rfl) ⟨1636862, by rfl⟩ : syracuseStep 2182483 = 3273725) B3273725
theorem B4910597 : Blo 2181435 4910597 := bbase (se 4 (by rfl) ⟨460368, by rfl⟩ : syracuseStep 4910597 = 920737) (by norm_num)
theorem B3273731 : Blo 2181435 3273731 := bstep (se 1 (by rfl) ⟨2455298, by rfl⟩ : syracuseStep 3273731 = 4910597) B4910597
theorem B2182487 : Blo 2181435 2182487 := bstep (se 1 (by rfl) ⟨1636865, by rfl⟩ : syracuseStep 2182487 = 3273731) B3273731
theorem B4143325 : Blo 2181435 4143325 := bbase (se 3 (by rfl) ⟨776873, by rfl⟩ : syracuseStep 4143325 = 1553747) (by norm_num)
theorem B5524433 : Blo 2181435 5524433 := bstep (se 2 (by rfl) ⟨2071662, by rfl⟩ : syracuseStep 5524433 = 4143325) B4143325
theorem B3682955 : Blo 2181435 3682955 := bstep (se 1 (by rfl) ⟨2762216, by rfl⟩ : syracuseStep 3682955 = 5524433) B5524433
theorem B2455303 : Blo 2181435 2455303 := bstep (se 1 (by rfl) ⟨1841477, by rfl⟩ : syracuseStep 2455303 = 3682955) B3682955
theorem B3273737 : Blo 2181435 3273737 := bstep (se 2 (by rfl) ⟨1227651, by rfl⟩ : syracuseStep 3273737 = 2455303) B2455303
theorem B2182491 : Blo 2181435 2182491 := bstep (se 1 (by rfl) ⟨1636868, by rfl⟩ : syracuseStep 2182491 = 3273737) B3273737
theorem B11048885 : Blo 2181435 11048885 := bbase (se 5 (by rfl) ⟨517916, by rfl⟩ : syracuseStep 11048885 = 1035833) (by norm_num)
theorem B7365923 : Blo 2181435 7365923 := bstep (se 1 (by rfl) ⟨5524442, by rfl⟩ : syracuseStep 7365923 = 11048885) B11048885
theorem B4910615 : Blo 2181435 4910615 := bstep (se 1 (by rfl) ⟨3682961, by rfl⟩ : syracuseStep 4910615 = 7365923) B7365923
theorem B3273743 : Blo 2181435 3273743 := bstep (se 1 (by rfl) ⟨2455307, by rfl⟩ : syracuseStep 3273743 = 4910615) B4910615
theorem B2182495 : Blo 2181435 2182495 := bstep (se 1 (by rfl) ⟨1636871, by rfl⟩ : syracuseStep 2182495 = 3273743) B3273743
theorem B3273749 : Blo 2181435 3273749 := bbase (se 6 (by rfl) ⟨76728, by rfl⟩ : syracuseStep 3273749 = 153457) (by norm_num)
theorem B2182499 : Blo 2181435 2182499 := bstep (se 1 (by rfl) ⟨1636874, by rfl⟩ : syracuseStep 2182499 = 3273749) B3273749
theorem B16799509 : Blo 2181435 16799509 := bbase (se 6 (by rfl) ⟨393738, by rfl⟩ : syracuseStep 16799509 = 787477) (by norm_num)
theorem B22399345 : Blo 2181435 22399345 := bstep (se 2 (by rfl) ⟨8399754, by rfl⟩ : syracuseStep 22399345 = 16799509) B16799509
theorem B29865793 : Blo 2181435 29865793 := bstep (se 2 (by rfl) ⟨11199672, by rfl⟩ : syracuseStep 29865793 = 22399345) B22399345
theorem B39821057 : Blo 2181435 39821057 := bstep (se 2 (by rfl) ⟨14932896, by rfl⟩ : syracuseStep 39821057 = 29865793) B29865793
theorem B26547371 : Blo 2181435 26547371 := bstep (se 1 (by rfl) ⟨19910528, by rfl⟩ : syracuseStep 26547371 = 39821057) B39821057
theorem B17698247 : Blo 2181435 17698247 := bstep (se 1 (by rfl) ⟨13273685, by rfl⟩ : syracuseStep 17698247 = 26547371) B26547371
theorem B11798831 : Blo 2181435 11798831 := bstep (se 1 (by rfl) ⟨8849123, by rfl⟩ : syracuseStep 11798831 = 17698247) B17698247
theorem B31463549 : Blo 2181435 31463549 := bstep (se 3 (by rfl) ⟨5899415, by rfl⟩ : syracuseStep 31463549 = 11798831) B11798831
theorem B20975699 : Blo 2181435 20975699 := bstep (se 1 (by rfl) ⟨15731774, by rfl⟩ : syracuseStep 20975699 = 31463549) B31463549
theorem B13983799 : Blo 2181435 13983799 := bstep (se 1 (by rfl) ⟨10487849, by rfl⟩ : syracuseStep 13983799 = 20975699) B20975699
theorem B18645065 : Blo 2181435 18645065 := bstep (se 2 (by rfl) ⟨6991899, by rfl⟩ : syracuseStep 18645065 = 13983799) B13983799
theorem B12430043 : Blo 2181435 12430043 := bstep (se 1 (by rfl) ⟨9322532, by rfl⟩ : syracuseStep 12430043 = 18645065) B18645065
theorem B8286695 : Blo 2181435 8286695 := bstep (se 1 (by rfl) ⟨6215021, by rfl⟩ : syracuseStep 8286695 = 12430043) B12430043
theorem B5524463 : Blo 2181435 5524463 := bstep (se 1 (by rfl) ⟨4143347, by rfl⟩ : syracuseStep 5524463 = 8286695) B8286695
theorem B3682975 : Blo 2181435 3682975 := bstep (se 1 (by rfl) ⟨2762231, by rfl⟩ : syracuseStep 3682975 = 5524463) B5524463
theorem B4910633 : Blo 2181435 4910633 := bstep (se 2 (by rfl) ⟨1841487, by rfl⟩ : syracuseStep 4910633 = 3682975) B3682975
theorem B3273755 : Blo 2181435 3273755 := bstep (se 1 (by rfl) ⟨2455316, by rfl⟩ : syracuseStep 3273755 = 4910633) B4910633
theorem B2182503 : Blo 2181435 2182503 := bstep (se 1 (by rfl) ⟨1636877, by rfl⟩ : syracuseStep 2182503 = 3273755) B3273755
theorem B2455321 : Blo 2181435 2455321 := bbase (se 2 (by rfl) ⟨920745, by rfl⟩ : syracuseStep 2455321 = 1841491) (by norm_num)
theorem B3273761 : Blo 2181435 3273761 := bstep (se 2 (by rfl) ⟨1227660, by rfl⟩ : syracuseStep 3273761 = 2455321) B2455321
theorem B2182507 : Blo 2181435 2182507 := bstep (se 1 (by rfl) ⟨1636880, by rfl⟩ : syracuseStep 2182507 = 3273761) B3273761
theorem B8286725 : Blo 2181435 8286725 := bbase (se 4 (by rfl) ⟨776880, by rfl⟩ : syracuseStep 8286725 = 1553761) (by norm_num)
theorem B5524483 : Blo 2181435 5524483 := bstep (se 1 (by rfl) ⟨4143362, by rfl⟩ : syracuseStep 5524483 = 8286725) B8286725
theorem B7365977 : Blo 2181435 7365977 := bstep (se 2 (by rfl) ⟨2762241, by rfl⟩ : syracuseStep 7365977 = 5524483) B5524483
theorem B4910651 : Blo 2181435 4910651 := bstep (se 1 (by rfl) ⟨3682988, by rfl⟩ : syracuseStep 4910651 = 7365977) B7365977
theorem B3273767 : Blo 2181435 3273767 := bstep (se 1 (by rfl) ⟨2455325, by rfl⟩ : syracuseStep 3273767 = 4910651) B4910651
theorem B2182511 : Blo 2181435 2182511 := bstep (se 1 (by rfl) ⟨1636883, by rfl⟩ : syracuseStep 2182511 = 3273767) B3273767
theorem B3273773 : Blo 2181435 3273773 := bbase (se 3 (by rfl) ⟨613832, by rfl⟩ : syracuseStep 3273773 = 1227665) (by norm_num)
theorem B2182515 : Blo 2181435 2182515 := bstep (se 1 (by rfl) ⟨1636886, by rfl⟩ : syracuseStep 2182515 = 3273773) B3273773
theorem B4910669 : Blo 2181435 4910669 := bbase (se 3 (by rfl) ⟨920750, by rfl⟩ : syracuseStep 4910669 = 1841501) (by norm_num)
theorem B3273779 : Blo 2181435 3273779 := bstep (se 1 (by rfl) ⟨2455334, by rfl⟩ : syracuseStep 3273779 = 4910669) B4910669
theorem B2182519 : Blo 2181435 2182519 := bstep (se 1 (by rfl) ⟨1636889, by rfl⟩ : syracuseStep 2182519 = 3273779) B3273779
theorem B2762257 : Blo 2181435 2762257 := bbase (se 2 (by rfl) ⟨1035846, by rfl⟩ : syracuseStep 2762257 = 2071693) (by norm_num)
theorem B3683009 : Blo 2181435 3683009 := bstep (se 2 (by rfl) ⟨1381128, by rfl⟩ : syracuseStep 3683009 = 2762257) B2762257
theorem B2455339 : Blo 2181435 2455339 := bstep (se 1 (by rfl) ⟨1841504, by rfl⟩ : syracuseStep 2455339 = 3683009) B3683009
theorem B3273785 : Blo 2181435 3273785 := bstep (se 2 (by rfl) ⟨1227669, by rfl⟩ : syracuseStep 3273785 = 2455339) B2455339
theorem B2182523 : Blo 2181435 2182523 := bstep (se 1 (by rfl) ⟨1636892, by rfl⟩ : syracuseStep 2182523 = 3273785) B3273785
theorem B4661317 : Blo 2181435 4661317 := bbase (se 4 (by rfl) ⟨436998, by rfl⟩ : syracuseStep 4661317 = 873997) (by norm_num)
theorem B24860357 : Blo 2181435 24860357 := bstep (se 4 (by rfl) ⟨2330658, by rfl⟩ : syracuseStep 24860357 = 4661317) B4661317
theorem B16573571 : Blo 2181435 16573571 := bstep (se 1 (by rfl) ⟨12430178, by rfl⟩ : syracuseStep 16573571 = 24860357) B24860357
theorem B11049047 : Blo 2181435 11049047 := bstep (se 1 (by rfl) ⟨8286785, by rfl⟩ : syracuseStep 11049047 = 16573571) B16573571
theorem B7366031 : Blo 2181435 7366031 := bstep (se 1 (by rfl) ⟨5524523, by rfl⟩ : syracuseStep 7366031 = 11049047) B11049047
theorem B4910687 : Blo 2181435 4910687 := bstep (se 1 (by rfl) ⟨3683015, by rfl⟩ : syracuseStep 4910687 = 7366031) B7366031
theorem B3273791 : Blo 2181435 3273791 := bstep (se 1 (by rfl) ⟨2455343, by rfl⟩ : syracuseStep 3273791 = 4910687) B4910687
theorem B2182527 : Blo 2181435 2182527 := bstep (se 1 (by rfl) ⟨1636895, by rfl⟩ : syracuseStep 2182527 = 3273791) B3273791
theorem B3273797 : Blo 2181435 3273797 := bbase (se 4 (by rfl) ⟨306918, by rfl⟩ : syracuseStep 3273797 = 613837) (by norm_num)
theorem B2182531 : Blo 2181435 2182531 := bstep (se 1 (by rfl) ⟨1636898, by rfl⟩ : syracuseStep 2182531 = 3273797) B3273797
theorem B3683029 : Blo 2181435 3683029 := bbase (se 7 (by rfl) ⟨43160, by rfl⟩ : syracuseStep 3683029 = 86321) (by norm_num)
theorem B4910705 : Blo 2181435 4910705 := bstep (se 2 (by rfl) ⟨1841514, by rfl⟩ : syracuseStep 4910705 = 3683029) B3683029
theorem B3273803 : Blo 2181435 3273803 := bstep (se 1 (by rfl) ⟨2455352, by rfl⟩ : syracuseStep 3273803 = 4910705) B4910705
theorem B2182535 : Blo 2181435 2182535 := bstep (se 1 (by rfl) ⟨1636901, by rfl⟩ : syracuseStep 2182535 = 3273803) B3273803
theorem B2455357 : Blo 2181435 2455357 := bbase (se 3 (by rfl) ⟨460379, by rfl⟩ : syracuseStep 2455357 = 920759) (by norm_num)
theorem B3273809 : Blo 2181435 3273809 := bstep (se 2 (by rfl) ⟨1227678, by rfl⟩ : syracuseStep 3273809 = 2455357) B2455357
theorem B2182539 : Blo 2181435 2182539 := bstep (se 1 (by rfl) ⟨1636904, by rfl⟩ : syracuseStep 2182539 = 3273809) B3273809
theorem B7366085 : Blo 2181435 7366085 := bbase (se 4 (by rfl) ⟨690570, by rfl⟩ : syracuseStep 7366085 = 1381141) (by norm_num)
theorem B4910723 : Blo 2181435 4910723 := bstep (se 1 (by rfl) ⟨3683042, by rfl⟩ : syracuseStep 4910723 = 7366085) B7366085
theorem B3273815 : Blo 2181435 3273815 := bstep (se 1 (by rfl) ⟨2455361, by rfl⟩ : syracuseStep 3273815 = 4910723) B4910723
theorem B2182543 : Blo 2181435 2182543 := bstep (se 1 (by rfl) ⟨1636907, by rfl⟩ : syracuseStep 2182543 = 3273815) B3273815
theorem B3273821 : Blo 2181435 3273821 := bbase (se 3 (by rfl) ⟨613841, by rfl⟩ : syracuseStep 3273821 = 1227683) (by norm_num)
theorem B2182547 : Blo 2181435 2182547 := bstep (se 1 (by rfl) ⟨1636910, by rfl⟩ : syracuseStep 2182547 = 3273821) B3273821
theorem B4910741 : Blo 2181435 4910741 := bbase (se 6 (by rfl) ⟨115095, by rfl⟩ : syracuseStep 4910741 = 230191) (by norm_num)
theorem B3273827 : Blo 2181435 3273827 := bstep (se 1 (by rfl) ⟨2455370, by rfl⟩ : syracuseStep 3273827 = 4910741) B4910741
theorem B2182551 : Blo 2181435 2182551 := bstep (se 1 (by rfl) ⟨1636913, by rfl⟩ : syracuseStep 2182551 = 3273827) B3273827
theorem B2330689 : Blo 2181435 2330689 := bbase (se 2 (by rfl) ⟨874008, by rfl⟩ : syracuseStep 2330689 = 1748017) (by norm_num)
theorem B3107585 : Blo 2181435 3107585 := bstep (se 2 (by rfl) ⟨1165344, by rfl⟩ : syracuseStep 3107585 = 2330689) B2330689
theorem B8286893 : Blo 2181435 8286893 := bstep (se 3 (by rfl) ⟨1553792, by rfl⟩ : syracuseStep 8286893 = 3107585) B3107585
theorem B5524595 : Blo 2181435 5524595 := bstep (se 1 (by rfl) ⟨4143446, by rfl⟩ : syracuseStep 5524595 = 8286893) B8286893
theorem B3683063 : Blo 2181435 3683063 := bstep (se 1 (by rfl) ⟨2762297, by rfl⟩ : syracuseStep 3683063 = 5524595) B5524595
theorem B2455375 : Blo 2181435 2455375 := bstep (se 1 (by rfl) ⟨1841531, by rfl⟩ : syracuseStep 2455375 = 3683063) B3683063
theorem B3273833 : Blo 2181435 3273833 := bstep (se 2 (by rfl) ⟨1227687, by rfl⟩ : syracuseStep 3273833 = 2455375) B2455375
theorem B2182555 : Blo 2181435 2182555 := bstep (se 1 (by rfl) ⟨1636916, by rfl⟩ : syracuseStep 2182555 = 3273833) B3273833
theorem B12599957 : Blo 2181435 12599957 := bbase (se 6 (by rfl) ⟨295311, by rfl⟩ : syracuseStep 12599957 = 590623) (by norm_num)
theorem B8399971 : Blo 2181435 8399971 := bstep (se 1 (by rfl) ⟨6299978, by rfl⟩ : syracuseStep 8399971 = 12599957) B12599957
theorem B11199961 : Blo 2181435 11199961 := bstep (se 2 (by rfl) ⟨4199985, by rfl⟩ : syracuseStep 11199961 = 8399971) B8399971
theorem B14933281 : Blo 2181435 14933281 := bstep (se 2 (by rfl) ⟨5599980, by rfl⟩ : syracuseStep 14933281 = 11199961) B11199961
theorem B19911041 : Blo 2181435 19911041 := bstep (se 2 (by rfl) ⟨7466640, by rfl⟩ : syracuseStep 19911041 = 14933281) B14933281
theorem B13274027 : Blo 2181435 13274027 := bstep (se 1 (by rfl) ⟨9955520, by rfl⟩ : syracuseStep 13274027 = 19911041) B19911041
theorem B8849351 : Blo 2181435 8849351 := bstep (se 1 (by rfl) ⟨6637013, by rfl⟩ : syracuseStep 8849351 = 13274027) B13274027
theorem B5899567 : Blo 2181435 5899567 := bstep (se 1 (by rfl) ⟨4424675, by rfl⟩ : syracuseStep 5899567 = 8849351) B8849351
theorem B7866089 : Blo 2181435 7866089 := bstep (se 2 (by rfl) ⟨2949783, by rfl⟩ : syracuseStep 7866089 = 5899567) B5899567
theorem B5244059 : Blo 2181435 5244059 := bstep (se 1 (by rfl) ⟨3933044, by rfl⟩ : syracuseStep 5244059 = 7866089) B7866089
theorem B13984157 : Blo 2181435 13984157 := bstep (se 3 (by rfl) ⟨2622029, by rfl⟩ : syracuseStep 13984157 = 5244059) B5244059
theorem B9322771 : Blo 2181435 9322771 := bstep (se 1 (by rfl) ⟨6992078, by rfl⟩ : syracuseStep 9322771 = 13984157) B13984157
theorem B12430361 : Blo 2181435 12430361 := bstep (se 2 (by rfl) ⟨4661385, by rfl⟩ : syracuseStep 12430361 = 9322771) B9322771
theorem B8286907 : Blo 2181435 8286907 := bstep (se 1 (by rfl) ⟨6215180, by rfl⟩ : syracuseStep 8286907 = 12430361) B12430361
theorem B11049209 : Blo 2181435 11049209 := bstep (se 2 (by rfl) ⟨4143453, by rfl⟩ : syracuseStep 11049209 = 8286907) B8286907
theorem B7366139 : Blo 2181435 7366139 := bstep (se 1 (by rfl) ⟨5524604, by rfl⟩ : syracuseStep 7366139 = 11049209) B11049209
theorem B4910759 : Blo 2181435 4910759 := bstep (se 1 (by rfl) ⟨3683069, by rfl⟩ : syracuseStep 4910759 = 7366139) B7366139
theorem B3273839 : Blo 2181435 3273839 := bstep (se 1 (by rfl) ⟨2455379, by rfl⟩ : syracuseStep 3273839 = 4910759) B4910759
theorem B2182559 : Blo 2181435 2182559 := bstep (se 1 (by rfl) ⟨1636919, by rfl⟩ : syracuseStep 2182559 = 3273839) B3273839
theorem B3273845 : Blo 2181435 3273845 := bbase (se 5 (by rfl) ⟨153461, by rfl⟩ : syracuseStep 3273845 = 306923) (by norm_num)
theorem B2182563 : Blo 2181435 2182563 := bstep (se 1 (by rfl) ⟨1636922, by rfl⟩ : syracuseStep 2182563 = 3273845) B3273845
theorem B4143469 : Blo 2181435 4143469 := bbase (se 3 (by rfl) ⟨776900, by rfl⟩ : syracuseStep 4143469 = 1553801) (by norm_num)
theorem B5524625 : Blo 2181435 5524625 := bstep (se 2 (by rfl) ⟨2071734, by rfl⟩ : syracuseStep 5524625 = 4143469) B4143469
theorem B3683083 : Blo 2181435 3683083 := bstep (se 1 (by rfl) ⟨2762312, by rfl⟩ : syracuseStep 3683083 = 5524625) B5524625
theorem B4910777 : Blo 2181435 4910777 := bstep (se 2 (by rfl) ⟨1841541, by rfl⟩ : syracuseStep 4910777 = 3683083) B3683083
theorem B3273851 : Blo 2181435 3273851 := bstep (se 1 (by rfl) ⟨2455388, by rfl⟩ : syracuseStep 3273851 = 4910777) B4910777
theorem B2182567 : Blo 2181435 2182567 := bstep (se 1 (by rfl) ⟨1636925, by rfl⟩ : syracuseStep 2182567 = 3273851) B3273851
theorem B2455393 : Blo 2181435 2455393 := bbase (se 2 (by rfl) ⟨920772, by rfl⟩ : syracuseStep 2455393 = 1841545) (by norm_num)
theorem B3273857 : Blo 2181435 3273857 := bstep (se 2 (by rfl) ⟨1227696, by rfl⟩ : syracuseStep 3273857 = 2455393) B2455393
theorem B2182571 : Blo 2181435 2182571 := bstep (se 1 (by rfl) ⟨1636928, by rfl⟩ : syracuseStep 2182571 = 3273857) B3273857
theorem B5524645 : Blo 2181435 5524645 := bbase (se 4 (by rfl) ⟨517935, by rfl⟩ : syracuseStep 5524645 = 1035871) (by norm_num)
theorem B7366193 : Blo 2181435 7366193 := bstep (se 2 (by rfl) ⟨2762322, by rfl⟩ : syracuseStep 7366193 = 5524645) B5524645
theorem B4910795 : Blo 2181435 4910795 := bstep (se 1 (by rfl) ⟨3683096, by rfl⟩ : syracuseStep 4910795 = 7366193) B7366193
theorem B3273863 : Blo 2181435 3273863 := bstep (se 1 (by rfl) ⟨2455397, by rfl⟩ : syracuseStep 3273863 = 4910795) B4910795
theorem B2182575 : Blo 2181435 2182575 := bstep (se 1 (by rfl) ⟨1636931, by rfl⟩ : syracuseStep 2182575 = 3273863) B3273863
theorem B3273869 : Blo 2181435 3273869 := bbase (se 3 (by rfl) ⟨613850, by rfl⟩ : syracuseStep 3273869 = 1227701) (by norm_num)
theorem B2182579 : Blo 2181435 2182579 := bstep (se 1 (by rfl) ⟨1636934, by rfl⟩ : syracuseStep 2182579 = 3273869) B3273869
theorem B4910813 : Blo 2181435 4910813 := bbase (se 3 (by rfl) ⟨920777, by rfl⟩ : syracuseStep 4910813 = 1841555) (by norm_num)
theorem B3273875 : Blo 2181435 3273875 := bstep (se 1 (by rfl) ⟨2455406, by rfl⟩ : syracuseStep 3273875 = 4910813) B4910813
theorem B2182583 : Blo 2181435 2182583 := bstep (se 1 (by rfl) ⟨1636937, by rfl⟩ : syracuseStep 2182583 = 3273875) B3273875
theorem B3683117 : Blo 2181435 3683117 := bbase (se 3 (by rfl) ⟨690584, by rfl⟩ : syracuseStep 3683117 = 1381169) (by norm_num)
theorem B2455411 : Blo 2181435 2455411 := bstep (se 1 (by rfl) ⟨1841558, by rfl⟩ : syracuseStep 2455411 = 3683117) B3683117
theorem B3273881 : Blo 2181435 3273881 := bstep (se 2 (by rfl) ⟨1227705, by rfl⟩ : syracuseStep 3273881 = 2455411) B2455411
theorem B2182587 : Blo 2181435 2182587 := bstep (se 1 (by rfl) ⟨1636940, by rfl⟩ : syracuseStep 2182587 = 3273881) B3273881
theorem B14175157 : Blo 2181435 14175157 := bbase (se 5 (by rfl) ⟨664460, by rfl⟩ : syracuseStep 14175157 = 1328921) (by norm_num)
theorem B18900209 : Blo 2181435 18900209 := bstep (se 2 (by rfl) ⟨7087578, by rfl⟩ : syracuseStep 18900209 = 14175157) B14175157
theorem B12600139 : Blo 2181435 12600139 := bstep (se 1 (by rfl) ⟨9450104, by rfl⟩ : syracuseStep 12600139 = 18900209) B18900209
theorem B16800185 : Blo 2181435 16800185 := bstep (se 2 (by rfl) ⟨6300069, by rfl⟩ : syracuseStep 16800185 = 12600139) B12600139
theorem B11200123 : Blo 2181435 11200123 := bstep (se 1 (by rfl) ⟨8400092, by rfl⟩ : syracuseStep 11200123 = 16800185) B16800185
theorem B14933497 : Blo 2181435 14933497 := bstep (se 2 (by rfl) ⟨5600061, by rfl⟩ : syracuseStep 14933497 = 11200123) B11200123
theorem B19911329 : Blo 2181435 19911329 := bstep (se 2 (by rfl) ⟨7466748, by rfl⟩ : syracuseStep 19911329 = 14933497) B14933497
theorem B13274219 : Blo 2181435 13274219 := bstep (se 1 (by rfl) ⟨9955664, by rfl⟩ : syracuseStep 13274219 = 19911329) B19911329
theorem B35397917 : Blo 2181435 35397917 := bstep (se 3 (by rfl) ⟨6637109, by rfl⟩ : syracuseStep 35397917 = 13274219) B13274219
theorem B23598611 : Blo 2181435 23598611 := bstep (se 1 (by rfl) ⟨17698958, by rfl⟩ : syracuseStep 23598611 = 35397917) B35397917
theorem B15732407 : Blo 2181435 15732407 := bstep (se 1 (by rfl) ⟨11799305, by rfl⟩ : syracuseStep 15732407 = 23598611) B23598611
theorem B41953085 : Blo 2181435 41953085 := bstep (se 3 (by rfl) ⟨7866203, by rfl⟩ : syracuseStep 41953085 = 15732407) B15732407
theorem B27968723 : Blo 2181435 27968723 := bstep (se 1 (by rfl) ⟨20976542, by rfl⟩ : syracuseStep 27968723 = 41953085) B41953085
theorem B18645815 : Blo 2181435 18645815 := bstep (se 1 (by rfl) ⟨13984361, by rfl⟩ : syracuseStep 18645815 = 27968723) B27968723
theorem B12430543 : Blo 2181435 12430543 := bstep (se 1 (by rfl) ⟨9322907, by rfl⟩ : syracuseStep 12430543 = 18645815) B18645815
theorem B16574057 : Blo 2181435 16574057 := bstep (se 2 (by rfl) ⟨6215271, by rfl⟩ : syracuseStep 16574057 = 12430543) B12430543
theorem B11049371 : Blo 2181435 11049371 := bstep (se 1 (by rfl) ⟨8287028, by rfl⟩ : syracuseStep 11049371 = 16574057) B16574057
theorem B7366247 : Blo 2181435 7366247 := bstep (se 1 (by rfl) ⟨5524685, by rfl⟩ : syracuseStep 7366247 = 11049371) B11049371
theorem B4910831 : Blo 2181435 4910831 := bstep (se 1 (by rfl) ⟨3683123, by rfl⟩ : syracuseStep 4910831 = 7366247) B7366247
theorem B3273887 : Blo 2181435 3273887 := bstep (se 1 (by rfl) ⟨2455415, by rfl⟩ : syracuseStep 3273887 = 4910831) B4910831
theorem B2182591 : Blo 2181435 2182591 := bstep (se 1 (by rfl) ⟨1636943, by rfl⟩ : syracuseStep 2182591 = 3273887) B3273887
theorem B3273893 : Blo 2181435 3273893 := bbase (se 4 (by rfl) ⟨306927, by rfl⟩ : syracuseStep 3273893 = 613855) (by norm_num)
theorem B2182595 : Blo 2181435 2182595 := bstep (se 1 (by rfl) ⟨1636946, by rfl⟩ : syracuseStep 2182595 = 3273893) B3273893
theorem B2762353 : Blo 2181435 2762353 := bbase (se 2 (by rfl) ⟨1035882, by rfl⟩ : syracuseStep 2762353 = 2071765) (by norm_num)
theorem B3683137 : Blo 2181435 3683137 := bstep (se 2 (by rfl) ⟨1381176, by rfl⟩ : syracuseStep 3683137 = 2762353) B2762353
theorem B4910849 : Blo 2181435 4910849 := bstep (se 2 (by rfl) ⟨1841568, by rfl⟩ : syracuseStep 4910849 = 3683137) B3683137
theorem B3273899 : Blo 2181435 3273899 := bstep (se 1 (by rfl) ⟨2455424, by rfl⟩ : syracuseStep 3273899 = 4910849) B4910849
theorem B2182599 : Blo 2181435 2182599 := bstep (se 1 (by rfl) ⟨1636949, by rfl⟩ : syracuseStep 2182599 = 3273899) B3273899
theorem B2455429 : Blo 2181435 2455429 := bbase (se 4 (by rfl) ⟨230196, by rfl⟩ : syracuseStep 2455429 = 460393) (by norm_num)
theorem B3273905 : Blo 2181435 3273905 := bstep (se 2 (by rfl) ⟨1227714, by rfl⟩ : syracuseStep 3273905 = 2455429) B2455429
theorem B2182603 : Blo 2181435 2182603 := bstep (se 1 (by rfl) ⟨1636952, by rfl⟩ : syracuseStep 2182603 = 3273905) B3273905
theorem B3496117 : Blo 2181435 3496117 := bbase (se 5 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 3496117 = 327761) (by norm_num)
theorem B4661489 : Blo 2181435 4661489 := bstep (se 2 (by rfl) ⟨1748058, by rfl⟩ : syracuseStep 4661489 = 3496117) B3496117
theorem B3107659 : Blo 2181435 3107659 := bstep (se 1 (by rfl) ⟨2330744, by rfl⟩ : syracuseStep 3107659 = 4661489) B4661489
theorem B4143545 : Blo 2181435 4143545 := bstep (se 2 (by rfl) ⟨1553829, by rfl⟩ : syracuseStep 4143545 = 3107659) B3107659
theorem B2762363 : Blo 2181435 2762363 := bstep (se 1 (by rfl) ⟨2071772, by rfl⟩ : syracuseStep 2762363 = 4143545) B4143545
theorem B7366301 : Blo 2181435 7366301 := bstep (se 3 (by rfl) ⟨1381181, by rfl⟩ : syracuseStep 7366301 = 2762363) B2762363
theorem B4910867 : Blo 2181435 4910867 := bstep (se 1 (by rfl) ⟨3683150, by rfl⟩ : syracuseStep 4910867 = 7366301) B7366301
theorem B3273911 : Blo 2181435 3273911 := bstep (se 1 (by rfl) ⟨2455433, by rfl⟩ : syracuseStep 3273911 = 4910867) B4910867
theorem B2182607 : Blo 2181435 2182607 := bstep (se 1 (by rfl) ⟨1636955, by rfl⟩ : syracuseStep 2182607 = 3273911) B3273911
theorem B3273917 : Blo 2181435 3273917 := bbase (se 3 (by rfl) ⟨613859, by rfl⟩ : syracuseStep 3273917 = 1227719) (by norm_num)
theorem B2182611 : Blo 2181435 2182611 := bstep (se 1 (by rfl) ⟨1636958, by rfl⟩ : syracuseStep 2182611 = 3273917) B3273917
theorem B4910885 : Blo 2181435 4910885 := bbase (se 4 (by rfl) ⟨460395, by rfl⟩ : syracuseStep 4910885 = 920791) (by norm_num)
theorem B3273923 : Blo 2181435 3273923 := bstep (se 1 (by rfl) ⟨2455442, by rfl⟩ : syracuseStep 3273923 = 4910885) B4910885
theorem B2182615 : Blo 2181435 2182615 := bstep (se 1 (by rfl) ⟨1636961, by rfl⟩ : syracuseStep 2182615 = 3273923) B3273923
theorem B5524757 : Blo 2181435 5524757 := bbase (se 6 (by rfl) ⟨129486, by rfl⟩ : syracuseStep 5524757 = 258973) (by norm_num)
theorem B3683171 : Blo 2181435 3683171 := bstep (se 1 (by rfl) ⟨2762378, by rfl⟩ : syracuseStep 3683171 = 5524757) B5524757
theorem B2455447 : Blo 2181435 2455447 := bstep (se 1 (by rfl) ⟨1841585, by rfl⟩ : syracuseStep 2455447 = 3683171) B3683171
theorem B3273929 : Blo 2181435 3273929 := bstep (se 2 (by rfl) ⟨1227723, by rfl⟩ : syracuseStep 3273929 = 2455447) B2455447
theorem B2182619 : Blo 2181435 2182619 := bstep (se 1 (by rfl) ⟨1636964, by rfl⟩ : syracuseStep 2182619 = 3273929) B3273929
theorem B9323045 : Blo 2181435 9323045 := bbase (se 4 (by rfl) ⟨874035, by rfl⟩ : syracuseStep 9323045 = 1748071) (by norm_num)
theorem B6215363 : Blo 2181435 6215363 := bstep (se 1 (by rfl) ⟨4661522, by rfl⟩ : syracuseStep 6215363 = 9323045) B9323045
theorem B4143575 : Blo 2181435 4143575 := bstep (se 1 (by rfl) ⟨3107681, by rfl⟩ : syracuseStep 4143575 = 6215363) B6215363
theorem B11049533 : Blo 2181435 11049533 := bstep (se 3 (by rfl) ⟨2071787, by rfl⟩ : syracuseStep 11049533 = 4143575) B4143575
theorem B7366355 : Blo 2181435 7366355 := bstep (se 1 (by rfl) ⟨5524766, by rfl⟩ : syracuseStep 7366355 = 11049533) B11049533
theorem B4910903 : Blo 2181435 4910903 := bstep (se 1 (by rfl) ⟨3683177, by rfl⟩ : syracuseStep 4910903 = 7366355) B7366355
theorem B3273935 : Blo 2181435 3273935 := bstep (se 1 (by rfl) ⟨2455451, by rfl⟩ : syracuseStep 3273935 = 4910903) B4910903
theorem B2182623 : Blo 2181435 2182623 := bstep (se 1 (by rfl) ⟨1636967, by rfl⟩ : syracuseStep 2182623 = 3273935) B3273935
theorem B3273941 : Blo 2181435 3273941 := bbase (se 7 (by rfl) ⟨38366, by rfl⟩ : syracuseStep 3273941 = 76733) (by norm_num)
theorem B2182627 : Blo 2181435 2182627 := bstep (se 1 (by rfl) ⟨1636970, by rfl⟩ : syracuseStep 2182627 = 3273941) B3273941
theorem B3107693 : Blo 2181435 3107693 := bbase (se 3 (by rfl) ⟨582692, by rfl⟩ : syracuseStep 3107693 = 1165385) (by norm_num)
theorem B8287181 : Blo 2181435 8287181 := bstep (se 3 (by rfl) ⟨1553846, by rfl⟩ : syracuseStep 8287181 = 3107693) B3107693
theorem B5524787 : Blo 2181435 5524787 := bstep (se 1 (by rfl) ⟨4143590, by rfl⟩ : syracuseStep 5524787 = 8287181) B8287181
theorem B3683191 : Blo 2181435 3683191 := bstep (se 1 (by rfl) ⟨2762393, by rfl⟩ : syracuseStep 3683191 = 5524787) B5524787
theorem B4910921 : Blo 2181435 4910921 := bstep (se 2 (by rfl) ⟨1841595, by rfl⟩ : syracuseStep 4910921 = 3683191) B3683191
theorem B3273947 : Blo 2181435 3273947 := bstep (se 1 (by rfl) ⟨2455460, by rfl⟩ : syracuseStep 3273947 = 4910921) B4910921
theorem B2182631 : Blo 2181435 2182631 := bstep (se 1 (by rfl) ⟨1636973, by rfl⟩ : syracuseStep 2182631 = 3273947) B3273947
theorem B2455465 : Blo 2181435 2455465 := bbase (se 2 (by rfl) ⟨920799, by rfl⟩ : syracuseStep 2455465 = 1841599) (by norm_num)
theorem B3273953 : Blo 2181435 3273953 := bstep (se 2 (by rfl) ⟨1227732, by rfl⟩ : syracuseStep 3273953 = 2455465) B2455465
theorem B2182635 : Blo 2181435 2182635 := bstep (se 1 (by rfl) ⟨1636976, by rfl⟩ : syracuseStep 2182635 = 3273953) B3273953
theorem B2800093 : Blo 2181435 2800093 := bbase (se 3 (by rfl) ⟨525017, by rfl⟩ : syracuseStep 2800093 = 1050035) (by norm_num)
theorem B3733457 : Blo 2181435 3733457 := bstep (se 2 (by rfl) ⟨1400046, by rfl⟩ : syracuseStep 3733457 = 2800093) B2800093
theorem B9955885 : Blo 2181435 9955885 := bstep (se 3 (by rfl) ⟨1866728, by rfl⟩ : syracuseStep 9955885 = 3733457) B3733457
theorem B13274513 : Blo 2181435 13274513 := bstep (se 2 (by rfl) ⟨4977942, by rfl⟩ : syracuseStep 13274513 = 9955885) B9955885
theorem B8849675 : Blo 2181435 8849675 := bstep (se 1 (by rfl) ⟨6637256, by rfl⟩ : syracuseStep 8849675 = 13274513) B13274513
theorem B23599133 : Blo 2181435 23599133 := bstep (se 3 (by rfl) ⟨4424837, by rfl⟩ : syracuseStep 23599133 = 8849675) B8849675
theorem B15732755 : Blo 2181435 15732755 := bstep (se 1 (by rfl) ⟨11799566, by rfl⟩ : syracuseStep 15732755 = 23599133) B23599133
theorem B10488503 : Blo 2181435 10488503 := bstep (se 1 (by rfl) ⟨7866377, by rfl⟩ : syracuseStep 10488503 = 15732755) B15732755
theorem B6992335 : Blo 2181435 6992335 := bstep (se 1 (by rfl) ⟨5244251, by rfl⟩ : syracuseStep 6992335 = 10488503) B10488503
theorem B9323113 : Blo 2181435 9323113 := bstep (se 2 (by rfl) ⟨3496167, by rfl⟩ : syracuseStep 9323113 = 6992335) B6992335
theorem B12430817 : Blo 2181435 12430817 := bstep (se 2 (by rfl) ⟨4661556, by rfl⟩ : syracuseStep 12430817 = 9323113) B9323113
theorem B8287211 : Blo 2181435 8287211 := bstep (se 1 (by rfl) ⟨6215408, by rfl⟩ : syracuseStep 8287211 = 12430817) B12430817
theorem B5524807 : Blo 2181435 5524807 := bstep (se 1 (by rfl) ⟨4143605, by rfl⟩ : syracuseStep 5524807 = 8287211) B8287211
theorem B7366409 : Blo 2181435 7366409 := bstep (se 2 (by rfl) ⟨2762403, by rfl⟩ : syracuseStep 7366409 = 5524807) B5524807
theorem B4910939 : Blo 2181435 4910939 := bstep (se 1 (by rfl) ⟨3683204, by rfl⟩ : syracuseStep 4910939 = 7366409) B7366409
theorem B3273959 : Blo 2181435 3273959 := bstep (se 1 (by rfl) ⟨2455469, by rfl⟩ : syracuseStep 3273959 = 4910939) B4910939
theorem B2182639 : Blo 2181435 2182639 := bstep (se 1 (by rfl) ⟨1636979, by rfl⟩ : syracuseStep 2182639 = 3273959) B3273959
theorem B3273965 : Blo 2181435 3273965 := bbase (se 3 (by rfl) ⟨613868, by rfl⟩ : syracuseStep 3273965 = 1227737) (by norm_num)
theorem B2182643 : Blo 2181435 2182643 := bstep (se 1 (by rfl) ⟨1636982, by rfl⟩ : syracuseStep 2182643 = 3273965) B3273965
theorem B4910957 : Blo 2181435 4910957 := bbase (se 3 (by rfl) ⟨920804, by rfl⟩ : syracuseStep 4910957 = 1841609) (by norm_num)
theorem B3273971 : Blo 2181435 3273971 := bstep (se 1 (by rfl) ⟨2455478, by rfl⟩ : syracuseStep 3273971 = 4910957) B4910957
theorem B2182647 : Blo 2181435 2182647 := bstep (se 1 (by rfl) ⟨1636985, by rfl⟩ : syracuseStep 2182647 = 3273971) B3273971
theorem B4143629 : Blo 2181435 4143629 := bbase (se 3 (by rfl) ⟨776930, by rfl⟩ : syracuseStep 4143629 = 1553861) (by norm_num)
theorem B2762419 : Blo 2181435 2762419 := bstep (se 1 (by rfl) ⟨2071814, by rfl⟩ : syracuseStep 2762419 = 4143629) B4143629
theorem B3683225 : Blo 2181435 3683225 := bstep (se 2 (by rfl) ⟨1381209, by rfl⟩ : syracuseStep 3683225 = 2762419) B2762419
theorem B2455483 : Blo 2181435 2455483 := bstep (se 1 (by rfl) ⟨1841612, by rfl⟩ : syracuseStep 2455483 = 3683225) B3683225
theorem B3273977 : Blo 2181435 3273977 := bstep (se 2 (by rfl) ⟨1227741, by rfl⟩ : syracuseStep 3273977 = 2455483) B2455483
theorem B2182651 : Blo 2181435 2182651 := bstep (se 1 (by rfl) ⟨1636988, by rfl⟩ : syracuseStep 2182651 = 3273977) B3273977
theorem B3318653 : Blo 2181435 3318653 := bbase (se 3 (by rfl) ⟨622247, by rfl⟩ : syracuseStep 3318653 = 1244495) (by norm_num)
theorem B2212435 : Blo 2181435 2212435 := bstep (se 1 (by rfl) ⟨1659326, by rfl⟩ : syracuseStep 2212435 = 3318653) B3318653
theorem B2949913 : Blo 2181435 2949913 := bstep (se 2 (by rfl) ⟨1106217, by rfl⟩ : syracuseStep 2949913 = 2212435) B2212435
theorem B3933217 : Blo 2181435 3933217 := bstep (se 2 (by rfl) ⟨1474956, by rfl⟩ : syracuseStep 3933217 = 2949913) B2949913
theorem B20977157 : Blo 2181435 20977157 := bstep (se 4 (by rfl) ⟨1966608, by rfl⟩ : syracuseStep 20977157 = 3933217) B3933217
theorem B55939085 : Blo 2181435 55939085 := bstep (se 3 (by rfl) ⟨10488578, by rfl⟩ : syracuseStep 55939085 = 20977157) B20977157
theorem B37292723 : Blo 2181435 37292723 := bstep (se 1 (by rfl) ⟨27969542, by rfl⟩ : syracuseStep 37292723 = 55939085) B55939085
theorem B24861815 : Blo 2181435 24861815 := bstep (se 1 (by rfl) ⟨18646361, by rfl⟩ : syracuseStep 24861815 = 37292723) B37292723
theorem B16574543 : Blo 2181435 16574543 := bstep (se 1 (by rfl) ⟨12430907, by rfl⟩ : syracuseStep 16574543 = 24861815) B24861815
theorem B11049695 : Blo 2181435 11049695 := bstep (se 1 (by rfl) ⟨8287271, by rfl⟩ : syracuseStep 11049695 = 16574543) B16574543
theorem B7366463 : Blo 2181435 7366463 := bstep (se 1 (by rfl) ⟨5524847, by rfl⟩ : syracuseStep 7366463 = 11049695) B11049695
theorem B4910975 : Blo 2181435 4910975 := bstep (se 1 (by rfl) ⟨3683231, by rfl⟩ : syracuseStep 4910975 = 7366463) B7366463
theorem B3273983 : Blo 2181435 3273983 := bstep (se 1 (by rfl) ⟨2455487, by rfl⟩ : syracuseStep 3273983 = 4910975) B4910975
theorem B2182655 : Blo 2181435 2182655 := bstep (se 1 (by rfl) ⟨1636991, by rfl⟩ : syracuseStep 2182655 = 3273983) B3273983
theorem B3273989 : Blo 2181435 3273989 := bbase (se 4 (by rfl) ⟨306936, by rfl⟩ : syracuseStep 3273989 = 613873) (by norm_num)
theorem B2182659 : Blo 2181435 2182659 := bstep (se 1 (by rfl) ⟨1636994, by rfl⟩ : syracuseStep 2182659 = 3273989) B3273989
theorem B3683245 : Blo 2181435 3683245 := bbase (se 3 (by rfl) ⟨690608, by rfl⟩ : syracuseStep 3683245 = 1381217) (by norm_num)
theorem B4910993 : Blo 2181435 4910993 := bstep (se 2 (by rfl) ⟨1841622, by rfl⟩ : syracuseStep 4910993 = 3683245) B3683245
theorem B3273995 : Blo 2181435 3273995 := bstep (se 1 (by rfl) ⟨2455496, by rfl⟩ : syracuseStep 3273995 = 4910993) B4910993
theorem B2182663 : Blo 2181435 2182663 := bstep (se 1 (by rfl) ⟨1636997, by rfl⟩ : syracuseStep 2182663 = 3273995) B3273995
theorem B2455501 : Blo 2181435 2455501 := bbase (se 3 (by rfl) ⟨460406, by rfl⟩ : syracuseStep 2455501 = 920813) (by norm_num)
theorem B3274001 : Blo 2181435 3274001 := bstep (se 2 (by rfl) ⟨1227750, by rfl⟩ : syracuseStep 3274001 = 2455501) B2455501
theorem B2182667 : Blo 2181435 2182667 := bstep (se 1 (by rfl) ⟨1637000, by rfl⟩ : syracuseStep 2182667 = 3274001) B3274001
theorem B7366517 : Blo 2181435 7366517 := bbase (se 5 (by rfl) ⟨345305, by rfl⟩ : syracuseStep 7366517 = 690611) (by norm_num)
theorem B4911011 : Blo 2181435 4911011 := bstep (se 1 (by rfl) ⟨3683258, by rfl⟩ : syracuseStep 4911011 = 7366517) B7366517
theorem B3274007 : Blo 2181435 3274007 := bstep (se 1 (by rfl) ⟨2455505, by rfl⟩ : syracuseStep 3274007 = 4911011) B4911011
theorem B2182671 : Blo 2181435 2182671 := bstep (se 1 (by rfl) ⟨1637003, by rfl⟩ : syracuseStep 2182671 = 3274007) B3274007
theorem B3274013 : Blo 2181435 3274013 := bbase (se 3 (by rfl) ⟨613877, by rfl⟩ : syracuseStep 3274013 = 1227755) (by norm_num)
theorem B2182675 : Blo 2181435 2182675 := bstep (se 1 (by rfl) ⟨1637006, by rfl⟩ : syracuseStep 2182675 = 3274013) B3274013
theorem B4911029 : Blo 2181435 4911029 := bbase (se 5 (by rfl) ⟨230204, by rfl⟩ : syracuseStep 4911029 = 460409) (by norm_num)
theorem B3274019 : Blo 2181435 3274019 := bstep (se 1 (by rfl) ⟨2455514, by rfl⟩ : syracuseStep 3274019 = 4911029) B4911029
theorem B2182679 : Blo 2181435 2182679 := bstep (se 1 (by rfl) ⟨1637009, by rfl⟩ : syracuseStep 2182679 = 3274019) B3274019
theorem B3933269 : Blo 2181435 3933269 := bbase (se 8 (by rfl) ⟨23046, by rfl⟩ : syracuseStep 3933269 = 46093) (by norm_num)
theorem B2622179 : Blo 2181435 2622179 := bstep (se 1 (by rfl) ⟨1966634, by rfl⟩ : syracuseStep 2622179 = 3933269) B3933269
theorem B6992477 : Blo 2181435 6992477 := bstep (se 3 (by rfl) ⟨1311089, by rfl⟩ : syracuseStep 6992477 = 2622179) B2622179
theorem B4661651 : Blo 2181435 4661651 := bstep (se 1 (by rfl) ⟨3496238, by rfl⟩ : syracuseStep 4661651 = 6992477) B6992477
theorem B12431069 : Blo 2181435 12431069 := bstep (se 3 (by rfl) ⟨2330825, by rfl⟩ : syracuseStep 12431069 = 4661651) B4661651
theorem B8287379 : Blo 2181435 8287379 := bstep (se 1 (by rfl) ⟨6215534, by rfl⟩ : syracuseStep 8287379 = 12431069) B12431069
theorem B5524919 : Blo 2181435 5524919 := bstep (se 1 (by rfl) ⟨4143689, by rfl⟩ : syracuseStep 5524919 = 8287379) B8287379
theorem B3683279 : Blo 2181435 3683279 := bstep (se 1 (by rfl) ⟨2762459, by rfl⟩ : syracuseStep 3683279 = 5524919) B5524919
theorem B2455519 : Blo 2181435 2455519 := bstep (se 1 (by rfl) ⟨1841639, by rfl⟩ : syracuseStep 2455519 = 3683279) B3683279
theorem B3274025 : Blo 2181435 3274025 := bstep (se 2 (by rfl) ⟨1227759, by rfl⟩ : syracuseStep 3274025 = 2455519) B2455519
theorem B2182683 : Blo 2181435 2182683 := bstep (se 1 (by rfl) ⟨1637012, by rfl⟩ : syracuseStep 2182683 = 3274025) B3274025
theorem B90827477 : Blo 2181435 90827477 := bbase (se 7 (by rfl) ⟨1064384, by rfl⟩ : syracuseStep 90827477 = 2128769) (by norm_num)
theorem B60551651 : Blo 2181435 60551651 := bstep (se 1 (by rfl) ⟨45413738, by rfl⟩ : syracuseStep 60551651 = 90827477) B90827477
theorem B40367767 : Blo 2181435 40367767 := bstep (se 1 (by rfl) ⟨30275825, by rfl⟩ : syracuseStep 40367767 = 60551651) B60551651
theorem B53823689 : Blo 2181435 53823689 := bstep (se 2 (by rfl) ⟨20183883, by rfl⟩ : syracuseStep 53823689 = 40367767) B40367767
theorem B35882459 : Blo 2181435 35882459 := bstep (se 1 (by rfl) ⟨26911844, by rfl⟩ : syracuseStep 35882459 = 53823689) B53823689
theorem B23921639 : Blo 2181435 23921639 := bstep (se 1 (by rfl) ⟨17941229, by rfl⟩ : syracuseStep 23921639 = 35882459) B35882459
theorem B15947759 : Blo 2181435 15947759 := bstep (se 1 (by rfl) ⟨11960819, by rfl⟩ : syracuseStep 15947759 = 23921639) B23921639
theorem B10631839 : Blo 2181435 10631839 := bstep (se 1 (by rfl) ⟨7973879, by rfl⟩ : syracuseStep 10631839 = 15947759) B15947759
theorem B14175785 : Blo 2181435 14175785 := bstep (se 2 (by rfl) ⟨5315919, by rfl⟩ : syracuseStep 14175785 = 10631839) B10631839
theorem B9450523 : Blo 2181435 9450523 := bstep (se 1 (by rfl) ⟨7087892, by rfl⟩ : syracuseStep 9450523 = 14175785) B14175785
theorem B12600697 : Blo 2181435 12600697 := bstep (se 2 (by rfl) ⟨4725261, by rfl⟩ : syracuseStep 12600697 = 9450523) B9450523
theorem B16800929 : Blo 2181435 16800929 := bstep (se 2 (by rfl) ⟨6300348, by rfl⟩ : syracuseStep 16800929 = 12600697) B12600697
theorem B11200619 : Blo 2181435 11200619 := bstep (se 1 (by rfl) ⟨8400464, by rfl⟩ : syracuseStep 11200619 = 16800929) B16800929
theorem B7467079 : Blo 2181435 7467079 := bstep (se 1 (by rfl) ⟨5600309, by rfl⟩ : syracuseStep 7467079 = 11200619) B11200619
theorem B9956105 : Blo 2181435 9956105 := bstep (se 2 (by rfl) ⟨3733539, by rfl⟩ : syracuseStep 9956105 = 7467079) B7467079
theorem B6637403 : Blo 2181435 6637403 := bstep (se 1 (by rfl) ⟨4978052, by rfl⟩ : syracuseStep 6637403 = 9956105) B9956105
theorem B17699741 : Blo 2181435 17699741 := bstep (se 3 (by rfl) ⟨3318701, by rfl⟩ : syracuseStep 17699741 = 6637403) B6637403
theorem B11799827 : Blo 2181435 11799827 := bstep (se 1 (by rfl) ⟨8849870, by rfl⟩ : syracuseStep 11799827 = 17699741) B17699741
theorem B7866551 : Blo 2181435 7866551 := bstep (se 1 (by rfl) ⟨5899913, by rfl⟩ : syracuseStep 7866551 = 11799827) B11799827
theorem B5244367 : Blo 2181435 5244367 := bstep (se 1 (by rfl) ⟨3933275, by rfl⟩ : syracuseStep 5244367 = 7866551) B7866551
theorem B6992489 : Blo 2181435 6992489 := bstep (se 2 (by rfl) ⟨2622183, by rfl⟩ : syracuseStep 6992489 = 5244367) B5244367
theorem B4661659 : Blo 2181435 4661659 := bstep (se 1 (by rfl) ⟨3496244, by rfl⟩ : syracuseStep 4661659 = 6992489) B6992489
theorem B6215545 : Blo 2181435 6215545 := bstep (se 2 (by rfl) ⟨2330829, by rfl⟩ : syracuseStep 6215545 = 4661659) B4661659
theorem B8287393 : Blo 2181435 8287393 := bstep (se 2 (by rfl) ⟨3107772, by rfl⟩ : syracuseStep 8287393 = 6215545) B6215545
theorem B11049857 : Blo 2181435 11049857 := bstep (se 2 (by rfl) ⟨4143696, by rfl⟩ : syracuseStep 11049857 = 8287393) B8287393
theorem B7366571 : Blo 2181435 7366571 := bstep (se 1 (by rfl) ⟨5524928, by rfl⟩ : syracuseStep 7366571 = 11049857) B11049857
theorem B4911047 : Blo 2181435 4911047 := bstep (se 1 (by rfl) ⟨3683285, by rfl⟩ : syracuseStep 4911047 = 7366571) B7366571
theorem B3274031 : Blo 2181435 3274031 := bstep (se 1 (by rfl) ⟨2455523, by rfl⟩ : syracuseStep 3274031 = 4911047) B4911047
theorem B2182687 : Blo 2181435 2182687 := bstep (se 1 (by rfl) ⟨1637015, by rfl⟩ : syracuseStep 2182687 = 3274031) B3274031
theorem B3274037 : Blo 2181435 3274037 := bbase (se 5 (by rfl) ⟨153470, by rfl⟩ : syracuseStep 3274037 = 306941) (by norm_num)
theorem B2182691 : Blo 2181435 2182691 := bstep (se 1 (by rfl) ⟨1637018, by rfl⟩ : syracuseStep 2182691 = 3274037) B3274037
theorem B5524949 : Blo 2181435 5524949 := bbase (se 7 (by rfl) ⟨64745, by rfl⟩ : syracuseStep 5524949 = 129491) (by norm_num)
theorem B3683299 : Blo 2181435 3683299 := bstep (se 1 (by rfl) ⟨2762474, by rfl⟩ : syracuseStep 3683299 = 5524949) B5524949
theorem B4911065 : Blo 2181435 4911065 := bstep (se 2 (by rfl) ⟨1841649, by rfl⟩ : syracuseStep 4911065 = 3683299) B3683299
theorem B3274043 : Blo 2181435 3274043 := bstep (se 1 (by rfl) ⟨2455532, by rfl⟩ : syracuseStep 3274043 = 4911065) B4911065
theorem B2182695 : Blo 2181435 2182695 := bstep (se 1 (by rfl) ⟨1637021, by rfl⟩ : syracuseStep 2182695 = 3274043) B3274043
theorem B2455537 : Blo 2181435 2455537 := bbase (se 2 (by rfl) ⟨920826, by rfl⟩ : syracuseStep 2455537 = 1841653) (by norm_num)
theorem B3274049 : Blo 2181435 3274049 := bstep (se 2 (by rfl) ⟨1227768, by rfl⟩ : syracuseStep 3274049 = 2455537) B2455537
theorem B2182699 : Blo 2181435 2182699 := bstep (se 1 (by rfl) ⟨1637024, by rfl⟩ : syracuseStep 2182699 = 3274049) B3274049
theorem B4485341 : Blo 2181435 4485341 := bbase (se 3 (by rfl) ⟨841001, by rfl⟩ : syracuseStep 4485341 = 1682003) (by norm_num)
theorem B11960909 : Blo 2181435 11960909 := bstep (se 3 (by rfl) ⟨2242670, by rfl⟩ : syracuseStep 11960909 = 4485341) B4485341
theorem B7973939 : Blo 2181435 7973939 := bstep (se 1 (by rfl) ⟨5980454, by rfl⟩ : syracuseStep 7973939 = 11960909) B11960909
theorem B5315959 : Blo 2181435 5315959 := bstep (se 1 (by rfl) ⟨3986969, by rfl⟩ : syracuseStep 5315959 = 7973939) B7973939
theorem B7087945 : Blo 2181435 7087945 := bstep (se 2 (by rfl) ⟨2657979, by rfl⟩ : syracuseStep 7087945 = 5315959) B5315959
theorem B9450593 : Blo 2181435 9450593 := bstep (se 2 (by rfl) ⟨3543972, by rfl⟩ : syracuseStep 9450593 = 7087945) B7087945
theorem B6300395 : Blo 2181435 6300395 := bstep (se 1 (by rfl) ⟨4725296, by rfl⟩ : syracuseStep 6300395 = 9450593) B9450593
theorem B4200263 : Blo 2181435 4200263 := bstep (se 1 (by rfl) ⟨3150197, by rfl⟩ : syracuseStep 4200263 = 6300395) B6300395
theorem B2800175 : Blo 2181435 2800175 := bstep (se 1 (by rfl) ⟨2100131, by rfl⟩ : syracuseStep 2800175 = 4200263) B4200263
theorem B29868533 : Blo 2181435 29868533 := bstep (se 5 (by rfl) ⟨1400087, by rfl⟩ : syracuseStep 29868533 = 2800175) B2800175
theorem B19912355 : Blo 2181435 19912355 := bstep (se 1 (by rfl) ⟨14934266, by rfl⟩ : syracuseStep 19912355 = 29868533) B29868533
theorem B13274903 : Blo 2181435 13274903 := bstep (se 1 (by rfl) ⟨9956177, by rfl⟩ : syracuseStep 13274903 = 19912355) B19912355
theorem B8849935 : Blo 2181435 8849935 := bstep (se 1 (by rfl) ⟨6637451, by rfl⟩ : syracuseStep 8849935 = 13274903) B13274903
theorem B11799913 : Blo 2181435 11799913 := bstep (se 2 (by rfl) ⟨4424967, by rfl⟩ : syracuseStep 11799913 = 8849935) B8849935
theorem B15733217 : Blo 2181435 15733217 := bstep (se 2 (by rfl) ⟨5899956, by rfl⟩ : syracuseStep 15733217 = 11799913) B11799913
theorem B10488811 : Blo 2181435 10488811 := bstep (se 1 (by rfl) ⟨7866608, by rfl⟩ : syracuseStep 10488811 = 15733217) B15733217
theorem B13985081 : Blo 2181435 13985081 := bstep (se 2 (by rfl) ⟨5244405, by rfl⟩ : syracuseStep 13985081 = 10488811) B10488811
theorem B9323387 : Blo 2181435 9323387 := bstep (se 1 (by rfl) ⟨6992540, by rfl⟩ : syracuseStep 9323387 = 13985081) B13985081
theorem B6215591 : Blo 2181435 6215591 := bstep (se 1 (by rfl) ⟨4661693, by rfl⟩ : syracuseStep 6215591 = 9323387) B9323387
theorem B4143727 : Blo 2181435 4143727 := bstep (se 1 (by rfl) ⟨3107795, by rfl⟩ : syracuseStep 4143727 = 6215591) B6215591
theorem B5524969 : Blo 2181435 5524969 := bstep (se 2 (by rfl) ⟨2071863, by rfl⟩ : syracuseStep 5524969 = 4143727) B4143727
theorem B7366625 : Blo 2181435 7366625 := bstep (se 2 (by rfl) ⟨2762484, by rfl⟩ : syracuseStep 7366625 = 5524969) B5524969
theorem B4911083 : Blo 2181435 4911083 := bstep (se 1 (by rfl) ⟨3683312, by rfl⟩ : syracuseStep 4911083 = 7366625) B7366625
theorem B3274055 : Blo 2181435 3274055 := bstep (se 1 (by rfl) ⟨2455541, by rfl⟩ : syracuseStep 3274055 = 4911083) B4911083
theorem B2182703 : Blo 2181435 2182703 := bstep (se 1 (by rfl) ⟨1637027, by rfl⟩ : syracuseStep 2182703 = 3274055) B3274055
theorem B3274061 : Blo 2181435 3274061 := bbase (se 3 (by rfl) ⟨613886, by rfl⟩ : syracuseStep 3274061 = 1227773) (by norm_num)
theorem B2182707 : Blo 2181435 2182707 := bstep (se 1 (by rfl) ⟨1637030, by rfl⟩ : syracuseStep 2182707 = 3274061) B3274061
theorem B4911101 : Blo 2181435 4911101 := bbase (se 3 (by rfl) ⟨920831, by rfl⟩ : syracuseStep 4911101 = 1841663) (by norm_num)
theorem B3274067 : Blo 2181435 3274067 := bstep (se 1 (by rfl) ⟨2455550, by rfl⟩ : syracuseStep 3274067 = 4911101) B4911101
theorem B2182711 : Blo 2181435 2182711 := bstep (se 1 (by rfl) ⟨1637033, by rfl⟩ : syracuseStep 2182711 = 3274067) B3274067
theorem B3683333 : Blo 2181435 3683333 := bbase (se 4 (by rfl) ⟨345312, by rfl⟩ : syracuseStep 3683333 = 690625) (by norm_num)
theorem B2455555 : Blo 2181435 2455555 := bstep (se 1 (by rfl) ⟨1841666, by rfl⟩ : syracuseStep 2455555 = 3683333) B3683333
theorem B3274073 : Blo 2181435 3274073 := bstep (se 2 (by rfl) ⟨1227777, by rfl⟩ : syracuseStep 3274073 = 2455555) B2455555
theorem B2182715 : Blo 2181435 2182715 := bstep (se 1 (by rfl) ⟨1637036, by rfl⟩ : syracuseStep 2182715 = 3274073) B3274073
theorem B16575029 : Blo 2181435 16575029 := bbase (se 5 (by rfl) ⟨776954, by rfl⟩ : syracuseStep 16575029 = 1553909) (by norm_num)
theorem B11050019 : Blo 2181435 11050019 := bstep (se 1 (by rfl) ⟨8287514, by rfl⟩ : syracuseStep 11050019 = 16575029) B16575029
theorem B7366679 : Blo 2181435 7366679 := bstep (se 1 (by rfl) ⟨5525009, by rfl⟩ : syracuseStep 7366679 = 11050019) B11050019
theorem B4911119 : Blo 2181435 4911119 := bstep (se 1 (by rfl) ⟨3683339, by rfl⟩ : syracuseStep 4911119 = 7366679) B7366679
theorem B3274079 : Blo 2181435 3274079 := bstep (se 1 (by rfl) ⟨2455559, by rfl⟩ : syracuseStep 3274079 = 4911119) B4911119
theorem B2182719 : Blo 2181435 2182719 := bstep (se 1 (by rfl) ⟨1637039, by rfl⟩ : syracuseStep 2182719 = 3274079) B3274079
theorem B3274085 : Blo 2181435 3274085 := bbase (se 4 (by rfl) ⟨306945, by rfl⟩ : syracuseStep 3274085 = 613891) (by norm_num)
theorem B2182723 : Blo 2181435 2182723 := bstep (se 1 (by rfl) ⟨1637042, by rfl⟩ : syracuseStep 2182723 = 3274085) B3274085
theorem B4143773 : Blo 2181435 4143773 := bbase (se 3 (by rfl) ⟨776957, by rfl⟩ : syracuseStep 4143773 = 1553915) (by norm_num)
theorem B2762515 : Blo 2181435 2762515 := bstep (se 1 (by rfl) ⟨2071886, by rfl⟩ : syracuseStep 2762515 = 4143773) B4143773
theorem B3683353 : Blo 2181435 3683353 := bstep (se 2 (by rfl) ⟨1381257, by rfl⟩ : syracuseStep 3683353 = 2762515) B2762515
theorem B4911137 : Blo 2181435 4911137 := bstep (se 2 (by rfl) ⟨1841676, by rfl⟩ : syracuseStep 4911137 = 3683353) B3683353
theorem B3274091 : Blo 2181435 3274091 := bstep (se 1 (by rfl) ⟨2455568, by rfl⟩ : syracuseStep 3274091 = 4911137) B4911137
theorem B2182727 : Blo 2181435 2182727 := bstep (se 1 (by rfl) ⟨1637045, by rfl⟩ : syracuseStep 2182727 = 3274091) B3274091
theorem B2455573 : Blo 2181435 2455573 := bbase (se 6 (by rfl) ⟨57552, by rfl⟩ : syracuseStep 2455573 = 115105) (by norm_num)
theorem B3274097 : Blo 2181435 3274097 := bstep (se 2 (by rfl) ⟨1227786, by rfl⟩ : syracuseStep 3274097 = 2455573) B2455573
theorem B2182731 : Blo 2181435 2182731 := bstep (se 1 (by rfl) ⟨1637048, by rfl⟩ : syracuseStep 2182731 = 3274097) B3274097
theorem B2762525 : Blo 2181435 2762525 := bbase (se 3 (by rfl) ⟨517973, by rfl⟩ : syracuseStep 2762525 = 1035947) (by norm_num)
theorem B7366733 : Blo 2181435 7366733 := bstep (se 3 (by rfl) ⟨1381262, by rfl⟩ : syracuseStep 7366733 = 2762525) B2762525
theorem B4911155 : Blo 2181435 4911155 := bstep (se 1 (by rfl) ⟨3683366, by rfl⟩ : syracuseStep 4911155 = 7366733) B7366733
theorem B3274103 : Blo 2181435 3274103 := bstep (se 1 (by rfl) ⟨2455577, by rfl⟩ : syracuseStep 3274103 = 4911155) B4911155
theorem B2182735 : Blo 2181435 2182735 := bstep (se 1 (by rfl) ⟨1637051, by rfl⟩ : syracuseStep 2182735 = 3274103) B3274103
theorem B3274109 : Blo 2181435 3274109 := bbase (se 3 (by rfl) ⟨613895, by rfl⟩ : syracuseStep 3274109 = 1227791) (by norm_num)
theorem B2182739 : Blo 2181435 2182739 := bstep (se 1 (by rfl) ⟨1637054, by rfl⟩ : syracuseStep 2182739 = 3274109) B3274109
theorem B4911173 : Blo 2181435 4911173 := bbase (se 4 (by rfl) ⟨460422, by rfl⟩ : syracuseStep 4911173 = 920845) (by norm_num)
theorem B3274115 : Blo 2181435 3274115 := bstep (se 1 (by rfl) ⟨2455586, by rfl⟩ : syracuseStep 3274115 = 4911173) B4911173
theorem B2182743 : Blo 2181435 2182743 := bstep (se 1 (by rfl) ⟨1637057, by rfl⟩ : syracuseStep 2182743 = 3274115) B3274115
theorem B6215717 : Blo 2181435 6215717 := bbase (se 4 (by rfl) ⟨582723, by rfl⟩ : syracuseStep 6215717 = 1165447) (by norm_num)
theorem B4143811 : Blo 2181435 4143811 := bstep (se 1 (by rfl) ⟨3107858, by rfl⟩ : syracuseStep 4143811 = 6215717) B6215717
theorem B5525081 : Blo 2181435 5525081 := bstep (se 2 (by rfl) ⟨2071905, by rfl⟩ : syracuseStep 5525081 = 4143811) B4143811
theorem B3683387 : Blo 2181435 3683387 := bstep (se 1 (by rfl) ⟨2762540, by rfl⟩ : syracuseStep 3683387 = 5525081) B5525081
theorem B2455591 : Blo 2181435 2455591 := bstep (se 1 (by rfl) ⟨1841693, by rfl⟩ : syracuseStep 2455591 = 3683387) B3683387
theorem B3274121 : Blo 2181435 3274121 := bstep (se 2 (by rfl) ⟨1227795, by rfl⟩ : syracuseStep 3274121 = 2455591) B2455591
theorem B2182747 : Blo 2181435 2182747 := bstep (se 1 (by rfl) ⟨1637060, by rfl⟩ : syracuseStep 2182747 = 3274121) B3274121
theorem B11050181 : Blo 2181435 11050181 := bbase (se 4 (by rfl) ⟨1035954, by rfl⟩ : syracuseStep 11050181 = 2071909) (by norm_num)
theorem B7366787 : Blo 2181435 7366787 := bstep (se 1 (by rfl) ⟨5525090, by rfl⟩ : syracuseStep 7366787 = 11050181) B11050181
theorem B4911191 : Blo 2181435 4911191 := bstep (se 1 (by rfl) ⟨3683393, by rfl⟩ : syracuseStep 4911191 = 7366787) B7366787
theorem B3274127 : Blo 2181435 3274127 := bstep (se 1 (by rfl) ⟨2455595, by rfl⟩ : syracuseStep 3274127 = 4911191) B4911191
theorem B2182751 : Blo 2181435 2182751 := bstep (se 1 (by rfl) ⟨1637063, by rfl⟩ : syracuseStep 2182751 = 3274127) B3274127
theorem B3274133 : Blo 2181435 3274133 := bbase (se 6 (by rfl) ⟨76737, by rfl⟩ : syracuseStep 3274133 = 153475) (by norm_num)
theorem B2182755 : Blo 2181435 2182755 := bstep (se 1 (by rfl) ⟨1637066, by rfl⟩ : syracuseStep 2182755 = 3274133) B3274133
theorem B4661813 : Blo 2181435 4661813 := bbase (se 5 (by rfl) ⟨218522, by rfl⟩ : syracuseStep 4661813 = 437045) (by norm_num)
theorem B12431501 : Blo 2181435 12431501 := bstep (se 3 (by rfl) ⟨2330906, by rfl⟩ : syracuseStep 12431501 = 4661813) B4661813
theorem B8287667 : Blo 2181435 8287667 := bstep (se 1 (by rfl) ⟨6215750, by rfl⟩ : syracuseStep 8287667 = 12431501) B12431501
theorem B5525111 : Blo 2181435 5525111 := bstep (se 1 (by rfl) ⟨4143833, by rfl⟩ : syracuseStep 5525111 = 8287667) B8287667
theorem B3683407 : Blo 2181435 3683407 := bstep (se 1 (by rfl) ⟨2762555, by rfl⟩ : syracuseStep 3683407 = 5525111) B5525111
theorem B4911209 : Blo 2181435 4911209 := bstep (se 2 (by rfl) ⟨1841703, by rfl⟩ : syracuseStep 4911209 = 3683407) B3683407
theorem B3274139 : Blo 2181435 3274139 := bstep (se 1 (by rfl) ⟨2455604, by rfl⟩ : syracuseStep 3274139 = 4911209) B4911209
theorem B2182759 : Blo 2181435 2182759 := bstep (se 1 (by rfl) ⟨1637069, by rfl⟩ : syracuseStep 2182759 = 3274139) B3274139
theorem B2455609 : Blo 2181435 2455609 := bbase (se 2 (by rfl) ⟨920853, by rfl⟩ : syracuseStep 2455609 = 1841707) (by norm_num)
theorem B3274145 : Blo 2181435 3274145 := bstep (se 2 (by rfl) ⟨1227804, by rfl⟩ : syracuseStep 3274145 = 2455609) B2455609
theorem B2182763 : Blo 2181435 2182763 := bstep (se 1 (by rfl) ⟨1637072, by rfl⟩ : syracuseStep 2182763 = 3274145) B3274145
theorem B3496373 : Blo 2181435 3496373 := bbase (se 5 (by rfl) ⟨163892, by rfl⟩ : syracuseStep 3496373 = 327785) (by norm_num)
theorem B2330915 : Blo 2181435 2330915 := bstep (se 1 (by rfl) ⟨1748186, by rfl⟩ : syracuseStep 2330915 = 3496373) B3496373
theorem B6215773 : Blo 2181435 6215773 := bstep (se 3 (by rfl) ⟨1165457, by rfl⟩ : syracuseStep 6215773 = 2330915) B2330915
theorem B8287697 : Blo 2181435 8287697 := bstep (se 2 (by rfl) ⟨3107886, by rfl⟩ : syracuseStep 8287697 = 6215773) B6215773
theorem B5525131 : Blo 2181435 5525131 := bstep (se 1 (by rfl) ⟨4143848, by rfl⟩ : syracuseStep 5525131 = 8287697) B8287697
theorem B7366841 : Blo 2181435 7366841 := bstep (se 2 (by rfl) ⟨2762565, by rfl⟩ : syracuseStep 7366841 = 5525131) B5525131
theorem B4911227 : Blo 2181435 4911227 := bstep (se 1 (by rfl) ⟨3683420, by rfl⟩ : syracuseStep 4911227 = 7366841) B7366841
theorem B3274151 : Blo 2181435 3274151 := bstep (se 1 (by rfl) ⟨2455613, by rfl⟩ : syracuseStep 3274151 = 4911227) B4911227
theorem B2182767 : Blo 2181435 2182767 := bstep (se 1 (by rfl) ⟨1637075, by rfl⟩ : syracuseStep 2182767 = 3274151) B3274151
theorem B3274157 : Blo 2181435 3274157 := bbase (se 3 (by rfl) ⟨613904, by rfl⟩ : syracuseStep 3274157 = 1227809) (by norm_num)
theorem B2182771 : Blo 2181435 2182771 := bstep (se 1 (by rfl) ⟨1637078, by rfl⟩ : syracuseStep 2182771 = 3274157) B3274157
theorem B4911245 : Blo 2181435 4911245 := bbase (se 3 (by rfl) ⟨920858, by rfl⟩ : syracuseStep 4911245 = 1841717) (by norm_num)
theorem B3274163 : Blo 2181435 3274163 := bstep (se 1 (by rfl) ⟨2455622, by rfl⟩ : syracuseStep 3274163 = 4911245) B4911245
theorem B2182775 : Blo 2181435 2182775 := bstep (se 1 (by rfl) ⟨1637081, by rfl⟩ : syracuseStep 2182775 = 3274163) B3274163
theorem B2762581 : Blo 2181435 2762581 := bbase (se 9 (by rfl) ⟨8093, by rfl⟩ : syracuseStep 2762581 = 16187) (by norm_num)
theorem B3683441 : Blo 2181435 3683441 := bstep (se 2 (by rfl) ⟨1381290, by rfl⟩ : syracuseStep 3683441 = 2762581) B2762581
theorem B2455627 : Blo 2181435 2455627 := bstep (se 1 (by rfl) ⟨1841720, by rfl⟩ : syracuseStep 2455627 = 3683441) B3683441
theorem B3274169 : Blo 2181435 3274169 := bstep (se 2 (by rfl) ⟨1227813, by rfl⟩ : syracuseStep 3274169 = 2455627) B2455627
theorem B2182779 : Blo 2181435 2182779 := bstep (se 1 (by rfl) ⟨1637084, by rfl⟩ : syracuseStep 2182779 = 3274169) B3274169
theorem B51092693 : Blo 2181435 51092693 := bbase (se 7 (by rfl) ⟨598742, by rfl⟩ : syracuseStep 51092693 = 1197485) (by norm_num)
theorem B34061795 : Blo 2181435 34061795 := bstep (se 1 (by rfl) ⟨25546346, by rfl⟩ : syracuseStep 34061795 = 51092693) B51092693
theorem B22707863 : Blo 2181435 22707863 := bstep (se 1 (by rfl) ⟨17030897, by rfl⟩ : syracuseStep 22707863 = 34061795) B34061795
theorem B15138575 : Blo 2181435 15138575 := bstep (se 1 (by rfl) ⟨11353931, by rfl⟩ : syracuseStep 15138575 = 22707863) B22707863
theorem B10092383 : Blo 2181435 10092383 := bstep (se 1 (by rfl) ⟨7569287, by rfl⟩ : syracuseStep 10092383 = 15138575) B15138575
theorem B6728255 : Blo 2181435 6728255 := bstep (se 1 (by rfl) ⟨5046191, by rfl⟩ : syracuseStep 6728255 = 10092383) B10092383
theorem B4485503 : Blo 2181435 4485503 := bstep (se 1 (by rfl) ⟨3364127, by rfl⟩ : syracuseStep 4485503 = 6728255) B6728255
theorem B11961341 : Blo 2181435 11961341 := bstep (se 3 (by rfl) ⟨2242751, by rfl⟩ : syracuseStep 11961341 = 4485503) B4485503
theorem B7974227 : Blo 2181435 7974227 := bstep (se 1 (by rfl) ⟨5980670, by rfl⟩ : syracuseStep 7974227 = 11961341) B11961341
theorem B21264605 : Blo 2181435 21264605 := bstep (se 3 (by rfl) ⟨3987113, by rfl⟩ : syracuseStep 21264605 = 7974227) B7974227
theorem B14176403 : Blo 2181435 14176403 := bstep (se 1 (by rfl) ⟨10632302, by rfl⟩ : syracuseStep 14176403 = 21264605) B21264605
theorem B9450935 : Blo 2181435 9450935 := bstep (se 1 (by rfl) ⟨7088201, by rfl⟩ : syracuseStep 9450935 = 14176403) B14176403
theorem B6300623 : Blo 2181435 6300623 := bstep (se 1 (by rfl) ⟨4725467, by rfl⟩ : syracuseStep 6300623 = 9450935) B9450935
theorem B16801661 : Blo 2181435 16801661 := bstep (se 3 (by rfl) ⟨3150311, by rfl⟩ : syracuseStep 16801661 = 6300623) B6300623
theorem B44804429 : Blo 2181435 44804429 := bstep (se 3 (by rfl) ⟨8400830, by rfl⟩ : syracuseStep 44804429 = 16801661) B16801661
theorem B29869619 : Blo 2181435 29869619 := bstep (se 1 (by rfl) ⟨22402214, by rfl⟩ : syracuseStep 29869619 = 44804429) B44804429
theorem B79652317 : Blo 2181435 79652317 := bstep (se 3 (by rfl) ⟨14934809, by rfl⟩ : syracuseStep 79652317 = 29869619) B29869619
theorem B106203089 : Blo 2181435 106203089 := bstep (se 2 (by rfl) ⟨39826158, by rfl⟩ : syracuseStep 106203089 = 79652317) B79652317
theorem B70802059 : Blo 2181435 70802059 := bstep (se 1 (by rfl) ⟨53101544, by rfl⟩ : syracuseStep 70802059 = 106203089) B106203089
theorem B94402745 : Blo 2181435 94402745 := bstep (se 2 (by rfl) ⟨35401029, by rfl⟩ : syracuseStep 94402745 = 70802059) B70802059
theorem B62935163 : Blo 2181435 62935163 := bstep (se 1 (by rfl) ⟨47201372, by rfl⟩ : syracuseStep 62935163 = 94402745) B94402745
theorem B41956775 : Blo 2181435 41956775 := bstep (se 1 (by rfl) ⟨31467581, by rfl⟩ : syracuseStep 41956775 = 62935163) B62935163
theorem B27971183 : Blo 2181435 27971183 := bstep (se 1 (by rfl) ⟨20978387, by rfl⟩ : syracuseStep 27971183 = 41956775) B41956775
theorem B18647455 : Blo 2181435 18647455 := bstep (se 1 (by rfl) ⟨13985591, by rfl⟩ : syracuseStep 18647455 = 27971183) B27971183
theorem B24863273 : Blo 2181435 24863273 := bstep (se 2 (by rfl) ⟨9323727, by rfl⟩ : syracuseStep 24863273 = 18647455) B18647455
theorem B16575515 : Blo 2181435 16575515 := bstep (se 1 (by rfl) ⟨12431636, by rfl⟩ : syracuseStep 16575515 = 24863273) B24863273
theorem B11050343 : Blo 2181435 11050343 := bstep (se 1 (by rfl) ⟨8287757, by rfl⟩ : syracuseStep 11050343 = 16575515) B16575515
theorem B7366895 : Blo 2181435 7366895 := bstep (se 1 (by rfl) ⟨5525171, by rfl⟩ : syracuseStep 7366895 = 11050343) B11050343
theorem B4911263 : Blo 2181435 4911263 := bstep (se 1 (by rfl) ⟨3683447, by rfl⟩ : syracuseStep 4911263 = 7366895) B7366895
theorem B3274175 : Blo 2181435 3274175 := bstep (se 1 (by rfl) ⟨2455631, by rfl⟩ : syracuseStep 3274175 = 4911263) B4911263
theorem B2182783 : Blo 2181435 2182783 := bstep (se 1 (by rfl) ⟨1637087, by rfl⟩ : syracuseStep 2182783 = 3274175) B3274175
theorem B3274181 : Blo 2181435 3274181 := bbase (se 4 (by rfl) ⟨306954, by rfl⟩ : syracuseStep 3274181 = 613909) (by norm_num)
theorem B2182787 : Blo 2181435 2182787 := bstep (se 1 (by rfl) ⟨1637090, by rfl⟩ : syracuseStep 2182787 = 3274181) B3274181
theorem B3683461 : Blo 2181435 3683461 := bbase (se 4 (by rfl) ⟨345324, by rfl⟩ : syracuseStep 3683461 = 690649) (by norm_num)
theorem B4911281 : Blo 2181435 4911281 := bstep (se 2 (by rfl) ⟨1841730, by rfl⟩ : syracuseStep 4911281 = 3683461) B3683461
theorem B3274187 : Blo 2181435 3274187 := bstep (se 1 (by rfl) ⟨2455640, by rfl⟩ : syracuseStep 3274187 = 4911281) B4911281
theorem B2182791 : Blo 2181435 2182791 := bstep (se 1 (by rfl) ⟨1637093, by rfl⟩ : syracuseStep 2182791 = 3274187) B3274187
theorem B2455645 : Blo 2181435 2455645 := bbase (se 3 (by rfl) ⟨460433, by rfl⟩ : syracuseStep 2455645 = 920867) (by norm_num)
theorem B3274193 : Blo 2181435 3274193 := bstep (se 2 (by rfl) ⟨1227822, by rfl⟩ : syracuseStep 3274193 = 2455645) B2455645
theorem B2182795 : Blo 2181435 2182795 := bstep (se 1 (by rfl) ⟨1637096, by rfl⟩ : syracuseStep 2182795 = 3274193) B3274193
theorem B7366949 : Blo 2181435 7366949 := bbase (se 4 (by rfl) ⟨690651, by rfl⟩ : syracuseStep 7366949 = 1381303) (by norm_num)
theorem B4911299 : Blo 2181435 4911299 := bstep (se 1 (by rfl) ⟨3683474, by rfl⟩ : syracuseStep 4911299 = 7366949) B7366949
theorem B3274199 : Blo 2181435 3274199 := bstep (se 1 (by rfl) ⟨2455649, by rfl⟩ : syracuseStep 3274199 = 4911299) B4911299
theorem B2182799 : Blo 2181435 2182799 := bstep (se 1 (by rfl) ⟨1637099, by rfl⟩ : syracuseStep 2182799 = 3274199) B3274199
theorem B3274205 : Blo 2181435 3274205 := bbase (se 3 (by rfl) ⟨613913, by rfl⟩ : syracuseStep 3274205 = 1227827) (by norm_num)
theorem B2182803 : Blo 2181435 2182803 := bstep (se 1 (by rfl) ⟨1637102, by rfl⟩ : syracuseStep 2182803 = 3274205) B3274205
theorem B4911317 : Blo 2181435 4911317 := bbase (se 7 (by rfl) ⟨57554, by rfl⟩ : syracuseStep 4911317 = 115109) (by norm_num)
theorem B3274211 : Blo 2181435 3274211 := bstep (se 1 (by rfl) ⟨2455658, by rfl⟩ : syracuseStep 3274211 = 4911317) B4911317
theorem B2182807 : Blo 2181435 2182807 := bstep (se 1 (by rfl) ⟨1637105, by rfl⟩ : syracuseStep 2182807 = 3274211) B3274211
theorem B6637781 : Blo 2181435 6637781 := bbase (se 7 (by rfl) ⟨77786, by rfl⟩ : syracuseStep 6637781 = 155573) (by norm_num)
theorem B4425187 : Blo 2181435 4425187 := bstep (se 1 (by rfl) ⟨3318890, by rfl⟩ : syracuseStep 4425187 = 6637781) B6637781
theorem B5900249 : Blo 2181435 5900249 := bstep (se 2 (by rfl) ⟨2212593, by rfl⟩ : syracuseStep 5900249 = 4425187) B4425187
theorem B15733997 : Blo 2181435 15733997 := bstep (se 3 (by rfl) ⟨2950124, by rfl⟩ : syracuseStep 15733997 = 5900249) B5900249
theorem B10489331 : Blo 2181435 10489331 := bstep (se 1 (by rfl) ⟨7866998, by rfl⟩ : syracuseStep 10489331 = 15733997) B15733997
theorem B6992887 : Blo 2181435 6992887 := bstep (se 1 (by rfl) ⟨5244665, by rfl⟩ : syracuseStep 6992887 = 10489331) B10489331
theorem B9323849 : Blo 2181435 9323849 := bstep (se 2 (by rfl) ⟨3496443, by rfl⟩ : syracuseStep 9323849 = 6992887) B6992887
theorem B6215899 : Blo 2181435 6215899 := bstep (se 1 (by rfl) ⟨4661924, by rfl⟩ : syracuseStep 6215899 = 9323849) B9323849
theorem B8287865 : Blo 2181435 8287865 := bstep (se 2 (by rfl) ⟨3107949, by rfl⟩ : syracuseStep 8287865 = 6215899) B6215899
theorem B5525243 : Blo 2181435 5525243 := bstep (se 1 (by rfl) ⟨4143932, by rfl⟩ : syracuseStep 5525243 = 8287865) B8287865
theorem B3683495 : Blo 2181435 3683495 := bstep (se 1 (by rfl) ⟨2762621, by rfl⟩ : syracuseStep 3683495 = 5525243) B5525243
theorem B2455663 : Blo 2181435 2455663 := bstep (se 1 (by rfl) ⟨1841747, by rfl⟩ : syracuseStep 2455663 = 3683495) B3683495
theorem B3274217 : Blo 2181435 3274217 := bstep (se 2 (by rfl) ⟨1227831, by rfl⟩ : syracuseStep 3274217 = 2455663) B2455663
theorem B2182811 : Blo 2181435 2182811 := bstep (se 1 (by rfl) ⟨1637108, by rfl⟩ : syracuseStep 2182811 = 3274217) B3274217
theorem B2622337 : Blo 2181435 2622337 := bbase (se 2 (by rfl) ⟨983376, by rfl⟩ : syracuseStep 2622337 = 1966753) (by norm_num)
theorem B13985797 : Blo 2181435 13985797 := bstep (se 4 (by rfl) ⟨1311168, by rfl⟩ : syracuseStep 13985797 = 2622337) B2622337
theorem B18647729 : Blo 2181435 18647729 := bstep (se 2 (by rfl) ⟨6992898, by rfl⟩ : syracuseStep 18647729 = 13985797) B13985797
theorem B12431819 : Blo 2181435 12431819 := bstep (se 1 (by rfl) ⟨9323864, by rfl⟩ : syracuseStep 12431819 = 18647729) B18647729
theorem B8287879 : Blo 2181435 8287879 := bstep (se 1 (by rfl) ⟨6215909, by rfl⟩ : syracuseStep 8287879 = 12431819) B12431819
theorem B11050505 : Blo 2181435 11050505 := bstep (se 2 (by rfl) ⟨4143939, by rfl⟩ : syracuseStep 11050505 = 8287879) B8287879
theorem B7367003 : Blo 2181435 7367003 := bstep (se 1 (by rfl) ⟨5525252, by rfl⟩ : syracuseStep 7367003 = 11050505) B11050505
theorem B4911335 : Blo 2181435 4911335 := bstep (se 1 (by rfl) ⟨3683501, by rfl⟩ : syracuseStep 4911335 = 7367003) B7367003
theorem B3274223 : Blo 2181435 3274223 := bstep (se 1 (by rfl) ⟨2455667, by rfl⟩ : syracuseStep 3274223 = 4911335) B4911335
theorem B2182815 : Blo 2181435 2182815 := bstep (se 1 (by rfl) ⟨1637111, by rfl⟩ : syracuseStep 2182815 = 3274223) B3274223
theorem B3274229 : Blo 2181435 3274229 := bbase (se 5 (by rfl) ⟨153479, by rfl⟩ : syracuseStep 3274229 = 306959) (by norm_num)
theorem B2182819 : Blo 2181435 2182819 := bstep (se 1 (by rfl) ⟨1637114, by rfl⟩ : syracuseStep 2182819 = 3274229) B3274229
theorem B11800565 : Blo 2181435 11800565 := bbase (se 5 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 11800565 = 1106303) (by norm_num)
theorem B7867043 : Blo 2181435 7867043 := bstep (se 1 (by rfl) ⟨5900282, by rfl⟩ : syracuseStep 7867043 = 11800565) B11800565
theorem B5244695 : Blo 2181435 5244695 := bstep (se 1 (by rfl) ⟨3933521, by rfl⟩ : syracuseStep 5244695 = 7867043) B7867043
theorem B3496463 : Blo 2181435 3496463 := bstep (se 1 (by rfl) ⟨2622347, by rfl⟩ : syracuseStep 3496463 = 5244695) B5244695
theorem B2330975 : Blo 2181435 2330975 := bstep (se 1 (by rfl) ⟨1748231, by rfl⟩ : syracuseStep 2330975 = 3496463) B3496463
theorem B6215933 : Blo 2181435 6215933 := bstep (se 3 (by rfl) ⟨1165487, by rfl⟩ : syracuseStep 6215933 = 2330975) B2330975
theorem B4143955 : Blo 2181435 4143955 := bstep (se 1 (by rfl) ⟨3107966, by rfl⟩ : syracuseStep 4143955 = 6215933) B6215933
theorem B5525273 : Blo 2181435 5525273 := bstep (se 2 (by rfl) ⟨2071977, by rfl⟩ : syracuseStep 5525273 = 4143955) B4143955
theorem B3683515 : Blo 2181435 3683515 := bstep (se 1 (by rfl) ⟨2762636, by rfl⟩ : syracuseStep 3683515 = 5525273) B5525273
theorem B4911353 : Blo 2181435 4911353 := bstep (se 2 (by rfl) ⟨1841757, by rfl⟩ : syracuseStep 4911353 = 3683515) B3683515
theorem B3274235 : Blo 2181435 3274235 := bstep (se 1 (by rfl) ⟨2455676, by rfl⟩ : syracuseStep 3274235 = 4911353) B4911353
theorem B2182823 : Blo 2181435 2182823 := bstep (se 1 (by rfl) ⟨1637117, by rfl⟩ : syracuseStep 2182823 = 3274235) B3274235
theorem B2455681 : Blo 2181435 2455681 := bbase (se 2 (by rfl) ⟨920880, by rfl⟩ : syracuseStep 2455681 = 1841761) (by norm_num)
theorem B3274241 : Blo 2181435 3274241 := bstep (se 2 (by rfl) ⟨1227840, by rfl⟩ : syracuseStep 3274241 = 2455681) B2455681
theorem B2182827 : Blo 2181435 2182827 := bstep (se 1 (by rfl) ⟨1637120, by rfl⟩ : syracuseStep 2182827 = 3274241) B3274241
theorem B5525293 : Blo 2181435 5525293 := bbase (se 3 (by rfl) ⟨1035992, by rfl⟩ : syracuseStep 5525293 = 2071985) (by norm_num)
theorem B7367057 : Blo 2181435 7367057 := bstep (se 2 (by rfl) ⟨2762646, by rfl⟩ : syracuseStep 7367057 = 5525293) B5525293
theorem B4911371 : Blo 2181435 4911371 := bstep (se 1 (by rfl) ⟨3683528, by rfl⟩ : syracuseStep 4911371 = 7367057) B7367057
theorem B3274247 : Blo 2181435 3274247 := bstep (se 1 (by rfl) ⟨2455685, by rfl⟩ : syracuseStep 3274247 = 4911371) B4911371
theorem B2182831 : Blo 2181435 2182831 := bstep (se 1 (by rfl) ⟨1637123, by rfl⟩ : syracuseStep 2182831 = 3274247) B3274247
theorem B3274253 : Blo 2181435 3274253 := bbase (se 3 (by rfl) ⟨613922, by rfl⟩ : syracuseStep 3274253 = 1227845) (by norm_num)
theorem B2182835 : Blo 2181435 2182835 := bstep (se 1 (by rfl) ⟨1637126, by rfl⟩ : syracuseStep 2182835 = 3274253) B3274253
theorem B4911389 : Blo 2181435 4911389 := bbase (se 3 (by rfl) ⟨920885, by rfl⟩ : syracuseStep 4911389 = 1841771) (by norm_num)
theorem B3274259 : Blo 2181435 3274259 := bstep (se 1 (by rfl) ⟨2455694, by rfl⟩ : syracuseStep 3274259 = 4911389) B4911389
theorem B2182839 : Blo 2181435 2182839 := bstep (se 1 (by rfl) ⟨1637129, by rfl⟩ : syracuseStep 2182839 = 3274259) B3274259
theorem B3683549 : Blo 2181435 3683549 := bbase (se 3 (by rfl) ⟨690665, by rfl⟩ : syracuseStep 3683549 = 1381331) (by norm_num)
theorem B2455699 : Blo 2181435 2455699 := bstep (se 1 (by rfl) ⟨1841774, by rfl⟩ : syracuseStep 2455699 = 3683549) B3683549
theorem B3274265 : Blo 2181435 3274265 := bstep (se 2 (by rfl) ⟨1227849, by rfl⟩ : syracuseStep 3274265 = 2455699) B2455699
theorem B2182843 : Blo 2181435 2182843 := bstep (se 1 (by rfl) ⟨1637132, by rfl⟩ : syracuseStep 2182843 = 3274265) B3274265
theorem B3733813 : Blo 2181435 3733813 := bbase (se 5 (by rfl) ⟨175022, by rfl⟩ : syracuseStep 3733813 = 350045) (by norm_num)
theorem B4978417 : Blo 2181435 4978417 := bstep (se 2 (by rfl) ⟨1866906, by rfl⟩ : syracuseStep 4978417 = 3733813) B3733813
theorem B6637889 : Blo 2181435 6637889 := bstep (se 2 (by rfl) ⟨2489208, by rfl⟩ : syracuseStep 6637889 = 4978417) B4978417
theorem B17701037 : Blo 2181435 17701037 := bstep (se 3 (by rfl) ⟨3318944, by rfl⟩ : syracuseStep 17701037 = 6637889) B6637889
theorem B11800691 : Blo 2181435 11800691 := bstep (se 1 (by rfl) ⟨8850518, by rfl⟩ : syracuseStep 11800691 = 17701037) B17701037
theorem B7867127 : Blo 2181435 7867127 := bstep (se 1 (by rfl) ⟨5900345, by rfl⟩ : syracuseStep 7867127 = 11800691) B11800691
theorem B5244751 : Blo 2181435 5244751 := bstep (se 1 (by rfl) ⟨3933563, by rfl⟩ : syracuseStep 5244751 = 7867127) B7867127
theorem B6993001 : Blo 2181435 6993001 := bstep (se 2 (by rfl) ⟨2622375, by rfl⟩ : syracuseStep 6993001 = 5244751) B5244751
theorem B9324001 : Blo 2181435 9324001 := bstep (se 2 (by rfl) ⟨3496500, by rfl⟩ : syracuseStep 9324001 = 6993001) B6993001
theorem B12432001 : Blo 2181435 12432001 := bstep (se 2 (by rfl) ⟨4662000, by rfl⟩ : syracuseStep 12432001 = 9324001) B9324001
theorem B16576001 : Blo 2181435 16576001 := bstep (se 2 (by rfl) ⟨6216000, by rfl⟩ : syracuseStep 16576001 = 12432001) B12432001
theorem B11050667 : Blo 2181435 11050667 := bstep (se 1 (by rfl) ⟨8288000, by rfl⟩ : syracuseStep 11050667 = 16576001) B16576001
theorem B7367111 : Blo 2181435 7367111 := bstep (se 1 (by rfl) ⟨5525333, by rfl⟩ : syracuseStep 7367111 = 11050667) B11050667
theorem B4911407 : Blo 2181435 4911407 := bstep (se 1 (by rfl) ⟨3683555, by rfl⟩ : syracuseStep 4911407 = 7367111) B7367111
theorem B3274271 : Blo 2181435 3274271 := bstep (se 1 (by rfl) ⟨2455703, by rfl⟩ : syracuseStep 3274271 = 4911407) B4911407
theorem B2182847 : Blo 2181435 2182847 := bstep (se 1 (by rfl) ⟨1637135, by rfl⟩ : syracuseStep 2182847 = 3274271) B3274271
theorem B3274277 : Blo 2181435 3274277 := bbase (se 4 (by rfl) ⟨306963, by rfl⟩ : syracuseStep 3274277 = 613927) (by norm_num)
theorem B2182851 : Blo 2181435 2182851 := bstep (se 1 (by rfl) ⟨1637138, by rfl⟩ : syracuseStep 2182851 = 3274277) B3274277
theorem B2762677 : Blo 2181435 2762677 := bbase (se 5 (by rfl) ⟨129500, by rfl⟩ : syracuseStep 2762677 = 259001) (by norm_num)
theorem B3683569 : Blo 2181435 3683569 := bstep (se 2 (by rfl) ⟨1381338, by rfl⟩ : syracuseStep 3683569 = 2762677) B2762677
theorem B4911425 : Blo 2181435 4911425 := bstep (se 2 (by rfl) ⟨1841784, by rfl⟩ : syracuseStep 4911425 = 3683569) B3683569
theorem B3274283 : Blo 2181435 3274283 := bstep (se 1 (by rfl) ⟨2455712, by rfl⟩ : syracuseStep 3274283 = 4911425) B4911425
theorem B2182855 : Blo 2181435 2182855 := bstep (se 1 (by rfl) ⟨1637141, by rfl⟩ : syracuseStep 2182855 = 3274283) B3274283
theorem B2455717 : Blo 2181435 2455717 := bbase (se 4 (by rfl) ⟨230223, by rfl⟩ : syracuseStep 2455717 = 460447) (by norm_num)
theorem B3274289 : Blo 2181435 3274289 := bstep (se 2 (by rfl) ⟨1227858, by rfl⟩ : syracuseStep 3274289 = 2455717) B2455717
theorem B2182859 : Blo 2181435 2182859 := bstep (se 1 (by rfl) ⟨1637144, by rfl⟩ : syracuseStep 2182859 = 3274289) B3274289
theorem B23601557 : Blo 2181435 23601557 := bbase (se 6 (by rfl) ⟨553161, by rfl⟩ : syracuseStep 23601557 = 1106323) (by norm_num)
theorem B15734371 : Blo 2181435 15734371 := bstep (se 1 (by rfl) ⟨11800778, by rfl⟩ : syracuseStep 15734371 = 23601557) B23601557
theorem B20979161 : Blo 2181435 20979161 := bstep (se 2 (by rfl) ⟨7867185, by rfl⟩ : syracuseStep 20979161 = 15734371) B15734371
theorem B13986107 : Blo 2181435 13986107 := bstep (se 1 (by rfl) ⟨10489580, by rfl⟩ : syracuseStep 13986107 = 20979161) B20979161
theorem B9324071 : Blo 2181435 9324071 := bstep (se 1 (by rfl) ⟨6993053, by rfl⟩ : syracuseStep 9324071 = 13986107) B13986107
theorem B6216047 : Blo 2181435 6216047 := bstep (se 1 (by rfl) ⟨4662035, by rfl⟩ : syracuseStep 6216047 = 9324071) B9324071
theorem B4144031 : Blo 2181435 4144031 := bstep (se 1 (by rfl) ⟨3108023, by rfl⟩ : syracuseStep 4144031 = 6216047) B6216047
theorem B2762687 : Blo 2181435 2762687 := bstep (se 1 (by rfl) ⟨2072015, by rfl⟩ : syracuseStep 2762687 = 4144031) B4144031
theorem B7367165 : Blo 2181435 7367165 := bstep (se 3 (by rfl) ⟨1381343, by rfl⟩ : syracuseStep 7367165 = 2762687) B2762687
theorem B4911443 : Blo 2181435 4911443 := bstep (se 1 (by rfl) ⟨3683582, by rfl⟩ : syracuseStep 4911443 = 7367165) B7367165
theorem B3274295 : Blo 2181435 3274295 := bstep (se 1 (by rfl) ⟨2455721, by rfl⟩ : syracuseStep 3274295 = 4911443) B4911443
theorem B2182863 : Blo 2181435 2182863 := bstep (se 1 (by rfl) ⟨1637147, by rfl⟩ : syracuseStep 2182863 = 3274295) B3274295
theorem B3274301 : Blo 2181435 3274301 := bbase (se 3 (by rfl) ⟨613931, by rfl⟩ : syracuseStep 3274301 = 1227863) (by norm_num)
theorem B2182867 : Blo 2181435 2182867 := bstep (se 1 (by rfl) ⟨1637150, by rfl⟩ : syracuseStep 2182867 = 3274301) B3274301
theorem B4911461 : Blo 2181435 4911461 := bbase (se 4 (by rfl) ⟨460449, by rfl⟩ : syracuseStep 4911461 = 920899) (by norm_num)
theorem B3274307 : Blo 2181435 3274307 := bstep (se 1 (by rfl) ⟨2455730, by rfl⟩ : syracuseStep 3274307 = 4911461) B4911461
theorem B2182871 : Blo 2181435 2182871 := bstep (se 1 (by rfl) ⟨1637153, by rfl⟩ : syracuseStep 2182871 = 3274307) B3274307
theorem B5525405 : Blo 2181435 5525405 := bbase (se 3 (by rfl) ⟨1036013, by rfl⟩ : syracuseStep 5525405 = 2072027) (by norm_num)
theorem B3683603 : Blo 2181435 3683603 := bstep (se 1 (by rfl) ⟨2762702, by rfl⟩ : syracuseStep 3683603 = 5525405) B5525405
theorem B2455735 : Blo 2181435 2455735 := bstep (se 1 (by rfl) ⟨1841801, by rfl⟩ : syracuseStep 2455735 = 3683603) B3683603
theorem B3274313 : Blo 2181435 3274313 := bstep (se 2 (by rfl) ⟨1227867, by rfl⟩ : syracuseStep 3274313 = 2455735) B2455735
theorem B2182875 : Blo 2181435 2182875 := bstep (se 1 (by rfl) ⟨1637156, by rfl⟩ : syracuseStep 2182875 = 3274313) B3274313
theorem B4144061 : Blo 2181435 4144061 := bbase (se 3 (by rfl) ⟨777011, by rfl⟩ : syracuseStep 4144061 = 1554023) (by norm_num)
theorem B11050829 : Blo 2181435 11050829 := bstep (se 3 (by rfl) ⟨2072030, by rfl⟩ : syracuseStep 11050829 = 4144061) B4144061
theorem B7367219 : Blo 2181435 7367219 := bstep (se 1 (by rfl) ⟨5525414, by rfl⟩ : syracuseStep 7367219 = 11050829) B11050829
theorem B4911479 : Blo 2181435 4911479 := bstep (se 1 (by rfl) ⟨3683609, by rfl⟩ : syracuseStep 4911479 = 7367219) B7367219
theorem B3274319 : Blo 2181435 3274319 := bstep (se 1 (by rfl) ⟨2455739, by rfl⟩ : syracuseStep 3274319 = 4911479) B4911479
theorem B2182879 : Blo 2181435 2182879 := bstep (se 1 (by rfl) ⟨1637159, by rfl⟩ : syracuseStep 2182879 = 3274319) B3274319
theorem B3274325 : Blo 2181435 3274325 := bbase (se 8 (by rfl) ⟨19185, by rfl⟩ : syracuseStep 3274325 = 38371) (by norm_num)
theorem B2182883 : Blo 2181435 2182883 := bstep (se 1 (by rfl) ⟨1637162, by rfl⟩ : syracuseStep 2182883 = 3274325) B3274325
theorem B3496565 : Blo 2181435 3496565 := bbase (se 5 (by rfl) ⟨163901, by rfl⟩ : syracuseStep 3496565 = 327803) (by norm_num)
theorem B9324173 : Blo 2181435 9324173 := bstep (se 3 (by rfl) ⟨1748282, by rfl⟩ : syracuseStep 9324173 = 3496565) B3496565
theorem B6216115 : Blo 2181435 6216115 := bstep (se 1 (by rfl) ⟨4662086, by rfl⟩ : syracuseStep 6216115 = 9324173) B9324173
theorem B8288153 : Blo 2181435 8288153 := bstep (se 2 (by rfl) ⟨3108057, by rfl⟩ : syracuseStep 8288153 = 6216115) B6216115
theorem B5525435 : Blo 2181435 5525435 := bstep (se 1 (by rfl) ⟨4144076, by rfl⟩ : syracuseStep 5525435 = 8288153) B8288153
theorem B3683623 : Blo 2181435 3683623 := bstep (se 1 (by rfl) ⟨2762717, by rfl⟩ : syracuseStep 3683623 = 5525435) B5525435
theorem B4911497 : Blo 2181435 4911497 := bstep (se 2 (by rfl) ⟨1841811, by rfl⟩ : syracuseStep 4911497 = 3683623) B3683623
theorem B3274331 : Blo 2181435 3274331 := bstep (se 1 (by rfl) ⟨2455748, by rfl⟩ : syracuseStep 3274331 = 4911497) B4911497
theorem B2182887 : Blo 2181435 2182887 := bstep (se 1 (by rfl) ⟨1637165, by rfl⟩ : syracuseStep 2182887 = 3274331) B3274331
theorem B2455753 : Blo 2181435 2455753 := bbase (se 2 (by rfl) ⟨920907, by rfl⟩ : syracuseStep 2455753 = 1841815) (by norm_num)
theorem B3274337 : Blo 2181435 3274337 := bstep (se 2 (by rfl) ⟨1227876, by rfl⟩ : syracuseStep 3274337 = 2455753) B2455753
theorem B2182891 : Blo 2181435 2182891 := bstep (se 1 (by rfl) ⟨1637168, by rfl⟩ : syracuseStep 2182891 = 3274337) B3274337
theorem B10489733 : Blo 2181435 10489733 := bbase (se 4 (by rfl) ⟨983412, by rfl⟩ : syracuseStep 10489733 = 1966825) (by norm_num)
theorem B6993155 : Blo 2181435 6993155 := bstep (se 1 (by rfl) ⟨5244866, by rfl⟩ : syracuseStep 6993155 = 10489733) B10489733
theorem B18648413 : Blo 2181435 18648413 := bstep (se 3 (by rfl) ⟨3496577, by rfl⟩ : syracuseStep 18648413 = 6993155) B6993155
theorem B12432275 : Blo 2181435 12432275 := bstep (se 1 (by rfl) ⟨9324206, by rfl⟩ : syracuseStep 12432275 = 18648413) B18648413
theorem B8288183 : Blo 2181435 8288183 := bstep (se 1 (by rfl) ⟨6216137, by rfl⟩ : syracuseStep 8288183 = 12432275) B12432275
theorem B5525455 : Blo 2181435 5525455 := bstep (se 1 (by rfl) ⟨4144091, by rfl⟩ : syracuseStep 5525455 = 8288183) B8288183
theorem B7367273 : Blo 2181435 7367273 := bstep (se 2 (by rfl) ⟨2762727, by rfl⟩ : syracuseStep 7367273 = 5525455) B5525455
theorem B4911515 : Blo 2181435 4911515 := bstep (se 1 (by rfl) ⟨3683636, by rfl⟩ : syracuseStep 4911515 = 7367273) B7367273
theorem B3274343 : Blo 2181435 3274343 := bstep (se 1 (by rfl) ⟨2455757, by rfl⟩ : syracuseStep 3274343 = 4911515) B4911515
theorem B2182895 : Blo 2181435 2182895 := bstep (se 1 (by rfl) ⟨1637171, by rfl⟩ : syracuseStep 2182895 = 3274343) B3274343
theorem B3274349 : Blo 2181435 3274349 := bbase (se 3 (by rfl) ⟨613940, by rfl⟩ : syracuseStep 3274349 = 1227881) (by norm_num)
theorem B2182899 : Blo 2181435 2182899 := bstep (se 1 (by rfl) ⟨1637174, by rfl⟩ : syracuseStep 2182899 = 3274349) B3274349
theorem B4911533 : Blo 2181435 4911533 := bbase (se 3 (by rfl) ⟨920912, by rfl⟩ : syracuseStep 4911533 = 1841825) (by norm_num)
theorem B3274355 : Blo 2181435 3274355 := bstep (se 1 (by rfl) ⟨2455766, by rfl⟩ : syracuseStep 3274355 = 4911533) B4911533
theorem B2182903 : Blo 2181435 2182903 := bstep (se 1 (by rfl) ⟨1637177, by rfl⟩ : syracuseStep 2182903 = 3274355) B3274355
theorem B2331065 : Blo 2181435 2331065 := bbase (se 2 (by rfl) ⟨874149, by rfl⟩ : syracuseStep 2331065 = 1748299) (by norm_num)
theorem B6216173 : Blo 2181435 6216173 := bstep (se 3 (by rfl) ⟨1165532, by rfl⟩ : syracuseStep 6216173 = 2331065) B2331065
theorem B4144115 : Blo 2181435 4144115 := bstep (se 1 (by rfl) ⟨3108086, by rfl⟩ : syracuseStep 4144115 = 6216173) B6216173
theorem B2762743 : Blo 2181435 2762743 := bstep (se 1 (by rfl) ⟨2072057, by rfl⟩ : syracuseStep 2762743 = 4144115) B4144115
theorem B3683657 : Blo 2181435 3683657 := bstep (se 2 (by rfl) ⟨1381371, by rfl⟩ : syracuseStep 3683657 = 2762743) B2762743
theorem B2455771 : Blo 2181435 2455771 := bstep (se 1 (by rfl) ⟨1841828, by rfl⟩ : syracuseStep 2455771 = 3683657) B3683657
theorem B3274361 : Blo 2181435 3274361 := bstep (se 2 (by rfl) ⟨1227885, by rfl⟩ : syracuseStep 3274361 = 2455771) B2455771
theorem B2182907 : Blo 2181435 2182907 := bstep (se 1 (by rfl) ⟨1637180, by rfl⟩ : syracuseStep 2182907 = 3274361) B3274361
theorem B2489281 : Blo 2181435 2489281 := bbase (se 2 (by rfl) ⟨933480, by rfl⟩ : syracuseStep 2489281 = 1866961) (by norm_num)
theorem B13276165 : Blo 2181435 13276165 := bstep (se 4 (by rfl) ⟨1244640, by rfl⟩ : syracuseStep 13276165 = 2489281) B2489281
theorem B17701553 : Blo 2181435 17701553 := bstep (se 2 (by rfl) ⟨6638082, by rfl⟩ : syracuseStep 17701553 = 13276165) B13276165
theorem B11801035 : Blo 2181435 11801035 := bstep (se 1 (by rfl) ⟨8850776, by rfl⟩ : syracuseStep 11801035 = 17701553) B17701553
theorem B62938853 : Blo 2181435 62938853 := bstep (se 4 (by rfl) ⟨5900517, by rfl⟩ : syracuseStep 62938853 = 11801035) B11801035
theorem B41959235 : Blo 2181435 41959235 := bstep (se 1 (by rfl) ⟨31469426, by rfl⟩ : syracuseStep 41959235 = 62938853) B62938853
theorem B27972823 : Blo 2181435 27972823 := bstep (se 1 (by rfl) ⟨20979617, by rfl⟩ : syracuseStep 27972823 = 41959235) B41959235
theorem B37297097 : Blo 2181435 37297097 := bstep (se 2 (by rfl) ⟨13986411, by rfl⟩ : syracuseStep 37297097 = 27972823) B27972823
theorem B24864731 : Blo 2181435 24864731 := bstep (se 1 (by rfl) ⟨18648548, by rfl⟩ : syracuseStep 24864731 = 37297097) B37297097
theorem B16576487 : Blo 2181435 16576487 := bstep (se 1 (by rfl) ⟨12432365, by rfl⟩ : syracuseStep 16576487 = 24864731) B24864731
theorem B11050991 : Blo 2181435 11050991 := bstep (se 1 (by rfl) ⟨8288243, by rfl⟩ : syracuseStep 11050991 = 16576487) B16576487
theorem B7367327 : Blo 2181435 7367327 := bstep (se 1 (by rfl) ⟨5525495, by rfl⟩ : syracuseStep 7367327 = 11050991) B11050991
theorem B4911551 : Blo 2181435 4911551 := bstep (se 1 (by rfl) ⟨3683663, by rfl⟩ : syracuseStep 4911551 = 7367327) B7367327
theorem B3274367 : Blo 2181435 3274367 := bstep (se 1 (by rfl) ⟨2455775, by rfl⟩ : syracuseStep 3274367 = 4911551) B4911551
theorem B2182911 : Blo 2181435 2182911 := bstep (se 1 (by rfl) ⟨1637183, by rfl⟩ : syracuseStep 2182911 = 3274367) B3274367
theorem B3274373 : Blo 2181435 3274373 := bbase (se 4 (by rfl) ⟨306972, by rfl⟩ : syracuseStep 3274373 = 613945) (by norm_num)
theorem B2182915 : Blo 2181435 2182915 := bstep (se 1 (by rfl) ⟨1637186, by rfl⟩ : syracuseStep 2182915 = 3274373) B3274373
theorem B3683677 : Blo 2181435 3683677 := bbase (se 3 (by rfl) ⟨690689, by rfl⟩ : syracuseStep 3683677 = 1381379) (by norm_num)
theorem B4911569 : Blo 2181435 4911569 := bstep (se 2 (by rfl) ⟨1841838, by rfl⟩ : syracuseStep 4911569 = 3683677) B3683677
theorem B3274379 : Blo 2181435 3274379 := bstep (se 1 (by rfl) ⟨2455784, by rfl⟩ : syracuseStep 3274379 = 4911569) B4911569
theorem B2182919 : Blo 2181435 2182919 := bstep (se 1 (by rfl) ⟨1637189, by rfl⟩ : syracuseStep 2182919 = 3274379) B3274379
theorem B2455789 : Blo 2181435 2455789 := bbase (se 3 (by rfl) ⟨460460, by rfl⟩ : syracuseStep 2455789 = 920921) (by norm_num)
theorem B3274385 : Blo 2181435 3274385 := bstep (se 2 (by rfl) ⟨1227894, by rfl⟩ : syracuseStep 3274385 = 2455789) B2455789
theorem B2182923 : Blo 2181435 2182923 := bstep (se 1 (by rfl) ⟨1637192, by rfl⟩ : syracuseStep 2182923 = 3274385) B3274385
theorem B7367381 : Blo 2181435 7367381 := bbase (se 7 (by rfl) ⟨86336, by rfl⟩ : syracuseStep 7367381 = 172673) (by norm_num)
theorem B4911587 : Blo 2181435 4911587 := bstep (se 1 (by rfl) ⟨3683690, by rfl⟩ : syracuseStep 4911587 = 7367381) B7367381
theorem B3274391 : Blo 2181435 3274391 := bstep (se 1 (by rfl) ⟨2455793, by rfl⟩ : syracuseStep 3274391 = 4911587) B4911587
theorem B2182927 : Blo 2181435 2182927 := bstep (se 1 (by rfl) ⟨1637195, by rfl⟩ : syracuseStep 2182927 = 3274391) B3274391
theorem B3274397 : Blo 2181435 3274397 := bbase (se 3 (by rfl) ⟨613949, by rfl⟩ : syracuseStep 3274397 = 1227899) (by norm_num)
theorem B2182931 : Blo 2181435 2182931 := bstep (se 1 (by rfl) ⟨1637198, by rfl⟩ : syracuseStep 2182931 = 3274397) B3274397
theorem B4911605 : Blo 2181435 4911605 := bbase (se 5 (by rfl) ⟨230231, by rfl⟩ : syracuseStep 4911605 = 460463) (by norm_num)
theorem B3274403 : Blo 2181435 3274403 := bstep (se 1 (by rfl) ⟨2455802, by rfl⟩ : syracuseStep 3274403 = 4911605) B4911605
theorem B2182935 : Blo 2181435 2182935 := bstep (se 1 (by rfl) ⟨1637201, by rfl⟩ : syracuseStep 2182935 = 3274403) B3274403
theorem B3319085 : Blo 2181435 3319085 := bbase (se 3 (by rfl) ⟨622328, by rfl⟩ : syracuseStep 3319085 = 1244657) (by norm_num)
theorem B2212723 : Blo 2181435 2212723 := bstep (se 1 (by rfl) ⟨1659542, by rfl⟩ : syracuseStep 2212723 = 3319085) B3319085
theorem B11801189 : Blo 2181435 11801189 := bstep (se 4 (by rfl) ⟨1106361, by rfl⟩ : syracuseStep 11801189 = 2212723) B2212723
theorem B7867459 : Blo 2181435 7867459 := bstep (se 1 (by rfl) ⟨5900594, by rfl⟩ : syracuseStep 7867459 = 11801189) B11801189
theorem B41959781 : Blo 2181435 41959781 := bstep (se 4 (by rfl) ⟨3933729, by rfl⟩ : syracuseStep 41959781 = 7867459) B7867459
theorem B27973187 : Blo 2181435 27973187 := bstep (se 1 (by rfl) ⟨20979890, by rfl⟩ : syracuseStep 27973187 = 41959781) B41959781
theorem B18648791 : Blo 2181435 18648791 := bstep (se 1 (by rfl) ⟨13986593, by rfl⟩ : syracuseStep 18648791 = 27973187) B27973187
theorem B12432527 : Blo 2181435 12432527 := bstep (se 1 (by rfl) ⟨9324395, by rfl⟩ : syracuseStep 12432527 = 18648791) B18648791
theorem B8288351 : Blo 2181435 8288351 := bstep (se 1 (by rfl) ⟨6216263, by rfl⟩ : syracuseStep 8288351 = 12432527) B12432527
theorem B5525567 : Blo 2181435 5525567 := bstep (se 1 (by rfl) ⟨4144175, by rfl⟩ : syracuseStep 5525567 = 8288351) B8288351
theorem B3683711 : Blo 2181435 3683711 := bstep (se 1 (by rfl) ⟨2762783, by rfl⟩ : syracuseStep 3683711 = 5525567) B5525567
theorem B2455807 : Blo 2181435 2455807 := bstep (se 1 (by rfl) ⟨1841855, by rfl⟩ : syracuseStep 2455807 = 3683711) B3683711
theorem B3274409 : Blo 2181435 3274409 := bstep (se 2 (by rfl) ⟨1227903, by rfl⟩ : syracuseStep 3274409 = 2455807) B2455807
theorem B2182939 : Blo 2181435 2182939 := bstep (se 1 (by rfl) ⟨1637204, by rfl⟩ : syracuseStep 2182939 = 3274409) B3274409
theorem B7088725 : Blo 2181435 7088725 := bbase (se 8 (by rfl) ⟨41535, by rfl⟩ : syracuseStep 7088725 = 83071) (by norm_num)
theorem B37806533 : Blo 2181435 37806533 := bstep (se 4 (by rfl) ⟨3544362, by rfl⟩ : syracuseStep 37806533 = 7088725) B7088725
theorem B25204355 : Blo 2181435 25204355 := bstep (se 1 (by rfl) ⟨18903266, by rfl⟩ : syracuseStep 25204355 = 37806533) B37806533
theorem B16802903 : Blo 2181435 16802903 := bstep (se 1 (by rfl) ⟨12602177, by rfl⟩ : syracuseStep 16802903 = 25204355) B25204355
theorem B11201935 : Blo 2181435 11201935 := bstep (se 1 (by rfl) ⟨8401451, by rfl⟩ : syracuseStep 11201935 = 16802903) B16802903
theorem B14935913 : Blo 2181435 14935913 := bstep (se 2 (by rfl) ⟨5600967, by rfl⟩ : syracuseStep 14935913 = 11201935) B11201935
theorem B9957275 : Blo 2181435 9957275 := bstep (se 1 (by rfl) ⟨7467956, by rfl⟩ : syracuseStep 9957275 = 14935913) B14935913
theorem B6638183 : Blo 2181435 6638183 := bstep (se 1 (by rfl) ⟨4978637, by rfl⟩ : syracuseStep 6638183 = 9957275) B9957275
theorem B4425455 : Blo 2181435 4425455 := bstep (se 1 (by rfl) ⟨3319091, by rfl⟩ : syracuseStep 4425455 = 6638183) B6638183
theorem B11801213 : Blo 2181435 11801213 := bstep (se 3 (by rfl) ⟨2212727, by rfl⟩ : syracuseStep 11801213 = 4425455) B4425455
theorem B7867475 : Blo 2181435 7867475 := bstep (se 1 (by rfl) ⟨5900606, by rfl⟩ : syracuseStep 7867475 = 11801213) B11801213
theorem B5244983 : Blo 2181435 5244983 := bstep (se 1 (by rfl) ⟨3933737, by rfl⟩ : syracuseStep 5244983 = 7867475) B7867475
theorem B3496655 : Blo 2181435 3496655 := bstep (se 1 (by rfl) ⟨2622491, by rfl⟩ : syracuseStep 3496655 = 5244983) B5244983
theorem B2331103 : Blo 2181435 2331103 := bstep (se 1 (by rfl) ⟨1748327, by rfl⟩ : syracuseStep 2331103 = 3496655) B3496655
theorem B3108137 : Blo 2181435 3108137 := bstep (se 2 (by rfl) ⟨1165551, by rfl⟩ : syracuseStep 3108137 = 2331103) B2331103
theorem B8288365 : Blo 2181435 8288365 := bstep (se 3 (by rfl) ⟨1554068, by rfl⟩ : syracuseStep 8288365 = 3108137) B3108137
theorem B11051153 : Blo 2181435 11051153 := bstep (se 2 (by rfl) ⟨4144182, by rfl⟩ : syracuseStep 11051153 = 8288365) B8288365
theorem B7367435 : Blo 2181435 7367435 := bstep (se 1 (by rfl) ⟨5525576, by rfl⟩ : syracuseStep 7367435 = 11051153) B11051153
theorem B4911623 : Blo 2181435 4911623 := bstep (se 1 (by rfl) ⟨3683717, by rfl⟩ : syracuseStep 4911623 = 7367435) B7367435
theorem B3274415 : Blo 2181435 3274415 := bstep (se 1 (by rfl) ⟨2455811, by rfl⟩ : syracuseStep 3274415 = 4911623) B4911623
theorem B2182943 : Blo 2181435 2182943 := bstep (se 1 (by rfl) ⟨1637207, by rfl⟩ : syracuseStep 2182943 = 3274415) B3274415
theorem B3274421 : Blo 2181435 3274421 := bbase (se 5 (by rfl) ⟨153488, by rfl⟩ : syracuseStep 3274421 = 306977) (by norm_num)
theorem B2182947 : Blo 2181435 2182947 := bstep (se 1 (by rfl) ⟨1637210, by rfl⟩ : syracuseStep 2182947 = 3274421) B3274421
theorem B5525597 : Blo 2181435 5525597 := bbase (se 3 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 5525597 = 2072099) (by norm_num)
theorem B3683731 : Blo 2181435 3683731 := bstep (se 1 (by rfl) ⟨2762798, by rfl⟩ : syracuseStep 3683731 = 5525597) B5525597
theorem B4911641 : Blo 2181435 4911641 := bstep (se 2 (by rfl) ⟨1841865, by rfl⟩ : syracuseStep 4911641 = 3683731) B3683731
theorem B3274427 : Blo 2181435 3274427 := bstep (se 1 (by rfl) ⟨2455820, by rfl⟩ : syracuseStep 3274427 = 4911641) B4911641
theorem B2182951 : Blo 2181435 2182951 := bstep (se 1 (by rfl) ⟨1637213, by rfl⟩ : syracuseStep 2182951 = 3274427) B3274427
theorem B2455825 : Blo 2181435 2455825 := bbase (se 2 (by rfl) ⟨920934, by rfl⟩ : syracuseStep 2455825 = 1841869) (by norm_num)
theorem B3274433 : Blo 2181435 3274433 := bstep (se 2 (by rfl) ⟨1227912, by rfl⟩ : syracuseStep 3274433 = 2455825) B2455825
theorem B2182955 : Blo 2181435 2182955 := bstep (se 1 (by rfl) ⟨1637216, by rfl⟩ : syracuseStep 2182955 = 3274433) B3274433
theorem B4144213 : Blo 2181435 4144213 := bbase (se 8 (by rfl) ⟨24282, by rfl⟩ : syracuseStep 4144213 = 48565) (by norm_num)
theorem B5525617 : Blo 2181435 5525617 := bstep (se 2 (by rfl) ⟨2072106, by rfl⟩ : syracuseStep 5525617 = 4144213) B4144213
theorem B7367489 : Blo 2181435 7367489 := bstep (se 2 (by rfl) ⟨2762808, by rfl⟩ : syracuseStep 7367489 = 5525617) B5525617
theorem B4911659 : Blo 2181435 4911659 := bstep (se 1 (by rfl) ⟨3683744, by rfl⟩ : syracuseStep 4911659 = 7367489) B7367489
theorem B3274439 : Blo 2181435 3274439 := bstep (se 1 (by rfl) ⟨2455829, by rfl⟩ : syracuseStep 3274439 = 4911659) B4911659
theorem B2182959 : Blo 2181435 2182959 := bstep (se 1 (by rfl) ⟨1637219, by rfl⟩ : syracuseStep 2182959 = 3274439) B3274439
theorem B3274445 : Blo 2181435 3274445 := bbase (se 3 (by rfl) ⟨613958, by rfl⟩ : syracuseStep 3274445 = 1227917) (by norm_num)
theorem B2182963 : Blo 2181435 2182963 := bstep (se 1 (by rfl) ⟨1637222, by rfl⟩ : syracuseStep 2182963 = 3274445) B3274445
theorem B4911677 : Blo 2181435 4911677 := bbase (se 3 (by rfl) ⟨920939, by rfl⟩ : syracuseStep 4911677 = 1841879) (by norm_num)
theorem B3274451 : Blo 2181435 3274451 := bstep (se 1 (by rfl) ⟨2455838, by rfl⟩ : syracuseStep 3274451 = 4911677) B4911677
theorem B2182967 : Blo 2181435 2182967 := bstep (se 1 (by rfl) ⟨1637225, by rfl⟩ : syracuseStep 2182967 = 3274451) B3274451
theorem B3683765 : Blo 2181435 3683765 := bbase (se 5 (by rfl) ⟨172676, by rfl⟩ : syracuseStep 3683765 = 345353) (by norm_num)
theorem B2455843 : Blo 2181435 2455843 := bstep (se 1 (by rfl) ⟨1841882, by rfl⟩ : syracuseStep 2455843 = 3683765) B3683765
theorem B3274457 : Blo 2181435 3274457 := bstep (se 2 (by rfl) ⟨1227921, by rfl⟩ : syracuseStep 3274457 = 2455843) B2455843
theorem B2182971 : Blo 2181435 2182971 := bstep (se 1 (by rfl) ⟨1637228, by rfl⟩ : syracuseStep 2182971 = 3274457) B3274457
theorem B2331137 : Blo 2181435 2331137 := bbase (se 2 (by rfl) ⟨874176, by rfl⟩ : syracuseStep 2331137 = 1748353) (by norm_num)
theorem B6216365 : Blo 2181435 6216365 := bstep (se 3 (by rfl) ⟨1165568, by rfl⟩ : syracuseStep 6216365 = 2331137) B2331137
theorem B16576973 : Blo 2181435 16576973 := bstep (se 3 (by rfl) ⟨3108182, by rfl⟩ : syracuseStep 16576973 = 6216365) B6216365
theorem B11051315 : Blo 2181435 11051315 := bstep (se 1 (by rfl) ⟨8288486, by rfl⟩ : syracuseStep 11051315 = 16576973) B16576973
theorem B7367543 : Blo 2181435 7367543 := bstep (se 1 (by rfl) ⟨5525657, by rfl⟩ : syracuseStep 7367543 = 11051315) B11051315
theorem B4911695 : Blo 2181435 4911695 := bstep (se 1 (by rfl) ⟨3683771, by rfl⟩ : syracuseStep 4911695 = 7367543) B7367543
theorem B3274463 : Blo 2181435 3274463 := bstep (se 1 (by rfl) ⟨2455847, by rfl⟩ : syracuseStep 3274463 = 4911695) B4911695
theorem B2182975 : Blo 2181435 2182975 := bstep (se 1 (by rfl) ⟨1637231, by rfl⟩ : syracuseStep 2182975 = 3274463) B3274463
theorem B3274469 : Blo 2181435 3274469 := bbase (se 4 (by rfl) ⟨306981, by rfl⟩ : syracuseStep 3274469 = 613963) (by norm_num)
theorem B2182979 : Blo 2181435 2182979 := bstep (se 1 (by rfl) ⟨1637234, by rfl⟩ : syracuseStep 2182979 = 3274469) B3274469
theorem B6216389 : Blo 2181435 6216389 := bbase (se 4 (by rfl) ⟨582786, by rfl⟩ : syracuseStep 6216389 = 1165573) (by norm_num)
theorem B4144259 : Blo 2181435 4144259 := bstep (se 1 (by rfl) ⟨3108194, by rfl⟩ : syracuseStep 4144259 = 6216389) B6216389
theorem B2762839 : Blo 2181435 2762839 := bstep (se 1 (by rfl) ⟨2072129, by rfl⟩ : syracuseStep 2762839 = 4144259) B4144259
theorem B3683785 : Blo 2181435 3683785 := bstep (se 2 (by rfl) ⟨1381419, by rfl⟩ : syracuseStep 3683785 = 2762839) B2762839
theorem B4911713 : Blo 2181435 4911713 := bstep (se 2 (by rfl) ⟨1841892, by rfl⟩ : syracuseStep 4911713 = 3683785) B3683785
theorem B3274475 : Blo 2181435 3274475 := bstep (se 1 (by rfl) ⟨2455856, by rfl⟩ : syracuseStep 3274475 = 4911713) B4911713
theorem B2182983 : Blo 2181435 2182983 := bstep (se 1 (by rfl) ⟨1637237, by rfl⟩ : syracuseStep 2182983 = 3274475) B3274475
theorem B2455861 : Blo 2181435 2455861 := bbase (se 5 (by rfl) ⟨115118, by rfl⟩ : syracuseStep 2455861 = 230237) (by norm_num)
theorem B3274481 : Blo 2181435 3274481 := bstep (se 2 (by rfl) ⟨1227930, by rfl⟩ : syracuseStep 3274481 = 2455861) B2455861
theorem B2182987 : Blo 2181435 2182987 := bstep (se 1 (by rfl) ⟨1637240, by rfl⟩ : syracuseStep 2182987 = 3274481) B3274481
theorem B2762849 : Blo 2181435 2762849 := bbase (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) (by norm_num)
theorem B7367597 : Blo 2181435 7367597 := bstep (se 3 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 7367597 = 2762849) B2762849
theorem B4911731 : Blo 2181435 4911731 := bstep (se 1 (by rfl) ⟨3683798, by rfl⟩ : syracuseStep 4911731 = 7367597) B7367597
theorem B3274487 : Blo 2181435 3274487 := bstep (se 1 (by rfl) ⟨2455865, by rfl⟩ : syracuseStep 3274487 = 4911731) B4911731
theorem B2182991 : Blo 2181435 2182991 := bstep (se 1 (by rfl) ⟨1637243, by rfl⟩ : syracuseStep 2182991 = 3274487) B3274487
theorem B3274493 : Blo 2181435 3274493 := bbase (se 3 (by rfl) ⟨613967, by rfl⟩ : syracuseStep 3274493 = 1227935) (by norm_num)
theorem B2182995 : Blo 2181435 2182995 := bstep (se 1 (by rfl) ⟨1637246, by rfl⟩ : syracuseStep 2182995 = 3274493) B3274493
theorem B4911749 : Blo 2181435 4911749 := bbase (se 4 (by rfl) ⟨460476, by rfl⟩ : syracuseStep 4911749 = 920953) (by norm_num)
theorem B3274499 : Blo 2181435 3274499 := bstep (se 1 (by rfl) ⟨2455874, by rfl⟩ : syracuseStep 3274499 = 4911749) B4911749
theorem B2182999 : Blo 2181435 2182999 := bstep (se 1 (by rfl) ⟨1637249, by rfl⟩ : syracuseStep 2182999 = 3274499) B3274499
theorem B2800561 : Blo 2181435 2800561 := bbase (se 2 (by rfl) ⟨1050210, by rfl⟩ : syracuseStep 2800561 = 2100421) (by norm_num)
theorem B3734081 : Blo 2181435 3734081 := bstep (se 2 (by rfl) ⟨1400280, by rfl⟩ : syracuseStep 3734081 = 2800561) B2800561
theorem B2489387 : Blo 2181435 2489387 := bstep (se 1 (by rfl) ⟨1867040, by rfl⟩ : syracuseStep 2489387 = 3734081) B3734081
theorem B6638365 : Blo 2181435 6638365 := bstep (se 3 (by rfl) ⟨1244693, by rfl⟩ : syracuseStep 6638365 = 2489387) B2489387
theorem B35404613 : Blo 2181435 35404613 := bstep (se 4 (by rfl) ⟨3319182, by rfl⟩ : syracuseStep 35404613 = 6638365) B6638365
theorem B23603075 : Blo 2181435 23603075 := bstep (se 1 (by rfl) ⟨17702306, by rfl⟩ : syracuseStep 23603075 = 35404613) B35404613
theorem B15735383 : Blo 2181435 15735383 := bstep (se 1 (by rfl) ⟨11801537, by rfl⟩ : syracuseStep 15735383 = 23603075) B23603075
theorem B10490255 : Blo 2181435 10490255 := bstep (se 1 (by rfl) ⟨7867691, by rfl⟩ : syracuseStep 10490255 = 15735383) B15735383
theorem B6993503 : Blo 2181435 6993503 := bstep (se 1 (by rfl) ⟨5245127, by rfl⟩ : syracuseStep 6993503 = 10490255) B10490255
theorem B4662335 : Blo 2181435 4662335 := bstep (se 1 (by rfl) ⟨3496751, by rfl⟩ : syracuseStep 4662335 = 6993503) B6993503
theorem B3108223 : Blo 2181435 3108223 := bstep (se 1 (by rfl) ⟨2331167, by rfl⟩ : syracuseStep 3108223 = 4662335) B4662335
theorem B4144297 : Blo 2181435 4144297 := bstep (se 2 (by rfl) ⟨1554111, by rfl⟩ : syracuseStep 4144297 = 3108223) B3108223
theorem B5525729 : Blo 2181435 5525729 := bstep (se 2 (by rfl) ⟨2072148, by rfl⟩ : syracuseStep 5525729 = 4144297) B4144297
theorem B3683819 : Blo 2181435 3683819 := bstep (se 1 (by rfl) ⟨2762864, by rfl⟩ : syracuseStep 3683819 = 5525729) B5525729
theorem B2455879 : Blo 2181435 2455879 := bstep (se 1 (by rfl) ⟨1841909, by rfl⟩ : syracuseStep 2455879 = 3683819) B3683819
theorem B3274505 : Blo 2181435 3274505 := bstep (se 2 (by rfl) ⟨1227939, by rfl⟩ : syracuseStep 3274505 = 2455879) B2455879
theorem B2183003 : Blo 2181435 2183003 := bstep (se 1 (by rfl) ⟨1637252, by rfl⟩ : syracuseStep 2183003 = 3274505) B3274505
theorem B11051477 : Blo 2181435 11051477 := bbase (se 7 (by rfl) ⟨129509, by rfl⟩ : syracuseStep 11051477 = 259019) (by norm_num)
theorem B7367651 : Blo 2181435 7367651 := bstep (se 1 (by rfl) ⟨5525738, by rfl⟩ : syracuseStep 7367651 = 11051477) B11051477
theorem B4911767 : Blo 2181435 4911767 := bstep (se 1 (by rfl) ⟨3683825, by rfl⟩ : syracuseStep 4911767 = 7367651) B7367651
theorem B3274511 : Blo 2181435 3274511 := bstep (se 1 (by rfl) ⟨2455883, by rfl⟩ : syracuseStep 3274511 = 4911767) B4911767
theorem B2183007 : Blo 2181435 2183007 := bstep (se 1 (by rfl) ⟨1637255, by rfl⟩ : syracuseStep 2183007 = 3274511) B3274511
theorem B3274517 : Blo 2181435 3274517 := bbase (se 6 (by rfl) ⟨76746, by rfl⟩ : syracuseStep 3274517 = 153493) (by norm_num)
theorem B2183011 : Blo 2181435 2183011 := bstep (se 1 (by rfl) ⟨1637258, by rfl⟩ : syracuseStep 2183011 = 3274517) B3274517
theorem B3592837 : Blo 2181435 3592837 := bbase (se 4 (by rfl) ⟨336828, by rfl⟩ : syracuseStep 3592837 = 673657) (by norm_num)
theorem B4790449 : Blo 2181435 4790449 := bstep (se 2 (by rfl) ⟨1796418, by rfl⟩ : syracuseStep 4790449 = 3592837) B3592837
theorem B6387265 : Blo 2181435 6387265 := bstep (se 2 (by rfl) ⟨2395224, by rfl⟩ : syracuseStep 6387265 = 4790449) B4790449
theorem B8516353 : Blo 2181435 8516353 := bstep (se 2 (by rfl) ⟨3193632, by rfl⟩ : syracuseStep 8516353 = 6387265) B6387265
theorem B11355137 : Blo 2181435 11355137 := bstep (se 2 (by rfl) ⟨4258176, by rfl⟩ : syracuseStep 11355137 = 8516353) B8516353
theorem B7570091 : Blo 2181435 7570091 := bstep (se 1 (by rfl) ⟨5677568, by rfl⟩ : syracuseStep 7570091 = 11355137) B11355137
theorem B20186909 : Blo 2181435 20186909 := bstep (se 3 (by rfl) ⟨3785045, by rfl⟩ : syracuseStep 20186909 = 7570091) B7570091
theorem B13457939 : Blo 2181435 13457939 := bstep (se 1 (by rfl) ⟨10093454, by rfl⟩ : syracuseStep 13457939 = 20186909) B20186909
theorem B143551349 : Blo 2181435 143551349 := bstep (se 5 (by rfl) ⟨6728969, by rfl⟩ : syracuseStep 143551349 = 13457939) B13457939
theorem B95700899 : Blo 2181435 95700899 := bstep (se 1 (by rfl) ⟨71775674, by rfl⟩ : syracuseStep 95700899 = 143551349) B143551349
theorem B255202397 : Blo 2181435 255202397 := bstep (se 3 (by rfl) ⟨47850449, by rfl⟩ : syracuseStep 255202397 = 95700899) B95700899
theorem B170134931 : Blo 2181435 170134931 := bstep (se 1 (by rfl) ⟨127601198, by rfl⟩ : syracuseStep 170134931 = 255202397) B255202397
theorem B113423287 : Blo 2181435 113423287 := bstep (se 1 (by rfl) ⟨85067465, by rfl⟩ : syracuseStep 113423287 = 170134931) B170134931
theorem B151231049 : Blo 2181435 151231049 := bstep (se 2 (by rfl) ⟨56711643, by rfl⟩ : syracuseStep 151231049 = 113423287) B113423287
theorem B100820699 : Blo 2181435 100820699 := bstep (se 1 (by rfl) ⟨75615524, by rfl⟩ : syracuseStep 100820699 = 151231049) B151231049
theorem B67213799 : Blo 2181435 67213799 := bstep (se 1 (by rfl) ⟨50410349, by rfl⟩ : syracuseStep 67213799 = 100820699) B100820699
theorem B44809199 : Blo 2181435 44809199 := bstep (se 1 (by rfl) ⟨33606899, by rfl⟩ : syracuseStep 44809199 = 67213799) B67213799
theorem B29872799 : Blo 2181435 29872799 := bstep (se 1 (by rfl) ⟨22404599, by rfl⟩ : syracuseStep 29872799 = 44809199) B44809199
theorem B19915199 : Blo 2181435 19915199 := bstep (se 1 (by rfl) ⟨14936399, by rfl⟩ : syracuseStep 19915199 = 29872799) B29872799
theorem B13276799 : Blo 2181435 13276799 := bstep (se 1 (by rfl) ⟨9957599, by rfl⟩ : syracuseStep 13276799 = 19915199) B19915199
theorem B8851199 : Blo 2181435 8851199 := bstep (se 1 (by rfl) ⟨6638399, by rfl⟩ : syracuseStep 8851199 = 13276799) B13276799
theorem B94412789 : Blo 2181435 94412789 := bstep (se 5 (by rfl) ⟨4425599, by rfl⟩ : syracuseStep 94412789 = 8851199) B8851199
theorem B62941859 : Blo 2181435 62941859 := bstep (se 1 (by rfl) ⟨47206394, by rfl⟩ : syracuseStep 62941859 = 94412789) B94412789
theorem B41961239 : Blo 2181435 41961239 := bstep (se 1 (by rfl) ⟨31470929, by rfl⟩ : syracuseStep 41961239 = 62941859) B62941859
theorem B27974159 : Blo 2181435 27974159 := bstep (se 1 (by rfl) ⟨20980619, by rfl⟩ : syracuseStep 27974159 = 41961239) B41961239
theorem B18649439 : Blo 2181435 18649439 := bstep (se 1 (by rfl) ⟨13987079, by rfl⟩ : syracuseStep 18649439 = 27974159) B27974159
theorem B12432959 : Blo 2181435 12432959 := bstep (se 1 (by rfl) ⟨9324719, by rfl⟩ : syracuseStep 12432959 = 18649439) B18649439
theorem B8288639 : Blo 2181435 8288639 := bstep (se 1 (by rfl) ⟨6216479, by rfl⟩ : syracuseStep 8288639 = 12432959) B12432959
theorem B5525759 : Blo 2181435 5525759 := bstep (se 1 (by rfl) ⟨4144319, by rfl⟩ : syracuseStep 5525759 = 8288639) B8288639
theorem B3683839 : Blo 2181435 3683839 := bstep (se 1 (by rfl) ⟨2762879, by rfl⟩ : syracuseStep 3683839 = 5525759) B5525759
theorem B4911785 : Blo 2181435 4911785 := bstep (se 2 (by rfl) ⟨1841919, by rfl⟩ : syracuseStep 4911785 = 3683839) B3683839
theorem B3274523 : Blo 2181435 3274523 := bstep (se 1 (by rfl) ⟨2455892, by rfl⟩ : syracuseStep 3274523 = 4911785) B4911785
theorem B2183015 : Blo 2181435 2183015 := bstep (se 1 (by rfl) ⟨1637261, by rfl⟩ : syracuseStep 2183015 = 3274523) B3274523
theorem B2455897 : Blo 2181435 2455897 := bbase (se 2 (by rfl) ⟨920961, by rfl⟩ : syracuseStep 2455897 = 1841923) (by norm_num)
theorem B3274529 : Blo 2181435 3274529 := bstep (se 2 (by rfl) ⟨1227948, by rfl⟩ : syracuseStep 3274529 = 2455897) B2455897
theorem B2183019 : Blo 2181435 2183019 := bstep (se 1 (by rfl) ⟨1637264, by rfl⟩ : syracuseStep 2183019 = 3274529) B3274529
theorem B3319213 : Blo 2181435 3319213 := bbase (se 3 (by rfl) ⟨622352, by rfl⟩ : syracuseStep 3319213 = 1244705) (by norm_num)
theorem B4425617 : Blo 2181435 4425617 := bstep (se 2 (by rfl) ⟨1659606, by rfl⟩ : syracuseStep 4425617 = 3319213) B3319213
theorem B11801645 : Blo 2181435 11801645 := bstep (se 3 (by rfl) ⟨2212808, by rfl⟩ : syracuseStep 11801645 = 4425617) B4425617
theorem B7867763 : Blo 2181435 7867763 := bstep (se 1 (by rfl) ⟨5900822, by rfl⟩ : syracuseStep 7867763 = 11801645) B11801645
theorem B5245175 : Blo 2181435 5245175 := bstep (se 1 (by rfl) ⟨3933881, by rfl⟩ : syracuseStep 5245175 = 7867763) B7867763
theorem B3496783 : Blo 2181435 3496783 := bstep (se 1 (by rfl) ⟨2622587, by rfl⟩ : syracuseStep 3496783 = 5245175) B5245175
theorem B4662377 : Blo 2181435 4662377 := bstep (se 2 (by rfl) ⟨1748391, by rfl⟩ : syracuseStep 4662377 = 3496783) B3496783
theorem B3108251 : Blo 2181435 3108251 := bstep (se 1 (by rfl) ⟨2331188, by rfl⟩ : syracuseStep 3108251 = 4662377) B4662377
theorem B8288669 : Blo 2181435 8288669 := bstep (se 3 (by rfl) ⟨1554125, by rfl⟩ : syracuseStep 8288669 = 3108251) B3108251
theorem B5525779 : Blo 2181435 5525779 := bstep (se 1 (by rfl) ⟨4144334, by rfl⟩ : syracuseStep 5525779 = 8288669) B8288669
theorem B7367705 : Blo 2181435 7367705 := bstep (se 2 (by rfl) ⟨2762889, by rfl⟩ : syracuseStep 7367705 = 5525779) B5525779
theorem B4911803 : Blo 2181435 4911803 := bstep (se 1 (by rfl) ⟨3683852, by rfl⟩ : syracuseStep 4911803 = 7367705) B7367705
theorem B3274535 : Blo 2181435 3274535 := bstep (se 1 (by rfl) ⟨2455901, by rfl⟩ : syracuseStep 3274535 = 4911803) B4911803
theorem B2183023 : Blo 2181435 2183023 := bstep (se 1 (by rfl) ⟨1637267, by rfl⟩ : syracuseStep 2183023 = 3274535) B3274535
theorem B3274541 : Blo 2181435 3274541 := bbase (se 3 (by rfl) ⟨613976, by rfl⟩ : syracuseStep 3274541 = 1227953) (by norm_num)
theorem B2183027 : Blo 2181435 2183027 := bstep (se 1 (by rfl) ⟨1637270, by rfl⟩ : syracuseStep 2183027 = 3274541) B3274541
theorem B4911821 : Blo 2181435 4911821 := bbase (se 3 (by rfl) ⟨920966, by rfl⟩ : syracuseStep 4911821 = 1841933) (by norm_num)
theorem B3274547 : Blo 2181435 3274547 := bstep (se 1 (by rfl) ⟨2455910, by rfl⟩ : syracuseStep 3274547 = 4911821) B4911821
theorem B2183031 : Blo 2181435 2183031 := bstep (se 1 (by rfl) ⟨1637273, by rfl⟩ : syracuseStep 2183031 = 3274547) B3274547
theorem B2762905 : Blo 2181435 2762905 := bbase (se 2 (by rfl) ⟨1036089, by rfl⟩ : syracuseStep 2762905 = 2072179) (by norm_num)
theorem B3683873 : Blo 2181435 3683873 := bstep (se 2 (by rfl) ⟨1381452, by rfl⟩ : syracuseStep 3683873 = 2762905) B2762905
theorem B2455915 : Blo 2181435 2455915 := bstep (se 1 (by rfl) ⟨1841936, by rfl⟩ : syracuseStep 2455915 = 3683873) B3683873
theorem B3274553 : Blo 2181435 3274553 := bstep (se 2 (by rfl) ⟨1227957, by rfl⟩ : syracuseStep 3274553 = 2455915) B2455915
theorem B2183035 : Blo 2181435 2183035 := bstep (se 1 (by rfl) ⟨1637276, by rfl⟩ : syracuseStep 2183035 = 3274553) B3274553
theorem B9324821 : Blo 2181435 9324821 := bbase (se 6 (by rfl) ⟨218550, by rfl⟩ : syracuseStep 9324821 = 437101) (by norm_num)
theorem B24866189 : Blo 2181435 24866189 := bstep (se 3 (by rfl) ⟨4662410, by rfl⟩ : syracuseStep 24866189 = 9324821) B9324821
theorem B16577459 : Blo 2181435 16577459 := bstep (se 1 (by rfl) ⟨12433094, by rfl⟩ : syracuseStep 16577459 = 24866189) B24866189
theorem B11051639 : Blo 2181435 11051639 := bstep (se 1 (by rfl) ⟨8288729, by rfl⟩ : syracuseStep 11051639 = 16577459) B16577459
theorem B7367759 : Blo 2181435 7367759 := bstep (se 1 (by rfl) ⟨5525819, by rfl⟩ : syracuseStep 7367759 = 11051639) B11051639
theorem B4911839 : Blo 2181435 4911839 := bstep (se 1 (by rfl) ⟨3683879, by rfl⟩ : syracuseStep 4911839 = 7367759) B7367759
theorem B3274559 : Blo 2181435 3274559 := bstep (se 1 (by rfl) ⟨2455919, by rfl⟩ : syracuseStep 3274559 = 4911839) B4911839
theorem B2183039 : Blo 2181435 2183039 := bstep (se 1 (by rfl) ⟨1637279, by rfl⟩ : syracuseStep 2183039 = 3274559) B3274559
theorem B3274565 : Blo 2181435 3274565 := bbase (se 4 (by rfl) ⟨306990, by rfl⟩ : syracuseStep 3274565 = 613981) (by norm_num)
theorem B2183043 : Blo 2181435 2183043 := bstep (se 1 (by rfl) ⟨1637282, by rfl⟩ : syracuseStep 2183043 = 3274565) B3274565
theorem B3683893 : Blo 2181435 3683893 := bbase (se 5 (by rfl) ⟨172682, by rfl⟩ : syracuseStep 3683893 = 345365) (by norm_num)
theorem B4911857 : Blo 2181435 4911857 := bstep (se 2 (by rfl) ⟨1841946, by rfl⟩ : syracuseStep 4911857 = 3683893) B3683893
theorem B3274571 : Blo 2181435 3274571 := bstep (se 1 (by rfl) ⟨2455928, by rfl⟩ : syracuseStep 3274571 = 4911857) B4911857
theorem B2183047 : Blo 2181435 2183047 := bstep (se 1 (by rfl) ⟨1637285, by rfl⟩ : syracuseStep 2183047 = 3274571) B3274571
theorem B2455933 : Blo 2181435 2455933 := bbase (se 3 (by rfl) ⟨460487, by rfl⟩ : syracuseStep 2455933 = 920975) (by norm_num)
theorem B3274577 : Blo 2181435 3274577 := bstep (se 2 (by rfl) ⟨1227966, by rfl⟩ : syracuseStep 3274577 = 2455933) B2455933
theorem B2183051 : Blo 2181435 2183051 := bstep (se 1 (by rfl) ⟨1637288, by rfl⟩ : syracuseStep 2183051 = 3274577) B3274577
theorem B7367813 : Blo 2181435 7367813 := bbase (se 4 (by rfl) ⟨690732, by rfl⟩ : syracuseStep 7367813 = 1381465) (by norm_num)
theorem B4911875 : Blo 2181435 4911875 := bstep (se 1 (by rfl) ⟨3683906, by rfl⟩ : syracuseStep 4911875 = 7367813) B7367813
theorem B3274583 : Blo 2181435 3274583 := bstep (se 1 (by rfl) ⟨2455937, by rfl⟩ : syracuseStep 3274583 = 4911875) B4911875
theorem B2183055 : Blo 2181435 2183055 := bstep (se 1 (by rfl) ⟨1637291, by rfl⟩ : syracuseStep 2183055 = 3274583) B3274583
theorem B3274589 : Blo 2181435 3274589 := bbase (se 3 (by rfl) ⟨613985, by rfl⟩ : syracuseStep 3274589 = 1227971) (by norm_num)
theorem B2183059 : Blo 2181435 2183059 := bstep (se 1 (by rfl) ⟨1637294, by rfl⟩ : syracuseStep 2183059 = 3274589) B3274589
theorem B4911893 : Blo 2181435 4911893 := bbase (se 6 (by rfl) ⟨115122, by rfl⟩ : syracuseStep 4911893 = 230245) (by norm_num)
theorem B3274595 : Blo 2181435 3274595 := bstep (se 1 (by rfl) ⟨2455946, by rfl⟩ : syracuseStep 3274595 = 4911893) B4911893
theorem B2183063 : Blo 2181435 2183063 := bstep (se 1 (by rfl) ⟨1637297, by rfl⟩ : syracuseStep 2183063 = 3274595) B3274595
theorem B8288837 : Blo 2181435 8288837 := bbase (se 4 (by rfl) ⟨777078, by rfl⟩ : syracuseStep 8288837 = 1554157) (by norm_num)
theorem B5525891 : Blo 2181435 5525891 := bstep (se 1 (by rfl) ⟨4144418, by rfl⟩ : syracuseStep 5525891 = 8288837) B8288837
theorem B3683927 : Blo 2181435 3683927 := bstep (se 1 (by rfl) ⟨2762945, by rfl⟩ : syracuseStep 3683927 = 5525891) B5525891
theorem B2455951 : Blo 2181435 2455951 := bstep (se 1 (by rfl) ⟨1841963, by rfl⟩ : syracuseStep 2455951 = 3683927) B3683927
theorem B3274601 : Blo 2181435 3274601 := bstep (se 2 (by rfl) ⟨1227975, by rfl⟩ : syracuseStep 3274601 = 2455951) B2455951
theorem B2183067 : Blo 2181435 2183067 := bstep (se 1 (by rfl) ⟨1637300, by rfl⟩ : syracuseStep 2183067 = 3274601) B3274601
theorem B13277141 : Blo 2181435 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B8851427 : Blo 2181435 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B5900951 : Blo 2181435 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B15735869 : Blo 2181435 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B10490579 : Blo 2181435 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B6993719 : Blo 2181435 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B4662479 : Blo 2181435 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B12433277 : Blo 2181435 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B8288851 : Blo 2181435 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B11051801 : Blo 2181435 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B7367867 : Blo 2181435 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B4911911 : Blo 2181435 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B3274607 : Blo 2181435 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B2183071 : Blo 2181435 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B3274613 : Blo 2181435 3274613 := bbase (se 5 (by rfl) ⟨153497, by rfl⟩ : syracuseStep 3274613 = 306995) (by norm_num)
theorem B2183075 : Blo 2181435 2183075 := bstep (se 1 (by rfl) ⟨1637306, by rfl⟩ : syracuseStep 2183075 = 3274613) B3274613
theorem B5601317 : Blo 2181435 5601317 := bbase (se 4 (by rfl) ⟨525123, by rfl⟩ : syracuseStep 5601317 = 1050247) (by norm_num)
theorem B14936845 : Blo 2181435 14936845 := bstep (se 3 (by rfl) ⟨2800658, by rfl⟩ : syracuseStep 14936845 = 5601317) B5601317
theorem B19915793 : Blo 2181435 19915793 := bstep (se 2 (by rfl) ⟨7468422, by rfl⟩ : syracuseStep 19915793 = 14936845) B14936845
theorem B13277195 : Blo 2181435 13277195 := bstep (se 1 (by rfl) ⟨9957896, by rfl⟩ : syracuseStep 13277195 = 19915793) B19915793
theorem B8851463 : Blo 2181435 8851463 := bstep (se 1 (by rfl) ⟨6638597, by rfl⟩ : syracuseStep 8851463 = 13277195) B13277195
theorem B5900975 : Blo 2181435 5900975 := bstep (se 1 (by rfl) ⟨4425731, by rfl⟩ : syracuseStep 5900975 = 8851463) B8851463
theorem B3933983 : Blo 2181435 3933983 := bstep (se 1 (by rfl) ⟨2950487, by rfl⟩ : syracuseStep 3933983 = 5900975) B5900975
theorem B2622655 : Blo 2181435 2622655 := bstep (se 1 (by rfl) ⟨1966991, by rfl⟩ : syracuseStep 2622655 = 3933983) B3933983
theorem B3496873 : Blo 2181435 3496873 := bstep (se 2 (by rfl) ⟨1311327, by rfl⟩ : syracuseStep 3496873 = 2622655) B2622655
theorem B4662497 : Blo 2181435 4662497 := bstep (se 2 (by rfl) ⟨1748436, by rfl⟩ : syracuseStep 4662497 = 3496873) B3496873
theorem B3108331 : Blo 2181435 3108331 := bstep (se 1 (by rfl) ⟨2331248, by rfl⟩ : syracuseStep 3108331 = 4662497) B4662497
theorem B4144441 : Blo 2181435 4144441 := bstep (se 2 (by rfl) ⟨1554165, by rfl⟩ : syracuseStep 4144441 = 3108331) B3108331
theorem B5525921 : Blo 2181435 5525921 := bstep (se 2 (by rfl) ⟨2072220, by rfl⟩ : syracuseStep 5525921 = 4144441) B4144441
theorem B3683947 : Blo 2181435 3683947 := bstep (se 1 (by rfl) ⟨2762960, by rfl⟩ : syracuseStep 3683947 = 5525921) B5525921
theorem B4911929 : Blo 2181435 4911929 := bstep (se 2 (by rfl) ⟨1841973, by rfl⟩ : syracuseStep 4911929 = 3683947) B3683947
theorem B3274619 : Blo 2181435 3274619 := bstep (se 1 (by rfl) ⟨2455964, by rfl⟩ : syracuseStep 3274619 = 4911929) B4911929
theorem B2183079 : Blo 2181435 2183079 := bstep (se 1 (by rfl) ⟨1637309, by rfl⟩ : syracuseStep 2183079 = 3274619) B3274619
theorem B2455969 : Blo 2181435 2455969 := bbase (se 2 (by rfl) ⟨920988, by rfl⟩ : syracuseStep 2455969 = 1841977) (by norm_num)
theorem B3274625 : Blo 2181435 3274625 := bstep (se 2 (by rfl) ⟨1227984, by rfl⟩ : syracuseStep 3274625 = 2455969) B2455969
theorem B2183083 : Blo 2181435 2183083 := bstep (se 1 (by rfl) ⟨1637312, by rfl⟩ : syracuseStep 2183083 = 3274625) B3274625
theorem B5525941 : Blo 2181435 5525941 := bbase (se 5 (by rfl) ⟨259028, by rfl⟩ : syracuseStep 5525941 = 518057) (by norm_num)
theorem B7367921 : Blo 2181435 7367921 := bstep (se 2 (by rfl) ⟨2762970, by rfl⟩ : syracuseStep 7367921 = 5525941) B5525941
theorem B4911947 : Blo 2181435 4911947 := bstep (se 1 (by rfl) ⟨3683960, by rfl⟩ : syracuseStep 4911947 = 7367921) B7367921
theorem B3274631 : Blo 2181435 3274631 := bstep (se 1 (by rfl) ⟨2455973, by rfl⟩ : syracuseStep 3274631 = 4911947) B4911947
theorem B2183087 : Blo 2181435 2183087 := bstep (se 1 (by rfl) ⟨1637315, by rfl⟩ : syracuseStep 2183087 = 3274631) B3274631
theorem B3274637 : Blo 2181435 3274637 := bbase (se 3 (by rfl) ⟨613994, by rfl⟩ : syracuseStep 3274637 = 1227989) (by norm_num)
theorem B2183091 : Blo 2181435 2183091 := bstep (se 1 (by rfl) ⟨1637318, by rfl⟩ : syracuseStep 2183091 = 3274637) B3274637
theorem B4911965 : Blo 2181435 4911965 := bbase (se 3 (by rfl) ⟨920993, by rfl⟩ : syracuseStep 4911965 = 1841987) (by norm_num)
theorem B3274643 : Blo 2181435 3274643 := bstep (se 1 (by rfl) ⟨2455982, by rfl⟩ : syracuseStep 3274643 = 4911965) B4911965
theorem B2183095 : Blo 2181435 2183095 := bstep (se 1 (by rfl) ⟨1637321, by rfl⟩ : syracuseStep 2183095 = 3274643) B3274643
theorem B3683981 : Blo 2181435 3683981 := bbase (se 3 (by rfl) ⟨690746, by rfl⟩ : syracuseStep 3683981 = 1381493) (by norm_num)
theorem B2455987 : Blo 2181435 2455987 := bstep (se 1 (by rfl) ⟨1841990, by rfl⟩ : syracuseStep 2455987 = 3683981) B3683981
theorem B3274649 : Blo 2181435 3274649 := bstep (se 2 (by rfl) ⟨1227993, by rfl⟩ : syracuseStep 3274649 = 2455987) B2455987
theorem B2183099 : Blo 2181435 2183099 := bstep (se 1 (by rfl) ⟨1637324, by rfl⟩ : syracuseStep 2183099 = 3274649) B3274649
theorem B2489501 : Blo 2181435 2489501 := bbase (se 3 (by rfl) ⟨466781, by rfl⟩ : syracuseStep 2489501 = 933563) (by norm_num)
theorem B6638669 : Blo 2181435 6638669 := bstep (se 3 (by rfl) ⟨1244750, by rfl⟩ : syracuseStep 6638669 = 2489501) B2489501
theorem B4425779 : Blo 2181435 4425779 := bstep (se 1 (by rfl) ⟨3319334, by rfl⟩ : syracuseStep 4425779 = 6638669) B6638669
theorem B2950519 : Blo 2181435 2950519 := bstep (se 1 (by rfl) ⟨2212889, by rfl⟩ : syracuseStep 2950519 = 4425779) B4425779
theorem B3934025 : Blo 2181435 3934025 := bstep (se 2 (by rfl) ⟨1475259, by rfl⟩ : syracuseStep 3934025 = 2950519) B2950519
theorem B2622683 : Blo 2181435 2622683 := bstep (se 1 (by rfl) ⟨1967012, by rfl⟩ : syracuseStep 2622683 = 3934025) B3934025
theorem B6993821 : Blo 2181435 6993821 := bstep (se 3 (by rfl) ⟨1311341, by rfl⟩ : syracuseStep 6993821 = 2622683) B2622683
theorem B18650189 : Blo 2181435 18650189 := bstep (se 3 (by rfl) ⟨3496910, by rfl⟩ : syracuseStep 18650189 = 6993821) B6993821
theorem B12433459 : Blo 2181435 12433459 := bstep (se 1 (by rfl) ⟨9325094, by rfl⟩ : syracuseStep 12433459 = 18650189) B18650189
theorem B16577945 : Blo 2181435 16577945 := bstep (se 2 (by rfl) ⟨6216729, by rfl⟩ : syracuseStep 16577945 = 12433459) B12433459
theorem B11051963 : Blo 2181435 11051963 := bstep (se 1 (by rfl) ⟨8288972, by rfl⟩ : syracuseStep 11051963 = 16577945) B16577945
theorem B7367975 : Blo 2181435 7367975 := bstep (se 1 (by rfl) ⟨5525981, by rfl⟩ : syracuseStep 7367975 = 11051963) B11051963
theorem B4911983 : Blo 2181435 4911983 := bstep (se 1 (by rfl) ⟨3683987, by rfl⟩ : syracuseStep 4911983 = 7367975) B7367975
theorem B3274655 : Blo 2181435 3274655 := bstep (se 1 (by rfl) ⟨2455991, by rfl⟩ : syracuseStep 3274655 = 4911983) B4911983
theorem B2183103 : Blo 2181435 2183103 := bstep (se 1 (by rfl) ⟨1637327, by rfl⟩ : syracuseStep 2183103 = 3274655) B3274655
theorem B3274661 : Blo 2181435 3274661 := bbase (se 4 (by rfl) ⟨306999, by rfl⟩ : syracuseStep 3274661 = 613999) (by norm_num)
theorem B2183107 : Blo 2181435 2183107 := bstep (se 1 (by rfl) ⟨1637330, by rfl⟩ : syracuseStep 2183107 = 3274661) B3274661
theorem B2763001 : Blo 2181435 2763001 := bbase (se 2 (by rfl) ⟨1036125, by rfl⟩ : syracuseStep 2763001 = 2072251) (by norm_num)
theorem B3684001 : Blo 2181435 3684001 := bstep (se 2 (by rfl) ⟨1381500, by rfl⟩ : syracuseStep 3684001 = 2763001) B2763001
theorem B4912001 : Blo 2181435 4912001 := bstep (se 2 (by rfl) ⟨1842000, by rfl⟩ : syracuseStep 4912001 = 3684001) B3684001
theorem B3274667 : Blo 2181435 3274667 := bstep (se 1 (by rfl) ⟨2456000, by rfl⟩ : syracuseStep 3274667 = 4912001) B4912001
theorem B2183111 : Blo 2181435 2183111 := bstep (se 1 (by rfl) ⟨1637333, by rfl⟩ : syracuseStep 2183111 = 3274667) B3274667
theorem B2456005 : Blo 2181435 2456005 := bbase (se 4 (by rfl) ⟨230250, by rfl⟩ : syracuseStep 2456005 = 460501) (by norm_num)
theorem B3274673 : Blo 2181435 3274673 := bstep (se 2 (by rfl) ⟨1228002, by rfl⟩ : syracuseStep 3274673 = 2456005) B2456005
theorem B2183115 : Blo 2181435 2183115 := bstep (se 1 (by rfl) ⟨1637336, by rfl⟩ : syracuseStep 2183115 = 3274673) B3274673
theorem B4144517 : Blo 2181435 4144517 := bbase (se 4 (by rfl) ⟨388548, by rfl⟩ : syracuseStep 4144517 = 777097) (by norm_num)
theorem B2763011 : Blo 2181435 2763011 := bstep (se 1 (by rfl) ⟨2072258, by rfl⟩ : syracuseStep 2763011 = 4144517) B4144517
theorem B7368029 : Blo 2181435 7368029 := bstep (se 3 (by rfl) ⟨1381505, by rfl⟩ : syracuseStep 7368029 = 2763011) B2763011
theorem B4912019 : Blo 2181435 4912019 := bstep (se 1 (by rfl) ⟨3684014, by rfl⟩ : syracuseStep 4912019 = 7368029) B7368029
theorem B3274679 : Blo 2181435 3274679 := bstep (se 1 (by rfl) ⟨2456009, by rfl⟩ : syracuseStep 3274679 = 4912019) B4912019
theorem B2183119 : Blo 2181435 2183119 := bstep (se 1 (by rfl) ⟨1637339, by rfl⟩ : syracuseStep 2183119 = 3274679) B3274679
theorem B3274685 : Blo 2181435 3274685 := bbase (se 3 (by rfl) ⟨614003, by rfl⟩ : syracuseStep 3274685 = 1228007) (by norm_num)
theorem B2183123 : Blo 2181435 2183123 := bstep (se 1 (by rfl) ⟨1637342, by rfl⟩ : syracuseStep 2183123 = 3274685) B3274685
theorem B4912037 : Blo 2181435 4912037 := bbase (se 4 (by rfl) ⟨460503, by rfl⟩ : syracuseStep 4912037 = 921007) (by norm_num)
theorem B3274691 : Blo 2181435 3274691 := bstep (se 1 (by rfl) ⟨2456018, by rfl⟩ : syracuseStep 3274691 = 4912037) B4912037
theorem B2183127 : Blo 2181435 2183127 := bstep (se 1 (by rfl) ⟨1637345, by rfl⟩ : syracuseStep 2183127 = 3274691) B3274691
theorem B5526053 : Blo 2181435 5526053 := bbase (se 4 (by rfl) ⟨518067, by rfl⟩ : syracuseStep 5526053 = 1036135) (by norm_num)
theorem B3684035 : Blo 2181435 3684035 := bstep (se 1 (by rfl) ⟨2763026, by rfl⟩ : syracuseStep 3684035 = 5526053) B5526053
theorem B2456023 : Blo 2181435 2456023 := bstep (se 1 (by rfl) ⟨1842017, by rfl⟩ : syracuseStep 2456023 = 3684035) B3684035
theorem B3274697 : Blo 2181435 3274697 := bstep (se 2 (by rfl) ⟨1228011, by rfl⟩ : syracuseStep 3274697 = 2456023) B2456023
theorem B2183131 : Blo 2181435 2183131 := bstep (se 1 (by rfl) ⟨1637348, by rfl⟩ : syracuseStep 2183131 = 3274697) B3274697
theorem B6216821 : Blo 2181435 6216821 := bbase (se 5 (by rfl) ⟨291413, by rfl⟩ : syracuseStep 6216821 = 582827) (by norm_num)
theorem B4144547 : Blo 2181435 4144547 := bstep (se 1 (by rfl) ⟨3108410, by rfl⟩ : syracuseStep 4144547 = 6216821) B6216821
theorem B11052125 : Blo 2181435 11052125 := bstep (se 3 (by rfl) ⟨2072273, by rfl⟩ : syracuseStep 11052125 = 4144547) B4144547
theorem B7368083 : Blo 2181435 7368083 := bstep (se 1 (by rfl) ⟨5526062, by rfl⟩ : syracuseStep 7368083 = 11052125) B11052125
theorem B4912055 : Blo 2181435 4912055 := bstep (se 1 (by rfl) ⟨3684041, by rfl⟩ : syracuseStep 4912055 = 7368083) B7368083
theorem B3274703 : Blo 2181435 3274703 := bstep (se 1 (by rfl) ⟨2456027, by rfl⟩ : syracuseStep 3274703 = 4912055) B4912055
theorem B2183135 : Blo 2181435 2183135 := bstep (se 1 (by rfl) ⟨1637351, by rfl⟩ : syracuseStep 2183135 = 3274703) B3274703
theorem B3274709 : Blo 2181435 3274709 := bbase (se 7 (by rfl) ⟨38375, by rfl⟩ : syracuseStep 3274709 = 76751) (by norm_num)
theorem B2183139 : Blo 2181435 2183139 := bstep (se 1 (by rfl) ⟨1637354, by rfl⟩ : syracuseStep 2183139 = 3274709) B3274709
theorem B8289125 : Blo 2181435 8289125 := bbase (se 4 (by rfl) ⟨777105, by rfl⟩ : syracuseStep 8289125 = 1554211) (by norm_num)
theorem B5526083 : Blo 2181435 5526083 := bstep (se 1 (by rfl) ⟨4144562, by rfl⟩ : syracuseStep 5526083 = 8289125) B8289125
theorem B3684055 : Blo 2181435 3684055 := bstep (se 1 (by rfl) ⟨2763041, by rfl⟩ : syracuseStep 3684055 = 5526083) B5526083
theorem B4912073 : Blo 2181435 4912073 := bstep (se 2 (by rfl) ⟨1842027, by rfl⟩ : syracuseStep 4912073 = 3684055) B3684055
theorem B3274715 : Blo 2181435 3274715 := bstep (se 1 (by rfl) ⟨2456036, by rfl⟩ : syracuseStep 3274715 = 4912073) B4912073
theorem B2183143 : Blo 2181435 2183143 := bstep (se 1 (by rfl) ⟨1637357, by rfl⟩ : syracuseStep 2183143 = 3274715) B3274715
theorem B2456041 : Blo 2181435 2456041 := bbase (se 2 (by rfl) ⟨921015, by rfl⟩ : syracuseStep 2456041 = 1842031) (by norm_num)
theorem B3274721 : Blo 2181435 3274721 := bstep (se 2 (by rfl) ⟨1228020, by rfl⟩ : syracuseStep 3274721 = 2456041) B2456041
theorem B2183147 : Blo 2181435 2183147 := bstep (se 1 (by rfl) ⟨1637360, by rfl⟩ : syracuseStep 2183147 = 3274721) B3274721
theorem B2331325 : Blo 2181435 2331325 := bbase (se 3 (by rfl) ⟨437123, by rfl⟩ : syracuseStep 2331325 = 874247) (by norm_num)
theorem B12433733 : Blo 2181435 12433733 := bstep (se 4 (by rfl) ⟨1165662, by rfl⟩ : syracuseStep 12433733 = 2331325) B2331325
theorem B8289155 : Blo 2181435 8289155 := bstep (se 1 (by rfl) ⟨6216866, by rfl⟩ : syracuseStep 8289155 = 12433733) B12433733
theorem B5526103 : Blo 2181435 5526103 := bstep (se 1 (by rfl) ⟨4144577, by rfl⟩ : syracuseStep 5526103 = 8289155) B8289155
theorem B7368137 : Blo 2181435 7368137 := bstep (se 2 (by rfl) ⟨2763051, by rfl⟩ : syracuseStep 7368137 = 5526103) B5526103
theorem B4912091 : Blo 2181435 4912091 := bstep (se 1 (by rfl) ⟨3684068, by rfl⟩ : syracuseStep 4912091 = 7368137) B7368137
theorem B3274727 : Blo 2181435 3274727 := bstep (se 1 (by rfl) ⟨2456045, by rfl⟩ : syracuseStep 3274727 = 4912091) B4912091
theorem B2183151 : Blo 2181435 2183151 := bstep (se 1 (by rfl) ⟨1637363, by rfl⟩ : syracuseStep 2183151 = 3274727) B3274727
theorem B3274733 : Blo 2181435 3274733 := bbase (se 3 (by rfl) ⟨614012, by rfl⟩ : syracuseStep 3274733 = 1228025) (by norm_num)
theorem B2183155 : Blo 2181435 2183155 := bstep (se 1 (by rfl) ⟨1637366, by rfl⟩ : syracuseStep 2183155 = 3274733) B3274733
theorem B4912109 : Blo 2181435 4912109 := bbase (se 3 (by rfl) ⟨921020, by rfl⟩ : syracuseStep 4912109 = 1842041) (by norm_num)
theorem B3274739 : Blo 2181435 3274739 := bstep (se 1 (by rfl) ⟨2456054, by rfl⟩ : syracuseStep 3274739 = 4912109) B4912109
theorem B2183159 : Blo 2181435 2183159 := bstep (se 1 (by rfl) ⟨1637369, by rfl⟩ : syracuseStep 2183159 = 3274739) B3274739
theorem B4662677 : Blo 2181435 4662677 := bbase (se 6 (by rfl) ⟨109281, by rfl⟩ : syracuseStep 4662677 = 218563) (by norm_num)
theorem B3108451 : Blo 2181435 3108451 := bstep (se 1 (by rfl) ⟨2331338, by rfl⟩ : syracuseStep 3108451 = 4662677) B4662677
theorem B4144601 : Blo 2181435 4144601 := bstep (se 2 (by rfl) ⟨1554225, by rfl⟩ : syracuseStep 4144601 = 3108451) B3108451
theorem B2763067 : Blo 2181435 2763067 := bstep (se 1 (by rfl) ⟨2072300, by rfl⟩ : syracuseStep 2763067 = 4144601) B4144601
theorem B3684089 : Blo 2181435 3684089 := bstep (se 2 (by rfl) ⟨1381533, by rfl⟩ : syracuseStep 3684089 = 2763067) B2763067
theorem B2456059 : Blo 2181435 2456059 := bstep (se 1 (by rfl) ⟨1842044, by rfl⟩ : syracuseStep 2456059 = 3684089) B3684089
theorem B3274745 : Blo 2181435 3274745 := bstep (se 2 (by rfl) ⟨1228029, by rfl⟩ : syracuseStep 3274745 = 2456059) B2456059
theorem B2183163 : Blo 2181435 2183163 := bstep (se 1 (by rfl) ⟨1637372, by rfl⟩ : syracuseStep 2183163 = 3274745) B3274745
theorem B8402309 : Blo 2181435 8402309 := bbase (se 4 (by rfl) ⟨787716, by rfl⟩ : syracuseStep 8402309 = 1575433) (by norm_num)
theorem B5601539 : Blo 2181435 5601539 := bstep (se 1 (by rfl) ⟨4201154, by rfl⟩ : syracuseStep 5601539 = 8402309) B8402309
theorem B14937437 : Blo 2181435 14937437 := bstep (se 3 (by rfl) ⟨2800769, by rfl⟩ : syracuseStep 14937437 = 5601539) B5601539
theorem B9958291 : Blo 2181435 9958291 := bstep (se 1 (by rfl) ⟨7468718, by rfl⟩ : syracuseStep 9958291 = 14937437) B14937437
theorem B53110885 : Blo 2181435 53110885 := bstep (se 4 (by rfl) ⟨4979145, by rfl⟩ : syracuseStep 53110885 = 9958291) B9958291
theorem B70814513 : Blo 2181435 70814513 := bstep (se 2 (by rfl) ⟨26555442, by rfl⟩ : syracuseStep 70814513 = 53110885) B53110885
theorem B188838701 : Blo 2181435 188838701 := bstep (se 3 (by rfl) ⟨35407256, by rfl⟩ : syracuseStep 188838701 = 70814513) B70814513
theorem B125892467 : Blo 2181435 125892467 := bstep (se 1 (by rfl) ⟨94419350, by rfl⟩ : syracuseStep 125892467 = 188838701) B188838701
theorem B83928311 : Blo 2181435 83928311 := bstep (se 1 (by rfl) ⟨62946233, by rfl⟩ : syracuseStep 83928311 = 125892467) B125892467
theorem B55952207 : Blo 2181435 55952207 := bstep (se 1 (by rfl) ⟨41964155, by rfl⟩ : syracuseStep 55952207 = 83928311) B83928311
theorem B37301471 : Blo 2181435 37301471 := bstep (se 1 (by rfl) ⟨27976103, by rfl⟩ : syracuseStep 37301471 = 55952207) B55952207
theorem B24867647 : Blo 2181435 24867647 := bstep (se 1 (by rfl) ⟨18650735, by rfl⟩ : syracuseStep 24867647 = 37301471) B37301471
theorem B16578431 : Blo 2181435 16578431 := bstep (se 1 (by rfl) ⟨12433823, by rfl⟩ : syracuseStep 16578431 = 24867647) B24867647
theorem B11052287 : Blo 2181435 11052287 := bstep (se 1 (by rfl) ⟨8289215, by rfl⟩ : syracuseStep 11052287 = 16578431) B16578431
theorem B7368191 : Blo 2181435 7368191 := bstep (se 1 (by rfl) ⟨5526143, by rfl⟩ : syracuseStep 7368191 = 11052287) B11052287
theorem B4912127 : Blo 2181435 4912127 := bstep (se 1 (by rfl) ⟨3684095, by rfl⟩ : syracuseStep 4912127 = 7368191) B7368191
theorem B3274751 : Blo 2181435 3274751 := bstep (se 1 (by rfl) ⟨2456063, by rfl⟩ : syracuseStep 3274751 = 4912127) B4912127
theorem B2183167 : Blo 2181435 2183167 := bstep (se 1 (by rfl) ⟨1637375, by rfl⟩ : syracuseStep 2183167 = 3274751) B3274751
theorem B3274757 : Blo 2181435 3274757 := bbase (se 4 (by rfl) ⟨307008, by rfl⟩ : syracuseStep 3274757 = 614017) (by norm_num)
theorem B2183171 : Blo 2181435 2183171 := bstep (se 1 (by rfl) ⟨1637378, by rfl⟩ : syracuseStep 2183171 = 3274757) B3274757
theorem B3684109 : Blo 2181435 3684109 := bbase (se 3 (by rfl) ⟨690770, by rfl⟩ : syracuseStep 3684109 = 1381541) (by norm_num)
theorem B4912145 : Blo 2181435 4912145 := bstep (se 2 (by rfl) ⟨1842054, by rfl⟩ : syracuseStep 4912145 = 3684109) B3684109
theorem B3274763 : Blo 2181435 3274763 := bstep (se 1 (by rfl) ⟨2456072, by rfl⟩ : syracuseStep 3274763 = 4912145) B4912145
theorem B2183175 : Blo 2181435 2183175 := bstep (se 1 (by rfl) ⟨1637381, by rfl⟩ : syracuseStep 2183175 = 3274763) B3274763
theorem B2456077 : Blo 2181435 2456077 := bbase (se 3 (by rfl) ⟨460514, by rfl⟩ : syracuseStep 2456077 = 921029) (by norm_num)
theorem B3274769 : Blo 2181435 3274769 := bstep (se 2 (by rfl) ⟨1228038, by rfl⟩ : syracuseStep 3274769 = 2456077) B2456077
theorem B2183179 : Blo 2181435 2183179 := bstep (se 1 (by rfl) ⟨1637384, by rfl⟩ : syracuseStep 2183179 = 3274769) B3274769
theorem B7368245 : Blo 2181435 7368245 := bbase (se 5 (by rfl) ⟨345386, by rfl⟩ : syracuseStep 7368245 = 690773) (by norm_num)
theorem B4912163 : Blo 2181435 4912163 := bstep (se 1 (by rfl) ⟨3684122, by rfl⟩ : syracuseStep 4912163 = 7368245) B7368245
theorem B3274775 : Blo 2181435 3274775 := bstep (se 1 (by rfl) ⟨2456081, by rfl⟩ : syracuseStep 3274775 = 4912163) B4912163
theorem B2183183 : Blo 2181435 2183183 := bstep (se 1 (by rfl) ⟨1637387, by rfl⟩ : syracuseStep 2183183 = 3274775) B3274775
theorem B3274781 : Blo 2181435 3274781 := bbase (se 3 (by rfl) ⟨614021, by rfl⟩ : syracuseStep 3274781 = 1228043) (by norm_num)
theorem B2183187 : Blo 2181435 2183187 := bstep (se 1 (by rfl) ⟨1637390, by rfl⟩ : syracuseStep 2183187 = 3274781) B3274781
theorem B4912181 : Blo 2181435 4912181 := bbase (se 5 (by rfl) ⟨230258, by rfl⟩ : syracuseStep 4912181 = 460517) (by norm_num)
theorem B3274787 : Blo 2181435 3274787 := bstep (se 1 (by rfl) ⟨2456090, by rfl⟩ : syracuseStep 3274787 = 4912181) B4912181
theorem B2183191 : Blo 2181435 2183191 := bstep (se 1 (by rfl) ⟨1637393, by rfl⟩ : syracuseStep 2183191 = 3274787) B3274787
theorem B6994117 : Blo 2181435 6994117 := bbase (se 4 (by rfl) ⟨655698, by rfl⟩ : syracuseStep 6994117 = 1311397) (by norm_num)
theorem B9325489 : Blo 2181435 9325489 := bstep (se 2 (by rfl) ⟨3497058, by rfl⟩ : syracuseStep 9325489 = 6994117) B6994117
theorem B12433985 : Blo 2181435 12433985 := bstep (se 2 (by rfl) ⟨4662744, by rfl⟩ : syracuseStep 12433985 = 9325489) B9325489
theorem B8289323 : Blo 2181435 8289323 := bstep (se 1 (by rfl) ⟨6216992, by rfl⟩ : syracuseStep 8289323 = 12433985) B12433985
theorem B5526215 : Blo 2181435 5526215 := bstep (se 1 (by rfl) ⟨4144661, by rfl⟩ : syracuseStep 5526215 = 8289323) B8289323
theorem B3684143 : Blo 2181435 3684143 := bstep (se 1 (by rfl) ⟨2763107, by rfl⟩ : syracuseStep 3684143 = 5526215) B5526215
theorem B2456095 : Blo 2181435 2456095 := bstep (se 1 (by rfl) ⟨1842071, by rfl⟩ : syracuseStep 2456095 = 3684143) B3684143
theorem B3274793 : Blo 2181435 3274793 := bstep (se 2 (by rfl) ⟨1228047, by rfl⟩ : syracuseStep 3274793 = 2456095) B2456095
theorem B2183195 : Blo 2181435 2183195 := bstep (se 1 (by rfl) ⟨1637396, by rfl⟩ : syracuseStep 2183195 = 3274793) B3274793
theorem B5245597 : Blo 2181435 5245597 := bbase (se 3 (by rfl) ⟨983549, by rfl⟩ : syracuseStep 5245597 = 1967099) (by norm_num)
theorem B6994129 : Blo 2181435 6994129 := bstep (se 2 (by rfl) ⟨2622798, by rfl⟩ : syracuseStep 6994129 = 5245597) B5245597
theorem B9325505 : Blo 2181435 9325505 := bstep (se 2 (by rfl) ⟨3497064, by rfl⟩ : syracuseStep 9325505 = 6994129) B6994129
theorem B6217003 : Blo 2181435 6217003 := bstep (se 1 (by rfl) ⟨4662752, by rfl⟩ : syracuseStep 6217003 = 9325505) B9325505
theorem B8289337 : Blo 2181435 8289337 := bstep (se 2 (by rfl) ⟨3108501, by rfl⟩ : syracuseStep 8289337 = 6217003) B6217003
theorem B11052449 : Blo 2181435 11052449 := bstep (se 2 (by rfl) ⟨4144668, by rfl⟩ : syracuseStep 11052449 = 8289337) B8289337
theorem B7368299 : Blo 2181435 7368299 := bstep (se 1 (by rfl) ⟨5526224, by rfl⟩ : syracuseStep 7368299 = 11052449) B11052449
theorem B4912199 : Blo 2181435 4912199 := bstep (se 1 (by rfl) ⟨3684149, by rfl⟩ : syracuseStep 4912199 = 7368299) B7368299
theorem B3274799 : Blo 2181435 3274799 := bstep (se 1 (by rfl) ⟨2456099, by rfl⟩ : syracuseStep 3274799 = 4912199) B4912199
theorem B2183199 : Blo 2181435 2183199 := bstep (se 1 (by rfl) ⟨1637399, by rfl⟩ : syracuseStep 2183199 = 3274799) B3274799
theorem B3274805 : Blo 2181435 3274805 := bbase (se 5 (by rfl) ⟨153506, by rfl⟩ : syracuseStep 3274805 = 307013) (by norm_num)
theorem B2183203 : Blo 2181435 2183203 := bstep (se 1 (by rfl) ⟨1637402, by rfl⟩ : syracuseStep 2183203 = 3274805) B3274805
theorem B5526245 : Blo 2181435 5526245 := bbase (se 4 (by rfl) ⟨518085, by rfl⟩ : syracuseStep 5526245 = 1036171) (by norm_num)
theorem B3684163 : Blo 2181435 3684163 := bstep (se 1 (by rfl) ⟨2763122, by rfl⟩ : syracuseStep 3684163 = 5526245) B5526245
theorem B4912217 : Blo 2181435 4912217 := bstep (se 2 (by rfl) ⟨1842081, by rfl⟩ : syracuseStep 4912217 = 3684163) B3684163
theorem B3274811 : Blo 2181435 3274811 := bstep (se 1 (by rfl) ⟨2456108, by rfl⟩ : syracuseStep 3274811 = 4912217) B4912217
theorem B2183207 : Blo 2181435 2183207 := bstep (se 1 (by rfl) ⟨1637405, by rfl⟩ : syracuseStep 2183207 = 3274811) B3274811
theorem B2456113 : Blo 2181435 2456113 := bbase (se 2 (by rfl) ⟨921042, by rfl⟩ : syracuseStep 2456113 = 1842085) (by norm_num)
theorem B3274817 : Blo 2181435 3274817 := bstep (se 2 (by rfl) ⟨1228056, by rfl⟩ : syracuseStep 3274817 = 2456113) B2456113
theorem B2183211 : Blo 2181435 2183211 := bstep (se 1 (by rfl) ⟨1637408, by rfl⟩ : syracuseStep 2183211 = 3274817) B3274817
theorem B6994181 : Blo 2181435 6994181 := bbase (se 4 (by rfl) ⟨655704, by rfl⟩ : syracuseStep 6994181 = 1311409) (by norm_num)
theorem B4662787 : Blo 2181435 4662787 := bstep (se 1 (by rfl) ⟨3497090, by rfl⟩ : syracuseStep 4662787 = 6994181) B6994181
theorem B6217049 : Blo 2181435 6217049 := bstep (se 2 (by rfl) ⟨2331393, by rfl⟩ : syracuseStep 6217049 = 4662787) B4662787
theorem B4144699 : Blo 2181435 4144699 := bstep (se 1 (by rfl) ⟨3108524, by rfl⟩ : syracuseStep 4144699 = 6217049) B6217049
theorem B5526265 : Blo 2181435 5526265 := bstep (se 2 (by rfl) ⟨2072349, by rfl⟩ : syracuseStep 5526265 = 4144699) B4144699
theorem B7368353 : Blo 2181435 7368353 := bstep (se 2 (by rfl) ⟨2763132, by rfl⟩ : syracuseStep 7368353 = 5526265) B5526265
theorem B4912235 : Blo 2181435 4912235 := bstep (se 1 (by rfl) ⟨3684176, by rfl⟩ : syracuseStep 4912235 = 7368353) B7368353
theorem B3274823 : Blo 2181435 3274823 := bstep (se 1 (by rfl) ⟨2456117, by rfl⟩ : syracuseStep 3274823 = 4912235) B4912235
theorem B2183215 : Blo 2181435 2183215 := bstep (se 1 (by rfl) ⟨1637411, by rfl⟩ : syracuseStep 2183215 = 3274823) B3274823
theorem B3274829 : Blo 2181435 3274829 := bbase (se 3 (by rfl) ⟨614030, by rfl⟩ : syracuseStep 3274829 = 1228061) (by norm_num)
theorem B2183219 : Blo 2181435 2183219 := bstep (se 1 (by rfl) ⟨1637414, by rfl⟩ : syracuseStep 2183219 = 3274829) B3274829
theorem B4912253 : Blo 2181435 4912253 := bbase (se 3 (by rfl) ⟨921047, by rfl⟩ : syracuseStep 4912253 = 1842095) (by norm_num)
theorem B3274835 : Blo 2181435 3274835 := bstep (se 1 (by rfl) ⟨2456126, by rfl⟩ : syracuseStep 3274835 = 4912253) B4912253
theorem B2183223 : Blo 2181435 2183223 := bstep (se 1 (by rfl) ⟨1637417, by rfl⟩ : syracuseStep 2183223 = 3274835) B3274835
theorem B3684197 : Blo 2181435 3684197 := bbase (se 4 (by rfl) ⟨345393, by rfl⟩ : syracuseStep 3684197 = 690787) (by norm_num)
theorem B2456131 : Blo 2181435 2456131 := bstep (se 1 (by rfl) ⟨1842098, by rfl⟩ : syracuseStep 2456131 = 3684197) B3684197
theorem B3274841 : Blo 2181435 3274841 := bstep (se 2 (by rfl) ⟨1228065, by rfl⟩ : syracuseStep 3274841 = 2456131) B2456131
theorem B2183227 : Blo 2181435 2183227 := bstep (se 1 (by rfl) ⟨1637420, by rfl⟩ : syracuseStep 2183227 = 3274841) B3274841
theorem B4662821 : Blo 2181435 4662821 := bbase (se 4 (by rfl) ⟨437139, by rfl⟩ : syracuseStep 4662821 = 874279) (by norm_num)
theorem B3108547 : Blo 2181435 3108547 := bstep (se 1 (by rfl) ⟨2331410, by rfl⟩ : syracuseStep 3108547 = 4662821) B4662821
theorem B16578917 : Blo 2181435 16578917 := bstep (se 4 (by rfl) ⟨1554273, by rfl⟩ : syracuseStep 16578917 = 3108547) B3108547
theorem B11052611 : Blo 2181435 11052611 := bstep (se 1 (by rfl) ⟨8289458, by rfl⟩ : syracuseStep 11052611 = 16578917) B16578917
theorem B7368407 : Blo 2181435 7368407 := bstep (se 1 (by rfl) ⟨5526305, by rfl⟩ : syracuseStep 7368407 = 11052611) B11052611
theorem B4912271 : Blo 2181435 4912271 := bstep (se 1 (by rfl) ⟨3684203, by rfl⟩ : syracuseStep 4912271 = 7368407) B7368407
theorem B3274847 : Blo 2181435 3274847 := bstep (se 1 (by rfl) ⟨2456135, by rfl⟩ : syracuseStep 3274847 = 4912271) B4912271
theorem B2183231 : Blo 2181435 2183231 := bstep (se 1 (by rfl) ⟨1637423, by rfl⟩ : syracuseStep 2183231 = 3274847) B3274847
theorem B3274853 : Blo 2181435 3274853 := bbase (se 4 (by rfl) ⟨307017, by rfl⟩ : syracuseStep 3274853 = 614035) (by norm_num)
theorem B2183235 : Blo 2181435 2183235 := bstep (se 1 (by rfl) ⟨1637426, by rfl⟩ : syracuseStep 2183235 = 3274853) B3274853
theorem B4375613 : Blo 2181435 4375613 := bbase (se 3 (by rfl) ⟨820427, by rfl⟩ : syracuseStep 4375613 = 1640855) (by norm_num)
theorem B2917075 : Blo 2181435 2917075 := bstep (se 1 (by rfl) ⟨2187806, by rfl⟩ : syracuseStep 2917075 = 4375613) B4375613
theorem B3889433 : Blo 2181435 3889433 := bstep (se 2 (by rfl) ⟨1458537, by rfl⟩ : syracuseStep 3889433 = 2917075) B2917075
theorem B2592955 : Blo 2181435 2592955 := bstep (se 1 (by rfl) ⟨1944716, by rfl⟩ : syracuseStep 2592955 = 3889433) B3889433
theorem B3457273 : Blo 2181435 3457273 := bstep (se 2 (by rfl) ⟨1296477, by rfl⟩ : syracuseStep 3457273 = 2592955) B2592955
theorem B295020629 : Blo 2181435 295020629 := bstep (se 8 (by rfl) ⟨1728636, by rfl⟩ : syracuseStep 295020629 = 3457273) B3457273
theorem B196680419 : Blo 2181435 196680419 := bstep (se 1 (by rfl) ⟨147510314, by rfl⟩ : syracuseStep 196680419 = 295020629) B295020629
theorem B131120279 : Blo 2181435 131120279 := bstep (se 1 (by rfl) ⟨98340209, by rfl⟩ : syracuseStep 131120279 = 196680419) B196680419
theorem B87413519 : Blo 2181435 87413519 := bstep (se 1 (by rfl) ⟨65560139, by rfl⟩ : syracuseStep 87413519 = 131120279) B131120279
theorem B233102717 : Blo 2181435 233102717 := bstep (se 3 (by rfl) ⟨43706759, by rfl⟩ : syracuseStep 233102717 = 87413519) B87413519
theorem B155401811 : Blo 2181435 155401811 := bstep (se 1 (by rfl) ⟨116551358, by rfl⟩ : syracuseStep 155401811 = 233102717) B233102717
theorem B103601207 : Blo 2181435 103601207 := bstep (se 1 (by rfl) ⟨77700905, by rfl⟩ : syracuseStep 103601207 = 155401811) B155401811
theorem B276269885 : Blo 2181435 276269885 := bstep (se 3 (by rfl) ⟨51800603, by rfl⟩ : syracuseStep 276269885 = 103601207) B103601207
theorem B184179923 : Blo 2181435 184179923 := bstep (se 1 (by rfl) ⟨138134942, by rfl⟩ : syracuseStep 184179923 = 276269885) B276269885
theorem B122786615 : Blo 2181435 122786615 := bstep (se 1 (by rfl) ⟨92089961, by rfl⟩ : syracuseStep 122786615 = 184179923) B184179923
theorem B327430973 : Blo 2181435 327430973 := bstep (se 3 (by rfl) ⟨61393307, by rfl⟩ : syracuseStep 327430973 = 122786615) B122786615
theorem B218287315 : Blo 2181435 218287315 := bstep (se 1 (by rfl) ⟨163715486, by rfl⟩ : syracuseStep 218287315 = 327430973) B327430973
theorem B1164199013 : Blo 2181435 1164199013 := bstep (se 4 (by rfl) ⟨109143657, by rfl⟩ : syracuseStep 1164199013 = 218287315) B218287315
theorem B776132675 : Blo 2181435 776132675 := bstep (se 1 (by rfl) ⟨582099506, by rfl⟩ : syracuseStep 776132675 = 1164199013) B1164199013
theorem B517421783 : Blo 2181435 517421783 := bstep (se 1 (by rfl) ⟨388066337, by rfl⟩ : syracuseStep 517421783 = 776132675) B776132675
theorem B1379791421 : Blo 2181435 1379791421 := bstep (se 3 (by rfl) ⟨258710891, by rfl⟩ : syracuseStep 1379791421 = 517421783) B517421783
theorem B919860947 : Blo 2181435 919860947 := bstep (se 1 (by rfl) ⟨689895710, by rfl⟩ : syracuseStep 919860947 = 1379791421) B1379791421
theorem B613240631 : Blo 2181435 613240631 := bstep (se 1 (by rfl) ⟨459930473, by rfl⟩ : syracuseStep 613240631 = 919860947) B919860947
theorem B408827087 : Blo 2181435 408827087 := bstep (se 1 (by rfl) ⟨306620315, by rfl⟩ : syracuseStep 408827087 = 613240631) B613240631
theorem B272551391 : Blo 2181435 272551391 := bstep (se 1 (by rfl) ⟨204413543, by rfl⟩ : syracuseStep 272551391 = 408827087) B408827087
theorem B181700927 : Blo 2181435 181700927 := bstep (se 1 (by rfl) ⟨136275695, by rfl⟩ : syracuseStep 181700927 = 272551391) B272551391
theorem B121133951 : Blo 2181435 121133951 := bstep (se 1 (by rfl) ⟨90850463, by rfl⟩ : syracuseStep 121133951 = 181700927) B181700927
theorem B80755967 : Blo 2181435 80755967 := bstep (se 1 (by rfl) ⟨60566975, by rfl⟩ : syracuseStep 80755967 = 121133951) B121133951
theorem B53837311 : Blo 2181435 53837311 := bstep (se 1 (by rfl) ⟨40377983, by rfl⟩ : syracuseStep 53837311 = 80755967) B80755967
theorem B71783081 : Blo 2181435 71783081 := bstep (se 2 (by rfl) ⟨26918655, by rfl⟩ : syracuseStep 71783081 = 53837311) B53837311
theorem B47855387 : Blo 2181435 47855387 := bstep (se 1 (by rfl) ⟨35891540, by rfl⟩ : syracuseStep 47855387 = 71783081) B71783081
theorem B31903591 : Blo 2181435 31903591 := bstep (se 1 (by rfl) ⟨23927693, by rfl⟩ : syracuseStep 31903591 = 47855387) B47855387
theorem B42538121 : Blo 2181435 42538121 := bstep (se 2 (by rfl) ⟨15951795, by rfl⟩ : syracuseStep 42538121 = 31903591) B31903591
theorem B28358747 : Blo 2181435 28358747 := bstep (se 1 (by rfl) ⟨21269060, by rfl⟩ : syracuseStep 28358747 = 42538121) B42538121
theorem B18905831 : Blo 2181435 18905831 := bstep (se 1 (by rfl) ⟨14179373, by rfl⟩ : syracuseStep 18905831 = 28358747) B28358747
theorem B12603887 : Blo 2181435 12603887 := bstep (se 1 (by rfl) ⟨9452915, by rfl⟩ : syracuseStep 12603887 = 18905831) B18905831
theorem B8402591 : Blo 2181435 8402591 := bstep (se 1 (by rfl) ⟨6301943, by rfl⟩ : syracuseStep 8402591 = 12603887) B12603887
theorem B5601727 : Blo 2181435 5601727 := bstep (se 1 (by rfl) ⟨4201295, by rfl⟩ : syracuseStep 5601727 = 8402591) B8402591
theorem B29875877 : Blo 2181435 29875877 := bstep (se 4 (by rfl) ⟨2800863, by rfl⟩ : syracuseStep 29875877 = 5601727) B5601727
theorem B19917251 : Blo 2181435 19917251 := bstep (se 1 (by rfl) ⟨14937938, by rfl⟩ : syracuseStep 19917251 = 29875877) B29875877
theorem B13278167 : Blo 2181435 13278167 := bstep (se 1 (by rfl) ⟨9958625, by rfl⟩ : syracuseStep 13278167 = 19917251) B19917251
theorem B8852111 : Blo 2181435 8852111 := bstep (se 1 (by rfl) ⟨6639083, by rfl⟩ : syracuseStep 8852111 = 13278167) B13278167
theorem B5901407 : Blo 2181435 5901407 := bstep (se 1 (by rfl) ⟨4426055, by rfl⟩ : syracuseStep 5901407 = 8852111) B8852111
theorem B3934271 : Blo 2181435 3934271 := bstep (se 1 (by rfl) ⟨2950703, by rfl⟩ : syracuseStep 3934271 = 5901407) B5901407
theorem B10491389 : Blo 2181435 10491389 := bstep (se 3 (by rfl) ⟨1967135, by rfl⟩ : syracuseStep 10491389 = 3934271) B3934271
theorem B6994259 : Blo 2181435 6994259 := bstep (se 1 (by rfl) ⟨5245694, by rfl⟩ : syracuseStep 6994259 = 10491389) B10491389
theorem B4662839 : Blo 2181435 4662839 := bstep (se 1 (by rfl) ⟨3497129, by rfl⟩ : syracuseStep 4662839 = 6994259) B6994259
theorem B3108559 : Blo 2181435 3108559 := bstep (se 1 (by rfl) ⟨2331419, by rfl⟩ : syracuseStep 3108559 = 4662839) B4662839
theorem B4144745 : Blo 2181435 4144745 := bstep (se 2 (by rfl) ⟨1554279, by rfl⟩ : syracuseStep 4144745 = 3108559) B3108559
theorem B2763163 : Blo 2181435 2763163 := bstep (se 1 (by rfl) ⟨2072372, by rfl⟩ : syracuseStep 2763163 = 4144745) B4144745
theorem B3684217 : Blo 2181435 3684217 := bstep (se 2 (by rfl) ⟨1381581, by rfl⟩ : syracuseStep 3684217 = 2763163) B2763163
theorem B4912289 : Blo 2181435 4912289 := bstep (se 2 (by rfl) ⟨1842108, by rfl⟩ : syracuseStep 4912289 = 3684217) B3684217
theorem B3274859 : Blo 2181435 3274859 := bstep (se 1 (by rfl) ⟨2456144, by rfl⟩ : syracuseStep 3274859 = 4912289) B4912289
theorem B2183239 : Blo 2181435 2183239 := bstep (se 1 (by rfl) ⟨1637429, by rfl⟩ : syracuseStep 2183239 = 3274859) B3274859
theorem B2456149 : Blo 2181435 2456149 := bbase (se 8 (by rfl) ⟨14391, by rfl⟩ : syracuseStep 2456149 = 28783) (by norm_num)
theorem B3274865 : Blo 2181435 3274865 := bstep (se 2 (by rfl) ⟨1228074, by rfl⟩ : syracuseStep 3274865 = 2456149) B2456149
theorem B2183243 : Blo 2181435 2183243 := bstep (se 1 (by rfl) ⟨1637432, by rfl⟩ : syracuseStep 2183243 = 3274865) B3274865
theorem B2763173 : Blo 2181435 2763173 := bbase (se 4 (by rfl) ⟨259047, by rfl⟩ : syracuseStep 2763173 = 518095) (by norm_num)
theorem B7368461 : Blo 2181435 7368461 := bstep (se 3 (by rfl) ⟨1381586, by rfl⟩ : syracuseStep 7368461 = 2763173) B2763173
theorem B4912307 : Blo 2181435 4912307 := bstep (se 1 (by rfl) ⟨3684230, by rfl⟩ : syracuseStep 4912307 = 7368461) B7368461
theorem B3274871 : Blo 2181435 3274871 := bstep (se 1 (by rfl) ⟨2456153, by rfl⟩ : syracuseStep 3274871 = 4912307) B4912307
theorem B2183247 : Blo 2181435 2183247 := bstep (se 1 (by rfl) ⟨1637435, by rfl⟩ : syracuseStep 2183247 = 3274871) B3274871
theorem B3274877 : Blo 2181435 3274877 := bbase (se 3 (by rfl) ⟨614039, by rfl⟩ : syracuseStep 3274877 = 1228079) (by norm_num)
theorem B2183251 : Blo 2181435 2183251 := bstep (se 1 (by rfl) ⟨1637438, by rfl⟩ : syracuseStep 2183251 = 3274877) B3274877
theorem B4912325 : Blo 2181435 4912325 := bbase (se 4 (by rfl) ⟨460530, by rfl⟩ : syracuseStep 4912325 = 921061) (by norm_num)
theorem B3274883 : Blo 2181435 3274883 := bstep (se 1 (by rfl) ⟨2456162, by rfl⟩ : syracuseStep 3274883 = 4912325) B4912325
theorem B2183255 : Blo 2181435 2183255 := bstep (se 1 (by rfl) ⟨1637441, by rfl⟩ : syracuseStep 2183255 = 3274883) B3274883
theorem B5901461 : Blo 2181435 5901461 := bbase (se 6 (by rfl) ⟨138315, by rfl⟩ : syracuseStep 5901461 = 276631) (by norm_num)
theorem B3934307 : Blo 2181435 3934307 := bstep (se 1 (by rfl) ⟨2950730, by rfl⟩ : syracuseStep 3934307 = 5901461) B5901461
theorem B2622871 : Blo 2181435 2622871 := bstep (se 1 (by rfl) ⟨1967153, by rfl⟩ : syracuseStep 2622871 = 3934307) B3934307
theorem B13988645 : Blo 2181435 13988645 := bstep (se 4 (by rfl) ⟨1311435, by rfl⟩ : syracuseStep 13988645 = 2622871) B2622871
theorem B9325763 : Blo 2181435 9325763 := bstep (se 1 (by rfl) ⟨6994322, by rfl⟩ : syracuseStep 9325763 = 13988645) B13988645
theorem B6217175 : Blo 2181435 6217175 := bstep (se 1 (by rfl) ⟨4662881, by rfl⟩ : syracuseStep 6217175 = 9325763) B9325763
theorem B4144783 : Blo 2181435 4144783 := bstep (se 1 (by rfl) ⟨3108587, by rfl⟩ : syracuseStep 4144783 = 6217175) B6217175
theorem B5526377 : Blo 2181435 5526377 := bstep (se 2 (by rfl) ⟨2072391, by rfl⟩ : syracuseStep 5526377 = 4144783) B4144783
theorem B3684251 : Blo 2181435 3684251 := bstep (se 1 (by rfl) ⟨2763188, by rfl⟩ : syracuseStep 3684251 = 5526377) B5526377
theorem B2456167 : Blo 2181435 2456167 := bstep (se 1 (by rfl) ⟨1842125, by rfl⟩ : syracuseStep 2456167 = 3684251) B3684251
theorem B3274889 : Blo 2181435 3274889 := bstep (se 2 (by rfl) ⟨1228083, by rfl⟩ : syracuseStep 3274889 = 2456167) B2456167
theorem B2183259 : Blo 2181435 2183259 := bstep (se 1 (by rfl) ⟨1637444, by rfl⟩ : syracuseStep 2183259 = 3274889) B3274889
theorem B11052773 : Blo 2181435 11052773 := bbase (se 4 (by rfl) ⟨1036197, by rfl⟩ : syracuseStep 11052773 = 2072395) (by norm_num)
theorem B7368515 : Blo 2181435 7368515 := bstep (se 1 (by rfl) ⟨5526386, by rfl⟩ : syracuseStep 7368515 = 11052773) B11052773
theorem B4912343 : Blo 2181435 4912343 := bstep (se 1 (by rfl) ⟨3684257, by rfl⟩ : syracuseStep 4912343 = 7368515) B7368515
theorem B3274895 : Blo 2181435 3274895 := bstep (se 1 (by rfl) ⟨2456171, by rfl⟩ : syracuseStep 3274895 = 4912343) B4912343
theorem B2183263 : Blo 2181435 2183263 := bstep (se 1 (by rfl) ⟨1637447, by rfl⟩ : syracuseStep 2183263 = 3274895) B3274895
theorem B3274901 : Blo 2181435 3274901 := bbase (se 6 (by rfl) ⟨76755, by rfl⟩ : syracuseStep 3274901 = 153511) (by norm_num)
theorem B2183267 : Blo 2181435 2183267 := bstep (se 1 (by rfl) ⟨1637450, by rfl⟩ : syracuseStep 2183267 = 3274901) B3274901
theorem B9325813 : Blo 2181435 9325813 := bbase (se 5 (by rfl) ⟨437147, by rfl⟩ : syracuseStep 9325813 = 874295) (by norm_num)
theorem B12434417 : Blo 2181435 12434417 := bstep (se 2 (by rfl) ⟨4662906, by rfl⟩ : syracuseStep 12434417 = 9325813) B9325813
theorem B8289611 : Blo 2181435 8289611 := bstep (se 1 (by rfl) ⟨6217208, by rfl⟩ : syracuseStep 8289611 = 12434417) B12434417
theorem B5526407 : Blo 2181435 5526407 := bstep (se 1 (by rfl) ⟨4144805, by rfl⟩ : syracuseStep 5526407 = 8289611) B8289611
theorem B3684271 : Blo 2181435 3684271 := bstep (se 1 (by rfl) ⟨2763203, by rfl⟩ : syracuseStep 3684271 = 5526407) B5526407
theorem B4912361 : Blo 2181435 4912361 := bstep (se 2 (by rfl) ⟨1842135, by rfl⟩ : syracuseStep 4912361 = 3684271) B3684271
theorem B3274907 : Blo 2181435 3274907 := bstep (se 1 (by rfl) ⟨2456180, by rfl⟩ : syracuseStep 3274907 = 4912361) B4912361
theorem B2183271 : Blo 2181435 2183271 := bstep (se 1 (by rfl) ⟨1637453, by rfl⟩ : syracuseStep 2183271 = 3274907) B3274907
theorem B2456185 : Blo 2181435 2456185 := bbase (se 2 (by rfl) ⟨921069, by rfl⟩ : syracuseStep 2456185 = 1842139) (by norm_num)
theorem B3274913 : Blo 2181435 3274913 := bstep (se 2 (by rfl) ⟨1228092, by rfl⟩ : syracuseStep 3274913 = 2456185) B2456185
theorem B2183275 : Blo 2181435 2183275 := bstep (se 1 (by rfl) ⟨1637456, by rfl⟩ : syracuseStep 2183275 = 3274913) B3274913
theorem B20983157 : Blo 2181435 20983157 := bbase (se 5 (by rfl) ⟨983585, by rfl⟩ : syracuseStep 20983157 = 1967171) (by norm_num)
theorem B13988771 : Blo 2181435 13988771 := bstep (se 1 (by rfl) ⟨10491578, by rfl⟩ : syracuseStep 13988771 = 20983157) B20983157
theorem B9325847 : Blo 2181435 9325847 := bstep (se 1 (by rfl) ⟨6994385, by rfl⟩ : syracuseStep 9325847 = 13988771) B13988771
theorem B6217231 : Blo 2181435 6217231 := bstep (se 1 (by rfl) ⟨4662923, by rfl⟩ : syracuseStep 6217231 = 9325847) B9325847
theorem B8289641 : Blo 2181435 8289641 := bstep (se 2 (by rfl) ⟨3108615, by rfl⟩ : syracuseStep 8289641 = 6217231) B6217231
theorem B5526427 : Blo 2181435 5526427 := bstep (se 1 (by rfl) ⟨4144820, by rfl⟩ : syracuseStep 5526427 = 8289641) B8289641
theorem B7368569 : Blo 2181435 7368569 := bstep (se 2 (by rfl) ⟨2763213, by rfl⟩ : syracuseStep 7368569 = 5526427) B5526427
theorem B4912379 : Blo 2181435 4912379 := bstep (se 1 (by rfl) ⟨3684284, by rfl⟩ : syracuseStep 4912379 = 7368569) B7368569
theorem B3274919 : Blo 2181435 3274919 := bstep (se 1 (by rfl) ⟨2456189, by rfl⟩ : syracuseStep 3274919 = 4912379) B4912379
theorem B2183279 : Blo 2181435 2183279 := bstep (se 1 (by rfl) ⟨1637459, by rfl⟩ : syracuseStep 2183279 = 3274919) B3274919
theorem B3274925 : Blo 2181435 3274925 := bbase (se 3 (by rfl) ⟨614048, by rfl⟩ : syracuseStep 3274925 = 1228097) (by norm_num)
theorem B2183283 : Blo 2181435 2183283 := bstep (se 1 (by rfl) ⟨1637462, by rfl⟩ : syracuseStep 2183283 = 3274925) B3274925
theorem B4912397 : Blo 2181435 4912397 := bbase (se 3 (by rfl) ⟨921074, by rfl⟩ : syracuseStep 4912397 = 1842149) (by norm_num)
theorem B3274931 : Blo 2181435 3274931 := bstep (se 1 (by rfl) ⟨2456198, by rfl⟩ : syracuseStep 3274931 = 4912397) B4912397
theorem B2183287 : Blo 2181435 2183287 := bstep (se 1 (by rfl) ⟨1637465, by rfl⟩ : syracuseStep 2183287 = 3274931) B3274931
theorem B2763229 : Blo 2181435 2763229 := bbase (se 3 (by rfl) ⟨518105, by rfl⟩ : syracuseStep 2763229 = 1036211) (by norm_num)
theorem B3684305 : Blo 2181435 3684305 := bstep (se 2 (by rfl) ⟨1381614, by rfl⟩ : syracuseStep 3684305 = 2763229) B2763229
theorem B2456203 : Blo 2181435 2456203 := bstep (se 1 (by rfl) ⟨1842152, by rfl⟩ : syracuseStep 2456203 = 3684305) B3684305
theorem B3274937 : Blo 2181435 3274937 := bstep (se 2 (by rfl) ⟨1228101, by rfl⟩ : syracuseStep 3274937 = 2456203) B2456203
theorem B2183291 : Blo 2181435 2183291 := bstep (se 1 (by rfl) ⟨1637468, by rfl⟩ : syracuseStep 2183291 = 3274937) B3274937
theorem B18651829 : Blo 2181435 18651829 := bbase (se 5 (by rfl) ⟨874304, by rfl⟩ : syracuseStep 18651829 = 1748609) (by norm_num)
theorem B24869105 : Blo 2181435 24869105 := bstep (se 2 (by rfl) ⟨9325914, by rfl⟩ : syracuseStep 24869105 = 18651829) B18651829
theorem B16579403 : Blo 2181435 16579403 := bstep (se 1 (by rfl) ⟨12434552, by rfl⟩ : syracuseStep 16579403 = 24869105) B24869105
theorem B11052935 : Blo 2181435 11052935 := bstep (se 1 (by rfl) ⟨8289701, by rfl⟩ : syracuseStep 11052935 = 16579403) B16579403
theorem B7368623 : Blo 2181435 7368623 := bstep (se 1 (by rfl) ⟨5526467, by rfl⟩ : syracuseStep 7368623 = 11052935) B11052935
theorem B4912415 : Blo 2181435 4912415 := bstep (se 1 (by rfl) ⟨3684311, by rfl⟩ : syracuseStep 4912415 = 7368623) B7368623
theorem B3274943 : Blo 2181435 3274943 := bstep (se 1 (by rfl) ⟨2456207, by rfl⟩ : syracuseStep 3274943 = 4912415) B4912415
theorem B2183295 : Blo 2181435 2183295 := bstep (se 1 (by rfl) ⟨1637471, by rfl⟩ : syracuseStep 2183295 = 3274943) B3274943
theorem B3274949 : Blo 2181435 3274949 := bbase (se 4 (by rfl) ⟨307026, by rfl⟩ : syracuseStep 3274949 = 614053) (by norm_num)
theorem B2183299 : Blo 2181435 2183299 := bstep (se 1 (by rfl) ⟨1637474, by rfl⟩ : syracuseStep 2183299 = 3274949) B3274949
theorem B3684325 : Blo 2181435 3684325 := bbase (se 4 (by rfl) ⟨345405, by rfl⟩ : syracuseStep 3684325 = 690811) (by norm_num)
theorem B4912433 : Blo 2181435 4912433 := bstep (se 2 (by rfl) ⟨1842162, by rfl⟩ : syracuseStep 4912433 = 3684325) B3684325
theorem B3274955 : Blo 2181435 3274955 := bstep (se 1 (by rfl) ⟨2456216, by rfl⟩ : syracuseStep 3274955 = 4912433) B4912433
theorem B2183303 : Blo 2181435 2183303 := bstep (se 1 (by rfl) ⟨1637477, by rfl⟩ : syracuseStep 2183303 = 3274955) B3274955
theorem B2456221 : Blo 2181435 2456221 := bbase (se 3 (by rfl) ⟨460541, by rfl⟩ : syracuseStep 2456221 = 921083) (by norm_num)
theorem B3274961 : Blo 2181435 3274961 := bstep (se 2 (by rfl) ⟨1228110, by rfl⟩ : syracuseStep 3274961 = 2456221) B2456221
theorem B2183307 : Blo 2181435 2183307 := bstep (se 1 (by rfl) ⟨1637480, by rfl⟩ : syracuseStep 2183307 = 3274961) B3274961
theorem B7368677 : Blo 2181435 7368677 := bbase (se 4 (by rfl) ⟨690813, by rfl⟩ : syracuseStep 7368677 = 1381627) (by norm_num)
theorem B4912451 : Blo 2181435 4912451 := bstep (se 1 (by rfl) ⟨3684338, by rfl⟩ : syracuseStep 4912451 = 7368677) B7368677
theorem B3274967 : Blo 2181435 3274967 := bstep (se 1 (by rfl) ⟨2456225, by rfl⟩ : syracuseStep 3274967 = 4912451) B4912451
theorem B2183311 : Blo 2181435 2183311 := bstep (se 1 (by rfl) ⟨1637483, by rfl⟩ : syracuseStep 2183311 = 3274967) B3274967
theorem B3274973 : Blo 2181435 3274973 := bbase (se 3 (by rfl) ⟨614057, by rfl⟩ : syracuseStep 3274973 = 1228115) (by norm_num)
theorem B2183315 : Blo 2181435 2183315 := bstep (se 1 (by rfl) ⟨1637486, by rfl⟩ : syracuseStep 2183315 = 3274973) B3274973
theorem B4912469 : Blo 2181435 4912469 := bbase (se 13 (by rfl) ⟨899, by rfl⟩ : syracuseStep 4912469 = 1799) (by norm_num)
theorem B3274979 : Blo 2181435 3274979 := bstep (se 1 (by rfl) ⟨2456234, by rfl⟩ : syracuseStep 3274979 = 4912469) B4912469
theorem B2183319 : Blo 2181435 2183319 := bstep (se 1 (by rfl) ⟨1637489, by rfl⟩ : syracuseStep 2183319 = 3274979) B3274979
theorem B2331509 : Blo 2181435 2331509 := bbase (se 5 (by rfl) ⟨109289, by rfl⟩ : syracuseStep 2331509 = 218579) (by norm_num)
theorem B6217357 : Blo 2181435 6217357 := bstep (se 3 (by rfl) ⟨1165754, by rfl⟩ : syracuseStep 6217357 = 2331509) B2331509
theorem B8289809 : Blo 2181435 8289809 := bstep (se 2 (by rfl) ⟨3108678, by rfl⟩ : syracuseStep 8289809 = 6217357) B6217357
theorem B5526539 : Blo 2181435 5526539 := bstep (se 1 (by rfl) ⟨4144904, by rfl⟩ : syracuseStep 5526539 = 8289809) B8289809
theorem B3684359 : Blo 2181435 3684359 := bstep (se 1 (by rfl) ⟨2763269, by rfl⟩ : syracuseStep 3684359 = 5526539) B5526539
theorem B2456239 : Blo 2181435 2456239 := bstep (se 1 (by rfl) ⟨1842179, by rfl⟩ : syracuseStep 2456239 = 3684359) B3684359
theorem B3274985 : Blo 2181435 3274985 := bstep (se 2 (by rfl) ⟨1228119, by rfl⟩ : syracuseStep 3274985 = 2456239) B2456239
theorem B2183323 : Blo 2181435 2183323 := bstep (se 1 (by rfl) ⟨1637492, by rfl⟩ : syracuseStep 2183323 = 3274985) B3274985
theorem B18906581 : Blo 2181435 18906581 := bbase (se 7 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 18906581 = 443123) (by norm_num)
theorem B50417549 : Blo 2181435 50417549 := bstep (se 3 (by rfl) ⟨9453290, by rfl⟩ : syracuseStep 50417549 = 18906581) B18906581
theorem B33611699 : Blo 2181435 33611699 := bstep (se 1 (by rfl) ⟨25208774, by rfl⟩ : syracuseStep 33611699 = 50417549) B50417549
theorem B89631197 : Blo 2181435 89631197 := bstep (se 3 (by rfl) ⟨16805849, by rfl⟩ : syracuseStep 89631197 = 33611699) B33611699
theorem B59754131 : Blo 2181435 59754131 := bstep (se 1 (by rfl) ⟨44815598, by rfl⟩ : syracuseStep 59754131 = 89631197) B89631197
theorem B39836087 : Blo 2181435 39836087 := bstep (se 1 (by rfl) ⟨29877065, by rfl⟩ : syracuseStep 39836087 = 59754131) B59754131
theorem B26557391 : Blo 2181435 26557391 := bstep (se 1 (by rfl) ⟨19918043, by rfl⟩ : syracuseStep 26557391 = 39836087) B39836087
theorem B17704927 : Blo 2181435 17704927 := bstep (se 1 (by rfl) ⟨13278695, by rfl⟩ : syracuseStep 17704927 = 26557391) B26557391
theorem B23606569 : Blo 2181435 23606569 := bstep (se 2 (by rfl) ⟨8852463, by rfl⟩ : syracuseStep 23606569 = 17704927) B17704927
theorem B31475425 : Blo 2181435 31475425 := bstep (se 2 (by rfl) ⟨11803284, by rfl⟩ : syracuseStep 31475425 = 23606569) B23606569
theorem B41967233 : Blo 2181435 41967233 := bstep (se 2 (by rfl) ⟨15737712, by rfl⟩ : syracuseStep 41967233 = 31475425) B31475425
theorem B27978155 : Blo 2181435 27978155 := bstep (se 1 (by rfl) ⟨20983616, by rfl⟩ : syracuseStep 27978155 = 41967233) B41967233
theorem B18652103 : Blo 2181435 18652103 := bstep (se 1 (by rfl) ⟨13989077, by rfl⟩ : syracuseStep 18652103 = 27978155) B27978155
theorem B12434735 : Blo 2181435 12434735 := bstep (se 1 (by rfl) ⟨9326051, by rfl⟩ : syracuseStep 12434735 = 18652103) B18652103
theorem B8289823 : Blo 2181435 8289823 := bstep (se 1 (by rfl) ⟨6217367, by rfl⟩ : syracuseStep 8289823 = 12434735) B12434735
theorem B11053097 : Blo 2181435 11053097 := bstep (se 2 (by rfl) ⟨4144911, by rfl⟩ : syracuseStep 11053097 = 8289823) B8289823
theorem B7368731 : Blo 2181435 7368731 := bstep (se 1 (by rfl) ⟨5526548, by rfl⟩ : syracuseStep 7368731 = 11053097) B11053097
theorem B4912487 : Blo 2181435 4912487 := bstep (se 1 (by rfl) ⟨3684365, by rfl⟩ : syracuseStep 4912487 = 7368731) B7368731
theorem B3274991 : Blo 2181435 3274991 := bstep (se 1 (by rfl) ⟨2456243, by rfl⟩ : syracuseStep 3274991 = 4912487) B4912487
theorem B2183327 : Blo 2181435 2183327 := bstep (se 1 (by rfl) ⟨1637495, by rfl⟩ : syracuseStep 2183327 = 3274991) B3274991
theorem B3274997 : Blo 2181435 3274997 := bbase (se 5 (by rfl) ⟨153515, by rfl⟩ : syracuseStep 3274997 = 307031) (by norm_num)
theorem B2183331 : Blo 2181435 2183331 := bstep (se 1 (by rfl) ⟨1637498, by rfl⟩ : syracuseStep 2183331 = 3274997) B3274997
theorem B5601973 : Blo 2181435 5601973 := bbase (se 5 (by rfl) ⟨262592, by rfl⟩ : syracuseStep 5601973 = 525185) (by norm_num)
theorem B7469297 : Blo 2181435 7469297 := bstep (se 2 (by rfl) ⟨2800986, by rfl⟩ : syracuseStep 7469297 = 5601973) B5601973
theorem B4979531 : Blo 2181435 4979531 := bstep (se 1 (by rfl) ⟨3734648, by rfl⟩ : syracuseStep 4979531 = 7469297) B7469297
theorem B3319687 : Blo 2181435 3319687 := bstep (se 1 (by rfl) ⟨2489765, by rfl⟩ : syracuseStep 3319687 = 4979531) B4979531
theorem B4426249 : Blo 2181435 4426249 := bstep (se 2 (by rfl) ⟨1659843, by rfl⟩ : syracuseStep 4426249 = 3319687) B3319687
theorem B5901665 : Blo 2181435 5901665 := bstep (se 2 (by rfl) ⟨2213124, by rfl⟩ : syracuseStep 5901665 = 4426249) B4426249
theorem B15737773 : Blo 2181435 15737773 := bstep (se 3 (by rfl) ⟨2950832, by rfl⟩ : syracuseStep 15737773 = 5901665) B5901665
theorem B20983697 : Blo 2181435 20983697 := bstep (se 2 (by rfl) ⟨7868886, by rfl⟩ : syracuseStep 20983697 = 15737773) B15737773
theorem B13989131 : Blo 2181435 13989131 := bstep (se 1 (by rfl) ⟨10491848, by rfl⟩ : syracuseStep 13989131 = 20983697) B20983697
theorem B9326087 : Blo 2181435 9326087 := bstep (se 1 (by rfl) ⟨6994565, by rfl⟩ : syracuseStep 9326087 = 13989131) B13989131
theorem B6217391 : Blo 2181435 6217391 := bstep (se 1 (by rfl) ⟨4663043, by rfl⟩ : syracuseStep 6217391 = 9326087) B9326087
theorem B4144927 : Blo 2181435 4144927 := bstep (se 1 (by rfl) ⟨3108695, by rfl⟩ : syracuseStep 4144927 = 6217391) B6217391
theorem B5526569 : Blo 2181435 5526569 := bstep (se 2 (by rfl) ⟨2072463, by rfl⟩ : syracuseStep 5526569 = 4144927) B4144927
theorem B3684379 : Blo 2181435 3684379 := bstep (se 1 (by rfl) ⟨2763284, by rfl⟩ : syracuseStep 3684379 = 5526569) B5526569
theorem B4912505 : Blo 2181435 4912505 := bstep (se 2 (by rfl) ⟨1842189, by rfl⟩ : syracuseStep 4912505 = 3684379) B3684379
theorem B3275003 : Blo 2181435 3275003 := bstep (se 1 (by rfl) ⟨2456252, by rfl⟩ : syracuseStep 3275003 = 4912505) B4912505
theorem B2183335 : Blo 2181435 2183335 := bstep (se 1 (by rfl) ⟨1637501, by rfl⟩ : syracuseStep 2183335 = 3275003) B3275003
theorem B2456257 : Blo 2181435 2456257 := bbase (se 2 (by rfl) ⟨921096, by rfl⟩ : syracuseStep 2456257 = 1842193) (by norm_num)
theorem B3275009 : Blo 2181435 3275009 := bstep (se 2 (by rfl) ⟨1228128, by rfl⟩ : syracuseStep 3275009 = 2456257) B2456257
theorem B2183339 : Blo 2181435 2183339 := bstep (se 1 (by rfl) ⟨1637504, by rfl⟩ : syracuseStep 2183339 = 3275009) B3275009
theorem B5526589 : Blo 2181435 5526589 := bbase (se 3 (by rfl) ⟨1036235, by rfl⟩ : syracuseStep 5526589 = 2072471) (by norm_num)
theorem B7368785 : Blo 2181435 7368785 := bstep (se 2 (by rfl) ⟨2763294, by rfl⟩ : syracuseStep 7368785 = 5526589) B5526589
theorem B4912523 : Blo 2181435 4912523 := bstep (se 1 (by rfl) ⟨3684392, by rfl⟩ : syracuseStep 4912523 = 7368785) B7368785
theorem B3275015 : Blo 2181435 3275015 := bstep (se 1 (by rfl) ⟨2456261, by rfl⟩ : syracuseStep 3275015 = 4912523) B4912523
theorem B2183343 : Blo 2181435 2183343 := bstep (se 1 (by rfl) ⟨1637507, by rfl⟩ : syracuseStep 2183343 = 3275015) B3275015
theorem B3275021 : Blo 2181435 3275021 := bbase (se 3 (by rfl) ⟨614066, by rfl⟩ : syracuseStep 3275021 = 1228133) (by norm_num)
theorem B2183347 : Blo 2181435 2183347 := bstep (se 1 (by rfl) ⟨1637510, by rfl⟩ : syracuseStep 2183347 = 3275021) B3275021
theorem B4912541 : Blo 2181435 4912541 := bbase (se 3 (by rfl) ⟨921101, by rfl⟩ : syracuseStep 4912541 = 1842203) (by norm_num)
theorem B3275027 : Blo 2181435 3275027 := bstep (se 1 (by rfl) ⟨2456270, by rfl⟩ : syracuseStep 3275027 = 4912541) B4912541
theorem B2183351 : Blo 2181435 2183351 := bstep (se 1 (by rfl) ⟨1637513, by rfl⟩ : syracuseStep 2183351 = 3275027) B3275027
theorem B3684413 : Blo 2181435 3684413 := bbase (se 3 (by rfl) ⟨690827, by rfl⟩ : syracuseStep 3684413 = 1381655) (by norm_num)
theorem B2456275 : Blo 2181435 2456275 := bstep (se 1 (by rfl) ⟨1842206, by rfl⟩ : syracuseStep 2456275 = 3684413) B3684413
theorem B3275033 : Blo 2181435 3275033 := bstep (se 2 (by rfl) ⟨1228137, by rfl⟩ : syracuseStep 3275033 = 2456275) B2456275
theorem B2183355 : Blo 2181435 2183355 := bstep (se 1 (by rfl) ⟨1637516, by rfl⟩ : syracuseStep 2183355 = 3275033) B3275033
theorem B8852597 : Blo 2181435 8852597 := bbase (se 5 (by rfl) ⟨414965, by rfl⟩ : syracuseStep 8852597 = 829931) (by norm_num)
theorem B5901731 : Blo 2181435 5901731 := bstep (se 1 (by rfl) ⟨4426298, by rfl⟩ : syracuseStep 5901731 = 8852597) B8852597
theorem B3934487 : Blo 2181435 3934487 := bstep (se 1 (by rfl) ⟨2950865, by rfl⟩ : syracuseStep 3934487 = 5901731) B5901731
theorem B2622991 : Blo 2181435 2622991 := bstep (se 1 (by rfl) ⟨1967243, by rfl⟩ : syracuseStep 2622991 = 3934487) B3934487
theorem B3497321 : Blo 2181435 3497321 := bstep (se 2 (by rfl) ⟨1311495, by rfl⟩ : syracuseStep 3497321 = 2622991) B2622991
theorem B2331547 : Blo 2181435 2331547 := bstep (se 1 (by rfl) ⟨1748660, by rfl⟩ : syracuseStep 2331547 = 3497321) B3497321
theorem B12434917 : Blo 2181435 12434917 := bstep (se 4 (by rfl) ⟨1165773, by rfl⟩ : syracuseStep 12434917 = 2331547) B2331547
theorem B16579889 : Blo 2181435 16579889 := bstep (se 2 (by rfl) ⟨6217458, by rfl⟩ : syracuseStep 16579889 = 12434917) B12434917
theorem B11053259 : Blo 2181435 11053259 := bstep (se 1 (by rfl) ⟨8289944, by rfl⟩ : syracuseStep 11053259 = 16579889) B16579889
theorem B7368839 : Blo 2181435 7368839 := bstep (se 1 (by rfl) ⟨5526629, by rfl⟩ : syracuseStep 7368839 = 11053259) B11053259
theorem B4912559 : Blo 2181435 4912559 := bstep (se 1 (by rfl) ⟨3684419, by rfl⟩ : syracuseStep 4912559 = 7368839) B7368839
theorem B3275039 : Blo 2181435 3275039 := bstep (se 1 (by rfl) ⟨2456279, by rfl⟩ : syracuseStep 3275039 = 4912559) B4912559
theorem B2183359 : Blo 2181435 2183359 := bstep (se 1 (by rfl) ⟨1637519, by rfl⟩ : syracuseStep 2183359 = 3275039) B3275039
theorem B3275045 : Blo 2181435 3275045 := bbase (se 4 (by rfl) ⟨307035, by rfl⟩ : syracuseStep 3275045 = 614071) (by norm_num)
theorem B2183363 : Blo 2181435 2183363 := bstep (se 1 (by rfl) ⟨1637522, by rfl⟩ : syracuseStep 2183363 = 3275045) B3275045
theorem B2763325 : Blo 2181435 2763325 := bbase (se 3 (by rfl) ⟨518123, by rfl⟩ : syracuseStep 2763325 = 1036247) (by norm_num)
theorem B3684433 : Blo 2181435 3684433 := bstep (se 2 (by rfl) ⟨1381662, by rfl⟩ : syracuseStep 3684433 = 2763325) B2763325
theorem B4912577 : Blo 2181435 4912577 := bstep (se 2 (by rfl) ⟨1842216, by rfl⟩ : syracuseStep 4912577 = 3684433) B3684433
theorem B3275051 : Blo 2181435 3275051 := bstep (se 1 (by rfl) ⟨2456288, by rfl⟩ : syracuseStep 3275051 = 4912577) B4912577
theorem B2183367 : Blo 2181435 2183367 := bstep (se 1 (by rfl) ⟨1637525, by rfl⟩ : syracuseStep 2183367 = 3275051) B3275051
theorem B2456293 : Blo 2181435 2456293 := bbase (se 4 (by rfl) ⟨230277, by rfl⟩ : syracuseStep 2456293 = 460555) (by norm_num)
theorem B3275057 : Blo 2181435 3275057 := bstep (se 2 (by rfl) ⟨1228146, by rfl⟩ : syracuseStep 3275057 = 2456293) B2456293
theorem B2183371 : Blo 2181435 2183371 := bstep (se 1 (by rfl) ⟨1637528, by rfl⟩ : syracuseStep 2183371 = 3275057) B3275057
theorem B5246021 : Blo 2181435 5246021 := bbase (se 4 (by rfl) ⟨491814, by rfl⟩ : syracuseStep 5246021 = 983629) (by norm_num)
theorem B3497347 : Blo 2181435 3497347 := bstep (se 1 (by rfl) ⟨2623010, by rfl⟩ : syracuseStep 3497347 = 5246021) B5246021
theorem B4663129 : Blo 2181435 4663129 := bstep (se 2 (by rfl) ⟨1748673, by rfl⟩ : syracuseStep 4663129 = 3497347) B3497347
theorem B6217505 : Blo 2181435 6217505 := bstep (se 2 (by rfl) ⟨2331564, by rfl⟩ : syracuseStep 6217505 = 4663129) B4663129
theorem B4145003 : Blo 2181435 4145003 := bstep (se 1 (by rfl) ⟨3108752, by rfl⟩ : syracuseStep 4145003 = 6217505) B6217505
theorem B2763335 : Blo 2181435 2763335 := bstep (se 1 (by rfl) ⟨2072501, by rfl⟩ : syracuseStep 2763335 = 4145003) B4145003
theorem B7368893 : Blo 2181435 7368893 := bstep (se 3 (by rfl) ⟨1381667, by rfl⟩ : syracuseStep 7368893 = 2763335) B2763335
theorem B4912595 : Blo 2181435 4912595 := bstep (se 1 (by rfl) ⟨3684446, by rfl⟩ : syracuseStep 4912595 = 7368893) B7368893
theorem B3275063 : Blo 2181435 3275063 := bstep (se 1 (by rfl) ⟨2456297, by rfl⟩ : syracuseStep 3275063 = 4912595) B4912595
theorem B2183375 : Blo 2181435 2183375 := bstep (se 1 (by rfl) ⟨1637531, by rfl⟩ : syracuseStep 2183375 = 3275063) B3275063
theorem B3275069 : Blo 2181435 3275069 := bbase (se 3 (by rfl) ⟨614075, by rfl⟩ : syracuseStep 3275069 = 1228151) (by norm_num)
theorem B2183379 : Blo 2181435 2183379 := bstep (se 1 (by rfl) ⟨1637534, by rfl⟩ : syracuseStep 2183379 = 3275069) B3275069
theorem B4912613 : Blo 2181435 4912613 := bbase (se 4 (by rfl) ⟨460557, by rfl⟩ : syracuseStep 4912613 = 921115) (by norm_num)
theorem B3275075 : Blo 2181435 3275075 := bstep (se 1 (by rfl) ⟨2456306, by rfl⟩ : syracuseStep 3275075 = 4912613) B4912613
theorem B2183383 : Blo 2181435 2183383 := bstep (se 1 (by rfl) ⟨1637537, by rfl⟩ : syracuseStep 2183383 = 3275075) B3275075
theorem B5526701 : Blo 2181435 5526701 := bbase (se 3 (by rfl) ⟨1036256, by rfl⟩ : syracuseStep 5526701 = 2072513) (by norm_num)
theorem B3684467 : Blo 2181435 3684467 := bstep (se 1 (by rfl) ⟨2763350, by rfl⟩ : syracuseStep 3684467 = 5526701) B5526701
theorem B2456311 : Blo 2181435 2456311 := bstep (se 1 (by rfl) ⟨1842233, by rfl⟩ : syracuseStep 2456311 = 3684467) B3684467
theorem B3275081 : Blo 2181435 3275081 := bstep (se 2 (by rfl) ⟨1228155, by rfl⟩ : syracuseStep 3275081 = 2456311) B2456311
theorem B2183387 : Blo 2181435 2183387 := bstep (se 1 (by rfl) ⟨1637540, by rfl⟩ : syracuseStep 2183387 = 3275081) B3275081
theorem B5602117 : Blo 2181435 5602117 := bbase (se 4 (by rfl) ⟨525198, by rfl⟩ : syracuseStep 5602117 = 1050397) (by norm_num)
theorem B7469489 : Blo 2181435 7469489 := bstep (se 2 (by rfl) ⟨2801058, by rfl⟩ : syracuseStep 7469489 = 5602117) B5602117
theorem B4979659 : Blo 2181435 4979659 := bstep (se 1 (by rfl) ⟨3734744, by rfl⟩ : syracuseStep 4979659 = 7469489) B7469489
theorem B6639545 : Blo 2181435 6639545 := bstep (se 2 (by rfl) ⟨2489829, by rfl⟩ : syracuseStep 6639545 = 4979659) B4979659
theorem B4426363 : Blo 2181435 4426363 := bstep (se 1 (by rfl) ⟨3319772, by rfl⟩ : syracuseStep 4426363 = 6639545) B6639545
theorem B5901817 : Blo 2181435 5901817 := bstep (se 2 (by rfl) ⟨2213181, by rfl⟩ : syracuseStep 5901817 = 4426363) B4426363
theorem B7869089 : Blo 2181435 7869089 := bstep (se 2 (by rfl) ⟨2950908, by rfl⟩ : syracuseStep 7869089 = 5901817) B5901817
theorem B5246059 : Blo 2181435 5246059 := bstep (se 1 (by rfl) ⟨3934544, by rfl⟩ : syracuseStep 5246059 = 7869089) B7869089
theorem B6994745 : Blo 2181435 6994745 := bstep (se 2 (by rfl) ⟨2623029, by rfl⟩ : syracuseStep 6994745 = 5246059) B5246059
theorem B4663163 : Blo 2181435 4663163 := bstep (se 1 (by rfl) ⟨3497372, by rfl⟩ : syracuseStep 4663163 = 6994745) B6994745
theorem B3108775 : Blo 2181435 3108775 := bstep (se 1 (by rfl) ⟨2331581, by rfl⟩ : syracuseStep 3108775 = 4663163) B4663163
theorem B4145033 : Blo 2181435 4145033 := bstep (se 2 (by rfl) ⟨1554387, by rfl⟩ : syracuseStep 4145033 = 3108775) B3108775
theorem B11053421 : Blo 2181435 11053421 := bstep (se 3 (by rfl) ⟨2072516, by rfl⟩ : syracuseStep 11053421 = 4145033) B4145033
theorem B7368947 : Blo 2181435 7368947 := bstep (se 1 (by rfl) ⟨5526710, by rfl⟩ : syracuseStep 7368947 = 11053421) B11053421
theorem B4912631 : Blo 2181435 4912631 := bstep (se 1 (by rfl) ⟨3684473, by rfl⟩ : syracuseStep 4912631 = 7368947) B7368947
theorem B3275087 : Blo 2181435 3275087 := bstep (se 1 (by rfl) ⟨2456315, by rfl⟩ : syracuseStep 3275087 = 4912631) B4912631
theorem B2183391 : Blo 2181435 2183391 := bstep (se 1 (by rfl) ⟨1637543, by rfl⟩ : syracuseStep 2183391 = 3275087) B3275087
theorem B3275093 : Blo 2181435 3275093 := bbase (se 10 (by rfl) ⟨4797, by rfl⟩ : syracuseStep 3275093 = 9595) (by norm_num)
theorem B2183395 : Blo 2181435 2183395 := bstep (se 1 (by rfl) ⟨1637546, by rfl⟩ : syracuseStep 2183395 = 3275093) B3275093
theorem B6217573 : Blo 2181435 6217573 := bbase (se 4 (by rfl) ⟨582897, by rfl⟩ : syracuseStep 6217573 = 1165795) (by norm_num)
theorem B8290097 : Blo 2181435 8290097 := bstep (se 2 (by rfl) ⟨3108786, by rfl⟩ : syracuseStep 8290097 = 6217573) B6217573
theorem B5526731 : Blo 2181435 5526731 := bstep (se 1 (by rfl) ⟨4145048, by rfl⟩ : syracuseStep 5526731 = 8290097) B8290097
theorem B3684487 : Blo 2181435 3684487 := bstep (se 1 (by rfl) ⟨2763365, by rfl⟩ : syracuseStep 3684487 = 5526731) B5526731
theorem B4912649 : Blo 2181435 4912649 := bstep (se 2 (by rfl) ⟨1842243, by rfl⟩ : syracuseStep 4912649 = 3684487) B3684487
theorem B3275099 : Blo 2181435 3275099 := bstep (se 1 (by rfl) ⟨2456324, by rfl⟩ : syracuseStep 3275099 = 4912649) B4912649
theorem B2183399 : Blo 2181435 2183399 := bstep (se 1 (by rfl) ⟨1637549, by rfl⟩ : syracuseStep 2183399 = 3275099) B3275099
theorem B2456329 : Blo 2181435 2456329 := bbase (se 2 (by rfl) ⟨921123, by rfl⟩ : syracuseStep 2456329 = 1842247) (by norm_num)
theorem B3275105 : Blo 2181435 3275105 := bstep (se 2 (by rfl) ⟨1228164, by rfl⟩ : syracuseStep 3275105 = 2456329) B2456329
theorem B2183403 : Blo 2181435 2183403 := bstep (se 1 (by rfl) ⟨1637552, by rfl⟩ : syracuseStep 2183403 = 3275105) B3275105
theorem B8852789 : Blo 2181435 8852789 := bbase (se 5 (by rfl) ⟨414974, by rfl⟩ : syracuseStep 8852789 = 829949) (by norm_num)
theorem B5901859 : Blo 2181435 5901859 := bstep (se 1 (by rfl) ⟨4426394, by rfl⟩ : syracuseStep 5901859 = 8852789) B8852789
theorem B7869145 : Blo 2181435 7869145 := bstep (se 2 (by rfl) ⟨2950929, by rfl⟩ : syracuseStep 7869145 = 5901859) B5901859
theorem B10492193 : Blo 2181435 10492193 := bstep (se 2 (by rfl) ⟨3934572, by rfl⟩ : syracuseStep 10492193 = 7869145) B7869145
theorem B27979181 : Blo 2181435 27979181 := bstep (se 3 (by rfl) ⟨5246096, by rfl⟩ : syracuseStep 27979181 = 10492193) B10492193
theorem B18652787 : Blo 2181435 18652787 := bstep (se 1 (by rfl) ⟨13989590, by rfl⟩ : syracuseStep 18652787 = 27979181) B27979181
theorem B12435191 : Blo 2181435 12435191 := bstep (se 1 (by rfl) ⟨9326393, by rfl⟩ : syracuseStep 12435191 = 18652787) B18652787
theorem B8290127 : Blo 2181435 8290127 := bstep (se 1 (by rfl) ⟨6217595, by rfl⟩ : syracuseStep 8290127 = 12435191) B12435191
theorem B5526751 : Blo 2181435 5526751 := bstep (se 1 (by rfl) ⟨4145063, by rfl⟩ : syracuseStep 5526751 = 8290127) B8290127
theorem B7369001 : Blo 2181435 7369001 := bstep (se 2 (by rfl) ⟨2763375, by rfl⟩ : syracuseStep 7369001 = 5526751) B5526751
theorem B4912667 : Blo 2181435 4912667 := bstep (se 1 (by rfl) ⟨3684500, by rfl⟩ : syracuseStep 4912667 = 7369001) B7369001
theorem B3275111 : Blo 2181435 3275111 := bstep (se 1 (by rfl) ⟨2456333, by rfl⟩ : syracuseStep 3275111 = 4912667) B4912667
theorem B2183407 : Blo 2181435 2183407 := bstep (se 1 (by rfl) ⟨1637555, by rfl⟩ : syracuseStep 2183407 = 3275111) B3275111
theorem B3275117 : Blo 2181435 3275117 := bbase (se 3 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 3275117 = 1228169) (by norm_num)
theorem B2183411 : Blo 2181435 2183411 := bstep (se 1 (by rfl) ⟨1637558, by rfl⟩ : syracuseStep 2183411 = 3275117) B3275117
theorem B4912685 : Blo 2181435 4912685 := bbase (se 3 (by rfl) ⟨921128, by rfl⟩ : syracuseStep 4912685 = 1842257) (by norm_num)
theorem B3275123 : Blo 2181435 3275123 := bstep (se 1 (by rfl) ⟨2456342, by rfl⟩ : syracuseStep 3275123 = 4912685) B4912685
theorem B2183415 : Blo 2181435 2183415 := bstep (se 1 (by rfl) ⟨1637561, by rfl⟩ : syracuseStep 2183415 = 3275123) B3275123
theorem B10657637 : Blo 2181435 10657637 := bbase (se 4 (by rfl) ⟨999153, by rfl⟩ : syracuseStep 10657637 = 1998307) (by norm_num)
theorem B7105091 : Blo 2181435 7105091 := bstep (se 1 (by rfl) ⟨5328818, by rfl⟩ : syracuseStep 7105091 = 10657637) B10657637
theorem B18946909 : Blo 2181435 18946909 := bstep (se 3 (by rfl) ⟨3552545, by rfl⟩ : syracuseStep 18946909 = 7105091) B7105091
theorem B25262545 : Blo 2181435 25262545 := bstep (se 2 (by rfl) ⟨9473454, by rfl⟩ : syracuseStep 25262545 = 18946909) B18946909
theorem B33683393 : Blo 2181435 33683393 := bstep (se 2 (by rfl) ⟨12631272, by rfl⟩ : syracuseStep 33683393 = 25262545) B25262545
theorem B22455595 : Blo 2181435 22455595 := bstep (se 1 (by rfl) ⟨16841696, by rfl⟩ : syracuseStep 22455595 = 33683393) B33683393
theorem B119763173 : Blo 2181435 119763173 := bstep (se 4 (by rfl) ⟨11227797, by rfl⟩ : syracuseStep 119763173 = 22455595) B22455595
theorem B79842115 : Blo 2181435 79842115 := bstep (se 1 (by rfl) ⟨59881586, by rfl⟩ : syracuseStep 79842115 = 119763173) B119763173
theorem B106456153 : Blo 2181435 106456153 := bstep (se 2 (by rfl) ⟨39921057, by rfl⟩ : syracuseStep 106456153 = 79842115) B79842115
theorem B141941537 : Blo 2181435 141941537 := bstep (se 2 (by rfl) ⟨53228076, by rfl⟩ : syracuseStep 141941537 = 106456153) B106456153
theorem B94627691 : Blo 2181435 94627691 := bstep (se 1 (by rfl) ⟨70970768, by rfl⟩ : syracuseStep 94627691 = 141941537) B141941537
theorem B63085127 : Blo 2181435 63085127 := bstep (se 1 (by rfl) ⟨47313845, by rfl⟩ : syracuseStep 63085127 = 94627691) B94627691
theorem B672908021 : Blo 2181435 672908021 := bstep (se 5 (by rfl) ⟨31542563, by rfl⟩ : syracuseStep 672908021 = 63085127) B63085127
theorem B448605347 : Blo 2181435 448605347 := bstep (se 1 (by rfl) ⟨336454010, by rfl⟩ : syracuseStep 448605347 = 672908021) B672908021
theorem B4785123701 : Blo 2181435 4785123701 := bstep (se 5 (by rfl) ⟨224302673, by rfl⟩ : syracuseStep 4785123701 = 448605347) B448605347
theorem B3190082467 : Blo 2181435 3190082467 := bstep (se 1 (by rfl) ⟨2392561850, by rfl⟩ : syracuseStep 3190082467 = 4785123701) B4785123701
theorem B4253443289 : Blo 2181435 4253443289 := bstep (se 2 (by rfl) ⟨1595041233, by rfl⟩ : syracuseStep 4253443289 = 3190082467) B3190082467
theorem B2835628859 : Blo 2181435 2835628859 := bstep (se 1 (by rfl) ⟨2126721644, by rfl⟩ : syracuseStep 2835628859 = 4253443289) B4253443289
theorem B1890419239 : Blo 2181435 1890419239 := bstep (se 1 (by rfl) ⟨1417814429, by rfl⟩ : syracuseStep 1890419239 = 2835628859) B2835628859
theorem B2520558985 : Blo 2181435 2520558985 := bstep (se 2 (by rfl) ⟨945209619, by rfl⟩ : syracuseStep 2520558985 = 1890419239) B1890419239
theorem B3360745313 : Blo 2181435 3360745313 := bstep (se 2 (by rfl) ⟨1260279492, by rfl⟩ : syracuseStep 3360745313 = 2520558985) B2520558985
theorem B2240496875 : Blo 2181435 2240496875 := bstep (se 1 (by rfl) ⟨1680372656, by rfl⟩ : syracuseStep 2240496875 = 3360745313) B3360745313
theorem B1493664583 : Blo 2181435 1493664583 := bstep (se 1 (by rfl) ⟨1120248437, by rfl⟩ : syracuseStep 1493664583 = 2240496875) B2240496875
theorem B1991552777 : Blo 2181435 1991552777 := bstep (se 2 (by rfl) ⟨746832291, by rfl⟩ : syracuseStep 1991552777 = 1493664583) B1493664583
theorem B1327701851 : Blo 2181435 1327701851 := bstep (se 1 (by rfl) ⟨995776388, by rfl⟩ : syracuseStep 1327701851 = 1991552777) B1991552777
theorem B885134567 : Blo 2181435 885134567 := bstep (se 1 (by rfl) ⟨663850925, by rfl⟩ : syracuseStep 885134567 = 1327701851) B1327701851
theorem B590089711 : Blo 2181435 590089711 := bstep (se 1 (by rfl) ⟨442567283, by rfl⟩ : syracuseStep 590089711 = 885134567) B885134567
theorem B786786281 : Blo 2181435 786786281 := bstep (se 2 (by rfl) ⟨295044855, by rfl⟩ : syracuseStep 786786281 = 590089711) B590089711
theorem B524524187 : Blo 2181435 524524187 := bstep (se 1 (by rfl) ⟨393393140, by rfl⟩ : syracuseStep 524524187 = 786786281) B786786281
theorem B349682791 : Blo 2181435 349682791 := bstep (se 1 (by rfl) ⟨262262093, by rfl⟩ : syracuseStep 349682791 = 524524187) B524524187
theorem B466243721 : Blo 2181435 466243721 := bstep (se 2 (by rfl) ⟨174841395, by rfl⟩ : syracuseStep 466243721 = 349682791) B349682791
theorem B310829147 : Blo 2181435 310829147 := bstep (se 1 (by rfl) ⟨233121860, by rfl⟩ : syracuseStep 310829147 = 466243721) B466243721
theorem B207219431 : Blo 2181435 207219431 := bstep (se 1 (by rfl) ⟨155414573, by rfl⟩ : syracuseStep 207219431 = 310829147) B310829147
theorem B552585149 : Blo 2181435 552585149 := bstep (se 3 (by rfl) ⟨103609715, by rfl⟩ : syracuseStep 552585149 = 207219431) B207219431
theorem B368390099 : Blo 2181435 368390099 := bstep (se 1 (by rfl) ⟨276292574, by rfl⟩ : syracuseStep 368390099 = 552585149) B552585149
theorem B245593399 : Blo 2181435 245593399 := bstep (se 1 (by rfl) ⟨184195049, by rfl⟩ : syracuseStep 245593399 = 368390099) B368390099
theorem B327457865 : Blo 2181435 327457865 := bstep (se 2 (by rfl) ⟨122796699, by rfl⟩ : syracuseStep 327457865 = 245593399) B245593399
theorem B218305243 : Blo 2181435 218305243 := bstep (se 1 (by rfl) ⟨163728932, by rfl⟩ : syracuseStep 218305243 = 327457865) B327457865
theorem B291073657 : Blo 2181435 291073657 := bstep (se 2 (by rfl) ⟨109152621, by rfl⟩ : syracuseStep 291073657 = 218305243) B218305243
theorem B388098209 : Blo 2181435 388098209 := bstep (se 2 (by rfl) ⟨145536828, by rfl⟩ : syracuseStep 388098209 = 291073657) B291073657
theorem B258732139 : Blo 2181435 258732139 := bstep (se 1 (by rfl) ⟨194049104, by rfl⟩ : syracuseStep 258732139 = 388098209) B388098209
theorem B344976185 : Blo 2181435 344976185 := bstep (se 2 (by rfl) ⟨129366069, by rfl⟩ : syracuseStep 344976185 = 258732139) B258732139
theorem B229984123 : Blo 2181435 229984123 := bstep (se 1 (by rfl) ⟨172488092, by rfl⟩ : syracuseStep 229984123 = 344976185) B344976185
theorem B306645497 : Blo 2181435 306645497 := bstep (se 2 (by rfl) ⟨114992061, by rfl⟩ : syracuseStep 306645497 = 229984123) B229984123
theorem B204430331 : Blo 2181435 204430331 := bstep (se 1 (by rfl) ⟨153322748, by rfl⟩ : syracuseStep 204430331 = 306645497) B306645497
theorem B136286887 : Blo 2181435 136286887 := bstep (se 1 (by rfl) ⟨102215165, by rfl⟩ : syracuseStep 136286887 = 204430331) B204430331
theorem B181715849 : Blo 2181435 181715849 := bstep (se 2 (by rfl) ⟨68143443, by rfl⟩ : syracuseStep 181715849 = 136286887) B136286887
theorem B121143899 : Blo 2181435 121143899 := bstep (se 1 (by rfl) ⟨90857924, by rfl⟩ : syracuseStep 121143899 = 181715849) B181715849
theorem B80762599 : Blo 2181435 80762599 := bstep (se 1 (by rfl) ⟨60571949, by rfl⟩ : syracuseStep 80762599 = 121143899) B121143899
theorem B107683465 : Blo 2181435 107683465 := bstep (se 2 (by rfl) ⟨40381299, by rfl⟩ : syracuseStep 107683465 = 80762599) B80762599
theorem B143577953 : Blo 2181435 143577953 := bstep (se 2 (by rfl) ⟨53841732, by rfl⟩ : syracuseStep 143577953 = 107683465) B107683465
theorem B95718635 : Blo 2181435 95718635 := bstep (se 1 (by rfl) ⟨71788976, by rfl⟩ : syracuseStep 95718635 = 143577953) B143577953
theorem B63812423 : Blo 2181435 63812423 := bstep (se 1 (by rfl) ⟨47859317, by rfl⟩ : syracuseStep 63812423 = 95718635) B95718635
theorem B42541615 : Blo 2181435 42541615 := bstep (se 1 (by rfl) ⟨31906211, by rfl⟩ : syracuseStep 42541615 = 63812423) B63812423
theorem B56722153 : Blo 2181435 56722153 := bstep (se 2 (by rfl) ⟨21270807, by rfl⟩ : syracuseStep 56722153 = 42541615) B42541615
theorem B75629537 : Blo 2181435 75629537 := bstep (se 2 (by rfl) ⟨28361076, by rfl⟩ : syracuseStep 75629537 = 56722153) B56722153
theorem B50419691 : Blo 2181435 50419691 := bstep (se 1 (by rfl) ⟨37814768, by rfl⟩ : syracuseStep 50419691 = 75629537) B75629537
theorem B33613127 : Blo 2181435 33613127 := bstep (se 1 (by rfl) ⟨25209845, by rfl⟩ : syracuseStep 33613127 = 50419691) B50419691
theorem B22408751 : Blo 2181435 22408751 := bstep (se 1 (by rfl) ⟨16806563, by rfl⟩ : syracuseStep 22408751 = 33613127) B33613127
theorem B14939167 : Blo 2181435 14939167 := bstep (se 1 (by rfl) ⟨11204375, by rfl⟩ : syracuseStep 14939167 = 22408751) B22408751
theorem B19918889 : Blo 2181435 19918889 := bstep (se 2 (by rfl) ⟨7469583, by rfl⟩ : syracuseStep 19918889 = 14939167) B14939167
theorem B13279259 : Blo 2181435 13279259 := bstep (se 1 (by rfl) ⟨9959444, by rfl⟩ : syracuseStep 13279259 = 19918889) B19918889
theorem B35411357 : Blo 2181435 35411357 := bstep (se 3 (by rfl) ⟨6639629, by rfl⟩ : syracuseStep 35411357 = 13279259) B13279259
theorem B23607571 : Blo 2181435 23607571 := bstep (se 1 (by rfl) ⟨17705678, by rfl⟩ : syracuseStep 23607571 = 35411357) B35411357
theorem B31476761 : Blo 2181435 31476761 := bstep (se 2 (by rfl) ⟨11803785, by rfl⟩ : syracuseStep 31476761 = 23607571) B23607571
theorem B20984507 : Blo 2181435 20984507 := bstep (se 1 (by rfl) ⟨15738380, by rfl⟩ : syracuseStep 20984507 = 31476761) B31476761
theorem B13989671 : Blo 2181435 13989671 := bstep (se 1 (by rfl) ⟨10492253, by rfl⟩ : syracuseStep 13989671 = 20984507) B20984507
theorem B9326447 : Blo 2181435 9326447 := bstep (se 1 (by rfl) ⟨6994835, by rfl⟩ : syracuseStep 9326447 = 13989671) B13989671
theorem B6217631 : Blo 2181435 6217631 := bstep (se 1 (by rfl) ⟨4663223, by rfl⟩ : syracuseStep 6217631 = 9326447) B9326447
theorem B4145087 : Blo 2181435 4145087 := bstep (se 1 (by rfl) ⟨3108815, by rfl⟩ : syracuseStep 4145087 = 6217631) B6217631
theorem B2763391 : Blo 2181435 2763391 := bstep (se 1 (by rfl) ⟨2072543, by rfl⟩ : syracuseStep 2763391 = 4145087) B4145087
theorem B3684521 : Blo 2181435 3684521 := bstep (se 2 (by rfl) ⟨1381695, by rfl⟩ : syracuseStep 3684521 = 2763391) B2763391
theorem B2456347 : Blo 2181435 2456347 := bstep (se 1 (by rfl) ⟨1842260, by rfl⟩ : syracuseStep 2456347 = 3684521) B3684521
theorem B3275129 : Blo 2181435 3275129 := bstep (se 2 (by rfl) ⟨1228173, by rfl⟩ : syracuseStep 3275129 = 2456347) B2456347
theorem B2183419 : Blo 2181435 2183419 := bstep (se 1 (by rfl) ⟨1637564, by rfl⟩ : syracuseStep 2183419 = 3275129) B3275129
theorem B3151237 : Blo 2181435 3151237 := bbase (se 4 (by rfl) ⟨295428, by rfl⟩ : syracuseStep 3151237 = 590857) (by norm_num)
theorem B4201649 : Blo 2181435 4201649 := bstep (se 2 (by rfl) ⟨1575618, by rfl⟩ : syracuseStep 4201649 = 3151237) B3151237
theorem B2801099 : Blo 2181435 2801099 := bstep (se 1 (by rfl) ⟨2100824, by rfl⟩ : syracuseStep 2801099 = 4201649) B4201649
theorem B7469597 : Blo 2181435 7469597 := bstep (se 3 (by rfl) ⟨1400549, by rfl⟩ : syracuseStep 7469597 = 2801099) B2801099
theorem B4979731 : Blo 2181435 4979731 := bstep (se 1 (by rfl) ⟨3734798, by rfl⟩ : syracuseStep 4979731 = 7469597) B7469597
theorem B6639641 : Blo 2181435 6639641 := bstep (se 2 (by rfl) ⟨2489865, by rfl⟩ : syracuseStep 6639641 = 4979731) B4979731
theorem B4426427 : Blo 2181435 4426427 := bstep (se 1 (by rfl) ⟨3319820, by rfl⟩ : syracuseStep 4426427 = 6639641) B6639641
theorem B11803805 : Blo 2181435 11803805 := bstep (se 3 (by rfl) ⟨2213213, by rfl⟩ : syracuseStep 11803805 = 4426427) B4426427
theorem B7869203 : Blo 2181435 7869203 := bstep (se 1 (by rfl) ⟨5901902, by rfl⟩ : syracuseStep 7869203 = 11803805) B11803805
theorem B5246135 : Blo 2181435 5246135 := bstep (se 1 (by rfl) ⟨3934601, by rfl⟩ : syracuseStep 5246135 = 7869203) B7869203
theorem B3497423 : Blo 2181435 3497423 := bstep (se 1 (by rfl) ⟨2623067, by rfl⟩ : syracuseStep 3497423 = 5246135) B5246135
theorem B37305845 : Blo 2181435 37305845 := bstep (se 5 (by rfl) ⟨1748711, by rfl⟩ : syracuseStep 37305845 = 3497423) B3497423
theorem B24870563 : Blo 2181435 24870563 := bstep (se 1 (by rfl) ⟨18652922, by rfl⟩ : syracuseStep 24870563 = 37305845) B37305845
theorem B16580375 : Blo 2181435 16580375 := bstep (se 1 (by rfl) ⟨12435281, by rfl⟩ : syracuseStep 16580375 = 24870563) B24870563
theorem B11053583 : Blo 2181435 11053583 := bstep (se 1 (by rfl) ⟨8290187, by rfl⟩ : syracuseStep 11053583 = 16580375) B16580375
theorem B7369055 : Blo 2181435 7369055 := bstep (se 1 (by rfl) ⟨5526791, by rfl⟩ : syracuseStep 7369055 = 11053583) B11053583
theorem B4912703 : Blo 2181435 4912703 := bstep (se 1 (by rfl) ⟨3684527, by rfl⟩ : syracuseStep 4912703 = 7369055) B7369055
theorem B3275135 : Blo 2181435 3275135 := bstep (se 1 (by rfl) ⟨2456351, by rfl⟩ : syracuseStep 3275135 = 4912703) B4912703
theorem B2183423 : Blo 2181435 2183423 := bstep (se 1 (by rfl) ⟨1637567, by rfl⟩ : syracuseStep 2183423 = 3275135) B3275135
theorem B3275141 : Blo 2181435 3275141 := bbase (se 4 (by rfl) ⟨307044, by rfl⟩ : syracuseStep 3275141 = 614089) (by norm_num)
theorem B2183427 : Blo 2181435 2183427 := bstep (se 1 (by rfl) ⟨1637570, by rfl⟩ : syracuseStep 2183427 = 3275141) B3275141
theorem B3684541 : Blo 2181435 3684541 := bbase (se 3 (by rfl) ⟨690851, by rfl⟩ : syracuseStep 3684541 = 1381703) (by norm_num)
theorem B4912721 : Blo 2181435 4912721 := bstep (se 2 (by rfl) ⟨1842270, by rfl⟩ : syracuseStep 4912721 = 3684541) B3684541
theorem B3275147 : Blo 2181435 3275147 := bstep (se 1 (by rfl) ⟨2456360, by rfl⟩ : syracuseStep 3275147 = 4912721) B4912721
theorem B2183431 : Blo 2181435 2183431 := bstep (se 1 (by rfl) ⟨1637573, by rfl⟩ : syracuseStep 2183431 = 3275147) B3275147
theorem B2456365 : Blo 2181435 2456365 := bbase (se 3 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 2456365 = 921137) (by norm_num)
theorem B3275153 : Blo 2181435 3275153 := bstep (se 2 (by rfl) ⟨1228182, by rfl⟩ : syracuseStep 3275153 = 2456365) B2456365
theorem B2183435 : Blo 2181435 2183435 := bstep (se 1 (by rfl) ⟨1637576, by rfl⟩ : syracuseStep 2183435 = 3275153) B3275153
theorem C0 (j : ℕ) (h1 : 545358 ≤ j) (h2 : j ≤ 545858) : Blo 2181435 (4 * j + 3) := by
  interval_cases j
  · exact B2181435
  · exact B2181439
  · exact B2181443
  · exact B2181447
  · exact B2181451
  · exact B2181455
  · exact B2181459
  · exact B2181463
  · exact B2181467
  · exact B2181471
  · exact B2181475
  · exact B2181479
  · exact B2181483
  · exact B2181487
  · exact B2181491
  · exact B2181495
  · exact B2181499
  · exact B2181503
  · exact B2181507
  · exact B2181511
  · exact B2181515
  · exact B2181519
  · exact B2181523
  · exact B2181527
  · exact B2181531
  · exact B2181535
  · exact B2181539
  · exact B2181543
  · exact B2181547
  · exact B2181551
  · exact B2181555
  · exact B2181559
  · exact B2181563
  · exact B2181567
  · exact B2181571
  · exact B2181575
  · exact B2181579
  · exact B2181583
  · exact B2181587
  · exact B2181591
  · exact B2181595
  · exact B2181599
  · exact B2181603
  · exact B2181607
  · exact B2181611
  · exact B2181615
  · exact B2181619
  · exact B2181623
  · exact B2181627
  · exact B2181631
  · exact B2181635
  · exact B2181639
  · exact B2181643
  · exact B2181647
  · exact B2181651
  · exact B2181655
  · exact B2181659
  · exact B2181663
  · exact B2181667
  · exact B2181671
  · exact B2181675
  · exact B2181679
  · exact B2181683
  · exact B2181687
  · exact B2181691
  · exact B2181695
  · exact B2181699
  · exact B2181703
  · exact B2181707
  · exact B2181711
  · exact B2181715
  · exact B2181719
  · exact B2181723
  · exact B2181727
  · exact B2181731
  · exact B2181735
  · exact B2181739
  · exact B2181743
  · exact B2181747
  · exact B2181751
  · exact B2181755
  · exact B2181759
  · exact B2181763
  · exact B2181767
  · exact B2181771
  · exact B2181775
  · exact B2181779
  · exact B2181783
  · exact B2181787
  · exact B2181791
  · exact B2181795
  · exact B2181799
  · exact B2181803
  · exact B2181807
  · exact B2181811
  · exact B2181815
  · exact B2181819
  · exact B2181823
  · exact B2181827
  · exact B2181831
  · exact B2181835
  · exact B2181839
  · exact B2181843
  · exact B2181847
  · exact B2181851
  · exact B2181855
  · exact B2181859
  · exact B2181863
  · exact B2181867
  · exact B2181871
  · exact B2181875
  · exact B2181879
  · exact B2181883
  · exact B2181887
  · exact B2181891
  · exact B2181895
  · exact B2181899
  · exact B2181903
  · exact B2181907
  · exact B2181911
  · exact B2181915
  · exact B2181919
  · exact B2181923
  · exact B2181927
  · exact B2181931
  · exact B2181935
  · exact B2181939
  · exact B2181943
  · exact B2181947
  · exact B2181951
  · exact B2181955
  · exact B2181959
  · exact B2181963
  · exact B2181967
  · exact B2181971
  · exact B2181975
  · exact B2181979
  · exact B2181983
  · exact B2181987
  · exact B2181991
  · exact B2181995
  · exact B2181999
  · exact B2182003
  · exact B2182007
  · exact B2182011
  · exact B2182015
  · exact B2182019
  · exact B2182023
  · exact B2182027
  · exact B2182031
  · exact B2182035
  · exact B2182039
  · exact B2182043
  · exact B2182047
  · exact B2182051
  · exact B2182055
  · exact B2182059
  · exact B2182063
  · exact B2182067
  · exact B2182071
  · exact B2182075
  · exact B2182079
  · exact B2182083
  · exact B2182087
  · exact B2182091
  · exact B2182095
  · exact B2182099
  · exact B2182103
  · exact B2182107
  · exact B2182111
  · exact B2182115
  · exact B2182119
  · exact B2182123
  · exact B2182127
  · exact B2182131
  · exact B2182135
  · exact B2182139
  · exact B2182143
  · exact B2182147
  · exact B2182151
  · exact B2182155
  · exact B2182159
  · exact B2182163
  · exact B2182167
  · exact B2182171
  · exact B2182175
  · exact B2182179
  · exact B2182183
  · exact B2182187
  · exact B2182191
  · exact B2182195
  · exact B2182199
  · exact B2182203
  · exact B2182207
  · exact B2182211
  · exact B2182215
  · exact B2182219
  · exact B2182223
  · exact B2182227
  · exact B2182231
  · exact B2182235
  · exact B2182239
  · exact B2182243
  · exact B2182247
  · exact B2182251
  · exact B2182255
  · exact B2182259
  · exact B2182263
  · exact B2182267
  · exact B2182271
  · exact B2182275
  · exact B2182279
  · exact B2182283
  · exact B2182287
  · exact B2182291
  · exact B2182295
  · exact B2182299
  · exact B2182303
  · exact B2182307
  · exact B2182311
  · exact B2182315
  · exact B2182319
  · exact B2182323
  · exact B2182327
  · exact B2182331
  · exact B2182335
  · exact B2182339
  · exact B2182343
  · exact B2182347
  · exact B2182351
  · exact B2182355
  · exact B2182359
  · exact B2182363
  · exact B2182367
  · exact B2182371
  · exact B2182375
  · exact B2182379
  · exact B2182383
  · exact B2182387
  · exact B2182391
  · exact B2182395
  · exact B2182399
  · exact B2182403
  · exact B2182407
  · exact B2182411
  · exact B2182415
  · exact B2182419
  · exact B2182423
  · exact B2182427
  · exact B2182431
  · exact B2182435
  · exact B2182439
  · exact B2182443
  · exact B2182447
  · exact B2182451
  · exact B2182455
  · exact B2182459
  · exact B2182463
  · exact B2182467
  · exact B2182471
  · exact B2182475
  · exact B2182479
  · exact B2182483
  · exact B2182487
  · exact B2182491
  · exact B2182495
  · exact B2182499
  · exact B2182503
  · exact B2182507
  · exact B2182511
  · exact B2182515
  · exact B2182519
  · exact B2182523
  · exact B2182527
  · exact B2182531
  · exact B2182535
  · exact B2182539
  · exact B2182543
  · exact B2182547
  · exact B2182551
  · exact B2182555
  · exact B2182559
  · exact B2182563
  · exact B2182567
  · exact B2182571
  · exact B2182575
  · exact B2182579
  · exact B2182583
  · exact B2182587
  · exact B2182591
  · exact B2182595
  · exact B2182599
  · exact B2182603
  · exact B2182607
  · exact B2182611
  · exact B2182615
  · exact B2182619
  · exact B2182623
  · exact B2182627
  · exact B2182631
  · exact B2182635
  · exact B2182639
  · exact B2182643
  · exact B2182647
  · exact B2182651
  · exact B2182655
  · exact B2182659
  · exact B2182663
  · exact B2182667
  · exact B2182671
  · exact B2182675
  · exact B2182679
  · exact B2182683
  · exact B2182687
  · exact B2182691
  · exact B2182695
  · exact B2182699
  · exact B2182703
  · exact B2182707
  · exact B2182711
  · exact B2182715
  · exact B2182719
  · exact B2182723
  · exact B2182727
  · exact B2182731
  · exact B2182735
  · exact B2182739
  · exact B2182743
  · exact B2182747
  · exact B2182751
  · exact B2182755
  · exact B2182759
  · exact B2182763
  · exact B2182767
  · exact B2182771
  · exact B2182775
  · exact B2182779
  · exact B2182783
  · exact B2182787
  · exact B2182791
  · exact B2182795
  · exact B2182799
  · exact B2182803
  · exact B2182807
  · exact B2182811
  · exact B2182815
  · exact B2182819
  · exact B2182823
  · exact B2182827
  · exact B2182831
  · exact B2182835
  · exact B2182839
  · exact B2182843
  · exact B2182847
  · exact B2182851
  · exact B2182855
  · exact B2182859
  · exact B2182863
  · exact B2182867
  · exact B2182871
  · exact B2182875
  · exact B2182879
  · exact B2182883
  · exact B2182887
  · exact B2182891
  · exact B2182895
  · exact B2182899
  · exact B2182903
  · exact B2182907
  · exact B2182911
  · exact B2182915
  · exact B2182919
  · exact B2182923
  · exact B2182927
  · exact B2182931
  · exact B2182935
  · exact B2182939
  · exact B2182943
  · exact B2182947
  · exact B2182951
  · exact B2182955
  · exact B2182959
  · exact B2182963
  · exact B2182967
  · exact B2182971
  · exact B2182975
  · exact B2182979
  · exact B2182983
  · exact B2182987
  · exact B2182991
  · exact B2182995
  · exact B2182999
  · exact B2183003
  · exact B2183007
  · exact B2183011
  · exact B2183015
  · exact B2183019
  · exact B2183023
  · exact B2183027
  · exact B2183031
  · exact B2183035
  · exact B2183039
  · exact B2183043
  · exact B2183047
  · exact B2183051
  · exact B2183055
  · exact B2183059
  · exact B2183063
  · exact B2183067
  · exact B2183071
  · exact B2183075
  · exact B2183079
  · exact B2183083
  · exact B2183087
  · exact B2183091
  · exact B2183095
  · exact B2183099
  · exact B2183103
  · exact B2183107
  · exact B2183111
  · exact B2183115
  · exact B2183119
  · exact B2183123
  · exact B2183127
  · exact B2183131
  · exact B2183135
  · exact B2183139
  · exact B2183143
  · exact B2183147
  · exact B2183151
  · exact B2183155
  · exact B2183159
  · exact B2183163
  · exact B2183167
  · exact B2183171
  · exact B2183175
  · exact B2183179
  · exact B2183183
  · exact B2183187
  · exact B2183191
  · exact B2183195
  · exact B2183199
  · exact B2183203
  · exact B2183207
  · exact B2183211
  · exact B2183215
  · exact B2183219
  · exact B2183223
  · exact B2183227
  · exact B2183231
  · exact B2183235
  · exact B2183239
  · exact B2183243
  · exact B2183247
  · exact B2183251
  · exact B2183255
  · exact B2183259
  · exact B2183263
  · exact B2183267
  · exact B2183271
  · exact B2183275
  · exact B2183279
  · exact B2183283
  · exact B2183287
  · exact B2183291
  · exact B2183295
  · exact B2183299
  · exact B2183303
  · exact B2183307
  · exact B2183311
  · exact B2183315
  · exact B2183319
  · exact B2183323
  · exact B2183327
  · exact B2183331
  · exact B2183335
  · exact B2183339
  · exact B2183343
  · exact B2183347
  · exact B2183351
  · exact B2183355
  · exact B2183359
  · exact B2183363
  · exact B2183367
  · exact B2183371
  · exact B2183375
  · exact B2183379
  · exact B2183383
  · exact B2183387
  · exact B2183391
  · exact B2183395
  · exact B2183399
  · exact B2183403
  · exact B2183407
  · exact B2183411
  · exact B2183415
  · exact B2183419
  · exact B2183423
  · exact B2183427
  · exact B2183431
  · exact B2183435
theorem solution (m : ℕ) (hlo : 2181435 ≤ m) (hhi : m ≤ 2183435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 545358 ≤ j := by omega
    have hj2 : j ≤ 545858 := by omega
    have hb : Blo 2181435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
