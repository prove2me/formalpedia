-- Prove2me | solution 1 for syracuse_descends_range_2213435_2215435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:32.222186+00:00
-- url     : https://prove2.me/submissions/18416be4-aca6-4470-95a5-47a8b75288e3

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

theorem B3735173 : Blo 2213435 3735173 := bbase (se 4 (by rfl) ⟨350172, by rfl⟩ : syracuseStep 3735173 = 700345) (by norm_num)
theorem B2490115 : Blo 2213435 2490115 := bstep (se 1 (by rfl) ⟨1867586, by rfl⟩ : syracuseStep 2490115 = 3735173) B3735173
theorem B3320153 : Blo 2213435 3320153 := bstep (se 2 (by rfl) ⟨1245057, by rfl⟩ : syracuseStep 3320153 = 2490115) B2490115
theorem B2213435 : Blo 2213435 2213435 := bstep (se 1 (by rfl) ⟨1660076, by rfl⟩ : syracuseStep 2213435 = 3320153) B3320153
theorem B16808309 : Blo 2213435 16808309 := bbase (se 5 (by rfl) ⟨787889, by rfl⟩ : syracuseStep 16808309 = 1575779) (by norm_num)
theorem B11205539 : Blo 2213435 11205539 := bstep (se 1 (by rfl) ⟨8404154, by rfl⟩ : syracuseStep 11205539 = 16808309) B16808309
theorem B7470359 : Blo 2213435 7470359 := bstep (se 1 (by rfl) ⟨5602769, by rfl⟩ : syracuseStep 7470359 = 11205539) B11205539
theorem B4980239 : Blo 2213435 4980239 := bstep (se 1 (by rfl) ⟨3735179, by rfl⟩ : syracuseStep 4980239 = 7470359) B7470359
theorem B3320159 : Blo 2213435 3320159 := bstep (se 1 (by rfl) ⟨2490119, by rfl⟩ : syracuseStep 3320159 = 4980239) B4980239
theorem B2213439 : Blo 2213435 2213439 := bstep (se 1 (by rfl) ⟨1660079, by rfl⟩ : syracuseStep 2213439 = 3320159) B3320159
theorem B3320165 : Blo 2213435 3320165 := bbase (se 4 (by rfl) ⟨311265, by rfl⟩ : syracuseStep 3320165 = 622531) (by norm_num)
theorem B2213443 : Blo 2213435 2213443 := bstep (se 1 (by rfl) ⟨1660082, by rfl⟩ : syracuseStep 2213443 = 3320165) B3320165
theorem B4202093 : Blo 2213435 4202093 := bbase (se 3 (by rfl) ⟨787892, by rfl⟩ : syracuseStep 4202093 = 1575785) (by norm_num)
theorem B2801395 : Blo 2213435 2801395 := bstep (se 1 (by rfl) ⟨2101046, by rfl⟩ : syracuseStep 2801395 = 4202093) B4202093
theorem B3735193 : Blo 2213435 3735193 := bstep (se 2 (by rfl) ⟨1400697, by rfl⟩ : syracuseStep 3735193 = 2801395) B2801395
theorem B4980257 : Blo 2213435 4980257 := bstep (se 2 (by rfl) ⟨1867596, by rfl⟩ : syracuseStep 4980257 = 3735193) B3735193
theorem B3320171 : Blo 2213435 3320171 := bstep (se 1 (by rfl) ⟨2490128, by rfl⟩ : syracuseStep 3320171 = 4980257) B4980257
theorem B2213447 : Blo 2213435 2213447 := bstep (se 1 (by rfl) ⟨1660085, by rfl⟩ : syracuseStep 2213447 = 3320171) B3320171
theorem B2490133 : Blo 2213435 2490133 := bbase (se 6 (by rfl) ⟨58362, by rfl⟩ : syracuseStep 2490133 = 116725) (by norm_num)
theorem B3320177 : Blo 2213435 3320177 := bstep (se 2 (by rfl) ⟨1245066, by rfl⟩ : syracuseStep 3320177 = 2490133) B2490133
theorem B2213451 : Blo 2213435 2213451 := bstep (se 1 (by rfl) ⟨1660088, by rfl⟩ : syracuseStep 2213451 = 3320177) B3320177
theorem B2801405 : Blo 2213435 2801405 := bbase (se 3 (by rfl) ⟨525263, by rfl⟩ : syracuseStep 2801405 = 1050527) (by norm_num)
theorem B7470413 : Blo 2213435 7470413 := bstep (se 3 (by rfl) ⟨1400702, by rfl⟩ : syracuseStep 7470413 = 2801405) B2801405
theorem B4980275 : Blo 2213435 4980275 := bstep (se 1 (by rfl) ⟨3735206, by rfl⟩ : syracuseStep 4980275 = 7470413) B7470413
theorem B3320183 : Blo 2213435 3320183 := bstep (se 1 (by rfl) ⟨2490137, by rfl⟩ : syracuseStep 3320183 = 4980275) B4980275
theorem B2213455 : Blo 2213435 2213455 := bstep (se 1 (by rfl) ⟨1660091, by rfl⟩ : syracuseStep 2213455 = 3320183) B3320183
theorem B3320189 : Blo 2213435 3320189 := bbase (se 3 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 3320189 = 1245071) (by norm_num)
theorem B2213459 : Blo 2213435 2213459 := bstep (se 1 (by rfl) ⟨1660094, by rfl⟩ : syracuseStep 2213459 = 3320189) B3320189
theorem B4980293 : Blo 2213435 4980293 := bbase (se 4 (by rfl) ⟨466902, by rfl⟩ : syracuseStep 4980293 = 933805) (by norm_num)
theorem B3320195 : Blo 2213435 3320195 := bstep (se 1 (by rfl) ⟨2490146, by rfl⟩ : syracuseStep 3320195 = 4980293) B4980293
theorem B2213463 : Blo 2213435 2213463 := bstep (se 1 (by rfl) ⟨1660097, by rfl⟩ : syracuseStep 2213463 = 3320195) B3320195
theorem B3545549 : Blo 2213435 3545549 := bbase (se 3 (by rfl) ⟨664790, by rfl⟩ : syracuseStep 3545549 = 1329581) (by norm_num)
theorem B2363699 : Blo 2213435 2363699 := bstep (se 1 (by rfl) ⟨1772774, by rfl⟩ : syracuseStep 2363699 = 3545549) B3545549
theorem B6303197 : Blo 2213435 6303197 := bstep (se 3 (by rfl) ⟨1181849, by rfl⟩ : syracuseStep 6303197 = 2363699) B2363699
theorem B4202131 : Blo 2213435 4202131 := bstep (se 1 (by rfl) ⟨3151598, by rfl⟩ : syracuseStep 4202131 = 6303197) B6303197
theorem B5602841 : Blo 2213435 5602841 := bstep (se 2 (by rfl) ⟨2101065, by rfl⟩ : syracuseStep 5602841 = 4202131) B4202131
theorem B3735227 : Blo 2213435 3735227 := bstep (se 1 (by rfl) ⟨2801420, by rfl⟩ : syracuseStep 3735227 = 5602841) B5602841
theorem B2490151 : Blo 2213435 2490151 := bstep (se 1 (by rfl) ⟨1867613, by rfl⟩ : syracuseStep 2490151 = 3735227) B3735227
theorem B3320201 : Blo 2213435 3320201 := bstep (se 2 (by rfl) ⟨1245075, by rfl⟩ : syracuseStep 3320201 = 2490151) B2490151
theorem B2213467 : Blo 2213435 2213467 := bstep (se 1 (by rfl) ⟨1660100, by rfl⟩ : syracuseStep 2213467 = 3320201) B3320201
theorem B11205701 : Blo 2213435 11205701 := bbase (se 4 (by rfl) ⟨1050534, by rfl⟩ : syracuseStep 11205701 = 2101069) (by norm_num)
theorem B7470467 : Blo 2213435 7470467 := bstep (se 1 (by rfl) ⟨5602850, by rfl⟩ : syracuseStep 7470467 = 11205701) B11205701
theorem B4980311 : Blo 2213435 4980311 := bstep (se 1 (by rfl) ⟨3735233, by rfl⟩ : syracuseStep 4980311 = 7470467) B7470467
theorem B3320207 : Blo 2213435 3320207 := bstep (se 1 (by rfl) ⟨2490155, by rfl⟩ : syracuseStep 3320207 = 4980311) B4980311
theorem B2213471 : Blo 2213435 2213471 := bstep (se 1 (by rfl) ⟨1660103, by rfl⟩ : syracuseStep 2213471 = 3320207) B3320207
theorem B3320213 : Blo 2213435 3320213 := bbase (se 6 (by rfl) ⟨77817, by rfl⟩ : syracuseStep 3320213 = 155635) (by norm_num)
theorem B2213475 : Blo 2213435 2213475 := bstep (se 1 (by rfl) ⟨1660106, by rfl⟩ : syracuseStep 2213475 = 3320213) B3320213
theorem B14375765 : Blo 2213435 14375765 := bbase (se 9 (by rfl) ⟨42116, by rfl⟩ : syracuseStep 14375765 = 84233) (by norm_num)
theorem B38335373 : Blo 2213435 38335373 := bstep (se 3 (by rfl) ⟨7187882, by rfl⟩ : syracuseStep 38335373 = 14375765) B14375765
theorem B25556915 : Blo 2213435 25556915 := bstep (se 1 (by rfl) ⟨19167686, by rfl⟩ : syracuseStep 25556915 = 38335373) B38335373
theorem B68151773 : Blo 2213435 68151773 := bstep (se 3 (by rfl) ⟨12778457, by rfl⟩ : syracuseStep 68151773 = 25556915) B25556915
theorem B45434515 : Blo 2213435 45434515 := bstep (se 1 (by rfl) ⟨34075886, by rfl⟩ : syracuseStep 45434515 = 68151773) B68151773
theorem B60579353 : Blo 2213435 60579353 := bstep (se 2 (by rfl) ⟨22717257, by rfl⟩ : syracuseStep 60579353 = 45434515) B45434515
theorem B40386235 : Blo 2213435 40386235 := bstep (se 1 (by rfl) ⟨30289676, by rfl⟩ : syracuseStep 40386235 = 60579353) B60579353
theorem B53848313 : Blo 2213435 53848313 := bstep (se 2 (by rfl) ⟨20193117, by rfl⟩ : syracuseStep 53848313 = 40386235) B40386235
theorem B35898875 : Blo 2213435 35898875 := bstep (se 1 (by rfl) ⟨26924156, by rfl⟩ : syracuseStep 35898875 = 53848313) B53848313
theorem B23932583 : Blo 2213435 23932583 := bstep (se 1 (by rfl) ⟨17949437, by rfl⟩ : syracuseStep 23932583 = 35898875) B35898875
theorem B15955055 : Blo 2213435 15955055 := bstep (se 1 (by rfl) ⟨11966291, by rfl⟩ : syracuseStep 15955055 = 23932583) B23932583
theorem B10636703 : Blo 2213435 10636703 := bstep (se 1 (by rfl) ⟨7977527, by rfl⟩ : syracuseStep 10636703 = 15955055) B15955055
theorem B7091135 : Blo 2213435 7091135 := bstep (se 1 (by rfl) ⟨5318351, by rfl⟩ : syracuseStep 7091135 = 10636703) B10636703
theorem B4727423 : Blo 2213435 4727423 := bstep (se 1 (by rfl) ⟨3545567, by rfl⟩ : syracuseStep 4727423 = 7091135) B7091135
theorem B12606461 : Blo 2213435 12606461 := bstep (se 3 (by rfl) ⟨2363711, by rfl⟩ : syracuseStep 12606461 = 4727423) B4727423
theorem B8404307 : Blo 2213435 8404307 := bstep (se 1 (by rfl) ⟨6303230, by rfl⟩ : syracuseStep 8404307 = 12606461) B12606461
theorem B5602871 : Blo 2213435 5602871 := bstep (se 1 (by rfl) ⟨4202153, by rfl⟩ : syracuseStep 5602871 = 8404307) B8404307
theorem B3735247 : Blo 2213435 3735247 := bstep (se 1 (by rfl) ⟨2801435, by rfl⟩ : syracuseStep 3735247 = 5602871) B5602871
theorem B4980329 : Blo 2213435 4980329 := bstep (se 2 (by rfl) ⟨1867623, by rfl⟩ : syracuseStep 4980329 = 3735247) B3735247
theorem B3320219 : Blo 2213435 3320219 := bstep (se 1 (by rfl) ⟨2490164, by rfl⟩ : syracuseStep 3320219 = 4980329) B4980329
theorem B2213479 : Blo 2213435 2213479 := bstep (se 1 (by rfl) ⟨1660109, by rfl⟩ : syracuseStep 2213479 = 3320219) B3320219
theorem B2490169 : Blo 2213435 2490169 := bbase (se 2 (by rfl) ⟨933813, by rfl⟩ : syracuseStep 2490169 = 1867627) (by norm_num)
theorem B3320225 : Blo 2213435 3320225 := bstep (se 2 (by rfl) ⟨1245084, by rfl⟩ : syracuseStep 3320225 = 2490169) B2490169
theorem B2213483 : Blo 2213435 2213483 := bstep (se 1 (by rfl) ⟨1660112, by rfl⟩ : syracuseStep 2213483 = 3320225) B3320225
theorem B6303253 : Blo 2213435 6303253 := bbase (se 6 (by rfl) ⟨147732, by rfl⟩ : syracuseStep 6303253 = 295465) (by norm_num)
theorem B8404337 : Blo 2213435 8404337 := bstep (se 2 (by rfl) ⟨3151626, by rfl⟩ : syracuseStep 8404337 = 6303253) B6303253
theorem B5602891 : Blo 2213435 5602891 := bstep (se 1 (by rfl) ⟨4202168, by rfl⟩ : syracuseStep 5602891 = 8404337) B8404337
theorem B7470521 : Blo 2213435 7470521 := bstep (se 2 (by rfl) ⟨2801445, by rfl⟩ : syracuseStep 7470521 = 5602891) B5602891
theorem B4980347 : Blo 2213435 4980347 := bstep (se 1 (by rfl) ⟨3735260, by rfl⟩ : syracuseStep 4980347 = 7470521) B7470521
theorem B3320231 : Blo 2213435 3320231 := bstep (se 1 (by rfl) ⟨2490173, by rfl⟩ : syracuseStep 3320231 = 4980347) B4980347
theorem B2213487 : Blo 2213435 2213487 := bstep (se 1 (by rfl) ⟨1660115, by rfl⟩ : syracuseStep 2213487 = 3320231) B3320231
theorem B3320237 : Blo 2213435 3320237 := bbase (se 3 (by rfl) ⟨622544, by rfl⟩ : syracuseStep 3320237 = 1245089) (by norm_num)
theorem B2213491 : Blo 2213435 2213491 := bstep (se 1 (by rfl) ⟨1660118, by rfl⟩ : syracuseStep 2213491 = 3320237) B3320237
theorem B4980365 : Blo 2213435 4980365 := bbase (se 3 (by rfl) ⟨933818, by rfl⟩ : syracuseStep 4980365 = 1867637) (by norm_num)
theorem B3320243 : Blo 2213435 3320243 := bstep (se 1 (by rfl) ⟨2490182, by rfl⟩ : syracuseStep 3320243 = 4980365) B4980365
theorem B2213495 : Blo 2213435 2213495 := bstep (se 1 (by rfl) ⟨1660121, by rfl⟩ : syracuseStep 2213495 = 3320243) B3320243
theorem B2801461 : Blo 2213435 2801461 := bbase (se 5 (by rfl) ⟨131318, by rfl⟩ : syracuseStep 2801461 = 262637) (by norm_num)
theorem B3735281 : Blo 2213435 3735281 := bstep (se 2 (by rfl) ⟨1400730, by rfl⟩ : syracuseStep 3735281 = 2801461) B2801461
theorem B2490187 : Blo 2213435 2490187 := bstep (se 1 (by rfl) ⟨1867640, by rfl⟩ : syracuseStep 2490187 = 3735281) B3735281
theorem B3320249 : Blo 2213435 3320249 := bstep (se 2 (by rfl) ⟨1245093, by rfl⟩ : syracuseStep 3320249 = 2490187) B2490187
theorem B2213499 : Blo 2213435 2213499 := bstep (se 1 (by rfl) ⟨1660124, by rfl⟩ : syracuseStep 2213499 = 3320249) B3320249
theorem B10234421 : Blo 2213435 10234421 := bbase (se 5 (by rfl) ⟨479738, by rfl⟩ : syracuseStep 10234421 = 959477) (by norm_num)
theorem B6822947 : Blo 2213435 6822947 := bstep (se 1 (by rfl) ⟨5117210, by rfl⟩ : syracuseStep 6822947 = 10234421) B10234421
theorem B18194525 : Blo 2213435 18194525 := bstep (se 3 (by rfl) ⟨3411473, by rfl⟩ : syracuseStep 18194525 = 6822947) B6822947
theorem B12129683 : Blo 2213435 12129683 := bstep (se 1 (by rfl) ⟨9097262, by rfl⟩ : syracuseStep 12129683 = 18194525) B18194525
theorem B32345821 : Blo 2213435 32345821 := bstep (se 3 (by rfl) ⟨6064841, by rfl⟩ : syracuseStep 32345821 = 12129683) B12129683
theorem B43127761 : Blo 2213435 43127761 := bstep (se 2 (by rfl) ⟨16172910, by rfl⟩ : syracuseStep 43127761 = 32345821) B32345821
theorem B57503681 : Blo 2213435 57503681 := bstep (se 2 (by rfl) ⟨21563880, by rfl⟩ : syracuseStep 57503681 = 43127761) B43127761
theorem B38335787 : Blo 2213435 38335787 := bstep (se 1 (by rfl) ⟨28751840, by rfl⟩ : syracuseStep 38335787 = 57503681) B57503681
theorem B25557191 : Blo 2213435 25557191 := bstep (se 1 (by rfl) ⟨19167893, by rfl⟩ : syracuseStep 25557191 = 38335787) B38335787
theorem B17038127 : Blo 2213435 17038127 := bstep (se 1 (by rfl) ⟨12778595, by rfl⟩ : syracuseStep 17038127 = 25557191) B25557191
theorem B11358751 : Blo 2213435 11358751 := bstep (se 1 (by rfl) ⟨8519063, by rfl⟩ : syracuseStep 11358751 = 17038127) B17038127
theorem B15145001 : Blo 2213435 15145001 := bstep (se 2 (by rfl) ⟨5679375, by rfl⟩ : syracuseStep 15145001 = 11358751) B11358751
theorem B10096667 : Blo 2213435 10096667 := bstep (se 1 (by rfl) ⟨7572500, by rfl⟩ : syracuseStep 10096667 = 15145001) B15145001
theorem B6731111 : Blo 2213435 6731111 := bstep (se 1 (by rfl) ⟨5048333, by rfl⟩ : syracuseStep 6731111 = 10096667) B10096667
theorem B4487407 : Blo 2213435 4487407 := bstep (se 1 (by rfl) ⟨3365555, by rfl⟩ : syracuseStep 4487407 = 6731111) B6731111
theorem B23932837 : Blo 2213435 23932837 := bstep (se 4 (by rfl) ⟨2243703, by rfl⟩ : syracuseStep 23932837 = 4487407) B4487407
theorem B31910449 : Blo 2213435 31910449 := bstep (se 2 (by rfl) ⟨11966418, by rfl⟩ : syracuseStep 31910449 = 23932837) B23932837
theorem B42547265 : Blo 2213435 42547265 := bstep (se 2 (by rfl) ⟨15955224, by rfl⟩ : syracuseStep 42547265 = 31910449) B31910449
theorem B28364843 : Blo 2213435 28364843 := bstep (se 1 (by rfl) ⟨21273632, by rfl⟩ : syracuseStep 28364843 = 42547265) B42547265
theorem B18909895 : Blo 2213435 18909895 := bstep (se 1 (by rfl) ⟨14182421, by rfl⟩ : syracuseStep 18909895 = 28364843) B28364843
theorem B25213193 : Blo 2213435 25213193 := bstep (se 2 (by rfl) ⟨9454947, by rfl⟩ : syracuseStep 25213193 = 18909895) B18909895
theorem B16808795 : Blo 2213435 16808795 := bstep (se 1 (by rfl) ⟨12606596, by rfl⟩ : syracuseStep 16808795 = 25213193) B25213193
theorem B11205863 : Blo 2213435 11205863 := bstep (se 1 (by rfl) ⟨8404397, by rfl⟩ : syracuseStep 11205863 = 16808795) B16808795
theorem B7470575 : Blo 2213435 7470575 := bstep (se 1 (by rfl) ⟨5602931, by rfl⟩ : syracuseStep 7470575 = 11205863) B11205863
theorem B4980383 : Blo 2213435 4980383 := bstep (se 1 (by rfl) ⟨3735287, by rfl⟩ : syracuseStep 4980383 = 7470575) B7470575
theorem B3320255 : Blo 2213435 3320255 := bstep (se 1 (by rfl) ⟨2490191, by rfl⟩ : syracuseStep 3320255 = 4980383) B4980383
theorem B2213503 : Blo 2213435 2213503 := bstep (se 1 (by rfl) ⟨1660127, by rfl⟩ : syracuseStep 2213503 = 3320255) B3320255
theorem B3320261 : Blo 2213435 3320261 := bbase (se 4 (by rfl) ⟨311274, by rfl⟩ : syracuseStep 3320261 = 622549) (by norm_num)
theorem B2213507 : Blo 2213435 2213507 := bstep (se 1 (by rfl) ⟨1660130, by rfl⟩ : syracuseStep 2213507 = 3320261) B3320261
theorem B3735301 : Blo 2213435 3735301 := bbase (se 4 (by rfl) ⟨350184, by rfl⟩ : syracuseStep 3735301 = 700369) (by norm_num)
theorem B4980401 : Blo 2213435 4980401 := bstep (se 2 (by rfl) ⟨1867650, by rfl⟩ : syracuseStep 4980401 = 3735301) B3735301
theorem B3320267 : Blo 2213435 3320267 := bstep (se 1 (by rfl) ⟨2490200, by rfl⟩ : syracuseStep 3320267 = 4980401) B4980401
theorem B2213511 : Blo 2213435 2213511 := bstep (se 1 (by rfl) ⟨1660133, by rfl⟩ : syracuseStep 2213511 = 3320267) B3320267
theorem B2490205 : Blo 2213435 2490205 := bbase (se 3 (by rfl) ⟨466913, by rfl⟩ : syracuseStep 2490205 = 933827) (by norm_num)
theorem B3320273 : Blo 2213435 3320273 := bstep (se 2 (by rfl) ⟨1245102, by rfl⟩ : syracuseStep 3320273 = 2490205) B2490205
theorem B2213515 : Blo 2213435 2213515 := bstep (se 1 (by rfl) ⟨1660136, by rfl⟩ : syracuseStep 2213515 = 3320273) B3320273
theorem B7470629 : Blo 2213435 7470629 := bbase (se 4 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 7470629 = 1400743) (by norm_num)
theorem B4980419 : Blo 2213435 4980419 := bstep (se 1 (by rfl) ⟨3735314, by rfl⟩ : syracuseStep 4980419 = 7470629) B7470629
theorem B3320279 : Blo 2213435 3320279 := bstep (se 1 (by rfl) ⟨2490209, by rfl⟩ : syracuseStep 3320279 = 4980419) B4980419
theorem B2213519 : Blo 2213435 2213519 := bstep (se 1 (by rfl) ⟨1660139, by rfl⟩ : syracuseStep 2213519 = 3320279) B3320279
theorem B3320285 : Blo 2213435 3320285 := bbase (se 3 (by rfl) ⟨622553, by rfl⟩ : syracuseStep 3320285 = 1245107) (by norm_num)
theorem B2213523 : Blo 2213435 2213523 := bstep (se 1 (by rfl) ⟨1660142, by rfl⟩ : syracuseStep 2213523 = 3320285) B3320285
theorem B4980437 : Blo 2213435 4980437 := bbase (se 7 (by rfl) ⟨58364, by rfl⟩ : syracuseStep 4980437 = 116729) (by norm_num)
theorem B3320291 : Blo 2213435 3320291 := bstep (se 1 (by rfl) ⟨2490218, by rfl⟩ : syracuseStep 3320291 = 4980437) B4980437
theorem B2213527 : Blo 2213435 2213527 := bstep (se 1 (by rfl) ⟨1660145, by rfl⟩ : syracuseStep 2213527 = 3320291) B3320291
theorem B5318477 : Blo 2213435 5318477 := bbase (se 3 (by rfl) ⟨997214, by rfl⟩ : syracuseStep 5318477 = 1994429) (by norm_num)
theorem B3545651 : Blo 2213435 3545651 := bstep (se 1 (by rfl) ⟨2659238, by rfl⟩ : syracuseStep 3545651 = 5318477) B5318477
theorem B9455069 : Blo 2213435 9455069 := bstep (se 3 (by rfl) ⟨1772825, by rfl⟩ : syracuseStep 9455069 = 3545651) B3545651
theorem B6303379 : Blo 2213435 6303379 := bstep (se 1 (by rfl) ⟨4727534, by rfl⟩ : syracuseStep 6303379 = 9455069) B9455069
theorem B8404505 : Blo 2213435 8404505 := bstep (se 2 (by rfl) ⟨3151689, by rfl⟩ : syracuseStep 8404505 = 6303379) B6303379
theorem B5603003 : Blo 2213435 5603003 := bstep (se 1 (by rfl) ⟨4202252, by rfl⟩ : syracuseStep 5603003 = 8404505) B8404505
theorem B3735335 : Blo 2213435 3735335 := bstep (se 1 (by rfl) ⟨2801501, by rfl⟩ : syracuseStep 3735335 = 5603003) B5603003
theorem B2490223 : Blo 2213435 2490223 := bstep (se 1 (by rfl) ⟨1867667, by rfl⟩ : syracuseStep 2490223 = 3735335) B3735335
theorem B3320297 : Blo 2213435 3320297 := bstep (se 2 (by rfl) ⟨1245111, by rfl⟩ : syracuseStep 3320297 = 2490223) B2490223
theorem B2213531 : Blo 2213435 2213531 := bstep (se 1 (by rfl) ⟨1660148, by rfl⟩ : syracuseStep 2213531 = 3320297) B3320297
theorem B21273941 : Blo 2213435 21273941 := bbase (se 11 (by rfl) ⟨15581, by rfl⟩ : syracuseStep 21273941 = 31163) (by norm_num)
theorem B14182627 : Blo 2213435 14182627 := bstep (se 1 (by rfl) ⟨10636970, by rfl⟩ : syracuseStep 14182627 = 21273941) B21273941
theorem B18910169 : Blo 2213435 18910169 := bstep (se 2 (by rfl) ⟨7091313, by rfl⟩ : syracuseStep 18910169 = 14182627) B14182627
theorem B12606779 : Blo 2213435 12606779 := bstep (se 1 (by rfl) ⟨9455084, by rfl⟩ : syracuseStep 12606779 = 18910169) B18910169
theorem B8404519 : Blo 2213435 8404519 := bstep (se 1 (by rfl) ⟨6303389, by rfl⟩ : syracuseStep 8404519 = 12606779) B12606779
theorem B11206025 : Blo 2213435 11206025 := bstep (se 2 (by rfl) ⟨4202259, by rfl⟩ : syracuseStep 11206025 = 8404519) B8404519
theorem B7470683 : Blo 2213435 7470683 := bstep (se 1 (by rfl) ⟨5603012, by rfl⟩ : syracuseStep 7470683 = 11206025) B11206025
theorem B4980455 : Blo 2213435 4980455 := bstep (se 1 (by rfl) ⟨3735341, by rfl⟩ : syracuseStep 4980455 = 7470683) B7470683
theorem B3320303 : Blo 2213435 3320303 := bstep (se 1 (by rfl) ⟨2490227, by rfl⟩ : syracuseStep 3320303 = 4980455) B4980455
theorem B2213535 : Blo 2213435 2213535 := bstep (se 1 (by rfl) ⟨1660151, by rfl⟩ : syracuseStep 2213535 = 3320303) B3320303
theorem B3320309 : Blo 2213435 3320309 := bbase (se 5 (by rfl) ⟨155639, by rfl⟩ : syracuseStep 3320309 = 311279) (by norm_num)
theorem B2213539 : Blo 2213435 2213539 := bstep (se 1 (by rfl) ⟨1660154, by rfl⟩ : syracuseStep 2213539 = 3320309) B3320309
theorem B6303413 : Blo 2213435 6303413 := bbase (se 5 (by rfl) ⟨295472, by rfl⟩ : syracuseStep 6303413 = 590945) (by norm_num)
theorem B4202275 : Blo 2213435 4202275 := bstep (se 1 (by rfl) ⟨3151706, by rfl⟩ : syracuseStep 4202275 = 6303413) B6303413
theorem B5603033 : Blo 2213435 5603033 := bstep (se 2 (by rfl) ⟨2101137, by rfl⟩ : syracuseStep 5603033 = 4202275) B4202275
theorem B3735355 : Blo 2213435 3735355 := bstep (se 1 (by rfl) ⟨2801516, by rfl⟩ : syracuseStep 3735355 = 5603033) B5603033
theorem B4980473 : Blo 2213435 4980473 := bstep (se 2 (by rfl) ⟨1867677, by rfl⟩ : syracuseStep 4980473 = 3735355) B3735355
theorem B3320315 : Blo 2213435 3320315 := bstep (se 1 (by rfl) ⟨2490236, by rfl⟩ : syracuseStep 3320315 = 4980473) B4980473
theorem B2213543 : Blo 2213435 2213543 := bstep (se 1 (by rfl) ⟨1660157, by rfl⟩ : syracuseStep 2213543 = 3320315) B3320315
theorem B2490241 : Blo 2213435 2490241 := bbase (se 2 (by rfl) ⟨933840, by rfl⟩ : syracuseStep 2490241 = 1867681) (by norm_num)
theorem B3320321 : Blo 2213435 3320321 := bstep (se 2 (by rfl) ⟨1245120, by rfl⟩ : syracuseStep 3320321 = 2490241) B2490241
theorem B2213547 : Blo 2213435 2213547 := bstep (se 1 (by rfl) ⟨1660160, by rfl⟩ : syracuseStep 2213547 = 3320321) B3320321
theorem B5603053 : Blo 2213435 5603053 := bbase (se 3 (by rfl) ⟨1050572, by rfl⟩ : syracuseStep 5603053 = 2101145) (by norm_num)
theorem B7470737 : Blo 2213435 7470737 := bstep (se 2 (by rfl) ⟨2801526, by rfl⟩ : syracuseStep 7470737 = 5603053) B5603053
theorem B4980491 : Blo 2213435 4980491 := bstep (se 1 (by rfl) ⟨3735368, by rfl⟩ : syracuseStep 4980491 = 7470737) B7470737
theorem B3320327 : Blo 2213435 3320327 := bstep (se 1 (by rfl) ⟨2490245, by rfl⟩ : syracuseStep 3320327 = 4980491) B4980491
theorem B2213551 : Blo 2213435 2213551 := bstep (se 1 (by rfl) ⟨1660163, by rfl⟩ : syracuseStep 2213551 = 3320327) B3320327
theorem B3320333 : Blo 2213435 3320333 := bbase (se 3 (by rfl) ⟨622562, by rfl⟩ : syracuseStep 3320333 = 1245125) (by norm_num)
theorem B2213555 : Blo 2213435 2213555 := bstep (se 1 (by rfl) ⟨1660166, by rfl⟩ : syracuseStep 2213555 = 3320333) B3320333
theorem B4980509 : Blo 2213435 4980509 := bbase (se 3 (by rfl) ⟨933845, by rfl⟩ : syracuseStep 4980509 = 1867691) (by norm_num)
theorem B3320339 : Blo 2213435 3320339 := bstep (se 1 (by rfl) ⟨2490254, by rfl⟩ : syracuseStep 3320339 = 4980509) B4980509
theorem B2213559 : Blo 2213435 2213559 := bstep (se 1 (by rfl) ⟨1660169, by rfl⟩ : syracuseStep 2213559 = 3320339) B3320339
theorem B3735389 : Blo 2213435 3735389 := bbase (se 3 (by rfl) ⟨700385, by rfl⟩ : syracuseStep 3735389 = 1400771) (by norm_num)
theorem B2490259 : Blo 2213435 2490259 := bstep (se 1 (by rfl) ⟨1867694, by rfl⟩ : syracuseStep 2490259 = 3735389) B3735389
theorem B3320345 : Blo 2213435 3320345 := bstep (se 2 (by rfl) ⟨1245129, by rfl⟩ : syracuseStep 3320345 = 2490259) B2490259
theorem B2213563 : Blo 2213435 2213563 := bstep (se 1 (by rfl) ⟨1660172, by rfl⟩ : syracuseStep 2213563 = 3320345) B3320345
theorem B9455221 : Blo 2213435 9455221 := bbase (se 5 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 9455221 = 886427) (by norm_num)
theorem B12606961 : Blo 2213435 12606961 := bstep (se 2 (by rfl) ⟨4727610, by rfl⟩ : syracuseStep 12606961 = 9455221) B9455221
theorem B16809281 : Blo 2213435 16809281 := bstep (se 2 (by rfl) ⟨6303480, by rfl⟩ : syracuseStep 16809281 = 12606961) B12606961
theorem B11206187 : Blo 2213435 11206187 := bstep (se 1 (by rfl) ⟨8404640, by rfl⟩ : syracuseStep 11206187 = 16809281) B16809281
theorem B7470791 : Blo 2213435 7470791 := bstep (se 1 (by rfl) ⟨5603093, by rfl⟩ : syracuseStep 7470791 = 11206187) B11206187
theorem B4980527 : Blo 2213435 4980527 := bstep (se 1 (by rfl) ⟨3735395, by rfl⟩ : syracuseStep 4980527 = 7470791) B7470791
theorem B3320351 : Blo 2213435 3320351 := bstep (se 1 (by rfl) ⟨2490263, by rfl⟩ : syracuseStep 3320351 = 4980527) B4980527
theorem B2213567 : Blo 2213435 2213567 := bstep (se 1 (by rfl) ⟨1660175, by rfl⟩ : syracuseStep 2213567 = 3320351) B3320351
theorem B3320357 : Blo 2213435 3320357 := bbase (se 4 (by rfl) ⟨311283, by rfl⟩ : syracuseStep 3320357 = 622567) (by norm_num)
theorem B2213571 : Blo 2213435 2213571 := bstep (se 1 (by rfl) ⟨1660178, by rfl⟩ : syracuseStep 2213571 = 3320357) B3320357
theorem B2801557 : Blo 2213435 2801557 := bbase (se 6 (by rfl) ⟨65661, by rfl⟩ : syracuseStep 2801557 = 131323) (by norm_num)
theorem B3735409 : Blo 2213435 3735409 := bstep (se 2 (by rfl) ⟨1400778, by rfl⟩ : syracuseStep 3735409 = 2801557) B2801557
theorem B4980545 : Blo 2213435 4980545 := bstep (se 2 (by rfl) ⟨1867704, by rfl⟩ : syracuseStep 4980545 = 3735409) B3735409
theorem B3320363 : Blo 2213435 3320363 := bstep (se 1 (by rfl) ⟨2490272, by rfl⟩ : syracuseStep 3320363 = 4980545) B4980545
theorem B2213575 : Blo 2213435 2213575 := bstep (se 1 (by rfl) ⟨1660181, by rfl⟩ : syracuseStep 2213575 = 3320363) B3320363
theorem B2490277 : Blo 2213435 2490277 := bbase (se 4 (by rfl) ⟨233463, by rfl⟩ : syracuseStep 2490277 = 466927) (by norm_num)
theorem B3320369 : Blo 2213435 3320369 := bstep (se 2 (by rfl) ⟨1245138, by rfl⟩ : syracuseStep 3320369 = 2490277) B2490277
theorem B2213579 : Blo 2213435 2213579 := bstep (se 1 (by rfl) ⟨1660184, by rfl⟩ : syracuseStep 2213579 = 3320369) B3320369
theorem B8975141 : Blo 2213435 8975141 := bbase (se 4 (by rfl) ⟨841419, by rfl⟩ : syracuseStep 8975141 = 1682839) (by norm_num)
theorem B5983427 : Blo 2213435 5983427 := bstep (se 1 (by rfl) ⟨4487570, by rfl⟩ : syracuseStep 5983427 = 8975141) B8975141
theorem B15955805 : Blo 2213435 15955805 := bstep (se 3 (by rfl) ⟨2991713, by rfl⟩ : syracuseStep 15955805 = 5983427) B5983427
theorem B10637203 : Blo 2213435 10637203 := bstep (se 1 (by rfl) ⟨7977902, by rfl⟩ : syracuseStep 10637203 = 15955805) B15955805
theorem B14182937 : Blo 2213435 14182937 := bstep (se 2 (by rfl) ⟨5318601, by rfl⟩ : syracuseStep 14182937 = 10637203) B10637203
theorem B9455291 : Blo 2213435 9455291 := bstep (se 1 (by rfl) ⟨7091468, by rfl⟩ : syracuseStep 9455291 = 14182937) B14182937
theorem B6303527 : Blo 2213435 6303527 := bstep (se 1 (by rfl) ⟨4727645, by rfl⟩ : syracuseStep 6303527 = 9455291) B9455291
theorem B4202351 : Blo 2213435 4202351 := bstep (se 1 (by rfl) ⟨3151763, by rfl⟩ : syracuseStep 4202351 = 6303527) B6303527
theorem B2801567 : Blo 2213435 2801567 := bstep (se 1 (by rfl) ⟨2101175, by rfl⟩ : syracuseStep 2801567 = 4202351) B4202351
theorem B7470845 : Blo 2213435 7470845 := bstep (se 3 (by rfl) ⟨1400783, by rfl⟩ : syracuseStep 7470845 = 2801567) B2801567
theorem B4980563 : Blo 2213435 4980563 := bstep (se 1 (by rfl) ⟨3735422, by rfl⟩ : syracuseStep 4980563 = 7470845) B7470845
theorem B3320375 : Blo 2213435 3320375 := bstep (se 1 (by rfl) ⟨2490281, by rfl⟩ : syracuseStep 3320375 = 4980563) B4980563
theorem B2213583 : Blo 2213435 2213583 := bstep (se 1 (by rfl) ⟨1660187, by rfl⟩ : syracuseStep 2213583 = 3320375) B3320375
theorem B3320381 : Blo 2213435 3320381 := bbase (se 3 (by rfl) ⟨622571, by rfl⟩ : syracuseStep 3320381 = 1245143) (by norm_num)
theorem B2213587 : Blo 2213435 2213587 := bstep (se 1 (by rfl) ⟨1660190, by rfl⟩ : syracuseStep 2213587 = 3320381) B3320381
theorem B4980581 : Blo 2213435 4980581 := bbase (se 4 (by rfl) ⟨466929, by rfl⟩ : syracuseStep 4980581 = 933859) (by norm_num)
theorem B3320387 : Blo 2213435 3320387 := bstep (se 1 (by rfl) ⟨2490290, by rfl⟩ : syracuseStep 3320387 = 4980581) B4980581
theorem B2213591 : Blo 2213435 2213591 := bstep (se 1 (by rfl) ⟨1660193, by rfl⟩ : syracuseStep 2213591 = 3320387) B3320387
theorem B5603165 : Blo 2213435 5603165 := bbase (se 3 (by rfl) ⟨1050593, by rfl⟩ : syracuseStep 5603165 = 2101187) (by norm_num)
theorem B3735443 : Blo 2213435 3735443 := bstep (se 1 (by rfl) ⟨2801582, by rfl⟩ : syracuseStep 3735443 = 5603165) B5603165
theorem B2490295 : Blo 2213435 2490295 := bstep (se 1 (by rfl) ⟨1867721, by rfl⟩ : syracuseStep 2490295 = 3735443) B3735443
theorem B3320393 : Blo 2213435 3320393 := bstep (se 2 (by rfl) ⟨1245147, by rfl⟩ : syracuseStep 3320393 = 2490295) B2490295
theorem B2213595 : Blo 2213435 2213595 := bstep (se 1 (by rfl) ⟨1660196, by rfl⟩ : syracuseStep 2213595 = 3320393) B3320393
theorem B4202381 : Blo 2213435 4202381 := bbase (se 3 (by rfl) ⟨787946, by rfl⟩ : syracuseStep 4202381 = 1575893) (by norm_num)
theorem B11206349 : Blo 2213435 11206349 := bstep (se 3 (by rfl) ⟨2101190, by rfl⟩ : syracuseStep 11206349 = 4202381) B4202381
theorem B7470899 : Blo 2213435 7470899 := bstep (se 1 (by rfl) ⟨5603174, by rfl⟩ : syracuseStep 7470899 = 11206349) B11206349
theorem B4980599 : Blo 2213435 4980599 := bstep (se 1 (by rfl) ⟨3735449, by rfl⟩ : syracuseStep 4980599 = 7470899) B7470899
theorem B3320399 : Blo 2213435 3320399 := bstep (se 1 (by rfl) ⟨2490299, by rfl⟩ : syracuseStep 3320399 = 4980599) B4980599
theorem B2213599 : Blo 2213435 2213599 := bstep (se 1 (by rfl) ⟨1660199, by rfl⟩ : syracuseStep 2213599 = 3320399) B3320399
theorem B3320405 : Blo 2213435 3320405 := bbase (se 8 (by rfl) ⟨19455, by rfl⟩ : syracuseStep 3320405 = 38911) (by norm_num)
theorem B2213603 : Blo 2213435 2213603 := bstep (se 1 (by rfl) ⟨1660202, by rfl⟩ : syracuseStep 2213603 = 3320405) B3320405
theorem B7977989 : Blo 2213435 7977989 := bbase (se 4 (by rfl) ⟨747936, by rfl⟩ : syracuseStep 7977989 = 1495873) (by norm_num)
theorem B5318659 : Blo 2213435 5318659 := bstep (se 1 (by rfl) ⟨3988994, by rfl⟩ : syracuseStep 5318659 = 7977989) B7977989
theorem B7091545 : Blo 2213435 7091545 := bstep (se 2 (by rfl) ⟨2659329, by rfl⟩ : syracuseStep 7091545 = 5318659) B5318659
theorem B9455393 : Blo 2213435 9455393 := bstep (se 2 (by rfl) ⟨3545772, by rfl⟩ : syracuseStep 9455393 = 7091545) B7091545
theorem B6303595 : Blo 2213435 6303595 := bstep (se 1 (by rfl) ⟨4727696, by rfl⟩ : syracuseStep 6303595 = 9455393) B9455393
theorem B8404793 : Blo 2213435 8404793 := bstep (se 2 (by rfl) ⟨3151797, by rfl⟩ : syracuseStep 8404793 = 6303595) B6303595
theorem B5603195 : Blo 2213435 5603195 := bstep (se 1 (by rfl) ⟨4202396, by rfl⟩ : syracuseStep 5603195 = 8404793) B8404793
theorem B3735463 : Blo 2213435 3735463 := bstep (se 1 (by rfl) ⟨2801597, by rfl⟩ : syracuseStep 3735463 = 5603195) B5603195
theorem B4980617 : Blo 2213435 4980617 := bstep (se 2 (by rfl) ⟨1867731, by rfl⟩ : syracuseStep 4980617 = 3735463) B3735463
theorem B3320411 : Blo 2213435 3320411 := bstep (se 1 (by rfl) ⟨2490308, by rfl⟩ : syracuseStep 3320411 = 4980617) B4980617
theorem B2213607 : Blo 2213435 2213607 := bstep (se 1 (by rfl) ⟨1660205, by rfl⟩ : syracuseStep 2213607 = 3320411) B3320411
theorem B2490313 : Blo 2213435 2490313 := bbase (se 2 (by rfl) ⟨933867, by rfl⟩ : syracuseStep 2490313 = 1867735) (by norm_num)
theorem B3320417 : Blo 2213435 3320417 := bstep (se 2 (by rfl) ⟨1245156, by rfl⟩ : syracuseStep 3320417 = 2490313) B2490313
theorem B2213611 : Blo 2213435 2213611 := bstep (se 1 (by rfl) ⟨1660208, by rfl⟩ : syracuseStep 2213611 = 3320417) B3320417
theorem B2991757 : Blo 2213435 2991757 := bbase (se 3 (by rfl) ⟨560954, by rfl⟩ : syracuseStep 2991757 = 1121909) (by norm_num)
theorem B3989009 : Blo 2213435 3989009 := bstep (se 2 (by rfl) ⟨1495878, by rfl⟩ : syracuseStep 3989009 = 2991757) B2991757
theorem B2659339 : Blo 2213435 2659339 := bstep (se 1 (by rfl) ⟨1994504, by rfl⟩ : syracuseStep 2659339 = 3989009) B3989009
theorem B3545785 : Blo 2213435 3545785 := bstep (se 2 (by rfl) ⟨1329669, by rfl⟩ : syracuseStep 3545785 = 2659339) B2659339
theorem B18910853 : Blo 2213435 18910853 := bstep (se 4 (by rfl) ⟨1772892, by rfl⟩ : syracuseStep 18910853 = 3545785) B3545785
theorem B12607235 : Blo 2213435 12607235 := bstep (se 1 (by rfl) ⟨9455426, by rfl⟩ : syracuseStep 12607235 = 18910853) B18910853
theorem B8404823 : Blo 2213435 8404823 := bstep (se 1 (by rfl) ⟨6303617, by rfl⟩ : syracuseStep 8404823 = 12607235) B12607235
theorem B5603215 : Blo 2213435 5603215 := bstep (se 1 (by rfl) ⟨4202411, by rfl⟩ : syracuseStep 5603215 = 8404823) B8404823
theorem B7470953 : Blo 2213435 7470953 := bstep (se 2 (by rfl) ⟨2801607, by rfl⟩ : syracuseStep 7470953 = 5603215) B5603215
theorem B4980635 : Blo 2213435 4980635 := bstep (se 1 (by rfl) ⟨3735476, by rfl⟩ : syracuseStep 4980635 = 7470953) B7470953
theorem B3320423 : Blo 2213435 3320423 := bstep (se 1 (by rfl) ⟨2490317, by rfl⟩ : syracuseStep 3320423 = 4980635) B4980635
theorem B2213615 : Blo 2213435 2213615 := bstep (se 1 (by rfl) ⟨1660211, by rfl⟩ : syracuseStep 2213615 = 3320423) B3320423
theorem B3320429 : Blo 2213435 3320429 := bbase (se 3 (by rfl) ⟨622580, by rfl⟩ : syracuseStep 3320429 = 1245161) (by norm_num)
theorem B2213619 : Blo 2213435 2213619 := bstep (se 1 (by rfl) ⟨1660214, by rfl⟩ : syracuseStep 2213619 = 3320429) B3320429
theorem B4980653 : Blo 2213435 4980653 := bbase (se 3 (by rfl) ⟨933872, by rfl⟩ : syracuseStep 4980653 = 1867745) (by norm_num)
theorem B3320435 : Blo 2213435 3320435 := bstep (se 1 (by rfl) ⟨2490326, by rfl⟩ : syracuseStep 3320435 = 4980653) B4980653
theorem B2213623 : Blo 2213435 2213623 := bstep (se 1 (by rfl) ⟨1660217, by rfl⟩ : syracuseStep 2213623 = 3320435) B3320435
theorem B6303653 : Blo 2213435 6303653 := bbase (se 4 (by rfl) ⟨590967, by rfl⟩ : syracuseStep 6303653 = 1181935) (by norm_num)
theorem B4202435 : Blo 2213435 4202435 := bstep (se 1 (by rfl) ⟨3151826, by rfl⟩ : syracuseStep 4202435 = 6303653) B6303653
theorem B2801623 : Blo 2213435 2801623 := bstep (se 1 (by rfl) ⟨2101217, by rfl⟩ : syracuseStep 2801623 = 4202435) B4202435
theorem B3735497 : Blo 2213435 3735497 := bstep (se 2 (by rfl) ⟨1400811, by rfl⟩ : syracuseStep 3735497 = 2801623) B2801623
theorem B2490331 : Blo 2213435 2490331 := bstep (se 1 (by rfl) ⟨1867748, by rfl⟩ : syracuseStep 2490331 = 3735497) B3735497
theorem B3320441 : Blo 2213435 3320441 := bstep (se 2 (by rfl) ⟨1245165, by rfl⟩ : syracuseStep 3320441 = 2490331) B2490331
theorem B2213627 : Blo 2213435 2213627 := bstep (se 1 (by rfl) ⟨1660220, by rfl⟩ : syracuseStep 2213627 = 3320441) B3320441
theorem B8975333 : Blo 2213435 8975333 := bbase (se 4 (by rfl) ⟨841437, by rfl⟩ : syracuseStep 8975333 = 1682875) (by norm_num)
theorem B23934221 : Blo 2213435 23934221 := bstep (se 3 (by rfl) ⟨4487666, by rfl⟩ : syracuseStep 23934221 = 8975333) B8975333
theorem B15956147 : Blo 2213435 15956147 := bstep (se 1 (by rfl) ⟨11967110, by rfl⟩ : syracuseStep 15956147 = 23934221) B23934221
theorem B42549725 : Blo 2213435 42549725 := bstep (se 3 (by rfl) ⟨7978073, by rfl⟩ : syracuseStep 42549725 = 15956147) B15956147
theorem B28366483 : Blo 2213435 28366483 := bstep (se 1 (by rfl) ⟨21274862, by rfl⟩ : syracuseStep 28366483 = 42549725) B42549725
theorem B37821977 : Blo 2213435 37821977 := bstep (se 2 (by rfl) ⟨14183241, by rfl⟩ : syracuseStep 37821977 = 28366483) B28366483
theorem B25214651 : Blo 2213435 25214651 := bstep (se 1 (by rfl) ⟨18910988, by rfl⟩ : syracuseStep 25214651 = 37821977) B37821977
theorem B16809767 : Blo 2213435 16809767 := bstep (se 1 (by rfl) ⟨12607325, by rfl⟩ : syracuseStep 16809767 = 25214651) B25214651
theorem B11206511 : Blo 2213435 11206511 := bstep (se 1 (by rfl) ⟨8404883, by rfl⟩ : syracuseStep 11206511 = 16809767) B16809767
theorem B7471007 : Blo 2213435 7471007 := bstep (se 1 (by rfl) ⟨5603255, by rfl⟩ : syracuseStep 7471007 = 11206511) B11206511
theorem B4980671 : Blo 2213435 4980671 := bstep (se 1 (by rfl) ⟨3735503, by rfl⟩ : syracuseStep 4980671 = 7471007) B7471007
theorem B3320447 : Blo 2213435 3320447 := bstep (se 1 (by rfl) ⟨2490335, by rfl⟩ : syracuseStep 3320447 = 4980671) B4980671
theorem B2213631 : Blo 2213435 2213631 := bstep (se 1 (by rfl) ⟨1660223, by rfl⟩ : syracuseStep 2213631 = 3320447) B3320447
theorem B3320453 : Blo 2213435 3320453 := bbase (se 4 (by rfl) ⟨311292, by rfl⟩ : syracuseStep 3320453 = 622585) (by norm_num)
theorem B2213635 : Blo 2213435 2213635 := bstep (se 1 (by rfl) ⟨1660226, by rfl⟩ : syracuseStep 2213635 = 3320453) B3320453
theorem B3735517 : Blo 2213435 3735517 := bbase (se 3 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 3735517 = 1400819) (by norm_num)
theorem B4980689 : Blo 2213435 4980689 := bstep (se 2 (by rfl) ⟨1867758, by rfl⟩ : syracuseStep 4980689 = 3735517) B3735517
theorem B3320459 : Blo 2213435 3320459 := bstep (se 1 (by rfl) ⟨2490344, by rfl⟩ : syracuseStep 3320459 = 4980689) B4980689
theorem B2213639 : Blo 2213435 2213639 := bstep (se 1 (by rfl) ⟨1660229, by rfl⟩ : syracuseStep 2213639 = 3320459) B3320459
theorem B2490349 : Blo 2213435 2490349 := bbase (se 3 (by rfl) ⟨466940, by rfl⟩ : syracuseStep 2490349 = 933881) (by norm_num)
theorem B3320465 : Blo 2213435 3320465 := bstep (se 2 (by rfl) ⟨1245174, by rfl⟩ : syracuseStep 3320465 = 2490349) B2490349
theorem B2213643 : Blo 2213435 2213643 := bstep (se 1 (by rfl) ⟨1660232, by rfl⟩ : syracuseStep 2213643 = 3320465) B3320465
theorem B7471061 : Blo 2213435 7471061 := bbase (se 7 (by rfl) ⟨87551, by rfl⟩ : syracuseStep 7471061 = 175103) (by norm_num)
theorem B4980707 : Blo 2213435 4980707 := bstep (se 1 (by rfl) ⟨3735530, by rfl⟩ : syracuseStep 4980707 = 7471061) B7471061
theorem B3320471 : Blo 2213435 3320471 := bstep (se 1 (by rfl) ⟨2490353, by rfl⟩ : syracuseStep 3320471 = 4980707) B4980707
theorem B2213647 : Blo 2213435 2213647 := bstep (se 1 (by rfl) ⟨1660235, by rfl⟩ : syracuseStep 2213647 = 3320471) B3320471
theorem B3320477 : Blo 2213435 3320477 := bbase (se 3 (by rfl) ⟨622589, by rfl⟩ : syracuseStep 3320477 = 1245179) (by norm_num)
theorem B2213651 : Blo 2213435 2213651 := bstep (se 1 (by rfl) ⟨1660238, by rfl⟩ : syracuseStep 2213651 = 3320477) B3320477
theorem B4980725 : Blo 2213435 4980725 := bbase (se 5 (by rfl) ⟨233471, by rfl⟩ : syracuseStep 4980725 = 466943) (by norm_num)
theorem B3320483 : Blo 2213435 3320483 := bstep (se 1 (by rfl) ⟨2490362, by rfl⟩ : syracuseStep 3320483 = 4980725) B4980725
theorem B2213655 : Blo 2213435 2213655 := bstep (se 1 (by rfl) ⟨1660241, by rfl⟩ : syracuseStep 2213655 = 3320483) B3320483
theorem B2769733 : Blo 2213435 2769733 := bbase (se 4 (by rfl) ⟨259662, by rfl⟩ : syracuseStep 2769733 = 519325) (by norm_num)
theorem B14771909 : Blo 2213435 14771909 := bstep (se 4 (by rfl) ⟨1384866, by rfl⟩ : syracuseStep 14771909 = 2769733) B2769733
theorem B9847939 : Blo 2213435 9847939 := bstep (se 1 (by rfl) ⟨7385954, by rfl⟩ : syracuseStep 9847939 = 14771909) B14771909
theorem B13130585 : Blo 2213435 13130585 := bstep (se 2 (by rfl) ⟨4923969, by rfl⟩ : syracuseStep 13130585 = 9847939) B9847939
theorem B8753723 : Blo 2213435 8753723 := bstep (se 1 (by rfl) ⟨6565292, by rfl⟩ : syracuseStep 8753723 = 13130585) B13130585
theorem B5835815 : Blo 2213435 5835815 := bstep (se 1 (by rfl) ⟨4376861, by rfl⟩ : syracuseStep 5835815 = 8753723) B8753723
theorem B3890543 : Blo 2213435 3890543 := bstep (se 1 (by rfl) ⟨2917907, by rfl⟩ : syracuseStep 3890543 = 5835815) B5835815
theorem B41499125 : Blo 2213435 41499125 := bstep (se 5 (by rfl) ⟨1945271, by rfl⟩ : syracuseStep 41499125 = 3890543) B3890543
theorem B27666083 : Blo 2213435 27666083 := bstep (se 1 (by rfl) ⟨20749562, by rfl⟩ : syracuseStep 27666083 = 41499125) B41499125
theorem B73776221 : Blo 2213435 73776221 := bstep (se 3 (by rfl) ⟨13833041, by rfl⟩ : syracuseStep 73776221 = 27666083) B27666083
theorem B786946357 : Blo 2213435 786946357 := bstep (se 5 (by rfl) ⟨36888110, by rfl⟩ : syracuseStep 786946357 = 73776221) B73776221
theorem B1049261809 : Blo 2213435 1049261809 := bstep (se 2 (by rfl) ⟨393473178, by rfl⟩ : syracuseStep 1049261809 = 786946357) B786946357
theorem B1399015745 : Blo 2213435 1399015745 := bstep (se 2 (by rfl) ⟨524630904, by rfl⟩ : syracuseStep 1399015745 = 1049261809) B1049261809
theorem B932677163 : Blo 2213435 932677163 := bstep (se 1 (by rfl) ⟨699507872, by rfl⟩ : syracuseStep 932677163 = 1399015745) B1399015745
theorem B621784775 : Blo 2213435 621784775 := bstep (se 1 (by rfl) ⟨466338581, by rfl⟩ : syracuseStep 621784775 = 932677163) B932677163
theorem B414523183 : Blo 2213435 414523183 := bstep (se 1 (by rfl) ⟨310892387, by rfl⟩ : syracuseStep 414523183 = 621784775) B621784775
theorem B552697577 : Blo 2213435 552697577 := bstep (se 2 (by rfl) ⟨207261591, by rfl⟩ : syracuseStep 552697577 = 414523183) B414523183
theorem B368465051 : Blo 2213435 368465051 := bstep (se 1 (by rfl) ⟨276348788, by rfl⟩ : syracuseStep 368465051 = 552697577) B552697577
theorem B245643367 : Blo 2213435 245643367 := bstep (se 1 (by rfl) ⟨184232525, by rfl⟩ : syracuseStep 245643367 = 368465051) B368465051
theorem B327524489 : Blo 2213435 327524489 := bstep (se 2 (by rfl) ⟨122821683, by rfl⟩ : syracuseStep 327524489 = 245643367) B245643367
theorem B218349659 : Blo 2213435 218349659 := bstep (se 1 (by rfl) ⟨163762244, by rfl⟩ : syracuseStep 218349659 = 327524489) B327524489
theorem B145566439 : Blo 2213435 145566439 := bstep (se 1 (by rfl) ⟨109174829, by rfl⟩ : syracuseStep 145566439 = 218349659) B218349659
theorem B776354341 : Blo 2213435 776354341 := bstep (se 4 (by rfl) ⟨72783219, by rfl⟩ : syracuseStep 776354341 = 145566439) B145566439
theorem B1035139121 : Blo 2213435 1035139121 := bstep (se 2 (by rfl) ⟨388177170, by rfl⟩ : syracuseStep 1035139121 = 776354341) B776354341
theorem B690092747 : Blo 2213435 690092747 := bstep (se 1 (by rfl) ⟨517569560, by rfl⟩ : syracuseStep 690092747 = 1035139121) B1035139121
theorem B460061831 : Blo 2213435 460061831 := bstep (se 1 (by rfl) ⟨345046373, by rfl⟩ : syracuseStep 460061831 = 690092747) B690092747
theorem B306707887 : Blo 2213435 306707887 := bstep (se 1 (by rfl) ⟨230030915, by rfl⟩ : syracuseStep 306707887 = 460061831) B460061831
theorem B1635775397 : Blo 2213435 1635775397 := bstep (se 4 (by rfl) ⟨153353943, by rfl⟩ : syracuseStep 1635775397 = 306707887) B306707887
theorem B1090516931 : Blo 2213435 1090516931 := bstep (se 1 (by rfl) ⟨817887698, by rfl⟩ : syracuseStep 1090516931 = 1635775397) B1635775397
theorem B727011287 : Blo 2213435 727011287 := bstep (se 1 (by rfl) ⟨545258465, by rfl⟩ : syracuseStep 727011287 = 1090516931) B1090516931
theorem B484674191 : Blo 2213435 484674191 := bstep (se 1 (by rfl) ⟨363505643, by rfl⟩ : syracuseStep 484674191 = 727011287) B727011287
theorem B323116127 : Blo 2213435 323116127 := bstep (se 1 (by rfl) ⟨242337095, by rfl⟩ : syracuseStep 323116127 = 484674191) B484674191
theorem B215410751 : Blo 2213435 215410751 := bstep (se 1 (by rfl) ⟨161558063, by rfl⟩ : syracuseStep 215410751 = 323116127) B323116127
theorem B143607167 : Blo 2213435 143607167 := bstep (se 1 (by rfl) ⟨107705375, by rfl⟩ : syracuseStep 143607167 = 215410751) B215410751
theorem B95738111 : Blo 2213435 95738111 := bstep (se 1 (by rfl) ⟨71803583, by rfl⟩ : syracuseStep 95738111 = 143607167) B143607167
theorem B63825407 : Blo 2213435 63825407 := bstep (se 1 (by rfl) ⟨47869055, by rfl⟩ : syracuseStep 63825407 = 95738111) B95738111
theorem B42550271 : Blo 2213435 42550271 := bstep (se 1 (by rfl) ⟨31912703, by rfl⟩ : syracuseStep 42550271 = 63825407) B63825407
theorem B28366847 : Blo 2213435 28366847 := bstep (se 1 (by rfl) ⟨21275135, by rfl⟩ : syracuseStep 28366847 = 42550271) B42550271
theorem B18911231 : Blo 2213435 18911231 := bstep (se 1 (by rfl) ⟨14183423, by rfl⟩ : syracuseStep 18911231 = 28366847) B28366847
theorem B12607487 : Blo 2213435 12607487 := bstep (se 1 (by rfl) ⟨9455615, by rfl⟩ : syracuseStep 12607487 = 18911231) B18911231
theorem B8404991 : Blo 2213435 8404991 := bstep (se 1 (by rfl) ⟨6303743, by rfl⟩ : syracuseStep 8404991 = 12607487) B12607487
theorem B5603327 : Blo 2213435 5603327 := bstep (se 1 (by rfl) ⟨4202495, by rfl⟩ : syracuseStep 5603327 = 8404991) B8404991
theorem B3735551 : Blo 2213435 3735551 := bstep (se 1 (by rfl) ⟨2801663, by rfl⟩ : syracuseStep 3735551 = 5603327) B5603327
theorem B2490367 : Blo 2213435 2490367 := bstep (se 1 (by rfl) ⟨1867775, by rfl⟩ : syracuseStep 2490367 = 3735551) B3735551
theorem B3320489 : Blo 2213435 3320489 := bstep (se 2 (by rfl) ⟨1245183, by rfl⟩ : syracuseStep 3320489 = 2490367) B2490367
theorem B2213659 : Blo 2213435 2213659 := bstep (se 1 (by rfl) ⟨1660244, by rfl⟩ : syracuseStep 2213659 = 3320489) B3320489
theorem B3151877 : Blo 2213435 3151877 := bbase (se 4 (by rfl) ⟨295488, by rfl⟩ : syracuseStep 3151877 = 590977) (by norm_num)
theorem B8405005 : Blo 2213435 8405005 := bstep (se 3 (by rfl) ⟨1575938, by rfl⟩ : syracuseStep 8405005 = 3151877) B3151877
theorem B11206673 : Blo 2213435 11206673 := bstep (se 2 (by rfl) ⟨4202502, by rfl⟩ : syracuseStep 11206673 = 8405005) B8405005
theorem B7471115 : Blo 2213435 7471115 := bstep (se 1 (by rfl) ⟨5603336, by rfl⟩ : syracuseStep 7471115 = 11206673) B11206673
theorem B4980743 : Blo 2213435 4980743 := bstep (se 1 (by rfl) ⟨3735557, by rfl⟩ : syracuseStep 4980743 = 7471115) B7471115
theorem B3320495 : Blo 2213435 3320495 := bstep (se 1 (by rfl) ⟨2490371, by rfl⟩ : syracuseStep 3320495 = 4980743) B4980743
theorem B2213663 : Blo 2213435 2213663 := bstep (se 1 (by rfl) ⟨1660247, by rfl⟩ : syracuseStep 2213663 = 3320495) B3320495
theorem B3320501 : Blo 2213435 3320501 := bbase (se 5 (by rfl) ⟨155648, by rfl⟩ : syracuseStep 3320501 = 311297) (by norm_num)
theorem B2213667 : Blo 2213435 2213667 := bstep (se 1 (by rfl) ⟨1660250, by rfl⟩ : syracuseStep 2213667 = 3320501) B3320501
theorem B5603357 : Blo 2213435 5603357 := bbase (se 3 (by rfl) ⟨1050629, by rfl⟩ : syracuseStep 5603357 = 2101259) (by norm_num)
theorem B3735571 : Blo 2213435 3735571 := bstep (se 1 (by rfl) ⟨2801678, by rfl⟩ : syracuseStep 3735571 = 5603357) B5603357
theorem B4980761 : Blo 2213435 4980761 := bstep (se 2 (by rfl) ⟨1867785, by rfl⟩ : syracuseStep 4980761 = 3735571) B3735571
theorem B3320507 : Blo 2213435 3320507 := bstep (se 1 (by rfl) ⟨2490380, by rfl⟩ : syracuseStep 3320507 = 4980761) B4980761
theorem B2213671 : Blo 2213435 2213671 := bstep (se 1 (by rfl) ⟨1660253, by rfl⟩ : syracuseStep 2213671 = 3320507) B3320507
theorem B2490385 : Blo 2213435 2490385 := bbase (se 2 (by rfl) ⟨933894, by rfl⟩ : syracuseStep 2490385 = 1867789) (by norm_num)
theorem B3320513 : Blo 2213435 3320513 := bstep (se 2 (by rfl) ⟨1245192, by rfl⟩ : syracuseStep 3320513 = 2490385) B2490385
theorem B2213675 : Blo 2213435 2213675 := bstep (se 1 (by rfl) ⟨1660256, by rfl⟩ : syracuseStep 2213675 = 3320513) B3320513
theorem B4202533 : Blo 2213435 4202533 := bbase (se 4 (by rfl) ⟨393987, by rfl⟩ : syracuseStep 4202533 = 787975) (by norm_num)
theorem B5603377 : Blo 2213435 5603377 := bstep (se 2 (by rfl) ⟨2101266, by rfl⟩ : syracuseStep 5603377 = 4202533) B4202533
theorem B7471169 : Blo 2213435 7471169 := bstep (se 2 (by rfl) ⟨2801688, by rfl⟩ : syracuseStep 7471169 = 5603377) B5603377
theorem B4980779 : Blo 2213435 4980779 := bstep (se 1 (by rfl) ⟨3735584, by rfl⟩ : syracuseStep 4980779 = 7471169) B7471169
theorem B3320519 : Blo 2213435 3320519 := bstep (se 1 (by rfl) ⟨2490389, by rfl⟩ : syracuseStep 3320519 = 4980779) B4980779
theorem B2213679 : Blo 2213435 2213679 := bstep (se 1 (by rfl) ⟨1660259, by rfl⟩ : syracuseStep 2213679 = 3320519) B3320519
theorem B3320525 : Blo 2213435 3320525 := bbase (se 3 (by rfl) ⟨622598, by rfl⟩ : syracuseStep 3320525 = 1245197) (by norm_num)
theorem B2213683 : Blo 2213435 2213683 := bstep (se 1 (by rfl) ⟨1660262, by rfl⟩ : syracuseStep 2213683 = 3320525) B3320525
theorem B4980797 : Blo 2213435 4980797 := bbase (se 3 (by rfl) ⟨933899, by rfl⟩ : syracuseStep 4980797 = 1867799) (by norm_num)
theorem B3320531 : Blo 2213435 3320531 := bstep (se 1 (by rfl) ⟨2490398, by rfl⟩ : syracuseStep 3320531 = 4980797) B4980797
theorem B2213687 : Blo 2213435 2213687 := bstep (se 1 (by rfl) ⟨1660265, by rfl⟩ : syracuseStep 2213687 = 3320531) B3320531
theorem B3735605 : Blo 2213435 3735605 := bbase (se 5 (by rfl) ⟨175106, by rfl⟩ : syracuseStep 3735605 = 350213) (by norm_num)
theorem B2490403 : Blo 2213435 2490403 := bstep (se 1 (by rfl) ⟨1867802, by rfl⟩ : syracuseStep 2490403 = 3735605) B3735605
theorem B3320537 : Blo 2213435 3320537 := bstep (se 2 (by rfl) ⟨1245201, by rfl⟩ : syracuseStep 3320537 = 2490403) B2490403
theorem B2213691 : Blo 2213435 2213691 := bstep (se 1 (by rfl) ⟨1660268, by rfl⟩ : syracuseStep 2213691 = 3320537) B3320537
theorem B6303845 : Blo 2213435 6303845 := bbase (se 4 (by rfl) ⟨590985, by rfl⟩ : syracuseStep 6303845 = 1181971) (by norm_num)
theorem B16810253 : Blo 2213435 16810253 := bstep (se 3 (by rfl) ⟨3151922, by rfl⟩ : syracuseStep 16810253 = 6303845) B6303845
theorem B11206835 : Blo 2213435 11206835 := bstep (se 1 (by rfl) ⟨8405126, by rfl⟩ : syracuseStep 11206835 = 16810253) B16810253
theorem B7471223 : Blo 2213435 7471223 := bstep (se 1 (by rfl) ⟨5603417, by rfl⟩ : syracuseStep 7471223 = 11206835) B11206835
theorem B4980815 : Blo 2213435 4980815 := bstep (se 1 (by rfl) ⟨3735611, by rfl⟩ : syracuseStep 4980815 = 7471223) B7471223
theorem B3320543 : Blo 2213435 3320543 := bstep (se 1 (by rfl) ⟨2490407, by rfl⟩ : syracuseStep 3320543 = 4980815) B4980815
theorem B2213695 : Blo 2213435 2213695 := bstep (se 1 (by rfl) ⟨1660271, by rfl⟩ : syracuseStep 2213695 = 3320543) B3320543
theorem B3320549 : Blo 2213435 3320549 := bbase (se 4 (by rfl) ⟨311301, by rfl⟩ : syracuseStep 3320549 = 622603) (by norm_num)
theorem B2213699 : Blo 2213435 2213699 := bstep (se 1 (by rfl) ⟨1660274, by rfl⟩ : syracuseStep 2213699 = 3320549) B3320549
theorem B7573189 : Blo 2213435 7573189 := bbase (se 4 (by rfl) ⟨709986, by rfl⟩ : syracuseStep 7573189 = 1419973) (by norm_num)
theorem B10097585 : Blo 2213435 10097585 := bstep (se 2 (by rfl) ⟨3786594, by rfl⟩ : syracuseStep 10097585 = 7573189) B7573189
theorem B6731723 : Blo 2213435 6731723 := bstep (se 1 (by rfl) ⟨5048792, by rfl⟩ : syracuseStep 6731723 = 10097585) B10097585
theorem B4487815 : Blo 2213435 4487815 := bstep (se 1 (by rfl) ⟨3365861, by rfl⟩ : syracuseStep 4487815 = 6731723) B6731723
theorem B5983753 : Blo 2213435 5983753 := bstep (se 2 (by rfl) ⟨2243907, by rfl⟩ : syracuseStep 5983753 = 4487815) B4487815
theorem B7978337 : Blo 2213435 7978337 := bstep (se 2 (by rfl) ⟨2991876, by rfl⟩ : syracuseStep 7978337 = 5983753) B5983753
theorem B5318891 : Blo 2213435 5318891 := bstep (se 1 (by rfl) ⟨3989168, by rfl⟩ : syracuseStep 5318891 = 7978337) B7978337
theorem B3545927 : Blo 2213435 3545927 := bstep (se 1 (by rfl) ⟨2659445, by rfl⟩ : syracuseStep 3545927 = 5318891) B5318891
theorem B2363951 : Blo 2213435 2363951 := bstep (se 1 (by rfl) ⟨1772963, by rfl⟩ : syracuseStep 2363951 = 3545927) B3545927
theorem B6303869 : Blo 2213435 6303869 := bstep (se 3 (by rfl) ⟨1181975, by rfl⟩ : syracuseStep 6303869 = 2363951) B2363951
theorem B4202579 : Blo 2213435 4202579 := bstep (se 1 (by rfl) ⟨3151934, by rfl⟩ : syracuseStep 4202579 = 6303869) B6303869
theorem B2801719 : Blo 2213435 2801719 := bstep (se 1 (by rfl) ⟨2101289, by rfl⟩ : syracuseStep 2801719 = 4202579) B4202579
theorem B3735625 : Blo 2213435 3735625 := bstep (se 2 (by rfl) ⟨1400859, by rfl⟩ : syracuseStep 3735625 = 2801719) B2801719
theorem B4980833 : Blo 2213435 4980833 := bstep (se 2 (by rfl) ⟨1867812, by rfl⟩ : syracuseStep 4980833 = 3735625) B3735625
theorem B3320555 : Blo 2213435 3320555 := bstep (se 1 (by rfl) ⟨2490416, by rfl⟩ : syracuseStep 3320555 = 4980833) B4980833
theorem B2213703 : Blo 2213435 2213703 := bstep (se 1 (by rfl) ⟨1660277, by rfl⟩ : syracuseStep 2213703 = 3320555) B3320555
theorem B2490421 : Blo 2213435 2490421 := bbase (se 5 (by rfl) ⟨116738, by rfl⟩ : syracuseStep 2490421 = 233477) (by norm_num)
theorem B3320561 : Blo 2213435 3320561 := bstep (se 2 (by rfl) ⟨1245210, by rfl⟩ : syracuseStep 3320561 = 2490421) B2490421
theorem B2213707 : Blo 2213435 2213707 := bstep (se 1 (by rfl) ⟨1660280, by rfl⟩ : syracuseStep 2213707 = 3320561) B3320561
theorem B2801729 : Blo 2213435 2801729 := bbase (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) (by norm_num)
theorem B7471277 : Blo 2213435 7471277 := bstep (se 3 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 7471277 = 2801729) B2801729
theorem B4980851 : Blo 2213435 4980851 := bstep (se 1 (by rfl) ⟨3735638, by rfl⟩ : syracuseStep 4980851 = 7471277) B7471277
theorem B3320567 : Blo 2213435 3320567 := bstep (se 1 (by rfl) ⟨2490425, by rfl⟩ : syracuseStep 3320567 = 4980851) B4980851
theorem B2213711 : Blo 2213435 2213711 := bstep (se 1 (by rfl) ⟨1660283, by rfl⟩ : syracuseStep 2213711 = 3320567) B3320567
theorem B3320573 : Blo 2213435 3320573 := bbase (se 3 (by rfl) ⟨622607, by rfl⟩ : syracuseStep 3320573 = 1245215) (by norm_num)
theorem B2213715 : Blo 2213435 2213715 := bstep (se 1 (by rfl) ⟨1660286, by rfl⟩ : syracuseStep 2213715 = 3320573) B3320573
theorem B4980869 : Blo 2213435 4980869 := bbase (se 4 (by rfl) ⟨466956, by rfl⟩ : syracuseStep 4980869 = 933913) (by norm_num)
theorem B3320579 : Blo 2213435 3320579 := bstep (se 1 (by rfl) ⟨2490434, by rfl⟩ : syracuseStep 3320579 = 4980869) B4980869
theorem B2213719 : Blo 2213435 2213719 := bstep (se 1 (by rfl) ⟨1660289, by rfl⟩ : syracuseStep 2213719 = 3320579) B3320579
theorem B4259957 : Blo 2213435 4259957 := bbase (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) (by norm_num)
theorem B45439541 : Blo 2213435 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B30293027 : Blo 2213435 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B20195351 : Blo 2213435 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B13463567 : Blo 2213435 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B8975711 : Blo 2213435 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B5983807 : Blo 2213435 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B7978409 : Blo 2213435 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B5318939 : Blo 2213435 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B3545959 : Blo 2213435 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B4727945 : Blo 2213435 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B3151963 : Blo 2213435 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B4202617 : Blo 2213435 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B5603489 : Blo 2213435 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B3735659 : Blo 2213435 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B2490439 : Blo 2213435 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B3320585 : Blo 2213435 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B2213723 : Blo 2213435 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B11206997 : Blo 2213435 11206997 := bbase (se 10 (by rfl) ⟨16416, by rfl⟩ : syracuseStep 11206997 = 32833) (by norm_num)
theorem B7471331 : Blo 2213435 7471331 := bstep (se 1 (by rfl) ⟨5603498, by rfl⟩ : syracuseStep 7471331 = 11206997) B11206997
theorem B4980887 : Blo 2213435 4980887 := bstep (se 1 (by rfl) ⟨3735665, by rfl⟩ : syracuseStep 4980887 = 7471331) B7471331
theorem B3320591 : Blo 2213435 3320591 := bstep (se 1 (by rfl) ⟨2490443, by rfl⟩ : syracuseStep 3320591 = 4980887) B4980887
theorem B2213727 : Blo 2213435 2213727 := bstep (se 1 (by rfl) ⟨1660295, by rfl⟩ : syracuseStep 2213727 = 3320591) B3320591
theorem B3320597 : Blo 2213435 3320597 := bbase (se 6 (by rfl) ⟨77826, by rfl⟩ : syracuseStep 3320597 = 155653) (by norm_num)
theorem B2213731 : Blo 2213435 2213731 := bstep (se 1 (by rfl) ⟨1660298, by rfl⟩ : syracuseStep 2213731 = 3320597) B3320597
theorem B3365909 : Blo 2213435 3365909 := bbase (se 6 (by rfl) ⟨78888, by rfl⟩ : syracuseStep 3365909 = 157777) (by norm_num)
theorem B2243939 : Blo 2213435 2243939 := bstep (se 1 (by rfl) ⟨1682954, by rfl⟩ : syracuseStep 2243939 = 3365909) B3365909
theorem B5983837 : Blo 2213435 5983837 := bstep (se 3 (by rfl) ⟨1121969, by rfl⟩ : syracuseStep 5983837 = 2243939) B2243939
theorem B31913797 : Blo 2213435 31913797 := bstep (se 4 (by rfl) ⟨2991918, by rfl⟩ : syracuseStep 31913797 = 5983837) B5983837
theorem B42551729 : Blo 2213435 42551729 := bstep (se 2 (by rfl) ⟨15956898, by rfl⟩ : syracuseStep 42551729 = 31913797) B31913797
theorem B28367819 : Blo 2213435 28367819 := bstep (se 1 (by rfl) ⟨21275864, by rfl⟩ : syracuseStep 28367819 = 42551729) B42551729
theorem B18911879 : Blo 2213435 18911879 := bstep (se 1 (by rfl) ⟨14183909, by rfl⟩ : syracuseStep 18911879 = 28367819) B28367819
theorem B12607919 : Blo 2213435 12607919 := bstep (se 1 (by rfl) ⟨9455939, by rfl⟩ : syracuseStep 12607919 = 18911879) B18911879
theorem B8405279 : Blo 2213435 8405279 := bstep (se 1 (by rfl) ⟨6303959, by rfl⟩ : syracuseStep 8405279 = 12607919) B12607919
theorem B5603519 : Blo 2213435 5603519 := bstep (se 1 (by rfl) ⟨4202639, by rfl⟩ : syracuseStep 5603519 = 8405279) B8405279
theorem B3735679 : Blo 2213435 3735679 := bstep (se 1 (by rfl) ⟨2801759, by rfl⟩ : syracuseStep 3735679 = 5603519) B5603519
theorem B4980905 : Blo 2213435 4980905 := bstep (se 2 (by rfl) ⟨1867839, by rfl⟩ : syracuseStep 4980905 = 3735679) B3735679
theorem B3320603 : Blo 2213435 3320603 := bstep (se 1 (by rfl) ⟨2490452, by rfl⟩ : syracuseStep 3320603 = 4980905) B4980905
theorem B2213735 : Blo 2213435 2213735 := bstep (se 1 (by rfl) ⟨1660301, by rfl⟩ : syracuseStep 2213735 = 3320603) B3320603
theorem B2490457 : Blo 2213435 2490457 := bbase (se 2 (by rfl) ⟨933921, by rfl⟩ : syracuseStep 2490457 = 1867843) (by norm_num)
theorem B3320609 : Blo 2213435 3320609 := bstep (se 2 (by rfl) ⟨1245228, by rfl⟩ : syracuseStep 3320609 = 2490457) B2490457
theorem B2213739 : Blo 2213435 2213739 := bstep (se 1 (by rfl) ⟨1660304, by rfl⟩ : syracuseStep 2213739 = 3320609) B3320609
theorem B2659493 : Blo 2213435 2659493 := bbase (se 4 (by rfl) ⟨249327, by rfl⟩ : syracuseStep 2659493 = 498655) (by norm_num)
theorem B7091981 : Blo 2213435 7091981 := bstep (se 3 (by rfl) ⟨1329746, by rfl⟩ : syracuseStep 7091981 = 2659493) B2659493
theorem B4727987 : Blo 2213435 4727987 := bstep (se 1 (by rfl) ⟨3545990, by rfl⟩ : syracuseStep 4727987 = 7091981) B7091981
theorem B3151991 : Blo 2213435 3151991 := bstep (se 1 (by rfl) ⟨2363993, by rfl⟩ : syracuseStep 3151991 = 4727987) B4727987
theorem B8405309 : Blo 2213435 8405309 := bstep (se 3 (by rfl) ⟨1575995, by rfl⟩ : syracuseStep 8405309 = 3151991) B3151991
theorem B5603539 : Blo 2213435 5603539 := bstep (se 1 (by rfl) ⟨4202654, by rfl⟩ : syracuseStep 5603539 = 8405309) B8405309
theorem B7471385 : Blo 2213435 7471385 := bstep (se 2 (by rfl) ⟨2801769, by rfl⟩ : syracuseStep 7471385 = 5603539) B5603539
theorem B4980923 : Blo 2213435 4980923 := bstep (se 1 (by rfl) ⟨3735692, by rfl⟩ : syracuseStep 4980923 = 7471385) B7471385
theorem B3320615 : Blo 2213435 3320615 := bstep (se 1 (by rfl) ⟨2490461, by rfl⟩ : syracuseStep 3320615 = 4980923) B4980923
theorem B2213743 : Blo 2213435 2213743 := bstep (se 1 (by rfl) ⟨1660307, by rfl⟩ : syracuseStep 2213743 = 3320615) B3320615
theorem B3320621 : Blo 2213435 3320621 := bbase (se 3 (by rfl) ⟨622616, by rfl⟩ : syracuseStep 3320621 = 1245233) (by norm_num)
theorem B2213747 : Blo 2213435 2213747 := bstep (se 1 (by rfl) ⟨1660310, by rfl⟩ : syracuseStep 2213747 = 3320621) B3320621
theorem B4980941 : Blo 2213435 4980941 := bbase (se 3 (by rfl) ⟨933926, by rfl⟩ : syracuseStep 4980941 = 1867853) (by norm_num)
theorem B3320627 : Blo 2213435 3320627 := bstep (se 1 (by rfl) ⟨2490470, by rfl⟩ : syracuseStep 3320627 = 4980941) B4980941
theorem B2213751 : Blo 2213435 2213751 := bstep (se 1 (by rfl) ⟨1660313, by rfl⟩ : syracuseStep 2213751 = 3320627) B3320627
theorem B2801785 : Blo 2213435 2801785 := bbase (se 2 (by rfl) ⟨1050669, by rfl⟩ : syracuseStep 2801785 = 2101339) (by norm_num)
theorem B3735713 : Blo 2213435 3735713 := bstep (se 2 (by rfl) ⟨1400892, by rfl⟩ : syracuseStep 3735713 = 2801785) B2801785
theorem B2490475 : Blo 2213435 2490475 := bstep (se 1 (by rfl) ⟨1867856, by rfl⟩ : syracuseStep 2490475 = 3735713) B3735713
theorem B3320633 : Blo 2213435 3320633 := bstep (se 2 (by rfl) ⟨1245237, by rfl⟩ : syracuseStep 3320633 = 2490475) B2490475
theorem B2213755 : Blo 2213435 2213755 := bstep (se 1 (by rfl) ⟨1660316, by rfl⟩ : syracuseStep 2213755 = 3320633) B3320633
theorem B20195669 : Blo 2213435 20195669 := bbase (se 10 (by rfl) ⟨29583, by rfl⟩ : syracuseStep 20195669 = 59167) (by norm_num)
theorem B53855117 : Blo 2213435 53855117 := bstep (se 3 (by rfl) ⟨10097834, by rfl⟩ : syracuseStep 53855117 = 20195669) B20195669
theorem B35903411 : Blo 2213435 35903411 := bstep (se 1 (by rfl) ⟨26927558, by rfl⟩ : syracuseStep 35903411 = 53855117) B53855117
theorem B23935607 : Blo 2213435 23935607 := bstep (se 1 (by rfl) ⟨17951705, by rfl⟩ : syracuseStep 23935607 = 35903411) B35903411
theorem B15957071 : Blo 2213435 15957071 := bstep (se 1 (by rfl) ⟨11967803, by rfl⟩ : syracuseStep 15957071 = 23935607) B23935607
theorem B10638047 : Blo 2213435 10638047 := bstep (se 1 (by rfl) ⟨7978535, by rfl⟩ : syracuseStep 10638047 = 15957071) B15957071
theorem B7092031 : Blo 2213435 7092031 := bstep (se 1 (by rfl) ⟨5319023, by rfl⟩ : syracuseStep 7092031 = 10638047) B10638047
theorem B9456041 : Blo 2213435 9456041 := bstep (se 2 (by rfl) ⟨3546015, by rfl⟩ : syracuseStep 9456041 = 7092031) B7092031
theorem B25216109 : Blo 2213435 25216109 := bstep (se 3 (by rfl) ⟨4728020, by rfl⟩ : syracuseStep 25216109 = 9456041) B9456041
theorem B16810739 : Blo 2213435 16810739 := bstep (se 1 (by rfl) ⟨12608054, by rfl⟩ : syracuseStep 16810739 = 25216109) B25216109
theorem B11207159 : Blo 2213435 11207159 := bstep (se 1 (by rfl) ⟨8405369, by rfl⟩ : syracuseStep 11207159 = 16810739) B16810739
theorem B7471439 : Blo 2213435 7471439 := bstep (se 1 (by rfl) ⟨5603579, by rfl⟩ : syracuseStep 7471439 = 11207159) B11207159
theorem B4980959 : Blo 2213435 4980959 := bstep (se 1 (by rfl) ⟨3735719, by rfl⟩ : syracuseStep 4980959 = 7471439) B7471439
theorem B3320639 : Blo 2213435 3320639 := bstep (se 1 (by rfl) ⟨2490479, by rfl⟩ : syracuseStep 3320639 = 4980959) B4980959
theorem B2213759 : Blo 2213435 2213759 := bstep (se 1 (by rfl) ⟨1660319, by rfl⟩ : syracuseStep 2213759 = 3320639) B3320639
theorem B3320645 : Blo 2213435 3320645 := bbase (se 4 (by rfl) ⟨311310, by rfl⟩ : syracuseStep 3320645 = 622621) (by norm_num)
theorem B2213763 : Blo 2213435 2213763 := bstep (se 1 (by rfl) ⟨1660322, by rfl⟩ : syracuseStep 2213763 = 3320645) B3320645
theorem B3735733 : Blo 2213435 3735733 := bbase (se 5 (by rfl) ⟨175112, by rfl⟩ : syracuseStep 3735733 = 350225) (by norm_num)
theorem B4980977 : Blo 2213435 4980977 := bstep (se 2 (by rfl) ⟨1867866, by rfl⟩ : syracuseStep 4980977 = 3735733) B3735733
theorem B3320651 : Blo 2213435 3320651 := bstep (se 1 (by rfl) ⟨2490488, by rfl⟩ : syracuseStep 3320651 = 4980977) B4980977
theorem B2213767 : Blo 2213435 2213767 := bstep (se 1 (by rfl) ⟨1660325, by rfl⟩ : syracuseStep 2213767 = 3320651) B3320651
theorem B2490493 : Blo 2213435 2490493 := bbase (se 3 (by rfl) ⟨466967, by rfl⟩ : syracuseStep 2490493 = 933935) (by norm_num)
theorem B3320657 : Blo 2213435 3320657 := bstep (se 2 (by rfl) ⟨1245246, by rfl⟩ : syracuseStep 3320657 = 2490493) B2490493
theorem B2213771 : Blo 2213435 2213771 := bstep (se 1 (by rfl) ⟨1660328, by rfl⟩ : syracuseStep 2213771 = 3320657) B3320657
theorem B7471493 : Blo 2213435 7471493 := bbase (se 4 (by rfl) ⟨700452, by rfl⟩ : syracuseStep 7471493 = 1400905) (by norm_num)
theorem B4980995 : Blo 2213435 4980995 := bstep (se 1 (by rfl) ⟨3735746, by rfl⟩ : syracuseStep 4980995 = 7471493) B7471493
theorem B3320663 : Blo 2213435 3320663 := bstep (se 1 (by rfl) ⟨2490497, by rfl⟩ : syracuseStep 3320663 = 4980995) B4980995
theorem B2213775 : Blo 2213435 2213775 := bstep (se 1 (by rfl) ⟨1660331, by rfl⟩ : syracuseStep 2213775 = 3320663) B3320663
theorem B3320669 : Blo 2213435 3320669 := bbase (se 3 (by rfl) ⟨622625, by rfl⟩ : syracuseStep 3320669 = 1245251) (by norm_num)
theorem B2213779 : Blo 2213435 2213779 := bstep (se 1 (by rfl) ⟨1660334, by rfl⟩ : syracuseStep 2213779 = 3320669) B3320669
theorem B4981013 : Blo 2213435 4981013 := bbase (se 6 (by rfl) ⟨116742, by rfl⟩ : syracuseStep 4981013 = 233485) (by norm_num)
theorem B3320675 : Blo 2213435 3320675 := bstep (se 1 (by rfl) ⟨2490506, by rfl⟩ : syracuseStep 3320675 = 4981013) B4981013
theorem B2213783 : Blo 2213435 2213783 := bstep (se 1 (by rfl) ⟨1660337, by rfl⟩ : syracuseStep 2213783 = 3320675) B3320675
theorem B8405477 : Blo 2213435 8405477 := bbase (se 4 (by rfl) ⟨788013, by rfl⟩ : syracuseStep 8405477 = 1576027) (by norm_num)
theorem B5603651 : Blo 2213435 5603651 := bstep (se 1 (by rfl) ⟨4202738, by rfl⟩ : syracuseStep 5603651 = 8405477) B8405477
theorem B3735767 : Blo 2213435 3735767 := bstep (se 1 (by rfl) ⟨2801825, by rfl⟩ : syracuseStep 3735767 = 5603651) B5603651
theorem B2490511 : Blo 2213435 2490511 := bstep (se 1 (by rfl) ⟨1867883, by rfl⟩ : syracuseStep 2490511 = 3735767) B3735767
theorem B3320681 : Blo 2213435 3320681 := bstep (se 2 (by rfl) ⟨1245255, by rfl⟩ : syracuseStep 3320681 = 2490511) B2490511
theorem B2213787 : Blo 2213435 2213787 := bstep (se 1 (by rfl) ⟨1660340, by rfl⟩ : syracuseStep 2213787 = 3320681) B3320681
theorem B5319101 : Blo 2213435 5319101 := bbase (se 3 (by rfl) ⟨997331, by rfl⟩ : syracuseStep 5319101 = 1994663) (by norm_num)
theorem B3546067 : Blo 2213435 3546067 := bstep (se 1 (by rfl) ⟨2659550, by rfl⟩ : syracuseStep 3546067 = 5319101) B5319101
theorem B4728089 : Blo 2213435 4728089 := bstep (se 2 (by rfl) ⟨1773033, by rfl⟩ : syracuseStep 4728089 = 3546067) B3546067
theorem B12608237 : Blo 2213435 12608237 := bstep (se 3 (by rfl) ⟨2364044, by rfl⟩ : syracuseStep 12608237 = 4728089) B4728089
theorem B8405491 : Blo 2213435 8405491 := bstep (se 1 (by rfl) ⟨6304118, by rfl⟩ : syracuseStep 8405491 = 12608237) B12608237
theorem B11207321 : Blo 2213435 11207321 := bstep (se 2 (by rfl) ⟨4202745, by rfl⟩ : syracuseStep 11207321 = 8405491) B8405491
theorem B7471547 : Blo 2213435 7471547 := bstep (se 1 (by rfl) ⟨5603660, by rfl⟩ : syracuseStep 7471547 = 11207321) B11207321
theorem B4981031 : Blo 2213435 4981031 := bstep (se 1 (by rfl) ⟨3735773, by rfl⟩ : syracuseStep 4981031 = 7471547) B7471547
theorem B3320687 : Blo 2213435 3320687 := bstep (se 1 (by rfl) ⟨2490515, by rfl⟩ : syracuseStep 3320687 = 4981031) B4981031
theorem B2213791 : Blo 2213435 2213791 := bstep (se 1 (by rfl) ⟨1660343, by rfl⟩ : syracuseStep 2213791 = 3320687) B3320687
theorem B3320693 : Blo 2213435 3320693 := bbase (se 5 (by rfl) ⟨155657, by rfl⟩ : syracuseStep 3320693 = 311315) (by norm_num)
theorem B2213795 : Blo 2213435 2213795 := bstep (se 1 (by rfl) ⟨1660346, by rfl⟩ : syracuseStep 2213795 = 3320693) B3320693
theorem B3989341 : Blo 2213435 3989341 := bbase (se 3 (by rfl) ⟨748001, by rfl⟩ : syracuseStep 3989341 = 1496003) (by norm_num)
theorem B5319121 : Blo 2213435 5319121 := bstep (se 2 (by rfl) ⟨1994670, by rfl⟩ : syracuseStep 5319121 = 3989341) B3989341
theorem B7092161 : Blo 2213435 7092161 := bstep (se 2 (by rfl) ⟨2659560, by rfl⟩ : syracuseStep 7092161 = 5319121) B5319121
theorem B4728107 : Blo 2213435 4728107 := bstep (se 1 (by rfl) ⟨3546080, by rfl⟩ : syracuseStep 4728107 = 7092161) B7092161
theorem B3152071 : Blo 2213435 3152071 := bstep (se 1 (by rfl) ⟨2364053, by rfl⟩ : syracuseStep 3152071 = 4728107) B4728107
theorem B4202761 : Blo 2213435 4202761 := bstep (se 2 (by rfl) ⟨1576035, by rfl⟩ : syracuseStep 4202761 = 3152071) B3152071
theorem B5603681 : Blo 2213435 5603681 := bstep (se 2 (by rfl) ⟨2101380, by rfl⟩ : syracuseStep 5603681 = 4202761) B4202761
theorem B3735787 : Blo 2213435 3735787 := bstep (se 1 (by rfl) ⟨2801840, by rfl⟩ : syracuseStep 3735787 = 5603681) B5603681
theorem B4981049 : Blo 2213435 4981049 := bstep (se 2 (by rfl) ⟨1867893, by rfl⟩ : syracuseStep 4981049 = 3735787) B3735787
theorem B3320699 : Blo 2213435 3320699 := bstep (se 1 (by rfl) ⟨2490524, by rfl⟩ : syracuseStep 3320699 = 4981049) B4981049
theorem B2213799 : Blo 2213435 2213799 := bstep (se 1 (by rfl) ⟨1660349, by rfl⟩ : syracuseStep 2213799 = 3320699) B3320699
theorem B2490529 : Blo 2213435 2490529 := bbase (se 2 (by rfl) ⟨933948, by rfl⟩ : syracuseStep 2490529 = 1867897) (by norm_num)
theorem B3320705 : Blo 2213435 3320705 := bstep (se 2 (by rfl) ⟨1245264, by rfl⟩ : syracuseStep 3320705 = 2490529) B2490529
theorem B2213803 : Blo 2213435 2213803 := bstep (se 1 (by rfl) ⟨1660352, by rfl⟩ : syracuseStep 2213803 = 3320705) B3320705
theorem B5603701 : Blo 2213435 5603701 := bbase (se 5 (by rfl) ⟨262673, by rfl⟩ : syracuseStep 5603701 = 525347) (by norm_num)
theorem B7471601 : Blo 2213435 7471601 := bstep (se 2 (by rfl) ⟨2801850, by rfl⟩ : syracuseStep 7471601 = 5603701) B5603701
theorem B4981067 : Blo 2213435 4981067 := bstep (se 1 (by rfl) ⟨3735800, by rfl⟩ : syracuseStep 4981067 = 7471601) B7471601
theorem B3320711 : Blo 2213435 3320711 := bstep (se 1 (by rfl) ⟨2490533, by rfl⟩ : syracuseStep 3320711 = 4981067) B4981067
theorem B2213807 : Blo 2213435 2213807 := bstep (se 1 (by rfl) ⟨1660355, by rfl⟩ : syracuseStep 2213807 = 3320711) B3320711
theorem B3320717 : Blo 2213435 3320717 := bbase (se 3 (by rfl) ⟨622634, by rfl⟩ : syracuseStep 3320717 = 1245269) (by norm_num)
theorem B2213811 : Blo 2213435 2213811 := bstep (se 1 (by rfl) ⟨1660358, by rfl⟩ : syracuseStep 2213811 = 3320717) B3320717
theorem B4981085 : Blo 2213435 4981085 := bbase (se 3 (by rfl) ⟨933953, by rfl⟩ : syracuseStep 4981085 = 1867907) (by norm_num)
theorem B3320723 : Blo 2213435 3320723 := bstep (se 1 (by rfl) ⟨2490542, by rfl⟩ : syracuseStep 3320723 = 4981085) B4981085
theorem B2213815 : Blo 2213435 2213815 := bstep (se 1 (by rfl) ⟨1660361, by rfl⟩ : syracuseStep 2213815 = 3320723) B3320723
theorem B3735821 : Blo 2213435 3735821 := bbase (se 3 (by rfl) ⟨700466, by rfl⟩ : syracuseStep 3735821 = 1400933) (by norm_num)
theorem B2490547 : Blo 2213435 2490547 := bstep (se 1 (by rfl) ⟨1867910, by rfl⟩ : syracuseStep 2490547 = 3735821) B3735821
theorem B3320729 : Blo 2213435 3320729 := bstep (se 2 (by rfl) ⟨1245273, by rfl⟩ : syracuseStep 3320729 = 2490547) B2490547
theorem B2213819 : Blo 2213435 2213819 := bstep (se 1 (by rfl) ⟨1660364, by rfl⟩ : syracuseStep 2213819 = 3320729) B3320729
theorem B18912629 : Blo 2213435 18912629 := bbase (se 5 (by rfl) ⟨886529, by rfl⟩ : syracuseStep 18912629 = 1773059) (by norm_num)
theorem B12608419 : Blo 2213435 12608419 := bstep (se 1 (by rfl) ⟨9456314, by rfl⟩ : syracuseStep 12608419 = 18912629) B18912629
theorem B16811225 : Blo 2213435 16811225 := bstep (se 2 (by rfl) ⟨6304209, by rfl⟩ : syracuseStep 16811225 = 12608419) B12608419
theorem B11207483 : Blo 2213435 11207483 := bstep (se 1 (by rfl) ⟨8405612, by rfl⟩ : syracuseStep 11207483 = 16811225) B16811225
theorem B7471655 : Blo 2213435 7471655 := bstep (se 1 (by rfl) ⟨5603741, by rfl⟩ : syracuseStep 7471655 = 11207483) B11207483
theorem B4981103 : Blo 2213435 4981103 := bstep (se 1 (by rfl) ⟨3735827, by rfl⟩ : syracuseStep 4981103 = 7471655) B7471655
theorem B3320735 : Blo 2213435 3320735 := bstep (se 1 (by rfl) ⟨2490551, by rfl⟩ : syracuseStep 3320735 = 4981103) B4981103
theorem B2213823 : Blo 2213435 2213823 := bstep (se 1 (by rfl) ⟨1660367, by rfl⟩ : syracuseStep 2213823 = 3320735) B3320735
theorem B3320741 : Blo 2213435 3320741 := bbase (se 4 (by rfl) ⟨311319, by rfl⟩ : syracuseStep 3320741 = 622639) (by norm_num)
theorem B2213827 : Blo 2213435 2213827 := bstep (se 1 (by rfl) ⟨1660370, by rfl⟩ : syracuseStep 2213827 = 3320741) B3320741
theorem B2801881 : Blo 2213435 2801881 := bbase (se 2 (by rfl) ⟨1050705, by rfl⟩ : syracuseStep 2801881 = 2101411) (by norm_num)
theorem B3735841 : Blo 2213435 3735841 := bstep (se 2 (by rfl) ⟨1400940, by rfl⟩ : syracuseStep 3735841 = 2801881) B2801881
theorem B4981121 : Blo 2213435 4981121 := bstep (se 2 (by rfl) ⟨1867920, by rfl⟩ : syracuseStep 4981121 = 3735841) B3735841
theorem B3320747 : Blo 2213435 3320747 := bstep (se 1 (by rfl) ⟨2490560, by rfl⟩ : syracuseStep 3320747 = 4981121) B4981121
theorem B2213831 : Blo 2213435 2213831 := bstep (se 1 (by rfl) ⟨1660373, by rfl⟩ : syracuseStep 2213831 = 3320747) B3320747
theorem B2490565 : Blo 2213435 2490565 := bbase (se 4 (by rfl) ⟨233490, by rfl⟩ : syracuseStep 2490565 = 466981) (by norm_num)
theorem B3320753 : Blo 2213435 3320753 := bstep (se 2 (by rfl) ⟨1245282, by rfl⟩ : syracuseStep 3320753 = 2490565) B2490565
theorem B2213835 : Blo 2213435 2213835 := bstep (se 1 (by rfl) ⟨1660376, by rfl⟩ : syracuseStep 2213835 = 3320753) B3320753
theorem B4202837 : Blo 2213435 4202837 := bbase (se 10 (by rfl) ⟨6156, by rfl⟩ : syracuseStep 4202837 = 12313) (by norm_num)
theorem B2801891 : Blo 2213435 2801891 := bstep (se 1 (by rfl) ⟨2101418, by rfl⟩ : syracuseStep 2801891 = 4202837) B4202837
theorem B7471709 : Blo 2213435 7471709 := bstep (se 3 (by rfl) ⟨1400945, by rfl⟩ : syracuseStep 7471709 = 2801891) B2801891
theorem B4981139 : Blo 2213435 4981139 := bstep (se 1 (by rfl) ⟨3735854, by rfl⟩ : syracuseStep 4981139 = 7471709) B7471709
theorem B3320759 : Blo 2213435 3320759 := bstep (se 1 (by rfl) ⟨2490569, by rfl⟩ : syracuseStep 3320759 = 4981139) B4981139
theorem B2213839 : Blo 2213435 2213839 := bstep (se 1 (by rfl) ⟨1660379, by rfl⟩ : syracuseStep 2213839 = 3320759) B3320759
theorem B3320765 : Blo 2213435 3320765 := bbase (se 3 (by rfl) ⟨622643, by rfl⟩ : syracuseStep 3320765 = 1245287) (by norm_num)
theorem B2213843 : Blo 2213435 2213843 := bstep (se 1 (by rfl) ⟨1660382, by rfl⟩ : syracuseStep 2213843 = 3320765) B3320765
theorem B4981157 : Blo 2213435 4981157 := bbase (se 4 (by rfl) ⟨466983, by rfl⟩ : syracuseStep 4981157 = 933967) (by norm_num)
theorem B3320771 : Blo 2213435 3320771 := bstep (se 1 (by rfl) ⟨2490578, by rfl⟩ : syracuseStep 3320771 = 4981157) B4981157
theorem B2213847 : Blo 2213435 2213847 := bstep (se 1 (by rfl) ⟨1660385, by rfl⟩ : syracuseStep 2213847 = 3320771) B3320771
theorem B5603813 : Blo 2213435 5603813 := bbase (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) (by norm_num)
theorem B3735875 : Blo 2213435 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B2490583 : Blo 2213435 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B3320777 : Blo 2213435 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B2213851 : Blo 2213435 2213851 := bstep (se 1 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 2213851 = 3320777) B3320777
theorem B2364113 : Blo 2213435 2364113 := bbase (se 2 (by rfl) ⟨886542, by rfl⟩ : syracuseStep 2364113 = 1773085) (by norm_num)
theorem B6304301 : Blo 2213435 6304301 := bstep (se 3 (by rfl) ⟨1182056, by rfl⟩ : syracuseStep 6304301 = 2364113) B2364113
theorem B4202867 : Blo 2213435 4202867 := bstep (se 1 (by rfl) ⟨3152150, by rfl⟩ : syracuseStep 4202867 = 6304301) B6304301
theorem B11207645 : Blo 2213435 11207645 := bstep (se 3 (by rfl) ⟨2101433, by rfl⟩ : syracuseStep 11207645 = 4202867) B4202867
theorem B7471763 : Blo 2213435 7471763 := bstep (se 1 (by rfl) ⟨5603822, by rfl⟩ : syracuseStep 7471763 = 11207645) B11207645
theorem B4981175 : Blo 2213435 4981175 := bstep (se 1 (by rfl) ⟨3735881, by rfl⟩ : syracuseStep 4981175 = 7471763) B7471763
theorem B3320783 : Blo 2213435 3320783 := bstep (se 1 (by rfl) ⟨2490587, by rfl⟩ : syracuseStep 3320783 = 4981175) B4981175
theorem B2213855 : Blo 2213435 2213855 := bstep (se 1 (by rfl) ⟨1660391, by rfl⟩ : syracuseStep 2213855 = 3320783) B3320783
theorem B3320789 : Blo 2213435 3320789 := bbase (se 7 (by rfl) ⟨38915, by rfl⟩ : syracuseStep 3320789 = 77831) (by norm_num)
theorem B2213859 : Blo 2213435 2213859 := bstep (se 1 (by rfl) ⟨1660394, by rfl⟩ : syracuseStep 2213859 = 3320789) B3320789
theorem B8405765 : Blo 2213435 8405765 := bbase (se 4 (by rfl) ⟨788040, by rfl⟩ : syracuseStep 8405765 = 1576081) (by norm_num)
theorem B5603843 : Blo 2213435 5603843 := bstep (se 1 (by rfl) ⟨4202882, by rfl⟩ : syracuseStep 5603843 = 8405765) B8405765
theorem B3735895 : Blo 2213435 3735895 := bstep (se 1 (by rfl) ⟨2801921, by rfl⟩ : syracuseStep 3735895 = 5603843) B5603843
theorem B4981193 : Blo 2213435 4981193 := bstep (se 2 (by rfl) ⟨1867947, by rfl⟩ : syracuseStep 4981193 = 3735895) B3735895
theorem B3320795 : Blo 2213435 3320795 := bstep (se 1 (by rfl) ⟨2490596, by rfl⟩ : syracuseStep 3320795 = 4981193) B4981193
theorem B2213863 : Blo 2213435 2213863 := bstep (se 1 (by rfl) ⟨1660397, by rfl⟩ : syracuseStep 2213863 = 3320795) B3320795
theorem B2490601 : Blo 2213435 2490601 := bbase (se 2 (by rfl) ⟨933975, by rfl⟩ : syracuseStep 2490601 = 1867951) (by norm_num)
theorem B3320801 : Blo 2213435 3320801 := bstep (se 2 (by rfl) ⟨1245300, by rfl⟩ : syracuseStep 3320801 = 2490601) B2490601
theorem B2213867 : Blo 2213435 2213867 := bstep (se 1 (by rfl) ⟨1660400, by rfl⟩ : syracuseStep 2213867 = 3320801) B3320801
theorem B12608693 : Blo 2213435 12608693 := bbase (se 5 (by rfl) ⟨591032, by rfl⟩ : syracuseStep 12608693 = 1182065) (by norm_num)
theorem B8405795 : Blo 2213435 8405795 := bstep (se 1 (by rfl) ⟨6304346, by rfl⟩ : syracuseStep 8405795 = 12608693) B12608693
theorem B5603863 : Blo 2213435 5603863 := bstep (se 1 (by rfl) ⟨4202897, by rfl⟩ : syracuseStep 5603863 = 8405795) B8405795
theorem B7471817 : Blo 2213435 7471817 := bstep (se 2 (by rfl) ⟨2801931, by rfl⟩ : syracuseStep 7471817 = 5603863) B5603863
theorem B4981211 : Blo 2213435 4981211 := bstep (se 1 (by rfl) ⟨3735908, by rfl⟩ : syracuseStep 4981211 = 7471817) B7471817
theorem B3320807 : Blo 2213435 3320807 := bstep (se 1 (by rfl) ⟨2490605, by rfl⟩ : syracuseStep 3320807 = 4981211) B4981211
theorem B2213871 : Blo 2213435 2213871 := bstep (se 1 (by rfl) ⟨1660403, by rfl⟩ : syracuseStep 2213871 = 3320807) B3320807
theorem B3320813 : Blo 2213435 3320813 := bbase (se 3 (by rfl) ⟨622652, by rfl⟩ : syracuseStep 3320813 = 1245305) (by norm_num)
theorem B2213875 : Blo 2213435 2213875 := bstep (se 1 (by rfl) ⟨1660406, by rfl⟩ : syracuseStep 2213875 = 3320813) B3320813
theorem B4981229 : Blo 2213435 4981229 := bbase (se 3 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 4981229 = 1867961) (by norm_num)
theorem B3320819 : Blo 2213435 3320819 := bstep (se 1 (by rfl) ⟨2490614, by rfl⟩ : syracuseStep 3320819 = 4981229) B4981229
theorem B2213879 : Blo 2213435 2213879 := bstep (se 1 (by rfl) ⟨1660409, by rfl⟩ : syracuseStep 2213879 = 3320819) B3320819
theorem B5615621 : Blo 2213435 5615621 := bbase (se 4 (by rfl) ⟨526464, by rfl⟩ : syracuseStep 5615621 = 1052929) (by norm_num)
theorem B3743747 : Blo 2213435 3743747 := bstep (se 1 (by rfl) ⟨2807810, by rfl⟩ : syracuseStep 3743747 = 5615621) B5615621
theorem B2495831 : Blo 2213435 2495831 := bstep (se 1 (by rfl) ⟨1871873, by rfl⟩ : syracuseStep 2495831 = 3743747) B3743747
theorem B6655549 : Blo 2213435 6655549 := bstep (se 3 (by rfl) ⟨1247915, by rfl⟩ : syracuseStep 6655549 = 2495831) B2495831
theorem B8874065 : Blo 2213435 8874065 := bstep (se 2 (by rfl) ⟨3327774, by rfl⟩ : syracuseStep 8874065 = 6655549) B6655549
theorem B5916043 : Blo 2213435 5916043 := bstep (se 1 (by rfl) ⟨4437032, by rfl⟩ : syracuseStep 5916043 = 8874065) B8874065
theorem B31552229 : Blo 2213435 31552229 := bstep (se 4 (by rfl) ⟨2958021, by rfl⟩ : syracuseStep 31552229 = 5916043) B5916043
theorem B21034819 : Blo 2213435 21034819 := bstep (se 1 (by rfl) ⟨15776114, by rfl⟩ : syracuseStep 21034819 = 31552229) B31552229
theorem B28046425 : Blo 2213435 28046425 := bstep (se 2 (by rfl) ⟨10517409, by rfl⟩ : syracuseStep 28046425 = 21034819) B21034819
theorem B37395233 : Blo 2213435 37395233 := bstep (se 2 (by rfl) ⟨14023212, by rfl⟩ : syracuseStep 37395233 = 28046425) B28046425
theorem B24930155 : Blo 2213435 24930155 := bstep (se 1 (by rfl) ⟨18697616, by rfl⟩ : syracuseStep 24930155 = 37395233) B37395233
theorem B16620103 : Blo 2213435 16620103 := bstep (se 1 (by rfl) ⟨12465077, by rfl⟩ : syracuseStep 16620103 = 24930155) B24930155
theorem B22160137 : Blo 2213435 22160137 := bstep (se 2 (by rfl) ⟨8310051, by rfl⟩ : syracuseStep 22160137 = 16620103) B16620103
theorem B29546849 : Blo 2213435 29546849 := bstep (se 2 (by rfl) ⟨11080068, by rfl⟩ : syracuseStep 29546849 = 22160137) B22160137
theorem B19697899 : Blo 2213435 19697899 := bstep (se 1 (by rfl) ⟨14773424, by rfl⟩ : syracuseStep 19697899 = 29546849) B29546849
theorem B26263865 : Blo 2213435 26263865 := bstep (se 2 (by rfl) ⟨9848949, by rfl⟩ : syracuseStep 26263865 = 19697899) B19697899
theorem B17509243 : Blo 2213435 17509243 := bstep (se 1 (by rfl) ⟨13131932, by rfl⟩ : syracuseStep 17509243 = 26263865) B26263865
theorem B23345657 : Blo 2213435 23345657 := bstep (se 2 (by rfl) ⟨8754621, by rfl⟩ : syracuseStep 23345657 = 17509243) B17509243
theorem B15563771 : Blo 2213435 15563771 := bstep (se 1 (by rfl) ⟨11672828, by rfl⟩ : syracuseStep 15563771 = 23345657) B23345657
theorem B10375847 : Blo 2213435 10375847 := bstep (se 1 (by rfl) ⟨7781885, by rfl⟩ : syracuseStep 10375847 = 15563771) B15563771
theorem B6917231 : Blo 2213435 6917231 := bstep (se 1 (by rfl) ⟨5187923, by rfl⟩ : syracuseStep 6917231 = 10375847) B10375847
theorem B4611487 : Blo 2213435 4611487 := bstep (se 1 (by rfl) ⟨3458615, by rfl⟩ : syracuseStep 4611487 = 6917231) B6917231
theorem B6148649 : Blo 2213435 6148649 := bstep (se 2 (by rfl) ⟨2305743, by rfl⟩ : syracuseStep 6148649 = 4611487) B4611487
theorem B4099099 : Blo 2213435 4099099 := bstep (se 1 (by rfl) ⟨3074324, by rfl⟩ : syracuseStep 4099099 = 6148649) B6148649
theorem B5465465 : Blo 2213435 5465465 := bstep (se 2 (by rfl) ⟨2049549, by rfl⟩ : syracuseStep 5465465 = 4099099) B4099099
theorem B3643643 : Blo 2213435 3643643 := bstep (se 1 (by rfl) ⟨2732732, by rfl⟩ : syracuseStep 3643643 = 5465465) B5465465
theorem B9716381 : Blo 2213435 9716381 := bstep (se 3 (by rfl) ⟨1821821, by rfl⟩ : syracuseStep 9716381 = 3643643) B3643643
theorem B6477587 : Blo 2213435 6477587 := bstep (se 1 (by rfl) ⟨4858190, by rfl⟩ : syracuseStep 6477587 = 9716381) B9716381
theorem B4318391 : Blo 2213435 4318391 := bstep (se 1 (by rfl) ⟨3238793, by rfl⟩ : syracuseStep 4318391 = 6477587) B6477587
theorem B11515709 : Blo 2213435 11515709 := bstep (se 3 (by rfl) ⟨2159195, by rfl⟩ : syracuseStep 11515709 = 4318391) B4318391
theorem B30708557 : Blo 2213435 30708557 := bstep (se 3 (by rfl) ⟨5757854, by rfl⟩ : syracuseStep 30708557 = 11515709) B11515709
theorem B20472371 : Blo 2213435 20472371 := bstep (se 1 (by rfl) ⟨15354278, by rfl⟩ : syracuseStep 20472371 = 30708557) B30708557
theorem B13648247 : Blo 2213435 13648247 := bstep (se 1 (by rfl) ⟨10236185, by rfl⟩ : syracuseStep 13648247 = 20472371) B20472371
theorem B9098831 : Blo 2213435 9098831 := bstep (se 1 (by rfl) ⟨6824123, by rfl⟩ : syracuseStep 9098831 = 13648247) B13648247
theorem B6065887 : Blo 2213435 6065887 := bstep (se 1 (by rfl) ⟨4549415, by rfl⟩ : syracuseStep 6065887 = 9098831) B9098831
theorem B8087849 : Blo 2213435 8087849 := bstep (se 2 (by rfl) ⟨3032943, by rfl⟩ : syracuseStep 8087849 = 6065887) B6065887
theorem B5391899 : Blo 2213435 5391899 := bstep (se 1 (by rfl) ⟨4043924, by rfl⟩ : syracuseStep 5391899 = 8087849) B8087849
theorem B3594599 : Blo 2213435 3594599 := bstep (se 1 (by rfl) ⟨2695949, by rfl⟩ : syracuseStep 3594599 = 5391899) B5391899
theorem B2396399 : Blo 2213435 2396399 := bstep (se 1 (by rfl) ⟨1797299, by rfl⟩ : syracuseStep 2396399 = 3594599) B3594599
theorem B6390397 : Blo 2213435 6390397 := bstep (se 3 (by rfl) ⟨1198199, by rfl⟩ : syracuseStep 6390397 = 2396399) B2396399
theorem B34082117 : Blo 2213435 34082117 := bstep (se 4 (by rfl) ⟨3195198, by rfl⟩ : syracuseStep 34082117 = 6390397) B6390397
theorem B22721411 : Blo 2213435 22721411 := bstep (se 1 (by rfl) ⟨17041058, by rfl⟩ : syracuseStep 22721411 = 34082117) B34082117
theorem B15147607 : Blo 2213435 15147607 := bstep (se 1 (by rfl) ⟨11360705, by rfl⟩ : syracuseStep 15147607 = 22721411) B22721411
theorem B20196809 : Blo 2213435 20196809 := bstep (se 2 (by rfl) ⟨7573803, by rfl⟩ : syracuseStep 20196809 = 15147607) B15147607
theorem B13464539 : Blo 2213435 13464539 := bstep (se 1 (by rfl) ⟨10098404, by rfl⟩ : syracuseStep 13464539 = 20196809) B20196809
theorem B8976359 : Blo 2213435 8976359 := bstep (se 1 (by rfl) ⟨6732269, by rfl⟩ : syracuseStep 8976359 = 13464539) B13464539
theorem B23936957 : Blo 2213435 23936957 := bstep (se 3 (by rfl) ⟨4488179, by rfl⟩ : syracuseStep 23936957 = 8976359) B8976359
theorem B15957971 : Blo 2213435 15957971 := bstep (se 1 (by rfl) ⟨11968478, by rfl⟩ : syracuseStep 15957971 = 23936957) B23936957
theorem B10638647 : Blo 2213435 10638647 := bstep (se 1 (by rfl) ⟨7978985, by rfl⟩ : syracuseStep 10638647 = 15957971) B15957971
theorem B7092431 : Blo 2213435 7092431 := bstep (se 1 (by rfl) ⟨5319323, by rfl⟩ : syracuseStep 7092431 = 10638647) B10638647
theorem B4728287 : Blo 2213435 4728287 := bstep (se 1 (by rfl) ⟨3546215, by rfl⟩ : syracuseStep 4728287 = 7092431) B7092431
theorem B3152191 : Blo 2213435 3152191 := bstep (se 1 (by rfl) ⟨2364143, by rfl⟩ : syracuseStep 3152191 = 4728287) B4728287
theorem B4202921 : Blo 2213435 4202921 := bstep (se 2 (by rfl) ⟨1576095, by rfl⟩ : syracuseStep 4202921 = 3152191) B3152191
theorem B2801947 : Blo 2213435 2801947 := bstep (se 1 (by rfl) ⟨2101460, by rfl⟩ : syracuseStep 2801947 = 4202921) B4202921
theorem B3735929 : Blo 2213435 3735929 := bstep (se 2 (by rfl) ⟨1400973, by rfl⟩ : syracuseStep 3735929 = 2801947) B2801947
theorem B2490619 : Blo 2213435 2490619 := bstep (se 1 (by rfl) ⟨1867964, by rfl⟩ : syracuseStep 2490619 = 3735929) B3735929
theorem B3320825 : Blo 2213435 3320825 := bstep (se 2 (by rfl) ⟨1245309, by rfl⟩ : syracuseStep 3320825 = 2490619) B2490619
theorem B2213883 : Blo 2213435 2213883 := bstep (se 1 (by rfl) ⟨1660412, by rfl⟩ : syracuseStep 2213883 = 3320825) B3320825
theorem B10783813 : Blo 2213435 10783813 := bbase (se 4 (by rfl) ⟨1010982, by rfl⟩ : syracuseStep 10783813 = 2021965) (by norm_num)
theorem B14378417 : Blo 2213435 14378417 := bstep (se 2 (by rfl) ⟨5391906, by rfl⟩ : syracuseStep 14378417 = 10783813) B10783813
theorem B9585611 : Blo 2213435 9585611 := bstep (se 1 (by rfl) ⟨7189208, by rfl⟩ : syracuseStep 9585611 = 14378417) B14378417
theorem B6390407 : Blo 2213435 6390407 := bstep (se 1 (by rfl) ⟨4792805, by rfl⟩ : syracuseStep 6390407 = 9585611) B9585611
theorem B4260271 : Blo 2213435 4260271 := bstep (se 1 (by rfl) ⟨3195203, by rfl⟩ : syracuseStep 4260271 = 6390407) B6390407
theorem B5680361 : Blo 2213435 5680361 := bstep (se 2 (by rfl) ⟨2130135, by rfl⟩ : syracuseStep 5680361 = 4260271) B4260271
theorem B3786907 : Blo 2213435 3786907 := bstep (se 1 (by rfl) ⟨2840180, by rfl⟩ : syracuseStep 3786907 = 5680361) B5680361
theorem B5049209 : Blo 2213435 5049209 := bstep (se 2 (by rfl) ⟨1893453, by rfl⟩ : syracuseStep 5049209 = 3786907) B3786907
theorem B3366139 : Blo 2213435 3366139 := bstep (se 1 (by rfl) ⟨2524604, by rfl⟩ : syracuseStep 3366139 = 5049209) B5049209
theorem B71810965 : Blo 2213435 71810965 := bstep (se 6 (by rfl) ⟨1683069, by rfl⟩ : syracuseStep 71810965 = 3366139) B3366139
theorem B95747953 : Blo 2213435 95747953 := bstep (se 2 (by rfl) ⟨35905482, by rfl⟩ : syracuseStep 95747953 = 71810965) B71810965
theorem B127663937 : Blo 2213435 127663937 := bstep (se 2 (by rfl) ⟨47873976, by rfl⟩ : syracuseStep 127663937 = 95747953) B95747953
theorem B85109291 : Blo 2213435 85109291 := bstep (se 1 (by rfl) ⟨63831968, by rfl⟩ : syracuseStep 85109291 = 127663937) B127663937
theorem B56739527 : Blo 2213435 56739527 := bstep (se 1 (by rfl) ⟨42554645, by rfl⟩ : syracuseStep 56739527 = 85109291) B85109291
theorem B37826351 : Blo 2213435 37826351 := bstep (se 1 (by rfl) ⟨28369763, by rfl⟩ : syracuseStep 37826351 = 56739527) B56739527
theorem B25217567 : Blo 2213435 25217567 := bstep (se 1 (by rfl) ⟨18913175, by rfl⟩ : syracuseStep 25217567 = 37826351) B37826351
theorem B16811711 : Blo 2213435 16811711 := bstep (se 1 (by rfl) ⟨12608783, by rfl⟩ : syracuseStep 16811711 = 25217567) B25217567
theorem B11207807 : Blo 2213435 11207807 := bstep (se 1 (by rfl) ⟨8405855, by rfl⟩ : syracuseStep 11207807 = 16811711) B16811711
theorem B7471871 : Blo 2213435 7471871 := bstep (se 1 (by rfl) ⟨5603903, by rfl⟩ : syracuseStep 7471871 = 11207807) B11207807
theorem B4981247 : Blo 2213435 4981247 := bstep (se 1 (by rfl) ⟨3735935, by rfl⟩ : syracuseStep 4981247 = 7471871) B7471871
theorem B3320831 : Blo 2213435 3320831 := bstep (se 1 (by rfl) ⟨2490623, by rfl⟩ : syracuseStep 3320831 = 4981247) B4981247
theorem B2213887 : Blo 2213435 2213887 := bstep (se 1 (by rfl) ⟨1660415, by rfl⟩ : syracuseStep 2213887 = 3320831) B3320831
theorem B3320837 : Blo 2213435 3320837 := bbase (se 4 (by rfl) ⟨311328, by rfl⟩ : syracuseStep 3320837 = 622657) (by norm_num)
theorem B2213891 : Blo 2213435 2213891 := bstep (se 1 (by rfl) ⟨1660418, by rfl⟩ : syracuseStep 2213891 = 3320837) B3320837
theorem B3735949 : Blo 2213435 3735949 := bbase (se 3 (by rfl) ⟨700490, by rfl⟩ : syracuseStep 3735949 = 1400981) (by norm_num)
theorem B4981265 : Blo 2213435 4981265 := bstep (se 2 (by rfl) ⟨1867974, by rfl⟩ : syracuseStep 4981265 = 3735949) B3735949
theorem B3320843 : Blo 2213435 3320843 := bstep (se 1 (by rfl) ⟨2490632, by rfl⟩ : syracuseStep 3320843 = 4981265) B4981265
theorem B2213895 : Blo 2213435 2213895 := bstep (se 1 (by rfl) ⟨1660421, by rfl⟩ : syracuseStep 2213895 = 3320843) B3320843
theorem B2490637 : Blo 2213435 2490637 := bbase (se 3 (by rfl) ⟨466994, by rfl⟩ : syracuseStep 2490637 = 933989) (by norm_num)
theorem B3320849 : Blo 2213435 3320849 := bstep (se 2 (by rfl) ⟨1245318, by rfl⟩ : syracuseStep 3320849 = 2490637) B2490637
theorem B2213899 : Blo 2213435 2213899 := bstep (se 1 (by rfl) ⟨1660424, by rfl⟩ : syracuseStep 2213899 = 3320849) B3320849
theorem B7471925 : Blo 2213435 7471925 := bbase (se 5 (by rfl) ⟨350246, by rfl⟩ : syracuseStep 7471925 = 700493) (by norm_num)
theorem B4981283 : Blo 2213435 4981283 := bstep (se 1 (by rfl) ⟨3735962, by rfl⟩ : syracuseStep 4981283 = 7471925) B7471925
theorem B3320855 : Blo 2213435 3320855 := bstep (se 1 (by rfl) ⟨2490641, by rfl⟩ : syracuseStep 3320855 = 4981283) B4981283
theorem B2213903 : Blo 2213435 2213903 := bstep (se 1 (by rfl) ⟨1660427, by rfl⟩ : syracuseStep 2213903 = 3320855) B3320855
theorem B3320861 : Blo 2213435 3320861 := bbase (se 3 (by rfl) ⟨622661, by rfl⟩ : syracuseStep 3320861 = 1245323) (by norm_num)
theorem B2213907 : Blo 2213435 2213907 := bstep (se 1 (by rfl) ⟨1660430, by rfl⟩ : syracuseStep 2213907 = 3320861) B3320861
theorem B4981301 : Blo 2213435 4981301 := bbase (se 5 (by rfl) ⟨233498, by rfl⟩ : syracuseStep 4981301 = 466997) (by norm_num)
theorem B3320867 : Blo 2213435 3320867 := bstep (se 1 (by rfl) ⟨2490650, by rfl⟩ : syracuseStep 3320867 = 4981301) B4981301
theorem B2213911 : Blo 2213435 2213911 := bstep (se 1 (by rfl) ⟨1660433, by rfl⟩ : syracuseStep 2213911 = 3320867) B3320867
theorem B9456709 : Blo 2213435 9456709 := bbase (se 4 (by rfl) ⟨886566, by rfl⟩ : syracuseStep 9456709 = 1773133) (by norm_num)
theorem B12608945 : Blo 2213435 12608945 := bstep (se 2 (by rfl) ⟨4728354, by rfl⟩ : syracuseStep 12608945 = 9456709) B9456709
theorem B8405963 : Blo 2213435 8405963 := bstep (se 1 (by rfl) ⟨6304472, by rfl⟩ : syracuseStep 8405963 = 12608945) B12608945
theorem B5603975 : Blo 2213435 5603975 := bstep (se 1 (by rfl) ⟨4202981, by rfl⟩ : syracuseStep 5603975 = 8405963) B8405963
theorem B3735983 : Blo 2213435 3735983 := bstep (se 1 (by rfl) ⟨2801987, by rfl⟩ : syracuseStep 3735983 = 5603975) B5603975
theorem B2490655 : Blo 2213435 2490655 := bstep (se 1 (by rfl) ⟨1867991, by rfl⟩ : syracuseStep 2490655 = 3735983) B3735983
theorem B3320873 : Blo 2213435 3320873 := bstep (se 2 (by rfl) ⟨1245327, by rfl⟩ : syracuseStep 3320873 = 2490655) B2490655
theorem B2213915 : Blo 2213435 2213915 := bstep (se 1 (by rfl) ⟨1660436, by rfl⟩ : syracuseStep 2213915 = 3320873) B3320873
theorem B9456725 : Blo 2213435 9456725 := bbase (se 8 (by rfl) ⟨55410, by rfl⟩ : syracuseStep 9456725 = 110821) (by norm_num)
theorem B6304483 : Blo 2213435 6304483 := bstep (se 1 (by rfl) ⟨4728362, by rfl⟩ : syracuseStep 6304483 = 9456725) B9456725
theorem B8405977 : Blo 2213435 8405977 := bstep (se 2 (by rfl) ⟨3152241, by rfl⟩ : syracuseStep 8405977 = 6304483) B6304483
theorem B11207969 : Blo 2213435 11207969 := bstep (se 2 (by rfl) ⟨4202988, by rfl⟩ : syracuseStep 11207969 = 8405977) B8405977
theorem B7471979 : Blo 2213435 7471979 := bstep (se 1 (by rfl) ⟨5603984, by rfl⟩ : syracuseStep 7471979 = 11207969) B11207969
theorem B4981319 : Blo 2213435 4981319 := bstep (se 1 (by rfl) ⟨3735989, by rfl⟩ : syracuseStep 4981319 = 7471979) B7471979
theorem B3320879 : Blo 2213435 3320879 := bstep (se 1 (by rfl) ⟨2490659, by rfl⟩ : syracuseStep 3320879 = 4981319) B4981319
theorem B2213919 : Blo 2213435 2213919 := bstep (se 1 (by rfl) ⟨1660439, by rfl⟩ : syracuseStep 2213919 = 3320879) B3320879
theorem B3320885 : Blo 2213435 3320885 := bbase (se 5 (by rfl) ⟨155666, by rfl⟩ : syracuseStep 3320885 = 311333) (by norm_num)
theorem B2213923 : Blo 2213435 2213923 := bstep (se 1 (by rfl) ⟨1660442, by rfl⟩ : syracuseStep 2213923 = 3320885) B3320885
theorem B5604005 : Blo 2213435 5604005 := bbase (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) (by norm_num)
theorem B3736003 : Blo 2213435 3736003 := bstep (se 1 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 3736003 = 5604005) B5604005
theorem B4981337 : Blo 2213435 4981337 := bstep (se 2 (by rfl) ⟨1868001, by rfl⟩ : syracuseStep 4981337 = 3736003) B3736003
theorem B3320891 : Blo 2213435 3320891 := bstep (se 1 (by rfl) ⟨2490668, by rfl⟩ : syracuseStep 3320891 = 4981337) B4981337
theorem B2213927 : Blo 2213435 2213927 := bstep (se 1 (by rfl) ⟨1660445, by rfl⟩ : syracuseStep 2213927 = 3320891) B3320891
theorem B2490673 : Blo 2213435 2490673 := bbase (se 2 (by rfl) ⟨934002, by rfl⟩ : syracuseStep 2490673 = 1868005) (by norm_num)
theorem B3320897 : Blo 2213435 3320897 := bstep (se 2 (by rfl) ⟨1245336, by rfl⟩ : syracuseStep 3320897 = 2490673) B2490673
theorem B2213931 : Blo 2213435 2213931 := bstep (se 1 (by rfl) ⟨1660448, by rfl⟩ : syracuseStep 2213931 = 3320897) B3320897
theorem B4728397 : Blo 2213435 4728397 := bbase (se 3 (by rfl) ⟨886574, by rfl⟩ : syracuseStep 4728397 = 1773149) (by norm_num)
theorem B6304529 : Blo 2213435 6304529 := bstep (se 2 (by rfl) ⟨2364198, by rfl⟩ : syracuseStep 6304529 = 4728397) B4728397
theorem B4203019 : Blo 2213435 4203019 := bstep (se 1 (by rfl) ⟨3152264, by rfl⟩ : syracuseStep 4203019 = 6304529) B6304529
theorem B5604025 : Blo 2213435 5604025 := bstep (se 2 (by rfl) ⟨2101509, by rfl⟩ : syracuseStep 5604025 = 4203019) B4203019
theorem B7472033 : Blo 2213435 7472033 := bstep (se 2 (by rfl) ⟨2802012, by rfl⟩ : syracuseStep 7472033 = 5604025) B5604025
theorem B4981355 : Blo 2213435 4981355 := bstep (se 1 (by rfl) ⟨3736016, by rfl⟩ : syracuseStep 4981355 = 7472033) B7472033
theorem B3320903 : Blo 2213435 3320903 := bstep (se 1 (by rfl) ⟨2490677, by rfl⟩ : syracuseStep 3320903 = 4981355) B4981355
theorem B2213935 : Blo 2213435 2213935 := bstep (se 1 (by rfl) ⟨1660451, by rfl⟩ : syracuseStep 2213935 = 3320903) B3320903
theorem B3320909 : Blo 2213435 3320909 := bbase (se 3 (by rfl) ⟨622670, by rfl⟩ : syracuseStep 3320909 = 1245341) (by norm_num)
theorem B2213939 : Blo 2213435 2213939 := bstep (se 1 (by rfl) ⟨1660454, by rfl⟩ : syracuseStep 2213939 = 3320909) B3320909
theorem B4981373 : Blo 2213435 4981373 := bbase (se 3 (by rfl) ⟨934007, by rfl⟩ : syracuseStep 4981373 = 1868015) (by norm_num)
theorem B3320915 : Blo 2213435 3320915 := bstep (se 1 (by rfl) ⟨2490686, by rfl⟩ : syracuseStep 3320915 = 4981373) B4981373
theorem B2213943 : Blo 2213435 2213943 := bstep (se 1 (by rfl) ⟨1660457, by rfl⟩ : syracuseStep 2213943 = 3320915) B3320915
theorem B3736037 : Blo 2213435 3736037 := bbase (se 4 (by rfl) ⟨350253, by rfl⟩ : syracuseStep 3736037 = 700507) (by norm_num)
theorem B2490691 : Blo 2213435 2490691 := bstep (se 1 (by rfl) ⟨1868018, by rfl⟩ : syracuseStep 2490691 = 3736037) B3736037
theorem B3320921 : Blo 2213435 3320921 := bstep (se 2 (by rfl) ⟨1245345, by rfl⟩ : syracuseStep 3320921 = 2490691) B2490691
theorem B2213947 : Blo 2213435 2213947 := bstep (se 1 (by rfl) ⟨1660460, by rfl⟩ : syracuseStep 2213947 = 3320921) B3320921
theorem B13464949 : Blo 2213435 13464949 := bbase (se 5 (by rfl) ⟨631169, by rfl⟩ : syracuseStep 13464949 = 1262339) (by norm_num)
theorem B17953265 : Blo 2213435 17953265 := bstep (se 2 (by rfl) ⟨6732474, by rfl⟩ : syracuseStep 17953265 = 13464949) B13464949
theorem B11968843 : Blo 2213435 11968843 := bstep (se 1 (by rfl) ⟨8976632, by rfl⟩ : syracuseStep 11968843 = 17953265) B17953265
theorem B15958457 : Blo 2213435 15958457 := bstep (se 2 (by rfl) ⟨5984421, by rfl⟩ : syracuseStep 15958457 = 11968843) B11968843
theorem B10638971 : Blo 2213435 10638971 := bstep (se 1 (by rfl) ⟨7979228, by rfl⟩ : syracuseStep 10638971 = 15958457) B15958457
theorem B7092647 : Blo 2213435 7092647 := bstep (se 1 (by rfl) ⟨5319485, by rfl⟩ : syracuseStep 7092647 = 10638971) B10638971
theorem B4728431 : Blo 2213435 4728431 := bstep (se 1 (by rfl) ⟨3546323, by rfl⟩ : syracuseStep 4728431 = 7092647) B7092647
theorem B3152287 : Blo 2213435 3152287 := bstep (se 1 (by rfl) ⟨2364215, by rfl⟩ : syracuseStep 3152287 = 4728431) B4728431
theorem B16812197 : Blo 2213435 16812197 := bstep (se 4 (by rfl) ⟨1576143, by rfl⟩ : syracuseStep 16812197 = 3152287) B3152287
theorem B11208131 : Blo 2213435 11208131 := bstep (se 1 (by rfl) ⟨8406098, by rfl⟩ : syracuseStep 11208131 = 16812197) B16812197
theorem B7472087 : Blo 2213435 7472087 := bstep (se 1 (by rfl) ⟨5604065, by rfl⟩ : syracuseStep 7472087 = 11208131) B11208131
theorem B4981391 : Blo 2213435 4981391 := bstep (se 1 (by rfl) ⟨3736043, by rfl⟩ : syracuseStep 4981391 = 7472087) B7472087
theorem B3320927 : Blo 2213435 3320927 := bstep (se 1 (by rfl) ⟨2490695, by rfl⟩ : syracuseStep 3320927 = 4981391) B4981391
theorem B2213951 : Blo 2213435 2213951 := bstep (se 1 (by rfl) ⟨1660463, by rfl⟩ : syracuseStep 2213951 = 3320927) B3320927
theorem B3320933 : Blo 2213435 3320933 := bbase (se 4 (by rfl) ⟨311337, by rfl⟩ : syracuseStep 3320933 = 622675) (by norm_num)
theorem B2213955 : Blo 2213435 2213955 := bstep (se 1 (by rfl) ⟨1660466, by rfl⟩ : syracuseStep 2213955 = 3320933) B3320933
theorem B2659753 : Blo 2213435 2659753 := bbase (se 2 (by rfl) ⟨997407, by rfl⟩ : syracuseStep 2659753 = 1994815) (by norm_num)
theorem B3546337 : Blo 2213435 3546337 := bstep (se 2 (by rfl) ⟨1329876, by rfl⟩ : syracuseStep 3546337 = 2659753) B2659753
theorem B4728449 : Blo 2213435 4728449 := bstep (se 2 (by rfl) ⟨1773168, by rfl⟩ : syracuseStep 4728449 = 3546337) B3546337
theorem B3152299 : Blo 2213435 3152299 := bstep (se 1 (by rfl) ⟨2364224, by rfl⟩ : syracuseStep 3152299 = 4728449) B4728449
theorem B4203065 : Blo 2213435 4203065 := bstep (se 2 (by rfl) ⟨1576149, by rfl⟩ : syracuseStep 4203065 = 3152299) B3152299
theorem B2802043 : Blo 2213435 2802043 := bstep (se 1 (by rfl) ⟨2101532, by rfl⟩ : syracuseStep 2802043 = 4203065) B4203065
theorem B3736057 : Blo 2213435 3736057 := bstep (se 2 (by rfl) ⟨1401021, by rfl⟩ : syracuseStep 3736057 = 2802043) B2802043
theorem B4981409 : Blo 2213435 4981409 := bstep (se 2 (by rfl) ⟨1868028, by rfl⟩ : syracuseStep 4981409 = 3736057) B3736057
theorem B3320939 : Blo 2213435 3320939 := bstep (se 1 (by rfl) ⟨2490704, by rfl⟩ : syracuseStep 3320939 = 4981409) B4981409
theorem B2213959 : Blo 2213435 2213959 := bstep (se 1 (by rfl) ⟨1660469, by rfl⟩ : syracuseStep 2213959 = 3320939) B3320939
theorem B2490709 : Blo 2213435 2490709 := bbase (se 10 (by rfl) ⟨3648, by rfl⟩ : syracuseStep 2490709 = 7297) (by norm_num)
theorem B3320945 : Blo 2213435 3320945 := bstep (se 2 (by rfl) ⟨1245354, by rfl⟩ : syracuseStep 3320945 = 2490709) B2490709
theorem B2213963 : Blo 2213435 2213963 := bstep (se 1 (by rfl) ⟨1660472, by rfl⟩ : syracuseStep 2213963 = 3320945) B3320945
theorem B2802053 : Blo 2213435 2802053 := bbase (se 4 (by rfl) ⟨262692, by rfl⟩ : syracuseStep 2802053 = 525385) (by norm_num)
theorem B7472141 : Blo 2213435 7472141 := bstep (se 3 (by rfl) ⟨1401026, by rfl⟩ : syracuseStep 7472141 = 2802053) B2802053
theorem B4981427 : Blo 2213435 4981427 := bstep (se 1 (by rfl) ⟨3736070, by rfl⟩ : syracuseStep 4981427 = 7472141) B7472141
theorem B3320951 : Blo 2213435 3320951 := bstep (se 1 (by rfl) ⟨2490713, by rfl⟩ : syracuseStep 3320951 = 4981427) B4981427
theorem B2213967 : Blo 2213435 2213967 := bstep (se 1 (by rfl) ⟨1660475, by rfl⟩ : syracuseStep 2213967 = 3320951) B3320951
theorem B3320957 : Blo 2213435 3320957 := bbase (se 3 (by rfl) ⟨622679, by rfl⟩ : syracuseStep 3320957 = 1245359) (by norm_num)
theorem B2213971 : Blo 2213435 2213971 := bstep (se 1 (by rfl) ⟨1660478, by rfl⟩ : syracuseStep 2213971 = 3320957) B3320957
theorem B4981445 : Blo 2213435 4981445 := bbase (se 4 (by rfl) ⟨467010, by rfl⟩ : syracuseStep 4981445 = 934021) (by norm_num)
theorem B3320963 : Blo 2213435 3320963 := bstep (se 1 (by rfl) ⟨2490722, by rfl⟩ : syracuseStep 3320963 = 4981445) B4981445
theorem B2213975 : Blo 2213435 2213975 := bstep (se 1 (by rfl) ⟨1660481, by rfl⟩ : syracuseStep 2213975 = 3320963) B3320963
theorem B6390677 : Blo 2213435 6390677 := bbase (se 6 (by rfl) ⟨149781, by rfl⟩ : syracuseStep 6390677 = 299563) (by norm_num)
theorem B4260451 : Blo 2213435 4260451 := bstep (se 1 (by rfl) ⟨3195338, by rfl⟩ : syracuseStep 4260451 = 6390677) B6390677
theorem B5680601 : Blo 2213435 5680601 := bstep (se 2 (by rfl) ⟨2130225, by rfl⟩ : syracuseStep 5680601 = 4260451) B4260451
theorem B3787067 : Blo 2213435 3787067 := bstep (se 1 (by rfl) ⟨2840300, by rfl⟩ : syracuseStep 3787067 = 5680601) B5680601
theorem B2524711 : Blo 2213435 2524711 := bstep (se 1 (by rfl) ⟨1893533, by rfl⟩ : syracuseStep 2524711 = 3787067) B3787067
theorem B3366281 : Blo 2213435 3366281 := bstep (se 2 (by rfl) ⟨1262355, by rfl⟩ : syracuseStep 3366281 = 2524711) B2524711
theorem B2244187 : Blo 2213435 2244187 := bstep (se 1 (by rfl) ⟨1683140, by rfl⟩ : syracuseStep 2244187 = 3366281) B3366281
theorem B2992249 : Blo 2213435 2992249 := bstep (se 2 (by rfl) ⟨1122093, by rfl⟩ : syracuseStep 2992249 = 2244187) B2244187
theorem B3989665 : Blo 2213435 3989665 := bstep (se 2 (by rfl) ⟨1496124, by rfl⟩ : syracuseStep 3989665 = 2992249) B2992249
theorem B21278213 : Blo 2213435 21278213 := bstep (se 4 (by rfl) ⟨1994832, by rfl⟩ : syracuseStep 21278213 = 3989665) B3989665
theorem B14185475 : Blo 2213435 14185475 := bstep (se 1 (by rfl) ⟨10639106, by rfl⟩ : syracuseStep 14185475 = 21278213) B21278213
theorem B9456983 : Blo 2213435 9456983 := bstep (se 1 (by rfl) ⟨7092737, by rfl⟩ : syracuseStep 9456983 = 14185475) B14185475
theorem B6304655 : Blo 2213435 6304655 := bstep (se 1 (by rfl) ⟨4728491, by rfl⟩ : syracuseStep 6304655 = 9456983) B9456983
theorem B4203103 : Blo 2213435 4203103 := bstep (se 1 (by rfl) ⟨3152327, by rfl⟩ : syracuseStep 4203103 = 6304655) B6304655
theorem B5604137 : Blo 2213435 5604137 := bstep (se 2 (by rfl) ⟨2101551, by rfl⟩ : syracuseStep 5604137 = 4203103) B4203103
theorem B3736091 : Blo 2213435 3736091 := bstep (se 1 (by rfl) ⟨2802068, by rfl⟩ : syracuseStep 3736091 = 5604137) B5604137
theorem B2490727 : Blo 2213435 2490727 := bstep (se 1 (by rfl) ⟨1868045, by rfl⟩ : syracuseStep 2490727 = 3736091) B3736091
theorem B3320969 : Blo 2213435 3320969 := bstep (se 2 (by rfl) ⟨1245363, by rfl⟩ : syracuseStep 3320969 = 2490727) B2490727
theorem B2213979 : Blo 2213435 2213979 := bstep (se 1 (by rfl) ⟨1660484, by rfl⟩ : syracuseStep 2213979 = 3320969) B3320969
theorem B11208293 : Blo 2213435 11208293 := bbase (se 4 (by rfl) ⟨1050777, by rfl⟩ : syracuseStep 11208293 = 2101555) (by norm_num)
theorem B7472195 : Blo 2213435 7472195 := bstep (se 1 (by rfl) ⟨5604146, by rfl⟩ : syracuseStep 7472195 = 11208293) B11208293
theorem B4981463 : Blo 2213435 4981463 := bstep (se 1 (by rfl) ⟨3736097, by rfl⟩ : syracuseStep 4981463 = 7472195) B7472195
theorem B3320975 : Blo 2213435 3320975 := bstep (se 1 (by rfl) ⟨2490731, by rfl⟩ : syracuseStep 3320975 = 4981463) B4981463
theorem B2213983 : Blo 2213435 2213983 := bstep (se 1 (by rfl) ⟨1660487, by rfl⟩ : syracuseStep 2213983 = 3320975) B3320975
theorem B3320981 : Blo 2213435 3320981 := bbase (se 6 (by rfl) ⟨77835, by rfl⟩ : syracuseStep 3320981 = 155671) (by norm_num)
theorem B2213987 : Blo 2213435 2213987 := bstep (se 1 (by rfl) ⟨1660490, by rfl⟩ : syracuseStep 2213987 = 3320981) B3320981
theorem B17953589 : Blo 2213435 17953589 := bbase (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) (by norm_num)
theorem B11969059 : Blo 2213435 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B15958745 : Blo 2213435 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B10639163 : Blo 2213435 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B7092775 : Blo 2213435 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B9457033 : Blo 2213435 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B12609377 : Blo 2213435 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B8406251 : Blo 2213435 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B5604167 : Blo 2213435 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B3736111 : Blo 2213435 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B4981481 : Blo 2213435 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B3320987 : Blo 2213435 3320987 := bstep (se 1 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 3320987 = 4981481) B4981481
theorem B2213991 : Blo 2213435 2213991 := bstep (se 1 (by rfl) ⟨1660493, by rfl⟩ : syracuseStep 2213991 = 3320987) B3320987
theorem B2490745 : Blo 2213435 2490745 := bbase (se 2 (by rfl) ⟨934029, by rfl⟩ : syracuseStep 2490745 = 1868059) (by norm_num)
theorem B3320993 : Blo 2213435 3320993 := bstep (se 2 (by rfl) ⟨1245372, by rfl⟩ : syracuseStep 3320993 = 2490745) B2490745
theorem B2213995 : Blo 2213435 2213995 := bstep (se 1 (by rfl) ⟨1660496, by rfl⟩ : syracuseStep 2213995 = 3320993) B3320993
theorem B7189573 : Blo 2213435 7189573 := bbase (se 4 (by rfl) ⟨674022, by rfl⟩ : syracuseStep 7189573 = 1348045) (by norm_num)
theorem B9586097 : Blo 2213435 9586097 := bstep (se 2 (by rfl) ⟨3594786, by rfl⟩ : syracuseStep 9586097 = 7189573) B7189573
theorem B6390731 : Blo 2213435 6390731 := bstep (se 1 (by rfl) ⟨4793048, by rfl⟩ : syracuseStep 6390731 = 9586097) B9586097
theorem B4260487 : Blo 2213435 4260487 := bstep (se 1 (by rfl) ⟨3195365, by rfl⟩ : syracuseStep 4260487 = 6390731) B6390731
theorem B5680649 : Blo 2213435 5680649 := bstep (se 2 (by rfl) ⟨2130243, by rfl⟩ : syracuseStep 5680649 = 4260487) B4260487
theorem B15148397 : Blo 2213435 15148397 := bstep (se 3 (by rfl) ⟨2840324, by rfl⟩ : syracuseStep 15148397 = 5680649) B5680649
theorem B10098931 : Blo 2213435 10098931 := bstep (se 1 (by rfl) ⟨7574198, by rfl⟩ : syracuseStep 10098931 = 15148397) B15148397
theorem B13465241 : Blo 2213435 13465241 := bstep (se 2 (by rfl) ⟨5049465, by rfl⟩ : syracuseStep 13465241 = 10098931) B10098931
theorem B8976827 : Blo 2213435 8976827 := bstep (se 1 (by rfl) ⟨6732620, by rfl⟩ : syracuseStep 8976827 = 13465241) B13465241
theorem B5984551 : Blo 2213435 5984551 := bstep (se 1 (by rfl) ⟨4488413, by rfl⟩ : syracuseStep 5984551 = 8976827) B8976827
theorem B7979401 : Blo 2213435 7979401 := bstep (se 2 (by rfl) ⟨2992275, by rfl⟩ : syracuseStep 7979401 = 5984551) B5984551
theorem B10639201 : Blo 2213435 10639201 := bstep (se 2 (by rfl) ⟨3989700, by rfl⟩ : syracuseStep 10639201 = 7979401) B7979401
theorem B14185601 : Blo 2213435 14185601 := bstep (se 2 (by rfl) ⟨5319600, by rfl⟩ : syracuseStep 14185601 = 10639201) B10639201
theorem B9457067 : Blo 2213435 9457067 := bstep (se 1 (by rfl) ⟨7092800, by rfl⟩ : syracuseStep 9457067 = 14185601) B14185601
theorem B6304711 : Blo 2213435 6304711 := bstep (se 1 (by rfl) ⟨4728533, by rfl⟩ : syracuseStep 6304711 = 9457067) B9457067
theorem B8406281 : Blo 2213435 8406281 := bstep (se 2 (by rfl) ⟨3152355, by rfl⟩ : syracuseStep 8406281 = 6304711) B6304711
theorem B5604187 : Blo 2213435 5604187 := bstep (se 1 (by rfl) ⟨4203140, by rfl⟩ : syracuseStep 5604187 = 8406281) B8406281
theorem B7472249 : Blo 2213435 7472249 := bstep (se 2 (by rfl) ⟨2802093, by rfl⟩ : syracuseStep 7472249 = 5604187) B5604187
theorem B4981499 : Blo 2213435 4981499 := bstep (se 1 (by rfl) ⟨3736124, by rfl⟩ : syracuseStep 4981499 = 7472249) B7472249
theorem B3320999 : Blo 2213435 3320999 := bstep (se 1 (by rfl) ⟨2490749, by rfl⟩ : syracuseStep 3320999 = 4981499) B4981499
theorem B2213999 : Blo 2213435 2213999 := bstep (se 1 (by rfl) ⟨1660499, by rfl⟩ : syracuseStep 2213999 = 3320999) B3320999
theorem B3321005 : Blo 2213435 3321005 := bbase (se 3 (by rfl) ⟨622688, by rfl⟩ : syracuseStep 3321005 = 1245377) (by norm_num)
theorem B2214003 : Blo 2213435 2214003 := bstep (se 1 (by rfl) ⟨1660502, by rfl⟩ : syracuseStep 2214003 = 3321005) B3321005
theorem B4981517 : Blo 2213435 4981517 := bbase (se 3 (by rfl) ⟨934034, by rfl⟩ : syracuseStep 4981517 = 1868069) (by norm_num)
theorem B3321011 : Blo 2213435 3321011 := bstep (se 1 (by rfl) ⟨2490758, by rfl⟩ : syracuseStep 3321011 = 4981517) B4981517
theorem B2214007 : Blo 2213435 2214007 := bstep (se 1 (by rfl) ⟨1660505, by rfl⟩ : syracuseStep 2214007 = 3321011) B3321011
theorem B2802109 : Blo 2213435 2802109 := bbase (se 3 (by rfl) ⟨525395, by rfl⟩ : syracuseStep 2802109 = 1050791) (by norm_num)
theorem B3736145 : Blo 2213435 3736145 := bstep (se 2 (by rfl) ⟨1401054, by rfl⟩ : syracuseStep 3736145 = 2802109) B2802109
theorem B2490763 : Blo 2213435 2490763 := bstep (se 1 (by rfl) ⟨1868072, by rfl⟩ : syracuseStep 2490763 = 3736145) B3736145
theorem B3321017 : Blo 2213435 3321017 := bstep (se 2 (by rfl) ⟨1245381, by rfl⟩ : syracuseStep 3321017 = 2490763) B2490763
theorem B2214011 : Blo 2213435 2214011 := bstep (se 1 (by rfl) ⟨1660508, by rfl⟩ : syracuseStep 2214011 = 3321017) B3321017
theorem B5188229 : Blo 2213435 5188229 := bbase (se 4 (by rfl) ⟨486396, by rfl⟩ : syracuseStep 5188229 = 972793) (by norm_num)
theorem B3458819 : Blo 2213435 3458819 := bstep (se 1 (by rfl) ⟨2594114, by rfl⟩ : syracuseStep 3458819 = 5188229) B5188229
theorem B2305879 : Blo 2213435 2305879 := bstep (se 1 (by rfl) ⟨1729409, by rfl⟩ : syracuseStep 2305879 = 3458819) B3458819
theorem B49192085 : Blo 2213435 49192085 := bstep (se 6 (by rfl) ⟨1152939, by rfl⟩ : syracuseStep 49192085 = 2305879) B2305879
theorem B32794723 : Blo 2213435 32794723 := bstep (se 1 (by rfl) ⟨24596042, by rfl⟩ : syracuseStep 32794723 = 49192085) B49192085
theorem B174905189 : Blo 2213435 174905189 := bstep (se 4 (by rfl) ⟨16397361, by rfl⟩ : syracuseStep 174905189 = 32794723) B32794723
theorem B116603459 : Blo 2213435 116603459 := bstep (se 1 (by rfl) ⟨87452594, by rfl⟩ : syracuseStep 116603459 = 174905189) B174905189
theorem B77735639 : Blo 2213435 77735639 := bstep (se 1 (by rfl) ⟨58301729, by rfl⟩ : syracuseStep 77735639 = 116603459) B116603459
theorem B207295037 : Blo 2213435 207295037 := bstep (se 3 (by rfl) ⟨38867819, by rfl⟩ : syracuseStep 207295037 = 77735639) B77735639
theorem B138196691 : Blo 2213435 138196691 := bstep (se 1 (by rfl) ⟨103647518, by rfl⟩ : syracuseStep 138196691 = 207295037) B207295037
theorem B92131127 : Blo 2213435 92131127 := bstep (se 1 (by rfl) ⟨69098345, by rfl⟩ : syracuseStep 92131127 = 138196691) B138196691
theorem B61420751 : Blo 2213435 61420751 := bstep (se 1 (by rfl) ⟨46065563, by rfl⟩ : syracuseStep 61420751 = 92131127) B92131127
theorem B40947167 : Blo 2213435 40947167 := bstep (se 1 (by rfl) ⟨30710375, by rfl⟩ : syracuseStep 40947167 = 61420751) B61420751
theorem B109192445 : Blo 2213435 109192445 := bstep (se 3 (by rfl) ⟨20473583, by rfl⟩ : syracuseStep 109192445 = 40947167) B40947167
theorem B72794963 : Blo 2213435 72794963 := bstep (se 1 (by rfl) ⟨54596222, by rfl⟩ : syracuseStep 72794963 = 109192445) B109192445
theorem B48529975 : Blo 2213435 48529975 := bstep (se 1 (by rfl) ⟨36397481, by rfl⟩ : syracuseStep 48529975 = 72794963) B72794963
theorem B64706633 : Blo 2213435 64706633 := bstep (se 2 (by rfl) ⟨24264987, by rfl⟩ : syracuseStep 64706633 = 48529975) B48529975
theorem B43137755 : Blo 2213435 43137755 := bstep (se 1 (by rfl) ⟨32353316, by rfl⟩ : syracuseStep 43137755 = 64706633) B64706633
theorem B28758503 : Blo 2213435 28758503 := bstep (se 1 (by rfl) ⟨21568877, by rfl⟩ : syracuseStep 28758503 = 43137755) B43137755
theorem B19172335 : Blo 2213435 19172335 := bstep (se 1 (by rfl) ⟨14379251, by rfl⟩ : syracuseStep 19172335 = 28758503) B28758503
theorem B25563113 : Blo 2213435 25563113 := bstep (se 2 (by rfl) ⟨9586167, by rfl⟩ : syracuseStep 25563113 = 19172335) B19172335
theorem B17042075 : Blo 2213435 17042075 := bstep (se 1 (by rfl) ⟨12781556, by rfl⟩ : syracuseStep 17042075 = 25563113) B25563113
theorem B11361383 : Blo 2213435 11361383 := bstep (se 1 (by rfl) ⟨8521037, by rfl⟩ : syracuseStep 11361383 = 17042075) B17042075
theorem B7574255 : Blo 2213435 7574255 := bstep (se 1 (by rfl) ⟨5680691, by rfl⟩ : syracuseStep 7574255 = 11361383) B11361383
theorem B5049503 : Blo 2213435 5049503 := bstep (se 1 (by rfl) ⟨3787127, by rfl⟩ : syracuseStep 5049503 = 7574255) B7574255
theorem B3366335 : Blo 2213435 3366335 := bstep (se 1 (by rfl) ⟨2524751, by rfl⟩ : syracuseStep 3366335 = 5049503) B5049503
theorem B2244223 : Blo 2213435 2244223 := bstep (se 1 (by rfl) ⟨1683167, by rfl⟩ : syracuseStep 2244223 = 3366335) B3366335
theorem B2992297 : Blo 2213435 2992297 := bstep (se 2 (by rfl) ⟨1122111, by rfl⟩ : syracuseStep 2992297 = 2244223) B2244223
theorem B3989729 : Blo 2213435 3989729 := bstep (se 2 (by rfl) ⟨1496148, by rfl⟩ : syracuseStep 3989729 = 2992297) B2992297
theorem B10639277 : Blo 2213435 10639277 := bstep (se 3 (by rfl) ⟨1994864, by rfl⟩ : syracuseStep 10639277 = 3989729) B3989729
theorem B7092851 : Blo 2213435 7092851 := bstep (se 1 (by rfl) ⟨5319638, by rfl⟩ : syracuseStep 7092851 = 10639277) B10639277
theorem B18914269 : Blo 2213435 18914269 := bstep (se 3 (by rfl) ⟨3546425, by rfl⟩ : syracuseStep 18914269 = 7092851) B7092851
theorem B25219025 : Blo 2213435 25219025 := bstep (se 2 (by rfl) ⟨9457134, by rfl⟩ : syracuseStep 25219025 = 18914269) B18914269
theorem B16812683 : Blo 2213435 16812683 := bstep (se 1 (by rfl) ⟨12609512, by rfl⟩ : syracuseStep 16812683 = 25219025) B25219025
theorem B11208455 : Blo 2213435 11208455 := bstep (se 1 (by rfl) ⟨8406341, by rfl⟩ : syracuseStep 11208455 = 16812683) B16812683
theorem B7472303 : Blo 2213435 7472303 := bstep (se 1 (by rfl) ⟨5604227, by rfl⟩ : syracuseStep 7472303 = 11208455) B11208455
theorem B4981535 : Blo 2213435 4981535 := bstep (se 1 (by rfl) ⟨3736151, by rfl⟩ : syracuseStep 4981535 = 7472303) B7472303
theorem B3321023 : Blo 2213435 3321023 := bstep (se 1 (by rfl) ⟨2490767, by rfl⟩ : syracuseStep 3321023 = 4981535) B4981535
theorem B2214015 : Blo 2213435 2214015 := bstep (se 1 (by rfl) ⟨1660511, by rfl⟩ : syracuseStep 2214015 = 3321023) B3321023
theorem B3321029 : Blo 2213435 3321029 := bbase (se 4 (by rfl) ⟨311346, by rfl⟩ : syracuseStep 3321029 = 622693) (by norm_num)
theorem B2214019 : Blo 2213435 2214019 := bstep (se 1 (by rfl) ⟨1660514, by rfl⟩ : syracuseStep 2214019 = 3321029) B3321029
theorem B3736165 : Blo 2213435 3736165 := bbase (se 4 (by rfl) ⟨350265, by rfl⟩ : syracuseStep 3736165 = 700531) (by norm_num)
theorem B4981553 : Blo 2213435 4981553 := bstep (se 2 (by rfl) ⟨1868082, by rfl⟩ : syracuseStep 4981553 = 3736165) B3736165
theorem B3321035 : Blo 2213435 3321035 := bstep (se 1 (by rfl) ⟨2490776, by rfl⟩ : syracuseStep 3321035 = 4981553) B4981553
theorem B2214023 : Blo 2213435 2214023 := bstep (se 1 (by rfl) ⟨1660517, by rfl⟩ : syracuseStep 2214023 = 3321035) B3321035
theorem B2490781 : Blo 2213435 2490781 := bbase (se 3 (by rfl) ⟨467021, by rfl⟩ : syracuseStep 2490781 = 934043) (by norm_num)
theorem B3321041 : Blo 2213435 3321041 := bstep (se 2 (by rfl) ⟨1245390, by rfl⟩ : syracuseStep 3321041 = 2490781) B2490781
theorem B2214027 : Blo 2213435 2214027 := bstep (se 1 (by rfl) ⟨1660520, by rfl⟩ : syracuseStep 2214027 = 3321041) B3321041
theorem B7472357 : Blo 2213435 7472357 := bbase (se 4 (by rfl) ⟨700533, by rfl⟩ : syracuseStep 7472357 = 1401067) (by norm_num)
theorem B4981571 : Blo 2213435 4981571 := bstep (se 1 (by rfl) ⟨3736178, by rfl⟩ : syracuseStep 4981571 = 7472357) B7472357
theorem B3321047 : Blo 2213435 3321047 := bstep (se 1 (by rfl) ⟨2490785, by rfl⟩ : syracuseStep 3321047 = 4981571) B4981571
theorem B2214031 : Blo 2213435 2214031 := bstep (se 1 (by rfl) ⟨1660523, by rfl⟩ : syracuseStep 2214031 = 3321047) B3321047
theorem B3321053 : Blo 2213435 3321053 := bbase (se 3 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 3321053 = 1245395) (by norm_num)
theorem B2214035 : Blo 2213435 2214035 := bstep (se 1 (by rfl) ⟨1660526, by rfl⟩ : syracuseStep 2214035 = 3321053) B3321053
theorem B4981589 : Blo 2213435 4981589 := bbase (se 9 (by rfl) ⟨14594, by rfl⟩ : syracuseStep 4981589 = 29189) (by norm_num)
theorem B3321059 : Blo 2213435 3321059 := bstep (se 1 (by rfl) ⟨2490794, by rfl⟩ : syracuseStep 3321059 = 4981589) B4981589
theorem B2214039 : Blo 2213435 2214039 := bstep (se 1 (by rfl) ⟨1660529, by rfl⟩ : syracuseStep 2214039 = 3321059) B3321059
theorem B6304837 : Blo 2213435 6304837 := bbase (se 4 (by rfl) ⟨591078, by rfl⟩ : syracuseStep 6304837 = 1182157) (by norm_num)
theorem B8406449 : Blo 2213435 8406449 := bstep (se 2 (by rfl) ⟨3152418, by rfl⟩ : syracuseStep 8406449 = 6304837) B6304837
theorem B5604299 : Blo 2213435 5604299 := bstep (se 1 (by rfl) ⟨4203224, by rfl⟩ : syracuseStep 5604299 = 8406449) B8406449
theorem B3736199 : Blo 2213435 3736199 := bstep (se 1 (by rfl) ⟨2802149, by rfl⟩ : syracuseStep 3736199 = 5604299) B5604299
theorem B2490799 : Blo 2213435 2490799 := bstep (se 1 (by rfl) ⟨1868099, by rfl⟩ : syracuseStep 2490799 = 3736199) B3736199
theorem B3321065 : Blo 2213435 3321065 := bstep (se 2 (by rfl) ⟨1245399, by rfl⟩ : syracuseStep 3321065 = 2490799) B2490799
theorem B2214043 : Blo 2213435 2214043 := bstep (se 1 (by rfl) ⟨1660532, by rfl⟩ : syracuseStep 2214043 = 3321065) B3321065
theorem B5836837 : Blo 2213435 5836837 := bbase (se 4 (by rfl) ⟨547203, by rfl⟩ : syracuseStep 5836837 = 1094407) (by norm_num)
theorem B7782449 : Blo 2213435 7782449 := bstep (se 2 (by rfl) ⟨2918418, by rfl⟩ : syracuseStep 7782449 = 5836837) B5836837
theorem B83012789 : Blo 2213435 83012789 := bstep (se 5 (by rfl) ⟨3891224, by rfl⟩ : syracuseStep 83012789 = 7782449) B7782449
theorem B221367437 : Blo 2213435 221367437 := bstep (se 3 (by rfl) ⟨41506394, by rfl⟩ : syracuseStep 221367437 = 83012789) B83012789
theorem B147578291 : Blo 2213435 147578291 := bstep (se 1 (by rfl) ⟨110683718, by rfl⟩ : syracuseStep 147578291 = 221367437) B221367437
theorem B98385527 : Blo 2213435 98385527 := bstep (se 1 (by rfl) ⟨73789145, by rfl⟩ : syracuseStep 98385527 = 147578291) B147578291
theorem B262361405 : Blo 2213435 262361405 := bstep (se 3 (by rfl) ⟨49192763, by rfl⟩ : syracuseStep 262361405 = 98385527) B98385527
theorem B174907603 : Blo 2213435 174907603 := bstep (se 1 (by rfl) ⟨131180702, by rfl⟩ : syracuseStep 174907603 = 262361405) B262361405
theorem B233210137 : Blo 2213435 233210137 := bstep (se 2 (by rfl) ⟨87453801, by rfl⟩ : syracuseStep 233210137 = 174907603) B174907603
theorem B310946849 : Blo 2213435 310946849 := bstep (se 2 (by rfl) ⟨116605068, by rfl⟩ : syracuseStep 310946849 = 233210137) B233210137
theorem B207297899 : Blo 2213435 207297899 := bstep (se 1 (by rfl) ⟨155473424, by rfl⟩ : syracuseStep 207297899 = 310946849) B310946849
theorem B138198599 : Blo 2213435 138198599 := bstep (se 1 (by rfl) ⟨103648949, by rfl⟩ : syracuseStep 138198599 = 207297899) B207297899
theorem B92132399 : Blo 2213435 92132399 := bstep (se 1 (by rfl) ⟨69099299, by rfl⟩ : syracuseStep 92132399 = 138198599) B138198599
theorem B61421599 : Blo 2213435 61421599 := bstep (se 1 (by rfl) ⟨46066199, by rfl⟩ : syracuseStep 61421599 = 92132399) B92132399
theorem B81895465 : Blo 2213435 81895465 := bstep (se 2 (by rfl) ⟨30710799, by rfl⟩ : syracuseStep 81895465 = 61421599) B61421599
theorem B109193953 : Blo 2213435 109193953 := bstep (se 2 (by rfl) ⟨40947732, by rfl⟩ : syracuseStep 109193953 = 81895465) B81895465
theorem B145591937 : Blo 2213435 145591937 := bstep (se 2 (by rfl) ⟨54596976, by rfl⟩ : syracuseStep 145591937 = 109193953) B109193953
theorem B97061291 : Blo 2213435 97061291 := bstep (se 1 (by rfl) ⟨72795968, by rfl⟩ : syracuseStep 97061291 = 145591937) B145591937
theorem B64707527 : Blo 2213435 64707527 := bstep (se 1 (by rfl) ⟨48530645, by rfl⟩ : syracuseStep 64707527 = 97061291) B97061291
theorem B43138351 : Blo 2213435 43138351 := bstep (se 1 (by rfl) ⟨32353763, by rfl⟩ : syracuseStep 43138351 = 64707527) B64707527
theorem B230071205 : Blo 2213435 230071205 := bstep (se 4 (by rfl) ⟨21569175, by rfl⟩ : syracuseStep 230071205 = 43138351) B43138351
theorem B153380803 : Blo 2213435 153380803 := bstep (se 1 (by rfl) ⟨115035602, by rfl⟩ : syracuseStep 153380803 = 230071205) B230071205
theorem B204507737 : Blo 2213435 204507737 := bstep (se 2 (by rfl) ⟨76690401, by rfl⟩ : syracuseStep 204507737 = 153380803) B153380803
theorem B136338491 : Blo 2213435 136338491 := bstep (se 1 (by rfl) ⟨102253868, by rfl⟩ : syracuseStep 136338491 = 204507737) B204507737
theorem B363569309 : Blo 2213435 363569309 := bstep (se 3 (by rfl) ⟨68169245, by rfl⟩ : syracuseStep 363569309 = 136338491) B136338491
theorem B242379539 : Blo 2213435 242379539 := bstep (se 1 (by rfl) ⟨181784654, by rfl⟩ : syracuseStep 242379539 = 363569309) B363569309
theorem B161586359 : Blo 2213435 161586359 := bstep (se 1 (by rfl) ⟨121189769, by rfl⟩ : syracuseStep 161586359 = 242379539) B242379539
theorem B107724239 : Blo 2213435 107724239 := bstep (se 1 (by rfl) ⟨80793179, by rfl⟩ : syracuseStep 107724239 = 161586359) B161586359
theorem B71816159 : Blo 2213435 71816159 := bstep (se 1 (by rfl) ⟨53862119, by rfl⟩ : syracuseStep 71816159 = 107724239) B107724239
theorem B47877439 : Blo 2213435 47877439 := bstep (se 1 (by rfl) ⟨35908079, by rfl⟩ : syracuseStep 47877439 = 71816159) B71816159
theorem B63836585 : Blo 2213435 63836585 := bstep (se 2 (by rfl) ⟨23938719, by rfl⟩ : syracuseStep 63836585 = 47877439) B47877439
theorem B42557723 : Blo 2213435 42557723 := bstep (se 1 (by rfl) ⟨31918292, by rfl⟩ : syracuseStep 42557723 = 63836585) B63836585
theorem B28371815 : Blo 2213435 28371815 := bstep (se 1 (by rfl) ⟨21278861, by rfl⟩ : syracuseStep 28371815 = 42557723) B42557723
theorem B18914543 : Blo 2213435 18914543 := bstep (se 1 (by rfl) ⟨14185907, by rfl⟩ : syracuseStep 18914543 = 28371815) B28371815
theorem B12609695 : Blo 2213435 12609695 := bstep (se 1 (by rfl) ⟨9457271, by rfl⟩ : syracuseStep 12609695 = 18914543) B18914543
theorem B8406463 : Blo 2213435 8406463 := bstep (se 1 (by rfl) ⟨6304847, by rfl⟩ : syracuseStep 8406463 = 12609695) B12609695
theorem B11208617 : Blo 2213435 11208617 := bstep (se 2 (by rfl) ⟨4203231, by rfl⟩ : syracuseStep 11208617 = 8406463) B8406463
theorem B7472411 : Blo 2213435 7472411 := bstep (se 1 (by rfl) ⟨5604308, by rfl⟩ : syracuseStep 7472411 = 11208617) B11208617
theorem B4981607 : Blo 2213435 4981607 := bstep (se 1 (by rfl) ⟨3736205, by rfl⟩ : syracuseStep 4981607 = 7472411) B7472411
theorem B3321071 : Blo 2213435 3321071 := bstep (se 1 (by rfl) ⟨2490803, by rfl⟩ : syracuseStep 3321071 = 4981607) B4981607
theorem B2214047 : Blo 2213435 2214047 := bstep (se 1 (by rfl) ⟨1660535, by rfl⟩ : syracuseStep 2214047 = 3321071) B3321071
theorem B3321077 : Blo 2213435 3321077 := bbase (se 5 (by rfl) ⟨155675, by rfl⟩ : syracuseStep 3321077 = 311351) (by norm_num)
theorem B2214051 : Blo 2213435 2214051 := bstep (se 1 (by rfl) ⟨1660538, by rfl⟩ : syracuseStep 2214051 = 3321077) B3321077
theorem B3412325 : Blo 2213435 3412325 := bbase (se 4 (by rfl) ⟨319905, by rfl⟩ : syracuseStep 3412325 = 639811) (by norm_num)
theorem B9099533 : Blo 2213435 9099533 := bstep (se 3 (by rfl) ⟨1706162, by rfl⟩ : syracuseStep 9099533 = 3412325) B3412325
theorem B6066355 : Blo 2213435 6066355 := bstep (se 1 (by rfl) ⟨4549766, by rfl⟩ : syracuseStep 6066355 = 9099533) B9099533
theorem B8088473 : Blo 2213435 8088473 := bstep (se 2 (by rfl) ⟨3033177, by rfl⟩ : syracuseStep 8088473 = 6066355) B6066355
theorem B5392315 : Blo 2213435 5392315 := bstep (se 1 (by rfl) ⟨4044236, by rfl⟩ : syracuseStep 5392315 = 8088473) B8088473
theorem B28759013 : Blo 2213435 28759013 := bstep (se 4 (by rfl) ⟨2696157, by rfl⟩ : syracuseStep 28759013 = 5392315) B5392315
theorem B19172675 : Blo 2213435 19172675 := bstep (se 1 (by rfl) ⟨14379506, by rfl⟩ : syracuseStep 19172675 = 28759013) B28759013
theorem B12781783 : Blo 2213435 12781783 := bstep (se 1 (by rfl) ⟨9586337, by rfl⟩ : syracuseStep 12781783 = 19172675) B19172675
theorem B68169509 : Blo 2213435 68169509 := bstep (se 4 (by rfl) ⟨6390891, by rfl⟩ : syracuseStep 68169509 = 12781783) B12781783
theorem B45446339 : Blo 2213435 45446339 := bstep (se 1 (by rfl) ⟨34084754, by rfl⟩ : syracuseStep 45446339 = 68169509) B68169509
theorem B30297559 : Blo 2213435 30297559 := bstep (se 1 (by rfl) ⟨22723169, by rfl⟩ : syracuseStep 30297559 = 45446339) B45446339
theorem B40396745 : Blo 2213435 40396745 := bstep (se 2 (by rfl) ⟨15148779, by rfl⟩ : syracuseStep 40396745 = 30297559) B30297559
theorem B26931163 : Blo 2213435 26931163 := bstep (se 1 (by rfl) ⟨20198372, by rfl⟩ : syracuseStep 26931163 = 40396745) B40396745
theorem B35908217 : Blo 2213435 35908217 := bstep (se 2 (by rfl) ⟨13465581, by rfl⟩ : syracuseStep 35908217 = 26931163) B26931163
theorem B23938811 : Blo 2213435 23938811 := bstep (se 1 (by rfl) ⟨17954108, by rfl⟩ : syracuseStep 23938811 = 35908217) B35908217
theorem B15959207 : Blo 2213435 15959207 := bstep (se 1 (by rfl) ⟨11969405, by rfl⟩ : syracuseStep 15959207 = 23938811) B23938811
theorem B10639471 : Blo 2213435 10639471 := bstep (se 1 (by rfl) ⟨7979603, by rfl⟩ : syracuseStep 10639471 = 15959207) B15959207
theorem B14185961 : Blo 2213435 14185961 := bstep (se 2 (by rfl) ⟨5319735, by rfl⟩ : syracuseStep 14185961 = 10639471) B10639471
theorem B9457307 : Blo 2213435 9457307 := bstep (se 1 (by rfl) ⟨7092980, by rfl⟩ : syracuseStep 9457307 = 14185961) B14185961
theorem B6304871 : Blo 2213435 6304871 := bstep (se 1 (by rfl) ⟨4728653, by rfl⟩ : syracuseStep 6304871 = 9457307) B9457307
theorem B4203247 : Blo 2213435 4203247 := bstep (se 1 (by rfl) ⟨3152435, by rfl⟩ : syracuseStep 4203247 = 6304871) B6304871
theorem B5604329 : Blo 2213435 5604329 := bstep (se 2 (by rfl) ⟨2101623, by rfl⟩ : syracuseStep 5604329 = 4203247) B4203247
theorem B3736219 : Blo 2213435 3736219 := bstep (se 1 (by rfl) ⟨2802164, by rfl⟩ : syracuseStep 3736219 = 5604329) B5604329
theorem B4981625 : Blo 2213435 4981625 := bstep (se 2 (by rfl) ⟨1868109, by rfl⟩ : syracuseStep 4981625 = 3736219) B3736219
theorem B3321083 : Blo 2213435 3321083 := bstep (se 1 (by rfl) ⟨2490812, by rfl⟩ : syracuseStep 3321083 = 4981625) B4981625
theorem B2214055 : Blo 2213435 2214055 := bstep (se 1 (by rfl) ⟨1660541, by rfl⟩ : syracuseStep 2214055 = 3321083) B3321083
theorem B2490817 : Blo 2213435 2490817 := bbase (se 2 (by rfl) ⟨934056, by rfl⟩ : syracuseStep 2490817 = 1868113) (by norm_num)
theorem B3321089 : Blo 2213435 3321089 := bstep (se 2 (by rfl) ⟨1245408, by rfl⟩ : syracuseStep 3321089 = 2490817) B2490817
theorem B2214059 : Blo 2213435 2214059 := bstep (se 1 (by rfl) ⟨1660544, by rfl⟩ : syracuseStep 2214059 = 3321089) B3321089
theorem B5604349 : Blo 2213435 5604349 := bbase (se 3 (by rfl) ⟨1050815, by rfl⟩ : syracuseStep 5604349 = 2101631) (by norm_num)
theorem B7472465 : Blo 2213435 7472465 := bstep (se 2 (by rfl) ⟨2802174, by rfl⟩ : syracuseStep 7472465 = 5604349) B5604349
theorem B4981643 : Blo 2213435 4981643 := bstep (se 1 (by rfl) ⟨3736232, by rfl⟩ : syracuseStep 4981643 = 7472465) B7472465
theorem B3321095 : Blo 2213435 3321095 := bstep (se 1 (by rfl) ⟨2490821, by rfl⟩ : syracuseStep 3321095 = 4981643) B4981643
theorem B2214063 : Blo 2213435 2214063 := bstep (se 1 (by rfl) ⟨1660547, by rfl⟩ : syracuseStep 2214063 = 3321095) B3321095
theorem B3321101 : Blo 2213435 3321101 := bbase (se 3 (by rfl) ⟨622706, by rfl⟩ : syracuseStep 3321101 = 1245413) (by norm_num)
theorem B2214067 : Blo 2213435 2214067 := bstep (se 1 (by rfl) ⟨1660550, by rfl⟩ : syracuseStep 2214067 = 3321101) B3321101
theorem B4981661 : Blo 2213435 4981661 := bbase (se 3 (by rfl) ⟨934061, by rfl⟩ : syracuseStep 4981661 = 1868123) (by norm_num)
theorem B3321107 : Blo 2213435 3321107 := bstep (se 1 (by rfl) ⟨2490830, by rfl⟩ : syracuseStep 3321107 = 4981661) B4981661
theorem B2214071 : Blo 2213435 2214071 := bstep (se 1 (by rfl) ⟨1660553, by rfl⟩ : syracuseStep 2214071 = 3321107) B3321107
theorem B3736253 : Blo 2213435 3736253 := bbase (se 3 (by rfl) ⟨700547, by rfl⟩ : syracuseStep 3736253 = 1401095) (by norm_num)
theorem B2490835 : Blo 2213435 2490835 := bstep (se 1 (by rfl) ⟨1868126, by rfl⟩ : syracuseStep 2490835 = 3736253) B3736253
theorem B3321113 : Blo 2213435 3321113 := bstep (se 2 (by rfl) ⟨1245417, by rfl⟩ : syracuseStep 3321113 = 2490835) B2490835
theorem B2214075 : Blo 2213435 2214075 := bstep (se 1 (by rfl) ⟨1660556, by rfl⟩ : syracuseStep 2214075 = 3321113) B3321113
theorem B12609877 : Blo 2213435 12609877 := bbase (se 10 (by rfl) ⟨18471, by rfl⟩ : syracuseStep 12609877 = 36943) (by norm_num)
theorem B16813169 : Blo 2213435 16813169 := bstep (se 2 (by rfl) ⟨6304938, by rfl⟩ : syracuseStep 16813169 = 12609877) B12609877
theorem B11208779 : Blo 2213435 11208779 := bstep (se 1 (by rfl) ⟨8406584, by rfl⟩ : syracuseStep 11208779 = 16813169) B16813169
theorem B7472519 : Blo 2213435 7472519 := bstep (se 1 (by rfl) ⟨5604389, by rfl⟩ : syracuseStep 7472519 = 11208779) B11208779
theorem B4981679 : Blo 2213435 4981679 := bstep (se 1 (by rfl) ⟨3736259, by rfl⟩ : syracuseStep 4981679 = 7472519) B7472519
theorem B3321119 : Blo 2213435 3321119 := bstep (se 1 (by rfl) ⟨2490839, by rfl⟩ : syracuseStep 3321119 = 4981679) B4981679
theorem B2214079 : Blo 2213435 2214079 := bstep (se 1 (by rfl) ⟨1660559, by rfl⟩ : syracuseStep 2214079 = 3321119) B3321119
theorem B3321125 : Blo 2213435 3321125 := bbase (se 4 (by rfl) ⟨311355, by rfl⟩ : syracuseStep 3321125 = 622711) (by norm_num)
theorem B2214083 : Blo 2213435 2214083 := bstep (se 1 (by rfl) ⟨1660562, by rfl⟩ : syracuseStep 2214083 = 3321125) B3321125
theorem B2802205 : Blo 2213435 2802205 := bbase (se 3 (by rfl) ⟨525413, by rfl⟩ : syracuseStep 2802205 = 1050827) (by norm_num)
theorem B3736273 : Blo 2213435 3736273 := bstep (se 2 (by rfl) ⟨1401102, by rfl⟩ : syracuseStep 3736273 = 2802205) B2802205
theorem B4981697 : Blo 2213435 4981697 := bstep (se 2 (by rfl) ⟨1868136, by rfl⟩ : syracuseStep 4981697 = 3736273) B3736273
theorem B3321131 : Blo 2213435 3321131 := bstep (se 1 (by rfl) ⟨2490848, by rfl⟩ : syracuseStep 3321131 = 4981697) B4981697
theorem B2214087 : Blo 2213435 2214087 := bstep (se 1 (by rfl) ⟨1660565, by rfl⟩ : syracuseStep 2214087 = 3321131) B3321131
theorem B2490853 : Blo 2213435 2490853 := bbase (se 4 (by rfl) ⟨233517, by rfl⟩ : syracuseStep 2490853 = 467035) (by norm_num)
theorem B3321137 : Blo 2213435 3321137 := bstep (se 2 (by rfl) ⟨1245426, by rfl⟩ : syracuseStep 3321137 = 2490853) B2490853
theorem B2214091 : Blo 2213435 2214091 := bstep (se 1 (by rfl) ⟨1660568, by rfl⟩ : syracuseStep 2214091 = 3321137) B3321137
theorem B7093109 : Blo 2213435 7093109 := bbase (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) (by norm_num)
theorem B4728739 : Blo 2213435 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B6304985 : Blo 2213435 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B4203323 : Blo 2213435 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B2802215 : Blo 2213435 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B7472573 : Blo 2213435 7472573 := bstep (se 3 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 7472573 = 2802215) B2802215
theorem B4981715 : Blo 2213435 4981715 := bstep (se 1 (by rfl) ⟨3736286, by rfl⟩ : syracuseStep 4981715 = 7472573) B7472573
theorem B3321143 : Blo 2213435 3321143 := bstep (se 1 (by rfl) ⟨2490857, by rfl⟩ : syracuseStep 3321143 = 4981715) B4981715
theorem B2214095 : Blo 2213435 2214095 := bstep (se 1 (by rfl) ⟨1660571, by rfl⟩ : syracuseStep 2214095 = 3321143) B3321143
theorem B3321149 : Blo 2213435 3321149 := bbase (se 3 (by rfl) ⟨622715, by rfl⟩ : syracuseStep 3321149 = 1245431) (by norm_num)
theorem B2214099 : Blo 2213435 2214099 := bstep (se 1 (by rfl) ⟨1660574, by rfl⟩ : syracuseStep 2214099 = 3321149) B3321149
theorem B4981733 : Blo 2213435 4981733 := bbase (se 4 (by rfl) ⟨467037, by rfl⟩ : syracuseStep 4981733 = 934075) (by norm_num)
theorem B3321155 : Blo 2213435 3321155 := bstep (se 1 (by rfl) ⟨2490866, by rfl⟩ : syracuseStep 3321155 = 4981733) B4981733
theorem B2214103 : Blo 2213435 2214103 := bstep (se 1 (by rfl) ⟨1660577, by rfl⟩ : syracuseStep 2214103 = 3321155) B3321155
theorem B5604461 : Blo 2213435 5604461 := bbase (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) (by norm_num)
theorem B3736307 : Blo 2213435 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B2490871 : Blo 2213435 2490871 := bstep (se 1 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 2490871 = 3736307) B3736307
theorem B3321161 : Blo 2213435 3321161 := bstep (se 2 (by rfl) ⟨1245435, by rfl⟩ : syracuseStep 3321161 = 2490871) B2490871
theorem B2214107 : Blo 2213435 2214107 := bstep (se 1 (by rfl) ⟨1660580, by rfl⟩ : syracuseStep 2214107 = 3321161) B3321161
theorem B4728773 : Blo 2213435 4728773 := bbase (se 4 (by rfl) ⟨443322, by rfl⟩ : syracuseStep 4728773 = 886645) (by norm_num)
theorem B3152515 : Blo 2213435 3152515 := bstep (se 1 (by rfl) ⟨2364386, by rfl⟩ : syracuseStep 3152515 = 4728773) B4728773
theorem B4203353 : Blo 2213435 4203353 := bstep (se 2 (by rfl) ⟨1576257, by rfl⟩ : syracuseStep 4203353 = 3152515) B3152515
theorem B11208941 : Blo 2213435 11208941 := bstep (se 3 (by rfl) ⟨2101676, by rfl⟩ : syracuseStep 11208941 = 4203353) B4203353
theorem B7472627 : Blo 2213435 7472627 := bstep (se 1 (by rfl) ⟨5604470, by rfl⟩ : syracuseStep 7472627 = 11208941) B11208941
theorem B4981751 : Blo 2213435 4981751 := bstep (se 1 (by rfl) ⟨3736313, by rfl⟩ : syracuseStep 4981751 = 7472627) B7472627
theorem B3321167 : Blo 2213435 3321167 := bstep (se 1 (by rfl) ⟨2490875, by rfl⟩ : syracuseStep 3321167 = 4981751) B4981751
theorem B2214111 : Blo 2213435 2214111 := bstep (se 1 (by rfl) ⟨1660583, by rfl⟩ : syracuseStep 2214111 = 3321167) B3321167
theorem B3321173 : Blo 2213435 3321173 := bbase (se 11 (by rfl) ⟨2432, by rfl⟩ : syracuseStep 3321173 = 4865) (by norm_num)
theorem B2214115 : Blo 2213435 2214115 := bstep (se 1 (by rfl) ⟨1660586, by rfl⟩ : syracuseStep 2214115 = 3321173) B3321173
theorem B2659945 : Blo 2213435 2659945 := bbase (se 2 (by rfl) ⟨997479, by rfl⟩ : syracuseStep 2659945 = 1994959) (by norm_num)
theorem B3546593 : Blo 2213435 3546593 := bstep (se 2 (by rfl) ⟨1329972, by rfl⟩ : syracuseStep 3546593 = 2659945) B2659945
theorem B2364395 : Blo 2213435 2364395 := bstep (se 1 (by rfl) ⟨1773296, by rfl⟩ : syracuseStep 2364395 = 3546593) B3546593
theorem B6305053 : Blo 2213435 6305053 := bstep (se 3 (by rfl) ⟨1182197, by rfl⟩ : syracuseStep 6305053 = 2364395) B2364395
theorem B8406737 : Blo 2213435 8406737 := bstep (se 2 (by rfl) ⟨3152526, by rfl⟩ : syracuseStep 8406737 = 6305053) B6305053
theorem B5604491 : Blo 2213435 5604491 := bstep (se 1 (by rfl) ⟨4203368, by rfl⟩ : syracuseStep 5604491 = 8406737) B8406737
theorem B3736327 : Blo 2213435 3736327 := bstep (se 1 (by rfl) ⟨2802245, by rfl⟩ : syracuseStep 3736327 = 5604491) B5604491
theorem B4981769 : Blo 2213435 4981769 := bstep (se 2 (by rfl) ⟨1868163, by rfl⟩ : syracuseStep 4981769 = 3736327) B3736327
theorem B3321179 : Blo 2213435 3321179 := bstep (se 1 (by rfl) ⟨2490884, by rfl⟩ : syracuseStep 3321179 = 4981769) B4981769
theorem B2214119 : Blo 2213435 2214119 := bstep (se 1 (by rfl) ⟨1660589, by rfl⟩ : syracuseStep 2214119 = 3321179) B3321179
theorem B2490889 : Blo 2213435 2490889 := bbase (se 2 (by rfl) ⟨934083, by rfl⟩ : syracuseStep 2490889 = 1868167) (by norm_num)
theorem B3321185 : Blo 2213435 3321185 := bstep (se 2 (by rfl) ⟨1245444, by rfl⟩ : syracuseStep 3321185 = 2490889) B2490889
theorem B2214123 : Blo 2213435 2214123 := bstep (se 1 (by rfl) ⟨1660592, by rfl⟩ : syracuseStep 2214123 = 3321185) B3321185
theorem B10784981 : Blo 2213435 10784981 := bbase (se 7 (by rfl) ⟨126386, by rfl⟩ : syracuseStep 10784981 = 252773) (by norm_num)
theorem B7189987 : Blo 2213435 7189987 := bstep (se 1 (by rfl) ⟨5392490, by rfl⟩ : syracuseStep 7189987 = 10784981) B10784981
theorem B9586649 : Blo 2213435 9586649 := bstep (se 2 (by rfl) ⟨3594993, by rfl⟩ : syracuseStep 9586649 = 7189987) B7189987
theorem B6391099 : Blo 2213435 6391099 := bstep (se 1 (by rfl) ⟨4793324, by rfl⟩ : syracuseStep 6391099 = 9586649) B9586649
theorem B8521465 : Blo 2213435 8521465 := bstep (se 2 (by rfl) ⟨3195549, by rfl⟩ : syracuseStep 8521465 = 6391099) B6391099
theorem B11361953 : Blo 2213435 11361953 := bstep (se 2 (by rfl) ⟨4260732, by rfl⟩ : syracuseStep 11361953 = 8521465) B8521465
theorem B7574635 : Blo 2213435 7574635 := bstep (se 1 (by rfl) ⟨5680976, by rfl⟩ : syracuseStep 7574635 = 11361953) B11361953
theorem B10099513 : Blo 2213435 10099513 := bstep (se 2 (by rfl) ⟨3787317, by rfl⟩ : syracuseStep 10099513 = 7574635) B7574635
theorem B13466017 : Blo 2213435 13466017 := bstep (se 2 (by rfl) ⟨5049756, by rfl⟩ : syracuseStep 13466017 = 10099513) B10099513
theorem B71818757 : Blo 2213435 71818757 := bstep (se 4 (by rfl) ⟨6733008, by rfl⟩ : syracuseStep 71818757 = 13466017) B13466017
theorem B47879171 : Blo 2213435 47879171 := bstep (se 1 (by rfl) ⟨35909378, by rfl⟩ : syracuseStep 47879171 = 71818757) B71818757
theorem B31919447 : Blo 2213435 31919447 := bstep (se 1 (by rfl) ⟨23939585, by rfl⟩ : syracuseStep 31919447 = 47879171) B47879171
theorem B21279631 : Blo 2213435 21279631 := bstep (se 1 (by rfl) ⟨15959723, by rfl⟩ : syracuseStep 21279631 = 31919447) B31919447
theorem B28372841 : Blo 2213435 28372841 := bstep (se 2 (by rfl) ⟨10639815, by rfl⟩ : syracuseStep 28372841 = 21279631) B21279631
theorem B18915227 : Blo 2213435 18915227 := bstep (se 1 (by rfl) ⟨14186420, by rfl⟩ : syracuseStep 18915227 = 28372841) B28372841
theorem B12610151 : Blo 2213435 12610151 := bstep (se 1 (by rfl) ⟨9457613, by rfl⟩ : syracuseStep 12610151 = 18915227) B18915227
theorem B8406767 : Blo 2213435 8406767 := bstep (se 1 (by rfl) ⟨6305075, by rfl⟩ : syracuseStep 8406767 = 12610151) B12610151
theorem B5604511 : Blo 2213435 5604511 := bstep (se 1 (by rfl) ⟨4203383, by rfl⟩ : syracuseStep 5604511 = 8406767) B8406767
theorem B7472681 : Blo 2213435 7472681 := bstep (se 2 (by rfl) ⟨2802255, by rfl⟩ : syracuseStep 7472681 = 5604511) B5604511
theorem B4981787 : Blo 2213435 4981787 := bstep (se 1 (by rfl) ⟨3736340, by rfl⟩ : syracuseStep 4981787 = 7472681) B7472681
theorem B3321191 : Blo 2213435 3321191 := bstep (se 1 (by rfl) ⟨2490893, by rfl⟩ : syracuseStep 3321191 = 4981787) B4981787
theorem B2214127 : Blo 2213435 2214127 := bstep (se 1 (by rfl) ⟨1660595, by rfl⟩ : syracuseStep 2214127 = 3321191) B3321191
theorem B3321197 : Blo 2213435 3321197 := bbase (se 3 (by rfl) ⟨622724, by rfl⟩ : syracuseStep 3321197 = 1245449) (by norm_num)
theorem B2214131 : Blo 2213435 2214131 := bstep (se 1 (by rfl) ⟨1660598, by rfl⟩ : syracuseStep 2214131 = 3321197) B3321197
theorem B4981805 : Blo 2213435 4981805 := bbase (se 3 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 4981805 = 1868177) (by norm_num)
theorem B3321203 : Blo 2213435 3321203 := bstep (se 1 (by rfl) ⟨2490902, by rfl⟩ : syracuseStep 3321203 = 4981805) B4981805
theorem B2214135 : Blo 2213435 2214135 := bstep (se 1 (by rfl) ⟨1660601, by rfl⟩ : syracuseStep 2214135 = 3321203) B3321203
theorem B2659969 : Blo 2213435 2659969 := bbase (se 2 (by rfl) ⟨997488, by rfl⟩ : syracuseStep 2659969 = 1994977) (by norm_num)
theorem B14186501 : Blo 2213435 14186501 := bstep (se 4 (by rfl) ⟨1329984, by rfl⟩ : syracuseStep 14186501 = 2659969) B2659969
theorem B9457667 : Blo 2213435 9457667 := bstep (se 1 (by rfl) ⟨7093250, by rfl⟩ : syracuseStep 9457667 = 14186501) B14186501
theorem B6305111 : Blo 2213435 6305111 := bstep (se 1 (by rfl) ⟨4728833, by rfl⟩ : syracuseStep 6305111 = 9457667) B9457667
theorem B4203407 : Blo 2213435 4203407 := bstep (se 1 (by rfl) ⟨3152555, by rfl⟩ : syracuseStep 4203407 = 6305111) B6305111
theorem B2802271 : Blo 2213435 2802271 := bstep (se 1 (by rfl) ⟨2101703, by rfl⟩ : syracuseStep 2802271 = 4203407) B4203407
theorem B3736361 : Blo 2213435 3736361 := bstep (se 2 (by rfl) ⟨1401135, by rfl⟩ : syracuseStep 3736361 = 2802271) B2802271
theorem B2490907 : Blo 2213435 2490907 := bstep (se 1 (by rfl) ⟨1868180, by rfl⟩ : syracuseStep 2490907 = 3736361) B3736361
theorem B3321209 : Blo 2213435 3321209 := bstep (se 2 (by rfl) ⟨1245453, by rfl⟩ : syracuseStep 3321209 = 2490907) B2490907
theorem B2214139 : Blo 2213435 2214139 := bstep (se 1 (by rfl) ⟨1660604, by rfl⟩ : syracuseStep 2214139 = 3321209) B3321209
theorem B2659973 : Blo 2213435 2659973 := bbase (se 4 (by rfl) ⟨249372, by rfl⟩ : syracuseStep 2659973 = 498745) (by norm_num)
theorem B7093261 : Blo 2213435 7093261 := bstep (se 3 (by rfl) ⟨1329986, by rfl⟩ : syracuseStep 7093261 = 2659973) B2659973
theorem B37830725 : Blo 2213435 37830725 := bstep (se 4 (by rfl) ⟨3546630, by rfl⟩ : syracuseStep 37830725 = 7093261) B7093261
theorem B25220483 : Blo 2213435 25220483 := bstep (se 1 (by rfl) ⟨18915362, by rfl⟩ : syracuseStep 25220483 = 37830725) B37830725
theorem B16813655 : Blo 2213435 16813655 := bstep (se 1 (by rfl) ⟨12610241, by rfl⟩ : syracuseStep 16813655 = 25220483) B25220483
theorem B11209103 : Blo 2213435 11209103 := bstep (se 1 (by rfl) ⟨8406827, by rfl⟩ : syracuseStep 11209103 = 16813655) B16813655
theorem B7472735 : Blo 2213435 7472735 := bstep (se 1 (by rfl) ⟨5604551, by rfl⟩ : syracuseStep 7472735 = 11209103) B11209103
theorem B4981823 : Blo 2213435 4981823 := bstep (se 1 (by rfl) ⟨3736367, by rfl⟩ : syracuseStep 4981823 = 7472735) B7472735
theorem B3321215 : Blo 2213435 3321215 := bstep (se 1 (by rfl) ⟨2490911, by rfl⟩ : syracuseStep 3321215 = 4981823) B4981823
theorem B2214143 : Blo 2213435 2214143 := bstep (se 1 (by rfl) ⟨1660607, by rfl⟩ : syracuseStep 2214143 = 3321215) B3321215
theorem B3321221 : Blo 2213435 3321221 := bbase (se 4 (by rfl) ⟨311364, by rfl⟩ : syracuseStep 3321221 = 622729) (by norm_num)
theorem B2214147 : Blo 2213435 2214147 := bstep (se 1 (by rfl) ⟨1660610, by rfl⟩ : syracuseStep 2214147 = 3321221) B3321221
theorem B3736381 : Blo 2213435 3736381 := bbase (se 3 (by rfl) ⟨700571, by rfl⟩ : syracuseStep 3736381 = 1401143) (by norm_num)
theorem B4981841 : Blo 2213435 4981841 := bstep (se 2 (by rfl) ⟨1868190, by rfl⟩ : syracuseStep 4981841 = 3736381) B3736381
theorem B3321227 : Blo 2213435 3321227 := bstep (se 1 (by rfl) ⟨2490920, by rfl⟩ : syracuseStep 3321227 = 4981841) B4981841
theorem B2214151 : Blo 2213435 2214151 := bstep (se 1 (by rfl) ⟨1660613, by rfl⟩ : syracuseStep 2214151 = 3321227) B3321227
theorem B2490925 : Blo 2213435 2490925 := bbase (se 3 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 2490925 = 934097) (by norm_num)
theorem B3321233 : Blo 2213435 3321233 := bstep (se 2 (by rfl) ⟨1245462, by rfl⟩ : syracuseStep 3321233 = 2490925) B2490925
theorem B2214155 : Blo 2213435 2214155 := bstep (se 1 (by rfl) ⟨1660616, by rfl⟩ : syracuseStep 2214155 = 3321233) B3321233
theorem B7472789 : Blo 2213435 7472789 := bbase (se 6 (by rfl) ⟨175143, by rfl⟩ : syracuseStep 7472789 = 350287) (by norm_num)
theorem B4981859 : Blo 2213435 4981859 := bstep (se 1 (by rfl) ⟨3736394, by rfl⟩ : syracuseStep 4981859 = 7472789) B7472789
theorem B3321239 : Blo 2213435 3321239 := bstep (se 1 (by rfl) ⟨2490929, by rfl⟩ : syracuseStep 3321239 = 4981859) B4981859
theorem B2214159 : Blo 2213435 2214159 := bstep (se 1 (by rfl) ⟨1660619, by rfl⟩ : syracuseStep 2214159 = 3321239) B3321239
theorem B3321245 : Blo 2213435 3321245 := bbase (se 3 (by rfl) ⟨622733, by rfl⟩ : syracuseStep 3321245 = 1245467) (by norm_num)
theorem B2214163 : Blo 2213435 2214163 := bstep (se 1 (by rfl) ⟨1660622, by rfl⟩ : syracuseStep 2214163 = 3321245) B3321245
theorem B4981877 : Blo 2213435 4981877 := bbase (se 5 (by rfl) ⟨233525, by rfl⟩ : syracuseStep 4981877 = 467051) (by norm_num)
theorem B3321251 : Blo 2213435 3321251 := bstep (se 1 (by rfl) ⟨2490938, by rfl⟩ : syracuseStep 3321251 = 4981877) B4981877
theorem B2214167 : Blo 2213435 2214167 := bstep (se 1 (by rfl) ⟨1660625, by rfl⟩ : syracuseStep 2214167 = 3321251) B3321251
theorem B18915605 : Blo 2213435 18915605 := bbase (se 6 (by rfl) ⟨443334, by rfl⟩ : syracuseStep 18915605 = 886669) (by norm_num)
theorem B12610403 : Blo 2213435 12610403 := bstep (se 1 (by rfl) ⟨9457802, by rfl⟩ : syracuseStep 12610403 = 18915605) B18915605
theorem B8406935 : Blo 2213435 8406935 := bstep (se 1 (by rfl) ⟨6305201, by rfl⟩ : syracuseStep 8406935 = 12610403) B12610403
theorem B5604623 : Blo 2213435 5604623 := bstep (se 1 (by rfl) ⟨4203467, by rfl⟩ : syracuseStep 5604623 = 8406935) B8406935
theorem B3736415 : Blo 2213435 3736415 := bstep (se 1 (by rfl) ⟨2802311, by rfl⟩ : syracuseStep 3736415 = 5604623) B5604623
theorem B2490943 : Blo 2213435 2490943 := bstep (se 1 (by rfl) ⟨1868207, by rfl⟩ : syracuseStep 2490943 = 3736415) B3736415
theorem B3321257 : Blo 2213435 3321257 := bstep (se 2 (by rfl) ⟨1245471, by rfl⟩ : syracuseStep 3321257 = 2490943) B2490943
theorem B2214171 : Blo 2213435 2214171 := bstep (se 1 (by rfl) ⟨1660628, by rfl⟩ : syracuseStep 2214171 = 3321257) B3321257
theorem B8406949 : Blo 2213435 8406949 := bbase (se 4 (by rfl) ⟨788151, by rfl⟩ : syracuseStep 8406949 = 1576303) (by norm_num)
theorem B11209265 : Blo 2213435 11209265 := bstep (se 2 (by rfl) ⟨4203474, by rfl⟩ : syracuseStep 11209265 = 8406949) B8406949
theorem B7472843 : Blo 2213435 7472843 := bstep (se 1 (by rfl) ⟨5604632, by rfl⟩ : syracuseStep 7472843 = 11209265) B11209265
theorem B4981895 : Blo 2213435 4981895 := bstep (se 1 (by rfl) ⟨3736421, by rfl⟩ : syracuseStep 4981895 = 7472843) B7472843
theorem B3321263 : Blo 2213435 3321263 := bstep (se 1 (by rfl) ⟨2490947, by rfl⟩ : syracuseStep 3321263 = 4981895) B4981895
theorem B2214175 : Blo 2213435 2214175 := bstep (se 1 (by rfl) ⟨1660631, by rfl⟩ : syracuseStep 2214175 = 3321263) B3321263
theorem B3321269 : Blo 2213435 3321269 := bbase (se 5 (by rfl) ⟨155684, by rfl⟩ : syracuseStep 3321269 = 311369) (by norm_num)
theorem B2214179 : Blo 2213435 2214179 := bstep (se 1 (by rfl) ⟨1660634, by rfl⟩ : syracuseStep 2214179 = 3321269) B3321269
theorem B5604653 : Blo 2213435 5604653 := bbase (se 3 (by rfl) ⟨1050872, by rfl⟩ : syracuseStep 5604653 = 2101745) (by norm_num)
theorem B3736435 : Blo 2213435 3736435 := bstep (se 1 (by rfl) ⟨2802326, by rfl⟩ : syracuseStep 3736435 = 5604653) B5604653
theorem B4981913 : Blo 2213435 4981913 := bstep (se 2 (by rfl) ⟨1868217, by rfl⟩ : syracuseStep 4981913 = 3736435) B3736435
theorem B3321275 : Blo 2213435 3321275 := bstep (se 1 (by rfl) ⟨2490956, by rfl⟩ : syracuseStep 3321275 = 4981913) B4981913
theorem B2214183 : Blo 2213435 2214183 := bstep (se 1 (by rfl) ⟨1660637, by rfl⟩ : syracuseStep 2214183 = 3321275) B3321275
theorem B2490961 : Blo 2213435 2490961 := bbase (se 2 (by rfl) ⟨934110, by rfl⟩ : syracuseStep 2490961 = 1868221) (by norm_num)
theorem B3321281 : Blo 2213435 3321281 := bstep (se 2 (by rfl) ⟨1245480, by rfl⟩ : syracuseStep 3321281 = 2490961) B2490961
theorem B2214187 : Blo 2213435 2214187 := bstep (se 1 (by rfl) ⟨1660640, by rfl⟩ : syracuseStep 2214187 = 3321281) B3321281
theorem B3152629 : Blo 2213435 3152629 := bbase (se 5 (by rfl) ⟨147779, by rfl⟩ : syracuseStep 3152629 = 295559) (by norm_num)
theorem B4203505 : Blo 2213435 4203505 := bstep (se 2 (by rfl) ⟨1576314, by rfl⟩ : syracuseStep 4203505 = 3152629) B3152629
theorem B5604673 : Blo 2213435 5604673 := bstep (se 2 (by rfl) ⟨2101752, by rfl⟩ : syracuseStep 5604673 = 4203505) B4203505
theorem B7472897 : Blo 2213435 7472897 := bstep (se 2 (by rfl) ⟨2802336, by rfl⟩ : syracuseStep 7472897 = 5604673) B5604673
theorem B4981931 : Blo 2213435 4981931 := bstep (se 1 (by rfl) ⟨3736448, by rfl⟩ : syracuseStep 4981931 = 7472897) B7472897
theorem B3321287 : Blo 2213435 3321287 := bstep (se 1 (by rfl) ⟨2490965, by rfl⟩ : syracuseStep 3321287 = 4981931) B4981931
theorem B2214191 : Blo 2213435 2214191 := bstep (se 1 (by rfl) ⟨1660643, by rfl⟩ : syracuseStep 2214191 = 3321287) B3321287
theorem B3321293 : Blo 2213435 3321293 := bbase (se 3 (by rfl) ⟨622742, by rfl⟩ : syracuseStep 3321293 = 1245485) (by norm_num)
theorem B2214195 : Blo 2213435 2214195 := bstep (se 1 (by rfl) ⟨1660646, by rfl⟩ : syracuseStep 2214195 = 3321293) B3321293
theorem B4981949 : Blo 2213435 4981949 := bbase (se 3 (by rfl) ⟨934115, by rfl⟩ : syracuseStep 4981949 = 1868231) (by norm_num)
theorem B3321299 : Blo 2213435 3321299 := bstep (se 1 (by rfl) ⟨2490974, by rfl⟩ : syracuseStep 3321299 = 4981949) B4981949
theorem B2214199 : Blo 2213435 2214199 := bstep (se 1 (by rfl) ⟨1660649, by rfl⟩ : syracuseStep 2214199 = 3321299) B3321299
theorem B3736469 : Blo 2213435 3736469 := bbase (se 6 (by rfl) ⟨87573, by rfl⟩ : syracuseStep 3736469 = 175147) (by norm_num)
theorem B2490979 : Blo 2213435 2490979 := bstep (se 1 (by rfl) ⟨1868234, by rfl⟩ : syracuseStep 2490979 = 3736469) B3736469
theorem B3321305 : Blo 2213435 3321305 := bstep (se 2 (by rfl) ⟨1245489, by rfl⟩ : syracuseStep 3321305 = 2490979) B2490979
theorem B2214203 : Blo 2213435 2214203 := bstep (se 1 (by rfl) ⟨1660652, by rfl⟩ : syracuseStep 2214203 = 3321305) B3321305
theorem B14186933 : Blo 2213435 14186933 := bbase (se 5 (by rfl) ⟨665012, by rfl⟩ : syracuseStep 14186933 = 1330025) (by norm_num)
theorem B9457955 : Blo 2213435 9457955 := bstep (se 1 (by rfl) ⟨7093466, by rfl⟩ : syracuseStep 9457955 = 14186933) B14186933
theorem B6305303 : Blo 2213435 6305303 := bstep (se 1 (by rfl) ⟨4728977, by rfl⟩ : syracuseStep 6305303 = 9457955) B9457955
theorem B16814141 : Blo 2213435 16814141 := bstep (se 3 (by rfl) ⟨3152651, by rfl⟩ : syracuseStep 16814141 = 6305303) B6305303
theorem B11209427 : Blo 2213435 11209427 := bstep (se 1 (by rfl) ⟨8407070, by rfl⟩ : syracuseStep 11209427 = 16814141) B16814141
theorem B7472951 : Blo 2213435 7472951 := bstep (se 1 (by rfl) ⟨5604713, by rfl⟩ : syracuseStep 7472951 = 11209427) B11209427
theorem B4981967 : Blo 2213435 4981967 := bstep (se 1 (by rfl) ⟨3736475, by rfl⟩ : syracuseStep 4981967 = 7472951) B7472951
theorem B3321311 : Blo 2213435 3321311 := bstep (se 1 (by rfl) ⟨2490983, by rfl⟩ : syracuseStep 3321311 = 4981967) B4981967
theorem B2214207 : Blo 2213435 2214207 := bstep (se 1 (by rfl) ⟨1660655, by rfl⟩ : syracuseStep 2214207 = 3321311) B3321311
theorem B3321317 : Blo 2213435 3321317 := bbase (se 4 (by rfl) ⟨311373, by rfl⟩ : syracuseStep 3321317 = 622747) (by norm_num)
theorem B2214211 : Blo 2213435 2214211 := bstep (se 1 (by rfl) ⟨1660658, by rfl⟩ : syracuseStep 2214211 = 3321317) B3321317
theorem B3195677 : Blo 2213435 3195677 := bbase (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) (by norm_num)
theorem B8521805 : Blo 2213435 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B22724813 : Blo 2213435 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B60599501 : Blo 2213435 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B40399667 : Blo 2213435 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B26933111 : Blo 2213435 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B17955407 : Blo 2213435 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B11970271 : Blo 2213435 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B15960361 : Blo 2213435 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B21280481 : Blo 2213435 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B14186987 : Blo 2213435 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B9457991 : Blo 2213435 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B6305327 : Blo 2213435 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B4203551 : Blo 2213435 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B2802367 : Blo 2213435 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B3736489 : Blo 2213435 3736489 := bstep (se 2 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 3736489 = 2802367) B2802367
theorem B4981985 : Blo 2213435 4981985 := bstep (se 2 (by rfl) ⟨1868244, by rfl⟩ : syracuseStep 4981985 = 3736489) B3736489
theorem B3321323 : Blo 2213435 3321323 := bstep (se 1 (by rfl) ⟨2490992, by rfl⟩ : syracuseStep 3321323 = 4981985) B4981985
theorem B2214215 : Blo 2213435 2214215 := bstep (se 1 (by rfl) ⟨1660661, by rfl⟩ : syracuseStep 2214215 = 3321323) B3321323
theorem B2490997 : Blo 2213435 2490997 := bbase (se 5 (by rfl) ⟨116765, by rfl⟩ : syracuseStep 2490997 = 233531) (by norm_num)
theorem B3321329 : Blo 2213435 3321329 := bstep (se 2 (by rfl) ⟨1245498, by rfl⟩ : syracuseStep 3321329 = 2490997) B2490997
theorem B2214219 : Blo 2213435 2214219 := bstep (se 1 (by rfl) ⟨1660664, by rfl⟩ : syracuseStep 2214219 = 3321329) B3321329
theorem B2802377 : Blo 2213435 2802377 := bbase (se 2 (by rfl) ⟨1050891, by rfl⟩ : syracuseStep 2802377 = 2101783) (by norm_num)
theorem B7473005 : Blo 2213435 7473005 := bstep (se 3 (by rfl) ⟨1401188, by rfl⟩ : syracuseStep 7473005 = 2802377) B2802377
theorem B4982003 : Blo 2213435 4982003 := bstep (se 1 (by rfl) ⟨3736502, by rfl⟩ : syracuseStep 4982003 = 7473005) B7473005
theorem B3321335 : Blo 2213435 3321335 := bstep (se 1 (by rfl) ⟨2491001, by rfl⟩ : syracuseStep 3321335 = 4982003) B4982003
theorem B2214223 : Blo 2213435 2214223 := bstep (se 1 (by rfl) ⟨1660667, by rfl⟩ : syracuseStep 2214223 = 3321335) B3321335
theorem B3321341 : Blo 2213435 3321341 := bbase (se 3 (by rfl) ⟨622751, by rfl⟩ : syracuseStep 3321341 = 1245503) (by norm_num)
theorem B2214227 : Blo 2213435 2214227 := bstep (se 1 (by rfl) ⟨1660670, by rfl⟩ : syracuseStep 2214227 = 3321341) B3321341
theorem B4982021 : Blo 2213435 4982021 := bbase (se 4 (by rfl) ⟨467064, by rfl⟩ : syracuseStep 4982021 = 934129) (by norm_num)
theorem B3321347 : Blo 2213435 3321347 := bstep (se 1 (by rfl) ⟨2491010, by rfl⟩ : syracuseStep 3321347 = 4982021) B4982021
theorem B2214231 : Blo 2213435 2214231 := bstep (se 1 (by rfl) ⟨1660673, by rfl⟩ : syracuseStep 2214231 = 3321347) B3321347
theorem B4203589 : Blo 2213435 4203589 := bbase (se 4 (by rfl) ⟨394086, by rfl⟩ : syracuseStep 4203589 = 788173) (by norm_num)
theorem B5604785 : Blo 2213435 5604785 := bstep (se 2 (by rfl) ⟨2101794, by rfl⟩ : syracuseStep 5604785 = 4203589) B4203589
theorem B3736523 : Blo 2213435 3736523 := bstep (se 1 (by rfl) ⟨2802392, by rfl⟩ : syracuseStep 3736523 = 5604785) B5604785
theorem B2491015 : Blo 2213435 2491015 := bstep (se 1 (by rfl) ⟨1868261, by rfl⟩ : syracuseStep 2491015 = 3736523) B3736523
theorem B3321353 : Blo 2213435 3321353 := bstep (se 2 (by rfl) ⟨1245507, by rfl⟩ : syracuseStep 3321353 = 2491015) B2491015
theorem B2214235 : Blo 2213435 2214235 := bstep (se 1 (by rfl) ⟨1660676, by rfl⟩ : syracuseStep 2214235 = 3321353) B3321353
theorem B11209589 : Blo 2213435 11209589 := bbase (se 5 (by rfl) ⟨525449, by rfl⟩ : syracuseStep 11209589 = 1050899) (by norm_num)
theorem B7473059 : Blo 2213435 7473059 := bstep (se 1 (by rfl) ⟨5604794, by rfl⟩ : syracuseStep 7473059 = 11209589) B11209589
theorem B4982039 : Blo 2213435 4982039 := bstep (se 1 (by rfl) ⟨3736529, by rfl⟩ : syracuseStep 4982039 = 7473059) B7473059
theorem B3321359 : Blo 2213435 3321359 := bstep (se 1 (by rfl) ⟨2491019, by rfl⟩ : syracuseStep 3321359 = 4982039) B4982039
theorem B2214239 : Blo 2213435 2214239 := bstep (se 1 (by rfl) ⟨1660679, by rfl⟩ : syracuseStep 2214239 = 3321359) B3321359
theorem B3321365 : Blo 2213435 3321365 := bbase (se 6 (by rfl) ⟨77844, by rfl⟩ : syracuseStep 3321365 = 155689) (by norm_num)
theorem B2214243 : Blo 2213435 2214243 := bstep (se 1 (by rfl) ⟨1660682, by rfl⟩ : syracuseStep 2214243 = 3321365) B3321365
theorem B3595189 : Blo 2213435 3595189 := bbase (se 5 (by rfl) ⟨168524, by rfl⟩ : syracuseStep 3595189 = 337049) (by norm_num)
theorem B4793585 : Blo 2213435 4793585 := bstep (se 2 (by rfl) ⟨1797594, by rfl⟩ : syracuseStep 4793585 = 3595189) B3595189
theorem B12782893 : Blo 2213435 12782893 := bstep (se 3 (by rfl) ⟨2396792, by rfl⟩ : syracuseStep 12782893 = 4793585) B4793585
theorem B17043857 : Blo 2213435 17043857 := bstep (se 2 (by rfl) ⟨6391446, by rfl⟩ : syracuseStep 17043857 = 12782893) B12782893
theorem B11362571 : Blo 2213435 11362571 := bstep (se 1 (by rfl) ⟨8521928, by rfl⟩ : syracuseStep 11362571 = 17043857) B17043857
theorem B7575047 : Blo 2213435 7575047 := bstep (se 1 (by rfl) ⟨5681285, by rfl⟩ : syracuseStep 7575047 = 11362571) B11362571
theorem B5050031 : Blo 2213435 5050031 := bstep (se 1 (by rfl) ⟨3787523, by rfl⟩ : syracuseStep 5050031 = 7575047) B7575047
theorem B13466749 : Blo 2213435 13466749 := bstep (se 3 (by rfl) ⟨2525015, by rfl⟩ : syracuseStep 13466749 = 5050031) B5050031
theorem B17955665 : Blo 2213435 17955665 := bstep (se 2 (by rfl) ⟨6733374, by rfl⟩ : syracuseStep 17955665 = 13466749) B13466749
theorem B11970443 : Blo 2213435 11970443 := bstep (se 1 (by rfl) ⟨8977832, by rfl⟩ : syracuseStep 11970443 = 17955665) B17955665
theorem B7980295 : Blo 2213435 7980295 := bstep (se 1 (by rfl) ⟨5985221, by rfl⟩ : syracuseStep 7980295 = 11970443) B11970443
theorem B10640393 : Blo 2213435 10640393 := bstep (se 2 (by rfl) ⟨3990147, by rfl⟩ : syracuseStep 10640393 = 7980295) B7980295
theorem B7093595 : Blo 2213435 7093595 := bstep (se 1 (by rfl) ⟨5320196, by rfl⟩ : syracuseStep 7093595 = 10640393) B10640393
theorem B18916253 : Blo 2213435 18916253 := bstep (se 3 (by rfl) ⟨3546797, by rfl⟩ : syracuseStep 18916253 = 7093595) B7093595
theorem B12610835 : Blo 2213435 12610835 := bstep (se 1 (by rfl) ⟨9458126, by rfl⟩ : syracuseStep 12610835 = 18916253) B18916253
theorem B8407223 : Blo 2213435 8407223 := bstep (se 1 (by rfl) ⟨6305417, by rfl⟩ : syracuseStep 8407223 = 12610835) B12610835
theorem B5604815 : Blo 2213435 5604815 := bstep (se 1 (by rfl) ⟨4203611, by rfl⟩ : syracuseStep 5604815 = 8407223) B8407223
theorem B3736543 : Blo 2213435 3736543 := bstep (se 1 (by rfl) ⟨2802407, by rfl⟩ : syracuseStep 3736543 = 5604815) B5604815
theorem B4982057 : Blo 2213435 4982057 := bstep (se 2 (by rfl) ⟨1868271, by rfl⟩ : syracuseStep 4982057 = 3736543) B3736543
theorem B3321371 : Blo 2213435 3321371 := bstep (se 1 (by rfl) ⟨2491028, by rfl⟩ : syracuseStep 3321371 = 4982057) B4982057
theorem B2214247 : Blo 2213435 2214247 := bstep (se 1 (by rfl) ⟨1660685, by rfl⟩ : syracuseStep 2214247 = 3321371) B3321371
theorem B2491033 : Blo 2213435 2491033 := bbase (se 2 (by rfl) ⟨934137, by rfl⟩ : syracuseStep 2491033 = 1868275) (by norm_num)
theorem B3321377 : Blo 2213435 3321377 := bstep (se 2 (by rfl) ⟨1245516, by rfl⟩ : syracuseStep 3321377 = 2491033) B2491033
theorem B2214251 : Blo 2213435 2214251 := bstep (se 1 (by rfl) ⟨1660688, by rfl⟩ : syracuseStep 2214251 = 3321377) B3321377
theorem B8407253 : Blo 2213435 8407253 := bbase (se 7 (by rfl) ⟨98522, by rfl⟩ : syracuseStep 8407253 = 197045) (by norm_num)
theorem B5604835 : Blo 2213435 5604835 := bstep (se 1 (by rfl) ⟨4203626, by rfl⟩ : syracuseStep 5604835 = 8407253) B8407253
theorem B7473113 : Blo 2213435 7473113 := bstep (se 2 (by rfl) ⟨2802417, by rfl⟩ : syracuseStep 7473113 = 5604835) B5604835
theorem B4982075 : Blo 2213435 4982075 := bstep (se 1 (by rfl) ⟨3736556, by rfl⟩ : syracuseStep 4982075 = 7473113) B7473113
theorem B3321383 : Blo 2213435 3321383 := bstep (se 1 (by rfl) ⟨2491037, by rfl⟩ : syracuseStep 3321383 = 4982075) B4982075
theorem B2214255 : Blo 2213435 2214255 := bstep (se 1 (by rfl) ⟨1660691, by rfl⟩ : syracuseStep 2214255 = 3321383) B3321383
theorem B3321389 : Blo 2213435 3321389 := bbase (se 3 (by rfl) ⟨622760, by rfl⟩ : syracuseStep 3321389 = 1245521) (by norm_num)
theorem B2214259 : Blo 2213435 2214259 := bstep (se 1 (by rfl) ⟨1660694, by rfl⟩ : syracuseStep 2214259 = 3321389) B3321389
theorem B4982093 : Blo 2213435 4982093 := bbase (se 3 (by rfl) ⟨934142, by rfl⟩ : syracuseStep 4982093 = 1868285) (by norm_num)
theorem B3321395 : Blo 2213435 3321395 := bstep (se 1 (by rfl) ⟨2491046, by rfl⟩ : syracuseStep 3321395 = 4982093) B4982093
theorem B2214263 : Blo 2213435 2214263 := bstep (se 1 (by rfl) ⟨1660697, by rfl⟩ : syracuseStep 2214263 = 3321395) B3321395
theorem B2802433 : Blo 2213435 2802433 := bbase (se 2 (by rfl) ⟨1050912, by rfl⟩ : syracuseStep 2802433 = 2101825) (by norm_num)
theorem B3736577 : Blo 2213435 3736577 := bstep (se 2 (by rfl) ⟨1401216, by rfl⟩ : syracuseStep 3736577 = 2802433) B2802433
theorem B2491051 : Blo 2213435 2491051 := bstep (se 1 (by rfl) ⟨1868288, by rfl⟩ : syracuseStep 2491051 = 3736577) B3736577
theorem B3321401 : Blo 2213435 3321401 := bstep (se 2 (by rfl) ⟨1245525, by rfl⟩ : syracuseStep 3321401 = 2491051) B2491051
theorem B2214267 : Blo 2213435 2214267 := bstep (se 1 (by rfl) ⟨1660700, by rfl⟩ : syracuseStep 2214267 = 3321401) B3321401
theorem B2364557 : Blo 2213435 2364557 := bbase (se 3 (by rfl) ⟨443354, by rfl⟩ : syracuseStep 2364557 = 886709) (by norm_num)
theorem B25221941 : Blo 2213435 25221941 := bstep (se 5 (by rfl) ⟨1182278, by rfl⟩ : syracuseStep 25221941 = 2364557) B2364557
theorem B16814627 : Blo 2213435 16814627 := bstep (se 1 (by rfl) ⟨12610970, by rfl⟩ : syracuseStep 16814627 = 25221941) B25221941
theorem B11209751 : Blo 2213435 11209751 := bstep (se 1 (by rfl) ⟨8407313, by rfl⟩ : syracuseStep 11209751 = 16814627) B16814627
theorem B7473167 : Blo 2213435 7473167 := bstep (se 1 (by rfl) ⟨5604875, by rfl⟩ : syracuseStep 7473167 = 11209751) B11209751
theorem B4982111 : Blo 2213435 4982111 := bstep (se 1 (by rfl) ⟨3736583, by rfl⟩ : syracuseStep 4982111 = 7473167) B7473167
theorem B3321407 : Blo 2213435 3321407 := bstep (se 1 (by rfl) ⟨2491055, by rfl⟩ : syracuseStep 3321407 = 4982111) B4982111
theorem B2214271 : Blo 2213435 2214271 := bstep (se 1 (by rfl) ⟨1660703, by rfl⟩ : syracuseStep 2214271 = 3321407) B3321407
theorem B3321413 : Blo 2213435 3321413 := bbase (se 4 (by rfl) ⟨311382, by rfl⟩ : syracuseStep 3321413 = 622765) (by norm_num)
theorem B2214275 : Blo 2213435 2214275 := bstep (se 1 (by rfl) ⟨1660706, by rfl⟩ : syracuseStep 2214275 = 3321413) B3321413
theorem B3736597 : Blo 2213435 3736597 := bbase (se 6 (by rfl) ⟨87576, by rfl⟩ : syracuseStep 3736597 = 175153) (by norm_num)
theorem B4982129 : Blo 2213435 4982129 := bstep (se 2 (by rfl) ⟨1868298, by rfl⟩ : syracuseStep 4982129 = 3736597) B3736597
theorem B3321419 : Blo 2213435 3321419 := bstep (se 1 (by rfl) ⟨2491064, by rfl⟩ : syracuseStep 3321419 = 4982129) B4982129
theorem B2214279 : Blo 2213435 2214279 := bstep (se 1 (by rfl) ⟨1660709, by rfl⟩ : syracuseStep 2214279 = 3321419) B3321419
theorem B2491069 : Blo 2213435 2491069 := bbase (se 3 (by rfl) ⟨467075, by rfl⟩ : syracuseStep 2491069 = 934151) (by norm_num)
theorem B3321425 : Blo 2213435 3321425 := bstep (se 2 (by rfl) ⟨1245534, by rfl⟩ : syracuseStep 3321425 = 2491069) B2491069
theorem B2214283 : Blo 2213435 2214283 := bstep (se 1 (by rfl) ⟨1660712, by rfl⟩ : syracuseStep 2214283 = 3321425) B3321425
theorem B7473221 : Blo 2213435 7473221 := bbase (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) (by norm_num)
theorem B4982147 : Blo 2213435 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B3321431 : Blo 2213435 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B2214287 : Blo 2213435 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B3321437 : Blo 2213435 3321437 := bbase (se 3 (by rfl) ⟨622769, by rfl⟩ : syracuseStep 3321437 = 1245539) (by norm_num)
theorem B2214291 : Blo 2213435 2214291 := bstep (se 1 (by rfl) ⟨1660718, by rfl⟩ : syracuseStep 2214291 = 3321437) B3321437
theorem B4982165 : Blo 2213435 4982165 := bbase (se 6 (by rfl) ⟨116769, by rfl⟩ : syracuseStep 4982165 = 233539) (by norm_num)
theorem B3321443 : Blo 2213435 3321443 := bstep (se 1 (by rfl) ⟨2491082, by rfl⟩ : syracuseStep 3321443 = 4982165) B4982165
theorem B2214295 : Blo 2213435 2214295 := bstep (se 1 (by rfl) ⟨1660721, by rfl⟩ : syracuseStep 2214295 = 3321443) B3321443
theorem B10640645 : Blo 2213435 10640645 := bbase (se 4 (by rfl) ⟨997560, by rfl⟩ : syracuseStep 10640645 = 1995121) (by norm_num)
theorem B7093763 : Blo 2213435 7093763 := bstep (se 1 (by rfl) ⟨5320322, by rfl⟩ : syracuseStep 7093763 = 10640645) B10640645
theorem B4729175 : Blo 2213435 4729175 := bstep (se 1 (by rfl) ⟨3546881, by rfl⟩ : syracuseStep 4729175 = 7093763) B7093763
theorem B3152783 : Blo 2213435 3152783 := bstep (se 1 (by rfl) ⟨2364587, by rfl⟩ : syracuseStep 3152783 = 4729175) B4729175
theorem B8407421 : Blo 2213435 8407421 := bstep (se 3 (by rfl) ⟨1576391, by rfl⟩ : syracuseStep 8407421 = 3152783) B3152783
theorem B5604947 : Blo 2213435 5604947 := bstep (se 1 (by rfl) ⟨4203710, by rfl⟩ : syracuseStep 5604947 = 8407421) B8407421
theorem B3736631 : Blo 2213435 3736631 := bstep (se 1 (by rfl) ⟨2802473, by rfl⟩ : syracuseStep 3736631 = 5604947) B5604947
theorem B2491087 : Blo 2213435 2491087 := bstep (se 1 (by rfl) ⟨1868315, by rfl⟩ : syracuseStep 2491087 = 3736631) B3736631
theorem B3321449 : Blo 2213435 3321449 := bstep (se 2 (by rfl) ⟨1245543, by rfl⟩ : syracuseStep 3321449 = 2491087) B2491087
theorem B2214299 : Blo 2213435 2214299 := bstep (se 1 (by rfl) ⟨1660724, by rfl⟩ : syracuseStep 2214299 = 3321449) B3321449
theorem B3366773 : Blo 2213435 3366773 := bbase (se 5 (by rfl) ⟨157817, by rfl⟩ : syracuseStep 3366773 = 315635) (by norm_num)
theorem B2244515 : Blo 2213435 2244515 := bstep (se 1 (by rfl) ⟨1683386, by rfl⟩ : syracuseStep 2244515 = 3366773) B3366773
theorem B5985373 : Blo 2213435 5985373 := bstep (se 3 (by rfl) ⟨1122257, by rfl⟩ : syracuseStep 5985373 = 2244515) B2244515
theorem B7980497 : Blo 2213435 7980497 := bstep (se 2 (by rfl) ⟨2992686, by rfl⟩ : syracuseStep 7980497 = 5985373) B5985373
theorem B5320331 : Blo 2213435 5320331 := bstep (se 1 (by rfl) ⟨3990248, by rfl⟩ : syracuseStep 5320331 = 7980497) B7980497
theorem B3546887 : Blo 2213435 3546887 := bstep (se 1 (by rfl) ⟨2660165, by rfl⟩ : syracuseStep 3546887 = 5320331) B5320331
theorem B9458365 : Blo 2213435 9458365 := bstep (se 3 (by rfl) ⟨1773443, by rfl⟩ : syracuseStep 9458365 = 3546887) B3546887
theorem B12611153 : Blo 2213435 12611153 := bstep (se 2 (by rfl) ⟨4729182, by rfl⟩ : syracuseStep 12611153 = 9458365) B9458365
theorem B8407435 : Blo 2213435 8407435 := bstep (se 1 (by rfl) ⟨6305576, by rfl⟩ : syracuseStep 8407435 = 12611153) B12611153
theorem B11209913 : Blo 2213435 11209913 := bstep (se 2 (by rfl) ⟨4203717, by rfl⟩ : syracuseStep 11209913 = 8407435) B8407435
theorem B7473275 : Blo 2213435 7473275 := bstep (se 1 (by rfl) ⟨5604956, by rfl⟩ : syracuseStep 7473275 = 11209913) B11209913
theorem B4982183 : Blo 2213435 4982183 := bstep (se 1 (by rfl) ⟨3736637, by rfl⟩ : syracuseStep 4982183 = 7473275) B7473275
theorem B3321455 : Blo 2213435 3321455 := bstep (se 1 (by rfl) ⟨2491091, by rfl⟩ : syracuseStep 3321455 = 4982183) B4982183
theorem B2214303 : Blo 2213435 2214303 := bstep (se 1 (by rfl) ⟨1660727, by rfl⟩ : syracuseStep 2214303 = 3321455) B3321455
theorem B3321461 : Blo 2213435 3321461 := bbase (se 5 (by rfl) ⟨155693, by rfl⟩ : syracuseStep 3321461 = 311387) (by norm_num)
theorem B2214307 : Blo 2213435 2214307 := bstep (se 1 (by rfl) ⟨1660730, by rfl⟩ : syracuseStep 2214307 = 3321461) B3321461
theorem B4203733 : Blo 2213435 4203733 := bbase (se 7 (by rfl) ⟨49262, by rfl⟩ : syracuseStep 4203733 = 98525) (by norm_num)
theorem B5604977 : Blo 2213435 5604977 := bstep (se 2 (by rfl) ⟨2101866, by rfl⟩ : syracuseStep 5604977 = 4203733) B4203733
theorem B3736651 : Blo 2213435 3736651 := bstep (se 1 (by rfl) ⟨2802488, by rfl⟩ : syracuseStep 3736651 = 5604977) B5604977
theorem B4982201 : Blo 2213435 4982201 := bstep (se 2 (by rfl) ⟨1868325, by rfl⟩ : syracuseStep 4982201 = 3736651) B3736651
theorem B3321467 : Blo 2213435 3321467 := bstep (se 1 (by rfl) ⟨2491100, by rfl⟩ : syracuseStep 3321467 = 4982201) B4982201
theorem B2214311 : Blo 2213435 2214311 := bstep (se 1 (by rfl) ⟨1660733, by rfl⟩ : syracuseStep 2214311 = 3321467) B3321467
theorem B2491105 : Blo 2213435 2491105 := bbase (se 2 (by rfl) ⟨934164, by rfl⟩ : syracuseStep 2491105 = 1868329) (by norm_num)
theorem B3321473 : Blo 2213435 3321473 := bstep (se 2 (by rfl) ⟨1245552, by rfl⟩ : syracuseStep 3321473 = 2491105) B2491105
theorem B2214315 : Blo 2213435 2214315 := bstep (se 1 (by rfl) ⟨1660736, by rfl⟩ : syracuseStep 2214315 = 3321473) B3321473
theorem B5604997 : Blo 2213435 5604997 := bbase (se 4 (by rfl) ⟨525468, by rfl⟩ : syracuseStep 5604997 = 1050937) (by norm_num)
theorem B7473329 : Blo 2213435 7473329 := bstep (se 2 (by rfl) ⟨2802498, by rfl⟩ : syracuseStep 7473329 = 5604997) B5604997
theorem B4982219 : Blo 2213435 4982219 := bstep (se 1 (by rfl) ⟨3736664, by rfl⟩ : syracuseStep 4982219 = 7473329) B7473329
theorem B3321479 : Blo 2213435 3321479 := bstep (se 1 (by rfl) ⟨2491109, by rfl⟩ : syracuseStep 3321479 = 4982219) B4982219
theorem B2214319 : Blo 2213435 2214319 := bstep (se 1 (by rfl) ⟨1660739, by rfl⟩ : syracuseStep 2214319 = 3321479) B3321479
theorem B3321485 : Blo 2213435 3321485 := bbase (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) (by norm_num)
theorem B2214323 : Blo 2213435 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B4982237 : Blo 2213435 4982237 := bbase (se 3 (by rfl) ⟨934169, by rfl⟩ : syracuseStep 4982237 = 1868339) (by norm_num)
theorem B3321491 : Blo 2213435 3321491 := bstep (se 1 (by rfl) ⟨2491118, by rfl⟩ : syracuseStep 3321491 = 4982237) B4982237
theorem B2214327 : Blo 2213435 2214327 := bstep (se 1 (by rfl) ⟨1660745, by rfl⟩ : syracuseStep 2214327 = 3321491) B3321491
theorem B3736685 : Blo 2213435 3736685 := bbase (se 3 (by rfl) ⟨700628, by rfl⟩ : syracuseStep 3736685 = 1401257) (by norm_num)
theorem B2491123 : Blo 2213435 2491123 := bstep (se 1 (by rfl) ⟨1868342, by rfl⟩ : syracuseStep 2491123 = 3736685) B3736685
theorem B3321497 : Blo 2213435 3321497 := bstep (se 2 (by rfl) ⟨1245561, by rfl⟩ : syracuseStep 3321497 = 2491123) B2491123
theorem B2214331 : Blo 2213435 2214331 := bstep (se 1 (by rfl) ⟨1660748, by rfl⟩ : syracuseStep 2214331 = 3321497) B3321497
theorem B3366821 : Blo 2213435 3366821 := bbase (se 4 (by rfl) ⟨315639, by rfl⟩ : syracuseStep 3366821 = 631279) (by norm_num)
theorem B2244547 : Blo 2213435 2244547 := bstep (se 1 (by rfl) ⟨1683410, by rfl⟩ : syracuseStep 2244547 = 3366821) B3366821
theorem B11970917 : Blo 2213435 11970917 := bstep (se 4 (by rfl) ⟨1122273, by rfl⟩ : syracuseStep 11970917 = 2244547) B2244547
theorem B7980611 : Blo 2213435 7980611 := bstep (se 1 (by rfl) ⟨5985458, by rfl⟩ : syracuseStep 7980611 = 11970917) B11970917
theorem B21281629 : Blo 2213435 21281629 := bstep (se 3 (by rfl) ⟨3990305, by rfl⟩ : syracuseStep 21281629 = 7980611) B7980611
theorem B28375505 : Blo 2213435 28375505 := bstep (se 2 (by rfl) ⟨10640814, by rfl⟩ : syracuseStep 28375505 = 21281629) B21281629
theorem B18917003 : Blo 2213435 18917003 := bstep (se 1 (by rfl) ⟨14187752, by rfl⟩ : syracuseStep 18917003 = 28375505) B28375505
theorem B12611335 : Blo 2213435 12611335 := bstep (se 1 (by rfl) ⟨9458501, by rfl⟩ : syracuseStep 12611335 = 18917003) B18917003
theorem B16815113 : Blo 2213435 16815113 := bstep (se 2 (by rfl) ⟨6305667, by rfl⟩ : syracuseStep 16815113 = 12611335) B12611335
theorem B11210075 : Blo 2213435 11210075 := bstep (se 1 (by rfl) ⟨8407556, by rfl⟩ : syracuseStep 11210075 = 16815113) B16815113
theorem B7473383 : Blo 2213435 7473383 := bstep (se 1 (by rfl) ⟨5605037, by rfl⟩ : syracuseStep 7473383 = 11210075) B11210075
theorem B4982255 : Blo 2213435 4982255 := bstep (se 1 (by rfl) ⟨3736691, by rfl⟩ : syracuseStep 4982255 = 7473383) B7473383
theorem B3321503 : Blo 2213435 3321503 := bstep (se 1 (by rfl) ⟨2491127, by rfl⟩ : syracuseStep 3321503 = 4982255) B4982255
theorem B2214335 : Blo 2213435 2214335 := bstep (se 1 (by rfl) ⟨1660751, by rfl⟩ : syracuseStep 2214335 = 3321503) B3321503
theorem B3321509 : Blo 2213435 3321509 := bbase (se 4 (by rfl) ⟨311391, by rfl⟩ : syracuseStep 3321509 = 622783) (by norm_num)
theorem B2214339 : Blo 2213435 2214339 := bstep (se 1 (by rfl) ⟨1660754, by rfl⟩ : syracuseStep 2214339 = 3321509) B3321509
theorem B2802529 : Blo 2213435 2802529 := bbase (se 2 (by rfl) ⟨1050948, by rfl⟩ : syracuseStep 2802529 = 2101897) (by norm_num)
theorem B3736705 : Blo 2213435 3736705 := bstep (se 2 (by rfl) ⟨1401264, by rfl⟩ : syracuseStep 3736705 = 2802529) B2802529
theorem B4982273 : Blo 2213435 4982273 := bstep (se 2 (by rfl) ⟨1868352, by rfl⟩ : syracuseStep 4982273 = 3736705) B3736705
theorem B3321515 : Blo 2213435 3321515 := bstep (se 1 (by rfl) ⟨2491136, by rfl⟩ : syracuseStep 3321515 = 4982273) B4982273
theorem B2214343 : Blo 2213435 2214343 := bstep (se 1 (by rfl) ⟨1660757, by rfl⟩ : syracuseStep 2214343 = 3321515) B3321515
theorem B2491141 : Blo 2213435 2491141 := bbase (se 4 (by rfl) ⟨233544, by rfl⟩ : syracuseStep 2491141 = 467089) (by norm_num)
theorem B3321521 : Blo 2213435 3321521 := bstep (se 2 (by rfl) ⟨1245570, by rfl⟩ : syracuseStep 3321521 = 2491141) B2491141
theorem B2214347 : Blo 2213435 2214347 := bstep (se 1 (by rfl) ⟨1660760, by rfl⟩ : syracuseStep 2214347 = 3321521) B3321521
theorem B3546965 : Blo 2213435 3546965 := bbase (se 9 (by rfl) ⟨10391, by rfl⟩ : syracuseStep 3546965 = 20783) (by norm_num)
theorem B2364643 : Blo 2213435 2364643 := bstep (se 1 (by rfl) ⟨1773482, by rfl⟩ : syracuseStep 2364643 = 3546965) B3546965
theorem B3152857 : Blo 2213435 3152857 := bstep (se 2 (by rfl) ⟨1182321, by rfl⟩ : syracuseStep 3152857 = 2364643) B2364643
theorem B4203809 : Blo 2213435 4203809 := bstep (se 2 (by rfl) ⟨1576428, by rfl⟩ : syracuseStep 4203809 = 3152857) B3152857
theorem B2802539 : Blo 2213435 2802539 := bstep (se 1 (by rfl) ⟨2101904, by rfl⟩ : syracuseStep 2802539 = 4203809) B4203809
theorem B7473437 : Blo 2213435 7473437 := bstep (se 3 (by rfl) ⟨1401269, by rfl⟩ : syracuseStep 7473437 = 2802539) B2802539
theorem B4982291 : Blo 2213435 4982291 := bstep (se 1 (by rfl) ⟨3736718, by rfl⟩ : syracuseStep 4982291 = 7473437) B7473437
theorem B3321527 : Blo 2213435 3321527 := bstep (se 1 (by rfl) ⟨2491145, by rfl⟩ : syracuseStep 3321527 = 4982291) B4982291
theorem B2214351 : Blo 2213435 2214351 := bstep (se 1 (by rfl) ⟨1660763, by rfl⟩ : syracuseStep 2214351 = 3321527) B3321527
theorem B3321533 : Blo 2213435 3321533 := bbase (se 3 (by rfl) ⟨622787, by rfl⟩ : syracuseStep 3321533 = 1245575) (by norm_num)
theorem B2214355 : Blo 2213435 2214355 := bstep (se 1 (by rfl) ⟨1660766, by rfl⟩ : syracuseStep 2214355 = 3321533) B3321533
theorem B4982309 : Blo 2213435 4982309 := bbase (se 4 (by rfl) ⟨467091, by rfl⟩ : syracuseStep 4982309 = 934183) (by norm_num)
theorem B3321539 : Blo 2213435 3321539 := bstep (se 1 (by rfl) ⟨2491154, by rfl⟩ : syracuseStep 3321539 = 4982309) B4982309
theorem B2214359 : Blo 2213435 2214359 := bstep (se 1 (by rfl) ⟨1660769, by rfl⟩ : syracuseStep 2214359 = 3321539) B3321539
theorem B5605109 : Blo 2213435 5605109 := bbase (se 5 (by rfl) ⟨262739, by rfl⟩ : syracuseStep 5605109 = 525479) (by norm_num)
theorem B3736739 : Blo 2213435 3736739 := bstep (se 1 (by rfl) ⟨2802554, by rfl⟩ : syracuseStep 3736739 = 5605109) B5605109
theorem B2491159 : Blo 2213435 2491159 := bstep (se 1 (by rfl) ⟨1868369, by rfl⟩ : syracuseStep 2491159 = 3736739) B3736739
theorem B3321545 : Blo 2213435 3321545 := bstep (se 2 (by rfl) ⟨1245579, by rfl⟩ : syracuseStep 3321545 = 2491159) B2491159
theorem B2214363 : Blo 2213435 2214363 := bstep (se 1 (by rfl) ⟨1660772, by rfl⟩ : syracuseStep 2214363 = 3321545) B3321545
theorem B4793845 : Blo 2213435 4793845 := bbase (se 5 (by rfl) ⟨224711, by rfl⟩ : syracuseStep 4793845 = 449423) (by norm_num)
theorem B6391793 : Blo 2213435 6391793 := bstep (se 2 (by rfl) ⟨2396922, by rfl⟩ : syracuseStep 6391793 = 4793845) B4793845
theorem B4261195 : Blo 2213435 4261195 := bstep (se 1 (by rfl) ⟨3195896, by rfl⟩ : syracuseStep 4261195 = 6391793) B6391793
theorem B5681593 : Blo 2213435 5681593 := bstep (se 2 (by rfl) ⟨2130597, by rfl⟩ : syracuseStep 5681593 = 4261195) B4261195
theorem B7575457 : Blo 2213435 7575457 := bstep (se 2 (by rfl) ⟨2840796, by rfl⟩ : syracuseStep 7575457 = 5681593) B5681593
theorem B10100609 : Blo 2213435 10100609 := bstep (se 2 (by rfl) ⟨3787728, by rfl⟩ : syracuseStep 10100609 = 7575457) B7575457
theorem B6733739 : Blo 2213435 6733739 := bstep (se 1 (by rfl) ⟨5050304, by rfl⟩ : syracuseStep 6733739 = 10100609) B10100609
theorem B17956637 : Blo 2213435 17956637 := bstep (se 3 (by rfl) ⟨3366869, by rfl⟩ : syracuseStep 17956637 = 6733739) B6733739
theorem B11971091 : Blo 2213435 11971091 := bstep (se 1 (by rfl) ⟨8978318, by rfl⟩ : syracuseStep 11971091 = 17956637) B17956637
theorem B31922909 : Blo 2213435 31922909 := bstep (se 3 (by rfl) ⟨5985545, by rfl⟩ : syracuseStep 31922909 = 11971091) B11971091
theorem B21281939 : Blo 2213435 21281939 := bstep (se 1 (by rfl) ⟨15961454, by rfl⟩ : syracuseStep 21281939 = 31922909) B31922909
theorem B14187959 : Blo 2213435 14187959 := bstep (se 1 (by rfl) ⟨10640969, by rfl⟩ : syracuseStep 14187959 = 21281939) B21281939
theorem B9458639 : Blo 2213435 9458639 := bstep (se 1 (by rfl) ⟨7093979, by rfl⟩ : syracuseStep 9458639 = 14187959) B14187959
theorem B6305759 : Blo 2213435 6305759 := bstep (se 1 (by rfl) ⟨4729319, by rfl⟩ : syracuseStep 6305759 = 9458639) B9458639
theorem B4203839 : Blo 2213435 4203839 := bstep (se 1 (by rfl) ⟨3152879, by rfl⟩ : syracuseStep 4203839 = 6305759) B6305759
theorem B11210237 : Blo 2213435 11210237 := bstep (se 3 (by rfl) ⟨2101919, by rfl⟩ : syracuseStep 11210237 = 4203839) B4203839
theorem B7473491 : Blo 2213435 7473491 := bstep (se 1 (by rfl) ⟨5605118, by rfl⟩ : syracuseStep 7473491 = 11210237) B11210237
theorem B4982327 : Blo 2213435 4982327 := bstep (se 1 (by rfl) ⟨3736745, by rfl⟩ : syracuseStep 4982327 = 7473491) B7473491
theorem B3321551 : Blo 2213435 3321551 := bstep (se 1 (by rfl) ⟨2491163, by rfl⟩ : syracuseStep 3321551 = 4982327) B4982327
theorem B2214367 : Blo 2213435 2214367 := bstep (se 1 (by rfl) ⟨1660775, by rfl⟩ : syracuseStep 2214367 = 3321551) B3321551
theorem B3321557 : Blo 2213435 3321557 := bbase (se 7 (by rfl) ⟨38924, by rfl⟩ : syracuseStep 3321557 = 77849) (by norm_num)
theorem B2214371 : Blo 2213435 2214371 := bstep (se 1 (by rfl) ⟨1660778, by rfl⟩ : syracuseStep 2214371 = 3321557) B3321557
theorem B5050325 : Blo 2213435 5050325 := bbase (se 7 (by rfl) ⟨59183, by rfl⟩ : syracuseStep 5050325 = 118367) (by norm_num)
theorem B3366883 : Blo 2213435 3366883 := bstep (se 1 (by rfl) ⟨2525162, by rfl⟩ : syracuseStep 3366883 = 5050325) B5050325
theorem B4489177 : Blo 2213435 4489177 := bstep (se 2 (by rfl) ⟨1683441, by rfl⟩ : syracuseStep 4489177 = 3366883) B3366883
theorem B5985569 : Blo 2213435 5985569 := bstep (se 2 (by rfl) ⟨2244588, by rfl⟩ : syracuseStep 5985569 = 4489177) B4489177
theorem B3990379 : Blo 2213435 3990379 := bstep (se 1 (by rfl) ⟨2992784, by rfl⟩ : syracuseStep 3990379 = 5985569) B5985569
theorem B5320505 : Blo 2213435 5320505 := bstep (se 2 (by rfl) ⟨1995189, by rfl⟩ : syracuseStep 5320505 = 3990379) B3990379
theorem B3547003 : Blo 2213435 3547003 := bstep (se 1 (by rfl) ⟨2660252, by rfl⟩ : syracuseStep 3547003 = 5320505) B5320505
theorem B4729337 : Blo 2213435 4729337 := bstep (se 2 (by rfl) ⟨1773501, by rfl⟩ : syracuseStep 4729337 = 3547003) B3547003
theorem B3152891 : Blo 2213435 3152891 := bstep (se 1 (by rfl) ⟨2364668, by rfl⟩ : syracuseStep 3152891 = 4729337) B4729337
theorem B8407709 : Blo 2213435 8407709 := bstep (se 3 (by rfl) ⟨1576445, by rfl⟩ : syracuseStep 8407709 = 3152891) B3152891
theorem B5605139 : Blo 2213435 5605139 := bstep (se 1 (by rfl) ⟨4203854, by rfl⟩ : syracuseStep 5605139 = 8407709) B8407709
theorem B3736759 : Blo 2213435 3736759 := bstep (se 1 (by rfl) ⟨2802569, by rfl⟩ : syracuseStep 3736759 = 5605139) B5605139
theorem B4982345 : Blo 2213435 4982345 := bstep (se 2 (by rfl) ⟨1868379, by rfl⟩ : syracuseStep 4982345 = 3736759) B3736759
theorem B3321563 : Blo 2213435 3321563 := bstep (se 1 (by rfl) ⟨2491172, by rfl⟩ : syracuseStep 3321563 = 4982345) B4982345
theorem B2214375 : Blo 2213435 2214375 := bstep (se 1 (by rfl) ⟨1660781, by rfl⟩ : syracuseStep 2214375 = 3321563) B3321563
theorem B2491177 : Blo 2213435 2491177 := bbase (se 2 (by rfl) ⟨934191, by rfl⟩ : syracuseStep 2491177 = 1868383) (by norm_num)
theorem B3321569 : Blo 2213435 3321569 := bstep (se 2 (by rfl) ⟨1245588, by rfl⟩ : syracuseStep 3321569 = 2491177) B2491177
theorem B2214379 : Blo 2213435 2214379 := bstep (se 1 (by rfl) ⟨1660784, by rfl⟩ : syracuseStep 2214379 = 3321569) B3321569
theorem B5985589 : Blo 2213435 5985589 := bbase (se 5 (by rfl) ⟨280574, by rfl⟩ : syracuseStep 5985589 = 561149) (by norm_num)
theorem B7980785 : Blo 2213435 7980785 := bstep (se 2 (by rfl) ⟨2992794, by rfl⟩ : syracuseStep 7980785 = 5985589) B5985589
theorem B5320523 : Blo 2213435 5320523 := bstep (se 1 (by rfl) ⟨3990392, by rfl⟩ : syracuseStep 5320523 = 7980785) B7980785
theorem B14188061 : Blo 2213435 14188061 := bstep (se 3 (by rfl) ⟨2660261, by rfl⟩ : syracuseStep 14188061 = 5320523) B5320523
theorem B9458707 : Blo 2213435 9458707 := bstep (se 1 (by rfl) ⟨7094030, by rfl⟩ : syracuseStep 9458707 = 14188061) B14188061
theorem B12611609 : Blo 2213435 12611609 := bstep (se 2 (by rfl) ⟨4729353, by rfl⟩ : syracuseStep 12611609 = 9458707) B9458707
theorem B8407739 : Blo 2213435 8407739 := bstep (se 1 (by rfl) ⟨6305804, by rfl⟩ : syracuseStep 8407739 = 12611609) B12611609
theorem B5605159 : Blo 2213435 5605159 := bstep (se 1 (by rfl) ⟨4203869, by rfl⟩ : syracuseStep 5605159 = 8407739) B8407739
theorem B7473545 : Blo 2213435 7473545 := bstep (se 2 (by rfl) ⟨2802579, by rfl⟩ : syracuseStep 7473545 = 5605159) B5605159
theorem B4982363 : Blo 2213435 4982363 := bstep (se 1 (by rfl) ⟨3736772, by rfl⟩ : syracuseStep 4982363 = 7473545) B7473545
theorem B3321575 : Blo 2213435 3321575 := bstep (se 1 (by rfl) ⟨2491181, by rfl⟩ : syracuseStep 3321575 = 4982363) B4982363
theorem B2214383 : Blo 2213435 2214383 := bstep (se 1 (by rfl) ⟨1660787, by rfl⟩ : syracuseStep 2214383 = 3321575) B3321575
theorem B3321581 : Blo 2213435 3321581 := bbase (se 3 (by rfl) ⟨622796, by rfl⟩ : syracuseStep 3321581 = 1245593) (by norm_num)
theorem B2214387 : Blo 2213435 2214387 := bstep (se 1 (by rfl) ⟨1660790, by rfl⟩ : syracuseStep 2214387 = 3321581) B3321581
theorem B4982381 : Blo 2213435 4982381 := bbase (se 3 (by rfl) ⟨934196, by rfl⟩ : syracuseStep 4982381 = 1868393) (by norm_num)
theorem B3321587 : Blo 2213435 3321587 := bstep (se 1 (by rfl) ⟨2491190, by rfl⟩ : syracuseStep 3321587 = 4982381) B4982381
theorem B2214391 : Blo 2213435 2214391 := bstep (se 1 (by rfl) ⟨1660793, by rfl⟩ : syracuseStep 2214391 = 3321587) B3321587
theorem B4203893 : Blo 2213435 4203893 := bbase (se 5 (by rfl) ⟨197057, by rfl⟩ : syracuseStep 4203893 = 394115) (by norm_num)
theorem B2802595 : Blo 2213435 2802595 := bstep (se 1 (by rfl) ⟨2101946, by rfl⟩ : syracuseStep 2802595 = 4203893) B4203893
theorem B3736793 : Blo 2213435 3736793 := bstep (se 2 (by rfl) ⟨1401297, by rfl⟩ : syracuseStep 3736793 = 2802595) B2802595
theorem B2491195 : Blo 2213435 2491195 := bstep (se 1 (by rfl) ⟨1868396, by rfl⟩ : syracuseStep 2491195 = 3736793) B3736793
theorem B3321593 : Blo 2213435 3321593 := bstep (se 2 (by rfl) ⟨1245597, by rfl⟩ : syracuseStep 3321593 = 2491195) B2491195
theorem B2214395 : Blo 2213435 2214395 := bstep (se 1 (by rfl) ⟨1660796, by rfl⟩ : syracuseStep 2214395 = 3321593) B3321593
theorem B2840837 : Blo 2213435 2840837 := bbase (se 4 (by rfl) ⟨266328, by rfl⟩ : syracuseStep 2840837 = 532657) (by norm_num)
theorem B7575565 : Blo 2213435 7575565 := bstep (se 3 (by rfl) ⟨1420418, by rfl⟩ : syracuseStep 7575565 = 2840837) B2840837
theorem B10100753 : Blo 2213435 10100753 := bstep (se 2 (by rfl) ⟨3787782, by rfl⟩ : syracuseStep 10100753 = 7575565) B7575565
theorem B6733835 : Blo 2213435 6733835 := bstep (se 1 (by rfl) ⟨5050376, by rfl⟩ : syracuseStep 6733835 = 10100753) B10100753
theorem B71827573 : Blo 2213435 71827573 := bstep (se 5 (by rfl) ⟨3366917, by rfl⟩ : syracuseStep 71827573 = 6733835) B6733835
theorem B95770097 : Blo 2213435 95770097 := bstep (se 2 (by rfl) ⟨35913786, by rfl⟩ : syracuseStep 95770097 = 71827573) B71827573
theorem B63846731 : Blo 2213435 63846731 := bstep (se 1 (by rfl) ⟨47885048, by rfl⟩ : syracuseStep 63846731 = 95770097) B95770097
theorem B42564487 : Blo 2213435 42564487 := bstep (se 1 (by rfl) ⟨31923365, by rfl⟩ : syracuseStep 42564487 = 63846731) B63846731
theorem B56752649 : Blo 2213435 56752649 := bstep (se 2 (by rfl) ⟨21282243, by rfl⟩ : syracuseStep 56752649 = 42564487) B42564487
theorem B37835099 : Blo 2213435 37835099 := bstep (se 1 (by rfl) ⟨28376324, by rfl⟩ : syracuseStep 37835099 = 56752649) B56752649
theorem B25223399 : Blo 2213435 25223399 := bstep (se 1 (by rfl) ⟨18917549, by rfl⟩ : syracuseStep 25223399 = 37835099) B37835099
theorem B16815599 : Blo 2213435 16815599 := bstep (se 1 (by rfl) ⟨12611699, by rfl⟩ : syracuseStep 16815599 = 25223399) B25223399
theorem B11210399 : Blo 2213435 11210399 := bstep (se 1 (by rfl) ⟨8407799, by rfl⟩ : syracuseStep 11210399 = 16815599) B16815599
theorem B7473599 : Blo 2213435 7473599 := bstep (se 1 (by rfl) ⟨5605199, by rfl⟩ : syracuseStep 7473599 = 11210399) B11210399
theorem B4982399 : Blo 2213435 4982399 := bstep (se 1 (by rfl) ⟨3736799, by rfl⟩ : syracuseStep 4982399 = 7473599) B7473599
theorem B3321599 : Blo 2213435 3321599 := bstep (se 1 (by rfl) ⟨2491199, by rfl⟩ : syracuseStep 3321599 = 4982399) B4982399
theorem B2214399 : Blo 2213435 2214399 := bstep (se 1 (by rfl) ⟨1660799, by rfl⟩ : syracuseStep 2214399 = 3321599) B3321599
theorem B3321605 : Blo 2213435 3321605 := bbase (se 4 (by rfl) ⟨311400, by rfl⟩ : syracuseStep 3321605 = 622801) (by norm_num)
theorem B2214403 : Blo 2213435 2214403 := bstep (se 1 (by rfl) ⟨1660802, by rfl⟩ : syracuseStep 2214403 = 3321605) B3321605
theorem B3736813 : Blo 2213435 3736813 := bbase (se 3 (by rfl) ⟨700652, by rfl⟩ : syracuseStep 3736813 = 1401305) (by norm_num)
theorem B4982417 : Blo 2213435 4982417 := bstep (se 2 (by rfl) ⟨1868406, by rfl⟩ : syracuseStep 4982417 = 3736813) B3736813
theorem B3321611 : Blo 2213435 3321611 := bstep (se 1 (by rfl) ⟨2491208, by rfl⟩ : syracuseStep 3321611 = 4982417) B4982417
theorem B2214407 : Blo 2213435 2214407 := bstep (se 1 (by rfl) ⟨1660805, by rfl⟩ : syracuseStep 2214407 = 3321611) B3321611
theorem B2491213 : Blo 2213435 2491213 := bbase (se 3 (by rfl) ⟨467102, by rfl⟩ : syracuseStep 2491213 = 934205) (by norm_num)
theorem B3321617 : Blo 2213435 3321617 := bstep (se 2 (by rfl) ⟨1245606, by rfl⟩ : syracuseStep 3321617 = 2491213) B2491213
theorem B2214411 : Blo 2213435 2214411 := bstep (se 1 (by rfl) ⟨1660808, by rfl⟩ : syracuseStep 2214411 = 3321617) B3321617
theorem B7473653 : Blo 2213435 7473653 := bbase (se 5 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 7473653 = 700655) (by norm_num)
theorem B4982435 : Blo 2213435 4982435 := bstep (se 1 (by rfl) ⟨3736826, by rfl⟩ : syracuseStep 4982435 = 7473653) B7473653
theorem B3321623 : Blo 2213435 3321623 := bstep (se 1 (by rfl) ⟨2491217, by rfl⟩ : syracuseStep 3321623 = 4982435) B4982435
theorem B2214415 : Blo 2213435 2214415 := bstep (se 1 (by rfl) ⟨1660811, by rfl⟩ : syracuseStep 2214415 = 3321623) B3321623
theorem B3321629 : Blo 2213435 3321629 := bbase (se 3 (by rfl) ⟨622805, by rfl⟩ : syracuseStep 3321629 = 1245611) (by norm_num)
theorem B2214419 : Blo 2213435 2214419 := bstep (se 1 (by rfl) ⟨1660814, by rfl⟩ : syracuseStep 2214419 = 3321629) B3321629
theorem B4982453 : Blo 2213435 4982453 := bbase (se 5 (by rfl) ⟨233552, by rfl⟩ : syracuseStep 4982453 = 467105) (by norm_num)
theorem B3321635 : Blo 2213435 3321635 := bstep (se 1 (by rfl) ⟨2491226, by rfl⟩ : syracuseStep 3321635 = 4982453) B4982453
theorem B2214423 : Blo 2213435 2214423 := bstep (se 1 (by rfl) ⟨1660817, by rfl⟩ : syracuseStep 2214423 = 3321635) B3321635
theorem B12611861 : Blo 2213435 12611861 := bbase (se 6 (by rfl) ⟨295590, by rfl⟩ : syracuseStep 12611861 = 591181) (by norm_num)
theorem B8407907 : Blo 2213435 8407907 := bstep (se 1 (by rfl) ⟨6305930, by rfl⟩ : syracuseStep 8407907 = 12611861) B12611861
theorem B5605271 : Blo 2213435 5605271 := bstep (se 1 (by rfl) ⟨4203953, by rfl⟩ : syracuseStep 5605271 = 8407907) B8407907
theorem B3736847 : Blo 2213435 3736847 := bstep (se 1 (by rfl) ⟨2802635, by rfl⟩ : syracuseStep 3736847 = 5605271) B5605271
theorem B2491231 : Blo 2213435 2491231 := bstep (se 1 (by rfl) ⟨1868423, by rfl⟩ : syracuseStep 2491231 = 3736847) B3736847
theorem B3321641 : Blo 2213435 3321641 := bstep (se 2 (by rfl) ⟨1245615, by rfl⟩ : syracuseStep 3321641 = 2491231) B2491231
theorem B2214427 : Blo 2213435 2214427 := bstep (se 1 (by rfl) ⟨1660820, by rfl⟩ : syracuseStep 2214427 = 3321641) B3321641
theorem B6305941 : Blo 2213435 6305941 := bbase (se 6 (by rfl) ⟨147795, by rfl⟩ : syracuseStep 6305941 = 295591) (by norm_num)
theorem B8407921 : Blo 2213435 8407921 := bstep (se 2 (by rfl) ⟨3152970, by rfl⟩ : syracuseStep 8407921 = 6305941) B6305941
theorem B11210561 : Blo 2213435 11210561 := bstep (se 2 (by rfl) ⟨4203960, by rfl⟩ : syracuseStep 11210561 = 8407921) B8407921
theorem B7473707 : Blo 2213435 7473707 := bstep (se 1 (by rfl) ⟨5605280, by rfl⟩ : syracuseStep 7473707 = 11210561) B11210561
theorem B4982471 : Blo 2213435 4982471 := bstep (se 1 (by rfl) ⟨3736853, by rfl⟩ : syracuseStep 4982471 = 7473707) B7473707
theorem B3321647 : Blo 2213435 3321647 := bstep (se 1 (by rfl) ⟨2491235, by rfl⟩ : syracuseStep 3321647 = 4982471) B4982471
theorem B2214431 : Blo 2213435 2214431 := bstep (se 1 (by rfl) ⟨1660823, by rfl⟩ : syracuseStep 2214431 = 3321647) B3321647
theorem B3321653 : Blo 2213435 3321653 := bbase (se 5 (by rfl) ⟨155702, by rfl⟩ : syracuseStep 3321653 = 311405) (by norm_num)
theorem B2214435 : Blo 2213435 2214435 := bstep (se 1 (by rfl) ⟨1660826, by rfl⟩ : syracuseStep 2214435 = 3321653) B3321653
theorem B5605301 : Blo 2213435 5605301 := bbase (se 5 (by rfl) ⟨262748, by rfl⟩ : syracuseStep 5605301 = 525497) (by norm_num)
theorem B3736867 : Blo 2213435 3736867 := bstep (se 1 (by rfl) ⟨2802650, by rfl⟩ : syracuseStep 3736867 = 5605301) B5605301
theorem B4982489 : Blo 2213435 4982489 := bstep (se 2 (by rfl) ⟨1868433, by rfl⟩ : syracuseStep 4982489 = 3736867) B3736867
theorem B3321659 : Blo 2213435 3321659 := bstep (se 1 (by rfl) ⟨2491244, by rfl⟩ : syracuseStep 3321659 = 4982489) B4982489
theorem B2214439 : Blo 2213435 2214439 := bstep (se 1 (by rfl) ⟨1660829, by rfl⟩ : syracuseStep 2214439 = 3321659) B3321659
theorem B2491249 : Blo 2213435 2491249 := bbase (se 2 (by rfl) ⟨934218, by rfl⟩ : syracuseStep 2491249 = 1868437) (by norm_num)
theorem B3321665 : Blo 2213435 3321665 := bstep (se 2 (by rfl) ⟨1245624, by rfl⟩ : syracuseStep 3321665 = 2491249) B2491249
theorem B2214443 : Blo 2213435 2214443 := bstep (se 1 (by rfl) ⟨1660832, by rfl⟩ : syracuseStep 2214443 = 3321665) B3321665
theorem B9458981 : Blo 2213435 9458981 := bbase (se 4 (by rfl) ⟨886779, by rfl⟩ : syracuseStep 9458981 = 1773559) (by norm_num)
theorem B6305987 : Blo 2213435 6305987 := bstep (se 1 (by rfl) ⟨4729490, by rfl⟩ : syracuseStep 6305987 = 9458981) B9458981
theorem B4203991 : Blo 2213435 4203991 := bstep (se 1 (by rfl) ⟨3152993, by rfl⟩ : syracuseStep 4203991 = 6305987) B6305987
theorem B5605321 : Blo 2213435 5605321 := bstep (se 2 (by rfl) ⟨2101995, by rfl⟩ : syracuseStep 5605321 = 4203991) B4203991
theorem B7473761 : Blo 2213435 7473761 := bstep (se 2 (by rfl) ⟨2802660, by rfl⟩ : syracuseStep 7473761 = 5605321) B5605321
theorem B4982507 : Blo 2213435 4982507 := bstep (se 1 (by rfl) ⟨3736880, by rfl⟩ : syracuseStep 4982507 = 7473761) B7473761
theorem B3321671 : Blo 2213435 3321671 := bstep (se 1 (by rfl) ⟨2491253, by rfl⟩ : syracuseStep 3321671 = 4982507) B4982507
theorem B2214447 : Blo 2213435 2214447 := bstep (se 1 (by rfl) ⟨1660835, by rfl⟩ : syracuseStep 2214447 = 3321671) B3321671
theorem B3321677 : Blo 2213435 3321677 := bbase (se 3 (by rfl) ⟨622814, by rfl⟩ : syracuseStep 3321677 = 1245629) (by norm_num)
theorem B2214451 : Blo 2213435 2214451 := bstep (se 1 (by rfl) ⟨1660838, by rfl⟩ : syracuseStep 2214451 = 3321677) B3321677
theorem B4982525 : Blo 2213435 4982525 := bbase (se 3 (by rfl) ⟨934223, by rfl⟩ : syracuseStep 4982525 = 1868447) (by norm_num)
theorem B3321683 : Blo 2213435 3321683 := bstep (se 1 (by rfl) ⟨2491262, by rfl⟩ : syracuseStep 3321683 = 4982525) B4982525
theorem B2214455 : Blo 2213435 2214455 := bstep (se 1 (by rfl) ⟨1660841, by rfl⟩ : syracuseStep 2214455 = 3321683) B3321683
theorem B3736901 : Blo 2213435 3736901 := bbase (se 4 (by rfl) ⟨350334, by rfl⟩ : syracuseStep 3736901 = 700669) (by norm_num)
theorem B2491267 : Blo 2213435 2491267 := bstep (se 1 (by rfl) ⟨1868450, by rfl⟩ : syracuseStep 2491267 = 3736901) B3736901
theorem B3321689 : Blo 2213435 3321689 := bstep (se 2 (by rfl) ⟨1245633, by rfl⟩ : syracuseStep 3321689 = 2491267) B2491267
theorem B2214459 : Blo 2213435 2214459 := bstep (se 1 (by rfl) ⟨1660844, by rfl⟩ : syracuseStep 2214459 = 3321689) B3321689
theorem B16816085 : Blo 2213435 16816085 := bbase (se 7 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 16816085 = 394127) (by norm_num)
theorem B11210723 : Blo 2213435 11210723 := bstep (se 1 (by rfl) ⟨8408042, by rfl⟩ : syracuseStep 11210723 = 16816085) B16816085
theorem B7473815 : Blo 2213435 7473815 := bstep (se 1 (by rfl) ⟨5605361, by rfl⟩ : syracuseStep 7473815 = 11210723) B11210723
theorem B4982543 : Blo 2213435 4982543 := bstep (se 1 (by rfl) ⟨3736907, by rfl⟩ : syracuseStep 4982543 = 7473815) B7473815
theorem B3321695 : Blo 2213435 3321695 := bstep (se 1 (by rfl) ⟨2491271, by rfl⟩ : syracuseStep 3321695 = 4982543) B4982543
theorem B2214463 : Blo 2213435 2214463 := bstep (se 1 (by rfl) ⟨1660847, by rfl⟩ : syracuseStep 2214463 = 3321695) B3321695
theorem B3321701 : Blo 2213435 3321701 := bbase (se 4 (by rfl) ⟨311409, by rfl⟩ : syracuseStep 3321701 = 622819) (by norm_num)
theorem B2214467 : Blo 2213435 2214467 := bstep (se 1 (by rfl) ⟨1660850, by rfl⟩ : syracuseStep 2214467 = 3321701) B3321701
theorem B4204037 : Blo 2213435 4204037 := bbase (se 4 (by rfl) ⟨394128, by rfl⟩ : syracuseStep 4204037 = 788257) (by norm_num)
theorem B2802691 : Blo 2213435 2802691 := bstep (se 1 (by rfl) ⟨2102018, by rfl⟩ : syracuseStep 2802691 = 4204037) B4204037
theorem B3736921 : Blo 2213435 3736921 := bstep (se 2 (by rfl) ⟨1401345, by rfl⟩ : syracuseStep 3736921 = 2802691) B2802691
theorem B4982561 : Blo 2213435 4982561 := bstep (se 2 (by rfl) ⟨1868460, by rfl⟩ : syracuseStep 4982561 = 3736921) B3736921
theorem B3321707 : Blo 2213435 3321707 := bstep (se 1 (by rfl) ⟨2491280, by rfl⟩ : syracuseStep 3321707 = 4982561) B4982561
theorem B2214471 : Blo 2213435 2214471 := bstep (se 1 (by rfl) ⟨1660853, by rfl⟩ : syracuseStep 2214471 = 3321707) B3321707
theorem B2491285 : Blo 2213435 2491285 := bbase (se 6 (by rfl) ⟨58389, by rfl⟩ : syracuseStep 2491285 = 116779) (by norm_num)
theorem B3321713 : Blo 2213435 3321713 := bstep (se 2 (by rfl) ⟨1245642, by rfl⟩ : syracuseStep 3321713 = 2491285) B2491285
theorem B2214475 : Blo 2213435 2214475 := bstep (se 1 (by rfl) ⟨1660856, by rfl⟩ : syracuseStep 2214475 = 3321713) B3321713
theorem B2802701 : Blo 2213435 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B7473869 : Blo 2213435 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B4982579 : Blo 2213435 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B3321719 : Blo 2213435 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B2214479 : Blo 2213435 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B3321725 : Blo 2213435 3321725 := bbase (se 3 (by rfl) ⟨622823, by rfl⟩ : syracuseStep 3321725 = 1245647) (by norm_num)
theorem B2214483 : Blo 2213435 2214483 := bstep (se 1 (by rfl) ⟨1660862, by rfl⟩ : syracuseStep 2214483 = 3321725) B3321725
theorem B4982597 : Blo 2213435 4982597 := bbase (se 4 (by rfl) ⟨467118, by rfl⟩ : syracuseStep 4982597 = 934237) (by norm_num)
theorem B3321731 : Blo 2213435 3321731 := bstep (se 1 (by rfl) ⟨2491298, by rfl⟩ : syracuseStep 3321731 = 4982597) B4982597
theorem B2214487 : Blo 2213435 2214487 := bstep (se 1 (by rfl) ⟨1660865, by rfl⟩ : syracuseStep 2214487 = 3321731) B3321731
theorem B3547189 : Blo 2213435 3547189 := bbase (se 5 (by rfl) ⟨166274, by rfl⟩ : syracuseStep 3547189 = 332549) (by norm_num)
theorem B4729585 : Blo 2213435 4729585 := bstep (se 2 (by rfl) ⟨1773594, by rfl⟩ : syracuseStep 4729585 = 3547189) B3547189
theorem B6306113 : Blo 2213435 6306113 := bstep (se 2 (by rfl) ⟨2364792, by rfl⟩ : syracuseStep 6306113 = 4729585) B4729585
theorem B4204075 : Blo 2213435 4204075 := bstep (se 1 (by rfl) ⟨3153056, by rfl⟩ : syracuseStep 4204075 = 6306113) B6306113
theorem B5605433 : Blo 2213435 5605433 := bstep (se 2 (by rfl) ⟨2102037, by rfl⟩ : syracuseStep 5605433 = 4204075) B4204075
theorem B3736955 : Blo 2213435 3736955 := bstep (se 1 (by rfl) ⟨2802716, by rfl⟩ : syracuseStep 3736955 = 5605433) B5605433
theorem B2491303 : Blo 2213435 2491303 := bstep (se 1 (by rfl) ⟨1868477, by rfl⟩ : syracuseStep 2491303 = 3736955) B3736955
theorem B3321737 : Blo 2213435 3321737 := bstep (se 2 (by rfl) ⟨1245651, by rfl⟩ : syracuseStep 3321737 = 2491303) B2491303
theorem B2214491 : Blo 2213435 2214491 := bstep (se 1 (by rfl) ⟨1660868, by rfl⟩ : syracuseStep 2214491 = 3321737) B3321737
theorem B11210885 : Blo 2213435 11210885 := bbase (se 4 (by rfl) ⟨1051020, by rfl⟩ : syracuseStep 11210885 = 2102041) (by norm_num)
theorem B7473923 : Blo 2213435 7473923 := bstep (se 1 (by rfl) ⟨5605442, by rfl⟩ : syracuseStep 7473923 = 11210885) B11210885
theorem B4982615 : Blo 2213435 4982615 := bstep (se 1 (by rfl) ⟨3736961, by rfl⟩ : syracuseStep 4982615 = 7473923) B7473923
theorem B3321743 : Blo 2213435 3321743 := bstep (se 1 (by rfl) ⟨2491307, by rfl⟩ : syracuseStep 3321743 = 4982615) B4982615
theorem B2214495 : Blo 2213435 2214495 := bstep (se 1 (by rfl) ⟨1660871, by rfl⟩ : syracuseStep 2214495 = 3321743) B3321743
theorem B3321749 : Blo 2213435 3321749 := bbase (se 6 (by rfl) ⟨77853, by rfl⟩ : syracuseStep 3321749 = 155707) (by norm_num)
theorem B2214499 : Blo 2213435 2214499 := bstep (se 1 (by rfl) ⟨1660874, by rfl⟩ : syracuseStep 2214499 = 3321749) B3321749
theorem B2364805 : Blo 2213435 2364805 := bbase (se 4 (by rfl) ⟨221700, by rfl⟩ : syracuseStep 2364805 = 443401) (by norm_num)
theorem B12612293 : Blo 2213435 12612293 := bstep (se 4 (by rfl) ⟨1182402, by rfl⟩ : syracuseStep 12612293 = 2364805) B2364805
theorem B8408195 : Blo 2213435 8408195 := bstep (se 1 (by rfl) ⟨6306146, by rfl⟩ : syracuseStep 8408195 = 12612293) B12612293
theorem B5605463 : Blo 2213435 5605463 := bstep (se 1 (by rfl) ⟨4204097, by rfl⟩ : syracuseStep 5605463 = 8408195) B8408195
theorem B3736975 : Blo 2213435 3736975 := bstep (se 1 (by rfl) ⟨2802731, by rfl⟩ : syracuseStep 3736975 = 5605463) B5605463
theorem B4982633 : Blo 2213435 4982633 := bstep (se 2 (by rfl) ⟨1868487, by rfl⟩ : syracuseStep 4982633 = 3736975) B3736975
theorem B3321755 : Blo 2213435 3321755 := bstep (se 1 (by rfl) ⟨2491316, by rfl⟩ : syracuseStep 3321755 = 4982633) B4982633
theorem B2214503 : Blo 2213435 2214503 := bstep (se 1 (by rfl) ⟨1660877, by rfl⟩ : syracuseStep 2214503 = 3321755) B3321755
theorem B2491321 : Blo 2213435 2491321 := bbase (se 2 (by rfl) ⟨934245, by rfl⟩ : syracuseStep 2491321 = 1868491) (by norm_num)
theorem B3321761 : Blo 2213435 3321761 := bstep (se 2 (by rfl) ⟨1245660, by rfl⟩ : syracuseStep 3321761 = 2491321) B2491321
theorem B2214507 : Blo 2213435 2214507 := bstep (se 1 (by rfl) ⟨1660880, by rfl⟩ : syracuseStep 2214507 = 3321761) B3321761
theorem B45455701 : Blo 2213435 45455701 := bbase (se 10 (by rfl) ⟨66585, by rfl⟩ : syracuseStep 45455701 = 133171) (by norm_num)
theorem B60607601 : Blo 2213435 60607601 := bstep (se 2 (by rfl) ⟨22727850, by rfl⟩ : syracuseStep 60607601 = 45455701) B45455701
theorem B40405067 : Blo 2213435 40405067 := bstep (se 1 (by rfl) ⟨30303800, by rfl⟩ : syracuseStep 40405067 = 60607601) B60607601
theorem B26936711 : Blo 2213435 26936711 := bstep (se 1 (by rfl) ⟨20202533, by rfl⟩ : syracuseStep 26936711 = 40405067) B40405067
theorem B17957807 : Blo 2213435 17957807 := bstep (se 1 (by rfl) ⟨13468355, by rfl⟩ : syracuseStep 17957807 = 26936711) B26936711
theorem B11971871 : Blo 2213435 11971871 := bstep (se 1 (by rfl) ⟨8978903, by rfl⟩ : syracuseStep 11971871 = 17957807) B17957807
theorem B7981247 : Blo 2213435 7981247 := bstep (se 1 (by rfl) ⟨5985935, by rfl⟩ : syracuseStep 7981247 = 11971871) B11971871
theorem B5320831 : Blo 2213435 5320831 := bstep (se 1 (by rfl) ⟨3990623, by rfl⟩ : syracuseStep 5320831 = 7981247) B7981247
theorem B7094441 : Blo 2213435 7094441 := bstep (se 2 (by rfl) ⟨2660415, by rfl⟩ : syracuseStep 7094441 = 5320831) B5320831
theorem B4729627 : Blo 2213435 4729627 := bstep (se 1 (by rfl) ⟨3547220, by rfl⟩ : syracuseStep 4729627 = 7094441) B7094441
theorem B6306169 : Blo 2213435 6306169 := bstep (se 2 (by rfl) ⟨2364813, by rfl⟩ : syracuseStep 6306169 = 4729627) B4729627
theorem B8408225 : Blo 2213435 8408225 := bstep (se 2 (by rfl) ⟨3153084, by rfl⟩ : syracuseStep 8408225 = 6306169) B6306169
theorem B5605483 : Blo 2213435 5605483 := bstep (se 1 (by rfl) ⟨4204112, by rfl⟩ : syracuseStep 5605483 = 8408225) B8408225
theorem B7473977 : Blo 2213435 7473977 := bstep (se 2 (by rfl) ⟨2802741, by rfl⟩ : syracuseStep 7473977 = 5605483) B5605483
theorem B4982651 : Blo 2213435 4982651 := bstep (se 1 (by rfl) ⟨3736988, by rfl⟩ : syracuseStep 4982651 = 7473977) B7473977
theorem B3321767 : Blo 2213435 3321767 := bstep (se 1 (by rfl) ⟨2491325, by rfl⟩ : syracuseStep 3321767 = 4982651) B4982651
theorem B2214511 : Blo 2213435 2214511 := bstep (se 1 (by rfl) ⟨1660883, by rfl⟩ : syracuseStep 2214511 = 3321767) B3321767
theorem B3321773 : Blo 2213435 3321773 := bbase (se 3 (by rfl) ⟨622832, by rfl⟩ : syracuseStep 3321773 = 1245665) (by norm_num)
theorem B2214515 : Blo 2213435 2214515 := bstep (se 1 (by rfl) ⟨1660886, by rfl⟩ : syracuseStep 2214515 = 3321773) B3321773
theorem B4982669 : Blo 2213435 4982669 := bbase (se 3 (by rfl) ⟨934250, by rfl⟩ : syracuseStep 4982669 = 1868501) (by norm_num)
theorem B3321779 : Blo 2213435 3321779 := bstep (se 1 (by rfl) ⟨2491334, by rfl⟩ : syracuseStep 3321779 = 4982669) B4982669
theorem B2214519 : Blo 2213435 2214519 := bstep (se 1 (by rfl) ⟨1660889, by rfl⟩ : syracuseStep 2214519 = 3321779) B3321779
theorem B2802757 : Blo 2213435 2802757 := bbase (se 4 (by rfl) ⟨262758, by rfl⟩ : syracuseStep 2802757 = 525517) (by norm_num)
theorem B3737009 : Blo 2213435 3737009 := bstep (se 2 (by rfl) ⟨1401378, by rfl⟩ : syracuseStep 3737009 = 2802757) B2802757
theorem B2491339 : Blo 2213435 2491339 := bstep (se 1 (by rfl) ⟨1868504, by rfl⟩ : syracuseStep 2491339 = 3737009) B3737009
theorem B3321785 : Blo 2213435 3321785 := bstep (se 2 (by rfl) ⟨1245669, by rfl⟩ : syracuseStep 3321785 = 2491339) B2491339
theorem B2214523 : Blo 2213435 2214523 := bstep (se 1 (by rfl) ⟨1660892, by rfl⟩ : syracuseStep 2214523 = 3321785) B3321785
theorem B5050669 : Blo 2213435 5050669 := bbase (se 3 (by rfl) ⟨947000, by rfl⟩ : syracuseStep 5050669 = 1894001) (by norm_num)
theorem B6734225 : Blo 2213435 6734225 := bstep (se 2 (by rfl) ⟨2525334, by rfl⟩ : syracuseStep 6734225 = 5050669) B5050669
theorem B17957933 : Blo 2213435 17957933 := bstep (se 3 (by rfl) ⟨3367112, by rfl⟩ : syracuseStep 17957933 = 6734225) B6734225
theorem B11971955 : Blo 2213435 11971955 := bstep (se 1 (by rfl) ⟨8978966, by rfl⟩ : syracuseStep 11971955 = 17957933) B17957933
theorem B7981303 : Blo 2213435 7981303 := bstep (se 1 (by rfl) ⟨5985977, by rfl⟩ : syracuseStep 7981303 = 11971955) B11971955
theorem B10641737 : Blo 2213435 10641737 := bstep (se 2 (by rfl) ⟨3990651, by rfl⟩ : syracuseStep 10641737 = 7981303) B7981303
theorem B28377965 : Blo 2213435 28377965 := bstep (se 3 (by rfl) ⟨5320868, by rfl⟩ : syracuseStep 28377965 = 10641737) B10641737
theorem B18918643 : Blo 2213435 18918643 := bstep (se 1 (by rfl) ⟨14188982, by rfl⟩ : syracuseStep 18918643 = 28377965) B28377965
theorem B25224857 : Blo 2213435 25224857 := bstep (se 2 (by rfl) ⟨9459321, by rfl⟩ : syracuseStep 25224857 = 18918643) B18918643
theorem B16816571 : Blo 2213435 16816571 := bstep (se 1 (by rfl) ⟨12612428, by rfl⟩ : syracuseStep 16816571 = 25224857) B25224857
theorem B11211047 : Blo 2213435 11211047 := bstep (se 1 (by rfl) ⟨8408285, by rfl⟩ : syracuseStep 11211047 = 16816571) B16816571
theorem B7474031 : Blo 2213435 7474031 := bstep (se 1 (by rfl) ⟨5605523, by rfl⟩ : syracuseStep 7474031 = 11211047) B11211047
theorem B4982687 : Blo 2213435 4982687 := bstep (se 1 (by rfl) ⟨3737015, by rfl⟩ : syracuseStep 4982687 = 7474031) B7474031
theorem B3321791 : Blo 2213435 3321791 := bstep (se 1 (by rfl) ⟨2491343, by rfl⟩ : syracuseStep 3321791 = 4982687) B4982687
theorem B2214527 : Blo 2213435 2214527 := bstep (se 1 (by rfl) ⟨1660895, by rfl⟩ : syracuseStep 2214527 = 3321791) B3321791
theorem B3321797 : Blo 2213435 3321797 := bbase (se 4 (by rfl) ⟨311418, by rfl⟩ : syracuseStep 3321797 = 622837) (by norm_num)
theorem B2214531 : Blo 2213435 2214531 := bstep (se 1 (by rfl) ⟨1660898, by rfl⟩ : syracuseStep 2214531 = 3321797) B3321797
theorem B3737029 : Blo 2213435 3737029 := bbase (se 4 (by rfl) ⟨350346, by rfl⟩ : syracuseStep 3737029 = 700693) (by norm_num)
theorem B4982705 : Blo 2213435 4982705 := bstep (se 2 (by rfl) ⟨1868514, by rfl⟩ : syracuseStep 4982705 = 3737029) B3737029
theorem B3321803 : Blo 2213435 3321803 := bstep (se 1 (by rfl) ⟨2491352, by rfl⟩ : syracuseStep 3321803 = 4982705) B4982705
theorem B2214535 : Blo 2213435 2214535 := bstep (se 1 (by rfl) ⟨1660901, by rfl⟩ : syracuseStep 2214535 = 3321803) B3321803
theorem B2491357 : Blo 2213435 2491357 := bbase (se 3 (by rfl) ⟨467129, by rfl⟩ : syracuseStep 2491357 = 934259) (by norm_num)
theorem B3321809 : Blo 2213435 3321809 := bstep (se 2 (by rfl) ⟨1245678, by rfl⟩ : syracuseStep 3321809 = 2491357) B2491357
theorem B2214539 : Blo 2213435 2214539 := bstep (se 1 (by rfl) ⟨1660904, by rfl⟩ : syracuseStep 2214539 = 3321809) B3321809
theorem B7474085 : Blo 2213435 7474085 := bbase (se 4 (by rfl) ⟨700695, by rfl⟩ : syracuseStep 7474085 = 1401391) (by norm_num)
theorem B4982723 : Blo 2213435 4982723 := bstep (se 1 (by rfl) ⟨3737042, by rfl⟩ : syracuseStep 4982723 = 7474085) B7474085
theorem B3321815 : Blo 2213435 3321815 := bstep (se 1 (by rfl) ⟨2491361, by rfl⟩ : syracuseStep 3321815 = 4982723) B4982723
theorem B2214543 : Blo 2213435 2214543 := bstep (se 1 (by rfl) ⟨1660907, by rfl⟩ : syracuseStep 2214543 = 3321815) B3321815
theorem B3321821 : Blo 2213435 3321821 := bbase (se 3 (by rfl) ⟨622841, by rfl⟩ : syracuseStep 3321821 = 1245683) (by norm_num)
theorem B2214547 : Blo 2213435 2214547 := bstep (se 1 (by rfl) ⟨1660910, by rfl⟩ : syracuseStep 2214547 = 3321821) B3321821
theorem B4982741 : Blo 2213435 4982741 := bbase (se 7 (by rfl) ⟨58391, by rfl⟩ : syracuseStep 4982741 = 116783) (by norm_num)
theorem B3321827 : Blo 2213435 3321827 := bstep (se 1 (by rfl) ⟨2491370, by rfl⟩ : syracuseStep 3321827 = 4982741) B4982741
theorem B2214551 : Blo 2213435 2214551 := bstep (se 1 (by rfl) ⟨1660913, by rfl⟩ : syracuseStep 2214551 = 3321827) B3321827
theorem B5682077 : Blo 2213435 5682077 := bbase (se 3 (by rfl) ⟨1065389, by rfl⟩ : syracuseStep 5682077 = 2130779) (by norm_num)
theorem B3788051 : Blo 2213435 3788051 := bstep (se 1 (by rfl) ⟨2841038, by rfl⟩ : syracuseStep 3788051 = 5682077) B5682077
theorem B10101469 : Blo 2213435 10101469 := bstep (se 3 (by rfl) ⟨1894025, by rfl⟩ : syracuseStep 10101469 = 3788051) B3788051
theorem B13468625 : Blo 2213435 13468625 := bstep (se 2 (by rfl) ⟨5050734, by rfl⟩ : syracuseStep 13468625 = 10101469) B10101469
theorem B8979083 : Blo 2213435 8979083 := bstep (se 1 (by rfl) ⟨6734312, by rfl⟩ : syracuseStep 8979083 = 13468625) B13468625
theorem B5986055 : Blo 2213435 5986055 := bstep (se 1 (by rfl) ⟨4489541, by rfl⟩ : syracuseStep 5986055 = 8979083) B8979083
theorem B3990703 : Blo 2213435 3990703 := bstep (se 1 (by rfl) ⟨2993027, by rfl⟩ : syracuseStep 3990703 = 5986055) B5986055
theorem B5320937 : Blo 2213435 5320937 := bstep (se 2 (by rfl) ⟨1995351, by rfl⟩ : syracuseStep 5320937 = 3990703) B3990703
theorem B14189165 : Blo 2213435 14189165 := bstep (se 3 (by rfl) ⟨2660468, by rfl⟩ : syracuseStep 14189165 = 5320937) B5320937
theorem B9459443 : Blo 2213435 9459443 := bstep (se 1 (by rfl) ⟨7094582, by rfl⟩ : syracuseStep 9459443 = 14189165) B14189165
theorem B6306295 : Blo 2213435 6306295 := bstep (se 1 (by rfl) ⟨4729721, by rfl⟩ : syracuseStep 6306295 = 9459443) B9459443
theorem B8408393 : Blo 2213435 8408393 := bstep (se 2 (by rfl) ⟨3153147, by rfl⟩ : syracuseStep 8408393 = 6306295) B6306295
theorem B5605595 : Blo 2213435 5605595 := bstep (se 1 (by rfl) ⟨4204196, by rfl⟩ : syracuseStep 5605595 = 8408393) B8408393
theorem B3737063 : Blo 2213435 3737063 := bstep (se 1 (by rfl) ⟨2802797, by rfl⟩ : syracuseStep 3737063 = 5605595) B5605595
theorem B2491375 : Blo 2213435 2491375 := bstep (se 1 (by rfl) ⟨1868531, by rfl⟩ : syracuseStep 2491375 = 3737063) B3737063
theorem B3321833 : Blo 2213435 3321833 := bstep (se 2 (by rfl) ⟨1245687, by rfl⟩ : syracuseStep 3321833 = 2491375) B2491375
theorem B2214555 : Blo 2213435 2214555 := bstep (se 1 (by rfl) ⟨1660916, by rfl⟩ : syracuseStep 2214555 = 3321833) B3321833
theorem B2660473 : Blo 2213435 2660473 := bbase (se 2 (by rfl) ⟨997677, by rfl⟩ : syracuseStep 2660473 = 1995355) (by norm_num)
theorem B3547297 : Blo 2213435 3547297 := bstep (se 2 (by rfl) ⟨1330236, by rfl⟩ : syracuseStep 3547297 = 2660473) B2660473
theorem B18918917 : Blo 2213435 18918917 := bstep (se 4 (by rfl) ⟨1773648, by rfl⟩ : syracuseStep 18918917 = 3547297) B3547297
theorem B12612611 : Blo 2213435 12612611 := bstep (se 1 (by rfl) ⟨9459458, by rfl⟩ : syracuseStep 12612611 = 18918917) B18918917
theorem B8408407 : Blo 2213435 8408407 := bstep (se 1 (by rfl) ⟨6306305, by rfl⟩ : syracuseStep 8408407 = 12612611) B12612611
theorem B11211209 : Blo 2213435 11211209 := bstep (se 2 (by rfl) ⟨4204203, by rfl⟩ : syracuseStep 11211209 = 8408407) B8408407
theorem B7474139 : Blo 2213435 7474139 := bstep (se 1 (by rfl) ⟨5605604, by rfl⟩ : syracuseStep 7474139 = 11211209) B11211209
theorem B4982759 : Blo 2213435 4982759 := bstep (se 1 (by rfl) ⟨3737069, by rfl⟩ : syracuseStep 4982759 = 7474139) B7474139
theorem B3321839 : Blo 2213435 3321839 := bstep (se 1 (by rfl) ⟨2491379, by rfl⟩ : syracuseStep 3321839 = 4982759) B4982759
theorem B2214559 : Blo 2213435 2214559 := bstep (se 1 (by rfl) ⟨1660919, by rfl⟩ : syracuseStep 2214559 = 3321839) B3321839
theorem B3321845 : Blo 2213435 3321845 := bbase (se 5 (by rfl) ⟨155711, by rfl⟩ : syracuseStep 3321845 = 311423) (by norm_num)
theorem B2214563 : Blo 2213435 2214563 := bstep (se 1 (by rfl) ⟨1660922, by rfl⟩ : syracuseStep 2214563 = 3321845) B3321845
theorem B3990725 : Blo 2213435 3990725 := bbase (se 4 (by rfl) ⟨374130, by rfl⟩ : syracuseStep 3990725 = 748261) (by norm_num)
theorem B2660483 : Blo 2213435 2660483 := bstep (se 1 (by rfl) ⟨1995362, by rfl⟩ : syracuseStep 2660483 = 3990725) B3990725
theorem B7094621 : Blo 2213435 7094621 := bstep (se 3 (by rfl) ⟨1330241, by rfl⟩ : syracuseStep 7094621 = 2660483) B2660483
theorem B4729747 : Blo 2213435 4729747 := bstep (se 1 (by rfl) ⟨3547310, by rfl⟩ : syracuseStep 4729747 = 7094621) B7094621
theorem B6306329 : Blo 2213435 6306329 := bstep (se 2 (by rfl) ⟨2364873, by rfl⟩ : syracuseStep 6306329 = 4729747) B4729747
theorem B4204219 : Blo 2213435 4204219 := bstep (se 1 (by rfl) ⟨3153164, by rfl⟩ : syracuseStep 4204219 = 6306329) B6306329
theorem B5605625 : Blo 2213435 5605625 := bstep (se 2 (by rfl) ⟨2102109, by rfl⟩ : syracuseStep 5605625 = 4204219) B4204219
theorem B3737083 : Blo 2213435 3737083 := bstep (se 1 (by rfl) ⟨2802812, by rfl⟩ : syracuseStep 3737083 = 5605625) B5605625
theorem B4982777 : Blo 2213435 4982777 := bstep (se 2 (by rfl) ⟨1868541, by rfl⟩ : syracuseStep 4982777 = 3737083) B3737083
theorem B3321851 : Blo 2213435 3321851 := bstep (se 1 (by rfl) ⟨2491388, by rfl⟩ : syracuseStep 3321851 = 4982777) B4982777
theorem B2214567 : Blo 2213435 2214567 := bstep (se 1 (by rfl) ⟨1660925, by rfl⟩ : syracuseStep 2214567 = 3321851) B3321851
theorem B2491393 : Blo 2213435 2491393 := bbase (se 2 (by rfl) ⟨934272, by rfl⟩ : syracuseStep 2491393 = 1868545) (by norm_num)
theorem B3321857 : Blo 2213435 3321857 := bstep (se 2 (by rfl) ⟨1245696, by rfl⟩ : syracuseStep 3321857 = 2491393) B2491393
theorem B2214571 : Blo 2213435 2214571 := bstep (se 1 (by rfl) ⟨1660928, by rfl⟩ : syracuseStep 2214571 = 3321857) B3321857
theorem B5605645 : Blo 2213435 5605645 := bbase (se 3 (by rfl) ⟨1051058, by rfl⟩ : syracuseStep 5605645 = 2102117) (by norm_num)
theorem B7474193 : Blo 2213435 7474193 := bstep (se 2 (by rfl) ⟨2802822, by rfl⟩ : syracuseStep 7474193 = 5605645) B5605645
theorem B4982795 : Blo 2213435 4982795 := bstep (se 1 (by rfl) ⟨3737096, by rfl⟩ : syracuseStep 4982795 = 7474193) B7474193
theorem B3321863 : Blo 2213435 3321863 := bstep (se 1 (by rfl) ⟨2491397, by rfl⟩ : syracuseStep 3321863 = 4982795) B4982795
theorem B2214575 : Blo 2213435 2214575 := bstep (se 1 (by rfl) ⟨1660931, by rfl⟩ : syracuseStep 2214575 = 3321863) B3321863
theorem B3321869 : Blo 2213435 3321869 := bbase (se 3 (by rfl) ⟨622850, by rfl⟩ : syracuseStep 3321869 = 1245701) (by norm_num)
theorem B2214579 : Blo 2213435 2214579 := bstep (se 1 (by rfl) ⟨1660934, by rfl⟩ : syracuseStep 2214579 = 3321869) B3321869
theorem B4982813 : Blo 2213435 4982813 := bbase (se 3 (by rfl) ⟨934277, by rfl⟩ : syracuseStep 4982813 = 1868555) (by norm_num)
theorem B3321875 : Blo 2213435 3321875 := bstep (se 1 (by rfl) ⟨2491406, by rfl⟩ : syracuseStep 3321875 = 4982813) B4982813
theorem B2214583 : Blo 2213435 2214583 := bstep (se 1 (by rfl) ⟨1660937, by rfl⟩ : syracuseStep 2214583 = 3321875) B3321875
theorem B3737117 : Blo 2213435 3737117 := bbase (se 3 (by rfl) ⟨700709, by rfl⟩ : syracuseStep 3737117 = 1401419) (by norm_num)
theorem B2491411 : Blo 2213435 2491411 := bstep (se 1 (by rfl) ⟨1868558, by rfl⟩ : syracuseStep 2491411 = 3737117) B3737117
theorem B3321881 : Blo 2213435 3321881 := bstep (se 2 (by rfl) ⟨1245705, by rfl⟩ : syracuseStep 3321881 = 2491411) B2491411
theorem B2214587 : Blo 2213435 2214587 := bstep (se 1 (by rfl) ⟨1660940, by rfl⟩ : syracuseStep 2214587 = 3321881) B3321881
theorem B4859741 : Blo 2213435 4859741 := bbase (se 3 (by rfl) ⟨911201, by rfl⟩ : syracuseStep 4859741 = 1822403) (by norm_num)
theorem B3239827 : Blo 2213435 3239827 := bstep (se 1 (by rfl) ⟨2429870, by rfl⟩ : syracuseStep 3239827 = 4859741) B4859741
theorem B17279077 : Blo 2213435 17279077 := bstep (se 4 (by rfl) ⟨1619913, by rfl⟩ : syracuseStep 17279077 = 3239827) B3239827
theorem B23038769 : Blo 2213435 23038769 := bstep (se 2 (by rfl) ⟨8639538, by rfl⟩ : syracuseStep 23038769 = 17279077) B17279077
theorem B15359179 : Blo 2213435 15359179 := bstep (se 1 (by rfl) ⟨11519384, by rfl⟩ : syracuseStep 15359179 = 23038769) B23038769
theorem B20478905 : Blo 2213435 20478905 := bstep (se 2 (by rfl) ⟨7679589, by rfl⟩ : syracuseStep 20478905 = 15359179) B15359179
theorem B13652603 : Blo 2213435 13652603 := bstep (se 1 (by rfl) ⟨10239452, by rfl⟩ : syracuseStep 13652603 = 20478905) B20478905
theorem B9101735 : Blo 2213435 9101735 := bstep (se 1 (by rfl) ⟨6826301, by rfl⟩ : syracuseStep 9101735 = 13652603) B13652603
theorem B6067823 : Blo 2213435 6067823 := bstep (se 1 (by rfl) ⟨4550867, by rfl⟩ : syracuseStep 6067823 = 9101735) B9101735
theorem B64723445 : Blo 2213435 64723445 := bstep (se 5 (by rfl) ⟨3033911, by rfl⟩ : syracuseStep 64723445 = 6067823) B6067823
theorem B43148963 : Blo 2213435 43148963 := bstep (se 1 (by rfl) ⟨32361722, by rfl⟩ : syracuseStep 43148963 = 64723445) B64723445
theorem B115063901 : Blo 2213435 115063901 := bstep (se 3 (by rfl) ⟨21574481, by rfl⟩ : syracuseStep 115063901 = 43148963) B43148963
theorem B76709267 : Blo 2213435 76709267 := bstep (se 1 (by rfl) ⟨57531950, by rfl⟩ : syracuseStep 76709267 = 115063901) B115063901
theorem B51139511 : Blo 2213435 51139511 := bstep (se 1 (by rfl) ⟨38354633, by rfl⟩ : syracuseStep 51139511 = 76709267) B76709267
theorem B34093007 : Blo 2213435 34093007 := bstep (se 1 (by rfl) ⟨25569755, by rfl⟩ : syracuseStep 34093007 = 51139511) B51139511
theorem B22728671 : Blo 2213435 22728671 := bstep (se 1 (by rfl) ⟨17046503, by rfl⟩ : syracuseStep 22728671 = 34093007) B34093007
theorem B15152447 : Blo 2213435 15152447 := bstep (se 1 (by rfl) ⟨11364335, by rfl⟩ : syracuseStep 15152447 = 22728671) B22728671
theorem B10101631 : Blo 2213435 10101631 := bstep (se 1 (by rfl) ⟨7576223, by rfl⟩ : syracuseStep 10101631 = 15152447) B15152447
theorem B13468841 : Blo 2213435 13468841 := bstep (se 2 (by rfl) ⟨5050815, by rfl⟩ : syracuseStep 13468841 = 10101631) B10101631
theorem B8979227 : Blo 2213435 8979227 := bstep (se 1 (by rfl) ⟨6734420, by rfl⟩ : syracuseStep 8979227 = 13468841) B13468841
theorem B5986151 : Blo 2213435 5986151 := bstep (se 1 (by rfl) ⟨4489613, by rfl⟩ : syracuseStep 5986151 = 8979227) B8979227
theorem B3990767 : Blo 2213435 3990767 := bstep (se 1 (by rfl) ⟨2993075, by rfl⟩ : syracuseStep 3990767 = 5986151) B5986151
theorem B10642045 : Blo 2213435 10642045 := bstep (se 3 (by rfl) ⟨1995383, by rfl⟩ : syracuseStep 10642045 = 3990767) B3990767
theorem B14189393 : Blo 2213435 14189393 := bstep (se 2 (by rfl) ⟨5321022, by rfl⟩ : syracuseStep 14189393 = 10642045) B10642045
theorem B9459595 : Blo 2213435 9459595 := bstep (se 1 (by rfl) ⟨7094696, by rfl⟩ : syracuseStep 9459595 = 14189393) B14189393
theorem B12612793 : Blo 2213435 12612793 := bstep (se 2 (by rfl) ⟨4729797, by rfl⟩ : syracuseStep 12612793 = 9459595) B9459595
theorem B16817057 : Blo 2213435 16817057 := bstep (se 2 (by rfl) ⟨6306396, by rfl⟩ : syracuseStep 16817057 = 12612793) B12612793
theorem B11211371 : Blo 2213435 11211371 := bstep (se 1 (by rfl) ⟨8408528, by rfl⟩ : syracuseStep 11211371 = 16817057) B16817057
theorem B7474247 : Blo 2213435 7474247 := bstep (se 1 (by rfl) ⟨5605685, by rfl⟩ : syracuseStep 7474247 = 11211371) B11211371
theorem B4982831 : Blo 2213435 4982831 := bstep (se 1 (by rfl) ⟨3737123, by rfl⟩ : syracuseStep 4982831 = 7474247) B7474247
theorem B3321887 : Blo 2213435 3321887 := bstep (se 1 (by rfl) ⟨2491415, by rfl⟩ : syracuseStep 3321887 = 4982831) B4982831
theorem B2214591 : Blo 2213435 2214591 := bstep (se 1 (by rfl) ⟨1660943, by rfl⟩ : syracuseStep 2214591 = 3321887) B3321887
theorem B3321893 : Blo 2213435 3321893 := bbase (se 4 (by rfl) ⟨311427, by rfl⟩ : syracuseStep 3321893 = 622855) (by norm_num)
theorem B2214595 : Blo 2213435 2214595 := bstep (se 1 (by rfl) ⟨1660946, by rfl⟩ : syracuseStep 2214595 = 3321893) B3321893
theorem B2802853 : Blo 2213435 2802853 := bbase (se 4 (by rfl) ⟨262767, by rfl⟩ : syracuseStep 2802853 = 525535) (by norm_num)
theorem B3737137 : Blo 2213435 3737137 := bstep (se 2 (by rfl) ⟨1401426, by rfl⟩ : syracuseStep 3737137 = 2802853) B2802853
theorem B4982849 : Blo 2213435 4982849 := bstep (se 2 (by rfl) ⟨1868568, by rfl⟩ : syracuseStep 4982849 = 3737137) B3737137
theorem B3321899 : Blo 2213435 3321899 := bstep (se 1 (by rfl) ⟨2491424, by rfl⟩ : syracuseStep 3321899 = 4982849) B4982849
theorem B2214599 : Blo 2213435 2214599 := bstep (se 1 (by rfl) ⟨1660949, by rfl⟩ : syracuseStep 2214599 = 3321899) B3321899
theorem B2491429 : Blo 2213435 2491429 := bbase (se 4 (by rfl) ⟨233571, by rfl⟩ : syracuseStep 2491429 = 467143) (by norm_num)
theorem B3321905 : Blo 2213435 3321905 := bstep (se 2 (by rfl) ⟨1245714, by rfl⟩ : syracuseStep 3321905 = 2491429) B2491429
theorem B2214603 : Blo 2213435 2214603 := bstep (se 1 (by rfl) ⟨1660952, by rfl⟩ : syracuseStep 2214603 = 3321905) B3321905
theorem B3990797 : Blo 2213435 3990797 := bbase (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) (by norm_num)
theorem B2660531 : Blo 2213435 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B7094749 : Blo 2213435 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B9459665 : Blo 2213435 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B6306443 : Blo 2213435 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B4204295 : Blo 2213435 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B2802863 : Blo 2213435 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B7474301 : Blo 2213435 7474301 := bstep (se 3 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 7474301 = 2802863) B2802863
theorem B4982867 : Blo 2213435 4982867 := bstep (se 1 (by rfl) ⟨3737150, by rfl⟩ : syracuseStep 4982867 = 7474301) B7474301
theorem B3321911 : Blo 2213435 3321911 := bstep (se 1 (by rfl) ⟨2491433, by rfl⟩ : syracuseStep 3321911 = 4982867) B4982867
theorem B2214607 : Blo 2213435 2214607 := bstep (se 1 (by rfl) ⟨1660955, by rfl⟩ : syracuseStep 2214607 = 3321911) B3321911
theorem B3321917 : Blo 2213435 3321917 := bbase (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) (by norm_num)
theorem B2214611 : Blo 2213435 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B4982885 : Blo 2213435 4982885 := bbase (se 4 (by rfl) ⟨467145, by rfl⟩ : syracuseStep 4982885 = 934291) (by norm_num)
theorem B3321923 : Blo 2213435 3321923 := bstep (se 1 (by rfl) ⟨2491442, by rfl⟩ : syracuseStep 3321923 = 4982885) B4982885
theorem B2214615 : Blo 2213435 2214615 := bstep (se 1 (by rfl) ⟨1660961, by rfl⟩ : syracuseStep 2214615 = 3321923) B3321923
theorem B5605757 : Blo 2213435 5605757 := bbase (se 3 (by rfl) ⟨1051079, by rfl⟩ : syracuseStep 5605757 = 2102159) (by norm_num)
theorem B3737171 : Blo 2213435 3737171 := bstep (se 1 (by rfl) ⟨2802878, by rfl⟩ : syracuseStep 3737171 = 5605757) B5605757
theorem B2491447 : Blo 2213435 2491447 := bstep (se 1 (by rfl) ⟨1868585, by rfl⟩ : syracuseStep 2491447 = 3737171) B3737171
theorem B3321929 : Blo 2213435 3321929 := bstep (se 2 (by rfl) ⟨1245723, by rfl⟩ : syracuseStep 3321929 = 2491447) B2491447
theorem B2214619 : Blo 2213435 2214619 := bstep (se 1 (by rfl) ⟨1660964, by rfl⟩ : syracuseStep 2214619 = 3321929) B3321929
theorem B4204325 : Blo 2213435 4204325 := bbase (se 4 (by rfl) ⟨394155, by rfl⟩ : syracuseStep 4204325 = 788311) (by norm_num)
theorem B11211533 : Blo 2213435 11211533 := bstep (se 3 (by rfl) ⟨2102162, by rfl⟩ : syracuseStep 11211533 = 4204325) B4204325
theorem B7474355 : Blo 2213435 7474355 := bstep (se 1 (by rfl) ⟨5605766, by rfl⟩ : syracuseStep 7474355 = 11211533) B11211533
theorem B4982903 : Blo 2213435 4982903 := bstep (se 1 (by rfl) ⟨3737177, by rfl⟩ : syracuseStep 4982903 = 7474355) B7474355
theorem B3321935 : Blo 2213435 3321935 := bstep (se 1 (by rfl) ⟨2491451, by rfl⟩ : syracuseStep 3321935 = 4982903) B4982903
theorem B2214623 : Blo 2213435 2214623 := bstep (se 1 (by rfl) ⟨1660967, by rfl⟩ : syracuseStep 2214623 = 3321935) B3321935
theorem B3321941 : Blo 2213435 3321941 := bbase (se 8 (by rfl) ⟨19464, by rfl⟩ : syracuseStep 3321941 = 38929) (by norm_num)
theorem B2214627 : Blo 2213435 2214627 := bstep (se 1 (by rfl) ⟨1660970, by rfl⟩ : syracuseStep 2214627 = 3321941) B3321941
theorem B44335189 : Blo 2213435 44335189 := bbase (se 8 (by rfl) ⟨259776, by rfl⟩ : syracuseStep 44335189 = 519553) (by norm_num)
theorem B59113585 : Blo 2213435 59113585 := bstep (se 2 (by rfl) ⟨22167594, by rfl⟩ : syracuseStep 59113585 = 44335189) B44335189
theorem B78818113 : Blo 2213435 78818113 := bstep (se 2 (by rfl) ⟨29556792, by rfl⟩ : syracuseStep 78818113 = 59113585) B59113585
theorem B420363269 : Blo 2213435 420363269 := bstep (se 4 (by rfl) ⟨39409056, by rfl⟩ : syracuseStep 420363269 = 78818113) B78818113
theorem B280242179 : Blo 2213435 280242179 := bstep (se 1 (by rfl) ⟨210181634, by rfl⟩ : syracuseStep 280242179 = 420363269) B420363269
theorem B186828119 : Blo 2213435 186828119 := bstep (se 1 (by rfl) ⟨140121089, by rfl⟩ : syracuseStep 186828119 = 280242179) B280242179
theorem B124552079 : Blo 2213435 124552079 := bstep (se 1 (by rfl) ⟨93414059, by rfl⟩ : syracuseStep 124552079 = 186828119) B186828119
theorem B83034719 : Blo 2213435 83034719 := bstep (se 1 (by rfl) ⟨62276039, by rfl⟩ : syracuseStep 83034719 = 124552079) B124552079
theorem B55356479 : Blo 2213435 55356479 := bstep (se 1 (by rfl) ⟨41517359, by rfl⟩ : syracuseStep 55356479 = 83034719) B83034719
theorem B36904319 : Blo 2213435 36904319 := bstep (se 1 (by rfl) ⟨27678239, by rfl⟩ : syracuseStep 36904319 = 55356479) B55356479
theorem B24602879 : Blo 2213435 24602879 := bstep (se 1 (by rfl) ⟨18452159, by rfl⟩ : syracuseStep 24602879 = 36904319) B36904319
theorem B65607677 : Blo 2213435 65607677 := bstep (se 3 (by rfl) ⟨12301439, by rfl⟩ : syracuseStep 65607677 = 24602879) B24602879
theorem B43738451 : Blo 2213435 43738451 := bstep (se 1 (by rfl) ⟨32803838, by rfl⟩ : syracuseStep 43738451 = 65607677) B65607677
theorem B29158967 : Blo 2213435 29158967 := bstep (se 1 (by rfl) ⟨21869225, by rfl⟩ : syracuseStep 29158967 = 43738451) B43738451
theorem B77757245 : Blo 2213435 77757245 := bstep (se 3 (by rfl) ⟨14579483, by rfl⟩ : syracuseStep 77757245 = 29158967) B29158967
theorem B51838163 : Blo 2213435 51838163 := bstep (se 1 (by rfl) ⟨38878622, by rfl⟩ : syracuseStep 51838163 = 77757245) B77757245
theorem B34558775 : Blo 2213435 34558775 := bstep (se 1 (by rfl) ⟨25919081, by rfl⟩ : syracuseStep 34558775 = 51838163) B51838163
theorem B23039183 : Blo 2213435 23039183 := bstep (se 1 (by rfl) ⟨17279387, by rfl⟩ : syracuseStep 23039183 = 34558775) B34558775
theorem B15359455 : Blo 2213435 15359455 := bstep (se 1 (by rfl) ⟨11519591, by rfl⟩ : syracuseStep 15359455 = 23039183) B23039183
theorem B20479273 : Blo 2213435 20479273 := bstep (se 2 (by rfl) ⟨7679727, by rfl⟩ : syracuseStep 20479273 = 15359455) B15359455
theorem B109222789 : Blo 2213435 109222789 := bstep (se 4 (by rfl) ⟨10239636, by rfl⟩ : syracuseStep 109222789 = 20479273) B20479273
theorem B145630385 : Blo 2213435 145630385 := bstep (se 2 (by rfl) ⟨54611394, by rfl⟩ : syracuseStep 145630385 = 109222789) B109222789
theorem B97086923 : Blo 2213435 97086923 := bstep (se 1 (by rfl) ⟨72815192, by rfl⟩ : syracuseStep 97086923 = 145630385) B145630385
theorem B64724615 : Blo 2213435 64724615 := bstep (se 1 (by rfl) ⟨48543461, by rfl⟩ : syracuseStep 64724615 = 97086923) B97086923
theorem B43149743 : Blo 2213435 43149743 := bstep (se 1 (by rfl) ⟨32362307, by rfl⟩ : syracuseStep 43149743 = 64724615) B64724615
theorem B28766495 : Blo 2213435 28766495 := bstep (se 1 (by rfl) ⟨21574871, by rfl⟩ : syracuseStep 28766495 = 43149743) B43149743
theorem B19177663 : Blo 2213435 19177663 := bstep (se 1 (by rfl) ⟨14383247, by rfl⟩ : syracuseStep 19177663 = 28766495) B28766495
theorem B25570217 : Blo 2213435 25570217 := bstep (se 2 (by rfl) ⟨9588831, by rfl⟩ : syracuseStep 25570217 = 19177663) B19177663
theorem B17046811 : Blo 2213435 17046811 := bstep (se 1 (by rfl) ⟨12785108, by rfl⟩ : syracuseStep 17046811 = 25570217) B25570217
theorem B22729081 : Blo 2213435 22729081 := bstep (se 2 (by rfl) ⟨8523405, by rfl⟩ : syracuseStep 22729081 = 17046811) B17046811
theorem B30305441 : Blo 2213435 30305441 := bstep (se 2 (by rfl) ⟨11364540, by rfl⟩ : syracuseStep 30305441 = 22729081) B22729081
theorem B20203627 : Blo 2213435 20203627 := bstep (se 1 (by rfl) ⟨15152720, by rfl⟩ : syracuseStep 20203627 = 30305441) B30305441
theorem B26938169 : Blo 2213435 26938169 := bstep (se 2 (by rfl) ⟨10101813, by rfl⟩ : syracuseStep 26938169 = 20203627) B20203627
theorem B17958779 : Blo 2213435 17958779 := bstep (se 1 (by rfl) ⟨13469084, by rfl⟩ : syracuseStep 17958779 = 26938169) B26938169
theorem B11972519 : Blo 2213435 11972519 := bstep (se 1 (by rfl) ⟨8979389, by rfl⟩ : syracuseStep 11972519 = 17958779) B17958779
theorem B7981679 : Blo 2213435 7981679 := bstep (se 1 (by rfl) ⟨5986259, by rfl⟩ : syracuseStep 7981679 = 11972519) B11972519
theorem B21284477 : Blo 2213435 21284477 := bstep (se 3 (by rfl) ⟨3990839, by rfl⟩ : syracuseStep 21284477 = 7981679) B7981679
theorem B14189651 : Blo 2213435 14189651 := bstep (se 1 (by rfl) ⟨10642238, by rfl⟩ : syracuseStep 14189651 = 21284477) B21284477
theorem B9459767 : Blo 2213435 9459767 := bstep (se 1 (by rfl) ⟨7094825, by rfl⟩ : syracuseStep 9459767 = 14189651) B14189651
theorem B6306511 : Blo 2213435 6306511 := bstep (se 1 (by rfl) ⟨4729883, by rfl⟩ : syracuseStep 6306511 = 9459767) B9459767
theorem B8408681 : Blo 2213435 8408681 := bstep (se 2 (by rfl) ⟨3153255, by rfl⟩ : syracuseStep 8408681 = 6306511) B6306511
theorem B5605787 : Blo 2213435 5605787 := bstep (se 1 (by rfl) ⟨4204340, by rfl⟩ : syracuseStep 5605787 = 8408681) B8408681
theorem B3737191 : Blo 2213435 3737191 := bstep (se 1 (by rfl) ⟨2802893, by rfl⟩ : syracuseStep 3737191 = 5605787) B5605787
theorem B4982921 : Blo 2213435 4982921 := bstep (se 2 (by rfl) ⟨1868595, by rfl⟩ : syracuseStep 4982921 = 3737191) B3737191
theorem B3321947 : Blo 2213435 3321947 := bstep (se 1 (by rfl) ⟨2491460, by rfl⟩ : syracuseStep 3321947 = 4982921) B4982921
theorem B2214631 : Blo 2213435 2214631 := bstep (se 1 (by rfl) ⟨1660973, by rfl⟩ : syracuseStep 2214631 = 3321947) B3321947
theorem B2491465 : Blo 2213435 2491465 := bbase (se 2 (by rfl) ⟨934299, by rfl⟩ : syracuseStep 2491465 = 1868599) (by norm_num)
theorem B3321953 : Blo 2213435 3321953 := bstep (se 2 (by rfl) ⟨1245732, by rfl⟩ : syracuseStep 3321953 = 2491465) B2491465
theorem B2214635 : Blo 2213435 2214635 := bstep (se 1 (by rfl) ⟨1660976, by rfl⟩ : syracuseStep 2214635 = 3321953) B3321953
theorem B2660569 : Blo 2213435 2660569 := bbase (se 2 (by rfl) ⟨997713, by rfl⟩ : syracuseStep 2660569 = 1995427) (by norm_num)
theorem B14189701 : Blo 2213435 14189701 := bstep (se 4 (by rfl) ⟨1330284, by rfl⟩ : syracuseStep 14189701 = 2660569) B2660569
theorem B18919601 : Blo 2213435 18919601 := bstep (se 2 (by rfl) ⟨7094850, by rfl⟩ : syracuseStep 18919601 = 14189701) B14189701
theorem B12613067 : Blo 2213435 12613067 := bstep (se 1 (by rfl) ⟨9459800, by rfl⟩ : syracuseStep 12613067 = 18919601) B18919601
theorem B8408711 : Blo 2213435 8408711 := bstep (se 1 (by rfl) ⟨6306533, by rfl⟩ : syracuseStep 8408711 = 12613067) B12613067
theorem B5605807 : Blo 2213435 5605807 := bstep (se 1 (by rfl) ⟨4204355, by rfl⟩ : syracuseStep 5605807 = 8408711) B8408711
theorem B7474409 : Blo 2213435 7474409 := bstep (se 2 (by rfl) ⟨2802903, by rfl⟩ : syracuseStep 7474409 = 5605807) B5605807
theorem B4982939 : Blo 2213435 4982939 := bstep (se 1 (by rfl) ⟨3737204, by rfl⟩ : syracuseStep 4982939 = 7474409) B7474409
theorem B3321959 : Blo 2213435 3321959 := bstep (se 1 (by rfl) ⟨2491469, by rfl⟩ : syracuseStep 3321959 = 4982939) B4982939
theorem B2214639 : Blo 2213435 2214639 := bstep (se 1 (by rfl) ⟨1660979, by rfl⟩ : syracuseStep 2214639 = 3321959) B3321959
theorem B3321965 : Blo 2213435 3321965 := bbase (se 3 (by rfl) ⟨622868, by rfl⟩ : syracuseStep 3321965 = 1245737) (by norm_num)
theorem B2214643 : Blo 2213435 2214643 := bstep (se 1 (by rfl) ⟨1660982, by rfl⟩ : syracuseStep 2214643 = 3321965) B3321965
theorem B4982957 : Blo 2213435 4982957 := bbase (se 3 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 4982957 = 1868609) (by norm_num)
theorem B3321971 : Blo 2213435 3321971 := bstep (se 1 (by rfl) ⟨2491478, by rfl⟩ : syracuseStep 3321971 = 4982957) B4982957
theorem B2214647 : Blo 2213435 2214647 := bstep (se 1 (by rfl) ⟨1660985, by rfl⟩ : syracuseStep 2214647 = 3321971) B3321971
theorem B2525477 : Blo 2213435 2525477 := bbase (se 4 (by rfl) ⟨236763, by rfl⟩ : syracuseStep 2525477 = 473527) (by norm_num)
theorem B6734605 : Blo 2213435 6734605 := bstep (se 3 (by rfl) ⟨1262738, by rfl⟩ : syracuseStep 6734605 = 2525477) B2525477
theorem B8979473 : Blo 2213435 8979473 := bstep (se 2 (by rfl) ⟨3367302, by rfl⟩ : syracuseStep 8979473 = 6734605) B6734605
theorem B5986315 : Blo 2213435 5986315 := bstep (se 1 (by rfl) ⟨4489736, by rfl⟩ : syracuseStep 5986315 = 8979473) B8979473
theorem B7981753 : Blo 2213435 7981753 := bstep (se 2 (by rfl) ⟨2993157, by rfl⟩ : syracuseStep 7981753 = 5986315) B5986315
theorem B10642337 : Blo 2213435 10642337 := bstep (se 2 (by rfl) ⟨3990876, by rfl⟩ : syracuseStep 10642337 = 7981753) B7981753
theorem B7094891 : Blo 2213435 7094891 := bstep (se 1 (by rfl) ⟨5321168, by rfl⟩ : syracuseStep 7094891 = 10642337) B10642337
theorem B4729927 : Blo 2213435 4729927 := bstep (se 1 (by rfl) ⟨3547445, by rfl⟩ : syracuseStep 4729927 = 7094891) B7094891
theorem B6306569 : Blo 2213435 6306569 := bstep (se 2 (by rfl) ⟨2364963, by rfl⟩ : syracuseStep 6306569 = 4729927) B4729927
theorem B4204379 : Blo 2213435 4204379 := bstep (se 1 (by rfl) ⟨3153284, by rfl⟩ : syracuseStep 4204379 = 6306569) B6306569
theorem B2802919 : Blo 2213435 2802919 := bstep (se 1 (by rfl) ⟨2102189, by rfl⟩ : syracuseStep 2802919 = 4204379) B4204379
theorem B3737225 : Blo 2213435 3737225 := bstep (se 2 (by rfl) ⟨1401459, by rfl⟩ : syracuseStep 3737225 = 2802919) B2802919
theorem B2491483 : Blo 2213435 2491483 := bstep (se 1 (by rfl) ⟨1868612, by rfl⟩ : syracuseStep 2491483 = 3737225) B3737225
theorem B3321977 : Blo 2213435 3321977 := bstep (se 2 (by rfl) ⟨1245741, by rfl⟩ : syracuseStep 3321977 = 2491483) B2491483
theorem B2214651 : Blo 2213435 2214651 := bstep (se 1 (by rfl) ⟨1660988, by rfl⟩ : syracuseStep 2214651 = 3321977) B3321977
theorem B28379605 : Blo 2213435 28379605 := bbase (se 7 (by rfl) ⟨332573, by rfl⟩ : syracuseStep 28379605 = 665147) (by norm_num)
theorem B37839473 : Blo 2213435 37839473 := bstep (se 2 (by rfl) ⟨14189802, by rfl⟩ : syracuseStep 37839473 = 28379605) B28379605
theorem B25226315 : Blo 2213435 25226315 := bstep (se 1 (by rfl) ⟨18919736, by rfl⟩ : syracuseStep 25226315 = 37839473) B37839473
theorem B16817543 : Blo 2213435 16817543 := bstep (se 1 (by rfl) ⟨12613157, by rfl⟩ : syracuseStep 16817543 = 25226315) B25226315
theorem B11211695 : Blo 2213435 11211695 := bstep (se 1 (by rfl) ⟨8408771, by rfl⟩ : syracuseStep 11211695 = 16817543) B16817543
theorem B7474463 : Blo 2213435 7474463 := bstep (se 1 (by rfl) ⟨5605847, by rfl⟩ : syracuseStep 7474463 = 11211695) B11211695
theorem B4982975 : Blo 2213435 4982975 := bstep (se 1 (by rfl) ⟨3737231, by rfl⟩ : syracuseStep 4982975 = 7474463) B7474463
theorem B3321983 : Blo 2213435 3321983 := bstep (se 1 (by rfl) ⟨2491487, by rfl⟩ : syracuseStep 3321983 = 4982975) B4982975
theorem B2214655 : Blo 2213435 2214655 := bstep (se 1 (by rfl) ⟨1660991, by rfl⟩ : syracuseStep 2214655 = 3321983) B3321983
theorem B3321989 : Blo 2213435 3321989 := bbase (se 4 (by rfl) ⟨311436, by rfl⟩ : syracuseStep 3321989 = 622873) (by norm_num)
theorem B2214659 : Blo 2213435 2214659 := bstep (se 1 (by rfl) ⟨1660994, by rfl⟩ : syracuseStep 2214659 = 3321989) B3321989
theorem B3737245 : Blo 2213435 3737245 := bbase (se 3 (by rfl) ⟨700733, by rfl⟩ : syracuseStep 3737245 = 1401467) (by norm_num)
theorem B4982993 : Blo 2213435 4982993 := bstep (se 2 (by rfl) ⟨1868622, by rfl⟩ : syracuseStep 4982993 = 3737245) B3737245
theorem B3321995 : Blo 2213435 3321995 := bstep (se 1 (by rfl) ⟨2491496, by rfl⟩ : syracuseStep 3321995 = 4982993) B4982993
theorem B2214663 : Blo 2213435 2214663 := bstep (se 1 (by rfl) ⟨1660997, by rfl⟩ : syracuseStep 2214663 = 3321995) B3321995
theorem B2491501 : Blo 2213435 2491501 := bbase (se 3 (by rfl) ⟨467156, by rfl⟩ : syracuseStep 2491501 = 934313) (by norm_num)
theorem B3322001 : Blo 2213435 3322001 := bstep (se 2 (by rfl) ⟨1245750, by rfl⟩ : syracuseStep 3322001 = 2491501) B2491501
theorem B2214667 : Blo 2213435 2214667 := bstep (se 1 (by rfl) ⟨1661000, by rfl⟩ : syracuseStep 2214667 = 3322001) B3322001
theorem B7474517 : Blo 2213435 7474517 := bbase (se 11 (by rfl) ⟨5474, by rfl⟩ : syracuseStep 7474517 = 10949) (by norm_num)
theorem B4983011 : Blo 2213435 4983011 := bstep (se 1 (by rfl) ⟨3737258, by rfl⟩ : syracuseStep 4983011 = 7474517) B7474517
theorem B3322007 : Blo 2213435 3322007 := bstep (se 1 (by rfl) ⟨2491505, by rfl⟩ : syracuseStep 3322007 = 4983011) B4983011
theorem B2214671 : Blo 2213435 2214671 := bstep (se 1 (by rfl) ⟨1661003, by rfl⟩ : syracuseStep 2214671 = 3322007) B3322007
theorem B3322013 : Blo 2213435 3322013 := bbase (se 3 (by rfl) ⟨622877, by rfl⟩ : syracuseStep 3322013 = 1245755) (by norm_num)
theorem B2214675 : Blo 2213435 2214675 := bstep (se 1 (by rfl) ⟨1661006, by rfl⟩ : syracuseStep 2214675 = 3322013) B3322013
theorem B4983029 : Blo 2213435 4983029 := bbase (se 5 (by rfl) ⟨233579, by rfl⟩ : syracuseStep 4983029 = 467159) (by norm_num)
theorem B3322019 : Blo 2213435 3322019 := bstep (se 1 (by rfl) ⟨2491514, by rfl⟩ : syracuseStep 3322019 = 4983029) B4983029
theorem B2214679 : Blo 2213435 2214679 := bstep (se 1 (by rfl) ⟨1661009, by rfl⟩ : syracuseStep 2214679 = 3322019) B3322019
theorem B15963733 : Blo 2213435 15963733 := bbase (se 8 (by rfl) ⟨93537, by rfl⟩ : syracuseStep 15963733 = 187075) (by norm_num)
theorem B21284977 : Blo 2213435 21284977 := bstep (se 2 (by rfl) ⟨7981866, by rfl⟩ : syracuseStep 21284977 = 15963733) B15963733
theorem B28379969 : Blo 2213435 28379969 := bstep (se 2 (by rfl) ⟨10642488, by rfl⟩ : syracuseStep 28379969 = 21284977) B21284977
theorem B18919979 : Blo 2213435 18919979 := bstep (se 1 (by rfl) ⟨14189984, by rfl⟩ : syracuseStep 18919979 = 28379969) B28379969
theorem B12613319 : Blo 2213435 12613319 := bstep (se 1 (by rfl) ⟨9459989, by rfl⟩ : syracuseStep 12613319 = 18919979) B18919979
theorem B8408879 : Blo 2213435 8408879 := bstep (se 1 (by rfl) ⟨6306659, by rfl⟩ : syracuseStep 8408879 = 12613319) B12613319
theorem B5605919 : Blo 2213435 5605919 := bstep (se 1 (by rfl) ⟨4204439, by rfl⟩ : syracuseStep 5605919 = 8408879) B8408879
theorem B3737279 : Blo 2213435 3737279 := bstep (se 1 (by rfl) ⟨2802959, by rfl⟩ : syracuseStep 3737279 = 5605919) B5605919
theorem B2491519 : Blo 2213435 2491519 := bstep (se 1 (by rfl) ⟨1868639, by rfl⟩ : syracuseStep 2491519 = 3737279) B3737279
theorem B3322025 : Blo 2213435 3322025 := bstep (se 2 (by rfl) ⟨1245759, by rfl⟩ : syracuseStep 3322025 = 2491519) B2491519
theorem B2214683 : Blo 2213435 2214683 := bstep (se 1 (by rfl) ⟨1661012, by rfl⟩ : syracuseStep 2214683 = 3322025) B3322025
theorem B3990941 : Blo 2213435 3990941 := bbase (se 3 (by rfl) ⟨748301, by rfl⟩ : syracuseStep 3990941 = 1496603) (by norm_num)
theorem B2660627 : Blo 2213435 2660627 := bstep (se 1 (by rfl) ⟨1995470, by rfl⟩ : syracuseStep 2660627 = 3990941) B3990941
theorem B7095005 : Blo 2213435 7095005 := bstep (se 3 (by rfl) ⟨1330313, by rfl⟩ : syracuseStep 7095005 = 2660627) B2660627
theorem B4730003 : Blo 2213435 4730003 := bstep (se 1 (by rfl) ⟨3547502, by rfl⟩ : syracuseStep 4730003 = 7095005) B7095005
theorem B3153335 : Blo 2213435 3153335 := bstep (se 1 (by rfl) ⟨2365001, by rfl⟩ : syracuseStep 3153335 = 4730003) B4730003
theorem B8408893 : Blo 2213435 8408893 := bstep (se 3 (by rfl) ⟨1576667, by rfl⟩ : syracuseStep 8408893 = 3153335) B3153335
theorem B11211857 : Blo 2213435 11211857 := bstep (se 2 (by rfl) ⟨4204446, by rfl⟩ : syracuseStep 11211857 = 8408893) B8408893
theorem B7474571 : Blo 2213435 7474571 := bstep (se 1 (by rfl) ⟨5605928, by rfl⟩ : syracuseStep 7474571 = 11211857) B11211857
theorem B4983047 : Blo 2213435 4983047 := bstep (se 1 (by rfl) ⟨3737285, by rfl⟩ : syracuseStep 4983047 = 7474571) B7474571
theorem B3322031 : Blo 2213435 3322031 := bstep (se 1 (by rfl) ⟨2491523, by rfl⟩ : syracuseStep 3322031 = 4983047) B4983047
theorem B2214687 : Blo 2213435 2214687 := bstep (se 1 (by rfl) ⟨1661015, by rfl⟩ : syracuseStep 2214687 = 3322031) B3322031
theorem B3322037 : Blo 2213435 3322037 := bbase (se 5 (by rfl) ⟨155720, by rfl⟩ : syracuseStep 3322037 = 311441) (by norm_num)
theorem B2214691 : Blo 2213435 2214691 := bstep (se 1 (by rfl) ⟨1661018, by rfl⟩ : syracuseStep 2214691 = 3322037) B3322037
theorem B5605949 : Blo 2213435 5605949 := bbase (se 3 (by rfl) ⟨1051115, by rfl⟩ : syracuseStep 5605949 = 2102231) (by norm_num)
theorem B3737299 : Blo 2213435 3737299 := bstep (se 1 (by rfl) ⟨2802974, by rfl⟩ : syracuseStep 3737299 = 5605949) B5605949
theorem B4983065 : Blo 2213435 4983065 := bstep (se 2 (by rfl) ⟨1868649, by rfl⟩ : syracuseStep 4983065 = 3737299) B3737299
theorem B3322043 : Blo 2213435 3322043 := bstep (se 1 (by rfl) ⟨2491532, by rfl⟩ : syracuseStep 3322043 = 4983065) B4983065
theorem B2214695 : Blo 2213435 2214695 := bstep (se 1 (by rfl) ⟨1661021, by rfl⟩ : syracuseStep 2214695 = 3322043) B3322043
theorem B2491537 : Blo 2213435 2491537 := bbase (se 2 (by rfl) ⟨934326, by rfl⟩ : syracuseStep 2491537 = 1868653) (by norm_num)
theorem B3322049 : Blo 2213435 3322049 := bstep (se 2 (by rfl) ⟨1245768, by rfl⟩ : syracuseStep 3322049 = 2491537) B2491537
theorem B2214699 : Blo 2213435 2214699 := bstep (se 1 (by rfl) ⟨1661024, by rfl⟩ : syracuseStep 2214699 = 3322049) B3322049
theorem B4204477 : Blo 2213435 4204477 := bbase (se 3 (by rfl) ⟨788339, by rfl⟩ : syracuseStep 4204477 = 1576679) (by norm_num)
theorem B5605969 : Blo 2213435 5605969 := bstep (se 2 (by rfl) ⟨2102238, by rfl⟩ : syracuseStep 5605969 = 4204477) B4204477
theorem B7474625 : Blo 2213435 7474625 := bstep (se 2 (by rfl) ⟨2802984, by rfl⟩ : syracuseStep 7474625 = 5605969) B5605969
theorem B4983083 : Blo 2213435 4983083 := bstep (se 1 (by rfl) ⟨3737312, by rfl⟩ : syracuseStep 4983083 = 7474625) B7474625
theorem B3322055 : Blo 2213435 3322055 := bstep (se 1 (by rfl) ⟨2491541, by rfl⟩ : syracuseStep 3322055 = 4983083) B4983083
theorem B2214703 : Blo 2213435 2214703 := bstep (se 1 (by rfl) ⟨1661027, by rfl⟩ : syracuseStep 2214703 = 3322055) B3322055
theorem B3322061 : Blo 2213435 3322061 := bbase (se 3 (by rfl) ⟨622886, by rfl⟩ : syracuseStep 3322061 = 1245773) (by norm_num)
theorem B2214707 : Blo 2213435 2214707 := bstep (se 1 (by rfl) ⟨1661030, by rfl⟩ : syracuseStep 2214707 = 3322061) B3322061
theorem B4983101 : Blo 2213435 4983101 := bbase (se 3 (by rfl) ⟨934331, by rfl⟩ : syracuseStep 4983101 = 1868663) (by norm_num)
theorem B3322067 : Blo 2213435 3322067 := bstep (se 1 (by rfl) ⟨2491550, by rfl⟩ : syracuseStep 3322067 = 4983101) B4983101
theorem B2214711 : Blo 2213435 2214711 := bstep (se 1 (by rfl) ⟨1661033, by rfl⟩ : syracuseStep 2214711 = 3322067) B3322067
theorem B3737333 : Blo 2213435 3737333 := bbase (se 5 (by rfl) ⟨175187, by rfl⟩ : syracuseStep 3737333 = 350375) (by norm_num)
theorem B2491555 : Blo 2213435 2491555 := bstep (se 1 (by rfl) ⟨1868666, by rfl⟩ : syracuseStep 2491555 = 3737333) B3737333
theorem B3322073 : Blo 2213435 3322073 := bstep (se 2 (by rfl) ⟨1245777, by rfl⟩ : syracuseStep 3322073 = 2491555) B2491555
theorem B2214715 : Blo 2213435 2214715 := bstep (se 1 (by rfl) ⟨1661036, by rfl⟩ : syracuseStep 2214715 = 3322073) B3322073
theorem B10642661 : Blo 2213435 10642661 := bbase (se 4 (by rfl) ⟨997749, by rfl⟩ : syracuseStep 10642661 = 1995499) (by norm_num)
theorem B7095107 : Blo 2213435 7095107 := bstep (se 1 (by rfl) ⟨5321330, by rfl⟩ : syracuseStep 7095107 = 10642661) B10642661
theorem B4730071 : Blo 2213435 4730071 := bstep (se 1 (by rfl) ⟨3547553, by rfl⟩ : syracuseStep 4730071 = 7095107) B7095107
theorem B6306761 : Blo 2213435 6306761 := bstep (se 2 (by rfl) ⟨2365035, by rfl⟩ : syracuseStep 6306761 = 4730071) B4730071
theorem B16818029 : Blo 2213435 16818029 := bstep (se 3 (by rfl) ⟨3153380, by rfl⟩ : syracuseStep 16818029 = 6306761) B6306761
theorem B11212019 : Blo 2213435 11212019 := bstep (se 1 (by rfl) ⟨8409014, by rfl⟩ : syracuseStep 11212019 = 16818029) B16818029
theorem B7474679 : Blo 2213435 7474679 := bstep (se 1 (by rfl) ⟨5606009, by rfl⟩ : syracuseStep 7474679 = 11212019) B11212019
theorem B4983119 : Blo 2213435 4983119 := bstep (se 1 (by rfl) ⟨3737339, by rfl⟩ : syracuseStep 4983119 = 7474679) B7474679
theorem B3322079 : Blo 2213435 3322079 := bstep (se 1 (by rfl) ⟨2491559, by rfl⟩ : syracuseStep 3322079 = 4983119) B4983119
theorem B2214719 : Blo 2213435 2214719 := bstep (se 1 (by rfl) ⟨1661039, by rfl⟩ : syracuseStep 2214719 = 3322079) B3322079
theorem B3322085 : Blo 2213435 3322085 := bbase (se 4 (by rfl) ⟨311445, by rfl⟩ : syracuseStep 3322085 = 622891) (by norm_num)
theorem B2214723 : Blo 2213435 2214723 := bstep (se 1 (by rfl) ⟨1661042, by rfl⟩ : syracuseStep 2214723 = 3322085) B3322085
theorem B8979781 : Blo 2213435 8979781 := bbase (se 4 (by rfl) ⟨841854, by rfl⟩ : syracuseStep 8979781 = 1683709) (by norm_num)
theorem B11973041 : Blo 2213435 11973041 := bstep (se 2 (by rfl) ⟨4489890, by rfl⟩ : syracuseStep 11973041 = 8979781) B8979781
theorem B7982027 : Blo 2213435 7982027 := bstep (se 1 (by rfl) ⟨5986520, by rfl⟩ : syracuseStep 7982027 = 11973041) B11973041
theorem B5321351 : Blo 2213435 5321351 := bstep (se 1 (by rfl) ⟨3991013, by rfl⟩ : syracuseStep 5321351 = 7982027) B7982027
theorem B3547567 : Blo 2213435 3547567 := bstep (se 1 (by rfl) ⟨2660675, by rfl⟩ : syracuseStep 3547567 = 5321351) B5321351
theorem B4730089 : Blo 2213435 4730089 := bstep (se 2 (by rfl) ⟨1773783, by rfl⟩ : syracuseStep 4730089 = 3547567) B3547567
theorem B6306785 : Blo 2213435 6306785 := bstep (se 2 (by rfl) ⟨2365044, by rfl⟩ : syracuseStep 6306785 = 4730089) B4730089
theorem B4204523 : Blo 2213435 4204523 := bstep (se 1 (by rfl) ⟨3153392, by rfl⟩ : syracuseStep 4204523 = 6306785) B6306785
theorem B2803015 : Blo 2213435 2803015 := bstep (se 1 (by rfl) ⟨2102261, by rfl⟩ : syracuseStep 2803015 = 4204523) B4204523
theorem B3737353 : Blo 2213435 3737353 := bstep (se 2 (by rfl) ⟨1401507, by rfl⟩ : syracuseStep 3737353 = 2803015) B2803015
theorem B4983137 : Blo 2213435 4983137 := bstep (se 2 (by rfl) ⟨1868676, by rfl⟩ : syracuseStep 4983137 = 3737353) B3737353
theorem B3322091 : Blo 2213435 3322091 := bstep (se 1 (by rfl) ⟨2491568, by rfl⟩ : syracuseStep 3322091 = 4983137) B4983137
theorem B2214727 : Blo 2213435 2214727 := bstep (se 1 (by rfl) ⟨1661045, by rfl⟩ : syracuseStep 2214727 = 3322091) B3322091
theorem B2491573 : Blo 2213435 2491573 := bbase (se 5 (by rfl) ⟨116792, by rfl⟩ : syracuseStep 2491573 = 233585) (by norm_num)
theorem B3322097 : Blo 2213435 3322097 := bstep (se 2 (by rfl) ⟨1245786, by rfl⟩ : syracuseStep 3322097 = 2491573) B2491573
theorem B2214731 : Blo 2213435 2214731 := bstep (se 1 (by rfl) ⟨1661048, by rfl⟩ : syracuseStep 2214731 = 3322097) B3322097
theorem B2803025 : Blo 2213435 2803025 := bbase (se 2 (by rfl) ⟨1051134, by rfl⟩ : syracuseStep 2803025 = 2102269) (by norm_num)
theorem B7474733 : Blo 2213435 7474733 := bstep (se 3 (by rfl) ⟨1401512, by rfl⟩ : syracuseStep 7474733 = 2803025) B2803025
theorem B4983155 : Blo 2213435 4983155 := bstep (se 1 (by rfl) ⟨3737366, by rfl⟩ : syracuseStep 4983155 = 7474733) B7474733
theorem B3322103 : Blo 2213435 3322103 := bstep (se 1 (by rfl) ⟨2491577, by rfl⟩ : syracuseStep 3322103 = 4983155) B4983155
theorem B2214735 : Blo 2213435 2214735 := bstep (se 1 (by rfl) ⟨1661051, by rfl⟩ : syracuseStep 2214735 = 3322103) B3322103
theorem B3322109 : Blo 2213435 3322109 := bbase (se 3 (by rfl) ⟨622895, by rfl⟩ : syracuseStep 3322109 = 1245791) (by norm_num)
theorem B2214739 : Blo 2213435 2214739 := bstep (se 1 (by rfl) ⟨1661054, by rfl⟩ : syracuseStep 2214739 = 3322109) B3322109
theorem B4983173 : Blo 2213435 4983173 := bbase (se 4 (by rfl) ⟨467172, by rfl⟩ : syracuseStep 4983173 = 934345) (by norm_num)
theorem B3322115 : Blo 2213435 3322115 := bstep (se 1 (by rfl) ⟨2491586, by rfl⟩ : syracuseStep 3322115 = 4983173) B4983173
theorem B2214743 : Blo 2213435 2214743 := bstep (se 1 (by rfl) ⟨1661057, by rfl⟩ : syracuseStep 2214743 = 3322115) B3322115
theorem B3153421 : Blo 2213435 3153421 := bbase (se 3 (by rfl) ⟨591266, by rfl⟩ : syracuseStep 3153421 = 1182533) (by norm_num)
theorem B4204561 : Blo 2213435 4204561 := bstep (se 2 (by rfl) ⟨1576710, by rfl⟩ : syracuseStep 4204561 = 3153421) B3153421
theorem B5606081 : Blo 2213435 5606081 := bstep (se 2 (by rfl) ⟨2102280, by rfl⟩ : syracuseStep 5606081 = 4204561) B4204561
theorem B3737387 : Blo 2213435 3737387 := bstep (se 1 (by rfl) ⟨2803040, by rfl⟩ : syracuseStep 3737387 = 5606081) B5606081
theorem B2491591 : Blo 2213435 2491591 := bstep (se 1 (by rfl) ⟨1868693, by rfl⟩ : syracuseStep 2491591 = 3737387) B3737387
theorem B3322121 : Blo 2213435 3322121 := bstep (se 2 (by rfl) ⟨1245795, by rfl⟩ : syracuseStep 3322121 = 2491591) B2491591
theorem B2214747 : Blo 2213435 2214747 := bstep (se 1 (by rfl) ⟨1661060, by rfl⟩ : syracuseStep 2214747 = 3322121) B3322121
theorem B11212181 : Blo 2213435 11212181 := bbase (se 6 (by rfl) ⟨262785, by rfl⟩ : syracuseStep 11212181 = 525571) (by norm_num)
theorem B7474787 : Blo 2213435 7474787 := bstep (se 1 (by rfl) ⟨5606090, by rfl⟩ : syracuseStep 7474787 = 11212181) B11212181
theorem B4983191 : Blo 2213435 4983191 := bstep (se 1 (by rfl) ⟨3737393, by rfl⟩ : syracuseStep 4983191 = 7474787) B7474787
theorem B3322127 : Blo 2213435 3322127 := bstep (se 1 (by rfl) ⟨2491595, by rfl⟩ : syracuseStep 3322127 = 4983191) B4983191
theorem B2214751 : Blo 2213435 2214751 := bstep (se 1 (by rfl) ⟨1661063, by rfl⟩ : syracuseStep 2214751 = 3322127) B3322127
theorem B3322133 : Blo 2213435 3322133 := bbase (se 6 (by rfl) ⟨77862, by rfl⟩ : syracuseStep 3322133 = 155725) (by norm_num)
theorem B2214755 : Blo 2213435 2214755 := bstep (se 1 (by rfl) ⟨1661066, by rfl⟩ : syracuseStep 2214755 = 3322133) B3322133
theorem B10642853 : Blo 2213435 10642853 := bbase (se 4 (by rfl) ⟨997767, by rfl⟩ : syracuseStep 10642853 = 1995535) (by norm_num)
theorem B28380941 : Blo 2213435 28380941 := bstep (se 3 (by rfl) ⟨5321426, by rfl⟩ : syracuseStep 28380941 = 10642853) B10642853
theorem B18920627 : Blo 2213435 18920627 := bstep (se 1 (by rfl) ⟨14190470, by rfl⟩ : syracuseStep 18920627 = 28380941) B28380941
theorem B12613751 : Blo 2213435 12613751 := bstep (se 1 (by rfl) ⟨9460313, by rfl⟩ : syracuseStep 12613751 = 18920627) B18920627
theorem B8409167 : Blo 2213435 8409167 := bstep (se 1 (by rfl) ⟨6306875, by rfl⟩ : syracuseStep 8409167 = 12613751) B12613751
theorem B5606111 : Blo 2213435 5606111 := bstep (se 1 (by rfl) ⟨4204583, by rfl⟩ : syracuseStep 5606111 = 8409167) B8409167
theorem B3737407 : Blo 2213435 3737407 := bstep (se 1 (by rfl) ⟨2803055, by rfl⟩ : syracuseStep 3737407 = 5606111) B5606111
theorem B4983209 : Blo 2213435 4983209 := bstep (se 2 (by rfl) ⟨1868703, by rfl⟩ : syracuseStep 4983209 = 3737407) B3737407
theorem B3322139 : Blo 2213435 3322139 := bstep (se 1 (by rfl) ⟨2491604, by rfl⟩ : syracuseStep 3322139 = 4983209) B4983209
theorem B2214759 : Blo 2213435 2214759 := bstep (se 1 (by rfl) ⟨1661069, by rfl⟩ : syracuseStep 2214759 = 3322139) B3322139
theorem B2491609 : Blo 2213435 2491609 := bbase (se 2 (by rfl) ⟨934353, by rfl⟩ : syracuseStep 2491609 = 1868707) (by norm_num)
theorem B3322145 : Blo 2213435 3322145 := bstep (se 2 (by rfl) ⟨1245804, by rfl⟩ : syracuseStep 3322145 = 2491609) B2491609
theorem B2214763 : Blo 2213435 2214763 := bstep (se 1 (by rfl) ⟨1661072, by rfl⟩ : syracuseStep 2214763 = 3322145) B3322145
theorem B8640229 : Blo 2213435 8640229 := bbase (se 4 (by rfl) ⟨810021, by rfl⟩ : syracuseStep 8640229 = 1620043) (by norm_num)
theorem B11520305 : Blo 2213435 11520305 := bstep (se 2 (by rfl) ⟨4320114, by rfl⟩ : syracuseStep 11520305 = 8640229) B8640229
theorem B7680203 : Blo 2213435 7680203 := bstep (se 1 (by rfl) ⟨5760152, by rfl⟩ : syracuseStep 7680203 = 11520305) B11520305
theorem B5120135 : Blo 2213435 5120135 := bstep (se 1 (by rfl) ⟨3840101, by rfl⟩ : syracuseStep 5120135 = 7680203) B7680203
theorem B3413423 : Blo 2213435 3413423 := bstep (se 1 (by rfl) ⟨2560067, by rfl⟩ : syracuseStep 3413423 = 5120135) B5120135
theorem B9102461 : Blo 2213435 9102461 := bstep (se 3 (by rfl) ⟨1706711, by rfl⟩ : syracuseStep 9102461 = 3413423) B3413423
theorem B24273229 : Blo 2213435 24273229 := bstep (se 3 (by rfl) ⟨4551230, by rfl⟩ : syracuseStep 24273229 = 9102461) B9102461
theorem B32364305 : Blo 2213435 32364305 := bstep (se 2 (by rfl) ⟨12136614, by rfl⟩ : syracuseStep 32364305 = 24273229) B24273229
theorem B21576203 : Blo 2213435 21576203 := bstep (se 1 (by rfl) ⟨16182152, by rfl⟩ : syracuseStep 21576203 = 32364305) B32364305
theorem B14384135 : Blo 2213435 14384135 := bstep (se 1 (by rfl) ⟨10788101, by rfl⟩ : syracuseStep 14384135 = 21576203) B21576203
theorem B9589423 : Blo 2213435 9589423 := bstep (se 1 (by rfl) ⟨7192067, by rfl⟩ : syracuseStep 9589423 = 14384135) B14384135
theorem B12785897 : Blo 2213435 12785897 := bstep (se 2 (by rfl) ⟨4794711, by rfl⟩ : syracuseStep 12785897 = 9589423) B9589423
theorem B34095725 : Blo 2213435 34095725 := bstep (se 3 (by rfl) ⟨6392948, by rfl⟩ : syracuseStep 34095725 = 12785897) B12785897
theorem B22730483 : Blo 2213435 22730483 := bstep (se 1 (by rfl) ⟨17047862, by rfl⟩ : syracuseStep 22730483 = 34095725) B34095725
theorem B15153655 : Blo 2213435 15153655 := bstep (se 1 (by rfl) ⟨11365241, by rfl⟩ : syracuseStep 15153655 = 22730483) B22730483
theorem B20204873 : Blo 2213435 20204873 := bstep (se 2 (by rfl) ⟨7576827, by rfl⟩ : syracuseStep 20204873 = 15153655) B15153655
theorem B13469915 : Blo 2213435 13469915 := bstep (se 1 (by rfl) ⟨10102436, by rfl⟩ : syracuseStep 13469915 = 20204873) B20204873
theorem B8979943 : Blo 2213435 8979943 := bstep (se 1 (by rfl) ⟨6734957, by rfl⟩ : syracuseStep 8979943 = 13469915) B13469915
theorem B11973257 : Blo 2213435 11973257 := bstep (se 2 (by rfl) ⟨4489971, by rfl⟩ : syracuseStep 11973257 = 8979943) B8979943
theorem B7982171 : Blo 2213435 7982171 := bstep (se 1 (by rfl) ⟨5986628, by rfl⟩ : syracuseStep 7982171 = 11973257) B11973257
theorem B5321447 : Blo 2213435 5321447 := bstep (se 1 (by rfl) ⟨3991085, by rfl⟩ : syracuseStep 5321447 = 7982171) B7982171
theorem B3547631 : Blo 2213435 3547631 := bstep (se 1 (by rfl) ⟨2660723, by rfl⟩ : syracuseStep 3547631 = 5321447) B5321447
theorem B2365087 : Blo 2213435 2365087 := bstep (se 1 (by rfl) ⟨1773815, by rfl⟩ : syracuseStep 2365087 = 3547631) B3547631
theorem B3153449 : Blo 2213435 3153449 := bstep (se 2 (by rfl) ⟨1182543, by rfl⟩ : syracuseStep 3153449 = 2365087) B2365087
theorem B8409197 : Blo 2213435 8409197 := bstep (se 3 (by rfl) ⟨1576724, by rfl⟩ : syracuseStep 8409197 = 3153449) B3153449
theorem B5606131 : Blo 2213435 5606131 := bstep (se 1 (by rfl) ⟨4204598, by rfl⟩ : syracuseStep 5606131 = 8409197) B8409197
theorem B7474841 : Blo 2213435 7474841 := bstep (se 2 (by rfl) ⟨2803065, by rfl⟩ : syracuseStep 7474841 = 5606131) B5606131
theorem B4983227 : Blo 2213435 4983227 := bstep (se 1 (by rfl) ⟨3737420, by rfl⟩ : syracuseStep 4983227 = 7474841) B7474841
theorem B3322151 : Blo 2213435 3322151 := bstep (se 1 (by rfl) ⟨2491613, by rfl⟩ : syracuseStep 3322151 = 4983227) B4983227
theorem B2214767 : Blo 2213435 2214767 := bstep (se 1 (by rfl) ⟨1661075, by rfl⟩ : syracuseStep 2214767 = 3322151) B3322151
theorem B3322157 : Blo 2213435 3322157 := bbase (se 3 (by rfl) ⟨622904, by rfl⟩ : syracuseStep 3322157 = 1245809) (by norm_num)
theorem B2214771 : Blo 2213435 2214771 := bstep (se 1 (by rfl) ⟨1661078, by rfl⟩ : syracuseStep 2214771 = 3322157) B3322157
theorem B4983245 : Blo 2213435 4983245 := bbase (se 3 (by rfl) ⟨934358, by rfl⟩ : syracuseStep 4983245 = 1868717) (by norm_num)
theorem B3322163 : Blo 2213435 3322163 := bstep (se 1 (by rfl) ⟨2491622, by rfl⟩ : syracuseStep 3322163 = 4983245) B4983245
theorem B2214775 : Blo 2213435 2214775 := bstep (se 1 (by rfl) ⟨1661081, by rfl⟩ : syracuseStep 2214775 = 3322163) B3322163
theorem B2803081 : Blo 2213435 2803081 := bbase (se 2 (by rfl) ⟨1051155, by rfl⟩ : syracuseStep 2803081 = 2102311) (by norm_num)
theorem B3737441 : Blo 2213435 3737441 := bstep (se 2 (by rfl) ⟨1401540, by rfl⟩ : syracuseStep 3737441 = 2803081) B2803081
theorem B2491627 : Blo 2213435 2491627 := bstep (se 1 (by rfl) ⟨1868720, by rfl⟩ : syracuseStep 2491627 = 3737441) B3737441
theorem B3322169 : Blo 2213435 3322169 := bstep (se 2 (by rfl) ⟨1245813, by rfl⟩ : syracuseStep 3322169 = 2491627) B2491627
theorem B2214779 : Blo 2213435 2214779 := bstep (se 1 (by rfl) ⟨1661084, by rfl⟩ : syracuseStep 2214779 = 3322169) B3322169
theorem B8523989 : Blo 2213435 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B5682659 : Blo 2213435 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B60615029 : Blo 2213435 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B40410019 : Blo 2213435 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B53880025 : Blo 2213435 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B71840033 : Blo 2213435 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B47893355 : Blo 2213435 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B31928903 : Blo 2213435 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B21285935 : Blo 2213435 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B14190623 : Blo 2213435 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B9460415 : Blo 2213435 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B25227773 : Blo 2213435 25227773 := bstep (se 3 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 25227773 = 9460415) B9460415
theorem B16818515 : Blo 2213435 16818515 := bstep (se 1 (by rfl) ⟨12613886, by rfl⟩ : syracuseStep 16818515 = 25227773) B25227773
theorem B11212343 : Blo 2213435 11212343 := bstep (se 1 (by rfl) ⟨8409257, by rfl⟩ : syracuseStep 11212343 = 16818515) B16818515
theorem B7474895 : Blo 2213435 7474895 := bstep (se 1 (by rfl) ⟨5606171, by rfl⟩ : syracuseStep 7474895 = 11212343) B11212343
theorem B4983263 : Blo 2213435 4983263 := bstep (se 1 (by rfl) ⟨3737447, by rfl⟩ : syracuseStep 4983263 = 7474895) B7474895
theorem B3322175 : Blo 2213435 3322175 := bstep (se 1 (by rfl) ⟨2491631, by rfl⟩ : syracuseStep 3322175 = 4983263) B4983263
theorem B2214783 : Blo 2213435 2214783 := bstep (se 1 (by rfl) ⟨1661087, by rfl⟩ : syracuseStep 2214783 = 3322175) B3322175
theorem B3322181 : Blo 2213435 3322181 := bbase (se 4 (by rfl) ⟨311454, by rfl⟩ : syracuseStep 3322181 = 622909) (by norm_num)
theorem B2214787 : Blo 2213435 2214787 := bstep (se 1 (by rfl) ⟨1661090, by rfl⟩ : syracuseStep 2214787 = 3322181) B3322181
theorem B3737461 : Blo 2213435 3737461 := bbase (se 5 (by rfl) ⟨175193, by rfl⟩ : syracuseStep 3737461 = 350387) (by norm_num)
theorem B4983281 : Blo 2213435 4983281 := bstep (se 2 (by rfl) ⟨1868730, by rfl⟩ : syracuseStep 4983281 = 3737461) B3737461
theorem B3322187 : Blo 2213435 3322187 := bstep (se 1 (by rfl) ⟨2491640, by rfl⟩ : syracuseStep 3322187 = 4983281) B4983281
theorem B2214791 : Blo 2213435 2214791 := bstep (se 1 (by rfl) ⟨1661093, by rfl⟩ : syracuseStep 2214791 = 3322187) B3322187
theorem B2491645 : Blo 2213435 2491645 := bbase (se 3 (by rfl) ⟨467183, by rfl⟩ : syracuseStep 2491645 = 934367) (by norm_num)
theorem B3322193 : Blo 2213435 3322193 := bstep (se 2 (by rfl) ⟨1245822, by rfl⟩ : syracuseStep 3322193 = 2491645) B2491645
theorem B2214795 : Blo 2213435 2214795 := bstep (se 1 (by rfl) ⟨1661096, by rfl⟩ : syracuseStep 2214795 = 3322193) B3322193
theorem B7474949 : Blo 2213435 7474949 := bbase (se 4 (by rfl) ⟨700776, by rfl⟩ : syracuseStep 7474949 = 1401553) (by norm_num)
theorem B4983299 : Blo 2213435 4983299 := bstep (se 1 (by rfl) ⟨3737474, by rfl⟩ : syracuseStep 4983299 = 7474949) B7474949
theorem B3322199 : Blo 2213435 3322199 := bstep (se 1 (by rfl) ⟨2491649, by rfl⟩ : syracuseStep 3322199 = 4983299) B4983299
theorem B2214799 : Blo 2213435 2214799 := bstep (se 1 (by rfl) ⟨1661099, by rfl⟩ : syracuseStep 2214799 = 3322199) B3322199
theorem B3322205 : Blo 2213435 3322205 := bbase (se 3 (by rfl) ⟨622913, by rfl⟩ : syracuseStep 3322205 = 1245827) (by norm_num)
theorem B2214803 : Blo 2213435 2214803 := bstep (se 1 (by rfl) ⟨1661102, by rfl⟩ : syracuseStep 2214803 = 3322205) B3322205
theorem B4983317 : Blo 2213435 4983317 := bbase (se 6 (by rfl) ⟨116796, by rfl⟩ : syracuseStep 4983317 = 233593) (by norm_num)
theorem B3322211 : Blo 2213435 3322211 := bstep (se 1 (by rfl) ⟨2491658, by rfl⟩ : syracuseStep 3322211 = 4983317) B4983317
theorem B2214807 : Blo 2213435 2214807 := bstep (se 1 (by rfl) ⟨1661105, by rfl⟩ : syracuseStep 2214807 = 3322211) B3322211
theorem B8409365 : Blo 2213435 8409365 := bbase (se 6 (by rfl) ⟨197094, by rfl⟩ : syracuseStep 8409365 = 394189) (by norm_num)
theorem B5606243 : Blo 2213435 5606243 := bstep (se 1 (by rfl) ⟨4204682, by rfl⟩ : syracuseStep 5606243 = 8409365) B8409365
theorem B3737495 : Blo 2213435 3737495 := bstep (se 1 (by rfl) ⟨2803121, by rfl⟩ : syracuseStep 3737495 = 5606243) B5606243
theorem B2491663 : Blo 2213435 2491663 := bstep (se 1 (by rfl) ⟨1868747, by rfl⟩ : syracuseStep 2491663 = 3737495) B3737495
theorem B3322217 : Blo 2213435 3322217 := bstep (se 2 (by rfl) ⟨1245831, by rfl⟩ : syracuseStep 3322217 = 2491663) B2491663
theorem B2214811 : Blo 2213435 2214811 := bstep (se 1 (by rfl) ⟨1661108, by rfl⟩ : syracuseStep 2214811 = 3322217) B3322217
theorem B12614069 : Blo 2213435 12614069 := bbase (se 5 (by rfl) ⟨591284, by rfl⟩ : syracuseStep 12614069 = 1182569) (by norm_num)
theorem B8409379 : Blo 2213435 8409379 := bstep (se 1 (by rfl) ⟨6307034, by rfl⟩ : syracuseStep 8409379 = 12614069) B12614069
theorem B11212505 : Blo 2213435 11212505 := bstep (se 2 (by rfl) ⟨4204689, by rfl⟩ : syracuseStep 11212505 = 8409379) B8409379
theorem B7475003 : Blo 2213435 7475003 := bstep (se 1 (by rfl) ⟨5606252, by rfl⟩ : syracuseStep 7475003 = 11212505) B11212505
theorem B4983335 : Blo 2213435 4983335 := bstep (se 1 (by rfl) ⟨3737501, by rfl⟩ : syracuseStep 4983335 = 7475003) B7475003
theorem B3322223 : Blo 2213435 3322223 := bstep (se 1 (by rfl) ⟨2491667, by rfl⟩ : syracuseStep 3322223 = 4983335) B4983335
theorem B2214815 : Blo 2213435 2214815 := bstep (se 1 (by rfl) ⟨1661111, by rfl⟩ : syracuseStep 2214815 = 3322223) B3322223
theorem B3322229 : Blo 2213435 3322229 := bbase (se 5 (by rfl) ⟨155729, by rfl⟩ : syracuseStep 3322229 = 311459) (by norm_num)
theorem B2214819 : Blo 2213435 2214819 := bstep (se 1 (by rfl) ⟨1661114, by rfl⟩ : syracuseStep 2214819 = 3322229) B3322229
theorem B3367565 : Blo 2213435 3367565 := bbase (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) (by norm_num)
theorem B2245043 : Blo 2213435 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B5986781 : Blo 2213435 5986781 := bstep (se 3 (by rfl) ⟨1122521, by rfl⟩ : syracuseStep 5986781 = 2245043) B2245043
theorem B3991187 : Blo 2213435 3991187 := bstep (se 1 (by rfl) ⟨2993390, by rfl⟩ : syracuseStep 3991187 = 5986781) B5986781
theorem B2660791 : Blo 2213435 2660791 := bstep (se 1 (by rfl) ⟨1995593, by rfl⟩ : syracuseStep 2660791 = 3991187) B3991187
theorem B3547721 : Blo 2213435 3547721 := bstep (se 2 (by rfl) ⟨1330395, by rfl⟩ : syracuseStep 3547721 = 2660791) B2660791
theorem B2365147 : Blo 2213435 2365147 := bstep (se 1 (by rfl) ⟨1773860, by rfl⟩ : syracuseStep 2365147 = 3547721) B3547721
theorem B3153529 : Blo 2213435 3153529 := bstep (se 2 (by rfl) ⟨1182573, by rfl⟩ : syracuseStep 3153529 = 2365147) B2365147
theorem B4204705 : Blo 2213435 4204705 := bstep (se 2 (by rfl) ⟨1576764, by rfl⟩ : syracuseStep 4204705 = 3153529) B3153529
theorem B5606273 : Blo 2213435 5606273 := bstep (se 2 (by rfl) ⟨2102352, by rfl⟩ : syracuseStep 5606273 = 4204705) B4204705
theorem B3737515 : Blo 2213435 3737515 := bstep (se 1 (by rfl) ⟨2803136, by rfl⟩ : syracuseStep 3737515 = 5606273) B5606273
theorem B4983353 : Blo 2213435 4983353 := bstep (se 2 (by rfl) ⟨1868757, by rfl⟩ : syracuseStep 4983353 = 3737515) B3737515
theorem B3322235 : Blo 2213435 3322235 := bstep (se 1 (by rfl) ⟨2491676, by rfl⟩ : syracuseStep 3322235 = 4983353) B4983353
theorem B2214823 : Blo 2213435 2214823 := bstep (se 1 (by rfl) ⟨1661117, by rfl⟩ : syracuseStep 2214823 = 3322235) B3322235
theorem B2491681 : Blo 2213435 2491681 := bbase (se 2 (by rfl) ⟨934380, by rfl⟩ : syracuseStep 2491681 = 1868761) (by norm_num)
theorem B3322241 : Blo 2213435 3322241 := bstep (se 2 (by rfl) ⟨1245840, by rfl⟩ : syracuseStep 3322241 = 2491681) B2491681
theorem B2214827 : Blo 2213435 2214827 := bstep (se 1 (by rfl) ⟨1661120, by rfl⟩ : syracuseStep 2214827 = 3322241) B3322241
theorem B5606293 : Blo 2213435 5606293 := bbase (se 6 (by rfl) ⟨131397, by rfl⟩ : syracuseStep 5606293 = 262795) (by norm_num)
theorem B7475057 : Blo 2213435 7475057 := bstep (se 2 (by rfl) ⟨2803146, by rfl⟩ : syracuseStep 7475057 = 5606293) B5606293
theorem B4983371 : Blo 2213435 4983371 := bstep (se 1 (by rfl) ⟨3737528, by rfl⟩ : syracuseStep 4983371 = 7475057) B7475057
theorem B3322247 : Blo 2213435 3322247 := bstep (se 1 (by rfl) ⟨2491685, by rfl⟩ : syracuseStep 3322247 = 4983371) B4983371
theorem B2214831 : Blo 2213435 2214831 := bstep (se 1 (by rfl) ⟨1661123, by rfl⟩ : syracuseStep 2214831 = 3322247) B3322247
theorem B3322253 : Blo 2213435 3322253 := bbase (se 3 (by rfl) ⟨622922, by rfl⟩ : syracuseStep 3322253 = 1245845) (by norm_num)
theorem B2214835 : Blo 2213435 2214835 := bstep (se 1 (by rfl) ⟨1661126, by rfl⟩ : syracuseStep 2214835 = 3322253) B3322253
theorem B4983389 : Blo 2213435 4983389 := bbase (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) (by norm_num)
theorem B3322259 : Blo 2213435 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B2214839 : Blo 2213435 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B3737549 : Blo 2213435 3737549 := bbase (se 3 (by rfl) ⟨700790, by rfl⟩ : syracuseStep 3737549 = 1401581) (by norm_num)
theorem B2491699 : Blo 2213435 2491699 := bstep (se 1 (by rfl) ⟨1868774, by rfl⟩ : syracuseStep 2491699 = 3737549) B3737549
theorem B3322265 : Blo 2213435 3322265 := bstep (se 2 (by rfl) ⟨1245849, by rfl⟩ : syracuseStep 3322265 = 2491699) B2491699
theorem B2214843 : Blo 2213435 2214843 := bstep (se 1 (by rfl) ⟨1661132, by rfl⟩ : syracuseStep 2214843 = 3322265) B3322265
theorem B11973685 : Blo 2213435 11973685 := bbase (se 5 (by rfl) ⟨561266, by rfl⟩ : syracuseStep 11973685 = 1122533) (by norm_num)
theorem B15964913 : Blo 2213435 15964913 := bstep (se 2 (by rfl) ⟨5986842, by rfl⟩ : syracuseStep 15964913 = 11973685) B11973685
theorem B10643275 : Blo 2213435 10643275 := bstep (se 1 (by rfl) ⟨7982456, by rfl⟩ : syracuseStep 10643275 = 15964913) B15964913
theorem B14191033 : Blo 2213435 14191033 := bstep (se 2 (by rfl) ⟨5321637, by rfl⟩ : syracuseStep 14191033 = 10643275) B10643275
theorem B18921377 : Blo 2213435 18921377 := bstep (se 2 (by rfl) ⟨7095516, by rfl⟩ : syracuseStep 18921377 = 14191033) B14191033
theorem B12614251 : Blo 2213435 12614251 := bstep (se 1 (by rfl) ⟨9460688, by rfl⟩ : syracuseStep 12614251 = 18921377) B18921377
theorem B16819001 : Blo 2213435 16819001 := bstep (se 2 (by rfl) ⟨6307125, by rfl⟩ : syracuseStep 16819001 = 12614251) B12614251
theorem B11212667 : Blo 2213435 11212667 := bstep (se 1 (by rfl) ⟨8409500, by rfl⟩ : syracuseStep 11212667 = 16819001) B16819001
theorem B7475111 : Blo 2213435 7475111 := bstep (se 1 (by rfl) ⟨5606333, by rfl⟩ : syracuseStep 7475111 = 11212667) B11212667
theorem B4983407 : Blo 2213435 4983407 := bstep (se 1 (by rfl) ⟨3737555, by rfl⟩ : syracuseStep 4983407 = 7475111) B7475111
theorem B3322271 : Blo 2213435 3322271 := bstep (se 1 (by rfl) ⟨2491703, by rfl⟩ : syracuseStep 3322271 = 4983407) B4983407
theorem B2214847 : Blo 2213435 2214847 := bstep (se 1 (by rfl) ⟨1661135, by rfl⟩ : syracuseStep 2214847 = 3322271) B3322271
theorem B3322277 : Blo 2213435 3322277 := bbase (se 4 (by rfl) ⟨311463, by rfl⟩ : syracuseStep 3322277 = 622927) (by norm_num)
theorem B2214851 : Blo 2213435 2214851 := bstep (se 1 (by rfl) ⟨1661138, by rfl⟩ : syracuseStep 2214851 = 3322277) B3322277
theorem B2803177 : Blo 2213435 2803177 := bbase (se 2 (by rfl) ⟨1051191, by rfl⟩ : syracuseStep 2803177 = 2102383) (by norm_num)
theorem B3737569 : Blo 2213435 3737569 := bstep (se 2 (by rfl) ⟨1401588, by rfl⟩ : syracuseStep 3737569 = 2803177) B2803177
theorem B4983425 : Blo 2213435 4983425 := bstep (se 2 (by rfl) ⟨1868784, by rfl⟩ : syracuseStep 4983425 = 3737569) B3737569
theorem B3322283 : Blo 2213435 3322283 := bstep (se 1 (by rfl) ⟨2491712, by rfl⟩ : syracuseStep 3322283 = 4983425) B4983425
theorem B2214855 : Blo 2213435 2214855 := bstep (se 1 (by rfl) ⟨1661141, by rfl⟩ : syracuseStep 2214855 = 3322283) B3322283
theorem B2491717 : Blo 2213435 2491717 := bbase (se 4 (by rfl) ⟨233598, by rfl⟩ : syracuseStep 2491717 = 467197) (by norm_num)
theorem B3322289 : Blo 2213435 3322289 := bstep (se 2 (by rfl) ⟨1245858, by rfl⟩ : syracuseStep 3322289 = 2491717) B2491717
theorem B2214859 : Blo 2213435 2214859 := bstep (se 1 (by rfl) ⟨1661144, by rfl⟩ : syracuseStep 2214859 = 3322289) B3322289
theorem B4204781 : Blo 2213435 4204781 := bbase (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) (by norm_num)
theorem B2803187 : Blo 2213435 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B7475165 : Blo 2213435 7475165 := bstep (se 3 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 7475165 = 2803187) B2803187
theorem B4983443 : Blo 2213435 4983443 := bstep (se 1 (by rfl) ⟨3737582, by rfl⟩ : syracuseStep 4983443 = 7475165) B7475165
theorem B3322295 : Blo 2213435 3322295 := bstep (se 1 (by rfl) ⟨2491721, by rfl⟩ : syracuseStep 3322295 = 4983443) B4983443
theorem B2214863 : Blo 2213435 2214863 := bstep (se 1 (by rfl) ⟨1661147, by rfl⟩ : syracuseStep 2214863 = 3322295) B3322295
theorem B3322301 : Blo 2213435 3322301 := bbase (se 3 (by rfl) ⟨622931, by rfl⟩ : syracuseStep 3322301 = 1245863) (by norm_num)
theorem B2214867 : Blo 2213435 2214867 := bstep (se 1 (by rfl) ⟨1661150, by rfl⟩ : syracuseStep 2214867 = 3322301) B3322301
theorem B4983461 : Blo 2213435 4983461 := bbase (se 4 (by rfl) ⟨467199, by rfl⟩ : syracuseStep 4983461 = 934399) (by norm_num)
theorem B3322307 : Blo 2213435 3322307 := bstep (se 1 (by rfl) ⟨2491730, by rfl⟩ : syracuseStep 3322307 = 4983461) B4983461
theorem B2214871 : Blo 2213435 2214871 := bstep (se 1 (by rfl) ⟨1661153, by rfl⟩ : syracuseStep 2214871 = 3322307) B3322307
theorem B5606405 : Blo 2213435 5606405 := bbase (se 4 (by rfl) ⟨525600, by rfl⟩ : syracuseStep 5606405 = 1051201) (by norm_num)
theorem B3737603 : Blo 2213435 3737603 := bstep (se 1 (by rfl) ⟨2803202, by rfl⟩ : syracuseStep 3737603 = 5606405) B5606405
theorem B2491735 : Blo 2213435 2491735 := bstep (se 1 (by rfl) ⟨1868801, by rfl⟩ : syracuseStep 2491735 = 3737603) B3737603
theorem B3322313 : Blo 2213435 3322313 := bstep (se 2 (by rfl) ⟨1245867, by rfl⟩ : syracuseStep 3322313 = 2491735) B2491735
theorem B2214875 : Blo 2213435 2214875 := bstep (se 1 (by rfl) ⟨1661156, by rfl⟩ : syracuseStep 2214875 = 3322313) B3322313
theorem B4730413 : Blo 2213435 4730413 := bbase (se 3 (by rfl) ⟨886952, by rfl⟩ : syracuseStep 4730413 = 1773905) (by norm_num)
theorem B6307217 : Blo 2213435 6307217 := bstep (se 2 (by rfl) ⟨2365206, by rfl⟩ : syracuseStep 6307217 = 4730413) B4730413
theorem B4204811 : Blo 2213435 4204811 := bstep (se 1 (by rfl) ⟨3153608, by rfl⟩ : syracuseStep 4204811 = 6307217) B6307217
theorem B11212829 : Blo 2213435 11212829 := bstep (se 3 (by rfl) ⟨2102405, by rfl⟩ : syracuseStep 11212829 = 4204811) B4204811
theorem B7475219 : Blo 2213435 7475219 := bstep (se 1 (by rfl) ⟨5606414, by rfl⟩ : syracuseStep 7475219 = 11212829) B11212829
theorem B4983479 : Blo 2213435 4983479 := bstep (se 1 (by rfl) ⟨3737609, by rfl⟩ : syracuseStep 4983479 = 7475219) B7475219
theorem B3322319 : Blo 2213435 3322319 := bstep (se 1 (by rfl) ⟨2491739, by rfl⟩ : syracuseStep 3322319 = 4983479) B4983479
theorem B2214879 : Blo 2213435 2214879 := bstep (se 1 (by rfl) ⟨1661159, by rfl⟩ : syracuseStep 2214879 = 3322319) B3322319
theorem B3322325 : Blo 2213435 3322325 := bbase (se 7 (by rfl) ⟨38933, by rfl⟩ : syracuseStep 3322325 = 77867) (by norm_num)
theorem B2214883 : Blo 2213435 2214883 := bstep (se 1 (by rfl) ⟨1661162, by rfl⟩ : syracuseStep 2214883 = 3322325) B3322325
theorem B8409653 : Blo 2213435 8409653 := bbase (se 5 (by rfl) ⟨394202, by rfl⟩ : syracuseStep 8409653 = 788405) (by norm_num)
theorem B5606435 : Blo 2213435 5606435 := bstep (se 1 (by rfl) ⟨4204826, by rfl⟩ : syracuseStep 5606435 = 8409653) B8409653
theorem B3737623 : Blo 2213435 3737623 := bstep (se 1 (by rfl) ⟨2803217, by rfl⟩ : syracuseStep 3737623 = 5606435) B5606435
theorem B4983497 : Blo 2213435 4983497 := bstep (se 2 (by rfl) ⟨1868811, by rfl⟩ : syracuseStep 4983497 = 3737623) B3737623
theorem B3322331 : Blo 2213435 3322331 := bstep (se 1 (by rfl) ⟨2491748, by rfl⟩ : syracuseStep 3322331 = 4983497) B4983497
theorem B2214887 : Blo 2213435 2214887 := bstep (se 1 (by rfl) ⟨1661165, by rfl⟩ : syracuseStep 2214887 = 3322331) B3322331
theorem B2491753 : Blo 2213435 2491753 := bbase (se 2 (by rfl) ⟨934407, by rfl⟩ : syracuseStep 2491753 = 1868815) (by norm_num)
theorem B3322337 : Blo 2213435 3322337 := bstep (se 2 (by rfl) ⟨1245876, by rfl⟩ : syracuseStep 3322337 = 2491753) B2491753
theorem B2214891 : Blo 2213435 2214891 := bstep (se 1 (by rfl) ⟨1661168, by rfl⟩ : syracuseStep 2214891 = 3322337) B3322337
theorem B4262213 : Blo 2213435 4262213 := bbase (se 4 (by rfl) ⟨399582, by rfl⟩ : syracuseStep 4262213 = 799165) (by norm_num)
theorem B2841475 : Blo 2213435 2841475 := bstep (se 1 (by rfl) ⟨2131106, by rfl⟩ : syracuseStep 2841475 = 4262213) B4262213
theorem B3788633 : Blo 2213435 3788633 := bstep (se 2 (by rfl) ⟨1420737, by rfl⟩ : syracuseStep 3788633 = 2841475) B2841475
theorem B2525755 : Blo 2213435 2525755 := bstep (se 1 (by rfl) ⟨1894316, by rfl⟩ : syracuseStep 2525755 = 3788633) B3788633
theorem B3367673 : Blo 2213435 3367673 := bstep (se 2 (by rfl) ⟨1262877, by rfl⟩ : syracuseStep 3367673 = 2525755) B2525755
theorem B2245115 : Blo 2213435 2245115 := bstep (se 1 (by rfl) ⟨1683836, by rfl⟩ : syracuseStep 2245115 = 3367673) B3367673
theorem B5986973 : Blo 2213435 5986973 := bstep (se 3 (by rfl) ⟨1122557, by rfl⟩ : syracuseStep 5986973 = 2245115) B2245115
theorem B15965261 : Blo 2213435 15965261 := bstep (se 3 (by rfl) ⟨2993486, by rfl⟩ : syracuseStep 15965261 = 5986973) B5986973
theorem B10643507 : Blo 2213435 10643507 := bstep (se 1 (by rfl) ⟨7982630, by rfl⟩ : syracuseStep 10643507 = 15965261) B15965261
theorem B7095671 : Blo 2213435 7095671 := bstep (se 1 (by rfl) ⟨5321753, by rfl⟩ : syracuseStep 7095671 = 10643507) B10643507
theorem B4730447 : Blo 2213435 4730447 := bstep (se 1 (by rfl) ⟨3547835, by rfl⟩ : syracuseStep 4730447 = 7095671) B7095671
theorem B12614525 : Blo 2213435 12614525 := bstep (se 3 (by rfl) ⟨2365223, by rfl⟩ : syracuseStep 12614525 = 4730447) B4730447
theorem B8409683 : Blo 2213435 8409683 := bstep (se 1 (by rfl) ⟨6307262, by rfl⟩ : syracuseStep 8409683 = 12614525) B12614525
theorem B5606455 : Blo 2213435 5606455 := bstep (se 1 (by rfl) ⟨4204841, by rfl⟩ : syracuseStep 5606455 = 8409683) B8409683
theorem B7475273 : Blo 2213435 7475273 := bstep (se 2 (by rfl) ⟨2803227, by rfl⟩ : syracuseStep 7475273 = 5606455) B5606455
theorem B4983515 : Blo 2213435 4983515 := bstep (se 1 (by rfl) ⟨3737636, by rfl⟩ : syracuseStep 4983515 = 7475273) B7475273
theorem B3322343 : Blo 2213435 3322343 := bstep (se 1 (by rfl) ⟨2491757, by rfl⟩ : syracuseStep 3322343 = 4983515) B4983515
theorem B2214895 : Blo 2213435 2214895 := bstep (se 1 (by rfl) ⟨1661171, by rfl⟩ : syracuseStep 2214895 = 3322343) B3322343
theorem B3322349 : Blo 2213435 3322349 := bbase (se 3 (by rfl) ⟨622940, by rfl⟩ : syracuseStep 3322349 = 1245881) (by norm_num)
theorem B2214899 : Blo 2213435 2214899 := bstep (se 1 (by rfl) ⟨1661174, by rfl⟩ : syracuseStep 2214899 = 3322349) B3322349
theorem B4983533 : Blo 2213435 4983533 := bbase (se 3 (by rfl) ⟨934412, by rfl⟩ : syracuseStep 4983533 = 1868825) (by norm_num)
theorem B3322355 : Blo 2213435 3322355 := bstep (se 1 (by rfl) ⟨2491766, by rfl⟩ : syracuseStep 3322355 = 4983533) B4983533
theorem B2214903 : Blo 2213435 2214903 := bstep (se 1 (by rfl) ⟨1661177, by rfl⟩ : syracuseStep 2214903 = 3322355) B3322355
theorem B2365237 : Blo 2213435 2365237 := bbase (se 5 (by rfl) ⟨110870, by rfl⟩ : syracuseStep 2365237 = 221741) (by norm_num)
theorem B3153649 : Blo 2213435 3153649 := bstep (se 2 (by rfl) ⟨1182618, by rfl⟩ : syracuseStep 3153649 = 2365237) B2365237
theorem B4204865 : Blo 2213435 4204865 := bstep (se 2 (by rfl) ⟨1576824, by rfl⟩ : syracuseStep 4204865 = 3153649) B3153649
theorem B2803243 : Blo 2213435 2803243 := bstep (se 1 (by rfl) ⟨2102432, by rfl⟩ : syracuseStep 2803243 = 4204865) B4204865
theorem B3737657 : Blo 2213435 3737657 := bstep (se 2 (by rfl) ⟨1401621, by rfl⟩ : syracuseStep 3737657 = 2803243) B2803243
theorem B2491771 : Blo 2213435 2491771 := bstep (se 1 (by rfl) ⟨1868828, by rfl⟩ : syracuseStep 2491771 = 3737657) B3737657
theorem B3322361 : Blo 2213435 3322361 := bstep (se 2 (by rfl) ⟨1245885, by rfl⟩ : syracuseStep 3322361 = 2491771) B2491771
theorem B2214907 : Blo 2213435 2214907 := bstep (se 1 (by rfl) ⟨1661180, by rfl⟩ : syracuseStep 2214907 = 3322361) B3322361
theorem B7577317 : Blo 2213435 7577317 := bbase (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) (by norm_num)
theorem B10103089 : Blo 2213435 10103089 := bstep (se 2 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 10103089 = 7577317) B7577317
theorem B13470785 : Blo 2213435 13470785 := bstep (se 2 (by rfl) ⟨5051544, by rfl⟩ : syracuseStep 13470785 = 10103089) B10103089
theorem B8980523 : Blo 2213435 8980523 := bstep (se 1 (by rfl) ⟨6735392, by rfl⟩ : syracuseStep 8980523 = 13470785) B13470785
theorem B5987015 : Blo 2213435 5987015 := bstep (se 1 (by rfl) ⟨4490261, by rfl⟩ : syracuseStep 5987015 = 8980523) B8980523
theorem B63861493 : Blo 2213435 63861493 := bstep (se 5 (by rfl) ⟨2993507, by rfl⟩ : syracuseStep 63861493 = 5987015) B5987015
theorem B85148657 : Blo 2213435 85148657 := bstep (se 2 (by rfl) ⟨31930746, by rfl⟩ : syracuseStep 85148657 = 63861493) B63861493
theorem B56765771 : Blo 2213435 56765771 := bstep (se 1 (by rfl) ⟨42574328, by rfl⟩ : syracuseStep 56765771 = 85148657) B85148657
theorem B37843847 : Blo 2213435 37843847 := bstep (se 1 (by rfl) ⟨28382885, by rfl⟩ : syracuseStep 37843847 = 56765771) B56765771
theorem B25229231 : Blo 2213435 25229231 := bstep (se 1 (by rfl) ⟨18921923, by rfl⟩ : syracuseStep 25229231 = 37843847) B37843847
theorem B16819487 : Blo 2213435 16819487 := bstep (se 1 (by rfl) ⟨12614615, by rfl⟩ : syracuseStep 16819487 = 25229231) B25229231
theorem B11212991 : Blo 2213435 11212991 := bstep (se 1 (by rfl) ⟨8409743, by rfl⟩ : syracuseStep 11212991 = 16819487) B16819487
theorem B7475327 : Blo 2213435 7475327 := bstep (se 1 (by rfl) ⟨5606495, by rfl⟩ : syracuseStep 7475327 = 11212991) B11212991
theorem B4983551 : Blo 2213435 4983551 := bstep (se 1 (by rfl) ⟨3737663, by rfl⟩ : syracuseStep 4983551 = 7475327) B7475327
theorem B3322367 : Blo 2213435 3322367 := bstep (se 1 (by rfl) ⟨2491775, by rfl⟩ : syracuseStep 3322367 = 4983551) B4983551
theorem B2214911 : Blo 2213435 2214911 := bstep (se 1 (by rfl) ⟨1661183, by rfl⟩ : syracuseStep 2214911 = 3322367) B3322367
theorem B3322373 : Blo 2213435 3322373 := bbase (se 4 (by rfl) ⟨311472, by rfl⟩ : syracuseStep 3322373 = 622945) (by norm_num)
theorem B2214915 : Blo 2213435 2214915 := bstep (se 1 (by rfl) ⟨1661186, by rfl⟩ : syracuseStep 2214915 = 3322373) B3322373
theorem B3737677 : Blo 2213435 3737677 := bbase (se 3 (by rfl) ⟨700814, by rfl⟩ : syracuseStep 3737677 = 1401629) (by norm_num)
theorem B4983569 : Blo 2213435 4983569 := bstep (se 2 (by rfl) ⟨1868838, by rfl⟩ : syracuseStep 4983569 = 3737677) B3737677
theorem B3322379 : Blo 2213435 3322379 := bstep (se 1 (by rfl) ⟨2491784, by rfl⟩ : syracuseStep 3322379 = 4983569) B4983569
theorem B2214919 : Blo 2213435 2214919 := bstep (se 1 (by rfl) ⟨1661189, by rfl⟩ : syracuseStep 2214919 = 3322379) B3322379
theorem B2491789 : Blo 2213435 2491789 := bbase (se 3 (by rfl) ⟨467210, by rfl⟩ : syracuseStep 2491789 = 934421) (by norm_num)
theorem B3322385 : Blo 2213435 3322385 := bstep (se 2 (by rfl) ⟨1245894, by rfl⟩ : syracuseStep 3322385 = 2491789) B2491789
theorem B2214923 : Blo 2213435 2214923 := bstep (se 1 (by rfl) ⟨1661192, by rfl⟩ : syracuseStep 2214923 = 3322385) B3322385
theorem B7475381 : Blo 2213435 7475381 := bbase (se 5 (by rfl) ⟨350408, by rfl⟩ : syracuseStep 7475381 = 700817) (by norm_num)
theorem B4983587 : Blo 2213435 4983587 := bstep (se 1 (by rfl) ⟨3737690, by rfl⟩ : syracuseStep 4983587 = 7475381) B7475381
theorem B3322391 : Blo 2213435 3322391 := bstep (se 1 (by rfl) ⟨2491793, by rfl⟩ : syracuseStep 3322391 = 4983587) B4983587
theorem B2214927 : Blo 2213435 2214927 := bstep (se 1 (by rfl) ⟨1661195, by rfl⟩ : syracuseStep 2214927 = 3322391) B3322391
theorem B3322397 : Blo 2213435 3322397 := bbase (se 3 (by rfl) ⟨622949, by rfl⟩ : syracuseStep 3322397 = 1245899) (by norm_num)
theorem B2214931 : Blo 2213435 2214931 := bstep (se 1 (by rfl) ⟨1661198, by rfl⟩ : syracuseStep 2214931 = 3322397) B3322397
theorem B4983605 : Blo 2213435 4983605 := bbase (se 5 (by rfl) ⟨233606, by rfl⟩ : syracuseStep 4983605 = 467213) (by norm_num)
theorem B3322403 : Blo 2213435 3322403 := bstep (se 1 (by rfl) ⟨2491802, by rfl⟩ : syracuseStep 3322403 = 4983605) B4983605
theorem B2214935 : Blo 2213435 2214935 := bstep (se 1 (by rfl) ⟨1661201, by rfl⟩ : syracuseStep 2214935 = 3322403) B3322403
theorem B5683061 : Blo 2213435 5683061 := bbase (se 5 (by rfl) ⟨266393, by rfl⟩ : syracuseStep 5683061 = 532787) (by norm_num)
theorem B15154829 : Blo 2213435 15154829 := bstep (se 3 (by rfl) ⟨2841530, by rfl⟩ : syracuseStep 15154829 = 5683061) B5683061
theorem B10103219 : Blo 2213435 10103219 := bstep (se 1 (by rfl) ⟨7577414, by rfl⟩ : syracuseStep 10103219 = 15154829) B15154829
theorem B6735479 : Blo 2213435 6735479 := bstep (se 1 (by rfl) ⟨5051609, by rfl⟩ : syracuseStep 6735479 = 10103219) B10103219
theorem B17961277 : Blo 2213435 17961277 := bstep (se 3 (by rfl) ⟨3367739, by rfl⟩ : syracuseStep 17961277 = 6735479) B6735479
theorem B23948369 : Blo 2213435 23948369 := bstep (se 2 (by rfl) ⟨8980638, by rfl⟩ : syracuseStep 23948369 = 17961277) B17961277
theorem B15965579 : Blo 2213435 15965579 := bstep (se 1 (by rfl) ⟨11974184, by rfl⟩ : syracuseStep 15965579 = 23948369) B23948369
theorem B10643719 : Blo 2213435 10643719 := bstep (se 1 (by rfl) ⟨7982789, by rfl⟩ : syracuseStep 10643719 = 15965579) B15965579
theorem B14191625 : Blo 2213435 14191625 := bstep (se 2 (by rfl) ⟨5321859, by rfl⟩ : syracuseStep 14191625 = 10643719) B10643719
theorem B9461083 : Blo 2213435 9461083 := bstep (se 1 (by rfl) ⟨7095812, by rfl⟩ : syracuseStep 9461083 = 14191625) B14191625
theorem B12614777 : Blo 2213435 12614777 := bstep (se 2 (by rfl) ⟨4730541, by rfl⟩ : syracuseStep 12614777 = 9461083) B9461083
theorem B8409851 : Blo 2213435 8409851 := bstep (se 1 (by rfl) ⟨6307388, by rfl⟩ : syracuseStep 8409851 = 12614777) B12614777
theorem B5606567 : Blo 2213435 5606567 := bstep (se 1 (by rfl) ⟨4204925, by rfl⟩ : syracuseStep 5606567 = 8409851) B8409851
theorem B3737711 : Blo 2213435 3737711 := bstep (se 1 (by rfl) ⟨2803283, by rfl⟩ : syracuseStep 3737711 = 5606567) B5606567
theorem B2491807 : Blo 2213435 2491807 := bstep (se 1 (by rfl) ⟨1868855, by rfl⟩ : syracuseStep 2491807 = 3737711) B3737711
theorem B3322409 : Blo 2213435 3322409 := bstep (se 2 (by rfl) ⟨1245903, by rfl⟩ : syracuseStep 3322409 = 2491807) B2491807
theorem B2214939 : Blo 2213435 2214939 := bstep (se 1 (by rfl) ⟨1661204, by rfl⟩ : syracuseStep 2214939 = 3322409) B3322409
theorem B10103237 : Blo 2213435 10103237 := bbase (se 4 (by rfl) ⟨947178, by rfl⟩ : syracuseStep 10103237 = 1894357) (by norm_num)
theorem B6735491 : Blo 2213435 6735491 := bstep (se 1 (by rfl) ⟨5051618, by rfl⟩ : syracuseStep 6735491 = 10103237) B10103237
theorem B4490327 : Blo 2213435 4490327 := bstep (se 1 (by rfl) ⟨3367745, by rfl⟩ : syracuseStep 4490327 = 6735491) B6735491
theorem B11974205 : Blo 2213435 11974205 := bstep (se 3 (by rfl) ⟨2245163, by rfl⟩ : syracuseStep 11974205 = 4490327) B4490327
theorem B7982803 : Blo 2213435 7982803 := bstep (se 1 (by rfl) ⟨5987102, by rfl⟩ : syracuseStep 7982803 = 11974205) B11974205
theorem B10643737 : Blo 2213435 10643737 := bstep (se 2 (by rfl) ⟨3991401, by rfl⟩ : syracuseStep 10643737 = 7982803) B7982803
theorem B14191649 : Blo 2213435 14191649 := bstep (se 2 (by rfl) ⟨5321868, by rfl⟩ : syracuseStep 14191649 = 10643737) B10643737
theorem B9461099 : Blo 2213435 9461099 := bstep (se 1 (by rfl) ⟨7095824, by rfl⟩ : syracuseStep 9461099 = 14191649) B14191649
theorem B6307399 : Blo 2213435 6307399 := bstep (se 1 (by rfl) ⟨4730549, by rfl⟩ : syracuseStep 6307399 = 9461099) B9461099
theorem B8409865 : Blo 2213435 8409865 := bstep (se 2 (by rfl) ⟨3153699, by rfl⟩ : syracuseStep 8409865 = 6307399) B6307399
theorem B11213153 : Blo 2213435 11213153 := bstep (se 2 (by rfl) ⟨4204932, by rfl⟩ : syracuseStep 11213153 = 8409865) B8409865
theorem B7475435 : Blo 2213435 7475435 := bstep (se 1 (by rfl) ⟨5606576, by rfl⟩ : syracuseStep 7475435 = 11213153) B11213153
theorem B4983623 : Blo 2213435 4983623 := bstep (se 1 (by rfl) ⟨3737717, by rfl⟩ : syracuseStep 4983623 = 7475435) B7475435
theorem B3322415 : Blo 2213435 3322415 := bstep (se 1 (by rfl) ⟨2491811, by rfl⟩ : syracuseStep 3322415 = 4983623) B4983623
theorem B2214943 : Blo 2213435 2214943 := bstep (se 1 (by rfl) ⟨1661207, by rfl⟩ : syracuseStep 2214943 = 3322415) B3322415
theorem B3322421 : Blo 2213435 3322421 := bbase (se 5 (by rfl) ⟨155738, by rfl⟩ : syracuseStep 3322421 = 311477) (by norm_num)
theorem B2214947 : Blo 2213435 2214947 := bstep (se 1 (by rfl) ⟨1661210, by rfl⟩ : syracuseStep 2214947 = 3322421) B3322421
theorem B5606597 : Blo 2213435 5606597 := bbase (se 4 (by rfl) ⟨525618, by rfl⟩ : syracuseStep 5606597 = 1051237) (by norm_num)
theorem B3737731 : Blo 2213435 3737731 := bstep (se 1 (by rfl) ⟨2803298, by rfl⟩ : syracuseStep 3737731 = 5606597) B5606597
theorem B4983641 : Blo 2213435 4983641 := bstep (se 2 (by rfl) ⟨1868865, by rfl⟩ : syracuseStep 4983641 = 3737731) B3737731
theorem B3322427 : Blo 2213435 3322427 := bstep (se 1 (by rfl) ⟨2491820, by rfl⟩ : syracuseStep 3322427 = 4983641) B4983641
theorem B2214951 : Blo 2213435 2214951 := bstep (se 1 (by rfl) ⟨1661213, by rfl⟩ : syracuseStep 2214951 = 3322427) B3322427
theorem B2491825 : Blo 2213435 2491825 := bbase (se 2 (by rfl) ⟨934434, by rfl⟩ : syracuseStep 2491825 = 1868869) (by norm_num)
theorem B3322433 : Blo 2213435 3322433 := bstep (se 2 (by rfl) ⟨1245912, by rfl⟩ : syracuseStep 3322433 = 2491825) B2491825
theorem B2214955 : Blo 2213435 2214955 := bstep (se 1 (by rfl) ⟨1661216, by rfl⟩ : syracuseStep 2214955 = 3322433) B3322433
theorem B6307445 : Blo 2213435 6307445 := bbase (se 5 (by rfl) ⟨295661, by rfl⟩ : syracuseStep 6307445 = 591323) (by norm_num)
theorem B4204963 : Blo 2213435 4204963 := bstep (se 1 (by rfl) ⟨3153722, by rfl⟩ : syracuseStep 4204963 = 6307445) B6307445
theorem B5606617 : Blo 2213435 5606617 := bstep (se 2 (by rfl) ⟨2102481, by rfl⟩ : syracuseStep 5606617 = 4204963) B4204963
theorem B7475489 : Blo 2213435 7475489 := bstep (se 2 (by rfl) ⟨2803308, by rfl⟩ : syracuseStep 7475489 = 5606617) B5606617
theorem B4983659 : Blo 2213435 4983659 := bstep (se 1 (by rfl) ⟨3737744, by rfl⟩ : syracuseStep 4983659 = 7475489) B7475489
theorem B3322439 : Blo 2213435 3322439 := bstep (se 1 (by rfl) ⟨2491829, by rfl⟩ : syracuseStep 3322439 = 4983659) B4983659
theorem B2214959 : Blo 2213435 2214959 := bstep (se 1 (by rfl) ⟨1661219, by rfl⟩ : syracuseStep 2214959 = 3322439) B3322439
theorem B3322445 : Blo 2213435 3322445 := bbase (se 3 (by rfl) ⟨622958, by rfl⟩ : syracuseStep 3322445 = 1245917) (by norm_num)
theorem B2214963 : Blo 2213435 2214963 := bstep (se 1 (by rfl) ⟨1661222, by rfl⟩ : syracuseStep 2214963 = 3322445) B3322445
theorem B4983677 : Blo 2213435 4983677 := bbase (se 3 (by rfl) ⟨934439, by rfl⟩ : syracuseStep 4983677 = 1868879) (by norm_num)
theorem B3322451 : Blo 2213435 3322451 := bstep (se 1 (by rfl) ⟨2491838, by rfl⟩ : syracuseStep 3322451 = 4983677) B4983677
theorem B2214967 : Blo 2213435 2214967 := bstep (se 1 (by rfl) ⟨1661225, by rfl⟩ : syracuseStep 2214967 = 3322451) B3322451
theorem B3737765 : Blo 2213435 3737765 := bbase (se 4 (by rfl) ⟨350415, by rfl⟩ : syracuseStep 3737765 = 700831) (by norm_num)
theorem B2491843 : Blo 2213435 2491843 := bstep (se 1 (by rfl) ⟨1868882, by rfl⟩ : syracuseStep 2491843 = 3737765) B3737765
theorem B3322457 : Blo 2213435 3322457 := bstep (se 2 (by rfl) ⟨1245921, by rfl⟩ : syracuseStep 3322457 = 2491843) B2491843
theorem B2214971 : Blo 2213435 2214971 := bstep (se 1 (by rfl) ⟨1661228, by rfl⟩ : syracuseStep 2214971 = 3322457) B3322457
theorem B2365309 : Blo 2213435 2365309 := bbase (se 3 (by rfl) ⟨443495, by rfl⟩ : syracuseStep 2365309 = 886991) (by norm_num)
theorem B3153745 : Blo 2213435 3153745 := bstep (se 2 (by rfl) ⟨1182654, by rfl⟩ : syracuseStep 3153745 = 2365309) B2365309
theorem B16819973 : Blo 2213435 16819973 := bstep (se 4 (by rfl) ⟨1576872, by rfl⟩ : syracuseStep 16819973 = 3153745) B3153745
theorem B11213315 : Blo 2213435 11213315 := bstep (se 1 (by rfl) ⟨8409986, by rfl⟩ : syracuseStep 11213315 = 16819973) B16819973
theorem B7475543 : Blo 2213435 7475543 := bstep (se 1 (by rfl) ⟨5606657, by rfl⟩ : syracuseStep 7475543 = 11213315) B11213315
theorem B4983695 : Blo 2213435 4983695 := bstep (se 1 (by rfl) ⟨3737771, by rfl⟩ : syracuseStep 4983695 = 7475543) B7475543
theorem B3322463 : Blo 2213435 3322463 := bstep (se 1 (by rfl) ⟨2491847, by rfl⟩ : syracuseStep 3322463 = 4983695) B4983695
theorem B2214975 : Blo 2213435 2214975 := bstep (se 1 (by rfl) ⟨1661231, by rfl⟩ : syracuseStep 2214975 = 3322463) B3322463
theorem B3322469 : Blo 2213435 3322469 := bbase (se 4 (by rfl) ⟨311481, by rfl⟩ : syracuseStep 3322469 = 622963) (by norm_num)
theorem B2214979 : Blo 2213435 2214979 := bstep (se 1 (by rfl) ⟨1661234, by rfl⟩ : syracuseStep 2214979 = 3322469) B3322469
theorem B3153757 : Blo 2213435 3153757 := bbase (se 3 (by rfl) ⟨591329, by rfl⟩ : syracuseStep 3153757 = 1182659) (by norm_num)
theorem B4205009 : Blo 2213435 4205009 := bstep (se 2 (by rfl) ⟨1576878, by rfl⟩ : syracuseStep 4205009 = 3153757) B3153757
theorem B2803339 : Blo 2213435 2803339 := bstep (se 1 (by rfl) ⟨2102504, by rfl⟩ : syracuseStep 2803339 = 4205009) B4205009
theorem B3737785 : Blo 2213435 3737785 := bstep (se 2 (by rfl) ⟨1401669, by rfl⟩ : syracuseStep 3737785 = 2803339) B2803339
theorem B4983713 : Blo 2213435 4983713 := bstep (se 2 (by rfl) ⟨1868892, by rfl⟩ : syracuseStep 4983713 = 3737785) B3737785
theorem B3322475 : Blo 2213435 3322475 := bstep (se 1 (by rfl) ⟨2491856, by rfl⟩ : syracuseStep 3322475 = 4983713) B4983713
theorem B2214983 : Blo 2213435 2214983 := bstep (se 1 (by rfl) ⟨1661237, by rfl⟩ : syracuseStep 2214983 = 3322475) B3322475
theorem B2491861 : Blo 2213435 2491861 := bbase (se 7 (by rfl) ⟨29201, by rfl⟩ : syracuseStep 2491861 = 58403) (by norm_num)
theorem B3322481 : Blo 2213435 3322481 := bstep (se 2 (by rfl) ⟨1245930, by rfl⟩ : syracuseStep 3322481 = 2491861) B2491861
theorem B2214987 : Blo 2213435 2214987 := bstep (se 1 (by rfl) ⟨1661240, by rfl⟩ : syracuseStep 2214987 = 3322481) B3322481
theorem B2803349 : Blo 2213435 2803349 := bbase (se 6 (by rfl) ⟨65703, by rfl⟩ : syracuseStep 2803349 = 131407) (by norm_num)
theorem B7475597 : Blo 2213435 7475597 := bstep (se 3 (by rfl) ⟨1401674, by rfl⟩ : syracuseStep 7475597 = 2803349) B2803349
theorem B4983731 : Blo 2213435 4983731 := bstep (se 1 (by rfl) ⟨3737798, by rfl⟩ : syracuseStep 4983731 = 7475597) B7475597
theorem B3322487 : Blo 2213435 3322487 := bstep (se 1 (by rfl) ⟨2491865, by rfl⟩ : syracuseStep 3322487 = 4983731) B4983731
theorem B2214991 : Blo 2213435 2214991 := bstep (se 1 (by rfl) ⟨1661243, by rfl⟩ : syracuseStep 2214991 = 3322487) B3322487
theorem B3322493 : Blo 2213435 3322493 := bbase (se 3 (by rfl) ⟨622967, by rfl⟩ : syracuseStep 3322493 = 1245935) (by norm_num)
theorem B2214995 : Blo 2213435 2214995 := bstep (se 1 (by rfl) ⟨1661246, by rfl⟩ : syracuseStep 2214995 = 3322493) B3322493
theorem B4983749 : Blo 2213435 4983749 := bbase (se 4 (by rfl) ⟨467226, by rfl⟩ : syracuseStep 4983749 = 934453) (by norm_num)
theorem B3322499 : Blo 2213435 3322499 := bstep (se 1 (by rfl) ⟨2491874, by rfl⟩ : syracuseStep 3322499 = 4983749) B4983749
theorem B2214999 : Blo 2213435 2214999 := bstep (se 1 (by rfl) ⟨1661249, by rfl⟩ : syracuseStep 2214999 = 3322499) B3322499
theorem B8980901 : Blo 2213435 8980901 := bbase (se 4 (by rfl) ⟨841959, by rfl⟩ : syracuseStep 8980901 = 1683919) (by norm_num)
theorem B5987267 : Blo 2213435 5987267 := bstep (se 1 (by rfl) ⟨4490450, by rfl⟩ : syracuseStep 5987267 = 8980901) B8980901
theorem B3991511 : Blo 2213435 3991511 := bstep (se 1 (by rfl) ⟨2993633, by rfl⟩ : syracuseStep 3991511 = 5987267) B5987267
theorem B2661007 : Blo 2213435 2661007 := bstep (se 1 (by rfl) ⟨1995755, by rfl⟩ : syracuseStep 2661007 = 3991511) B3991511
theorem B3548009 : Blo 2213435 3548009 := bstep (se 2 (by rfl) ⟨1330503, by rfl⟩ : syracuseStep 3548009 = 2661007) B2661007
theorem B9461357 : Blo 2213435 9461357 := bstep (se 3 (by rfl) ⟨1774004, by rfl⟩ : syracuseStep 9461357 = 3548009) B3548009
theorem B6307571 : Blo 2213435 6307571 := bstep (se 1 (by rfl) ⟨4730678, by rfl⟩ : syracuseStep 6307571 = 9461357) B9461357
theorem B4205047 : Blo 2213435 4205047 := bstep (se 1 (by rfl) ⟨3153785, by rfl⟩ : syracuseStep 4205047 = 6307571) B6307571
theorem B5606729 : Blo 2213435 5606729 := bstep (se 2 (by rfl) ⟨2102523, by rfl⟩ : syracuseStep 5606729 = 4205047) B4205047
theorem B3737819 : Blo 2213435 3737819 := bstep (se 1 (by rfl) ⟨2803364, by rfl⟩ : syracuseStep 3737819 = 5606729) B5606729
theorem B2491879 : Blo 2213435 2491879 := bstep (se 1 (by rfl) ⟨1868909, by rfl⟩ : syracuseStep 2491879 = 3737819) B3737819
theorem B3322505 : Blo 2213435 3322505 := bstep (se 2 (by rfl) ⟨1245939, by rfl⟩ : syracuseStep 3322505 = 2491879) B2491879
theorem B2215003 : Blo 2213435 2215003 := bstep (se 1 (by rfl) ⟨1661252, by rfl⟩ : syracuseStep 2215003 = 3322505) B3322505
theorem B11213477 : Blo 2213435 11213477 := bbase (se 4 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 11213477 = 2102527) (by norm_num)
theorem B7475651 : Blo 2213435 7475651 := bstep (se 1 (by rfl) ⟨5606738, by rfl⟩ : syracuseStep 7475651 = 11213477) B11213477
theorem B4983767 : Blo 2213435 4983767 := bstep (se 1 (by rfl) ⟨3737825, by rfl⟩ : syracuseStep 4983767 = 7475651) B7475651
theorem B3322511 : Blo 2213435 3322511 := bstep (se 1 (by rfl) ⟨2491883, by rfl⟩ : syracuseStep 3322511 = 4983767) B4983767
theorem B2215007 : Blo 2213435 2215007 := bstep (se 1 (by rfl) ⟨1661255, by rfl⟩ : syracuseStep 2215007 = 3322511) B3322511
theorem B3322517 : Blo 2213435 3322517 := bbase (se 6 (by rfl) ⟨77871, by rfl⟩ : syracuseStep 3322517 = 155743) (by norm_num)
theorem B2215011 : Blo 2213435 2215011 := bstep (se 1 (by rfl) ⟨1661258, by rfl⟩ : syracuseStep 2215011 = 3322517) B3322517
theorem B16183957 : Blo 2213435 16183957 := bbase (se 6 (by rfl) ⟨379311, by rfl⟩ : syracuseStep 16183957 = 758623) (by norm_num)
theorem B21578609 : Blo 2213435 21578609 := bstep (se 2 (by rfl) ⟨8091978, by rfl⟩ : syracuseStep 21578609 = 16183957) B16183957
theorem B57542957 : Blo 2213435 57542957 := bstep (se 3 (by rfl) ⟨10789304, by rfl⟩ : syracuseStep 57542957 = 21578609) B21578609
theorem B38361971 : Blo 2213435 38361971 := bstep (se 1 (by rfl) ⟨28771478, by rfl⟩ : syracuseStep 38361971 = 57542957) B57542957
theorem B102298589 : Blo 2213435 102298589 := bstep (se 3 (by rfl) ⟨19180985, by rfl⟩ : syracuseStep 102298589 = 38361971) B38361971
theorem B68199059 : Blo 2213435 68199059 := bstep (se 1 (by rfl) ⟨51149294, by rfl⟩ : syracuseStep 68199059 = 102298589) B102298589
theorem B45466039 : Blo 2213435 45466039 := bstep (se 1 (by rfl) ⟨34099529, by rfl⟩ : syracuseStep 45466039 = 68199059) B68199059
theorem B60621385 : Blo 2213435 60621385 := bstep (se 2 (by rfl) ⟨22733019, by rfl⟩ : syracuseStep 60621385 = 45466039) B45466039
theorem B80828513 : Blo 2213435 80828513 := bstep (se 2 (by rfl) ⟨30310692, by rfl⟩ : syracuseStep 80828513 = 60621385) B60621385
theorem B53885675 : Blo 2213435 53885675 := bstep (se 1 (by rfl) ⟨40414256, by rfl⟩ : syracuseStep 53885675 = 80828513) B80828513
theorem B35923783 : Blo 2213435 35923783 := bstep (se 1 (by rfl) ⟨26942837, by rfl⟩ : syracuseStep 35923783 = 53885675) B53885675
theorem B47898377 : Blo 2213435 47898377 := bstep (se 2 (by rfl) ⟨17961891, by rfl⟩ : syracuseStep 47898377 = 35923783) B35923783
theorem B31932251 : Blo 2213435 31932251 := bstep (se 1 (by rfl) ⟨23949188, by rfl⟩ : syracuseStep 31932251 = 47898377) B47898377
theorem B21288167 : Blo 2213435 21288167 := bstep (se 1 (by rfl) ⟨15966125, by rfl⟩ : syracuseStep 21288167 = 31932251) B31932251
theorem B14192111 : Blo 2213435 14192111 := bstep (se 1 (by rfl) ⟨10644083, by rfl⟩ : syracuseStep 14192111 = 21288167) B21288167
theorem B9461407 : Blo 2213435 9461407 := bstep (se 1 (by rfl) ⟨7096055, by rfl⟩ : syracuseStep 9461407 = 14192111) B14192111
theorem B12615209 : Blo 2213435 12615209 := bstep (se 2 (by rfl) ⟨4730703, by rfl⟩ : syracuseStep 12615209 = 9461407) B9461407
theorem B8410139 : Blo 2213435 8410139 := bstep (se 1 (by rfl) ⟨6307604, by rfl⟩ : syracuseStep 8410139 = 12615209) B12615209
theorem B5606759 : Blo 2213435 5606759 := bstep (se 1 (by rfl) ⟨4205069, by rfl⟩ : syracuseStep 5606759 = 8410139) B8410139
theorem B3737839 : Blo 2213435 3737839 := bstep (se 1 (by rfl) ⟨2803379, by rfl⟩ : syracuseStep 3737839 = 5606759) B5606759
theorem B4983785 : Blo 2213435 4983785 := bstep (se 2 (by rfl) ⟨1868919, by rfl⟩ : syracuseStep 4983785 = 3737839) B3737839
theorem B3322523 : Blo 2213435 3322523 := bstep (se 1 (by rfl) ⟨2491892, by rfl⟩ : syracuseStep 3322523 = 4983785) B4983785
theorem B2215015 : Blo 2213435 2215015 := bstep (se 1 (by rfl) ⟨1661261, by rfl⟩ : syracuseStep 2215015 = 3322523) B3322523
theorem B2491897 : Blo 2213435 2491897 := bbase (se 2 (by rfl) ⟨934461, by rfl⟩ : syracuseStep 2491897 = 1868923) (by norm_num)
theorem B3322529 : Blo 2213435 3322529 := bstep (se 2 (by rfl) ⟨1245948, by rfl⟩ : syracuseStep 3322529 = 2491897) B2491897
theorem B2215019 : Blo 2213435 2215019 := bstep (se 1 (by rfl) ⟨1661264, by rfl⟩ : syracuseStep 2215019 = 3322529) B3322529
theorem B5322061 : Blo 2213435 5322061 := bbase (se 3 (by rfl) ⟨997886, by rfl⟩ : syracuseStep 5322061 = 1995773) (by norm_num)
theorem B7096081 : Blo 2213435 7096081 := bstep (se 2 (by rfl) ⟨2661030, by rfl⟩ : syracuseStep 7096081 = 5322061) B5322061
theorem B9461441 : Blo 2213435 9461441 := bstep (se 2 (by rfl) ⟨3548040, by rfl⟩ : syracuseStep 9461441 = 7096081) B7096081
theorem B6307627 : Blo 2213435 6307627 := bstep (se 1 (by rfl) ⟨4730720, by rfl⟩ : syracuseStep 6307627 = 9461441) B9461441
theorem B8410169 : Blo 2213435 8410169 := bstep (se 2 (by rfl) ⟨3153813, by rfl⟩ : syracuseStep 8410169 = 6307627) B6307627
theorem B5606779 : Blo 2213435 5606779 := bstep (se 1 (by rfl) ⟨4205084, by rfl⟩ : syracuseStep 5606779 = 8410169) B8410169
theorem B7475705 : Blo 2213435 7475705 := bstep (se 2 (by rfl) ⟨2803389, by rfl⟩ : syracuseStep 7475705 = 5606779) B5606779
theorem B4983803 : Blo 2213435 4983803 := bstep (se 1 (by rfl) ⟨3737852, by rfl⟩ : syracuseStep 4983803 = 7475705) B7475705
theorem B3322535 : Blo 2213435 3322535 := bstep (se 1 (by rfl) ⟨2491901, by rfl⟩ : syracuseStep 3322535 = 4983803) B4983803
theorem B2215023 : Blo 2213435 2215023 := bstep (se 1 (by rfl) ⟨1661267, by rfl⟩ : syracuseStep 2215023 = 3322535) B3322535
theorem B3322541 : Blo 2213435 3322541 := bbase (se 3 (by rfl) ⟨622976, by rfl⟩ : syracuseStep 3322541 = 1245953) (by norm_num)
theorem B2215027 : Blo 2213435 2215027 := bstep (se 1 (by rfl) ⟨1661270, by rfl⟩ : syracuseStep 2215027 = 3322541) B3322541
theorem B4983821 : Blo 2213435 4983821 := bbase (se 3 (by rfl) ⟨934466, by rfl⟩ : syracuseStep 4983821 = 1868933) (by norm_num)
theorem B3322547 : Blo 2213435 3322547 := bstep (se 1 (by rfl) ⟨2491910, by rfl⟩ : syracuseStep 3322547 = 4983821) B4983821
theorem B2215031 : Blo 2213435 2215031 := bstep (se 1 (by rfl) ⟨1661273, by rfl⟩ : syracuseStep 2215031 = 3322547) B3322547
theorem B2803405 : Blo 2213435 2803405 := bbase (se 3 (by rfl) ⟨525638, by rfl⟩ : syracuseStep 2803405 = 1051277) (by norm_num)
theorem B3737873 : Blo 2213435 3737873 := bstep (se 2 (by rfl) ⟨1401702, by rfl⟩ : syracuseStep 3737873 = 2803405) B2803405
theorem B2491915 : Blo 2213435 2491915 := bstep (se 1 (by rfl) ⟨1868936, by rfl⟩ : syracuseStep 2491915 = 3737873) B3737873
theorem B3322553 : Blo 2213435 3322553 := bstep (se 2 (by rfl) ⟨1245957, by rfl⟩ : syracuseStep 3322553 = 2491915) B2491915
theorem B2215035 : Blo 2213435 2215035 := bstep (se 1 (by rfl) ⟨1661276, by rfl⟩ : syracuseStep 2215035 = 3322553) B3322553
theorem B5051837 : Blo 2213435 5051837 := bbase (se 3 (by rfl) ⟨947219, by rfl⟩ : syracuseStep 5051837 = 1894439) (by norm_num)
theorem B3367891 : Blo 2213435 3367891 := bstep (se 1 (by rfl) ⟨2525918, by rfl⟩ : syracuseStep 3367891 = 5051837) B5051837
theorem B4490521 : Blo 2213435 4490521 := bstep (se 2 (by rfl) ⟨1683945, by rfl⟩ : syracuseStep 4490521 = 3367891) B3367891
theorem B23949445 : Blo 2213435 23949445 := bstep (se 4 (by rfl) ⟨2245260, by rfl⟩ : syracuseStep 23949445 = 4490521) B4490521
theorem B31932593 : Blo 2213435 31932593 := bstep (se 2 (by rfl) ⟨11974722, by rfl⟩ : syracuseStep 31932593 = 23949445) B23949445
theorem B21288395 : Blo 2213435 21288395 := bstep (se 1 (by rfl) ⟨15966296, by rfl⟩ : syracuseStep 21288395 = 31932593) B31932593
theorem B14192263 : Blo 2213435 14192263 := bstep (se 1 (by rfl) ⟨10644197, by rfl⟩ : syracuseStep 14192263 = 21288395) B21288395
theorem B18923017 : Blo 2213435 18923017 := bstep (se 2 (by rfl) ⟨7096131, by rfl⟩ : syracuseStep 18923017 = 14192263) B14192263
theorem B25230689 : Blo 2213435 25230689 := bstep (se 2 (by rfl) ⟨9461508, by rfl⟩ : syracuseStep 25230689 = 18923017) B18923017
theorem B16820459 : Blo 2213435 16820459 := bstep (se 1 (by rfl) ⟨12615344, by rfl⟩ : syracuseStep 16820459 = 25230689) B25230689
theorem B11213639 : Blo 2213435 11213639 := bstep (se 1 (by rfl) ⟨8410229, by rfl⟩ : syracuseStep 11213639 = 16820459) B16820459
theorem B7475759 : Blo 2213435 7475759 := bstep (se 1 (by rfl) ⟨5606819, by rfl⟩ : syracuseStep 7475759 = 11213639) B11213639
theorem B4983839 : Blo 2213435 4983839 := bstep (se 1 (by rfl) ⟨3737879, by rfl⟩ : syracuseStep 4983839 = 7475759) B7475759
theorem B3322559 : Blo 2213435 3322559 := bstep (se 1 (by rfl) ⟨2491919, by rfl⟩ : syracuseStep 3322559 = 4983839) B4983839
theorem B2215039 : Blo 2213435 2215039 := bstep (se 1 (by rfl) ⟨1661279, by rfl⟩ : syracuseStep 2215039 = 3322559) B3322559
theorem B3322565 : Blo 2213435 3322565 := bbase (se 4 (by rfl) ⟨311490, by rfl⟩ : syracuseStep 3322565 = 622981) (by norm_num)
theorem B2215043 : Blo 2213435 2215043 := bstep (se 1 (by rfl) ⟨1661282, by rfl⟩ : syracuseStep 2215043 = 3322565) B3322565
theorem B3737893 : Blo 2213435 3737893 := bbase (se 4 (by rfl) ⟨350427, by rfl⟩ : syracuseStep 3737893 = 700855) (by norm_num)
theorem B4983857 : Blo 2213435 4983857 := bstep (se 2 (by rfl) ⟨1868946, by rfl⟩ : syracuseStep 4983857 = 3737893) B3737893
theorem B3322571 : Blo 2213435 3322571 := bstep (se 1 (by rfl) ⟨2491928, by rfl⟩ : syracuseStep 3322571 = 4983857) B4983857
theorem B2215047 : Blo 2213435 2215047 := bstep (se 1 (by rfl) ⟨1661285, by rfl⟩ : syracuseStep 2215047 = 3322571) B3322571
theorem B2491933 : Blo 2213435 2491933 := bbase (se 3 (by rfl) ⟨467237, by rfl⟩ : syracuseStep 2491933 = 934475) (by norm_num)
theorem B3322577 : Blo 2213435 3322577 := bstep (se 2 (by rfl) ⟨1245966, by rfl⟩ : syracuseStep 3322577 = 2491933) B2491933
theorem B2215051 : Blo 2213435 2215051 := bstep (se 1 (by rfl) ⟨1661288, by rfl⟩ : syracuseStep 2215051 = 3322577) B3322577
theorem B7475813 : Blo 2213435 7475813 := bbase (se 4 (by rfl) ⟨700857, by rfl⟩ : syracuseStep 7475813 = 1401715) (by norm_num)
theorem B4983875 : Blo 2213435 4983875 := bstep (se 1 (by rfl) ⟨3737906, by rfl⟩ : syracuseStep 4983875 = 7475813) B7475813
theorem B3322583 : Blo 2213435 3322583 := bstep (se 1 (by rfl) ⟨2491937, by rfl⟩ : syracuseStep 3322583 = 4983875) B4983875
theorem B2215055 : Blo 2213435 2215055 := bstep (se 1 (by rfl) ⟨1661291, by rfl⟩ : syracuseStep 2215055 = 3322583) B3322583
theorem B3322589 : Blo 2213435 3322589 := bbase (se 3 (by rfl) ⟨622985, by rfl⟩ : syracuseStep 3322589 = 1245971) (by norm_num)
theorem B2215059 : Blo 2213435 2215059 := bstep (se 1 (by rfl) ⟨1661294, by rfl⟩ : syracuseStep 2215059 = 3322589) B3322589
theorem B4983893 : Blo 2213435 4983893 := bbase (se 8 (by rfl) ⟨29202, by rfl⟩ : syracuseStep 4983893 = 58405) (by norm_num)
theorem B3322595 : Blo 2213435 3322595 := bstep (se 1 (by rfl) ⟨2491946, by rfl⟩ : syracuseStep 3322595 = 4983893) B4983893
theorem B2215063 : Blo 2213435 2215063 := bstep (se 1 (by rfl) ⟨1661297, by rfl⟩ : syracuseStep 2215063 = 3322595) B3322595
theorem B3413885 : Blo 2213435 3413885 := bbase (se 3 (by rfl) ⟨640103, by rfl⟩ : syracuseStep 3413885 = 1280207) (by norm_num)
theorem B9103693 : Blo 2213435 9103693 := bstep (se 3 (by rfl) ⟨1706942, by rfl⟩ : syracuseStep 9103693 = 3413885) B3413885
theorem B12138257 : Blo 2213435 12138257 := bstep (se 2 (by rfl) ⟨4551846, by rfl⟩ : syracuseStep 12138257 = 9103693) B9103693
theorem B8092171 : Blo 2213435 8092171 := bstep (se 1 (by rfl) ⟨6069128, by rfl⟩ : syracuseStep 8092171 = 12138257) B12138257
theorem B10789561 : Blo 2213435 10789561 := bstep (se 2 (by rfl) ⟨4046085, by rfl⟩ : syracuseStep 10789561 = 8092171) B8092171
theorem B14386081 : Blo 2213435 14386081 := bstep (se 2 (by rfl) ⟨5394780, by rfl⟩ : syracuseStep 14386081 = 10789561) B10789561
theorem B19181441 : Blo 2213435 19181441 := bstep (se 2 (by rfl) ⟨7193040, by rfl⟩ : syracuseStep 19181441 = 14386081) B14386081
theorem B12787627 : Blo 2213435 12787627 := bstep (se 1 (by rfl) ⟨9590720, by rfl⟩ : syracuseStep 12787627 = 19181441) B19181441
theorem B17050169 : Blo 2213435 17050169 := bstep (se 2 (by rfl) ⟨6393813, by rfl⟩ : syracuseStep 17050169 = 12787627) B12787627
theorem B11366779 : Blo 2213435 11366779 := bstep (se 1 (by rfl) ⟨8525084, by rfl⟩ : syracuseStep 11366779 = 17050169) B17050169
theorem B15155705 : Blo 2213435 15155705 := bstep (se 2 (by rfl) ⟨5683389, by rfl⟩ : syracuseStep 15155705 = 11366779) B11366779
theorem B40415213 : Blo 2213435 40415213 := bstep (se 3 (by rfl) ⟨7577852, by rfl⟩ : syracuseStep 40415213 = 15155705) B15155705
theorem B26943475 : Blo 2213435 26943475 := bstep (se 1 (by rfl) ⟨20207606, by rfl⟩ : syracuseStep 26943475 = 40415213) B40415213
theorem B35924633 : Blo 2213435 35924633 := bstep (se 2 (by rfl) ⟨13471737, by rfl⟩ : syracuseStep 35924633 = 26943475) B26943475
theorem B23949755 : Blo 2213435 23949755 := bstep (se 1 (by rfl) ⟨17962316, by rfl⟩ : syracuseStep 23949755 = 35924633) B35924633
theorem B15966503 : Blo 2213435 15966503 := bstep (se 1 (by rfl) ⟨11974877, by rfl⟩ : syracuseStep 15966503 = 23949755) B23949755
theorem B10644335 : Blo 2213435 10644335 := bstep (se 1 (by rfl) ⟨7983251, by rfl⟩ : syracuseStep 10644335 = 15966503) B15966503
theorem B7096223 : Blo 2213435 7096223 := bstep (se 1 (by rfl) ⟨5322167, by rfl⟩ : syracuseStep 7096223 = 10644335) B10644335
theorem B4730815 : Blo 2213435 4730815 := bstep (se 1 (by rfl) ⟨3548111, by rfl⟩ : syracuseStep 4730815 = 7096223) B7096223
theorem B6307753 : Blo 2213435 6307753 := bstep (se 2 (by rfl) ⟨2365407, by rfl⟩ : syracuseStep 6307753 = 4730815) B4730815
theorem B8410337 : Blo 2213435 8410337 := bstep (se 2 (by rfl) ⟨3153876, by rfl⟩ : syracuseStep 8410337 = 6307753) B6307753
theorem B5606891 : Blo 2213435 5606891 := bstep (se 1 (by rfl) ⟨4205168, by rfl⟩ : syracuseStep 5606891 = 8410337) B8410337
theorem B3737927 : Blo 2213435 3737927 := bstep (se 1 (by rfl) ⟨2803445, by rfl⟩ : syracuseStep 3737927 = 5606891) B5606891
theorem B2491951 : Blo 2213435 2491951 := bstep (se 1 (by rfl) ⟨1868963, by rfl⟩ : syracuseStep 2491951 = 3737927) B3737927
theorem B3322601 : Blo 2213435 3322601 := bstep (se 2 (by rfl) ⟨1245975, by rfl⟩ : syracuseStep 3322601 = 2491951) B2491951
theorem B2215067 : Blo 2213435 2215067 := bstep (se 1 (by rfl) ⟨1661300, by rfl⟩ : syracuseStep 2215067 = 3322601) B3322601
theorem B4927109 : Blo 2213435 4927109 := bbase (se 4 (by rfl) ⟨461916, by rfl⟩ : syracuseStep 4927109 = 923833) (by norm_num)
theorem B13138957 : Blo 2213435 13138957 := bstep (se 3 (by rfl) ⟨2463554, by rfl⟩ : syracuseStep 13138957 = 4927109) B4927109
theorem B17518609 : Blo 2213435 17518609 := bstep (se 2 (by rfl) ⟨6569478, by rfl⟩ : syracuseStep 17518609 = 13138957) B13138957
theorem B23358145 : Blo 2213435 23358145 := bstep (se 2 (by rfl) ⟨8759304, by rfl⟩ : syracuseStep 23358145 = 17518609) B17518609
theorem B31144193 : Blo 2213435 31144193 := bstep (se 2 (by rfl) ⟨11679072, by rfl⟩ : syracuseStep 31144193 = 23358145) B23358145
theorem B20762795 : Blo 2213435 20762795 := bstep (se 1 (by rfl) ⟨15572096, by rfl⟩ : syracuseStep 20762795 = 31144193) B31144193
theorem B55367453 : Blo 2213435 55367453 := bstep (se 3 (by rfl) ⟨10381397, by rfl⟩ : syracuseStep 55367453 = 20762795) B20762795
theorem B147646541 : Blo 2213435 147646541 := bstep (se 3 (by rfl) ⟨27683726, by rfl⟩ : syracuseStep 147646541 = 55367453) B55367453
theorem B393724109 : Blo 2213435 393724109 := bstep (se 3 (by rfl) ⟨73823270, by rfl⟩ : syracuseStep 393724109 = 147646541) B147646541
theorem B1049930957 : Blo 2213435 1049930957 := bstep (se 3 (by rfl) ⟨196862054, by rfl⟩ : syracuseStep 1049930957 = 393724109) B393724109
theorem B699953971 : Blo 2213435 699953971 := bstep (se 1 (by rfl) ⟨524965478, by rfl⟩ : syracuseStep 699953971 = 1049930957) B1049930957
theorem B933271961 : Blo 2213435 933271961 := bstep (se 2 (by rfl) ⟨349976985, by rfl⟩ : syracuseStep 933271961 = 699953971) B699953971
theorem B9954900917 : Blo 2213435 9954900917 := bstep (se 5 (by rfl) ⟨466635980, by rfl⟩ : syracuseStep 9954900917 = 933271961) B933271961
theorem B6636600611 : Blo 2213435 6636600611 := bstep (se 1 (by rfl) ⟨4977450458, by rfl⟩ : syracuseStep 6636600611 = 9954900917) B9954900917
theorem B4424400407 : Blo 2213435 4424400407 := bstep (se 1 (by rfl) ⟨3318300305, by rfl⟩ : syracuseStep 4424400407 = 6636600611) B6636600611
theorem B2949600271 : Blo 2213435 2949600271 := bstep (se 1 (by rfl) ⟨2212200203, by rfl⟩ : syracuseStep 2949600271 = 4424400407) B4424400407
theorem B3932800361 : Blo 2213435 3932800361 := bstep (se 2 (by rfl) ⟨1474800135, by rfl⟩ : syracuseStep 3932800361 = 2949600271) B2949600271
theorem B2621866907 : Blo 2213435 2621866907 := bstep (se 1 (by rfl) ⟨1966400180, by rfl⟩ : syracuseStep 2621866907 = 3932800361) B3932800361
theorem B1747911271 : Blo 2213435 1747911271 := bstep (se 1 (by rfl) ⟨1310933453, by rfl⟩ : syracuseStep 1747911271 = 2621866907) B2621866907
theorem B2330548361 : Blo 2213435 2330548361 := bstep (se 2 (by rfl) ⟨873955635, by rfl⟩ : syracuseStep 2330548361 = 1747911271) B1747911271
theorem B1553698907 : Blo 2213435 1553698907 := bstep (se 1 (by rfl) ⟨1165274180, by rfl⟩ : syracuseStep 1553698907 = 2330548361) B2330548361
theorem B1035799271 : Blo 2213435 1035799271 := bstep (se 1 (by rfl) ⟨776849453, by rfl⟩ : syracuseStep 1035799271 = 1553698907) B1553698907
theorem B690532847 : Blo 2213435 690532847 := bstep (se 1 (by rfl) ⟨517899635, by rfl⟩ : syracuseStep 690532847 = 1035799271) B1035799271
theorem B460355231 : Blo 2213435 460355231 := bstep (se 1 (by rfl) ⟨345266423, by rfl⟩ : syracuseStep 460355231 = 690532847) B690532847
theorem B306903487 : Blo 2213435 306903487 := bstep (se 1 (by rfl) ⟨230177615, by rfl⟩ : syracuseStep 306903487 = 460355231) B460355231
theorem B409204649 : Blo 2213435 409204649 := bstep (se 2 (by rfl) ⟨153451743, by rfl⟩ : syracuseStep 409204649 = 306903487) B306903487
theorem B272803099 : Blo 2213435 272803099 := bstep (se 1 (by rfl) ⟨204602324, by rfl⟩ : syracuseStep 272803099 = 409204649) B409204649
theorem B363737465 : Blo 2213435 363737465 := bstep (se 2 (by rfl) ⟨136401549, by rfl⟩ : syracuseStep 363737465 = 272803099) B272803099
theorem B242491643 : Blo 2213435 242491643 := bstep (se 1 (by rfl) ⟨181868732, by rfl⟩ : syracuseStep 242491643 = 363737465) B363737465
theorem B161661095 : Blo 2213435 161661095 := bstep (se 1 (by rfl) ⟨121245821, by rfl⟩ : syracuseStep 161661095 = 242491643) B242491643
theorem B107774063 : Blo 2213435 107774063 := bstep (se 1 (by rfl) ⟨80830547, by rfl⟩ : syracuseStep 107774063 = 161661095) B161661095
theorem B71849375 : Blo 2213435 71849375 := bstep (se 1 (by rfl) ⟨53887031, by rfl⟩ : syracuseStep 71849375 = 107774063) B107774063
theorem B47899583 : Blo 2213435 47899583 := bstep (se 1 (by rfl) ⟨35924687, by rfl⟩ : syracuseStep 47899583 = 71849375) B71849375
theorem B31933055 : Blo 2213435 31933055 := bstep (se 1 (by rfl) ⟨23949791, by rfl⟩ : syracuseStep 31933055 = 47899583) B47899583
theorem B21288703 : Blo 2213435 21288703 := bstep (se 1 (by rfl) ⟨15966527, by rfl⟩ : syracuseStep 21288703 = 31933055) B31933055
theorem B28384937 : Blo 2213435 28384937 := bstep (se 2 (by rfl) ⟨10644351, by rfl⟩ : syracuseStep 28384937 = 21288703) B21288703
theorem B18923291 : Blo 2213435 18923291 := bstep (se 1 (by rfl) ⟨14192468, by rfl⟩ : syracuseStep 18923291 = 28384937) B28384937
theorem B12615527 : Blo 2213435 12615527 := bstep (se 1 (by rfl) ⟨9461645, by rfl⟩ : syracuseStep 12615527 = 18923291) B18923291
theorem B8410351 : Blo 2213435 8410351 := bstep (se 1 (by rfl) ⟨6307763, by rfl⟩ : syracuseStep 8410351 = 12615527) B12615527
theorem B11213801 : Blo 2213435 11213801 := bstep (se 2 (by rfl) ⟨4205175, by rfl⟩ : syracuseStep 11213801 = 8410351) B8410351
theorem B7475867 : Blo 2213435 7475867 := bstep (se 1 (by rfl) ⟨5606900, by rfl⟩ : syracuseStep 7475867 = 11213801) B11213801
theorem B4983911 : Blo 2213435 4983911 := bstep (se 1 (by rfl) ⟨3737933, by rfl⟩ : syracuseStep 4983911 = 7475867) B7475867
theorem B3322607 : Blo 2213435 3322607 := bstep (se 1 (by rfl) ⟨2491955, by rfl⟩ : syracuseStep 3322607 = 4983911) B4983911
theorem B2215071 : Blo 2213435 2215071 := bstep (se 1 (by rfl) ⟨1661303, by rfl⟩ : syracuseStep 2215071 = 3322607) B3322607
theorem B3322613 : Blo 2213435 3322613 := bbase (se 5 (by rfl) ⟨155747, by rfl⟩ : syracuseStep 3322613 = 311495) (by norm_num)
theorem B2215075 : Blo 2213435 2215075 := bstep (se 1 (by rfl) ⟨1661306, by rfl⟩ : syracuseStep 2215075 = 3322613) B3322613
theorem B7096261 : Blo 2213435 7096261 := bbase (se 4 (by rfl) ⟨665274, by rfl⟩ : syracuseStep 7096261 = 1330549) (by norm_num)
theorem B9461681 : Blo 2213435 9461681 := bstep (se 2 (by rfl) ⟨3548130, by rfl⟩ : syracuseStep 9461681 = 7096261) B7096261
theorem B6307787 : Blo 2213435 6307787 := bstep (se 1 (by rfl) ⟨4730840, by rfl⟩ : syracuseStep 6307787 = 9461681) B9461681
theorem B4205191 : Blo 2213435 4205191 := bstep (se 1 (by rfl) ⟨3153893, by rfl⟩ : syracuseStep 4205191 = 6307787) B6307787
theorem B5606921 : Blo 2213435 5606921 := bstep (se 2 (by rfl) ⟨2102595, by rfl⟩ : syracuseStep 5606921 = 4205191) B4205191
theorem B3737947 : Blo 2213435 3737947 := bstep (se 1 (by rfl) ⟨2803460, by rfl⟩ : syracuseStep 3737947 = 5606921) B5606921
theorem B4983929 : Blo 2213435 4983929 := bstep (se 2 (by rfl) ⟨1868973, by rfl⟩ : syracuseStep 4983929 = 3737947) B3737947
theorem B3322619 : Blo 2213435 3322619 := bstep (se 1 (by rfl) ⟨2491964, by rfl⟩ : syracuseStep 3322619 = 4983929) B4983929
theorem B2215079 : Blo 2213435 2215079 := bstep (se 1 (by rfl) ⟨1661309, by rfl⟩ : syracuseStep 2215079 = 3322619) B3322619
theorem B2491969 : Blo 2213435 2491969 := bbase (se 2 (by rfl) ⟨934488, by rfl⟩ : syracuseStep 2491969 = 1868977) (by norm_num)
theorem B3322625 : Blo 2213435 3322625 := bstep (se 2 (by rfl) ⟨1245984, by rfl⟩ : syracuseStep 3322625 = 2491969) B2491969
theorem B2215083 : Blo 2213435 2215083 := bstep (se 1 (by rfl) ⟨1661312, by rfl⟩ : syracuseStep 2215083 = 3322625) B3322625
theorem B5606941 : Blo 2213435 5606941 := bbase (se 3 (by rfl) ⟨1051301, by rfl⟩ : syracuseStep 5606941 = 2102603) (by norm_num)
theorem B7475921 : Blo 2213435 7475921 := bstep (se 2 (by rfl) ⟨2803470, by rfl⟩ : syracuseStep 7475921 = 5606941) B5606941
theorem B4983947 : Blo 2213435 4983947 := bstep (se 1 (by rfl) ⟨3737960, by rfl⟩ : syracuseStep 4983947 = 7475921) B7475921
theorem B3322631 : Blo 2213435 3322631 := bstep (se 1 (by rfl) ⟨2491973, by rfl⟩ : syracuseStep 3322631 = 4983947) B4983947
theorem B2215087 : Blo 2213435 2215087 := bstep (se 1 (by rfl) ⟨1661315, by rfl⟩ : syracuseStep 2215087 = 3322631) B3322631
theorem B3322637 : Blo 2213435 3322637 := bbase (se 3 (by rfl) ⟨622994, by rfl⟩ : syracuseStep 3322637 = 1245989) (by norm_num)
theorem B2215091 : Blo 2213435 2215091 := bstep (se 1 (by rfl) ⟨1661318, by rfl⟩ : syracuseStep 2215091 = 3322637) B3322637
theorem B4983965 : Blo 2213435 4983965 := bbase (se 3 (by rfl) ⟨934493, by rfl⟩ : syracuseStep 4983965 = 1868987) (by norm_num)
theorem B3322643 : Blo 2213435 3322643 := bstep (se 1 (by rfl) ⟨2491982, by rfl⟩ : syracuseStep 3322643 = 4983965) B4983965
theorem B2215095 : Blo 2213435 2215095 := bstep (se 1 (by rfl) ⟨1661321, by rfl⟩ : syracuseStep 2215095 = 3322643) B3322643
theorem B3737981 : Blo 2213435 3737981 := bbase (se 3 (by rfl) ⟨700871, by rfl⟩ : syracuseStep 3737981 = 1401743) (by norm_num)
theorem B2491987 : Blo 2213435 2491987 := bstep (se 1 (by rfl) ⟨1868990, by rfl⟩ : syracuseStep 2491987 = 3737981) B3737981
theorem B3322649 : Blo 2213435 3322649 := bstep (se 2 (by rfl) ⟨1245993, by rfl⟩ : syracuseStep 3322649 = 2491987) B2491987
theorem B2215099 : Blo 2213435 2215099 := bstep (se 1 (by rfl) ⟨1661324, by rfl⟩ : syracuseStep 2215099 = 3322649) B3322649
theorem B5322253 : Blo 2213435 5322253 := bbase (se 3 (by rfl) ⟨997922, by rfl⟩ : syracuseStep 5322253 = 1995845) (by norm_num)
theorem B7096337 : Blo 2213435 7096337 := bstep (se 2 (by rfl) ⟨2661126, by rfl⟩ : syracuseStep 7096337 = 5322253) B5322253
theorem B4730891 : Blo 2213435 4730891 := bstep (se 1 (by rfl) ⟨3548168, by rfl⟩ : syracuseStep 4730891 = 7096337) B7096337
theorem B12615709 : Blo 2213435 12615709 := bstep (se 3 (by rfl) ⟨2365445, by rfl⟩ : syracuseStep 12615709 = 4730891) B4730891
theorem B16820945 : Blo 2213435 16820945 := bstep (se 2 (by rfl) ⟨6307854, by rfl⟩ : syracuseStep 16820945 = 12615709) B12615709
theorem B11213963 : Blo 2213435 11213963 := bstep (se 1 (by rfl) ⟨8410472, by rfl⟩ : syracuseStep 11213963 = 16820945) B16820945
theorem B7475975 : Blo 2213435 7475975 := bstep (se 1 (by rfl) ⟨5606981, by rfl⟩ : syracuseStep 7475975 = 11213963) B11213963
theorem B4983983 : Blo 2213435 4983983 := bstep (se 1 (by rfl) ⟨3737987, by rfl⟩ : syracuseStep 4983983 = 7475975) B7475975
theorem B3322655 : Blo 2213435 3322655 := bstep (se 1 (by rfl) ⟨2491991, by rfl⟩ : syracuseStep 3322655 = 4983983) B4983983
theorem B2215103 : Blo 2213435 2215103 := bstep (se 1 (by rfl) ⟨1661327, by rfl⟩ : syracuseStep 2215103 = 3322655) B3322655
theorem B3322661 : Blo 2213435 3322661 := bbase (se 4 (by rfl) ⟨311499, by rfl⟩ : syracuseStep 3322661 = 622999) (by norm_num)
theorem B2215107 : Blo 2213435 2215107 := bstep (se 1 (by rfl) ⟨1661330, by rfl⟩ : syracuseStep 2215107 = 3322661) B3322661
theorem B2803501 : Blo 2213435 2803501 := bbase (se 3 (by rfl) ⟨525656, by rfl⟩ : syracuseStep 2803501 = 1051313) (by norm_num)
theorem B3738001 : Blo 2213435 3738001 := bstep (se 2 (by rfl) ⟨1401750, by rfl⟩ : syracuseStep 3738001 = 2803501) B2803501
theorem B4984001 : Blo 2213435 4984001 := bstep (se 2 (by rfl) ⟨1869000, by rfl⟩ : syracuseStep 4984001 = 3738001) B3738001
theorem B3322667 : Blo 2213435 3322667 := bstep (se 1 (by rfl) ⟨2492000, by rfl⟩ : syracuseStep 3322667 = 4984001) B4984001
theorem B2215111 : Blo 2213435 2215111 := bstep (se 1 (by rfl) ⟨1661333, by rfl⟩ : syracuseStep 2215111 = 3322667) B3322667
theorem B2492005 : Blo 2213435 2492005 := bbase (se 4 (by rfl) ⟨233625, by rfl⟩ : syracuseStep 2492005 = 467251) (by norm_num)
theorem B3322673 : Blo 2213435 3322673 := bstep (se 2 (by rfl) ⟨1246002, by rfl⟩ : syracuseStep 3322673 = 2492005) B2492005
theorem B2215115 : Blo 2213435 2215115 := bstep (se 1 (by rfl) ⟨1661336, by rfl⟩ : syracuseStep 2215115 = 3322673) B3322673
theorem B5322293 : Blo 2213435 5322293 := bbase (se 5 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 5322293 = 498965) (by norm_num)
theorem B3548195 : Blo 2213435 3548195 := bstep (se 1 (by rfl) ⟨2661146, by rfl⟩ : syracuseStep 3548195 = 5322293) B5322293
theorem B2365463 : Blo 2213435 2365463 := bstep (se 1 (by rfl) ⟨1774097, by rfl⟩ : syracuseStep 2365463 = 3548195) B3548195
theorem B6307901 : Blo 2213435 6307901 := bstep (se 3 (by rfl) ⟨1182731, by rfl⟩ : syracuseStep 6307901 = 2365463) B2365463
theorem B4205267 : Blo 2213435 4205267 := bstep (se 1 (by rfl) ⟨3153950, by rfl⟩ : syracuseStep 4205267 = 6307901) B6307901
theorem B2803511 : Blo 2213435 2803511 := bstep (se 1 (by rfl) ⟨2102633, by rfl⟩ : syracuseStep 2803511 = 4205267) B4205267
theorem B7476029 : Blo 2213435 7476029 := bstep (se 3 (by rfl) ⟨1401755, by rfl⟩ : syracuseStep 7476029 = 2803511) B2803511
theorem B4984019 : Blo 2213435 4984019 := bstep (se 1 (by rfl) ⟨3738014, by rfl⟩ : syracuseStep 4984019 = 7476029) B7476029
theorem B3322679 : Blo 2213435 3322679 := bstep (se 1 (by rfl) ⟨2492009, by rfl⟩ : syracuseStep 3322679 = 4984019) B4984019
theorem B2215119 : Blo 2213435 2215119 := bstep (se 1 (by rfl) ⟨1661339, by rfl⟩ : syracuseStep 2215119 = 3322679) B3322679
theorem B3322685 : Blo 2213435 3322685 := bbase (se 3 (by rfl) ⟨623003, by rfl⟩ : syracuseStep 3322685 = 1246007) (by norm_num)
theorem B2215123 : Blo 2213435 2215123 := bstep (se 1 (by rfl) ⟨1661342, by rfl⟩ : syracuseStep 2215123 = 3322685) B3322685
theorem B4984037 : Blo 2213435 4984037 := bbase (se 4 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 4984037 = 934507) (by norm_num)
theorem B3322691 : Blo 2213435 3322691 := bstep (se 1 (by rfl) ⟨2492018, by rfl⟩ : syracuseStep 3322691 = 4984037) B4984037
theorem B2215127 : Blo 2213435 2215127 := bstep (se 1 (by rfl) ⟨1661345, by rfl⟩ : syracuseStep 2215127 = 3322691) B3322691
theorem B5607053 : Blo 2213435 5607053 := bbase (se 3 (by rfl) ⟨1051322, by rfl⟩ : syracuseStep 5607053 = 2102645) (by norm_num)
theorem B3738035 : Blo 2213435 3738035 := bstep (se 1 (by rfl) ⟨2803526, by rfl⟩ : syracuseStep 3738035 = 5607053) B5607053
theorem B2492023 : Blo 2213435 2492023 := bstep (se 1 (by rfl) ⟨1869017, by rfl⟩ : syracuseStep 2492023 = 3738035) B3738035
theorem B3322697 : Blo 2213435 3322697 := bstep (se 2 (by rfl) ⟨1246011, by rfl⟩ : syracuseStep 3322697 = 2492023) B2492023
theorem B2215131 : Blo 2213435 2215131 := bstep (se 1 (by rfl) ⟨1661348, by rfl⟩ : syracuseStep 2215131 = 3322697) B3322697
theorem B3153973 : Blo 2213435 3153973 := bbase (se 5 (by rfl) ⟨147842, by rfl⟩ : syracuseStep 3153973 = 295685) (by norm_num)
theorem B4205297 : Blo 2213435 4205297 := bstep (se 2 (by rfl) ⟨1576986, by rfl⟩ : syracuseStep 4205297 = 3153973) B3153973
theorem B11214125 : Blo 2213435 11214125 := bstep (se 3 (by rfl) ⟨2102648, by rfl⟩ : syracuseStep 11214125 = 4205297) B4205297
theorem B7476083 : Blo 2213435 7476083 := bstep (se 1 (by rfl) ⟨5607062, by rfl⟩ : syracuseStep 7476083 = 11214125) B11214125
theorem B4984055 : Blo 2213435 4984055 := bstep (se 1 (by rfl) ⟨3738041, by rfl⟩ : syracuseStep 4984055 = 7476083) B7476083
theorem B3322703 : Blo 2213435 3322703 := bstep (se 1 (by rfl) ⟨2492027, by rfl⟩ : syracuseStep 3322703 = 4984055) B4984055
theorem B2215135 : Blo 2213435 2215135 := bstep (se 1 (by rfl) ⟨1661351, by rfl⟩ : syracuseStep 2215135 = 3322703) B3322703
theorem B3322709 : Blo 2213435 3322709 := bbase (se 9 (by rfl) ⟨9734, by rfl⟩ : syracuseStep 3322709 = 19469) (by norm_num)
theorem B2215139 : Blo 2213435 2215139 := bstep (se 1 (by rfl) ⟨1661354, by rfl⟩ : syracuseStep 2215139 = 3322709) B3322709
theorem B5052077 : Blo 2213435 5052077 := bbase (se 3 (by rfl) ⟨947264, by rfl⟩ : syracuseStep 5052077 = 1894529) (by norm_num)
theorem B3368051 : Blo 2213435 3368051 := bstep (se 1 (by rfl) ⟨2526038, by rfl⟩ : syracuseStep 3368051 = 5052077) B5052077
theorem B2245367 : Blo 2213435 2245367 := bstep (se 1 (by rfl) ⟨1684025, by rfl⟩ : syracuseStep 2245367 = 3368051) B3368051
theorem B5987645 : Blo 2213435 5987645 := bstep (se 3 (by rfl) ⟨1122683, by rfl⟩ : syracuseStep 5987645 = 2245367) B2245367
theorem B3991763 : Blo 2213435 3991763 := bstep (se 1 (by rfl) ⟨2993822, by rfl⟩ : syracuseStep 3991763 = 5987645) B5987645
theorem B2661175 : Blo 2213435 2661175 := bstep (se 1 (by rfl) ⟨1995881, by rfl⟩ : syracuseStep 2661175 = 3991763) B3991763
theorem B3548233 : Blo 2213435 3548233 := bstep (se 2 (by rfl) ⟨1330587, by rfl⟩ : syracuseStep 3548233 = 2661175) B2661175
theorem B4730977 : Blo 2213435 4730977 := bstep (se 2 (by rfl) ⟨1774116, by rfl⟩ : syracuseStep 4730977 = 3548233) B3548233
theorem B6307969 : Blo 2213435 6307969 := bstep (se 2 (by rfl) ⟨2365488, by rfl⟩ : syracuseStep 6307969 = 4730977) B4730977
theorem B8410625 : Blo 2213435 8410625 := bstep (se 2 (by rfl) ⟨3153984, by rfl⟩ : syracuseStep 8410625 = 6307969) B6307969
theorem B5607083 : Blo 2213435 5607083 := bstep (se 1 (by rfl) ⟨4205312, by rfl⟩ : syracuseStep 5607083 = 8410625) B8410625
theorem B3738055 : Blo 2213435 3738055 := bstep (se 1 (by rfl) ⟨2803541, by rfl⟩ : syracuseStep 3738055 = 5607083) B5607083
theorem B4984073 : Blo 2213435 4984073 := bstep (se 2 (by rfl) ⟨1869027, by rfl⟩ : syracuseStep 4984073 = 3738055) B3738055
theorem B3322715 : Blo 2213435 3322715 := bstep (se 1 (by rfl) ⟨2492036, by rfl⟩ : syracuseStep 3322715 = 4984073) B4984073
theorem B2215143 : Blo 2213435 2215143 := bstep (se 1 (by rfl) ⟨1661357, by rfl⟩ : syracuseStep 2215143 = 3322715) B3322715
theorem B2492041 : Blo 2213435 2492041 := bbase (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) (by norm_num)
theorem B3322721 : Blo 2213435 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B2215147 : Blo 2213435 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B13472245 : Blo 2213435 13472245 := bbase (se 5 (by rfl) ⟨631511, by rfl⟩ : syracuseStep 13472245 = 1263023) (by norm_num)
theorem B17962993 : Blo 2213435 17962993 := bstep (se 2 (by rfl) ⟨6736122, by rfl⟩ : syracuseStep 17962993 = 13472245) B13472245
theorem B23950657 : Blo 2213435 23950657 := bstep (se 2 (by rfl) ⟨8981496, by rfl⟩ : syracuseStep 23950657 = 17962993) B17962993
theorem B31934209 : Blo 2213435 31934209 := bstep (se 2 (by rfl) ⟨11975328, by rfl⟩ : syracuseStep 31934209 = 23950657) B23950657
theorem B42578945 : Blo 2213435 42578945 := bstep (se 2 (by rfl) ⟨15967104, by rfl⟩ : syracuseStep 42578945 = 31934209) B31934209
theorem B28385963 : Blo 2213435 28385963 := bstep (se 1 (by rfl) ⟨21289472, by rfl⟩ : syracuseStep 28385963 = 42578945) B42578945
theorem B18923975 : Blo 2213435 18923975 := bstep (se 1 (by rfl) ⟨14192981, by rfl⟩ : syracuseStep 18923975 = 28385963) B28385963
theorem B12615983 : Blo 2213435 12615983 := bstep (se 1 (by rfl) ⟨9461987, by rfl⟩ : syracuseStep 12615983 = 18923975) B18923975
theorem B8410655 : Blo 2213435 8410655 := bstep (se 1 (by rfl) ⟨6307991, by rfl⟩ : syracuseStep 8410655 = 12615983) B12615983
theorem B5607103 : Blo 2213435 5607103 := bstep (se 1 (by rfl) ⟨4205327, by rfl⟩ : syracuseStep 5607103 = 8410655) B8410655
theorem B7476137 : Blo 2213435 7476137 := bstep (se 2 (by rfl) ⟨2803551, by rfl⟩ : syracuseStep 7476137 = 5607103) B5607103
theorem B4984091 : Blo 2213435 4984091 := bstep (se 1 (by rfl) ⟨3738068, by rfl⟩ : syracuseStep 4984091 = 7476137) B7476137
theorem B3322727 : Blo 2213435 3322727 := bstep (se 1 (by rfl) ⟨2492045, by rfl⟩ : syracuseStep 3322727 = 4984091) B4984091
theorem B2215151 : Blo 2213435 2215151 := bstep (se 1 (by rfl) ⟨1661363, by rfl⟩ : syracuseStep 2215151 = 3322727) B3322727
theorem B3322733 : Blo 2213435 3322733 := bbase (se 3 (by rfl) ⟨623012, by rfl⟩ : syracuseStep 3322733 = 1246025) (by norm_num)
theorem B2215155 : Blo 2213435 2215155 := bstep (se 1 (by rfl) ⟨1661366, by rfl⟩ : syracuseStep 2215155 = 3322733) B3322733
theorem B4984109 : Blo 2213435 4984109 := bbase (se 3 (by rfl) ⟨934520, by rfl⟩ : syracuseStep 4984109 = 1869041) (by norm_num)
theorem B3322739 : Blo 2213435 3322739 := bstep (se 1 (by rfl) ⟨2492054, by rfl⟩ : syracuseStep 3322739 = 4984109) B4984109
theorem B2215159 : Blo 2213435 2215159 := bstep (se 1 (by rfl) ⟨1661369, by rfl⟩ : syracuseStep 2215159 = 3322739) B3322739
theorem B2526061 : Blo 2213435 2526061 := bbase (se 3 (by rfl) ⟨473636, by rfl⟩ : syracuseStep 2526061 = 947273) (by norm_num)
theorem B3368081 : Blo 2213435 3368081 := bstep (se 2 (by rfl) ⟨1263030, by rfl⟩ : syracuseStep 3368081 = 2526061) B2526061
theorem B8981549 : Blo 2213435 8981549 := bstep (se 3 (by rfl) ⟨1684040, by rfl⟩ : syracuseStep 8981549 = 3368081) B3368081
theorem B5987699 : Blo 2213435 5987699 := bstep (se 1 (by rfl) ⟨4490774, by rfl⟩ : syracuseStep 5987699 = 8981549) B8981549
theorem B3991799 : Blo 2213435 3991799 := bstep (se 1 (by rfl) ⟨2993849, by rfl⟩ : syracuseStep 3991799 = 5987699) B5987699
theorem B10644797 : Blo 2213435 10644797 := bstep (se 3 (by rfl) ⟨1995899, by rfl⟩ : syracuseStep 10644797 = 3991799) B3991799
theorem B7096531 : Blo 2213435 7096531 := bstep (se 1 (by rfl) ⟨5322398, by rfl⟩ : syracuseStep 7096531 = 10644797) B10644797
theorem B9462041 : Blo 2213435 9462041 := bstep (se 2 (by rfl) ⟨3548265, by rfl⟩ : syracuseStep 9462041 = 7096531) B7096531
theorem B6308027 : Blo 2213435 6308027 := bstep (se 1 (by rfl) ⟨4731020, by rfl⟩ : syracuseStep 6308027 = 9462041) B9462041
theorem B4205351 : Blo 2213435 4205351 := bstep (se 1 (by rfl) ⟨3154013, by rfl⟩ : syracuseStep 4205351 = 6308027) B6308027
theorem B2803567 : Blo 2213435 2803567 := bstep (se 1 (by rfl) ⟨2102675, by rfl⟩ : syracuseStep 2803567 = 4205351) B4205351
theorem B3738089 : Blo 2213435 3738089 := bstep (se 2 (by rfl) ⟨1401783, by rfl⟩ : syracuseStep 3738089 = 2803567) B2803567
theorem B2492059 : Blo 2213435 2492059 := bstep (se 1 (by rfl) ⟨1869044, by rfl⟩ : syracuseStep 2492059 = 3738089) B3738089
theorem B3322745 : Blo 2213435 3322745 := bstep (se 2 (by rfl) ⟨1246029, by rfl⟩ : syracuseStep 3322745 = 2492059) B2492059
theorem B2215163 : Blo 2213435 2215163 := bstep (se 1 (by rfl) ⟨1661372, by rfl⟩ : syracuseStep 2215163 = 3322745) B3322745
theorem B5683645 : Blo 2213435 5683645 := bbase (se 3 (by rfl) ⟨1065683, by rfl⟩ : syracuseStep 5683645 = 2131367) (by norm_num)
theorem B7578193 : Blo 2213435 7578193 := bstep (se 2 (by rfl) ⟨2841822, by rfl⟩ : syracuseStep 7578193 = 5683645) B5683645
theorem B10104257 : Blo 2213435 10104257 := bstep (se 2 (by rfl) ⟨3789096, by rfl⟩ : syracuseStep 10104257 = 7578193) B7578193
theorem B6736171 : Blo 2213435 6736171 := bstep (se 1 (by rfl) ⟨5052128, by rfl⟩ : syracuseStep 6736171 = 10104257) B10104257
theorem B8981561 : Blo 2213435 8981561 := bstep (se 2 (by rfl) ⟨3368085, by rfl⟩ : syracuseStep 8981561 = 6736171) B6736171
theorem B23950829 : Blo 2213435 23950829 := bstep (se 3 (by rfl) ⟨4490780, by rfl⟩ : syracuseStep 23950829 = 8981561) B8981561
theorem B15967219 : Blo 2213435 15967219 := bstep (se 1 (by rfl) ⟨11975414, by rfl⟩ : syracuseStep 15967219 = 23950829) B23950829
theorem B21289625 : Blo 2213435 21289625 := bstep (se 2 (by rfl) ⟨7983609, by rfl⟩ : syracuseStep 21289625 = 15967219) B15967219
theorem B14193083 : Blo 2213435 14193083 := bstep (se 1 (by rfl) ⟨10644812, by rfl⟩ : syracuseStep 14193083 = 21289625) B21289625
theorem B37848221 : Blo 2213435 37848221 := bstep (se 3 (by rfl) ⟨7096541, by rfl⟩ : syracuseStep 37848221 = 14193083) B14193083
theorem B25232147 : Blo 2213435 25232147 := bstep (se 1 (by rfl) ⟨18924110, by rfl⟩ : syracuseStep 25232147 = 37848221) B37848221
theorem B16821431 : Blo 2213435 16821431 := bstep (se 1 (by rfl) ⟨12616073, by rfl⟩ : syracuseStep 16821431 = 25232147) B25232147
theorem B11214287 : Blo 2213435 11214287 := bstep (se 1 (by rfl) ⟨8410715, by rfl⟩ : syracuseStep 11214287 = 16821431) B16821431
theorem B7476191 : Blo 2213435 7476191 := bstep (se 1 (by rfl) ⟨5607143, by rfl⟩ : syracuseStep 7476191 = 11214287) B11214287
theorem B4984127 : Blo 2213435 4984127 := bstep (se 1 (by rfl) ⟨3738095, by rfl⟩ : syracuseStep 4984127 = 7476191) B7476191
theorem B3322751 : Blo 2213435 3322751 := bstep (se 1 (by rfl) ⟨2492063, by rfl⟩ : syracuseStep 3322751 = 4984127) B4984127
theorem B2215167 : Blo 2213435 2215167 := bstep (se 1 (by rfl) ⟨1661375, by rfl⟩ : syracuseStep 2215167 = 3322751) B3322751
theorem B3322757 : Blo 2213435 3322757 := bbase (se 4 (by rfl) ⟨311508, by rfl⟩ : syracuseStep 3322757 = 623017) (by norm_num)
theorem B2215171 : Blo 2213435 2215171 := bstep (se 1 (by rfl) ⟨1661378, by rfl⟩ : syracuseStep 2215171 = 3322757) B3322757
theorem B3738109 : Blo 2213435 3738109 := bbase (se 3 (by rfl) ⟨700895, by rfl⟩ : syracuseStep 3738109 = 1401791) (by norm_num)
theorem B4984145 : Blo 2213435 4984145 := bstep (se 2 (by rfl) ⟨1869054, by rfl⟩ : syracuseStep 4984145 = 3738109) B3738109
theorem B3322763 : Blo 2213435 3322763 := bstep (se 1 (by rfl) ⟨2492072, by rfl⟩ : syracuseStep 3322763 = 4984145) B4984145
theorem B2215175 : Blo 2213435 2215175 := bstep (se 1 (by rfl) ⟨1661381, by rfl⟩ : syracuseStep 2215175 = 3322763) B3322763
theorem B2492077 : Blo 2213435 2492077 := bbase (se 3 (by rfl) ⟨467264, by rfl⟩ : syracuseStep 2492077 = 934529) (by norm_num)
theorem B3322769 : Blo 2213435 3322769 := bstep (se 2 (by rfl) ⟨1246038, by rfl⟩ : syracuseStep 3322769 = 2492077) B2492077
theorem B2215179 : Blo 2213435 2215179 := bstep (se 1 (by rfl) ⟨1661384, by rfl⟩ : syracuseStep 2215179 = 3322769) B3322769
theorem B7476245 : Blo 2213435 7476245 := bbase (se 6 (by rfl) ⟨175224, by rfl⟩ : syracuseStep 7476245 = 350449) (by norm_num)
theorem B4984163 : Blo 2213435 4984163 := bstep (se 1 (by rfl) ⟨3738122, by rfl⟩ : syracuseStep 4984163 = 7476245) B7476245
theorem B3322775 : Blo 2213435 3322775 := bstep (se 1 (by rfl) ⟨2492081, by rfl⟩ : syracuseStep 3322775 = 4984163) B4984163
theorem B2215183 : Blo 2213435 2215183 := bstep (se 1 (by rfl) ⟨1661387, by rfl⟩ : syracuseStep 2215183 = 3322775) B3322775
theorem B3322781 : Blo 2213435 3322781 := bbase (se 3 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 3322781 = 1246043) (by norm_num)
theorem B2215187 : Blo 2213435 2215187 := bstep (se 1 (by rfl) ⟨1661390, by rfl⟩ : syracuseStep 2215187 = 3322781) B3322781
theorem B4984181 : Blo 2213435 4984181 := bbase (se 5 (by rfl) ⟨233633, by rfl⟩ : syracuseStep 4984181 = 467267) (by norm_num)
theorem B3322787 : Blo 2213435 3322787 := bstep (se 1 (by rfl) ⟨2492090, by rfl⟩ : syracuseStep 3322787 = 4984181) B4984181
theorem B2215191 : Blo 2213435 2215191 := bstep (se 1 (by rfl) ⟨1661393, by rfl⟩ : syracuseStep 2215191 = 3322787) B3322787
theorem B10644949 : Blo 2213435 10644949 := bbase (se 7 (by rfl) ⟨124745, by rfl⟩ : syracuseStep 10644949 = 249491) (by norm_num)
theorem B14193265 : Blo 2213435 14193265 := bstep (se 2 (by rfl) ⟨5322474, by rfl⟩ : syracuseStep 14193265 = 10644949) B10644949
theorem B18924353 : Blo 2213435 18924353 := bstep (se 2 (by rfl) ⟨7096632, by rfl⟩ : syracuseStep 18924353 = 14193265) B14193265
theorem B12616235 : Blo 2213435 12616235 := bstep (se 1 (by rfl) ⟨9462176, by rfl⟩ : syracuseStep 12616235 = 18924353) B18924353
theorem B8410823 : Blo 2213435 8410823 := bstep (se 1 (by rfl) ⟨6308117, by rfl⟩ : syracuseStep 8410823 = 12616235) B12616235
theorem B5607215 : Blo 2213435 5607215 := bstep (se 1 (by rfl) ⟨4205411, by rfl⟩ : syracuseStep 5607215 = 8410823) B8410823
theorem B3738143 : Blo 2213435 3738143 := bstep (se 1 (by rfl) ⟨2803607, by rfl⟩ : syracuseStep 3738143 = 5607215) B5607215
theorem B2492095 : Blo 2213435 2492095 := bstep (se 1 (by rfl) ⟨1869071, by rfl⟩ : syracuseStep 2492095 = 3738143) B3738143
theorem B3322793 : Blo 2213435 3322793 := bstep (se 2 (by rfl) ⟨1246047, by rfl⟩ : syracuseStep 3322793 = 2492095) B2492095
theorem B2215195 : Blo 2213435 2215195 := bstep (se 1 (by rfl) ⟨1661396, by rfl⟩ : syracuseStep 2215195 = 3322793) B3322793
theorem B8410837 : Blo 2213435 8410837 := bbase (se 7 (by rfl) ⟨98564, by rfl⟩ : syracuseStep 8410837 = 197129) (by norm_num)
theorem B11214449 : Blo 2213435 11214449 := bstep (se 2 (by rfl) ⟨4205418, by rfl⟩ : syracuseStep 11214449 = 8410837) B8410837
theorem B7476299 : Blo 2213435 7476299 := bstep (se 1 (by rfl) ⟨5607224, by rfl⟩ : syracuseStep 7476299 = 11214449) B11214449
theorem B4984199 : Blo 2213435 4984199 := bstep (se 1 (by rfl) ⟨3738149, by rfl⟩ : syracuseStep 4984199 = 7476299) B7476299
theorem B3322799 : Blo 2213435 3322799 := bstep (se 1 (by rfl) ⟨2492099, by rfl⟩ : syracuseStep 3322799 = 4984199) B4984199
theorem B2215199 : Blo 2213435 2215199 := bstep (se 1 (by rfl) ⟨1661399, by rfl⟩ : syracuseStep 2215199 = 3322799) B3322799
theorem B3322805 : Blo 2213435 3322805 := bbase (se 5 (by rfl) ⟨155756, by rfl⟩ : syracuseStep 3322805 = 311513) (by norm_num)
theorem B2215203 : Blo 2213435 2215203 := bstep (se 1 (by rfl) ⟨1661402, by rfl⟩ : syracuseStep 2215203 = 3322805) B3322805
theorem B5607245 : Blo 2213435 5607245 := bbase (se 3 (by rfl) ⟨1051358, by rfl⟩ : syracuseStep 5607245 = 2102717) (by norm_num)
theorem B3738163 : Blo 2213435 3738163 := bstep (se 1 (by rfl) ⟨2803622, by rfl⟩ : syracuseStep 3738163 = 5607245) B5607245
theorem B4984217 : Blo 2213435 4984217 := bstep (se 2 (by rfl) ⟨1869081, by rfl⟩ : syracuseStep 4984217 = 3738163) B3738163
theorem B3322811 : Blo 2213435 3322811 := bstep (se 1 (by rfl) ⟨2492108, by rfl⟩ : syracuseStep 3322811 = 4984217) B4984217
theorem B2215207 : Blo 2213435 2215207 := bstep (se 1 (by rfl) ⟨1661405, by rfl⟩ : syracuseStep 2215207 = 3322811) B3322811
theorem B2492113 : Blo 2213435 2492113 := bbase (se 2 (by rfl) ⟨934542, by rfl⟩ : syracuseStep 2492113 = 1869085) (by norm_num)
theorem B3322817 : Blo 2213435 3322817 := bstep (se 2 (by rfl) ⟨1246056, by rfl⟩ : syracuseStep 3322817 = 2492113) B2492113
theorem B2215211 : Blo 2213435 2215211 := bstep (se 1 (by rfl) ⟨1661408, by rfl⟩ : syracuseStep 2215211 = 3322817) B3322817
theorem B3840877 : Blo 2213435 3840877 := bbase (se 3 (by rfl) ⟨720164, by rfl⟩ : syracuseStep 3840877 = 1440329) (by norm_num)
theorem B20484677 : Blo 2213435 20484677 := bstep (se 4 (by rfl) ⟨1920438, by rfl⟩ : syracuseStep 20484677 = 3840877) B3840877
theorem B54625805 : Blo 2213435 54625805 := bstep (se 3 (by rfl) ⟨10242338, by rfl⟩ : syracuseStep 54625805 = 20484677) B20484677
theorem B36417203 : Blo 2213435 36417203 := bstep (se 1 (by rfl) ⟨27312902, by rfl⟩ : syracuseStep 36417203 = 54625805) B54625805
theorem B24278135 : Blo 2213435 24278135 := bstep (se 1 (by rfl) ⟨18208601, by rfl⟩ : syracuseStep 24278135 = 36417203) B36417203
theorem B64741693 : Blo 2213435 64741693 := bstep (se 3 (by rfl) ⟨12139067, by rfl⟩ : syracuseStep 64741693 = 24278135) B24278135
theorem B86322257 : Blo 2213435 86322257 := bstep (se 2 (by rfl) ⟨32370846, by rfl⟩ : syracuseStep 86322257 = 64741693) B64741693
theorem B57548171 : Blo 2213435 57548171 := bstep (se 1 (by rfl) ⟨43161128, by rfl⟩ : syracuseStep 57548171 = 86322257) B86322257
theorem B153461789 : Blo 2213435 153461789 := bstep (se 3 (by rfl) ⟨28774085, by rfl⟩ : syracuseStep 153461789 = 57548171) B57548171
theorem B102307859 : Blo 2213435 102307859 := bstep (se 1 (by rfl) ⟨76730894, by rfl⟩ : syracuseStep 102307859 = 153461789) B153461789
theorem B68205239 : Blo 2213435 68205239 := bstep (se 1 (by rfl) ⟨51153929, by rfl⟩ : syracuseStep 68205239 = 102307859) B102307859
theorem B45470159 : Blo 2213435 45470159 := bstep (se 1 (by rfl) ⟨34102619, by rfl⟩ : syracuseStep 45470159 = 68205239) B68205239
theorem B30313439 : Blo 2213435 30313439 := bstep (se 1 (by rfl) ⟨22735079, by rfl⟩ : syracuseStep 30313439 = 45470159) B45470159
theorem B20208959 : Blo 2213435 20208959 := bstep (se 1 (by rfl) ⟨15156719, by rfl⟩ : syracuseStep 20208959 = 30313439) B30313439
theorem B13472639 : Blo 2213435 13472639 := bstep (se 1 (by rfl) ⟨10104479, by rfl⟩ : syracuseStep 13472639 = 20208959) B20208959
theorem B8981759 : Blo 2213435 8981759 := bstep (se 1 (by rfl) ⟨6736319, by rfl⟩ : syracuseStep 8981759 = 13472639) B13472639
theorem B5987839 : Blo 2213435 5987839 := bstep (se 1 (by rfl) ⟨4490879, by rfl⟩ : syracuseStep 5987839 = 8981759) B8981759
theorem B7983785 : Blo 2213435 7983785 := bstep (se 2 (by rfl) ⟨2993919, by rfl⟩ : syracuseStep 7983785 = 5987839) B5987839
theorem B5322523 : Blo 2213435 5322523 := bstep (se 1 (by rfl) ⟨3991892, by rfl⟩ : syracuseStep 5322523 = 7983785) B7983785
theorem B7096697 : Blo 2213435 7096697 := bstep (se 2 (by rfl) ⟨2661261, by rfl⟩ : syracuseStep 7096697 = 5322523) B5322523
theorem B4731131 : Blo 2213435 4731131 := bstep (se 1 (by rfl) ⟨3548348, by rfl⟩ : syracuseStep 4731131 = 7096697) B7096697
theorem B3154087 : Blo 2213435 3154087 := bstep (se 1 (by rfl) ⟨2365565, by rfl⟩ : syracuseStep 3154087 = 4731131) B4731131
theorem B4205449 : Blo 2213435 4205449 := bstep (se 2 (by rfl) ⟨1577043, by rfl⟩ : syracuseStep 4205449 = 3154087) B3154087
theorem B5607265 : Blo 2213435 5607265 := bstep (se 2 (by rfl) ⟨2102724, by rfl⟩ : syracuseStep 5607265 = 4205449) B4205449
theorem B7476353 : Blo 2213435 7476353 := bstep (se 2 (by rfl) ⟨2803632, by rfl⟩ : syracuseStep 7476353 = 5607265) B5607265
theorem B4984235 : Blo 2213435 4984235 := bstep (se 1 (by rfl) ⟨3738176, by rfl⟩ : syracuseStep 4984235 = 7476353) B7476353
theorem B3322823 : Blo 2213435 3322823 := bstep (se 1 (by rfl) ⟨2492117, by rfl⟩ : syracuseStep 3322823 = 4984235) B4984235
theorem B2215215 : Blo 2213435 2215215 := bstep (se 1 (by rfl) ⟨1661411, by rfl⟩ : syracuseStep 2215215 = 3322823) B3322823
theorem B3322829 : Blo 2213435 3322829 := bbase (se 3 (by rfl) ⟨623030, by rfl⟩ : syracuseStep 3322829 = 1246061) (by norm_num)
theorem B2215219 : Blo 2213435 2215219 := bstep (se 1 (by rfl) ⟨1661414, by rfl⟩ : syracuseStep 2215219 = 3322829) B3322829
theorem B4984253 : Blo 2213435 4984253 := bbase (se 3 (by rfl) ⟨934547, by rfl⟩ : syracuseStep 4984253 = 1869095) (by norm_num)
theorem B3322835 : Blo 2213435 3322835 := bstep (se 1 (by rfl) ⟨2492126, by rfl⟩ : syracuseStep 3322835 = 4984253) B4984253
theorem B2215223 : Blo 2213435 2215223 := bstep (se 1 (by rfl) ⟨1661417, by rfl⟩ : syracuseStep 2215223 = 3322835) B3322835
theorem B3738197 : Blo 2213435 3738197 := bbase (se 8 (by rfl) ⟨21903, by rfl⟩ : syracuseStep 3738197 = 43807) (by norm_num)
theorem B2492131 : Blo 2213435 2492131 := bstep (se 1 (by rfl) ⟨1869098, by rfl⟩ : syracuseStep 2492131 = 3738197) B3738197
theorem B3322841 : Blo 2213435 3322841 := bstep (se 2 (by rfl) ⟨1246065, by rfl⟩ : syracuseStep 3322841 = 2492131) B2492131
theorem B2215227 : Blo 2213435 2215227 := bstep (se 1 (by rfl) ⟨1661420, by rfl⟩ : syracuseStep 2215227 = 3322841) B3322841
theorem B4614293 : Blo 2213435 4614293 := bbase (se 6 (by rfl) ⟨108147, by rfl⟩ : syracuseStep 4614293 = 216295) (by norm_num)
theorem B12304781 : Blo 2213435 12304781 := bstep (se 3 (by rfl) ⟨2307146, by rfl⟩ : syracuseStep 12304781 = 4614293) B4614293
theorem B8203187 : Blo 2213435 8203187 := bstep (se 1 (by rfl) ⟨6152390, by rfl⟩ : syracuseStep 8203187 = 12304781) B12304781
theorem B5468791 : Blo 2213435 5468791 := bstep (se 1 (by rfl) ⟨4101593, by rfl⟩ : syracuseStep 5468791 = 8203187) B8203187
theorem B7291721 : Blo 2213435 7291721 := bstep (se 2 (by rfl) ⟨2734395, by rfl⟩ : syracuseStep 7291721 = 5468791) B5468791
theorem B4861147 : Blo 2213435 4861147 := bstep (se 1 (by rfl) ⟨3645860, by rfl⟩ : syracuseStep 4861147 = 7291721) B7291721
theorem B6481529 : Blo 2213435 6481529 := bstep (se 2 (by rfl) ⟨2430573, by rfl⟩ : syracuseStep 6481529 = 4861147) B4861147
theorem B4321019 : Blo 2213435 4321019 := bstep (se 1 (by rfl) ⟨3240764, by rfl⟩ : syracuseStep 4321019 = 6481529) B6481529
theorem B2880679 : Blo 2213435 2880679 := bstep (se 1 (by rfl) ⟨2160509, by rfl⟩ : syracuseStep 2880679 = 4321019) B4321019
theorem B3840905 : Blo 2213435 3840905 := bstep (se 2 (by rfl) ⟨1440339, by rfl⟩ : syracuseStep 3840905 = 2880679) B2880679
theorem B10242413 : Blo 2213435 10242413 := bstep (se 3 (by rfl) ⟨1920452, by rfl⟩ : syracuseStep 10242413 = 3840905) B3840905
theorem B6828275 : Blo 2213435 6828275 := bstep (se 1 (by rfl) ⟨5121206, by rfl⟩ : syracuseStep 6828275 = 10242413) B10242413
theorem B4552183 : Blo 2213435 4552183 := bstep (se 1 (by rfl) ⟨3414137, by rfl⟩ : syracuseStep 4552183 = 6828275) B6828275
theorem B24278309 : Blo 2213435 24278309 := bstep (se 4 (by rfl) ⟨2276091, by rfl⟩ : syracuseStep 24278309 = 4552183) B4552183
theorem B16185539 : Blo 2213435 16185539 := bstep (se 1 (by rfl) ⟨12139154, by rfl⟩ : syracuseStep 16185539 = 24278309) B24278309
theorem B43161437 : Blo 2213435 43161437 := bstep (se 3 (by rfl) ⟨8092769, by rfl⟩ : syracuseStep 43161437 = 16185539) B16185539
theorem B28774291 : Blo 2213435 28774291 := bstep (se 1 (by rfl) ⟨21580718, by rfl⟩ : syracuseStep 28774291 = 43161437) B43161437
theorem B38365721 : Blo 2213435 38365721 := bstep (se 2 (by rfl) ⟨14387145, by rfl⟩ : syracuseStep 38365721 = 28774291) B28774291
theorem B25577147 : Blo 2213435 25577147 := bstep (se 1 (by rfl) ⟨19182860, by rfl⟩ : syracuseStep 25577147 = 38365721) B38365721
theorem B17051431 : Blo 2213435 17051431 := bstep (se 1 (by rfl) ⟨12788573, by rfl⟩ : syracuseStep 17051431 = 25577147) B25577147
theorem B22735241 : Blo 2213435 22735241 := bstep (se 2 (by rfl) ⟨8525715, by rfl⟩ : syracuseStep 22735241 = 17051431) B17051431
theorem B15156827 : Blo 2213435 15156827 := bstep (se 1 (by rfl) ⟨11367620, by rfl⟩ : syracuseStep 15156827 = 22735241) B22735241
theorem B10104551 : Blo 2213435 10104551 := bstep (se 1 (by rfl) ⟨7578413, by rfl⟩ : syracuseStep 10104551 = 15156827) B15156827
theorem B6736367 : Blo 2213435 6736367 := bstep (se 1 (by rfl) ⟨5052275, by rfl⟩ : syracuseStep 6736367 = 10104551) B10104551
theorem B4490911 : Blo 2213435 4490911 := bstep (se 1 (by rfl) ⟨3368183, by rfl⟩ : syracuseStep 4490911 = 6736367) B6736367
theorem B5987881 : Blo 2213435 5987881 := bstep (se 2 (by rfl) ⟨2245455, by rfl⟩ : syracuseStep 5987881 = 4490911) B4490911
theorem B7983841 : Blo 2213435 7983841 := bstep (se 2 (by rfl) ⟨2993940, by rfl⟩ : syracuseStep 7983841 = 5987881) B5987881
theorem B10645121 : Blo 2213435 10645121 := bstep (se 2 (by rfl) ⟨3991920, by rfl⟩ : syracuseStep 10645121 = 7983841) B7983841
theorem B7096747 : Blo 2213435 7096747 := bstep (se 1 (by rfl) ⟨5322560, by rfl⟩ : syracuseStep 7096747 = 10645121) B10645121
theorem B9462329 : Blo 2213435 9462329 := bstep (se 2 (by rfl) ⟨3548373, by rfl⟩ : syracuseStep 9462329 = 7096747) B7096747
theorem B6308219 : Blo 2213435 6308219 := bstep (se 1 (by rfl) ⟨4731164, by rfl⟩ : syracuseStep 6308219 = 9462329) B9462329
theorem B16821917 : Blo 2213435 16821917 := bstep (se 3 (by rfl) ⟨3154109, by rfl⟩ : syracuseStep 16821917 = 6308219) B6308219
theorem B11214611 : Blo 2213435 11214611 := bstep (se 1 (by rfl) ⟨8410958, by rfl⟩ : syracuseStep 11214611 = 16821917) B16821917
theorem B7476407 : Blo 2213435 7476407 := bstep (se 1 (by rfl) ⟨5607305, by rfl⟩ : syracuseStep 7476407 = 11214611) B11214611
theorem B4984271 : Blo 2213435 4984271 := bstep (se 1 (by rfl) ⟨3738203, by rfl⟩ : syracuseStep 4984271 = 7476407) B7476407
theorem B3322847 : Blo 2213435 3322847 := bstep (se 1 (by rfl) ⟨2492135, by rfl⟩ : syracuseStep 3322847 = 4984271) B4984271
theorem B2215231 : Blo 2213435 2215231 := bstep (se 1 (by rfl) ⟨1661423, by rfl⟩ : syracuseStep 2215231 = 3322847) B3322847
theorem B3322853 : Blo 2213435 3322853 := bbase (se 4 (by rfl) ⟨311517, by rfl⟩ : syracuseStep 3322853 = 623035) (by norm_num)
theorem B2215235 : Blo 2213435 2215235 := bstep (se 1 (by rfl) ⟨1661426, by rfl⟩ : syracuseStep 2215235 = 3322853) B3322853
theorem B5322581 : Blo 2213435 5322581 := bbase (se 9 (by rfl) ⟨15593, by rfl⟩ : syracuseStep 5322581 = 31187) (by norm_num)
theorem B3548387 : Blo 2213435 3548387 := bstep (se 1 (by rfl) ⟨2661290, by rfl⟩ : syracuseStep 3548387 = 5322581) B5322581
theorem B9462365 : Blo 2213435 9462365 := bstep (se 3 (by rfl) ⟨1774193, by rfl⟩ : syracuseStep 9462365 = 3548387) B3548387
theorem B6308243 : Blo 2213435 6308243 := bstep (se 1 (by rfl) ⟨4731182, by rfl⟩ : syracuseStep 6308243 = 9462365) B9462365
theorem B4205495 : Blo 2213435 4205495 := bstep (se 1 (by rfl) ⟨3154121, by rfl⟩ : syracuseStep 4205495 = 6308243) B6308243
theorem B2803663 : Blo 2213435 2803663 := bstep (se 1 (by rfl) ⟨2102747, by rfl⟩ : syracuseStep 2803663 = 4205495) B4205495
theorem B3738217 : Blo 2213435 3738217 := bstep (se 2 (by rfl) ⟨1401831, by rfl⟩ : syracuseStep 3738217 = 2803663) B2803663
theorem B4984289 : Blo 2213435 4984289 := bstep (se 2 (by rfl) ⟨1869108, by rfl⟩ : syracuseStep 4984289 = 3738217) B3738217
theorem B3322859 : Blo 2213435 3322859 := bstep (se 1 (by rfl) ⟨2492144, by rfl⟩ : syracuseStep 3322859 = 4984289) B4984289
theorem B2215239 : Blo 2213435 2215239 := bstep (se 1 (by rfl) ⟨1661429, by rfl⟩ : syracuseStep 2215239 = 3322859) B3322859
theorem B2492149 : Blo 2213435 2492149 := bbase (se 5 (by rfl) ⟨116819, by rfl⟩ : syracuseStep 2492149 = 233639) (by norm_num)
theorem B3322865 : Blo 2213435 3322865 := bstep (se 2 (by rfl) ⟨1246074, by rfl⟩ : syracuseStep 3322865 = 2492149) B2492149
theorem B2215243 : Blo 2213435 2215243 := bstep (se 1 (by rfl) ⟨1661432, by rfl⟩ : syracuseStep 2215243 = 3322865) B3322865
theorem B2803673 : Blo 2213435 2803673 := bbase (se 2 (by rfl) ⟨1051377, by rfl⟩ : syracuseStep 2803673 = 2102755) (by norm_num)
theorem B7476461 : Blo 2213435 7476461 := bstep (se 3 (by rfl) ⟨1401836, by rfl⟩ : syracuseStep 7476461 = 2803673) B2803673
theorem B4984307 : Blo 2213435 4984307 := bstep (se 1 (by rfl) ⟨3738230, by rfl⟩ : syracuseStep 4984307 = 7476461) B7476461
theorem B3322871 : Blo 2213435 3322871 := bstep (se 1 (by rfl) ⟨2492153, by rfl⟩ : syracuseStep 3322871 = 4984307) B4984307
theorem B2215247 : Blo 2213435 2215247 := bstep (se 1 (by rfl) ⟨1661435, by rfl⟩ : syracuseStep 2215247 = 3322871) B3322871
theorem B3322877 : Blo 2213435 3322877 := bbase (se 3 (by rfl) ⟨623039, by rfl⟩ : syracuseStep 3322877 = 1246079) (by norm_num)
theorem B2215251 : Blo 2213435 2215251 := bstep (se 1 (by rfl) ⟨1661438, by rfl⟩ : syracuseStep 2215251 = 3322877) B3322877
theorem B4984325 : Blo 2213435 4984325 := bbase (se 4 (by rfl) ⟨467280, by rfl⟩ : syracuseStep 4984325 = 934561) (by norm_num)
theorem B3322883 : Blo 2213435 3322883 := bstep (se 1 (by rfl) ⟨2492162, by rfl⟩ : syracuseStep 3322883 = 4984325) B4984325
theorem B2215255 : Blo 2213435 2215255 := bstep (se 1 (by rfl) ⟨1661441, by rfl⟩ : syracuseStep 2215255 = 3322883) B3322883
theorem B4205533 : Blo 2213435 4205533 := bbase (se 3 (by rfl) ⟨788537, by rfl⟩ : syracuseStep 4205533 = 1577075) (by norm_num)
theorem B5607377 : Blo 2213435 5607377 := bstep (se 2 (by rfl) ⟨2102766, by rfl⟩ : syracuseStep 5607377 = 4205533) B4205533
theorem B3738251 : Blo 2213435 3738251 := bstep (se 1 (by rfl) ⟨2803688, by rfl⟩ : syracuseStep 3738251 = 5607377) B5607377
theorem B2492167 : Blo 2213435 2492167 := bstep (se 1 (by rfl) ⟨1869125, by rfl⟩ : syracuseStep 2492167 = 3738251) B3738251
theorem B3322889 : Blo 2213435 3322889 := bstep (se 2 (by rfl) ⟨1246083, by rfl⟩ : syracuseStep 3322889 = 2492167) B2492167
theorem B2215259 : Blo 2213435 2215259 := bstep (se 1 (by rfl) ⟨1661444, by rfl⟩ : syracuseStep 2215259 = 3322889) B3322889
theorem B11214773 : Blo 2213435 11214773 := bbase (se 5 (by rfl) ⟨525692, by rfl⟩ : syracuseStep 11214773 = 1051385) (by norm_num)
theorem B7476515 : Blo 2213435 7476515 := bstep (se 1 (by rfl) ⟨5607386, by rfl⟩ : syracuseStep 7476515 = 11214773) B11214773
theorem B4984343 : Blo 2213435 4984343 := bstep (se 1 (by rfl) ⟨3738257, by rfl⟩ : syracuseStep 4984343 = 7476515) B7476515
theorem B3322895 : Blo 2213435 3322895 := bstep (se 1 (by rfl) ⟨2492171, by rfl⟩ : syracuseStep 3322895 = 4984343) B4984343
theorem B2215263 : Blo 2213435 2215263 := bstep (se 1 (by rfl) ⟨1661447, by rfl⟩ : syracuseStep 2215263 = 3322895) B3322895
theorem B3322901 : Blo 2213435 3322901 := bbase (se 6 (by rfl) ⟨77880, by rfl⟩ : syracuseStep 3322901 = 155761) (by norm_num)
theorem B2215267 : Blo 2213435 2215267 := bstep (se 1 (by rfl) ⟨1661450, by rfl⟩ : syracuseStep 2215267 = 3322901) B3322901
theorem B5987989 : Blo 2213435 5987989 := bbase (se 6 (by rfl) ⟨140343, by rfl⟩ : syracuseStep 5987989 = 280687) (by norm_num)
theorem B31935941 : Blo 2213435 31935941 := bstep (se 4 (by rfl) ⟨2993994, by rfl⟩ : syracuseStep 31935941 = 5987989) B5987989
theorem B21290627 : Blo 2213435 21290627 := bstep (se 1 (by rfl) ⟨15967970, by rfl⟩ : syracuseStep 21290627 = 31935941) B31935941
theorem B14193751 : Blo 2213435 14193751 := bstep (se 1 (by rfl) ⟨10645313, by rfl⟩ : syracuseStep 14193751 = 21290627) B21290627
theorem B18925001 : Blo 2213435 18925001 := bstep (se 2 (by rfl) ⟨7096875, by rfl⟩ : syracuseStep 18925001 = 14193751) B14193751
theorem B12616667 : Blo 2213435 12616667 := bstep (se 1 (by rfl) ⟨9462500, by rfl⟩ : syracuseStep 12616667 = 18925001) B18925001
theorem B8411111 : Blo 2213435 8411111 := bstep (se 1 (by rfl) ⟨6308333, by rfl⟩ : syracuseStep 8411111 = 12616667) B12616667
theorem B5607407 : Blo 2213435 5607407 := bstep (se 1 (by rfl) ⟨4205555, by rfl⟩ : syracuseStep 5607407 = 8411111) B8411111
theorem B3738271 : Blo 2213435 3738271 := bstep (se 1 (by rfl) ⟨2803703, by rfl⟩ : syracuseStep 3738271 = 5607407) B5607407
theorem B4984361 : Blo 2213435 4984361 := bstep (se 2 (by rfl) ⟨1869135, by rfl⟩ : syracuseStep 4984361 = 3738271) B3738271
theorem B3322907 : Blo 2213435 3322907 := bstep (se 1 (by rfl) ⟨2492180, by rfl⟩ : syracuseStep 3322907 = 4984361) B4984361
theorem B2215271 : Blo 2213435 2215271 := bstep (se 1 (by rfl) ⟨1661453, by rfl⟩ : syracuseStep 2215271 = 3322907) B3322907
theorem B2492185 : Blo 2213435 2492185 := bbase (se 2 (by rfl) ⟨934569, by rfl⟩ : syracuseStep 2492185 = 1869139) (by norm_num)
theorem B3322913 : Blo 2213435 3322913 := bstep (se 2 (by rfl) ⟨1246092, by rfl⟩ : syracuseStep 3322913 = 2492185) B2492185
theorem B2215275 : Blo 2213435 2215275 := bstep (se 1 (by rfl) ⟨1661456, by rfl⟩ : syracuseStep 2215275 = 3322913) B3322913
theorem B8411141 : Blo 2213435 8411141 := bbase (se 4 (by rfl) ⟨788544, by rfl⟩ : syracuseStep 8411141 = 1577089) (by norm_num)
theorem B5607427 : Blo 2213435 5607427 := bstep (se 1 (by rfl) ⟨4205570, by rfl⟩ : syracuseStep 5607427 = 8411141) B8411141
theorem B7476569 : Blo 2213435 7476569 := bstep (se 2 (by rfl) ⟨2803713, by rfl⟩ : syracuseStep 7476569 = 5607427) B5607427
theorem B4984379 : Blo 2213435 4984379 := bstep (se 1 (by rfl) ⟨3738284, by rfl⟩ : syracuseStep 4984379 = 7476569) B7476569
theorem B3322919 : Blo 2213435 3322919 := bstep (se 1 (by rfl) ⟨2492189, by rfl⟩ : syracuseStep 3322919 = 4984379) B4984379
theorem B2215279 : Blo 2213435 2215279 := bstep (se 1 (by rfl) ⟨1661459, by rfl⟩ : syracuseStep 2215279 = 3322919) B3322919
theorem B3322925 : Blo 2213435 3322925 := bbase (se 3 (by rfl) ⟨623048, by rfl⟩ : syracuseStep 3322925 = 1246097) (by norm_num)
theorem B2215283 : Blo 2213435 2215283 := bstep (se 1 (by rfl) ⟨1661462, by rfl⟩ : syracuseStep 2215283 = 3322925) B3322925
theorem B4984397 : Blo 2213435 4984397 := bbase (se 3 (by rfl) ⟨934574, by rfl⟩ : syracuseStep 4984397 = 1869149) (by norm_num)
theorem B3322931 : Blo 2213435 3322931 := bstep (se 1 (by rfl) ⟨2492198, by rfl⟩ : syracuseStep 3322931 = 4984397) B4984397
theorem B2215287 : Blo 2213435 2215287 := bstep (se 1 (by rfl) ⟨1661465, by rfl⟩ : syracuseStep 2215287 = 3322931) B3322931
theorem B2803729 : Blo 2213435 2803729 := bbase (se 2 (by rfl) ⟨1051398, by rfl⟩ : syracuseStep 2803729 = 2102797) (by norm_num)
theorem B3738305 : Blo 2213435 3738305 := bstep (se 2 (by rfl) ⟨1401864, by rfl⟩ : syracuseStep 3738305 = 2803729) B2803729
theorem B2492203 : Blo 2213435 2492203 := bstep (se 1 (by rfl) ⟨1869152, by rfl⟩ : syracuseStep 2492203 = 3738305) B3738305
theorem B3322937 : Blo 2213435 3322937 := bstep (se 2 (by rfl) ⟨1246101, by rfl⟩ : syracuseStep 3322937 = 2492203) B2492203
theorem B2215291 : Blo 2213435 2215291 := bstep (se 1 (by rfl) ⟨1661468, by rfl⟩ : syracuseStep 2215291 = 3322937) B3322937
theorem B4731301 : Blo 2213435 4731301 := bbase (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) (by norm_num)
theorem B25233605 : Blo 2213435 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B16822403 : Blo 2213435 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B11214935 : Blo 2213435 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B7476623 : Blo 2213435 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B4984415 : Blo 2213435 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B3322943 : Blo 2213435 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B2215295 : Blo 2213435 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B3322949 : Blo 2213435 3322949 := bbase (se 4 (by rfl) ⟨311526, by rfl⟩ : syracuseStep 3322949 = 623053) (by norm_num)
theorem B2215299 : Blo 2213435 2215299 := bstep (se 1 (by rfl) ⟨1661474, by rfl⟩ : syracuseStep 2215299 = 3322949) B3322949
theorem B3738325 : Blo 2213435 3738325 := bbase (se 7 (by rfl) ⟨43808, by rfl⟩ : syracuseStep 3738325 = 87617) (by norm_num)
theorem B4984433 : Blo 2213435 4984433 := bstep (se 2 (by rfl) ⟨1869162, by rfl⟩ : syracuseStep 4984433 = 3738325) B3738325
theorem B3322955 : Blo 2213435 3322955 := bstep (se 1 (by rfl) ⟨2492216, by rfl⟩ : syracuseStep 3322955 = 4984433) B4984433
theorem B2215303 : Blo 2213435 2215303 := bstep (se 1 (by rfl) ⟨1661477, by rfl⟩ : syracuseStep 2215303 = 3322955) B3322955
theorem B2492221 : Blo 2213435 2492221 := bbase (se 3 (by rfl) ⟨467291, by rfl⟩ : syracuseStep 2492221 = 934583) (by norm_num)
theorem B3322961 : Blo 2213435 3322961 := bstep (se 2 (by rfl) ⟨1246110, by rfl⟩ : syracuseStep 3322961 = 2492221) B2492221
theorem B2215307 : Blo 2213435 2215307 := bstep (se 1 (by rfl) ⟨1661480, by rfl⟩ : syracuseStep 2215307 = 3322961) B3322961
theorem B7476677 : Blo 2213435 7476677 := bbase (se 4 (by rfl) ⟨700938, by rfl⟩ : syracuseStep 7476677 = 1401877) (by norm_num)
theorem B4984451 : Blo 2213435 4984451 := bstep (se 1 (by rfl) ⟨3738338, by rfl⟩ : syracuseStep 4984451 = 7476677) B7476677
theorem B3322967 : Blo 2213435 3322967 := bstep (se 1 (by rfl) ⟨2492225, by rfl⟩ : syracuseStep 3322967 = 4984451) B4984451
theorem B2215311 : Blo 2213435 2215311 := bstep (se 1 (by rfl) ⟨1661483, by rfl⟩ : syracuseStep 2215311 = 3322967) B3322967
theorem B3322973 : Blo 2213435 3322973 := bbase (se 3 (by rfl) ⟨623057, by rfl⟩ : syracuseStep 3322973 = 1246115) (by norm_num)
theorem B2215315 : Blo 2213435 2215315 := bstep (se 1 (by rfl) ⟨1661486, by rfl⟩ : syracuseStep 2215315 = 3322973) B3322973
theorem B4984469 : Blo 2213435 4984469 := bbase (se 6 (by rfl) ⟨116823, by rfl⟩ : syracuseStep 4984469 = 233647) (by norm_num)
theorem B3322979 : Blo 2213435 3322979 := bstep (se 1 (by rfl) ⟨2492234, by rfl⟩ : syracuseStep 3322979 = 4984469) B4984469
theorem B2215319 : Blo 2213435 2215319 := bstep (se 1 (by rfl) ⟨1661489, by rfl⟩ : syracuseStep 2215319 = 3322979) B3322979
theorem B2365681 : Blo 2213435 2365681 := bbase (se 2 (by rfl) ⟨887130, by rfl⟩ : syracuseStep 2365681 = 1774261) (by norm_num)
theorem B3154241 : Blo 2213435 3154241 := bstep (se 2 (by rfl) ⟨1182840, by rfl⟩ : syracuseStep 3154241 = 2365681) B2365681
theorem B8411309 : Blo 2213435 8411309 := bstep (se 3 (by rfl) ⟨1577120, by rfl⟩ : syracuseStep 8411309 = 3154241) B3154241
theorem B5607539 : Blo 2213435 5607539 := bstep (se 1 (by rfl) ⟨4205654, by rfl⟩ : syracuseStep 5607539 = 8411309) B8411309
theorem B3738359 : Blo 2213435 3738359 := bstep (se 1 (by rfl) ⟨2803769, by rfl⟩ : syracuseStep 3738359 = 5607539) B5607539
theorem B2492239 : Blo 2213435 2492239 := bstep (se 1 (by rfl) ⟨1869179, by rfl⟩ : syracuseStep 2492239 = 3738359) B3738359
theorem B3322985 : Blo 2213435 3322985 := bstep (se 2 (by rfl) ⟨1246119, by rfl⟩ : syracuseStep 3322985 = 2492239) B2492239
theorem B2215323 : Blo 2213435 2215323 := bstep (se 1 (by rfl) ⟨1661492, by rfl⟩ : syracuseStep 2215323 = 3322985) B3322985
theorem B6394565 : Blo 2213435 6394565 := bbase (se 4 (by rfl) ⟨599490, by rfl⟩ : syracuseStep 6394565 = 1198981) (by norm_num)
theorem B4263043 : Blo 2213435 4263043 := bstep (se 1 (by rfl) ⟨3197282, by rfl⟩ : syracuseStep 4263043 = 6394565) B6394565
theorem B5684057 : Blo 2213435 5684057 := bstep (se 2 (by rfl) ⟨2131521, by rfl⟩ : syracuseStep 5684057 = 4263043) B4263043
theorem B3789371 : Blo 2213435 3789371 := bstep (se 1 (by rfl) ⟨2842028, by rfl⟩ : syracuseStep 3789371 = 5684057) B5684057
theorem B2526247 : Blo 2213435 2526247 := bstep (se 1 (by rfl) ⟨1894685, by rfl⟩ : syracuseStep 2526247 = 3789371) B3789371
theorem B13473317 : Blo 2213435 13473317 := bstep (se 4 (by rfl) ⟨1263123, by rfl⟩ : syracuseStep 13473317 = 2526247) B2526247
theorem B8982211 : Blo 2213435 8982211 := bstep (se 1 (by rfl) ⟨6736658, by rfl⟩ : syracuseStep 8982211 = 13473317) B13473317
theorem B11976281 : Blo 2213435 11976281 := bstep (se 2 (by rfl) ⟨4491105, by rfl⟩ : syracuseStep 11976281 = 8982211) B8982211
theorem B7984187 : Blo 2213435 7984187 := bstep (se 1 (by rfl) ⟨5988140, by rfl⟩ : syracuseStep 7984187 = 11976281) B11976281
theorem B5322791 : Blo 2213435 5322791 := bstep (se 1 (by rfl) ⟨3992093, by rfl⟩ : syracuseStep 5322791 = 7984187) B7984187
theorem B14194109 : Blo 2213435 14194109 := bstep (se 3 (by rfl) ⟨2661395, by rfl⟩ : syracuseStep 14194109 = 5322791) B5322791
theorem B9462739 : Blo 2213435 9462739 := bstep (se 1 (by rfl) ⟨7097054, by rfl⟩ : syracuseStep 9462739 = 14194109) B14194109
theorem B12616985 : Blo 2213435 12616985 := bstep (se 2 (by rfl) ⟨4731369, by rfl⟩ : syracuseStep 12616985 = 9462739) B9462739
theorem B8411323 : Blo 2213435 8411323 := bstep (se 1 (by rfl) ⟨6308492, by rfl⟩ : syracuseStep 8411323 = 12616985) B12616985
theorem B11215097 : Blo 2213435 11215097 := bstep (se 2 (by rfl) ⟨4205661, by rfl⟩ : syracuseStep 11215097 = 8411323) B8411323
theorem B7476731 : Blo 2213435 7476731 := bstep (se 1 (by rfl) ⟨5607548, by rfl⟩ : syracuseStep 7476731 = 11215097) B11215097
theorem B4984487 : Blo 2213435 4984487 := bstep (se 1 (by rfl) ⟨3738365, by rfl⟩ : syracuseStep 4984487 = 7476731) B7476731
theorem B3322991 : Blo 2213435 3322991 := bstep (se 1 (by rfl) ⟨2492243, by rfl⟩ : syracuseStep 3322991 = 4984487) B4984487
theorem B2215327 : Blo 2213435 2215327 := bstep (se 1 (by rfl) ⟨1661495, by rfl⟩ : syracuseStep 2215327 = 3322991) B3322991
theorem B3322997 : Blo 2213435 3322997 := bbase (se 5 (by rfl) ⟨155765, by rfl⟩ : syracuseStep 3322997 = 311531) (by norm_num)
theorem B2215331 : Blo 2213435 2215331 := bstep (se 1 (by rfl) ⟨1661498, by rfl⟩ : syracuseStep 2215331 = 3322997) B3322997
theorem B4205677 : Blo 2213435 4205677 := bbase (se 3 (by rfl) ⟨788564, by rfl⟩ : syracuseStep 4205677 = 1577129) (by norm_num)
theorem B5607569 : Blo 2213435 5607569 := bstep (se 2 (by rfl) ⟨2102838, by rfl⟩ : syracuseStep 5607569 = 4205677) B4205677
theorem B3738379 : Blo 2213435 3738379 := bstep (se 1 (by rfl) ⟨2803784, by rfl⟩ : syracuseStep 3738379 = 5607569) B5607569
theorem B4984505 : Blo 2213435 4984505 := bstep (se 2 (by rfl) ⟨1869189, by rfl⟩ : syracuseStep 4984505 = 3738379) B3738379
theorem B3323003 : Blo 2213435 3323003 := bstep (se 1 (by rfl) ⟨2492252, by rfl⟩ : syracuseStep 3323003 = 4984505) B4984505
theorem B2215335 : Blo 2213435 2215335 := bstep (se 1 (by rfl) ⟨1661501, by rfl⟩ : syracuseStep 2215335 = 3323003) B3323003
theorem B2492257 : Blo 2213435 2492257 := bbase (se 2 (by rfl) ⟨934596, by rfl⟩ : syracuseStep 2492257 = 1869193) (by norm_num)
theorem B3323009 : Blo 2213435 3323009 := bstep (se 2 (by rfl) ⟨1246128, by rfl⟩ : syracuseStep 3323009 = 2492257) B2492257
theorem B2215339 : Blo 2213435 2215339 := bstep (se 1 (by rfl) ⟨1661504, by rfl⟩ : syracuseStep 2215339 = 3323009) B3323009
theorem B5607589 : Blo 2213435 5607589 := bbase (se 4 (by rfl) ⟨525711, by rfl⟩ : syracuseStep 5607589 = 1051423) (by norm_num)
theorem B7476785 : Blo 2213435 7476785 := bstep (se 2 (by rfl) ⟨2803794, by rfl⟩ : syracuseStep 7476785 = 5607589) B5607589
theorem B4984523 : Blo 2213435 4984523 := bstep (se 1 (by rfl) ⟨3738392, by rfl⟩ : syracuseStep 4984523 = 7476785) B7476785
theorem B3323015 : Blo 2213435 3323015 := bstep (se 1 (by rfl) ⟨2492261, by rfl⟩ : syracuseStep 3323015 = 4984523) B4984523
theorem B2215343 : Blo 2213435 2215343 := bstep (se 1 (by rfl) ⟨1661507, by rfl⟩ : syracuseStep 2215343 = 3323015) B3323015
theorem B3323021 : Blo 2213435 3323021 := bbase (se 3 (by rfl) ⟨623066, by rfl⟩ : syracuseStep 3323021 = 1246133) (by norm_num)
theorem B2215347 : Blo 2213435 2215347 := bstep (se 1 (by rfl) ⟨1661510, by rfl⟩ : syracuseStep 2215347 = 3323021) B3323021
theorem B4984541 : Blo 2213435 4984541 := bbase (se 3 (by rfl) ⟨934601, by rfl⟩ : syracuseStep 4984541 = 1869203) (by norm_num)
theorem B3323027 : Blo 2213435 3323027 := bstep (se 1 (by rfl) ⟨2492270, by rfl⟩ : syracuseStep 3323027 = 4984541) B4984541
theorem B2215351 : Blo 2213435 2215351 := bstep (se 1 (by rfl) ⟨1661513, by rfl⟩ : syracuseStep 2215351 = 3323027) B3323027
theorem B3738413 : Blo 2213435 3738413 := bbase (se 3 (by rfl) ⟨700952, by rfl⟩ : syracuseStep 3738413 = 1401905) (by norm_num)
theorem B2492275 : Blo 2213435 2492275 := bstep (se 1 (by rfl) ⟨1869206, by rfl⟩ : syracuseStep 2492275 = 3738413) B3738413
theorem B3323033 : Blo 2213435 3323033 := bstep (se 2 (by rfl) ⟨1246137, by rfl⟩ : syracuseStep 3323033 = 2492275) B2492275
theorem B2215355 : Blo 2213435 2215355 := bstep (se 1 (by rfl) ⟨1661516, by rfl⟩ : syracuseStep 2215355 = 3323033) B3323033
theorem B2430713 : Blo 2213435 2430713 := bbase (se 2 (by rfl) ⟨911517, by rfl⟩ : syracuseStep 2430713 = 1823035) (by norm_num)
theorem B6481901 : Blo 2213435 6481901 := bstep (se 3 (by rfl) ⟨1215356, by rfl⟩ : syracuseStep 6481901 = 2430713) B2430713
theorem B17285069 : Blo 2213435 17285069 := bstep (se 3 (by rfl) ⟨3240950, by rfl⟩ : syracuseStep 17285069 = 6481901) B6481901
theorem B11523379 : Blo 2213435 11523379 := bstep (se 1 (by rfl) ⟨8642534, by rfl⟩ : syracuseStep 11523379 = 17285069) B17285069
theorem B15364505 : Blo 2213435 15364505 := bstep (se 2 (by rfl) ⟨5761689, by rfl⟩ : syracuseStep 15364505 = 11523379) B11523379
theorem B10243003 : Blo 2213435 10243003 := bstep (se 1 (by rfl) ⟨7682252, by rfl⟩ : syracuseStep 10243003 = 15364505) B15364505
theorem B13657337 : Blo 2213435 13657337 := bstep (se 2 (by rfl) ⟨5121501, by rfl⟩ : syracuseStep 13657337 = 10243003) B10243003
theorem B9104891 : Blo 2213435 9104891 := bstep (se 1 (by rfl) ⟨6828668, by rfl⟩ : syracuseStep 9104891 = 13657337) B13657337
theorem B24279709 : Blo 2213435 24279709 := bstep (se 3 (by rfl) ⟨4552445, by rfl⟩ : syracuseStep 24279709 = 9104891) B9104891
theorem B32372945 : Blo 2213435 32372945 := bstep (se 2 (by rfl) ⟨12139854, by rfl⟩ : syracuseStep 32372945 = 24279709) B24279709
theorem B21581963 : Blo 2213435 21581963 := bstep (se 1 (by rfl) ⟨16186472, by rfl⟩ : syracuseStep 21581963 = 32372945) B32372945
theorem B14387975 : Blo 2213435 14387975 := bstep (se 1 (by rfl) ⟨10790981, by rfl⟩ : syracuseStep 14387975 = 21581963) B21581963
theorem B9591983 : Blo 2213435 9591983 := bstep (se 1 (by rfl) ⟨7193987, by rfl⟩ : syracuseStep 9591983 = 14387975) B14387975
theorem B6394655 : Blo 2213435 6394655 := bstep (se 1 (by rfl) ⟨4795991, by rfl⟩ : syracuseStep 6394655 = 9591983) B9591983
theorem B4263103 : Blo 2213435 4263103 := bstep (se 1 (by rfl) ⟨3197327, by rfl⟩ : syracuseStep 4263103 = 6394655) B6394655
theorem B5684137 : Blo 2213435 5684137 := bstep (se 2 (by rfl) ⟨2131551, by rfl⟩ : syracuseStep 5684137 = 4263103) B4263103
theorem B30315397 : Blo 2213435 30315397 := bstep (se 4 (by rfl) ⟨2842068, by rfl⟩ : syracuseStep 30315397 = 5684137) B5684137
theorem B40420529 : Blo 2213435 40420529 := bstep (se 2 (by rfl) ⟨15157698, by rfl⟩ : syracuseStep 40420529 = 30315397) B30315397
theorem B26947019 : Blo 2213435 26947019 := bstep (se 1 (by rfl) ⟨20210264, by rfl⟩ : syracuseStep 26947019 = 40420529) B40420529
theorem B17964679 : Blo 2213435 17964679 := bstep (se 1 (by rfl) ⟨13473509, by rfl⟩ : syracuseStep 17964679 = 26947019) B26947019
theorem B23952905 : Blo 2213435 23952905 := bstep (se 2 (by rfl) ⟨8982339, by rfl⟩ : syracuseStep 23952905 = 17964679) B17964679
theorem B15968603 : Blo 2213435 15968603 := bstep (se 1 (by rfl) ⟨11976452, by rfl⟩ : syracuseStep 15968603 = 23952905) B23952905
theorem B42582941 : Blo 2213435 42582941 := bstep (se 3 (by rfl) ⟨7984301, by rfl⟩ : syracuseStep 42582941 = 15968603) B15968603
theorem B28388627 : Blo 2213435 28388627 := bstep (se 1 (by rfl) ⟨21291470, by rfl⟩ : syracuseStep 28388627 = 42582941) B42582941
theorem B18925751 : Blo 2213435 18925751 := bstep (se 1 (by rfl) ⟨14194313, by rfl⟩ : syracuseStep 18925751 = 28388627) B28388627
theorem B12617167 : Blo 2213435 12617167 := bstep (se 1 (by rfl) ⟨9462875, by rfl⟩ : syracuseStep 12617167 = 18925751) B18925751
theorem B16822889 : Blo 2213435 16822889 := bstep (se 2 (by rfl) ⟨6308583, by rfl⟩ : syracuseStep 16822889 = 12617167) B12617167
theorem B11215259 : Blo 2213435 11215259 := bstep (se 1 (by rfl) ⟨8411444, by rfl⟩ : syracuseStep 11215259 = 16822889) B16822889
theorem B7476839 : Blo 2213435 7476839 := bstep (se 1 (by rfl) ⟨5607629, by rfl⟩ : syracuseStep 7476839 = 11215259) B11215259
theorem B4984559 : Blo 2213435 4984559 := bstep (se 1 (by rfl) ⟨3738419, by rfl⟩ : syracuseStep 4984559 = 7476839) B7476839
theorem B3323039 : Blo 2213435 3323039 := bstep (se 1 (by rfl) ⟨2492279, by rfl⟩ : syracuseStep 3323039 = 4984559) B4984559
theorem B2215359 : Blo 2213435 2215359 := bstep (se 1 (by rfl) ⟨1661519, by rfl⟩ : syracuseStep 2215359 = 3323039) B3323039
theorem B3323045 : Blo 2213435 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B2215363 : Blo 2213435 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B2803825 : Blo 2213435 2803825 := bbase (se 2 (by rfl) ⟨1051434, by rfl⟩ : syracuseStep 2803825 = 2102869) (by norm_num)
theorem B3738433 : Blo 2213435 3738433 := bstep (se 2 (by rfl) ⟨1401912, by rfl⟩ : syracuseStep 3738433 = 2803825) B2803825
theorem B4984577 : Blo 2213435 4984577 := bstep (se 2 (by rfl) ⟨1869216, by rfl⟩ : syracuseStep 4984577 = 3738433) B3738433
theorem B3323051 : Blo 2213435 3323051 := bstep (se 1 (by rfl) ⟨2492288, by rfl⟩ : syracuseStep 3323051 = 4984577) B4984577
theorem B2215367 : Blo 2213435 2215367 := bstep (se 1 (by rfl) ⟨1661525, by rfl⟩ : syracuseStep 2215367 = 3323051) B3323051
theorem B2492293 : Blo 2213435 2492293 := bbase (se 4 (by rfl) ⟨233652, by rfl⟩ : syracuseStep 2492293 = 467305) (by norm_num)
theorem B3323057 : Blo 2213435 3323057 := bstep (se 2 (by rfl) ⟨1246146, by rfl⟩ : syracuseStep 3323057 = 2492293) B2492293
theorem B2215371 : Blo 2213435 2215371 := bstep (se 1 (by rfl) ⟨1661528, by rfl⟩ : syracuseStep 2215371 = 3323057) B3323057
theorem B3548605 : Blo 2213435 3548605 := bbase (se 3 (by rfl) ⟨665363, by rfl⟩ : syracuseStep 3548605 = 1330727) (by norm_num)
theorem B4731473 : Blo 2213435 4731473 := bstep (se 2 (by rfl) ⟨1774302, by rfl⟩ : syracuseStep 4731473 = 3548605) B3548605
theorem B3154315 : Blo 2213435 3154315 := bstep (se 1 (by rfl) ⟨2365736, by rfl⟩ : syracuseStep 3154315 = 4731473) B4731473
theorem B4205753 : Blo 2213435 4205753 := bstep (se 2 (by rfl) ⟨1577157, by rfl⟩ : syracuseStep 4205753 = 3154315) B3154315
theorem B2803835 : Blo 2213435 2803835 := bstep (se 1 (by rfl) ⟨2102876, by rfl⟩ : syracuseStep 2803835 = 4205753) B4205753
theorem B7476893 : Blo 2213435 7476893 := bstep (se 3 (by rfl) ⟨1401917, by rfl⟩ : syracuseStep 7476893 = 2803835) B2803835
theorem B4984595 : Blo 2213435 4984595 := bstep (se 1 (by rfl) ⟨3738446, by rfl⟩ : syracuseStep 4984595 = 7476893) B7476893
theorem B3323063 : Blo 2213435 3323063 := bstep (se 1 (by rfl) ⟨2492297, by rfl⟩ : syracuseStep 3323063 = 4984595) B4984595
theorem B2215375 : Blo 2213435 2215375 := bstep (se 1 (by rfl) ⟨1661531, by rfl⟩ : syracuseStep 2215375 = 3323063) B3323063
theorem B3323069 : Blo 2213435 3323069 := bbase (se 3 (by rfl) ⟨623075, by rfl⟩ : syracuseStep 3323069 = 1246151) (by norm_num)
theorem B2215379 : Blo 2213435 2215379 := bstep (se 1 (by rfl) ⟨1661534, by rfl⟩ : syracuseStep 2215379 = 3323069) B3323069
theorem B4984613 : Blo 2213435 4984613 := bbase (se 4 (by rfl) ⟨467307, by rfl⟩ : syracuseStep 4984613 = 934615) (by norm_num)
theorem B3323075 : Blo 2213435 3323075 := bstep (se 1 (by rfl) ⟨2492306, by rfl⟩ : syracuseStep 3323075 = 4984613) B4984613
theorem B2215383 : Blo 2213435 2215383 := bstep (se 1 (by rfl) ⟨1661537, by rfl⟩ : syracuseStep 2215383 = 3323075) B3323075
theorem B5607701 : Blo 2213435 5607701 := bbase (se 6 (by rfl) ⟨131430, by rfl⟩ : syracuseStep 5607701 = 262861) (by norm_num)
theorem B3738467 : Blo 2213435 3738467 := bstep (se 1 (by rfl) ⟨2803850, by rfl⟩ : syracuseStep 3738467 = 5607701) B5607701
theorem B2492311 : Blo 2213435 2492311 := bstep (se 1 (by rfl) ⟨1869233, by rfl⟩ : syracuseStep 2492311 = 3738467) B3738467
theorem B3323081 : Blo 2213435 3323081 := bstep (se 2 (by rfl) ⟨1246155, by rfl⟩ : syracuseStep 3323081 = 2492311) B2492311
theorem B2215387 : Blo 2213435 2215387 := bstep (se 1 (by rfl) ⟨1661540, by rfl⟩ : syracuseStep 2215387 = 3323081) B3323081
theorem B9463013 : Blo 2213435 9463013 := bbase (se 4 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 9463013 = 1774315) (by norm_num)
theorem B6308675 : Blo 2213435 6308675 := bstep (se 1 (by rfl) ⟨4731506, by rfl⟩ : syracuseStep 6308675 = 9463013) B9463013
theorem B4205783 : Blo 2213435 4205783 := bstep (se 1 (by rfl) ⟨3154337, by rfl⟩ : syracuseStep 4205783 = 6308675) B6308675
theorem B11215421 : Blo 2213435 11215421 := bstep (se 3 (by rfl) ⟨2102891, by rfl⟩ : syracuseStep 11215421 = 4205783) B4205783
theorem B7476947 : Blo 2213435 7476947 := bstep (se 1 (by rfl) ⟨5607710, by rfl⟩ : syracuseStep 7476947 = 11215421) B11215421
theorem B4984631 : Blo 2213435 4984631 := bstep (se 1 (by rfl) ⟨3738473, by rfl⟩ : syracuseStep 4984631 = 7476947) B7476947
theorem B3323087 : Blo 2213435 3323087 := bstep (se 1 (by rfl) ⟨2492315, by rfl⟩ : syracuseStep 3323087 = 4984631) B4984631
theorem B2215391 : Blo 2213435 2215391 := bstep (se 1 (by rfl) ⟨1661543, by rfl⟩ : syracuseStep 2215391 = 3323087) B3323087
theorem B3323093 : Blo 2213435 3323093 := bbase (se 7 (by rfl) ⟨38942, by rfl⟩ : syracuseStep 3323093 = 77885) (by norm_num)
theorem B2215395 : Blo 2213435 2215395 := bstep (se 1 (by rfl) ⟨1661546, by rfl⟩ : syracuseStep 2215395 = 3323093) B3323093
theorem B3154349 : Blo 2213435 3154349 := bbase (se 3 (by rfl) ⟨591440, by rfl⟩ : syracuseStep 3154349 = 1182881) (by norm_num)
theorem B8411597 : Blo 2213435 8411597 := bstep (se 3 (by rfl) ⟨1577174, by rfl⟩ : syracuseStep 8411597 = 3154349) B3154349
theorem B5607731 : Blo 2213435 5607731 := bstep (se 1 (by rfl) ⟨4205798, by rfl⟩ : syracuseStep 5607731 = 8411597) B8411597
theorem B3738487 : Blo 2213435 3738487 := bstep (se 1 (by rfl) ⟨2803865, by rfl⟩ : syracuseStep 3738487 = 5607731) B5607731
theorem B4984649 : Blo 2213435 4984649 := bstep (se 2 (by rfl) ⟨1869243, by rfl⟩ : syracuseStep 4984649 = 3738487) B3738487
theorem B3323099 : Blo 2213435 3323099 := bstep (se 1 (by rfl) ⟨2492324, by rfl⟩ : syracuseStep 3323099 = 4984649) B4984649
theorem B2215399 : Blo 2213435 2215399 := bstep (se 1 (by rfl) ⟨1661549, by rfl⟩ : syracuseStep 2215399 = 3323099) B3323099
theorem B2492329 : Blo 2213435 2492329 := bbase (se 2 (by rfl) ⟨934623, by rfl⟩ : syracuseStep 2492329 = 1869247) (by norm_num)
theorem B3323105 : Blo 2213435 3323105 := bstep (se 2 (by rfl) ⟨1246164, by rfl⟩ : syracuseStep 3323105 = 2492329) B2492329
theorem B2215403 : Blo 2213435 2215403 := bstep (se 1 (by rfl) ⟨1661552, by rfl⟩ : syracuseStep 2215403 = 3323105) B3323105
theorem B5684261 : Blo 2213435 5684261 := bbase (se 4 (by rfl) ⟨532899, by rfl⟩ : syracuseStep 5684261 = 1065799) (by norm_num)
theorem B15158029 : Blo 2213435 15158029 := bstep (se 3 (by rfl) ⟨2842130, by rfl⟩ : syracuseStep 15158029 = 5684261) B5684261
theorem B20210705 : Blo 2213435 20210705 := bstep (se 2 (by rfl) ⟨7579014, by rfl⟩ : syracuseStep 20210705 = 15158029) B15158029
theorem B13473803 : Blo 2213435 13473803 := bstep (se 1 (by rfl) ⟨10105352, by rfl⟩ : syracuseStep 13473803 = 20210705) B20210705
theorem B35930141 : Blo 2213435 35930141 := bstep (se 3 (by rfl) ⟨6736901, by rfl⟩ : syracuseStep 35930141 = 13473803) B13473803
theorem B23953427 : Blo 2213435 23953427 := bstep (se 1 (by rfl) ⟨17965070, by rfl⟩ : syracuseStep 23953427 = 35930141) B35930141
theorem B15968951 : Blo 2213435 15968951 := bstep (se 1 (by rfl) ⟨11976713, by rfl⟩ : syracuseStep 15968951 = 23953427) B23953427
theorem B10645967 : Blo 2213435 10645967 := bstep (se 1 (by rfl) ⟨7984475, by rfl⟩ : syracuseStep 10645967 = 15968951) B15968951
theorem B7097311 : Blo 2213435 7097311 := bstep (se 1 (by rfl) ⟨5322983, by rfl⟩ : syracuseStep 7097311 = 10645967) B10645967
theorem B9463081 : Blo 2213435 9463081 := bstep (se 2 (by rfl) ⟨3548655, by rfl⟩ : syracuseStep 9463081 = 7097311) B7097311
theorem B12617441 : Blo 2213435 12617441 := bstep (se 2 (by rfl) ⟨4731540, by rfl⟩ : syracuseStep 12617441 = 9463081) B9463081
theorem B8411627 : Blo 2213435 8411627 := bstep (se 1 (by rfl) ⟨6308720, by rfl⟩ : syracuseStep 8411627 = 12617441) B12617441
theorem B5607751 : Blo 2213435 5607751 := bstep (se 1 (by rfl) ⟨4205813, by rfl⟩ : syracuseStep 5607751 = 8411627) B8411627
theorem B7477001 : Blo 2213435 7477001 := bstep (se 2 (by rfl) ⟨2803875, by rfl⟩ : syracuseStep 7477001 = 5607751) B5607751
theorem B4984667 : Blo 2213435 4984667 := bstep (se 1 (by rfl) ⟨3738500, by rfl⟩ : syracuseStep 4984667 = 7477001) B7477001
theorem B3323111 : Blo 2213435 3323111 := bstep (se 1 (by rfl) ⟨2492333, by rfl⟩ : syracuseStep 3323111 = 4984667) B4984667
theorem B2215407 : Blo 2213435 2215407 := bstep (se 1 (by rfl) ⟨1661555, by rfl⟩ : syracuseStep 2215407 = 3323111) B3323111
theorem B3323117 : Blo 2213435 3323117 := bbase (se 3 (by rfl) ⟨623084, by rfl⟩ : syracuseStep 3323117 = 1246169) (by norm_num)
theorem B2215411 : Blo 2213435 2215411 := bstep (se 1 (by rfl) ⟨1661558, by rfl⟩ : syracuseStep 2215411 = 3323117) B3323117
theorem B4984685 : Blo 2213435 4984685 := bbase (se 3 (by rfl) ⟨934628, by rfl⟩ : syracuseStep 4984685 = 1869257) (by norm_num)
theorem B3323123 : Blo 2213435 3323123 := bstep (se 1 (by rfl) ⟨2492342, by rfl⟩ : syracuseStep 3323123 = 4984685) B4984685
theorem B2215415 : Blo 2213435 2215415 := bstep (se 1 (by rfl) ⟨1661561, by rfl⟩ : syracuseStep 2215415 = 3323123) B3323123
theorem B4205837 : Blo 2213435 4205837 := bbase (se 3 (by rfl) ⟨788594, by rfl⟩ : syracuseStep 4205837 = 1577189) (by norm_num)
theorem B2803891 : Blo 2213435 2803891 := bstep (se 1 (by rfl) ⟨2102918, by rfl⟩ : syracuseStep 2803891 = 4205837) B4205837
theorem B3738521 : Blo 2213435 3738521 := bstep (se 2 (by rfl) ⟨1401945, by rfl⟩ : syracuseStep 3738521 = 2803891) B2803891
theorem B2492347 : Blo 2213435 2492347 := bstep (se 1 (by rfl) ⟨1869260, by rfl⟩ : syracuseStep 2492347 = 3738521) B3738521
theorem B3323129 : Blo 2213435 3323129 := bstep (se 2 (by rfl) ⟨1246173, by rfl⟩ : syracuseStep 3323129 = 2492347) B2492347
theorem B2215419 : Blo 2213435 2215419 := bstep (se 1 (by rfl) ⟨1661564, by rfl⟩ : syracuseStep 2215419 = 3323129) B3323129
theorem B21292085 : Blo 2213435 21292085 := bbase (se 5 (by rfl) ⟨998066, by rfl⟩ : syracuseStep 21292085 = 1996133) (by norm_num)
theorem B56778893 : Blo 2213435 56778893 := bstep (se 3 (by rfl) ⟨10646042, by rfl⟩ : syracuseStep 56778893 = 21292085) B21292085
theorem B37852595 : Blo 2213435 37852595 := bstep (se 1 (by rfl) ⟨28389446, by rfl⟩ : syracuseStep 37852595 = 56778893) B56778893
theorem B25235063 : Blo 2213435 25235063 := bstep (se 1 (by rfl) ⟨18926297, by rfl⟩ : syracuseStep 25235063 = 37852595) B37852595
theorem B16823375 : Blo 2213435 16823375 := bstep (se 1 (by rfl) ⟨12617531, by rfl⟩ : syracuseStep 16823375 = 25235063) B25235063
theorem B11215583 : Blo 2213435 11215583 := bstep (se 1 (by rfl) ⟨8411687, by rfl⟩ : syracuseStep 11215583 = 16823375) B16823375
theorem B7477055 : Blo 2213435 7477055 := bstep (se 1 (by rfl) ⟨5607791, by rfl⟩ : syracuseStep 7477055 = 11215583) B11215583
theorem B4984703 : Blo 2213435 4984703 := bstep (se 1 (by rfl) ⟨3738527, by rfl⟩ : syracuseStep 4984703 = 7477055) B7477055
theorem B3323135 : Blo 2213435 3323135 := bstep (se 1 (by rfl) ⟨2492351, by rfl⟩ : syracuseStep 3323135 = 4984703) B4984703
theorem B2215423 : Blo 2213435 2215423 := bstep (se 1 (by rfl) ⟨1661567, by rfl⟩ : syracuseStep 2215423 = 3323135) B3323135
theorem B3323141 : Blo 2213435 3323141 := bbase (se 4 (by rfl) ⟨311544, by rfl⟩ : syracuseStep 3323141 = 623089) (by norm_num)
theorem B2215427 : Blo 2213435 2215427 := bstep (se 1 (by rfl) ⟨1661570, by rfl⟩ : syracuseStep 2215427 = 3323141) B3323141
theorem B3738541 : Blo 2213435 3738541 := bbase (se 3 (by rfl) ⟨700976, by rfl⟩ : syracuseStep 3738541 = 1401953) (by norm_num)
theorem B4984721 : Blo 2213435 4984721 := bstep (se 2 (by rfl) ⟨1869270, by rfl⟩ : syracuseStep 4984721 = 3738541) B3738541
theorem B3323147 : Blo 2213435 3323147 := bstep (se 1 (by rfl) ⟨2492360, by rfl⟩ : syracuseStep 3323147 = 4984721) B4984721
theorem B2215431 : Blo 2213435 2215431 := bstep (se 1 (by rfl) ⟨1661573, by rfl⟩ : syracuseStep 2215431 = 3323147) B3323147
theorem B2492365 : Blo 2213435 2492365 := bbase (se 3 (by rfl) ⟨467318, by rfl⟩ : syracuseStep 2492365 = 934637) (by norm_num)
theorem B3323153 : Blo 2213435 3323153 := bstep (se 2 (by rfl) ⟨1246182, by rfl⟩ : syracuseStep 3323153 = 2492365) B2492365
theorem B2215435 : Blo 2213435 2215435 := bstep (se 1 (by rfl) ⟨1661576, by rfl⟩ : syracuseStep 2215435 = 3323153) B3323153
theorem C0 (j : ℕ) (h1 : 553358 ≤ j) (h2 : j ≤ 553858) : Blo 2213435 (4 * j + 3) := by
  interval_cases j
  · exact B2213435
  · exact B2213439
  · exact B2213443
  · exact B2213447
  · exact B2213451
  · exact B2213455
  · exact B2213459
  · exact B2213463
  · exact B2213467
  · exact B2213471
  · exact B2213475
  · exact B2213479
  · exact B2213483
  · exact B2213487
  · exact B2213491
  · exact B2213495
  · exact B2213499
  · exact B2213503
  · exact B2213507
  · exact B2213511
  · exact B2213515
  · exact B2213519
  · exact B2213523
  · exact B2213527
  · exact B2213531
  · exact B2213535
  · exact B2213539
  · exact B2213543
  · exact B2213547
  · exact B2213551
  · exact B2213555
  · exact B2213559
  · exact B2213563
  · exact B2213567
  · exact B2213571
  · exact B2213575
  · exact B2213579
  · exact B2213583
  · exact B2213587
  · exact B2213591
  · exact B2213595
  · exact B2213599
  · exact B2213603
  · exact B2213607
  · exact B2213611
  · exact B2213615
  · exact B2213619
  · exact B2213623
  · exact B2213627
  · exact B2213631
  · exact B2213635
  · exact B2213639
  · exact B2213643
  · exact B2213647
  · exact B2213651
  · exact B2213655
  · exact B2213659
  · exact B2213663
  · exact B2213667
  · exact B2213671
  · exact B2213675
  · exact B2213679
  · exact B2213683
  · exact B2213687
  · exact B2213691
  · exact B2213695
  · exact B2213699
  · exact B2213703
  · exact B2213707
  · exact B2213711
  · exact B2213715
  · exact B2213719
  · exact B2213723
  · exact B2213727
  · exact B2213731
  · exact B2213735
  · exact B2213739
  · exact B2213743
  · exact B2213747
  · exact B2213751
  · exact B2213755
  · exact B2213759
  · exact B2213763
  · exact B2213767
  · exact B2213771
  · exact B2213775
  · exact B2213779
  · exact B2213783
  · exact B2213787
  · exact B2213791
  · exact B2213795
  · exact B2213799
  · exact B2213803
  · exact B2213807
  · exact B2213811
  · exact B2213815
  · exact B2213819
  · exact B2213823
  · exact B2213827
  · exact B2213831
  · exact B2213835
  · exact B2213839
  · exact B2213843
  · exact B2213847
  · exact B2213851
  · exact B2213855
  · exact B2213859
  · exact B2213863
  · exact B2213867
  · exact B2213871
  · exact B2213875
  · exact B2213879
  · exact B2213883
  · exact B2213887
  · exact B2213891
  · exact B2213895
  · exact B2213899
  · exact B2213903
  · exact B2213907
  · exact B2213911
  · exact B2213915
  · exact B2213919
  · exact B2213923
  · exact B2213927
  · exact B2213931
  · exact B2213935
  · exact B2213939
  · exact B2213943
  · exact B2213947
  · exact B2213951
  · exact B2213955
  · exact B2213959
  · exact B2213963
  · exact B2213967
  · exact B2213971
  · exact B2213975
  · exact B2213979
  · exact B2213983
  · exact B2213987
  · exact B2213991
  · exact B2213995
  · exact B2213999
  · exact B2214003
  · exact B2214007
  · exact B2214011
  · exact B2214015
  · exact B2214019
  · exact B2214023
  · exact B2214027
  · exact B2214031
  · exact B2214035
  · exact B2214039
  · exact B2214043
  · exact B2214047
  · exact B2214051
  · exact B2214055
  · exact B2214059
  · exact B2214063
  · exact B2214067
  · exact B2214071
  · exact B2214075
  · exact B2214079
  · exact B2214083
  · exact B2214087
  · exact B2214091
  · exact B2214095
  · exact B2214099
  · exact B2214103
  · exact B2214107
  · exact B2214111
  · exact B2214115
  · exact B2214119
  · exact B2214123
  · exact B2214127
  · exact B2214131
  · exact B2214135
  · exact B2214139
  · exact B2214143
  · exact B2214147
  · exact B2214151
  · exact B2214155
  · exact B2214159
  · exact B2214163
  · exact B2214167
  · exact B2214171
  · exact B2214175
  · exact B2214179
  · exact B2214183
  · exact B2214187
  · exact B2214191
  · exact B2214195
  · exact B2214199
  · exact B2214203
  · exact B2214207
  · exact B2214211
  · exact B2214215
  · exact B2214219
  · exact B2214223
  · exact B2214227
  · exact B2214231
  · exact B2214235
  · exact B2214239
  · exact B2214243
  · exact B2214247
  · exact B2214251
  · exact B2214255
  · exact B2214259
  · exact B2214263
  · exact B2214267
  · exact B2214271
  · exact B2214275
  · exact B2214279
  · exact B2214283
  · exact B2214287
  · exact B2214291
  · exact B2214295
  · exact B2214299
  · exact B2214303
  · exact B2214307
  · exact B2214311
  · exact B2214315
  · exact B2214319
  · exact B2214323
  · exact B2214327
  · exact B2214331
  · exact B2214335
  · exact B2214339
  · exact B2214343
  · exact B2214347
  · exact B2214351
  · exact B2214355
  · exact B2214359
  · exact B2214363
  · exact B2214367
  · exact B2214371
  · exact B2214375
  · exact B2214379
  · exact B2214383
  · exact B2214387
  · exact B2214391
  · exact B2214395
  · exact B2214399
  · exact B2214403
  · exact B2214407
  · exact B2214411
  · exact B2214415
  · exact B2214419
  · exact B2214423
  · exact B2214427
  · exact B2214431
  · exact B2214435
  · exact B2214439
  · exact B2214443
  · exact B2214447
  · exact B2214451
  · exact B2214455
  · exact B2214459
  · exact B2214463
  · exact B2214467
  · exact B2214471
  · exact B2214475
  · exact B2214479
  · exact B2214483
  · exact B2214487
  · exact B2214491
  · exact B2214495
  · exact B2214499
  · exact B2214503
  · exact B2214507
  · exact B2214511
  · exact B2214515
  · exact B2214519
  · exact B2214523
  · exact B2214527
  · exact B2214531
  · exact B2214535
  · exact B2214539
  · exact B2214543
  · exact B2214547
  · exact B2214551
  · exact B2214555
  · exact B2214559
  · exact B2214563
  · exact B2214567
  · exact B2214571
  · exact B2214575
  · exact B2214579
  · exact B2214583
  · exact B2214587
  · exact B2214591
  · exact B2214595
  · exact B2214599
  · exact B2214603
  · exact B2214607
  · exact B2214611
  · exact B2214615
  · exact B2214619
  · exact B2214623
  · exact B2214627
  · exact B2214631
  · exact B2214635
  · exact B2214639
  · exact B2214643
  · exact B2214647
  · exact B2214651
  · exact B2214655
  · exact B2214659
  · exact B2214663
  · exact B2214667
  · exact B2214671
  · exact B2214675
  · exact B2214679
  · exact B2214683
  · exact B2214687
  · exact B2214691
  · exact B2214695
  · exact B2214699
  · exact B2214703
  · exact B2214707
  · exact B2214711
  · exact B2214715
  · exact B2214719
  · exact B2214723
  · exact B2214727
  · exact B2214731
  · exact B2214735
  · exact B2214739
  · exact B2214743
  · exact B2214747
  · exact B2214751
  · exact B2214755
  · exact B2214759
  · exact B2214763
  · exact B2214767
  · exact B2214771
  · exact B2214775
  · exact B2214779
  · exact B2214783
  · exact B2214787
  · exact B2214791
  · exact B2214795
  · exact B2214799
  · exact B2214803
  · exact B2214807
  · exact B2214811
  · exact B2214815
  · exact B2214819
  · exact B2214823
  · exact B2214827
  · exact B2214831
  · exact B2214835
  · exact B2214839
  · exact B2214843
  · exact B2214847
  · exact B2214851
  · exact B2214855
  · exact B2214859
  · exact B2214863
  · exact B2214867
  · exact B2214871
  · exact B2214875
  · exact B2214879
  · exact B2214883
  · exact B2214887
  · exact B2214891
  · exact B2214895
  · exact B2214899
  · exact B2214903
  · exact B2214907
  · exact B2214911
  · exact B2214915
  · exact B2214919
  · exact B2214923
  · exact B2214927
  · exact B2214931
  · exact B2214935
  · exact B2214939
  · exact B2214943
  · exact B2214947
  · exact B2214951
  · exact B2214955
  · exact B2214959
  · exact B2214963
  · exact B2214967
  · exact B2214971
  · exact B2214975
  · exact B2214979
  · exact B2214983
  · exact B2214987
  · exact B2214991
  · exact B2214995
  · exact B2214999
  · exact B2215003
  · exact B2215007
  · exact B2215011
  · exact B2215015
  · exact B2215019
  · exact B2215023
  · exact B2215027
  · exact B2215031
  · exact B2215035
  · exact B2215039
  · exact B2215043
  · exact B2215047
  · exact B2215051
  · exact B2215055
  · exact B2215059
  · exact B2215063
  · exact B2215067
  · exact B2215071
  · exact B2215075
  · exact B2215079
  · exact B2215083
  · exact B2215087
  · exact B2215091
  · exact B2215095
  · exact B2215099
  · exact B2215103
  · exact B2215107
  · exact B2215111
  · exact B2215115
  · exact B2215119
  · exact B2215123
  · exact B2215127
  · exact B2215131
  · exact B2215135
  · exact B2215139
  · exact B2215143
  · exact B2215147
  · exact B2215151
  · exact B2215155
  · exact B2215159
  · exact B2215163
  · exact B2215167
  · exact B2215171
  · exact B2215175
  · exact B2215179
  · exact B2215183
  · exact B2215187
  · exact B2215191
  · exact B2215195
  · exact B2215199
  · exact B2215203
  · exact B2215207
  · exact B2215211
  · exact B2215215
  · exact B2215219
  · exact B2215223
  · exact B2215227
  · exact B2215231
  · exact B2215235
  · exact B2215239
  · exact B2215243
  · exact B2215247
  · exact B2215251
  · exact B2215255
  · exact B2215259
  · exact B2215263
  · exact B2215267
  · exact B2215271
  · exact B2215275
  · exact B2215279
  · exact B2215283
  · exact B2215287
  · exact B2215291
  · exact B2215295
  · exact B2215299
  · exact B2215303
  · exact B2215307
  · exact B2215311
  · exact B2215315
  · exact B2215319
  · exact B2215323
  · exact B2215327
  · exact B2215331
  · exact B2215335
  · exact B2215339
  · exact B2215343
  · exact B2215347
  · exact B2215351
  · exact B2215355
  · exact B2215359
  · exact B2215363
  · exact B2215367
  · exact B2215371
  · exact B2215375
  · exact B2215379
  · exact B2215383
  · exact B2215387
  · exact B2215391
  · exact B2215395
  · exact B2215399
  · exact B2215403
  · exact B2215407
  · exact B2215411
  · exact B2215415
  · exact B2215419
  · exact B2215423
  · exact B2215427
  · exact B2215431
  · exact B2215435
theorem solution (m : ℕ) (hlo : 2213435 ≤ m) (hhi : m ≤ 2215435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 553358 ≤ j := by omega
    have hj2 : j ≤ 553858 := by omega
    have hb : Blo 2213435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
