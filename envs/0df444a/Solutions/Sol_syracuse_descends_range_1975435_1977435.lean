-- Prove2me | solution 1 for syracuse_descends_range_1975435_1977435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:07.145765+00:00
-- url     : https://prove2.me/submissions/49e16e77-31d0-4f0e-bcf4-e2990b31ebbd

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

theorem B2222365 : Blo 1975435 2222365 := bbase (se 3 (by rfl) ⟨416693, by rfl⟩ : syracuseStep 2222365 = 833387) (by norm_num)
theorem B2963153 : Blo 1975435 2963153 := bstep (se 2 (by rfl) ⟨1111182, by rfl⟩ : syracuseStep 2963153 = 2222365) B2222365
theorem B1975435 : Blo 1975435 1975435 := bstep (se 1 (by rfl) ⟨1481576, by rfl⟩ : syracuseStep 1975435 = 2963153) B2963153
theorem B6667109 : Blo 1975435 6667109 := bbase (se 4 (by rfl) ⟨625041, by rfl⟩ : syracuseStep 6667109 = 1250083) (by norm_num)
theorem B4444739 : Blo 1975435 4444739 := bstep (se 1 (by rfl) ⟨3333554, by rfl⟩ : syracuseStep 4444739 = 6667109) B6667109
theorem B2963159 : Blo 1975435 2963159 := bstep (se 1 (by rfl) ⟨2222369, by rfl⟩ : syracuseStep 2963159 = 4444739) B4444739
theorem B1975439 : Blo 1975435 1975439 := bstep (se 1 (by rfl) ⟨1481579, by rfl⟩ : syracuseStep 1975439 = 2963159) B2963159
theorem B2963165 : Blo 1975435 2963165 := bbase (se 3 (by rfl) ⟨555593, by rfl⟩ : syracuseStep 2963165 = 1111187) (by norm_num)
theorem B1975443 : Blo 1975435 1975443 := bstep (se 1 (by rfl) ⟨1481582, by rfl⟩ : syracuseStep 1975443 = 2963165) B2963165
theorem B4444757 : Blo 1975435 4444757 := bbase (se 8 (by rfl) ⟨26043, by rfl⟩ : syracuseStep 4444757 = 52087) (by norm_num)
theorem B2963171 : Blo 1975435 2963171 := bstep (se 1 (by rfl) ⟨2222378, by rfl⟩ : syracuseStep 2963171 = 4444757) B4444757
theorem B1975447 : Blo 1975435 1975447 := bstep (se 1 (by rfl) ⟨1481585, by rfl⟩ : syracuseStep 1975447 = 2963171) B2963171
theorem B3164293 : Blo 1975435 3164293 := bbase (se 4 (by rfl) ⟨296652, by rfl⟩ : syracuseStep 3164293 = 593305) (by norm_num)
theorem B4219057 : Blo 1975435 4219057 := bstep (se 2 (by rfl) ⟨1582146, by rfl⟩ : syracuseStep 4219057 = 3164293) B3164293
theorem B5625409 : Blo 1975435 5625409 := bstep (se 2 (by rfl) ⟨2109528, by rfl⟩ : syracuseStep 5625409 = 4219057) B4219057
theorem B7500545 : Blo 1975435 7500545 := bstep (se 2 (by rfl) ⟨2812704, by rfl⟩ : syracuseStep 7500545 = 5625409) B5625409
theorem B5000363 : Blo 1975435 5000363 := bstep (se 1 (by rfl) ⟨3750272, by rfl⟩ : syracuseStep 5000363 = 7500545) B7500545
theorem B3333575 : Blo 1975435 3333575 := bstep (se 1 (by rfl) ⟨2500181, by rfl⟩ : syracuseStep 3333575 = 5000363) B5000363
theorem B2222383 : Blo 1975435 2222383 := bstep (se 1 (by rfl) ⟨1666787, by rfl⟩ : syracuseStep 2222383 = 3333575) B3333575
theorem B2963177 : Blo 1975435 2963177 := bstep (se 2 (by rfl) ⟨1111191, by rfl⟩ : syracuseStep 2963177 = 2222383) B2222383
theorem B1975451 : Blo 1975435 1975451 := bstep (se 1 (by rfl) ⟨1481588, by rfl⟩ : syracuseStep 1975451 = 2963177) B2963177
theorem B25314389 : Blo 1975435 25314389 := bbase (se 8 (by rfl) ⟨148326, by rfl⟩ : syracuseStep 25314389 = 296653) (by norm_num)
theorem B16876259 : Blo 1975435 16876259 := bstep (se 1 (by rfl) ⟨12657194, by rfl⟩ : syracuseStep 16876259 = 25314389) B25314389
theorem B11250839 : Blo 1975435 11250839 := bstep (se 1 (by rfl) ⟨8438129, by rfl⟩ : syracuseStep 11250839 = 16876259) B16876259
theorem B7500559 : Blo 1975435 7500559 := bstep (se 1 (by rfl) ⟨5625419, by rfl⟩ : syracuseStep 7500559 = 11250839) B11250839
theorem B10000745 : Blo 1975435 10000745 := bstep (se 2 (by rfl) ⟨3750279, by rfl⟩ : syracuseStep 10000745 = 7500559) B7500559
theorem B6667163 : Blo 1975435 6667163 := bstep (se 1 (by rfl) ⟨5000372, by rfl⟩ : syracuseStep 6667163 = 10000745) B10000745
theorem B4444775 : Blo 1975435 4444775 := bstep (se 1 (by rfl) ⟨3333581, by rfl⟩ : syracuseStep 4444775 = 6667163) B6667163
theorem B2963183 : Blo 1975435 2963183 := bstep (se 1 (by rfl) ⟨2222387, by rfl⟩ : syracuseStep 2963183 = 4444775) B4444775
theorem B1975455 : Blo 1975435 1975455 := bstep (se 1 (by rfl) ⟨1481591, by rfl⟩ : syracuseStep 1975455 = 2963183) B2963183
theorem B2963189 : Blo 1975435 2963189 := bbase (se 5 (by rfl) ⟨138899, by rfl⟩ : syracuseStep 2963189 = 277799) (by norm_num)
theorem B1975459 : Blo 1975435 1975459 := bstep (se 1 (by rfl) ⟨1481594, by rfl⟩ : syracuseStep 1975459 = 2963189) B2963189
theorem B8438165 : Blo 1975435 8438165 := bbase (se 6 (by rfl) ⟨197769, by rfl⟩ : syracuseStep 8438165 = 395539) (by norm_num)
theorem B5625443 : Blo 1975435 5625443 := bstep (se 1 (by rfl) ⟨4219082, by rfl⟩ : syracuseStep 5625443 = 8438165) B8438165
theorem B3750295 : Blo 1975435 3750295 := bstep (se 1 (by rfl) ⟨2812721, by rfl⟩ : syracuseStep 3750295 = 5625443) B5625443
theorem B5000393 : Blo 1975435 5000393 := bstep (se 2 (by rfl) ⟨1875147, by rfl⟩ : syracuseStep 5000393 = 3750295) B3750295
theorem B3333595 : Blo 1975435 3333595 := bstep (se 1 (by rfl) ⟨2500196, by rfl⟩ : syracuseStep 3333595 = 5000393) B5000393
theorem B4444793 : Blo 1975435 4444793 := bstep (se 2 (by rfl) ⟨1666797, by rfl⟩ : syracuseStep 4444793 = 3333595) B3333595
theorem B2963195 : Blo 1975435 2963195 := bstep (se 1 (by rfl) ⟨2222396, by rfl⟩ : syracuseStep 2963195 = 4444793) B4444793
theorem B1975463 : Blo 1975435 1975463 := bstep (se 1 (by rfl) ⟨1481597, by rfl⟩ : syracuseStep 1975463 = 2963195) B2963195
theorem B2222401 : Blo 1975435 2222401 := bbase (se 2 (by rfl) ⟨833400, by rfl⟩ : syracuseStep 2222401 = 1666801) (by norm_num)
theorem B2963201 : Blo 1975435 2963201 := bstep (se 2 (by rfl) ⟨1111200, by rfl⟩ : syracuseStep 2963201 = 2222401) B2222401
theorem B1975467 : Blo 1975435 1975467 := bstep (se 1 (by rfl) ⟨1481600, by rfl⟩ : syracuseStep 1975467 = 2963201) B2963201
theorem B5000413 : Blo 1975435 5000413 := bbase (se 3 (by rfl) ⟨937577, by rfl⟩ : syracuseStep 5000413 = 1875155) (by norm_num)
theorem B6667217 : Blo 1975435 6667217 := bstep (se 2 (by rfl) ⟨2500206, by rfl⟩ : syracuseStep 6667217 = 5000413) B5000413
theorem B4444811 : Blo 1975435 4444811 := bstep (se 1 (by rfl) ⟨3333608, by rfl⟩ : syracuseStep 4444811 = 6667217) B6667217
theorem B2963207 : Blo 1975435 2963207 := bstep (se 1 (by rfl) ⟨2222405, by rfl⟩ : syracuseStep 2963207 = 4444811) B4444811
theorem B1975471 : Blo 1975435 1975471 := bstep (se 1 (by rfl) ⟨1481603, by rfl⟩ : syracuseStep 1975471 = 2963207) B2963207
theorem B2963213 : Blo 1975435 2963213 := bbase (se 3 (by rfl) ⟨555602, by rfl⟩ : syracuseStep 2963213 = 1111205) (by norm_num)
theorem B1975475 : Blo 1975435 1975475 := bstep (se 1 (by rfl) ⟨1481606, by rfl⟩ : syracuseStep 1975475 = 2963213) B2963213
theorem B4444829 : Blo 1975435 4444829 := bbase (se 3 (by rfl) ⟨833405, by rfl⟩ : syracuseStep 4444829 = 1666811) (by norm_num)
theorem B2963219 : Blo 1975435 2963219 := bstep (se 1 (by rfl) ⟨2222414, by rfl⟩ : syracuseStep 2963219 = 4444829) B4444829
theorem B1975479 : Blo 1975435 1975479 := bstep (se 1 (by rfl) ⟨1481609, by rfl⟩ : syracuseStep 1975479 = 2963219) B2963219
theorem B3333629 : Blo 1975435 3333629 := bbase (se 3 (by rfl) ⟨625055, by rfl⟩ : syracuseStep 3333629 = 1250111) (by norm_num)
theorem B2222419 : Blo 1975435 2222419 := bstep (se 1 (by rfl) ⟨1666814, by rfl⟩ : syracuseStep 2222419 = 3333629) B3333629
theorem B2963225 : Blo 1975435 2963225 := bstep (se 2 (by rfl) ⟨1111209, by rfl⟩ : syracuseStep 2963225 = 2222419) B2222419
theorem B1975483 : Blo 1975435 1975483 := bstep (se 1 (by rfl) ⟨1481612, by rfl⟩ : syracuseStep 1975483 = 2963225) B2963225
theorem B4219133 : Blo 1975435 4219133 := bbase (se 3 (by rfl) ⟨791087, by rfl⟩ : syracuseStep 4219133 = 1582175) (by norm_num)
theorem B11251021 : Blo 1975435 11251021 := bstep (se 3 (by rfl) ⟨2109566, by rfl⟩ : syracuseStep 11251021 = 4219133) B4219133
theorem B15001361 : Blo 1975435 15001361 := bstep (se 2 (by rfl) ⟨5625510, by rfl⟩ : syracuseStep 15001361 = 11251021) B11251021
theorem B10000907 : Blo 1975435 10000907 := bstep (se 1 (by rfl) ⟨7500680, by rfl⟩ : syracuseStep 10000907 = 15001361) B15001361
theorem B6667271 : Blo 1975435 6667271 := bstep (se 1 (by rfl) ⟨5000453, by rfl⟩ : syracuseStep 6667271 = 10000907) B10000907
theorem B4444847 : Blo 1975435 4444847 := bstep (se 1 (by rfl) ⟨3333635, by rfl⟩ : syracuseStep 4444847 = 6667271) B6667271
theorem B2963231 : Blo 1975435 2963231 := bstep (se 1 (by rfl) ⟨2222423, by rfl⟩ : syracuseStep 2963231 = 4444847) B4444847
theorem B1975487 : Blo 1975435 1975487 := bstep (se 1 (by rfl) ⟨1481615, by rfl⟩ : syracuseStep 1975487 = 2963231) B2963231
theorem B2963237 : Blo 1975435 2963237 := bbase (se 4 (by rfl) ⟨277803, by rfl⟩ : syracuseStep 2963237 = 555607) (by norm_num)
theorem B1975491 : Blo 1975435 1975491 := bstep (se 1 (by rfl) ⟨1481618, by rfl⟩ : syracuseStep 1975491 = 2963237) B2963237
theorem B2500237 : Blo 1975435 2500237 := bbase (se 3 (by rfl) ⟨468794, by rfl⟩ : syracuseStep 2500237 = 937589) (by norm_num)
theorem B3333649 : Blo 1975435 3333649 := bstep (se 2 (by rfl) ⟨1250118, by rfl⟩ : syracuseStep 3333649 = 2500237) B2500237
theorem B4444865 : Blo 1975435 4444865 := bstep (se 2 (by rfl) ⟨1666824, by rfl⟩ : syracuseStep 4444865 = 3333649) B3333649
theorem B2963243 : Blo 1975435 2963243 := bstep (se 1 (by rfl) ⟨2222432, by rfl⟩ : syracuseStep 2963243 = 4444865) B4444865
theorem B1975495 : Blo 1975435 1975495 := bstep (se 1 (by rfl) ⟨1481621, by rfl⟩ : syracuseStep 1975495 = 2963243) B2963243
theorem B2222437 : Blo 1975435 2222437 := bbase (se 4 (by rfl) ⟨208353, by rfl⟩ : syracuseStep 2222437 = 416707) (by norm_num)
theorem B2963249 : Blo 1975435 2963249 := bstep (se 2 (by rfl) ⟨1111218, by rfl⟩ : syracuseStep 2963249 = 2222437) B2222437
theorem B1975499 : Blo 1975435 1975499 := bstep (se 1 (by rfl) ⟨1481624, by rfl⟩ : syracuseStep 1975499 = 2963249) B2963249
theorem B5625557 : Blo 1975435 5625557 := bbase (se 7 (by rfl) ⟨65924, by rfl⟩ : syracuseStep 5625557 = 131849) (by norm_num)
theorem B3750371 : Blo 1975435 3750371 := bstep (se 1 (by rfl) ⟨2812778, by rfl⟩ : syracuseStep 3750371 = 5625557) B5625557
theorem B2500247 : Blo 1975435 2500247 := bstep (se 1 (by rfl) ⟨1875185, by rfl⟩ : syracuseStep 2500247 = 3750371) B3750371
theorem B6667325 : Blo 1975435 6667325 := bstep (se 3 (by rfl) ⟨1250123, by rfl⟩ : syracuseStep 6667325 = 2500247) B2500247
theorem B4444883 : Blo 1975435 4444883 := bstep (se 1 (by rfl) ⟨3333662, by rfl⟩ : syracuseStep 4444883 = 6667325) B6667325
theorem B2963255 : Blo 1975435 2963255 := bstep (se 1 (by rfl) ⟨2222441, by rfl⟩ : syracuseStep 2963255 = 4444883) B4444883
theorem B1975503 : Blo 1975435 1975503 := bstep (se 1 (by rfl) ⟨1481627, by rfl⟩ : syracuseStep 1975503 = 2963255) B2963255
theorem B2963261 : Blo 1975435 2963261 := bbase (se 3 (by rfl) ⟨555611, by rfl⟩ : syracuseStep 2963261 = 1111223) (by norm_num)
theorem B1975507 : Blo 1975435 1975507 := bstep (se 1 (by rfl) ⟨1481630, by rfl⟩ : syracuseStep 1975507 = 2963261) B2963261
theorem B4444901 : Blo 1975435 4444901 := bbase (se 4 (by rfl) ⟨416709, by rfl⟩ : syracuseStep 4444901 = 833419) (by norm_num)
theorem B2963267 : Blo 1975435 2963267 := bstep (se 1 (by rfl) ⟨2222450, by rfl⟩ : syracuseStep 2963267 = 4444901) B4444901
theorem B1975511 : Blo 1975435 1975511 := bstep (se 1 (by rfl) ⟨1481633, by rfl⟩ : syracuseStep 1975511 = 2963267) B2963267
theorem B5000525 : Blo 1975435 5000525 := bbase (se 3 (by rfl) ⟨937598, by rfl⟩ : syracuseStep 5000525 = 1875197) (by norm_num)
theorem B3333683 : Blo 1975435 3333683 := bstep (se 1 (by rfl) ⟨2500262, by rfl⟩ : syracuseStep 3333683 = 5000525) B5000525
theorem B2222455 : Blo 1975435 2222455 := bstep (se 1 (by rfl) ⟨1666841, by rfl⟩ : syracuseStep 2222455 = 3333683) B3333683
theorem B2963273 : Blo 1975435 2963273 := bstep (se 2 (by rfl) ⟨1111227, by rfl⟩ : syracuseStep 2963273 = 2222455) B2222455
theorem B1975515 : Blo 1975435 1975515 := bstep (se 1 (by rfl) ⟨1481636, by rfl⟩ : syracuseStep 1975515 = 2963273) B2963273
theorem B2109601 : Blo 1975435 2109601 := bbase (se 2 (by rfl) ⟨791100, by rfl⟩ : syracuseStep 2109601 = 1582201) (by norm_num)
theorem B2812801 : Blo 1975435 2812801 := bstep (se 2 (by rfl) ⟨1054800, by rfl⟩ : syracuseStep 2812801 = 2109601) B2109601
theorem B3750401 : Blo 1975435 3750401 := bstep (se 2 (by rfl) ⟨1406400, by rfl⟩ : syracuseStep 3750401 = 2812801) B2812801
theorem B10001069 : Blo 1975435 10001069 := bstep (se 3 (by rfl) ⟨1875200, by rfl⟩ : syracuseStep 10001069 = 3750401) B3750401
theorem B6667379 : Blo 1975435 6667379 := bstep (se 1 (by rfl) ⟨5000534, by rfl⟩ : syracuseStep 6667379 = 10001069) B10001069
theorem B4444919 : Blo 1975435 4444919 := bstep (se 1 (by rfl) ⟨3333689, by rfl⟩ : syracuseStep 4444919 = 6667379) B6667379
theorem B2963279 : Blo 1975435 2963279 := bstep (se 1 (by rfl) ⟨2222459, by rfl⟩ : syracuseStep 2963279 = 4444919) B4444919
theorem B1975519 : Blo 1975435 1975519 := bstep (se 1 (by rfl) ⟨1481639, by rfl⟩ : syracuseStep 1975519 = 2963279) B2963279
theorem B2963285 : Blo 1975435 2963285 := bbase (se 9 (by rfl) ⟨8681, by rfl⟩ : syracuseStep 2963285 = 17363) (by norm_num)
theorem B1975523 : Blo 1975435 1975523 := bstep (se 1 (by rfl) ⟨1481642, by rfl⟩ : syracuseStep 1975523 = 2963285) B2963285
theorem B2138393 : Blo 1975435 2138393 := bbase (se 2 (by rfl) ⟨801897, by rfl⟩ : syracuseStep 2138393 = 1603795) (by norm_num)
theorem B5702381 : Blo 1975435 5702381 := bstep (se 3 (by rfl) ⟨1069196, by rfl⟩ : syracuseStep 5702381 = 2138393) B2138393
theorem B3801587 : Blo 1975435 3801587 := bstep (se 1 (by rfl) ⟨2851190, by rfl⟩ : syracuseStep 3801587 = 5702381) B5702381
theorem B10137565 : Blo 1975435 10137565 := bstep (se 3 (by rfl) ⟨1900793, by rfl⟩ : syracuseStep 10137565 = 3801587) B3801587
theorem B13516753 : Blo 1975435 13516753 := bstep (se 2 (by rfl) ⟨5068782, by rfl⟩ : syracuseStep 13516753 = 10137565) B10137565
theorem B18022337 : Blo 1975435 18022337 := bstep (se 2 (by rfl) ⟨6758376, by rfl⟩ : syracuseStep 18022337 = 13516753) B13516753
theorem B12014891 : Blo 1975435 12014891 := bstep (se 1 (by rfl) ⟨9011168, by rfl⟩ : syracuseStep 12014891 = 18022337) B18022337
theorem B8009927 : Blo 1975435 8009927 := bstep (se 1 (by rfl) ⟨6007445, by rfl⟩ : syracuseStep 8009927 = 12014891) B12014891
theorem B5339951 : Blo 1975435 5339951 := bstep (se 1 (by rfl) ⟨4004963, by rfl⟩ : syracuseStep 5339951 = 8009927) B8009927
theorem B3559967 : Blo 1975435 3559967 := bstep (se 1 (by rfl) ⟨2669975, by rfl⟩ : syracuseStep 3559967 = 5339951) B5339951
theorem B2373311 : Blo 1975435 2373311 := bstep (se 1 (by rfl) ⟨1779983, by rfl⟩ : syracuseStep 2373311 = 3559967) B3559967
theorem B6328829 : Blo 1975435 6328829 := bstep (se 3 (by rfl) ⟨1186655, by rfl⟩ : syracuseStep 6328829 = 2373311) B2373311
theorem B4219219 : Blo 1975435 4219219 := bstep (se 1 (by rfl) ⟨3164414, by rfl⟩ : syracuseStep 4219219 = 6328829) B6328829
theorem B5625625 : Blo 1975435 5625625 := bstep (se 2 (by rfl) ⟨2109609, by rfl⟩ : syracuseStep 5625625 = 4219219) B4219219
theorem B7500833 : Blo 1975435 7500833 := bstep (se 2 (by rfl) ⟨2812812, by rfl⟩ : syracuseStep 7500833 = 5625625) B5625625
theorem B5000555 : Blo 1975435 5000555 := bstep (se 1 (by rfl) ⟨3750416, by rfl⟩ : syracuseStep 5000555 = 7500833) B7500833
theorem B3333703 : Blo 1975435 3333703 := bstep (se 1 (by rfl) ⟨2500277, by rfl⟩ : syracuseStep 3333703 = 5000555) B5000555
theorem B4444937 : Blo 1975435 4444937 := bstep (se 2 (by rfl) ⟨1666851, by rfl⟩ : syracuseStep 4444937 = 3333703) B3333703
theorem B2963291 : Blo 1975435 2963291 := bstep (se 1 (by rfl) ⟨2222468, by rfl⟩ : syracuseStep 2963291 = 4444937) B4444937
theorem B1975527 : Blo 1975435 1975527 := bstep (se 1 (by rfl) ⟨1481645, by rfl⟩ : syracuseStep 1975527 = 2963291) B2963291
theorem B2222473 : Blo 1975435 2222473 := bbase (se 2 (by rfl) ⟨833427, by rfl⟩ : syracuseStep 2222473 = 1666855) (by norm_num)
theorem B2963297 : Blo 1975435 2963297 := bstep (se 2 (by rfl) ⟨1111236, by rfl⟩ : syracuseStep 2963297 = 2222473) B2222473
theorem B1975531 : Blo 1975435 1975531 := bstep (se 1 (by rfl) ⟨1481648, by rfl⟩ : syracuseStep 1975531 = 2963297) B2963297
theorem B2002489 : Blo 1975435 2002489 := bbase (se 2 (by rfl) ⟨750933, by rfl⟩ : syracuseStep 2002489 = 1501867) (by norm_num)
theorem B10679941 : Blo 1975435 10679941 := bstep (se 4 (by rfl) ⟨1001244, by rfl⟩ : syracuseStep 10679941 = 2002489) B2002489
theorem B56959685 : Blo 1975435 56959685 := bstep (se 4 (by rfl) ⟨5339970, by rfl⟩ : syracuseStep 56959685 = 10679941) B10679941
theorem B37973123 : Blo 1975435 37973123 := bstep (se 1 (by rfl) ⟨28479842, by rfl⟩ : syracuseStep 37973123 = 56959685) B56959685
theorem B25315415 : Blo 1975435 25315415 := bstep (se 1 (by rfl) ⟨18986561, by rfl⟩ : syracuseStep 25315415 = 37973123) B37973123
theorem B16876943 : Blo 1975435 16876943 := bstep (se 1 (by rfl) ⟨12657707, by rfl⟩ : syracuseStep 16876943 = 25315415) B25315415
theorem B11251295 : Blo 1975435 11251295 := bstep (se 1 (by rfl) ⟨8438471, by rfl⟩ : syracuseStep 11251295 = 16876943) B16876943
theorem B7500863 : Blo 1975435 7500863 := bstep (se 1 (by rfl) ⟨5625647, by rfl⟩ : syracuseStep 7500863 = 11251295) B11251295
theorem B5000575 : Blo 1975435 5000575 := bstep (se 1 (by rfl) ⟨3750431, by rfl⟩ : syracuseStep 5000575 = 7500863) B7500863
theorem B6667433 : Blo 1975435 6667433 := bstep (se 2 (by rfl) ⟨2500287, by rfl⟩ : syracuseStep 6667433 = 5000575) B5000575
theorem B4444955 : Blo 1975435 4444955 := bstep (se 1 (by rfl) ⟨3333716, by rfl⟩ : syracuseStep 4444955 = 6667433) B6667433
theorem B2963303 : Blo 1975435 2963303 := bstep (se 1 (by rfl) ⟨2222477, by rfl⟩ : syracuseStep 2963303 = 4444955) B4444955
theorem B1975535 : Blo 1975435 1975535 := bstep (se 1 (by rfl) ⟨1481651, by rfl⟩ : syracuseStep 1975535 = 2963303) B2963303
theorem B2963309 : Blo 1975435 2963309 := bbase (se 3 (by rfl) ⟨555620, by rfl⟩ : syracuseStep 2963309 = 1111241) (by norm_num)
theorem B1975539 : Blo 1975435 1975539 := bstep (se 1 (by rfl) ⟨1481654, by rfl⟩ : syracuseStep 1975539 = 2963309) B2963309
theorem B4444973 : Blo 1975435 4444973 := bbase (se 3 (by rfl) ⟨833432, by rfl⟩ : syracuseStep 4444973 = 1666865) (by norm_num)
theorem B2963315 : Blo 1975435 2963315 := bstep (se 1 (by rfl) ⟨2222486, by rfl⟩ : syracuseStep 2963315 = 4444973) B4444973
theorem B1975543 : Blo 1975435 1975543 := bstep (se 1 (by rfl) ⟨1481657, by rfl⟩ : syracuseStep 1975543 = 2963315) B2963315
theorem B7603253 : Blo 1975435 7603253 := bbase (se 5 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 7603253 = 712805) (by norm_num)
theorem B5068835 : Blo 1975435 5068835 := bstep (se 1 (by rfl) ⟨3801626, by rfl⟩ : syracuseStep 5068835 = 7603253) B7603253
theorem B3379223 : Blo 1975435 3379223 := bstep (se 1 (by rfl) ⟨2534417, by rfl⟩ : syracuseStep 3379223 = 5068835) B5068835
theorem B2252815 : Blo 1975435 2252815 := bstep (se 1 (by rfl) ⟨1689611, by rfl⟩ : syracuseStep 2252815 = 3379223) B3379223
theorem B12015013 : Blo 1975435 12015013 := bstep (se 4 (by rfl) ⟨1126407, by rfl⟩ : syracuseStep 12015013 = 2252815) B2252815
theorem B16020017 : Blo 1975435 16020017 := bstep (se 2 (by rfl) ⟨6007506, by rfl⟩ : syracuseStep 16020017 = 12015013) B12015013
theorem B10680011 : Blo 1975435 10680011 := bstep (se 1 (by rfl) ⟨8010008, by rfl⟩ : syracuseStep 10680011 = 16020017) B16020017
theorem B7120007 : Blo 1975435 7120007 := bstep (se 1 (by rfl) ⟨5340005, by rfl⟩ : syracuseStep 7120007 = 10680011) B10680011
theorem B4746671 : Blo 1975435 4746671 := bstep (se 1 (by rfl) ⟨3560003, by rfl⟩ : syracuseStep 4746671 = 7120007) B7120007
theorem B3164447 : Blo 1975435 3164447 := bstep (se 1 (by rfl) ⟨2373335, by rfl⟩ : syracuseStep 3164447 = 4746671) B4746671
theorem B8438525 : Blo 1975435 8438525 := bstep (se 3 (by rfl) ⟨1582223, by rfl⟩ : syracuseStep 8438525 = 3164447) B3164447
theorem B5625683 : Blo 1975435 5625683 := bstep (se 1 (by rfl) ⟨4219262, by rfl⟩ : syracuseStep 5625683 = 8438525) B8438525
theorem B3750455 : Blo 1975435 3750455 := bstep (se 1 (by rfl) ⟨2812841, by rfl⟩ : syracuseStep 3750455 = 5625683) B5625683
theorem B2500303 : Blo 1975435 2500303 := bstep (se 1 (by rfl) ⟨1875227, by rfl⟩ : syracuseStep 2500303 = 3750455) B3750455
theorem B3333737 : Blo 1975435 3333737 := bstep (se 2 (by rfl) ⟨1250151, by rfl⟩ : syracuseStep 3333737 = 2500303) B2500303
theorem B2222491 : Blo 1975435 2222491 := bstep (se 1 (by rfl) ⟨1666868, by rfl⟩ : syracuseStep 2222491 = 3333737) B3333737
theorem B2963321 : Blo 1975435 2963321 := bstep (se 2 (by rfl) ⟨1111245, by rfl⟩ : syracuseStep 2963321 = 2222491) B2222491
theorem B1975547 : Blo 1975435 1975547 := bstep (se 1 (by rfl) ⟨1481660, by rfl⟩ : syracuseStep 1975547 = 2963321) B2963321
theorem B3379229 : Blo 1975435 3379229 := bbase (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) (by norm_num)
theorem B2252819 : Blo 1975435 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B6007517 : Blo 1975435 6007517 := bstep (se 3 (by rfl) ⟨1126409, by rfl⟩ : syracuseStep 6007517 = 2252819) B2252819
theorem B4005011 : Blo 1975435 4005011 := bstep (se 1 (by rfl) ⟨3003758, by rfl⟩ : syracuseStep 4005011 = 6007517) B6007517
theorem B2670007 : Blo 1975435 2670007 := bstep (se 1 (by rfl) ⟨2002505, by rfl⟩ : syracuseStep 2670007 = 4005011) B4005011
theorem B3560009 : Blo 1975435 3560009 := bstep (se 2 (by rfl) ⟨1335003, by rfl⟩ : syracuseStep 3560009 = 2670007) B2670007
theorem B9493357 : Blo 1975435 9493357 := bstep (se 3 (by rfl) ⟨1780004, by rfl⟩ : syracuseStep 9493357 = 3560009) B3560009
theorem B12657809 : Blo 1975435 12657809 := bstep (se 2 (by rfl) ⟨4746678, by rfl⟩ : syracuseStep 12657809 = 9493357) B9493357
theorem B33754157 : Blo 1975435 33754157 := bstep (se 3 (by rfl) ⟨6328904, by rfl⟩ : syracuseStep 33754157 = 12657809) B12657809
theorem B22502771 : Blo 1975435 22502771 := bstep (se 1 (by rfl) ⟨16877078, by rfl⟩ : syracuseStep 22502771 = 33754157) B33754157
theorem B15001847 : Blo 1975435 15001847 := bstep (se 1 (by rfl) ⟨11251385, by rfl⟩ : syracuseStep 15001847 = 22502771) B22502771
theorem B10001231 : Blo 1975435 10001231 := bstep (se 1 (by rfl) ⟨7500923, by rfl⟩ : syracuseStep 10001231 = 15001847) B15001847
theorem B6667487 : Blo 1975435 6667487 := bstep (se 1 (by rfl) ⟨5000615, by rfl⟩ : syracuseStep 6667487 = 10001231) B10001231
theorem B4444991 : Blo 1975435 4444991 := bstep (se 1 (by rfl) ⟨3333743, by rfl⟩ : syracuseStep 4444991 = 6667487) B6667487
theorem B2963327 : Blo 1975435 2963327 := bstep (se 1 (by rfl) ⟨2222495, by rfl⟩ : syracuseStep 2963327 = 4444991) B4444991
theorem B1975551 : Blo 1975435 1975551 := bstep (se 1 (by rfl) ⟨1481663, by rfl⟩ : syracuseStep 1975551 = 2963327) B2963327
theorem B2963333 : Blo 1975435 2963333 := bbase (se 4 (by rfl) ⟨277812, by rfl⟩ : syracuseStep 2963333 = 555625) (by norm_num)
theorem B1975555 : Blo 1975435 1975555 := bstep (se 1 (by rfl) ⟨1481666, by rfl⟩ : syracuseStep 1975555 = 2963333) B2963333
theorem B3333757 : Blo 1975435 3333757 := bbase (se 3 (by rfl) ⟨625079, by rfl⟩ : syracuseStep 3333757 = 1250159) (by norm_num)
theorem B4445009 : Blo 1975435 4445009 := bstep (se 2 (by rfl) ⟨1666878, by rfl⟩ : syracuseStep 4445009 = 3333757) B3333757
theorem B2963339 : Blo 1975435 2963339 := bstep (se 1 (by rfl) ⟨2222504, by rfl⟩ : syracuseStep 2963339 = 4445009) B4445009
theorem B1975559 : Blo 1975435 1975559 := bstep (se 1 (by rfl) ⟨1481669, by rfl⟩ : syracuseStep 1975559 = 2963339) B2963339
theorem B2222509 : Blo 1975435 2222509 := bbase (se 3 (by rfl) ⟨416720, by rfl⟩ : syracuseStep 2222509 = 833441) (by norm_num)
theorem B2963345 : Blo 1975435 2963345 := bstep (se 2 (by rfl) ⟨1111254, by rfl⟩ : syracuseStep 2963345 = 2222509) B2222509
theorem B1975563 : Blo 1975435 1975563 := bstep (se 1 (by rfl) ⟨1481672, by rfl⟩ : syracuseStep 1975563 = 2963345) B2963345
theorem B6667541 : Blo 1975435 6667541 := bbase (se 6 (by rfl) ⟨156270, by rfl⟩ : syracuseStep 6667541 = 312541) (by norm_num)
theorem B4445027 : Blo 1975435 4445027 := bstep (se 1 (by rfl) ⟨3333770, by rfl⟩ : syracuseStep 4445027 = 6667541) B6667541
theorem B2963351 : Blo 1975435 2963351 := bstep (se 1 (by rfl) ⟨2222513, by rfl⟩ : syracuseStep 2963351 = 4445027) B4445027
theorem B1975567 : Blo 1975435 1975567 := bstep (se 1 (by rfl) ⟨1481675, by rfl⟩ : syracuseStep 1975567 = 2963351) B2963351
theorem B2963357 : Blo 1975435 2963357 := bbase (se 3 (by rfl) ⟨555629, by rfl⟩ : syracuseStep 2963357 = 1111259) (by norm_num)
theorem B1975571 : Blo 1975435 1975571 := bstep (se 1 (by rfl) ⟨1481678, by rfl⟩ : syracuseStep 1975571 = 2963357) B2963357
theorem B4445045 : Blo 1975435 4445045 := bbase (se 5 (by rfl) ⟨208361, by rfl⟩ : syracuseStep 4445045 = 416723) (by norm_num)
theorem B2963363 : Blo 1975435 2963363 := bstep (se 1 (by rfl) ⟨2222522, by rfl⟩ : syracuseStep 2963363 = 4445045) B4445045
theorem B1975575 : Blo 1975435 1975575 := bstep (se 1 (by rfl) ⟨1481681, by rfl⟩ : syracuseStep 1975575 = 2963363) B2963363
theorem B4811509 : Blo 1975435 4811509 := bbase (se 5 (by rfl) ⟨225539, by rfl⟩ : syracuseStep 4811509 = 451079) (by norm_num)
theorem B6415345 : Blo 1975435 6415345 := bstep (se 2 (by rfl) ⟨2405754, by rfl⟩ : syracuseStep 6415345 = 4811509) B4811509
theorem B8553793 : Blo 1975435 8553793 := bstep (se 2 (by rfl) ⟨3207672, by rfl⟩ : syracuseStep 8553793 = 6415345) B6415345
theorem B11405057 : Blo 1975435 11405057 := bstep (se 2 (by rfl) ⟨4276896, by rfl⟩ : syracuseStep 11405057 = 8553793) B8553793
theorem B30413485 : Blo 1975435 30413485 := bstep (se 3 (by rfl) ⟨5702528, by rfl⟩ : syracuseStep 30413485 = 11405057) B11405057
theorem B40551313 : Blo 1975435 40551313 := bstep (se 2 (by rfl) ⟨15206742, by rfl⟩ : syracuseStep 40551313 = 30413485) B30413485
theorem B54068417 : Blo 1975435 54068417 := bstep (se 2 (by rfl) ⟨20275656, by rfl⟩ : syracuseStep 54068417 = 40551313) B40551313
theorem B36045611 : Blo 1975435 36045611 := bstep (se 1 (by rfl) ⟨27034208, by rfl⟩ : syracuseStep 36045611 = 54068417) B54068417
theorem B24030407 : Blo 1975435 24030407 := bstep (se 1 (by rfl) ⟨18022805, by rfl⟩ : syracuseStep 24030407 = 36045611) B36045611
theorem B16020271 : Blo 1975435 16020271 := bstep (se 1 (by rfl) ⟨12015203, by rfl⟩ : syracuseStep 16020271 = 24030407) B24030407
theorem B21360361 : Blo 1975435 21360361 := bstep (se 2 (by rfl) ⟨8010135, by rfl⟩ : syracuseStep 21360361 = 16020271) B16020271
theorem B28480481 : Blo 1975435 28480481 := bstep (se 2 (by rfl) ⟨10680180, by rfl⟩ : syracuseStep 28480481 = 21360361) B21360361
theorem B18986987 : Blo 1975435 18986987 := bstep (se 1 (by rfl) ⟨14240240, by rfl⟩ : syracuseStep 18986987 = 28480481) B28480481
theorem B12657991 : Blo 1975435 12657991 := bstep (se 1 (by rfl) ⟨9493493, by rfl⟩ : syracuseStep 12657991 = 18986987) B18986987
theorem B16877321 : Blo 1975435 16877321 := bstep (se 2 (by rfl) ⟨6328995, by rfl⟩ : syracuseStep 16877321 = 12657991) B12657991
theorem B11251547 : Blo 1975435 11251547 := bstep (se 1 (by rfl) ⟨8438660, by rfl⟩ : syracuseStep 11251547 = 16877321) B16877321
theorem B7501031 : Blo 1975435 7501031 := bstep (se 1 (by rfl) ⟨5625773, by rfl⟩ : syracuseStep 7501031 = 11251547) B11251547
theorem B5000687 : Blo 1975435 5000687 := bstep (se 1 (by rfl) ⟨3750515, by rfl⟩ : syracuseStep 5000687 = 7501031) B7501031
theorem B3333791 : Blo 1975435 3333791 := bstep (se 1 (by rfl) ⟨2500343, by rfl⟩ : syracuseStep 3333791 = 5000687) B5000687
theorem B2222527 : Blo 1975435 2222527 := bstep (se 1 (by rfl) ⟨1666895, by rfl⟩ : syracuseStep 2222527 = 3333791) B3333791
theorem B2963369 : Blo 1975435 2963369 := bstep (se 2 (by rfl) ⟨1111263, by rfl⟩ : syracuseStep 2963369 = 2222527) B2222527
theorem B1975579 : Blo 1975435 1975579 := bstep (se 1 (by rfl) ⟨1481684, by rfl⟩ : syracuseStep 1975579 = 2963369) B2963369
theorem B7501045 : Blo 1975435 7501045 := bbase (se 5 (by rfl) ⟨351611, by rfl⟩ : syracuseStep 7501045 = 703223) (by norm_num)
theorem B10001393 : Blo 1975435 10001393 := bstep (se 2 (by rfl) ⟨3750522, by rfl⟩ : syracuseStep 10001393 = 7501045) B7501045
theorem B6667595 : Blo 1975435 6667595 := bstep (se 1 (by rfl) ⟨5000696, by rfl⟩ : syracuseStep 6667595 = 10001393) B10001393
theorem B4445063 : Blo 1975435 4445063 := bstep (se 1 (by rfl) ⟨3333797, by rfl⟩ : syracuseStep 4445063 = 6667595) B6667595
theorem B2963375 : Blo 1975435 2963375 := bstep (se 1 (by rfl) ⟨2222531, by rfl⟩ : syracuseStep 2963375 = 4445063) B4445063
theorem B1975583 : Blo 1975435 1975583 := bstep (se 1 (by rfl) ⟨1481687, by rfl⟩ : syracuseStep 1975583 = 2963375) B2963375
theorem B2963381 : Blo 1975435 2963381 := bbase (se 5 (by rfl) ⟨138908, by rfl⟩ : syracuseStep 2963381 = 277817) (by norm_num)
theorem B1975587 : Blo 1975435 1975587 := bstep (se 1 (by rfl) ⟨1481690, by rfl⟩ : syracuseStep 1975587 = 2963381) B2963381
theorem B5000717 : Blo 1975435 5000717 := bbase (se 3 (by rfl) ⟨937634, by rfl⟩ : syracuseStep 5000717 = 1875269) (by norm_num)
theorem B3333811 : Blo 1975435 3333811 := bstep (se 1 (by rfl) ⟨2500358, by rfl⟩ : syracuseStep 3333811 = 5000717) B5000717
theorem B4445081 : Blo 1975435 4445081 := bstep (se 2 (by rfl) ⟨1666905, by rfl⟩ : syracuseStep 4445081 = 3333811) B3333811
theorem B2963387 : Blo 1975435 2963387 := bstep (se 1 (by rfl) ⟨2222540, by rfl⟩ : syracuseStep 2963387 = 4445081) B4445081
theorem B1975591 : Blo 1975435 1975591 := bstep (se 1 (by rfl) ⟨1481693, by rfl⟩ : syracuseStep 1975591 = 2963387) B2963387
theorem B2222545 : Blo 1975435 2222545 := bbase (se 2 (by rfl) ⟨833454, by rfl⟩ : syracuseStep 2222545 = 1666909) (by norm_num)
theorem B2963393 : Blo 1975435 2963393 := bstep (se 2 (by rfl) ⟨1111272, by rfl⟩ : syracuseStep 2963393 = 2222545) B2222545
theorem B1975595 : Blo 1975435 1975595 := bstep (se 1 (by rfl) ⟨1481696, by rfl⟩ : syracuseStep 1975595 = 2963393) B2963393
theorem B4219373 : Blo 1975435 4219373 := bbase (se 3 (by rfl) ⟨791132, by rfl⟩ : syracuseStep 4219373 = 1582265) (by norm_num)
theorem B2812915 : Blo 1975435 2812915 := bstep (se 1 (by rfl) ⟨2109686, by rfl⟩ : syracuseStep 2812915 = 4219373) B4219373
theorem B3750553 : Blo 1975435 3750553 := bstep (se 2 (by rfl) ⟨1406457, by rfl⟩ : syracuseStep 3750553 = 2812915) B2812915
theorem B5000737 : Blo 1975435 5000737 := bstep (se 2 (by rfl) ⟨1875276, by rfl⟩ : syracuseStep 5000737 = 3750553) B3750553
theorem B6667649 : Blo 1975435 6667649 := bstep (se 2 (by rfl) ⟨2500368, by rfl⟩ : syracuseStep 6667649 = 5000737) B5000737
theorem B4445099 : Blo 1975435 4445099 := bstep (se 1 (by rfl) ⟨3333824, by rfl⟩ : syracuseStep 4445099 = 6667649) B6667649
theorem B2963399 : Blo 1975435 2963399 := bstep (se 1 (by rfl) ⟨2222549, by rfl⟩ : syracuseStep 2963399 = 4445099) B4445099
theorem B1975599 : Blo 1975435 1975599 := bstep (se 1 (by rfl) ⟨1481699, by rfl⟩ : syracuseStep 1975599 = 2963399) B2963399
theorem B2963405 : Blo 1975435 2963405 := bbase (se 3 (by rfl) ⟨555638, by rfl⟩ : syracuseStep 2963405 = 1111277) (by norm_num)
theorem B1975603 : Blo 1975435 1975603 := bstep (se 1 (by rfl) ⟨1481702, by rfl⟩ : syracuseStep 1975603 = 2963405) B2963405
theorem B4445117 : Blo 1975435 4445117 := bbase (se 3 (by rfl) ⟨833459, by rfl⟩ : syracuseStep 4445117 = 1666919) (by norm_num)
theorem B2963411 : Blo 1975435 2963411 := bstep (se 1 (by rfl) ⟨2222558, by rfl⟩ : syracuseStep 2963411 = 4445117) B4445117
theorem B1975607 : Blo 1975435 1975607 := bstep (se 1 (by rfl) ⟨1481705, by rfl⟩ : syracuseStep 1975607 = 2963411) B2963411
theorem B3333845 : Blo 1975435 3333845 := bbase (se 7 (by rfl) ⟨39068, by rfl⟩ : syracuseStep 3333845 = 78137) (by norm_num)
theorem B2222563 : Blo 1975435 2222563 := bstep (se 1 (by rfl) ⟨1666922, by rfl⟩ : syracuseStep 2222563 = 3333845) B3333845
theorem B2963417 : Blo 1975435 2963417 := bstep (se 2 (by rfl) ⟨1111281, by rfl⟩ : syracuseStep 2963417 = 2222563) B2222563
theorem B1975611 : Blo 1975435 1975611 := bstep (se 1 (by rfl) ⟨1481708, by rfl⟩ : syracuseStep 1975611 = 2963417) B2963417
theorem B3560125 : Blo 1975435 3560125 := bbase (se 3 (by rfl) ⟨667523, by rfl⟩ : syracuseStep 3560125 = 1335047) (by norm_num)
theorem B4746833 : Blo 1975435 4746833 := bstep (se 2 (by rfl) ⟨1780062, by rfl⟩ : syracuseStep 4746833 = 3560125) B3560125
theorem B3164555 : Blo 1975435 3164555 := bstep (se 1 (by rfl) ⟨2373416, by rfl⟩ : syracuseStep 3164555 = 4746833) B4746833
theorem B8438813 : Blo 1975435 8438813 := bstep (se 3 (by rfl) ⟨1582277, by rfl⟩ : syracuseStep 8438813 = 3164555) B3164555
theorem B5625875 : Blo 1975435 5625875 := bstep (se 1 (by rfl) ⟨4219406, by rfl⟩ : syracuseStep 5625875 = 8438813) B8438813
theorem B15002333 : Blo 1975435 15002333 := bstep (se 3 (by rfl) ⟨2812937, by rfl⟩ : syracuseStep 15002333 = 5625875) B5625875
theorem B10001555 : Blo 1975435 10001555 := bstep (se 1 (by rfl) ⟨7501166, by rfl⟩ : syracuseStep 10001555 = 15002333) B15002333
theorem B6667703 : Blo 1975435 6667703 := bstep (se 1 (by rfl) ⟨5000777, by rfl⟩ : syracuseStep 6667703 = 10001555) B10001555
theorem B4445135 : Blo 1975435 4445135 := bstep (se 1 (by rfl) ⟨3333851, by rfl⟩ : syracuseStep 4445135 = 6667703) B6667703
theorem B2963423 : Blo 1975435 2963423 := bstep (se 1 (by rfl) ⟨2222567, by rfl⟩ : syracuseStep 2963423 = 4445135) B4445135
theorem B1975615 : Blo 1975435 1975615 := bstep (se 1 (by rfl) ⟨1481711, by rfl⟩ : syracuseStep 1975615 = 2963423) B2963423
theorem B2963429 : Blo 1975435 2963429 := bbase (se 4 (by rfl) ⟨277821, by rfl⟩ : syracuseStep 2963429 = 555643) (by norm_num)
theorem B1975619 : Blo 1975435 1975619 := bstep (se 1 (by rfl) ⟨1481714, by rfl⟩ : syracuseStep 1975619 = 2963429) B2963429
theorem B4746853 : Blo 1975435 4746853 := bbase (se 4 (by rfl) ⟨445017, by rfl⟩ : syracuseStep 4746853 = 890035) (by norm_num)
theorem B6329137 : Blo 1975435 6329137 := bstep (se 2 (by rfl) ⟨2373426, by rfl⟩ : syracuseStep 6329137 = 4746853) B4746853
theorem B8438849 : Blo 1975435 8438849 := bstep (se 2 (by rfl) ⟨3164568, by rfl⟩ : syracuseStep 8438849 = 6329137) B6329137
theorem B5625899 : Blo 1975435 5625899 := bstep (se 1 (by rfl) ⟨4219424, by rfl⟩ : syracuseStep 5625899 = 8438849) B8438849
theorem B3750599 : Blo 1975435 3750599 := bstep (se 1 (by rfl) ⟨2812949, by rfl⟩ : syracuseStep 3750599 = 5625899) B5625899
theorem B2500399 : Blo 1975435 2500399 := bstep (se 1 (by rfl) ⟨1875299, by rfl⟩ : syracuseStep 2500399 = 3750599) B3750599
theorem B3333865 : Blo 1975435 3333865 := bstep (se 2 (by rfl) ⟨1250199, by rfl⟩ : syracuseStep 3333865 = 2500399) B2500399
theorem B4445153 : Blo 1975435 4445153 := bstep (se 2 (by rfl) ⟨1666932, by rfl⟩ : syracuseStep 4445153 = 3333865) B3333865
theorem B2963435 : Blo 1975435 2963435 := bstep (se 1 (by rfl) ⟨2222576, by rfl⟩ : syracuseStep 2963435 = 4445153) B4445153
theorem B1975623 : Blo 1975435 1975623 := bstep (se 1 (by rfl) ⟨1481717, by rfl⟩ : syracuseStep 1975623 = 2963435) B2963435
theorem B2222581 : Blo 1975435 2222581 := bbase (se 5 (by rfl) ⟨104183, by rfl⟩ : syracuseStep 2222581 = 208367) (by norm_num)
theorem B2963441 : Blo 1975435 2963441 := bstep (se 2 (by rfl) ⟨1111290, by rfl⟩ : syracuseStep 2963441 = 2222581) B2222581
theorem B1975627 : Blo 1975435 1975627 := bstep (se 1 (by rfl) ⟨1481720, by rfl⟩ : syracuseStep 1975627 = 2963441) B2963441
theorem B2500409 : Blo 1975435 2500409 := bbase (se 2 (by rfl) ⟨937653, by rfl⟩ : syracuseStep 2500409 = 1875307) (by norm_num)
theorem B6667757 : Blo 1975435 6667757 := bstep (se 3 (by rfl) ⟨1250204, by rfl⟩ : syracuseStep 6667757 = 2500409) B2500409
theorem B4445171 : Blo 1975435 4445171 := bstep (se 1 (by rfl) ⟨3333878, by rfl⟩ : syracuseStep 4445171 = 6667757) B6667757
theorem B2963447 : Blo 1975435 2963447 := bstep (se 1 (by rfl) ⟨2222585, by rfl⟩ : syracuseStep 2963447 = 4445171) B4445171
theorem B1975631 : Blo 1975435 1975631 := bstep (se 1 (by rfl) ⟨1481723, by rfl⟩ : syracuseStep 1975631 = 2963447) B2963447
theorem B2963453 : Blo 1975435 2963453 := bbase (se 3 (by rfl) ⟨555647, by rfl⟩ : syracuseStep 2963453 = 1111295) (by norm_num)
theorem B1975635 : Blo 1975435 1975635 := bstep (se 1 (by rfl) ⟨1481726, by rfl⟩ : syracuseStep 1975635 = 2963453) B2963453
theorem B4445189 : Blo 1975435 4445189 := bbase (se 4 (by rfl) ⟨416736, by rfl⟩ : syracuseStep 4445189 = 833473) (by norm_num)
theorem B2963459 : Blo 1975435 2963459 := bstep (se 1 (by rfl) ⟨2222594, by rfl⟩ : syracuseStep 2963459 = 4445189) B4445189
theorem B1975639 : Blo 1975435 1975639 := bstep (se 1 (by rfl) ⟨1481729, by rfl⟩ : syracuseStep 1975639 = 2963459) B2963459
theorem B3750637 : Blo 1975435 3750637 := bbase (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) (by norm_num)
theorem B5000849 : Blo 1975435 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B3333899 : Blo 1975435 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B2222599 : Blo 1975435 2222599 := bstep (se 1 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 2222599 = 3333899) B3333899
theorem B2963465 : Blo 1975435 2963465 := bstep (se 2 (by rfl) ⟨1111299, by rfl⟩ : syracuseStep 2963465 = 2222599) B2222599
theorem B1975643 : Blo 1975435 1975643 := bstep (se 1 (by rfl) ⟨1481732, by rfl⟩ : syracuseStep 1975643 = 2963465) B2963465
theorem B10001717 : Blo 1975435 10001717 := bbase (se 5 (by rfl) ⟨468830, by rfl⟩ : syracuseStep 10001717 = 937661) (by norm_num)
theorem B6667811 : Blo 1975435 6667811 := bstep (se 1 (by rfl) ⟨5000858, by rfl⟩ : syracuseStep 6667811 = 10001717) B10001717
theorem B4445207 : Blo 1975435 4445207 := bstep (se 1 (by rfl) ⟨3333905, by rfl⟩ : syracuseStep 4445207 = 6667811) B6667811
theorem B2963471 : Blo 1975435 2963471 := bstep (se 1 (by rfl) ⟨2222603, by rfl⟩ : syracuseStep 2963471 = 4445207) B4445207
theorem B1975647 : Blo 1975435 1975647 := bstep (se 1 (by rfl) ⟨1481735, by rfl⟩ : syracuseStep 1975647 = 2963471) B2963471
theorem B2963477 : Blo 1975435 2963477 := bbase (se 6 (by rfl) ⟨69456, by rfl⟩ : syracuseStep 2963477 = 138913) (by norm_num)
theorem B1975651 : Blo 1975435 1975651 := bstep (se 1 (by rfl) ⟨1481738, by rfl⟩ : syracuseStep 1975651 = 2963477) B2963477
theorem B3560197 : Blo 1975435 3560197 := bbase (se 4 (by rfl) ⟨333768, by rfl⟩ : syracuseStep 3560197 = 667537) (by norm_num)
theorem B4746929 : Blo 1975435 4746929 := bstep (se 2 (by rfl) ⟨1780098, by rfl⟩ : syracuseStep 4746929 = 3560197) B3560197
theorem B12658477 : Blo 1975435 12658477 := bstep (se 3 (by rfl) ⟨2373464, by rfl⟩ : syracuseStep 12658477 = 4746929) B4746929
theorem B16877969 : Blo 1975435 16877969 := bstep (se 2 (by rfl) ⟨6329238, by rfl⟩ : syracuseStep 16877969 = 12658477) B12658477
theorem B11251979 : Blo 1975435 11251979 := bstep (se 1 (by rfl) ⟨8438984, by rfl⟩ : syracuseStep 11251979 = 16877969) B16877969
theorem B7501319 : Blo 1975435 7501319 := bstep (se 1 (by rfl) ⟨5625989, by rfl⟩ : syracuseStep 7501319 = 11251979) B11251979
theorem B5000879 : Blo 1975435 5000879 := bstep (se 1 (by rfl) ⟨3750659, by rfl⟩ : syracuseStep 5000879 = 7501319) B7501319
theorem B3333919 : Blo 1975435 3333919 := bstep (se 1 (by rfl) ⟨2500439, by rfl⟩ : syracuseStep 3333919 = 5000879) B5000879
theorem B4445225 : Blo 1975435 4445225 := bstep (se 2 (by rfl) ⟨1666959, by rfl⟩ : syracuseStep 4445225 = 3333919) B3333919
theorem B2963483 : Blo 1975435 2963483 := bstep (se 1 (by rfl) ⟨2222612, by rfl⟩ : syracuseStep 2963483 = 4445225) B4445225
theorem B1975655 : Blo 1975435 1975655 := bstep (se 1 (by rfl) ⟨1481741, by rfl⟩ : syracuseStep 1975655 = 2963483) B2963483
theorem B2222617 : Blo 1975435 2222617 := bbase (se 2 (by rfl) ⟨833481, by rfl⟩ : syracuseStep 2222617 = 1666963) (by norm_num)
theorem B2963489 : Blo 1975435 2963489 := bstep (se 2 (by rfl) ⟨1111308, by rfl⟩ : syracuseStep 2963489 = 2222617) B2222617
theorem B1975659 : Blo 1975435 1975659 := bstep (se 1 (by rfl) ⟨1481744, by rfl⟩ : syracuseStep 1975659 = 2963489) B2963489
theorem B7501349 : Blo 1975435 7501349 := bbase (se 4 (by rfl) ⟨703251, by rfl⟩ : syracuseStep 7501349 = 1406503) (by norm_num)
theorem B5000899 : Blo 1975435 5000899 := bstep (se 1 (by rfl) ⟨3750674, by rfl⟩ : syracuseStep 5000899 = 7501349) B7501349
theorem B6667865 : Blo 1975435 6667865 := bstep (se 2 (by rfl) ⟨2500449, by rfl⟩ : syracuseStep 6667865 = 5000899) B5000899
theorem B4445243 : Blo 1975435 4445243 := bstep (se 1 (by rfl) ⟨3333932, by rfl⟩ : syracuseStep 4445243 = 6667865) B6667865
theorem B2963495 : Blo 1975435 2963495 := bstep (se 1 (by rfl) ⟨2222621, by rfl⟩ : syracuseStep 2963495 = 4445243) B4445243
theorem B1975663 : Blo 1975435 1975663 := bstep (se 1 (by rfl) ⟨1481747, by rfl⟩ : syracuseStep 1975663 = 2963495) B2963495
theorem B2963501 : Blo 1975435 2963501 := bbase (se 3 (by rfl) ⟨555656, by rfl⟩ : syracuseStep 2963501 = 1111313) (by norm_num)
theorem B1975667 : Blo 1975435 1975667 := bstep (se 1 (by rfl) ⟨1481750, by rfl⟩ : syracuseStep 1975667 = 2963501) B2963501
theorem B4445261 : Blo 1975435 4445261 := bbase (se 3 (by rfl) ⟨833486, by rfl⟩ : syracuseStep 4445261 = 1666973) (by norm_num)
theorem B2963507 : Blo 1975435 2963507 := bstep (se 1 (by rfl) ⟨2222630, by rfl⟩ : syracuseStep 2963507 = 4445261) B4445261
theorem B1975671 : Blo 1975435 1975671 := bstep (se 1 (by rfl) ⟨1481753, by rfl⟩ : syracuseStep 1975671 = 2963507) B2963507
theorem B2500465 : Blo 1975435 2500465 := bbase (se 2 (by rfl) ⟨937674, by rfl⟩ : syracuseStep 2500465 = 1875349) (by norm_num)
theorem B3333953 : Blo 1975435 3333953 := bstep (se 2 (by rfl) ⟨1250232, by rfl⟩ : syracuseStep 3333953 = 2500465) B2500465
theorem B2222635 : Blo 1975435 2222635 := bstep (se 1 (by rfl) ⟨1666976, by rfl⟩ : syracuseStep 2222635 = 3333953) B3333953
theorem B2963513 : Blo 1975435 2963513 := bstep (se 2 (by rfl) ⟨1111317, by rfl⟩ : syracuseStep 2963513 = 2222635) B2222635
theorem B1975675 : Blo 1975435 1975675 := bstep (se 1 (by rfl) ⟨1481756, by rfl⟩ : syracuseStep 1975675 = 2963513) B2963513
theorem B9493973 : Blo 1975435 9493973 := bbase (se 7 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 9493973 = 222515) (by norm_num)
theorem B6329315 : Blo 1975435 6329315 := bstep (se 1 (by rfl) ⟨4746986, by rfl⟩ : syracuseStep 6329315 = 9493973) B9493973
theorem B4219543 : Blo 1975435 4219543 := bstep (se 1 (by rfl) ⟨3164657, by rfl⟩ : syracuseStep 4219543 = 6329315) B6329315
theorem B22504229 : Blo 1975435 22504229 := bstep (se 4 (by rfl) ⟨2109771, by rfl⟩ : syracuseStep 22504229 = 4219543) B4219543
theorem B15002819 : Blo 1975435 15002819 := bstep (se 1 (by rfl) ⟨11252114, by rfl⟩ : syracuseStep 15002819 = 22504229) B22504229
theorem B10001879 : Blo 1975435 10001879 := bstep (se 1 (by rfl) ⟨7501409, by rfl⟩ : syracuseStep 10001879 = 15002819) B15002819
theorem B6667919 : Blo 1975435 6667919 := bstep (se 1 (by rfl) ⟨5000939, by rfl⟩ : syracuseStep 6667919 = 10001879) B10001879
theorem B4445279 : Blo 1975435 4445279 := bstep (se 1 (by rfl) ⟨3333959, by rfl⟩ : syracuseStep 4445279 = 6667919) B6667919
theorem B2963519 : Blo 1975435 2963519 := bstep (se 1 (by rfl) ⟨2222639, by rfl⟩ : syracuseStep 2963519 = 4445279) B4445279
theorem B1975679 : Blo 1975435 1975679 := bstep (se 1 (by rfl) ⟨1481759, by rfl⟩ : syracuseStep 1975679 = 2963519) B2963519
theorem B2963525 : Blo 1975435 2963525 := bbase (se 4 (by rfl) ⟨277830, by rfl⟩ : syracuseStep 2963525 = 555661) (by norm_num)
theorem B1975683 : Blo 1975435 1975683 := bstep (se 1 (by rfl) ⟨1481762, by rfl⟩ : syracuseStep 1975683 = 2963525) B2963525
theorem B3333973 : Blo 1975435 3333973 := bbase (se 9 (by rfl) ⟨9767, by rfl⟩ : syracuseStep 3333973 = 19535) (by norm_num)
theorem B4445297 : Blo 1975435 4445297 := bstep (se 2 (by rfl) ⟨1666986, by rfl⟩ : syracuseStep 4445297 = 3333973) B3333973
theorem B2963531 : Blo 1975435 2963531 := bstep (se 1 (by rfl) ⟨2222648, by rfl⟩ : syracuseStep 2963531 = 4445297) B4445297
theorem B1975687 : Blo 1975435 1975687 := bstep (se 1 (by rfl) ⟨1481765, by rfl⟩ : syracuseStep 1975687 = 2963531) B2963531
theorem B2222653 : Blo 1975435 2222653 := bbase (se 3 (by rfl) ⟨416747, by rfl⟩ : syracuseStep 2222653 = 833495) (by norm_num)
theorem B2963537 : Blo 1975435 2963537 := bstep (se 2 (by rfl) ⟨1111326, by rfl⟩ : syracuseStep 2963537 = 2222653) B2222653
theorem B1975691 : Blo 1975435 1975691 := bstep (se 1 (by rfl) ⟨1481768, by rfl⟩ : syracuseStep 1975691 = 2963537) B2963537
theorem B6667973 : Blo 1975435 6667973 := bbase (se 4 (by rfl) ⟨625122, by rfl⟩ : syracuseStep 6667973 = 1250245) (by norm_num)
theorem B4445315 : Blo 1975435 4445315 := bstep (se 1 (by rfl) ⟨3333986, by rfl⟩ : syracuseStep 4445315 = 6667973) B6667973
theorem B2963543 : Blo 1975435 2963543 := bstep (se 1 (by rfl) ⟨2222657, by rfl⟩ : syracuseStep 2963543 = 4445315) B4445315
theorem B1975695 : Blo 1975435 1975695 := bstep (se 1 (by rfl) ⟨1481771, by rfl⟩ : syracuseStep 1975695 = 2963543) B2963543
theorem B2963549 : Blo 1975435 2963549 := bbase (se 3 (by rfl) ⟨555665, by rfl⟩ : syracuseStep 2963549 = 1111331) (by norm_num)
theorem B1975699 : Blo 1975435 1975699 := bstep (se 1 (by rfl) ⟨1481774, by rfl⟩ : syracuseStep 1975699 = 2963549) B2963549
theorem B4445333 : Blo 1975435 4445333 := bbase (se 6 (by rfl) ⟨104187, by rfl⟩ : syracuseStep 4445333 = 208375) (by norm_num)
theorem B2963555 : Blo 1975435 2963555 := bstep (se 1 (by rfl) ⟨2222666, by rfl⟩ : syracuseStep 2963555 = 4445333) B4445333
theorem B1975703 : Blo 1975435 1975703 := bstep (se 1 (by rfl) ⟨1481777, by rfl⟩ : syracuseStep 1975703 = 2963555) B2963555
theorem B2813069 : Blo 1975435 2813069 := bbase (se 3 (by rfl) ⟨527450, by rfl⟩ : syracuseStep 2813069 = 1054901) (by norm_num)
theorem B7501517 : Blo 1975435 7501517 := bstep (se 3 (by rfl) ⟨1406534, by rfl⟩ : syracuseStep 7501517 = 2813069) B2813069
theorem B5001011 : Blo 1975435 5001011 := bstep (se 1 (by rfl) ⟨3750758, by rfl⟩ : syracuseStep 5001011 = 7501517) B7501517
theorem B3334007 : Blo 1975435 3334007 := bstep (se 1 (by rfl) ⟨2500505, by rfl⟩ : syracuseStep 3334007 = 5001011) B5001011
theorem B2222671 : Blo 1975435 2222671 := bstep (se 1 (by rfl) ⟨1667003, by rfl⟩ : syracuseStep 2222671 = 3334007) B3334007
theorem B2963561 : Blo 1975435 2963561 := bstep (se 2 (by rfl) ⟨1111335, by rfl⟩ : syracuseStep 2963561 = 2222671) B2222671
theorem B1975707 : Blo 1975435 1975707 := bstep (se 1 (by rfl) ⟨1481780, by rfl⟩ : syracuseStep 1975707 = 2963561) B2963561
theorem B9012005 : Blo 1975435 9012005 := bbase (se 4 (by rfl) ⟨844875, by rfl⟩ : syracuseStep 9012005 = 1689751) (by norm_num)
theorem B6008003 : Blo 1975435 6008003 := bstep (se 1 (by rfl) ⟨4506002, by rfl⟩ : syracuseStep 6008003 = 9012005) B9012005
theorem B4005335 : Blo 1975435 4005335 := bstep (se 1 (by rfl) ⟨3004001, by rfl⟩ : syracuseStep 4005335 = 6008003) B6008003
theorem B10680893 : Blo 1975435 10680893 := bstep (se 3 (by rfl) ⟨2002667, by rfl⟩ : syracuseStep 10680893 = 4005335) B4005335
theorem B7120595 : Blo 1975435 7120595 := bstep (se 1 (by rfl) ⟨5340446, by rfl⟩ : syracuseStep 7120595 = 10680893) B10680893
theorem B18988253 : Blo 1975435 18988253 := bstep (se 3 (by rfl) ⟨3560297, by rfl⟩ : syracuseStep 18988253 = 7120595) B7120595
theorem B12658835 : Blo 1975435 12658835 := bstep (se 1 (by rfl) ⟨9494126, by rfl⟩ : syracuseStep 12658835 = 18988253) B18988253
theorem B8439223 : Blo 1975435 8439223 := bstep (se 1 (by rfl) ⟨6329417, by rfl⟩ : syracuseStep 8439223 = 12658835) B12658835
theorem B11252297 : Blo 1975435 11252297 := bstep (se 2 (by rfl) ⟨4219611, by rfl⟩ : syracuseStep 11252297 = 8439223) B8439223
theorem B7501531 : Blo 1975435 7501531 := bstep (se 1 (by rfl) ⟨5626148, by rfl⟩ : syracuseStep 7501531 = 11252297) B11252297
theorem B10002041 : Blo 1975435 10002041 := bstep (se 2 (by rfl) ⟨3750765, by rfl⟩ : syracuseStep 10002041 = 7501531) B7501531
theorem B6668027 : Blo 1975435 6668027 := bstep (se 1 (by rfl) ⟨5001020, by rfl⟩ : syracuseStep 6668027 = 10002041) B10002041
theorem B4445351 : Blo 1975435 4445351 := bstep (se 1 (by rfl) ⟨3334013, by rfl⟩ : syracuseStep 4445351 = 6668027) B6668027
theorem B2963567 : Blo 1975435 2963567 := bstep (se 1 (by rfl) ⟨2222675, by rfl⟩ : syracuseStep 2963567 = 4445351) B4445351
theorem B1975711 : Blo 1975435 1975711 := bstep (se 1 (by rfl) ⟨1481783, by rfl⟩ : syracuseStep 1975711 = 2963567) B2963567
theorem B2963573 : Blo 1975435 2963573 := bbase (se 5 (by rfl) ⟨138917, by rfl⟩ : syracuseStep 2963573 = 277835) (by norm_num)
theorem B1975715 : Blo 1975435 1975715 := bstep (se 1 (by rfl) ⟨1481786, by rfl⟩ : syracuseStep 1975715 = 2963573) B2963573
theorem B3750781 : Blo 1975435 3750781 := bbase (se 3 (by rfl) ⟨703271, by rfl⟩ : syracuseStep 3750781 = 1406543) (by norm_num)
theorem B5001041 : Blo 1975435 5001041 := bstep (se 2 (by rfl) ⟨1875390, by rfl⟩ : syracuseStep 5001041 = 3750781) B3750781
theorem B3334027 : Blo 1975435 3334027 := bstep (se 1 (by rfl) ⟨2500520, by rfl⟩ : syracuseStep 3334027 = 5001041) B5001041
theorem B4445369 : Blo 1975435 4445369 := bstep (se 2 (by rfl) ⟨1667013, by rfl⟩ : syracuseStep 4445369 = 3334027) B3334027
theorem B2963579 : Blo 1975435 2963579 := bstep (se 1 (by rfl) ⟨2222684, by rfl⟩ : syracuseStep 2963579 = 4445369) B4445369
theorem B1975719 : Blo 1975435 1975719 := bstep (se 1 (by rfl) ⟨1481789, by rfl⟩ : syracuseStep 1975719 = 2963579) B2963579
theorem B2222689 : Blo 1975435 2222689 := bbase (se 2 (by rfl) ⟨833508, by rfl⟩ : syracuseStep 2222689 = 1667017) (by norm_num)
theorem B2963585 : Blo 1975435 2963585 := bstep (se 2 (by rfl) ⟨1111344, by rfl⟩ : syracuseStep 2963585 = 2222689) B2222689
theorem B1975723 : Blo 1975435 1975723 := bstep (se 1 (by rfl) ⟨1481792, by rfl⟩ : syracuseStep 1975723 = 2963585) B2963585
theorem B5001061 : Blo 1975435 5001061 := bbase (se 4 (by rfl) ⟨468849, by rfl⟩ : syracuseStep 5001061 = 937699) (by norm_num)
theorem B6668081 : Blo 1975435 6668081 := bstep (se 2 (by rfl) ⟨2500530, by rfl⟩ : syracuseStep 6668081 = 5001061) B5001061
theorem B4445387 : Blo 1975435 4445387 := bstep (se 1 (by rfl) ⟨3334040, by rfl⟩ : syracuseStep 4445387 = 6668081) B6668081
theorem B2963591 : Blo 1975435 2963591 := bstep (se 1 (by rfl) ⟨2222693, by rfl⟩ : syracuseStep 2963591 = 4445387) B4445387
theorem B1975727 : Blo 1975435 1975727 := bstep (se 1 (by rfl) ⟨1481795, by rfl⟩ : syracuseStep 1975727 = 2963591) B2963591
theorem B2963597 : Blo 1975435 2963597 := bbase (se 3 (by rfl) ⟨555674, by rfl⟩ : syracuseStep 2963597 = 1111349) (by norm_num)
theorem B1975731 : Blo 1975435 1975731 := bstep (se 1 (by rfl) ⟨1481798, by rfl⟩ : syracuseStep 1975731 = 2963597) B2963597
theorem B4445405 : Blo 1975435 4445405 := bbase (se 3 (by rfl) ⟨833513, by rfl⟩ : syracuseStep 4445405 = 1667027) (by norm_num)
theorem B2963603 : Blo 1975435 2963603 := bstep (se 1 (by rfl) ⟨2222702, by rfl⟩ : syracuseStep 2963603 = 4445405) B4445405
theorem B1975735 : Blo 1975435 1975735 := bstep (se 1 (by rfl) ⟨1481801, by rfl⟩ : syracuseStep 1975735 = 2963603) B2963603
theorem B3334061 : Blo 1975435 3334061 := bbase (se 3 (by rfl) ⟨625136, by rfl⟩ : syracuseStep 3334061 = 1250273) (by norm_num)
theorem B2222707 : Blo 1975435 2222707 := bstep (se 1 (by rfl) ⟨1667030, by rfl⟩ : syracuseStep 2222707 = 3334061) B3334061
theorem B2963609 : Blo 1975435 2963609 := bstep (se 2 (by rfl) ⟨1111353, by rfl⟩ : syracuseStep 2963609 = 2222707) B2222707
theorem B1975739 : Blo 1975435 1975739 := bstep (se 1 (by rfl) ⟨1481804, by rfl⟩ : syracuseStep 1975739 = 2963609) B2963609
theorem B2569249 : Blo 1975435 2569249 := bbase (se 2 (by rfl) ⟨963468, by rfl⟩ : syracuseStep 2569249 = 1926937) (by norm_num)
theorem B3425665 : Blo 1975435 3425665 := bstep (se 2 (by rfl) ⟨1284624, by rfl⟩ : syracuseStep 3425665 = 2569249) B2569249
theorem B4567553 : Blo 1975435 4567553 := bstep (se 2 (by rfl) ⟨1712832, by rfl⟩ : syracuseStep 4567553 = 3425665) B3425665
theorem B3045035 : Blo 1975435 3045035 := bstep (se 1 (by rfl) ⟨2283776, by rfl⟩ : syracuseStep 3045035 = 4567553) B4567553
theorem B8120093 : Blo 1975435 8120093 := bstep (se 3 (by rfl) ⟨1522517, by rfl⟩ : syracuseStep 8120093 = 3045035) B3045035
theorem B21653581 : Blo 1975435 21653581 := bstep (se 3 (by rfl) ⟨4060046, by rfl⟩ : syracuseStep 21653581 = 8120093) B8120093
theorem B28871441 : Blo 1975435 28871441 := bstep (se 2 (by rfl) ⟨10826790, by rfl⟩ : syracuseStep 28871441 = 21653581) B21653581
theorem B19247627 : Blo 1975435 19247627 := bstep (se 1 (by rfl) ⟨14435720, by rfl⟩ : syracuseStep 19247627 = 28871441) B28871441
theorem B12831751 : Blo 1975435 12831751 := bstep (se 1 (by rfl) ⟨9623813, by rfl⟩ : syracuseStep 12831751 = 19247627) B19247627
theorem B17109001 : Blo 1975435 17109001 := bstep (se 2 (by rfl) ⟨6415875, by rfl⟩ : syracuseStep 17109001 = 12831751) B12831751
theorem B91248005 : Blo 1975435 91248005 := bstep (se 4 (by rfl) ⟨8554500, by rfl⟩ : syracuseStep 91248005 = 17109001) B17109001
theorem B243328013 : Blo 1975435 243328013 := bstep (se 3 (by rfl) ⟨45624002, by rfl⟩ : syracuseStep 243328013 = 91248005) B91248005
theorem B162218675 : Blo 1975435 162218675 := bstep (se 1 (by rfl) ⟨121664006, by rfl⟩ : syracuseStep 162218675 = 243328013) B243328013
theorem B108145783 : Blo 1975435 108145783 := bstep (se 1 (by rfl) ⟨81109337, by rfl⟩ : syracuseStep 108145783 = 162218675) B162218675
theorem B144194377 : Blo 1975435 144194377 := bstep (se 2 (by rfl) ⟨54072891, by rfl⟩ : syracuseStep 144194377 = 108145783) B108145783
theorem B192259169 : Blo 1975435 192259169 := bstep (se 2 (by rfl) ⟨72097188, by rfl⟩ : syracuseStep 192259169 = 144194377) B144194377
theorem B128172779 : Blo 1975435 128172779 := bstep (se 1 (by rfl) ⟨96129584, by rfl⟩ : syracuseStep 128172779 = 192259169) B192259169
theorem B85448519 : Blo 1975435 85448519 := bstep (se 1 (by rfl) ⟨64086389, by rfl⟩ : syracuseStep 85448519 = 128172779) B128172779
theorem B56965679 : Blo 1975435 56965679 := bstep (se 1 (by rfl) ⟨42724259, by rfl⟩ : syracuseStep 56965679 = 85448519) B85448519
theorem B37977119 : Blo 1975435 37977119 := bstep (se 1 (by rfl) ⟨28482839, by rfl⟩ : syracuseStep 37977119 = 56965679) B56965679
theorem B25318079 : Blo 1975435 25318079 := bstep (se 1 (by rfl) ⟨18988559, by rfl⟩ : syracuseStep 25318079 = 37977119) B37977119
theorem B16878719 : Blo 1975435 16878719 := bstep (se 1 (by rfl) ⟨12659039, by rfl⟩ : syracuseStep 16878719 = 25318079) B25318079
theorem B11252479 : Blo 1975435 11252479 := bstep (se 1 (by rfl) ⟨8439359, by rfl⟩ : syracuseStep 11252479 = 16878719) B16878719
theorem B15003305 : Blo 1975435 15003305 := bstep (se 2 (by rfl) ⟨5626239, by rfl⟩ : syracuseStep 15003305 = 11252479) B11252479
theorem B10002203 : Blo 1975435 10002203 := bstep (se 1 (by rfl) ⟨7501652, by rfl⟩ : syracuseStep 10002203 = 15003305) B15003305
theorem B6668135 : Blo 1975435 6668135 := bstep (se 1 (by rfl) ⟨5001101, by rfl⟩ : syracuseStep 6668135 = 10002203) B10002203
theorem B4445423 : Blo 1975435 4445423 := bstep (se 1 (by rfl) ⟨3334067, by rfl⟩ : syracuseStep 4445423 = 6668135) B6668135
theorem B2963615 : Blo 1975435 2963615 := bstep (se 1 (by rfl) ⟨2222711, by rfl⟩ : syracuseStep 2963615 = 4445423) B4445423
theorem B1975743 : Blo 1975435 1975743 := bstep (se 1 (by rfl) ⟨1481807, by rfl⟩ : syracuseStep 1975743 = 2963615) B2963615
theorem B2963621 : Blo 1975435 2963621 := bbase (se 4 (by rfl) ⟨277839, by rfl⟩ : syracuseStep 2963621 = 555679) (by norm_num)
theorem B1975747 : Blo 1975435 1975747 := bstep (se 1 (by rfl) ⟨1481810, by rfl⟩ : syracuseStep 1975747 = 2963621) B2963621
theorem B2500561 : Blo 1975435 2500561 := bbase (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) (by norm_num)
theorem B3334081 : Blo 1975435 3334081 := bstep (se 2 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 3334081 = 2500561) B2500561
theorem B4445441 : Blo 1975435 4445441 := bstep (se 2 (by rfl) ⟨1667040, by rfl⟩ : syracuseStep 4445441 = 3334081) B3334081
theorem B2963627 : Blo 1975435 2963627 := bstep (se 1 (by rfl) ⟨2222720, by rfl⟩ : syracuseStep 2963627 = 4445441) B4445441
theorem B1975751 : Blo 1975435 1975751 := bstep (se 1 (by rfl) ⟨1481813, by rfl⟩ : syracuseStep 1975751 = 2963627) B2963627
theorem B2222725 : Blo 1975435 2222725 := bbase (se 4 (by rfl) ⟨208380, by rfl⟩ : syracuseStep 2222725 = 416761) (by norm_num)
theorem B2963633 : Blo 1975435 2963633 := bstep (se 2 (by rfl) ⟨1111362, by rfl⟩ : syracuseStep 2963633 = 2222725) B2222725
theorem B1975755 : Blo 1975435 1975755 := bstep (se 1 (by rfl) ⟨1481816, by rfl⟩ : syracuseStep 1975755 = 2963633) B2963633
theorem B6329573 : Blo 1975435 6329573 := bbase (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) (by norm_num)
theorem B4219715 : Blo 1975435 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B2813143 : Blo 1975435 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B3750857 : Blo 1975435 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B2500571 : Blo 1975435 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B6668189 : Blo 1975435 6668189 := bstep (se 3 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 6668189 = 2500571) B2500571
theorem B4445459 : Blo 1975435 4445459 := bstep (se 1 (by rfl) ⟨3334094, by rfl⟩ : syracuseStep 4445459 = 6668189) B6668189
theorem B2963639 : Blo 1975435 2963639 := bstep (se 1 (by rfl) ⟨2222729, by rfl⟩ : syracuseStep 2963639 = 4445459) B4445459
theorem B1975759 : Blo 1975435 1975759 := bstep (se 1 (by rfl) ⟨1481819, by rfl⟩ : syracuseStep 1975759 = 2963639) B2963639
theorem B2963645 : Blo 1975435 2963645 := bbase (se 3 (by rfl) ⟨555683, by rfl⟩ : syracuseStep 2963645 = 1111367) (by norm_num)
theorem B1975763 : Blo 1975435 1975763 := bstep (se 1 (by rfl) ⟨1481822, by rfl⟩ : syracuseStep 1975763 = 2963645) B2963645
theorem B4445477 : Blo 1975435 4445477 := bbase (se 4 (by rfl) ⟨416763, by rfl⟩ : syracuseStep 4445477 = 833527) (by norm_num)
theorem B2963651 : Blo 1975435 2963651 := bstep (se 1 (by rfl) ⟨2222738, by rfl⟩ : syracuseStep 2963651 = 4445477) B4445477
theorem B1975767 : Blo 1975435 1975767 := bstep (se 1 (by rfl) ⟨1481825, by rfl⟩ : syracuseStep 1975767 = 2963651) B2963651
theorem B5001173 : Blo 1975435 5001173 := bbase (se 7 (by rfl) ⟨58607, by rfl⟩ : syracuseStep 5001173 = 117215) (by norm_num)
theorem B3334115 : Blo 1975435 3334115 := bstep (se 1 (by rfl) ⟨2500586, by rfl⟩ : syracuseStep 3334115 = 5001173) B5001173
theorem B2222743 : Blo 1975435 2222743 := bstep (se 1 (by rfl) ⟨1667057, by rfl⟩ : syracuseStep 2222743 = 3334115) B3334115
theorem B2963657 : Blo 1975435 2963657 := bstep (se 2 (by rfl) ⟨1111371, by rfl⟩ : syracuseStep 2963657 = 2222743) B2222743
theorem B1975771 : Blo 1975435 1975771 := bstep (se 1 (by rfl) ⟨1481828, by rfl⟩ : syracuseStep 1975771 = 2963657) B2963657
theorem B14241653 : Blo 1975435 14241653 := bbase (se 5 (by rfl) ⟨667577, by rfl⟩ : syracuseStep 14241653 = 1335155) (by norm_num)
theorem B9494435 : Blo 1975435 9494435 := bstep (se 1 (by rfl) ⟨7120826, by rfl⟩ : syracuseStep 9494435 = 14241653) B14241653
theorem B6329623 : Blo 1975435 6329623 := bstep (se 1 (by rfl) ⟨4747217, by rfl⟩ : syracuseStep 6329623 = 9494435) B9494435
theorem B8439497 : Blo 1975435 8439497 := bstep (se 2 (by rfl) ⟨3164811, by rfl⟩ : syracuseStep 8439497 = 6329623) B6329623
theorem B5626331 : Blo 1975435 5626331 := bstep (se 1 (by rfl) ⟨4219748, by rfl⟩ : syracuseStep 5626331 = 8439497) B8439497
theorem B3750887 : Blo 1975435 3750887 := bstep (se 1 (by rfl) ⟨2813165, by rfl⟩ : syracuseStep 3750887 = 5626331) B5626331
theorem B10002365 : Blo 1975435 10002365 := bstep (se 3 (by rfl) ⟨1875443, by rfl⟩ : syracuseStep 10002365 = 3750887) B3750887
theorem B6668243 : Blo 1975435 6668243 := bstep (se 1 (by rfl) ⟨5001182, by rfl⟩ : syracuseStep 6668243 = 10002365) B10002365
theorem B4445495 : Blo 1975435 4445495 := bstep (se 1 (by rfl) ⟨3334121, by rfl⟩ : syracuseStep 4445495 = 6668243) B6668243
theorem B2963663 : Blo 1975435 2963663 := bstep (se 1 (by rfl) ⟨2222747, by rfl⟩ : syracuseStep 2963663 = 4445495) B4445495
theorem B1975775 : Blo 1975435 1975775 := bstep (se 1 (by rfl) ⟨1481831, by rfl⟩ : syracuseStep 1975775 = 2963663) B2963663
theorem B2963669 : Blo 1975435 2963669 := bbase (se 7 (by rfl) ⟨34730, by rfl⟩ : syracuseStep 2963669 = 69461) (by norm_num)
theorem B1975779 : Blo 1975435 1975779 := bstep (se 1 (by rfl) ⟨1481834, by rfl⟩ : syracuseStep 1975779 = 2963669) B2963669
theorem B3560429 : Blo 1975435 3560429 := bbase (se 3 (by rfl) ⟨667580, by rfl⟩ : syracuseStep 3560429 = 1335161) (by norm_num)
theorem B2373619 : Blo 1975435 2373619 := bstep (se 1 (by rfl) ⟨1780214, by rfl⟩ : syracuseStep 2373619 = 3560429) B3560429
theorem B3164825 : Blo 1975435 3164825 := bstep (se 2 (by rfl) ⟨1186809, by rfl⟩ : syracuseStep 3164825 = 2373619) B2373619
theorem B2109883 : Blo 1975435 2109883 := bstep (se 1 (by rfl) ⟨1582412, by rfl⟩ : syracuseStep 2109883 = 3164825) B3164825
theorem B2813177 : Blo 1975435 2813177 := bstep (se 2 (by rfl) ⟨1054941, by rfl⟩ : syracuseStep 2813177 = 2109883) B2109883
theorem B7501805 : Blo 1975435 7501805 := bstep (se 3 (by rfl) ⟨1406588, by rfl⟩ : syracuseStep 7501805 = 2813177) B2813177
theorem B5001203 : Blo 1975435 5001203 := bstep (se 1 (by rfl) ⟨3750902, by rfl⟩ : syracuseStep 5001203 = 7501805) B7501805
theorem B3334135 : Blo 1975435 3334135 := bstep (se 1 (by rfl) ⟨2500601, by rfl⟩ : syracuseStep 3334135 = 5001203) B5001203
theorem B4445513 : Blo 1975435 4445513 := bstep (se 2 (by rfl) ⟨1667067, by rfl⟩ : syracuseStep 4445513 = 3334135) B3334135
theorem B2963675 : Blo 1975435 2963675 := bstep (se 1 (by rfl) ⟨2222756, by rfl⟩ : syracuseStep 2963675 = 4445513) B4445513
theorem B1975783 : Blo 1975435 1975783 := bstep (se 1 (by rfl) ⟨1481837, by rfl⟩ : syracuseStep 1975783 = 2963675) B2963675
theorem B2222761 : Blo 1975435 2222761 := bbase (se 2 (by rfl) ⟨833535, by rfl⟩ : syracuseStep 2222761 = 1667071) (by norm_num)
theorem B2963681 : Blo 1975435 2963681 := bstep (se 2 (by rfl) ⟨1111380, by rfl⟩ : syracuseStep 2963681 = 2222761) B2222761
theorem B1975787 : Blo 1975435 1975787 := bstep (se 1 (by rfl) ⟨1481840, by rfl⟩ : syracuseStep 1975787 = 2963681) B2963681
theorem B3164837 : Blo 1975435 3164837 := bbase (se 4 (by rfl) ⟨296703, by rfl⟩ : syracuseStep 3164837 = 593407) (by norm_num)
theorem B8439565 : Blo 1975435 8439565 := bstep (se 3 (by rfl) ⟨1582418, by rfl⟩ : syracuseStep 8439565 = 3164837) B3164837
theorem B11252753 : Blo 1975435 11252753 := bstep (se 2 (by rfl) ⟨4219782, by rfl⟩ : syracuseStep 11252753 = 8439565) B8439565
theorem B7501835 : Blo 1975435 7501835 := bstep (se 1 (by rfl) ⟨5626376, by rfl⟩ : syracuseStep 7501835 = 11252753) B11252753
theorem B5001223 : Blo 1975435 5001223 := bstep (se 1 (by rfl) ⟨3750917, by rfl⟩ : syracuseStep 5001223 = 7501835) B7501835
theorem B6668297 : Blo 1975435 6668297 := bstep (se 2 (by rfl) ⟨2500611, by rfl⟩ : syracuseStep 6668297 = 5001223) B5001223
theorem B4445531 : Blo 1975435 4445531 := bstep (se 1 (by rfl) ⟨3334148, by rfl⟩ : syracuseStep 4445531 = 6668297) B6668297
theorem B2963687 : Blo 1975435 2963687 := bstep (se 1 (by rfl) ⟨2222765, by rfl⟩ : syracuseStep 2963687 = 4445531) B4445531
theorem B1975791 : Blo 1975435 1975791 := bstep (se 1 (by rfl) ⟨1481843, by rfl⟩ : syracuseStep 1975791 = 2963687) B2963687
theorem B2963693 : Blo 1975435 2963693 := bbase (se 3 (by rfl) ⟨555692, by rfl⟩ : syracuseStep 2963693 = 1111385) (by norm_num)
theorem B1975795 : Blo 1975435 1975795 := bstep (se 1 (by rfl) ⟨1481846, by rfl⟩ : syracuseStep 1975795 = 2963693) B2963693
theorem B4445549 : Blo 1975435 4445549 := bbase (se 3 (by rfl) ⟨833540, by rfl⟩ : syracuseStep 4445549 = 1667081) (by norm_num)
theorem B2963699 : Blo 1975435 2963699 := bstep (se 1 (by rfl) ⟨2222774, by rfl⟩ : syracuseStep 2963699 = 4445549) B4445549
theorem B1975799 : Blo 1975435 1975799 := bstep (se 1 (by rfl) ⟨1481849, by rfl⟩ : syracuseStep 1975799 = 2963699) B2963699
theorem B3750941 : Blo 1975435 3750941 := bbase (se 3 (by rfl) ⟨703301, by rfl⟩ : syracuseStep 3750941 = 1406603) (by norm_num)
theorem B2500627 : Blo 1975435 2500627 := bstep (se 1 (by rfl) ⟨1875470, by rfl⟩ : syracuseStep 2500627 = 3750941) B3750941
theorem B3334169 : Blo 1975435 3334169 := bstep (se 2 (by rfl) ⟨1250313, by rfl⟩ : syracuseStep 3334169 = 2500627) B2500627
theorem B2222779 : Blo 1975435 2222779 := bstep (se 1 (by rfl) ⟨1667084, by rfl⟩ : syracuseStep 2222779 = 3334169) B3334169
theorem B2963705 : Blo 1975435 2963705 := bstep (se 2 (by rfl) ⟨1111389, by rfl⟩ : syracuseStep 2963705 = 2222779) B2222779
theorem B1975803 : Blo 1975435 1975803 := bstep (se 1 (by rfl) ⟨1481852, by rfl⟩ : syracuseStep 1975803 = 2963705) B2963705
theorem B4506221 : Blo 1975435 4506221 := bbase (se 3 (by rfl) ⟨844916, by rfl⟩ : syracuseStep 4506221 = 1689833) (by norm_num)
theorem B3004147 : Blo 1975435 3004147 := bstep (se 1 (by rfl) ⟨2253110, by rfl⟩ : syracuseStep 3004147 = 4506221) B4506221
theorem B16022117 : Blo 1975435 16022117 := bstep (se 4 (by rfl) ⟨1502073, by rfl⟩ : syracuseStep 16022117 = 3004147) B3004147
theorem B10681411 : Blo 1975435 10681411 := bstep (se 1 (by rfl) ⟨8011058, by rfl⟩ : syracuseStep 10681411 = 16022117) B16022117
theorem B14241881 : Blo 1975435 14241881 := bstep (se 2 (by rfl) ⟨5340705, by rfl⟩ : syracuseStep 14241881 = 10681411) B10681411
theorem B9494587 : Blo 1975435 9494587 := bstep (se 1 (by rfl) ⟨7120940, by rfl⟩ : syracuseStep 9494587 = 14241881) B14241881
theorem B50637797 : Blo 1975435 50637797 := bstep (se 4 (by rfl) ⟨4747293, by rfl⟩ : syracuseStep 50637797 = 9494587) B9494587
theorem B33758531 : Blo 1975435 33758531 := bstep (se 1 (by rfl) ⟨25318898, by rfl⟩ : syracuseStep 33758531 = 50637797) B50637797
theorem B22505687 : Blo 1975435 22505687 := bstep (se 1 (by rfl) ⟨16879265, by rfl⟩ : syracuseStep 22505687 = 33758531) B33758531
theorem B15003791 : Blo 1975435 15003791 := bstep (se 1 (by rfl) ⟨11252843, by rfl⟩ : syracuseStep 15003791 = 22505687) B22505687
theorem B10002527 : Blo 1975435 10002527 := bstep (se 1 (by rfl) ⟨7501895, by rfl⟩ : syracuseStep 10002527 = 15003791) B15003791
theorem B6668351 : Blo 1975435 6668351 := bstep (se 1 (by rfl) ⟨5001263, by rfl⟩ : syracuseStep 6668351 = 10002527) B10002527
theorem B4445567 : Blo 1975435 4445567 := bstep (se 1 (by rfl) ⟨3334175, by rfl⟩ : syracuseStep 4445567 = 6668351) B6668351
theorem B2963711 : Blo 1975435 2963711 := bstep (se 1 (by rfl) ⟨2222783, by rfl⟩ : syracuseStep 2963711 = 4445567) B4445567
theorem B1975807 : Blo 1975435 1975807 := bstep (se 1 (by rfl) ⟨1481855, by rfl⟩ : syracuseStep 1975807 = 2963711) B2963711
theorem B2963717 : Blo 1975435 2963717 := bbase (se 4 (by rfl) ⟨277848, by rfl⟩ : syracuseStep 2963717 = 555697) (by norm_num)
theorem B1975811 : Blo 1975435 1975811 := bstep (se 1 (by rfl) ⟨1481858, by rfl⟩ : syracuseStep 1975811 = 2963717) B2963717
theorem B3334189 : Blo 1975435 3334189 := bbase (se 3 (by rfl) ⟨625160, by rfl⟩ : syracuseStep 3334189 = 1250321) (by norm_num)
theorem B4445585 : Blo 1975435 4445585 := bstep (se 2 (by rfl) ⟨1667094, by rfl⟩ : syracuseStep 4445585 = 3334189) B3334189
theorem B2963723 : Blo 1975435 2963723 := bstep (se 1 (by rfl) ⟨2222792, by rfl⟩ : syracuseStep 2963723 = 4445585) B4445585
theorem B1975815 : Blo 1975435 1975815 := bstep (se 1 (by rfl) ⟨1481861, by rfl⟩ : syracuseStep 1975815 = 2963723) B2963723
theorem B2222797 : Blo 1975435 2222797 := bbase (se 3 (by rfl) ⟨416774, by rfl⟩ : syracuseStep 2222797 = 833549) (by norm_num)
theorem B2963729 : Blo 1975435 2963729 := bstep (se 2 (by rfl) ⟨1111398, by rfl⟩ : syracuseStep 2963729 = 2222797) B2222797
theorem B1975819 : Blo 1975435 1975819 := bstep (se 1 (by rfl) ⟨1481864, by rfl⟩ : syracuseStep 1975819 = 2963729) B2963729
theorem B6668405 : Blo 1975435 6668405 := bbase (se 5 (by rfl) ⟨312581, by rfl⟩ : syracuseStep 6668405 = 625163) (by norm_num)
theorem B4445603 : Blo 1975435 4445603 := bstep (se 1 (by rfl) ⟨3334202, by rfl⟩ : syracuseStep 4445603 = 6668405) B6668405
theorem B2963735 : Blo 1975435 2963735 := bstep (se 1 (by rfl) ⟨2222801, by rfl⟩ : syracuseStep 2963735 = 4445603) B4445603
theorem B1975823 : Blo 1975435 1975823 := bstep (se 1 (by rfl) ⟨1481867, by rfl⟩ : syracuseStep 1975823 = 2963735) B2963735
theorem B2963741 : Blo 1975435 2963741 := bbase (se 3 (by rfl) ⟨555701, by rfl⟩ : syracuseStep 2963741 = 1111403) (by norm_num)
theorem B1975827 : Blo 1975435 1975827 := bstep (se 1 (by rfl) ⟨1481870, by rfl⟩ : syracuseStep 1975827 = 2963741) B2963741
theorem B4445621 : Blo 1975435 4445621 := bbase (se 5 (by rfl) ⟨208388, by rfl⟩ : syracuseStep 4445621 = 416777) (by norm_num)
theorem B2963747 : Blo 1975435 2963747 := bstep (se 1 (by rfl) ⟨2222810, by rfl⟩ : syracuseStep 2963747 = 4445621) B4445621
theorem B1975831 : Blo 1975435 1975831 := bstep (se 1 (by rfl) ⟨1481873, by rfl⟩ : syracuseStep 1975831 = 2963747) B2963747
theorem B4219877 : Blo 1975435 4219877 := bbase (se 4 (by rfl) ⟨395613, by rfl⟩ : syracuseStep 4219877 = 791227) (by norm_num)
theorem B11253005 : Blo 1975435 11253005 := bstep (se 3 (by rfl) ⟨2109938, by rfl⟩ : syracuseStep 11253005 = 4219877) B4219877
theorem B7502003 : Blo 1975435 7502003 := bstep (se 1 (by rfl) ⟨5626502, by rfl⟩ : syracuseStep 7502003 = 11253005) B11253005
theorem B5001335 : Blo 1975435 5001335 := bstep (se 1 (by rfl) ⟨3751001, by rfl⟩ : syracuseStep 5001335 = 7502003) B7502003
theorem B3334223 : Blo 1975435 3334223 := bstep (se 1 (by rfl) ⟨2500667, by rfl⟩ : syracuseStep 3334223 = 5001335) B5001335
theorem B2222815 : Blo 1975435 2222815 := bstep (se 1 (by rfl) ⟨1667111, by rfl⟩ : syracuseStep 2222815 = 3334223) B3334223
theorem B2963753 : Blo 1975435 2963753 := bstep (se 2 (by rfl) ⟨1111407, by rfl⟩ : syracuseStep 2963753 = 2222815) B2222815
theorem B1975835 : Blo 1975435 1975835 := bstep (se 1 (by rfl) ⟨1481876, by rfl⟩ : syracuseStep 1975835 = 2963753) B2963753
theorem B4219885 : Blo 1975435 4219885 := bbase (se 3 (by rfl) ⟨791228, by rfl⟩ : syracuseStep 4219885 = 1582457) (by norm_num)
theorem B5626513 : Blo 1975435 5626513 := bstep (se 2 (by rfl) ⟨2109942, by rfl⟩ : syracuseStep 5626513 = 4219885) B4219885
theorem B7502017 : Blo 1975435 7502017 := bstep (se 2 (by rfl) ⟨2813256, by rfl⟩ : syracuseStep 7502017 = 5626513) B5626513
theorem B10002689 : Blo 1975435 10002689 := bstep (se 2 (by rfl) ⟨3751008, by rfl⟩ : syracuseStep 10002689 = 7502017) B7502017
theorem B6668459 : Blo 1975435 6668459 := bstep (se 1 (by rfl) ⟨5001344, by rfl⟩ : syracuseStep 6668459 = 10002689) B10002689
theorem B4445639 : Blo 1975435 4445639 := bstep (se 1 (by rfl) ⟨3334229, by rfl⟩ : syracuseStep 4445639 = 6668459) B6668459
theorem B2963759 : Blo 1975435 2963759 := bstep (se 1 (by rfl) ⟨2222819, by rfl⟩ : syracuseStep 2963759 = 4445639) B4445639
theorem B1975839 : Blo 1975435 1975839 := bstep (se 1 (by rfl) ⟨1481879, by rfl⟩ : syracuseStep 1975839 = 2963759) B2963759
theorem B2963765 : Blo 1975435 2963765 := bbase (se 5 (by rfl) ⟨138926, by rfl⟩ : syracuseStep 2963765 = 277853) (by norm_num)
theorem B1975843 : Blo 1975435 1975843 := bstep (se 1 (by rfl) ⟨1481882, by rfl⟩ : syracuseStep 1975843 = 2963765) B2963765
theorem B5001365 : Blo 1975435 5001365 := bbase (se 6 (by rfl) ⟨117219, by rfl⟩ : syracuseStep 5001365 = 234439) (by norm_num)
theorem B3334243 : Blo 1975435 3334243 := bstep (se 1 (by rfl) ⟨2500682, by rfl⟩ : syracuseStep 3334243 = 5001365) B5001365
theorem B4445657 : Blo 1975435 4445657 := bstep (se 2 (by rfl) ⟨1667121, by rfl⟩ : syracuseStep 4445657 = 3334243) B3334243
theorem B2963771 : Blo 1975435 2963771 := bstep (se 1 (by rfl) ⟨2222828, by rfl⟩ : syracuseStep 2963771 = 4445657) B4445657
theorem B1975847 : Blo 1975435 1975847 := bstep (se 1 (by rfl) ⟨1481885, by rfl⟩ : syracuseStep 1975847 = 2963771) B2963771
theorem B2222833 : Blo 1975435 2222833 := bbase (se 2 (by rfl) ⟨833562, by rfl⟩ : syracuseStep 2222833 = 1667125) (by norm_num)
theorem B2963777 : Blo 1975435 2963777 := bstep (se 2 (by rfl) ⟨1111416, by rfl⟩ : syracuseStep 2963777 = 2222833) B2222833
theorem B1975851 : Blo 1975435 1975851 := bstep (se 1 (by rfl) ⟨1481888, by rfl⟩ : syracuseStep 1975851 = 2963777) B2963777
theorem B36050645 : Blo 1975435 36050645 := bbase (se 7 (by rfl) ⟨422468, by rfl⟩ : syracuseStep 36050645 = 844937) (by norm_num)
theorem B24033763 : Blo 1975435 24033763 := bstep (se 1 (by rfl) ⟨18025322, by rfl⟩ : syracuseStep 24033763 = 36050645) B36050645
theorem B32045017 : Blo 1975435 32045017 := bstep (se 2 (by rfl) ⟨12016881, by rfl⟩ : syracuseStep 32045017 = 24033763) B24033763
theorem B42726689 : Blo 1975435 42726689 := bstep (se 2 (by rfl) ⟨16022508, by rfl⟩ : syracuseStep 42726689 = 32045017) B32045017
theorem B28484459 : Blo 1975435 28484459 := bstep (se 1 (by rfl) ⟨21363344, by rfl⟩ : syracuseStep 28484459 = 42726689) B42726689
theorem B18989639 : Blo 1975435 18989639 := bstep (se 1 (by rfl) ⟨14242229, by rfl⟩ : syracuseStep 18989639 = 28484459) B28484459
theorem B12659759 : Blo 1975435 12659759 := bstep (se 1 (by rfl) ⟨9494819, by rfl⟩ : syracuseStep 12659759 = 18989639) B18989639
theorem B8439839 : Blo 1975435 8439839 := bstep (se 1 (by rfl) ⟨6329879, by rfl⟩ : syracuseStep 8439839 = 12659759) B12659759
theorem B5626559 : Blo 1975435 5626559 := bstep (se 1 (by rfl) ⟨4219919, by rfl⟩ : syracuseStep 5626559 = 8439839) B8439839
theorem B3751039 : Blo 1975435 3751039 := bstep (se 1 (by rfl) ⟨2813279, by rfl⟩ : syracuseStep 3751039 = 5626559) B5626559
theorem B5001385 : Blo 1975435 5001385 := bstep (se 2 (by rfl) ⟨1875519, by rfl⟩ : syracuseStep 5001385 = 3751039) B3751039
theorem B6668513 : Blo 1975435 6668513 := bstep (se 2 (by rfl) ⟨2500692, by rfl⟩ : syracuseStep 6668513 = 5001385) B5001385
theorem B4445675 : Blo 1975435 4445675 := bstep (se 1 (by rfl) ⟨3334256, by rfl⟩ : syracuseStep 4445675 = 6668513) B6668513
theorem B2963783 : Blo 1975435 2963783 := bstep (se 1 (by rfl) ⟨2222837, by rfl⟩ : syracuseStep 2963783 = 4445675) B4445675
theorem B1975855 : Blo 1975435 1975855 := bstep (se 1 (by rfl) ⟨1481891, by rfl⟩ : syracuseStep 1975855 = 2963783) B2963783
theorem B2963789 : Blo 1975435 2963789 := bbase (se 3 (by rfl) ⟨555710, by rfl⟩ : syracuseStep 2963789 = 1111421) (by norm_num)
theorem B1975859 : Blo 1975435 1975859 := bstep (se 1 (by rfl) ⟨1481894, by rfl⟩ : syracuseStep 1975859 = 2963789) B2963789
theorem B4445693 : Blo 1975435 4445693 := bbase (se 3 (by rfl) ⟨833567, by rfl⟩ : syracuseStep 4445693 = 1667135) (by norm_num)
theorem B2963795 : Blo 1975435 2963795 := bstep (se 1 (by rfl) ⟨2222846, by rfl⟩ : syracuseStep 2963795 = 4445693) B4445693
theorem B1975863 : Blo 1975435 1975863 := bstep (se 1 (by rfl) ⟨1481897, by rfl⟩ : syracuseStep 1975863 = 2963795) B2963795
theorem B3334277 : Blo 1975435 3334277 := bbase (se 4 (by rfl) ⟨312588, by rfl⟩ : syracuseStep 3334277 = 625177) (by norm_num)
theorem B2222851 : Blo 1975435 2222851 := bstep (se 1 (by rfl) ⟨1667138, by rfl⟩ : syracuseStep 2222851 = 3334277) B3334277
theorem B2963801 : Blo 1975435 2963801 := bstep (se 2 (by rfl) ⟨1111425, by rfl⟩ : syracuseStep 2963801 = 2222851) B2222851
theorem B1975867 : Blo 1975435 1975867 := bstep (se 1 (by rfl) ⟨1481900, by rfl⟩ : syracuseStep 1975867 = 2963801) B2963801
theorem B15004277 : Blo 1975435 15004277 := bbase (se 5 (by rfl) ⟨703325, by rfl⟩ : syracuseStep 15004277 = 1406651) (by norm_num)
theorem B10002851 : Blo 1975435 10002851 := bstep (se 1 (by rfl) ⟨7502138, by rfl⟩ : syracuseStep 10002851 = 15004277) B15004277
theorem B6668567 : Blo 1975435 6668567 := bstep (se 1 (by rfl) ⟨5001425, by rfl⟩ : syracuseStep 6668567 = 10002851) B10002851
theorem B4445711 : Blo 1975435 4445711 := bstep (se 1 (by rfl) ⟨3334283, by rfl⟩ : syracuseStep 4445711 = 6668567) B6668567
theorem B2963807 : Blo 1975435 2963807 := bstep (se 1 (by rfl) ⟨2222855, by rfl⟩ : syracuseStep 2963807 = 4445711) B4445711
theorem B1975871 : Blo 1975435 1975871 := bstep (se 1 (by rfl) ⟨1481903, by rfl⟩ : syracuseStep 1975871 = 2963807) B2963807
theorem B2963813 : Blo 1975435 2963813 := bbase (se 4 (by rfl) ⟨277857, by rfl⟩ : syracuseStep 2963813 = 555715) (by norm_num)
theorem B1975875 : Blo 1975435 1975875 := bstep (se 1 (by rfl) ⟨1481906, by rfl⟩ : syracuseStep 1975875 = 2963813) B2963813
theorem B3751085 : Blo 1975435 3751085 := bbase (se 3 (by rfl) ⟨703328, by rfl⟩ : syracuseStep 3751085 = 1406657) (by norm_num)
theorem B2500723 : Blo 1975435 2500723 := bstep (se 1 (by rfl) ⟨1875542, by rfl⟩ : syracuseStep 2500723 = 3751085) B3751085
theorem B3334297 : Blo 1975435 3334297 := bstep (se 2 (by rfl) ⟨1250361, by rfl⟩ : syracuseStep 3334297 = 2500723) B2500723
theorem B4445729 : Blo 1975435 4445729 := bstep (se 2 (by rfl) ⟨1667148, by rfl⟩ : syracuseStep 4445729 = 3334297) B3334297
theorem B2963819 : Blo 1975435 2963819 := bstep (se 1 (by rfl) ⟨2222864, by rfl⟩ : syracuseStep 2963819 = 4445729) B4445729
theorem B1975879 : Blo 1975435 1975879 := bstep (se 1 (by rfl) ⟨1481909, by rfl⟩ : syracuseStep 1975879 = 2963819) B2963819
theorem B2222869 : Blo 1975435 2222869 := bbase (se 6 (by rfl) ⟨52098, by rfl⟩ : syracuseStep 2222869 = 104197) (by norm_num)
theorem B2963825 : Blo 1975435 2963825 := bstep (se 2 (by rfl) ⟨1111434, by rfl⟩ : syracuseStep 2963825 = 2222869) B2222869
theorem B1975883 : Blo 1975435 1975883 := bstep (se 1 (by rfl) ⟨1481912, by rfl⟩ : syracuseStep 1975883 = 2963825) B2963825
theorem B2500733 : Blo 1975435 2500733 := bbase (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) (by norm_num)
theorem B6668621 : Blo 1975435 6668621 := bstep (se 3 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 6668621 = 2500733) B2500733
theorem B4445747 : Blo 1975435 4445747 := bstep (se 1 (by rfl) ⟨3334310, by rfl⟩ : syracuseStep 4445747 = 6668621) B6668621
theorem B2963831 : Blo 1975435 2963831 := bstep (se 1 (by rfl) ⟨2222873, by rfl⟩ : syracuseStep 2963831 = 4445747) B4445747
theorem B1975887 : Blo 1975435 1975887 := bstep (se 1 (by rfl) ⟨1481915, by rfl⟩ : syracuseStep 1975887 = 2963831) B2963831
theorem B2963837 : Blo 1975435 2963837 := bbase (se 3 (by rfl) ⟨555719, by rfl⟩ : syracuseStep 2963837 = 1111439) (by norm_num)
theorem B1975891 : Blo 1975435 1975891 := bstep (se 1 (by rfl) ⟨1481918, by rfl⟩ : syracuseStep 1975891 = 2963837) B2963837
theorem B4445765 : Blo 1975435 4445765 := bbase (se 4 (by rfl) ⟨416790, by rfl⟩ : syracuseStep 4445765 = 833581) (by norm_num)
theorem B2963843 : Blo 1975435 2963843 := bstep (se 1 (by rfl) ⟨2222882, by rfl⟩ : syracuseStep 2963843 = 4445765) B4445765
theorem B1975895 : Blo 1975435 1975895 := bstep (se 1 (by rfl) ⟨1481921, by rfl⟩ : syracuseStep 1975895 = 2963843) B2963843
theorem B4747517 : Blo 1975435 4747517 := bbase (se 3 (by rfl) ⟨890159, by rfl⟩ : syracuseStep 4747517 = 1780319) (by norm_num)
theorem B3165011 : Blo 1975435 3165011 := bstep (se 1 (by rfl) ⟨2373758, by rfl⟩ : syracuseStep 3165011 = 4747517) B4747517
theorem B2110007 : Blo 1975435 2110007 := bstep (se 1 (by rfl) ⟨1582505, by rfl⟩ : syracuseStep 2110007 = 3165011) B3165011
theorem B5626685 : Blo 1975435 5626685 := bstep (se 3 (by rfl) ⟨1055003, by rfl⟩ : syracuseStep 5626685 = 2110007) B2110007
theorem B3751123 : Blo 1975435 3751123 := bstep (se 1 (by rfl) ⟨2813342, by rfl⟩ : syracuseStep 3751123 = 5626685) B5626685
theorem B5001497 : Blo 1975435 5001497 := bstep (se 2 (by rfl) ⟨1875561, by rfl⟩ : syracuseStep 5001497 = 3751123) B3751123
theorem B3334331 : Blo 1975435 3334331 := bstep (se 1 (by rfl) ⟨2500748, by rfl⟩ : syracuseStep 3334331 = 5001497) B5001497
theorem B2222887 : Blo 1975435 2222887 := bstep (se 1 (by rfl) ⟨1667165, by rfl⟩ : syracuseStep 2222887 = 3334331) B3334331
theorem B2963849 : Blo 1975435 2963849 := bstep (se 2 (by rfl) ⟨1111443, by rfl⟩ : syracuseStep 2963849 = 2222887) B2222887
theorem B1975899 : Blo 1975435 1975899 := bstep (se 1 (by rfl) ⟨1481924, by rfl⟩ : syracuseStep 1975899 = 2963849) B2963849
theorem B10003013 : Blo 1975435 10003013 := bbase (se 4 (by rfl) ⟨937782, by rfl⟩ : syracuseStep 10003013 = 1875565) (by norm_num)
theorem B6668675 : Blo 1975435 6668675 := bstep (se 1 (by rfl) ⟨5001506, by rfl⟩ : syracuseStep 6668675 = 10003013) B10003013
theorem B4445783 : Blo 1975435 4445783 := bstep (se 1 (by rfl) ⟨3334337, by rfl⟩ : syracuseStep 4445783 = 6668675) B6668675
theorem B2963855 : Blo 1975435 2963855 := bstep (se 1 (by rfl) ⟨2222891, by rfl⟩ : syracuseStep 2963855 = 4445783) B4445783
theorem B1975903 : Blo 1975435 1975903 := bstep (se 1 (by rfl) ⟨1481927, by rfl⟩ : syracuseStep 1975903 = 2963855) B2963855
theorem B2963861 : Blo 1975435 2963861 := bbase (se 6 (by rfl) ⟨69465, by rfl⟩ : syracuseStep 2963861 = 138931) (by norm_num)
theorem B1975907 : Blo 1975435 1975907 := bstep (se 1 (by rfl) ⟨1481930, by rfl⟩ : syracuseStep 1975907 = 2963861) B2963861
theorem B7121317 : Blo 1975435 7121317 := bbase (se 4 (by rfl) ⟨667623, by rfl⟩ : syracuseStep 7121317 = 1335247) (by norm_num)
theorem B9495089 : Blo 1975435 9495089 := bstep (se 2 (by rfl) ⟨3560658, by rfl⟩ : syracuseStep 9495089 = 7121317) B7121317
theorem B6330059 : Blo 1975435 6330059 := bstep (se 1 (by rfl) ⟨4747544, by rfl⟩ : syracuseStep 6330059 = 9495089) B9495089
theorem B4220039 : Blo 1975435 4220039 := bstep (se 1 (by rfl) ⟨3165029, by rfl⟩ : syracuseStep 4220039 = 6330059) B6330059
theorem B11253437 : Blo 1975435 11253437 := bstep (se 3 (by rfl) ⟨2110019, by rfl⟩ : syracuseStep 11253437 = 4220039) B4220039
theorem B7502291 : Blo 1975435 7502291 := bstep (se 1 (by rfl) ⟨5626718, by rfl⟩ : syracuseStep 7502291 = 11253437) B11253437
theorem B5001527 : Blo 1975435 5001527 := bstep (se 1 (by rfl) ⟨3751145, by rfl⟩ : syracuseStep 5001527 = 7502291) B7502291
theorem B3334351 : Blo 1975435 3334351 := bstep (se 1 (by rfl) ⟨2500763, by rfl⟩ : syracuseStep 3334351 = 5001527) B5001527
theorem B4445801 : Blo 1975435 4445801 := bstep (se 2 (by rfl) ⟨1667175, by rfl⟩ : syracuseStep 4445801 = 3334351) B3334351
theorem B2963867 : Blo 1975435 2963867 := bstep (se 1 (by rfl) ⟨2222900, by rfl⟩ : syracuseStep 2963867 = 4445801) B4445801
theorem B1975911 : Blo 1975435 1975911 := bstep (se 1 (by rfl) ⟨1481933, by rfl⟩ : syracuseStep 1975911 = 2963867) B2963867
theorem B2222905 : Blo 1975435 2222905 := bbase (se 2 (by rfl) ⟨833589, by rfl⟩ : syracuseStep 2222905 = 1667179) (by norm_num)
theorem B2963873 : Blo 1975435 2963873 := bstep (se 2 (by rfl) ⟨1111452, by rfl⟩ : syracuseStep 2963873 = 2222905) B2222905
theorem B1975915 : Blo 1975435 1975915 := bstep (se 1 (by rfl) ⟨1481936, by rfl⟩ : syracuseStep 1975915 = 2963873) B2963873
theorem B5626741 : Blo 1975435 5626741 := bbase (se 5 (by rfl) ⟨263753, by rfl⟩ : syracuseStep 5626741 = 527507) (by norm_num)
theorem B7502321 : Blo 1975435 7502321 := bstep (se 2 (by rfl) ⟨2813370, by rfl⟩ : syracuseStep 7502321 = 5626741) B5626741
theorem B5001547 : Blo 1975435 5001547 := bstep (se 1 (by rfl) ⟨3751160, by rfl⟩ : syracuseStep 5001547 = 7502321) B7502321
theorem B6668729 : Blo 1975435 6668729 := bstep (se 2 (by rfl) ⟨2500773, by rfl⟩ : syracuseStep 6668729 = 5001547) B5001547
theorem B4445819 : Blo 1975435 4445819 := bstep (se 1 (by rfl) ⟨3334364, by rfl⟩ : syracuseStep 4445819 = 6668729) B6668729
theorem B2963879 : Blo 1975435 2963879 := bstep (se 1 (by rfl) ⟨2222909, by rfl⟩ : syracuseStep 2963879 = 4445819) B4445819
theorem B1975919 : Blo 1975435 1975919 := bstep (se 1 (by rfl) ⟨1481939, by rfl⟩ : syracuseStep 1975919 = 2963879) B2963879
theorem B2963885 : Blo 1975435 2963885 := bbase (se 3 (by rfl) ⟨555728, by rfl⟩ : syracuseStep 2963885 = 1111457) (by norm_num)
theorem B1975923 : Blo 1975435 1975923 := bstep (se 1 (by rfl) ⟨1481942, by rfl⟩ : syracuseStep 1975923 = 2963885) B2963885
theorem B4445837 : Blo 1975435 4445837 := bbase (se 3 (by rfl) ⟨833594, by rfl⟩ : syracuseStep 4445837 = 1667189) (by norm_num)
theorem B2963891 : Blo 1975435 2963891 := bstep (se 1 (by rfl) ⟨2222918, by rfl⟩ : syracuseStep 2963891 = 4445837) B4445837
theorem B1975927 : Blo 1975435 1975927 := bstep (se 1 (by rfl) ⟨1481945, by rfl⟩ : syracuseStep 1975927 = 2963891) B2963891
theorem B2500789 : Blo 1975435 2500789 := bbase (se 5 (by rfl) ⟨117224, by rfl⟩ : syracuseStep 2500789 = 234449) (by norm_num)
theorem B3334385 : Blo 1975435 3334385 := bstep (se 2 (by rfl) ⟨1250394, by rfl⟩ : syracuseStep 3334385 = 2500789) B2500789
theorem B2222923 : Blo 1975435 2222923 := bstep (se 1 (by rfl) ⟨1667192, by rfl⟩ : syracuseStep 2222923 = 3334385) B3334385
theorem B2963897 : Blo 1975435 2963897 := bstep (se 2 (by rfl) ⟨1111461, by rfl⟩ : syracuseStep 2963897 = 2222923) B2222923
theorem B1975931 : Blo 1975435 1975931 := bstep (se 1 (by rfl) ⟨1481948, by rfl⟩ : syracuseStep 1975931 = 2963897) B2963897
theorem B2030221 : Blo 1975435 2030221 := bbase (se 3 (by rfl) ⟨380666, by rfl⟩ : syracuseStep 2030221 = 761333) (by norm_num)
theorem B2706961 : Blo 1975435 2706961 := bstep (se 2 (by rfl) ⟨1015110, by rfl⟩ : syracuseStep 2706961 = 2030221) B2030221
theorem B3609281 : Blo 1975435 3609281 := bstep (se 2 (by rfl) ⟨1353480, by rfl⟩ : syracuseStep 3609281 = 2706961) B2706961
theorem B9624749 : Blo 1975435 9624749 := bstep (se 3 (by rfl) ⟨1804640, by rfl⟩ : syracuseStep 9624749 = 3609281) B3609281
theorem B25665997 : Blo 1975435 25665997 := bstep (se 3 (by rfl) ⟨4812374, by rfl⟩ : syracuseStep 25665997 = 9624749) B9624749
theorem B34221329 : Blo 1975435 34221329 := bstep (se 2 (by rfl) ⟨12832998, by rfl⟩ : syracuseStep 34221329 = 25665997) B25665997
theorem B22814219 : Blo 1975435 22814219 := bstep (se 1 (by rfl) ⟨17110664, by rfl⟩ : syracuseStep 22814219 = 34221329) B34221329
theorem B15209479 : Blo 1975435 15209479 := bstep (se 1 (by rfl) ⟨11407109, by rfl⟩ : syracuseStep 15209479 = 22814219) B22814219
theorem B20279305 : Blo 1975435 20279305 := bstep (se 2 (by rfl) ⟨7604739, by rfl⟩ : syracuseStep 20279305 = 15209479) B15209479
theorem B108156293 : Blo 1975435 108156293 := bstep (se 4 (by rfl) ⟨10139652, by rfl⟩ : syracuseStep 108156293 = 20279305) B20279305
theorem B72104195 : Blo 1975435 72104195 := bstep (se 1 (by rfl) ⟨54078146, by rfl⟩ : syracuseStep 72104195 = 108156293) B108156293
theorem B48069463 : Blo 1975435 48069463 := bstep (se 1 (by rfl) ⟨36052097, by rfl⟩ : syracuseStep 48069463 = 72104195) B72104195
theorem B64092617 : Blo 1975435 64092617 := bstep (se 2 (by rfl) ⟨24034731, by rfl⟩ : syracuseStep 64092617 = 48069463) B48069463
theorem B42728411 : Blo 1975435 42728411 := bstep (se 1 (by rfl) ⟨32046308, by rfl⟩ : syracuseStep 42728411 = 64092617) B64092617
theorem B28485607 : Blo 1975435 28485607 := bstep (se 1 (by rfl) ⟨21364205, by rfl⟩ : syracuseStep 28485607 = 42728411) B42728411
theorem B37980809 : Blo 1975435 37980809 := bstep (se 2 (by rfl) ⟨14242803, by rfl⟩ : syracuseStep 37980809 = 28485607) B28485607
theorem B25320539 : Blo 1975435 25320539 := bstep (se 1 (by rfl) ⟨18990404, by rfl⟩ : syracuseStep 25320539 = 37980809) B37980809
theorem B16880359 : Blo 1975435 16880359 := bstep (se 1 (by rfl) ⟨12660269, by rfl⟩ : syracuseStep 16880359 = 25320539) B25320539
theorem B22507145 : Blo 1975435 22507145 := bstep (se 2 (by rfl) ⟨8440179, by rfl⟩ : syracuseStep 22507145 = 16880359) B16880359
theorem B15004763 : Blo 1975435 15004763 := bstep (se 1 (by rfl) ⟨11253572, by rfl⟩ : syracuseStep 15004763 = 22507145) B22507145
theorem B10003175 : Blo 1975435 10003175 := bstep (se 1 (by rfl) ⟨7502381, by rfl⟩ : syracuseStep 10003175 = 15004763) B15004763
theorem B6668783 : Blo 1975435 6668783 := bstep (se 1 (by rfl) ⟨5001587, by rfl⟩ : syracuseStep 6668783 = 10003175) B10003175
theorem B4445855 : Blo 1975435 4445855 := bstep (se 1 (by rfl) ⟨3334391, by rfl⟩ : syracuseStep 4445855 = 6668783) B6668783
theorem B2963903 : Blo 1975435 2963903 := bstep (se 1 (by rfl) ⟨2222927, by rfl⟩ : syracuseStep 2963903 = 4445855) B4445855
theorem B1975935 : Blo 1975435 1975935 := bstep (se 1 (by rfl) ⟨1481951, by rfl⟩ : syracuseStep 1975935 = 2963903) B2963903
theorem B2963909 : Blo 1975435 2963909 := bbase (se 4 (by rfl) ⟨277866, by rfl⟩ : syracuseStep 2963909 = 555733) (by norm_num)
theorem B1975939 : Blo 1975435 1975939 := bstep (se 1 (by rfl) ⟨1481954, by rfl⟩ : syracuseStep 1975939 = 2963909) B2963909
theorem B3334405 : Blo 1975435 3334405 := bbase (se 4 (by rfl) ⟨312600, by rfl⟩ : syracuseStep 3334405 = 625201) (by norm_num)
theorem B4445873 : Blo 1975435 4445873 := bstep (se 2 (by rfl) ⟨1667202, by rfl⟩ : syracuseStep 4445873 = 3334405) B3334405
theorem B2963915 : Blo 1975435 2963915 := bstep (se 1 (by rfl) ⟨2222936, by rfl⟩ : syracuseStep 2963915 = 4445873) B4445873
theorem B1975943 : Blo 1975435 1975943 := bstep (se 1 (by rfl) ⟨1481957, by rfl⟩ : syracuseStep 1975943 = 2963915) B2963915
theorem B2222941 : Blo 1975435 2222941 := bbase (se 3 (by rfl) ⟨416801, by rfl⟩ : syracuseStep 2222941 = 833603) (by norm_num)
theorem B2963921 : Blo 1975435 2963921 := bstep (se 2 (by rfl) ⟨1111470, by rfl⟩ : syracuseStep 2963921 = 2222941) B2222941
theorem B1975947 : Blo 1975435 1975947 := bstep (se 1 (by rfl) ⟨1481960, by rfl⟩ : syracuseStep 1975947 = 2963921) B2963921
theorem B6668837 : Blo 1975435 6668837 := bbase (se 4 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 6668837 = 1250407) (by norm_num)
theorem B4445891 : Blo 1975435 4445891 := bstep (se 1 (by rfl) ⟨3334418, by rfl⟩ : syracuseStep 4445891 = 6668837) B6668837
theorem B2963927 : Blo 1975435 2963927 := bstep (se 1 (by rfl) ⟨2222945, by rfl⟩ : syracuseStep 2963927 = 4445891) B4445891
theorem B1975951 : Blo 1975435 1975951 := bstep (se 1 (by rfl) ⟨1481963, by rfl⟩ : syracuseStep 1975951 = 2963927) B2963927
theorem B2963933 : Blo 1975435 2963933 := bbase (se 3 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 2963933 = 1111475) (by norm_num)
theorem B1975955 : Blo 1975435 1975955 := bstep (se 1 (by rfl) ⟨1481966, by rfl⟩ : syracuseStep 1975955 = 2963933) B2963933
theorem B4445909 : Blo 1975435 4445909 := bbase (se 7 (by rfl) ⟨52100, by rfl⟩ : syracuseStep 4445909 = 104201) (by norm_num)
theorem B2963939 : Blo 1975435 2963939 := bstep (se 1 (by rfl) ⟨2222954, by rfl⟩ : syracuseStep 2963939 = 4445909) B4445909
theorem B1975959 : Blo 1975435 1975959 := bstep (se 1 (by rfl) ⟨1481969, by rfl⟩ : syracuseStep 1975959 = 2963939) B2963939
theorem B2670565 : Blo 1975435 2670565 := bbase (se 4 (by rfl) ⟨250365, by rfl⟩ : syracuseStep 2670565 = 500731) (by norm_num)
theorem B3560753 : Blo 1975435 3560753 := bstep (se 2 (by rfl) ⟨1335282, by rfl⟩ : syracuseStep 3560753 = 2670565) B2670565
theorem B2373835 : Blo 1975435 2373835 := bstep (se 1 (by rfl) ⟨1780376, by rfl⟩ : syracuseStep 2373835 = 3560753) B3560753
theorem B3165113 : Blo 1975435 3165113 := bstep (se 2 (by rfl) ⟨1186917, by rfl⟩ : syracuseStep 3165113 = 2373835) B2373835
theorem B8440301 : Blo 1975435 8440301 := bstep (se 3 (by rfl) ⟨1582556, by rfl⟩ : syracuseStep 8440301 = 3165113) B3165113
theorem B5626867 : Blo 1975435 5626867 := bstep (se 1 (by rfl) ⟨4220150, by rfl⟩ : syracuseStep 5626867 = 8440301) B8440301
theorem B7502489 : Blo 1975435 7502489 := bstep (se 2 (by rfl) ⟨2813433, by rfl⟩ : syracuseStep 7502489 = 5626867) B5626867
theorem B5001659 : Blo 1975435 5001659 := bstep (se 1 (by rfl) ⟨3751244, by rfl⟩ : syracuseStep 5001659 = 7502489) B7502489
theorem B3334439 : Blo 1975435 3334439 := bstep (se 1 (by rfl) ⟨2500829, by rfl⟩ : syracuseStep 3334439 = 5001659) B5001659
theorem B2222959 : Blo 1975435 2222959 := bstep (se 1 (by rfl) ⟨1667219, by rfl⟩ : syracuseStep 2222959 = 3334439) B3334439
theorem B2963945 : Blo 1975435 2963945 := bstep (se 2 (by rfl) ⟨1111479, by rfl⟩ : syracuseStep 2963945 = 2222959) B2222959
theorem B1975963 : Blo 1975435 1975963 := bstep (se 1 (by rfl) ⟨1481972, by rfl⟩ : syracuseStep 1975963 = 2963945) B2963945
theorem B5069909 : Blo 1975435 5069909 := bbase (se 8 (by rfl) ⟨29706, by rfl⟩ : syracuseStep 5069909 = 59413) (by norm_num)
theorem B13519757 : Blo 1975435 13519757 := bstep (se 3 (by rfl) ⟨2534954, by rfl⟩ : syracuseStep 13519757 = 5069909) B5069909
theorem B36052685 : Blo 1975435 36052685 := bstep (se 3 (by rfl) ⟨6759878, by rfl⟩ : syracuseStep 36052685 = 13519757) B13519757
theorem B24035123 : Blo 1975435 24035123 := bstep (se 1 (by rfl) ⟨18026342, by rfl⟩ : syracuseStep 24035123 = 36052685) B36052685
theorem B16023415 : Blo 1975435 16023415 := bstep (se 1 (by rfl) ⟨12017561, by rfl⟩ : syracuseStep 16023415 = 24035123) B24035123
theorem B21364553 : Blo 1975435 21364553 := bstep (se 2 (by rfl) ⟨8011707, by rfl⟩ : syracuseStep 21364553 = 16023415) B16023415
theorem B14243035 : Blo 1975435 14243035 := bstep (se 1 (by rfl) ⟨10682276, by rfl⟩ : syracuseStep 14243035 = 21364553) B21364553
theorem B18990713 : Blo 1975435 18990713 := bstep (se 2 (by rfl) ⟨7121517, by rfl⟩ : syracuseStep 18990713 = 14243035) B14243035
theorem B12660475 : Blo 1975435 12660475 := bstep (se 1 (by rfl) ⟨9495356, by rfl⟩ : syracuseStep 12660475 = 18990713) B18990713
theorem B16880633 : Blo 1975435 16880633 := bstep (se 2 (by rfl) ⟨6330237, by rfl⟩ : syracuseStep 16880633 = 12660475) B12660475
theorem B11253755 : Blo 1975435 11253755 := bstep (se 1 (by rfl) ⟨8440316, by rfl⟩ : syracuseStep 11253755 = 16880633) B16880633
theorem B7502503 : Blo 1975435 7502503 := bstep (se 1 (by rfl) ⟨5626877, by rfl⟩ : syracuseStep 7502503 = 11253755) B11253755
theorem B10003337 : Blo 1975435 10003337 := bstep (se 2 (by rfl) ⟨3751251, by rfl⟩ : syracuseStep 10003337 = 7502503) B7502503
theorem B6668891 : Blo 1975435 6668891 := bstep (se 1 (by rfl) ⟨5001668, by rfl⟩ : syracuseStep 6668891 = 10003337) B10003337
theorem B4445927 : Blo 1975435 4445927 := bstep (se 1 (by rfl) ⟨3334445, by rfl⟩ : syracuseStep 4445927 = 6668891) B6668891
theorem B2963951 : Blo 1975435 2963951 := bstep (se 1 (by rfl) ⟨2222963, by rfl⟩ : syracuseStep 2963951 = 4445927) B4445927
theorem B1975967 : Blo 1975435 1975967 := bstep (se 1 (by rfl) ⟨1481975, by rfl⟩ : syracuseStep 1975967 = 2963951) B2963951
theorem B2963957 : Blo 1975435 2963957 := bbase (se 5 (by rfl) ⟨138935, by rfl⟩ : syracuseStep 2963957 = 277871) (by norm_num)
theorem B1975971 : Blo 1975435 1975971 := bstep (se 1 (by rfl) ⟨1481978, by rfl⟩ : syracuseStep 1975971 = 2963957) B2963957
theorem B5626901 : Blo 1975435 5626901 := bbase (se 6 (by rfl) ⟨131880, by rfl⟩ : syracuseStep 5626901 = 263761) (by norm_num)
theorem B3751267 : Blo 1975435 3751267 := bstep (se 1 (by rfl) ⟨2813450, by rfl⟩ : syracuseStep 3751267 = 5626901) B5626901
theorem B5001689 : Blo 1975435 5001689 := bstep (se 2 (by rfl) ⟨1875633, by rfl⟩ : syracuseStep 5001689 = 3751267) B3751267
theorem B3334459 : Blo 1975435 3334459 := bstep (se 1 (by rfl) ⟨2500844, by rfl⟩ : syracuseStep 3334459 = 5001689) B5001689
theorem B4445945 : Blo 1975435 4445945 := bstep (se 2 (by rfl) ⟨1667229, by rfl⟩ : syracuseStep 4445945 = 3334459) B3334459
theorem B2963963 : Blo 1975435 2963963 := bstep (se 1 (by rfl) ⟨2222972, by rfl⟩ : syracuseStep 2963963 = 4445945) B4445945
theorem B1975975 : Blo 1975435 1975975 := bstep (se 1 (by rfl) ⟨1481981, by rfl⟩ : syracuseStep 1975975 = 2963963) B2963963
theorem B2222977 : Blo 1975435 2222977 := bbase (se 2 (by rfl) ⟨833616, by rfl⟩ : syracuseStep 2222977 = 1667233) (by norm_num)
theorem B2963969 : Blo 1975435 2963969 := bstep (se 2 (by rfl) ⟨1111488, by rfl⟩ : syracuseStep 2963969 = 2222977) B2222977
theorem B1975979 : Blo 1975435 1975979 := bstep (se 1 (by rfl) ⟨1481984, by rfl⟩ : syracuseStep 1975979 = 2963969) B2963969
theorem B5001709 : Blo 1975435 5001709 := bbase (se 3 (by rfl) ⟨937820, by rfl⟩ : syracuseStep 5001709 = 1875641) (by norm_num)
theorem B6668945 : Blo 1975435 6668945 := bstep (se 2 (by rfl) ⟨2500854, by rfl⟩ : syracuseStep 6668945 = 5001709) B5001709
theorem B4445963 : Blo 1975435 4445963 := bstep (se 1 (by rfl) ⟨3334472, by rfl⟩ : syracuseStep 4445963 = 6668945) B6668945
theorem B2963975 : Blo 1975435 2963975 := bstep (se 1 (by rfl) ⟨2222981, by rfl⟩ : syracuseStep 2963975 = 4445963) B4445963
theorem B1975983 : Blo 1975435 1975983 := bstep (se 1 (by rfl) ⟨1481987, by rfl⟩ : syracuseStep 1975983 = 2963975) B2963975
theorem B2963981 : Blo 1975435 2963981 := bbase (se 3 (by rfl) ⟨555746, by rfl⟩ : syracuseStep 2963981 = 1111493) (by norm_num)
theorem B1975987 : Blo 1975435 1975987 := bstep (se 1 (by rfl) ⟨1481990, by rfl⟩ : syracuseStep 1975987 = 2963981) B2963981
theorem B4445981 : Blo 1975435 4445981 := bbase (se 3 (by rfl) ⟨833621, by rfl⟩ : syracuseStep 4445981 = 1667243) (by norm_num)
theorem B2963987 : Blo 1975435 2963987 := bstep (se 1 (by rfl) ⟨2222990, by rfl⟩ : syracuseStep 2963987 = 4445981) B4445981
theorem B1975991 : Blo 1975435 1975991 := bstep (se 1 (by rfl) ⟨1481993, by rfl⟩ : syracuseStep 1975991 = 2963987) B2963987
theorem B3334493 : Blo 1975435 3334493 := bbase (se 3 (by rfl) ⟨625217, by rfl⟩ : syracuseStep 3334493 = 1250435) (by norm_num)
theorem B2222995 : Blo 1975435 2222995 := bstep (se 1 (by rfl) ⟨1667246, by rfl⟩ : syracuseStep 2222995 = 3334493) B3334493
theorem B2963993 : Blo 1975435 2963993 := bstep (se 2 (by rfl) ⟨1111497, by rfl⟩ : syracuseStep 2963993 = 2222995) B2222995
theorem B1975995 : Blo 1975435 1975995 := bstep (se 1 (by rfl) ⟨1481996, by rfl⟩ : syracuseStep 1975995 = 2963993) B2963993
theorem B8440453 : Blo 1975435 8440453 := bbase (se 4 (by rfl) ⟨791292, by rfl⟩ : syracuseStep 8440453 = 1582585) (by norm_num)
theorem B11253937 : Blo 1975435 11253937 := bstep (se 2 (by rfl) ⟨4220226, by rfl⟩ : syracuseStep 11253937 = 8440453) B8440453
theorem B15005249 : Blo 1975435 15005249 := bstep (se 2 (by rfl) ⟨5626968, by rfl⟩ : syracuseStep 15005249 = 11253937) B11253937
theorem B10003499 : Blo 1975435 10003499 := bstep (se 1 (by rfl) ⟨7502624, by rfl⟩ : syracuseStep 10003499 = 15005249) B15005249
theorem B6668999 : Blo 1975435 6668999 := bstep (se 1 (by rfl) ⟨5001749, by rfl⟩ : syracuseStep 6668999 = 10003499) B10003499
theorem B4445999 : Blo 1975435 4445999 := bstep (se 1 (by rfl) ⟨3334499, by rfl⟩ : syracuseStep 4445999 = 6668999) B6668999
theorem B2963999 : Blo 1975435 2963999 := bstep (se 1 (by rfl) ⟨2222999, by rfl⟩ : syracuseStep 2963999 = 4445999) B4445999
theorem B1975999 : Blo 1975435 1975999 := bstep (se 1 (by rfl) ⟨1481999, by rfl⟩ : syracuseStep 1975999 = 2963999) B2963999
theorem B2964005 : Blo 1975435 2964005 := bbase (se 4 (by rfl) ⟨277875, by rfl⟩ : syracuseStep 2964005 = 555751) (by norm_num)
theorem B1976003 : Blo 1975435 1976003 := bstep (se 1 (by rfl) ⟨1482002, by rfl⟩ : syracuseStep 1976003 = 2964005) B2964005
theorem B2500885 : Blo 1975435 2500885 := bbase (se 6 (by rfl) ⟨58614, by rfl⟩ : syracuseStep 2500885 = 117229) (by norm_num)
theorem B3334513 : Blo 1975435 3334513 := bstep (se 2 (by rfl) ⟨1250442, by rfl⟩ : syracuseStep 3334513 = 2500885) B2500885
theorem B4446017 : Blo 1975435 4446017 := bstep (se 2 (by rfl) ⟨1667256, by rfl⟩ : syracuseStep 4446017 = 3334513) B3334513
theorem B2964011 : Blo 1975435 2964011 := bstep (se 1 (by rfl) ⟨2223008, by rfl⟩ : syracuseStep 2964011 = 4446017) B4446017
theorem B1976007 : Blo 1975435 1976007 := bstep (se 1 (by rfl) ⟨1482005, by rfl⟩ : syracuseStep 1976007 = 2964011) B2964011
theorem B2223013 : Blo 1975435 2223013 := bbase (se 4 (by rfl) ⟨208407, by rfl⟩ : syracuseStep 2223013 = 416815) (by norm_num)
theorem B2964017 : Blo 1975435 2964017 := bstep (se 2 (by rfl) ⟨1111506, by rfl⟩ : syracuseStep 2964017 = 2223013) B2223013
theorem B1976011 : Blo 1975435 1976011 := bstep (se 1 (by rfl) ⟨1482008, by rfl⟩ : syracuseStep 1976011 = 2964017) B2964017
theorem B9495589 : Blo 1975435 9495589 := bbase (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) (by norm_num)
theorem B12660785 : Blo 1975435 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B8440523 : Blo 1975435 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B5627015 : Blo 1975435 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B3751343 : Blo 1975435 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B2500895 : Blo 1975435 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B6669053 : Blo 1975435 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B4446035 : Blo 1975435 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B2964023 : Blo 1975435 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B1976015 : Blo 1975435 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B2964029 : Blo 1975435 2964029 := bbase (se 3 (by rfl) ⟨555755, by rfl⟩ : syracuseStep 2964029 = 1111511) (by norm_num)
theorem B1976019 : Blo 1975435 1976019 := bstep (se 1 (by rfl) ⟨1482014, by rfl⟩ : syracuseStep 1976019 = 2964029) B2964029
theorem B4446053 : Blo 1975435 4446053 := bbase (se 4 (by rfl) ⟨416817, by rfl⟩ : syracuseStep 4446053 = 833635) (by norm_num)
theorem B2964035 : Blo 1975435 2964035 := bstep (se 1 (by rfl) ⟨2223026, by rfl⟩ : syracuseStep 2964035 = 4446053) B4446053
theorem B1976023 : Blo 1975435 1976023 := bstep (se 1 (by rfl) ⟨1482017, by rfl⟩ : syracuseStep 1976023 = 2964035) B2964035
theorem B5001821 : Blo 1975435 5001821 := bbase (se 3 (by rfl) ⟨937841, by rfl⟩ : syracuseStep 5001821 = 1875683) (by norm_num)
theorem B3334547 : Blo 1975435 3334547 := bstep (se 1 (by rfl) ⟨2500910, by rfl⟩ : syracuseStep 3334547 = 5001821) B5001821
theorem B2223031 : Blo 1975435 2223031 := bstep (se 1 (by rfl) ⟨1667273, by rfl⟩ : syracuseStep 2223031 = 3334547) B3334547
theorem B2964041 : Blo 1975435 2964041 := bstep (se 2 (by rfl) ⟨1111515, by rfl⟩ : syracuseStep 2964041 = 2223031) B2223031
theorem B1976027 : Blo 1975435 1976027 := bstep (se 1 (by rfl) ⟨1482020, by rfl⟩ : syracuseStep 1976027 = 2964041) B2964041
theorem B3751373 : Blo 1975435 3751373 := bbase (se 3 (by rfl) ⟨703382, by rfl⟩ : syracuseStep 3751373 = 1406765) (by norm_num)
theorem B10003661 : Blo 1975435 10003661 := bstep (se 3 (by rfl) ⟨1875686, by rfl⟩ : syracuseStep 10003661 = 3751373) B3751373
theorem B6669107 : Blo 1975435 6669107 := bstep (se 1 (by rfl) ⟨5001830, by rfl⟩ : syracuseStep 6669107 = 10003661) B10003661
theorem B4446071 : Blo 1975435 4446071 := bstep (se 1 (by rfl) ⟨3334553, by rfl⟩ : syracuseStep 4446071 = 6669107) B6669107
theorem B2964047 : Blo 1975435 2964047 := bstep (se 1 (by rfl) ⟨2223035, by rfl⟩ : syracuseStep 2964047 = 4446071) B4446071
theorem B1976031 : Blo 1975435 1976031 := bstep (se 1 (by rfl) ⟨1482023, by rfl⟩ : syracuseStep 1976031 = 2964047) B2964047
theorem B2964053 : Blo 1975435 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B1976035 : Blo 1975435 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B6330469 : Blo 1975435 6330469 := bbase (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) (by norm_num)
theorem B8440625 : Blo 1975435 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B5627083 : Blo 1975435 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B7502777 : Blo 1975435 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B5001851 : Blo 1975435 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B3334567 : Blo 1975435 3334567 := bstep (se 1 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 3334567 = 5001851) B5001851
theorem B4446089 : Blo 1975435 4446089 := bstep (se 2 (by rfl) ⟨1667283, by rfl⟩ : syracuseStep 4446089 = 3334567) B3334567
theorem B2964059 : Blo 1975435 2964059 := bstep (se 1 (by rfl) ⟨2223044, by rfl⟩ : syracuseStep 2964059 = 4446089) B4446089
theorem B1976039 : Blo 1975435 1976039 := bstep (se 1 (by rfl) ⟨1482029, by rfl⟩ : syracuseStep 1976039 = 2964059) B2964059
theorem B2223049 : Blo 1975435 2223049 := bbase (se 2 (by rfl) ⟨833643, by rfl⟩ : syracuseStep 2223049 = 1667287) (by norm_num)
theorem B2964065 : Blo 1975435 2964065 := bstep (se 2 (by rfl) ⟨1111524, by rfl⟩ : syracuseStep 2964065 = 2223049) B2223049
theorem B1976043 : Blo 1975435 1976043 := bstep (se 1 (by rfl) ⟨1482032, by rfl⟩ : syracuseStep 1976043 = 2964065) B2964065
theorem B3380077 : Blo 1975435 3380077 := bbase (se 3 (by rfl) ⟨633764, by rfl⟩ : syracuseStep 3380077 = 1267529) (by norm_num)
theorem B4506769 : Blo 1975435 4506769 := bstep (se 2 (by rfl) ⟨1690038, by rfl⟩ : syracuseStep 4506769 = 3380077) B3380077
theorem B24036101 : Blo 1975435 24036101 := bstep (se 4 (by rfl) ⟨2253384, by rfl⟩ : syracuseStep 24036101 = 4506769) B4506769
theorem B16024067 : Blo 1975435 16024067 := bstep (se 1 (by rfl) ⟨12018050, by rfl⟩ : syracuseStep 16024067 = 24036101) B24036101
theorem B10682711 : Blo 1975435 10682711 := bstep (se 1 (by rfl) ⟨8012033, by rfl⟩ : syracuseStep 10682711 = 16024067) B16024067
theorem B7121807 : Blo 1975435 7121807 := bstep (se 1 (by rfl) ⟨5341355, by rfl⟩ : syracuseStep 7121807 = 10682711) B10682711
theorem B4747871 : Blo 1975435 4747871 := bstep (se 1 (by rfl) ⟨3560903, by rfl⟩ : syracuseStep 4747871 = 7121807) B7121807
theorem B3165247 : Blo 1975435 3165247 := bstep (se 1 (by rfl) ⟨2373935, by rfl⟩ : syracuseStep 3165247 = 4747871) B4747871
theorem B16881317 : Blo 1975435 16881317 := bstep (se 4 (by rfl) ⟨1582623, by rfl⟩ : syracuseStep 16881317 = 3165247) B3165247
theorem B11254211 : Blo 1975435 11254211 := bstep (se 1 (by rfl) ⟨8440658, by rfl⟩ : syracuseStep 11254211 = 16881317) B16881317
theorem B7502807 : Blo 1975435 7502807 := bstep (se 1 (by rfl) ⟨5627105, by rfl⟩ : syracuseStep 7502807 = 11254211) B11254211
theorem B5001871 : Blo 1975435 5001871 := bstep (se 1 (by rfl) ⟨3751403, by rfl⟩ : syracuseStep 5001871 = 7502807) B7502807
theorem B6669161 : Blo 1975435 6669161 := bstep (se 2 (by rfl) ⟨2500935, by rfl⟩ : syracuseStep 6669161 = 5001871) B5001871
theorem B4446107 : Blo 1975435 4446107 := bstep (se 1 (by rfl) ⟨3334580, by rfl⟩ : syracuseStep 4446107 = 6669161) B6669161
theorem B2964071 : Blo 1975435 2964071 := bstep (se 1 (by rfl) ⟨2223053, by rfl⟩ : syracuseStep 2964071 = 4446107) B4446107
theorem B1976047 : Blo 1975435 1976047 := bstep (se 1 (by rfl) ⟨1482035, by rfl⟩ : syracuseStep 1976047 = 2964071) B2964071
theorem B2964077 : Blo 1975435 2964077 := bbase (se 3 (by rfl) ⟨555764, by rfl⟩ : syracuseStep 2964077 = 1111529) (by norm_num)
theorem B1976051 : Blo 1975435 1976051 := bstep (se 1 (by rfl) ⟨1482038, by rfl⟩ : syracuseStep 1976051 = 2964077) B2964077
theorem B4446125 : Blo 1975435 4446125 := bbase (se 3 (by rfl) ⟨833648, by rfl⟩ : syracuseStep 4446125 = 1667297) (by norm_num)
theorem B2964083 : Blo 1975435 2964083 := bstep (se 1 (by rfl) ⟨2223062, by rfl⟩ : syracuseStep 2964083 = 4446125) B4446125
theorem B1976055 : Blo 1975435 1976055 := bstep (se 1 (by rfl) ⟨1482041, by rfl⟩ : syracuseStep 1976055 = 2964083) B2964083
theorem B5627141 : Blo 1975435 5627141 := bbase (se 4 (by rfl) ⟨527544, by rfl⟩ : syracuseStep 5627141 = 1055089) (by norm_num)
theorem B3751427 : Blo 1975435 3751427 := bstep (se 1 (by rfl) ⟨2813570, by rfl⟩ : syracuseStep 3751427 = 5627141) B5627141
theorem B2500951 : Blo 1975435 2500951 := bstep (se 1 (by rfl) ⟨1875713, by rfl⟩ : syracuseStep 2500951 = 3751427) B3751427
theorem B3334601 : Blo 1975435 3334601 := bstep (se 2 (by rfl) ⟨1250475, by rfl⟩ : syracuseStep 3334601 = 2500951) B2500951
theorem B2223067 : Blo 1975435 2223067 := bstep (se 1 (by rfl) ⟨1667300, by rfl⟩ : syracuseStep 2223067 = 3334601) B3334601
theorem B2964089 : Blo 1975435 2964089 := bstep (se 2 (by rfl) ⟨1111533, by rfl⟩ : syracuseStep 2964089 = 2223067) B2223067
theorem B1976059 : Blo 1975435 1976059 := bstep (se 1 (by rfl) ⟨1482044, by rfl⟩ : syracuseStep 1976059 = 2964089) B2964089
theorem B22815701 : Blo 1975435 22815701 := bbase (se 7 (by rfl) ⟨267371, by rfl⟩ : syracuseStep 22815701 = 534743) (by norm_num)
theorem B15210467 : Blo 1975435 15210467 := bstep (se 1 (by rfl) ⟨11407850, by rfl⟩ : syracuseStep 15210467 = 22815701) B22815701
theorem B10140311 : Blo 1975435 10140311 := bstep (se 1 (by rfl) ⟨7605233, by rfl⟩ : syracuseStep 10140311 = 15210467) B15210467
theorem B6760207 : Blo 1975435 6760207 := bstep (se 1 (by rfl) ⟨5070155, by rfl⟩ : syracuseStep 6760207 = 10140311) B10140311
theorem B9013609 : Blo 1975435 9013609 := bstep (se 2 (by rfl) ⟨3380103, by rfl⟩ : syracuseStep 9013609 = 6760207) B6760207
theorem B12018145 : Blo 1975435 12018145 := bstep (se 2 (by rfl) ⟨4506804, by rfl⟩ : syracuseStep 12018145 = 9013609) B9013609
theorem B16024193 : Blo 1975435 16024193 := bstep (se 2 (by rfl) ⟨6009072, by rfl⟩ : syracuseStep 16024193 = 12018145) B12018145
theorem B10682795 : Blo 1975435 10682795 := bstep (se 1 (by rfl) ⟨8012096, by rfl⟩ : syracuseStep 10682795 = 16024193) B16024193
theorem B7121863 : Blo 1975435 7121863 := bstep (se 1 (by rfl) ⟨5341397, by rfl⟩ : syracuseStep 7121863 = 10682795) B10682795
theorem B37983269 : Blo 1975435 37983269 := bstep (se 4 (by rfl) ⟨3560931, by rfl⟩ : syracuseStep 37983269 = 7121863) B7121863
theorem B25322179 : Blo 1975435 25322179 := bstep (se 1 (by rfl) ⟨18991634, by rfl⟩ : syracuseStep 25322179 = 37983269) B37983269
theorem B33762905 : Blo 1975435 33762905 := bstep (se 2 (by rfl) ⟨12661089, by rfl⟩ : syracuseStep 33762905 = 25322179) B25322179
theorem B22508603 : Blo 1975435 22508603 := bstep (se 1 (by rfl) ⟨16881452, by rfl⟩ : syracuseStep 22508603 = 33762905) B33762905
theorem B15005735 : Blo 1975435 15005735 := bstep (se 1 (by rfl) ⟨11254301, by rfl⟩ : syracuseStep 15005735 = 22508603) B22508603
theorem B10003823 : Blo 1975435 10003823 := bstep (se 1 (by rfl) ⟨7502867, by rfl⟩ : syracuseStep 10003823 = 15005735) B15005735
theorem B6669215 : Blo 1975435 6669215 := bstep (se 1 (by rfl) ⟨5001911, by rfl⟩ : syracuseStep 6669215 = 10003823) B10003823
theorem B4446143 : Blo 1975435 4446143 := bstep (se 1 (by rfl) ⟨3334607, by rfl⟩ : syracuseStep 4446143 = 6669215) B6669215
theorem B2964095 : Blo 1975435 2964095 := bstep (se 1 (by rfl) ⟨2223071, by rfl⟩ : syracuseStep 2964095 = 4446143) B4446143
theorem B1976063 : Blo 1975435 1976063 := bstep (se 1 (by rfl) ⟨1482047, by rfl⟩ : syracuseStep 1976063 = 2964095) B2964095
theorem B2964101 : Blo 1975435 2964101 := bbase (se 4 (by rfl) ⟨277884, by rfl⟩ : syracuseStep 2964101 = 555769) (by norm_num)
theorem B1976067 : Blo 1975435 1976067 := bstep (se 1 (by rfl) ⟨1482050, by rfl⟩ : syracuseStep 1976067 = 2964101) B2964101
theorem B3334621 : Blo 1975435 3334621 := bbase (se 3 (by rfl) ⟨625241, by rfl⟩ : syracuseStep 3334621 = 1250483) (by norm_num)
theorem B4446161 : Blo 1975435 4446161 := bstep (se 2 (by rfl) ⟨1667310, by rfl⟩ : syracuseStep 4446161 = 3334621) B3334621
theorem B2964107 : Blo 1975435 2964107 := bstep (se 1 (by rfl) ⟨2223080, by rfl⟩ : syracuseStep 2964107 = 4446161) B4446161
theorem B1976071 : Blo 1975435 1976071 := bstep (se 1 (by rfl) ⟨1482053, by rfl⟩ : syracuseStep 1976071 = 2964107) B2964107
theorem B2223085 : Blo 1975435 2223085 := bbase (se 3 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 2223085 = 833657) (by norm_num)
theorem B2964113 : Blo 1975435 2964113 := bstep (se 2 (by rfl) ⟨1111542, by rfl⟩ : syracuseStep 2964113 = 2223085) B2223085
theorem B1976075 : Blo 1975435 1976075 := bstep (se 1 (by rfl) ⟨1482056, by rfl⟩ : syracuseStep 1976075 = 2964113) B2964113
theorem B6669269 : Blo 1975435 6669269 := bbase (se 7 (by rfl) ⟨78155, by rfl⟩ : syracuseStep 6669269 = 156311) (by norm_num)
theorem B4446179 : Blo 1975435 4446179 := bstep (se 1 (by rfl) ⟨3334634, by rfl⟩ : syracuseStep 4446179 = 6669269) B6669269
theorem B2964119 : Blo 1975435 2964119 := bstep (se 1 (by rfl) ⟨2223089, by rfl⟩ : syracuseStep 2964119 = 4446179) B4446179
theorem B1976079 : Blo 1975435 1976079 := bstep (se 1 (by rfl) ⟨1482059, by rfl⟩ : syracuseStep 1976079 = 2964119) B2964119
theorem B2964125 : Blo 1975435 2964125 := bbase (se 3 (by rfl) ⟨555773, by rfl⟩ : syracuseStep 2964125 = 1111547) (by norm_num)
theorem B1976083 : Blo 1975435 1976083 := bstep (se 1 (by rfl) ⟨1482062, by rfl⟩ : syracuseStep 1976083 = 2964125) B2964125
theorem B4446197 : Blo 1975435 4446197 := bbase (se 5 (by rfl) ⟨208415, by rfl⟩ : syracuseStep 4446197 = 416831) (by norm_num)
theorem B2964131 : Blo 1975435 2964131 := bstep (se 1 (by rfl) ⟨2223098, by rfl⟩ : syracuseStep 2964131 = 4446197) B4446197
theorem B1976087 : Blo 1975435 1976087 := bstep (se 1 (by rfl) ⟨1482065, by rfl⟩ : syracuseStep 1976087 = 2964131) B2964131
theorem B5781829 : Blo 1975435 5781829 := bbase (se 4 (by rfl) ⟨542046, by rfl⟩ : syracuseStep 5781829 = 1084093) (by norm_num)
theorem B7709105 : Blo 1975435 7709105 := bstep (se 2 (by rfl) ⟨2890914, by rfl⟩ : syracuseStep 7709105 = 5781829) B5781829
theorem B20557613 : Blo 1975435 20557613 := bstep (se 3 (by rfl) ⟨3854552, by rfl⟩ : syracuseStep 20557613 = 7709105) B7709105
theorem B13705075 : Blo 1975435 13705075 := bstep (se 1 (by rfl) ⟨10278806, by rfl⟩ : syracuseStep 13705075 = 20557613) B20557613
theorem B18273433 : Blo 1975435 18273433 := bstep (se 2 (by rfl) ⟨6852537, by rfl⟩ : syracuseStep 18273433 = 13705075) B13705075
theorem B24364577 : Blo 1975435 24364577 := bstep (se 2 (by rfl) ⟨9136716, by rfl⟩ : syracuseStep 24364577 = 18273433) B18273433
theorem B16243051 : Blo 1975435 16243051 := bstep (se 1 (by rfl) ⟨12182288, by rfl⟩ : syracuseStep 16243051 = 24364577) B24364577
theorem B21657401 : Blo 1975435 21657401 := bstep (se 2 (by rfl) ⟨8121525, by rfl⟩ : syracuseStep 21657401 = 16243051) B16243051
theorem B14438267 : Blo 1975435 14438267 := bstep (se 1 (by rfl) ⟨10828700, by rfl⟩ : syracuseStep 14438267 = 21657401) B21657401
theorem B9625511 : Blo 1975435 9625511 := bstep (se 1 (by rfl) ⟨7219133, by rfl⟩ : syracuseStep 9625511 = 14438267) B14438267
theorem B25668029 : Blo 1975435 25668029 := bstep (se 3 (by rfl) ⟨4812755, by rfl⟩ : syracuseStep 25668029 = 9625511) B9625511
theorem B17112019 : Blo 1975435 17112019 := bstep (se 1 (by rfl) ⟨12834014, by rfl⟩ : syracuseStep 17112019 = 25668029) B25668029
theorem B22816025 : Blo 1975435 22816025 := bstep (se 2 (by rfl) ⟨8556009, by rfl⟩ : syracuseStep 22816025 = 17112019) B17112019
theorem B15210683 : Blo 1975435 15210683 := bstep (se 1 (by rfl) ⟨11408012, by rfl⟩ : syracuseStep 15210683 = 22816025) B22816025
theorem B10140455 : Blo 1975435 10140455 := bstep (se 1 (by rfl) ⟨7605341, by rfl⟩ : syracuseStep 10140455 = 15210683) B15210683
theorem B27041213 : Blo 1975435 27041213 := bstep (se 3 (by rfl) ⟨5070227, by rfl⟩ : syracuseStep 27041213 = 10140455) B10140455
theorem B72109901 : Blo 1975435 72109901 := bstep (se 3 (by rfl) ⟨13520606, by rfl⟩ : syracuseStep 72109901 = 27041213) B27041213
theorem B48073267 : Blo 1975435 48073267 := bstep (se 1 (by rfl) ⟨36054950, by rfl⟩ : syracuseStep 48073267 = 72109901) B72109901
theorem B64097689 : Blo 1975435 64097689 := bstep (se 2 (by rfl) ⟨24036633, by rfl⟩ : syracuseStep 64097689 = 48073267) B48073267
theorem B85463585 : Blo 1975435 85463585 := bstep (se 2 (by rfl) ⟨32048844, by rfl⟩ : syracuseStep 85463585 = 64097689) B64097689
theorem B56975723 : Blo 1975435 56975723 := bstep (se 1 (by rfl) ⟨42731792, by rfl⟩ : syracuseStep 56975723 = 85463585) B85463585
theorem B37983815 : Blo 1975435 37983815 := bstep (se 1 (by rfl) ⟨28487861, by rfl⟩ : syracuseStep 37983815 = 56975723) B56975723
theorem B25322543 : Blo 1975435 25322543 := bstep (se 1 (by rfl) ⟨18991907, by rfl⟩ : syracuseStep 25322543 = 37983815) B37983815
theorem B16881695 : Blo 1975435 16881695 := bstep (se 1 (by rfl) ⟨12661271, by rfl⟩ : syracuseStep 16881695 = 25322543) B25322543
theorem B11254463 : Blo 1975435 11254463 := bstep (se 1 (by rfl) ⟨8440847, by rfl⟩ : syracuseStep 11254463 = 16881695) B16881695
theorem B7502975 : Blo 1975435 7502975 := bstep (se 1 (by rfl) ⟨5627231, by rfl⟩ : syracuseStep 7502975 = 11254463) B11254463
theorem B5001983 : Blo 1975435 5001983 := bstep (se 1 (by rfl) ⟨3751487, by rfl⟩ : syracuseStep 5001983 = 7502975) B7502975
theorem B3334655 : Blo 1975435 3334655 := bstep (se 1 (by rfl) ⟨2500991, by rfl⟩ : syracuseStep 3334655 = 5001983) B5001983
theorem B2223103 : Blo 1975435 2223103 := bstep (se 1 (by rfl) ⟨1667327, by rfl⟩ : syracuseStep 2223103 = 3334655) B3334655
theorem B2964137 : Blo 1975435 2964137 := bstep (se 2 (by rfl) ⟨1111551, by rfl⟩ : syracuseStep 2964137 = 2223103) B2223103
theorem B1976091 : Blo 1975435 1976091 := bstep (se 1 (by rfl) ⟨1482068, by rfl⟩ : syracuseStep 1976091 = 2964137) B2964137
theorem B2813621 : Blo 1975435 2813621 := bbase (se 5 (by rfl) ⟨131888, by rfl⟩ : syracuseStep 2813621 = 263777) (by norm_num)
theorem B7502989 : Blo 1975435 7502989 := bstep (se 3 (by rfl) ⟨1406810, by rfl⟩ : syracuseStep 7502989 = 2813621) B2813621
theorem B10003985 : Blo 1975435 10003985 := bstep (se 2 (by rfl) ⟨3751494, by rfl⟩ : syracuseStep 10003985 = 7502989) B7502989
theorem B6669323 : Blo 1975435 6669323 := bstep (se 1 (by rfl) ⟨5001992, by rfl⟩ : syracuseStep 6669323 = 10003985) B10003985
theorem B4446215 : Blo 1975435 4446215 := bstep (se 1 (by rfl) ⟨3334661, by rfl⟩ : syracuseStep 4446215 = 6669323) B6669323
theorem B2964143 : Blo 1975435 2964143 := bstep (se 1 (by rfl) ⟨2223107, by rfl⟩ : syracuseStep 2964143 = 4446215) B4446215
theorem B1976095 : Blo 1975435 1976095 := bstep (se 1 (by rfl) ⟨1482071, by rfl⟩ : syracuseStep 1976095 = 2964143) B2964143
theorem B2964149 : Blo 1975435 2964149 := bbase (se 5 (by rfl) ⟨138944, by rfl⟩ : syracuseStep 2964149 = 277889) (by norm_num)
theorem B1976099 : Blo 1975435 1976099 := bstep (se 1 (by rfl) ⟨1482074, by rfl⟩ : syracuseStep 1976099 = 2964149) B2964149
theorem B5002013 : Blo 1975435 5002013 := bbase (se 3 (by rfl) ⟨937877, by rfl⟩ : syracuseStep 5002013 = 1875755) (by norm_num)
theorem B3334675 : Blo 1975435 3334675 := bstep (se 1 (by rfl) ⟨2501006, by rfl⟩ : syracuseStep 3334675 = 5002013) B5002013
theorem B4446233 : Blo 1975435 4446233 := bstep (se 2 (by rfl) ⟨1667337, by rfl⟩ : syracuseStep 4446233 = 3334675) B3334675
theorem B2964155 : Blo 1975435 2964155 := bstep (se 1 (by rfl) ⟨2223116, by rfl⟩ : syracuseStep 2964155 = 4446233) B4446233
theorem B1976103 : Blo 1975435 1976103 := bstep (se 1 (by rfl) ⟨1482077, by rfl⟩ : syracuseStep 1976103 = 2964155) B2964155
theorem B2223121 : Blo 1975435 2223121 := bbase (se 2 (by rfl) ⟨833670, by rfl⟩ : syracuseStep 2223121 = 1667341) (by norm_num)
theorem B2964161 : Blo 1975435 2964161 := bstep (se 2 (by rfl) ⟨1111560, by rfl⟩ : syracuseStep 2964161 = 2223121) B2223121
theorem B1976107 : Blo 1975435 1976107 := bstep (se 1 (by rfl) ⟨1482080, by rfl⟩ : syracuseStep 1976107 = 2964161) B2964161
theorem B3751525 : Blo 1975435 3751525 := bbase (se 4 (by rfl) ⟨351705, by rfl⟩ : syracuseStep 3751525 = 703411) (by norm_num)
theorem B5002033 : Blo 1975435 5002033 := bstep (se 2 (by rfl) ⟨1875762, by rfl⟩ : syracuseStep 5002033 = 3751525) B3751525
theorem B6669377 : Blo 1975435 6669377 := bstep (se 2 (by rfl) ⟨2501016, by rfl⟩ : syracuseStep 6669377 = 5002033) B5002033
theorem B4446251 : Blo 1975435 4446251 := bstep (se 1 (by rfl) ⟨3334688, by rfl⟩ : syracuseStep 4446251 = 6669377) B6669377
theorem B2964167 : Blo 1975435 2964167 := bstep (se 1 (by rfl) ⟨2223125, by rfl⟩ : syracuseStep 2964167 = 4446251) B4446251
theorem B1976111 : Blo 1975435 1976111 := bstep (se 1 (by rfl) ⟨1482083, by rfl⟩ : syracuseStep 1976111 = 2964167) B2964167
theorem B2964173 : Blo 1975435 2964173 := bbase (se 3 (by rfl) ⟨555782, by rfl⟩ : syracuseStep 2964173 = 1111565) (by norm_num)
theorem B1976115 : Blo 1975435 1976115 := bstep (se 1 (by rfl) ⟨1482086, by rfl⟩ : syracuseStep 1976115 = 2964173) B2964173
theorem B4446269 : Blo 1975435 4446269 := bbase (se 3 (by rfl) ⟨833675, by rfl⟩ : syracuseStep 4446269 = 1667351) (by norm_num)
theorem B2964179 : Blo 1975435 2964179 := bstep (se 1 (by rfl) ⟨2223134, by rfl⟩ : syracuseStep 2964179 = 4446269) B4446269
theorem B1976119 : Blo 1975435 1976119 := bstep (se 1 (by rfl) ⟨1482089, by rfl⟩ : syracuseStep 1976119 = 2964179) B2964179
theorem B3334709 : Blo 1975435 3334709 := bbase (se 5 (by rfl) ⟨156314, by rfl⟩ : syracuseStep 3334709 = 312629) (by norm_num)
theorem B2223139 : Blo 1975435 2223139 := bstep (se 1 (by rfl) ⟨1667354, by rfl⟩ : syracuseStep 2223139 = 3334709) B3334709
theorem B2964185 : Blo 1975435 2964185 := bstep (se 2 (by rfl) ⟨1111569, by rfl⟩ : syracuseStep 2964185 = 2223139) B2223139
theorem B1976123 : Blo 1975435 1976123 := bstep (se 1 (by rfl) ⟨1482092, by rfl⟩ : syracuseStep 1976123 = 2964185) B2964185
theorem B5627333 : Blo 1975435 5627333 := bbase (se 4 (by rfl) ⟨527562, by rfl⟩ : syracuseStep 5627333 = 1055125) (by norm_num)
theorem B15006221 : Blo 1975435 15006221 := bstep (se 3 (by rfl) ⟨2813666, by rfl⟩ : syracuseStep 15006221 = 5627333) B5627333
theorem B10004147 : Blo 1975435 10004147 := bstep (se 1 (by rfl) ⟨7503110, by rfl⟩ : syracuseStep 10004147 = 15006221) B15006221
theorem B6669431 : Blo 1975435 6669431 := bstep (se 1 (by rfl) ⟨5002073, by rfl⟩ : syracuseStep 6669431 = 10004147) B10004147
theorem B4446287 : Blo 1975435 4446287 := bstep (se 1 (by rfl) ⟨3334715, by rfl⟩ : syracuseStep 4446287 = 6669431) B6669431
theorem B2964191 : Blo 1975435 2964191 := bstep (se 1 (by rfl) ⟨2223143, by rfl⟩ : syracuseStep 2964191 = 4446287) B4446287
theorem B1976127 : Blo 1975435 1976127 := bstep (se 1 (by rfl) ⟨1482095, by rfl⟩ : syracuseStep 1976127 = 2964191) B2964191
theorem B2964197 : Blo 1975435 2964197 := bbase (se 4 (by rfl) ⟨277893, by rfl⟩ : syracuseStep 2964197 = 555787) (by norm_num)
theorem B1976131 : Blo 1975435 1976131 := bstep (se 1 (by rfl) ⟨1482098, by rfl⟩ : syracuseStep 1976131 = 2964197) B2964197
theorem B3165389 : Blo 1975435 3165389 := bbase (se 3 (by rfl) ⟨593510, by rfl⟩ : syracuseStep 3165389 = 1187021) (by norm_num)
theorem B2110259 : Blo 1975435 2110259 := bstep (se 1 (by rfl) ⟨1582694, by rfl⟩ : syracuseStep 2110259 = 3165389) B3165389
theorem B5627357 : Blo 1975435 5627357 := bstep (se 3 (by rfl) ⟨1055129, by rfl⟩ : syracuseStep 5627357 = 2110259) B2110259
theorem B3751571 : Blo 1975435 3751571 := bstep (se 1 (by rfl) ⟨2813678, by rfl⟩ : syracuseStep 3751571 = 5627357) B5627357
theorem B2501047 : Blo 1975435 2501047 := bstep (se 1 (by rfl) ⟨1875785, by rfl⟩ : syracuseStep 2501047 = 3751571) B3751571
theorem B3334729 : Blo 1975435 3334729 := bstep (se 2 (by rfl) ⟨1250523, by rfl⟩ : syracuseStep 3334729 = 2501047) B2501047
theorem B4446305 : Blo 1975435 4446305 := bstep (se 2 (by rfl) ⟨1667364, by rfl⟩ : syracuseStep 4446305 = 3334729) B3334729
theorem B2964203 : Blo 1975435 2964203 := bstep (se 1 (by rfl) ⟨2223152, by rfl⟩ : syracuseStep 2964203 = 4446305) B4446305
theorem B1976135 : Blo 1975435 1976135 := bstep (se 1 (by rfl) ⟨1482101, by rfl⟩ : syracuseStep 1976135 = 2964203) B2964203
theorem B2223157 : Blo 1975435 2223157 := bbase (se 5 (by rfl) ⟨104210, by rfl⟩ : syracuseStep 2223157 = 208421) (by norm_num)
theorem B2964209 : Blo 1975435 2964209 := bstep (se 2 (by rfl) ⟨1111578, by rfl⟩ : syracuseStep 2964209 = 2223157) B2223157
theorem B1976139 : Blo 1975435 1976139 := bstep (se 1 (by rfl) ⟨1482104, by rfl⟩ : syracuseStep 1976139 = 2964209) B2964209
theorem B2501057 : Blo 1975435 2501057 := bbase (se 2 (by rfl) ⟨937896, by rfl⟩ : syracuseStep 2501057 = 1875793) (by norm_num)
theorem B6669485 : Blo 1975435 6669485 := bstep (se 3 (by rfl) ⟨1250528, by rfl⟩ : syracuseStep 6669485 = 2501057) B2501057
theorem B4446323 : Blo 1975435 4446323 := bstep (se 1 (by rfl) ⟨3334742, by rfl⟩ : syracuseStep 4446323 = 6669485) B6669485
theorem B2964215 : Blo 1975435 2964215 := bstep (se 1 (by rfl) ⟨2223161, by rfl⟩ : syracuseStep 2964215 = 4446323) B4446323
theorem B1976143 : Blo 1975435 1976143 := bstep (se 1 (by rfl) ⟨1482107, by rfl⟩ : syracuseStep 1976143 = 2964215) B2964215
theorem B2964221 : Blo 1975435 2964221 := bbase (se 3 (by rfl) ⟨555791, by rfl⟩ : syracuseStep 2964221 = 1111583) (by norm_num)
theorem B1976147 : Blo 1975435 1976147 := bstep (se 1 (by rfl) ⟨1482110, by rfl⟩ : syracuseStep 1976147 = 2964221) B2964221
theorem B4446341 : Blo 1975435 4446341 := bbase (se 4 (by rfl) ⟨416844, by rfl⟩ : syracuseStep 4446341 = 833689) (by norm_num)
theorem B2964227 : Blo 1975435 2964227 := bstep (se 1 (by rfl) ⟨2223170, by rfl⟩ : syracuseStep 2964227 = 4446341) B4446341
theorem B1976151 : Blo 1975435 1976151 := bstep (se 1 (by rfl) ⟨1482113, by rfl⟩ : syracuseStep 1976151 = 2964227) B2964227
theorem B3165421 : Blo 1975435 3165421 := bbase (se 3 (by rfl) ⟨593516, by rfl⟩ : syracuseStep 3165421 = 1187033) (by norm_num)
theorem B4220561 : Blo 1975435 4220561 := bstep (se 2 (by rfl) ⟨1582710, by rfl⟩ : syracuseStep 4220561 = 3165421) B3165421
theorem B2813707 : Blo 1975435 2813707 := bstep (se 1 (by rfl) ⟨2110280, by rfl⟩ : syracuseStep 2813707 = 4220561) B4220561
theorem B3751609 : Blo 1975435 3751609 := bstep (se 2 (by rfl) ⟨1406853, by rfl⟩ : syracuseStep 3751609 = 2813707) B2813707
theorem B5002145 : Blo 1975435 5002145 := bstep (se 2 (by rfl) ⟨1875804, by rfl⟩ : syracuseStep 5002145 = 3751609) B3751609
theorem B3334763 : Blo 1975435 3334763 := bstep (se 1 (by rfl) ⟨2501072, by rfl⟩ : syracuseStep 3334763 = 5002145) B5002145
theorem B2223175 : Blo 1975435 2223175 := bstep (se 1 (by rfl) ⟨1667381, by rfl⟩ : syracuseStep 2223175 = 3334763) B3334763
theorem B2964233 : Blo 1975435 2964233 := bstep (se 2 (by rfl) ⟨1111587, by rfl⟩ : syracuseStep 2964233 = 2223175) B2223175
theorem B1976155 : Blo 1975435 1976155 := bstep (se 1 (by rfl) ⟨1482116, by rfl⟩ : syracuseStep 1976155 = 2964233) B2964233
theorem B10004309 : Blo 1975435 10004309 := bbase (se 9 (by rfl) ⟨29309, by rfl⟩ : syracuseStep 10004309 = 58619) (by norm_num)
theorem B6669539 : Blo 1975435 6669539 := bstep (se 1 (by rfl) ⟨5002154, by rfl⟩ : syracuseStep 6669539 = 10004309) B10004309
theorem B4446359 : Blo 1975435 4446359 := bstep (se 1 (by rfl) ⟨3334769, by rfl⟩ : syracuseStep 4446359 = 6669539) B6669539
theorem B2964239 : Blo 1975435 2964239 := bstep (se 1 (by rfl) ⟨2223179, by rfl⟩ : syracuseStep 2964239 = 4446359) B4446359
theorem B1976159 : Blo 1975435 1976159 := bstep (se 1 (by rfl) ⟨1482119, by rfl⟩ : syracuseStep 1976159 = 2964239) B2964239
theorem B2964245 : Blo 1975435 2964245 := bbase (se 6 (by rfl) ⟨69474, by rfl⟩ : syracuseStep 2964245 = 138949) (by norm_num)
theorem B1976163 : Blo 1975435 1976163 := bstep (se 1 (by rfl) ⟨1482122, by rfl⟩ : syracuseStep 1976163 = 2964245) B2964245
theorem B4812941 : Blo 1975435 4812941 := bbase (se 3 (by rfl) ⟨902426, by rfl⟩ : syracuseStep 4812941 = 1804853) (by norm_num)
theorem B3208627 : Blo 1975435 3208627 := bstep (se 1 (by rfl) ⟨2406470, by rfl⟩ : syracuseStep 3208627 = 4812941) B4812941
theorem B4278169 : Blo 1975435 4278169 := bstep (se 2 (by rfl) ⟨1604313, by rfl⟩ : syracuseStep 4278169 = 3208627) B3208627
theorem B5704225 : Blo 1975435 5704225 := bstep (se 2 (by rfl) ⟨2139084, by rfl⟩ : syracuseStep 5704225 = 4278169) B4278169
theorem B121690133 : Blo 1975435 121690133 := bstep (se 6 (by rfl) ⟨2852112, by rfl⟩ : syracuseStep 121690133 = 5704225) B5704225
theorem B81126755 : Blo 1975435 81126755 := bstep (se 1 (by rfl) ⟨60845066, by rfl⟩ : syracuseStep 81126755 = 121690133) B121690133
theorem B54084503 : Blo 1975435 54084503 := bstep (se 1 (by rfl) ⟨40563377, by rfl⟩ : syracuseStep 54084503 = 81126755) B81126755
theorem B36056335 : Blo 1975435 36056335 := bstep (se 1 (by rfl) ⟨27042251, by rfl⟩ : syracuseStep 36056335 = 54084503) B54084503
theorem B48075113 : Blo 1975435 48075113 := bstep (se 2 (by rfl) ⟨18028167, by rfl⟩ : syracuseStep 48075113 = 36056335) B36056335
theorem B32050075 : Blo 1975435 32050075 := bstep (se 1 (by rfl) ⟨24037556, by rfl⟩ : syracuseStep 32050075 = 48075113) B48075113
theorem B42733433 : Blo 1975435 42733433 := bstep (se 2 (by rfl) ⟨16025037, by rfl⟩ : syracuseStep 42733433 = 32050075) B32050075
theorem B28488955 : Blo 1975435 28488955 := bstep (se 1 (by rfl) ⟨21366716, by rfl⟩ : syracuseStep 28488955 = 42733433) B42733433
theorem B37985273 : Blo 1975435 37985273 := bstep (se 2 (by rfl) ⟨14244477, by rfl⟩ : syracuseStep 37985273 = 28488955) B28488955
theorem B25323515 : Blo 1975435 25323515 := bstep (se 1 (by rfl) ⟨18992636, by rfl⟩ : syracuseStep 25323515 = 37985273) B37985273
theorem B16882343 : Blo 1975435 16882343 := bstep (se 1 (by rfl) ⟨12661757, by rfl⟩ : syracuseStep 16882343 = 25323515) B25323515
theorem B11254895 : Blo 1975435 11254895 := bstep (se 1 (by rfl) ⟨8441171, by rfl⟩ : syracuseStep 11254895 = 16882343) B16882343
theorem B7503263 : Blo 1975435 7503263 := bstep (se 1 (by rfl) ⟨5627447, by rfl⟩ : syracuseStep 7503263 = 11254895) B11254895
theorem B5002175 : Blo 1975435 5002175 := bstep (se 1 (by rfl) ⟨3751631, by rfl⟩ : syracuseStep 5002175 = 7503263) B7503263
theorem B3334783 : Blo 1975435 3334783 := bstep (se 1 (by rfl) ⟨2501087, by rfl⟩ : syracuseStep 3334783 = 5002175) B5002175
theorem B4446377 : Blo 1975435 4446377 := bstep (se 2 (by rfl) ⟨1667391, by rfl⟩ : syracuseStep 4446377 = 3334783) B3334783
theorem B2964251 : Blo 1975435 2964251 := bstep (se 1 (by rfl) ⟨2223188, by rfl⟩ : syracuseStep 2964251 = 4446377) B4446377
theorem B1976167 : Blo 1975435 1976167 := bstep (se 1 (by rfl) ⟨1482125, by rfl⟩ : syracuseStep 1976167 = 2964251) B2964251
theorem B2223193 : Blo 1975435 2223193 := bbase (se 2 (by rfl) ⟨833697, by rfl⟩ : syracuseStep 2223193 = 1667395) (by norm_num)
theorem B2964257 : Blo 1975435 2964257 := bstep (se 2 (by rfl) ⟨1111596, by rfl⟩ : syracuseStep 2964257 = 2223193) B2223193
theorem B1976171 : Blo 1975435 1976171 := bstep (se 1 (by rfl) ⟨1482128, by rfl⟩ : syracuseStep 1976171 = 2964257) B2964257
theorem B4006277 : Blo 1975435 4006277 := bbase (se 4 (by rfl) ⟨375588, by rfl⟩ : syracuseStep 4006277 = 751177) (by norm_num)
theorem B2670851 : Blo 1975435 2670851 := bstep (se 1 (by rfl) ⟨2003138, by rfl⟩ : syracuseStep 2670851 = 4006277) B4006277
theorem B7122269 : Blo 1975435 7122269 := bstep (se 3 (by rfl) ⟨1335425, by rfl⟩ : syracuseStep 7122269 = 2670851) B2670851
theorem B4748179 : Blo 1975435 4748179 := bstep (se 1 (by rfl) ⟨3561134, by rfl⟩ : syracuseStep 4748179 = 7122269) B7122269
theorem B6330905 : Blo 1975435 6330905 := bstep (se 2 (by rfl) ⟨2374089, by rfl⟩ : syracuseStep 6330905 = 4748179) B4748179
theorem B4220603 : Blo 1975435 4220603 := bstep (se 1 (by rfl) ⟨3165452, by rfl⟩ : syracuseStep 4220603 = 6330905) B6330905
theorem B2813735 : Blo 1975435 2813735 := bstep (se 1 (by rfl) ⟨2110301, by rfl⟩ : syracuseStep 2813735 = 4220603) B4220603
theorem B7503293 : Blo 1975435 7503293 := bstep (se 3 (by rfl) ⟨1406867, by rfl⟩ : syracuseStep 7503293 = 2813735) B2813735
theorem B5002195 : Blo 1975435 5002195 := bstep (se 1 (by rfl) ⟨3751646, by rfl⟩ : syracuseStep 5002195 = 7503293) B7503293
theorem B6669593 : Blo 1975435 6669593 := bstep (se 2 (by rfl) ⟨2501097, by rfl⟩ : syracuseStep 6669593 = 5002195) B5002195
theorem B4446395 : Blo 1975435 4446395 := bstep (se 1 (by rfl) ⟨3334796, by rfl⟩ : syracuseStep 4446395 = 6669593) B6669593
theorem B2964263 : Blo 1975435 2964263 := bstep (se 1 (by rfl) ⟨2223197, by rfl⟩ : syracuseStep 2964263 = 4446395) B4446395
theorem B1976175 : Blo 1975435 1976175 := bstep (se 1 (by rfl) ⟨1482131, by rfl⟩ : syracuseStep 1976175 = 2964263) B2964263
theorem B2964269 : Blo 1975435 2964269 := bbase (se 3 (by rfl) ⟨555800, by rfl⟩ : syracuseStep 2964269 = 1111601) (by norm_num)
theorem B1976179 : Blo 1975435 1976179 := bstep (se 1 (by rfl) ⟨1482134, by rfl⟩ : syracuseStep 1976179 = 2964269) B2964269
theorem B4446413 : Blo 1975435 4446413 := bbase (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) (by norm_num)
theorem B2964275 : Blo 1975435 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1976183 : Blo 1975435 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B2501113 : Blo 1975435 2501113 := bbase (se 2 (by rfl) ⟨937917, by rfl⟩ : syracuseStep 2501113 = 1875835) (by norm_num)
theorem B3334817 : Blo 1975435 3334817 := bstep (se 2 (by rfl) ⟨1250556, by rfl⟩ : syracuseStep 3334817 = 2501113) B2501113
theorem B2223211 : Blo 1975435 2223211 := bstep (se 1 (by rfl) ⟨1667408, by rfl⟩ : syracuseStep 2223211 = 3334817) B3334817
theorem B2964281 : Blo 1975435 2964281 := bstep (se 2 (by rfl) ⟨1111605, by rfl⟩ : syracuseStep 2964281 = 2223211) B2223211
theorem B1976187 : Blo 1975435 1976187 := bstep (se 1 (by rfl) ⟨1482140, by rfl⟩ : syracuseStep 1976187 = 2964281) B2964281
theorem B7122325 : Blo 1975435 7122325 := bbase (se 6 (by rfl) ⟨166929, by rfl⟩ : syracuseStep 7122325 = 333859) (by norm_num)
theorem B9496433 : Blo 1975435 9496433 := bstep (se 2 (by rfl) ⟨3561162, by rfl⟩ : syracuseStep 9496433 = 7122325) B7122325
theorem B6330955 : Blo 1975435 6330955 := bstep (se 1 (by rfl) ⟨4748216, by rfl⟩ : syracuseStep 6330955 = 9496433) B9496433
theorem B8441273 : Blo 1975435 8441273 := bstep (se 2 (by rfl) ⟨3165477, by rfl⟩ : syracuseStep 8441273 = 6330955) B6330955
theorem B22510061 : Blo 1975435 22510061 := bstep (se 3 (by rfl) ⟨4220636, by rfl⟩ : syracuseStep 22510061 = 8441273) B8441273
theorem B15006707 : Blo 1975435 15006707 := bstep (se 1 (by rfl) ⟨11255030, by rfl⟩ : syracuseStep 15006707 = 22510061) B22510061
theorem B10004471 : Blo 1975435 10004471 := bstep (se 1 (by rfl) ⟨7503353, by rfl⟩ : syracuseStep 10004471 = 15006707) B15006707
theorem B6669647 : Blo 1975435 6669647 := bstep (se 1 (by rfl) ⟨5002235, by rfl⟩ : syracuseStep 6669647 = 10004471) B10004471
theorem B4446431 : Blo 1975435 4446431 := bstep (se 1 (by rfl) ⟨3334823, by rfl⟩ : syracuseStep 4446431 = 6669647) B6669647
theorem B2964287 : Blo 1975435 2964287 := bstep (se 1 (by rfl) ⟨2223215, by rfl⟩ : syracuseStep 2964287 = 4446431) B4446431
theorem B1976191 : Blo 1975435 1976191 := bstep (se 1 (by rfl) ⟨1482143, by rfl⟩ : syracuseStep 1976191 = 2964287) B2964287
theorem B2964293 : Blo 1975435 2964293 := bbase (se 4 (by rfl) ⟨277902, by rfl⟩ : syracuseStep 2964293 = 555805) (by norm_num)
theorem B1976195 : Blo 1975435 1976195 := bstep (se 1 (by rfl) ⟨1482146, by rfl⟩ : syracuseStep 1976195 = 2964293) B2964293
theorem B3334837 : Blo 1975435 3334837 := bbase (se 5 (by rfl) ⟨156320, by rfl⟩ : syracuseStep 3334837 = 312641) (by norm_num)
theorem B4446449 : Blo 1975435 4446449 := bstep (se 2 (by rfl) ⟨1667418, by rfl⟩ : syracuseStep 4446449 = 3334837) B3334837
theorem B2964299 : Blo 1975435 2964299 := bstep (se 1 (by rfl) ⟨2223224, by rfl⟩ : syracuseStep 2964299 = 4446449) B4446449
theorem B1976199 : Blo 1975435 1976199 := bstep (se 1 (by rfl) ⟨1482149, by rfl⟩ : syracuseStep 1976199 = 2964299) B2964299
theorem B2223229 : Blo 1975435 2223229 := bbase (se 3 (by rfl) ⟨416855, by rfl⟩ : syracuseStep 2223229 = 833711) (by norm_num)
theorem B2964305 : Blo 1975435 2964305 := bstep (se 2 (by rfl) ⟨1111614, by rfl⟩ : syracuseStep 2964305 = 2223229) B2223229
theorem B1976203 : Blo 1975435 1976203 := bstep (se 1 (by rfl) ⟨1482152, by rfl⟩ : syracuseStep 1976203 = 2964305) B2964305
theorem B6669701 : Blo 1975435 6669701 := bbase (se 4 (by rfl) ⟨625284, by rfl⟩ : syracuseStep 6669701 = 1250569) (by norm_num)
theorem B4446467 : Blo 1975435 4446467 := bstep (se 1 (by rfl) ⟨3334850, by rfl⟩ : syracuseStep 4446467 = 6669701) B6669701
theorem B2964311 : Blo 1975435 2964311 := bstep (se 1 (by rfl) ⟨2223233, by rfl⟩ : syracuseStep 2964311 = 4446467) B4446467
theorem B1976207 : Blo 1975435 1976207 := bstep (se 1 (by rfl) ⟨1482155, by rfl⟩ : syracuseStep 1976207 = 2964311) B2964311
theorem B2964317 : Blo 1975435 2964317 := bbase (se 3 (by rfl) ⟨555809, by rfl⟩ : syracuseStep 2964317 = 1111619) (by norm_num)
theorem B1976211 : Blo 1975435 1976211 := bstep (se 1 (by rfl) ⟨1482158, by rfl⟩ : syracuseStep 1976211 = 2964317) B2964317
theorem B4446485 : Blo 1975435 4446485 := bbase (se 6 (by rfl) ⟨104214, by rfl⟩ : syracuseStep 4446485 = 208429) (by norm_num)
theorem B2964323 : Blo 1975435 2964323 := bstep (se 1 (by rfl) ⟨2223242, by rfl⟩ : syracuseStep 2964323 = 4446485) B4446485
theorem B1976215 : Blo 1975435 1976215 := bstep (se 1 (by rfl) ⟨1482161, by rfl⟩ : syracuseStep 1976215 = 2964323) B2964323
theorem B7503461 : Blo 1975435 7503461 := bbase (se 4 (by rfl) ⟨703449, by rfl⟩ : syracuseStep 7503461 = 1406899) (by norm_num)
theorem B5002307 : Blo 1975435 5002307 := bstep (se 1 (by rfl) ⟨3751730, by rfl⟩ : syracuseStep 5002307 = 7503461) B7503461
theorem B3334871 : Blo 1975435 3334871 := bstep (se 1 (by rfl) ⟨2501153, by rfl⟩ : syracuseStep 3334871 = 5002307) B5002307
theorem B2223247 : Blo 1975435 2223247 := bstep (se 1 (by rfl) ⟨1667435, by rfl⟩ : syracuseStep 2223247 = 3334871) B3334871
theorem B2964329 : Blo 1975435 2964329 := bstep (se 2 (by rfl) ⟨1111623, by rfl⟩ : syracuseStep 2964329 = 2223247) B2223247
theorem B1976219 : Blo 1975435 1976219 := bstep (se 1 (by rfl) ⟨1482164, by rfl⟩ : syracuseStep 1976219 = 2964329) B2964329
theorem B3561221 : Blo 1975435 3561221 := bbase (se 4 (by rfl) ⟨333864, by rfl⟩ : syracuseStep 3561221 = 667729) (by norm_num)
theorem B2374147 : Blo 1975435 2374147 := bstep (se 1 (by rfl) ⟨1780610, by rfl⟩ : syracuseStep 2374147 = 3561221) B3561221
theorem B3165529 : Blo 1975435 3165529 := bstep (se 2 (by rfl) ⟨1187073, by rfl⟩ : syracuseStep 3165529 = 2374147) B2374147
theorem B4220705 : Blo 1975435 4220705 := bstep (se 2 (by rfl) ⟨1582764, by rfl⟩ : syracuseStep 4220705 = 3165529) B3165529
theorem B11255213 : Blo 1975435 11255213 := bstep (se 3 (by rfl) ⟨2110352, by rfl⟩ : syracuseStep 11255213 = 4220705) B4220705
theorem B7503475 : Blo 1975435 7503475 := bstep (se 1 (by rfl) ⟨5627606, by rfl⟩ : syracuseStep 7503475 = 11255213) B11255213
theorem B10004633 : Blo 1975435 10004633 := bstep (se 2 (by rfl) ⟨3751737, by rfl⟩ : syracuseStep 10004633 = 7503475) B7503475
theorem B6669755 : Blo 1975435 6669755 := bstep (se 1 (by rfl) ⟨5002316, by rfl⟩ : syracuseStep 6669755 = 10004633) B10004633
theorem B4446503 : Blo 1975435 4446503 := bstep (se 1 (by rfl) ⟨3334877, by rfl⟩ : syracuseStep 4446503 = 6669755) B6669755
theorem B2964335 : Blo 1975435 2964335 := bstep (se 1 (by rfl) ⟨2223251, by rfl⟩ : syracuseStep 2964335 = 4446503) B4446503
theorem B1976223 : Blo 1975435 1976223 := bstep (se 1 (by rfl) ⟨1482167, by rfl⟩ : syracuseStep 1976223 = 2964335) B2964335
theorem B2964341 : Blo 1975435 2964341 := bbase (se 5 (by rfl) ⟨138953, by rfl⟩ : syracuseStep 2964341 = 277907) (by norm_num)
theorem B1976227 : Blo 1975435 1976227 := bstep (se 1 (by rfl) ⟨1482170, by rfl⟩ : syracuseStep 1976227 = 2964341) B2964341
theorem B2374157 : Blo 1975435 2374157 := bbase (se 3 (by rfl) ⟨445154, by rfl⟩ : syracuseStep 2374157 = 890309) (by norm_num)
theorem B6331085 : Blo 1975435 6331085 := bstep (se 3 (by rfl) ⟨1187078, by rfl⟩ : syracuseStep 6331085 = 2374157) B2374157
theorem B4220723 : Blo 1975435 4220723 := bstep (se 1 (by rfl) ⟨3165542, by rfl⟩ : syracuseStep 4220723 = 6331085) B6331085
theorem B2813815 : Blo 1975435 2813815 := bstep (se 1 (by rfl) ⟨2110361, by rfl⟩ : syracuseStep 2813815 = 4220723) B4220723
theorem B3751753 : Blo 1975435 3751753 := bstep (se 2 (by rfl) ⟨1406907, by rfl⟩ : syracuseStep 3751753 = 2813815) B2813815
theorem B5002337 : Blo 1975435 5002337 := bstep (se 2 (by rfl) ⟨1875876, by rfl⟩ : syracuseStep 5002337 = 3751753) B3751753
theorem B3334891 : Blo 1975435 3334891 := bstep (se 1 (by rfl) ⟨2501168, by rfl⟩ : syracuseStep 3334891 = 5002337) B5002337
theorem B4446521 : Blo 1975435 4446521 := bstep (se 2 (by rfl) ⟨1667445, by rfl⟩ : syracuseStep 4446521 = 3334891) B3334891
theorem B2964347 : Blo 1975435 2964347 := bstep (se 1 (by rfl) ⟨2223260, by rfl⟩ : syracuseStep 2964347 = 4446521) B4446521
theorem B1976231 : Blo 1975435 1976231 := bstep (se 1 (by rfl) ⟨1482173, by rfl⟩ : syracuseStep 1976231 = 2964347) B2964347
theorem B2223265 : Blo 1975435 2223265 := bbase (se 2 (by rfl) ⟨833724, by rfl⟩ : syracuseStep 2223265 = 1667449) (by norm_num)
theorem B2964353 : Blo 1975435 2964353 := bstep (se 2 (by rfl) ⟨1111632, by rfl⟩ : syracuseStep 2964353 = 2223265) B2223265
theorem B1976235 : Blo 1975435 1976235 := bstep (se 1 (by rfl) ⟨1482176, by rfl⟩ : syracuseStep 1976235 = 2964353) B2964353
theorem B5002357 : Blo 1975435 5002357 := bbase (se 5 (by rfl) ⟨234485, by rfl⟩ : syracuseStep 5002357 = 468971) (by norm_num)
theorem B6669809 : Blo 1975435 6669809 := bstep (se 2 (by rfl) ⟨2501178, by rfl⟩ : syracuseStep 6669809 = 5002357) B5002357
theorem B4446539 : Blo 1975435 4446539 := bstep (se 1 (by rfl) ⟨3334904, by rfl⟩ : syracuseStep 4446539 = 6669809) B6669809
theorem B2964359 : Blo 1975435 2964359 := bstep (se 1 (by rfl) ⟨2223269, by rfl⟩ : syracuseStep 2964359 = 4446539) B4446539
theorem B1976239 : Blo 1975435 1976239 := bstep (se 1 (by rfl) ⟨1482179, by rfl⟩ : syracuseStep 1976239 = 2964359) B2964359
theorem B2964365 : Blo 1975435 2964365 := bbase (se 3 (by rfl) ⟨555818, by rfl⟩ : syracuseStep 2964365 = 1111637) (by norm_num)
theorem B1976243 : Blo 1975435 1976243 := bstep (se 1 (by rfl) ⟨1482182, by rfl⟩ : syracuseStep 1976243 = 2964365) B2964365
theorem B4446557 : Blo 1975435 4446557 := bbase (se 3 (by rfl) ⟨833729, by rfl⟩ : syracuseStep 4446557 = 1667459) (by norm_num)
theorem B2964371 : Blo 1975435 2964371 := bstep (se 1 (by rfl) ⟨2223278, by rfl⟩ : syracuseStep 2964371 = 4446557) B4446557
theorem B1976247 : Blo 1975435 1976247 := bstep (se 1 (by rfl) ⟨1482185, by rfl⟩ : syracuseStep 1976247 = 2964371) B2964371
theorem B3334925 : Blo 1975435 3334925 := bbase (se 3 (by rfl) ⟨625298, by rfl⟩ : syracuseStep 3334925 = 1250597) (by norm_num)
theorem B2223283 : Blo 1975435 2223283 := bstep (se 1 (by rfl) ⟨1667462, by rfl⟩ : syracuseStep 2223283 = 3334925) B3334925
theorem B2964377 : Blo 1975435 2964377 := bstep (se 2 (by rfl) ⟨1111641, by rfl⟩ : syracuseStep 2964377 = 2223283) B2223283
theorem B1976251 : Blo 1975435 1976251 := bstep (se 1 (by rfl) ⟨1482188, by rfl⟩ : syracuseStep 1976251 = 2964377) B2964377
theorem B16883093 : Blo 1975435 16883093 := bbase (se 6 (by rfl) ⟨395697, by rfl⟩ : syracuseStep 16883093 = 791395) (by norm_num)
theorem B11255395 : Blo 1975435 11255395 := bstep (se 1 (by rfl) ⟨8441546, by rfl⟩ : syracuseStep 11255395 = 16883093) B16883093
theorem B15007193 : Blo 1975435 15007193 := bstep (se 2 (by rfl) ⟨5627697, by rfl⟩ : syracuseStep 15007193 = 11255395) B11255395
theorem B10004795 : Blo 1975435 10004795 := bstep (se 1 (by rfl) ⟨7503596, by rfl⟩ : syracuseStep 10004795 = 15007193) B15007193
theorem B6669863 : Blo 1975435 6669863 := bstep (se 1 (by rfl) ⟨5002397, by rfl⟩ : syracuseStep 6669863 = 10004795) B10004795
theorem B4446575 : Blo 1975435 4446575 := bstep (se 1 (by rfl) ⟨3334931, by rfl⟩ : syracuseStep 4446575 = 6669863) B6669863
theorem B2964383 : Blo 1975435 2964383 := bstep (se 1 (by rfl) ⟨2223287, by rfl⟩ : syracuseStep 2964383 = 4446575) B4446575
theorem B1976255 : Blo 1975435 1976255 := bstep (se 1 (by rfl) ⟨1482191, by rfl⟩ : syracuseStep 1976255 = 2964383) B2964383
theorem B2964389 : Blo 1975435 2964389 := bbase (se 4 (by rfl) ⟨277911, by rfl⟩ : syracuseStep 2964389 = 555823) (by norm_num)
theorem B1976259 : Blo 1975435 1976259 := bstep (se 1 (by rfl) ⟨1482194, by rfl⟩ : syracuseStep 1976259 = 2964389) B2964389
theorem B2501209 : Blo 1975435 2501209 := bbase (se 2 (by rfl) ⟨937953, by rfl⟩ : syracuseStep 2501209 = 1875907) (by norm_num)
theorem B3334945 : Blo 1975435 3334945 := bstep (se 2 (by rfl) ⟨1250604, by rfl⟩ : syracuseStep 3334945 = 2501209) B2501209
theorem B4446593 : Blo 1975435 4446593 := bstep (se 2 (by rfl) ⟨1667472, by rfl⟩ : syracuseStep 4446593 = 3334945) B3334945
theorem B2964395 : Blo 1975435 2964395 := bstep (se 1 (by rfl) ⟨2223296, by rfl⟩ : syracuseStep 2964395 = 4446593) B4446593
theorem B1976263 : Blo 1975435 1976263 := bstep (se 1 (by rfl) ⟨1482197, by rfl⟩ : syracuseStep 1976263 = 2964395) B2964395
theorem B2223301 : Blo 1975435 2223301 := bbase (se 4 (by rfl) ⟨208434, by rfl⟩ : syracuseStep 2223301 = 416869) (by norm_num)
theorem B2964401 : Blo 1975435 2964401 := bstep (se 2 (by rfl) ⟨1111650, by rfl⟩ : syracuseStep 2964401 = 2223301) B2223301
theorem B1976267 : Blo 1975435 1976267 := bstep (se 1 (by rfl) ⟨1482200, by rfl⟩ : syracuseStep 1976267 = 2964401) B2964401
theorem B3751829 : Blo 1975435 3751829 := bbase (se 6 (by rfl) ⟨87933, by rfl⟩ : syracuseStep 3751829 = 175867) (by norm_num)
theorem B2501219 : Blo 1975435 2501219 := bstep (se 1 (by rfl) ⟨1875914, by rfl⟩ : syracuseStep 2501219 = 3751829) B3751829
theorem B6669917 : Blo 1975435 6669917 := bstep (se 3 (by rfl) ⟨1250609, by rfl⟩ : syracuseStep 6669917 = 2501219) B2501219
theorem B4446611 : Blo 1975435 4446611 := bstep (se 1 (by rfl) ⟨3334958, by rfl⟩ : syracuseStep 4446611 = 6669917) B6669917
theorem B2964407 : Blo 1975435 2964407 := bstep (se 1 (by rfl) ⟨2223305, by rfl⟩ : syracuseStep 2964407 = 4446611) B4446611
theorem B1976271 : Blo 1975435 1976271 := bstep (se 1 (by rfl) ⟨1482203, by rfl⟩ : syracuseStep 1976271 = 2964407) B2964407
theorem B2964413 : Blo 1975435 2964413 := bbase (se 3 (by rfl) ⟨555827, by rfl⟩ : syracuseStep 2964413 = 1111655) (by norm_num)
theorem B1976275 : Blo 1975435 1976275 := bstep (se 1 (by rfl) ⟨1482206, by rfl⟩ : syracuseStep 1976275 = 2964413) B2964413
theorem B4446629 : Blo 1975435 4446629 := bbase (se 4 (by rfl) ⟨416871, by rfl⟩ : syracuseStep 4446629 = 833743) (by norm_num)
theorem B2964419 : Blo 1975435 2964419 := bstep (se 1 (by rfl) ⟨2223314, by rfl⟩ : syracuseStep 2964419 = 4446629) B4446629
theorem B1976279 : Blo 1975435 1976279 := bstep (se 1 (by rfl) ⟨1482209, by rfl⟩ : syracuseStep 1976279 = 2964419) B2964419
theorem B5002469 : Blo 1975435 5002469 := bbase (se 4 (by rfl) ⟨468981, by rfl⟩ : syracuseStep 5002469 = 937963) (by norm_num)
theorem B3334979 : Blo 1975435 3334979 := bstep (se 1 (by rfl) ⟨2501234, by rfl⟩ : syracuseStep 3334979 = 5002469) B5002469
theorem B2223319 : Blo 1975435 2223319 := bstep (se 1 (by rfl) ⟨1667489, by rfl⟩ : syracuseStep 2223319 = 3334979) B3334979
theorem B2964425 : Blo 1975435 2964425 := bstep (se 2 (by rfl) ⟨1111659, by rfl⟩ : syracuseStep 2964425 = 2223319) B2223319
theorem B1976283 : Blo 1975435 1976283 := bstep (se 1 (by rfl) ⟨1482212, by rfl⟩ : syracuseStep 1976283 = 2964425) B2964425
theorem B2110421 : Blo 1975435 2110421 := bbase (se 7 (by rfl) ⟨24731, by rfl⟩ : syracuseStep 2110421 = 49463) (by norm_num)
theorem B5627789 : Blo 1975435 5627789 := bstep (se 3 (by rfl) ⟨1055210, by rfl⟩ : syracuseStep 5627789 = 2110421) B2110421
theorem B3751859 : Blo 1975435 3751859 := bstep (se 1 (by rfl) ⟨2813894, by rfl⟩ : syracuseStep 3751859 = 5627789) B5627789
theorem B10004957 : Blo 1975435 10004957 := bstep (se 3 (by rfl) ⟨1875929, by rfl⟩ : syracuseStep 10004957 = 3751859) B3751859
theorem B6669971 : Blo 1975435 6669971 := bstep (se 1 (by rfl) ⟨5002478, by rfl⟩ : syracuseStep 6669971 = 10004957) B10004957
theorem B4446647 : Blo 1975435 4446647 := bstep (se 1 (by rfl) ⟨3334985, by rfl⟩ : syracuseStep 4446647 = 6669971) B6669971
theorem B2964431 : Blo 1975435 2964431 := bstep (se 1 (by rfl) ⟨2223323, by rfl⟩ : syracuseStep 2964431 = 4446647) B4446647
theorem B1976287 : Blo 1975435 1976287 := bstep (se 1 (by rfl) ⟨1482215, by rfl⟩ : syracuseStep 1976287 = 2964431) B2964431
theorem B2964437 : Blo 1975435 2964437 := bbase (se 7 (by rfl) ⟨34739, by rfl⟩ : syracuseStep 2964437 = 69479) (by norm_num)
theorem B1976291 : Blo 1975435 1976291 := bstep (se 1 (by rfl) ⟨1482218, by rfl⟩ : syracuseStep 1976291 = 2964437) B2964437
theorem B7503749 : Blo 1975435 7503749 := bbase (se 4 (by rfl) ⟨703476, by rfl⟩ : syracuseStep 7503749 = 1406953) (by norm_num)
theorem B5002499 : Blo 1975435 5002499 := bstep (se 1 (by rfl) ⟨3751874, by rfl⟩ : syracuseStep 5002499 = 7503749) B7503749
theorem B3334999 : Blo 1975435 3334999 := bstep (se 1 (by rfl) ⟨2501249, by rfl⟩ : syracuseStep 3334999 = 5002499) B5002499
theorem B4446665 : Blo 1975435 4446665 := bstep (se 2 (by rfl) ⟨1667499, by rfl⟩ : syracuseStep 4446665 = 3334999) B3334999
theorem B2964443 : Blo 1975435 2964443 := bstep (se 1 (by rfl) ⟨2223332, by rfl⟩ : syracuseStep 2964443 = 4446665) B4446665
theorem B1976295 : Blo 1975435 1976295 := bstep (se 1 (by rfl) ⟨1482221, by rfl⟩ : syracuseStep 1976295 = 2964443) B2964443
theorem B2223337 : Blo 1975435 2223337 := bbase (se 2 (by rfl) ⟨833751, by rfl⟩ : syracuseStep 2223337 = 1667503) (by norm_num)
theorem B2964449 : Blo 1975435 2964449 := bstep (se 2 (by rfl) ⟨1111668, by rfl⟩ : syracuseStep 2964449 = 2223337) B2223337
theorem B1976299 : Blo 1975435 1976299 := bstep (se 1 (by rfl) ⟨1482224, by rfl⟩ : syracuseStep 1976299 = 2964449) B2964449
theorem B11255669 : Blo 1975435 11255669 := bbase (se 5 (by rfl) ⟨527609, by rfl⟩ : syracuseStep 11255669 = 1055219) (by norm_num)
theorem B7503779 : Blo 1975435 7503779 := bstep (se 1 (by rfl) ⟨5627834, by rfl⟩ : syracuseStep 7503779 = 11255669) B11255669
theorem B5002519 : Blo 1975435 5002519 := bstep (se 1 (by rfl) ⟨3751889, by rfl⟩ : syracuseStep 5002519 = 7503779) B7503779
theorem B6670025 : Blo 1975435 6670025 := bstep (se 2 (by rfl) ⟨2501259, by rfl⟩ : syracuseStep 6670025 = 5002519) B5002519
theorem B4446683 : Blo 1975435 4446683 := bstep (se 1 (by rfl) ⟨3335012, by rfl⟩ : syracuseStep 4446683 = 6670025) B6670025
theorem B2964455 : Blo 1975435 2964455 := bstep (se 1 (by rfl) ⟨2223341, by rfl⟩ : syracuseStep 2964455 = 4446683) B4446683
theorem B1976303 : Blo 1975435 1976303 := bstep (se 1 (by rfl) ⟨1482227, by rfl⟩ : syracuseStep 1976303 = 2964455) B2964455
theorem B2964461 : Blo 1975435 2964461 := bbase (se 3 (by rfl) ⟨555836, by rfl⟩ : syracuseStep 2964461 = 1111673) (by norm_num)
theorem B1976307 : Blo 1975435 1976307 := bstep (se 1 (by rfl) ⟨1482230, by rfl⟩ : syracuseStep 1976307 = 2964461) B2964461
theorem B4446701 : Blo 1975435 4446701 := bbase (se 3 (by rfl) ⟨833756, by rfl⟩ : syracuseStep 4446701 = 1667513) (by norm_num)
theorem B2964467 : Blo 1975435 2964467 := bstep (se 1 (by rfl) ⟨2223350, by rfl⟩ : syracuseStep 2964467 = 4446701) B4446701
theorem B1976311 : Blo 1975435 1976311 := bstep (se 1 (by rfl) ⟨1482233, by rfl⟩ : syracuseStep 1976311 = 2964467) B2964467
theorem B9137765 : Blo 1975435 9137765 := bbase (se 4 (by rfl) ⟨856665, by rfl⟩ : syracuseStep 9137765 = 1713331) (by norm_num)
theorem B6091843 : Blo 1975435 6091843 := bstep (se 1 (by rfl) ⟨4568882, by rfl⟩ : syracuseStep 6091843 = 9137765) B9137765
theorem B8122457 : Blo 1975435 8122457 := bstep (se 2 (by rfl) ⟨3045921, by rfl⟩ : syracuseStep 8122457 = 6091843) B6091843
theorem B5414971 : Blo 1975435 5414971 := bstep (se 1 (by rfl) ⟨4061228, by rfl⟩ : syracuseStep 5414971 = 8122457) B8122457
theorem B7219961 : Blo 1975435 7219961 := bstep (se 2 (by rfl) ⟨2707485, by rfl⟩ : syracuseStep 7219961 = 5414971) B5414971
theorem B4813307 : Blo 1975435 4813307 := bstep (se 1 (by rfl) ⟨3609980, by rfl⟩ : syracuseStep 4813307 = 7219961) B7219961
theorem B3208871 : Blo 1975435 3208871 := bstep (se 1 (by rfl) ⟨2406653, by rfl⟩ : syracuseStep 3208871 = 4813307) B4813307
theorem B2139247 : Blo 1975435 2139247 := bstep (se 1 (by rfl) ⟨1604435, by rfl⟩ : syracuseStep 2139247 = 3208871) B3208871
theorem B2852329 : Blo 1975435 2852329 := bstep (se 2 (by rfl) ⟨1069623, by rfl⟩ : syracuseStep 2852329 = 2139247) B2139247
theorem B3803105 : Blo 1975435 3803105 := bstep (se 2 (by rfl) ⟨1426164, by rfl⟩ : syracuseStep 3803105 = 2852329) B2852329
theorem B2535403 : Blo 1975435 2535403 := bstep (se 1 (by rfl) ⟨1901552, by rfl⟩ : syracuseStep 2535403 = 3803105) B3803105
theorem B3380537 : Blo 1975435 3380537 := bstep (se 2 (by rfl) ⟨1267701, by rfl⟩ : syracuseStep 3380537 = 2535403) B2535403
theorem B2253691 : Blo 1975435 2253691 := bstep (se 1 (by rfl) ⟨1690268, by rfl⟩ : syracuseStep 2253691 = 3380537) B3380537
theorem B3004921 : Blo 1975435 3004921 := bstep (se 2 (by rfl) ⟨1126845, by rfl⟩ : syracuseStep 3004921 = 2253691) B2253691
theorem B16026245 : Blo 1975435 16026245 := bstep (se 4 (by rfl) ⟨1502460, by rfl⟩ : syracuseStep 16026245 = 3004921) B3004921
theorem B10684163 : Blo 1975435 10684163 := bstep (se 1 (by rfl) ⟨8013122, by rfl⟩ : syracuseStep 10684163 = 16026245) B16026245
theorem B7122775 : Blo 1975435 7122775 := bstep (se 1 (by rfl) ⟨5342081, by rfl⟩ : syracuseStep 7122775 = 10684163) B10684163
theorem B9497033 : Blo 1975435 9497033 := bstep (se 2 (by rfl) ⟨3561387, by rfl⟩ : syracuseStep 9497033 = 7122775) B7122775
theorem B6331355 : Blo 1975435 6331355 := bstep (se 1 (by rfl) ⟨4748516, by rfl⟩ : syracuseStep 6331355 = 9497033) B9497033
theorem B4220903 : Blo 1975435 4220903 := bstep (se 1 (by rfl) ⟨3165677, by rfl⟩ : syracuseStep 4220903 = 6331355) B6331355
theorem B2813935 : Blo 1975435 2813935 := bstep (se 1 (by rfl) ⟨2110451, by rfl⟩ : syracuseStep 2813935 = 4220903) B4220903
theorem B3751913 : Blo 1975435 3751913 := bstep (se 2 (by rfl) ⟨1406967, by rfl⟩ : syracuseStep 3751913 = 2813935) B2813935
theorem B2501275 : Blo 1975435 2501275 := bstep (se 1 (by rfl) ⟨1875956, by rfl⟩ : syracuseStep 2501275 = 3751913) B3751913
theorem B3335033 : Blo 1975435 3335033 := bstep (se 2 (by rfl) ⟨1250637, by rfl⟩ : syracuseStep 3335033 = 2501275) B2501275
theorem B2223355 : Blo 1975435 2223355 := bstep (se 1 (by rfl) ⟨1667516, by rfl⟩ : syracuseStep 2223355 = 3335033) B3335033
theorem B2964473 : Blo 1975435 2964473 := bstep (se 2 (by rfl) ⟨1111677, by rfl⟩ : syracuseStep 2964473 = 2223355) B2223355
theorem B1976315 : Blo 1975435 1976315 := bstep (se 1 (by rfl) ⟨1482236, by rfl⟩ : syracuseStep 1976315 = 2964473) B2964473
theorem B7318469 : Blo 1975435 7318469 := bbase (se 4 (by rfl) ⟨686106, by rfl⟩ : syracuseStep 7318469 = 1372213) (by norm_num)
theorem B19515917 : Blo 1975435 19515917 := bstep (se 3 (by rfl) ⟨3659234, by rfl⟩ : syracuseStep 19515917 = 7318469) B7318469
theorem B13010611 : Blo 1975435 13010611 := bstep (se 1 (by rfl) ⟨9757958, by rfl⟩ : syracuseStep 13010611 = 19515917) B19515917
theorem B17347481 : Blo 1975435 17347481 := bstep (se 2 (by rfl) ⟨6505305, by rfl⟩ : syracuseStep 17347481 = 13010611) B13010611
theorem B11564987 : Blo 1975435 11564987 := bstep (se 1 (by rfl) ⟨8673740, by rfl⟩ : syracuseStep 11564987 = 17347481) B17347481
theorem B123359861 : Blo 1975435 123359861 := bstep (se 5 (by rfl) ⟨5782493, by rfl⟩ : syracuseStep 123359861 = 11564987) B11564987
theorem B82239907 : Blo 1975435 82239907 := bstep (se 1 (by rfl) ⟨61679930, by rfl⟩ : syracuseStep 82239907 = 123359861) B123359861
theorem B109653209 : Blo 1975435 109653209 := bstep (se 2 (by rfl) ⟨41119953, by rfl⟩ : syracuseStep 109653209 = 82239907) B82239907
theorem B73102139 : Blo 1975435 73102139 := bstep (se 1 (by rfl) ⟨54826604, by rfl⟩ : syracuseStep 73102139 = 109653209) B109653209
theorem B48734759 : Blo 1975435 48734759 := bstep (se 1 (by rfl) ⟨36551069, by rfl⟩ : syracuseStep 48734759 = 73102139) B73102139
theorem B32489839 : Blo 1975435 32489839 := bstep (se 1 (by rfl) ⟨24367379, by rfl⟩ : syracuseStep 32489839 = 48734759) B48734759
theorem B43319785 : Blo 1975435 43319785 := bstep (se 2 (by rfl) ⟨16244919, by rfl⟩ : syracuseStep 43319785 = 32489839) B32489839
theorem B57759713 : Blo 1975435 57759713 := bstep (se 2 (by rfl) ⟨21659892, by rfl⟩ : syracuseStep 57759713 = 43319785) B43319785
theorem B38506475 : Blo 1975435 38506475 := bstep (se 1 (by rfl) ⟨28879856, by rfl⟩ : syracuseStep 38506475 = 57759713) B57759713
theorem B102683933 : Blo 1975435 102683933 := bstep (se 3 (by rfl) ⟨19253237, by rfl⟩ : syracuseStep 102683933 = 38506475) B38506475
theorem B68455955 : Blo 1975435 68455955 := bstep (se 1 (by rfl) ⟨51341966, by rfl⟩ : syracuseStep 68455955 = 102683933) B102683933
theorem B45637303 : Blo 1975435 45637303 := bstep (se 1 (by rfl) ⟨34227977, by rfl⟩ : syracuseStep 45637303 = 68455955) B68455955
theorem B60849737 : Blo 1975435 60849737 := bstep (se 2 (by rfl) ⟨22818651, by rfl⟩ : syracuseStep 60849737 = 45637303) B45637303
theorem B40566491 : Blo 1975435 40566491 := bstep (se 1 (by rfl) ⟨30424868, by rfl⟩ : syracuseStep 40566491 = 60849737) B60849737
theorem B27044327 : Blo 1975435 27044327 := bstep (se 1 (by rfl) ⟨20283245, by rfl⟩ : syracuseStep 27044327 = 40566491) B40566491
theorem B72118205 : Blo 1975435 72118205 := bstep (se 3 (by rfl) ⟨13522163, by rfl⟩ : syracuseStep 72118205 = 27044327) B27044327
theorem B48078803 : Blo 1975435 48078803 := bstep (se 1 (by rfl) ⟨36059102, by rfl⟩ : syracuseStep 48078803 = 72118205) B72118205
theorem B128210141 : Blo 1975435 128210141 := bstep (se 3 (by rfl) ⟨24039401, by rfl⟩ : syracuseStep 128210141 = 48078803) B48078803
theorem B85473427 : Blo 1975435 85473427 := bstep (se 1 (by rfl) ⟨64105070, by rfl⟩ : syracuseStep 85473427 = 128210141) B128210141
theorem B113964569 : Blo 1975435 113964569 := bstep (se 2 (by rfl) ⟨42736713, by rfl⟩ : syracuseStep 113964569 = 85473427) B85473427
theorem B75976379 : Blo 1975435 75976379 := bstep (se 1 (by rfl) ⟨56982284, by rfl⟩ : syracuseStep 75976379 = 113964569) B113964569
theorem B50650919 : Blo 1975435 50650919 := bstep (se 1 (by rfl) ⟨37988189, by rfl⟩ : syracuseStep 50650919 = 75976379) B75976379
theorem B33767279 : Blo 1975435 33767279 := bstep (se 1 (by rfl) ⟨25325459, by rfl⟩ : syracuseStep 33767279 = 50650919) B50650919
theorem B22511519 : Blo 1975435 22511519 := bstep (se 1 (by rfl) ⟨16883639, by rfl⟩ : syracuseStep 22511519 = 33767279) B33767279
theorem B15007679 : Blo 1975435 15007679 := bstep (se 1 (by rfl) ⟨11255759, by rfl⟩ : syracuseStep 15007679 = 22511519) B22511519
theorem B10005119 : Blo 1975435 10005119 := bstep (se 1 (by rfl) ⟨7503839, by rfl⟩ : syracuseStep 10005119 = 15007679) B15007679
theorem B6670079 : Blo 1975435 6670079 := bstep (se 1 (by rfl) ⟨5002559, by rfl⟩ : syracuseStep 6670079 = 10005119) B10005119
theorem B4446719 : Blo 1975435 4446719 := bstep (se 1 (by rfl) ⟨3335039, by rfl⟩ : syracuseStep 4446719 = 6670079) B6670079
theorem B2964479 : Blo 1975435 2964479 := bstep (se 1 (by rfl) ⟨2223359, by rfl⟩ : syracuseStep 2964479 = 4446719) B4446719
theorem B1976319 : Blo 1975435 1976319 := bstep (se 1 (by rfl) ⟨1482239, by rfl⟩ : syracuseStep 1976319 = 2964479) B2964479
theorem B2964485 : Blo 1975435 2964485 := bbase (se 4 (by rfl) ⟨277920, by rfl⟩ : syracuseStep 2964485 = 555841) (by norm_num)
theorem B1976323 : Blo 1975435 1976323 := bstep (se 1 (by rfl) ⟨1482242, by rfl⟩ : syracuseStep 1976323 = 2964485) B2964485
theorem B3335053 : Blo 1975435 3335053 := bbase (se 3 (by rfl) ⟨625322, by rfl⟩ : syracuseStep 3335053 = 1250645) (by norm_num)
theorem B4446737 : Blo 1975435 4446737 := bstep (se 2 (by rfl) ⟨1667526, by rfl⟩ : syracuseStep 4446737 = 3335053) B3335053
theorem B2964491 : Blo 1975435 2964491 := bstep (se 1 (by rfl) ⟨2223368, by rfl⟩ : syracuseStep 2964491 = 4446737) B4446737
theorem B1976327 : Blo 1975435 1976327 := bstep (se 1 (by rfl) ⟨1482245, by rfl⟩ : syracuseStep 1976327 = 2964491) B2964491
theorem B2223373 : Blo 1975435 2223373 := bbase (se 3 (by rfl) ⟨416882, by rfl⟩ : syracuseStep 2223373 = 833765) (by norm_num)
theorem B2964497 : Blo 1975435 2964497 := bstep (se 2 (by rfl) ⟨1111686, by rfl⟩ : syracuseStep 2964497 = 2223373) B2223373
theorem B1976331 : Blo 1975435 1976331 := bstep (se 1 (by rfl) ⟨1482248, by rfl⟩ : syracuseStep 1976331 = 2964497) B2964497
theorem B6670133 : Blo 1975435 6670133 := bbase (se 5 (by rfl) ⟨312662, by rfl⟩ : syracuseStep 6670133 = 625325) (by norm_num)
theorem B4446755 : Blo 1975435 4446755 := bstep (se 1 (by rfl) ⟨3335066, by rfl⟩ : syracuseStep 4446755 = 6670133) B6670133
theorem B2964503 : Blo 1975435 2964503 := bstep (se 1 (by rfl) ⟨2223377, by rfl⟩ : syracuseStep 2964503 = 4446755) B4446755
theorem B1976335 : Blo 1975435 1976335 := bstep (se 1 (by rfl) ⟨1482251, by rfl⟩ : syracuseStep 1976335 = 2964503) B2964503
theorem B2964509 : Blo 1975435 2964509 := bbase (se 3 (by rfl) ⟨555845, by rfl⟩ : syracuseStep 2964509 = 1111691) (by norm_num)
theorem B1976339 : Blo 1975435 1976339 := bstep (se 1 (by rfl) ⟨1482254, by rfl⟩ : syracuseStep 1976339 = 2964509) B2964509
theorem B4446773 : Blo 1975435 4446773 := bbase (se 5 (by rfl) ⟨208442, by rfl⟩ : syracuseStep 4446773 = 416885) (by norm_num)
theorem B2964515 : Blo 1975435 2964515 := bstep (se 1 (by rfl) ⟨2223386, by rfl⟩ : syracuseStep 2964515 = 4446773) B4446773
theorem B1976343 : Blo 1975435 1976343 := bstep (se 1 (by rfl) ⟨1482257, by rfl⟩ : syracuseStep 1976343 = 2964515) B2964515
theorem B8441941 : Blo 1975435 8441941 := bbase (se 8 (by rfl) ⟨49464, by rfl⟩ : syracuseStep 8441941 = 98929) (by norm_num)
theorem B11255921 : Blo 1975435 11255921 := bstep (se 2 (by rfl) ⟨4220970, by rfl⟩ : syracuseStep 11255921 = 8441941) B8441941
theorem B7503947 : Blo 1975435 7503947 := bstep (se 1 (by rfl) ⟨5627960, by rfl⟩ : syracuseStep 7503947 = 11255921) B11255921
theorem B5002631 : Blo 1975435 5002631 := bstep (se 1 (by rfl) ⟨3751973, by rfl⟩ : syracuseStep 5002631 = 7503947) B7503947
theorem B3335087 : Blo 1975435 3335087 := bstep (se 1 (by rfl) ⟨2501315, by rfl⟩ : syracuseStep 3335087 = 5002631) B5002631
theorem B2223391 : Blo 1975435 2223391 := bstep (se 1 (by rfl) ⟨1667543, by rfl⟩ : syracuseStep 2223391 = 3335087) B3335087
theorem B2964521 : Blo 1975435 2964521 := bstep (se 2 (by rfl) ⟨1111695, by rfl⟩ : syracuseStep 2964521 = 2223391) B2223391
theorem B1976347 : Blo 1975435 1976347 := bstep (se 1 (by rfl) ⟨1482260, by rfl⟩ : syracuseStep 1976347 = 2964521) B2964521
theorem B8441957 : Blo 1975435 8441957 := bbase (se 4 (by rfl) ⟨791433, by rfl⟩ : syracuseStep 8441957 = 1582867) (by norm_num)
theorem B5627971 : Blo 1975435 5627971 := bstep (se 1 (by rfl) ⟨4220978, by rfl⟩ : syracuseStep 5627971 = 8441957) B8441957
theorem B7503961 : Blo 1975435 7503961 := bstep (se 2 (by rfl) ⟨2813985, by rfl⟩ : syracuseStep 7503961 = 5627971) B5627971
theorem B10005281 : Blo 1975435 10005281 := bstep (se 2 (by rfl) ⟨3751980, by rfl⟩ : syracuseStep 10005281 = 7503961) B7503961
theorem B6670187 : Blo 1975435 6670187 := bstep (se 1 (by rfl) ⟨5002640, by rfl⟩ : syracuseStep 6670187 = 10005281) B10005281
theorem B4446791 : Blo 1975435 4446791 := bstep (se 1 (by rfl) ⟨3335093, by rfl⟩ : syracuseStep 4446791 = 6670187) B6670187
theorem B2964527 : Blo 1975435 2964527 := bstep (se 1 (by rfl) ⟨2223395, by rfl⟩ : syracuseStep 2964527 = 4446791) B4446791
theorem B1976351 : Blo 1975435 1976351 := bstep (se 1 (by rfl) ⟨1482263, by rfl⟩ : syracuseStep 1976351 = 2964527) B2964527
theorem B2964533 : Blo 1975435 2964533 := bbase (se 5 (by rfl) ⟨138962, by rfl⟩ : syracuseStep 2964533 = 277925) (by norm_num)
theorem B1976355 : Blo 1975435 1976355 := bstep (se 1 (by rfl) ⟨1482266, by rfl⟩ : syracuseStep 1976355 = 2964533) B2964533
theorem B5002661 : Blo 1975435 5002661 := bbase (se 4 (by rfl) ⟨468999, by rfl⟩ : syracuseStep 5002661 = 937999) (by norm_num)
theorem B3335107 : Blo 1975435 3335107 := bstep (se 1 (by rfl) ⟨2501330, by rfl⟩ : syracuseStep 3335107 = 5002661) B5002661
theorem B4446809 : Blo 1975435 4446809 := bstep (se 2 (by rfl) ⟨1667553, by rfl⟩ : syracuseStep 4446809 = 3335107) B3335107
theorem B2964539 : Blo 1975435 2964539 := bstep (se 1 (by rfl) ⟨2223404, by rfl⟩ : syracuseStep 2964539 = 4446809) B4446809
theorem B1976359 : Blo 1975435 1976359 := bstep (se 1 (by rfl) ⟨1482269, by rfl⟩ : syracuseStep 1976359 = 2964539) B2964539
theorem B2223409 : Blo 1975435 2223409 := bbase (se 2 (by rfl) ⟨833778, by rfl⟩ : syracuseStep 2223409 = 1667557) (by norm_num)
theorem B2964545 : Blo 1975435 2964545 := bstep (se 2 (by rfl) ⟨1111704, by rfl⟩ : syracuseStep 2964545 = 2223409) B2223409
theorem B1976363 : Blo 1975435 1976363 := bstep (se 1 (by rfl) ⟨1482272, by rfl⟩ : syracuseStep 1976363 = 2964545) B2964545
theorem B4221013 : Blo 1975435 4221013 := bbase (se 8 (by rfl) ⟨24732, by rfl⟩ : syracuseStep 4221013 = 49465) (by norm_num)
theorem B5628017 : Blo 1975435 5628017 := bstep (se 2 (by rfl) ⟨2110506, by rfl⟩ : syracuseStep 5628017 = 4221013) B4221013
theorem B3752011 : Blo 1975435 3752011 := bstep (se 1 (by rfl) ⟨2814008, by rfl⟩ : syracuseStep 3752011 = 5628017) B5628017
theorem B5002681 : Blo 1975435 5002681 := bstep (se 2 (by rfl) ⟨1876005, by rfl⟩ : syracuseStep 5002681 = 3752011) B3752011
theorem B6670241 : Blo 1975435 6670241 := bstep (se 2 (by rfl) ⟨2501340, by rfl⟩ : syracuseStep 6670241 = 5002681) B5002681
theorem B4446827 : Blo 1975435 4446827 := bstep (se 1 (by rfl) ⟨3335120, by rfl⟩ : syracuseStep 4446827 = 6670241) B6670241
theorem B2964551 : Blo 1975435 2964551 := bstep (se 1 (by rfl) ⟨2223413, by rfl⟩ : syracuseStep 2964551 = 4446827) B4446827
theorem B1976367 : Blo 1975435 1976367 := bstep (se 1 (by rfl) ⟨1482275, by rfl⟩ : syracuseStep 1976367 = 2964551) B2964551
theorem B2964557 : Blo 1975435 2964557 := bbase (se 3 (by rfl) ⟨555854, by rfl⟩ : syracuseStep 2964557 = 1111709) (by norm_num)
theorem B1976371 : Blo 1975435 1976371 := bstep (se 1 (by rfl) ⟨1482278, by rfl⟩ : syracuseStep 1976371 = 2964557) B2964557
theorem B4446845 : Blo 1975435 4446845 := bbase (se 3 (by rfl) ⟨833783, by rfl⟩ : syracuseStep 4446845 = 1667567) (by norm_num)
theorem B2964563 : Blo 1975435 2964563 := bstep (se 1 (by rfl) ⟨2223422, by rfl⟩ : syracuseStep 2964563 = 4446845) B4446845
theorem B1976375 : Blo 1975435 1976375 := bstep (se 1 (by rfl) ⟨1482281, by rfl⟩ : syracuseStep 1976375 = 2964563) B2964563
theorem B3335141 : Blo 1975435 3335141 := bbase (se 4 (by rfl) ⟨312669, by rfl⟩ : syracuseStep 3335141 = 625339) (by norm_num)
theorem B2223427 : Blo 1975435 2223427 := bstep (se 1 (by rfl) ⟨1667570, by rfl⟩ : syracuseStep 2223427 = 3335141) B3335141
theorem B2964569 : Blo 1975435 2964569 := bstep (se 2 (by rfl) ⟨1111713, by rfl⟩ : syracuseStep 2964569 = 2223427) B2223427
theorem B1976379 : Blo 1975435 1976379 := bstep (se 1 (by rfl) ⟨1482284, by rfl⟩ : syracuseStep 1976379 = 2964569) B2964569
theorem B3561509 : Blo 1975435 3561509 := bbase (se 4 (by rfl) ⟨333891, by rfl⟩ : syracuseStep 3561509 = 667783) (by norm_num)
theorem B9497357 : Blo 1975435 9497357 := bstep (se 3 (by rfl) ⟨1780754, by rfl⟩ : syracuseStep 9497357 = 3561509) B3561509
theorem B6331571 : Blo 1975435 6331571 := bstep (se 1 (by rfl) ⟨4748678, by rfl⟩ : syracuseStep 6331571 = 9497357) B9497357
theorem B4221047 : Blo 1975435 4221047 := bstep (se 1 (by rfl) ⟨3165785, by rfl⟩ : syracuseStep 4221047 = 6331571) B6331571
theorem B2814031 : Blo 1975435 2814031 := bstep (se 1 (by rfl) ⟨2110523, by rfl⟩ : syracuseStep 2814031 = 4221047) B4221047
theorem B15008165 : Blo 1975435 15008165 := bstep (se 4 (by rfl) ⟨1407015, by rfl⟩ : syracuseStep 15008165 = 2814031) B2814031
theorem B10005443 : Blo 1975435 10005443 := bstep (se 1 (by rfl) ⟨7504082, by rfl⟩ : syracuseStep 10005443 = 15008165) B15008165
theorem B6670295 : Blo 1975435 6670295 := bstep (se 1 (by rfl) ⟨5002721, by rfl⟩ : syracuseStep 6670295 = 10005443) B10005443
theorem B4446863 : Blo 1975435 4446863 := bstep (se 1 (by rfl) ⟨3335147, by rfl⟩ : syracuseStep 4446863 = 6670295) B6670295
theorem B2964575 : Blo 1975435 2964575 := bstep (se 1 (by rfl) ⟨2223431, by rfl⟩ : syracuseStep 2964575 = 4446863) B4446863
theorem B1976383 : Blo 1975435 1976383 := bstep (se 1 (by rfl) ⟨1482287, by rfl⟩ : syracuseStep 1976383 = 2964575) B2964575
theorem B2964581 : Blo 1975435 2964581 := bbase (se 4 (by rfl) ⟨277929, by rfl⟩ : syracuseStep 2964581 = 555859) (by norm_num)
theorem B1976387 : Blo 1975435 1976387 := bstep (se 1 (by rfl) ⟨1482290, by rfl⟩ : syracuseStep 1976387 = 2964581) B2964581
theorem B6761333 : Blo 1975435 6761333 := bbase (se 5 (by rfl) ⟨316937, by rfl⟩ : syracuseStep 6761333 = 633875) (by norm_num)
theorem B18030221 : Blo 1975435 18030221 := bstep (se 3 (by rfl) ⟨3380666, by rfl⟩ : syracuseStep 18030221 = 6761333) B6761333
theorem B12020147 : Blo 1975435 12020147 := bstep (se 1 (by rfl) ⟨9015110, by rfl⟩ : syracuseStep 12020147 = 18030221) B18030221
theorem B8013431 : Blo 1975435 8013431 := bstep (se 1 (by rfl) ⟨6010073, by rfl⟩ : syracuseStep 8013431 = 12020147) B12020147
theorem B5342287 : Blo 1975435 5342287 := bstep (se 1 (by rfl) ⟨4006715, by rfl⟩ : syracuseStep 5342287 = 8013431) B8013431
theorem B7123049 : Blo 1975435 7123049 := bstep (se 2 (by rfl) ⟨2671143, by rfl⟩ : syracuseStep 7123049 = 5342287) B5342287
theorem B4748699 : Blo 1975435 4748699 := bstep (se 1 (by rfl) ⟨3561524, by rfl⟩ : syracuseStep 4748699 = 7123049) B7123049
theorem B3165799 : Blo 1975435 3165799 := bstep (se 1 (by rfl) ⟨2374349, by rfl⟩ : syracuseStep 3165799 = 4748699) B4748699
theorem B4221065 : Blo 1975435 4221065 := bstep (se 2 (by rfl) ⟨1582899, by rfl⟩ : syracuseStep 4221065 = 3165799) B3165799
theorem B2814043 : Blo 1975435 2814043 := bstep (se 1 (by rfl) ⟨2110532, by rfl⟩ : syracuseStep 2814043 = 4221065) B4221065
theorem B3752057 : Blo 1975435 3752057 := bstep (se 2 (by rfl) ⟨1407021, by rfl⟩ : syracuseStep 3752057 = 2814043) B2814043
theorem B2501371 : Blo 1975435 2501371 := bstep (se 1 (by rfl) ⟨1876028, by rfl⟩ : syracuseStep 2501371 = 3752057) B3752057
theorem B3335161 : Blo 1975435 3335161 := bstep (se 2 (by rfl) ⟨1250685, by rfl⟩ : syracuseStep 3335161 = 2501371) B2501371
theorem B4446881 : Blo 1975435 4446881 := bstep (se 2 (by rfl) ⟨1667580, by rfl⟩ : syracuseStep 4446881 = 3335161) B3335161
theorem B2964587 : Blo 1975435 2964587 := bstep (se 1 (by rfl) ⟨2223440, by rfl⟩ : syracuseStep 2964587 = 4446881) B4446881
theorem B1976391 : Blo 1975435 1976391 := bstep (se 1 (by rfl) ⟨1482293, by rfl⟩ : syracuseStep 1976391 = 2964587) B2964587
theorem B2223445 : Blo 1975435 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B2964593 : Blo 1975435 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B1976395 : Blo 1975435 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B2501381 : Blo 1975435 2501381 := bbase (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) (by norm_num)
theorem B6670349 : Blo 1975435 6670349 := bstep (se 3 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 6670349 = 2501381) B2501381
theorem B4446899 : Blo 1975435 4446899 := bstep (se 1 (by rfl) ⟨3335174, by rfl⟩ : syracuseStep 4446899 = 6670349) B6670349
theorem B2964599 : Blo 1975435 2964599 := bstep (se 1 (by rfl) ⟨2223449, by rfl⟩ : syracuseStep 2964599 = 4446899) B4446899
theorem B1976399 : Blo 1975435 1976399 := bstep (se 1 (by rfl) ⟨1482299, by rfl⟩ : syracuseStep 1976399 = 2964599) B2964599
theorem B2964605 : Blo 1975435 2964605 := bbase (se 3 (by rfl) ⟨555863, by rfl⟩ : syracuseStep 2964605 = 1111727) (by norm_num)
theorem B1976403 : Blo 1975435 1976403 := bstep (se 1 (by rfl) ⟨1482302, by rfl⟩ : syracuseStep 1976403 = 2964605) B2964605
theorem B4446917 : Blo 1975435 4446917 := bbase (se 4 (by rfl) ⟨416898, by rfl⟩ : syracuseStep 4446917 = 833797) (by norm_num)
theorem B2964611 : Blo 1975435 2964611 := bstep (se 1 (by rfl) ⟨2223458, by rfl⟩ : syracuseStep 2964611 = 4446917) B4446917
theorem B1976407 : Blo 1975435 1976407 := bstep (se 1 (by rfl) ⟨1482305, by rfl⟩ : syracuseStep 1976407 = 2964611) B2964611
theorem B8557397 : Blo 1975435 8557397 := bbase (se 9 (by rfl) ⟨25070, by rfl⟩ : syracuseStep 8557397 = 50141) (by norm_num)
theorem B5704931 : Blo 1975435 5704931 := bstep (se 1 (by rfl) ⟨4278698, by rfl⟩ : syracuseStep 5704931 = 8557397) B8557397
theorem B15213149 : Blo 1975435 15213149 := bstep (se 3 (by rfl) ⟨2852465, by rfl⟩ : syracuseStep 15213149 = 5704931) B5704931
theorem B10142099 : Blo 1975435 10142099 := bstep (se 1 (by rfl) ⟨7606574, by rfl⟩ : syracuseStep 10142099 = 15213149) B15213149
theorem B6761399 : Blo 1975435 6761399 := bstep (se 1 (by rfl) ⟨5071049, by rfl⟩ : syracuseStep 6761399 = 10142099) B10142099
theorem B72121589 : Blo 1975435 72121589 := bstep (se 5 (by rfl) ⟨3380699, by rfl⟩ : syracuseStep 72121589 = 6761399) B6761399
theorem B48081059 : Blo 1975435 48081059 := bstep (se 1 (by rfl) ⟨36060794, by rfl⟩ : syracuseStep 48081059 = 72121589) B72121589
theorem B32054039 : Blo 1975435 32054039 := bstep (se 1 (by rfl) ⟨24040529, by rfl⟩ : syracuseStep 32054039 = 48081059) B48081059
theorem B21369359 : Blo 1975435 21369359 := bstep (se 1 (by rfl) ⟨16027019, by rfl⟩ : syracuseStep 21369359 = 32054039) B32054039
theorem B14246239 : Blo 1975435 14246239 := bstep (se 1 (by rfl) ⟨10684679, by rfl⟩ : syracuseStep 14246239 = 21369359) B21369359
theorem B18994985 : Blo 1975435 18994985 := bstep (se 2 (by rfl) ⟨7123119, by rfl⟩ : syracuseStep 18994985 = 14246239) B14246239
theorem B12663323 : Blo 1975435 12663323 := bstep (se 1 (by rfl) ⟨9497492, by rfl⟩ : syracuseStep 12663323 = 18994985) B18994985
theorem B8442215 : Blo 1975435 8442215 := bstep (se 1 (by rfl) ⟨6331661, by rfl⟩ : syracuseStep 8442215 = 12663323) B12663323
theorem B5628143 : Blo 1975435 5628143 := bstep (se 1 (by rfl) ⟨4221107, by rfl⟩ : syracuseStep 5628143 = 8442215) B8442215
theorem B3752095 : Blo 1975435 3752095 := bstep (se 1 (by rfl) ⟨2814071, by rfl⟩ : syracuseStep 3752095 = 5628143) B5628143
theorem B5002793 : Blo 1975435 5002793 := bstep (se 2 (by rfl) ⟨1876047, by rfl⟩ : syracuseStep 5002793 = 3752095) B3752095
theorem B3335195 : Blo 1975435 3335195 := bstep (se 1 (by rfl) ⟨2501396, by rfl⟩ : syracuseStep 3335195 = 5002793) B5002793
theorem B2223463 : Blo 1975435 2223463 := bstep (se 1 (by rfl) ⟨1667597, by rfl⟩ : syracuseStep 2223463 = 3335195) B3335195
theorem B2964617 : Blo 1975435 2964617 := bstep (se 2 (by rfl) ⟨1111731, by rfl⟩ : syracuseStep 2964617 = 2223463) B2223463
theorem B1976411 : Blo 1975435 1976411 := bstep (se 1 (by rfl) ⟨1482308, by rfl⟩ : syracuseStep 1976411 = 2964617) B2964617
theorem B10005605 : Blo 1975435 10005605 := bbase (se 4 (by rfl) ⟨938025, by rfl⟩ : syracuseStep 10005605 = 1876051) (by norm_num)
theorem B6670403 : Blo 1975435 6670403 := bstep (se 1 (by rfl) ⟨5002802, by rfl⟩ : syracuseStep 6670403 = 10005605) B10005605
theorem B4446935 : Blo 1975435 4446935 := bstep (se 1 (by rfl) ⟨3335201, by rfl⟩ : syracuseStep 4446935 = 6670403) B6670403
theorem B2964623 : Blo 1975435 2964623 := bstep (se 1 (by rfl) ⟨2223467, by rfl⟩ : syracuseStep 2964623 = 4446935) B4446935
theorem B1976415 : Blo 1975435 1976415 := bstep (se 1 (by rfl) ⟨1482311, by rfl⟩ : syracuseStep 1976415 = 2964623) B2964623
theorem B2964629 : Blo 1975435 2964629 := bbase (se 6 (by rfl) ⟨69483, by rfl⟩ : syracuseStep 2964629 = 138967) (by norm_num)
theorem B1976419 : Blo 1975435 1976419 := bstep (se 1 (by rfl) ⟨1482314, by rfl⟩ : syracuseStep 1976419 = 2964629) B2964629
theorem B3561581 : Blo 1975435 3561581 := bbase (se 3 (by rfl) ⟨667796, by rfl⟩ : syracuseStep 3561581 = 1335593) (by norm_num)
theorem B9497549 : Blo 1975435 9497549 := bstep (se 3 (by rfl) ⟨1780790, by rfl⟩ : syracuseStep 9497549 = 3561581) B3561581
theorem B6331699 : Blo 1975435 6331699 := bstep (se 1 (by rfl) ⟨4748774, by rfl⟩ : syracuseStep 6331699 = 9497549) B9497549
theorem B8442265 : Blo 1975435 8442265 := bstep (se 2 (by rfl) ⟨3165849, by rfl⟩ : syracuseStep 8442265 = 6331699) B6331699
theorem B11256353 : Blo 1975435 11256353 := bstep (se 2 (by rfl) ⟨4221132, by rfl⟩ : syracuseStep 11256353 = 8442265) B8442265
theorem B7504235 : Blo 1975435 7504235 := bstep (se 1 (by rfl) ⟨5628176, by rfl⟩ : syracuseStep 7504235 = 11256353) B11256353
theorem B5002823 : Blo 1975435 5002823 := bstep (se 1 (by rfl) ⟨3752117, by rfl⟩ : syracuseStep 5002823 = 7504235) B7504235
theorem B3335215 : Blo 1975435 3335215 := bstep (se 1 (by rfl) ⟨2501411, by rfl⟩ : syracuseStep 3335215 = 5002823) B5002823
theorem B4446953 : Blo 1975435 4446953 := bstep (se 2 (by rfl) ⟨1667607, by rfl⟩ : syracuseStep 4446953 = 3335215) B3335215
theorem B2964635 : Blo 1975435 2964635 := bstep (se 1 (by rfl) ⟨2223476, by rfl⟩ : syracuseStep 2964635 = 4446953) B4446953
theorem B1976423 : Blo 1975435 1976423 := bstep (se 1 (by rfl) ⟨1482317, by rfl⟩ : syracuseStep 1976423 = 2964635) B2964635
theorem B2223481 : Blo 1975435 2223481 := bbase (se 2 (by rfl) ⟨833805, by rfl⟩ : syracuseStep 2223481 = 1667611) (by norm_num)
theorem B2964641 : Blo 1975435 2964641 := bstep (se 2 (by rfl) ⟨1111740, by rfl⟩ : syracuseStep 2964641 = 2223481) B2223481
theorem B1976427 : Blo 1975435 1976427 := bstep (se 1 (by rfl) ⟨1482320, by rfl⟩ : syracuseStep 1976427 = 2964641) B2964641
theorem B4507645 : Blo 1975435 4507645 := bbase (se 3 (by rfl) ⟨845183, by rfl⟩ : syracuseStep 4507645 = 1690367) (by norm_num)
theorem B6010193 : Blo 1975435 6010193 := bstep (se 2 (by rfl) ⟨2253822, by rfl⟩ : syracuseStep 6010193 = 4507645) B4507645
theorem B4006795 : Blo 1975435 4006795 := bstep (se 1 (by rfl) ⟨3005096, by rfl⟩ : syracuseStep 4006795 = 6010193) B6010193
theorem B5342393 : Blo 1975435 5342393 := bstep (se 2 (by rfl) ⟨2003397, by rfl⟩ : syracuseStep 5342393 = 4006795) B4006795
theorem B14246381 : Blo 1975435 14246381 := bstep (se 3 (by rfl) ⟨2671196, by rfl⟩ : syracuseStep 14246381 = 5342393) B5342393
theorem B9497587 : Blo 1975435 9497587 := bstep (se 1 (by rfl) ⟨7123190, by rfl⟩ : syracuseStep 9497587 = 14246381) B14246381
theorem B12663449 : Blo 1975435 12663449 := bstep (se 2 (by rfl) ⟨4748793, by rfl⟩ : syracuseStep 12663449 = 9497587) B9497587
theorem B8442299 : Blo 1975435 8442299 := bstep (se 1 (by rfl) ⟨6331724, by rfl⟩ : syracuseStep 8442299 = 12663449) B12663449
theorem B5628199 : Blo 1975435 5628199 := bstep (se 1 (by rfl) ⟨4221149, by rfl⟩ : syracuseStep 5628199 = 8442299) B8442299
theorem B7504265 : Blo 1975435 7504265 := bstep (se 2 (by rfl) ⟨2814099, by rfl⟩ : syracuseStep 7504265 = 5628199) B5628199
theorem B5002843 : Blo 1975435 5002843 := bstep (se 1 (by rfl) ⟨3752132, by rfl⟩ : syracuseStep 5002843 = 7504265) B7504265
theorem B6670457 : Blo 1975435 6670457 := bstep (se 2 (by rfl) ⟨2501421, by rfl⟩ : syracuseStep 6670457 = 5002843) B5002843
theorem B4446971 : Blo 1975435 4446971 := bstep (se 1 (by rfl) ⟨3335228, by rfl⟩ : syracuseStep 4446971 = 6670457) B6670457
theorem B2964647 : Blo 1975435 2964647 := bstep (se 1 (by rfl) ⟨2223485, by rfl⟩ : syracuseStep 2964647 = 4446971) B4446971
theorem B1976431 : Blo 1975435 1976431 := bstep (se 1 (by rfl) ⟨1482323, by rfl⟩ : syracuseStep 1976431 = 2964647) B2964647
theorem B2964653 : Blo 1975435 2964653 := bbase (se 3 (by rfl) ⟨555872, by rfl⟩ : syracuseStep 2964653 = 1111745) (by norm_num)
theorem B1976435 : Blo 1975435 1976435 := bstep (se 1 (by rfl) ⟨1482326, by rfl⟩ : syracuseStep 1976435 = 2964653) B2964653
theorem B4446989 : Blo 1975435 4446989 := bbase (se 3 (by rfl) ⟨833810, by rfl⟩ : syracuseStep 4446989 = 1667621) (by norm_num)
theorem B2964659 : Blo 1975435 2964659 := bstep (se 1 (by rfl) ⟨2223494, by rfl⟩ : syracuseStep 2964659 = 4446989) B4446989
theorem B1976439 : Blo 1975435 1976439 := bstep (se 1 (by rfl) ⟨1482329, by rfl⟩ : syracuseStep 1976439 = 2964659) B2964659
theorem B2501437 : Blo 1975435 2501437 := bbase (se 3 (by rfl) ⟨469019, by rfl⟩ : syracuseStep 2501437 = 938039) (by norm_num)
theorem B3335249 : Blo 1975435 3335249 := bstep (se 2 (by rfl) ⟨1250718, by rfl⟩ : syracuseStep 3335249 = 2501437) B2501437
theorem B2223499 : Blo 1975435 2223499 := bstep (se 1 (by rfl) ⟨1667624, by rfl⟩ : syracuseStep 2223499 = 3335249) B3335249
theorem B2964665 : Blo 1975435 2964665 := bstep (se 2 (by rfl) ⟨1111749, by rfl⟩ : syracuseStep 2964665 = 2223499) B2223499
theorem B1976443 : Blo 1975435 1976443 := bstep (se 1 (by rfl) ⟨1482332, by rfl⟩ : syracuseStep 1976443 = 2964665) B2964665
theorem B6505733 : Blo 1975435 6505733 := bbase (se 4 (by rfl) ⟨609912, by rfl⟩ : syracuseStep 6505733 = 1219825) (by norm_num)
theorem B4337155 : Blo 1975435 4337155 := bstep (se 1 (by rfl) ⟨3252866, by rfl⟩ : syracuseStep 4337155 = 6505733) B6505733
theorem B5782873 : Blo 1975435 5782873 := bstep (se 2 (by rfl) ⟨2168577, by rfl⟩ : syracuseStep 5782873 = 4337155) B4337155
theorem B7710497 : Blo 1975435 7710497 := bstep (se 2 (by rfl) ⟨2891436, by rfl⟩ : syracuseStep 7710497 = 5782873) B5782873
theorem B5140331 : Blo 1975435 5140331 := bstep (se 1 (by rfl) ⟨3855248, by rfl⟩ : syracuseStep 5140331 = 7710497) B7710497
theorem B3426887 : Blo 1975435 3426887 := bstep (se 1 (by rfl) ⟨2570165, by rfl⟩ : syracuseStep 3426887 = 5140331) B5140331
theorem B9138365 : Blo 1975435 9138365 := bstep (se 3 (by rfl) ⟨1713443, by rfl⟩ : syracuseStep 9138365 = 3426887) B3426887
theorem B6092243 : Blo 1975435 6092243 := bstep (se 1 (by rfl) ⟨4569182, by rfl⟩ : syracuseStep 6092243 = 9138365) B9138365
theorem B4061495 : Blo 1975435 4061495 := bstep (se 1 (by rfl) ⟨3046121, by rfl⟩ : syracuseStep 4061495 = 6092243) B6092243
theorem B2707663 : Blo 1975435 2707663 := bstep (se 1 (by rfl) ⟨2030747, by rfl⟩ : syracuseStep 2707663 = 4061495) B4061495
theorem B3610217 : Blo 1975435 3610217 := bstep (se 2 (by rfl) ⟨1353831, by rfl⟩ : syracuseStep 3610217 = 2707663) B2707663
theorem B9627245 : Blo 1975435 9627245 := bstep (se 3 (by rfl) ⟨1805108, by rfl⟩ : syracuseStep 9627245 = 3610217) B3610217
theorem B6418163 : Blo 1975435 6418163 := bstep (se 1 (by rfl) ⟨4813622, by rfl⟩ : syracuseStep 6418163 = 9627245) B9627245
theorem B17115101 : Blo 1975435 17115101 := bstep (se 3 (by rfl) ⟨3209081, by rfl⟩ : syracuseStep 17115101 = 6418163) B6418163
theorem B11410067 : Blo 1975435 11410067 := bstep (se 1 (by rfl) ⟨8557550, by rfl⟩ : syracuseStep 11410067 = 17115101) B17115101
theorem B7606711 : Blo 1975435 7606711 := bstep (se 1 (by rfl) ⟨5705033, by rfl⟩ : syracuseStep 7606711 = 11410067) B11410067
theorem B10142281 : Blo 1975435 10142281 := bstep (se 2 (by rfl) ⟨3803355, by rfl⟩ : syracuseStep 10142281 = 7606711) B7606711
theorem B13523041 : Blo 1975435 13523041 := bstep (se 2 (by rfl) ⟨5071140, by rfl⟩ : syracuseStep 13523041 = 10142281) B10142281
theorem B72122885 : Blo 1975435 72122885 := bstep (se 4 (by rfl) ⟨6761520, by rfl⟩ : syracuseStep 72122885 = 13523041) B13523041
theorem B48081923 : Blo 1975435 48081923 := bstep (se 1 (by rfl) ⟨36061442, by rfl⟩ : syracuseStep 48081923 = 72122885) B72122885
theorem B32054615 : Blo 1975435 32054615 := bstep (se 1 (by rfl) ⟨24040961, by rfl⟩ : syracuseStep 32054615 = 48081923) B48081923
theorem B21369743 : Blo 1975435 21369743 := bstep (se 1 (by rfl) ⟨16027307, by rfl⟩ : syracuseStep 21369743 = 32054615) B32054615
theorem B14246495 : Blo 1975435 14246495 := bstep (se 1 (by rfl) ⟨10684871, by rfl⟩ : syracuseStep 14246495 = 21369743) B21369743
theorem B9497663 : Blo 1975435 9497663 := bstep (se 1 (by rfl) ⟨7123247, by rfl⟩ : syracuseStep 9497663 = 14246495) B14246495
theorem B6331775 : Blo 1975435 6331775 := bstep (se 1 (by rfl) ⟨4748831, by rfl⟩ : syracuseStep 6331775 = 9497663) B9497663
theorem B16884733 : Blo 1975435 16884733 := bstep (se 3 (by rfl) ⟨3165887, by rfl⟩ : syracuseStep 16884733 = 6331775) B6331775
theorem B22512977 : Blo 1975435 22512977 := bstep (se 2 (by rfl) ⟨8442366, by rfl⟩ : syracuseStep 22512977 = 16884733) B16884733
theorem B15008651 : Blo 1975435 15008651 := bstep (se 1 (by rfl) ⟨11256488, by rfl⟩ : syracuseStep 15008651 = 22512977) B22512977
theorem B10005767 : Blo 1975435 10005767 := bstep (se 1 (by rfl) ⟨7504325, by rfl⟩ : syracuseStep 10005767 = 15008651) B15008651
theorem B6670511 : Blo 1975435 6670511 := bstep (se 1 (by rfl) ⟨5002883, by rfl⟩ : syracuseStep 6670511 = 10005767) B10005767
theorem B4447007 : Blo 1975435 4447007 := bstep (se 1 (by rfl) ⟨3335255, by rfl⟩ : syracuseStep 4447007 = 6670511) B6670511
theorem B2964671 : Blo 1975435 2964671 := bstep (se 1 (by rfl) ⟨2223503, by rfl⟩ : syracuseStep 2964671 = 4447007) B4447007
theorem B1976447 : Blo 1975435 1976447 := bstep (se 1 (by rfl) ⟨1482335, by rfl⟩ : syracuseStep 1976447 = 2964671) B2964671
theorem B2964677 : Blo 1975435 2964677 := bbase (se 4 (by rfl) ⟨277938, by rfl⟩ : syracuseStep 2964677 = 555877) (by norm_num)
theorem B1976451 : Blo 1975435 1976451 := bstep (se 1 (by rfl) ⟨1482338, by rfl⟩ : syracuseStep 1976451 = 2964677) B2964677
theorem B3335269 : Blo 1975435 3335269 := bbase (se 4 (by rfl) ⟨312681, by rfl⟩ : syracuseStep 3335269 = 625363) (by norm_num)
theorem B4447025 : Blo 1975435 4447025 := bstep (se 2 (by rfl) ⟨1667634, by rfl⟩ : syracuseStep 4447025 = 3335269) B3335269
theorem B2964683 : Blo 1975435 2964683 := bstep (se 1 (by rfl) ⟨2223512, by rfl⟩ : syracuseStep 2964683 = 4447025) B4447025
theorem B1976455 : Blo 1975435 1976455 := bstep (se 1 (by rfl) ⟨1482341, by rfl⟩ : syracuseStep 1976455 = 2964683) B2964683
theorem B2223517 : Blo 1975435 2223517 := bbase (se 3 (by rfl) ⟨416909, by rfl⟩ : syracuseStep 2223517 = 833819) (by norm_num)
theorem B2964689 : Blo 1975435 2964689 := bstep (se 2 (by rfl) ⟨1111758, by rfl⟩ : syracuseStep 2964689 = 2223517) B2223517
theorem B1976459 : Blo 1975435 1976459 := bstep (se 1 (by rfl) ⟨1482344, by rfl⟩ : syracuseStep 1976459 = 2964689) B2964689
theorem B6670565 : Blo 1975435 6670565 := bbase (se 4 (by rfl) ⟨625365, by rfl⟩ : syracuseStep 6670565 = 1250731) (by norm_num)
theorem B4447043 : Blo 1975435 4447043 := bstep (se 1 (by rfl) ⟨3335282, by rfl⟩ : syracuseStep 4447043 = 6670565) B6670565
theorem B2964695 : Blo 1975435 2964695 := bstep (se 1 (by rfl) ⟨2223521, by rfl⟩ : syracuseStep 2964695 = 4447043) B4447043
theorem B1976463 : Blo 1975435 1976463 := bstep (se 1 (by rfl) ⟨1482347, by rfl⟩ : syracuseStep 1976463 = 2964695) B2964695
theorem B2964701 : Blo 1975435 2964701 := bbase (se 3 (by rfl) ⟨555881, by rfl⟩ : syracuseStep 2964701 = 1111763) (by norm_num)
theorem B1976467 : Blo 1975435 1976467 := bstep (se 1 (by rfl) ⟨1482350, by rfl⟩ : syracuseStep 1976467 = 2964701) B2964701
theorem B4447061 : Blo 1975435 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B2964707 : Blo 1975435 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B1976471 : Blo 1975435 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B5628325 : Blo 1975435 5628325 := bbase (se 4 (by rfl) ⟨527655, by rfl⟩ : syracuseStep 5628325 = 1055311) (by norm_num)
theorem B7504433 : Blo 1975435 7504433 := bstep (se 2 (by rfl) ⟨2814162, by rfl⟩ : syracuseStep 7504433 = 5628325) B5628325
theorem B5002955 : Blo 1975435 5002955 := bstep (se 1 (by rfl) ⟨3752216, by rfl⟩ : syracuseStep 5002955 = 7504433) B7504433
theorem B3335303 : Blo 1975435 3335303 := bstep (se 1 (by rfl) ⟨2501477, by rfl⟩ : syracuseStep 3335303 = 5002955) B5002955
theorem B2223535 : Blo 1975435 2223535 := bstep (se 1 (by rfl) ⟨1667651, by rfl⟩ : syracuseStep 2223535 = 3335303) B3335303
theorem B2964713 : Blo 1975435 2964713 := bstep (se 2 (by rfl) ⟨1111767, by rfl⟩ : syracuseStep 2964713 = 2223535) B2223535
theorem B1976475 : Blo 1975435 1976475 := bstep (se 1 (by rfl) ⟨1482356, by rfl⟩ : syracuseStep 1976475 = 2964713) B2964713
theorem B2671261 : Blo 1975435 2671261 := bbase (se 3 (by rfl) ⟨500861, by rfl⟩ : syracuseStep 2671261 = 1001723) (by norm_num)
theorem B56986901 : Blo 1975435 56986901 := bstep (se 6 (by rfl) ⟨1335630, by rfl⟩ : syracuseStep 56986901 = 2671261) B2671261
theorem B37991267 : Blo 1975435 37991267 := bstep (se 1 (by rfl) ⟨28493450, by rfl⟩ : syracuseStep 37991267 = 56986901) B56986901
theorem B25327511 : Blo 1975435 25327511 := bstep (se 1 (by rfl) ⟨18995633, by rfl⟩ : syracuseStep 25327511 = 37991267) B37991267
theorem B16885007 : Blo 1975435 16885007 := bstep (se 1 (by rfl) ⟨12663755, by rfl⟩ : syracuseStep 16885007 = 25327511) B25327511
theorem B11256671 : Blo 1975435 11256671 := bstep (se 1 (by rfl) ⟨8442503, by rfl⟩ : syracuseStep 11256671 = 16885007) B16885007
theorem B7504447 : Blo 1975435 7504447 := bstep (se 1 (by rfl) ⟨5628335, by rfl⟩ : syracuseStep 7504447 = 11256671) B11256671
theorem B10005929 : Blo 1975435 10005929 := bstep (se 2 (by rfl) ⟨3752223, by rfl⟩ : syracuseStep 10005929 = 7504447) B7504447
theorem B6670619 : Blo 1975435 6670619 := bstep (se 1 (by rfl) ⟨5002964, by rfl⟩ : syracuseStep 6670619 = 10005929) B10005929
theorem B4447079 : Blo 1975435 4447079 := bstep (se 1 (by rfl) ⟨3335309, by rfl⟩ : syracuseStep 4447079 = 6670619) B6670619
theorem B2964719 : Blo 1975435 2964719 := bstep (se 1 (by rfl) ⟨2223539, by rfl⟩ : syracuseStep 2964719 = 4447079) B4447079
theorem B1976479 : Blo 1975435 1976479 := bstep (se 1 (by rfl) ⟨1482359, by rfl⟩ : syracuseStep 1976479 = 2964719) B2964719
theorem B2964725 : Blo 1975435 2964725 := bbase (se 5 (by rfl) ⟨138971, by rfl⟩ : syracuseStep 2964725 = 277943) (by norm_num)
theorem B1976483 : Blo 1975435 1976483 := bstep (se 1 (by rfl) ⟨1482362, by rfl⟩ : syracuseStep 1976483 = 2964725) B2964725
theorem B4006909 : Blo 1975435 4006909 := bbase (se 3 (by rfl) ⟨751295, by rfl⟩ : syracuseStep 4006909 = 1502591) (by norm_num)
theorem B5342545 : Blo 1975435 5342545 := bstep (se 2 (by rfl) ⟨2003454, by rfl⟩ : syracuseStep 5342545 = 4006909) B4006909
theorem B7123393 : Blo 1975435 7123393 := bstep (se 2 (by rfl) ⟨2671272, by rfl⟩ : syracuseStep 7123393 = 5342545) B5342545
theorem B9497857 : Blo 1975435 9497857 := bstep (se 2 (by rfl) ⟨3561696, by rfl⟩ : syracuseStep 9497857 = 7123393) B7123393
theorem B12663809 : Blo 1975435 12663809 := bstep (se 2 (by rfl) ⟨4748928, by rfl⟩ : syracuseStep 12663809 = 9497857) B9497857
theorem B8442539 : Blo 1975435 8442539 := bstep (se 1 (by rfl) ⟨6331904, by rfl⟩ : syracuseStep 8442539 = 12663809) B12663809
theorem B5628359 : Blo 1975435 5628359 := bstep (se 1 (by rfl) ⟨4221269, by rfl⟩ : syracuseStep 5628359 = 8442539) B8442539
theorem B3752239 : Blo 1975435 3752239 := bstep (se 1 (by rfl) ⟨2814179, by rfl⟩ : syracuseStep 3752239 = 5628359) B5628359
theorem B5002985 : Blo 1975435 5002985 := bstep (se 2 (by rfl) ⟨1876119, by rfl⟩ : syracuseStep 5002985 = 3752239) B3752239
theorem B3335323 : Blo 1975435 3335323 := bstep (se 1 (by rfl) ⟨2501492, by rfl⟩ : syracuseStep 3335323 = 5002985) B5002985
theorem B4447097 : Blo 1975435 4447097 := bstep (se 2 (by rfl) ⟨1667661, by rfl⟩ : syracuseStep 4447097 = 3335323) B3335323
theorem B2964731 : Blo 1975435 2964731 := bstep (se 1 (by rfl) ⟨2223548, by rfl⟩ : syracuseStep 2964731 = 4447097) B4447097
theorem B1976487 : Blo 1975435 1976487 := bstep (se 1 (by rfl) ⟨1482365, by rfl⟩ : syracuseStep 1976487 = 2964731) B2964731
theorem B2223553 : Blo 1975435 2223553 := bbase (se 2 (by rfl) ⟨833832, by rfl⟩ : syracuseStep 2223553 = 1667665) (by norm_num)
theorem B2964737 : Blo 1975435 2964737 := bstep (se 2 (by rfl) ⟨1111776, by rfl⟩ : syracuseStep 2964737 = 2223553) B2223553
theorem B1976491 : Blo 1975435 1976491 := bstep (se 1 (by rfl) ⟨1482368, by rfl⟩ : syracuseStep 1976491 = 2964737) B2964737
theorem B5003005 : Blo 1975435 5003005 := bbase (se 3 (by rfl) ⟨938063, by rfl⟩ : syracuseStep 5003005 = 1876127) (by norm_num)
theorem B6670673 : Blo 1975435 6670673 := bstep (se 2 (by rfl) ⟨2501502, by rfl⟩ : syracuseStep 6670673 = 5003005) B5003005
theorem B4447115 : Blo 1975435 4447115 := bstep (se 1 (by rfl) ⟨3335336, by rfl⟩ : syracuseStep 4447115 = 6670673) B6670673
theorem B2964743 : Blo 1975435 2964743 := bstep (se 1 (by rfl) ⟨2223557, by rfl⟩ : syracuseStep 2964743 = 4447115) B4447115
theorem B1976495 : Blo 1975435 1976495 := bstep (se 1 (by rfl) ⟨1482371, by rfl⟩ : syracuseStep 1976495 = 2964743) B2964743
theorem B2964749 : Blo 1975435 2964749 := bbase (se 3 (by rfl) ⟨555890, by rfl⟩ : syracuseStep 2964749 = 1111781) (by norm_num)
theorem B1976499 : Blo 1975435 1976499 := bstep (se 1 (by rfl) ⟨1482374, by rfl⟩ : syracuseStep 1976499 = 2964749) B2964749
theorem B4447133 : Blo 1975435 4447133 := bbase (se 3 (by rfl) ⟨833837, by rfl⟩ : syracuseStep 4447133 = 1667675) (by norm_num)
theorem B2964755 : Blo 1975435 2964755 := bstep (se 1 (by rfl) ⟨2223566, by rfl⟩ : syracuseStep 2964755 = 4447133) B4447133
theorem B1976503 : Blo 1975435 1976503 := bstep (se 1 (by rfl) ⟨1482377, by rfl⟩ : syracuseStep 1976503 = 2964755) B2964755
theorem B3335357 : Blo 1975435 3335357 := bbase (se 3 (by rfl) ⟨625379, by rfl⟩ : syracuseStep 3335357 = 1250759) (by norm_num)
theorem B2223571 : Blo 1975435 2223571 := bstep (se 1 (by rfl) ⟨1667678, by rfl⟩ : syracuseStep 2223571 = 3335357) B3335357
theorem B2964761 : Blo 1975435 2964761 := bstep (se 2 (by rfl) ⟨1111785, by rfl⟩ : syracuseStep 2964761 = 2223571) B2223571
theorem B1976507 : Blo 1975435 1976507 := bstep (se 1 (by rfl) ⟨1482380, by rfl⟩ : syracuseStep 1976507 = 2964761) B2964761
theorem B11256853 : Blo 1975435 11256853 := bbase (se 6 (by rfl) ⟨263832, by rfl⟩ : syracuseStep 11256853 = 527665) (by norm_num)
theorem B15009137 : Blo 1975435 15009137 := bstep (se 2 (by rfl) ⟨5628426, by rfl⟩ : syracuseStep 15009137 = 11256853) B11256853
theorem B10006091 : Blo 1975435 10006091 := bstep (se 1 (by rfl) ⟨7504568, by rfl⟩ : syracuseStep 10006091 = 15009137) B15009137
theorem B6670727 : Blo 1975435 6670727 := bstep (se 1 (by rfl) ⟨5003045, by rfl⟩ : syracuseStep 6670727 = 10006091) B10006091
theorem B4447151 : Blo 1975435 4447151 := bstep (se 1 (by rfl) ⟨3335363, by rfl⟩ : syracuseStep 4447151 = 6670727) B6670727
theorem B2964767 : Blo 1975435 2964767 := bstep (se 1 (by rfl) ⟨2223575, by rfl⟩ : syracuseStep 2964767 = 4447151) B4447151
theorem B1976511 : Blo 1975435 1976511 := bstep (se 1 (by rfl) ⟨1482383, by rfl⟩ : syracuseStep 1976511 = 2964767) B2964767
theorem B2964773 : Blo 1975435 2964773 := bbase (se 4 (by rfl) ⟨277947, by rfl⟩ : syracuseStep 2964773 = 555895) (by norm_num)
theorem B1976515 : Blo 1975435 1976515 := bstep (se 1 (by rfl) ⟨1482386, by rfl⟩ : syracuseStep 1976515 = 2964773) B2964773
theorem B2501533 : Blo 1975435 2501533 := bbase (se 3 (by rfl) ⟨469037, by rfl⟩ : syracuseStep 2501533 = 938075) (by norm_num)
theorem B3335377 : Blo 1975435 3335377 := bstep (se 2 (by rfl) ⟨1250766, by rfl⟩ : syracuseStep 3335377 = 2501533) B2501533
theorem B4447169 : Blo 1975435 4447169 := bstep (se 2 (by rfl) ⟨1667688, by rfl⟩ : syracuseStep 4447169 = 3335377) B3335377
theorem B2964779 : Blo 1975435 2964779 := bstep (se 1 (by rfl) ⟨2223584, by rfl⟩ : syracuseStep 2964779 = 4447169) B4447169
theorem B1976519 : Blo 1975435 1976519 := bstep (se 1 (by rfl) ⟨1482389, by rfl⟩ : syracuseStep 1976519 = 2964779) B2964779
theorem B2223589 : Blo 1975435 2223589 := bbase (se 4 (by rfl) ⟨208461, by rfl⟩ : syracuseStep 2223589 = 416923) (by norm_num)
theorem B2964785 : Blo 1975435 2964785 := bstep (se 2 (by rfl) ⟨1111794, by rfl⟩ : syracuseStep 2964785 = 2223589) B2223589
theorem B1976523 : Blo 1975435 1976523 := bstep (se 1 (by rfl) ⟨1482392, by rfl⟩ : syracuseStep 1976523 = 2964785) B2964785
theorem B5071349 : Blo 1975435 5071349 := bbase (se 5 (by rfl) ⟨237719, by rfl⟩ : syracuseStep 5071349 = 475439) (by norm_num)
theorem B13523597 : Blo 1975435 13523597 := bstep (se 3 (by rfl) ⟨2535674, by rfl⟩ : syracuseStep 13523597 = 5071349) B5071349
theorem B9015731 : Blo 1975435 9015731 := bstep (se 1 (by rfl) ⟨6761798, by rfl⟩ : syracuseStep 9015731 = 13523597) B13523597
theorem B6010487 : Blo 1975435 6010487 := bstep (se 1 (by rfl) ⟨4507865, by rfl⟩ : syracuseStep 6010487 = 9015731) B9015731
theorem B4006991 : Blo 1975435 4006991 := bstep (se 1 (by rfl) ⟨3005243, by rfl⟩ : syracuseStep 4006991 = 6010487) B6010487
theorem B2671327 : Blo 1975435 2671327 := bstep (se 1 (by rfl) ⟨2003495, by rfl⟩ : syracuseStep 2671327 = 4006991) B4006991
theorem B3561769 : Blo 1975435 3561769 := bstep (se 2 (by rfl) ⟨1335663, by rfl⟩ : syracuseStep 3561769 = 2671327) B2671327
theorem B4749025 : Blo 1975435 4749025 := bstep (se 2 (by rfl) ⟨1780884, by rfl⟩ : syracuseStep 4749025 = 3561769) B3561769
theorem B6332033 : Blo 1975435 6332033 := bstep (se 2 (by rfl) ⟨2374512, by rfl⟩ : syracuseStep 6332033 = 4749025) B4749025
theorem B4221355 : Blo 1975435 4221355 := bstep (se 1 (by rfl) ⟨3166016, by rfl⟩ : syracuseStep 4221355 = 6332033) B6332033
theorem B5628473 : Blo 1975435 5628473 := bstep (se 2 (by rfl) ⟨2110677, by rfl⟩ : syracuseStep 5628473 = 4221355) B4221355
theorem B3752315 : Blo 1975435 3752315 := bstep (se 1 (by rfl) ⟨2814236, by rfl⟩ : syracuseStep 3752315 = 5628473) B5628473
theorem B2501543 : Blo 1975435 2501543 := bstep (se 1 (by rfl) ⟨1876157, by rfl⟩ : syracuseStep 2501543 = 3752315) B3752315
theorem B6670781 : Blo 1975435 6670781 := bstep (se 3 (by rfl) ⟨1250771, by rfl⟩ : syracuseStep 6670781 = 2501543) B2501543
theorem B4447187 : Blo 1975435 4447187 := bstep (se 1 (by rfl) ⟨3335390, by rfl⟩ : syracuseStep 4447187 = 6670781) B6670781
theorem B2964791 : Blo 1975435 2964791 := bstep (se 1 (by rfl) ⟨2223593, by rfl⟩ : syracuseStep 2964791 = 4447187) B4447187
theorem B1976527 : Blo 1975435 1976527 := bstep (se 1 (by rfl) ⟨1482395, by rfl⟩ : syracuseStep 1976527 = 2964791) B2964791
theorem B2964797 : Blo 1975435 2964797 := bbase (se 3 (by rfl) ⟨555899, by rfl⟩ : syracuseStep 2964797 = 1111799) (by norm_num)
theorem B1976531 : Blo 1975435 1976531 := bstep (se 1 (by rfl) ⟨1482398, by rfl⟩ : syracuseStep 1976531 = 2964797) B2964797
theorem B4447205 : Blo 1975435 4447205 := bbase (se 4 (by rfl) ⟨416925, by rfl⟩ : syracuseStep 4447205 = 833851) (by norm_num)
theorem B2964803 : Blo 1975435 2964803 := bstep (se 1 (by rfl) ⟨2223602, by rfl⟩ : syracuseStep 2964803 = 4447205) B4447205
theorem B1976535 : Blo 1975435 1976535 := bstep (se 1 (by rfl) ⟨1482401, by rfl⟩ : syracuseStep 1976535 = 2964803) B2964803
theorem B5003117 : Blo 1975435 5003117 := bbase (se 3 (by rfl) ⟨938084, by rfl⟩ : syracuseStep 5003117 = 1876169) (by norm_num)
theorem B3335411 : Blo 1975435 3335411 := bstep (se 1 (by rfl) ⟨2501558, by rfl⟩ : syracuseStep 3335411 = 5003117) B5003117
theorem B2223607 : Blo 1975435 2223607 := bstep (se 1 (by rfl) ⟨1667705, by rfl⟩ : syracuseStep 2223607 = 3335411) B3335411
theorem B2964809 : Blo 1975435 2964809 := bstep (se 2 (by rfl) ⟨1111803, by rfl⟩ : syracuseStep 2964809 = 2223607) B2223607
theorem B1976539 : Blo 1975435 1976539 := bstep (se 1 (by rfl) ⟨1482404, by rfl⟩ : syracuseStep 1976539 = 2964809) B2964809
theorem B4221389 : Blo 1975435 4221389 := bbase (se 3 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 4221389 = 1583021) (by norm_num)
theorem B2814259 : Blo 1975435 2814259 := bstep (se 1 (by rfl) ⟨2110694, by rfl⟩ : syracuseStep 2814259 = 4221389) B4221389
theorem B3752345 : Blo 1975435 3752345 := bstep (se 2 (by rfl) ⟨1407129, by rfl⟩ : syracuseStep 3752345 = 2814259) B2814259
theorem B10006253 : Blo 1975435 10006253 := bstep (se 3 (by rfl) ⟨1876172, by rfl⟩ : syracuseStep 10006253 = 3752345) B3752345
theorem B6670835 : Blo 1975435 6670835 := bstep (se 1 (by rfl) ⟨5003126, by rfl⟩ : syracuseStep 6670835 = 10006253) B10006253
theorem B4447223 : Blo 1975435 4447223 := bstep (se 1 (by rfl) ⟨3335417, by rfl⟩ : syracuseStep 4447223 = 6670835) B6670835
theorem B2964815 : Blo 1975435 2964815 := bstep (se 1 (by rfl) ⟨2223611, by rfl⟩ : syracuseStep 2964815 = 4447223) B4447223
theorem B1976543 : Blo 1975435 1976543 := bstep (se 1 (by rfl) ⟨1482407, by rfl⟩ : syracuseStep 1976543 = 2964815) B2964815
theorem B2964821 : Blo 1975435 2964821 := bbase (se 11 (by rfl) ⟨2171, by rfl⟩ : syracuseStep 2964821 = 4343) (by norm_num)
theorem B1976547 : Blo 1975435 1976547 := bstep (se 1 (by rfl) ⟨1482410, by rfl⟩ : syracuseStep 1976547 = 2964821) B2964821
theorem B65874005 : Blo 1975435 65874005 := bbase (se 8 (by rfl) ⟨385980, by rfl⟩ : syracuseStep 65874005 = 771961) (by norm_num)
theorem B43916003 : Blo 1975435 43916003 := bstep (se 1 (by rfl) ⟨32937002, by rfl⟩ : syracuseStep 43916003 = 65874005) B65874005
theorem B29277335 : Blo 1975435 29277335 := bstep (se 1 (by rfl) ⟨21958001, by rfl⟩ : syracuseStep 29277335 = 43916003) B43916003
theorem B78072893 : Blo 1975435 78072893 := bstep (se 3 (by rfl) ⟨14638667, by rfl⟩ : syracuseStep 78072893 = 29277335) B29277335
theorem B52048595 : Blo 1975435 52048595 := bstep (se 1 (by rfl) ⟨39036446, by rfl⟩ : syracuseStep 52048595 = 78072893) B78072893
theorem B34699063 : Blo 1975435 34699063 := bstep (se 1 (by rfl) ⟨26024297, by rfl⟩ : syracuseStep 34699063 = 52048595) B52048595
theorem B46265417 : Blo 1975435 46265417 := bstep (se 2 (by rfl) ⟨17349531, by rfl⟩ : syracuseStep 46265417 = 34699063) B34699063
theorem B30843611 : Blo 1975435 30843611 := bstep (se 1 (by rfl) ⟨23132708, by rfl⟩ : syracuseStep 30843611 = 46265417) B46265417
theorem B20562407 : Blo 1975435 20562407 := bstep (se 1 (by rfl) ⟨15421805, by rfl⟩ : syracuseStep 20562407 = 30843611) B30843611
theorem B13708271 : Blo 1975435 13708271 := bstep (se 1 (by rfl) ⟨10281203, by rfl⟩ : syracuseStep 13708271 = 20562407) B20562407
theorem B9138847 : Blo 1975435 9138847 := bstep (se 1 (by rfl) ⟨6854135, by rfl⟩ : syracuseStep 9138847 = 13708271) B13708271
theorem B12185129 : Blo 1975435 12185129 := bstep (se 2 (by rfl) ⟨4569423, by rfl⟩ : syracuseStep 12185129 = 9138847) B9138847
theorem B8123419 : Blo 1975435 8123419 := bstep (se 1 (by rfl) ⟨6092564, by rfl⟩ : syracuseStep 8123419 = 12185129) B12185129
theorem B10831225 : Blo 1975435 10831225 := bstep (se 2 (by rfl) ⟨4061709, by rfl⟩ : syracuseStep 10831225 = 8123419) B8123419
theorem B14441633 : Blo 1975435 14441633 := bstep (se 2 (by rfl) ⟨5415612, by rfl⟩ : syracuseStep 14441633 = 10831225) B10831225
theorem B9627755 : Blo 1975435 9627755 := bstep (se 1 (by rfl) ⟨7220816, by rfl⟩ : syracuseStep 9627755 = 14441633) B14441633
theorem B25674013 : Blo 1975435 25674013 := bstep (se 3 (by rfl) ⟨4813877, by rfl⟩ : syracuseStep 25674013 = 9627755) B9627755
theorem B136928069 : Blo 1975435 136928069 := bstep (se 4 (by rfl) ⟨12837006, by rfl⟩ : syracuseStep 136928069 = 25674013) B25674013
theorem B91285379 : Blo 1975435 91285379 := bstep (se 1 (by rfl) ⟨68464034, by rfl⟩ : syracuseStep 91285379 = 136928069) B136928069
theorem B60856919 : Blo 1975435 60856919 := bstep (se 1 (by rfl) ⟨45642689, by rfl⟩ : syracuseStep 60856919 = 91285379) B91285379
theorem B40571279 : Blo 1975435 40571279 := bstep (se 1 (by rfl) ⟨30428459, by rfl⟩ : syracuseStep 40571279 = 60856919) B60856919
theorem B27047519 : Blo 1975435 27047519 := bstep (se 1 (by rfl) ⟨20285639, by rfl⟩ : syracuseStep 27047519 = 40571279) B40571279
theorem B18031679 : Blo 1975435 18031679 := bstep (se 1 (by rfl) ⟨13523759, by rfl⟩ : syracuseStep 18031679 = 27047519) B27047519
theorem B12021119 : Blo 1975435 12021119 := bstep (se 1 (by rfl) ⟨9015839, by rfl⟩ : syracuseStep 12021119 = 18031679) B18031679
theorem B8014079 : Blo 1975435 8014079 := bstep (se 1 (by rfl) ⟨6010559, by rfl⟩ : syracuseStep 8014079 = 12021119) B12021119
theorem B5342719 : Blo 1975435 5342719 := bstep (se 1 (by rfl) ⟨4007039, by rfl⟩ : syracuseStep 5342719 = 8014079) B8014079
theorem B7123625 : Blo 1975435 7123625 := bstep (se 2 (by rfl) ⟨2671359, by rfl⟩ : syracuseStep 7123625 = 5342719) B5342719
theorem B4749083 : Blo 1975435 4749083 := bstep (se 1 (by rfl) ⟨3561812, by rfl⟩ : syracuseStep 4749083 = 7123625) B7123625
theorem B3166055 : Blo 1975435 3166055 := bstep (se 1 (by rfl) ⟨2374541, by rfl⟩ : syracuseStep 3166055 = 4749083) B4749083
theorem B2110703 : Blo 1975435 2110703 := bstep (se 1 (by rfl) ⟨1583027, by rfl⟩ : syracuseStep 2110703 = 3166055) B3166055
theorem B5628541 : Blo 1975435 5628541 := bstep (se 3 (by rfl) ⟨1055351, by rfl⟩ : syracuseStep 5628541 = 2110703) B2110703
theorem B7504721 : Blo 1975435 7504721 := bstep (se 2 (by rfl) ⟨2814270, by rfl⟩ : syracuseStep 7504721 = 5628541) B5628541
theorem B5003147 : Blo 1975435 5003147 := bstep (se 1 (by rfl) ⟨3752360, by rfl⟩ : syracuseStep 5003147 = 7504721) B7504721
theorem B3335431 : Blo 1975435 3335431 := bstep (se 1 (by rfl) ⟨2501573, by rfl⟩ : syracuseStep 3335431 = 5003147) B5003147
theorem B4447241 : Blo 1975435 4447241 := bstep (se 2 (by rfl) ⟨1667715, by rfl⟩ : syracuseStep 4447241 = 3335431) B3335431
theorem B2964827 : Blo 1975435 2964827 := bstep (se 1 (by rfl) ⟨2223620, by rfl⟩ : syracuseStep 2964827 = 4447241) B4447241
theorem B1976551 : Blo 1975435 1976551 := bstep (se 1 (by rfl) ⟨1482413, by rfl⟩ : syracuseStep 1976551 = 2964827) B2964827
theorem B2223625 : Blo 1975435 2223625 := bbase (se 2 (by rfl) ⟨833859, by rfl⟩ : syracuseStep 2223625 = 1667719) (by norm_num)
theorem B2964833 : Blo 1975435 2964833 := bstep (se 2 (by rfl) ⟨1111812, by rfl⟩ : syracuseStep 2964833 = 2223625) B2223625
theorem B1976555 : Blo 1975435 1976555 := bstep (se 1 (by rfl) ⟨1482416, by rfl⟩ : syracuseStep 1976555 = 2964833) B2964833
theorem B3803573 : Blo 1975435 3803573 := bbase (se 5 (by rfl) ⟨178292, by rfl⟩ : syracuseStep 3803573 = 356585) (by norm_num)
theorem B2535715 : Blo 1975435 2535715 := bstep (se 1 (by rfl) ⟨1901786, by rfl⟩ : syracuseStep 2535715 = 3803573) B3803573
theorem B3380953 : Blo 1975435 3380953 := bstep (se 2 (by rfl) ⟨1267857, by rfl⟩ : syracuseStep 3380953 = 2535715) B2535715
theorem B4507937 : Blo 1975435 4507937 := bstep (se 2 (by rfl) ⟨1690476, by rfl⟩ : syracuseStep 4507937 = 3380953) B3380953
theorem B3005291 : Blo 1975435 3005291 := bstep (se 1 (by rfl) ⟨2253968, by rfl⟩ : syracuseStep 3005291 = 4507937) B4507937
theorem B2003527 : Blo 1975435 2003527 := bstep (se 1 (by rfl) ⟨1502645, by rfl⟩ : syracuseStep 2003527 = 3005291) B3005291
theorem B10685477 : Blo 1975435 10685477 := bstep (se 4 (by rfl) ⟨1001763, by rfl⟩ : syracuseStep 10685477 = 2003527) B2003527
theorem B28494605 : Blo 1975435 28494605 := bstep (se 3 (by rfl) ⟨5342738, by rfl⟩ : syracuseStep 28494605 = 10685477) B10685477
theorem B18996403 : Blo 1975435 18996403 := bstep (se 1 (by rfl) ⟨14247302, by rfl⟩ : syracuseStep 18996403 = 28494605) B28494605
theorem B25328537 : Blo 1975435 25328537 := bstep (se 2 (by rfl) ⟨9498201, by rfl⟩ : syracuseStep 25328537 = 18996403) B18996403
theorem B16885691 : Blo 1975435 16885691 := bstep (se 1 (by rfl) ⟨12664268, by rfl⟩ : syracuseStep 16885691 = 25328537) B25328537
theorem B11257127 : Blo 1975435 11257127 := bstep (se 1 (by rfl) ⟨8442845, by rfl⟩ : syracuseStep 11257127 = 16885691) B16885691
theorem B7504751 : Blo 1975435 7504751 := bstep (se 1 (by rfl) ⟨5628563, by rfl⟩ : syracuseStep 7504751 = 11257127) B11257127
theorem B5003167 : Blo 1975435 5003167 := bstep (se 1 (by rfl) ⟨3752375, by rfl⟩ : syracuseStep 5003167 = 7504751) B7504751
theorem B6670889 : Blo 1975435 6670889 := bstep (se 2 (by rfl) ⟨2501583, by rfl⟩ : syracuseStep 6670889 = 5003167) B5003167
theorem B4447259 : Blo 1975435 4447259 := bstep (se 1 (by rfl) ⟨3335444, by rfl⟩ : syracuseStep 4447259 = 6670889) B6670889
theorem B2964839 : Blo 1975435 2964839 := bstep (se 1 (by rfl) ⟨2223629, by rfl⟩ : syracuseStep 2964839 = 4447259) B4447259
theorem B1976559 : Blo 1975435 1976559 := bstep (se 1 (by rfl) ⟨1482419, by rfl⟩ : syracuseStep 1976559 = 2964839) B2964839
theorem B2964845 : Blo 1975435 2964845 := bbase (se 3 (by rfl) ⟨555908, by rfl⟩ : syracuseStep 2964845 = 1111817) (by norm_num)
theorem B1976563 : Blo 1975435 1976563 := bstep (se 1 (by rfl) ⟨1482422, by rfl⟩ : syracuseStep 1976563 = 2964845) B2964845
theorem B4447277 : Blo 1975435 4447277 := bbase (se 3 (by rfl) ⟨833864, by rfl⟩ : syracuseStep 4447277 = 1667729) (by norm_num)
theorem B2964851 : Blo 1975435 2964851 := bstep (se 1 (by rfl) ⟨2223638, by rfl⟩ : syracuseStep 2964851 = 4447277) B4447277
theorem B1976567 : Blo 1975435 1976567 := bstep (se 1 (by rfl) ⟨1482425, by rfl⟩ : syracuseStep 1976567 = 2964851) B2964851
theorem B5342773 : Blo 1975435 5342773 := bbase (se 5 (by rfl) ⟨250442, by rfl⟩ : syracuseStep 5342773 = 500885) (by norm_num)
theorem B7123697 : Blo 1975435 7123697 := bstep (se 2 (by rfl) ⟨2671386, by rfl⟩ : syracuseStep 7123697 = 5342773) B5342773
theorem B4749131 : Blo 1975435 4749131 := bstep (se 1 (by rfl) ⟨3561848, by rfl⟩ : syracuseStep 4749131 = 7123697) B7123697
theorem B12664349 : Blo 1975435 12664349 := bstep (se 3 (by rfl) ⟨2374565, by rfl⟩ : syracuseStep 12664349 = 4749131) B4749131
theorem B8442899 : Blo 1975435 8442899 := bstep (se 1 (by rfl) ⟨6332174, by rfl⟩ : syracuseStep 8442899 = 12664349) B12664349
theorem B5628599 : Blo 1975435 5628599 := bstep (se 1 (by rfl) ⟨4221449, by rfl⟩ : syracuseStep 5628599 = 8442899) B8442899
theorem B3752399 : Blo 1975435 3752399 := bstep (se 1 (by rfl) ⟨2814299, by rfl⟩ : syracuseStep 3752399 = 5628599) B5628599
theorem B2501599 : Blo 1975435 2501599 := bstep (se 1 (by rfl) ⟨1876199, by rfl⟩ : syracuseStep 2501599 = 3752399) B3752399
theorem B3335465 : Blo 1975435 3335465 := bstep (se 2 (by rfl) ⟨1250799, by rfl⟩ : syracuseStep 3335465 = 2501599) B2501599
theorem B2223643 : Blo 1975435 2223643 := bstep (se 1 (by rfl) ⟨1667732, by rfl⟩ : syracuseStep 2223643 = 3335465) B3335465
theorem B2964857 : Blo 1975435 2964857 := bstep (se 2 (by rfl) ⟨1111821, by rfl⟩ : syracuseStep 2964857 = 2223643) B2223643
theorem B1976571 : Blo 1975435 1976571 := bstep (se 1 (by rfl) ⟨1482428, by rfl⟩ : syracuseStep 1976571 = 2964857) B2964857
theorem B3610453 : Blo 1975435 3610453 := bbase (se 9 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 3610453 = 21155) (by norm_num)
theorem B4813937 : Blo 1975435 4813937 := bstep (se 2 (by rfl) ⟨1805226, by rfl⟩ : syracuseStep 4813937 = 3610453) B3610453
theorem B3209291 : Blo 1975435 3209291 := bstep (se 1 (by rfl) ⟨2406968, by rfl⟩ : syracuseStep 3209291 = 4813937) B4813937
theorem B2139527 : Blo 1975435 2139527 := bstep (se 1 (by rfl) ⟨1604645, by rfl⟩ : syracuseStep 2139527 = 3209291) B3209291
theorem B5705405 : Blo 1975435 5705405 := bstep (se 3 (by rfl) ⟨1069763, by rfl⟩ : syracuseStep 5705405 = 2139527) B2139527
theorem B3803603 : Blo 1975435 3803603 := bstep (se 1 (by rfl) ⟨2852702, by rfl⟩ : syracuseStep 3803603 = 5705405) B5705405
theorem B10142941 : Blo 1975435 10142941 := bstep (se 3 (by rfl) ⟨1901801, by rfl⟩ : syracuseStep 10142941 = 3803603) B3803603
theorem B13523921 : Blo 1975435 13523921 := bstep (se 2 (by rfl) ⟨5071470, by rfl⟩ : syracuseStep 13523921 = 10142941) B10142941
theorem B9015947 : Blo 1975435 9015947 := bstep (se 1 (by rfl) ⟨6761960, by rfl⟩ : syracuseStep 9015947 = 13523921) B13523921
theorem B6010631 : Blo 1975435 6010631 := bstep (se 1 (by rfl) ⟨4507973, by rfl⟩ : syracuseStep 6010631 = 9015947) B9015947
theorem B4007087 : Blo 1975435 4007087 := bstep (se 1 (by rfl) ⟨3005315, by rfl⟩ : syracuseStep 4007087 = 6010631) B6010631
theorem B2671391 : Blo 1975435 2671391 := bstep (se 1 (by rfl) ⟨2003543, by rfl⟩ : syracuseStep 2671391 = 4007087) B4007087
theorem B7123709 : Blo 1975435 7123709 := bstep (se 3 (by rfl) ⟨1335695, by rfl⟩ : syracuseStep 7123709 = 2671391) B2671391
theorem B4749139 : Blo 1975435 4749139 := bstep (se 1 (by rfl) ⟨3561854, by rfl⟩ : syracuseStep 4749139 = 7123709) B7123709
theorem B6332185 : Blo 1975435 6332185 := bstep (se 2 (by rfl) ⟨2374569, by rfl⟩ : syracuseStep 6332185 = 4749139) B4749139
theorem B33771653 : Blo 1975435 33771653 := bstep (se 4 (by rfl) ⟨3166092, by rfl⟩ : syracuseStep 33771653 = 6332185) B6332185
theorem B22514435 : Blo 1975435 22514435 := bstep (se 1 (by rfl) ⟨16885826, by rfl⟩ : syracuseStep 22514435 = 33771653) B33771653
theorem B15009623 : Blo 1975435 15009623 := bstep (se 1 (by rfl) ⟨11257217, by rfl⟩ : syracuseStep 15009623 = 22514435) B22514435
theorem B10006415 : Blo 1975435 10006415 := bstep (se 1 (by rfl) ⟨7504811, by rfl⟩ : syracuseStep 10006415 = 15009623) B15009623
theorem B6670943 : Blo 1975435 6670943 := bstep (se 1 (by rfl) ⟨5003207, by rfl⟩ : syracuseStep 6670943 = 10006415) B10006415
theorem B4447295 : Blo 1975435 4447295 := bstep (se 1 (by rfl) ⟨3335471, by rfl⟩ : syracuseStep 4447295 = 6670943) B6670943
theorem B2964863 : Blo 1975435 2964863 := bstep (se 1 (by rfl) ⟨2223647, by rfl⟩ : syracuseStep 2964863 = 4447295) B4447295
theorem B1976575 : Blo 1975435 1976575 := bstep (se 1 (by rfl) ⟨1482431, by rfl⟩ : syracuseStep 1976575 = 2964863) B2964863
theorem B2964869 : Blo 1975435 2964869 := bbase (se 4 (by rfl) ⟨277956, by rfl⟩ : syracuseStep 2964869 = 555913) (by norm_num)
theorem B1976579 : Blo 1975435 1976579 := bstep (se 1 (by rfl) ⟨1482434, by rfl⟩ : syracuseStep 1976579 = 2964869) B2964869
theorem B3335485 : Blo 1975435 3335485 := bbase (se 3 (by rfl) ⟨625403, by rfl⟩ : syracuseStep 3335485 = 1250807) (by norm_num)
theorem B4447313 : Blo 1975435 4447313 := bstep (se 2 (by rfl) ⟨1667742, by rfl⟩ : syracuseStep 4447313 = 3335485) B3335485
theorem B2964875 : Blo 1975435 2964875 := bstep (se 1 (by rfl) ⟨2223656, by rfl⟩ : syracuseStep 2964875 = 4447313) B4447313
theorem B1976583 : Blo 1975435 1976583 := bstep (se 1 (by rfl) ⟨1482437, by rfl⟩ : syracuseStep 1976583 = 2964875) B2964875
theorem B2223661 : Blo 1975435 2223661 := bbase (se 3 (by rfl) ⟨416936, by rfl⟩ : syracuseStep 2223661 = 833873) (by norm_num)
theorem B2964881 : Blo 1975435 2964881 := bstep (se 2 (by rfl) ⟨1111830, by rfl⟩ : syracuseStep 2964881 = 2223661) B2223661
theorem B1976587 : Blo 1975435 1976587 := bstep (se 1 (by rfl) ⟨1482440, by rfl⟩ : syracuseStep 1976587 = 2964881) B2964881
theorem B6670997 : Blo 1975435 6670997 := bbase (se 6 (by rfl) ⟨156351, by rfl⟩ : syracuseStep 6670997 = 312703) (by norm_num)
theorem B4447331 : Blo 1975435 4447331 := bstep (se 1 (by rfl) ⟨3335498, by rfl⟩ : syracuseStep 4447331 = 6670997) B6670997
theorem B2964887 : Blo 1975435 2964887 := bstep (se 1 (by rfl) ⟨2223665, by rfl⟩ : syracuseStep 2964887 = 4447331) B4447331
theorem B1976591 : Blo 1975435 1976591 := bstep (se 1 (by rfl) ⟨1482443, by rfl⟩ : syracuseStep 1976591 = 2964887) B2964887
theorem B2964893 : Blo 1975435 2964893 := bbase (se 3 (by rfl) ⟨555917, by rfl⟩ : syracuseStep 2964893 = 1111835) (by norm_num)
theorem B1976595 : Blo 1975435 1976595 := bstep (se 1 (by rfl) ⟨1482446, by rfl⟩ : syracuseStep 1976595 = 2964893) B2964893
theorem B4447349 : Blo 1975435 4447349 := bbase (se 5 (by rfl) ⟨208469, by rfl⟩ : syracuseStep 4447349 = 416939) (by norm_num)
theorem B2964899 : Blo 1975435 2964899 := bstep (se 1 (by rfl) ⟨2223674, by rfl⟩ : syracuseStep 2964899 = 4447349) B4447349
theorem B1976599 : Blo 1975435 1976599 := bstep (se 1 (by rfl) ⟨1482449, by rfl⟩ : syracuseStep 1976599 = 2964899) B2964899
theorem B16886069 : Blo 1975435 16886069 := bbase (se 5 (by rfl) ⟨791534, by rfl⟩ : syracuseStep 16886069 = 1583069) (by norm_num)
theorem B11257379 : Blo 1975435 11257379 := bstep (se 1 (by rfl) ⟨8443034, by rfl⟩ : syracuseStep 11257379 = 16886069) B16886069
theorem B7504919 : Blo 1975435 7504919 := bstep (se 1 (by rfl) ⟨5628689, by rfl⟩ : syracuseStep 7504919 = 11257379) B11257379
theorem B5003279 : Blo 1975435 5003279 := bstep (se 1 (by rfl) ⟨3752459, by rfl⟩ : syracuseStep 5003279 = 7504919) B7504919
theorem B3335519 : Blo 1975435 3335519 := bstep (se 1 (by rfl) ⟨2501639, by rfl⟩ : syracuseStep 3335519 = 5003279) B5003279
theorem B2223679 : Blo 1975435 2223679 := bstep (se 1 (by rfl) ⟨1667759, by rfl⟩ : syracuseStep 2223679 = 3335519) B3335519
theorem B2964905 : Blo 1975435 2964905 := bstep (se 2 (by rfl) ⟨1111839, by rfl⟩ : syracuseStep 2964905 = 2223679) B2223679
theorem B1976603 : Blo 1975435 1976603 := bstep (se 1 (by rfl) ⟨1482452, by rfl⟩ : syracuseStep 1976603 = 2964905) B2964905
theorem B7504933 : Blo 1975435 7504933 := bbase (se 4 (by rfl) ⟨703587, by rfl⟩ : syracuseStep 7504933 = 1407175) (by norm_num)
theorem B10006577 : Blo 1975435 10006577 := bstep (se 2 (by rfl) ⟨3752466, by rfl⟩ : syracuseStep 10006577 = 7504933) B7504933
theorem B6671051 : Blo 1975435 6671051 := bstep (se 1 (by rfl) ⟨5003288, by rfl⟩ : syracuseStep 6671051 = 10006577) B10006577
theorem B4447367 : Blo 1975435 4447367 := bstep (se 1 (by rfl) ⟨3335525, by rfl⟩ : syracuseStep 4447367 = 6671051) B6671051
theorem B2964911 : Blo 1975435 2964911 := bstep (se 1 (by rfl) ⟨2223683, by rfl⟩ : syracuseStep 2964911 = 4447367) B4447367
theorem B1976607 : Blo 1975435 1976607 := bstep (se 1 (by rfl) ⟨1482455, by rfl⟩ : syracuseStep 1976607 = 2964911) B2964911
theorem B2964917 : Blo 1975435 2964917 := bbase (se 5 (by rfl) ⟨138980, by rfl⟩ : syracuseStep 2964917 = 277961) (by norm_num)
theorem B1976611 : Blo 1975435 1976611 := bstep (se 1 (by rfl) ⟨1482458, by rfl⟩ : syracuseStep 1976611 = 2964917) B2964917
theorem B5003309 : Blo 1975435 5003309 := bbase (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) (by norm_num)
theorem B3335539 : Blo 1975435 3335539 := bstep (se 1 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 3335539 = 5003309) B5003309
theorem B4447385 : Blo 1975435 4447385 := bstep (se 2 (by rfl) ⟨1667769, by rfl⟩ : syracuseStep 4447385 = 3335539) B3335539
theorem B2964923 : Blo 1975435 2964923 := bstep (se 1 (by rfl) ⟨2223692, by rfl⟩ : syracuseStep 2964923 = 4447385) B4447385
theorem B1976615 : Blo 1975435 1976615 := bstep (se 1 (by rfl) ⟨1482461, by rfl⟩ : syracuseStep 1976615 = 2964923) B2964923
theorem B2223697 : Blo 1975435 2223697 := bbase (se 2 (by rfl) ⟨833886, by rfl⟩ : syracuseStep 2223697 = 1667773) (by norm_num)
theorem B2964929 : Blo 1975435 2964929 := bstep (se 2 (by rfl) ⟨1111848, by rfl⟩ : syracuseStep 2964929 = 2223697) B2223697
theorem B1976619 : Blo 1975435 1976619 := bstep (se 1 (by rfl) ⟨1482464, by rfl⟩ : syracuseStep 1976619 = 2964929) B2964929
theorem B2814373 : Blo 1975435 2814373 := bbase (se 4 (by rfl) ⟨263847, by rfl⟩ : syracuseStep 2814373 = 527695) (by norm_num)
theorem B3752497 : Blo 1975435 3752497 := bstep (se 2 (by rfl) ⟨1407186, by rfl⟩ : syracuseStep 3752497 = 2814373) B2814373
theorem B5003329 : Blo 1975435 5003329 := bstep (se 2 (by rfl) ⟨1876248, by rfl⟩ : syracuseStep 5003329 = 3752497) B3752497
theorem B6671105 : Blo 1975435 6671105 := bstep (se 2 (by rfl) ⟨2501664, by rfl⟩ : syracuseStep 6671105 = 5003329) B5003329
theorem B4447403 : Blo 1975435 4447403 := bstep (se 1 (by rfl) ⟨3335552, by rfl⟩ : syracuseStep 4447403 = 6671105) B6671105
theorem B2964935 : Blo 1975435 2964935 := bstep (se 1 (by rfl) ⟨2223701, by rfl⟩ : syracuseStep 2964935 = 4447403) B4447403
theorem B1976623 : Blo 1975435 1976623 := bstep (se 1 (by rfl) ⟨1482467, by rfl⟩ : syracuseStep 1976623 = 2964935) B2964935
theorem B2964941 : Blo 1975435 2964941 := bbase (se 3 (by rfl) ⟨555926, by rfl⟩ : syracuseStep 2964941 = 1111853) (by norm_num)
theorem B1976627 : Blo 1975435 1976627 := bstep (se 1 (by rfl) ⟨1482470, by rfl⟩ : syracuseStep 1976627 = 2964941) B2964941
theorem B4447421 : Blo 1975435 4447421 := bbase (se 3 (by rfl) ⟨833891, by rfl⟩ : syracuseStep 4447421 = 1667783) (by norm_num)
theorem B2964947 : Blo 1975435 2964947 := bstep (se 1 (by rfl) ⟨2223710, by rfl⟩ : syracuseStep 2964947 = 4447421) B4447421
theorem B1976631 : Blo 1975435 1976631 := bstep (se 1 (by rfl) ⟨1482473, by rfl⟩ : syracuseStep 1976631 = 2964947) B2964947
theorem B3335573 : Blo 1975435 3335573 := bbase (se 6 (by rfl) ⟨78177, by rfl⟩ : syracuseStep 3335573 = 156355) (by norm_num)
theorem B2223715 : Blo 1975435 2223715 := bstep (se 1 (by rfl) ⟨1667786, by rfl⟩ : syracuseStep 2223715 = 3335573) B3335573
theorem B2964953 : Blo 1975435 2964953 := bstep (se 2 (by rfl) ⟨1111857, by rfl⟩ : syracuseStep 2964953 = 2223715) B2223715
theorem B1976635 : Blo 1975435 1976635 := bstep (se 1 (by rfl) ⟨1482476, by rfl⟩ : syracuseStep 1976635 = 2964953) B2964953
theorem B4749293 : Blo 1975435 4749293 := bbase (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) (by norm_num)
theorem B12664781 : Blo 1975435 12664781 := bstep (se 3 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 12664781 = 4749293) B4749293
theorem B8443187 : Blo 1975435 8443187 := bstep (se 1 (by rfl) ⟨6332390, by rfl⟩ : syracuseStep 8443187 = 12664781) B12664781
theorem B5628791 : Blo 1975435 5628791 := bstep (se 1 (by rfl) ⟨4221593, by rfl⟩ : syracuseStep 5628791 = 8443187) B8443187
theorem B15010109 : Blo 1975435 15010109 := bstep (se 3 (by rfl) ⟨2814395, by rfl⟩ : syracuseStep 15010109 = 5628791) B5628791
theorem B10006739 : Blo 1975435 10006739 := bstep (se 1 (by rfl) ⟨7505054, by rfl⟩ : syracuseStep 10006739 = 15010109) B15010109
theorem B6671159 : Blo 1975435 6671159 := bstep (se 1 (by rfl) ⟨5003369, by rfl⟩ : syracuseStep 6671159 = 10006739) B10006739
theorem B4447439 : Blo 1975435 4447439 := bstep (se 1 (by rfl) ⟨3335579, by rfl⟩ : syracuseStep 4447439 = 6671159) B6671159
theorem B2964959 : Blo 1975435 2964959 := bstep (se 1 (by rfl) ⟨2223719, by rfl⟩ : syracuseStep 2964959 = 4447439) B4447439
theorem B1976639 : Blo 1975435 1976639 := bstep (se 1 (by rfl) ⟨1482479, by rfl⟩ : syracuseStep 1976639 = 2964959) B2964959
theorem B2964965 : Blo 1975435 2964965 := bbase (se 4 (by rfl) ⟨277965, by rfl⟩ : syracuseStep 2964965 = 555931) (by norm_num)
theorem B1976643 : Blo 1975435 1976643 := bstep (se 1 (by rfl) ⟨1482482, by rfl⟩ : syracuseStep 1976643 = 2964965) B2964965
theorem B2003617 : Blo 1975435 2003617 := bbase (se 2 (by rfl) ⟨751356, by rfl⟩ : syracuseStep 2003617 = 1502713) (by norm_num)
theorem B2671489 : Blo 1975435 2671489 := bstep (se 2 (by rfl) ⟨1001808, by rfl⟩ : syracuseStep 2671489 = 2003617) B2003617
theorem B3561985 : Blo 1975435 3561985 := bstep (se 2 (by rfl) ⟨1335744, by rfl⟩ : syracuseStep 3561985 = 2671489) B2671489
theorem B18997253 : Blo 1975435 18997253 := bstep (se 4 (by rfl) ⟨1780992, by rfl⟩ : syracuseStep 18997253 = 3561985) B3561985
theorem B12664835 : Blo 1975435 12664835 := bstep (se 1 (by rfl) ⟨9498626, by rfl⟩ : syracuseStep 12664835 = 18997253) B18997253
theorem B8443223 : Blo 1975435 8443223 := bstep (se 1 (by rfl) ⟨6332417, by rfl⟩ : syracuseStep 8443223 = 12664835) B12664835
theorem B5628815 : Blo 1975435 5628815 := bstep (se 1 (by rfl) ⟨4221611, by rfl⟩ : syracuseStep 5628815 = 8443223) B8443223
theorem B3752543 : Blo 1975435 3752543 := bstep (se 1 (by rfl) ⟨2814407, by rfl⟩ : syracuseStep 3752543 = 5628815) B5628815
theorem B2501695 : Blo 1975435 2501695 := bstep (se 1 (by rfl) ⟨1876271, by rfl⟩ : syracuseStep 2501695 = 3752543) B3752543
theorem B3335593 : Blo 1975435 3335593 := bstep (se 2 (by rfl) ⟨1250847, by rfl⟩ : syracuseStep 3335593 = 2501695) B2501695
theorem B4447457 : Blo 1975435 4447457 := bstep (se 2 (by rfl) ⟨1667796, by rfl⟩ : syracuseStep 4447457 = 3335593) B3335593
theorem B2964971 : Blo 1975435 2964971 := bstep (se 1 (by rfl) ⟨2223728, by rfl⟩ : syracuseStep 2964971 = 4447457) B4447457
theorem B1976647 : Blo 1975435 1976647 := bstep (se 1 (by rfl) ⟨1482485, by rfl⟩ : syracuseStep 1976647 = 2964971) B2964971
theorem B2223733 : Blo 1975435 2223733 := bbase (se 5 (by rfl) ⟨104237, by rfl⟩ : syracuseStep 2223733 = 208475) (by norm_num)
theorem B2964977 : Blo 1975435 2964977 := bstep (se 2 (by rfl) ⟨1111866, by rfl⟩ : syracuseStep 2964977 = 2223733) B2223733
theorem B1976651 : Blo 1975435 1976651 := bstep (se 1 (by rfl) ⟨1482488, by rfl⟩ : syracuseStep 1976651 = 2964977) B2964977
theorem B2501705 : Blo 1975435 2501705 := bbase (se 2 (by rfl) ⟨938139, by rfl⟩ : syracuseStep 2501705 = 1876279) (by norm_num)
theorem B6671213 : Blo 1975435 6671213 := bstep (se 3 (by rfl) ⟨1250852, by rfl⟩ : syracuseStep 6671213 = 2501705) B2501705
theorem B4447475 : Blo 1975435 4447475 := bstep (se 1 (by rfl) ⟨3335606, by rfl⟩ : syracuseStep 4447475 = 6671213) B6671213
theorem B2964983 : Blo 1975435 2964983 := bstep (se 1 (by rfl) ⟨2223737, by rfl⟩ : syracuseStep 2964983 = 4447475) B4447475
theorem B1976655 : Blo 1975435 1976655 := bstep (se 1 (by rfl) ⟨1482491, by rfl⟩ : syracuseStep 1976655 = 2964983) B2964983
theorem B2964989 : Blo 1975435 2964989 := bbase (se 3 (by rfl) ⟨555935, by rfl⟩ : syracuseStep 2964989 = 1111871) (by norm_num)
theorem B1976659 : Blo 1975435 1976659 := bstep (se 1 (by rfl) ⟨1482494, by rfl⟩ : syracuseStep 1976659 = 2964989) B2964989
theorem B4447493 : Blo 1975435 4447493 := bbase (se 4 (by rfl) ⟨416952, by rfl⟩ : syracuseStep 4447493 = 833905) (by norm_num)
theorem B2964995 : Blo 1975435 2964995 := bstep (se 1 (by rfl) ⟨2223746, by rfl⟩ : syracuseStep 2964995 = 4447493) B4447493
theorem B1976663 : Blo 1975435 1976663 := bstep (se 1 (by rfl) ⟨1482497, by rfl⟩ : syracuseStep 1976663 = 2964995) B2964995
theorem B3752581 : Blo 1975435 3752581 := bbase (se 4 (by rfl) ⟨351804, by rfl⟩ : syracuseStep 3752581 = 703609) (by norm_num)
theorem B5003441 : Blo 1975435 5003441 := bstep (se 2 (by rfl) ⟨1876290, by rfl⟩ : syracuseStep 5003441 = 3752581) B3752581
theorem B3335627 : Blo 1975435 3335627 := bstep (se 1 (by rfl) ⟨2501720, by rfl⟩ : syracuseStep 3335627 = 5003441) B5003441
theorem B2223751 : Blo 1975435 2223751 := bstep (se 1 (by rfl) ⟨1667813, by rfl⟩ : syracuseStep 2223751 = 3335627) B3335627
theorem B2965001 : Blo 1975435 2965001 := bstep (se 2 (by rfl) ⟨1111875, by rfl⟩ : syracuseStep 2965001 = 2223751) B2223751
theorem B1976667 : Blo 1975435 1976667 := bstep (se 1 (by rfl) ⟨1482500, by rfl⟩ : syracuseStep 1976667 = 2965001) B2965001
theorem B10006901 : Blo 1975435 10006901 := bbase (se 5 (by rfl) ⟨469073, by rfl⟩ : syracuseStep 10006901 = 938147) (by norm_num)
theorem B6671267 : Blo 1975435 6671267 := bstep (se 1 (by rfl) ⟨5003450, by rfl⟩ : syracuseStep 6671267 = 10006901) B10006901
theorem B4447511 : Blo 1975435 4447511 := bstep (se 1 (by rfl) ⟨3335633, by rfl⟩ : syracuseStep 4447511 = 6671267) B6671267
theorem B2965007 : Blo 1975435 2965007 := bstep (se 1 (by rfl) ⟨2223755, by rfl⟩ : syracuseStep 2965007 = 4447511) B4447511
theorem B1976671 : Blo 1975435 1976671 := bstep (se 1 (by rfl) ⟨1482503, by rfl⟩ : syracuseStep 1976671 = 2965007) B2965007
theorem B2965013 : Blo 1975435 2965013 := bbase (se 6 (by rfl) ⟨69492, by rfl⟩ : syracuseStep 2965013 = 138985) (by norm_num)
theorem B1976675 : Blo 1975435 1976675 := bstep (se 1 (by rfl) ⟨1482506, by rfl⟩ : syracuseStep 1976675 = 2965013) B2965013
theorem B7607605 : Blo 1975435 7607605 := bbase (se 5 (by rfl) ⟨356606, by rfl⟩ : syracuseStep 7607605 = 713213) (by norm_num)
theorem B10143473 : Blo 1975435 10143473 := bstep (se 2 (by rfl) ⟨3803802, by rfl⟩ : syracuseStep 10143473 = 7607605) B7607605
theorem B27049261 : Blo 1975435 27049261 := bstep (se 3 (by rfl) ⟨5071736, by rfl⟩ : syracuseStep 27049261 = 10143473) B10143473
theorem B36065681 : Blo 1975435 36065681 := bstep (se 2 (by rfl) ⟨13524630, by rfl⟩ : syracuseStep 36065681 = 27049261) B27049261
theorem B24043787 : Blo 1975435 24043787 := bstep (se 1 (by rfl) ⟨18032840, by rfl⟩ : syracuseStep 24043787 = 36065681) B36065681
theorem B16029191 : Blo 1975435 16029191 := bstep (se 1 (by rfl) ⟨12021893, by rfl⟩ : syracuseStep 16029191 = 24043787) B24043787
theorem B10686127 : Blo 1975435 10686127 := bstep (se 1 (by rfl) ⟨8014595, by rfl⟩ : syracuseStep 10686127 = 16029191) B16029191
theorem B14248169 : Blo 1975435 14248169 := bstep (se 2 (by rfl) ⟨5343063, by rfl⟩ : syracuseStep 14248169 = 10686127) B10686127
theorem B9498779 : Blo 1975435 9498779 := bstep (se 1 (by rfl) ⟨7124084, by rfl⟩ : syracuseStep 9498779 = 14248169) B14248169
theorem B6332519 : Blo 1975435 6332519 := bstep (se 1 (by rfl) ⟨4749389, by rfl⟩ : syracuseStep 6332519 = 9498779) B9498779
theorem B16886717 : Blo 1975435 16886717 := bstep (se 3 (by rfl) ⟨3166259, by rfl⟩ : syracuseStep 16886717 = 6332519) B6332519
theorem B11257811 : Blo 1975435 11257811 := bstep (se 1 (by rfl) ⟨8443358, by rfl⟩ : syracuseStep 11257811 = 16886717) B16886717
theorem B7505207 : Blo 1975435 7505207 := bstep (se 1 (by rfl) ⟨5628905, by rfl⟩ : syracuseStep 7505207 = 11257811) B11257811
theorem B5003471 : Blo 1975435 5003471 := bstep (se 1 (by rfl) ⟨3752603, by rfl⟩ : syracuseStep 5003471 = 7505207) B7505207
theorem B3335647 : Blo 1975435 3335647 := bstep (se 1 (by rfl) ⟨2501735, by rfl⟩ : syracuseStep 3335647 = 5003471) B5003471
theorem B4447529 : Blo 1975435 4447529 := bstep (se 2 (by rfl) ⟨1667823, by rfl⟩ : syracuseStep 4447529 = 3335647) B3335647
theorem B2965019 : Blo 1975435 2965019 := bstep (se 1 (by rfl) ⟨2223764, by rfl⟩ : syracuseStep 2965019 = 4447529) B4447529
theorem B1976679 : Blo 1975435 1976679 := bstep (se 1 (by rfl) ⟨1482509, by rfl⟩ : syracuseStep 1976679 = 2965019) B2965019
theorem B2223769 : Blo 1975435 2223769 := bbase (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) (by norm_num)
theorem B2965025 : Blo 1975435 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B1976683 : Blo 1975435 1976683 := bstep (se 1 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 1976683 = 2965025) B2965025
theorem B7505237 : Blo 1975435 7505237 := bbase (se 12 (by rfl) ⟨2748, by rfl⟩ : syracuseStep 7505237 = 5497) (by norm_num)
theorem B5003491 : Blo 1975435 5003491 := bstep (se 1 (by rfl) ⟨3752618, by rfl⟩ : syracuseStep 5003491 = 7505237) B7505237
theorem B6671321 : Blo 1975435 6671321 := bstep (se 2 (by rfl) ⟨2501745, by rfl⟩ : syracuseStep 6671321 = 5003491) B5003491
theorem B4447547 : Blo 1975435 4447547 := bstep (se 1 (by rfl) ⟨3335660, by rfl⟩ : syracuseStep 4447547 = 6671321) B6671321
theorem B2965031 : Blo 1975435 2965031 := bstep (se 1 (by rfl) ⟨2223773, by rfl⟩ : syracuseStep 2965031 = 4447547) B4447547
theorem B1976687 : Blo 1975435 1976687 := bstep (se 1 (by rfl) ⟨1482515, by rfl⟩ : syracuseStep 1976687 = 2965031) B2965031
theorem B2965037 : Blo 1975435 2965037 := bbase (se 3 (by rfl) ⟨555944, by rfl⟩ : syracuseStep 2965037 = 1111889) (by norm_num)
theorem B1976691 : Blo 1975435 1976691 := bstep (se 1 (by rfl) ⟨1482518, by rfl⟩ : syracuseStep 1976691 = 2965037) B2965037
theorem B4447565 : Blo 1975435 4447565 := bbase (se 3 (by rfl) ⟨833918, by rfl⟩ : syracuseStep 4447565 = 1667837) (by norm_num)
theorem B2965043 : Blo 1975435 2965043 := bstep (se 1 (by rfl) ⟨2223782, by rfl⟩ : syracuseStep 2965043 = 4447565) B4447565
theorem B1976695 : Blo 1975435 1976695 := bstep (se 1 (by rfl) ⟨1482521, by rfl⟩ : syracuseStep 1976695 = 2965043) B2965043
theorem B2501761 : Blo 1975435 2501761 := bbase (se 2 (by rfl) ⟨938160, by rfl⟩ : syracuseStep 2501761 = 1876321) (by norm_num)
theorem B3335681 : Blo 1975435 3335681 := bstep (se 2 (by rfl) ⟨1250880, by rfl⟩ : syracuseStep 3335681 = 2501761) B2501761
theorem B2223787 : Blo 1975435 2223787 := bstep (se 1 (by rfl) ⟨1667840, by rfl⟩ : syracuseStep 2223787 = 3335681) B3335681
theorem B2965049 : Blo 1975435 2965049 := bstep (se 2 (by rfl) ⟨1111893, by rfl⟩ : syracuseStep 2965049 = 2223787) B2223787
theorem B1976699 : Blo 1975435 1976699 := bstep (se 1 (by rfl) ⟨1482524, by rfl⟩ : syracuseStep 1976699 = 2965049) B2965049
theorem B2110865 : Blo 1975435 2110865 := bbase (se 2 (by rfl) ⟨791574, by rfl⟩ : syracuseStep 2110865 = 1583149) (by norm_num)
theorem B22515893 : Blo 1975435 22515893 := bstep (se 5 (by rfl) ⟨1055432, by rfl⟩ : syracuseStep 22515893 = 2110865) B2110865
theorem B15010595 : Blo 1975435 15010595 := bstep (se 1 (by rfl) ⟨11257946, by rfl⟩ : syracuseStep 15010595 = 22515893) B22515893
theorem B10007063 : Blo 1975435 10007063 := bstep (se 1 (by rfl) ⟨7505297, by rfl⟩ : syracuseStep 10007063 = 15010595) B15010595
theorem B6671375 : Blo 1975435 6671375 := bstep (se 1 (by rfl) ⟨5003531, by rfl⟩ : syracuseStep 6671375 = 10007063) B10007063
theorem B4447583 : Blo 1975435 4447583 := bstep (se 1 (by rfl) ⟨3335687, by rfl⟩ : syracuseStep 4447583 = 6671375) B6671375
theorem B2965055 : Blo 1975435 2965055 := bstep (se 1 (by rfl) ⟨2223791, by rfl⟩ : syracuseStep 2965055 = 4447583) B4447583
theorem B1976703 : Blo 1975435 1976703 := bstep (se 1 (by rfl) ⟨1482527, by rfl⟩ : syracuseStep 1976703 = 2965055) B2965055
theorem B2965061 : Blo 1975435 2965061 := bbase (se 4 (by rfl) ⟨277974, by rfl⟩ : syracuseStep 2965061 = 555949) (by norm_num)
theorem B1976707 : Blo 1975435 1976707 := bstep (se 1 (by rfl) ⟨1482530, by rfl⟩ : syracuseStep 1976707 = 2965061) B2965061
theorem B3335701 : Blo 1975435 3335701 := bbase (se 6 (by rfl) ⟨78180, by rfl⟩ : syracuseStep 3335701 = 156361) (by norm_num)
theorem B4447601 : Blo 1975435 4447601 := bstep (se 2 (by rfl) ⟨1667850, by rfl⟩ : syracuseStep 4447601 = 3335701) B3335701
theorem B2965067 : Blo 1975435 2965067 := bstep (se 1 (by rfl) ⟨2223800, by rfl⟩ : syracuseStep 2965067 = 4447601) B4447601
theorem B1976711 : Blo 1975435 1976711 := bstep (se 1 (by rfl) ⟨1482533, by rfl⟩ : syracuseStep 1976711 = 2965067) B2965067
theorem B2223805 : Blo 1975435 2223805 := bbase (se 3 (by rfl) ⟨416963, by rfl⟩ : syracuseStep 2223805 = 833927) (by norm_num)
theorem B2965073 : Blo 1975435 2965073 := bstep (se 2 (by rfl) ⟨1111902, by rfl⟩ : syracuseStep 2965073 = 2223805) B2223805
theorem B1976715 : Blo 1975435 1976715 := bstep (se 1 (by rfl) ⟨1482536, by rfl⟩ : syracuseStep 1976715 = 2965073) B2965073
theorem B6671429 : Blo 1975435 6671429 := bbase (se 4 (by rfl) ⟨625446, by rfl⟩ : syracuseStep 6671429 = 1250893) (by norm_num)
theorem B4447619 : Blo 1975435 4447619 := bstep (se 1 (by rfl) ⟨3335714, by rfl⟩ : syracuseStep 4447619 = 6671429) B6671429
theorem B2965079 : Blo 1975435 2965079 := bstep (se 1 (by rfl) ⟨2223809, by rfl⟩ : syracuseStep 2965079 = 4447619) B4447619
theorem B1976719 : Blo 1975435 1976719 := bstep (se 1 (by rfl) ⟨1482539, by rfl⟩ : syracuseStep 1976719 = 2965079) B2965079
theorem B2965085 : Blo 1975435 2965085 := bbase (se 3 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 2965085 = 1111907) (by norm_num)
theorem B1976723 : Blo 1975435 1976723 := bstep (se 1 (by rfl) ⟨1482542, by rfl⟩ : syracuseStep 1976723 = 2965085) B2965085
theorem B4447637 : Blo 1975435 4447637 := bbase (se 6 (by rfl) ⟨104241, by rfl⟩ : syracuseStep 4447637 = 208483) (by norm_num)
theorem B2965091 : Blo 1975435 2965091 := bstep (se 1 (by rfl) ⟨2223818, by rfl⟩ : syracuseStep 2965091 = 4447637) B4447637
theorem B1976727 : Blo 1975435 1976727 := bstep (se 1 (by rfl) ⟨1482545, by rfl⟩ : syracuseStep 1976727 = 2965091) B2965091
theorem B21372821 : Blo 1975435 21372821 := bbase (se 6 (by rfl) ⟨500925, by rfl⟩ : syracuseStep 21372821 = 1001851) (by norm_num)
theorem B14248547 : Blo 1975435 14248547 := bstep (se 1 (by rfl) ⟨10686410, by rfl⟩ : syracuseStep 14248547 = 21372821) B21372821
theorem B9499031 : Blo 1975435 9499031 := bstep (se 1 (by rfl) ⟨7124273, by rfl⟩ : syracuseStep 9499031 = 14248547) B14248547
theorem B6332687 : Blo 1975435 6332687 := bstep (se 1 (by rfl) ⟨4749515, by rfl⟩ : syracuseStep 6332687 = 9499031) B9499031
theorem B4221791 : Blo 1975435 4221791 := bstep (se 1 (by rfl) ⟨3166343, by rfl⟩ : syracuseStep 4221791 = 6332687) B6332687
theorem B2814527 : Blo 1975435 2814527 := bstep (se 1 (by rfl) ⟨2110895, by rfl⟩ : syracuseStep 2814527 = 4221791) B4221791
theorem B7505405 : Blo 1975435 7505405 := bstep (se 3 (by rfl) ⟨1407263, by rfl⟩ : syracuseStep 7505405 = 2814527) B2814527
theorem B5003603 : Blo 1975435 5003603 := bstep (se 1 (by rfl) ⟨3752702, by rfl⟩ : syracuseStep 5003603 = 7505405) B7505405
theorem B3335735 : Blo 1975435 3335735 := bstep (se 1 (by rfl) ⟨2501801, by rfl⟩ : syracuseStep 3335735 = 5003603) B5003603
theorem B2223823 : Blo 1975435 2223823 := bstep (se 1 (by rfl) ⟨1667867, by rfl⟩ : syracuseStep 2223823 = 3335735) B3335735
theorem B2965097 : Blo 1975435 2965097 := bstep (se 2 (by rfl) ⟨1111911, by rfl⟩ : syracuseStep 2965097 = 2223823) B2223823
theorem B1976731 : Blo 1975435 1976731 := bstep (se 1 (by rfl) ⟨1482548, by rfl⟩ : syracuseStep 1976731 = 2965097) B2965097
theorem B3166349 : Blo 1975435 3166349 := bbase (se 3 (by rfl) ⟨593690, by rfl⟩ : syracuseStep 3166349 = 1187381) (by norm_num)
theorem B8443597 : Blo 1975435 8443597 := bstep (se 3 (by rfl) ⟨1583174, by rfl⟩ : syracuseStep 8443597 = 3166349) B3166349
theorem B11258129 : Blo 1975435 11258129 := bstep (se 2 (by rfl) ⟨4221798, by rfl⟩ : syracuseStep 11258129 = 8443597) B8443597
theorem B7505419 : Blo 1975435 7505419 := bstep (se 1 (by rfl) ⟨5629064, by rfl⟩ : syracuseStep 7505419 = 11258129) B11258129
theorem B10007225 : Blo 1975435 10007225 := bstep (se 2 (by rfl) ⟨3752709, by rfl⟩ : syracuseStep 10007225 = 7505419) B7505419
theorem B6671483 : Blo 1975435 6671483 := bstep (se 1 (by rfl) ⟨5003612, by rfl⟩ : syracuseStep 6671483 = 10007225) B10007225
theorem B4447655 : Blo 1975435 4447655 := bstep (se 1 (by rfl) ⟨3335741, by rfl⟩ : syracuseStep 4447655 = 6671483) B6671483
theorem B2965103 : Blo 1975435 2965103 := bstep (se 1 (by rfl) ⟨2223827, by rfl⟩ : syracuseStep 2965103 = 4447655) B4447655
theorem B1976735 : Blo 1975435 1976735 := bstep (se 1 (by rfl) ⟨1482551, by rfl⟩ : syracuseStep 1976735 = 2965103) B2965103
theorem B2965109 : Blo 1975435 2965109 := bbase (se 5 (by rfl) ⟨138989, by rfl⟩ : syracuseStep 2965109 = 277979) (by norm_num)
theorem B1976739 : Blo 1975435 1976739 := bstep (se 1 (by rfl) ⟨1482554, by rfl⟩ : syracuseStep 1976739 = 2965109) B2965109
theorem B3752725 : Blo 1975435 3752725 := bbase (se 6 (by rfl) ⟨87954, by rfl⟩ : syracuseStep 3752725 = 175909) (by norm_num)
theorem B5003633 : Blo 1975435 5003633 := bstep (se 2 (by rfl) ⟨1876362, by rfl⟩ : syracuseStep 5003633 = 3752725) B3752725
theorem B3335755 : Blo 1975435 3335755 := bstep (se 1 (by rfl) ⟨2501816, by rfl⟩ : syracuseStep 3335755 = 5003633) B5003633
theorem B4447673 : Blo 1975435 4447673 := bstep (se 2 (by rfl) ⟨1667877, by rfl⟩ : syracuseStep 4447673 = 3335755) B3335755
theorem B2965115 : Blo 1975435 2965115 := bstep (se 1 (by rfl) ⟨2223836, by rfl⟩ : syracuseStep 2965115 = 4447673) B4447673
theorem B1976743 : Blo 1975435 1976743 := bstep (se 1 (by rfl) ⟨1482557, by rfl⟩ : syracuseStep 1976743 = 2965115) B2965115
theorem B2223841 : Blo 1975435 2223841 := bbase (se 2 (by rfl) ⟨833940, by rfl⟩ : syracuseStep 2223841 = 1667881) (by norm_num)
theorem B2965121 : Blo 1975435 2965121 := bstep (se 2 (by rfl) ⟨1111920, by rfl⟩ : syracuseStep 2965121 = 2223841) B2223841
theorem B1976747 : Blo 1975435 1976747 := bstep (se 1 (by rfl) ⟨1482560, by rfl⟩ : syracuseStep 1976747 = 2965121) B2965121
theorem B5003653 : Blo 1975435 5003653 := bbase (se 4 (by rfl) ⟨469092, by rfl⟩ : syracuseStep 5003653 = 938185) (by norm_num)
theorem B6671537 : Blo 1975435 6671537 := bstep (se 2 (by rfl) ⟨2501826, by rfl⟩ : syracuseStep 6671537 = 5003653) B5003653
theorem B4447691 : Blo 1975435 4447691 := bstep (se 1 (by rfl) ⟨3335768, by rfl⟩ : syracuseStep 4447691 = 6671537) B6671537
theorem B2965127 : Blo 1975435 2965127 := bstep (se 1 (by rfl) ⟨2223845, by rfl⟩ : syracuseStep 2965127 = 4447691) B4447691
theorem B1976751 : Blo 1975435 1976751 := bstep (se 1 (by rfl) ⟨1482563, by rfl⟩ : syracuseStep 1976751 = 2965127) B2965127
theorem B2965133 : Blo 1975435 2965133 := bbase (se 3 (by rfl) ⟨555962, by rfl⟩ : syracuseStep 2965133 = 1111925) (by norm_num)
theorem B1976755 : Blo 1975435 1976755 := bstep (se 1 (by rfl) ⟨1482566, by rfl⟩ : syracuseStep 1976755 = 2965133) B2965133
theorem B4447709 : Blo 1975435 4447709 := bbase (se 3 (by rfl) ⟨833945, by rfl⟩ : syracuseStep 4447709 = 1667891) (by norm_num)
theorem B2965139 : Blo 1975435 2965139 := bstep (se 1 (by rfl) ⟨2223854, by rfl⟩ : syracuseStep 2965139 = 4447709) B4447709
theorem B1976759 : Blo 1975435 1976759 := bstep (se 1 (by rfl) ⟨1482569, by rfl⟩ : syracuseStep 1976759 = 2965139) B2965139
theorem B3335789 : Blo 1975435 3335789 := bbase (se 3 (by rfl) ⟨625460, by rfl⟩ : syracuseStep 3335789 = 1250921) (by norm_num)
theorem B2223859 : Blo 1975435 2223859 := bstep (se 1 (by rfl) ⟨1667894, by rfl⟩ : syracuseStep 2223859 = 3335789) B3335789
theorem B2965145 : Blo 1975435 2965145 := bstep (se 2 (by rfl) ⟨1111929, by rfl⟩ : syracuseStep 2965145 = 2223859) B2223859
theorem B1976763 : Blo 1975435 1976763 := bstep (se 1 (by rfl) ⟨1482572, by rfl⟩ : syracuseStep 1976763 = 2965145) B2965145
theorem B25042517 : Blo 1975435 25042517 := bbase (se 8 (by rfl) ⟨146733, by rfl⟩ : syracuseStep 25042517 = 293467) (by norm_num)
theorem B16695011 : Blo 1975435 16695011 := bstep (se 1 (by rfl) ⟨12521258, by rfl⟩ : syracuseStep 16695011 = 25042517) B25042517
theorem B44520029 : Blo 1975435 44520029 := bstep (se 3 (by rfl) ⟨8347505, by rfl⟩ : syracuseStep 44520029 = 16695011) B16695011
theorem B29680019 : Blo 1975435 29680019 := bstep (se 1 (by rfl) ⟨22260014, by rfl⟩ : syracuseStep 29680019 = 44520029) B44520029
theorem B19786679 : Blo 1975435 19786679 := bstep (se 1 (by rfl) ⟨14840009, by rfl⟩ : syracuseStep 19786679 = 29680019) B29680019
theorem B13191119 : Blo 1975435 13191119 := bstep (se 1 (by rfl) ⟨9893339, by rfl⟩ : syracuseStep 13191119 = 19786679) B19786679
theorem B8794079 : Blo 1975435 8794079 := bstep (se 1 (by rfl) ⟨6595559, by rfl⟩ : syracuseStep 8794079 = 13191119) B13191119
theorem B5862719 : Blo 1975435 5862719 := bstep (se 1 (by rfl) ⟨4397039, by rfl⟩ : syracuseStep 5862719 = 8794079) B8794079
theorem B15633917 : Blo 1975435 15633917 := bstep (se 3 (by rfl) ⟨2931359, by rfl⟩ : syracuseStep 15633917 = 5862719) B5862719
theorem B10422611 : Blo 1975435 10422611 := bstep (se 1 (by rfl) ⟨7816958, by rfl⟩ : syracuseStep 10422611 = 15633917) B15633917
theorem B6948407 : Blo 1975435 6948407 := bstep (se 1 (by rfl) ⟨5211305, by rfl⟩ : syracuseStep 6948407 = 10422611) B10422611
theorem B4632271 : Blo 1975435 4632271 := bstep (se 1 (by rfl) ⟨3474203, by rfl⟩ : syracuseStep 4632271 = 6948407) B6948407
theorem B98821781 : Blo 1975435 98821781 := bstep (se 6 (by rfl) ⟨2316135, by rfl⟩ : syracuseStep 98821781 = 4632271) B4632271
theorem B65881187 : Blo 1975435 65881187 := bstep (se 1 (by rfl) ⟨49410890, by rfl⟩ : syracuseStep 65881187 = 98821781) B98821781
theorem B43920791 : Blo 1975435 43920791 := bstep (se 1 (by rfl) ⟨32940593, by rfl⟩ : syracuseStep 43920791 = 65881187) B65881187
theorem B29280527 : Blo 1975435 29280527 := bstep (se 1 (by rfl) ⟨21960395, by rfl⟩ : syracuseStep 29280527 = 43920791) B43920791
theorem B19520351 : Blo 1975435 19520351 := bstep (se 1 (by rfl) ⟨14640263, by rfl⟩ : syracuseStep 19520351 = 29280527) B29280527
theorem B13013567 : Blo 1975435 13013567 := bstep (se 1 (by rfl) ⟨9760175, by rfl⟩ : syracuseStep 13013567 = 19520351) B19520351
theorem B8675711 : Blo 1975435 8675711 := bstep (se 1 (by rfl) ⟨6506783, by rfl⟩ : syracuseStep 8675711 = 13013567) B13013567
theorem B5783807 : Blo 1975435 5783807 := bstep (se 1 (by rfl) ⟨4337855, by rfl⟩ : syracuseStep 5783807 = 8675711) B8675711
theorem B3855871 : Blo 1975435 3855871 := bstep (se 1 (by rfl) ⟨2891903, by rfl⟩ : syracuseStep 3855871 = 5783807) B5783807
theorem B5141161 : Blo 1975435 5141161 := bstep (se 2 (by rfl) ⟨1927935, by rfl⟩ : syracuseStep 5141161 = 3855871) B3855871
theorem B6854881 : Blo 1975435 6854881 := bstep (se 2 (by rfl) ⟨2570580, by rfl⟩ : syracuseStep 6854881 = 5141161) B5141161
theorem B9139841 : Blo 1975435 9139841 := bstep (se 2 (by rfl) ⟨3427440, by rfl⟩ : syracuseStep 9139841 = 6854881) B6854881
theorem B6093227 : Blo 1975435 6093227 := bstep (se 1 (by rfl) ⟨4569920, by rfl⟩ : syracuseStep 6093227 = 9139841) B9139841
theorem B16248605 : Blo 1975435 16248605 := bstep (se 3 (by rfl) ⟨3046613, by rfl⟩ : syracuseStep 16248605 = 6093227) B6093227
theorem B173318453 : Blo 1975435 173318453 := bstep (se 5 (by rfl) ⟨8124302, by rfl⟩ : syracuseStep 173318453 = 16248605) B16248605
theorem B115545635 : Blo 1975435 115545635 := bstep (se 1 (by rfl) ⟨86659226, by rfl⟩ : syracuseStep 115545635 = 173318453) B173318453
theorem B77030423 : Blo 1975435 77030423 := bstep (se 1 (by rfl) ⟨57772817, by rfl⟩ : syracuseStep 77030423 = 115545635) B115545635
theorem B51353615 : Blo 1975435 51353615 := bstep (se 1 (by rfl) ⟨38515211, by rfl⟩ : syracuseStep 51353615 = 77030423) B77030423
theorem B34235743 : Blo 1975435 34235743 := bstep (se 1 (by rfl) ⟨25676807, by rfl⟩ : syracuseStep 34235743 = 51353615) B51353615
theorem B45647657 : Blo 1975435 45647657 := bstep (se 2 (by rfl) ⟨17117871, by rfl⟩ : syracuseStep 45647657 = 34235743) B34235743
theorem B30431771 : Blo 1975435 30431771 := bstep (se 1 (by rfl) ⟨22823828, by rfl⟩ : syracuseStep 30431771 = 45647657) B45647657
theorem B20287847 : Blo 1975435 20287847 := bstep (se 1 (by rfl) ⟨15215885, by rfl⟩ : syracuseStep 20287847 = 30431771) B30431771
theorem B13525231 : Blo 1975435 13525231 := bstep (se 1 (by rfl) ⟨10143923, by rfl⟩ : syracuseStep 13525231 = 20287847) B20287847
theorem B18033641 : Blo 1975435 18033641 := bstep (se 2 (by rfl) ⟨6762615, by rfl⟩ : syracuseStep 18033641 = 13525231) B13525231
theorem B12022427 : Blo 1975435 12022427 := bstep (se 1 (by rfl) ⟨9016820, by rfl⟩ : syracuseStep 12022427 = 18033641) B18033641
theorem B8014951 : Blo 1975435 8014951 := bstep (se 1 (by rfl) ⟨6011213, by rfl⟩ : syracuseStep 8014951 = 12022427) B12022427
theorem B10686601 : Blo 1975435 10686601 := bstep (se 2 (by rfl) ⟨4007475, by rfl⟩ : syracuseStep 10686601 = 8014951) B8014951
theorem B14248801 : Blo 1975435 14248801 := bstep (se 2 (by rfl) ⟨5343300, by rfl⟩ : syracuseStep 14248801 = 10686601) B10686601
theorem B18998401 : Blo 1975435 18998401 := bstep (se 2 (by rfl) ⟨7124400, by rfl⟩ : syracuseStep 18998401 = 14248801) B14248801
theorem B25331201 : Blo 1975435 25331201 := bstep (se 2 (by rfl) ⟨9499200, by rfl⟩ : syracuseStep 25331201 = 18998401) B18998401
theorem B16887467 : Blo 1975435 16887467 := bstep (se 1 (by rfl) ⟨12665600, by rfl⟩ : syracuseStep 16887467 = 25331201) B25331201
theorem B11258311 : Blo 1975435 11258311 := bstep (se 1 (by rfl) ⟨8443733, by rfl⟩ : syracuseStep 11258311 = 16887467) B16887467
theorem B15011081 : Blo 1975435 15011081 := bstep (se 2 (by rfl) ⟨5629155, by rfl⟩ : syracuseStep 15011081 = 11258311) B11258311
theorem B10007387 : Blo 1975435 10007387 := bstep (se 1 (by rfl) ⟨7505540, by rfl⟩ : syracuseStep 10007387 = 15011081) B15011081
theorem B6671591 : Blo 1975435 6671591 := bstep (se 1 (by rfl) ⟨5003693, by rfl⟩ : syracuseStep 6671591 = 10007387) B10007387
theorem B4447727 : Blo 1975435 4447727 := bstep (se 1 (by rfl) ⟨3335795, by rfl⟩ : syracuseStep 4447727 = 6671591) B6671591
theorem B2965151 : Blo 1975435 2965151 := bstep (se 1 (by rfl) ⟨2223863, by rfl⟩ : syracuseStep 2965151 = 4447727) B4447727
theorem B1976767 : Blo 1975435 1976767 := bstep (se 1 (by rfl) ⟨1482575, by rfl⟩ : syracuseStep 1976767 = 2965151) B2965151
theorem B2965157 : Blo 1975435 2965157 := bbase (se 4 (by rfl) ⟨277983, by rfl⟩ : syracuseStep 2965157 = 555967) (by norm_num)
theorem B1976771 : Blo 1975435 1976771 := bstep (se 1 (by rfl) ⟨1482578, by rfl⟩ : syracuseStep 1976771 = 2965157) B2965157
theorem B2501857 : Blo 1975435 2501857 := bbase (se 2 (by rfl) ⟨938196, by rfl⟩ : syracuseStep 2501857 = 1876393) (by norm_num)
theorem B3335809 : Blo 1975435 3335809 := bstep (se 2 (by rfl) ⟨1250928, by rfl⟩ : syracuseStep 3335809 = 2501857) B2501857
theorem B4447745 : Blo 1975435 4447745 := bstep (se 2 (by rfl) ⟨1667904, by rfl⟩ : syracuseStep 4447745 = 3335809) B3335809
theorem B2965163 : Blo 1975435 2965163 := bstep (se 1 (by rfl) ⟨2223872, by rfl⟩ : syracuseStep 2965163 = 4447745) B4447745
theorem B1976775 : Blo 1975435 1976775 := bstep (se 1 (by rfl) ⟨1482581, by rfl⟩ : syracuseStep 1976775 = 2965163) B2965163
theorem B2223877 : Blo 1975435 2223877 := bbase (se 4 (by rfl) ⟨208488, by rfl⟩ : syracuseStep 2223877 = 416977) (by norm_num)
theorem B2965169 : Blo 1975435 2965169 := bstep (se 2 (by rfl) ⟨1111938, by rfl⟩ : syracuseStep 2965169 = 2223877) B2223877
theorem B1976779 : Blo 1975435 1976779 := bstep (se 1 (by rfl) ⟨1482584, by rfl⟩ : syracuseStep 1976779 = 2965169) B2965169
theorem B2254225 : Blo 1975435 2254225 := bbase (se 2 (by rfl) ⟨845334, by rfl⟩ : syracuseStep 2254225 = 1690669) (by norm_num)
theorem B3005633 : Blo 1975435 3005633 := bstep (se 2 (by rfl) ⟨1127112, by rfl⟩ : syracuseStep 3005633 = 2254225) B2254225
theorem B8015021 : Blo 1975435 8015021 := bstep (se 3 (by rfl) ⟨1502816, by rfl⟩ : syracuseStep 8015021 = 3005633) B3005633
theorem B5343347 : Blo 1975435 5343347 := bstep (se 1 (by rfl) ⟨4007510, by rfl⟩ : syracuseStep 5343347 = 8015021) B8015021
theorem B3562231 : Blo 1975435 3562231 := bstep (se 1 (by rfl) ⟨2671673, by rfl⟩ : syracuseStep 3562231 = 5343347) B5343347
theorem B4749641 : Blo 1975435 4749641 := bstep (se 2 (by rfl) ⟨1781115, by rfl⟩ : syracuseStep 4749641 = 3562231) B3562231
theorem B3166427 : Blo 1975435 3166427 := bstep (se 1 (by rfl) ⟨2374820, by rfl⟩ : syracuseStep 3166427 = 4749641) B4749641
theorem B2110951 : Blo 1975435 2110951 := bstep (se 1 (by rfl) ⟨1583213, by rfl⟩ : syracuseStep 2110951 = 3166427) B3166427
theorem B2814601 : Blo 1975435 2814601 := bstep (se 2 (by rfl) ⟨1055475, by rfl⟩ : syracuseStep 2814601 = 2110951) B2110951
theorem B3752801 : Blo 1975435 3752801 := bstep (se 2 (by rfl) ⟨1407300, by rfl⟩ : syracuseStep 3752801 = 2814601) B2814601
theorem B2501867 : Blo 1975435 2501867 := bstep (se 1 (by rfl) ⟨1876400, by rfl⟩ : syracuseStep 2501867 = 3752801) B3752801
theorem B6671645 : Blo 1975435 6671645 := bstep (se 3 (by rfl) ⟨1250933, by rfl⟩ : syracuseStep 6671645 = 2501867) B2501867
theorem B4447763 : Blo 1975435 4447763 := bstep (se 1 (by rfl) ⟨3335822, by rfl⟩ : syracuseStep 4447763 = 6671645) B6671645
theorem B2965175 : Blo 1975435 2965175 := bstep (se 1 (by rfl) ⟨2223881, by rfl⟩ : syracuseStep 2965175 = 4447763) B4447763
theorem B1976783 : Blo 1975435 1976783 := bstep (se 1 (by rfl) ⟨1482587, by rfl⟩ : syracuseStep 1976783 = 2965175) B2965175
theorem B2965181 : Blo 1975435 2965181 := bbase (se 3 (by rfl) ⟨555971, by rfl⟩ : syracuseStep 2965181 = 1111943) (by norm_num)
theorem B1976787 : Blo 1975435 1976787 := bstep (se 1 (by rfl) ⟨1482590, by rfl⟩ : syracuseStep 1976787 = 2965181) B2965181
theorem B4447781 : Blo 1975435 4447781 := bbase (se 4 (by rfl) ⟨416979, by rfl⟩ : syracuseStep 4447781 = 833959) (by norm_num)
theorem B2965187 : Blo 1975435 2965187 := bstep (se 1 (by rfl) ⟨2223890, by rfl⟩ : syracuseStep 2965187 = 4447781) B4447781
theorem B1976791 : Blo 1975435 1976791 := bstep (se 1 (by rfl) ⟨1482593, by rfl⟩ : syracuseStep 1976791 = 2965187) B2965187
theorem B5003765 : Blo 1975435 5003765 := bbase (se 5 (by rfl) ⟨234551, by rfl⟩ : syracuseStep 5003765 = 469103) (by norm_num)
theorem B3335843 : Blo 1975435 3335843 := bstep (se 1 (by rfl) ⟨2501882, by rfl⟩ : syracuseStep 3335843 = 5003765) B5003765
theorem B2223895 : Blo 1975435 2223895 := bstep (se 1 (by rfl) ⟨1667921, by rfl⟩ : syracuseStep 2223895 = 3335843) B3335843
theorem B2965193 : Blo 1975435 2965193 := bstep (se 2 (by rfl) ⟨1111947, by rfl⟩ : syracuseStep 2965193 = 2223895) B2223895
theorem B1976795 : Blo 1975435 1976795 := bstep (se 1 (by rfl) ⟨1482596, by rfl⟩ : syracuseStep 1976795 = 2965193) B2965193
theorem B2139769 : Blo 1975435 2139769 := bbase (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) (by norm_num)
theorem B2853025 : Blo 1975435 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B15216133 : Blo 1975435 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B20288177 : Blo 1975435 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B13525451 : Blo 1975435 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B9016967 : Blo 1975435 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B24045245 : Blo 1975435 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B16030163 : Blo 1975435 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B42747101 : Blo 1975435 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B28498067 : Blo 1975435 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B18998711 : Blo 1975435 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B12665807 : Blo 1975435 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B8443871 : Blo 1975435 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B5629247 : Blo 1975435 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B3752831 : Blo 1975435 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B10007549 : Blo 1975435 10007549 := bstep (se 3 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 10007549 = 3752831) B3752831
theorem B6671699 : Blo 1975435 6671699 := bstep (se 1 (by rfl) ⟨5003774, by rfl⟩ : syracuseStep 6671699 = 10007549) B10007549
theorem B4447799 : Blo 1975435 4447799 := bstep (se 1 (by rfl) ⟨3335849, by rfl⟩ : syracuseStep 4447799 = 6671699) B6671699
theorem B2965199 : Blo 1975435 2965199 := bstep (se 1 (by rfl) ⟨2223899, by rfl⟩ : syracuseStep 2965199 = 4447799) B4447799
theorem B1976799 : Blo 1975435 1976799 := bstep (se 1 (by rfl) ⟨1482599, by rfl⟩ : syracuseStep 1976799 = 2965199) B2965199
theorem B2965205 : Blo 1975435 2965205 := bbase (se 7 (by rfl) ⟨34748, by rfl⟩ : syracuseStep 2965205 = 69497) (by norm_num)
theorem B1976803 : Blo 1975435 1976803 := bstep (se 1 (by rfl) ⟨1482602, by rfl⟩ : syracuseStep 1976803 = 2965205) B2965205
theorem B2374849 : Blo 1975435 2374849 := bbase (se 2 (by rfl) ⟨890568, by rfl⟩ : syracuseStep 2374849 = 1781137) (by norm_num)
theorem B3166465 : Blo 1975435 3166465 := bstep (se 2 (by rfl) ⟨1187424, by rfl⟩ : syracuseStep 3166465 = 2374849) B2374849
theorem B4221953 : Blo 1975435 4221953 := bstep (se 2 (by rfl) ⟨1583232, by rfl⟩ : syracuseStep 4221953 = 3166465) B3166465
theorem B2814635 : Blo 1975435 2814635 := bstep (se 1 (by rfl) ⟨2110976, by rfl⟩ : syracuseStep 2814635 = 4221953) B4221953
theorem B7505693 : Blo 1975435 7505693 := bstep (se 3 (by rfl) ⟨1407317, by rfl⟩ : syracuseStep 7505693 = 2814635) B2814635
theorem B5003795 : Blo 1975435 5003795 := bstep (se 1 (by rfl) ⟨3752846, by rfl⟩ : syracuseStep 5003795 = 7505693) B7505693
theorem B3335863 : Blo 1975435 3335863 := bstep (se 1 (by rfl) ⟨2501897, by rfl⟩ : syracuseStep 3335863 = 5003795) B5003795
theorem B4447817 : Blo 1975435 4447817 := bstep (se 2 (by rfl) ⟨1667931, by rfl⟩ : syracuseStep 4447817 = 3335863) B3335863
theorem B2965211 : Blo 1975435 2965211 := bstep (se 1 (by rfl) ⟨2223908, by rfl⟩ : syracuseStep 2965211 = 4447817) B4447817
theorem B1976807 : Blo 1975435 1976807 := bstep (se 1 (by rfl) ⟨1482605, by rfl⟩ : syracuseStep 1976807 = 2965211) B2965211
theorem B2223913 : Blo 1975435 2223913 := bbase (se 2 (by rfl) ⟨833967, by rfl⟩ : syracuseStep 2223913 = 1667935) (by norm_num)
theorem B2965217 : Blo 1975435 2965217 := bstep (se 2 (by rfl) ⟨1111956, by rfl⟩ : syracuseStep 2965217 = 2223913) B2223913
theorem B1976811 : Blo 1975435 1976811 := bstep (se 1 (by rfl) ⟨1482608, by rfl⟩ : syracuseStep 1976811 = 2965217) B2965217
theorem B12665909 : Blo 1975435 12665909 := bbase (se 5 (by rfl) ⟨593714, by rfl⟩ : syracuseStep 12665909 = 1187429) (by norm_num)
theorem B8443939 : Blo 1975435 8443939 := bstep (se 1 (by rfl) ⟨6332954, by rfl⟩ : syracuseStep 8443939 = 12665909) B12665909
theorem B11258585 : Blo 1975435 11258585 := bstep (se 2 (by rfl) ⟨4221969, by rfl⟩ : syracuseStep 11258585 = 8443939) B8443939
theorem B7505723 : Blo 1975435 7505723 := bstep (se 1 (by rfl) ⟨5629292, by rfl⟩ : syracuseStep 7505723 = 11258585) B11258585
theorem B5003815 : Blo 1975435 5003815 := bstep (se 1 (by rfl) ⟨3752861, by rfl⟩ : syracuseStep 5003815 = 7505723) B7505723
theorem B6671753 : Blo 1975435 6671753 := bstep (se 2 (by rfl) ⟨2501907, by rfl⟩ : syracuseStep 6671753 = 5003815) B5003815
theorem B4447835 : Blo 1975435 4447835 := bstep (se 1 (by rfl) ⟨3335876, by rfl⟩ : syracuseStep 4447835 = 6671753) B6671753
theorem B2965223 : Blo 1975435 2965223 := bstep (se 1 (by rfl) ⟨2223917, by rfl⟩ : syracuseStep 2965223 = 4447835) B4447835
theorem B1976815 : Blo 1975435 1976815 := bstep (se 1 (by rfl) ⟨1482611, by rfl⟩ : syracuseStep 1976815 = 2965223) B2965223
theorem B2965229 : Blo 1975435 2965229 := bbase (se 3 (by rfl) ⟨555980, by rfl⟩ : syracuseStep 2965229 = 1111961) (by norm_num)
theorem B1976819 : Blo 1975435 1976819 := bstep (se 1 (by rfl) ⟨1482614, by rfl⟩ : syracuseStep 1976819 = 2965229) B2965229
theorem B4447853 : Blo 1975435 4447853 := bbase (se 3 (by rfl) ⟨833972, by rfl⟩ : syracuseStep 4447853 = 1667945) (by norm_num)
theorem B2965235 : Blo 1975435 2965235 := bstep (se 1 (by rfl) ⟨2223926, by rfl⟩ : syracuseStep 2965235 = 4447853) B4447853
theorem B1976823 : Blo 1975435 1976823 := bstep (se 1 (by rfl) ⟨1482617, by rfl⟩ : syracuseStep 1976823 = 2965235) B2965235
theorem B3752885 : Blo 1975435 3752885 := bbase (se 5 (by rfl) ⟨175916, by rfl⟩ : syracuseStep 3752885 = 351833) (by norm_num)
theorem B2501923 : Blo 1975435 2501923 := bstep (se 1 (by rfl) ⟨1876442, by rfl⟩ : syracuseStep 2501923 = 3752885) B3752885
theorem B3335897 : Blo 1975435 3335897 := bstep (se 2 (by rfl) ⟨1250961, by rfl⟩ : syracuseStep 3335897 = 2501923) B2501923
theorem B2223931 : Blo 1975435 2223931 := bstep (se 1 (by rfl) ⟨1667948, by rfl⟩ : syracuseStep 2223931 = 3335897) B3335897
theorem B2965241 : Blo 1975435 2965241 := bstep (se 2 (by rfl) ⟨1111965, by rfl⟩ : syracuseStep 2965241 = 2223931) B2223931
theorem B1976827 : Blo 1975435 1976827 := bstep (se 1 (by rfl) ⟨1482620, by rfl⟩ : syracuseStep 1976827 = 2965241) B2965241
theorem B8124565 : Blo 1975435 8124565 := bbase (se 6 (by rfl) ⟨190419, by rfl⟩ : syracuseStep 8124565 = 380839) (by norm_num)
theorem B10832753 : Blo 1975435 10832753 := bstep (se 2 (by rfl) ⟨4062282, by rfl⟩ : syracuseStep 10832753 = 8124565) B8124565
theorem B7221835 : Blo 1975435 7221835 := bstep (se 1 (by rfl) ⟨5416376, by rfl⟩ : syracuseStep 7221835 = 10832753) B10832753
theorem B9629113 : Blo 1975435 9629113 := bstep (se 2 (by rfl) ⟨3610917, by rfl⟩ : syracuseStep 9629113 = 7221835) B7221835
theorem B12838817 : Blo 1975435 12838817 := bstep (se 2 (by rfl) ⟨4814556, by rfl⟩ : syracuseStep 12838817 = 9629113) B9629113
theorem B34236845 : Blo 1975435 34236845 := bstep (se 3 (by rfl) ⟨6419408, by rfl⟩ : syracuseStep 34236845 = 12838817) B12838817
theorem B22824563 : Blo 1975435 22824563 := bstep (se 1 (by rfl) ⟨17118422, by rfl⟩ : syracuseStep 22824563 = 34236845) B34236845
theorem B60865501 : Blo 1975435 60865501 := bstep (se 3 (by rfl) ⟨11412281, by rfl⟩ : syracuseStep 60865501 = 22824563) B22824563
theorem B81154001 : Blo 1975435 81154001 := bstep (se 2 (by rfl) ⟨30432750, by rfl⟩ : syracuseStep 81154001 = 60865501) B60865501
theorem B54102667 : Blo 1975435 54102667 := bstep (se 1 (by rfl) ⟨40577000, by rfl⟩ : syracuseStep 54102667 = 81154001) B81154001
theorem B72136889 : Blo 1975435 72136889 := bstep (se 2 (by rfl) ⟨27051333, by rfl⟩ : syracuseStep 72136889 = 54102667) B54102667
theorem B48091259 : Blo 1975435 48091259 := bstep (se 1 (by rfl) ⟨36068444, by rfl⟩ : syracuseStep 48091259 = 72136889) B72136889
theorem B128243357 : Blo 1975435 128243357 := bstep (se 3 (by rfl) ⟨24045629, by rfl⟩ : syracuseStep 128243357 = 48091259) B48091259
theorem B85495571 : Blo 1975435 85495571 := bstep (se 1 (by rfl) ⟨64121678, by rfl⟩ : syracuseStep 85495571 = 128243357) B128243357
theorem B56997047 : Blo 1975435 56997047 := bstep (se 1 (by rfl) ⟨42747785, by rfl⟩ : syracuseStep 56997047 = 85495571) B85495571
theorem B37998031 : Blo 1975435 37998031 := bstep (se 1 (by rfl) ⟨28498523, by rfl⟩ : syracuseStep 37998031 = 56997047) B56997047
theorem B50664041 : Blo 1975435 50664041 := bstep (se 2 (by rfl) ⟨18999015, by rfl⟩ : syracuseStep 50664041 = 37998031) B37998031
theorem B33776027 : Blo 1975435 33776027 := bstep (se 1 (by rfl) ⟨25332020, by rfl⟩ : syracuseStep 33776027 = 50664041) B50664041
theorem B22517351 : Blo 1975435 22517351 := bstep (se 1 (by rfl) ⟨16888013, by rfl⟩ : syracuseStep 22517351 = 33776027) B33776027
theorem B15011567 : Blo 1975435 15011567 := bstep (se 1 (by rfl) ⟨11258675, by rfl⟩ : syracuseStep 15011567 = 22517351) B22517351
theorem B10007711 : Blo 1975435 10007711 := bstep (se 1 (by rfl) ⟨7505783, by rfl⟩ : syracuseStep 10007711 = 15011567) B15011567
theorem B6671807 : Blo 1975435 6671807 := bstep (se 1 (by rfl) ⟨5003855, by rfl⟩ : syracuseStep 6671807 = 10007711) B10007711
theorem B4447871 : Blo 1975435 4447871 := bstep (se 1 (by rfl) ⟨3335903, by rfl⟩ : syracuseStep 4447871 = 6671807) B6671807
theorem B2965247 : Blo 1975435 2965247 := bstep (se 1 (by rfl) ⟨2223935, by rfl⟩ : syracuseStep 2965247 = 4447871) B4447871
theorem B1976831 : Blo 1975435 1976831 := bstep (se 1 (by rfl) ⟨1482623, by rfl⟩ : syracuseStep 1976831 = 2965247) B2965247
theorem B2965253 : Blo 1975435 2965253 := bbase (se 4 (by rfl) ⟨277992, by rfl⟩ : syracuseStep 2965253 = 555985) (by norm_num)
theorem B1976835 : Blo 1975435 1976835 := bstep (se 1 (by rfl) ⟨1482626, by rfl⟩ : syracuseStep 1976835 = 2965253) B2965253
theorem B3335917 : Blo 1975435 3335917 := bbase (se 3 (by rfl) ⟨625484, by rfl⟩ : syracuseStep 3335917 = 1250969) (by norm_num)
theorem B4447889 : Blo 1975435 4447889 := bstep (se 2 (by rfl) ⟨1667958, by rfl⟩ : syracuseStep 4447889 = 3335917) B3335917
theorem B2965259 : Blo 1975435 2965259 := bstep (se 1 (by rfl) ⟨2223944, by rfl⟩ : syracuseStep 2965259 = 4447889) B4447889
theorem B1976839 : Blo 1975435 1976839 := bstep (se 1 (by rfl) ⟨1482629, by rfl⟩ : syracuseStep 1976839 = 2965259) B2965259
theorem B2223949 : Blo 1975435 2223949 := bbase (se 3 (by rfl) ⟨416990, by rfl⟩ : syracuseStep 2223949 = 833981) (by norm_num)
theorem B2965265 : Blo 1975435 2965265 := bstep (se 2 (by rfl) ⟨1111974, by rfl⟩ : syracuseStep 2965265 = 2223949) B2223949
theorem B1976843 : Blo 1975435 1976843 := bstep (se 1 (by rfl) ⟨1482632, by rfl⟩ : syracuseStep 1976843 = 2965265) B2965265
theorem B6671861 : Blo 1975435 6671861 := bbase (se 5 (by rfl) ⟨312743, by rfl⟩ : syracuseStep 6671861 = 625487) (by norm_num)
theorem B4447907 : Blo 1975435 4447907 := bstep (se 1 (by rfl) ⟨3335930, by rfl⟩ : syracuseStep 4447907 = 6671861) B6671861
theorem B2965271 : Blo 1975435 2965271 := bstep (se 1 (by rfl) ⟨2223953, by rfl⟩ : syracuseStep 2965271 = 4447907) B4447907
theorem B1976847 : Blo 1975435 1976847 := bstep (se 1 (by rfl) ⟨1482635, by rfl⟩ : syracuseStep 1976847 = 2965271) B2965271
theorem B2965277 : Blo 1975435 2965277 := bbase (se 3 (by rfl) ⟨555989, by rfl⟩ : syracuseStep 2965277 = 1111979) (by norm_num)
theorem B1976851 : Blo 1975435 1976851 := bstep (se 1 (by rfl) ⟨1482638, by rfl⟩ : syracuseStep 1976851 = 2965277) B2965277
theorem B4447925 : Blo 1975435 4447925 := bbase (se 5 (by rfl) ⟨208496, by rfl⟩ : syracuseStep 4447925 = 416993) (by norm_num)
theorem B2965283 : Blo 1975435 2965283 := bstep (se 1 (by rfl) ⟨2223962, by rfl⟩ : syracuseStep 2965283 = 4447925) B4447925
theorem B1976855 : Blo 1975435 1976855 := bstep (se 1 (by rfl) ⟨1482641, by rfl⟩ : syracuseStep 1976855 = 2965283) B2965283
theorem B11258837 : Blo 1975435 11258837 := bbase (se 7 (by rfl) ⟨131939, by rfl⟩ : syracuseStep 11258837 = 263879) (by norm_num)
theorem B7505891 : Blo 1975435 7505891 := bstep (se 1 (by rfl) ⟨5629418, by rfl⟩ : syracuseStep 7505891 = 11258837) B11258837
theorem B5003927 : Blo 1975435 5003927 := bstep (se 1 (by rfl) ⟨3752945, by rfl⟩ : syracuseStep 5003927 = 7505891) B7505891
theorem B3335951 : Blo 1975435 3335951 := bstep (se 1 (by rfl) ⟨2501963, by rfl⟩ : syracuseStep 3335951 = 5003927) B5003927
theorem B2223967 : Blo 1975435 2223967 := bstep (se 1 (by rfl) ⟨1667975, by rfl⟩ : syracuseStep 2223967 = 3335951) B3335951
theorem B2965289 : Blo 1975435 2965289 := bstep (se 2 (by rfl) ⟨1111983, by rfl⟩ : syracuseStep 2965289 = 2223967) B2223967
theorem B1976859 : Blo 1975435 1976859 := bstep (se 1 (by rfl) ⟨1482644, by rfl⟩ : syracuseStep 1976859 = 2965289) B2965289
theorem B5629429 : Blo 1975435 5629429 := bbase (se 5 (by rfl) ⟨263879, by rfl⟩ : syracuseStep 5629429 = 527759) (by norm_num)
theorem B7505905 : Blo 1975435 7505905 := bstep (se 2 (by rfl) ⟨2814714, by rfl⟩ : syracuseStep 7505905 = 5629429) B5629429
theorem B10007873 : Blo 1975435 10007873 := bstep (se 2 (by rfl) ⟨3752952, by rfl⟩ : syracuseStep 10007873 = 7505905) B7505905
theorem B6671915 : Blo 1975435 6671915 := bstep (se 1 (by rfl) ⟨5003936, by rfl⟩ : syracuseStep 6671915 = 10007873) B10007873
theorem B4447943 : Blo 1975435 4447943 := bstep (se 1 (by rfl) ⟨3335957, by rfl⟩ : syracuseStep 4447943 = 6671915) B6671915
theorem B2965295 : Blo 1975435 2965295 := bstep (se 1 (by rfl) ⟨2223971, by rfl⟩ : syracuseStep 2965295 = 4447943) B4447943
theorem B1976863 : Blo 1975435 1976863 := bstep (se 1 (by rfl) ⟨1482647, by rfl⟩ : syracuseStep 1976863 = 2965295) B2965295
theorem B2965301 : Blo 1975435 2965301 := bbase (se 5 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 2965301 = 277997) (by norm_num)
theorem B1976867 : Blo 1975435 1976867 := bstep (se 1 (by rfl) ⟨1482650, by rfl⟩ : syracuseStep 1976867 = 2965301) B2965301
theorem B5003957 : Blo 1975435 5003957 := bbase (se 5 (by rfl) ⟨234560, by rfl⟩ : syracuseStep 5003957 = 469121) (by norm_num)
theorem B3335971 : Blo 1975435 3335971 := bstep (se 1 (by rfl) ⟨2501978, by rfl⟩ : syracuseStep 3335971 = 5003957) B5003957
theorem B4447961 : Blo 1975435 4447961 := bstep (se 2 (by rfl) ⟨1667985, by rfl⟩ : syracuseStep 4447961 = 3335971) B3335971
theorem B2965307 : Blo 1975435 2965307 := bstep (se 1 (by rfl) ⟨2223980, by rfl⟩ : syracuseStep 2965307 = 4447961) B4447961
theorem B1976871 : Blo 1975435 1976871 := bstep (se 1 (by rfl) ⟨1482653, by rfl⟩ : syracuseStep 1976871 = 2965307) B2965307
theorem B2223985 : Blo 1975435 2223985 := bbase (se 2 (by rfl) ⟨833994, by rfl⟩ : syracuseStep 2223985 = 1667989) (by norm_num)
theorem B2965313 : Blo 1975435 2965313 := bstep (se 2 (by rfl) ⟨1111992, by rfl⟩ : syracuseStep 2965313 = 2223985) B2223985
theorem B1976875 : Blo 1975435 1976875 := bstep (se 1 (by rfl) ⟨1482656, by rfl⟩ : syracuseStep 1976875 = 2965313) B2965313
theorem B8444213 : Blo 1975435 8444213 := bbase (se 5 (by rfl) ⟨395822, by rfl⟩ : syracuseStep 8444213 = 791645) (by norm_num)
theorem B5629475 : Blo 1975435 5629475 := bstep (se 1 (by rfl) ⟨4222106, by rfl⟩ : syracuseStep 5629475 = 8444213) B8444213
theorem B3752983 : Blo 1975435 3752983 := bstep (se 1 (by rfl) ⟨2814737, by rfl⟩ : syracuseStep 3752983 = 5629475) B5629475
theorem B5003977 : Blo 1975435 5003977 := bstep (se 2 (by rfl) ⟨1876491, by rfl⟩ : syracuseStep 5003977 = 3752983) B3752983
theorem B6671969 : Blo 1975435 6671969 := bstep (se 2 (by rfl) ⟨2501988, by rfl⟩ : syracuseStep 6671969 = 5003977) B5003977
theorem B4447979 : Blo 1975435 4447979 := bstep (se 1 (by rfl) ⟨3335984, by rfl⟩ : syracuseStep 4447979 = 6671969) B6671969
theorem B2965319 : Blo 1975435 2965319 := bstep (se 1 (by rfl) ⟨2223989, by rfl⟩ : syracuseStep 2965319 = 4447979) B4447979
theorem B1976879 : Blo 1975435 1976879 := bstep (se 1 (by rfl) ⟨1482659, by rfl⟩ : syracuseStep 1976879 = 2965319) B2965319
theorem B2965325 : Blo 1975435 2965325 := bbase (se 3 (by rfl) ⟨555998, by rfl⟩ : syracuseStep 2965325 = 1111997) (by norm_num)
theorem B1976883 : Blo 1975435 1976883 := bstep (se 1 (by rfl) ⟨1482662, by rfl⟩ : syracuseStep 1976883 = 2965325) B2965325
theorem B4447997 : Blo 1975435 4447997 := bbase (se 3 (by rfl) ⟨833999, by rfl⟩ : syracuseStep 4447997 = 1667999) (by norm_num)
theorem B2965331 : Blo 1975435 2965331 := bstep (se 1 (by rfl) ⟨2223998, by rfl⟩ : syracuseStep 2965331 = 4447997) B4447997
theorem B1976887 : Blo 1975435 1976887 := bstep (se 1 (by rfl) ⟨1482665, by rfl⟩ : syracuseStep 1976887 = 2965331) B2965331
theorem B3336005 : Blo 1975435 3336005 := bbase (se 4 (by rfl) ⟨312750, by rfl⟩ : syracuseStep 3336005 = 625501) (by norm_num)
theorem B2224003 : Blo 1975435 2224003 := bstep (se 1 (by rfl) ⟨1668002, by rfl⟩ : syracuseStep 2224003 = 3336005) B3336005
theorem B2965337 : Blo 1975435 2965337 := bstep (se 2 (by rfl) ⟨1112001, by rfl⟩ : syracuseStep 2965337 = 2224003) B2224003
theorem B1976891 : Blo 1975435 1976891 := bstep (se 1 (by rfl) ⟨1482668, by rfl⟩ : syracuseStep 1976891 = 2965337) B2965337
theorem B15012053 : Blo 1975435 15012053 := bbase (se 7 (by rfl) ⟨175922, by rfl⟩ : syracuseStep 15012053 = 351845) (by norm_num)
theorem B10008035 : Blo 1975435 10008035 := bstep (se 1 (by rfl) ⟨7506026, by rfl⟩ : syracuseStep 10008035 = 15012053) B15012053
theorem B6672023 : Blo 1975435 6672023 := bstep (se 1 (by rfl) ⟨5004017, by rfl⟩ : syracuseStep 6672023 = 10008035) B10008035
theorem B4448015 : Blo 1975435 4448015 := bstep (se 1 (by rfl) ⟨3336011, by rfl⟩ : syracuseStep 4448015 = 6672023) B6672023
theorem B2965343 : Blo 1975435 2965343 := bstep (se 1 (by rfl) ⟨2224007, by rfl⟩ : syracuseStep 2965343 = 4448015) B4448015
theorem B1976895 : Blo 1975435 1976895 := bstep (se 1 (by rfl) ⟨1482671, by rfl⟩ : syracuseStep 1976895 = 2965343) B2965343
theorem B2965349 : Blo 1975435 2965349 := bbase (se 4 (by rfl) ⟨278001, by rfl⟩ : syracuseStep 2965349 = 556003) (by norm_num)
theorem B1976899 : Blo 1975435 1976899 := bstep (se 1 (by rfl) ⟨1482674, by rfl⟩ : syracuseStep 1976899 = 2965349) B2965349
theorem B3753029 : Blo 1975435 3753029 := bbase (se 4 (by rfl) ⟨351846, by rfl⟩ : syracuseStep 3753029 = 703693) (by norm_num)
theorem B2502019 : Blo 1975435 2502019 := bstep (se 1 (by rfl) ⟨1876514, by rfl⟩ : syracuseStep 2502019 = 3753029) B3753029
theorem B3336025 : Blo 1975435 3336025 := bstep (se 2 (by rfl) ⟨1251009, by rfl⟩ : syracuseStep 3336025 = 2502019) B2502019
theorem B4448033 : Blo 1975435 4448033 := bstep (se 2 (by rfl) ⟨1668012, by rfl⟩ : syracuseStep 4448033 = 3336025) B3336025
theorem B2965355 : Blo 1975435 2965355 := bstep (se 1 (by rfl) ⟨2224016, by rfl⟩ : syracuseStep 2965355 = 4448033) B4448033
theorem B1976903 : Blo 1975435 1976903 := bstep (se 1 (by rfl) ⟨1482677, by rfl⟩ : syracuseStep 1976903 = 2965355) B2965355
theorem B2224021 : Blo 1975435 2224021 := bbase (se 6 (by rfl) ⟨52125, by rfl⟩ : syracuseStep 2224021 = 104251) (by norm_num)
theorem B2965361 : Blo 1975435 2965361 := bstep (se 2 (by rfl) ⟨1112010, by rfl⟩ : syracuseStep 2965361 = 2224021) B2224021
theorem B1976907 : Blo 1975435 1976907 := bstep (se 1 (by rfl) ⟨1482680, by rfl⟩ : syracuseStep 1976907 = 2965361) B2965361
theorem B2502029 : Blo 1975435 2502029 := bbase (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) (by norm_num)
theorem B6672077 : Blo 1975435 6672077 := bstep (se 3 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 6672077 = 2502029) B2502029
theorem B4448051 : Blo 1975435 4448051 := bstep (se 1 (by rfl) ⟨3336038, by rfl⟩ : syracuseStep 4448051 = 6672077) B6672077
theorem B2965367 : Blo 1975435 2965367 := bstep (se 1 (by rfl) ⟨2224025, by rfl⟩ : syracuseStep 2965367 = 4448051) B4448051
theorem B1976911 : Blo 1975435 1976911 := bstep (se 1 (by rfl) ⟨1482683, by rfl⟩ : syracuseStep 1976911 = 2965367) B2965367
theorem B2965373 : Blo 1975435 2965373 := bbase (se 3 (by rfl) ⟨556007, by rfl⟩ : syracuseStep 2965373 = 1112015) (by norm_num)
theorem B1976915 : Blo 1975435 1976915 := bstep (se 1 (by rfl) ⟨1482686, by rfl⟩ : syracuseStep 1976915 = 2965373) B2965373
theorem B4448069 : Blo 1975435 4448069 := bbase (se 4 (by rfl) ⟨417006, by rfl⟩ : syracuseStep 4448069 = 834013) (by norm_num)
theorem B2965379 : Blo 1975435 2965379 := bstep (se 1 (by rfl) ⟨2224034, by rfl⟩ : syracuseStep 2965379 = 4448069) B4448069
theorem B1976919 : Blo 1975435 1976919 := bstep (se 1 (by rfl) ⟨1482689, by rfl⟩ : syracuseStep 1976919 = 2965379) B2965379
theorem B2003897 : Blo 1975435 2003897 := bbase (se 2 (by rfl) ⟨751461, by rfl⟩ : syracuseStep 2003897 = 1502923) (by norm_num)
theorem B5343725 : Blo 1975435 5343725 := bstep (se 3 (by rfl) ⟨1001948, by rfl⟩ : syracuseStep 5343725 = 2003897) B2003897
theorem B3562483 : Blo 1975435 3562483 := bstep (se 1 (by rfl) ⟨2671862, by rfl⟩ : syracuseStep 3562483 = 5343725) B5343725
theorem B4749977 : Blo 1975435 4749977 := bstep (se 2 (by rfl) ⟨1781241, by rfl⟩ : syracuseStep 4749977 = 3562483) B3562483
theorem B3166651 : Blo 1975435 3166651 := bstep (se 1 (by rfl) ⟨2374988, by rfl⟩ : syracuseStep 3166651 = 4749977) B4749977
theorem B4222201 : Blo 1975435 4222201 := bstep (se 2 (by rfl) ⟨1583325, by rfl⟩ : syracuseStep 4222201 = 3166651) B3166651
theorem B5629601 : Blo 1975435 5629601 := bstep (se 2 (by rfl) ⟨2111100, by rfl⟩ : syracuseStep 5629601 = 4222201) B4222201
theorem B3753067 : Blo 1975435 3753067 := bstep (se 1 (by rfl) ⟨2814800, by rfl⟩ : syracuseStep 3753067 = 5629601) B5629601
theorem B5004089 : Blo 1975435 5004089 := bstep (se 2 (by rfl) ⟨1876533, by rfl⟩ : syracuseStep 5004089 = 3753067) B3753067
theorem B3336059 : Blo 1975435 3336059 := bstep (se 1 (by rfl) ⟨2502044, by rfl⟩ : syracuseStep 3336059 = 5004089) B5004089
theorem B2224039 : Blo 1975435 2224039 := bstep (se 1 (by rfl) ⟨1668029, by rfl⟩ : syracuseStep 2224039 = 3336059) B3336059
theorem B2965385 : Blo 1975435 2965385 := bstep (se 2 (by rfl) ⟨1112019, by rfl⟩ : syracuseStep 2965385 = 2224039) B2224039
theorem B1976923 : Blo 1975435 1976923 := bstep (se 1 (by rfl) ⟨1482692, by rfl⟩ : syracuseStep 1976923 = 2965385) B2965385
theorem B10008197 : Blo 1975435 10008197 := bbase (se 4 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 10008197 = 1876537) (by norm_num)
theorem B6672131 : Blo 1975435 6672131 := bstep (se 1 (by rfl) ⟨5004098, by rfl⟩ : syracuseStep 6672131 = 10008197) B10008197
theorem B4448087 : Blo 1975435 4448087 := bstep (se 1 (by rfl) ⟨3336065, by rfl⟩ : syracuseStep 4448087 = 6672131) B6672131
theorem B2965391 : Blo 1975435 2965391 := bstep (se 1 (by rfl) ⟨2224043, by rfl⟩ : syracuseStep 2965391 = 4448087) B4448087
theorem B1976927 : Blo 1975435 1976927 := bstep (se 1 (by rfl) ⟨1482695, by rfl⟩ : syracuseStep 1976927 = 2965391) B2965391
theorem B2965397 : Blo 1975435 2965397 := bbase (se 6 (by rfl) ⟨69501, by rfl⟩ : syracuseStep 2965397 = 139003) (by norm_num)
theorem B1976931 : Blo 1975435 1976931 := bstep (se 1 (by rfl) ⟨1482698, by rfl⟩ : syracuseStep 1976931 = 2965397) B2965397
theorem B2111113 : Blo 1975435 2111113 := bbase (se 2 (by rfl) ⟨791667, by rfl⟩ : syracuseStep 2111113 = 1583335) (by norm_num)
theorem B11259269 : Blo 1975435 11259269 := bstep (se 4 (by rfl) ⟨1055556, by rfl⟩ : syracuseStep 11259269 = 2111113) B2111113
theorem B7506179 : Blo 1975435 7506179 := bstep (se 1 (by rfl) ⟨5629634, by rfl⟩ : syracuseStep 7506179 = 11259269) B11259269
theorem B5004119 : Blo 1975435 5004119 := bstep (se 1 (by rfl) ⟨3753089, by rfl⟩ : syracuseStep 5004119 = 7506179) B7506179
theorem B3336079 : Blo 1975435 3336079 := bstep (se 1 (by rfl) ⟨2502059, by rfl⟩ : syracuseStep 3336079 = 5004119) B5004119
theorem B4448105 : Blo 1975435 4448105 := bstep (se 2 (by rfl) ⟨1668039, by rfl⟩ : syracuseStep 4448105 = 3336079) B3336079
theorem B2965403 : Blo 1975435 2965403 := bstep (se 1 (by rfl) ⟨2224052, by rfl⟩ : syracuseStep 2965403 = 4448105) B4448105
theorem B1976935 : Blo 1975435 1976935 := bstep (se 1 (by rfl) ⟨1482701, by rfl⟩ : syracuseStep 1976935 = 2965403) B2965403
theorem B2224057 : Blo 1975435 2224057 := bbase (se 2 (by rfl) ⟨834021, by rfl⟩ : syracuseStep 2224057 = 1668043) (by norm_num)
theorem B2965409 : Blo 1975435 2965409 := bstep (se 2 (by rfl) ⟨1112028, by rfl⟩ : syracuseStep 2965409 = 2224057) B2224057
theorem B1976939 : Blo 1975435 1976939 := bstep (se 1 (by rfl) ⟨1482704, by rfl⟩ : syracuseStep 1976939 = 2965409) B2965409
theorem B6333365 : Blo 1975435 6333365 := bbase (se 5 (by rfl) ⟨296876, by rfl⟩ : syracuseStep 6333365 = 593753) (by norm_num)
theorem B4222243 : Blo 1975435 4222243 := bstep (se 1 (by rfl) ⟨3166682, by rfl⟩ : syracuseStep 4222243 = 6333365) B6333365
theorem B5629657 : Blo 1975435 5629657 := bstep (se 2 (by rfl) ⟨2111121, by rfl⟩ : syracuseStep 5629657 = 4222243) B4222243
theorem B7506209 : Blo 1975435 7506209 := bstep (se 2 (by rfl) ⟨2814828, by rfl⟩ : syracuseStep 7506209 = 5629657) B5629657
theorem B5004139 : Blo 1975435 5004139 := bstep (se 1 (by rfl) ⟨3753104, by rfl⟩ : syracuseStep 5004139 = 7506209) B7506209
theorem B6672185 : Blo 1975435 6672185 := bstep (se 2 (by rfl) ⟨2502069, by rfl⟩ : syracuseStep 6672185 = 5004139) B5004139
theorem B4448123 : Blo 1975435 4448123 := bstep (se 1 (by rfl) ⟨3336092, by rfl⟩ : syracuseStep 4448123 = 6672185) B6672185
theorem B2965415 : Blo 1975435 2965415 := bstep (se 1 (by rfl) ⟨2224061, by rfl⟩ : syracuseStep 2965415 = 4448123) B4448123
theorem B1976943 : Blo 1975435 1976943 := bstep (se 1 (by rfl) ⟨1482707, by rfl⟩ : syracuseStep 1976943 = 2965415) B2965415
theorem B2965421 : Blo 1975435 2965421 := bbase (se 3 (by rfl) ⟨556016, by rfl⟩ : syracuseStep 2965421 = 1112033) (by norm_num)
theorem B1976947 : Blo 1975435 1976947 := bstep (se 1 (by rfl) ⟨1482710, by rfl⟩ : syracuseStep 1976947 = 2965421) B2965421
theorem B4448141 : Blo 1975435 4448141 := bbase (se 3 (by rfl) ⟨834026, by rfl⟩ : syracuseStep 4448141 = 1668053) (by norm_num)
theorem B2965427 : Blo 1975435 2965427 := bstep (se 1 (by rfl) ⟨2224070, by rfl⟩ : syracuseStep 2965427 = 4448141) B4448141
theorem B1976951 : Blo 1975435 1976951 := bstep (se 1 (by rfl) ⟨1482713, by rfl⟩ : syracuseStep 1976951 = 2965427) B2965427
theorem B2502085 : Blo 1975435 2502085 := bbase (se 4 (by rfl) ⟨234570, by rfl⟩ : syracuseStep 2502085 = 469141) (by norm_num)
theorem B3336113 : Blo 1975435 3336113 := bstep (se 2 (by rfl) ⟨1251042, by rfl⟩ : syracuseStep 3336113 = 2502085) B2502085
theorem B2224075 : Blo 1975435 2224075 := bstep (se 1 (by rfl) ⟨1668056, by rfl⟩ : syracuseStep 2224075 = 3336113) B3336113
theorem B2965433 : Blo 1975435 2965433 := bstep (se 2 (by rfl) ⟨1112037, by rfl⟩ : syracuseStep 2965433 = 2224075) B2224075
theorem B1976955 : Blo 1975435 1976955 := bstep (se 1 (by rfl) ⟨1482716, by rfl⟩ : syracuseStep 1976955 = 2965433) B2965433
theorem B24047189 : Blo 1975435 24047189 := bbase (se 8 (by rfl) ⟨140901, by rfl⟩ : syracuseStep 24047189 = 281803) (by norm_num)
theorem B16031459 : Blo 1975435 16031459 := bstep (se 1 (by rfl) ⟨12023594, by rfl⟩ : syracuseStep 16031459 = 24047189) B24047189
theorem B10687639 : Blo 1975435 10687639 := bstep (se 1 (by rfl) ⟨8015729, by rfl⟩ : syracuseStep 10687639 = 16031459) B16031459
theorem B14250185 : Blo 1975435 14250185 := bstep (se 2 (by rfl) ⟨5343819, by rfl⟩ : syracuseStep 14250185 = 10687639) B10687639
theorem B9500123 : Blo 1975435 9500123 := bstep (se 1 (by rfl) ⟨7125092, by rfl⟩ : syracuseStep 9500123 = 14250185) B14250185
theorem B25333661 : Blo 1975435 25333661 := bstep (se 3 (by rfl) ⟨4750061, by rfl⟩ : syracuseStep 25333661 = 9500123) B9500123
theorem B16889107 : Blo 1975435 16889107 := bstep (se 1 (by rfl) ⟨12666830, by rfl⟩ : syracuseStep 16889107 = 25333661) B25333661
theorem B22518809 : Blo 1975435 22518809 := bstep (se 2 (by rfl) ⟨8444553, by rfl⟩ : syracuseStep 22518809 = 16889107) B16889107
theorem B15012539 : Blo 1975435 15012539 := bstep (se 1 (by rfl) ⟨11259404, by rfl⟩ : syracuseStep 15012539 = 22518809) B22518809
theorem B10008359 : Blo 1975435 10008359 := bstep (se 1 (by rfl) ⟨7506269, by rfl⟩ : syracuseStep 10008359 = 15012539) B15012539
theorem B6672239 : Blo 1975435 6672239 := bstep (se 1 (by rfl) ⟨5004179, by rfl⟩ : syracuseStep 6672239 = 10008359) B10008359
theorem B4448159 : Blo 1975435 4448159 := bstep (se 1 (by rfl) ⟨3336119, by rfl⟩ : syracuseStep 4448159 = 6672239) B6672239
theorem B2965439 : Blo 1975435 2965439 := bstep (se 1 (by rfl) ⟨2224079, by rfl⟩ : syracuseStep 2965439 = 4448159) B4448159
theorem B1976959 : Blo 1975435 1976959 := bstep (se 1 (by rfl) ⟨1482719, by rfl⟩ : syracuseStep 1976959 = 2965439) B2965439
theorem B2965445 : Blo 1975435 2965445 := bbase (se 4 (by rfl) ⟨278010, by rfl⟩ : syracuseStep 2965445 = 556021) (by norm_num)
theorem B1976963 : Blo 1975435 1976963 := bstep (se 1 (by rfl) ⟨1482722, by rfl⟩ : syracuseStep 1976963 = 2965445) B2965445
theorem B3336133 : Blo 1975435 3336133 := bbase (se 4 (by rfl) ⟨312762, by rfl⟩ : syracuseStep 3336133 = 625525) (by norm_num)
theorem B4448177 : Blo 1975435 4448177 := bstep (se 2 (by rfl) ⟨1668066, by rfl⟩ : syracuseStep 4448177 = 3336133) B3336133
theorem B2965451 : Blo 1975435 2965451 := bstep (se 1 (by rfl) ⟨2224088, by rfl⟩ : syracuseStep 2965451 = 4448177) B4448177
theorem B1976967 : Blo 1975435 1976967 := bstep (se 1 (by rfl) ⟨1482725, by rfl⟩ : syracuseStep 1976967 = 2965451) B2965451
theorem B2224093 : Blo 1975435 2224093 := bbase (se 3 (by rfl) ⟨417017, by rfl⟩ : syracuseStep 2224093 = 834035) (by norm_num)
theorem B2965457 : Blo 1975435 2965457 := bstep (se 2 (by rfl) ⟨1112046, by rfl⟩ : syracuseStep 2965457 = 2224093) B2224093
theorem B1976971 : Blo 1975435 1976971 := bstep (se 1 (by rfl) ⟨1482728, by rfl⟩ : syracuseStep 1976971 = 2965457) B2965457
theorem B6672293 : Blo 1975435 6672293 := bbase (se 4 (by rfl) ⟨625527, by rfl⟩ : syracuseStep 6672293 = 1251055) (by norm_num)
theorem B4448195 : Blo 1975435 4448195 := bstep (se 1 (by rfl) ⟨3336146, by rfl⟩ : syracuseStep 4448195 = 6672293) B6672293
theorem B2965463 : Blo 1975435 2965463 := bstep (se 1 (by rfl) ⟨2224097, by rfl⟩ : syracuseStep 2965463 = 4448195) B4448195
theorem B1976975 : Blo 1975435 1976975 := bstep (se 1 (by rfl) ⟨1482731, by rfl⟩ : syracuseStep 1976975 = 2965463) B2965463
theorem B2965469 : Blo 1975435 2965469 := bbase (se 3 (by rfl) ⟨556025, by rfl⟩ : syracuseStep 2965469 = 1112051) (by norm_num)
theorem B1976979 : Blo 1975435 1976979 := bstep (se 1 (by rfl) ⟨1482734, by rfl⟩ : syracuseStep 1976979 = 2965469) B2965469
theorem B4448213 : Blo 1975435 4448213 := bbase (se 7 (by rfl) ⟨52127, by rfl⟩ : syracuseStep 4448213 = 104255) (by norm_num)
theorem B2965475 : Blo 1975435 2965475 := bstep (se 1 (by rfl) ⟨2224106, by rfl⟩ : syracuseStep 2965475 = 4448213) B4448213
theorem B1976983 : Blo 1975435 1976983 := bstep (se 1 (by rfl) ⟨1482737, by rfl⟩ : syracuseStep 1976983 = 2965475) B2965475
theorem B2375065 : Blo 1975435 2375065 := bbase (se 2 (by rfl) ⟨890649, by rfl⟩ : syracuseStep 2375065 = 1781299) (by norm_num)
theorem B12667013 : Blo 1975435 12667013 := bstep (se 4 (by rfl) ⟨1187532, by rfl⟩ : syracuseStep 12667013 = 2375065) B2375065
theorem B8444675 : Blo 1975435 8444675 := bstep (se 1 (by rfl) ⟨6333506, by rfl⟩ : syracuseStep 8444675 = 12667013) B12667013
theorem B5629783 : Blo 1975435 5629783 := bstep (se 1 (by rfl) ⟨4222337, by rfl⟩ : syracuseStep 5629783 = 8444675) B8444675
theorem B7506377 : Blo 1975435 7506377 := bstep (se 2 (by rfl) ⟨2814891, by rfl⟩ : syracuseStep 7506377 = 5629783) B5629783
theorem B5004251 : Blo 1975435 5004251 := bstep (se 1 (by rfl) ⟨3753188, by rfl⟩ : syracuseStep 5004251 = 7506377) B7506377
theorem B3336167 : Blo 1975435 3336167 := bstep (se 1 (by rfl) ⟨2502125, by rfl⟩ : syracuseStep 3336167 = 5004251) B5004251
theorem B2224111 : Blo 1975435 2224111 := bstep (se 1 (by rfl) ⟨1668083, by rfl⟩ : syracuseStep 2224111 = 3336167) B3336167
theorem B2965481 : Blo 1975435 2965481 := bstep (se 2 (by rfl) ⟨1112055, by rfl⟩ : syracuseStep 2965481 = 2224111) B2224111
theorem B1976987 : Blo 1975435 1976987 := bstep (se 1 (by rfl) ⟨1482740, by rfl⟩ : syracuseStep 1976987 = 2965481) B2965481
theorem B8015861 : Blo 1975435 8015861 := bbase (se 5 (by rfl) ⟨375743, by rfl⟩ : syracuseStep 8015861 = 751487) (by norm_num)
theorem B5343907 : Blo 1975435 5343907 := bstep (se 1 (by rfl) ⟨4007930, by rfl⟩ : syracuseStep 5343907 = 8015861) B8015861
theorem B7125209 : Blo 1975435 7125209 := bstep (se 2 (by rfl) ⟨2671953, by rfl⟩ : syracuseStep 7125209 = 5343907) B5343907
theorem B4750139 : Blo 1975435 4750139 := bstep (se 1 (by rfl) ⟨3562604, by rfl⟩ : syracuseStep 4750139 = 7125209) B7125209
theorem B3166759 : Blo 1975435 3166759 := bstep (se 1 (by rfl) ⟨2375069, by rfl⟩ : syracuseStep 3166759 = 4750139) B4750139
theorem B16889381 : Blo 1975435 16889381 := bstep (se 4 (by rfl) ⟨1583379, by rfl⟩ : syracuseStep 16889381 = 3166759) B3166759
theorem B11259587 : Blo 1975435 11259587 := bstep (se 1 (by rfl) ⟨8444690, by rfl⟩ : syracuseStep 11259587 = 16889381) B16889381
theorem B7506391 : Blo 1975435 7506391 := bstep (se 1 (by rfl) ⟨5629793, by rfl⟩ : syracuseStep 7506391 = 11259587) B11259587
theorem B10008521 : Blo 1975435 10008521 := bstep (se 2 (by rfl) ⟨3753195, by rfl⟩ : syracuseStep 10008521 = 7506391) B7506391
theorem B6672347 : Blo 1975435 6672347 := bstep (se 1 (by rfl) ⟨5004260, by rfl⟩ : syracuseStep 6672347 = 10008521) B10008521
theorem B4448231 : Blo 1975435 4448231 := bstep (se 1 (by rfl) ⟨3336173, by rfl⟩ : syracuseStep 4448231 = 6672347) B6672347
theorem B2965487 : Blo 1975435 2965487 := bstep (se 1 (by rfl) ⟨2224115, by rfl⟩ : syracuseStep 2965487 = 4448231) B4448231
theorem B1976991 : Blo 1975435 1976991 := bstep (se 1 (by rfl) ⟨1482743, by rfl⟩ : syracuseStep 1976991 = 2965487) B2965487
theorem B2965493 : Blo 1975435 2965493 := bbase (se 5 (by rfl) ⟨139007, by rfl⟩ : syracuseStep 2965493 = 278015) (by norm_num)
theorem B1976995 : Blo 1975435 1976995 := bstep (se 1 (by rfl) ⟨1482746, by rfl⟩ : syracuseStep 1976995 = 2965493) B2965493
theorem B4508941 : Blo 1975435 4508941 := bbase (se 3 (by rfl) ⟨845426, by rfl⟩ : syracuseStep 4508941 = 1690853) (by norm_num)
theorem B6011921 : Blo 1975435 6011921 := bstep (se 2 (by rfl) ⟨2254470, by rfl⟩ : syracuseStep 6011921 = 4508941) B4508941
theorem B16031789 : Blo 1975435 16031789 := bstep (se 3 (by rfl) ⟨3005960, by rfl⟩ : syracuseStep 16031789 = 6011921) B6011921
theorem B10687859 : Blo 1975435 10687859 := bstep (se 1 (by rfl) ⟨8015894, by rfl⟩ : syracuseStep 10687859 = 16031789) B16031789
theorem B7125239 : Blo 1975435 7125239 := bstep (se 1 (by rfl) ⟨5343929, by rfl⟩ : syracuseStep 7125239 = 10687859) B10687859
theorem B4750159 : Blo 1975435 4750159 := bstep (se 1 (by rfl) ⟨3562619, by rfl⟩ : syracuseStep 4750159 = 7125239) B7125239
theorem B6333545 : Blo 1975435 6333545 := bstep (se 2 (by rfl) ⟨2375079, by rfl⟩ : syracuseStep 6333545 = 4750159) B4750159
theorem B4222363 : Blo 1975435 4222363 := bstep (se 1 (by rfl) ⟨3166772, by rfl⟩ : syracuseStep 4222363 = 6333545) B6333545
theorem B5629817 : Blo 1975435 5629817 := bstep (se 2 (by rfl) ⟨2111181, by rfl⟩ : syracuseStep 5629817 = 4222363) B4222363
theorem B3753211 : Blo 1975435 3753211 := bstep (se 1 (by rfl) ⟨2814908, by rfl⟩ : syracuseStep 3753211 = 5629817) B5629817
theorem B5004281 : Blo 1975435 5004281 := bstep (se 2 (by rfl) ⟨1876605, by rfl⟩ : syracuseStep 5004281 = 3753211) B3753211
theorem B3336187 : Blo 1975435 3336187 := bstep (se 1 (by rfl) ⟨2502140, by rfl⟩ : syracuseStep 3336187 = 5004281) B5004281
theorem B4448249 : Blo 1975435 4448249 := bstep (se 2 (by rfl) ⟨1668093, by rfl⟩ : syracuseStep 4448249 = 3336187) B3336187
theorem B2965499 : Blo 1975435 2965499 := bstep (se 1 (by rfl) ⟨2224124, by rfl⟩ : syracuseStep 2965499 = 4448249) B4448249
theorem B1976999 : Blo 1975435 1976999 := bstep (se 1 (by rfl) ⟨1482749, by rfl⟩ : syracuseStep 1976999 = 2965499) B2965499
theorem B2224129 : Blo 1975435 2224129 := bbase (se 2 (by rfl) ⟨834048, by rfl⟩ : syracuseStep 2224129 = 1668097) (by norm_num)
theorem B2965505 : Blo 1975435 2965505 := bstep (se 2 (by rfl) ⟨1112064, by rfl⟩ : syracuseStep 2965505 = 2224129) B2224129
theorem B1977003 : Blo 1975435 1977003 := bstep (se 1 (by rfl) ⟨1482752, by rfl⟩ : syracuseStep 1977003 = 2965505) B2965505
theorem B5004301 : Blo 1975435 5004301 := bbase (se 3 (by rfl) ⟨938306, by rfl⟩ : syracuseStep 5004301 = 1876613) (by norm_num)
theorem B6672401 : Blo 1975435 6672401 := bstep (se 2 (by rfl) ⟨2502150, by rfl⟩ : syracuseStep 6672401 = 5004301) B5004301
theorem B4448267 : Blo 1975435 4448267 := bstep (se 1 (by rfl) ⟨3336200, by rfl⟩ : syracuseStep 4448267 = 6672401) B6672401
theorem B2965511 : Blo 1975435 2965511 := bstep (se 1 (by rfl) ⟨2224133, by rfl⟩ : syracuseStep 2965511 = 4448267) B4448267
theorem B1977007 : Blo 1975435 1977007 := bstep (se 1 (by rfl) ⟨1482755, by rfl⟩ : syracuseStep 1977007 = 2965511) B2965511
theorem B2965517 : Blo 1975435 2965517 := bbase (se 3 (by rfl) ⟨556034, by rfl⟩ : syracuseStep 2965517 = 1112069) (by norm_num)
theorem B1977011 : Blo 1975435 1977011 := bstep (se 1 (by rfl) ⟨1482758, by rfl⟩ : syracuseStep 1977011 = 2965517) B2965517
theorem B4448285 : Blo 1975435 4448285 := bbase (se 3 (by rfl) ⟨834053, by rfl⟩ : syracuseStep 4448285 = 1668107) (by norm_num)
theorem B2965523 : Blo 1975435 2965523 := bstep (se 1 (by rfl) ⟨2224142, by rfl⟩ : syracuseStep 2965523 = 4448285) B4448285
theorem B1977015 : Blo 1975435 1977015 := bstep (se 1 (by rfl) ⟨1482761, by rfl⟩ : syracuseStep 1977015 = 2965523) B2965523
theorem B3336221 : Blo 1975435 3336221 := bbase (se 3 (by rfl) ⟨625541, by rfl⟩ : syracuseStep 3336221 = 1251083) (by norm_num)
theorem B2224147 : Blo 1975435 2224147 := bstep (se 1 (by rfl) ⟨1668110, by rfl⟩ : syracuseStep 2224147 = 3336221) B3336221
theorem B2965529 : Blo 1975435 2965529 := bstep (se 2 (by rfl) ⟨1112073, by rfl⟩ : syracuseStep 2965529 = 2224147) B2224147
theorem B1977019 : Blo 1975435 1977019 := bstep (se 1 (by rfl) ⟨1482764, by rfl⟩ : syracuseStep 1977019 = 2965529) B2965529
theorem B32063957 : Blo 1975435 32063957 := bbase (se 7 (by rfl) ⟨375749, by rfl⟩ : syracuseStep 32063957 = 751499) (by norm_num)
theorem B21375971 : Blo 1975435 21375971 := bstep (se 1 (by rfl) ⟨16031978, by rfl⟩ : syracuseStep 21375971 = 32063957) B32063957
theorem B14250647 : Blo 1975435 14250647 := bstep (se 1 (by rfl) ⟨10687985, by rfl⟩ : syracuseStep 14250647 = 21375971) B21375971
theorem B9500431 : Blo 1975435 9500431 := bstep (se 1 (by rfl) ⟨7125323, by rfl⟩ : syracuseStep 9500431 = 14250647) B14250647
theorem B12667241 : Blo 1975435 12667241 := bstep (se 2 (by rfl) ⟨4750215, by rfl⟩ : syracuseStep 12667241 = 9500431) B9500431
theorem B8444827 : Blo 1975435 8444827 := bstep (se 1 (by rfl) ⟨6333620, by rfl⟩ : syracuseStep 8444827 = 12667241) B12667241
theorem B11259769 : Blo 1975435 11259769 := bstep (se 2 (by rfl) ⟨4222413, by rfl⟩ : syracuseStep 11259769 = 8444827) B8444827
theorem B15013025 : Blo 1975435 15013025 := bstep (se 2 (by rfl) ⟨5629884, by rfl⟩ : syracuseStep 15013025 = 11259769) B11259769
theorem B10008683 : Blo 1975435 10008683 := bstep (se 1 (by rfl) ⟨7506512, by rfl⟩ : syracuseStep 10008683 = 15013025) B15013025
theorem B6672455 : Blo 1975435 6672455 := bstep (se 1 (by rfl) ⟨5004341, by rfl⟩ : syracuseStep 6672455 = 10008683) B10008683
theorem B4448303 : Blo 1975435 4448303 := bstep (se 1 (by rfl) ⟨3336227, by rfl⟩ : syracuseStep 4448303 = 6672455) B6672455
theorem B2965535 : Blo 1975435 2965535 := bstep (se 1 (by rfl) ⟨2224151, by rfl⟩ : syracuseStep 2965535 = 4448303) B4448303
theorem B1977023 : Blo 1975435 1977023 := bstep (se 1 (by rfl) ⟨1482767, by rfl⟩ : syracuseStep 1977023 = 2965535) B2965535
theorem B2965541 : Blo 1975435 2965541 := bbase (se 4 (by rfl) ⟨278019, by rfl⟩ : syracuseStep 2965541 = 556039) (by norm_num)
theorem B1977027 : Blo 1975435 1977027 := bstep (se 1 (by rfl) ⟨1482770, by rfl⟩ : syracuseStep 1977027 = 2965541) B2965541
theorem B2502181 : Blo 1975435 2502181 := bbase (se 4 (by rfl) ⟨234579, by rfl⟩ : syracuseStep 2502181 = 469159) (by norm_num)
theorem B3336241 : Blo 1975435 3336241 := bstep (se 2 (by rfl) ⟨1251090, by rfl⟩ : syracuseStep 3336241 = 2502181) B2502181
theorem B4448321 : Blo 1975435 4448321 := bstep (se 2 (by rfl) ⟨1668120, by rfl⟩ : syracuseStep 4448321 = 3336241) B3336241
theorem B2965547 : Blo 1975435 2965547 := bstep (se 1 (by rfl) ⟨2224160, by rfl⟩ : syracuseStep 2965547 = 4448321) B4448321
theorem B1977031 : Blo 1975435 1977031 := bstep (se 1 (by rfl) ⟨1482773, by rfl⟩ : syracuseStep 1977031 = 2965547) B2965547
theorem B2224165 : Blo 1975435 2224165 := bbase (se 4 (by rfl) ⟨208515, by rfl⟩ : syracuseStep 2224165 = 417031) (by norm_num)
theorem B2965553 : Blo 1975435 2965553 := bstep (se 2 (by rfl) ⟨1112082, by rfl⟩ : syracuseStep 2965553 = 2224165) B2224165
theorem B1977035 : Blo 1975435 1977035 := bstep (se 1 (by rfl) ⟨1482776, by rfl⟩ : syracuseStep 1977035 = 2965553) B2965553
theorem B12024085 : Blo 1975435 12024085 := bbase (se 6 (by rfl) ⟨281814, by rfl⟩ : syracuseStep 12024085 = 563629) (by norm_num)
theorem B16032113 : Blo 1975435 16032113 := bstep (se 2 (by rfl) ⟨6012042, by rfl⟩ : syracuseStep 16032113 = 12024085) B12024085
theorem B10688075 : Blo 1975435 10688075 := bstep (se 1 (by rfl) ⟨8016056, by rfl⟩ : syracuseStep 10688075 = 16032113) B16032113
theorem B7125383 : Blo 1975435 7125383 := bstep (se 1 (by rfl) ⟨5344037, by rfl⟩ : syracuseStep 7125383 = 10688075) B10688075
theorem B4750255 : Blo 1975435 4750255 := bstep (se 1 (by rfl) ⟨3562691, by rfl⟩ : syracuseStep 4750255 = 7125383) B7125383
theorem B6333673 : Blo 1975435 6333673 := bstep (se 2 (by rfl) ⟨2375127, by rfl⟩ : syracuseStep 6333673 = 4750255) B4750255
theorem B8444897 : Blo 1975435 8444897 := bstep (se 2 (by rfl) ⟨3166836, by rfl⟩ : syracuseStep 8444897 = 6333673) B6333673
theorem B5629931 : Blo 1975435 5629931 := bstep (se 1 (by rfl) ⟨4222448, by rfl⟩ : syracuseStep 5629931 = 8444897) B8444897
theorem B3753287 : Blo 1975435 3753287 := bstep (se 1 (by rfl) ⟨2814965, by rfl⟩ : syracuseStep 3753287 = 5629931) B5629931
theorem B2502191 : Blo 1975435 2502191 := bstep (se 1 (by rfl) ⟨1876643, by rfl⟩ : syracuseStep 2502191 = 3753287) B3753287
theorem B6672509 : Blo 1975435 6672509 := bstep (se 3 (by rfl) ⟨1251095, by rfl⟩ : syracuseStep 6672509 = 2502191) B2502191
theorem B4448339 : Blo 1975435 4448339 := bstep (se 1 (by rfl) ⟨3336254, by rfl⟩ : syracuseStep 4448339 = 6672509) B6672509
theorem B2965559 : Blo 1975435 2965559 := bstep (se 1 (by rfl) ⟨2224169, by rfl⟩ : syracuseStep 2965559 = 4448339) B4448339
theorem B1977039 : Blo 1975435 1977039 := bstep (se 1 (by rfl) ⟨1482779, by rfl⟩ : syracuseStep 1977039 = 2965559) B2965559
theorem B2965565 : Blo 1975435 2965565 := bbase (se 3 (by rfl) ⟨556043, by rfl⟩ : syracuseStep 2965565 = 1112087) (by norm_num)
theorem B1977043 : Blo 1975435 1977043 := bstep (se 1 (by rfl) ⟨1482782, by rfl⟩ : syracuseStep 1977043 = 2965565) B2965565
theorem B4448357 : Blo 1975435 4448357 := bbase (se 4 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 4448357 = 834067) (by norm_num)
theorem B2965571 : Blo 1975435 2965571 := bstep (se 1 (by rfl) ⟨2224178, by rfl⟩ : syracuseStep 2965571 = 4448357) B4448357
theorem B1977047 : Blo 1975435 1977047 := bstep (se 1 (by rfl) ⟨1482785, by rfl⟩ : syracuseStep 1977047 = 2965571) B2965571
theorem B5004413 : Blo 1975435 5004413 := bbase (se 3 (by rfl) ⟨938327, by rfl⟩ : syracuseStep 5004413 = 1876655) (by norm_num)
theorem B3336275 : Blo 1975435 3336275 := bstep (se 1 (by rfl) ⟨2502206, by rfl⟩ : syracuseStep 3336275 = 5004413) B5004413
theorem B2224183 : Blo 1975435 2224183 := bstep (se 1 (by rfl) ⟨1668137, by rfl⟩ : syracuseStep 2224183 = 3336275) B3336275
theorem B2965577 : Blo 1975435 2965577 := bstep (se 2 (by rfl) ⟨1112091, by rfl⟩ : syracuseStep 2965577 = 2224183) B2224183
theorem B1977051 : Blo 1975435 1977051 := bstep (se 1 (by rfl) ⟨1482788, by rfl⟩ : syracuseStep 1977051 = 2965577) B2965577
theorem B3753317 : Blo 1975435 3753317 := bbase (se 4 (by rfl) ⟨351873, by rfl⟩ : syracuseStep 3753317 = 703747) (by norm_num)
theorem B10008845 : Blo 1975435 10008845 := bstep (se 3 (by rfl) ⟨1876658, by rfl⟩ : syracuseStep 10008845 = 3753317) B3753317
theorem B6672563 : Blo 1975435 6672563 := bstep (se 1 (by rfl) ⟨5004422, by rfl⟩ : syracuseStep 6672563 = 10008845) B10008845
theorem B4448375 : Blo 1975435 4448375 := bstep (se 1 (by rfl) ⟨3336281, by rfl⟩ : syracuseStep 4448375 = 6672563) B6672563
theorem B2965583 : Blo 1975435 2965583 := bstep (se 1 (by rfl) ⟨2224187, by rfl⟩ : syracuseStep 2965583 = 4448375) B4448375
theorem B1977055 : Blo 1975435 1977055 := bstep (se 1 (by rfl) ⟨1482791, by rfl⟩ : syracuseStep 1977055 = 2965583) B2965583
theorem B2965589 : Blo 1975435 2965589 := bbase (se 8 (by rfl) ⟨17376, by rfl⟩ : syracuseStep 2965589 = 34753) (by norm_num)
theorem B1977059 : Blo 1975435 1977059 := bstep (se 1 (by rfl) ⟨1482794, by rfl⟩ : syracuseStep 1977059 = 2965589) B2965589
theorem B8125525 : Blo 1975435 8125525 := bbase (se 8 (by rfl) ⟨47610, by rfl⟩ : syracuseStep 8125525 = 95221) (by norm_num)
theorem B10834033 : Blo 1975435 10834033 := bstep (se 2 (by rfl) ⟨4062762, by rfl⟩ : syracuseStep 10834033 = 8125525) B8125525
theorem B14445377 : Blo 1975435 14445377 := bstep (se 2 (by rfl) ⟨5417016, by rfl⟩ : syracuseStep 14445377 = 10834033) B10834033
theorem B9630251 : Blo 1975435 9630251 := bstep (se 1 (by rfl) ⟨7222688, by rfl⟩ : syracuseStep 9630251 = 14445377) B14445377
theorem B6420167 : Blo 1975435 6420167 := bstep (se 1 (by rfl) ⟨4815125, by rfl⟩ : syracuseStep 6420167 = 9630251) B9630251
theorem B4280111 : Blo 1975435 4280111 := bstep (se 1 (by rfl) ⟨3210083, by rfl⟩ : syracuseStep 4280111 = 6420167) B6420167
theorem B2853407 : Blo 1975435 2853407 := bstep (se 1 (by rfl) ⟨2140055, by rfl⟩ : syracuseStep 2853407 = 4280111) B4280111
theorem B7609085 : Blo 1975435 7609085 := bstep (se 3 (by rfl) ⟨1426703, by rfl⟩ : syracuseStep 7609085 = 2853407) B2853407
theorem B5072723 : Blo 1975435 5072723 := bstep (se 1 (by rfl) ⟨3804542, by rfl⟩ : syracuseStep 5072723 = 7609085) B7609085
theorem B3381815 : Blo 1975435 3381815 := bstep (se 1 (by rfl) ⟨2536361, by rfl⟩ : syracuseStep 3381815 = 5072723) B5072723
theorem B2254543 : Blo 1975435 2254543 := bstep (se 1 (by rfl) ⟨1690907, by rfl⟩ : syracuseStep 2254543 = 3381815) B3381815
theorem B12024229 : Blo 1975435 12024229 := bstep (se 4 (by rfl) ⟨1127271, by rfl⟩ : syracuseStep 12024229 = 2254543) B2254543
theorem B16032305 : Blo 1975435 16032305 := bstep (se 2 (by rfl) ⟨6012114, by rfl⟩ : syracuseStep 16032305 = 12024229) B12024229
theorem B10688203 : Blo 1975435 10688203 := bstep (se 1 (by rfl) ⟨8016152, by rfl⟩ : syracuseStep 10688203 = 16032305) B16032305
theorem B14250937 : Blo 1975435 14250937 := bstep (se 2 (by rfl) ⟨5344101, by rfl⟩ : syracuseStep 14250937 = 10688203) B10688203
theorem B19001249 : Blo 1975435 19001249 := bstep (se 2 (by rfl) ⟨7125468, by rfl⟩ : syracuseStep 19001249 = 14250937) B14250937
theorem B12667499 : Blo 1975435 12667499 := bstep (se 1 (by rfl) ⟨9500624, by rfl⟩ : syracuseStep 12667499 = 19001249) B19001249
theorem B8444999 : Blo 1975435 8444999 := bstep (se 1 (by rfl) ⟨6333749, by rfl⟩ : syracuseStep 8444999 = 12667499) B12667499
theorem B5629999 : Blo 1975435 5629999 := bstep (se 1 (by rfl) ⟨4222499, by rfl⟩ : syracuseStep 5629999 = 8444999) B8444999
theorem B7506665 : Blo 1975435 7506665 := bstep (se 2 (by rfl) ⟨2814999, by rfl⟩ : syracuseStep 7506665 = 5629999) B5629999
theorem B5004443 : Blo 1975435 5004443 := bstep (se 1 (by rfl) ⟨3753332, by rfl⟩ : syracuseStep 5004443 = 7506665) B7506665
theorem B3336295 : Blo 1975435 3336295 := bstep (se 1 (by rfl) ⟨2502221, by rfl⟩ : syracuseStep 3336295 = 5004443) B5004443
theorem B4448393 : Blo 1975435 4448393 := bstep (se 2 (by rfl) ⟨1668147, by rfl⟩ : syracuseStep 4448393 = 3336295) B3336295
theorem B2965595 : Blo 1975435 2965595 := bstep (se 1 (by rfl) ⟨2224196, by rfl⟩ : syracuseStep 2965595 = 4448393) B4448393
theorem B1977063 : Blo 1975435 1977063 := bstep (se 1 (by rfl) ⟨1482797, by rfl⟩ : syracuseStep 1977063 = 2965595) B2965595
theorem B2224201 : Blo 1975435 2224201 := bbase (se 2 (by rfl) ⟨834075, by rfl⟩ : syracuseStep 2224201 = 1668151) (by norm_num)
theorem B2965601 : Blo 1975435 2965601 := bstep (se 2 (by rfl) ⟨1112100, by rfl⟩ : syracuseStep 2965601 = 2224201) B2224201
theorem B1977067 : Blo 1975435 1977067 := bstep (se 1 (by rfl) ⟨1482800, by rfl⟩ : syracuseStep 1977067 = 2965601) B2965601
theorem B5212109 : Blo 1975435 5212109 := bbase (se 3 (by rfl) ⟨977270, by rfl⟩ : syracuseStep 5212109 = 1954541) (by norm_num)
theorem B3474739 : Blo 1975435 3474739 := bstep (se 1 (by rfl) ⟨2606054, by rfl⟩ : syracuseStep 3474739 = 5212109) B5212109
theorem B4632985 : Blo 1975435 4632985 := bstep (se 2 (by rfl) ⟨1737369, by rfl⟩ : syracuseStep 4632985 = 3474739) B3474739
theorem B6177313 : Blo 1975435 6177313 := bstep (se 2 (by rfl) ⟨2316492, by rfl⟩ : syracuseStep 6177313 = 4632985) B4632985
theorem B8236417 : Blo 1975435 8236417 := bstep (se 2 (by rfl) ⟨3088656, by rfl⟩ : syracuseStep 8236417 = 6177313) B6177313
theorem B10981889 : Blo 1975435 10981889 := bstep (se 2 (by rfl) ⟨4118208, by rfl⟩ : syracuseStep 10981889 = 8236417) B8236417
theorem B7321259 : Blo 1975435 7321259 := bstep (se 1 (by rfl) ⟨5490944, by rfl⟩ : syracuseStep 7321259 = 10981889) B10981889
theorem B4880839 : Blo 1975435 4880839 := bstep (se 1 (by rfl) ⟨3660629, by rfl⟩ : syracuseStep 4880839 = 7321259) B7321259
theorem B6507785 : Blo 1975435 6507785 := bstep (se 2 (by rfl) ⟨2440419, by rfl⟩ : syracuseStep 6507785 = 4880839) B4880839
theorem B4338523 : Blo 1975435 4338523 := bstep (se 1 (by rfl) ⟨3253892, by rfl⟩ : syracuseStep 4338523 = 6507785) B6507785
theorem B23138789 : Blo 1975435 23138789 := bstep (se 4 (by rfl) ⟨2169261, by rfl⟩ : syracuseStep 23138789 = 4338523) B4338523
theorem B246813749 : Blo 1975435 246813749 := bstep (se 5 (by rfl) ⟨11569394, by rfl⟩ : syracuseStep 246813749 = 23138789) B23138789
theorem B164542499 : Blo 1975435 164542499 := bstep (se 1 (by rfl) ⟨123406874, by rfl⟩ : syracuseStep 164542499 = 246813749) B246813749
theorem B109694999 : Blo 1975435 109694999 := bstep (se 1 (by rfl) ⟨82271249, by rfl⟩ : syracuseStep 109694999 = 164542499) B164542499
theorem B73129999 : Blo 1975435 73129999 := bstep (se 1 (by rfl) ⟨54847499, by rfl⟩ : syracuseStep 73129999 = 109694999) B109694999
theorem B97506665 : Blo 1975435 97506665 := bstep (se 2 (by rfl) ⟨36564999, by rfl⟩ : syracuseStep 97506665 = 73129999) B73129999
theorem B65004443 : Blo 1975435 65004443 := bstep (se 1 (by rfl) ⟨48753332, by rfl⟩ : syracuseStep 65004443 = 97506665) B97506665
theorem B43336295 : Blo 1975435 43336295 := bstep (se 1 (by rfl) ⟨32502221, by rfl⟩ : syracuseStep 43336295 = 65004443) B65004443
theorem B28890863 : Blo 1975435 28890863 := bstep (se 1 (by rfl) ⟨21668147, by rfl⟩ : syracuseStep 28890863 = 43336295) B43336295
theorem B19260575 : Blo 1975435 19260575 := bstep (se 1 (by rfl) ⟨14445431, by rfl⟩ : syracuseStep 19260575 = 28890863) B28890863
theorem B12840383 : Blo 1975435 12840383 := bstep (se 1 (by rfl) ⟨9630287, by rfl⟩ : syracuseStep 12840383 = 19260575) B19260575
theorem B8560255 : Blo 1975435 8560255 := bstep (se 1 (by rfl) ⟨6420191, by rfl⟩ : syracuseStep 8560255 = 12840383) B12840383
theorem B11413673 : Blo 1975435 11413673 := bstep (se 2 (by rfl) ⟨4280127, by rfl⟩ : syracuseStep 11413673 = 8560255) B8560255
theorem B7609115 : Blo 1975435 7609115 := bstep (se 1 (by rfl) ⟨5706836, by rfl⟩ : syracuseStep 7609115 = 11413673) B11413673
theorem B5072743 : Blo 1975435 5072743 := bstep (se 1 (by rfl) ⟨3804557, by rfl⟩ : syracuseStep 5072743 = 7609115) B7609115
theorem B6763657 : Blo 1975435 6763657 := bstep (se 2 (by rfl) ⟨2536371, by rfl⟩ : syracuseStep 6763657 = 5072743) B5072743
theorem B9018209 : Blo 1975435 9018209 := bstep (se 2 (by rfl) ⟨3381828, by rfl⟩ : syracuseStep 9018209 = 6763657) B6763657
theorem B6012139 : Blo 1975435 6012139 := bstep (se 1 (by rfl) ⟨4509104, by rfl⟩ : syracuseStep 6012139 = 9018209) B9018209
theorem B8016185 : Blo 1975435 8016185 := bstep (se 2 (by rfl) ⟨3006069, by rfl⟩ : syracuseStep 8016185 = 6012139) B6012139
theorem B5344123 : Blo 1975435 5344123 := bstep (se 1 (by rfl) ⟨4008092, by rfl⟩ : syracuseStep 5344123 = 8016185) B8016185
theorem B7125497 : Blo 1975435 7125497 := bstep (se 2 (by rfl) ⟨2672061, by rfl⟩ : syracuseStep 7125497 = 5344123) B5344123
theorem B4750331 : Blo 1975435 4750331 := bstep (se 1 (by rfl) ⟨3562748, by rfl⟩ : syracuseStep 4750331 = 7125497) B7125497
theorem B12667549 : Blo 1975435 12667549 := bstep (se 3 (by rfl) ⟨2375165, by rfl⟩ : syracuseStep 12667549 = 4750331) B4750331
theorem B16890065 : Blo 1975435 16890065 := bstep (se 2 (by rfl) ⟨6333774, by rfl⟩ : syracuseStep 16890065 = 12667549) B12667549
theorem B11260043 : Blo 1975435 11260043 := bstep (se 1 (by rfl) ⟨8445032, by rfl⟩ : syracuseStep 11260043 = 16890065) B16890065
theorem B7506695 : Blo 1975435 7506695 := bstep (se 1 (by rfl) ⟨5630021, by rfl⟩ : syracuseStep 7506695 = 11260043) B11260043
theorem B5004463 : Blo 1975435 5004463 := bstep (se 1 (by rfl) ⟨3753347, by rfl⟩ : syracuseStep 5004463 = 7506695) B7506695
theorem B6672617 : Blo 1975435 6672617 := bstep (se 2 (by rfl) ⟨2502231, by rfl⟩ : syracuseStep 6672617 = 5004463) B5004463
theorem B4448411 : Blo 1975435 4448411 := bstep (se 1 (by rfl) ⟨3336308, by rfl⟩ : syracuseStep 4448411 = 6672617) B6672617
theorem B2965607 : Blo 1975435 2965607 := bstep (se 1 (by rfl) ⟨2224205, by rfl⟩ : syracuseStep 2965607 = 4448411) B4448411
theorem B1977071 : Blo 1975435 1977071 := bstep (se 1 (by rfl) ⟨1482803, by rfl⟩ : syracuseStep 1977071 = 2965607) B2965607
theorem B2965613 : Blo 1975435 2965613 := bbase (se 3 (by rfl) ⟨556052, by rfl⟩ : syracuseStep 2965613 = 1112105) (by norm_num)
theorem B1977075 : Blo 1975435 1977075 := bstep (se 1 (by rfl) ⟨1482806, by rfl⟩ : syracuseStep 1977075 = 2965613) B2965613
theorem B4448429 : Blo 1975435 4448429 := bbase (se 3 (by rfl) ⟨834080, by rfl⟩ : syracuseStep 4448429 = 1668161) (by norm_num)
theorem B2965619 : Blo 1975435 2965619 := bstep (se 1 (by rfl) ⟨2224214, by rfl⟩ : syracuseStep 2965619 = 4448429) B4448429
theorem B1977079 : Blo 1975435 1977079 := bstep (se 1 (by rfl) ⟨1482809, by rfl⟩ : syracuseStep 1977079 = 2965619) B2965619
theorem B2285329 : Blo 1975435 2285329 := bbase (se 2 (by rfl) ⟨856998, by rfl⟩ : syracuseStep 2285329 = 1713997) (by norm_num)
theorem B3047105 : Blo 1975435 3047105 := bstep (se 2 (by rfl) ⟨1142664, by rfl⟩ : syracuseStep 3047105 = 2285329) B2285329
theorem B2031403 : Blo 1975435 2031403 := bstep (se 1 (by rfl) ⟨1523552, by rfl⟩ : syracuseStep 2031403 = 3047105) B3047105
theorem B2708537 : Blo 1975435 2708537 := bstep (se 2 (by rfl) ⟨1015701, by rfl⟩ : syracuseStep 2708537 = 2031403) B2031403
theorem B7222765 : Blo 1975435 7222765 := bstep (se 3 (by rfl) ⟨1354268, by rfl⟩ : syracuseStep 7222765 = 2708537) B2708537
theorem B9630353 : Blo 1975435 9630353 := bstep (se 2 (by rfl) ⟨3611382, by rfl⟩ : syracuseStep 9630353 = 7222765) B7222765
theorem B6420235 : Blo 1975435 6420235 := bstep (se 1 (by rfl) ⟨4815176, by rfl⟩ : syracuseStep 6420235 = 9630353) B9630353
theorem B8560313 : Blo 1975435 8560313 := bstep (se 2 (by rfl) ⟨3210117, by rfl⟩ : syracuseStep 8560313 = 6420235) B6420235
theorem B5706875 : Blo 1975435 5706875 := bstep (se 1 (by rfl) ⟨4280156, by rfl⟩ : syracuseStep 5706875 = 8560313) B8560313
theorem B3804583 : Blo 1975435 3804583 := bstep (se 1 (by rfl) ⟨2853437, by rfl⟩ : syracuseStep 3804583 = 5706875) B5706875
theorem B5072777 : Blo 1975435 5072777 := bstep (se 2 (by rfl) ⟨1902291, by rfl⟩ : syracuseStep 5072777 = 3804583) B3804583
theorem B3381851 : Blo 1975435 3381851 := bstep (se 1 (by rfl) ⟨2536388, by rfl⟩ : syracuseStep 3381851 = 5072777) B5072777
theorem B2254567 : Blo 1975435 2254567 := bstep (se 1 (by rfl) ⟨1690925, by rfl⟩ : syracuseStep 2254567 = 3381851) B3381851
theorem B3006089 : Blo 1975435 3006089 := bstep (se 2 (by rfl) ⟨1127283, by rfl⟩ : syracuseStep 3006089 = 2254567) B2254567
theorem B2004059 : Blo 1975435 2004059 := bstep (se 1 (by rfl) ⟨1503044, by rfl⟩ : syracuseStep 2004059 = 3006089) B3006089
theorem B5344157 : Blo 1975435 5344157 := bstep (se 3 (by rfl) ⟨1002029, by rfl⟩ : syracuseStep 5344157 = 2004059) B2004059
theorem B14251085 : Blo 1975435 14251085 := bstep (se 3 (by rfl) ⟨2672078, by rfl⟩ : syracuseStep 14251085 = 5344157) B5344157
theorem B9500723 : Blo 1975435 9500723 := bstep (se 1 (by rfl) ⟨7125542, by rfl⟩ : syracuseStep 9500723 = 14251085) B14251085
theorem B6333815 : Blo 1975435 6333815 := bstep (se 1 (by rfl) ⟨4750361, by rfl⟩ : syracuseStep 6333815 = 9500723) B9500723
theorem B4222543 : Blo 1975435 4222543 := bstep (se 1 (by rfl) ⟨3166907, by rfl⟩ : syracuseStep 4222543 = 6333815) B6333815
theorem B5630057 : Blo 1975435 5630057 := bstep (se 2 (by rfl) ⟨2111271, by rfl⟩ : syracuseStep 5630057 = 4222543) B4222543
theorem B3753371 : Blo 1975435 3753371 := bstep (se 1 (by rfl) ⟨2815028, by rfl⟩ : syracuseStep 3753371 = 5630057) B5630057
theorem B2502247 : Blo 1975435 2502247 := bstep (se 1 (by rfl) ⟨1876685, by rfl⟩ : syracuseStep 2502247 = 3753371) B3753371
theorem B3336329 : Blo 1975435 3336329 := bstep (se 2 (by rfl) ⟨1251123, by rfl⟩ : syracuseStep 3336329 = 2502247) B2502247
theorem B2224219 : Blo 1975435 2224219 := bstep (se 1 (by rfl) ⟨1668164, by rfl⟩ : syracuseStep 2224219 = 3336329) B3336329
theorem B2965625 : Blo 1975435 2965625 := bstep (se 2 (by rfl) ⟨1112109, by rfl⟩ : syracuseStep 2965625 = 2224219) B2224219
theorem B1977083 : Blo 1975435 1977083 := bstep (se 1 (by rfl) ⟨1482812, by rfl⟩ : syracuseStep 1977083 = 2965625) B2965625
theorem B4008125 : Blo 1975435 4008125 := bbase (se 3 (by rfl) ⟨751523, by rfl⟩ : syracuseStep 4008125 = 1503047) (by norm_num)
theorem B2672083 : Blo 1975435 2672083 := bstep (se 1 (by rfl) ⟨2004062, by rfl⟩ : syracuseStep 2672083 = 4008125) B4008125
theorem B3562777 : Blo 1975435 3562777 := bstep (se 2 (by rfl) ⟨1336041, by rfl⟩ : syracuseStep 3562777 = 2672083) B2672083
theorem B4750369 : Blo 1975435 4750369 := bstep (se 2 (by rfl) ⟨1781388, by rfl⟩ : syracuseStep 4750369 = 3562777) B3562777
theorem B25335301 : Blo 1975435 25335301 := bstep (se 4 (by rfl) ⟨2375184, by rfl⟩ : syracuseStep 25335301 = 4750369) B4750369
theorem B33780401 : Blo 1975435 33780401 := bstep (se 2 (by rfl) ⟨12667650, by rfl⟩ : syracuseStep 33780401 = 25335301) B25335301
theorem B22520267 : Blo 1975435 22520267 := bstep (se 1 (by rfl) ⟨16890200, by rfl⟩ : syracuseStep 22520267 = 33780401) B33780401
theorem B15013511 : Blo 1975435 15013511 := bstep (se 1 (by rfl) ⟨11260133, by rfl⟩ : syracuseStep 15013511 = 22520267) B22520267
theorem B10009007 : Blo 1975435 10009007 := bstep (se 1 (by rfl) ⟨7506755, by rfl⟩ : syracuseStep 10009007 = 15013511) B15013511
theorem B6672671 : Blo 1975435 6672671 := bstep (se 1 (by rfl) ⟨5004503, by rfl⟩ : syracuseStep 6672671 = 10009007) B10009007
theorem B4448447 : Blo 1975435 4448447 := bstep (se 1 (by rfl) ⟨3336335, by rfl⟩ : syracuseStep 4448447 = 6672671) B6672671
theorem B2965631 : Blo 1975435 2965631 := bstep (se 1 (by rfl) ⟨2224223, by rfl⟩ : syracuseStep 2965631 = 4448447) B4448447
theorem B1977087 : Blo 1975435 1977087 := bstep (se 1 (by rfl) ⟨1482815, by rfl⟩ : syracuseStep 1977087 = 2965631) B2965631
theorem B2965637 : Blo 1975435 2965637 := bbase (se 4 (by rfl) ⟨278028, by rfl⟩ : syracuseStep 2965637 = 556057) (by norm_num)
theorem B1977091 : Blo 1975435 1977091 := bstep (se 1 (by rfl) ⟨1482818, by rfl⟩ : syracuseStep 1977091 = 2965637) B2965637
theorem B3336349 : Blo 1975435 3336349 := bbase (se 3 (by rfl) ⟨625565, by rfl⟩ : syracuseStep 3336349 = 1251131) (by norm_num)
theorem B4448465 : Blo 1975435 4448465 := bstep (se 2 (by rfl) ⟨1668174, by rfl⟩ : syracuseStep 4448465 = 3336349) B3336349
theorem B2965643 : Blo 1975435 2965643 := bstep (se 1 (by rfl) ⟨2224232, by rfl⟩ : syracuseStep 2965643 = 4448465) B4448465
theorem B1977095 : Blo 1975435 1977095 := bstep (se 1 (by rfl) ⟨1482821, by rfl⟩ : syracuseStep 1977095 = 2965643) B2965643
theorem B2224237 : Blo 1975435 2224237 := bbase (se 3 (by rfl) ⟨417044, by rfl⟩ : syracuseStep 2224237 = 834089) (by norm_num)
theorem B2965649 : Blo 1975435 2965649 := bstep (se 2 (by rfl) ⟨1112118, by rfl⟩ : syracuseStep 2965649 = 2224237) B2224237
theorem B1977099 : Blo 1975435 1977099 := bstep (se 1 (by rfl) ⟨1482824, by rfl⟩ : syracuseStep 1977099 = 2965649) B2965649
theorem B6672725 : Blo 1975435 6672725 := bbase (se 10 (by rfl) ⟨9774, by rfl⟩ : syracuseStep 6672725 = 19549) (by norm_num)
theorem B4448483 : Blo 1975435 4448483 := bstep (se 1 (by rfl) ⟨3336362, by rfl⟩ : syracuseStep 4448483 = 6672725) B6672725
theorem B2965655 : Blo 1975435 2965655 := bstep (se 1 (by rfl) ⟨2224241, by rfl⟩ : syracuseStep 2965655 = 4448483) B4448483
theorem B1977103 : Blo 1975435 1977103 := bstep (se 1 (by rfl) ⟨1482827, by rfl⟩ : syracuseStep 1977103 = 2965655) B2965655
theorem B2965661 : Blo 1975435 2965661 := bbase (se 3 (by rfl) ⟨556061, by rfl⟩ : syracuseStep 2965661 = 1112123) (by norm_num)
theorem B1977107 : Blo 1975435 1977107 := bstep (se 1 (by rfl) ⟨1482830, by rfl⟩ : syracuseStep 1977107 = 2965661) B2965661
theorem B4448501 : Blo 1975435 4448501 := bbase (se 5 (by rfl) ⟨208523, by rfl⟩ : syracuseStep 4448501 = 417047) (by norm_num)
theorem B2965667 : Blo 1975435 2965667 := bstep (se 1 (by rfl) ⟨2224250, by rfl⟩ : syracuseStep 2965667 = 4448501) B4448501
theorem B1977111 : Blo 1975435 1977111 := bstep (se 1 (by rfl) ⟨1482833, by rfl⟩ : syracuseStep 1977111 = 2965667) B2965667
theorem B19001749 : Blo 1975435 19001749 := bbase (se 6 (by rfl) ⟨445353, by rfl⟩ : syracuseStep 19001749 = 890707) (by norm_num)
theorem B25335665 : Blo 1975435 25335665 := bstep (se 2 (by rfl) ⟨9500874, by rfl⟩ : syracuseStep 25335665 = 19001749) B19001749
theorem B16890443 : Blo 1975435 16890443 := bstep (se 1 (by rfl) ⟨12667832, by rfl⟩ : syracuseStep 16890443 = 25335665) B25335665
theorem B11260295 : Blo 1975435 11260295 := bstep (se 1 (by rfl) ⟨8445221, by rfl⟩ : syracuseStep 11260295 = 16890443) B16890443
theorem B7506863 : Blo 1975435 7506863 := bstep (se 1 (by rfl) ⟨5630147, by rfl⟩ : syracuseStep 7506863 = 11260295) B11260295
theorem B5004575 : Blo 1975435 5004575 := bstep (se 1 (by rfl) ⟨3753431, by rfl⟩ : syracuseStep 5004575 = 7506863) B7506863
theorem B3336383 : Blo 1975435 3336383 := bstep (se 1 (by rfl) ⟨2502287, by rfl⟩ : syracuseStep 3336383 = 5004575) B5004575
theorem B2224255 : Blo 1975435 2224255 := bstep (se 1 (by rfl) ⟨1668191, by rfl⟩ : syracuseStep 2224255 = 3336383) B3336383
theorem B2965673 : Blo 1975435 2965673 := bstep (se 2 (by rfl) ⟨1112127, by rfl⟩ : syracuseStep 2965673 = 2224255) B2224255
theorem B1977115 : Blo 1975435 1977115 := bstep (se 1 (by rfl) ⟨1482836, by rfl⟩ : syracuseStep 1977115 = 2965673) B2965673
theorem B17591285 : Blo 1975435 17591285 := bbase (se 5 (by rfl) ⟨824591, by rfl⟩ : syracuseStep 17591285 = 1649183) (by norm_num)
theorem B11727523 : Blo 1975435 11727523 := bstep (se 1 (by rfl) ⟨8795642, by rfl⟩ : syracuseStep 11727523 = 17591285) B17591285
theorem B62546789 : Blo 1975435 62546789 := bstep (se 4 (by rfl) ⟨5863761, by rfl⟩ : syracuseStep 62546789 = 11727523) B11727523
theorem B166791437 : Blo 1975435 166791437 := bstep (se 3 (by rfl) ⟨31273394, by rfl⟩ : syracuseStep 166791437 = 62546789) B62546789
theorem B111194291 : Blo 1975435 111194291 := bstep (se 1 (by rfl) ⟨83395718, by rfl⟩ : syracuseStep 111194291 = 166791437) B166791437
theorem B74129527 : Blo 1975435 74129527 := bstep (se 1 (by rfl) ⟨55597145, by rfl⟩ : syracuseStep 74129527 = 111194291) B111194291
theorem B98839369 : Blo 1975435 98839369 := bstep (se 2 (by rfl) ⟨37064763, by rfl⟩ : syracuseStep 98839369 = 74129527) B74129527
theorem B131785825 : Blo 1975435 131785825 := bstep (se 2 (by rfl) ⟨49419684, by rfl⟩ : syracuseStep 131785825 = 98839369) B98839369
theorem B175714433 : Blo 1975435 175714433 := bstep (se 2 (by rfl) ⟨65892912, by rfl⟩ : syracuseStep 175714433 = 131785825) B131785825
theorem B117142955 : Blo 1975435 117142955 := bstep (se 1 (by rfl) ⟨87857216, by rfl⟩ : syracuseStep 117142955 = 175714433) B175714433
theorem B78095303 : Blo 1975435 78095303 := bstep (se 1 (by rfl) ⟨58571477, by rfl⟩ : syracuseStep 78095303 = 117142955) B117142955
theorem B52063535 : Blo 1975435 52063535 := bstep (se 1 (by rfl) ⟨39047651, by rfl⟩ : syracuseStep 52063535 = 78095303) B78095303
theorem B34709023 : Blo 1975435 34709023 := bstep (se 1 (by rfl) ⟨26031767, by rfl⟩ : syracuseStep 34709023 = 52063535) B52063535
theorem B46278697 : Blo 1975435 46278697 := bstep (se 2 (by rfl) ⟨17354511, by rfl⟩ : syracuseStep 46278697 = 34709023) B34709023
theorem B61704929 : Blo 1975435 61704929 := bstep (se 2 (by rfl) ⟨23139348, by rfl⟩ : syracuseStep 61704929 = 46278697) B46278697
theorem B164546477 : Blo 1975435 164546477 := bstep (se 3 (by rfl) ⟨30852464, by rfl⟩ : syracuseStep 164546477 = 61704929) B61704929
theorem B109697651 : Blo 1975435 109697651 := bstep (se 1 (by rfl) ⟨82273238, by rfl⟩ : syracuseStep 109697651 = 164546477) B164546477
theorem B73131767 : Blo 1975435 73131767 := bstep (se 1 (by rfl) ⟨54848825, by rfl⟩ : syracuseStep 73131767 = 109697651) B109697651
theorem B48754511 : Blo 1975435 48754511 := bstep (se 1 (by rfl) ⟨36565883, by rfl⟩ : syracuseStep 48754511 = 73131767) B73131767
theorem B32503007 : Blo 1975435 32503007 := bstep (se 1 (by rfl) ⟨24377255, by rfl⟩ : syracuseStep 32503007 = 48754511) B48754511
theorem B21668671 : Blo 1975435 21668671 := bstep (se 1 (by rfl) ⟨16251503, by rfl⟩ : syracuseStep 21668671 = 32503007) B32503007
theorem B28891561 : Blo 1975435 28891561 := bstep (se 2 (by rfl) ⟨10834335, by rfl⟩ : syracuseStep 28891561 = 21668671) B21668671
theorem B38522081 : Blo 1975435 38522081 := bstep (se 2 (by rfl) ⟨14445780, by rfl⟩ : syracuseStep 38522081 = 28891561) B28891561
theorem B25681387 : Blo 1975435 25681387 := bstep (se 1 (by rfl) ⟨19261040, by rfl⟩ : syracuseStep 25681387 = 38522081) B38522081
theorem B34241849 : Blo 1975435 34241849 := bstep (se 2 (by rfl) ⟨12840693, by rfl⟩ : syracuseStep 34241849 = 25681387) B25681387
theorem B22827899 : Blo 1975435 22827899 := bstep (se 1 (by rfl) ⟨17120924, by rfl⟩ : syracuseStep 22827899 = 34241849) B34241849
theorem B15218599 : Blo 1975435 15218599 := bstep (se 1 (by rfl) ⟨11413949, by rfl⟩ : syracuseStep 15218599 = 22827899) B22827899
theorem B20291465 : Blo 1975435 20291465 := bstep (se 2 (by rfl) ⟨7609299, by rfl⟩ : syracuseStep 20291465 = 15218599) B15218599
theorem B13527643 : Blo 1975435 13527643 := bstep (se 1 (by rfl) ⟨10145732, by rfl⟩ : syracuseStep 13527643 = 20291465) B20291465
theorem B18036857 : Blo 1975435 18036857 := bstep (se 2 (by rfl) ⟨6763821, by rfl⟩ : syracuseStep 18036857 = 13527643) B13527643
theorem B12024571 : Blo 1975435 12024571 := bstep (se 1 (by rfl) ⟨9018428, by rfl⟩ : syracuseStep 12024571 = 18036857) B18036857
theorem B16032761 : Blo 1975435 16032761 := bstep (se 2 (by rfl) ⟨6012285, by rfl⟩ : syracuseStep 16032761 = 12024571) B12024571
theorem B10688507 : Blo 1975435 10688507 := bstep (se 1 (by rfl) ⟨8016380, by rfl⟩ : syracuseStep 10688507 = 16032761) B16032761
theorem B7125671 : Blo 1975435 7125671 := bstep (se 1 (by rfl) ⟨5344253, by rfl⟩ : syracuseStep 7125671 = 10688507) B10688507
theorem B4750447 : Blo 1975435 4750447 := bstep (se 1 (by rfl) ⟨3562835, by rfl⟩ : syracuseStep 4750447 = 7125671) B7125671
theorem B6333929 : Blo 1975435 6333929 := bstep (se 2 (by rfl) ⟨2375223, by rfl⟩ : syracuseStep 6333929 = 4750447) B4750447
theorem B4222619 : Blo 1975435 4222619 := bstep (se 1 (by rfl) ⟨3166964, by rfl⟩ : syracuseStep 4222619 = 6333929) B6333929
theorem B2815079 : Blo 1975435 2815079 := bstep (se 1 (by rfl) ⟨2111309, by rfl⟩ : syracuseStep 2815079 = 4222619) B4222619
theorem B7506877 : Blo 1975435 7506877 := bstep (se 3 (by rfl) ⟨1407539, by rfl⟩ : syracuseStep 7506877 = 2815079) B2815079
theorem B10009169 : Blo 1975435 10009169 := bstep (se 2 (by rfl) ⟨3753438, by rfl⟩ : syracuseStep 10009169 = 7506877) B7506877
theorem B6672779 : Blo 1975435 6672779 := bstep (se 1 (by rfl) ⟨5004584, by rfl⟩ : syracuseStep 6672779 = 10009169) B10009169
theorem B4448519 : Blo 1975435 4448519 := bstep (se 1 (by rfl) ⟨3336389, by rfl⟩ : syracuseStep 4448519 = 6672779) B6672779
theorem B2965679 : Blo 1975435 2965679 := bstep (se 1 (by rfl) ⟨2224259, by rfl⟩ : syracuseStep 2965679 = 4448519) B4448519
theorem B1977119 : Blo 1975435 1977119 := bstep (se 1 (by rfl) ⟨1482839, by rfl⟩ : syracuseStep 1977119 = 2965679) B2965679
theorem B2965685 : Blo 1975435 2965685 := bbase (se 5 (by rfl) ⟨139016, by rfl⟩ : syracuseStep 2965685 = 278033) (by norm_num)
theorem B1977123 : Blo 1975435 1977123 := bstep (se 1 (by rfl) ⟨1482842, by rfl⟩ : syracuseStep 1977123 = 2965685) B2965685
theorem B5004605 : Blo 1975435 5004605 := bbase (se 3 (by rfl) ⟨938363, by rfl⟩ : syracuseStep 5004605 = 1876727) (by norm_num)
theorem B3336403 : Blo 1975435 3336403 := bstep (se 1 (by rfl) ⟨2502302, by rfl⟩ : syracuseStep 3336403 = 5004605) B5004605
theorem B4448537 : Blo 1975435 4448537 := bstep (se 2 (by rfl) ⟨1668201, by rfl⟩ : syracuseStep 4448537 = 3336403) B3336403
theorem B2965691 : Blo 1975435 2965691 := bstep (se 1 (by rfl) ⟨2224268, by rfl⟩ : syracuseStep 2965691 = 4448537) B4448537
theorem B1977127 : Blo 1975435 1977127 := bstep (se 1 (by rfl) ⟨1482845, by rfl⟩ : syracuseStep 1977127 = 2965691) B2965691
theorem B2224273 : Blo 1975435 2224273 := bbase (se 2 (by rfl) ⟨834102, by rfl⟩ : syracuseStep 2224273 = 1668205) (by norm_num)
theorem B2965697 : Blo 1975435 2965697 := bstep (se 2 (by rfl) ⟨1112136, by rfl⟩ : syracuseStep 2965697 = 2224273) B2224273
theorem B1977131 : Blo 1975435 1977131 := bstep (se 1 (by rfl) ⟨1482848, by rfl⟩ : syracuseStep 1977131 = 2965697) B2965697
theorem B3753469 : Blo 1975435 3753469 := bbase (se 3 (by rfl) ⟨703775, by rfl⟩ : syracuseStep 3753469 = 1407551) (by norm_num)
theorem B5004625 : Blo 1975435 5004625 := bstep (se 2 (by rfl) ⟨1876734, by rfl⟩ : syracuseStep 5004625 = 3753469) B3753469
theorem B6672833 : Blo 1975435 6672833 := bstep (se 2 (by rfl) ⟨2502312, by rfl⟩ : syracuseStep 6672833 = 5004625) B5004625
theorem B4448555 : Blo 1975435 4448555 := bstep (se 1 (by rfl) ⟨3336416, by rfl⟩ : syracuseStep 4448555 = 6672833) B6672833
theorem B2965703 : Blo 1975435 2965703 := bstep (se 1 (by rfl) ⟨2224277, by rfl⟩ : syracuseStep 2965703 = 4448555) B4448555
theorem B1977135 : Blo 1975435 1977135 := bstep (se 1 (by rfl) ⟨1482851, by rfl⟩ : syracuseStep 1977135 = 2965703) B2965703
theorem B2965709 : Blo 1975435 2965709 := bbase (se 3 (by rfl) ⟨556070, by rfl⟩ : syracuseStep 2965709 = 1112141) (by norm_num)
theorem B1977139 : Blo 1975435 1977139 := bstep (se 1 (by rfl) ⟨1482854, by rfl⟩ : syracuseStep 1977139 = 2965709) B2965709
theorem B4448573 : Blo 1975435 4448573 := bbase (se 3 (by rfl) ⟨834107, by rfl⟩ : syracuseStep 4448573 = 1668215) (by norm_num)
theorem B2965715 : Blo 1975435 2965715 := bstep (se 1 (by rfl) ⟨2224286, by rfl⟩ : syracuseStep 2965715 = 4448573) B4448573
theorem B1977143 : Blo 1975435 1977143 := bstep (se 1 (by rfl) ⟨1482857, by rfl⟩ : syracuseStep 1977143 = 2965715) B2965715
theorem B3336437 : Blo 1975435 3336437 := bbase (se 5 (by rfl) ⟨156395, by rfl⟩ : syracuseStep 3336437 = 312791) (by norm_num)
theorem B2224291 : Blo 1975435 2224291 := bstep (se 1 (by rfl) ⟨1668218, by rfl⟩ : syracuseStep 2224291 = 3336437) B3336437
theorem B2965721 : Blo 1975435 2965721 := bstep (se 2 (by rfl) ⟨1112145, by rfl⟩ : syracuseStep 2965721 = 2224291) B2224291
theorem B1977147 : Blo 1975435 1977147 := bstep (se 1 (by rfl) ⟨1482860, by rfl⟩ : syracuseStep 1977147 = 2965721) B2965721
theorem B9630677 : Blo 1975435 9630677 := bbase (se 7 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 9630677 = 225719) (by norm_num)
theorem B25681805 : Blo 1975435 25681805 := bstep (se 3 (by rfl) ⟨4815338, by rfl⟩ : syracuseStep 25681805 = 9630677) B9630677
theorem B17121203 : Blo 1975435 17121203 := bstep (se 1 (by rfl) ⟨12840902, by rfl⟩ : syracuseStep 17121203 = 25681805) B25681805
theorem B11414135 : Blo 1975435 11414135 := bstep (se 1 (by rfl) ⟨8560601, by rfl⟩ : syracuseStep 11414135 = 17121203) B17121203
theorem B7609423 : Blo 1975435 7609423 := bstep (se 1 (by rfl) ⟨5707067, by rfl⟩ : syracuseStep 7609423 = 11414135) B11414135
theorem B10145897 : Blo 1975435 10145897 := bstep (se 2 (by rfl) ⟨3804711, by rfl⟩ : syracuseStep 10145897 = 7609423) B7609423
theorem B6763931 : Blo 1975435 6763931 := bstep (se 1 (by rfl) ⟨5072948, by rfl⟩ : syracuseStep 6763931 = 10145897) B10145897
theorem B4509287 : Blo 1975435 4509287 := bstep (se 1 (by rfl) ⟨3381965, by rfl⟩ : syracuseStep 4509287 = 6763931) B6763931
theorem B3006191 : Blo 1975435 3006191 := bstep (se 1 (by rfl) ⟨2254643, by rfl⟩ : syracuseStep 3006191 = 4509287) B4509287
theorem B8016509 : Blo 1975435 8016509 := bstep (se 3 (by rfl) ⟨1503095, by rfl⟩ : syracuseStep 8016509 = 3006191) B3006191
theorem B21377357 : Blo 1975435 21377357 := bstep (se 3 (by rfl) ⟨4008254, by rfl⟩ : syracuseStep 21377357 = 8016509) B8016509
theorem B14251571 : Blo 1975435 14251571 := bstep (se 1 (by rfl) ⟨10688678, by rfl⟩ : syracuseStep 14251571 = 21377357) B21377357
theorem B9501047 : Blo 1975435 9501047 := bstep (se 1 (by rfl) ⟨7125785, by rfl⟩ : syracuseStep 9501047 = 14251571) B14251571
theorem B6334031 : Blo 1975435 6334031 := bstep (se 1 (by rfl) ⟨4750523, by rfl⟩ : syracuseStep 6334031 = 9501047) B9501047
theorem B4222687 : Blo 1975435 4222687 := bstep (se 1 (by rfl) ⟨3167015, by rfl⟩ : syracuseStep 4222687 = 6334031) B6334031
theorem B5630249 : Blo 1975435 5630249 := bstep (se 2 (by rfl) ⟨2111343, by rfl⟩ : syracuseStep 5630249 = 4222687) B4222687
theorem B15013997 : Blo 1975435 15013997 := bstep (se 3 (by rfl) ⟨2815124, by rfl⟩ : syracuseStep 15013997 = 5630249) B5630249
theorem B10009331 : Blo 1975435 10009331 := bstep (se 1 (by rfl) ⟨7506998, by rfl⟩ : syracuseStep 10009331 = 15013997) B15013997
theorem B6672887 : Blo 1975435 6672887 := bstep (se 1 (by rfl) ⟨5004665, by rfl⟩ : syracuseStep 6672887 = 10009331) B10009331
theorem B4448591 : Blo 1975435 4448591 := bstep (se 1 (by rfl) ⟨3336443, by rfl⟩ : syracuseStep 4448591 = 6672887) B6672887
theorem B2965727 : Blo 1975435 2965727 := bstep (se 1 (by rfl) ⟨2224295, by rfl⟩ : syracuseStep 2965727 = 4448591) B4448591
theorem B1977151 : Blo 1975435 1977151 := bstep (se 1 (by rfl) ⟨1482863, by rfl⟩ : syracuseStep 1977151 = 2965727) B2965727
theorem B2965733 : Blo 1975435 2965733 := bbase (se 4 (by rfl) ⟨278037, by rfl⟩ : syracuseStep 2965733 = 556075) (by norm_num)
theorem B1977155 : Blo 1975435 1977155 := bstep (se 1 (by rfl) ⟨1482866, by rfl⟩ : syracuseStep 1977155 = 2965733) B2965733
theorem B3167029 : Blo 1975435 3167029 := bbase (se 5 (by rfl) ⟨148454, by rfl⟩ : syracuseStep 3167029 = 296909) (by norm_num)
theorem B4222705 : Blo 1975435 4222705 := bstep (se 2 (by rfl) ⟨1583514, by rfl⟩ : syracuseStep 4222705 = 3167029) B3167029
theorem B5630273 : Blo 1975435 5630273 := bstep (se 2 (by rfl) ⟨2111352, by rfl⟩ : syracuseStep 5630273 = 4222705) B4222705
theorem B3753515 : Blo 1975435 3753515 := bstep (se 1 (by rfl) ⟨2815136, by rfl⟩ : syracuseStep 3753515 = 5630273) B5630273
theorem B2502343 : Blo 1975435 2502343 := bstep (se 1 (by rfl) ⟨1876757, by rfl⟩ : syracuseStep 2502343 = 3753515) B3753515
theorem B3336457 : Blo 1975435 3336457 := bstep (se 2 (by rfl) ⟨1251171, by rfl⟩ : syracuseStep 3336457 = 2502343) B2502343
theorem B4448609 : Blo 1975435 4448609 := bstep (se 2 (by rfl) ⟨1668228, by rfl⟩ : syracuseStep 4448609 = 3336457) B3336457
theorem B2965739 : Blo 1975435 2965739 := bstep (se 1 (by rfl) ⟨2224304, by rfl⟩ : syracuseStep 2965739 = 4448609) B4448609
theorem B1977159 : Blo 1975435 1977159 := bstep (se 1 (by rfl) ⟨1482869, by rfl⟩ : syracuseStep 1977159 = 2965739) B2965739
theorem B2224309 : Blo 1975435 2224309 := bbase (se 5 (by rfl) ⟨104264, by rfl⟩ : syracuseStep 2224309 = 208529) (by norm_num)
theorem B2965745 : Blo 1975435 2965745 := bstep (se 2 (by rfl) ⟨1112154, by rfl⟩ : syracuseStep 2965745 = 2224309) B2224309
theorem B1977163 : Blo 1975435 1977163 := bstep (se 1 (by rfl) ⟨1482872, by rfl⟩ : syracuseStep 1977163 = 2965745) B2965745
theorem B2502353 : Blo 1975435 2502353 := bbase (se 2 (by rfl) ⟨938382, by rfl⟩ : syracuseStep 2502353 = 1876765) (by norm_num)
theorem B6672941 : Blo 1975435 6672941 := bstep (se 3 (by rfl) ⟨1251176, by rfl⟩ : syracuseStep 6672941 = 2502353) B2502353
theorem B4448627 : Blo 1975435 4448627 := bstep (se 1 (by rfl) ⟨3336470, by rfl⟩ : syracuseStep 4448627 = 6672941) B6672941
theorem B2965751 : Blo 1975435 2965751 := bstep (se 1 (by rfl) ⟨2224313, by rfl⟩ : syracuseStep 2965751 = 4448627) B4448627
theorem B1977167 : Blo 1975435 1977167 := bstep (se 1 (by rfl) ⟨1482875, by rfl⟩ : syracuseStep 1977167 = 2965751) B2965751
theorem B2965757 : Blo 1975435 2965757 := bbase (se 3 (by rfl) ⟨556079, by rfl⟩ : syracuseStep 2965757 = 1112159) (by norm_num)
theorem B1977171 : Blo 1975435 1977171 := bstep (se 1 (by rfl) ⟨1482878, by rfl⟩ : syracuseStep 1977171 = 2965757) B2965757
theorem B4448645 : Blo 1975435 4448645 := bbase (se 4 (by rfl) ⟨417060, by rfl⟩ : syracuseStep 4448645 = 834121) (by norm_num)
theorem B2965763 : Blo 1975435 2965763 := bstep (se 1 (by rfl) ⟨2224322, by rfl⟩ : syracuseStep 2965763 = 4448645) B4448645
theorem B1977175 : Blo 1975435 1977175 := bstep (se 1 (by rfl) ⟨1482881, by rfl⟩ : syracuseStep 1977175 = 2965763) B2965763
theorem B2815165 : Blo 1975435 2815165 := bbase (se 3 (by rfl) ⟨527843, by rfl⟩ : syracuseStep 2815165 = 1055687) (by norm_num)
theorem B3753553 : Blo 1975435 3753553 := bstep (se 2 (by rfl) ⟨1407582, by rfl⟩ : syracuseStep 3753553 = 2815165) B2815165
theorem B5004737 : Blo 1975435 5004737 := bstep (se 2 (by rfl) ⟨1876776, by rfl⟩ : syracuseStep 5004737 = 3753553) B3753553
theorem B3336491 : Blo 1975435 3336491 := bstep (se 1 (by rfl) ⟨2502368, by rfl⟩ : syracuseStep 3336491 = 5004737) B5004737
theorem B2224327 : Blo 1975435 2224327 := bstep (se 1 (by rfl) ⟨1668245, by rfl⟩ : syracuseStep 2224327 = 3336491) B3336491
theorem B2965769 : Blo 1975435 2965769 := bstep (se 2 (by rfl) ⟨1112163, by rfl⟩ : syracuseStep 2965769 = 2224327) B2224327
theorem B1977179 : Blo 1975435 1977179 := bstep (se 1 (by rfl) ⟨1482884, by rfl⟩ : syracuseStep 1977179 = 2965769) B2965769
theorem B10009493 : Blo 1975435 10009493 := bbase (se 6 (by rfl) ⟨234597, by rfl⟩ : syracuseStep 10009493 = 469195) (by norm_num)
theorem B6672995 : Blo 1975435 6672995 := bstep (se 1 (by rfl) ⟨5004746, by rfl⟩ : syracuseStep 6672995 = 10009493) B10009493
theorem B4448663 : Blo 1975435 4448663 := bstep (se 1 (by rfl) ⟨3336497, by rfl⟩ : syracuseStep 4448663 = 6672995) B6672995
theorem B2965775 : Blo 1975435 2965775 := bstep (se 1 (by rfl) ⟨2224331, by rfl⟩ : syracuseStep 2965775 = 4448663) B4448663
theorem B1977183 : Blo 1975435 1977183 := bstep (se 1 (by rfl) ⟨1482887, by rfl⟩ : syracuseStep 1977183 = 2965775) B2965775
theorem B2965781 : Blo 1975435 2965781 := bbase (se 6 (by rfl) ⟨69510, by rfl⟩ : syracuseStep 2965781 = 139021) (by norm_num)
theorem B1977187 : Blo 1975435 1977187 := bstep (se 1 (by rfl) ⟨1482890, by rfl⟩ : syracuseStep 1977187 = 2965781) B2965781
theorem B7713397 : Blo 1975435 7713397 := bbase (se 5 (by rfl) ⟨361565, by rfl⟩ : syracuseStep 7713397 = 723131) (by norm_num)
theorem B10284529 : Blo 1975435 10284529 := bstep (se 2 (by rfl) ⟨3856698, by rfl⟩ : syracuseStep 10284529 = 7713397) B7713397
theorem B13712705 : Blo 1975435 13712705 := bstep (se 2 (by rfl) ⟨5142264, by rfl⟩ : syracuseStep 13712705 = 10284529) B10284529
theorem B9141803 : Blo 1975435 9141803 := bstep (se 1 (by rfl) ⟨6856352, by rfl⟩ : syracuseStep 9141803 = 13712705) B13712705
theorem B6094535 : Blo 1975435 6094535 := bstep (se 1 (by rfl) ⟨4570901, by rfl⟩ : syracuseStep 6094535 = 9141803) B9141803
theorem B16252093 : Blo 1975435 16252093 := bstep (se 3 (by rfl) ⟨3047267, by rfl⟩ : syracuseStep 16252093 = 6094535) B6094535
theorem B21669457 : Blo 1975435 21669457 := bstep (se 2 (by rfl) ⟨8126046, by rfl⟩ : syracuseStep 21669457 = 16252093) B16252093
theorem B28892609 : Blo 1975435 28892609 := bstep (se 2 (by rfl) ⟨10834728, by rfl⟩ : syracuseStep 28892609 = 21669457) B21669457
theorem B19261739 : Blo 1975435 19261739 := bstep (se 1 (by rfl) ⟨14446304, by rfl⟩ : syracuseStep 19261739 = 28892609) B28892609
theorem B12841159 : Blo 1975435 12841159 := bstep (se 1 (by rfl) ⟨9630869, by rfl⟩ : syracuseStep 12841159 = 19261739) B19261739
theorem B17121545 : Blo 1975435 17121545 := bstep (se 2 (by rfl) ⟨6420579, by rfl⟩ : syracuseStep 17121545 = 12841159) B12841159
theorem B11414363 : Blo 1975435 11414363 := bstep (se 1 (by rfl) ⟨8560772, by rfl⟩ : syracuseStep 11414363 = 17121545) B17121545
theorem B30438301 : Blo 1975435 30438301 := bstep (se 3 (by rfl) ⟨5707181, by rfl⟩ : syracuseStep 30438301 = 11414363) B11414363
theorem B40584401 : Blo 1975435 40584401 := bstep (se 2 (by rfl) ⟨15219150, by rfl⟩ : syracuseStep 40584401 = 30438301) B30438301
theorem B27056267 : Blo 1975435 27056267 := bstep (se 1 (by rfl) ⟨20292200, by rfl⟩ : syracuseStep 27056267 = 40584401) B40584401
theorem B18037511 : Blo 1975435 18037511 := bstep (se 1 (by rfl) ⟨13528133, by rfl⟩ : syracuseStep 18037511 = 27056267) B27056267
theorem B12025007 : Blo 1975435 12025007 := bstep (se 1 (by rfl) ⟨9018755, by rfl⟩ : syracuseStep 12025007 = 18037511) B18037511
theorem B8016671 : Blo 1975435 8016671 := bstep (se 1 (by rfl) ⟨6012503, by rfl⟩ : syracuseStep 8016671 = 12025007) B12025007
theorem B21377789 : Blo 1975435 21377789 := bstep (se 3 (by rfl) ⟨4008335, by rfl⟩ : syracuseStep 21377789 = 8016671) B8016671
theorem B14251859 : Blo 1975435 14251859 := bstep (se 1 (by rfl) ⟨10688894, by rfl⟩ : syracuseStep 14251859 = 21377789) B21377789
theorem B9501239 : Blo 1975435 9501239 := bstep (se 1 (by rfl) ⟨7125929, by rfl⟩ : syracuseStep 9501239 = 14251859) B14251859
theorem B25336637 : Blo 1975435 25336637 := bstep (se 3 (by rfl) ⟨4750619, by rfl⟩ : syracuseStep 25336637 = 9501239) B9501239
theorem B16891091 : Blo 1975435 16891091 := bstep (se 1 (by rfl) ⟨12668318, by rfl⟩ : syracuseStep 16891091 = 25336637) B25336637
theorem B11260727 : Blo 1975435 11260727 := bstep (se 1 (by rfl) ⟨8445545, by rfl⟩ : syracuseStep 11260727 = 16891091) B16891091
theorem B7507151 : Blo 1975435 7507151 := bstep (se 1 (by rfl) ⟨5630363, by rfl⟩ : syracuseStep 7507151 = 11260727) B11260727
theorem B5004767 : Blo 1975435 5004767 := bstep (se 1 (by rfl) ⟨3753575, by rfl⟩ : syracuseStep 5004767 = 7507151) B7507151
theorem B3336511 : Blo 1975435 3336511 := bstep (se 1 (by rfl) ⟨2502383, by rfl⟩ : syracuseStep 3336511 = 5004767) B5004767
theorem B4448681 : Blo 1975435 4448681 := bstep (se 2 (by rfl) ⟨1668255, by rfl⟩ : syracuseStep 4448681 = 3336511) B3336511
theorem B2965787 : Blo 1975435 2965787 := bstep (se 1 (by rfl) ⟨2224340, by rfl⟩ : syracuseStep 2965787 = 4448681) B4448681
theorem B1977191 : Blo 1975435 1977191 := bstep (se 1 (by rfl) ⟨1482893, by rfl⟩ : syracuseStep 1977191 = 2965787) B2965787
theorem B2224345 : Blo 1975435 2224345 := bbase (se 2 (by rfl) ⟨834129, by rfl⟩ : syracuseStep 2224345 = 1668259) (by norm_num)
theorem B2965793 : Blo 1975435 2965793 := bstep (se 2 (by rfl) ⟨1112172, by rfl⟩ : syracuseStep 2965793 = 2224345) B2224345
theorem B1977195 : Blo 1975435 1977195 := bstep (se 1 (by rfl) ⟨1482896, by rfl⟩ : syracuseStep 1977195 = 2965793) B2965793
theorem B3167093 : Blo 1975435 3167093 := bbase (se 5 (by rfl) ⟨148457, by rfl⟩ : syracuseStep 3167093 = 296915) (by norm_num)
theorem B2111395 : Blo 1975435 2111395 := bstep (se 1 (by rfl) ⟨1583546, by rfl⟩ : syracuseStep 2111395 = 3167093) B3167093
theorem B2815193 : Blo 1975435 2815193 := bstep (se 2 (by rfl) ⟨1055697, by rfl⟩ : syracuseStep 2815193 = 2111395) B2111395
theorem B7507181 : Blo 1975435 7507181 := bstep (se 3 (by rfl) ⟨1407596, by rfl⟩ : syracuseStep 7507181 = 2815193) B2815193
theorem B5004787 : Blo 1975435 5004787 := bstep (se 1 (by rfl) ⟨3753590, by rfl⟩ : syracuseStep 5004787 = 7507181) B7507181
theorem B6673049 : Blo 1975435 6673049 := bstep (se 2 (by rfl) ⟨2502393, by rfl⟩ : syracuseStep 6673049 = 5004787) B5004787
theorem B4448699 : Blo 1975435 4448699 := bstep (se 1 (by rfl) ⟨3336524, by rfl⟩ : syracuseStep 4448699 = 6673049) B6673049
theorem B2965799 : Blo 1975435 2965799 := bstep (se 1 (by rfl) ⟨2224349, by rfl⟩ : syracuseStep 2965799 = 4448699) B4448699
theorem B1977199 : Blo 1975435 1977199 := bstep (se 1 (by rfl) ⟨1482899, by rfl⟩ : syracuseStep 1977199 = 2965799) B2965799
theorem B2965805 : Blo 1975435 2965805 := bbase (se 3 (by rfl) ⟨556088, by rfl⟩ : syracuseStep 2965805 = 1112177) (by norm_num)
theorem B1977203 : Blo 1975435 1977203 := bstep (se 1 (by rfl) ⟨1482902, by rfl⟩ : syracuseStep 1977203 = 2965805) B2965805
theorem B4448717 : Blo 1975435 4448717 := bbase (se 3 (by rfl) ⟨834134, by rfl⟩ : syracuseStep 4448717 = 1668269) (by norm_num)
theorem B2965811 : Blo 1975435 2965811 := bstep (se 1 (by rfl) ⟨2224358, by rfl⟩ : syracuseStep 2965811 = 4448717) B4448717
theorem B1977207 : Blo 1975435 1977207 := bstep (se 1 (by rfl) ⟨1482905, by rfl⟩ : syracuseStep 1977207 = 2965811) B2965811
theorem B2502409 : Blo 1975435 2502409 := bbase (se 2 (by rfl) ⟨938403, by rfl⟩ : syracuseStep 2502409 = 1876807) (by norm_num)
theorem B3336545 : Blo 1975435 3336545 := bstep (se 2 (by rfl) ⟨1251204, by rfl⟩ : syracuseStep 3336545 = 2502409) B2502409
theorem B2224363 : Blo 1975435 2224363 := bstep (se 1 (by rfl) ⟨1668272, by rfl⟩ : syracuseStep 2224363 = 3336545) B3336545
theorem B2965817 : Blo 1975435 2965817 := bstep (se 2 (by rfl) ⟨1112181, by rfl⟩ : syracuseStep 2965817 = 2224363) B2224363
theorem B1977211 : Blo 1975435 1977211 := bstep (se 1 (by rfl) ⟨1482908, by rfl⟩ : syracuseStep 1977211 = 2965817) B2965817
theorem B17832149 : Blo 1975435 17832149 := bbase (se 7 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 17832149 = 417941) (by norm_num)
theorem B11888099 : Blo 1975435 11888099 := bstep (se 1 (by rfl) ⟨8916074, by rfl⟩ : syracuseStep 11888099 = 17832149) B17832149
theorem B7925399 : Blo 1975435 7925399 := bstep (se 1 (by rfl) ⟨5944049, by rfl⟩ : syracuseStep 7925399 = 11888099) B11888099
theorem B84537589 : Blo 1975435 84537589 := bstep (se 5 (by rfl) ⟨3962699, by rfl⟩ : syracuseStep 84537589 = 7925399) B7925399
theorem B112716785 : Blo 1975435 112716785 := bstep (se 2 (by rfl) ⟨42268794, by rfl⟩ : syracuseStep 112716785 = 84537589) B84537589
theorem B75144523 : Blo 1975435 75144523 := bstep (se 1 (by rfl) ⟨56358392, by rfl⟩ : syracuseStep 75144523 = 112716785) B112716785
theorem B100192697 : Blo 1975435 100192697 := bstep (se 2 (by rfl) ⟨37572261, by rfl⟩ : syracuseStep 100192697 = 75144523) B75144523
theorem B66795131 : Blo 1975435 66795131 := bstep (se 1 (by rfl) ⟨50096348, by rfl⟩ : syracuseStep 66795131 = 100192697) B100192697
theorem B178120349 : Blo 1975435 178120349 := bstep (se 3 (by rfl) ⟨33397565, by rfl⟩ : syracuseStep 178120349 = 66795131) B66795131
theorem B118746899 : Blo 1975435 118746899 := bstep (se 1 (by rfl) ⟨89060174, by rfl⟩ : syracuseStep 118746899 = 178120349) B178120349
theorem B79164599 : Blo 1975435 79164599 := bstep (se 1 (by rfl) ⟨59373449, by rfl⟩ : syracuseStep 79164599 = 118746899) B118746899
theorem B211105597 : Blo 1975435 211105597 := bstep (se 3 (by rfl) ⟨39582299, by rfl⟩ : syracuseStep 211105597 = 79164599) B79164599
theorem B281474129 : Blo 1975435 281474129 := bstep (se 2 (by rfl) ⟨105552798, by rfl⟩ : syracuseStep 281474129 = 211105597) B211105597
theorem B187649419 : Blo 1975435 187649419 := bstep (se 1 (by rfl) ⟨140737064, by rfl⟩ : syracuseStep 187649419 = 281474129) B281474129
theorem B250199225 : Blo 1975435 250199225 := bstep (se 2 (by rfl) ⟨93824709, by rfl⟩ : syracuseStep 250199225 = 187649419) B187649419
theorem B166799483 : Blo 1975435 166799483 := bstep (se 1 (by rfl) ⟨125099612, by rfl⟩ : syracuseStep 166799483 = 250199225) B250199225
theorem B111199655 : Blo 1975435 111199655 := bstep (se 1 (by rfl) ⟨83399741, by rfl⟩ : syracuseStep 111199655 = 166799483) B166799483
theorem B296532413 : Blo 1975435 296532413 := bstep (se 3 (by rfl) ⟨55599827, by rfl⟩ : syracuseStep 296532413 = 111199655) B111199655
theorem B197688275 : Blo 1975435 197688275 := bstep (se 1 (by rfl) ⟨148266206, by rfl⟩ : syracuseStep 197688275 = 296532413) B296532413
theorem B131792183 : Blo 1975435 131792183 := bstep (se 1 (by rfl) ⟨98844137, by rfl⟩ : syracuseStep 131792183 = 197688275) B197688275
theorem B87861455 : Blo 1975435 87861455 := bstep (se 1 (by rfl) ⟨65896091, by rfl⟩ : syracuseStep 87861455 = 131792183) B131792183
theorem B58574303 : Blo 1975435 58574303 := bstep (se 1 (by rfl) ⟨43930727, by rfl⟩ : syracuseStep 58574303 = 87861455) B87861455
theorem B39049535 : Blo 1975435 39049535 := bstep (se 1 (by rfl) ⟨29287151, by rfl⟩ : syracuseStep 39049535 = 58574303) B58574303
theorem B26033023 : Blo 1975435 26033023 := bstep (se 1 (by rfl) ⟨19524767, by rfl⟩ : syracuseStep 26033023 = 39049535) B39049535
theorem B34710697 : Blo 1975435 34710697 := bstep (se 2 (by rfl) ⟨13016511, by rfl⟩ : syracuseStep 34710697 = 26033023) B26033023
theorem B46280929 : Blo 1975435 46280929 := bstep (se 2 (by rfl) ⟨17355348, by rfl⟩ : syracuseStep 46280929 = 34710697) B34710697
theorem B61707905 : Blo 1975435 61707905 := bstep (se 2 (by rfl) ⟨23140464, by rfl⟩ : syracuseStep 61707905 = 46280929) B46280929
theorem B41138603 : Blo 1975435 41138603 := bstep (se 1 (by rfl) ⟨30853952, by rfl⟩ : syracuseStep 41138603 = 61707905) B61707905
theorem B27425735 : Blo 1975435 27425735 := bstep (se 1 (by rfl) ⟨20569301, by rfl⟩ : syracuseStep 27425735 = 41138603) B41138603
theorem B18283823 : Blo 1975435 18283823 := bstep (se 1 (by rfl) ⟨13712867, by rfl⟩ : syracuseStep 18283823 = 27425735) B27425735
theorem B12189215 : Blo 1975435 12189215 := bstep (se 1 (by rfl) ⟨9141911, by rfl⟩ : syracuseStep 12189215 = 18283823) B18283823
theorem B8126143 : Blo 1975435 8126143 := bstep (se 1 (by rfl) ⟨6094607, by rfl⟩ : syracuseStep 8126143 = 12189215) B12189215
theorem B43339429 : Blo 1975435 43339429 := bstep (se 4 (by rfl) ⟨4063071, by rfl⟩ : syracuseStep 43339429 = 8126143) B8126143
theorem B57785905 : Blo 1975435 57785905 := bstep (se 2 (by rfl) ⟨21669714, by rfl⟩ : syracuseStep 57785905 = 43339429) B43339429
theorem B308191493 : Blo 1975435 308191493 := bstep (se 4 (by rfl) ⟨28892952, by rfl⟩ : syracuseStep 308191493 = 57785905) B57785905
theorem B205460995 : Blo 1975435 205460995 := bstep (se 1 (by rfl) ⟨154095746, by rfl⟩ : syracuseStep 205460995 = 308191493) B308191493
theorem B273947993 : Blo 1975435 273947993 := bstep (se 2 (by rfl) ⟨102730497, by rfl⟩ : syracuseStep 273947993 = 205460995) B205460995
theorem B182631995 : Blo 1975435 182631995 := bstep (se 1 (by rfl) ⟨136973996, by rfl⟩ : syracuseStep 182631995 = 273947993) B273947993
theorem B121754663 : Blo 1975435 121754663 := bstep (se 1 (by rfl) ⟨91315997, by rfl⟩ : syracuseStep 121754663 = 182631995) B182631995
theorem B81169775 : Blo 1975435 81169775 := bstep (se 1 (by rfl) ⟨60877331, by rfl⟩ : syracuseStep 81169775 = 121754663) B121754663
theorem B54113183 : Blo 1975435 54113183 := bstep (se 1 (by rfl) ⟨40584887, by rfl⟩ : syracuseStep 54113183 = 81169775) B81169775
theorem B36075455 : Blo 1975435 36075455 := bstep (se 1 (by rfl) ⟨27056591, by rfl⟩ : syracuseStep 36075455 = 54113183) B54113183
theorem B24050303 : Blo 1975435 24050303 := bstep (se 1 (by rfl) ⟨18037727, by rfl⟩ : syracuseStep 24050303 = 36075455) B36075455
theorem B16033535 : Blo 1975435 16033535 := bstep (se 1 (by rfl) ⟨12025151, by rfl⟩ : syracuseStep 16033535 = 24050303) B24050303
theorem B10689023 : Blo 1975435 10689023 := bstep (se 1 (by rfl) ⟨8016767, by rfl⟩ : syracuseStep 10689023 = 16033535) B16033535
theorem B28504061 : Blo 1975435 28504061 := bstep (se 3 (by rfl) ⟨5344511, by rfl⟩ : syracuseStep 28504061 = 10689023) B10689023
theorem B19002707 : Blo 1975435 19002707 := bstep (se 1 (by rfl) ⟨14252030, by rfl⟩ : syracuseStep 19002707 = 28504061) B28504061
theorem B12668471 : Blo 1975435 12668471 := bstep (se 1 (by rfl) ⟨9501353, by rfl⟩ : syracuseStep 12668471 = 19002707) B19002707
theorem B8445647 : Blo 1975435 8445647 := bstep (se 1 (by rfl) ⟨6334235, by rfl⟩ : syracuseStep 8445647 = 12668471) B12668471
theorem B22521725 : Blo 1975435 22521725 := bstep (se 3 (by rfl) ⟨4222823, by rfl⟩ : syracuseStep 22521725 = 8445647) B8445647
theorem B15014483 : Blo 1975435 15014483 := bstep (se 1 (by rfl) ⟨11260862, by rfl⟩ : syracuseStep 15014483 = 22521725) B22521725
theorem B10009655 : Blo 1975435 10009655 := bstep (se 1 (by rfl) ⟨7507241, by rfl⟩ : syracuseStep 10009655 = 15014483) B15014483
theorem B6673103 : Blo 1975435 6673103 := bstep (se 1 (by rfl) ⟨5004827, by rfl⟩ : syracuseStep 6673103 = 10009655) B10009655
theorem B4448735 : Blo 1975435 4448735 := bstep (se 1 (by rfl) ⟨3336551, by rfl⟩ : syracuseStep 4448735 = 6673103) B6673103
theorem B2965823 : Blo 1975435 2965823 := bstep (se 1 (by rfl) ⟨2224367, by rfl⟩ : syracuseStep 2965823 = 4448735) B4448735
theorem B1977215 : Blo 1975435 1977215 := bstep (se 1 (by rfl) ⟨1482911, by rfl⟩ : syracuseStep 1977215 = 2965823) B2965823
theorem B2965829 : Blo 1975435 2965829 := bbase (se 4 (by rfl) ⟨278046, by rfl⟩ : syracuseStep 2965829 = 556093) (by norm_num)
theorem B1977219 : Blo 1975435 1977219 := bstep (se 1 (by rfl) ⟨1482914, by rfl⟩ : syracuseStep 1977219 = 2965829) B2965829
theorem B3336565 : Blo 1975435 3336565 := bbase (se 5 (by rfl) ⟨156401, by rfl⟩ : syracuseStep 3336565 = 312803) (by norm_num)
theorem B4448753 : Blo 1975435 4448753 := bstep (se 2 (by rfl) ⟨1668282, by rfl⟩ : syracuseStep 4448753 = 3336565) B3336565
theorem B2965835 : Blo 1975435 2965835 := bstep (se 1 (by rfl) ⟨2224376, by rfl⟩ : syracuseStep 2965835 = 4448753) B4448753
theorem B1977223 : Blo 1975435 1977223 := bstep (se 1 (by rfl) ⟨1482917, by rfl⟩ : syracuseStep 1977223 = 2965835) B2965835
theorem B2224381 : Blo 1975435 2224381 := bbase (se 3 (by rfl) ⟨417071, by rfl⟩ : syracuseStep 2224381 = 834143) (by norm_num)
theorem B2965841 : Blo 1975435 2965841 := bstep (se 2 (by rfl) ⟨1112190, by rfl⟩ : syracuseStep 2965841 = 2224381) B2224381
theorem B1977227 : Blo 1975435 1977227 := bstep (se 1 (by rfl) ⟨1482920, by rfl⟩ : syracuseStep 1977227 = 2965841) B2965841
theorem B6673157 : Blo 1975435 6673157 := bbase (se 4 (by rfl) ⟨625608, by rfl⟩ : syracuseStep 6673157 = 1251217) (by norm_num)
theorem B4448771 : Blo 1975435 4448771 := bstep (se 1 (by rfl) ⟨3336578, by rfl⟩ : syracuseStep 4448771 = 6673157) B6673157
theorem B2965847 : Blo 1975435 2965847 := bstep (se 1 (by rfl) ⟨2224385, by rfl⟩ : syracuseStep 2965847 = 4448771) B4448771
theorem B1977231 : Blo 1975435 1977231 := bstep (se 1 (by rfl) ⟨1482923, by rfl⟩ : syracuseStep 1977231 = 2965847) B2965847
theorem B2965853 : Blo 1975435 2965853 := bbase (se 3 (by rfl) ⟨556097, by rfl⟩ : syracuseStep 2965853 = 1112195) (by norm_num)
theorem B1977235 : Blo 1975435 1977235 := bstep (se 1 (by rfl) ⟨1482926, by rfl⟩ : syracuseStep 1977235 = 2965853) B2965853
theorem B4448789 : Blo 1975435 4448789 := bbase (se 6 (by rfl) ⟨104268, by rfl⟩ : syracuseStep 4448789 = 208537) (by norm_num)
theorem B2965859 : Blo 1975435 2965859 := bstep (se 1 (by rfl) ⟨2224394, by rfl⟩ : syracuseStep 2965859 = 4448789) B4448789
theorem B1977239 : Blo 1975435 1977239 := bstep (se 1 (by rfl) ⟨1482929, by rfl⟩ : syracuseStep 1977239 = 2965859) B2965859
theorem B7507349 : Blo 1975435 7507349 := bbase (se 6 (by rfl) ⟨175953, by rfl⟩ : syracuseStep 7507349 = 351907) (by norm_num)
theorem B5004899 : Blo 1975435 5004899 := bstep (se 1 (by rfl) ⟨3753674, by rfl⟩ : syracuseStep 5004899 = 7507349) B7507349
theorem B3336599 : Blo 1975435 3336599 := bstep (se 1 (by rfl) ⟨2502449, by rfl⟩ : syracuseStep 3336599 = 5004899) B5004899
theorem B2224399 : Blo 1975435 2224399 := bstep (se 1 (by rfl) ⟨1668299, by rfl⟩ : syracuseStep 2224399 = 3336599) B3336599
theorem B2965865 : Blo 1975435 2965865 := bstep (se 2 (by rfl) ⟨1112199, by rfl⟩ : syracuseStep 2965865 = 2224399) B2224399
theorem B1977243 : Blo 1975435 1977243 := bstep (se 1 (by rfl) ⟨1482932, by rfl⟩ : syracuseStep 1977243 = 2965865) B2965865
theorem B11261045 : Blo 1975435 11261045 := bbase (se 5 (by rfl) ⟨527861, by rfl⟩ : syracuseStep 11261045 = 1055723) (by norm_num)
theorem B7507363 : Blo 1975435 7507363 := bstep (se 1 (by rfl) ⟨5630522, by rfl⟩ : syracuseStep 7507363 = 11261045) B11261045
theorem B10009817 : Blo 1975435 10009817 := bstep (se 2 (by rfl) ⟨3753681, by rfl⟩ : syracuseStep 10009817 = 7507363) B7507363
theorem B6673211 : Blo 1975435 6673211 := bstep (se 1 (by rfl) ⟨5004908, by rfl⟩ : syracuseStep 6673211 = 10009817) B10009817
theorem B4448807 : Blo 1975435 4448807 := bstep (se 1 (by rfl) ⟨3336605, by rfl⟩ : syracuseStep 4448807 = 6673211) B6673211
theorem B2965871 : Blo 1975435 2965871 := bstep (se 1 (by rfl) ⟨2224403, by rfl⟩ : syracuseStep 2965871 = 4448807) B4448807
theorem B1977247 : Blo 1975435 1977247 := bstep (se 1 (by rfl) ⟨1482935, by rfl⟩ : syracuseStep 1977247 = 2965871) B2965871
theorem B2965877 : Blo 1975435 2965877 := bbase (se 5 (by rfl) ⟨139025, by rfl⟩ : syracuseStep 2965877 = 278051) (by norm_num)
theorem B1977251 : Blo 1975435 1977251 := bstep (se 1 (by rfl) ⟨1482938, by rfl⟩ : syracuseStep 1977251 = 2965877) B2965877
theorem B2536609 : Blo 1975435 2536609 := bbase (se 2 (by rfl) ⟨951228, by rfl⟩ : syracuseStep 2536609 = 1902457) (by norm_num)
theorem B3382145 : Blo 1975435 3382145 := bstep (se 2 (by rfl) ⟨1268304, by rfl⟩ : syracuseStep 3382145 = 2536609) B2536609
theorem B2254763 : Blo 1975435 2254763 := bstep (se 1 (by rfl) ⟨1691072, by rfl⟩ : syracuseStep 2254763 = 3382145) B3382145
theorem B6012701 : Blo 1975435 6012701 := bstep (se 3 (by rfl) ⟨1127381, by rfl⟩ : syracuseStep 6012701 = 2254763) B2254763
theorem B4008467 : Blo 1975435 4008467 := bstep (se 1 (by rfl) ⟨3006350, by rfl⟩ : syracuseStep 4008467 = 6012701) B6012701
theorem B10689245 : Blo 1975435 10689245 := bstep (se 3 (by rfl) ⟨2004233, by rfl⟩ : syracuseStep 10689245 = 4008467) B4008467
theorem B7126163 : Blo 1975435 7126163 := bstep (se 1 (by rfl) ⟨5344622, by rfl⟩ : syracuseStep 7126163 = 10689245) B10689245
theorem B4750775 : Blo 1975435 4750775 := bstep (se 1 (by rfl) ⟨3563081, by rfl⟩ : syracuseStep 4750775 = 7126163) B7126163
theorem B3167183 : Blo 1975435 3167183 := bstep (se 1 (by rfl) ⟨2375387, by rfl⟩ : syracuseStep 3167183 = 4750775) B4750775
theorem B2111455 : Blo 1975435 2111455 := bstep (se 1 (by rfl) ⟨1583591, by rfl⟩ : syracuseStep 2111455 = 3167183) B3167183
theorem B2815273 : Blo 1975435 2815273 := bstep (se 2 (by rfl) ⟨1055727, by rfl⟩ : syracuseStep 2815273 = 2111455) B2111455
theorem B3753697 : Blo 1975435 3753697 := bstep (se 2 (by rfl) ⟨1407636, by rfl⟩ : syracuseStep 3753697 = 2815273) B2815273
theorem B5004929 : Blo 1975435 5004929 := bstep (se 2 (by rfl) ⟨1876848, by rfl⟩ : syracuseStep 5004929 = 3753697) B3753697
theorem B3336619 : Blo 1975435 3336619 := bstep (se 1 (by rfl) ⟨2502464, by rfl⟩ : syracuseStep 3336619 = 5004929) B5004929
theorem B4448825 : Blo 1975435 4448825 := bstep (se 2 (by rfl) ⟨1668309, by rfl⟩ : syracuseStep 4448825 = 3336619) B3336619
theorem B2965883 : Blo 1975435 2965883 := bstep (se 1 (by rfl) ⟨2224412, by rfl⟩ : syracuseStep 2965883 = 4448825) B4448825
theorem B1977255 : Blo 1975435 1977255 := bstep (se 1 (by rfl) ⟨1482941, by rfl⟩ : syracuseStep 1977255 = 2965883) B2965883
theorem B2224417 : Blo 1975435 2224417 := bbase (se 2 (by rfl) ⟨834156, by rfl⟩ : syracuseStep 2224417 = 1668313) (by norm_num)
theorem B2965889 : Blo 1975435 2965889 := bstep (se 2 (by rfl) ⟨1112208, by rfl⟩ : syracuseStep 2965889 = 2224417) B2224417
theorem B1977259 : Blo 1975435 1977259 := bstep (se 1 (by rfl) ⟨1482944, by rfl⟩ : syracuseStep 1977259 = 2965889) B2965889
theorem B5004949 : Blo 1975435 5004949 := bbase (se 6 (by rfl) ⟨117303, by rfl⟩ : syracuseStep 5004949 = 234607) (by norm_num)
theorem B6673265 : Blo 1975435 6673265 := bstep (se 2 (by rfl) ⟨2502474, by rfl⟩ : syracuseStep 6673265 = 5004949) B5004949
theorem B4448843 : Blo 1975435 4448843 := bstep (se 1 (by rfl) ⟨3336632, by rfl⟩ : syracuseStep 4448843 = 6673265) B6673265
theorem B2965895 : Blo 1975435 2965895 := bstep (se 1 (by rfl) ⟨2224421, by rfl⟩ : syracuseStep 2965895 = 4448843) B4448843
theorem B1977263 : Blo 1975435 1977263 := bstep (se 1 (by rfl) ⟨1482947, by rfl⟩ : syracuseStep 1977263 = 2965895) B2965895
theorem B2965901 : Blo 1975435 2965901 := bbase (se 3 (by rfl) ⟨556106, by rfl⟩ : syracuseStep 2965901 = 1112213) (by norm_num)
theorem B1977267 : Blo 1975435 1977267 := bstep (se 1 (by rfl) ⟨1482950, by rfl⟩ : syracuseStep 1977267 = 2965901) B2965901
theorem B4448861 : Blo 1975435 4448861 := bbase (se 3 (by rfl) ⟨834161, by rfl⟩ : syracuseStep 4448861 = 1668323) (by norm_num)
theorem B2965907 : Blo 1975435 2965907 := bstep (se 1 (by rfl) ⟨2224430, by rfl⟩ : syracuseStep 2965907 = 4448861) B4448861
theorem B1977271 : Blo 1975435 1977271 := bstep (se 1 (by rfl) ⟨1482953, by rfl⟩ : syracuseStep 1977271 = 2965907) B2965907
theorem B3336653 : Blo 1975435 3336653 := bbase (se 3 (by rfl) ⟨625622, by rfl⟩ : syracuseStep 3336653 = 1251245) (by norm_num)
theorem B2224435 : Blo 1975435 2224435 := bstep (se 1 (by rfl) ⟨1668326, by rfl⟩ : syracuseStep 2224435 = 3336653) B3336653
theorem B2965913 : Blo 1975435 2965913 := bstep (se 2 (by rfl) ⟨1112217, by rfl⟩ : syracuseStep 2965913 = 2224435) B2224435
theorem B1977275 : Blo 1975435 1977275 := bstep (se 1 (by rfl) ⟨1482956, by rfl⟩ : syracuseStep 1977275 = 2965913) B2965913
theorem B2004257 : Blo 1975435 2004257 := bbase (se 2 (by rfl) ⟨751596, by rfl⟩ : syracuseStep 2004257 = 1503193) (by norm_num)
theorem B5344685 : Blo 1975435 5344685 := bstep (se 3 (by rfl) ⟨1002128, by rfl⟩ : syracuseStep 5344685 = 2004257) B2004257
theorem B3563123 : Blo 1975435 3563123 := bstep (se 1 (by rfl) ⟨2672342, by rfl⟩ : syracuseStep 3563123 = 5344685) B5344685
theorem B9501661 : Blo 1975435 9501661 := bstep (se 3 (by rfl) ⟨1781561, by rfl⟩ : syracuseStep 9501661 = 3563123) B3563123
theorem B12668881 : Blo 1975435 12668881 := bstep (se 2 (by rfl) ⟨4750830, by rfl⟩ : syracuseStep 12668881 = 9501661) B9501661
theorem B16891841 : Blo 1975435 16891841 := bstep (se 2 (by rfl) ⟨6334440, by rfl⟩ : syracuseStep 16891841 = 12668881) B12668881
theorem B11261227 : Blo 1975435 11261227 := bstep (se 1 (by rfl) ⟨8445920, by rfl⟩ : syracuseStep 11261227 = 16891841) B16891841
theorem B15014969 : Blo 1975435 15014969 := bstep (se 2 (by rfl) ⟨5630613, by rfl⟩ : syracuseStep 15014969 = 11261227) B11261227
theorem B10009979 : Blo 1975435 10009979 := bstep (se 1 (by rfl) ⟨7507484, by rfl⟩ : syracuseStep 10009979 = 15014969) B15014969
theorem B6673319 : Blo 1975435 6673319 := bstep (se 1 (by rfl) ⟨5004989, by rfl⟩ : syracuseStep 6673319 = 10009979) B10009979
theorem B4448879 : Blo 1975435 4448879 := bstep (se 1 (by rfl) ⟨3336659, by rfl⟩ : syracuseStep 4448879 = 6673319) B6673319
theorem B2965919 : Blo 1975435 2965919 := bstep (se 1 (by rfl) ⟨2224439, by rfl⟩ : syracuseStep 2965919 = 4448879) B4448879
theorem B1977279 : Blo 1975435 1977279 := bstep (se 1 (by rfl) ⟨1482959, by rfl⟩ : syracuseStep 1977279 = 2965919) B2965919
theorem B2965925 : Blo 1975435 2965925 := bbase (se 4 (by rfl) ⟨278055, by rfl⟩ : syracuseStep 2965925 = 556111) (by norm_num)
theorem B1977283 : Blo 1975435 1977283 := bstep (se 1 (by rfl) ⟨1482962, by rfl⟩ : syracuseStep 1977283 = 2965925) B2965925
theorem B2502505 : Blo 1975435 2502505 := bbase (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) (by norm_num)
theorem B3336673 : Blo 1975435 3336673 := bstep (se 2 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 3336673 = 2502505) B2502505
theorem B4448897 : Blo 1975435 4448897 := bstep (se 2 (by rfl) ⟨1668336, by rfl⟩ : syracuseStep 4448897 = 3336673) B3336673
theorem B2965931 : Blo 1975435 2965931 := bstep (se 1 (by rfl) ⟨2224448, by rfl⟩ : syracuseStep 2965931 = 4448897) B4448897
theorem B1977287 : Blo 1975435 1977287 := bstep (se 1 (by rfl) ⟨1482965, by rfl⟩ : syracuseStep 1977287 = 2965931) B2965931
theorem B2224453 : Blo 1975435 2224453 := bbase (se 4 (by rfl) ⟨208542, by rfl⟩ : syracuseStep 2224453 = 417085) (by norm_num)
theorem B2965937 : Blo 1975435 2965937 := bstep (se 2 (by rfl) ⟨1112226, by rfl⟩ : syracuseStep 2965937 = 2224453) B2224453
theorem B1977291 : Blo 1975435 1977291 := bstep (se 1 (by rfl) ⟨1482968, by rfl⟩ : syracuseStep 1977291 = 2965937) B2965937
theorem B3753773 : Blo 1975435 3753773 := bbase (se 3 (by rfl) ⟨703832, by rfl⟩ : syracuseStep 3753773 = 1407665) (by norm_num)
theorem B2502515 : Blo 1975435 2502515 := bstep (se 1 (by rfl) ⟨1876886, by rfl⟩ : syracuseStep 2502515 = 3753773) B3753773
theorem B6673373 : Blo 1975435 6673373 := bstep (se 3 (by rfl) ⟨1251257, by rfl⟩ : syracuseStep 6673373 = 2502515) B2502515
theorem B4448915 : Blo 1975435 4448915 := bstep (se 1 (by rfl) ⟨3336686, by rfl⟩ : syracuseStep 4448915 = 6673373) B6673373
theorem B2965943 : Blo 1975435 2965943 := bstep (se 1 (by rfl) ⟨2224457, by rfl⟩ : syracuseStep 2965943 = 4448915) B4448915
theorem B1977295 : Blo 1975435 1977295 := bstep (se 1 (by rfl) ⟨1482971, by rfl⟩ : syracuseStep 1977295 = 2965943) B2965943
theorem B2965949 : Blo 1975435 2965949 := bbase (se 3 (by rfl) ⟨556115, by rfl⟩ : syracuseStep 2965949 = 1112231) (by norm_num)
theorem B1977299 : Blo 1975435 1977299 := bstep (se 1 (by rfl) ⟨1482974, by rfl⟩ : syracuseStep 1977299 = 2965949) B2965949
theorem B4448933 : Blo 1975435 4448933 := bbase (se 4 (by rfl) ⟨417087, by rfl⟩ : syracuseStep 4448933 = 834175) (by norm_num)
theorem B2965955 : Blo 1975435 2965955 := bstep (se 1 (by rfl) ⟨2224466, by rfl⟩ : syracuseStep 2965955 = 4448933) B4448933
theorem B1977303 : Blo 1975435 1977303 := bstep (se 1 (by rfl) ⟨1482977, by rfl⟩ : syracuseStep 1977303 = 2965955) B2965955
theorem B5005061 : Blo 1975435 5005061 := bbase (se 4 (by rfl) ⟨469224, by rfl⟩ : syracuseStep 5005061 = 938449) (by norm_num)
theorem B3336707 : Blo 1975435 3336707 := bstep (se 1 (by rfl) ⟨2502530, by rfl⟩ : syracuseStep 3336707 = 5005061) B5005061
theorem B2224471 : Blo 1975435 2224471 := bstep (se 1 (by rfl) ⟨1668353, by rfl⟩ : syracuseStep 2224471 = 3336707) B3336707
theorem B2965961 : Blo 1975435 2965961 := bstep (se 2 (by rfl) ⟨1112235, by rfl⟩ : syracuseStep 2965961 = 2224471) B2224471
theorem B1977307 : Blo 1975435 1977307 := bstep (se 1 (by rfl) ⟨1482980, by rfl⟩ : syracuseStep 1977307 = 2965961) B2965961
theorem B4223029 : Blo 1975435 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B5630705 : Blo 1975435 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B3753803 : Blo 1975435 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B10010141 : Blo 1975435 10010141 := bstep (se 3 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 10010141 = 3753803) B3753803
theorem B6673427 : Blo 1975435 6673427 := bstep (se 1 (by rfl) ⟨5005070, by rfl⟩ : syracuseStep 6673427 = 10010141) B10010141
theorem B4448951 : Blo 1975435 4448951 := bstep (se 1 (by rfl) ⟨3336713, by rfl⟩ : syracuseStep 4448951 = 6673427) B6673427
theorem B2965967 : Blo 1975435 2965967 := bstep (se 1 (by rfl) ⟨2224475, by rfl⟩ : syracuseStep 2965967 = 4448951) B4448951
theorem B1977311 : Blo 1975435 1977311 := bstep (se 1 (by rfl) ⟨1482983, by rfl⟩ : syracuseStep 1977311 = 2965967) B2965967
theorem B2965973 : Blo 1975435 2965973 := bbase (se 7 (by rfl) ⟨34757, by rfl⟩ : syracuseStep 2965973 = 69515) (by norm_num)
theorem B1977315 : Blo 1975435 1977315 := bstep (se 1 (by rfl) ⟨1482986, by rfl⟩ : syracuseStep 1977315 = 2965973) B2965973
theorem B7507637 : Blo 1975435 7507637 := bbase (se 5 (by rfl) ⟨351920, by rfl⟩ : syracuseStep 7507637 = 703841) (by norm_num)
theorem B5005091 : Blo 1975435 5005091 := bstep (se 1 (by rfl) ⟨3753818, by rfl⟩ : syracuseStep 5005091 = 7507637) B7507637
theorem B3336727 : Blo 1975435 3336727 := bstep (se 1 (by rfl) ⟨2502545, by rfl⟩ : syracuseStep 3336727 = 5005091) B5005091
theorem B4448969 : Blo 1975435 4448969 := bstep (se 2 (by rfl) ⟨1668363, by rfl⟩ : syracuseStep 4448969 = 3336727) B3336727
theorem B2965979 : Blo 1975435 2965979 := bstep (se 1 (by rfl) ⟨2224484, by rfl⟩ : syracuseStep 2965979 = 4448969) B4448969
theorem B1977319 : Blo 1975435 1977319 := bstep (se 1 (by rfl) ⟨1482989, by rfl⟩ : syracuseStep 1977319 = 2965979) B2965979
theorem B2224489 : Blo 1975435 2224489 := bbase (se 2 (by rfl) ⟨834183, by rfl⟩ : syracuseStep 2224489 = 1668367) (by norm_num)
theorem B2965985 : Blo 1975435 2965985 := bstep (se 2 (by rfl) ⟨1112244, by rfl⟩ : syracuseStep 2965985 = 2224489) B2224489
theorem B1977323 : Blo 1975435 1977323 := bstep (se 1 (by rfl) ⟨1482992, by rfl⟩ : syracuseStep 1977323 = 2965985) B2965985
theorem B9501893 : Blo 1975435 9501893 := bbase (se 4 (by rfl) ⟨890802, by rfl⟩ : syracuseStep 9501893 = 1781605) (by norm_num)
theorem B6334595 : Blo 1975435 6334595 := bstep (se 1 (by rfl) ⟨4750946, by rfl⟩ : syracuseStep 6334595 = 9501893) B9501893
theorem B4223063 : Blo 1975435 4223063 := bstep (se 1 (by rfl) ⟨3167297, by rfl⟩ : syracuseStep 4223063 = 6334595) B6334595
theorem B11261501 : Blo 1975435 11261501 := bstep (se 3 (by rfl) ⟨2111531, by rfl⟩ : syracuseStep 11261501 = 4223063) B4223063
theorem B7507667 : Blo 1975435 7507667 := bstep (se 1 (by rfl) ⟨5630750, by rfl⟩ : syracuseStep 7507667 = 11261501) B11261501
theorem B5005111 : Blo 1975435 5005111 := bstep (se 1 (by rfl) ⟨3753833, by rfl⟩ : syracuseStep 5005111 = 7507667) B7507667
theorem B6673481 : Blo 1975435 6673481 := bstep (se 2 (by rfl) ⟨2502555, by rfl⟩ : syracuseStep 6673481 = 5005111) B5005111
theorem B4448987 : Blo 1975435 4448987 := bstep (se 1 (by rfl) ⟨3336740, by rfl⟩ : syracuseStep 4448987 = 6673481) B6673481
theorem B2965991 : Blo 1975435 2965991 := bstep (se 1 (by rfl) ⟨2224493, by rfl⟩ : syracuseStep 2965991 = 4448987) B4448987
theorem B1977327 : Blo 1975435 1977327 := bstep (se 1 (by rfl) ⟨1482995, by rfl⟩ : syracuseStep 1977327 = 2965991) B2965991
theorem B2965997 : Blo 1975435 2965997 := bbase (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) (by norm_num)
theorem B1977331 : Blo 1975435 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B4449005 : Blo 1975435 4449005 := bbase (se 3 (by rfl) ⟨834188, by rfl⟩ : syracuseStep 4449005 = 1668377) (by norm_num)
theorem B2966003 : Blo 1975435 2966003 := bstep (se 1 (by rfl) ⟨2224502, by rfl⟩ : syracuseStep 2966003 = 4449005) B4449005
theorem B1977335 : Blo 1975435 1977335 := bstep (se 1 (by rfl) ⟨1483001, by rfl⟩ : syracuseStep 1977335 = 2966003) B2966003
theorem B2111545 : Blo 1975435 2111545 := bbase (se 2 (by rfl) ⟨791829, by rfl⟩ : syracuseStep 2111545 = 1583659) (by norm_num)
theorem B2815393 : Blo 1975435 2815393 := bstep (se 2 (by rfl) ⟨1055772, by rfl⟩ : syracuseStep 2815393 = 2111545) B2111545
theorem B3753857 : Blo 1975435 3753857 := bstep (se 2 (by rfl) ⟨1407696, by rfl⟩ : syracuseStep 3753857 = 2815393) B2815393
theorem B2502571 : Blo 1975435 2502571 := bstep (se 1 (by rfl) ⟨1876928, by rfl⟩ : syracuseStep 2502571 = 3753857) B3753857
theorem B3336761 : Blo 1975435 3336761 := bstep (se 2 (by rfl) ⟨1251285, by rfl⟩ : syracuseStep 3336761 = 2502571) B2502571
theorem B2224507 : Blo 1975435 2224507 := bstep (se 1 (by rfl) ⟨1668380, by rfl⟩ : syracuseStep 2224507 = 3336761) B3336761
theorem B2966009 : Blo 1975435 2966009 := bstep (se 2 (by rfl) ⟨1112253, by rfl⟩ : syracuseStep 2966009 = 2224507) B2224507
theorem B1977339 : Blo 1975435 1977339 := bstep (se 1 (by rfl) ⟨1483004, by rfl⟩ : syracuseStep 1977339 = 2966009) B2966009
theorem B14447413 : Blo 1975435 14447413 := bbase (se 5 (by rfl) ⟨677222, by rfl⟩ : syracuseStep 14447413 = 1354445) (by norm_num)
theorem B19263217 : Blo 1975435 19263217 := bstep (se 2 (by rfl) ⟨7223706, by rfl⟩ : syracuseStep 19263217 = 14447413) B14447413
theorem B25684289 : Blo 1975435 25684289 := bstep (se 2 (by rfl) ⟨9631608, by rfl⟩ : syracuseStep 25684289 = 19263217) B19263217
theorem B17122859 : Blo 1975435 17122859 := bstep (se 1 (by rfl) ⟨12842144, by rfl⟩ : syracuseStep 17122859 = 25684289) B25684289
theorem B11415239 : Blo 1975435 11415239 := bstep (se 1 (by rfl) ⟨8561429, by rfl⟩ : syracuseStep 11415239 = 17122859) B17122859
theorem B7610159 : Blo 1975435 7610159 := bstep (se 1 (by rfl) ⟨5707619, by rfl⟩ : syracuseStep 7610159 = 11415239) B11415239
theorem B5073439 : Blo 1975435 5073439 := bstep (se 1 (by rfl) ⟨3805079, by rfl⟩ : syracuseStep 5073439 = 7610159) B7610159
theorem B6764585 : Blo 1975435 6764585 := bstep (se 2 (by rfl) ⟨2536719, by rfl⟩ : syracuseStep 6764585 = 5073439) B5073439
theorem B72155573 : Blo 1975435 72155573 := bstep (se 5 (by rfl) ⟨3382292, by rfl⟩ : syracuseStep 72155573 = 6764585) B6764585
theorem B48103715 : Blo 1975435 48103715 := bstep (se 1 (by rfl) ⟨36077786, by rfl⟩ : syracuseStep 48103715 = 72155573) B72155573
theorem B32069143 : Blo 1975435 32069143 := bstep (se 1 (by rfl) ⟨24051857, by rfl⟩ : syracuseStep 32069143 = 48103715) B48103715
theorem B42758857 : Blo 1975435 42758857 := bstep (se 2 (by rfl) ⟨16034571, by rfl⟩ : syracuseStep 42758857 = 32069143) B32069143
theorem B57011809 : Blo 1975435 57011809 := bstep (se 2 (by rfl) ⟨21379428, by rfl⟩ : syracuseStep 57011809 = 42758857) B42758857
theorem B76015745 : Blo 1975435 76015745 := bstep (se 2 (by rfl) ⟨28505904, by rfl⟩ : syracuseStep 76015745 = 57011809) B57011809
theorem B50677163 : Blo 1975435 50677163 := bstep (se 1 (by rfl) ⟨38007872, by rfl⟩ : syracuseStep 50677163 = 76015745) B76015745
theorem B33784775 : Blo 1975435 33784775 := bstep (se 1 (by rfl) ⟨25338581, by rfl⟩ : syracuseStep 33784775 = 50677163) B50677163
theorem B22523183 : Blo 1975435 22523183 := bstep (se 1 (by rfl) ⟨16892387, by rfl⟩ : syracuseStep 22523183 = 33784775) B33784775
theorem B15015455 : Blo 1975435 15015455 := bstep (se 1 (by rfl) ⟨11261591, by rfl⟩ : syracuseStep 15015455 = 22523183) B22523183
theorem B10010303 : Blo 1975435 10010303 := bstep (se 1 (by rfl) ⟨7507727, by rfl⟩ : syracuseStep 10010303 = 15015455) B15015455
theorem B6673535 : Blo 1975435 6673535 := bstep (se 1 (by rfl) ⟨5005151, by rfl⟩ : syracuseStep 6673535 = 10010303) B10010303
theorem B4449023 : Blo 1975435 4449023 := bstep (se 1 (by rfl) ⟨3336767, by rfl⟩ : syracuseStep 4449023 = 6673535) B6673535
theorem B2966015 : Blo 1975435 2966015 := bstep (se 1 (by rfl) ⟨2224511, by rfl⟩ : syracuseStep 2966015 = 4449023) B4449023
theorem B1977343 : Blo 1975435 1977343 := bstep (se 1 (by rfl) ⟨1483007, by rfl⟩ : syracuseStep 1977343 = 2966015) B2966015
theorem B2966021 : Blo 1975435 2966021 := bbase (se 4 (by rfl) ⟨278064, by rfl⟩ : syracuseStep 2966021 = 556129) (by norm_num)
theorem B1977347 : Blo 1975435 1977347 := bstep (se 1 (by rfl) ⟨1483010, by rfl⟩ : syracuseStep 1977347 = 2966021) B2966021
theorem B3336781 : Blo 1975435 3336781 := bbase (se 3 (by rfl) ⟨625646, by rfl⟩ : syracuseStep 3336781 = 1251293) (by norm_num)
theorem B4449041 : Blo 1975435 4449041 := bstep (se 2 (by rfl) ⟨1668390, by rfl⟩ : syracuseStep 4449041 = 3336781) B3336781
theorem B2966027 : Blo 1975435 2966027 := bstep (se 1 (by rfl) ⟨2224520, by rfl⟩ : syracuseStep 2966027 = 4449041) B4449041
theorem B1977351 : Blo 1975435 1977351 := bstep (se 1 (by rfl) ⟨1483013, by rfl⟩ : syracuseStep 1977351 = 2966027) B2966027
theorem B2224525 : Blo 1975435 2224525 := bbase (se 3 (by rfl) ⟨417098, by rfl⟩ : syracuseStep 2224525 = 834197) (by norm_num)
theorem B2966033 : Blo 1975435 2966033 := bstep (se 2 (by rfl) ⟨1112262, by rfl⟩ : syracuseStep 2966033 = 2224525) B2224525
theorem B1977355 : Blo 1975435 1977355 := bstep (se 1 (by rfl) ⟨1483016, by rfl⟩ : syracuseStep 1977355 = 2966033) B2966033
theorem B6673589 : Blo 1975435 6673589 := bbase (se 5 (by rfl) ⟨312824, by rfl⟩ : syracuseStep 6673589 = 625649) (by norm_num)
theorem B4449059 : Blo 1975435 4449059 := bstep (se 1 (by rfl) ⟨3336794, by rfl⟩ : syracuseStep 4449059 = 6673589) B6673589
theorem B2966039 : Blo 1975435 2966039 := bstep (se 1 (by rfl) ⟨2224529, by rfl⟩ : syracuseStep 2966039 = 4449059) B4449059
theorem B1977359 : Blo 1975435 1977359 := bstep (se 1 (by rfl) ⟨1483019, by rfl⟩ : syracuseStep 1977359 = 2966039) B2966039
theorem B2966045 : Blo 1975435 2966045 := bbase (se 3 (by rfl) ⟨556133, by rfl⟩ : syracuseStep 2966045 = 1112267) (by norm_num)
theorem B1977363 : Blo 1975435 1977363 := bstep (se 1 (by rfl) ⟨1483022, by rfl⟩ : syracuseStep 1977363 = 2966045) B2966045
theorem B4449077 : Blo 1975435 4449077 := bbase (se 5 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 4449077 = 417101) (by norm_num)
theorem B2966051 : Blo 1975435 2966051 := bstep (se 1 (by rfl) ⟨2224538, by rfl⟩ : syracuseStep 2966051 = 4449077) B4449077
theorem B1977367 : Blo 1975435 1977367 := bstep (se 1 (by rfl) ⟨1483025, by rfl⟩ : syracuseStep 1977367 = 2966051) B2966051
theorem B4008701 : Blo 1975435 4008701 := bbase (se 3 (by rfl) ⟨751631, by rfl⟩ : syracuseStep 4008701 = 1503263) (by norm_num)
theorem B10689869 : Blo 1975435 10689869 := bstep (se 3 (by rfl) ⟨2004350, by rfl⟩ : syracuseStep 10689869 = 4008701) B4008701
theorem B7126579 : Blo 1975435 7126579 := bstep (se 1 (by rfl) ⟨5344934, by rfl⟩ : syracuseStep 7126579 = 10689869) B10689869
theorem B9502105 : Blo 1975435 9502105 := bstep (se 2 (by rfl) ⟨3563289, by rfl⟩ : syracuseStep 9502105 = 7126579) B7126579
theorem B12669473 : Blo 1975435 12669473 := bstep (se 2 (by rfl) ⟨4751052, by rfl⟩ : syracuseStep 12669473 = 9502105) B9502105
theorem B8446315 : Blo 1975435 8446315 := bstep (se 1 (by rfl) ⟨6334736, by rfl⟩ : syracuseStep 8446315 = 12669473) B12669473
theorem B11261753 : Blo 1975435 11261753 := bstep (se 2 (by rfl) ⟨4223157, by rfl⟩ : syracuseStep 11261753 = 8446315) B8446315
theorem B7507835 : Blo 1975435 7507835 := bstep (se 1 (by rfl) ⟨5630876, by rfl⟩ : syracuseStep 7507835 = 11261753) B11261753
theorem B5005223 : Blo 1975435 5005223 := bstep (se 1 (by rfl) ⟨3753917, by rfl⟩ : syracuseStep 5005223 = 7507835) B7507835
theorem B3336815 : Blo 1975435 3336815 := bstep (se 1 (by rfl) ⟨2502611, by rfl⟩ : syracuseStep 3336815 = 5005223) B5005223
theorem B2224543 : Blo 1975435 2224543 := bstep (se 1 (by rfl) ⟨1668407, by rfl⟩ : syracuseStep 2224543 = 3336815) B3336815
theorem B2966057 : Blo 1975435 2966057 := bstep (se 2 (by rfl) ⟨1112271, by rfl⟩ : syracuseStep 2966057 = 2224543) B2224543
theorem B1977371 : Blo 1975435 1977371 := bstep (se 1 (by rfl) ⟨1483028, by rfl⟩ : syracuseStep 1977371 = 2966057) B2966057
theorem B10147045 : Blo 1975435 10147045 := bbase (se 4 (by rfl) ⟨951285, by rfl⟩ : syracuseStep 10147045 = 1902571) (by norm_num)
theorem B13529393 : Blo 1975435 13529393 := bstep (se 2 (by rfl) ⟨5073522, by rfl⟩ : syracuseStep 13529393 = 10147045) B10147045
theorem B9019595 : Blo 1975435 9019595 := bstep (se 1 (by rfl) ⟨6764696, by rfl⟩ : syracuseStep 9019595 = 13529393) B13529393
theorem B6013063 : Blo 1975435 6013063 := bstep (se 1 (by rfl) ⟨4509797, by rfl⟩ : syracuseStep 6013063 = 9019595) B9019595
theorem B8017417 : Blo 1975435 8017417 := bstep (se 2 (by rfl) ⟨3006531, by rfl⟩ : syracuseStep 8017417 = 6013063) B6013063
theorem B10689889 : Blo 1975435 10689889 := bstep (se 2 (by rfl) ⟨4008708, by rfl⟩ : syracuseStep 10689889 = 8017417) B8017417
theorem B14253185 : Blo 1975435 14253185 := bstep (se 2 (by rfl) ⟨5344944, by rfl⟩ : syracuseStep 14253185 = 10689889) B10689889
theorem B9502123 : Blo 1975435 9502123 := bstep (se 1 (by rfl) ⟨7126592, by rfl⟩ : syracuseStep 9502123 = 14253185) B14253185
theorem B12669497 : Blo 1975435 12669497 := bstep (se 2 (by rfl) ⟨4751061, by rfl⟩ : syracuseStep 12669497 = 9502123) B9502123
theorem B8446331 : Blo 1975435 8446331 := bstep (se 1 (by rfl) ⟨6334748, by rfl⟩ : syracuseStep 8446331 = 12669497) B12669497
theorem B5630887 : Blo 1975435 5630887 := bstep (se 1 (by rfl) ⟨4223165, by rfl⟩ : syracuseStep 5630887 = 8446331) B8446331
theorem B7507849 : Blo 1975435 7507849 := bstep (se 2 (by rfl) ⟨2815443, by rfl⟩ : syracuseStep 7507849 = 5630887) B5630887
theorem B10010465 : Blo 1975435 10010465 := bstep (se 2 (by rfl) ⟨3753924, by rfl⟩ : syracuseStep 10010465 = 7507849) B7507849
theorem B6673643 : Blo 1975435 6673643 := bstep (se 1 (by rfl) ⟨5005232, by rfl⟩ : syracuseStep 6673643 = 10010465) B10010465
theorem B4449095 : Blo 1975435 4449095 := bstep (se 1 (by rfl) ⟨3336821, by rfl⟩ : syracuseStep 4449095 = 6673643) B6673643
theorem B2966063 : Blo 1975435 2966063 := bstep (se 1 (by rfl) ⟨2224547, by rfl⟩ : syracuseStep 2966063 = 4449095) B4449095
theorem B1977375 : Blo 1975435 1977375 := bstep (se 1 (by rfl) ⟨1483031, by rfl⟩ : syracuseStep 1977375 = 2966063) B2966063
theorem B2966069 : Blo 1975435 2966069 := bbase (se 5 (by rfl) ⟨139034, by rfl⟩ : syracuseStep 2966069 = 278069) (by norm_num)
theorem B1977379 : Blo 1975435 1977379 := bstep (se 1 (by rfl) ⟨1483034, by rfl⟩ : syracuseStep 1977379 = 2966069) B2966069
theorem B5005253 : Blo 1975435 5005253 := bbase (se 4 (by rfl) ⟨469242, by rfl⟩ : syracuseStep 5005253 = 938485) (by norm_num)
theorem B3336835 : Blo 1975435 3336835 := bstep (se 1 (by rfl) ⟨2502626, by rfl⟩ : syracuseStep 3336835 = 5005253) B5005253
theorem B4449113 : Blo 1975435 4449113 := bstep (se 2 (by rfl) ⟨1668417, by rfl⟩ : syracuseStep 4449113 = 3336835) B3336835
theorem B2966075 : Blo 1975435 2966075 := bstep (se 1 (by rfl) ⟨2224556, by rfl⟩ : syracuseStep 2966075 = 4449113) B4449113
theorem B1977383 : Blo 1975435 1977383 := bstep (se 1 (by rfl) ⟨1483037, by rfl⟩ : syracuseStep 1977383 = 2966075) B2966075
theorem B2224561 : Blo 1975435 2224561 := bbase (se 2 (by rfl) ⟨834210, by rfl⟩ : syracuseStep 2224561 = 1668421) (by norm_num)
theorem B2966081 : Blo 1975435 2966081 := bstep (se 2 (by rfl) ⟨1112280, by rfl⟩ : syracuseStep 2966081 = 2224561) B2224561
theorem B1977387 : Blo 1975435 1977387 := bstep (se 1 (by rfl) ⟨1483040, by rfl⟩ : syracuseStep 1977387 = 2966081) B2966081
theorem B5630933 : Blo 1975435 5630933 := bbase (se 7 (by rfl) ⟨65987, by rfl⟩ : syracuseStep 5630933 = 131975) (by norm_num)
theorem B3753955 : Blo 1975435 3753955 := bstep (se 1 (by rfl) ⟨2815466, by rfl⟩ : syracuseStep 3753955 = 5630933) B5630933
theorem B5005273 : Blo 1975435 5005273 := bstep (se 2 (by rfl) ⟨1876977, by rfl⟩ : syracuseStep 5005273 = 3753955) B3753955
theorem B6673697 : Blo 1975435 6673697 := bstep (se 2 (by rfl) ⟨2502636, by rfl⟩ : syracuseStep 6673697 = 5005273) B5005273
theorem B4449131 : Blo 1975435 4449131 := bstep (se 1 (by rfl) ⟨3336848, by rfl⟩ : syracuseStep 4449131 = 6673697) B6673697
theorem B2966087 : Blo 1975435 2966087 := bstep (se 1 (by rfl) ⟨2224565, by rfl⟩ : syracuseStep 2966087 = 4449131) B4449131
theorem B1977391 : Blo 1975435 1977391 := bstep (se 1 (by rfl) ⟨1483043, by rfl⟩ : syracuseStep 1977391 = 2966087) B2966087
theorem B2966093 : Blo 1975435 2966093 := bbase (se 3 (by rfl) ⟨556142, by rfl⟩ : syracuseStep 2966093 = 1112285) (by norm_num)
theorem B1977395 : Blo 1975435 1977395 := bstep (se 1 (by rfl) ⟨1483046, by rfl⟩ : syracuseStep 1977395 = 2966093) B2966093
theorem B4449149 : Blo 1975435 4449149 := bbase (se 3 (by rfl) ⟨834215, by rfl⟩ : syracuseStep 4449149 = 1668431) (by norm_num)
theorem B2966099 : Blo 1975435 2966099 := bstep (se 1 (by rfl) ⟨2224574, by rfl⟩ : syracuseStep 2966099 = 4449149) B4449149
theorem B1977399 : Blo 1975435 1977399 := bstep (se 1 (by rfl) ⟨1483049, by rfl⟩ : syracuseStep 1977399 = 2966099) B2966099
theorem B3336869 : Blo 1975435 3336869 := bbase (se 4 (by rfl) ⟨312831, by rfl⟩ : syracuseStep 3336869 = 625663) (by norm_num)
theorem B2224579 : Blo 1975435 2224579 := bstep (se 1 (by rfl) ⟨1668434, by rfl⟩ : syracuseStep 2224579 = 3336869) B3336869
theorem B2966105 : Blo 1975435 2966105 := bstep (se 2 (by rfl) ⟨1112289, by rfl⟩ : syracuseStep 2966105 = 2224579) B2224579
theorem B1977403 : Blo 1975435 1977403 := bstep (se 1 (by rfl) ⟨1483052, by rfl⟩ : syracuseStep 1977403 = 2966105) B2966105
theorem B2111617 : Blo 1975435 2111617 := bbase (se 2 (by rfl) ⟨791856, by rfl⟩ : syracuseStep 2111617 = 1583713) (by norm_num)
theorem B2815489 : Blo 1975435 2815489 := bstep (se 2 (by rfl) ⟨1055808, by rfl⟩ : syracuseStep 2815489 = 2111617) B2111617
theorem B15015941 : Blo 1975435 15015941 := bstep (se 4 (by rfl) ⟨1407744, by rfl⟩ : syracuseStep 15015941 = 2815489) B2815489
theorem B10010627 : Blo 1975435 10010627 := bstep (se 1 (by rfl) ⟨7507970, by rfl⟩ : syracuseStep 10010627 = 15015941) B15015941
theorem B6673751 : Blo 1975435 6673751 := bstep (se 1 (by rfl) ⟨5005313, by rfl⟩ : syracuseStep 6673751 = 10010627) B10010627
theorem B4449167 : Blo 1975435 4449167 := bstep (se 1 (by rfl) ⟨3336875, by rfl⟩ : syracuseStep 4449167 = 6673751) B6673751
theorem B2966111 : Blo 1975435 2966111 := bstep (se 1 (by rfl) ⟨2224583, by rfl⟩ : syracuseStep 2966111 = 4449167) B4449167
theorem B1977407 : Blo 1975435 1977407 := bstep (se 1 (by rfl) ⟨1483055, by rfl⟩ : syracuseStep 1977407 = 2966111) B2966111
theorem B2966117 : Blo 1975435 2966117 := bbase (se 4 (by rfl) ⟨278073, by rfl⟩ : syracuseStep 2966117 = 556147) (by norm_num)
theorem B1977411 : Blo 1975435 1977411 := bstep (se 1 (by rfl) ⟨1483058, by rfl⟩ : syracuseStep 1977411 = 2966117) B2966117
theorem B2815501 : Blo 1975435 2815501 := bbase (se 3 (by rfl) ⟨527906, by rfl⟩ : syracuseStep 2815501 = 1055813) (by norm_num)
theorem B3754001 : Blo 1975435 3754001 := bstep (se 2 (by rfl) ⟨1407750, by rfl⟩ : syracuseStep 3754001 = 2815501) B2815501
theorem B2502667 : Blo 1975435 2502667 := bstep (se 1 (by rfl) ⟨1877000, by rfl⟩ : syracuseStep 2502667 = 3754001) B3754001
theorem B3336889 : Blo 1975435 3336889 := bstep (se 2 (by rfl) ⟨1251333, by rfl⟩ : syracuseStep 3336889 = 2502667) B2502667
theorem B4449185 : Blo 1975435 4449185 := bstep (se 2 (by rfl) ⟨1668444, by rfl⟩ : syracuseStep 4449185 = 3336889) B3336889
theorem B2966123 : Blo 1975435 2966123 := bstep (se 1 (by rfl) ⟨2224592, by rfl⟩ : syracuseStep 2966123 = 4449185) B4449185
theorem B1977415 : Blo 1975435 1977415 := bstep (se 1 (by rfl) ⟨1483061, by rfl⟩ : syracuseStep 1977415 = 2966123) B2966123
theorem B2224597 : Blo 1975435 2224597 := bbase (se 7 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 2224597 = 52139) (by norm_num)
theorem B2966129 : Blo 1975435 2966129 := bstep (se 2 (by rfl) ⟨1112298, by rfl⟩ : syracuseStep 2966129 = 2224597) B2224597
theorem B1977419 : Blo 1975435 1977419 := bstep (se 1 (by rfl) ⟨1483064, by rfl⟩ : syracuseStep 1977419 = 2966129) B2966129
theorem B2502677 : Blo 1975435 2502677 := bbase (se 6 (by rfl) ⟨58656, by rfl⟩ : syracuseStep 2502677 = 117313) (by norm_num)
theorem B6673805 : Blo 1975435 6673805 := bstep (se 3 (by rfl) ⟨1251338, by rfl⟩ : syracuseStep 6673805 = 2502677) B2502677
theorem B4449203 : Blo 1975435 4449203 := bstep (se 1 (by rfl) ⟨3336902, by rfl⟩ : syracuseStep 4449203 = 6673805) B6673805
theorem B2966135 : Blo 1975435 2966135 := bstep (se 1 (by rfl) ⟨2224601, by rfl⟩ : syracuseStep 2966135 = 4449203) B4449203
theorem B1977423 : Blo 1975435 1977423 := bstep (se 1 (by rfl) ⟨1483067, by rfl⟩ : syracuseStep 1977423 = 2966135) B2966135
theorem B2966141 : Blo 1975435 2966141 := bbase (se 3 (by rfl) ⟨556151, by rfl⟩ : syracuseStep 2966141 = 1112303) (by norm_num)
theorem B1977427 : Blo 1975435 1977427 := bstep (se 1 (by rfl) ⟨1483070, by rfl⟩ : syracuseStep 1977427 = 2966141) B2966141
theorem B4449221 : Blo 1975435 4449221 := bbase (se 4 (by rfl) ⟨417114, by rfl⟩ : syracuseStep 4449221 = 834229) (by norm_num)
theorem B2966147 : Blo 1975435 2966147 := bstep (se 1 (by rfl) ⟨2224610, by rfl⟩ : syracuseStep 2966147 = 4449221) B4449221
theorem B1977431 : Blo 1975435 1977431 := bstep (se 1 (by rfl) ⟨1483073, by rfl⟩ : syracuseStep 1977431 = 2966147) B2966147
theorem B10426133 : Blo 1975435 10426133 := bbase (se 6 (by rfl) ⟨244362, by rfl⟩ : syracuseStep 10426133 = 488725) (by norm_num)
theorem B6950755 : Blo 1975435 6950755 := bstep (se 1 (by rfl) ⟨5213066, by rfl⟩ : syracuseStep 6950755 = 10426133) B10426133
theorem B37070693 : Blo 1975435 37070693 := bstep (se 4 (by rfl) ⟨3475377, by rfl⟩ : syracuseStep 37070693 = 6950755) B6950755
theorem B24713795 : Blo 1975435 24713795 := bstep (se 1 (by rfl) ⟨18535346, by rfl⟩ : syracuseStep 24713795 = 37070693) B37070693
theorem B65903453 : Blo 1975435 65903453 := bstep (se 3 (by rfl) ⟨12356897, by rfl⟩ : syracuseStep 65903453 = 24713795) B24713795
theorem B43935635 : Blo 1975435 43935635 := bstep (se 1 (by rfl) ⟨32951726, by rfl⟩ : syracuseStep 43935635 = 65903453) B65903453
theorem B29290423 : Blo 1975435 29290423 := bstep (se 1 (by rfl) ⟨21967817, by rfl⟩ : syracuseStep 29290423 = 43935635) B43935635
theorem B39053897 : Blo 1975435 39053897 := bstep (se 2 (by rfl) ⟨14645211, by rfl⟩ : syracuseStep 39053897 = 29290423) B29290423
theorem B26035931 : Blo 1975435 26035931 := bstep (se 1 (by rfl) ⟨19526948, by rfl⟩ : syracuseStep 26035931 = 39053897) B39053897
theorem B69429149 : Blo 1975435 69429149 := bstep (se 3 (by rfl) ⟨13017965, by rfl⟩ : syracuseStep 69429149 = 26035931) B26035931
theorem B46286099 : Blo 1975435 46286099 := bstep (se 1 (by rfl) ⟨34714574, by rfl⟩ : syracuseStep 46286099 = 69429149) B69429149
theorem B30857399 : Blo 1975435 30857399 := bstep (se 1 (by rfl) ⟨23143049, by rfl⟩ : syracuseStep 30857399 = 46286099) B46286099
theorem B20571599 : Blo 1975435 20571599 := bstep (se 1 (by rfl) ⟨15428699, by rfl⟩ : syracuseStep 20571599 = 30857399) B30857399
theorem B13714399 : Blo 1975435 13714399 := bstep (se 1 (by rfl) ⟨10285799, by rfl⟩ : syracuseStep 13714399 = 20571599) B20571599
theorem B73143461 : Blo 1975435 73143461 := bstep (se 4 (by rfl) ⟨6857199, by rfl⟩ : syracuseStep 73143461 = 13714399) B13714399
theorem B48762307 : Blo 1975435 48762307 := bstep (se 1 (by rfl) ⟨36571730, by rfl⟩ : syracuseStep 48762307 = 73143461) B73143461
theorem B260065637 : Blo 1975435 260065637 := bstep (se 4 (by rfl) ⟨24381153, by rfl⟩ : syracuseStep 260065637 = 48762307) B48762307
theorem B173377091 : Blo 1975435 173377091 := bstep (se 1 (by rfl) ⟨130032818, by rfl⟩ : syracuseStep 173377091 = 260065637) B260065637
theorem B115584727 : Blo 1975435 115584727 := bstep (se 1 (by rfl) ⟨86688545, by rfl⟩ : syracuseStep 115584727 = 173377091) B173377091
theorem B154112969 : Blo 1975435 154112969 := bstep (se 2 (by rfl) ⟨57792363, by rfl⟩ : syracuseStep 154112969 = 115584727) B115584727
theorem B102741979 : Blo 1975435 102741979 := bstep (se 1 (by rfl) ⟨77056484, by rfl⟩ : syracuseStep 102741979 = 154112969) B154112969
theorem B136989305 : Blo 1975435 136989305 := bstep (se 2 (by rfl) ⟨51370989, by rfl⟩ : syracuseStep 136989305 = 102741979) B102741979
theorem B91326203 : Blo 1975435 91326203 := bstep (se 1 (by rfl) ⟨68494652, by rfl⟩ : syracuseStep 91326203 = 136989305) B136989305
theorem B60884135 : Blo 1975435 60884135 := bstep (se 1 (by rfl) ⟨45663101, by rfl⟩ : syracuseStep 60884135 = 91326203) B91326203
theorem B40589423 : Blo 1975435 40589423 := bstep (se 1 (by rfl) ⟨30442067, by rfl⟩ : syracuseStep 40589423 = 60884135) B60884135
theorem B27059615 : Blo 1975435 27059615 := bstep (se 1 (by rfl) ⟨20294711, by rfl⟩ : syracuseStep 27059615 = 40589423) B40589423
theorem B18039743 : Blo 1975435 18039743 := bstep (se 1 (by rfl) ⟨13529807, by rfl⟩ : syracuseStep 18039743 = 27059615) B27059615
theorem B12026495 : Blo 1975435 12026495 := bstep (se 1 (by rfl) ⟨9019871, by rfl⟩ : syracuseStep 12026495 = 18039743) B18039743
theorem B8017663 : Blo 1975435 8017663 := bstep (se 1 (by rfl) ⟨6013247, by rfl⟩ : syracuseStep 8017663 = 12026495) B12026495
theorem B10690217 : Blo 1975435 10690217 := bstep (se 2 (by rfl) ⟨4008831, by rfl⟩ : syracuseStep 10690217 = 8017663) B8017663
theorem B7126811 : Blo 1975435 7126811 := bstep (se 1 (by rfl) ⟨5345108, by rfl⟩ : syracuseStep 7126811 = 10690217) B10690217
theorem B4751207 : Blo 1975435 4751207 := bstep (se 1 (by rfl) ⟨3563405, by rfl⟩ : syracuseStep 4751207 = 7126811) B7126811
theorem B3167471 : Blo 1975435 3167471 := bstep (se 1 (by rfl) ⟨2375603, by rfl⟩ : syracuseStep 3167471 = 4751207) B4751207
theorem B8446589 : Blo 1975435 8446589 := bstep (se 3 (by rfl) ⟨1583735, by rfl⟩ : syracuseStep 8446589 = 3167471) B3167471
theorem B5631059 : Blo 1975435 5631059 := bstep (se 1 (by rfl) ⟨4223294, by rfl⟩ : syracuseStep 5631059 = 8446589) B8446589
theorem B3754039 : Blo 1975435 3754039 := bstep (se 1 (by rfl) ⟨2815529, by rfl⟩ : syracuseStep 3754039 = 5631059) B5631059
theorem B5005385 : Blo 1975435 5005385 := bstep (se 2 (by rfl) ⟨1877019, by rfl⟩ : syracuseStep 5005385 = 3754039) B3754039
theorem B3336923 : Blo 1975435 3336923 := bstep (se 1 (by rfl) ⟨2502692, by rfl⟩ : syracuseStep 3336923 = 5005385) B5005385
theorem B2224615 : Blo 1975435 2224615 := bstep (se 1 (by rfl) ⟨1668461, by rfl⟩ : syracuseStep 2224615 = 3336923) B3336923
theorem B2966153 : Blo 1975435 2966153 := bstep (se 2 (by rfl) ⟨1112307, by rfl⟩ : syracuseStep 2966153 = 2224615) B2224615
theorem B1977435 : Blo 1975435 1977435 := bstep (se 1 (by rfl) ⟨1483076, by rfl⟩ : syracuseStep 1977435 = 2966153) B2966153
theorem C0 (j : ℕ) (h1 : 493858 ≤ j) (h2 : j ≤ 494358) : Blo 1975435 (4 * j + 3) := by
  interval_cases j
  · exact B1975435
  · exact B1975439
  · exact B1975443
  · exact B1975447
  · exact B1975451
  · exact B1975455
  · exact B1975459
  · exact B1975463
  · exact B1975467
  · exact B1975471
  · exact B1975475
  · exact B1975479
  · exact B1975483
  · exact B1975487
  · exact B1975491
  · exact B1975495
  · exact B1975499
  · exact B1975503
  · exact B1975507
  · exact B1975511
  · exact B1975515
  · exact B1975519
  · exact B1975523
  · exact B1975527
  · exact B1975531
  · exact B1975535
  · exact B1975539
  · exact B1975543
  · exact B1975547
  · exact B1975551
  · exact B1975555
  · exact B1975559
  · exact B1975563
  · exact B1975567
  · exact B1975571
  · exact B1975575
  · exact B1975579
  · exact B1975583
  · exact B1975587
  · exact B1975591
  · exact B1975595
  · exact B1975599
  · exact B1975603
  · exact B1975607
  · exact B1975611
  · exact B1975615
  · exact B1975619
  · exact B1975623
  · exact B1975627
  · exact B1975631
  · exact B1975635
  · exact B1975639
  · exact B1975643
  · exact B1975647
  · exact B1975651
  · exact B1975655
  · exact B1975659
  · exact B1975663
  · exact B1975667
  · exact B1975671
  · exact B1975675
  · exact B1975679
  · exact B1975683
  · exact B1975687
  · exact B1975691
  · exact B1975695
  · exact B1975699
  · exact B1975703
  · exact B1975707
  · exact B1975711
  · exact B1975715
  · exact B1975719
  · exact B1975723
  · exact B1975727
  · exact B1975731
  · exact B1975735
  · exact B1975739
  · exact B1975743
  · exact B1975747
  · exact B1975751
  · exact B1975755
  · exact B1975759
  · exact B1975763
  · exact B1975767
  · exact B1975771
  · exact B1975775
  · exact B1975779
  · exact B1975783
  · exact B1975787
  · exact B1975791
  · exact B1975795
  · exact B1975799
  · exact B1975803
  · exact B1975807
  · exact B1975811
  · exact B1975815
  · exact B1975819
  · exact B1975823
  · exact B1975827
  · exact B1975831
  · exact B1975835
  · exact B1975839
  · exact B1975843
  · exact B1975847
  · exact B1975851
  · exact B1975855
  · exact B1975859
  · exact B1975863
  · exact B1975867
  · exact B1975871
  · exact B1975875
  · exact B1975879
  · exact B1975883
  · exact B1975887
  · exact B1975891
  · exact B1975895
  · exact B1975899
  · exact B1975903
  · exact B1975907
  · exact B1975911
  · exact B1975915
  · exact B1975919
  · exact B1975923
  · exact B1975927
  · exact B1975931
  · exact B1975935
  · exact B1975939
  · exact B1975943
  · exact B1975947
  · exact B1975951
  · exact B1975955
  · exact B1975959
  · exact B1975963
  · exact B1975967
  · exact B1975971
  · exact B1975975
  · exact B1975979
  · exact B1975983
  · exact B1975987
  · exact B1975991
  · exact B1975995
  · exact B1975999
  · exact B1976003
  · exact B1976007
  · exact B1976011
  · exact B1976015
  · exact B1976019
  · exact B1976023
  · exact B1976027
  · exact B1976031
  · exact B1976035
  · exact B1976039
  · exact B1976043
  · exact B1976047
  · exact B1976051
  · exact B1976055
  · exact B1976059
  · exact B1976063
  · exact B1976067
  · exact B1976071
  · exact B1976075
  · exact B1976079
  · exact B1976083
  · exact B1976087
  · exact B1976091
  · exact B1976095
  · exact B1976099
  · exact B1976103
  · exact B1976107
  · exact B1976111
  · exact B1976115
  · exact B1976119
  · exact B1976123
  · exact B1976127
  · exact B1976131
  · exact B1976135
  · exact B1976139
  · exact B1976143
  · exact B1976147
  · exact B1976151
  · exact B1976155
  · exact B1976159
  · exact B1976163
  · exact B1976167
  · exact B1976171
  · exact B1976175
  · exact B1976179
  · exact B1976183
  · exact B1976187
  · exact B1976191
  · exact B1976195
  · exact B1976199
  · exact B1976203
  · exact B1976207
  · exact B1976211
  · exact B1976215
  · exact B1976219
  · exact B1976223
  · exact B1976227
  · exact B1976231
  · exact B1976235
  · exact B1976239
  · exact B1976243
  · exact B1976247
  · exact B1976251
  · exact B1976255
  · exact B1976259
  · exact B1976263
  · exact B1976267
  · exact B1976271
  · exact B1976275
  · exact B1976279
  · exact B1976283
  · exact B1976287
  · exact B1976291
  · exact B1976295
  · exact B1976299
  · exact B1976303
  · exact B1976307
  · exact B1976311
  · exact B1976315
  · exact B1976319
  · exact B1976323
  · exact B1976327
  · exact B1976331
  · exact B1976335
  · exact B1976339
  · exact B1976343
  · exact B1976347
  · exact B1976351
  · exact B1976355
  · exact B1976359
  · exact B1976363
  · exact B1976367
  · exact B1976371
  · exact B1976375
  · exact B1976379
  · exact B1976383
  · exact B1976387
  · exact B1976391
  · exact B1976395
  · exact B1976399
  · exact B1976403
  · exact B1976407
  · exact B1976411
  · exact B1976415
  · exact B1976419
  · exact B1976423
  · exact B1976427
  · exact B1976431
  · exact B1976435
  · exact B1976439
  · exact B1976443
  · exact B1976447
  · exact B1976451
  · exact B1976455
  · exact B1976459
  · exact B1976463
  · exact B1976467
  · exact B1976471
  · exact B1976475
  · exact B1976479
  · exact B1976483
  · exact B1976487
  · exact B1976491
  · exact B1976495
  · exact B1976499
  · exact B1976503
  · exact B1976507
  · exact B1976511
  · exact B1976515
  · exact B1976519
  · exact B1976523
  · exact B1976527
  · exact B1976531
  · exact B1976535
  · exact B1976539
  · exact B1976543
  · exact B1976547
  · exact B1976551
  · exact B1976555
  · exact B1976559
  · exact B1976563
  · exact B1976567
  · exact B1976571
  · exact B1976575
  · exact B1976579
  · exact B1976583
  · exact B1976587
  · exact B1976591
  · exact B1976595
  · exact B1976599
  · exact B1976603
  · exact B1976607
  · exact B1976611
  · exact B1976615
  · exact B1976619
  · exact B1976623
  · exact B1976627
  · exact B1976631
  · exact B1976635
  · exact B1976639
  · exact B1976643
  · exact B1976647
  · exact B1976651
  · exact B1976655
  · exact B1976659
  · exact B1976663
  · exact B1976667
  · exact B1976671
  · exact B1976675
  · exact B1976679
  · exact B1976683
  · exact B1976687
  · exact B1976691
  · exact B1976695
  · exact B1976699
  · exact B1976703
  · exact B1976707
  · exact B1976711
  · exact B1976715
  · exact B1976719
  · exact B1976723
  · exact B1976727
  · exact B1976731
  · exact B1976735
  · exact B1976739
  · exact B1976743
  · exact B1976747
  · exact B1976751
  · exact B1976755
  · exact B1976759
  · exact B1976763
  · exact B1976767
  · exact B1976771
  · exact B1976775
  · exact B1976779
  · exact B1976783
  · exact B1976787
  · exact B1976791
  · exact B1976795
  · exact B1976799
  · exact B1976803
  · exact B1976807
  · exact B1976811
  · exact B1976815
  · exact B1976819
  · exact B1976823
  · exact B1976827
  · exact B1976831
  · exact B1976835
  · exact B1976839
  · exact B1976843
  · exact B1976847
  · exact B1976851
  · exact B1976855
  · exact B1976859
  · exact B1976863
  · exact B1976867
  · exact B1976871
  · exact B1976875
  · exact B1976879
  · exact B1976883
  · exact B1976887
  · exact B1976891
  · exact B1976895
  · exact B1976899
  · exact B1976903
  · exact B1976907
  · exact B1976911
  · exact B1976915
  · exact B1976919
  · exact B1976923
  · exact B1976927
  · exact B1976931
  · exact B1976935
  · exact B1976939
  · exact B1976943
  · exact B1976947
  · exact B1976951
  · exact B1976955
  · exact B1976959
  · exact B1976963
  · exact B1976967
  · exact B1976971
  · exact B1976975
  · exact B1976979
  · exact B1976983
  · exact B1976987
  · exact B1976991
  · exact B1976995
  · exact B1976999
  · exact B1977003
  · exact B1977007
  · exact B1977011
  · exact B1977015
  · exact B1977019
  · exact B1977023
  · exact B1977027
  · exact B1977031
  · exact B1977035
  · exact B1977039
  · exact B1977043
  · exact B1977047
  · exact B1977051
  · exact B1977055
  · exact B1977059
  · exact B1977063
  · exact B1977067
  · exact B1977071
  · exact B1977075
  · exact B1977079
  · exact B1977083
  · exact B1977087
  · exact B1977091
  · exact B1977095
  · exact B1977099
  · exact B1977103
  · exact B1977107
  · exact B1977111
  · exact B1977115
  · exact B1977119
  · exact B1977123
  · exact B1977127
  · exact B1977131
  · exact B1977135
  · exact B1977139
  · exact B1977143
  · exact B1977147
  · exact B1977151
  · exact B1977155
  · exact B1977159
  · exact B1977163
  · exact B1977167
  · exact B1977171
  · exact B1977175
  · exact B1977179
  · exact B1977183
  · exact B1977187
  · exact B1977191
  · exact B1977195
  · exact B1977199
  · exact B1977203
  · exact B1977207
  · exact B1977211
  · exact B1977215
  · exact B1977219
  · exact B1977223
  · exact B1977227
  · exact B1977231
  · exact B1977235
  · exact B1977239
  · exact B1977243
  · exact B1977247
  · exact B1977251
  · exact B1977255
  · exact B1977259
  · exact B1977263
  · exact B1977267
  · exact B1977271
  · exact B1977275
  · exact B1977279
  · exact B1977283
  · exact B1977287
  · exact B1977291
  · exact B1977295
  · exact B1977299
  · exact B1977303
  · exact B1977307
  · exact B1977311
  · exact B1977315
  · exact B1977319
  · exact B1977323
  · exact B1977327
  · exact B1977331
  · exact B1977335
  · exact B1977339
  · exact B1977343
  · exact B1977347
  · exact B1977351
  · exact B1977355
  · exact B1977359
  · exact B1977363
  · exact B1977367
  · exact B1977371
  · exact B1977375
  · exact B1977379
  · exact B1977383
  · exact B1977387
  · exact B1977391
  · exact B1977395
  · exact B1977399
  · exact B1977403
  · exact B1977407
  · exact B1977411
  · exact B1977415
  · exact B1977419
  · exact B1977423
  · exact B1977427
  · exact B1977431
  · exact B1977435
theorem solution (m : ℕ) (hlo : 1975435 ≤ m) (hhi : m ≤ 1977435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 493858 ≤ j := by omega
    have hj2 : j ≤ 494358 := by omega
    have hb : Blo 1975435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
