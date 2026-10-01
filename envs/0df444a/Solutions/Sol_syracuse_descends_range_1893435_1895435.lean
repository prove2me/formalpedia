-- Prove2me | solution 1 for syracuse_descends_range_1893435_1895435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:44.057236+00:00
-- url     : https://prove2.me/submissions/3af4b18f-6b74-468b-a6b7-c007d8091d4c

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

theorem B3195173 : Blo 1893435 3195173 := bbase (se 4 (by rfl) ⟨299547, by rfl⟩ : syracuseStep 3195173 = 599095) (by norm_num)
theorem B2130115 : Blo 1893435 2130115 := bstep (se 1 (by rfl) ⟨1597586, by rfl⟩ : syracuseStep 2130115 = 3195173) B3195173
theorem B2840153 : Blo 1893435 2840153 := bstep (se 2 (by rfl) ⟨1065057, by rfl⟩ : syracuseStep 2840153 = 2130115) B2130115
theorem B1893435 : Blo 1893435 1893435 := bstep (se 1 (by rfl) ⟨1420076, by rfl⟩ : syracuseStep 1893435 = 2840153) B2840153
theorem B2695933 : Blo 1893435 2695933 := bbase (se 3 (by rfl) ⟨505487, by rfl⟩ : syracuseStep 2695933 = 1010975) (by norm_num)
theorem B14378309 : Blo 1893435 14378309 := bstep (se 4 (by rfl) ⟨1347966, by rfl⟩ : syracuseStep 14378309 = 2695933) B2695933
theorem B9585539 : Blo 1893435 9585539 := bstep (se 1 (by rfl) ⟨7189154, by rfl⟩ : syracuseStep 9585539 = 14378309) B14378309
theorem B6390359 : Blo 1893435 6390359 := bstep (se 1 (by rfl) ⟨4792769, by rfl⟩ : syracuseStep 6390359 = 9585539) B9585539
theorem B4260239 : Blo 1893435 4260239 := bstep (se 1 (by rfl) ⟨3195179, by rfl⟩ : syracuseStep 4260239 = 6390359) B6390359
theorem B2840159 : Blo 1893435 2840159 := bstep (se 1 (by rfl) ⟨2130119, by rfl⟩ : syracuseStep 2840159 = 4260239) B4260239
theorem B1893439 : Blo 1893435 1893439 := bstep (se 1 (by rfl) ⟨1420079, by rfl⟩ : syracuseStep 1893439 = 2840159) B2840159
theorem B2840165 : Blo 1893435 2840165 := bbase (se 4 (by rfl) ⟨266265, by rfl⟩ : syracuseStep 2840165 = 532531) (by norm_num)
theorem B1893443 : Blo 1893435 1893443 := bstep (se 1 (by rfl) ⟨1420082, by rfl⟩ : syracuseStep 1893443 = 2840165) B2840165
theorem B3838565 : Blo 1893435 3838565 := bbase (se 4 (by rfl) ⟨359865, by rfl⟩ : syracuseStep 3838565 = 719731) (by norm_num)
theorem B2559043 : Blo 1893435 2559043 := bstep (se 1 (by rfl) ⟨1919282, by rfl⟩ : syracuseStep 2559043 = 3838565) B3838565
theorem B3412057 : Blo 1893435 3412057 := bstep (se 2 (by rfl) ⟨1279521, by rfl⟩ : syracuseStep 3412057 = 2559043) B2559043
theorem B4549409 : Blo 1893435 4549409 := bstep (se 2 (by rfl) ⟨1706028, by rfl⟩ : syracuseStep 4549409 = 3412057) B3412057
theorem B3032939 : Blo 1893435 3032939 := bstep (se 1 (by rfl) ⟨2274704, by rfl⟩ : syracuseStep 3032939 = 4549409) B4549409
theorem B2021959 : Blo 1893435 2021959 := bstep (se 1 (by rfl) ⟨1516469, by rfl⟩ : syracuseStep 2021959 = 3032939) B3032939
theorem B2695945 : Blo 1893435 2695945 := bstep (se 2 (by rfl) ⟨1010979, by rfl⟩ : syracuseStep 2695945 = 2021959) B2021959
theorem B3594593 : Blo 1893435 3594593 := bstep (se 2 (by rfl) ⟨1347972, by rfl⟩ : syracuseStep 3594593 = 2695945) B2695945
theorem B2396395 : Blo 1893435 2396395 := bstep (se 1 (by rfl) ⟨1797296, by rfl⟩ : syracuseStep 2396395 = 3594593) B3594593
theorem B3195193 : Blo 1893435 3195193 := bstep (se 2 (by rfl) ⟨1198197, by rfl⟩ : syracuseStep 3195193 = 2396395) B2396395
theorem B4260257 : Blo 1893435 4260257 := bstep (se 2 (by rfl) ⟨1597596, by rfl⟩ : syracuseStep 4260257 = 3195193) B3195193
theorem B2840171 : Blo 1893435 2840171 := bstep (se 1 (by rfl) ⟨2130128, by rfl⟩ : syracuseStep 2840171 = 4260257) B4260257
theorem B1893447 : Blo 1893435 1893447 := bstep (se 1 (by rfl) ⟨1420085, by rfl⟩ : syracuseStep 1893447 = 2840171) B2840171
theorem B2130133 : Blo 1893435 2130133 := bbase (se 7 (by rfl) ⟨24962, by rfl⟩ : syracuseStep 2130133 = 49925) (by norm_num)
theorem B2840177 : Blo 1893435 2840177 := bstep (se 2 (by rfl) ⟨1065066, by rfl⟩ : syracuseStep 2840177 = 2130133) B2130133
theorem B1893451 : Blo 1893435 1893451 := bstep (se 1 (by rfl) ⟨1420088, by rfl⟩ : syracuseStep 1893451 = 2840177) B2840177
theorem B2396405 : Blo 1893435 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B6390413 : Blo 1893435 6390413 := bstep (se 3 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 6390413 = 2396405) B2396405
theorem B4260275 : Blo 1893435 4260275 := bstep (se 1 (by rfl) ⟨3195206, by rfl⟩ : syracuseStep 4260275 = 6390413) B6390413
theorem B2840183 : Blo 1893435 2840183 := bstep (se 1 (by rfl) ⟨2130137, by rfl⟩ : syracuseStep 2840183 = 4260275) B4260275
theorem B1893455 : Blo 1893435 1893455 := bstep (se 1 (by rfl) ⟨1420091, by rfl⟩ : syracuseStep 1893455 = 2840183) B2840183
theorem B2840189 : Blo 1893435 2840189 := bbase (se 3 (by rfl) ⟨532535, by rfl⟩ : syracuseStep 2840189 = 1065071) (by norm_num)
theorem B1893459 : Blo 1893435 1893459 := bstep (se 1 (by rfl) ⟨1420094, by rfl⟩ : syracuseStep 1893459 = 2840189) B2840189
theorem B4260293 : Blo 1893435 4260293 := bbase (se 4 (by rfl) ⟨399402, by rfl⟩ : syracuseStep 4260293 = 798805) (by norm_num)
theorem B2840195 : Blo 1893435 2840195 := bstep (se 1 (by rfl) ⟨2130146, by rfl⟩ : syracuseStep 2840195 = 4260293) B4260293
theorem B1893463 : Blo 1893435 1893463 := bstep (se 1 (by rfl) ⟨1420097, by rfl⟩ : syracuseStep 1893463 = 2840195) B2840195
theorem B6065941 : Blo 1893435 6065941 := bbase (se 6 (by rfl) ⟨142170, by rfl⟩ : syracuseStep 6065941 = 284341) (by norm_num)
theorem B8087921 : Blo 1893435 8087921 := bstep (se 2 (by rfl) ⟨3032970, by rfl⟩ : syracuseStep 8087921 = 6065941) B6065941
theorem B5391947 : Blo 1893435 5391947 := bstep (se 1 (by rfl) ⟨4043960, by rfl⟩ : syracuseStep 5391947 = 8087921) B8087921
theorem B3594631 : Blo 1893435 3594631 := bstep (se 1 (by rfl) ⟨2695973, by rfl⟩ : syracuseStep 3594631 = 5391947) B5391947
theorem B4792841 : Blo 1893435 4792841 := bstep (se 2 (by rfl) ⟨1797315, by rfl⟩ : syracuseStep 4792841 = 3594631) B3594631
theorem B3195227 : Blo 1893435 3195227 := bstep (se 1 (by rfl) ⟨2396420, by rfl⟩ : syracuseStep 3195227 = 4792841) B4792841
theorem B2130151 : Blo 1893435 2130151 := bstep (se 1 (by rfl) ⟨1597613, by rfl⟩ : syracuseStep 2130151 = 3195227) B3195227
theorem B2840201 : Blo 1893435 2840201 := bstep (se 2 (by rfl) ⟨1065075, by rfl⟩ : syracuseStep 2840201 = 2130151) B2130151
theorem B1893467 : Blo 1893435 1893467 := bstep (se 1 (by rfl) ⟨1420100, by rfl⟩ : syracuseStep 1893467 = 2840201) B2840201
theorem B9585701 : Blo 1893435 9585701 := bbase (se 4 (by rfl) ⟨898659, by rfl⟩ : syracuseStep 9585701 = 1797319) (by norm_num)
theorem B6390467 : Blo 1893435 6390467 := bstep (se 1 (by rfl) ⟨4792850, by rfl⟩ : syracuseStep 6390467 = 9585701) B9585701
theorem B4260311 : Blo 1893435 4260311 := bstep (se 1 (by rfl) ⟨3195233, by rfl⟩ : syracuseStep 4260311 = 6390467) B6390467
theorem B2840207 : Blo 1893435 2840207 := bstep (se 1 (by rfl) ⟨2130155, by rfl⟩ : syracuseStep 2840207 = 4260311) B4260311
theorem B1893471 : Blo 1893435 1893471 := bstep (se 1 (by rfl) ⟨1420103, by rfl⟩ : syracuseStep 1893471 = 2840207) B2840207
theorem B2840213 : Blo 1893435 2840213 := bbase (se 6 (by rfl) ⟨66567, by rfl⟩ : syracuseStep 2840213 = 133135) (by norm_num)
theorem B1893475 : Blo 1893435 1893475 := bstep (se 1 (by rfl) ⟨1420106, by rfl⟩ : syracuseStep 1893475 = 2840213) B2840213
theorem B12131957 : Blo 1893435 12131957 := bbase (se 5 (by rfl) ⟨568685, by rfl⟩ : syracuseStep 12131957 = 1137371) (by norm_num)
theorem B8087971 : Blo 1893435 8087971 := bstep (se 1 (by rfl) ⟨6065978, by rfl⟩ : syracuseStep 8087971 = 12131957) B12131957
theorem B10783961 : Blo 1893435 10783961 := bstep (se 2 (by rfl) ⟨4043985, by rfl⟩ : syracuseStep 10783961 = 8087971) B8087971
theorem B7189307 : Blo 1893435 7189307 := bstep (se 1 (by rfl) ⟨5391980, by rfl⟩ : syracuseStep 7189307 = 10783961) B10783961
theorem B4792871 : Blo 1893435 4792871 := bstep (se 1 (by rfl) ⟨3594653, by rfl⟩ : syracuseStep 4792871 = 7189307) B7189307
theorem B3195247 : Blo 1893435 3195247 := bstep (se 1 (by rfl) ⟨2396435, by rfl⟩ : syracuseStep 3195247 = 4792871) B4792871
theorem B4260329 : Blo 1893435 4260329 := bstep (se 2 (by rfl) ⟨1597623, by rfl⟩ : syracuseStep 4260329 = 3195247) B3195247
theorem B2840219 : Blo 1893435 2840219 := bstep (se 1 (by rfl) ⟨2130164, by rfl⟩ : syracuseStep 2840219 = 4260329) B4260329
theorem B1893479 : Blo 1893435 1893479 := bstep (se 1 (by rfl) ⟨1420109, by rfl⟩ : syracuseStep 1893479 = 2840219) B2840219
theorem B2130169 : Blo 1893435 2130169 := bbase (se 2 (by rfl) ⟨798813, by rfl⟩ : syracuseStep 2130169 = 1597627) (by norm_num)
theorem B2840225 : Blo 1893435 2840225 := bstep (se 2 (by rfl) ⟨1065084, by rfl⟩ : syracuseStep 2840225 = 2130169) B2130169
theorem B1893483 : Blo 1893435 1893483 := bstep (se 1 (by rfl) ⟨1420112, by rfl⟩ : syracuseStep 1893483 = 2840225) B2840225
theorem B8088005 : Blo 1893435 8088005 := bbase (se 4 (by rfl) ⟨758250, by rfl⟩ : syracuseStep 8088005 = 1516501) (by norm_num)
theorem B5392003 : Blo 1893435 5392003 := bstep (se 1 (by rfl) ⟨4044002, by rfl⟩ : syracuseStep 5392003 = 8088005) B8088005
theorem B7189337 : Blo 1893435 7189337 := bstep (se 2 (by rfl) ⟨2696001, by rfl⟩ : syracuseStep 7189337 = 5392003) B5392003
theorem B4792891 : Blo 1893435 4792891 := bstep (se 1 (by rfl) ⟨3594668, by rfl⟩ : syracuseStep 4792891 = 7189337) B7189337
theorem B6390521 : Blo 1893435 6390521 := bstep (se 2 (by rfl) ⟨2396445, by rfl⟩ : syracuseStep 6390521 = 4792891) B4792891
theorem B4260347 : Blo 1893435 4260347 := bstep (se 1 (by rfl) ⟨3195260, by rfl⟩ : syracuseStep 4260347 = 6390521) B6390521
theorem B2840231 : Blo 1893435 2840231 := bstep (se 1 (by rfl) ⟨2130173, by rfl⟩ : syracuseStep 2840231 = 4260347) B4260347
theorem B1893487 : Blo 1893435 1893487 := bstep (se 1 (by rfl) ⟨1420115, by rfl⟩ : syracuseStep 1893487 = 2840231) B2840231
theorem B2840237 : Blo 1893435 2840237 := bbase (se 3 (by rfl) ⟨532544, by rfl⟩ : syracuseStep 2840237 = 1065089) (by norm_num)
theorem B1893491 : Blo 1893435 1893491 := bstep (se 1 (by rfl) ⟨1420118, by rfl⟩ : syracuseStep 1893491 = 2840237) B2840237
theorem B4260365 : Blo 1893435 4260365 := bbase (se 3 (by rfl) ⟨798818, by rfl⟩ : syracuseStep 4260365 = 1597637) (by norm_num)
theorem B2840243 : Blo 1893435 2840243 := bstep (se 1 (by rfl) ⟨2130182, by rfl⟩ : syracuseStep 2840243 = 4260365) B4260365
theorem B1893495 : Blo 1893435 1893495 := bstep (se 1 (by rfl) ⟨1420121, by rfl⟩ : syracuseStep 1893495 = 2840243) B2840243
theorem B2396461 : Blo 1893435 2396461 := bbase (se 3 (by rfl) ⟨449336, by rfl⟩ : syracuseStep 2396461 = 898673) (by norm_num)
theorem B3195281 : Blo 1893435 3195281 := bstep (se 2 (by rfl) ⟨1198230, by rfl⟩ : syracuseStep 3195281 = 2396461) B2396461
theorem B2130187 : Blo 1893435 2130187 := bstep (se 1 (by rfl) ⟨1597640, by rfl⟩ : syracuseStep 2130187 = 3195281) B3195281
theorem B2840249 : Blo 1893435 2840249 := bstep (se 2 (by rfl) ⟨1065093, by rfl⟩ : syracuseStep 2840249 = 2130187) B2130187
theorem B1893499 : Blo 1893435 1893499 := bstep (se 1 (by rfl) ⟨1420124, by rfl⟩ : syracuseStep 1893499 = 2840249) B2840249
theorem B4549541 : Blo 1893435 4549541 := bbase (se 4 (by rfl) ⟨426519, by rfl⟩ : syracuseStep 4549541 = 853039) (by norm_num)
theorem B12132109 : Blo 1893435 12132109 := bstep (se 3 (by rfl) ⟨2274770, by rfl⟩ : syracuseStep 12132109 = 4549541) B4549541
theorem B16176145 : Blo 1893435 16176145 := bstep (se 2 (by rfl) ⟨6066054, by rfl⟩ : syracuseStep 16176145 = 12132109) B12132109
theorem B21568193 : Blo 1893435 21568193 := bstep (se 2 (by rfl) ⟨8088072, by rfl⟩ : syracuseStep 21568193 = 16176145) B16176145
theorem B14378795 : Blo 1893435 14378795 := bstep (se 1 (by rfl) ⟨10784096, by rfl⟩ : syracuseStep 14378795 = 21568193) B21568193
theorem B9585863 : Blo 1893435 9585863 := bstep (se 1 (by rfl) ⟨7189397, by rfl⟩ : syracuseStep 9585863 = 14378795) B14378795
theorem B6390575 : Blo 1893435 6390575 := bstep (se 1 (by rfl) ⟨4792931, by rfl⟩ : syracuseStep 6390575 = 9585863) B9585863
theorem B4260383 : Blo 1893435 4260383 := bstep (se 1 (by rfl) ⟨3195287, by rfl⟩ : syracuseStep 4260383 = 6390575) B6390575
theorem B2840255 : Blo 1893435 2840255 := bstep (se 1 (by rfl) ⟨2130191, by rfl⟩ : syracuseStep 2840255 = 4260383) B4260383
theorem B1893503 : Blo 1893435 1893503 := bstep (se 1 (by rfl) ⟨1420127, by rfl⟩ : syracuseStep 1893503 = 2840255) B2840255
theorem B2840261 : Blo 1893435 2840261 := bbase (se 4 (by rfl) ⟨266274, by rfl⟩ : syracuseStep 2840261 = 532549) (by norm_num)
theorem B1893507 : Blo 1893435 1893507 := bstep (se 1 (by rfl) ⟨1420130, by rfl⟩ : syracuseStep 1893507 = 2840261) B2840261
theorem B3195301 : Blo 1893435 3195301 := bbase (se 4 (by rfl) ⟨299559, by rfl⟩ : syracuseStep 3195301 = 599119) (by norm_num)
theorem B4260401 : Blo 1893435 4260401 := bstep (se 2 (by rfl) ⟨1597650, by rfl⟩ : syracuseStep 4260401 = 3195301) B3195301
theorem B2840267 : Blo 1893435 2840267 := bstep (se 1 (by rfl) ⟨2130200, by rfl⟩ : syracuseStep 2840267 = 4260401) B4260401
theorem B1893511 : Blo 1893435 1893511 := bstep (se 1 (by rfl) ⟨1420133, by rfl⟩ : syracuseStep 1893511 = 2840267) B2840267
theorem B2130205 : Blo 1893435 2130205 := bbase (se 3 (by rfl) ⟨399413, by rfl⟩ : syracuseStep 2130205 = 798827) (by norm_num)
theorem B2840273 : Blo 1893435 2840273 := bstep (se 2 (by rfl) ⟨1065102, by rfl⟩ : syracuseStep 2840273 = 2130205) B2130205
theorem B1893515 : Blo 1893435 1893515 := bstep (se 1 (by rfl) ⟨1420136, by rfl⟩ : syracuseStep 1893515 = 2840273) B2840273
theorem B6390629 : Blo 1893435 6390629 := bbase (se 4 (by rfl) ⟨599121, by rfl⟩ : syracuseStep 6390629 = 1198243) (by norm_num)
theorem B4260419 : Blo 1893435 4260419 := bstep (se 1 (by rfl) ⟨3195314, by rfl⟩ : syracuseStep 4260419 = 6390629) B6390629
theorem B2840279 : Blo 1893435 2840279 := bstep (se 1 (by rfl) ⟨2130209, by rfl⟩ : syracuseStep 2840279 = 4260419) B4260419
theorem B1893519 : Blo 1893435 1893519 := bstep (se 1 (by rfl) ⟨1420139, by rfl⟩ : syracuseStep 1893519 = 2840279) B2840279
theorem B2840285 : Blo 1893435 2840285 := bbase (se 3 (by rfl) ⟨532553, by rfl⟩ : syracuseStep 2840285 = 1065107) (by norm_num)
theorem B1893523 : Blo 1893435 1893523 := bstep (se 1 (by rfl) ⟨1420142, by rfl⟩ : syracuseStep 1893523 = 2840285) B2840285
theorem B4260437 : Blo 1893435 4260437 := bbase (se 8 (by rfl) ⟨24963, by rfl⟩ : syracuseStep 4260437 = 49927) (by norm_num)
theorem B2840291 : Blo 1893435 2840291 := bstep (se 1 (by rfl) ⟨2130218, by rfl⟩ : syracuseStep 2840291 = 4260437) B4260437
theorem B1893527 : Blo 1893435 1893527 := bstep (se 1 (by rfl) ⟨1420145, by rfl⟩ : syracuseStep 1893527 = 2840291) B2840291
theorem B2274805 : Blo 1893435 2274805 := bbase (se 5 (by rfl) ⟨106631, by rfl⟩ : syracuseStep 2274805 = 213263) (by norm_num)
theorem B3033073 : Blo 1893435 3033073 := bstep (se 2 (by rfl) ⟨1137402, by rfl⟩ : syracuseStep 3033073 = 2274805) B2274805
theorem B4044097 : Blo 1893435 4044097 := bstep (se 2 (by rfl) ⟨1516536, by rfl⟩ : syracuseStep 4044097 = 3033073) B3033073
theorem B5392129 : Blo 1893435 5392129 := bstep (se 2 (by rfl) ⟨2022048, by rfl⟩ : syracuseStep 5392129 = 4044097) B4044097
theorem B7189505 : Blo 1893435 7189505 := bstep (se 2 (by rfl) ⟨2696064, by rfl⟩ : syracuseStep 7189505 = 5392129) B5392129
theorem B4793003 : Blo 1893435 4793003 := bstep (se 1 (by rfl) ⟨3594752, by rfl⟩ : syracuseStep 4793003 = 7189505) B7189505
theorem B3195335 : Blo 1893435 3195335 := bstep (se 1 (by rfl) ⟨2396501, by rfl⟩ : syracuseStep 3195335 = 4793003) B4793003
theorem B2130223 : Blo 1893435 2130223 := bstep (se 1 (by rfl) ⟨1597667, by rfl⟩ : syracuseStep 2130223 = 3195335) B3195335
theorem B2840297 : Blo 1893435 2840297 := bstep (se 2 (by rfl) ⟨1065111, by rfl⟩ : syracuseStep 2840297 = 2130223) B2130223
theorem B1893531 : Blo 1893435 1893531 := bstep (se 1 (by rfl) ⟨1420148, by rfl⟩ : syracuseStep 1893531 = 2840297) B2840297
theorem B2274809 : Blo 1893435 2274809 := bbase (se 2 (by rfl) ⟨853053, by rfl⟩ : syracuseStep 2274809 = 1706107) (by norm_num)
theorem B24264629 : Blo 1893435 24264629 := bstep (se 5 (by rfl) ⟨1137404, by rfl⟩ : syracuseStep 24264629 = 2274809) B2274809
theorem B16176419 : Blo 1893435 16176419 := bstep (se 1 (by rfl) ⟨12132314, by rfl⟩ : syracuseStep 16176419 = 24264629) B24264629
theorem B10784279 : Blo 1893435 10784279 := bstep (se 1 (by rfl) ⟨8088209, by rfl⟩ : syracuseStep 10784279 = 16176419) B16176419
theorem B7189519 : Blo 1893435 7189519 := bstep (se 1 (by rfl) ⟨5392139, by rfl⟩ : syracuseStep 7189519 = 10784279) B10784279
theorem B9586025 : Blo 1893435 9586025 := bstep (se 2 (by rfl) ⟨3594759, by rfl⟩ : syracuseStep 9586025 = 7189519) B7189519
theorem B6390683 : Blo 1893435 6390683 := bstep (se 1 (by rfl) ⟨4793012, by rfl⟩ : syracuseStep 6390683 = 9586025) B9586025
theorem B4260455 : Blo 1893435 4260455 := bstep (se 1 (by rfl) ⟨3195341, by rfl⟩ : syracuseStep 4260455 = 6390683) B6390683
theorem B2840303 : Blo 1893435 2840303 := bstep (se 1 (by rfl) ⟨2130227, by rfl⟩ : syracuseStep 2840303 = 4260455) B4260455
theorem B1893535 : Blo 1893435 1893535 := bstep (se 1 (by rfl) ⟨1420151, by rfl⟩ : syracuseStep 1893535 = 2840303) B2840303
theorem B2840309 : Blo 1893435 2840309 := bbase (se 5 (by rfl) ⟨133139, by rfl⟩ : syracuseStep 2840309 = 266279) (by norm_num)
theorem B1893539 : Blo 1893435 1893539 := bstep (se 1 (by rfl) ⟨1420154, by rfl⟩ : syracuseStep 1893539 = 2840309) B2840309
theorem B8088245 : Blo 1893435 8088245 := bbase (se 5 (by rfl) ⟨379136, by rfl⟩ : syracuseStep 8088245 = 758273) (by norm_num)
theorem B5392163 : Blo 1893435 5392163 := bstep (se 1 (by rfl) ⟨4044122, by rfl⟩ : syracuseStep 5392163 = 8088245) B8088245
theorem B3594775 : Blo 1893435 3594775 := bstep (se 1 (by rfl) ⟨2696081, by rfl⟩ : syracuseStep 3594775 = 5392163) B5392163
theorem B4793033 : Blo 1893435 4793033 := bstep (se 2 (by rfl) ⟨1797387, by rfl⟩ : syracuseStep 4793033 = 3594775) B3594775
theorem B3195355 : Blo 1893435 3195355 := bstep (se 1 (by rfl) ⟨2396516, by rfl⟩ : syracuseStep 3195355 = 4793033) B4793033
theorem B4260473 : Blo 1893435 4260473 := bstep (se 2 (by rfl) ⟨1597677, by rfl⟩ : syracuseStep 4260473 = 3195355) B3195355
theorem B2840315 : Blo 1893435 2840315 := bstep (se 1 (by rfl) ⟨2130236, by rfl⟩ : syracuseStep 2840315 = 4260473) B4260473
theorem B1893543 : Blo 1893435 1893543 := bstep (se 1 (by rfl) ⟨1420157, by rfl⟩ : syracuseStep 1893543 = 2840315) B2840315
theorem B2130241 : Blo 1893435 2130241 := bbase (se 2 (by rfl) ⟨798840, by rfl⟩ : syracuseStep 2130241 = 1597681) (by norm_num)
theorem B2840321 : Blo 1893435 2840321 := bstep (se 2 (by rfl) ⟨1065120, by rfl⟩ : syracuseStep 2840321 = 2130241) B2130241
theorem B1893547 : Blo 1893435 1893547 := bstep (se 1 (by rfl) ⟨1420160, by rfl⟩ : syracuseStep 1893547 = 2840321) B2840321
theorem B4793053 : Blo 1893435 4793053 := bbase (se 3 (by rfl) ⟨898697, by rfl⟩ : syracuseStep 4793053 = 1797395) (by norm_num)
theorem B6390737 : Blo 1893435 6390737 := bstep (se 2 (by rfl) ⟨2396526, by rfl⟩ : syracuseStep 6390737 = 4793053) B4793053
theorem B4260491 : Blo 1893435 4260491 := bstep (se 1 (by rfl) ⟨3195368, by rfl⟩ : syracuseStep 4260491 = 6390737) B6390737
theorem B2840327 : Blo 1893435 2840327 := bstep (se 1 (by rfl) ⟨2130245, by rfl⟩ : syracuseStep 2840327 = 4260491) B4260491
theorem B1893551 : Blo 1893435 1893551 := bstep (se 1 (by rfl) ⟨1420163, by rfl⟩ : syracuseStep 1893551 = 2840327) B2840327
theorem B2840333 : Blo 1893435 2840333 := bbase (se 3 (by rfl) ⟨532562, by rfl⟩ : syracuseStep 2840333 = 1065125) (by norm_num)
theorem B1893555 : Blo 1893435 1893555 := bstep (se 1 (by rfl) ⟨1420166, by rfl⟩ : syracuseStep 1893555 = 2840333) B2840333
theorem B4260509 : Blo 1893435 4260509 := bbase (se 3 (by rfl) ⟨798845, by rfl⟩ : syracuseStep 4260509 = 1597691) (by norm_num)
theorem B2840339 : Blo 1893435 2840339 := bstep (se 1 (by rfl) ⟨2130254, by rfl⟩ : syracuseStep 2840339 = 4260509) B4260509
theorem B1893559 : Blo 1893435 1893559 := bstep (se 1 (by rfl) ⟨1420169, by rfl⟩ : syracuseStep 1893559 = 2840339) B2840339
theorem B3195389 : Blo 1893435 3195389 := bbase (se 3 (by rfl) ⟨599135, by rfl⟩ : syracuseStep 3195389 = 1198271) (by norm_num)
theorem B2130259 : Blo 1893435 2130259 := bstep (se 1 (by rfl) ⟨1597694, by rfl⟩ : syracuseStep 2130259 = 3195389) B3195389
theorem B2840345 : Blo 1893435 2840345 := bstep (se 2 (by rfl) ⟨1065129, by rfl⟩ : syracuseStep 2840345 = 2130259) B2130259
theorem B1893563 : Blo 1893435 1893563 := bstep (se 1 (by rfl) ⟨1420172, by rfl⟩ : syracuseStep 1893563 = 2840345) B2840345
theorem B4044173 : Blo 1893435 4044173 := bbase (se 3 (by rfl) ⟨758282, by rfl⟩ : syracuseStep 4044173 = 1516565) (by norm_num)
theorem B10784461 : Blo 1893435 10784461 := bstep (se 3 (by rfl) ⟨2022086, by rfl⟩ : syracuseStep 10784461 = 4044173) B4044173
theorem B14379281 : Blo 1893435 14379281 := bstep (se 2 (by rfl) ⟨5392230, by rfl⟩ : syracuseStep 14379281 = 10784461) B10784461
theorem B9586187 : Blo 1893435 9586187 := bstep (se 1 (by rfl) ⟨7189640, by rfl⟩ : syracuseStep 9586187 = 14379281) B14379281
theorem B6390791 : Blo 1893435 6390791 := bstep (se 1 (by rfl) ⟨4793093, by rfl⟩ : syracuseStep 6390791 = 9586187) B9586187
theorem B4260527 : Blo 1893435 4260527 := bstep (se 1 (by rfl) ⟨3195395, by rfl⟩ : syracuseStep 4260527 = 6390791) B6390791
theorem B2840351 : Blo 1893435 2840351 := bstep (se 1 (by rfl) ⟨2130263, by rfl⟩ : syracuseStep 2840351 = 4260527) B4260527
theorem B1893567 : Blo 1893435 1893567 := bstep (se 1 (by rfl) ⟨1420175, by rfl⟩ : syracuseStep 1893567 = 2840351) B2840351
theorem B2840357 : Blo 1893435 2840357 := bbase (se 4 (by rfl) ⟨266283, by rfl⟩ : syracuseStep 2840357 = 532567) (by norm_num)
theorem B1893571 : Blo 1893435 1893571 := bstep (se 1 (by rfl) ⟨1420178, by rfl⟩ : syracuseStep 1893571 = 2840357) B2840357
theorem B2396557 : Blo 1893435 2396557 := bbase (se 3 (by rfl) ⟨449354, by rfl⟩ : syracuseStep 2396557 = 898709) (by norm_num)
theorem B3195409 : Blo 1893435 3195409 := bstep (se 2 (by rfl) ⟨1198278, by rfl⟩ : syracuseStep 3195409 = 2396557) B2396557
theorem B4260545 : Blo 1893435 4260545 := bstep (se 2 (by rfl) ⟨1597704, by rfl⟩ : syracuseStep 4260545 = 3195409) B3195409
theorem B2840363 : Blo 1893435 2840363 := bstep (se 1 (by rfl) ⟨2130272, by rfl⟩ : syracuseStep 2840363 = 4260545) B4260545
theorem B1893575 : Blo 1893435 1893575 := bstep (se 1 (by rfl) ⟨1420181, by rfl⟩ : syracuseStep 1893575 = 2840363) B2840363
theorem B2130277 : Blo 1893435 2130277 := bbase (se 4 (by rfl) ⟨199713, by rfl⟩ : syracuseStep 2130277 = 399427) (by norm_num)
theorem B2840369 : Blo 1893435 2840369 := bstep (se 2 (by rfl) ⟨1065138, by rfl⟩ : syracuseStep 2840369 = 2130277) B2130277
theorem B1893579 : Blo 1893435 1893579 := bstep (se 1 (by rfl) ⟨1420184, by rfl⟩ : syracuseStep 1893579 = 2840369) B2840369
theorem B5392277 : Blo 1893435 5392277 := bbase (se 6 (by rfl) ⟨126381, by rfl⟩ : syracuseStep 5392277 = 252763) (by norm_num)
theorem B3594851 : Blo 1893435 3594851 := bstep (se 1 (by rfl) ⟨2696138, by rfl⟩ : syracuseStep 3594851 = 5392277) B5392277
theorem B2396567 : Blo 1893435 2396567 := bstep (se 1 (by rfl) ⟨1797425, by rfl⟩ : syracuseStep 2396567 = 3594851) B3594851
theorem B6390845 : Blo 1893435 6390845 := bstep (se 3 (by rfl) ⟨1198283, by rfl⟩ : syracuseStep 6390845 = 2396567) B2396567
theorem B4260563 : Blo 1893435 4260563 := bstep (se 1 (by rfl) ⟨3195422, by rfl⟩ : syracuseStep 4260563 = 6390845) B6390845
theorem B2840375 : Blo 1893435 2840375 := bstep (se 1 (by rfl) ⟨2130281, by rfl⟩ : syracuseStep 2840375 = 4260563) B4260563
theorem B1893583 : Blo 1893435 1893583 := bstep (se 1 (by rfl) ⟨1420187, by rfl⟩ : syracuseStep 1893583 = 2840375) B2840375
theorem B2840381 : Blo 1893435 2840381 := bbase (se 3 (by rfl) ⟨532571, by rfl⟩ : syracuseStep 2840381 = 1065143) (by norm_num)
theorem B1893587 : Blo 1893435 1893587 := bstep (se 1 (by rfl) ⟨1420190, by rfl⟩ : syracuseStep 1893587 = 2840381) B2840381
theorem B4260581 : Blo 1893435 4260581 := bbase (se 4 (by rfl) ⟨399429, by rfl⟩ : syracuseStep 4260581 = 798859) (by norm_num)
theorem B2840387 : Blo 1893435 2840387 := bstep (se 1 (by rfl) ⟨2130290, by rfl⟩ : syracuseStep 2840387 = 4260581) B4260581
theorem B1893591 : Blo 1893435 1893591 := bstep (se 1 (by rfl) ⟨1420193, by rfl⟩ : syracuseStep 1893591 = 2840387) B2840387
theorem B4793165 : Blo 1893435 4793165 := bbase (se 3 (by rfl) ⟨898718, by rfl⟩ : syracuseStep 4793165 = 1797437) (by norm_num)
theorem B3195443 : Blo 1893435 3195443 := bstep (se 1 (by rfl) ⟨2396582, by rfl⟩ : syracuseStep 3195443 = 4793165) B4793165
theorem B2130295 : Blo 1893435 2130295 := bstep (se 1 (by rfl) ⟨1597721, by rfl⟩ : syracuseStep 2130295 = 3195443) B3195443
theorem B2840393 : Blo 1893435 2840393 := bstep (se 2 (by rfl) ⟨1065147, by rfl⟩ : syracuseStep 2840393 = 2130295) B2130295
theorem B1893595 : Blo 1893435 1893595 := bstep (se 1 (by rfl) ⟨1420196, by rfl⟩ : syracuseStep 1893595 = 2840393) B2840393
theorem B2022121 : Blo 1893435 2022121 := bbase (se 2 (by rfl) ⟨758295, by rfl⟩ : syracuseStep 2022121 = 1516591) (by norm_num)
theorem B2696161 : Blo 1893435 2696161 := bstep (se 2 (by rfl) ⟨1011060, by rfl⟩ : syracuseStep 2696161 = 2022121) B2022121
theorem B3594881 : Blo 1893435 3594881 := bstep (se 2 (by rfl) ⟨1348080, by rfl⟩ : syracuseStep 3594881 = 2696161) B2696161
theorem B9586349 : Blo 1893435 9586349 := bstep (se 3 (by rfl) ⟨1797440, by rfl⟩ : syracuseStep 9586349 = 3594881) B3594881
theorem B6390899 : Blo 1893435 6390899 := bstep (se 1 (by rfl) ⟨4793174, by rfl⟩ : syracuseStep 6390899 = 9586349) B9586349
theorem B4260599 : Blo 1893435 4260599 := bstep (se 1 (by rfl) ⟨3195449, by rfl⟩ : syracuseStep 4260599 = 6390899) B6390899
theorem B2840399 : Blo 1893435 2840399 := bstep (se 1 (by rfl) ⟨2130299, by rfl⟩ : syracuseStep 2840399 = 4260599) B4260599
theorem B1893599 : Blo 1893435 1893599 := bstep (se 1 (by rfl) ⟨1420199, by rfl⟩ : syracuseStep 1893599 = 2840399) B2840399
theorem B2840405 : Blo 1893435 2840405 := bbase (se 9 (by rfl) ⟨8321, by rfl⟩ : syracuseStep 2840405 = 16643) (by norm_num)
theorem B1893603 : Blo 1893435 1893603 := bstep (se 1 (by rfl) ⟨1420202, by rfl⟩ : syracuseStep 1893603 = 2840405) B2840405
theorem B6066389 : Blo 1893435 6066389 := bbase (se 7 (by rfl) ⟨71090, by rfl⟩ : syracuseStep 6066389 = 142181) (by norm_num)
theorem B4044259 : Blo 1893435 4044259 := bstep (se 1 (by rfl) ⟨3033194, by rfl⟩ : syracuseStep 4044259 = 6066389) B6066389
theorem B5392345 : Blo 1893435 5392345 := bstep (se 2 (by rfl) ⟨2022129, by rfl⟩ : syracuseStep 5392345 = 4044259) B4044259
theorem B7189793 : Blo 1893435 7189793 := bstep (se 2 (by rfl) ⟨2696172, by rfl⟩ : syracuseStep 7189793 = 5392345) B5392345
theorem B4793195 : Blo 1893435 4793195 := bstep (se 1 (by rfl) ⟨3594896, by rfl⟩ : syracuseStep 4793195 = 7189793) B7189793
theorem B3195463 : Blo 1893435 3195463 := bstep (se 1 (by rfl) ⟨2396597, by rfl⟩ : syracuseStep 3195463 = 4793195) B4793195
theorem B4260617 : Blo 1893435 4260617 := bstep (se 2 (by rfl) ⟨1597731, by rfl⟩ : syracuseStep 4260617 = 3195463) B3195463
theorem B2840411 : Blo 1893435 2840411 := bstep (se 1 (by rfl) ⟨2130308, by rfl⟩ : syracuseStep 2840411 = 4260617) B4260617
theorem B1893607 : Blo 1893435 1893607 := bstep (se 1 (by rfl) ⟨1420205, by rfl⟩ : syracuseStep 1893607 = 2840411) B2840411
theorem B2130313 : Blo 1893435 2130313 := bbase (se 2 (by rfl) ⟨798867, by rfl⟩ : syracuseStep 2130313 = 1597735) (by norm_num)
theorem B2840417 : Blo 1893435 2840417 := bstep (se 2 (by rfl) ⟨1065156, by rfl⟩ : syracuseStep 2840417 = 2130313) B2130313
theorem B1893611 : Blo 1893435 1893611 := bstep (se 1 (by rfl) ⟨1420208, by rfl⟩ : syracuseStep 1893611 = 2840417) B2840417
theorem B4858613 : Blo 1893435 4858613 := bbase (se 5 (by rfl) ⟨227747, by rfl⟩ : syracuseStep 4858613 = 455495) (by norm_num)
theorem B3239075 : Blo 1893435 3239075 := bstep (se 1 (by rfl) ⟨2429306, by rfl⟩ : syracuseStep 3239075 = 4858613) B4858613
theorem B2159383 : Blo 1893435 2159383 := bstep (se 1 (by rfl) ⟨1619537, by rfl⟩ : syracuseStep 2159383 = 3239075) B3239075
theorem B2879177 : Blo 1893435 2879177 := bstep (se 2 (by rfl) ⟨1079691, by rfl⟩ : syracuseStep 2879177 = 2159383) B2159383
theorem B30711221 : Blo 1893435 30711221 := bstep (se 5 (by rfl) ⟨1439588, by rfl⟩ : syracuseStep 30711221 = 2879177) B2879177
theorem B20474147 : Blo 1893435 20474147 := bstep (se 1 (by rfl) ⟨15355610, by rfl⟩ : syracuseStep 20474147 = 30711221) B30711221
theorem B54597725 : Blo 1893435 54597725 := bstep (se 3 (by rfl) ⟨10237073, by rfl⟩ : syracuseStep 54597725 = 20474147) B20474147
theorem B36398483 : Blo 1893435 36398483 := bstep (se 1 (by rfl) ⟨27298862, by rfl⟩ : syracuseStep 36398483 = 54597725) B54597725
theorem B24265655 : Blo 1893435 24265655 := bstep (se 1 (by rfl) ⟨18199241, by rfl⟩ : syracuseStep 24265655 = 36398483) B36398483
theorem B16177103 : Blo 1893435 16177103 := bstep (se 1 (by rfl) ⟨12132827, by rfl⟩ : syracuseStep 16177103 = 24265655) B24265655
theorem B10784735 : Blo 1893435 10784735 := bstep (se 1 (by rfl) ⟨8088551, by rfl⟩ : syracuseStep 10784735 = 16177103) B16177103
theorem B7189823 : Blo 1893435 7189823 := bstep (se 1 (by rfl) ⟨5392367, by rfl⟩ : syracuseStep 7189823 = 10784735) B10784735
theorem B4793215 : Blo 1893435 4793215 := bstep (se 1 (by rfl) ⟨3594911, by rfl⟩ : syracuseStep 4793215 = 7189823) B7189823
theorem B6390953 : Blo 1893435 6390953 := bstep (se 2 (by rfl) ⟨2396607, by rfl⟩ : syracuseStep 6390953 = 4793215) B4793215
theorem B4260635 : Blo 1893435 4260635 := bstep (se 1 (by rfl) ⟨3195476, by rfl⟩ : syracuseStep 4260635 = 6390953) B6390953
theorem B2840423 : Blo 1893435 2840423 := bstep (se 1 (by rfl) ⟨2130317, by rfl⟩ : syracuseStep 2840423 = 4260635) B4260635
theorem B1893615 : Blo 1893435 1893615 := bstep (se 1 (by rfl) ⟨1420211, by rfl⟩ : syracuseStep 1893615 = 2840423) B2840423
theorem B2840429 : Blo 1893435 2840429 := bbase (se 3 (by rfl) ⟨532580, by rfl⟩ : syracuseStep 2840429 = 1065161) (by norm_num)
theorem B1893619 : Blo 1893435 1893619 := bstep (se 1 (by rfl) ⟨1420214, by rfl⟩ : syracuseStep 1893619 = 2840429) B2840429
theorem B4260653 : Blo 1893435 4260653 := bbase (se 3 (by rfl) ⟨798872, by rfl⟩ : syracuseStep 4260653 = 1597745) (by norm_num)
theorem B2840435 : Blo 1893435 2840435 := bstep (se 1 (by rfl) ⟨2130326, by rfl⟩ : syracuseStep 2840435 = 4260653) B4260653
theorem B1893623 : Blo 1893435 1893623 := bstep (se 1 (by rfl) ⟨1420217, by rfl⟩ : syracuseStep 1893623 = 2840435) B2840435
theorem B3412381 : Blo 1893435 3412381 := bbase (se 3 (by rfl) ⟨639821, by rfl⟩ : syracuseStep 3412381 = 1279643) (by norm_num)
theorem B4549841 : Blo 1893435 4549841 := bstep (se 2 (by rfl) ⟨1706190, by rfl⟩ : syracuseStep 4549841 = 3412381) B3412381
theorem B3033227 : Blo 1893435 3033227 := bstep (se 1 (by rfl) ⟨2274920, by rfl⟩ : syracuseStep 3033227 = 4549841) B4549841
theorem B8088605 : Blo 1893435 8088605 := bstep (se 3 (by rfl) ⟨1516613, by rfl⟩ : syracuseStep 8088605 = 3033227) B3033227
theorem B5392403 : Blo 1893435 5392403 := bstep (se 1 (by rfl) ⟨4044302, by rfl⟩ : syracuseStep 5392403 = 8088605) B8088605
theorem B3594935 : Blo 1893435 3594935 := bstep (se 1 (by rfl) ⟨2696201, by rfl⟩ : syracuseStep 3594935 = 5392403) B5392403
theorem B2396623 : Blo 1893435 2396623 := bstep (se 1 (by rfl) ⟨1797467, by rfl⟩ : syracuseStep 2396623 = 3594935) B3594935
theorem B3195497 : Blo 1893435 3195497 := bstep (se 2 (by rfl) ⟨1198311, by rfl⟩ : syracuseStep 3195497 = 2396623) B2396623
theorem B2130331 : Blo 1893435 2130331 := bstep (se 1 (by rfl) ⟨1597748, by rfl⟩ : syracuseStep 2130331 = 3195497) B3195497
theorem B2840441 : Blo 1893435 2840441 := bstep (se 2 (by rfl) ⟨1065165, by rfl⟩ : syracuseStep 2840441 = 2130331) B2130331
theorem B1893627 : Blo 1893435 1893627 := bstep (se 1 (by rfl) ⟨1420220, by rfl⟩ : syracuseStep 1893627 = 2840441) B2840441
theorem B6824773 : Blo 1893435 6824773 := bbase (se 4 (by rfl) ⟨639822, by rfl⟩ : syracuseStep 6824773 = 1279645) (by norm_num)
theorem B9099697 : Blo 1893435 9099697 := bstep (se 2 (by rfl) ⟨3412386, by rfl⟩ : syracuseStep 9099697 = 6824773) B6824773
theorem B12132929 : Blo 1893435 12132929 := bstep (se 2 (by rfl) ⟨4549848, by rfl⟩ : syracuseStep 12132929 = 9099697) B9099697
theorem B32354477 : Blo 1893435 32354477 := bstep (se 3 (by rfl) ⟨6066464, by rfl⟩ : syracuseStep 32354477 = 12132929) B12132929
theorem B21569651 : Blo 1893435 21569651 := bstep (se 1 (by rfl) ⟨16177238, by rfl⟩ : syracuseStep 21569651 = 32354477) B32354477
theorem B14379767 : Blo 1893435 14379767 := bstep (se 1 (by rfl) ⟨10784825, by rfl⟩ : syracuseStep 14379767 = 21569651) B21569651
theorem B9586511 : Blo 1893435 9586511 := bstep (se 1 (by rfl) ⟨7189883, by rfl⟩ : syracuseStep 9586511 = 14379767) B14379767
theorem B6391007 : Blo 1893435 6391007 := bstep (se 1 (by rfl) ⟨4793255, by rfl⟩ : syracuseStep 6391007 = 9586511) B9586511
theorem B4260671 : Blo 1893435 4260671 := bstep (se 1 (by rfl) ⟨3195503, by rfl⟩ : syracuseStep 4260671 = 6391007) B6391007
theorem B2840447 : Blo 1893435 2840447 := bstep (se 1 (by rfl) ⟨2130335, by rfl⟩ : syracuseStep 2840447 = 4260671) B4260671
theorem B1893631 : Blo 1893435 1893631 := bstep (se 1 (by rfl) ⟨1420223, by rfl⟩ : syracuseStep 1893631 = 2840447) B2840447
theorem B2840453 : Blo 1893435 2840453 := bbase (se 4 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 2840453 = 532585) (by norm_num)
theorem B1893635 : Blo 1893435 1893635 := bstep (se 1 (by rfl) ⟨1420226, by rfl⟩ : syracuseStep 1893635 = 2840453) B2840453
theorem B3195517 : Blo 1893435 3195517 := bbase (se 3 (by rfl) ⟨599159, by rfl⟩ : syracuseStep 3195517 = 1198319) (by norm_num)
theorem B4260689 : Blo 1893435 4260689 := bstep (se 2 (by rfl) ⟨1597758, by rfl⟩ : syracuseStep 4260689 = 3195517) B3195517
theorem B2840459 : Blo 1893435 2840459 := bstep (se 1 (by rfl) ⟨2130344, by rfl⟩ : syracuseStep 2840459 = 4260689) B4260689
theorem B1893639 : Blo 1893435 1893639 := bstep (se 1 (by rfl) ⟨1420229, by rfl⟩ : syracuseStep 1893639 = 2840459) B2840459
theorem B2130349 : Blo 1893435 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B2840465 : Blo 1893435 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B1893643 : Blo 1893435 1893643 := bstep (se 1 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 1893643 = 2840465) B2840465
theorem B6391061 : Blo 1893435 6391061 := bbase (se 6 (by rfl) ⟨149790, by rfl⟩ : syracuseStep 6391061 = 299581) (by norm_num)
theorem B4260707 : Blo 1893435 4260707 := bstep (se 1 (by rfl) ⟨3195530, by rfl⟩ : syracuseStep 4260707 = 6391061) B6391061
theorem B2840471 : Blo 1893435 2840471 := bstep (se 1 (by rfl) ⟨2130353, by rfl⟩ : syracuseStep 2840471 = 4260707) B4260707
theorem B1893647 : Blo 1893435 1893647 := bstep (se 1 (by rfl) ⟨1420235, by rfl⟩ : syracuseStep 1893647 = 2840471) B2840471
theorem B2840477 : Blo 1893435 2840477 := bbase (se 3 (by rfl) ⟨532589, by rfl⟩ : syracuseStep 2840477 = 1065179) (by norm_num)
theorem B1893651 : Blo 1893435 1893651 := bstep (se 1 (by rfl) ⟨1420238, by rfl⟩ : syracuseStep 1893651 = 2840477) B2840477
theorem B4260725 : Blo 1893435 4260725 := bbase (se 5 (by rfl) ⟨199721, by rfl⟩ : syracuseStep 4260725 = 399443) (by norm_num)
theorem B2840483 : Blo 1893435 2840483 := bstep (se 1 (by rfl) ⟨2130362, by rfl⟩ : syracuseStep 2840483 = 4260725) B4260725
theorem B1893655 : Blo 1893435 1893655 := bstep (se 1 (by rfl) ⟨1420241, by rfl⟩ : syracuseStep 1893655 = 2840483) B2840483
theorem B3644045 : Blo 1893435 3644045 := bbase (se 3 (by rfl) ⟨683258, by rfl⟩ : syracuseStep 3644045 = 1366517) (by norm_num)
theorem B2429363 : Blo 1893435 2429363 := bstep (se 1 (by rfl) ⟨1822022, by rfl⟩ : syracuseStep 2429363 = 3644045) B3644045
theorem B6478301 : Blo 1893435 6478301 := bstep (se 3 (by rfl) ⟨1214681, by rfl⟩ : syracuseStep 6478301 = 2429363) B2429363
theorem B4318867 : Blo 1893435 4318867 := bstep (se 1 (by rfl) ⟨3239150, by rfl⟩ : syracuseStep 4318867 = 6478301) B6478301
theorem B5758489 : Blo 1893435 5758489 := bstep (se 2 (by rfl) ⟨2159433, by rfl⟩ : syracuseStep 5758489 = 4318867) B4318867
theorem B7677985 : Blo 1893435 7677985 := bstep (se 2 (by rfl) ⟨2879244, by rfl⟩ : syracuseStep 7677985 = 5758489) B5758489
theorem B10237313 : Blo 1893435 10237313 := bstep (se 2 (by rfl) ⟨3838992, by rfl⟩ : syracuseStep 10237313 = 7677985) B7677985
theorem B27299501 : Blo 1893435 27299501 := bstep (se 3 (by rfl) ⟨5118656, by rfl⟩ : syracuseStep 27299501 = 10237313) B10237313
theorem B18199667 : Blo 1893435 18199667 := bstep (se 1 (by rfl) ⟨13649750, by rfl⟩ : syracuseStep 18199667 = 27299501) B27299501
theorem B12133111 : Blo 1893435 12133111 := bstep (se 1 (by rfl) ⟨9099833, by rfl⟩ : syracuseStep 12133111 = 18199667) B18199667
theorem B16177481 : Blo 1893435 16177481 := bstep (se 2 (by rfl) ⟨6066555, by rfl⟩ : syracuseStep 16177481 = 12133111) B12133111
theorem B10784987 : Blo 1893435 10784987 := bstep (se 1 (by rfl) ⟨8088740, by rfl⟩ : syracuseStep 10784987 = 16177481) B16177481
theorem B7189991 : Blo 1893435 7189991 := bstep (se 1 (by rfl) ⟨5392493, by rfl⟩ : syracuseStep 7189991 = 10784987) B10784987
theorem B4793327 : Blo 1893435 4793327 := bstep (se 1 (by rfl) ⟨3594995, by rfl⟩ : syracuseStep 4793327 = 7189991) B7189991
theorem B3195551 : Blo 1893435 3195551 := bstep (se 1 (by rfl) ⟨2396663, by rfl⟩ : syracuseStep 3195551 = 4793327) B4793327
theorem B2130367 : Blo 1893435 2130367 := bstep (se 1 (by rfl) ⟨1597775, by rfl⟩ : syracuseStep 2130367 = 3195551) B3195551
theorem B2840489 : Blo 1893435 2840489 := bstep (se 2 (by rfl) ⟨1065183, by rfl⟩ : syracuseStep 2840489 = 2130367) B2130367
theorem B1893659 : Blo 1893435 1893659 := bstep (se 1 (by rfl) ⟨1420244, by rfl⟩ : syracuseStep 1893659 = 2840489) B2840489
theorem B7190005 : Blo 1893435 7190005 := bbase (se 5 (by rfl) ⟨337031, by rfl⟩ : syracuseStep 7190005 = 674063) (by norm_num)
theorem B9586673 : Blo 1893435 9586673 := bstep (se 2 (by rfl) ⟨3595002, by rfl⟩ : syracuseStep 9586673 = 7190005) B7190005
theorem B6391115 : Blo 1893435 6391115 := bstep (se 1 (by rfl) ⟨4793336, by rfl⟩ : syracuseStep 6391115 = 9586673) B9586673
theorem B4260743 : Blo 1893435 4260743 := bstep (se 1 (by rfl) ⟨3195557, by rfl⟩ : syracuseStep 4260743 = 6391115) B6391115
theorem B2840495 : Blo 1893435 2840495 := bstep (se 1 (by rfl) ⟨2130371, by rfl⟩ : syracuseStep 2840495 = 4260743) B4260743
theorem B1893663 : Blo 1893435 1893663 := bstep (se 1 (by rfl) ⟨1420247, by rfl⟩ : syracuseStep 1893663 = 2840495) B2840495
theorem B2840501 : Blo 1893435 2840501 := bbase (se 5 (by rfl) ⟨133148, by rfl⟩ : syracuseStep 2840501 = 266297) (by norm_num)
theorem B1893667 : Blo 1893435 1893667 := bstep (se 1 (by rfl) ⟨1420250, by rfl⟩ : syracuseStep 1893667 = 2840501) B2840501
theorem B4793357 : Blo 1893435 4793357 := bbase (se 3 (by rfl) ⟨898754, by rfl⟩ : syracuseStep 4793357 = 1797509) (by norm_num)
theorem B3195571 : Blo 1893435 3195571 := bstep (se 1 (by rfl) ⟨2396678, by rfl⟩ : syracuseStep 3195571 = 4793357) B4793357
theorem B4260761 : Blo 1893435 4260761 := bstep (se 2 (by rfl) ⟨1597785, by rfl⟩ : syracuseStep 4260761 = 3195571) B3195571
theorem B2840507 : Blo 1893435 2840507 := bstep (se 1 (by rfl) ⟨2130380, by rfl⟩ : syracuseStep 2840507 = 4260761) B4260761
theorem B1893671 : Blo 1893435 1893671 := bstep (se 1 (by rfl) ⟨1420253, by rfl⟩ : syracuseStep 1893671 = 2840507) B2840507
theorem B2130385 : Blo 1893435 2130385 := bbase (se 2 (by rfl) ⟨798894, by rfl⟩ : syracuseStep 2130385 = 1597789) (by norm_num)
theorem B2840513 : Blo 1893435 2840513 := bstep (se 2 (by rfl) ⟨1065192, by rfl⟩ : syracuseStep 2840513 = 2130385) B2130385
theorem B1893675 : Blo 1893435 1893675 := bstep (se 1 (by rfl) ⟨1420256, by rfl⟩ : syracuseStep 1893675 = 2840513) B2840513
theorem B4044413 : Blo 1893435 4044413 := bbase (se 3 (by rfl) ⟨758327, by rfl⟩ : syracuseStep 4044413 = 1516655) (by norm_num)
theorem B2696275 : Blo 1893435 2696275 := bstep (se 1 (by rfl) ⟨2022206, by rfl⟩ : syracuseStep 2696275 = 4044413) B4044413
theorem B3595033 : Blo 1893435 3595033 := bstep (se 2 (by rfl) ⟨1348137, by rfl⟩ : syracuseStep 3595033 = 2696275) B2696275
theorem B4793377 : Blo 1893435 4793377 := bstep (se 2 (by rfl) ⟨1797516, by rfl⟩ : syracuseStep 4793377 = 3595033) B3595033
theorem B6391169 : Blo 1893435 6391169 := bstep (se 2 (by rfl) ⟨2396688, by rfl⟩ : syracuseStep 6391169 = 4793377) B4793377
theorem B4260779 : Blo 1893435 4260779 := bstep (se 1 (by rfl) ⟨3195584, by rfl⟩ : syracuseStep 4260779 = 6391169) B6391169
theorem B2840519 : Blo 1893435 2840519 := bstep (se 1 (by rfl) ⟨2130389, by rfl⟩ : syracuseStep 2840519 = 4260779) B4260779
theorem B1893679 : Blo 1893435 1893679 := bstep (se 1 (by rfl) ⟨1420259, by rfl⟩ : syracuseStep 1893679 = 2840519) B2840519
theorem B2840525 : Blo 1893435 2840525 := bbase (se 3 (by rfl) ⟨532598, by rfl⟩ : syracuseStep 2840525 = 1065197) (by norm_num)
theorem B1893683 : Blo 1893435 1893683 := bstep (se 1 (by rfl) ⟨1420262, by rfl⟩ : syracuseStep 1893683 = 2840525) B2840525
theorem B4260797 : Blo 1893435 4260797 := bbase (se 3 (by rfl) ⟨798899, by rfl⟩ : syracuseStep 4260797 = 1597799) (by norm_num)
theorem B2840531 : Blo 1893435 2840531 := bstep (se 1 (by rfl) ⟨2130398, by rfl⟩ : syracuseStep 2840531 = 4260797) B4260797
theorem B1893687 : Blo 1893435 1893687 := bstep (se 1 (by rfl) ⟨1420265, by rfl⟩ : syracuseStep 1893687 = 2840531) B2840531
theorem B3195605 : Blo 1893435 3195605 := bbase (se 7 (by rfl) ⟨37448, by rfl⟩ : syracuseStep 3195605 = 74897) (by norm_num)
theorem B2130403 : Blo 1893435 2130403 := bstep (se 1 (by rfl) ⟨1597802, by rfl⟩ : syracuseStep 2130403 = 3195605) B3195605
theorem B2840537 : Blo 1893435 2840537 := bstep (se 2 (by rfl) ⟨1065201, by rfl⟩ : syracuseStep 2840537 = 2130403) B2130403
theorem B1893691 : Blo 1893435 1893691 := bstep (se 1 (by rfl) ⟨1420268, by rfl⟩ : syracuseStep 1893691 = 2840537) B2840537
theorem B1919533 : Blo 1893435 1919533 := bbase (se 3 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 1919533 = 719825) (by norm_num)
theorem B2559377 : Blo 1893435 2559377 := bstep (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) B1919533
theorem B6825005 : Blo 1893435 6825005 := bstep (se 3 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 6825005 = 2559377) B2559377
theorem B4550003 : Blo 1893435 4550003 := bstep (se 1 (by rfl) ⟨3412502, by rfl⟩ : syracuseStep 4550003 = 6825005) B6825005
theorem B3033335 : Blo 1893435 3033335 := bstep (se 1 (by rfl) ⟨2275001, by rfl⟩ : syracuseStep 3033335 = 4550003) B4550003
theorem B8088893 : Blo 1893435 8088893 := bstep (se 3 (by rfl) ⟨1516667, by rfl⟩ : syracuseStep 8088893 = 3033335) B3033335
theorem B5392595 : Blo 1893435 5392595 := bstep (se 1 (by rfl) ⟨4044446, by rfl⟩ : syracuseStep 5392595 = 8088893) B8088893
theorem B14380253 : Blo 1893435 14380253 := bstep (se 3 (by rfl) ⟨2696297, by rfl⟩ : syracuseStep 14380253 = 5392595) B5392595
theorem B9586835 : Blo 1893435 9586835 := bstep (se 1 (by rfl) ⟨7190126, by rfl⟩ : syracuseStep 9586835 = 14380253) B14380253
theorem B6391223 : Blo 1893435 6391223 := bstep (se 1 (by rfl) ⟨4793417, by rfl⟩ : syracuseStep 6391223 = 9586835) B9586835
theorem B4260815 : Blo 1893435 4260815 := bstep (se 1 (by rfl) ⟨3195611, by rfl⟩ : syracuseStep 4260815 = 6391223) B6391223
theorem B2840543 : Blo 1893435 2840543 := bstep (se 1 (by rfl) ⟨2130407, by rfl⟩ : syracuseStep 2840543 = 4260815) B4260815
theorem B1893695 : Blo 1893435 1893695 := bstep (se 1 (by rfl) ⟨1420271, by rfl⟩ : syracuseStep 1893695 = 2840543) B2840543
theorem B2840549 : Blo 1893435 2840549 := bbase (se 4 (by rfl) ⟨266301, by rfl⟩ : syracuseStep 2840549 = 532603) (by norm_num)
theorem B1893699 : Blo 1893435 1893699 := bstep (se 1 (by rfl) ⟨1420274, by rfl⟩ : syracuseStep 1893699 = 2840549) B2840549
theorem B7678165 : Blo 1893435 7678165 := bbase (se 7 (by rfl) ⟨89978, by rfl⟩ : syracuseStep 7678165 = 179957) (by norm_num)
theorem B10237553 : Blo 1893435 10237553 := bstep (se 2 (by rfl) ⟨3839082, by rfl⟩ : syracuseStep 10237553 = 7678165) B7678165
theorem B6825035 : Blo 1893435 6825035 := bstep (se 1 (by rfl) ⟨5118776, by rfl⟩ : syracuseStep 6825035 = 10237553) B10237553
theorem B4550023 : Blo 1893435 4550023 := bstep (se 1 (by rfl) ⟨3412517, by rfl⟩ : syracuseStep 4550023 = 6825035) B6825035
theorem B6066697 : Blo 1893435 6066697 := bstep (se 2 (by rfl) ⟨2275011, by rfl⟩ : syracuseStep 6066697 = 4550023) B4550023
theorem B8088929 : Blo 1893435 8088929 := bstep (se 2 (by rfl) ⟨3033348, by rfl⟩ : syracuseStep 8088929 = 6066697) B6066697
theorem B5392619 : Blo 1893435 5392619 := bstep (se 1 (by rfl) ⟨4044464, by rfl⟩ : syracuseStep 5392619 = 8088929) B8088929
theorem B3595079 : Blo 1893435 3595079 := bstep (se 1 (by rfl) ⟨2696309, by rfl⟩ : syracuseStep 3595079 = 5392619) B5392619
theorem B2396719 : Blo 1893435 2396719 := bstep (se 1 (by rfl) ⟨1797539, by rfl⟩ : syracuseStep 2396719 = 3595079) B3595079
theorem B3195625 : Blo 1893435 3195625 := bstep (se 2 (by rfl) ⟨1198359, by rfl⟩ : syracuseStep 3195625 = 2396719) B2396719
theorem B4260833 : Blo 1893435 4260833 := bstep (se 2 (by rfl) ⟨1597812, by rfl⟩ : syracuseStep 4260833 = 3195625) B3195625
theorem B2840555 : Blo 1893435 2840555 := bstep (se 1 (by rfl) ⟨2130416, by rfl⟩ : syracuseStep 2840555 = 4260833) B4260833
theorem B1893703 : Blo 1893435 1893703 := bstep (se 1 (by rfl) ⟨1420277, by rfl⟩ : syracuseStep 1893703 = 2840555) B2840555
theorem B2130421 : Blo 1893435 2130421 := bbase (se 5 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 2130421 = 199727) (by norm_num)
theorem B2840561 : Blo 1893435 2840561 := bstep (se 2 (by rfl) ⟨1065210, by rfl⟩ : syracuseStep 2840561 = 2130421) B2130421
theorem B1893707 : Blo 1893435 1893707 := bstep (se 1 (by rfl) ⟨1420280, by rfl⟩ : syracuseStep 1893707 = 2840561) B2840561
theorem B2396729 : Blo 1893435 2396729 := bbase (se 2 (by rfl) ⟨898773, by rfl⟩ : syracuseStep 2396729 = 1797547) (by norm_num)
theorem B6391277 : Blo 1893435 6391277 := bstep (se 3 (by rfl) ⟨1198364, by rfl⟩ : syracuseStep 6391277 = 2396729) B2396729
theorem B4260851 : Blo 1893435 4260851 := bstep (se 1 (by rfl) ⟨3195638, by rfl⟩ : syracuseStep 4260851 = 6391277) B6391277
theorem B2840567 : Blo 1893435 2840567 := bstep (se 1 (by rfl) ⟨2130425, by rfl⟩ : syracuseStep 2840567 = 4260851) B4260851
theorem B1893711 : Blo 1893435 1893711 := bstep (se 1 (by rfl) ⟨1420283, by rfl⟩ : syracuseStep 1893711 = 2840567) B2840567
theorem B2840573 : Blo 1893435 2840573 := bbase (se 3 (by rfl) ⟨532607, by rfl⟩ : syracuseStep 2840573 = 1065215) (by norm_num)
theorem B1893715 : Blo 1893435 1893715 := bstep (se 1 (by rfl) ⟨1420286, by rfl⟩ : syracuseStep 1893715 = 2840573) B2840573
theorem B4260869 : Blo 1893435 4260869 := bbase (se 4 (by rfl) ⟨399456, by rfl⟩ : syracuseStep 4260869 = 798913) (by norm_num)
theorem B2840579 : Blo 1893435 2840579 := bstep (se 1 (by rfl) ⟨2130434, by rfl⟩ : syracuseStep 2840579 = 4260869) B4260869
theorem B1893719 : Blo 1893435 1893719 := bstep (se 1 (by rfl) ⟨1420289, by rfl⟩ : syracuseStep 1893719 = 2840579) B2840579
theorem B3595117 : Blo 1893435 3595117 := bbase (se 3 (by rfl) ⟨674084, by rfl⟩ : syracuseStep 3595117 = 1348169) (by norm_num)
theorem B4793489 : Blo 1893435 4793489 := bstep (se 2 (by rfl) ⟨1797558, by rfl⟩ : syracuseStep 4793489 = 3595117) B3595117
theorem B3195659 : Blo 1893435 3195659 := bstep (se 1 (by rfl) ⟨2396744, by rfl⟩ : syracuseStep 3195659 = 4793489) B4793489
theorem B2130439 : Blo 1893435 2130439 := bstep (se 1 (by rfl) ⟨1597829, by rfl⟩ : syracuseStep 2130439 = 3195659) B3195659
theorem B2840585 : Blo 1893435 2840585 := bstep (se 2 (by rfl) ⟨1065219, by rfl⟩ : syracuseStep 2840585 = 2130439) B2130439
theorem B1893723 : Blo 1893435 1893723 := bstep (se 1 (by rfl) ⟨1420292, by rfl⟩ : syracuseStep 1893723 = 2840585) B2840585
theorem B9586997 : Blo 1893435 9586997 := bbase (se 5 (by rfl) ⟨449390, by rfl⟩ : syracuseStep 9586997 = 898781) (by norm_num)
theorem B6391331 : Blo 1893435 6391331 := bstep (se 1 (by rfl) ⟨4793498, by rfl⟩ : syracuseStep 6391331 = 9586997) B9586997
theorem B4260887 : Blo 1893435 4260887 := bstep (se 1 (by rfl) ⟨3195665, by rfl⟩ : syracuseStep 4260887 = 6391331) B6391331
theorem B2840591 : Blo 1893435 2840591 := bstep (se 1 (by rfl) ⟨2130443, by rfl⟩ : syracuseStep 2840591 = 4260887) B4260887
theorem B1893727 : Blo 1893435 1893727 := bstep (se 1 (by rfl) ⟨1420295, by rfl⟩ : syracuseStep 1893727 = 2840591) B2840591
theorem B2840597 : Blo 1893435 2840597 := bbase (se 6 (by rfl) ⟨66576, by rfl⟩ : syracuseStep 2840597 = 133153) (by norm_num)
theorem B1893731 : Blo 1893435 1893731 := bstep (se 1 (by rfl) ⟨1420298, by rfl⟩ : syracuseStep 1893731 = 2840597) B2840597
theorem B2429461 : Blo 1893435 2429461 := bbase (se 6 (by rfl) ⟨56940, by rfl⟩ : syracuseStep 2429461 = 113881) (by norm_num)
theorem B3239281 : Blo 1893435 3239281 := bstep (se 2 (by rfl) ⟨1214730, by rfl⟩ : syracuseStep 3239281 = 2429461) B2429461
theorem B4319041 : Blo 1893435 4319041 := bstep (se 2 (by rfl) ⟨1619640, by rfl⟩ : syracuseStep 4319041 = 3239281) B3239281
theorem B5758721 : Blo 1893435 5758721 := bstep (se 2 (by rfl) ⟨2159520, by rfl⟩ : syracuseStep 5758721 = 4319041) B4319041
theorem B3839147 : Blo 1893435 3839147 := bstep (se 1 (by rfl) ⟨2879360, by rfl⟩ : syracuseStep 3839147 = 5758721) B5758721
theorem B2559431 : Blo 1893435 2559431 := bstep (se 1 (by rfl) ⟨1919573, by rfl⟩ : syracuseStep 2559431 = 3839147) B3839147
theorem B6825149 : Blo 1893435 6825149 := bstep (se 3 (by rfl) ⟨1279715, by rfl⟩ : syracuseStep 6825149 = 2559431) B2559431
theorem B4550099 : Blo 1893435 4550099 := bstep (se 1 (by rfl) ⟨3412574, by rfl⟩ : syracuseStep 4550099 = 6825149) B6825149
theorem B12133597 : Blo 1893435 12133597 := bstep (se 3 (by rfl) ⟨2275049, by rfl⟩ : syracuseStep 12133597 = 4550099) B4550099
theorem B16178129 : Blo 1893435 16178129 := bstep (se 2 (by rfl) ⟨6066798, by rfl⟩ : syracuseStep 16178129 = 12133597) B12133597
theorem B10785419 : Blo 1893435 10785419 := bstep (se 1 (by rfl) ⟨8089064, by rfl⟩ : syracuseStep 10785419 = 16178129) B16178129
theorem B7190279 : Blo 1893435 7190279 := bstep (se 1 (by rfl) ⟨5392709, by rfl⟩ : syracuseStep 7190279 = 10785419) B10785419
theorem B4793519 : Blo 1893435 4793519 := bstep (se 1 (by rfl) ⟨3595139, by rfl⟩ : syracuseStep 4793519 = 7190279) B7190279
theorem B3195679 : Blo 1893435 3195679 := bstep (se 1 (by rfl) ⟨2396759, by rfl⟩ : syracuseStep 3195679 = 4793519) B4793519
theorem B4260905 : Blo 1893435 4260905 := bstep (se 2 (by rfl) ⟨1597839, by rfl⟩ : syracuseStep 4260905 = 3195679) B3195679
theorem B2840603 : Blo 1893435 2840603 := bstep (se 1 (by rfl) ⟨2130452, by rfl⟩ : syracuseStep 2840603 = 4260905) B4260905
theorem B1893735 : Blo 1893435 1893735 := bstep (se 1 (by rfl) ⟨1420301, by rfl⟩ : syracuseStep 1893735 = 2840603) B2840603
theorem B2130457 : Blo 1893435 2130457 := bbase (se 2 (by rfl) ⟨798921, by rfl⟩ : syracuseStep 2130457 = 1597843) (by norm_num)
theorem B2840609 : Blo 1893435 2840609 := bstep (se 2 (by rfl) ⟨1065228, by rfl⟩ : syracuseStep 2840609 = 2130457) B2130457
theorem B1893739 : Blo 1893435 1893739 := bstep (se 1 (by rfl) ⟨1420304, by rfl⟩ : syracuseStep 1893739 = 2840609) B2840609
theorem B7190309 : Blo 1893435 7190309 := bbase (se 4 (by rfl) ⟨674091, by rfl⟩ : syracuseStep 7190309 = 1348183) (by norm_num)
theorem B4793539 : Blo 1893435 4793539 := bstep (se 1 (by rfl) ⟨3595154, by rfl⟩ : syracuseStep 4793539 = 7190309) B7190309
theorem B6391385 : Blo 1893435 6391385 := bstep (se 2 (by rfl) ⟨2396769, by rfl⟩ : syracuseStep 6391385 = 4793539) B4793539
theorem B4260923 : Blo 1893435 4260923 := bstep (se 1 (by rfl) ⟨3195692, by rfl⟩ : syracuseStep 4260923 = 6391385) B6391385
theorem B2840615 : Blo 1893435 2840615 := bstep (se 1 (by rfl) ⟨2130461, by rfl⟩ : syracuseStep 2840615 = 4260923) B4260923
theorem B1893743 : Blo 1893435 1893743 := bstep (se 1 (by rfl) ⟨1420307, by rfl⟩ : syracuseStep 1893743 = 2840615) B2840615
theorem B2840621 : Blo 1893435 2840621 := bbase (se 3 (by rfl) ⟨532616, by rfl⟩ : syracuseStep 2840621 = 1065233) (by norm_num)
theorem B1893747 : Blo 1893435 1893747 := bstep (se 1 (by rfl) ⟨1420310, by rfl⟩ : syracuseStep 1893747 = 2840621) B2840621
theorem B4260941 : Blo 1893435 4260941 := bbase (se 3 (by rfl) ⟨798926, by rfl⟩ : syracuseStep 4260941 = 1597853) (by norm_num)
theorem B2840627 : Blo 1893435 2840627 := bstep (se 1 (by rfl) ⟨2130470, by rfl⟩ : syracuseStep 2840627 = 4260941) B4260941
theorem B1893751 : Blo 1893435 1893751 := bstep (se 1 (by rfl) ⟨1420313, by rfl⟩ : syracuseStep 1893751 = 2840627) B2840627
theorem B2396785 : Blo 1893435 2396785 := bbase (se 2 (by rfl) ⟨898794, by rfl⟩ : syracuseStep 2396785 = 1797589) (by norm_num)
theorem B3195713 : Blo 1893435 3195713 := bstep (se 2 (by rfl) ⟨1198392, by rfl⟩ : syracuseStep 3195713 = 2396785) B2396785
theorem B2130475 : Blo 1893435 2130475 := bstep (se 1 (by rfl) ⟨1597856, by rfl⟩ : syracuseStep 2130475 = 3195713) B3195713
theorem B2840633 : Blo 1893435 2840633 := bstep (se 2 (by rfl) ⟨1065237, by rfl⟩ : syracuseStep 2840633 = 2130475) B2130475
theorem B1893755 : Blo 1893435 1893755 := bstep (se 1 (by rfl) ⟨1420316, by rfl⟩ : syracuseStep 1893755 = 2840633) B2840633
theorem B3644237 : Blo 1893435 3644237 := bbase (se 3 (by rfl) ⟨683294, by rfl⟩ : syracuseStep 3644237 = 1366589) (by norm_num)
theorem B9717965 : Blo 1893435 9717965 := bstep (se 3 (by rfl) ⟨1822118, by rfl⟩ : syracuseStep 9717965 = 3644237) B3644237
theorem B6478643 : Blo 1893435 6478643 := bstep (se 1 (by rfl) ⟨4858982, by rfl⟩ : syracuseStep 6478643 = 9717965) B9717965
theorem B4319095 : Blo 1893435 4319095 := bstep (se 1 (by rfl) ⟨3239321, by rfl⟩ : syracuseStep 4319095 = 6478643) B6478643
theorem B5758793 : Blo 1893435 5758793 := bstep (se 2 (by rfl) ⟨2159547, by rfl⟩ : syracuseStep 5758793 = 4319095) B4319095
theorem B3839195 : Blo 1893435 3839195 := bstep (se 1 (by rfl) ⟨2879396, by rfl⟩ : syracuseStep 3839195 = 5758793) B5758793
theorem B10237853 : Blo 1893435 10237853 := bstep (se 3 (by rfl) ⟨1919597, by rfl⟩ : syracuseStep 10237853 = 3839195) B3839195
theorem B6825235 : Blo 1893435 6825235 := bstep (se 1 (by rfl) ⟨5118926, by rfl⟩ : syracuseStep 6825235 = 10237853) B10237853
theorem B9100313 : Blo 1893435 9100313 := bstep (se 2 (by rfl) ⟨3412617, by rfl⟩ : syracuseStep 9100313 = 6825235) B6825235
theorem B6066875 : Blo 1893435 6066875 := bstep (se 1 (by rfl) ⟨4550156, by rfl⟩ : syracuseStep 6066875 = 9100313) B9100313
theorem B4044583 : Blo 1893435 4044583 := bstep (se 1 (by rfl) ⟨3033437, by rfl⟩ : syracuseStep 4044583 = 6066875) B6066875
theorem B21571109 : Blo 1893435 21571109 := bstep (se 4 (by rfl) ⟨2022291, by rfl⟩ : syracuseStep 21571109 = 4044583) B4044583
theorem B14380739 : Blo 1893435 14380739 := bstep (se 1 (by rfl) ⟨10785554, by rfl⟩ : syracuseStep 14380739 = 21571109) B21571109
theorem B9587159 : Blo 1893435 9587159 := bstep (se 1 (by rfl) ⟨7190369, by rfl⟩ : syracuseStep 9587159 = 14380739) B14380739
theorem B6391439 : Blo 1893435 6391439 := bstep (se 1 (by rfl) ⟨4793579, by rfl⟩ : syracuseStep 6391439 = 9587159) B9587159
theorem B4260959 : Blo 1893435 4260959 := bstep (se 1 (by rfl) ⟨3195719, by rfl⟩ : syracuseStep 4260959 = 6391439) B6391439
theorem B2840639 : Blo 1893435 2840639 := bstep (se 1 (by rfl) ⟨2130479, by rfl⟩ : syracuseStep 2840639 = 4260959) B4260959
theorem B1893759 : Blo 1893435 1893759 := bstep (se 1 (by rfl) ⟨1420319, by rfl⟩ : syracuseStep 1893759 = 2840639) B2840639
theorem B2840645 : Blo 1893435 2840645 := bbase (se 4 (by rfl) ⟨266310, by rfl⟩ : syracuseStep 2840645 = 532621) (by norm_num)
theorem B1893763 : Blo 1893435 1893763 := bstep (se 1 (by rfl) ⟨1420322, by rfl⟩ : syracuseStep 1893763 = 2840645) B2840645
theorem B3195733 : Blo 1893435 3195733 := bbase (se 9 (by rfl) ⟨9362, by rfl⟩ : syracuseStep 3195733 = 18725) (by norm_num)
theorem B4260977 : Blo 1893435 4260977 := bstep (se 2 (by rfl) ⟨1597866, by rfl⟩ : syracuseStep 4260977 = 3195733) B3195733
theorem B2840651 : Blo 1893435 2840651 := bstep (se 1 (by rfl) ⟨2130488, by rfl⟩ : syracuseStep 2840651 = 4260977) B4260977
theorem B1893767 : Blo 1893435 1893767 := bstep (se 1 (by rfl) ⟨1420325, by rfl⟩ : syracuseStep 1893767 = 2840651) B2840651
theorem B2130493 : Blo 1893435 2130493 := bbase (se 3 (by rfl) ⟨399467, by rfl⟩ : syracuseStep 2130493 = 798935) (by norm_num)
theorem B2840657 : Blo 1893435 2840657 := bstep (se 2 (by rfl) ⟨1065246, by rfl⟩ : syracuseStep 2840657 = 2130493) B2130493
theorem B1893771 : Blo 1893435 1893771 := bstep (se 1 (by rfl) ⟨1420328, by rfl⟩ : syracuseStep 1893771 = 2840657) B2840657
theorem B6391493 : Blo 1893435 6391493 := bbase (se 4 (by rfl) ⟨599202, by rfl⟩ : syracuseStep 6391493 = 1198405) (by norm_num)
theorem B4260995 : Blo 1893435 4260995 := bstep (se 1 (by rfl) ⟨3195746, by rfl⟩ : syracuseStep 4260995 = 6391493) B6391493
theorem B2840663 : Blo 1893435 2840663 := bstep (se 1 (by rfl) ⟨2130497, by rfl⟩ : syracuseStep 2840663 = 4260995) B4260995
theorem B1893775 : Blo 1893435 1893775 := bstep (se 1 (by rfl) ⟨1420331, by rfl⟩ : syracuseStep 1893775 = 2840663) B2840663
theorem B2840669 : Blo 1893435 2840669 := bbase (se 3 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 2840669 = 1065251) (by norm_num)
theorem B1893779 : Blo 1893435 1893779 := bstep (se 1 (by rfl) ⟨1420334, by rfl⟩ : syracuseStep 1893779 = 2840669) B2840669
theorem B4261013 : Blo 1893435 4261013 := bbase (se 6 (by rfl) ⟨99867, by rfl⟩ : syracuseStep 4261013 = 199735) (by norm_num)
theorem B2840675 : Blo 1893435 2840675 := bstep (se 1 (by rfl) ⟨2130506, by rfl⟩ : syracuseStep 2840675 = 4261013) B4261013
theorem B1893783 : Blo 1893435 1893783 := bstep (se 1 (by rfl) ⟨1420337, by rfl⟩ : syracuseStep 1893783 = 2840675) B2840675
theorem B2696429 : Blo 1893435 2696429 := bbase (se 3 (by rfl) ⟨505580, by rfl⟩ : syracuseStep 2696429 = 1011161) (by norm_num)
theorem B7190477 : Blo 1893435 7190477 := bstep (se 3 (by rfl) ⟨1348214, by rfl⟩ : syracuseStep 7190477 = 2696429) B2696429
theorem B4793651 : Blo 1893435 4793651 := bstep (se 1 (by rfl) ⟨3595238, by rfl⟩ : syracuseStep 4793651 = 7190477) B7190477
theorem B3195767 : Blo 1893435 3195767 := bstep (se 1 (by rfl) ⟨2396825, by rfl⟩ : syracuseStep 3195767 = 4793651) B4793651
theorem B2130511 : Blo 1893435 2130511 := bstep (se 1 (by rfl) ⟨1597883, by rfl⟩ : syracuseStep 2130511 = 3195767) B3195767
theorem B2840681 : Blo 1893435 2840681 := bstep (se 2 (by rfl) ⟨1065255, by rfl⟩ : syracuseStep 2840681 = 2130511) B2130511
theorem B1893787 : Blo 1893435 1893787 := bstep (se 1 (by rfl) ⟨1420340, by rfl⟩ : syracuseStep 1893787 = 2840681) B2840681
theorem B5119013 : Blo 1893435 5119013 := bbase (se 4 (by rfl) ⟨479907, by rfl⟩ : syracuseStep 5119013 = 959815) (by norm_num)
theorem B3412675 : Blo 1893435 3412675 := bstep (se 1 (by rfl) ⟨2559506, by rfl⟩ : syracuseStep 3412675 = 5119013) B5119013
theorem B18200933 : Blo 1893435 18200933 := bstep (se 4 (by rfl) ⟨1706337, by rfl⟩ : syracuseStep 18200933 = 3412675) B3412675
theorem B12133955 : Blo 1893435 12133955 := bstep (se 1 (by rfl) ⟨9100466, by rfl⟩ : syracuseStep 12133955 = 18200933) B18200933
theorem B8089303 : Blo 1893435 8089303 := bstep (se 1 (by rfl) ⟨6066977, by rfl⟩ : syracuseStep 8089303 = 12133955) B12133955
theorem B10785737 : Blo 1893435 10785737 := bstep (se 2 (by rfl) ⟨4044651, by rfl⟩ : syracuseStep 10785737 = 8089303) B8089303
theorem B7190491 : Blo 1893435 7190491 := bstep (se 1 (by rfl) ⟨5392868, by rfl⟩ : syracuseStep 7190491 = 10785737) B10785737
theorem B9587321 : Blo 1893435 9587321 := bstep (se 2 (by rfl) ⟨3595245, by rfl⟩ : syracuseStep 9587321 = 7190491) B7190491
theorem B6391547 : Blo 1893435 6391547 := bstep (se 1 (by rfl) ⟨4793660, by rfl⟩ : syracuseStep 6391547 = 9587321) B9587321
theorem B4261031 : Blo 1893435 4261031 := bstep (se 1 (by rfl) ⟨3195773, by rfl⟩ : syracuseStep 4261031 = 6391547) B6391547
theorem B2840687 : Blo 1893435 2840687 := bstep (se 1 (by rfl) ⟨2130515, by rfl⟩ : syracuseStep 2840687 = 4261031) B4261031
theorem B1893791 : Blo 1893435 1893791 := bstep (se 1 (by rfl) ⟨1420343, by rfl⟩ : syracuseStep 1893791 = 2840687) B2840687
theorem B2840693 : Blo 1893435 2840693 := bbase (se 5 (by rfl) ⟨133157, by rfl⟩ : syracuseStep 2840693 = 266315) (by norm_num)
theorem B1893795 : Blo 1893435 1893795 := bstep (se 1 (by rfl) ⟨1420346, by rfl⟩ : syracuseStep 1893795 = 2840693) B2840693
theorem B3595261 : Blo 1893435 3595261 := bbase (se 3 (by rfl) ⟨674111, by rfl⟩ : syracuseStep 3595261 = 1348223) (by norm_num)
theorem B4793681 : Blo 1893435 4793681 := bstep (se 2 (by rfl) ⟨1797630, by rfl⟩ : syracuseStep 4793681 = 3595261) B3595261
theorem B3195787 : Blo 1893435 3195787 := bstep (se 1 (by rfl) ⟨2396840, by rfl⟩ : syracuseStep 3195787 = 4793681) B4793681
theorem B4261049 : Blo 1893435 4261049 := bstep (se 2 (by rfl) ⟨1597893, by rfl⟩ : syracuseStep 4261049 = 3195787) B3195787
theorem B2840699 : Blo 1893435 2840699 := bstep (se 1 (by rfl) ⟨2130524, by rfl⟩ : syracuseStep 2840699 = 4261049) B4261049
theorem B1893799 : Blo 1893435 1893799 := bstep (se 1 (by rfl) ⟨1420349, by rfl⟩ : syracuseStep 1893799 = 2840699) B2840699
theorem B2130529 : Blo 1893435 2130529 := bbase (se 2 (by rfl) ⟨798948, by rfl⟩ : syracuseStep 2130529 = 1597897) (by norm_num)
theorem B2840705 : Blo 1893435 2840705 := bstep (se 2 (by rfl) ⟨1065264, by rfl⟩ : syracuseStep 2840705 = 2130529) B2130529
theorem B1893803 : Blo 1893435 1893803 := bstep (se 1 (by rfl) ⟨1420352, by rfl⟩ : syracuseStep 1893803 = 2840705) B2840705
theorem B4793701 : Blo 1893435 4793701 := bbase (se 4 (by rfl) ⟨449409, by rfl⟩ : syracuseStep 4793701 = 898819) (by norm_num)
theorem B6391601 : Blo 1893435 6391601 := bstep (se 2 (by rfl) ⟨2396850, by rfl⟩ : syracuseStep 6391601 = 4793701) B4793701
theorem B4261067 : Blo 1893435 4261067 := bstep (se 1 (by rfl) ⟨3195800, by rfl⟩ : syracuseStep 4261067 = 6391601) B6391601
theorem B2840711 : Blo 1893435 2840711 := bstep (se 1 (by rfl) ⟨2130533, by rfl⟩ : syracuseStep 2840711 = 4261067) B4261067
theorem B1893807 : Blo 1893435 1893807 := bstep (se 1 (by rfl) ⟨1420355, by rfl⟩ : syracuseStep 1893807 = 2840711) B2840711
theorem B2840717 : Blo 1893435 2840717 := bbase (se 3 (by rfl) ⟨532634, by rfl⟩ : syracuseStep 2840717 = 1065269) (by norm_num)
theorem B1893811 : Blo 1893435 1893811 := bstep (se 1 (by rfl) ⟨1420358, by rfl⟩ : syracuseStep 1893811 = 2840717) B2840717
theorem B4261085 : Blo 1893435 4261085 := bbase (se 3 (by rfl) ⟨798953, by rfl⟩ : syracuseStep 4261085 = 1597907) (by norm_num)
theorem B2840723 : Blo 1893435 2840723 := bstep (se 1 (by rfl) ⟨2130542, by rfl⟩ : syracuseStep 2840723 = 4261085) B4261085
theorem B1893815 : Blo 1893435 1893815 := bstep (se 1 (by rfl) ⟨1420361, by rfl⟩ : syracuseStep 1893815 = 2840723) B2840723
theorem B3195821 : Blo 1893435 3195821 := bbase (se 3 (by rfl) ⟨599216, by rfl⟩ : syracuseStep 3195821 = 1198433) (by norm_num)
theorem B2130547 : Blo 1893435 2130547 := bstep (se 1 (by rfl) ⟨1597910, by rfl⟩ : syracuseStep 2130547 = 3195821) B3195821
theorem B2840729 : Blo 1893435 2840729 := bstep (se 2 (by rfl) ⟨1065273, by rfl⟩ : syracuseStep 2840729 = 2130547) B2130547
theorem B1893819 : Blo 1893435 1893819 := bstep (se 1 (by rfl) ⟨1420364, by rfl⟩ : syracuseStep 1893819 = 2840729) B2840729
theorem B7108661 : Blo 1893435 7108661 := bbase (se 5 (by rfl) ⟨333218, by rfl⟩ : syracuseStep 7108661 = 666437) (by norm_num)
theorem B18956429 : Blo 1893435 18956429 := bstep (se 3 (by rfl) ⟨3554330, by rfl⟩ : syracuseStep 18956429 = 7108661) B7108661
theorem B12637619 : Blo 1893435 12637619 := bstep (se 1 (by rfl) ⟨9478214, by rfl⟩ : syracuseStep 12637619 = 18956429) B18956429
theorem B8425079 : Blo 1893435 8425079 := bstep (se 1 (by rfl) ⟨6318809, by rfl⟩ : syracuseStep 8425079 = 12637619) B12637619
theorem B5616719 : Blo 1893435 5616719 := bstep (se 1 (by rfl) ⟨4212539, by rfl⟩ : syracuseStep 5616719 = 8425079) B8425079
theorem B3744479 : Blo 1893435 3744479 := bstep (se 1 (by rfl) ⟨2808359, by rfl⟩ : syracuseStep 3744479 = 5616719) B5616719
theorem B9985277 : Blo 1893435 9985277 := bstep (se 3 (by rfl) ⟨1872239, by rfl⟩ : syracuseStep 9985277 = 3744479) B3744479
theorem B26627405 : Blo 1893435 26627405 := bstep (se 3 (by rfl) ⟨4992638, by rfl⟩ : syracuseStep 26627405 = 9985277) B9985277
theorem B284025653 : Blo 1893435 284025653 := bstep (se 5 (by rfl) ⟨13313702, by rfl⟩ : syracuseStep 284025653 = 26627405) B26627405
theorem B189350435 : Blo 1893435 189350435 := bstep (se 1 (by rfl) ⟨142012826, by rfl⟩ : syracuseStep 189350435 = 284025653) B284025653
theorem B126233623 : Blo 1893435 126233623 := bstep (se 1 (by rfl) ⟨94675217, by rfl⟩ : syracuseStep 126233623 = 189350435) B189350435
theorem B673245989 : Blo 1893435 673245989 := bstep (se 4 (by rfl) ⟨63116811, by rfl⟩ : syracuseStep 673245989 = 126233623) B126233623
theorem B448830659 : Blo 1893435 448830659 := bstep (se 1 (by rfl) ⟨336622994, by rfl⟩ : syracuseStep 448830659 = 673245989) B673245989
theorem B299220439 : Blo 1893435 299220439 := bstep (se 1 (by rfl) ⟨224415329, by rfl⟩ : syracuseStep 299220439 = 448830659) B448830659
theorem B398960585 : Blo 1893435 398960585 := bstep (se 2 (by rfl) ⟨149610219, by rfl⟩ : syracuseStep 398960585 = 299220439) B299220439
theorem B265973723 : Blo 1893435 265973723 := bstep (se 1 (by rfl) ⟨199480292, by rfl⟩ : syracuseStep 265973723 = 398960585) B398960585
theorem B177315815 : Blo 1893435 177315815 := bstep (se 1 (by rfl) ⟨132986861, by rfl⟩ : syracuseStep 177315815 = 265973723) B265973723
theorem B472842173 : Blo 1893435 472842173 := bstep (se 3 (by rfl) ⟨88657907, by rfl⟩ : syracuseStep 472842173 = 177315815) B177315815
theorem B315228115 : Blo 1893435 315228115 := bstep (se 1 (by rfl) ⟨236421086, by rfl⟩ : syracuseStep 315228115 = 472842173) B472842173
theorem B420304153 : Blo 1893435 420304153 := bstep (se 2 (by rfl) ⟨157614057, by rfl⟩ : syracuseStep 420304153 = 315228115) B315228115
theorem B560405537 : Blo 1893435 560405537 := bstep (se 2 (by rfl) ⟨210152076, by rfl⟩ : syracuseStep 560405537 = 420304153) B420304153
theorem B373603691 : Blo 1893435 373603691 := bstep (se 1 (by rfl) ⟨280202768, by rfl⟩ : syracuseStep 373603691 = 560405537) B560405537
theorem B249069127 : Blo 1893435 249069127 := bstep (se 1 (by rfl) ⟨186801845, by rfl⟩ : syracuseStep 249069127 = 373603691) B373603691
theorem B332092169 : Blo 1893435 332092169 := bstep (se 2 (by rfl) ⟨124534563, by rfl⟩ : syracuseStep 332092169 = 249069127) B249069127
theorem B221394779 : Blo 1893435 221394779 := bstep (se 1 (by rfl) ⟨166046084, by rfl⟩ : syracuseStep 221394779 = 332092169) B332092169
theorem B147596519 : Blo 1893435 147596519 := bstep (se 1 (by rfl) ⟨110697389, by rfl⟩ : syracuseStep 147596519 = 221394779) B221394779
theorem B98397679 : Blo 1893435 98397679 := bstep (se 1 (by rfl) ⟨73798259, by rfl⟩ : syracuseStep 98397679 = 147596519) B147596519
theorem B131196905 : Blo 1893435 131196905 := bstep (se 2 (by rfl) ⟨49198839, by rfl⟩ : syracuseStep 131196905 = 98397679) B98397679
theorem B87464603 : Blo 1893435 87464603 := bstep (se 1 (by rfl) ⟨65598452, by rfl⟩ : syracuseStep 87464603 = 131196905) B131196905
theorem B58309735 : Blo 1893435 58309735 := bstep (se 1 (by rfl) ⟨43732301, by rfl⟩ : syracuseStep 58309735 = 87464603) B87464603
theorem B77746313 : Blo 1893435 77746313 := bstep (se 2 (by rfl) ⟨29154867, by rfl⟩ : syracuseStep 77746313 = 58309735) B58309735
theorem B51830875 : Blo 1893435 51830875 := bstep (se 1 (by rfl) ⟨38873156, by rfl⟩ : syracuseStep 51830875 = 77746313) B77746313
theorem B69107833 : Blo 1893435 69107833 := bstep (se 2 (by rfl) ⟨25915437, by rfl⟩ : syracuseStep 69107833 = 51830875) B51830875
theorem B92143777 : Blo 1893435 92143777 := bstep (se 2 (by rfl) ⟨34553916, by rfl⟩ : syracuseStep 92143777 = 69107833) B69107833
theorem B122858369 : Blo 1893435 122858369 := bstep (se 2 (by rfl) ⟨46071888, by rfl⟩ : syracuseStep 122858369 = 92143777) B92143777
theorem B81905579 : Blo 1893435 81905579 := bstep (se 1 (by rfl) ⟨61429184, by rfl⟩ : syracuseStep 81905579 = 122858369) B122858369
theorem B54603719 : Blo 1893435 54603719 := bstep (se 1 (by rfl) ⟨40952789, by rfl⟩ : syracuseStep 54603719 = 81905579) B81905579
theorem B36402479 : Blo 1893435 36402479 := bstep (se 1 (by rfl) ⟨27301859, by rfl⟩ : syracuseStep 36402479 = 54603719) B54603719
theorem B24268319 : Blo 1893435 24268319 := bstep (se 1 (by rfl) ⟨18201239, by rfl⟩ : syracuseStep 24268319 = 36402479) B36402479
theorem B16178879 : Blo 1893435 16178879 := bstep (se 1 (by rfl) ⟨12134159, by rfl⟩ : syracuseStep 16178879 = 24268319) B24268319
theorem B10785919 : Blo 1893435 10785919 := bstep (se 1 (by rfl) ⟨8089439, by rfl⟩ : syracuseStep 10785919 = 16178879) B16178879
theorem B14381225 : Blo 1893435 14381225 := bstep (se 2 (by rfl) ⟨5392959, by rfl⟩ : syracuseStep 14381225 = 10785919) B10785919
theorem B9587483 : Blo 1893435 9587483 := bstep (se 1 (by rfl) ⟨7190612, by rfl⟩ : syracuseStep 9587483 = 14381225) B14381225
theorem B6391655 : Blo 1893435 6391655 := bstep (se 1 (by rfl) ⟨4793741, by rfl⟩ : syracuseStep 6391655 = 9587483) B9587483
theorem B4261103 : Blo 1893435 4261103 := bstep (se 1 (by rfl) ⟨3195827, by rfl⟩ : syracuseStep 4261103 = 6391655) B6391655
theorem B2840735 : Blo 1893435 2840735 := bstep (se 1 (by rfl) ⟨2130551, by rfl⟩ : syracuseStep 2840735 = 4261103) B4261103
theorem B1893823 : Blo 1893435 1893823 := bstep (se 1 (by rfl) ⟨1420367, by rfl⟩ : syracuseStep 1893823 = 2840735) B2840735
theorem B2840741 : Blo 1893435 2840741 := bbase (se 4 (by rfl) ⟨266319, by rfl⟩ : syracuseStep 2840741 = 532639) (by norm_num)
theorem B1893827 : Blo 1893435 1893827 := bstep (se 1 (by rfl) ⟨1420370, by rfl⟩ : syracuseStep 1893827 = 2840741) B2840741
theorem B2396881 : Blo 1893435 2396881 := bbase (se 2 (by rfl) ⟨898830, by rfl⟩ : syracuseStep 2396881 = 1797661) (by norm_num)
theorem B3195841 : Blo 1893435 3195841 := bstep (se 2 (by rfl) ⟨1198440, by rfl⟩ : syracuseStep 3195841 = 2396881) B2396881
theorem B4261121 : Blo 1893435 4261121 := bstep (se 2 (by rfl) ⟨1597920, by rfl⟩ : syracuseStep 4261121 = 3195841) B3195841
theorem B2840747 : Blo 1893435 2840747 := bstep (se 1 (by rfl) ⟨2130560, by rfl⟩ : syracuseStep 2840747 = 4261121) B4261121
theorem B1893831 : Blo 1893435 1893831 := bstep (se 1 (by rfl) ⟨1420373, by rfl⟩ : syracuseStep 1893831 = 2840747) B2840747
theorem B2130565 : Blo 1893435 2130565 := bbase (se 4 (by rfl) ⟨199740, by rfl⟩ : syracuseStep 2130565 = 399481) (by norm_num)
theorem B2840753 : Blo 1893435 2840753 := bstep (se 2 (by rfl) ⟨1065282, by rfl⟩ : syracuseStep 2840753 = 2130565) B2130565
theorem B1893835 : Blo 1893435 1893835 := bstep (se 1 (by rfl) ⟨1420376, by rfl⟩ : syracuseStep 1893835 = 2840753) B2840753
theorem B9224869 : Blo 1893435 9224869 := bbase (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) (by norm_num)
theorem B12299825 : Blo 1893435 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B8199883 : Blo 1893435 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B43732709 : Blo 1893435 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B29155139 : Blo 1893435 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B19436759 : Blo 1893435 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B12957839 : Blo 1893435 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B8638559 : Blo 1893435 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B5759039 : Blo 1893435 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B3839359 : Blo 1893435 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B5119145 : Blo 1893435 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B3412763 : Blo 1893435 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B2275175 : Blo 1893435 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B6067133 : Blo 1893435 6067133 := bstep (se 3 (by rfl) ⟨1137587, by rfl⟩ : syracuseStep 6067133 = 2275175) B2275175
theorem B4044755 : Blo 1893435 4044755 := bstep (se 1 (by rfl) ⟨3033566, by rfl⟩ : syracuseStep 4044755 = 6067133) B6067133
theorem B2696503 : Blo 1893435 2696503 := bstep (se 1 (by rfl) ⟨2022377, by rfl⟩ : syracuseStep 2696503 = 4044755) B4044755
theorem B3595337 : Blo 1893435 3595337 := bstep (se 2 (by rfl) ⟨1348251, by rfl⟩ : syracuseStep 3595337 = 2696503) B2696503
theorem B2396891 : Blo 1893435 2396891 := bstep (se 1 (by rfl) ⟨1797668, by rfl⟩ : syracuseStep 2396891 = 3595337) B3595337
theorem B6391709 : Blo 1893435 6391709 := bstep (se 3 (by rfl) ⟨1198445, by rfl⟩ : syracuseStep 6391709 = 2396891) B2396891
theorem B4261139 : Blo 1893435 4261139 := bstep (se 1 (by rfl) ⟨3195854, by rfl⟩ : syracuseStep 4261139 = 6391709) B6391709
theorem B2840759 : Blo 1893435 2840759 := bstep (se 1 (by rfl) ⟨2130569, by rfl⟩ : syracuseStep 2840759 = 4261139) B4261139
theorem B1893839 : Blo 1893435 1893839 := bstep (se 1 (by rfl) ⟨1420379, by rfl⟩ : syracuseStep 1893839 = 2840759) B2840759
theorem B2840765 : Blo 1893435 2840765 := bbase (se 3 (by rfl) ⟨532643, by rfl⟩ : syracuseStep 2840765 = 1065287) (by norm_num)
theorem B1893843 : Blo 1893435 1893843 := bstep (se 1 (by rfl) ⟨1420382, by rfl⟩ : syracuseStep 1893843 = 2840765) B2840765
theorem B4261157 : Blo 1893435 4261157 := bbase (se 4 (by rfl) ⟨399483, by rfl⟩ : syracuseStep 4261157 = 798967) (by norm_num)
theorem B2840771 : Blo 1893435 2840771 := bstep (se 1 (by rfl) ⟨2130578, by rfl⟩ : syracuseStep 2840771 = 4261157) B4261157
theorem B1893847 : Blo 1893435 1893847 := bstep (se 1 (by rfl) ⟨1420385, by rfl⟩ : syracuseStep 1893847 = 2840771) B2840771
theorem B4793813 : Blo 1893435 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B3195875 : Blo 1893435 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B2130583 : Blo 1893435 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B2840777 : Blo 1893435 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B1893851 : Blo 1893435 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B12957941 : Blo 1893435 12957941 := bbase (se 5 (by rfl) ⟨607403, by rfl⟩ : syracuseStep 12957941 = 1214807) (by norm_num)
theorem B34554509 : Blo 1893435 34554509 := bstep (se 3 (by rfl) ⟨6478970, by rfl⟩ : syracuseStep 34554509 = 12957941) B12957941
theorem B23036339 : Blo 1893435 23036339 := bstep (se 1 (by rfl) ⟨17277254, by rfl⟩ : syracuseStep 23036339 = 34554509) B34554509
theorem B15357559 : Blo 1893435 15357559 := bstep (se 1 (by rfl) ⟨11518169, by rfl⟩ : syracuseStep 15357559 = 23036339) B23036339
theorem B20476745 : Blo 1893435 20476745 := bstep (se 2 (by rfl) ⟨7678779, by rfl⟩ : syracuseStep 20476745 = 15357559) B15357559
theorem B13651163 : Blo 1893435 13651163 := bstep (se 1 (by rfl) ⟨10238372, by rfl⟩ : syracuseStep 13651163 = 20476745) B20476745
theorem B9100775 : Blo 1893435 9100775 := bstep (se 1 (by rfl) ⟨6825581, by rfl⟩ : syracuseStep 9100775 = 13651163) B13651163
theorem B6067183 : Blo 1893435 6067183 := bstep (se 1 (by rfl) ⟨4550387, by rfl⟩ : syracuseStep 6067183 = 9100775) B9100775
theorem B8089577 : Blo 1893435 8089577 := bstep (se 2 (by rfl) ⟨3033591, by rfl⟩ : syracuseStep 8089577 = 6067183) B6067183
theorem B5393051 : Blo 1893435 5393051 := bstep (se 1 (by rfl) ⟨4044788, by rfl⟩ : syracuseStep 5393051 = 8089577) B8089577
theorem B3595367 : Blo 1893435 3595367 := bstep (se 1 (by rfl) ⟨2696525, by rfl⟩ : syracuseStep 3595367 = 5393051) B5393051
theorem B9587645 : Blo 1893435 9587645 := bstep (se 3 (by rfl) ⟨1797683, by rfl⟩ : syracuseStep 9587645 = 3595367) B3595367
theorem B6391763 : Blo 1893435 6391763 := bstep (se 1 (by rfl) ⟨4793822, by rfl⟩ : syracuseStep 6391763 = 9587645) B9587645
theorem B4261175 : Blo 1893435 4261175 := bstep (se 1 (by rfl) ⟨3195881, by rfl⟩ : syracuseStep 4261175 = 6391763) B6391763
theorem B2840783 : Blo 1893435 2840783 := bstep (se 1 (by rfl) ⟨2130587, by rfl⟩ : syracuseStep 2840783 = 4261175) B4261175
theorem B1893855 : Blo 1893435 1893855 := bstep (se 1 (by rfl) ⟨1420391, by rfl⟩ : syracuseStep 1893855 = 2840783) B2840783
theorem B2840789 : Blo 1893435 2840789 := bbase (se 7 (by rfl) ⟨33290, by rfl⟩ : syracuseStep 2840789 = 66581) (by norm_num)
theorem B1893859 : Blo 1893435 1893859 := bstep (se 1 (by rfl) ⟨1420394, by rfl⟩ : syracuseStep 1893859 = 2840789) B2840789
theorem B3033605 : Blo 1893435 3033605 := bbase (se 4 (by rfl) ⟨284400, by rfl⟩ : syracuseStep 3033605 = 568801) (by norm_num)
theorem B2022403 : Blo 1893435 2022403 := bstep (se 1 (by rfl) ⟨1516802, by rfl⟩ : syracuseStep 2022403 = 3033605) B3033605
theorem B2696537 : Blo 1893435 2696537 := bstep (se 2 (by rfl) ⟨1011201, by rfl⟩ : syracuseStep 2696537 = 2022403) B2022403
theorem B7190765 : Blo 1893435 7190765 := bstep (se 3 (by rfl) ⟨1348268, by rfl⟩ : syracuseStep 7190765 = 2696537) B2696537
theorem B4793843 : Blo 1893435 4793843 := bstep (se 1 (by rfl) ⟨3595382, by rfl⟩ : syracuseStep 4793843 = 7190765) B7190765
theorem B3195895 : Blo 1893435 3195895 := bstep (se 1 (by rfl) ⟨2396921, by rfl⟩ : syracuseStep 3195895 = 4793843) B4793843
theorem B4261193 : Blo 1893435 4261193 := bstep (se 2 (by rfl) ⟨1597947, by rfl⟩ : syracuseStep 4261193 = 3195895) B3195895
theorem B2840795 : Blo 1893435 2840795 := bstep (se 1 (by rfl) ⟨2130596, by rfl⟩ : syracuseStep 2840795 = 4261193) B4261193
theorem B1893863 : Blo 1893435 1893863 := bstep (se 1 (by rfl) ⟨1420397, by rfl⟩ : syracuseStep 1893863 = 2840795) B2840795
theorem B2130601 : Blo 1893435 2130601 := bbase (se 2 (by rfl) ⟨798975, by rfl⟩ : syracuseStep 2130601 = 1597951) (by norm_num)
theorem B2840801 : Blo 1893435 2840801 := bstep (se 2 (by rfl) ⟨1065300, by rfl⟩ : syracuseStep 2840801 = 2130601) B2130601
theorem B1893867 : Blo 1893435 1893867 := bstep (se 1 (by rfl) ⟨1420400, by rfl⟩ : syracuseStep 1893867 = 2840801) B2840801
theorem B2275213 : Blo 1893435 2275213 := bbase (se 3 (by rfl) ⟨426602, by rfl⟩ : syracuseStep 2275213 = 853205) (by norm_num)
theorem B3033617 : Blo 1893435 3033617 := bstep (se 2 (by rfl) ⟨1137606, by rfl⟩ : syracuseStep 3033617 = 2275213) B2275213
theorem B8089645 : Blo 1893435 8089645 := bstep (se 3 (by rfl) ⟨1516808, by rfl⟩ : syracuseStep 8089645 = 3033617) B3033617
theorem B10786193 : Blo 1893435 10786193 := bstep (se 2 (by rfl) ⟨4044822, by rfl⟩ : syracuseStep 10786193 = 8089645) B8089645
theorem B7190795 : Blo 1893435 7190795 := bstep (se 1 (by rfl) ⟨5393096, by rfl⟩ : syracuseStep 7190795 = 10786193) B10786193
theorem B4793863 : Blo 1893435 4793863 := bstep (se 1 (by rfl) ⟨3595397, by rfl⟩ : syracuseStep 4793863 = 7190795) B7190795
theorem B6391817 : Blo 1893435 6391817 := bstep (se 2 (by rfl) ⟨2396931, by rfl⟩ : syracuseStep 6391817 = 4793863) B4793863
theorem B4261211 : Blo 1893435 4261211 := bstep (se 1 (by rfl) ⟨3195908, by rfl⟩ : syracuseStep 4261211 = 6391817) B6391817
theorem B2840807 : Blo 1893435 2840807 := bstep (se 1 (by rfl) ⟨2130605, by rfl⟩ : syracuseStep 2840807 = 4261211) B4261211
theorem B1893871 : Blo 1893435 1893871 := bstep (se 1 (by rfl) ⟨1420403, by rfl⟩ : syracuseStep 1893871 = 2840807) B2840807
theorem B2840813 : Blo 1893435 2840813 := bbase (se 3 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 2840813 = 1065305) (by norm_num)
theorem B1893875 : Blo 1893435 1893875 := bstep (se 1 (by rfl) ⟨1420406, by rfl⟩ : syracuseStep 1893875 = 2840813) B2840813
theorem B4261229 : Blo 1893435 4261229 := bbase (se 3 (by rfl) ⟨798980, by rfl⟩ : syracuseStep 4261229 = 1597961) (by norm_num)
theorem B2840819 : Blo 1893435 2840819 := bstep (se 1 (by rfl) ⟨2130614, by rfl⟩ : syracuseStep 2840819 = 4261229) B4261229
theorem B1893879 : Blo 1893435 1893879 := bstep (se 1 (by rfl) ⟨1420409, by rfl⟩ : syracuseStep 1893879 = 2840819) B2840819
theorem B3595421 : Blo 1893435 3595421 := bbase (se 3 (by rfl) ⟨674141, by rfl⟩ : syracuseStep 3595421 = 1348283) (by norm_num)
theorem B2396947 : Blo 1893435 2396947 := bstep (se 1 (by rfl) ⟨1797710, by rfl⟩ : syracuseStep 2396947 = 3595421) B3595421
theorem B3195929 : Blo 1893435 3195929 := bstep (se 2 (by rfl) ⟨1198473, by rfl⟩ : syracuseStep 3195929 = 2396947) B2396947
theorem B2130619 : Blo 1893435 2130619 := bstep (se 1 (by rfl) ⟨1597964, by rfl⟩ : syracuseStep 2130619 = 3195929) B3195929
theorem B2840825 : Blo 1893435 2840825 := bstep (se 2 (by rfl) ⟨1065309, by rfl⟩ : syracuseStep 2840825 = 2130619) B2130619
theorem B1893883 : Blo 1893435 1893883 := bstep (se 1 (by rfl) ⟨1420412, by rfl⟩ : syracuseStep 1893883 = 2840825) B2840825
theorem B44330453 : Blo 1893435 44330453 := bbase (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) (by norm_num)
theorem B472858165 : Blo 1893435 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B630477553 : Blo 1893435 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B840636737 : Blo 1893435 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B560424491 : Blo 1893435 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B373616327 : Blo 1893435 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B249077551 : Blo 1893435 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B332103401 : Blo 1893435 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B221402267 : Blo 1893435 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B147601511 : Blo 1893435 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B98401007 : Blo 1893435 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B262402685 : Blo 1893435 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B174935123 : Blo 1893435 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B116623415 : Blo 1893435 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B77748943 : Blo 1893435 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B103665257 : Blo 1893435 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B69110171 : Blo 1893435 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B46073447 : Blo 1893435 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B30715631 : Blo 1893435 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B20477087 : Blo 1893435 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B13651391 : Blo 1893435 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B9100927 : Blo 1893435 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B48538277 : Blo 1893435 48538277 := bstep (se 4 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 48538277 = 9100927) B9100927
theorem B32358851 : Blo 1893435 32358851 := bstep (se 1 (by rfl) ⟨24269138, by rfl⟩ : syracuseStep 32358851 = 48538277) B48538277
theorem B21572567 : Blo 1893435 21572567 := bstep (se 1 (by rfl) ⟨16179425, by rfl⟩ : syracuseStep 21572567 = 32358851) B32358851
theorem B14381711 : Blo 1893435 14381711 := bstep (se 1 (by rfl) ⟨10786283, by rfl⟩ : syracuseStep 14381711 = 21572567) B21572567
theorem B9587807 : Blo 1893435 9587807 := bstep (se 1 (by rfl) ⟨7190855, by rfl⟩ : syracuseStep 9587807 = 14381711) B14381711
theorem B6391871 : Blo 1893435 6391871 := bstep (se 1 (by rfl) ⟨4793903, by rfl⟩ : syracuseStep 6391871 = 9587807) B9587807
theorem B4261247 : Blo 1893435 4261247 := bstep (se 1 (by rfl) ⟨3195935, by rfl⟩ : syracuseStep 4261247 = 6391871) B6391871
theorem B2840831 : Blo 1893435 2840831 := bstep (se 1 (by rfl) ⟨2130623, by rfl⟩ : syracuseStep 2840831 = 4261247) B4261247
theorem B1893887 : Blo 1893435 1893887 := bstep (se 1 (by rfl) ⟨1420415, by rfl⟩ : syracuseStep 1893887 = 2840831) B2840831
theorem B2840837 : Blo 1893435 2840837 := bbase (se 4 (by rfl) ⟨266328, by rfl⟩ : syracuseStep 2840837 = 532657) (by norm_num)
theorem B1893891 : Blo 1893435 1893891 := bstep (se 1 (by rfl) ⟨1420418, by rfl⟩ : syracuseStep 1893891 = 2840837) B2840837
theorem B3195949 : Blo 1893435 3195949 := bbase (se 3 (by rfl) ⟨599240, by rfl⟩ : syracuseStep 3195949 = 1198481) (by norm_num)
theorem B4261265 : Blo 1893435 4261265 := bstep (se 2 (by rfl) ⟨1597974, by rfl⟩ : syracuseStep 4261265 = 3195949) B3195949
theorem B2840843 : Blo 1893435 2840843 := bstep (se 1 (by rfl) ⟨2130632, by rfl⟩ : syracuseStep 2840843 = 4261265) B4261265
theorem B1893895 : Blo 1893435 1893895 := bstep (se 1 (by rfl) ⟨1420421, by rfl⟩ : syracuseStep 1893895 = 2840843) B2840843
theorem B2130637 : Blo 1893435 2130637 := bbase (se 3 (by rfl) ⟨399494, by rfl⟩ : syracuseStep 2130637 = 798989) (by norm_num)
theorem B2840849 : Blo 1893435 2840849 := bstep (se 2 (by rfl) ⟨1065318, by rfl⟩ : syracuseStep 2840849 = 2130637) B2130637
theorem B1893899 : Blo 1893435 1893899 := bstep (se 1 (by rfl) ⟨1420424, by rfl⟩ : syracuseStep 1893899 = 2840849) B2840849
theorem B6391925 : Blo 1893435 6391925 := bbase (se 5 (by rfl) ⟨299621, by rfl⟩ : syracuseStep 6391925 = 599243) (by norm_num)
theorem B4261283 : Blo 1893435 4261283 := bstep (se 1 (by rfl) ⟨3195962, by rfl⟩ : syracuseStep 4261283 = 6391925) B6391925
theorem B2840855 : Blo 1893435 2840855 := bstep (se 1 (by rfl) ⟨2130641, by rfl⟩ : syracuseStep 2840855 = 4261283) B4261283
theorem B1893903 : Blo 1893435 1893903 := bstep (se 1 (by rfl) ⟨1420427, by rfl⟩ : syracuseStep 1893903 = 2840855) B2840855
theorem B2840861 : Blo 1893435 2840861 := bbase (se 3 (by rfl) ⟨532661, by rfl⟩ : syracuseStep 2840861 = 1065323) (by norm_num)
theorem B1893907 : Blo 1893435 1893907 := bstep (se 1 (by rfl) ⟨1420430, by rfl⟩ : syracuseStep 1893907 = 2840861) B2840861
theorem B4261301 : Blo 1893435 4261301 := bbase (se 5 (by rfl) ⟨199748, by rfl⟩ : syracuseStep 4261301 = 399497) (by norm_num)
theorem B2840867 : Blo 1893435 2840867 := bstep (se 1 (by rfl) ⟨2130650, by rfl⟩ : syracuseStep 2840867 = 4261301) B4261301
theorem B1893911 : Blo 1893435 1893911 := bstep (se 1 (by rfl) ⟨1420433, by rfl⟩ : syracuseStep 1893911 = 2840867) B2840867
theorem B4044917 : Blo 1893435 4044917 := bbase (se 5 (by rfl) ⟨189605, by rfl⟩ : syracuseStep 4044917 = 379211) (by norm_num)
theorem B10786445 : Blo 1893435 10786445 := bstep (se 3 (by rfl) ⟨2022458, by rfl⟩ : syracuseStep 10786445 = 4044917) B4044917
theorem B7190963 : Blo 1893435 7190963 := bstep (se 1 (by rfl) ⟨5393222, by rfl⟩ : syracuseStep 7190963 = 10786445) B10786445
theorem B4793975 : Blo 1893435 4793975 := bstep (se 1 (by rfl) ⟨3595481, by rfl⟩ : syracuseStep 4793975 = 7190963) B7190963
theorem B3195983 : Blo 1893435 3195983 := bstep (se 1 (by rfl) ⟨2396987, by rfl⟩ : syracuseStep 3195983 = 4793975) B4793975
theorem B2130655 : Blo 1893435 2130655 := bstep (se 1 (by rfl) ⟨1597991, by rfl⟩ : syracuseStep 2130655 = 3195983) B3195983
theorem B2840873 : Blo 1893435 2840873 := bstep (se 2 (by rfl) ⟨1065327, by rfl⟩ : syracuseStep 2840873 = 2130655) B2130655
theorem B1893915 : Blo 1893435 1893915 := bstep (se 1 (by rfl) ⟨1420436, by rfl⟩ : syracuseStep 1893915 = 2840873) B2840873
theorem B4044925 : Blo 1893435 4044925 := bbase (se 3 (by rfl) ⟨758423, by rfl⟩ : syracuseStep 4044925 = 1516847) (by norm_num)
theorem B5393233 : Blo 1893435 5393233 := bstep (se 2 (by rfl) ⟨2022462, by rfl⟩ : syracuseStep 5393233 = 4044925) B4044925
theorem B7190977 : Blo 1893435 7190977 := bstep (se 2 (by rfl) ⟨2696616, by rfl⟩ : syracuseStep 7190977 = 5393233) B5393233
theorem B9587969 : Blo 1893435 9587969 := bstep (se 2 (by rfl) ⟨3595488, by rfl⟩ : syracuseStep 9587969 = 7190977) B7190977
theorem B6391979 : Blo 1893435 6391979 := bstep (se 1 (by rfl) ⟨4793984, by rfl⟩ : syracuseStep 6391979 = 9587969) B9587969
theorem B4261319 : Blo 1893435 4261319 := bstep (se 1 (by rfl) ⟨3195989, by rfl⟩ : syracuseStep 4261319 = 6391979) B6391979
theorem B2840879 : Blo 1893435 2840879 := bstep (se 1 (by rfl) ⟨2130659, by rfl⟩ : syracuseStep 2840879 = 4261319) B4261319
theorem B1893919 : Blo 1893435 1893919 := bstep (se 1 (by rfl) ⟨1420439, by rfl⟩ : syracuseStep 1893919 = 2840879) B2840879
theorem B2840885 : Blo 1893435 2840885 := bbase (se 5 (by rfl) ⟨133166, by rfl⟩ : syracuseStep 2840885 = 266333) (by norm_num)
theorem B1893923 : Blo 1893435 1893923 := bstep (se 1 (by rfl) ⟨1420442, by rfl⟩ : syracuseStep 1893923 = 2840885) B2840885
theorem B4794005 : Blo 1893435 4794005 := bbase (se 6 (by rfl) ⟨112359, by rfl⟩ : syracuseStep 4794005 = 224719) (by norm_num)
theorem B3196003 : Blo 1893435 3196003 := bstep (se 1 (by rfl) ⟨2397002, by rfl⟩ : syracuseStep 3196003 = 4794005) B4794005
theorem B4261337 : Blo 1893435 4261337 := bstep (se 2 (by rfl) ⟨1598001, by rfl⟩ : syracuseStep 4261337 = 3196003) B3196003
theorem B2840891 : Blo 1893435 2840891 := bstep (se 1 (by rfl) ⟨2130668, by rfl⟩ : syracuseStep 2840891 = 4261337) B4261337
theorem B1893927 : Blo 1893435 1893927 := bstep (se 1 (by rfl) ⟨1420445, by rfl⟩ : syracuseStep 1893927 = 2840891) B2840891
theorem B2130673 : Blo 1893435 2130673 := bbase (se 2 (by rfl) ⟨799002, by rfl⟩ : syracuseStep 2130673 = 1598005) (by norm_num)
theorem B2840897 : Blo 1893435 2840897 := bstep (se 2 (by rfl) ⟨1065336, by rfl⟩ : syracuseStep 2840897 = 2130673) B2130673
theorem B1893931 : Blo 1893435 1893931 := bstep (se 1 (by rfl) ⟨1420448, by rfl⟩ : syracuseStep 1893931 = 2840897) B2840897
theorem B18702389 : Blo 1893435 18702389 := bbase (se 5 (by rfl) ⟨876674, by rfl⟩ : syracuseStep 18702389 = 1753349) (by norm_num)
theorem B12468259 : Blo 1893435 12468259 := bstep (se 1 (by rfl) ⟨9351194, by rfl⟩ : syracuseStep 12468259 = 18702389) B18702389
theorem B66497381 : Blo 1893435 66497381 := bstep (se 4 (by rfl) ⟨6234129, by rfl⟩ : syracuseStep 66497381 = 12468259) B12468259
theorem B44331587 : Blo 1893435 44331587 := bstep (se 1 (by rfl) ⟨33248690, by rfl⟩ : syracuseStep 44331587 = 66497381) B66497381
theorem B29554391 : Blo 1893435 29554391 := bstep (se 1 (by rfl) ⟨22165793, by rfl⟩ : syracuseStep 29554391 = 44331587) B44331587
theorem B19702927 : Blo 1893435 19702927 := bstep (se 1 (by rfl) ⟨14777195, by rfl⟩ : syracuseStep 19702927 = 29554391) B29554391
theorem B26270569 : Blo 1893435 26270569 := bstep (se 2 (by rfl) ⟨9851463, by rfl⟩ : syracuseStep 26270569 = 19702927) B19702927
theorem B35027425 : Blo 1893435 35027425 := bstep (se 2 (by rfl) ⟨13135284, by rfl⟩ : syracuseStep 35027425 = 26270569) B26270569
theorem B46703233 : Blo 1893435 46703233 := bstep (se 2 (by rfl) ⟨17513712, by rfl⟩ : syracuseStep 46703233 = 35027425) B35027425
theorem B249083909 : Blo 1893435 249083909 := bstep (se 4 (by rfl) ⟨23351616, by rfl⟩ : syracuseStep 249083909 = 46703233) B46703233
theorem B166055939 : Blo 1893435 166055939 := bstep (se 1 (by rfl) ⟨124541954, by rfl⟩ : syracuseStep 166055939 = 249083909) B249083909
theorem B110703959 : Blo 1893435 110703959 := bstep (se 1 (by rfl) ⟨83027969, by rfl⟩ : syracuseStep 110703959 = 166055939) B166055939
theorem B73802639 : Blo 1893435 73802639 := bstep (se 1 (by rfl) ⟨55351979, by rfl⟩ : syracuseStep 73802639 = 110703959) B110703959
theorem B49201759 : Blo 1893435 49201759 := bstep (se 1 (by rfl) ⟨36901319, by rfl⟩ : syracuseStep 49201759 = 73802639) B73802639
theorem B262409381 : Blo 1893435 262409381 := bstep (se 4 (by rfl) ⟨24600879, by rfl⟩ : syracuseStep 262409381 = 49201759) B49201759
theorem B174939587 : Blo 1893435 174939587 := bstep (se 1 (by rfl) ⟨131204690, by rfl⟩ : syracuseStep 174939587 = 262409381) B262409381
theorem B116626391 : Blo 1893435 116626391 := bstep (se 1 (by rfl) ⟨87469793, by rfl⟩ : syracuseStep 116626391 = 174939587) B174939587
theorem B77750927 : Blo 1893435 77750927 := bstep (se 1 (by rfl) ⟨58313195, by rfl⟩ : syracuseStep 77750927 = 116626391) B116626391
theorem B51833951 : Blo 1893435 51833951 := bstep (se 1 (by rfl) ⟨38875463, by rfl⟩ : syracuseStep 51833951 = 77750927) B77750927
theorem B34555967 : Blo 1893435 34555967 := bstep (se 1 (by rfl) ⟨25916975, by rfl⟩ : syracuseStep 34555967 = 51833951) B51833951
theorem B23037311 : Blo 1893435 23037311 := bstep (se 1 (by rfl) ⟨17277983, by rfl⟩ : syracuseStep 23037311 = 34555967) B34555967
theorem B61432829 : Blo 1893435 61432829 := bstep (se 3 (by rfl) ⟨11518655, by rfl⟩ : syracuseStep 61432829 = 23037311) B23037311
theorem B40955219 : Blo 1893435 40955219 := bstep (se 1 (by rfl) ⟨30716414, by rfl⟩ : syracuseStep 40955219 = 61432829) B61432829
theorem B27303479 : Blo 1893435 27303479 := bstep (se 1 (by rfl) ⟨20477609, by rfl⟩ : syracuseStep 27303479 = 40955219) B40955219
theorem B18202319 : Blo 1893435 18202319 := bstep (se 1 (by rfl) ⟨13651739, by rfl⟩ : syracuseStep 18202319 = 27303479) B27303479
theorem B12134879 : Blo 1893435 12134879 := bstep (se 1 (by rfl) ⟨9101159, by rfl⟩ : syracuseStep 12134879 = 18202319) B18202319
theorem B8089919 : Blo 1893435 8089919 := bstep (se 1 (by rfl) ⟨6067439, by rfl⟩ : syracuseStep 8089919 = 12134879) B12134879
theorem B5393279 : Blo 1893435 5393279 := bstep (se 1 (by rfl) ⟨4044959, by rfl⟩ : syracuseStep 5393279 = 8089919) B8089919
theorem B3595519 : Blo 1893435 3595519 := bstep (se 1 (by rfl) ⟨2696639, by rfl⟩ : syracuseStep 3595519 = 5393279) B5393279
theorem B4794025 : Blo 1893435 4794025 := bstep (se 2 (by rfl) ⟨1797759, by rfl⟩ : syracuseStep 4794025 = 3595519) B3595519
theorem B6392033 : Blo 1893435 6392033 := bstep (se 2 (by rfl) ⟨2397012, by rfl⟩ : syracuseStep 6392033 = 4794025) B4794025
theorem B4261355 : Blo 1893435 4261355 := bstep (se 1 (by rfl) ⟨3196016, by rfl⟩ : syracuseStep 4261355 = 6392033) B6392033
theorem B2840903 : Blo 1893435 2840903 := bstep (se 1 (by rfl) ⟨2130677, by rfl⟩ : syracuseStep 2840903 = 4261355) B4261355
theorem B1893935 : Blo 1893435 1893935 := bstep (se 1 (by rfl) ⟨1420451, by rfl⟩ : syracuseStep 1893935 = 2840903) B2840903
theorem B2840909 : Blo 1893435 2840909 := bbase (se 3 (by rfl) ⟨532670, by rfl⟩ : syracuseStep 2840909 = 1065341) (by norm_num)
theorem B1893939 : Blo 1893435 1893939 := bstep (se 1 (by rfl) ⟨1420454, by rfl⟩ : syracuseStep 1893939 = 2840909) B2840909
theorem B4261373 : Blo 1893435 4261373 := bbase (se 3 (by rfl) ⟨799007, by rfl⟩ : syracuseStep 4261373 = 1598015) (by norm_num)
theorem B2840915 : Blo 1893435 2840915 := bstep (se 1 (by rfl) ⟨2130686, by rfl⟩ : syracuseStep 2840915 = 4261373) B4261373
theorem B1893943 : Blo 1893435 1893943 := bstep (se 1 (by rfl) ⟨1420457, by rfl⟩ : syracuseStep 1893943 = 2840915) B2840915
theorem B3196037 : Blo 1893435 3196037 := bbase (se 4 (by rfl) ⟨299628, by rfl⟩ : syracuseStep 3196037 = 599257) (by norm_num)
theorem B2130691 : Blo 1893435 2130691 := bstep (se 1 (by rfl) ⟨1598018, by rfl⟩ : syracuseStep 2130691 = 3196037) B3196037
theorem B2840921 : Blo 1893435 2840921 := bstep (se 2 (by rfl) ⟨1065345, by rfl⟩ : syracuseStep 2840921 = 2130691) B2130691
theorem B1893947 : Blo 1893435 1893947 := bstep (se 1 (by rfl) ⟨1420460, by rfl⟩ : syracuseStep 1893947 = 2840921) B2840921
theorem B14382197 : Blo 1893435 14382197 := bbase (se 5 (by rfl) ⟨674165, by rfl⟩ : syracuseStep 14382197 = 1348331) (by norm_num)
theorem B9588131 : Blo 1893435 9588131 := bstep (se 1 (by rfl) ⟨7191098, by rfl⟩ : syracuseStep 9588131 = 14382197) B14382197
theorem B6392087 : Blo 1893435 6392087 := bstep (se 1 (by rfl) ⟨4794065, by rfl⟩ : syracuseStep 6392087 = 9588131) B9588131
theorem B4261391 : Blo 1893435 4261391 := bstep (se 1 (by rfl) ⟨3196043, by rfl⟩ : syracuseStep 4261391 = 6392087) B6392087
theorem B2840927 : Blo 1893435 2840927 := bstep (se 1 (by rfl) ⟨2130695, by rfl⟩ : syracuseStep 2840927 = 4261391) B4261391
theorem B1893951 : Blo 1893435 1893951 := bstep (se 1 (by rfl) ⟨1420463, by rfl⟩ : syracuseStep 1893951 = 2840927) B2840927
theorem B2840933 : Blo 1893435 2840933 := bbase (se 4 (by rfl) ⟨266337, by rfl⟩ : syracuseStep 2840933 = 532675) (by norm_num)
theorem B1893955 : Blo 1893435 1893955 := bstep (se 1 (by rfl) ⟨1420466, by rfl⟩ : syracuseStep 1893955 = 2840933) B2840933
theorem B3595565 : Blo 1893435 3595565 := bbase (se 3 (by rfl) ⟨674168, by rfl⟩ : syracuseStep 3595565 = 1348337) (by norm_num)
theorem B2397043 : Blo 1893435 2397043 := bstep (se 1 (by rfl) ⟨1797782, by rfl⟩ : syracuseStep 2397043 = 3595565) B3595565
theorem B3196057 : Blo 1893435 3196057 := bstep (se 2 (by rfl) ⟨1198521, by rfl⟩ : syracuseStep 3196057 = 2397043) B2397043
theorem B4261409 : Blo 1893435 4261409 := bstep (se 2 (by rfl) ⟨1598028, by rfl⟩ : syracuseStep 4261409 = 3196057) B3196057
theorem B2840939 : Blo 1893435 2840939 := bstep (se 1 (by rfl) ⟨2130704, by rfl⟩ : syracuseStep 2840939 = 4261409) B4261409
theorem B1893959 : Blo 1893435 1893959 := bstep (se 1 (by rfl) ⟨1420469, by rfl⟩ : syracuseStep 1893959 = 2840939) B2840939
theorem B2130709 : Blo 1893435 2130709 := bbase (se 6 (by rfl) ⟨49938, by rfl⟩ : syracuseStep 2130709 = 99877) (by norm_num)
theorem B2840945 : Blo 1893435 2840945 := bstep (se 2 (by rfl) ⟨1065354, by rfl⟩ : syracuseStep 2840945 = 2130709) B2130709
theorem B1893963 : Blo 1893435 1893963 := bstep (se 1 (by rfl) ⟨1420472, by rfl⟩ : syracuseStep 1893963 = 2840945) B2840945
theorem B2397053 : Blo 1893435 2397053 := bbase (se 3 (by rfl) ⟨449447, by rfl⟩ : syracuseStep 2397053 = 898895) (by norm_num)
theorem B6392141 : Blo 1893435 6392141 := bstep (se 3 (by rfl) ⟨1198526, by rfl⟩ : syracuseStep 6392141 = 2397053) B2397053
theorem B4261427 : Blo 1893435 4261427 := bstep (se 1 (by rfl) ⟨3196070, by rfl⟩ : syracuseStep 4261427 = 6392141) B6392141
theorem B2840951 : Blo 1893435 2840951 := bstep (se 1 (by rfl) ⟨2130713, by rfl⟩ : syracuseStep 2840951 = 4261427) B4261427
theorem B1893967 : Blo 1893435 1893967 := bstep (se 1 (by rfl) ⟨1420475, by rfl⟩ : syracuseStep 1893967 = 2840951) B2840951
theorem B2840957 : Blo 1893435 2840957 := bbase (se 3 (by rfl) ⟨532679, by rfl⟩ : syracuseStep 2840957 = 1065359) (by norm_num)
theorem B1893971 : Blo 1893435 1893971 := bstep (se 1 (by rfl) ⟨1420478, by rfl⟩ : syracuseStep 1893971 = 2840957) B2840957
theorem B4261445 : Blo 1893435 4261445 := bbase (se 4 (by rfl) ⟨399510, by rfl⟩ : syracuseStep 4261445 = 799021) (by norm_num)
theorem B2840963 : Blo 1893435 2840963 := bstep (se 1 (by rfl) ⟨2130722, by rfl⟩ : syracuseStep 2840963 = 4261445) B4261445
theorem B1893975 : Blo 1893435 1893975 := bstep (se 1 (by rfl) ⟨1420481, by rfl⟩ : syracuseStep 1893975 = 2840963) B2840963
theorem B14578645 : Blo 1893435 14578645 := bbase (se 7 (by rfl) ⟨170843, by rfl⟩ : syracuseStep 14578645 = 341687) (by norm_num)
theorem B19438193 : Blo 1893435 19438193 := bstep (se 2 (by rfl) ⟨7289322, by rfl⟩ : syracuseStep 19438193 = 14578645) B14578645
theorem B12958795 : Blo 1893435 12958795 := bstep (se 1 (by rfl) ⟨9719096, by rfl⟩ : syracuseStep 12958795 = 19438193) B19438193
theorem B17278393 : Blo 1893435 17278393 := bstep (se 2 (by rfl) ⟨6479397, by rfl⟩ : syracuseStep 17278393 = 12958795) B12958795
theorem B23037857 : Blo 1893435 23037857 := bstep (se 2 (by rfl) ⟨8639196, by rfl⟩ : syracuseStep 23037857 = 17278393) B17278393
theorem B15358571 : Blo 1893435 15358571 := bstep (se 1 (by rfl) ⟨11518928, by rfl⟩ : syracuseStep 15358571 = 23037857) B23037857
theorem B10239047 : Blo 1893435 10239047 := bstep (se 1 (by rfl) ⟨7679285, by rfl⟩ : syracuseStep 10239047 = 15358571) B15358571
theorem B6826031 : Blo 1893435 6826031 := bstep (se 1 (by rfl) ⟨5119523, by rfl⟩ : syracuseStep 6826031 = 10239047) B10239047
theorem B4550687 : Blo 1893435 4550687 := bstep (se 1 (by rfl) ⟨3413015, by rfl⟩ : syracuseStep 4550687 = 6826031) B6826031
theorem B3033791 : Blo 1893435 3033791 := bstep (se 1 (by rfl) ⟨2275343, by rfl⟩ : syracuseStep 3033791 = 4550687) B4550687
theorem B2022527 : Blo 1893435 2022527 := bstep (se 1 (by rfl) ⟨1516895, by rfl⟩ : syracuseStep 2022527 = 3033791) B3033791
theorem B5393405 : Blo 1893435 5393405 := bstep (se 3 (by rfl) ⟨1011263, by rfl⟩ : syracuseStep 5393405 = 2022527) B2022527
theorem B3595603 : Blo 1893435 3595603 := bstep (se 1 (by rfl) ⟨2696702, by rfl⟩ : syracuseStep 3595603 = 5393405) B5393405
theorem B4794137 : Blo 1893435 4794137 := bstep (se 2 (by rfl) ⟨1797801, by rfl⟩ : syracuseStep 4794137 = 3595603) B3595603
theorem B3196091 : Blo 1893435 3196091 := bstep (se 1 (by rfl) ⟨2397068, by rfl⟩ : syracuseStep 3196091 = 4794137) B4794137
theorem B2130727 : Blo 1893435 2130727 := bstep (se 1 (by rfl) ⟨1598045, by rfl⟩ : syracuseStep 2130727 = 3196091) B3196091
theorem B2840969 : Blo 1893435 2840969 := bstep (se 2 (by rfl) ⟨1065363, by rfl⟩ : syracuseStep 2840969 = 2130727) B2130727
theorem B1893979 : Blo 1893435 1893979 := bstep (se 1 (by rfl) ⟨1420484, by rfl⟩ : syracuseStep 1893979 = 2840969) B2840969
theorem B9588293 : Blo 1893435 9588293 := bbase (se 4 (by rfl) ⟨898902, by rfl⟩ : syracuseStep 9588293 = 1797805) (by norm_num)
theorem B6392195 : Blo 1893435 6392195 := bstep (se 1 (by rfl) ⟨4794146, by rfl⟩ : syracuseStep 6392195 = 9588293) B9588293
theorem B4261463 : Blo 1893435 4261463 := bstep (se 1 (by rfl) ⟨3196097, by rfl⟩ : syracuseStep 4261463 = 6392195) B6392195
theorem B2840975 : Blo 1893435 2840975 := bstep (se 1 (by rfl) ⟨2130731, by rfl⟩ : syracuseStep 2840975 = 4261463) B4261463
theorem B1893983 : Blo 1893435 1893983 := bstep (se 1 (by rfl) ⟨1420487, by rfl⟩ : syracuseStep 1893983 = 2840975) B2840975
theorem B2840981 : Blo 1893435 2840981 := bbase (se 6 (by rfl) ⟨66585, by rfl⟩ : syracuseStep 2840981 = 133171) (by norm_num)
theorem B1893987 : Blo 1893435 1893987 := bstep (se 1 (by rfl) ⟨1420490, by rfl⟩ : syracuseStep 1893987 = 2840981) B2840981
theorem B9101429 : Blo 1893435 9101429 := bbase (se 5 (by rfl) ⟨426629, by rfl⟩ : syracuseStep 9101429 = 853259) (by norm_num)
theorem B6067619 : Blo 1893435 6067619 := bstep (se 1 (by rfl) ⟨4550714, by rfl⟩ : syracuseStep 6067619 = 9101429) B9101429
theorem B4045079 : Blo 1893435 4045079 := bstep (se 1 (by rfl) ⟨3033809, by rfl⟩ : syracuseStep 4045079 = 6067619) B6067619
theorem B10786877 : Blo 1893435 10786877 := bstep (se 3 (by rfl) ⟨2022539, by rfl⟩ : syracuseStep 10786877 = 4045079) B4045079
theorem B7191251 : Blo 1893435 7191251 := bstep (se 1 (by rfl) ⟨5393438, by rfl⟩ : syracuseStep 7191251 = 10786877) B10786877
theorem B4794167 : Blo 1893435 4794167 := bstep (se 1 (by rfl) ⟨3595625, by rfl⟩ : syracuseStep 4794167 = 7191251) B7191251
theorem B3196111 : Blo 1893435 3196111 := bstep (se 1 (by rfl) ⟨2397083, by rfl⟩ : syracuseStep 3196111 = 4794167) B4794167
theorem B4261481 : Blo 1893435 4261481 := bstep (se 2 (by rfl) ⟨1598055, by rfl⟩ : syracuseStep 4261481 = 3196111) B3196111
theorem B2840987 : Blo 1893435 2840987 := bstep (se 1 (by rfl) ⟨2130740, by rfl⟩ : syracuseStep 2840987 = 4261481) B4261481
theorem B1893991 : Blo 1893435 1893991 := bstep (se 1 (by rfl) ⟨1420493, by rfl⟩ : syracuseStep 1893991 = 2840987) B2840987
theorem B2130745 : Blo 1893435 2130745 := bbase (se 2 (by rfl) ⟨799029, by rfl⟩ : syracuseStep 2130745 = 1598059) (by norm_num)
theorem B2840993 : Blo 1893435 2840993 := bstep (se 2 (by rfl) ⟨1065372, by rfl⟩ : syracuseStep 2840993 = 2130745) B2130745
theorem B1893995 : Blo 1893435 1893995 := bstep (se 1 (by rfl) ⟨1420496, by rfl⟩ : syracuseStep 1893995 = 2840993) B2840993
theorem B5393461 : Blo 1893435 5393461 := bbase (se 5 (by rfl) ⟨252818, by rfl⟩ : syracuseStep 5393461 = 505637) (by norm_num)
theorem B7191281 : Blo 1893435 7191281 := bstep (se 2 (by rfl) ⟨2696730, by rfl⟩ : syracuseStep 7191281 = 5393461) B5393461
theorem B4794187 : Blo 1893435 4794187 := bstep (se 1 (by rfl) ⟨3595640, by rfl⟩ : syracuseStep 4794187 = 7191281) B7191281
theorem B6392249 : Blo 1893435 6392249 := bstep (se 2 (by rfl) ⟨2397093, by rfl⟩ : syracuseStep 6392249 = 4794187) B4794187
theorem B4261499 : Blo 1893435 4261499 := bstep (se 1 (by rfl) ⟨3196124, by rfl⟩ : syracuseStep 4261499 = 6392249) B6392249
theorem B2840999 : Blo 1893435 2840999 := bstep (se 1 (by rfl) ⟨2130749, by rfl⟩ : syracuseStep 2840999 = 4261499) B4261499
theorem B1893999 : Blo 1893435 1893999 := bstep (se 1 (by rfl) ⟨1420499, by rfl⟩ : syracuseStep 1893999 = 2840999) B2840999
theorem B2841005 : Blo 1893435 2841005 := bbase (se 3 (by rfl) ⟨532688, by rfl⟩ : syracuseStep 2841005 = 1065377) (by norm_num)
theorem B1894003 : Blo 1893435 1894003 := bstep (se 1 (by rfl) ⟨1420502, by rfl⟩ : syracuseStep 1894003 = 2841005) B2841005
theorem B4261517 : Blo 1893435 4261517 := bbase (se 3 (by rfl) ⟨799034, by rfl⟩ : syracuseStep 4261517 = 1598069) (by norm_num)
theorem B2841011 : Blo 1893435 2841011 := bstep (se 1 (by rfl) ⟨2130758, by rfl⟩ : syracuseStep 2841011 = 4261517) B4261517
theorem B1894007 : Blo 1893435 1894007 := bstep (se 1 (by rfl) ⟨1420505, by rfl⟩ : syracuseStep 1894007 = 2841011) B2841011
theorem B2397109 : Blo 1893435 2397109 := bbase (se 5 (by rfl) ⟨112364, by rfl⟩ : syracuseStep 2397109 = 224729) (by norm_num)
theorem B3196145 : Blo 1893435 3196145 := bstep (se 2 (by rfl) ⟨1198554, by rfl⟩ : syracuseStep 3196145 = 2397109) B2397109
theorem B2130763 : Blo 1893435 2130763 := bstep (se 1 (by rfl) ⟨1598072, by rfl⟩ : syracuseStep 2130763 = 3196145) B3196145
theorem B2841017 : Blo 1893435 2841017 := bstep (se 2 (by rfl) ⟨1065381, by rfl⟩ : syracuseStep 2841017 = 2130763) B2130763
theorem B1894011 : Blo 1893435 1894011 := bstep (se 1 (by rfl) ⟨1420508, by rfl⟩ : syracuseStep 1894011 = 2841017) B2841017
theorem B26271701 : Blo 1893435 26271701 := bbase (se 7 (by rfl) ⟨307871, by rfl⟩ : syracuseStep 26271701 = 615743) (by norm_num)
theorem B17514467 : Blo 1893435 17514467 := bstep (se 1 (by rfl) ⟨13135850, by rfl⟩ : syracuseStep 17514467 = 26271701) B26271701
theorem B11676311 : Blo 1893435 11676311 := bstep (se 1 (by rfl) ⟨8757233, by rfl⟩ : syracuseStep 11676311 = 17514467) B17514467
theorem B7784207 : Blo 1893435 7784207 := bstep (se 1 (by rfl) ⟨5838155, by rfl⟩ : syracuseStep 7784207 = 11676311) B11676311
theorem B5189471 : Blo 1893435 5189471 := bstep (se 1 (by rfl) ⟨3892103, by rfl⟩ : syracuseStep 5189471 = 7784207) B7784207
theorem B3459647 : Blo 1893435 3459647 := bstep (se 1 (by rfl) ⟨2594735, by rfl⟩ : syracuseStep 3459647 = 5189471) B5189471
theorem B2306431 : Blo 1893435 2306431 := bstep (se 1 (by rfl) ⟨1729823, by rfl⟩ : syracuseStep 2306431 = 3459647) B3459647
theorem B3075241 : Blo 1893435 3075241 := bstep (se 2 (by rfl) ⟨1153215, by rfl⟩ : syracuseStep 3075241 = 2306431) B2306431
theorem B4100321 : Blo 1893435 4100321 := bstep (se 2 (by rfl) ⟨1537620, by rfl⟩ : syracuseStep 4100321 = 3075241) B3075241
theorem B10934189 : Blo 1893435 10934189 := bstep (se 3 (by rfl) ⟨2050160, by rfl⟩ : syracuseStep 10934189 = 4100321) B4100321
theorem B7289459 : Blo 1893435 7289459 := bstep (se 1 (by rfl) ⟨5467094, by rfl⟩ : syracuseStep 7289459 = 10934189) B10934189
theorem B4859639 : Blo 1893435 4859639 := bstep (se 1 (by rfl) ⟨3644729, by rfl⟩ : syracuseStep 4859639 = 7289459) B7289459
theorem B3239759 : Blo 1893435 3239759 := bstep (se 1 (by rfl) ⟨2429819, by rfl⟩ : syracuseStep 3239759 = 4859639) B4859639
theorem B2159839 : Blo 1893435 2159839 := bstep (se 1 (by rfl) ⟨1619879, by rfl⟩ : syracuseStep 2159839 = 3239759) B3239759
theorem B2879785 : Blo 1893435 2879785 := bstep (se 2 (by rfl) ⟨1079919, by rfl⟩ : syracuseStep 2879785 = 2159839) B2159839
theorem B15358853 : Blo 1893435 15358853 := bstep (se 4 (by rfl) ⟨1439892, by rfl⟩ : syracuseStep 15358853 = 2879785) B2879785
theorem B40956941 : Blo 1893435 40956941 := bstep (se 3 (by rfl) ⟨7679426, by rfl⟩ : syracuseStep 40956941 = 15358853) B15358853
theorem B27304627 : Blo 1893435 27304627 := bstep (se 1 (by rfl) ⟨20478470, by rfl⟩ : syracuseStep 27304627 = 40956941) B40956941
theorem B36406169 : Blo 1893435 36406169 := bstep (se 2 (by rfl) ⟨13652313, by rfl⟩ : syracuseStep 36406169 = 27304627) B27304627
theorem B24270779 : Blo 1893435 24270779 := bstep (se 1 (by rfl) ⟨18203084, by rfl⟩ : syracuseStep 24270779 = 36406169) B36406169
theorem B16180519 : Blo 1893435 16180519 := bstep (se 1 (by rfl) ⟨12135389, by rfl⟩ : syracuseStep 16180519 = 24270779) B24270779
theorem B21574025 : Blo 1893435 21574025 := bstep (se 2 (by rfl) ⟨8090259, by rfl⟩ : syracuseStep 21574025 = 16180519) B16180519
theorem B14382683 : Blo 1893435 14382683 := bstep (se 1 (by rfl) ⟨10787012, by rfl⟩ : syracuseStep 14382683 = 21574025) B21574025
theorem B9588455 : Blo 1893435 9588455 := bstep (se 1 (by rfl) ⟨7191341, by rfl⟩ : syracuseStep 9588455 = 14382683) B14382683
theorem B6392303 : Blo 1893435 6392303 := bstep (se 1 (by rfl) ⟨4794227, by rfl⟩ : syracuseStep 6392303 = 9588455) B9588455
theorem B4261535 : Blo 1893435 4261535 := bstep (se 1 (by rfl) ⟨3196151, by rfl⟩ : syracuseStep 4261535 = 6392303) B6392303
theorem B2841023 : Blo 1893435 2841023 := bstep (se 1 (by rfl) ⟨2130767, by rfl⟩ : syracuseStep 2841023 = 4261535) B4261535
theorem B1894015 : Blo 1893435 1894015 := bstep (se 1 (by rfl) ⟨1420511, by rfl⟩ : syracuseStep 1894015 = 2841023) B2841023
theorem B2841029 : Blo 1893435 2841029 := bbase (se 4 (by rfl) ⟨266346, by rfl⟩ : syracuseStep 2841029 = 532693) (by norm_num)
theorem B1894019 : Blo 1893435 1894019 := bstep (se 1 (by rfl) ⟨1420514, by rfl⟩ : syracuseStep 1894019 = 2841029) B2841029
theorem B3196165 : Blo 1893435 3196165 := bbase (se 4 (by rfl) ⟨299640, by rfl⟩ : syracuseStep 3196165 = 599281) (by norm_num)
theorem B4261553 : Blo 1893435 4261553 := bstep (se 2 (by rfl) ⟨1598082, by rfl⟩ : syracuseStep 4261553 = 3196165) B3196165
theorem B2841035 : Blo 1893435 2841035 := bstep (se 1 (by rfl) ⟨2130776, by rfl⟩ : syracuseStep 2841035 = 4261553) B4261553
theorem B1894023 : Blo 1893435 1894023 := bstep (se 1 (by rfl) ⟨1420517, by rfl⟩ : syracuseStep 1894023 = 2841035) B2841035
theorem B2130781 : Blo 1893435 2130781 := bbase (se 3 (by rfl) ⟨399521, by rfl⟩ : syracuseStep 2130781 = 799043) (by norm_num)
theorem B2841041 : Blo 1893435 2841041 := bstep (se 2 (by rfl) ⟨1065390, by rfl⟩ : syracuseStep 2841041 = 2130781) B2130781
theorem B1894027 : Blo 1893435 1894027 := bstep (se 1 (by rfl) ⟨1420520, by rfl⟩ : syracuseStep 1894027 = 2841041) B2841041
theorem B6392357 : Blo 1893435 6392357 := bbase (se 4 (by rfl) ⟨599283, by rfl⟩ : syracuseStep 6392357 = 1198567) (by norm_num)
theorem B4261571 : Blo 1893435 4261571 := bstep (se 1 (by rfl) ⟨3196178, by rfl⟩ : syracuseStep 4261571 = 6392357) B6392357
theorem B2841047 : Blo 1893435 2841047 := bstep (se 1 (by rfl) ⟨2130785, by rfl⟩ : syracuseStep 2841047 = 4261571) B4261571
theorem B1894031 : Blo 1893435 1894031 := bstep (se 1 (by rfl) ⟨1420523, by rfl⟩ : syracuseStep 1894031 = 2841047) B2841047
theorem B2841053 : Blo 1893435 2841053 := bbase (se 3 (by rfl) ⟨532697, by rfl⟩ : syracuseStep 2841053 = 1065395) (by norm_num)
theorem B1894035 : Blo 1893435 1894035 := bstep (se 1 (by rfl) ⟨1420526, by rfl⟩ : syracuseStep 1894035 = 2841053) B2841053
theorem B4261589 : Blo 1893435 4261589 := bbase (se 7 (by rfl) ⟨49940, by rfl⟩ : syracuseStep 4261589 = 99881) (by norm_num)
theorem B2841059 : Blo 1893435 2841059 := bstep (se 1 (by rfl) ⟨2130794, by rfl⟩ : syracuseStep 2841059 = 4261589) B4261589
theorem B1894039 : Blo 1893435 1894039 := bstep (se 1 (by rfl) ⟨1420529, by rfl⟩ : syracuseStep 1894039 = 2841059) B2841059
theorem B3033893 : Blo 1893435 3033893 := bbase (se 4 (by rfl) ⟨284427, by rfl⟩ : syracuseStep 3033893 = 568855) (by norm_num)
theorem B8090381 : Blo 1893435 8090381 := bstep (se 3 (by rfl) ⟨1516946, by rfl⟩ : syracuseStep 8090381 = 3033893) B3033893
theorem B5393587 : Blo 1893435 5393587 := bstep (se 1 (by rfl) ⟨4045190, by rfl⟩ : syracuseStep 5393587 = 8090381) B8090381
theorem B7191449 : Blo 1893435 7191449 := bstep (se 2 (by rfl) ⟨2696793, by rfl⟩ : syracuseStep 7191449 = 5393587) B5393587
theorem B4794299 : Blo 1893435 4794299 := bstep (se 1 (by rfl) ⟨3595724, by rfl⟩ : syracuseStep 4794299 = 7191449) B7191449
theorem B3196199 : Blo 1893435 3196199 := bstep (se 1 (by rfl) ⟨2397149, by rfl⟩ : syracuseStep 3196199 = 4794299) B4794299
theorem B2130799 : Blo 1893435 2130799 := bstep (se 1 (by rfl) ⟨1598099, by rfl⟩ : syracuseStep 2130799 = 3196199) B3196199
theorem B2841065 : Blo 1893435 2841065 := bstep (se 2 (by rfl) ⟨1065399, by rfl⟩ : syracuseStep 2841065 = 2130799) B2130799
theorem B1894043 : Blo 1893435 1894043 := bstep (se 1 (by rfl) ⟨1420532, by rfl⟩ : syracuseStep 1894043 = 2841065) B2841065
theorem B7679557 : Blo 1893435 7679557 := bbase (se 4 (by rfl) ⟨719958, by rfl⟩ : syracuseStep 7679557 = 1439917) (by norm_num)
theorem B10239409 : Blo 1893435 10239409 := bstep (se 2 (by rfl) ⟨3839778, by rfl⟩ : syracuseStep 10239409 = 7679557) B7679557
theorem B13652545 : Blo 1893435 13652545 := bstep (se 2 (by rfl) ⟨5119704, by rfl⟩ : syracuseStep 13652545 = 10239409) B10239409
theorem B18203393 : Blo 1893435 18203393 := bstep (se 2 (by rfl) ⟨6826272, by rfl⟩ : syracuseStep 18203393 = 13652545) B13652545
theorem B12135595 : Blo 1893435 12135595 := bstep (se 1 (by rfl) ⟨9101696, by rfl⟩ : syracuseStep 12135595 = 18203393) B18203393
theorem B16180793 : Blo 1893435 16180793 := bstep (se 2 (by rfl) ⟨6067797, by rfl⟩ : syracuseStep 16180793 = 12135595) B12135595
theorem B10787195 : Blo 1893435 10787195 := bstep (se 1 (by rfl) ⟨8090396, by rfl⟩ : syracuseStep 10787195 = 16180793) B16180793
theorem B7191463 : Blo 1893435 7191463 := bstep (se 1 (by rfl) ⟨5393597, by rfl⟩ : syracuseStep 7191463 = 10787195) B10787195
theorem B9588617 : Blo 1893435 9588617 := bstep (se 2 (by rfl) ⟨3595731, by rfl⟩ : syracuseStep 9588617 = 7191463) B7191463
theorem B6392411 : Blo 1893435 6392411 := bstep (se 1 (by rfl) ⟨4794308, by rfl⟩ : syracuseStep 6392411 = 9588617) B9588617
theorem B4261607 : Blo 1893435 4261607 := bstep (se 1 (by rfl) ⟨3196205, by rfl⟩ : syracuseStep 4261607 = 6392411) B6392411
theorem B2841071 : Blo 1893435 2841071 := bstep (se 1 (by rfl) ⟨2130803, by rfl⟩ : syracuseStep 2841071 = 4261607) B4261607
theorem B1894047 : Blo 1893435 1894047 := bstep (se 1 (by rfl) ⟨1420535, by rfl⟩ : syracuseStep 1894047 = 2841071) B2841071
theorem B2841077 : Blo 1893435 2841077 := bbase (se 5 (by rfl) ⟨133175, by rfl⟩ : syracuseStep 2841077 = 266351) (by norm_num)
theorem B1894051 : Blo 1893435 1894051 := bstep (se 1 (by rfl) ⟨1420538, by rfl⟩ : syracuseStep 1894051 = 2841077) B2841077
theorem B5393621 : Blo 1893435 5393621 := bbase (se 7 (by rfl) ⟨63206, by rfl⟩ : syracuseStep 5393621 = 126413) (by norm_num)
theorem B3595747 : Blo 1893435 3595747 := bstep (se 1 (by rfl) ⟨2696810, by rfl⟩ : syracuseStep 3595747 = 5393621) B5393621
theorem B4794329 : Blo 1893435 4794329 := bstep (se 2 (by rfl) ⟨1797873, by rfl⟩ : syracuseStep 4794329 = 3595747) B3595747
theorem B3196219 : Blo 1893435 3196219 := bstep (se 1 (by rfl) ⟨2397164, by rfl⟩ : syracuseStep 3196219 = 4794329) B4794329
theorem B4261625 : Blo 1893435 4261625 := bstep (se 2 (by rfl) ⟨1598109, by rfl⟩ : syracuseStep 4261625 = 3196219) B3196219
theorem B2841083 : Blo 1893435 2841083 := bstep (se 1 (by rfl) ⟨2130812, by rfl⟩ : syracuseStep 2841083 = 4261625) B4261625
theorem B1894055 : Blo 1893435 1894055 := bstep (se 1 (by rfl) ⟨1420541, by rfl⟩ : syracuseStep 1894055 = 2841083) B2841083
theorem B2130817 : Blo 1893435 2130817 := bbase (se 2 (by rfl) ⟨799056, by rfl⟩ : syracuseStep 2130817 = 1598113) (by norm_num)
theorem B2841089 : Blo 1893435 2841089 := bstep (se 2 (by rfl) ⟨1065408, by rfl⟩ : syracuseStep 2841089 = 2130817) B2130817
theorem B1894059 : Blo 1893435 1894059 := bstep (se 1 (by rfl) ⟨1420544, by rfl⟩ : syracuseStep 1894059 = 2841089) B2841089
theorem B4794349 : Blo 1893435 4794349 := bbase (se 3 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 4794349 = 1797881) (by norm_num)
theorem B6392465 : Blo 1893435 6392465 := bstep (se 2 (by rfl) ⟨2397174, by rfl⟩ : syracuseStep 6392465 = 4794349) B4794349
theorem B4261643 : Blo 1893435 4261643 := bstep (se 1 (by rfl) ⟨3196232, by rfl⟩ : syracuseStep 4261643 = 6392465) B6392465
theorem B2841095 : Blo 1893435 2841095 := bstep (se 1 (by rfl) ⟨2130821, by rfl⟩ : syracuseStep 2841095 = 4261643) B4261643
theorem B1894063 : Blo 1893435 1894063 := bstep (se 1 (by rfl) ⟨1420547, by rfl⟩ : syracuseStep 1894063 = 2841095) B2841095
theorem B2841101 : Blo 1893435 2841101 := bbase (se 3 (by rfl) ⟨532706, by rfl⟩ : syracuseStep 2841101 = 1065413) (by norm_num)
theorem B1894067 : Blo 1893435 1894067 := bstep (se 1 (by rfl) ⟨1420550, by rfl⟩ : syracuseStep 1894067 = 2841101) B2841101
theorem B4261661 : Blo 1893435 4261661 := bbase (se 3 (by rfl) ⟨799061, by rfl⟩ : syracuseStep 4261661 = 1598123) (by norm_num)
theorem B2841107 : Blo 1893435 2841107 := bstep (se 1 (by rfl) ⟨2130830, by rfl⟩ : syracuseStep 2841107 = 4261661) B4261661
theorem B1894071 : Blo 1893435 1894071 := bstep (se 1 (by rfl) ⟨1420553, by rfl⟩ : syracuseStep 1894071 = 2841107) B2841107
theorem B3196253 : Blo 1893435 3196253 := bbase (se 3 (by rfl) ⟨599297, by rfl⟩ : syracuseStep 3196253 = 1198595) (by norm_num)
theorem B2130835 : Blo 1893435 2130835 := bstep (se 1 (by rfl) ⟨1598126, by rfl⟩ : syracuseStep 2130835 = 3196253) B3196253
theorem B2841113 : Blo 1893435 2841113 := bstep (se 2 (by rfl) ⟨1065417, by rfl⟩ : syracuseStep 2841113 = 2130835) B2130835
theorem B1894075 : Blo 1893435 1894075 := bstep (se 1 (by rfl) ⟨1420556, by rfl⟩ : syracuseStep 1894075 = 2841113) B2841113
theorem B8090533 : Blo 1893435 8090533 := bbase (se 4 (by rfl) ⟨758487, by rfl⟩ : syracuseStep 8090533 = 1516975) (by norm_num)
theorem B10787377 : Blo 1893435 10787377 := bstep (se 2 (by rfl) ⟨4045266, by rfl⟩ : syracuseStep 10787377 = 8090533) B8090533
theorem B14383169 : Blo 1893435 14383169 := bstep (se 2 (by rfl) ⟨5393688, by rfl⟩ : syracuseStep 14383169 = 10787377) B10787377
theorem B9588779 : Blo 1893435 9588779 := bstep (se 1 (by rfl) ⟨7191584, by rfl⟩ : syracuseStep 9588779 = 14383169) B14383169
theorem B6392519 : Blo 1893435 6392519 := bstep (se 1 (by rfl) ⟨4794389, by rfl⟩ : syracuseStep 6392519 = 9588779) B9588779
theorem B4261679 : Blo 1893435 4261679 := bstep (se 1 (by rfl) ⟨3196259, by rfl⟩ : syracuseStep 4261679 = 6392519) B6392519
theorem B2841119 : Blo 1893435 2841119 := bstep (se 1 (by rfl) ⟨2130839, by rfl⟩ : syracuseStep 2841119 = 4261679) B4261679
theorem B1894079 : Blo 1893435 1894079 := bstep (se 1 (by rfl) ⟨1420559, by rfl⟩ : syracuseStep 1894079 = 2841119) B2841119
theorem B2841125 : Blo 1893435 2841125 := bbase (se 4 (by rfl) ⟨266355, by rfl⟩ : syracuseStep 2841125 = 532711) (by norm_num)
theorem B1894083 : Blo 1893435 1894083 := bstep (se 1 (by rfl) ⟨1420562, by rfl⟩ : syracuseStep 1894083 = 2841125) B2841125
theorem B2397205 : Blo 1893435 2397205 := bbase (se 6 (by rfl) ⟨56184, by rfl⟩ : syracuseStep 2397205 = 112369) (by norm_num)
theorem B3196273 : Blo 1893435 3196273 := bstep (se 2 (by rfl) ⟨1198602, by rfl⟩ : syracuseStep 3196273 = 2397205) B2397205
theorem B4261697 : Blo 1893435 4261697 := bstep (se 2 (by rfl) ⟨1598136, by rfl⟩ : syracuseStep 4261697 = 3196273) B3196273
theorem B2841131 : Blo 1893435 2841131 := bstep (se 1 (by rfl) ⟨2130848, by rfl⟩ : syracuseStep 2841131 = 4261697) B4261697
theorem B1894087 : Blo 1893435 1894087 := bstep (se 1 (by rfl) ⟨1420565, by rfl⟩ : syracuseStep 1894087 = 2841131) B2841131
theorem B2130853 : Blo 1893435 2130853 := bbase (se 4 (by rfl) ⟨199767, by rfl⟩ : syracuseStep 2130853 = 399535) (by norm_num)
theorem B2841137 : Blo 1893435 2841137 := bstep (se 2 (by rfl) ⟨1065426, by rfl⟩ : syracuseStep 2841137 = 2130853) B2130853
theorem B1894091 : Blo 1893435 1894091 := bstep (se 1 (by rfl) ⟨1420568, by rfl⟩ : syracuseStep 1894091 = 2841137) B2841137
theorem B7784533 : Blo 1893435 7784533 := bbase (se 8 (by rfl) ⟨45612, by rfl⟩ : syracuseStep 7784533 = 91225) (by norm_num)
theorem B10379377 : Blo 1893435 10379377 := bstep (se 2 (by rfl) ⟨3892266, by rfl⟩ : syracuseStep 10379377 = 7784533) B7784533
theorem B13839169 : Blo 1893435 13839169 := bstep (se 2 (by rfl) ⟨5189688, by rfl⟩ : syracuseStep 13839169 = 10379377) B10379377
theorem B18452225 : Blo 1893435 18452225 := bstep (se 2 (by rfl) ⟨6919584, by rfl⟩ : syracuseStep 18452225 = 13839169) B13839169
theorem B12301483 : Blo 1893435 12301483 := bstep (se 1 (by rfl) ⟨9226112, by rfl⟩ : syracuseStep 12301483 = 18452225) B18452225
theorem B16401977 : Blo 1893435 16401977 := bstep (se 2 (by rfl) ⟨6150741, by rfl⟩ : syracuseStep 16401977 = 12301483) B12301483
theorem B10934651 : Blo 1893435 10934651 := bstep (se 1 (by rfl) ⟨8200988, by rfl⟩ : syracuseStep 10934651 = 16401977) B16401977
theorem B7289767 : Blo 1893435 7289767 := bstep (se 1 (by rfl) ⟨5467325, by rfl⟩ : syracuseStep 7289767 = 10934651) B10934651
theorem B9719689 : Blo 1893435 9719689 := bstep (se 2 (by rfl) ⟨3644883, by rfl⟩ : syracuseStep 9719689 = 7289767) B7289767
theorem B12959585 : Blo 1893435 12959585 := bstep (se 2 (by rfl) ⟨4859844, by rfl⟩ : syracuseStep 12959585 = 9719689) B9719689
theorem B8639723 : Blo 1893435 8639723 := bstep (se 1 (by rfl) ⟨6479792, by rfl⟩ : syracuseStep 8639723 = 12959585) B12959585
theorem B23039261 : Blo 1893435 23039261 := bstep (se 3 (by rfl) ⟨4319861, by rfl⟩ : syracuseStep 23039261 = 8639723) B8639723
theorem B15359507 : Blo 1893435 15359507 := bstep (se 1 (by rfl) ⟨11519630, by rfl⟩ : syracuseStep 15359507 = 23039261) B23039261
theorem B10239671 : Blo 1893435 10239671 := bstep (se 1 (by rfl) ⟨7679753, by rfl⟩ : syracuseStep 10239671 = 15359507) B15359507
theorem B6826447 : Blo 1893435 6826447 := bstep (se 1 (by rfl) ⟨5119835, by rfl⟩ : syracuseStep 6826447 = 10239671) B10239671
theorem B9101929 : Blo 1893435 9101929 := bstep (se 2 (by rfl) ⟨3413223, by rfl⟩ : syracuseStep 9101929 = 6826447) B6826447
theorem B12135905 : Blo 1893435 12135905 := bstep (se 2 (by rfl) ⟨4550964, by rfl⟩ : syracuseStep 12135905 = 9101929) B9101929
theorem B8090603 : Blo 1893435 8090603 := bstep (se 1 (by rfl) ⟨6067952, by rfl⟩ : syracuseStep 8090603 = 12135905) B12135905
theorem B5393735 : Blo 1893435 5393735 := bstep (se 1 (by rfl) ⟨4045301, by rfl⟩ : syracuseStep 5393735 = 8090603) B8090603
theorem B3595823 : Blo 1893435 3595823 := bstep (se 1 (by rfl) ⟨2696867, by rfl⟩ : syracuseStep 3595823 = 5393735) B5393735
theorem B2397215 : Blo 1893435 2397215 := bstep (se 1 (by rfl) ⟨1797911, by rfl⟩ : syracuseStep 2397215 = 3595823) B3595823
theorem B6392573 : Blo 1893435 6392573 := bstep (se 3 (by rfl) ⟨1198607, by rfl⟩ : syracuseStep 6392573 = 2397215) B2397215
theorem B4261715 : Blo 1893435 4261715 := bstep (se 1 (by rfl) ⟨3196286, by rfl⟩ : syracuseStep 4261715 = 6392573) B6392573
theorem B2841143 : Blo 1893435 2841143 := bstep (se 1 (by rfl) ⟨2130857, by rfl⟩ : syracuseStep 2841143 = 4261715) B4261715
theorem B1894095 : Blo 1893435 1894095 := bstep (se 1 (by rfl) ⟨1420571, by rfl⟩ : syracuseStep 1894095 = 2841143) B2841143
theorem B2841149 : Blo 1893435 2841149 := bbase (se 3 (by rfl) ⟨532715, by rfl⟩ : syracuseStep 2841149 = 1065431) (by norm_num)
theorem B1894099 : Blo 1893435 1894099 := bstep (se 1 (by rfl) ⟨1420574, by rfl⟩ : syracuseStep 1894099 = 2841149) B2841149
theorem B4261733 : Blo 1893435 4261733 := bbase (se 4 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 4261733 = 799075) (by norm_num)
theorem B2841155 : Blo 1893435 2841155 := bstep (se 1 (by rfl) ⟨2130866, by rfl⟩ : syracuseStep 2841155 = 4261733) B4261733
theorem B1894103 : Blo 1893435 1894103 := bstep (se 1 (by rfl) ⟨1420577, by rfl⟩ : syracuseStep 1894103 = 2841155) B2841155
theorem B4794461 : Blo 1893435 4794461 := bbase (se 3 (by rfl) ⟨898961, by rfl⟩ : syracuseStep 4794461 = 1797923) (by norm_num)
theorem B3196307 : Blo 1893435 3196307 := bstep (se 1 (by rfl) ⟨2397230, by rfl⟩ : syracuseStep 3196307 = 4794461) B4794461
theorem B2130871 : Blo 1893435 2130871 := bstep (se 1 (by rfl) ⟨1598153, by rfl⟩ : syracuseStep 2130871 = 3196307) B3196307
theorem B2841161 : Blo 1893435 2841161 := bstep (se 2 (by rfl) ⟨1065435, by rfl⟩ : syracuseStep 2841161 = 2130871) B2130871
theorem B1894107 : Blo 1893435 1894107 := bstep (se 1 (by rfl) ⟨1420580, by rfl⟩ : syracuseStep 1894107 = 2841161) B2841161
theorem B3595853 : Blo 1893435 3595853 := bbase (se 3 (by rfl) ⟨674222, by rfl⟩ : syracuseStep 3595853 = 1348445) (by norm_num)
theorem B9588941 : Blo 1893435 9588941 := bstep (se 3 (by rfl) ⟨1797926, by rfl⟩ : syracuseStep 9588941 = 3595853) B3595853
theorem B6392627 : Blo 1893435 6392627 := bstep (se 1 (by rfl) ⟨4794470, by rfl⟩ : syracuseStep 6392627 = 9588941) B9588941
theorem B4261751 : Blo 1893435 4261751 := bstep (se 1 (by rfl) ⟨3196313, by rfl⟩ : syracuseStep 4261751 = 6392627) B6392627
theorem B2841167 : Blo 1893435 2841167 := bstep (se 1 (by rfl) ⟨2130875, by rfl⟩ : syracuseStep 2841167 = 4261751) B4261751
theorem B1894111 : Blo 1893435 1894111 := bstep (se 1 (by rfl) ⟨1420583, by rfl⟩ : syracuseStep 1894111 = 2841167) B2841167
theorem B2841173 : Blo 1893435 2841173 := bbase (se 8 (by rfl) ⟨16647, by rfl⟩ : syracuseStep 2841173 = 33295) (by norm_num)
theorem B1894115 : Blo 1893435 1894115 := bstep (se 1 (by rfl) ⟨1420586, by rfl⟩ : syracuseStep 1894115 = 2841173) B2841173
theorem B4859909 : Blo 1893435 4859909 := bbase (se 4 (by rfl) ⟨455616, by rfl⟩ : syracuseStep 4859909 = 911233) (by norm_num)
theorem B3239939 : Blo 1893435 3239939 := bstep (se 1 (by rfl) ⟨2429954, by rfl⟩ : syracuseStep 3239939 = 4859909) B4859909
theorem B2159959 : Blo 1893435 2159959 := bstep (se 1 (by rfl) ⟨1619969, by rfl⟩ : syracuseStep 2159959 = 3239939) B3239939
theorem B2879945 : Blo 1893435 2879945 := bstep (se 2 (by rfl) ⟨1079979, by rfl⟩ : syracuseStep 2879945 = 2159959) B2159959
theorem B1919963 : Blo 1893435 1919963 := bstep (se 1 (by rfl) ⟨1439972, by rfl⟩ : syracuseStep 1919963 = 2879945) B2879945
theorem B5119901 : Blo 1893435 5119901 := bstep (se 3 (by rfl) ⟨959981, by rfl⟩ : syracuseStep 5119901 = 1919963) B1919963
theorem B3413267 : Blo 1893435 3413267 := bstep (se 1 (by rfl) ⟨2559950, by rfl⟩ : syracuseStep 3413267 = 5119901) B5119901
theorem B2275511 : Blo 1893435 2275511 := bstep (se 1 (by rfl) ⟨1706633, by rfl⟩ : syracuseStep 2275511 = 3413267) B3413267
theorem B6068029 : Blo 1893435 6068029 := bstep (se 3 (by rfl) ⟨1137755, by rfl⟩ : syracuseStep 6068029 = 2275511) B2275511
theorem B8090705 : Blo 1893435 8090705 := bstep (se 2 (by rfl) ⟨3034014, by rfl⟩ : syracuseStep 8090705 = 6068029) B6068029
theorem B5393803 : Blo 1893435 5393803 := bstep (se 1 (by rfl) ⟨4045352, by rfl⟩ : syracuseStep 5393803 = 8090705) B8090705
theorem B7191737 : Blo 1893435 7191737 := bstep (se 2 (by rfl) ⟨2696901, by rfl⟩ : syracuseStep 7191737 = 5393803) B5393803
theorem B4794491 : Blo 1893435 4794491 := bstep (se 1 (by rfl) ⟨3595868, by rfl⟩ : syracuseStep 4794491 = 7191737) B7191737
theorem B3196327 : Blo 1893435 3196327 := bstep (se 1 (by rfl) ⟨2397245, by rfl⟩ : syracuseStep 3196327 = 4794491) B4794491
theorem B4261769 : Blo 1893435 4261769 := bstep (se 2 (by rfl) ⟨1598163, by rfl⟩ : syracuseStep 4261769 = 3196327) B3196327
theorem B2841179 : Blo 1893435 2841179 := bstep (se 1 (by rfl) ⟨2130884, by rfl⟩ : syracuseStep 2841179 = 4261769) B4261769
theorem B1894119 : Blo 1893435 1894119 := bstep (se 1 (by rfl) ⟨1420589, by rfl⟩ : syracuseStep 1894119 = 2841179) B2841179
theorem B2130889 : Blo 1893435 2130889 := bbase (se 2 (by rfl) ⟨799083, by rfl⟩ : syracuseStep 2130889 = 1598167) (by norm_num)
theorem B2841185 : Blo 1893435 2841185 := bstep (se 2 (by rfl) ⟨1065444, by rfl⟩ : syracuseStep 2841185 = 2130889) B2130889
theorem B1894123 : Blo 1893435 1894123 := bstep (se 1 (by rfl) ⟨1420592, by rfl⟩ : syracuseStep 1894123 = 2841185) B2841185
theorem B2879957 : Blo 1893435 2879957 := bbase (se 7 (by rfl) ⟨33749, by rfl⟩ : syracuseStep 2879957 = 67499) (by norm_num)
theorem B1919971 : Blo 1893435 1919971 := bstep (se 1 (by rfl) ⟨1439978, by rfl⟩ : syracuseStep 1919971 = 2879957) B2879957
theorem B2559961 : Blo 1893435 2559961 := bstep (se 2 (by rfl) ⟨959985, by rfl⟩ : syracuseStep 2559961 = 1919971) B1919971
theorem B3413281 : Blo 1893435 3413281 := bstep (se 2 (by rfl) ⟨1279980, by rfl⟩ : syracuseStep 3413281 = 2559961) B2559961
theorem B4551041 : Blo 1893435 4551041 := bstep (se 2 (by rfl) ⟨1706640, by rfl⟩ : syracuseStep 4551041 = 3413281) B3413281
theorem B3034027 : Blo 1893435 3034027 := bstep (se 1 (by rfl) ⟨2275520, by rfl⟩ : syracuseStep 3034027 = 4551041) B4551041
theorem B16181477 : Blo 1893435 16181477 := bstep (se 4 (by rfl) ⟨1517013, by rfl⟩ : syracuseStep 16181477 = 3034027) B3034027
theorem B10787651 : Blo 1893435 10787651 := bstep (se 1 (by rfl) ⟨8090738, by rfl⟩ : syracuseStep 10787651 = 16181477) B16181477
theorem B7191767 : Blo 1893435 7191767 := bstep (se 1 (by rfl) ⟨5393825, by rfl⟩ : syracuseStep 7191767 = 10787651) B10787651
theorem B4794511 : Blo 1893435 4794511 := bstep (se 1 (by rfl) ⟨3595883, by rfl⟩ : syracuseStep 4794511 = 7191767) B7191767
theorem B6392681 : Blo 1893435 6392681 := bstep (se 2 (by rfl) ⟨2397255, by rfl⟩ : syracuseStep 6392681 = 4794511) B4794511
theorem B4261787 : Blo 1893435 4261787 := bstep (se 1 (by rfl) ⟨3196340, by rfl⟩ : syracuseStep 4261787 = 6392681) B6392681
theorem B2841191 : Blo 1893435 2841191 := bstep (se 1 (by rfl) ⟨2130893, by rfl⟩ : syracuseStep 2841191 = 4261787) B4261787
theorem B1894127 : Blo 1893435 1894127 := bstep (se 1 (by rfl) ⟨1420595, by rfl⟩ : syracuseStep 1894127 = 2841191) B2841191
theorem B2841197 : Blo 1893435 2841197 := bbase (se 3 (by rfl) ⟨532724, by rfl⟩ : syracuseStep 2841197 = 1065449) (by norm_num)
theorem B1894131 : Blo 1893435 1894131 := bstep (se 1 (by rfl) ⟨1420598, by rfl⟩ : syracuseStep 1894131 = 2841197) B2841197
theorem B4261805 : Blo 1893435 4261805 := bbase (se 3 (by rfl) ⟨799088, by rfl⟩ : syracuseStep 4261805 = 1598177) (by norm_num)
theorem B2841203 : Blo 1893435 2841203 := bstep (se 1 (by rfl) ⟨2130902, by rfl⟩ : syracuseStep 2841203 = 4261805) B4261805
theorem B1894135 : Blo 1893435 1894135 := bstep (se 1 (by rfl) ⟨1420601, by rfl⟩ : syracuseStep 1894135 = 2841203) B2841203
theorem B5393861 : Blo 1893435 5393861 := bbase (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) (by norm_num)
theorem B3595907 : Blo 1893435 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B2397271 : Blo 1893435 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B3196361 : Blo 1893435 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B2130907 : Blo 1893435 2130907 := bstep (se 1 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 2130907 = 3196361) B3196361
theorem B2841209 : Blo 1893435 2841209 := bstep (se 2 (by rfl) ⟨1065453, by rfl⟩ : syracuseStep 2841209 = 2130907) B2130907
theorem B1894139 : Blo 1893435 1894139 := bstep (se 1 (by rfl) ⟨1420604, by rfl⟩ : syracuseStep 1894139 = 2841209) B2841209
theorem B3413309 : Blo 1893435 3413309 := bbase (se 3 (by rfl) ⟨639995, by rfl⟩ : syracuseStep 3413309 = 1279991) (by norm_num)
theorem B36408629 : Blo 1893435 36408629 := bstep (se 5 (by rfl) ⟨1706654, by rfl⟩ : syracuseStep 36408629 = 3413309) B3413309
theorem B24272419 : Blo 1893435 24272419 := bstep (se 1 (by rfl) ⟨18204314, by rfl⟩ : syracuseStep 24272419 = 36408629) B36408629
theorem B32363225 : Blo 1893435 32363225 := bstep (se 2 (by rfl) ⟨12136209, by rfl⟩ : syracuseStep 32363225 = 24272419) B24272419
theorem B21575483 : Blo 1893435 21575483 := bstep (se 1 (by rfl) ⟨16181612, by rfl⟩ : syracuseStep 21575483 = 32363225) B32363225
theorem B14383655 : Blo 1893435 14383655 := bstep (se 1 (by rfl) ⟨10787741, by rfl⟩ : syracuseStep 14383655 = 21575483) B21575483
theorem B9589103 : Blo 1893435 9589103 := bstep (se 1 (by rfl) ⟨7191827, by rfl⟩ : syracuseStep 9589103 = 14383655) B14383655
theorem B6392735 : Blo 1893435 6392735 := bstep (se 1 (by rfl) ⟨4794551, by rfl⟩ : syracuseStep 6392735 = 9589103) B9589103
theorem B4261823 : Blo 1893435 4261823 := bstep (se 1 (by rfl) ⟨3196367, by rfl⟩ : syracuseStep 4261823 = 6392735) B6392735
theorem B2841215 : Blo 1893435 2841215 := bstep (se 1 (by rfl) ⟨2130911, by rfl⟩ : syracuseStep 2841215 = 4261823) B4261823
theorem B1894143 : Blo 1893435 1894143 := bstep (se 1 (by rfl) ⟨1420607, by rfl⟩ : syracuseStep 1894143 = 2841215) B2841215
theorem B2841221 : Blo 1893435 2841221 := bbase (se 4 (by rfl) ⟨266364, by rfl⟩ : syracuseStep 2841221 = 532729) (by norm_num)
theorem B1894147 : Blo 1893435 1894147 := bstep (se 1 (by rfl) ⟨1420610, by rfl⟩ : syracuseStep 1894147 = 2841221) B2841221
theorem B3196381 : Blo 1893435 3196381 := bbase (se 3 (by rfl) ⟨599321, by rfl⟩ : syracuseStep 3196381 = 1198643) (by norm_num)
theorem B4261841 : Blo 1893435 4261841 := bstep (se 2 (by rfl) ⟨1598190, by rfl⟩ : syracuseStep 4261841 = 3196381) B3196381
theorem B2841227 : Blo 1893435 2841227 := bstep (se 1 (by rfl) ⟨2130920, by rfl⟩ : syracuseStep 2841227 = 4261841) B4261841
theorem B1894151 : Blo 1893435 1894151 := bstep (se 1 (by rfl) ⟨1420613, by rfl⟩ : syracuseStep 1894151 = 2841227) B2841227
theorem B2130925 : Blo 1893435 2130925 := bbase (se 3 (by rfl) ⟨399548, by rfl⟩ : syracuseStep 2130925 = 799097) (by norm_num)
theorem B2841233 : Blo 1893435 2841233 := bstep (se 2 (by rfl) ⟨1065462, by rfl⟩ : syracuseStep 2841233 = 2130925) B2130925
theorem B1894155 : Blo 1893435 1894155 := bstep (se 1 (by rfl) ⟨1420616, by rfl⟩ : syracuseStep 1894155 = 2841233) B2841233
theorem B6392789 : Blo 1893435 6392789 := bbase (se 7 (by rfl) ⟨74915, by rfl⟩ : syracuseStep 6392789 = 149831) (by norm_num)
theorem B4261859 : Blo 1893435 4261859 := bstep (se 1 (by rfl) ⟨3196394, by rfl⟩ : syracuseStep 4261859 = 6392789) B6392789
theorem B2841239 : Blo 1893435 2841239 := bstep (se 1 (by rfl) ⟨2130929, by rfl⟩ : syracuseStep 2841239 = 4261859) B4261859
theorem B1894159 : Blo 1893435 1894159 := bstep (se 1 (by rfl) ⟨1420619, by rfl⟩ : syracuseStep 1894159 = 2841239) B2841239
theorem B2841245 : Blo 1893435 2841245 := bbase (se 3 (by rfl) ⟨532733, by rfl⟩ : syracuseStep 2841245 = 1065467) (by norm_num)
theorem B1894163 : Blo 1893435 1894163 := bstep (se 1 (by rfl) ⟨1420622, by rfl⟩ : syracuseStep 1894163 = 2841245) B2841245
theorem B4261877 : Blo 1893435 4261877 := bbase (se 5 (by rfl) ⟨199775, by rfl⟩ : syracuseStep 4261877 = 399551) (by norm_num)
theorem B2841251 : Blo 1893435 2841251 := bstep (se 1 (by rfl) ⟨2130938, by rfl⟩ : syracuseStep 2841251 = 4261877) B4261877
theorem B1894167 : Blo 1893435 1894167 := bstep (se 1 (by rfl) ⟨1420625, by rfl⟩ : syracuseStep 1894167 = 2841251) B2841251
theorem B1972765 : Blo 1893435 1972765 := bbase (se 3 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 1972765 = 739787) (by norm_num)
theorem B10521413 : Blo 1893435 10521413 := bstep (se 4 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 10521413 = 1972765) B1972765
theorem B7014275 : Blo 1893435 7014275 := bstep (se 1 (by rfl) ⟨5260706, by rfl⟩ : syracuseStep 7014275 = 10521413) B10521413
theorem B4676183 : Blo 1893435 4676183 := bstep (se 1 (by rfl) ⟨3507137, by rfl⟩ : syracuseStep 4676183 = 7014275) B7014275
theorem B3117455 : Blo 1893435 3117455 := bstep (se 1 (by rfl) ⟨2338091, by rfl⟩ : syracuseStep 3117455 = 4676183) B4676183
theorem B2078303 : Blo 1893435 2078303 := bstep (se 1 (by rfl) ⟨1558727, by rfl⟩ : syracuseStep 2078303 = 3117455) B3117455
theorem B5542141 : Blo 1893435 5542141 := bstep (se 3 (by rfl) ⟨1039151, by rfl⟩ : syracuseStep 5542141 = 2078303) B2078303
theorem B7389521 : Blo 1893435 7389521 := bstep (se 2 (by rfl) ⟨2771070, by rfl⟩ : syracuseStep 7389521 = 5542141) B5542141
theorem B4926347 : Blo 1893435 4926347 := bstep (se 1 (by rfl) ⟨3694760, by rfl⟩ : syracuseStep 4926347 = 7389521) B7389521
theorem B3284231 : Blo 1893435 3284231 := bstep (se 1 (by rfl) ⟨2463173, by rfl⟩ : syracuseStep 3284231 = 4926347) B4926347
theorem B8757949 : Blo 1893435 8757949 := bstep (se 3 (by rfl) ⟨1642115, by rfl⟩ : syracuseStep 8757949 = 3284231) B3284231
theorem B11677265 : Blo 1893435 11677265 := bstep (se 2 (by rfl) ⟨4378974, by rfl⟩ : syracuseStep 11677265 = 8757949) B8757949
theorem B7784843 : Blo 1893435 7784843 := bstep (se 1 (by rfl) ⟨5838632, by rfl⟩ : syracuseStep 7784843 = 11677265) B11677265
theorem B20759581 : Blo 1893435 20759581 := bstep (se 3 (by rfl) ⟨3892421, by rfl⟩ : syracuseStep 20759581 = 7784843) B7784843
theorem B110717765 : Blo 1893435 110717765 := bstep (se 4 (by rfl) ⟨10379790, by rfl⟩ : syracuseStep 110717765 = 20759581) B20759581
theorem B73811843 : Blo 1893435 73811843 := bstep (se 1 (by rfl) ⟨55358882, by rfl⟩ : syracuseStep 73811843 = 110717765) B110717765
theorem B49207895 : Blo 1893435 49207895 := bstep (se 1 (by rfl) ⟨36905921, by rfl⟩ : syracuseStep 49207895 = 73811843) B73811843
theorem B32805263 : Blo 1893435 32805263 := bstep (se 1 (by rfl) ⟨24603947, by rfl⟩ : syracuseStep 32805263 = 49207895) B49207895
theorem B21870175 : Blo 1893435 21870175 := bstep (se 1 (by rfl) ⟨16402631, by rfl⟩ : syracuseStep 21870175 = 32805263) B32805263
theorem B29160233 : Blo 1893435 29160233 := bstep (se 2 (by rfl) ⟨10935087, by rfl⟩ : syracuseStep 29160233 = 21870175) B21870175
theorem B19440155 : Blo 1893435 19440155 := bstep (se 1 (by rfl) ⟨14580116, by rfl⟩ : syracuseStep 19440155 = 29160233) B29160233
theorem B12960103 : Blo 1893435 12960103 := bstep (se 1 (by rfl) ⟨9720077, by rfl⟩ : syracuseStep 12960103 = 19440155) B19440155
theorem B17280137 : Blo 1893435 17280137 := bstep (se 2 (by rfl) ⟨6480051, by rfl⟩ : syracuseStep 17280137 = 12960103) B12960103
theorem B11520091 : Blo 1893435 11520091 := bstep (se 1 (by rfl) ⟨8640068, by rfl⟩ : syracuseStep 11520091 = 17280137) B17280137
theorem B15360121 : Blo 1893435 15360121 := bstep (se 2 (by rfl) ⟨5760045, by rfl⟩ : syracuseStep 15360121 = 11520091) B11520091
theorem B81920645 : Blo 1893435 81920645 := bstep (se 4 (by rfl) ⟨7680060, by rfl⟩ : syracuseStep 81920645 = 15360121) B15360121
theorem B54613763 : Blo 1893435 54613763 := bstep (se 1 (by rfl) ⟨40960322, by rfl⟩ : syracuseStep 54613763 = 81920645) B81920645
theorem B36409175 : Blo 1893435 36409175 := bstep (se 1 (by rfl) ⟨27306881, by rfl⟩ : syracuseStep 36409175 = 54613763) B54613763
theorem B24272783 : Blo 1893435 24272783 := bstep (se 1 (by rfl) ⟨18204587, by rfl⟩ : syracuseStep 24272783 = 36409175) B36409175
theorem B16181855 : Blo 1893435 16181855 := bstep (se 1 (by rfl) ⟨12136391, by rfl⟩ : syracuseStep 16181855 = 24272783) B24272783
theorem B10787903 : Blo 1893435 10787903 := bstep (se 1 (by rfl) ⟨8090927, by rfl⟩ : syracuseStep 10787903 = 16181855) B16181855
theorem B7191935 : Blo 1893435 7191935 := bstep (se 1 (by rfl) ⟨5393951, by rfl⟩ : syracuseStep 7191935 = 10787903) B10787903
theorem B4794623 : Blo 1893435 4794623 := bstep (se 1 (by rfl) ⟨3595967, by rfl⟩ : syracuseStep 4794623 = 7191935) B7191935
theorem B3196415 : Blo 1893435 3196415 := bstep (se 1 (by rfl) ⟨2397311, by rfl⟩ : syracuseStep 3196415 = 4794623) B4794623
theorem B2130943 : Blo 1893435 2130943 := bstep (se 1 (by rfl) ⟨1598207, by rfl⟩ : syracuseStep 2130943 = 3196415) B3196415
theorem B2841257 : Blo 1893435 2841257 := bstep (se 2 (by rfl) ⟨1065471, by rfl⟩ : syracuseStep 2841257 = 2130943) B2130943
theorem B1894171 : Blo 1893435 1894171 := bstep (se 1 (by rfl) ⟨1420628, by rfl⟩ : syracuseStep 1894171 = 2841257) B2841257
theorem B2696981 : Blo 1893435 2696981 := bbase (se 6 (by rfl) ⟨63210, by rfl⟩ : syracuseStep 2696981 = 126421) (by norm_num)
theorem B7191949 : Blo 1893435 7191949 := bstep (se 3 (by rfl) ⟨1348490, by rfl⟩ : syracuseStep 7191949 = 2696981) B2696981
theorem B9589265 : Blo 1893435 9589265 := bstep (se 2 (by rfl) ⟨3595974, by rfl⟩ : syracuseStep 9589265 = 7191949) B7191949
theorem B6392843 : Blo 1893435 6392843 := bstep (se 1 (by rfl) ⟨4794632, by rfl⟩ : syracuseStep 6392843 = 9589265) B9589265
theorem B4261895 : Blo 1893435 4261895 := bstep (se 1 (by rfl) ⟨3196421, by rfl⟩ : syracuseStep 4261895 = 6392843) B6392843
theorem B2841263 : Blo 1893435 2841263 := bstep (se 1 (by rfl) ⟨2130947, by rfl⟩ : syracuseStep 2841263 = 4261895) B4261895
theorem B1894175 : Blo 1893435 1894175 := bstep (se 1 (by rfl) ⟨1420631, by rfl⟩ : syracuseStep 1894175 = 2841263) B2841263
theorem B2841269 : Blo 1893435 2841269 := bbase (se 5 (by rfl) ⟨133184, by rfl⟩ : syracuseStep 2841269 = 266369) (by norm_num)
theorem B1894179 : Blo 1893435 1894179 := bstep (se 1 (by rfl) ⟨1420634, by rfl⟩ : syracuseStep 1894179 = 2841269) B2841269
theorem B4794653 : Blo 1893435 4794653 := bbase (se 3 (by rfl) ⟨898997, by rfl⟩ : syracuseStep 4794653 = 1797995) (by norm_num)
theorem B3196435 : Blo 1893435 3196435 := bstep (se 1 (by rfl) ⟨2397326, by rfl⟩ : syracuseStep 3196435 = 4794653) B4794653
theorem B4261913 : Blo 1893435 4261913 := bstep (se 2 (by rfl) ⟨1598217, by rfl⟩ : syracuseStep 4261913 = 3196435) B3196435
theorem B2841275 : Blo 1893435 2841275 := bstep (se 1 (by rfl) ⟨2130956, by rfl⟩ : syracuseStep 2841275 = 4261913) B4261913
theorem B1894183 : Blo 1893435 1894183 := bstep (se 1 (by rfl) ⟨1420637, by rfl⟩ : syracuseStep 1894183 = 2841275) B2841275
theorem B2130961 : Blo 1893435 2130961 := bbase (se 2 (by rfl) ⟨799110, by rfl⟩ : syracuseStep 2130961 = 1598221) (by norm_num)
theorem B2841281 : Blo 1893435 2841281 := bstep (se 2 (by rfl) ⟨1065480, by rfl⟩ : syracuseStep 2841281 = 2130961) B2130961
theorem B1894187 : Blo 1893435 1894187 := bstep (se 1 (by rfl) ⟨1420640, by rfl⟩ : syracuseStep 1894187 = 2841281) B2841281
theorem B3596005 : Blo 1893435 3596005 := bbase (se 4 (by rfl) ⟨337125, by rfl⟩ : syracuseStep 3596005 = 674251) (by norm_num)
theorem B4794673 : Blo 1893435 4794673 := bstep (se 2 (by rfl) ⟨1798002, by rfl⟩ : syracuseStep 4794673 = 3596005) B3596005
theorem B6392897 : Blo 1893435 6392897 := bstep (se 2 (by rfl) ⟨2397336, by rfl⟩ : syracuseStep 6392897 = 4794673) B4794673
theorem B4261931 : Blo 1893435 4261931 := bstep (se 1 (by rfl) ⟨3196448, by rfl⟩ : syracuseStep 4261931 = 6392897) B6392897
theorem B2841287 : Blo 1893435 2841287 := bstep (se 1 (by rfl) ⟨2130965, by rfl⟩ : syracuseStep 2841287 = 4261931) B4261931
theorem B1894191 : Blo 1893435 1894191 := bstep (se 1 (by rfl) ⟨1420643, by rfl⟩ : syracuseStep 1894191 = 2841287) B2841287
theorem B2841293 : Blo 1893435 2841293 := bbase (se 3 (by rfl) ⟨532742, by rfl⟩ : syracuseStep 2841293 = 1065485) (by norm_num)
theorem B1894195 : Blo 1893435 1894195 := bstep (se 1 (by rfl) ⟨1420646, by rfl⟩ : syracuseStep 1894195 = 2841293) B2841293
theorem B4261949 : Blo 1893435 4261949 := bbase (se 3 (by rfl) ⟨799115, by rfl⟩ : syracuseStep 4261949 = 1598231) (by norm_num)
theorem B2841299 : Blo 1893435 2841299 := bstep (se 1 (by rfl) ⟨2130974, by rfl⟩ : syracuseStep 2841299 = 4261949) B4261949
theorem B1894199 : Blo 1893435 1894199 := bstep (se 1 (by rfl) ⟨1420649, by rfl⟩ : syracuseStep 1894199 = 2841299) B2841299
theorem B3196469 : Blo 1893435 3196469 := bbase (se 5 (by rfl) ⟨149834, by rfl⟩ : syracuseStep 3196469 = 299669) (by norm_num)
theorem B2130979 : Blo 1893435 2130979 := bstep (se 1 (by rfl) ⟨1598234, by rfl⟩ : syracuseStep 2130979 = 3196469) B3196469
theorem B2841305 : Blo 1893435 2841305 := bstep (se 2 (by rfl) ⟨1065489, by rfl⟩ : syracuseStep 2841305 = 2130979) B2130979
theorem B1894203 : Blo 1893435 1894203 := bstep (se 1 (by rfl) ⟨1420652, by rfl⟩ : syracuseStep 1894203 = 2841305) B2841305
theorem B5394053 : Blo 1893435 5394053 := bbase (se 4 (by rfl) ⟨505692, by rfl⟩ : syracuseStep 5394053 = 1011385) (by norm_num)
theorem B14384141 : Blo 1893435 14384141 := bstep (se 3 (by rfl) ⟨2697026, by rfl⟩ : syracuseStep 14384141 = 5394053) B5394053
theorem B9589427 : Blo 1893435 9589427 := bstep (se 1 (by rfl) ⟨7192070, by rfl⟩ : syracuseStep 9589427 = 14384141) B14384141
theorem B6392951 : Blo 1893435 6392951 := bstep (se 1 (by rfl) ⟨4794713, by rfl⟩ : syracuseStep 6392951 = 9589427) B9589427
theorem B4261967 : Blo 1893435 4261967 := bstep (se 1 (by rfl) ⟨3196475, by rfl⟩ : syracuseStep 4261967 = 6392951) B6392951
theorem B2841311 : Blo 1893435 2841311 := bstep (se 1 (by rfl) ⟨2130983, by rfl⟩ : syracuseStep 2841311 = 4261967) B4261967
theorem B1894207 : Blo 1893435 1894207 := bstep (se 1 (by rfl) ⟨1420655, by rfl⟩ : syracuseStep 1894207 = 2841311) B2841311
theorem B2841317 : Blo 1893435 2841317 := bbase (se 4 (by rfl) ⟨266373, by rfl⟩ : syracuseStep 2841317 = 532747) (by norm_num)
theorem B1894211 : Blo 1893435 1894211 := bstep (se 1 (by rfl) ⟨1420658, by rfl⟩ : syracuseStep 1894211 = 2841317) B2841317
theorem B1920061 : Blo 1893435 1920061 := bbase (se 3 (by rfl) ⟨360011, by rfl⟩ : syracuseStep 1920061 = 720023) (by norm_num)
theorem B2560081 : Blo 1893435 2560081 := bstep (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) B1920061
theorem B3413441 : Blo 1893435 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B2275627 : Blo 1893435 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B3034169 : Blo 1893435 3034169 := bstep (se 2 (by rfl) ⟨1137813, by rfl⟩ : syracuseStep 3034169 = 2275627) B2275627
theorem B2022779 : Blo 1893435 2022779 := bstep (se 1 (by rfl) ⟨1517084, by rfl⟩ : syracuseStep 2022779 = 3034169) B3034169
theorem B5394077 : Blo 1893435 5394077 := bstep (se 3 (by rfl) ⟨1011389, by rfl⟩ : syracuseStep 5394077 = 2022779) B2022779
theorem B3596051 : Blo 1893435 3596051 := bstep (se 1 (by rfl) ⟨2697038, by rfl⟩ : syracuseStep 3596051 = 5394077) B5394077
theorem B2397367 : Blo 1893435 2397367 := bstep (se 1 (by rfl) ⟨1798025, by rfl⟩ : syracuseStep 2397367 = 3596051) B3596051
theorem B3196489 : Blo 1893435 3196489 := bstep (se 2 (by rfl) ⟨1198683, by rfl⟩ : syracuseStep 3196489 = 2397367) B2397367
theorem B4261985 : Blo 1893435 4261985 := bstep (se 2 (by rfl) ⟨1598244, by rfl⟩ : syracuseStep 4261985 = 3196489) B3196489
theorem B2841323 : Blo 1893435 2841323 := bstep (se 1 (by rfl) ⟨2130992, by rfl⟩ : syracuseStep 2841323 = 4261985) B4261985
theorem B1894215 : Blo 1893435 1894215 := bstep (se 1 (by rfl) ⟨1420661, by rfl⟩ : syracuseStep 1894215 = 2841323) B2841323
theorem B2130997 : Blo 1893435 2130997 := bbase (se 5 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 2130997 = 199781) (by norm_num)
theorem B2841329 : Blo 1893435 2841329 := bstep (se 2 (by rfl) ⟨1065498, by rfl⟩ : syracuseStep 2841329 = 2130997) B2130997
theorem B1894219 : Blo 1893435 1894219 := bstep (se 1 (by rfl) ⟨1420664, by rfl⟩ : syracuseStep 1894219 = 2841329) B2841329
theorem B2397377 : Blo 1893435 2397377 := bbase (se 2 (by rfl) ⟨899016, by rfl⟩ : syracuseStep 2397377 = 1798033) (by norm_num)
theorem B6393005 : Blo 1893435 6393005 := bstep (se 3 (by rfl) ⟨1198688, by rfl⟩ : syracuseStep 6393005 = 2397377) B2397377
theorem B4262003 : Blo 1893435 4262003 := bstep (se 1 (by rfl) ⟨3196502, by rfl⟩ : syracuseStep 4262003 = 6393005) B6393005
theorem B2841335 : Blo 1893435 2841335 := bstep (se 1 (by rfl) ⟨2131001, by rfl⟩ : syracuseStep 2841335 = 4262003) B4262003
theorem B1894223 : Blo 1893435 1894223 := bstep (se 1 (by rfl) ⟨1420667, by rfl⟩ : syracuseStep 1894223 = 2841335) B2841335
theorem B2841341 : Blo 1893435 2841341 := bbase (se 3 (by rfl) ⟨532751, by rfl⟩ : syracuseStep 2841341 = 1065503) (by norm_num)
theorem B1894227 : Blo 1893435 1894227 := bstep (se 1 (by rfl) ⟨1420670, by rfl⟩ : syracuseStep 1894227 = 2841341) B2841341
theorem B4262021 : Blo 1893435 4262021 := bbase (se 4 (by rfl) ⟨399564, by rfl⟩ : syracuseStep 4262021 = 799129) (by norm_num)
theorem B2841347 : Blo 1893435 2841347 := bstep (se 1 (by rfl) ⟨2131010, by rfl⟩ : syracuseStep 2841347 = 4262021) B4262021
theorem B1894231 : Blo 1893435 1894231 := bstep (se 1 (by rfl) ⟨1420673, by rfl⟩ : syracuseStep 1894231 = 2841347) B2841347
theorem B3413477 : Blo 1893435 3413477 := bbase (se 4 (by rfl) ⟨320013, by rfl⟩ : syracuseStep 3413477 = 640027) (by norm_num)
theorem B2275651 : Blo 1893435 2275651 := bstep (se 1 (by rfl) ⟨1706738, by rfl⟩ : syracuseStep 2275651 = 3413477) B3413477
theorem B3034201 : Blo 1893435 3034201 := bstep (se 2 (by rfl) ⟨1137825, by rfl⟩ : syracuseStep 3034201 = 2275651) B2275651
theorem B4045601 : Blo 1893435 4045601 := bstep (se 2 (by rfl) ⟨1517100, by rfl⟩ : syracuseStep 4045601 = 3034201) B3034201
theorem B2697067 : Blo 1893435 2697067 := bstep (se 1 (by rfl) ⟨2022800, by rfl⟩ : syracuseStep 2697067 = 4045601) B4045601
theorem B3596089 : Blo 1893435 3596089 := bstep (se 2 (by rfl) ⟨1348533, by rfl⟩ : syracuseStep 3596089 = 2697067) B2697067
theorem B4794785 : Blo 1893435 4794785 := bstep (se 2 (by rfl) ⟨1798044, by rfl⟩ : syracuseStep 4794785 = 3596089) B3596089
theorem B3196523 : Blo 1893435 3196523 := bstep (se 1 (by rfl) ⟨2397392, by rfl⟩ : syracuseStep 3196523 = 4794785) B4794785
theorem B2131015 : Blo 1893435 2131015 := bstep (se 1 (by rfl) ⟨1598261, by rfl⟩ : syracuseStep 2131015 = 3196523) B3196523
theorem B2841353 : Blo 1893435 2841353 := bstep (se 2 (by rfl) ⟨1065507, by rfl⟩ : syracuseStep 2841353 = 2131015) B2131015
theorem B1894235 : Blo 1893435 1894235 := bstep (se 1 (by rfl) ⟨1420676, by rfl⟩ : syracuseStep 1894235 = 2841353) B2841353
theorem B9589589 : Blo 1893435 9589589 := bbase (se 9 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 9589589 = 56189) (by norm_num)
theorem B6393059 : Blo 1893435 6393059 := bstep (se 1 (by rfl) ⟨4794794, by rfl⟩ : syracuseStep 6393059 = 9589589) B9589589
theorem B4262039 : Blo 1893435 4262039 := bstep (se 1 (by rfl) ⟨3196529, by rfl⟩ : syracuseStep 4262039 = 6393059) B6393059
theorem B2841359 : Blo 1893435 2841359 := bstep (se 1 (by rfl) ⟨2131019, by rfl⟩ : syracuseStep 2841359 = 4262039) B4262039
theorem B1894239 : Blo 1893435 1894239 := bstep (se 1 (by rfl) ⟨1420679, by rfl⟩ : syracuseStep 1894239 = 2841359) B2841359
theorem B2841365 : Blo 1893435 2841365 := bbase (se 6 (by rfl) ⟨66594, by rfl⟩ : syracuseStep 2841365 = 133189) (by norm_num)
theorem B1894243 : Blo 1893435 1894243 := bstep (se 1 (by rfl) ⟨1420682, by rfl⟩ : syracuseStep 1894243 = 2841365) B2841365
theorem B3694909 : Blo 1893435 3694909 := bbase (se 3 (by rfl) ⟨692795, by rfl⟩ : syracuseStep 3694909 = 1385591) (by norm_num)
theorem B4926545 : Blo 1893435 4926545 := bstep (se 2 (by rfl) ⟨1847454, by rfl⟩ : syracuseStep 4926545 = 3694909) B3694909
theorem B3284363 : Blo 1893435 3284363 := bstep (se 1 (by rfl) ⟨2463272, by rfl⟩ : syracuseStep 3284363 = 4926545) B4926545
theorem B2189575 : Blo 1893435 2189575 := bstep (se 1 (by rfl) ⟨1642181, by rfl⟩ : syracuseStep 2189575 = 3284363) B3284363
theorem B11677733 : Blo 1893435 11677733 := bstep (se 4 (by rfl) ⟨1094787, by rfl⟩ : syracuseStep 11677733 = 2189575) B2189575
theorem B7785155 : Blo 1893435 7785155 := bstep (se 1 (by rfl) ⟨5838866, by rfl⟩ : syracuseStep 7785155 = 11677733) B11677733
theorem B5190103 : Blo 1893435 5190103 := bstep (se 1 (by rfl) ⟨3892577, by rfl⟩ : syracuseStep 5190103 = 7785155) B7785155
theorem B6920137 : Blo 1893435 6920137 := bstep (se 2 (by rfl) ⟨2595051, by rfl⟩ : syracuseStep 6920137 = 5190103) B5190103
theorem B36907397 : Blo 1893435 36907397 := bstep (se 4 (by rfl) ⟨3460068, by rfl⟩ : syracuseStep 36907397 = 6920137) B6920137
theorem B24604931 : Blo 1893435 24604931 := bstep (se 1 (by rfl) ⟨18453698, by rfl⟩ : syracuseStep 24604931 = 36907397) B36907397
theorem B65613149 : Blo 1893435 65613149 := bstep (se 3 (by rfl) ⟨12302465, by rfl⟩ : syracuseStep 65613149 = 24604931) B24604931
theorem B43742099 : Blo 1893435 43742099 := bstep (se 1 (by rfl) ⟨32806574, by rfl⟩ : syracuseStep 43742099 = 65613149) B65613149
theorem B29161399 : Blo 1893435 29161399 := bstep (se 1 (by rfl) ⟨21871049, by rfl⟩ : syracuseStep 29161399 = 43742099) B43742099
theorem B38881865 : Blo 1893435 38881865 := bstep (se 2 (by rfl) ⟨14580699, by rfl⟩ : syracuseStep 38881865 = 29161399) B29161399
theorem B25921243 : Blo 1893435 25921243 := bstep (se 1 (by rfl) ⟨19440932, by rfl⟩ : syracuseStep 25921243 = 38881865) B38881865
theorem B34561657 : Blo 1893435 34561657 := bstep (se 2 (by rfl) ⟨12960621, by rfl⟩ : syracuseStep 34561657 = 25921243) B25921243
theorem B46082209 : Blo 1893435 46082209 := bstep (se 2 (by rfl) ⟨17280828, by rfl⟩ : syracuseStep 46082209 = 34561657) B34561657
theorem B61442945 : Blo 1893435 61442945 := bstep (se 2 (by rfl) ⟨23041104, by rfl⟩ : syracuseStep 61442945 = 46082209) B46082209
theorem B40961963 : Blo 1893435 40961963 := bstep (se 1 (by rfl) ⟨30721472, by rfl⟩ : syracuseStep 40961963 = 61442945) B61442945
theorem B27307975 : Blo 1893435 27307975 := bstep (se 1 (by rfl) ⟨20480981, by rfl⟩ : syracuseStep 27307975 = 40961963) B40961963
theorem B36410633 : Blo 1893435 36410633 := bstep (se 2 (by rfl) ⟨13653987, by rfl⟩ : syracuseStep 36410633 = 27307975) B27307975
theorem B24273755 : Blo 1893435 24273755 := bstep (se 1 (by rfl) ⟨18205316, by rfl⟩ : syracuseStep 24273755 = 36410633) B36410633
theorem B16182503 : Blo 1893435 16182503 := bstep (se 1 (by rfl) ⟨12136877, by rfl⟩ : syracuseStep 16182503 = 24273755) B24273755
theorem B10788335 : Blo 1893435 10788335 := bstep (se 1 (by rfl) ⟨8091251, by rfl⟩ : syracuseStep 10788335 = 16182503) B16182503
theorem B7192223 : Blo 1893435 7192223 := bstep (se 1 (by rfl) ⟨5394167, by rfl⟩ : syracuseStep 7192223 = 10788335) B10788335
theorem B4794815 : Blo 1893435 4794815 := bstep (se 1 (by rfl) ⟨3596111, by rfl⟩ : syracuseStep 4794815 = 7192223) B7192223
theorem B3196543 : Blo 1893435 3196543 := bstep (se 1 (by rfl) ⟨2397407, by rfl⟩ : syracuseStep 3196543 = 4794815) B4794815
theorem B4262057 : Blo 1893435 4262057 := bstep (se 2 (by rfl) ⟨1598271, by rfl⟩ : syracuseStep 4262057 = 3196543) B3196543
theorem B2841371 : Blo 1893435 2841371 := bstep (se 1 (by rfl) ⟨2131028, by rfl⟩ : syracuseStep 2841371 = 4262057) B4262057
theorem B1894247 : Blo 1893435 1894247 := bstep (se 1 (by rfl) ⟨1420685, by rfl⟩ : syracuseStep 1894247 = 2841371) B2841371
theorem B2131033 : Blo 1893435 2131033 := bbase (se 2 (by rfl) ⟨799137, by rfl⟩ : syracuseStep 2131033 = 1598275) (by norm_num)
theorem B2841377 : Blo 1893435 2841377 := bstep (se 2 (by rfl) ⟨1065516, by rfl⟩ : syracuseStep 2841377 = 2131033) B2131033
theorem B1894251 : Blo 1893435 1894251 := bstep (se 1 (by rfl) ⟨1420688, by rfl⟩ : syracuseStep 1894251 = 2841377) B2841377
theorem B4551349 : Blo 1893435 4551349 := bbase (se 5 (by rfl) ⟨213344, by rfl⟩ : syracuseStep 4551349 = 426689) (by norm_num)
theorem B6068465 : Blo 1893435 6068465 := bstep (se 2 (by rfl) ⟨2275674, by rfl⟩ : syracuseStep 6068465 = 4551349) B4551349
theorem B4045643 : Blo 1893435 4045643 := bstep (se 1 (by rfl) ⟨3034232, by rfl⟩ : syracuseStep 4045643 = 6068465) B6068465
theorem B2697095 : Blo 1893435 2697095 := bstep (se 1 (by rfl) ⟨2022821, by rfl⟩ : syracuseStep 2697095 = 4045643) B4045643
theorem B7192253 : Blo 1893435 7192253 := bstep (se 3 (by rfl) ⟨1348547, by rfl⟩ : syracuseStep 7192253 = 2697095) B2697095
theorem B4794835 : Blo 1893435 4794835 := bstep (se 1 (by rfl) ⟨3596126, by rfl⟩ : syracuseStep 4794835 = 7192253) B7192253
theorem B6393113 : Blo 1893435 6393113 := bstep (se 2 (by rfl) ⟨2397417, by rfl⟩ : syracuseStep 6393113 = 4794835) B4794835
theorem B4262075 : Blo 1893435 4262075 := bstep (se 1 (by rfl) ⟨3196556, by rfl⟩ : syracuseStep 4262075 = 6393113) B6393113
theorem B2841383 : Blo 1893435 2841383 := bstep (se 1 (by rfl) ⟨2131037, by rfl⟩ : syracuseStep 2841383 = 4262075) B4262075
theorem B1894255 : Blo 1893435 1894255 := bstep (se 1 (by rfl) ⟨1420691, by rfl⟩ : syracuseStep 1894255 = 2841383) B2841383
theorem B2841389 : Blo 1893435 2841389 := bbase (se 3 (by rfl) ⟨532760, by rfl⟩ : syracuseStep 2841389 = 1065521) (by norm_num)
theorem B1894259 : Blo 1893435 1894259 := bstep (se 1 (by rfl) ⟨1420694, by rfl⟩ : syracuseStep 1894259 = 2841389) B2841389
theorem B4262093 : Blo 1893435 4262093 := bbase (se 3 (by rfl) ⟨799142, by rfl⟩ : syracuseStep 4262093 = 1598285) (by norm_num)
theorem B2841395 : Blo 1893435 2841395 := bstep (se 1 (by rfl) ⟨2131046, by rfl⟩ : syracuseStep 2841395 = 4262093) B4262093
theorem B1894263 : Blo 1893435 1894263 := bstep (se 1 (by rfl) ⟨1420697, by rfl⟩ : syracuseStep 1894263 = 2841395) B2841395
theorem B2397433 : Blo 1893435 2397433 := bbase (se 2 (by rfl) ⟨899037, by rfl⟩ : syracuseStep 2397433 = 1798075) (by norm_num)
theorem B3196577 : Blo 1893435 3196577 := bstep (se 2 (by rfl) ⟨1198716, by rfl⟩ : syracuseStep 3196577 = 2397433) B2397433
theorem B2131051 : Blo 1893435 2131051 := bstep (se 1 (by rfl) ⟨1598288, by rfl⟩ : syracuseStep 2131051 = 3196577) B3196577
theorem B2841401 : Blo 1893435 2841401 := bstep (se 2 (by rfl) ⟨1065525, by rfl⟩ : syracuseStep 2841401 = 2131051) B2131051
theorem B1894267 : Blo 1893435 1894267 := bstep (se 1 (by rfl) ⟨1420700, by rfl⟩ : syracuseStep 1894267 = 2841401) B2841401
theorem B9102773 : Blo 1893435 9102773 := bbase (se 5 (by rfl) ⟨426692, by rfl⟩ : syracuseStep 9102773 = 853385) (by norm_num)
theorem B6068515 : Blo 1893435 6068515 := bstep (se 1 (by rfl) ⟨4551386, by rfl⟩ : syracuseStep 6068515 = 9102773) B9102773
theorem B8091353 : Blo 1893435 8091353 := bstep (se 2 (by rfl) ⟨3034257, by rfl⟩ : syracuseStep 8091353 = 6068515) B6068515
theorem B21576941 : Blo 1893435 21576941 := bstep (se 3 (by rfl) ⟨4045676, by rfl⟩ : syracuseStep 21576941 = 8091353) B8091353
theorem B14384627 : Blo 1893435 14384627 := bstep (se 1 (by rfl) ⟨10788470, by rfl⟩ : syracuseStep 14384627 = 21576941) B21576941
theorem B9589751 : Blo 1893435 9589751 := bstep (se 1 (by rfl) ⟨7192313, by rfl⟩ : syracuseStep 9589751 = 14384627) B14384627
theorem B6393167 : Blo 1893435 6393167 := bstep (se 1 (by rfl) ⟨4794875, by rfl⟩ : syracuseStep 6393167 = 9589751) B9589751
theorem B4262111 : Blo 1893435 4262111 := bstep (se 1 (by rfl) ⟨3196583, by rfl⟩ : syracuseStep 4262111 = 6393167) B6393167
theorem B2841407 : Blo 1893435 2841407 := bstep (se 1 (by rfl) ⟨2131055, by rfl⟩ : syracuseStep 2841407 = 4262111) B4262111
theorem B1894271 : Blo 1893435 1894271 := bstep (se 1 (by rfl) ⟨1420703, by rfl⟩ : syracuseStep 1894271 = 2841407) B2841407
theorem B2841413 : Blo 1893435 2841413 := bbase (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) (by norm_num)
theorem B1894275 : Blo 1893435 1894275 := bstep (se 1 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 1894275 = 2841413) B2841413
theorem B3196597 : Blo 1893435 3196597 := bbase (se 5 (by rfl) ⟨149840, by rfl⟩ : syracuseStep 3196597 = 299681) (by norm_num)
theorem B4262129 : Blo 1893435 4262129 := bstep (se 2 (by rfl) ⟨1598298, by rfl⟩ : syracuseStep 4262129 = 3196597) B3196597
theorem B2841419 : Blo 1893435 2841419 := bstep (se 1 (by rfl) ⟨2131064, by rfl⟩ : syracuseStep 2841419 = 4262129) B4262129
theorem B1894279 : Blo 1893435 1894279 := bstep (se 1 (by rfl) ⟨1420709, by rfl⟩ : syracuseStep 1894279 = 2841419) B2841419
theorem B2131069 : Blo 1893435 2131069 := bbase (se 3 (by rfl) ⟨399575, by rfl⟩ : syracuseStep 2131069 = 799151) (by norm_num)
theorem B2841425 : Blo 1893435 2841425 := bstep (se 2 (by rfl) ⟨1065534, by rfl⟩ : syracuseStep 2841425 = 2131069) B2131069
theorem B1894283 : Blo 1893435 1894283 := bstep (se 1 (by rfl) ⟨1420712, by rfl⟩ : syracuseStep 1894283 = 2841425) B2841425
theorem B6393221 : Blo 1893435 6393221 := bbase (se 4 (by rfl) ⟨599364, by rfl⟩ : syracuseStep 6393221 = 1198729) (by norm_num)
theorem B4262147 : Blo 1893435 4262147 := bstep (se 1 (by rfl) ⟨3196610, by rfl⟩ : syracuseStep 4262147 = 6393221) B6393221
theorem B2841431 : Blo 1893435 2841431 := bstep (se 1 (by rfl) ⟨2131073, by rfl⟩ : syracuseStep 2841431 = 4262147) B4262147
theorem B1894287 : Blo 1893435 1894287 := bstep (se 1 (by rfl) ⟨1420715, by rfl⟩ : syracuseStep 1894287 = 2841431) B2841431
theorem B2841437 : Blo 1893435 2841437 := bbase (se 3 (by rfl) ⟨532769, by rfl⟩ : syracuseStep 2841437 = 1065539) (by norm_num)
theorem B1894291 : Blo 1893435 1894291 := bstep (se 1 (by rfl) ⟨1420718, by rfl⟩ : syracuseStep 1894291 = 2841437) B2841437
theorem B4262165 : Blo 1893435 4262165 := bbase (se 6 (by rfl) ⟨99894, by rfl⟩ : syracuseStep 4262165 = 199789) (by norm_num)
theorem B2841443 : Blo 1893435 2841443 := bstep (se 1 (by rfl) ⟨2131082, by rfl⟩ : syracuseStep 2841443 = 4262165) B4262165
theorem B1894295 : Blo 1893435 1894295 := bstep (se 1 (by rfl) ⟨1420721, by rfl⟩ : syracuseStep 1894295 = 2841443) B2841443
theorem B7192421 : Blo 1893435 7192421 := bbase (se 4 (by rfl) ⟨674289, by rfl⟩ : syracuseStep 7192421 = 1348579) (by norm_num)
theorem B4794947 : Blo 1893435 4794947 := bstep (se 1 (by rfl) ⟨3596210, by rfl⟩ : syracuseStep 4794947 = 7192421) B7192421
theorem B3196631 : Blo 1893435 3196631 := bstep (se 1 (by rfl) ⟨2397473, by rfl⟩ : syracuseStep 3196631 = 4794947) B4794947
theorem B2131087 : Blo 1893435 2131087 := bstep (se 1 (by rfl) ⟨1598315, by rfl⟩ : syracuseStep 2131087 = 3196631) B3196631
theorem B2841449 : Blo 1893435 2841449 := bstep (se 2 (by rfl) ⟨1065543, by rfl⟩ : syracuseStep 2841449 = 2131087) B2131087
theorem B1894299 : Blo 1893435 1894299 := bstep (se 1 (by rfl) ⟨1420724, by rfl⟩ : syracuseStep 1894299 = 2841449) B2841449
theorem B3034309 : Blo 1893435 3034309 := bbase (se 4 (by rfl) ⟨284466, by rfl⟩ : syracuseStep 3034309 = 568933) (by norm_num)
theorem B4045745 : Blo 1893435 4045745 := bstep (se 2 (by rfl) ⟨1517154, by rfl⟩ : syracuseStep 4045745 = 3034309) B3034309
theorem B10788653 : Blo 1893435 10788653 := bstep (se 3 (by rfl) ⟨2022872, by rfl⟩ : syracuseStep 10788653 = 4045745) B4045745
theorem B7192435 : Blo 1893435 7192435 := bstep (se 1 (by rfl) ⟨5394326, by rfl⟩ : syracuseStep 7192435 = 10788653) B10788653
theorem B9589913 : Blo 1893435 9589913 := bstep (se 2 (by rfl) ⟨3596217, by rfl⟩ : syracuseStep 9589913 = 7192435) B7192435
theorem B6393275 : Blo 1893435 6393275 := bstep (se 1 (by rfl) ⟨4794956, by rfl⟩ : syracuseStep 6393275 = 9589913) B9589913
theorem B4262183 : Blo 1893435 4262183 := bstep (se 1 (by rfl) ⟨3196637, by rfl⟩ : syracuseStep 4262183 = 6393275) B6393275
theorem B2841455 : Blo 1893435 2841455 := bstep (se 1 (by rfl) ⟨2131091, by rfl⟩ : syracuseStep 2841455 = 4262183) B4262183
theorem B1894303 : Blo 1893435 1894303 := bstep (se 1 (by rfl) ⟨1420727, by rfl⟩ : syracuseStep 1894303 = 2841455) B2841455
theorem B2841461 : Blo 1893435 2841461 := bbase (se 5 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 2841461 = 266387) (by norm_num)
theorem B1894307 : Blo 1893435 1894307 := bstep (se 1 (by rfl) ⟨1420730, by rfl⟩ : syracuseStep 1894307 = 2841461) B2841461
theorem B6068645 : Blo 1893435 6068645 := bbase (se 4 (by rfl) ⟨568935, by rfl⟩ : syracuseStep 6068645 = 1137871) (by norm_num)
theorem B4045763 : Blo 1893435 4045763 := bstep (se 1 (by rfl) ⟨3034322, by rfl⟩ : syracuseStep 4045763 = 6068645) B6068645
theorem B2697175 : Blo 1893435 2697175 := bstep (se 1 (by rfl) ⟨2022881, by rfl⟩ : syracuseStep 2697175 = 4045763) B4045763
theorem B3596233 : Blo 1893435 3596233 := bstep (se 2 (by rfl) ⟨1348587, by rfl⟩ : syracuseStep 3596233 = 2697175) B2697175
theorem B4794977 : Blo 1893435 4794977 := bstep (se 2 (by rfl) ⟨1798116, by rfl⟩ : syracuseStep 4794977 = 3596233) B3596233
theorem B3196651 : Blo 1893435 3196651 := bstep (se 1 (by rfl) ⟨2397488, by rfl⟩ : syracuseStep 3196651 = 4794977) B4794977
theorem B4262201 : Blo 1893435 4262201 := bstep (se 2 (by rfl) ⟨1598325, by rfl⟩ : syracuseStep 4262201 = 3196651) B3196651
theorem B2841467 : Blo 1893435 2841467 := bstep (se 1 (by rfl) ⟨2131100, by rfl⟩ : syracuseStep 2841467 = 4262201) B4262201
theorem B1894311 : Blo 1893435 1894311 := bstep (se 1 (by rfl) ⟨1420733, by rfl⟩ : syracuseStep 1894311 = 2841467) B2841467
theorem B2131105 : Blo 1893435 2131105 := bbase (se 2 (by rfl) ⟨799164, by rfl⟩ : syracuseStep 2131105 = 1598329) (by norm_num)
theorem B2841473 : Blo 1893435 2841473 := bstep (se 2 (by rfl) ⟨1065552, by rfl⟩ : syracuseStep 2841473 = 2131105) B2131105
theorem B1894315 : Blo 1893435 1894315 := bstep (se 1 (by rfl) ⟨1420736, by rfl⟩ : syracuseStep 1894315 = 2841473) B2841473
theorem B4794997 : Blo 1893435 4794997 := bbase (se 5 (by rfl) ⟨224765, by rfl⟩ : syracuseStep 4794997 = 449531) (by norm_num)
theorem B6393329 : Blo 1893435 6393329 := bstep (se 2 (by rfl) ⟨2397498, by rfl⟩ : syracuseStep 6393329 = 4794997) B4794997
theorem B4262219 : Blo 1893435 4262219 := bstep (se 1 (by rfl) ⟨3196664, by rfl⟩ : syracuseStep 4262219 = 6393329) B6393329
theorem B2841479 : Blo 1893435 2841479 := bstep (se 1 (by rfl) ⟨2131109, by rfl⟩ : syracuseStep 2841479 = 4262219) B4262219
theorem B1894319 : Blo 1893435 1894319 := bstep (se 1 (by rfl) ⟨1420739, by rfl⟩ : syracuseStep 1894319 = 2841479) B2841479
theorem B2841485 : Blo 1893435 2841485 := bbase (se 3 (by rfl) ⟨532778, by rfl⟩ : syracuseStep 2841485 = 1065557) (by norm_num)
theorem B1894323 : Blo 1893435 1894323 := bstep (se 1 (by rfl) ⟨1420742, by rfl⟩ : syracuseStep 1894323 = 2841485) B2841485
theorem B4262237 : Blo 1893435 4262237 := bbase (se 3 (by rfl) ⟨799169, by rfl⟩ : syracuseStep 4262237 = 1598339) (by norm_num)
theorem B2841491 : Blo 1893435 2841491 := bstep (se 1 (by rfl) ⟨2131118, by rfl⟩ : syracuseStep 2841491 = 4262237) B4262237
theorem B1894327 : Blo 1893435 1894327 := bstep (se 1 (by rfl) ⟨1420745, by rfl⟩ : syracuseStep 1894327 = 2841491) B2841491
theorem B3196685 : Blo 1893435 3196685 := bbase (se 3 (by rfl) ⟨599378, by rfl⟩ : syracuseStep 3196685 = 1198757) (by norm_num)
theorem B2131123 : Blo 1893435 2131123 := bstep (se 1 (by rfl) ⟨1598342, by rfl⟩ : syracuseStep 2131123 = 3196685) B3196685
theorem B2841497 : Blo 1893435 2841497 := bstep (se 2 (by rfl) ⟨1065561, by rfl⟩ : syracuseStep 2841497 = 2131123) B2131123
theorem B1894331 : Blo 1893435 1894331 := bstep (se 1 (by rfl) ⟨1420748, by rfl⟩ : syracuseStep 1894331 = 2841497) B2841497
theorem B16183253 : Blo 1893435 16183253 := bbase (se 7 (by rfl) ⟨189647, by rfl⟩ : syracuseStep 16183253 = 379295) (by norm_num)
theorem B10788835 : Blo 1893435 10788835 := bstep (se 1 (by rfl) ⟨8091626, by rfl⟩ : syracuseStep 10788835 = 16183253) B16183253
theorem B14385113 : Blo 1893435 14385113 := bstep (se 2 (by rfl) ⟨5394417, by rfl⟩ : syracuseStep 14385113 = 10788835) B10788835
theorem B9590075 : Blo 1893435 9590075 := bstep (se 1 (by rfl) ⟨7192556, by rfl⟩ : syracuseStep 9590075 = 14385113) B14385113
theorem B6393383 : Blo 1893435 6393383 := bstep (se 1 (by rfl) ⟨4795037, by rfl⟩ : syracuseStep 6393383 = 9590075) B9590075
theorem B4262255 : Blo 1893435 4262255 := bstep (se 1 (by rfl) ⟨3196691, by rfl⟩ : syracuseStep 4262255 = 6393383) B6393383
theorem B2841503 : Blo 1893435 2841503 := bstep (se 1 (by rfl) ⟨2131127, by rfl⟩ : syracuseStep 2841503 = 4262255) B4262255
theorem B1894335 : Blo 1893435 1894335 := bstep (se 1 (by rfl) ⟨1420751, by rfl⟩ : syracuseStep 1894335 = 2841503) B2841503
theorem B2841509 : Blo 1893435 2841509 := bbase (se 4 (by rfl) ⟨266391, by rfl⟩ : syracuseStep 2841509 = 532783) (by norm_num)
theorem B1894339 : Blo 1893435 1894339 := bstep (se 1 (by rfl) ⟨1420754, by rfl⟩ : syracuseStep 1894339 = 2841509) B2841509
theorem B2397529 : Blo 1893435 2397529 := bbase (se 2 (by rfl) ⟨899073, by rfl⟩ : syracuseStep 2397529 = 1798147) (by norm_num)
theorem B3196705 : Blo 1893435 3196705 := bstep (se 2 (by rfl) ⟨1198764, by rfl⟩ : syracuseStep 3196705 = 2397529) B2397529
theorem B4262273 : Blo 1893435 4262273 := bstep (se 2 (by rfl) ⟨1598352, by rfl⟩ : syracuseStep 4262273 = 3196705) B3196705
theorem B2841515 : Blo 1893435 2841515 := bstep (se 1 (by rfl) ⟨2131136, by rfl⟩ : syracuseStep 2841515 = 4262273) B4262273
theorem B1894343 : Blo 1893435 1894343 := bstep (se 1 (by rfl) ⟨1420757, by rfl⟩ : syracuseStep 1894343 = 2841515) B2841515
theorem B2131141 : Blo 1893435 2131141 := bbase (se 4 (by rfl) ⟨199794, by rfl⟩ : syracuseStep 2131141 = 399589) (by norm_num)
theorem B2841521 : Blo 1893435 2841521 := bstep (se 2 (by rfl) ⟨1065570, by rfl⟩ : syracuseStep 2841521 = 2131141) B2131141
theorem B1894347 : Blo 1893435 1894347 := bstep (se 1 (by rfl) ⟨1420760, by rfl⟩ : syracuseStep 1894347 = 2841521) B2841521
theorem B3596309 : Blo 1893435 3596309 := bbase (se 6 (by rfl) ⟨84288, by rfl⟩ : syracuseStep 3596309 = 168577) (by norm_num)
theorem B2397539 : Blo 1893435 2397539 := bstep (se 1 (by rfl) ⟨1798154, by rfl⟩ : syracuseStep 2397539 = 3596309) B3596309
theorem B6393437 : Blo 1893435 6393437 := bstep (se 3 (by rfl) ⟨1198769, by rfl⟩ : syracuseStep 6393437 = 2397539) B2397539
theorem B4262291 : Blo 1893435 4262291 := bstep (se 1 (by rfl) ⟨3196718, by rfl⟩ : syracuseStep 4262291 = 6393437) B6393437
theorem B2841527 : Blo 1893435 2841527 := bstep (se 1 (by rfl) ⟨2131145, by rfl⟩ : syracuseStep 2841527 = 4262291) B4262291
theorem B1894351 : Blo 1893435 1894351 := bstep (se 1 (by rfl) ⟨1420763, by rfl⟩ : syracuseStep 1894351 = 2841527) B2841527
theorem B2841533 : Blo 1893435 2841533 := bbase (se 3 (by rfl) ⟨532787, by rfl⟩ : syracuseStep 2841533 = 1065575) (by norm_num)
theorem B1894355 : Blo 1893435 1894355 := bstep (se 1 (by rfl) ⟨1420766, by rfl⟩ : syracuseStep 1894355 = 2841533) B2841533
theorem B4262309 : Blo 1893435 4262309 := bbase (se 4 (by rfl) ⟨399591, by rfl⟩ : syracuseStep 4262309 = 799183) (by norm_num)
theorem B2841539 : Blo 1893435 2841539 := bstep (se 1 (by rfl) ⟨2131154, by rfl⟩ : syracuseStep 2841539 = 4262309) B4262309
theorem B1894359 : Blo 1893435 1894359 := bstep (se 1 (by rfl) ⟨1420769, by rfl⟩ : syracuseStep 1894359 = 2841539) B2841539
theorem B4795109 : Blo 1893435 4795109 := bbase (se 4 (by rfl) ⟨449541, by rfl⟩ : syracuseStep 4795109 = 899083) (by norm_num)
theorem B3196739 : Blo 1893435 3196739 := bstep (se 1 (by rfl) ⟨2397554, by rfl⟩ : syracuseStep 3196739 = 4795109) B4795109
theorem B2131159 : Blo 1893435 2131159 := bstep (se 1 (by rfl) ⟨1598369, by rfl⟩ : syracuseStep 2131159 = 3196739) B3196739
theorem B2841545 : Blo 1893435 2841545 := bstep (se 2 (by rfl) ⟨1065579, by rfl⟩ : syracuseStep 2841545 = 2131159) B2131159
theorem B1894363 : Blo 1893435 1894363 := bstep (se 1 (by rfl) ⟨1420772, by rfl⟩ : syracuseStep 1894363 = 2841545) B2841545
theorem B2022941 : Blo 1893435 2022941 := bbase (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) (by norm_num)
theorem B5394509 : Blo 1893435 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B3596339 : Blo 1893435 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B9590237 : Blo 1893435 9590237 := bstep (se 3 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 9590237 = 3596339) B3596339
theorem B6393491 : Blo 1893435 6393491 := bstep (se 1 (by rfl) ⟨4795118, by rfl⟩ : syracuseStep 6393491 = 9590237) B9590237
theorem B4262327 : Blo 1893435 4262327 := bstep (se 1 (by rfl) ⟨3196745, by rfl⟩ : syracuseStep 4262327 = 6393491) B6393491
theorem B2841551 : Blo 1893435 2841551 := bstep (se 1 (by rfl) ⟨2131163, by rfl⟩ : syracuseStep 2841551 = 4262327) B4262327
theorem B1894367 : Blo 1893435 1894367 := bstep (se 1 (by rfl) ⟨1420775, by rfl⟩ : syracuseStep 1894367 = 2841551) B2841551
theorem B2841557 : Blo 1893435 2841557 := bbase (se 7 (by rfl) ⟨33299, by rfl⟩ : syracuseStep 2841557 = 66599) (by norm_num)
theorem B1894371 : Blo 1893435 1894371 := bstep (se 1 (by rfl) ⟨1420778, by rfl⟩ : syracuseStep 1894371 = 2841557) B2841557
theorem B7192709 : Blo 1893435 7192709 := bbase (se 4 (by rfl) ⟨674316, by rfl⟩ : syracuseStep 7192709 = 1348633) (by norm_num)
theorem B4795139 : Blo 1893435 4795139 := bstep (se 1 (by rfl) ⟨3596354, by rfl⟩ : syracuseStep 4795139 = 7192709) B7192709
theorem B3196759 : Blo 1893435 3196759 := bstep (se 1 (by rfl) ⟨2397569, by rfl⟩ : syracuseStep 3196759 = 4795139) B4795139
theorem B4262345 : Blo 1893435 4262345 := bstep (se 2 (by rfl) ⟨1598379, by rfl⟩ : syracuseStep 4262345 = 3196759) B3196759
theorem B2841563 : Blo 1893435 2841563 := bstep (se 1 (by rfl) ⟨2131172, by rfl⟩ : syracuseStep 2841563 = 4262345) B4262345
theorem B1894375 : Blo 1893435 1894375 := bstep (se 1 (by rfl) ⟨1420781, by rfl⟩ : syracuseStep 1894375 = 2841563) B2841563
theorem B2131177 : Blo 1893435 2131177 := bbase (se 2 (by rfl) ⟨799191, by rfl⟩ : syracuseStep 2131177 = 1598383) (by norm_num)
theorem B2841569 : Blo 1893435 2841569 := bstep (se 2 (by rfl) ⟨1065588, by rfl⟩ : syracuseStep 2841569 = 2131177) B2131177
theorem B1894379 : Blo 1893435 1894379 := bstep (se 1 (by rfl) ⟨1420784, by rfl⟩ : syracuseStep 1894379 = 2841569) B2841569
theorem B10789109 : Blo 1893435 10789109 := bbase (se 5 (by rfl) ⟨505739, by rfl⟩ : syracuseStep 10789109 = 1011479) (by norm_num)
theorem B7192739 : Blo 1893435 7192739 := bstep (se 1 (by rfl) ⟨5394554, by rfl⟩ : syracuseStep 7192739 = 10789109) B10789109
theorem B4795159 : Blo 1893435 4795159 := bstep (se 1 (by rfl) ⟨3596369, by rfl⟩ : syracuseStep 4795159 = 7192739) B7192739
theorem B6393545 : Blo 1893435 6393545 := bstep (se 2 (by rfl) ⟨2397579, by rfl⟩ : syracuseStep 6393545 = 4795159) B4795159
theorem B4262363 : Blo 1893435 4262363 := bstep (se 1 (by rfl) ⟨3196772, by rfl⟩ : syracuseStep 4262363 = 6393545) B6393545
theorem B2841575 : Blo 1893435 2841575 := bstep (se 1 (by rfl) ⟨2131181, by rfl⟩ : syracuseStep 2841575 = 4262363) B4262363
theorem B1894383 : Blo 1893435 1894383 := bstep (se 1 (by rfl) ⟨1420787, by rfl⟩ : syracuseStep 1894383 = 2841575) B2841575
theorem B2841581 : Blo 1893435 2841581 := bbase (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) (by norm_num)
theorem B1894387 : Blo 1893435 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B4262381 : Blo 1893435 4262381 := bbase (se 3 (by rfl) ⟨799196, by rfl⟩ : syracuseStep 4262381 = 1598393) (by norm_num)
theorem B2841587 : Blo 1893435 2841587 := bstep (se 1 (by rfl) ⟨2131190, by rfl⟩ : syracuseStep 2841587 = 4262381) B4262381
theorem B1894391 : Blo 1893435 1894391 := bstep (se 1 (by rfl) ⟨1420793, by rfl⟩ : syracuseStep 1894391 = 2841587) B2841587
theorem B3413765 : Blo 1893435 3413765 := bbase (se 4 (by rfl) ⟨320040, by rfl⟩ : syracuseStep 3413765 = 640081) (by norm_num)
theorem B9103373 : Blo 1893435 9103373 := bstep (se 3 (by rfl) ⟨1706882, by rfl⟩ : syracuseStep 9103373 = 3413765) B3413765
theorem B6068915 : Blo 1893435 6068915 := bstep (se 1 (by rfl) ⟨4551686, by rfl⟩ : syracuseStep 6068915 = 9103373) B9103373
theorem B4045943 : Blo 1893435 4045943 := bstep (se 1 (by rfl) ⟨3034457, by rfl⟩ : syracuseStep 4045943 = 6068915) B6068915
theorem B2697295 : Blo 1893435 2697295 := bstep (se 1 (by rfl) ⟨2022971, by rfl⟩ : syracuseStep 2697295 = 4045943) B4045943
theorem B3596393 : Blo 1893435 3596393 := bstep (se 2 (by rfl) ⟨1348647, by rfl⟩ : syracuseStep 3596393 = 2697295) B2697295
theorem B2397595 : Blo 1893435 2397595 := bstep (se 1 (by rfl) ⟨1798196, by rfl⟩ : syracuseStep 2397595 = 3596393) B3596393
theorem B3196793 : Blo 1893435 3196793 := bstep (se 2 (by rfl) ⟨1198797, by rfl⟩ : syracuseStep 3196793 = 2397595) B2397595
theorem B2131195 : Blo 1893435 2131195 := bstep (se 1 (by rfl) ⟨1598396, by rfl⟩ : syracuseStep 2131195 = 3196793) B3196793
theorem B2841593 : Blo 1893435 2841593 := bstep (se 2 (by rfl) ⟨1065597, by rfl⟩ : syracuseStep 2841593 = 2131195) B2131195
theorem B1894395 : Blo 1893435 1894395 := bstep (se 1 (by rfl) ⟨1420796, by rfl⟩ : syracuseStep 1894395 = 2841593) B2841593
theorem B2463469 : Blo 1893435 2463469 := bbase (se 3 (by rfl) ⟨461900, by rfl⟩ : syracuseStep 2463469 = 923801) (by norm_num)
theorem B52554005 : Blo 1893435 52554005 := bstep (se 6 (by rfl) ⟨1231734, by rfl⟩ : syracuseStep 52554005 = 2463469) B2463469
theorem B35036003 : Blo 1893435 35036003 := bstep (se 1 (by rfl) ⟨26277002, by rfl⟩ : syracuseStep 35036003 = 52554005) B52554005
theorem B23357335 : Blo 1893435 23357335 := bstep (se 1 (by rfl) ⟨17518001, by rfl⟩ : syracuseStep 23357335 = 35036003) B35036003
theorem B31143113 : Blo 1893435 31143113 := bstep (se 2 (by rfl) ⟨11678667, by rfl⟩ : syracuseStep 31143113 = 23357335) B23357335
theorem B20762075 : Blo 1893435 20762075 := bstep (se 1 (by rfl) ⟨15571556, by rfl⟩ : syracuseStep 20762075 = 31143113) B31143113
theorem B13841383 : Blo 1893435 13841383 := bstep (se 1 (by rfl) ⟨10381037, by rfl⟩ : syracuseStep 13841383 = 20762075) B20762075
theorem B18455177 : Blo 1893435 18455177 := bstep (se 2 (by rfl) ⟨6920691, by rfl⟩ : syracuseStep 18455177 = 13841383) B13841383
theorem B12303451 : Blo 1893435 12303451 := bstep (se 1 (by rfl) ⟨9227588, by rfl⟩ : syracuseStep 12303451 = 18455177) B18455177
theorem B16404601 : Blo 1893435 16404601 := bstep (se 2 (by rfl) ⟨6151725, by rfl⟩ : syracuseStep 16404601 = 12303451) B12303451
theorem B21872801 : Blo 1893435 21872801 := bstep (se 2 (by rfl) ⟨8202300, by rfl⟩ : syracuseStep 21872801 = 16404601) B16404601
theorem B14581867 : Blo 1893435 14581867 := bstep (se 1 (by rfl) ⟨10936400, by rfl⟩ : syracuseStep 14581867 = 21872801) B21872801
theorem B19442489 : Blo 1893435 19442489 := bstep (se 2 (by rfl) ⟨7290933, by rfl⟩ : syracuseStep 19442489 = 14581867) B14581867
theorem B51846637 : Blo 1893435 51846637 := bstep (se 3 (by rfl) ⟨9721244, by rfl⟩ : syracuseStep 51846637 = 19442489) B19442489
theorem B69128849 : Blo 1893435 69128849 := bstep (se 2 (by rfl) ⟨25923318, by rfl⟩ : syracuseStep 69128849 = 51846637) B51846637
theorem B184343597 : Blo 1893435 184343597 := bstep (se 3 (by rfl) ⟨34564424, by rfl⟩ : syracuseStep 184343597 = 69128849) B69128849
theorem B122895731 : Blo 1893435 122895731 := bstep (se 1 (by rfl) ⟨92171798, by rfl⟩ : syracuseStep 122895731 = 184343597) B184343597
theorem B81930487 : Blo 1893435 81930487 := bstep (se 1 (by rfl) ⟨61447865, by rfl⟩ : syracuseStep 81930487 = 122895731) B122895731
theorem B109240649 : Blo 1893435 109240649 := bstep (se 2 (by rfl) ⟨40965243, by rfl⟩ : syracuseStep 109240649 = 81930487) B81930487
theorem B72827099 : Blo 1893435 72827099 := bstep (se 1 (by rfl) ⟨54620324, by rfl⟩ : syracuseStep 72827099 = 109240649) B109240649
theorem B48551399 : Blo 1893435 48551399 := bstep (se 1 (by rfl) ⟨36413549, by rfl⟩ : syracuseStep 48551399 = 72827099) B72827099
theorem B32367599 : Blo 1893435 32367599 := bstep (se 1 (by rfl) ⟨24275699, by rfl⟩ : syracuseStep 32367599 = 48551399) B48551399
theorem B21578399 : Blo 1893435 21578399 := bstep (se 1 (by rfl) ⟨16183799, by rfl⟩ : syracuseStep 21578399 = 32367599) B32367599
theorem B14385599 : Blo 1893435 14385599 := bstep (se 1 (by rfl) ⟨10789199, by rfl⟩ : syracuseStep 14385599 = 21578399) B21578399
theorem B9590399 : Blo 1893435 9590399 := bstep (se 1 (by rfl) ⟨7192799, by rfl⟩ : syracuseStep 9590399 = 14385599) B14385599
theorem B6393599 : Blo 1893435 6393599 := bstep (se 1 (by rfl) ⟨4795199, by rfl⟩ : syracuseStep 6393599 = 9590399) B9590399
theorem B4262399 : Blo 1893435 4262399 := bstep (se 1 (by rfl) ⟨3196799, by rfl⟩ : syracuseStep 4262399 = 6393599) B6393599
theorem B2841599 : Blo 1893435 2841599 := bstep (se 1 (by rfl) ⟨2131199, by rfl⟩ : syracuseStep 2841599 = 4262399) B4262399
theorem B1894399 : Blo 1893435 1894399 := bstep (se 1 (by rfl) ⟨1420799, by rfl⟩ : syracuseStep 1894399 = 2841599) B2841599
theorem B2841605 : Blo 1893435 2841605 := bbase (se 4 (by rfl) ⟨266400, by rfl⟩ : syracuseStep 2841605 = 532801) (by norm_num)
theorem B1894403 : Blo 1893435 1894403 := bstep (se 1 (by rfl) ⟨1420802, by rfl⟩ : syracuseStep 1894403 = 2841605) B2841605
theorem B3196813 : Blo 1893435 3196813 := bbase (se 3 (by rfl) ⟨599402, by rfl⟩ : syracuseStep 3196813 = 1198805) (by norm_num)
theorem B4262417 : Blo 1893435 4262417 := bstep (se 2 (by rfl) ⟨1598406, by rfl⟩ : syracuseStep 4262417 = 3196813) B3196813
theorem B2841611 : Blo 1893435 2841611 := bstep (se 1 (by rfl) ⟨2131208, by rfl⟩ : syracuseStep 2841611 = 4262417) B4262417
theorem B1894407 : Blo 1893435 1894407 := bstep (se 1 (by rfl) ⟨1420805, by rfl⟩ : syracuseStep 1894407 = 2841611) B2841611
theorem B2131213 : Blo 1893435 2131213 := bbase (se 3 (by rfl) ⟨399602, by rfl⟩ : syracuseStep 2131213 = 799205) (by norm_num)
theorem B2841617 : Blo 1893435 2841617 := bstep (se 2 (by rfl) ⟨1065606, by rfl⟩ : syracuseStep 2841617 = 2131213) B2131213
theorem B1894411 : Blo 1893435 1894411 := bstep (se 1 (by rfl) ⟨1420808, by rfl⟩ : syracuseStep 1894411 = 2841617) B2841617
theorem B6393653 : Blo 1893435 6393653 := bbase (se 5 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 6393653 = 599405) (by norm_num)
theorem B4262435 : Blo 1893435 4262435 := bstep (se 1 (by rfl) ⟨3196826, by rfl⟩ : syracuseStep 4262435 = 6393653) B6393653
theorem B2841623 : Blo 1893435 2841623 := bstep (se 1 (by rfl) ⟨2131217, by rfl⟩ : syracuseStep 2841623 = 4262435) B4262435
theorem B1894415 : Blo 1893435 1894415 := bstep (se 1 (by rfl) ⟨1420811, by rfl⟩ : syracuseStep 1894415 = 2841623) B2841623
theorem B2841629 : Blo 1893435 2841629 := bbase (se 3 (by rfl) ⟨532805, by rfl⟩ : syracuseStep 2841629 = 1065611) (by norm_num)
theorem B1894419 : Blo 1893435 1894419 := bstep (se 1 (by rfl) ⟨1420814, by rfl⟩ : syracuseStep 1894419 = 2841629) B2841629
theorem B4262453 : Blo 1893435 4262453 := bbase (se 5 (by rfl) ⟨199802, by rfl⟩ : syracuseStep 4262453 = 399605) (by norm_num)
theorem B2841635 : Blo 1893435 2841635 := bstep (se 1 (by rfl) ⟨2131226, by rfl⟩ : syracuseStep 2841635 = 4262453) B4262453
theorem B1894423 : Blo 1893435 1894423 := bstep (se 1 (by rfl) ⟨1420817, by rfl⟩ : syracuseStep 1894423 = 2841635) B2841635
theorem B8092021 : Blo 1893435 8092021 := bbase (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) (by norm_num)
theorem B10789361 : Blo 1893435 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B7192907 : Blo 1893435 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B4795271 : Blo 1893435 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B3196847 : Blo 1893435 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B2131231 : Blo 1893435 2131231 := bstep (se 1 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 2131231 = 3196847) B3196847
theorem B2841641 : Blo 1893435 2841641 := bstep (se 2 (by rfl) ⟨1065615, by rfl⟩ : syracuseStep 2841641 = 2131231) B2131231
theorem B1894427 : Blo 1893435 1894427 := bstep (se 1 (by rfl) ⟨1420820, by rfl⟩ : syracuseStep 1894427 = 2841641) B2841641
theorem B8092037 : Blo 1893435 8092037 := bbase (se 4 (by rfl) ⟨758628, by rfl⟩ : syracuseStep 8092037 = 1517257) (by norm_num)
theorem B5394691 : Blo 1893435 5394691 := bstep (se 1 (by rfl) ⟨4046018, by rfl⟩ : syracuseStep 5394691 = 8092037) B8092037
theorem B7192921 : Blo 1893435 7192921 := bstep (se 2 (by rfl) ⟨2697345, by rfl⟩ : syracuseStep 7192921 = 5394691) B5394691
theorem B9590561 : Blo 1893435 9590561 := bstep (se 2 (by rfl) ⟨3596460, by rfl⟩ : syracuseStep 9590561 = 7192921) B7192921
theorem B6393707 : Blo 1893435 6393707 := bstep (se 1 (by rfl) ⟨4795280, by rfl⟩ : syracuseStep 6393707 = 9590561) B9590561
theorem B4262471 : Blo 1893435 4262471 := bstep (se 1 (by rfl) ⟨3196853, by rfl⟩ : syracuseStep 4262471 = 6393707) B6393707
theorem B2841647 : Blo 1893435 2841647 := bstep (se 1 (by rfl) ⟨2131235, by rfl⟩ : syracuseStep 2841647 = 4262471) B4262471
theorem B1894431 : Blo 1893435 1894431 := bstep (se 1 (by rfl) ⟨1420823, by rfl⟩ : syracuseStep 1894431 = 2841647) B2841647
theorem B2841653 : Blo 1893435 2841653 := bbase (se 5 (by rfl) ⟨133202, by rfl⟩ : syracuseStep 2841653 = 266405) (by norm_num)
theorem B1894435 : Blo 1893435 1894435 := bstep (se 1 (by rfl) ⟨1420826, by rfl⟩ : syracuseStep 1894435 = 2841653) B2841653
theorem B4795301 : Blo 1893435 4795301 := bbase (se 4 (by rfl) ⟨449559, by rfl⟩ : syracuseStep 4795301 = 899119) (by norm_num)
theorem B3196867 : Blo 1893435 3196867 := bstep (se 1 (by rfl) ⟨2397650, by rfl⟩ : syracuseStep 3196867 = 4795301) B4795301
theorem B4262489 : Blo 1893435 4262489 := bstep (se 2 (by rfl) ⟨1598433, by rfl⟩ : syracuseStep 4262489 = 3196867) B3196867
theorem B2841659 : Blo 1893435 2841659 := bstep (se 1 (by rfl) ⟨2131244, by rfl⟩ : syracuseStep 2841659 = 4262489) B4262489
theorem B1894439 : Blo 1893435 1894439 := bstep (se 1 (by rfl) ⟨1420829, by rfl⟩ : syracuseStep 1894439 = 2841659) B2841659
theorem B2131249 : Blo 1893435 2131249 := bbase (se 2 (by rfl) ⟨799218, by rfl⟩ : syracuseStep 2131249 = 1598437) (by norm_num)
theorem B2841665 : Blo 1893435 2841665 := bstep (se 2 (by rfl) ⟨1065624, by rfl⟩ : syracuseStep 2841665 = 2131249) B2131249
theorem B1894443 : Blo 1893435 1894443 := bstep (se 1 (by rfl) ⟨1420832, by rfl⟩ : syracuseStep 1894443 = 2841665) B2841665
theorem B4046053 : Blo 1893435 4046053 := bbase (se 4 (by rfl) ⟨379317, by rfl⟩ : syracuseStep 4046053 = 758635) (by norm_num)
theorem B5394737 : Blo 1893435 5394737 := bstep (se 2 (by rfl) ⟨2023026, by rfl⟩ : syracuseStep 5394737 = 4046053) B4046053
theorem B3596491 : Blo 1893435 3596491 := bstep (se 1 (by rfl) ⟨2697368, by rfl⟩ : syracuseStep 3596491 = 5394737) B5394737
theorem B4795321 : Blo 1893435 4795321 := bstep (se 2 (by rfl) ⟨1798245, by rfl⟩ : syracuseStep 4795321 = 3596491) B3596491
theorem B6393761 : Blo 1893435 6393761 := bstep (se 2 (by rfl) ⟨2397660, by rfl⟩ : syracuseStep 6393761 = 4795321) B4795321
theorem B4262507 : Blo 1893435 4262507 := bstep (se 1 (by rfl) ⟨3196880, by rfl⟩ : syracuseStep 4262507 = 6393761) B6393761
theorem B2841671 : Blo 1893435 2841671 := bstep (se 1 (by rfl) ⟨2131253, by rfl⟩ : syracuseStep 2841671 = 4262507) B4262507
theorem B1894447 : Blo 1893435 1894447 := bstep (se 1 (by rfl) ⟨1420835, by rfl⟩ : syracuseStep 1894447 = 2841671) B2841671
theorem B2841677 : Blo 1893435 2841677 := bbase (se 3 (by rfl) ⟨532814, by rfl⟩ : syracuseStep 2841677 = 1065629) (by norm_num)
theorem B1894451 : Blo 1893435 1894451 := bstep (se 1 (by rfl) ⟨1420838, by rfl⟩ : syracuseStep 1894451 = 2841677) B2841677
theorem B4262525 : Blo 1893435 4262525 := bbase (se 3 (by rfl) ⟨799223, by rfl⟩ : syracuseStep 4262525 = 1598447) (by norm_num)
theorem B2841683 : Blo 1893435 2841683 := bstep (se 1 (by rfl) ⟨2131262, by rfl⟩ : syracuseStep 2841683 = 4262525) B4262525
theorem B1894455 : Blo 1893435 1894455 := bstep (se 1 (by rfl) ⟨1420841, by rfl⟩ : syracuseStep 1894455 = 2841683) B2841683
theorem B3196901 : Blo 1893435 3196901 := bbase (se 4 (by rfl) ⟨299709, by rfl⟩ : syracuseStep 3196901 = 599419) (by norm_num)
theorem B2131267 : Blo 1893435 2131267 := bstep (se 1 (by rfl) ⟨1598450, by rfl⟩ : syracuseStep 2131267 = 3196901) B3196901
theorem B2841689 : Blo 1893435 2841689 := bstep (se 2 (by rfl) ⟨1065633, by rfl⟩ : syracuseStep 2841689 = 2131267) B2131267
theorem B1894459 : Blo 1893435 1894459 := bstep (se 1 (by rfl) ⟨1420844, by rfl⟩ : syracuseStep 1894459 = 2841689) B2841689
theorem B2595349 : Blo 1893435 2595349 := bbase (se 6 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 2595349 = 121657) (by norm_num)
theorem B3460465 : Blo 1893435 3460465 := bstep (se 2 (by rfl) ⟨1297674, by rfl⟩ : syracuseStep 3460465 = 2595349) B2595349
theorem B18455813 : Blo 1893435 18455813 := bstep (se 4 (by rfl) ⟨1730232, by rfl⟩ : syracuseStep 18455813 = 3460465) B3460465
theorem B12303875 : Blo 1893435 12303875 := bstep (se 1 (by rfl) ⟨9227906, by rfl⟩ : syracuseStep 12303875 = 18455813) B18455813
theorem B8202583 : Blo 1893435 8202583 := bstep (se 1 (by rfl) ⟨6151937, by rfl⟩ : syracuseStep 8202583 = 12303875) B12303875
theorem B10936777 : Blo 1893435 10936777 := bstep (se 2 (by rfl) ⟨4101291, by rfl⟩ : syracuseStep 10936777 = 8202583) B8202583
theorem B14582369 : Blo 1893435 14582369 := bstep (se 2 (by rfl) ⟨5468388, by rfl⟩ : syracuseStep 14582369 = 10936777) B10936777
theorem B9721579 : Blo 1893435 9721579 := bstep (se 1 (by rfl) ⟨7291184, by rfl⟩ : syracuseStep 9721579 = 14582369) B14582369
theorem B12962105 : Blo 1893435 12962105 := bstep (se 2 (by rfl) ⟨4860789, by rfl⟩ : syracuseStep 12962105 = 9721579) B9721579
theorem B8641403 : Blo 1893435 8641403 := bstep (se 1 (by rfl) ⟨6481052, by rfl⟩ : syracuseStep 8641403 = 12962105) B12962105
theorem B5760935 : Blo 1893435 5760935 := bstep (se 1 (by rfl) ⟨4320701, by rfl⟩ : syracuseStep 5760935 = 8641403) B8641403
theorem B3840623 : Blo 1893435 3840623 := bstep (se 1 (by rfl) ⟨2880467, by rfl⟩ : syracuseStep 3840623 = 5760935) B5760935
theorem B2560415 : Blo 1893435 2560415 := bstep (se 1 (by rfl) ⟨1920311, by rfl⟩ : syracuseStep 2560415 = 3840623) B3840623
theorem B6827773 : Blo 1893435 6827773 := bstep (se 3 (by rfl) ⟨1280207, by rfl⟩ : syracuseStep 6827773 = 2560415) B2560415
theorem B9103697 : Blo 1893435 9103697 := bstep (se 2 (by rfl) ⟨3413886, by rfl⟩ : syracuseStep 9103697 = 6827773) B6827773
theorem B6069131 : Blo 1893435 6069131 := bstep (se 1 (by rfl) ⟨4551848, by rfl⟩ : syracuseStep 6069131 = 9103697) B9103697
theorem B4046087 : Blo 1893435 4046087 := bstep (se 1 (by rfl) ⟨3034565, by rfl⟩ : syracuseStep 4046087 = 6069131) B6069131
theorem B2697391 : Blo 1893435 2697391 := bstep (se 1 (by rfl) ⟨2023043, by rfl⟩ : syracuseStep 2697391 = 4046087) B4046087
theorem B14386085 : Blo 1893435 14386085 := bstep (se 4 (by rfl) ⟨1348695, by rfl⟩ : syracuseStep 14386085 = 2697391) B2697391
theorem B9590723 : Blo 1893435 9590723 := bstep (se 1 (by rfl) ⟨7193042, by rfl⟩ : syracuseStep 9590723 = 14386085) B14386085
theorem B6393815 : Blo 1893435 6393815 := bstep (se 1 (by rfl) ⟨4795361, by rfl⟩ : syracuseStep 6393815 = 9590723) B9590723
theorem B4262543 : Blo 1893435 4262543 := bstep (se 1 (by rfl) ⟨3196907, by rfl⟩ : syracuseStep 4262543 = 6393815) B6393815
theorem B2841695 : Blo 1893435 2841695 := bstep (se 1 (by rfl) ⟨2131271, by rfl⟩ : syracuseStep 2841695 = 4262543) B4262543
theorem B1894463 : Blo 1893435 1894463 := bstep (se 1 (by rfl) ⟨1420847, by rfl⟩ : syracuseStep 1894463 = 2841695) B2841695
theorem B2841701 : Blo 1893435 2841701 := bbase (se 4 (by rfl) ⟨266409, by rfl⟩ : syracuseStep 2841701 = 532819) (by norm_num)
theorem B1894467 : Blo 1893435 1894467 := bstep (se 1 (by rfl) ⟨1420850, by rfl⟩ : syracuseStep 1894467 = 2841701) B2841701
theorem B4551869 : Blo 1893435 4551869 := bbase (se 3 (by rfl) ⟨853475, by rfl⟩ : syracuseStep 4551869 = 1706951) (by norm_num)
theorem B3034579 : Blo 1893435 3034579 := bstep (se 1 (by rfl) ⟨2275934, by rfl⟩ : syracuseStep 3034579 = 4551869) B4551869
theorem B4046105 : Blo 1893435 4046105 := bstep (se 2 (by rfl) ⟨1517289, by rfl⟩ : syracuseStep 4046105 = 3034579) B3034579
theorem B2697403 : Blo 1893435 2697403 := bstep (se 1 (by rfl) ⟨2023052, by rfl⟩ : syracuseStep 2697403 = 4046105) B4046105
theorem B3596537 : Blo 1893435 3596537 := bstep (se 2 (by rfl) ⟨1348701, by rfl⟩ : syracuseStep 3596537 = 2697403) B2697403
theorem B2397691 : Blo 1893435 2397691 := bstep (se 1 (by rfl) ⟨1798268, by rfl⟩ : syracuseStep 2397691 = 3596537) B3596537
theorem B3196921 : Blo 1893435 3196921 := bstep (se 2 (by rfl) ⟨1198845, by rfl⟩ : syracuseStep 3196921 = 2397691) B2397691
theorem B4262561 : Blo 1893435 4262561 := bstep (se 2 (by rfl) ⟨1598460, by rfl⟩ : syracuseStep 4262561 = 3196921) B3196921
theorem B2841707 : Blo 1893435 2841707 := bstep (se 1 (by rfl) ⟨2131280, by rfl⟩ : syracuseStep 2841707 = 4262561) B4262561
theorem B1894471 : Blo 1893435 1894471 := bstep (se 1 (by rfl) ⟨1420853, by rfl⟩ : syracuseStep 1894471 = 2841707) B2841707
theorem B2131285 : Blo 1893435 2131285 := bbase (se 12 (by rfl) ⟨780, by rfl⟩ : syracuseStep 2131285 = 1561) (by norm_num)
theorem B2841713 : Blo 1893435 2841713 := bstep (se 2 (by rfl) ⟨1065642, by rfl⟩ : syracuseStep 2841713 = 2131285) B2131285
theorem B1894475 : Blo 1893435 1894475 := bstep (se 1 (by rfl) ⟨1420856, by rfl⟩ : syracuseStep 1894475 = 2841713) B2841713
theorem B2397701 : Blo 1893435 2397701 := bbase (se 4 (by rfl) ⟨224784, by rfl⟩ : syracuseStep 2397701 = 449569) (by norm_num)
theorem B6393869 : Blo 1893435 6393869 := bstep (se 3 (by rfl) ⟨1198850, by rfl⟩ : syracuseStep 6393869 = 2397701) B2397701
theorem B4262579 : Blo 1893435 4262579 := bstep (se 1 (by rfl) ⟨3196934, by rfl⟩ : syracuseStep 4262579 = 6393869) B6393869
theorem B2841719 : Blo 1893435 2841719 := bstep (se 1 (by rfl) ⟨2131289, by rfl⟩ : syracuseStep 2841719 = 4262579) B4262579
theorem B1894479 : Blo 1893435 1894479 := bstep (se 1 (by rfl) ⟨1420859, by rfl⟩ : syracuseStep 1894479 = 2841719) B2841719
theorem B2841725 : Blo 1893435 2841725 := bbase (se 3 (by rfl) ⟨532823, by rfl⟩ : syracuseStep 2841725 = 1065647) (by norm_num)
theorem B1894483 : Blo 1893435 1894483 := bstep (se 1 (by rfl) ⟨1420862, by rfl⟩ : syracuseStep 1894483 = 2841725) B2841725
theorem B4262597 : Blo 1893435 4262597 := bbase (se 4 (by rfl) ⟨399618, by rfl⟩ : syracuseStep 4262597 = 799237) (by norm_num)
theorem B2841731 : Blo 1893435 2841731 := bstep (se 1 (by rfl) ⟨2131298, by rfl⟩ : syracuseStep 2841731 = 4262597) B4262597
theorem B1894487 : Blo 1893435 1894487 := bstep (se 1 (by rfl) ⟨1420865, by rfl⟩ : syracuseStep 1894487 = 2841731) B2841731
theorem B2560453 : Blo 1893435 2560453 := bbase (se 4 (by rfl) ⟨240042, by rfl⟩ : syracuseStep 2560453 = 480085) (by norm_num)
theorem B13655749 : Blo 1893435 13655749 := bstep (se 4 (by rfl) ⟨1280226, by rfl⟩ : syracuseStep 13655749 = 2560453) B2560453
theorem B18207665 : Blo 1893435 18207665 := bstep (se 2 (by rfl) ⟨6827874, by rfl⟩ : syracuseStep 18207665 = 13655749) B13655749
theorem B12138443 : Blo 1893435 12138443 := bstep (se 1 (by rfl) ⟨9103832, by rfl⟩ : syracuseStep 12138443 = 18207665) B18207665
theorem B8092295 : Blo 1893435 8092295 := bstep (se 1 (by rfl) ⟨6069221, by rfl⟩ : syracuseStep 8092295 = 12138443) B12138443
theorem B5394863 : Blo 1893435 5394863 := bstep (se 1 (by rfl) ⟨4046147, by rfl⟩ : syracuseStep 5394863 = 8092295) B8092295
theorem B3596575 : Blo 1893435 3596575 := bstep (se 1 (by rfl) ⟨2697431, by rfl⟩ : syracuseStep 3596575 = 5394863) B5394863
theorem B4795433 : Blo 1893435 4795433 := bstep (se 2 (by rfl) ⟨1798287, by rfl⟩ : syracuseStep 4795433 = 3596575) B3596575
theorem B3196955 : Blo 1893435 3196955 := bstep (se 1 (by rfl) ⟨2397716, by rfl⟩ : syracuseStep 3196955 = 4795433) B4795433
theorem B2131303 : Blo 1893435 2131303 := bstep (se 1 (by rfl) ⟨1598477, by rfl⟩ : syracuseStep 2131303 = 3196955) B3196955
theorem B2841737 : Blo 1893435 2841737 := bstep (se 2 (by rfl) ⟨1065651, by rfl⟩ : syracuseStep 2841737 = 2131303) B2131303
theorem B1894491 : Blo 1893435 1894491 := bstep (se 1 (by rfl) ⟨1420868, by rfl⟩ : syracuseStep 1894491 = 2841737) B2841737
theorem B9590885 : Blo 1893435 9590885 := bbase (se 4 (by rfl) ⟨899145, by rfl⟩ : syracuseStep 9590885 = 1798291) (by norm_num)
theorem B6393923 : Blo 1893435 6393923 := bstep (se 1 (by rfl) ⟨4795442, by rfl⟩ : syracuseStep 6393923 = 9590885) B9590885
theorem B4262615 : Blo 1893435 4262615 := bstep (se 1 (by rfl) ⟨3196961, by rfl⟩ : syracuseStep 4262615 = 6393923) B6393923
theorem B2841743 : Blo 1893435 2841743 := bstep (se 1 (by rfl) ⟨2131307, by rfl⟩ : syracuseStep 2841743 = 4262615) B4262615
theorem B1894495 : Blo 1893435 1894495 := bstep (se 1 (by rfl) ⟨1420871, by rfl⟩ : syracuseStep 1894495 = 2841743) B2841743
theorem B2841749 : Blo 1893435 2841749 := bbase (se 6 (by rfl) ⟨66603, by rfl⟩ : syracuseStep 2841749 = 133207) (by norm_num)
theorem B1894499 : Blo 1893435 1894499 := bstep (se 1 (by rfl) ⟨1420874, by rfl⟩ : syracuseStep 1894499 = 2841749) B2841749
theorem B2560469 : Blo 1893435 2560469 := bbase (se 7 (by rfl) ⟨30005, by rfl⟩ : syracuseStep 2560469 = 60011) (by norm_num)
theorem B6827917 : Blo 1893435 6827917 := bstep (se 3 (by rfl) ⟨1280234, by rfl⟩ : syracuseStep 6827917 = 2560469) B2560469
theorem B9103889 : Blo 1893435 9103889 := bstep (se 2 (by rfl) ⟨3413958, by rfl⟩ : syracuseStep 9103889 = 6827917) B6827917
theorem B6069259 : Blo 1893435 6069259 := bstep (se 1 (by rfl) ⟨4551944, by rfl⟩ : syracuseStep 6069259 = 9103889) B9103889
theorem B8092345 : Blo 1893435 8092345 := bstep (se 2 (by rfl) ⟨3034629, by rfl⟩ : syracuseStep 8092345 = 6069259) B6069259
theorem B10789793 : Blo 1893435 10789793 := bstep (se 2 (by rfl) ⟨4046172, by rfl⟩ : syracuseStep 10789793 = 8092345) B8092345
theorem B7193195 : Blo 1893435 7193195 := bstep (se 1 (by rfl) ⟨5394896, by rfl⟩ : syracuseStep 7193195 = 10789793) B10789793
theorem B4795463 : Blo 1893435 4795463 := bstep (se 1 (by rfl) ⟨3596597, by rfl⟩ : syracuseStep 4795463 = 7193195) B7193195
theorem B3196975 : Blo 1893435 3196975 := bstep (se 1 (by rfl) ⟨2397731, by rfl⟩ : syracuseStep 3196975 = 4795463) B4795463
theorem B4262633 : Blo 1893435 4262633 := bstep (se 2 (by rfl) ⟨1598487, by rfl⟩ : syracuseStep 4262633 = 3196975) B3196975
theorem B2841755 : Blo 1893435 2841755 := bstep (se 1 (by rfl) ⟨2131316, by rfl⟩ : syracuseStep 2841755 = 4262633) B4262633
theorem B1894503 : Blo 1893435 1894503 := bstep (se 1 (by rfl) ⟨1420877, by rfl⟩ : syracuseStep 1894503 = 2841755) B2841755
theorem B2131321 : Blo 1893435 2131321 := bbase (se 2 (by rfl) ⟨799245, by rfl⟩ : syracuseStep 2131321 = 1598491) (by norm_num)
theorem B2841761 : Blo 1893435 2841761 := bstep (se 2 (by rfl) ⟨1065660, by rfl⟩ : syracuseStep 2841761 = 2131321) B2131321
theorem B1894507 : Blo 1893435 1894507 := bstep (se 1 (by rfl) ⟨1420880, by rfl⟩ : syracuseStep 1894507 = 2841761) B2841761
theorem B7491685 : Blo 1893435 7491685 := bbase (se 4 (by rfl) ⟨702345, by rfl⟩ : syracuseStep 7491685 = 1404691) (by norm_num)
theorem B9988913 : Blo 1893435 9988913 := bstep (se 2 (by rfl) ⟨3745842, by rfl⟩ : syracuseStep 9988913 = 7491685) B7491685
theorem B6659275 : Blo 1893435 6659275 := bstep (se 1 (by rfl) ⟨4994456, by rfl⟩ : syracuseStep 6659275 = 9988913) B9988913
theorem B8879033 : Blo 1893435 8879033 := bstep (se 2 (by rfl) ⟨3329637, by rfl⟩ : syracuseStep 8879033 = 6659275) B6659275
theorem B5919355 : Blo 1893435 5919355 := bstep (se 1 (by rfl) ⟨4439516, by rfl⟩ : syracuseStep 5919355 = 8879033) B8879033
theorem B7892473 : Blo 1893435 7892473 := bstep (se 2 (by rfl) ⟨2959677, by rfl⟩ : syracuseStep 7892473 = 5919355) B5919355
theorem B10523297 : Blo 1893435 10523297 := bstep (se 2 (by rfl) ⟨3946236, by rfl⟩ : syracuseStep 10523297 = 7892473) B7892473
theorem B28062125 : Blo 1893435 28062125 := bstep (se 3 (by rfl) ⟨5261648, by rfl⟩ : syracuseStep 28062125 = 10523297) B10523297
theorem B18708083 : Blo 1893435 18708083 := bstep (se 1 (by rfl) ⟨14031062, by rfl⟩ : syracuseStep 18708083 = 28062125) B28062125
theorem B12472055 : Blo 1893435 12472055 := bstep (se 1 (by rfl) ⟨9354041, by rfl⟩ : syracuseStep 12472055 = 18708083) B18708083
theorem B8314703 : Blo 1893435 8314703 := bstep (se 1 (by rfl) ⟨6236027, by rfl⟩ : syracuseStep 8314703 = 12472055) B12472055
theorem B5543135 : Blo 1893435 5543135 := bstep (se 1 (by rfl) ⟨4157351, by rfl⟩ : syracuseStep 5543135 = 8314703) B8314703
theorem B3695423 : Blo 1893435 3695423 := bstep (se 1 (by rfl) ⟨2771567, by rfl⟩ : syracuseStep 3695423 = 5543135) B5543135
theorem B9854461 : Blo 1893435 9854461 := bstep (se 3 (by rfl) ⟨1847711, by rfl⟩ : syracuseStep 9854461 = 3695423) B3695423
theorem B13139281 : Blo 1893435 13139281 := bstep (se 2 (by rfl) ⟨4927230, by rfl⟩ : syracuseStep 13139281 = 9854461) B9854461
theorem B17519041 : Blo 1893435 17519041 := bstep (se 2 (by rfl) ⟨6569640, by rfl⟩ : syracuseStep 17519041 = 13139281) B13139281
theorem B23358721 : Blo 1893435 23358721 := bstep (se 2 (by rfl) ⟨8759520, by rfl⟩ : syracuseStep 23358721 = 17519041) B17519041
theorem B31144961 : Blo 1893435 31144961 := bstep (se 2 (by rfl) ⟨11679360, by rfl⟩ : syracuseStep 31144961 = 23358721) B23358721
theorem B20763307 : Blo 1893435 20763307 := bstep (se 1 (by rfl) ⟨15572480, by rfl⟩ : syracuseStep 20763307 = 31144961) B31144961
theorem B110737637 : Blo 1893435 110737637 := bstep (se 4 (by rfl) ⟨10381653, by rfl⟩ : syracuseStep 110737637 = 20763307) B20763307
theorem B73825091 : Blo 1893435 73825091 := bstep (se 1 (by rfl) ⟨55368818, by rfl⟩ : syracuseStep 73825091 = 110737637) B110737637
theorem B49216727 : Blo 1893435 49216727 := bstep (se 1 (by rfl) ⟨36912545, by rfl⟩ : syracuseStep 49216727 = 73825091) B73825091
theorem B32811151 : Blo 1893435 32811151 := bstep (se 1 (by rfl) ⟨24608363, by rfl⟩ : syracuseStep 32811151 = 49216727) B49216727
theorem B43748201 : Blo 1893435 43748201 := bstep (se 2 (by rfl) ⟨16405575, by rfl⟩ : syracuseStep 43748201 = 32811151) B32811151
theorem B29165467 : Blo 1893435 29165467 := bstep (se 1 (by rfl) ⟨21874100, by rfl⟩ : syracuseStep 29165467 = 43748201) B43748201
theorem B38887289 : Blo 1893435 38887289 := bstep (se 2 (by rfl) ⟨14582733, by rfl⟩ : syracuseStep 38887289 = 29165467) B29165467
theorem B25924859 : Blo 1893435 25924859 := bstep (se 1 (by rfl) ⟨19443644, by rfl⟩ : syracuseStep 25924859 = 38887289) B38887289
theorem B17283239 : Blo 1893435 17283239 := bstep (se 1 (by rfl) ⟨12962429, by rfl⟩ : syracuseStep 17283239 = 25924859) B25924859
theorem B11522159 : Blo 1893435 11522159 := bstep (se 1 (by rfl) ⟨8641619, by rfl⟩ : syracuseStep 11522159 = 17283239) B17283239
theorem B7681439 : Blo 1893435 7681439 := bstep (se 1 (by rfl) ⟨5761079, by rfl⟩ : syracuseStep 7681439 = 11522159) B11522159
theorem B20483837 : Blo 1893435 20483837 := bstep (se 3 (by rfl) ⟨3840719, by rfl⟩ : syracuseStep 20483837 = 7681439) B7681439
theorem B13655891 : Blo 1893435 13655891 := bstep (se 1 (by rfl) ⟨10241918, by rfl⟩ : syracuseStep 13655891 = 20483837) B20483837
theorem B9103927 : Blo 1893435 9103927 := bstep (se 1 (by rfl) ⟨6827945, by rfl⟩ : syracuseStep 9103927 = 13655891) B13655891
theorem B12138569 : Blo 1893435 12138569 := bstep (se 2 (by rfl) ⟨4551963, by rfl⟩ : syracuseStep 12138569 = 9103927) B9103927
theorem B8092379 : Blo 1893435 8092379 := bstep (se 1 (by rfl) ⟨6069284, by rfl⟩ : syracuseStep 8092379 = 12138569) B12138569
theorem B5394919 : Blo 1893435 5394919 := bstep (se 1 (by rfl) ⟨4046189, by rfl⟩ : syracuseStep 5394919 = 8092379) B8092379
theorem B7193225 : Blo 1893435 7193225 := bstep (se 2 (by rfl) ⟨2697459, by rfl⟩ : syracuseStep 7193225 = 5394919) B5394919
theorem B4795483 : Blo 1893435 4795483 := bstep (se 1 (by rfl) ⟨3596612, by rfl⟩ : syracuseStep 4795483 = 7193225) B7193225
theorem B6393977 : Blo 1893435 6393977 := bstep (se 2 (by rfl) ⟨2397741, by rfl⟩ : syracuseStep 6393977 = 4795483) B4795483
theorem B4262651 : Blo 1893435 4262651 := bstep (se 1 (by rfl) ⟨3196988, by rfl⟩ : syracuseStep 4262651 = 6393977) B6393977
theorem B2841767 : Blo 1893435 2841767 := bstep (se 1 (by rfl) ⟨2131325, by rfl⟩ : syracuseStep 2841767 = 4262651) B4262651
theorem B1894511 : Blo 1893435 1894511 := bstep (se 1 (by rfl) ⟨1420883, by rfl⟩ : syracuseStep 1894511 = 2841767) B2841767
theorem B2841773 : Blo 1893435 2841773 := bbase (se 3 (by rfl) ⟨532832, by rfl⟩ : syracuseStep 2841773 = 1065665) (by norm_num)
theorem B1894515 : Blo 1893435 1894515 := bstep (se 1 (by rfl) ⟨1420886, by rfl⟩ : syracuseStep 1894515 = 2841773) B2841773
theorem B4262669 : Blo 1893435 4262669 := bbase (se 3 (by rfl) ⟨799250, by rfl⟩ : syracuseStep 4262669 = 1598501) (by norm_num)
theorem B2841779 : Blo 1893435 2841779 := bstep (se 1 (by rfl) ⟨2131334, by rfl⟩ : syracuseStep 2841779 = 4262669) B4262669
theorem B1894519 : Blo 1893435 1894519 := bstep (se 1 (by rfl) ⟨1420889, by rfl⟩ : syracuseStep 1894519 = 2841779) B2841779
theorem B2397757 : Blo 1893435 2397757 := bbase (se 3 (by rfl) ⟨449579, by rfl⟩ : syracuseStep 2397757 = 899159) (by norm_num)
theorem B3197009 : Blo 1893435 3197009 := bstep (se 2 (by rfl) ⟨1198878, by rfl⟩ : syracuseStep 3197009 = 2397757) B2397757
theorem B2131339 : Blo 1893435 2131339 := bstep (se 1 (by rfl) ⟨1598504, by rfl⟩ : syracuseStep 2131339 = 3197009) B3197009
theorem B2841785 : Blo 1893435 2841785 := bstep (se 2 (by rfl) ⟨1065669, by rfl⟩ : syracuseStep 2841785 = 2131339) B2131339
theorem B1894523 : Blo 1893435 1894523 := bstep (se 1 (by rfl) ⟨1420892, by rfl⟩ : syracuseStep 1894523 = 2841785) B2841785
theorem B2560501 : Blo 1893435 2560501 := bbase (se 5 (by rfl) ⟨120023, by rfl⟩ : syracuseStep 2560501 = 240047) (by norm_num)
theorem B13656005 : Blo 1893435 13656005 := bstep (se 4 (by rfl) ⟨1280250, by rfl⟩ : syracuseStep 13656005 = 2560501) B2560501
theorem B9104003 : Blo 1893435 9104003 := bstep (se 1 (by rfl) ⟨6828002, by rfl⟩ : syracuseStep 9104003 = 13656005) B13656005
theorem B6069335 : Blo 1893435 6069335 := bstep (se 1 (by rfl) ⟨4552001, by rfl⟩ : syracuseStep 6069335 = 9104003) B9104003
theorem B16184893 : Blo 1893435 16184893 := bstep (se 3 (by rfl) ⟨3034667, by rfl⟩ : syracuseStep 16184893 = 6069335) B6069335
theorem B21579857 : Blo 1893435 21579857 := bstep (se 2 (by rfl) ⟨8092446, by rfl⟩ : syracuseStep 21579857 = 16184893) B16184893
theorem B14386571 : Blo 1893435 14386571 := bstep (se 1 (by rfl) ⟨10789928, by rfl⟩ : syracuseStep 14386571 = 21579857) B21579857
theorem B9591047 : Blo 1893435 9591047 := bstep (se 1 (by rfl) ⟨7193285, by rfl⟩ : syracuseStep 9591047 = 14386571) B14386571
theorem B6394031 : Blo 1893435 6394031 := bstep (se 1 (by rfl) ⟨4795523, by rfl⟩ : syracuseStep 6394031 = 9591047) B9591047
theorem B4262687 : Blo 1893435 4262687 := bstep (se 1 (by rfl) ⟨3197015, by rfl⟩ : syracuseStep 4262687 = 6394031) B6394031
theorem B2841791 : Blo 1893435 2841791 := bstep (se 1 (by rfl) ⟨2131343, by rfl⟩ : syracuseStep 2841791 = 4262687) B4262687
theorem B1894527 : Blo 1893435 1894527 := bstep (se 1 (by rfl) ⟨1420895, by rfl⟩ : syracuseStep 1894527 = 2841791) B2841791
theorem B2841797 : Blo 1893435 2841797 := bbase (se 4 (by rfl) ⟨266418, by rfl⟩ : syracuseStep 2841797 = 532837) (by norm_num)
theorem B1894531 : Blo 1893435 1894531 := bstep (se 1 (by rfl) ⟨1420898, by rfl⟩ : syracuseStep 1894531 = 2841797) B2841797
theorem B3197029 : Blo 1893435 3197029 := bbase (se 4 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 3197029 = 599443) (by norm_num)
theorem B4262705 : Blo 1893435 4262705 := bstep (se 2 (by rfl) ⟨1598514, by rfl⟩ : syracuseStep 4262705 = 3197029) B3197029
theorem B2841803 : Blo 1893435 2841803 := bstep (se 1 (by rfl) ⟨2131352, by rfl⟩ : syracuseStep 2841803 = 4262705) B4262705
theorem B1894535 : Blo 1893435 1894535 := bstep (se 1 (by rfl) ⟨1420901, by rfl⟩ : syracuseStep 1894535 = 2841803) B2841803
theorem B2131357 : Blo 1893435 2131357 := bbase (se 3 (by rfl) ⟨399629, by rfl⟩ : syracuseStep 2131357 = 799259) (by norm_num)
theorem B2841809 : Blo 1893435 2841809 := bstep (se 2 (by rfl) ⟨1065678, by rfl⟩ : syracuseStep 2841809 = 2131357) B2131357
theorem B1894539 : Blo 1893435 1894539 := bstep (se 1 (by rfl) ⟨1420904, by rfl⟩ : syracuseStep 1894539 = 2841809) B2841809
theorem B6394085 : Blo 1893435 6394085 := bbase (se 4 (by rfl) ⟨599445, by rfl⟩ : syracuseStep 6394085 = 1198891) (by norm_num)
theorem B4262723 : Blo 1893435 4262723 := bstep (se 1 (by rfl) ⟨3197042, by rfl⟩ : syracuseStep 4262723 = 6394085) B6394085
theorem B2841815 : Blo 1893435 2841815 := bstep (se 1 (by rfl) ⟨2131361, by rfl⟩ : syracuseStep 2841815 = 4262723) B4262723
theorem B1894543 : Blo 1893435 1894543 := bstep (se 1 (by rfl) ⟨1420907, by rfl⟩ : syracuseStep 1894543 = 2841815) B2841815
theorem B2841821 : Blo 1893435 2841821 := bbase (se 3 (by rfl) ⟨532841, by rfl⟩ : syracuseStep 2841821 = 1065683) (by norm_num)
theorem B1894547 : Blo 1893435 1894547 := bstep (se 1 (by rfl) ⟨1420910, by rfl⟩ : syracuseStep 1894547 = 2841821) B2841821
theorem B4262741 : Blo 1893435 4262741 := bbase (se 9 (by rfl) ⟨12488, by rfl⟩ : syracuseStep 4262741 = 24977) (by norm_num)
theorem B2841827 : Blo 1893435 2841827 := bstep (se 1 (by rfl) ⟨2131370, by rfl⟩ : syracuseStep 2841827 = 4262741) B4262741
theorem B1894551 : Blo 1893435 1894551 := bstep (se 1 (by rfl) ⟨1420913, by rfl⟩ : syracuseStep 1894551 = 2841827) B2841827
theorem B5395045 : Blo 1893435 5395045 := bbase (se 4 (by rfl) ⟨505785, by rfl⟩ : syracuseStep 5395045 = 1011571) (by norm_num)
theorem B7193393 : Blo 1893435 7193393 := bstep (se 2 (by rfl) ⟨2697522, by rfl⟩ : syracuseStep 7193393 = 5395045) B5395045
theorem B4795595 : Blo 1893435 4795595 := bstep (se 1 (by rfl) ⟨3596696, by rfl⟩ : syracuseStep 4795595 = 7193393) B7193393
theorem B3197063 : Blo 1893435 3197063 := bstep (se 1 (by rfl) ⟨2397797, by rfl⟩ : syracuseStep 3197063 = 4795595) B4795595
theorem B2131375 : Blo 1893435 2131375 := bstep (se 1 (by rfl) ⟨1598531, by rfl⟩ : syracuseStep 2131375 = 3197063) B3197063
theorem B2841833 : Blo 1893435 2841833 := bstep (se 2 (by rfl) ⟨1065687, by rfl⟩ : syracuseStep 2841833 = 2131375) B2131375
theorem B1894555 : Blo 1893435 1894555 := bstep (se 1 (by rfl) ⟨1420916, by rfl⟩ : syracuseStep 1894555 = 2841833) B2841833
theorem B2430517 : Blo 1893435 2430517 := bbase (se 5 (by rfl) ⟨113930, by rfl⟩ : syracuseStep 2430517 = 227861) (by norm_num)
theorem B3240689 : Blo 1893435 3240689 := bstep (se 2 (by rfl) ⟨1215258, by rfl⟩ : syracuseStep 3240689 = 2430517) B2430517
theorem B8641837 : Blo 1893435 8641837 := bstep (se 3 (by rfl) ⟨1620344, by rfl⟩ : syracuseStep 8641837 = 3240689) B3240689
theorem B11522449 : Blo 1893435 11522449 := bstep (se 2 (by rfl) ⟨4320918, by rfl⟩ : syracuseStep 11522449 = 8641837) B8641837
theorem B15363265 : Blo 1893435 15363265 := bstep (se 2 (by rfl) ⟨5761224, by rfl⟩ : syracuseStep 15363265 = 11522449) B11522449
theorem B20484353 : Blo 1893435 20484353 := bstep (se 2 (by rfl) ⟨7681632, by rfl⟩ : syracuseStep 20484353 = 15363265) B15363265
theorem B54624941 : Blo 1893435 54624941 := bstep (se 3 (by rfl) ⟨10242176, by rfl⟩ : syracuseStep 54624941 = 20484353) B20484353
theorem B36416627 : Blo 1893435 36416627 := bstep (se 1 (by rfl) ⟨27312470, by rfl⟩ : syracuseStep 36416627 = 54624941) B54624941
theorem B24277751 : Blo 1893435 24277751 := bstep (se 1 (by rfl) ⟨18208313, by rfl⟩ : syracuseStep 24277751 = 36416627) B36416627
theorem B16185167 : Blo 1893435 16185167 := bstep (se 1 (by rfl) ⟨12138875, by rfl⟩ : syracuseStep 16185167 = 24277751) B24277751
theorem B10790111 : Blo 1893435 10790111 := bstep (se 1 (by rfl) ⟨8092583, by rfl⟩ : syracuseStep 10790111 = 16185167) B16185167
theorem B7193407 : Blo 1893435 7193407 := bstep (se 1 (by rfl) ⟨5395055, by rfl⟩ : syracuseStep 7193407 = 10790111) B10790111
theorem B9591209 : Blo 1893435 9591209 := bstep (se 2 (by rfl) ⟨3596703, by rfl⟩ : syracuseStep 9591209 = 7193407) B7193407
theorem B6394139 : Blo 1893435 6394139 := bstep (se 1 (by rfl) ⟨4795604, by rfl⟩ : syracuseStep 6394139 = 9591209) B9591209
theorem B4262759 : Blo 1893435 4262759 := bstep (se 1 (by rfl) ⟨3197069, by rfl⟩ : syracuseStep 4262759 = 6394139) B6394139
theorem B2841839 : Blo 1893435 2841839 := bstep (se 1 (by rfl) ⟨2131379, by rfl⟩ : syracuseStep 2841839 = 4262759) B4262759
theorem B1894559 : Blo 1893435 1894559 := bstep (se 1 (by rfl) ⟨1420919, by rfl⟩ : syracuseStep 1894559 = 2841839) B2841839
theorem B2841845 : Blo 1893435 2841845 := bbase (se 5 (by rfl) ⟨133211, by rfl⟩ : syracuseStep 2841845 = 266423) (by norm_num)
theorem B1894563 : Blo 1893435 1894563 := bstep (se 1 (by rfl) ⟨1420922, by rfl⟩ : syracuseStep 1894563 = 2841845) B2841845
theorem B9104197 : Blo 1893435 9104197 := bbase (se 4 (by rfl) ⟨853518, by rfl⟩ : syracuseStep 9104197 = 1707037) (by norm_num)
theorem B12138929 : Blo 1893435 12138929 := bstep (se 2 (by rfl) ⟨4552098, by rfl⟩ : syracuseStep 12138929 = 9104197) B9104197
theorem B8092619 : Blo 1893435 8092619 := bstep (se 1 (by rfl) ⟨6069464, by rfl⟩ : syracuseStep 8092619 = 12138929) B12138929
theorem B5395079 : Blo 1893435 5395079 := bstep (se 1 (by rfl) ⟨4046309, by rfl⟩ : syracuseStep 5395079 = 8092619) B8092619
theorem B3596719 : Blo 1893435 3596719 := bstep (se 1 (by rfl) ⟨2697539, by rfl⟩ : syracuseStep 3596719 = 5395079) B5395079
theorem B4795625 : Blo 1893435 4795625 := bstep (se 2 (by rfl) ⟨1798359, by rfl⟩ : syracuseStep 4795625 = 3596719) B3596719
theorem B3197083 : Blo 1893435 3197083 := bstep (se 1 (by rfl) ⟨2397812, by rfl⟩ : syracuseStep 3197083 = 4795625) B4795625
theorem B4262777 : Blo 1893435 4262777 := bstep (se 2 (by rfl) ⟨1598541, by rfl⟩ : syracuseStep 4262777 = 3197083) B3197083
theorem B2841851 : Blo 1893435 2841851 := bstep (se 1 (by rfl) ⟨2131388, by rfl⟩ : syracuseStep 2841851 = 4262777) B4262777
theorem B1894567 : Blo 1893435 1894567 := bstep (se 1 (by rfl) ⟨1420925, by rfl⟩ : syracuseStep 1894567 = 2841851) B2841851
theorem B2131393 : Blo 1893435 2131393 := bbase (se 2 (by rfl) ⟨799272, by rfl⟩ : syracuseStep 2131393 = 1598545) (by norm_num)
theorem B2841857 : Blo 1893435 2841857 := bstep (se 2 (by rfl) ⟨1065696, by rfl⟩ : syracuseStep 2841857 = 2131393) B2131393
theorem B1894571 : Blo 1893435 1894571 := bstep (se 1 (by rfl) ⟨1420928, by rfl⟩ : syracuseStep 1894571 = 2841857) B2841857
theorem B4795645 : Blo 1893435 4795645 := bbase (se 3 (by rfl) ⟨899183, by rfl⟩ : syracuseStep 4795645 = 1798367) (by norm_num)
theorem B6394193 : Blo 1893435 6394193 := bstep (se 2 (by rfl) ⟨2397822, by rfl⟩ : syracuseStep 6394193 = 4795645) B4795645
theorem B4262795 : Blo 1893435 4262795 := bstep (se 1 (by rfl) ⟨3197096, by rfl⟩ : syracuseStep 4262795 = 6394193) B6394193
theorem B2841863 : Blo 1893435 2841863 := bstep (se 1 (by rfl) ⟨2131397, by rfl⟩ : syracuseStep 2841863 = 4262795) B4262795
theorem B1894575 : Blo 1893435 1894575 := bstep (se 1 (by rfl) ⟨1420931, by rfl⟩ : syracuseStep 1894575 = 2841863) B2841863
theorem B2841869 : Blo 1893435 2841869 := bbase (se 3 (by rfl) ⟨532850, by rfl⟩ : syracuseStep 2841869 = 1065701) (by norm_num)
theorem B1894579 : Blo 1893435 1894579 := bstep (se 1 (by rfl) ⟨1420934, by rfl⟩ : syracuseStep 1894579 = 2841869) B2841869
theorem B4262813 : Blo 1893435 4262813 := bbase (se 3 (by rfl) ⟨799277, by rfl⟩ : syracuseStep 4262813 = 1598555) (by norm_num)
theorem B2841875 : Blo 1893435 2841875 := bstep (se 1 (by rfl) ⟨2131406, by rfl⟩ : syracuseStep 2841875 = 4262813) B4262813
theorem B1894583 : Blo 1893435 1894583 := bstep (se 1 (by rfl) ⟨1420937, by rfl⟩ : syracuseStep 1894583 = 2841875) B2841875
theorem B3197117 : Blo 1893435 3197117 := bbase (se 3 (by rfl) ⟨599459, by rfl⟩ : syracuseStep 3197117 = 1198919) (by norm_num)
theorem B2131411 : Blo 1893435 2131411 := bstep (se 1 (by rfl) ⟨1598558, by rfl⟩ : syracuseStep 2131411 = 3197117) B3197117
theorem B2841881 : Blo 1893435 2841881 := bstep (se 2 (by rfl) ⟨1065705, by rfl⟩ : syracuseStep 2841881 = 2131411) B2131411
theorem B1894587 : Blo 1893435 1894587 := bstep (se 1 (by rfl) ⟨1420940, by rfl⟩ : syracuseStep 1894587 = 2841881) B2841881
theorem B10790293 : Blo 1893435 10790293 := bbase (se 6 (by rfl) ⟨252897, by rfl⟩ : syracuseStep 10790293 = 505795) (by norm_num)
theorem B14387057 : Blo 1893435 14387057 := bstep (se 2 (by rfl) ⟨5395146, by rfl⟩ : syracuseStep 14387057 = 10790293) B10790293
theorem B9591371 : Blo 1893435 9591371 := bstep (se 1 (by rfl) ⟨7193528, by rfl⟩ : syracuseStep 9591371 = 14387057) B14387057
theorem B6394247 : Blo 1893435 6394247 := bstep (se 1 (by rfl) ⟨4795685, by rfl⟩ : syracuseStep 6394247 = 9591371) B9591371
theorem B4262831 : Blo 1893435 4262831 := bstep (se 1 (by rfl) ⟨3197123, by rfl⟩ : syracuseStep 4262831 = 6394247) B6394247
theorem B2841887 : Blo 1893435 2841887 := bstep (se 1 (by rfl) ⟨2131415, by rfl⟩ : syracuseStep 2841887 = 4262831) B4262831
theorem B1894591 : Blo 1893435 1894591 := bstep (se 1 (by rfl) ⟨1420943, by rfl⟩ : syracuseStep 1894591 = 2841887) B2841887
theorem B2841893 : Blo 1893435 2841893 := bbase (se 4 (by rfl) ⟨266427, by rfl⟩ : syracuseStep 2841893 = 532855) (by norm_num)
theorem B1894595 : Blo 1893435 1894595 := bstep (se 1 (by rfl) ⟨1420946, by rfl⟩ : syracuseStep 1894595 = 2841893) B2841893
theorem B2397853 : Blo 1893435 2397853 := bbase (se 3 (by rfl) ⟨449597, by rfl⟩ : syracuseStep 2397853 = 899195) (by norm_num)
theorem B3197137 : Blo 1893435 3197137 := bstep (se 2 (by rfl) ⟨1198926, by rfl⟩ : syracuseStep 3197137 = 2397853) B2397853
theorem B4262849 : Blo 1893435 4262849 := bstep (se 2 (by rfl) ⟨1598568, by rfl⟩ : syracuseStep 4262849 = 3197137) B3197137
theorem B2841899 : Blo 1893435 2841899 := bstep (se 1 (by rfl) ⟨2131424, by rfl⟩ : syracuseStep 2841899 = 4262849) B4262849
theorem B1894599 : Blo 1893435 1894599 := bstep (se 1 (by rfl) ⟨1420949, by rfl⟩ : syracuseStep 1894599 = 2841899) B2841899
theorem B2131429 : Blo 1893435 2131429 := bbase (se 4 (by rfl) ⟨199821, by rfl⟩ : syracuseStep 2131429 = 399643) (by norm_num)
theorem B2841905 : Blo 1893435 2841905 := bstep (se 2 (by rfl) ⟨1065714, by rfl⟩ : syracuseStep 2841905 = 2131429) B2131429
theorem B1894603 : Blo 1893435 1894603 := bstep (se 1 (by rfl) ⟨1420952, by rfl⟩ : syracuseStep 1894603 = 2841905) B2841905
theorem B6828293 : Blo 1893435 6828293 := bbase (se 4 (by rfl) ⟨640152, by rfl⟩ : syracuseStep 6828293 = 1280305) (by norm_num)
theorem B4552195 : Blo 1893435 4552195 := bstep (se 1 (by rfl) ⟨3414146, by rfl⟩ : syracuseStep 4552195 = 6828293) B6828293
theorem B6069593 : Blo 1893435 6069593 := bstep (se 2 (by rfl) ⟨2276097, by rfl⟩ : syracuseStep 6069593 = 4552195) B4552195
theorem B4046395 : Blo 1893435 4046395 := bstep (se 1 (by rfl) ⟨3034796, by rfl⟩ : syracuseStep 4046395 = 6069593) B6069593
theorem B5395193 : Blo 1893435 5395193 := bstep (se 2 (by rfl) ⟨2023197, by rfl⟩ : syracuseStep 5395193 = 4046395) B4046395
theorem B3596795 : Blo 1893435 3596795 := bstep (se 1 (by rfl) ⟨2697596, by rfl⟩ : syracuseStep 3596795 = 5395193) B5395193
theorem B2397863 : Blo 1893435 2397863 := bstep (se 1 (by rfl) ⟨1798397, by rfl⟩ : syracuseStep 2397863 = 3596795) B3596795
theorem B6394301 : Blo 1893435 6394301 := bstep (se 3 (by rfl) ⟨1198931, by rfl⟩ : syracuseStep 6394301 = 2397863) B2397863
theorem B4262867 : Blo 1893435 4262867 := bstep (se 1 (by rfl) ⟨3197150, by rfl⟩ : syracuseStep 4262867 = 6394301) B6394301
theorem B2841911 : Blo 1893435 2841911 := bstep (se 1 (by rfl) ⟨2131433, by rfl⟩ : syracuseStep 2841911 = 4262867) B4262867
theorem B1894607 : Blo 1893435 1894607 := bstep (se 1 (by rfl) ⟨1420955, by rfl⟩ : syracuseStep 1894607 = 2841911) B2841911
theorem B2841917 : Blo 1893435 2841917 := bbase (se 3 (by rfl) ⟨532859, by rfl⟩ : syracuseStep 2841917 = 1065719) (by norm_num)
theorem B1894611 : Blo 1893435 1894611 := bstep (se 1 (by rfl) ⟨1420958, by rfl⟩ : syracuseStep 1894611 = 2841917) B2841917
theorem B4262885 : Blo 1893435 4262885 := bbase (se 4 (by rfl) ⟨399645, by rfl⟩ : syracuseStep 4262885 = 799291) (by norm_num)
theorem B2841923 : Blo 1893435 2841923 := bstep (se 1 (by rfl) ⟨2131442, by rfl⟩ : syracuseStep 2841923 = 4262885) B4262885
theorem B1894615 : Blo 1893435 1894615 := bstep (se 1 (by rfl) ⟨1420961, by rfl⟩ : syracuseStep 1894615 = 2841923) B2841923
theorem B4795757 : Blo 1893435 4795757 := bbase (se 3 (by rfl) ⟨899204, by rfl⟩ : syracuseStep 4795757 = 1798409) (by norm_num)
theorem B3197171 : Blo 1893435 3197171 := bstep (se 1 (by rfl) ⟨2397878, by rfl⟩ : syracuseStep 3197171 = 4795757) B4795757
theorem B2131447 : Blo 1893435 2131447 := bstep (se 1 (by rfl) ⟨1598585, by rfl⟩ : syracuseStep 2131447 = 3197171) B3197171
theorem B2841929 : Blo 1893435 2841929 := bstep (se 2 (by rfl) ⟨1065723, by rfl⟩ : syracuseStep 2841929 = 2131447) B2131447
theorem B1894619 : Blo 1893435 1894619 := bstep (se 1 (by rfl) ⟨1420964, by rfl⟩ : syracuseStep 1894619 = 2841929) B2841929
theorem B4046429 : Blo 1893435 4046429 := bbase (se 3 (by rfl) ⟨758705, by rfl⟩ : syracuseStep 4046429 = 1517411) (by norm_num)
theorem B2697619 : Blo 1893435 2697619 := bstep (se 1 (by rfl) ⟨2023214, by rfl⟩ : syracuseStep 2697619 = 4046429) B4046429
theorem B3596825 : Blo 1893435 3596825 := bstep (se 2 (by rfl) ⟨1348809, by rfl⟩ : syracuseStep 3596825 = 2697619) B2697619
theorem B9591533 : Blo 1893435 9591533 := bstep (se 3 (by rfl) ⟨1798412, by rfl⟩ : syracuseStep 9591533 = 3596825) B3596825
theorem B6394355 : Blo 1893435 6394355 := bstep (se 1 (by rfl) ⟨4795766, by rfl⟩ : syracuseStep 6394355 = 9591533) B9591533
theorem B4262903 : Blo 1893435 4262903 := bstep (se 1 (by rfl) ⟨3197177, by rfl⟩ : syracuseStep 4262903 = 6394355) B6394355
theorem B2841935 : Blo 1893435 2841935 := bstep (se 1 (by rfl) ⟨2131451, by rfl⟩ : syracuseStep 2841935 = 4262903) B4262903
theorem B1894623 : Blo 1893435 1894623 := bstep (se 1 (by rfl) ⟨1420967, by rfl⟩ : syracuseStep 1894623 = 2841935) B2841935
theorem B2841941 : Blo 1893435 2841941 := bbase (se 11 (by rfl) ⟨2081, by rfl⟩ : syracuseStep 2841941 = 4163) (by norm_num)
theorem B1894627 : Blo 1893435 1894627 := bstep (se 1 (by rfl) ⟨1420970, by rfl⟩ : syracuseStep 1894627 = 2841941) B2841941
theorem B4552253 : Blo 1893435 4552253 := bbase (se 3 (by rfl) ⟨853547, by rfl⟩ : syracuseStep 4552253 = 1707095) (by norm_num)
theorem B3034835 : Blo 1893435 3034835 := bstep (se 1 (by rfl) ⟨2276126, by rfl⟩ : syracuseStep 3034835 = 4552253) B4552253
theorem B2023223 : Blo 1893435 2023223 := bstep (se 1 (by rfl) ⟨1517417, by rfl⟩ : syracuseStep 2023223 = 3034835) B3034835
theorem B5395261 : Blo 1893435 5395261 := bstep (se 3 (by rfl) ⟨1011611, by rfl⟩ : syracuseStep 5395261 = 2023223) B2023223
theorem B7193681 : Blo 1893435 7193681 := bstep (se 2 (by rfl) ⟨2697630, by rfl⟩ : syracuseStep 7193681 = 5395261) B5395261
theorem B4795787 : Blo 1893435 4795787 := bstep (se 1 (by rfl) ⟨3596840, by rfl⟩ : syracuseStep 4795787 = 7193681) B7193681
theorem B3197191 : Blo 1893435 3197191 := bstep (se 1 (by rfl) ⟨2397893, by rfl⟩ : syracuseStep 3197191 = 4795787) B4795787
theorem B4262921 : Blo 1893435 4262921 := bstep (se 2 (by rfl) ⟨1598595, by rfl⟩ : syracuseStep 4262921 = 3197191) B3197191
theorem B2841947 : Blo 1893435 2841947 := bstep (se 1 (by rfl) ⟨2131460, by rfl⟩ : syracuseStep 2841947 = 4262921) B4262921
theorem B1894631 : Blo 1893435 1894631 := bstep (se 1 (by rfl) ⟨1420973, by rfl⟩ : syracuseStep 1894631 = 2841947) B2841947
theorem B2131465 : Blo 1893435 2131465 := bbase (se 2 (by rfl) ⟨799299, by rfl⟩ : syracuseStep 2131465 = 1598599) (by norm_num)
theorem B2841953 : Blo 1893435 2841953 := bstep (se 2 (by rfl) ⟨1065732, by rfl⟩ : syracuseStep 2841953 = 2131465) B2131465
theorem B1894635 : Blo 1893435 1894635 := bstep (se 1 (by rfl) ⟨1420976, by rfl⟩ : syracuseStep 1894635 = 2841953) B2841953
theorem B30727829 : Blo 1893435 30727829 := bbase (se 6 (by rfl) ⟨720183, by rfl⟩ : syracuseStep 30727829 = 1440367) (by norm_num)
theorem B20485219 : Blo 1893435 20485219 := bstep (se 1 (by rfl) ⟨15363914, by rfl⟩ : syracuseStep 20485219 = 30727829) B30727829
theorem B27313625 : Blo 1893435 27313625 := bstep (se 2 (by rfl) ⟨10242609, by rfl⟩ : syracuseStep 27313625 = 20485219) B20485219
theorem B18209083 : Blo 1893435 18209083 := bstep (se 1 (by rfl) ⟨13656812, by rfl⟩ : syracuseStep 18209083 = 27313625) B27313625
theorem B24278777 : Blo 1893435 24278777 := bstep (se 2 (by rfl) ⟨9104541, by rfl⟩ : syracuseStep 24278777 = 18209083) B18209083
theorem B16185851 : Blo 1893435 16185851 := bstep (se 1 (by rfl) ⟨12139388, by rfl⟩ : syracuseStep 16185851 = 24278777) B24278777
theorem B10790567 : Blo 1893435 10790567 := bstep (se 1 (by rfl) ⟨8092925, by rfl⟩ : syracuseStep 10790567 = 16185851) B16185851
theorem B7193711 : Blo 1893435 7193711 := bstep (se 1 (by rfl) ⟨5395283, by rfl⟩ : syracuseStep 7193711 = 10790567) B10790567
theorem B4795807 : Blo 1893435 4795807 := bstep (se 1 (by rfl) ⟨3596855, by rfl⟩ : syracuseStep 4795807 = 7193711) B7193711
theorem B6394409 : Blo 1893435 6394409 := bstep (se 2 (by rfl) ⟨2397903, by rfl⟩ : syracuseStep 6394409 = 4795807) B4795807
theorem B4262939 : Blo 1893435 4262939 := bstep (se 1 (by rfl) ⟨3197204, by rfl⟩ : syracuseStep 4262939 = 6394409) B6394409
theorem B2841959 : Blo 1893435 2841959 := bstep (se 1 (by rfl) ⟨2131469, by rfl⟩ : syracuseStep 2841959 = 4262939) B4262939
theorem B1894639 : Blo 1893435 1894639 := bstep (se 1 (by rfl) ⟨1420979, by rfl⟩ : syracuseStep 1894639 = 2841959) B2841959
theorem B2841965 : Blo 1893435 2841965 := bbase (se 3 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 2841965 = 1065737) (by norm_num)
theorem B1894643 : Blo 1893435 1894643 := bstep (se 1 (by rfl) ⟨1420982, by rfl⟩ : syracuseStep 1894643 = 2841965) B2841965
theorem B4262957 : Blo 1893435 4262957 := bbase (se 3 (by rfl) ⟨799304, by rfl⟩ : syracuseStep 4262957 = 1598609) (by norm_num)
theorem B2841971 : Blo 1893435 2841971 := bstep (se 1 (by rfl) ⟨2131478, by rfl⟩ : syracuseStep 2841971 = 4262957) B4262957
theorem B1894647 : Blo 1893435 1894647 := bstep (se 1 (by rfl) ⟨1420985, by rfl⟩ : syracuseStep 1894647 = 2841971) B2841971
theorem B4552301 : Blo 1893435 4552301 := bbase (se 3 (by rfl) ⟨853556, by rfl⟩ : syracuseStep 4552301 = 1707113) (by norm_num)
theorem B12139469 : Blo 1893435 12139469 := bstep (se 3 (by rfl) ⟨2276150, by rfl⟩ : syracuseStep 12139469 = 4552301) B4552301
theorem B8092979 : Blo 1893435 8092979 := bstep (se 1 (by rfl) ⟨6069734, by rfl⟩ : syracuseStep 8092979 = 12139469) B12139469
theorem B5395319 : Blo 1893435 5395319 := bstep (se 1 (by rfl) ⟨4046489, by rfl⟩ : syracuseStep 5395319 = 8092979) B8092979
theorem B3596879 : Blo 1893435 3596879 := bstep (se 1 (by rfl) ⟨2697659, by rfl⟩ : syracuseStep 3596879 = 5395319) B5395319
theorem B2397919 : Blo 1893435 2397919 := bstep (se 1 (by rfl) ⟨1798439, by rfl⟩ : syracuseStep 2397919 = 3596879) B3596879
theorem B3197225 : Blo 1893435 3197225 := bstep (se 2 (by rfl) ⟨1198959, by rfl⟩ : syracuseStep 3197225 = 2397919) B2397919
theorem B2131483 : Blo 1893435 2131483 := bstep (se 1 (by rfl) ⟨1598612, by rfl⟩ : syracuseStep 2131483 = 3197225) B3197225
theorem B2841977 : Blo 1893435 2841977 := bstep (se 2 (by rfl) ⟨1065741, by rfl⟩ : syracuseStep 2841977 = 2131483) B2131483
theorem B1894651 : Blo 1893435 1894651 := bstep (se 1 (by rfl) ⟨1420988, by rfl⟩ : syracuseStep 1894651 = 2841977) B2841977
theorem B4552309 : Blo 1893435 4552309 := bbase (se 5 (by rfl) ⟨213389, by rfl⟩ : syracuseStep 4552309 = 426779) (by norm_num)
theorem B6069745 : Blo 1893435 6069745 := bstep (se 2 (by rfl) ⟨2276154, by rfl⟩ : syracuseStep 6069745 = 4552309) B4552309
theorem B32371973 : Blo 1893435 32371973 := bstep (se 4 (by rfl) ⟨3034872, by rfl⟩ : syracuseStep 32371973 = 6069745) B6069745
theorem B21581315 : Blo 1893435 21581315 := bstep (se 1 (by rfl) ⟨16185986, by rfl⟩ : syracuseStep 21581315 = 32371973) B32371973
theorem B14387543 : Blo 1893435 14387543 := bstep (se 1 (by rfl) ⟨10790657, by rfl⟩ : syracuseStep 14387543 = 21581315) B21581315
theorem B9591695 : Blo 1893435 9591695 := bstep (se 1 (by rfl) ⟨7193771, by rfl⟩ : syracuseStep 9591695 = 14387543) B14387543
theorem B6394463 : Blo 1893435 6394463 := bstep (se 1 (by rfl) ⟨4795847, by rfl⟩ : syracuseStep 6394463 = 9591695) B9591695
theorem B4262975 : Blo 1893435 4262975 := bstep (se 1 (by rfl) ⟨3197231, by rfl⟩ : syracuseStep 4262975 = 6394463) B6394463
theorem B2841983 : Blo 1893435 2841983 := bstep (se 1 (by rfl) ⟨2131487, by rfl⟩ : syracuseStep 2841983 = 4262975) B4262975
theorem B1894655 : Blo 1893435 1894655 := bstep (se 1 (by rfl) ⟨1420991, by rfl⟩ : syracuseStep 1894655 = 2841983) B2841983
theorem B2841989 : Blo 1893435 2841989 := bbase (se 4 (by rfl) ⟨266436, by rfl⟩ : syracuseStep 2841989 = 532873) (by norm_num)
theorem B1894659 : Blo 1893435 1894659 := bstep (se 1 (by rfl) ⟨1420994, by rfl⟩ : syracuseStep 1894659 = 2841989) B2841989
theorem B3197245 : Blo 1893435 3197245 := bbase (se 3 (by rfl) ⟨599483, by rfl⟩ : syracuseStep 3197245 = 1198967) (by norm_num)
theorem B4262993 : Blo 1893435 4262993 := bstep (se 2 (by rfl) ⟨1598622, by rfl⟩ : syracuseStep 4262993 = 3197245) B3197245
theorem B2841995 : Blo 1893435 2841995 := bstep (se 1 (by rfl) ⟨2131496, by rfl⟩ : syracuseStep 2841995 = 4262993) B4262993
theorem B1894663 : Blo 1893435 1894663 := bstep (se 1 (by rfl) ⟨1420997, by rfl⟩ : syracuseStep 1894663 = 2841995) B2841995
theorem B2131501 : Blo 1893435 2131501 := bbase (se 3 (by rfl) ⟨399656, by rfl⟩ : syracuseStep 2131501 = 799313) (by norm_num)
theorem B2842001 : Blo 1893435 2842001 := bstep (se 2 (by rfl) ⟨1065750, by rfl⟩ : syracuseStep 2842001 = 2131501) B2131501
theorem B1894667 : Blo 1893435 1894667 := bstep (se 1 (by rfl) ⟨1421000, by rfl⟩ : syracuseStep 1894667 = 2842001) B2842001
theorem B6394517 : Blo 1893435 6394517 := bbase (se 6 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 6394517 = 299743) (by norm_num)
theorem B4263011 : Blo 1893435 4263011 := bstep (se 1 (by rfl) ⟨3197258, by rfl⟩ : syracuseStep 4263011 = 6394517) B6394517
theorem B2842007 : Blo 1893435 2842007 := bstep (se 1 (by rfl) ⟨2131505, by rfl⟩ : syracuseStep 2842007 = 4263011) B4263011
theorem B1894671 : Blo 1893435 1894671 := bstep (se 1 (by rfl) ⟨1421003, by rfl⟩ : syracuseStep 1894671 = 2842007) B2842007
theorem B2842013 : Blo 1893435 2842013 := bbase (se 3 (by rfl) ⟨532877, by rfl⟩ : syracuseStep 2842013 = 1065755) (by norm_num)
theorem B1894675 : Blo 1893435 1894675 := bstep (se 1 (by rfl) ⟨1421006, by rfl⟩ : syracuseStep 1894675 = 2842013) B2842013
theorem B4263029 : Blo 1893435 4263029 := bbase (se 5 (by rfl) ⟨199829, by rfl⟩ : syracuseStep 4263029 = 399659) (by norm_num)
theorem B2842019 : Blo 1893435 2842019 := bstep (se 1 (by rfl) ⟨2131514, by rfl⟩ : syracuseStep 2842019 = 4263029) B4263029
theorem B1894679 : Blo 1893435 1894679 := bstep (se 1 (by rfl) ⟨1421009, by rfl⟩ : syracuseStep 1894679 = 2842019) B2842019
theorem B16186229 : Blo 1893435 16186229 := bbase (se 5 (by rfl) ⟨758729, by rfl⟩ : syracuseStep 16186229 = 1517459) (by norm_num)
theorem B10790819 : Blo 1893435 10790819 := bstep (se 1 (by rfl) ⟨8093114, by rfl⟩ : syracuseStep 10790819 = 16186229) B16186229
theorem B7193879 : Blo 1893435 7193879 := bstep (se 1 (by rfl) ⟨5395409, by rfl⟩ : syracuseStep 7193879 = 10790819) B10790819
theorem B4795919 : Blo 1893435 4795919 := bstep (se 1 (by rfl) ⟨3596939, by rfl⟩ : syracuseStep 4795919 = 7193879) B7193879
theorem B3197279 : Blo 1893435 3197279 := bstep (se 1 (by rfl) ⟨2397959, by rfl⟩ : syracuseStep 3197279 = 4795919) B4795919
theorem B2131519 : Blo 1893435 2131519 := bstep (se 1 (by rfl) ⟨1598639, by rfl⟩ : syracuseStep 2131519 = 3197279) B3197279
theorem B2842025 : Blo 1893435 2842025 := bstep (se 2 (by rfl) ⟨1065759, by rfl⟩ : syracuseStep 2842025 = 2131519) B2131519
theorem B1894683 : Blo 1893435 1894683 := bstep (se 1 (by rfl) ⟨1421012, by rfl⟩ : syracuseStep 1894683 = 2842025) B2842025
theorem B7193893 : Blo 1893435 7193893 := bbase (se 4 (by rfl) ⟨674427, by rfl⟩ : syracuseStep 7193893 = 1348855) (by norm_num)
theorem B9591857 : Blo 1893435 9591857 := bstep (se 2 (by rfl) ⟨3596946, by rfl⟩ : syracuseStep 9591857 = 7193893) B7193893
theorem B6394571 : Blo 1893435 6394571 := bstep (se 1 (by rfl) ⟨4795928, by rfl⟩ : syracuseStep 6394571 = 9591857) B9591857
theorem B4263047 : Blo 1893435 4263047 := bstep (se 1 (by rfl) ⟨3197285, by rfl⟩ : syracuseStep 4263047 = 6394571) B6394571
theorem B2842031 : Blo 1893435 2842031 := bstep (se 1 (by rfl) ⟨2131523, by rfl⟩ : syracuseStep 2842031 = 4263047) B4263047
theorem B1894687 : Blo 1893435 1894687 := bstep (se 1 (by rfl) ⟨1421015, by rfl⟩ : syracuseStep 1894687 = 2842031) B2842031
theorem B2842037 : Blo 1893435 2842037 := bbase (se 5 (by rfl) ⟨133220, by rfl⟩ : syracuseStep 2842037 = 266441) (by norm_num)
theorem B1894691 : Blo 1893435 1894691 := bstep (se 1 (by rfl) ⟨1421018, by rfl⟩ : syracuseStep 1894691 = 2842037) B2842037
theorem B4795949 : Blo 1893435 4795949 := bbase (se 3 (by rfl) ⟨899240, by rfl⟩ : syracuseStep 4795949 = 1798481) (by norm_num)
theorem B3197299 : Blo 1893435 3197299 := bstep (se 1 (by rfl) ⟨2397974, by rfl⟩ : syracuseStep 3197299 = 4795949) B4795949
theorem B4263065 : Blo 1893435 4263065 := bstep (se 2 (by rfl) ⟨1598649, by rfl⟩ : syracuseStep 4263065 = 3197299) B3197299
theorem B2842043 : Blo 1893435 2842043 := bstep (se 1 (by rfl) ⟨2131532, by rfl⟩ : syracuseStep 2842043 = 4263065) B4263065
theorem B1894695 : Blo 1893435 1894695 := bstep (se 1 (by rfl) ⟨1421021, by rfl⟩ : syracuseStep 1894695 = 2842043) B2842043
theorem B2131537 : Blo 1893435 2131537 := bbase (se 2 (by rfl) ⟨799326, by rfl⟩ : syracuseStep 2131537 = 1598653) (by norm_num)
theorem B2842049 : Blo 1893435 2842049 := bstep (se 2 (by rfl) ⟨1065768, by rfl⟩ : syracuseStep 2842049 = 2131537) B2131537
theorem B1894699 : Blo 1893435 1894699 := bstep (se 1 (by rfl) ⟨1421024, by rfl⟩ : syracuseStep 1894699 = 2842049) B2842049
theorem B2697733 : Blo 1893435 2697733 := bbase (se 4 (by rfl) ⟨252912, by rfl⟩ : syracuseStep 2697733 = 505825) (by norm_num)
theorem B3596977 : Blo 1893435 3596977 := bstep (se 2 (by rfl) ⟨1348866, by rfl⟩ : syracuseStep 3596977 = 2697733) B2697733
theorem B4795969 : Blo 1893435 4795969 := bstep (se 2 (by rfl) ⟨1798488, by rfl⟩ : syracuseStep 4795969 = 3596977) B3596977
theorem B6394625 : Blo 1893435 6394625 := bstep (se 2 (by rfl) ⟨2397984, by rfl⟩ : syracuseStep 6394625 = 4795969) B4795969
theorem B4263083 : Blo 1893435 4263083 := bstep (se 1 (by rfl) ⟨3197312, by rfl⟩ : syracuseStep 4263083 = 6394625) B6394625
theorem B2842055 : Blo 1893435 2842055 := bstep (se 1 (by rfl) ⟨2131541, by rfl⟩ : syracuseStep 2842055 = 4263083) B4263083
theorem B1894703 : Blo 1893435 1894703 := bstep (se 1 (by rfl) ⟨1421027, by rfl⟩ : syracuseStep 1894703 = 2842055) B2842055
theorem B2842061 : Blo 1893435 2842061 := bbase (se 3 (by rfl) ⟨532886, by rfl⟩ : syracuseStep 2842061 = 1065773) (by norm_num)
theorem B1894707 : Blo 1893435 1894707 := bstep (se 1 (by rfl) ⟨1421030, by rfl⟩ : syracuseStep 1894707 = 2842061) B2842061
theorem B4263101 : Blo 1893435 4263101 := bbase (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) (by norm_num)
theorem B2842067 : Blo 1893435 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B1894711 : Blo 1893435 1894711 := bstep (se 1 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 1894711 = 2842067) B2842067
theorem B3197333 : Blo 1893435 3197333 := bbase (se 6 (by rfl) ⟨74937, by rfl⟩ : syracuseStep 3197333 = 149875) (by norm_num)
theorem B2131555 : Blo 1893435 2131555 := bstep (se 1 (by rfl) ⟨1598666, by rfl⟩ : syracuseStep 2131555 = 3197333) B3197333
theorem B2842073 : Blo 1893435 2842073 := bstep (se 2 (by rfl) ⟨1065777, by rfl⟩ : syracuseStep 2842073 = 2131555) B2131555
theorem B1894715 : Blo 1893435 1894715 := bstep (se 1 (by rfl) ⟨1421036, by rfl⟩ : syracuseStep 1894715 = 2842073) B2842073
theorem B15364565 : Blo 1893435 15364565 := bbase (se 7 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 15364565 = 360107) (by norm_num)
theorem B10243043 : Blo 1893435 10243043 := bstep (se 1 (by rfl) ⟨7682282, by rfl⟩ : syracuseStep 10243043 = 15364565) B15364565
theorem B6828695 : Blo 1893435 6828695 := bstep (se 1 (by rfl) ⟨5121521, by rfl⟩ : syracuseStep 6828695 = 10243043) B10243043
theorem B4552463 : Blo 1893435 4552463 := bstep (se 1 (by rfl) ⟨3414347, by rfl⟩ : syracuseStep 4552463 = 6828695) B6828695
theorem B12139901 : Blo 1893435 12139901 := bstep (se 3 (by rfl) ⟨2276231, by rfl⟩ : syracuseStep 12139901 = 4552463) B4552463
theorem B8093267 : Blo 1893435 8093267 := bstep (se 1 (by rfl) ⟨6069950, by rfl⟩ : syracuseStep 8093267 = 12139901) B12139901
theorem B5395511 : Blo 1893435 5395511 := bstep (se 1 (by rfl) ⟨4046633, by rfl⟩ : syracuseStep 5395511 = 8093267) B8093267
theorem B14388029 : Blo 1893435 14388029 := bstep (se 3 (by rfl) ⟨2697755, by rfl⟩ : syracuseStep 14388029 = 5395511) B5395511
theorem B9592019 : Blo 1893435 9592019 := bstep (se 1 (by rfl) ⟨7194014, by rfl⟩ : syracuseStep 9592019 = 14388029) B14388029
theorem B6394679 : Blo 1893435 6394679 := bstep (se 1 (by rfl) ⟨4796009, by rfl⟩ : syracuseStep 6394679 = 9592019) B9592019
theorem B4263119 : Blo 1893435 4263119 := bstep (se 1 (by rfl) ⟨3197339, by rfl⟩ : syracuseStep 4263119 = 6394679) B6394679
theorem B2842079 : Blo 1893435 2842079 := bstep (se 1 (by rfl) ⟨2131559, by rfl⟩ : syracuseStep 2842079 = 4263119) B4263119
theorem B1894719 : Blo 1893435 1894719 := bstep (se 1 (by rfl) ⟨1421039, by rfl⟩ : syracuseStep 1894719 = 2842079) B2842079
theorem B2842085 : Blo 1893435 2842085 := bbase (se 4 (by rfl) ⟨266445, by rfl⟩ : syracuseStep 2842085 = 532891) (by norm_num)
theorem B1894723 : Blo 1893435 1894723 := bstep (se 1 (by rfl) ⟨1421042, by rfl⟩ : syracuseStep 1894723 = 2842085) B2842085
theorem B6828725 : Blo 1893435 6828725 := bbase (se 5 (by rfl) ⟨320096, by rfl⟩ : syracuseStep 6828725 = 640193) (by norm_num)
theorem B18209933 : Blo 1893435 18209933 := bstep (se 3 (by rfl) ⟨3414362, by rfl⟩ : syracuseStep 18209933 = 6828725) B6828725
theorem B12139955 : Blo 1893435 12139955 := bstep (se 1 (by rfl) ⟨9104966, by rfl⟩ : syracuseStep 12139955 = 18209933) B18209933
theorem B8093303 : Blo 1893435 8093303 := bstep (se 1 (by rfl) ⟨6069977, by rfl⟩ : syracuseStep 8093303 = 12139955) B12139955
theorem B5395535 : Blo 1893435 5395535 := bstep (se 1 (by rfl) ⟨4046651, by rfl⟩ : syracuseStep 5395535 = 8093303) B8093303
theorem B3597023 : Blo 1893435 3597023 := bstep (se 1 (by rfl) ⟨2697767, by rfl⟩ : syracuseStep 3597023 = 5395535) B5395535
theorem B2398015 : Blo 1893435 2398015 := bstep (se 1 (by rfl) ⟨1798511, by rfl⟩ : syracuseStep 2398015 = 3597023) B3597023
theorem B3197353 : Blo 1893435 3197353 := bstep (se 2 (by rfl) ⟨1199007, by rfl⟩ : syracuseStep 3197353 = 2398015) B2398015
theorem B4263137 : Blo 1893435 4263137 := bstep (se 2 (by rfl) ⟨1598676, by rfl⟩ : syracuseStep 4263137 = 3197353) B3197353
theorem B2842091 : Blo 1893435 2842091 := bstep (se 1 (by rfl) ⟨2131568, by rfl⟩ : syracuseStep 2842091 = 4263137) B4263137
theorem B1894727 : Blo 1893435 1894727 := bstep (se 1 (by rfl) ⟨1421045, by rfl⟩ : syracuseStep 1894727 = 2842091) B2842091
theorem B2131573 : Blo 1893435 2131573 := bbase (se 5 (by rfl) ⟨99917, by rfl⟩ : syracuseStep 2131573 = 199835) (by norm_num)
theorem B2842097 : Blo 1893435 2842097 := bstep (se 2 (by rfl) ⟨1065786, by rfl⟩ : syracuseStep 2842097 = 2131573) B2131573
theorem B1894731 : Blo 1893435 1894731 := bstep (se 1 (by rfl) ⟨1421048, by rfl⟩ : syracuseStep 1894731 = 2842097) B2842097
theorem B2398025 : Blo 1893435 2398025 := bbase (se 2 (by rfl) ⟨899259, by rfl⟩ : syracuseStep 2398025 = 1798519) (by norm_num)
theorem B6394733 : Blo 1893435 6394733 := bstep (se 3 (by rfl) ⟨1199012, by rfl⟩ : syracuseStep 6394733 = 2398025) B2398025
theorem B4263155 : Blo 1893435 4263155 := bstep (se 1 (by rfl) ⟨3197366, by rfl⟩ : syracuseStep 4263155 = 6394733) B6394733
theorem B2842103 : Blo 1893435 2842103 := bstep (se 1 (by rfl) ⟨2131577, by rfl⟩ : syracuseStep 2842103 = 4263155) B4263155
theorem B1894735 : Blo 1893435 1894735 := bstep (se 1 (by rfl) ⟨1421051, by rfl⟩ : syracuseStep 1894735 = 2842103) B2842103
theorem B2842109 : Blo 1893435 2842109 := bbase (se 3 (by rfl) ⟨532895, by rfl⟩ : syracuseStep 2842109 = 1065791) (by norm_num)
theorem B1894739 : Blo 1893435 1894739 := bstep (se 1 (by rfl) ⟨1421054, by rfl⟩ : syracuseStep 1894739 = 2842109) B2842109
theorem B4263173 : Blo 1893435 4263173 := bbase (se 4 (by rfl) ⟨399672, by rfl⟩ : syracuseStep 4263173 = 799345) (by norm_num)
theorem B2842115 : Blo 1893435 2842115 := bstep (se 1 (by rfl) ⟨2131586, by rfl⟩ : syracuseStep 2842115 = 4263173) B4263173
theorem B1894743 : Blo 1893435 1894743 := bstep (se 1 (by rfl) ⟨1421057, by rfl⟩ : syracuseStep 1894743 = 2842115) B2842115
theorem B3597061 : Blo 1893435 3597061 := bbase (se 4 (by rfl) ⟨337224, by rfl⟩ : syracuseStep 3597061 = 674449) (by norm_num)
theorem B4796081 : Blo 1893435 4796081 := bstep (se 2 (by rfl) ⟨1798530, by rfl⟩ : syracuseStep 4796081 = 3597061) B3597061
theorem B3197387 : Blo 1893435 3197387 := bstep (se 1 (by rfl) ⟨2398040, by rfl⟩ : syracuseStep 3197387 = 4796081) B4796081
theorem B2131591 : Blo 1893435 2131591 := bstep (se 1 (by rfl) ⟨1598693, by rfl⟩ : syracuseStep 2131591 = 3197387) B3197387
theorem B2842121 : Blo 1893435 2842121 := bstep (se 2 (by rfl) ⟨1065795, by rfl⟩ : syracuseStep 2842121 = 2131591) B2131591
theorem B1894747 : Blo 1893435 1894747 := bstep (se 1 (by rfl) ⟨1421060, by rfl⟩ : syracuseStep 1894747 = 2842121) B2842121
theorem B9592181 : Blo 1893435 9592181 := bbase (se 5 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 9592181 = 899267) (by norm_num)
theorem B6394787 : Blo 1893435 6394787 := bstep (se 1 (by rfl) ⟨4796090, by rfl⟩ : syracuseStep 6394787 = 9592181) B9592181
theorem B4263191 : Blo 1893435 4263191 := bstep (se 1 (by rfl) ⟨3197393, by rfl⟩ : syracuseStep 4263191 = 6394787) B6394787
theorem B2842127 : Blo 1893435 2842127 := bstep (se 1 (by rfl) ⟨2131595, by rfl⟩ : syracuseStep 2842127 = 4263191) B4263191
theorem B1894751 : Blo 1893435 1894751 := bstep (se 1 (by rfl) ⟨1421063, by rfl⟩ : syracuseStep 1894751 = 2842127) B2842127
theorem B2842133 : Blo 1893435 2842133 := bbase (se 6 (by rfl) ⟨66612, by rfl⟩ : syracuseStep 2842133 = 133225) (by norm_num)
theorem B1894755 : Blo 1893435 1894755 := bstep (se 1 (by rfl) ⟨1421066, by rfl⟩ : syracuseStep 1894755 = 2842133) B2842133
theorem B3461005 : Blo 1893435 3461005 := bbase (se 3 (by rfl) ⟨648938, by rfl⟩ : syracuseStep 3461005 = 1297877) (by norm_num)
theorem B4614673 : Blo 1893435 4614673 := bstep (se 2 (by rfl) ⟨1730502, by rfl⟩ : syracuseStep 4614673 = 3461005) B3461005
theorem B6152897 : Blo 1893435 6152897 := bstep (se 2 (by rfl) ⟨2307336, by rfl⟩ : syracuseStep 6152897 = 4614673) B4614673
theorem B4101931 : Blo 1893435 4101931 := bstep (se 1 (by rfl) ⟨3076448, by rfl⟩ : syracuseStep 4101931 = 6152897) B6152897
theorem B21876965 : Blo 1893435 21876965 := bstep (se 4 (by rfl) ⟨2050965, by rfl⟩ : syracuseStep 21876965 = 4101931) B4101931
theorem B14584643 : Blo 1893435 14584643 := bstep (se 1 (by rfl) ⟨10938482, by rfl⟩ : syracuseStep 14584643 = 21876965) B21876965
theorem B9723095 : Blo 1893435 9723095 := bstep (se 1 (by rfl) ⟨7292321, by rfl⟩ : syracuseStep 9723095 = 14584643) B14584643
theorem B6482063 : Blo 1893435 6482063 := bstep (se 1 (by rfl) ⟨4861547, by rfl⟩ : syracuseStep 6482063 = 9723095) B9723095
theorem B17285501 : Blo 1893435 17285501 := bstep (se 3 (by rfl) ⟨3241031, by rfl⟩ : syracuseStep 17285501 = 6482063) B6482063
theorem B46094669 : Blo 1893435 46094669 := bstep (se 3 (by rfl) ⟨8642750, by rfl⟩ : syracuseStep 46094669 = 17285501) B17285501
theorem B30729779 : Blo 1893435 30729779 := bstep (se 1 (by rfl) ⟨23047334, by rfl⟩ : syracuseStep 30729779 = 46094669) B46094669
theorem B20486519 : Blo 1893435 20486519 := bstep (se 1 (by rfl) ⟨15364889, by rfl⟩ : syracuseStep 20486519 = 30729779) B30729779
theorem B13657679 : Blo 1893435 13657679 := bstep (se 1 (by rfl) ⟨10243259, by rfl⟩ : syracuseStep 13657679 = 20486519) B20486519
theorem B9105119 : Blo 1893435 9105119 := bstep (se 1 (by rfl) ⟨6828839, by rfl⟩ : syracuseStep 9105119 = 13657679) B13657679
theorem B6070079 : Blo 1893435 6070079 := bstep (se 1 (by rfl) ⟨4552559, by rfl⟩ : syracuseStep 6070079 = 9105119) B9105119
theorem B16186877 : Blo 1893435 16186877 := bstep (se 3 (by rfl) ⟨3035039, by rfl⟩ : syracuseStep 16186877 = 6070079) B6070079
theorem B10791251 : Blo 1893435 10791251 := bstep (se 1 (by rfl) ⟨8093438, by rfl⟩ : syracuseStep 10791251 = 16186877) B16186877
theorem B7194167 : Blo 1893435 7194167 := bstep (se 1 (by rfl) ⟨5395625, by rfl⟩ : syracuseStep 7194167 = 10791251) B10791251
theorem B4796111 : Blo 1893435 4796111 := bstep (se 1 (by rfl) ⟨3597083, by rfl⟩ : syracuseStep 4796111 = 7194167) B7194167
theorem B3197407 : Blo 1893435 3197407 := bstep (se 1 (by rfl) ⟨2398055, by rfl⟩ : syracuseStep 3197407 = 4796111) B4796111
theorem B4263209 : Blo 1893435 4263209 := bstep (se 2 (by rfl) ⟨1598703, by rfl⟩ : syracuseStep 4263209 = 3197407) B3197407
theorem B2842139 : Blo 1893435 2842139 := bstep (se 1 (by rfl) ⟨2131604, by rfl⟩ : syracuseStep 2842139 = 4263209) B4263209
theorem B1894759 : Blo 1893435 1894759 := bstep (se 1 (by rfl) ⟨1421069, by rfl⟩ : syracuseStep 1894759 = 2842139) B2842139
theorem B2131609 : Blo 1893435 2131609 := bbase (se 2 (by rfl) ⟨799353, by rfl⟩ : syracuseStep 2131609 = 1598707) (by norm_num)
theorem B2842145 : Blo 1893435 2842145 := bstep (se 2 (by rfl) ⟨1065804, by rfl⟩ : syracuseStep 2842145 = 2131609) B2131609
theorem B1894763 : Blo 1893435 1894763 := bstep (se 1 (by rfl) ⟨1421072, by rfl⟩ : syracuseStep 1894763 = 2842145) B2842145
theorem B7194197 : Blo 1893435 7194197 := bbase (se 8 (by rfl) ⟨42153, by rfl⟩ : syracuseStep 7194197 = 84307) (by norm_num)
theorem B4796131 : Blo 1893435 4796131 := bstep (se 1 (by rfl) ⟨3597098, by rfl⟩ : syracuseStep 4796131 = 7194197) B7194197
theorem B6394841 : Blo 1893435 6394841 := bstep (se 2 (by rfl) ⟨2398065, by rfl⟩ : syracuseStep 6394841 = 4796131) B4796131
theorem B4263227 : Blo 1893435 4263227 := bstep (se 1 (by rfl) ⟨3197420, by rfl⟩ : syracuseStep 4263227 = 6394841) B6394841
theorem B2842151 : Blo 1893435 2842151 := bstep (se 1 (by rfl) ⟨2131613, by rfl⟩ : syracuseStep 2842151 = 4263227) B4263227
theorem B1894767 : Blo 1893435 1894767 := bstep (se 1 (by rfl) ⟨1421075, by rfl⟩ : syracuseStep 1894767 = 2842151) B2842151
theorem B2842157 : Blo 1893435 2842157 := bbase (se 3 (by rfl) ⟨532904, by rfl⟩ : syracuseStep 2842157 = 1065809) (by norm_num)
theorem B1894771 : Blo 1893435 1894771 := bstep (se 1 (by rfl) ⟨1421078, by rfl⟩ : syracuseStep 1894771 = 2842157) B2842157
theorem B4263245 : Blo 1893435 4263245 := bbase (se 3 (by rfl) ⟨799358, by rfl⟩ : syracuseStep 4263245 = 1598717) (by norm_num)
theorem B2842163 : Blo 1893435 2842163 := bstep (se 1 (by rfl) ⟨2131622, by rfl⟩ : syracuseStep 2842163 = 4263245) B4263245
theorem B1894775 : Blo 1893435 1894775 := bstep (se 1 (by rfl) ⟨1421081, by rfl⟩ : syracuseStep 1894775 = 2842163) B2842163
theorem B2398081 : Blo 1893435 2398081 := bbase (se 2 (by rfl) ⟨899280, by rfl⟩ : syracuseStep 2398081 = 1798561) (by norm_num)
theorem B3197441 : Blo 1893435 3197441 := bstep (se 2 (by rfl) ⟨1199040, by rfl⟩ : syracuseStep 3197441 = 2398081) B2398081
theorem B2131627 : Blo 1893435 2131627 := bstep (se 1 (by rfl) ⟨1598720, by rfl⟩ : syracuseStep 2131627 = 3197441) B3197441
theorem B2842169 : Blo 1893435 2842169 := bstep (se 2 (by rfl) ⟨1065813, by rfl⟩ : syracuseStep 2842169 = 2131627) B2131627
theorem B1894779 : Blo 1893435 1894779 := bstep (se 1 (by rfl) ⟨1421084, by rfl⟩ : syracuseStep 1894779 = 2842169) B2842169
theorem B2023385 : Blo 1893435 2023385 := bbase (se 2 (by rfl) ⟨758769, by rfl⟩ : syracuseStep 2023385 = 1517539) (by norm_num)
theorem B21582773 : Blo 1893435 21582773 := bstep (se 5 (by rfl) ⟨1011692, by rfl⟩ : syracuseStep 21582773 = 2023385) B2023385
theorem B14388515 : Blo 1893435 14388515 := bstep (se 1 (by rfl) ⟨10791386, by rfl⟩ : syracuseStep 14388515 = 21582773) B21582773
theorem B9592343 : Blo 1893435 9592343 := bstep (se 1 (by rfl) ⟨7194257, by rfl⟩ : syracuseStep 9592343 = 14388515) B14388515
theorem B6394895 : Blo 1893435 6394895 := bstep (se 1 (by rfl) ⟨4796171, by rfl⟩ : syracuseStep 6394895 = 9592343) B9592343
theorem B4263263 : Blo 1893435 4263263 := bstep (se 1 (by rfl) ⟨3197447, by rfl⟩ : syracuseStep 4263263 = 6394895) B6394895
theorem B2842175 : Blo 1893435 2842175 := bstep (se 1 (by rfl) ⟨2131631, by rfl⟩ : syracuseStep 2842175 = 4263263) B4263263
theorem B1894783 : Blo 1893435 1894783 := bstep (se 1 (by rfl) ⟨1421087, by rfl⟩ : syracuseStep 1894783 = 2842175) B2842175
theorem B2842181 : Blo 1893435 2842181 := bbase (se 4 (by rfl) ⟨266454, by rfl⟩ : syracuseStep 2842181 = 532909) (by norm_num)
theorem B1894787 : Blo 1893435 1894787 := bstep (se 1 (by rfl) ⟨1421090, by rfl⟩ : syracuseStep 1894787 = 2842181) B2842181
theorem B3197461 : Blo 1893435 3197461 := bbase (se 6 (by rfl) ⟨74940, by rfl⟩ : syracuseStep 3197461 = 149881) (by norm_num)
theorem B4263281 : Blo 1893435 4263281 := bstep (se 2 (by rfl) ⟨1598730, by rfl⟩ : syracuseStep 4263281 = 3197461) B3197461
theorem B2842187 : Blo 1893435 2842187 := bstep (se 1 (by rfl) ⟨2131640, by rfl⟩ : syracuseStep 2842187 = 4263281) B4263281
theorem B1894791 : Blo 1893435 1894791 := bstep (se 1 (by rfl) ⟨1421093, by rfl⟩ : syracuseStep 1894791 = 2842187) B2842187
theorem B2131645 : Blo 1893435 2131645 := bbase (se 3 (by rfl) ⟨399683, by rfl⟩ : syracuseStep 2131645 = 799367) (by norm_num)
theorem B2842193 : Blo 1893435 2842193 := bstep (se 2 (by rfl) ⟨1065822, by rfl⟩ : syracuseStep 2842193 = 2131645) B2131645
theorem B1894795 : Blo 1893435 1894795 := bstep (se 1 (by rfl) ⟨1421096, by rfl⟩ : syracuseStep 1894795 = 2842193) B2842193
theorem B6394949 : Blo 1893435 6394949 := bbase (se 4 (by rfl) ⟨599526, by rfl⟩ : syracuseStep 6394949 = 1199053) (by norm_num)
theorem B4263299 : Blo 1893435 4263299 := bstep (se 1 (by rfl) ⟨3197474, by rfl⟩ : syracuseStep 4263299 = 6394949) B6394949
theorem B2842199 : Blo 1893435 2842199 := bstep (se 1 (by rfl) ⟨2131649, by rfl⟩ : syracuseStep 2842199 = 4263299) B4263299
theorem B1894799 : Blo 1893435 1894799 := bstep (se 1 (by rfl) ⟨1421099, by rfl⟩ : syracuseStep 1894799 = 2842199) B2842199
theorem B2842205 : Blo 1893435 2842205 := bbase (se 3 (by rfl) ⟨532913, by rfl⟩ : syracuseStep 2842205 = 1065827) (by norm_num)
theorem B1894803 : Blo 1893435 1894803 := bstep (se 1 (by rfl) ⟨1421102, by rfl⟩ : syracuseStep 1894803 = 2842205) B2842205
theorem B4263317 : Blo 1893435 4263317 := bbase (se 6 (by rfl) ⟨99921, by rfl⟩ : syracuseStep 4263317 = 199843) (by norm_num)
theorem B2842211 : Blo 1893435 2842211 := bstep (se 1 (by rfl) ⟨2131658, by rfl⟩ : syracuseStep 2842211 = 4263317) B4263317
theorem B1894807 : Blo 1893435 1894807 := bstep (se 1 (by rfl) ⟨1421105, by rfl⟩ : syracuseStep 1894807 = 2842211) B2842211
theorem B9723365 : Blo 1893435 9723365 := bbase (se 4 (by rfl) ⟨911565, by rfl⟩ : syracuseStep 9723365 = 1823131) (by norm_num)
theorem B6482243 : Blo 1893435 6482243 := bstep (se 1 (by rfl) ⟨4861682, by rfl⟩ : syracuseStep 6482243 = 9723365) B9723365
theorem B4321495 : Blo 1893435 4321495 := bstep (se 1 (by rfl) ⟨3241121, by rfl⟩ : syracuseStep 4321495 = 6482243) B6482243
theorem B23047973 : Blo 1893435 23047973 := bstep (se 4 (by rfl) ⟨2160747, by rfl⟩ : syracuseStep 23047973 = 4321495) B4321495
theorem B15365315 : Blo 1893435 15365315 := bstep (se 1 (by rfl) ⟨11523986, by rfl⟩ : syracuseStep 15365315 = 23047973) B23047973
theorem B10243543 : Blo 1893435 10243543 := bstep (se 1 (by rfl) ⟨7682657, by rfl⟩ : syracuseStep 10243543 = 15365315) B15365315
theorem B13658057 : Blo 1893435 13658057 := bstep (se 2 (by rfl) ⟨5121771, by rfl⟩ : syracuseStep 13658057 = 10243543) B10243543
theorem B9105371 : Blo 1893435 9105371 := bstep (se 1 (by rfl) ⟨6829028, by rfl⟩ : syracuseStep 9105371 = 13658057) B13658057
theorem B6070247 : Blo 1893435 6070247 := bstep (se 1 (by rfl) ⟨4552685, by rfl⟩ : syracuseStep 6070247 = 9105371) B9105371
theorem B4046831 : Blo 1893435 4046831 := bstep (se 1 (by rfl) ⟨3035123, by rfl⟩ : syracuseStep 4046831 = 6070247) B6070247
theorem B2697887 : Blo 1893435 2697887 := bstep (se 1 (by rfl) ⟨2023415, by rfl⟩ : syracuseStep 2697887 = 4046831) B4046831
theorem B7194365 : Blo 1893435 7194365 := bstep (se 3 (by rfl) ⟨1348943, by rfl⟩ : syracuseStep 7194365 = 2697887) B2697887
theorem B4796243 : Blo 1893435 4796243 := bstep (se 1 (by rfl) ⟨3597182, by rfl⟩ : syracuseStep 4796243 = 7194365) B7194365
theorem B3197495 : Blo 1893435 3197495 := bstep (se 1 (by rfl) ⟨2398121, by rfl⟩ : syracuseStep 3197495 = 4796243) B4796243
theorem B2131663 : Blo 1893435 2131663 := bstep (se 1 (by rfl) ⟨1598747, by rfl⟩ : syracuseStep 2131663 = 3197495) B3197495
theorem B2842217 : Blo 1893435 2842217 := bstep (se 2 (by rfl) ⟨1065831, by rfl⟩ : syracuseStep 2842217 = 2131663) B2131663
theorem B1894811 : Blo 1893435 1894811 := bstep (se 1 (by rfl) ⟨1421108, by rfl⟩ : syracuseStep 1894811 = 2842217) B2842217
theorem B2667149 : Blo 1893435 2667149 := bbase (se 3 (by rfl) ⟨500090, by rfl⟩ : syracuseStep 2667149 = 1000181) (by norm_num)
theorem B28449589 : Blo 1893435 28449589 := bstep (se 5 (by rfl) ⟨1333574, by rfl⟩ : syracuseStep 28449589 = 2667149) B2667149
theorem B37932785 : Blo 1893435 37932785 := bstep (se 2 (by rfl) ⟨14224794, by rfl⟩ : syracuseStep 37932785 = 28449589) B28449589
theorem B25288523 : Blo 1893435 25288523 := bstep (se 1 (by rfl) ⟨18966392, by rfl⟩ : syracuseStep 25288523 = 37932785) B37932785
theorem B16859015 : Blo 1893435 16859015 := bstep (se 1 (by rfl) ⟨12644261, by rfl⟩ : syracuseStep 16859015 = 25288523) B25288523
theorem B11239343 : Blo 1893435 11239343 := bstep (se 1 (by rfl) ⟨8429507, by rfl⟩ : syracuseStep 11239343 = 16859015) B16859015
theorem B7492895 : Blo 1893435 7492895 := bstep (se 1 (by rfl) ⟨5619671, by rfl⟩ : syracuseStep 7492895 = 11239343) B11239343
theorem B4995263 : Blo 1893435 4995263 := bstep (se 1 (by rfl) ⟨3746447, by rfl⟩ : syracuseStep 4995263 = 7492895) B7492895
theorem B3330175 : Blo 1893435 3330175 := bstep (se 1 (by rfl) ⟨2497631, by rfl⟩ : syracuseStep 3330175 = 4995263) B4995263
theorem B4440233 : Blo 1893435 4440233 := bstep (se 2 (by rfl) ⟨1665087, by rfl⟩ : syracuseStep 4440233 = 3330175) B3330175
theorem B2960155 : Blo 1893435 2960155 := bstep (se 1 (by rfl) ⟨2220116, by rfl⟩ : syracuseStep 2960155 = 4440233) B4440233
theorem B15787493 : Blo 1893435 15787493 := bstep (se 4 (by rfl) ⟨1480077, by rfl⟩ : syracuseStep 15787493 = 2960155) B2960155
theorem B10524995 : Blo 1893435 10524995 := bstep (se 1 (by rfl) ⟨7893746, by rfl⟩ : syracuseStep 10524995 = 15787493) B15787493
theorem B7016663 : Blo 1893435 7016663 := bstep (se 1 (by rfl) ⟨5262497, by rfl⟩ : syracuseStep 7016663 = 10524995) B10524995
theorem B18711101 : Blo 1893435 18711101 := bstep (se 3 (by rfl) ⟨3508331, by rfl⟩ : syracuseStep 18711101 = 7016663) B7016663
theorem B49896269 : Blo 1893435 49896269 := bstep (se 3 (by rfl) ⟨9355550, by rfl⟩ : syracuseStep 49896269 = 18711101) B18711101
theorem B33264179 : Blo 1893435 33264179 := bstep (se 1 (by rfl) ⟨24948134, by rfl⟩ : syracuseStep 33264179 = 49896269) B49896269
theorem B22176119 : Blo 1893435 22176119 := bstep (se 1 (by rfl) ⟨16632089, by rfl⟩ : syracuseStep 22176119 = 33264179) B33264179
theorem B14784079 : Blo 1893435 14784079 := bstep (se 1 (by rfl) ⟨11088059, by rfl⟩ : syracuseStep 14784079 = 22176119) B22176119
theorem B19712105 : Blo 1893435 19712105 := bstep (se 2 (by rfl) ⟨7392039, by rfl⟩ : syracuseStep 19712105 = 14784079) B14784079
theorem B13141403 : Blo 1893435 13141403 := bstep (se 1 (by rfl) ⟨9856052, by rfl⟩ : syracuseStep 13141403 = 19712105) B19712105
theorem B8760935 : Blo 1893435 8760935 := bstep (se 1 (by rfl) ⟨6570701, by rfl⟩ : syracuseStep 8760935 = 13141403) B13141403
theorem B5840623 : Blo 1893435 5840623 := bstep (se 1 (by rfl) ⟨4380467, by rfl⟩ : syracuseStep 5840623 = 8760935) B8760935
theorem B7787497 : Blo 1893435 7787497 := bstep (se 2 (by rfl) ⟨2920311, by rfl⟩ : syracuseStep 7787497 = 5840623) B5840623
theorem B10383329 : Blo 1893435 10383329 := bstep (se 2 (by rfl) ⟨3893748, by rfl⟩ : syracuseStep 10383329 = 7787497) B7787497
theorem B27688877 : Blo 1893435 27688877 := bstep (se 3 (by rfl) ⟨5191664, by rfl⟩ : syracuseStep 27688877 = 10383329) B10383329
theorem B18459251 : Blo 1893435 18459251 := bstep (se 1 (by rfl) ⟨13844438, by rfl⟩ : syracuseStep 18459251 = 27688877) B27688877
theorem B12306167 : Blo 1893435 12306167 := bstep (se 1 (by rfl) ⟨9229625, by rfl⟩ : syracuseStep 12306167 = 18459251) B18459251
theorem B8204111 : Blo 1893435 8204111 := bstep (se 1 (by rfl) ⟨6153083, by rfl⟩ : syracuseStep 8204111 = 12306167) B12306167
theorem B5469407 : Blo 1893435 5469407 := bstep (se 1 (by rfl) ⟨4102055, by rfl⟩ : syracuseStep 5469407 = 8204111) B8204111
theorem B3646271 : Blo 1893435 3646271 := bstep (se 1 (by rfl) ⟨2734703, by rfl⟩ : syracuseStep 3646271 = 5469407) B5469407
theorem B2430847 : Blo 1893435 2430847 := bstep (se 1 (by rfl) ⟨1823135, by rfl⟩ : syracuseStep 2430847 = 3646271) B3646271
theorem B3241129 : Blo 1893435 3241129 := bstep (se 2 (by rfl) ⟨1215423, by rfl⟩ : syracuseStep 3241129 = 2430847) B2430847
theorem B4321505 : Blo 1893435 4321505 := bstep (se 2 (by rfl) ⟨1620564, by rfl⟩ : syracuseStep 4321505 = 3241129) B3241129
theorem B2881003 : Blo 1893435 2881003 := bstep (se 1 (by rfl) ⟨2160752, by rfl⟩ : syracuseStep 2881003 = 4321505) B4321505
theorem B3841337 : Blo 1893435 3841337 := bstep (se 2 (by rfl) ⟨1440501, by rfl⟩ : syracuseStep 3841337 = 2881003) B2881003
theorem B2560891 : Blo 1893435 2560891 := bstep (se 1 (by rfl) ⟨1920668, by rfl⟩ : syracuseStep 2560891 = 3841337) B3841337
theorem B3414521 : Blo 1893435 3414521 := bstep (se 2 (by rfl) ⟨1280445, by rfl⟩ : syracuseStep 3414521 = 2560891) B2560891
theorem B2276347 : Blo 1893435 2276347 := bstep (se 1 (by rfl) ⟨1707260, by rfl⟩ : syracuseStep 2276347 = 3414521) B3414521
theorem B3035129 : Blo 1893435 3035129 := bstep (se 2 (by rfl) ⟨1138173, by rfl⟩ : syracuseStep 3035129 = 2276347) B2276347
theorem B8093677 : Blo 1893435 8093677 := bstep (se 3 (by rfl) ⟨1517564, by rfl⟩ : syracuseStep 8093677 = 3035129) B3035129
theorem B10791569 : Blo 1893435 10791569 := bstep (se 2 (by rfl) ⟨4046838, by rfl⟩ : syracuseStep 10791569 = 8093677) B8093677
theorem B7194379 : Blo 1893435 7194379 := bstep (se 1 (by rfl) ⟨5395784, by rfl⟩ : syracuseStep 7194379 = 10791569) B10791569
theorem B9592505 : Blo 1893435 9592505 := bstep (se 2 (by rfl) ⟨3597189, by rfl⟩ : syracuseStep 9592505 = 7194379) B7194379
theorem B6395003 : Blo 1893435 6395003 := bstep (se 1 (by rfl) ⟨4796252, by rfl⟩ : syracuseStep 6395003 = 9592505) B9592505
theorem B4263335 : Blo 1893435 4263335 := bstep (se 1 (by rfl) ⟨3197501, by rfl⟩ : syracuseStep 4263335 = 6395003) B6395003
theorem B2842223 : Blo 1893435 2842223 := bstep (se 1 (by rfl) ⟨2131667, by rfl⟩ : syracuseStep 2842223 = 4263335) B4263335
theorem B1894815 : Blo 1893435 1894815 := bstep (se 1 (by rfl) ⟨1421111, by rfl⟩ : syracuseStep 1894815 = 2842223) B2842223
theorem B2842229 : Blo 1893435 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B1894819 : Blo 1893435 1894819 := bstep (se 1 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 1894819 = 2842229) B2842229
theorem B3597205 : Blo 1893435 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B4796273 : Blo 1893435 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B3197515 : Blo 1893435 3197515 := bstep (se 1 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 3197515 = 4796273) B4796273
theorem B4263353 : Blo 1893435 4263353 := bstep (se 2 (by rfl) ⟨1598757, by rfl⟩ : syracuseStep 4263353 = 3197515) B3197515
theorem B2842235 : Blo 1893435 2842235 := bstep (se 1 (by rfl) ⟨2131676, by rfl⟩ : syracuseStep 2842235 = 4263353) B4263353
theorem B1894823 : Blo 1893435 1894823 := bstep (se 1 (by rfl) ⟨1421117, by rfl⟩ : syracuseStep 1894823 = 2842235) B2842235
theorem B2131681 : Blo 1893435 2131681 := bbase (se 2 (by rfl) ⟨799380, by rfl⟩ : syracuseStep 2131681 = 1598761) (by norm_num)
theorem B2842241 : Blo 1893435 2842241 := bstep (se 2 (by rfl) ⟨1065840, by rfl⟩ : syracuseStep 2842241 = 2131681) B2131681
theorem B1894827 : Blo 1893435 1894827 := bstep (se 1 (by rfl) ⟨1421120, by rfl⟩ : syracuseStep 1894827 = 2842241) B2842241
theorem B4796293 : Blo 1893435 4796293 := bbase (se 4 (by rfl) ⟨449652, by rfl⟩ : syracuseStep 4796293 = 899305) (by norm_num)
theorem B6395057 : Blo 1893435 6395057 := bstep (se 2 (by rfl) ⟨2398146, by rfl⟩ : syracuseStep 6395057 = 4796293) B4796293
theorem B4263371 : Blo 1893435 4263371 := bstep (se 1 (by rfl) ⟨3197528, by rfl⟩ : syracuseStep 4263371 = 6395057) B6395057
theorem B2842247 : Blo 1893435 2842247 := bstep (se 1 (by rfl) ⟨2131685, by rfl⟩ : syracuseStep 2842247 = 4263371) B4263371
theorem B1894831 : Blo 1893435 1894831 := bstep (se 1 (by rfl) ⟨1421123, by rfl⟩ : syracuseStep 1894831 = 2842247) B2842247
theorem B2842253 : Blo 1893435 2842253 := bbase (se 3 (by rfl) ⟨532922, by rfl⟩ : syracuseStep 2842253 = 1065845) (by norm_num)
theorem B1894835 : Blo 1893435 1894835 := bstep (se 1 (by rfl) ⟨1421126, by rfl⟩ : syracuseStep 1894835 = 2842253) B2842253
theorem B4263389 : Blo 1893435 4263389 := bbase (se 3 (by rfl) ⟨799385, by rfl⟩ : syracuseStep 4263389 = 1598771) (by norm_num)
theorem B2842259 : Blo 1893435 2842259 := bstep (se 1 (by rfl) ⟨2131694, by rfl⟩ : syracuseStep 2842259 = 4263389) B4263389
theorem B1894839 : Blo 1893435 1894839 := bstep (se 1 (by rfl) ⟨1421129, by rfl⟩ : syracuseStep 1894839 = 2842259) B2842259
theorem B3197549 : Blo 1893435 3197549 := bbase (se 3 (by rfl) ⟨599540, by rfl⟩ : syracuseStep 3197549 = 1199081) (by norm_num)
theorem B2131699 : Blo 1893435 2131699 := bstep (se 1 (by rfl) ⟨1598774, by rfl⟩ : syracuseStep 2131699 = 3197549) B3197549
theorem B2842265 : Blo 1893435 2842265 := bstep (se 2 (by rfl) ⟨1065849, by rfl⟩ : syracuseStep 2842265 = 2131699) B2131699
theorem B1894843 : Blo 1893435 1894843 := bstep (se 1 (by rfl) ⟨1421132, by rfl⟩ : syracuseStep 1894843 = 2842265) B2842265
theorem B37422805 : Blo 1893435 37422805 := bbase (se 7 (by rfl) ⟨438548, by rfl⟩ : syracuseStep 37422805 = 877097) (by norm_num)
theorem B49897073 : Blo 1893435 49897073 := bstep (se 2 (by rfl) ⟨18711402, by rfl⟩ : syracuseStep 49897073 = 37422805) B37422805
theorem B33264715 : Blo 1893435 33264715 := bstep (se 1 (by rfl) ⟨24948536, by rfl⟩ : syracuseStep 33264715 = 49897073) B49897073
theorem B44352953 : Blo 1893435 44352953 := bstep (se 2 (by rfl) ⟨16632357, by rfl⟩ : syracuseStep 44352953 = 33264715) B33264715
theorem B29568635 : Blo 1893435 29568635 := bstep (se 1 (by rfl) ⟨22176476, by rfl⟩ : syracuseStep 29568635 = 44352953) B44352953
theorem B19712423 : Blo 1893435 19712423 := bstep (se 1 (by rfl) ⟨14784317, by rfl⟩ : syracuseStep 19712423 = 29568635) B29568635
theorem B13141615 : Blo 1893435 13141615 := bstep (se 1 (by rfl) ⟨9856211, by rfl⟩ : syracuseStep 13141615 = 19712423) B19712423
theorem B17522153 : Blo 1893435 17522153 := bstep (se 2 (by rfl) ⟨6570807, by rfl⟩ : syracuseStep 17522153 = 13141615) B13141615
theorem B11681435 : Blo 1893435 11681435 := bstep (se 1 (by rfl) ⟨8761076, by rfl⟩ : syracuseStep 11681435 = 17522153) B17522153
theorem B7787623 : Blo 1893435 7787623 := bstep (se 1 (by rfl) ⟨5840717, by rfl⟩ : syracuseStep 7787623 = 11681435) B11681435
theorem B10383497 : Blo 1893435 10383497 := bstep (se 2 (by rfl) ⟨3893811, by rfl⟩ : syracuseStep 10383497 = 7787623) B7787623
theorem B6922331 : Blo 1893435 6922331 := bstep (se 1 (by rfl) ⟨5191748, by rfl⟩ : syracuseStep 6922331 = 10383497) B10383497
theorem B4614887 : Blo 1893435 4614887 := bstep (se 1 (by rfl) ⟨3461165, by rfl⟩ : syracuseStep 4614887 = 6922331) B6922331
theorem B3076591 : Blo 1893435 3076591 := bstep (se 1 (by rfl) ⟨2307443, by rfl⟩ : syracuseStep 3076591 = 4614887) B4614887
theorem B4102121 : Blo 1893435 4102121 := bstep (se 2 (by rfl) ⟨1538295, by rfl⟩ : syracuseStep 4102121 = 3076591) B3076591
theorem B10938989 : Blo 1893435 10938989 := bstep (se 3 (by rfl) ⟨2051060, by rfl⟩ : syracuseStep 10938989 = 4102121) B4102121
theorem B7292659 : Blo 1893435 7292659 := bstep (se 1 (by rfl) ⟨5469494, by rfl⟩ : syracuseStep 7292659 = 10938989) B10938989
theorem B9723545 : Blo 1893435 9723545 := bstep (se 2 (by rfl) ⟨3646329, by rfl⟩ : syracuseStep 9723545 = 7292659) B7292659
theorem B6482363 : Blo 1893435 6482363 := bstep (se 1 (by rfl) ⟨4861772, by rfl⟩ : syracuseStep 6482363 = 9723545) B9723545
theorem B17286301 : Blo 1893435 17286301 := bstep (se 3 (by rfl) ⟨3241181, by rfl⟩ : syracuseStep 17286301 = 6482363) B6482363
theorem B23048401 : Blo 1893435 23048401 := bstep (se 2 (by rfl) ⟨8643150, by rfl⟩ : syracuseStep 23048401 = 17286301) B17286301
theorem B30731201 : Blo 1893435 30731201 := bstep (se 2 (by rfl) ⟨11524200, by rfl⟩ : syracuseStep 30731201 = 23048401) B23048401
theorem B20487467 : Blo 1893435 20487467 := bstep (se 1 (by rfl) ⟨15365600, by rfl⟩ : syracuseStep 20487467 = 30731201) B30731201
theorem B13658311 : Blo 1893435 13658311 := bstep (se 1 (by rfl) ⟨10243733, by rfl⟩ : syracuseStep 13658311 = 20487467) B20487467
theorem B18211081 : Blo 1893435 18211081 := bstep (se 2 (by rfl) ⟨6829155, by rfl⟩ : syracuseStep 18211081 = 13658311) B13658311
theorem B24281441 : Blo 1893435 24281441 := bstep (se 2 (by rfl) ⟨9105540, by rfl⟩ : syracuseStep 24281441 = 18211081) B18211081
theorem B16187627 : Blo 1893435 16187627 := bstep (se 1 (by rfl) ⟨12140720, by rfl⟩ : syracuseStep 16187627 = 24281441) B24281441
theorem B10791751 : Blo 1893435 10791751 := bstep (se 1 (by rfl) ⟨8093813, by rfl⟩ : syracuseStep 10791751 = 16187627) B16187627
theorem B14389001 : Blo 1893435 14389001 := bstep (se 2 (by rfl) ⟨5395875, by rfl⟩ : syracuseStep 14389001 = 10791751) B10791751
theorem B9592667 : Blo 1893435 9592667 := bstep (se 1 (by rfl) ⟨7194500, by rfl⟩ : syracuseStep 9592667 = 14389001) B14389001
theorem B6395111 : Blo 1893435 6395111 := bstep (se 1 (by rfl) ⟨4796333, by rfl⟩ : syracuseStep 6395111 = 9592667) B9592667
theorem B4263407 : Blo 1893435 4263407 := bstep (se 1 (by rfl) ⟨3197555, by rfl⟩ : syracuseStep 4263407 = 6395111) B6395111
theorem B2842271 : Blo 1893435 2842271 := bstep (se 1 (by rfl) ⟨2131703, by rfl⟩ : syracuseStep 2842271 = 4263407) B4263407
theorem B1894847 : Blo 1893435 1894847 := bstep (se 1 (by rfl) ⟨1421135, by rfl⟩ : syracuseStep 1894847 = 2842271) B2842271
theorem B2842277 : Blo 1893435 2842277 := bbase (se 4 (by rfl) ⟨266463, by rfl⟩ : syracuseStep 2842277 = 532927) (by norm_num)
theorem B1894851 : Blo 1893435 1894851 := bstep (se 1 (by rfl) ⟨1421138, by rfl⟩ : syracuseStep 1894851 = 2842277) B2842277
theorem B2398177 : Blo 1893435 2398177 := bbase (se 2 (by rfl) ⟨899316, by rfl⟩ : syracuseStep 2398177 = 1798633) (by norm_num)
theorem B3197569 : Blo 1893435 3197569 := bstep (se 2 (by rfl) ⟨1199088, by rfl⟩ : syracuseStep 3197569 = 2398177) B2398177
theorem B4263425 : Blo 1893435 4263425 := bstep (se 2 (by rfl) ⟨1598784, by rfl⟩ : syracuseStep 4263425 = 3197569) B3197569
theorem B2842283 : Blo 1893435 2842283 := bstep (se 1 (by rfl) ⟨2131712, by rfl⟩ : syracuseStep 2842283 = 4263425) B4263425
theorem B1894855 : Blo 1893435 1894855 := bstep (se 1 (by rfl) ⟨1421141, by rfl⟩ : syracuseStep 1894855 = 2842283) B2842283
theorem B2131717 : Blo 1893435 2131717 := bbase (se 4 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 2131717 = 399697) (by norm_num)
theorem B2842289 : Blo 1893435 2842289 := bstep (se 2 (by rfl) ⟨1065858, by rfl⟩ : syracuseStep 2842289 = 2131717) B2131717
theorem B1894859 : Blo 1893435 1894859 := bstep (se 1 (by rfl) ⟨1421144, by rfl⟩ : syracuseStep 1894859 = 2842289) B2842289
theorem B13844789 : Blo 1893435 13844789 := bbase (se 5 (by rfl) ⟨648974, by rfl⟩ : syracuseStep 13844789 = 1297949) (by norm_num)
theorem B9229859 : Blo 1893435 9229859 := bstep (se 1 (by rfl) ⟨6922394, by rfl⟩ : syracuseStep 9229859 = 13844789) B13844789
theorem B6153239 : Blo 1893435 6153239 := bstep (se 1 (by rfl) ⟨4614929, by rfl⟩ : syracuseStep 6153239 = 9229859) B9229859
theorem B4102159 : Blo 1893435 4102159 := bstep (se 1 (by rfl) ⟨3076619, by rfl⟩ : syracuseStep 4102159 = 6153239) B6153239
theorem B5469545 : Blo 1893435 5469545 := bstep (se 2 (by rfl) ⟨2051079, by rfl⟩ : syracuseStep 5469545 = 4102159) B4102159
theorem B14585453 : Blo 1893435 14585453 := bstep (se 3 (by rfl) ⟨2734772, by rfl⟩ : syracuseStep 14585453 = 5469545) B5469545
theorem B9723635 : Blo 1893435 9723635 := bstep (se 1 (by rfl) ⟨7292726, by rfl⟩ : syracuseStep 9723635 = 14585453) B14585453
theorem B6482423 : Blo 1893435 6482423 := bstep (se 1 (by rfl) ⟨4861817, by rfl⟩ : syracuseStep 6482423 = 9723635) B9723635
theorem B4321615 : Blo 1893435 4321615 := bstep (se 1 (by rfl) ⟨3241211, by rfl⟩ : syracuseStep 4321615 = 6482423) B6482423
theorem B5762153 : Blo 1893435 5762153 := bstep (se 2 (by rfl) ⟨2160807, by rfl⟩ : syracuseStep 5762153 = 4321615) B4321615
theorem B3841435 : Blo 1893435 3841435 := bstep (se 1 (by rfl) ⟨2881076, by rfl⟩ : syracuseStep 3841435 = 5762153) B5762153
theorem B5121913 : Blo 1893435 5121913 := bstep (se 2 (by rfl) ⟨1920717, by rfl⟩ : syracuseStep 5121913 = 3841435) B3841435
theorem B6829217 : Blo 1893435 6829217 := bstep (se 2 (by rfl) ⟨2560956, by rfl⟩ : syracuseStep 6829217 = 5121913) B5121913
theorem B4552811 : Blo 1893435 4552811 := bstep (se 1 (by rfl) ⟨3414608, by rfl⟩ : syracuseStep 4552811 = 6829217) B6829217
theorem B3035207 : Blo 1893435 3035207 := bstep (se 1 (by rfl) ⟨2276405, by rfl⟩ : syracuseStep 3035207 = 4552811) B4552811
theorem B2023471 : Blo 1893435 2023471 := bstep (se 1 (by rfl) ⟨1517603, by rfl⟩ : syracuseStep 2023471 = 3035207) B3035207
theorem B2697961 : Blo 1893435 2697961 := bstep (se 2 (by rfl) ⟨1011735, by rfl⟩ : syracuseStep 2697961 = 2023471) B2023471
theorem B3597281 : Blo 1893435 3597281 := bstep (se 2 (by rfl) ⟨1348980, by rfl⟩ : syracuseStep 3597281 = 2697961) B2697961
theorem B2398187 : Blo 1893435 2398187 := bstep (se 1 (by rfl) ⟨1798640, by rfl⟩ : syracuseStep 2398187 = 3597281) B3597281
theorem B6395165 : Blo 1893435 6395165 := bstep (se 3 (by rfl) ⟨1199093, by rfl⟩ : syracuseStep 6395165 = 2398187) B2398187
theorem B4263443 : Blo 1893435 4263443 := bstep (se 1 (by rfl) ⟨3197582, by rfl⟩ : syracuseStep 4263443 = 6395165) B6395165
theorem B2842295 : Blo 1893435 2842295 := bstep (se 1 (by rfl) ⟨2131721, by rfl⟩ : syracuseStep 2842295 = 4263443) B4263443
theorem B1894863 : Blo 1893435 1894863 := bstep (se 1 (by rfl) ⟨1421147, by rfl⟩ : syracuseStep 1894863 = 2842295) B2842295
theorem B2842301 : Blo 1893435 2842301 := bbase (se 3 (by rfl) ⟨532931, by rfl⟩ : syracuseStep 2842301 = 1065863) (by norm_num)
theorem B1894867 : Blo 1893435 1894867 := bstep (se 1 (by rfl) ⟨1421150, by rfl⟩ : syracuseStep 1894867 = 2842301) B2842301
theorem B4263461 : Blo 1893435 4263461 := bbase (se 4 (by rfl) ⟨399699, by rfl⟩ : syracuseStep 4263461 = 799399) (by norm_num)
theorem B2842307 : Blo 1893435 2842307 := bstep (se 1 (by rfl) ⟨2131730, by rfl⟩ : syracuseStep 2842307 = 4263461) B4263461
theorem B1894871 : Blo 1893435 1894871 := bstep (se 1 (by rfl) ⟨1421153, by rfl⟩ : syracuseStep 1894871 = 2842307) B2842307
theorem B4796405 : Blo 1893435 4796405 := bbase (se 5 (by rfl) ⟨224831, by rfl⟩ : syracuseStep 4796405 = 449663) (by norm_num)
theorem B3197603 : Blo 1893435 3197603 := bstep (se 1 (by rfl) ⟨2398202, by rfl⟩ : syracuseStep 3197603 = 4796405) B4796405
theorem B2131735 : Blo 1893435 2131735 := bstep (se 1 (by rfl) ⟨1598801, by rfl⟩ : syracuseStep 2131735 = 3197603) B3197603
theorem B2842313 : Blo 1893435 2842313 := bstep (se 2 (by rfl) ⟨1065867, by rfl⟩ : syracuseStep 2842313 = 2131735) B2131735
theorem B1894875 : Blo 1893435 1894875 := bstep (se 1 (by rfl) ⟨1421156, by rfl⟩ : syracuseStep 1894875 = 2842313) B2842313
theorem B14784565 : Blo 1893435 14784565 := bbase (se 5 (by rfl) ⟨693026, by rfl⟩ : syracuseStep 14784565 = 1386053) (by norm_num)
theorem B19712753 : Blo 1893435 19712753 := bstep (se 2 (by rfl) ⟨7392282, by rfl⟩ : syracuseStep 19712753 = 14784565) B14784565
theorem B13141835 : Blo 1893435 13141835 := bstep (se 1 (by rfl) ⟨9856376, by rfl⟩ : syracuseStep 13141835 = 19712753) B19712753
theorem B8761223 : Blo 1893435 8761223 := bstep (se 1 (by rfl) ⟨6570917, by rfl⟩ : syracuseStep 8761223 = 13141835) B13141835
theorem B23363261 : Blo 1893435 23363261 := bstep (se 3 (by rfl) ⟨4380611, by rfl⟩ : syracuseStep 23363261 = 8761223) B8761223
theorem B15575507 : Blo 1893435 15575507 := bstep (se 1 (by rfl) ⟨11681630, by rfl⟩ : syracuseStep 15575507 = 23363261) B23363261
theorem B10383671 : Blo 1893435 10383671 := bstep (se 1 (by rfl) ⟨7787753, by rfl⟩ : syracuseStep 10383671 = 15575507) B15575507
theorem B27689789 : Blo 1893435 27689789 := bstep (se 3 (by rfl) ⟨5191835, by rfl⟩ : syracuseStep 27689789 = 10383671) B10383671
theorem B18459859 : Blo 1893435 18459859 := bstep (se 1 (by rfl) ⟨13844894, by rfl⟩ : syracuseStep 18459859 = 27689789) B27689789
theorem B24613145 : Blo 1893435 24613145 := bstep (se 2 (by rfl) ⟨9229929, by rfl⟩ : syracuseStep 24613145 = 18459859) B18459859
theorem B16408763 : Blo 1893435 16408763 := bstep (se 1 (by rfl) ⟨12306572, by rfl⟩ : syracuseStep 16408763 = 24613145) B24613145
theorem B10939175 : Blo 1893435 10939175 := bstep (se 1 (by rfl) ⟨8204381, by rfl⟩ : syracuseStep 10939175 = 16408763) B16408763
theorem B7292783 : Blo 1893435 7292783 := bstep (se 1 (by rfl) ⟨5469587, by rfl⟩ : syracuseStep 7292783 = 10939175) B10939175
theorem B4861855 : Blo 1893435 4861855 := bstep (se 1 (by rfl) ⟨3646391, by rfl⟩ : syracuseStep 4861855 = 7292783) B7292783
theorem B6482473 : Blo 1893435 6482473 := bstep (se 2 (by rfl) ⟨2430927, by rfl⟩ : syracuseStep 6482473 = 4861855) B4861855
theorem B138292757 : Blo 1893435 138292757 := bstep (se 6 (by rfl) ⟨3241236, by rfl⟩ : syracuseStep 138292757 = 6482473) B6482473
theorem B92195171 : Blo 1893435 92195171 := bstep (se 1 (by rfl) ⟨69146378, by rfl⟩ : syracuseStep 92195171 = 138292757) B138292757
theorem B61463447 : Blo 1893435 61463447 := bstep (se 1 (by rfl) ⟨46097585, by rfl⟩ : syracuseStep 61463447 = 92195171) B92195171
theorem B40975631 : Blo 1893435 40975631 := bstep (se 1 (by rfl) ⟨30731723, by rfl⟩ : syracuseStep 40975631 = 61463447) B61463447
theorem B27317087 : Blo 1893435 27317087 := bstep (se 1 (by rfl) ⟨20487815, by rfl⟩ : syracuseStep 27317087 = 40975631) B40975631
theorem B18211391 : Blo 1893435 18211391 := bstep (se 1 (by rfl) ⟨13658543, by rfl⟩ : syracuseStep 18211391 = 27317087) B27317087
theorem B12140927 : Blo 1893435 12140927 := bstep (se 1 (by rfl) ⟨9105695, by rfl⟩ : syracuseStep 12140927 = 18211391) B18211391
theorem B8093951 : Blo 1893435 8093951 := bstep (se 1 (by rfl) ⟨6070463, by rfl⟩ : syracuseStep 8093951 = 12140927) B12140927
theorem B5395967 : Blo 1893435 5395967 := bstep (se 1 (by rfl) ⟨4046975, by rfl⟩ : syracuseStep 5395967 = 8093951) B8093951
theorem B3597311 : Blo 1893435 3597311 := bstep (se 1 (by rfl) ⟨2697983, by rfl⟩ : syracuseStep 3597311 = 5395967) B5395967
theorem B9592829 : Blo 1893435 9592829 := bstep (se 3 (by rfl) ⟨1798655, by rfl⟩ : syracuseStep 9592829 = 3597311) B3597311
theorem B6395219 : Blo 1893435 6395219 := bstep (se 1 (by rfl) ⟨4796414, by rfl⟩ : syracuseStep 6395219 = 9592829) B9592829
theorem B4263479 : Blo 1893435 4263479 := bstep (se 1 (by rfl) ⟨3197609, by rfl⟩ : syracuseStep 4263479 = 6395219) B6395219
theorem B2842319 : Blo 1893435 2842319 := bstep (se 1 (by rfl) ⟨2131739, by rfl⟩ : syracuseStep 2842319 = 4263479) B4263479
theorem B1894879 : Blo 1893435 1894879 := bstep (se 1 (by rfl) ⟨1421159, by rfl⟩ : syracuseStep 1894879 = 2842319) B2842319
theorem B2842325 : Blo 1893435 2842325 := bbase (se 7 (by rfl) ⟨33308, by rfl⟩ : syracuseStep 2842325 = 66617) (by norm_num)
theorem B1894883 : Blo 1893435 1894883 := bstep (se 1 (by rfl) ⟨1421162, by rfl⟩ : syracuseStep 1894883 = 2842325) B2842325
theorem B3035245 : Blo 1893435 3035245 := bbase (se 3 (by rfl) ⟨569108, by rfl⟩ : syracuseStep 3035245 = 1138217) (by norm_num)
theorem B4046993 : Blo 1893435 4046993 := bstep (se 2 (by rfl) ⟨1517622, by rfl⟩ : syracuseStep 4046993 = 3035245) B3035245
theorem B2697995 : Blo 1893435 2697995 := bstep (se 1 (by rfl) ⟨2023496, by rfl⟩ : syracuseStep 2697995 = 4046993) B4046993
theorem B7194653 : Blo 1893435 7194653 := bstep (se 3 (by rfl) ⟨1348997, by rfl⟩ : syracuseStep 7194653 = 2697995) B2697995
theorem B4796435 : Blo 1893435 4796435 := bstep (se 1 (by rfl) ⟨3597326, by rfl⟩ : syracuseStep 4796435 = 7194653) B7194653
theorem B3197623 : Blo 1893435 3197623 := bstep (se 1 (by rfl) ⟨2398217, by rfl⟩ : syracuseStep 3197623 = 4796435) B4796435
theorem B4263497 : Blo 1893435 4263497 := bstep (se 2 (by rfl) ⟨1598811, by rfl⟩ : syracuseStep 4263497 = 3197623) B3197623
theorem B2842331 : Blo 1893435 2842331 := bstep (se 1 (by rfl) ⟨2131748, by rfl⟩ : syracuseStep 2842331 = 4263497) B4263497
theorem B1894887 : Blo 1893435 1894887 := bstep (se 1 (by rfl) ⟨1421165, by rfl⟩ : syracuseStep 1894887 = 2842331) B2842331
theorem B2131753 : Blo 1893435 2131753 := bbase (se 2 (by rfl) ⟨799407, by rfl⟩ : syracuseStep 2131753 = 1598815) (by norm_num)
theorem B2842337 : Blo 1893435 2842337 := bstep (se 2 (by rfl) ⟨1065876, by rfl⟩ : syracuseStep 2842337 = 2131753) B2131753
theorem B1894891 : Blo 1893435 1894891 := bstep (se 1 (by rfl) ⟨1421168, by rfl⟩ : syracuseStep 1894891 = 2842337) B2842337
theorem B9723797 : Blo 1893435 9723797 := bbase (se 6 (by rfl) ⟨227901, by rfl⟩ : syracuseStep 9723797 = 455803) (by norm_num)
theorem B6482531 : Blo 1893435 6482531 := bstep (se 1 (by rfl) ⟨4861898, by rfl⟩ : syracuseStep 6482531 = 9723797) B9723797
theorem B4321687 : Blo 1893435 4321687 := bstep (se 1 (by rfl) ⟨3241265, by rfl⟩ : syracuseStep 4321687 = 6482531) B6482531
theorem B5762249 : Blo 1893435 5762249 := bstep (se 2 (by rfl) ⟨2160843, by rfl⟩ : syracuseStep 5762249 = 4321687) B4321687
theorem B3841499 : Blo 1893435 3841499 := bstep (se 1 (by rfl) ⟨2881124, by rfl⟩ : syracuseStep 3841499 = 5762249) B5762249
theorem B2560999 : Blo 1893435 2560999 := bstep (se 1 (by rfl) ⟨1920749, by rfl⟩ : syracuseStep 2560999 = 3841499) B3841499
theorem B3414665 : Blo 1893435 3414665 := bstep (se 2 (by rfl) ⟨1280499, by rfl⟩ : syracuseStep 3414665 = 2560999) B2560999
theorem B2276443 : Blo 1893435 2276443 := bstep (se 1 (by rfl) ⟨1707332, by rfl⟩ : syracuseStep 2276443 = 3414665) B3414665
theorem B12141029 : Blo 1893435 12141029 := bstep (se 4 (by rfl) ⟨1138221, by rfl⟩ : syracuseStep 12141029 = 2276443) B2276443
theorem B8094019 : Blo 1893435 8094019 := bstep (se 1 (by rfl) ⟨6070514, by rfl⟩ : syracuseStep 8094019 = 12141029) B12141029
theorem B10792025 : Blo 1893435 10792025 := bstep (se 2 (by rfl) ⟨4047009, by rfl⟩ : syracuseStep 10792025 = 8094019) B8094019
theorem B7194683 : Blo 1893435 7194683 := bstep (se 1 (by rfl) ⟨5396012, by rfl⟩ : syracuseStep 7194683 = 10792025) B10792025
theorem B4796455 : Blo 1893435 4796455 := bstep (se 1 (by rfl) ⟨3597341, by rfl⟩ : syracuseStep 4796455 = 7194683) B7194683
theorem B6395273 : Blo 1893435 6395273 := bstep (se 2 (by rfl) ⟨2398227, by rfl⟩ : syracuseStep 6395273 = 4796455) B4796455
theorem B4263515 : Blo 1893435 4263515 := bstep (se 1 (by rfl) ⟨3197636, by rfl⟩ : syracuseStep 4263515 = 6395273) B6395273
theorem B2842343 : Blo 1893435 2842343 := bstep (se 1 (by rfl) ⟨2131757, by rfl⟩ : syracuseStep 2842343 = 4263515) B4263515
theorem B1894895 : Blo 1893435 1894895 := bstep (se 1 (by rfl) ⟨1421171, by rfl⟩ : syracuseStep 1894895 = 2842343) B2842343
theorem B2842349 : Blo 1893435 2842349 := bbase (se 3 (by rfl) ⟨532940, by rfl⟩ : syracuseStep 2842349 = 1065881) (by norm_num)
theorem B1894899 : Blo 1893435 1894899 := bstep (se 1 (by rfl) ⟨1421174, by rfl⟩ : syracuseStep 1894899 = 2842349) B2842349
theorem B4263533 : Blo 1893435 4263533 := bbase (se 3 (by rfl) ⟨799412, by rfl⟩ : syracuseStep 4263533 = 1598825) (by norm_num)
theorem B2842355 : Blo 1893435 2842355 := bstep (se 1 (by rfl) ⟨2131766, by rfl⟩ : syracuseStep 2842355 = 4263533) B4263533
theorem B1894903 : Blo 1893435 1894903 := bstep (se 1 (by rfl) ⟨1421177, by rfl⟩ : syracuseStep 1894903 = 2842355) B2842355
theorem B3597365 : Blo 1893435 3597365 := bbase (se 5 (by rfl) ⟨168626, by rfl⟩ : syracuseStep 3597365 = 337253) (by norm_num)
theorem B2398243 : Blo 1893435 2398243 := bstep (se 1 (by rfl) ⟨1798682, by rfl⟩ : syracuseStep 2398243 = 3597365) B3597365
theorem B3197657 : Blo 1893435 3197657 := bstep (se 2 (by rfl) ⟨1199121, by rfl⟩ : syracuseStep 3197657 = 2398243) B2398243
theorem B2131771 : Blo 1893435 2131771 := bstep (se 1 (by rfl) ⟨1598828, by rfl⟩ : syracuseStep 2131771 = 3197657) B3197657
theorem B2842361 : Blo 1893435 2842361 := bstep (se 2 (by rfl) ⟨1065885, by rfl⟩ : syracuseStep 2842361 = 2131771) B2131771
theorem B1894907 : Blo 1893435 1894907 := bstep (se 1 (by rfl) ⟨1421180, by rfl⟩ : syracuseStep 1894907 = 2842361) B2842361
theorem B25930325 : Blo 1893435 25930325 := bbase (se 8 (by rfl) ⟨151935, by rfl⟩ : syracuseStep 25930325 = 303871) (by norm_num)
theorem B69147533 : Blo 1893435 69147533 := bstep (se 3 (by rfl) ⟨12965162, by rfl⟩ : syracuseStep 69147533 = 25930325) B25930325
theorem B184393421 : Blo 1893435 184393421 := bstep (se 3 (by rfl) ⟨34573766, by rfl⟩ : syracuseStep 184393421 = 69147533) B69147533
theorem B122928947 : Blo 1893435 122928947 := bstep (se 1 (by rfl) ⟨92196710, by rfl⟩ : syracuseStep 122928947 = 184393421) B184393421
theorem B81952631 : Blo 1893435 81952631 := bstep (se 1 (by rfl) ⟨61464473, by rfl⟩ : syracuseStep 81952631 = 122928947) B122928947
theorem B54635087 : Blo 1893435 54635087 := bstep (se 1 (by rfl) ⟨40976315, by rfl⟩ : syracuseStep 54635087 = 81952631) B81952631
theorem B36423391 : Blo 1893435 36423391 := bstep (se 1 (by rfl) ⟨27317543, by rfl⟩ : syracuseStep 36423391 = 54635087) B54635087
theorem B48564521 : Blo 1893435 48564521 := bstep (se 2 (by rfl) ⟨18211695, by rfl⟩ : syracuseStep 48564521 = 36423391) B36423391
theorem B32376347 : Blo 1893435 32376347 := bstep (se 1 (by rfl) ⟨24282260, by rfl⟩ : syracuseStep 32376347 = 48564521) B48564521
theorem B21584231 : Blo 1893435 21584231 := bstep (se 1 (by rfl) ⟨16188173, by rfl⟩ : syracuseStep 21584231 = 32376347) B32376347
theorem B14389487 : Blo 1893435 14389487 := bstep (se 1 (by rfl) ⟨10792115, by rfl⟩ : syracuseStep 14389487 = 21584231) B21584231
theorem B9592991 : Blo 1893435 9592991 := bstep (se 1 (by rfl) ⟨7194743, by rfl⟩ : syracuseStep 9592991 = 14389487) B14389487
theorem B6395327 : Blo 1893435 6395327 := bstep (se 1 (by rfl) ⟨4796495, by rfl⟩ : syracuseStep 6395327 = 9592991) B9592991
theorem B4263551 : Blo 1893435 4263551 := bstep (se 1 (by rfl) ⟨3197663, by rfl⟩ : syracuseStep 4263551 = 6395327) B6395327
theorem B2842367 : Blo 1893435 2842367 := bstep (se 1 (by rfl) ⟨2131775, by rfl⟩ : syracuseStep 2842367 = 4263551) B4263551
theorem B1894911 : Blo 1893435 1894911 := bstep (se 1 (by rfl) ⟨1421183, by rfl⟩ : syracuseStep 1894911 = 2842367) B2842367
theorem B2842373 : Blo 1893435 2842373 := bbase (se 4 (by rfl) ⟨266472, by rfl⟩ : syracuseStep 2842373 = 532945) (by norm_num)
theorem B1894915 : Blo 1893435 1894915 := bstep (se 1 (by rfl) ⟨1421186, by rfl⟩ : syracuseStep 1894915 = 2842373) B2842373
theorem B3197677 : Blo 1893435 3197677 := bbase (se 3 (by rfl) ⟨599564, by rfl⟩ : syracuseStep 3197677 = 1199129) (by norm_num)
theorem B4263569 : Blo 1893435 4263569 := bstep (se 2 (by rfl) ⟨1598838, by rfl⟩ : syracuseStep 4263569 = 3197677) B3197677
theorem B2842379 : Blo 1893435 2842379 := bstep (se 1 (by rfl) ⟨2131784, by rfl⟩ : syracuseStep 2842379 = 4263569) B4263569
theorem B1894919 : Blo 1893435 1894919 := bstep (se 1 (by rfl) ⟨1421189, by rfl⟩ : syracuseStep 1894919 = 2842379) B2842379
theorem B2131789 : Blo 1893435 2131789 := bbase (se 3 (by rfl) ⟨399710, by rfl⟩ : syracuseStep 2131789 = 799421) (by norm_num)
theorem B2842385 : Blo 1893435 2842385 := bstep (se 2 (by rfl) ⟨1065894, by rfl⟩ : syracuseStep 2842385 = 2131789) B2131789
theorem B1894923 : Blo 1893435 1894923 := bstep (se 1 (by rfl) ⟨1421192, by rfl⟩ : syracuseStep 1894923 = 2842385) B2842385
theorem B6395381 : Blo 1893435 6395381 := bbase (se 5 (by rfl) ⟨299783, by rfl⟩ : syracuseStep 6395381 = 599567) (by norm_num)
theorem B4263587 : Blo 1893435 4263587 := bstep (se 1 (by rfl) ⟨3197690, by rfl⟩ : syracuseStep 4263587 = 6395381) B6395381
theorem B2842391 : Blo 1893435 2842391 := bstep (se 1 (by rfl) ⟨2131793, by rfl⟩ : syracuseStep 2842391 = 4263587) B4263587
theorem B1894927 : Blo 1893435 1894927 := bstep (se 1 (by rfl) ⟨1421195, by rfl⟩ : syracuseStep 1894927 = 2842391) B2842391
theorem B2842397 : Blo 1893435 2842397 := bbase (se 3 (by rfl) ⟨532949, by rfl⟩ : syracuseStep 2842397 = 1065899) (by norm_num)
theorem B1894931 : Blo 1893435 1894931 := bstep (se 1 (by rfl) ⟨1421198, by rfl⟩ : syracuseStep 1894931 = 2842397) B2842397
theorem B4263605 : Blo 1893435 4263605 := bbase (se 5 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 4263605 = 399713) (by norm_num)
theorem B2842403 : Blo 1893435 2842403 := bstep (se 1 (by rfl) ⟨2131802, by rfl⟩ : syracuseStep 2842403 = 4263605) B4263605
theorem B1894935 : Blo 1893435 1894935 := bstep (se 1 (by rfl) ⟨1421201, by rfl⟩ : syracuseStep 1894935 = 2842403) B2842403
theorem B10792277 : Blo 1893435 10792277 := bbase (se 11 (by rfl) ⟨7904, by rfl⟩ : syracuseStep 10792277 = 15809) (by norm_num)
theorem B7194851 : Blo 1893435 7194851 := bstep (se 1 (by rfl) ⟨5396138, by rfl⟩ : syracuseStep 7194851 = 10792277) B10792277
theorem B4796567 : Blo 1893435 4796567 := bstep (se 1 (by rfl) ⟨3597425, by rfl⟩ : syracuseStep 4796567 = 7194851) B7194851
theorem B3197711 : Blo 1893435 3197711 := bstep (se 1 (by rfl) ⟨2398283, by rfl⟩ : syracuseStep 3197711 = 4796567) B4796567
theorem B2131807 : Blo 1893435 2131807 := bstep (se 1 (by rfl) ⟨1598855, by rfl⟩ : syracuseStep 2131807 = 3197711) B3197711
theorem B2842409 : Blo 1893435 2842409 := bstep (se 2 (by rfl) ⟨1065903, by rfl⟩ : syracuseStep 2842409 = 2131807) B2131807
theorem B1894939 : Blo 1893435 1894939 := bstep (se 1 (by rfl) ⟨1421204, by rfl⟩ : syracuseStep 1894939 = 2842409) B2842409
theorem B5396149 : Blo 1893435 5396149 := bbase (se 5 (by rfl) ⟨252944, by rfl⟩ : syracuseStep 5396149 = 505889) (by norm_num)
theorem B7194865 : Blo 1893435 7194865 := bstep (se 2 (by rfl) ⟨2698074, by rfl⟩ : syracuseStep 7194865 = 5396149) B5396149
theorem B9593153 : Blo 1893435 9593153 := bstep (se 2 (by rfl) ⟨3597432, by rfl⟩ : syracuseStep 9593153 = 7194865) B7194865
theorem B6395435 : Blo 1893435 6395435 := bstep (se 1 (by rfl) ⟨4796576, by rfl⟩ : syracuseStep 6395435 = 9593153) B9593153
theorem B4263623 : Blo 1893435 4263623 := bstep (se 1 (by rfl) ⟨3197717, by rfl⟩ : syracuseStep 4263623 = 6395435) B6395435
theorem B2842415 : Blo 1893435 2842415 := bstep (se 1 (by rfl) ⟨2131811, by rfl⟩ : syracuseStep 2842415 = 4263623) B4263623
theorem B1894943 : Blo 1893435 1894943 := bstep (se 1 (by rfl) ⟨1421207, by rfl⟩ : syracuseStep 1894943 = 2842415) B2842415
theorem B2842421 : Blo 1893435 2842421 := bbase (se 5 (by rfl) ⟨133238, by rfl⟩ : syracuseStep 2842421 = 266477) (by norm_num)
theorem B1894947 : Blo 1893435 1894947 := bstep (se 1 (by rfl) ⟨1421210, by rfl⟩ : syracuseStep 1894947 = 2842421) B2842421
theorem B4796597 : Blo 1893435 4796597 := bbase (se 5 (by rfl) ⟨224840, by rfl⟩ : syracuseStep 4796597 = 449681) (by norm_num)
theorem B3197731 : Blo 1893435 3197731 := bstep (se 1 (by rfl) ⟨2398298, by rfl⟩ : syracuseStep 3197731 = 4796597) B4796597
theorem B4263641 : Blo 1893435 4263641 := bstep (se 2 (by rfl) ⟨1598865, by rfl⟩ : syracuseStep 4263641 = 3197731) B3197731
theorem B2842427 : Blo 1893435 2842427 := bstep (se 1 (by rfl) ⟨2131820, by rfl⟩ : syracuseStep 2842427 = 4263641) B4263641
theorem B1894951 : Blo 1893435 1894951 := bstep (se 1 (by rfl) ⟨1421213, by rfl⟩ : syracuseStep 1894951 = 2842427) B2842427
theorem B2131825 : Blo 1893435 2131825 := bbase (se 2 (by rfl) ⟨799434, by rfl⟩ : syracuseStep 2131825 = 1598869) (by norm_num)
theorem B2842433 : Blo 1893435 2842433 := bstep (se 2 (by rfl) ⟨1065912, by rfl⟩ : syracuseStep 2842433 = 2131825) B2131825
theorem B1894955 : Blo 1893435 1894955 := bstep (se 1 (by rfl) ⟨1421216, by rfl⟩ : syracuseStep 1894955 = 2842433) B2842433
theorem B8094293 : Blo 1893435 8094293 := bbase (se 8 (by rfl) ⟨47427, by rfl⟩ : syracuseStep 8094293 = 94855) (by norm_num)
theorem B5396195 : Blo 1893435 5396195 := bstep (se 1 (by rfl) ⟨4047146, by rfl⟩ : syracuseStep 5396195 = 8094293) B8094293
theorem B3597463 : Blo 1893435 3597463 := bstep (se 1 (by rfl) ⟨2698097, by rfl⟩ : syracuseStep 3597463 = 5396195) B5396195
theorem B4796617 : Blo 1893435 4796617 := bstep (se 2 (by rfl) ⟨1798731, by rfl⟩ : syracuseStep 4796617 = 3597463) B3597463
theorem B6395489 : Blo 1893435 6395489 := bstep (se 2 (by rfl) ⟨2398308, by rfl⟩ : syracuseStep 6395489 = 4796617) B4796617
theorem B4263659 : Blo 1893435 4263659 := bstep (se 1 (by rfl) ⟨3197744, by rfl⟩ : syracuseStep 4263659 = 6395489) B6395489
theorem B2842439 : Blo 1893435 2842439 := bstep (se 1 (by rfl) ⟨2131829, by rfl⟩ : syracuseStep 2842439 = 4263659) B4263659
theorem B1894959 : Blo 1893435 1894959 := bstep (se 1 (by rfl) ⟨1421219, by rfl⟩ : syracuseStep 1894959 = 2842439) B2842439
theorem B2842445 : Blo 1893435 2842445 := bbase (se 3 (by rfl) ⟨532958, by rfl⟩ : syracuseStep 2842445 = 1065917) (by norm_num)
theorem B1894963 : Blo 1893435 1894963 := bstep (se 1 (by rfl) ⟨1421222, by rfl⟩ : syracuseStep 1894963 = 2842445) B2842445
theorem B4263677 : Blo 1893435 4263677 := bbase (se 3 (by rfl) ⟨799439, by rfl⟩ : syracuseStep 4263677 = 1598879) (by norm_num)
theorem B2842451 : Blo 1893435 2842451 := bstep (se 1 (by rfl) ⟨2131838, by rfl⟩ : syracuseStep 2842451 = 4263677) B4263677
theorem B1894967 : Blo 1893435 1894967 := bstep (se 1 (by rfl) ⟨1421225, by rfl⟩ : syracuseStep 1894967 = 2842451) B2842451
theorem B3197765 : Blo 1893435 3197765 := bbase (se 4 (by rfl) ⟨299790, by rfl⟩ : syracuseStep 3197765 = 599581) (by norm_num)
theorem B2131843 : Blo 1893435 2131843 := bstep (se 1 (by rfl) ⟨1598882, by rfl⟩ : syracuseStep 2131843 = 3197765) B3197765
theorem B2842457 : Blo 1893435 2842457 := bstep (se 2 (by rfl) ⟨1065921, by rfl⟩ : syracuseStep 2842457 = 2131843) B2131843
theorem B1894971 : Blo 1893435 1894971 := bstep (se 1 (by rfl) ⟨1421228, by rfl⟩ : syracuseStep 1894971 = 2842457) B2842457
theorem B14389973 : Blo 1893435 14389973 := bbase (se 7 (by rfl) ⟨168632, by rfl⟩ : syracuseStep 14389973 = 337265) (by norm_num)
theorem B9593315 : Blo 1893435 9593315 := bstep (se 1 (by rfl) ⟨7194986, by rfl⟩ : syracuseStep 9593315 = 14389973) B14389973
theorem B6395543 : Blo 1893435 6395543 := bstep (se 1 (by rfl) ⟨4796657, by rfl⟩ : syracuseStep 6395543 = 9593315) B9593315
theorem B4263695 : Blo 1893435 4263695 := bstep (se 1 (by rfl) ⟨3197771, by rfl⟩ : syracuseStep 4263695 = 6395543) B6395543
theorem B2842463 : Blo 1893435 2842463 := bstep (se 1 (by rfl) ⟨2131847, by rfl⟩ : syracuseStep 2842463 = 4263695) B4263695
theorem B1894975 : Blo 1893435 1894975 := bstep (se 1 (by rfl) ⟨1421231, by rfl⟩ : syracuseStep 1894975 = 2842463) B2842463
theorem B2842469 : Blo 1893435 2842469 := bbase (se 4 (by rfl) ⟨266481, by rfl⟩ : syracuseStep 2842469 = 532963) (by norm_num)
theorem B1894979 : Blo 1893435 1894979 := bstep (se 1 (by rfl) ⟨1421234, by rfl⟩ : syracuseStep 1894979 = 2842469) B2842469
theorem B3597509 : Blo 1893435 3597509 := bbase (se 4 (by rfl) ⟨337266, by rfl⟩ : syracuseStep 3597509 = 674533) (by norm_num)
theorem B2398339 : Blo 1893435 2398339 := bstep (se 1 (by rfl) ⟨1798754, by rfl⟩ : syracuseStep 2398339 = 3597509) B3597509
theorem B3197785 : Blo 1893435 3197785 := bstep (se 2 (by rfl) ⟨1199169, by rfl⟩ : syracuseStep 3197785 = 2398339) B2398339
theorem B4263713 : Blo 1893435 4263713 := bstep (se 2 (by rfl) ⟨1598892, by rfl⟩ : syracuseStep 4263713 = 3197785) B3197785
theorem B2842475 : Blo 1893435 2842475 := bstep (se 1 (by rfl) ⟨2131856, by rfl⟩ : syracuseStep 2842475 = 4263713) B4263713
theorem B1894983 : Blo 1893435 1894983 := bstep (se 1 (by rfl) ⟨1421237, by rfl⟩ : syracuseStep 1894983 = 2842475) B2842475
theorem B2131861 : Blo 1893435 2131861 := bbase (se 6 (by rfl) ⟨49965, by rfl⟩ : syracuseStep 2131861 = 99931) (by norm_num)
theorem B2842481 : Blo 1893435 2842481 := bstep (se 2 (by rfl) ⟨1065930, by rfl⟩ : syracuseStep 2842481 = 2131861) B2131861
theorem B1894987 : Blo 1893435 1894987 := bstep (se 1 (by rfl) ⟨1421240, by rfl⟩ : syracuseStep 1894987 = 2842481) B2842481
theorem B2398349 : Blo 1893435 2398349 := bbase (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) (by norm_num)
theorem B6395597 : Blo 1893435 6395597 := bstep (se 3 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 6395597 = 2398349) B2398349
theorem B4263731 : Blo 1893435 4263731 := bstep (se 1 (by rfl) ⟨3197798, by rfl⟩ : syracuseStep 4263731 = 6395597) B6395597
theorem B2842487 : Blo 1893435 2842487 := bstep (se 1 (by rfl) ⟨2131865, by rfl⟩ : syracuseStep 2842487 = 4263731) B4263731
theorem B1894991 : Blo 1893435 1894991 := bstep (se 1 (by rfl) ⟨1421243, by rfl⟩ : syracuseStep 1894991 = 2842487) B2842487
theorem B2842493 : Blo 1893435 2842493 := bbase (se 3 (by rfl) ⟨532967, by rfl⟩ : syracuseStep 2842493 = 1065935) (by norm_num)
theorem B1894995 : Blo 1893435 1894995 := bstep (se 1 (by rfl) ⟨1421246, by rfl⟩ : syracuseStep 1894995 = 2842493) B2842493
theorem B4263749 : Blo 1893435 4263749 := bbase (se 4 (by rfl) ⟨399726, by rfl⟩ : syracuseStep 4263749 = 799453) (by norm_num)
theorem B2842499 : Blo 1893435 2842499 := bstep (se 1 (by rfl) ⟨2131874, by rfl⟩ : syracuseStep 2842499 = 4263749) B4263749
theorem B1894999 : Blo 1893435 1894999 := bstep (se 1 (by rfl) ⟨1421249, by rfl⟩ : syracuseStep 1894999 = 2842499) B2842499
theorem B6237653 : Blo 1893435 6237653 := bbase (se 7 (by rfl) ⟨73097, by rfl⟩ : syracuseStep 6237653 = 146195) (by norm_num)
theorem B66534965 : Blo 1893435 66534965 := bstep (se 5 (by rfl) ⟨3118826, by rfl⟩ : syracuseStep 66534965 = 6237653) B6237653
theorem B44356643 : Blo 1893435 44356643 := bstep (se 1 (by rfl) ⟨33267482, by rfl⟩ : syracuseStep 44356643 = 66534965) B66534965
theorem B29571095 : Blo 1893435 29571095 := bstep (se 1 (by rfl) ⟨22178321, by rfl⟩ : syracuseStep 29571095 = 44356643) B44356643
theorem B19714063 : Blo 1893435 19714063 := bstep (se 1 (by rfl) ⟨14785547, by rfl⟩ : syracuseStep 19714063 = 29571095) B29571095
theorem B26285417 : Blo 1893435 26285417 := bstep (se 2 (by rfl) ⟨9857031, by rfl⟩ : syracuseStep 26285417 = 19714063) B19714063
theorem B17523611 : Blo 1893435 17523611 := bstep (se 1 (by rfl) ⟨13142708, by rfl⟩ : syracuseStep 17523611 = 26285417) B26285417
theorem B11682407 : Blo 1893435 11682407 := bstep (se 1 (by rfl) ⟨8761805, by rfl⟩ : syracuseStep 11682407 = 17523611) B17523611
theorem B31153085 : Blo 1893435 31153085 := bstep (se 3 (by rfl) ⟨5841203, by rfl⟩ : syracuseStep 31153085 = 11682407) B11682407
theorem B20768723 : Blo 1893435 20768723 := bstep (se 1 (by rfl) ⟨15576542, by rfl⟩ : syracuseStep 20768723 = 31153085) B31153085
theorem B13845815 : Blo 1893435 13845815 := bstep (se 1 (by rfl) ⟨10384361, by rfl⟩ : syracuseStep 13845815 = 20768723) B20768723
theorem B9230543 : Blo 1893435 9230543 := bstep (se 1 (by rfl) ⟨6922907, by rfl⟩ : syracuseStep 9230543 = 13845815) B13845815
theorem B6153695 : Blo 1893435 6153695 := bstep (se 1 (by rfl) ⟨4615271, by rfl⟩ : syracuseStep 6153695 = 9230543) B9230543
theorem B4102463 : Blo 1893435 4102463 := bstep (se 1 (by rfl) ⟨3076847, by rfl⟩ : syracuseStep 4102463 = 6153695) B6153695
theorem B2734975 : Blo 1893435 2734975 := bstep (se 1 (by rfl) ⟨2051231, by rfl⟩ : syracuseStep 2734975 = 4102463) B4102463
theorem B3646633 : Blo 1893435 3646633 := bstep (se 2 (by rfl) ⟨1367487, by rfl⟩ : syracuseStep 3646633 = 2734975) B2734975
theorem B4862177 : Blo 1893435 4862177 := bstep (se 2 (by rfl) ⟨1823316, by rfl⟩ : syracuseStep 4862177 = 3646633) B3646633
theorem B3241451 : Blo 1893435 3241451 := bstep (se 1 (by rfl) ⟨2431088, by rfl⟩ : syracuseStep 3241451 = 4862177) B4862177
theorem B2160967 : Blo 1893435 2160967 := bstep (se 1 (by rfl) ⟨1620725, by rfl⟩ : syracuseStep 2160967 = 3241451) B3241451
theorem B2881289 : Blo 1893435 2881289 := bstep (se 2 (by rfl) ⟨1080483, by rfl⟩ : syracuseStep 2881289 = 2160967) B2160967
theorem B7683437 : Blo 1893435 7683437 := bstep (se 3 (by rfl) ⟨1440644, by rfl⟩ : syracuseStep 7683437 = 2881289) B2881289
theorem B5122291 : Blo 1893435 5122291 := bstep (se 1 (by rfl) ⟨3841718, by rfl⟩ : syracuseStep 5122291 = 7683437) B7683437
theorem B6829721 : Blo 1893435 6829721 := bstep (se 2 (by rfl) ⟨2561145, by rfl⟩ : syracuseStep 6829721 = 5122291) B5122291
theorem B4553147 : Blo 1893435 4553147 := bstep (se 1 (by rfl) ⟨3414860, by rfl⟩ : syracuseStep 4553147 = 6829721) B6829721
theorem B3035431 : Blo 1893435 3035431 := bstep (se 1 (by rfl) ⟨2276573, by rfl⟩ : syracuseStep 3035431 = 4553147) B4553147
theorem B4047241 : Blo 1893435 4047241 := bstep (se 2 (by rfl) ⟨1517715, by rfl⟩ : syracuseStep 4047241 = 3035431) B3035431
theorem B5396321 : Blo 1893435 5396321 := bstep (se 2 (by rfl) ⟨2023620, by rfl⟩ : syracuseStep 5396321 = 4047241) B4047241
theorem B3597547 : Blo 1893435 3597547 := bstep (se 1 (by rfl) ⟨2698160, by rfl⟩ : syracuseStep 3597547 = 5396321) B5396321
theorem B4796729 : Blo 1893435 4796729 := bstep (se 2 (by rfl) ⟨1798773, by rfl⟩ : syracuseStep 4796729 = 3597547) B3597547
theorem B3197819 : Blo 1893435 3197819 := bstep (se 1 (by rfl) ⟨2398364, by rfl⟩ : syracuseStep 3197819 = 4796729) B4796729
theorem B2131879 : Blo 1893435 2131879 := bstep (se 1 (by rfl) ⟨1598909, by rfl⟩ : syracuseStep 2131879 = 3197819) B3197819
theorem B2842505 : Blo 1893435 2842505 := bstep (se 2 (by rfl) ⟨1065939, by rfl⟩ : syracuseStep 2842505 = 2131879) B2131879
theorem B1895003 : Blo 1893435 1895003 := bstep (se 1 (by rfl) ⟨1421252, by rfl⟩ : syracuseStep 1895003 = 2842505) B2842505
theorem B9593477 : Blo 1893435 9593477 := bbase (se 4 (by rfl) ⟨899388, by rfl⟩ : syracuseStep 9593477 = 1798777) (by norm_num)
theorem B6395651 : Blo 1893435 6395651 := bstep (se 1 (by rfl) ⟨4796738, by rfl⟩ : syracuseStep 6395651 = 9593477) B9593477
theorem B4263767 : Blo 1893435 4263767 := bstep (se 1 (by rfl) ⟨3197825, by rfl⟩ : syracuseStep 4263767 = 6395651) B6395651
theorem B2842511 : Blo 1893435 2842511 := bstep (se 1 (by rfl) ⟨2131883, by rfl⟩ : syracuseStep 2842511 = 4263767) B4263767
theorem B1895007 : Blo 1893435 1895007 := bstep (se 1 (by rfl) ⟨1421255, by rfl⟩ : syracuseStep 1895007 = 2842511) B2842511
theorem B2842517 : Blo 1893435 2842517 := bbase (se 6 (by rfl) ⟨66621, by rfl⟩ : syracuseStep 2842517 = 133243) (by norm_num)
theorem B1895011 : Blo 1893435 1895011 := bstep (se 1 (by rfl) ⟨1421258, by rfl⟩ : syracuseStep 1895011 = 2842517) B2842517
theorem B2023633 : Blo 1893435 2023633 := bbase (se 2 (by rfl) ⟨758862, by rfl⟩ : syracuseStep 2023633 = 1517725) (by norm_num)
theorem B10792709 : Blo 1893435 10792709 := bstep (se 4 (by rfl) ⟨1011816, by rfl⟩ : syracuseStep 10792709 = 2023633) B2023633
theorem B7195139 : Blo 1893435 7195139 := bstep (se 1 (by rfl) ⟨5396354, by rfl⟩ : syracuseStep 7195139 = 10792709) B10792709
theorem B4796759 : Blo 1893435 4796759 := bstep (se 1 (by rfl) ⟨3597569, by rfl⟩ : syracuseStep 4796759 = 7195139) B7195139
theorem B3197839 : Blo 1893435 3197839 := bstep (se 1 (by rfl) ⟨2398379, by rfl⟩ : syracuseStep 3197839 = 4796759) B4796759
theorem B4263785 : Blo 1893435 4263785 := bstep (se 2 (by rfl) ⟨1598919, by rfl⟩ : syracuseStep 4263785 = 3197839) B3197839
theorem B2842523 : Blo 1893435 2842523 := bstep (se 1 (by rfl) ⟨2131892, by rfl⟩ : syracuseStep 2842523 = 4263785) B4263785
theorem B1895015 : Blo 1893435 1895015 := bstep (se 1 (by rfl) ⟨1421261, by rfl⟩ : syracuseStep 1895015 = 2842523) B2842523
theorem B2131897 : Blo 1893435 2131897 := bbase (se 2 (by rfl) ⟨799461, by rfl⟩ : syracuseStep 2131897 = 1598923) (by norm_num)
theorem B2842529 : Blo 1893435 2842529 := bstep (se 2 (by rfl) ⟨1065948, by rfl⟩ : syracuseStep 2842529 = 2131897) B2131897
theorem B1895019 : Blo 1893435 1895019 := bstep (se 1 (by rfl) ⟨1421264, by rfl⟩ : syracuseStep 1895019 = 2842529) B2842529
theorem B2276597 : Blo 1893435 2276597 := bbase (se 5 (by rfl) ⟨106715, by rfl⟩ : syracuseStep 2276597 = 213431) (by norm_num)
theorem B6070925 : Blo 1893435 6070925 := bstep (se 3 (by rfl) ⟨1138298, by rfl⟩ : syracuseStep 6070925 = 2276597) B2276597
theorem B4047283 : Blo 1893435 4047283 := bstep (se 1 (by rfl) ⟨3035462, by rfl⟩ : syracuseStep 4047283 = 6070925) B6070925
theorem B5396377 : Blo 1893435 5396377 := bstep (se 2 (by rfl) ⟨2023641, by rfl⟩ : syracuseStep 5396377 = 4047283) B4047283
theorem B7195169 : Blo 1893435 7195169 := bstep (se 2 (by rfl) ⟨2698188, by rfl⟩ : syracuseStep 7195169 = 5396377) B5396377
theorem B4796779 : Blo 1893435 4796779 := bstep (se 1 (by rfl) ⟨3597584, by rfl⟩ : syracuseStep 4796779 = 7195169) B7195169
theorem B6395705 : Blo 1893435 6395705 := bstep (se 2 (by rfl) ⟨2398389, by rfl⟩ : syracuseStep 6395705 = 4796779) B4796779
theorem B4263803 : Blo 1893435 4263803 := bstep (se 1 (by rfl) ⟨3197852, by rfl⟩ : syracuseStep 4263803 = 6395705) B6395705
theorem B2842535 : Blo 1893435 2842535 := bstep (se 1 (by rfl) ⟨2131901, by rfl⟩ : syracuseStep 2842535 = 4263803) B4263803
theorem B1895023 : Blo 1893435 1895023 := bstep (se 1 (by rfl) ⟨1421267, by rfl⟩ : syracuseStep 1895023 = 2842535) B2842535
theorem B2842541 : Blo 1893435 2842541 := bbase (se 3 (by rfl) ⟨532976, by rfl⟩ : syracuseStep 2842541 = 1065953) (by norm_num)
theorem B1895027 : Blo 1893435 1895027 := bstep (se 1 (by rfl) ⟨1421270, by rfl⟩ : syracuseStep 1895027 = 2842541) B2842541
theorem B4263821 : Blo 1893435 4263821 := bbase (se 3 (by rfl) ⟨799466, by rfl⟩ : syracuseStep 4263821 = 1598933) (by norm_num)
theorem B2842547 : Blo 1893435 2842547 := bstep (se 1 (by rfl) ⟨2131910, by rfl⟩ : syracuseStep 2842547 = 4263821) B4263821
theorem B1895031 : Blo 1893435 1895031 := bstep (se 1 (by rfl) ⟨1421273, by rfl⟩ : syracuseStep 1895031 = 2842547) B2842547
theorem B2398405 : Blo 1893435 2398405 := bbase (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) (by norm_num)
theorem B3197873 : Blo 1893435 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B2131915 : Blo 1893435 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B2842553 : Blo 1893435 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B1895035 : Blo 1893435 1895035 := bstep (se 1 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 1895035 = 2842553) B2842553
theorem B11682613 : Blo 1893435 11682613 := bbase (se 5 (by rfl) ⟨547622, by rfl⟩ : syracuseStep 11682613 = 1095245) (by norm_num)
theorem B62307269 : Blo 1893435 62307269 := bstep (se 4 (by rfl) ⟨5841306, by rfl⟩ : syracuseStep 62307269 = 11682613) B11682613
theorem B41538179 : Blo 1893435 41538179 := bstep (se 1 (by rfl) ⟨31153634, by rfl⟩ : syracuseStep 41538179 = 62307269) B62307269
theorem B27692119 : Blo 1893435 27692119 := bstep (se 1 (by rfl) ⟨20769089, by rfl⟩ : syracuseStep 27692119 = 41538179) B41538179
theorem B36922825 : Blo 1893435 36922825 := bstep (se 2 (by rfl) ⟨13846059, by rfl⟩ : syracuseStep 36922825 = 27692119) B27692119
theorem B49230433 : Blo 1893435 49230433 := bstep (se 2 (by rfl) ⟨18461412, by rfl⟩ : syracuseStep 49230433 = 36922825) B36922825
theorem B65640577 : Blo 1893435 65640577 := bstep (se 2 (by rfl) ⟨24615216, by rfl⟩ : syracuseStep 65640577 = 49230433) B49230433
theorem B87520769 : Blo 1893435 87520769 := bstep (se 2 (by rfl) ⟨32820288, by rfl⟩ : syracuseStep 87520769 = 65640577) B65640577
theorem B58347179 : Blo 1893435 58347179 := bstep (se 1 (by rfl) ⟨43760384, by rfl⟩ : syracuseStep 58347179 = 87520769) B87520769
theorem B38898119 : Blo 1893435 38898119 := bstep (se 1 (by rfl) ⟨29173589, by rfl⟩ : syracuseStep 38898119 = 58347179) B58347179
theorem B25932079 : Blo 1893435 25932079 := bstep (se 1 (by rfl) ⟨19449059, by rfl⟩ : syracuseStep 25932079 = 38898119) B38898119
theorem B34576105 : Blo 1893435 34576105 := bstep (se 2 (by rfl) ⟨12966039, by rfl⟩ : syracuseStep 34576105 = 25932079) B25932079
theorem B46101473 : Blo 1893435 46101473 := bstep (se 2 (by rfl) ⟨17288052, by rfl⟩ : syracuseStep 46101473 = 34576105) B34576105
theorem B30734315 : Blo 1893435 30734315 := bstep (se 1 (by rfl) ⟨23050736, by rfl⟩ : syracuseStep 30734315 = 46101473) B46101473
theorem B20489543 : Blo 1893435 20489543 := bstep (se 1 (by rfl) ⟨15367157, by rfl⟩ : syracuseStep 20489543 = 30734315) B30734315
theorem B13659695 : Blo 1893435 13659695 := bstep (se 1 (by rfl) ⟨10244771, by rfl⟩ : syracuseStep 13659695 = 20489543) B20489543
theorem B9106463 : Blo 1893435 9106463 := bstep (se 1 (by rfl) ⟨6829847, by rfl⟩ : syracuseStep 9106463 = 13659695) B13659695
theorem B24283901 : Blo 1893435 24283901 := bstep (se 3 (by rfl) ⟨4553231, by rfl⟩ : syracuseStep 24283901 = 9106463) B9106463
theorem B16189267 : Blo 1893435 16189267 := bstep (se 1 (by rfl) ⟨12141950, by rfl⟩ : syracuseStep 16189267 = 24283901) B24283901
theorem B21585689 : Blo 1893435 21585689 := bstep (se 2 (by rfl) ⟨8094633, by rfl⟩ : syracuseStep 21585689 = 16189267) B16189267
theorem B14390459 : Blo 1893435 14390459 := bstep (se 1 (by rfl) ⟨10792844, by rfl⟩ : syracuseStep 14390459 = 21585689) B21585689
theorem B9593639 : Blo 1893435 9593639 := bstep (se 1 (by rfl) ⟨7195229, by rfl⟩ : syracuseStep 9593639 = 14390459) B14390459
theorem B6395759 : Blo 1893435 6395759 := bstep (se 1 (by rfl) ⟨4796819, by rfl⟩ : syracuseStep 6395759 = 9593639) B9593639
theorem B4263839 : Blo 1893435 4263839 := bstep (se 1 (by rfl) ⟨3197879, by rfl⟩ : syracuseStep 4263839 = 6395759) B6395759
theorem B2842559 : Blo 1893435 2842559 := bstep (se 1 (by rfl) ⟨2131919, by rfl⟩ : syracuseStep 2842559 = 4263839) B4263839
theorem B1895039 : Blo 1893435 1895039 := bstep (se 1 (by rfl) ⟨1421279, by rfl⟩ : syracuseStep 1895039 = 2842559) B2842559
theorem B2842565 : Blo 1893435 2842565 := bbase (se 4 (by rfl) ⟨266490, by rfl⟩ : syracuseStep 2842565 = 532981) (by norm_num)
theorem B1895043 : Blo 1893435 1895043 := bstep (se 1 (by rfl) ⟨1421282, by rfl⟩ : syracuseStep 1895043 = 2842565) B2842565
theorem B3197893 : Blo 1893435 3197893 := bbase (se 4 (by rfl) ⟨299802, by rfl⟩ : syracuseStep 3197893 = 599605) (by norm_num)
theorem B4263857 : Blo 1893435 4263857 := bstep (se 2 (by rfl) ⟨1598946, by rfl⟩ : syracuseStep 4263857 = 3197893) B3197893
theorem B2842571 : Blo 1893435 2842571 := bstep (se 1 (by rfl) ⟨2131928, by rfl⟩ : syracuseStep 2842571 = 4263857) B4263857
theorem B1895047 : Blo 1893435 1895047 := bstep (se 1 (by rfl) ⟨1421285, by rfl⟩ : syracuseStep 1895047 = 2842571) B2842571
theorem B2131933 : Blo 1893435 2131933 := bbase (se 3 (by rfl) ⟨399737, by rfl⟩ : syracuseStep 2131933 = 799475) (by norm_num)
theorem B2842577 : Blo 1893435 2842577 := bstep (se 2 (by rfl) ⟨1065966, by rfl⟩ : syracuseStep 2842577 = 2131933) B2131933
theorem B1895051 : Blo 1893435 1895051 := bstep (se 1 (by rfl) ⟨1421288, by rfl⟩ : syracuseStep 1895051 = 2842577) B2842577
theorem B6395813 : Blo 1893435 6395813 := bbase (se 4 (by rfl) ⟨599607, by rfl⟩ : syracuseStep 6395813 = 1199215) (by norm_num)
theorem B4263875 : Blo 1893435 4263875 := bstep (se 1 (by rfl) ⟨3197906, by rfl⟩ : syracuseStep 4263875 = 6395813) B6395813
theorem B2842583 : Blo 1893435 2842583 := bstep (se 1 (by rfl) ⟨2131937, by rfl⟩ : syracuseStep 2842583 = 4263875) B4263875
theorem B1895055 : Blo 1893435 1895055 := bstep (se 1 (by rfl) ⟨1421291, by rfl⟩ : syracuseStep 1895055 = 2842583) B2842583
theorem B2842589 : Blo 1893435 2842589 := bbase (se 3 (by rfl) ⟨532985, by rfl⟩ : syracuseStep 2842589 = 1065971) (by norm_num)
theorem B1895059 : Blo 1893435 1895059 := bstep (se 1 (by rfl) ⟨1421294, by rfl⟩ : syracuseStep 1895059 = 2842589) B2842589
theorem B4263893 : Blo 1893435 4263893 := bbase (se 7 (by rfl) ⟨49967, by rfl⟩ : syracuseStep 4263893 = 99935) (by norm_num)
theorem B2842595 : Blo 1893435 2842595 := bstep (se 1 (by rfl) ⟨2131946, by rfl⟩ : syracuseStep 2842595 = 4263893) B4263893
theorem B1895063 : Blo 1893435 1895063 := bstep (se 1 (by rfl) ⟨1421297, by rfl⟩ : syracuseStep 1895063 = 2842595) B2842595
theorem B12142133 : Blo 1893435 12142133 := bbase (se 5 (by rfl) ⟨569162, by rfl⟩ : syracuseStep 12142133 = 1138325) (by norm_num)
theorem B8094755 : Blo 1893435 8094755 := bstep (se 1 (by rfl) ⟨6071066, by rfl⟩ : syracuseStep 8094755 = 12142133) B12142133
theorem B5396503 : Blo 1893435 5396503 := bstep (se 1 (by rfl) ⟨4047377, by rfl⟩ : syracuseStep 5396503 = 8094755) B8094755
theorem B7195337 : Blo 1893435 7195337 := bstep (se 2 (by rfl) ⟨2698251, by rfl⟩ : syracuseStep 7195337 = 5396503) B5396503
theorem B4796891 : Blo 1893435 4796891 := bstep (se 1 (by rfl) ⟨3597668, by rfl⟩ : syracuseStep 4796891 = 7195337) B7195337
theorem B3197927 : Blo 1893435 3197927 := bstep (se 1 (by rfl) ⟨2398445, by rfl⟩ : syracuseStep 3197927 = 4796891) B4796891
theorem B2131951 : Blo 1893435 2131951 := bstep (se 1 (by rfl) ⟨1598963, by rfl⟩ : syracuseStep 2131951 = 3197927) B3197927
theorem B2842601 : Blo 1893435 2842601 := bstep (se 2 (by rfl) ⟨1065975, by rfl⟩ : syracuseStep 2842601 = 2131951) B2131951
theorem B1895067 : Blo 1893435 1895067 := bstep (se 1 (by rfl) ⟨1421300, by rfl⟩ : syracuseStep 1895067 = 2842601) B2842601
theorem B4553309 : Blo 1893435 4553309 := bbase (se 3 (by rfl) ⟨853745, by rfl⟩ : syracuseStep 4553309 = 1707491) (by norm_num)
theorem B3035539 : Blo 1893435 3035539 := bstep (se 1 (by rfl) ⟨2276654, by rfl⟩ : syracuseStep 3035539 = 4553309) B4553309
theorem B16189541 : Blo 1893435 16189541 := bstep (se 4 (by rfl) ⟨1517769, by rfl⟩ : syracuseStep 16189541 = 3035539) B3035539
theorem B10793027 : Blo 1893435 10793027 := bstep (se 1 (by rfl) ⟨8094770, by rfl⟩ : syracuseStep 10793027 = 16189541) B16189541
theorem B7195351 : Blo 1893435 7195351 := bstep (se 1 (by rfl) ⟨5396513, by rfl⟩ : syracuseStep 7195351 = 10793027) B10793027
theorem B9593801 : Blo 1893435 9593801 := bstep (se 2 (by rfl) ⟨3597675, by rfl⟩ : syracuseStep 9593801 = 7195351) B7195351
theorem B6395867 : Blo 1893435 6395867 := bstep (se 1 (by rfl) ⟨4796900, by rfl⟩ : syracuseStep 6395867 = 9593801) B9593801
theorem B4263911 : Blo 1893435 4263911 := bstep (se 1 (by rfl) ⟨3197933, by rfl⟩ : syracuseStep 4263911 = 6395867) B6395867
theorem B2842607 : Blo 1893435 2842607 := bstep (se 1 (by rfl) ⟨2131955, by rfl⟩ : syracuseStep 2842607 = 4263911) B4263911
theorem B1895071 : Blo 1893435 1895071 := bstep (se 1 (by rfl) ⟨1421303, by rfl⟩ : syracuseStep 1895071 = 2842607) B2842607
theorem B2842613 : Blo 1893435 2842613 := bbase (se 5 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 2842613 = 266495) (by norm_num)
theorem B1895075 : Blo 1893435 1895075 := bstep (se 1 (by rfl) ⟨1421306, by rfl⟩ : syracuseStep 1895075 = 2842613) B2842613
theorem B3414997 : Blo 1893435 3414997 := bbase (se 7 (by rfl) ⟨40019, by rfl⟩ : syracuseStep 3414997 = 80039) (by norm_num)
theorem B4553329 : Blo 1893435 4553329 := bstep (se 2 (by rfl) ⟨1707498, by rfl⟩ : syracuseStep 4553329 = 3414997) B3414997
theorem B6071105 : Blo 1893435 6071105 := bstep (se 2 (by rfl) ⟨2276664, by rfl⟩ : syracuseStep 6071105 = 4553329) B4553329
theorem B4047403 : Blo 1893435 4047403 := bstep (se 1 (by rfl) ⟨3035552, by rfl⟩ : syracuseStep 4047403 = 6071105) B6071105
theorem B5396537 : Blo 1893435 5396537 := bstep (se 2 (by rfl) ⟨2023701, by rfl⟩ : syracuseStep 5396537 = 4047403) B4047403
theorem B3597691 : Blo 1893435 3597691 := bstep (se 1 (by rfl) ⟨2698268, by rfl⟩ : syracuseStep 3597691 = 5396537) B5396537
theorem B4796921 : Blo 1893435 4796921 := bstep (se 2 (by rfl) ⟨1798845, by rfl⟩ : syracuseStep 4796921 = 3597691) B3597691
theorem B3197947 : Blo 1893435 3197947 := bstep (se 1 (by rfl) ⟨2398460, by rfl⟩ : syracuseStep 3197947 = 4796921) B4796921
theorem B4263929 : Blo 1893435 4263929 := bstep (se 2 (by rfl) ⟨1598973, by rfl⟩ : syracuseStep 4263929 = 3197947) B3197947
theorem B2842619 : Blo 1893435 2842619 := bstep (se 1 (by rfl) ⟨2131964, by rfl⟩ : syracuseStep 2842619 = 4263929) B4263929
theorem B1895079 : Blo 1893435 1895079 := bstep (se 1 (by rfl) ⟨1421309, by rfl⟩ : syracuseStep 1895079 = 2842619) B2842619
theorem B2131969 : Blo 1893435 2131969 := bbase (se 2 (by rfl) ⟨799488, by rfl⟩ : syracuseStep 2131969 = 1598977) (by norm_num)
theorem B2842625 : Blo 1893435 2842625 := bstep (se 2 (by rfl) ⟨1065984, by rfl⟩ : syracuseStep 2842625 = 2131969) B2131969
theorem B1895083 : Blo 1893435 1895083 := bstep (se 1 (by rfl) ⟨1421312, by rfl⟩ : syracuseStep 1895083 = 2842625) B2842625
theorem B4796941 : Blo 1893435 4796941 := bbase (se 3 (by rfl) ⟨899426, by rfl⟩ : syracuseStep 4796941 = 1798853) (by norm_num)
theorem B6395921 : Blo 1893435 6395921 := bstep (se 2 (by rfl) ⟨2398470, by rfl⟩ : syracuseStep 6395921 = 4796941) B4796941
theorem B4263947 : Blo 1893435 4263947 := bstep (se 1 (by rfl) ⟨3197960, by rfl⟩ : syracuseStep 4263947 = 6395921) B6395921
theorem B2842631 : Blo 1893435 2842631 := bstep (se 1 (by rfl) ⟨2131973, by rfl⟩ : syracuseStep 2842631 = 4263947) B4263947
theorem B1895087 : Blo 1893435 1895087 := bstep (se 1 (by rfl) ⟨1421315, by rfl⟩ : syracuseStep 1895087 = 2842631) B2842631
theorem B2842637 : Blo 1893435 2842637 := bbase (se 3 (by rfl) ⟨532994, by rfl⟩ : syracuseStep 2842637 = 1065989) (by norm_num)
theorem B1895091 : Blo 1893435 1895091 := bstep (se 1 (by rfl) ⟨1421318, by rfl⟩ : syracuseStep 1895091 = 2842637) B2842637
theorem B4263965 : Blo 1893435 4263965 := bbase (se 3 (by rfl) ⟨799493, by rfl⟩ : syracuseStep 4263965 = 1598987) (by norm_num)
theorem B2842643 : Blo 1893435 2842643 := bstep (se 1 (by rfl) ⟨2131982, by rfl⟩ : syracuseStep 2842643 = 4263965) B4263965
theorem B1895095 : Blo 1893435 1895095 := bstep (se 1 (by rfl) ⟨1421321, by rfl⟩ : syracuseStep 1895095 = 2842643) B2842643
theorem B3197981 : Blo 1893435 3197981 := bbase (se 3 (by rfl) ⟨599621, by rfl⟩ : syracuseStep 3197981 = 1199243) (by norm_num)
theorem B2131987 : Blo 1893435 2131987 := bstep (se 1 (by rfl) ⟨1598990, by rfl⟩ : syracuseStep 2131987 = 3197981) B3197981
theorem B2842649 : Blo 1893435 2842649 := bstep (se 2 (by rfl) ⟨1065993, by rfl⟩ : syracuseStep 2842649 = 2131987) B2131987
theorem B1895099 : Blo 1893435 1895099 := bstep (se 1 (by rfl) ⟨1421324, by rfl⟩ : syracuseStep 1895099 = 2842649) B2842649
theorem B2079325 : Blo 1893435 2079325 := bbase (se 3 (by rfl) ⟨389873, by rfl⟩ : syracuseStep 2079325 = 779747) (by norm_num)
theorem B2772433 : Blo 1893435 2772433 := bstep (se 2 (by rfl) ⟨1039662, by rfl⟩ : syracuseStep 2772433 = 2079325) B2079325
theorem B14786309 : Blo 1893435 14786309 := bstep (se 4 (by rfl) ⟨1386216, by rfl⟩ : syracuseStep 14786309 = 2772433) B2772433
theorem B9857539 : Blo 1893435 9857539 := bstep (se 1 (by rfl) ⟨7393154, by rfl⟩ : syracuseStep 9857539 = 14786309) B14786309
theorem B52573541 : Blo 1893435 52573541 := bstep (se 4 (by rfl) ⟨4928769, by rfl⟩ : syracuseStep 52573541 = 9857539) B9857539
theorem B140196109 : Blo 1893435 140196109 := bstep (se 3 (by rfl) ⟨26286770, by rfl⟩ : syracuseStep 140196109 = 52573541) B52573541
theorem B186928145 : Blo 1893435 186928145 := bstep (se 2 (by rfl) ⟨70098054, by rfl⟩ : syracuseStep 186928145 = 140196109) B140196109
theorem B124618763 : Blo 1893435 124618763 := bstep (se 1 (by rfl) ⟨93464072, by rfl⟩ : syracuseStep 124618763 = 186928145) B186928145
theorem B332316701 : Blo 1893435 332316701 := bstep (se 3 (by rfl) ⟨62309381, by rfl⟩ : syracuseStep 332316701 = 124618763) B124618763
theorem B221544467 : Blo 1893435 221544467 := bstep (se 1 (by rfl) ⟨166158350, by rfl⟩ : syracuseStep 221544467 = 332316701) B332316701
theorem B147696311 : Blo 1893435 147696311 := bstep (se 1 (by rfl) ⟨110772233, by rfl⟩ : syracuseStep 147696311 = 221544467) B221544467
theorem B98464207 : Blo 1893435 98464207 := bstep (se 1 (by rfl) ⟨73848155, by rfl⟩ : syracuseStep 98464207 = 147696311) B147696311
theorem B131285609 : Blo 1893435 131285609 := bstep (se 2 (by rfl) ⟨49232103, by rfl⟩ : syracuseStep 131285609 = 98464207) B98464207
theorem B87523739 : Blo 1893435 87523739 := bstep (se 1 (by rfl) ⟨65642804, by rfl⟩ : syracuseStep 87523739 = 131285609) B131285609
theorem B58349159 : Blo 1893435 58349159 := bstep (se 1 (by rfl) ⟨43761869, by rfl⟩ : syracuseStep 58349159 = 87523739) B87523739
theorem B38899439 : Blo 1893435 38899439 := bstep (se 1 (by rfl) ⟨29174579, by rfl⟩ : syracuseStep 38899439 = 58349159) B58349159
theorem B25932959 : Blo 1893435 25932959 := bstep (se 1 (by rfl) ⟨19449719, by rfl⟩ : syracuseStep 25932959 = 38899439) B38899439
theorem B17288639 : Blo 1893435 17288639 := bstep (se 1 (by rfl) ⟨12966479, by rfl⟩ : syracuseStep 17288639 = 25932959) B25932959
theorem B11525759 : Blo 1893435 11525759 := bstep (se 1 (by rfl) ⟨8644319, by rfl⟩ : syracuseStep 11525759 = 17288639) B17288639
theorem B7683839 : Blo 1893435 7683839 := bstep (se 1 (by rfl) ⟨5762879, by rfl⟩ : syracuseStep 7683839 = 11525759) B11525759
theorem B5122559 : Blo 1893435 5122559 := bstep (se 1 (by rfl) ⟨3841919, by rfl⟩ : syracuseStep 5122559 = 7683839) B7683839
theorem B13660157 : Blo 1893435 13660157 := bstep (se 3 (by rfl) ⟨2561279, by rfl⟩ : syracuseStep 13660157 = 5122559) B5122559
theorem B9106771 : Blo 1893435 9106771 := bstep (se 1 (by rfl) ⟨6830078, by rfl⟩ : syracuseStep 9106771 = 13660157) B13660157
theorem B12142361 : Blo 1893435 12142361 := bstep (se 2 (by rfl) ⟨4553385, by rfl⟩ : syracuseStep 12142361 = 9106771) B9106771
theorem B8094907 : Blo 1893435 8094907 := bstep (se 1 (by rfl) ⟨6071180, by rfl⟩ : syracuseStep 8094907 = 12142361) B12142361
theorem B10793209 : Blo 1893435 10793209 := bstep (se 2 (by rfl) ⟨4047453, by rfl⟩ : syracuseStep 10793209 = 8094907) B8094907
theorem B14390945 : Blo 1893435 14390945 := bstep (se 2 (by rfl) ⟨5396604, by rfl⟩ : syracuseStep 14390945 = 10793209) B10793209
theorem B9593963 : Blo 1893435 9593963 := bstep (se 1 (by rfl) ⟨7195472, by rfl⟩ : syracuseStep 9593963 = 14390945) B14390945
theorem B6395975 : Blo 1893435 6395975 := bstep (se 1 (by rfl) ⟨4796981, by rfl⟩ : syracuseStep 6395975 = 9593963) B9593963
theorem B4263983 : Blo 1893435 4263983 := bstep (se 1 (by rfl) ⟨3197987, by rfl⟩ : syracuseStep 4263983 = 6395975) B6395975
theorem B2842655 : Blo 1893435 2842655 := bstep (se 1 (by rfl) ⟨2131991, by rfl⟩ : syracuseStep 2842655 = 4263983) B4263983
theorem B1895103 : Blo 1893435 1895103 := bstep (se 1 (by rfl) ⟨1421327, by rfl⟩ : syracuseStep 1895103 = 2842655) B2842655
theorem B2842661 : Blo 1893435 2842661 := bbase (se 4 (by rfl) ⟨266499, by rfl⟩ : syracuseStep 2842661 = 532999) (by norm_num)
theorem B1895107 : Blo 1893435 1895107 := bstep (se 1 (by rfl) ⟨1421330, by rfl⟩ : syracuseStep 1895107 = 2842661) B2842661
theorem B2398501 : Blo 1893435 2398501 := bbase (se 4 (by rfl) ⟨224859, by rfl⟩ : syracuseStep 2398501 = 449719) (by norm_num)
theorem B3198001 : Blo 1893435 3198001 := bstep (se 2 (by rfl) ⟨1199250, by rfl⟩ : syracuseStep 3198001 = 2398501) B2398501
theorem B4264001 : Blo 1893435 4264001 := bstep (se 2 (by rfl) ⟨1599000, by rfl⟩ : syracuseStep 4264001 = 3198001) B3198001
theorem B2842667 : Blo 1893435 2842667 := bstep (se 1 (by rfl) ⟨2132000, by rfl⟩ : syracuseStep 2842667 = 4264001) B4264001
theorem B1895111 : Blo 1893435 1895111 := bstep (se 1 (by rfl) ⟨1421333, by rfl⟩ : syracuseStep 1895111 = 2842667) B2842667
theorem B2132005 : Blo 1893435 2132005 := bbase (se 4 (by rfl) ⟨199875, by rfl⟩ : syracuseStep 2132005 = 399751) (by norm_num)
theorem B2842673 : Blo 1893435 2842673 := bstep (se 2 (by rfl) ⟨1066002, by rfl⟩ : syracuseStep 2842673 = 2132005) B2132005
theorem B1895115 : Blo 1893435 1895115 := bstep (se 1 (by rfl) ⟨1421336, by rfl⟩ : syracuseStep 1895115 = 2842673) B2842673
theorem B3415069 : Blo 1893435 3415069 := bbase (se 3 (by rfl) ⟨640325, by rfl⟩ : syracuseStep 3415069 = 1280651) (by norm_num)
theorem B4553425 : Blo 1893435 4553425 := bstep (se 2 (by rfl) ⟨1707534, by rfl⟩ : syracuseStep 4553425 = 3415069) B3415069
theorem B6071233 : Blo 1893435 6071233 := bstep (se 2 (by rfl) ⟨2276712, by rfl⟩ : syracuseStep 6071233 = 4553425) B4553425
theorem B8094977 : Blo 1893435 8094977 := bstep (se 2 (by rfl) ⟨3035616, by rfl⟩ : syracuseStep 8094977 = 6071233) B6071233
theorem B5396651 : Blo 1893435 5396651 := bstep (se 1 (by rfl) ⟨4047488, by rfl⟩ : syracuseStep 5396651 = 8094977) B8094977
theorem B3597767 : Blo 1893435 3597767 := bstep (se 1 (by rfl) ⟨2698325, by rfl⟩ : syracuseStep 3597767 = 5396651) B5396651
theorem B2398511 : Blo 1893435 2398511 := bstep (se 1 (by rfl) ⟨1798883, by rfl⟩ : syracuseStep 2398511 = 3597767) B3597767
theorem B6396029 : Blo 1893435 6396029 := bstep (se 3 (by rfl) ⟨1199255, by rfl⟩ : syracuseStep 6396029 = 2398511) B2398511
theorem B4264019 : Blo 1893435 4264019 := bstep (se 1 (by rfl) ⟨3198014, by rfl⟩ : syracuseStep 4264019 = 6396029) B6396029
theorem B2842679 : Blo 1893435 2842679 := bstep (se 1 (by rfl) ⟨2132009, by rfl⟩ : syracuseStep 2842679 = 4264019) B4264019
theorem B1895119 : Blo 1893435 1895119 := bstep (se 1 (by rfl) ⟨1421339, by rfl⟩ : syracuseStep 1895119 = 2842679) B2842679
theorem B2842685 : Blo 1893435 2842685 := bbase (se 3 (by rfl) ⟨533003, by rfl⟩ : syracuseStep 2842685 = 1066007) (by norm_num)
theorem B1895123 : Blo 1893435 1895123 := bstep (se 1 (by rfl) ⟨1421342, by rfl⟩ : syracuseStep 1895123 = 2842685) B2842685
theorem B4264037 : Blo 1893435 4264037 := bbase (se 4 (by rfl) ⟨399753, by rfl⟩ : syracuseStep 4264037 = 799507) (by norm_num)
theorem B2842691 : Blo 1893435 2842691 := bstep (se 1 (by rfl) ⟨2132018, by rfl⟩ : syracuseStep 2842691 = 4264037) B4264037
theorem B1895127 : Blo 1893435 1895127 := bstep (se 1 (by rfl) ⟨1421345, by rfl⟩ : syracuseStep 1895127 = 2842691) B2842691
theorem B4797053 : Blo 1893435 4797053 := bbase (se 3 (by rfl) ⟨899447, by rfl⟩ : syracuseStep 4797053 = 1798895) (by norm_num)
theorem B3198035 : Blo 1893435 3198035 := bstep (se 1 (by rfl) ⟨2398526, by rfl⟩ : syracuseStep 3198035 = 4797053) B4797053
theorem B2132023 : Blo 1893435 2132023 := bstep (se 1 (by rfl) ⟨1599017, by rfl⟩ : syracuseStep 2132023 = 3198035) B3198035
theorem B2842697 : Blo 1893435 2842697 := bstep (se 2 (by rfl) ⟨1066011, by rfl⟩ : syracuseStep 2842697 = 2132023) B2132023
theorem B1895131 : Blo 1893435 1895131 := bstep (se 1 (by rfl) ⟨1421348, by rfl⟩ : syracuseStep 1895131 = 2842697) B2842697
theorem B3597797 : Blo 1893435 3597797 := bbase (se 4 (by rfl) ⟨337293, by rfl⟩ : syracuseStep 3597797 = 674587) (by norm_num)
theorem B9594125 : Blo 1893435 9594125 := bstep (se 3 (by rfl) ⟨1798898, by rfl⟩ : syracuseStep 9594125 = 3597797) B3597797
theorem B6396083 : Blo 1893435 6396083 := bstep (se 1 (by rfl) ⟨4797062, by rfl⟩ : syracuseStep 6396083 = 9594125) B9594125
theorem B4264055 : Blo 1893435 4264055 := bstep (se 1 (by rfl) ⟨3198041, by rfl⟩ : syracuseStep 4264055 = 6396083) B6396083
theorem B2842703 : Blo 1893435 2842703 := bstep (se 1 (by rfl) ⟨2132027, by rfl⟩ : syracuseStep 2842703 = 4264055) B4264055
theorem B1895135 : Blo 1893435 1895135 := bstep (se 1 (by rfl) ⟨1421351, by rfl⟩ : syracuseStep 1895135 = 2842703) B2842703
theorem B2842709 : Blo 1893435 2842709 := bbase (se 8 (by rfl) ⟨16656, by rfl⟩ : syracuseStep 2842709 = 33313) (by norm_num)
theorem B1895139 : Blo 1893435 1895139 := bstep (se 1 (by rfl) ⟨1421354, by rfl⟩ : syracuseStep 1895139 = 2842709) B2842709
theorem B9857749 : Blo 1893435 9857749 := bbase (se 7 (by rfl) ⟨115520, by rfl⟩ : syracuseStep 9857749 = 231041) (by norm_num)
theorem B13143665 : Blo 1893435 13143665 := bstep (se 2 (by rfl) ⟨4928874, by rfl⟩ : syracuseStep 13143665 = 9857749) B9857749
theorem B35049773 : Blo 1893435 35049773 := bstep (se 3 (by rfl) ⟨6571832, by rfl⟩ : syracuseStep 35049773 = 13143665) B13143665
theorem B93466061 : Blo 1893435 93466061 := bstep (se 3 (by rfl) ⟨17524886, by rfl⟩ : syracuseStep 93466061 = 35049773) B35049773
theorem B62310707 : Blo 1893435 62310707 := bstep (se 1 (by rfl) ⟨46733030, by rfl⟩ : syracuseStep 62310707 = 93466061) B93466061
theorem B41540471 : Blo 1893435 41540471 := bstep (se 1 (by rfl) ⟨31155353, by rfl⟩ : syracuseStep 41540471 = 62310707) B62310707
theorem B27693647 : Blo 1893435 27693647 := bstep (se 1 (by rfl) ⟨20770235, by rfl⟩ : syracuseStep 27693647 = 41540471) B41540471
theorem B18462431 : Blo 1893435 18462431 := bstep (se 1 (by rfl) ⟨13846823, by rfl⟩ : syracuseStep 18462431 = 27693647) B27693647
theorem B12308287 : Blo 1893435 12308287 := bstep (se 1 (by rfl) ⟨9231215, by rfl⟩ : syracuseStep 12308287 = 18462431) B18462431
theorem B16411049 : Blo 1893435 16411049 := bstep (se 2 (by rfl) ⟨6154143, by rfl⟩ : syracuseStep 16411049 = 12308287) B12308287
theorem B10940699 : Blo 1893435 10940699 := bstep (se 1 (by rfl) ⟨8205524, by rfl⟩ : syracuseStep 10940699 = 16411049) B16411049
theorem B7293799 : Blo 1893435 7293799 := bstep (se 1 (by rfl) ⟨5470349, by rfl⟩ : syracuseStep 7293799 = 10940699) B10940699
theorem B9725065 : Blo 1893435 9725065 := bstep (se 2 (by rfl) ⟨3646899, by rfl⟩ : syracuseStep 9725065 = 7293799) B7293799
theorem B51867013 : Blo 1893435 51867013 := bstep (se 4 (by rfl) ⟨4862532, by rfl⟩ : syracuseStep 51867013 = 9725065) B9725065
theorem B69156017 : Blo 1893435 69156017 := bstep (se 2 (by rfl) ⟨25933506, by rfl⟩ : syracuseStep 69156017 = 51867013) B51867013
theorem B46104011 : Blo 1893435 46104011 := bstep (se 1 (by rfl) ⟨34578008, by rfl⟩ : syracuseStep 46104011 = 69156017) B69156017
theorem B30736007 : Blo 1893435 30736007 := bstep (se 1 (by rfl) ⟨23052005, by rfl⟩ : syracuseStep 30736007 = 46104011) B46104011
theorem B20490671 : Blo 1893435 20490671 := bstep (se 1 (by rfl) ⟨15368003, by rfl⟩ : syracuseStep 20490671 = 30736007) B30736007
theorem B13660447 : Blo 1893435 13660447 := bstep (se 1 (by rfl) ⟨10245335, by rfl⟩ : syracuseStep 13660447 = 20490671) B20490671
theorem B18213929 : Blo 1893435 18213929 := bstep (se 2 (by rfl) ⟨6830223, by rfl⟩ : syracuseStep 18213929 = 13660447) B13660447
theorem B12142619 : Blo 1893435 12142619 := bstep (se 1 (by rfl) ⟨9106964, by rfl⟩ : syracuseStep 12142619 = 18213929) B18213929
theorem B8095079 : Blo 1893435 8095079 := bstep (se 1 (by rfl) ⟨6071309, by rfl⟩ : syracuseStep 8095079 = 12142619) B12142619
theorem B5396719 : Blo 1893435 5396719 := bstep (se 1 (by rfl) ⟨4047539, by rfl⟩ : syracuseStep 5396719 = 8095079) B8095079
theorem B7195625 : Blo 1893435 7195625 := bstep (se 2 (by rfl) ⟨2698359, by rfl⟩ : syracuseStep 7195625 = 5396719) B5396719
theorem B4797083 : Blo 1893435 4797083 := bstep (se 1 (by rfl) ⟨3597812, by rfl⟩ : syracuseStep 4797083 = 7195625) B7195625
theorem B3198055 : Blo 1893435 3198055 := bstep (se 1 (by rfl) ⟨2398541, by rfl⟩ : syracuseStep 3198055 = 4797083) B4797083
theorem B4264073 : Blo 1893435 4264073 := bstep (se 2 (by rfl) ⟨1599027, by rfl⟩ : syracuseStep 4264073 = 3198055) B3198055
theorem B2842715 : Blo 1893435 2842715 := bstep (se 1 (by rfl) ⟨2132036, by rfl⟩ : syracuseStep 2842715 = 4264073) B4264073
theorem B1895143 : Blo 1893435 1895143 := bstep (se 1 (by rfl) ⟨1421357, by rfl⟩ : syracuseStep 1895143 = 2842715) B2842715
theorem B2132041 : Blo 1893435 2132041 := bbase (se 2 (by rfl) ⟨799515, by rfl⟩ : syracuseStep 2132041 = 1599031) (by norm_num)
theorem B2842721 : Blo 1893435 2842721 := bstep (se 2 (by rfl) ⟨1066020, by rfl⟩ : syracuseStep 2842721 = 2132041) B2132041
theorem B1895147 : Blo 1893435 1895147 := bstep (se 1 (by rfl) ⟨1421360, by rfl⟩ : syracuseStep 1895147 = 2842721) B2842721
theorem B4553501 : Blo 1893435 4553501 := bbase (se 3 (by rfl) ⟨853781, by rfl⟩ : syracuseStep 4553501 = 1707563) (by norm_num)
theorem B12142669 : Blo 1893435 12142669 := bstep (se 3 (by rfl) ⟨2276750, by rfl⟩ : syracuseStep 12142669 = 4553501) B4553501
theorem B16190225 : Blo 1893435 16190225 := bstep (se 2 (by rfl) ⟨6071334, by rfl⟩ : syracuseStep 16190225 = 12142669) B12142669
theorem B10793483 : Blo 1893435 10793483 := bstep (se 1 (by rfl) ⟨8095112, by rfl⟩ : syracuseStep 10793483 = 16190225) B16190225
theorem B7195655 : Blo 1893435 7195655 := bstep (se 1 (by rfl) ⟨5396741, by rfl⟩ : syracuseStep 7195655 = 10793483) B10793483
theorem B4797103 : Blo 1893435 4797103 := bstep (se 1 (by rfl) ⟨3597827, by rfl⟩ : syracuseStep 4797103 = 7195655) B7195655
theorem B6396137 : Blo 1893435 6396137 := bstep (se 2 (by rfl) ⟨2398551, by rfl⟩ : syracuseStep 6396137 = 4797103) B4797103
theorem B4264091 : Blo 1893435 4264091 := bstep (se 1 (by rfl) ⟨3198068, by rfl⟩ : syracuseStep 4264091 = 6396137) B6396137
theorem B2842727 : Blo 1893435 2842727 := bstep (se 1 (by rfl) ⟨2132045, by rfl⟩ : syracuseStep 2842727 = 4264091) B4264091
theorem B1895151 : Blo 1893435 1895151 := bstep (se 1 (by rfl) ⟨1421363, by rfl⟩ : syracuseStep 1895151 = 2842727) B2842727
theorem B2842733 : Blo 1893435 2842733 := bbase (se 3 (by rfl) ⟨533012, by rfl⟩ : syracuseStep 2842733 = 1066025) (by norm_num)
theorem B1895155 : Blo 1893435 1895155 := bstep (se 1 (by rfl) ⟨1421366, by rfl⟩ : syracuseStep 1895155 = 2842733) B2842733
theorem B4264109 : Blo 1893435 4264109 := bbase (se 3 (by rfl) ⟨799520, by rfl⟩ : syracuseStep 4264109 = 1599041) (by norm_num)
theorem B2842739 : Blo 1893435 2842739 := bstep (se 1 (by rfl) ⟨2132054, by rfl⟩ : syracuseStep 2842739 = 4264109) B4264109
theorem B1895159 : Blo 1893435 1895159 := bstep (se 1 (by rfl) ⟨1421369, by rfl⟩ : syracuseStep 1895159 = 2842739) B2842739
theorem B7684085 : Blo 1893435 7684085 := bbase (se 5 (by rfl) ⟨360191, by rfl⟩ : syracuseStep 7684085 = 720383) (by norm_num)
theorem B20490893 : Blo 1893435 20490893 := bstep (se 3 (by rfl) ⟨3842042, by rfl⟩ : syracuseStep 20490893 = 7684085) B7684085
theorem B13660595 : Blo 1893435 13660595 := bstep (se 1 (by rfl) ⟨10245446, by rfl⟩ : syracuseStep 13660595 = 20490893) B20490893
theorem B9107063 : Blo 1893435 9107063 := bstep (se 1 (by rfl) ⟨6830297, by rfl⟩ : syracuseStep 9107063 = 13660595) B13660595
theorem B6071375 : Blo 1893435 6071375 := bstep (se 1 (by rfl) ⟨4553531, by rfl⟩ : syracuseStep 6071375 = 9107063) B9107063
theorem B4047583 : Blo 1893435 4047583 := bstep (se 1 (by rfl) ⟨3035687, by rfl⟩ : syracuseStep 4047583 = 6071375) B6071375
theorem B5396777 : Blo 1893435 5396777 := bstep (se 2 (by rfl) ⟨2023791, by rfl⟩ : syracuseStep 5396777 = 4047583) B4047583
theorem B3597851 : Blo 1893435 3597851 := bstep (se 1 (by rfl) ⟨2698388, by rfl⟩ : syracuseStep 3597851 = 5396777) B5396777
theorem B2398567 : Blo 1893435 2398567 := bstep (se 1 (by rfl) ⟨1798925, by rfl⟩ : syracuseStep 2398567 = 3597851) B3597851
theorem B3198089 : Blo 1893435 3198089 := bstep (se 2 (by rfl) ⟨1199283, by rfl⟩ : syracuseStep 3198089 = 2398567) B2398567
theorem B2132059 : Blo 1893435 2132059 := bstep (se 1 (by rfl) ⟨1599044, by rfl⟩ : syracuseStep 2132059 = 3198089) B3198089
theorem B2842745 : Blo 1893435 2842745 := bstep (se 2 (by rfl) ⟨1066029, by rfl⟩ : syracuseStep 2842745 = 2132059) B2132059
theorem B1895163 : Blo 1893435 1895163 := bstep (se 1 (by rfl) ⟨1421372, by rfl⟩ : syracuseStep 1895163 = 2842745) B2842745
theorem B6830309 : Blo 1893435 6830309 := bbase (se 4 (by rfl) ⟨640341, by rfl⟩ : syracuseStep 6830309 = 1280683) (by norm_num)
theorem B4553539 : Blo 1893435 4553539 := bstep (se 1 (by rfl) ⟨3415154, by rfl⟩ : syracuseStep 4553539 = 6830309) B6830309
theorem B24285541 : Blo 1893435 24285541 := bstep (se 4 (by rfl) ⟨2276769, by rfl⟩ : syracuseStep 24285541 = 4553539) B4553539
theorem B32380721 : Blo 1893435 32380721 := bstep (se 2 (by rfl) ⟨12142770, by rfl⟩ : syracuseStep 32380721 = 24285541) B24285541
theorem B21587147 : Blo 1893435 21587147 := bstep (se 1 (by rfl) ⟨16190360, by rfl⟩ : syracuseStep 21587147 = 32380721) B32380721
theorem B14391431 : Blo 1893435 14391431 := bstep (se 1 (by rfl) ⟨10793573, by rfl⟩ : syracuseStep 14391431 = 21587147) B21587147
theorem B9594287 : Blo 1893435 9594287 := bstep (se 1 (by rfl) ⟨7195715, by rfl⟩ : syracuseStep 9594287 = 14391431) B14391431
theorem B6396191 : Blo 1893435 6396191 := bstep (se 1 (by rfl) ⟨4797143, by rfl⟩ : syracuseStep 6396191 = 9594287) B9594287
theorem B4264127 : Blo 1893435 4264127 := bstep (se 1 (by rfl) ⟨3198095, by rfl⟩ : syracuseStep 4264127 = 6396191) B6396191
theorem B2842751 : Blo 1893435 2842751 := bstep (se 1 (by rfl) ⟨2132063, by rfl⟩ : syracuseStep 2842751 = 4264127) B4264127
theorem B1895167 : Blo 1893435 1895167 := bstep (se 1 (by rfl) ⟨1421375, by rfl⟩ : syracuseStep 1895167 = 2842751) B2842751
theorem B2842757 : Blo 1893435 2842757 := bbase (se 4 (by rfl) ⟨266508, by rfl⟩ : syracuseStep 2842757 = 533017) (by norm_num)
theorem B1895171 : Blo 1893435 1895171 := bstep (se 1 (by rfl) ⟨1421378, by rfl⟩ : syracuseStep 1895171 = 2842757) B2842757
theorem B3198109 : Blo 1893435 3198109 := bbase (se 3 (by rfl) ⟨599645, by rfl⟩ : syracuseStep 3198109 = 1199291) (by norm_num)
theorem B4264145 : Blo 1893435 4264145 := bstep (se 2 (by rfl) ⟨1599054, by rfl⟩ : syracuseStep 4264145 = 3198109) B3198109
theorem B2842763 : Blo 1893435 2842763 := bstep (se 1 (by rfl) ⟨2132072, by rfl⟩ : syracuseStep 2842763 = 4264145) B4264145
theorem B1895175 : Blo 1893435 1895175 := bstep (se 1 (by rfl) ⟨1421381, by rfl⟩ : syracuseStep 1895175 = 2842763) B2842763
theorem B2132077 : Blo 1893435 2132077 := bbase (se 3 (by rfl) ⟨399764, by rfl⟩ : syracuseStep 2132077 = 799529) (by norm_num)
theorem B2842769 : Blo 1893435 2842769 := bstep (se 2 (by rfl) ⟨1066038, by rfl⟩ : syracuseStep 2842769 = 2132077) B2132077
theorem B1895179 : Blo 1893435 1895179 := bstep (se 1 (by rfl) ⟨1421384, by rfl⟩ : syracuseStep 1895179 = 2842769) B2842769
theorem B6396245 : Blo 1893435 6396245 := bbase (se 10 (by rfl) ⟨9369, by rfl⟩ : syracuseStep 6396245 = 18739) (by norm_num)
theorem B4264163 : Blo 1893435 4264163 := bstep (se 1 (by rfl) ⟨3198122, by rfl⟩ : syracuseStep 4264163 = 6396245) B6396245
theorem B2842775 : Blo 1893435 2842775 := bstep (se 1 (by rfl) ⟨2132081, by rfl⟩ : syracuseStep 2842775 = 4264163) B4264163
theorem B1895183 : Blo 1893435 1895183 := bstep (se 1 (by rfl) ⟨1421387, by rfl⟩ : syracuseStep 1895183 = 2842775) B2842775
theorem B2842781 : Blo 1893435 2842781 := bbase (se 3 (by rfl) ⟨533021, by rfl⟩ : syracuseStep 2842781 = 1066043) (by norm_num)
theorem B1895187 : Blo 1893435 1895187 := bstep (se 1 (by rfl) ⟨1421390, by rfl⟩ : syracuseStep 1895187 = 2842781) B2842781
theorem B4264181 : Blo 1893435 4264181 := bbase (se 5 (by rfl) ⟨199883, by rfl⟩ : syracuseStep 4264181 = 399767) (by norm_num)
theorem B2842787 : Blo 1893435 2842787 := bstep (se 1 (by rfl) ⟨2132090, by rfl⟩ : syracuseStep 2842787 = 4264181) B4264181
theorem B1895191 : Blo 1893435 1895191 := bstep (se 1 (by rfl) ⟨1421393, by rfl⟩ : syracuseStep 1895191 = 2842787) B2842787
theorem B7684213 : Blo 1893435 7684213 := bbase (se 5 (by rfl) ⟨360197, by rfl⟩ : syracuseStep 7684213 = 720395) (by norm_num)
theorem B10245617 : Blo 1893435 10245617 := bstep (se 2 (by rfl) ⟨3842106, by rfl⟩ : syracuseStep 10245617 = 7684213) B7684213
theorem B6830411 : Blo 1893435 6830411 := bstep (se 1 (by rfl) ⟨5122808, by rfl⟩ : syracuseStep 6830411 = 10245617) B10245617
theorem B18214429 : Blo 1893435 18214429 := bstep (se 3 (by rfl) ⟨3415205, by rfl⟩ : syracuseStep 18214429 = 6830411) B6830411
theorem B24285905 : Blo 1893435 24285905 := bstep (se 2 (by rfl) ⟨9107214, by rfl⟩ : syracuseStep 24285905 = 18214429) B18214429
theorem B16190603 : Blo 1893435 16190603 := bstep (se 1 (by rfl) ⟨12142952, by rfl⟩ : syracuseStep 16190603 = 24285905) B24285905
theorem B10793735 : Blo 1893435 10793735 := bstep (se 1 (by rfl) ⟨8095301, by rfl⟩ : syracuseStep 10793735 = 16190603) B16190603
theorem B7195823 : Blo 1893435 7195823 := bstep (se 1 (by rfl) ⟨5396867, by rfl⟩ : syracuseStep 7195823 = 10793735) B10793735
theorem B4797215 : Blo 1893435 4797215 := bstep (se 1 (by rfl) ⟨3597911, by rfl⟩ : syracuseStep 4797215 = 7195823) B7195823
theorem B3198143 : Blo 1893435 3198143 := bstep (se 1 (by rfl) ⟨2398607, by rfl⟩ : syracuseStep 3198143 = 4797215) B4797215
theorem B2132095 : Blo 1893435 2132095 := bstep (se 1 (by rfl) ⟨1599071, by rfl⟩ : syracuseStep 2132095 = 3198143) B3198143
theorem B2842793 : Blo 1893435 2842793 := bstep (se 2 (by rfl) ⟨1066047, by rfl⟩ : syracuseStep 2842793 = 2132095) B2132095
theorem B1895195 : Blo 1893435 1895195 := bstep (se 1 (by rfl) ⟨1421396, by rfl⟩ : syracuseStep 1895195 = 2842793) B2842793
theorem B3415213 : Blo 1893435 3415213 := bbase (se 3 (by rfl) ⟨640352, by rfl⟩ : syracuseStep 3415213 = 1280705) (by norm_num)
theorem B4553617 : Blo 1893435 4553617 := bstep (se 2 (by rfl) ⟨1707606, by rfl⟩ : syracuseStep 4553617 = 3415213) B3415213
theorem B6071489 : Blo 1893435 6071489 := bstep (se 2 (by rfl) ⟨2276808, by rfl⟩ : syracuseStep 6071489 = 4553617) B4553617
theorem B4047659 : Blo 1893435 4047659 := bstep (se 1 (by rfl) ⟨3035744, by rfl⟩ : syracuseStep 4047659 = 6071489) B6071489
theorem B2698439 : Blo 1893435 2698439 := bstep (se 1 (by rfl) ⟨2023829, by rfl⟩ : syracuseStep 2698439 = 4047659) B4047659
theorem B7195837 : Blo 1893435 7195837 := bstep (se 3 (by rfl) ⟨1349219, by rfl⟩ : syracuseStep 7195837 = 2698439) B2698439
theorem B9594449 : Blo 1893435 9594449 := bstep (se 2 (by rfl) ⟨3597918, by rfl⟩ : syracuseStep 9594449 = 7195837) B7195837
theorem B6396299 : Blo 1893435 6396299 := bstep (se 1 (by rfl) ⟨4797224, by rfl⟩ : syracuseStep 6396299 = 9594449) B9594449
theorem B4264199 : Blo 1893435 4264199 := bstep (se 1 (by rfl) ⟨3198149, by rfl⟩ : syracuseStep 4264199 = 6396299) B6396299
theorem B2842799 : Blo 1893435 2842799 := bstep (se 1 (by rfl) ⟨2132099, by rfl⟩ : syracuseStep 2842799 = 4264199) B4264199
theorem B1895199 : Blo 1893435 1895199 := bstep (se 1 (by rfl) ⟨1421399, by rfl⟩ : syracuseStep 1895199 = 2842799) B2842799
theorem B2842805 : Blo 1893435 2842805 := bbase (se 5 (by rfl) ⟨133256, by rfl⟩ : syracuseStep 2842805 = 266513) (by norm_num)
theorem B1895203 : Blo 1893435 1895203 := bstep (se 1 (by rfl) ⟨1421402, by rfl⟩ : syracuseStep 1895203 = 2842805) B2842805
theorem B4797245 : Blo 1893435 4797245 := bbase (se 3 (by rfl) ⟨899483, by rfl⟩ : syracuseStep 4797245 = 1798967) (by norm_num)
theorem B3198163 : Blo 1893435 3198163 := bstep (se 1 (by rfl) ⟨2398622, by rfl⟩ : syracuseStep 3198163 = 4797245) B4797245
theorem B4264217 : Blo 1893435 4264217 := bstep (se 2 (by rfl) ⟨1599081, by rfl⟩ : syracuseStep 4264217 = 3198163) B3198163
theorem B2842811 : Blo 1893435 2842811 := bstep (se 1 (by rfl) ⟨2132108, by rfl⟩ : syracuseStep 2842811 = 4264217) B4264217
theorem B1895207 : Blo 1893435 1895207 := bstep (se 1 (by rfl) ⟨1421405, by rfl⟩ : syracuseStep 1895207 = 2842811) B2842811
theorem B2132113 : Blo 1893435 2132113 := bbase (se 2 (by rfl) ⟨799542, by rfl⟩ : syracuseStep 2132113 = 1599085) (by norm_num)
theorem B2842817 : Blo 1893435 2842817 := bstep (se 2 (by rfl) ⟨1066056, by rfl⟩ : syracuseStep 2842817 = 2132113) B2132113
theorem B1895211 : Blo 1893435 1895211 := bstep (se 1 (by rfl) ⟨1421408, by rfl⟩ : syracuseStep 1895211 = 2842817) B2842817
theorem B3597949 : Blo 1893435 3597949 := bbase (se 3 (by rfl) ⟨674615, by rfl⟩ : syracuseStep 3597949 = 1349231) (by norm_num)
theorem B4797265 : Blo 1893435 4797265 := bstep (se 2 (by rfl) ⟨1798974, by rfl⟩ : syracuseStep 4797265 = 3597949) B3597949
theorem B6396353 : Blo 1893435 6396353 := bstep (se 2 (by rfl) ⟨2398632, by rfl⟩ : syracuseStep 6396353 = 4797265) B4797265
theorem B4264235 : Blo 1893435 4264235 := bstep (se 1 (by rfl) ⟨3198176, by rfl⟩ : syracuseStep 4264235 = 6396353) B6396353
theorem B2842823 : Blo 1893435 2842823 := bstep (se 1 (by rfl) ⟨2132117, by rfl⟩ : syracuseStep 2842823 = 4264235) B4264235
theorem B1895215 : Blo 1893435 1895215 := bstep (se 1 (by rfl) ⟨1421411, by rfl⟩ : syracuseStep 1895215 = 2842823) B2842823
theorem B2842829 : Blo 1893435 2842829 := bbase (se 3 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 2842829 = 1066061) (by norm_num)
theorem B1895219 : Blo 1893435 1895219 := bstep (se 1 (by rfl) ⟨1421414, by rfl⟩ : syracuseStep 1895219 = 2842829) B2842829
theorem B4264253 : Blo 1893435 4264253 := bbase (se 3 (by rfl) ⟨799547, by rfl⟩ : syracuseStep 4264253 = 1599095) (by norm_num)
theorem B2842835 : Blo 1893435 2842835 := bstep (se 1 (by rfl) ⟨2132126, by rfl⟩ : syracuseStep 2842835 = 4264253) B4264253
theorem B1895223 : Blo 1893435 1895223 := bstep (se 1 (by rfl) ⟨1421417, by rfl⟩ : syracuseStep 1895223 = 2842835) B2842835
theorem B3198197 : Blo 1893435 3198197 := bbase (se 5 (by rfl) ⟨149915, by rfl⟩ : syracuseStep 3198197 = 299831) (by norm_num)
theorem B2132131 : Blo 1893435 2132131 := bstep (se 1 (by rfl) ⟨1599098, by rfl⟩ : syracuseStep 2132131 = 3198197) B3198197
theorem B2842841 : Blo 1893435 2842841 := bstep (se 2 (by rfl) ⟨1066065, by rfl⟩ : syracuseStep 2842841 = 2132131) B2132131
theorem B1895227 : Blo 1893435 1895227 := bstep (se 1 (by rfl) ⟨1421420, by rfl⟩ : syracuseStep 1895227 = 2842841) B2842841
theorem B5763269 : Blo 1893435 5763269 := bbase (se 4 (by rfl) ⟨540306, by rfl⟩ : syracuseStep 5763269 = 1080613) (by norm_num)
theorem B15368717 : Blo 1893435 15368717 := bstep (se 3 (by rfl) ⟨2881634, by rfl⟩ : syracuseStep 15368717 = 5763269) B5763269
theorem B10245811 : Blo 1893435 10245811 := bstep (se 1 (by rfl) ⟨7684358, by rfl⟩ : syracuseStep 10245811 = 15368717) B15368717
theorem B13661081 : Blo 1893435 13661081 := bstep (se 2 (by rfl) ⟨5122905, by rfl⟩ : syracuseStep 13661081 = 10245811) B10245811
theorem B9107387 : Blo 1893435 9107387 := bstep (se 1 (by rfl) ⟨6830540, by rfl⟩ : syracuseStep 9107387 = 13661081) B13661081
theorem B6071591 : Blo 1893435 6071591 := bstep (se 1 (by rfl) ⟨4553693, by rfl⟩ : syracuseStep 6071591 = 9107387) B9107387
theorem B4047727 : Blo 1893435 4047727 := bstep (se 1 (by rfl) ⟨3035795, by rfl⟩ : syracuseStep 4047727 = 6071591) B6071591
theorem B5396969 : Blo 1893435 5396969 := bstep (se 2 (by rfl) ⟨2023863, by rfl⟩ : syracuseStep 5396969 = 4047727) B4047727
theorem B14391917 : Blo 1893435 14391917 := bstep (se 3 (by rfl) ⟨2698484, by rfl⟩ : syracuseStep 14391917 = 5396969) B5396969
theorem B9594611 : Blo 1893435 9594611 := bstep (se 1 (by rfl) ⟨7195958, by rfl⟩ : syracuseStep 9594611 = 14391917) B14391917
theorem B6396407 : Blo 1893435 6396407 := bstep (se 1 (by rfl) ⟨4797305, by rfl⟩ : syracuseStep 6396407 = 9594611) B9594611
theorem B4264271 : Blo 1893435 4264271 := bstep (se 1 (by rfl) ⟨3198203, by rfl⟩ : syracuseStep 4264271 = 6396407) B6396407
theorem B2842847 : Blo 1893435 2842847 := bstep (se 1 (by rfl) ⟨2132135, by rfl⟩ : syracuseStep 2842847 = 4264271) B4264271
theorem B1895231 : Blo 1893435 1895231 := bstep (se 1 (by rfl) ⟨1421423, by rfl⟩ : syracuseStep 1895231 = 2842847) B2842847
theorem B2842853 : Blo 1893435 2842853 := bbase (se 4 (by rfl) ⟨266517, by rfl⟩ : syracuseStep 2842853 = 533035) (by norm_num)
theorem B1895235 : Blo 1893435 1895235 := bstep (se 1 (by rfl) ⟨1421426, by rfl⟩ : syracuseStep 1895235 = 2842853) B2842853
theorem B2276857 : Blo 1893435 2276857 := bbase (se 2 (by rfl) ⟨853821, by rfl⟩ : syracuseStep 2276857 = 1707643) (by norm_num)
theorem B3035809 : Blo 1893435 3035809 := bstep (se 2 (by rfl) ⟨1138428, by rfl⟩ : syracuseStep 3035809 = 2276857) B2276857
theorem B4047745 : Blo 1893435 4047745 := bstep (se 2 (by rfl) ⟨1517904, by rfl⟩ : syracuseStep 4047745 = 3035809) B3035809
theorem B5396993 : Blo 1893435 5396993 := bstep (se 2 (by rfl) ⟨2023872, by rfl⟩ : syracuseStep 5396993 = 4047745) B4047745
theorem B3597995 : Blo 1893435 3597995 := bstep (se 1 (by rfl) ⟨2698496, by rfl⟩ : syracuseStep 3597995 = 5396993) B5396993
theorem B2398663 : Blo 1893435 2398663 := bstep (se 1 (by rfl) ⟨1798997, by rfl⟩ : syracuseStep 2398663 = 3597995) B3597995
theorem B3198217 : Blo 1893435 3198217 := bstep (se 2 (by rfl) ⟨1199331, by rfl⟩ : syracuseStep 3198217 = 2398663) B2398663
theorem B4264289 : Blo 1893435 4264289 := bstep (se 2 (by rfl) ⟨1599108, by rfl⟩ : syracuseStep 4264289 = 3198217) B3198217
theorem B2842859 : Blo 1893435 2842859 := bstep (se 1 (by rfl) ⟨2132144, by rfl⟩ : syracuseStep 2842859 = 4264289) B4264289
theorem B1895239 : Blo 1893435 1895239 := bstep (se 1 (by rfl) ⟨1421429, by rfl⟩ : syracuseStep 1895239 = 2842859) B2842859
theorem B2132149 : Blo 1893435 2132149 := bbase (se 5 (by rfl) ⟨99944, by rfl⟩ : syracuseStep 2132149 = 199889) (by norm_num)
theorem B2842865 : Blo 1893435 2842865 := bstep (se 2 (by rfl) ⟨1066074, by rfl⟩ : syracuseStep 2842865 = 2132149) B2132149
theorem B1895243 : Blo 1893435 1895243 := bstep (se 1 (by rfl) ⟨1421432, by rfl⟩ : syracuseStep 1895243 = 2842865) B2842865
theorem B2398673 : Blo 1893435 2398673 := bbase (se 2 (by rfl) ⟨899502, by rfl⟩ : syracuseStep 2398673 = 1799005) (by norm_num)
theorem B6396461 : Blo 1893435 6396461 := bstep (se 3 (by rfl) ⟨1199336, by rfl⟩ : syracuseStep 6396461 = 2398673) B2398673
theorem B4264307 : Blo 1893435 4264307 := bstep (se 1 (by rfl) ⟨3198230, by rfl⟩ : syracuseStep 4264307 = 6396461) B6396461
theorem B2842871 : Blo 1893435 2842871 := bstep (se 1 (by rfl) ⟨2132153, by rfl⟩ : syracuseStep 2842871 = 4264307) B4264307
theorem B1895247 : Blo 1893435 1895247 := bstep (se 1 (by rfl) ⟨1421435, by rfl⟩ : syracuseStep 1895247 = 2842871) B2842871
theorem B2842877 : Blo 1893435 2842877 := bbase (se 3 (by rfl) ⟨533039, by rfl⟩ : syracuseStep 2842877 = 1066079) (by norm_num)
theorem B1895251 : Blo 1893435 1895251 := bstep (se 1 (by rfl) ⟨1421438, by rfl⟩ : syracuseStep 1895251 = 2842877) B2842877
theorem B4264325 : Blo 1893435 4264325 := bbase (se 4 (by rfl) ⟨399780, by rfl⟩ : syracuseStep 4264325 = 799561) (by norm_num)
theorem B2842883 : Blo 1893435 2842883 := bstep (se 1 (by rfl) ⟨2132162, by rfl⟩ : syracuseStep 2842883 = 4264325) B4264325
theorem B1895255 : Blo 1893435 1895255 := bstep (se 1 (by rfl) ⟨1421441, by rfl⟩ : syracuseStep 1895255 = 2842883) B2842883
theorem B2698525 : Blo 1893435 2698525 := bbase (se 3 (by rfl) ⟨505973, by rfl⟩ : syracuseStep 2698525 = 1011947) (by norm_num)
theorem B3598033 : Blo 1893435 3598033 := bstep (se 2 (by rfl) ⟨1349262, by rfl⟩ : syracuseStep 3598033 = 2698525) B2698525
theorem B4797377 : Blo 1893435 4797377 := bstep (se 2 (by rfl) ⟨1799016, by rfl⟩ : syracuseStep 4797377 = 3598033) B3598033
theorem B3198251 : Blo 1893435 3198251 := bstep (se 1 (by rfl) ⟨2398688, by rfl⟩ : syracuseStep 3198251 = 4797377) B4797377
theorem B2132167 : Blo 1893435 2132167 := bstep (se 1 (by rfl) ⟨1599125, by rfl⟩ : syracuseStep 2132167 = 3198251) B3198251
theorem B2842889 : Blo 1893435 2842889 := bstep (se 2 (by rfl) ⟨1066083, by rfl⟩ : syracuseStep 2842889 = 2132167) B2132167
theorem B1895259 : Blo 1893435 1895259 := bstep (se 1 (by rfl) ⟨1421444, by rfl⟩ : syracuseStep 1895259 = 2842889) B2842889
theorem B9594773 : Blo 1893435 9594773 := bbase (se 6 (by rfl) ⟨224877, by rfl⟩ : syracuseStep 9594773 = 449755) (by norm_num)
theorem B6396515 : Blo 1893435 6396515 := bstep (se 1 (by rfl) ⟨4797386, by rfl⟩ : syracuseStep 6396515 = 9594773) B9594773
theorem B4264343 : Blo 1893435 4264343 := bstep (se 1 (by rfl) ⟨3198257, by rfl⟩ : syracuseStep 4264343 = 6396515) B6396515
theorem B2842895 : Blo 1893435 2842895 := bstep (se 1 (by rfl) ⟨2132171, by rfl⟩ : syracuseStep 2842895 = 4264343) B4264343
theorem B1895263 : Blo 1893435 1895263 := bstep (se 1 (by rfl) ⟨1421447, by rfl⟩ : syracuseStep 1895263 = 2842895) B2842895
theorem B2842901 : Blo 1893435 2842901 := bbase (se 6 (by rfl) ⟨66630, by rfl⟩ : syracuseStep 2842901 = 133261) (by norm_num)
theorem B1895267 : Blo 1893435 1895267 := bstep (se 1 (by rfl) ⟨1421450, by rfl⟩ : syracuseStep 1895267 = 2842901) B2842901
theorem B3509173 : Blo 1893435 3509173 := bbase (se 5 (by rfl) ⟨164492, by rfl⟩ : syracuseStep 3509173 = 328985) (by norm_num)
theorem B4678897 : Blo 1893435 4678897 := bstep (se 2 (by rfl) ⟨1754586, by rfl⟩ : syracuseStep 4678897 = 3509173) B3509173
theorem B6238529 : Blo 1893435 6238529 := bstep (se 2 (by rfl) ⟨2339448, by rfl⟩ : syracuseStep 6238529 = 4678897) B4678897
theorem B4159019 : Blo 1893435 4159019 := bstep (se 1 (by rfl) ⟨3119264, by rfl⟩ : syracuseStep 4159019 = 6238529) B6238529
theorem B11090717 : Blo 1893435 11090717 := bstep (se 3 (by rfl) ⟨2079509, by rfl⟩ : syracuseStep 11090717 = 4159019) B4159019
theorem B118300981 : Blo 1893435 118300981 := bstep (se 5 (by rfl) ⟨5545358, by rfl⟩ : syracuseStep 118300981 = 11090717) B11090717
theorem B157734641 : Blo 1893435 157734641 := bstep (se 2 (by rfl) ⟨59150490, by rfl⟩ : syracuseStep 157734641 = 118300981) B118300981
theorem B420625709 : Blo 1893435 420625709 := bstep (se 3 (by rfl) ⟨78867320, by rfl⟩ : syracuseStep 420625709 = 157734641) B157734641
theorem B280417139 : Blo 1893435 280417139 := bstep (se 1 (by rfl) ⟨210312854, by rfl⟩ : syracuseStep 280417139 = 420625709) B420625709
theorem B186944759 : Blo 1893435 186944759 := bstep (se 1 (by rfl) ⟨140208569, by rfl⟩ : syracuseStep 186944759 = 280417139) B280417139
theorem B124629839 : Blo 1893435 124629839 := bstep (se 1 (by rfl) ⟨93472379, by rfl⟩ : syracuseStep 124629839 = 186944759) B186944759
theorem B83086559 : Blo 1893435 83086559 := bstep (se 1 (by rfl) ⟨62314919, by rfl⟩ : syracuseStep 83086559 = 124629839) B124629839
theorem B55391039 : Blo 1893435 55391039 := bstep (se 1 (by rfl) ⟨41543279, by rfl⟩ : syracuseStep 55391039 = 83086559) B83086559
theorem B36927359 : Blo 1893435 36927359 := bstep (se 1 (by rfl) ⟨27695519, by rfl⟩ : syracuseStep 36927359 = 55391039) B55391039
theorem B24618239 : Blo 1893435 24618239 := bstep (se 1 (by rfl) ⟨18463679, by rfl⟩ : syracuseStep 24618239 = 36927359) B36927359
theorem B16412159 : Blo 1893435 16412159 := bstep (se 1 (by rfl) ⟨12309119, by rfl⟩ : syracuseStep 16412159 = 24618239) B24618239
theorem B10941439 : Blo 1893435 10941439 := bstep (se 1 (by rfl) ⟨8206079, by rfl⟩ : syracuseStep 10941439 = 16412159) B16412159
theorem B14588585 : Blo 1893435 14588585 := bstep (se 2 (by rfl) ⟨5470719, by rfl⟩ : syracuseStep 14588585 = 10941439) B10941439
theorem B9725723 : Blo 1893435 9725723 := bstep (se 1 (by rfl) ⟨7294292, by rfl⟩ : syracuseStep 9725723 = 14588585) B14588585
theorem B6483815 : Blo 1893435 6483815 := bstep (se 1 (by rfl) ⟨4862861, by rfl⟩ : syracuseStep 6483815 = 9725723) B9725723
theorem B4322543 : Blo 1893435 4322543 := bstep (se 1 (by rfl) ⟨3241907, by rfl⟩ : syracuseStep 4322543 = 6483815) B6483815
theorem B11526781 : Blo 1893435 11526781 := bstep (se 3 (by rfl) ⟨2161271, by rfl⟩ : syracuseStep 11526781 = 4322543) B4322543
theorem B15369041 : Blo 1893435 15369041 := bstep (se 2 (by rfl) ⟨5763390, by rfl⟩ : syracuseStep 15369041 = 11526781) B11526781
theorem B10246027 : Blo 1893435 10246027 := bstep (se 1 (by rfl) ⟨7684520, by rfl⟩ : syracuseStep 10246027 = 15369041) B15369041
theorem B13661369 : Blo 1893435 13661369 := bstep (se 2 (by rfl) ⟨5123013, by rfl⟩ : syracuseStep 13661369 = 10246027) B10246027
theorem B9107579 : Blo 1893435 9107579 := bstep (se 1 (by rfl) ⟨6830684, by rfl⟩ : syracuseStep 9107579 = 13661369) B13661369
theorem B24286877 : Blo 1893435 24286877 := bstep (se 3 (by rfl) ⟨4553789, by rfl⟩ : syracuseStep 24286877 = 9107579) B9107579
theorem B16191251 : Blo 1893435 16191251 := bstep (se 1 (by rfl) ⟨12143438, by rfl⟩ : syracuseStep 16191251 = 24286877) B24286877
theorem B10794167 : Blo 1893435 10794167 := bstep (se 1 (by rfl) ⟨8095625, by rfl⟩ : syracuseStep 10794167 = 16191251) B16191251
theorem B7196111 : Blo 1893435 7196111 := bstep (se 1 (by rfl) ⟨5397083, by rfl⟩ : syracuseStep 7196111 = 10794167) B10794167
theorem B4797407 : Blo 1893435 4797407 := bstep (se 1 (by rfl) ⟨3598055, by rfl⟩ : syracuseStep 4797407 = 7196111) B7196111
theorem B3198271 : Blo 1893435 3198271 := bstep (se 1 (by rfl) ⟨2398703, by rfl⟩ : syracuseStep 3198271 = 4797407) B4797407
theorem B4264361 : Blo 1893435 4264361 := bstep (se 2 (by rfl) ⟨1599135, by rfl⟩ : syracuseStep 4264361 = 3198271) B3198271
theorem B2842907 : Blo 1893435 2842907 := bstep (se 1 (by rfl) ⟨2132180, by rfl⟩ : syracuseStep 2842907 = 4264361) B4264361
theorem B1895271 : Blo 1893435 1895271 := bstep (se 1 (by rfl) ⟨1421453, by rfl⟩ : syracuseStep 1895271 = 2842907) B2842907
theorem B2132185 : Blo 1893435 2132185 := bbase (se 2 (by rfl) ⟨799569, by rfl⟩ : syracuseStep 2132185 = 1599139) (by norm_num)
theorem B2842913 : Blo 1893435 2842913 := bstep (se 2 (by rfl) ⟨1066092, by rfl⟩ : syracuseStep 2842913 = 2132185) B2132185
theorem B1895275 : Blo 1893435 1895275 := bstep (se 1 (by rfl) ⟨1421456, by rfl⟩ : syracuseStep 1895275 = 2842913) B2842913
theorem B2276905 : Blo 1893435 2276905 := bbase (se 2 (by rfl) ⟨853839, by rfl⟩ : syracuseStep 2276905 = 1707679) (by norm_num)
theorem B3035873 : Blo 1893435 3035873 := bstep (se 2 (by rfl) ⟨1138452, by rfl⟩ : syracuseStep 3035873 = 2276905) B2276905
theorem B2023915 : Blo 1893435 2023915 := bstep (se 1 (by rfl) ⟨1517936, by rfl⟩ : syracuseStep 2023915 = 3035873) B3035873
theorem B2698553 : Blo 1893435 2698553 := bstep (se 2 (by rfl) ⟨1011957, by rfl⟩ : syracuseStep 2698553 = 2023915) B2023915
theorem B7196141 : Blo 1893435 7196141 := bstep (se 3 (by rfl) ⟨1349276, by rfl⟩ : syracuseStep 7196141 = 2698553) B2698553
theorem B4797427 : Blo 1893435 4797427 := bstep (se 1 (by rfl) ⟨3598070, by rfl⟩ : syracuseStep 4797427 = 7196141) B7196141
theorem B6396569 : Blo 1893435 6396569 := bstep (se 2 (by rfl) ⟨2398713, by rfl⟩ : syracuseStep 6396569 = 4797427) B4797427
theorem B4264379 : Blo 1893435 4264379 := bstep (se 1 (by rfl) ⟨3198284, by rfl⟩ : syracuseStep 4264379 = 6396569) B6396569
theorem B2842919 : Blo 1893435 2842919 := bstep (se 1 (by rfl) ⟨2132189, by rfl⟩ : syracuseStep 2842919 = 4264379) B4264379
theorem B1895279 : Blo 1893435 1895279 := bstep (se 1 (by rfl) ⟨1421459, by rfl⟩ : syracuseStep 1895279 = 2842919) B2842919
theorem B2842925 : Blo 1893435 2842925 := bbase (se 3 (by rfl) ⟨533048, by rfl⟩ : syracuseStep 2842925 = 1066097) (by norm_num)
theorem B1895283 : Blo 1893435 1895283 := bstep (se 1 (by rfl) ⟨1421462, by rfl⟩ : syracuseStep 1895283 = 2842925) B2842925
theorem B4264397 : Blo 1893435 4264397 := bbase (se 3 (by rfl) ⟨799574, by rfl⟩ : syracuseStep 4264397 = 1599149) (by norm_num)
theorem B2842931 : Blo 1893435 2842931 := bstep (se 1 (by rfl) ⟨2132198, by rfl⟩ : syracuseStep 2842931 = 4264397) B4264397
theorem B1895287 : Blo 1893435 1895287 := bstep (se 1 (by rfl) ⟨1421465, by rfl⟩ : syracuseStep 1895287 = 2842931) B2842931
theorem B2398729 : Blo 1893435 2398729 := bbase (se 2 (by rfl) ⟨899523, by rfl⟩ : syracuseStep 2398729 = 1799047) (by norm_num)
theorem B3198305 : Blo 1893435 3198305 := bstep (se 2 (by rfl) ⟨1199364, by rfl⟩ : syracuseStep 3198305 = 2398729) B2398729
theorem B2132203 : Blo 1893435 2132203 := bstep (se 1 (by rfl) ⟨1599152, by rfl⟩ : syracuseStep 2132203 = 3198305) B3198305
theorem B2842937 : Blo 1893435 2842937 := bstep (se 2 (by rfl) ⟨1066101, by rfl⟩ : syracuseStep 2842937 = 2132203) B2132203
theorem B1895291 : Blo 1893435 1895291 := bstep (se 1 (by rfl) ⟨1421468, by rfl⟩ : syracuseStep 1895291 = 2842937) B2842937
theorem B4322597 : Blo 1893435 4322597 := bbase (se 4 (by rfl) ⟨405243, by rfl⟩ : syracuseStep 4322597 = 810487) (by norm_num)
theorem B46107701 : Blo 1893435 46107701 := bstep (se 5 (by rfl) ⟨2161298, by rfl⟩ : syracuseStep 46107701 = 4322597) B4322597
theorem B30738467 : Blo 1893435 30738467 := bstep (se 1 (by rfl) ⟨23053850, by rfl⟩ : syracuseStep 30738467 = 46107701) B46107701
theorem B20492311 : Blo 1893435 20492311 := bstep (se 1 (by rfl) ⟨15369233, by rfl⟩ : syracuseStep 20492311 = 30738467) B30738467
theorem B27323081 : Blo 1893435 27323081 := bstep (se 2 (by rfl) ⟨10246155, by rfl⟩ : syracuseStep 27323081 = 20492311) B20492311
theorem B18215387 : Blo 1893435 18215387 := bstep (se 1 (by rfl) ⟨13661540, by rfl⟩ : syracuseStep 18215387 = 27323081) B27323081
theorem B12143591 : Blo 1893435 12143591 := bstep (se 1 (by rfl) ⟨9107693, by rfl⟩ : syracuseStep 12143591 = 18215387) B18215387
theorem B8095727 : Blo 1893435 8095727 := bstep (se 1 (by rfl) ⟨6071795, by rfl⟩ : syracuseStep 8095727 = 12143591) B12143591
theorem B21588605 : Blo 1893435 21588605 := bstep (se 3 (by rfl) ⟨4047863, by rfl⟩ : syracuseStep 21588605 = 8095727) B8095727
theorem B14392403 : Blo 1893435 14392403 := bstep (se 1 (by rfl) ⟨10794302, by rfl⟩ : syracuseStep 14392403 = 21588605) B21588605
theorem B9594935 : Blo 1893435 9594935 := bstep (se 1 (by rfl) ⟨7196201, by rfl⟩ : syracuseStep 9594935 = 14392403) B14392403
theorem B6396623 : Blo 1893435 6396623 := bstep (se 1 (by rfl) ⟨4797467, by rfl⟩ : syracuseStep 6396623 = 9594935) B9594935
theorem B4264415 : Blo 1893435 4264415 := bstep (se 1 (by rfl) ⟨3198311, by rfl⟩ : syracuseStep 4264415 = 6396623) B6396623
theorem B2842943 : Blo 1893435 2842943 := bstep (se 1 (by rfl) ⟨2132207, by rfl⟩ : syracuseStep 2842943 = 4264415) B4264415
theorem B1895295 : Blo 1893435 1895295 := bstep (se 1 (by rfl) ⟨1421471, by rfl⟩ : syracuseStep 1895295 = 2842943) B2842943
theorem B2842949 : Blo 1893435 2842949 := bbase (se 4 (by rfl) ⟨266526, by rfl⟩ : syracuseStep 2842949 = 533053) (by norm_num)
theorem B1895299 : Blo 1893435 1895299 := bstep (se 1 (by rfl) ⟨1421474, by rfl⟩ : syracuseStep 1895299 = 2842949) B2842949
theorem B3198325 : Blo 1893435 3198325 := bbase (se 5 (by rfl) ⟨149921, by rfl⟩ : syracuseStep 3198325 = 299843) (by norm_num)
theorem B4264433 : Blo 1893435 4264433 := bstep (se 2 (by rfl) ⟨1599162, by rfl⟩ : syracuseStep 4264433 = 3198325) B3198325
theorem B2842955 : Blo 1893435 2842955 := bstep (se 1 (by rfl) ⟨2132216, by rfl⟩ : syracuseStep 2842955 = 4264433) B4264433
theorem B1895303 : Blo 1893435 1895303 := bstep (se 1 (by rfl) ⟨1421477, by rfl⟩ : syracuseStep 1895303 = 2842955) B2842955
theorem B2132221 : Blo 1893435 2132221 := bbase (se 3 (by rfl) ⟨399791, by rfl⟩ : syracuseStep 2132221 = 799583) (by norm_num)
theorem B2842961 : Blo 1893435 2842961 := bstep (se 2 (by rfl) ⟨1066110, by rfl⟩ : syracuseStep 2842961 = 2132221) B2132221
theorem B1895307 : Blo 1893435 1895307 := bstep (se 1 (by rfl) ⟨1421480, by rfl⟩ : syracuseStep 1895307 = 2842961) B2842961
theorem B6396677 : Blo 1893435 6396677 := bbase (se 4 (by rfl) ⟨599688, by rfl⟩ : syracuseStep 6396677 = 1199377) (by norm_num)
theorem B4264451 : Blo 1893435 4264451 := bstep (se 1 (by rfl) ⟨3198338, by rfl⟩ : syracuseStep 4264451 = 6396677) B6396677
theorem B2842967 : Blo 1893435 2842967 := bstep (se 1 (by rfl) ⟨2132225, by rfl⟩ : syracuseStep 2842967 = 4264451) B4264451
theorem B1895311 : Blo 1893435 1895311 := bstep (se 1 (by rfl) ⟨1421483, by rfl⟩ : syracuseStep 1895311 = 2842967) B2842967
theorem B2842973 : Blo 1893435 2842973 := bbase (se 3 (by rfl) ⟨533057, by rfl⟩ : syracuseStep 2842973 = 1066115) (by norm_num)
theorem B1895315 : Blo 1893435 1895315 := bstep (se 1 (by rfl) ⟨1421486, by rfl⟩ : syracuseStep 1895315 = 2842973) B2842973
theorem B4264469 : Blo 1893435 4264469 := bbase (se 6 (by rfl) ⟨99948, by rfl⟩ : syracuseStep 4264469 = 199897) (by norm_num)
theorem B2842979 : Blo 1893435 2842979 := bstep (se 1 (by rfl) ⟨2132234, by rfl⟩ : syracuseStep 2842979 = 4264469) B4264469
theorem B1895319 : Blo 1893435 1895319 := bstep (se 1 (by rfl) ⟨1421489, by rfl⟩ : syracuseStep 1895319 = 2842979) B2842979
theorem B7196309 : Blo 1893435 7196309 := bbase (se 6 (by rfl) ⟨168663, by rfl⟩ : syracuseStep 7196309 = 337327) (by norm_num)
theorem B4797539 : Blo 1893435 4797539 := bstep (se 1 (by rfl) ⟨3598154, by rfl⟩ : syracuseStep 4797539 = 7196309) B7196309
theorem B3198359 : Blo 1893435 3198359 := bstep (se 1 (by rfl) ⟨2398769, by rfl⟩ : syracuseStep 3198359 = 4797539) B4797539
theorem B2132239 : Blo 1893435 2132239 := bstep (se 1 (by rfl) ⟨1599179, by rfl⟩ : syracuseStep 2132239 = 3198359) B3198359
theorem B2842985 : Blo 1893435 2842985 := bstep (se 2 (by rfl) ⟨1066119, by rfl⟩ : syracuseStep 2842985 = 2132239) B2132239
theorem B1895323 : Blo 1893435 1895323 := bstep (se 1 (by rfl) ⟨1421492, by rfl⟩ : syracuseStep 1895323 = 2842985) B2842985
theorem B10794485 : Blo 1893435 10794485 := bbase (se 5 (by rfl) ⟨505991, by rfl⟩ : syracuseStep 10794485 = 1011983) (by norm_num)
theorem B7196323 : Blo 1893435 7196323 := bstep (se 1 (by rfl) ⟨5397242, by rfl⟩ : syracuseStep 7196323 = 10794485) B10794485
theorem B9595097 : Blo 1893435 9595097 := bstep (se 2 (by rfl) ⟨3598161, by rfl⟩ : syracuseStep 9595097 = 7196323) B7196323
theorem B6396731 : Blo 1893435 6396731 := bstep (se 1 (by rfl) ⟨4797548, by rfl⟩ : syracuseStep 6396731 = 9595097) B9595097
theorem B4264487 : Blo 1893435 4264487 := bstep (se 1 (by rfl) ⟨3198365, by rfl⟩ : syracuseStep 4264487 = 6396731) B6396731
theorem B2842991 : Blo 1893435 2842991 := bstep (se 1 (by rfl) ⟨2132243, by rfl⟩ : syracuseStep 2842991 = 4264487) B4264487
theorem B1895327 : Blo 1893435 1895327 := bstep (se 1 (by rfl) ⟨1421495, by rfl⟩ : syracuseStep 1895327 = 2842991) B2842991
theorem B2842997 : Blo 1893435 2842997 := bbase (se 5 (by rfl) ⟨133265, by rfl⟩ : syracuseStep 2842997 = 266531) (by norm_num)
theorem B1895331 : Blo 1893435 1895331 := bstep (se 1 (by rfl) ⟨1421498, by rfl⟩ : syracuseStep 1895331 = 2842997) B2842997
theorem B5123189 : Blo 1893435 5123189 := bbase (se 5 (by rfl) ⟨240149, by rfl⟩ : syracuseStep 5123189 = 480299) (by norm_num)
theorem B3415459 : Blo 1893435 3415459 := bstep (se 1 (by rfl) ⟨2561594, by rfl⟩ : syracuseStep 3415459 = 5123189) B5123189
theorem B4553945 : Blo 1893435 4553945 := bstep (se 2 (by rfl) ⟨1707729, by rfl⟩ : syracuseStep 4553945 = 3415459) B3415459
theorem B3035963 : Blo 1893435 3035963 := bstep (se 1 (by rfl) ⟨2276972, by rfl⟩ : syracuseStep 3035963 = 4553945) B4553945
theorem B2023975 : Blo 1893435 2023975 := bstep (se 1 (by rfl) ⟨1517981, by rfl⟩ : syracuseStep 2023975 = 3035963) B3035963
theorem B2698633 : Blo 1893435 2698633 := bstep (se 2 (by rfl) ⟨1011987, by rfl⟩ : syracuseStep 2698633 = 2023975) B2023975
theorem B3598177 : Blo 1893435 3598177 := bstep (se 2 (by rfl) ⟨1349316, by rfl⟩ : syracuseStep 3598177 = 2698633) B2698633
theorem B4797569 : Blo 1893435 4797569 := bstep (se 2 (by rfl) ⟨1799088, by rfl⟩ : syracuseStep 4797569 = 3598177) B3598177
theorem B3198379 : Blo 1893435 3198379 := bstep (se 1 (by rfl) ⟨2398784, by rfl⟩ : syracuseStep 3198379 = 4797569) B4797569
theorem B4264505 : Blo 1893435 4264505 := bstep (se 2 (by rfl) ⟨1599189, by rfl⟩ : syracuseStep 4264505 = 3198379) B3198379
theorem B2843003 : Blo 1893435 2843003 := bstep (se 1 (by rfl) ⟨2132252, by rfl⟩ : syracuseStep 2843003 = 4264505) B4264505
theorem B1895335 : Blo 1893435 1895335 := bstep (se 1 (by rfl) ⟨1421501, by rfl⟩ : syracuseStep 1895335 = 2843003) B2843003
theorem B2132257 : Blo 1893435 2132257 := bbase (se 2 (by rfl) ⟨799596, by rfl⟩ : syracuseStep 2132257 = 1599193) (by norm_num)
theorem B2843009 : Blo 1893435 2843009 := bstep (se 2 (by rfl) ⟨1066128, by rfl⟩ : syracuseStep 2843009 = 2132257) B2132257
theorem B1895339 : Blo 1893435 1895339 := bstep (se 1 (by rfl) ⟨1421504, by rfl⟩ : syracuseStep 1895339 = 2843009) B2843009
theorem B4797589 : Blo 1893435 4797589 := bbase (se 6 (by rfl) ⟨112443, by rfl⟩ : syracuseStep 4797589 = 224887) (by norm_num)
theorem B6396785 : Blo 1893435 6396785 := bstep (se 2 (by rfl) ⟨2398794, by rfl⟩ : syracuseStep 6396785 = 4797589) B4797589
theorem B4264523 : Blo 1893435 4264523 := bstep (se 1 (by rfl) ⟨3198392, by rfl⟩ : syracuseStep 4264523 = 6396785) B6396785
theorem B2843015 : Blo 1893435 2843015 := bstep (se 1 (by rfl) ⟨2132261, by rfl⟩ : syracuseStep 2843015 = 4264523) B4264523
theorem B1895343 : Blo 1893435 1895343 := bstep (se 1 (by rfl) ⟨1421507, by rfl⟩ : syracuseStep 1895343 = 2843015) B2843015
theorem B2843021 : Blo 1893435 2843021 := bbase (se 3 (by rfl) ⟨533066, by rfl⟩ : syracuseStep 2843021 = 1066133) (by norm_num)
theorem B1895347 : Blo 1893435 1895347 := bstep (se 1 (by rfl) ⟨1421510, by rfl⟩ : syracuseStep 1895347 = 2843021) B2843021
theorem B4264541 : Blo 1893435 4264541 := bbase (se 3 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 4264541 = 1599203) (by norm_num)
theorem B2843027 : Blo 1893435 2843027 := bstep (se 1 (by rfl) ⟨2132270, by rfl⟩ : syracuseStep 2843027 = 4264541) B4264541
theorem B1895351 : Blo 1893435 1895351 := bstep (se 1 (by rfl) ⟨1421513, by rfl⟩ : syracuseStep 1895351 = 2843027) B2843027
theorem B3198413 : Blo 1893435 3198413 := bbase (se 3 (by rfl) ⟨599702, by rfl⟩ : syracuseStep 3198413 = 1199405) (by norm_num)
theorem B2132275 : Blo 1893435 2132275 := bstep (se 1 (by rfl) ⟨1599206, by rfl⟩ : syracuseStep 2132275 = 3198413) B3198413
theorem B2843033 : Blo 1893435 2843033 := bstep (se 2 (by rfl) ⟨1066137, by rfl⟩ : syracuseStep 2843033 = 2132275) B2132275
theorem B1895355 : Blo 1893435 1895355 := bstep (se 1 (by rfl) ⟨1421516, by rfl⟩ : syracuseStep 1895355 = 2843033) B2843033
theorem B2881829 : Blo 1893435 2881829 := bbase (se 4 (by rfl) ⟨270171, by rfl⟩ : syracuseStep 2881829 = 540343) (by norm_num)
theorem B7684877 : Blo 1893435 7684877 := bstep (se 3 (by rfl) ⟨1440914, by rfl⟩ : syracuseStep 7684877 = 2881829) B2881829
theorem B5123251 : Blo 1893435 5123251 := bstep (se 1 (by rfl) ⟨3842438, by rfl⟩ : syracuseStep 5123251 = 7684877) B7684877
theorem B6831001 : Blo 1893435 6831001 := bstep (se 2 (by rfl) ⟨2561625, by rfl⟩ : syracuseStep 6831001 = 5123251) B5123251
theorem B9108001 : Blo 1893435 9108001 := bstep (se 2 (by rfl) ⟨3415500, by rfl⟩ : syracuseStep 9108001 = 6831001) B6831001
theorem B12144001 : Blo 1893435 12144001 := bstep (se 2 (by rfl) ⟨4554000, by rfl⟩ : syracuseStep 12144001 = 9108001) B9108001
theorem B16192001 : Blo 1893435 16192001 := bstep (se 2 (by rfl) ⟨6072000, by rfl⟩ : syracuseStep 16192001 = 12144001) B12144001
theorem B10794667 : Blo 1893435 10794667 := bstep (se 1 (by rfl) ⟨8096000, by rfl⟩ : syracuseStep 10794667 = 16192001) B16192001
theorem B14392889 : Blo 1893435 14392889 := bstep (se 2 (by rfl) ⟨5397333, by rfl⟩ : syracuseStep 14392889 = 10794667) B10794667
theorem B9595259 : Blo 1893435 9595259 := bstep (se 1 (by rfl) ⟨7196444, by rfl⟩ : syracuseStep 9595259 = 14392889) B14392889
theorem B6396839 : Blo 1893435 6396839 := bstep (se 1 (by rfl) ⟨4797629, by rfl⟩ : syracuseStep 6396839 = 9595259) B9595259
theorem B4264559 : Blo 1893435 4264559 := bstep (se 1 (by rfl) ⟨3198419, by rfl⟩ : syracuseStep 4264559 = 6396839) B6396839
theorem B2843039 : Blo 1893435 2843039 := bstep (se 1 (by rfl) ⟨2132279, by rfl⟩ : syracuseStep 2843039 = 4264559) B4264559
theorem B1895359 : Blo 1893435 1895359 := bstep (se 1 (by rfl) ⟨1421519, by rfl⟩ : syracuseStep 1895359 = 2843039) B2843039
theorem B2843045 : Blo 1893435 2843045 := bbase (se 4 (by rfl) ⟨266535, by rfl⟩ : syracuseStep 2843045 = 533071) (by norm_num)
theorem B1895363 : Blo 1893435 1895363 := bstep (se 1 (by rfl) ⟨1421522, by rfl⟩ : syracuseStep 1895363 = 2843045) B2843045
theorem B2398825 : Blo 1893435 2398825 := bbase (se 2 (by rfl) ⟨899559, by rfl⟩ : syracuseStep 2398825 = 1799119) (by norm_num)
theorem B3198433 : Blo 1893435 3198433 := bstep (se 2 (by rfl) ⟨1199412, by rfl⟩ : syracuseStep 3198433 = 2398825) B2398825
theorem B4264577 : Blo 1893435 4264577 := bstep (se 2 (by rfl) ⟨1599216, by rfl⟩ : syracuseStep 4264577 = 3198433) B3198433
theorem B2843051 : Blo 1893435 2843051 := bstep (se 1 (by rfl) ⟨2132288, by rfl⟩ : syracuseStep 2843051 = 4264577) B4264577
theorem B1895367 : Blo 1893435 1895367 := bstep (se 1 (by rfl) ⟨1421525, by rfl⟩ : syracuseStep 1895367 = 2843051) B2843051
theorem B2132293 : Blo 1893435 2132293 := bbase (se 4 (by rfl) ⟨199902, by rfl⟩ : syracuseStep 2132293 = 399805) (by norm_num)
theorem B2843057 : Blo 1893435 2843057 := bstep (se 2 (by rfl) ⟨1066146, by rfl⟩ : syracuseStep 2843057 = 2132293) B2132293
theorem B1895371 : Blo 1893435 1895371 := bstep (se 1 (by rfl) ⟨1421528, by rfl⟩ : syracuseStep 1895371 = 2843057) B2843057
theorem B3598253 : Blo 1893435 3598253 := bbase (se 3 (by rfl) ⟨674672, by rfl⟩ : syracuseStep 3598253 = 1349345) (by norm_num)
theorem B2398835 : Blo 1893435 2398835 := bstep (se 1 (by rfl) ⟨1799126, by rfl⟩ : syracuseStep 2398835 = 3598253) B3598253
theorem B6396893 : Blo 1893435 6396893 := bstep (se 3 (by rfl) ⟨1199417, by rfl⟩ : syracuseStep 6396893 = 2398835) B2398835
theorem B4264595 : Blo 1893435 4264595 := bstep (se 1 (by rfl) ⟨3198446, by rfl⟩ : syracuseStep 4264595 = 6396893) B6396893
theorem B2843063 : Blo 1893435 2843063 := bstep (se 1 (by rfl) ⟨2132297, by rfl⟩ : syracuseStep 2843063 = 4264595) B4264595
theorem B1895375 : Blo 1893435 1895375 := bstep (se 1 (by rfl) ⟨1421531, by rfl⟩ : syracuseStep 1895375 = 2843063) B2843063
theorem B2843069 : Blo 1893435 2843069 := bbase (se 3 (by rfl) ⟨533075, by rfl⟩ : syracuseStep 2843069 = 1066151) (by norm_num)
theorem B1895379 : Blo 1893435 1895379 := bstep (se 1 (by rfl) ⟨1421534, by rfl⟩ : syracuseStep 1895379 = 2843069) B2843069
theorem B4264613 : Blo 1893435 4264613 := bbase (se 4 (by rfl) ⟨399807, by rfl⟩ : syracuseStep 4264613 = 799615) (by norm_num)
theorem B2843075 : Blo 1893435 2843075 := bstep (se 1 (by rfl) ⟨2132306, by rfl⟩ : syracuseStep 2843075 = 4264613) B4264613
theorem B1895383 : Blo 1893435 1895383 := bstep (se 1 (by rfl) ⟨1421537, by rfl⟩ : syracuseStep 1895383 = 2843075) B2843075
theorem B4797701 : Blo 1893435 4797701 := bbase (se 4 (by rfl) ⟨449784, by rfl⟩ : syracuseStep 4797701 = 899569) (by norm_num)
theorem B3198467 : Blo 1893435 3198467 := bstep (se 1 (by rfl) ⟨2398850, by rfl⟩ : syracuseStep 3198467 = 4797701) B4797701
theorem B2132311 : Blo 1893435 2132311 := bstep (se 1 (by rfl) ⟨1599233, by rfl⟩ : syracuseStep 2132311 = 3198467) B3198467
theorem B2843081 : Blo 1893435 2843081 := bstep (se 2 (by rfl) ⟨1066155, by rfl⟩ : syracuseStep 2843081 = 2132311) B2132311
theorem B1895387 : Blo 1893435 1895387 := bstep (se 1 (by rfl) ⟨1421540, by rfl⟩ : syracuseStep 1895387 = 2843081) B2843081
theorem B4048069 : Blo 1893435 4048069 := bbase (se 4 (by rfl) ⟨379506, by rfl⟩ : syracuseStep 4048069 = 759013) (by norm_num)
theorem B5397425 : Blo 1893435 5397425 := bstep (se 2 (by rfl) ⟨2024034, by rfl⟩ : syracuseStep 5397425 = 4048069) B4048069
theorem B3598283 : Blo 1893435 3598283 := bstep (se 1 (by rfl) ⟨2698712, by rfl⟩ : syracuseStep 3598283 = 5397425) B5397425
theorem B9595421 : Blo 1893435 9595421 := bstep (se 3 (by rfl) ⟨1799141, by rfl⟩ : syracuseStep 9595421 = 3598283) B3598283
theorem B6396947 : Blo 1893435 6396947 := bstep (se 1 (by rfl) ⟨4797710, by rfl⟩ : syracuseStep 6396947 = 9595421) B9595421
theorem B4264631 : Blo 1893435 4264631 := bstep (se 1 (by rfl) ⟨3198473, by rfl⟩ : syracuseStep 4264631 = 6396947) B6396947
theorem B2843087 : Blo 1893435 2843087 := bstep (se 1 (by rfl) ⟨2132315, by rfl⟩ : syracuseStep 2843087 = 4264631) B4264631
theorem B1895391 : Blo 1893435 1895391 := bstep (se 1 (by rfl) ⟨1421543, by rfl⟩ : syracuseStep 1895391 = 2843087) B2843087
theorem B2843093 : Blo 1893435 2843093 := bbase (se 7 (by rfl) ⟨33317, by rfl⟩ : syracuseStep 2843093 = 66635) (by norm_num)
theorem B1895395 : Blo 1893435 1895395 := bstep (se 1 (by rfl) ⟨1421546, by rfl⟩ : syracuseStep 1895395 = 2843093) B2843093
theorem B7196597 : Blo 1893435 7196597 := bbase (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) (by norm_num)
theorem B4797731 : Blo 1893435 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B3198487 : Blo 1893435 3198487 := bstep (se 1 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 3198487 = 4797731) B4797731
theorem B4264649 : Blo 1893435 4264649 := bstep (se 2 (by rfl) ⟨1599243, by rfl⟩ : syracuseStep 4264649 = 3198487) B3198487
theorem B2843099 : Blo 1893435 2843099 := bstep (se 1 (by rfl) ⟨2132324, by rfl⟩ : syracuseStep 2843099 = 4264649) B4264649
theorem B1895399 : Blo 1893435 1895399 := bstep (se 1 (by rfl) ⟨1421549, by rfl⟩ : syracuseStep 1895399 = 2843099) B2843099
theorem B2132329 : Blo 1893435 2132329 := bbase (se 2 (by rfl) ⟨799623, by rfl⟩ : syracuseStep 2132329 = 1599247) (by norm_num)
theorem B2843105 : Blo 1893435 2843105 := bstep (se 2 (by rfl) ⟨1066164, by rfl⟩ : syracuseStep 2843105 = 2132329) B2132329
theorem B1895403 : Blo 1893435 1895403 := bstep (se 1 (by rfl) ⟨1421552, by rfl⟩ : syracuseStep 1895403 = 2843105) B2843105
theorem B9726421 : Blo 1893435 9726421 := bbase (se 7 (by rfl) ⟨113981, by rfl⟩ : syracuseStep 9726421 = 227963) (by norm_num)
theorem B12968561 : Blo 1893435 12968561 := bstep (se 2 (by rfl) ⟨4863210, by rfl⟩ : syracuseStep 12968561 = 9726421) B9726421
theorem B8645707 : Blo 1893435 8645707 := bstep (se 1 (by rfl) ⟨6484280, by rfl⟩ : syracuseStep 8645707 = 12968561) B12968561
theorem B11527609 : Blo 1893435 11527609 := bstep (se 2 (by rfl) ⟨4322853, by rfl⟩ : syracuseStep 11527609 = 8645707) B8645707
theorem B15370145 : Blo 1893435 15370145 := bstep (se 2 (by rfl) ⟨5763804, by rfl⟩ : syracuseStep 15370145 = 11527609) B11527609
theorem B10246763 : Blo 1893435 10246763 := bstep (se 1 (by rfl) ⟨7685072, by rfl⟩ : syracuseStep 10246763 = 15370145) B15370145
theorem B6831175 : Blo 1893435 6831175 := bstep (se 1 (by rfl) ⟨5123381, by rfl⟩ : syracuseStep 6831175 = 10246763) B10246763
theorem B9108233 : Blo 1893435 9108233 := bstep (se 2 (by rfl) ⟨3415587, by rfl⟩ : syracuseStep 9108233 = 6831175) B6831175
theorem B6072155 : Blo 1893435 6072155 := bstep (se 1 (by rfl) ⟨4554116, by rfl⟩ : syracuseStep 6072155 = 9108233) B9108233
theorem B4048103 : Blo 1893435 4048103 := bstep (se 1 (by rfl) ⟨3036077, by rfl⟩ : syracuseStep 4048103 = 6072155) B6072155
theorem B10794941 : Blo 1893435 10794941 := bstep (se 3 (by rfl) ⟨2024051, by rfl⟩ : syracuseStep 10794941 = 4048103) B4048103
theorem B7196627 : Blo 1893435 7196627 := bstep (se 1 (by rfl) ⟨5397470, by rfl⟩ : syracuseStep 7196627 = 10794941) B10794941
theorem B4797751 : Blo 1893435 4797751 := bstep (se 1 (by rfl) ⟨3598313, by rfl⟩ : syracuseStep 4797751 = 7196627) B7196627
theorem B6397001 : Blo 1893435 6397001 := bstep (se 2 (by rfl) ⟨2398875, by rfl⟩ : syracuseStep 6397001 = 4797751) B4797751
theorem B4264667 : Blo 1893435 4264667 := bstep (se 1 (by rfl) ⟨3198500, by rfl⟩ : syracuseStep 4264667 = 6397001) B6397001
theorem B2843111 : Blo 1893435 2843111 := bstep (se 1 (by rfl) ⟨2132333, by rfl⟩ : syracuseStep 2843111 = 4264667) B4264667
theorem B1895407 : Blo 1893435 1895407 := bstep (se 1 (by rfl) ⟨1421555, by rfl⟩ : syracuseStep 1895407 = 2843111) B2843111
theorem B2843117 : Blo 1893435 2843117 := bbase (se 3 (by rfl) ⟨533084, by rfl⟩ : syracuseStep 2843117 = 1066169) (by norm_num)
theorem B1895411 : Blo 1893435 1895411 := bstep (se 1 (by rfl) ⟨1421558, by rfl⟩ : syracuseStep 1895411 = 2843117) B2843117
theorem B4264685 : Blo 1893435 4264685 := bbase (se 3 (by rfl) ⟨799628, by rfl⟩ : syracuseStep 4264685 = 1599257) (by norm_num)
theorem B2843123 : Blo 1893435 2843123 := bstep (se 1 (by rfl) ⟨2132342, by rfl⟩ : syracuseStep 2843123 = 4264685) B4264685
theorem B1895415 : Blo 1893435 1895415 := bstep (se 1 (by rfl) ⟨1421561, by rfl⟩ : syracuseStep 1895415 = 2843123) B2843123
theorem B2024065 : Blo 1893435 2024065 := bbase (se 2 (by rfl) ⟨759024, by rfl⟩ : syracuseStep 2024065 = 1518049) (by norm_num)
theorem B2698753 : Blo 1893435 2698753 := bstep (se 2 (by rfl) ⟨1012032, by rfl⟩ : syracuseStep 2698753 = 2024065) B2024065
theorem B3598337 : Blo 1893435 3598337 := bstep (se 2 (by rfl) ⟨1349376, by rfl⟩ : syracuseStep 3598337 = 2698753) B2698753
theorem B2398891 : Blo 1893435 2398891 := bstep (se 1 (by rfl) ⟨1799168, by rfl⟩ : syracuseStep 2398891 = 3598337) B3598337
theorem B3198521 : Blo 1893435 3198521 := bstep (se 2 (by rfl) ⟨1199445, by rfl⟩ : syracuseStep 3198521 = 2398891) B2398891
theorem B2132347 : Blo 1893435 2132347 := bstep (se 1 (by rfl) ⟨1599260, by rfl⟩ : syracuseStep 2132347 = 3198521) B3198521
theorem B2843129 : Blo 1893435 2843129 := bstep (se 2 (by rfl) ⟨1066173, by rfl⟩ : syracuseStep 2843129 = 2132347) B2132347
theorem B1895419 : Blo 1893435 1895419 := bstep (se 1 (by rfl) ⟨1421564, by rfl⟩ : syracuseStep 1895419 = 2843129) B2843129
theorem B3509453 : Blo 1893435 3509453 := bbase (se 3 (by rfl) ⟨658022, by rfl⟩ : syracuseStep 3509453 = 1316045) (by norm_num)
theorem B2339635 : Blo 1893435 2339635 := bstep (se 1 (by rfl) ⟨1754726, by rfl⟩ : syracuseStep 2339635 = 3509453) B3509453
theorem B3119513 : Blo 1893435 3119513 := bstep (se 2 (by rfl) ⟨1169817, by rfl⟩ : syracuseStep 3119513 = 2339635) B2339635
theorem B8318701 : Blo 1893435 8318701 := bstep (se 3 (by rfl) ⟨1559756, by rfl⟩ : syracuseStep 8318701 = 3119513) B3119513
theorem B11091601 : Blo 1893435 11091601 := bstep (se 2 (by rfl) ⟨4159350, by rfl⟩ : syracuseStep 11091601 = 8318701) B8318701
theorem B59155205 : Blo 1893435 59155205 := bstep (se 4 (by rfl) ⟨5545800, by rfl⟩ : syracuseStep 59155205 = 11091601) B11091601
theorem B157747213 : Blo 1893435 157747213 := bstep (se 3 (by rfl) ⟨29577602, by rfl⟩ : syracuseStep 157747213 = 59155205) B59155205
theorem B210329617 : Blo 1893435 210329617 := bstep (se 2 (by rfl) ⟨78873606, by rfl⟩ : syracuseStep 210329617 = 157747213) B157747213
theorem B280439489 : Blo 1893435 280439489 := bstep (se 2 (by rfl) ⟨105164808, by rfl⟩ : syracuseStep 280439489 = 210329617) B210329617
theorem B186959659 : Blo 1893435 186959659 := bstep (se 1 (by rfl) ⟨140219744, by rfl⟩ : syracuseStep 186959659 = 280439489) B280439489
theorem B249279545 : Blo 1893435 249279545 := bstep (se 2 (by rfl) ⟨93479829, by rfl⟩ : syracuseStep 249279545 = 186959659) B186959659
theorem B664745453 : Blo 1893435 664745453 := bstep (se 3 (by rfl) ⟨124639772, by rfl⟩ : syracuseStep 664745453 = 249279545) B249279545
theorem B443163635 : Blo 1893435 443163635 := bstep (se 1 (by rfl) ⟨332372726, by rfl⟩ : syracuseStep 443163635 = 664745453) B664745453
theorem B295442423 : Blo 1893435 295442423 := bstep (se 1 (by rfl) ⟨221581817, by rfl⟩ : syracuseStep 295442423 = 443163635) B443163635
theorem B196961615 : Blo 1893435 196961615 := bstep (se 1 (by rfl) ⟨147721211, by rfl⟩ : syracuseStep 196961615 = 295442423) B295442423
theorem B131307743 : Blo 1893435 131307743 := bstep (se 1 (by rfl) ⟨98480807, by rfl⟩ : syracuseStep 131307743 = 196961615) B196961615
theorem B87538495 : Blo 1893435 87538495 := bstep (se 1 (by rfl) ⟨65653871, by rfl⟩ : syracuseStep 87538495 = 131307743) B131307743
theorem B116717993 : Blo 1893435 116717993 := bstep (se 2 (by rfl) ⟨43769247, by rfl⟩ : syracuseStep 116717993 = 87538495) B87538495
theorem B77811995 : Blo 1893435 77811995 := bstep (se 1 (by rfl) ⟨58358996, by rfl⟩ : syracuseStep 77811995 = 116717993) B116717993
theorem B51874663 : Blo 1893435 51874663 := bstep (se 1 (by rfl) ⟨38905997, by rfl⟩ : syracuseStep 51874663 = 77811995) B77811995
theorem B69166217 : Blo 1893435 69166217 := bstep (se 2 (by rfl) ⟨25937331, by rfl⟩ : syracuseStep 69166217 = 51874663) B51874663
theorem B46110811 : Blo 1893435 46110811 := bstep (se 1 (by rfl) ⟨34583108, by rfl⟩ : syracuseStep 46110811 = 69166217) B69166217
theorem B61481081 : Blo 1893435 61481081 := bstep (se 2 (by rfl) ⟨23055405, by rfl⟩ : syracuseStep 61481081 = 46110811) B46110811
theorem B40987387 : Blo 1893435 40987387 := bstep (se 1 (by rfl) ⟨30740540, by rfl⟩ : syracuseStep 40987387 = 61481081) B61481081
theorem B54649849 : Blo 1893435 54649849 := bstep (se 2 (by rfl) ⟨20493693, by rfl⟩ : syracuseStep 54649849 = 40987387) B40987387
theorem B72866465 : Blo 1893435 72866465 := bstep (se 2 (by rfl) ⟨27324924, by rfl⟩ : syracuseStep 72866465 = 54649849) B54649849
theorem B48577643 : Blo 1893435 48577643 := bstep (se 1 (by rfl) ⟨36433232, by rfl⟩ : syracuseStep 48577643 = 72866465) B72866465
theorem B32385095 : Blo 1893435 32385095 := bstep (se 1 (by rfl) ⟨24288821, by rfl⟩ : syracuseStep 32385095 = 48577643) B48577643
theorem B21590063 : Blo 1893435 21590063 := bstep (se 1 (by rfl) ⟨16192547, by rfl⟩ : syracuseStep 21590063 = 32385095) B32385095
theorem B14393375 : Blo 1893435 14393375 := bstep (se 1 (by rfl) ⟨10795031, by rfl⟩ : syracuseStep 14393375 = 21590063) B21590063
theorem B9595583 : Blo 1893435 9595583 := bstep (se 1 (by rfl) ⟨7196687, by rfl⟩ : syracuseStep 9595583 = 14393375) B14393375
theorem B6397055 : Blo 1893435 6397055 := bstep (se 1 (by rfl) ⟨4797791, by rfl⟩ : syracuseStep 6397055 = 9595583) B9595583
theorem B4264703 : Blo 1893435 4264703 := bstep (se 1 (by rfl) ⟨3198527, by rfl⟩ : syracuseStep 4264703 = 6397055) B6397055
theorem B2843135 : Blo 1893435 2843135 := bstep (se 1 (by rfl) ⟨2132351, by rfl⟩ : syracuseStep 2843135 = 4264703) B4264703
theorem B1895423 : Blo 1893435 1895423 := bstep (se 1 (by rfl) ⟨1421567, by rfl⟩ : syracuseStep 1895423 = 2843135) B2843135
theorem B2843141 : Blo 1893435 2843141 := bbase (se 4 (by rfl) ⟨266544, by rfl⟩ : syracuseStep 2843141 = 533089) (by norm_num)
theorem B1895427 : Blo 1893435 1895427 := bstep (se 1 (by rfl) ⟨1421570, by rfl⟩ : syracuseStep 1895427 = 2843141) B2843141
theorem B3198541 : Blo 1893435 3198541 := bbase (se 3 (by rfl) ⟨599726, by rfl⟩ : syracuseStep 3198541 = 1199453) (by norm_num)
theorem B4264721 : Blo 1893435 4264721 := bstep (se 2 (by rfl) ⟨1599270, by rfl⟩ : syracuseStep 4264721 = 3198541) B3198541
theorem B2843147 : Blo 1893435 2843147 := bstep (se 1 (by rfl) ⟨2132360, by rfl⟩ : syracuseStep 2843147 = 4264721) B4264721
theorem B1895431 : Blo 1893435 1895431 := bstep (se 1 (by rfl) ⟨1421573, by rfl⟩ : syracuseStep 1895431 = 2843147) B2843147
theorem B2132365 : Blo 1893435 2132365 := bbase (se 3 (by rfl) ⟨399818, by rfl⟩ : syracuseStep 2132365 = 799637) (by norm_num)
theorem B2843153 : Blo 1893435 2843153 := bstep (se 2 (by rfl) ⟨1066182, by rfl⟩ : syracuseStep 2843153 = 2132365) B2132365
theorem B1895435 : Blo 1893435 1895435 := bstep (se 1 (by rfl) ⟨1421576, by rfl⟩ : syracuseStep 1895435 = 2843153) B2843153
theorem C0 (j : ℕ) (h1 : 473358 ≤ j) (h2 : j ≤ 473858) : Blo 1893435 (4 * j + 3) := by
  interval_cases j
  · exact B1893435
  · exact B1893439
  · exact B1893443
  · exact B1893447
  · exact B1893451
  · exact B1893455
  · exact B1893459
  · exact B1893463
  · exact B1893467
  · exact B1893471
  · exact B1893475
  · exact B1893479
  · exact B1893483
  · exact B1893487
  · exact B1893491
  · exact B1893495
  · exact B1893499
  · exact B1893503
  · exact B1893507
  · exact B1893511
  · exact B1893515
  · exact B1893519
  · exact B1893523
  · exact B1893527
  · exact B1893531
  · exact B1893535
  · exact B1893539
  · exact B1893543
  · exact B1893547
  · exact B1893551
  · exact B1893555
  · exact B1893559
  · exact B1893563
  · exact B1893567
  · exact B1893571
  · exact B1893575
  · exact B1893579
  · exact B1893583
  · exact B1893587
  · exact B1893591
  · exact B1893595
  · exact B1893599
  · exact B1893603
  · exact B1893607
  · exact B1893611
  · exact B1893615
  · exact B1893619
  · exact B1893623
  · exact B1893627
  · exact B1893631
  · exact B1893635
  · exact B1893639
  · exact B1893643
  · exact B1893647
  · exact B1893651
  · exact B1893655
  · exact B1893659
  · exact B1893663
  · exact B1893667
  · exact B1893671
  · exact B1893675
  · exact B1893679
  · exact B1893683
  · exact B1893687
  · exact B1893691
  · exact B1893695
  · exact B1893699
  · exact B1893703
  · exact B1893707
  · exact B1893711
  · exact B1893715
  · exact B1893719
  · exact B1893723
  · exact B1893727
  · exact B1893731
  · exact B1893735
  · exact B1893739
  · exact B1893743
  · exact B1893747
  · exact B1893751
  · exact B1893755
  · exact B1893759
  · exact B1893763
  · exact B1893767
  · exact B1893771
  · exact B1893775
  · exact B1893779
  · exact B1893783
  · exact B1893787
  · exact B1893791
  · exact B1893795
  · exact B1893799
  · exact B1893803
  · exact B1893807
  · exact B1893811
  · exact B1893815
  · exact B1893819
  · exact B1893823
  · exact B1893827
  · exact B1893831
  · exact B1893835
  · exact B1893839
  · exact B1893843
  · exact B1893847
  · exact B1893851
  · exact B1893855
  · exact B1893859
  · exact B1893863
  · exact B1893867
  · exact B1893871
  · exact B1893875
  · exact B1893879
  · exact B1893883
  · exact B1893887
  · exact B1893891
  · exact B1893895
  · exact B1893899
  · exact B1893903
  · exact B1893907
  · exact B1893911
  · exact B1893915
  · exact B1893919
  · exact B1893923
  · exact B1893927
  · exact B1893931
  · exact B1893935
  · exact B1893939
  · exact B1893943
  · exact B1893947
  · exact B1893951
  · exact B1893955
  · exact B1893959
  · exact B1893963
  · exact B1893967
  · exact B1893971
  · exact B1893975
  · exact B1893979
  · exact B1893983
  · exact B1893987
  · exact B1893991
  · exact B1893995
  · exact B1893999
  · exact B1894003
  · exact B1894007
  · exact B1894011
  · exact B1894015
  · exact B1894019
  · exact B1894023
  · exact B1894027
  · exact B1894031
  · exact B1894035
  · exact B1894039
  · exact B1894043
  · exact B1894047
  · exact B1894051
  · exact B1894055
  · exact B1894059
  · exact B1894063
  · exact B1894067
  · exact B1894071
  · exact B1894075
  · exact B1894079
  · exact B1894083
  · exact B1894087
  · exact B1894091
  · exact B1894095
  · exact B1894099
  · exact B1894103
  · exact B1894107
  · exact B1894111
  · exact B1894115
  · exact B1894119
  · exact B1894123
  · exact B1894127
  · exact B1894131
  · exact B1894135
  · exact B1894139
  · exact B1894143
  · exact B1894147
  · exact B1894151
  · exact B1894155
  · exact B1894159
  · exact B1894163
  · exact B1894167
  · exact B1894171
  · exact B1894175
  · exact B1894179
  · exact B1894183
  · exact B1894187
  · exact B1894191
  · exact B1894195
  · exact B1894199
  · exact B1894203
  · exact B1894207
  · exact B1894211
  · exact B1894215
  · exact B1894219
  · exact B1894223
  · exact B1894227
  · exact B1894231
  · exact B1894235
  · exact B1894239
  · exact B1894243
  · exact B1894247
  · exact B1894251
  · exact B1894255
  · exact B1894259
  · exact B1894263
  · exact B1894267
  · exact B1894271
  · exact B1894275
  · exact B1894279
  · exact B1894283
  · exact B1894287
  · exact B1894291
  · exact B1894295
  · exact B1894299
  · exact B1894303
  · exact B1894307
  · exact B1894311
  · exact B1894315
  · exact B1894319
  · exact B1894323
  · exact B1894327
  · exact B1894331
  · exact B1894335
  · exact B1894339
  · exact B1894343
  · exact B1894347
  · exact B1894351
  · exact B1894355
  · exact B1894359
  · exact B1894363
  · exact B1894367
  · exact B1894371
  · exact B1894375
  · exact B1894379
  · exact B1894383
  · exact B1894387
  · exact B1894391
  · exact B1894395
  · exact B1894399
  · exact B1894403
  · exact B1894407
  · exact B1894411
  · exact B1894415
  · exact B1894419
  · exact B1894423
  · exact B1894427
  · exact B1894431
  · exact B1894435
  · exact B1894439
  · exact B1894443
  · exact B1894447
  · exact B1894451
  · exact B1894455
  · exact B1894459
  · exact B1894463
  · exact B1894467
  · exact B1894471
  · exact B1894475
  · exact B1894479
  · exact B1894483
  · exact B1894487
  · exact B1894491
  · exact B1894495
  · exact B1894499
  · exact B1894503
  · exact B1894507
  · exact B1894511
  · exact B1894515
  · exact B1894519
  · exact B1894523
  · exact B1894527
  · exact B1894531
  · exact B1894535
  · exact B1894539
  · exact B1894543
  · exact B1894547
  · exact B1894551
  · exact B1894555
  · exact B1894559
  · exact B1894563
  · exact B1894567
  · exact B1894571
  · exact B1894575
  · exact B1894579
  · exact B1894583
  · exact B1894587
  · exact B1894591
  · exact B1894595
  · exact B1894599
  · exact B1894603
  · exact B1894607
  · exact B1894611
  · exact B1894615
  · exact B1894619
  · exact B1894623
  · exact B1894627
  · exact B1894631
  · exact B1894635
  · exact B1894639
  · exact B1894643
  · exact B1894647
  · exact B1894651
  · exact B1894655
  · exact B1894659
  · exact B1894663
  · exact B1894667
  · exact B1894671
  · exact B1894675
  · exact B1894679
  · exact B1894683
  · exact B1894687
  · exact B1894691
  · exact B1894695
  · exact B1894699
  · exact B1894703
  · exact B1894707
  · exact B1894711
  · exact B1894715
  · exact B1894719
  · exact B1894723
  · exact B1894727
  · exact B1894731
  · exact B1894735
  · exact B1894739
  · exact B1894743
  · exact B1894747
  · exact B1894751
  · exact B1894755
  · exact B1894759
  · exact B1894763
  · exact B1894767
  · exact B1894771
  · exact B1894775
  · exact B1894779
  · exact B1894783
  · exact B1894787
  · exact B1894791
  · exact B1894795
  · exact B1894799
  · exact B1894803
  · exact B1894807
  · exact B1894811
  · exact B1894815
  · exact B1894819
  · exact B1894823
  · exact B1894827
  · exact B1894831
  · exact B1894835
  · exact B1894839
  · exact B1894843
  · exact B1894847
  · exact B1894851
  · exact B1894855
  · exact B1894859
  · exact B1894863
  · exact B1894867
  · exact B1894871
  · exact B1894875
  · exact B1894879
  · exact B1894883
  · exact B1894887
  · exact B1894891
  · exact B1894895
  · exact B1894899
  · exact B1894903
  · exact B1894907
  · exact B1894911
  · exact B1894915
  · exact B1894919
  · exact B1894923
  · exact B1894927
  · exact B1894931
  · exact B1894935
  · exact B1894939
  · exact B1894943
  · exact B1894947
  · exact B1894951
  · exact B1894955
  · exact B1894959
  · exact B1894963
  · exact B1894967
  · exact B1894971
  · exact B1894975
  · exact B1894979
  · exact B1894983
  · exact B1894987
  · exact B1894991
  · exact B1894995
  · exact B1894999
  · exact B1895003
  · exact B1895007
  · exact B1895011
  · exact B1895015
  · exact B1895019
  · exact B1895023
  · exact B1895027
  · exact B1895031
  · exact B1895035
  · exact B1895039
  · exact B1895043
  · exact B1895047
  · exact B1895051
  · exact B1895055
  · exact B1895059
  · exact B1895063
  · exact B1895067
  · exact B1895071
  · exact B1895075
  · exact B1895079
  · exact B1895083
  · exact B1895087
  · exact B1895091
  · exact B1895095
  · exact B1895099
  · exact B1895103
  · exact B1895107
  · exact B1895111
  · exact B1895115
  · exact B1895119
  · exact B1895123
  · exact B1895127
  · exact B1895131
  · exact B1895135
  · exact B1895139
  · exact B1895143
  · exact B1895147
  · exact B1895151
  · exact B1895155
  · exact B1895159
  · exact B1895163
  · exact B1895167
  · exact B1895171
  · exact B1895175
  · exact B1895179
  · exact B1895183
  · exact B1895187
  · exact B1895191
  · exact B1895195
  · exact B1895199
  · exact B1895203
  · exact B1895207
  · exact B1895211
  · exact B1895215
  · exact B1895219
  · exact B1895223
  · exact B1895227
  · exact B1895231
  · exact B1895235
  · exact B1895239
  · exact B1895243
  · exact B1895247
  · exact B1895251
  · exact B1895255
  · exact B1895259
  · exact B1895263
  · exact B1895267
  · exact B1895271
  · exact B1895275
  · exact B1895279
  · exact B1895283
  · exact B1895287
  · exact B1895291
  · exact B1895295
  · exact B1895299
  · exact B1895303
  · exact B1895307
  · exact B1895311
  · exact B1895315
  · exact B1895319
  · exact B1895323
  · exact B1895327
  · exact B1895331
  · exact B1895335
  · exact B1895339
  · exact B1895343
  · exact B1895347
  · exact B1895351
  · exact B1895355
  · exact B1895359
  · exact B1895363
  · exact B1895367
  · exact B1895371
  · exact B1895375
  · exact B1895379
  · exact B1895383
  · exact B1895387
  · exact B1895391
  · exact B1895395
  · exact B1895399
  · exact B1895403
  · exact B1895407
  · exact B1895411
  · exact B1895415
  · exact B1895419
  · exact B1895423
  · exact B1895427
  · exact B1895431
  · exact B1895435
theorem solution (m : ℕ) (hlo : 1893435 ≤ m) (hhi : m ≤ 1895435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 473358 ≤ j := by omega
    have hj2 : j ≤ 473858 := by omega
    have hb : Blo 1893435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
