-- Prove2me | solution 1 for syracuse_descends_range_2053435_2055435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:30.186693+00:00
-- url     : https://prove2.me/submissions/8b05923b-e55f-45eb-bf0a-9af82d45f276

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

theorem B3465173 : Blo 2053435 3465173 := bbase (se 7 (by rfl) ⟨40607, by rfl⟩ : syracuseStep 3465173 = 81215) (by norm_num)
theorem B2310115 : Blo 2053435 2310115 := bstep (se 1 (by rfl) ⟨1732586, by rfl⟩ : syracuseStep 2310115 = 3465173) B3465173
theorem B3080153 : Blo 2053435 3080153 := bstep (se 2 (by rfl) ⟨1155057, by rfl⟩ : syracuseStep 3080153 = 2310115) B2310115
theorem B2053435 : Blo 2053435 2053435 := bstep (se 1 (by rfl) ⟨1540076, by rfl⟩ : syracuseStep 2053435 = 3080153) B3080153
theorem B8771237 : Blo 2053435 8771237 := bbase (se 4 (by rfl) ⟨822303, by rfl⟩ : syracuseStep 8771237 = 1644607) (by norm_num)
theorem B5847491 : Blo 2053435 5847491 := bstep (se 1 (by rfl) ⟨4385618, by rfl⟩ : syracuseStep 5847491 = 8771237) B8771237
theorem B15593309 : Blo 2053435 15593309 := bstep (se 3 (by rfl) ⟨2923745, by rfl⟩ : syracuseStep 15593309 = 5847491) B5847491
theorem B10395539 : Blo 2053435 10395539 := bstep (se 1 (by rfl) ⟨7796654, by rfl⟩ : syracuseStep 10395539 = 15593309) B15593309
theorem B6930359 : Blo 2053435 6930359 := bstep (se 1 (by rfl) ⟨5197769, by rfl⟩ : syracuseStep 6930359 = 10395539) B10395539
theorem B4620239 : Blo 2053435 4620239 := bstep (se 1 (by rfl) ⟨3465179, by rfl⟩ : syracuseStep 4620239 = 6930359) B6930359
theorem B3080159 : Blo 2053435 3080159 := bstep (se 1 (by rfl) ⟨2310119, by rfl⟩ : syracuseStep 3080159 = 4620239) B4620239
theorem B2053439 : Blo 2053435 2053439 := bstep (se 1 (by rfl) ⟨1540079, by rfl⟩ : syracuseStep 2053439 = 3080159) B3080159
theorem B3080165 : Blo 2053435 3080165 := bbase (se 4 (by rfl) ⟨288765, by rfl⟩ : syracuseStep 3080165 = 577531) (by norm_num)
theorem B2053443 : Blo 2053435 2053443 := bstep (se 1 (by rfl) ⟨1540082, by rfl⟩ : syracuseStep 2053443 = 3080165) B3080165
theorem B14801525 : Blo 2053435 14801525 := bbase (se 5 (by rfl) ⟨693821, by rfl⟩ : syracuseStep 14801525 = 1387643) (by norm_num)
theorem B9867683 : Blo 2053435 9867683 := bstep (se 1 (by rfl) ⟨7400762, by rfl⟩ : syracuseStep 9867683 = 14801525) B14801525
theorem B6578455 : Blo 2053435 6578455 := bstep (se 1 (by rfl) ⟨4933841, by rfl⟩ : syracuseStep 6578455 = 9867683) B9867683
theorem B8771273 : Blo 2053435 8771273 := bstep (se 2 (by rfl) ⟨3289227, by rfl⟩ : syracuseStep 8771273 = 6578455) B6578455
theorem B5847515 : Blo 2053435 5847515 := bstep (se 1 (by rfl) ⟨4385636, by rfl⟩ : syracuseStep 5847515 = 8771273) B8771273
theorem B3898343 : Blo 2053435 3898343 := bstep (se 1 (by rfl) ⟨2923757, by rfl⟩ : syracuseStep 3898343 = 5847515) B5847515
theorem B2598895 : Blo 2053435 2598895 := bstep (se 1 (by rfl) ⟨1949171, by rfl⟩ : syracuseStep 2598895 = 3898343) B3898343
theorem B3465193 : Blo 2053435 3465193 := bstep (se 2 (by rfl) ⟨1299447, by rfl⟩ : syracuseStep 3465193 = 2598895) B2598895
theorem B4620257 : Blo 2053435 4620257 := bstep (se 2 (by rfl) ⟨1732596, by rfl⟩ : syracuseStep 4620257 = 3465193) B3465193
theorem B3080171 : Blo 2053435 3080171 := bstep (se 1 (by rfl) ⟨2310128, by rfl⟩ : syracuseStep 3080171 = 4620257) B4620257
theorem B2053447 : Blo 2053435 2053447 := bstep (se 1 (by rfl) ⟨1540085, by rfl⟩ : syracuseStep 2053447 = 3080171) B3080171
theorem B2310133 : Blo 2053435 2310133 := bbase (se 5 (by rfl) ⟨108287, by rfl⟩ : syracuseStep 2310133 = 216575) (by norm_num)
theorem B3080177 : Blo 2053435 3080177 := bstep (se 2 (by rfl) ⟨1155066, by rfl⟩ : syracuseStep 3080177 = 2310133) B2310133
theorem B2053451 : Blo 2053435 2053451 := bstep (se 1 (by rfl) ⟨1540088, by rfl⟩ : syracuseStep 2053451 = 3080177) B3080177
theorem B2598905 : Blo 2053435 2598905 := bbase (se 2 (by rfl) ⟨974589, by rfl⟩ : syracuseStep 2598905 = 1949179) (by norm_num)
theorem B6930413 : Blo 2053435 6930413 := bstep (se 3 (by rfl) ⟨1299452, by rfl⟩ : syracuseStep 6930413 = 2598905) B2598905
theorem B4620275 : Blo 2053435 4620275 := bstep (se 1 (by rfl) ⟨3465206, by rfl⟩ : syracuseStep 4620275 = 6930413) B6930413
theorem B3080183 : Blo 2053435 3080183 := bstep (se 1 (by rfl) ⟨2310137, by rfl⟩ : syracuseStep 3080183 = 4620275) B4620275
theorem B2053455 : Blo 2053435 2053455 := bstep (se 1 (by rfl) ⟨1540091, by rfl⟩ : syracuseStep 2053455 = 3080183) B3080183
theorem B3080189 : Blo 2053435 3080189 := bbase (se 3 (by rfl) ⟨577535, by rfl⟩ : syracuseStep 3080189 = 1155071) (by norm_num)
theorem B2053459 : Blo 2053435 2053459 := bstep (se 1 (by rfl) ⟨1540094, by rfl⟩ : syracuseStep 2053459 = 3080189) B3080189
theorem B4620293 : Blo 2053435 4620293 := bbase (se 4 (by rfl) ⟨433152, by rfl⟩ : syracuseStep 4620293 = 866305) (by norm_num)
theorem B3080195 : Blo 2053435 3080195 := bstep (se 1 (by rfl) ⟨2310146, by rfl⟩ : syracuseStep 3080195 = 4620293) B4620293
theorem B2053463 : Blo 2053435 2053463 := bstep (se 1 (by rfl) ⟨1540097, by rfl⟩ : syracuseStep 2053463 = 3080195) B3080195
theorem B3898381 : Blo 2053435 3898381 := bbase (se 3 (by rfl) ⟨730946, by rfl⟩ : syracuseStep 3898381 = 1461893) (by norm_num)
theorem B5197841 : Blo 2053435 5197841 := bstep (se 2 (by rfl) ⟨1949190, by rfl⟩ : syracuseStep 5197841 = 3898381) B3898381
theorem B3465227 : Blo 2053435 3465227 := bstep (se 1 (by rfl) ⟨2598920, by rfl⟩ : syracuseStep 3465227 = 5197841) B5197841
theorem B2310151 : Blo 2053435 2310151 := bstep (se 1 (by rfl) ⟨1732613, by rfl⟩ : syracuseStep 2310151 = 3465227) B3465227
theorem B3080201 : Blo 2053435 3080201 := bstep (se 2 (by rfl) ⟨1155075, by rfl⟩ : syracuseStep 3080201 = 2310151) B2310151
theorem B2053467 : Blo 2053435 2053467 := bstep (se 1 (by rfl) ⟨1540100, by rfl⟩ : syracuseStep 2053467 = 3080201) B3080201
theorem B10395701 : Blo 2053435 10395701 := bbase (se 5 (by rfl) ⟨487298, by rfl⟩ : syracuseStep 10395701 = 974597) (by norm_num)
theorem B6930467 : Blo 2053435 6930467 := bstep (se 1 (by rfl) ⟨5197850, by rfl⟩ : syracuseStep 6930467 = 10395701) B10395701
theorem B4620311 : Blo 2053435 4620311 := bstep (se 1 (by rfl) ⟨3465233, by rfl⟩ : syracuseStep 4620311 = 6930467) B6930467
theorem B3080207 : Blo 2053435 3080207 := bstep (se 1 (by rfl) ⟨2310155, by rfl⟩ : syracuseStep 3080207 = 4620311) B4620311
theorem B2053471 : Blo 2053435 2053471 := bstep (se 1 (by rfl) ⟨1540103, by rfl⟩ : syracuseStep 2053471 = 3080207) B3080207
theorem B3080213 : Blo 2053435 3080213 := bbase (se 6 (by rfl) ⟨72192, by rfl⟩ : syracuseStep 3080213 = 144385) (by norm_num)
theorem B2053475 : Blo 2053435 2053475 := bstep (se 1 (by rfl) ⟨1540106, by rfl⟩ : syracuseStep 2053475 = 3080213) B3080213
theorem B3122245 : Blo 2053435 3122245 := bbase (se 4 (by rfl) ⟨292710, by rfl⟩ : syracuseStep 3122245 = 585421) (by norm_num)
theorem B16651973 : Blo 2053435 16651973 := bstep (se 4 (by rfl) ⟨1561122, by rfl⟩ : syracuseStep 16651973 = 3122245) B3122245
theorem B11101315 : Blo 2053435 11101315 := bstep (se 1 (by rfl) ⟨8325986, by rfl⟩ : syracuseStep 11101315 = 16651973) B16651973
theorem B14801753 : Blo 2053435 14801753 := bstep (se 2 (by rfl) ⟨5550657, by rfl⟩ : syracuseStep 14801753 = 11101315) B11101315
theorem B9867835 : Blo 2053435 9867835 := bstep (se 1 (by rfl) ⟨7400876, by rfl⟩ : syracuseStep 9867835 = 14801753) B14801753
theorem B13157113 : Blo 2053435 13157113 := bstep (se 2 (by rfl) ⟨4933917, by rfl⟩ : syracuseStep 13157113 = 9867835) B9867835
theorem B17542817 : Blo 2053435 17542817 := bstep (se 2 (by rfl) ⟨6578556, by rfl⟩ : syracuseStep 17542817 = 13157113) B13157113
theorem B11695211 : Blo 2053435 11695211 := bstep (se 1 (by rfl) ⟨8771408, by rfl⟩ : syracuseStep 11695211 = 17542817) B17542817
theorem B7796807 : Blo 2053435 7796807 := bstep (se 1 (by rfl) ⟨5847605, by rfl⟩ : syracuseStep 7796807 = 11695211) B11695211
theorem B5197871 : Blo 2053435 5197871 := bstep (se 1 (by rfl) ⟨3898403, by rfl⟩ : syracuseStep 5197871 = 7796807) B7796807
theorem B3465247 : Blo 2053435 3465247 := bstep (se 1 (by rfl) ⟨2598935, by rfl⟩ : syracuseStep 3465247 = 5197871) B5197871
theorem B4620329 : Blo 2053435 4620329 := bstep (se 2 (by rfl) ⟨1732623, by rfl⟩ : syracuseStep 4620329 = 3465247) B3465247
theorem B3080219 : Blo 2053435 3080219 := bstep (se 1 (by rfl) ⟨2310164, by rfl⟩ : syracuseStep 3080219 = 4620329) B4620329
theorem B2053479 : Blo 2053435 2053479 := bstep (se 1 (by rfl) ⟨1540109, by rfl⟩ : syracuseStep 2053479 = 3080219) B3080219
theorem B2310169 : Blo 2053435 2310169 := bbase (se 2 (by rfl) ⟨866313, by rfl⟩ : syracuseStep 2310169 = 1732627) (by norm_num)
theorem B3080225 : Blo 2053435 3080225 := bstep (se 2 (by rfl) ⟨1155084, by rfl⟩ : syracuseStep 3080225 = 2310169) B2310169
theorem B2053483 : Blo 2053435 2053483 := bstep (se 1 (by rfl) ⟨1540112, by rfl⟩ : syracuseStep 2053483 = 3080225) B3080225
theorem B7796837 : Blo 2053435 7796837 := bbase (se 4 (by rfl) ⟨730953, by rfl⟩ : syracuseStep 7796837 = 1461907) (by norm_num)
theorem B5197891 : Blo 2053435 5197891 := bstep (se 1 (by rfl) ⟨3898418, by rfl⟩ : syracuseStep 5197891 = 7796837) B7796837
theorem B6930521 : Blo 2053435 6930521 := bstep (se 2 (by rfl) ⟨2598945, by rfl⟩ : syracuseStep 6930521 = 5197891) B5197891
theorem B4620347 : Blo 2053435 4620347 := bstep (se 1 (by rfl) ⟨3465260, by rfl⟩ : syracuseStep 4620347 = 6930521) B6930521
theorem B3080231 : Blo 2053435 3080231 := bstep (se 1 (by rfl) ⟨2310173, by rfl⟩ : syracuseStep 3080231 = 4620347) B4620347
theorem B2053487 : Blo 2053435 2053487 := bstep (se 1 (by rfl) ⟨1540115, by rfl⟩ : syracuseStep 2053487 = 3080231) B3080231
theorem B3080237 : Blo 2053435 3080237 := bbase (se 3 (by rfl) ⟨577544, by rfl⟩ : syracuseStep 3080237 = 1155089) (by norm_num)
theorem B2053491 : Blo 2053435 2053491 := bstep (se 1 (by rfl) ⟨1540118, by rfl⟩ : syracuseStep 2053491 = 3080237) B3080237
theorem B4620365 : Blo 2053435 4620365 := bbase (se 3 (by rfl) ⟨866318, by rfl⟩ : syracuseStep 4620365 = 1732637) (by norm_num)
theorem B3080243 : Blo 2053435 3080243 := bstep (se 1 (by rfl) ⟨2310182, by rfl⟩ : syracuseStep 3080243 = 4620365) B4620365
theorem B2053495 : Blo 2053435 2053495 := bstep (se 1 (by rfl) ⟨1540121, by rfl⟩ : syracuseStep 2053495 = 3080243) B3080243
theorem B2598961 : Blo 2053435 2598961 := bbase (se 2 (by rfl) ⟨974610, by rfl⟩ : syracuseStep 2598961 = 1949221) (by norm_num)
theorem B3465281 : Blo 2053435 3465281 := bstep (se 2 (by rfl) ⟨1299480, by rfl⟩ : syracuseStep 3465281 = 2598961) B2598961
theorem B2310187 : Blo 2053435 2310187 := bstep (se 1 (by rfl) ⟨1732640, by rfl⟩ : syracuseStep 2310187 = 3465281) B3465281
theorem B3080249 : Blo 2053435 3080249 := bstep (se 2 (by rfl) ⟨1155093, by rfl⟩ : syracuseStep 3080249 = 2310187) B2310187
theorem B2053499 : Blo 2053435 2053499 := bstep (se 1 (by rfl) ⟨1540124, by rfl⟩ : syracuseStep 2053499 = 3080249) B3080249
theorem B2081521 : Blo 2053435 2081521 := bbase (se 2 (by rfl) ⟨780570, by rfl⟩ : syracuseStep 2081521 = 1561141) (by norm_num)
theorem B11101445 : Blo 2053435 11101445 := bstep (se 4 (by rfl) ⟨1040760, by rfl⟩ : syracuseStep 11101445 = 2081521) B2081521
theorem B7400963 : Blo 2053435 7400963 := bstep (se 1 (by rfl) ⟨5550722, by rfl⟩ : syracuseStep 7400963 = 11101445) B11101445
theorem B4933975 : Blo 2053435 4933975 := bstep (se 1 (by rfl) ⟨3700481, by rfl⟩ : syracuseStep 4933975 = 7400963) B7400963
theorem B6578633 : Blo 2053435 6578633 := bstep (se 2 (by rfl) ⟨2466987, by rfl⟩ : syracuseStep 6578633 = 4933975) B4933975
theorem B4385755 : Blo 2053435 4385755 := bstep (se 1 (by rfl) ⟨3289316, by rfl⟩ : syracuseStep 4385755 = 6578633) B6578633
theorem B23390693 : Blo 2053435 23390693 := bstep (se 4 (by rfl) ⟨2192877, by rfl⟩ : syracuseStep 23390693 = 4385755) B4385755
theorem B15593795 : Blo 2053435 15593795 := bstep (se 1 (by rfl) ⟨11695346, by rfl⟩ : syracuseStep 15593795 = 23390693) B23390693
theorem B10395863 : Blo 2053435 10395863 := bstep (se 1 (by rfl) ⟨7796897, by rfl⟩ : syracuseStep 10395863 = 15593795) B15593795
theorem B6930575 : Blo 2053435 6930575 := bstep (se 1 (by rfl) ⟨5197931, by rfl⟩ : syracuseStep 6930575 = 10395863) B10395863
theorem B4620383 : Blo 2053435 4620383 := bstep (se 1 (by rfl) ⟨3465287, by rfl⟩ : syracuseStep 4620383 = 6930575) B6930575
theorem B3080255 : Blo 2053435 3080255 := bstep (se 1 (by rfl) ⟨2310191, by rfl⟩ : syracuseStep 3080255 = 4620383) B4620383
theorem B2053503 : Blo 2053435 2053503 := bstep (se 1 (by rfl) ⟨1540127, by rfl⟩ : syracuseStep 2053503 = 3080255) B3080255
theorem B3080261 : Blo 2053435 3080261 := bbase (se 4 (by rfl) ⟨288774, by rfl⟩ : syracuseStep 3080261 = 577549) (by norm_num)
theorem B2053507 : Blo 2053435 2053507 := bstep (se 1 (by rfl) ⟨1540130, by rfl⟩ : syracuseStep 2053507 = 3080261) B3080261
theorem B3465301 : Blo 2053435 3465301 := bbase (se 8 (by rfl) ⟨20304, by rfl⟩ : syracuseStep 3465301 = 40609) (by norm_num)
theorem B4620401 : Blo 2053435 4620401 := bstep (se 2 (by rfl) ⟨1732650, by rfl⟩ : syracuseStep 4620401 = 3465301) B3465301
theorem B3080267 : Blo 2053435 3080267 := bstep (se 1 (by rfl) ⟨2310200, by rfl⟩ : syracuseStep 3080267 = 4620401) B4620401
theorem B2053511 : Blo 2053435 2053511 := bstep (se 1 (by rfl) ⟨1540133, by rfl⟩ : syracuseStep 2053511 = 3080267) B3080267
theorem B2310205 : Blo 2053435 2310205 := bbase (se 3 (by rfl) ⟨433163, by rfl⟩ : syracuseStep 2310205 = 866327) (by norm_num)
theorem B3080273 : Blo 2053435 3080273 := bstep (se 2 (by rfl) ⟨1155102, by rfl⟩ : syracuseStep 3080273 = 2310205) B2310205
theorem B2053515 : Blo 2053435 2053515 := bstep (se 1 (by rfl) ⟨1540136, by rfl⟩ : syracuseStep 2053515 = 3080273) B3080273
theorem B6930629 : Blo 2053435 6930629 := bbase (se 4 (by rfl) ⟨649746, by rfl⟩ : syracuseStep 6930629 = 1299493) (by norm_num)
theorem B4620419 : Blo 2053435 4620419 := bstep (se 1 (by rfl) ⟨3465314, by rfl⟩ : syracuseStep 4620419 = 6930629) B6930629
theorem B3080279 : Blo 2053435 3080279 := bstep (se 1 (by rfl) ⟨2310209, by rfl⟩ : syracuseStep 3080279 = 4620419) B4620419
theorem B2053519 : Blo 2053435 2053519 := bstep (se 1 (by rfl) ⟨1540139, by rfl⟩ : syracuseStep 2053519 = 3080279) B3080279
theorem B3080285 : Blo 2053435 3080285 := bbase (se 3 (by rfl) ⟨577553, by rfl⟩ : syracuseStep 3080285 = 1155107) (by norm_num)
theorem B2053523 : Blo 2053435 2053523 := bstep (se 1 (by rfl) ⟨1540142, by rfl⟩ : syracuseStep 2053523 = 3080285) B3080285
theorem B4620437 : Blo 2053435 4620437 := bbase (se 6 (by rfl) ⟨108291, by rfl⟩ : syracuseStep 4620437 = 216583) (by norm_num)
theorem B3080291 : Blo 2053435 3080291 := bstep (se 1 (by rfl) ⟨2310218, by rfl⟩ : syracuseStep 3080291 = 4620437) B4620437
theorem B2053527 : Blo 2053435 2053527 := bstep (se 1 (by rfl) ⟨1540145, by rfl⟩ : syracuseStep 2053527 = 3080291) B3080291
theorem B2923877 : Blo 2053435 2923877 := bbase (se 4 (by rfl) ⟨274113, by rfl⟩ : syracuseStep 2923877 = 548227) (by norm_num)
theorem B7797005 : Blo 2053435 7797005 := bstep (se 3 (by rfl) ⟨1461938, by rfl⟩ : syracuseStep 7797005 = 2923877) B2923877
theorem B5198003 : Blo 2053435 5198003 := bstep (se 1 (by rfl) ⟨3898502, by rfl⟩ : syracuseStep 5198003 = 7797005) B7797005
theorem B3465335 : Blo 2053435 3465335 := bstep (se 1 (by rfl) ⟨2599001, by rfl⟩ : syracuseStep 3465335 = 5198003) B5198003
theorem B2310223 : Blo 2053435 2310223 := bstep (se 1 (by rfl) ⟨1732667, by rfl⟩ : syracuseStep 2310223 = 3465335) B3465335
theorem B3080297 : Blo 2053435 3080297 := bstep (se 2 (by rfl) ⟨1155111, by rfl⟩ : syracuseStep 3080297 = 2310223) B2310223
theorem B2053531 : Blo 2053435 2053531 := bstep (se 1 (by rfl) ⟨1540148, by rfl⟩ : syracuseStep 2053531 = 3080297) B3080297
theorem B71130581 : Blo 2053435 71130581 := bbase (se 7 (by rfl) ⟨833561, by rfl⟩ : syracuseStep 71130581 = 1667123) (by norm_num)
theorem B47420387 : Blo 2053435 47420387 := bstep (se 1 (by rfl) ⟨35565290, by rfl⟩ : syracuseStep 47420387 = 71130581) B71130581
theorem B31613591 : Blo 2053435 31613591 := bstep (se 1 (by rfl) ⟨23710193, by rfl⟩ : syracuseStep 31613591 = 47420387) B47420387
theorem B21075727 : Blo 2053435 21075727 := bstep (se 1 (by rfl) ⟨15806795, by rfl⟩ : syracuseStep 21075727 = 31613591) B31613591
theorem B28100969 : Blo 2053435 28100969 := bstep (se 2 (by rfl) ⟨10537863, by rfl⟩ : syracuseStep 28100969 = 21075727) B21075727
theorem B18733979 : Blo 2053435 18733979 := bstep (se 1 (by rfl) ⟨14050484, by rfl⟩ : syracuseStep 18733979 = 28100969) B28100969
theorem B12489319 : Blo 2053435 12489319 := bstep (se 1 (by rfl) ⟨9366989, by rfl⟩ : syracuseStep 12489319 = 18733979) B18733979
theorem B66609701 : Blo 2053435 66609701 := bstep (se 4 (by rfl) ⟨6244659, by rfl⟩ : syracuseStep 66609701 = 12489319) B12489319
theorem B44406467 : Blo 2053435 44406467 := bstep (se 1 (by rfl) ⟨33304850, by rfl⟩ : syracuseStep 44406467 = 66609701) B66609701
theorem B29604311 : Blo 2053435 29604311 := bstep (se 1 (by rfl) ⟨22203233, by rfl⟩ : syracuseStep 29604311 = 44406467) B44406467
theorem B19736207 : Blo 2053435 19736207 := bstep (se 1 (by rfl) ⟨14802155, by rfl⟩ : syracuseStep 19736207 = 29604311) B29604311
theorem B13157471 : Blo 2053435 13157471 := bstep (se 1 (by rfl) ⟨9868103, by rfl⟩ : syracuseStep 13157471 = 19736207) B19736207
theorem B8771647 : Blo 2053435 8771647 := bstep (se 1 (by rfl) ⟨6578735, by rfl⟩ : syracuseStep 8771647 = 13157471) B13157471
theorem B11695529 : Blo 2053435 11695529 := bstep (se 2 (by rfl) ⟨4385823, by rfl⟩ : syracuseStep 11695529 = 8771647) B8771647
theorem B7797019 : Blo 2053435 7797019 := bstep (se 1 (by rfl) ⟨5847764, by rfl⟩ : syracuseStep 7797019 = 11695529) B11695529
theorem B10396025 : Blo 2053435 10396025 := bstep (se 2 (by rfl) ⟨3898509, by rfl⟩ : syracuseStep 10396025 = 7797019) B7797019
theorem B6930683 : Blo 2053435 6930683 := bstep (se 1 (by rfl) ⟨5198012, by rfl⟩ : syracuseStep 6930683 = 10396025) B10396025
theorem B4620455 : Blo 2053435 4620455 := bstep (se 1 (by rfl) ⟨3465341, by rfl⟩ : syracuseStep 4620455 = 6930683) B6930683
theorem B3080303 : Blo 2053435 3080303 := bstep (se 1 (by rfl) ⟨2310227, by rfl⟩ : syracuseStep 3080303 = 4620455) B4620455
theorem B2053535 : Blo 2053435 2053535 := bstep (se 1 (by rfl) ⟨1540151, by rfl⟩ : syracuseStep 2053535 = 3080303) B3080303
theorem B3080309 : Blo 2053435 3080309 := bbase (se 5 (by rfl) ⟨144389, by rfl⟩ : syracuseStep 3080309 = 288779) (by norm_num)
theorem B2053539 : Blo 2053435 2053539 := bstep (se 1 (by rfl) ⟨1540154, by rfl⟩ : syracuseStep 2053539 = 3080309) B3080309
theorem B3898525 : Blo 2053435 3898525 := bbase (se 3 (by rfl) ⟨730973, by rfl⟩ : syracuseStep 3898525 = 1461947) (by norm_num)
theorem B5198033 : Blo 2053435 5198033 := bstep (se 2 (by rfl) ⟨1949262, by rfl⟩ : syracuseStep 5198033 = 3898525) B3898525
theorem B3465355 : Blo 2053435 3465355 := bstep (se 1 (by rfl) ⟨2599016, by rfl⟩ : syracuseStep 3465355 = 5198033) B5198033
theorem B4620473 : Blo 2053435 4620473 := bstep (se 2 (by rfl) ⟨1732677, by rfl⟩ : syracuseStep 4620473 = 3465355) B3465355
theorem B3080315 : Blo 2053435 3080315 := bstep (se 1 (by rfl) ⟨2310236, by rfl⟩ : syracuseStep 3080315 = 4620473) B4620473
theorem B2053543 : Blo 2053435 2053543 := bstep (se 1 (by rfl) ⟨1540157, by rfl⟩ : syracuseStep 2053543 = 3080315) B3080315
theorem B2310241 : Blo 2053435 2310241 := bbase (se 2 (by rfl) ⟨866340, by rfl⟩ : syracuseStep 2310241 = 1732681) (by norm_num)
theorem B3080321 : Blo 2053435 3080321 := bstep (se 2 (by rfl) ⟨1155120, by rfl⟩ : syracuseStep 3080321 = 2310241) B2310241
theorem B2053547 : Blo 2053435 2053547 := bstep (se 1 (by rfl) ⟨1540160, by rfl⟩ : syracuseStep 2053547 = 3080321) B3080321
theorem B5198053 : Blo 2053435 5198053 := bbase (se 4 (by rfl) ⟨487317, by rfl⟩ : syracuseStep 5198053 = 974635) (by norm_num)
theorem B6930737 : Blo 2053435 6930737 := bstep (se 2 (by rfl) ⟨2599026, by rfl⟩ : syracuseStep 6930737 = 5198053) B5198053
theorem B4620491 : Blo 2053435 4620491 := bstep (se 1 (by rfl) ⟨3465368, by rfl⟩ : syracuseStep 4620491 = 6930737) B6930737
theorem B3080327 : Blo 2053435 3080327 := bstep (se 1 (by rfl) ⟨2310245, by rfl⟩ : syracuseStep 3080327 = 4620491) B4620491
theorem B2053551 : Blo 2053435 2053551 := bstep (se 1 (by rfl) ⟨1540163, by rfl⟩ : syracuseStep 2053551 = 3080327) B3080327
theorem B3080333 : Blo 2053435 3080333 := bbase (se 3 (by rfl) ⟨577562, by rfl⟩ : syracuseStep 3080333 = 1155125) (by norm_num)
theorem B2053555 : Blo 2053435 2053555 := bstep (se 1 (by rfl) ⟨1540166, by rfl⟩ : syracuseStep 2053555 = 3080333) B3080333
theorem B4620509 : Blo 2053435 4620509 := bbase (se 3 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 4620509 = 1732691) (by norm_num)
theorem B3080339 : Blo 2053435 3080339 := bstep (se 1 (by rfl) ⟨2310254, by rfl⟩ : syracuseStep 3080339 = 4620509) B4620509
theorem B2053559 : Blo 2053435 2053559 := bstep (se 1 (by rfl) ⟨1540169, by rfl⟩ : syracuseStep 2053559 = 3080339) B3080339
theorem B3465389 : Blo 2053435 3465389 := bbase (se 3 (by rfl) ⟨649760, by rfl⟩ : syracuseStep 3465389 = 1299521) (by norm_num)
theorem B2310259 : Blo 2053435 2310259 := bstep (se 1 (by rfl) ⟨1732694, by rfl⟩ : syracuseStep 2310259 = 3465389) B3465389
theorem B3080345 : Blo 2053435 3080345 := bstep (se 2 (by rfl) ⟨1155129, by rfl⟩ : syracuseStep 3080345 = 2310259) B2310259
theorem B2053563 : Blo 2053435 2053563 := bstep (se 1 (by rfl) ⟨1540172, by rfl⟩ : syracuseStep 2053563 = 3080345) B3080345
theorem B6244757 : Blo 2053435 6244757 := bbase (se 6 (by rfl) ⟨146361, by rfl⟩ : syracuseStep 6244757 = 292723) (by norm_num)
theorem B4163171 : Blo 2053435 4163171 := bstep (se 1 (by rfl) ⟨3122378, by rfl⟩ : syracuseStep 4163171 = 6244757) B6244757
theorem B11101789 : Blo 2053435 11101789 := bstep (se 3 (by rfl) ⟨2081585, by rfl⟩ : syracuseStep 11101789 = 4163171) B4163171
theorem B59209541 : Blo 2053435 59209541 := bstep (se 4 (by rfl) ⟨5550894, by rfl⟩ : syracuseStep 59209541 = 11101789) B11101789
theorem B39473027 : Blo 2053435 39473027 := bstep (se 1 (by rfl) ⟨29604770, by rfl⟩ : syracuseStep 39473027 = 59209541) B59209541
theorem B26315351 : Blo 2053435 26315351 := bstep (se 1 (by rfl) ⟨19736513, by rfl⟩ : syracuseStep 26315351 = 39473027) B39473027
theorem B17543567 : Blo 2053435 17543567 := bstep (se 1 (by rfl) ⟨13157675, by rfl⟩ : syracuseStep 17543567 = 26315351) B26315351
theorem B11695711 : Blo 2053435 11695711 := bstep (se 1 (by rfl) ⟨8771783, by rfl⟩ : syracuseStep 11695711 = 17543567) B17543567
theorem B15594281 : Blo 2053435 15594281 := bstep (se 2 (by rfl) ⟨5847855, by rfl⟩ : syracuseStep 15594281 = 11695711) B11695711
theorem B10396187 : Blo 2053435 10396187 := bstep (se 1 (by rfl) ⟨7797140, by rfl⟩ : syracuseStep 10396187 = 15594281) B15594281
theorem B6930791 : Blo 2053435 6930791 := bstep (se 1 (by rfl) ⟨5198093, by rfl⟩ : syracuseStep 6930791 = 10396187) B10396187
theorem B4620527 : Blo 2053435 4620527 := bstep (se 1 (by rfl) ⟨3465395, by rfl⟩ : syracuseStep 4620527 = 6930791) B6930791
theorem B3080351 : Blo 2053435 3080351 := bstep (se 1 (by rfl) ⟨2310263, by rfl⟩ : syracuseStep 3080351 = 4620527) B4620527
theorem B2053567 : Blo 2053435 2053567 := bstep (se 1 (by rfl) ⟨1540175, by rfl⟩ : syracuseStep 2053567 = 3080351) B3080351
theorem B3080357 : Blo 2053435 3080357 := bbase (se 4 (by rfl) ⟨288783, by rfl⟩ : syracuseStep 3080357 = 577567) (by norm_num)
theorem B2053571 : Blo 2053435 2053571 := bstep (se 1 (by rfl) ⟨1540178, by rfl⟩ : syracuseStep 2053571 = 3080357) B3080357
theorem B2599057 : Blo 2053435 2599057 := bbase (se 2 (by rfl) ⟨974646, by rfl⟩ : syracuseStep 2599057 = 1949293) (by norm_num)
theorem B3465409 : Blo 2053435 3465409 := bstep (se 2 (by rfl) ⟨1299528, by rfl⟩ : syracuseStep 3465409 = 2599057) B2599057
theorem B4620545 : Blo 2053435 4620545 := bstep (se 2 (by rfl) ⟨1732704, by rfl⟩ : syracuseStep 4620545 = 3465409) B3465409
theorem B3080363 : Blo 2053435 3080363 := bstep (se 1 (by rfl) ⟨2310272, by rfl⟩ : syracuseStep 3080363 = 4620545) B4620545
theorem B2053575 : Blo 2053435 2053575 := bstep (se 1 (by rfl) ⟨1540181, by rfl⟩ : syracuseStep 2053575 = 3080363) B3080363
theorem B2310277 : Blo 2053435 2310277 := bbase (se 4 (by rfl) ⟨216588, by rfl⟩ : syracuseStep 2310277 = 433177) (by norm_num)
theorem B3080369 : Blo 2053435 3080369 := bstep (se 2 (by rfl) ⟨1155138, by rfl⟩ : syracuseStep 3080369 = 2310277) B2310277
theorem B2053579 : Blo 2053435 2053579 := bstep (se 1 (by rfl) ⟨1540184, by rfl⟩ : syracuseStep 2053579 = 3080369) B3080369
theorem B7401253 : Blo 2053435 7401253 := bbase (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) (by norm_num)
theorem B9868337 : Blo 2053435 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B6578891 : Blo 2053435 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B4385927 : Blo 2053435 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B2923951 : Blo 2053435 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B3898601 : Blo 2053435 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B2599067 : Blo 2053435 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B6930845 : Blo 2053435 6930845 := bstep (se 3 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 6930845 = 2599067) B2599067
theorem B4620563 : Blo 2053435 4620563 := bstep (se 1 (by rfl) ⟨3465422, by rfl⟩ : syracuseStep 4620563 = 6930845) B6930845
theorem B3080375 : Blo 2053435 3080375 := bstep (se 1 (by rfl) ⟨2310281, by rfl⟩ : syracuseStep 3080375 = 4620563) B4620563
theorem B2053583 : Blo 2053435 2053583 := bstep (se 1 (by rfl) ⟨1540187, by rfl⟩ : syracuseStep 2053583 = 3080375) B3080375
theorem B3080381 : Blo 2053435 3080381 := bbase (se 3 (by rfl) ⟨577571, by rfl⟩ : syracuseStep 3080381 = 1155143) (by norm_num)
theorem B2053587 : Blo 2053435 2053587 := bstep (se 1 (by rfl) ⟨1540190, by rfl⟩ : syracuseStep 2053587 = 3080381) B3080381
theorem B4620581 : Blo 2053435 4620581 := bbase (se 4 (by rfl) ⟨433179, by rfl⟩ : syracuseStep 4620581 = 866359) (by norm_num)
theorem B3080387 : Blo 2053435 3080387 := bstep (se 1 (by rfl) ⟨2310290, by rfl⟩ : syracuseStep 3080387 = 4620581) B4620581
theorem B2053591 : Blo 2053435 2053591 := bstep (se 1 (by rfl) ⟨1540193, by rfl⟩ : syracuseStep 2053591 = 3080387) B3080387
theorem B5198165 : Blo 2053435 5198165 := bbase (se 10 (by rfl) ⟨7614, by rfl⟩ : syracuseStep 5198165 = 15229) (by norm_num)
theorem B3465443 : Blo 2053435 3465443 := bstep (se 1 (by rfl) ⟨2599082, by rfl⟩ : syracuseStep 3465443 = 5198165) B5198165
theorem B2310295 : Blo 2053435 2310295 := bstep (se 1 (by rfl) ⟨1732721, by rfl⟩ : syracuseStep 2310295 = 3465443) B3465443
theorem B3080393 : Blo 2053435 3080393 := bstep (se 2 (by rfl) ⟨1155147, by rfl⟩ : syracuseStep 3080393 = 2310295) B2310295
theorem B2053595 : Blo 2053435 2053595 := bstep (se 1 (by rfl) ⟨1540196, by rfl⟩ : syracuseStep 2053595 = 3080393) B3080393
theorem B9367285 : Blo 2053435 9367285 := bbase (se 5 (by rfl) ⟨439091, by rfl⟩ : syracuseStep 9367285 = 878183) (by norm_num)
theorem B12489713 : Blo 2053435 12489713 := bstep (se 2 (by rfl) ⟨4683642, by rfl⟩ : syracuseStep 12489713 = 9367285) B9367285
theorem B8326475 : Blo 2053435 8326475 := bstep (se 1 (by rfl) ⟨6244856, by rfl⟩ : syracuseStep 8326475 = 12489713) B12489713
theorem B5550983 : Blo 2053435 5550983 := bstep (se 1 (by rfl) ⟨4163237, by rfl⟩ : syracuseStep 5550983 = 8326475) B8326475
theorem B3700655 : Blo 2053435 3700655 := bstep (se 1 (by rfl) ⟨2775491, by rfl⟩ : syracuseStep 3700655 = 5550983) B5550983
theorem B2467103 : Blo 2053435 2467103 := bstep (se 1 (by rfl) ⟨1850327, by rfl⟩ : syracuseStep 2467103 = 3700655) B3700655
theorem B6578941 : Blo 2053435 6578941 := bstep (se 3 (by rfl) ⟨1233551, by rfl⟩ : syracuseStep 6578941 = 2467103) B2467103
theorem B8771921 : Blo 2053435 8771921 := bstep (se 2 (by rfl) ⟨3289470, by rfl⟩ : syracuseStep 8771921 = 6578941) B6578941
theorem B5847947 : Blo 2053435 5847947 := bstep (se 1 (by rfl) ⟨4385960, by rfl⟩ : syracuseStep 5847947 = 8771921) B8771921
theorem B3898631 : Blo 2053435 3898631 := bstep (se 1 (by rfl) ⟨2923973, by rfl⟩ : syracuseStep 3898631 = 5847947) B5847947
theorem B10396349 : Blo 2053435 10396349 := bstep (se 3 (by rfl) ⟨1949315, by rfl⟩ : syracuseStep 10396349 = 3898631) B3898631
theorem B6930899 : Blo 2053435 6930899 := bstep (se 1 (by rfl) ⟨5198174, by rfl⟩ : syracuseStep 6930899 = 10396349) B10396349
theorem B4620599 : Blo 2053435 4620599 := bstep (se 1 (by rfl) ⟨3465449, by rfl⟩ : syracuseStep 4620599 = 6930899) B6930899
theorem B3080399 : Blo 2053435 3080399 := bstep (se 1 (by rfl) ⟨2310299, by rfl⟩ : syracuseStep 3080399 = 4620599) B4620599
theorem B2053599 : Blo 2053435 2053599 := bstep (se 1 (by rfl) ⟨1540199, by rfl⟩ : syracuseStep 2053599 = 3080399) B3080399
theorem B3080405 : Blo 2053435 3080405 := bbase (se 7 (by rfl) ⟨36098, by rfl⟩ : syracuseStep 3080405 = 72197) (by norm_num)
theorem B2053603 : Blo 2053435 2053603 := bstep (se 1 (by rfl) ⟨1540202, by rfl⟩ : syracuseStep 2053603 = 3080405) B3080405
theorem B2192989 : Blo 2053435 2192989 := bbase (se 3 (by rfl) ⟨411185, by rfl⟩ : syracuseStep 2192989 = 822371) (by norm_num)
theorem B2923985 : Blo 2053435 2923985 := bstep (se 2 (by rfl) ⟨1096494, by rfl⟩ : syracuseStep 2923985 = 2192989) B2192989
theorem B7797293 : Blo 2053435 7797293 := bstep (se 3 (by rfl) ⟨1461992, by rfl⟩ : syracuseStep 7797293 = 2923985) B2923985
theorem B5198195 : Blo 2053435 5198195 := bstep (se 1 (by rfl) ⟨3898646, by rfl⟩ : syracuseStep 5198195 = 7797293) B7797293
theorem B3465463 : Blo 2053435 3465463 := bstep (se 1 (by rfl) ⟨2599097, by rfl⟩ : syracuseStep 3465463 = 5198195) B5198195
theorem B4620617 : Blo 2053435 4620617 := bstep (se 2 (by rfl) ⟨1732731, by rfl⟩ : syracuseStep 4620617 = 3465463) B3465463
theorem B3080411 : Blo 2053435 3080411 := bstep (se 1 (by rfl) ⟨2310308, by rfl⟩ : syracuseStep 3080411 = 4620617) B4620617
theorem B2053607 : Blo 2053435 2053607 := bstep (se 1 (by rfl) ⟨1540205, by rfl⟩ : syracuseStep 2053607 = 3080411) B3080411
theorem B2310313 : Blo 2053435 2310313 := bbase (se 2 (by rfl) ⟨866367, by rfl⟩ : syracuseStep 2310313 = 1732735) (by norm_num)
theorem B3080417 : Blo 2053435 3080417 := bstep (se 2 (by rfl) ⟨1155156, by rfl⟩ : syracuseStep 3080417 = 2310313) B2310313
theorem B2053611 : Blo 2053435 2053611 := bstep (se 1 (by rfl) ⟨1540208, by rfl⟩ : syracuseStep 2053611 = 3080417) B3080417
theorem B8771989 : Blo 2053435 8771989 := bbase (se 6 (by rfl) ⟨205593, by rfl⟩ : syracuseStep 8771989 = 411187) (by norm_num)
theorem B11695985 : Blo 2053435 11695985 := bstep (se 2 (by rfl) ⟨4385994, by rfl⟩ : syracuseStep 11695985 = 8771989) B8771989
theorem B7797323 : Blo 2053435 7797323 := bstep (se 1 (by rfl) ⟨5847992, by rfl⟩ : syracuseStep 7797323 = 11695985) B11695985
theorem B5198215 : Blo 2053435 5198215 := bstep (se 1 (by rfl) ⟨3898661, by rfl⟩ : syracuseStep 5198215 = 7797323) B7797323
theorem B6930953 : Blo 2053435 6930953 := bstep (se 2 (by rfl) ⟨2599107, by rfl⟩ : syracuseStep 6930953 = 5198215) B5198215
theorem B4620635 : Blo 2053435 4620635 := bstep (se 1 (by rfl) ⟨3465476, by rfl⟩ : syracuseStep 4620635 = 6930953) B6930953
theorem B3080423 : Blo 2053435 3080423 := bstep (se 1 (by rfl) ⟨2310317, by rfl⟩ : syracuseStep 3080423 = 4620635) B4620635
theorem B2053615 : Blo 2053435 2053615 := bstep (se 1 (by rfl) ⟨1540211, by rfl⟩ : syracuseStep 2053615 = 3080423) B3080423
theorem B3080429 : Blo 2053435 3080429 := bbase (se 3 (by rfl) ⟨577580, by rfl⟩ : syracuseStep 3080429 = 1155161) (by norm_num)
theorem B2053619 : Blo 2053435 2053619 := bstep (se 1 (by rfl) ⟨1540214, by rfl⟩ : syracuseStep 2053619 = 3080429) B3080429
theorem B4620653 : Blo 2053435 4620653 := bbase (se 3 (by rfl) ⟨866372, by rfl⟩ : syracuseStep 4620653 = 1732745) (by norm_num)
theorem B3080435 : Blo 2053435 3080435 := bstep (se 1 (by rfl) ⟨2310326, by rfl⟩ : syracuseStep 3080435 = 4620653) B4620653
theorem B2053623 : Blo 2053435 2053623 := bstep (se 1 (by rfl) ⟨1540217, by rfl⟩ : syracuseStep 2053623 = 3080435) B3080435
theorem B3898685 : Blo 2053435 3898685 := bbase (se 3 (by rfl) ⟨731003, by rfl⟩ : syracuseStep 3898685 = 1462007) (by norm_num)
theorem B2599123 : Blo 2053435 2599123 := bstep (se 1 (by rfl) ⟨1949342, by rfl⟩ : syracuseStep 2599123 = 3898685) B3898685
theorem B3465497 : Blo 2053435 3465497 := bstep (se 2 (by rfl) ⟨1299561, by rfl⟩ : syracuseStep 3465497 = 2599123) B2599123
theorem B2310331 : Blo 2053435 2310331 := bstep (se 1 (by rfl) ⟨1732748, by rfl⟩ : syracuseStep 2310331 = 3465497) B3465497
theorem B3080441 : Blo 2053435 3080441 := bstep (se 2 (by rfl) ⟨1155165, by rfl⟩ : syracuseStep 3080441 = 2310331) B2310331
theorem B2053627 : Blo 2053435 2053627 := bstep (se 1 (by rfl) ⟨1540220, by rfl⟩ : syracuseStep 2053627 = 3080441) B3080441
theorem B2467141 : Blo 2053435 2467141 := bbase (se 4 (by rfl) ⟨231294, by rfl⟩ : syracuseStep 2467141 = 462589) (by norm_num)
theorem B52632341 : Blo 2053435 52632341 := bstep (se 6 (by rfl) ⟨1233570, by rfl⟩ : syracuseStep 52632341 = 2467141) B2467141
theorem B35088227 : Blo 2053435 35088227 := bstep (se 1 (by rfl) ⟨26316170, by rfl⟩ : syracuseStep 35088227 = 52632341) B52632341
theorem B23392151 : Blo 2053435 23392151 := bstep (se 1 (by rfl) ⟨17544113, by rfl⟩ : syracuseStep 23392151 = 35088227) B35088227
theorem B15594767 : Blo 2053435 15594767 := bstep (se 1 (by rfl) ⟨11696075, by rfl⟩ : syracuseStep 15594767 = 23392151) B23392151
theorem B10396511 : Blo 2053435 10396511 := bstep (se 1 (by rfl) ⟨7797383, by rfl⟩ : syracuseStep 10396511 = 15594767) B15594767
theorem B6931007 : Blo 2053435 6931007 := bstep (se 1 (by rfl) ⟨5198255, by rfl⟩ : syracuseStep 6931007 = 10396511) B10396511
theorem B4620671 : Blo 2053435 4620671 := bstep (se 1 (by rfl) ⟨3465503, by rfl⟩ : syracuseStep 4620671 = 6931007) B6931007
theorem B3080447 : Blo 2053435 3080447 := bstep (se 1 (by rfl) ⟨2310335, by rfl⟩ : syracuseStep 3080447 = 4620671) B4620671
theorem B2053631 : Blo 2053435 2053631 := bstep (se 1 (by rfl) ⟨1540223, by rfl⟩ : syracuseStep 2053631 = 3080447) B3080447
theorem B3080453 : Blo 2053435 3080453 := bbase (se 4 (by rfl) ⟨288792, by rfl⟩ : syracuseStep 3080453 = 577585) (by norm_num)
theorem B2053635 : Blo 2053435 2053635 := bstep (se 1 (by rfl) ⟨1540226, by rfl⟩ : syracuseStep 2053635 = 3080453) B3080453
theorem B3465517 : Blo 2053435 3465517 := bbase (se 3 (by rfl) ⟨649784, by rfl⟩ : syracuseStep 3465517 = 1299569) (by norm_num)
theorem B4620689 : Blo 2053435 4620689 := bstep (se 2 (by rfl) ⟨1732758, by rfl⟩ : syracuseStep 4620689 = 3465517) B3465517
theorem B3080459 : Blo 2053435 3080459 := bstep (se 1 (by rfl) ⟨2310344, by rfl⟩ : syracuseStep 3080459 = 4620689) B4620689
theorem B2053639 : Blo 2053435 2053639 := bstep (se 1 (by rfl) ⟨1540229, by rfl⟩ : syracuseStep 2053639 = 3080459) B3080459
theorem B2310349 : Blo 2053435 2310349 := bbase (se 3 (by rfl) ⟨433190, by rfl⟩ : syracuseStep 2310349 = 866381) (by norm_num)
theorem B3080465 : Blo 2053435 3080465 := bstep (se 2 (by rfl) ⟨1155174, by rfl⟩ : syracuseStep 3080465 = 2310349) B2310349
theorem B2053643 : Blo 2053435 2053643 := bstep (se 1 (by rfl) ⟨1540232, by rfl⟩ : syracuseStep 2053643 = 3080465) B3080465
theorem B6931061 : Blo 2053435 6931061 := bbase (se 5 (by rfl) ⟨324893, by rfl⟩ : syracuseStep 6931061 = 649787) (by norm_num)
theorem B4620707 : Blo 2053435 4620707 := bstep (se 1 (by rfl) ⟨3465530, by rfl⟩ : syracuseStep 4620707 = 6931061) B6931061
theorem B3080471 : Blo 2053435 3080471 := bstep (se 1 (by rfl) ⟨2310353, by rfl⟩ : syracuseStep 3080471 = 4620707) B4620707
theorem B2053647 : Blo 2053435 2053647 := bstep (se 1 (by rfl) ⟨1540235, by rfl⟩ : syracuseStep 2053647 = 3080471) B3080471
theorem B3080477 : Blo 2053435 3080477 := bbase (se 3 (by rfl) ⟨577589, by rfl⟩ : syracuseStep 3080477 = 1155179) (by norm_num)
theorem B2053651 : Blo 2053435 2053651 := bstep (se 1 (by rfl) ⟨1540238, by rfl⟩ : syracuseStep 2053651 = 3080477) B3080477
theorem B4620725 : Blo 2053435 4620725 := bbase (se 5 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 4620725 = 433193) (by norm_num)
theorem B3080483 : Blo 2053435 3080483 := bstep (se 1 (by rfl) ⟨2310362, by rfl⟩ : syracuseStep 3080483 = 4620725) B4620725
theorem B2053655 : Blo 2053435 2053655 := bstep (se 1 (by rfl) ⟨1540241, by rfl⟩ : syracuseStep 2053655 = 3080483) B3080483
theorem B5927909 : Blo 2053435 5927909 := bbase (se 4 (by rfl) ⟨555741, by rfl⟩ : syracuseStep 5927909 = 1111483) (by norm_num)
theorem B15807757 : Blo 2053435 15807757 := bstep (se 3 (by rfl) ⟨2963954, by rfl⟩ : syracuseStep 15807757 = 5927909) B5927909
theorem B21077009 : Blo 2053435 21077009 := bstep (se 2 (by rfl) ⟨7903878, by rfl⟩ : syracuseStep 21077009 = 15807757) B15807757
theorem B14051339 : Blo 2053435 14051339 := bstep (se 1 (by rfl) ⟨10538504, by rfl⟩ : syracuseStep 14051339 = 21077009) B21077009
theorem B9367559 : Blo 2053435 9367559 := bstep (se 1 (by rfl) ⟨7025669, by rfl⟩ : syracuseStep 9367559 = 14051339) B14051339
theorem B6245039 : Blo 2053435 6245039 := bstep (se 1 (by rfl) ⟨4683779, by rfl⟩ : syracuseStep 6245039 = 9367559) B9367559
theorem B16653437 : Blo 2053435 16653437 := bstep (se 3 (by rfl) ⟨3122519, by rfl⟩ : syracuseStep 16653437 = 6245039) B6245039
theorem B11102291 : Blo 2053435 11102291 := bstep (se 1 (by rfl) ⟨8326718, by rfl⟩ : syracuseStep 11102291 = 16653437) B16653437
theorem B7401527 : Blo 2053435 7401527 := bstep (se 1 (by rfl) ⟨5551145, by rfl⟩ : syracuseStep 7401527 = 11102291) B11102291
theorem B4934351 : Blo 2053435 4934351 := bstep (se 1 (by rfl) ⟨3700763, by rfl⟩ : syracuseStep 4934351 = 7401527) B7401527
theorem B3289567 : Blo 2053435 3289567 := bstep (se 1 (by rfl) ⟨2467175, by rfl⟩ : syracuseStep 3289567 = 4934351) B4934351
theorem B4386089 : Blo 2053435 4386089 := bstep (se 2 (by rfl) ⟨1644783, by rfl⟩ : syracuseStep 4386089 = 3289567) B3289567
theorem B11696237 : Blo 2053435 11696237 := bstep (se 3 (by rfl) ⟨2193044, by rfl⟩ : syracuseStep 11696237 = 4386089) B4386089
theorem B7797491 : Blo 2053435 7797491 := bstep (se 1 (by rfl) ⟨5848118, by rfl⟩ : syracuseStep 7797491 = 11696237) B11696237
theorem B5198327 : Blo 2053435 5198327 := bstep (se 1 (by rfl) ⟨3898745, by rfl⟩ : syracuseStep 5198327 = 7797491) B7797491
theorem B3465551 : Blo 2053435 3465551 := bstep (se 1 (by rfl) ⟨2599163, by rfl⟩ : syracuseStep 3465551 = 5198327) B5198327
theorem B2310367 : Blo 2053435 2310367 := bstep (se 1 (by rfl) ⟨1732775, by rfl⟩ : syracuseStep 2310367 = 3465551) B3465551
theorem B3080489 : Blo 2053435 3080489 := bstep (se 2 (by rfl) ⟨1155183, by rfl⟩ : syracuseStep 3080489 = 2310367) B2310367
theorem B2053659 : Blo 2053435 2053659 := bstep (se 1 (by rfl) ⟨1540244, by rfl⟩ : syracuseStep 2053659 = 3080489) B3080489
theorem B3289573 : Blo 2053435 3289573 := bbase (se 4 (by rfl) ⟨308397, by rfl⟩ : syracuseStep 3289573 = 616795) (by norm_num)
theorem B4386097 : Blo 2053435 4386097 := bstep (se 2 (by rfl) ⟨1644786, by rfl⟩ : syracuseStep 4386097 = 3289573) B3289573
theorem B5848129 : Blo 2053435 5848129 := bstep (se 2 (by rfl) ⟨2193048, by rfl⟩ : syracuseStep 5848129 = 4386097) B4386097
theorem B7797505 : Blo 2053435 7797505 := bstep (se 2 (by rfl) ⟨2924064, by rfl⟩ : syracuseStep 7797505 = 5848129) B5848129
theorem B10396673 : Blo 2053435 10396673 := bstep (se 2 (by rfl) ⟨3898752, by rfl⟩ : syracuseStep 10396673 = 7797505) B7797505
theorem B6931115 : Blo 2053435 6931115 := bstep (se 1 (by rfl) ⟨5198336, by rfl⟩ : syracuseStep 6931115 = 10396673) B10396673
theorem B4620743 : Blo 2053435 4620743 := bstep (se 1 (by rfl) ⟨3465557, by rfl⟩ : syracuseStep 4620743 = 6931115) B6931115
theorem B3080495 : Blo 2053435 3080495 := bstep (se 1 (by rfl) ⟨2310371, by rfl⟩ : syracuseStep 3080495 = 4620743) B4620743
theorem B2053663 : Blo 2053435 2053663 := bstep (se 1 (by rfl) ⟨1540247, by rfl⟩ : syracuseStep 2053663 = 3080495) B3080495
theorem B3080501 : Blo 2053435 3080501 := bbase (se 5 (by rfl) ⟨144398, by rfl⟩ : syracuseStep 3080501 = 288797) (by norm_num)
theorem B2053667 : Blo 2053435 2053667 := bstep (se 1 (by rfl) ⟨1540250, by rfl⟩ : syracuseStep 2053667 = 3080501) B3080501
theorem B5198357 : Blo 2053435 5198357 := bbase (se 6 (by rfl) ⟨121836, by rfl⟩ : syracuseStep 5198357 = 243673) (by norm_num)
theorem B3465571 : Blo 2053435 3465571 := bstep (se 1 (by rfl) ⟨2599178, by rfl⟩ : syracuseStep 3465571 = 5198357) B5198357
theorem B4620761 : Blo 2053435 4620761 := bstep (se 2 (by rfl) ⟨1732785, by rfl⟩ : syracuseStep 4620761 = 3465571) B3465571
theorem B3080507 : Blo 2053435 3080507 := bstep (se 1 (by rfl) ⟨2310380, by rfl⟩ : syracuseStep 3080507 = 4620761) B4620761
theorem B2053671 : Blo 2053435 2053671 := bstep (se 1 (by rfl) ⟨1540253, by rfl⟩ : syracuseStep 2053671 = 3080507) B3080507
theorem B2310385 : Blo 2053435 2310385 := bbase (se 2 (by rfl) ⟨866394, by rfl⟩ : syracuseStep 2310385 = 1732789) (by norm_num)
theorem B3080513 : Blo 2053435 3080513 := bstep (se 2 (by rfl) ⟨1155192, by rfl⟩ : syracuseStep 3080513 = 2310385) B2310385
theorem B2053675 : Blo 2053435 2053675 := bstep (se 1 (by rfl) ⟨1540256, by rfl⟩ : syracuseStep 2053675 = 3080513) B3080513
theorem B73089877 : Blo 2053435 73089877 := bbase (se 9 (by rfl) ⟨214130, by rfl⟩ : syracuseStep 73089877 = 428261) (by norm_num)
theorem B97453169 : Blo 2053435 97453169 := bstep (se 2 (by rfl) ⟨36544938, by rfl⟩ : syracuseStep 97453169 = 73089877) B73089877
theorem B64968779 : Blo 2053435 64968779 := bstep (se 1 (by rfl) ⟨48726584, by rfl⟩ : syracuseStep 64968779 = 97453169) B97453169
theorem B43312519 : Blo 2053435 43312519 := bstep (se 1 (by rfl) ⟨32484389, by rfl⟩ : syracuseStep 43312519 = 64968779) B64968779
theorem B57750025 : Blo 2053435 57750025 := bstep (se 2 (by rfl) ⟨21656259, by rfl⟩ : syracuseStep 57750025 = 43312519) B43312519
theorem B77000033 : Blo 2053435 77000033 := bstep (se 2 (by rfl) ⟨28875012, by rfl⟩ : syracuseStep 77000033 = 57750025) B57750025
theorem B51333355 : Blo 2053435 51333355 := bstep (se 1 (by rfl) ⟨38500016, by rfl⟩ : syracuseStep 51333355 = 77000033) B77000033
theorem B68444473 : Blo 2053435 68444473 := bstep (se 2 (by rfl) ⟨25666677, by rfl⟩ : syracuseStep 68444473 = 51333355) B51333355
theorem B91259297 : Blo 2053435 91259297 := bstep (se 2 (by rfl) ⟨34222236, by rfl⟩ : syracuseStep 91259297 = 68444473) B68444473
theorem B60839531 : Blo 2053435 60839531 := bstep (se 1 (by rfl) ⟨45629648, by rfl⟩ : syracuseStep 60839531 = 91259297) B91259297
theorem B40559687 : Blo 2053435 40559687 := bstep (se 1 (by rfl) ⟨30419765, by rfl⟩ : syracuseStep 40559687 = 60839531) B60839531
theorem B27039791 : Blo 2053435 27039791 := bstep (se 1 (by rfl) ⟨20279843, by rfl⟩ : syracuseStep 27039791 = 40559687) B40559687
theorem B72106109 : Blo 2053435 72106109 := bstep (se 3 (by rfl) ⟨13519895, by rfl⟩ : syracuseStep 72106109 = 27039791) B27039791
theorem B48070739 : Blo 2053435 48070739 := bstep (se 1 (by rfl) ⟨36053054, by rfl⟩ : syracuseStep 48070739 = 72106109) B72106109
theorem B32047159 : Blo 2053435 32047159 := bstep (se 1 (by rfl) ⟨24035369, by rfl⟩ : syracuseStep 32047159 = 48070739) B48070739
theorem B42729545 : Blo 2053435 42729545 := bstep (se 2 (by rfl) ⟨16023579, by rfl⟩ : syracuseStep 42729545 = 32047159) B32047159
theorem B28486363 : Blo 2053435 28486363 := bstep (se 1 (by rfl) ⟨21364772, by rfl⟩ : syracuseStep 28486363 = 42729545) B42729545
theorem B37981817 : Blo 2053435 37981817 := bstep (se 2 (by rfl) ⟨14243181, by rfl⟩ : syracuseStep 37981817 = 28486363) B28486363
theorem B25321211 : Blo 2053435 25321211 := bstep (se 1 (by rfl) ⟨18990908, by rfl⟩ : syracuseStep 25321211 = 37981817) B37981817
theorem B16880807 : Blo 2053435 16880807 := bstep (se 1 (by rfl) ⟨12660605, by rfl⟩ : syracuseStep 16880807 = 25321211) B25321211
theorem B11253871 : Blo 2053435 11253871 := bstep (se 1 (by rfl) ⟨8440403, by rfl⟩ : syracuseStep 11253871 = 16880807) B16880807
theorem B15005161 : Blo 2053435 15005161 := bstep (se 2 (by rfl) ⟨5626935, by rfl⟩ : syracuseStep 15005161 = 11253871) B11253871
theorem B20006881 : Blo 2053435 20006881 := bstep (se 2 (by rfl) ⟨7502580, by rfl⟩ : syracuseStep 20006881 = 15005161) B15005161
theorem B106703365 : Blo 2053435 106703365 := bstep (se 4 (by rfl) ⟨10003440, by rfl⟩ : syracuseStep 106703365 = 20006881) B20006881
theorem B142271153 : Blo 2053435 142271153 := bstep (se 2 (by rfl) ⟨53351682, by rfl⟩ : syracuseStep 142271153 = 106703365) B106703365
theorem B94847435 : Blo 2053435 94847435 := bstep (se 1 (by rfl) ⟨71135576, by rfl⟩ : syracuseStep 94847435 = 142271153) B142271153
theorem B63231623 : Blo 2053435 63231623 := bstep (se 1 (by rfl) ⟨47423717, by rfl⟩ : syracuseStep 63231623 = 94847435) B94847435
theorem B42154415 : Blo 2053435 42154415 := bstep (se 1 (by rfl) ⟨31615811, by rfl⟩ : syracuseStep 42154415 = 63231623) B63231623
theorem B28102943 : Blo 2053435 28102943 := bstep (se 1 (by rfl) ⟨21077207, by rfl⟩ : syracuseStep 28102943 = 42154415) B42154415
theorem B18735295 : Blo 2053435 18735295 := bstep (se 1 (by rfl) ⟨14051471, by rfl⟩ : syracuseStep 18735295 = 28102943) B28102943
theorem B24980393 : Blo 2053435 24980393 := bstep (se 2 (by rfl) ⟨9367647, by rfl⟩ : syracuseStep 24980393 = 18735295) B18735295
theorem B16653595 : Blo 2053435 16653595 := bstep (se 1 (by rfl) ⟨12490196, by rfl⟩ : syracuseStep 16653595 = 24980393) B24980393
theorem B22204793 : Blo 2053435 22204793 := bstep (se 2 (by rfl) ⟨8326797, by rfl⟩ : syracuseStep 22204793 = 16653595) B16653595
theorem B14803195 : Blo 2053435 14803195 := bstep (se 1 (by rfl) ⟨11102396, by rfl⟩ : syracuseStep 14803195 = 22204793) B22204793
theorem B19737593 : Blo 2053435 19737593 := bstep (se 2 (by rfl) ⟨7401597, by rfl⟩ : syracuseStep 19737593 = 14803195) B14803195
theorem B13158395 : Blo 2053435 13158395 := bstep (se 1 (by rfl) ⟨9868796, by rfl⟩ : syracuseStep 13158395 = 19737593) B19737593
theorem B8772263 : Blo 2053435 8772263 := bstep (se 1 (by rfl) ⟨6579197, by rfl⟩ : syracuseStep 8772263 = 13158395) B13158395
theorem B5848175 : Blo 2053435 5848175 := bstep (se 1 (by rfl) ⟨4386131, by rfl⟩ : syracuseStep 5848175 = 8772263) B8772263
theorem B3898783 : Blo 2053435 3898783 := bstep (se 1 (by rfl) ⟨2924087, by rfl⟩ : syracuseStep 3898783 = 5848175) B5848175
theorem B5198377 : Blo 2053435 5198377 := bstep (se 2 (by rfl) ⟨1949391, by rfl⟩ : syracuseStep 5198377 = 3898783) B3898783
theorem B6931169 : Blo 2053435 6931169 := bstep (se 2 (by rfl) ⟨2599188, by rfl⟩ : syracuseStep 6931169 = 5198377) B5198377
theorem B4620779 : Blo 2053435 4620779 := bstep (se 1 (by rfl) ⟨3465584, by rfl⟩ : syracuseStep 4620779 = 6931169) B6931169
theorem B3080519 : Blo 2053435 3080519 := bstep (se 1 (by rfl) ⟨2310389, by rfl⟩ : syracuseStep 3080519 = 4620779) B4620779
theorem B2053679 : Blo 2053435 2053679 := bstep (se 1 (by rfl) ⟨1540259, by rfl⟩ : syracuseStep 2053679 = 3080519) B3080519
theorem B3080525 : Blo 2053435 3080525 := bbase (se 3 (by rfl) ⟨577598, by rfl⟩ : syracuseStep 3080525 = 1155197) (by norm_num)
theorem B2053683 : Blo 2053435 2053683 := bstep (se 1 (by rfl) ⟨1540262, by rfl⟩ : syracuseStep 2053683 = 3080525) B3080525
theorem B4620797 : Blo 2053435 4620797 := bbase (se 3 (by rfl) ⟨866399, by rfl⟩ : syracuseStep 4620797 = 1732799) (by norm_num)
theorem B3080531 : Blo 2053435 3080531 := bstep (se 1 (by rfl) ⟨2310398, by rfl⟩ : syracuseStep 3080531 = 4620797) B4620797
theorem B2053687 : Blo 2053435 2053687 := bstep (se 1 (by rfl) ⟨1540265, by rfl⟩ : syracuseStep 2053687 = 3080531) B3080531
theorem B3465605 : Blo 2053435 3465605 := bbase (se 4 (by rfl) ⟨324900, by rfl⟩ : syracuseStep 3465605 = 649801) (by norm_num)
theorem B2310403 : Blo 2053435 2310403 := bstep (se 1 (by rfl) ⟨1732802, by rfl⟩ : syracuseStep 2310403 = 3465605) B3465605
theorem B3080537 : Blo 2053435 3080537 := bstep (se 2 (by rfl) ⟨1155201, by rfl⟩ : syracuseStep 3080537 = 2310403) B2310403
theorem B2053691 : Blo 2053435 2053691 := bstep (se 1 (by rfl) ⟨1540268, by rfl⟩ : syracuseStep 2053691 = 3080537) B3080537
theorem B15595253 : Blo 2053435 15595253 := bbase (se 5 (by rfl) ⟨731027, by rfl⟩ : syracuseStep 15595253 = 1462055) (by norm_num)
theorem B10396835 : Blo 2053435 10396835 := bstep (se 1 (by rfl) ⟨7797626, by rfl⟩ : syracuseStep 10396835 = 15595253) B15595253
theorem B6931223 : Blo 2053435 6931223 := bstep (se 1 (by rfl) ⟨5198417, by rfl⟩ : syracuseStep 6931223 = 10396835) B10396835
theorem B4620815 : Blo 2053435 4620815 := bstep (se 1 (by rfl) ⟨3465611, by rfl⟩ : syracuseStep 4620815 = 6931223) B6931223
theorem B3080543 : Blo 2053435 3080543 := bstep (se 1 (by rfl) ⟨2310407, by rfl⟩ : syracuseStep 3080543 = 4620815) B4620815
theorem B2053695 : Blo 2053435 2053695 := bstep (se 1 (by rfl) ⟨1540271, by rfl⟩ : syracuseStep 2053695 = 3080543) B3080543
theorem B3080549 : Blo 2053435 3080549 := bbase (se 4 (by rfl) ⟨288801, by rfl⟩ : syracuseStep 3080549 = 577603) (by norm_num)
theorem B2053699 : Blo 2053435 2053699 := bstep (se 1 (by rfl) ⟨1540274, by rfl⟩ : syracuseStep 2053699 = 3080549) B3080549
theorem B3898829 : Blo 2053435 3898829 := bbase (se 3 (by rfl) ⟨731030, by rfl⟩ : syracuseStep 3898829 = 1462061) (by norm_num)
theorem B2599219 : Blo 2053435 2599219 := bstep (se 1 (by rfl) ⟨1949414, by rfl⟩ : syracuseStep 2599219 = 3898829) B3898829
theorem B3465625 : Blo 2053435 3465625 := bstep (se 2 (by rfl) ⟨1299609, by rfl⟩ : syracuseStep 3465625 = 2599219) B2599219
theorem B4620833 : Blo 2053435 4620833 := bstep (se 2 (by rfl) ⟨1732812, by rfl⟩ : syracuseStep 4620833 = 3465625) B3465625
theorem B3080555 : Blo 2053435 3080555 := bstep (se 1 (by rfl) ⟨2310416, by rfl⟩ : syracuseStep 3080555 = 4620833) B4620833
theorem B2053703 : Blo 2053435 2053703 := bstep (se 1 (by rfl) ⟨1540277, by rfl⟩ : syracuseStep 2053703 = 3080555) B3080555
theorem B2310421 : Blo 2053435 2310421 := bbase (se 6 (by rfl) ⟨54150, by rfl⟩ : syracuseStep 2310421 = 108301) (by norm_num)
theorem B3080561 : Blo 2053435 3080561 := bstep (se 2 (by rfl) ⟨1155210, by rfl⟩ : syracuseStep 3080561 = 2310421) B2310421
theorem B2053707 : Blo 2053435 2053707 := bstep (se 1 (by rfl) ⟨1540280, by rfl⟩ : syracuseStep 2053707 = 3080561) B3080561
theorem B2599229 : Blo 2053435 2599229 := bbase (se 3 (by rfl) ⟨487355, by rfl⟩ : syracuseStep 2599229 = 974711) (by norm_num)
theorem B6931277 : Blo 2053435 6931277 := bstep (se 3 (by rfl) ⟨1299614, by rfl⟩ : syracuseStep 6931277 = 2599229) B2599229
theorem B4620851 : Blo 2053435 4620851 := bstep (se 1 (by rfl) ⟨3465638, by rfl⟩ : syracuseStep 4620851 = 6931277) B6931277
theorem B3080567 : Blo 2053435 3080567 := bstep (se 1 (by rfl) ⟨2310425, by rfl⟩ : syracuseStep 3080567 = 4620851) B4620851
theorem B2053711 : Blo 2053435 2053711 := bstep (se 1 (by rfl) ⟨1540283, by rfl⟩ : syracuseStep 2053711 = 3080567) B3080567
theorem B3080573 : Blo 2053435 3080573 := bbase (se 3 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 3080573 = 1155215) (by norm_num)
theorem B2053715 : Blo 2053435 2053715 := bstep (se 1 (by rfl) ⟨1540286, by rfl⟩ : syracuseStep 2053715 = 3080573) B3080573
theorem B4620869 : Blo 2053435 4620869 := bbase (se 4 (by rfl) ⟨433206, by rfl⟩ : syracuseStep 4620869 = 866413) (by norm_num)
theorem B3080579 : Blo 2053435 3080579 := bstep (se 1 (by rfl) ⟨2310434, by rfl⟩ : syracuseStep 3080579 = 4620869) B4620869
theorem B2053719 : Blo 2053435 2053719 := bstep (se 1 (by rfl) ⟨1540289, by rfl⟩ : syracuseStep 2053719 = 3080579) B3080579
theorem B2193113 : Blo 2053435 2193113 := bbase (se 2 (by rfl) ⟨822417, by rfl⟩ : syracuseStep 2193113 = 1644835) (by norm_num)
theorem B5848301 : Blo 2053435 5848301 := bstep (se 3 (by rfl) ⟨1096556, by rfl⟩ : syracuseStep 5848301 = 2193113) B2193113
theorem B3898867 : Blo 2053435 3898867 := bstep (se 1 (by rfl) ⟨2924150, by rfl⟩ : syracuseStep 3898867 = 5848301) B5848301
theorem B5198489 : Blo 2053435 5198489 := bstep (se 2 (by rfl) ⟨1949433, by rfl⟩ : syracuseStep 5198489 = 3898867) B3898867
theorem B3465659 : Blo 2053435 3465659 := bstep (se 1 (by rfl) ⟨2599244, by rfl⟩ : syracuseStep 3465659 = 5198489) B5198489
theorem B2310439 : Blo 2053435 2310439 := bstep (se 1 (by rfl) ⟨1732829, by rfl⟩ : syracuseStep 2310439 = 3465659) B3465659
theorem B3080585 : Blo 2053435 3080585 := bstep (se 2 (by rfl) ⟨1155219, by rfl⟩ : syracuseStep 3080585 = 2310439) B2310439
theorem B2053723 : Blo 2053435 2053723 := bstep (se 1 (by rfl) ⟨1540292, by rfl⟩ : syracuseStep 2053723 = 3080585) B3080585
theorem B10396997 : Blo 2053435 10396997 := bbase (se 4 (by rfl) ⟨974718, by rfl⟩ : syracuseStep 10396997 = 1949437) (by norm_num)
theorem B6931331 : Blo 2053435 6931331 := bstep (se 1 (by rfl) ⟨5198498, by rfl⟩ : syracuseStep 6931331 = 10396997) B10396997
theorem B4620887 : Blo 2053435 4620887 := bstep (se 1 (by rfl) ⟨3465665, by rfl⟩ : syracuseStep 4620887 = 6931331) B6931331
theorem B3080591 : Blo 2053435 3080591 := bstep (se 1 (by rfl) ⟨2310443, by rfl⟩ : syracuseStep 3080591 = 4620887) B4620887
theorem B2053727 : Blo 2053435 2053727 := bstep (se 1 (by rfl) ⟨1540295, by rfl⟩ : syracuseStep 2053727 = 3080591) B3080591
theorem B3080597 : Blo 2053435 3080597 := bbase (se 6 (by rfl) ⟨72201, by rfl⟩ : syracuseStep 3080597 = 144403) (by norm_num)
theorem B2053731 : Blo 2053435 2053731 := bstep (se 1 (by rfl) ⟨1540298, by rfl⟩ : syracuseStep 2053731 = 3080597) B3080597
theorem B4934533 : Blo 2053435 4934533 := bbase (se 4 (by rfl) ⟨462612, by rfl⟩ : syracuseStep 4934533 = 925225) (by norm_num)
theorem B6579377 : Blo 2053435 6579377 := bstep (se 2 (by rfl) ⟨2467266, by rfl⟩ : syracuseStep 6579377 = 4934533) B4934533
theorem B4386251 : Blo 2053435 4386251 := bstep (se 1 (by rfl) ⟨3289688, by rfl⟩ : syracuseStep 4386251 = 6579377) B6579377
theorem B11696669 : Blo 2053435 11696669 := bstep (se 3 (by rfl) ⟨2193125, by rfl⟩ : syracuseStep 11696669 = 4386251) B4386251
theorem B7797779 : Blo 2053435 7797779 := bstep (se 1 (by rfl) ⟨5848334, by rfl⟩ : syracuseStep 7797779 = 11696669) B11696669
theorem B5198519 : Blo 2053435 5198519 := bstep (se 1 (by rfl) ⟨3898889, by rfl⟩ : syracuseStep 5198519 = 7797779) B7797779
theorem B3465679 : Blo 2053435 3465679 := bstep (se 1 (by rfl) ⟨2599259, by rfl⟩ : syracuseStep 3465679 = 5198519) B5198519
theorem B4620905 : Blo 2053435 4620905 := bstep (se 2 (by rfl) ⟨1732839, by rfl⟩ : syracuseStep 4620905 = 3465679) B3465679
theorem B3080603 : Blo 2053435 3080603 := bstep (se 1 (by rfl) ⟨2310452, by rfl⟩ : syracuseStep 3080603 = 4620905) B4620905
theorem B2053735 : Blo 2053435 2053735 := bstep (se 1 (by rfl) ⟨1540301, by rfl⟩ : syracuseStep 2053735 = 3080603) B3080603
theorem B2310457 : Blo 2053435 2310457 := bbase (se 2 (by rfl) ⟨866421, by rfl⟩ : syracuseStep 2310457 = 1732843) (by norm_num)
theorem B3080609 : Blo 2053435 3080609 := bstep (se 2 (by rfl) ⟨1155228, by rfl⟩ : syracuseStep 3080609 = 2310457) B2310457
theorem B2053739 : Blo 2053435 2053739 := bstep (se 1 (by rfl) ⟨1540304, by rfl⟩ : syracuseStep 2053739 = 3080609) B3080609
theorem B5848357 : Blo 2053435 5848357 := bbase (se 4 (by rfl) ⟨548283, by rfl⟩ : syracuseStep 5848357 = 1096567) (by norm_num)
theorem B7797809 : Blo 2053435 7797809 := bstep (se 2 (by rfl) ⟨2924178, by rfl⟩ : syracuseStep 7797809 = 5848357) B5848357
theorem B5198539 : Blo 2053435 5198539 := bstep (se 1 (by rfl) ⟨3898904, by rfl⟩ : syracuseStep 5198539 = 7797809) B7797809
theorem B6931385 : Blo 2053435 6931385 := bstep (se 2 (by rfl) ⟨2599269, by rfl⟩ : syracuseStep 6931385 = 5198539) B5198539
theorem B4620923 : Blo 2053435 4620923 := bstep (se 1 (by rfl) ⟨3465692, by rfl⟩ : syracuseStep 4620923 = 6931385) B6931385
theorem B3080615 : Blo 2053435 3080615 := bstep (se 1 (by rfl) ⟨2310461, by rfl⟩ : syracuseStep 3080615 = 4620923) B4620923
theorem B2053743 : Blo 2053435 2053743 := bstep (se 1 (by rfl) ⟨1540307, by rfl⟩ : syracuseStep 2053743 = 3080615) B3080615
theorem B3080621 : Blo 2053435 3080621 := bbase (se 3 (by rfl) ⟨577616, by rfl⟩ : syracuseStep 3080621 = 1155233) (by norm_num)
theorem B2053747 : Blo 2053435 2053747 := bstep (se 1 (by rfl) ⟨1540310, by rfl⟩ : syracuseStep 2053747 = 3080621) B3080621
theorem B4620941 : Blo 2053435 4620941 := bbase (se 3 (by rfl) ⟨866426, by rfl⟩ : syracuseStep 4620941 = 1732853) (by norm_num)
theorem B3080627 : Blo 2053435 3080627 := bstep (se 1 (by rfl) ⟨2310470, by rfl⟩ : syracuseStep 3080627 = 4620941) B4620941
theorem B2053751 : Blo 2053435 2053751 := bstep (se 1 (by rfl) ⟨1540313, by rfl⟩ : syracuseStep 2053751 = 3080627) B3080627
theorem B2599285 : Blo 2053435 2599285 := bbase (se 5 (by rfl) ⟨121841, by rfl⟩ : syracuseStep 2599285 = 243683) (by norm_num)
theorem B3465713 : Blo 2053435 3465713 := bstep (se 2 (by rfl) ⟨1299642, by rfl⟩ : syracuseStep 3465713 = 2599285) B2599285
theorem B2310475 : Blo 2053435 2310475 := bstep (se 1 (by rfl) ⟨1732856, by rfl⟩ : syracuseStep 2310475 = 3465713) B3465713
theorem B3080633 : Blo 2053435 3080633 := bstep (se 2 (by rfl) ⟨1155237, by rfl⟩ : syracuseStep 3080633 = 2310475) B2310475
theorem B2053755 : Blo 2053435 2053755 := bstep (se 1 (by rfl) ⟨1540316, by rfl⟩ : syracuseStep 2053755 = 3080633) B3080633
theorem B10539013 : Blo 2053435 10539013 := bbase (se 4 (by rfl) ⟨988032, by rfl⟩ : syracuseStep 10539013 = 1976065) (by norm_num)
theorem B14052017 : Blo 2053435 14052017 := bstep (se 2 (by rfl) ⟨5269506, by rfl⟩ : syracuseStep 14052017 = 10539013) B10539013
theorem B9368011 : Blo 2053435 9368011 := bstep (se 1 (by rfl) ⟨7026008, by rfl⟩ : syracuseStep 9368011 = 14052017) B14052017
theorem B12490681 : Blo 2053435 12490681 := bstep (se 2 (by rfl) ⟨4684005, by rfl⟩ : syracuseStep 12490681 = 9368011) B9368011
theorem B16654241 : Blo 2053435 16654241 := bstep (se 2 (by rfl) ⟨6245340, by rfl⟩ : syracuseStep 16654241 = 12490681) B12490681
theorem B11102827 : Blo 2053435 11102827 := bstep (se 1 (by rfl) ⟨8327120, by rfl⟩ : syracuseStep 11102827 = 16654241) B16654241
theorem B14803769 : Blo 2053435 14803769 := bstep (se 2 (by rfl) ⟨5551413, by rfl⟩ : syracuseStep 14803769 = 11102827) B11102827
theorem B39476717 : Blo 2053435 39476717 := bstep (se 3 (by rfl) ⟨7401884, by rfl⟩ : syracuseStep 39476717 = 14803769) B14803769
theorem B26317811 : Blo 2053435 26317811 := bstep (se 1 (by rfl) ⟨19738358, by rfl⟩ : syracuseStep 26317811 = 39476717) B39476717
theorem B17545207 : Blo 2053435 17545207 := bstep (se 1 (by rfl) ⟨13158905, by rfl⟩ : syracuseStep 17545207 = 26317811) B26317811
theorem B23393609 : Blo 2053435 23393609 := bstep (se 2 (by rfl) ⟨8772603, by rfl⟩ : syracuseStep 23393609 = 17545207) B17545207
theorem B15595739 : Blo 2053435 15595739 := bstep (se 1 (by rfl) ⟨11696804, by rfl⟩ : syracuseStep 15595739 = 23393609) B23393609
theorem B10397159 : Blo 2053435 10397159 := bstep (se 1 (by rfl) ⟨7797869, by rfl⟩ : syracuseStep 10397159 = 15595739) B15595739
theorem B6931439 : Blo 2053435 6931439 := bstep (se 1 (by rfl) ⟨5198579, by rfl⟩ : syracuseStep 6931439 = 10397159) B10397159
theorem B4620959 : Blo 2053435 4620959 := bstep (se 1 (by rfl) ⟨3465719, by rfl⟩ : syracuseStep 4620959 = 6931439) B6931439
theorem B3080639 : Blo 2053435 3080639 := bstep (se 1 (by rfl) ⟨2310479, by rfl⟩ : syracuseStep 3080639 = 4620959) B4620959
theorem B2053759 : Blo 2053435 2053759 := bstep (se 1 (by rfl) ⟨1540319, by rfl⟩ : syracuseStep 2053759 = 3080639) B3080639
theorem B3080645 : Blo 2053435 3080645 := bbase (se 4 (by rfl) ⟨288810, by rfl⟩ : syracuseStep 3080645 = 577621) (by norm_num)
theorem B2053763 : Blo 2053435 2053763 := bstep (se 1 (by rfl) ⟨1540322, by rfl⟩ : syracuseStep 2053763 = 3080645) B3080645
theorem B3465733 : Blo 2053435 3465733 := bbase (se 4 (by rfl) ⟨324912, by rfl⟩ : syracuseStep 3465733 = 649825) (by norm_num)
theorem B4620977 : Blo 2053435 4620977 := bstep (se 2 (by rfl) ⟨1732866, by rfl⟩ : syracuseStep 4620977 = 3465733) B3465733
theorem B3080651 : Blo 2053435 3080651 := bstep (se 1 (by rfl) ⟨2310488, by rfl⟩ : syracuseStep 3080651 = 4620977) B4620977
theorem B2053767 : Blo 2053435 2053767 := bstep (se 1 (by rfl) ⟨1540325, by rfl⟩ : syracuseStep 2053767 = 3080651) B3080651
theorem B2310493 : Blo 2053435 2310493 := bbase (se 3 (by rfl) ⟨433217, by rfl⟩ : syracuseStep 2310493 = 866435) (by norm_num)
theorem B3080657 : Blo 2053435 3080657 := bstep (se 2 (by rfl) ⟨1155246, by rfl⟩ : syracuseStep 3080657 = 2310493) B2310493
theorem B2053771 : Blo 2053435 2053771 := bstep (se 1 (by rfl) ⟨1540328, by rfl⟩ : syracuseStep 2053771 = 3080657) B3080657
theorem B6931493 : Blo 2053435 6931493 := bbase (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) (by norm_num)
theorem B4620995 : Blo 2053435 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B3080663 : Blo 2053435 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B2053775 : Blo 2053435 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B3080669 : Blo 2053435 3080669 := bbase (se 3 (by rfl) ⟨577625, by rfl⟩ : syracuseStep 3080669 = 1155251) (by norm_num)
theorem B2053779 : Blo 2053435 2053779 := bstep (se 1 (by rfl) ⟨1540334, by rfl⟩ : syracuseStep 2053779 = 3080669) B3080669
theorem B4621013 : Blo 2053435 4621013 := bbase (se 7 (by rfl) ⟨54152, by rfl⟩ : syracuseStep 4621013 = 108305) (by norm_num)
theorem B3080675 : Blo 2053435 3080675 := bstep (se 1 (by rfl) ⟨2310506, by rfl⟩ : syracuseStep 3080675 = 4621013) B4621013
theorem B2053783 : Blo 2053435 2053783 := bstep (se 1 (by rfl) ⟨1540337, by rfl⟩ : syracuseStep 2053783 = 3080675) B3080675
theorem B8772725 : Blo 2053435 8772725 := bbase (se 5 (by rfl) ⟨411221, by rfl⟩ : syracuseStep 8772725 = 822443) (by norm_num)
theorem B5848483 : Blo 2053435 5848483 := bstep (se 1 (by rfl) ⟨4386362, by rfl⟩ : syracuseStep 5848483 = 8772725) B8772725
theorem B7797977 : Blo 2053435 7797977 := bstep (se 2 (by rfl) ⟨2924241, by rfl⟩ : syracuseStep 7797977 = 5848483) B5848483
theorem B5198651 : Blo 2053435 5198651 := bstep (se 1 (by rfl) ⟨3898988, by rfl⟩ : syracuseStep 5198651 = 7797977) B7797977
theorem B3465767 : Blo 2053435 3465767 := bstep (se 1 (by rfl) ⟨2599325, by rfl⟩ : syracuseStep 3465767 = 5198651) B5198651
theorem B2310511 : Blo 2053435 2310511 := bstep (se 1 (by rfl) ⟨1732883, by rfl⟩ : syracuseStep 2310511 = 3465767) B3465767
theorem B3080681 : Blo 2053435 3080681 := bstep (se 2 (by rfl) ⟨1155255, by rfl⟩ : syracuseStep 3080681 = 2310511) B2310511
theorem B2053787 : Blo 2053435 2053787 := bstep (se 1 (by rfl) ⟨1540340, by rfl⟩ : syracuseStep 2053787 = 3080681) B3080681
theorem B2500997 : Blo 2053435 2500997 := bbase (se 4 (by rfl) ⟨234468, by rfl⟩ : syracuseStep 2500997 = 468937) (by norm_num)
theorem B6669325 : Blo 2053435 6669325 := bstep (se 3 (by rfl) ⟨1250498, by rfl⟩ : syracuseStep 6669325 = 2500997) B2500997
theorem B8892433 : Blo 2053435 8892433 := bstep (se 2 (by rfl) ⟨3334662, by rfl⟩ : syracuseStep 8892433 = 6669325) B6669325
theorem B11856577 : Blo 2053435 11856577 := bstep (se 2 (by rfl) ⟨4446216, by rfl⟩ : syracuseStep 11856577 = 8892433) B8892433
theorem B15808769 : Blo 2053435 15808769 := bstep (se 2 (by rfl) ⟨5928288, by rfl⟩ : syracuseStep 15808769 = 11856577) B11856577
theorem B10539179 : Blo 2053435 10539179 := bstep (se 1 (by rfl) ⟨7904384, by rfl⟩ : syracuseStep 10539179 = 15808769) B15808769
theorem B7026119 : Blo 2053435 7026119 := bstep (se 1 (by rfl) ⟨5269589, by rfl⟩ : syracuseStep 7026119 = 10539179) B10539179
theorem B4684079 : Blo 2053435 4684079 := bstep (se 1 (by rfl) ⟨3513059, by rfl⟩ : syracuseStep 4684079 = 7026119) B7026119
theorem B3122719 : Blo 2053435 3122719 := bstep (se 1 (by rfl) ⟨2342039, by rfl⟩ : syracuseStep 3122719 = 4684079) B4684079
theorem B16654501 : Blo 2053435 16654501 := bstep (se 4 (by rfl) ⟨1561359, by rfl⟩ : syracuseStep 16654501 = 3122719) B3122719
theorem B22206001 : Blo 2053435 22206001 := bstep (se 2 (by rfl) ⟨8327250, by rfl⟩ : syracuseStep 22206001 = 16654501) B16654501
theorem B29608001 : Blo 2053435 29608001 := bstep (se 2 (by rfl) ⟨11103000, by rfl⟩ : syracuseStep 29608001 = 22206001) B22206001
theorem B19738667 : Blo 2053435 19738667 := bstep (se 1 (by rfl) ⟨14804000, by rfl⟩ : syracuseStep 19738667 = 29608001) B29608001
theorem B13159111 : Blo 2053435 13159111 := bstep (se 1 (by rfl) ⟨9869333, by rfl⟩ : syracuseStep 13159111 = 19738667) B19738667
theorem B17545481 : Blo 2053435 17545481 := bstep (se 2 (by rfl) ⟨6579555, by rfl⟩ : syracuseStep 17545481 = 13159111) B13159111
theorem B11696987 : Blo 2053435 11696987 := bstep (se 1 (by rfl) ⟨8772740, by rfl⟩ : syracuseStep 11696987 = 17545481) B17545481
theorem B7797991 : Blo 2053435 7797991 := bstep (se 1 (by rfl) ⟨5848493, by rfl⟩ : syracuseStep 7797991 = 11696987) B11696987
theorem B10397321 : Blo 2053435 10397321 := bstep (se 2 (by rfl) ⟨3898995, by rfl⟩ : syracuseStep 10397321 = 7797991) B7797991
theorem B6931547 : Blo 2053435 6931547 := bstep (se 1 (by rfl) ⟨5198660, by rfl⟩ : syracuseStep 6931547 = 10397321) B10397321
theorem B4621031 : Blo 2053435 4621031 := bstep (se 1 (by rfl) ⟨3465773, by rfl⟩ : syracuseStep 4621031 = 6931547) B6931547
theorem B3080687 : Blo 2053435 3080687 := bstep (se 1 (by rfl) ⟨2310515, by rfl⟩ : syracuseStep 3080687 = 4621031) B4621031
theorem B2053791 : Blo 2053435 2053791 := bstep (se 1 (by rfl) ⟨1540343, by rfl⟩ : syracuseStep 2053791 = 3080687) B3080687
theorem B3080693 : Blo 2053435 3080693 := bbase (se 5 (by rfl) ⟨144407, by rfl⟩ : syracuseStep 3080693 = 288815) (by norm_num)
theorem B2053795 : Blo 2053435 2053795 := bstep (se 1 (by rfl) ⟨1540346, by rfl⟩ : syracuseStep 2053795 = 3080693) B3080693
theorem B5848517 : Blo 2053435 5848517 := bbase (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) (by norm_num)
theorem B3899011 : Blo 2053435 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B5198681 : Blo 2053435 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B3465787 : Blo 2053435 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B4621049 : Blo 2053435 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B3080699 : Blo 2053435 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B2053799 : Blo 2053435 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B2310529 : Blo 2053435 2310529 := bbase (se 2 (by rfl) ⟨866448, by rfl⟩ : syracuseStep 2310529 = 1732897) (by norm_num)
theorem B3080705 : Blo 2053435 3080705 := bstep (se 2 (by rfl) ⟨1155264, by rfl⟩ : syracuseStep 3080705 = 2310529) B2310529
theorem B2053803 : Blo 2053435 2053803 := bstep (se 1 (by rfl) ⟨1540352, by rfl⟩ : syracuseStep 2053803 = 3080705) B3080705
theorem B5198701 : Blo 2053435 5198701 := bbase (se 3 (by rfl) ⟨974756, by rfl⟩ : syracuseStep 5198701 = 1949513) (by norm_num)
theorem B6931601 : Blo 2053435 6931601 := bstep (se 2 (by rfl) ⟨2599350, by rfl⟩ : syracuseStep 6931601 = 5198701) B5198701
theorem B4621067 : Blo 2053435 4621067 := bstep (se 1 (by rfl) ⟨3465800, by rfl⟩ : syracuseStep 4621067 = 6931601) B6931601
theorem B3080711 : Blo 2053435 3080711 := bstep (se 1 (by rfl) ⟨2310533, by rfl⟩ : syracuseStep 3080711 = 4621067) B4621067
theorem B2053807 : Blo 2053435 2053807 := bstep (se 1 (by rfl) ⟨1540355, by rfl⟩ : syracuseStep 2053807 = 3080711) B3080711
theorem B3080717 : Blo 2053435 3080717 := bbase (se 3 (by rfl) ⟨577634, by rfl⟩ : syracuseStep 3080717 = 1155269) (by norm_num)
theorem B2053811 : Blo 2053435 2053811 := bstep (se 1 (by rfl) ⟨1540358, by rfl⟩ : syracuseStep 2053811 = 3080717) B3080717
theorem B4621085 : Blo 2053435 4621085 := bbase (se 3 (by rfl) ⟨866453, by rfl⟩ : syracuseStep 4621085 = 1732907) (by norm_num)
theorem B3080723 : Blo 2053435 3080723 := bstep (se 1 (by rfl) ⟨2310542, by rfl⟩ : syracuseStep 3080723 = 4621085) B4621085
theorem B2053815 : Blo 2053435 2053815 := bstep (se 1 (by rfl) ⟨1540361, by rfl⟩ : syracuseStep 2053815 = 3080723) B3080723
theorem B3465821 : Blo 2053435 3465821 := bbase (se 3 (by rfl) ⟨649841, by rfl⟩ : syracuseStep 3465821 = 1299683) (by norm_num)
theorem B2310547 : Blo 2053435 2310547 := bstep (se 1 (by rfl) ⟨1732910, by rfl⟩ : syracuseStep 2310547 = 3465821) B3465821
theorem B3080729 : Blo 2053435 3080729 := bstep (se 2 (by rfl) ⟨1155273, by rfl⟩ : syracuseStep 3080729 = 2310547) B2310547
theorem B2053819 : Blo 2053435 2053819 := bstep (se 1 (by rfl) ⟨1540364, by rfl⟩ : syracuseStep 2053819 = 3080729) B3080729
theorem B3289829 : Blo 2053435 3289829 := bbase (se 4 (by rfl) ⟨308421, by rfl⟩ : syracuseStep 3289829 = 616843) (by norm_num)
theorem B8772877 : Blo 2053435 8772877 := bstep (se 3 (by rfl) ⟨1644914, by rfl⟩ : syracuseStep 8772877 = 3289829) B3289829
theorem B11697169 : Blo 2053435 11697169 := bstep (se 2 (by rfl) ⟨4386438, by rfl⟩ : syracuseStep 11697169 = 8772877) B8772877
theorem B15596225 : Blo 2053435 15596225 := bstep (se 2 (by rfl) ⟨5848584, by rfl⟩ : syracuseStep 15596225 = 11697169) B11697169
theorem B10397483 : Blo 2053435 10397483 := bstep (se 1 (by rfl) ⟨7798112, by rfl⟩ : syracuseStep 10397483 = 15596225) B15596225
theorem B6931655 : Blo 2053435 6931655 := bstep (se 1 (by rfl) ⟨5198741, by rfl⟩ : syracuseStep 6931655 = 10397483) B10397483
theorem B4621103 : Blo 2053435 4621103 := bstep (se 1 (by rfl) ⟨3465827, by rfl⟩ : syracuseStep 4621103 = 6931655) B6931655
theorem B3080735 : Blo 2053435 3080735 := bstep (se 1 (by rfl) ⟨2310551, by rfl⟩ : syracuseStep 3080735 = 4621103) B4621103
theorem B2053823 : Blo 2053435 2053823 := bstep (se 1 (by rfl) ⟨1540367, by rfl⟩ : syracuseStep 2053823 = 3080735) B3080735
theorem B3080741 : Blo 2053435 3080741 := bbase (se 4 (by rfl) ⟨288819, by rfl⟩ : syracuseStep 3080741 = 577639) (by norm_num)
theorem B2053827 : Blo 2053435 2053827 := bstep (se 1 (by rfl) ⟨1540370, by rfl⟩ : syracuseStep 2053827 = 3080741) B3080741
theorem B2599381 : Blo 2053435 2599381 := bbase (se 7 (by rfl) ⟨30461, by rfl⟩ : syracuseStep 2599381 = 60923) (by norm_num)
theorem B3465841 : Blo 2053435 3465841 := bstep (se 2 (by rfl) ⟨1299690, by rfl⟩ : syracuseStep 3465841 = 2599381) B2599381
theorem B4621121 : Blo 2053435 4621121 := bstep (se 2 (by rfl) ⟨1732920, by rfl⟩ : syracuseStep 4621121 = 3465841) B3465841
theorem B3080747 : Blo 2053435 3080747 := bstep (se 1 (by rfl) ⟨2310560, by rfl⟩ : syracuseStep 3080747 = 4621121) B4621121
theorem B2053831 : Blo 2053435 2053831 := bstep (se 1 (by rfl) ⟨1540373, by rfl⟩ : syracuseStep 2053831 = 3080747) B3080747
theorem B2310565 : Blo 2053435 2310565 := bbase (se 4 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 2310565 = 433231) (by norm_num)
theorem B3080753 : Blo 2053435 3080753 := bstep (se 2 (by rfl) ⟨1155282, by rfl⟩ : syracuseStep 3080753 = 2310565) B2310565
theorem B2053835 : Blo 2053435 2053835 := bstep (se 1 (by rfl) ⟨1540376, by rfl⟩ : syracuseStep 2053835 = 3080753) B3080753
theorem B5139533 : Blo 2053435 5139533 := bbase (se 3 (by rfl) ⟨963662, by rfl⟩ : syracuseStep 5139533 = 1927325) (by norm_num)
theorem B13705421 : Blo 2053435 13705421 := bstep (se 3 (by rfl) ⟨2569766, by rfl⟩ : syracuseStep 13705421 = 5139533) B5139533
theorem B36547789 : Blo 2053435 36547789 := bstep (se 3 (by rfl) ⟨6852710, by rfl⟩ : syracuseStep 36547789 = 13705421) B13705421
theorem B48730385 : Blo 2053435 48730385 := bstep (se 2 (by rfl) ⟨18273894, by rfl⟩ : syracuseStep 48730385 = 36547789) B36547789
theorem B32486923 : Blo 2053435 32486923 := bstep (se 1 (by rfl) ⟨24365192, by rfl⟩ : syracuseStep 32486923 = 48730385) B48730385
theorem B43315897 : Blo 2053435 43315897 := bstep (se 2 (by rfl) ⟨16243461, by rfl⟩ : syracuseStep 43315897 = 32486923) B32486923
theorem B57754529 : Blo 2053435 57754529 := bstep (se 2 (by rfl) ⟨21657948, by rfl⟩ : syracuseStep 57754529 = 43315897) B43315897
theorem B38503019 : Blo 2053435 38503019 := bstep (se 1 (by rfl) ⟨28877264, by rfl⟩ : syracuseStep 38503019 = 57754529) B57754529
theorem B25668679 : Blo 2053435 25668679 := bstep (se 1 (by rfl) ⟨19251509, by rfl⟩ : syracuseStep 25668679 = 38503019) B38503019
theorem B34224905 : Blo 2053435 34224905 := bstep (se 2 (by rfl) ⟨12834339, by rfl⟩ : syracuseStep 34224905 = 25668679) B25668679
theorem B22816603 : Blo 2053435 22816603 := bstep (se 1 (by rfl) ⟨17112452, by rfl⟩ : syracuseStep 22816603 = 34224905) B34224905
theorem B30422137 : Blo 2053435 30422137 := bstep (se 2 (by rfl) ⟨11408301, by rfl⟩ : syracuseStep 30422137 = 22816603) B22816603
theorem B40562849 : Blo 2053435 40562849 := bstep (se 2 (by rfl) ⟨15211068, by rfl⟩ : syracuseStep 40562849 = 30422137) B30422137
theorem B27041899 : Blo 2053435 27041899 := bstep (se 1 (by rfl) ⟨20281424, by rfl⟩ : syracuseStep 27041899 = 40562849) B40562849
theorem B36055865 : Blo 2053435 36055865 := bstep (se 2 (by rfl) ⟨13520949, by rfl⟩ : syracuseStep 36055865 = 27041899) B27041899
theorem B24037243 : Blo 2053435 24037243 := bstep (se 1 (by rfl) ⟨18027932, by rfl⟩ : syracuseStep 24037243 = 36055865) B36055865
theorem B128198629 : Blo 2053435 128198629 := bstep (se 4 (by rfl) ⟨12018621, by rfl⟩ : syracuseStep 128198629 = 24037243) B24037243
theorem B170931505 : Blo 2053435 170931505 := bstep (se 2 (by rfl) ⟨64099314, by rfl⟩ : syracuseStep 170931505 = 128198629) B128198629
theorem B227908673 : Blo 2053435 227908673 := bstep (se 2 (by rfl) ⟨85465752, by rfl⟩ : syracuseStep 227908673 = 170931505) B170931505
theorem B151939115 : Blo 2053435 151939115 := bstep (se 1 (by rfl) ⟨113954336, by rfl⟩ : syracuseStep 151939115 = 227908673) B227908673
theorem B101292743 : Blo 2053435 101292743 := bstep (se 1 (by rfl) ⟨75969557, by rfl⟩ : syracuseStep 101292743 = 151939115) B151939115
theorem B67528495 : Blo 2053435 67528495 := bstep (se 1 (by rfl) ⟨50646371, by rfl⟩ : syracuseStep 67528495 = 101292743) B101292743
theorem B90037993 : Blo 2053435 90037993 := bstep (se 2 (by rfl) ⟨33764247, by rfl⟩ : syracuseStep 90037993 = 67528495) B67528495
theorem B120050657 : Blo 2053435 120050657 := bstep (se 2 (by rfl) ⟨45018996, by rfl⟩ : syracuseStep 120050657 = 90037993) B90037993
theorem B80033771 : Blo 2053435 80033771 := bstep (se 1 (by rfl) ⟨60025328, by rfl⟩ : syracuseStep 80033771 = 120050657) B120050657
theorem B53355847 : Blo 2053435 53355847 := bstep (se 1 (by rfl) ⟨40016885, by rfl⟩ : syracuseStep 53355847 = 80033771) B80033771
theorem B71141129 : Blo 2053435 71141129 := bstep (se 2 (by rfl) ⟨26677923, by rfl⟩ : syracuseStep 71141129 = 53355847) B53355847
theorem B47427419 : Blo 2053435 47427419 := bstep (se 1 (by rfl) ⟨35570564, by rfl⟩ : syracuseStep 47427419 = 71141129) B71141129
theorem B31618279 : Blo 2053435 31618279 := bstep (se 1 (by rfl) ⟨23713709, by rfl⟩ : syracuseStep 31618279 = 47427419) B47427419
theorem B42157705 : Blo 2053435 42157705 := bstep (se 2 (by rfl) ⟨15809139, by rfl⟩ : syracuseStep 42157705 = 31618279) B31618279
theorem B56210273 : Blo 2053435 56210273 := bstep (se 2 (by rfl) ⟨21078852, by rfl⟩ : syracuseStep 56210273 = 42157705) B42157705
theorem B37473515 : Blo 2053435 37473515 := bstep (se 1 (by rfl) ⟨28105136, by rfl⟩ : syracuseStep 37473515 = 56210273) B56210273
theorem B24982343 : Blo 2053435 24982343 := bstep (se 1 (by rfl) ⟨18736757, by rfl⟩ : syracuseStep 24982343 = 37473515) B37473515
theorem B16654895 : Blo 2053435 16654895 := bstep (se 1 (by rfl) ⟨12491171, by rfl⟩ : syracuseStep 16654895 = 24982343) B24982343
theorem B11103263 : Blo 2053435 11103263 := bstep (se 1 (by rfl) ⟨8327447, by rfl⟩ : syracuseStep 11103263 = 16654895) B16654895
theorem B7402175 : Blo 2053435 7402175 := bstep (se 1 (by rfl) ⟨5551631, by rfl⟩ : syracuseStep 7402175 = 11103263) B11103263
theorem B4934783 : Blo 2053435 4934783 := bstep (se 1 (by rfl) ⟨3701087, by rfl⟩ : syracuseStep 4934783 = 7402175) B7402175
theorem B13159421 : Blo 2053435 13159421 := bstep (se 3 (by rfl) ⟨2467391, by rfl⟩ : syracuseStep 13159421 = 4934783) B4934783
theorem B8772947 : Blo 2053435 8772947 := bstep (se 1 (by rfl) ⟨6579710, by rfl⟩ : syracuseStep 8772947 = 13159421) B13159421
theorem B5848631 : Blo 2053435 5848631 := bstep (se 1 (by rfl) ⟨4386473, by rfl⟩ : syracuseStep 5848631 = 8772947) B8772947
theorem B3899087 : Blo 2053435 3899087 := bstep (se 1 (by rfl) ⟨2924315, by rfl⟩ : syracuseStep 3899087 = 5848631) B5848631
theorem B2599391 : Blo 2053435 2599391 := bstep (se 1 (by rfl) ⟨1949543, by rfl⟩ : syracuseStep 2599391 = 3899087) B3899087
theorem B6931709 : Blo 2053435 6931709 := bstep (se 3 (by rfl) ⟨1299695, by rfl⟩ : syracuseStep 6931709 = 2599391) B2599391
theorem B4621139 : Blo 2053435 4621139 := bstep (se 1 (by rfl) ⟨3465854, by rfl⟩ : syracuseStep 4621139 = 6931709) B6931709
theorem B3080759 : Blo 2053435 3080759 := bstep (se 1 (by rfl) ⟨2310569, by rfl⟩ : syracuseStep 3080759 = 4621139) B4621139
theorem B2053839 : Blo 2053435 2053839 := bstep (se 1 (by rfl) ⟨1540379, by rfl⟩ : syracuseStep 2053839 = 3080759) B3080759
theorem B3080765 : Blo 2053435 3080765 := bbase (se 3 (by rfl) ⟨577643, by rfl⟩ : syracuseStep 3080765 = 1155287) (by norm_num)
theorem B2053843 : Blo 2053435 2053843 := bstep (se 1 (by rfl) ⟨1540382, by rfl⟩ : syracuseStep 2053843 = 3080765) B3080765
theorem B4621157 : Blo 2053435 4621157 := bbase (se 4 (by rfl) ⟨433233, by rfl⟩ : syracuseStep 4621157 = 866467) (by norm_num)
theorem B3080771 : Blo 2053435 3080771 := bstep (se 1 (by rfl) ⟨2310578, by rfl⟩ : syracuseStep 3080771 = 4621157) B4621157
theorem B2053847 : Blo 2053435 2053847 := bstep (se 1 (by rfl) ⟨1540385, by rfl⟩ : syracuseStep 2053847 = 3080771) B3080771
theorem B5198813 : Blo 2053435 5198813 := bbase (se 3 (by rfl) ⟨974777, by rfl⟩ : syracuseStep 5198813 = 1949555) (by norm_num)
theorem B3465875 : Blo 2053435 3465875 := bstep (se 1 (by rfl) ⟨2599406, by rfl⟩ : syracuseStep 3465875 = 5198813) B5198813
theorem B2310583 : Blo 2053435 2310583 := bstep (se 1 (by rfl) ⟨1732937, by rfl⟩ : syracuseStep 2310583 = 3465875) B3465875
theorem B3080777 : Blo 2053435 3080777 := bstep (se 2 (by rfl) ⟨1155291, by rfl⟩ : syracuseStep 3080777 = 2310583) B2310583
theorem B2053851 : Blo 2053435 2053851 := bstep (se 1 (by rfl) ⟨1540388, by rfl⟩ : syracuseStep 2053851 = 3080777) B3080777
theorem B3899117 : Blo 2053435 3899117 := bbase (se 3 (by rfl) ⟨731084, by rfl⟩ : syracuseStep 3899117 = 1462169) (by norm_num)
theorem B10397645 : Blo 2053435 10397645 := bstep (se 3 (by rfl) ⟨1949558, by rfl⟩ : syracuseStep 10397645 = 3899117) B3899117
theorem B6931763 : Blo 2053435 6931763 := bstep (se 1 (by rfl) ⟨5198822, by rfl⟩ : syracuseStep 6931763 = 10397645) B10397645
theorem B4621175 : Blo 2053435 4621175 := bstep (se 1 (by rfl) ⟨3465881, by rfl⟩ : syracuseStep 4621175 = 6931763) B6931763
theorem B3080783 : Blo 2053435 3080783 := bstep (se 1 (by rfl) ⟨2310587, by rfl⟩ : syracuseStep 3080783 = 4621175) B4621175
theorem B2053855 : Blo 2053435 2053855 := bstep (se 1 (by rfl) ⟨1540391, by rfl⟩ : syracuseStep 2053855 = 3080783) B3080783
theorem B3080789 : Blo 2053435 3080789 := bbase (se 8 (by rfl) ⟨18051, by rfl⟩ : syracuseStep 3080789 = 36103) (by norm_num)
theorem B2053859 : Blo 2053435 2053859 := bstep (se 1 (by rfl) ⟨1540394, by rfl⟩ : syracuseStep 2053859 = 3080789) B3080789
theorem B7402261 : Blo 2053435 7402261 := bbase (se 6 (by rfl) ⟨173490, by rfl⟩ : syracuseStep 7402261 = 346981) (by norm_num)
theorem B9869681 : Blo 2053435 9869681 := bstep (se 2 (by rfl) ⟨3701130, by rfl⟩ : syracuseStep 9869681 = 7402261) B7402261
theorem B6579787 : Blo 2053435 6579787 := bstep (se 1 (by rfl) ⟨4934840, by rfl⟩ : syracuseStep 6579787 = 9869681) B9869681
theorem B8773049 : Blo 2053435 8773049 := bstep (se 2 (by rfl) ⟨3289893, by rfl⟩ : syracuseStep 8773049 = 6579787) B6579787
theorem B5848699 : Blo 2053435 5848699 := bstep (se 1 (by rfl) ⟨4386524, by rfl⟩ : syracuseStep 5848699 = 8773049) B8773049
theorem B7798265 : Blo 2053435 7798265 := bstep (se 2 (by rfl) ⟨2924349, by rfl⟩ : syracuseStep 7798265 = 5848699) B5848699
theorem B5198843 : Blo 2053435 5198843 := bstep (se 1 (by rfl) ⟨3899132, by rfl⟩ : syracuseStep 5198843 = 7798265) B7798265
theorem B3465895 : Blo 2053435 3465895 := bstep (se 1 (by rfl) ⟨2599421, by rfl⟩ : syracuseStep 3465895 = 5198843) B5198843
theorem B4621193 : Blo 2053435 4621193 := bstep (se 2 (by rfl) ⟨1732947, by rfl⟩ : syracuseStep 4621193 = 3465895) B3465895
theorem B3080795 : Blo 2053435 3080795 := bstep (se 1 (by rfl) ⟨2310596, by rfl⟩ : syracuseStep 3080795 = 4621193) B4621193
theorem B2053863 : Blo 2053435 2053863 := bstep (se 1 (by rfl) ⟨1540397, by rfl⟩ : syracuseStep 2053863 = 3080795) B3080795
theorem B2310601 : Blo 2053435 2310601 := bbase (se 2 (by rfl) ⟨866475, by rfl⟩ : syracuseStep 2310601 = 1732951) (by norm_num)
theorem B3080801 : Blo 2053435 3080801 := bstep (se 2 (by rfl) ⟨1155300, by rfl⟩ : syracuseStep 3080801 = 2310601) B2310601
theorem B2053867 : Blo 2053435 2053867 := bstep (se 1 (by rfl) ⟨1540400, by rfl⟩ : syracuseStep 2053867 = 3080801) B3080801
theorem B17546165 : Blo 2053435 17546165 := bbase (se 5 (by rfl) ⟨822476, by rfl⟩ : syracuseStep 17546165 = 1644953) (by norm_num)
theorem B11697443 : Blo 2053435 11697443 := bstep (se 1 (by rfl) ⟨8773082, by rfl⟩ : syracuseStep 11697443 = 17546165) B17546165
theorem B7798295 : Blo 2053435 7798295 := bstep (se 1 (by rfl) ⟨5848721, by rfl⟩ : syracuseStep 7798295 = 11697443) B11697443
theorem B5198863 : Blo 2053435 5198863 := bstep (se 1 (by rfl) ⟨3899147, by rfl⟩ : syracuseStep 5198863 = 7798295) B7798295
theorem B6931817 : Blo 2053435 6931817 := bstep (se 2 (by rfl) ⟨2599431, by rfl⟩ : syracuseStep 6931817 = 5198863) B5198863
theorem B4621211 : Blo 2053435 4621211 := bstep (se 1 (by rfl) ⟨3465908, by rfl⟩ : syracuseStep 4621211 = 6931817) B6931817
theorem B3080807 : Blo 2053435 3080807 := bstep (se 1 (by rfl) ⟨2310605, by rfl⟩ : syracuseStep 3080807 = 4621211) B4621211
theorem B2053871 : Blo 2053435 2053871 := bstep (se 1 (by rfl) ⟨1540403, by rfl⟩ : syracuseStep 2053871 = 3080807) B3080807
theorem B3080813 : Blo 2053435 3080813 := bbase (se 3 (by rfl) ⟨577652, by rfl⟩ : syracuseStep 3080813 = 1155305) (by norm_num)
theorem B2053875 : Blo 2053435 2053875 := bstep (se 1 (by rfl) ⟨1540406, by rfl⟩ : syracuseStep 2053875 = 3080813) B3080813
theorem B4621229 : Blo 2053435 4621229 := bbase (se 3 (by rfl) ⟨866480, by rfl⟩ : syracuseStep 4621229 = 1732961) (by norm_num)
theorem B3080819 : Blo 2053435 3080819 := bstep (se 1 (by rfl) ⟨2310614, by rfl⟩ : syracuseStep 3080819 = 4621229) B4621229
theorem B2053879 : Blo 2053435 2053879 := bstep (se 1 (by rfl) ⟨1540409, by rfl⟩ : syracuseStep 2053879 = 3080819) B3080819
theorem B5848757 : Blo 2053435 5848757 := bbase (se 5 (by rfl) ⟨274160, by rfl⟩ : syracuseStep 5848757 = 548321) (by norm_num)
theorem B3899171 : Blo 2053435 3899171 := bstep (se 1 (by rfl) ⟨2924378, by rfl⟩ : syracuseStep 3899171 = 5848757) B5848757
theorem B2599447 : Blo 2053435 2599447 := bstep (se 1 (by rfl) ⟨1949585, by rfl⟩ : syracuseStep 2599447 = 3899171) B3899171
theorem B3465929 : Blo 2053435 3465929 := bstep (se 2 (by rfl) ⟨1299723, by rfl⟩ : syracuseStep 3465929 = 2599447) B2599447
theorem B2310619 : Blo 2053435 2310619 := bstep (se 1 (by rfl) ⟨1732964, by rfl⟩ : syracuseStep 2310619 = 3465929) B3465929
theorem B3080825 : Blo 2053435 3080825 := bstep (se 2 (by rfl) ⟨1155309, by rfl⟩ : syracuseStep 3080825 = 2310619) B2310619
theorem B2053883 : Blo 2053435 2053883 := bstep (se 1 (by rfl) ⟨1540412, by rfl⟩ : syracuseStep 2053883 = 3080825) B3080825
theorem B2604889 : Blo 2053435 2604889 := bbase (se 2 (by rfl) ⟨976833, by rfl⟩ : syracuseStep 2604889 = 1953667) (by norm_num)
theorem B13892741 : Blo 2053435 13892741 := bstep (se 4 (by rfl) ⟨1302444, by rfl⟩ : syracuseStep 13892741 = 2604889) B2604889
theorem B9261827 : Blo 2053435 9261827 := bstep (se 1 (by rfl) ⟨6946370, by rfl⟩ : syracuseStep 9261827 = 13892741) B13892741
theorem B6174551 : Blo 2053435 6174551 := bstep (se 1 (by rfl) ⟨4630913, by rfl⟩ : syracuseStep 6174551 = 9261827) B9261827
theorem B4116367 : Blo 2053435 4116367 := bstep (se 1 (by rfl) ⟨3087275, by rfl⟩ : syracuseStep 4116367 = 6174551) B6174551
theorem B5488489 : Blo 2053435 5488489 := bstep (se 2 (by rfl) ⟨2058183, by rfl⟩ : syracuseStep 5488489 = 4116367) B4116367
theorem B7317985 : Blo 2053435 7317985 := bstep (se 2 (by rfl) ⟨2744244, by rfl⟩ : syracuseStep 7317985 = 5488489) B5488489
theorem B9757313 : Blo 2053435 9757313 := bstep (se 2 (by rfl) ⟨3658992, by rfl⟩ : syracuseStep 9757313 = 7317985) B7317985
theorem B6504875 : Blo 2053435 6504875 := bstep (se 1 (by rfl) ⟨4878656, by rfl⟩ : syracuseStep 6504875 = 9757313) B9757313
theorem B4336583 : Blo 2053435 4336583 := bstep (se 1 (by rfl) ⟨3252437, by rfl⟩ : syracuseStep 4336583 = 6504875) B6504875
theorem B11564221 : Blo 2053435 11564221 := bstep (se 3 (by rfl) ⟨2168291, by rfl⟩ : syracuseStep 11564221 = 4336583) B4336583
theorem B15418961 : Blo 2053435 15418961 := bstep (se 2 (by rfl) ⟨5782110, by rfl⟩ : syracuseStep 15418961 = 11564221) B11564221
theorem B10279307 : Blo 2053435 10279307 := bstep (se 1 (by rfl) ⟨7709480, by rfl⟩ : syracuseStep 10279307 = 15418961) B15418961
theorem B6852871 : Blo 2053435 6852871 := bstep (se 1 (by rfl) ⟨5139653, by rfl⟩ : syracuseStep 6852871 = 10279307) B10279307
theorem B9137161 : Blo 2053435 9137161 := bstep (se 2 (by rfl) ⟨3426435, by rfl⟩ : syracuseStep 9137161 = 6852871) B6852871
theorem B12182881 : Blo 2053435 12182881 := bstep (se 2 (by rfl) ⟨4568580, by rfl⟩ : syracuseStep 12182881 = 9137161) B9137161
theorem B16243841 : Blo 2053435 16243841 := bstep (se 2 (by rfl) ⟨6091440, by rfl⟩ : syracuseStep 16243841 = 12182881) B12182881
theorem B10829227 : Blo 2053435 10829227 := bstep (se 1 (by rfl) ⟨8121920, by rfl⟩ : syracuseStep 10829227 = 16243841) B16243841
theorem B14438969 : Blo 2053435 14438969 := bstep (se 2 (by rfl) ⟨5414613, by rfl⟩ : syracuseStep 14438969 = 10829227) B10829227
theorem B9625979 : Blo 2053435 9625979 := bstep (se 1 (by rfl) ⟨7219484, by rfl⟩ : syracuseStep 9625979 = 14438969) B14438969
theorem B6417319 : Blo 2053435 6417319 := bstep (se 1 (by rfl) ⟨4812989, by rfl⟩ : syracuseStep 6417319 = 9625979) B9625979
theorem B8556425 : Blo 2053435 8556425 := bstep (se 2 (by rfl) ⟨3208659, by rfl⟩ : syracuseStep 8556425 = 6417319) B6417319
theorem B5704283 : Blo 2053435 5704283 := bstep (se 1 (by rfl) ⟨4278212, by rfl⟩ : syracuseStep 5704283 = 8556425) B8556425
theorem B15211421 : Blo 2053435 15211421 := bstep (se 3 (by rfl) ⟨2852141, by rfl⟩ : syracuseStep 15211421 = 5704283) B5704283
theorem B10140947 : Blo 2053435 10140947 := bstep (se 1 (by rfl) ⟨7605710, by rfl⟩ : syracuseStep 10140947 = 15211421) B15211421
theorem B6760631 : Blo 2053435 6760631 := bstep (se 1 (by rfl) ⟨5070473, by rfl⟩ : syracuseStep 6760631 = 10140947) B10140947
theorem B18028349 : Blo 2053435 18028349 := bstep (se 3 (by rfl) ⟨3380315, by rfl⟩ : syracuseStep 18028349 = 6760631) B6760631
theorem B12018899 : Blo 2053435 12018899 := bstep (se 1 (by rfl) ⟨9014174, by rfl⟩ : syracuseStep 12018899 = 18028349) B18028349
theorem B32050397 : Blo 2053435 32050397 := bstep (se 3 (by rfl) ⟨6009449, by rfl⟩ : syracuseStep 32050397 = 12018899) B12018899
theorem B21366931 : Blo 2053435 21366931 := bstep (se 1 (by rfl) ⟨16025198, by rfl⟩ : syracuseStep 21366931 = 32050397) B32050397
theorem B28489241 : Blo 2053435 28489241 := bstep (se 2 (by rfl) ⟨10683465, by rfl⟩ : syracuseStep 28489241 = 21366931) B21366931
theorem B18992827 : Blo 2053435 18992827 := bstep (se 1 (by rfl) ⟨14244620, by rfl⟩ : syracuseStep 18992827 = 28489241) B28489241
theorem B25323769 : Blo 2053435 25323769 := bstep (se 2 (by rfl) ⟨9496413, by rfl⟩ : syracuseStep 25323769 = 18992827) B18992827
theorem B33765025 : Blo 2053435 33765025 := bstep (se 2 (by rfl) ⟨12661884, by rfl⟩ : syracuseStep 33765025 = 25323769) B25323769
theorem B45020033 : Blo 2053435 45020033 := bstep (se 2 (by rfl) ⟨16882512, by rfl⟩ : syracuseStep 45020033 = 33765025) B33765025
theorem B30013355 : Blo 2053435 30013355 := bstep (se 1 (by rfl) ⟨22510016, by rfl⟩ : syracuseStep 30013355 = 45020033) B45020033
theorem B80035613 : Blo 2053435 80035613 := bstep (se 3 (by rfl) ⟨15006677, by rfl⟩ : syracuseStep 80035613 = 30013355) B30013355
theorem B53357075 : Blo 2053435 53357075 := bstep (se 1 (by rfl) ⟨40017806, by rfl⟩ : syracuseStep 53357075 = 80035613) B80035613
theorem B35571383 : Blo 2053435 35571383 := bstep (se 1 (by rfl) ⟨26678537, by rfl⟩ : syracuseStep 35571383 = 53357075) B53357075
theorem B23714255 : Blo 2053435 23714255 := bstep (se 1 (by rfl) ⟨17785691, by rfl⟩ : syracuseStep 23714255 = 35571383) B35571383
theorem B15809503 : Blo 2053435 15809503 := bstep (se 1 (by rfl) ⟨11857127, by rfl⟩ : syracuseStep 15809503 = 23714255) B23714255
theorem B21079337 : Blo 2053435 21079337 := bstep (se 2 (by rfl) ⟨7904751, by rfl⟩ : syracuseStep 21079337 = 15809503) B15809503
theorem B56211565 : Blo 2053435 56211565 := bstep (se 3 (by rfl) ⟨10539668, by rfl⟩ : syracuseStep 56211565 = 21079337) B21079337
theorem B74948753 : Blo 2053435 74948753 := bstep (se 2 (by rfl) ⟨28105782, by rfl⟩ : syracuseStep 74948753 = 56211565) B56211565
theorem B49965835 : Blo 2053435 49965835 := bstep (se 1 (by rfl) ⟨37474376, by rfl⟩ : syracuseStep 49965835 = 74948753) B74948753
theorem B66621113 : Blo 2053435 66621113 := bstep (se 2 (by rfl) ⟨24982917, by rfl⟩ : syracuseStep 66621113 = 49965835) B49965835
theorem B44414075 : Blo 2053435 44414075 := bstep (se 1 (by rfl) ⟨33310556, by rfl⟩ : syracuseStep 44414075 = 66621113) B66621113
theorem B29609383 : Blo 2053435 29609383 := bstep (se 1 (by rfl) ⟨22207037, by rfl⟩ : syracuseStep 29609383 = 44414075) B44414075
theorem B39479177 : Blo 2053435 39479177 := bstep (se 2 (by rfl) ⟨14804691, by rfl⟩ : syracuseStep 39479177 = 29609383) B29609383
theorem B26319451 : Blo 2053435 26319451 := bstep (se 1 (by rfl) ⟨19739588, by rfl⟩ : syracuseStep 26319451 = 39479177) B39479177
theorem B35092601 : Blo 2053435 35092601 := bstep (se 2 (by rfl) ⟨13159725, by rfl⟩ : syracuseStep 35092601 = 26319451) B26319451
theorem B23395067 : Blo 2053435 23395067 := bstep (se 1 (by rfl) ⟨17546300, by rfl⟩ : syracuseStep 23395067 = 35092601) B35092601
theorem B15596711 : Blo 2053435 15596711 := bstep (se 1 (by rfl) ⟨11697533, by rfl⟩ : syracuseStep 15596711 = 23395067) B23395067
theorem B10397807 : Blo 2053435 10397807 := bstep (se 1 (by rfl) ⟨7798355, by rfl⟩ : syracuseStep 10397807 = 15596711) B15596711
theorem B6931871 : Blo 2053435 6931871 := bstep (se 1 (by rfl) ⟨5198903, by rfl⟩ : syracuseStep 6931871 = 10397807) B10397807
theorem B4621247 : Blo 2053435 4621247 := bstep (se 1 (by rfl) ⟨3465935, by rfl⟩ : syracuseStep 4621247 = 6931871) B6931871
theorem B3080831 : Blo 2053435 3080831 := bstep (se 1 (by rfl) ⟨2310623, by rfl⟩ : syracuseStep 3080831 = 4621247) B4621247
theorem B2053887 : Blo 2053435 2053887 := bstep (se 1 (by rfl) ⟨1540415, by rfl⟩ : syracuseStep 2053887 = 3080831) B3080831
theorem B3080837 : Blo 2053435 3080837 := bbase (se 4 (by rfl) ⟨288828, by rfl⟩ : syracuseStep 3080837 = 577657) (by norm_num)
theorem B2053891 : Blo 2053435 2053891 := bstep (se 1 (by rfl) ⟨1540418, by rfl⟩ : syracuseStep 2053891 = 3080837) B3080837
theorem B3465949 : Blo 2053435 3465949 := bbase (se 3 (by rfl) ⟨649865, by rfl⟩ : syracuseStep 3465949 = 1299731) (by norm_num)
theorem B4621265 : Blo 2053435 4621265 := bstep (se 2 (by rfl) ⟨1732974, by rfl⟩ : syracuseStep 4621265 = 3465949) B3465949
theorem B3080843 : Blo 2053435 3080843 := bstep (se 1 (by rfl) ⟨2310632, by rfl⟩ : syracuseStep 3080843 = 4621265) B4621265
theorem B2053895 : Blo 2053435 2053895 := bstep (se 1 (by rfl) ⟨1540421, by rfl⟩ : syracuseStep 2053895 = 3080843) B3080843
theorem B2310637 : Blo 2053435 2310637 := bbase (se 3 (by rfl) ⟨433244, by rfl⟩ : syracuseStep 2310637 = 866489) (by norm_num)
theorem B3080849 : Blo 2053435 3080849 := bstep (se 2 (by rfl) ⟨1155318, by rfl⟩ : syracuseStep 3080849 = 2310637) B2310637
theorem B2053899 : Blo 2053435 2053899 := bstep (se 1 (by rfl) ⟨1540424, by rfl⟩ : syracuseStep 2053899 = 3080849) B3080849
theorem B6931925 : Blo 2053435 6931925 := bbase (se 7 (by rfl) ⟨81233, by rfl⟩ : syracuseStep 6931925 = 162467) (by norm_num)
theorem B4621283 : Blo 2053435 4621283 := bstep (se 1 (by rfl) ⟨3465962, by rfl⟩ : syracuseStep 4621283 = 6931925) B6931925
theorem B3080855 : Blo 2053435 3080855 := bstep (se 1 (by rfl) ⟨2310641, by rfl⟩ : syracuseStep 3080855 = 4621283) B4621283
theorem B2053903 : Blo 2053435 2053903 := bstep (se 1 (by rfl) ⟨1540427, by rfl⟩ : syracuseStep 2053903 = 3080855) B3080855
theorem B3080861 : Blo 2053435 3080861 := bbase (se 3 (by rfl) ⟨577661, by rfl⟩ : syracuseStep 3080861 = 1155323) (by norm_num)
theorem B2053907 : Blo 2053435 2053907 := bstep (se 1 (by rfl) ⟨1540430, by rfl⟩ : syracuseStep 2053907 = 3080861) B3080861
theorem B4621301 : Blo 2053435 4621301 := bbase (se 5 (by rfl) ⟨216623, by rfl⟩ : syracuseStep 4621301 = 433247) (by norm_num)
theorem B3080867 : Blo 2053435 3080867 := bstep (se 1 (by rfl) ⟨2310650, by rfl⟩ : syracuseStep 3080867 = 4621301) B4621301
theorem B2053911 : Blo 2053435 2053911 := bstep (se 1 (by rfl) ⟨1540433, by rfl⟩ : syracuseStep 2053911 = 3080867) B3080867
theorem B14244821 : Blo 2053435 14244821 := bbase (se 7 (by rfl) ⟨166931, by rfl⟩ : syracuseStep 14244821 = 333863) (by norm_num)
theorem B9496547 : Blo 2053435 9496547 := bstep (se 1 (by rfl) ⟨7122410, by rfl⟩ : syracuseStep 9496547 = 14244821) B14244821
theorem B6331031 : Blo 2053435 6331031 := bstep (se 1 (by rfl) ⟨4748273, by rfl⟩ : syracuseStep 6331031 = 9496547) B9496547
theorem B4220687 : Blo 2053435 4220687 := bstep (se 1 (by rfl) ⟨3165515, by rfl⟩ : syracuseStep 4220687 = 6331031) B6331031
theorem B11255165 : Blo 2053435 11255165 := bstep (se 3 (by rfl) ⟨2110343, by rfl⟩ : syracuseStep 11255165 = 4220687) B4220687
theorem B7503443 : Blo 2053435 7503443 := bstep (se 1 (by rfl) ⟨5627582, by rfl⟩ : syracuseStep 7503443 = 11255165) B11255165
theorem B5002295 : Blo 2053435 5002295 := bstep (se 1 (by rfl) ⟨3751721, by rfl⟩ : syracuseStep 5002295 = 7503443) B7503443
theorem B13339453 : Blo 2053435 13339453 := bstep (se 3 (by rfl) ⟨2501147, by rfl⟩ : syracuseStep 13339453 = 5002295) B5002295
theorem B17785937 : Blo 2053435 17785937 := bstep (se 2 (by rfl) ⟨6669726, by rfl⟩ : syracuseStep 17785937 = 13339453) B13339453
theorem B47429165 : Blo 2053435 47429165 := bstep (se 3 (by rfl) ⟨8892968, by rfl⟩ : syracuseStep 47429165 = 17785937) B17785937
theorem B126477773 : Blo 2053435 126477773 := bstep (se 3 (by rfl) ⟨23714582, by rfl⟩ : syracuseStep 126477773 = 47429165) B47429165
theorem B84318515 : Blo 2053435 84318515 := bstep (se 1 (by rfl) ⟨63238886, by rfl⟩ : syracuseStep 84318515 = 126477773) B126477773
theorem B56212343 : Blo 2053435 56212343 := bstep (se 1 (by rfl) ⟨42159257, by rfl⟩ : syracuseStep 56212343 = 84318515) B84318515
theorem B37474895 : Blo 2053435 37474895 := bstep (se 1 (by rfl) ⟨28106171, by rfl⟩ : syracuseStep 37474895 = 56212343) B56212343
theorem B24983263 : Blo 2053435 24983263 := bstep (se 1 (by rfl) ⟨18737447, by rfl⟩ : syracuseStep 24983263 = 37474895) B37474895
theorem B33311017 : Blo 2053435 33311017 := bstep (se 2 (by rfl) ⟨12491631, by rfl⟩ : syracuseStep 33311017 = 24983263) B24983263
theorem B44414689 : Blo 2053435 44414689 := bstep (se 2 (by rfl) ⟨16655508, by rfl⟩ : syracuseStep 44414689 = 33311017) B33311017
theorem B59219585 : Blo 2053435 59219585 := bstep (se 2 (by rfl) ⟨22207344, by rfl⟩ : syracuseStep 59219585 = 44414689) B44414689
theorem B39479723 : Blo 2053435 39479723 := bstep (se 1 (by rfl) ⟨29609792, by rfl⟩ : syracuseStep 39479723 = 59219585) B59219585
theorem B26319815 : Blo 2053435 26319815 := bstep (se 1 (by rfl) ⟨19739861, by rfl⟩ : syracuseStep 26319815 = 39479723) B39479723
theorem B17546543 : Blo 2053435 17546543 := bstep (se 1 (by rfl) ⟨13159907, by rfl⟩ : syracuseStep 17546543 = 26319815) B26319815
theorem B11697695 : Blo 2053435 11697695 := bstep (se 1 (by rfl) ⟨8773271, by rfl⟩ : syracuseStep 11697695 = 17546543) B17546543
theorem B7798463 : Blo 2053435 7798463 := bstep (se 1 (by rfl) ⟨5848847, by rfl⟩ : syracuseStep 7798463 = 11697695) B11697695
theorem B5198975 : Blo 2053435 5198975 := bstep (se 1 (by rfl) ⟨3899231, by rfl⟩ : syracuseStep 5198975 = 7798463) B7798463
theorem B3465983 : Blo 2053435 3465983 := bstep (se 1 (by rfl) ⟨2599487, by rfl⟩ : syracuseStep 3465983 = 5198975) B5198975
theorem B2310655 : Blo 2053435 2310655 := bstep (se 1 (by rfl) ⟨1732991, by rfl⟩ : syracuseStep 2310655 = 3465983) B3465983
theorem B3080873 : Blo 2053435 3080873 := bstep (se 2 (by rfl) ⟨1155327, by rfl⟩ : syracuseStep 3080873 = 2310655) B2310655
theorem B2053915 : Blo 2053435 2053915 := bstep (se 1 (by rfl) ⟨1540436, by rfl⟩ : syracuseStep 2053915 = 3080873) B3080873
theorem B2924429 : Blo 2053435 2924429 := bbase (se 3 (by rfl) ⟨548330, by rfl⟩ : syracuseStep 2924429 = 1096661) (by norm_num)
theorem B7798477 : Blo 2053435 7798477 := bstep (se 3 (by rfl) ⟨1462214, by rfl⟩ : syracuseStep 7798477 = 2924429) B2924429
theorem B10397969 : Blo 2053435 10397969 := bstep (se 2 (by rfl) ⟨3899238, by rfl⟩ : syracuseStep 10397969 = 7798477) B7798477
theorem B6931979 : Blo 2053435 6931979 := bstep (se 1 (by rfl) ⟨5198984, by rfl⟩ : syracuseStep 6931979 = 10397969) B10397969
theorem B4621319 : Blo 2053435 4621319 := bstep (se 1 (by rfl) ⟨3465989, by rfl⟩ : syracuseStep 4621319 = 6931979) B6931979
theorem B3080879 : Blo 2053435 3080879 := bstep (se 1 (by rfl) ⟨2310659, by rfl⟩ : syracuseStep 3080879 = 4621319) B4621319
theorem B2053919 : Blo 2053435 2053919 := bstep (se 1 (by rfl) ⟨1540439, by rfl⟩ : syracuseStep 2053919 = 3080879) B3080879
theorem B3080885 : Blo 2053435 3080885 := bbase (se 5 (by rfl) ⟨144416, by rfl⟩ : syracuseStep 3080885 = 288833) (by norm_num)
theorem B2053923 : Blo 2053435 2053923 := bstep (se 1 (by rfl) ⟨1540442, by rfl⟩ : syracuseStep 2053923 = 3080885) B3080885
theorem B5199005 : Blo 2053435 5199005 := bbase (se 3 (by rfl) ⟨974813, by rfl⟩ : syracuseStep 5199005 = 1949627) (by norm_num)
theorem B3466003 : Blo 2053435 3466003 := bstep (se 1 (by rfl) ⟨2599502, by rfl⟩ : syracuseStep 3466003 = 5199005) B5199005
theorem B4621337 : Blo 2053435 4621337 := bstep (se 2 (by rfl) ⟨1733001, by rfl⟩ : syracuseStep 4621337 = 3466003) B3466003
theorem B3080891 : Blo 2053435 3080891 := bstep (se 1 (by rfl) ⟨2310668, by rfl⟩ : syracuseStep 3080891 = 4621337) B4621337
theorem B2053927 : Blo 2053435 2053927 := bstep (se 1 (by rfl) ⟨1540445, by rfl⟩ : syracuseStep 2053927 = 3080891) B3080891
theorem B2310673 : Blo 2053435 2310673 := bbase (se 2 (by rfl) ⟨866502, by rfl⟩ : syracuseStep 2310673 = 1733005) (by norm_num)
theorem B3080897 : Blo 2053435 3080897 := bstep (se 2 (by rfl) ⟨1155336, by rfl⟩ : syracuseStep 3080897 = 2310673) B2310673
theorem B2053931 : Blo 2053435 2053931 := bstep (se 1 (by rfl) ⟨1540448, by rfl⟩ : syracuseStep 2053931 = 3080897) B3080897
theorem B3899269 : Blo 2053435 3899269 := bbase (se 4 (by rfl) ⟨365556, by rfl⟩ : syracuseStep 3899269 = 731113) (by norm_num)
theorem B5199025 : Blo 2053435 5199025 := bstep (se 2 (by rfl) ⟨1949634, by rfl⟩ : syracuseStep 5199025 = 3899269) B3899269
theorem B6932033 : Blo 2053435 6932033 := bstep (se 2 (by rfl) ⟨2599512, by rfl⟩ : syracuseStep 6932033 = 5199025) B5199025
theorem B4621355 : Blo 2053435 4621355 := bstep (se 1 (by rfl) ⟨3466016, by rfl⟩ : syracuseStep 4621355 = 6932033) B6932033
theorem B3080903 : Blo 2053435 3080903 := bstep (se 1 (by rfl) ⟨2310677, by rfl⟩ : syracuseStep 3080903 = 4621355) B4621355
theorem B2053935 : Blo 2053435 2053935 := bstep (se 1 (by rfl) ⟨1540451, by rfl⟩ : syracuseStep 2053935 = 3080903) B3080903
theorem B3080909 : Blo 2053435 3080909 := bbase (se 3 (by rfl) ⟨577670, by rfl⟩ : syracuseStep 3080909 = 1155341) (by norm_num)
theorem B2053939 : Blo 2053435 2053939 := bstep (se 1 (by rfl) ⟨1540454, by rfl⟩ : syracuseStep 2053939 = 3080909) B3080909
theorem B4621373 : Blo 2053435 4621373 := bbase (se 3 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 4621373 = 1733015) (by norm_num)
theorem B3080915 : Blo 2053435 3080915 := bstep (se 1 (by rfl) ⟨2310686, by rfl⟩ : syracuseStep 3080915 = 4621373) B4621373
theorem B2053943 : Blo 2053435 2053943 := bstep (se 1 (by rfl) ⟨1540457, by rfl⟩ : syracuseStep 2053943 = 3080915) B3080915
theorem B3466037 : Blo 2053435 3466037 := bbase (se 5 (by rfl) ⟨162470, by rfl⟩ : syracuseStep 3466037 = 324941) (by norm_num)
theorem B2310691 : Blo 2053435 2310691 := bstep (se 1 (by rfl) ⟨1733018, by rfl⟩ : syracuseStep 2310691 = 3466037) B3466037
theorem B3080921 : Blo 2053435 3080921 := bstep (se 2 (by rfl) ⟨1155345, by rfl⟩ : syracuseStep 3080921 = 2310691) B2310691
theorem B2053947 : Blo 2053435 2053947 := bstep (se 1 (by rfl) ⟨1540460, by rfl⟩ : syracuseStep 2053947 = 3080921) B3080921
theorem B5848949 : Blo 2053435 5848949 := bbase (se 5 (by rfl) ⟨274169, by rfl⟩ : syracuseStep 5848949 = 548339) (by norm_num)
theorem B15597197 : Blo 2053435 15597197 := bstep (se 3 (by rfl) ⟨2924474, by rfl⟩ : syracuseStep 15597197 = 5848949) B5848949
theorem B10398131 : Blo 2053435 10398131 := bstep (se 1 (by rfl) ⟨7798598, by rfl⟩ : syracuseStep 10398131 = 15597197) B15597197
theorem B6932087 : Blo 2053435 6932087 := bstep (se 1 (by rfl) ⟨5199065, by rfl⟩ : syracuseStep 6932087 = 10398131) B10398131
theorem B4621391 : Blo 2053435 4621391 := bstep (se 1 (by rfl) ⟨3466043, by rfl⟩ : syracuseStep 4621391 = 6932087) B6932087
theorem B3080927 : Blo 2053435 3080927 := bstep (se 1 (by rfl) ⟨2310695, by rfl⟩ : syracuseStep 3080927 = 4621391) B4621391
theorem B2053951 : Blo 2053435 2053951 := bstep (se 1 (by rfl) ⟨1540463, by rfl⟩ : syracuseStep 2053951 = 3080927) B3080927
theorem B3080933 : Blo 2053435 3080933 := bbase (se 4 (by rfl) ⟨288837, by rfl⟩ : syracuseStep 3080933 = 577675) (by norm_num)
theorem B2053955 : Blo 2053435 2053955 := bstep (se 1 (by rfl) ⟨1540466, by rfl⟩ : syracuseStep 2053955 = 3080933) B3080933
theorem B2193365 : Blo 2053435 2193365 := bbase (se 7 (by rfl) ⟨25703, by rfl⟩ : syracuseStep 2193365 = 51407) (by norm_num)
theorem B5848973 : Blo 2053435 5848973 := bstep (se 3 (by rfl) ⟨1096682, by rfl⟩ : syracuseStep 5848973 = 2193365) B2193365
theorem B3899315 : Blo 2053435 3899315 := bstep (se 1 (by rfl) ⟨2924486, by rfl⟩ : syracuseStep 3899315 = 5848973) B5848973
theorem B2599543 : Blo 2053435 2599543 := bstep (se 1 (by rfl) ⟨1949657, by rfl⟩ : syracuseStep 2599543 = 3899315) B3899315
theorem B3466057 : Blo 2053435 3466057 := bstep (se 2 (by rfl) ⟨1299771, by rfl⟩ : syracuseStep 3466057 = 2599543) B2599543
theorem B4621409 : Blo 2053435 4621409 := bstep (se 2 (by rfl) ⟨1733028, by rfl⟩ : syracuseStep 4621409 = 3466057) B3466057
theorem B3080939 : Blo 2053435 3080939 := bstep (se 1 (by rfl) ⟨2310704, by rfl⟩ : syracuseStep 3080939 = 4621409) B4621409
theorem B2053959 : Blo 2053435 2053959 := bstep (se 1 (by rfl) ⟨1540469, by rfl⟩ : syracuseStep 2053959 = 3080939) B3080939
theorem B2310709 : Blo 2053435 2310709 := bbase (se 5 (by rfl) ⟨108314, by rfl⟩ : syracuseStep 2310709 = 216629) (by norm_num)
theorem B3080945 : Blo 2053435 3080945 := bstep (se 2 (by rfl) ⟨1155354, by rfl⟩ : syracuseStep 3080945 = 2310709) B2310709
theorem B2053963 : Blo 2053435 2053963 := bstep (se 1 (by rfl) ⟨1540472, by rfl⟩ : syracuseStep 2053963 = 3080945) B3080945
theorem B2599553 : Blo 2053435 2599553 := bbase (se 2 (by rfl) ⟨974832, by rfl⟩ : syracuseStep 2599553 = 1949665) (by norm_num)
theorem B6932141 : Blo 2053435 6932141 := bstep (se 3 (by rfl) ⟨1299776, by rfl⟩ : syracuseStep 6932141 = 2599553) B2599553
theorem B4621427 : Blo 2053435 4621427 := bstep (se 1 (by rfl) ⟨3466070, by rfl⟩ : syracuseStep 4621427 = 6932141) B6932141
theorem B3080951 : Blo 2053435 3080951 := bstep (se 1 (by rfl) ⟨2310713, by rfl⟩ : syracuseStep 3080951 = 4621427) B4621427
theorem B2053967 : Blo 2053435 2053967 := bstep (se 1 (by rfl) ⟨1540475, by rfl⟩ : syracuseStep 2053967 = 3080951) B3080951
theorem B3080957 : Blo 2053435 3080957 := bbase (se 3 (by rfl) ⟨577679, by rfl⟩ : syracuseStep 3080957 = 1155359) (by norm_num)
theorem B2053971 : Blo 2053435 2053971 := bstep (se 1 (by rfl) ⟨1540478, by rfl⟩ : syracuseStep 2053971 = 3080957) B3080957
theorem B4621445 : Blo 2053435 4621445 := bbase (se 4 (by rfl) ⟨433260, by rfl⟩ : syracuseStep 4621445 = 866521) (by norm_num)
theorem B3080963 : Blo 2053435 3080963 := bstep (se 1 (by rfl) ⟨2310722, by rfl⟩ : syracuseStep 3080963 = 4621445) B4621445
theorem B2053975 : Blo 2053435 2053975 := bstep (se 1 (by rfl) ⟨1540481, by rfl⟩ : syracuseStep 2053975 = 3080963) B3080963
theorem B4386773 : Blo 2053435 4386773 := bbase (se 7 (by rfl) ⟨51407, by rfl⟩ : syracuseStep 4386773 = 102815) (by norm_num)
theorem B2924515 : Blo 2053435 2924515 := bstep (se 1 (by rfl) ⟨2193386, by rfl⟩ : syracuseStep 2924515 = 4386773) B4386773
theorem B3899353 : Blo 2053435 3899353 := bstep (se 2 (by rfl) ⟨1462257, by rfl⟩ : syracuseStep 3899353 = 2924515) B2924515
theorem B5199137 : Blo 2053435 5199137 := bstep (se 2 (by rfl) ⟨1949676, by rfl⟩ : syracuseStep 5199137 = 3899353) B3899353
theorem B3466091 : Blo 2053435 3466091 := bstep (se 1 (by rfl) ⟨2599568, by rfl⟩ : syracuseStep 3466091 = 5199137) B5199137
theorem B2310727 : Blo 2053435 2310727 := bstep (se 1 (by rfl) ⟨1733045, by rfl⟩ : syracuseStep 2310727 = 3466091) B3466091
theorem B3080969 : Blo 2053435 3080969 := bstep (se 2 (by rfl) ⟨1155363, by rfl⟩ : syracuseStep 3080969 = 2310727) B2310727
theorem B2053979 : Blo 2053435 2053979 := bstep (se 1 (by rfl) ⟨1540484, by rfl⟩ : syracuseStep 2053979 = 3080969) B3080969
theorem B10398293 : Blo 2053435 10398293 := bbase (se 8 (by rfl) ⟨60927, by rfl⟩ : syracuseStep 10398293 = 121855) (by norm_num)
theorem B6932195 : Blo 2053435 6932195 := bstep (se 1 (by rfl) ⟨5199146, by rfl⟩ : syracuseStep 6932195 = 10398293) B10398293
theorem B4621463 : Blo 2053435 4621463 := bstep (se 1 (by rfl) ⟨3466097, by rfl⟩ : syracuseStep 4621463 = 6932195) B6932195
theorem B3080975 : Blo 2053435 3080975 := bstep (se 1 (by rfl) ⟨2310731, by rfl⟩ : syracuseStep 3080975 = 4621463) B4621463
theorem B2053983 : Blo 2053435 2053983 := bstep (se 1 (by rfl) ⟨1540487, by rfl⟩ : syracuseStep 2053983 = 3080975) B3080975
theorem B3080981 : Blo 2053435 3080981 := bbase (se 6 (by rfl) ⟨72210, by rfl⟩ : syracuseStep 3080981 = 144421) (by norm_num)
theorem B2053987 : Blo 2053435 2053987 := bstep (se 1 (by rfl) ⟨1540490, by rfl⟩ : syracuseStep 2053987 = 3080981) B3080981
theorem B2284409 : Blo 2053435 2284409 := bbase (se 2 (by rfl) ⟨856653, by rfl⟩ : syracuseStep 2284409 = 1713307) (by norm_num)
theorem B6091757 : Blo 2053435 6091757 := bstep (se 3 (by rfl) ⟨1142204, by rfl⟩ : syracuseStep 6091757 = 2284409) B2284409
theorem B4061171 : Blo 2053435 4061171 := bstep (se 1 (by rfl) ⟨3045878, by rfl⟩ : syracuseStep 4061171 = 6091757) B6091757
theorem B2707447 : Blo 2053435 2707447 := bstep (se 1 (by rfl) ⟨2030585, by rfl⟩ : syracuseStep 2707447 = 4061171) B4061171
theorem B3609929 : Blo 2053435 3609929 := bstep (se 2 (by rfl) ⟨1353723, by rfl⟩ : syracuseStep 3609929 = 2707447) B2707447
theorem B2406619 : Blo 2053435 2406619 := bstep (se 1 (by rfl) ⟨1804964, by rfl⟩ : syracuseStep 2406619 = 3609929) B3609929
theorem B3208825 : Blo 2053435 3208825 := bstep (se 2 (by rfl) ⟨1203309, by rfl⟩ : syracuseStep 3208825 = 2406619) B2406619
theorem B4278433 : Blo 2053435 4278433 := bstep (se 2 (by rfl) ⟨1604412, by rfl⟩ : syracuseStep 4278433 = 3208825) B3208825
theorem B5704577 : Blo 2053435 5704577 := bstep (se 2 (by rfl) ⟨2139216, by rfl⟩ : syracuseStep 5704577 = 4278433) B4278433
theorem B3803051 : Blo 2053435 3803051 := bstep (se 1 (by rfl) ⟨2852288, by rfl⟩ : syracuseStep 3803051 = 5704577) B5704577
theorem B10141469 : Blo 2053435 10141469 := bstep (se 3 (by rfl) ⟨1901525, by rfl⟩ : syracuseStep 10141469 = 3803051) B3803051
theorem B6760979 : Blo 2053435 6760979 := bstep (se 1 (by rfl) ⟨5070734, by rfl⟩ : syracuseStep 6760979 = 10141469) B10141469
theorem B4507319 : Blo 2053435 4507319 := bstep (se 1 (by rfl) ⟨3380489, by rfl⟩ : syracuseStep 4507319 = 6760979) B6760979
theorem B3004879 : Blo 2053435 3004879 := bstep (se 1 (by rfl) ⟨2253659, by rfl⟩ : syracuseStep 3004879 = 4507319) B4507319
theorem B4006505 : Blo 2053435 4006505 := bstep (se 2 (by rfl) ⟨1502439, by rfl⟩ : syracuseStep 4006505 = 3004879) B3004879
theorem B2671003 : Blo 2053435 2671003 := bstep (se 1 (by rfl) ⟨2003252, by rfl⟩ : syracuseStep 2671003 = 4006505) B4006505
theorem B3561337 : Blo 2053435 3561337 := bstep (se 2 (by rfl) ⟨1335501, by rfl⟩ : syracuseStep 3561337 = 2671003) B2671003
theorem B18993797 : Blo 2053435 18993797 := bstep (se 4 (by rfl) ⟨1780668, by rfl⟩ : syracuseStep 18993797 = 3561337) B3561337
theorem B12662531 : Blo 2053435 12662531 := bstep (se 1 (by rfl) ⟨9496898, by rfl⟩ : syracuseStep 12662531 = 18993797) B18993797
theorem B8441687 : Blo 2053435 8441687 := bstep (se 1 (by rfl) ⟨6331265, by rfl⟩ : syracuseStep 8441687 = 12662531) B12662531
theorem B5627791 : Blo 2053435 5627791 := bstep (se 1 (by rfl) ⟨4220843, by rfl⟩ : syracuseStep 5627791 = 8441687) B8441687
theorem B7503721 : Blo 2053435 7503721 := bstep (se 2 (by rfl) ⟨2813895, by rfl⟩ : syracuseStep 7503721 = 5627791) B5627791
theorem B40019845 : Blo 2053435 40019845 := bstep (se 4 (by rfl) ⟨3751860, by rfl⟩ : syracuseStep 40019845 = 7503721) B7503721
theorem B53359793 : Blo 2053435 53359793 := bstep (se 2 (by rfl) ⟨20009922, by rfl⟩ : syracuseStep 53359793 = 40019845) B40019845
theorem B35573195 : Blo 2053435 35573195 := bstep (se 1 (by rfl) ⟨26679896, by rfl⟩ : syracuseStep 35573195 = 53359793) B53359793
theorem B23715463 : Blo 2053435 23715463 := bstep (se 1 (by rfl) ⟨17786597, by rfl⟩ : syracuseStep 23715463 = 35573195) B35573195
theorem B31620617 : Blo 2053435 31620617 := bstep (se 2 (by rfl) ⟨11857731, by rfl⟩ : syracuseStep 31620617 = 23715463) B23715463
theorem B21080411 : Blo 2053435 21080411 := bstep (se 1 (by rfl) ⟨15810308, by rfl⟩ : syracuseStep 21080411 = 31620617) B31620617
theorem B14053607 : Blo 2053435 14053607 := bstep (se 1 (by rfl) ⟨10540205, by rfl⟩ : syracuseStep 14053607 = 21080411) B21080411
theorem B9369071 : Blo 2053435 9369071 := bstep (se 1 (by rfl) ⟨7026803, by rfl⟩ : syracuseStep 9369071 = 14053607) B14053607
theorem B6246047 : Blo 2053435 6246047 := bstep (se 1 (by rfl) ⟨4684535, by rfl⟩ : syracuseStep 6246047 = 9369071) B9369071
theorem B4164031 : Blo 2053435 4164031 := bstep (se 1 (by rfl) ⟨3123023, by rfl⟩ : syracuseStep 4164031 = 6246047) B6246047
theorem B22208165 : Blo 2053435 22208165 := bstep (se 4 (by rfl) ⟨2082015, by rfl⟩ : syracuseStep 22208165 = 4164031) B4164031
theorem B14805443 : Blo 2053435 14805443 := bstep (se 1 (by rfl) ⟨11104082, by rfl⟩ : syracuseStep 14805443 = 22208165) B22208165
theorem B39481181 : Blo 2053435 39481181 := bstep (se 3 (by rfl) ⟨7402721, by rfl⟩ : syracuseStep 39481181 = 14805443) B14805443
theorem B26320787 : Blo 2053435 26320787 := bstep (se 1 (by rfl) ⟨19740590, by rfl⟩ : syracuseStep 26320787 = 39481181) B39481181
theorem B17547191 : Blo 2053435 17547191 := bstep (se 1 (by rfl) ⟨13160393, by rfl⟩ : syracuseStep 17547191 = 26320787) B26320787
theorem B11698127 : Blo 2053435 11698127 := bstep (se 1 (by rfl) ⟨8773595, by rfl⟩ : syracuseStep 11698127 = 17547191) B17547191
theorem B7798751 : Blo 2053435 7798751 := bstep (se 1 (by rfl) ⟨5849063, by rfl⟩ : syracuseStep 7798751 = 11698127) B11698127
theorem B5199167 : Blo 2053435 5199167 := bstep (se 1 (by rfl) ⟨3899375, by rfl⟩ : syracuseStep 5199167 = 7798751) B7798751
theorem B3466111 : Blo 2053435 3466111 := bstep (se 1 (by rfl) ⟨2599583, by rfl⟩ : syracuseStep 3466111 = 5199167) B5199167
theorem B4621481 : Blo 2053435 4621481 := bstep (se 2 (by rfl) ⟨1733055, by rfl⟩ : syracuseStep 4621481 = 3466111) B3466111
theorem B3080987 : Blo 2053435 3080987 := bstep (se 1 (by rfl) ⟨2310740, by rfl⟩ : syracuseStep 3080987 = 4621481) B4621481
theorem B2053991 : Blo 2053435 2053991 := bstep (se 1 (by rfl) ⟨1540493, by rfl⟩ : syracuseStep 2053991 = 3080987) B3080987
theorem B2310745 : Blo 2053435 2310745 := bbase (se 2 (by rfl) ⟨866529, by rfl⟩ : syracuseStep 2310745 = 1733059) (by norm_num)
theorem B3080993 : Blo 2053435 3080993 := bstep (se 2 (by rfl) ⟨1155372, by rfl⟩ : syracuseStep 3080993 = 2310745) B2310745
theorem B2053995 : Blo 2053435 2053995 := bstep (se 1 (by rfl) ⟨1540496, by rfl⟩ : syracuseStep 2053995 = 3080993) B3080993
theorem B7219877 : Blo 2053435 7219877 := bbase (se 4 (by rfl) ⟨676863, by rfl⟩ : syracuseStep 7219877 = 1353727) (by norm_num)
theorem B19253005 : Blo 2053435 19253005 := bstep (se 3 (by rfl) ⟨3609938, by rfl⟩ : syracuseStep 19253005 = 7219877) B7219877
theorem B102682693 : Blo 2053435 102682693 := bstep (se 4 (by rfl) ⟨9626502, by rfl⟩ : syracuseStep 102682693 = 19253005) B19253005
theorem B136910257 : Blo 2053435 136910257 := bstep (se 2 (by rfl) ⟨51341346, by rfl⟩ : syracuseStep 136910257 = 102682693) B102682693
theorem B730188037 : Blo 2053435 730188037 := bstep (se 4 (by rfl) ⟨68455128, by rfl⟩ : syracuseStep 730188037 = 136910257) B136910257
theorem B973584049 : Blo 2053435 973584049 := bstep (se 2 (by rfl) ⟨365094018, by rfl⟩ : syracuseStep 973584049 = 730188037) B730188037
theorem B1298112065 : Blo 2053435 1298112065 := bstep (se 2 (by rfl) ⟨486792024, by rfl⟩ : syracuseStep 1298112065 = 973584049) B973584049
theorem B865408043 : Blo 2053435 865408043 := bstep (se 1 (by rfl) ⟨649056032, by rfl⟩ : syracuseStep 865408043 = 1298112065) B1298112065
theorem B576938695 : Blo 2053435 576938695 := bstep (se 1 (by rfl) ⟨432704021, by rfl⟩ : syracuseStep 576938695 = 865408043) B865408043
theorem B769251593 : Blo 2053435 769251593 := bstep (se 2 (by rfl) ⟨288469347, by rfl⟩ : syracuseStep 769251593 = 576938695) B576938695
theorem B2051337581 : Blo 2053435 2051337581 := bstep (se 3 (by rfl) ⟨384625796, by rfl⟩ : syracuseStep 2051337581 = 769251593) B769251593
theorem B1367558387 : Blo 2053435 1367558387 := bstep (se 1 (by rfl) ⟨1025668790, by rfl⟩ : syracuseStep 1367558387 = 2051337581) B2051337581
theorem B911705591 : Blo 2053435 911705591 := bstep (se 1 (by rfl) ⟨683779193, by rfl⟩ : syracuseStep 911705591 = 1367558387) B1367558387
theorem B2431214909 : Blo 2053435 2431214909 := bstep (se 3 (by rfl) ⟨455852795, by rfl⟩ : syracuseStep 2431214909 = 911705591) B911705591
theorem B1620809939 : Blo 2053435 1620809939 := bstep (se 1 (by rfl) ⟨1215607454, by rfl⟩ : syracuseStep 1620809939 = 2431214909) B2431214909
theorem B1080539959 : Blo 2053435 1080539959 := bstep (se 1 (by rfl) ⟨810404969, by rfl⟩ : syracuseStep 1080539959 = 1620809939) B1620809939
theorem B1440719945 : Blo 2053435 1440719945 := bstep (se 2 (by rfl) ⟨540269979, by rfl⟩ : syracuseStep 1440719945 = 1080539959) B1080539959
theorem B960479963 : Blo 2053435 960479963 := bstep (se 1 (by rfl) ⟨720359972, by rfl⟩ : syracuseStep 960479963 = 1440719945) B1440719945
theorem B640319975 : Blo 2053435 640319975 := bstep (se 1 (by rfl) ⟨480239981, by rfl⟩ : syracuseStep 640319975 = 960479963) B960479963
theorem B426879983 : Blo 2053435 426879983 := bstep (se 1 (by rfl) ⟨320159987, by rfl⟩ : syracuseStep 426879983 = 640319975) B640319975
theorem B284586655 : Blo 2053435 284586655 := bstep (se 1 (by rfl) ⟨213439991, by rfl⟩ : syracuseStep 284586655 = 426879983) B426879983
theorem B379448873 : Blo 2053435 379448873 := bstep (se 2 (by rfl) ⟨142293327, by rfl⟩ : syracuseStep 379448873 = 284586655) B284586655
theorem B252965915 : Blo 2053435 252965915 := bstep (se 1 (by rfl) ⟨189724436, by rfl⟩ : syracuseStep 252965915 = 379448873) B379448873
theorem B168643943 : Blo 2053435 168643943 := bstep (se 1 (by rfl) ⟨126482957, by rfl⟩ : syracuseStep 168643943 = 252965915) B252965915
theorem B112429295 : Blo 2053435 112429295 := bstep (se 1 (by rfl) ⟨84321971, by rfl⟩ : syracuseStep 112429295 = 168643943) B168643943
theorem B74952863 : Blo 2053435 74952863 := bstep (se 1 (by rfl) ⟨56214647, by rfl⟩ : syracuseStep 74952863 = 112429295) B112429295
theorem B49968575 : Blo 2053435 49968575 := bstep (se 1 (by rfl) ⟨37476431, by rfl⟩ : syracuseStep 49968575 = 74952863) B74952863
theorem B33312383 : Blo 2053435 33312383 := bstep (se 1 (by rfl) ⟨24984287, by rfl⟩ : syracuseStep 33312383 = 49968575) B49968575
theorem B22208255 : Blo 2053435 22208255 := bstep (se 1 (by rfl) ⟨16656191, by rfl⟩ : syracuseStep 22208255 = 33312383) B33312383
theorem B14805503 : Blo 2053435 14805503 := bstep (se 1 (by rfl) ⟨11104127, by rfl⟩ : syracuseStep 14805503 = 22208255) B22208255
theorem B9870335 : Blo 2053435 9870335 := bstep (se 1 (by rfl) ⟨7402751, by rfl⟩ : syracuseStep 9870335 = 14805503) B14805503
theorem B6580223 : Blo 2053435 6580223 := bstep (se 1 (by rfl) ⟨4935167, by rfl⟩ : syracuseStep 6580223 = 9870335) B9870335
theorem B4386815 : Blo 2053435 4386815 := bstep (se 1 (by rfl) ⟨3290111, by rfl⟩ : syracuseStep 4386815 = 6580223) B6580223
theorem B2924543 : Blo 2053435 2924543 := bstep (se 1 (by rfl) ⟨2193407, by rfl⟩ : syracuseStep 2924543 = 4386815) B4386815
theorem B7798781 : Blo 2053435 7798781 := bstep (se 3 (by rfl) ⟨1462271, by rfl⟩ : syracuseStep 7798781 = 2924543) B2924543
theorem B5199187 : Blo 2053435 5199187 := bstep (se 1 (by rfl) ⟨3899390, by rfl⟩ : syracuseStep 5199187 = 7798781) B7798781
theorem B6932249 : Blo 2053435 6932249 := bstep (se 2 (by rfl) ⟨2599593, by rfl⟩ : syracuseStep 6932249 = 5199187) B5199187
theorem B4621499 : Blo 2053435 4621499 := bstep (se 1 (by rfl) ⟨3466124, by rfl⟩ : syracuseStep 4621499 = 6932249) B6932249
theorem B3080999 : Blo 2053435 3080999 := bstep (se 1 (by rfl) ⟨2310749, by rfl⟩ : syracuseStep 3080999 = 4621499) B4621499
theorem B2053999 : Blo 2053435 2053999 := bstep (se 1 (by rfl) ⟨1540499, by rfl⟩ : syracuseStep 2053999 = 3080999) B3080999
theorem B3081005 : Blo 2053435 3081005 := bbase (se 3 (by rfl) ⟨577688, by rfl⟩ : syracuseStep 3081005 = 1155377) (by norm_num)
theorem B2054003 : Blo 2053435 2054003 := bstep (se 1 (by rfl) ⟨1540502, by rfl⟩ : syracuseStep 2054003 = 3081005) B3081005
theorem B4621517 : Blo 2053435 4621517 := bbase (se 3 (by rfl) ⟨866534, by rfl⟩ : syracuseStep 4621517 = 1733069) (by norm_num)
theorem B3081011 : Blo 2053435 3081011 := bstep (se 1 (by rfl) ⟨2310758, by rfl⟩ : syracuseStep 3081011 = 4621517) B4621517
theorem B2054007 : Blo 2053435 2054007 := bstep (se 1 (by rfl) ⟨1540505, by rfl⟩ : syracuseStep 2054007 = 3081011) B3081011
theorem B2599609 : Blo 2053435 2599609 := bbase (se 2 (by rfl) ⟨974853, by rfl⟩ : syracuseStep 2599609 = 1949707) (by norm_num)
theorem B3466145 : Blo 2053435 3466145 := bstep (se 2 (by rfl) ⟨1299804, by rfl⟩ : syracuseStep 3466145 = 2599609) B2599609
theorem B2310763 : Blo 2053435 2310763 := bstep (se 1 (by rfl) ⟨1733072, by rfl⟩ : syracuseStep 2310763 = 3466145) B3466145
theorem B3081017 : Blo 2053435 3081017 := bstep (se 2 (by rfl) ⟨1155381, by rfl⟩ : syracuseStep 3081017 = 2310763) B2310763
theorem B2054011 : Blo 2053435 2054011 := bstep (se 1 (by rfl) ⟨1540508, by rfl⟩ : syracuseStep 2054011 = 3081017) B3081017
theorem B4935205 : Blo 2053435 4935205 := bbase (se 4 (by rfl) ⟨462675, by rfl⟩ : syracuseStep 4935205 = 925351) (by norm_num)
theorem B6580273 : Blo 2053435 6580273 := bstep (se 2 (by rfl) ⟨2467602, by rfl⟩ : syracuseStep 6580273 = 4935205) B4935205
theorem B8773697 : Blo 2053435 8773697 := bstep (se 2 (by rfl) ⟨3290136, by rfl⟩ : syracuseStep 8773697 = 6580273) B6580273
theorem B23396525 : Blo 2053435 23396525 := bstep (se 3 (by rfl) ⟨4386848, by rfl⟩ : syracuseStep 23396525 = 8773697) B8773697
theorem B15597683 : Blo 2053435 15597683 := bstep (se 1 (by rfl) ⟨11698262, by rfl⟩ : syracuseStep 15597683 = 23396525) B23396525
theorem B10398455 : Blo 2053435 10398455 := bstep (se 1 (by rfl) ⟨7798841, by rfl⟩ : syracuseStep 10398455 = 15597683) B15597683
theorem B6932303 : Blo 2053435 6932303 := bstep (se 1 (by rfl) ⟨5199227, by rfl⟩ : syracuseStep 6932303 = 10398455) B10398455
theorem B4621535 : Blo 2053435 4621535 := bstep (se 1 (by rfl) ⟨3466151, by rfl⟩ : syracuseStep 4621535 = 6932303) B6932303
theorem B3081023 : Blo 2053435 3081023 := bstep (se 1 (by rfl) ⟨2310767, by rfl⟩ : syracuseStep 3081023 = 4621535) B4621535
theorem B2054015 : Blo 2053435 2054015 := bstep (se 1 (by rfl) ⟨1540511, by rfl⟩ : syracuseStep 2054015 = 3081023) B3081023
theorem B3081029 : Blo 2053435 3081029 := bbase (se 4 (by rfl) ⟨288846, by rfl⟩ : syracuseStep 3081029 = 577693) (by norm_num)
theorem B2054019 : Blo 2053435 2054019 := bstep (se 1 (by rfl) ⟨1540514, by rfl⟩ : syracuseStep 2054019 = 3081029) B3081029
theorem B3466165 : Blo 2053435 3466165 := bbase (se 5 (by rfl) ⟨162476, by rfl⟩ : syracuseStep 3466165 = 324953) (by norm_num)
theorem B4621553 : Blo 2053435 4621553 := bstep (se 2 (by rfl) ⟨1733082, by rfl⟩ : syracuseStep 4621553 = 3466165) B3466165
theorem B3081035 : Blo 2053435 3081035 := bstep (se 1 (by rfl) ⟨2310776, by rfl⟩ : syracuseStep 3081035 = 4621553) B4621553
theorem B2054023 : Blo 2053435 2054023 := bstep (se 1 (by rfl) ⟨1540517, by rfl⟩ : syracuseStep 2054023 = 3081035) B3081035
theorem B2310781 : Blo 2053435 2310781 := bbase (se 3 (by rfl) ⟨433271, by rfl⟩ : syracuseStep 2310781 = 866543) (by norm_num)
theorem B3081041 : Blo 2053435 3081041 := bstep (se 2 (by rfl) ⟨1155390, by rfl⟩ : syracuseStep 3081041 = 2310781) B2310781
theorem B2054027 : Blo 2053435 2054027 := bstep (se 1 (by rfl) ⟨1540520, by rfl⟩ : syracuseStep 2054027 = 3081041) B3081041
theorem B6932357 : Blo 2053435 6932357 := bbase (se 4 (by rfl) ⟨649908, by rfl⟩ : syracuseStep 6932357 = 1299817) (by norm_num)
theorem B4621571 : Blo 2053435 4621571 := bstep (se 1 (by rfl) ⟨3466178, by rfl⟩ : syracuseStep 4621571 = 6932357) B6932357
theorem B3081047 : Blo 2053435 3081047 := bstep (se 1 (by rfl) ⟨2310785, by rfl⟩ : syracuseStep 3081047 = 4621571) B4621571
theorem B2054031 : Blo 2053435 2054031 := bstep (se 1 (by rfl) ⟨1540523, by rfl⟩ : syracuseStep 2054031 = 3081047) B3081047
theorem B3081053 : Blo 2053435 3081053 := bbase (se 3 (by rfl) ⟨577697, by rfl⟩ : syracuseStep 3081053 = 1155395) (by norm_num)
theorem B2054035 : Blo 2053435 2054035 := bstep (se 1 (by rfl) ⟨1540526, by rfl⟩ : syracuseStep 2054035 = 3081053) B3081053
theorem B4621589 : Blo 2053435 4621589 := bbase (se 6 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 4621589 = 216637) (by norm_num)
theorem B3081059 : Blo 2053435 3081059 := bstep (se 1 (by rfl) ⟨2310794, by rfl⟩ : syracuseStep 3081059 = 4621589) B4621589
theorem B2054039 : Blo 2053435 2054039 := bstep (se 1 (by rfl) ⟨1540529, by rfl⟩ : syracuseStep 2054039 = 3081059) B3081059
theorem B7798949 : Blo 2053435 7798949 := bbase (se 4 (by rfl) ⟨731151, by rfl⟩ : syracuseStep 7798949 = 1462303) (by norm_num)
theorem B5199299 : Blo 2053435 5199299 := bstep (se 1 (by rfl) ⟨3899474, by rfl⟩ : syracuseStep 5199299 = 7798949) B7798949
theorem B3466199 : Blo 2053435 3466199 := bstep (se 1 (by rfl) ⟨2599649, by rfl⟩ : syracuseStep 3466199 = 5199299) B5199299
theorem B2310799 : Blo 2053435 2310799 := bstep (se 1 (by rfl) ⟨1733099, by rfl⟩ : syracuseStep 2310799 = 3466199) B3466199
theorem B3081065 : Blo 2053435 3081065 := bstep (se 2 (by rfl) ⟨1155399, by rfl⟩ : syracuseStep 3081065 = 2310799) B2310799
theorem B2054043 : Blo 2053435 2054043 := bstep (se 1 (by rfl) ⟨1540532, by rfl⟩ : syracuseStep 2054043 = 3081065) B3081065
theorem B4386917 : Blo 2053435 4386917 := bbase (se 4 (by rfl) ⟨411273, by rfl⟩ : syracuseStep 4386917 = 822547) (by norm_num)
theorem B11698445 : Blo 2053435 11698445 := bstep (se 3 (by rfl) ⟨2193458, by rfl⟩ : syracuseStep 11698445 = 4386917) B4386917
theorem B7798963 : Blo 2053435 7798963 := bstep (se 1 (by rfl) ⟨5849222, by rfl⟩ : syracuseStep 7798963 = 11698445) B11698445
theorem B10398617 : Blo 2053435 10398617 := bstep (se 2 (by rfl) ⟨3899481, by rfl⟩ : syracuseStep 10398617 = 7798963) B7798963
theorem B6932411 : Blo 2053435 6932411 := bstep (se 1 (by rfl) ⟨5199308, by rfl⟩ : syracuseStep 6932411 = 10398617) B10398617
theorem B4621607 : Blo 2053435 4621607 := bstep (se 1 (by rfl) ⟨3466205, by rfl⟩ : syracuseStep 4621607 = 6932411) B6932411
theorem B3081071 : Blo 2053435 3081071 := bstep (se 1 (by rfl) ⟨2310803, by rfl⟩ : syracuseStep 3081071 = 4621607) B4621607
theorem B2054047 : Blo 2053435 2054047 := bstep (se 1 (by rfl) ⟨1540535, by rfl⟩ : syracuseStep 2054047 = 3081071) B3081071
theorem B3081077 : Blo 2053435 3081077 := bbase (se 5 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 3081077 = 288851) (by norm_num)
theorem B2054051 : Blo 2053435 2054051 := bstep (se 1 (by rfl) ⟨1540538, by rfl⟩ : syracuseStep 2054051 = 3081077) B3081077
theorem B3701477 : Blo 2053435 3701477 := bbase (se 4 (by rfl) ⟨347013, by rfl⟩ : syracuseStep 3701477 = 694027) (by norm_num)
theorem B9870605 : Blo 2053435 9870605 := bstep (se 3 (by rfl) ⟨1850738, by rfl⟩ : syracuseStep 9870605 = 3701477) B3701477
theorem B6580403 : Blo 2053435 6580403 := bstep (se 1 (by rfl) ⟨4935302, by rfl⟩ : syracuseStep 6580403 = 9870605) B9870605
theorem B4386935 : Blo 2053435 4386935 := bstep (se 1 (by rfl) ⟨3290201, by rfl⟩ : syracuseStep 4386935 = 6580403) B6580403
theorem B2924623 : Blo 2053435 2924623 := bstep (se 1 (by rfl) ⟨2193467, by rfl⟩ : syracuseStep 2924623 = 4386935) B4386935
theorem B3899497 : Blo 2053435 3899497 := bstep (se 2 (by rfl) ⟨1462311, by rfl⟩ : syracuseStep 3899497 = 2924623) B2924623
theorem B5199329 : Blo 2053435 5199329 := bstep (se 2 (by rfl) ⟨1949748, by rfl⟩ : syracuseStep 5199329 = 3899497) B3899497
theorem B3466219 : Blo 2053435 3466219 := bstep (se 1 (by rfl) ⟨2599664, by rfl⟩ : syracuseStep 3466219 = 5199329) B5199329
theorem B4621625 : Blo 2053435 4621625 := bstep (se 2 (by rfl) ⟨1733109, by rfl⟩ : syracuseStep 4621625 = 3466219) B3466219
theorem B3081083 : Blo 2053435 3081083 := bstep (se 1 (by rfl) ⟨2310812, by rfl⟩ : syracuseStep 3081083 = 4621625) B4621625
theorem B2054055 : Blo 2053435 2054055 := bstep (se 1 (by rfl) ⟨1540541, by rfl⟩ : syracuseStep 2054055 = 3081083) B3081083
theorem B2310817 : Blo 2053435 2310817 := bbase (se 2 (by rfl) ⟨866556, by rfl⟩ : syracuseStep 2310817 = 1733113) (by norm_num)
theorem B3081089 : Blo 2053435 3081089 := bstep (se 2 (by rfl) ⟨1155408, by rfl⟩ : syracuseStep 3081089 = 2310817) B2310817
theorem B2054059 : Blo 2053435 2054059 := bstep (se 1 (by rfl) ⟨1540544, by rfl⟩ : syracuseStep 2054059 = 3081089) B3081089
theorem B5199349 : Blo 2053435 5199349 := bbase (se 5 (by rfl) ⟨243719, by rfl⟩ : syracuseStep 5199349 = 487439) (by norm_num)
theorem B6932465 : Blo 2053435 6932465 := bstep (se 2 (by rfl) ⟨2599674, by rfl⟩ : syracuseStep 6932465 = 5199349) B5199349
theorem B4621643 : Blo 2053435 4621643 := bstep (se 1 (by rfl) ⟨3466232, by rfl⟩ : syracuseStep 4621643 = 6932465) B6932465
theorem B3081095 : Blo 2053435 3081095 := bstep (se 1 (by rfl) ⟨2310821, by rfl⟩ : syracuseStep 3081095 = 4621643) B4621643
theorem B2054063 : Blo 2053435 2054063 := bstep (se 1 (by rfl) ⟨1540547, by rfl⟩ : syracuseStep 2054063 = 3081095) B3081095
theorem B3081101 : Blo 2053435 3081101 := bbase (se 3 (by rfl) ⟨577706, by rfl⟩ : syracuseStep 3081101 = 1155413) (by norm_num)
theorem B2054067 : Blo 2053435 2054067 := bstep (se 1 (by rfl) ⟨1540550, by rfl⟩ : syracuseStep 2054067 = 3081101) B3081101
theorem B4621661 : Blo 2053435 4621661 := bbase (se 3 (by rfl) ⟨866561, by rfl⟩ : syracuseStep 4621661 = 1733123) (by norm_num)
theorem B3081107 : Blo 2053435 3081107 := bstep (se 1 (by rfl) ⟨2310830, by rfl⟩ : syracuseStep 3081107 = 4621661) B4621661
theorem B2054071 : Blo 2053435 2054071 := bstep (se 1 (by rfl) ⟨1540553, by rfl⟩ : syracuseStep 2054071 = 3081107) B3081107
theorem B3466253 : Blo 2053435 3466253 := bbase (se 3 (by rfl) ⟨649922, by rfl⟩ : syracuseStep 3466253 = 1299845) (by norm_num)
theorem B2310835 : Blo 2053435 2310835 := bstep (se 1 (by rfl) ⟨1733126, by rfl⟩ : syracuseStep 2310835 = 3466253) B3466253
theorem B3081113 : Blo 2053435 3081113 := bstep (se 2 (by rfl) ⟨1155417, by rfl⟩ : syracuseStep 3081113 = 2310835) B2310835
theorem B2054075 : Blo 2053435 2054075 := bstep (se 1 (by rfl) ⟨1540556, by rfl⟩ : syracuseStep 2054075 = 3081113) B3081113
theorem B3473509 : Blo 2053435 3473509 := bbase (se 4 (by rfl) ⟨325641, by rfl⟩ : syracuseStep 3473509 = 651283) (by norm_num)
theorem B4631345 : Blo 2053435 4631345 := bstep (se 2 (by rfl) ⟨1736754, by rfl⟩ : syracuseStep 4631345 = 3473509) B3473509
theorem B3087563 : Blo 2053435 3087563 := bstep (se 1 (by rfl) ⟨2315672, by rfl⟩ : syracuseStep 3087563 = 4631345) B4631345
theorem B8233501 : Blo 2053435 8233501 := bstep (se 3 (by rfl) ⟨1543781, by rfl⟩ : syracuseStep 8233501 = 3087563) B3087563
theorem B10978001 : Blo 2053435 10978001 := bstep (se 2 (by rfl) ⟨4116750, by rfl⟩ : syracuseStep 10978001 = 8233501) B8233501
theorem B7318667 : Blo 2053435 7318667 := bstep (se 1 (by rfl) ⟨5489000, by rfl⟩ : syracuseStep 7318667 = 10978001) B10978001
theorem B19516445 : Blo 2053435 19516445 := bstep (se 3 (by rfl) ⟨3659333, by rfl⟩ : syracuseStep 19516445 = 7318667) B7318667
theorem B13010963 : Blo 2053435 13010963 := bstep (se 1 (by rfl) ⟨9758222, by rfl⟩ : syracuseStep 13010963 = 19516445) B19516445
theorem B34695901 : Blo 2053435 34695901 := bstep (se 3 (by rfl) ⟨6505481, by rfl⟩ : syracuseStep 34695901 = 13010963) B13010963
theorem B46261201 : Blo 2053435 46261201 := bstep (se 2 (by rfl) ⟨17347950, by rfl⟩ : syracuseStep 46261201 = 34695901) B34695901
theorem B61681601 : Blo 2053435 61681601 := bstep (se 2 (by rfl) ⟨23130600, by rfl⟩ : syracuseStep 61681601 = 46261201) B46261201
theorem B164484269 : Blo 2053435 164484269 := bstep (se 3 (by rfl) ⟨30840800, by rfl⟩ : syracuseStep 164484269 = 61681601) B61681601
theorem B109656179 : Blo 2053435 109656179 := bstep (se 1 (by rfl) ⟨82242134, by rfl⟩ : syracuseStep 109656179 = 164484269) B164484269
theorem B73104119 : Blo 2053435 73104119 := bstep (se 1 (by rfl) ⟨54828089, by rfl⟩ : syracuseStep 73104119 = 109656179) B109656179
theorem B48736079 : Blo 2053435 48736079 := bstep (se 1 (by rfl) ⟨36552059, by rfl⟩ : syracuseStep 48736079 = 73104119) B73104119
theorem B32490719 : Blo 2053435 32490719 := bstep (se 1 (by rfl) ⟨24368039, by rfl⟩ : syracuseStep 32490719 = 48736079) B48736079
theorem B21660479 : Blo 2053435 21660479 := bstep (se 1 (by rfl) ⟨16245359, by rfl⟩ : syracuseStep 21660479 = 32490719) B32490719
theorem B14440319 : Blo 2053435 14440319 := bstep (se 1 (by rfl) ⟨10830239, by rfl⟩ : syracuseStep 14440319 = 21660479) B21660479
theorem B9626879 : Blo 2053435 9626879 := bstep (se 1 (by rfl) ⟨7220159, by rfl⟩ : syracuseStep 9626879 = 14440319) B14440319
theorem B6417919 : Blo 2053435 6417919 := bstep (se 1 (by rfl) ⟨4813439, by rfl⟩ : syracuseStep 6417919 = 9626879) B9626879
theorem B34228901 : Blo 2053435 34228901 := bstep (se 4 (by rfl) ⟨3208959, by rfl⟩ : syracuseStep 34228901 = 6417919) B6417919
theorem B22819267 : Blo 2053435 22819267 := bstep (se 1 (by rfl) ⟨17114450, by rfl⟩ : syracuseStep 22819267 = 34228901) B34228901
theorem B121702757 : Blo 2053435 121702757 := bstep (se 4 (by rfl) ⟨11409633, by rfl⟩ : syracuseStep 121702757 = 22819267) B22819267
theorem B324540685 : Blo 2053435 324540685 := bstep (se 3 (by rfl) ⟨60851378, by rfl⟩ : syracuseStep 324540685 = 121702757) B121702757
theorem B432720913 : Blo 2053435 432720913 := bstep (se 2 (by rfl) ⟨162270342, by rfl⟩ : syracuseStep 432720913 = 324540685) B324540685
theorem B576961217 : Blo 2053435 576961217 := bstep (se 2 (by rfl) ⟨216360456, by rfl⟩ : syracuseStep 576961217 = 432720913) B432720913
theorem B384640811 : Blo 2053435 384640811 := bstep (se 1 (by rfl) ⟨288480608, by rfl⟩ : syracuseStep 384640811 = 576961217) B576961217
theorem B256427207 : Blo 2053435 256427207 := bstep (se 1 (by rfl) ⟨192320405, by rfl⟩ : syracuseStep 256427207 = 384640811) B384640811
theorem B170951471 : Blo 2053435 170951471 := bstep (se 1 (by rfl) ⟨128213603, by rfl⟩ : syracuseStep 170951471 = 256427207) B256427207
theorem B113967647 : Blo 2053435 113967647 := bstep (se 1 (by rfl) ⟨85475735, by rfl⟩ : syracuseStep 113967647 = 170951471) B170951471
theorem B75978431 : Blo 2053435 75978431 := bstep (se 1 (by rfl) ⟨56983823, by rfl⟩ : syracuseStep 75978431 = 113967647) B113967647
theorem B50652287 : Blo 2053435 50652287 := bstep (se 1 (by rfl) ⟨37989215, by rfl⟩ : syracuseStep 50652287 = 75978431) B75978431
theorem B33768191 : Blo 2053435 33768191 := bstep (se 1 (by rfl) ⟨25326143, by rfl⟩ : syracuseStep 33768191 = 50652287) B50652287
theorem B90048509 : Blo 2053435 90048509 := bstep (se 3 (by rfl) ⟨16884095, by rfl⟩ : syracuseStep 90048509 = 33768191) B33768191
theorem B60032339 : Blo 2053435 60032339 := bstep (se 1 (by rfl) ⟨45024254, by rfl⟩ : syracuseStep 60032339 = 90048509) B90048509
theorem B40021559 : Blo 2053435 40021559 := bstep (se 1 (by rfl) ⟨30016169, by rfl⟩ : syracuseStep 40021559 = 60032339) B60032339
theorem B26681039 : Blo 2053435 26681039 := bstep (se 1 (by rfl) ⟨20010779, by rfl⟩ : syracuseStep 26681039 = 40021559) B40021559
theorem B17787359 : Blo 2053435 17787359 := bstep (se 1 (by rfl) ⟨13340519, by rfl⟩ : syracuseStep 17787359 = 26681039) B26681039
theorem B11858239 : Blo 2053435 11858239 := bstep (se 1 (by rfl) ⟨8893679, by rfl⟩ : syracuseStep 11858239 = 17787359) B17787359
theorem B15810985 : Blo 2053435 15810985 := bstep (se 2 (by rfl) ⟨5929119, by rfl⟩ : syracuseStep 15810985 = 11858239) B11858239
theorem B21081313 : Blo 2053435 21081313 := bstep (se 2 (by rfl) ⟨7905492, by rfl⟩ : syracuseStep 21081313 = 15810985) B15810985
theorem B28108417 : Blo 2053435 28108417 := bstep (se 2 (by rfl) ⟨10540656, by rfl⟩ : syracuseStep 28108417 = 21081313) B21081313
theorem B37477889 : Blo 2053435 37477889 := bstep (se 2 (by rfl) ⟨14054208, by rfl⟩ : syracuseStep 37477889 = 28108417) B28108417
theorem B24985259 : Blo 2053435 24985259 := bstep (se 1 (by rfl) ⟨18738944, by rfl⟩ : syracuseStep 24985259 = 37477889) B37477889
theorem B16656839 : Blo 2053435 16656839 := bstep (se 1 (by rfl) ⟨12492629, by rfl⟩ : syracuseStep 16656839 = 24985259) B24985259
theorem B11104559 : Blo 2053435 11104559 := bstep (se 1 (by rfl) ⟨8328419, by rfl⟩ : syracuseStep 11104559 = 16656839) B16656839
theorem B7403039 : Blo 2053435 7403039 := bstep (se 1 (by rfl) ⟨5552279, by rfl⟩ : syracuseStep 7403039 = 11104559) B11104559
theorem B4935359 : Blo 2053435 4935359 := bstep (se 1 (by rfl) ⟨3701519, by rfl⟩ : syracuseStep 4935359 = 7403039) B7403039
theorem B3290239 : Blo 2053435 3290239 := bstep (se 1 (by rfl) ⟨2467679, by rfl⟩ : syracuseStep 3290239 = 4935359) B4935359
theorem B17547941 : Blo 2053435 17547941 := bstep (se 4 (by rfl) ⟨1645119, by rfl⟩ : syracuseStep 17547941 = 3290239) B3290239
theorem B11698627 : Blo 2053435 11698627 := bstep (se 1 (by rfl) ⟨8773970, by rfl⟩ : syracuseStep 11698627 = 17547941) B17547941
theorem B15598169 : Blo 2053435 15598169 := bstep (se 2 (by rfl) ⟨5849313, by rfl⟩ : syracuseStep 15598169 = 11698627) B11698627
theorem B10398779 : Blo 2053435 10398779 := bstep (se 1 (by rfl) ⟨7799084, by rfl⟩ : syracuseStep 10398779 = 15598169) B15598169
theorem B6932519 : Blo 2053435 6932519 := bstep (se 1 (by rfl) ⟨5199389, by rfl⟩ : syracuseStep 6932519 = 10398779) B10398779
theorem B4621679 : Blo 2053435 4621679 := bstep (se 1 (by rfl) ⟨3466259, by rfl⟩ : syracuseStep 4621679 = 6932519) B6932519
theorem B3081119 : Blo 2053435 3081119 := bstep (se 1 (by rfl) ⟨2310839, by rfl⟩ : syracuseStep 3081119 = 4621679) B4621679
theorem B2054079 : Blo 2053435 2054079 := bstep (se 1 (by rfl) ⟨1540559, by rfl⟩ : syracuseStep 2054079 = 3081119) B3081119
theorem B3081125 : Blo 2053435 3081125 := bbase (se 4 (by rfl) ⟨288855, by rfl⟩ : syracuseStep 3081125 = 577711) (by norm_num)
theorem B2054083 : Blo 2053435 2054083 := bstep (se 1 (by rfl) ⟨1540562, by rfl⟩ : syracuseStep 2054083 = 3081125) B3081125
theorem B2599705 : Blo 2053435 2599705 := bbase (se 2 (by rfl) ⟨974889, by rfl⟩ : syracuseStep 2599705 = 1949779) (by norm_num)
theorem B3466273 : Blo 2053435 3466273 := bstep (se 2 (by rfl) ⟨1299852, by rfl⟩ : syracuseStep 3466273 = 2599705) B2599705
theorem B4621697 : Blo 2053435 4621697 := bstep (se 2 (by rfl) ⟨1733136, by rfl⟩ : syracuseStep 4621697 = 3466273) B3466273
theorem B3081131 : Blo 2053435 3081131 := bstep (se 1 (by rfl) ⟨2310848, by rfl⟩ : syracuseStep 3081131 = 4621697) B4621697
theorem B2054087 : Blo 2053435 2054087 := bstep (se 1 (by rfl) ⟨1540565, by rfl⟩ : syracuseStep 2054087 = 3081131) B3081131
theorem B2310853 : Blo 2053435 2310853 := bbase (se 4 (by rfl) ⟨216642, by rfl⟩ : syracuseStep 2310853 = 433285) (by norm_num)
theorem B3081137 : Blo 2053435 3081137 := bstep (se 2 (by rfl) ⟨1155426, by rfl⟩ : syracuseStep 3081137 = 2310853) B2310853
theorem B2054091 : Blo 2053435 2054091 := bstep (se 1 (by rfl) ⟨1540568, by rfl⟩ : syracuseStep 2054091 = 3081137) B3081137
theorem B3899573 : Blo 2053435 3899573 := bbase (se 5 (by rfl) ⟨182792, by rfl⟩ : syracuseStep 3899573 = 365585) (by norm_num)
theorem B2599715 : Blo 2053435 2599715 := bstep (se 1 (by rfl) ⟨1949786, by rfl⟩ : syracuseStep 2599715 = 3899573) B3899573
theorem B6932573 : Blo 2053435 6932573 := bstep (se 3 (by rfl) ⟨1299857, by rfl⟩ : syracuseStep 6932573 = 2599715) B2599715
theorem B4621715 : Blo 2053435 4621715 := bstep (se 1 (by rfl) ⟨3466286, by rfl⟩ : syracuseStep 4621715 = 6932573) B6932573
theorem B3081143 : Blo 2053435 3081143 := bstep (se 1 (by rfl) ⟨2310857, by rfl⟩ : syracuseStep 3081143 = 4621715) B4621715
theorem B2054095 : Blo 2053435 2054095 := bstep (se 1 (by rfl) ⟨1540571, by rfl⟩ : syracuseStep 2054095 = 3081143) B3081143
theorem B3081149 : Blo 2053435 3081149 := bbase (se 3 (by rfl) ⟨577715, by rfl⟩ : syracuseStep 3081149 = 1155431) (by norm_num)
theorem B2054099 : Blo 2053435 2054099 := bstep (se 1 (by rfl) ⟨1540574, by rfl⟩ : syracuseStep 2054099 = 3081149) B3081149
theorem B4621733 : Blo 2053435 4621733 := bbase (se 4 (by rfl) ⟨433287, by rfl⟩ : syracuseStep 4621733 = 866575) (by norm_num)
theorem B3081155 : Blo 2053435 3081155 := bstep (se 1 (by rfl) ⟨2310866, by rfl⟩ : syracuseStep 3081155 = 4621733) B4621733
theorem B2054103 : Blo 2053435 2054103 := bstep (se 1 (by rfl) ⟨1540577, by rfl⟩ : syracuseStep 2054103 = 3081155) B3081155
theorem B5199461 : Blo 2053435 5199461 := bbase (se 4 (by rfl) ⟨487449, by rfl⟩ : syracuseStep 5199461 = 974899) (by norm_num)
theorem B3466307 : Blo 2053435 3466307 := bstep (se 1 (by rfl) ⟨2599730, by rfl⟩ : syracuseStep 3466307 = 5199461) B5199461
theorem B2310871 : Blo 2053435 2310871 := bstep (se 1 (by rfl) ⟨1733153, by rfl⟩ : syracuseStep 2310871 = 3466307) B3466307
theorem B3081161 : Blo 2053435 3081161 := bstep (se 2 (by rfl) ⟨1155435, by rfl⟩ : syracuseStep 3081161 = 2310871) B2310871
theorem B2054107 : Blo 2053435 2054107 := bstep (se 1 (by rfl) ⟨1540580, by rfl⟩ : syracuseStep 2054107 = 3081161) B3081161
theorem B4935437 : Blo 2053435 4935437 := bbase (se 3 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 4935437 = 1850789) (by norm_num)
theorem B3290291 : Blo 2053435 3290291 := bstep (se 1 (by rfl) ⟨2467718, by rfl⟩ : syracuseStep 3290291 = 4935437) B4935437
theorem B2193527 : Blo 2053435 2193527 := bstep (se 1 (by rfl) ⟨1645145, by rfl⟩ : syracuseStep 2193527 = 3290291) B3290291
theorem B5849405 : Blo 2053435 5849405 := bstep (se 3 (by rfl) ⟨1096763, by rfl⟩ : syracuseStep 5849405 = 2193527) B2193527
theorem B3899603 : Blo 2053435 3899603 := bstep (se 1 (by rfl) ⟨2924702, by rfl⟩ : syracuseStep 3899603 = 5849405) B5849405
theorem B10398941 : Blo 2053435 10398941 := bstep (se 3 (by rfl) ⟨1949801, by rfl⟩ : syracuseStep 10398941 = 3899603) B3899603
theorem B6932627 : Blo 2053435 6932627 := bstep (se 1 (by rfl) ⟨5199470, by rfl⟩ : syracuseStep 6932627 = 10398941) B10398941
theorem B4621751 : Blo 2053435 4621751 := bstep (se 1 (by rfl) ⟨3466313, by rfl⟩ : syracuseStep 4621751 = 6932627) B6932627
theorem B3081167 : Blo 2053435 3081167 := bstep (se 1 (by rfl) ⟨2310875, by rfl⟩ : syracuseStep 3081167 = 4621751) B4621751
theorem B2054111 : Blo 2053435 2054111 := bstep (se 1 (by rfl) ⟨1540583, by rfl⟩ : syracuseStep 2054111 = 3081167) B3081167
theorem B3081173 : Blo 2053435 3081173 := bbase (se 7 (by rfl) ⟨36107, by rfl⟩ : syracuseStep 3081173 = 72215) (by norm_num)
theorem B2054115 : Blo 2053435 2054115 := bstep (se 1 (by rfl) ⟨1540586, by rfl⟩ : syracuseStep 2054115 = 3081173) B3081173
theorem B7799237 : Blo 2053435 7799237 := bbase (se 4 (by rfl) ⟨731178, by rfl⟩ : syracuseStep 7799237 = 1462357) (by norm_num)
theorem B5199491 : Blo 2053435 5199491 := bstep (se 1 (by rfl) ⟨3899618, by rfl⟩ : syracuseStep 5199491 = 7799237) B7799237
theorem B3466327 : Blo 2053435 3466327 := bstep (se 1 (by rfl) ⟨2599745, by rfl⟩ : syracuseStep 3466327 = 5199491) B5199491
theorem B4621769 : Blo 2053435 4621769 := bstep (se 2 (by rfl) ⟨1733163, by rfl⟩ : syracuseStep 4621769 = 3466327) B3466327
theorem B3081179 : Blo 2053435 3081179 := bstep (se 1 (by rfl) ⟨2310884, by rfl⟩ : syracuseStep 3081179 = 4621769) B4621769
theorem B2054119 : Blo 2053435 2054119 := bstep (se 1 (by rfl) ⟨1540589, by rfl⟩ : syracuseStep 2054119 = 3081179) B3081179
theorem B2310889 : Blo 2053435 2310889 := bbase (se 2 (by rfl) ⟨866583, by rfl⟩ : syracuseStep 2310889 = 1733167) (by norm_num)
theorem B3081185 : Blo 2053435 3081185 := bstep (se 2 (by rfl) ⟨1155444, by rfl⟩ : syracuseStep 3081185 = 2310889) B2310889
theorem B2054123 : Blo 2053435 2054123 := bstep (se 1 (by rfl) ⟨1540592, by rfl⟩ : syracuseStep 2054123 = 3081185) B3081185
theorem B11698901 : Blo 2053435 11698901 := bbase (se 7 (by rfl) ⟨137096, by rfl⟩ : syracuseStep 11698901 = 274193) (by norm_num)
theorem B7799267 : Blo 2053435 7799267 := bstep (se 1 (by rfl) ⟨5849450, by rfl⟩ : syracuseStep 7799267 = 11698901) B11698901
theorem B5199511 : Blo 2053435 5199511 := bstep (se 1 (by rfl) ⟨3899633, by rfl⟩ : syracuseStep 5199511 = 7799267) B7799267
theorem B6932681 : Blo 2053435 6932681 := bstep (se 2 (by rfl) ⟨2599755, by rfl⟩ : syracuseStep 6932681 = 5199511) B5199511
theorem B4621787 : Blo 2053435 4621787 := bstep (se 1 (by rfl) ⟨3466340, by rfl⟩ : syracuseStep 4621787 = 6932681) B6932681
theorem B3081191 : Blo 2053435 3081191 := bstep (se 1 (by rfl) ⟨2310893, by rfl⟩ : syracuseStep 3081191 = 4621787) B4621787
theorem B2054127 : Blo 2053435 2054127 := bstep (se 1 (by rfl) ⟨1540595, by rfl⟩ : syracuseStep 2054127 = 3081191) B3081191
theorem B3081197 : Blo 2053435 3081197 := bbase (se 3 (by rfl) ⟨577724, by rfl⟩ : syracuseStep 3081197 = 1155449) (by norm_num)
theorem B2054131 : Blo 2053435 2054131 := bstep (se 1 (by rfl) ⟨1540598, by rfl⟩ : syracuseStep 2054131 = 3081197) B3081197
theorem B4621805 : Blo 2053435 4621805 := bbase (se 3 (by rfl) ⟨866588, by rfl⟩ : syracuseStep 4621805 = 1733177) (by norm_num)
theorem B3081203 : Blo 2053435 3081203 := bstep (se 1 (by rfl) ⟨2310902, by rfl⟩ : syracuseStep 3081203 = 4621805) B4621805
theorem B2054135 : Blo 2053435 2054135 := bstep (se 1 (by rfl) ⟨1540601, by rfl⟩ : syracuseStep 2054135 = 3081203) B3081203
theorem B3701629 : Blo 2053435 3701629 := bbase (se 3 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 3701629 = 1388111) (by norm_num)
theorem B4935505 : Blo 2053435 4935505 := bstep (se 2 (by rfl) ⟨1850814, by rfl⟩ : syracuseStep 4935505 = 3701629) B3701629
theorem B6580673 : Blo 2053435 6580673 := bstep (se 2 (by rfl) ⟨2467752, by rfl⟩ : syracuseStep 6580673 = 4935505) B4935505
theorem B4387115 : Blo 2053435 4387115 := bstep (se 1 (by rfl) ⟨3290336, by rfl⟩ : syracuseStep 4387115 = 6580673) B6580673
theorem B2924743 : Blo 2053435 2924743 := bstep (se 1 (by rfl) ⟨2193557, by rfl⟩ : syracuseStep 2924743 = 4387115) B4387115
theorem B3899657 : Blo 2053435 3899657 := bstep (se 2 (by rfl) ⟨1462371, by rfl⟩ : syracuseStep 3899657 = 2924743) B2924743
theorem B2599771 : Blo 2053435 2599771 := bstep (se 1 (by rfl) ⟨1949828, by rfl⟩ : syracuseStep 2599771 = 3899657) B3899657
theorem B3466361 : Blo 2053435 3466361 := bstep (se 2 (by rfl) ⟨1299885, by rfl⟩ : syracuseStep 3466361 = 2599771) B2599771
theorem B2310907 : Blo 2053435 2310907 := bstep (se 1 (by rfl) ⟨1733180, by rfl⟩ : syracuseStep 2310907 = 3466361) B3466361
theorem B3081209 : Blo 2053435 3081209 := bstep (se 2 (by rfl) ⟨1155453, by rfl⟩ : syracuseStep 3081209 = 2310907) B2310907
theorem B2054139 : Blo 2053435 2054139 := bstep (se 1 (by rfl) ⟨1540604, by rfl⟩ : syracuseStep 2054139 = 3081209) B3081209
theorem B8328677 : Blo 2053435 8328677 := bbase (se 4 (by rfl) ⟨780813, by rfl⟩ : syracuseStep 8328677 = 1561627) (by norm_num)
theorem B22209805 : Blo 2053435 22209805 := bstep (se 3 (by rfl) ⟨4164338, by rfl⟩ : syracuseStep 22209805 = 8328677) B8328677
theorem B118452293 : Blo 2053435 118452293 := bstep (se 4 (by rfl) ⟨11104902, by rfl⟩ : syracuseStep 118452293 = 22209805) B22209805
theorem B78968195 : Blo 2053435 78968195 := bstep (se 1 (by rfl) ⟨59226146, by rfl⟩ : syracuseStep 78968195 = 118452293) B118452293
theorem B52645463 : Blo 2053435 52645463 := bstep (se 1 (by rfl) ⟨39484097, by rfl⟩ : syracuseStep 52645463 = 78968195) B78968195
theorem B35096975 : Blo 2053435 35096975 := bstep (se 1 (by rfl) ⟨26322731, by rfl⟩ : syracuseStep 35096975 = 52645463) B52645463
theorem B23397983 : Blo 2053435 23397983 := bstep (se 1 (by rfl) ⟨17548487, by rfl⟩ : syracuseStep 23397983 = 35096975) B35096975
theorem B15598655 : Blo 2053435 15598655 := bstep (se 1 (by rfl) ⟨11698991, by rfl⟩ : syracuseStep 15598655 = 23397983) B23397983
theorem B10399103 : Blo 2053435 10399103 := bstep (se 1 (by rfl) ⟨7799327, by rfl⟩ : syracuseStep 10399103 = 15598655) B15598655
theorem B6932735 : Blo 2053435 6932735 := bstep (se 1 (by rfl) ⟨5199551, by rfl⟩ : syracuseStep 6932735 = 10399103) B10399103
theorem B4621823 : Blo 2053435 4621823 := bstep (se 1 (by rfl) ⟨3466367, by rfl⟩ : syracuseStep 4621823 = 6932735) B6932735
theorem B3081215 : Blo 2053435 3081215 := bstep (se 1 (by rfl) ⟨2310911, by rfl⟩ : syracuseStep 3081215 = 4621823) B4621823
theorem B2054143 : Blo 2053435 2054143 := bstep (se 1 (by rfl) ⟨1540607, by rfl⟩ : syracuseStep 2054143 = 3081215) B3081215
theorem B3081221 : Blo 2053435 3081221 := bbase (se 4 (by rfl) ⟨288864, by rfl⟩ : syracuseStep 3081221 = 577729) (by norm_num)
theorem B2054147 : Blo 2053435 2054147 := bstep (se 1 (by rfl) ⟨1540610, by rfl⟩ : syracuseStep 2054147 = 3081221) B3081221
theorem B3466381 : Blo 2053435 3466381 := bbase (se 3 (by rfl) ⟨649946, by rfl⟩ : syracuseStep 3466381 = 1299893) (by norm_num)
theorem B4621841 : Blo 2053435 4621841 := bstep (se 2 (by rfl) ⟨1733190, by rfl⟩ : syracuseStep 4621841 = 3466381) B3466381
theorem B3081227 : Blo 2053435 3081227 := bstep (se 1 (by rfl) ⟨2310920, by rfl⟩ : syracuseStep 3081227 = 4621841) B4621841
theorem B2054151 : Blo 2053435 2054151 := bstep (se 1 (by rfl) ⟨1540613, by rfl⟩ : syracuseStep 2054151 = 3081227) B3081227
theorem B2310925 : Blo 2053435 2310925 := bbase (se 3 (by rfl) ⟨433298, by rfl⟩ : syracuseStep 2310925 = 866597) (by norm_num)
theorem B3081233 : Blo 2053435 3081233 := bstep (se 2 (by rfl) ⟨1155462, by rfl⟩ : syracuseStep 3081233 = 2310925) B2310925
theorem B2054155 : Blo 2053435 2054155 := bstep (se 1 (by rfl) ⟨1540616, by rfl⟩ : syracuseStep 2054155 = 3081233) B3081233
theorem B6932789 : Blo 2053435 6932789 := bbase (se 5 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 6932789 = 649949) (by norm_num)
theorem B4621859 : Blo 2053435 4621859 := bstep (se 1 (by rfl) ⟨3466394, by rfl⟩ : syracuseStep 4621859 = 6932789) B6932789
theorem B3081239 : Blo 2053435 3081239 := bstep (se 1 (by rfl) ⟨2310929, by rfl⟩ : syracuseStep 3081239 = 4621859) B4621859
theorem B2054159 : Blo 2053435 2054159 := bstep (se 1 (by rfl) ⟨1540619, by rfl⟩ : syracuseStep 2054159 = 3081239) B3081239
theorem B3081245 : Blo 2053435 3081245 := bbase (se 3 (by rfl) ⟨577733, by rfl⟩ : syracuseStep 3081245 = 1155467) (by norm_num)
theorem B2054163 : Blo 2053435 2054163 := bstep (se 1 (by rfl) ⟨1540622, by rfl⟩ : syracuseStep 2054163 = 3081245) B3081245
theorem B4621877 : Blo 2053435 4621877 := bbase (se 5 (by rfl) ⟨216650, by rfl⟩ : syracuseStep 4621877 = 433301) (by norm_num)
theorem B3081251 : Blo 2053435 3081251 := bstep (se 1 (by rfl) ⟨2310938, by rfl⟩ : syracuseStep 3081251 = 4621877) B4621877
theorem B2054167 : Blo 2053435 2054167 := bstep (se 1 (by rfl) ⟨1540625, by rfl⟩ : syracuseStep 2054167 = 3081251) B3081251
theorem B4935581 : Blo 2053435 4935581 := bbase (se 3 (by rfl) ⟨925421, by rfl⟩ : syracuseStep 4935581 = 1850843) (by norm_num)
theorem B3290387 : Blo 2053435 3290387 := bstep (se 1 (by rfl) ⟨2467790, by rfl⟩ : syracuseStep 3290387 = 4935581) B4935581
theorem B8774365 : Blo 2053435 8774365 := bstep (se 3 (by rfl) ⟨1645193, by rfl⟩ : syracuseStep 8774365 = 3290387) B3290387
theorem B11699153 : Blo 2053435 11699153 := bstep (se 2 (by rfl) ⟨4387182, by rfl⟩ : syracuseStep 11699153 = 8774365) B8774365
theorem B7799435 : Blo 2053435 7799435 := bstep (se 1 (by rfl) ⟨5849576, by rfl⟩ : syracuseStep 7799435 = 11699153) B11699153
theorem B5199623 : Blo 2053435 5199623 := bstep (se 1 (by rfl) ⟨3899717, by rfl⟩ : syracuseStep 5199623 = 7799435) B7799435
theorem B3466415 : Blo 2053435 3466415 := bstep (se 1 (by rfl) ⟨2599811, by rfl⟩ : syracuseStep 3466415 = 5199623) B5199623
theorem B2310943 : Blo 2053435 2310943 := bstep (se 1 (by rfl) ⟨1733207, by rfl⟩ : syracuseStep 2310943 = 3466415) B3466415
theorem B3081257 : Blo 2053435 3081257 := bstep (se 2 (by rfl) ⟨1155471, by rfl⟩ : syracuseStep 3081257 = 2310943) B2310943
theorem B2054171 : Blo 2053435 2054171 := bstep (se 1 (by rfl) ⟨1540628, by rfl⟩ : syracuseStep 2054171 = 3081257) B3081257
theorem B3701693 : Blo 2053435 3701693 := bbase (se 3 (by rfl) ⟨694067, by rfl⟩ : syracuseStep 3701693 = 1388135) (by norm_num)
theorem B2467795 : Blo 2053435 2467795 := bstep (se 1 (by rfl) ⟨1850846, by rfl⟩ : syracuseStep 2467795 = 3701693) B3701693
theorem B3290393 : Blo 2053435 3290393 := bstep (se 2 (by rfl) ⟨1233897, by rfl⟩ : syracuseStep 3290393 = 2467795) B2467795
theorem B8774381 : Blo 2053435 8774381 := bstep (se 3 (by rfl) ⟨1645196, by rfl⟩ : syracuseStep 8774381 = 3290393) B3290393
theorem B5849587 : Blo 2053435 5849587 := bstep (se 1 (by rfl) ⟨4387190, by rfl⟩ : syracuseStep 5849587 = 8774381) B8774381
theorem B7799449 : Blo 2053435 7799449 := bstep (se 2 (by rfl) ⟨2924793, by rfl⟩ : syracuseStep 7799449 = 5849587) B5849587
theorem B10399265 : Blo 2053435 10399265 := bstep (se 2 (by rfl) ⟨3899724, by rfl⟩ : syracuseStep 10399265 = 7799449) B7799449
theorem B6932843 : Blo 2053435 6932843 := bstep (se 1 (by rfl) ⟨5199632, by rfl⟩ : syracuseStep 6932843 = 10399265) B10399265
theorem B4621895 : Blo 2053435 4621895 := bstep (se 1 (by rfl) ⟨3466421, by rfl⟩ : syracuseStep 4621895 = 6932843) B6932843
theorem B3081263 : Blo 2053435 3081263 := bstep (se 1 (by rfl) ⟨2310947, by rfl⟩ : syracuseStep 3081263 = 4621895) B4621895
theorem B2054175 : Blo 2053435 2054175 := bstep (se 1 (by rfl) ⟨1540631, by rfl⟩ : syracuseStep 2054175 = 3081263) B3081263
theorem B3081269 : Blo 2053435 3081269 := bbase (se 5 (by rfl) ⟨144434, by rfl⟩ : syracuseStep 3081269 = 288869) (by norm_num)
theorem B2054179 : Blo 2053435 2054179 := bstep (se 1 (by rfl) ⟨1540634, by rfl⟩ : syracuseStep 2054179 = 3081269) B3081269
theorem B5199653 : Blo 2053435 5199653 := bbase (se 4 (by rfl) ⟨487467, by rfl⟩ : syracuseStep 5199653 = 974935) (by norm_num)
theorem B3466435 : Blo 2053435 3466435 := bstep (se 1 (by rfl) ⟨2599826, by rfl⟩ : syracuseStep 3466435 = 5199653) B5199653
theorem B4621913 : Blo 2053435 4621913 := bstep (se 2 (by rfl) ⟨1733217, by rfl⟩ : syracuseStep 4621913 = 3466435) B3466435
theorem B3081275 : Blo 2053435 3081275 := bstep (se 1 (by rfl) ⟨2310956, by rfl⟩ : syracuseStep 3081275 = 4621913) B4621913
theorem B2054183 : Blo 2053435 2054183 := bstep (se 1 (by rfl) ⟨1540637, by rfl⟩ : syracuseStep 2054183 = 3081275) B3081275
theorem B2310961 : Blo 2053435 2310961 := bbase (se 2 (by rfl) ⟨866610, by rfl⟩ : syracuseStep 2310961 = 1733221) (by norm_num)
theorem B3081281 : Blo 2053435 3081281 := bstep (se 2 (by rfl) ⟨1155480, by rfl⟩ : syracuseStep 3081281 = 2310961) B2310961
theorem B2054187 : Blo 2053435 2054187 := bstep (se 1 (by rfl) ⟨1540640, by rfl⟩ : syracuseStep 2054187 = 3081281) B3081281
theorem B4935629 : Blo 2053435 4935629 := bbase (se 3 (by rfl) ⟨925430, by rfl⟩ : syracuseStep 4935629 = 1850861) (by norm_num)
theorem B3290419 : Blo 2053435 3290419 := bstep (se 1 (by rfl) ⟨2467814, by rfl⟩ : syracuseStep 3290419 = 4935629) B4935629
theorem B4387225 : Blo 2053435 4387225 := bstep (se 2 (by rfl) ⟨1645209, by rfl⟩ : syracuseStep 4387225 = 3290419) B3290419
theorem B5849633 : Blo 2053435 5849633 := bstep (se 2 (by rfl) ⟨2193612, by rfl⟩ : syracuseStep 5849633 = 4387225) B4387225
theorem B3899755 : Blo 2053435 3899755 := bstep (se 1 (by rfl) ⟨2924816, by rfl⟩ : syracuseStep 3899755 = 5849633) B5849633
theorem B5199673 : Blo 2053435 5199673 := bstep (se 2 (by rfl) ⟨1949877, by rfl⟩ : syracuseStep 5199673 = 3899755) B3899755
theorem B6932897 : Blo 2053435 6932897 := bstep (se 2 (by rfl) ⟨2599836, by rfl⟩ : syracuseStep 6932897 = 5199673) B5199673
theorem B4621931 : Blo 2053435 4621931 := bstep (se 1 (by rfl) ⟨3466448, by rfl⟩ : syracuseStep 4621931 = 6932897) B6932897
theorem B3081287 : Blo 2053435 3081287 := bstep (se 1 (by rfl) ⟨2310965, by rfl⟩ : syracuseStep 3081287 = 4621931) B4621931
theorem B2054191 : Blo 2053435 2054191 := bstep (se 1 (by rfl) ⟨1540643, by rfl⟩ : syracuseStep 2054191 = 3081287) B3081287
theorem B3081293 : Blo 2053435 3081293 := bbase (se 3 (by rfl) ⟨577742, by rfl⟩ : syracuseStep 3081293 = 1155485) (by norm_num)
theorem B2054195 : Blo 2053435 2054195 := bstep (se 1 (by rfl) ⟨1540646, by rfl⟩ : syracuseStep 2054195 = 3081293) B3081293
theorem B4621949 : Blo 2053435 4621949 := bbase (se 3 (by rfl) ⟨866615, by rfl⟩ : syracuseStep 4621949 = 1733231) (by norm_num)
theorem B3081299 : Blo 2053435 3081299 := bstep (se 1 (by rfl) ⟨2310974, by rfl⟩ : syracuseStep 3081299 = 4621949) B4621949
theorem B2054199 : Blo 2053435 2054199 := bstep (se 1 (by rfl) ⟨1540649, by rfl⟩ : syracuseStep 2054199 = 3081299) B3081299
theorem B3466469 : Blo 2053435 3466469 := bbase (se 4 (by rfl) ⟨324981, by rfl⟩ : syracuseStep 3466469 = 649963) (by norm_num)
theorem B2310979 : Blo 2053435 2310979 := bstep (se 1 (by rfl) ⟨1733234, by rfl⟩ : syracuseStep 2310979 = 3466469) B3466469
theorem B3081305 : Blo 2053435 3081305 := bstep (se 2 (by rfl) ⟨1155489, by rfl⟩ : syracuseStep 3081305 = 2310979) B2310979
theorem B2054203 : Blo 2053435 2054203 := bstep (se 1 (by rfl) ⟨1540652, by rfl⟩ : syracuseStep 2054203 = 3081305) B3081305
theorem B3513773 : Blo 2053435 3513773 := bbase (se 3 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 3513773 = 1317665) (by norm_num)
theorem B2342515 : Blo 2053435 2342515 := bstep (se 1 (by rfl) ⟨1756886, by rfl⟩ : syracuseStep 2342515 = 3513773) B3513773
theorem B3123353 : Blo 2053435 3123353 := bstep (se 2 (by rfl) ⟨1171257, by rfl⟩ : syracuseStep 3123353 = 2342515) B2342515
theorem B2082235 : Blo 2053435 2082235 := bstep (se 1 (by rfl) ⟨1561676, by rfl⟩ : syracuseStep 2082235 = 3123353) B3123353
theorem B2776313 : Blo 2053435 2776313 := bstep (se 2 (by rfl) ⟨1041117, by rfl⟩ : syracuseStep 2776313 = 2082235) B2082235
theorem B7403501 : Blo 2053435 7403501 := bstep (se 3 (by rfl) ⟨1388156, by rfl⟩ : syracuseStep 7403501 = 2776313) B2776313
theorem B4935667 : Blo 2053435 4935667 := bstep (se 1 (by rfl) ⟨3701750, by rfl⟩ : syracuseStep 4935667 = 7403501) B7403501
theorem B6580889 : Blo 2053435 6580889 := bstep (se 2 (by rfl) ⟨2467833, by rfl⟩ : syracuseStep 6580889 = 4935667) B4935667
theorem B4387259 : Blo 2053435 4387259 := bstep (se 1 (by rfl) ⟨3290444, by rfl⟩ : syracuseStep 4387259 = 6580889) B6580889
theorem B2924839 : Blo 2053435 2924839 := bstep (se 1 (by rfl) ⟨2193629, by rfl⟩ : syracuseStep 2924839 = 4387259) B4387259
theorem B15599141 : Blo 2053435 15599141 := bstep (se 4 (by rfl) ⟨1462419, by rfl⟩ : syracuseStep 15599141 = 2924839) B2924839
theorem B10399427 : Blo 2053435 10399427 := bstep (se 1 (by rfl) ⟨7799570, by rfl⟩ : syracuseStep 10399427 = 15599141) B15599141
theorem B6932951 : Blo 2053435 6932951 := bstep (se 1 (by rfl) ⟨5199713, by rfl⟩ : syracuseStep 6932951 = 10399427) B10399427
theorem B4621967 : Blo 2053435 4621967 := bstep (se 1 (by rfl) ⟨3466475, by rfl⟩ : syracuseStep 4621967 = 6932951) B6932951
theorem B3081311 : Blo 2053435 3081311 := bstep (se 1 (by rfl) ⟨2310983, by rfl⟩ : syracuseStep 3081311 = 4621967) B4621967
theorem B2054207 : Blo 2053435 2054207 := bstep (se 1 (by rfl) ⟨1540655, by rfl⟩ : syracuseStep 2054207 = 3081311) B3081311
theorem B3081317 : Blo 2053435 3081317 := bbase (se 4 (by rfl) ⟨288873, by rfl⟩ : syracuseStep 3081317 = 577747) (by norm_num)
theorem B2054211 : Blo 2053435 2054211 := bstep (se 1 (by rfl) ⟨1540658, by rfl⟩ : syracuseStep 2054211 = 3081317) B3081317
theorem B4387277 : Blo 2053435 4387277 := bbase (se 3 (by rfl) ⟨822614, by rfl⟩ : syracuseStep 4387277 = 1645229) (by norm_num)
theorem B2924851 : Blo 2053435 2924851 := bstep (se 1 (by rfl) ⟨2193638, by rfl⟩ : syracuseStep 2924851 = 4387277) B4387277
theorem B3899801 : Blo 2053435 3899801 := bstep (se 2 (by rfl) ⟨1462425, by rfl⟩ : syracuseStep 3899801 = 2924851) B2924851
theorem B2599867 : Blo 2053435 2599867 := bstep (se 1 (by rfl) ⟨1949900, by rfl⟩ : syracuseStep 2599867 = 3899801) B3899801
theorem B3466489 : Blo 2053435 3466489 := bstep (se 2 (by rfl) ⟨1299933, by rfl⟩ : syracuseStep 3466489 = 2599867) B2599867
theorem B4621985 : Blo 2053435 4621985 := bstep (se 2 (by rfl) ⟨1733244, by rfl⟩ : syracuseStep 4621985 = 3466489) B3466489
theorem B3081323 : Blo 2053435 3081323 := bstep (se 1 (by rfl) ⟨2310992, by rfl⟩ : syracuseStep 3081323 = 4621985) B4621985
theorem B2054215 : Blo 2053435 2054215 := bstep (se 1 (by rfl) ⟨1540661, by rfl⟩ : syracuseStep 2054215 = 3081323) B3081323
theorem B2310997 : Blo 2053435 2310997 := bbase (se 9 (by rfl) ⟨6770, by rfl⟩ : syracuseStep 2310997 = 13541) (by norm_num)
theorem B3081329 : Blo 2053435 3081329 := bstep (se 2 (by rfl) ⟨1155498, by rfl⟩ : syracuseStep 3081329 = 2310997) B2310997
theorem B2054219 : Blo 2053435 2054219 := bstep (se 1 (by rfl) ⟨1540664, by rfl⟩ : syracuseStep 2054219 = 3081329) B3081329
theorem B2599877 : Blo 2053435 2599877 := bbase (se 4 (by rfl) ⟨243738, by rfl⟩ : syracuseStep 2599877 = 487477) (by norm_num)
theorem B6933005 : Blo 2053435 6933005 := bstep (se 3 (by rfl) ⟨1299938, by rfl⟩ : syracuseStep 6933005 = 2599877) B2599877
theorem B4622003 : Blo 2053435 4622003 := bstep (se 1 (by rfl) ⟨3466502, by rfl⟩ : syracuseStep 4622003 = 6933005) B6933005
theorem B3081335 : Blo 2053435 3081335 := bstep (se 1 (by rfl) ⟨2311001, by rfl⟩ : syracuseStep 3081335 = 4622003) B4622003
theorem B2054223 : Blo 2053435 2054223 := bstep (se 1 (by rfl) ⟨1540667, by rfl⟩ : syracuseStep 2054223 = 3081335) B3081335
theorem B3081341 : Blo 2053435 3081341 := bbase (se 3 (by rfl) ⟨577751, by rfl⟩ : syracuseStep 3081341 = 1155503) (by norm_num)
theorem B2054227 : Blo 2053435 2054227 := bstep (se 1 (by rfl) ⟨1540670, by rfl⟩ : syracuseStep 2054227 = 3081341) B3081341
theorem B4622021 : Blo 2053435 4622021 := bbase (se 4 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 4622021 = 866629) (by norm_num)
theorem B3081347 : Blo 2053435 3081347 := bstep (se 1 (by rfl) ⟨2311010, by rfl⟩ : syracuseStep 3081347 = 4622021) B4622021
theorem B2054231 : Blo 2053435 2054231 := bstep (se 1 (by rfl) ⟨1540673, by rfl⟩ : syracuseStep 2054231 = 3081347) B3081347
theorem B8894357 : Blo 2053435 8894357 := bbase (se 6 (by rfl) ⟨208461, by rfl⟩ : syracuseStep 8894357 = 416923) (by norm_num)
theorem B5929571 : Blo 2053435 5929571 := bstep (se 1 (by rfl) ⟨4447178, by rfl⟩ : syracuseStep 5929571 = 8894357) B8894357
theorem B3953047 : Blo 2053435 3953047 := bstep (se 1 (by rfl) ⟨2964785, by rfl⟩ : syracuseStep 3953047 = 5929571) B5929571
theorem B5270729 : Blo 2053435 5270729 := bstep (se 2 (by rfl) ⟨1976523, by rfl⟩ : syracuseStep 5270729 = 3953047) B3953047
theorem B14055277 : Blo 2053435 14055277 := bstep (se 3 (by rfl) ⟨2635364, by rfl⟩ : syracuseStep 14055277 = 5270729) B5270729
theorem B18740369 : Blo 2053435 18740369 := bstep (se 2 (by rfl) ⟨7027638, by rfl⟩ : syracuseStep 18740369 = 14055277) B14055277
theorem B49974317 : Blo 2053435 49974317 := bstep (se 3 (by rfl) ⟨9370184, by rfl⟩ : syracuseStep 49974317 = 18740369) B18740369
theorem B33316211 : Blo 2053435 33316211 := bstep (se 1 (by rfl) ⟨24987158, by rfl⟩ : syracuseStep 33316211 = 49974317) B49974317
theorem B22210807 : Blo 2053435 22210807 := bstep (se 1 (by rfl) ⟨16658105, by rfl⟩ : syracuseStep 22210807 = 33316211) B33316211
theorem B29614409 : Blo 2053435 29614409 := bstep (se 2 (by rfl) ⟨11105403, by rfl⟩ : syracuseStep 29614409 = 22210807) B22210807
theorem B19742939 : Blo 2053435 19742939 := bstep (se 1 (by rfl) ⟨14807204, by rfl⟩ : syracuseStep 19742939 = 29614409) B29614409
theorem B13161959 : Blo 2053435 13161959 := bstep (se 1 (by rfl) ⟨9871469, by rfl⟩ : syracuseStep 13161959 = 19742939) B19742939
theorem B8774639 : Blo 2053435 8774639 := bstep (se 1 (by rfl) ⟨6580979, by rfl⟩ : syracuseStep 8774639 = 13161959) B13161959
theorem B5849759 : Blo 2053435 5849759 := bstep (se 1 (by rfl) ⟨4387319, by rfl⟩ : syracuseStep 5849759 = 8774639) B8774639
theorem B3899839 : Blo 2053435 3899839 := bstep (se 1 (by rfl) ⟨2924879, by rfl⟩ : syracuseStep 3899839 = 5849759) B5849759
theorem B5199785 : Blo 2053435 5199785 := bstep (se 2 (by rfl) ⟨1949919, by rfl⟩ : syracuseStep 5199785 = 3899839) B3899839
theorem B3466523 : Blo 2053435 3466523 := bstep (se 1 (by rfl) ⟨2599892, by rfl⟩ : syracuseStep 3466523 = 5199785) B5199785
theorem B2311015 : Blo 2053435 2311015 := bstep (se 1 (by rfl) ⟨1733261, by rfl⟩ : syracuseStep 2311015 = 3466523) B3466523
theorem B3081353 : Blo 2053435 3081353 := bstep (se 2 (by rfl) ⟨1155507, by rfl⟩ : syracuseStep 3081353 = 2311015) B2311015
theorem B2054235 : Blo 2053435 2054235 := bstep (se 1 (by rfl) ⟨1540676, by rfl⟩ : syracuseStep 2054235 = 3081353) B3081353
theorem B10399589 : Blo 2053435 10399589 := bbase (se 4 (by rfl) ⟨974961, by rfl⟩ : syracuseStep 10399589 = 1949923) (by norm_num)
theorem B6933059 : Blo 2053435 6933059 := bstep (se 1 (by rfl) ⟨5199794, by rfl⟩ : syracuseStep 6933059 = 10399589) B10399589
theorem B4622039 : Blo 2053435 4622039 := bstep (se 1 (by rfl) ⟨3466529, by rfl⟩ : syracuseStep 4622039 = 6933059) B6933059
theorem B3081359 : Blo 2053435 3081359 := bstep (se 1 (by rfl) ⟨2311019, by rfl⟩ : syracuseStep 3081359 = 4622039) B4622039
theorem B2054239 : Blo 2053435 2054239 := bstep (se 1 (by rfl) ⟨1540679, by rfl⟩ : syracuseStep 2054239 = 3081359) B3081359
theorem B3081365 : Blo 2053435 3081365 := bbase (se 6 (by rfl) ⟨72219, by rfl⟩ : syracuseStep 3081365 = 144439) (by norm_num)
theorem B2054243 : Blo 2053435 2054243 := bstep (se 1 (by rfl) ⟨1540682, by rfl⟩ : syracuseStep 2054243 = 3081365) B3081365
theorem B10006213 : Blo 2053435 10006213 := bbase (se 4 (by rfl) ⟨938082, by rfl⟩ : syracuseStep 10006213 = 1876165) (by norm_num)
theorem B13341617 : Blo 2053435 13341617 := bstep (se 2 (by rfl) ⟨5003106, by rfl⟩ : syracuseStep 13341617 = 10006213) B10006213
theorem B8894411 : Blo 2053435 8894411 := bstep (se 1 (by rfl) ⟨6670808, by rfl⟩ : syracuseStep 8894411 = 13341617) B13341617
theorem B5929607 : Blo 2053435 5929607 := bstep (se 1 (by rfl) ⟨4447205, by rfl⟩ : syracuseStep 5929607 = 8894411) B8894411
theorem B3953071 : Blo 2053435 3953071 := bstep (se 1 (by rfl) ⟨2964803, by rfl⟩ : syracuseStep 3953071 = 5929607) B5929607
theorem B5270761 : Blo 2053435 5270761 := bstep (se 2 (by rfl) ⟨1976535, by rfl⟩ : syracuseStep 5270761 = 3953071) B3953071
theorem B7027681 : Blo 2053435 7027681 := bstep (se 2 (by rfl) ⟨2635380, by rfl⟩ : syracuseStep 7027681 = 5270761) B5270761
theorem B9370241 : Blo 2053435 9370241 := bstep (se 2 (by rfl) ⟨3513840, by rfl⟩ : syracuseStep 9370241 = 7027681) B7027681
theorem B6246827 : Blo 2053435 6246827 := bstep (se 1 (by rfl) ⟨4685120, by rfl⟩ : syracuseStep 6246827 = 9370241) B9370241
theorem B4164551 : Blo 2053435 4164551 := bstep (se 1 (by rfl) ⟨3123413, by rfl⟩ : syracuseStep 4164551 = 6246827) B6246827
theorem B2776367 : Blo 2053435 2776367 := bstep (se 1 (by rfl) ⟨2082275, by rfl⟩ : syracuseStep 2776367 = 4164551) B4164551
theorem B7403645 : Blo 2053435 7403645 := bstep (se 3 (by rfl) ⟨1388183, by rfl⟩ : syracuseStep 7403645 = 2776367) B2776367
theorem B4935763 : Blo 2053435 4935763 := bstep (se 1 (by rfl) ⟨3701822, by rfl⟩ : syracuseStep 4935763 = 7403645) B7403645
theorem B6581017 : Blo 2053435 6581017 := bstep (se 2 (by rfl) ⟨2467881, by rfl⟩ : syracuseStep 6581017 = 4935763) B4935763
theorem B8774689 : Blo 2053435 8774689 := bstep (se 2 (by rfl) ⟨3290508, by rfl⟩ : syracuseStep 8774689 = 6581017) B6581017
theorem B11699585 : Blo 2053435 11699585 := bstep (se 2 (by rfl) ⟨4387344, by rfl⟩ : syracuseStep 11699585 = 8774689) B8774689
theorem B7799723 : Blo 2053435 7799723 := bstep (se 1 (by rfl) ⟨5849792, by rfl⟩ : syracuseStep 7799723 = 11699585) B11699585
theorem B5199815 : Blo 2053435 5199815 := bstep (se 1 (by rfl) ⟨3899861, by rfl⟩ : syracuseStep 5199815 = 7799723) B7799723
theorem B3466543 : Blo 2053435 3466543 := bstep (se 1 (by rfl) ⟨2599907, by rfl⟩ : syracuseStep 3466543 = 5199815) B5199815
theorem B4622057 : Blo 2053435 4622057 := bstep (se 2 (by rfl) ⟨1733271, by rfl⟩ : syracuseStep 4622057 = 3466543) B3466543
theorem B3081371 : Blo 2053435 3081371 := bstep (se 1 (by rfl) ⟨2311028, by rfl⟩ : syracuseStep 3081371 = 4622057) B4622057
theorem B2054247 : Blo 2053435 2054247 := bstep (se 1 (by rfl) ⟨1540685, by rfl⟩ : syracuseStep 2054247 = 3081371) B3081371
theorem B2311033 : Blo 2053435 2311033 := bbase (se 2 (by rfl) ⟨866637, by rfl⟩ : syracuseStep 2311033 = 1733275) (by norm_num)
theorem B3081377 : Blo 2053435 3081377 := bstep (se 2 (by rfl) ⟨1155516, by rfl⟩ : syracuseStep 3081377 = 2311033) B2311033
theorem B2054251 : Blo 2053435 2054251 := bstep (se 1 (by rfl) ⟨1540688, by rfl⟩ : syracuseStep 2054251 = 3081377) B3081377
theorem B3701837 : Blo 2053435 3701837 := bbase (se 3 (by rfl) ⟨694094, by rfl⟩ : syracuseStep 3701837 = 1388189) (by norm_num)
theorem B2467891 : Blo 2053435 2467891 := bstep (se 1 (by rfl) ⟨1850918, by rfl⟩ : syracuseStep 2467891 = 3701837) B3701837
theorem B13162085 : Blo 2053435 13162085 := bstep (se 4 (by rfl) ⟨1233945, by rfl⟩ : syracuseStep 13162085 = 2467891) B2467891
theorem B8774723 : Blo 2053435 8774723 := bstep (se 1 (by rfl) ⟨6581042, by rfl⟩ : syracuseStep 8774723 = 13162085) B13162085
theorem B5849815 : Blo 2053435 5849815 := bstep (se 1 (by rfl) ⟨4387361, by rfl⟩ : syracuseStep 5849815 = 8774723) B8774723
theorem B7799753 : Blo 2053435 7799753 := bstep (se 2 (by rfl) ⟨2924907, by rfl⟩ : syracuseStep 7799753 = 5849815) B5849815
theorem B5199835 : Blo 2053435 5199835 := bstep (se 1 (by rfl) ⟨3899876, by rfl⟩ : syracuseStep 5199835 = 7799753) B7799753
theorem B6933113 : Blo 2053435 6933113 := bstep (se 2 (by rfl) ⟨2599917, by rfl⟩ : syracuseStep 6933113 = 5199835) B5199835
theorem B4622075 : Blo 2053435 4622075 := bstep (se 1 (by rfl) ⟨3466556, by rfl⟩ : syracuseStep 4622075 = 6933113) B6933113
theorem B3081383 : Blo 2053435 3081383 := bstep (se 1 (by rfl) ⟨2311037, by rfl⟩ : syracuseStep 3081383 = 4622075) B4622075
theorem B2054255 : Blo 2053435 2054255 := bstep (se 1 (by rfl) ⟨1540691, by rfl⟩ : syracuseStep 2054255 = 3081383) B3081383
theorem B3081389 : Blo 2053435 3081389 := bbase (se 3 (by rfl) ⟨577760, by rfl⟩ : syracuseStep 3081389 = 1155521) (by norm_num)
theorem B2054259 : Blo 2053435 2054259 := bstep (se 1 (by rfl) ⟨1540694, by rfl⟩ : syracuseStep 2054259 = 3081389) B3081389
theorem B4622093 : Blo 2053435 4622093 := bbase (se 3 (by rfl) ⟨866642, by rfl⟩ : syracuseStep 4622093 = 1733285) (by norm_num)
theorem B3081395 : Blo 2053435 3081395 := bstep (se 1 (by rfl) ⟨2311046, by rfl⟩ : syracuseStep 3081395 = 4622093) B4622093
theorem B2054263 : Blo 2053435 2054263 := bstep (se 1 (by rfl) ⟨1540697, by rfl⟩ : syracuseStep 2054263 = 3081395) B3081395
theorem B2599933 : Blo 2053435 2599933 := bbase (se 3 (by rfl) ⟨487487, by rfl⟩ : syracuseStep 2599933 = 974975) (by norm_num)
theorem B3466577 : Blo 2053435 3466577 := bstep (se 2 (by rfl) ⟨1299966, by rfl⟩ : syracuseStep 3466577 = 2599933) B2599933
theorem B2311051 : Blo 2053435 2311051 := bstep (se 1 (by rfl) ⟨1733288, by rfl⟩ : syracuseStep 2311051 = 3466577) B3466577
theorem B3081401 : Blo 2053435 3081401 := bstep (se 2 (by rfl) ⟨1155525, by rfl⟩ : syracuseStep 3081401 = 2311051) B2311051
theorem B2054267 : Blo 2053435 2054267 := bstep (se 1 (by rfl) ⟨1540700, by rfl⟩ : syracuseStep 2054267 = 3081401) B3081401
theorem B6581093 : Blo 2053435 6581093 := bbase (se 4 (by rfl) ⟨616977, by rfl⟩ : syracuseStep 6581093 = 1233955) (by norm_num)
theorem B17549581 : Blo 2053435 17549581 := bstep (se 3 (by rfl) ⟨3290546, by rfl⟩ : syracuseStep 17549581 = 6581093) B6581093
theorem B23399441 : Blo 2053435 23399441 := bstep (se 2 (by rfl) ⟨8774790, by rfl⟩ : syracuseStep 23399441 = 17549581) B17549581
theorem B15599627 : Blo 2053435 15599627 := bstep (se 1 (by rfl) ⟨11699720, by rfl⟩ : syracuseStep 15599627 = 23399441) B23399441
theorem B10399751 : Blo 2053435 10399751 := bstep (se 1 (by rfl) ⟨7799813, by rfl⟩ : syracuseStep 10399751 = 15599627) B15599627
theorem B6933167 : Blo 2053435 6933167 := bstep (se 1 (by rfl) ⟨5199875, by rfl⟩ : syracuseStep 6933167 = 10399751) B10399751
theorem B4622111 : Blo 2053435 4622111 := bstep (se 1 (by rfl) ⟨3466583, by rfl⟩ : syracuseStep 4622111 = 6933167) B6933167
theorem B3081407 : Blo 2053435 3081407 := bstep (se 1 (by rfl) ⟨2311055, by rfl⟩ : syracuseStep 3081407 = 4622111) B4622111
theorem B2054271 : Blo 2053435 2054271 := bstep (se 1 (by rfl) ⟨1540703, by rfl⟩ : syracuseStep 2054271 = 3081407) B3081407
theorem B3081413 : Blo 2053435 3081413 := bbase (se 4 (by rfl) ⟨288882, by rfl⟩ : syracuseStep 3081413 = 577765) (by norm_num)
theorem B2054275 : Blo 2053435 2054275 := bstep (se 1 (by rfl) ⟨1540706, by rfl⟩ : syracuseStep 2054275 = 3081413) B3081413
theorem B3466597 : Blo 2053435 3466597 := bbase (se 4 (by rfl) ⟨324993, by rfl⟩ : syracuseStep 3466597 = 649987) (by norm_num)
theorem B4622129 : Blo 2053435 4622129 := bstep (se 2 (by rfl) ⟨1733298, by rfl⟩ : syracuseStep 4622129 = 3466597) B3466597
theorem B3081419 : Blo 2053435 3081419 := bstep (se 1 (by rfl) ⟨2311064, by rfl⟩ : syracuseStep 3081419 = 4622129) B4622129
theorem B2054279 : Blo 2053435 2054279 := bstep (se 1 (by rfl) ⟨1540709, by rfl⟩ : syracuseStep 2054279 = 3081419) B3081419
theorem B2311069 : Blo 2053435 2311069 := bbase (se 3 (by rfl) ⟨433325, by rfl⟩ : syracuseStep 2311069 = 866651) (by norm_num)
theorem B3081425 : Blo 2053435 3081425 := bstep (se 2 (by rfl) ⟨1155534, by rfl⟩ : syracuseStep 3081425 = 2311069) B2311069
theorem B2054283 : Blo 2053435 2054283 := bstep (se 1 (by rfl) ⟨1540712, by rfl⟩ : syracuseStep 2054283 = 3081425) B3081425
theorem B6933221 : Blo 2053435 6933221 := bbase (se 4 (by rfl) ⟨649989, by rfl⟩ : syracuseStep 6933221 = 1299979) (by norm_num)
theorem B4622147 : Blo 2053435 4622147 := bstep (se 1 (by rfl) ⟨3466610, by rfl⟩ : syracuseStep 4622147 = 6933221) B6933221
theorem B3081431 : Blo 2053435 3081431 := bstep (se 1 (by rfl) ⟨2311073, by rfl⟩ : syracuseStep 3081431 = 4622147) B4622147
theorem B2054287 : Blo 2053435 2054287 := bstep (se 1 (by rfl) ⟨1540715, by rfl⟩ : syracuseStep 2054287 = 3081431) B3081431
theorem B3081437 : Blo 2053435 3081437 := bbase (se 3 (by rfl) ⟨577769, by rfl⟩ : syracuseStep 3081437 = 1155539) (by norm_num)
theorem B2054291 : Blo 2053435 2054291 := bstep (se 1 (by rfl) ⟨1540718, by rfl⟩ : syracuseStep 2054291 = 3081437) B3081437
theorem B4622165 : Blo 2053435 4622165 := bbase (se 9 (by rfl) ⟨13541, by rfl⟩ : syracuseStep 4622165 = 27083) (by norm_num)
theorem B3081443 : Blo 2053435 3081443 := bstep (se 1 (by rfl) ⟨2311082, by rfl⟩ : syracuseStep 3081443 = 4622165) B4622165
theorem B2054295 : Blo 2053435 2054295 := bstep (se 1 (by rfl) ⟨1540721, by rfl⟩ : syracuseStep 2054295 = 3081443) B3081443
theorem B5849941 : Blo 2053435 5849941 := bbase (se 9 (by rfl) ⟨17138, by rfl⟩ : syracuseStep 5849941 = 34277) (by norm_num)
theorem B7799921 : Blo 2053435 7799921 := bstep (se 2 (by rfl) ⟨2924970, by rfl⟩ : syracuseStep 7799921 = 5849941) B5849941
theorem B5199947 : Blo 2053435 5199947 := bstep (se 1 (by rfl) ⟨3899960, by rfl⟩ : syracuseStep 5199947 = 7799921) B7799921
theorem B3466631 : Blo 2053435 3466631 := bstep (se 1 (by rfl) ⟨2599973, by rfl⟩ : syracuseStep 3466631 = 5199947) B5199947
theorem B2311087 : Blo 2053435 2311087 := bstep (se 1 (by rfl) ⟨1733315, by rfl⟩ : syracuseStep 2311087 = 3466631) B3466631
theorem B3081449 : Blo 2053435 3081449 := bstep (se 2 (by rfl) ⟨1155543, by rfl⟩ : syracuseStep 3081449 = 2311087) B2311087
theorem B2054299 : Blo 2053435 2054299 := bstep (se 1 (by rfl) ⟨1540724, by rfl⟩ : syracuseStep 2054299 = 3081449) B3081449
theorem B4447325 : Blo 2053435 4447325 := bbase (se 3 (by rfl) ⟨833873, by rfl⟩ : syracuseStep 4447325 = 1667747) (by norm_num)
theorem B11859533 : Blo 2053435 11859533 := bstep (se 3 (by rfl) ⟨2223662, by rfl⟩ : syracuseStep 11859533 = 4447325) B4447325
theorem B7906355 : Blo 2053435 7906355 := bstep (se 1 (by rfl) ⟨5929766, by rfl⟩ : syracuseStep 7906355 = 11859533) B11859533
theorem B5270903 : Blo 2053435 5270903 := bstep (se 1 (by rfl) ⟨3953177, by rfl⟩ : syracuseStep 5270903 = 7906355) B7906355
theorem B3513935 : Blo 2053435 3513935 := bstep (se 1 (by rfl) ⟨2635451, by rfl⟩ : syracuseStep 3513935 = 5270903) B5270903
theorem B2342623 : Blo 2053435 2342623 := bstep (se 1 (by rfl) ⟨1756967, by rfl⟩ : syracuseStep 2342623 = 3513935) B3513935
theorem B49975957 : Blo 2053435 49975957 := bstep (se 6 (by rfl) ⟨1171311, by rfl⟩ : syracuseStep 49975957 = 2342623) B2342623
theorem B66634609 : Blo 2053435 66634609 := bstep (se 2 (by rfl) ⟨24987978, by rfl⟩ : syracuseStep 66634609 = 49975957) B49975957
theorem B88846145 : Blo 2053435 88846145 := bstep (se 2 (by rfl) ⟨33317304, by rfl⟩ : syracuseStep 88846145 = 66634609) B66634609
theorem B59230763 : Blo 2053435 59230763 := bstep (se 1 (by rfl) ⟨44423072, by rfl⟩ : syracuseStep 59230763 = 88846145) B88846145
theorem B39487175 : Blo 2053435 39487175 := bstep (se 1 (by rfl) ⟨29615381, by rfl⟩ : syracuseStep 39487175 = 59230763) B59230763
theorem B26324783 : Blo 2053435 26324783 := bstep (se 1 (by rfl) ⟨19743587, by rfl⟩ : syracuseStep 26324783 = 39487175) B39487175
theorem B17549855 : Blo 2053435 17549855 := bstep (se 1 (by rfl) ⟨13162391, by rfl⟩ : syracuseStep 17549855 = 26324783) B26324783
theorem B11699903 : Blo 2053435 11699903 := bstep (se 1 (by rfl) ⟨8774927, by rfl⟩ : syracuseStep 11699903 = 17549855) B17549855
theorem B7799935 : Blo 2053435 7799935 := bstep (se 1 (by rfl) ⟨5849951, by rfl⟩ : syracuseStep 7799935 = 11699903) B11699903
theorem B10399913 : Blo 2053435 10399913 := bstep (se 2 (by rfl) ⟨3899967, by rfl⟩ : syracuseStep 10399913 = 7799935) B7799935
theorem B6933275 : Blo 2053435 6933275 := bstep (se 1 (by rfl) ⟨5199956, by rfl⟩ : syracuseStep 6933275 = 10399913) B10399913
theorem B4622183 : Blo 2053435 4622183 := bstep (se 1 (by rfl) ⟨3466637, by rfl⟩ : syracuseStep 4622183 = 6933275) B6933275
theorem B3081455 : Blo 2053435 3081455 := bstep (se 1 (by rfl) ⟨2311091, by rfl⟩ : syracuseStep 3081455 = 4622183) B4622183
theorem B2054303 : Blo 2053435 2054303 := bstep (se 1 (by rfl) ⟨1540727, by rfl⟩ : syracuseStep 2054303 = 3081455) B3081455
theorem B3081461 : Blo 2053435 3081461 := bbase (se 5 (by rfl) ⟨144443, by rfl⟩ : syracuseStep 3081461 = 288887) (by norm_num)
theorem B2054307 : Blo 2053435 2054307 := bstep (se 1 (by rfl) ⟨1540730, by rfl⟩ : syracuseStep 2054307 = 3081461) B3081461
theorem B4935917 : Blo 2053435 4935917 := bbase (se 3 (by rfl) ⟨925484, by rfl⟩ : syracuseStep 4935917 = 1850969) (by norm_num)
theorem B13162445 : Blo 2053435 13162445 := bstep (se 3 (by rfl) ⟨2467958, by rfl⟩ : syracuseStep 13162445 = 4935917) B4935917
theorem B8774963 : Blo 2053435 8774963 := bstep (se 1 (by rfl) ⟨6581222, by rfl⟩ : syracuseStep 8774963 = 13162445) B13162445
theorem B5849975 : Blo 2053435 5849975 := bstep (se 1 (by rfl) ⟨4387481, by rfl⟩ : syracuseStep 5849975 = 8774963) B8774963
theorem B3899983 : Blo 2053435 3899983 := bstep (se 1 (by rfl) ⟨2924987, by rfl⟩ : syracuseStep 3899983 = 5849975) B5849975
theorem B5199977 : Blo 2053435 5199977 := bstep (se 2 (by rfl) ⟨1949991, by rfl⟩ : syracuseStep 5199977 = 3899983) B3899983
theorem B3466651 : Blo 2053435 3466651 := bstep (se 1 (by rfl) ⟨2599988, by rfl⟩ : syracuseStep 3466651 = 5199977) B5199977
theorem B4622201 : Blo 2053435 4622201 := bstep (se 2 (by rfl) ⟨1733325, by rfl⟩ : syracuseStep 4622201 = 3466651) B3466651
theorem B3081467 : Blo 2053435 3081467 := bstep (se 1 (by rfl) ⟨2311100, by rfl⟩ : syracuseStep 3081467 = 4622201) B4622201
theorem B2054311 : Blo 2053435 2054311 := bstep (se 1 (by rfl) ⟨1540733, by rfl⟩ : syracuseStep 2054311 = 3081467) B3081467
theorem B2311105 : Blo 2053435 2311105 := bbase (se 2 (by rfl) ⟨866664, by rfl⟩ : syracuseStep 2311105 = 1733329) (by norm_num)
theorem B3081473 : Blo 2053435 3081473 := bstep (se 2 (by rfl) ⟨1155552, by rfl⟩ : syracuseStep 3081473 = 2311105) B2311105
theorem B2054315 : Blo 2053435 2054315 := bstep (se 1 (by rfl) ⟨1540736, by rfl⟩ : syracuseStep 2054315 = 3081473) B3081473
theorem B5199997 : Blo 2053435 5199997 := bbase (se 3 (by rfl) ⟨974999, by rfl⟩ : syracuseStep 5199997 = 1949999) (by norm_num)
theorem B6933329 : Blo 2053435 6933329 := bstep (se 2 (by rfl) ⟨2599998, by rfl⟩ : syracuseStep 6933329 = 5199997) B5199997
theorem B4622219 : Blo 2053435 4622219 := bstep (se 1 (by rfl) ⟨3466664, by rfl⟩ : syracuseStep 4622219 = 6933329) B6933329
theorem B3081479 : Blo 2053435 3081479 := bstep (se 1 (by rfl) ⟨2311109, by rfl⟩ : syracuseStep 3081479 = 4622219) B4622219
theorem B2054319 : Blo 2053435 2054319 := bstep (se 1 (by rfl) ⟨1540739, by rfl⟩ : syracuseStep 2054319 = 3081479) B3081479
theorem B3081485 : Blo 2053435 3081485 := bbase (se 3 (by rfl) ⟨577778, by rfl⟩ : syracuseStep 3081485 = 1155557) (by norm_num)
theorem B2054323 : Blo 2053435 2054323 := bstep (se 1 (by rfl) ⟨1540742, by rfl⟩ : syracuseStep 2054323 = 3081485) B3081485
theorem B4622237 : Blo 2053435 4622237 := bbase (se 3 (by rfl) ⟨866669, by rfl⟩ : syracuseStep 4622237 = 1733339) (by norm_num)
theorem B3081491 : Blo 2053435 3081491 := bstep (se 1 (by rfl) ⟨2311118, by rfl⟩ : syracuseStep 3081491 = 4622237) B4622237
theorem B2054327 : Blo 2053435 2054327 := bstep (se 1 (by rfl) ⟨1540745, by rfl⟩ : syracuseStep 2054327 = 3081491) B3081491
theorem B3466685 : Blo 2053435 3466685 := bbase (se 3 (by rfl) ⟨650003, by rfl⟩ : syracuseStep 3466685 = 1300007) (by norm_num)
theorem B2311123 : Blo 2053435 2311123 := bstep (se 1 (by rfl) ⟨1733342, by rfl⟩ : syracuseStep 2311123 = 3466685) B3466685
theorem B3081497 : Blo 2053435 3081497 := bstep (se 2 (by rfl) ⟨1155561, by rfl⟩ : syracuseStep 3081497 = 2311123) B2311123
theorem B2054331 : Blo 2053435 2054331 := bstep (se 1 (by rfl) ⟨1540748, by rfl⟩ : syracuseStep 2054331 = 3081497) B3081497
theorem B11700085 : Blo 2053435 11700085 := bbase (se 5 (by rfl) ⟨548441, by rfl⟩ : syracuseStep 11700085 = 1096883) (by norm_num)
theorem B15600113 : Blo 2053435 15600113 := bstep (se 2 (by rfl) ⟨5850042, by rfl⟩ : syracuseStep 15600113 = 11700085) B11700085
theorem B10400075 : Blo 2053435 10400075 := bstep (se 1 (by rfl) ⟨7800056, by rfl⟩ : syracuseStep 10400075 = 15600113) B15600113
theorem B6933383 : Blo 2053435 6933383 := bstep (se 1 (by rfl) ⟨5200037, by rfl⟩ : syracuseStep 6933383 = 10400075) B10400075
theorem B4622255 : Blo 2053435 4622255 := bstep (se 1 (by rfl) ⟨3466691, by rfl⟩ : syracuseStep 4622255 = 6933383) B6933383
theorem B3081503 : Blo 2053435 3081503 := bstep (se 1 (by rfl) ⟨2311127, by rfl⟩ : syracuseStep 3081503 = 4622255) B4622255
theorem B2054335 : Blo 2053435 2054335 := bstep (se 1 (by rfl) ⟨1540751, by rfl⟩ : syracuseStep 2054335 = 3081503) B3081503
theorem B3081509 : Blo 2053435 3081509 := bbase (se 4 (by rfl) ⟨288891, by rfl⟩ : syracuseStep 3081509 = 577783) (by norm_num)
theorem B2054339 : Blo 2053435 2054339 := bstep (se 1 (by rfl) ⟨1540754, by rfl⟩ : syracuseStep 2054339 = 3081509) B3081509
theorem B2600029 : Blo 2053435 2600029 := bbase (se 3 (by rfl) ⟨487505, by rfl⟩ : syracuseStep 2600029 = 975011) (by norm_num)
theorem B3466705 : Blo 2053435 3466705 := bstep (se 2 (by rfl) ⟨1300014, by rfl⟩ : syracuseStep 3466705 = 2600029) B2600029
theorem B4622273 : Blo 2053435 4622273 := bstep (se 2 (by rfl) ⟨1733352, by rfl⟩ : syracuseStep 4622273 = 3466705) B3466705
theorem B3081515 : Blo 2053435 3081515 := bstep (se 1 (by rfl) ⟨2311136, by rfl⟩ : syracuseStep 3081515 = 4622273) B4622273
theorem B2054343 : Blo 2053435 2054343 := bstep (se 1 (by rfl) ⟨1540757, by rfl⟩ : syracuseStep 2054343 = 3081515) B3081515
theorem B2311141 : Blo 2053435 2311141 := bbase (se 4 (by rfl) ⟨216669, by rfl⟩ : syracuseStep 2311141 = 433339) (by norm_num)
theorem B3081521 : Blo 2053435 3081521 := bstep (se 2 (by rfl) ⟨1155570, by rfl⟩ : syracuseStep 3081521 = 2311141) B2311141
theorem B2054347 : Blo 2053435 2054347 := bstep (se 1 (by rfl) ⟨1540760, by rfl⟩ : syracuseStep 2054347 = 3081521) B3081521
theorem B4447429 : Blo 2053435 4447429 := bbase (se 4 (by rfl) ⟨416946, by rfl⟩ : syracuseStep 4447429 = 833893) (by norm_num)
theorem B94878485 : Blo 2053435 94878485 := bstep (se 6 (by rfl) ⟨2223714, by rfl⟩ : syracuseStep 94878485 = 4447429) B4447429
theorem B63252323 : Blo 2053435 63252323 := bstep (se 1 (by rfl) ⟨47439242, by rfl⟩ : syracuseStep 63252323 = 94878485) B94878485
theorem B42168215 : Blo 2053435 42168215 := bstep (se 1 (by rfl) ⟨31626161, by rfl⟩ : syracuseStep 42168215 = 63252323) B63252323
theorem B28112143 : Blo 2053435 28112143 := bstep (se 1 (by rfl) ⟨21084107, by rfl⟩ : syracuseStep 28112143 = 42168215) B42168215
theorem B37482857 : Blo 2053435 37482857 := bstep (se 2 (by rfl) ⟨14056071, by rfl⟩ : syracuseStep 37482857 = 28112143) B28112143
theorem B24988571 : Blo 2053435 24988571 := bstep (se 1 (by rfl) ⟨18741428, by rfl⟩ : syracuseStep 24988571 = 37482857) B37482857
theorem B16659047 : Blo 2053435 16659047 := bstep (se 1 (by rfl) ⟨12494285, by rfl⟩ : syracuseStep 16659047 = 24988571) B24988571
theorem B11106031 : Blo 2053435 11106031 := bstep (se 1 (by rfl) ⟨8329523, by rfl⟩ : syracuseStep 11106031 = 16659047) B16659047
theorem B14808041 : Blo 2053435 14808041 := bstep (se 2 (by rfl) ⟨5553015, by rfl⟩ : syracuseStep 14808041 = 11106031) B11106031
theorem B9872027 : Blo 2053435 9872027 := bstep (se 1 (by rfl) ⟨7404020, by rfl⟩ : syracuseStep 9872027 = 14808041) B14808041
theorem B6581351 : Blo 2053435 6581351 := bstep (se 1 (by rfl) ⟨4936013, by rfl⟩ : syracuseStep 6581351 = 9872027) B9872027
theorem B4387567 : Blo 2053435 4387567 := bstep (se 1 (by rfl) ⟨3290675, by rfl⟩ : syracuseStep 4387567 = 6581351) B6581351
theorem B5850089 : Blo 2053435 5850089 := bstep (se 2 (by rfl) ⟨2193783, by rfl⟩ : syracuseStep 5850089 = 4387567) B4387567
theorem B3900059 : Blo 2053435 3900059 := bstep (se 1 (by rfl) ⟨2925044, by rfl⟩ : syracuseStep 3900059 = 5850089) B5850089
theorem B2600039 : Blo 2053435 2600039 := bstep (se 1 (by rfl) ⟨1950029, by rfl⟩ : syracuseStep 2600039 = 3900059) B3900059
theorem B6933437 : Blo 2053435 6933437 := bstep (se 3 (by rfl) ⟨1300019, by rfl⟩ : syracuseStep 6933437 = 2600039) B2600039
theorem B4622291 : Blo 2053435 4622291 := bstep (se 1 (by rfl) ⟨3466718, by rfl⟩ : syracuseStep 4622291 = 6933437) B6933437
theorem B3081527 : Blo 2053435 3081527 := bstep (se 1 (by rfl) ⟨2311145, by rfl⟩ : syracuseStep 3081527 = 4622291) B4622291
theorem B2054351 : Blo 2053435 2054351 := bstep (se 1 (by rfl) ⟨1540763, by rfl⟩ : syracuseStep 2054351 = 3081527) B3081527
theorem B3081533 : Blo 2053435 3081533 := bbase (se 3 (by rfl) ⟨577787, by rfl⟩ : syracuseStep 3081533 = 1155575) (by norm_num)
theorem B2054355 : Blo 2053435 2054355 := bstep (se 1 (by rfl) ⟨1540766, by rfl⟩ : syracuseStep 2054355 = 3081533) B3081533
theorem B4622309 : Blo 2053435 4622309 := bbase (se 4 (by rfl) ⟨433341, by rfl⟩ : syracuseStep 4622309 = 866683) (by norm_num)
theorem B3081539 : Blo 2053435 3081539 := bstep (se 1 (by rfl) ⟨2311154, by rfl⟩ : syracuseStep 3081539 = 4622309) B4622309
theorem B2054359 : Blo 2053435 2054359 := bstep (se 1 (by rfl) ⟨1540769, by rfl⟩ : syracuseStep 2054359 = 3081539) B3081539
theorem B5200109 : Blo 2053435 5200109 := bbase (se 3 (by rfl) ⟨975020, by rfl⟩ : syracuseStep 5200109 = 1950041) (by norm_num)
theorem B3466739 : Blo 2053435 3466739 := bstep (se 1 (by rfl) ⟨2600054, by rfl⟩ : syracuseStep 3466739 = 5200109) B5200109
theorem B2311159 : Blo 2053435 2311159 := bstep (se 1 (by rfl) ⟨1733369, by rfl⟩ : syracuseStep 2311159 = 3466739) B3466739
theorem B3081545 : Blo 2053435 3081545 := bstep (se 2 (by rfl) ⟨1155579, by rfl⟩ : syracuseStep 3081545 = 2311159) B2311159
theorem B2054363 : Blo 2053435 2054363 := bstep (se 1 (by rfl) ⟨1540772, by rfl⟩ : syracuseStep 2054363 = 3081545) B3081545
theorem B3290701 : Blo 2053435 3290701 := bbase (se 3 (by rfl) ⟨617006, by rfl⟩ : syracuseStep 3290701 = 1234013) (by norm_num)
theorem B4387601 : Blo 2053435 4387601 := bstep (se 2 (by rfl) ⟨1645350, by rfl⟩ : syracuseStep 4387601 = 3290701) B3290701
theorem B2925067 : Blo 2053435 2925067 := bstep (se 1 (by rfl) ⟨2193800, by rfl⟩ : syracuseStep 2925067 = 4387601) B4387601
theorem B3900089 : Blo 2053435 3900089 := bstep (se 2 (by rfl) ⟨1462533, by rfl⟩ : syracuseStep 3900089 = 2925067) B2925067
theorem B10400237 : Blo 2053435 10400237 := bstep (se 3 (by rfl) ⟨1950044, by rfl⟩ : syracuseStep 10400237 = 3900089) B3900089
theorem B6933491 : Blo 2053435 6933491 := bstep (se 1 (by rfl) ⟨5200118, by rfl⟩ : syracuseStep 6933491 = 10400237) B10400237
theorem B4622327 : Blo 2053435 4622327 := bstep (se 1 (by rfl) ⟨3466745, by rfl⟩ : syracuseStep 4622327 = 6933491) B6933491
theorem B3081551 : Blo 2053435 3081551 := bstep (se 1 (by rfl) ⟨2311163, by rfl⟩ : syracuseStep 3081551 = 4622327) B4622327
theorem B2054367 : Blo 2053435 2054367 := bstep (se 1 (by rfl) ⟨1540775, by rfl⟩ : syracuseStep 2054367 = 3081551) B3081551
theorem B3081557 : Blo 2053435 3081557 := bbase (se 12 (by rfl) ⟨1128, by rfl⟩ : syracuseStep 3081557 = 2257) (by norm_num)
theorem B2054371 : Blo 2053435 2054371 := bstep (se 1 (by rfl) ⟨1540778, by rfl⟩ : syracuseStep 2054371 = 3081557) B3081557
theorem B2193809 : Blo 2053435 2193809 := bbase (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) (by norm_num)
theorem B5850157 : Blo 2053435 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B7800209 : Blo 2053435 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B5200139 : Blo 2053435 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B3466759 : Blo 2053435 3466759 := bstep (se 1 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 3466759 = 5200139) B5200139
theorem B4622345 : Blo 2053435 4622345 := bstep (se 2 (by rfl) ⟨1733379, by rfl⟩ : syracuseStep 4622345 = 3466759) B3466759
theorem B3081563 : Blo 2053435 3081563 := bstep (se 1 (by rfl) ⟨2311172, by rfl⟩ : syracuseStep 3081563 = 4622345) B4622345
theorem B2054375 : Blo 2053435 2054375 := bstep (se 1 (by rfl) ⟨1540781, by rfl⟩ : syracuseStep 2054375 = 3081563) B3081563
theorem B2311177 : Blo 2053435 2311177 := bbase (se 2 (by rfl) ⟨866691, by rfl⟩ : syracuseStep 2311177 = 1733383) (by norm_num)
theorem B3081569 : Blo 2053435 3081569 := bstep (se 2 (by rfl) ⟨1155588, by rfl⟩ : syracuseStep 3081569 = 2311177) B2311177
theorem B2054379 : Blo 2053435 2054379 := bstep (se 1 (by rfl) ⟨1540784, by rfl⟩ : syracuseStep 2054379 = 3081569) B3081569
theorem B2082413 : Blo 2053435 2082413 := bbase (se 3 (by rfl) ⟨390452, by rfl⟩ : syracuseStep 2082413 = 780905) (by norm_num)
theorem B5553101 : Blo 2053435 5553101 := bstep (se 3 (by rfl) ⟨1041206, by rfl⟩ : syracuseStep 5553101 = 2082413) B2082413
theorem B3702067 : Blo 2053435 3702067 := bstep (se 1 (by rfl) ⟨2776550, by rfl⟩ : syracuseStep 3702067 = 5553101) B5553101
theorem B19744357 : Blo 2053435 19744357 := bstep (se 4 (by rfl) ⟨1851033, by rfl⟩ : syracuseStep 19744357 = 3702067) B3702067
theorem B26325809 : Blo 2053435 26325809 := bstep (se 2 (by rfl) ⟨9872178, by rfl⟩ : syracuseStep 26325809 = 19744357) B19744357
theorem B17550539 : Blo 2053435 17550539 := bstep (se 1 (by rfl) ⟨13162904, by rfl⟩ : syracuseStep 17550539 = 26325809) B26325809
theorem B11700359 : Blo 2053435 11700359 := bstep (se 1 (by rfl) ⟨8775269, by rfl⟩ : syracuseStep 11700359 = 17550539) B17550539
theorem B7800239 : Blo 2053435 7800239 := bstep (se 1 (by rfl) ⟨5850179, by rfl⟩ : syracuseStep 7800239 = 11700359) B11700359
theorem B5200159 : Blo 2053435 5200159 := bstep (se 1 (by rfl) ⟨3900119, by rfl⟩ : syracuseStep 5200159 = 7800239) B7800239
theorem B6933545 : Blo 2053435 6933545 := bstep (se 2 (by rfl) ⟨2600079, by rfl⟩ : syracuseStep 6933545 = 5200159) B5200159
theorem B4622363 : Blo 2053435 4622363 := bstep (se 1 (by rfl) ⟨3466772, by rfl⟩ : syracuseStep 4622363 = 6933545) B6933545
theorem B3081575 : Blo 2053435 3081575 := bstep (se 1 (by rfl) ⟨2311181, by rfl⟩ : syracuseStep 3081575 = 4622363) B4622363
theorem B2054383 : Blo 2053435 2054383 := bstep (se 1 (by rfl) ⟨1540787, by rfl⟩ : syracuseStep 2054383 = 3081575) B3081575
theorem B3081581 : Blo 2053435 3081581 := bbase (se 3 (by rfl) ⟨577796, by rfl⟩ : syracuseStep 3081581 = 1155593) (by norm_num)
theorem B2054387 : Blo 2053435 2054387 := bstep (se 1 (by rfl) ⟨1540790, by rfl⟩ : syracuseStep 2054387 = 3081581) B3081581
theorem B4622381 : Blo 2053435 4622381 := bbase (se 3 (by rfl) ⟨866696, by rfl⟩ : syracuseStep 4622381 = 1733393) (by norm_num)
theorem B3081587 : Blo 2053435 3081587 := bstep (se 1 (by rfl) ⟨2311190, by rfl⟩ : syracuseStep 3081587 = 4622381) B4622381
theorem B2054391 : Blo 2053435 2054391 := bstep (se 1 (by rfl) ⟨1540793, by rfl⟩ : syracuseStep 2054391 = 3081587) B3081587
theorem B14056373 : Blo 2053435 14056373 := bbase (se 5 (by rfl) ⟨658892, by rfl⟩ : syracuseStep 14056373 = 1317785) (by norm_num)
theorem B37483661 : Blo 2053435 37483661 := bstep (se 3 (by rfl) ⟨7028186, by rfl⟩ : syracuseStep 37483661 = 14056373) B14056373
theorem B24989107 : Blo 2053435 24989107 := bstep (se 1 (by rfl) ⟨18741830, by rfl⟩ : syracuseStep 24989107 = 37483661) B37483661
theorem B33318809 : Blo 2053435 33318809 := bstep (se 2 (by rfl) ⟨12494553, by rfl⟩ : syracuseStep 33318809 = 24989107) B24989107
theorem B22212539 : Blo 2053435 22212539 := bstep (se 1 (by rfl) ⟨16659404, by rfl⟩ : syracuseStep 22212539 = 33318809) B33318809
theorem B14808359 : Blo 2053435 14808359 := bstep (se 1 (by rfl) ⟨11106269, by rfl⟩ : syracuseStep 14808359 = 22212539) B22212539
theorem B9872239 : Blo 2053435 9872239 := bstep (se 1 (by rfl) ⟨7404179, by rfl⟩ : syracuseStep 9872239 = 14808359) B14808359
theorem B13162985 : Blo 2053435 13162985 := bstep (se 2 (by rfl) ⟨4936119, by rfl⟩ : syracuseStep 13162985 = 9872239) B9872239
theorem B8775323 : Blo 2053435 8775323 := bstep (se 1 (by rfl) ⟨6581492, by rfl⟩ : syracuseStep 8775323 = 13162985) B13162985
theorem B5850215 : Blo 2053435 5850215 := bstep (se 1 (by rfl) ⟨4387661, by rfl⟩ : syracuseStep 5850215 = 8775323) B8775323
theorem B3900143 : Blo 2053435 3900143 := bstep (se 1 (by rfl) ⟨2925107, by rfl⟩ : syracuseStep 3900143 = 5850215) B5850215
theorem B2600095 : Blo 2053435 2600095 := bstep (se 1 (by rfl) ⟨1950071, by rfl⟩ : syracuseStep 2600095 = 3900143) B3900143
theorem B3466793 : Blo 2053435 3466793 := bstep (se 2 (by rfl) ⟨1300047, by rfl⟩ : syracuseStep 3466793 = 2600095) B2600095
theorem B2311195 : Blo 2053435 2311195 := bstep (se 1 (by rfl) ⟨1733396, by rfl⟩ : syracuseStep 2311195 = 3466793) B3466793
theorem B3081593 : Blo 2053435 3081593 := bstep (se 2 (by rfl) ⟨1155597, by rfl⟩ : syracuseStep 3081593 = 2311195) B2311195
theorem B2054395 : Blo 2053435 2054395 := bstep (se 1 (by rfl) ⟨1540796, by rfl⟩ : syracuseStep 2054395 = 3081593) B3081593
theorem B2965021 : Blo 2053435 2965021 := bbase (se 3 (by rfl) ⟨555941, by rfl⟩ : syracuseStep 2965021 = 1111883) (by norm_num)
theorem B63253781 : Blo 2053435 63253781 := bstep (se 6 (by rfl) ⟨1482510, by rfl⟩ : syracuseStep 63253781 = 2965021) B2965021
theorem B42169187 : Blo 2053435 42169187 := bstep (se 1 (by rfl) ⟨31626890, by rfl⟩ : syracuseStep 42169187 = 63253781) B63253781
theorem B112451165 : Blo 2053435 112451165 := bstep (se 3 (by rfl) ⟨21084593, by rfl⟩ : syracuseStep 112451165 = 42169187) B42169187
theorem B74967443 : Blo 2053435 74967443 := bstep (se 1 (by rfl) ⟨56225582, by rfl⟩ : syracuseStep 74967443 = 112451165) B112451165
theorem B49978295 : Blo 2053435 49978295 := bstep (se 1 (by rfl) ⟨37483721, by rfl⟩ : syracuseStep 49978295 = 74967443) B74967443
theorem B33318863 : Blo 2053435 33318863 := bstep (se 1 (by rfl) ⟨24989147, by rfl⟩ : syracuseStep 33318863 = 49978295) B49978295
theorem B22212575 : Blo 2053435 22212575 := bstep (se 1 (by rfl) ⟨16659431, by rfl⟩ : syracuseStep 22212575 = 33318863) B33318863
theorem B14808383 : Blo 2053435 14808383 := bstep (se 1 (by rfl) ⟨11106287, by rfl⟩ : syracuseStep 14808383 = 22212575) B22212575
theorem B9872255 : Blo 2053435 9872255 := bstep (se 1 (by rfl) ⟨7404191, by rfl⟩ : syracuseStep 9872255 = 14808383) B14808383
theorem B6581503 : Blo 2053435 6581503 := bstep (se 1 (by rfl) ⟨4936127, by rfl⟩ : syracuseStep 6581503 = 9872255) B9872255
theorem B35101349 : Blo 2053435 35101349 := bstep (se 4 (by rfl) ⟨3290751, by rfl⟩ : syracuseStep 35101349 = 6581503) B6581503
theorem B23400899 : Blo 2053435 23400899 := bstep (se 1 (by rfl) ⟨17550674, by rfl⟩ : syracuseStep 23400899 = 35101349) B35101349
theorem B15600599 : Blo 2053435 15600599 := bstep (se 1 (by rfl) ⟨11700449, by rfl⟩ : syracuseStep 15600599 = 23400899) B23400899
theorem B10400399 : Blo 2053435 10400399 := bstep (se 1 (by rfl) ⟨7800299, by rfl⟩ : syracuseStep 10400399 = 15600599) B15600599
theorem B6933599 : Blo 2053435 6933599 := bstep (se 1 (by rfl) ⟨5200199, by rfl⟩ : syracuseStep 6933599 = 10400399) B10400399
theorem B4622399 : Blo 2053435 4622399 := bstep (se 1 (by rfl) ⟨3466799, by rfl⟩ : syracuseStep 4622399 = 6933599) B6933599
theorem B3081599 : Blo 2053435 3081599 := bstep (se 1 (by rfl) ⟨2311199, by rfl⟩ : syracuseStep 3081599 = 4622399) B4622399
theorem B2054399 : Blo 2053435 2054399 := bstep (se 1 (by rfl) ⟨1540799, by rfl⟩ : syracuseStep 2054399 = 3081599) B3081599
theorem B3081605 : Blo 2053435 3081605 := bbase (se 4 (by rfl) ⟨288900, by rfl⟩ : syracuseStep 3081605 = 577801) (by norm_num)
theorem B2054403 : Blo 2053435 2054403 := bstep (se 1 (by rfl) ⟨1540802, by rfl⟩ : syracuseStep 2054403 = 3081605) B3081605
theorem B3466813 : Blo 2053435 3466813 := bbase (se 3 (by rfl) ⟨650027, by rfl⟩ : syracuseStep 3466813 = 1300055) (by norm_num)
theorem B4622417 : Blo 2053435 4622417 := bstep (se 2 (by rfl) ⟨1733406, by rfl⟩ : syracuseStep 4622417 = 3466813) B3466813
theorem B3081611 : Blo 2053435 3081611 := bstep (se 1 (by rfl) ⟨2311208, by rfl⟩ : syracuseStep 3081611 = 4622417) B4622417
theorem B2054407 : Blo 2053435 2054407 := bstep (se 1 (by rfl) ⟨1540805, by rfl⟩ : syracuseStep 2054407 = 3081611) B3081611
theorem B2311213 : Blo 2053435 2311213 := bbase (se 3 (by rfl) ⟨433352, by rfl⟩ : syracuseStep 2311213 = 866705) (by norm_num)
theorem B3081617 : Blo 2053435 3081617 := bstep (se 2 (by rfl) ⟨1155606, by rfl⟩ : syracuseStep 3081617 = 2311213) B2311213
theorem B2054411 : Blo 2053435 2054411 := bstep (se 1 (by rfl) ⟨1540808, by rfl⟩ : syracuseStep 2054411 = 3081617) B3081617
theorem B6933653 : Blo 2053435 6933653 := bbase (se 6 (by rfl) ⟨162507, by rfl⟩ : syracuseStep 6933653 = 325015) (by norm_num)
theorem B4622435 : Blo 2053435 4622435 := bstep (se 1 (by rfl) ⟨3466826, by rfl⟩ : syracuseStep 4622435 = 6933653) B6933653
theorem B3081623 : Blo 2053435 3081623 := bstep (se 1 (by rfl) ⟨2311217, by rfl⟩ : syracuseStep 3081623 = 4622435) B4622435
theorem B2054415 : Blo 2053435 2054415 := bstep (se 1 (by rfl) ⟨1540811, by rfl⟩ : syracuseStep 2054415 = 3081623) B3081623
theorem B3081629 : Blo 2053435 3081629 := bbase (se 3 (by rfl) ⟨577805, by rfl⟩ : syracuseStep 3081629 = 1155611) (by norm_num)
theorem B2054419 : Blo 2053435 2054419 := bstep (se 1 (by rfl) ⟨1540814, by rfl⟩ : syracuseStep 2054419 = 3081629) B3081629
theorem B4622453 : Blo 2053435 4622453 := bbase (se 5 (by rfl) ⟨216677, by rfl⟩ : syracuseStep 4622453 = 433355) (by norm_num)
theorem B3081635 : Blo 2053435 3081635 := bstep (se 1 (by rfl) ⟨2311226, by rfl⟩ : syracuseStep 3081635 = 4622453) B4622453
theorem B2054423 : Blo 2053435 2054423 := bstep (se 1 (by rfl) ⟨1540817, by rfl⟩ : syracuseStep 2054423 = 3081635) B3081635
theorem B3290797 : Blo 2053435 3290797 := bbase (se 3 (by rfl) ⟨617024, by rfl⟩ : syracuseStep 3290797 = 1234049) (by norm_num)
theorem B17550917 : Blo 2053435 17550917 := bstep (se 4 (by rfl) ⟨1645398, by rfl⟩ : syracuseStep 17550917 = 3290797) B3290797
theorem B11700611 : Blo 2053435 11700611 := bstep (se 1 (by rfl) ⟨8775458, by rfl⟩ : syracuseStep 11700611 = 17550917) B17550917
theorem B7800407 : Blo 2053435 7800407 := bstep (se 1 (by rfl) ⟨5850305, by rfl⟩ : syracuseStep 7800407 = 11700611) B11700611
theorem B5200271 : Blo 2053435 5200271 := bstep (se 1 (by rfl) ⟨3900203, by rfl⟩ : syracuseStep 5200271 = 7800407) B7800407
theorem B3466847 : Blo 2053435 3466847 := bstep (se 1 (by rfl) ⟨2600135, by rfl⟩ : syracuseStep 3466847 = 5200271) B5200271
theorem B2311231 : Blo 2053435 2311231 := bstep (se 1 (by rfl) ⟨1733423, by rfl⟩ : syracuseStep 2311231 = 3466847) B3466847
theorem B3081641 : Blo 2053435 3081641 := bstep (se 2 (by rfl) ⟨1155615, by rfl⟩ : syracuseStep 3081641 = 2311231) B2311231
theorem B2054427 : Blo 2053435 2054427 := bstep (se 1 (by rfl) ⟨1540820, by rfl⟩ : syracuseStep 2054427 = 3081641) B3081641
theorem B7800421 : Blo 2053435 7800421 := bbase (se 4 (by rfl) ⟨731289, by rfl⟩ : syracuseStep 7800421 = 1462579) (by norm_num)
theorem B10400561 : Blo 2053435 10400561 := bstep (se 2 (by rfl) ⟨3900210, by rfl⟩ : syracuseStep 10400561 = 7800421) B7800421
theorem B6933707 : Blo 2053435 6933707 := bstep (se 1 (by rfl) ⟨5200280, by rfl⟩ : syracuseStep 6933707 = 10400561) B10400561
theorem B4622471 : Blo 2053435 4622471 := bstep (se 1 (by rfl) ⟨3466853, by rfl⟩ : syracuseStep 4622471 = 6933707) B6933707
theorem B3081647 : Blo 2053435 3081647 := bstep (se 1 (by rfl) ⟨2311235, by rfl⟩ : syracuseStep 3081647 = 4622471) B4622471
theorem B2054431 : Blo 2053435 2054431 := bstep (se 1 (by rfl) ⟨1540823, by rfl⟩ : syracuseStep 2054431 = 3081647) B3081647
theorem B3081653 : Blo 2053435 3081653 := bbase (se 5 (by rfl) ⟨144452, by rfl⟩ : syracuseStep 3081653 = 288905) (by norm_num)
theorem B2054435 : Blo 2053435 2054435 := bstep (se 1 (by rfl) ⟨1540826, by rfl⟩ : syracuseStep 2054435 = 3081653) B3081653
theorem B5200301 : Blo 2053435 5200301 := bbase (se 3 (by rfl) ⟨975056, by rfl⟩ : syracuseStep 5200301 = 1950113) (by norm_num)
theorem B3466867 : Blo 2053435 3466867 := bstep (se 1 (by rfl) ⟨2600150, by rfl⟩ : syracuseStep 3466867 = 5200301) B5200301
theorem B4622489 : Blo 2053435 4622489 := bstep (se 2 (by rfl) ⟨1733433, by rfl⟩ : syracuseStep 4622489 = 3466867) B3466867
theorem B3081659 : Blo 2053435 3081659 := bstep (se 1 (by rfl) ⟨2311244, by rfl⟩ : syracuseStep 3081659 = 4622489) B4622489
theorem B2054439 : Blo 2053435 2054439 := bstep (se 1 (by rfl) ⟨1540829, by rfl⟩ : syracuseStep 2054439 = 3081659) B3081659
theorem B2311249 : Blo 2053435 2311249 := bbase (se 2 (by rfl) ⟨866718, by rfl⟩ : syracuseStep 2311249 = 1733437) (by norm_num)
theorem B3081665 : Blo 2053435 3081665 := bstep (se 2 (by rfl) ⟨1155624, by rfl⟩ : syracuseStep 3081665 = 2311249) B2311249
theorem B2054443 : Blo 2053435 2054443 := bstep (se 1 (by rfl) ⟨1540832, by rfl⟩ : syracuseStep 2054443 = 3081665) B3081665
theorem B2925181 : Blo 2053435 2925181 := bbase (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) (by norm_num)
theorem B3900241 : Blo 2053435 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B5200321 : Blo 2053435 5200321 := bstep (se 2 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 5200321 = 3900241) B3900241
theorem B6933761 : Blo 2053435 6933761 := bstep (se 2 (by rfl) ⟨2600160, by rfl⟩ : syracuseStep 6933761 = 5200321) B5200321
theorem B4622507 : Blo 2053435 4622507 := bstep (se 1 (by rfl) ⟨3466880, by rfl⟩ : syracuseStep 4622507 = 6933761) B6933761
theorem B3081671 : Blo 2053435 3081671 := bstep (se 1 (by rfl) ⟨2311253, by rfl⟩ : syracuseStep 3081671 = 4622507) B4622507
theorem B2054447 : Blo 2053435 2054447 := bstep (se 1 (by rfl) ⟨1540835, by rfl⟩ : syracuseStep 2054447 = 3081671) B3081671
theorem B3081677 : Blo 2053435 3081677 := bbase (se 3 (by rfl) ⟨577814, by rfl⟩ : syracuseStep 3081677 = 1155629) (by norm_num)
theorem B2054451 : Blo 2053435 2054451 := bstep (se 1 (by rfl) ⟨1540838, by rfl⟩ : syracuseStep 2054451 = 3081677) B3081677
theorem B4622525 : Blo 2053435 4622525 := bbase (se 3 (by rfl) ⟨866723, by rfl⟩ : syracuseStep 4622525 = 1733447) (by norm_num)
theorem B3081683 : Blo 2053435 3081683 := bstep (se 1 (by rfl) ⟨2311262, by rfl⟩ : syracuseStep 3081683 = 4622525) B4622525
theorem B2054455 : Blo 2053435 2054455 := bstep (se 1 (by rfl) ⟨1540841, by rfl⟩ : syracuseStep 2054455 = 3081683) B3081683
theorem B3466901 : Blo 2053435 3466901 := bbase (se 6 (by rfl) ⟨81255, by rfl⟩ : syracuseStep 3466901 = 162511) (by norm_num)
theorem B2311267 : Blo 2053435 2311267 := bstep (se 1 (by rfl) ⟨1733450, by rfl⟩ : syracuseStep 2311267 = 3466901) B3466901
theorem B3081689 : Blo 2053435 3081689 := bstep (se 2 (by rfl) ⟨1155633, by rfl⟩ : syracuseStep 3081689 = 2311267) B2311267
theorem B2054459 : Blo 2053435 2054459 := bstep (se 1 (by rfl) ⟨1540844, by rfl⟩ : syracuseStep 2054459 = 3081689) B3081689
theorem B5553317 : Blo 2053435 5553317 := bbase (se 4 (by rfl) ⟨520623, by rfl⟩ : syracuseStep 5553317 = 1041247) (by norm_num)
theorem B14808845 : Blo 2053435 14808845 := bstep (se 3 (by rfl) ⟨2776658, by rfl⟩ : syracuseStep 14808845 = 5553317) B5553317
theorem B9872563 : Blo 2053435 9872563 := bstep (se 1 (by rfl) ⟨7404422, by rfl⟩ : syracuseStep 9872563 = 14808845) B14808845
theorem B13163417 : Blo 2053435 13163417 := bstep (se 2 (by rfl) ⟨4936281, by rfl⟩ : syracuseStep 13163417 = 9872563) B9872563
theorem B8775611 : Blo 2053435 8775611 := bstep (se 1 (by rfl) ⟨6581708, by rfl⟩ : syracuseStep 8775611 = 13163417) B13163417
theorem B5850407 : Blo 2053435 5850407 := bstep (se 1 (by rfl) ⟨4387805, by rfl⟩ : syracuseStep 5850407 = 8775611) B8775611
theorem B15601085 : Blo 2053435 15601085 := bstep (se 3 (by rfl) ⟨2925203, by rfl⟩ : syracuseStep 15601085 = 5850407) B5850407
theorem B10400723 : Blo 2053435 10400723 := bstep (se 1 (by rfl) ⟨7800542, by rfl⟩ : syracuseStep 10400723 = 15601085) B15601085
theorem B6933815 : Blo 2053435 6933815 := bstep (se 1 (by rfl) ⟨5200361, by rfl⟩ : syracuseStep 6933815 = 10400723) B10400723
theorem B4622543 : Blo 2053435 4622543 := bstep (se 1 (by rfl) ⟨3466907, by rfl⟩ : syracuseStep 4622543 = 6933815) B6933815
theorem B3081695 : Blo 2053435 3081695 := bstep (se 1 (by rfl) ⟨2311271, by rfl⟩ : syracuseStep 3081695 = 4622543) B4622543
theorem B2054463 : Blo 2053435 2054463 := bstep (se 1 (by rfl) ⟨1540847, by rfl⟩ : syracuseStep 2054463 = 3081695) B3081695
theorem B3081701 : Blo 2053435 3081701 := bbase (se 4 (by rfl) ⟨288909, by rfl⟩ : syracuseStep 3081701 = 577819) (by norm_num)
theorem B2054467 : Blo 2053435 2054467 := bstep (se 1 (by rfl) ⟨1540850, by rfl⟩ : syracuseStep 2054467 = 3081701) B3081701
theorem B7505477 : Blo 2053435 7505477 := bbase (se 4 (by rfl) ⟨703638, by rfl⟩ : syracuseStep 7505477 = 1407277) (by norm_num)
theorem B5003651 : Blo 2053435 5003651 := bstep (se 1 (by rfl) ⟨3752738, by rfl⟩ : syracuseStep 5003651 = 7505477) B7505477
theorem B13343069 : Blo 2053435 13343069 := bstep (se 3 (by rfl) ⟨2501825, by rfl⟩ : syracuseStep 13343069 = 5003651) B5003651
theorem B8895379 : Blo 2053435 8895379 := bstep (se 1 (by rfl) ⟨6671534, by rfl⟩ : syracuseStep 8895379 = 13343069) B13343069
theorem B11860505 : Blo 2053435 11860505 := bstep (se 2 (by rfl) ⟨4447689, by rfl⟩ : syracuseStep 11860505 = 8895379) B8895379
theorem B7907003 : Blo 2053435 7907003 := bstep (se 1 (by rfl) ⟨5930252, by rfl⟩ : syracuseStep 7907003 = 11860505) B11860505
theorem B5271335 : Blo 2053435 5271335 := bstep (se 1 (by rfl) ⟨3953501, by rfl⟩ : syracuseStep 5271335 = 7907003) B7907003
theorem B3514223 : Blo 2053435 3514223 := bstep (se 1 (by rfl) ⟨2635667, by rfl⟩ : syracuseStep 3514223 = 5271335) B5271335
theorem B9371261 : Blo 2053435 9371261 := bstep (se 3 (by rfl) ⟨1757111, by rfl⟩ : syracuseStep 9371261 = 3514223) B3514223
theorem B24990029 : Blo 2053435 24990029 := bstep (se 3 (by rfl) ⟨4685630, by rfl⟩ : syracuseStep 24990029 = 9371261) B9371261
theorem B16660019 : Blo 2053435 16660019 := bstep (se 1 (by rfl) ⟨12495014, by rfl⟩ : syracuseStep 16660019 = 24990029) B24990029
theorem B44426717 : Blo 2053435 44426717 := bstep (se 3 (by rfl) ⟨8330009, by rfl⟩ : syracuseStep 44426717 = 16660019) B16660019
theorem B29617811 : Blo 2053435 29617811 := bstep (se 1 (by rfl) ⟨22213358, by rfl⟩ : syracuseStep 29617811 = 44426717) B44426717
theorem B19745207 : Blo 2053435 19745207 := bstep (se 1 (by rfl) ⟨14808905, by rfl⟩ : syracuseStep 19745207 = 29617811) B29617811
theorem B13163471 : Blo 2053435 13163471 := bstep (se 1 (by rfl) ⟨9872603, by rfl⟩ : syracuseStep 13163471 = 19745207) B19745207
theorem B8775647 : Blo 2053435 8775647 := bstep (se 1 (by rfl) ⟨6581735, by rfl⟩ : syracuseStep 8775647 = 13163471) B13163471
theorem B5850431 : Blo 2053435 5850431 := bstep (se 1 (by rfl) ⟨4387823, by rfl⟩ : syracuseStep 5850431 = 8775647) B8775647
theorem B3900287 : Blo 2053435 3900287 := bstep (se 1 (by rfl) ⟨2925215, by rfl⟩ : syracuseStep 3900287 = 5850431) B5850431
theorem B2600191 : Blo 2053435 2600191 := bstep (se 1 (by rfl) ⟨1950143, by rfl⟩ : syracuseStep 2600191 = 3900287) B3900287
theorem B3466921 : Blo 2053435 3466921 := bstep (se 2 (by rfl) ⟨1300095, by rfl⟩ : syracuseStep 3466921 = 2600191) B2600191
theorem B4622561 : Blo 2053435 4622561 := bstep (se 2 (by rfl) ⟨1733460, by rfl⟩ : syracuseStep 4622561 = 3466921) B3466921
theorem B3081707 : Blo 2053435 3081707 := bstep (se 1 (by rfl) ⟨2311280, by rfl⟩ : syracuseStep 3081707 = 4622561) B4622561
theorem B2054471 : Blo 2053435 2054471 := bstep (se 1 (by rfl) ⟨1540853, by rfl⟩ : syracuseStep 2054471 = 3081707) B3081707
theorem B2311285 : Blo 2053435 2311285 := bbase (se 5 (by rfl) ⟨108341, by rfl⟩ : syracuseStep 2311285 = 216683) (by norm_num)
theorem B3081713 : Blo 2053435 3081713 := bstep (se 2 (by rfl) ⟨1155642, by rfl⟩ : syracuseStep 3081713 = 2311285) B2311285
theorem B2054475 : Blo 2053435 2054475 := bstep (se 1 (by rfl) ⟨1540856, by rfl⟩ : syracuseStep 2054475 = 3081713) B3081713
theorem B2600201 : Blo 2053435 2600201 := bbase (se 2 (by rfl) ⟨975075, by rfl⟩ : syracuseStep 2600201 = 1950151) (by norm_num)
theorem B6933869 : Blo 2053435 6933869 := bstep (se 3 (by rfl) ⟨1300100, by rfl⟩ : syracuseStep 6933869 = 2600201) B2600201
theorem B4622579 : Blo 2053435 4622579 := bstep (se 1 (by rfl) ⟨3466934, by rfl⟩ : syracuseStep 4622579 = 6933869) B6933869
theorem B3081719 : Blo 2053435 3081719 := bstep (se 1 (by rfl) ⟨2311289, by rfl⟩ : syracuseStep 3081719 = 4622579) B4622579
theorem B2054479 : Blo 2053435 2054479 := bstep (se 1 (by rfl) ⟨1540859, by rfl⟩ : syracuseStep 2054479 = 3081719) B3081719
theorem B3081725 : Blo 2053435 3081725 := bbase (se 3 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 3081725 = 1155647) (by norm_num)
theorem B2054483 : Blo 2053435 2054483 := bstep (se 1 (by rfl) ⟨1540862, by rfl⟩ : syracuseStep 2054483 = 3081725) B3081725
theorem B4622597 : Blo 2053435 4622597 := bbase (se 4 (by rfl) ⟨433368, by rfl⟩ : syracuseStep 4622597 = 866737) (by norm_num)
theorem B3081731 : Blo 2053435 3081731 := bstep (se 1 (by rfl) ⟨2311298, by rfl⟩ : syracuseStep 3081731 = 4622597) B4622597
theorem B2054487 : Blo 2053435 2054487 := bstep (se 1 (by rfl) ⟨1540865, by rfl⟩ : syracuseStep 2054487 = 3081731) B3081731
theorem B3900325 : Blo 2053435 3900325 := bbase (se 4 (by rfl) ⟨365655, by rfl⟩ : syracuseStep 3900325 = 731311) (by norm_num)
theorem B5200433 : Blo 2053435 5200433 := bstep (se 2 (by rfl) ⟨1950162, by rfl⟩ : syracuseStep 5200433 = 3900325) B3900325
theorem B3466955 : Blo 2053435 3466955 := bstep (se 1 (by rfl) ⟨2600216, by rfl⟩ : syracuseStep 3466955 = 5200433) B5200433
theorem B2311303 : Blo 2053435 2311303 := bstep (se 1 (by rfl) ⟨1733477, by rfl⟩ : syracuseStep 2311303 = 3466955) B3466955
theorem B3081737 : Blo 2053435 3081737 := bstep (se 2 (by rfl) ⟨1155651, by rfl⟩ : syracuseStep 3081737 = 2311303) B2311303
theorem B2054491 : Blo 2053435 2054491 := bstep (se 1 (by rfl) ⟨1540868, by rfl⟩ : syracuseStep 2054491 = 3081737) B3081737
theorem B10400885 : Blo 2053435 10400885 := bbase (se 5 (by rfl) ⟨487541, by rfl⟩ : syracuseStep 10400885 = 975083) (by norm_num)
theorem B6933923 : Blo 2053435 6933923 := bstep (se 1 (by rfl) ⟨5200442, by rfl⟩ : syracuseStep 6933923 = 10400885) B10400885
theorem B4622615 : Blo 2053435 4622615 := bstep (se 1 (by rfl) ⟨3466961, by rfl⟩ : syracuseStep 4622615 = 6933923) B6933923
theorem B3081743 : Blo 2053435 3081743 := bstep (se 1 (by rfl) ⟨2311307, by rfl⟩ : syracuseStep 3081743 = 4622615) B4622615
theorem B2054495 : Blo 2053435 2054495 := bstep (se 1 (by rfl) ⟨1540871, by rfl⟩ : syracuseStep 2054495 = 3081743) B3081743
theorem B3081749 : Blo 2053435 3081749 := bbase (se 6 (by rfl) ⟨72228, by rfl⟩ : syracuseStep 3081749 = 144457) (by norm_num)
theorem B2054499 : Blo 2053435 2054499 := bstep (se 1 (by rfl) ⟨1540874, by rfl⟩ : syracuseStep 2054499 = 3081749) B3081749
theorem B2468189 : Blo 2053435 2468189 := bbase (se 3 (by rfl) ⟨462785, by rfl⟩ : syracuseStep 2468189 = 925571) (by norm_num)
theorem B6581837 : Blo 2053435 6581837 := bstep (se 3 (by rfl) ⟨1234094, by rfl⟩ : syracuseStep 6581837 = 2468189) B2468189
theorem B17551565 : Blo 2053435 17551565 := bstep (se 3 (by rfl) ⟨3290918, by rfl⟩ : syracuseStep 17551565 = 6581837) B6581837
theorem B11701043 : Blo 2053435 11701043 := bstep (se 1 (by rfl) ⟨8775782, by rfl⟩ : syracuseStep 11701043 = 17551565) B17551565
theorem B7800695 : Blo 2053435 7800695 := bstep (se 1 (by rfl) ⟨5850521, by rfl⟩ : syracuseStep 7800695 = 11701043) B11701043
theorem B5200463 : Blo 2053435 5200463 := bstep (se 1 (by rfl) ⟨3900347, by rfl⟩ : syracuseStep 5200463 = 7800695) B7800695
theorem B3466975 : Blo 2053435 3466975 := bstep (se 1 (by rfl) ⟨2600231, by rfl⟩ : syracuseStep 3466975 = 5200463) B5200463
theorem B4622633 : Blo 2053435 4622633 := bstep (se 2 (by rfl) ⟨1733487, by rfl⟩ : syracuseStep 4622633 = 3466975) B3466975
theorem B3081755 : Blo 2053435 3081755 := bstep (se 1 (by rfl) ⟨2311316, by rfl⟩ : syracuseStep 3081755 = 4622633) B4622633
theorem B2054503 : Blo 2053435 2054503 := bstep (se 1 (by rfl) ⟨1540877, by rfl⟩ : syracuseStep 2054503 = 3081755) B3081755
theorem B2311321 : Blo 2053435 2311321 := bbase (se 2 (by rfl) ⟨866745, by rfl⟩ : syracuseStep 2311321 = 1733491) (by norm_num)
theorem B3081761 : Blo 2053435 3081761 := bstep (se 2 (by rfl) ⟨1155660, by rfl⟩ : syracuseStep 3081761 = 2311321) B2311321
theorem B2054507 : Blo 2053435 2054507 := bstep (se 1 (by rfl) ⟨1540880, by rfl⟩ : syracuseStep 2054507 = 3081761) B3081761
theorem B7800725 : Blo 2053435 7800725 := bbase (se 6 (by rfl) ⟨182829, by rfl⟩ : syracuseStep 7800725 = 365659) (by norm_num)
theorem B5200483 : Blo 2053435 5200483 := bstep (se 1 (by rfl) ⟨3900362, by rfl⟩ : syracuseStep 5200483 = 7800725) B7800725
theorem B6933977 : Blo 2053435 6933977 := bstep (se 2 (by rfl) ⟨2600241, by rfl⟩ : syracuseStep 6933977 = 5200483) B5200483
theorem B4622651 : Blo 2053435 4622651 := bstep (se 1 (by rfl) ⟨3466988, by rfl⟩ : syracuseStep 4622651 = 6933977) B6933977
theorem B3081767 : Blo 2053435 3081767 := bstep (se 1 (by rfl) ⟨2311325, by rfl⟩ : syracuseStep 3081767 = 4622651) B4622651
theorem B2054511 : Blo 2053435 2054511 := bstep (se 1 (by rfl) ⟨1540883, by rfl⟩ : syracuseStep 2054511 = 3081767) B3081767
theorem B3081773 : Blo 2053435 3081773 := bbase (se 3 (by rfl) ⟨577832, by rfl⟩ : syracuseStep 3081773 = 1155665) (by norm_num)
theorem B2054515 : Blo 2053435 2054515 := bstep (se 1 (by rfl) ⟨1540886, by rfl⟩ : syracuseStep 2054515 = 3081773) B3081773
theorem B4622669 : Blo 2053435 4622669 := bbase (se 3 (by rfl) ⟨866750, by rfl⟩ : syracuseStep 4622669 = 1733501) (by norm_num)
theorem B3081779 : Blo 2053435 3081779 := bstep (se 1 (by rfl) ⟨2311334, by rfl⟩ : syracuseStep 3081779 = 4622669) B4622669
theorem B2054519 : Blo 2053435 2054519 := bstep (se 1 (by rfl) ⟨1540889, by rfl⟩ : syracuseStep 2054519 = 3081779) B3081779
theorem B2600257 : Blo 2053435 2600257 := bbase (se 2 (by rfl) ⟨975096, by rfl⟩ : syracuseStep 2600257 = 1950193) (by norm_num)
theorem B3467009 : Blo 2053435 3467009 := bstep (se 2 (by rfl) ⟨1300128, by rfl⟩ : syracuseStep 3467009 = 2600257) B2600257
theorem B2311339 : Blo 2053435 2311339 := bstep (se 1 (by rfl) ⟨1733504, by rfl⟩ : syracuseStep 2311339 = 3467009) B3467009
theorem B3081785 : Blo 2053435 3081785 := bstep (se 2 (by rfl) ⟨1155669, by rfl⟩ : syracuseStep 3081785 = 2311339) B2311339
theorem B2054523 : Blo 2053435 2054523 := bstep (se 1 (by rfl) ⟨1540892, by rfl⟩ : syracuseStep 2054523 = 3081785) B3081785
theorem B3290957 : Blo 2053435 3290957 := bbase (se 3 (by rfl) ⟨617054, by rfl⟩ : syracuseStep 3290957 = 1234109) (by norm_num)
theorem B2193971 : Blo 2053435 2193971 := bstep (se 1 (by rfl) ⟨1645478, by rfl⟩ : syracuseStep 2193971 = 3290957) B3290957
theorem B23402357 : Blo 2053435 23402357 := bstep (se 5 (by rfl) ⟨1096985, by rfl⟩ : syracuseStep 23402357 = 2193971) B2193971
theorem B15601571 : Blo 2053435 15601571 := bstep (se 1 (by rfl) ⟨11701178, by rfl⟩ : syracuseStep 15601571 = 23402357) B23402357
theorem B10401047 : Blo 2053435 10401047 := bstep (se 1 (by rfl) ⟨7800785, by rfl⟩ : syracuseStep 10401047 = 15601571) B15601571
theorem B6934031 : Blo 2053435 6934031 := bstep (se 1 (by rfl) ⟨5200523, by rfl⟩ : syracuseStep 6934031 = 10401047) B10401047
theorem B4622687 : Blo 2053435 4622687 := bstep (se 1 (by rfl) ⟨3467015, by rfl⟩ : syracuseStep 4622687 = 6934031) B6934031
theorem B3081791 : Blo 2053435 3081791 := bstep (se 1 (by rfl) ⟨2311343, by rfl⟩ : syracuseStep 3081791 = 4622687) B4622687
theorem B2054527 : Blo 2053435 2054527 := bstep (se 1 (by rfl) ⟨1540895, by rfl⟩ : syracuseStep 2054527 = 3081791) B3081791
theorem B3081797 : Blo 2053435 3081797 := bbase (se 4 (by rfl) ⟨288918, by rfl⟩ : syracuseStep 3081797 = 577837) (by norm_num)
theorem B2054531 : Blo 2053435 2054531 := bstep (se 1 (by rfl) ⟨1540898, by rfl⟩ : syracuseStep 2054531 = 3081797) B3081797
theorem B3467029 : Blo 2053435 3467029 := bbase (se 6 (by rfl) ⟨81258, by rfl⟩ : syracuseStep 3467029 = 162517) (by norm_num)
theorem B4622705 : Blo 2053435 4622705 := bstep (se 2 (by rfl) ⟨1733514, by rfl⟩ : syracuseStep 4622705 = 3467029) B3467029
theorem B3081803 : Blo 2053435 3081803 := bstep (se 1 (by rfl) ⟨2311352, by rfl⟩ : syracuseStep 3081803 = 4622705) B4622705
theorem B2054535 : Blo 2053435 2054535 := bstep (se 1 (by rfl) ⟨1540901, by rfl⟩ : syracuseStep 2054535 = 3081803) B3081803
theorem B2311357 : Blo 2053435 2311357 := bbase (se 3 (by rfl) ⟨433379, by rfl⟩ : syracuseStep 2311357 = 866759) (by norm_num)
theorem B3081809 : Blo 2053435 3081809 := bstep (se 2 (by rfl) ⟨1155678, by rfl⟩ : syracuseStep 3081809 = 2311357) B2311357
theorem B2054539 : Blo 2053435 2054539 := bstep (se 1 (by rfl) ⟨1540904, by rfl⟩ : syracuseStep 2054539 = 3081809) B3081809
theorem B6934085 : Blo 2053435 6934085 := bbase (se 4 (by rfl) ⟨650070, by rfl⟩ : syracuseStep 6934085 = 1300141) (by norm_num)
theorem B4622723 : Blo 2053435 4622723 := bstep (se 1 (by rfl) ⟨3467042, by rfl⟩ : syracuseStep 4622723 = 6934085) B6934085
theorem B3081815 : Blo 2053435 3081815 := bstep (se 1 (by rfl) ⟨2311361, by rfl⟩ : syracuseStep 3081815 = 4622723) B4622723
theorem B2054543 : Blo 2053435 2054543 := bstep (se 1 (by rfl) ⟨1540907, by rfl⟩ : syracuseStep 2054543 = 3081815) B3081815
theorem B3081821 : Blo 2053435 3081821 := bbase (se 3 (by rfl) ⟨577841, by rfl⟩ : syracuseStep 3081821 = 1155683) (by norm_num)
theorem B2054547 : Blo 2053435 2054547 := bstep (se 1 (by rfl) ⟨1540910, by rfl⟩ : syracuseStep 2054547 = 3081821) B3081821
theorem B4622741 : Blo 2053435 4622741 := bbase (se 6 (by rfl) ⟨108345, by rfl⟩ : syracuseStep 4622741 = 216691) (by norm_num)
theorem B3081827 : Blo 2053435 3081827 := bstep (se 1 (by rfl) ⟨2311370, by rfl⟩ : syracuseStep 3081827 = 4622741) B4622741
theorem B2054551 : Blo 2053435 2054551 := bstep (se 1 (by rfl) ⟨1540913, by rfl⟩ : syracuseStep 2054551 = 3081827) B3081827
theorem B6582005 : Blo 2053435 6582005 := bbase (se 5 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 6582005 = 617063) (by norm_num)
theorem B4388003 : Blo 2053435 4388003 := bstep (se 1 (by rfl) ⟨3291002, by rfl⟩ : syracuseStep 4388003 = 6582005) B6582005
theorem B2925335 : Blo 2053435 2925335 := bstep (se 1 (by rfl) ⟨2194001, by rfl⟩ : syracuseStep 2925335 = 4388003) B4388003
theorem B7800893 : Blo 2053435 7800893 := bstep (se 3 (by rfl) ⟨1462667, by rfl⟩ : syracuseStep 7800893 = 2925335) B2925335
theorem B5200595 : Blo 2053435 5200595 := bstep (se 1 (by rfl) ⟨3900446, by rfl⟩ : syracuseStep 5200595 = 7800893) B7800893
theorem B3467063 : Blo 2053435 3467063 := bstep (se 1 (by rfl) ⟨2600297, by rfl⟩ : syracuseStep 3467063 = 5200595) B5200595
theorem B2311375 : Blo 2053435 2311375 := bstep (se 1 (by rfl) ⟨1733531, by rfl⟩ : syracuseStep 2311375 = 3467063) B3467063
theorem B3081833 : Blo 2053435 3081833 := bstep (se 2 (by rfl) ⟨1155687, by rfl⟩ : syracuseStep 3081833 = 2311375) B2311375
theorem B2054555 : Blo 2053435 2054555 := bstep (se 1 (by rfl) ⟨1540916, by rfl⟩ : syracuseStep 2054555 = 3081833) B3081833
theorem B8776021 : Blo 2053435 8776021 := bbase (se 10 (by rfl) ⟨12855, by rfl⟩ : syracuseStep 8776021 = 25711) (by norm_num)
theorem B11701361 : Blo 2053435 11701361 := bstep (se 2 (by rfl) ⟨4388010, by rfl⟩ : syracuseStep 11701361 = 8776021) B8776021
theorem B7800907 : Blo 2053435 7800907 := bstep (se 1 (by rfl) ⟨5850680, by rfl⟩ : syracuseStep 7800907 = 11701361) B11701361
theorem B10401209 : Blo 2053435 10401209 := bstep (se 2 (by rfl) ⟨3900453, by rfl⟩ : syracuseStep 10401209 = 7800907) B7800907
theorem B6934139 : Blo 2053435 6934139 := bstep (se 1 (by rfl) ⟨5200604, by rfl⟩ : syracuseStep 6934139 = 10401209) B10401209
theorem B4622759 : Blo 2053435 4622759 := bstep (se 1 (by rfl) ⟨3467069, by rfl⟩ : syracuseStep 4622759 = 6934139) B6934139
theorem B3081839 : Blo 2053435 3081839 := bstep (se 1 (by rfl) ⟨2311379, by rfl⟩ : syracuseStep 3081839 = 4622759) B4622759
theorem B2054559 : Blo 2053435 2054559 := bstep (se 1 (by rfl) ⟨1540919, by rfl⟩ : syracuseStep 2054559 = 3081839) B3081839
theorem B3081845 : Blo 2053435 3081845 := bbase (se 5 (by rfl) ⟨144461, by rfl⟩ : syracuseStep 3081845 = 288923) (by norm_num)
theorem B2054563 : Blo 2053435 2054563 := bstep (se 1 (by rfl) ⟨1540922, by rfl⟩ : syracuseStep 2054563 = 3081845) B3081845
theorem B3900469 : Blo 2053435 3900469 := bbase (se 5 (by rfl) ⟨182834, by rfl⟩ : syracuseStep 3900469 = 365669) (by norm_num)
theorem B5200625 : Blo 2053435 5200625 := bstep (se 2 (by rfl) ⟨1950234, by rfl⟩ : syracuseStep 5200625 = 3900469) B3900469
theorem B3467083 : Blo 2053435 3467083 := bstep (se 1 (by rfl) ⟨2600312, by rfl⟩ : syracuseStep 3467083 = 5200625) B5200625
theorem B4622777 : Blo 2053435 4622777 := bstep (se 2 (by rfl) ⟨1733541, by rfl⟩ : syracuseStep 4622777 = 3467083) B3467083
theorem B3081851 : Blo 2053435 3081851 := bstep (se 1 (by rfl) ⟨2311388, by rfl⟩ : syracuseStep 3081851 = 4622777) B4622777
theorem B2054567 : Blo 2053435 2054567 := bstep (se 1 (by rfl) ⟨1540925, by rfl⟩ : syracuseStep 2054567 = 3081851) B3081851
theorem B2311393 : Blo 2053435 2311393 := bbase (se 2 (by rfl) ⟨866772, by rfl⟩ : syracuseStep 2311393 = 1733545) (by norm_num)
theorem B3081857 : Blo 2053435 3081857 := bstep (se 2 (by rfl) ⟨1155696, by rfl⟩ : syracuseStep 3081857 = 2311393) B2311393
theorem B2054571 : Blo 2053435 2054571 := bstep (se 1 (by rfl) ⟨1540928, by rfl⟩ : syracuseStep 2054571 = 3081857) B3081857
theorem B5200645 : Blo 2053435 5200645 := bbase (se 4 (by rfl) ⟨487560, by rfl⟩ : syracuseStep 5200645 = 975121) (by norm_num)
theorem B6934193 : Blo 2053435 6934193 := bstep (se 2 (by rfl) ⟨2600322, by rfl⟩ : syracuseStep 6934193 = 5200645) B5200645
theorem B4622795 : Blo 2053435 4622795 := bstep (se 1 (by rfl) ⟨3467096, by rfl⟩ : syracuseStep 4622795 = 6934193) B6934193
theorem B3081863 : Blo 2053435 3081863 := bstep (se 1 (by rfl) ⟨2311397, by rfl⟩ : syracuseStep 3081863 = 4622795) B4622795
theorem B2054575 : Blo 2053435 2054575 := bstep (se 1 (by rfl) ⟨1540931, by rfl⟩ : syracuseStep 2054575 = 3081863) B3081863
theorem B3081869 : Blo 2053435 3081869 := bbase (se 3 (by rfl) ⟨577850, by rfl⟩ : syracuseStep 3081869 = 1155701) (by norm_num)
theorem B2054579 : Blo 2053435 2054579 := bstep (se 1 (by rfl) ⟨1540934, by rfl⟩ : syracuseStep 2054579 = 3081869) B3081869
theorem B4622813 : Blo 2053435 4622813 := bbase (se 3 (by rfl) ⟨866777, by rfl⟩ : syracuseStep 4622813 = 1733555) (by norm_num)
theorem B3081875 : Blo 2053435 3081875 := bstep (se 1 (by rfl) ⟨2311406, by rfl⟩ : syracuseStep 3081875 = 4622813) B4622813
theorem B2054583 : Blo 2053435 2054583 := bstep (se 1 (by rfl) ⟨1540937, by rfl⟩ : syracuseStep 2054583 = 3081875) B3081875
theorem B3467117 : Blo 2053435 3467117 := bbase (se 3 (by rfl) ⟨650084, by rfl⟩ : syracuseStep 3467117 = 1300169) (by norm_num)
theorem B2311411 : Blo 2053435 2311411 := bstep (se 1 (by rfl) ⟨1733558, by rfl⟩ : syracuseStep 2311411 = 3467117) B3467117
theorem B3081881 : Blo 2053435 3081881 := bstep (se 2 (by rfl) ⟨1155705, by rfl⟩ : syracuseStep 3081881 = 2311411) B2311411
theorem B2054587 : Blo 2053435 2054587 := bstep (se 1 (by rfl) ⟨1540940, by rfl⟩ : syracuseStep 2054587 = 3081881) B3081881
theorem B5343565 : Blo 2053435 5343565 := bbase (se 3 (by rfl) ⟨1001918, by rfl⟩ : syracuseStep 5343565 = 2003837) (by norm_num)
theorem B7124753 : Blo 2053435 7124753 := bstep (se 2 (by rfl) ⟨2671782, by rfl⟩ : syracuseStep 7124753 = 5343565) B5343565
theorem B18999341 : Blo 2053435 18999341 := bstep (se 3 (by rfl) ⟨3562376, by rfl⟩ : syracuseStep 18999341 = 7124753) B7124753
theorem B12666227 : Blo 2053435 12666227 := bstep (se 1 (by rfl) ⟨9499670, by rfl⟩ : syracuseStep 12666227 = 18999341) B18999341
theorem B33776605 : Blo 2053435 33776605 := bstep (se 3 (by rfl) ⟨6333113, by rfl⟩ : syracuseStep 33776605 = 12666227) B12666227
theorem B180141893 : Blo 2053435 180141893 := bstep (se 4 (by rfl) ⟨16888302, by rfl⟩ : syracuseStep 180141893 = 33776605) B33776605
theorem B120094595 : Blo 2053435 120094595 := bstep (se 1 (by rfl) ⟨90070946, by rfl⟩ : syracuseStep 120094595 = 180141893) B180141893
theorem B80063063 : Blo 2053435 80063063 := bstep (se 1 (by rfl) ⟨60047297, by rfl⟩ : syracuseStep 80063063 = 120094595) B120094595
theorem B53375375 : Blo 2053435 53375375 := bstep (se 1 (by rfl) ⟨40031531, by rfl⟩ : syracuseStep 53375375 = 80063063) B80063063
theorem B35583583 : Blo 2053435 35583583 := bstep (se 1 (by rfl) ⟨26687687, by rfl⟩ : syracuseStep 35583583 = 53375375) B53375375
theorem B47444777 : Blo 2053435 47444777 := bstep (se 2 (by rfl) ⟨17791791, by rfl⟩ : syracuseStep 47444777 = 35583583) B35583583
theorem B31629851 : Blo 2053435 31629851 := bstep (se 1 (by rfl) ⟨23722388, by rfl⟩ : syracuseStep 31629851 = 47444777) B47444777
theorem B21086567 : Blo 2053435 21086567 := bstep (se 1 (by rfl) ⟨15814925, by rfl⟩ : syracuseStep 21086567 = 31629851) B31629851
theorem B14057711 : Blo 2053435 14057711 := bstep (se 1 (by rfl) ⟨10543283, by rfl⟩ : syracuseStep 14057711 = 21086567) B21086567
theorem B9371807 : Blo 2053435 9371807 := bstep (se 1 (by rfl) ⟨7028855, by rfl⟩ : syracuseStep 9371807 = 14057711) B14057711
theorem B6247871 : Blo 2053435 6247871 := bstep (se 1 (by rfl) ⟨4685903, by rfl⟩ : syracuseStep 6247871 = 9371807) B9371807
theorem B4165247 : Blo 2053435 4165247 := bstep (se 1 (by rfl) ⟨3123935, by rfl⟩ : syracuseStep 4165247 = 6247871) B6247871
theorem B11107325 : Blo 2053435 11107325 := bstep (se 3 (by rfl) ⟨2082623, by rfl⟩ : syracuseStep 11107325 = 4165247) B4165247
theorem B29619533 : Blo 2053435 29619533 := bstep (se 3 (by rfl) ⟨5553662, by rfl⟩ : syracuseStep 29619533 = 11107325) B11107325
theorem B19746355 : Blo 2053435 19746355 := bstep (se 1 (by rfl) ⟨14809766, by rfl⟩ : syracuseStep 19746355 = 29619533) B29619533
theorem B26328473 : Blo 2053435 26328473 := bstep (se 2 (by rfl) ⟨9873177, by rfl⟩ : syracuseStep 26328473 = 19746355) B19746355
theorem B17552315 : Blo 2053435 17552315 := bstep (se 1 (by rfl) ⟨13164236, by rfl⟩ : syracuseStep 17552315 = 26328473) B26328473
theorem B11701543 : Blo 2053435 11701543 := bstep (se 1 (by rfl) ⟨8776157, by rfl⟩ : syracuseStep 11701543 = 17552315) B17552315
theorem B15602057 : Blo 2053435 15602057 := bstep (se 2 (by rfl) ⟨5850771, by rfl⟩ : syracuseStep 15602057 = 11701543) B11701543
theorem B10401371 : Blo 2053435 10401371 := bstep (se 1 (by rfl) ⟨7801028, by rfl⟩ : syracuseStep 10401371 = 15602057) B15602057
theorem B6934247 : Blo 2053435 6934247 := bstep (se 1 (by rfl) ⟨5200685, by rfl⟩ : syracuseStep 6934247 = 10401371) B10401371
theorem B4622831 : Blo 2053435 4622831 := bstep (se 1 (by rfl) ⟨3467123, by rfl⟩ : syracuseStep 4622831 = 6934247) B6934247
theorem B3081887 : Blo 2053435 3081887 := bstep (se 1 (by rfl) ⟨2311415, by rfl⟩ : syracuseStep 3081887 = 4622831) B4622831
theorem B2054591 : Blo 2053435 2054591 := bstep (se 1 (by rfl) ⟨1540943, by rfl⟩ : syracuseStep 2054591 = 3081887) B3081887
theorem B3081893 : Blo 2053435 3081893 := bbase (se 4 (by rfl) ⟨288927, by rfl⟩ : syracuseStep 3081893 = 577855) (by norm_num)
theorem B2054595 : Blo 2053435 2054595 := bstep (se 1 (by rfl) ⟨1540946, by rfl⟩ : syracuseStep 2054595 = 3081893) B3081893
theorem B2600353 : Blo 2053435 2600353 := bbase (se 2 (by rfl) ⟨975132, by rfl⟩ : syracuseStep 2600353 = 1950265) (by norm_num)
theorem B3467137 : Blo 2053435 3467137 := bstep (se 2 (by rfl) ⟨1300176, by rfl⟩ : syracuseStep 3467137 = 2600353) B2600353
theorem B4622849 : Blo 2053435 4622849 := bstep (se 2 (by rfl) ⟨1733568, by rfl⟩ : syracuseStep 4622849 = 3467137) B3467137
theorem B3081899 : Blo 2053435 3081899 := bstep (se 1 (by rfl) ⟨2311424, by rfl⟩ : syracuseStep 3081899 = 4622849) B4622849
theorem B2054599 : Blo 2053435 2054599 := bstep (se 1 (by rfl) ⟨1540949, by rfl⟩ : syracuseStep 2054599 = 3081899) B3081899
theorem B2311429 : Blo 2053435 2311429 := bbase (se 4 (by rfl) ⟨216696, by rfl⟩ : syracuseStep 2311429 = 433393) (by norm_num)
theorem B3081905 : Blo 2053435 3081905 := bstep (se 2 (by rfl) ⟨1155714, by rfl⟩ : syracuseStep 3081905 = 2311429) B2311429
theorem B2054603 : Blo 2053435 2054603 := bstep (se 1 (by rfl) ⟨1540952, by rfl⟩ : syracuseStep 2054603 = 3081905) B3081905
theorem B2194057 : Blo 2053435 2194057 := bbase (se 2 (by rfl) ⟨822771, by rfl⟩ : syracuseStep 2194057 = 1645543) (by norm_num)
theorem B2925409 : Blo 2053435 2925409 := bstep (se 2 (by rfl) ⟨1097028, by rfl⟩ : syracuseStep 2925409 = 2194057) B2194057
theorem B3900545 : Blo 2053435 3900545 := bstep (se 2 (by rfl) ⟨1462704, by rfl⟩ : syracuseStep 3900545 = 2925409) B2925409
theorem B2600363 : Blo 2053435 2600363 := bstep (se 1 (by rfl) ⟨1950272, by rfl⟩ : syracuseStep 2600363 = 3900545) B3900545
theorem B6934301 : Blo 2053435 6934301 := bstep (se 3 (by rfl) ⟨1300181, by rfl⟩ : syracuseStep 6934301 = 2600363) B2600363
theorem B4622867 : Blo 2053435 4622867 := bstep (se 1 (by rfl) ⟨3467150, by rfl⟩ : syracuseStep 4622867 = 6934301) B6934301
theorem B3081911 : Blo 2053435 3081911 := bstep (se 1 (by rfl) ⟨2311433, by rfl⟩ : syracuseStep 3081911 = 4622867) B4622867
theorem B2054607 : Blo 2053435 2054607 := bstep (se 1 (by rfl) ⟨1540955, by rfl⟩ : syracuseStep 2054607 = 3081911) B3081911
theorem B3081917 : Blo 2053435 3081917 := bbase (se 3 (by rfl) ⟨577859, by rfl⟩ : syracuseStep 3081917 = 1155719) (by norm_num)
theorem B2054611 : Blo 2053435 2054611 := bstep (se 1 (by rfl) ⟨1540958, by rfl⟩ : syracuseStep 2054611 = 3081917) B3081917
theorem B4622885 : Blo 2053435 4622885 := bbase (se 4 (by rfl) ⟨433395, by rfl⟩ : syracuseStep 4622885 = 866791) (by norm_num)
theorem B3081923 : Blo 2053435 3081923 := bstep (se 1 (by rfl) ⟨2311442, by rfl⟩ : syracuseStep 3081923 = 4622885) B4622885
theorem B2054615 : Blo 2053435 2054615 := bstep (se 1 (by rfl) ⟨1540961, by rfl⟩ : syracuseStep 2054615 = 3081923) B3081923
theorem B5200757 : Blo 2053435 5200757 := bbase (se 5 (by rfl) ⟨243785, by rfl⟩ : syracuseStep 5200757 = 487571) (by norm_num)
theorem B3467171 : Blo 2053435 3467171 := bstep (se 1 (by rfl) ⟨2600378, by rfl⟩ : syracuseStep 3467171 = 5200757) B5200757
theorem B2311447 : Blo 2053435 2311447 := bstep (se 1 (by rfl) ⟨1733585, by rfl⟩ : syracuseStep 2311447 = 3467171) B3467171
theorem B3081929 : Blo 2053435 3081929 := bstep (se 2 (by rfl) ⟨1155723, by rfl⟩ : syracuseStep 3081929 = 2311447) B2311447
theorem B2054619 : Blo 2053435 2054619 := bstep (se 1 (by rfl) ⟨1540964, by rfl⟩ : syracuseStep 2054619 = 3081929) B3081929
theorem B7028965 : Blo 2053435 7028965 := bbase (se 4 (by rfl) ⟨658965, by rfl⟩ : syracuseStep 7028965 = 1317931) (by norm_num)
theorem B9371953 : Blo 2053435 9371953 := bstep (se 2 (by rfl) ⟨3514482, by rfl⟩ : syracuseStep 9371953 = 7028965) B7028965
theorem B49983749 : Blo 2053435 49983749 := bstep (se 4 (by rfl) ⟨4685976, by rfl⟩ : syracuseStep 49983749 = 9371953) B9371953
theorem B33322499 : Blo 2053435 33322499 := bstep (se 1 (by rfl) ⟨24991874, by rfl⟩ : syracuseStep 33322499 = 49983749) B49983749
theorem B22214999 : Blo 2053435 22214999 := bstep (se 1 (by rfl) ⟨16661249, by rfl⟩ : syracuseStep 22214999 = 33322499) B33322499
theorem B14809999 : Blo 2053435 14809999 := bstep (se 1 (by rfl) ⟨11107499, by rfl⟩ : syracuseStep 14809999 = 22214999) B22214999
theorem B19746665 : Blo 2053435 19746665 := bstep (se 2 (by rfl) ⟨7404999, by rfl⟩ : syracuseStep 19746665 = 14809999) B14809999
theorem B13164443 : Blo 2053435 13164443 := bstep (se 1 (by rfl) ⟨9873332, by rfl⟩ : syracuseStep 13164443 = 19746665) B19746665
theorem B8776295 : Blo 2053435 8776295 := bstep (se 1 (by rfl) ⟨6582221, by rfl⟩ : syracuseStep 8776295 = 13164443) B13164443
theorem B5850863 : Blo 2053435 5850863 := bstep (se 1 (by rfl) ⟨4388147, by rfl⟩ : syracuseStep 5850863 = 8776295) B8776295
theorem B3900575 : Blo 2053435 3900575 := bstep (se 1 (by rfl) ⟨2925431, by rfl⟩ : syracuseStep 3900575 = 5850863) B5850863
theorem B10401533 : Blo 2053435 10401533 := bstep (se 3 (by rfl) ⟨1950287, by rfl⟩ : syracuseStep 10401533 = 3900575) B3900575
theorem B6934355 : Blo 2053435 6934355 := bstep (se 1 (by rfl) ⟨5200766, by rfl⟩ : syracuseStep 6934355 = 10401533) B10401533
theorem B4622903 : Blo 2053435 4622903 := bstep (se 1 (by rfl) ⟨3467177, by rfl⟩ : syracuseStep 4622903 = 6934355) B6934355
theorem B3081935 : Blo 2053435 3081935 := bstep (se 1 (by rfl) ⟨2311451, by rfl⟩ : syracuseStep 3081935 = 4622903) B4622903
theorem B2054623 : Blo 2053435 2054623 := bstep (se 1 (by rfl) ⟨1540967, by rfl⟩ : syracuseStep 2054623 = 3081935) B3081935
theorem B3081941 : Blo 2053435 3081941 := bbase (se 7 (by rfl) ⟨36116, by rfl⟩ : syracuseStep 3081941 = 72233) (by norm_num)
theorem B2054627 : Blo 2053435 2054627 := bstep (se 1 (by rfl) ⟨1540970, by rfl⟩ : syracuseStep 2054627 = 3081941) B3081941
theorem B4388165 : Blo 2053435 4388165 := bbase (se 4 (by rfl) ⟨411390, by rfl⟩ : syracuseStep 4388165 = 822781) (by norm_num)
theorem B2925443 : Blo 2053435 2925443 := bstep (se 1 (by rfl) ⟨2194082, by rfl⟩ : syracuseStep 2925443 = 4388165) B4388165
theorem B7801181 : Blo 2053435 7801181 := bstep (se 3 (by rfl) ⟨1462721, by rfl⟩ : syracuseStep 7801181 = 2925443) B2925443
theorem B5200787 : Blo 2053435 5200787 := bstep (se 1 (by rfl) ⟨3900590, by rfl⟩ : syracuseStep 5200787 = 7801181) B7801181
theorem B3467191 : Blo 2053435 3467191 := bstep (se 1 (by rfl) ⟨2600393, by rfl⟩ : syracuseStep 3467191 = 5200787) B5200787
theorem B4622921 : Blo 2053435 4622921 := bstep (se 2 (by rfl) ⟨1733595, by rfl⟩ : syracuseStep 4622921 = 3467191) B3467191
theorem B3081947 : Blo 2053435 3081947 := bstep (se 1 (by rfl) ⟨2311460, by rfl⟩ : syracuseStep 3081947 = 4622921) B4622921
theorem B2054631 : Blo 2053435 2054631 := bstep (se 1 (by rfl) ⟨1540973, by rfl⟩ : syracuseStep 2054631 = 3081947) B3081947
theorem B2311465 : Blo 2053435 2311465 := bbase (se 2 (by rfl) ⟨866799, by rfl⟩ : syracuseStep 2311465 = 1733599) (by norm_num)
theorem B3081953 : Blo 2053435 3081953 := bstep (se 2 (by rfl) ⟨1155732, by rfl⟩ : syracuseStep 3081953 = 2311465) B2311465
theorem B2054635 : Blo 2053435 2054635 := bstep (se 1 (by rfl) ⟨1540976, by rfl⟩ : syracuseStep 2054635 = 3081953) B3081953
theorem B8444357 : Blo 2053435 8444357 := bbase (se 4 (by rfl) ⟨791658, by rfl⟩ : syracuseStep 8444357 = 1583317) (by norm_num)
theorem B5629571 : Blo 2053435 5629571 := bstep (se 1 (by rfl) ⟨4222178, by rfl⟩ : syracuseStep 5629571 = 8444357) B8444357
theorem B3753047 : Blo 2053435 3753047 := bstep (se 1 (by rfl) ⟨2814785, by rfl⟩ : syracuseStep 3753047 = 5629571) B5629571
theorem B2502031 : Blo 2053435 2502031 := bstep (se 1 (by rfl) ⟨1876523, by rfl⟩ : syracuseStep 2502031 = 3753047) B3753047
theorem B3336041 : Blo 2053435 3336041 := bstep (se 2 (by rfl) ⟨1251015, by rfl⟩ : syracuseStep 3336041 = 2502031) B2502031
theorem B2224027 : Blo 2053435 2224027 := bstep (se 1 (by rfl) ⟨1668020, by rfl⟩ : syracuseStep 2224027 = 3336041) B3336041
theorem B11861477 : Blo 2053435 11861477 := bstep (se 4 (by rfl) ⟨1112013, by rfl⟩ : syracuseStep 11861477 = 2224027) B2224027
theorem B7907651 : Blo 2053435 7907651 := bstep (se 1 (by rfl) ⟨5930738, by rfl⟩ : syracuseStep 7907651 = 11861477) B11861477
theorem B5271767 : Blo 2053435 5271767 := bstep (se 1 (by rfl) ⟨3953825, by rfl⟩ : syracuseStep 5271767 = 7907651) B7907651
theorem B3514511 : Blo 2053435 3514511 := bstep (se 1 (by rfl) ⟨2635883, by rfl⟩ : syracuseStep 3514511 = 5271767) B5271767
theorem B2343007 : Blo 2053435 2343007 := bstep (se 1 (by rfl) ⟨1757255, by rfl⟩ : syracuseStep 2343007 = 3514511) B3514511
theorem B3124009 : Blo 2053435 3124009 := bstep (se 2 (by rfl) ⟨1171503, by rfl⟩ : syracuseStep 3124009 = 2343007) B2343007
theorem B4165345 : Blo 2053435 4165345 := bstep (se 2 (by rfl) ⟨1562004, by rfl⟩ : syracuseStep 4165345 = 3124009) B3124009
theorem B5553793 : Blo 2053435 5553793 := bstep (se 2 (by rfl) ⟨2082672, by rfl⟩ : syracuseStep 5553793 = 4165345) B4165345
theorem B7405057 : Blo 2053435 7405057 := bstep (se 2 (by rfl) ⟨2776896, by rfl⟩ : syracuseStep 7405057 = 5553793) B5553793
theorem B9873409 : Blo 2053435 9873409 := bstep (se 2 (by rfl) ⟨3702528, by rfl⟩ : syracuseStep 9873409 = 7405057) B7405057
theorem B13164545 : Blo 2053435 13164545 := bstep (se 2 (by rfl) ⟨4936704, by rfl⟩ : syracuseStep 13164545 = 9873409) B9873409
theorem B8776363 : Blo 2053435 8776363 := bstep (se 1 (by rfl) ⟨6582272, by rfl⟩ : syracuseStep 8776363 = 13164545) B13164545
theorem B11701817 : Blo 2053435 11701817 := bstep (se 2 (by rfl) ⟨4388181, by rfl⟩ : syracuseStep 11701817 = 8776363) B8776363
theorem B7801211 : Blo 2053435 7801211 := bstep (se 1 (by rfl) ⟨5850908, by rfl⟩ : syracuseStep 7801211 = 11701817) B11701817
theorem B5200807 : Blo 2053435 5200807 := bstep (se 1 (by rfl) ⟨3900605, by rfl⟩ : syracuseStep 5200807 = 7801211) B7801211
theorem B6934409 : Blo 2053435 6934409 := bstep (se 2 (by rfl) ⟨2600403, by rfl⟩ : syracuseStep 6934409 = 5200807) B5200807
theorem B4622939 : Blo 2053435 4622939 := bstep (se 1 (by rfl) ⟨3467204, by rfl⟩ : syracuseStep 4622939 = 6934409) B6934409
theorem B3081959 : Blo 2053435 3081959 := bstep (se 1 (by rfl) ⟨2311469, by rfl⟩ : syracuseStep 3081959 = 4622939) B4622939
theorem B2054639 : Blo 2053435 2054639 := bstep (se 1 (by rfl) ⟨1540979, by rfl⟩ : syracuseStep 2054639 = 3081959) B3081959
theorem B3081965 : Blo 2053435 3081965 := bbase (se 3 (by rfl) ⟨577868, by rfl⟩ : syracuseStep 3081965 = 1155737) (by norm_num)
theorem B2054643 : Blo 2053435 2054643 := bstep (se 1 (by rfl) ⟨1540982, by rfl⟩ : syracuseStep 2054643 = 3081965) B3081965
theorem B4622957 : Blo 2053435 4622957 := bbase (se 3 (by rfl) ⟨866804, by rfl⟩ : syracuseStep 4622957 = 1733609) (by norm_num)
theorem B3081971 : Blo 2053435 3081971 := bstep (se 1 (by rfl) ⟨2311478, by rfl⟩ : syracuseStep 3081971 = 4622957) B4622957
theorem B2054647 : Blo 2053435 2054647 := bstep (se 1 (by rfl) ⟨1540985, by rfl⟩ : syracuseStep 2054647 = 3081971) B3081971
theorem B3900629 : Blo 2053435 3900629 := bbase (se 7 (by rfl) ⟨45710, by rfl⟩ : syracuseStep 3900629 = 91421) (by norm_num)
theorem B2600419 : Blo 2053435 2600419 := bstep (se 1 (by rfl) ⟨1950314, by rfl⟩ : syracuseStep 2600419 = 3900629) B3900629
theorem B3467225 : Blo 2053435 3467225 := bstep (se 2 (by rfl) ⟨1300209, by rfl⟩ : syracuseStep 3467225 = 2600419) B2600419
theorem B2311483 : Blo 2053435 2311483 := bstep (se 1 (by rfl) ⟨1733612, by rfl⟩ : syracuseStep 2311483 = 3467225) B3467225
theorem B3081977 : Blo 2053435 3081977 := bstep (se 2 (by rfl) ⟨1155741, by rfl⟩ : syracuseStep 3081977 = 2311483) B2311483
theorem B2054651 : Blo 2053435 2054651 := bstep (se 1 (by rfl) ⟨1540988, by rfl⟩ : syracuseStep 2054651 = 3081977) B3081977
theorem B5416645 : Blo 2053435 5416645 := bbase (se 4 (by rfl) ⟨507810, by rfl⟩ : syracuseStep 5416645 = 1015621) (by norm_num)
theorem B7222193 : Blo 2053435 7222193 := bstep (se 2 (by rfl) ⟨2708322, by rfl⟩ : syracuseStep 7222193 = 5416645) B5416645
theorem B4814795 : Blo 2053435 4814795 := bstep (se 1 (by rfl) ⟨3611096, by rfl⟩ : syracuseStep 4814795 = 7222193) B7222193
theorem B3209863 : Blo 2053435 3209863 := bstep (se 1 (by rfl) ⟨2407397, by rfl⟩ : syracuseStep 3209863 = 4814795) B4814795
theorem B4279817 : Blo 2053435 4279817 := bstep (se 2 (by rfl) ⟨1604931, by rfl⟩ : syracuseStep 4279817 = 3209863) B3209863
theorem B11412845 : Blo 2053435 11412845 := bstep (se 3 (by rfl) ⟨2139908, by rfl⟩ : syracuseStep 11412845 = 4279817) B4279817
theorem B7608563 : Blo 2053435 7608563 := bstep (se 1 (by rfl) ⟨5706422, by rfl⟩ : syracuseStep 7608563 = 11412845) B11412845
theorem B5072375 : Blo 2053435 5072375 := bstep (se 1 (by rfl) ⟨3804281, by rfl⟩ : syracuseStep 5072375 = 7608563) B7608563
theorem B3381583 : Blo 2053435 3381583 := bstep (se 1 (by rfl) ⟨2536187, by rfl⟩ : syracuseStep 3381583 = 5072375) B5072375
theorem B4508777 : Blo 2053435 4508777 := bstep (se 2 (by rfl) ⟨1690791, by rfl⟩ : syracuseStep 4508777 = 3381583) B3381583
theorem B3005851 : Blo 2053435 3005851 := bstep (se 1 (by rfl) ⟨2254388, by rfl⟩ : syracuseStep 3005851 = 4508777) B4508777
theorem B4007801 : Blo 2053435 4007801 := bstep (se 2 (by rfl) ⟨1502925, by rfl⟩ : syracuseStep 4007801 = 3005851) B3005851
theorem B2671867 : Blo 2053435 2671867 := bstep (se 1 (by rfl) ⟨2003900, by rfl⟩ : syracuseStep 2671867 = 4007801) B4007801
theorem B3562489 : Blo 2053435 3562489 := bstep (se 2 (by rfl) ⟨1335933, by rfl⟩ : syracuseStep 3562489 = 2671867) B2671867
theorem B4749985 : Blo 2053435 4749985 := bstep (se 2 (by rfl) ⟨1781244, by rfl⟩ : syracuseStep 4749985 = 3562489) B3562489
theorem B6333313 : Blo 2053435 6333313 := bstep (se 2 (by rfl) ⟨2374992, by rfl⟩ : syracuseStep 6333313 = 4749985) B4749985
theorem B8444417 : Blo 2053435 8444417 := bstep (se 2 (by rfl) ⟨3166656, by rfl⟩ : syracuseStep 8444417 = 6333313) B6333313
theorem B22518445 : Blo 2053435 22518445 := bstep (se 3 (by rfl) ⟨4222208, by rfl⟩ : syracuseStep 22518445 = 8444417) B8444417
theorem B30024593 : Blo 2053435 30024593 := bstep (se 2 (by rfl) ⟨11259222, by rfl⟩ : syracuseStep 30024593 = 22518445) B22518445
theorem B20016395 : Blo 2053435 20016395 := bstep (se 1 (by rfl) ⟨15012296, by rfl⟩ : syracuseStep 20016395 = 30024593) B30024593
theorem B13344263 : Blo 2053435 13344263 := bstep (se 1 (by rfl) ⟨10008197, by rfl⟩ : syracuseStep 13344263 = 20016395) B20016395
theorem B8896175 : Blo 2053435 8896175 := bstep (se 1 (by rfl) ⟨6672131, by rfl⟩ : syracuseStep 8896175 = 13344263) B13344263
theorem B5930783 : Blo 2053435 5930783 := bstep (se 1 (by rfl) ⟨4448087, by rfl⟩ : syracuseStep 5930783 = 8896175) B8896175
theorem B3953855 : Blo 2053435 3953855 := bstep (se 1 (by rfl) ⟨2965391, by rfl⟩ : syracuseStep 3953855 = 5930783) B5930783
theorem B2635903 : Blo 2053435 2635903 := bstep (se 1 (by rfl) ⟨1976927, by rfl⟩ : syracuseStep 2635903 = 3953855) B3953855
theorem B3514537 : Blo 2053435 3514537 := bstep (se 2 (by rfl) ⟨1317951, by rfl⟩ : syracuseStep 3514537 = 2635903) B2635903
theorem B4686049 : Blo 2053435 4686049 := bstep (se 2 (by rfl) ⟨1757268, by rfl⟩ : syracuseStep 4686049 = 3514537) B3514537
theorem B6248065 : Blo 2053435 6248065 := bstep (se 2 (by rfl) ⟨2343024, by rfl⟩ : syracuseStep 6248065 = 4686049) B4686049
theorem B8330753 : Blo 2053435 8330753 := bstep (se 2 (by rfl) ⟨3124032, by rfl⟩ : syracuseStep 8330753 = 6248065) B6248065
theorem B22215341 : Blo 2053435 22215341 := bstep (se 3 (by rfl) ⟨4165376, by rfl⟩ : syracuseStep 22215341 = 8330753) B8330753
theorem B59240909 : Blo 2053435 59240909 := bstep (se 3 (by rfl) ⟨11107670, by rfl⟩ : syracuseStep 59240909 = 22215341) B22215341
theorem B39493939 : Blo 2053435 39493939 := bstep (se 1 (by rfl) ⟨29620454, by rfl⟩ : syracuseStep 39493939 = 59240909) B59240909
theorem B52658585 : Blo 2053435 52658585 := bstep (se 2 (by rfl) ⟨19746969, by rfl⟩ : syracuseStep 52658585 = 39493939) B39493939
theorem B35105723 : Blo 2053435 35105723 := bstep (se 1 (by rfl) ⟨26329292, by rfl⟩ : syracuseStep 35105723 = 52658585) B52658585
theorem B23403815 : Blo 2053435 23403815 := bstep (se 1 (by rfl) ⟨17552861, by rfl⟩ : syracuseStep 23403815 = 35105723) B35105723
theorem B15602543 : Blo 2053435 15602543 := bstep (se 1 (by rfl) ⟨11701907, by rfl⟩ : syracuseStep 15602543 = 23403815) B23403815
theorem B10401695 : Blo 2053435 10401695 := bstep (se 1 (by rfl) ⟨7801271, by rfl⟩ : syracuseStep 10401695 = 15602543) B15602543
theorem B6934463 : Blo 2053435 6934463 := bstep (se 1 (by rfl) ⟨5200847, by rfl⟩ : syracuseStep 6934463 = 10401695) B10401695
theorem B4622975 : Blo 2053435 4622975 := bstep (se 1 (by rfl) ⟨3467231, by rfl⟩ : syracuseStep 4622975 = 6934463) B6934463
theorem B3081983 : Blo 2053435 3081983 := bstep (se 1 (by rfl) ⟨2311487, by rfl⟩ : syracuseStep 3081983 = 4622975) B4622975
theorem B2054655 : Blo 2053435 2054655 := bstep (se 1 (by rfl) ⟨1540991, by rfl⟩ : syracuseStep 2054655 = 3081983) B3081983
theorem B3081989 : Blo 2053435 3081989 := bbase (se 4 (by rfl) ⟨288936, by rfl⟩ : syracuseStep 3081989 = 577873) (by norm_num)
theorem B2054659 : Blo 2053435 2054659 := bstep (se 1 (by rfl) ⟨1540994, by rfl⟩ : syracuseStep 2054659 = 3081989) B3081989
theorem B3467245 : Blo 2053435 3467245 := bbase (se 3 (by rfl) ⟨650108, by rfl⟩ : syracuseStep 3467245 = 1300217) (by norm_num)
theorem B4622993 : Blo 2053435 4622993 := bstep (se 2 (by rfl) ⟨1733622, by rfl⟩ : syracuseStep 4622993 = 3467245) B3467245
theorem B3081995 : Blo 2053435 3081995 := bstep (se 1 (by rfl) ⟨2311496, by rfl⟩ : syracuseStep 3081995 = 4622993) B4622993
theorem B2054663 : Blo 2053435 2054663 := bstep (se 1 (by rfl) ⟨1540997, by rfl⟩ : syracuseStep 2054663 = 3081995) B3081995
theorem B2311501 : Blo 2053435 2311501 := bbase (se 3 (by rfl) ⟨433406, by rfl⟩ : syracuseStep 2311501 = 866813) (by norm_num)
theorem B3082001 : Blo 2053435 3082001 := bstep (se 2 (by rfl) ⟨1155750, by rfl⟩ : syracuseStep 3082001 = 2311501) B2311501
theorem B2054667 : Blo 2053435 2054667 := bstep (se 1 (by rfl) ⟨1541000, by rfl⟩ : syracuseStep 2054667 = 3082001) B3082001
theorem B6934517 : Blo 2053435 6934517 := bbase (se 5 (by rfl) ⟨325055, by rfl⟩ : syracuseStep 6934517 = 650111) (by norm_num)
theorem B4623011 : Blo 2053435 4623011 := bstep (se 1 (by rfl) ⟨3467258, by rfl⟩ : syracuseStep 4623011 = 6934517) B6934517
theorem B3082007 : Blo 2053435 3082007 := bstep (se 1 (by rfl) ⟨2311505, by rfl⟩ : syracuseStep 3082007 = 4623011) B4623011
theorem B2054671 : Blo 2053435 2054671 := bstep (se 1 (by rfl) ⟨1541003, by rfl⟩ : syracuseStep 2054671 = 3082007) B3082007
theorem B3082013 : Blo 2053435 3082013 := bbase (se 3 (by rfl) ⟨577877, by rfl⟩ : syracuseStep 3082013 = 1155755) (by norm_num)
theorem B2054675 : Blo 2053435 2054675 := bstep (se 1 (by rfl) ⟨1541006, by rfl⟩ : syracuseStep 2054675 = 3082013) B3082013
theorem B4623029 : Blo 2053435 4623029 := bbase (se 5 (by rfl) ⟨216704, by rfl⟩ : syracuseStep 4623029 = 433409) (by norm_num)
theorem B3082019 : Blo 2053435 3082019 := bstep (se 1 (by rfl) ⟨2311514, by rfl⟩ : syracuseStep 3082019 = 4623029) B4623029
theorem B2054679 : Blo 2053435 2054679 := bstep (se 1 (by rfl) ⟨1541009, by rfl⟩ : syracuseStep 2054679 = 3082019) B3082019
theorem B11702069 : Blo 2053435 11702069 := bbase (se 5 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 11702069 = 1097069) (by norm_num)
theorem B7801379 : Blo 2053435 7801379 := bstep (se 1 (by rfl) ⟨5851034, by rfl⟩ : syracuseStep 7801379 = 11702069) B11702069
theorem B5200919 : Blo 2053435 5200919 := bstep (se 1 (by rfl) ⟨3900689, by rfl⟩ : syracuseStep 5200919 = 7801379) B7801379
theorem B3467279 : Blo 2053435 3467279 := bstep (se 1 (by rfl) ⟨2600459, by rfl⟩ : syracuseStep 3467279 = 5200919) B5200919
theorem B2311519 : Blo 2053435 2311519 := bstep (se 1 (by rfl) ⟨1733639, by rfl⟩ : syracuseStep 2311519 = 3467279) B3467279
theorem B3082025 : Blo 2053435 3082025 := bstep (se 2 (by rfl) ⟨1155759, by rfl⟩ : syracuseStep 3082025 = 2311519) B2311519
theorem B2054683 : Blo 2053435 2054683 := bstep (se 1 (by rfl) ⟨1541012, by rfl⟩ : syracuseStep 2054683 = 3082025) B3082025
theorem B5851045 : Blo 2053435 5851045 := bbase (se 4 (by rfl) ⟨548535, by rfl⟩ : syracuseStep 5851045 = 1097071) (by norm_num)
theorem B7801393 : Blo 2053435 7801393 := bstep (se 2 (by rfl) ⟨2925522, by rfl⟩ : syracuseStep 7801393 = 5851045) B5851045
theorem B10401857 : Blo 2053435 10401857 := bstep (se 2 (by rfl) ⟨3900696, by rfl⟩ : syracuseStep 10401857 = 7801393) B7801393
theorem B6934571 : Blo 2053435 6934571 := bstep (se 1 (by rfl) ⟨5200928, by rfl⟩ : syracuseStep 6934571 = 10401857) B10401857
theorem B4623047 : Blo 2053435 4623047 := bstep (se 1 (by rfl) ⟨3467285, by rfl⟩ : syracuseStep 4623047 = 6934571) B6934571
theorem B3082031 : Blo 2053435 3082031 := bstep (se 1 (by rfl) ⟨2311523, by rfl⟩ : syracuseStep 3082031 = 4623047) B4623047
theorem B2054687 : Blo 2053435 2054687 := bstep (se 1 (by rfl) ⟨1541015, by rfl⟩ : syracuseStep 2054687 = 3082031) B3082031
theorem B3082037 : Blo 2053435 3082037 := bbase (se 5 (by rfl) ⟨144470, by rfl⟩ : syracuseStep 3082037 = 288941) (by norm_num)
theorem B2054691 : Blo 2053435 2054691 := bstep (se 1 (by rfl) ⟨1541018, by rfl⟩ : syracuseStep 2054691 = 3082037) B3082037
theorem B5200949 : Blo 2053435 5200949 := bbase (se 5 (by rfl) ⟨243794, by rfl⟩ : syracuseStep 5200949 = 487589) (by norm_num)
theorem B3467299 : Blo 2053435 3467299 := bstep (se 1 (by rfl) ⟨2600474, by rfl⟩ : syracuseStep 3467299 = 5200949) B5200949
theorem B4623065 : Blo 2053435 4623065 := bstep (se 2 (by rfl) ⟨1733649, by rfl⟩ : syracuseStep 4623065 = 3467299) B3467299
theorem B3082043 : Blo 2053435 3082043 := bstep (se 1 (by rfl) ⟨2311532, by rfl⟩ : syracuseStep 3082043 = 4623065) B4623065
theorem B2054695 : Blo 2053435 2054695 := bstep (se 1 (by rfl) ⟨1541021, by rfl⟩ : syracuseStep 2054695 = 3082043) B3082043
theorem B2311537 : Blo 2053435 2311537 := bbase (se 2 (by rfl) ⟨866826, by rfl⟩ : syracuseStep 2311537 = 1733653) (by norm_num)
theorem B3082049 : Blo 2053435 3082049 := bstep (se 2 (by rfl) ⟨1155768, by rfl⟩ : syracuseStep 3082049 = 2311537) B2311537
theorem B2054699 : Blo 2053435 2054699 := bstep (se 1 (by rfl) ⟨1541024, by rfl⟩ : syracuseStep 2054699 = 3082049) B3082049
theorem B10543861 : Blo 2053435 10543861 := bbase (se 5 (by rfl) ⟨494243, by rfl⟩ : syracuseStep 10543861 = 988487) (by norm_num)
theorem B14058481 : Blo 2053435 14058481 := bstep (se 2 (by rfl) ⟨5271930, by rfl⟩ : syracuseStep 14058481 = 10543861) B10543861
theorem B18744641 : Blo 2053435 18744641 := bstep (se 2 (by rfl) ⟨7029240, by rfl⟩ : syracuseStep 18744641 = 14058481) B14058481
theorem B12496427 : Blo 2053435 12496427 := bstep (se 1 (by rfl) ⟨9372320, by rfl⟩ : syracuseStep 12496427 = 18744641) B18744641
theorem B8330951 : Blo 2053435 8330951 := bstep (se 1 (by rfl) ⟨6248213, by rfl⟩ : syracuseStep 8330951 = 12496427) B12496427
theorem B5553967 : Blo 2053435 5553967 := bstep (se 1 (by rfl) ⟨4165475, by rfl⟩ : syracuseStep 5553967 = 8330951) B8330951
theorem B7405289 : Blo 2053435 7405289 := bstep (se 2 (by rfl) ⟨2776983, by rfl⟩ : syracuseStep 7405289 = 5553967) B5553967
theorem B4936859 : Blo 2053435 4936859 := bstep (se 1 (by rfl) ⟨3702644, by rfl⟩ : syracuseStep 4936859 = 7405289) B7405289
theorem B3291239 : Blo 2053435 3291239 := bstep (se 1 (by rfl) ⟨2468429, by rfl⟩ : syracuseStep 3291239 = 4936859) B4936859
theorem B8776637 : Blo 2053435 8776637 := bstep (se 3 (by rfl) ⟨1645619, by rfl⟩ : syracuseStep 8776637 = 3291239) B3291239
theorem B5851091 : Blo 2053435 5851091 := bstep (se 1 (by rfl) ⟨4388318, by rfl⟩ : syracuseStep 5851091 = 8776637) B8776637
theorem B3900727 : Blo 2053435 3900727 := bstep (se 1 (by rfl) ⟨2925545, by rfl⟩ : syracuseStep 3900727 = 5851091) B5851091
theorem B5200969 : Blo 2053435 5200969 := bstep (se 2 (by rfl) ⟨1950363, by rfl⟩ : syracuseStep 5200969 = 3900727) B3900727
theorem B6934625 : Blo 2053435 6934625 := bstep (se 2 (by rfl) ⟨2600484, by rfl⟩ : syracuseStep 6934625 = 5200969) B5200969
theorem B4623083 : Blo 2053435 4623083 := bstep (se 1 (by rfl) ⟨3467312, by rfl⟩ : syracuseStep 4623083 = 6934625) B6934625
theorem B3082055 : Blo 2053435 3082055 := bstep (se 1 (by rfl) ⟨2311541, by rfl⟩ : syracuseStep 3082055 = 4623083) B4623083
theorem B2054703 : Blo 2053435 2054703 := bstep (se 1 (by rfl) ⟨1541027, by rfl⟩ : syracuseStep 2054703 = 3082055) B3082055
theorem B3082061 : Blo 2053435 3082061 := bbase (se 3 (by rfl) ⟨577886, by rfl⟩ : syracuseStep 3082061 = 1155773) (by norm_num)
theorem B2054707 : Blo 2053435 2054707 := bstep (se 1 (by rfl) ⟨1541030, by rfl⟩ : syracuseStep 2054707 = 3082061) B3082061
theorem B4623101 : Blo 2053435 4623101 := bbase (se 3 (by rfl) ⟨866831, by rfl⟩ : syracuseStep 4623101 = 1733663) (by norm_num)
theorem B3082067 : Blo 2053435 3082067 := bstep (se 1 (by rfl) ⟨2311550, by rfl⟩ : syracuseStep 3082067 = 4623101) B4623101
theorem B2054711 : Blo 2053435 2054711 := bstep (se 1 (by rfl) ⟨1541033, by rfl⟩ : syracuseStep 2054711 = 3082067) B3082067
theorem B3467333 : Blo 2053435 3467333 := bbase (se 4 (by rfl) ⟨325062, by rfl⟩ : syracuseStep 3467333 = 650125) (by norm_num)
theorem B2311555 : Blo 2053435 2311555 := bstep (se 1 (by rfl) ⟨1733666, by rfl⟩ : syracuseStep 2311555 = 3467333) B3467333
theorem B3082073 : Blo 2053435 3082073 := bstep (se 2 (by rfl) ⟨1155777, by rfl⟩ : syracuseStep 3082073 = 2311555) B2311555
theorem B2054715 : Blo 2053435 2054715 := bstep (se 1 (by rfl) ⟨1541036, by rfl⟩ : syracuseStep 2054715 = 3082073) B3082073
theorem B15603029 : Blo 2053435 15603029 := bbase (se 14 (by rfl) ⟨1428, by rfl⟩ : syracuseStep 15603029 = 2857) (by norm_num)
theorem B10402019 : Blo 2053435 10402019 := bstep (se 1 (by rfl) ⟨7801514, by rfl⟩ : syracuseStep 10402019 = 15603029) B15603029
theorem B6934679 : Blo 2053435 6934679 := bstep (se 1 (by rfl) ⟨5201009, by rfl⟩ : syracuseStep 6934679 = 10402019) B10402019
theorem B4623119 : Blo 2053435 4623119 := bstep (se 1 (by rfl) ⟨3467339, by rfl⟩ : syracuseStep 4623119 = 6934679) B6934679
theorem B3082079 : Blo 2053435 3082079 := bstep (se 1 (by rfl) ⟨2311559, by rfl⟩ : syracuseStep 3082079 = 4623119) B4623119
theorem B2054719 : Blo 2053435 2054719 := bstep (se 1 (by rfl) ⟨1541039, by rfl⟩ : syracuseStep 2054719 = 3082079) B3082079
theorem B3082085 : Blo 2053435 3082085 := bbase (se 4 (by rfl) ⟨288945, by rfl⟩ : syracuseStep 3082085 = 577891) (by norm_num)
theorem B2054723 : Blo 2053435 2054723 := bstep (se 1 (by rfl) ⟨1541042, by rfl⟩ : syracuseStep 2054723 = 3082085) B3082085
theorem B3900773 : Blo 2053435 3900773 := bbase (se 4 (by rfl) ⟨365697, by rfl⟩ : syracuseStep 3900773 = 731395) (by norm_num)
theorem B2600515 : Blo 2053435 2600515 := bstep (se 1 (by rfl) ⟨1950386, by rfl⟩ : syracuseStep 2600515 = 3900773) B3900773
theorem B3467353 : Blo 2053435 3467353 := bstep (se 2 (by rfl) ⟨1300257, by rfl⟩ : syracuseStep 3467353 = 2600515) B2600515
theorem B4623137 : Blo 2053435 4623137 := bstep (se 2 (by rfl) ⟨1733676, by rfl⟩ : syracuseStep 4623137 = 3467353) B3467353
theorem B3082091 : Blo 2053435 3082091 := bstep (se 1 (by rfl) ⟨2311568, by rfl⟩ : syracuseStep 3082091 = 4623137) B4623137
theorem B2054727 : Blo 2053435 2054727 := bstep (se 1 (by rfl) ⟨1541045, by rfl⟩ : syracuseStep 2054727 = 3082091) B3082091
theorem B2311573 : Blo 2053435 2311573 := bbase (se 6 (by rfl) ⟨54177, by rfl⟩ : syracuseStep 2311573 = 108355) (by norm_num)
theorem B3082097 : Blo 2053435 3082097 := bstep (se 2 (by rfl) ⟨1155786, by rfl⟩ : syracuseStep 3082097 = 2311573) B2311573
theorem B2054731 : Blo 2053435 2054731 := bstep (se 1 (by rfl) ⟨1541048, by rfl⟩ : syracuseStep 2054731 = 3082097) B3082097
theorem B2600525 : Blo 2053435 2600525 := bbase (se 3 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 2600525 = 975197) (by norm_num)
theorem B6934733 : Blo 2053435 6934733 := bstep (se 3 (by rfl) ⟨1300262, by rfl⟩ : syracuseStep 6934733 = 2600525) B2600525
theorem B4623155 : Blo 2053435 4623155 := bstep (se 1 (by rfl) ⟨3467366, by rfl⟩ : syracuseStep 4623155 = 6934733) B6934733
theorem B3082103 : Blo 2053435 3082103 := bstep (se 1 (by rfl) ⟨2311577, by rfl⟩ : syracuseStep 3082103 = 4623155) B4623155
theorem B2054735 : Blo 2053435 2054735 := bstep (se 1 (by rfl) ⟨1541051, by rfl⟩ : syracuseStep 2054735 = 3082103) B3082103
theorem B3082109 : Blo 2053435 3082109 := bbase (se 3 (by rfl) ⟨577895, by rfl⟩ : syracuseStep 3082109 = 1155791) (by norm_num)
theorem B2054739 : Blo 2053435 2054739 := bstep (se 1 (by rfl) ⟨1541054, by rfl⟩ : syracuseStep 2054739 = 3082109) B3082109
theorem B4623173 : Blo 2053435 4623173 := bbase (se 4 (by rfl) ⟨433422, by rfl⟩ : syracuseStep 4623173 = 866845) (by norm_num)
theorem B3082115 : Blo 2053435 3082115 := bstep (se 1 (by rfl) ⟨2311586, by rfl⟩ : syracuseStep 3082115 = 4623173) B4623173
theorem B2054743 : Blo 2053435 2054743 := bstep (se 1 (by rfl) ⟨1541057, by rfl⟩ : syracuseStep 2054743 = 3082115) B3082115
theorem B4388413 : Blo 2053435 4388413 := bbase (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) (by norm_num)
theorem B5851217 : Blo 2053435 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B3900811 : Blo 2053435 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B5201081 : Blo 2053435 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B3467387 : Blo 2053435 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B2311591 : Blo 2053435 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B3082121 : Blo 2053435 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B2054747 : Blo 2053435 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B10402181 : Blo 2053435 10402181 := bbase (se 4 (by rfl) ⟨975204, by rfl⟩ : syracuseStep 10402181 = 1950409) (by norm_num)
theorem B6934787 : Blo 2053435 6934787 := bstep (se 1 (by rfl) ⟨5201090, by rfl⟩ : syracuseStep 6934787 = 10402181) B10402181
theorem B4623191 : Blo 2053435 4623191 := bstep (se 1 (by rfl) ⟨3467393, by rfl⟩ : syracuseStep 4623191 = 6934787) B6934787
theorem B3082127 : Blo 2053435 3082127 := bstep (se 1 (by rfl) ⟨2311595, by rfl⟩ : syracuseStep 3082127 = 4623191) B4623191
theorem B2054751 : Blo 2053435 2054751 := bstep (se 1 (by rfl) ⟨1541063, by rfl⟩ : syracuseStep 2054751 = 3082127) B3082127
theorem B3082133 : Blo 2053435 3082133 := bbase (se 6 (by rfl) ⟨72237, by rfl⟩ : syracuseStep 3082133 = 144475) (by norm_num)
theorem B2054755 : Blo 2053435 2054755 := bstep (se 1 (by rfl) ⟨1541066, by rfl⟩ : syracuseStep 2054755 = 3082133) B3082133
theorem B2468497 : Blo 2053435 2468497 := bbase (se 2 (by rfl) ⟨925686, by rfl⟩ : syracuseStep 2468497 = 1851373) (by norm_num)
theorem B3291329 : Blo 2053435 3291329 := bstep (se 2 (by rfl) ⟨1234248, by rfl⟩ : syracuseStep 3291329 = 2468497) B2468497
theorem B2194219 : Blo 2053435 2194219 := bstep (se 1 (by rfl) ⟨1645664, by rfl⟩ : syracuseStep 2194219 = 3291329) B3291329
theorem B11702501 : Blo 2053435 11702501 := bstep (se 4 (by rfl) ⟨1097109, by rfl⟩ : syracuseStep 11702501 = 2194219) B2194219
theorem B7801667 : Blo 2053435 7801667 := bstep (se 1 (by rfl) ⟨5851250, by rfl⟩ : syracuseStep 7801667 = 11702501) B11702501
theorem B5201111 : Blo 2053435 5201111 := bstep (se 1 (by rfl) ⟨3900833, by rfl⟩ : syracuseStep 5201111 = 7801667) B7801667
theorem B3467407 : Blo 2053435 3467407 := bstep (se 1 (by rfl) ⟨2600555, by rfl⟩ : syracuseStep 3467407 = 5201111) B5201111
theorem B4623209 : Blo 2053435 4623209 := bstep (se 2 (by rfl) ⟨1733703, by rfl⟩ : syracuseStep 4623209 = 3467407) B3467407
theorem B3082139 : Blo 2053435 3082139 := bstep (se 1 (by rfl) ⟨2311604, by rfl⟩ : syracuseStep 3082139 = 4623209) B4623209
theorem B2054759 : Blo 2053435 2054759 := bstep (se 1 (by rfl) ⟨1541069, by rfl⟩ : syracuseStep 2054759 = 3082139) B3082139
theorem B2311609 : Blo 2053435 2311609 := bbase (se 2 (by rfl) ⟨866853, by rfl⟩ : syracuseStep 2311609 = 1733707) (by norm_num)
theorem B3082145 : Blo 2053435 3082145 := bstep (se 2 (by rfl) ⟨1155804, by rfl⟩ : syracuseStep 3082145 = 2311609) B2311609
theorem B2054763 : Blo 2053435 2054763 := bstep (se 1 (by rfl) ⟨1541072, by rfl⟩ : syracuseStep 2054763 = 3082145) B3082145
theorem B8896661 : Blo 2053435 8896661 := bbase (se 6 (by rfl) ⟨208515, by rfl⟩ : syracuseStep 8896661 = 417031) (by norm_num)
theorem B5931107 : Blo 2053435 5931107 := bstep (se 1 (by rfl) ⟨4448330, by rfl⟩ : syracuseStep 5931107 = 8896661) B8896661
theorem B3954071 : Blo 2053435 3954071 := bstep (se 1 (by rfl) ⟨2965553, by rfl⟩ : syracuseStep 3954071 = 5931107) B5931107
theorem B2636047 : Blo 2053435 2636047 := bstep (se 1 (by rfl) ⟨1977035, by rfl⟩ : syracuseStep 2636047 = 3954071) B3954071
theorem B14058917 : Blo 2053435 14058917 := bstep (se 4 (by rfl) ⟨1318023, by rfl⟩ : syracuseStep 14058917 = 2636047) B2636047
theorem B9372611 : Blo 2053435 9372611 := bstep (se 1 (by rfl) ⟨7029458, by rfl⟩ : syracuseStep 9372611 = 14058917) B14058917
theorem B24993629 : Blo 2053435 24993629 := bstep (se 3 (by rfl) ⟨4686305, by rfl⟩ : syracuseStep 24993629 = 9372611) B9372611
theorem B16662419 : Blo 2053435 16662419 := bstep (se 1 (by rfl) ⟨12496814, by rfl⟩ : syracuseStep 16662419 = 24993629) B24993629
theorem B11108279 : Blo 2053435 11108279 := bstep (se 1 (by rfl) ⟨8331209, by rfl⟩ : syracuseStep 11108279 = 16662419) B16662419
theorem B7405519 : Blo 2053435 7405519 := bstep (se 1 (by rfl) ⟨5554139, by rfl⟩ : syracuseStep 7405519 = 11108279) B11108279
theorem B9874025 : Blo 2053435 9874025 := bstep (se 2 (by rfl) ⟨3702759, by rfl⟩ : syracuseStep 9874025 = 7405519) B7405519
theorem B6582683 : Blo 2053435 6582683 := bstep (se 1 (by rfl) ⟨4937012, by rfl⟩ : syracuseStep 6582683 = 9874025) B9874025
theorem B4388455 : Blo 2053435 4388455 := bstep (se 1 (by rfl) ⟨3291341, by rfl⟩ : syracuseStep 4388455 = 6582683) B6582683
theorem B5851273 : Blo 2053435 5851273 := bstep (se 2 (by rfl) ⟨2194227, by rfl⟩ : syracuseStep 5851273 = 4388455) B4388455
theorem B7801697 : Blo 2053435 7801697 := bstep (se 2 (by rfl) ⟨2925636, by rfl⟩ : syracuseStep 7801697 = 5851273) B5851273
theorem B5201131 : Blo 2053435 5201131 := bstep (se 1 (by rfl) ⟨3900848, by rfl⟩ : syracuseStep 5201131 = 7801697) B7801697
theorem B6934841 : Blo 2053435 6934841 := bstep (se 2 (by rfl) ⟨2600565, by rfl⟩ : syracuseStep 6934841 = 5201131) B5201131
theorem B4623227 : Blo 2053435 4623227 := bstep (se 1 (by rfl) ⟨3467420, by rfl⟩ : syracuseStep 4623227 = 6934841) B6934841
theorem B3082151 : Blo 2053435 3082151 := bstep (se 1 (by rfl) ⟨2311613, by rfl⟩ : syracuseStep 3082151 = 4623227) B4623227
theorem B2054767 : Blo 2053435 2054767 := bstep (se 1 (by rfl) ⟨1541075, by rfl⟩ : syracuseStep 2054767 = 3082151) B3082151
theorem B3082157 : Blo 2053435 3082157 := bbase (se 3 (by rfl) ⟨577904, by rfl⟩ : syracuseStep 3082157 = 1155809) (by norm_num)
theorem B2054771 : Blo 2053435 2054771 := bstep (se 1 (by rfl) ⟨1541078, by rfl⟩ : syracuseStep 2054771 = 3082157) B3082157
theorem B4623245 : Blo 2053435 4623245 := bbase (se 3 (by rfl) ⟨866858, by rfl⟩ : syracuseStep 4623245 = 1733717) (by norm_num)
theorem B3082163 : Blo 2053435 3082163 := bstep (se 1 (by rfl) ⟨2311622, by rfl⟩ : syracuseStep 3082163 = 4623245) B4623245
theorem B2054775 : Blo 2053435 2054775 := bstep (se 1 (by rfl) ⟨1541081, by rfl⟩ : syracuseStep 2054775 = 3082163) B3082163
theorem B2600581 : Blo 2053435 2600581 := bbase (se 4 (by rfl) ⟨243804, by rfl⟩ : syracuseStep 2600581 = 487609) (by norm_num)
theorem B3467441 : Blo 2053435 3467441 := bstep (se 2 (by rfl) ⟨1300290, by rfl⟩ : syracuseStep 3467441 = 2600581) B2600581
theorem B2311627 : Blo 2053435 2311627 := bstep (se 1 (by rfl) ⟨1733720, by rfl⟩ : syracuseStep 2311627 = 3467441) B3467441
theorem B3082169 : Blo 2053435 3082169 := bstep (se 2 (by rfl) ⟨1155813, by rfl⟩ : syracuseStep 3082169 = 2311627) B2311627
theorem B2054779 : Blo 2053435 2054779 := bstep (se 1 (by rfl) ⟨1541084, by rfl⟩ : syracuseStep 2054779 = 3082169) B3082169
theorem B2468525 : Blo 2053435 2468525 := bbase (se 3 (by rfl) ⟨462848, by rfl⟩ : syracuseStep 2468525 = 925697) (by norm_num)
theorem B26330933 : Blo 2053435 26330933 := bstep (se 5 (by rfl) ⟨1234262, by rfl⟩ : syracuseStep 26330933 = 2468525) B2468525
theorem B17553955 : Blo 2053435 17553955 := bstep (se 1 (by rfl) ⟨13165466, by rfl⟩ : syracuseStep 17553955 = 26330933) B26330933
theorem B23405273 : Blo 2053435 23405273 := bstep (se 2 (by rfl) ⟨8776977, by rfl⟩ : syracuseStep 23405273 = 17553955) B17553955
theorem B15603515 : Blo 2053435 15603515 := bstep (se 1 (by rfl) ⟨11702636, by rfl⟩ : syracuseStep 15603515 = 23405273) B23405273
theorem B10402343 : Blo 2053435 10402343 := bstep (se 1 (by rfl) ⟨7801757, by rfl⟩ : syracuseStep 10402343 = 15603515) B15603515
theorem B6934895 : Blo 2053435 6934895 := bstep (se 1 (by rfl) ⟨5201171, by rfl⟩ : syracuseStep 6934895 = 10402343) B10402343
theorem B4623263 : Blo 2053435 4623263 := bstep (se 1 (by rfl) ⟨3467447, by rfl⟩ : syracuseStep 4623263 = 6934895) B6934895
theorem B3082175 : Blo 2053435 3082175 := bstep (se 1 (by rfl) ⟨2311631, by rfl⟩ : syracuseStep 3082175 = 4623263) B4623263
theorem B2054783 : Blo 2053435 2054783 := bstep (se 1 (by rfl) ⟨1541087, by rfl⟩ : syracuseStep 2054783 = 3082175) B3082175
theorem B3082181 : Blo 2053435 3082181 := bbase (se 4 (by rfl) ⟨288954, by rfl⟩ : syracuseStep 3082181 = 577909) (by norm_num)
theorem B2054787 : Blo 2053435 2054787 := bstep (se 1 (by rfl) ⟨1541090, by rfl⟩ : syracuseStep 2054787 = 3082181) B3082181
theorem B3467461 : Blo 2053435 3467461 := bbase (se 4 (by rfl) ⟨325074, by rfl⟩ : syracuseStep 3467461 = 650149) (by norm_num)
theorem B4623281 : Blo 2053435 4623281 := bstep (se 2 (by rfl) ⟨1733730, by rfl⟩ : syracuseStep 4623281 = 3467461) B3467461
theorem B3082187 : Blo 2053435 3082187 := bstep (se 1 (by rfl) ⟨2311640, by rfl⟩ : syracuseStep 3082187 = 4623281) B4623281
theorem B2054791 : Blo 2053435 2054791 := bstep (se 1 (by rfl) ⟨1541093, by rfl⟩ : syracuseStep 2054791 = 3082187) B3082187
theorem B2311645 : Blo 2053435 2311645 := bbase (se 3 (by rfl) ⟨433433, by rfl⟩ : syracuseStep 2311645 = 866867) (by norm_num)
theorem B3082193 : Blo 2053435 3082193 := bstep (se 2 (by rfl) ⟨1155822, by rfl⟩ : syracuseStep 3082193 = 2311645) B2311645
theorem B2054795 : Blo 2053435 2054795 := bstep (se 1 (by rfl) ⟨1541096, by rfl⟩ : syracuseStep 2054795 = 3082193) B3082193
theorem B6934949 : Blo 2053435 6934949 := bbase (se 4 (by rfl) ⟨650151, by rfl⟩ : syracuseStep 6934949 = 1300303) (by norm_num)
theorem B4623299 : Blo 2053435 4623299 := bstep (se 1 (by rfl) ⟨3467474, by rfl⟩ : syracuseStep 4623299 = 6934949) B6934949
theorem B3082199 : Blo 2053435 3082199 := bstep (se 1 (by rfl) ⟨2311649, by rfl⟩ : syracuseStep 3082199 = 4623299) B4623299
theorem B2054799 : Blo 2053435 2054799 := bstep (se 1 (by rfl) ⟨1541099, by rfl⟩ : syracuseStep 2054799 = 3082199) B3082199
theorem B3082205 : Blo 2053435 3082205 := bbase (se 3 (by rfl) ⟨577913, by rfl⟩ : syracuseStep 3082205 = 1155827) (by norm_num)
theorem B2054803 : Blo 2053435 2054803 := bstep (se 1 (by rfl) ⟨1541102, by rfl⟩ : syracuseStep 2054803 = 3082205) B3082205
theorem B4623317 : Blo 2053435 4623317 := bbase (se 7 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 4623317 = 108359) (by norm_num)
theorem B3082211 : Blo 2053435 3082211 := bstep (se 1 (by rfl) ⟨2311658, by rfl⟩ : syracuseStep 3082211 = 4623317) B4623317
theorem B2054807 : Blo 2053435 2054807 := bstep (se 1 (by rfl) ⟨1541105, by rfl⟩ : syracuseStep 2054807 = 3082211) B3082211
theorem B8896853 : Blo 2053435 8896853 := bbase (se 10 (by rfl) ⟨13032, by rfl⟩ : syracuseStep 8896853 = 26065) (by norm_num)
theorem B5931235 : Blo 2053435 5931235 := bstep (se 1 (by rfl) ⟨4448426, by rfl⟩ : syracuseStep 5931235 = 8896853) B8896853
theorem B7908313 : Blo 2053435 7908313 := bstep (se 2 (by rfl) ⟨2965617, by rfl⟩ : syracuseStep 7908313 = 5931235) B5931235
theorem B10544417 : Blo 2053435 10544417 := bstep (se 2 (by rfl) ⟨3954156, by rfl⟩ : syracuseStep 10544417 = 7908313) B7908313
theorem B7029611 : Blo 2053435 7029611 := bstep (se 1 (by rfl) ⟨5272208, by rfl⟩ : syracuseStep 7029611 = 10544417) B10544417
theorem B4686407 : Blo 2053435 4686407 := bstep (se 1 (by rfl) ⟨3514805, by rfl⟩ : syracuseStep 4686407 = 7029611) B7029611
theorem B3124271 : Blo 2053435 3124271 := bstep (se 1 (by rfl) ⟨2343203, by rfl⟩ : syracuseStep 3124271 = 4686407) B4686407
theorem B8331389 : Blo 2053435 8331389 := bstep (se 3 (by rfl) ⟨1562135, by rfl⟩ : syracuseStep 8331389 = 3124271) B3124271
theorem B5554259 : Blo 2053435 5554259 := bstep (se 1 (by rfl) ⟨4165694, by rfl⟩ : syracuseStep 5554259 = 8331389) B8331389
theorem B3702839 : Blo 2053435 3702839 := bstep (se 1 (by rfl) ⟨2777129, by rfl⟩ : syracuseStep 3702839 = 5554259) B5554259
theorem B9874237 : Blo 2053435 9874237 := bstep (se 3 (by rfl) ⟨1851419, by rfl⟩ : syracuseStep 9874237 = 3702839) B3702839
theorem B13165649 : Blo 2053435 13165649 := bstep (se 2 (by rfl) ⟨4937118, by rfl⟩ : syracuseStep 13165649 = 9874237) B9874237
theorem B8777099 : Blo 2053435 8777099 := bstep (se 1 (by rfl) ⟨6582824, by rfl⟩ : syracuseStep 8777099 = 13165649) B13165649
theorem B5851399 : Blo 2053435 5851399 := bstep (se 1 (by rfl) ⟨4388549, by rfl⟩ : syracuseStep 5851399 = 8777099) B8777099
theorem B7801865 : Blo 2053435 7801865 := bstep (se 2 (by rfl) ⟨2925699, by rfl⟩ : syracuseStep 7801865 = 5851399) B5851399
theorem B5201243 : Blo 2053435 5201243 := bstep (se 1 (by rfl) ⟨3900932, by rfl⟩ : syracuseStep 5201243 = 7801865) B7801865
theorem B3467495 : Blo 2053435 3467495 := bstep (se 1 (by rfl) ⟨2600621, by rfl⟩ : syracuseStep 3467495 = 5201243) B5201243
theorem B2311663 : Blo 2053435 2311663 := bstep (se 1 (by rfl) ⟨1733747, by rfl⟩ : syracuseStep 2311663 = 3467495) B3467495
theorem B3082217 : Blo 2053435 3082217 := bstep (se 2 (by rfl) ⟨1155831, by rfl⟩ : syracuseStep 3082217 = 2311663) B2311663
theorem B2054811 : Blo 2053435 2054811 := bstep (se 1 (by rfl) ⟨1541108, by rfl⟩ : syracuseStep 2054811 = 3082217) B3082217
theorem B17554229 : Blo 2053435 17554229 := bbase (se 5 (by rfl) ⟨822854, by rfl⟩ : syracuseStep 17554229 = 1645709) (by norm_num)
theorem B11702819 : Blo 2053435 11702819 := bstep (se 1 (by rfl) ⟨8777114, by rfl⟩ : syracuseStep 11702819 = 17554229) B17554229
theorem B7801879 : Blo 2053435 7801879 := bstep (se 1 (by rfl) ⟨5851409, by rfl⟩ : syracuseStep 7801879 = 11702819) B11702819
theorem B10402505 : Blo 2053435 10402505 := bstep (se 2 (by rfl) ⟨3900939, by rfl⟩ : syracuseStep 10402505 = 7801879) B7801879
theorem B6935003 : Blo 2053435 6935003 := bstep (se 1 (by rfl) ⟨5201252, by rfl⟩ : syracuseStep 6935003 = 10402505) B10402505
theorem B4623335 : Blo 2053435 4623335 := bstep (se 1 (by rfl) ⟨3467501, by rfl⟩ : syracuseStep 4623335 = 6935003) B6935003
theorem B3082223 : Blo 2053435 3082223 := bstep (se 1 (by rfl) ⟨2311667, by rfl⟩ : syracuseStep 3082223 = 4623335) B4623335
theorem B2054815 : Blo 2053435 2054815 := bstep (se 1 (by rfl) ⟨1541111, by rfl⟩ : syracuseStep 2054815 = 3082223) B3082223
theorem B3082229 : Blo 2053435 3082229 := bbase (se 5 (by rfl) ⟨144479, by rfl⟩ : syracuseStep 3082229 = 288959) (by norm_num)
theorem B2054819 : Blo 2053435 2054819 := bstep (se 1 (by rfl) ⟨1541114, by rfl⟩ : syracuseStep 2054819 = 3082229) B3082229
theorem B2343217 : Blo 2053435 2343217 := bbase (se 2 (by rfl) ⟨878706, by rfl⟩ : syracuseStep 2343217 = 1757413) (by norm_num)
theorem B3124289 : Blo 2053435 3124289 := bstep (se 2 (by rfl) ⟨1171608, by rfl⟩ : syracuseStep 3124289 = 2343217) B2343217
theorem B8331437 : Blo 2053435 8331437 := bstep (se 3 (by rfl) ⟨1562144, by rfl⟩ : syracuseStep 8331437 = 3124289) B3124289
theorem B22217165 : Blo 2053435 22217165 := bstep (se 3 (by rfl) ⟨4165718, by rfl⟩ : syracuseStep 22217165 = 8331437) B8331437
theorem B14811443 : Blo 2053435 14811443 := bstep (se 1 (by rfl) ⟨11108582, by rfl⟩ : syracuseStep 14811443 = 22217165) B22217165
theorem B9874295 : Blo 2053435 9874295 := bstep (se 1 (by rfl) ⟨7405721, by rfl⟩ : syracuseStep 9874295 = 14811443) B14811443
theorem B6582863 : Blo 2053435 6582863 := bstep (se 1 (by rfl) ⟨4937147, by rfl⟩ : syracuseStep 6582863 = 9874295) B9874295
theorem B4388575 : Blo 2053435 4388575 := bstep (se 1 (by rfl) ⟨3291431, by rfl⟩ : syracuseStep 4388575 = 6582863) B6582863
theorem B5851433 : Blo 2053435 5851433 := bstep (se 2 (by rfl) ⟨2194287, by rfl⟩ : syracuseStep 5851433 = 4388575) B4388575
theorem B3900955 : Blo 2053435 3900955 := bstep (se 1 (by rfl) ⟨2925716, by rfl⟩ : syracuseStep 3900955 = 5851433) B5851433
theorem B5201273 : Blo 2053435 5201273 := bstep (se 2 (by rfl) ⟨1950477, by rfl⟩ : syracuseStep 5201273 = 3900955) B3900955
theorem B3467515 : Blo 2053435 3467515 := bstep (se 1 (by rfl) ⟨2600636, by rfl⟩ : syracuseStep 3467515 = 5201273) B5201273
theorem B4623353 : Blo 2053435 4623353 := bstep (se 2 (by rfl) ⟨1733757, by rfl⟩ : syracuseStep 4623353 = 3467515) B3467515
theorem B3082235 : Blo 2053435 3082235 := bstep (se 1 (by rfl) ⟨2311676, by rfl⟩ : syracuseStep 3082235 = 4623353) B4623353
theorem B2054823 : Blo 2053435 2054823 := bstep (se 1 (by rfl) ⟨1541117, by rfl⟩ : syracuseStep 2054823 = 3082235) B3082235
theorem B2311681 : Blo 2053435 2311681 := bbase (se 2 (by rfl) ⟨866880, by rfl⟩ : syracuseStep 2311681 = 1733761) (by norm_num)
theorem B3082241 : Blo 2053435 3082241 := bstep (se 2 (by rfl) ⟨1155840, by rfl⟩ : syracuseStep 3082241 = 2311681) B2311681
theorem B2054827 : Blo 2053435 2054827 := bstep (se 1 (by rfl) ⟨1541120, by rfl⟩ : syracuseStep 2054827 = 3082241) B3082241
theorem B5201293 : Blo 2053435 5201293 := bbase (se 3 (by rfl) ⟨975242, by rfl⟩ : syracuseStep 5201293 = 1950485) (by norm_num)
theorem B6935057 : Blo 2053435 6935057 := bstep (se 2 (by rfl) ⟨2600646, by rfl⟩ : syracuseStep 6935057 = 5201293) B5201293
theorem B4623371 : Blo 2053435 4623371 := bstep (se 1 (by rfl) ⟨3467528, by rfl⟩ : syracuseStep 4623371 = 6935057) B6935057
theorem B3082247 : Blo 2053435 3082247 := bstep (se 1 (by rfl) ⟨2311685, by rfl⟩ : syracuseStep 3082247 = 4623371) B4623371
theorem B2054831 : Blo 2053435 2054831 := bstep (se 1 (by rfl) ⟨1541123, by rfl⟩ : syracuseStep 2054831 = 3082247) B3082247
theorem B3082253 : Blo 2053435 3082253 := bbase (se 3 (by rfl) ⟨577922, by rfl⟩ : syracuseStep 3082253 = 1155845) (by norm_num)
theorem B2054835 : Blo 2053435 2054835 := bstep (se 1 (by rfl) ⟨1541126, by rfl⟩ : syracuseStep 2054835 = 3082253) B3082253
theorem B4623389 : Blo 2053435 4623389 := bbase (se 3 (by rfl) ⟨866885, by rfl⟩ : syracuseStep 4623389 = 1733771) (by norm_num)
theorem B3082259 : Blo 2053435 3082259 := bstep (se 1 (by rfl) ⟨2311694, by rfl⟩ : syracuseStep 3082259 = 4623389) B4623389
theorem B2054839 : Blo 2053435 2054839 := bstep (se 1 (by rfl) ⟨1541129, by rfl⟩ : syracuseStep 2054839 = 3082259) B3082259
theorem B3467549 : Blo 2053435 3467549 := bbase (se 3 (by rfl) ⟨650165, by rfl⟩ : syracuseStep 3467549 = 1300331) (by norm_num)
theorem B2311699 : Blo 2053435 2311699 := bstep (se 1 (by rfl) ⟨1733774, by rfl⟩ : syracuseStep 2311699 = 3467549) B3467549
theorem B3082265 : Blo 2053435 3082265 := bstep (se 2 (by rfl) ⟨1155849, by rfl⟩ : syracuseStep 3082265 = 2311699) B2311699
theorem B2054843 : Blo 2053435 2054843 := bstep (se 1 (by rfl) ⟨1541132, by rfl⟩ : syracuseStep 2054843 = 3082265) B3082265
theorem B13165877 : Blo 2053435 13165877 := bbase (se 5 (by rfl) ⟨617150, by rfl⟩ : syracuseStep 13165877 = 1234301) (by norm_num)
theorem B8777251 : Blo 2053435 8777251 := bstep (se 1 (by rfl) ⟨6582938, by rfl⟩ : syracuseStep 8777251 = 13165877) B13165877
theorem B11703001 : Blo 2053435 11703001 := bstep (se 2 (by rfl) ⟨4388625, by rfl⟩ : syracuseStep 11703001 = 8777251) B8777251
theorem B15604001 : Blo 2053435 15604001 := bstep (se 2 (by rfl) ⟨5851500, by rfl⟩ : syracuseStep 15604001 = 11703001) B11703001
theorem B10402667 : Blo 2053435 10402667 := bstep (se 1 (by rfl) ⟨7802000, by rfl⟩ : syracuseStep 10402667 = 15604001) B15604001
theorem B6935111 : Blo 2053435 6935111 := bstep (se 1 (by rfl) ⟨5201333, by rfl⟩ : syracuseStep 6935111 = 10402667) B10402667
theorem B4623407 : Blo 2053435 4623407 := bstep (se 1 (by rfl) ⟨3467555, by rfl⟩ : syracuseStep 4623407 = 6935111) B6935111
theorem B3082271 : Blo 2053435 3082271 := bstep (se 1 (by rfl) ⟨2311703, by rfl⟩ : syracuseStep 3082271 = 4623407) B4623407
theorem B2054847 : Blo 2053435 2054847 := bstep (se 1 (by rfl) ⟨1541135, by rfl⟩ : syracuseStep 2054847 = 3082271) B3082271
theorem B3082277 : Blo 2053435 3082277 := bbase (se 4 (by rfl) ⟨288963, by rfl⟩ : syracuseStep 3082277 = 577927) (by norm_num)
theorem B2054851 : Blo 2053435 2054851 := bstep (se 1 (by rfl) ⟨1541138, by rfl⟩ : syracuseStep 2054851 = 3082277) B3082277
theorem B2600677 : Blo 2053435 2600677 := bbase (se 4 (by rfl) ⟨243813, by rfl⟩ : syracuseStep 2600677 = 487627) (by norm_num)
theorem B3467569 : Blo 2053435 3467569 := bstep (se 2 (by rfl) ⟨1300338, by rfl⟩ : syracuseStep 3467569 = 2600677) B2600677
theorem B4623425 : Blo 2053435 4623425 := bstep (se 2 (by rfl) ⟨1733784, by rfl⟩ : syracuseStep 4623425 = 3467569) B3467569
theorem B3082283 : Blo 2053435 3082283 := bstep (se 1 (by rfl) ⟨2311712, by rfl⟩ : syracuseStep 3082283 = 4623425) B4623425
theorem B2054855 : Blo 2053435 2054855 := bstep (se 1 (by rfl) ⟨1541141, by rfl⟩ : syracuseStep 2054855 = 3082283) B3082283
theorem B2311717 : Blo 2053435 2311717 := bbase (se 4 (by rfl) ⟨216723, by rfl⟩ : syracuseStep 2311717 = 433447) (by norm_num)
theorem B3082289 : Blo 2053435 3082289 := bstep (se 2 (by rfl) ⟨1155858, by rfl⟩ : syracuseStep 3082289 = 2311717) B2311717
theorem B2054859 : Blo 2053435 2054859 := bstep (se 1 (by rfl) ⟨1541144, by rfl⟩ : syracuseStep 2054859 = 3082289) B3082289
theorem B26442197 : Blo 2053435 26442197 := bbase (se 7 (by rfl) ⟨309869, by rfl⟩ : syracuseStep 26442197 = 619739) (by norm_num)
theorem B17628131 : Blo 2053435 17628131 := bstep (se 1 (by rfl) ⟨13221098, by rfl⟩ : syracuseStep 17628131 = 26442197) B26442197
theorem B11752087 : Blo 2053435 11752087 := bstep (se 1 (by rfl) ⟨8814065, by rfl⟩ : syracuseStep 11752087 = 17628131) B17628131
theorem B15669449 : Blo 2053435 15669449 := bstep (se 2 (by rfl) ⟨5876043, by rfl⟩ : syracuseStep 15669449 = 11752087) B11752087
theorem B10446299 : Blo 2053435 10446299 := bstep (se 1 (by rfl) ⟨7834724, by rfl⟩ : syracuseStep 10446299 = 15669449) B15669449
theorem B6964199 : Blo 2053435 6964199 := bstep (se 1 (by rfl) ⟨5223149, by rfl⟩ : syracuseStep 6964199 = 10446299) B10446299
theorem B74284789 : Blo 2053435 74284789 := bstep (se 5 (by rfl) ⟨3482099, by rfl⟩ : syracuseStep 74284789 = 6964199) B6964199
theorem B99046385 : Blo 2053435 99046385 := bstep (se 2 (by rfl) ⟨37142394, by rfl⟩ : syracuseStep 99046385 = 74284789) B74284789
theorem B66030923 : Blo 2053435 66030923 := bstep (se 1 (by rfl) ⟨49523192, by rfl⟩ : syracuseStep 66030923 = 99046385) B99046385
theorem B44020615 : Blo 2053435 44020615 := bstep (se 1 (by rfl) ⟨33015461, by rfl⟩ : syracuseStep 44020615 = 66030923) B66030923
theorem B58694153 : Blo 2053435 58694153 := bstep (se 2 (by rfl) ⟨22010307, by rfl⟩ : syracuseStep 58694153 = 44020615) B44020615
theorem B156517741 : Blo 2053435 156517741 := bstep (se 3 (by rfl) ⟨29347076, by rfl⟩ : syracuseStep 156517741 = 58694153) B58694153
theorem B208690321 : Blo 2053435 208690321 := bstep (se 2 (by rfl) ⟨78258870, by rfl⟩ : syracuseStep 208690321 = 156517741) B156517741
theorem B4452060181 : Blo 2053435 4452060181 := bstep (se 6 (by rfl) ⟨104345160, by rfl⟩ : syracuseStep 4452060181 = 208690321) B208690321
theorem B5936080241 : Blo 2053435 5936080241 := bstep (se 2 (by rfl) ⟨2226030090, by rfl⟩ : syracuseStep 5936080241 = 4452060181) B4452060181
theorem B3957386827 : Blo 2053435 3957386827 := bstep (se 1 (by rfl) ⟨2968040120, by rfl⟩ : syracuseStep 3957386827 = 5936080241) B5936080241
theorem B5276515769 : Blo 2053435 5276515769 := bstep (se 2 (by rfl) ⟨1978693413, by rfl⟩ : syracuseStep 5276515769 = 3957386827) B3957386827
theorem B3517677179 : Blo 2053435 3517677179 := bstep (se 1 (by rfl) ⟨2638257884, by rfl⟩ : syracuseStep 3517677179 = 5276515769) B5276515769
theorem B2345118119 : Blo 2053435 2345118119 := bstep (se 1 (by rfl) ⟨1758838589, by rfl⟩ : syracuseStep 2345118119 = 3517677179) B3517677179
theorem B1563412079 : Blo 2053435 1563412079 := bstep (se 1 (by rfl) ⟨1172559059, by rfl⟩ : syracuseStep 1563412079 = 2345118119) B2345118119
theorem B1042274719 : Blo 2053435 1042274719 := bstep (se 1 (by rfl) ⟨781706039, by rfl⟩ : syracuseStep 1042274719 = 1563412079) B1563412079
theorem B1389699625 : Blo 2053435 1389699625 := bstep (se 2 (by rfl) ⟨521137359, by rfl⟩ : syracuseStep 1389699625 = 1042274719) B1042274719
theorem B1852932833 : Blo 2053435 1852932833 := bstep (se 2 (by rfl) ⟨694849812, by rfl⟩ : syracuseStep 1852932833 = 1389699625) B1389699625
theorem B1235288555 : Blo 2053435 1235288555 := bstep (se 1 (by rfl) ⟨926466416, by rfl⟩ : syracuseStep 1235288555 = 1852932833) B1852932833
theorem B823525703 : Blo 2053435 823525703 := bstep (se 1 (by rfl) ⟨617644277, by rfl⟩ : syracuseStep 823525703 = 1235288555) B1235288555
theorem B549017135 : Blo 2053435 549017135 := bstep (se 1 (by rfl) ⟨411762851, by rfl⟩ : syracuseStep 549017135 = 823525703) B823525703
theorem B366011423 : Blo 2053435 366011423 := bstep (se 1 (by rfl) ⟨274508567, by rfl⟩ : syracuseStep 366011423 = 549017135) B549017135
theorem B244007615 : Blo 2053435 244007615 := bstep (se 1 (by rfl) ⟨183005711, by rfl⟩ : syracuseStep 244007615 = 366011423) B366011423
theorem B162671743 : Blo 2053435 162671743 := bstep (se 1 (by rfl) ⟨122003807, by rfl⟩ : syracuseStep 162671743 = 244007615) B244007615
theorem B216895657 : Blo 2053435 216895657 := bstep (se 2 (by rfl) ⟨81335871, by rfl⟩ : syracuseStep 216895657 = 162671743) B162671743
theorem B289194209 : Blo 2053435 289194209 := bstep (se 2 (by rfl) ⟨108447828, by rfl⟩ : syracuseStep 289194209 = 216895657) B216895657
theorem B192796139 : Blo 2053435 192796139 := bstep (se 1 (by rfl) ⟨144597104, by rfl⟩ : syracuseStep 192796139 = 289194209) B289194209
theorem B514123037 : Blo 2053435 514123037 := bstep (se 3 (by rfl) ⟨96398069, by rfl⟩ : syracuseStep 514123037 = 192796139) B192796139
theorem B342748691 : Blo 2053435 342748691 := bstep (se 1 (by rfl) ⟨257061518, by rfl⟩ : syracuseStep 342748691 = 514123037) B514123037
theorem B228499127 : Blo 2053435 228499127 := bstep (se 1 (by rfl) ⟨171374345, by rfl⟩ : syracuseStep 228499127 = 342748691) B342748691
theorem B152332751 : Blo 2053435 152332751 := bstep (se 1 (by rfl) ⟨114249563, by rfl⟩ : syracuseStep 152332751 = 228499127) B228499127
theorem B101555167 : Blo 2053435 101555167 := bstep (se 1 (by rfl) ⟨76166375, by rfl⟩ : syracuseStep 101555167 = 152332751) B152332751
theorem B135406889 : Blo 2053435 135406889 := bstep (se 2 (by rfl) ⟨50777583, by rfl⟩ : syracuseStep 135406889 = 101555167) B101555167
theorem B90271259 : Blo 2053435 90271259 := bstep (se 1 (by rfl) ⟨67703444, by rfl⟩ : syracuseStep 90271259 = 135406889) B135406889
theorem B60180839 : Blo 2053435 60180839 := bstep (se 1 (by rfl) ⟨45135629, by rfl⟩ : syracuseStep 60180839 = 90271259) B90271259
theorem B40120559 : Blo 2053435 40120559 := bstep (se 1 (by rfl) ⟨30090419, by rfl⟩ : syracuseStep 40120559 = 60180839) B60180839
theorem B26747039 : Blo 2053435 26747039 := bstep (se 1 (by rfl) ⟨20060279, by rfl⟩ : syracuseStep 26747039 = 40120559) B40120559
theorem B17831359 : Blo 2053435 17831359 := bstep (se 1 (by rfl) ⟨13373519, by rfl⟩ : syracuseStep 17831359 = 26747039) B26747039
theorem B95100581 : Blo 2053435 95100581 := bstep (se 4 (by rfl) ⟨8915679, by rfl⟩ : syracuseStep 95100581 = 17831359) B17831359
theorem B253601549 : Blo 2053435 253601549 := bstep (se 3 (by rfl) ⟨47550290, by rfl⟩ : syracuseStep 253601549 = 95100581) B95100581
theorem B169067699 : Blo 2053435 169067699 := bstep (se 1 (by rfl) ⟨126800774, by rfl⟩ : syracuseStep 169067699 = 253601549) B253601549
theorem B112711799 : Blo 2053435 112711799 := bstep (se 1 (by rfl) ⟨84533849, by rfl⟩ : syracuseStep 112711799 = 169067699) B169067699
theorem B75141199 : Blo 2053435 75141199 := bstep (se 1 (by rfl) ⟨56355899, by rfl⟩ : syracuseStep 75141199 = 112711799) B112711799
theorem B100188265 : Blo 2053435 100188265 := bstep (se 2 (by rfl) ⟨37570599, by rfl⟩ : syracuseStep 100188265 = 75141199) B75141199
theorem B133584353 : Blo 2053435 133584353 := bstep (se 2 (by rfl) ⟨50094132, by rfl⟩ : syracuseStep 133584353 = 100188265) B100188265
theorem B89056235 : Blo 2053435 89056235 := bstep (se 1 (by rfl) ⟨66792176, by rfl⟩ : syracuseStep 89056235 = 133584353) B133584353
theorem B59370823 : Blo 2053435 59370823 := bstep (se 1 (by rfl) ⟨44528117, by rfl⟩ : syracuseStep 59370823 = 89056235) B89056235
theorem B79161097 : Blo 2053435 79161097 := bstep (se 2 (by rfl) ⟨29685411, by rfl⟩ : syracuseStep 79161097 = 59370823) B59370823
theorem B105548129 : Blo 2053435 105548129 := bstep (se 2 (by rfl) ⟨39580548, by rfl⟩ : syracuseStep 105548129 = 79161097) B79161097
theorem B70365419 : Blo 2053435 70365419 := bstep (se 1 (by rfl) ⟨52774064, by rfl⟩ : syracuseStep 70365419 = 105548129) B105548129
theorem B46910279 : Blo 2053435 46910279 := bstep (se 1 (by rfl) ⟨35182709, by rfl⟩ : syracuseStep 46910279 = 70365419) B70365419
theorem B125094077 : Blo 2053435 125094077 := bstep (se 3 (by rfl) ⟨23455139, by rfl⟩ : syracuseStep 125094077 = 46910279) B46910279
theorem B83396051 : Blo 2053435 83396051 := bstep (se 1 (by rfl) ⟨62547038, by rfl⟩ : syracuseStep 83396051 = 125094077) B125094077
theorem B55597367 : Blo 2053435 55597367 := bstep (se 1 (by rfl) ⟨41698025, by rfl⟩ : syracuseStep 55597367 = 83396051) B83396051
theorem B37064911 : Blo 2053435 37064911 := bstep (se 1 (by rfl) ⟨27798683, by rfl⟩ : syracuseStep 37064911 = 55597367) B55597367
theorem B49419881 : Blo 2053435 49419881 := bstep (se 2 (by rfl) ⟨18532455, by rfl⟩ : syracuseStep 49419881 = 37064911) B37064911
theorem B32946587 : Blo 2053435 32946587 := bstep (se 1 (by rfl) ⟨24709940, by rfl⟩ : syracuseStep 32946587 = 49419881) B49419881
theorem B21964391 : Blo 2053435 21964391 := bstep (se 1 (by rfl) ⟨16473293, by rfl⟩ : syracuseStep 21964391 = 32946587) B32946587
theorem B14642927 : Blo 2053435 14642927 := bstep (se 1 (by rfl) ⟨10982195, by rfl⟩ : syracuseStep 14642927 = 21964391) B21964391
theorem B9761951 : Blo 2053435 9761951 := bstep (se 1 (by rfl) ⟨7321463, by rfl⟩ : syracuseStep 9761951 = 14642927) B14642927
theorem B6507967 : Blo 2053435 6507967 := bstep (se 1 (by rfl) ⟨4880975, by rfl⟩ : syracuseStep 6507967 = 9761951) B9761951
theorem B8677289 : Blo 2053435 8677289 := bstep (se 2 (by rfl) ⟨3253983, by rfl⟩ : syracuseStep 8677289 = 6507967) B6507967
theorem B5784859 : Blo 2053435 5784859 := bstep (se 1 (by rfl) ⟨4338644, by rfl⟩ : syracuseStep 5784859 = 8677289) B8677289
theorem B7713145 : Blo 2053435 7713145 := bstep (se 2 (by rfl) ⟨2892429, by rfl⟩ : syracuseStep 7713145 = 5784859) B5784859
theorem B10284193 : Blo 2053435 10284193 := bstep (se 2 (by rfl) ⟨3856572, by rfl⟩ : syracuseStep 10284193 = 7713145) B7713145
theorem B13712257 : Blo 2053435 13712257 := bstep (se 2 (by rfl) ⟨5142096, by rfl⟩ : syracuseStep 13712257 = 10284193) B10284193
theorem B18283009 : Blo 2053435 18283009 := bstep (se 2 (by rfl) ⟨6856128, by rfl⟩ : syracuseStep 18283009 = 13712257) B13712257
theorem B24377345 : Blo 2053435 24377345 := bstep (se 2 (by rfl) ⟨9141504, by rfl⟩ : syracuseStep 24377345 = 18283009) B18283009
theorem B16251563 : Blo 2053435 16251563 := bstep (se 1 (by rfl) ⟨12188672, by rfl⟩ : syracuseStep 16251563 = 24377345) B24377345
theorem B43337501 : Blo 2053435 43337501 := bstep (se 3 (by rfl) ⟨8125781, by rfl⟩ : syracuseStep 43337501 = 16251563) B16251563
theorem B28891667 : Blo 2053435 28891667 := bstep (se 1 (by rfl) ⟨21668750, by rfl⟩ : syracuseStep 28891667 = 43337501) B43337501
theorem B19261111 : Blo 2053435 19261111 := bstep (se 1 (by rfl) ⟨14445833, by rfl⟩ : syracuseStep 19261111 = 28891667) B28891667
theorem B25681481 : Blo 2053435 25681481 := bstep (se 2 (by rfl) ⟨9630555, by rfl⟩ : syracuseStep 25681481 = 19261111) B19261111
theorem B17120987 : Blo 2053435 17120987 := bstep (se 1 (by rfl) ⟨12840740, by rfl⟩ : syracuseStep 17120987 = 25681481) B25681481
theorem B11413991 : Blo 2053435 11413991 := bstep (se 1 (by rfl) ⟨8560493, by rfl⟩ : syracuseStep 11413991 = 17120987) B17120987
theorem B30437309 : Blo 2053435 30437309 := bstep (se 3 (by rfl) ⟨5706995, by rfl⟩ : syracuseStep 30437309 = 11413991) B11413991
theorem B20291539 : Blo 2053435 20291539 := bstep (se 1 (by rfl) ⟨15218654, by rfl⟩ : syracuseStep 20291539 = 30437309) B30437309
theorem B27055385 : Blo 2053435 27055385 := bstep (se 2 (by rfl) ⟨10145769, by rfl⟩ : syracuseStep 27055385 = 20291539) B20291539
theorem B18036923 : Blo 2053435 18036923 := bstep (se 1 (by rfl) ⟨13527692, by rfl⟩ : syracuseStep 18036923 = 27055385) B27055385
theorem B48098461 : Blo 2053435 48098461 := bstep (se 3 (by rfl) ⟨9018461, by rfl⟩ : syracuseStep 48098461 = 18036923) B18036923
theorem B64131281 : Blo 2053435 64131281 := bstep (se 2 (by rfl) ⟨24049230, by rfl⟩ : syracuseStep 64131281 = 48098461) B48098461
theorem B42754187 : Blo 2053435 42754187 := bstep (se 1 (by rfl) ⟨32065640, by rfl⟩ : syracuseStep 42754187 = 64131281) B64131281
theorem B114011165 : Blo 2053435 114011165 := bstep (se 3 (by rfl) ⟨21377093, by rfl⟩ : syracuseStep 114011165 = 42754187) B42754187
theorem B76007443 : Blo 2053435 76007443 := bstep (se 1 (by rfl) ⟨57005582, by rfl⟩ : syracuseStep 76007443 = 114011165) B114011165
theorem B101343257 : Blo 2053435 101343257 := bstep (se 2 (by rfl) ⟨38003721, by rfl⟩ : syracuseStep 101343257 = 76007443) B76007443
theorem B67562171 : Blo 2053435 67562171 := bstep (se 1 (by rfl) ⟨50671628, by rfl⟩ : syracuseStep 67562171 = 101343257) B101343257
theorem B45041447 : Blo 2053435 45041447 := bstep (se 1 (by rfl) ⟨33781085, by rfl⟩ : syracuseStep 45041447 = 67562171) B67562171
theorem B30027631 : Blo 2053435 30027631 := bstep (se 1 (by rfl) ⟨22520723, by rfl⟩ : syracuseStep 30027631 = 45041447) B45041447
theorem B40036841 : Blo 2053435 40036841 := bstep (se 2 (by rfl) ⟨15013815, by rfl⟩ : syracuseStep 40036841 = 30027631) B30027631
theorem B26691227 : Blo 2053435 26691227 := bstep (se 1 (by rfl) ⟨20018420, by rfl⟩ : syracuseStep 26691227 = 40036841) B40036841
theorem B17794151 : Blo 2053435 17794151 := bstep (se 1 (by rfl) ⟨13345613, by rfl⟩ : syracuseStep 17794151 = 26691227) B26691227
theorem B11862767 : Blo 2053435 11862767 := bstep (se 1 (by rfl) ⟨8897075, by rfl⟩ : syracuseStep 11862767 = 17794151) B17794151
theorem B7908511 : Blo 2053435 7908511 := bstep (se 1 (by rfl) ⟨5931383, by rfl⟩ : syracuseStep 7908511 = 11862767) B11862767
theorem B10544681 : Blo 2053435 10544681 := bstep (se 2 (by rfl) ⟨3954255, by rfl⟩ : syracuseStep 10544681 = 7908511) B7908511
theorem B28119149 : Blo 2053435 28119149 := bstep (se 3 (by rfl) ⟨5272340, by rfl⟩ : syracuseStep 28119149 = 10544681) B10544681
theorem B18746099 : Blo 2053435 18746099 := bstep (se 1 (by rfl) ⟨14059574, by rfl⟩ : syracuseStep 18746099 = 28119149) B28119149
theorem B12497399 : Blo 2053435 12497399 := bstep (se 1 (by rfl) ⟨9373049, by rfl⟩ : syracuseStep 12497399 = 18746099) B18746099
theorem B8331599 : Blo 2053435 8331599 := bstep (se 1 (by rfl) ⟨6248699, by rfl⟩ : syracuseStep 8331599 = 12497399) B12497399
theorem B22217597 : Blo 2053435 22217597 := bstep (se 3 (by rfl) ⟨4165799, by rfl⟩ : syracuseStep 22217597 = 8331599) B8331599
theorem B14811731 : Blo 2053435 14811731 := bstep (se 1 (by rfl) ⟨11108798, by rfl⟩ : syracuseStep 14811731 = 22217597) B22217597
theorem B9874487 : Blo 2053435 9874487 := bstep (se 1 (by rfl) ⟨7405865, by rfl⟩ : syracuseStep 9874487 = 14811731) B14811731
theorem B6582991 : Blo 2053435 6582991 := bstep (se 1 (by rfl) ⟨4937243, by rfl⟩ : syracuseStep 6582991 = 9874487) B9874487
theorem B8777321 : Blo 2053435 8777321 := bstep (se 2 (by rfl) ⟨3291495, by rfl⟩ : syracuseStep 8777321 = 6582991) B6582991
theorem B5851547 : Blo 2053435 5851547 := bstep (se 1 (by rfl) ⟨4388660, by rfl⟩ : syracuseStep 5851547 = 8777321) B8777321
theorem B3901031 : Blo 2053435 3901031 := bstep (se 1 (by rfl) ⟨2925773, by rfl⟩ : syracuseStep 3901031 = 5851547) B5851547
theorem B2600687 : Blo 2053435 2600687 := bstep (se 1 (by rfl) ⟨1950515, by rfl⟩ : syracuseStep 2600687 = 3901031) B3901031
theorem B6935165 : Blo 2053435 6935165 := bstep (se 3 (by rfl) ⟨1300343, by rfl⟩ : syracuseStep 6935165 = 2600687) B2600687
theorem B4623443 : Blo 2053435 4623443 := bstep (se 1 (by rfl) ⟨3467582, by rfl⟩ : syracuseStep 4623443 = 6935165) B6935165
theorem B3082295 : Blo 2053435 3082295 := bstep (se 1 (by rfl) ⟨2311721, by rfl⟩ : syracuseStep 3082295 = 4623443) B4623443
theorem B2054863 : Blo 2053435 2054863 := bstep (se 1 (by rfl) ⟨1541147, by rfl⟩ : syracuseStep 2054863 = 3082295) B3082295
theorem B3082301 : Blo 2053435 3082301 := bbase (se 3 (by rfl) ⟨577931, by rfl⟩ : syracuseStep 3082301 = 1155863) (by norm_num)
theorem B2054867 : Blo 2053435 2054867 := bstep (se 1 (by rfl) ⟨1541150, by rfl⟩ : syracuseStep 2054867 = 3082301) B3082301
theorem B4623461 : Blo 2053435 4623461 := bbase (se 4 (by rfl) ⟨433449, by rfl⟩ : syracuseStep 4623461 = 866899) (by norm_num)
theorem B3082307 : Blo 2053435 3082307 := bstep (se 1 (by rfl) ⟨2311730, by rfl⟩ : syracuseStep 3082307 = 4623461) B4623461
theorem B2054871 : Blo 2053435 2054871 := bstep (se 1 (by rfl) ⟨1541153, by rfl⟩ : syracuseStep 2054871 = 3082307) B3082307
theorem B5201405 : Blo 2053435 5201405 := bbase (se 3 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 5201405 = 1950527) (by norm_num)
theorem B3467603 : Blo 2053435 3467603 := bstep (se 1 (by rfl) ⟨2600702, by rfl⟩ : syracuseStep 3467603 = 5201405) B5201405
theorem B2311735 : Blo 2053435 2311735 := bstep (se 1 (by rfl) ⟨1733801, by rfl⟩ : syracuseStep 2311735 = 3467603) B3467603
theorem B3082313 : Blo 2053435 3082313 := bstep (se 2 (by rfl) ⟨1155867, by rfl⟩ : syracuseStep 3082313 = 2311735) B2311735
theorem B2054875 : Blo 2053435 2054875 := bstep (se 1 (by rfl) ⟨1541156, by rfl⟩ : syracuseStep 2054875 = 3082313) B3082313
theorem B3901061 : Blo 2053435 3901061 := bbase (se 4 (by rfl) ⟨365724, by rfl⟩ : syracuseStep 3901061 = 731449) (by norm_num)
theorem B10402829 : Blo 2053435 10402829 := bstep (se 3 (by rfl) ⟨1950530, by rfl⟩ : syracuseStep 10402829 = 3901061) B3901061
theorem B6935219 : Blo 2053435 6935219 := bstep (se 1 (by rfl) ⟨5201414, by rfl⟩ : syracuseStep 6935219 = 10402829) B10402829
theorem B4623479 : Blo 2053435 4623479 := bstep (se 1 (by rfl) ⟨3467609, by rfl⟩ : syracuseStep 4623479 = 6935219) B6935219
theorem B3082319 : Blo 2053435 3082319 := bstep (se 1 (by rfl) ⟨2311739, by rfl⟩ : syracuseStep 3082319 = 4623479) B4623479
theorem B2054879 : Blo 2053435 2054879 := bstep (se 1 (by rfl) ⟨1541159, by rfl⟩ : syracuseStep 2054879 = 3082319) B3082319
theorem B3082325 : Blo 2053435 3082325 := bbase (se 8 (by rfl) ⟨18060, by rfl⟩ : syracuseStep 3082325 = 36121) (by norm_num)
theorem B2054883 : Blo 2053435 2054883 := bstep (se 1 (by rfl) ⟨1541162, by rfl⟩ : syracuseStep 2054883 = 3082325) B3082325
theorem B3954301 : Blo 2053435 3954301 := bbase (se 3 (by rfl) ⟨741431, by rfl⟩ : syracuseStep 3954301 = 1482863) (by norm_num)
theorem B84358421 : Blo 2053435 84358421 := bstep (se 6 (by rfl) ⟨1977150, by rfl⟩ : syracuseStep 84358421 = 3954301) B3954301
theorem B56238947 : Blo 2053435 56238947 := bstep (se 1 (by rfl) ⟨42179210, by rfl⟩ : syracuseStep 56238947 = 84358421) B84358421
theorem B37492631 : Blo 2053435 37492631 := bstep (se 1 (by rfl) ⟨28119473, by rfl⟩ : syracuseStep 37492631 = 56238947) B56238947
theorem B24995087 : Blo 2053435 24995087 := bstep (se 1 (by rfl) ⟨18746315, by rfl⟩ : syracuseStep 24995087 = 37492631) B37492631
theorem B16663391 : Blo 2053435 16663391 := bstep (se 1 (by rfl) ⟨12497543, by rfl⟩ : syracuseStep 16663391 = 24995087) B24995087
theorem B11108927 : Blo 2053435 11108927 := bstep (se 1 (by rfl) ⟨8331695, by rfl⟩ : syracuseStep 11108927 = 16663391) B16663391
theorem B29623805 : Blo 2053435 29623805 := bstep (se 3 (by rfl) ⟨5554463, by rfl⟩ : syracuseStep 29623805 = 11108927) B11108927
theorem B19749203 : Blo 2053435 19749203 := bstep (se 1 (by rfl) ⟨14811902, by rfl⟩ : syracuseStep 19749203 = 29623805) B29623805
theorem B13166135 : Blo 2053435 13166135 := bstep (se 1 (by rfl) ⟨9874601, by rfl⟩ : syracuseStep 13166135 = 19749203) B19749203
theorem B8777423 : Blo 2053435 8777423 := bstep (se 1 (by rfl) ⟨6583067, by rfl⟩ : syracuseStep 8777423 = 13166135) B13166135
theorem B5851615 : Blo 2053435 5851615 := bstep (se 1 (by rfl) ⟨4388711, by rfl⟩ : syracuseStep 5851615 = 8777423) B8777423
theorem B7802153 : Blo 2053435 7802153 := bstep (se 2 (by rfl) ⟨2925807, by rfl⟩ : syracuseStep 7802153 = 5851615) B5851615
theorem B5201435 : Blo 2053435 5201435 := bstep (se 1 (by rfl) ⟨3901076, by rfl⟩ : syracuseStep 5201435 = 7802153) B7802153
theorem B3467623 : Blo 2053435 3467623 := bstep (se 1 (by rfl) ⟨2600717, by rfl⟩ : syracuseStep 3467623 = 5201435) B5201435
theorem B4623497 : Blo 2053435 4623497 := bstep (se 2 (by rfl) ⟨1733811, by rfl⟩ : syracuseStep 4623497 = 3467623) B3467623
theorem B3082331 : Blo 2053435 3082331 := bstep (se 1 (by rfl) ⟨2311748, by rfl⟩ : syracuseStep 3082331 = 4623497) B4623497
theorem B2054887 : Blo 2053435 2054887 := bstep (se 1 (by rfl) ⟨1541165, by rfl⟩ : syracuseStep 2054887 = 3082331) B3082331
theorem B2311753 : Blo 2053435 2311753 := bbase (se 2 (by rfl) ⟨866907, by rfl⟩ : syracuseStep 2311753 = 1733815) (by norm_num)
theorem B3082337 : Blo 2053435 3082337 := bstep (se 2 (by rfl) ⟨1155876, by rfl⟩ : syracuseStep 3082337 = 2311753) B2311753
theorem B2054891 : Blo 2053435 2054891 := bstep (se 1 (by rfl) ⟨1541168, by rfl⟩ : syracuseStep 2054891 = 3082337) B3082337
theorem B4750541 : Blo 2053435 4750541 := bbase (se 3 (by rfl) ⟨890726, by rfl⟩ : syracuseStep 4750541 = 1781453) (by norm_num)
theorem B3167027 : Blo 2053435 3167027 := bstep (se 1 (by rfl) ⟨2375270, by rfl⟩ : syracuseStep 3167027 = 4750541) B4750541
theorem B2111351 : Blo 2053435 2111351 := bstep (se 1 (by rfl) ⟨1583513, by rfl⟩ : syracuseStep 2111351 = 3167027) B3167027
theorem B5630269 : Blo 2053435 5630269 := bstep (se 3 (by rfl) ⟨1055675, by rfl⟩ : syracuseStep 5630269 = 2111351) B2111351
theorem B7507025 : Blo 2053435 7507025 := bstep (se 2 (by rfl) ⟨2815134, by rfl⟩ : syracuseStep 7507025 = 5630269) B5630269
theorem B5004683 : Blo 2053435 5004683 := bstep (se 1 (by rfl) ⟨3753512, by rfl⟩ : syracuseStep 5004683 = 7507025) B7507025
theorem B3336455 : Blo 2053435 3336455 := bstep (se 1 (by rfl) ⟨2502341, by rfl⟩ : syracuseStep 3336455 = 5004683) B5004683
theorem B2224303 : Blo 2053435 2224303 := bstep (se 1 (by rfl) ⟨1668227, by rfl⟩ : syracuseStep 2224303 = 3336455) B3336455
theorem B11862949 : Blo 2053435 11862949 := bstep (se 4 (by rfl) ⟨1112151, by rfl⟩ : syracuseStep 11862949 = 2224303) B2224303
theorem B15817265 : Blo 2053435 15817265 := bstep (se 2 (by rfl) ⟨5931474, by rfl⟩ : syracuseStep 15817265 = 11862949) B11862949
theorem B10544843 : Blo 2053435 10544843 := bstep (se 1 (by rfl) ⟨7908632, by rfl⟩ : syracuseStep 10544843 = 15817265) B15817265
theorem B28119581 : Blo 2053435 28119581 := bstep (se 3 (by rfl) ⟨5272421, by rfl⟩ : syracuseStep 28119581 = 10544843) B10544843
theorem B18746387 : Blo 2053435 18746387 := bstep (se 1 (by rfl) ⟨14059790, by rfl⟩ : syracuseStep 18746387 = 28119581) B28119581
theorem B12497591 : Blo 2053435 12497591 := bstep (se 1 (by rfl) ⟨9373193, by rfl⟩ : syracuseStep 12497591 = 18746387) B18746387
theorem B33326909 : Blo 2053435 33326909 := bstep (se 3 (by rfl) ⟨6248795, by rfl⟩ : syracuseStep 33326909 = 12497591) B12497591
theorem B22217939 : Blo 2053435 22217939 := bstep (se 1 (by rfl) ⟨16663454, by rfl⟩ : syracuseStep 22217939 = 33326909) B33326909
theorem B14811959 : Blo 2053435 14811959 := bstep (se 1 (by rfl) ⟨11108969, by rfl⟩ : syracuseStep 14811959 = 22217939) B22217939
theorem B9874639 : Blo 2053435 9874639 := bstep (se 1 (by rfl) ⟨7405979, by rfl⟩ : syracuseStep 9874639 = 14811959) B14811959
theorem B13166185 : Blo 2053435 13166185 := bstep (se 2 (by rfl) ⟨4937319, by rfl⟩ : syracuseStep 13166185 = 9874639) B9874639
theorem B17554913 : Blo 2053435 17554913 := bstep (se 2 (by rfl) ⟨6583092, by rfl⟩ : syracuseStep 17554913 = 13166185) B13166185
theorem B11703275 : Blo 2053435 11703275 := bstep (se 1 (by rfl) ⟨8777456, by rfl⟩ : syracuseStep 11703275 = 17554913) B17554913
theorem B7802183 : Blo 2053435 7802183 := bstep (se 1 (by rfl) ⟨5851637, by rfl⟩ : syracuseStep 7802183 = 11703275) B11703275
theorem B5201455 : Blo 2053435 5201455 := bstep (se 1 (by rfl) ⟨3901091, by rfl⟩ : syracuseStep 5201455 = 7802183) B7802183
theorem B6935273 : Blo 2053435 6935273 := bstep (se 2 (by rfl) ⟨2600727, by rfl⟩ : syracuseStep 6935273 = 5201455) B5201455
theorem B4623515 : Blo 2053435 4623515 := bstep (se 1 (by rfl) ⟨3467636, by rfl⟩ : syracuseStep 4623515 = 6935273) B6935273
theorem B3082343 : Blo 2053435 3082343 := bstep (se 1 (by rfl) ⟨2311757, by rfl⟩ : syracuseStep 3082343 = 4623515) B4623515
theorem B2054895 : Blo 2053435 2054895 := bstep (se 1 (by rfl) ⟨1541171, by rfl⟩ : syracuseStep 2054895 = 3082343) B3082343
theorem B3082349 : Blo 2053435 3082349 := bbase (se 3 (by rfl) ⟨577940, by rfl⟩ : syracuseStep 3082349 = 1155881) (by norm_num)
theorem B2054899 : Blo 2053435 2054899 := bstep (se 1 (by rfl) ⟨1541174, by rfl⟩ : syracuseStep 2054899 = 3082349) B3082349
theorem B4623533 : Blo 2053435 4623533 := bbase (se 3 (by rfl) ⟨866912, by rfl⟩ : syracuseStep 4623533 = 1733825) (by norm_num)
theorem B3082355 : Blo 2053435 3082355 := bstep (se 1 (by rfl) ⟨2311766, by rfl⟩ : syracuseStep 3082355 = 4623533) B4623533
theorem B2054903 : Blo 2053435 2054903 := bstep (se 1 (by rfl) ⟨1541177, by rfl⟩ : syracuseStep 2054903 = 3082355) B3082355
theorem B3703013 : Blo 2053435 3703013 := bbase (se 4 (by rfl) ⟨347157, by rfl⟩ : syracuseStep 3703013 = 694315) (by norm_num)
theorem B2468675 : Blo 2053435 2468675 := bstep (se 1 (by rfl) ⟨1851506, by rfl⟩ : syracuseStep 2468675 = 3703013) B3703013
theorem B6583133 : Blo 2053435 6583133 := bstep (se 3 (by rfl) ⟨1234337, by rfl⟩ : syracuseStep 6583133 = 2468675) B2468675
theorem B4388755 : Blo 2053435 4388755 := bstep (se 1 (by rfl) ⟨3291566, by rfl⟩ : syracuseStep 4388755 = 6583133) B6583133
theorem B5851673 : Blo 2053435 5851673 := bstep (se 2 (by rfl) ⟨2194377, by rfl⟩ : syracuseStep 5851673 = 4388755) B4388755
theorem B3901115 : Blo 2053435 3901115 := bstep (se 1 (by rfl) ⟨2925836, by rfl⟩ : syracuseStep 3901115 = 5851673) B5851673
theorem B2600743 : Blo 2053435 2600743 := bstep (se 1 (by rfl) ⟨1950557, by rfl⟩ : syracuseStep 2600743 = 3901115) B3901115
theorem B3467657 : Blo 2053435 3467657 := bstep (se 2 (by rfl) ⟨1300371, by rfl⟩ : syracuseStep 3467657 = 2600743) B2600743
theorem B2311771 : Blo 2053435 2311771 := bstep (se 1 (by rfl) ⟨1733828, by rfl⟩ : syracuseStep 2311771 = 3467657) B3467657
theorem B3082361 : Blo 2053435 3082361 := bstep (se 2 (by rfl) ⟨1155885, by rfl⟩ : syracuseStep 3082361 = 2311771) B2311771
theorem B2054907 : Blo 2053435 2054907 := bstep (se 1 (by rfl) ⟨1541180, by rfl⟩ : syracuseStep 2054907 = 3082361) B3082361
theorem B19524341 : Blo 2053435 19524341 := bbase (se 5 (by rfl) ⟨915203, by rfl⟩ : syracuseStep 19524341 = 1830407) (by norm_num)
theorem B52064909 : Blo 2053435 52064909 := bstep (se 3 (by rfl) ⟨9762170, by rfl⟩ : syracuseStep 52064909 = 19524341) B19524341
theorem B34709939 : Blo 2053435 34709939 := bstep (se 1 (by rfl) ⟨26032454, by rfl⟩ : syracuseStep 34709939 = 52064909) B52064909
theorem B23139959 : Blo 2053435 23139959 := bstep (se 1 (by rfl) ⟨17354969, by rfl⟩ : syracuseStep 23139959 = 34709939) B34709939
theorem B61706557 : Blo 2053435 61706557 := bstep (se 3 (by rfl) ⟨11569979, by rfl⟩ : syracuseStep 61706557 = 23139959) B23139959
theorem B82275409 : Blo 2053435 82275409 := bstep (se 2 (by rfl) ⟨30853278, by rfl⟩ : syracuseStep 82275409 = 61706557) B61706557
theorem B438802181 : Blo 2053435 438802181 := bstep (se 4 (by rfl) ⟨41137704, by rfl⟩ : syracuseStep 438802181 = 82275409) B82275409
theorem B292534787 : Blo 2053435 292534787 := bstep (se 1 (by rfl) ⟨219401090, by rfl⟩ : syracuseStep 292534787 = 438802181) B438802181
theorem B780092765 : Blo 2053435 780092765 := bstep (se 3 (by rfl) ⟨146267393, by rfl⟩ : syracuseStep 780092765 = 292534787) B292534787
theorem B520061843 : Blo 2053435 520061843 := bstep (se 1 (by rfl) ⟨390046382, by rfl⟩ : syracuseStep 520061843 = 780092765) B780092765
theorem B1386831581 : Blo 2053435 1386831581 := bstep (se 3 (by rfl) ⟨260030921, by rfl⟩ : syracuseStep 1386831581 = 520061843) B520061843
theorem B924554387 : Blo 2053435 924554387 := bstep (se 1 (by rfl) ⟨693415790, by rfl⟩ : syracuseStep 924554387 = 1386831581) B1386831581
theorem B616369591 : Blo 2053435 616369591 := bstep (se 1 (by rfl) ⟨462277193, by rfl⟩ : syracuseStep 616369591 = 924554387) B924554387
theorem B821826121 : Blo 2053435 821826121 := bstep (se 2 (by rfl) ⟨308184795, by rfl⟩ : syracuseStep 821826121 = 616369591) B616369591
theorem B1095768161 : Blo 2053435 1095768161 := bstep (se 2 (by rfl) ⟨410913060, by rfl⟩ : syracuseStep 1095768161 = 821826121) B821826121
theorem B730512107 : Blo 2053435 730512107 := bstep (se 1 (by rfl) ⟨547884080, by rfl⟩ : syracuseStep 730512107 = 1095768161) B1095768161
theorem B487008071 : Blo 2053435 487008071 := bstep (se 1 (by rfl) ⟨365256053, by rfl⟩ : syracuseStep 487008071 = 730512107) B730512107
theorem B324672047 : Blo 2053435 324672047 := bstep (se 1 (by rfl) ⟨243504035, by rfl⟩ : syracuseStep 324672047 = 487008071) B487008071
theorem B216448031 : Blo 2053435 216448031 := bstep (se 1 (by rfl) ⟨162336023, by rfl⟩ : syracuseStep 216448031 = 324672047) B324672047
theorem B577194749 : Blo 2053435 577194749 := bstep (se 3 (by rfl) ⟨108224015, by rfl⟩ : syracuseStep 577194749 = 216448031) B216448031
theorem B384796499 : Blo 2053435 384796499 := bstep (se 1 (by rfl) ⟨288597374, by rfl⟩ : syracuseStep 384796499 = 577194749) B577194749
theorem B4104495989 : Blo 2053435 4104495989 := bstep (se 5 (by rfl) ⟨192398249, by rfl⟩ : syracuseStep 4104495989 = 384796499) B384796499
theorem B2736330659 : Blo 2053435 2736330659 := bstep (se 1 (by rfl) ⟨2052247994, by rfl⟩ : syracuseStep 2736330659 = 4104495989) B4104495989
theorem B1824220439 : Blo 2053435 1824220439 := bstep (se 1 (by rfl) ⟨1368165329, by rfl⟩ : syracuseStep 1824220439 = 2736330659) B2736330659
theorem B1216146959 : Blo 2053435 1216146959 := bstep (se 1 (by rfl) ⟨912110219, by rfl⟩ : syracuseStep 1216146959 = 1824220439) B1824220439
theorem B810764639 : Blo 2053435 810764639 := bstep (se 1 (by rfl) ⟨608073479, by rfl⟩ : syracuseStep 810764639 = 1216146959) B1216146959
theorem B540509759 : Blo 2053435 540509759 := bstep (se 1 (by rfl) ⟨405382319, by rfl⟩ : syracuseStep 540509759 = 810764639) B810764639
theorem B360339839 : Blo 2053435 360339839 := bstep (se 1 (by rfl) ⟨270254879, by rfl⟩ : syracuseStep 360339839 = 540509759) B540509759
theorem B240226559 : Blo 2053435 240226559 := bstep (se 1 (by rfl) ⟨180169919, by rfl⟩ : syracuseStep 240226559 = 360339839) B360339839
theorem B160151039 : Blo 2053435 160151039 := bstep (se 1 (by rfl) ⟨120113279, by rfl⟩ : syracuseStep 160151039 = 240226559) B240226559
theorem B106767359 : Blo 2053435 106767359 := bstep (se 1 (by rfl) ⟨80075519, by rfl⟩ : syracuseStep 106767359 = 160151039) B160151039
theorem B71178239 : Blo 2053435 71178239 := bstep (se 1 (by rfl) ⟨53383679, by rfl⟩ : syracuseStep 71178239 = 106767359) B106767359
theorem B47452159 : Blo 2053435 47452159 := bstep (se 1 (by rfl) ⟨35589119, by rfl⟩ : syracuseStep 47452159 = 71178239) B71178239
theorem B63269545 : Blo 2053435 63269545 := bstep (se 2 (by rfl) ⟨23726079, by rfl⟩ : syracuseStep 63269545 = 47452159) B47452159
theorem B84359393 : Blo 2053435 84359393 := bstep (se 2 (by rfl) ⟨31634772, by rfl⟩ : syracuseStep 84359393 = 63269545) B63269545
theorem B56239595 : Blo 2053435 56239595 := bstep (se 1 (by rfl) ⟨42179696, by rfl⟩ : syracuseStep 56239595 = 84359393) B84359393
theorem B37493063 : Blo 2053435 37493063 := bstep (se 1 (by rfl) ⟨28119797, by rfl⟩ : syracuseStep 37493063 = 56239595) B56239595
theorem B24995375 : Blo 2053435 24995375 := bstep (se 1 (by rfl) ⟨18746531, by rfl⟩ : syracuseStep 24995375 = 37493063) B37493063
theorem B16663583 : Blo 2053435 16663583 := bstep (se 1 (by rfl) ⟨12497687, by rfl⟩ : syracuseStep 16663583 = 24995375) B24995375
theorem B11109055 : Blo 2053435 11109055 := bstep (se 1 (by rfl) ⟨8331791, by rfl⟩ : syracuseStep 11109055 = 16663583) B16663583
theorem B14812073 : Blo 2053435 14812073 := bstep (se 2 (by rfl) ⟨5554527, by rfl⟩ : syracuseStep 14812073 = 11109055) B11109055
theorem B9874715 : Blo 2053435 9874715 := bstep (se 1 (by rfl) ⟨7406036, by rfl⟩ : syracuseStep 9874715 = 14812073) B14812073
theorem B26332573 : Blo 2053435 26332573 := bstep (se 3 (by rfl) ⟨4937357, by rfl⟩ : syracuseStep 26332573 = 9874715) B9874715
theorem B35110097 : Blo 2053435 35110097 := bstep (se 2 (by rfl) ⟨13166286, by rfl⟩ : syracuseStep 35110097 = 26332573) B26332573
theorem B23406731 : Blo 2053435 23406731 := bstep (se 1 (by rfl) ⟨17555048, by rfl⟩ : syracuseStep 23406731 = 35110097) B35110097
theorem B15604487 : Blo 2053435 15604487 := bstep (se 1 (by rfl) ⟨11703365, by rfl⟩ : syracuseStep 15604487 = 23406731) B23406731
theorem B10402991 : Blo 2053435 10402991 := bstep (se 1 (by rfl) ⟨7802243, by rfl⟩ : syracuseStep 10402991 = 15604487) B15604487
theorem B6935327 : Blo 2053435 6935327 := bstep (se 1 (by rfl) ⟨5201495, by rfl⟩ : syracuseStep 6935327 = 10402991) B10402991
theorem B4623551 : Blo 2053435 4623551 := bstep (se 1 (by rfl) ⟨3467663, by rfl⟩ : syracuseStep 4623551 = 6935327) B6935327
theorem B3082367 : Blo 2053435 3082367 := bstep (se 1 (by rfl) ⟨2311775, by rfl⟩ : syracuseStep 3082367 = 4623551) B4623551
theorem B2054911 : Blo 2053435 2054911 := bstep (se 1 (by rfl) ⟨1541183, by rfl⟩ : syracuseStep 2054911 = 3082367) B3082367
theorem B3082373 : Blo 2053435 3082373 := bbase (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) (by norm_num)
theorem B2054915 : Blo 2053435 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B3467677 : Blo 2053435 3467677 := bbase (se 3 (by rfl) ⟨650189, by rfl⟩ : syracuseStep 3467677 = 1300379) (by norm_num)
theorem B4623569 : Blo 2053435 4623569 := bstep (se 2 (by rfl) ⟨1733838, by rfl⟩ : syracuseStep 4623569 = 3467677) B3467677
theorem B3082379 : Blo 2053435 3082379 := bstep (se 1 (by rfl) ⟨2311784, by rfl⟩ : syracuseStep 3082379 = 4623569) B4623569
theorem B2054919 : Blo 2053435 2054919 := bstep (se 1 (by rfl) ⟨1541189, by rfl⟩ : syracuseStep 2054919 = 3082379) B3082379
theorem B2311789 : Blo 2053435 2311789 := bbase (se 3 (by rfl) ⟨433460, by rfl⟩ : syracuseStep 2311789 = 866921) (by norm_num)
theorem B3082385 : Blo 2053435 3082385 := bstep (se 2 (by rfl) ⟨1155894, by rfl⟩ : syracuseStep 3082385 = 2311789) B2311789
theorem B2054923 : Blo 2053435 2054923 := bstep (se 1 (by rfl) ⟨1541192, by rfl⟩ : syracuseStep 2054923 = 3082385) B3082385
theorem B6935381 : Blo 2053435 6935381 := bbase (se 9 (by rfl) ⟨20318, by rfl⟩ : syracuseStep 6935381 = 40637) (by norm_num)
theorem B4623587 : Blo 2053435 4623587 := bstep (se 1 (by rfl) ⟨3467690, by rfl⟩ : syracuseStep 4623587 = 6935381) B6935381
theorem B3082391 : Blo 2053435 3082391 := bstep (se 1 (by rfl) ⟨2311793, by rfl⟩ : syracuseStep 3082391 = 4623587) B4623587
theorem B2054927 : Blo 2053435 2054927 := bstep (se 1 (by rfl) ⟨1541195, by rfl⟩ : syracuseStep 2054927 = 3082391) B3082391
theorem B3082397 : Blo 2053435 3082397 := bbase (se 3 (by rfl) ⟨577949, by rfl⟩ : syracuseStep 3082397 = 1155899) (by norm_num)
theorem B2054931 : Blo 2053435 2054931 := bstep (se 1 (by rfl) ⟨1541198, by rfl⟩ : syracuseStep 2054931 = 3082397) B3082397
theorem B4623605 : Blo 2053435 4623605 := bbase (se 5 (by rfl) ⟨216731, by rfl⟩ : syracuseStep 4623605 = 433463) (by norm_num)
theorem B3082403 : Blo 2053435 3082403 := bstep (se 1 (by rfl) ⟨2311802, by rfl⟩ : syracuseStep 3082403 = 4623605) B4623605
theorem B2054935 : Blo 2053435 2054935 := bstep (se 1 (by rfl) ⟨1541201, by rfl⟩ : syracuseStep 2054935 = 3082403) B3082403
theorem B2672237 : Blo 2053435 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B7125965 : Blo 2053435 7125965 := bstep (se 3 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 7125965 = 2672237) B2672237
theorem B4750643 : Blo 2053435 4750643 := bstep (se 1 (by rfl) ⟨3562982, by rfl⟩ : syracuseStep 4750643 = 7125965) B7125965
theorem B3167095 : Blo 2053435 3167095 := bstep (se 1 (by rfl) ⟨2375321, by rfl⟩ : syracuseStep 3167095 = 4750643) B4750643
theorem B4222793 : Blo 2053435 4222793 := bstep (se 2 (by rfl) ⟨1583547, by rfl⟩ : syracuseStep 4222793 = 3167095) B3167095
theorem B11260781 : Blo 2053435 11260781 := bstep (se 3 (by rfl) ⟨2111396, by rfl⟩ : syracuseStep 11260781 = 4222793) B4222793
theorem B7507187 : Blo 2053435 7507187 := bstep (se 1 (by rfl) ⟨5630390, by rfl⟩ : syracuseStep 7507187 = 11260781) B11260781
theorem B5004791 : Blo 2053435 5004791 := bstep (se 1 (by rfl) ⟨3753593, by rfl⟩ : syracuseStep 5004791 = 7507187) B7507187
theorem B3336527 : Blo 2053435 3336527 := bstep (se 1 (by rfl) ⟨2502395, by rfl⟩ : syracuseStep 3336527 = 5004791) B5004791
theorem B2224351 : Blo 2053435 2224351 := bstep (se 1 (by rfl) ⟨1668263, by rfl⟩ : syracuseStep 2224351 = 3336527) B3336527
theorem B2965801 : Blo 2053435 2965801 := bstep (se 2 (by rfl) ⟨1112175, by rfl⟩ : syracuseStep 2965801 = 2224351) B2224351
theorem B3954401 : Blo 2053435 3954401 := bstep (se 2 (by rfl) ⟨1482900, by rfl⟩ : syracuseStep 3954401 = 2965801) B2965801
theorem B42180277 : Blo 2053435 42180277 := bstep (se 5 (by rfl) ⟨1977200, by rfl⟩ : syracuseStep 42180277 = 3954401) B3954401
theorem B56240369 : Blo 2053435 56240369 := bstep (se 2 (by rfl) ⟨21090138, by rfl⟩ : syracuseStep 56240369 = 42180277) B42180277
theorem B37493579 : Blo 2053435 37493579 := bstep (se 1 (by rfl) ⟨28120184, by rfl⟩ : syracuseStep 37493579 = 56240369) B56240369
theorem B24995719 : Blo 2053435 24995719 := bstep (se 1 (by rfl) ⟨18746789, by rfl⟩ : syracuseStep 24995719 = 37493579) B37493579
theorem B33327625 : Blo 2053435 33327625 := bstep (se 2 (by rfl) ⟨12497859, by rfl⟩ : syracuseStep 33327625 = 24995719) B24995719
theorem B44436833 : Blo 2053435 44436833 := bstep (se 2 (by rfl) ⟨16663812, by rfl⟩ : syracuseStep 44436833 = 33327625) B33327625
theorem B29624555 : Blo 2053435 29624555 := bstep (se 1 (by rfl) ⟨22218416, by rfl⟩ : syracuseStep 29624555 = 44436833) B44436833
theorem B19749703 : Blo 2053435 19749703 := bstep (se 1 (by rfl) ⟨14812277, by rfl⟩ : syracuseStep 19749703 = 29624555) B29624555
theorem B26332937 : Blo 2053435 26332937 := bstep (se 2 (by rfl) ⟨9874851, by rfl⟩ : syracuseStep 26332937 = 19749703) B19749703
theorem B17555291 : Blo 2053435 17555291 := bstep (se 1 (by rfl) ⟨13166468, by rfl⟩ : syracuseStep 17555291 = 26332937) B26332937
theorem B11703527 : Blo 2053435 11703527 := bstep (se 1 (by rfl) ⟨8777645, by rfl⟩ : syracuseStep 11703527 = 17555291) B17555291
theorem B7802351 : Blo 2053435 7802351 := bstep (se 1 (by rfl) ⟨5851763, by rfl⟩ : syracuseStep 7802351 = 11703527) B11703527
theorem B5201567 : Blo 2053435 5201567 := bstep (se 1 (by rfl) ⟨3901175, by rfl⟩ : syracuseStep 5201567 = 7802351) B7802351
theorem B3467711 : Blo 2053435 3467711 := bstep (se 1 (by rfl) ⟨2600783, by rfl⟩ : syracuseStep 3467711 = 5201567) B5201567
theorem B2311807 : Blo 2053435 2311807 := bstep (se 1 (by rfl) ⟨1733855, by rfl⟩ : syracuseStep 2311807 = 3467711) B3467711
theorem B3082409 : Blo 2053435 3082409 := bstep (se 2 (by rfl) ⟨1155903, by rfl⟩ : syracuseStep 3082409 = 2311807) B2311807
theorem B2054939 : Blo 2053435 2054939 := bstep (se 1 (by rfl) ⟨1541204, by rfl⟩ : syracuseStep 2054939 = 3082409) B3082409
theorem B2636273 : Blo 2053435 2636273 := bbase (se 2 (by rfl) ⟨988602, by rfl⟩ : syracuseStep 2636273 = 1977205) (by norm_num)
theorem B7030061 : Blo 2053435 7030061 := bstep (se 3 (by rfl) ⟨1318136, by rfl⟩ : syracuseStep 7030061 = 2636273) B2636273
theorem B4686707 : Blo 2053435 4686707 := bstep (se 1 (by rfl) ⟨3515030, by rfl⟩ : syracuseStep 4686707 = 7030061) B7030061
theorem B12497885 : Blo 2053435 12497885 := bstep (se 3 (by rfl) ⟨2343353, by rfl⟩ : syracuseStep 12497885 = 4686707) B4686707
theorem B8331923 : Blo 2053435 8331923 := bstep (se 1 (by rfl) ⟨6248942, by rfl⟩ : syracuseStep 8331923 = 12497885) B12497885
theorem B22218461 : Blo 2053435 22218461 := bstep (se 3 (by rfl) ⟨4165961, by rfl⟩ : syracuseStep 22218461 = 8331923) B8331923
theorem B14812307 : Blo 2053435 14812307 := bstep (se 1 (by rfl) ⟨11109230, by rfl⟩ : syracuseStep 14812307 = 22218461) B22218461
theorem B9874871 : Blo 2053435 9874871 := bstep (se 1 (by rfl) ⟨7406153, by rfl⟩ : syracuseStep 9874871 = 14812307) B14812307
theorem B6583247 : Blo 2053435 6583247 := bstep (se 1 (by rfl) ⟨4937435, by rfl⟩ : syracuseStep 6583247 = 9874871) B9874871
theorem B4388831 : Blo 2053435 4388831 := bstep (se 1 (by rfl) ⟨3291623, by rfl⟩ : syracuseStep 4388831 = 6583247) B6583247
theorem B2925887 : Blo 2053435 2925887 := bstep (se 1 (by rfl) ⟨2194415, by rfl⟩ : syracuseStep 2925887 = 4388831) B4388831
theorem B7802365 : Blo 2053435 7802365 := bstep (se 3 (by rfl) ⟨1462943, by rfl⟩ : syracuseStep 7802365 = 2925887) B2925887
theorem B10403153 : Blo 2053435 10403153 := bstep (se 2 (by rfl) ⟨3901182, by rfl⟩ : syracuseStep 10403153 = 7802365) B7802365
theorem B6935435 : Blo 2053435 6935435 := bstep (se 1 (by rfl) ⟨5201576, by rfl⟩ : syracuseStep 6935435 = 10403153) B10403153
theorem B4623623 : Blo 2053435 4623623 := bstep (se 1 (by rfl) ⟨3467717, by rfl⟩ : syracuseStep 4623623 = 6935435) B6935435
theorem B3082415 : Blo 2053435 3082415 := bstep (se 1 (by rfl) ⟨2311811, by rfl⟩ : syracuseStep 3082415 = 4623623) B4623623
theorem B2054943 : Blo 2053435 2054943 := bstep (se 1 (by rfl) ⟨1541207, by rfl⟩ : syracuseStep 2054943 = 3082415) B3082415
theorem B3082421 : Blo 2053435 3082421 := bbase (se 5 (by rfl) ⟨144488, by rfl⟩ : syracuseStep 3082421 = 288977) (by norm_num)
theorem B2054947 : Blo 2053435 2054947 := bstep (se 1 (by rfl) ⟨1541210, by rfl⟩ : syracuseStep 2054947 = 3082421) B3082421
theorem B5201597 : Blo 2053435 5201597 := bbase (se 3 (by rfl) ⟨975299, by rfl⟩ : syracuseStep 5201597 = 1950599) (by norm_num)
theorem B3467731 : Blo 2053435 3467731 := bstep (se 1 (by rfl) ⟨2600798, by rfl⟩ : syracuseStep 3467731 = 5201597) B5201597
theorem B4623641 : Blo 2053435 4623641 := bstep (se 2 (by rfl) ⟨1733865, by rfl⟩ : syracuseStep 4623641 = 3467731) B3467731
theorem B3082427 : Blo 2053435 3082427 := bstep (se 1 (by rfl) ⟨2311820, by rfl⟩ : syracuseStep 3082427 = 4623641) B4623641
theorem B2054951 : Blo 2053435 2054951 := bstep (se 1 (by rfl) ⟨1541213, by rfl⟩ : syracuseStep 2054951 = 3082427) B3082427
theorem B2311825 : Blo 2053435 2311825 := bbase (se 2 (by rfl) ⟨866934, by rfl⟩ : syracuseStep 2311825 = 1733869) (by norm_num)
theorem B3082433 : Blo 2053435 3082433 := bstep (se 2 (by rfl) ⟨1155912, by rfl⟩ : syracuseStep 3082433 = 2311825) B2311825
theorem B2054955 : Blo 2053435 2054955 := bstep (se 1 (by rfl) ⟨1541216, by rfl⟩ : syracuseStep 2054955 = 3082433) B3082433
theorem B3901213 : Blo 2053435 3901213 := bbase (se 3 (by rfl) ⟨731477, by rfl⟩ : syracuseStep 3901213 = 1462955) (by norm_num)
theorem B5201617 : Blo 2053435 5201617 := bstep (se 2 (by rfl) ⟨1950606, by rfl⟩ : syracuseStep 5201617 = 3901213) B3901213
theorem B6935489 : Blo 2053435 6935489 := bstep (se 2 (by rfl) ⟨2600808, by rfl⟩ : syracuseStep 6935489 = 5201617) B5201617
theorem B4623659 : Blo 2053435 4623659 := bstep (se 1 (by rfl) ⟨3467744, by rfl⟩ : syracuseStep 4623659 = 6935489) B6935489
theorem B3082439 : Blo 2053435 3082439 := bstep (se 1 (by rfl) ⟨2311829, by rfl⟩ : syracuseStep 3082439 = 4623659) B4623659
theorem B2054959 : Blo 2053435 2054959 := bstep (se 1 (by rfl) ⟨1541219, by rfl⟩ : syracuseStep 2054959 = 3082439) B3082439
theorem B3082445 : Blo 2053435 3082445 := bbase (se 3 (by rfl) ⟨577958, by rfl⟩ : syracuseStep 3082445 = 1155917) (by norm_num)
theorem B2054963 : Blo 2053435 2054963 := bstep (se 1 (by rfl) ⟨1541222, by rfl⟩ : syracuseStep 2054963 = 3082445) B3082445
theorem B4623677 : Blo 2053435 4623677 := bbase (se 3 (by rfl) ⟨866939, by rfl⟩ : syracuseStep 4623677 = 1733879) (by norm_num)
theorem B3082451 : Blo 2053435 3082451 := bstep (se 1 (by rfl) ⟨2311838, by rfl⟩ : syracuseStep 3082451 = 4623677) B4623677
theorem B2054967 : Blo 2053435 2054967 := bstep (se 1 (by rfl) ⟨1541225, by rfl⟩ : syracuseStep 2054967 = 3082451) B3082451
theorem B3467765 : Blo 2053435 3467765 := bbase (se 5 (by rfl) ⟨162551, by rfl⟩ : syracuseStep 3467765 = 325103) (by norm_num)
theorem B2311843 : Blo 2053435 2311843 := bstep (se 1 (by rfl) ⟨1733882, by rfl⟩ : syracuseStep 2311843 = 3467765) B3467765
theorem B3082457 : Blo 2053435 3082457 := bstep (se 2 (by rfl) ⟨1155921, by rfl⟩ : syracuseStep 3082457 = 2311843) B2311843
theorem B2054971 : Blo 2053435 2054971 := bstep (se 1 (by rfl) ⟨1541228, by rfl⟩ : syracuseStep 2054971 = 3082457) B3082457
theorem B6583349 : Blo 2053435 6583349 := bbase (se 5 (by rfl) ⟨308594, by rfl⟩ : syracuseStep 6583349 = 617189) (by norm_num)
theorem B4388899 : Blo 2053435 4388899 := bstep (se 1 (by rfl) ⟨3291674, by rfl⟩ : syracuseStep 4388899 = 6583349) B6583349
theorem B5851865 : Blo 2053435 5851865 := bstep (se 2 (by rfl) ⟨2194449, by rfl⟩ : syracuseStep 5851865 = 4388899) B4388899
theorem B15604973 : Blo 2053435 15604973 := bstep (se 3 (by rfl) ⟨2925932, by rfl⟩ : syracuseStep 15604973 = 5851865) B5851865
theorem B10403315 : Blo 2053435 10403315 := bstep (se 1 (by rfl) ⟨7802486, by rfl⟩ : syracuseStep 10403315 = 15604973) B15604973
theorem B6935543 : Blo 2053435 6935543 := bstep (se 1 (by rfl) ⟨5201657, by rfl⟩ : syracuseStep 6935543 = 10403315) B10403315
theorem B4623695 : Blo 2053435 4623695 := bstep (se 1 (by rfl) ⟨3467771, by rfl⟩ : syracuseStep 4623695 = 6935543) B6935543
theorem B3082463 : Blo 2053435 3082463 := bstep (se 1 (by rfl) ⟨2311847, by rfl⟩ : syracuseStep 3082463 = 4623695) B4623695
theorem B2054975 : Blo 2053435 2054975 := bstep (se 1 (by rfl) ⟨1541231, by rfl⟩ : syracuseStep 2054975 = 3082463) B3082463
theorem B3082469 : Blo 2053435 3082469 := bbase (se 4 (by rfl) ⟨288981, by rfl⟩ : syracuseStep 3082469 = 577963) (by norm_num)
theorem B2054979 : Blo 2053435 2054979 := bstep (se 1 (by rfl) ⟨1541234, by rfl⟩ : syracuseStep 2054979 = 3082469) B3082469
theorem B4388917 : Blo 2053435 4388917 := bbase (se 5 (by rfl) ⟨205730, by rfl⟩ : syracuseStep 4388917 = 411461) (by norm_num)
theorem B5851889 : Blo 2053435 5851889 := bstep (se 2 (by rfl) ⟨2194458, by rfl⟩ : syracuseStep 5851889 = 4388917) B4388917
theorem B3901259 : Blo 2053435 3901259 := bstep (se 1 (by rfl) ⟨2925944, by rfl⟩ : syracuseStep 3901259 = 5851889) B5851889
theorem B2600839 : Blo 2053435 2600839 := bstep (se 1 (by rfl) ⟨1950629, by rfl⟩ : syracuseStep 2600839 = 3901259) B3901259
theorem B3467785 : Blo 2053435 3467785 := bstep (se 2 (by rfl) ⟨1300419, by rfl⟩ : syracuseStep 3467785 = 2600839) B2600839
theorem B4623713 : Blo 2053435 4623713 := bstep (se 2 (by rfl) ⟨1733892, by rfl⟩ : syracuseStep 4623713 = 3467785) B3467785
theorem B3082475 : Blo 2053435 3082475 := bstep (se 1 (by rfl) ⟨2311856, by rfl⟩ : syracuseStep 3082475 = 4623713) B4623713
theorem B2054983 : Blo 2053435 2054983 := bstep (se 1 (by rfl) ⟨1541237, by rfl⟩ : syracuseStep 2054983 = 3082475) B3082475
theorem B2311861 : Blo 2053435 2311861 := bbase (se 5 (by rfl) ⟨108368, by rfl⟩ : syracuseStep 2311861 = 216737) (by norm_num)
theorem B3082481 : Blo 2053435 3082481 := bstep (se 2 (by rfl) ⟨1155930, by rfl⟩ : syracuseStep 3082481 = 2311861) B2311861
theorem B2054987 : Blo 2053435 2054987 := bstep (se 1 (by rfl) ⟨1541240, by rfl⟩ : syracuseStep 2054987 = 3082481) B3082481
theorem B2600849 : Blo 2053435 2600849 := bbase (se 2 (by rfl) ⟨975318, by rfl⟩ : syracuseStep 2600849 = 1950637) (by norm_num)
theorem B6935597 : Blo 2053435 6935597 := bstep (se 3 (by rfl) ⟨1300424, by rfl⟩ : syracuseStep 6935597 = 2600849) B2600849
theorem B4623731 : Blo 2053435 4623731 := bstep (se 1 (by rfl) ⟨3467798, by rfl⟩ : syracuseStep 4623731 = 6935597) B6935597
theorem B3082487 : Blo 2053435 3082487 := bstep (se 1 (by rfl) ⟨2311865, by rfl⟩ : syracuseStep 3082487 = 4623731) B4623731
theorem B2054991 : Blo 2053435 2054991 := bstep (se 1 (by rfl) ⟨1541243, by rfl⟩ : syracuseStep 2054991 = 3082487) B3082487
theorem B3082493 : Blo 2053435 3082493 := bbase (se 3 (by rfl) ⟨577967, by rfl⟩ : syracuseStep 3082493 = 1155935) (by norm_num)
theorem B2054995 : Blo 2053435 2054995 := bstep (se 1 (by rfl) ⟨1541246, by rfl⟩ : syracuseStep 2054995 = 3082493) B3082493
theorem B4623749 : Blo 2053435 4623749 := bbase (se 4 (by rfl) ⟨433476, by rfl⟩ : syracuseStep 4623749 = 866953) (by norm_num)
theorem B3082499 : Blo 2053435 3082499 := bstep (se 1 (by rfl) ⟨2311874, by rfl⟩ : syracuseStep 3082499 = 4623749) B4623749
theorem B2054999 : Blo 2053435 2054999 := bstep (se 1 (by rfl) ⟨1541249, by rfl⟩ : syracuseStep 2054999 = 3082499) B3082499
theorem B2925973 : Blo 2053435 2925973 := bbase (se 6 (by rfl) ⟨68577, by rfl⟩ : syracuseStep 2925973 = 137155) (by norm_num)
theorem B3901297 : Blo 2053435 3901297 := bstep (se 2 (by rfl) ⟨1462986, by rfl⟩ : syracuseStep 3901297 = 2925973) B2925973
theorem B5201729 : Blo 2053435 5201729 := bstep (se 2 (by rfl) ⟨1950648, by rfl⟩ : syracuseStep 5201729 = 3901297) B3901297
theorem B3467819 : Blo 2053435 3467819 := bstep (se 1 (by rfl) ⟨2600864, by rfl⟩ : syracuseStep 3467819 = 5201729) B5201729
theorem B2311879 : Blo 2053435 2311879 := bstep (se 1 (by rfl) ⟨1733909, by rfl⟩ : syracuseStep 2311879 = 3467819) B3467819
theorem B3082505 : Blo 2053435 3082505 := bstep (se 2 (by rfl) ⟨1155939, by rfl⟩ : syracuseStep 3082505 = 2311879) B2311879
theorem B2055003 : Blo 2053435 2055003 := bstep (se 1 (by rfl) ⟨1541252, by rfl⟩ : syracuseStep 2055003 = 3082505) B3082505
theorem B10403477 : Blo 2053435 10403477 := bbase (se 6 (by rfl) ⟨243831, by rfl⟩ : syracuseStep 10403477 = 487663) (by norm_num)
theorem B6935651 : Blo 2053435 6935651 := bstep (se 1 (by rfl) ⟨5201738, by rfl⟩ : syracuseStep 6935651 = 10403477) B10403477
theorem B4623767 : Blo 2053435 4623767 := bstep (se 1 (by rfl) ⟨3467825, by rfl⟩ : syracuseStep 4623767 = 6935651) B6935651
theorem B3082511 : Blo 2053435 3082511 := bstep (se 1 (by rfl) ⟨2311883, by rfl⟩ : syracuseStep 3082511 = 4623767) B4623767
theorem B2055007 : Blo 2053435 2055007 := bstep (se 1 (by rfl) ⟨1541255, by rfl⟩ : syracuseStep 2055007 = 3082511) B3082511
theorem B3082517 : Blo 2053435 3082517 := bbase (se 6 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 3082517 = 144493) (by norm_num)
theorem B2055011 : Blo 2053435 2055011 := bstep (se 1 (by rfl) ⟨1541258, by rfl⟩ : syracuseStep 2055011 = 3082517) B3082517
theorem B26333909 : Blo 2053435 26333909 := bbase (se 7 (by rfl) ⟨308600, by rfl⟩ : syracuseStep 26333909 = 617201) (by norm_num)
theorem B17555939 : Blo 2053435 17555939 := bstep (se 1 (by rfl) ⟨13166954, by rfl⟩ : syracuseStep 17555939 = 26333909) B26333909
theorem B11703959 : Blo 2053435 11703959 := bstep (se 1 (by rfl) ⟨8777969, by rfl⟩ : syracuseStep 11703959 = 17555939) B17555939
theorem B7802639 : Blo 2053435 7802639 := bstep (se 1 (by rfl) ⟨5851979, by rfl⟩ : syracuseStep 7802639 = 11703959) B11703959
theorem B5201759 : Blo 2053435 5201759 := bstep (se 1 (by rfl) ⟨3901319, by rfl⟩ : syracuseStep 5201759 = 7802639) B7802639
theorem B3467839 : Blo 2053435 3467839 := bstep (se 1 (by rfl) ⟨2600879, by rfl⟩ : syracuseStep 3467839 = 5201759) B5201759
theorem B4623785 : Blo 2053435 4623785 := bstep (se 2 (by rfl) ⟨1733919, by rfl⟩ : syracuseStep 4623785 = 3467839) B3467839
theorem B3082523 : Blo 2053435 3082523 := bstep (se 1 (by rfl) ⟨2311892, by rfl⟩ : syracuseStep 3082523 = 4623785) B4623785
theorem B2055015 : Blo 2053435 2055015 := bstep (se 1 (by rfl) ⟨1541261, by rfl⟩ : syracuseStep 2055015 = 3082523) B3082523
theorem B2311897 : Blo 2053435 2311897 := bbase (se 2 (by rfl) ⟨866961, by rfl⟩ : syracuseStep 2311897 = 1733923) (by norm_num)
theorem B3082529 : Blo 2053435 3082529 := bstep (se 2 (by rfl) ⟨1155948, by rfl⟩ : syracuseStep 3082529 = 2311897) B2311897
theorem B2055019 : Blo 2053435 2055019 := bstep (se 1 (by rfl) ⟨1541264, by rfl⟩ : syracuseStep 2055019 = 3082529) B3082529
theorem B2194501 : Blo 2053435 2194501 := bbase (se 4 (by rfl) ⟨205734, by rfl⟩ : syracuseStep 2194501 = 411469) (by norm_num)
theorem B2926001 : Blo 2053435 2926001 := bstep (se 2 (by rfl) ⟨1097250, by rfl⟩ : syracuseStep 2926001 = 2194501) B2194501
theorem B7802669 : Blo 2053435 7802669 := bstep (se 3 (by rfl) ⟨1463000, by rfl⟩ : syracuseStep 7802669 = 2926001) B2926001
theorem B5201779 : Blo 2053435 5201779 := bstep (se 1 (by rfl) ⟨3901334, by rfl⟩ : syracuseStep 5201779 = 7802669) B7802669
theorem B6935705 : Blo 2053435 6935705 := bstep (se 2 (by rfl) ⟨2600889, by rfl⟩ : syracuseStep 6935705 = 5201779) B5201779
theorem B4623803 : Blo 2053435 4623803 := bstep (se 1 (by rfl) ⟨3467852, by rfl⟩ : syracuseStep 4623803 = 6935705) B6935705
theorem B3082535 : Blo 2053435 3082535 := bstep (se 1 (by rfl) ⟨2311901, by rfl⟩ : syracuseStep 3082535 = 4623803) B4623803
theorem B2055023 : Blo 2053435 2055023 := bstep (se 1 (by rfl) ⟨1541267, by rfl⟩ : syracuseStep 2055023 = 3082535) B3082535
theorem B3082541 : Blo 2053435 3082541 := bbase (se 3 (by rfl) ⟨577976, by rfl⟩ : syracuseStep 3082541 = 1155953) (by norm_num)
theorem B2055027 : Blo 2053435 2055027 := bstep (se 1 (by rfl) ⟨1541270, by rfl⟩ : syracuseStep 2055027 = 3082541) B3082541
theorem B4623821 : Blo 2053435 4623821 := bbase (se 3 (by rfl) ⟨866966, by rfl⟩ : syracuseStep 4623821 = 1733933) (by norm_num)
theorem B3082547 : Blo 2053435 3082547 := bstep (se 1 (by rfl) ⟨2311910, by rfl⟩ : syracuseStep 3082547 = 4623821) B4623821
theorem B2055031 : Blo 2053435 2055031 := bstep (se 1 (by rfl) ⟨1541273, by rfl⟩ : syracuseStep 2055031 = 3082547) B3082547
theorem B2600905 : Blo 2053435 2600905 := bbase (se 2 (by rfl) ⟨975339, by rfl⟩ : syracuseStep 2600905 = 1950679) (by norm_num)
theorem B3467873 : Blo 2053435 3467873 := bstep (se 2 (by rfl) ⟨1300452, by rfl⟩ : syracuseStep 3467873 = 2600905) B2600905
theorem B2311915 : Blo 2053435 2311915 := bstep (se 1 (by rfl) ⟨1733936, by rfl⟩ : syracuseStep 2311915 = 3467873) B3467873
theorem B3082553 : Blo 2053435 3082553 := bstep (se 2 (by rfl) ⟨1155957, by rfl⟩ : syracuseStep 3082553 = 2311915) B2311915
theorem B2055035 : Blo 2053435 2055035 := bstep (se 1 (by rfl) ⟨1541276, by rfl⟩ : syracuseStep 2055035 = 3082553) B3082553
theorem B2777437 : Blo 2053435 2777437 := bbase (se 3 (by rfl) ⟨520769, by rfl⟩ : syracuseStep 2777437 = 1041539) (by norm_num)
theorem B3703249 : Blo 2053435 3703249 := bstep (se 2 (by rfl) ⟨1388718, by rfl⟩ : syracuseStep 3703249 = 2777437) B2777437
theorem B19750661 : Blo 2053435 19750661 := bstep (se 4 (by rfl) ⟨1851624, by rfl⟩ : syracuseStep 19750661 = 3703249) B3703249
theorem B13167107 : Blo 2053435 13167107 := bstep (se 1 (by rfl) ⟨9875330, by rfl⟩ : syracuseStep 13167107 = 19750661) B19750661
theorem B8778071 : Blo 2053435 8778071 := bstep (se 1 (by rfl) ⟨6583553, by rfl⟩ : syracuseStep 8778071 = 13167107) B13167107
theorem B23408189 : Blo 2053435 23408189 := bstep (se 3 (by rfl) ⟨4389035, by rfl⟩ : syracuseStep 23408189 = 8778071) B8778071
theorem B15605459 : Blo 2053435 15605459 := bstep (se 1 (by rfl) ⟨11704094, by rfl⟩ : syracuseStep 15605459 = 23408189) B23408189
theorem B10403639 : Blo 2053435 10403639 := bstep (se 1 (by rfl) ⟨7802729, by rfl⟩ : syracuseStep 10403639 = 15605459) B15605459
theorem B6935759 : Blo 2053435 6935759 := bstep (se 1 (by rfl) ⟨5201819, by rfl⟩ : syracuseStep 6935759 = 10403639) B10403639
theorem B4623839 : Blo 2053435 4623839 := bstep (se 1 (by rfl) ⟨3467879, by rfl⟩ : syracuseStep 4623839 = 6935759) B6935759
theorem B3082559 : Blo 2053435 3082559 := bstep (se 1 (by rfl) ⟨2311919, by rfl⟩ : syracuseStep 3082559 = 4623839) B4623839
theorem B2055039 : Blo 2053435 2055039 := bstep (se 1 (by rfl) ⟨1541279, by rfl⟩ : syracuseStep 2055039 = 3082559) B3082559
theorem B3082565 : Blo 2053435 3082565 := bbase (se 4 (by rfl) ⟨288990, by rfl⟩ : syracuseStep 3082565 = 577981) (by norm_num)
theorem B2055043 : Blo 2053435 2055043 := bstep (se 1 (by rfl) ⟨1541282, by rfl⟩ : syracuseStep 2055043 = 3082565) B3082565
theorem B3467893 : Blo 2053435 3467893 := bbase (se 5 (by rfl) ⟨162557, by rfl⟩ : syracuseStep 3467893 = 325115) (by norm_num)
theorem B4623857 : Blo 2053435 4623857 := bstep (se 2 (by rfl) ⟨1733946, by rfl⟩ : syracuseStep 4623857 = 3467893) B3467893
theorem B3082571 : Blo 2053435 3082571 := bstep (se 1 (by rfl) ⟨2311928, by rfl⟩ : syracuseStep 3082571 = 4623857) B4623857
theorem B2055047 : Blo 2053435 2055047 := bstep (se 1 (by rfl) ⟨1541285, by rfl⟩ : syracuseStep 2055047 = 3082571) B3082571
theorem B2311933 : Blo 2053435 2311933 := bbase (se 3 (by rfl) ⟨433487, by rfl⟩ : syracuseStep 2311933 = 866975) (by norm_num)
theorem B3082577 : Blo 2053435 3082577 := bstep (se 2 (by rfl) ⟨1155966, by rfl⟩ : syracuseStep 3082577 = 2311933) B2311933
theorem B2055051 : Blo 2053435 2055051 := bstep (se 1 (by rfl) ⟨1541288, by rfl⟩ : syracuseStep 2055051 = 3082577) B3082577
theorem B6935813 : Blo 2053435 6935813 := bbase (se 4 (by rfl) ⟨650232, by rfl⟩ : syracuseStep 6935813 = 1300465) (by norm_num)
theorem B4623875 : Blo 2053435 4623875 := bstep (se 1 (by rfl) ⟨3467906, by rfl⟩ : syracuseStep 4623875 = 6935813) B6935813
theorem B3082583 : Blo 2053435 3082583 := bstep (se 1 (by rfl) ⟨2311937, by rfl⟩ : syracuseStep 3082583 = 4623875) B4623875
theorem B2055055 : Blo 2053435 2055055 := bstep (se 1 (by rfl) ⟨1541291, by rfl⟩ : syracuseStep 2055055 = 3082583) B3082583
theorem B3082589 : Blo 2053435 3082589 := bbase (se 3 (by rfl) ⟨577985, by rfl⟩ : syracuseStep 3082589 = 1155971) (by norm_num)
theorem B2055059 : Blo 2053435 2055059 := bstep (se 1 (by rfl) ⟨1541294, by rfl⟩ : syracuseStep 2055059 = 3082589) B3082589
theorem B4623893 : Blo 2053435 4623893 := bbase (se 6 (by rfl) ⟨108372, by rfl⟩ : syracuseStep 4623893 = 216745) (by norm_num)
theorem B3082595 : Blo 2053435 3082595 := bstep (se 1 (by rfl) ⟨2311946, by rfl⟩ : syracuseStep 3082595 = 4623893) B4623893
theorem B2055063 : Blo 2053435 2055063 := bstep (se 1 (by rfl) ⟨1541297, by rfl⟩ : syracuseStep 2055063 = 3082595) B3082595
theorem B7802837 : Blo 2053435 7802837 := bbase (se 7 (by rfl) ⟨91439, by rfl⟩ : syracuseStep 7802837 = 182879) (by norm_num)
theorem B5201891 : Blo 2053435 5201891 := bstep (se 1 (by rfl) ⟨3901418, by rfl⟩ : syracuseStep 5201891 = 7802837) B7802837
theorem B3467927 : Blo 2053435 3467927 := bstep (se 1 (by rfl) ⟨2600945, by rfl⟩ : syracuseStep 3467927 = 5201891) B5201891
theorem B2311951 : Blo 2053435 2311951 := bstep (se 1 (by rfl) ⟨1733963, by rfl⟩ : syracuseStep 2311951 = 3467927) B3467927
theorem B3082601 : Blo 2053435 3082601 := bstep (se 2 (by rfl) ⟨1155975, by rfl⟩ : syracuseStep 3082601 = 2311951) B2311951
theorem B2055067 : Blo 2053435 2055067 := bstep (se 1 (by rfl) ⟨1541300, by rfl⟩ : syracuseStep 2055067 = 3082601) B3082601
theorem B11704277 : Blo 2053435 11704277 := bbase (se 7 (by rfl) ⟨137159, by rfl⟩ : syracuseStep 11704277 = 274319) (by norm_num)
theorem B7802851 : Blo 2053435 7802851 := bstep (se 1 (by rfl) ⟨5852138, by rfl⟩ : syracuseStep 7802851 = 11704277) B11704277
theorem B10403801 : Blo 2053435 10403801 := bstep (se 2 (by rfl) ⟨3901425, by rfl⟩ : syracuseStep 10403801 = 7802851) B7802851
theorem B6935867 : Blo 2053435 6935867 := bstep (se 1 (by rfl) ⟨5201900, by rfl⟩ : syracuseStep 6935867 = 10403801) B10403801
theorem B4623911 : Blo 2053435 4623911 := bstep (se 1 (by rfl) ⟨3467933, by rfl⟩ : syracuseStep 4623911 = 6935867) B6935867
theorem B3082607 : Blo 2053435 3082607 := bstep (se 1 (by rfl) ⟨2311955, by rfl⟩ : syracuseStep 3082607 = 4623911) B4623911
theorem B2055071 : Blo 2053435 2055071 := bstep (se 1 (by rfl) ⟨1541303, by rfl⟩ : syracuseStep 2055071 = 3082607) B3082607
theorem B3082613 : Blo 2053435 3082613 := bbase (se 5 (by rfl) ⟨144497, by rfl⟩ : syracuseStep 3082613 = 288995) (by norm_num)
theorem B2055075 : Blo 2053435 2055075 := bstep (se 1 (by rfl) ⟨1541306, by rfl⟩ : syracuseStep 2055075 = 3082613) B3082613
theorem B2194561 : Blo 2053435 2194561 := bbase (se 2 (by rfl) ⟨822960, by rfl⟩ : syracuseStep 2194561 = 1645921) (by norm_num)
theorem B2926081 : Blo 2053435 2926081 := bstep (se 2 (by rfl) ⟨1097280, by rfl⟩ : syracuseStep 2926081 = 2194561) B2194561
theorem B3901441 : Blo 2053435 3901441 := bstep (se 2 (by rfl) ⟨1463040, by rfl⟩ : syracuseStep 3901441 = 2926081) B2926081
theorem B5201921 : Blo 2053435 5201921 := bstep (se 2 (by rfl) ⟨1950720, by rfl⟩ : syracuseStep 5201921 = 3901441) B3901441
theorem B3467947 : Blo 2053435 3467947 := bstep (se 1 (by rfl) ⟨2600960, by rfl⟩ : syracuseStep 3467947 = 5201921) B5201921
theorem B4623929 : Blo 2053435 4623929 := bstep (se 2 (by rfl) ⟨1733973, by rfl⟩ : syracuseStep 4623929 = 3467947) B3467947
theorem B3082619 : Blo 2053435 3082619 := bstep (se 1 (by rfl) ⟨2311964, by rfl⟩ : syracuseStep 3082619 = 4623929) B4623929
theorem B2055079 : Blo 2053435 2055079 := bstep (se 1 (by rfl) ⟨1541309, by rfl⟩ : syracuseStep 2055079 = 3082619) B3082619
theorem B2311969 : Blo 2053435 2311969 := bbase (se 2 (by rfl) ⟨866988, by rfl⟩ : syracuseStep 2311969 = 1733977) (by norm_num)
theorem B3082625 : Blo 2053435 3082625 := bstep (se 2 (by rfl) ⟨1155984, by rfl⟩ : syracuseStep 3082625 = 2311969) B2311969
theorem B2055083 : Blo 2053435 2055083 := bstep (se 1 (by rfl) ⟨1541312, by rfl⟩ : syracuseStep 2055083 = 3082625) B3082625
theorem B5201941 : Blo 2053435 5201941 := bbase (se 6 (by rfl) ⟨121920, by rfl⟩ : syracuseStep 5201941 = 243841) (by norm_num)
theorem B6935921 : Blo 2053435 6935921 := bstep (se 2 (by rfl) ⟨2600970, by rfl⟩ : syracuseStep 6935921 = 5201941) B5201941
theorem B4623947 : Blo 2053435 4623947 := bstep (se 1 (by rfl) ⟨3467960, by rfl⟩ : syracuseStep 4623947 = 6935921) B6935921
theorem B3082631 : Blo 2053435 3082631 := bstep (se 1 (by rfl) ⟨2311973, by rfl⟩ : syracuseStep 3082631 = 4623947) B4623947
theorem B2055087 : Blo 2053435 2055087 := bstep (se 1 (by rfl) ⟨1541315, by rfl⟩ : syracuseStep 2055087 = 3082631) B3082631
theorem B3082637 : Blo 2053435 3082637 := bbase (se 3 (by rfl) ⟨577994, by rfl⟩ : syracuseStep 3082637 = 1155989) (by norm_num)
theorem B2055091 : Blo 2053435 2055091 := bstep (se 1 (by rfl) ⟨1541318, by rfl⟩ : syracuseStep 2055091 = 3082637) B3082637
theorem B4623965 : Blo 2053435 4623965 := bbase (se 3 (by rfl) ⟨866993, by rfl⟩ : syracuseStep 4623965 = 1733987) (by norm_num)
theorem B3082643 : Blo 2053435 3082643 := bstep (se 1 (by rfl) ⟨2311982, by rfl⟩ : syracuseStep 3082643 = 4623965) B4623965
theorem B2055095 : Blo 2053435 2055095 := bstep (se 1 (by rfl) ⟨1541321, by rfl⟩ : syracuseStep 2055095 = 3082643) B3082643
theorem B3467981 : Blo 2053435 3467981 := bbase (se 3 (by rfl) ⟨650246, by rfl⟩ : syracuseStep 3467981 = 1300493) (by norm_num)
theorem B2311987 : Blo 2053435 2311987 := bstep (se 1 (by rfl) ⟨1733990, by rfl⟩ : syracuseStep 2311987 = 3467981) B3467981
theorem B3082649 : Blo 2053435 3082649 := bstep (se 2 (by rfl) ⟨1155993, by rfl⟩ : syracuseStep 3082649 = 2311987) B2311987
theorem B2055099 : Blo 2053435 2055099 := bstep (se 1 (by rfl) ⟨1541324, by rfl⟩ : syracuseStep 2055099 = 3082649) B3082649
theorem B90093397 : Blo 2053435 90093397 := bbase (se 9 (by rfl) ⟨263945, by rfl⟩ : syracuseStep 90093397 = 527891) (by norm_num)
theorem B120124529 : Blo 2053435 120124529 := bstep (se 2 (by rfl) ⟨45046698, by rfl⟩ : syracuseStep 120124529 = 90093397) B90093397
theorem B80083019 : Blo 2053435 80083019 := bstep (se 1 (by rfl) ⟨60062264, by rfl⟩ : syracuseStep 80083019 = 120124529) B120124529
theorem B53388679 : Blo 2053435 53388679 := bstep (se 1 (by rfl) ⟨40041509, by rfl⟩ : syracuseStep 53388679 = 80083019) B80083019
theorem B71184905 : Blo 2053435 71184905 := bstep (se 2 (by rfl) ⟨26694339, by rfl⟩ : syracuseStep 71184905 = 53388679) B53388679
theorem B47456603 : Blo 2053435 47456603 := bstep (se 1 (by rfl) ⟨35592452, by rfl⟩ : syracuseStep 47456603 = 71184905) B71184905
theorem B31637735 : Blo 2053435 31637735 := bstep (se 1 (by rfl) ⟨23728301, by rfl⟩ : syracuseStep 31637735 = 47456603) B47456603
theorem B21091823 : Blo 2053435 21091823 := bstep (se 1 (by rfl) ⟨15818867, by rfl⟩ : syracuseStep 21091823 = 31637735) B31637735
theorem B14061215 : Blo 2053435 14061215 := bstep (se 1 (by rfl) ⟨10545911, by rfl⟩ : syracuseStep 14061215 = 21091823) B21091823
theorem B9374143 : Blo 2053435 9374143 := bstep (se 1 (by rfl) ⟨7030607, by rfl⟩ : syracuseStep 9374143 = 14061215) B14061215
theorem B12498857 : Blo 2053435 12498857 := bstep (se 2 (by rfl) ⟨4687071, by rfl⟩ : syracuseStep 12498857 = 9374143) B9374143
theorem B8332571 : Blo 2053435 8332571 := bstep (se 1 (by rfl) ⟨6249428, by rfl⟩ : syracuseStep 8332571 = 12498857) B12498857
theorem B5555047 : Blo 2053435 5555047 := bstep (se 1 (by rfl) ⟨4166285, by rfl⟩ : syracuseStep 5555047 = 8332571) B8332571
theorem B7406729 : Blo 2053435 7406729 := bstep (se 2 (by rfl) ⟨2777523, by rfl⟩ : syracuseStep 7406729 = 5555047) B5555047
theorem B4937819 : Blo 2053435 4937819 := bstep (se 1 (by rfl) ⟨3703364, by rfl⟩ : syracuseStep 4937819 = 7406729) B7406729
theorem B13167517 : Blo 2053435 13167517 := bstep (se 3 (by rfl) ⟨2468909, by rfl⟩ : syracuseStep 13167517 = 4937819) B4937819
theorem B17556689 : Blo 2053435 17556689 := bstep (se 2 (by rfl) ⟨6583758, by rfl⟩ : syracuseStep 17556689 = 13167517) B13167517
theorem B11704459 : Blo 2053435 11704459 := bstep (se 1 (by rfl) ⟨8778344, by rfl⟩ : syracuseStep 11704459 = 17556689) B17556689
theorem B15605945 : Blo 2053435 15605945 := bstep (se 2 (by rfl) ⟨5852229, by rfl⟩ : syracuseStep 15605945 = 11704459) B11704459
theorem B10403963 : Blo 2053435 10403963 := bstep (se 1 (by rfl) ⟨7802972, by rfl⟩ : syracuseStep 10403963 = 15605945) B15605945
theorem B6935975 : Blo 2053435 6935975 := bstep (se 1 (by rfl) ⟨5201981, by rfl⟩ : syracuseStep 6935975 = 10403963) B10403963
theorem B4623983 : Blo 2053435 4623983 := bstep (se 1 (by rfl) ⟨3467987, by rfl⟩ : syracuseStep 4623983 = 6935975) B6935975
theorem B3082655 : Blo 2053435 3082655 := bstep (se 1 (by rfl) ⟨2311991, by rfl⟩ : syracuseStep 3082655 = 4623983) B4623983
theorem B2055103 : Blo 2053435 2055103 := bstep (se 1 (by rfl) ⟨1541327, by rfl⟩ : syracuseStep 2055103 = 3082655) B3082655
theorem B3082661 : Blo 2053435 3082661 := bbase (se 4 (by rfl) ⟨288999, by rfl⟩ : syracuseStep 3082661 = 577999) (by norm_num)
theorem B2055107 : Blo 2053435 2055107 := bstep (se 1 (by rfl) ⟨1541330, by rfl⟩ : syracuseStep 2055107 = 3082661) B3082661
theorem B2601001 : Blo 2053435 2601001 := bbase (se 2 (by rfl) ⟨975375, by rfl⟩ : syracuseStep 2601001 = 1950751) (by norm_num)
theorem B3468001 : Blo 2053435 3468001 := bstep (se 2 (by rfl) ⟨1300500, by rfl⟩ : syracuseStep 3468001 = 2601001) B2601001
theorem B4624001 : Blo 2053435 4624001 := bstep (se 2 (by rfl) ⟨1734000, by rfl⟩ : syracuseStep 4624001 = 3468001) B3468001
theorem B3082667 : Blo 2053435 3082667 := bstep (se 1 (by rfl) ⟨2312000, by rfl⟩ : syracuseStep 3082667 = 4624001) B4624001
theorem B2055111 : Blo 2053435 2055111 := bstep (se 1 (by rfl) ⟨1541333, by rfl⟩ : syracuseStep 2055111 = 3082667) B3082667
theorem B2312005 : Blo 2053435 2312005 := bbase (se 4 (by rfl) ⟨216750, by rfl⟩ : syracuseStep 2312005 = 433501) (by norm_num)
theorem B3082673 : Blo 2053435 3082673 := bstep (se 2 (by rfl) ⟨1156002, by rfl⟩ : syracuseStep 3082673 = 2312005) B2312005
theorem B2055115 : Blo 2053435 2055115 := bstep (se 1 (by rfl) ⟨1541336, by rfl⟩ : syracuseStep 2055115 = 3082673) B3082673
theorem B3901517 : Blo 2053435 3901517 := bbase (se 3 (by rfl) ⟨731534, by rfl⟩ : syracuseStep 3901517 = 1463069) (by norm_num)
theorem B2601011 : Blo 2053435 2601011 := bstep (se 1 (by rfl) ⟨1950758, by rfl⟩ : syracuseStep 2601011 = 3901517) B3901517
theorem B6936029 : Blo 2053435 6936029 := bstep (se 3 (by rfl) ⟨1300505, by rfl⟩ : syracuseStep 6936029 = 2601011) B2601011
theorem B4624019 : Blo 2053435 4624019 := bstep (se 1 (by rfl) ⟨3468014, by rfl⟩ : syracuseStep 4624019 = 6936029) B6936029
theorem B3082679 : Blo 2053435 3082679 := bstep (se 1 (by rfl) ⟨2312009, by rfl⟩ : syracuseStep 3082679 = 4624019) B4624019
theorem B2055119 : Blo 2053435 2055119 := bstep (se 1 (by rfl) ⟨1541339, by rfl⟩ : syracuseStep 2055119 = 3082679) B3082679
theorem B3082685 : Blo 2053435 3082685 := bbase (se 3 (by rfl) ⟨578003, by rfl⟩ : syracuseStep 3082685 = 1156007) (by norm_num)
theorem B2055123 : Blo 2053435 2055123 := bstep (se 1 (by rfl) ⟨1541342, by rfl⟩ : syracuseStep 2055123 = 3082685) B3082685
theorem B4624037 : Blo 2053435 4624037 := bbase (se 4 (by rfl) ⟨433503, by rfl⟩ : syracuseStep 4624037 = 867007) (by norm_num)
theorem B3082691 : Blo 2053435 3082691 := bstep (se 1 (by rfl) ⟨2312018, by rfl⟩ : syracuseStep 3082691 = 4624037) B4624037
theorem B2055127 : Blo 2053435 2055127 := bstep (se 1 (by rfl) ⟨1541345, by rfl⟩ : syracuseStep 2055127 = 3082691) B3082691
theorem B5202053 : Blo 2053435 5202053 := bbase (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) (by norm_num)
theorem B3468035 : Blo 2053435 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B2312023 : Blo 2053435 2312023 := bstep (se 1 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 2312023 = 3468035) B3468035
theorem B3082697 : Blo 2053435 3082697 := bstep (se 2 (by rfl) ⟨1156011, by rfl⟩ : syracuseStep 3082697 = 2312023) B2312023
theorem B2055131 : Blo 2053435 2055131 := bstep (se 1 (by rfl) ⟨1541348, by rfl⟩ : syracuseStep 2055131 = 3082697) B3082697
theorem B21379925 : Blo 2053435 21379925 := bbase (se 9 (by rfl) ⟨62636, by rfl⟩ : syracuseStep 21379925 = 125273) (by norm_num)
theorem B14253283 : Blo 2053435 14253283 := bstep (se 1 (by rfl) ⟨10689962, by rfl⟩ : syracuseStep 14253283 = 21379925) B21379925
theorem B19004377 : Blo 2053435 19004377 := bstep (se 2 (by rfl) ⟨7126641, by rfl⟩ : syracuseStep 19004377 = 14253283) B14253283
theorem B25339169 : Blo 2053435 25339169 := bstep (se 2 (by rfl) ⟨9502188, by rfl⟩ : syracuseStep 25339169 = 19004377) B19004377
theorem B67571117 : Blo 2053435 67571117 := bstep (se 3 (by rfl) ⟨12669584, by rfl⟩ : syracuseStep 67571117 = 25339169) B25339169
theorem B45047411 : Blo 2053435 45047411 := bstep (se 1 (by rfl) ⟨33785558, by rfl⟩ : syracuseStep 45047411 = 67571117) B67571117
theorem B30031607 : Blo 2053435 30031607 := bstep (se 1 (by rfl) ⟨22523705, by rfl⟩ : syracuseStep 30031607 = 45047411) B45047411
theorem B80084285 : Blo 2053435 80084285 := bstep (se 3 (by rfl) ⟨15015803, by rfl⟩ : syracuseStep 80084285 = 30031607) B30031607
theorem B53389523 : Blo 2053435 53389523 := bstep (se 1 (by rfl) ⟨40042142, by rfl⟩ : syracuseStep 53389523 = 80084285) B80084285
theorem B35593015 : Blo 2053435 35593015 := bstep (se 1 (by rfl) ⟨26694761, by rfl⟩ : syracuseStep 35593015 = 53389523) B53389523
theorem B47457353 : Blo 2053435 47457353 := bstep (se 2 (by rfl) ⟨17796507, by rfl⟩ : syracuseStep 47457353 = 35593015) B35593015
theorem B31638235 : Blo 2053435 31638235 := bstep (se 1 (by rfl) ⟨23728676, by rfl⟩ : syracuseStep 31638235 = 47457353) B47457353
theorem B42184313 : Blo 2053435 42184313 := bstep (se 2 (by rfl) ⟨15819117, by rfl⟩ : syracuseStep 42184313 = 31638235) B31638235
theorem B28122875 : Blo 2053435 28122875 := bstep (se 1 (by rfl) ⟨21092156, by rfl⟩ : syracuseStep 28122875 = 42184313) B42184313
theorem B18748583 : Blo 2053435 18748583 := bstep (se 1 (by rfl) ⟨14061437, by rfl⟩ : syracuseStep 18748583 = 28122875) B28122875
theorem B12499055 : Blo 2053435 12499055 := bstep (se 1 (by rfl) ⟨9374291, by rfl⟩ : syracuseStep 12499055 = 18748583) B18748583
theorem B8332703 : Blo 2053435 8332703 := bstep (se 1 (by rfl) ⟨6249527, by rfl⟩ : syracuseStep 8332703 = 12499055) B12499055
theorem B5555135 : Blo 2053435 5555135 := bstep (se 1 (by rfl) ⟨4166351, by rfl⟩ : syracuseStep 5555135 = 8332703) B8332703
theorem B3703423 : Blo 2053435 3703423 := bstep (se 1 (by rfl) ⟨2777567, by rfl⟩ : syracuseStep 3703423 = 5555135) B5555135
theorem B4937897 : Blo 2053435 4937897 := bstep (se 2 (by rfl) ⟨1851711, by rfl⟩ : syracuseStep 4937897 = 3703423) B3703423
theorem B3291931 : Blo 2053435 3291931 := bstep (se 1 (by rfl) ⟨2468948, by rfl⟩ : syracuseStep 3291931 = 4937897) B4937897
theorem B4389241 : Blo 2053435 4389241 := bstep (se 2 (by rfl) ⟨1645965, by rfl⟩ : syracuseStep 4389241 = 3291931) B3291931
theorem B5852321 : Blo 2053435 5852321 := bstep (se 2 (by rfl) ⟨2194620, by rfl⟩ : syracuseStep 5852321 = 4389241) B4389241
theorem B3901547 : Blo 2053435 3901547 := bstep (se 1 (by rfl) ⟨2926160, by rfl⟩ : syracuseStep 3901547 = 5852321) B5852321
theorem B10404125 : Blo 2053435 10404125 := bstep (se 3 (by rfl) ⟨1950773, by rfl⟩ : syracuseStep 10404125 = 3901547) B3901547
theorem B6936083 : Blo 2053435 6936083 := bstep (se 1 (by rfl) ⟨5202062, by rfl⟩ : syracuseStep 6936083 = 10404125) B10404125
theorem B4624055 : Blo 2053435 4624055 := bstep (se 1 (by rfl) ⟨3468041, by rfl⟩ : syracuseStep 4624055 = 6936083) B6936083
theorem B3082703 : Blo 2053435 3082703 := bstep (se 1 (by rfl) ⟨2312027, by rfl⟩ : syracuseStep 3082703 = 4624055) B4624055
theorem B2055135 : Blo 2053435 2055135 := bstep (se 1 (by rfl) ⟨1541351, by rfl⟩ : syracuseStep 2055135 = 3082703) B3082703
theorem B3082709 : Blo 2053435 3082709 := bbase (se 7 (by rfl) ⟨36125, by rfl⟩ : syracuseStep 3082709 = 72251) (by norm_num)
theorem B2055139 : Blo 2053435 2055139 := bstep (se 1 (by rfl) ⟨1541354, by rfl⟩ : syracuseStep 2055139 = 3082709) B3082709
theorem B7803125 : Blo 2053435 7803125 := bbase (se 5 (by rfl) ⟨365771, by rfl⟩ : syracuseStep 7803125 = 731543) (by norm_num)
theorem B5202083 : Blo 2053435 5202083 := bstep (se 1 (by rfl) ⟨3901562, by rfl⟩ : syracuseStep 5202083 = 7803125) B7803125
theorem B3468055 : Blo 2053435 3468055 := bstep (se 1 (by rfl) ⟨2601041, by rfl⟩ : syracuseStep 3468055 = 5202083) B5202083
theorem B4624073 : Blo 2053435 4624073 := bstep (se 2 (by rfl) ⟨1734027, by rfl⟩ : syracuseStep 4624073 = 3468055) B3468055
theorem B3082715 : Blo 2053435 3082715 := bstep (se 1 (by rfl) ⟨2312036, by rfl⟩ : syracuseStep 3082715 = 4624073) B4624073
theorem B2055143 : Blo 2053435 2055143 := bstep (se 1 (by rfl) ⟨1541357, by rfl⟩ : syracuseStep 2055143 = 3082715) B3082715
theorem B2312041 : Blo 2053435 2312041 := bbase (se 2 (by rfl) ⟨867015, by rfl⟩ : syracuseStep 2312041 = 1734031) (by norm_num)
theorem B3082721 : Blo 2053435 3082721 := bstep (se 2 (by rfl) ⟨1156020, by rfl⟩ : syracuseStep 3082721 = 2312041) B2312041
theorem B2055147 : Blo 2053435 2055147 := bstep (se 1 (by rfl) ⟨1541360, by rfl⟩ : syracuseStep 2055147 = 3082721) B3082721
theorem B3711197 : Blo 2053435 3711197 := bbase (se 3 (by rfl) ⟨695849, by rfl⟩ : syracuseStep 3711197 = 1391699) (by norm_num)
theorem B2474131 : Blo 2053435 2474131 := bstep (se 1 (by rfl) ⟨1855598, by rfl⟩ : syracuseStep 2474131 = 3711197) B3711197
theorem B3298841 : Blo 2053435 3298841 := bstep (se 2 (by rfl) ⟨1237065, by rfl⟩ : syracuseStep 3298841 = 2474131) B2474131
theorem B2199227 : Blo 2053435 2199227 := bstep (se 1 (by rfl) ⟨1649420, by rfl⟩ : syracuseStep 2199227 = 3298841) B3298841
theorem B5864605 : Blo 2053435 5864605 := bstep (se 3 (by rfl) ⟨1099613, by rfl⟩ : syracuseStep 5864605 = 2199227) B2199227
theorem B125111573 : Blo 2053435 125111573 := bstep (se 6 (by rfl) ⟨2932302, by rfl⟩ : syracuseStep 125111573 = 5864605) B5864605
theorem B83407715 : Blo 2053435 83407715 := bstep (se 1 (by rfl) ⟨62555786, by rfl⟩ : syracuseStep 83407715 = 125111573) B125111573
theorem B55605143 : Blo 2053435 55605143 := bstep (se 1 (by rfl) ⟨41703857, by rfl⟩ : syracuseStep 55605143 = 83407715) B83407715
theorem B37070095 : Blo 2053435 37070095 := bstep (se 1 (by rfl) ⟨27802571, by rfl⟩ : syracuseStep 37070095 = 55605143) B55605143
theorem B49426793 : Blo 2053435 49426793 := bstep (se 2 (by rfl) ⟨18535047, by rfl⟩ : syracuseStep 49426793 = 37070095) B37070095
theorem B32951195 : Blo 2053435 32951195 := bstep (se 1 (by rfl) ⟨24713396, by rfl⟩ : syracuseStep 32951195 = 49426793) B49426793
theorem B21967463 : Blo 2053435 21967463 := bstep (se 1 (by rfl) ⟨16475597, by rfl⟩ : syracuseStep 21967463 = 32951195) B32951195
theorem B14644975 : Blo 2053435 14644975 := bstep (se 1 (by rfl) ⟨10983731, by rfl⟩ : syracuseStep 14644975 = 21967463) B21967463
theorem B19526633 : Blo 2053435 19526633 := bstep (se 2 (by rfl) ⟨7322487, by rfl⟩ : syracuseStep 19526633 = 14644975) B14644975
theorem B13017755 : Blo 2053435 13017755 := bstep (se 1 (by rfl) ⟨9763316, by rfl⟩ : syracuseStep 13017755 = 19526633) B19526633
theorem B8678503 : Blo 2053435 8678503 := bstep (se 1 (by rfl) ⟨6508877, by rfl⟩ : syracuseStep 8678503 = 13017755) B13017755
theorem B46285349 : Blo 2053435 46285349 := bstep (se 4 (by rfl) ⟨4339251, by rfl⟩ : syracuseStep 46285349 = 8678503) B8678503
theorem B123427597 : Blo 2053435 123427597 := bstep (se 3 (by rfl) ⟨23142674, by rfl⟩ : syracuseStep 123427597 = 46285349) B46285349
theorem B164570129 : Blo 2053435 164570129 := bstep (se 2 (by rfl) ⟨61713798, by rfl⟩ : syracuseStep 164570129 = 123427597) B123427597
theorem B109713419 : Blo 2053435 109713419 := bstep (se 1 (by rfl) ⟨82285064, by rfl⟩ : syracuseStep 109713419 = 164570129) B164570129
theorem B73142279 : Blo 2053435 73142279 := bstep (se 1 (by rfl) ⟨54856709, by rfl⟩ : syracuseStep 73142279 = 109713419) B109713419
theorem B48761519 : Blo 2053435 48761519 := bstep (se 1 (by rfl) ⟨36571139, by rfl⟩ : syracuseStep 48761519 = 73142279) B73142279
theorem B130030717 : Blo 2053435 130030717 := bstep (se 3 (by rfl) ⟨24380759, by rfl⟩ : syracuseStep 130030717 = 48761519) B48761519
theorem B173374289 : Blo 2053435 173374289 := bstep (se 2 (by rfl) ⟨65015358, by rfl⟩ : syracuseStep 173374289 = 130030717) B130030717
theorem B115582859 : Blo 2053435 115582859 := bstep (se 1 (by rfl) ⟨86687144, by rfl⟩ : syracuseStep 115582859 = 173374289) B173374289
theorem B77055239 : Blo 2053435 77055239 := bstep (se 1 (by rfl) ⟨57791429, by rfl⟩ : syracuseStep 77055239 = 115582859) B115582859
theorem B51370159 : Blo 2053435 51370159 := bstep (se 1 (by rfl) ⟨38527619, by rfl⟩ : syracuseStep 51370159 = 77055239) B77055239
theorem B68493545 : Blo 2053435 68493545 := bstep (se 2 (by rfl) ⟨25685079, by rfl⟩ : syracuseStep 68493545 = 51370159) B51370159
theorem B45662363 : Blo 2053435 45662363 := bstep (se 1 (by rfl) ⟨34246772, by rfl⟩ : syracuseStep 45662363 = 68493545) B68493545
theorem B30441575 : Blo 2053435 30441575 := bstep (se 1 (by rfl) ⟨22831181, by rfl⟩ : syracuseStep 30441575 = 45662363) B45662363
theorem B20294383 : Blo 2053435 20294383 := bstep (se 1 (by rfl) ⟨15220787, by rfl⟩ : syracuseStep 20294383 = 30441575) B30441575
theorem B27059177 : Blo 2053435 27059177 := bstep (se 2 (by rfl) ⟨10147191, by rfl⟩ : syracuseStep 27059177 = 20294383) B20294383
theorem B18039451 : Blo 2053435 18039451 := bstep (se 1 (by rfl) ⟨13529588, by rfl⟩ : syracuseStep 18039451 = 27059177) B27059177
theorem B24052601 : Blo 2053435 24052601 := bstep (se 2 (by rfl) ⟨9019725, by rfl⟩ : syracuseStep 24052601 = 18039451) B18039451
theorem B16035067 : Blo 2053435 16035067 := bstep (se 1 (by rfl) ⟨12026300, by rfl⟩ : syracuseStep 16035067 = 24052601) B24052601
theorem B85520357 : Blo 2053435 85520357 := bstep (se 4 (by rfl) ⟨8017533, by rfl⟩ : syracuseStep 85520357 = 16035067) B16035067
theorem B57013571 : Blo 2053435 57013571 := bstep (se 1 (by rfl) ⟨42760178, by rfl⟩ : syracuseStep 57013571 = 85520357) B85520357
theorem B38009047 : Blo 2053435 38009047 := bstep (se 1 (by rfl) ⟨28506785, by rfl⟩ : syracuseStep 38009047 = 57013571) B57013571
theorem B50678729 : Blo 2053435 50678729 := bstep (se 2 (by rfl) ⟨19004523, by rfl⟩ : syracuseStep 50678729 = 38009047) B38009047
theorem B33785819 : Blo 2053435 33785819 := bstep (se 1 (by rfl) ⟨25339364, by rfl⟩ : syracuseStep 33785819 = 50678729) B50678729
theorem B22523879 : Blo 2053435 22523879 := bstep (se 1 (by rfl) ⟨16892909, by rfl⟩ : syracuseStep 22523879 = 33785819) B33785819
theorem B60063677 : Blo 2053435 60063677 := bstep (se 3 (by rfl) ⟨11261939, by rfl⟩ : syracuseStep 60063677 = 22523879) B22523879
theorem B40042451 : Blo 2053435 40042451 := bstep (se 1 (by rfl) ⟨30031838, by rfl⟩ : syracuseStep 40042451 = 60063677) B60063677
theorem B26694967 : Blo 2053435 26694967 := bstep (se 1 (by rfl) ⟨20021225, by rfl⟩ : syracuseStep 26694967 = 40042451) B40042451
theorem B35593289 : Blo 2053435 35593289 := bstep (se 2 (by rfl) ⟨13347483, by rfl⟩ : syracuseStep 35593289 = 26694967) B26694967
theorem B23728859 : Blo 2053435 23728859 := bstep (se 1 (by rfl) ⟨17796644, by rfl⟩ : syracuseStep 23728859 = 35593289) B35593289
theorem B15819239 : Blo 2053435 15819239 := bstep (se 1 (by rfl) ⟨11864429, by rfl⟩ : syracuseStep 15819239 = 23728859) B23728859
theorem B10546159 : Blo 2053435 10546159 := bstep (se 1 (by rfl) ⟨7909619, by rfl⟩ : syracuseStep 10546159 = 15819239) B15819239
theorem B14061545 : Blo 2053435 14061545 := bstep (se 2 (by rfl) ⟨5273079, by rfl⟩ : syracuseStep 14061545 = 10546159) B10546159
theorem B9374363 : Blo 2053435 9374363 := bstep (se 1 (by rfl) ⟨7030772, by rfl⟩ : syracuseStep 9374363 = 14061545) B14061545
theorem B6249575 : Blo 2053435 6249575 := bstep (se 1 (by rfl) ⟨4687181, by rfl⟩ : syracuseStep 6249575 = 9374363) B9374363
theorem B16665533 : Blo 2053435 16665533 := bstep (se 3 (by rfl) ⟨3124787, by rfl⟩ : syracuseStep 16665533 = 6249575) B6249575
theorem B11110355 : Blo 2053435 11110355 := bstep (se 1 (by rfl) ⟨8332766, by rfl⟩ : syracuseStep 11110355 = 16665533) B16665533
theorem B7406903 : Blo 2053435 7406903 := bstep (se 1 (by rfl) ⟨5555177, by rfl⟩ : syracuseStep 7406903 = 11110355) B11110355
theorem B4937935 : Blo 2053435 4937935 := bstep (se 1 (by rfl) ⟨3703451, by rfl⟩ : syracuseStep 4937935 = 7406903) B7406903
theorem B6583913 : Blo 2053435 6583913 := bstep (se 2 (by rfl) ⟨2468967, by rfl⟩ : syracuseStep 6583913 = 4937935) B4937935
theorem B4389275 : Blo 2053435 4389275 := bstep (se 1 (by rfl) ⟨3291956, by rfl⟩ : syracuseStep 4389275 = 6583913) B6583913
theorem B11704733 : Blo 2053435 11704733 := bstep (se 3 (by rfl) ⟨2194637, by rfl⟩ : syracuseStep 11704733 = 4389275) B4389275
theorem B7803155 : Blo 2053435 7803155 := bstep (se 1 (by rfl) ⟨5852366, by rfl⟩ : syracuseStep 7803155 = 11704733) B11704733
theorem B5202103 : Blo 2053435 5202103 := bstep (se 1 (by rfl) ⟨3901577, by rfl⟩ : syracuseStep 5202103 = 7803155) B7803155
theorem B6936137 : Blo 2053435 6936137 := bstep (se 2 (by rfl) ⟨2601051, by rfl⟩ : syracuseStep 6936137 = 5202103) B5202103
theorem B4624091 : Blo 2053435 4624091 := bstep (se 1 (by rfl) ⟨3468068, by rfl⟩ : syracuseStep 4624091 = 6936137) B6936137
theorem B3082727 : Blo 2053435 3082727 := bstep (se 1 (by rfl) ⟨2312045, by rfl⟩ : syracuseStep 3082727 = 4624091) B4624091
theorem B2055151 : Blo 2053435 2055151 := bstep (se 1 (by rfl) ⟨1541363, by rfl⟩ : syracuseStep 2055151 = 3082727) B3082727
theorem B3082733 : Blo 2053435 3082733 := bbase (se 3 (by rfl) ⟨578012, by rfl⟩ : syracuseStep 3082733 = 1156025) (by norm_num)
theorem B2055155 : Blo 2053435 2055155 := bstep (se 1 (by rfl) ⟨1541366, by rfl⟩ : syracuseStep 2055155 = 3082733) B3082733
theorem B4624109 : Blo 2053435 4624109 := bbase (se 3 (by rfl) ⟨867020, by rfl⟩ : syracuseStep 4624109 = 1734041) (by norm_num)
theorem B3082739 : Blo 2053435 3082739 := bstep (se 1 (by rfl) ⟨2312054, by rfl⟩ : syracuseStep 3082739 = 4624109) B4624109
theorem B2055159 : Blo 2053435 2055159 := bstep (se 1 (by rfl) ⟨1541369, by rfl⟩ : syracuseStep 2055159 = 3082739) B3082739
theorem B2083205 : Blo 2053435 2083205 := bbase (se 4 (by rfl) ⟨195300, by rfl⟩ : syracuseStep 2083205 = 390601) (by norm_num)
theorem B5555213 : Blo 2053435 5555213 := bstep (se 3 (by rfl) ⟨1041602, by rfl⟩ : syracuseStep 5555213 = 2083205) B2083205
theorem B3703475 : Blo 2053435 3703475 := bstep (se 1 (by rfl) ⟨2777606, by rfl⟩ : syracuseStep 3703475 = 5555213) B5555213
theorem B2468983 : Blo 2053435 2468983 := bstep (se 1 (by rfl) ⟨1851737, by rfl⟩ : syracuseStep 2468983 = 3703475) B3703475
theorem B3291977 : Blo 2053435 3291977 := bstep (se 2 (by rfl) ⟨1234491, by rfl⟩ : syracuseStep 3291977 = 2468983) B2468983
theorem B2194651 : Blo 2053435 2194651 := bstep (se 1 (by rfl) ⟨1645988, by rfl⟩ : syracuseStep 2194651 = 3291977) B3291977
theorem B2926201 : Blo 2053435 2926201 := bstep (se 2 (by rfl) ⟨1097325, by rfl⟩ : syracuseStep 2926201 = 2194651) B2194651
theorem B3901601 : Blo 2053435 3901601 := bstep (se 2 (by rfl) ⟨1463100, by rfl⟩ : syracuseStep 3901601 = 2926201) B2926201
theorem B2601067 : Blo 2053435 2601067 := bstep (se 1 (by rfl) ⟨1950800, by rfl⟩ : syracuseStep 2601067 = 3901601) B3901601
theorem B3468089 : Blo 2053435 3468089 := bstep (se 2 (by rfl) ⟨1300533, by rfl⟩ : syracuseStep 3468089 = 2601067) B2601067
theorem B2312059 : Blo 2053435 2312059 := bstep (se 1 (by rfl) ⟨1734044, by rfl⟩ : syracuseStep 2312059 = 3468089) B3468089
theorem B3082745 : Blo 2053435 3082745 := bstep (se 2 (by rfl) ⟨1156029, by rfl⟩ : syracuseStep 3082745 = 2312059) B2312059
theorem B2055163 : Blo 2053435 2055163 := bstep (se 1 (by rfl) ⟨1541372, by rfl⟩ : syracuseStep 2055163 = 3082745) B3082745
theorem B8898389 : Blo 2053435 8898389 := bbase (se 9 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 8898389 = 52139) (by norm_num)
theorem B5932259 : Blo 2053435 5932259 := bstep (se 1 (by rfl) ⟨4449194, by rfl⟩ : syracuseStep 5932259 = 8898389) B8898389
theorem B3954839 : Blo 2053435 3954839 := bstep (se 1 (by rfl) ⟨2966129, by rfl⟩ : syracuseStep 3954839 = 5932259) B5932259
theorem B10546237 : Blo 2053435 10546237 := bstep (se 3 (by rfl) ⟨1977419, by rfl⟩ : syracuseStep 10546237 = 3954839) B3954839
theorem B14061649 : Blo 2053435 14061649 := bstep (se 2 (by rfl) ⟨5273118, by rfl⟩ : syracuseStep 14061649 = 10546237) B10546237
theorem B18748865 : Blo 2053435 18748865 := bstep (se 2 (by rfl) ⟨7030824, by rfl⟩ : syracuseStep 18748865 = 14061649) B14061649
theorem B49996973 : Blo 2053435 49996973 := bstep (se 3 (by rfl) ⟨9374432, by rfl⟩ : syracuseStep 49996973 = 18748865) B18748865
theorem B133325261 : Blo 2053435 133325261 := bstep (se 3 (by rfl) ⟨24998486, by rfl⟩ : syracuseStep 133325261 = 49996973) B49996973
theorem B88883507 : Blo 2053435 88883507 := bstep (se 1 (by rfl) ⟨66662630, by rfl⟩ : syracuseStep 88883507 = 133325261) B133325261
theorem B59255671 : Blo 2053435 59255671 := bstep (se 1 (by rfl) ⟨44441753, by rfl⟩ : syracuseStep 59255671 = 88883507) B88883507
theorem B79007561 : Blo 2053435 79007561 := bstep (se 2 (by rfl) ⟨29627835, by rfl⟩ : syracuseStep 79007561 = 59255671) B59255671
theorem B52671707 : Blo 2053435 52671707 := bstep (se 1 (by rfl) ⟨39503780, by rfl⟩ : syracuseStep 52671707 = 79007561) B79007561
theorem B35114471 : Blo 2053435 35114471 := bstep (se 1 (by rfl) ⟨26335853, by rfl⟩ : syracuseStep 35114471 = 52671707) B52671707
theorem B23409647 : Blo 2053435 23409647 := bstep (se 1 (by rfl) ⟨17557235, by rfl⟩ : syracuseStep 23409647 = 35114471) B35114471
theorem B15606431 : Blo 2053435 15606431 := bstep (se 1 (by rfl) ⟨11704823, by rfl⟩ : syracuseStep 15606431 = 23409647) B23409647
theorem B10404287 : Blo 2053435 10404287 := bstep (se 1 (by rfl) ⟨7803215, by rfl⟩ : syracuseStep 10404287 = 15606431) B15606431
theorem B6936191 : Blo 2053435 6936191 := bstep (se 1 (by rfl) ⟨5202143, by rfl⟩ : syracuseStep 6936191 = 10404287) B10404287
theorem B4624127 : Blo 2053435 4624127 := bstep (se 1 (by rfl) ⟨3468095, by rfl⟩ : syracuseStep 4624127 = 6936191) B6936191
theorem B3082751 : Blo 2053435 3082751 := bstep (se 1 (by rfl) ⟨2312063, by rfl⟩ : syracuseStep 3082751 = 4624127) B4624127
theorem B2055167 : Blo 2053435 2055167 := bstep (se 1 (by rfl) ⟨1541375, by rfl⟩ : syracuseStep 2055167 = 3082751) B3082751
theorem B3082757 : Blo 2053435 3082757 := bbase (se 4 (by rfl) ⟨289008, by rfl⟩ : syracuseStep 3082757 = 578017) (by norm_num)
theorem B2055171 : Blo 2053435 2055171 := bstep (se 1 (by rfl) ⟨1541378, by rfl⟩ : syracuseStep 2055171 = 3082757) B3082757
theorem B3468109 : Blo 2053435 3468109 := bbase (se 3 (by rfl) ⟨650270, by rfl⟩ : syracuseStep 3468109 = 1300541) (by norm_num)
theorem B4624145 : Blo 2053435 4624145 := bstep (se 2 (by rfl) ⟨1734054, by rfl⟩ : syracuseStep 4624145 = 3468109) B3468109
theorem B3082763 : Blo 2053435 3082763 := bstep (se 1 (by rfl) ⟨2312072, by rfl⟩ : syracuseStep 3082763 = 4624145) B4624145
theorem B2055175 : Blo 2053435 2055175 := bstep (se 1 (by rfl) ⟨1541381, by rfl⟩ : syracuseStep 2055175 = 3082763) B3082763
theorem B2312077 : Blo 2053435 2312077 := bbase (se 3 (by rfl) ⟨433514, by rfl⟩ : syracuseStep 2312077 = 867029) (by norm_num)
theorem B3082769 : Blo 2053435 3082769 := bstep (se 2 (by rfl) ⟨1156038, by rfl⟩ : syracuseStep 3082769 = 2312077) B2312077
theorem B2055179 : Blo 2053435 2055179 := bstep (se 1 (by rfl) ⟨1541384, by rfl⟩ : syracuseStep 2055179 = 3082769) B3082769
theorem B6936245 : Blo 2053435 6936245 := bbase (se 5 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 6936245 = 650273) (by norm_num)
theorem B4624163 : Blo 2053435 4624163 := bstep (se 1 (by rfl) ⟨3468122, by rfl⟩ : syracuseStep 4624163 = 6936245) B6936245
theorem B3082775 : Blo 2053435 3082775 := bstep (se 1 (by rfl) ⟨2312081, by rfl⟩ : syracuseStep 3082775 = 4624163) B4624163
theorem B2055183 : Blo 2053435 2055183 := bstep (se 1 (by rfl) ⟨1541387, by rfl⟩ : syracuseStep 2055183 = 3082775) B3082775
theorem B3082781 : Blo 2053435 3082781 := bbase (se 3 (by rfl) ⟨578021, by rfl⟩ : syracuseStep 3082781 = 1156043) (by norm_num)
theorem B2055187 : Blo 2053435 2055187 := bstep (se 1 (by rfl) ⟨1541390, by rfl⟩ : syracuseStep 2055187 = 3082781) B3082781
theorem B4624181 : Blo 2053435 4624181 := bbase (se 5 (by rfl) ⟨216758, by rfl⟩ : syracuseStep 4624181 = 433517) (by norm_num)
theorem B3082787 : Blo 2053435 3082787 := bstep (se 1 (by rfl) ⟨2312090, by rfl⟩ : syracuseStep 3082787 = 4624181) B4624181
theorem B2055191 : Blo 2053435 2055191 := bstep (se 1 (by rfl) ⟨1541393, by rfl⟩ : syracuseStep 2055191 = 3082787) B3082787
theorem B2636597 : Blo 2053435 2636597 := bbase (se 5 (by rfl) ⟨123590, by rfl⟩ : syracuseStep 2636597 = 247181) (by norm_num)
theorem B7030925 : Blo 2053435 7030925 := bstep (se 3 (by rfl) ⟨1318298, by rfl⟩ : syracuseStep 7030925 = 2636597) B2636597
theorem B4687283 : Blo 2053435 4687283 := bstep (se 1 (by rfl) ⟨3515462, by rfl⟩ : syracuseStep 4687283 = 7030925) B7030925
theorem B3124855 : Blo 2053435 3124855 := bstep (se 1 (by rfl) ⟨2343641, by rfl⟩ : syracuseStep 3124855 = 4687283) B4687283
theorem B4166473 : Blo 2053435 4166473 := bstep (se 2 (by rfl) ⟨1562427, by rfl⟩ : syracuseStep 4166473 = 3124855) B3124855
theorem B5555297 : Blo 2053435 5555297 := bstep (se 2 (by rfl) ⟨2083236, by rfl⟩ : syracuseStep 5555297 = 4166473) B4166473
theorem B3703531 : Blo 2053435 3703531 := bstep (se 1 (by rfl) ⟨2777648, by rfl⟩ : syracuseStep 3703531 = 5555297) B5555297
theorem B4938041 : Blo 2053435 4938041 := bstep (se 2 (by rfl) ⟨1851765, by rfl⟩ : syracuseStep 4938041 = 3703531) B3703531
theorem B13168109 : Blo 2053435 13168109 := bstep (se 3 (by rfl) ⟨2469020, by rfl⟩ : syracuseStep 13168109 = 4938041) B4938041
theorem B8778739 : Blo 2053435 8778739 := bstep (se 1 (by rfl) ⟨6584054, by rfl⟩ : syracuseStep 8778739 = 13168109) B13168109
theorem B11704985 : Blo 2053435 11704985 := bstep (se 2 (by rfl) ⟨4389369, by rfl⟩ : syracuseStep 11704985 = 8778739) B8778739
theorem B7803323 : Blo 2053435 7803323 := bstep (se 1 (by rfl) ⟨5852492, by rfl⟩ : syracuseStep 7803323 = 11704985) B11704985
theorem B5202215 : Blo 2053435 5202215 := bstep (se 1 (by rfl) ⟨3901661, by rfl⟩ : syracuseStep 5202215 = 7803323) B7803323
theorem B3468143 : Blo 2053435 3468143 := bstep (se 1 (by rfl) ⟨2601107, by rfl⟩ : syracuseStep 3468143 = 5202215) B5202215
theorem B2312095 : Blo 2053435 2312095 := bstep (se 1 (by rfl) ⟨1734071, by rfl⟩ : syracuseStep 2312095 = 3468143) B3468143
theorem B3082793 : Blo 2053435 3082793 := bstep (se 2 (by rfl) ⟨1156047, by rfl⟩ : syracuseStep 3082793 = 2312095) B2312095
theorem B2055195 : Blo 2053435 2055195 := bstep (se 1 (by rfl) ⟨1541396, by rfl⟩ : syracuseStep 2055195 = 3082793) B3082793
theorem B2469025 : Blo 2053435 2469025 := bbase (se 2 (by rfl) ⟨925884, by rfl⟩ : syracuseStep 2469025 = 1851769) (by norm_num)
theorem B13168133 : Blo 2053435 13168133 := bstep (se 4 (by rfl) ⟨1234512, by rfl⟩ : syracuseStep 13168133 = 2469025) B2469025
theorem B8778755 : Blo 2053435 8778755 := bstep (se 1 (by rfl) ⟨6584066, by rfl⟩ : syracuseStep 8778755 = 13168133) B13168133
theorem B5852503 : Blo 2053435 5852503 := bstep (se 1 (by rfl) ⟨4389377, by rfl⟩ : syracuseStep 5852503 = 8778755) B8778755
theorem B7803337 : Blo 2053435 7803337 := bstep (se 2 (by rfl) ⟨2926251, by rfl⟩ : syracuseStep 7803337 = 5852503) B5852503
theorem B10404449 : Blo 2053435 10404449 := bstep (se 2 (by rfl) ⟨3901668, by rfl⟩ : syracuseStep 10404449 = 7803337) B7803337
theorem B6936299 : Blo 2053435 6936299 := bstep (se 1 (by rfl) ⟨5202224, by rfl⟩ : syracuseStep 6936299 = 10404449) B10404449
theorem B4624199 : Blo 2053435 4624199 := bstep (se 1 (by rfl) ⟨3468149, by rfl⟩ : syracuseStep 4624199 = 6936299) B6936299
theorem B3082799 : Blo 2053435 3082799 := bstep (se 1 (by rfl) ⟨2312099, by rfl⟩ : syracuseStep 3082799 = 4624199) B4624199
theorem B2055199 : Blo 2053435 2055199 := bstep (se 1 (by rfl) ⟨1541399, by rfl⟩ : syracuseStep 2055199 = 3082799) B3082799
theorem B3082805 : Blo 2053435 3082805 := bbase (se 5 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 3082805 = 289013) (by norm_num)
theorem B2055203 : Blo 2053435 2055203 := bstep (se 1 (by rfl) ⟨1541402, by rfl⟩ : syracuseStep 2055203 = 3082805) B3082805
theorem B5202245 : Blo 2053435 5202245 := bbase (se 4 (by rfl) ⟨487710, by rfl⟩ : syracuseStep 5202245 = 975421) (by norm_num)
theorem B3468163 : Blo 2053435 3468163 := bstep (se 1 (by rfl) ⟨2601122, by rfl⟩ : syracuseStep 3468163 = 5202245) B5202245
theorem B4624217 : Blo 2053435 4624217 := bstep (se 2 (by rfl) ⟨1734081, by rfl⟩ : syracuseStep 4624217 = 3468163) B3468163
theorem B3082811 : Blo 2053435 3082811 := bstep (se 1 (by rfl) ⟨2312108, by rfl⟩ : syracuseStep 3082811 = 4624217) B4624217
theorem B2055207 : Blo 2053435 2055207 := bstep (se 1 (by rfl) ⟨1541405, by rfl⟩ : syracuseStep 2055207 = 3082811) B3082811
theorem B2312113 : Blo 2053435 2312113 := bbase (se 2 (by rfl) ⟨867042, by rfl⟩ : syracuseStep 2312113 = 1734085) (by norm_num)
theorem B3082817 : Blo 2053435 3082817 := bstep (se 2 (by rfl) ⟨1156056, by rfl⟩ : syracuseStep 3082817 = 2312113) B2312113
theorem B2055211 : Blo 2053435 2055211 := bstep (se 1 (by rfl) ⟨1541408, by rfl⟩ : syracuseStep 2055211 = 3082817) B3082817
theorem B5852549 : Blo 2053435 5852549 := bbase (se 4 (by rfl) ⟨548676, by rfl⟩ : syracuseStep 5852549 = 1097353) (by norm_num)
theorem B3901699 : Blo 2053435 3901699 := bstep (se 1 (by rfl) ⟨2926274, by rfl⟩ : syracuseStep 3901699 = 5852549) B5852549
theorem B5202265 : Blo 2053435 5202265 := bstep (se 2 (by rfl) ⟨1950849, by rfl⟩ : syracuseStep 5202265 = 3901699) B3901699
theorem B6936353 : Blo 2053435 6936353 := bstep (se 2 (by rfl) ⟨2601132, by rfl⟩ : syracuseStep 6936353 = 5202265) B5202265
theorem B4624235 : Blo 2053435 4624235 := bstep (se 1 (by rfl) ⟨3468176, by rfl⟩ : syracuseStep 4624235 = 6936353) B6936353
theorem B3082823 : Blo 2053435 3082823 := bstep (se 1 (by rfl) ⟨2312117, by rfl⟩ : syracuseStep 3082823 = 4624235) B4624235
theorem B2055215 : Blo 2053435 2055215 := bstep (se 1 (by rfl) ⟨1541411, by rfl⟩ : syracuseStep 2055215 = 3082823) B3082823
theorem B3082829 : Blo 2053435 3082829 := bbase (se 3 (by rfl) ⟨578030, by rfl⟩ : syracuseStep 3082829 = 1156061) (by norm_num)
theorem B2055219 : Blo 2053435 2055219 := bstep (se 1 (by rfl) ⟨1541414, by rfl⟩ : syracuseStep 2055219 = 3082829) B3082829
theorem B4624253 : Blo 2053435 4624253 := bbase (se 3 (by rfl) ⟨867047, by rfl⟩ : syracuseStep 4624253 = 1734095) (by norm_num)
theorem B3082835 : Blo 2053435 3082835 := bstep (se 1 (by rfl) ⟨2312126, by rfl⟩ : syracuseStep 3082835 = 4624253) B4624253
theorem B2055223 : Blo 2053435 2055223 := bstep (se 1 (by rfl) ⟨1541417, by rfl⟩ : syracuseStep 2055223 = 3082835) B3082835
theorem B3468197 : Blo 2053435 3468197 := bbase (se 4 (by rfl) ⟨325143, by rfl⟩ : syracuseStep 3468197 = 650287) (by norm_num)
theorem B2312131 : Blo 2053435 2312131 := bstep (se 1 (by rfl) ⟨1734098, by rfl⟩ : syracuseStep 2312131 = 3468197) B3468197
theorem B3082841 : Blo 2053435 3082841 := bstep (se 2 (by rfl) ⟨1156065, by rfl⟩ : syracuseStep 3082841 = 2312131) B2312131
theorem B2055227 : Blo 2053435 2055227 := bstep (se 1 (by rfl) ⟨1541420, by rfl⟩ : syracuseStep 2055227 = 3082841) B3082841
theorem B3292085 : Blo 2053435 3292085 := bbase (se 5 (by rfl) ⟨154316, by rfl⟩ : syracuseStep 3292085 = 308633) (by norm_num)
theorem B2194723 : Blo 2053435 2194723 := bstep (se 1 (by rfl) ⟨1646042, by rfl⟩ : syracuseStep 2194723 = 3292085) B3292085
theorem B2926297 : Blo 2053435 2926297 := bstep (se 2 (by rfl) ⟨1097361, by rfl⟩ : syracuseStep 2926297 = 2194723) B2194723
theorem B15606917 : Blo 2053435 15606917 := bstep (se 4 (by rfl) ⟨1463148, by rfl⟩ : syracuseStep 15606917 = 2926297) B2926297
theorem B10404611 : Blo 2053435 10404611 := bstep (se 1 (by rfl) ⟨7803458, by rfl⟩ : syracuseStep 10404611 = 15606917) B15606917
theorem B6936407 : Blo 2053435 6936407 := bstep (se 1 (by rfl) ⟨5202305, by rfl⟩ : syracuseStep 6936407 = 10404611) B10404611
theorem B4624271 : Blo 2053435 4624271 := bstep (se 1 (by rfl) ⟨3468203, by rfl⟩ : syracuseStep 4624271 = 6936407) B6936407
theorem B3082847 : Blo 2053435 3082847 := bstep (se 1 (by rfl) ⟨2312135, by rfl⟩ : syracuseStep 3082847 = 4624271) B4624271
theorem B2055231 : Blo 2053435 2055231 := bstep (se 1 (by rfl) ⟨1541423, by rfl⟩ : syracuseStep 2055231 = 3082847) B3082847
theorem B3082853 : Blo 2053435 3082853 := bbase (se 4 (by rfl) ⟨289017, by rfl⟩ : syracuseStep 3082853 = 578035) (by norm_num)
theorem B2055235 : Blo 2053435 2055235 := bstep (se 1 (by rfl) ⟨1541426, by rfl⟩ : syracuseStep 2055235 = 3082853) B3082853
theorem B2926309 : Blo 2053435 2926309 := bbase (se 4 (by rfl) ⟨274341, by rfl⟩ : syracuseStep 2926309 = 548683) (by norm_num)
theorem B3901745 : Blo 2053435 3901745 := bstep (se 2 (by rfl) ⟨1463154, by rfl⟩ : syracuseStep 3901745 = 2926309) B2926309
theorem B2601163 : Blo 2053435 2601163 := bstep (se 1 (by rfl) ⟨1950872, by rfl⟩ : syracuseStep 2601163 = 3901745) B3901745
theorem B3468217 : Blo 2053435 3468217 := bstep (se 2 (by rfl) ⟨1300581, by rfl⟩ : syracuseStep 3468217 = 2601163) B2601163
theorem B4624289 : Blo 2053435 4624289 := bstep (se 2 (by rfl) ⟨1734108, by rfl⟩ : syracuseStep 4624289 = 3468217) B3468217
theorem B3082859 : Blo 2053435 3082859 := bstep (se 1 (by rfl) ⟨2312144, by rfl⟩ : syracuseStep 3082859 = 4624289) B4624289
theorem B2055239 : Blo 2053435 2055239 := bstep (se 1 (by rfl) ⟨1541429, by rfl⟩ : syracuseStep 2055239 = 3082859) B3082859
theorem B2312149 : Blo 2053435 2312149 := bbase (se 7 (by rfl) ⟨27095, by rfl⟩ : syracuseStep 2312149 = 54191) (by norm_num)
theorem B3082865 : Blo 2053435 3082865 := bstep (se 2 (by rfl) ⟨1156074, by rfl⟩ : syracuseStep 3082865 = 2312149) B2312149
theorem B2055243 : Blo 2053435 2055243 := bstep (se 1 (by rfl) ⟨1541432, by rfl⟩ : syracuseStep 2055243 = 3082865) B3082865
theorem B2601173 : Blo 2053435 2601173 := bbase (se 7 (by rfl) ⟨30482, by rfl⟩ : syracuseStep 2601173 = 60965) (by norm_num)
theorem B6936461 : Blo 2053435 6936461 := bstep (se 3 (by rfl) ⟨1300586, by rfl⟩ : syracuseStep 6936461 = 2601173) B2601173
theorem B4624307 : Blo 2053435 4624307 := bstep (se 1 (by rfl) ⟨3468230, by rfl⟩ : syracuseStep 4624307 = 6936461) B6936461
theorem B3082871 : Blo 2053435 3082871 := bstep (se 1 (by rfl) ⟨2312153, by rfl⟩ : syracuseStep 3082871 = 4624307) B4624307
theorem B2055247 : Blo 2053435 2055247 := bstep (se 1 (by rfl) ⟨1541435, by rfl⟩ : syracuseStep 2055247 = 3082871) B3082871
theorem B3082877 : Blo 2053435 3082877 := bbase (se 3 (by rfl) ⟨578039, by rfl⟩ : syracuseStep 3082877 = 1156079) (by norm_num)
theorem B2055251 : Blo 2053435 2055251 := bstep (se 1 (by rfl) ⟨1541438, by rfl⟩ : syracuseStep 2055251 = 3082877) B3082877
theorem B4624325 : Blo 2053435 4624325 := bbase (se 4 (by rfl) ⟨433530, by rfl⟩ : syracuseStep 4624325 = 867061) (by norm_num)
theorem B3082883 : Blo 2053435 3082883 := bstep (se 1 (by rfl) ⟨2312162, by rfl⟩ : syracuseStep 3082883 = 4624325) B4624325
theorem B2055255 : Blo 2053435 2055255 := bstep (se 1 (by rfl) ⟨1541441, by rfl⟩ : syracuseStep 2055255 = 3082883) B3082883
theorem B8779013 : Blo 2053435 8779013 := bbase (se 4 (by rfl) ⟨823032, by rfl⟩ : syracuseStep 8779013 = 1646065) (by norm_num)
theorem B5852675 : Blo 2053435 5852675 := bstep (se 1 (by rfl) ⟨4389506, by rfl⟩ : syracuseStep 5852675 = 8779013) B8779013
theorem B3901783 : Blo 2053435 3901783 := bstep (se 1 (by rfl) ⟨2926337, by rfl⟩ : syracuseStep 3901783 = 5852675) B5852675
theorem B5202377 : Blo 2053435 5202377 := bstep (se 2 (by rfl) ⟨1950891, by rfl⟩ : syracuseStep 5202377 = 3901783) B3901783
theorem B3468251 : Blo 2053435 3468251 := bstep (se 1 (by rfl) ⟨2601188, by rfl⟩ : syracuseStep 3468251 = 5202377) B5202377
theorem B2312167 : Blo 2053435 2312167 := bstep (se 1 (by rfl) ⟨1734125, by rfl⟩ : syracuseStep 2312167 = 3468251) B3468251
theorem B3082889 : Blo 2053435 3082889 := bstep (se 2 (by rfl) ⟨1156083, by rfl⟩ : syracuseStep 3082889 = 2312167) B2312167
theorem B2055259 : Blo 2053435 2055259 := bstep (se 1 (by rfl) ⟨1541444, by rfl⟩ : syracuseStep 2055259 = 3082889) B3082889
theorem B10404773 : Blo 2053435 10404773 := bbase (se 4 (by rfl) ⟨975447, by rfl⟩ : syracuseStep 10404773 = 1950895) (by norm_num)
theorem B6936515 : Blo 2053435 6936515 := bstep (se 1 (by rfl) ⟨5202386, by rfl⟩ : syracuseStep 6936515 = 10404773) B10404773
theorem B4624343 : Blo 2053435 4624343 := bstep (se 1 (by rfl) ⟨3468257, by rfl⟩ : syracuseStep 4624343 = 6936515) B6936515
theorem B3082895 : Blo 2053435 3082895 := bstep (se 1 (by rfl) ⟨2312171, by rfl⟩ : syracuseStep 3082895 = 4624343) B4624343
theorem B2055263 : Blo 2053435 2055263 := bstep (se 1 (by rfl) ⟨1541447, by rfl⟩ : syracuseStep 2055263 = 3082895) B3082895
theorem B3082901 : Blo 2053435 3082901 := bbase (se 6 (by rfl) ⟨72255, by rfl⟩ : syracuseStep 3082901 = 144511) (by norm_num)
theorem B2055267 : Blo 2053435 2055267 := bstep (se 1 (by rfl) ⟨1541450, by rfl⟩ : syracuseStep 2055267 = 3082901) B3082901
theorem B8446949 : Blo 2053435 8446949 := bbase (se 4 (by rfl) ⟨791901, by rfl⟩ : syracuseStep 8446949 = 1583803) (by norm_num)
theorem B5631299 : Blo 2053435 5631299 := bstep (se 1 (by rfl) ⟨4223474, by rfl⟩ : syracuseStep 5631299 = 8446949) B8446949
theorem B3754199 : Blo 2053435 3754199 := bstep (se 1 (by rfl) ⟨2815649, by rfl⟩ : syracuseStep 3754199 = 5631299) B5631299
theorem B2502799 : Blo 2053435 2502799 := bstep (se 1 (by rfl) ⟨1877099, by rfl⟩ : syracuseStep 2502799 = 3754199) B3754199
theorem B13348261 : Blo 2053435 13348261 := bstep (se 4 (by rfl) ⟨1251399, by rfl⟩ : syracuseStep 13348261 = 2502799) B2502799
theorem B17797681 : Blo 2053435 17797681 := bstep (se 2 (by rfl) ⟨6674130, by rfl⟩ : syracuseStep 17797681 = 13348261) B13348261
theorem B23730241 : Blo 2053435 23730241 := bstep (se 2 (by rfl) ⟨8898840, by rfl⟩ : syracuseStep 23730241 = 17797681) B17797681
theorem B31640321 : Blo 2053435 31640321 := bstep (se 2 (by rfl) ⟨11865120, by rfl⟩ : syracuseStep 31640321 = 23730241) B23730241
theorem B21093547 : Blo 2053435 21093547 := bstep (se 1 (by rfl) ⟨15820160, by rfl⟩ : syracuseStep 21093547 = 31640321) B31640321
theorem B28124729 : Blo 2053435 28124729 := bstep (se 2 (by rfl) ⟨10546773, by rfl⟩ : syracuseStep 28124729 = 21093547) B21093547
theorem B18749819 : Blo 2053435 18749819 := bstep (se 1 (by rfl) ⟨14062364, by rfl⟩ : syracuseStep 18749819 = 28124729) B28124729
theorem B12499879 : Blo 2053435 12499879 := bstep (se 1 (by rfl) ⟨9374909, by rfl⟩ : syracuseStep 12499879 = 18749819) B18749819
theorem B16666505 : Blo 2053435 16666505 := bstep (se 2 (by rfl) ⟨6249939, by rfl⟩ : syracuseStep 16666505 = 12499879) B12499879
theorem B11111003 : Blo 2053435 11111003 := bstep (se 1 (by rfl) ⟨8333252, by rfl⟩ : syracuseStep 11111003 = 16666505) B16666505
theorem B7407335 : Blo 2053435 7407335 := bstep (se 1 (by rfl) ⟨5555501, by rfl⟩ : syracuseStep 7407335 = 11111003) B11111003
theorem B19752893 : Blo 2053435 19752893 := bstep (se 3 (by rfl) ⟨3703667, by rfl⟩ : syracuseStep 19752893 = 7407335) B7407335
theorem B13168595 : Blo 2053435 13168595 := bstep (se 1 (by rfl) ⟨9876446, by rfl⟩ : syracuseStep 13168595 = 19752893) B19752893
theorem B8779063 : Blo 2053435 8779063 := bstep (se 1 (by rfl) ⟨6584297, by rfl⟩ : syracuseStep 8779063 = 13168595) B13168595
theorem B11705417 : Blo 2053435 11705417 := bstep (se 2 (by rfl) ⟨4389531, by rfl⟩ : syracuseStep 11705417 = 8779063) B8779063
theorem B7803611 : Blo 2053435 7803611 := bstep (se 1 (by rfl) ⟨5852708, by rfl⟩ : syracuseStep 7803611 = 11705417) B11705417
theorem B5202407 : Blo 2053435 5202407 := bstep (se 1 (by rfl) ⟨3901805, by rfl⟩ : syracuseStep 5202407 = 7803611) B7803611
theorem B3468271 : Blo 2053435 3468271 := bstep (se 1 (by rfl) ⟨2601203, by rfl⟩ : syracuseStep 3468271 = 5202407) B5202407
theorem B4624361 : Blo 2053435 4624361 := bstep (se 2 (by rfl) ⟨1734135, by rfl⟩ : syracuseStep 4624361 = 3468271) B3468271
theorem B3082907 : Blo 2053435 3082907 := bstep (se 1 (by rfl) ⟨2312180, by rfl⟩ : syracuseStep 3082907 = 4624361) B4624361
theorem B2055271 : Blo 2053435 2055271 := bstep (se 1 (by rfl) ⟨1541453, by rfl⟩ : syracuseStep 2055271 = 3082907) B3082907
theorem B2312185 : Blo 2053435 2312185 := bbase (se 2 (by rfl) ⟨867069, by rfl⟩ : syracuseStep 2312185 = 1734139) (by norm_num)
theorem B3082913 : Blo 2053435 3082913 := bstep (se 2 (by rfl) ⟨1156092, by rfl⟩ : syracuseStep 3082913 = 2312185) B2312185
theorem B2055275 : Blo 2053435 2055275 := bstep (se 1 (by rfl) ⟨1541456, by rfl⟩ : syracuseStep 2055275 = 3082913) B3082913
theorem B9876485 : Blo 2053435 9876485 := bbase (se 4 (by rfl) ⟨925920, by rfl⟩ : syracuseStep 9876485 = 1851841) (by norm_num)
theorem B6584323 : Blo 2053435 6584323 := bstep (se 1 (by rfl) ⟨4938242, by rfl⟩ : syracuseStep 6584323 = 9876485) B9876485
theorem B8779097 : Blo 2053435 8779097 := bstep (se 2 (by rfl) ⟨3292161, by rfl⟩ : syracuseStep 8779097 = 6584323) B6584323
theorem B5852731 : Blo 2053435 5852731 := bstep (se 1 (by rfl) ⟨4389548, by rfl⟩ : syracuseStep 5852731 = 8779097) B8779097
theorem B7803641 : Blo 2053435 7803641 := bstep (se 2 (by rfl) ⟨2926365, by rfl⟩ : syracuseStep 7803641 = 5852731) B5852731
theorem B5202427 : Blo 2053435 5202427 := bstep (se 1 (by rfl) ⟨3901820, by rfl⟩ : syracuseStep 5202427 = 7803641) B7803641
theorem B6936569 : Blo 2053435 6936569 := bstep (se 2 (by rfl) ⟨2601213, by rfl⟩ : syracuseStep 6936569 = 5202427) B5202427
theorem B4624379 : Blo 2053435 4624379 := bstep (se 1 (by rfl) ⟨3468284, by rfl⟩ : syracuseStep 4624379 = 6936569) B6936569
theorem B3082919 : Blo 2053435 3082919 := bstep (se 1 (by rfl) ⟨2312189, by rfl⟩ : syracuseStep 3082919 = 4624379) B4624379
theorem B2055279 : Blo 2053435 2055279 := bstep (se 1 (by rfl) ⟨1541459, by rfl⟩ : syracuseStep 2055279 = 3082919) B3082919
theorem B3082925 : Blo 2053435 3082925 := bbase (se 3 (by rfl) ⟨578048, by rfl⟩ : syracuseStep 3082925 = 1156097) (by norm_num)
theorem B2055283 : Blo 2053435 2055283 := bstep (se 1 (by rfl) ⟨1541462, by rfl⟩ : syracuseStep 2055283 = 3082925) B3082925
theorem B4624397 : Blo 2053435 4624397 := bbase (se 3 (by rfl) ⟨867074, by rfl⟩ : syracuseStep 4624397 = 1734149) (by norm_num)
theorem B3082931 : Blo 2053435 3082931 := bstep (se 1 (by rfl) ⟨2312198, by rfl⟩ : syracuseStep 3082931 = 4624397) B4624397
theorem B2055287 : Blo 2053435 2055287 := bstep (se 1 (by rfl) ⟨1541465, by rfl⟩ : syracuseStep 2055287 = 3082931) B3082931
theorem B2601229 : Blo 2053435 2601229 := bbase (se 3 (by rfl) ⟨487730, by rfl⟩ : syracuseStep 2601229 = 975461) (by norm_num)
theorem B3468305 : Blo 2053435 3468305 := bstep (se 2 (by rfl) ⟨1300614, by rfl⟩ : syracuseStep 3468305 = 2601229) B2601229
theorem B2312203 : Blo 2053435 2312203 := bstep (se 1 (by rfl) ⟨1734152, by rfl⟩ : syracuseStep 2312203 = 3468305) B3468305
theorem B3082937 : Blo 2053435 3082937 := bstep (se 2 (by rfl) ⟨1156101, by rfl⟩ : syracuseStep 3082937 = 2312203) B2312203
theorem B2055291 : Blo 2053435 2055291 := bstep (se 1 (by rfl) ⟨1541468, by rfl⟩ : syracuseStep 2055291 = 3082937) B3082937
theorem B3563597 : Blo 2053435 3563597 := bbase (se 3 (by rfl) ⟨668174, by rfl⟩ : syracuseStep 3563597 = 1336349) (by norm_num)
theorem B9502925 : Blo 2053435 9502925 := bstep (se 3 (by rfl) ⟨1781798, by rfl⟩ : syracuseStep 9502925 = 3563597) B3563597
theorem B101364533 : Blo 2053435 101364533 := bstep (se 5 (by rfl) ⟨4751462, by rfl⟩ : syracuseStep 101364533 = 9502925) B9502925
theorem B67576355 : Blo 2053435 67576355 := bstep (se 1 (by rfl) ⟨50682266, by rfl⟩ : syracuseStep 67576355 = 101364533) B101364533
theorem B45050903 : Blo 2053435 45050903 := bstep (se 1 (by rfl) ⟨33788177, by rfl⟩ : syracuseStep 45050903 = 67576355) B67576355
theorem B30033935 : Blo 2053435 30033935 := bstep (se 1 (by rfl) ⟨22525451, by rfl⟩ : syracuseStep 30033935 = 45050903) B45050903
theorem B20022623 : Blo 2053435 20022623 := bstep (se 1 (by rfl) ⟨15016967, by rfl⟩ : syracuseStep 20022623 = 30033935) B30033935
theorem B13348415 : Blo 2053435 13348415 := bstep (se 1 (by rfl) ⟨10011311, by rfl⟩ : syracuseStep 13348415 = 20022623) B20022623
theorem B35595773 : Blo 2053435 35595773 := bstep (se 3 (by rfl) ⟨6674207, by rfl⟩ : syracuseStep 35595773 = 13348415) B13348415
theorem B23730515 : Blo 2053435 23730515 := bstep (se 1 (by rfl) ⟨17797886, by rfl⟩ : syracuseStep 23730515 = 35595773) B35595773
theorem B15820343 : Blo 2053435 15820343 := bstep (se 1 (by rfl) ⟨11865257, by rfl⟩ : syracuseStep 15820343 = 23730515) B23730515
theorem B10546895 : Blo 2053435 10546895 := bstep (se 1 (by rfl) ⟨7910171, by rfl⟩ : syracuseStep 10546895 = 15820343) B15820343
theorem B28125053 : Blo 2053435 28125053 := bstep (se 3 (by rfl) ⟨5273447, by rfl⟩ : syracuseStep 28125053 = 10546895) B10546895
theorem B18750035 : Blo 2053435 18750035 := bstep (se 1 (by rfl) ⟨14062526, by rfl⟩ : syracuseStep 18750035 = 28125053) B28125053
theorem B12500023 : Blo 2053435 12500023 := bstep (se 1 (by rfl) ⟨9375017, by rfl⟩ : syracuseStep 12500023 = 18750035) B18750035
theorem B16666697 : Blo 2053435 16666697 := bstep (se 2 (by rfl) ⟨6250011, by rfl⟩ : syracuseStep 16666697 = 12500023) B12500023
theorem B11111131 : Blo 2053435 11111131 := bstep (se 1 (by rfl) ⟨8333348, by rfl⟩ : syracuseStep 11111131 = 16666697) B16666697
theorem B14814841 : Blo 2053435 14814841 := bstep (se 2 (by rfl) ⟨5555565, by rfl⟩ : syracuseStep 14814841 = 11111131) B11111131
theorem B19753121 : Blo 2053435 19753121 := bstep (se 2 (by rfl) ⟨7407420, by rfl⟩ : syracuseStep 19753121 = 14814841) B14814841
theorem B13168747 : Blo 2053435 13168747 := bstep (se 1 (by rfl) ⟨9876560, by rfl⟩ : syracuseStep 13168747 = 19753121) B19753121
theorem B17558329 : Blo 2053435 17558329 := bstep (se 2 (by rfl) ⟨6584373, by rfl⟩ : syracuseStep 17558329 = 13168747) B13168747
theorem B23411105 : Blo 2053435 23411105 := bstep (se 2 (by rfl) ⟨8779164, by rfl⟩ : syracuseStep 23411105 = 17558329) B17558329
theorem B15607403 : Blo 2053435 15607403 := bstep (se 1 (by rfl) ⟨11705552, by rfl⟩ : syracuseStep 15607403 = 23411105) B23411105
theorem B10404935 : Blo 2053435 10404935 := bstep (se 1 (by rfl) ⟨7803701, by rfl⟩ : syracuseStep 10404935 = 15607403) B15607403
theorem B6936623 : Blo 2053435 6936623 := bstep (se 1 (by rfl) ⟨5202467, by rfl⟩ : syracuseStep 6936623 = 10404935) B10404935
theorem B4624415 : Blo 2053435 4624415 := bstep (se 1 (by rfl) ⟨3468311, by rfl⟩ : syracuseStep 4624415 = 6936623) B6936623
theorem B3082943 : Blo 2053435 3082943 := bstep (se 1 (by rfl) ⟨2312207, by rfl⟩ : syracuseStep 3082943 = 4624415) B4624415
theorem B2055295 : Blo 2053435 2055295 := bstep (se 1 (by rfl) ⟨1541471, by rfl⟩ : syracuseStep 2055295 = 3082943) B3082943
theorem B3082949 : Blo 2053435 3082949 := bbase (se 4 (by rfl) ⟨289026, by rfl⟩ : syracuseStep 3082949 = 578053) (by norm_num)
theorem B2055299 : Blo 2053435 2055299 := bstep (se 1 (by rfl) ⟨1541474, by rfl⟩ : syracuseStep 2055299 = 3082949) B3082949
theorem B3468325 : Blo 2053435 3468325 := bbase (se 4 (by rfl) ⟨325155, by rfl⟩ : syracuseStep 3468325 = 650311) (by norm_num)
theorem B4624433 : Blo 2053435 4624433 := bstep (se 2 (by rfl) ⟨1734162, by rfl⟩ : syracuseStep 4624433 = 3468325) B3468325
theorem B3082955 : Blo 2053435 3082955 := bstep (se 1 (by rfl) ⟨2312216, by rfl⟩ : syracuseStep 3082955 = 4624433) B4624433
theorem B2055303 : Blo 2053435 2055303 := bstep (se 1 (by rfl) ⟨1541477, by rfl⟩ : syracuseStep 2055303 = 3082955) B3082955
theorem B2312221 : Blo 2053435 2312221 := bbase (se 3 (by rfl) ⟨433541, by rfl⟩ : syracuseStep 2312221 = 867083) (by norm_num)
theorem B3082961 : Blo 2053435 3082961 := bstep (se 2 (by rfl) ⟨1156110, by rfl⟩ : syracuseStep 3082961 = 2312221) B2312221
theorem B2055307 : Blo 2053435 2055307 := bstep (se 1 (by rfl) ⟨1541480, by rfl⟩ : syracuseStep 2055307 = 3082961) B3082961
theorem B6936677 : Blo 2053435 6936677 := bbase (se 4 (by rfl) ⟨650313, by rfl⟩ : syracuseStep 6936677 = 1300627) (by norm_num)
theorem B4624451 : Blo 2053435 4624451 := bstep (se 1 (by rfl) ⟨3468338, by rfl⟩ : syracuseStep 4624451 = 6936677) B6936677
theorem B3082967 : Blo 2053435 3082967 := bstep (se 1 (by rfl) ⟨2312225, by rfl⟩ : syracuseStep 3082967 = 4624451) B4624451
theorem B2055311 : Blo 2053435 2055311 := bstep (se 1 (by rfl) ⟨1541483, by rfl⟩ : syracuseStep 2055311 = 3082967) B3082967
theorem B3082973 : Blo 2053435 3082973 := bbase (se 3 (by rfl) ⟨578057, by rfl⟩ : syracuseStep 3082973 = 1156115) (by norm_num)
theorem B2055315 : Blo 2053435 2055315 := bstep (se 1 (by rfl) ⟨1541486, by rfl⟩ : syracuseStep 2055315 = 3082973) B3082973
theorem B4624469 : Blo 2053435 4624469 := bbase (se 8 (by rfl) ⟨27096, by rfl⟩ : syracuseStep 4624469 = 54193) (by norm_num)
theorem B3082979 : Blo 2053435 3082979 := bstep (se 1 (by rfl) ⟨2312234, by rfl⟩ : syracuseStep 3082979 = 4624469) B4624469
theorem B2055319 : Blo 2053435 2055319 := bstep (se 1 (by rfl) ⟨1541489, by rfl⟩ : syracuseStep 2055319 = 3082979) B3082979
theorem B4938349 : Blo 2053435 4938349 := bbase (se 3 (by rfl) ⟨925940, by rfl⟩ : syracuseStep 4938349 = 1851881) (by norm_num)
theorem B6584465 : Blo 2053435 6584465 := bstep (se 2 (by rfl) ⟨2469174, by rfl⟩ : syracuseStep 6584465 = 4938349) B4938349
theorem B4389643 : Blo 2053435 4389643 := bstep (se 1 (by rfl) ⟨3292232, by rfl⟩ : syracuseStep 4389643 = 6584465) B6584465
theorem B5852857 : Blo 2053435 5852857 := bstep (se 2 (by rfl) ⟨2194821, by rfl⟩ : syracuseStep 5852857 = 4389643) B4389643
theorem B7803809 : Blo 2053435 7803809 := bstep (se 2 (by rfl) ⟨2926428, by rfl⟩ : syracuseStep 7803809 = 5852857) B5852857
theorem B5202539 : Blo 2053435 5202539 := bstep (se 1 (by rfl) ⟨3901904, by rfl⟩ : syracuseStep 5202539 = 7803809) B7803809
theorem B3468359 : Blo 2053435 3468359 := bstep (se 1 (by rfl) ⟨2601269, by rfl⟩ : syracuseStep 3468359 = 5202539) B5202539
theorem B2312239 : Blo 2053435 2312239 := bstep (se 1 (by rfl) ⟨1734179, by rfl⟩ : syracuseStep 2312239 = 3468359) B3468359
theorem B3082985 : Blo 2053435 3082985 := bstep (se 2 (by rfl) ⟨1156119, by rfl⟩ : syracuseStep 3082985 = 2312239) B2312239
theorem B2055323 : Blo 2053435 2055323 := bstep (se 1 (by rfl) ⟨1541492, by rfl⟩ : syracuseStep 2055323 = 3082985) B3082985
theorem B19753429 : Blo 2053435 19753429 := bbase (se 7 (by rfl) ⟨231485, by rfl⟩ : syracuseStep 19753429 = 462971) (by norm_num)
theorem B26337905 : Blo 2053435 26337905 := bstep (se 2 (by rfl) ⟨9876714, by rfl⟩ : syracuseStep 26337905 = 19753429) B19753429
theorem B17558603 : Blo 2053435 17558603 := bstep (se 1 (by rfl) ⟨13168952, by rfl⟩ : syracuseStep 17558603 = 26337905) B26337905
theorem B11705735 : Blo 2053435 11705735 := bstep (se 1 (by rfl) ⟨8779301, by rfl⟩ : syracuseStep 11705735 = 17558603) B17558603
theorem B7803823 : Blo 2053435 7803823 := bstep (se 1 (by rfl) ⟨5852867, by rfl⟩ : syracuseStep 7803823 = 11705735) B11705735
theorem B10405097 : Blo 2053435 10405097 := bstep (se 2 (by rfl) ⟨3901911, by rfl⟩ : syracuseStep 10405097 = 7803823) B7803823
theorem B6936731 : Blo 2053435 6936731 := bstep (se 1 (by rfl) ⟨5202548, by rfl⟩ : syracuseStep 6936731 = 10405097) B10405097
theorem B4624487 : Blo 2053435 4624487 := bstep (se 1 (by rfl) ⟨3468365, by rfl⟩ : syracuseStep 4624487 = 6936731) B6936731
theorem B3082991 : Blo 2053435 3082991 := bstep (se 1 (by rfl) ⟨2312243, by rfl⟩ : syracuseStep 3082991 = 4624487) B4624487
theorem B2055327 : Blo 2053435 2055327 := bstep (se 1 (by rfl) ⟨1541495, by rfl⟩ : syracuseStep 2055327 = 3082991) B3082991
theorem B3082997 : Blo 2053435 3082997 := bbase (se 5 (by rfl) ⟨144515, by rfl⟩ : syracuseStep 3082997 = 289031) (by norm_num)
theorem B2055331 : Blo 2053435 2055331 := bstep (se 1 (by rfl) ⟨1541498, by rfl⟩ : syracuseStep 2055331 = 3082997) B3082997
theorem B14062805 : Blo 2053435 14062805 := bbase (se 7 (by rfl) ⟨164798, by rfl⟩ : syracuseStep 14062805 = 329597) (by norm_num)
theorem B9375203 : Blo 2053435 9375203 := bstep (se 1 (by rfl) ⟨7031402, by rfl⟩ : syracuseStep 9375203 = 14062805) B14062805
theorem B6250135 : Blo 2053435 6250135 := bstep (se 1 (by rfl) ⟨4687601, by rfl⟩ : syracuseStep 6250135 = 9375203) B9375203
theorem B8333513 : Blo 2053435 8333513 := bstep (se 2 (by rfl) ⟨3125067, by rfl⟩ : syracuseStep 8333513 = 6250135) B6250135
theorem B5555675 : Blo 2053435 5555675 := bstep (se 1 (by rfl) ⟨4166756, by rfl⟩ : syracuseStep 5555675 = 8333513) B8333513
theorem B14815133 : Blo 2053435 14815133 := bstep (se 3 (by rfl) ⟨2777837, by rfl⟩ : syracuseStep 14815133 = 5555675) B5555675
theorem B9876755 : Blo 2053435 9876755 := bstep (se 1 (by rfl) ⟨7407566, by rfl⟩ : syracuseStep 9876755 = 14815133) B14815133
theorem B6584503 : Blo 2053435 6584503 := bstep (se 1 (by rfl) ⟨4938377, by rfl⟩ : syracuseStep 6584503 = 9876755) B9876755
theorem B8779337 : Blo 2053435 8779337 := bstep (se 2 (by rfl) ⟨3292251, by rfl⟩ : syracuseStep 8779337 = 6584503) B6584503
theorem B5852891 : Blo 2053435 5852891 := bstep (se 1 (by rfl) ⟨4389668, by rfl⟩ : syracuseStep 5852891 = 8779337) B8779337
theorem B3901927 : Blo 2053435 3901927 := bstep (se 1 (by rfl) ⟨2926445, by rfl⟩ : syracuseStep 3901927 = 5852891) B5852891
theorem B5202569 : Blo 2053435 5202569 := bstep (se 2 (by rfl) ⟨1950963, by rfl⟩ : syracuseStep 5202569 = 3901927) B3901927
theorem B3468379 : Blo 2053435 3468379 := bstep (se 1 (by rfl) ⟨2601284, by rfl⟩ : syracuseStep 3468379 = 5202569) B5202569
theorem B4624505 : Blo 2053435 4624505 := bstep (se 2 (by rfl) ⟨1734189, by rfl⟩ : syracuseStep 4624505 = 3468379) B3468379
theorem B3083003 : Blo 2053435 3083003 := bstep (se 1 (by rfl) ⟨2312252, by rfl⟩ : syracuseStep 3083003 = 4624505) B4624505
theorem B2055335 : Blo 2053435 2055335 := bstep (se 1 (by rfl) ⟨1541501, by rfl⟩ : syracuseStep 2055335 = 3083003) B3083003
theorem B2312257 : Blo 2053435 2312257 := bbase (se 2 (by rfl) ⟨867096, by rfl⟩ : syracuseStep 2312257 = 1734193) (by norm_num)
theorem B3083009 : Blo 2053435 3083009 := bstep (se 2 (by rfl) ⟨1156128, by rfl⟩ : syracuseStep 3083009 = 2312257) B2312257
theorem B2055339 : Blo 2053435 2055339 := bstep (se 1 (by rfl) ⟨1541504, by rfl⟩ : syracuseStep 2055339 = 3083009) B3083009
theorem B5202589 : Blo 2053435 5202589 := bbase (se 3 (by rfl) ⟨975485, by rfl⟩ : syracuseStep 5202589 = 1950971) (by norm_num)
theorem B6936785 : Blo 2053435 6936785 := bstep (se 2 (by rfl) ⟨2601294, by rfl⟩ : syracuseStep 6936785 = 5202589) B5202589
theorem B4624523 : Blo 2053435 4624523 := bstep (se 1 (by rfl) ⟨3468392, by rfl⟩ : syracuseStep 4624523 = 6936785) B6936785
theorem B3083015 : Blo 2053435 3083015 := bstep (se 1 (by rfl) ⟨2312261, by rfl⟩ : syracuseStep 3083015 = 4624523) B4624523
theorem B2055343 : Blo 2053435 2055343 := bstep (se 1 (by rfl) ⟨1541507, by rfl⟩ : syracuseStep 2055343 = 3083015) B3083015
theorem B3083021 : Blo 2053435 3083021 := bbase (se 3 (by rfl) ⟨578066, by rfl⟩ : syracuseStep 3083021 = 1156133) (by norm_num)
theorem B2055347 : Blo 2053435 2055347 := bstep (se 1 (by rfl) ⟨1541510, by rfl⟩ : syracuseStep 2055347 = 3083021) B3083021
theorem B4624541 : Blo 2053435 4624541 := bbase (se 3 (by rfl) ⟨867101, by rfl⟩ : syracuseStep 4624541 = 1734203) (by norm_num)
theorem B3083027 : Blo 2053435 3083027 := bstep (se 1 (by rfl) ⟨2312270, by rfl⟩ : syracuseStep 3083027 = 4624541) B4624541
theorem B2055351 : Blo 2053435 2055351 := bstep (se 1 (by rfl) ⟨1541513, by rfl⟩ : syracuseStep 2055351 = 3083027) B3083027
theorem B3468413 : Blo 2053435 3468413 := bbase (se 3 (by rfl) ⟨650327, by rfl⟩ : syracuseStep 3468413 = 1300655) (by norm_num)
theorem B2312275 : Blo 2053435 2312275 := bstep (se 1 (by rfl) ⟨1734206, by rfl⟩ : syracuseStep 2312275 = 3468413) B3468413
theorem B3083033 : Blo 2053435 3083033 := bstep (se 2 (by rfl) ⟨1156137, by rfl⟩ : syracuseStep 3083033 = 2312275) B2312275
theorem B2055355 : Blo 2053435 2055355 := bstep (se 1 (by rfl) ⟨1541516, by rfl⟩ : syracuseStep 2055355 = 3083033) B3083033
theorem B9876869 : Blo 2053435 9876869 := bbase (se 4 (by rfl) ⟨925956, by rfl⟩ : syracuseStep 9876869 = 1851913) (by norm_num)
theorem B6584579 : Blo 2053435 6584579 := bstep (se 1 (by rfl) ⟨4938434, by rfl⟩ : syracuseStep 6584579 = 9876869) B9876869
theorem B4389719 : Blo 2053435 4389719 := bstep (se 1 (by rfl) ⟨3292289, by rfl⟩ : syracuseStep 4389719 = 6584579) B6584579
theorem B11705917 : Blo 2053435 11705917 := bstep (se 3 (by rfl) ⟨2194859, by rfl⟩ : syracuseStep 11705917 = 4389719) B4389719
theorem B15607889 : Blo 2053435 15607889 := bstep (se 2 (by rfl) ⟨5852958, by rfl⟩ : syracuseStep 15607889 = 11705917) B11705917
theorem B10405259 : Blo 2053435 10405259 := bstep (se 1 (by rfl) ⟨7803944, by rfl⟩ : syracuseStep 10405259 = 15607889) B15607889
theorem B6936839 : Blo 2053435 6936839 := bstep (se 1 (by rfl) ⟨5202629, by rfl⟩ : syracuseStep 6936839 = 10405259) B10405259
theorem B4624559 : Blo 2053435 4624559 := bstep (se 1 (by rfl) ⟨3468419, by rfl⟩ : syracuseStep 4624559 = 6936839) B6936839
theorem B3083039 : Blo 2053435 3083039 := bstep (se 1 (by rfl) ⟨2312279, by rfl⟩ : syracuseStep 3083039 = 4624559) B4624559
theorem B2055359 : Blo 2053435 2055359 := bstep (se 1 (by rfl) ⟨1541519, by rfl⟩ : syracuseStep 2055359 = 3083039) B3083039
theorem B3083045 : Blo 2053435 3083045 := bbase (se 4 (by rfl) ⟨289035, by rfl⟩ : syracuseStep 3083045 = 578071) (by norm_num)
theorem B2055363 : Blo 2053435 2055363 := bstep (se 1 (by rfl) ⟨1541522, by rfl⟩ : syracuseStep 2055363 = 3083045) B3083045
theorem B2601325 : Blo 2053435 2601325 := bbase (se 3 (by rfl) ⟨487748, by rfl⟩ : syracuseStep 2601325 = 975497) (by norm_num)
theorem B3468433 : Blo 2053435 3468433 := bstep (se 2 (by rfl) ⟨1300662, by rfl⟩ : syracuseStep 3468433 = 2601325) B2601325
theorem B4624577 : Blo 2053435 4624577 := bstep (se 2 (by rfl) ⟨1734216, by rfl⟩ : syracuseStep 4624577 = 3468433) B3468433
theorem B3083051 : Blo 2053435 3083051 := bstep (se 1 (by rfl) ⟨2312288, by rfl⟩ : syracuseStep 3083051 = 4624577) B4624577
theorem B2055367 : Blo 2053435 2055367 := bstep (se 1 (by rfl) ⟨1541525, by rfl⟩ : syracuseStep 2055367 = 3083051) B3083051
theorem B2312293 : Blo 2053435 2312293 := bbase (se 4 (by rfl) ⟨216777, by rfl⟩ : syracuseStep 2312293 = 433555) (by norm_num)
theorem B3083057 : Blo 2053435 3083057 := bstep (se 2 (by rfl) ⟨1156146, by rfl⟩ : syracuseStep 3083057 = 2312293) B2312293
theorem B2055371 : Blo 2053435 2055371 := bstep (se 1 (by rfl) ⟨1541528, by rfl⟩ : syracuseStep 2055371 = 3083057) B3083057
theorem B2194877 : Blo 2053435 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B5853005 : Blo 2053435 5853005 := bstep (se 3 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 5853005 = 2194877) B2194877
theorem B3902003 : Blo 2053435 3902003 := bstep (se 1 (by rfl) ⟨2926502, by rfl⟩ : syracuseStep 3902003 = 5853005) B5853005
theorem B2601335 : Blo 2053435 2601335 := bstep (se 1 (by rfl) ⟨1951001, by rfl⟩ : syracuseStep 2601335 = 3902003) B3902003
theorem B6936893 : Blo 2053435 6936893 := bstep (se 3 (by rfl) ⟨1300667, by rfl⟩ : syracuseStep 6936893 = 2601335) B2601335
theorem B4624595 : Blo 2053435 4624595 := bstep (se 1 (by rfl) ⟨3468446, by rfl⟩ : syracuseStep 4624595 = 6936893) B6936893
theorem B3083063 : Blo 2053435 3083063 := bstep (se 1 (by rfl) ⟨2312297, by rfl⟩ : syracuseStep 3083063 = 4624595) B4624595
theorem B2055375 : Blo 2053435 2055375 := bstep (se 1 (by rfl) ⟨1541531, by rfl⟩ : syracuseStep 2055375 = 3083063) B3083063
theorem B3083069 : Blo 2053435 3083069 := bbase (se 3 (by rfl) ⟨578075, by rfl⟩ : syracuseStep 3083069 = 1156151) (by norm_num)
theorem B2055379 : Blo 2053435 2055379 := bstep (se 1 (by rfl) ⟨1541534, by rfl⟩ : syracuseStep 2055379 = 3083069) B3083069
theorem B4624613 : Blo 2053435 4624613 := bbase (se 4 (by rfl) ⟨433557, by rfl⟩ : syracuseStep 4624613 = 867115) (by norm_num)
theorem B3083075 : Blo 2053435 3083075 := bstep (se 1 (by rfl) ⟨2312306, by rfl⟩ : syracuseStep 3083075 = 4624613) B4624613
theorem B2055383 : Blo 2053435 2055383 := bstep (se 1 (by rfl) ⟨1541537, by rfl⟩ : syracuseStep 2055383 = 3083075) B3083075
theorem B5202701 : Blo 2053435 5202701 := bbase (se 3 (by rfl) ⟨975506, by rfl⟩ : syracuseStep 5202701 = 1951013) (by norm_num)
theorem B3468467 : Blo 2053435 3468467 := bstep (se 1 (by rfl) ⟨2601350, by rfl⟩ : syracuseStep 3468467 = 5202701) B5202701
theorem B2312311 : Blo 2053435 2312311 := bstep (se 1 (by rfl) ⟨1734233, by rfl⟩ : syracuseStep 2312311 = 3468467) B3468467
theorem B3083081 : Blo 2053435 3083081 := bstep (se 2 (by rfl) ⟨1156155, by rfl⟩ : syracuseStep 3083081 = 2312311) B2312311
theorem B2055387 : Blo 2053435 2055387 := bstep (se 1 (by rfl) ⟨1541540, by rfl⟩ : syracuseStep 2055387 = 3083081) B3083081
theorem B2926525 : Blo 2053435 2926525 := bbase (se 3 (by rfl) ⟨548723, by rfl⟩ : syracuseStep 2926525 = 1097447) (by norm_num)
theorem B3902033 : Blo 2053435 3902033 := bstep (se 2 (by rfl) ⟨1463262, by rfl⟩ : syracuseStep 3902033 = 2926525) B2926525
theorem B10405421 : Blo 2053435 10405421 := bstep (se 3 (by rfl) ⟨1951016, by rfl⟩ : syracuseStep 10405421 = 3902033) B3902033
theorem B6936947 : Blo 2053435 6936947 := bstep (se 1 (by rfl) ⟨5202710, by rfl⟩ : syracuseStep 6936947 = 10405421) B10405421
theorem B4624631 : Blo 2053435 4624631 := bstep (se 1 (by rfl) ⟨3468473, by rfl⟩ : syracuseStep 4624631 = 6936947) B6936947
theorem B3083087 : Blo 2053435 3083087 := bstep (se 1 (by rfl) ⟨2312315, by rfl⟩ : syracuseStep 3083087 = 4624631) B4624631
theorem B2055391 : Blo 2053435 2055391 := bstep (se 1 (by rfl) ⟨1541543, by rfl⟩ : syracuseStep 2055391 = 3083087) B3083087
theorem B3083093 : Blo 2053435 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B2055395 : Blo 2053435 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B4389805 : Blo 2053435 4389805 := bbase (se 3 (by rfl) ⟨823088, by rfl⟩ : syracuseStep 4389805 = 1646177) (by norm_num)
theorem B5853073 : Blo 2053435 5853073 := bstep (se 2 (by rfl) ⟨2194902, by rfl⟩ : syracuseStep 5853073 = 4389805) B4389805
theorem B7804097 : Blo 2053435 7804097 := bstep (se 2 (by rfl) ⟨2926536, by rfl⟩ : syracuseStep 7804097 = 5853073) B5853073
theorem B5202731 : Blo 2053435 5202731 := bstep (se 1 (by rfl) ⟨3902048, by rfl⟩ : syracuseStep 5202731 = 7804097) B7804097
theorem B3468487 : Blo 2053435 3468487 := bstep (se 1 (by rfl) ⟨2601365, by rfl⟩ : syracuseStep 3468487 = 5202731) B5202731
theorem B4624649 : Blo 2053435 4624649 := bstep (se 2 (by rfl) ⟨1734243, by rfl⟩ : syracuseStep 4624649 = 3468487) B3468487
theorem B3083099 : Blo 2053435 3083099 := bstep (se 1 (by rfl) ⟨2312324, by rfl⟩ : syracuseStep 3083099 = 4624649) B4624649
theorem B2055399 : Blo 2053435 2055399 := bstep (se 1 (by rfl) ⟨1541549, by rfl⟩ : syracuseStep 2055399 = 3083099) B3083099
theorem B2312329 : Blo 2053435 2312329 := bbase (se 2 (by rfl) ⟨867123, by rfl⟩ : syracuseStep 2312329 = 1734247) (by norm_num)
theorem B3083105 : Blo 2053435 3083105 := bstep (se 2 (by rfl) ⟨1156164, by rfl⟩ : syracuseStep 3083105 = 2312329) B2312329
theorem B2055403 : Blo 2053435 2055403 := bstep (se 1 (by rfl) ⟨1541552, by rfl⟩ : syracuseStep 2055403 = 3083105) B3083105
theorem B35597717 : Blo 2053435 35597717 := bbase (se 6 (by rfl) ⟨834321, by rfl⟩ : syracuseStep 35597717 = 1668643) (by norm_num)
theorem B23731811 : Blo 2053435 23731811 := bstep (se 1 (by rfl) ⟨17798858, by rfl⟩ : syracuseStep 23731811 = 35597717) B35597717
theorem B15821207 : Blo 2053435 15821207 := bstep (se 1 (by rfl) ⟨11865905, by rfl⟩ : syracuseStep 15821207 = 23731811) B23731811
theorem B10547471 : Blo 2053435 10547471 := bstep (se 1 (by rfl) ⟨7910603, by rfl⟩ : syracuseStep 10547471 = 15821207) B15821207
theorem B7031647 : Blo 2053435 7031647 := bstep (se 1 (by rfl) ⟨5273735, by rfl⟩ : syracuseStep 7031647 = 10547471) B10547471
theorem B9375529 : Blo 2053435 9375529 := bstep (se 2 (by rfl) ⟨3515823, by rfl⟩ : syracuseStep 9375529 = 7031647) B7031647
theorem B12500705 : Blo 2053435 12500705 := bstep (se 2 (by rfl) ⟨4687764, by rfl⟩ : syracuseStep 12500705 = 9375529) B9375529
theorem B8333803 : Blo 2053435 8333803 := bstep (se 1 (by rfl) ⟨6250352, by rfl⟩ : syracuseStep 8333803 = 12500705) B12500705
theorem B11111737 : Blo 2053435 11111737 := bstep (se 2 (by rfl) ⟨4166901, by rfl⟩ : syracuseStep 11111737 = 8333803) B8333803
theorem B14815649 : Blo 2053435 14815649 := bstep (se 2 (by rfl) ⟨5555868, by rfl⟩ : syracuseStep 14815649 = 11111737) B11111737
theorem B39508397 : Blo 2053435 39508397 := bstep (se 3 (by rfl) ⟨7407824, by rfl⟩ : syracuseStep 39508397 = 14815649) B14815649
theorem B26338931 : Blo 2053435 26338931 := bstep (se 1 (by rfl) ⟨19754198, by rfl⟩ : syracuseStep 26338931 = 39508397) B39508397
theorem B17559287 : Blo 2053435 17559287 := bstep (se 1 (by rfl) ⟨13169465, by rfl⟩ : syracuseStep 17559287 = 26338931) B26338931
theorem B11706191 : Blo 2053435 11706191 := bstep (se 1 (by rfl) ⟨8779643, by rfl⟩ : syracuseStep 11706191 = 17559287) B17559287
theorem B7804127 : Blo 2053435 7804127 := bstep (se 1 (by rfl) ⟨5853095, by rfl⟩ : syracuseStep 7804127 = 11706191) B11706191
theorem B5202751 : Blo 2053435 5202751 := bstep (se 1 (by rfl) ⟨3902063, by rfl⟩ : syracuseStep 5202751 = 7804127) B7804127
theorem B6937001 : Blo 2053435 6937001 := bstep (se 2 (by rfl) ⟨2601375, by rfl⟩ : syracuseStep 6937001 = 5202751) B5202751
theorem B4624667 : Blo 2053435 4624667 := bstep (se 1 (by rfl) ⟨3468500, by rfl⟩ : syracuseStep 4624667 = 6937001) B6937001
theorem B3083111 : Blo 2053435 3083111 := bstep (se 1 (by rfl) ⟨2312333, by rfl⟩ : syracuseStep 3083111 = 4624667) B4624667
theorem B2055407 : Blo 2053435 2055407 := bstep (se 1 (by rfl) ⟨1541555, by rfl⟩ : syracuseStep 2055407 = 3083111) B3083111
theorem B3083117 : Blo 2053435 3083117 := bbase (se 3 (by rfl) ⟨578084, by rfl⟩ : syracuseStep 3083117 = 1156169) (by norm_num)
theorem B2055411 : Blo 2053435 2055411 := bstep (se 1 (by rfl) ⟨1541558, by rfl⟩ : syracuseStep 2055411 = 3083117) B3083117
theorem B4624685 : Blo 2053435 4624685 := bbase (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) (by norm_num)
theorem B3083123 : Blo 2053435 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B2055415 : Blo 2053435 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B6584773 : Blo 2053435 6584773 := bbase (se 4 (by rfl) ⟨617322, by rfl⟩ : syracuseStep 6584773 = 1234645) (by norm_num)
theorem B8779697 : Blo 2053435 8779697 := bstep (se 2 (by rfl) ⟨3292386, by rfl⟩ : syracuseStep 8779697 = 6584773) B6584773
theorem B5853131 : Blo 2053435 5853131 := bstep (se 1 (by rfl) ⟨4389848, by rfl⟩ : syracuseStep 5853131 = 8779697) B8779697
theorem B3902087 : Blo 2053435 3902087 := bstep (se 1 (by rfl) ⟨2926565, by rfl⟩ : syracuseStep 3902087 = 5853131) B5853131
theorem B2601391 : Blo 2053435 2601391 := bstep (se 1 (by rfl) ⟨1951043, by rfl⟩ : syracuseStep 2601391 = 3902087) B3902087
theorem B3468521 : Blo 2053435 3468521 := bstep (se 2 (by rfl) ⟨1300695, by rfl⟩ : syracuseStep 3468521 = 2601391) B2601391
theorem B2312347 : Blo 2053435 2312347 := bstep (se 1 (by rfl) ⟨1734260, by rfl⟩ : syracuseStep 2312347 = 3468521) B3468521
theorem B3083129 : Blo 2053435 3083129 := bstep (se 2 (by rfl) ⟨1156173, by rfl⟩ : syracuseStep 3083129 = 2312347) B2312347
theorem B2055419 : Blo 2053435 2055419 := bstep (se 1 (by rfl) ⟨1541564, by rfl⟩ : syracuseStep 2055419 = 3083129) B3083129
theorem B3006973 : Blo 2053435 3006973 := bbase (se 3 (by rfl) ⟨563807, by rfl⟩ : syracuseStep 3006973 = 1127615) (by norm_num)
theorem B16037189 : Blo 2053435 16037189 := bstep (se 4 (by rfl) ⟨1503486, by rfl⟩ : syracuseStep 16037189 = 3006973) B3006973
theorem B10691459 : Blo 2053435 10691459 := bstep (se 1 (by rfl) ⟨8018594, by rfl⟩ : syracuseStep 10691459 = 16037189) B16037189
theorem B7127639 : Blo 2053435 7127639 := bstep (se 1 (by rfl) ⟨5345729, by rfl⟩ : syracuseStep 7127639 = 10691459) B10691459
theorem B4751759 : Blo 2053435 4751759 := bstep (se 1 (by rfl) ⟨3563819, by rfl⟩ : syracuseStep 4751759 = 7127639) B7127639
theorem B3167839 : Blo 2053435 3167839 := bstep (se 1 (by rfl) ⟨2375879, by rfl⟩ : syracuseStep 3167839 = 4751759) B4751759
theorem B16895141 : Blo 2053435 16895141 := bstep (se 4 (by rfl) ⟨1583919, by rfl⟩ : syracuseStep 16895141 = 3167839) B3167839
theorem B11263427 : Blo 2053435 11263427 := bstep (se 1 (by rfl) ⟨8447570, by rfl⟩ : syracuseStep 11263427 = 16895141) B16895141
theorem B7508951 : Blo 2053435 7508951 := bstep (se 1 (by rfl) ⟨5631713, by rfl⟩ : syracuseStep 7508951 = 11263427) B11263427
theorem B5005967 : Blo 2053435 5005967 := bstep (se 1 (by rfl) ⟨3754475, by rfl⟩ : syracuseStep 5005967 = 7508951) B7508951
theorem B53396981 : Blo 2053435 53396981 := bstep (se 5 (by rfl) ⟨2502983, by rfl⟩ : syracuseStep 53396981 = 5005967) B5005967
theorem B35597987 : Blo 2053435 35597987 := bstep (se 1 (by rfl) ⟨26698490, by rfl⟩ : syracuseStep 35597987 = 53396981) B53396981
theorem B23731991 : Blo 2053435 23731991 := bstep (se 1 (by rfl) ⟨17798993, by rfl⟩ : syracuseStep 23731991 = 35597987) B35597987
theorem B15821327 : Blo 2053435 15821327 := bstep (se 1 (by rfl) ⟨11865995, by rfl⟩ : syracuseStep 15821327 = 23731991) B23731991
theorem B10547551 : Blo 2053435 10547551 := bstep (se 1 (by rfl) ⟨7910663, by rfl⟩ : syracuseStep 10547551 = 15821327) B15821327
theorem B14063401 : Blo 2053435 14063401 := bstep (se 2 (by rfl) ⟨5273775, by rfl⟩ : syracuseStep 14063401 = 10547551) B10547551
theorem B75004805 : Blo 2053435 75004805 := bstep (se 4 (by rfl) ⟨7031700, by rfl⟩ : syracuseStep 75004805 = 14063401) B14063401
theorem B50003203 : Blo 2053435 50003203 := bstep (se 1 (by rfl) ⟨37502402, by rfl⟩ : syracuseStep 50003203 = 75004805) B75004805
theorem B66670937 : Blo 2053435 66670937 := bstep (se 2 (by rfl) ⟨25001601, by rfl⟩ : syracuseStep 66670937 = 50003203) B50003203
theorem B44447291 : Blo 2053435 44447291 := bstep (se 1 (by rfl) ⟨33335468, by rfl⟩ : syracuseStep 44447291 = 66670937) B66670937
theorem B29631527 : Blo 2053435 29631527 := bstep (se 1 (by rfl) ⟨22223645, by rfl⟩ : syracuseStep 29631527 = 44447291) B44447291
theorem B19754351 : Blo 2053435 19754351 := bstep (se 1 (by rfl) ⟨14815763, by rfl⟩ : syracuseStep 19754351 = 29631527) B29631527
theorem B13169567 : Blo 2053435 13169567 := bstep (se 1 (by rfl) ⟨9877175, by rfl⟩ : syracuseStep 13169567 = 19754351) B19754351
theorem B35118845 : Blo 2053435 35118845 := bstep (se 3 (by rfl) ⟨6584783, by rfl⟩ : syracuseStep 35118845 = 13169567) B13169567
theorem B23412563 : Blo 2053435 23412563 := bstep (se 1 (by rfl) ⟨17559422, by rfl⟩ : syracuseStep 23412563 = 35118845) B35118845
theorem B15608375 : Blo 2053435 15608375 := bstep (se 1 (by rfl) ⟨11706281, by rfl⟩ : syracuseStep 15608375 = 23412563) B23412563
theorem B10405583 : Blo 2053435 10405583 := bstep (se 1 (by rfl) ⟨7804187, by rfl⟩ : syracuseStep 10405583 = 15608375) B15608375
theorem B6937055 : Blo 2053435 6937055 := bstep (se 1 (by rfl) ⟨5202791, by rfl⟩ : syracuseStep 6937055 = 10405583) B10405583
theorem B4624703 : Blo 2053435 4624703 := bstep (se 1 (by rfl) ⟨3468527, by rfl⟩ : syracuseStep 4624703 = 6937055) B6937055
theorem B3083135 : Blo 2053435 3083135 := bstep (se 1 (by rfl) ⟨2312351, by rfl⟩ : syracuseStep 3083135 = 4624703) B4624703
theorem B2055423 : Blo 2053435 2055423 := bstep (se 1 (by rfl) ⟨1541567, by rfl⟩ : syracuseStep 2055423 = 3083135) B3083135
theorem B3083141 : Blo 2053435 3083141 := bbase (se 4 (by rfl) ⟨289044, by rfl⟩ : syracuseStep 3083141 = 578089) (by norm_num)
theorem B2055427 : Blo 2053435 2055427 := bstep (se 1 (by rfl) ⟨1541570, by rfl⟩ : syracuseStep 2055427 = 3083141) B3083141
theorem B3468541 : Blo 2053435 3468541 := bbase (se 3 (by rfl) ⟨650351, by rfl⟩ : syracuseStep 3468541 = 1300703) (by norm_num)
theorem B4624721 : Blo 2053435 4624721 := bstep (se 2 (by rfl) ⟨1734270, by rfl⟩ : syracuseStep 4624721 = 3468541) B3468541
theorem B3083147 : Blo 2053435 3083147 := bstep (se 1 (by rfl) ⟨2312360, by rfl⟩ : syracuseStep 3083147 = 4624721) B4624721
theorem B2055431 : Blo 2053435 2055431 := bstep (se 1 (by rfl) ⟨1541573, by rfl⟩ : syracuseStep 2055431 = 3083147) B3083147
theorem B2312365 : Blo 2053435 2312365 := bbase (se 3 (by rfl) ⟨433568, by rfl⟩ : syracuseStep 2312365 = 867137) (by norm_num)
theorem B3083153 : Blo 2053435 3083153 := bstep (se 2 (by rfl) ⟨1156182, by rfl⟩ : syracuseStep 3083153 = 2312365) B2312365
theorem B2055435 : Blo 2053435 2055435 := bstep (se 1 (by rfl) ⟨1541576, by rfl⟩ : syracuseStep 2055435 = 3083153) B3083153
theorem C0 (j : ℕ) (h1 : 513358 ≤ j) (h2 : j ≤ 513858) : Blo 2053435 (4 * j + 3) := by
  interval_cases j
  · exact B2053435
  · exact B2053439
  · exact B2053443
  · exact B2053447
  · exact B2053451
  · exact B2053455
  · exact B2053459
  · exact B2053463
  · exact B2053467
  · exact B2053471
  · exact B2053475
  · exact B2053479
  · exact B2053483
  · exact B2053487
  · exact B2053491
  · exact B2053495
  · exact B2053499
  · exact B2053503
  · exact B2053507
  · exact B2053511
  · exact B2053515
  · exact B2053519
  · exact B2053523
  · exact B2053527
  · exact B2053531
  · exact B2053535
  · exact B2053539
  · exact B2053543
  · exact B2053547
  · exact B2053551
  · exact B2053555
  · exact B2053559
  · exact B2053563
  · exact B2053567
  · exact B2053571
  · exact B2053575
  · exact B2053579
  · exact B2053583
  · exact B2053587
  · exact B2053591
  · exact B2053595
  · exact B2053599
  · exact B2053603
  · exact B2053607
  · exact B2053611
  · exact B2053615
  · exact B2053619
  · exact B2053623
  · exact B2053627
  · exact B2053631
  · exact B2053635
  · exact B2053639
  · exact B2053643
  · exact B2053647
  · exact B2053651
  · exact B2053655
  · exact B2053659
  · exact B2053663
  · exact B2053667
  · exact B2053671
  · exact B2053675
  · exact B2053679
  · exact B2053683
  · exact B2053687
  · exact B2053691
  · exact B2053695
  · exact B2053699
  · exact B2053703
  · exact B2053707
  · exact B2053711
  · exact B2053715
  · exact B2053719
  · exact B2053723
  · exact B2053727
  · exact B2053731
  · exact B2053735
  · exact B2053739
  · exact B2053743
  · exact B2053747
  · exact B2053751
  · exact B2053755
  · exact B2053759
  · exact B2053763
  · exact B2053767
  · exact B2053771
  · exact B2053775
  · exact B2053779
  · exact B2053783
  · exact B2053787
  · exact B2053791
  · exact B2053795
  · exact B2053799
  · exact B2053803
  · exact B2053807
  · exact B2053811
  · exact B2053815
  · exact B2053819
  · exact B2053823
  · exact B2053827
  · exact B2053831
  · exact B2053835
  · exact B2053839
  · exact B2053843
  · exact B2053847
  · exact B2053851
  · exact B2053855
  · exact B2053859
  · exact B2053863
  · exact B2053867
  · exact B2053871
  · exact B2053875
  · exact B2053879
  · exact B2053883
  · exact B2053887
  · exact B2053891
  · exact B2053895
  · exact B2053899
  · exact B2053903
  · exact B2053907
  · exact B2053911
  · exact B2053915
  · exact B2053919
  · exact B2053923
  · exact B2053927
  · exact B2053931
  · exact B2053935
  · exact B2053939
  · exact B2053943
  · exact B2053947
  · exact B2053951
  · exact B2053955
  · exact B2053959
  · exact B2053963
  · exact B2053967
  · exact B2053971
  · exact B2053975
  · exact B2053979
  · exact B2053983
  · exact B2053987
  · exact B2053991
  · exact B2053995
  · exact B2053999
  · exact B2054003
  · exact B2054007
  · exact B2054011
  · exact B2054015
  · exact B2054019
  · exact B2054023
  · exact B2054027
  · exact B2054031
  · exact B2054035
  · exact B2054039
  · exact B2054043
  · exact B2054047
  · exact B2054051
  · exact B2054055
  · exact B2054059
  · exact B2054063
  · exact B2054067
  · exact B2054071
  · exact B2054075
  · exact B2054079
  · exact B2054083
  · exact B2054087
  · exact B2054091
  · exact B2054095
  · exact B2054099
  · exact B2054103
  · exact B2054107
  · exact B2054111
  · exact B2054115
  · exact B2054119
  · exact B2054123
  · exact B2054127
  · exact B2054131
  · exact B2054135
  · exact B2054139
  · exact B2054143
  · exact B2054147
  · exact B2054151
  · exact B2054155
  · exact B2054159
  · exact B2054163
  · exact B2054167
  · exact B2054171
  · exact B2054175
  · exact B2054179
  · exact B2054183
  · exact B2054187
  · exact B2054191
  · exact B2054195
  · exact B2054199
  · exact B2054203
  · exact B2054207
  · exact B2054211
  · exact B2054215
  · exact B2054219
  · exact B2054223
  · exact B2054227
  · exact B2054231
  · exact B2054235
  · exact B2054239
  · exact B2054243
  · exact B2054247
  · exact B2054251
  · exact B2054255
  · exact B2054259
  · exact B2054263
  · exact B2054267
  · exact B2054271
  · exact B2054275
  · exact B2054279
  · exact B2054283
  · exact B2054287
  · exact B2054291
  · exact B2054295
  · exact B2054299
  · exact B2054303
  · exact B2054307
  · exact B2054311
  · exact B2054315
  · exact B2054319
  · exact B2054323
  · exact B2054327
  · exact B2054331
  · exact B2054335
  · exact B2054339
  · exact B2054343
  · exact B2054347
  · exact B2054351
  · exact B2054355
  · exact B2054359
  · exact B2054363
  · exact B2054367
  · exact B2054371
  · exact B2054375
  · exact B2054379
  · exact B2054383
  · exact B2054387
  · exact B2054391
  · exact B2054395
  · exact B2054399
  · exact B2054403
  · exact B2054407
  · exact B2054411
  · exact B2054415
  · exact B2054419
  · exact B2054423
  · exact B2054427
  · exact B2054431
  · exact B2054435
  · exact B2054439
  · exact B2054443
  · exact B2054447
  · exact B2054451
  · exact B2054455
  · exact B2054459
  · exact B2054463
  · exact B2054467
  · exact B2054471
  · exact B2054475
  · exact B2054479
  · exact B2054483
  · exact B2054487
  · exact B2054491
  · exact B2054495
  · exact B2054499
  · exact B2054503
  · exact B2054507
  · exact B2054511
  · exact B2054515
  · exact B2054519
  · exact B2054523
  · exact B2054527
  · exact B2054531
  · exact B2054535
  · exact B2054539
  · exact B2054543
  · exact B2054547
  · exact B2054551
  · exact B2054555
  · exact B2054559
  · exact B2054563
  · exact B2054567
  · exact B2054571
  · exact B2054575
  · exact B2054579
  · exact B2054583
  · exact B2054587
  · exact B2054591
  · exact B2054595
  · exact B2054599
  · exact B2054603
  · exact B2054607
  · exact B2054611
  · exact B2054615
  · exact B2054619
  · exact B2054623
  · exact B2054627
  · exact B2054631
  · exact B2054635
  · exact B2054639
  · exact B2054643
  · exact B2054647
  · exact B2054651
  · exact B2054655
  · exact B2054659
  · exact B2054663
  · exact B2054667
  · exact B2054671
  · exact B2054675
  · exact B2054679
  · exact B2054683
  · exact B2054687
  · exact B2054691
  · exact B2054695
  · exact B2054699
  · exact B2054703
  · exact B2054707
  · exact B2054711
  · exact B2054715
  · exact B2054719
  · exact B2054723
  · exact B2054727
  · exact B2054731
  · exact B2054735
  · exact B2054739
  · exact B2054743
  · exact B2054747
  · exact B2054751
  · exact B2054755
  · exact B2054759
  · exact B2054763
  · exact B2054767
  · exact B2054771
  · exact B2054775
  · exact B2054779
  · exact B2054783
  · exact B2054787
  · exact B2054791
  · exact B2054795
  · exact B2054799
  · exact B2054803
  · exact B2054807
  · exact B2054811
  · exact B2054815
  · exact B2054819
  · exact B2054823
  · exact B2054827
  · exact B2054831
  · exact B2054835
  · exact B2054839
  · exact B2054843
  · exact B2054847
  · exact B2054851
  · exact B2054855
  · exact B2054859
  · exact B2054863
  · exact B2054867
  · exact B2054871
  · exact B2054875
  · exact B2054879
  · exact B2054883
  · exact B2054887
  · exact B2054891
  · exact B2054895
  · exact B2054899
  · exact B2054903
  · exact B2054907
  · exact B2054911
  · exact B2054915
  · exact B2054919
  · exact B2054923
  · exact B2054927
  · exact B2054931
  · exact B2054935
  · exact B2054939
  · exact B2054943
  · exact B2054947
  · exact B2054951
  · exact B2054955
  · exact B2054959
  · exact B2054963
  · exact B2054967
  · exact B2054971
  · exact B2054975
  · exact B2054979
  · exact B2054983
  · exact B2054987
  · exact B2054991
  · exact B2054995
  · exact B2054999
  · exact B2055003
  · exact B2055007
  · exact B2055011
  · exact B2055015
  · exact B2055019
  · exact B2055023
  · exact B2055027
  · exact B2055031
  · exact B2055035
  · exact B2055039
  · exact B2055043
  · exact B2055047
  · exact B2055051
  · exact B2055055
  · exact B2055059
  · exact B2055063
  · exact B2055067
  · exact B2055071
  · exact B2055075
  · exact B2055079
  · exact B2055083
  · exact B2055087
  · exact B2055091
  · exact B2055095
  · exact B2055099
  · exact B2055103
  · exact B2055107
  · exact B2055111
  · exact B2055115
  · exact B2055119
  · exact B2055123
  · exact B2055127
  · exact B2055131
  · exact B2055135
  · exact B2055139
  · exact B2055143
  · exact B2055147
  · exact B2055151
  · exact B2055155
  · exact B2055159
  · exact B2055163
  · exact B2055167
  · exact B2055171
  · exact B2055175
  · exact B2055179
  · exact B2055183
  · exact B2055187
  · exact B2055191
  · exact B2055195
  · exact B2055199
  · exact B2055203
  · exact B2055207
  · exact B2055211
  · exact B2055215
  · exact B2055219
  · exact B2055223
  · exact B2055227
  · exact B2055231
  · exact B2055235
  · exact B2055239
  · exact B2055243
  · exact B2055247
  · exact B2055251
  · exact B2055255
  · exact B2055259
  · exact B2055263
  · exact B2055267
  · exact B2055271
  · exact B2055275
  · exact B2055279
  · exact B2055283
  · exact B2055287
  · exact B2055291
  · exact B2055295
  · exact B2055299
  · exact B2055303
  · exact B2055307
  · exact B2055311
  · exact B2055315
  · exact B2055319
  · exact B2055323
  · exact B2055327
  · exact B2055331
  · exact B2055335
  · exact B2055339
  · exact B2055343
  · exact B2055347
  · exact B2055351
  · exact B2055355
  · exact B2055359
  · exact B2055363
  · exact B2055367
  · exact B2055371
  · exact B2055375
  · exact B2055379
  · exact B2055383
  · exact B2055387
  · exact B2055391
  · exact B2055395
  · exact B2055399
  · exact B2055403
  · exact B2055407
  · exact B2055411
  · exact B2055415
  · exact B2055419
  · exact B2055423
  · exact B2055427
  · exact B2055431
  · exact B2055435
theorem solution (m : ℕ) (hlo : 2053435 ≤ m) (hhi : m ≤ 2055435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 513358 ≤ j := by omega
    have hj2 : j ≤ 513858 := by omega
    have hb : Blo 2053435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
