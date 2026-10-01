-- Prove2me | solution 1 for syracuse_descends_range_2197435_2199435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:14.958212+00:00
-- url     : https://prove2.me/submissions/8352cccb-eaf6-4a01-8e7a-321115c46d82

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

theorem B3708173 : Blo 2197435 3708173 := bbase (se 3 (by rfl) ⟨695282, by rfl⟩ : syracuseStep 3708173 = 1390565) (by norm_num)
theorem B2472115 : Blo 2197435 2472115 := bstep (se 1 (by rfl) ⟨1854086, by rfl⟩ : syracuseStep 2472115 = 3708173) B3708173
theorem B3296153 : Blo 2197435 3296153 := bstep (se 2 (by rfl) ⟨1236057, by rfl⟩ : syracuseStep 3296153 = 2472115) B2472115
theorem B2197435 : Blo 2197435 2197435 := bstep (se 1 (by rfl) ⟨1648076, by rfl⟩ : syracuseStep 2197435 = 3296153) B3296153
theorem B18772661 : Blo 2197435 18772661 := bbase (se 5 (by rfl) ⟨879968, by rfl⟩ : syracuseStep 18772661 = 1759937) (by norm_num)
theorem B12515107 : Blo 2197435 12515107 := bstep (se 1 (by rfl) ⟨9386330, by rfl⟩ : syracuseStep 12515107 = 18772661) B18772661
theorem B16686809 : Blo 2197435 16686809 := bstep (se 2 (by rfl) ⟨6257553, by rfl⟩ : syracuseStep 16686809 = 12515107) B12515107
theorem B11124539 : Blo 2197435 11124539 := bstep (se 1 (by rfl) ⟨8343404, by rfl⟩ : syracuseStep 11124539 = 16686809) B16686809
theorem B7416359 : Blo 2197435 7416359 := bstep (se 1 (by rfl) ⟨5562269, by rfl⟩ : syracuseStep 7416359 = 11124539) B11124539
theorem B4944239 : Blo 2197435 4944239 := bstep (se 1 (by rfl) ⟨3708179, by rfl⟩ : syracuseStep 4944239 = 7416359) B7416359
theorem B3296159 : Blo 2197435 3296159 := bstep (se 1 (by rfl) ⟨2472119, by rfl⟩ : syracuseStep 3296159 = 4944239) B4944239
theorem B2197439 : Blo 2197435 2197439 := bstep (se 1 (by rfl) ⟨1648079, by rfl⟩ : syracuseStep 2197439 = 3296159) B3296159
theorem B3296165 : Blo 2197435 3296165 := bbase (se 4 (by rfl) ⟨309015, by rfl⟩ : syracuseStep 3296165 = 618031) (by norm_num)
theorem B2197443 : Blo 2197435 2197443 := bstep (se 1 (by rfl) ⟨1648082, by rfl⟩ : syracuseStep 2197443 = 3296165) B3296165
theorem B2781145 : Blo 2197435 2781145 := bbase (se 2 (by rfl) ⟨1042929, by rfl⟩ : syracuseStep 2781145 = 2085859) (by norm_num)
theorem B3708193 : Blo 2197435 3708193 := bstep (se 2 (by rfl) ⟨1390572, by rfl⟩ : syracuseStep 3708193 = 2781145) B2781145
theorem B4944257 : Blo 2197435 4944257 := bstep (se 2 (by rfl) ⟨1854096, by rfl⟩ : syracuseStep 4944257 = 3708193) B3708193
theorem B3296171 : Blo 2197435 3296171 := bstep (se 1 (by rfl) ⟨2472128, by rfl⟩ : syracuseStep 3296171 = 4944257) B4944257
theorem B2197447 : Blo 2197435 2197447 := bstep (se 1 (by rfl) ⟨1648085, by rfl⟩ : syracuseStep 2197447 = 3296171) B3296171
theorem B2472133 : Blo 2197435 2472133 := bbase (se 4 (by rfl) ⟨231762, by rfl⟩ : syracuseStep 2472133 = 463525) (by norm_num)
theorem B3296177 : Blo 2197435 3296177 := bstep (se 2 (by rfl) ⟨1236066, by rfl⟩ : syracuseStep 3296177 = 2472133) B2472133
theorem B2197451 : Blo 2197435 2197451 := bstep (se 1 (by rfl) ⟨1648088, by rfl⟩ : syracuseStep 2197451 = 3296177) B3296177
theorem B4171733 : Blo 2197435 4171733 := bbase (se 7 (by rfl) ⟨48887, by rfl⟩ : syracuseStep 4171733 = 97775) (by norm_num)
theorem B2781155 : Blo 2197435 2781155 := bstep (se 1 (by rfl) ⟨2085866, by rfl⟩ : syracuseStep 2781155 = 4171733) B4171733
theorem B7416413 : Blo 2197435 7416413 := bstep (se 3 (by rfl) ⟨1390577, by rfl⟩ : syracuseStep 7416413 = 2781155) B2781155
theorem B4944275 : Blo 2197435 4944275 := bstep (se 1 (by rfl) ⟨3708206, by rfl⟩ : syracuseStep 4944275 = 7416413) B7416413
theorem B3296183 : Blo 2197435 3296183 := bstep (se 1 (by rfl) ⟨2472137, by rfl⟩ : syracuseStep 3296183 = 4944275) B4944275
theorem B2197455 : Blo 2197435 2197455 := bstep (se 1 (by rfl) ⟨1648091, by rfl⟩ : syracuseStep 2197455 = 3296183) B3296183
theorem B3296189 : Blo 2197435 3296189 := bbase (se 3 (by rfl) ⟨618035, by rfl⟩ : syracuseStep 3296189 = 1236071) (by norm_num)
theorem B2197459 : Blo 2197435 2197459 := bstep (se 1 (by rfl) ⟨1648094, by rfl⟩ : syracuseStep 2197459 = 3296189) B3296189
theorem B4944293 : Blo 2197435 4944293 := bbase (se 4 (by rfl) ⟨463527, by rfl⟩ : syracuseStep 4944293 = 927055) (by norm_num)
theorem B3296195 : Blo 2197435 3296195 := bstep (se 1 (by rfl) ⟨2472146, by rfl⟩ : syracuseStep 3296195 = 4944293) B4944293
theorem B2197463 : Blo 2197435 2197463 := bstep (se 1 (by rfl) ⟨1648097, by rfl⟩ : syracuseStep 2197463 = 3296195) B3296195
theorem B5562341 : Blo 2197435 5562341 := bbase (se 4 (by rfl) ⟨521469, by rfl⟩ : syracuseStep 5562341 = 1042939) (by norm_num)
theorem B3708227 : Blo 2197435 3708227 := bstep (se 1 (by rfl) ⟨2781170, by rfl⟩ : syracuseStep 3708227 = 5562341) B5562341
theorem B2472151 : Blo 2197435 2472151 := bstep (se 1 (by rfl) ⟨1854113, by rfl⟩ : syracuseStep 2472151 = 3708227) B3708227
theorem B3296201 : Blo 2197435 3296201 := bstep (se 2 (by rfl) ⟨1236075, by rfl⟩ : syracuseStep 3296201 = 2472151) B2472151
theorem B2197467 : Blo 2197435 2197467 := bstep (se 1 (by rfl) ⟨1648100, by rfl⟩ : syracuseStep 2197467 = 3296201) B3296201
theorem B2346617 : Blo 2197435 2346617 := bbase (se 2 (by rfl) ⟨879981, by rfl⟩ : syracuseStep 2346617 = 1759963) (by norm_num)
theorem B6257645 : Blo 2197435 6257645 := bstep (se 3 (by rfl) ⟨1173308, by rfl⟩ : syracuseStep 6257645 = 2346617) B2346617
theorem B4171763 : Blo 2197435 4171763 := bstep (se 1 (by rfl) ⟨3128822, by rfl⟩ : syracuseStep 4171763 = 6257645) B6257645
theorem B11124701 : Blo 2197435 11124701 := bstep (se 3 (by rfl) ⟨2085881, by rfl⟩ : syracuseStep 11124701 = 4171763) B4171763
theorem B7416467 : Blo 2197435 7416467 := bstep (se 1 (by rfl) ⟨5562350, by rfl⟩ : syracuseStep 7416467 = 11124701) B11124701
theorem B4944311 : Blo 2197435 4944311 := bstep (se 1 (by rfl) ⟨3708233, by rfl⟩ : syracuseStep 4944311 = 7416467) B7416467
theorem B3296207 : Blo 2197435 3296207 := bstep (se 1 (by rfl) ⟨2472155, by rfl⟩ : syracuseStep 3296207 = 4944311) B4944311
theorem B2197471 : Blo 2197435 2197471 := bstep (se 1 (by rfl) ⟨1648103, by rfl⟩ : syracuseStep 2197471 = 3296207) B3296207
theorem B3296213 : Blo 2197435 3296213 := bbase (se 7 (by rfl) ⟨38627, by rfl⟩ : syracuseStep 3296213 = 77255) (by norm_num)
theorem B2197475 : Blo 2197435 2197475 := bstep (se 1 (by rfl) ⟨1648106, by rfl⟩ : syracuseStep 2197475 = 3296213) B3296213
theorem B8343557 : Blo 2197435 8343557 := bbase (se 4 (by rfl) ⟨782208, by rfl⟩ : syracuseStep 8343557 = 1564417) (by norm_num)
theorem B5562371 : Blo 2197435 5562371 := bstep (se 1 (by rfl) ⟨4171778, by rfl⟩ : syracuseStep 5562371 = 8343557) B8343557
theorem B3708247 : Blo 2197435 3708247 := bstep (se 1 (by rfl) ⟨2781185, by rfl⟩ : syracuseStep 3708247 = 5562371) B5562371
theorem B4944329 : Blo 2197435 4944329 := bstep (se 2 (by rfl) ⟨1854123, by rfl⟩ : syracuseStep 4944329 = 3708247) B3708247
theorem B3296219 : Blo 2197435 3296219 := bstep (se 1 (by rfl) ⟨2472164, by rfl⟩ : syracuseStep 3296219 = 4944329) B4944329
theorem B2197479 : Blo 2197435 2197479 := bstep (se 1 (by rfl) ⟨1648109, by rfl⟩ : syracuseStep 2197479 = 3296219) B3296219
theorem B2472169 : Blo 2197435 2472169 := bbase (se 2 (by rfl) ⟨927063, by rfl⟩ : syracuseStep 2472169 = 1854127) (by norm_num)
theorem B3296225 : Blo 2197435 3296225 := bstep (se 2 (by rfl) ⟨1236084, by rfl⟩ : syracuseStep 3296225 = 2472169) B2472169
theorem B2197483 : Blo 2197435 2197483 := bstep (se 1 (by rfl) ⟨1648112, by rfl⟩ : syracuseStep 2197483 = 3296225) B3296225
theorem B12515381 : Blo 2197435 12515381 := bbase (se 5 (by rfl) ⟨586658, by rfl⟩ : syracuseStep 12515381 = 1173317) (by norm_num)
theorem B8343587 : Blo 2197435 8343587 := bstep (se 1 (by rfl) ⟨6257690, by rfl⟩ : syracuseStep 8343587 = 12515381) B12515381
theorem B5562391 : Blo 2197435 5562391 := bstep (se 1 (by rfl) ⟨4171793, by rfl⟩ : syracuseStep 5562391 = 8343587) B8343587
theorem B7416521 : Blo 2197435 7416521 := bstep (se 2 (by rfl) ⟨2781195, by rfl⟩ : syracuseStep 7416521 = 5562391) B5562391
theorem B4944347 : Blo 2197435 4944347 := bstep (se 1 (by rfl) ⟨3708260, by rfl⟩ : syracuseStep 4944347 = 7416521) B7416521
theorem B3296231 : Blo 2197435 3296231 := bstep (se 1 (by rfl) ⟨2472173, by rfl⟩ : syracuseStep 3296231 = 4944347) B4944347
theorem B2197487 : Blo 2197435 2197487 := bstep (se 1 (by rfl) ⟨1648115, by rfl⟩ : syracuseStep 2197487 = 3296231) B3296231
theorem B3296237 : Blo 2197435 3296237 := bbase (se 3 (by rfl) ⟨618044, by rfl⟩ : syracuseStep 3296237 = 1236089) (by norm_num)
theorem B2197491 : Blo 2197435 2197491 := bstep (se 1 (by rfl) ⟨1648118, by rfl⟩ : syracuseStep 2197491 = 3296237) B3296237
theorem B4944365 : Blo 2197435 4944365 := bbase (se 3 (by rfl) ⟨927068, by rfl⟩ : syracuseStep 4944365 = 1854137) (by norm_num)
theorem B3296243 : Blo 2197435 3296243 := bstep (se 1 (by rfl) ⟨2472182, by rfl⟩ : syracuseStep 3296243 = 4944365) B4944365
theorem B2197495 : Blo 2197435 2197495 := bstep (se 1 (by rfl) ⟨1648121, by rfl⟩ : syracuseStep 2197495 = 3296243) B3296243
theorem B3567997 : Blo 2197435 3567997 := bbase (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) (by norm_num)
theorem B4757329 : Blo 2197435 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B6343105 : Blo 2197435 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B8457473 : Blo 2197435 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B22553261 : Blo 2197435 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B15035507 : Blo 2197435 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B10023671 : Blo 2197435 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B6682447 : Blo 2197435 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B8909929 : Blo 2197435 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B11879905 : Blo 2197435 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B15839873 : Blo 2197435 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B10559915 : Blo 2197435 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B7039943 : Blo 2197435 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B4693295 : Blo 2197435 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B3128863 : Blo 2197435 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B4171817 : Blo 2197435 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B2781211 : Blo 2197435 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B3708281 : Blo 2197435 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B2472187 : Blo 2197435 2472187 := bstep (se 1 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 2472187 = 3708281) B3708281
theorem B3296249 : Blo 2197435 3296249 := bstep (se 2 (by rfl) ⟨1236093, by rfl⟩ : syracuseStep 3296249 = 2472187) B2472187
theorem B2197499 : Blo 2197435 2197499 := bstep (se 1 (by rfl) ⟨1648124, by rfl⟩ : syracuseStep 2197499 = 3296249) B3296249
theorem B2676001 : Blo 2197435 2676001 := bbase (se 2 (by rfl) ⟨1003500, by rfl⟩ : syracuseStep 2676001 = 2007001) (by norm_num)
theorem B3568001 : Blo 2197435 3568001 := bstep (se 2 (by rfl) ⟨1338000, by rfl⟩ : syracuseStep 3568001 = 2676001) B2676001
theorem B9514669 : Blo 2197435 9514669 := bstep (se 3 (by rfl) ⟨1784000, by rfl⟩ : syracuseStep 9514669 = 3568001) B3568001
theorem B12686225 : Blo 2197435 12686225 := bstep (se 2 (by rfl) ⟨4757334, by rfl⟩ : syracuseStep 12686225 = 9514669) B9514669
theorem B33829933 : Blo 2197435 33829933 := bstep (se 3 (by rfl) ⟨6343112, by rfl⟩ : syracuseStep 33829933 = 12686225) B12686225
theorem B45106577 : Blo 2197435 45106577 := bstep (se 2 (by rfl) ⟨16914966, by rfl⟩ : syracuseStep 45106577 = 33829933) B33829933
theorem B30071051 : Blo 2197435 30071051 := bstep (se 1 (by rfl) ⟨22553288, by rfl⟩ : syracuseStep 30071051 = 45106577) B45106577
theorem B20047367 : Blo 2197435 20047367 := bstep (se 1 (by rfl) ⟨15035525, by rfl⟩ : syracuseStep 20047367 = 30071051) B30071051
theorem B13364911 : Blo 2197435 13364911 := bstep (se 1 (by rfl) ⟨10023683, by rfl⟩ : syracuseStep 13364911 = 20047367) B20047367
theorem B17819881 : Blo 2197435 17819881 := bstep (se 2 (by rfl) ⟨6682455, by rfl⟩ : syracuseStep 17819881 = 13364911) B13364911
theorem B95039365 : Blo 2197435 95039365 := bstep (se 4 (by rfl) ⟨8909940, by rfl⟩ : syracuseStep 95039365 = 17819881) B17819881
theorem B126719153 : Blo 2197435 126719153 := bstep (se 2 (by rfl) ⟨47519682, by rfl⟩ : syracuseStep 126719153 = 95039365) B95039365
theorem B84479435 : Blo 2197435 84479435 := bstep (se 1 (by rfl) ⟨63359576, by rfl⟩ : syracuseStep 84479435 = 126719153) B126719153
theorem B56319623 : Blo 2197435 56319623 := bstep (se 1 (by rfl) ⟨42239717, by rfl⟩ : syracuseStep 56319623 = 84479435) B84479435
theorem B37546415 : Blo 2197435 37546415 := bstep (se 1 (by rfl) ⟨28159811, by rfl⟩ : syracuseStep 37546415 = 56319623) B56319623
theorem B25030943 : Blo 2197435 25030943 := bstep (se 1 (by rfl) ⟨18773207, by rfl⟩ : syracuseStep 25030943 = 37546415) B37546415
theorem B16687295 : Blo 2197435 16687295 := bstep (se 1 (by rfl) ⟨12515471, by rfl⟩ : syracuseStep 16687295 = 25030943) B25030943
theorem B11124863 : Blo 2197435 11124863 := bstep (se 1 (by rfl) ⟨8343647, by rfl⟩ : syracuseStep 11124863 = 16687295) B16687295
theorem B7416575 : Blo 2197435 7416575 := bstep (se 1 (by rfl) ⟨5562431, by rfl⟩ : syracuseStep 7416575 = 11124863) B11124863
theorem B4944383 : Blo 2197435 4944383 := bstep (se 1 (by rfl) ⟨3708287, by rfl⟩ : syracuseStep 4944383 = 7416575) B7416575
theorem B3296255 : Blo 2197435 3296255 := bstep (se 1 (by rfl) ⟨2472191, by rfl⟩ : syracuseStep 3296255 = 4944383) B4944383
theorem B2197503 : Blo 2197435 2197503 := bstep (se 1 (by rfl) ⟨1648127, by rfl⟩ : syracuseStep 2197503 = 3296255) B3296255
theorem B3296261 : Blo 2197435 3296261 := bbase (se 4 (by rfl) ⟨309024, by rfl⟩ : syracuseStep 3296261 = 618049) (by norm_num)
theorem B2197507 : Blo 2197435 2197507 := bstep (se 1 (by rfl) ⟨1648130, by rfl⟩ : syracuseStep 2197507 = 3296261) B3296261
theorem B3708301 : Blo 2197435 3708301 := bbase (se 3 (by rfl) ⟨695306, by rfl⟩ : syracuseStep 3708301 = 1390613) (by norm_num)
theorem B4944401 : Blo 2197435 4944401 := bstep (se 2 (by rfl) ⟨1854150, by rfl⟩ : syracuseStep 4944401 = 3708301) B3708301
theorem B3296267 : Blo 2197435 3296267 := bstep (se 1 (by rfl) ⟨2472200, by rfl⟩ : syracuseStep 3296267 = 4944401) B4944401
theorem B2197511 : Blo 2197435 2197511 := bstep (se 1 (by rfl) ⟨1648133, by rfl⟩ : syracuseStep 2197511 = 3296267) B3296267
theorem B2472205 : Blo 2197435 2472205 := bbase (se 3 (by rfl) ⟨463538, by rfl⟩ : syracuseStep 2472205 = 927077) (by norm_num)
theorem B3296273 : Blo 2197435 3296273 := bstep (se 2 (by rfl) ⟨1236102, by rfl⟩ : syracuseStep 3296273 = 2472205) B2472205
theorem B2197515 : Blo 2197435 2197515 := bstep (se 1 (by rfl) ⟨1648136, by rfl⟩ : syracuseStep 2197515 = 3296273) B3296273
theorem B7416629 : Blo 2197435 7416629 := bbase (se 5 (by rfl) ⟨347654, by rfl⟩ : syracuseStep 7416629 = 695309) (by norm_num)
theorem B4944419 : Blo 2197435 4944419 := bstep (se 1 (by rfl) ⟨3708314, by rfl⟩ : syracuseStep 4944419 = 7416629) B7416629
theorem B3296279 : Blo 2197435 3296279 := bstep (se 1 (by rfl) ⟨2472209, by rfl⟩ : syracuseStep 3296279 = 4944419) B4944419
theorem B2197519 : Blo 2197435 2197519 := bstep (se 1 (by rfl) ⟨1648139, by rfl⟩ : syracuseStep 2197519 = 3296279) B3296279
theorem B3296285 : Blo 2197435 3296285 := bbase (se 3 (by rfl) ⟨618053, by rfl⟩ : syracuseStep 3296285 = 1236107) (by norm_num)
theorem B2197523 : Blo 2197435 2197523 := bstep (se 1 (by rfl) ⟨1648142, by rfl⟩ : syracuseStep 2197523 = 3296285) B3296285
theorem B4944437 : Blo 2197435 4944437 := bbase (se 5 (by rfl) ⟨231770, by rfl⟩ : syracuseStep 4944437 = 463541) (by norm_num)
theorem B3296291 : Blo 2197435 3296291 := bstep (se 1 (by rfl) ⟨2472218, by rfl⟩ : syracuseStep 3296291 = 4944437) B4944437
theorem B2197527 : Blo 2197435 2197527 := bstep (se 1 (by rfl) ⟨1648145, by rfl⟩ : syracuseStep 2197527 = 3296291) B3296291
theorem B9386725 : Blo 2197435 9386725 := bbase (se 4 (by rfl) ⟨880005, by rfl⟩ : syracuseStep 9386725 = 1760011) (by norm_num)
theorem B12515633 : Blo 2197435 12515633 := bstep (se 2 (by rfl) ⟨4693362, by rfl⟩ : syracuseStep 12515633 = 9386725) B9386725
theorem B8343755 : Blo 2197435 8343755 := bstep (se 1 (by rfl) ⟨6257816, by rfl⟩ : syracuseStep 8343755 = 12515633) B12515633
theorem B5562503 : Blo 2197435 5562503 := bstep (se 1 (by rfl) ⟨4171877, by rfl⟩ : syracuseStep 5562503 = 8343755) B8343755
theorem B3708335 : Blo 2197435 3708335 := bstep (se 1 (by rfl) ⟨2781251, by rfl⟩ : syracuseStep 3708335 = 5562503) B5562503
theorem B2472223 : Blo 2197435 2472223 := bstep (se 1 (by rfl) ⟨1854167, by rfl⟩ : syracuseStep 2472223 = 3708335) B3708335
theorem B3296297 : Blo 2197435 3296297 := bstep (se 2 (by rfl) ⟨1236111, by rfl⟩ : syracuseStep 3296297 = 2472223) B2472223
theorem B2197531 : Blo 2197435 2197531 := bstep (se 1 (by rfl) ⟨1648148, by rfl⟩ : syracuseStep 2197531 = 3296297) B3296297
theorem B9386741 : Blo 2197435 9386741 := bbase (se 5 (by rfl) ⟨440003, by rfl⟩ : syracuseStep 9386741 = 880007) (by norm_num)
theorem B6257827 : Blo 2197435 6257827 := bstep (se 1 (by rfl) ⟨4693370, by rfl⟩ : syracuseStep 6257827 = 9386741) B9386741
theorem B8343769 : Blo 2197435 8343769 := bstep (se 2 (by rfl) ⟨3128913, by rfl⟩ : syracuseStep 8343769 = 6257827) B6257827
theorem B11125025 : Blo 2197435 11125025 := bstep (se 2 (by rfl) ⟨4171884, by rfl⟩ : syracuseStep 11125025 = 8343769) B8343769
theorem B7416683 : Blo 2197435 7416683 := bstep (se 1 (by rfl) ⟨5562512, by rfl⟩ : syracuseStep 7416683 = 11125025) B11125025
theorem B4944455 : Blo 2197435 4944455 := bstep (se 1 (by rfl) ⟨3708341, by rfl⟩ : syracuseStep 4944455 = 7416683) B7416683
theorem B3296303 : Blo 2197435 3296303 := bstep (se 1 (by rfl) ⟨2472227, by rfl⟩ : syracuseStep 3296303 = 4944455) B4944455
theorem B2197535 : Blo 2197435 2197535 := bstep (se 1 (by rfl) ⟨1648151, by rfl⟩ : syracuseStep 2197535 = 3296303) B3296303
theorem B3296309 : Blo 2197435 3296309 := bbase (se 5 (by rfl) ⟨154514, by rfl⟩ : syracuseStep 3296309 = 309029) (by norm_num)
theorem B2197539 : Blo 2197435 2197539 := bstep (se 1 (by rfl) ⟨1648154, by rfl⟩ : syracuseStep 2197539 = 3296309) B3296309
theorem B5562533 : Blo 2197435 5562533 := bbase (se 4 (by rfl) ⟨521487, by rfl⟩ : syracuseStep 5562533 = 1042975) (by norm_num)
theorem B3708355 : Blo 2197435 3708355 := bstep (se 1 (by rfl) ⟨2781266, by rfl⟩ : syracuseStep 3708355 = 5562533) B5562533
theorem B4944473 : Blo 2197435 4944473 := bstep (se 2 (by rfl) ⟨1854177, by rfl⟩ : syracuseStep 4944473 = 3708355) B3708355
theorem B3296315 : Blo 2197435 3296315 := bstep (se 1 (by rfl) ⟨2472236, by rfl⟩ : syracuseStep 3296315 = 4944473) B4944473
theorem B2197543 : Blo 2197435 2197543 := bstep (se 1 (by rfl) ⟨1648157, by rfl⟩ : syracuseStep 2197543 = 3296315) B3296315
theorem B2472241 : Blo 2197435 2472241 := bbase (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) (by norm_num)
theorem B3296321 : Blo 2197435 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B2197547 : Blo 2197435 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B4693405 : Blo 2197435 4693405 := bbase (se 3 (by rfl) ⟨880013, by rfl⟩ : syracuseStep 4693405 = 1760027) (by norm_num)
theorem B6257873 : Blo 2197435 6257873 := bstep (se 2 (by rfl) ⟨2346702, by rfl⟩ : syracuseStep 6257873 = 4693405) B4693405
theorem B4171915 : Blo 2197435 4171915 := bstep (se 1 (by rfl) ⟨3128936, by rfl⟩ : syracuseStep 4171915 = 6257873) B6257873
theorem B5562553 : Blo 2197435 5562553 := bstep (se 2 (by rfl) ⟨2085957, by rfl⟩ : syracuseStep 5562553 = 4171915) B4171915
theorem B7416737 : Blo 2197435 7416737 := bstep (se 2 (by rfl) ⟨2781276, by rfl⟩ : syracuseStep 7416737 = 5562553) B5562553
theorem B4944491 : Blo 2197435 4944491 := bstep (se 1 (by rfl) ⟨3708368, by rfl⟩ : syracuseStep 4944491 = 7416737) B7416737
theorem B3296327 : Blo 2197435 3296327 := bstep (se 1 (by rfl) ⟨2472245, by rfl⟩ : syracuseStep 3296327 = 4944491) B4944491
theorem B2197551 : Blo 2197435 2197551 := bstep (se 1 (by rfl) ⟨1648163, by rfl⟩ : syracuseStep 2197551 = 3296327) B3296327
theorem B3296333 : Blo 2197435 3296333 := bbase (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) (by norm_num)
theorem B2197555 : Blo 2197435 2197555 := bstep (se 1 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 2197555 = 3296333) B3296333
theorem B4944509 : Blo 2197435 4944509 := bbase (se 3 (by rfl) ⟨927095, by rfl⟩ : syracuseStep 4944509 = 1854191) (by norm_num)
theorem B3296339 : Blo 2197435 3296339 := bstep (se 1 (by rfl) ⟨2472254, by rfl⟩ : syracuseStep 3296339 = 4944509) B4944509
theorem B2197559 : Blo 2197435 2197559 := bstep (se 1 (by rfl) ⟨1648169, by rfl⟩ : syracuseStep 2197559 = 3296339) B3296339
theorem B3708389 : Blo 2197435 3708389 := bbase (se 4 (by rfl) ⟨347661, by rfl⟩ : syracuseStep 3708389 = 695323) (by norm_num)
theorem B2472259 : Blo 2197435 2472259 := bstep (se 1 (by rfl) ⟨1854194, by rfl⟩ : syracuseStep 2472259 = 3708389) B3708389
theorem B3296345 : Blo 2197435 3296345 := bstep (se 2 (by rfl) ⟨1236129, by rfl⟩ : syracuseStep 3296345 = 2472259) B2472259
theorem B2197563 : Blo 2197435 2197563 := bstep (se 1 (by rfl) ⟨1648172, by rfl⟩ : syracuseStep 2197563 = 3296345) B3296345
theorem B10299365 : Blo 2197435 10299365 := bbase (se 4 (by rfl) ⟨965565, by rfl⟩ : syracuseStep 10299365 = 1931131) (by norm_num)
theorem B6866243 : Blo 2197435 6866243 := bstep (se 1 (by rfl) ⟨5149682, by rfl⟩ : syracuseStep 6866243 = 10299365) B10299365
theorem B4577495 : Blo 2197435 4577495 := bstep (se 1 (by rfl) ⟨3433121, by rfl⟩ : syracuseStep 4577495 = 6866243) B6866243
theorem B48826613 : Blo 2197435 48826613 := bstep (se 5 (by rfl) ⟨2288747, by rfl⟩ : syracuseStep 48826613 = 4577495) B4577495
theorem B130204301 : Blo 2197435 130204301 := bstep (se 3 (by rfl) ⟨24413306, by rfl⟩ : syracuseStep 130204301 = 48826613) B48826613
theorem B347211469 : Blo 2197435 347211469 := bstep (se 3 (by rfl) ⟨65102150, by rfl⟩ : syracuseStep 347211469 = 130204301) B130204301
theorem B462948625 : Blo 2197435 462948625 := bstep (se 2 (by rfl) ⟨173605734, by rfl⟩ : syracuseStep 462948625 = 347211469) B347211469
theorem B617264833 : Blo 2197435 617264833 := bstep (se 2 (by rfl) ⟨231474312, by rfl⟩ : syracuseStep 617264833 = 462948625) B462948625
theorem B823019777 : Blo 2197435 823019777 := bstep (se 2 (by rfl) ⟨308632416, by rfl⟩ : syracuseStep 823019777 = 617264833) B617264833
theorem B548679851 : Blo 2197435 548679851 := bstep (se 1 (by rfl) ⟨411509888, by rfl⟩ : syracuseStep 548679851 = 823019777) B823019777
theorem B365786567 : Blo 2197435 365786567 := bstep (se 1 (by rfl) ⟨274339925, by rfl⟩ : syracuseStep 365786567 = 548679851) B548679851
theorem B243857711 : Blo 2197435 243857711 := bstep (se 1 (by rfl) ⟨182893283, by rfl⟩ : syracuseStep 243857711 = 365786567) B365786567
theorem B162571807 : Blo 2197435 162571807 := bstep (se 1 (by rfl) ⟨121928855, by rfl⟩ : syracuseStep 162571807 = 243857711) B243857711
theorem B216762409 : Blo 2197435 216762409 := bstep (se 2 (by rfl) ⟨81285903, by rfl⟩ : syracuseStep 216762409 = 162571807) B162571807
theorem B289016545 : Blo 2197435 289016545 := bstep (se 2 (by rfl) ⟨108381204, by rfl⟩ : syracuseStep 289016545 = 216762409) B216762409
theorem B385355393 : Blo 2197435 385355393 := bstep (se 2 (by rfl) ⟨144508272, by rfl⟩ : syracuseStep 385355393 = 289016545) B289016545
theorem B256903595 : Blo 2197435 256903595 := bstep (se 1 (by rfl) ⟨192677696, by rfl⟩ : syracuseStep 256903595 = 385355393) B385355393
theorem B171269063 : Blo 2197435 171269063 := bstep (se 1 (by rfl) ⟨128451797, by rfl⟩ : syracuseStep 171269063 = 256903595) B256903595
theorem B114179375 : Blo 2197435 114179375 := bstep (se 1 (by rfl) ⟨85634531, by rfl⟩ : syracuseStep 114179375 = 171269063) B171269063
theorem B76119583 : Blo 2197435 76119583 := bstep (se 1 (by rfl) ⟨57089687, by rfl⟩ : syracuseStep 76119583 = 114179375) B114179375
theorem B101492777 : Blo 2197435 101492777 := bstep (se 2 (by rfl) ⟨38059791, by rfl⟩ : syracuseStep 101492777 = 76119583) B76119583
theorem B67661851 : Blo 2197435 67661851 := bstep (se 1 (by rfl) ⟨50746388, by rfl⟩ : syracuseStep 67661851 = 101492777) B101492777
theorem B90215801 : Blo 2197435 90215801 := bstep (se 2 (by rfl) ⟨33830925, by rfl⟩ : syracuseStep 90215801 = 67661851) B67661851
theorem B60143867 : Blo 2197435 60143867 := bstep (se 1 (by rfl) ⟨45107900, by rfl⟩ : syracuseStep 60143867 = 90215801) B90215801
theorem B40095911 : Blo 2197435 40095911 := bstep (se 1 (by rfl) ⟨30071933, by rfl⟩ : syracuseStep 40095911 = 60143867) B60143867
theorem B26730607 : Blo 2197435 26730607 := bstep (se 1 (by rfl) ⟨20047955, by rfl⟩ : syracuseStep 26730607 = 40095911) B40095911
theorem B35640809 : Blo 2197435 35640809 := bstep (se 2 (by rfl) ⟨13365303, by rfl⟩ : syracuseStep 35640809 = 26730607) B26730607
theorem B23760539 : Blo 2197435 23760539 := bstep (se 1 (by rfl) ⟨17820404, by rfl⟩ : syracuseStep 23760539 = 35640809) B35640809
theorem B15840359 : Blo 2197435 15840359 := bstep (se 1 (by rfl) ⟨11880269, by rfl⟩ : syracuseStep 15840359 = 23760539) B23760539
theorem B10560239 : Blo 2197435 10560239 := bstep (se 1 (by rfl) ⟨7920179, by rfl⟩ : syracuseStep 10560239 = 15840359) B15840359
theorem B7040159 : Blo 2197435 7040159 := bstep (se 1 (by rfl) ⟨5280119, by rfl⟩ : syracuseStep 7040159 = 10560239) B10560239
theorem B4693439 : Blo 2197435 4693439 := bstep (se 1 (by rfl) ⟨3520079, by rfl⟩ : syracuseStep 4693439 = 7040159) B7040159
theorem B3128959 : Blo 2197435 3128959 := bstep (se 1 (by rfl) ⟨2346719, by rfl⟩ : syracuseStep 3128959 = 4693439) B4693439
theorem B16687781 : Blo 2197435 16687781 := bstep (se 4 (by rfl) ⟨1564479, by rfl⟩ : syracuseStep 16687781 = 3128959) B3128959
theorem B11125187 : Blo 2197435 11125187 := bstep (se 1 (by rfl) ⟨8343890, by rfl⟩ : syracuseStep 11125187 = 16687781) B16687781
theorem B7416791 : Blo 2197435 7416791 := bstep (se 1 (by rfl) ⟨5562593, by rfl⟩ : syracuseStep 7416791 = 11125187) B11125187
theorem B4944527 : Blo 2197435 4944527 := bstep (se 1 (by rfl) ⟨3708395, by rfl⟩ : syracuseStep 4944527 = 7416791) B7416791
theorem B3296351 : Blo 2197435 3296351 := bstep (se 1 (by rfl) ⟨2472263, by rfl⟩ : syracuseStep 3296351 = 4944527) B4944527
theorem B2197567 : Blo 2197435 2197567 := bstep (se 1 (by rfl) ⟨1648175, by rfl⟩ : syracuseStep 2197567 = 3296351) B3296351
theorem B3296357 : Blo 2197435 3296357 := bbase (se 4 (by rfl) ⟨309033, by rfl⟩ : syracuseStep 3296357 = 618067) (by norm_num)
theorem B2197571 : Blo 2197435 2197571 := bstep (se 1 (by rfl) ⟨1648178, by rfl⟩ : syracuseStep 2197571 = 3296357) B3296357
theorem B3520093 : Blo 2197435 3520093 := bbase (se 3 (by rfl) ⟨660017, by rfl⟩ : syracuseStep 3520093 = 1320035) (by norm_num)
theorem B4693457 : Blo 2197435 4693457 := bstep (se 2 (by rfl) ⟨1760046, by rfl⟩ : syracuseStep 4693457 = 3520093) B3520093
theorem B3128971 : Blo 2197435 3128971 := bstep (se 1 (by rfl) ⟨2346728, by rfl⟩ : syracuseStep 3128971 = 4693457) B4693457
theorem B4171961 : Blo 2197435 4171961 := bstep (se 2 (by rfl) ⟨1564485, by rfl⟩ : syracuseStep 4171961 = 3128971) B3128971
theorem B2781307 : Blo 2197435 2781307 := bstep (se 1 (by rfl) ⟨2085980, by rfl⟩ : syracuseStep 2781307 = 4171961) B4171961
theorem B3708409 : Blo 2197435 3708409 := bstep (se 2 (by rfl) ⟨1390653, by rfl⟩ : syracuseStep 3708409 = 2781307) B2781307
theorem B4944545 : Blo 2197435 4944545 := bstep (se 2 (by rfl) ⟨1854204, by rfl⟩ : syracuseStep 4944545 = 3708409) B3708409
theorem B3296363 : Blo 2197435 3296363 := bstep (se 1 (by rfl) ⟨2472272, by rfl⟩ : syracuseStep 3296363 = 4944545) B4944545
theorem B2197575 : Blo 2197435 2197575 := bstep (se 1 (by rfl) ⟨1648181, by rfl⟩ : syracuseStep 2197575 = 3296363) B3296363
theorem B2472277 : Blo 2197435 2472277 := bbase (se 10 (by rfl) ⟨3621, by rfl⟩ : syracuseStep 2472277 = 7243) (by norm_num)
theorem B3296369 : Blo 2197435 3296369 := bstep (se 2 (by rfl) ⟨1236138, by rfl⟩ : syracuseStep 3296369 = 2472277) B2472277
theorem B2197579 : Blo 2197435 2197579 := bstep (se 1 (by rfl) ⟨1648184, by rfl⟩ : syracuseStep 2197579 = 3296369) B3296369
theorem B2781317 : Blo 2197435 2781317 := bbase (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) (by norm_num)
theorem B7416845 : Blo 2197435 7416845 := bstep (se 3 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 7416845 = 2781317) B2781317
theorem B4944563 : Blo 2197435 4944563 := bstep (se 1 (by rfl) ⟨3708422, by rfl⟩ : syracuseStep 4944563 = 7416845) B7416845
theorem B3296375 : Blo 2197435 3296375 := bstep (se 1 (by rfl) ⟨2472281, by rfl⟩ : syracuseStep 3296375 = 4944563) B4944563
theorem B2197583 : Blo 2197435 2197583 := bstep (se 1 (by rfl) ⟨1648187, by rfl⟩ : syracuseStep 2197583 = 3296375) B3296375
theorem B3296381 : Blo 2197435 3296381 := bbase (se 3 (by rfl) ⟨618071, by rfl⟩ : syracuseStep 3296381 = 1236143) (by norm_num)
theorem B2197587 : Blo 2197435 2197587 := bstep (se 1 (by rfl) ⟨1648190, by rfl⟩ : syracuseStep 2197587 = 3296381) B3296381
theorem B4944581 : Blo 2197435 4944581 := bbase (se 4 (by rfl) ⟨463554, by rfl⟩ : syracuseStep 4944581 = 927109) (by norm_num)
theorem B3296387 : Blo 2197435 3296387 := bstep (se 1 (by rfl) ⟨2472290, by rfl⟩ : syracuseStep 3296387 = 4944581) B4944581
theorem B2197591 : Blo 2197435 2197591 := bstep (se 1 (by rfl) ⟨1648193, by rfl⟩ : syracuseStep 2197591 = 3296387) B3296387
theorem B2819281 : Blo 2197435 2819281 := bbase (se 2 (by rfl) ⟨1057230, by rfl⟩ : syracuseStep 2819281 = 2114461) (by norm_num)
theorem B3759041 : Blo 2197435 3759041 := bstep (se 2 (by rfl) ⟨1409640, by rfl⟩ : syracuseStep 3759041 = 2819281) B2819281
theorem B2506027 : Blo 2197435 2506027 := bstep (se 1 (by rfl) ⟨1879520, by rfl⟩ : syracuseStep 2506027 = 3759041) B3759041
theorem B3341369 : Blo 2197435 3341369 := bstep (se 2 (by rfl) ⟨1253013, by rfl⟩ : syracuseStep 3341369 = 2506027) B2506027
theorem B8910317 : Blo 2197435 8910317 := bstep (se 3 (by rfl) ⟨1670684, by rfl⟩ : syracuseStep 8910317 = 3341369) B3341369
theorem B5940211 : Blo 2197435 5940211 := bstep (se 1 (by rfl) ⟨4455158, by rfl⟩ : syracuseStep 5940211 = 8910317) B8910317
theorem B7920281 : Blo 2197435 7920281 := bstep (se 2 (by rfl) ⟨2970105, by rfl⟩ : syracuseStep 7920281 = 5940211) B5940211
theorem B21120749 : Blo 2197435 21120749 := bstep (se 3 (by rfl) ⟨3960140, by rfl⟩ : syracuseStep 21120749 = 7920281) B7920281
theorem B14080499 : Blo 2197435 14080499 := bstep (se 1 (by rfl) ⟨10560374, by rfl⟩ : syracuseStep 14080499 = 21120749) B21120749
theorem B9386999 : Blo 2197435 9386999 := bstep (se 1 (by rfl) ⟨7040249, by rfl⟩ : syracuseStep 9386999 = 14080499) B14080499
theorem B6257999 : Blo 2197435 6257999 := bstep (se 1 (by rfl) ⟨4693499, by rfl⟩ : syracuseStep 6257999 = 9386999) B9386999
theorem B4171999 : Blo 2197435 4171999 := bstep (se 1 (by rfl) ⟨3128999, by rfl⟩ : syracuseStep 4171999 = 6257999) B6257999
theorem B5562665 : Blo 2197435 5562665 := bstep (se 2 (by rfl) ⟨2085999, by rfl⟩ : syracuseStep 5562665 = 4171999) B4171999
theorem B3708443 : Blo 2197435 3708443 := bstep (se 1 (by rfl) ⟨2781332, by rfl⟩ : syracuseStep 3708443 = 5562665) B5562665
theorem B2472295 : Blo 2197435 2472295 := bstep (se 1 (by rfl) ⟨1854221, by rfl⟩ : syracuseStep 2472295 = 3708443) B3708443
theorem B3296393 : Blo 2197435 3296393 := bstep (se 2 (by rfl) ⟨1236147, by rfl⟩ : syracuseStep 3296393 = 2472295) B2472295
theorem B2197595 : Blo 2197435 2197595 := bstep (se 1 (by rfl) ⟨1648196, by rfl⟩ : syracuseStep 2197595 = 3296393) B3296393
theorem B11125349 : Blo 2197435 11125349 := bbase (se 4 (by rfl) ⟨1043001, by rfl⟩ : syracuseStep 11125349 = 2086003) (by norm_num)
theorem B7416899 : Blo 2197435 7416899 := bstep (se 1 (by rfl) ⟨5562674, by rfl⟩ : syracuseStep 7416899 = 11125349) B11125349
theorem B4944599 : Blo 2197435 4944599 := bstep (se 1 (by rfl) ⟨3708449, by rfl⟩ : syracuseStep 4944599 = 7416899) B7416899
theorem B3296399 : Blo 2197435 3296399 := bstep (se 1 (by rfl) ⟨2472299, by rfl⟩ : syracuseStep 3296399 = 4944599) B4944599
theorem B2197599 : Blo 2197435 2197599 := bstep (se 1 (by rfl) ⟨1648199, by rfl⟩ : syracuseStep 2197599 = 3296399) B3296399
theorem B3296405 : Blo 2197435 3296405 := bbase (se 6 (by rfl) ⟨77259, by rfl⟩ : syracuseStep 3296405 = 154519) (by norm_num)
theorem B2197603 : Blo 2197435 2197603 := bstep (se 1 (by rfl) ⟨1648202, by rfl⟩ : syracuseStep 2197603 = 3296405) B3296405
theorem B26731093 : Blo 2197435 26731093 := bbase (se 8 (by rfl) ⟨156627, by rfl⟩ : syracuseStep 26731093 = 313255) (by norm_num)
theorem B35641457 : Blo 2197435 35641457 := bstep (se 2 (by rfl) ⟨13365546, by rfl⟩ : syracuseStep 35641457 = 26731093) B26731093
theorem B23760971 : Blo 2197435 23760971 := bstep (se 1 (by rfl) ⟨17820728, by rfl⟩ : syracuseStep 23760971 = 35641457) B35641457
theorem B15840647 : Blo 2197435 15840647 := bstep (se 1 (by rfl) ⟨11880485, by rfl⟩ : syracuseStep 15840647 = 23760971) B23760971
theorem B10560431 : Blo 2197435 10560431 := bstep (se 1 (by rfl) ⟨7920323, by rfl⟩ : syracuseStep 10560431 = 15840647) B15840647
theorem B7040287 : Blo 2197435 7040287 := bstep (se 1 (by rfl) ⟨5280215, by rfl⟩ : syracuseStep 7040287 = 10560431) B10560431
theorem B9387049 : Blo 2197435 9387049 := bstep (se 2 (by rfl) ⟨3520143, by rfl⟩ : syracuseStep 9387049 = 7040287) B7040287
theorem B12516065 : Blo 2197435 12516065 := bstep (se 2 (by rfl) ⟨4693524, by rfl⟩ : syracuseStep 12516065 = 9387049) B9387049
theorem B8344043 : Blo 2197435 8344043 := bstep (se 1 (by rfl) ⟨6258032, by rfl⟩ : syracuseStep 8344043 = 12516065) B12516065
theorem B5562695 : Blo 2197435 5562695 := bstep (se 1 (by rfl) ⟨4172021, by rfl⟩ : syracuseStep 5562695 = 8344043) B8344043
theorem B3708463 : Blo 2197435 3708463 := bstep (se 1 (by rfl) ⟨2781347, by rfl⟩ : syracuseStep 3708463 = 5562695) B5562695
theorem B4944617 : Blo 2197435 4944617 := bstep (se 2 (by rfl) ⟨1854231, by rfl⟩ : syracuseStep 4944617 = 3708463) B3708463
theorem B3296411 : Blo 2197435 3296411 := bstep (se 1 (by rfl) ⟨2472308, by rfl⟩ : syracuseStep 3296411 = 4944617) B4944617
theorem B2197607 : Blo 2197435 2197607 := bstep (se 1 (by rfl) ⟨1648205, by rfl⟩ : syracuseStep 2197607 = 3296411) B3296411
theorem B2472313 : Blo 2197435 2472313 := bbase (se 2 (by rfl) ⟨927117, by rfl⟩ : syracuseStep 2472313 = 1854235) (by norm_num)
theorem B3296417 : Blo 2197435 3296417 := bstep (se 2 (by rfl) ⟨1236156, by rfl⟩ : syracuseStep 3296417 = 2472313) B2472313
theorem B2197611 : Blo 2197435 2197611 := bstep (se 1 (by rfl) ⟨1648208, by rfl⟩ : syracuseStep 2197611 = 3296417) B3296417
theorem B10560469 : Blo 2197435 10560469 := bbase (se 7 (by rfl) ⟨123755, by rfl⟩ : syracuseStep 10560469 = 247511) (by norm_num)
theorem B14080625 : Blo 2197435 14080625 := bstep (se 2 (by rfl) ⟨5280234, by rfl⟩ : syracuseStep 14080625 = 10560469) B10560469
theorem B9387083 : Blo 2197435 9387083 := bstep (se 1 (by rfl) ⟨7040312, by rfl⟩ : syracuseStep 9387083 = 14080625) B14080625
theorem B6258055 : Blo 2197435 6258055 := bstep (se 1 (by rfl) ⟨4693541, by rfl⟩ : syracuseStep 6258055 = 9387083) B9387083
theorem B8344073 : Blo 2197435 8344073 := bstep (se 2 (by rfl) ⟨3129027, by rfl⟩ : syracuseStep 8344073 = 6258055) B6258055
theorem B5562715 : Blo 2197435 5562715 := bstep (se 1 (by rfl) ⟨4172036, by rfl⟩ : syracuseStep 5562715 = 8344073) B8344073
theorem B7416953 : Blo 2197435 7416953 := bstep (se 2 (by rfl) ⟨2781357, by rfl⟩ : syracuseStep 7416953 = 5562715) B5562715
theorem B4944635 : Blo 2197435 4944635 := bstep (se 1 (by rfl) ⟨3708476, by rfl⟩ : syracuseStep 4944635 = 7416953) B7416953
theorem B3296423 : Blo 2197435 3296423 := bstep (se 1 (by rfl) ⟨2472317, by rfl⟩ : syracuseStep 3296423 = 4944635) B4944635
theorem B2197615 : Blo 2197435 2197615 := bstep (se 1 (by rfl) ⟨1648211, by rfl⟩ : syracuseStep 2197615 = 3296423) B3296423
theorem B3296429 : Blo 2197435 3296429 := bbase (se 3 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 3296429 = 1236161) (by norm_num)
theorem B2197619 : Blo 2197435 2197619 := bstep (se 1 (by rfl) ⟨1648214, by rfl⟩ : syracuseStep 2197619 = 3296429) B3296429
theorem B4944653 : Blo 2197435 4944653 := bbase (se 3 (by rfl) ⟨927122, by rfl⟩ : syracuseStep 4944653 = 1854245) (by norm_num)
theorem B3296435 : Blo 2197435 3296435 := bstep (se 1 (by rfl) ⟨2472326, by rfl⟩ : syracuseStep 3296435 = 4944653) B4944653
theorem B2197623 : Blo 2197435 2197623 := bstep (se 1 (by rfl) ⟨1648217, by rfl⟩ : syracuseStep 2197623 = 3296435) B3296435
theorem B2781373 : Blo 2197435 2781373 := bbase (se 3 (by rfl) ⟨521507, by rfl⟩ : syracuseStep 2781373 = 1043015) (by norm_num)
theorem B3708497 : Blo 2197435 3708497 := bstep (se 2 (by rfl) ⟨1390686, by rfl⟩ : syracuseStep 3708497 = 2781373) B2781373
theorem B2472331 : Blo 2197435 2472331 := bstep (se 1 (by rfl) ⟨1854248, by rfl⟩ : syracuseStep 2472331 = 3708497) B3708497
theorem B3296441 : Blo 2197435 3296441 := bstep (se 2 (by rfl) ⟨1236165, by rfl⟩ : syracuseStep 3296441 = 2472331) B2472331
theorem B2197627 : Blo 2197435 2197627 := bstep (se 1 (by rfl) ⟨1648220, by rfl⟩ : syracuseStep 2197627 = 3296441) B3296441
theorem B4822525 : Blo 2197435 4822525 := bbase (se 3 (by rfl) ⟨904223, by rfl⟩ : syracuseStep 4822525 = 1808447) (by norm_num)
theorem B6430033 : Blo 2197435 6430033 := bstep (se 2 (by rfl) ⟨2411262, by rfl⟩ : syracuseStep 6430033 = 4822525) B4822525
theorem B8573377 : Blo 2197435 8573377 := bstep (se 2 (by rfl) ⟨3215016, by rfl⟩ : syracuseStep 8573377 = 6430033) B6430033
theorem B11431169 : Blo 2197435 11431169 := bstep (se 2 (by rfl) ⟨4286688, by rfl⟩ : syracuseStep 11431169 = 8573377) B8573377
theorem B7620779 : Blo 2197435 7620779 := bstep (se 1 (by rfl) ⟨5715584, by rfl⟩ : syracuseStep 7620779 = 11431169) B11431169
theorem B5080519 : Blo 2197435 5080519 := bstep (se 1 (by rfl) ⟨3810389, by rfl⟩ : syracuseStep 5080519 = 7620779) B7620779
theorem B6774025 : Blo 2197435 6774025 := bstep (se 2 (by rfl) ⟨2540259, by rfl⟩ : syracuseStep 6774025 = 5080519) B5080519
theorem B9032033 : Blo 2197435 9032033 := bstep (se 2 (by rfl) ⟨3387012, by rfl⟩ : syracuseStep 9032033 = 6774025) B6774025
theorem B24085421 : Blo 2197435 24085421 := bstep (se 3 (by rfl) ⟨4516016, by rfl⟩ : syracuseStep 24085421 = 9032033) B9032033
theorem B16056947 : Blo 2197435 16056947 := bstep (se 1 (by rfl) ⟨12042710, by rfl⟩ : syracuseStep 16056947 = 24085421) B24085421
theorem B10704631 : Blo 2197435 10704631 := bstep (se 1 (by rfl) ⟨8028473, by rfl⟩ : syracuseStep 10704631 = 16056947) B16056947
theorem B14272841 : Blo 2197435 14272841 := bstep (se 2 (by rfl) ⟨5352315, by rfl⟩ : syracuseStep 14272841 = 10704631) B10704631
theorem B9515227 : Blo 2197435 9515227 := bstep (se 1 (by rfl) ⟨7136420, by rfl⟩ : syracuseStep 9515227 = 14272841) B14272841
theorem B12686969 : Blo 2197435 12686969 := bstep (se 2 (by rfl) ⟨4757613, by rfl⟩ : syracuseStep 12686969 = 9515227) B9515227
theorem B8457979 : Blo 2197435 8457979 := bstep (se 1 (by rfl) ⟨6343484, by rfl⟩ : syracuseStep 8457979 = 12686969) B12686969
theorem B11277305 : Blo 2197435 11277305 := bstep (se 2 (by rfl) ⟨4228989, by rfl⟩ : syracuseStep 11277305 = 8457979) B8457979
theorem B7518203 : Blo 2197435 7518203 := bstep (se 1 (by rfl) ⟨5638652, by rfl⟩ : syracuseStep 7518203 = 11277305) B11277305
theorem B5012135 : Blo 2197435 5012135 := bstep (se 1 (by rfl) ⟨3759101, by rfl⟩ : syracuseStep 5012135 = 7518203) B7518203
theorem B3341423 : Blo 2197435 3341423 := bstep (se 1 (by rfl) ⟨2506067, by rfl⟩ : syracuseStep 3341423 = 5012135) B5012135
theorem B8910461 : Blo 2197435 8910461 := bstep (se 3 (by rfl) ⟨1670711, by rfl⟩ : syracuseStep 8910461 = 3341423) B3341423
theorem B5940307 : Blo 2197435 5940307 := bstep (se 1 (by rfl) ⟨4455230, by rfl⟩ : syracuseStep 5940307 = 8910461) B8910461
theorem B7920409 : Blo 2197435 7920409 := bstep (se 2 (by rfl) ⟨2970153, by rfl⟩ : syracuseStep 7920409 = 5940307) B5940307
theorem B10560545 : Blo 2197435 10560545 := bstep (se 2 (by rfl) ⟨3960204, by rfl⟩ : syracuseStep 10560545 = 7920409) B7920409
theorem B7040363 : Blo 2197435 7040363 := bstep (se 1 (by rfl) ⟨5280272, by rfl⟩ : syracuseStep 7040363 = 10560545) B10560545
theorem B18774301 : Blo 2197435 18774301 := bstep (se 3 (by rfl) ⟨3520181, by rfl⟩ : syracuseStep 18774301 = 7040363) B7040363
theorem B25032401 : Blo 2197435 25032401 := bstep (se 2 (by rfl) ⟨9387150, by rfl⟩ : syracuseStep 25032401 = 18774301) B18774301
theorem B16688267 : Blo 2197435 16688267 := bstep (se 1 (by rfl) ⟨12516200, by rfl⟩ : syracuseStep 16688267 = 25032401) B25032401
theorem B11125511 : Blo 2197435 11125511 := bstep (se 1 (by rfl) ⟨8344133, by rfl⟩ : syracuseStep 11125511 = 16688267) B16688267
theorem B7417007 : Blo 2197435 7417007 := bstep (se 1 (by rfl) ⟨5562755, by rfl⟩ : syracuseStep 7417007 = 11125511) B11125511
theorem B4944671 : Blo 2197435 4944671 := bstep (se 1 (by rfl) ⟨3708503, by rfl⟩ : syracuseStep 4944671 = 7417007) B7417007
theorem B3296447 : Blo 2197435 3296447 := bstep (se 1 (by rfl) ⟨2472335, by rfl⟩ : syracuseStep 3296447 = 4944671) B4944671
theorem B2197631 : Blo 2197435 2197631 := bstep (se 1 (by rfl) ⟨1648223, by rfl⟩ : syracuseStep 2197631 = 3296447) B3296447
theorem B3296453 : Blo 2197435 3296453 := bbase (se 4 (by rfl) ⟨309042, by rfl⟩ : syracuseStep 3296453 = 618085) (by norm_num)
theorem B2197635 : Blo 2197435 2197635 := bstep (se 1 (by rfl) ⟨1648226, by rfl⟩ : syracuseStep 2197635 = 3296453) B3296453
theorem B3708517 : Blo 2197435 3708517 := bbase (se 4 (by rfl) ⟨347673, by rfl⟩ : syracuseStep 3708517 = 695347) (by norm_num)
theorem B4944689 : Blo 2197435 4944689 := bstep (se 2 (by rfl) ⟨1854258, by rfl⟩ : syracuseStep 4944689 = 3708517) B3708517
theorem B3296459 : Blo 2197435 3296459 := bstep (se 1 (by rfl) ⟨2472344, by rfl⟩ : syracuseStep 3296459 = 4944689) B4944689
theorem B2197639 : Blo 2197435 2197639 := bstep (se 1 (by rfl) ⟨1648229, by rfl⟩ : syracuseStep 2197639 = 3296459) B3296459
theorem B2472349 : Blo 2197435 2472349 := bbase (se 3 (by rfl) ⟨463565, by rfl⟩ : syracuseStep 2472349 = 927131) (by norm_num)
theorem B3296465 : Blo 2197435 3296465 := bstep (se 2 (by rfl) ⟨1236174, by rfl⟩ : syracuseStep 3296465 = 2472349) B2472349
theorem B2197643 : Blo 2197435 2197643 := bstep (se 1 (by rfl) ⟨1648232, by rfl⟩ : syracuseStep 2197643 = 3296465) B3296465
theorem B7417061 : Blo 2197435 7417061 := bbase (se 4 (by rfl) ⟨695349, by rfl⟩ : syracuseStep 7417061 = 1390699) (by norm_num)
theorem B4944707 : Blo 2197435 4944707 := bstep (se 1 (by rfl) ⟨3708530, by rfl⟩ : syracuseStep 4944707 = 7417061) B7417061
theorem B3296471 : Blo 2197435 3296471 := bstep (se 1 (by rfl) ⟨2472353, by rfl⟩ : syracuseStep 3296471 = 4944707) B4944707
theorem B2197647 : Blo 2197435 2197647 := bstep (se 1 (by rfl) ⟨1648235, by rfl⟩ : syracuseStep 2197647 = 3296471) B3296471
theorem B3296477 : Blo 2197435 3296477 := bbase (se 3 (by rfl) ⟨618089, by rfl⟩ : syracuseStep 3296477 = 1236179) (by norm_num)
theorem B2197651 : Blo 2197435 2197651 := bstep (se 1 (by rfl) ⟨1648238, by rfl⟩ : syracuseStep 2197651 = 3296477) B3296477
theorem B4944725 : Blo 2197435 4944725 := bbase (se 9 (by rfl) ⟨14486, by rfl⟩ : syracuseStep 4944725 = 28973) (by norm_num)
theorem B3296483 : Blo 2197435 3296483 := bstep (se 1 (by rfl) ⟨2472362, by rfl⟩ : syracuseStep 3296483 = 4944725) B4944725
theorem B2197655 : Blo 2197435 2197655 := bstep (se 1 (by rfl) ⟨1648241, by rfl⟩ : syracuseStep 2197655 = 3296483) B3296483
theorem B6258181 : Blo 2197435 6258181 := bbase (se 4 (by rfl) ⟨586704, by rfl⟩ : syracuseStep 6258181 = 1173409) (by norm_num)
theorem B8344241 : Blo 2197435 8344241 := bstep (se 2 (by rfl) ⟨3129090, by rfl⟩ : syracuseStep 8344241 = 6258181) B6258181
theorem B5562827 : Blo 2197435 5562827 := bstep (se 1 (by rfl) ⟨4172120, by rfl⟩ : syracuseStep 5562827 = 8344241) B8344241
theorem B3708551 : Blo 2197435 3708551 := bstep (se 1 (by rfl) ⟨2781413, by rfl⟩ : syracuseStep 3708551 = 5562827) B5562827
theorem B2472367 : Blo 2197435 2472367 := bstep (se 1 (by rfl) ⟨1854275, by rfl⟩ : syracuseStep 2472367 = 3708551) B3708551
theorem B3296489 : Blo 2197435 3296489 := bstep (se 2 (by rfl) ⟨1236183, by rfl⟩ : syracuseStep 3296489 = 2472367) B2472367
theorem B2197659 : Blo 2197435 2197659 := bstep (se 1 (by rfl) ⟨1648244, by rfl⟩ : syracuseStep 2197659 = 3296489) B3296489
theorem B3568261 : Blo 2197435 3568261 := bbase (se 4 (by rfl) ⟨334524, by rfl⟩ : syracuseStep 3568261 = 669049) (by norm_num)
theorem B4757681 : Blo 2197435 4757681 := bstep (se 2 (by rfl) ⟨1784130, by rfl⟩ : syracuseStep 4757681 = 3568261) B3568261
theorem B12687149 : Blo 2197435 12687149 := bstep (se 3 (by rfl) ⟨2378840, by rfl⟩ : syracuseStep 12687149 = 4757681) B4757681
theorem B33832397 : Blo 2197435 33832397 := bstep (se 3 (by rfl) ⟨6343574, by rfl⟩ : syracuseStep 33832397 = 12687149) B12687149
theorem B22554931 : Blo 2197435 22554931 := bstep (se 1 (by rfl) ⟨16916198, by rfl⟩ : syracuseStep 22554931 = 33832397) B33832397
theorem B30073241 : Blo 2197435 30073241 := bstep (se 2 (by rfl) ⟨11277465, by rfl⟩ : syracuseStep 30073241 = 22554931) B22554931
theorem B80195309 : Blo 2197435 80195309 := bstep (se 3 (by rfl) ⟨15036620, by rfl⟩ : syracuseStep 80195309 = 30073241) B30073241
theorem B53463539 : Blo 2197435 53463539 := bstep (se 1 (by rfl) ⟨40097654, by rfl⟩ : syracuseStep 53463539 = 80195309) B80195309
theorem B35642359 : Blo 2197435 35642359 := bstep (se 1 (by rfl) ⟨26731769, by rfl⟩ : syracuseStep 35642359 = 53463539) B53463539
theorem B47523145 : Blo 2197435 47523145 := bstep (se 2 (by rfl) ⟨17821179, by rfl⟩ : syracuseStep 47523145 = 35642359) B35642359
theorem B63364193 : Blo 2197435 63364193 := bstep (se 2 (by rfl) ⟨23761572, by rfl⟩ : syracuseStep 63364193 = 47523145) B47523145
theorem B42242795 : Blo 2197435 42242795 := bstep (se 1 (by rfl) ⟨31682096, by rfl⟩ : syracuseStep 42242795 = 63364193) B63364193
theorem B28161863 : Blo 2197435 28161863 := bstep (se 1 (by rfl) ⟨21121397, by rfl⟩ : syracuseStep 28161863 = 42242795) B42242795
theorem B18774575 : Blo 2197435 18774575 := bstep (se 1 (by rfl) ⟨14080931, by rfl⟩ : syracuseStep 18774575 = 28161863) B28161863
theorem B12516383 : Blo 2197435 12516383 := bstep (se 1 (by rfl) ⟨9387287, by rfl⟩ : syracuseStep 12516383 = 18774575) B18774575
theorem B8344255 : Blo 2197435 8344255 := bstep (se 1 (by rfl) ⟨6258191, by rfl⟩ : syracuseStep 8344255 = 12516383) B12516383
theorem B11125673 : Blo 2197435 11125673 := bstep (se 2 (by rfl) ⟨4172127, by rfl⟩ : syracuseStep 11125673 = 8344255) B8344255
theorem B7417115 : Blo 2197435 7417115 := bstep (se 1 (by rfl) ⟨5562836, by rfl⟩ : syracuseStep 7417115 = 11125673) B11125673
theorem B4944743 : Blo 2197435 4944743 := bstep (se 1 (by rfl) ⟨3708557, by rfl⟩ : syracuseStep 4944743 = 7417115) B7417115
theorem B3296495 : Blo 2197435 3296495 := bstep (se 1 (by rfl) ⟨2472371, by rfl⟩ : syracuseStep 3296495 = 4944743) B4944743
theorem B2197663 : Blo 2197435 2197663 := bstep (se 1 (by rfl) ⟨1648247, by rfl⟩ : syracuseStep 2197663 = 3296495) B3296495
theorem B3296501 : Blo 2197435 3296501 := bbase (se 5 (by rfl) ⟨154523, by rfl⟩ : syracuseStep 3296501 = 309047) (by norm_num)
theorem B2197667 : Blo 2197435 2197667 := bstep (se 1 (by rfl) ⟨1648250, by rfl⟩ : syracuseStep 2197667 = 3296501) B3296501
theorem B15841109 : Blo 2197435 15841109 := bbase (se 9 (by rfl) ⟨46409, by rfl⟩ : syracuseStep 15841109 = 92819) (by norm_num)
theorem B10560739 : Blo 2197435 10560739 := bstep (se 1 (by rfl) ⟨7920554, by rfl⟩ : syracuseStep 10560739 = 15841109) B15841109
theorem B14080985 : Blo 2197435 14080985 := bstep (se 2 (by rfl) ⟨5280369, by rfl⟩ : syracuseStep 14080985 = 10560739) B10560739
theorem B9387323 : Blo 2197435 9387323 := bstep (se 1 (by rfl) ⟨7040492, by rfl⟩ : syracuseStep 9387323 = 14080985) B14080985
theorem B6258215 : Blo 2197435 6258215 := bstep (se 1 (by rfl) ⟨4693661, by rfl⟩ : syracuseStep 6258215 = 9387323) B9387323
theorem B4172143 : Blo 2197435 4172143 := bstep (se 1 (by rfl) ⟨3129107, by rfl⟩ : syracuseStep 4172143 = 6258215) B6258215
theorem B5562857 : Blo 2197435 5562857 := bstep (se 2 (by rfl) ⟨2086071, by rfl⟩ : syracuseStep 5562857 = 4172143) B4172143
theorem B3708571 : Blo 2197435 3708571 := bstep (se 1 (by rfl) ⟨2781428, by rfl⟩ : syracuseStep 3708571 = 5562857) B5562857
theorem B4944761 : Blo 2197435 4944761 := bstep (se 2 (by rfl) ⟨1854285, by rfl⟩ : syracuseStep 4944761 = 3708571) B3708571
theorem B3296507 : Blo 2197435 3296507 := bstep (se 1 (by rfl) ⟨2472380, by rfl⟩ : syracuseStep 3296507 = 4944761) B4944761
theorem B2197671 : Blo 2197435 2197671 := bstep (se 1 (by rfl) ⟨1648253, by rfl⟩ : syracuseStep 2197671 = 3296507) B3296507
theorem B2472385 : Blo 2197435 2472385 := bbase (se 2 (by rfl) ⟨927144, by rfl⟩ : syracuseStep 2472385 = 1854289) (by norm_num)
theorem B3296513 : Blo 2197435 3296513 := bstep (se 2 (by rfl) ⟨1236192, by rfl⟩ : syracuseStep 3296513 = 2472385) B2472385
theorem B2197675 : Blo 2197435 2197675 := bstep (se 1 (by rfl) ⟨1648256, by rfl⟩ : syracuseStep 2197675 = 3296513) B3296513
theorem B5562877 : Blo 2197435 5562877 := bbase (se 3 (by rfl) ⟨1043039, by rfl⟩ : syracuseStep 5562877 = 2086079) (by norm_num)
theorem B7417169 : Blo 2197435 7417169 := bstep (se 2 (by rfl) ⟨2781438, by rfl⟩ : syracuseStep 7417169 = 5562877) B5562877
theorem B4944779 : Blo 2197435 4944779 := bstep (se 1 (by rfl) ⟨3708584, by rfl⟩ : syracuseStep 4944779 = 7417169) B7417169
theorem B3296519 : Blo 2197435 3296519 := bstep (se 1 (by rfl) ⟨2472389, by rfl⟩ : syracuseStep 3296519 = 4944779) B4944779
theorem B2197679 : Blo 2197435 2197679 := bstep (se 1 (by rfl) ⟨1648259, by rfl⟩ : syracuseStep 2197679 = 3296519) B3296519
theorem B3296525 : Blo 2197435 3296525 := bbase (se 3 (by rfl) ⟨618098, by rfl⟩ : syracuseStep 3296525 = 1236197) (by norm_num)
theorem B2197683 : Blo 2197435 2197683 := bstep (se 1 (by rfl) ⟨1648262, by rfl⟩ : syracuseStep 2197683 = 3296525) B3296525
theorem B4944797 : Blo 2197435 4944797 := bbase (se 3 (by rfl) ⟨927149, by rfl⟩ : syracuseStep 4944797 = 1854299) (by norm_num)
theorem B3296531 : Blo 2197435 3296531 := bstep (se 1 (by rfl) ⟨2472398, by rfl⟩ : syracuseStep 3296531 = 4944797) B4944797
theorem B2197687 : Blo 2197435 2197687 := bstep (se 1 (by rfl) ⟨1648265, by rfl⟩ : syracuseStep 2197687 = 3296531) B3296531
theorem B3708605 : Blo 2197435 3708605 := bbase (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) (by norm_num)
theorem B2472403 : Blo 2197435 2472403 := bstep (se 1 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 2472403 = 3708605) B3708605
theorem B3296537 : Blo 2197435 3296537 := bstep (se 2 (by rfl) ⟨1236201, by rfl⟩ : syracuseStep 3296537 = 2472403) B2472403
theorem B2197691 : Blo 2197435 2197691 := bstep (se 1 (by rfl) ⟨1648268, by rfl⟩ : syracuseStep 2197691 = 3296537) B3296537
theorem B12516565 : Blo 2197435 12516565 := bbase (se 7 (by rfl) ⟨146678, by rfl⟩ : syracuseStep 12516565 = 293357) (by norm_num)
theorem B16688753 : Blo 2197435 16688753 := bstep (se 2 (by rfl) ⟨6258282, by rfl⟩ : syracuseStep 16688753 = 12516565) B12516565
theorem B11125835 : Blo 2197435 11125835 := bstep (se 1 (by rfl) ⟨8344376, by rfl⟩ : syracuseStep 11125835 = 16688753) B16688753
theorem B7417223 : Blo 2197435 7417223 := bstep (se 1 (by rfl) ⟨5562917, by rfl⟩ : syracuseStep 7417223 = 11125835) B11125835
theorem B4944815 : Blo 2197435 4944815 := bstep (se 1 (by rfl) ⟨3708611, by rfl⟩ : syracuseStep 4944815 = 7417223) B7417223
theorem B3296543 : Blo 2197435 3296543 := bstep (se 1 (by rfl) ⟨2472407, by rfl⟩ : syracuseStep 3296543 = 4944815) B4944815
theorem B2197695 : Blo 2197435 2197695 := bstep (se 1 (by rfl) ⟨1648271, by rfl⟩ : syracuseStep 2197695 = 3296543) B3296543
theorem B3296549 : Blo 2197435 3296549 := bbase (se 4 (by rfl) ⟨309051, by rfl⟩ : syracuseStep 3296549 = 618103) (by norm_num)
theorem B2197699 : Blo 2197435 2197699 := bstep (se 1 (by rfl) ⟨1648274, by rfl⟩ : syracuseStep 2197699 = 3296549) B3296549
theorem B2781469 : Blo 2197435 2781469 := bbase (se 3 (by rfl) ⟨521525, by rfl⟩ : syracuseStep 2781469 = 1043051) (by norm_num)
theorem B3708625 : Blo 2197435 3708625 := bstep (se 2 (by rfl) ⟨1390734, by rfl⟩ : syracuseStep 3708625 = 2781469) B2781469
theorem B4944833 : Blo 2197435 4944833 := bstep (se 2 (by rfl) ⟨1854312, by rfl⟩ : syracuseStep 4944833 = 3708625) B3708625
theorem B3296555 : Blo 2197435 3296555 := bstep (se 1 (by rfl) ⟨2472416, by rfl⟩ : syracuseStep 3296555 = 4944833) B4944833
theorem B2197703 : Blo 2197435 2197703 := bstep (se 1 (by rfl) ⟨1648277, by rfl⟩ : syracuseStep 2197703 = 3296555) B3296555
theorem B2472421 : Blo 2197435 2472421 := bbase (se 4 (by rfl) ⟨231789, by rfl⟩ : syracuseStep 2472421 = 463579) (by norm_num)
theorem B3296561 : Blo 2197435 3296561 := bstep (se 2 (by rfl) ⟨1236210, by rfl⟩ : syracuseStep 3296561 = 2472421) B2472421
theorem B2197707 : Blo 2197435 2197707 := bstep (se 1 (by rfl) ⟨1648280, by rfl⟩ : syracuseStep 2197707 = 3296561) B3296561
theorem B2640233 : Blo 2197435 2640233 := bbase (se 2 (by rfl) ⟨990087, by rfl⟩ : syracuseStep 2640233 = 1980175) (by norm_num)
theorem B7040621 : Blo 2197435 7040621 := bstep (se 3 (by rfl) ⟨1320116, by rfl⟩ : syracuseStep 7040621 = 2640233) B2640233
theorem B4693747 : Blo 2197435 4693747 := bstep (se 1 (by rfl) ⟨3520310, by rfl⟩ : syracuseStep 4693747 = 7040621) B7040621
theorem B6258329 : Blo 2197435 6258329 := bstep (se 2 (by rfl) ⟨2346873, by rfl⟩ : syracuseStep 6258329 = 4693747) B4693747
theorem B4172219 : Blo 2197435 4172219 := bstep (se 1 (by rfl) ⟨3129164, by rfl⟩ : syracuseStep 4172219 = 6258329) B6258329
theorem B2781479 : Blo 2197435 2781479 := bstep (se 1 (by rfl) ⟨2086109, by rfl⟩ : syracuseStep 2781479 = 4172219) B4172219
theorem B7417277 : Blo 2197435 7417277 := bstep (se 3 (by rfl) ⟨1390739, by rfl⟩ : syracuseStep 7417277 = 2781479) B2781479
theorem B4944851 : Blo 2197435 4944851 := bstep (se 1 (by rfl) ⟨3708638, by rfl⟩ : syracuseStep 4944851 = 7417277) B7417277
theorem B3296567 : Blo 2197435 3296567 := bstep (se 1 (by rfl) ⟨2472425, by rfl⟩ : syracuseStep 3296567 = 4944851) B4944851
theorem B2197711 : Blo 2197435 2197711 := bstep (se 1 (by rfl) ⟨1648283, by rfl⟩ : syracuseStep 2197711 = 3296567) B3296567
theorem B3296573 : Blo 2197435 3296573 := bbase (se 3 (by rfl) ⟨618107, by rfl⟩ : syracuseStep 3296573 = 1236215) (by norm_num)
theorem B2197715 : Blo 2197435 2197715 := bstep (se 1 (by rfl) ⟨1648286, by rfl⟩ : syracuseStep 2197715 = 3296573) B3296573
theorem B4944869 : Blo 2197435 4944869 := bbase (se 4 (by rfl) ⟨463581, by rfl⟩ : syracuseStep 4944869 = 927163) (by norm_num)
theorem B3296579 : Blo 2197435 3296579 := bstep (se 1 (by rfl) ⟨2472434, by rfl⟩ : syracuseStep 3296579 = 4944869) B4944869
theorem B2197719 : Blo 2197435 2197719 := bstep (se 1 (by rfl) ⟨1648289, by rfl⟩ : syracuseStep 2197719 = 3296579) B3296579
theorem B5562989 : Blo 2197435 5562989 := bbase (se 3 (by rfl) ⟨1043060, by rfl⟩ : syracuseStep 5562989 = 2086121) (by norm_num)
theorem B3708659 : Blo 2197435 3708659 := bstep (se 1 (by rfl) ⟨2781494, by rfl⟩ : syracuseStep 3708659 = 5562989) B5562989
theorem B2472439 : Blo 2197435 2472439 := bstep (se 1 (by rfl) ⟨1854329, by rfl⟩ : syracuseStep 2472439 = 3708659) B3708659
theorem B3296585 : Blo 2197435 3296585 := bstep (se 2 (by rfl) ⟨1236219, by rfl⟩ : syracuseStep 3296585 = 2472439) B2472439
theorem B2197723 : Blo 2197435 2197723 := bstep (se 1 (by rfl) ⟨1648292, by rfl⟩ : syracuseStep 2197723 = 3296585) B3296585
theorem B4693781 : Blo 2197435 4693781 := bbase (se 6 (by rfl) ⟨110010, by rfl⟩ : syracuseStep 4693781 = 220021) (by norm_num)
theorem B3129187 : Blo 2197435 3129187 := bstep (se 1 (by rfl) ⟨2346890, by rfl⟩ : syracuseStep 3129187 = 4693781) B4693781
theorem B4172249 : Blo 2197435 4172249 := bstep (se 2 (by rfl) ⟨1564593, by rfl⟩ : syracuseStep 4172249 = 3129187) B3129187
theorem B11125997 : Blo 2197435 11125997 := bstep (se 3 (by rfl) ⟨2086124, by rfl⟩ : syracuseStep 11125997 = 4172249) B4172249
theorem B7417331 : Blo 2197435 7417331 := bstep (se 1 (by rfl) ⟨5562998, by rfl⟩ : syracuseStep 7417331 = 11125997) B11125997
theorem B4944887 : Blo 2197435 4944887 := bstep (se 1 (by rfl) ⟨3708665, by rfl⟩ : syracuseStep 4944887 = 7417331) B7417331
theorem B3296591 : Blo 2197435 3296591 := bstep (se 1 (by rfl) ⟨2472443, by rfl⟩ : syracuseStep 3296591 = 4944887) B4944887
theorem B2197727 : Blo 2197435 2197727 := bstep (se 1 (by rfl) ⟨1648295, by rfl⟩ : syracuseStep 2197727 = 3296591) B3296591
theorem B3296597 : Blo 2197435 3296597 := bbase (se 11 (by rfl) ⟨2414, by rfl⟩ : syracuseStep 3296597 = 4829) (by norm_num)
theorem B2197731 : Blo 2197435 2197731 := bstep (se 1 (by rfl) ⟨1648298, by rfl⟩ : syracuseStep 2197731 = 3296597) B3296597
theorem B3520349 : Blo 2197435 3520349 := bbase (se 3 (by rfl) ⟨660065, by rfl⟩ : syracuseStep 3520349 = 1320131) (by norm_num)
theorem B2346899 : Blo 2197435 2346899 := bstep (se 1 (by rfl) ⟨1760174, by rfl⟩ : syracuseStep 2346899 = 3520349) B3520349
theorem B6258397 : Blo 2197435 6258397 := bstep (se 3 (by rfl) ⟨1173449, by rfl⟩ : syracuseStep 6258397 = 2346899) B2346899
theorem B8344529 : Blo 2197435 8344529 := bstep (se 2 (by rfl) ⟨3129198, by rfl⟩ : syracuseStep 8344529 = 6258397) B6258397
theorem B5563019 : Blo 2197435 5563019 := bstep (se 1 (by rfl) ⟨4172264, by rfl⟩ : syracuseStep 5563019 = 8344529) B8344529
theorem B3708679 : Blo 2197435 3708679 := bstep (se 1 (by rfl) ⟨2781509, by rfl⟩ : syracuseStep 3708679 = 5563019) B5563019
theorem B4944905 : Blo 2197435 4944905 := bstep (se 2 (by rfl) ⟨1854339, by rfl⟩ : syracuseStep 4944905 = 3708679) B3708679
theorem B3296603 : Blo 2197435 3296603 := bstep (se 1 (by rfl) ⟨2472452, by rfl⟩ : syracuseStep 3296603 = 4944905) B4944905
theorem B2197735 : Blo 2197435 2197735 := bstep (se 1 (by rfl) ⟨1648301, by rfl⟩ : syracuseStep 2197735 = 3296603) B3296603
theorem B2472457 : Blo 2197435 2472457 := bbase (se 2 (by rfl) ⟨927171, by rfl⟩ : syracuseStep 2472457 = 1854343) (by norm_num)
theorem B3296609 : Blo 2197435 3296609 := bstep (se 2 (by rfl) ⟨1236228, by rfl⟩ : syracuseStep 3296609 = 2472457) B2472457
theorem B2197739 : Blo 2197435 2197739 := bstep (se 1 (by rfl) ⟨1648304, by rfl⟩ : syracuseStep 2197739 = 3296609) B3296609
theorem B3759293 : Blo 2197435 3759293 := bbase (se 3 (by rfl) ⟨704867, by rfl⟩ : syracuseStep 3759293 = 1409735) (by norm_num)
theorem B2506195 : Blo 2197435 2506195 := bstep (se 1 (by rfl) ⟨1879646, by rfl⟩ : syracuseStep 2506195 = 3759293) B3759293
theorem B3341593 : Blo 2197435 3341593 := bstep (se 2 (by rfl) ⟨1253097, by rfl⟩ : syracuseStep 3341593 = 2506195) B2506195
theorem B17821829 : Blo 2197435 17821829 := bstep (se 4 (by rfl) ⟨1670796, by rfl⟩ : syracuseStep 17821829 = 3341593) B3341593
theorem B47524877 : Blo 2197435 47524877 := bstep (se 3 (by rfl) ⟨8910914, by rfl⟩ : syracuseStep 47524877 = 17821829) B17821829
theorem B31683251 : Blo 2197435 31683251 := bstep (se 1 (by rfl) ⟨23762438, by rfl⟩ : syracuseStep 31683251 = 47524877) B47524877
theorem B21122167 : Blo 2197435 21122167 := bstep (se 1 (by rfl) ⟨15841625, by rfl⟩ : syracuseStep 21122167 = 31683251) B31683251
theorem B28162889 : Blo 2197435 28162889 := bstep (se 2 (by rfl) ⟨10561083, by rfl⟩ : syracuseStep 28162889 = 21122167) B21122167
theorem B18775259 : Blo 2197435 18775259 := bstep (se 1 (by rfl) ⟨14081444, by rfl⟩ : syracuseStep 18775259 = 28162889) B28162889
theorem B12516839 : Blo 2197435 12516839 := bstep (se 1 (by rfl) ⟨9387629, by rfl⟩ : syracuseStep 12516839 = 18775259) B18775259
theorem B8344559 : Blo 2197435 8344559 := bstep (se 1 (by rfl) ⟨6258419, by rfl⟩ : syracuseStep 8344559 = 12516839) B12516839
theorem B5563039 : Blo 2197435 5563039 := bstep (se 1 (by rfl) ⟨4172279, by rfl⟩ : syracuseStep 5563039 = 8344559) B8344559
theorem B7417385 : Blo 2197435 7417385 := bstep (se 2 (by rfl) ⟨2781519, by rfl⟩ : syracuseStep 7417385 = 5563039) B5563039
theorem B4944923 : Blo 2197435 4944923 := bstep (se 1 (by rfl) ⟨3708692, by rfl⟩ : syracuseStep 4944923 = 7417385) B7417385
theorem B3296615 : Blo 2197435 3296615 := bstep (se 1 (by rfl) ⟨2472461, by rfl⟩ : syracuseStep 3296615 = 4944923) B4944923
theorem B2197743 : Blo 2197435 2197743 := bstep (se 1 (by rfl) ⟨1648307, by rfl⟩ : syracuseStep 2197743 = 3296615) B3296615
theorem B3296621 : Blo 2197435 3296621 := bbase (se 3 (by rfl) ⟨618116, by rfl⟩ : syracuseStep 3296621 = 1236233) (by norm_num)
theorem B2197747 : Blo 2197435 2197747 := bstep (se 1 (by rfl) ⟨1648310, by rfl⟩ : syracuseStep 2197747 = 3296621) B3296621
theorem B4944941 : Blo 2197435 4944941 := bbase (se 3 (by rfl) ⟨927176, by rfl⟩ : syracuseStep 4944941 = 1854353) (by norm_num)
theorem B3296627 : Blo 2197435 3296627 := bstep (se 1 (by rfl) ⟨2472470, by rfl⟩ : syracuseStep 3296627 = 4944941) B4944941
theorem B2197751 : Blo 2197435 2197751 := bstep (se 1 (by rfl) ⟨1648313, by rfl⟩ : syracuseStep 2197751 = 3296627) B3296627
theorem B14081525 : Blo 2197435 14081525 := bbase (se 5 (by rfl) ⟨660071, by rfl⟩ : syracuseStep 14081525 = 1320143) (by norm_num)
theorem B9387683 : Blo 2197435 9387683 := bstep (se 1 (by rfl) ⟨7040762, by rfl⟩ : syracuseStep 9387683 = 14081525) B14081525
theorem B6258455 : Blo 2197435 6258455 := bstep (se 1 (by rfl) ⟨4693841, by rfl⟩ : syracuseStep 6258455 = 9387683) B9387683
theorem B4172303 : Blo 2197435 4172303 := bstep (se 1 (by rfl) ⟨3129227, by rfl⟩ : syracuseStep 4172303 = 6258455) B6258455
theorem B2781535 : Blo 2197435 2781535 := bstep (se 1 (by rfl) ⟨2086151, by rfl⟩ : syracuseStep 2781535 = 4172303) B4172303
theorem B3708713 : Blo 2197435 3708713 := bstep (se 2 (by rfl) ⟨1390767, by rfl⟩ : syracuseStep 3708713 = 2781535) B2781535
theorem B2472475 : Blo 2197435 2472475 := bstep (se 1 (by rfl) ⟨1854356, by rfl⟩ : syracuseStep 2472475 = 3708713) B3708713
theorem B3296633 : Blo 2197435 3296633 := bstep (se 2 (by rfl) ⟨1236237, by rfl⟩ : syracuseStep 3296633 = 2472475) B2472475
theorem B2197755 : Blo 2197435 2197755 := bstep (se 1 (by rfl) ⟨1648316, by rfl⟩ : syracuseStep 2197755 = 3296633) B3296633
theorem B7040773 : Blo 2197435 7040773 := bbase (se 4 (by rfl) ⟨660072, by rfl⟩ : syracuseStep 7040773 = 1320145) (by norm_num)
theorem B37550789 : Blo 2197435 37550789 := bstep (se 4 (by rfl) ⟨3520386, by rfl⟩ : syracuseStep 37550789 = 7040773) B7040773
theorem B25033859 : Blo 2197435 25033859 := bstep (se 1 (by rfl) ⟨18775394, by rfl⟩ : syracuseStep 25033859 = 37550789) B37550789
theorem B16689239 : Blo 2197435 16689239 := bstep (se 1 (by rfl) ⟨12516929, by rfl⟩ : syracuseStep 16689239 = 25033859) B25033859
theorem B11126159 : Blo 2197435 11126159 := bstep (se 1 (by rfl) ⟨8344619, by rfl⟩ : syracuseStep 11126159 = 16689239) B16689239
theorem B7417439 : Blo 2197435 7417439 := bstep (se 1 (by rfl) ⟨5563079, by rfl⟩ : syracuseStep 7417439 = 11126159) B11126159
theorem B4944959 : Blo 2197435 4944959 := bstep (se 1 (by rfl) ⟨3708719, by rfl⟩ : syracuseStep 4944959 = 7417439) B7417439
theorem B3296639 : Blo 2197435 3296639 := bstep (se 1 (by rfl) ⟨2472479, by rfl⟩ : syracuseStep 3296639 = 4944959) B4944959
theorem B2197759 : Blo 2197435 2197759 := bstep (se 1 (by rfl) ⟨1648319, by rfl⟩ : syracuseStep 2197759 = 3296639) B3296639
theorem B3296645 : Blo 2197435 3296645 := bbase (se 4 (by rfl) ⟨309060, by rfl⟩ : syracuseStep 3296645 = 618121) (by norm_num)
theorem B2197763 : Blo 2197435 2197763 := bstep (se 1 (by rfl) ⟨1648322, by rfl⟩ : syracuseStep 2197763 = 3296645) B3296645
theorem B3708733 : Blo 2197435 3708733 := bbase (se 3 (by rfl) ⟨695387, by rfl⟩ : syracuseStep 3708733 = 1390775) (by norm_num)
theorem B4944977 : Blo 2197435 4944977 := bstep (se 2 (by rfl) ⟨1854366, by rfl⟩ : syracuseStep 4944977 = 3708733) B3708733
theorem B3296651 : Blo 2197435 3296651 := bstep (se 1 (by rfl) ⟨2472488, by rfl⟩ : syracuseStep 3296651 = 4944977) B4944977
theorem B2197767 : Blo 2197435 2197767 := bstep (se 1 (by rfl) ⟨1648325, by rfl⟩ : syracuseStep 2197767 = 3296651) B3296651
theorem B2472493 : Blo 2197435 2472493 := bbase (se 3 (by rfl) ⟨463592, by rfl⟩ : syracuseStep 2472493 = 927185) (by norm_num)
theorem B3296657 : Blo 2197435 3296657 := bstep (se 2 (by rfl) ⟨1236246, by rfl⟩ : syracuseStep 3296657 = 2472493) B2472493
theorem B2197771 : Blo 2197435 2197771 := bstep (se 1 (by rfl) ⟨1648328, by rfl⟩ : syracuseStep 2197771 = 3296657) B3296657
theorem B7417493 : Blo 2197435 7417493 := bbase (se 6 (by rfl) ⟨173847, by rfl⟩ : syracuseStep 7417493 = 347695) (by norm_num)
theorem B4944995 : Blo 2197435 4944995 := bstep (se 1 (by rfl) ⟨3708746, by rfl⟩ : syracuseStep 4944995 = 7417493) B7417493
theorem B3296663 : Blo 2197435 3296663 := bstep (se 1 (by rfl) ⟨2472497, by rfl⟩ : syracuseStep 3296663 = 4944995) B4944995
theorem B2197775 : Blo 2197435 2197775 := bstep (se 1 (by rfl) ⟨1648331, by rfl⟩ : syracuseStep 2197775 = 3296663) B3296663
theorem B3296669 : Blo 2197435 3296669 := bbase (se 3 (by rfl) ⟨618125, by rfl⟩ : syracuseStep 3296669 = 1236251) (by norm_num)
theorem B2197779 : Blo 2197435 2197779 := bstep (se 1 (by rfl) ⟨1648334, by rfl⟩ : syracuseStep 2197779 = 3296669) B3296669
theorem B4945013 : Blo 2197435 4945013 := bbase (se 5 (by rfl) ⟨231797, by rfl⟩ : syracuseStep 4945013 = 463595) (by norm_num)
theorem B3296675 : Blo 2197435 3296675 := bstep (se 1 (by rfl) ⟨2472506, by rfl⟩ : syracuseStep 3296675 = 4945013) B4945013
theorem B2197783 : Blo 2197435 2197783 := bstep (se 1 (by rfl) ⟨1648337, by rfl⟩ : syracuseStep 2197783 = 3296675) B3296675
theorem B18775637 : Blo 2197435 18775637 := bbase (se 8 (by rfl) ⟨110013, by rfl⟩ : syracuseStep 18775637 = 220027) (by norm_num)
theorem B12517091 : Blo 2197435 12517091 := bstep (se 1 (by rfl) ⟨9387818, by rfl⟩ : syracuseStep 12517091 = 18775637) B18775637
theorem B8344727 : Blo 2197435 8344727 := bstep (se 1 (by rfl) ⟨6258545, by rfl⟩ : syracuseStep 8344727 = 12517091) B12517091
theorem B5563151 : Blo 2197435 5563151 := bstep (se 1 (by rfl) ⟨4172363, by rfl⟩ : syracuseStep 5563151 = 8344727) B8344727
theorem B3708767 : Blo 2197435 3708767 := bstep (se 1 (by rfl) ⟨2781575, by rfl⟩ : syracuseStep 3708767 = 5563151) B5563151
theorem B2472511 : Blo 2197435 2472511 := bstep (se 1 (by rfl) ⟨1854383, by rfl⟩ : syracuseStep 2472511 = 3708767) B3708767
theorem B3296681 : Blo 2197435 3296681 := bstep (se 2 (by rfl) ⟨1236255, by rfl⟩ : syracuseStep 3296681 = 2472511) B2472511
theorem B2197787 : Blo 2197435 2197787 := bstep (se 1 (by rfl) ⟨1648340, by rfl⟩ : syracuseStep 2197787 = 3296681) B3296681
theorem B8344741 : Blo 2197435 8344741 := bbase (se 4 (by rfl) ⟨782319, by rfl⟩ : syracuseStep 8344741 = 1564639) (by norm_num)
theorem B11126321 : Blo 2197435 11126321 := bstep (se 2 (by rfl) ⟨4172370, by rfl⟩ : syracuseStep 11126321 = 8344741) B8344741
theorem B7417547 : Blo 2197435 7417547 := bstep (se 1 (by rfl) ⟨5563160, by rfl⟩ : syracuseStep 7417547 = 11126321) B11126321
theorem B4945031 : Blo 2197435 4945031 := bstep (se 1 (by rfl) ⟨3708773, by rfl⟩ : syracuseStep 4945031 = 7417547) B7417547
theorem B3296687 : Blo 2197435 3296687 := bstep (se 1 (by rfl) ⟨2472515, by rfl⟩ : syracuseStep 3296687 = 4945031) B4945031
theorem B2197791 : Blo 2197435 2197791 := bstep (se 1 (by rfl) ⟨1648343, by rfl⟩ : syracuseStep 2197791 = 3296687) B3296687
theorem B3296693 : Blo 2197435 3296693 := bbase (se 5 (by rfl) ⟨154532, by rfl⟩ : syracuseStep 3296693 = 309065) (by norm_num)
theorem B2197795 : Blo 2197435 2197795 := bstep (se 1 (by rfl) ⟨1648346, by rfl⟩ : syracuseStep 2197795 = 3296693) B3296693
theorem B5563181 : Blo 2197435 5563181 := bbase (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) (by norm_num)
theorem B3708787 : Blo 2197435 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B4945049 : Blo 2197435 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B3296699 : Blo 2197435 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B2197799 : Blo 2197435 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B2472529 : Blo 2197435 2472529 := bbase (se 2 (by rfl) ⟨927198, by rfl⟩ : syracuseStep 2472529 = 1854397) (by norm_num)
theorem B3296705 : Blo 2197435 3296705 := bstep (se 2 (by rfl) ⟨1236264, by rfl⟩ : syracuseStep 3296705 = 2472529) B2472529
theorem B2197803 : Blo 2197435 2197803 := bstep (se 1 (by rfl) ⟨1648352, by rfl⟩ : syracuseStep 2197803 = 3296705) B3296705
theorem B3129301 : Blo 2197435 3129301 := bbase (se 7 (by rfl) ⟨36671, by rfl⟩ : syracuseStep 3129301 = 73343) (by norm_num)
theorem B4172401 : Blo 2197435 4172401 := bstep (se 2 (by rfl) ⟨1564650, by rfl⟩ : syracuseStep 4172401 = 3129301) B3129301
theorem B5563201 : Blo 2197435 5563201 := bstep (se 2 (by rfl) ⟨2086200, by rfl⟩ : syracuseStep 5563201 = 4172401) B4172401
theorem B7417601 : Blo 2197435 7417601 := bstep (se 2 (by rfl) ⟨2781600, by rfl⟩ : syracuseStep 7417601 = 5563201) B5563201
theorem B4945067 : Blo 2197435 4945067 := bstep (se 1 (by rfl) ⟨3708800, by rfl⟩ : syracuseStep 4945067 = 7417601) B7417601
theorem B3296711 : Blo 2197435 3296711 := bstep (se 1 (by rfl) ⟨2472533, by rfl⟩ : syracuseStep 3296711 = 4945067) B4945067
theorem B2197807 : Blo 2197435 2197807 := bstep (se 1 (by rfl) ⟨1648355, by rfl⟩ : syracuseStep 2197807 = 3296711) B3296711
theorem B3296717 : Blo 2197435 3296717 := bbase (se 3 (by rfl) ⟨618134, by rfl⟩ : syracuseStep 3296717 = 1236269) (by norm_num)
theorem B2197811 : Blo 2197435 2197811 := bstep (se 1 (by rfl) ⟨1648358, by rfl⟩ : syracuseStep 2197811 = 3296717) B3296717
theorem B4945085 : Blo 2197435 4945085 := bbase (se 3 (by rfl) ⟨927203, by rfl⟩ : syracuseStep 4945085 = 1854407) (by norm_num)
theorem B3296723 : Blo 2197435 3296723 := bstep (se 1 (by rfl) ⟨2472542, by rfl⟩ : syracuseStep 3296723 = 4945085) B4945085
theorem B2197815 : Blo 2197435 2197815 := bstep (se 1 (by rfl) ⟨1648361, by rfl⟩ : syracuseStep 2197815 = 3296723) B3296723
theorem B3708821 : Blo 2197435 3708821 := bbase (se 6 (by rfl) ⟨86925, by rfl⟩ : syracuseStep 3708821 = 173851) (by norm_num)
theorem B2472547 : Blo 2197435 2472547 := bstep (se 1 (by rfl) ⟨1854410, by rfl⟩ : syracuseStep 2472547 = 3708821) B3708821
theorem B3296729 : Blo 2197435 3296729 := bstep (se 2 (by rfl) ⟨1236273, by rfl⟩ : syracuseStep 3296729 = 2472547) B2472547
theorem B2197819 : Blo 2197435 2197819 := bstep (se 1 (by rfl) ⟨1648364, by rfl⟩ : syracuseStep 2197819 = 3296729) B3296729
theorem B2411473 : Blo 2197435 2411473 := bbase (se 2 (by rfl) ⟨904302, by rfl⟩ : syracuseStep 2411473 = 1808605) (by norm_num)
theorem B3215297 : Blo 2197435 3215297 := bstep (se 2 (by rfl) ⟨1205736, by rfl⟩ : syracuseStep 3215297 = 2411473) B2411473
theorem B8574125 : Blo 2197435 8574125 := bstep (se 3 (by rfl) ⟨1607648, by rfl⟩ : syracuseStep 8574125 = 3215297) B3215297
theorem B91457333 : Blo 2197435 91457333 := bstep (se 5 (by rfl) ⟨4287062, by rfl⟩ : syracuseStep 91457333 = 8574125) B8574125
theorem B60971555 : Blo 2197435 60971555 := bstep (se 1 (by rfl) ⟨45728666, by rfl⟩ : syracuseStep 60971555 = 91457333) B91457333
theorem B40647703 : Blo 2197435 40647703 := bstep (se 1 (by rfl) ⟨30485777, by rfl⟩ : syracuseStep 40647703 = 60971555) B60971555
theorem B54196937 : Blo 2197435 54196937 := bstep (se 2 (by rfl) ⟨20323851, by rfl⟩ : syracuseStep 54196937 = 40647703) B40647703
theorem B36131291 : Blo 2197435 36131291 := bstep (se 1 (by rfl) ⟨27098468, by rfl⟩ : syracuseStep 36131291 = 54196937) B54196937
theorem B24087527 : Blo 2197435 24087527 := bstep (se 1 (by rfl) ⟨18065645, by rfl⟩ : syracuseStep 24087527 = 36131291) B36131291
theorem B16058351 : Blo 2197435 16058351 := bstep (se 1 (by rfl) ⟨12043763, by rfl⟩ : syracuseStep 16058351 = 24087527) B24087527
theorem B10705567 : Blo 2197435 10705567 := bstep (se 1 (by rfl) ⟨8029175, by rfl⟩ : syracuseStep 10705567 = 16058351) B16058351
theorem B14274089 : Blo 2197435 14274089 := bstep (se 2 (by rfl) ⟨5352783, by rfl⟩ : syracuseStep 14274089 = 10705567) B10705567
theorem B9516059 : Blo 2197435 9516059 := bstep (se 1 (by rfl) ⟨7137044, by rfl⟩ : syracuseStep 9516059 = 14274089) B14274089
theorem B6344039 : Blo 2197435 6344039 := bstep (se 1 (by rfl) ⟨4758029, by rfl⟩ : syracuseStep 6344039 = 9516059) B9516059
theorem B16917437 : Blo 2197435 16917437 := bstep (se 3 (by rfl) ⟨3172019, by rfl⟩ : syracuseStep 16917437 = 6344039) B6344039
theorem B11278291 : Blo 2197435 11278291 := bstep (se 1 (by rfl) ⟨8458718, by rfl⟩ : syracuseStep 11278291 = 16917437) B16917437
theorem B15037721 : Blo 2197435 15037721 := bstep (se 2 (by rfl) ⟨5639145, by rfl⟩ : syracuseStep 15037721 = 11278291) B11278291
theorem B10025147 : Blo 2197435 10025147 := bstep (se 1 (by rfl) ⟨7518860, by rfl⟩ : syracuseStep 10025147 = 15037721) B15037721
theorem B6683431 : Blo 2197435 6683431 := bstep (se 1 (by rfl) ⟨5012573, by rfl⟩ : syracuseStep 6683431 = 10025147) B10025147
theorem B8911241 : Blo 2197435 8911241 := bstep (se 2 (by rfl) ⟨3341715, by rfl⟩ : syracuseStep 8911241 = 6683431) B6683431
theorem B5940827 : Blo 2197435 5940827 := bstep (se 1 (by rfl) ⟨4455620, by rfl⟩ : syracuseStep 5940827 = 8911241) B8911241
theorem B3960551 : Blo 2197435 3960551 := bstep (se 1 (by rfl) ⟨2970413, by rfl⟩ : syracuseStep 3960551 = 5940827) B5940827
theorem B2640367 : Blo 2197435 2640367 := bstep (se 1 (by rfl) ⟨1980275, by rfl⟩ : syracuseStep 2640367 = 3960551) B3960551
theorem B14081957 : Blo 2197435 14081957 := bstep (se 4 (by rfl) ⟨1320183, by rfl⟩ : syracuseStep 14081957 = 2640367) B2640367
theorem B9387971 : Blo 2197435 9387971 := bstep (se 1 (by rfl) ⟨7040978, by rfl⟩ : syracuseStep 9387971 = 14081957) B14081957
theorem B6258647 : Blo 2197435 6258647 := bstep (se 1 (by rfl) ⟨4693985, by rfl⟩ : syracuseStep 6258647 = 9387971) B9387971
theorem B16689725 : Blo 2197435 16689725 := bstep (se 3 (by rfl) ⟨3129323, by rfl⟩ : syracuseStep 16689725 = 6258647) B6258647
theorem B11126483 : Blo 2197435 11126483 := bstep (se 1 (by rfl) ⟨8344862, by rfl⟩ : syracuseStep 11126483 = 16689725) B16689725
theorem B7417655 : Blo 2197435 7417655 := bstep (se 1 (by rfl) ⟨5563241, by rfl⟩ : syracuseStep 7417655 = 11126483) B11126483
theorem B4945103 : Blo 2197435 4945103 := bstep (se 1 (by rfl) ⟨3708827, by rfl⟩ : syracuseStep 4945103 = 7417655) B7417655
theorem B3296735 : Blo 2197435 3296735 := bstep (se 1 (by rfl) ⟨2472551, by rfl⟩ : syracuseStep 3296735 = 4945103) B4945103
theorem B2197823 : Blo 2197435 2197823 := bstep (se 1 (by rfl) ⟨1648367, by rfl⟩ : syracuseStep 2197823 = 3296735) B3296735
theorem B3296741 : Blo 2197435 3296741 := bbase (se 4 (by rfl) ⟨309069, by rfl⟩ : syracuseStep 3296741 = 618139) (by norm_num)
theorem B2197827 : Blo 2197435 2197827 := bstep (se 1 (by rfl) ⟨1648370, by rfl⟩ : syracuseStep 2197827 = 3296741) B3296741
theorem B38583701 : Blo 2197435 38583701 := bbase (se 6 (by rfl) ⟨904305, by rfl⟩ : syracuseStep 38583701 = 1808611) (by norm_num)
theorem B25722467 : Blo 2197435 25722467 := bstep (se 1 (by rfl) ⟨19291850, by rfl⟩ : syracuseStep 25722467 = 38583701) B38583701
theorem B17148311 : Blo 2197435 17148311 := bstep (se 1 (by rfl) ⟨12861233, by rfl⟩ : syracuseStep 17148311 = 25722467) B25722467
theorem B11432207 : Blo 2197435 11432207 := bstep (se 1 (by rfl) ⟨8574155, by rfl⟩ : syracuseStep 11432207 = 17148311) B17148311
theorem B7621471 : Blo 2197435 7621471 := bstep (se 1 (by rfl) ⟨5716103, by rfl⟩ : syracuseStep 7621471 = 11432207) B11432207
theorem B40647845 : Blo 2197435 40647845 := bstep (se 4 (by rfl) ⟨3810735, by rfl⟩ : syracuseStep 40647845 = 7621471) B7621471
theorem B27098563 : Blo 2197435 27098563 := bstep (se 1 (by rfl) ⟨20323922, by rfl⟩ : syracuseStep 27098563 = 40647845) B40647845
theorem B36131417 : Blo 2197435 36131417 := bstep (se 2 (by rfl) ⟨13549281, by rfl⟩ : syracuseStep 36131417 = 27098563) B27098563
theorem B24087611 : Blo 2197435 24087611 := bstep (se 1 (by rfl) ⟨18065708, by rfl⟩ : syracuseStep 24087611 = 36131417) B36131417
theorem B16058407 : Blo 2197435 16058407 := bstep (se 1 (by rfl) ⟨12043805, by rfl⟩ : syracuseStep 16058407 = 24087611) B24087611
theorem B21411209 : Blo 2197435 21411209 := bstep (se 2 (by rfl) ⟨8029203, by rfl⟩ : syracuseStep 21411209 = 16058407) B16058407
theorem B14274139 : Blo 2197435 14274139 := bstep (se 1 (by rfl) ⟨10705604, by rfl⟩ : syracuseStep 14274139 = 21411209) B21411209
theorem B19032185 : Blo 2197435 19032185 := bstep (se 2 (by rfl) ⟨7137069, by rfl⟩ : syracuseStep 19032185 = 14274139) B14274139
theorem B50752493 : Blo 2197435 50752493 := bstep (se 3 (by rfl) ⟨9516092, by rfl⟩ : syracuseStep 50752493 = 19032185) B19032185
theorem B33834995 : Blo 2197435 33834995 := bstep (se 1 (by rfl) ⟨25376246, by rfl⟩ : syracuseStep 33834995 = 50752493) B50752493
theorem B22556663 : Blo 2197435 22556663 := bstep (se 1 (by rfl) ⟨16917497, by rfl⟩ : syracuseStep 22556663 = 33834995) B33834995
theorem B15037775 : Blo 2197435 15037775 := bstep (se 1 (by rfl) ⟨11278331, by rfl⟩ : syracuseStep 15037775 = 22556663) B22556663
theorem B10025183 : Blo 2197435 10025183 := bstep (se 1 (by rfl) ⟨7518887, by rfl⟩ : syracuseStep 10025183 = 15037775) B15037775
theorem B6683455 : Blo 2197435 6683455 := bstep (se 1 (by rfl) ⟨5012591, by rfl⟩ : syracuseStep 6683455 = 10025183) B10025183
theorem B35645093 : Blo 2197435 35645093 := bstep (se 4 (by rfl) ⟨3341727, by rfl⟩ : syracuseStep 35645093 = 6683455) B6683455
theorem B23763395 : Blo 2197435 23763395 := bstep (se 1 (by rfl) ⟨17822546, by rfl⟩ : syracuseStep 23763395 = 35645093) B35645093
theorem B15842263 : Blo 2197435 15842263 := bstep (se 1 (by rfl) ⟨11881697, by rfl⟩ : syracuseStep 15842263 = 23763395) B23763395
theorem B21123017 : Blo 2197435 21123017 := bstep (se 2 (by rfl) ⟨7921131, by rfl⟩ : syracuseStep 21123017 = 15842263) B15842263
theorem B14082011 : Blo 2197435 14082011 := bstep (se 1 (by rfl) ⟨10561508, by rfl⟩ : syracuseStep 14082011 = 21123017) B21123017
theorem B9388007 : Blo 2197435 9388007 := bstep (se 1 (by rfl) ⟨7041005, by rfl⟩ : syracuseStep 9388007 = 14082011) B14082011
theorem B6258671 : Blo 2197435 6258671 := bstep (se 1 (by rfl) ⟨4694003, by rfl⟩ : syracuseStep 6258671 = 9388007) B9388007
theorem B4172447 : Blo 2197435 4172447 := bstep (se 1 (by rfl) ⟨3129335, by rfl⟩ : syracuseStep 4172447 = 6258671) B6258671
theorem B2781631 : Blo 2197435 2781631 := bstep (se 1 (by rfl) ⟨2086223, by rfl⟩ : syracuseStep 2781631 = 4172447) B4172447
theorem B3708841 : Blo 2197435 3708841 := bstep (se 2 (by rfl) ⟨1390815, by rfl⟩ : syracuseStep 3708841 = 2781631) B2781631
theorem B4945121 : Blo 2197435 4945121 := bstep (se 2 (by rfl) ⟨1854420, by rfl⟩ : syracuseStep 4945121 = 3708841) B3708841
theorem B3296747 : Blo 2197435 3296747 := bstep (se 1 (by rfl) ⟨2472560, by rfl⟩ : syracuseStep 3296747 = 4945121) B4945121
theorem B2197831 : Blo 2197435 2197831 := bstep (se 1 (by rfl) ⟨1648373, by rfl⟩ : syracuseStep 2197831 = 3296747) B3296747
theorem B2472565 : Blo 2197435 2472565 := bbase (se 5 (by rfl) ⟨115901, by rfl⟩ : syracuseStep 2472565 = 231803) (by norm_num)
theorem B3296753 : Blo 2197435 3296753 := bstep (se 2 (by rfl) ⟨1236282, by rfl⟩ : syracuseStep 3296753 = 2472565) B2472565
theorem B2197835 : Blo 2197435 2197835 := bstep (se 1 (by rfl) ⟨1648376, by rfl⟩ : syracuseStep 2197835 = 3296753) B3296753
theorem B2781641 : Blo 2197435 2781641 := bbase (se 2 (by rfl) ⟨1043115, by rfl⟩ : syracuseStep 2781641 = 2086231) (by norm_num)
theorem B7417709 : Blo 2197435 7417709 := bstep (se 3 (by rfl) ⟨1390820, by rfl⟩ : syracuseStep 7417709 = 2781641) B2781641
theorem B4945139 : Blo 2197435 4945139 := bstep (se 1 (by rfl) ⟨3708854, by rfl⟩ : syracuseStep 4945139 = 7417709) B7417709
theorem B3296759 : Blo 2197435 3296759 := bstep (se 1 (by rfl) ⟨2472569, by rfl⟩ : syracuseStep 3296759 = 4945139) B4945139
theorem B2197839 : Blo 2197435 2197839 := bstep (se 1 (by rfl) ⟨1648379, by rfl⟩ : syracuseStep 2197839 = 3296759) B3296759
theorem B3296765 : Blo 2197435 3296765 := bbase (se 3 (by rfl) ⟨618143, by rfl⟩ : syracuseStep 3296765 = 1236287) (by norm_num)
theorem B2197843 : Blo 2197435 2197843 := bstep (se 1 (by rfl) ⟨1648382, by rfl⟩ : syracuseStep 2197843 = 3296765) B3296765
theorem B4945157 : Blo 2197435 4945157 := bbase (se 4 (by rfl) ⟨463608, by rfl⟩ : syracuseStep 4945157 = 927217) (by norm_num)
theorem B3296771 : Blo 2197435 3296771 := bstep (se 1 (by rfl) ⟨2472578, by rfl⟩ : syracuseStep 3296771 = 4945157) B4945157
theorem B2197847 : Blo 2197435 2197847 := bstep (se 1 (by rfl) ⟨1648385, by rfl⟩ : syracuseStep 2197847 = 3296771) B3296771
theorem B4172485 : Blo 2197435 4172485 := bbase (se 4 (by rfl) ⟨391170, by rfl⟩ : syracuseStep 4172485 = 782341) (by norm_num)
theorem B5563313 : Blo 2197435 5563313 := bstep (se 2 (by rfl) ⟨2086242, by rfl⟩ : syracuseStep 5563313 = 4172485) B4172485
theorem B3708875 : Blo 2197435 3708875 := bstep (se 1 (by rfl) ⟨2781656, by rfl⟩ : syracuseStep 3708875 = 5563313) B5563313
theorem B2472583 : Blo 2197435 2472583 := bstep (se 1 (by rfl) ⟨1854437, by rfl⟩ : syracuseStep 2472583 = 3708875) B3708875
theorem B3296777 : Blo 2197435 3296777 := bstep (se 2 (by rfl) ⟨1236291, by rfl⟩ : syracuseStep 3296777 = 2472583) B2472583
theorem B2197851 : Blo 2197435 2197851 := bstep (se 1 (by rfl) ⟨1648388, by rfl⟩ : syracuseStep 2197851 = 3296777) B3296777
theorem B11126645 : Blo 2197435 11126645 := bbase (se 5 (by rfl) ⟨521561, by rfl⟩ : syracuseStep 11126645 = 1043123) (by norm_num)
theorem B7417763 : Blo 2197435 7417763 := bstep (se 1 (by rfl) ⟨5563322, by rfl⟩ : syracuseStep 7417763 = 11126645) B11126645
theorem B4945175 : Blo 2197435 4945175 := bstep (se 1 (by rfl) ⟨3708881, by rfl⟩ : syracuseStep 4945175 = 7417763) B7417763
theorem B3296783 : Blo 2197435 3296783 := bstep (se 1 (by rfl) ⟨2472587, by rfl⟩ : syracuseStep 3296783 = 4945175) B4945175
theorem B2197855 : Blo 2197435 2197855 := bstep (se 1 (by rfl) ⟨1648391, by rfl⟩ : syracuseStep 2197855 = 3296783) B3296783
theorem B3296789 : Blo 2197435 3296789 := bbase (se 6 (by rfl) ⟨77268, by rfl⟩ : syracuseStep 3296789 = 154537) (by norm_num)
theorem B2197859 : Blo 2197435 2197859 := bstep (se 1 (by rfl) ⟨1648394, by rfl⟩ : syracuseStep 2197859 = 3296789) B3296789
theorem B7518997 : Blo 2197435 7518997 := bbase (se 6 (by rfl) ⟨176226, by rfl⟩ : syracuseStep 7518997 = 352453) (by norm_num)
theorem B10025329 : Blo 2197435 10025329 := bstep (se 2 (by rfl) ⟨3759498, by rfl⟩ : syracuseStep 10025329 = 7518997) B7518997
theorem B13367105 : Blo 2197435 13367105 := bstep (se 2 (by rfl) ⟨5012664, by rfl⟩ : syracuseStep 13367105 = 10025329) B10025329
theorem B8911403 : Blo 2197435 8911403 := bstep (se 1 (by rfl) ⟨6683552, by rfl⟩ : syracuseStep 8911403 = 13367105) B13367105
theorem B5940935 : Blo 2197435 5940935 := bstep (se 1 (by rfl) ⟨4455701, by rfl⟩ : syracuseStep 5940935 = 8911403) B8911403
theorem B3960623 : Blo 2197435 3960623 := bstep (se 1 (by rfl) ⟨2970467, by rfl⟩ : syracuseStep 3960623 = 5940935) B5940935
theorem B10561661 : Blo 2197435 10561661 := bstep (se 3 (by rfl) ⟨1980311, by rfl⟩ : syracuseStep 10561661 = 3960623) B3960623
theorem B7041107 : Blo 2197435 7041107 := bstep (se 1 (by rfl) ⟨5280830, by rfl⟩ : syracuseStep 7041107 = 10561661) B10561661
theorem B18776285 : Blo 2197435 18776285 := bstep (se 3 (by rfl) ⟨3520553, by rfl⟩ : syracuseStep 18776285 = 7041107) B7041107
theorem B12517523 : Blo 2197435 12517523 := bstep (se 1 (by rfl) ⟨9388142, by rfl⟩ : syracuseStep 12517523 = 18776285) B18776285
theorem B8345015 : Blo 2197435 8345015 := bstep (se 1 (by rfl) ⟨6258761, by rfl⟩ : syracuseStep 8345015 = 12517523) B12517523
theorem B5563343 : Blo 2197435 5563343 := bstep (se 1 (by rfl) ⟨4172507, by rfl⟩ : syracuseStep 5563343 = 8345015) B8345015
theorem B3708895 : Blo 2197435 3708895 := bstep (se 1 (by rfl) ⟨2781671, by rfl⟩ : syracuseStep 3708895 = 5563343) B5563343
theorem B4945193 : Blo 2197435 4945193 := bstep (se 2 (by rfl) ⟨1854447, by rfl⟩ : syracuseStep 4945193 = 3708895) B3708895
theorem B3296795 : Blo 2197435 3296795 := bstep (se 1 (by rfl) ⟨2472596, by rfl⟩ : syracuseStep 3296795 = 4945193) B4945193
theorem B2197863 : Blo 2197435 2197863 := bstep (se 1 (by rfl) ⟨1648397, by rfl⟩ : syracuseStep 2197863 = 3296795) B3296795
theorem B2472601 : Blo 2197435 2472601 := bbase (se 2 (by rfl) ⟨927225, by rfl⟩ : syracuseStep 2472601 = 1854451) (by norm_num)
theorem B3296801 : Blo 2197435 3296801 := bstep (se 2 (by rfl) ⟨1236300, by rfl⟩ : syracuseStep 3296801 = 2472601) B2472601
theorem B2197867 : Blo 2197435 2197867 := bstep (se 1 (by rfl) ⟨1648400, by rfl⟩ : syracuseStep 2197867 = 3296801) B3296801
theorem B8345045 : Blo 2197435 8345045 := bbase (se 7 (by rfl) ⟨97793, by rfl⟩ : syracuseStep 8345045 = 195587) (by norm_num)
theorem B5563363 : Blo 2197435 5563363 := bstep (se 1 (by rfl) ⟨4172522, by rfl⟩ : syracuseStep 5563363 = 8345045) B8345045
theorem B7417817 : Blo 2197435 7417817 := bstep (se 2 (by rfl) ⟨2781681, by rfl⟩ : syracuseStep 7417817 = 5563363) B5563363
theorem B4945211 : Blo 2197435 4945211 := bstep (se 1 (by rfl) ⟨3708908, by rfl⟩ : syracuseStep 4945211 = 7417817) B7417817
theorem B3296807 : Blo 2197435 3296807 := bstep (se 1 (by rfl) ⟨2472605, by rfl⟩ : syracuseStep 3296807 = 4945211) B4945211
theorem B2197871 : Blo 2197435 2197871 := bstep (se 1 (by rfl) ⟨1648403, by rfl⟩ : syracuseStep 2197871 = 3296807) B3296807
theorem B3296813 : Blo 2197435 3296813 := bbase (se 3 (by rfl) ⟨618152, by rfl⟩ : syracuseStep 3296813 = 1236305) (by norm_num)
theorem B2197875 : Blo 2197435 2197875 := bstep (se 1 (by rfl) ⟨1648406, by rfl⟩ : syracuseStep 2197875 = 3296813) B3296813
theorem B4945229 : Blo 2197435 4945229 := bbase (se 3 (by rfl) ⟨927230, by rfl⟩ : syracuseStep 4945229 = 1854461) (by norm_num)
theorem B3296819 : Blo 2197435 3296819 := bstep (se 1 (by rfl) ⟨2472614, by rfl⟩ : syracuseStep 3296819 = 4945229) B4945229
theorem B2197879 : Blo 2197435 2197879 := bstep (se 1 (by rfl) ⟨1648409, by rfl⟩ : syracuseStep 2197879 = 3296819) B3296819
theorem B2781697 : Blo 2197435 2781697 := bbase (se 2 (by rfl) ⟨1043136, by rfl⟩ : syracuseStep 2781697 = 2086273) (by norm_num)
theorem B3708929 : Blo 2197435 3708929 := bstep (se 2 (by rfl) ⟨1390848, by rfl⟩ : syracuseStep 3708929 = 2781697) B2781697
theorem B2472619 : Blo 2197435 2472619 := bstep (se 1 (by rfl) ⟨1854464, by rfl⟩ : syracuseStep 2472619 = 3708929) B3708929
theorem B3296825 : Blo 2197435 3296825 := bstep (se 2 (by rfl) ⟨1236309, by rfl⟩ : syracuseStep 3296825 = 2472619) B2472619
theorem B2197883 : Blo 2197435 2197883 := bstep (se 1 (by rfl) ⟨1648412, by rfl⟩ : syracuseStep 2197883 = 3296825) B3296825
theorem B2347061 : Blo 2197435 2347061 := bbase (se 5 (by rfl) ⟨110018, by rfl⟩ : syracuseStep 2347061 = 220037) (by norm_num)
theorem B25035317 : Blo 2197435 25035317 := bstep (se 5 (by rfl) ⟨1173530, by rfl⟩ : syracuseStep 25035317 = 2347061) B2347061
theorem B16690211 : Blo 2197435 16690211 := bstep (se 1 (by rfl) ⟨12517658, by rfl⟩ : syracuseStep 16690211 = 25035317) B25035317
theorem B11126807 : Blo 2197435 11126807 := bstep (se 1 (by rfl) ⟨8345105, by rfl⟩ : syracuseStep 11126807 = 16690211) B16690211
theorem B7417871 : Blo 2197435 7417871 := bstep (se 1 (by rfl) ⟨5563403, by rfl⟩ : syracuseStep 7417871 = 11126807) B11126807
theorem B4945247 : Blo 2197435 4945247 := bstep (se 1 (by rfl) ⟨3708935, by rfl⟩ : syracuseStep 4945247 = 7417871) B7417871
theorem B3296831 : Blo 2197435 3296831 := bstep (se 1 (by rfl) ⟨2472623, by rfl⟩ : syracuseStep 3296831 = 4945247) B4945247
theorem B2197887 : Blo 2197435 2197887 := bstep (se 1 (by rfl) ⟨1648415, by rfl⟩ : syracuseStep 2197887 = 3296831) B3296831
theorem B3296837 : Blo 2197435 3296837 := bbase (se 4 (by rfl) ⟨309078, by rfl⟩ : syracuseStep 3296837 = 618157) (by norm_num)
theorem B2197891 : Blo 2197435 2197891 := bstep (se 1 (by rfl) ⟨1648418, by rfl⟩ : syracuseStep 2197891 = 3296837) B3296837
theorem B3708949 : Blo 2197435 3708949 := bbase (se 6 (by rfl) ⟨86928, by rfl⟩ : syracuseStep 3708949 = 173857) (by norm_num)
theorem B4945265 : Blo 2197435 4945265 := bstep (se 2 (by rfl) ⟨1854474, by rfl⟩ : syracuseStep 4945265 = 3708949) B3708949
theorem B3296843 : Blo 2197435 3296843 := bstep (se 1 (by rfl) ⟨2472632, by rfl⟩ : syracuseStep 3296843 = 4945265) B4945265
theorem B2197895 : Blo 2197435 2197895 := bstep (se 1 (by rfl) ⟨1648421, by rfl⟩ : syracuseStep 2197895 = 3296843) B3296843
theorem B2472637 : Blo 2197435 2472637 := bbase (se 3 (by rfl) ⟨463619, by rfl⟩ : syracuseStep 2472637 = 927239) (by norm_num)
theorem B3296849 : Blo 2197435 3296849 := bstep (se 2 (by rfl) ⟨1236318, by rfl⟩ : syracuseStep 3296849 = 2472637) B2472637
theorem B2197899 : Blo 2197435 2197899 := bstep (se 1 (by rfl) ⟨1648424, by rfl⟩ : syracuseStep 2197899 = 3296849) B3296849
theorem B7417925 : Blo 2197435 7417925 := bbase (se 4 (by rfl) ⟨695430, by rfl⟩ : syracuseStep 7417925 = 1390861) (by norm_num)
theorem B4945283 : Blo 2197435 4945283 := bstep (se 1 (by rfl) ⟨3708962, by rfl⟩ : syracuseStep 4945283 = 7417925) B7417925
theorem B3296855 : Blo 2197435 3296855 := bstep (se 1 (by rfl) ⟨2472641, by rfl⟩ : syracuseStep 3296855 = 4945283) B4945283
theorem B2197903 : Blo 2197435 2197903 := bstep (se 1 (by rfl) ⟨1648427, by rfl⟩ : syracuseStep 2197903 = 3296855) B3296855
theorem B3296861 : Blo 2197435 3296861 := bbase (se 3 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 3296861 = 1236323) (by norm_num)
theorem B2197907 : Blo 2197435 2197907 := bstep (se 1 (by rfl) ⟨1648430, by rfl⟩ : syracuseStep 2197907 = 3296861) B3296861
theorem B4945301 : Blo 2197435 4945301 := bbase (se 6 (by rfl) ⟨115905, by rfl⟩ : syracuseStep 4945301 = 231811) (by norm_num)
theorem B3296867 : Blo 2197435 3296867 := bstep (se 1 (by rfl) ⟨2472650, by rfl⟩ : syracuseStep 3296867 = 4945301) B4945301
theorem B2197911 : Blo 2197435 2197911 := bstep (se 1 (by rfl) ⟨1648433, by rfl⟩ : syracuseStep 2197911 = 3296867) B3296867
theorem B5500069 : Blo 2197435 5500069 := bbase (se 4 (by rfl) ⟨515631, by rfl⟩ : syracuseStep 5500069 = 1031263) (by norm_num)
theorem B29333701 : Blo 2197435 29333701 := bstep (se 4 (by rfl) ⟨2750034, by rfl⟩ : syracuseStep 29333701 = 5500069) B5500069
theorem B156446405 : Blo 2197435 156446405 := bstep (se 4 (by rfl) ⟨14666850, by rfl⟩ : syracuseStep 156446405 = 29333701) B29333701
theorem B104297603 : Blo 2197435 104297603 := bstep (se 1 (by rfl) ⟨78223202, by rfl⟩ : syracuseStep 104297603 = 156446405) B156446405
theorem B278126941 : Blo 2197435 278126941 := bstep (se 3 (by rfl) ⟨52148801, by rfl⟩ : syracuseStep 278126941 = 104297603) B104297603
theorem B370835921 : Blo 2197435 370835921 := bstep (se 2 (by rfl) ⟨139063470, by rfl⟩ : syracuseStep 370835921 = 278126941) B278126941
theorem B988895789 : Blo 2197435 988895789 := bstep (se 3 (by rfl) ⟨185417960, by rfl⟩ : syracuseStep 988895789 = 370835921) B370835921
theorem B659263859 : Blo 2197435 659263859 := bstep (se 1 (by rfl) ⟨494447894, by rfl⟩ : syracuseStep 659263859 = 988895789) B988895789
theorem B439509239 : Blo 2197435 439509239 := bstep (se 1 (by rfl) ⟨329631929, by rfl⟩ : syracuseStep 439509239 = 659263859) B659263859
theorem B293006159 : Blo 2197435 293006159 := bstep (se 1 (by rfl) ⟨219754619, by rfl⟩ : syracuseStep 293006159 = 439509239) B439509239
theorem B195337439 : Blo 2197435 195337439 := bstep (se 1 (by rfl) ⟨146503079, by rfl⟩ : syracuseStep 195337439 = 293006159) B293006159
theorem B130224959 : Blo 2197435 130224959 := bstep (se 1 (by rfl) ⟨97668719, by rfl⟩ : syracuseStep 130224959 = 195337439) B195337439
theorem B86816639 : Blo 2197435 86816639 := bstep (se 1 (by rfl) ⟨65112479, by rfl⟩ : syracuseStep 86816639 = 130224959) B130224959
theorem B57877759 : Blo 2197435 57877759 := bstep (se 1 (by rfl) ⟨43408319, by rfl⟩ : syracuseStep 57877759 = 86816639) B86816639
theorem B308681381 : Blo 2197435 308681381 := bstep (se 4 (by rfl) ⟨28938879, by rfl⟩ : syracuseStep 308681381 = 57877759) B57877759
theorem B205787587 : Blo 2197435 205787587 := bstep (se 1 (by rfl) ⟨154340690, by rfl⟩ : syracuseStep 205787587 = 308681381) B308681381
theorem B274383449 : Blo 2197435 274383449 := bstep (se 2 (by rfl) ⟨102893793, by rfl⟩ : syracuseStep 274383449 = 205787587) B205787587
theorem B182922299 : Blo 2197435 182922299 := bstep (se 1 (by rfl) ⟨137191724, by rfl⟩ : syracuseStep 182922299 = 274383449) B274383449
theorem B121948199 : Blo 2197435 121948199 := bstep (se 1 (by rfl) ⟨91461149, by rfl⟩ : syracuseStep 121948199 = 182922299) B182922299
theorem B81298799 : Blo 2197435 81298799 := bstep (se 1 (by rfl) ⟨60974099, by rfl⟩ : syracuseStep 81298799 = 121948199) B121948199
theorem B54199199 : Blo 2197435 54199199 := bstep (se 1 (by rfl) ⟨40649399, by rfl⟩ : syracuseStep 54199199 = 81298799) B81298799
theorem B36132799 : Blo 2197435 36132799 := bstep (se 1 (by rfl) ⟨27099599, by rfl⟩ : syracuseStep 36132799 = 54199199) B54199199
theorem B48177065 : Blo 2197435 48177065 := bstep (se 2 (by rfl) ⟨18066399, by rfl⟩ : syracuseStep 48177065 = 36132799) B36132799
theorem B32118043 : Blo 2197435 32118043 := bstep (se 1 (by rfl) ⟨24088532, by rfl⟩ : syracuseStep 32118043 = 48177065) B48177065
theorem B42824057 : Blo 2197435 42824057 := bstep (se 2 (by rfl) ⟨16059021, by rfl⟩ : syracuseStep 42824057 = 32118043) B32118043
theorem B114197485 : Blo 2197435 114197485 := bstep (se 3 (by rfl) ⟨21412028, by rfl⟩ : syracuseStep 114197485 = 42824057) B42824057
theorem B152263313 : Blo 2197435 152263313 := bstep (se 2 (by rfl) ⟨57098742, by rfl⟩ : syracuseStep 152263313 = 114197485) B114197485
theorem B101508875 : Blo 2197435 101508875 := bstep (se 1 (by rfl) ⟨76131656, by rfl⟩ : syracuseStep 101508875 = 152263313) B152263313
theorem B67672583 : Blo 2197435 67672583 := bstep (se 1 (by rfl) ⟨50754437, by rfl⟩ : syracuseStep 67672583 = 101508875) B101508875
theorem B45115055 : Blo 2197435 45115055 := bstep (se 1 (by rfl) ⟨33836291, by rfl⟩ : syracuseStep 45115055 = 67672583) B67672583
theorem B30076703 : Blo 2197435 30076703 := bstep (se 1 (by rfl) ⟨22557527, by rfl⟩ : syracuseStep 30076703 = 45115055) B45115055
theorem B20051135 : Blo 2197435 20051135 := bstep (se 1 (by rfl) ⟨15038351, by rfl⟩ : syracuseStep 20051135 = 30076703) B30076703
theorem B13367423 : Blo 2197435 13367423 := bstep (se 1 (by rfl) ⟨10025567, by rfl⟩ : syracuseStep 13367423 = 20051135) B20051135
theorem B8911615 : Blo 2197435 8911615 := bstep (se 1 (by rfl) ⟨6683711, by rfl⟩ : syracuseStep 8911615 = 13367423) B13367423
theorem B11882153 : Blo 2197435 11882153 := bstep (se 2 (by rfl) ⟨4455807, by rfl⟩ : syracuseStep 11882153 = 8911615) B8911615
theorem B7921435 : Blo 2197435 7921435 := bstep (se 1 (by rfl) ⟨5941076, by rfl⟩ : syracuseStep 7921435 = 11882153) B11882153
theorem B10561913 : Blo 2197435 10561913 := bstep (se 2 (by rfl) ⟨3960717, by rfl⟩ : syracuseStep 10561913 = 7921435) B7921435
theorem B7041275 : Blo 2197435 7041275 := bstep (se 1 (by rfl) ⟨5280956, by rfl⟩ : syracuseStep 7041275 = 10561913) B10561913
theorem B4694183 : Blo 2197435 4694183 := bstep (se 1 (by rfl) ⟨3520637, by rfl⟩ : syracuseStep 4694183 = 7041275) B7041275
theorem B3129455 : Blo 2197435 3129455 := bstep (se 1 (by rfl) ⟨2347091, by rfl⟩ : syracuseStep 3129455 = 4694183) B4694183
theorem B8345213 : Blo 2197435 8345213 := bstep (se 3 (by rfl) ⟨1564727, by rfl⟩ : syracuseStep 8345213 = 3129455) B3129455
theorem B5563475 : Blo 2197435 5563475 := bstep (se 1 (by rfl) ⟨4172606, by rfl⟩ : syracuseStep 5563475 = 8345213) B8345213
theorem B3708983 : Blo 2197435 3708983 := bstep (se 1 (by rfl) ⟨2781737, by rfl⟩ : syracuseStep 3708983 = 5563475) B5563475
theorem B2472655 : Blo 2197435 2472655 := bstep (se 1 (by rfl) ⟨1854491, by rfl⟩ : syracuseStep 2472655 = 3708983) B3708983
theorem B3296873 : Blo 2197435 3296873 := bstep (se 2 (by rfl) ⟨1236327, by rfl⟩ : syracuseStep 3296873 = 2472655) B2472655
theorem B2197915 : Blo 2197435 2197915 := bstep (se 1 (by rfl) ⟨1648436, by rfl⟩ : syracuseStep 2197915 = 3296873) B3296873
theorem B5280965 : Blo 2197435 5280965 := bbase (se 4 (by rfl) ⟨495090, by rfl⟩ : syracuseStep 5280965 = 990181) (by norm_num)
theorem B3520643 : Blo 2197435 3520643 := bstep (se 1 (by rfl) ⟨2640482, by rfl⟩ : syracuseStep 3520643 = 5280965) B5280965
theorem B9388381 : Blo 2197435 9388381 := bstep (se 3 (by rfl) ⟨1760321, by rfl⟩ : syracuseStep 9388381 = 3520643) B3520643
theorem B12517841 : Blo 2197435 12517841 := bstep (se 2 (by rfl) ⟨4694190, by rfl⟩ : syracuseStep 12517841 = 9388381) B9388381
theorem B8345227 : Blo 2197435 8345227 := bstep (se 1 (by rfl) ⟨6258920, by rfl⟩ : syracuseStep 8345227 = 12517841) B12517841
theorem B11126969 : Blo 2197435 11126969 := bstep (se 2 (by rfl) ⟨4172613, by rfl⟩ : syracuseStep 11126969 = 8345227) B8345227
theorem B7417979 : Blo 2197435 7417979 := bstep (se 1 (by rfl) ⟨5563484, by rfl⟩ : syracuseStep 7417979 = 11126969) B11126969
theorem B4945319 : Blo 2197435 4945319 := bstep (se 1 (by rfl) ⟨3708989, by rfl⟩ : syracuseStep 4945319 = 7417979) B7417979
theorem B3296879 : Blo 2197435 3296879 := bstep (se 1 (by rfl) ⟨2472659, by rfl⟩ : syracuseStep 3296879 = 4945319) B4945319
theorem B2197919 : Blo 2197435 2197919 := bstep (se 1 (by rfl) ⟨1648439, by rfl⟩ : syracuseStep 2197919 = 3296879) B3296879
theorem B3296885 : Blo 2197435 3296885 := bbase (se 5 (by rfl) ⟨154541, by rfl⟩ : syracuseStep 3296885 = 309083) (by norm_num)
theorem B2197923 : Blo 2197435 2197923 := bstep (se 1 (by rfl) ⟨1648442, by rfl⟩ : syracuseStep 2197923 = 3296885) B3296885
theorem B4172629 : Blo 2197435 4172629 := bbase (se 9 (by rfl) ⟨12224, by rfl⟩ : syracuseStep 4172629 = 24449) (by norm_num)
theorem B5563505 : Blo 2197435 5563505 := bstep (se 2 (by rfl) ⟨2086314, by rfl⟩ : syracuseStep 5563505 = 4172629) B4172629
theorem B3709003 : Blo 2197435 3709003 := bstep (se 1 (by rfl) ⟨2781752, by rfl⟩ : syracuseStep 3709003 = 5563505) B5563505
theorem B4945337 : Blo 2197435 4945337 := bstep (se 2 (by rfl) ⟨1854501, by rfl⟩ : syracuseStep 4945337 = 3709003) B3709003
theorem B3296891 : Blo 2197435 3296891 := bstep (se 1 (by rfl) ⟨2472668, by rfl⟩ : syracuseStep 3296891 = 4945337) B4945337
theorem B2197927 : Blo 2197435 2197927 := bstep (se 1 (by rfl) ⟨1648445, by rfl⟩ : syracuseStep 2197927 = 3296891) B3296891
theorem B2472673 : Blo 2197435 2472673 := bbase (se 2 (by rfl) ⟨927252, by rfl⟩ : syracuseStep 2472673 = 1854505) (by norm_num)
theorem B3296897 : Blo 2197435 3296897 := bstep (se 2 (by rfl) ⟨1236336, by rfl⟩ : syracuseStep 3296897 = 2472673) B2472673
theorem B2197931 : Blo 2197435 2197931 := bstep (se 1 (by rfl) ⟨1648448, by rfl⟩ : syracuseStep 2197931 = 3296897) B3296897
theorem B5563525 : Blo 2197435 5563525 := bbase (se 4 (by rfl) ⟨521580, by rfl⟩ : syracuseStep 5563525 = 1043161) (by norm_num)
theorem B7418033 : Blo 2197435 7418033 := bstep (se 2 (by rfl) ⟨2781762, by rfl⟩ : syracuseStep 7418033 = 5563525) B5563525
theorem B4945355 : Blo 2197435 4945355 := bstep (se 1 (by rfl) ⟨3709016, by rfl⟩ : syracuseStep 4945355 = 7418033) B7418033
theorem B3296903 : Blo 2197435 3296903 := bstep (se 1 (by rfl) ⟨2472677, by rfl⟩ : syracuseStep 3296903 = 4945355) B4945355
theorem B2197935 : Blo 2197435 2197935 := bstep (se 1 (by rfl) ⟨1648451, by rfl⟩ : syracuseStep 2197935 = 3296903) B3296903
theorem B3296909 : Blo 2197435 3296909 := bbase (se 3 (by rfl) ⟨618170, by rfl⟩ : syracuseStep 3296909 = 1236341) (by norm_num)
theorem B2197939 : Blo 2197435 2197939 := bstep (se 1 (by rfl) ⟨1648454, by rfl⟩ : syracuseStep 2197939 = 3296909) B3296909
theorem B4945373 : Blo 2197435 4945373 := bbase (se 3 (by rfl) ⟨927257, by rfl⟩ : syracuseStep 4945373 = 1854515) (by norm_num)
theorem B3296915 : Blo 2197435 3296915 := bstep (se 1 (by rfl) ⟨2472686, by rfl⟩ : syracuseStep 3296915 = 4945373) B4945373
theorem B2197943 : Blo 2197435 2197943 := bstep (se 1 (by rfl) ⟨1648457, by rfl⟩ : syracuseStep 2197943 = 3296915) B3296915
theorem B3709037 : Blo 2197435 3709037 := bbase (se 3 (by rfl) ⟨695444, by rfl⟩ : syracuseStep 3709037 = 1390889) (by norm_num)
theorem B2472691 : Blo 2197435 2472691 := bstep (se 1 (by rfl) ⟨1854518, by rfl⟩ : syracuseStep 2472691 = 3709037) B3709037
theorem B3296921 : Blo 2197435 3296921 := bstep (se 2 (by rfl) ⟨1236345, by rfl⟩ : syracuseStep 3296921 = 2472691) B2472691
theorem B2197947 : Blo 2197435 2197947 := bstep (se 1 (by rfl) ⟨1648460, by rfl⟩ : syracuseStep 2197947 = 3296921) B3296921
theorem B3960781 : Blo 2197435 3960781 := bbase (se 3 (by rfl) ⟨742646, by rfl⟩ : syracuseStep 3960781 = 1485293) (by norm_num)
theorem B21124165 : Blo 2197435 21124165 := bstep (se 4 (by rfl) ⟨1980390, by rfl⟩ : syracuseStep 21124165 = 3960781) B3960781
theorem B28165553 : Blo 2197435 28165553 := bstep (se 2 (by rfl) ⟨10562082, by rfl⟩ : syracuseStep 28165553 = 21124165) B21124165
theorem B18777035 : Blo 2197435 18777035 := bstep (se 1 (by rfl) ⟨14082776, by rfl⟩ : syracuseStep 18777035 = 28165553) B28165553
theorem B12518023 : Blo 2197435 12518023 := bstep (se 1 (by rfl) ⟨9388517, by rfl⟩ : syracuseStep 12518023 = 18777035) B18777035
theorem B16690697 : Blo 2197435 16690697 := bstep (se 2 (by rfl) ⟨6259011, by rfl⟩ : syracuseStep 16690697 = 12518023) B12518023
theorem B11127131 : Blo 2197435 11127131 := bstep (se 1 (by rfl) ⟨8345348, by rfl⟩ : syracuseStep 11127131 = 16690697) B16690697
theorem B7418087 : Blo 2197435 7418087 := bstep (se 1 (by rfl) ⟨5563565, by rfl⟩ : syracuseStep 7418087 = 11127131) B11127131
theorem B4945391 : Blo 2197435 4945391 := bstep (se 1 (by rfl) ⟨3709043, by rfl⟩ : syracuseStep 4945391 = 7418087) B7418087
theorem B3296927 : Blo 2197435 3296927 := bstep (se 1 (by rfl) ⟨2472695, by rfl⟩ : syracuseStep 3296927 = 4945391) B4945391
theorem B2197951 : Blo 2197435 2197951 := bstep (se 1 (by rfl) ⟨1648463, by rfl⟩ : syracuseStep 2197951 = 3296927) B3296927
theorem B3296933 : Blo 2197435 3296933 := bbase (se 4 (by rfl) ⟨309087, by rfl⟩ : syracuseStep 3296933 = 618175) (by norm_num)
theorem B2197955 : Blo 2197435 2197955 := bstep (se 1 (by rfl) ⟨1648466, by rfl⟩ : syracuseStep 2197955 = 3296933) B3296933
theorem B2781793 : Blo 2197435 2781793 := bbase (se 2 (by rfl) ⟨1043172, by rfl⟩ : syracuseStep 2781793 = 2086345) (by norm_num)
theorem B3709057 : Blo 2197435 3709057 := bstep (se 2 (by rfl) ⟨1390896, by rfl⟩ : syracuseStep 3709057 = 2781793) B2781793
theorem B4945409 : Blo 2197435 4945409 := bstep (se 2 (by rfl) ⟨1854528, by rfl⟩ : syracuseStep 4945409 = 3709057) B3709057
theorem B3296939 : Blo 2197435 3296939 := bstep (se 1 (by rfl) ⟨2472704, by rfl⟩ : syracuseStep 3296939 = 4945409) B4945409
theorem B2197959 : Blo 2197435 2197959 := bstep (se 1 (by rfl) ⟨1648469, by rfl⟩ : syracuseStep 2197959 = 3296939) B3296939
theorem B2472709 : Blo 2197435 2472709 := bbase (se 4 (by rfl) ⟨231816, by rfl⟩ : syracuseStep 2472709 = 463633) (by norm_num)
theorem B3296945 : Blo 2197435 3296945 := bstep (se 2 (by rfl) ⟨1236354, by rfl⟩ : syracuseStep 3296945 = 2472709) B2472709
theorem B2197963 : Blo 2197435 2197963 := bstep (se 1 (by rfl) ⟨1648472, by rfl⟩ : syracuseStep 2197963 = 3296945) B3296945
theorem B2640541 : Blo 2197435 2640541 := bbase (se 3 (by rfl) ⟨495101, by rfl⟩ : syracuseStep 2640541 = 990203) (by norm_num)
theorem B3520721 : Blo 2197435 3520721 := bstep (se 2 (by rfl) ⟨1320270, by rfl⟩ : syracuseStep 3520721 = 2640541) B2640541
theorem B2347147 : Blo 2197435 2347147 := bstep (se 1 (by rfl) ⟨1760360, by rfl⟩ : syracuseStep 2347147 = 3520721) B3520721
theorem B3129529 : Blo 2197435 3129529 := bstep (se 2 (by rfl) ⟨1173573, by rfl⟩ : syracuseStep 3129529 = 2347147) B2347147
theorem B4172705 : Blo 2197435 4172705 := bstep (se 2 (by rfl) ⟨1564764, by rfl⟩ : syracuseStep 4172705 = 3129529) B3129529
theorem B2781803 : Blo 2197435 2781803 := bstep (se 1 (by rfl) ⟨2086352, by rfl⟩ : syracuseStep 2781803 = 4172705) B4172705
theorem B7418141 : Blo 2197435 7418141 := bstep (se 3 (by rfl) ⟨1390901, by rfl⟩ : syracuseStep 7418141 = 2781803) B2781803
theorem B4945427 : Blo 2197435 4945427 := bstep (se 1 (by rfl) ⟨3709070, by rfl⟩ : syracuseStep 4945427 = 7418141) B7418141
theorem B3296951 : Blo 2197435 3296951 := bstep (se 1 (by rfl) ⟨2472713, by rfl⟩ : syracuseStep 3296951 = 4945427) B4945427
theorem B2197967 : Blo 2197435 2197967 := bstep (se 1 (by rfl) ⟨1648475, by rfl⟩ : syracuseStep 2197967 = 3296951) B3296951
theorem B3296957 : Blo 2197435 3296957 := bbase (se 3 (by rfl) ⟨618179, by rfl⟩ : syracuseStep 3296957 = 1236359) (by norm_num)
theorem B2197971 : Blo 2197435 2197971 := bstep (se 1 (by rfl) ⟨1648478, by rfl⟩ : syracuseStep 2197971 = 3296957) B3296957
theorem B4945445 : Blo 2197435 4945445 := bbase (se 4 (by rfl) ⟨463635, by rfl⟩ : syracuseStep 4945445 = 927271) (by norm_num)
theorem B3296963 : Blo 2197435 3296963 := bstep (se 1 (by rfl) ⟨2472722, by rfl⟩ : syracuseStep 3296963 = 4945445) B4945445
theorem B2197975 : Blo 2197435 2197975 := bstep (se 1 (by rfl) ⟨1648481, by rfl⟩ : syracuseStep 2197975 = 3296963) B3296963
theorem B5563637 : Blo 2197435 5563637 := bbase (se 5 (by rfl) ⟨260795, by rfl⟩ : syracuseStep 5563637 = 521591) (by norm_num)
theorem B3709091 : Blo 2197435 3709091 := bstep (se 1 (by rfl) ⟨2781818, by rfl⟩ : syracuseStep 3709091 = 5563637) B5563637
theorem B2472727 : Blo 2197435 2472727 := bstep (se 1 (by rfl) ⟨1854545, by rfl⟩ : syracuseStep 2472727 = 3709091) B3709091
theorem B3296969 : Blo 2197435 3296969 := bstep (se 2 (by rfl) ⟨1236363, by rfl⟩ : syracuseStep 3296969 = 2472727) B2472727
theorem B2197979 : Blo 2197435 2197979 := bstep (se 1 (by rfl) ⟨1648484, by rfl⟩ : syracuseStep 2197979 = 3296969) B3296969
theorem B8459333 : Blo 2197435 8459333 := bbase (se 4 (by rfl) ⟨793062, by rfl⟩ : syracuseStep 8459333 = 1586125) (by norm_num)
theorem B5639555 : Blo 2197435 5639555 := bstep (se 1 (by rfl) ⟨4229666, by rfl⟩ : syracuseStep 5639555 = 8459333) B8459333
theorem B3759703 : Blo 2197435 3759703 := bstep (se 1 (by rfl) ⟨2819777, by rfl⟩ : syracuseStep 3759703 = 5639555) B5639555
theorem B20051749 : Blo 2197435 20051749 := bstep (se 4 (by rfl) ⟨1879851, by rfl⟩ : syracuseStep 20051749 = 3759703) B3759703
theorem B26735665 : Blo 2197435 26735665 := bstep (se 2 (by rfl) ⟨10025874, by rfl⟩ : syracuseStep 26735665 = 20051749) B20051749
theorem B35647553 : Blo 2197435 35647553 := bstep (se 2 (by rfl) ⟨13367832, by rfl⟩ : syracuseStep 35647553 = 26735665) B26735665
theorem B23765035 : Blo 2197435 23765035 := bstep (se 1 (by rfl) ⟨17823776, by rfl⟩ : syracuseStep 23765035 = 35647553) B35647553
theorem B31686713 : Blo 2197435 31686713 := bstep (se 2 (by rfl) ⟨11882517, by rfl⟩ : syracuseStep 31686713 = 23765035) B23765035
theorem B21124475 : Blo 2197435 21124475 := bstep (se 1 (by rfl) ⟨15843356, by rfl⟩ : syracuseStep 21124475 = 31686713) B31686713
theorem B14082983 : Blo 2197435 14082983 := bstep (se 1 (by rfl) ⟨10562237, by rfl⟩ : syracuseStep 14082983 = 21124475) B21124475
theorem B9388655 : Blo 2197435 9388655 := bstep (se 1 (by rfl) ⟨7041491, by rfl⟩ : syracuseStep 9388655 = 14082983) B14082983
theorem B6259103 : Blo 2197435 6259103 := bstep (se 1 (by rfl) ⟨4694327, by rfl⟩ : syracuseStep 6259103 = 9388655) B9388655
theorem B4172735 : Blo 2197435 4172735 := bstep (se 1 (by rfl) ⟨3129551, by rfl⟩ : syracuseStep 4172735 = 6259103) B6259103
theorem B11127293 : Blo 2197435 11127293 := bstep (se 3 (by rfl) ⟨2086367, by rfl⟩ : syracuseStep 11127293 = 4172735) B4172735
theorem B7418195 : Blo 2197435 7418195 := bstep (se 1 (by rfl) ⟨5563646, by rfl⟩ : syracuseStep 7418195 = 11127293) B11127293
theorem B4945463 : Blo 2197435 4945463 := bstep (se 1 (by rfl) ⟨3709097, by rfl⟩ : syracuseStep 4945463 = 7418195) B7418195
theorem B3296975 : Blo 2197435 3296975 := bstep (se 1 (by rfl) ⟨2472731, by rfl⟩ : syracuseStep 3296975 = 4945463) B4945463
theorem B2197983 : Blo 2197435 2197983 := bstep (se 1 (by rfl) ⟨1648487, by rfl⟩ : syracuseStep 2197983 = 3296975) B3296975
theorem B3296981 : Blo 2197435 3296981 := bbase (se 7 (by rfl) ⟨38636, by rfl⟩ : syracuseStep 3296981 = 77273) (by norm_num)
theorem B2197987 : Blo 2197435 2197987 := bstep (se 1 (by rfl) ⟨1648490, by rfl⟩ : syracuseStep 2197987 = 3296981) B3296981
theorem B2227981 : Blo 2197435 2227981 := bbase (se 3 (by rfl) ⟨417746, by rfl⟩ : syracuseStep 2227981 = 835493) (by norm_num)
theorem B2970641 : Blo 2197435 2970641 := bstep (se 2 (by rfl) ⟨1113990, by rfl⟩ : syracuseStep 2970641 = 2227981) B2227981
theorem B7921709 : Blo 2197435 7921709 := bstep (se 3 (by rfl) ⟨1485320, by rfl⟩ : syracuseStep 7921709 = 2970641) B2970641
theorem B5281139 : Blo 2197435 5281139 := bstep (se 1 (by rfl) ⟨3960854, by rfl⟩ : syracuseStep 5281139 = 7921709) B7921709
theorem B3520759 : Blo 2197435 3520759 := bstep (se 1 (by rfl) ⟨2640569, by rfl⟩ : syracuseStep 3520759 = 5281139) B5281139
theorem B4694345 : Blo 2197435 4694345 := bstep (se 2 (by rfl) ⟨1760379, by rfl⟩ : syracuseStep 4694345 = 3520759) B3520759
theorem B3129563 : Blo 2197435 3129563 := bstep (se 1 (by rfl) ⟨2347172, by rfl⟩ : syracuseStep 3129563 = 4694345) B4694345
theorem B8345501 : Blo 2197435 8345501 := bstep (se 3 (by rfl) ⟨1564781, by rfl⟩ : syracuseStep 8345501 = 3129563) B3129563
theorem B5563667 : Blo 2197435 5563667 := bstep (se 1 (by rfl) ⟨4172750, by rfl⟩ : syracuseStep 5563667 = 8345501) B8345501
theorem B3709111 : Blo 2197435 3709111 := bstep (se 1 (by rfl) ⟨2781833, by rfl⟩ : syracuseStep 3709111 = 5563667) B5563667
theorem B4945481 : Blo 2197435 4945481 := bstep (se 2 (by rfl) ⟨1854555, by rfl⟩ : syracuseStep 4945481 = 3709111) B3709111
theorem B3296987 : Blo 2197435 3296987 := bstep (se 1 (by rfl) ⟨2472740, by rfl⟩ : syracuseStep 3296987 = 4945481) B4945481
theorem B2197991 : Blo 2197435 2197991 := bstep (se 1 (by rfl) ⟨1648493, by rfl⟩ : syracuseStep 2197991 = 3296987) B3296987
theorem B2472745 : Blo 2197435 2472745 := bbase (se 2 (by rfl) ⟨927279, by rfl⟩ : syracuseStep 2472745 = 1854559) (by norm_num)
theorem B3296993 : Blo 2197435 3296993 := bstep (se 2 (by rfl) ⟨1236372, by rfl⟩ : syracuseStep 3296993 = 2472745) B2472745
theorem B2197995 : Blo 2197435 2197995 := bstep (se 1 (by rfl) ⟨1648496, by rfl⟩ : syracuseStep 2197995 = 3296993) B3296993
theorem B5281157 : Blo 2197435 5281157 := bbase (se 4 (by rfl) ⟨495108, by rfl⟩ : syracuseStep 5281157 = 990217) (by norm_num)
theorem B14083085 : Blo 2197435 14083085 := bstep (se 3 (by rfl) ⟨2640578, by rfl⟩ : syracuseStep 14083085 = 5281157) B5281157
theorem B9388723 : Blo 2197435 9388723 := bstep (se 1 (by rfl) ⟨7041542, by rfl⟩ : syracuseStep 9388723 = 14083085) B14083085
theorem B12518297 : Blo 2197435 12518297 := bstep (se 2 (by rfl) ⟨4694361, by rfl⟩ : syracuseStep 12518297 = 9388723) B9388723
theorem B8345531 : Blo 2197435 8345531 := bstep (se 1 (by rfl) ⟨6259148, by rfl⟩ : syracuseStep 8345531 = 12518297) B12518297
theorem B5563687 : Blo 2197435 5563687 := bstep (se 1 (by rfl) ⟨4172765, by rfl⟩ : syracuseStep 5563687 = 8345531) B8345531
theorem B7418249 : Blo 2197435 7418249 := bstep (se 2 (by rfl) ⟨2781843, by rfl⟩ : syracuseStep 7418249 = 5563687) B5563687
theorem B4945499 : Blo 2197435 4945499 := bstep (se 1 (by rfl) ⟨3709124, by rfl⟩ : syracuseStep 4945499 = 7418249) B7418249
theorem B3296999 : Blo 2197435 3296999 := bstep (se 1 (by rfl) ⟨2472749, by rfl⟩ : syracuseStep 3296999 = 4945499) B4945499
theorem B2197999 : Blo 2197435 2197999 := bstep (se 1 (by rfl) ⟨1648499, by rfl⟩ : syracuseStep 2197999 = 3296999) B3296999
theorem B3297005 : Blo 2197435 3297005 := bbase (se 3 (by rfl) ⟨618188, by rfl⟩ : syracuseStep 3297005 = 1236377) (by norm_num)
theorem B2198003 : Blo 2197435 2198003 := bstep (se 1 (by rfl) ⟨1648502, by rfl⟩ : syracuseStep 2198003 = 3297005) B3297005
theorem B4945517 : Blo 2197435 4945517 := bbase (se 3 (by rfl) ⟨927284, by rfl⟩ : syracuseStep 4945517 = 1854569) (by norm_num)
theorem B3297011 : Blo 2197435 3297011 := bstep (se 1 (by rfl) ⟨2472758, by rfl⟩ : syracuseStep 3297011 = 4945517) B4945517
theorem B2198007 : Blo 2197435 2198007 := bstep (se 1 (by rfl) ⟨1648505, by rfl⟩ : syracuseStep 2198007 = 3297011) B3297011
theorem B4172789 : Blo 2197435 4172789 := bbase (se 5 (by rfl) ⟨195599, by rfl⟩ : syracuseStep 4172789 = 391199) (by norm_num)
theorem B2781859 : Blo 2197435 2781859 := bstep (se 1 (by rfl) ⟨2086394, by rfl⟩ : syracuseStep 2781859 = 4172789) B4172789
theorem B3709145 : Blo 2197435 3709145 := bstep (se 2 (by rfl) ⟨1390929, by rfl⟩ : syracuseStep 3709145 = 2781859) B2781859
theorem B2472763 : Blo 2197435 2472763 := bstep (se 1 (by rfl) ⟨1854572, by rfl⟩ : syracuseStep 2472763 = 3709145) B3709145
theorem B3297017 : Blo 2197435 3297017 := bstep (se 2 (by rfl) ⟨1236381, by rfl⟩ : syracuseStep 3297017 = 2472763) B2472763
theorem B2198011 : Blo 2197435 2198011 := bstep (se 1 (by rfl) ⟨1648508, by rfl⟩ : syracuseStep 2198011 = 3297017) B3297017
theorem B15039029 : Blo 2197435 15039029 := bbase (se 5 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 15039029 = 1409909) (by norm_num)
theorem B10026019 : Blo 2197435 10026019 := bstep (se 1 (by rfl) ⟨7519514, by rfl⟩ : syracuseStep 10026019 = 15039029) B15039029
theorem B13368025 : Blo 2197435 13368025 := bstep (se 2 (by rfl) ⟨5013009, by rfl⟩ : syracuseStep 13368025 = 10026019) B10026019
theorem B17824033 : Blo 2197435 17824033 := bstep (se 2 (by rfl) ⟨6684012, by rfl⟩ : syracuseStep 17824033 = 13368025) B13368025
theorem B95061509 : Blo 2197435 95061509 := bstep (se 4 (by rfl) ⟨8912016, by rfl⟩ : syracuseStep 95061509 = 17824033) B17824033
theorem B63374339 : Blo 2197435 63374339 := bstep (se 1 (by rfl) ⟨47530754, by rfl⟩ : syracuseStep 63374339 = 95061509) B95061509
theorem B42249559 : Blo 2197435 42249559 := bstep (se 1 (by rfl) ⟨31687169, by rfl⟩ : syracuseStep 42249559 = 63374339) B63374339
theorem B56332745 : Blo 2197435 56332745 := bstep (se 2 (by rfl) ⟨21124779, by rfl⟩ : syracuseStep 56332745 = 42249559) B42249559
theorem B37555163 : Blo 2197435 37555163 := bstep (se 1 (by rfl) ⟨28166372, by rfl⟩ : syracuseStep 37555163 = 56332745) B56332745
theorem B25036775 : Blo 2197435 25036775 := bstep (se 1 (by rfl) ⟨18777581, by rfl⟩ : syracuseStep 25036775 = 37555163) B37555163
theorem B16691183 : Blo 2197435 16691183 := bstep (se 1 (by rfl) ⟨12518387, by rfl⟩ : syracuseStep 16691183 = 25036775) B25036775
theorem B11127455 : Blo 2197435 11127455 := bstep (se 1 (by rfl) ⟨8345591, by rfl⟩ : syracuseStep 11127455 = 16691183) B16691183
theorem B7418303 : Blo 2197435 7418303 := bstep (se 1 (by rfl) ⟨5563727, by rfl⟩ : syracuseStep 7418303 = 11127455) B11127455
theorem B4945535 : Blo 2197435 4945535 := bstep (se 1 (by rfl) ⟨3709151, by rfl⟩ : syracuseStep 4945535 = 7418303) B7418303
theorem B3297023 : Blo 2197435 3297023 := bstep (se 1 (by rfl) ⟨2472767, by rfl⟩ : syracuseStep 3297023 = 4945535) B4945535
theorem B2198015 : Blo 2197435 2198015 := bstep (se 1 (by rfl) ⟨1648511, by rfl⟩ : syracuseStep 2198015 = 3297023) B3297023
theorem B3297029 : Blo 2197435 3297029 := bbase (se 4 (by rfl) ⟨309096, by rfl⟩ : syracuseStep 3297029 = 618193) (by norm_num)
theorem B2198019 : Blo 2197435 2198019 := bstep (se 1 (by rfl) ⟨1648514, by rfl⟩ : syracuseStep 2198019 = 3297029) B3297029
theorem B3709165 : Blo 2197435 3709165 := bbase (se 3 (by rfl) ⟨695468, by rfl⟩ : syracuseStep 3709165 = 1390937) (by norm_num)
theorem B4945553 : Blo 2197435 4945553 := bstep (se 2 (by rfl) ⟨1854582, by rfl⟩ : syracuseStep 4945553 = 3709165) B3709165
theorem B3297035 : Blo 2197435 3297035 := bstep (se 1 (by rfl) ⟨2472776, by rfl⟩ : syracuseStep 3297035 = 4945553) B4945553
theorem B2198023 : Blo 2197435 2198023 := bstep (se 1 (by rfl) ⟨1648517, by rfl⟩ : syracuseStep 2198023 = 3297035) B3297035
theorem B2472781 : Blo 2197435 2472781 := bbase (se 3 (by rfl) ⟨463646, by rfl⟩ : syracuseStep 2472781 = 927293) (by norm_num)
theorem B3297041 : Blo 2197435 3297041 := bstep (se 2 (by rfl) ⟨1236390, by rfl⟩ : syracuseStep 3297041 = 2472781) B2472781
theorem B2198027 : Blo 2197435 2198027 := bstep (se 1 (by rfl) ⟨1648520, by rfl⟩ : syracuseStep 2198027 = 3297041) B3297041
theorem B7418357 : Blo 2197435 7418357 := bbase (se 5 (by rfl) ⟨347735, by rfl⟩ : syracuseStep 7418357 = 695471) (by norm_num)
theorem B4945571 : Blo 2197435 4945571 := bstep (se 1 (by rfl) ⟨3709178, by rfl⟩ : syracuseStep 4945571 = 7418357) B7418357
theorem B3297047 : Blo 2197435 3297047 := bstep (se 1 (by rfl) ⟨2472785, by rfl⟩ : syracuseStep 3297047 = 4945571) B4945571
theorem B2198031 : Blo 2197435 2198031 := bstep (se 1 (by rfl) ⟨1648523, by rfl⟩ : syracuseStep 2198031 = 3297047) B3297047
theorem B3297053 : Blo 2197435 3297053 := bbase (se 3 (by rfl) ⟨618197, by rfl⟩ : syracuseStep 3297053 = 1236395) (by norm_num)
theorem B2198035 : Blo 2197435 2198035 := bstep (se 1 (by rfl) ⟨1648526, by rfl⟩ : syracuseStep 2198035 = 3297053) B3297053
theorem B4945589 : Blo 2197435 4945589 := bbase (se 5 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 4945589 = 463649) (by norm_num)
theorem B3297059 : Blo 2197435 3297059 := bstep (se 1 (by rfl) ⟨2472794, by rfl⟩ : syracuseStep 3297059 = 4945589) B4945589
theorem B2198039 : Blo 2197435 2198039 := bstep (se 1 (by rfl) ⟨1648529, by rfl⟩ : syracuseStep 2198039 = 3297059) B3297059
theorem B12518549 : Blo 2197435 12518549 := bbase (se 6 (by rfl) ⟨293403, by rfl⟩ : syracuseStep 12518549 = 586807) (by norm_num)
theorem B8345699 : Blo 2197435 8345699 := bstep (se 1 (by rfl) ⟨6259274, by rfl⟩ : syracuseStep 8345699 = 12518549) B12518549
theorem B5563799 : Blo 2197435 5563799 := bstep (se 1 (by rfl) ⟨4172849, by rfl⟩ : syracuseStep 5563799 = 8345699) B8345699
theorem B3709199 : Blo 2197435 3709199 := bstep (se 1 (by rfl) ⟨2781899, by rfl⟩ : syracuseStep 3709199 = 5563799) B5563799
theorem B2472799 : Blo 2197435 2472799 := bstep (se 1 (by rfl) ⟨1854599, by rfl⟩ : syracuseStep 2472799 = 3709199) B3709199
theorem B3297065 : Blo 2197435 3297065 := bstep (se 2 (by rfl) ⟨1236399, by rfl⟩ : syracuseStep 3297065 = 2472799) B2472799
theorem B2198043 : Blo 2197435 2198043 := bstep (se 1 (by rfl) ⟨1648532, by rfl⟩ : syracuseStep 2198043 = 3297065) B3297065
theorem B6259285 : Blo 2197435 6259285 := bbase (se 8 (by rfl) ⟨36675, by rfl⟩ : syracuseStep 6259285 = 73351) (by norm_num)
theorem B8345713 : Blo 2197435 8345713 := bstep (se 2 (by rfl) ⟨3129642, by rfl⟩ : syracuseStep 8345713 = 6259285) B6259285
theorem B11127617 : Blo 2197435 11127617 := bstep (se 2 (by rfl) ⟨4172856, by rfl⟩ : syracuseStep 11127617 = 8345713) B8345713
theorem B7418411 : Blo 2197435 7418411 := bstep (se 1 (by rfl) ⟨5563808, by rfl⟩ : syracuseStep 7418411 = 11127617) B11127617
theorem B4945607 : Blo 2197435 4945607 := bstep (se 1 (by rfl) ⟨3709205, by rfl⟩ : syracuseStep 4945607 = 7418411) B7418411
theorem B3297071 : Blo 2197435 3297071 := bstep (se 1 (by rfl) ⟨2472803, by rfl⟩ : syracuseStep 3297071 = 4945607) B4945607
theorem B2198047 : Blo 2197435 2198047 := bstep (se 1 (by rfl) ⟨1648535, by rfl⟩ : syracuseStep 2198047 = 3297071) B3297071
theorem B3297077 : Blo 2197435 3297077 := bbase (se 5 (by rfl) ⟨154550, by rfl⟩ : syracuseStep 3297077 = 309101) (by norm_num)
theorem B2198051 : Blo 2197435 2198051 := bstep (se 1 (by rfl) ⟨1648538, by rfl⟩ : syracuseStep 2198051 = 3297077) B3297077
theorem B5563829 : Blo 2197435 5563829 := bbase (se 5 (by rfl) ⟨260804, by rfl⟩ : syracuseStep 5563829 = 521609) (by norm_num)
theorem B3709219 : Blo 2197435 3709219 := bstep (se 1 (by rfl) ⟨2781914, by rfl⟩ : syracuseStep 3709219 = 5563829) B5563829
theorem B4945625 : Blo 2197435 4945625 := bstep (se 2 (by rfl) ⟨1854609, by rfl⟩ : syracuseStep 4945625 = 3709219) B3709219
theorem B3297083 : Blo 2197435 3297083 := bstep (se 1 (by rfl) ⟨2472812, by rfl⟩ : syracuseStep 3297083 = 4945625) B4945625
theorem B2198055 : Blo 2197435 2198055 := bstep (se 1 (by rfl) ⟨1648541, by rfl⟩ : syracuseStep 2198055 = 3297083) B3297083
theorem B2472817 : Blo 2197435 2472817 := bbase (se 2 (by rfl) ⟨927306, by rfl⟩ : syracuseStep 2472817 = 1854613) (by norm_num)
theorem B3297089 : Blo 2197435 3297089 := bstep (se 2 (by rfl) ⟨1236408, by rfl⟩ : syracuseStep 3297089 = 2472817) B2472817
theorem B2198059 : Blo 2197435 2198059 := bstep (se 1 (by rfl) ⟨1648544, by rfl⟩ : syracuseStep 2198059 = 3297089) B3297089
theorem B9388997 : Blo 2197435 9388997 := bbase (se 4 (by rfl) ⟨880218, by rfl⟩ : syracuseStep 9388997 = 1760437) (by norm_num)
theorem B6259331 : Blo 2197435 6259331 := bstep (se 1 (by rfl) ⟨4694498, by rfl⟩ : syracuseStep 6259331 = 9388997) B9388997
theorem B4172887 : Blo 2197435 4172887 := bstep (se 1 (by rfl) ⟨3129665, by rfl⟩ : syracuseStep 4172887 = 6259331) B6259331
theorem B5563849 : Blo 2197435 5563849 := bstep (se 2 (by rfl) ⟨2086443, by rfl⟩ : syracuseStep 5563849 = 4172887) B4172887
theorem B7418465 : Blo 2197435 7418465 := bstep (se 2 (by rfl) ⟨2781924, by rfl⟩ : syracuseStep 7418465 = 5563849) B5563849
theorem B4945643 : Blo 2197435 4945643 := bstep (se 1 (by rfl) ⟨3709232, by rfl⟩ : syracuseStep 4945643 = 7418465) B7418465
theorem B3297095 : Blo 2197435 3297095 := bstep (se 1 (by rfl) ⟨2472821, by rfl⟩ : syracuseStep 3297095 = 4945643) B4945643
theorem B2198063 : Blo 2197435 2198063 := bstep (se 1 (by rfl) ⟨1648547, by rfl⟩ : syracuseStep 2198063 = 3297095) B3297095
theorem B3297101 : Blo 2197435 3297101 := bbase (se 3 (by rfl) ⟨618206, by rfl⟩ : syracuseStep 3297101 = 1236413) (by norm_num)
theorem B2198067 : Blo 2197435 2198067 := bstep (se 1 (by rfl) ⟨1648550, by rfl⟩ : syracuseStep 2198067 = 3297101) B3297101
theorem B4945661 : Blo 2197435 4945661 := bbase (se 3 (by rfl) ⟨927311, by rfl⟩ : syracuseStep 4945661 = 1854623) (by norm_num)
theorem B3297107 : Blo 2197435 3297107 := bstep (se 1 (by rfl) ⟨2472830, by rfl⟩ : syracuseStep 3297107 = 4945661) B4945661
theorem B2198071 : Blo 2197435 2198071 := bstep (se 1 (by rfl) ⟨1648553, by rfl⟩ : syracuseStep 2198071 = 3297107) B3297107
theorem B3709253 : Blo 2197435 3709253 := bbase (se 4 (by rfl) ⟨347742, by rfl⟩ : syracuseStep 3709253 = 695485) (by norm_num)
theorem B2472835 : Blo 2197435 2472835 := bstep (se 1 (by rfl) ⟨1854626, by rfl⟩ : syracuseStep 2472835 = 3709253) B3709253
theorem B3297113 : Blo 2197435 3297113 := bstep (se 2 (by rfl) ⟨1236417, by rfl⟩ : syracuseStep 3297113 = 2472835) B2472835
theorem B2198075 : Blo 2197435 2198075 := bstep (se 1 (by rfl) ⟨1648556, by rfl⟩ : syracuseStep 2198075 = 3297113) B3297113
theorem B16691669 : Blo 2197435 16691669 := bbase (se 7 (by rfl) ⟨195605, by rfl⟩ : syracuseStep 16691669 = 391211) (by norm_num)
theorem B11127779 : Blo 2197435 11127779 := bstep (se 1 (by rfl) ⟨8345834, by rfl⟩ : syracuseStep 11127779 = 16691669) B16691669
theorem B7418519 : Blo 2197435 7418519 := bstep (se 1 (by rfl) ⟨5563889, by rfl⟩ : syracuseStep 7418519 = 11127779) B11127779
theorem B4945679 : Blo 2197435 4945679 := bstep (se 1 (by rfl) ⟨3709259, by rfl⟩ : syracuseStep 4945679 = 7418519) B7418519
theorem B3297119 : Blo 2197435 3297119 := bstep (se 1 (by rfl) ⟨2472839, by rfl⟩ : syracuseStep 3297119 = 4945679) B4945679
theorem B2198079 : Blo 2197435 2198079 := bstep (se 1 (by rfl) ⟨1648559, by rfl⟩ : syracuseStep 2198079 = 3297119) B3297119
theorem B3297125 : Blo 2197435 3297125 := bbase (se 4 (by rfl) ⟨309105, by rfl⟩ : syracuseStep 3297125 = 618211) (by norm_num)
theorem B2198083 : Blo 2197435 2198083 := bstep (se 1 (by rfl) ⟨1648562, by rfl⟩ : syracuseStep 2198083 = 3297125) B3297125
theorem B4172933 : Blo 2197435 4172933 := bbase (se 4 (by rfl) ⟨391212, by rfl⟩ : syracuseStep 4172933 = 782425) (by norm_num)
theorem B2781955 : Blo 2197435 2781955 := bstep (se 1 (by rfl) ⟨2086466, by rfl⟩ : syracuseStep 2781955 = 4172933) B4172933
theorem B3709273 : Blo 2197435 3709273 := bstep (se 2 (by rfl) ⟨1390977, by rfl⟩ : syracuseStep 3709273 = 2781955) B2781955
theorem B4945697 : Blo 2197435 4945697 := bstep (se 2 (by rfl) ⟨1854636, by rfl⟩ : syracuseStep 4945697 = 3709273) B3709273
theorem B3297131 : Blo 2197435 3297131 := bstep (se 1 (by rfl) ⟨2472848, by rfl⟩ : syracuseStep 3297131 = 4945697) B4945697
theorem B2198087 : Blo 2197435 2198087 := bstep (se 1 (by rfl) ⟨1648565, by rfl⟩ : syracuseStep 2198087 = 3297131) B3297131
theorem B2472853 : Blo 2197435 2472853 := bbase (se 6 (by rfl) ⟨57957, by rfl⟩ : syracuseStep 2472853 = 115915) (by norm_num)
theorem B3297137 : Blo 2197435 3297137 := bstep (se 2 (by rfl) ⟨1236426, by rfl⟩ : syracuseStep 3297137 = 2472853) B2472853
theorem B2198091 : Blo 2197435 2198091 := bstep (se 1 (by rfl) ⟨1648568, by rfl⟩ : syracuseStep 2198091 = 3297137) B3297137
theorem B2781965 : Blo 2197435 2781965 := bbase (se 3 (by rfl) ⟨521618, by rfl⟩ : syracuseStep 2781965 = 1043237) (by norm_num)
theorem B7418573 : Blo 2197435 7418573 := bstep (se 3 (by rfl) ⟨1390982, by rfl⟩ : syracuseStep 7418573 = 2781965) B2781965
theorem B4945715 : Blo 2197435 4945715 := bstep (se 1 (by rfl) ⟨3709286, by rfl⟩ : syracuseStep 4945715 = 7418573) B7418573
theorem B3297143 : Blo 2197435 3297143 := bstep (se 1 (by rfl) ⟨2472857, by rfl⟩ : syracuseStep 3297143 = 4945715) B4945715
theorem B2198095 : Blo 2197435 2198095 := bstep (se 1 (by rfl) ⟨1648571, by rfl⟩ : syracuseStep 2198095 = 3297143) B3297143
theorem B3297149 : Blo 2197435 3297149 := bbase (se 3 (by rfl) ⟨618215, by rfl⟩ : syracuseStep 3297149 = 1236431) (by norm_num)
theorem B2198099 : Blo 2197435 2198099 := bstep (se 1 (by rfl) ⟨1648574, by rfl⟩ : syracuseStep 2198099 = 3297149) B3297149
theorem B4945733 : Blo 2197435 4945733 := bbase (se 4 (by rfl) ⟨463662, by rfl⟩ : syracuseStep 4945733 = 927325) (by norm_num)
theorem B3297155 : Blo 2197435 3297155 := bstep (se 1 (by rfl) ⟨2472866, by rfl⟩ : syracuseStep 3297155 = 4945733) B4945733
theorem B2198103 : Blo 2197435 2198103 := bstep (se 1 (by rfl) ⟨1648577, by rfl⟩ : syracuseStep 2198103 = 3297155) B3297155
theorem B2640709 : Blo 2197435 2640709 := bbase (se 4 (by rfl) ⟨247566, by rfl⟩ : syracuseStep 2640709 = 495133) (by norm_num)
theorem B3520945 : Blo 2197435 3520945 := bstep (se 2 (by rfl) ⟨1320354, by rfl⟩ : syracuseStep 3520945 = 2640709) B2640709
theorem B4694593 : Blo 2197435 4694593 := bstep (se 2 (by rfl) ⟨1760472, by rfl⟩ : syracuseStep 4694593 = 3520945) B3520945
theorem B6259457 : Blo 2197435 6259457 := bstep (se 2 (by rfl) ⟨2347296, by rfl⟩ : syracuseStep 6259457 = 4694593) B4694593
theorem B4172971 : Blo 2197435 4172971 := bstep (se 1 (by rfl) ⟨3129728, by rfl⟩ : syracuseStep 4172971 = 6259457) B6259457
theorem B5563961 : Blo 2197435 5563961 := bstep (se 2 (by rfl) ⟨2086485, by rfl⟩ : syracuseStep 5563961 = 4172971) B4172971
theorem B3709307 : Blo 2197435 3709307 := bstep (se 1 (by rfl) ⟨2781980, by rfl⟩ : syracuseStep 3709307 = 5563961) B5563961
theorem B2472871 : Blo 2197435 2472871 := bstep (se 1 (by rfl) ⟨1854653, by rfl⟩ : syracuseStep 2472871 = 3709307) B3709307
theorem B3297161 : Blo 2197435 3297161 := bstep (se 2 (by rfl) ⟨1236435, by rfl⟩ : syracuseStep 3297161 = 2472871) B2472871
theorem B2198107 : Blo 2197435 2198107 := bstep (se 1 (by rfl) ⟨1648580, by rfl⟩ : syracuseStep 2198107 = 3297161) B3297161
theorem B11127941 : Blo 2197435 11127941 := bbase (se 4 (by rfl) ⟨1043244, by rfl⟩ : syracuseStep 11127941 = 2086489) (by norm_num)
theorem B7418627 : Blo 2197435 7418627 := bstep (se 1 (by rfl) ⟨5563970, by rfl⟩ : syracuseStep 7418627 = 11127941) B11127941
theorem B4945751 : Blo 2197435 4945751 := bstep (se 1 (by rfl) ⟨3709313, by rfl⟩ : syracuseStep 4945751 = 7418627) B7418627
theorem B3297167 : Blo 2197435 3297167 := bstep (se 1 (by rfl) ⟨2472875, by rfl⟩ : syracuseStep 3297167 = 4945751) B4945751
theorem B2198111 : Blo 2197435 2198111 := bstep (se 1 (by rfl) ⟨1648583, by rfl⟩ : syracuseStep 2198111 = 3297167) B3297167
theorem B3297173 : Blo 2197435 3297173 := bbase (se 6 (by rfl) ⟨77277, by rfl⟩ : syracuseStep 3297173 = 154555) (by norm_num)
theorem B2198115 : Blo 2197435 2198115 := bstep (se 1 (by rfl) ⟨1648586, by rfl⟩ : syracuseStep 2198115 = 3297173) B3297173
theorem B2347309 : Blo 2197435 2347309 := bbase (se 3 (by rfl) ⟨440120, by rfl⟩ : syracuseStep 2347309 = 880241) (by norm_num)
theorem B12518981 : Blo 2197435 12518981 := bstep (se 4 (by rfl) ⟨1173654, by rfl⟩ : syracuseStep 12518981 = 2347309) B2347309
theorem B8345987 : Blo 2197435 8345987 := bstep (se 1 (by rfl) ⟨6259490, by rfl⟩ : syracuseStep 8345987 = 12518981) B12518981
theorem B5563991 : Blo 2197435 5563991 := bstep (se 1 (by rfl) ⟨4172993, by rfl⟩ : syracuseStep 5563991 = 8345987) B8345987
theorem B3709327 : Blo 2197435 3709327 := bstep (se 1 (by rfl) ⟨2781995, by rfl⟩ : syracuseStep 3709327 = 5563991) B5563991
theorem B4945769 : Blo 2197435 4945769 := bstep (se 2 (by rfl) ⟨1854663, by rfl⟩ : syracuseStep 4945769 = 3709327) B3709327
theorem B3297179 : Blo 2197435 3297179 := bstep (se 1 (by rfl) ⟨2472884, by rfl⟩ : syracuseStep 3297179 = 4945769) B4945769
theorem B2198119 : Blo 2197435 2198119 := bstep (se 1 (by rfl) ⟨1648589, by rfl⟩ : syracuseStep 2198119 = 3297179) B3297179
theorem B2472889 : Blo 2197435 2472889 := bbase (se 2 (by rfl) ⟨927333, by rfl⟩ : syracuseStep 2472889 = 1854667) (by norm_num)
theorem B3297185 : Blo 2197435 3297185 := bstep (se 2 (by rfl) ⟨1236444, by rfl⟩ : syracuseStep 3297185 = 2472889) B2472889
theorem B2198123 : Blo 2197435 2198123 := bstep (se 1 (by rfl) ⟨1648592, by rfl⟩ : syracuseStep 2198123 = 3297185) B3297185
theorem B4456237 : Blo 2197435 4456237 := bbase (se 3 (by rfl) ⟨835544, by rfl⟩ : syracuseStep 4456237 = 1671089) (by norm_num)
theorem B5941649 : Blo 2197435 5941649 := bstep (se 2 (by rfl) ⟨2228118, by rfl⟩ : syracuseStep 5941649 = 4456237) B4456237
theorem B3961099 : Blo 2197435 3961099 := bstep (se 1 (by rfl) ⟨2970824, by rfl⟩ : syracuseStep 3961099 = 5941649) B5941649
theorem B5281465 : Blo 2197435 5281465 := bstep (se 2 (by rfl) ⟨1980549, by rfl⟩ : syracuseStep 5281465 = 3961099) B3961099
theorem B7041953 : Blo 2197435 7041953 := bstep (se 2 (by rfl) ⟨2640732, by rfl⟩ : syracuseStep 7041953 = 5281465) B5281465
theorem B4694635 : Blo 2197435 4694635 := bstep (se 1 (by rfl) ⟨3520976, by rfl⟩ : syracuseStep 4694635 = 7041953) B7041953
theorem B6259513 : Blo 2197435 6259513 := bstep (se 2 (by rfl) ⟨2347317, by rfl⟩ : syracuseStep 6259513 = 4694635) B4694635
theorem B8346017 : Blo 2197435 8346017 := bstep (se 2 (by rfl) ⟨3129756, by rfl⟩ : syracuseStep 8346017 = 6259513) B6259513
theorem B5564011 : Blo 2197435 5564011 := bstep (se 1 (by rfl) ⟨4173008, by rfl⟩ : syracuseStep 5564011 = 8346017) B8346017
theorem B7418681 : Blo 2197435 7418681 := bstep (se 2 (by rfl) ⟨2782005, by rfl⟩ : syracuseStep 7418681 = 5564011) B5564011
theorem B4945787 : Blo 2197435 4945787 := bstep (se 1 (by rfl) ⟨3709340, by rfl⟩ : syracuseStep 4945787 = 7418681) B7418681
theorem B3297191 : Blo 2197435 3297191 := bstep (se 1 (by rfl) ⟨2472893, by rfl⟩ : syracuseStep 3297191 = 4945787) B4945787
theorem B2198127 : Blo 2197435 2198127 := bstep (se 1 (by rfl) ⟨1648595, by rfl⟩ : syracuseStep 2198127 = 3297191) B3297191
theorem B3297197 : Blo 2197435 3297197 := bbase (se 3 (by rfl) ⟨618224, by rfl⟩ : syracuseStep 3297197 = 1236449) (by norm_num)
theorem B2198131 : Blo 2197435 2198131 := bstep (se 1 (by rfl) ⟨1648598, by rfl⟩ : syracuseStep 2198131 = 3297197) B3297197
theorem B4945805 : Blo 2197435 4945805 := bbase (se 3 (by rfl) ⟨927338, by rfl⟩ : syracuseStep 4945805 = 1854677) (by norm_num)
theorem B3297203 : Blo 2197435 3297203 := bstep (se 1 (by rfl) ⟨2472902, by rfl⟩ : syracuseStep 3297203 = 4945805) B4945805
theorem B2198135 : Blo 2197435 2198135 := bstep (se 1 (by rfl) ⟨1648601, by rfl⟩ : syracuseStep 2198135 = 3297203) B3297203
theorem B2782021 : Blo 2197435 2782021 := bbase (se 4 (by rfl) ⟨260814, by rfl⟩ : syracuseStep 2782021 = 521629) (by norm_num)
theorem B3709361 : Blo 2197435 3709361 := bstep (se 2 (by rfl) ⟨1391010, by rfl⟩ : syracuseStep 3709361 = 2782021) B2782021
theorem B2472907 : Blo 2197435 2472907 := bstep (se 1 (by rfl) ⟨1854680, by rfl⟩ : syracuseStep 2472907 = 3709361) B3709361
theorem B3297209 : Blo 2197435 3297209 := bstep (se 2 (by rfl) ⟨1236453, by rfl⟩ : syracuseStep 3297209 = 2472907) B2472907
theorem B2198139 : Blo 2197435 2198139 := bstep (se 1 (by rfl) ⟨1648604, by rfl⟩ : syracuseStep 2198139 = 3297209) B3297209
theorem B9517445 : Blo 2197435 9517445 := bbase (se 4 (by rfl) ⟨892260, by rfl⟩ : syracuseStep 9517445 = 1784521) (by norm_num)
theorem B6344963 : Blo 2197435 6344963 := bstep (se 1 (by rfl) ⟨4758722, by rfl⟩ : syracuseStep 6344963 = 9517445) B9517445
theorem B4229975 : Blo 2197435 4229975 := bstep (se 1 (by rfl) ⟨3172481, by rfl⟩ : syracuseStep 4229975 = 6344963) B6344963
theorem B2819983 : Blo 2197435 2819983 := bstep (se 1 (by rfl) ⟨2114987, by rfl⟩ : syracuseStep 2819983 = 4229975) B4229975
theorem B3759977 : Blo 2197435 3759977 := bstep (se 2 (by rfl) ⟨1409991, by rfl⟩ : syracuseStep 3759977 = 2819983) B2819983
theorem B10026605 : Blo 2197435 10026605 := bstep (se 3 (by rfl) ⟨1879988, by rfl⟩ : syracuseStep 10026605 = 3759977) B3759977
theorem B6684403 : Blo 2197435 6684403 := bstep (se 1 (by rfl) ⟨5013302, by rfl⟩ : syracuseStep 6684403 = 10026605) B10026605
theorem B8912537 : Blo 2197435 8912537 := bstep (se 2 (by rfl) ⟨3342201, by rfl⟩ : syracuseStep 8912537 = 6684403) B6684403
theorem B5941691 : Blo 2197435 5941691 := bstep (se 1 (by rfl) ⟨4456268, by rfl⟩ : syracuseStep 5941691 = 8912537) B8912537
theorem B3961127 : Blo 2197435 3961127 := bstep (se 1 (by rfl) ⟨2970845, by rfl⟩ : syracuseStep 3961127 = 5941691) B5941691
theorem B10563005 : Blo 2197435 10563005 := bstep (se 3 (by rfl) ⟨1980563, by rfl⟩ : syracuseStep 10563005 = 3961127) B3961127
theorem B28168013 : Blo 2197435 28168013 := bstep (se 3 (by rfl) ⟨5281502, by rfl⟩ : syracuseStep 28168013 = 10563005) B10563005
theorem B18778675 : Blo 2197435 18778675 := bstep (se 1 (by rfl) ⟨14084006, by rfl⟩ : syracuseStep 18778675 = 28168013) B28168013
theorem B25038233 : Blo 2197435 25038233 := bstep (se 2 (by rfl) ⟨9389337, by rfl⟩ : syracuseStep 25038233 = 18778675) B18778675
theorem B16692155 : Blo 2197435 16692155 := bstep (se 1 (by rfl) ⟨12519116, by rfl⟩ : syracuseStep 16692155 = 25038233) B25038233
theorem B11128103 : Blo 2197435 11128103 := bstep (se 1 (by rfl) ⟨8346077, by rfl⟩ : syracuseStep 11128103 = 16692155) B16692155
theorem B7418735 : Blo 2197435 7418735 := bstep (se 1 (by rfl) ⟨5564051, by rfl⟩ : syracuseStep 7418735 = 11128103) B11128103
theorem B4945823 : Blo 2197435 4945823 := bstep (se 1 (by rfl) ⟨3709367, by rfl⟩ : syracuseStep 4945823 = 7418735) B7418735
theorem B3297215 : Blo 2197435 3297215 := bstep (se 1 (by rfl) ⟨2472911, by rfl⟩ : syracuseStep 3297215 = 4945823) B4945823
theorem B2198143 : Blo 2197435 2198143 := bstep (se 1 (by rfl) ⟨1648607, by rfl⟩ : syracuseStep 2198143 = 3297215) B3297215
theorem B3297221 : Blo 2197435 3297221 := bbase (se 4 (by rfl) ⟨309114, by rfl⟩ : syracuseStep 3297221 = 618229) (by norm_num)
theorem B2198147 : Blo 2197435 2198147 := bstep (se 1 (by rfl) ⟨1648610, by rfl⟩ : syracuseStep 2198147 = 3297221) B3297221
theorem B3709381 : Blo 2197435 3709381 := bbase (se 4 (by rfl) ⟨347754, by rfl⟩ : syracuseStep 3709381 = 695509) (by norm_num)
theorem B4945841 : Blo 2197435 4945841 := bstep (se 2 (by rfl) ⟨1854690, by rfl⟩ : syracuseStep 4945841 = 3709381) B3709381
theorem B3297227 : Blo 2197435 3297227 := bstep (se 1 (by rfl) ⟨2472920, by rfl⟩ : syracuseStep 3297227 = 4945841) B4945841
theorem B2198151 : Blo 2197435 2198151 := bstep (se 1 (by rfl) ⟨1648613, by rfl⟩ : syracuseStep 2198151 = 3297227) B3297227
theorem B2472925 : Blo 2197435 2472925 := bbase (se 3 (by rfl) ⟨463673, by rfl⟩ : syracuseStep 2472925 = 927347) (by norm_num)
theorem B3297233 : Blo 2197435 3297233 := bstep (se 2 (by rfl) ⟨1236462, by rfl⟩ : syracuseStep 3297233 = 2472925) B2472925
theorem B2198155 : Blo 2197435 2198155 := bstep (se 1 (by rfl) ⟨1648616, by rfl⟩ : syracuseStep 2198155 = 3297233) B3297233
theorem B7418789 : Blo 2197435 7418789 := bbase (se 4 (by rfl) ⟨695511, by rfl⟩ : syracuseStep 7418789 = 1391023) (by norm_num)
theorem B4945859 : Blo 2197435 4945859 := bstep (se 1 (by rfl) ⟨3709394, by rfl⟩ : syracuseStep 4945859 = 7418789) B7418789
theorem B3297239 : Blo 2197435 3297239 := bstep (se 1 (by rfl) ⟨2472929, by rfl⟩ : syracuseStep 3297239 = 4945859) B4945859
theorem B2198159 : Blo 2197435 2198159 := bstep (se 1 (by rfl) ⟨1648619, by rfl⟩ : syracuseStep 2198159 = 3297239) B3297239
theorem B3297245 : Blo 2197435 3297245 := bbase (se 3 (by rfl) ⟨618233, by rfl⟩ : syracuseStep 3297245 = 1236467) (by norm_num)
theorem B2198163 : Blo 2197435 2198163 := bstep (se 1 (by rfl) ⟨1648622, by rfl⟩ : syracuseStep 2198163 = 3297245) B3297245
theorem B4945877 : Blo 2197435 4945877 := bbase (se 7 (by rfl) ⟨57959, by rfl⟩ : syracuseStep 4945877 = 115919) (by norm_num)
theorem B3297251 : Blo 2197435 3297251 := bstep (se 1 (by rfl) ⟨2472938, by rfl⟩ : syracuseStep 3297251 = 4945877) B4945877
theorem B2198167 : Blo 2197435 2198167 := bstep (se 1 (by rfl) ⟨1648625, by rfl⟩ : syracuseStep 2198167 = 3297251) B3297251
theorem B7922357 : Blo 2197435 7922357 := bbase (se 5 (by rfl) ⟨371360, by rfl⟩ : syracuseStep 7922357 = 742721) (by norm_num)
theorem B5281571 : Blo 2197435 5281571 := bstep (se 1 (by rfl) ⟨3961178, by rfl⟩ : syracuseStep 5281571 = 7922357) B7922357
theorem B14084189 : Blo 2197435 14084189 := bstep (se 3 (by rfl) ⟨2640785, by rfl⟩ : syracuseStep 14084189 = 5281571) B5281571
theorem B9389459 : Blo 2197435 9389459 := bstep (se 1 (by rfl) ⟨7042094, by rfl⟩ : syracuseStep 9389459 = 14084189) B14084189
theorem B6259639 : Blo 2197435 6259639 := bstep (se 1 (by rfl) ⟨4694729, by rfl⟩ : syracuseStep 6259639 = 9389459) B9389459
theorem B8346185 : Blo 2197435 8346185 := bstep (se 2 (by rfl) ⟨3129819, by rfl⟩ : syracuseStep 8346185 = 6259639) B6259639
theorem B5564123 : Blo 2197435 5564123 := bstep (se 1 (by rfl) ⟨4173092, by rfl⟩ : syracuseStep 5564123 = 8346185) B8346185
theorem B3709415 : Blo 2197435 3709415 := bstep (se 1 (by rfl) ⟨2782061, by rfl⟩ : syracuseStep 3709415 = 5564123) B5564123
theorem B2472943 : Blo 2197435 2472943 := bstep (se 1 (by rfl) ⟨1854707, by rfl⟩ : syracuseStep 2472943 = 3709415) B3709415
theorem B3297257 : Blo 2197435 3297257 := bstep (se 2 (by rfl) ⟨1236471, by rfl⟩ : syracuseStep 3297257 = 2472943) B2472943
theorem B2198171 : Blo 2197435 2198171 := bstep (se 1 (by rfl) ⟨1648628, by rfl⟩ : syracuseStep 2198171 = 3297257) B3297257
theorem B3521053 : Blo 2197435 3521053 := bbase (se 3 (by rfl) ⟨660197, by rfl⟩ : syracuseStep 3521053 = 1320395) (by norm_num)
theorem B18778949 : Blo 2197435 18778949 := bstep (se 4 (by rfl) ⟨1760526, by rfl⟩ : syracuseStep 18778949 = 3521053) B3521053
theorem B12519299 : Blo 2197435 12519299 := bstep (se 1 (by rfl) ⟨9389474, by rfl⟩ : syracuseStep 12519299 = 18778949) B18778949
theorem B8346199 : Blo 2197435 8346199 := bstep (se 1 (by rfl) ⟨6259649, by rfl⟩ : syracuseStep 8346199 = 12519299) B12519299
theorem B11128265 : Blo 2197435 11128265 := bstep (se 2 (by rfl) ⟨4173099, by rfl⟩ : syracuseStep 11128265 = 8346199) B8346199
theorem B7418843 : Blo 2197435 7418843 := bstep (se 1 (by rfl) ⟨5564132, by rfl⟩ : syracuseStep 7418843 = 11128265) B11128265
theorem B4945895 : Blo 2197435 4945895 := bstep (se 1 (by rfl) ⟨3709421, by rfl⟩ : syracuseStep 4945895 = 7418843) B7418843
theorem B3297263 : Blo 2197435 3297263 := bstep (se 1 (by rfl) ⟨2472947, by rfl⟩ : syracuseStep 3297263 = 4945895) B4945895
theorem B2198175 : Blo 2197435 2198175 := bstep (se 1 (by rfl) ⟨1648631, by rfl⟩ : syracuseStep 2198175 = 3297263) B3297263
theorem B3297269 : Blo 2197435 3297269 := bbase (se 5 (by rfl) ⟨154559, by rfl⟩ : syracuseStep 3297269 = 309119) (by norm_num)
theorem B2198179 : Blo 2197435 2198179 := bstep (se 1 (by rfl) ⟨1648634, by rfl⟩ : syracuseStep 2198179 = 3297269) B3297269
theorem B7042133 : Blo 2197435 7042133 := bbase (se 8 (by rfl) ⟨41262, by rfl⟩ : syracuseStep 7042133 = 82525) (by norm_num)
theorem B4694755 : Blo 2197435 4694755 := bstep (se 1 (by rfl) ⟨3521066, by rfl⟩ : syracuseStep 4694755 = 7042133) B7042133
theorem B6259673 : Blo 2197435 6259673 := bstep (se 2 (by rfl) ⟨2347377, by rfl⟩ : syracuseStep 6259673 = 4694755) B4694755
theorem B4173115 : Blo 2197435 4173115 := bstep (se 1 (by rfl) ⟨3129836, by rfl⟩ : syracuseStep 4173115 = 6259673) B6259673
theorem B5564153 : Blo 2197435 5564153 := bstep (se 2 (by rfl) ⟨2086557, by rfl⟩ : syracuseStep 5564153 = 4173115) B4173115
theorem B3709435 : Blo 2197435 3709435 := bstep (se 1 (by rfl) ⟨2782076, by rfl⟩ : syracuseStep 3709435 = 5564153) B5564153
theorem B4945913 : Blo 2197435 4945913 := bstep (se 2 (by rfl) ⟨1854717, by rfl⟩ : syracuseStep 4945913 = 3709435) B3709435
theorem B3297275 : Blo 2197435 3297275 := bstep (se 1 (by rfl) ⟨2472956, by rfl⟩ : syracuseStep 3297275 = 4945913) B4945913
theorem B2198183 : Blo 2197435 2198183 := bstep (se 1 (by rfl) ⟨1648637, by rfl⟩ : syracuseStep 2198183 = 3297275) B3297275
theorem B2472961 : Blo 2197435 2472961 := bbase (se 2 (by rfl) ⟨927360, by rfl⟩ : syracuseStep 2472961 = 1854721) (by norm_num)
theorem B3297281 : Blo 2197435 3297281 := bstep (se 2 (by rfl) ⟨1236480, by rfl⟩ : syracuseStep 3297281 = 2472961) B2472961
theorem B2198187 : Blo 2197435 2198187 := bstep (se 1 (by rfl) ⟨1648640, by rfl⟩ : syracuseStep 2198187 = 3297281) B3297281
theorem B5564173 : Blo 2197435 5564173 := bbase (se 3 (by rfl) ⟨1043282, by rfl⟩ : syracuseStep 5564173 = 2086565) (by norm_num)
theorem B7418897 : Blo 2197435 7418897 := bstep (se 2 (by rfl) ⟨2782086, by rfl⟩ : syracuseStep 7418897 = 5564173) B5564173
theorem B4945931 : Blo 2197435 4945931 := bstep (se 1 (by rfl) ⟨3709448, by rfl⟩ : syracuseStep 4945931 = 7418897) B7418897
theorem B3297287 : Blo 2197435 3297287 := bstep (se 1 (by rfl) ⟨2472965, by rfl⟩ : syracuseStep 3297287 = 4945931) B4945931
theorem B2198191 : Blo 2197435 2198191 := bstep (se 1 (by rfl) ⟨1648643, by rfl⟩ : syracuseStep 2198191 = 3297287) B3297287
theorem B3297293 : Blo 2197435 3297293 := bbase (se 3 (by rfl) ⟨618242, by rfl⟩ : syracuseStep 3297293 = 1236485) (by norm_num)
theorem B2198195 : Blo 2197435 2198195 := bstep (se 1 (by rfl) ⟨1648646, by rfl⟩ : syracuseStep 2198195 = 3297293) B3297293
theorem B4945949 : Blo 2197435 4945949 := bbase (se 3 (by rfl) ⟨927365, by rfl⟩ : syracuseStep 4945949 = 1854731) (by norm_num)
theorem B3297299 : Blo 2197435 3297299 := bstep (se 1 (by rfl) ⟨2472974, by rfl⟩ : syracuseStep 3297299 = 4945949) B4945949
theorem B2198199 : Blo 2197435 2198199 := bstep (se 1 (by rfl) ⟨1648649, by rfl⟩ : syracuseStep 2198199 = 3297299) B3297299
theorem B3709469 : Blo 2197435 3709469 := bbase (se 3 (by rfl) ⟨695525, by rfl⟩ : syracuseStep 3709469 = 1391051) (by norm_num)
theorem B2472979 : Blo 2197435 2472979 := bstep (se 1 (by rfl) ⟨1854734, by rfl⟩ : syracuseStep 2472979 = 3709469) B3709469
theorem B3297305 : Blo 2197435 3297305 := bstep (se 2 (by rfl) ⟨1236489, by rfl⟩ : syracuseStep 3297305 = 2472979) B2472979
theorem B2198203 : Blo 2197435 2198203 := bstep (se 1 (by rfl) ⟨1648652, by rfl⟩ : syracuseStep 2198203 = 3297305) B3297305
theorem B7922485 : Blo 2197435 7922485 := bbase (se 5 (by rfl) ⟨371366, by rfl⟩ : syracuseStep 7922485 = 742733) (by norm_num)
theorem B10563313 : Blo 2197435 10563313 := bstep (se 2 (by rfl) ⟨3961242, by rfl⟩ : syracuseStep 10563313 = 7922485) B7922485
theorem B14084417 : Blo 2197435 14084417 := bstep (se 2 (by rfl) ⟨5281656, by rfl⟩ : syracuseStep 14084417 = 10563313) B10563313
theorem B9389611 : Blo 2197435 9389611 := bstep (se 1 (by rfl) ⟨7042208, by rfl⟩ : syracuseStep 9389611 = 14084417) B14084417
theorem B12519481 : Blo 2197435 12519481 := bstep (se 2 (by rfl) ⟨4694805, by rfl⟩ : syracuseStep 12519481 = 9389611) B9389611
theorem B16692641 : Blo 2197435 16692641 := bstep (se 2 (by rfl) ⟨6259740, by rfl⟩ : syracuseStep 16692641 = 12519481) B12519481
theorem B11128427 : Blo 2197435 11128427 := bstep (se 1 (by rfl) ⟨8346320, by rfl⟩ : syracuseStep 11128427 = 16692641) B16692641
theorem B7418951 : Blo 2197435 7418951 := bstep (se 1 (by rfl) ⟨5564213, by rfl⟩ : syracuseStep 7418951 = 11128427) B11128427
theorem B4945967 : Blo 2197435 4945967 := bstep (se 1 (by rfl) ⟨3709475, by rfl⟩ : syracuseStep 4945967 = 7418951) B7418951
theorem B3297311 : Blo 2197435 3297311 := bstep (se 1 (by rfl) ⟨2472983, by rfl⟩ : syracuseStep 3297311 = 4945967) B4945967
theorem B2198207 : Blo 2197435 2198207 := bstep (se 1 (by rfl) ⟨1648655, by rfl⟩ : syracuseStep 2198207 = 3297311) B3297311
theorem B3297317 : Blo 2197435 3297317 := bbase (se 4 (by rfl) ⟨309123, by rfl⟩ : syracuseStep 3297317 = 618247) (by norm_num)
theorem B2198211 : Blo 2197435 2198211 := bstep (se 1 (by rfl) ⟨1648658, by rfl⟩ : syracuseStep 2198211 = 3297317) B3297317
theorem B2782117 : Blo 2197435 2782117 := bbase (se 4 (by rfl) ⟨260823, by rfl⟩ : syracuseStep 2782117 = 521647) (by norm_num)
theorem B3709489 : Blo 2197435 3709489 := bstep (se 2 (by rfl) ⟨1391058, by rfl⟩ : syracuseStep 3709489 = 2782117) B2782117
theorem B4945985 : Blo 2197435 4945985 := bstep (se 2 (by rfl) ⟨1854744, by rfl⟩ : syracuseStep 4945985 = 3709489) B3709489
theorem B3297323 : Blo 2197435 3297323 := bstep (se 1 (by rfl) ⟨2472992, by rfl⟩ : syracuseStep 3297323 = 4945985) B4945985
theorem B2198215 : Blo 2197435 2198215 := bstep (se 1 (by rfl) ⟨1648661, by rfl⟩ : syracuseStep 2198215 = 3297323) B3297323
theorem B2472997 : Blo 2197435 2472997 := bbase (se 4 (by rfl) ⟨231843, by rfl⟩ : syracuseStep 2472997 = 463687) (by norm_num)
theorem B3297329 : Blo 2197435 3297329 := bstep (se 2 (by rfl) ⟨1236498, by rfl⟩ : syracuseStep 3297329 = 2472997) B2472997
theorem B2198219 : Blo 2197435 2198219 := bstep (se 1 (by rfl) ⟨1648664, by rfl⟩ : syracuseStep 2198219 = 3297329) B3297329
theorem B7042261 : Blo 2197435 7042261 := bbase (se 7 (by rfl) ⟨82526, by rfl⟩ : syracuseStep 7042261 = 165053) (by norm_num)
theorem B9389681 : Blo 2197435 9389681 := bstep (se 2 (by rfl) ⟨3521130, by rfl⟩ : syracuseStep 9389681 = 7042261) B7042261
theorem B6259787 : Blo 2197435 6259787 := bstep (se 1 (by rfl) ⟨4694840, by rfl⟩ : syracuseStep 6259787 = 9389681) B9389681
theorem B4173191 : Blo 2197435 4173191 := bstep (se 1 (by rfl) ⟨3129893, by rfl⟩ : syracuseStep 4173191 = 6259787) B6259787
theorem B2782127 : Blo 2197435 2782127 := bstep (se 1 (by rfl) ⟨2086595, by rfl⟩ : syracuseStep 2782127 = 4173191) B4173191
theorem B7419005 : Blo 2197435 7419005 := bstep (se 3 (by rfl) ⟨1391063, by rfl⟩ : syracuseStep 7419005 = 2782127) B2782127
theorem B4946003 : Blo 2197435 4946003 := bstep (se 1 (by rfl) ⟨3709502, by rfl⟩ : syracuseStep 4946003 = 7419005) B7419005
theorem B3297335 : Blo 2197435 3297335 := bstep (se 1 (by rfl) ⟨2473001, by rfl⟩ : syracuseStep 3297335 = 4946003) B4946003
theorem B2198223 : Blo 2197435 2198223 := bstep (se 1 (by rfl) ⟨1648667, by rfl⟩ : syracuseStep 2198223 = 3297335) B3297335
theorem B3297341 : Blo 2197435 3297341 := bbase (se 3 (by rfl) ⟨618251, by rfl⟩ : syracuseStep 3297341 = 1236503) (by norm_num)
theorem B2198227 : Blo 2197435 2198227 := bstep (se 1 (by rfl) ⟨1648670, by rfl⟩ : syracuseStep 2198227 = 3297341) B3297341
theorem B4946021 : Blo 2197435 4946021 := bbase (se 4 (by rfl) ⟨463689, by rfl⟩ : syracuseStep 4946021 = 927379) (by norm_num)
theorem B3297347 : Blo 2197435 3297347 := bstep (se 1 (by rfl) ⟨2473010, by rfl⟩ : syracuseStep 3297347 = 4946021) B4946021
theorem B2198231 : Blo 2197435 2198231 := bstep (se 1 (by rfl) ⟨1648673, by rfl⟩ : syracuseStep 2198231 = 3297347) B3297347
theorem B5564285 : Blo 2197435 5564285 := bbase (se 3 (by rfl) ⟨1043303, by rfl⟩ : syracuseStep 5564285 = 2086607) (by norm_num)
theorem B3709523 : Blo 2197435 3709523 := bstep (se 1 (by rfl) ⟨2782142, by rfl⟩ : syracuseStep 3709523 = 5564285) B5564285
theorem B2473015 : Blo 2197435 2473015 := bstep (se 1 (by rfl) ⟨1854761, by rfl⟩ : syracuseStep 2473015 = 3709523) B3709523
theorem B3297353 : Blo 2197435 3297353 := bstep (se 2 (by rfl) ⟨1236507, by rfl⟩ : syracuseStep 3297353 = 2473015) B2473015
theorem B2198235 : Blo 2197435 2198235 := bstep (se 1 (by rfl) ⟨1648676, by rfl⟩ : syracuseStep 2198235 = 3297353) B3297353
theorem B4173221 : Blo 2197435 4173221 := bbase (se 4 (by rfl) ⟨391239, by rfl⟩ : syracuseStep 4173221 = 782479) (by norm_num)
theorem B11128589 : Blo 2197435 11128589 := bstep (se 3 (by rfl) ⟨2086610, by rfl⟩ : syracuseStep 11128589 = 4173221) B4173221
theorem B7419059 : Blo 2197435 7419059 := bstep (se 1 (by rfl) ⟨5564294, by rfl⟩ : syracuseStep 7419059 = 11128589) B11128589
theorem B4946039 : Blo 2197435 4946039 := bstep (se 1 (by rfl) ⟨3709529, by rfl⟩ : syracuseStep 4946039 = 7419059) B7419059
theorem B3297359 : Blo 2197435 3297359 := bstep (se 1 (by rfl) ⟨2473019, by rfl⟩ : syracuseStep 3297359 = 4946039) B4946039
theorem B2198239 : Blo 2197435 2198239 := bstep (se 1 (by rfl) ⟨1648679, by rfl⟩ : syracuseStep 2198239 = 3297359) B3297359
theorem B3297365 : Blo 2197435 3297365 := bbase (se 8 (by rfl) ⟨19320, by rfl⟩ : syracuseStep 3297365 = 38641) (by norm_num)
theorem B2198243 : Blo 2197435 2198243 := bstep (se 1 (by rfl) ⟨1648682, by rfl⟩ : syracuseStep 2198243 = 3297365) B3297365
theorem B5941973 : Blo 2197435 5941973 := bbase (se 7 (by rfl) ⟨69632, by rfl⟩ : syracuseStep 5941973 = 139265) (by norm_num)
theorem B3961315 : Blo 2197435 3961315 := bstep (se 1 (by rfl) ⟨2970986, by rfl⟩ : syracuseStep 3961315 = 5941973) B5941973
theorem B21127013 : Blo 2197435 21127013 := bstep (se 4 (by rfl) ⟨1980657, by rfl⟩ : syracuseStep 21127013 = 3961315) B3961315
theorem B14084675 : Blo 2197435 14084675 := bstep (se 1 (by rfl) ⟨10563506, by rfl⟩ : syracuseStep 14084675 = 21127013) B21127013
theorem B9389783 : Blo 2197435 9389783 := bstep (se 1 (by rfl) ⟨7042337, by rfl⟩ : syracuseStep 9389783 = 14084675) B14084675
theorem B6259855 : Blo 2197435 6259855 := bstep (se 1 (by rfl) ⟨4694891, by rfl⟩ : syracuseStep 6259855 = 9389783) B9389783
theorem B8346473 : Blo 2197435 8346473 := bstep (se 2 (by rfl) ⟨3129927, by rfl⟩ : syracuseStep 8346473 = 6259855) B6259855
theorem B5564315 : Blo 2197435 5564315 := bstep (se 1 (by rfl) ⟨4173236, by rfl⟩ : syracuseStep 5564315 = 8346473) B8346473
theorem B3709543 : Blo 2197435 3709543 := bstep (se 1 (by rfl) ⟨2782157, by rfl⟩ : syracuseStep 3709543 = 5564315) B5564315
theorem B4946057 : Blo 2197435 4946057 := bstep (se 2 (by rfl) ⟨1854771, by rfl⟩ : syracuseStep 4946057 = 3709543) B3709543
theorem B3297371 : Blo 2197435 3297371 := bstep (se 1 (by rfl) ⟨2473028, by rfl⟩ : syracuseStep 3297371 = 4946057) B4946057
theorem B2198247 : Blo 2197435 2198247 := bstep (se 1 (by rfl) ⟨1648685, by rfl⟩ : syracuseStep 2198247 = 3297371) B3297371
theorem B2473033 : Blo 2197435 2473033 := bbase (se 2 (by rfl) ⟨927387, by rfl⟩ : syracuseStep 2473033 = 1854775) (by norm_num)
theorem B3297377 : Blo 2197435 3297377 := bstep (se 2 (by rfl) ⟨1236516, by rfl⟩ : syracuseStep 3297377 = 2473033) B2473033
theorem B2198251 : Blo 2197435 2198251 := bstep (se 1 (by rfl) ⟨1648688, by rfl⟩ : syracuseStep 2198251 = 3297377) B3297377
theorem B14084725 : Blo 2197435 14084725 := bbase (se 5 (by rfl) ⟨660221, by rfl⟩ : syracuseStep 14084725 = 1320443) (by norm_num)
theorem B18779633 : Blo 2197435 18779633 := bstep (se 2 (by rfl) ⟨7042362, by rfl⟩ : syracuseStep 18779633 = 14084725) B14084725
theorem B12519755 : Blo 2197435 12519755 := bstep (se 1 (by rfl) ⟨9389816, by rfl⟩ : syracuseStep 12519755 = 18779633) B18779633
theorem B8346503 : Blo 2197435 8346503 := bstep (se 1 (by rfl) ⟨6259877, by rfl⟩ : syracuseStep 8346503 = 12519755) B12519755
theorem B5564335 : Blo 2197435 5564335 := bstep (se 1 (by rfl) ⟨4173251, by rfl⟩ : syracuseStep 5564335 = 8346503) B8346503
theorem B7419113 : Blo 2197435 7419113 := bstep (se 2 (by rfl) ⟨2782167, by rfl⟩ : syracuseStep 7419113 = 5564335) B5564335
theorem B4946075 : Blo 2197435 4946075 := bstep (se 1 (by rfl) ⟨3709556, by rfl⟩ : syracuseStep 4946075 = 7419113) B7419113
theorem B3297383 : Blo 2197435 3297383 := bstep (se 1 (by rfl) ⟨2473037, by rfl⟩ : syracuseStep 3297383 = 4946075) B4946075
theorem B2198255 : Blo 2197435 2198255 := bstep (se 1 (by rfl) ⟨1648691, by rfl⟩ : syracuseStep 2198255 = 3297383) B3297383
theorem B3297389 : Blo 2197435 3297389 := bbase (se 3 (by rfl) ⟨618260, by rfl⟩ : syracuseStep 3297389 = 1236521) (by norm_num)
theorem B2198259 : Blo 2197435 2198259 := bstep (se 1 (by rfl) ⟨1648694, by rfl⟩ : syracuseStep 2198259 = 3297389) B3297389
theorem B4946093 : Blo 2197435 4946093 := bbase (se 3 (by rfl) ⟨927392, by rfl⟩ : syracuseStep 4946093 = 1854785) (by norm_num)
theorem B3297395 : Blo 2197435 3297395 := bstep (se 1 (by rfl) ⟨2473046, by rfl⟩ : syracuseStep 3297395 = 4946093) B4946093
theorem B2198263 : Blo 2197435 2198263 := bstep (se 1 (by rfl) ⟨1648697, by rfl⟩ : syracuseStep 2198263 = 3297395) B3297395
theorem B10563605 : Blo 2197435 10563605 := bbase (se 6 (by rfl) ⟨247584, by rfl⟩ : syracuseStep 10563605 = 495169) (by norm_num)
theorem B7042403 : Blo 2197435 7042403 := bstep (se 1 (by rfl) ⟨5281802, by rfl⟩ : syracuseStep 7042403 = 10563605) B10563605
theorem B4694935 : Blo 2197435 4694935 := bstep (se 1 (by rfl) ⟨3521201, by rfl⟩ : syracuseStep 4694935 = 7042403) B7042403
theorem B6259913 : Blo 2197435 6259913 := bstep (se 2 (by rfl) ⟨2347467, by rfl⟩ : syracuseStep 6259913 = 4694935) B4694935
theorem B4173275 : Blo 2197435 4173275 := bstep (se 1 (by rfl) ⟨3129956, by rfl⟩ : syracuseStep 4173275 = 6259913) B6259913
theorem B2782183 : Blo 2197435 2782183 := bstep (se 1 (by rfl) ⟨2086637, by rfl⟩ : syracuseStep 2782183 = 4173275) B4173275
theorem B3709577 : Blo 2197435 3709577 := bstep (se 2 (by rfl) ⟨1391091, by rfl⟩ : syracuseStep 3709577 = 2782183) B2782183
theorem B2473051 : Blo 2197435 2473051 := bstep (se 1 (by rfl) ⟨1854788, by rfl⟩ : syracuseStep 2473051 = 3709577) B3709577
theorem B3297401 : Blo 2197435 3297401 := bstep (se 2 (by rfl) ⟨1236525, by rfl⟩ : syracuseStep 3297401 = 2473051) B2473051
theorem B2198267 : Blo 2197435 2198267 := bstep (se 1 (by rfl) ⟨1648700, by rfl⟩ : syracuseStep 2198267 = 3297401) B3297401
theorem B2640905 : Blo 2197435 2640905 := bbase (se 2 (by rfl) ⟨990339, by rfl⟩ : syracuseStep 2640905 = 1980679) (by norm_num)
theorem B28169653 : Blo 2197435 28169653 := bstep (se 5 (by rfl) ⟨1320452, by rfl⟩ : syracuseStep 28169653 = 2640905) B2640905
theorem B37559537 : Blo 2197435 37559537 := bstep (se 2 (by rfl) ⟨14084826, by rfl⟩ : syracuseStep 37559537 = 28169653) B28169653
theorem B25039691 : Blo 2197435 25039691 := bstep (se 1 (by rfl) ⟨18779768, by rfl⟩ : syracuseStep 25039691 = 37559537) B37559537
theorem B16693127 : Blo 2197435 16693127 := bstep (se 1 (by rfl) ⟨12519845, by rfl⟩ : syracuseStep 16693127 = 25039691) B25039691
theorem B11128751 : Blo 2197435 11128751 := bstep (se 1 (by rfl) ⟨8346563, by rfl⟩ : syracuseStep 11128751 = 16693127) B16693127
theorem B7419167 : Blo 2197435 7419167 := bstep (se 1 (by rfl) ⟨5564375, by rfl⟩ : syracuseStep 7419167 = 11128751) B11128751
theorem B4946111 : Blo 2197435 4946111 := bstep (se 1 (by rfl) ⟨3709583, by rfl⟩ : syracuseStep 4946111 = 7419167) B7419167
theorem B3297407 : Blo 2197435 3297407 := bstep (se 1 (by rfl) ⟨2473055, by rfl⟩ : syracuseStep 3297407 = 4946111) B4946111
theorem B2198271 : Blo 2197435 2198271 := bstep (se 1 (by rfl) ⟨1648703, by rfl⟩ : syracuseStep 2198271 = 3297407) B3297407
theorem B3297413 : Blo 2197435 3297413 := bbase (se 4 (by rfl) ⟨309132, by rfl⟩ : syracuseStep 3297413 = 618265) (by norm_num)
theorem B2198275 : Blo 2197435 2198275 := bstep (se 1 (by rfl) ⟨1648706, by rfl⟩ : syracuseStep 2198275 = 3297413) B3297413
theorem B3709597 : Blo 2197435 3709597 := bbase (se 3 (by rfl) ⟨695549, by rfl⟩ : syracuseStep 3709597 = 1391099) (by norm_num)
theorem B4946129 : Blo 2197435 4946129 := bstep (se 2 (by rfl) ⟨1854798, by rfl⟩ : syracuseStep 4946129 = 3709597) B3709597
theorem B3297419 : Blo 2197435 3297419 := bstep (se 1 (by rfl) ⟨2473064, by rfl⟩ : syracuseStep 3297419 = 4946129) B4946129
theorem B2198279 : Blo 2197435 2198279 := bstep (se 1 (by rfl) ⟨1648709, by rfl⟩ : syracuseStep 2198279 = 3297419) B3297419
theorem B2473069 : Blo 2197435 2473069 := bbase (se 3 (by rfl) ⟨463700, by rfl⟩ : syracuseStep 2473069 = 927401) (by norm_num)
theorem B3297425 : Blo 2197435 3297425 := bstep (se 2 (by rfl) ⟨1236534, by rfl⟩ : syracuseStep 3297425 = 2473069) B2473069
theorem B2198283 : Blo 2197435 2198283 := bstep (se 1 (by rfl) ⟨1648712, by rfl⟩ : syracuseStep 2198283 = 3297425) B3297425
theorem B7419221 : Blo 2197435 7419221 := bbase (se 13 (by rfl) ⟨1358, by rfl⟩ : syracuseStep 7419221 = 2717) (by norm_num)
theorem B4946147 : Blo 2197435 4946147 := bstep (se 1 (by rfl) ⟨3709610, by rfl⟩ : syracuseStep 4946147 = 7419221) B7419221
theorem B3297431 : Blo 2197435 3297431 := bstep (se 1 (by rfl) ⟨2473073, by rfl⟩ : syracuseStep 3297431 = 4946147) B4946147
theorem B2198287 : Blo 2197435 2198287 := bstep (se 1 (by rfl) ⟨1648715, by rfl⟩ : syracuseStep 2198287 = 3297431) B3297431
theorem B3297437 : Blo 2197435 3297437 := bbase (se 3 (by rfl) ⟨618269, by rfl⟩ : syracuseStep 3297437 = 1236539) (by norm_num)
theorem B2198291 : Blo 2197435 2198291 := bstep (se 1 (by rfl) ⟨1648718, by rfl⟩ : syracuseStep 2198291 = 3297437) B3297437
theorem B4946165 : Blo 2197435 4946165 := bbase (se 5 (by rfl) ⟨231851, by rfl⟩ : syracuseStep 4946165 = 463703) (by norm_num)
theorem B3297443 : Blo 2197435 3297443 := bstep (se 1 (by rfl) ⟨2473082, by rfl⟩ : syracuseStep 3297443 = 4946165) B4946165
theorem B2198295 : Blo 2197435 2198295 := bstep (se 1 (by rfl) ⟨1648721, by rfl⟩ : syracuseStep 2198295 = 3297443) B3297443
theorem B3811549 : Blo 2197435 3811549 := bbase (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) (by norm_num)
theorem B5082065 : Blo 2197435 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B3388043 : Blo 2197435 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B2258695 : Blo 2197435 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B12046373 : Blo 2197435 12046373 := bstep (se 4 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 12046373 = 2258695) B2258695
theorem B8030915 : Blo 2197435 8030915 := bstep (se 1 (by rfl) ⟨6023186, by rfl⟩ : syracuseStep 8030915 = 12046373) B12046373
theorem B5353943 : Blo 2197435 5353943 := bstep (se 1 (by rfl) ⟨4015457, by rfl⟩ : syracuseStep 5353943 = 8030915) B8030915
theorem B14277181 : Blo 2197435 14277181 := bstep (se 3 (by rfl) ⟨2676971, by rfl⟩ : syracuseStep 14277181 = 5353943) B5353943
theorem B19036241 : Blo 2197435 19036241 := bstep (se 2 (by rfl) ⟨7138590, by rfl⟩ : syracuseStep 19036241 = 14277181) B14277181
theorem B12690827 : Blo 2197435 12690827 := bstep (se 1 (by rfl) ⟨9518120, by rfl⟩ : syracuseStep 12690827 = 19036241) B19036241
theorem B8460551 : Blo 2197435 8460551 := bstep (se 1 (by rfl) ⟨6345413, by rfl⟩ : syracuseStep 8460551 = 12690827) B12690827
theorem B5640367 : Blo 2197435 5640367 := bstep (se 1 (by rfl) ⟨4230275, by rfl⟩ : syracuseStep 5640367 = 8460551) B8460551
theorem B7520489 : Blo 2197435 7520489 := bstep (se 2 (by rfl) ⟨2820183, by rfl⟩ : syracuseStep 7520489 = 5640367) B5640367
theorem B5013659 : Blo 2197435 5013659 := bstep (se 1 (by rfl) ⟨3760244, by rfl⟩ : syracuseStep 5013659 = 7520489) B7520489
theorem B3342439 : Blo 2197435 3342439 := bstep (se 1 (by rfl) ⟨2506829, by rfl⟩ : syracuseStep 3342439 = 5013659) B5013659
theorem B4456585 : Blo 2197435 4456585 := bstep (se 2 (by rfl) ⟨1671219, by rfl⟩ : syracuseStep 4456585 = 3342439) B3342439
theorem B23768453 : Blo 2197435 23768453 := bstep (se 4 (by rfl) ⟨2228292, by rfl⟩ : syracuseStep 23768453 = 4456585) B4456585
theorem B15845635 : Blo 2197435 15845635 := bstep (se 1 (by rfl) ⟨11884226, by rfl⟩ : syracuseStep 15845635 = 23768453) B23768453
theorem B21127513 : Blo 2197435 21127513 := bstep (se 2 (by rfl) ⟨7922817, by rfl⟩ : syracuseStep 21127513 = 15845635) B15845635
theorem B28170017 : Blo 2197435 28170017 := bstep (se 2 (by rfl) ⟨10563756, by rfl⟩ : syracuseStep 28170017 = 21127513) B21127513
theorem B18780011 : Blo 2197435 18780011 := bstep (se 1 (by rfl) ⟨14085008, by rfl⟩ : syracuseStep 18780011 = 28170017) B28170017
theorem B12520007 : Blo 2197435 12520007 := bstep (se 1 (by rfl) ⟨9390005, by rfl⟩ : syracuseStep 12520007 = 18780011) B18780011
theorem B8346671 : Blo 2197435 8346671 := bstep (se 1 (by rfl) ⟨6260003, by rfl⟩ : syracuseStep 8346671 = 12520007) B12520007
theorem B5564447 : Blo 2197435 5564447 := bstep (se 1 (by rfl) ⟨4173335, by rfl⟩ : syracuseStep 5564447 = 8346671) B8346671
theorem B3709631 : Blo 2197435 3709631 := bstep (se 1 (by rfl) ⟨2782223, by rfl⟩ : syracuseStep 3709631 = 5564447) B5564447
theorem B2473087 : Blo 2197435 2473087 := bstep (se 1 (by rfl) ⟨1854815, by rfl⟩ : syracuseStep 2473087 = 3709631) B3709631
theorem B3297449 : Blo 2197435 3297449 := bstep (se 2 (by rfl) ⟨1236543, by rfl⟩ : syracuseStep 3297449 = 2473087) B2473087
theorem B2198299 : Blo 2197435 2198299 := bstep (se 1 (by rfl) ⟨1648724, by rfl⟩ : syracuseStep 2198299 = 3297449) B3297449
theorem B7042517 : Blo 2197435 7042517 := bbase (se 7 (by rfl) ⟨82529, by rfl⟩ : syracuseStep 7042517 = 165059) (by norm_num)
theorem B4695011 : Blo 2197435 4695011 := bstep (se 1 (by rfl) ⟨3521258, by rfl⟩ : syracuseStep 4695011 = 7042517) B7042517
theorem B3130007 : Blo 2197435 3130007 := bstep (se 1 (by rfl) ⟨2347505, by rfl⟩ : syracuseStep 3130007 = 4695011) B4695011
theorem B8346685 : Blo 2197435 8346685 := bstep (se 3 (by rfl) ⟨1565003, by rfl⟩ : syracuseStep 8346685 = 3130007) B3130007
theorem B11128913 : Blo 2197435 11128913 := bstep (se 2 (by rfl) ⟨4173342, by rfl⟩ : syracuseStep 11128913 = 8346685) B8346685
theorem B7419275 : Blo 2197435 7419275 := bstep (se 1 (by rfl) ⟨5564456, by rfl⟩ : syracuseStep 7419275 = 11128913) B11128913
theorem B4946183 : Blo 2197435 4946183 := bstep (se 1 (by rfl) ⟨3709637, by rfl⟩ : syracuseStep 4946183 = 7419275) B7419275
theorem B3297455 : Blo 2197435 3297455 := bstep (se 1 (by rfl) ⟨2473091, by rfl⟩ : syracuseStep 3297455 = 4946183) B4946183
theorem B2198303 : Blo 2197435 2198303 := bstep (se 1 (by rfl) ⟨1648727, by rfl⟩ : syracuseStep 2198303 = 3297455) B3297455
theorem B3297461 : Blo 2197435 3297461 := bbase (se 5 (by rfl) ⟨154568, by rfl⟩ : syracuseStep 3297461 = 309137) (by norm_num)
theorem B2198307 : Blo 2197435 2198307 := bstep (se 1 (by rfl) ⟨1648730, by rfl⟩ : syracuseStep 2198307 = 3297461) B3297461
theorem B5564477 : Blo 2197435 5564477 := bbase (se 3 (by rfl) ⟨1043339, by rfl⟩ : syracuseStep 5564477 = 2086679) (by norm_num)
theorem B3709651 : Blo 2197435 3709651 := bstep (se 1 (by rfl) ⟨2782238, by rfl⟩ : syracuseStep 3709651 = 5564477) B5564477
theorem B4946201 : Blo 2197435 4946201 := bstep (se 2 (by rfl) ⟨1854825, by rfl⟩ : syracuseStep 4946201 = 3709651) B3709651
theorem B3297467 : Blo 2197435 3297467 := bstep (se 1 (by rfl) ⟨2473100, by rfl⟩ : syracuseStep 3297467 = 4946201) B4946201
theorem B2198311 : Blo 2197435 2198311 := bstep (se 1 (by rfl) ⟨1648733, by rfl⟩ : syracuseStep 2198311 = 3297467) B3297467
theorem B2473105 : Blo 2197435 2473105 := bbase (se 2 (by rfl) ⟨927414, by rfl⟩ : syracuseStep 2473105 = 1854829) (by norm_num)
theorem B3297473 : Blo 2197435 3297473 := bstep (se 2 (by rfl) ⟨1236552, by rfl⟩ : syracuseStep 3297473 = 2473105) B2473105
theorem B2198315 : Blo 2197435 2198315 := bstep (se 1 (by rfl) ⟨1648736, by rfl⟩ : syracuseStep 2198315 = 3297473) B3297473
theorem B4173373 : Blo 2197435 4173373 := bbase (se 3 (by rfl) ⟨782507, by rfl⟩ : syracuseStep 4173373 = 1565015) (by norm_num)
theorem B5564497 : Blo 2197435 5564497 := bstep (se 2 (by rfl) ⟨2086686, by rfl⟩ : syracuseStep 5564497 = 4173373) B4173373
theorem B7419329 : Blo 2197435 7419329 := bstep (se 2 (by rfl) ⟨2782248, by rfl⟩ : syracuseStep 7419329 = 5564497) B5564497
theorem B4946219 : Blo 2197435 4946219 := bstep (se 1 (by rfl) ⟨3709664, by rfl⟩ : syracuseStep 4946219 = 7419329) B7419329
theorem B3297479 : Blo 2197435 3297479 := bstep (se 1 (by rfl) ⟨2473109, by rfl⟩ : syracuseStep 3297479 = 4946219) B4946219
theorem B2198319 : Blo 2197435 2198319 := bstep (se 1 (by rfl) ⟨1648739, by rfl⟩ : syracuseStep 2198319 = 3297479) B3297479
theorem B3297485 : Blo 2197435 3297485 := bbase (se 3 (by rfl) ⟨618278, by rfl⟩ : syracuseStep 3297485 = 1236557) (by norm_num)
theorem B2198323 : Blo 2197435 2198323 := bstep (se 1 (by rfl) ⟨1648742, by rfl⟩ : syracuseStep 2198323 = 3297485) B3297485
theorem B4946237 : Blo 2197435 4946237 := bbase (se 3 (by rfl) ⟨927419, by rfl⟩ : syracuseStep 4946237 = 1854839) (by norm_num)
theorem B3297491 : Blo 2197435 3297491 := bstep (se 1 (by rfl) ⟨2473118, by rfl⟩ : syracuseStep 3297491 = 4946237) B4946237
theorem B2198327 : Blo 2197435 2198327 := bstep (se 1 (by rfl) ⟨1648745, by rfl⟩ : syracuseStep 2198327 = 3297491) B3297491
theorem B3709685 : Blo 2197435 3709685 := bbase (se 5 (by rfl) ⟨173891, by rfl⟩ : syracuseStep 3709685 = 347783) (by norm_num)
theorem B2473123 : Blo 2197435 2473123 := bstep (se 1 (by rfl) ⟨1854842, by rfl⟩ : syracuseStep 2473123 = 3709685) B3709685
theorem B3297497 : Blo 2197435 3297497 := bstep (se 2 (by rfl) ⟨1236561, by rfl⟩ : syracuseStep 3297497 = 2473123) B2473123
theorem B2198331 : Blo 2197435 2198331 := bstep (se 1 (by rfl) ⟨1648748, by rfl⟩ : syracuseStep 2198331 = 3297497) B3297497
theorem B2228329 : Blo 2197435 2228329 := bbase (se 2 (by rfl) ⟨835623, by rfl⟩ : syracuseStep 2228329 = 1671247) (by norm_num)
theorem B11884421 : Blo 2197435 11884421 := bstep (se 4 (by rfl) ⟨1114164, by rfl⟩ : syracuseStep 11884421 = 2228329) B2228329
theorem B7922947 : Blo 2197435 7922947 := bstep (se 1 (by rfl) ⟨5942210, by rfl⟩ : syracuseStep 7922947 = 11884421) B11884421
theorem B10563929 : Blo 2197435 10563929 := bstep (se 2 (by rfl) ⟨3961473, by rfl⟩ : syracuseStep 10563929 = 7922947) B7922947
theorem B7042619 : Blo 2197435 7042619 := bstep (se 1 (by rfl) ⟨5281964, by rfl⟩ : syracuseStep 7042619 = 10563929) B10563929
theorem B4695079 : Blo 2197435 4695079 := bstep (se 1 (by rfl) ⟨3521309, by rfl⟩ : syracuseStep 4695079 = 7042619) B7042619
theorem B6260105 : Blo 2197435 6260105 := bstep (se 2 (by rfl) ⟨2347539, by rfl⟩ : syracuseStep 6260105 = 4695079) B4695079
theorem B16693613 : Blo 2197435 16693613 := bstep (se 3 (by rfl) ⟨3130052, by rfl⟩ : syracuseStep 16693613 = 6260105) B6260105
theorem B11129075 : Blo 2197435 11129075 := bstep (se 1 (by rfl) ⟨8346806, by rfl⟩ : syracuseStep 11129075 = 16693613) B16693613
theorem B7419383 : Blo 2197435 7419383 := bstep (se 1 (by rfl) ⟨5564537, by rfl⟩ : syracuseStep 7419383 = 11129075) B11129075
theorem B4946255 : Blo 2197435 4946255 := bstep (se 1 (by rfl) ⟨3709691, by rfl⟩ : syracuseStep 4946255 = 7419383) B7419383
theorem B3297503 : Blo 2197435 3297503 := bstep (se 1 (by rfl) ⟨2473127, by rfl⟩ : syracuseStep 3297503 = 4946255) B4946255
theorem B2198335 : Blo 2197435 2198335 := bstep (se 1 (by rfl) ⟨1648751, by rfl⟩ : syracuseStep 2198335 = 3297503) B3297503
theorem B3297509 : Blo 2197435 3297509 := bbase (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) (by norm_num)
theorem B2198339 : Blo 2197435 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B2971117 : Blo 2197435 2971117 := bbase (se 3 (by rfl) ⟨557084, by rfl⟩ : syracuseStep 2971117 = 1114169) (by norm_num)
theorem B3961489 : Blo 2197435 3961489 := bstep (se 2 (by rfl) ⟨1485558, by rfl⟩ : syracuseStep 3961489 = 2971117) B2971117
theorem B5281985 : Blo 2197435 5281985 := bstep (se 2 (by rfl) ⟨1980744, by rfl⟩ : syracuseStep 5281985 = 3961489) B3961489
theorem B3521323 : Blo 2197435 3521323 := bstep (se 1 (by rfl) ⟨2640992, by rfl⟩ : syracuseStep 3521323 = 5281985) B5281985
theorem B4695097 : Blo 2197435 4695097 := bstep (se 2 (by rfl) ⟨1760661, by rfl⟩ : syracuseStep 4695097 = 3521323) B3521323
theorem B6260129 : Blo 2197435 6260129 := bstep (se 2 (by rfl) ⟨2347548, by rfl⟩ : syracuseStep 6260129 = 4695097) B4695097
theorem B4173419 : Blo 2197435 4173419 := bstep (se 1 (by rfl) ⟨3130064, by rfl⟩ : syracuseStep 4173419 = 6260129) B6260129
theorem B2782279 : Blo 2197435 2782279 := bstep (se 1 (by rfl) ⟨2086709, by rfl⟩ : syracuseStep 2782279 = 4173419) B4173419
theorem B3709705 : Blo 2197435 3709705 := bstep (se 2 (by rfl) ⟨1391139, by rfl⟩ : syracuseStep 3709705 = 2782279) B2782279
theorem B4946273 : Blo 2197435 4946273 := bstep (se 2 (by rfl) ⟨1854852, by rfl⟩ : syracuseStep 4946273 = 3709705) B3709705
theorem B3297515 : Blo 2197435 3297515 := bstep (se 1 (by rfl) ⟨2473136, by rfl⟩ : syracuseStep 3297515 = 4946273) B4946273
theorem B2198343 : Blo 2197435 2198343 := bstep (se 1 (by rfl) ⟨1648757, by rfl⟩ : syracuseStep 2198343 = 3297515) B3297515
theorem B2473141 : Blo 2197435 2473141 := bbase (se 5 (by rfl) ⟨115928, by rfl⟩ : syracuseStep 2473141 = 231857) (by norm_num)
theorem B3297521 : Blo 2197435 3297521 := bstep (se 2 (by rfl) ⟨1236570, by rfl⟩ : syracuseStep 3297521 = 2473141) B2473141
theorem B2198347 : Blo 2197435 2198347 := bstep (se 1 (by rfl) ⟨1648760, by rfl⟩ : syracuseStep 2198347 = 3297521) B3297521
theorem B2782289 : Blo 2197435 2782289 := bbase (se 2 (by rfl) ⟨1043358, by rfl⟩ : syracuseStep 2782289 = 2086717) (by norm_num)
theorem B7419437 : Blo 2197435 7419437 := bstep (se 3 (by rfl) ⟨1391144, by rfl⟩ : syracuseStep 7419437 = 2782289) B2782289
theorem B4946291 : Blo 2197435 4946291 := bstep (se 1 (by rfl) ⟨3709718, by rfl⟩ : syracuseStep 4946291 = 7419437) B7419437
theorem B3297527 : Blo 2197435 3297527 := bstep (se 1 (by rfl) ⟨2473145, by rfl⟩ : syracuseStep 3297527 = 4946291) B4946291
theorem B2198351 : Blo 2197435 2198351 := bstep (se 1 (by rfl) ⟨1648763, by rfl⟩ : syracuseStep 2198351 = 3297527) B3297527
theorem B3297533 : Blo 2197435 3297533 := bbase (se 3 (by rfl) ⟨618287, by rfl⟩ : syracuseStep 3297533 = 1236575) (by norm_num)
theorem B2198355 : Blo 2197435 2198355 := bstep (se 1 (by rfl) ⟨1648766, by rfl⟩ : syracuseStep 2198355 = 3297533) B3297533
theorem B4946309 : Blo 2197435 4946309 := bbase (se 4 (by rfl) ⟨463716, by rfl⟩ : syracuseStep 4946309 = 927433) (by norm_num)
theorem B3297539 : Blo 2197435 3297539 := bstep (se 1 (by rfl) ⟨2473154, by rfl⟩ : syracuseStep 3297539 = 4946309) B4946309
theorem B2198359 : Blo 2197435 2198359 := bstep (se 1 (by rfl) ⟨1648769, by rfl⟩ : syracuseStep 2198359 = 3297539) B3297539
theorem B3130093 : Blo 2197435 3130093 := bbase (se 3 (by rfl) ⟨586892, by rfl⟩ : syracuseStep 3130093 = 1173785) (by norm_num)
theorem B4173457 : Blo 2197435 4173457 := bstep (se 2 (by rfl) ⟨1565046, by rfl⟩ : syracuseStep 4173457 = 3130093) B3130093
theorem B5564609 : Blo 2197435 5564609 := bstep (se 2 (by rfl) ⟨2086728, by rfl⟩ : syracuseStep 5564609 = 4173457) B4173457
theorem B3709739 : Blo 2197435 3709739 := bstep (se 1 (by rfl) ⟨2782304, by rfl⟩ : syracuseStep 3709739 = 5564609) B5564609
theorem B2473159 : Blo 2197435 2473159 := bstep (se 1 (by rfl) ⟨1854869, by rfl⟩ : syracuseStep 2473159 = 3709739) B3709739
theorem B3297545 : Blo 2197435 3297545 := bstep (se 2 (by rfl) ⟨1236579, by rfl⟩ : syracuseStep 3297545 = 2473159) B2473159
theorem B2198363 : Blo 2197435 2198363 := bstep (se 1 (by rfl) ⟨1648772, by rfl⟩ : syracuseStep 2198363 = 3297545) B3297545
theorem B11129237 : Blo 2197435 11129237 := bbase (se 6 (by rfl) ⟨260841, by rfl⟩ : syracuseStep 11129237 = 521683) (by norm_num)
theorem B7419491 : Blo 2197435 7419491 := bstep (se 1 (by rfl) ⟨5564618, by rfl⟩ : syracuseStep 7419491 = 11129237) B11129237
theorem B4946327 : Blo 2197435 4946327 := bstep (se 1 (by rfl) ⟨3709745, by rfl⟩ : syracuseStep 4946327 = 7419491) B7419491
theorem B3297551 : Blo 2197435 3297551 := bstep (se 1 (by rfl) ⟨2473163, by rfl⟩ : syracuseStep 3297551 = 4946327) B4946327
theorem B2198367 : Blo 2197435 2198367 := bstep (se 1 (by rfl) ⟨1648775, by rfl⟩ : syracuseStep 2198367 = 3297551) B3297551
theorem B3297557 : Blo 2197435 3297557 := bbase (se 6 (by rfl) ⟨77286, by rfl⟩ : syracuseStep 3297557 = 154573) (by norm_num)
theorem B2198371 : Blo 2197435 2198371 := bstep (se 1 (by rfl) ⟨1648778, by rfl⟩ : syracuseStep 2198371 = 3297557) B3297557
theorem B6685109 : Blo 2197435 6685109 := bbase (se 5 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 6685109 = 626729) (by norm_num)
theorem B4456739 : Blo 2197435 4456739 := bstep (se 1 (by rfl) ⟨3342554, by rfl⟩ : syracuseStep 4456739 = 6685109) B6685109
theorem B11884637 : Blo 2197435 11884637 := bstep (se 3 (by rfl) ⟨2228369, by rfl⟩ : syracuseStep 11884637 = 4456739) B4456739
theorem B7923091 : Blo 2197435 7923091 := bstep (se 1 (by rfl) ⟨5942318, by rfl⟩ : syracuseStep 7923091 = 11884637) B11884637
theorem B10564121 : Blo 2197435 10564121 := bstep (se 2 (by rfl) ⟨3961545, by rfl⟩ : syracuseStep 10564121 = 7923091) B7923091
theorem B28170989 : Blo 2197435 28170989 := bstep (se 3 (by rfl) ⟨5282060, by rfl⟩ : syracuseStep 28170989 = 10564121) B10564121
theorem B18780659 : Blo 2197435 18780659 := bstep (se 1 (by rfl) ⟨14085494, by rfl⟩ : syracuseStep 18780659 = 28170989) B28170989
theorem B12520439 : Blo 2197435 12520439 := bstep (se 1 (by rfl) ⟨9390329, by rfl⟩ : syracuseStep 12520439 = 18780659) B18780659
theorem B8346959 : Blo 2197435 8346959 := bstep (se 1 (by rfl) ⟨6260219, by rfl⟩ : syracuseStep 8346959 = 12520439) B12520439
theorem B5564639 : Blo 2197435 5564639 := bstep (se 1 (by rfl) ⟨4173479, by rfl⟩ : syracuseStep 5564639 = 8346959) B8346959
theorem B3709759 : Blo 2197435 3709759 := bstep (se 1 (by rfl) ⟨2782319, by rfl⟩ : syracuseStep 3709759 = 5564639) B5564639
theorem B4946345 : Blo 2197435 4946345 := bstep (se 2 (by rfl) ⟨1854879, by rfl⟩ : syracuseStep 4946345 = 3709759) B3709759
theorem B3297563 : Blo 2197435 3297563 := bstep (se 1 (by rfl) ⟨2473172, by rfl⟩ : syracuseStep 3297563 = 4946345) B4946345
theorem B2198375 : Blo 2197435 2198375 := bstep (se 1 (by rfl) ⟨1648781, by rfl⟩ : syracuseStep 2198375 = 3297563) B3297563
theorem B2473177 : Blo 2197435 2473177 := bbase (se 2 (by rfl) ⟨927441, by rfl⟩ : syracuseStep 2473177 = 1854883) (by norm_num)
theorem B3297569 : Blo 2197435 3297569 := bstep (se 2 (by rfl) ⟨1236588, by rfl⟩ : syracuseStep 3297569 = 2473177) B2473177
theorem B2198379 : Blo 2197435 2198379 := bstep (se 1 (by rfl) ⟨1648784, by rfl⟩ : syracuseStep 2198379 = 3297569) B3297569
theorem B4456757 : Blo 2197435 4456757 := bbase (se 5 (by rfl) ⟨208910, by rfl⟩ : syracuseStep 4456757 = 417821) (by norm_num)
theorem B2971171 : Blo 2197435 2971171 := bstep (se 1 (by rfl) ⟨2228378, by rfl⟩ : syracuseStep 2971171 = 4456757) B4456757
theorem B3961561 : Blo 2197435 3961561 := bstep (se 2 (by rfl) ⟨1485585, by rfl⟩ : syracuseStep 3961561 = 2971171) B2971171
theorem B5282081 : Blo 2197435 5282081 := bstep (se 2 (by rfl) ⟨1980780, by rfl⟩ : syracuseStep 5282081 = 3961561) B3961561
theorem B3521387 : Blo 2197435 3521387 := bstep (se 1 (by rfl) ⟨2641040, by rfl⟩ : syracuseStep 3521387 = 5282081) B5282081
theorem B2347591 : Blo 2197435 2347591 := bstep (se 1 (by rfl) ⟨1760693, by rfl⟩ : syracuseStep 2347591 = 3521387) B3521387
theorem B3130121 : Blo 2197435 3130121 := bstep (se 2 (by rfl) ⟨1173795, by rfl⟩ : syracuseStep 3130121 = 2347591) B2347591
theorem B8346989 : Blo 2197435 8346989 := bstep (se 3 (by rfl) ⟨1565060, by rfl⟩ : syracuseStep 8346989 = 3130121) B3130121
theorem B5564659 : Blo 2197435 5564659 := bstep (se 1 (by rfl) ⟨4173494, by rfl⟩ : syracuseStep 5564659 = 8346989) B8346989
theorem B7419545 : Blo 2197435 7419545 := bstep (se 2 (by rfl) ⟨2782329, by rfl⟩ : syracuseStep 7419545 = 5564659) B5564659
theorem B4946363 : Blo 2197435 4946363 := bstep (se 1 (by rfl) ⟨3709772, by rfl⟩ : syracuseStep 4946363 = 7419545) B7419545
theorem B3297575 : Blo 2197435 3297575 := bstep (se 1 (by rfl) ⟨2473181, by rfl⟩ : syracuseStep 3297575 = 4946363) B4946363
theorem B2198383 : Blo 2197435 2198383 := bstep (se 1 (by rfl) ⟨1648787, by rfl⟩ : syracuseStep 2198383 = 3297575) B3297575
theorem B3297581 : Blo 2197435 3297581 := bbase (se 3 (by rfl) ⟨618296, by rfl⟩ : syracuseStep 3297581 = 1236593) (by norm_num)
theorem B2198387 : Blo 2197435 2198387 := bstep (se 1 (by rfl) ⟨1648790, by rfl⟩ : syracuseStep 2198387 = 3297581) B3297581
theorem B4946381 : Blo 2197435 4946381 := bbase (se 3 (by rfl) ⟨927446, by rfl⟩ : syracuseStep 4946381 = 1854893) (by norm_num)
theorem B3297587 : Blo 2197435 3297587 := bstep (se 1 (by rfl) ⟨2473190, by rfl⟩ : syracuseStep 3297587 = 4946381) B4946381
theorem B2198391 : Blo 2197435 2198391 := bstep (se 1 (by rfl) ⟨1648793, by rfl⟩ : syracuseStep 2198391 = 3297587) B3297587
theorem B2782345 : Blo 2197435 2782345 := bbase (se 2 (by rfl) ⟨1043379, by rfl⟩ : syracuseStep 2782345 = 2086759) (by norm_num)
theorem B3709793 : Blo 2197435 3709793 := bstep (se 2 (by rfl) ⟨1391172, by rfl⟩ : syracuseStep 3709793 = 2782345) B2782345
theorem B2473195 : Blo 2197435 2473195 := bstep (se 1 (by rfl) ⟨1854896, by rfl⟩ : syracuseStep 2473195 = 3709793) B3709793
theorem B3297593 : Blo 2197435 3297593 := bstep (se 2 (by rfl) ⟨1236597, by rfl⟩ : syracuseStep 3297593 = 2473195) B2473195
theorem B2198395 : Blo 2197435 2198395 := bstep (se 1 (by rfl) ⟨1648796, by rfl⟩ : syracuseStep 2198395 = 3297593) B3297593
theorem B2677093 : Blo 2197435 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B14277829 : Blo 2197435 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B19037105 : Blo 2197435 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B12691403 : Blo 2197435 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B8460935 : Blo 2197435 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B5640623 : Blo 2197435 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B3760415 : Blo 2197435 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B2506943 : Blo 2197435 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B6685181 : Blo 2197435 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B4456787 : Blo 2197435 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B47539061 : Blo 2197435 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B31692707 : Blo 2197435 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B21128471 : Blo 2197435 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B14085647 : Blo 2197435 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B9390431 : Blo 2197435 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B25041149 : Blo 2197435 25041149 := bstep (se 3 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 25041149 = 9390431) B9390431
theorem B16694099 : Blo 2197435 16694099 := bstep (se 1 (by rfl) ⟨12520574, by rfl⟩ : syracuseStep 16694099 = 25041149) B25041149
theorem B11129399 : Blo 2197435 11129399 := bstep (se 1 (by rfl) ⟨8347049, by rfl⟩ : syracuseStep 11129399 = 16694099) B16694099
theorem B7419599 : Blo 2197435 7419599 := bstep (se 1 (by rfl) ⟨5564699, by rfl⟩ : syracuseStep 7419599 = 11129399) B11129399
theorem B4946399 : Blo 2197435 4946399 := bstep (se 1 (by rfl) ⟨3709799, by rfl⟩ : syracuseStep 4946399 = 7419599) B7419599
theorem B3297599 : Blo 2197435 3297599 := bstep (se 1 (by rfl) ⟨2473199, by rfl⟩ : syracuseStep 3297599 = 4946399) B4946399
theorem B2198399 : Blo 2197435 2198399 := bstep (se 1 (by rfl) ⟨1648799, by rfl⟩ : syracuseStep 2198399 = 3297599) B3297599
theorem B3297605 : Blo 2197435 3297605 := bbase (se 4 (by rfl) ⟨309150, by rfl⟩ : syracuseStep 3297605 = 618301) (by norm_num)
theorem B2198403 : Blo 2197435 2198403 := bstep (se 1 (by rfl) ⟨1648802, by rfl⟩ : syracuseStep 2198403 = 3297605) B3297605
theorem B3709813 : Blo 2197435 3709813 := bbase (se 5 (by rfl) ⟨173897, by rfl⟩ : syracuseStep 3709813 = 347795) (by norm_num)
theorem B4946417 : Blo 2197435 4946417 := bstep (se 2 (by rfl) ⟨1854906, by rfl⟩ : syracuseStep 4946417 = 3709813) B3709813
theorem B3297611 : Blo 2197435 3297611 := bstep (se 1 (by rfl) ⟨2473208, by rfl⟩ : syracuseStep 3297611 = 4946417) B4946417
theorem B2198407 : Blo 2197435 2198407 := bstep (se 1 (by rfl) ⟨1648805, by rfl⟩ : syracuseStep 2198407 = 3297611) B3297611
theorem B2473213 : Blo 2197435 2473213 := bbase (se 3 (by rfl) ⟨463727, by rfl⟩ : syracuseStep 2473213 = 927455) (by norm_num)
theorem B3297617 : Blo 2197435 3297617 := bstep (se 2 (by rfl) ⟨1236606, by rfl⟩ : syracuseStep 3297617 = 2473213) B2473213
theorem B2198411 : Blo 2197435 2198411 := bstep (se 1 (by rfl) ⟨1648808, by rfl⟩ : syracuseStep 2198411 = 3297617) B3297617
theorem B7419653 : Blo 2197435 7419653 := bbase (se 4 (by rfl) ⟨695592, by rfl⟩ : syracuseStep 7419653 = 1391185) (by norm_num)
theorem B4946435 : Blo 2197435 4946435 := bstep (se 1 (by rfl) ⟨3709826, by rfl⟩ : syracuseStep 4946435 = 7419653) B7419653
theorem B3297623 : Blo 2197435 3297623 := bstep (se 1 (by rfl) ⟨2473217, by rfl⟩ : syracuseStep 3297623 = 4946435) B4946435
theorem B2198415 : Blo 2197435 2198415 := bstep (se 1 (by rfl) ⟨1648811, by rfl⟩ : syracuseStep 2198415 = 3297623) B3297623
theorem B3297629 : Blo 2197435 3297629 := bbase (se 3 (by rfl) ⟨618305, by rfl⟩ : syracuseStep 3297629 = 1236611) (by norm_num)
theorem B2198419 : Blo 2197435 2198419 := bstep (se 1 (by rfl) ⟨1648814, by rfl⟩ : syracuseStep 2198419 = 3297629) B3297629
theorem B4946453 : Blo 2197435 4946453 := bbase (se 6 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 4946453 = 231865) (by norm_num)
theorem B3297635 : Blo 2197435 3297635 := bstep (se 1 (by rfl) ⟨2473226, by rfl⟩ : syracuseStep 3297635 = 4946453) B4946453
theorem B2198423 : Blo 2197435 2198423 := bstep (se 1 (by rfl) ⟨1648817, by rfl⟩ : syracuseStep 2198423 = 3297635) B3297635
theorem B8347157 : Blo 2197435 8347157 := bbase (se 6 (by rfl) ⟨195636, by rfl⟩ : syracuseStep 8347157 = 391273) (by norm_num)
theorem B5564771 : Blo 2197435 5564771 := bstep (se 1 (by rfl) ⟨4173578, by rfl⟩ : syracuseStep 5564771 = 8347157) B8347157
theorem B3709847 : Blo 2197435 3709847 := bstep (se 1 (by rfl) ⟨2782385, by rfl⟩ : syracuseStep 3709847 = 5564771) B5564771
theorem B2473231 : Blo 2197435 2473231 := bstep (se 1 (by rfl) ⟨1854923, by rfl⟩ : syracuseStep 2473231 = 3709847) B3709847
theorem B3297641 : Blo 2197435 3297641 := bstep (se 2 (by rfl) ⟨1236615, by rfl⟩ : syracuseStep 3297641 = 2473231) B2473231
theorem B2198427 : Blo 2197435 2198427 := bstep (se 1 (by rfl) ⟨1648820, by rfl⟩ : syracuseStep 2198427 = 3297641) B3297641
theorem B12520757 : Blo 2197435 12520757 := bbase (se 5 (by rfl) ⟨586910, by rfl⟩ : syracuseStep 12520757 = 1173821) (by norm_num)
theorem B8347171 : Blo 2197435 8347171 := bstep (se 1 (by rfl) ⟨6260378, by rfl⟩ : syracuseStep 8347171 = 12520757) B12520757
theorem B11129561 : Blo 2197435 11129561 := bstep (se 2 (by rfl) ⟨4173585, by rfl⟩ : syracuseStep 11129561 = 8347171) B8347171
theorem B7419707 : Blo 2197435 7419707 := bstep (se 1 (by rfl) ⟨5564780, by rfl⟩ : syracuseStep 7419707 = 11129561) B11129561
theorem B4946471 : Blo 2197435 4946471 := bstep (se 1 (by rfl) ⟨3709853, by rfl⟩ : syracuseStep 4946471 = 7419707) B7419707
theorem B3297647 : Blo 2197435 3297647 := bstep (se 1 (by rfl) ⟨2473235, by rfl⟩ : syracuseStep 3297647 = 4946471) B4946471
theorem B2198431 : Blo 2197435 2198431 := bstep (se 1 (by rfl) ⟨1648823, by rfl⟩ : syracuseStep 2198431 = 3297647) B3297647
theorem B3297653 : Blo 2197435 3297653 := bbase (se 5 (by rfl) ⟨154577, by rfl⟩ : syracuseStep 3297653 = 309155) (by norm_num)
theorem B2198435 : Blo 2197435 2198435 := bstep (se 1 (by rfl) ⟨1648826, by rfl⟩ : syracuseStep 2198435 = 3297653) B3297653
theorem B3521477 : Blo 2197435 3521477 := bbase (se 4 (by rfl) ⟨330138, by rfl⟩ : syracuseStep 3521477 = 660277) (by norm_num)
theorem B2347651 : Blo 2197435 2347651 := bstep (se 1 (by rfl) ⟨1760738, by rfl⟩ : syracuseStep 2347651 = 3521477) B3521477
theorem B3130201 : Blo 2197435 3130201 := bstep (se 2 (by rfl) ⟨1173825, by rfl⟩ : syracuseStep 3130201 = 2347651) B2347651
theorem B4173601 : Blo 2197435 4173601 := bstep (se 2 (by rfl) ⟨1565100, by rfl⟩ : syracuseStep 4173601 = 3130201) B3130201
theorem B5564801 : Blo 2197435 5564801 := bstep (se 2 (by rfl) ⟨2086800, by rfl⟩ : syracuseStep 5564801 = 4173601) B4173601
theorem B3709867 : Blo 2197435 3709867 := bstep (se 1 (by rfl) ⟨2782400, by rfl⟩ : syracuseStep 3709867 = 5564801) B5564801
theorem B4946489 : Blo 2197435 4946489 := bstep (se 2 (by rfl) ⟨1854933, by rfl⟩ : syracuseStep 4946489 = 3709867) B3709867
theorem B3297659 : Blo 2197435 3297659 := bstep (se 1 (by rfl) ⟨2473244, by rfl⟩ : syracuseStep 3297659 = 4946489) B4946489
theorem B2198439 : Blo 2197435 2198439 := bstep (se 1 (by rfl) ⟨1648829, by rfl⟩ : syracuseStep 2198439 = 3297659) B3297659
theorem B2473249 : Blo 2197435 2473249 := bbase (se 2 (by rfl) ⟨927468, by rfl⟩ : syracuseStep 2473249 = 1854937) (by norm_num)
theorem B3297665 : Blo 2197435 3297665 := bstep (se 2 (by rfl) ⟨1236624, by rfl⟩ : syracuseStep 3297665 = 2473249) B2473249
theorem B2198443 : Blo 2197435 2198443 := bstep (se 1 (by rfl) ⟨1648832, by rfl⟩ : syracuseStep 2198443 = 3297665) B3297665
theorem B5564821 : Blo 2197435 5564821 := bbase (se 6 (by rfl) ⟨130425, by rfl⟩ : syracuseStep 5564821 = 260851) (by norm_num)
theorem B7419761 : Blo 2197435 7419761 := bstep (se 2 (by rfl) ⟨2782410, by rfl⟩ : syracuseStep 7419761 = 5564821) B5564821
theorem B4946507 : Blo 2197435 4946507 := bstep (se 1 (by rfl) ⟨3709880, by rfl⟩ : syracuseStep 4946507 = 7419761) B7419761
theorem B3297671 : Blo 2197435 3297671 := bstep (se 1 (by rfl) ⟨2473253, by rfl⟩ : syracuseStep 3297671 = 4946507) B4946507
theorem B2198447 : Blo 2197435 2198447 := bstep (se 1 (by rfl) ⟨1648835, by rfl⟩ : syracuseStep 2198447 = 3297671) B3297671
theorem B3297677 : Blo 2197435 3297677 := bbase (se 3 (by rfl) ⟨618314, by rfl⟩ : syracuseStep 3297677 = 1236629) (by norm_num)
theorem B2198451 : Blo 2197435 2198451 := bstep (se 1 (by rfl) ⟨1648838, by rfl⟩ : syracuseStep 2198451 = 3297677) B3297677
theorem B4946525 : Blo 2197435 4946525 := bbase (se 3 (by rfl) ⟨927473, by rfl⟩ : syracuseStep 4946525 = 1854947) (by norm_num)
theorem B3297683 : Blo 2197435 3297683 := bstep (se 1 (by rfl) ⟨2473262, by rfl⟩ : syracuseStep 3297683 = 4946525) B4946525
theorem B2198455 : Blo 2197435 2198455 := bstep (se 1 (by rfl) ⟨1648841, by rfl⟩ : syracuseStep 2198455 = 3297683) B3297683
theorem B3709901 : Blo 2197435 3709901 := bbase (se 3 (by rfl) ⟨695606, by rfl⟩ : syracuseStep 3709901 = 1391213) (by norm_num)
theorem B2473267 : Blo 2197435 2473267 := bstep (se 1 (by rfl) ⟨1854950, by rfl⟩ : syracuseStep 2473267 = 3709901) B3709901
theorem B3297689 : Blo 2197435 3297689 := bstep (se 2 (by rfl) ⟨1236633, by rfl⟩ : syracuseStep 3297689 = 2473267) B2473267
theorem B2198459 : Blo 2197435 2198459 := bstep (se 1 (by rfl) ⟨1648844, by rfl⟩ : syracuseStep 2198459 = 3297689) B3297689
theorem B2320921 : Blo 2197435 2320921 := bbase (se 2 (by rfl) ⟨870345, by rfl⟩ : syracuseStep 2320921 = 1740691) (by norm_num)
theorem B3094561 : Blo 2197435 3094561 := bstep (se 2 (by rfl) ⟨1160460, by rfl⟩ : syracuseStep 3094561 = 2320921) B2320921
theorem B4126081 : Blo 2197435 4126081 := bstep (se 2 (by rfl) ⟨1547280, by rfl⟩ : syracuseStep 4126081 = 3094561) B3094561
theorem B5501441 : Blo 2197435 5501441 := bstep (se 2 (by rfl) ⟨2063040, by rfl⟩ : syracuseStep 5501441 = 4126081) B4126081
theorem B3667627 : Blo 2197435 3667627 := bstep (se 1 (by rfl) ⟨2750720, by rfl⟩ : syracuseStep 3667627 = 5501441) B5501441
theorem B4890169 : Blo 2197435 4890169 := bstep (se 2 (by rfl) ⟨1833813, by rfl⟩ : syracuseStep 4890169 = 3667627) B3667627
theorem B6520225 : Blo 2197435 6520225 := bstep (se 2 (by rfl) ⟨2445084, by rfl⟩ : syracuseStep 6520225 = 4890169) B4890169
theorem B8693633 : Blo 2197435 8693633 := bstep (se 2 (by rfl) ⟨3260112, by rfl⟩ : syracuseStep 8693633 = 6520225) B6520225
theorem B5795755 : Blo 2197435 5795755 := bstep (se 1 (by rfl) ⟨4346816, by rfl⟩ : syracuseStep 5795755 = 8693633) B8693633
theorem B30910693 : Blo 2197435 30910693 := bstep (se 4 (by rfl) ⟨2897877, by rfl⟩ : syracuseStep 30910693 = 5795755) B5795755
theorem B41214257 : Blo 2197435 41214257 := bstep (se 2 (by rfl) ⟨15455346, by rfl⟩ : syracuseStep 41214257 = 30910693) B30910693
theorem B27476171 : Blo 2197435 27476171 := bstep (se 1 (by rfl) ⟨20607128, by rfl⟩ : syracuseStep 27476171 = 41214257) B41214257
theorem B18317447 : Blo 2197435 18317447 := bstep (se 1 (by rfl) ⟨13738085, by rfl⟩ : syracuseStep 18317447 = 27476171) B27476171
theorem B12211631 : Blo 2197435 12211631 := bstep (se 1 (by rfl) ⟨9158723, by rfl⟩ : syracuseStep 12211631 = 18317447) B18317447
theorem B8141087 : Blo 2197435 8141087 := bstep (se 1 (by rfl) ⟨6105815, by rfl⟩ : syracuseStep 8141087 = 12211631) B12211631
theorem B21709565 : Blo 2197435 21709565 := bstep (se 3 (by rfl) ⟨4070543, by rfl⟩ : syracuseStep 21709565 = 8141087) B8141087
theorem B14473043 : Blo 2197435 14473043 := bstep (se 1 (by rfl) ⟨10854782, by rfl⟩ : syracuseStep 14473043 = 21709565) B21709565
theorem B9648695 : Blo 2197435 9648695 := bstep (se 1 (by rfl) ⟨7236521, by rfl⟩ : syracuseStep 9648695 = 14473043) B14473043
theorem B6432463 : Blo 2197435 6432463 := bstep (se 1 (by rfl) ⟨4824347, by rfl⟩ : syracuseStep 6432463 = 9648695) B9648695
theorem B34306469 : Blo 2197435 34306469 := bstep (se 4 (by rfl) ⟨3216231, by rfl⟩ : syracuseStep 34306469 = 6432463) B6432463
theorem B22870979 : Blo 2197435 22870979 := bstep (se 1 (by rfl) ⟨17153234, by rfl⟩ : syracuseStep 22870979 = 34306469) B34306469
theorem B15247319 : Blo 2197435 15247319 := bstep (se 1 (by rfl) ⟨11435489, by rfl⟩ : syracuseStep 15247319 = 22870979) B22870979
theorem B40659517 : Blo 2197435 40659517 := bstep (se 3 (by rfl) ⟨7623659, by rfl⟩ : syracuseStep 40659517 = 15247319) B15247319
theorem B54212689 : Blo 2197435 54212689 := bstep (se 2 (by rfl) ⟨20329758, by rfl⟩ : syracuseStep 54212689 = 40659517) B40659517
theorem B72283585 : Blo 2197435 72283585 := bstep (se 2 (by rfl) ⟨27106344, by rfl⟩ : syracuseStep 72283585 = 54212689) B54212689
theorem B96378113 : Blo 2197435 96378113 := bstep (se 2 (by rfl) ⟨36141792, by rfl⟩ : syracuseStep 96378113 = 72283585) B72283585
theorem B64252075 : Blo 2197435 64252075 := bstep (se 1 (by rfl) ⟨48189056, by rfl⟩ : syracuseStep 64252075 = 96378113) B96378113
theorem B85669433 : Blo 2197435 85669433 := bstep (se 2 (by rfl) ⟨32126037, by rfl⟩ : syracuseStep 85669433 = 64252075) B64252075
theorem B57112955 : Blo 2197435 57112955 := bstep (se 1 (by rfl) ⟨42834716, by rfl⟩ : syracuseStep 57112955 = 85669433) B85669433
theorem B38075303 : Blo 2197435 38075303 := bstep (se 1 (by rfl) ⟨28556477, by rfl⟩ : syracuseStep 38075303 = 57112955) B57112955
theorem B101534141 : Blo 2197435 101534141 := bstep (se 3 (by rfl) ⟨19037651, by rfl⟩ : syracuseStep 101534141 = 38075303) B38075303
theorem B67689427 : Blo 2197435 67689427 := bstep (se 1 (by rfl) ⟨50767070, by rfl⟩ : syracuseStep 67689427 = 101534141) B101534141
theorem B90252569 : Blo 2197435 90252569 := bstep (se 2 (by rfl) ⟨33844713, by rfl⟩ : syracuseStep 90252569 = 67689427) B67689427
theorem B60168379 : Blo 2197435 60168379 := bstep (se 1 (by rfl) ⟨45126284, by rfl⟩ : syracuseStep 60168379 = 90252569) B90252569
theorem B80224505 : Blo 2197435 80224505 := bstep (se 2 (by rfl) ⟨30084189, by rfl⟩ : syracuseStep 80224505 = 60168379) B60168379
theorem B53483003 : Blo 2197435 53483003 := bstep (se 1 (by rfl) ⟨40112252, by rfl⟩ : syracuseStep 53483003 = 80224505) B80224505
theorem B35655335 : Blo 2197435 35655335 := bstep (se 1 (by rfl) ⟨26741501, by rfl⟩ : syracuseStep 35655335 = 53483003) B53483003
theorem B23770223 : Blo 2197435 23770223 := bstep (se 1 (by rfl) ⟨17827667, by rfl⟩ : syracuseStep 23770223 = 35655335) B35655335
theorem B15846815 : Blo 2197435 15846815 := bstep (se 1 (by rfl) ⟨11885111, by rfl⟩ : syracuseStep 15846815 = 23770223) B23770223
theorem B10564543 : Blo 2197435 10564543 := bstep (se 1 (by rfl) ⟨7923407, by rfl⟩ : syracuseStep 10564543 = 15846815) B15846815
theorem B14086057 : Blo 2197435 14086057 := bstep (se 2 (by rfl) ⟨5282271, by rfl⟩ : syracuseStep 14086057 = 10564543) B10564543
theorem B18781409 : Blo 2197435 18781409 := bstep (se 2 (by rfl) ⟨7043028, by rfl⟩ : syracuseStep 18781409 = 14086057) B14086057
theorem B12520939 : Blo 2197435 12520939 := bstep (se 1 (by rfl) ⟨9390704, by rfl⟩ : syracuseStep 12520939 = 18781409) B18781409
theorem B16694585 : Blo 2197435 16694585 := bstep (se 2 (by rfl) ⟨6260469, by rfl⟩ : syracuseStep 16694585 = 12520939) B12520939
theorem B11129723 : Blo 2197435 11129723 := bstep (se 1 (by rfl) ⟨8347292, by rfl⟩ : syracuseStep 11129723 = 16694585) B16694585
theorem B7419815 : Blo 2197435 7419815 := bstep (se 1 (by rfl) ⟨5564861, by rfl⟩ : syracuseStep 7419815 = 11129723) B11129723
theorem B4946543 : Blo 2197435 4946543 := bstep (se 1 (by rfl) ⟨3709907, by rfl⟩ : syracuseStep 4946543 = 7419815) B7419815
theorem B3297695 : Blo 2197435 3297695 := bstep (se 1 (by rfl) ⟨2473271, by rfl⟩ : syracuseStep 3297695 = 4946543) B4946543
theorem B2198463 : Blo 2197435 2198463 := bstep (se 1 (by rfl) ⟨1648847, by rfl⟩ : syracuseStep 2198463 = 3297695) B3297695
theorem B3297701 : Blo 2197435 3297701 := bbase (se 4 (by rfl) ⟨309159, by rfl⟩ : syracuseStep 3297701 = 618319) (by norm_num)
theorem B2198467 : Blo 2197435 2198467 := bstep (se 1 (by rfl) ⟨1648850, by rfl⟩ : syracuseStep 2198467 = 3297701) B3297701
theorem B2782441 : Blo 2197435 2782441 := bbase (se 2 (by rfl) ⟨1043415, by rfl⟩ : syracuseStep 2782441 = 2086831) (by norm_num)
theorem B3709921 : Blo 2197435 3709921 := bstep (se 2 (by rfl) ⟨1391220, by rfl⟩ : syracuseStep 3709921 = 2782441) B2782441
theorem B4946561 : Blo 2197435 4946561 := bstep (se 2 (by rfl) ⟨1854960, by rfl⟩ : syracuseStep 4946561 = 3709921) B3709921
theorem B3297707 : Blo 2197435 3297707 := bstep (se 1 (by rfl) ⟨2473280, by rfl⟩ : syracuseStep 3297707 = 4946561) B4946561
theorem B2198471 : Blo 2197435 2198471 := bstep (se 1 (by rfl) ⟨1648853, by rfl⟩ : syracuseStep 2198471 = 3297707) B3297707
theorem B2473285 : Blo 2197435 2473285 := bbase (se 4 (by rfl) ⟨231870, by rfl⟩ : syracuseStep 2473285 = 463741) (by norm_num)
theorem B3297713 : Blo 2197435 3297713 := bstep (se 2 (by rfl) ⟨1236642, by rfl⟩ : syracuseStep 3297713 = 2473285) B2473285
theorem B2198475 : Blo 2197435 2198475 := bstep (se 1 (by rfl) ⟨1648856, by rfl⟩ : syracuseStep 2198475 = 3297713) B3297713
theorem B4173677 : Blo 2197435 4173677 := bbase (se 3 (by rfl) ⟨782564, by rfl⟩ : syracuseStep 4173677 = 1565129) (by norm_num)
theorem B2782451 : Blo 2197435 2782451 := bstep (se 1 (by rfl) ⟨2086838, by rfl⟩ : syracuseStep 2782451 = 4173677) B4173677
theorem B7419869 : Blo 2197435 7419869 := bstep (se 3 (by rfl) ⟨1391225, by rfl⟩ : syracuseStep 7419869 = 2782451) B2782451
theorem B4946579 : Blo 2197435 4946579 := bstep (se 1 (by rfl) ⟨3709934, by rfl⟩ : syracuseStep 4946579 = 7419869) B7419869
theorem B3297719 : Blo 2197435 3297719 := bstep (se 1 (by rfl) ⟨2473289, by rfl⟩ : syracuseStep 3297719 = 4946579) B4946579
theorem B2198479 : Blo 2197435 2198479 := bstep (se 1 (by rfl) ⟨1648859, by rfl⟩ : syracuseStep 2198479 = 3297719) B3297719
theorem B3297725 : Blo 2197435 3297725 := bbase (se 3 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 3297725 = 1236647) (by norm_num)
theorem B2198483 : Blo 2197435 2198483 := bstep (se 1 (by rfl) ⟨1648862, by rfl⟩ : syracuseStep 2198483 = 3297725) B3297725
theorem B4946597 : Blo 2197435 4946597 := bbase (se 4 (by rfl) ⟨463743, by rfl⟩ : syracuseStep 4946597 = 927487) (by norm_num)
theorem B3297731 : Blo 2197435 3297731 := bstep (se 1 (by rfl) ⟨2473298, by rfl⟩ : syracuseStep 3297731 = 4946597) B4946597
theorem B2198487 : Blo 2197435 2198487 := bstep (se 1 (by rfl) ⟨1648865, by rfl⟩ : syracuseStep 2198487 = 3297731) B3297731
theorem B5564933 : Blo 2197435 5564933 := bbase (se 4 (by rfl) ⟨521712, by rfl⟩ : syracuseStep 5564933 = 1043425) (by norm_num)
theorem B3709955 : Blo 2197435 3709955 := bstep (se 1 (by rfl) ⟨2782466, by rfl⟩ : syracuseStep 3709955 = 5564933) B5564933
theorem B2473303 : Blo 2197435 2473303 := bstep (se 1 (by rfl) ⟨1854977, by rfl⟩ : syracuseStep 2473303 = 3709955) B3709955
theorem B3297737 : Blo 2197435 3297737 := bstep (se 2 (by rfl) ⟨1236651, by rfl⟩ : syracuseStep 3297737 = 2473303) B2473303
theorem B2198491 : Blo 2197435 2198491 := bstep (se 1 (by rfl) ⟨1648868, by rfl⟩ : syracuseStep 2198491 = 3297737) B3297737
theorem B4695421 : Blo 2197435 4695421 := bbase (se 3 (by rfl) ⟨880391, by rfl⟩ : syracuseStep 4695421 = 1760783) (by norm_num)
theorem B6260561 : Blo 2197435 6260561 := bstep (se 2 (by rfl) ⟨2347710, by rfl⟩ : syracuseStep 6260561 = 4695421) B4695421
theorem B4173707 : Blo 2197435 4173707 := bstep (se 1 (by rfl) ⟨3130280, by rfl⟩ : syracuseStep 4173707 = 6260561) B6260561
theorem B11129885 : Blo 2197435 11129885 := bstep (se 3 (by rfl) ⟨2086853, by rfl⟩ : syracuseStep 11129885 = 4173707) B4173707
theorem B7419923 : Blo 2197435 7419923 := bstep (se 1 (by rfl) ⟨5564942, by rfl⟩ : syracuseStep 7419923 = 11129885) B11129885
theorem B4946615 : Blo 2197435 4946615 := bstep (se 1 (by rfl) ⟨3709961, by rfl⟩ : syracuseStep 4946615 = 7419923) B7419923
theorem B3297743 : Blo 2197435 3297743 := bstep (se 1 (by rfl) ⟨2473307, by rfl⟩ : syracuseStep 3297743 = 4946615) B4946615
theorem B2198495 : Blo 2197435 2198495 := bstep (se 1 (by rfl) ⟨1648871, by rfl⟩ : syracuseStep 2198495 = 3297743) B3297743
theorem B3297749 : Blo 2197435 3297749 := bbase (se 7 (by rfl) ⟨38645, by rfl⟩ : syracuseStep 3297749 = 77291) (by norm_num)
theorem B2198499 : Blo 2197435 2198499 := bstep (se 1 (by rfl) ⟨1648874, by rfl⟩ : syracuseStep 2198499 = 3297749) B3297749
theorem B8347445 : Blo 2197435 8347445 := bbase (se 5 (by rfl) ⟨391286, by rfl⟩ : syracuseStep 8347445 = 782573) (by norm_num)
theorem B5564963 : Blo 2197435 5564963 := bstep (se 1 (by rfl) ⟨4173722, by rfl⟩ : syracuseStep 5564963 = 8347445) B8347445
theorem B3709975 : Blo 2197435 3709975 := bstep (se 1 (by rfl) ⟨2782481, by rfl⟩ : syracuseStep 3709975 = 5564963) B5564963
theorem B4946633 : Blo 2197435 4946633 := bstep (se 2 (by rfl) ⟨1854987, by rfl⟩ : syracuseStep 4946633 = 3709975) B3709975
theorem B3297755 : Blo 2197435 3297755 := bstep (se 1 (by rfl) ⟨2473316, by rfl⟩ : syracuseStep 3297755 = 4946633) B4946633
theorem B2198503 : Blo 2197435 2198503 := bstep (se 1 (by rfl) ⟨1648877, by rfl⟩ : syracuseStep 2198503 = 3297755) B3297755
theorem B2473321 : Blo 2197435 2473321 := bbase (se 2 (by rfl) ⟨927495, by rfl⟩ : syracuseStep 2473321 = 1854991) (by norm_num)
theorem B3297761 : Blo 2197435 3297761 := bstep (se 2 (by rfl) ⟨1236660, by rfl⟩ : syracuseStep 3297761 = 2473321) B2473321
theorem B2198507 : Blo 2197435 2198507 := bstep (se 1 (by rfl) ⟨1648880, by rfl⟩ : syracuseStep 2198507 = 3297761) B3297761
theorem B6023765 : Blo 2197435 6023765 := bbase (se 8 (by rfl) ⟨35295, by rfl⟩ : syracuseStep 6023765 = 70591) (by norm_num)
theorem B16063373 : Blo 2197435 16063373 := bstep (se 3 (by rfl) ⟨3011882, by rfl⟩ : syracuseStep 16063373 = 6023765) B6023765
theorem B42835661 : Blo 2197435 42835661 := bstep (se 3 (by rfl) ⟨8031686, by rfl⟩ : syracuseStep 42835661 = 16063373) B16063373
theorem B28557107 : Blo 2197435 28557107 := bstep (se 1 (by rfl) ⟨21417830, by rfl⟩ : syracuseStep 28557107 = 42835661) B42835661
theorem B19038071 : Blo 2197435 19038071 := bstep (se 1 (by rfl) ⟨14278553, by rfl⟩ : syracuseStep 19038071 = 28557107) B28557107
theorem B12692047 : Blo 2197435 12692047 := bstep (se 1 (by rfl) ⟨9519035, by rfl⟩ : syracuseStep 12692047 = 19038071) B19038071
theorem B16922729 : Blo 2197435 16922729 := bstep (se 2 (by rfl) ⟨6346023, by rfl⟩ : syracuseStep 16922729 = 12692047) B12692047
theorem B45127277 : Blo 2197435 45127277 := bstep (se 3 (by rfl) ⟨8461364, by rfl⟩ : syracuseStep 45127277 = 16922729) B16922729
theorem B30084851 : Blo 2197435 30084851 := bstep (se 1 (by rfl) ⟨22563638, by rfl⟩ : syracuseStep 30084851 = 45127277) B45127277
theorem B20056567 : Blo 2197435 20056567 := bstep (se 1 (by rfl) ⟨15042425, by rfl⟩ : syracuseStep 20056567 = 30084851) B30084851
theorem B26742089 : Blo 2197435 26742089 := bstep (se 2 (by rfl) ⟨10028283, by rfl⟩ : syracuseStep 26742089 = 20056567) B20056567
theorem B17828059 : Blo 2197435 17828059 := bstep (se 1 (by rfl) ⟨13371044, by rfl⟩ : syracuseStep 17828059 = 26742089) B26742089
theorem B23770745 : Blo 2197435 23770745 := bstep (se 2 (by rfl) ⟨8914029, by rfl⟩ : syracuseStep 23770745 = 17828059) B17828059
theorem B15847163 : Blo 2197435 15847163 := bstep (se 1 (by rfl) ⟨11885372, by rfl⟩ : syracuseStep 15847163 = 23770745) B23770745
theorem B10564775 : Blo 2197435 10564775 := bstep (se 1 (by rfl) ⟨7923581, by rfl⟩ : syracuseStep 10564775 = 15847163) B15847163
theorem B7043183 : Blo 2197435 7043183 := bstep (se 1 (by rfl) ⟨5282387, by rfl⟩ : syracuseStep 7043183 = 10564775) B10564775
theorem B4695455 : Blo 2197435 4695455 := bstep (se 1 (by rfl) ⟨3521591, by rfl⟩ : syracuseStep 4695455 = 7043183) B7043183
theorem B12521213 : Blo 2197435 12521213 := bstep (se 3 (by rfl) ⟨2347727, by rfl⟩ : syracuseStep 12521213 = 4695455) B4695455
theorem B8347475 : Blo 2197435 8347475 := bstep (se 1 (by rfl) ⟨6260606, by rfl⟩ : syracuseStep 8347475 = 12521213) B12521213
theorem B5564983 : Blo 2197435 5564983 := bstep (se 1 (by rfl) ⟨4173737, by rfl⟩ : syracuseStep 5564983 = 8347475) B8347475
theorem B7419977 : Blo 2197435 7419977 := bstep (se 2 (by rfl) ⟨2782491, by rfl⟩ : syracuseStep 7419977 = 5564983) B5564983
theorem B4946651 : Blo 2197435 4946651 := bstep (se 1 (by rfl) ⟨3709988, by rfl⟩ : syracuseStep 4946651 = 7419977) B7419977
theorem B3297767 : Blo 2197435 3297767 := bstep (se 1 (by rfl) ⟨2473325, by rfl⟩ : syracuseStep 3297767 = 4946651) B4946651
theorem B2198511 : Blo 2197435 2198511 := bstep (se 1 (by rfl) ⟨1648883, by rfl⟩ : syracuseStep 2198511 = 3297767) B3297767
theorem B3297773 : Blo 2197435 3297773 := bbase (se 3 (by rfl) ⟨618332, by rfl⟩ : syracuseStep 3297773 = 1236665) (by norm_num)
theorem B2198515 : Blo 2197435 2198515 := bstep (se 1 (by rfl) ⟨1648886, by rfl⟩ : syracuseStep 2198515 = 3297773) B3297773
theorem B4946669 : Blo 2197435 4946669 := bbase (se 3 (by rfl) ⟨927500, by rfl⟩ : syracuseStep 4946669 = 1855001) (by norm_num)
theorem B3297779 : Blo 2197435 3297779 := bstep (se 1 (by rfl) ⟨2473334, by rfl⟩ : syracuseStep 3297779 = 4946669) B4946669
theorem B2198519 : Blo 2197435 2198519 := bstep (se 1 (by rfl) ⟨1648889, by rfl⟩ : syracuseStep 2198519 = 3297779) B3297779
theorem B2347741 : Blo 2197435 2347741 := bbase (se 3 (by rfl) ⟨440201, by rfl⟩ : syracuseStep 2347741 = 880403) (by norm_num)
theorem B3130321 : Blo 2197435 3130321 := bstep (se 2 (by rfl) ⟨1173870, by rfl⟩ : syracuseStep 3130321 = 2347741) B2347741
theorem B4173761 : Blo 2197435 4173761 := bstep (se 2 (by rfl) ⟨1565160, by rfl⟩ : syracuseStep 4173761 = 3130321) B3130321
theorem B2782507 : Blo 2197435 2782507 := bstep (se 1 (by rfl) ⟨2086880, by rfl⟩ : syracuseStep 2782507 = 4173761) B4173761
theorem B3710009 : Blo 2197435 3710009 := bstep (se 2 (by rfl) ⟨1391253, by rfl⟩ : syracuseStep 3710009 = 2782507) B2782507
theorem B2473339 : Blo 2197435 2473339 := bstep (se 1 (by rfl) ⟨1855004, by rfl⟩ : syracuseStep 2473339 = 3710009) B3710009
theorem B3297785 : Blo 2197435 3297785 := bstep (se 2 (by rfl) ⟨1236669, by rfl⟩ : syracuseStep 3297785 = 2473339) B2473339
theorem B2198523 : Blo 2197435 2198523 := bstep (se 1 (by rfl) ⟨1648892, by rfl⟩ : syracuseStep 2198523 = 3297785) B3297785
theorem B2677249 : Blo 2197435 2677249 := bbase (se 2 (by rfl) ⟨1003968, by rfl⟩ : syracuseStep 2677249 = 2007937) (by norm_num)
theorem B3569665 : Blo 2197435 3569665 := bstep (se 2 (by rfl) ⟨1338624, by rfl⟩ : syracuseStep 3569665 = 2677249) B2677249
theorem B4759553 : Blo 2197435 4759553 := bstep (se 2 (by rfl) ⟨1784832, by rfl⟩ : syracuseStep 4759553 = 3569665) B3569665
theorem B3173035 : Blo 2197435 3173035 := bstep (se 1 (by rfl) ⟨2379776, by rfl⟩ : syracuseStep 3173035 = 4759553) B4759553
theorem B4230713 : Blo 2197435 4230713 := bstep (se 2 (by rfl) ⟨1586517, by rfl⟩ : syracuseStep 4230713 = 3173035) B3173035
theorem B2820475 : Blo 2197435 2820475 := bstep (se 1 (by rfl) ⟨2115356, by rfl⟩ : syracuseStep 2820475 = 4230713) B4230713
theorem B3760633 : Blo 2197435 3760633 := bstep (se 2 (by rfl) ⟨1410237, by rfl⟩ : syracuseStep 3760633 = 2820475) B2820475
theorem B20056709 : Blo 2197435 20056709 := bstep (se 4 (by rfl) ⟨1880316, by rfl⟩ : syracuseStep 20056709 = 3760633) B3760633
theorem B13371139 : Blo 2197435 13371139 := bstep (se 1 (by rfl) ⟨10028354, by rfl⟩ : syracuseStep 13371139 = 20056709) B20056709
theorem B17828185 : Blo 2197435 17828185 := bstep (se 2 (by rfl) ⟨6685569, by rfl⟩ : syracuseStep 17828185 = 13371139) B13371139
theorem B23770913 : Blo 2197435 23770913 := bstep (se 2 (by rfl) ⟨8914092, by rfl⟩ : syracuseStep 23770913 = 17828185) B17828185
theorem B63389101 : Blo 2197435 63389101 := bstep (se 3 (by rfl) ⟨11885456, by rfl⟩ : syracuseStep 63389101 = 23770913) B23770913
theorem B84518801 : Blo 2197435 84518801 := bstep (se 2 (by rfl) ⟨31694550, by rfl⟩ : syracuseStep 84518801 = 63389101) B63389101
theorem B56345867 : Blo 2197435 56345867 := bstep (se 1 (by rfl) ⟨42259400, by rfl⟩ : syracuseStep 56345867 = 84518801) B84518801
theorem B37563911 : Blo 2197435 37563911 := bstep (se 1 (by rfl) ⟨28172933, by rfl⟩ : syracuseStep 37563911 = 56345867) B56345867
theorem B25042607 : Blo 2197435 25042607 := bstep (se 1 (by rfl) ⟨18781955, by rfl⟩ : syracuseStep 25042607 = 37563911) B37563911
theorem B16695071 : Blo 2197435 16695071 := bstep (se 1 (by rfl) ⟨12521303, by rfl⟩ : syracuseStep 16695071 = 25042607) B25042607
theorem B11130047 : Blo 2197435 11130047 := bstep (se 1 (by rfl) ⟨8347535, by rfl⟩ : syracuseStep 11130047 = 16695071) B16695071
theorem B7420031 : Blo 2197435 7420031 := bstep (se 1 (by rfl) ⟨5565023, by rfl⟩ : syracuseStep 7420031 = 11130047) B11130047
theorem B4946687 : Blo 2197435 4946687 := bstep (se 1 (by rfl) ⟨3710015, by rfl⟩ : syracuseStep 4946687 = 7420031) B7420031
theorem B3297791 : Blo 2197435 3297791 := bstep (se 1 (by rfl) ⟨2473343, by rfl⟩ : syracuseStep 3297791 = 4946687) B4946687
theorem B2198527 : Blo 2197435 2198527 := bstep (se 1 (by rfl) ⟨1648895, by rfl⟩ : syracuseStep 2198527 = 3297791) B3297791
theorem B3297797 : Blo 2197435 3297797 := bbase (se 4 (by rfl) ⟨309168, by rfl⟩ : syracuseStep 3297797 = 618337) (by norm_num)
theorem B2198531 : Blo 2197435 2198531 := bstep (se 1 (by rfl) ⟨1648898, by rfl⟩ : syracuseStep 2198531 = 3297797) B3297797
theorem B3710029 : Blo 2197435 3710029 := bbase (se 3 (by rfl) ⟨695630, by rfl⟩ : syracuseStep 3710029 = 1391261) (by norm_num)
theorem B4946705 : Blo 2197435 4946705 := bstep (se 2 (by rfl) ⟨1855014, by rfl⟩ : syracuseStep 4946705 = 3710029) B3710029
theorem B3297803 : Blo 2197435 3297803 := bstep (se 1 (by rfl) ⟨2473352, by rfl⟩ : syracuseStep 3297803 = 4946705) B4946705
theorem B2198535 : Blo 2197435 2198535 := bstep (se 1 (by rfl) ⟨1648901, by rfl⟩ : syracuseStep 2198535 = 3297803) B3297803
theorem B2473357 : Blo 2197435 2473357 := bbase (se 3 (by rfl) ⟨463754, by rfl⟩ : syracuseStep 2473357 = 927509) (by norm_num)
theorem B3297809 : Blo 2197435 3297809 := bstep (se 2 (by rfl) ⟨1236678, by rfl⟩ : syracuseStep 3297809 = 2473357) B2473357
theorem B2198539 : Blo 2197435 2198539 := bstep (se 1 (by rfl) ⟨1648904, by rfl⟩ : syracuseStep 2198539 = 3297809) B3297809
theorem B7420085 : Blo 2197435 7420085 := bbase (se 5 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 7420085 = 695633) (by norm_num)
theorem B4946723 : Blo 2197435 4946723 := bstep (se 1 (by rfl) ⟨3710042, by rfl⟩ : syracuseStep 4946723 = 7420085) B7420085
theorem B3297815 : Blo 2197435 3297815 := bstep (se 1 (by rfl) ⟨2473361, by rfl⟩ : syracuseStep 3297815 = 4946723) B4946723
theorem B2198543 : Blo 2197435 2198543 := bstep (se 1 (by rfl) ⟨1648907, by rfl⟩ : syracuseStep 2198543 = 3297815) B3297815
theorem B3297821 : Blo 2197435 3297821 := bbase (se 3 (by rfl) ⟨618341, by rfl⟩ : syracuseStep 3297821 = 1236683) (by norm_num)
theorem B2198547 : Blo 2197435 2198547 := bstep (se 1 (by rfl) ⟨1648910, by rfl⟩ : syracuseStep 2198547 = 3297821) B3297821
theorem B4946741 : Blo 2197435 4946741 := bbase (se 5 (by rfl) ⟨231878, by rfl⟩ : syracuseStep 4946741 = 463757) (by norm_num)
theorem B3297827 : Blo 2197435 3297827 := bstep (se 1 (by rfl) ⟨2473370, by rfl⟩ : syracuseStep 3297827 = 4946741) B4946741
theorem B2198551 : Blo 2197435 2198551 := bstep (se 1 (by rfl) ⟨1648913, by rfl⟩ : syracuseStep 2198551 = 3297827) B3297827
theorem B10028485 : Blo 2197435 10028485 := bbase (se 4 (by rfl) ⟨940170, by rfl⟩ : syracuseStep 10028485 = 1880341) (by norm_num)
theorem B13371313 : Blo 2197435 13371313 := bstep (se 2 (by rfl) ⟨5014242, by rfl⟩ : syracuseStep 13371313 = 10028485) B10028485
theorem B17828417 : Blo 2197435 17828417 := bstep (se 2 (by rfl) ⟨6685656, by rfl⟩ : syracuseStep 17828417 = 13371313) B13371313
theorem B11885611 : Blo 2197435 11885611 := bstep (se 1 (by rfl) ⟨8914208, by rfl⟩ : syracuseStep 11885611 = 17828417) B17828417
theorem B15847481 : Blo 2197435 15847481 := bstep (se 2 (by rfl) ⟨5942805, by rfl⟩ : syracuseStep 15847481 = 11885611) B11885611
theorem B10564987 : Blo 2197435 10564987 := bstep (se 1 (by rfl) ⟨7923740, by rfl⟩ : syracuseStep 10564987 = 15847481) B15847481
theorem B14086649 : Blo 2197435 14086649 := bstep (se 2 (by rfl) ⟨5282493, by rfl⟩ : syracuseStep 14086649 = 10564987) B10564987
theorem B9391099 : Blo 2197435 9391099 := bstep (se 1 (by rfl) ⟨7043324, by rfl⟩ : syracuseStep 9391099 = 14086649) B14086649
theorem B12521465 : Blo 2197435 12521465 := bstep (se 2 (by rfl) ⟨4695549, by rfl⟩ : syracuseStep 12521465 = 9391099) B9391099
theorem B8347643 : Blo 2197435 8347643 := bstep (se 1 (by rfl) ⟨6260732, by rfl⟩ : syracuseStep 8347643 = 12521465) B12521465
theorem B5565095 : Blo 2197435 5565095 := bstep (se 1 (by rfl) ⟨4173821, by rfl⟩ : syracuseStep 5565095 = 8347643) B8347643
theorem B3710063 : Blo 2197435 3710063 := bstep (se 1 (by rfl) ⟨2782547, by rfl⟩ : syracuseStep 3710063 = 5565095) B5565095
theorem B2473375 : Blo 2197435 2473375 := bstep (se 1 (by rfl) ⟨1855031, by rfl⟩ : syracuseStep 2473375 = 3710063) B3710063
theorem B3297833 : Blo 2197435 3297833 := bstep (se 2 (by rfl) ⟨1236687, by rfl⟩ : syracuseStep 3297833 = 2473375) B2473375
theorem B2198555 : Blo 2197435 2198555 := bstep (se 1 (by rfl) ⟨1648916, by rfl⟩ : syracuseStep 2198555 = 3297833) B3297833
theorem B3961877 : Blo 2197435 3961877 := bbase (se 6 (by rfl) ⟨92856, by rfl⟩ : syracuseStep 3961877 = 185713) (by norm_num)
theorem B10565005 : Blo 2197435 10565005 := bstep (se 3 (by rfl) ⟨1980938, by rfl⟩ : syracuseStep 10565005 = 3961877) B3961877
theorem B14086673 : Blo 2197435 14086673 := bstep (se 2 (by rfl) ⟨5282502, by rfl⟩ : syracuseStep 14086673 = 10565005) B10565005
theorem B9391115 : Blo 2197435 9391115 := bstep (se 1 (by rfl) ⟨7043336, by rfl⟩ : syracuseStep 9391115 = 14086673) B14086673
theorem B6260743 : Blo 2197435 6260743 := bstep (se 1 (by rfl) ⟨4695557, by rfl⟩ : syracuseStep 6260743 = 9391115) B9391115
theorem B8347657 : Blo 2197435 8347657 := bstep (se 2 (by rfl) ⟨3130371, by rfl⟩ : syracuseStep 8347657 = 6260743) B6260743
theorem B11130209 : Blo 2197435 11130209 := bstep (se 2 (by rfl) ⟨4173828, by rfl⟩ : syracuseStep 11130209 = 8347657) B8347657
theorem B7420139 : Blo 2197435 7420139 := bstep (se 1 (by rfl) ⟨5565104, by rfl⟩ : syracuseStep 7420139 = 11130209) B11130209
theorem B4946759 : Blo 2197435 4946759 := bstep (se 1 (by rfl) ⟨3710069, by rfl⟩ : syracuseStep 4946759 = 7420139) B7420139
theorem B3297839 : Blo 2197435 3297839 := bstep (se 1 (by rfl) ⟨2473379, by rfl⟩ : syracuseStep 3297839 = 4946759) B4946759
theorem B2198559 : Blo 2197435 2198559 := bstep (se 1 (by rfl) ⟨1648919, by rfl⟩ : syracuseStep 2198559 = 3297839) B3297839
theorem B3297845 : Blo 2197435 3297845 := bbase (se 5 (by rfl) ⟨154586, by rfl⟩ : syracuseStep 3297845 = 309173) (by norm_num)
theorem B2198563 : Blo 2197435 2198563 := bstep (se 1 (by rfl) ⟨1648922, by rfl⟩ : syracuseStep 2198563 = 3297845) B3297845
theorem B5565125 : Blo 2197435 5565125 := bbase (se 4 (by rfl) ⟨521730, by rfl⟩ : syracuseStep 5565125 = 1043461) (by norm_num)
theorem B3710083 : Blo 2197435 3710083 := bstep (se 1 (by rfl) ⟨2782562, by rfl⟩ : syracuseStep 3710083 = 5565125) B5565125
theorem B4946777 : Blo 2197435 4946777 := bstep (se 2 (by rfl) ⟨1855041, by rfl⟩ : syracuseStep 4946777 = 3710083) B3710083
theorem B3297851 : Blo 2197435 3297851 := bstep (se 1 (by rfl) ⟨2473388, by rfl⟩ : syracuseStep 3297851 = 4946777) B4946777
theorem B2198567 : Blo 2197435 2198567 := bstep (se 1 (by rfl) ⟨1648925, by rfl⟩ : syracuseStep 2198567 = 3297851) B3297851
theorem B2473393 : Blo 2197435 2473393 := bbase (se 2 (by rfl) ⟨927522, by rfl⟩ : syracuseStep 2473393 = 1855045) (by norm_num)
theorem B3297857 : Blo 2197435 3297857 := bstep (se 2 (by rfl) ⟨1236696, by rfl⟩ : syracuseStep 3297857 = 2473393) B2473393
theorem B2198571 : Blo 2197435 2198571 := bstep (se 1 (by rfl) ⟨1648928, by rfl⟩ : syracuseStep 2198571 = 3297857) B3297857
theorem B6260789 : Blo 2197435 6260789 := bbase (se 5 (by rfl) ⟨293474, by rfl⟩ : syracuseStep 6260789 = 586949) (by norm_num)
theorem B4173859 : Blo 2197435 4173859 := bstep (se 1 (by rfl) ⟨3130394, by rfl⟩ : syracuseStep 4173859 = 6260789) B6260789
theorem B5565145 : Blo 2197435 5565145 := bstep (se 2 (by rfl) ⟨2086929, by rfl⟩ : syracuseStep 5565145 = 4173859) B4173859
theorem B7420193 : Blo 2197435 7420193 := bstep (se 2 (by rfl) ⟨2782572, by rfl⟩ : syracuseStep 7420193 = 5565145) B5565145
theorem B4946795 : Blo 2197435 4946795 := bstep (se 1 (by rfl) ⟨3710096, by rfl⟩ : syracuseStep 4946795 = 7420193) B7420193
theorem B3297863 : Blo 2197435 3297863 := bstep (se 1 (by rfl) ⟨2473397, by rfl⟩ : syracuseStep 3297863 = 4946795) B4946795
theorem B2198575 : Blo 2197435 2198575 := bstep (se 1 (by rfl) ⟨1648931, by rfl⟩ : syracuseStep 2198575 = 3297863) B3297863
theorem B3297869 : Blo 2197435 3297869 := bbase (se 3 (by rfl) ⟨618350, by rfl⟩ : syracuseStep 3297869 = 1236701) (by norm_num)
theorem B2198579 : Blo 2197435 2198579 := bstep (se 1 (by rfl) ⟨1648934, by rfl⟩ : syracuseStep 2198579 = 3297869) B3297869
theorem B4946813 : Blo 2197435 4946813 := bbase (se 3 (by rfl) ⟨927527, by rfl⟩ : syracuseStep 4946813 = 1855055) (by norm_num)
theorem B3297875 : Blo 2197435 3297875 := bstep (se 1 (by rfl) ⟨2473406, by rfl⟩ : syracuseStep 3297875 = 4946813) B4946813
theorem B2198583 : Blo 2197435 2198583 := bstep (se 1 (by rfl) ⟨1648937, by rfl⟩ : syracuseStep 2198583 = 3297875) B3297875
theorem B3710117 : Blo 2197435 3710117 := bbase (se 4 (by rfl) ⟨347823, by rfl⟩ : syracuseStep 3710117 = 695647) (by norm_num)
theorem B2473411 : Blo 2197435 2473411 := bstep (se 1 (by rfl) ⟨1855058, by rfl⟩ : syracuseStep 2473411 = 3710117) B3710117
theorem B3297881 : Blo 2197435 3297881 := bstep (se 2 (by rfl) ⟨1236705, by rfl⟩ : syracuseStep 3297881 = 2473411) B2473411
theorem B2198587 : Blo 2197435 2198587 := bstep (se 1 (by rfl) ⟨1648940, by rfl⟩ : syracuseStep 2198587 = 3297881) B3297881
theorem B2347813 : Blo 2197435 2347813 := bbase (se 4 (by rfl) ⟨220107, by rfl⟩ : syracuseStep 2347813 = 440215) (by norm_num)
theorem B3130417 : Blo 2197435 3130417 := bstep (se 2 (by rfl) ⟨1173906, by rfl⟩ : syracuseStep 3130417 = 2347813) B2347813
theorem B16695557 : Blo 2197435 16695557 := bstep (se 4 (by rfl) ⟨1565208, by rfl⟩ : syracuseStep 16695557 = 3130417) B3130417
theorem B11130371 : Blo 2197435 11130371 := bstep (se 1 (by rfl) ⟨8347778, by rfl⟩ : syracuseStep 11130371 = 16695557) B16695557
theorem B7420247 : Blo 2197435 7420247 := bstep (se 1 (by rfl) ⟨5565185, by rfl⟩ : syracuseStep 7420247 = 11130371) B11130371
theorem B4946831 : Blo 2197435 4946831 := bstep (se 1 (by rfl) ⟨3710123, by rfl⟩ : syracuseStep 4946831 = 7420247) B7420247
theorem B3297887 : Blo 2197435 3297887 := bstep (se 1 (by rfl) ⟨2473415, by rfl⟩ : syracuseStep 3297887 = 4946831) B4946831
theorem B2198591 : Blo 2197435 2198591 := bstep (se 1 (by rfl) ⟨1648943, by rfl⟩ : syracuseStep 2198591 = 3297887) B3297887
theorem B3297893 : Blo 2197435 3297893 := bbase (se 4 (by rfl) ⟨309177, by rfl⟩ : syracuseStep 3297893 = 618355) (by norm_num)
theorem B2198595 : Blo 2197435 2198595 := bstep (se 1 (by rfl) ⟨1648946, by rfl⟩ : syracuseStep 2198595 = 3297893) B3297893
theorem B3130429 : Blo 2197435 3130429 := bbase (se 3 (by rfl) ⟨586955, by rfl⟩ : syracuseStep 3130429 = 1173911) (by norm_num)
theorem B4173905 : Blo 2197435 4173905 := bstep (se 2 (by rfl) ⟨1565214, by rfl⟩ : syracuseStep 4173905 = 3130429) B3130429
theorem B2782603 : Blo 2197435 2782603 := bstep (se 1 (by rfl) ⟨2086952, by rfl⟩ : syracuseStep 2782603 = 4173905) B4173905
theorem B3710137 : Blo 2197435 3710137 := bstep (se 2 (by rfl) ⟨1391301, by rfl⟩ : syracuseStep 3710137 = 2782603) B2782603
theorem B4946849 : Blo 2197435 4946849 := bstep (se 2 (by rfl) ⟨1855068, by rfl⟩ : syracuseStep 4946849 = 3710137) B3710137
theorem B3297899 : Blo 2197435 3297899 := bstep (se 1 (by rfl) ⟨2473424, by rfl⟩ : syracuseStep 3297899 = 4946849) B4946849
theorem B2198599 : Blo 2197435 2198599 := bstep (se 1 (by rfl) ⟨1648949, by rfl⟩ : syracuseStep 2198599 = 3297899) B3297899
theorem B2473429 : Blo 2197435 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B3297905 : Blo 2197435 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B2198603 : Blo 2197435 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B2782613 : Blo 2197435 2782613 := bbase (se 6 (by rfl) ⟨65217, by rfl⟩ : syracuseStep 2782613 = 130435) (by norm_num)
theorem B7420301 : Blo 2197435 7420301 := bstep (se 3 (by rfl) ⟨1391306, by rfl⟩ : syracuseStep 7420301 = 2782613) B2782613
theorem B4946867 : Blo 2197435 4946867 := bstep (se 1 (by rfl) ⟨3710150, by rfl⟩ : syracuseStep 4946867 = 7420301) B7420301
theorem B3297911 : Blo 2197435 3297911 := bstep (se 1 (by rfl) ⟨2473433, by rfl⟩ : syracuseStep 3297911 = 4946867) B4946867
theorem B2198607 : Blo 2197435 2198607 := bstep (se 1 (by rfl) ⟨1648955, by rfl⟩ : syracuseStep 2198607 = 3297911) B3297911
theorem B3297917 : Blo 2197435 3297917 := bbase (se 3 (by rfl) ⟨618359, by rfl⟩ : syracuseStep 3297917 = 1236719) (by norm_num)
theorem B2198611 : Blo 2197435 2198611 := bstep (se 1 (by rfl) ⟨1648958, by rfl⟩ : syracuseStep 2198611 = 3297917) B3297917
theorem B4946885 : Blo 2197435 4946885 := bbase (se 4 (by rfl) ⟨463770, by rfl⟩ : syracuseStep 4946885 = 927541) (by norm_num)
theorem B3297923 : Blo 2197435 3297923 := bstep (se 1 (by rfl) ⟨2473442, by rfl⟩ : syracuseStep 3297923 = 4946885) B4946885
theorem B2198615 : Blo 2197435 2198615 := bstep (se 1 (by rfl) ⟨1648961, by rfl⟩ : syracuseStep 2198615 = 3297923) B3297923
theorem B3521765 : Blo 2197435 3521765 := bbase (se 4 (by rfl) ⟨330165, by rfl⟩ : syracuseStep 3521765 = 660331) (by norm_num)
theorem B9391373 : Blo 2197435 9391373 := bstep (se 3 (by rfl) ⟨1760882, by rfl⟩ : syracuseStep 9391373 = 3521765) B3521765
theorem B6260915 : Blo 2197435 6260915 := bstep (se 1 (by rfl) ⟨4695686, by rfl⟩ : syracuseStep 6260915 = 9391373) B9391373
theorem B4173943 : Blo 2197435 4173943 := bstep (se 1 (by rfl) ⟨3130457, by rfl⟩ : syracuseStep 4173943 = 6260915) B6260915
theorem B5565257 : Blo 2197435 5565257 := bstep (se 2 (by rfl) ⟨2086971, by rfl⟩ : syracuseStep 5565257 = 4173943) B4173943
theorem B3710171 : Blo 2197435 3710171 := bstep (se 1 (by rfl) ⟨2782628, by rfl⟩ : syracuseStep 3710171 = 5565257) B5565257
theorem B2473447 : Blo 2197435 2473447 := bstep (se 1 (by rfl) ⟨1855085, by rfl⟩ : syracuseStep 2473447 = 3710171) B3710171
theorem B3297929 : Blo 2197435 3297929 := bstep (se 2 (by rfl) ⟨1236723, by rfl⟩ : syracuseStep 3297929 = 2473447) B2473447
theorem B2198619 : Blo 2197435 2198619 := bstep (se 1 (by rfl) ⟨1648964, by rfl⟩ : syracuseStep 2198619 = 3297929) B3297929
theorem B11130533 : Blo 2197435 11130533 := bbase (se 4 (by rfl) ⟨1043487, by rfl⟩ : syracuseStep 11130533 = 2086975) (by norm_num)
theorem B7420355 : Blo 2197435 7420355 := bstep (se 1 (by rfl) ⟨5565266, by rfl⟩ : syracuseStep 7420355 = 11130533) B11130533
theorem B4946903 : Blo 2197435 4946903 := bstep (se 1 (by rfl) ⟨3710177, by rfl⟩ : syracuseStep 4946903 = 7420355) B7420355
theorem B3297935 : Blo 2197435 3297935 := bstep (se 1 (by rfl) ⟨2473451, by rfl⟩ : syracuseStep 3297935 = 4946903) B4946903
theorem B2198623 : Blo 2197435 2198623 := bstep (se 1 (by rfl) ⟨1648967, by rfl⟩ : syracuseStep 2198623 = 3297935) B3297935
theorem B3297941 : Blo 2197435 3297941 := bbase (se 6 (by rfl) ⟨77295, by rfl⟩ : syracuseStep 3297941 = 154591) (by norm_num)
theorem B2198627 : Blo 2197435 2198627 := bstep (se 1 (by rfl) ⟨1648970, by rfl⟩ : syracuseStep 2198627 = 3297941) B3297941
theorem B21418997 : Blo 2197435 21418997 := bbase (se 5 (by rfl) ⟨1004015, by rfl⟩ : syracuseStep 21418997 = 2008031) (by norm_num)
theorem B57117325 : Blo 2197435 57117325 := bstep (se 3 (by rfl) ⟨10709498, by rfl⟩ : syracuseStep 57117325 = 21418997) B21418997
theorem B76156433 : Blo 2197435 76156433 := bstep (se 2 (by rfl) ⟨28558662, by rfl⟩ : syracuseStep 76156433 = 57117325) B57117325
theorem B50770955 : Blo 2197435 50770955 := bstep (se 1 (by rfl) ⟨38078216, by rfl⟩ : syracuseStep 50770955 = 76156433) B76156433
theorem B33847303 : Blo 2197435 33847303 := bstep (se 1 (by rfl) ⟨25385477, by rfl⟩ : syracuseStep 33847303 = 50770955) B50770955
theorem B45129737 : Blo 2197435 45129737 := bstep (se 2 (by rfl) ⟨16923651, by rfl⟩ : syracuseStep 45129737 = 33847303) B33847303
theorem B30086491 : Blo 2197435 30086491 := bstep (se 1 (by rfl) ⟨22564868, by rfl⟩ : syracuseStep 30086491 = 45129737) B45129737
theorem B40115321 : Blo 2197435 40115321 := bstep (se 2 (by rfl) ⟨15043245, by rfl⟩ : syracuseStep 40115321 = 30086491) B30086491
theorem B26743547 : Blo 2197435 26743547 := bstep (se 1 (by rfl) ⟨20057660, by rfl⟩ : syracuseStep 26743547 = 40115321) B40115321
theorem B71316125 : Blo 2197435 71316125 := bstep (se 3 (by rfl) ⟨13371773, by rfl⟩ : syracuseStep 71316125 = 26743547) B26743547
theorem B47544083 : Blo 2197435 47544083 := bstep (se 1 (by rfl) ⟨35658062, by rfl⟩ : syracuseStep 47544083 = 71316125) B71316125
theorem B31696055 : Blo 2197435 31696055 := bstep (se 1 (by rfl) ⟨23772041, by rfl⟩ : syracuseStep 31696055 = 47544083) B47544083
theorem B21130703 : Blo 2197435 21130703 := bstep (se 1 (by rfl) ⟨15848027, by rfl⟩ : syracuseStep 21130703 = 31696055) B31696055
theorem B14087135 : Blo 2197435 14087135 := bstep (se 1 (by rfl) ⟨10565351, by rfl⟩ : syracuseStep 14087135 = 21130703) B21130703
theorem B9391423 : Blo 2197435 9391423 := bstep (se 1 (by rfl) ⟨7043567, by rfl⟩ : syracuseStep 9391423 = 14087135) B14087135
theorem B12521897 : Blo 2197435 12521897 := bstep (se 2 (by rfl) ⟨4695711, by rfl⟩ : syracuseStep 12521897 = 9391423) B9391423
theorem B8347931 : Blo 2197435 8347931 := bstep (se 1 (by rfl) ⟨6260948, by rfl⟩ : syracuseStep 8347931 = 12521897) B12521897
theorem B5565287 : Blo 2197435 5565287 := bstep (se 1 (by rfl) ⟨4173965, by rfl⟩ : syracuseStep 5565287 = 8347931) B8347931
theorem B3710191 : Blo 2197435 3710191 := bstep (se 1 (by rfl) ⟨2782643, by rfl⟩ : syracuseStep 3710191 = 5565287) B5565287
theorem B4946921 : Blo 2197435 4946921 := bstep (se 2 (by rfl) ⟨1855095, by rfl⟩ : syracuseStep 4946921 = 3710191) B3710191
theorem B3297947 : Blo 2197435 3297947 := bstep (se 1 (by rfl) ⟨2473460, by rfl⟩ : syracuseStep 3297947 = 4946921) B4946921
theorem B2198631 : Blo 2197435 2198631 := bstep (se 1 (by rfl) ⟨1648973, by rfl⟩ : syracuseStep 2198631 = 3297947) B3297947
theorem B2473465 : Blo 2197435 2473465 := bbase (se 2 (by rfl) ⟨927549, by rfl⟩ : syracuseStep 2473465 = 1855099) (by norm_num)
theorem B3297953 : Blo 2197435 3297953 := bstep (se 2 (by rfl) ⟨1236732, by rfl⟩ : syracuseStep 3297953 = 2473465) B2473465
theorem B2198635 : Blo 2197435 2198635 := bstep (se 1 (by rfl) ⟨1648976, by rfl⟩ : syracuseStep 2198635 = 3297953) B3297953
theorem B8914549 : Blo 2197435 8914549 := bbase (se 5 (by rfl) ⟨417869, by rfl⟩ : syracuseStep 8914549 = 835739) (by norm_num)
theorem B11886065 : Blo 2197435 11886065 := bstep (se 2 (by rfl) ⟨4457274, by rfl⟩ : syracuseStep 11886065 = 8914549) B8914549
theorem B7924043 : Blo 2197435 7924043 := bstep (se 1 (by rfl) ⟨5943032, by rfl⟩ : syracuseStep 7924043 = 11886065) B11886065
theorem B5282695 : Blo 2197435 5282695 := bstep (se 1 (by rfl) ⟨3962021, by rfl⟩ : syracuseStep 5282695 = 7924043) B7924043
theorem B7043593 : Blo 2197435 7043593 := bstep (se 2 (by rfl) ⟨2641347, by rfl⟩ : syracuseStep 7043593 = 5282695) B5282695
theorem B9391457 : Blo 2197435 9391457 := bstep (se 2 (by rfl) ⟨3521796, by rfl⟩ : syracuseStep 9391457 = 7043593) B7043593
theorem B6260971 : Blo 2197435 6260971 := bstep (se 1 (by rfl) ⟨4695728, by rfl⟩ : syracuseStep 6260971 = 9391457) B9391457
theorem B8347961 : Blo 2197435 8347961 := bstep (se 2 (by rfl) ⟨3130485, by rfl⟩ : syracuseStep 8347961 = 6260971) B6260971
theorem B5565307 : Blo 2197435 5565307 := bstep (se 1 (by rfl) ⟨4173980, by rfl⟩ : syracuseStep 5565307 = 8347961) B8347961
theorem B7420409 : Blo 2197435 7420409 := bstep (se 2 (by rfl) ⟨2782653, by rfl⟩ : syracuseStep 7420409 = 5565307) B5565307
theorem B4946939 : Blo 2197435 4946939 := bstep (se 1 (by rfl) ⟨3710204, by rfl⟩ : syracuseStep 4946939 = 7420409) B7420409
theorem B3297959 : Blo 2197435 3297959 := bstep (se 1 (by rfl) ⟨2473469, by rfl⟩ : syracuseStep 3297959 = 4946939) B4946939
theorem B2198639 : Blo 2197435 2198639 := bstep (se 1 (by rfl) ⟨1648979, by rfl⟩ : syracuseStep 2198639 = 3297959) B3297959
theorem B3297965 : Blo 2197435 3297965 := bbase (se 3 (by rfl) ⟨618368, by rfl⟩ : syracuseStep 3297965 = 1236737) (by norm_num)
theorem B2198643 : Blo 2197435 2198643 := bstep (se 1 (by rfl) ⟨1648982, by rfl⟩ : syracuseStep 2198643 = 3297965) B3297965
theorem B4946957 : Blo 2197435 4946957 := bbase (se 3 (by rfl) ⟨927554, by rfl⟩ : syracuseStep 4946957 = 1855109) (by norm_num)
theorem B3297971 : Blo 2197435 3297971 := bstep (se 1 (by rfl) ⟨2473478, by rfl⟩ : syracuseStep 3297971 = 4946957) B4946957
theorem B2198647 : Blo 2197435 2198647 := bstep (se 1 (by rfl) ⟨1648985, by rfl⟩ : syracuseStep 2198647 = 3297971) B3297971
theorem B2782669 : Blo 2197435 2782669 := bbase (se 3 (by rfl) ⟨521750, by rfl⟩ : syracuseStep 2782669 = 1043501) (by norm_num)
theorem B3710225 : Blo 2197435 3710225 := bstep (se 2 (by rfl) ⟨1391334, by rfl⟩ : syracuseStep 3710225 = 2782669) B2782669
theorem B2473483 : Blo 2197435 2473483 := bstep (se 1 (by rfl) ⟨1855112, by rfl⟩ : syracuseStep 2473483 = 3710225) B3710225
theorem B3297977 : Blo 2197435 3297977 := bstep (se 2 (by rfl) ⟨1236741, by rfl⟩ : syracuseStep 3297977 = 2473483) B2473483
theorem B2198651 : Blo 2197435 2198651 := bstep (se 1 (by rfl) ⟨1648988, by rfl⟩ : syracuseStep 2198651 = 3297977) B3297977
theorem B2228653 : Blo 2197435 2228653 := bbase (se 3 (by rfl) ⟨417872, by rfl⟩ : syracuseStep 2228653 = 835745) (by norm_num)
theorem B11886149 : Blo 2197435 11886149 := bstep (se 4 (by rfl) ⟨1114326, by rfl⟩ : syracuseStep 11886149 = 2228653) B2228653
theorem B31696397 : Blo 2197435 31696397 := bstep (se 3 (by rfl) ⟨5943074, by rfl⟩ : syracuseStep 31696397 = 11886149) B11886149
theorem B21130931 : Blo 2197435 21130931 := bstep (se 1 (by rfl) ⟨15848198, by rfl⟩ : syracuseStep 21130931 = 31696397) B31696397
theorem B14087287 : Blo 2197435 14087287 := bstep (se 1 (by rfl) ⟨10565465, by rfl⟩ : syracuseStep 14087287 = 21130931) B21130931
theorem B18783049 : Blo 2197435 18783049 := bstep (se 2 (by rfl) ⟨7043643, by rfl⟩ : syracuseStep 18783049 = 14087287) B14087287
theorem B25044065 : Blo 2197435 25044065 := bstep (se 2 (by rfl) ⟨9391524, by rfl⟩ : syracuseStep 25044065 = 18783049) B18783049
theorem B16696043 : Blo 2197435 16696043 := bstep (se 1 (by rfl) ⟨12522032, by rfl⟩ : syracuseStep 16696043 = 25044065) B25044065
theorem B11130695 : Blo 2197435 11130695 := bstep (se 1 (by rfl) ⟨8348021, by rfl⟩ : syracuseStep 11130695 = 16696043) B16696043
theorem B7420463 : Blo 2197435 7420463 := bstep (se 1 (by rfl) ⟨5565347, by rfl⟩ : syracuseStep 7420463 = 11130695) B11130695
theorem B4946975 : Blo 2197435 4946975 := bstep (se 1 (by rfl) ⟨3710231, by rfl⟩ : syracuseStep 4946975 = 7420463) B7420463
theorem B3297983 : Blo 2197435 3297983 := bstep (se 1 (by rfl) ⟨2473487, by rfl⟩ : syracuseStep 3297983 = 4946975) B4946975
theorem B2198655 : Blo 2197435 2198655 := bstep (se 1 (by rfl) ⟨1648991, by rfl⟩ : syracuseStep 2198655 = 3297983) B3297983
theorem B3297989 : Blo 2197435 3297989 := bbase (se 4 (by rfl) ⟨309186, by rfl⟩ : syracuseStep 3297989 = 618373) (by norm_num)
theorem B2198659 : Blo 2197435 2198659 := bstep (se 1 (by rfl) ⟨1648994, by rfl⟩ : syracuseStep 2198659 = 3297989) B3297989
theorem B3710245 : Blo 2197435 3710245 := bbase (se 4 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 3710245 = 695671) (by norm_num)
theorem B4946993 : Blo 2197435 4946993 := bstep (se 2 (by rfl) ⟨1855122, by rfl⟩ : syracuseStep 4946993 = 3710245) B3710245
theorem B3297995 : Blo 2197435 3297995 := bstep (se 1 (by rfl) ⟨2473496, by rfl⟩ : syracuseStep 3297995 = 4946993) B4946993
theorem B2198663 : Blo 2197435 2198663 := bstep (se 1 (by rfl) ⟨1648997, by rfl⟩ : syracuseStep 2198663 = 3297995) B3297995
theorem B2473501 : Blo 2197435 2473501 := bbase (se 3 (by rfl) ⟨463781, by rfl⟩ : syracuseStep 2473501 = 927563) (by norm_num)
theorem B3298001 : Blo 2197435 3298001 := bstep (se 2 (by rfl) ⟨1236750, by rfl⟩ : syracuseStep 3298001 = 2473501) B2473501
theorem B2198667 : Blo 2197435 2198667 := bstep (se 1 (by rfl) ⟨1649000, by rfl⟩ : syracuseStep 2198667 = 3298001) B3298001
theorem B7420517 : Blo 2197435 7420517 := bbase (se 4 (by rfl) ⟨695673, by rfl⟩ : syracuseStep 7420517 = 1391347) (by norm_num)
theorem B4947011 : Blo 2197435 4947011 := bstep (se 1 (by rfl) ⟨3710258, by rfl⟩ : syracuseStep 4947011 = 7420517) B7420517
theorem B3298007 : Blo 2197435 3298007 := bstep (se 1 (by rfl) ⟨2473505, by rfl⟩ : syracuseStep 3298007 = 4947011) B4947011
theorem B2198671 : Blo 2197435 2198671 := bstep (se 1 (by rfl) ⟨1649003, by rfl⟩ : syracuseStep 2198671 = 3298007) B3298007
theorem B3298013 : Blo 2197435 3298013 := bbase (se 3 (by rfl) ⟨618377, by rfl⟩ : syracuseStep 3298013 = 1236755) (by norm_num)
theorem B2198675 : Blo 2197435 2198675 := bstep (se 1 (by rfl) ⟨1649006, by rfl⟩ : syracuseStep 2198675 = 3298013) B3298013
theorem B4947029 : Blo 2197435 4947029 := bbase (se 8 (by rfl) ⟨28986, by rfl⟩ : syracuseStep 4947029 = 57973) (by norm_num)
theorem B3298019 : Blo 2197435 3298019 := bstep (se 1 (by rfl) ⟨2473514, by rfl⟩ : syracuseStep 3298019 = 4947029) B4947029
theorem B2198679 : Blo 2197435 2198679 := bstep (se 1 (by rfl) ⟨1649009, by rfl⟩ : syracuseStep 2198679 = 3298019) B3298019
theorem B15848405 : Blo 2197435 15848405 := bbase (se 7 (by rfl) ⟨185723, by rfl⟩ : syracuseStep 15848405 = 371447) (by norm_num)
theorem B10565603 : Blo 2197435 10565603 := bstep (se 1 (by rfl) ⟨7924202, by rfl⟩ : syracuseStep 10565603 = 15848405) B15848405
theorem B7043735 : Blo 2197435 7043735 := bstep (se 1 (by rfl) ⟨5282801, by rfl⟩ : syracuseStep 7043735 = 10565603) B10565603
theorem B4695823 : Blo 2197435 4695823 := bstep (se 1 (by rfl) ⟨3521867, by rfl⟩ : syracuseStep 4695823 = 7043735) B7043735
theorem B6261097 : Blo 2197435 6261097 := bstep (se 2 (by rfl) ⟨2347911, by rfl⟩ : syracuseStep 6261097 = 4695823) B4695823
theorem B8348129 : Blo 2197435 8348129 := bstep (se 2 (by rfl) ⟨3130548, by rfl⟩ : syracuseStep 8348129 = 6261097) B6261097
theorem B5565419 : Blo 2197435 5565419 := bstep (se 1 (by rfl) ⟨4174064, by rfl⟩ : syracuseStep 5565419 = 8348129) B8348129
theorem B3710279 : Blo 2197435 3710279 := bstep (se 1 (by rfl) ⟨2782709, by rfl⟩ : syracuseStep 3710279 = 5565419) B5565419
theorem B2473519 : Blo 2197435 2473519 := bstep (se 1 (by rfl) ⟨1855139, by rfl⟩ : syracuseStep 2473519 = 3710279) B3710279
theorem B3298025 : Blo 2197435 3298025 := bstep (se 2 (by rfl) ⟨1236759, by rfl⟩ : syracuseStep 3298025 = 2473519) B2473519
theorem B2198683 : Blo 2197435 2198683 := bstep (se 1 (by rfl) ⟨1649012, by rfl⟩ : syracuseStep 2198683 = 3298025) B3298025
theorem B2379949 : Blo 2197435 2379949 := bbase (se 3 (by rfl) ⟨446240, by rfl⟩ : syracuseStep 2379949 = 892481) (by norm_num)
theorem B12693061 : Blo 2197435 12693061 := bstep (se 4 (by rfl) ⟨1189974, by rfl⟩ : syracuseStep 12693061 = 2379949) B2379949
theorem B16924081 : Blo 2197435 16924081 := bstep (se 2 (by rfl) ⟨6346530, by rfl⟩ : syracuseStep 16924081 = 12693061) B12693061
theorem B22565441 : Blo 2197435 22565441 := bstep (se 2 (by rfl) ⟨8462040, by rfl⟩ : syracuseStep 22565441 = 16924081) B16924081
theorem B15043627 : Blo 2197435 15043627 := bstep (se 1 (by rfl) ⟨11282720, by rfl⟩ : syracuseStep 15043627 = 22565441) B22565441
theorem B80232677 : Blo 2197435 80232677 := bstep (se 4 (by rfl) ⟨7521813, by rfl⟩ : syracuseStep 80232677 = 15043627) B15043627
theorem B53488451 : Blo 2197435 53488451 := bstep (se 1 (by rfl) ⟨40116338, by rfl⟩ : syracuseStep 53488451 = 80232677) B80232677
theorem B35658967 : Blo 2197435 35658967 := bstep (se 1 (by rfl) ⟨26744225, by rfl⟩ : syracuseStep 35658967 = 53488451) B53488451
theorem B47545289 : Blo 2197435 47545289 := bstep (se 2 (by rfl) ⟨17829483, by rfl⟩ : syracuseStep 47545289 = 35658967) B35658967
theorem B31696859 : Blo 2197435 31696859 := bstep (se 1 (by rfl) ⟨23772644, by rfl⟩ : syracuseStep 31696859 = 47545289) B47545289
theorem B21131239 : Blo 2197435 21131239 := bstep (se 1 (by rfl) ⟨15848429, by rfl⟩ : syracuseStep 21131239 = 31696859) B31696859
theorem B28174985 : Blo 2197435 28174985 := bstep (se 2 (by rfl) ⟨10565619, by rfl⟩ : syracuseStep 28174985 = 21131239) B21131239
theorem B18783323 : Blo 2197435 18783323 := bstep (se 1 (by rfl) ⟨14087492, by rfl⟩ : syracuseStep 18783323 = 28174985) B28174985
theorem B12522215 : Blo 2197435 12522215 := bstep (se 1 (by rfl) ⟨9391661, by rfl⟩ : syracuseStep 12522215 = 18783323) B18783323
theorem B8348143 : Blo 2197435 8348143 := bstep (se 1 (by rfl) ⟨6261107, by rfl⟩ : syracuseStep 8348143 = 12522215) B12522215
theorem B11130857 : Blo 2197435 11130857 := bstep (se 2 (by rfl) ⟨4174071, by rfl⟩ : syracuseStep 11130857 = 8348143) B8348143
theorem B7420571 : Blo 2197435 7420571 := bstep (se 1 (by rfl) ⟨5565428, by rfl⟩ : syracuseStep 7420571 = 11130857) B11130857
theorem B4947047 : Blo 2197435 4947047 := bstep (se 1 (by rfl) ⟨3710285, by rfl⟩ : syracuseStep 4947047 = 7420571) B7420571
theorem B3298031 : Blo 2197435 3298031 := bstep (se 1 (by rfl) ⟨2473523, by rfl⟩ : syracuseStep 3298031 = 4947047) B4947047
theorem B2198687 : Blo 2197435 2198687 := bstep (se 1 (by rfl) ⟨1649015, by rfl⟩ : syracuseStep 2198687 = 3298031) B3298031
theorem B3298037 : Blo 2197435 3298037 := bbase (se 5 (by rfl) ⟨154595, by rfl⟩ : syracuseStep 3298037 = 309191) (by norm_num)
theorem B2198691 : Blo 2197435 2198691 := bstep (se 1 (by rfl) ⟨1649018, by rfl⟩ : syracuseStep 2198691 = 3298037) B3298037
theorem B4457389 : Blo 2197435 4457389 := bbase (se 3 (by rfl) ⟨835760, by rfl⟩ : syracuseStep 4457389 = 1671521) (by norm_num)
theorem B5943185 : Blo 2197435 5943185 := bstep (se 2 (by rfl) ⟨2228694, by rfl⟩ : syracuseStep 5943185 = 4457389) B4457389
theorem B3962123 : Blo 2197435 3962123 := bstep (se 1 (by rfl) ⟨2971592, by rfl⟩ : syracuseStep 3962123 = 5943185) B5943185
theorem B2641415 : Blo 2197435 2641415 := bstep (se 1 (by rfl) ⟨1981061, by rfl⟩ : syracuseStep 2641415 = 3962123) B3962123
theorem B7043773 : Blo 2197435 7043773 := bstep (se 3 (by rfl) ⟨1320707, by rfl⟩ : syracuseStep 7043773 = 2641415) B2641415
theorem B9391697 : Blo 2197435 9391697 := bstep (se 2 (by rfl) ⟨3521886, by rfl⟩ : syracuseStep 9391697 = 7043773) B7043773
theorem B6261131 : Blo 2197435 6261131 := bstep (se 1 (by rfl) ⟨4695848, by rfl⟩ : syracuseStep 6261131 = 9391697) B9391697
theorem B4174087 : Blo 2197435 4174087 := bstep (se 1 (by rfl) ⟨3130565, by rfl⟩ : syracuseStep 4174087 = 6261131) B6261131
theorem B5565449 : Blo 2197435 5565449 := bstep (se 2 (by rfl) ⟨2087043, by rfl⟩ : syracuseStep 5565449 = 4174087) B4174087
theorem B3710299 : Blo 2197435 3710299 := bstep (se 1 (by rfl) ⟨2782724, by rfl⟩ : syracuseStep 3710299 = 5565449) B5565449
theorem B4947065 : Blo 2197435 4947065 := bstep (se 2 (by rfl) ⟨1855149, by rfl⟩ : syracuseStep 4947065 = 3710299) B3710299
theorem B3298043 : Blo 2197435 3298043 := bstep (se 1 (by rfl) ⟨2473532, by rfl⟩ : syracuseStep 3298043 = 4947065) B4947065
theorem B2198695 : Blo 2197435 2198695 := bstep (se 1 (by rfl) ⟨1649021, by rfl⟩ : syracuseStep 2198695 = 3298043) B3298043
theorem B2473537 : Blo 2197435 2473537 := bbase (se 2 (by rfl) ⟨927576, by rfl⟩ : syracuseStep 2473537 = 1855153) (by norm_num)
theorem B3298049 : Blo 2197435 3298049 := bstep (se 2 (by rfl) ⟨1236768, by rfl⟩ : syracuseStep 3298049 = 2473537) B2473537
theorem B2198699 : Blo 2197435 2198699 := bstep (se 1 (by rfl) ⟨1649024, by rfl⟩ : syracuseStep 2198699 = 3298049) B3298049
theorem B5565469 : Blo 2197435 5565469 := bbase (se 3 (by rfl) ⟨1043525, by rfl⟩ : syracuseStep 5565469 = 2087051) (by norm_num)
theorem B7420625 : Blo 2197435 7420625 := bstep (se 2 (by rfl) ⟨2782734, by rfl⟩ : syracuseStep 7420625 = 5565469) B5565469
theorem B4947083 : Blo 2197435 4947083 := bstep (se 1 (by rfl) ⟨3710312, by rfl⟩ : syracuseStep 4947083 = 7420625) B7420625
theorem B3298055 : Blo 2197435 3298055 := bstep (se 1 (by rfl) ⟨2473541, by rfl⟩ : syracuseStep 3298055 = 4947083) B4947083
theorem B2198703 : Blo 2197435 2198703 := bstep (se 1 (by rfl) ⟨1649027, by rfl⟩ : syracuseStep 2198703 = 3298055) B3298055
theorem B3298061 : Blo 2197435 3298061 := bbase (se 3 (by rfl) ⟨618386, by rfl⟩ : syracuseStep 3298061 = 1236773) (by norm_num)
theorem B2198707 : Blo 2197435 2198707 := bstep (se 1 (by rfl) ⟨1649030, by rfl⟩ : syracuseStep 2198707 = 3298061) B3298061
theorem B4947101 : Blo 2197435 4947101 := bbase (se 3 (by rfl) ⟨927581, by rfl⟩ : syracuseStep 4947101 = 1855163) (by norm_num)
theorem B3298067 : Blo 2197435 3298067 := bstep (se 1 (by rfl) ⟨2473550, by rfl⟩ : syracuseStep 3298067 = 4947101) B4947101
theorem B2198711 : Blo 2197435 2198711 := bstep (se 1 (by rfl) ⟨1649033, by rfl⟩ : syracuseStep 2198711 = 3298067) B3298067
theorem B3710333 : Blo 2197435 3710333 := bbase (se 3 (by rfl) ⟨695687, by rfl⟩ : syracuseStep 3710333 = 1391375) (by norm_num)
theorem B2473555 : Blo 2197435 2473555 := bstep (se 1 (by rfl) ⟨1855166, by rfl⟩ : syracuseStep 2473555 = 3710333) B3710333
theorem B3298073 : Blo 2197435 3298073 := bstep (se 2 (by rfl) ⟨1236777, by rfl⟩ : syracuseStep 3298073 = 2473555) B2473555
theorem B2198715 : Blo 2197435 2198715 := bstep (se 1 (by rfl) ⟨1649036, by rfl⟩ : syracuseStep 2198715 = 3298073) B3298073
theorem B7521925 : Blo 2197435 7521925 := bbase (se 4 (by rfl) ⟨705180, by rfl⟩ : syracuseStep 7521925 = 1410361) (by norm_num)
theorem B10029233 : Blo 2197435 10029233 := bstep (se 2 (by rfl) ⟨3760962, by rfl⟩ : syracuseStep 10029233 = 7521925) B7521925
theorem B6686155 : Blo 2197435 6686155 := bstep (se 1 (by rfl) ⟨5014616, by rfl⟩ : syracuseStep 6686155 = 10029233) B10029233
theorem B8914873 : Blo 2197435 8914873 := bstep (se 2 (by rfl) ⟨3343077, by rfl⟩ : syracuseStep 8914873 = 6686155) B6686155
theorem B11886497 : Blo 2197435 11886497 := bstep (se 2 (by rfl) ⟨4457436, by rfl⟩ : syracuseStep 11886497 = 8914873) B8914873
theorem B7924331 : Blo 2197435 7924331 := bstep (se 1 (by rfl) ⟨5943248, by rfl⟩ : syracuseStep 7924331 = 11886497) B11886497
theorem B5282887 : Blo 2197435 5282887 := bstep (se 1 (by rfl) ⟨3962165, by rfl⟩ : syracuseStep 5282887 = 7924331) B7924331
theorem B7043849 : Blo 2197435 7043849 := bstep (se 2 (by rfl) ⟨2641443, by rfl⟩ : syracuseStep 7043849 = 5282887) B5282887
theorem B4695899 : Blo 2197435 4695899 := bstep (se 1 (by rfl) ⟨3521924, by rfl⟩ : syracuseStep 4695899 = 7043849) B7043849
theorem B12522397 : Blo 2197435 12522397 := bstep (se 3 (by rfl) ⟨2347949, by rfl⟩ : syracuseStep 12522397 = 4695899) B4695899
theorem B16696529 : Blo 2197435 16696529 := bstep (se 2 (by rfl) ⟨6261198, by rfl⟩ : syracuseStep 16696529 = 12522397) B12522397
theorem B11131019 : Blo 2197435 11131019 := bstep (se 1 (by rfl) ⟨8348264, by rfl⟩ : syracuseStep 11131019 = 16696529) B16696529
theorem B7420679 : Blo 2197435 7420679 := bstep (se 1 (by rfl) ⟨5565509, by rfl⟩ : syracuseStep 7420679 = 11131019) B11131019
theorem B4947119 : Blo 2197435 4947119 := bstep (se 1 (by rfl) ⟨3710339, by rfl⟩ : syracuseStep 4947119 = 7420679) B7420679
theorem B3298079 : Blo 2197435 3298079 := bstep (se 1 (by rfl) ⟨2473559, by rfl⟩ : syracuseStep 3298079 = 4947119) B4947119
theorem B2198719 : Blo 2197435 2198719 := bstep (se 1 (by rfl) ⟨1649039, by rfl⟩ : syracuseStep 2198719 = 3298079) B3298079
theorem B3298085 : Blo 2197435 3298085 := bbase (se 4 (by rfl) ⟨309195, by rfl⟩ : syracuseStep 3298085 = 618391) (by norm_num)
theorem B2198723 : Blo 2197435 2198723 := bstep (se 1 (by rfl) ⟨1649042, by rfl⟩ : syracuseStep 2198723 = 3298085) B3298085
theorem B2782765 : Blo 2197435 2782765 := bbase (se 3 (by rfl) ⟨521768, by rfl⟩ : syracuseStep 2782765 = 1043537) (by norm_num)
theorem B3710353 : Blo 2197435 3710353 := bstep (se 2 (by rfl) ⟨1391382, by rfl⟩ : syracuseStep 3710353 = 2782765) B2782765
theorem B4947137 : Blo 2197435 4947137 := bstep (se 2 (by rfl) ⟨1855176, by rfl⟩ : syracuseStep 4947137 = 3710353) B3710353
theorem B3298091 : Blo 2197435 3298091 := bstep (se 1 (by rfl) ⟨2473568, by rfl⟩ : syracuseStep 3298091 = 4947137) B4947137
theorem B2198727 : Blo 2197435 2198727 := bstep (se 1 (by rfl) ⟨1649045, by rfl⟩ : syracuseStep 2198727 = 3298091) B3298091
theorem B2473573 : Blo 2197435 2473573 := bbase (se 4 (by rfl) ⟨231897, by rfl⟩ : syracuseStep 2473573 = 463795) (by norm_num)
theorem B3298097 : Blo 2197435 3298097 := bstep (se 2 (by rfl) ⟨1236786, by rfl⟩ : syracuseStep 3298097 = 2473573) B2473573
theorem B2198731 : Blo 2197435 2198731 := bstep (se 1 (by rfl) ⟨1649048, by rfl⟩ : syracuseStep 2198731 = 3298097) B3298097
theorem B5355005 : Blo 2197435 5355005 := bbase (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) (by norm_num)
theorem B14280013 : Blo 2197435 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B19040017 : Blo 2197435 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B25386689 : Blo 2197435 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B16924459 : Blo 2197435 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B22565945 : Blo 2197435 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B15043963 : Blo 2197435 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B20058617 : Blo 2197435 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B13372411 : Blo 2197435 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B17829881 : Blo 2197435 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B11886587 : Blo 2197435 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B7924391 : Blo 2197435 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B5282927 : Blo 2197435 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B3521951 : Blo 2197435 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B2347967 : Blo 2197435 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B6261245 : Blo 2197435 6261245 := bstep (se 3 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 6261245 = 2347967) B2347967
theorem B4174163 : Blo 2197435 4174163 := bstep (se 1 (by rfl) ⟨3130622, by rfl⟩ : syracuseStep 4174163 = 6261245) B6261245
theorem B2782775 : Blo 2197435 2782775 := bstep (se 1 (by rfl) ⟨2087081, by rfl⟩ : syracuseStep 2782775 = 4174163) B4174163
theorem B7420733 : Blo 2197435 7420733 := bstep (se 3 (by rfl) ⟨1391387, by rfl⟩ : syracuseStep 7420733 = 2782775) B2782775
theorem B4947155 : Blo 2197435 4947155 := bstep (se 1 (by rfl) ⟨3710366, by rfl⟩ : syracuseStep 4947155 = 7420733) B7420733
theorem B3298103 : Blo 2197435 3298103 := bstep (se 1 (by rfl) ⟨2473577, by rfl⟩ : syracuseStep 3298103 = 4947155) B4947155
theorem B2198735 : Blo 2197435 2198735 := bstep (se 1 (by rfl) ⟨1649051, by rfl⟩ : syracuseStep 2198735 = 3298103) B3298103
theorem B3298109 : Blo 2197435 3298109 := bbase (se 3 (by rfl) ⟨618395, by rfl⟩ : syracuseStep 3298109 = 1236791) (by norm_num)
theorem B2198739 : Blo 2197435 2198739 := bstep (se 1 (by rfl) ⟨1649054, by rfl⟩ : syracuseStep 2198739 = 3298109) B3298109
theorem B4947173 : Blo 2197435 4947173 := bbase (se 4 (by rfl) ⟨463797, by rfl⟩ : syracuseStep 4947173 = 927595) (by norm_num)
theorem B3298115 : Blo 2197435 3298115 := bstep (se 1 (by rfl) ⟨2473586, by rfl⟩ : syracuseStep 3298115 = 4947173) B4947173
theorem B2198743 : Blo 2197435 2198743 := bstep (se 1 (by rfl) ⟨1649057, by rfl⟩ : syracuseStep 2198743 = 3298115) B3298115
theorem B5565581 : Blo 2197435 5565581 := bbase (se 3 (by rfl) ⟨1043546, by rfl⟩ : syracuseStep 5565581 = 2087093) (by norm_num)
theorem B3710387 : Blo 2197435 3710387 := bstep (se 1 (by rfl) ⟨2782790, by rfl⟩ : syracuseStep 3710387 = 5565581) B5565581
theorem B2473591 : Blo 2197435 2473591 := bstep (se 1 (by rfl) ⟨1855193, by rfl⟩ : syracuseStep 2473591 = 3710387) B3710387
theorem B3298121 : Blo 2197435 3298121 := bstep (se 2 (by rfl) ⟨1236795, by rfl⟩ : syracuseStep 3298121 = 2473591) B2473591
theorem B2198747 : Blo 2197435 2198747 := bstep (se 1 (by rfl) ⟨1649060, by rfl⟩ : syracuseStep 2198747 = 3298121) B3298121
theorem B3130645 : Blo 2197435 3130645 := bbase (se 6 (by rfl) ⟨73374, by rfl⟩ : syracuseStep 3130645 = 146749) (by norm_num)
theorem B4174193 : Blo 2197435 4174193 := bstep (se 2 (by rfl) ⟨1565322, by rfl⟩ : syracuseStep 4174193 = 3130645) B3130645
theorem B11131181 : Blo 2197435 11131181 := bstep (se 3 (by rfl) ⟨2087096, by rfl⟩ : syracuseStep 11131181 = 4174193) B4174193
theorem B7420787 : Blo 2197435 7420787 := bstep (se 1 (by rfl) ⟨5565590, by rfl⟩ : syracuseStep 7420787 = 11131181) B11131181
theorem B4947191 : Blo 2197435 4947191 := bstep (se 1 (by rfl) ⟨3710393, by rfl⟩ : syracuseStep 4947191 = 7420787) B7420787
theorem B3298127 : Blo 2197435 3298127 := bstep (se 1 (by rfl) ⟨2473595, by rfl⟩ : syracuseStep 3298127 = 4947191) B4947191
theorem B2198751 : Blo 2197435 2198751 := bstep (se 1 (by rfl) ⟨1649063, by rfl⟩ : syracuseStep 2198751 = 3298127) B3298127
theorem B3298133 : Blo 2197435 3298133 := bbase (se 9 (by rfl) ⟨9662, by rfl⟩ : syracuseStep 3298133 = 19325) (by norm_num)
theorem B2198755 : Blo 2197435 2198755 := bstep (se 1 (by rfl) ⟨1649066, by rfl⟩ : syracuseStep 2198755 = 3298133) B3298133
theorem B3521989 : Blo 2197435 3521989 := bbase (se 4 (by rfl) ⟨330186, by rfl⟩ : syracuseStep 3521989 = 660373) (by norm_num)
theorem B4695985 : Blo 2197435 4695985 := bstep (se 2 (by rfl) ⟨1760994, by rfl⟩ : syracuseStep 4695985 = 3521989) B3521989
theorem B6261313 : Blo 2197435 6261313 := bstep (se 2 (by rfl) ⟨2347992, by rfl⟩ : syracuseStep 6261313 = 4695985) B4695985
theorem B8348417 : Blo 2197435 8348417 := bstep (se 2 (by rfl) ⟨3130656, by rfl⟩ : syracuseStep 8348417 = 6261313) B6261313
theorem B5565611 : Blo 2197435 5565611 := bstep (se 1 (by rfl) ⟨4174208, by rfl⟩ : syracuseStep 5565611 = 8348417) B8348417
theorem B3710407 : Blo 2197435 3710407 := bstep (se 1 (by rfl) ⟨2782805, by rfl⟩ : syracuseStep 3710407 = 5565611) B5565611
theorem B4947209 : Blo 2197435 4947209 := bstep (se 2 (by rfl) ⟨1855203, by rfl⟩ : syracuseStep 4947209 = 3710407) B3710407
theorem B3298139 : Blo 2197435 3298139 := bstep (se 1 (by rfl) ⟨2473604, by rfl⟩ : syracuseStep 3298139 = 4947209) B4947209
theorem B2198759 : Blo 2197435 2198759 := bstep (se 1 (by rfl) ⟨1649069, by rfl⟩ : syracuseStep 2198759 = 3298139) B3298139
theorem B2473609 : Blo 2197435 2473609 := bbase (se 2 (by rfl) ⟨927603, by rfl⟩ : syracuseStep 2473609 = 1855207) (by norm_num)
theorem B3298145 : Blo 2197435 3298145 := bstep (se 2 (by rfl) ⟨1236804, by rfl⟩ : syracuseStep 3298145 = 2473609) B2473609
theorem B2198763 : Blo 2197435 2198763 := bstep (se 1 (by rfl) ⟨1649072, by rfl⟩ : syracuseStep 2198763 = 3298145) B3298145
theorem B17830133 : Blo 2197435 17830133 := bbase (se 5 (by rfl) ⟨835787, by rfl⟩ : syracuseStep 17830133 = 1671575) (by norm_num)
theorem B11886755 : Blo 2197435 11886755 := bstep (se 1 (by rfl) ⟨8915066, by rfl⟩ : syracuseStep 11886755 = 17830133) B17830133
theorem B31698013 : Blo 2197435 31698013 := bstep (se 3 (by rfl) ⟨5943377, by rfl⟩ : syracuseStep 31698013 = 11886755) B11886755
theorem B42264017 : Blo 2197435 42264017 := bstep (se 2 (by rfl) ⟨15849006, by rfl⟩ : syracuseStep 42264017 = 31698013) B31698013
theorem B28176011 : Blo 2197435 28176011 := bstep (se 1 (by rfl) ⟨21132008, by rfl⟩ : syracuseStep 28176011 = 42264017) B42264017
theorem B18784007 : Blo 2197435 18784007 := bstep (se 1 (by rfl) ⟨14088005, by rfl⟩ : syracuseStep 18784007 = 28176011) B28176011
theorem B12522671 : Blo 2197435 12522671 := bstep (se 1 (by rfl) ⟨9392003, by rfl⟩ : syracuseStep 12522671 = 18784007) B18784007
theorem B8348447 : Blo 2197435 8348447 := bstep (se 1 (by rfl) ⟨6261335, by rfl⟩ : syracuseStep 8348447 = 12522671) B12522671
theorem B5565631 : Blo 2197435 5565631 := bstep (se 1 (by rfl) ⟨4174223, by rfl⟩ : syracuseStep 5565631 = 8348447) B8348447
theorem B7420841 : Blo 2197435 7420841 := bstep (se 2 (by rfl) ⟨2782815, by rfl⟩ : syracuseStep 7420841 = 5565631) B5565631
theorem B4947227 : Blo 2197435 4947227 := bstep (se 1 (by rfl) ⟨3710420, by rfl⟩ : syracuseStep 4947227 = 7420841) B7420841
theorem B3298151 : Blo 2197435 3298151 := bstep (se 1 (by rfl) ⟨2473613, by rfl⟩ : syracuseStep 3298151 = 4947227) B4947227
theorem B2198767 : Blo 2197435 2198767 := bstep (se 1 (by rfl) ⟨1649075, by rfl⟩ : syracuseStep 2198767 = 3298151) B3298151
theorem B3298157 : Blo 2197435 3298157 := bbase (se 3 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 3298157 = 1236809) (by norm_num)
theorem B2198771 : Blo 2197435 2198771 := bstep (se 1 (by rfl) ⟨1649078, by rfl⟩ : syracuseStep 2198771 = 3298157) B3298157
theorem B4947245 : Blo 2197435 4947245 := bbase (se 3 (by rfl) ⟨927608, by rfl⟩ : syracuseStep 4947245 = 1855217) (by norm_num)
theorem B3298163 : Blo 2197435 3298163 := bstep (se 1 (by rfl) ⟨2473622, by rfl⟩ : syracuseStep 3298163 = 4947245) B4947245
theorem B2198775 : Blo 2197435 2198775 := bstep (se 1 (by rfl) ⟨1649081, by rfl⟩ : syracuseStep 2198775 = 3298163) B3298163
theorem B7924549 : Blo 2197435 7924549 := bbase (se 4 (by rfl) ⟨742926, by rfl⟩ : syracuseStep 7924549 = 1485853) (by norm_num)
theorem B10566065 : Blo 2197435 10566065 := bstep (se 2 (by rfl) ⟨3962274, by rfl⟩ : syracuseStep 10566065 = 7924549) B7924549
theorem B7044043 : Blo 2197435 7044043 := bstep (se 1 (by rfl) ⟨5283032, by rfl⟩ : syracuseStep 7044043 = 10566065) B10566065
theorem B9392057 : Blo 2197435 9392057 := bstep (se 2 (by rfl) ⟨3522021, by rfl⟩ : syracuseStep 9392057 = 7044043) B7044043
theorem B6261371 : Blo 2197435 6261371 := bstep (se 1 (by rfl) ⟨4696028, by rfl⟩ : syracuseStep 6261371 = 9392057) B9392057
theorem B4174247 : Blo 2197435 4174247 := bstep (se 1 (by rfl) ⟨3130685, by rfl⟩ : syracuseStep 4174247 = 6261371) B6261371
theorem B2782831 : Blo 2197435 2782831 := bstep (se 1 (by rfl) ⟨2087123, by rfl⟩ : syracuseStep 2782831 = 4174247) B4174247
theorem B3710441 : Blo 2197435 3710441 := bstep (se 2 (by rfl) ⟨1391415, by rfl⟩ : syracuseStep 3710441 = 2782831) B2782831
theorem B2473627 : Blo 2197435 2473627 := bstep (se 1 (by rfl) ⟨1855220, by rfl⟩ : syracuseStep 2473627 = 3710441) B3710441
theorem B3298169 : Blo 2197435 3298169 := bstep (se 2 (by rfl) ⟨1236813, by rfl⟩ : syracuseStep 3298169 = 2473627) B2473627
theorem B2198779 : Blo 2197435 2198779 := bstep (se 1 (by rfl) ⟨1649084, by rfl⟩ : syracuseStep 2198779 = 3298169) B3298169
theorem B9520213 : Blo 2197435 9520213 := bbase (se 8 (by rfl) ⟨55782, by rfl⟩ : syracuseStep 9520213 = 111565) (by norm_num)
theorem B12693617 : Blo 2197435 12693617 := bstep (se 2 (by rfl) ⟨4760106, by rfl⟩ : syracuseStep 12693617 = 9520213) B9520213
theorem B8462411 : Blo 2197435 8462411 := bstep (se 1 (by rfl) ⟨6346808, by rfl⟩ : syracuseStep 8462411 = 12693617) B12693617
theorem B5641607 : Blo 2197435 5641607 := bstep (se 1 (by rfl) ⟨4231205, by rfl⟩ : syracuseStep 5641607 = 8462411) B8462411
theorem B15044285 : Blo 2197435 15044285 := bstep (se 3 (by rfl) ⟨2820803, by rfl⟩ : syracuseStep 15044285 = 5641607) B5641607
theorem B10029523 : Blo 2197435 10029523 := bstep (se 1 (by rfl) ⟨7522142, by rfl⟩ : syracuseStep 10029523 = 15044285) B15044285
theorem B13372697 : Blo 2197435 13372697 := bstep (se 2 (by rfl) ⟨5014761, by rfl⟩ : syracuseStep 13372697 = 10029523) B10029523
theorem B8915131 : Blo 2197435 8915131 := bstep (se 1 (by rfl) ⟨6686348, by rfl⟩ : syracuseStep 8915131 = 13372697) B13372697
theorem B11886841 : Blo 2197435 11886841 := bstep (se 2 (by rfl) ⟨4457565, by rfl⟩ : syracuseStep 11886841 = 8915131) B8915131
theorem B15849121 : Blo 2197435 15849121 := bstep (se 2 (by rfl) ⟨5943420, by rfl⟩ : syracuseStep 15849121 = 11886841) B11886841
theorem B21132161 : Blo 2197435 21132161 := bstep (se 2 (by rfl) ⟨7924560, by rfl⟩ : syracuseStep 21132161 = 15849121) B15849121
theorem B14088107 : Blo 2197435 14088107 := bstep (se 1 (by rfl) ⟨10566080, by rfl⟩ : syracuseStep 14088107 = 21132161) B21132161
theorem B37568285 : Blo 2197435 37568285 := bstep (se 3 (by rfl) ⟨7044053, by rfl⟩ : syracuseStep 37568285 = 14088107) B14088107
theorem B25045523 : Blo 2197435 25045523 := bstep (se 1 (by rfl) ⟨18784142, by rfl⟩ : syracuseStep 25045523 = 37568285) B37568285
theorem B16697015 : Blo 2197435 16697015 := bstep (se 1 (by rfl) ⟨12522761, by rfl⟩ : syracuseStep 16697015 = 25045523) B25045523
theorem B11131343 : Blo 2197435 11131343 := bstep (se 1 (by rfl) ⟨8348507, by rfl⟩ : syracuseStep 11131343 = 16697015) B16697015
theorem B7420895 : Blo 2197435 7420895 := bstep (se 1 (by rfl) ⟨5565671, by rfl⟩ : syracuseStep 7420895 = 11131343) B11131343
theorem B4947263 : Blo 2197435 4947263 := bstep (se 1 (by rfl) ⟨3710447, by rfl⟩ : syracuseStep 4947263 = 7420895) B7420895
theorem B3298175 : Blo 2197435 3298175 := bstep (se 1 (by rfl) ⟨2473631, by rfl⟩ : syracuseStep 3298175 = 4947263) B4947263
theorem B2198783 : Blo 2197435 2198783 := bstep (se 1 (by rfl) ⟨1649087, by rfl⟩ : syracuseStep 2198783 = 3298175) B3298175
theorem B3298181 : Blo 2197435 3298181 := bbase (se 4 (by rfl) ⟨309204, by rfl⟩ : syracuseStep 3298181 = 618409) (by norm_num)
theorem B2198787 : Blo 2197435 2198787 := bstep (se 1 (by rfl) ⟨1649090, by rfl⟩ : syracuseStep 2198787 = 3298181) B3298181
theorem B3710461 : Blo 2197435 3710461 := bbase (se 3 (by rfl) ⟨695711, by rfl⟩ : syracuseStep 3710461 = 1391423) (by norm_num)
theorem B4947281 : Blo 2197435 4947281 := bstep (se 2 (by rfl) ⟨1855230, by rfl⟩ : syracuseStep 4947281 = 3710461) B3710461
theorem B3298187 : Blo 2197435 3298187 := bstep (se 1 (by rfl) ⟨2473640, by rfl⟩ : syracuseStep 3298187 = 4947281) B4947281
theorem B2198791 : Blo 2197435 2198791 := bstep (se 1 (by rfl) ⟨1649093, by rfl⟩ : syracuseStep 2198791 = 3298187) B3298187
theorem B2473645 : Blo 2197435 2473645 := bbase (se 3 (by rfl) ⟨463808, by rfl⟩ : syracuseStep 2473645 = 927617) (by norm_num)
theorem B3298193 : Blo 2197435 3298193 := bstep (se 2 (by rfl) ⟨1236822, by rfl⟩ : syracuseStep 3298193 = 2473645) B2473645
theorem B2198795 : Blo 2197435 2198795 := bstep (se 1 (by rfl) ⟨1649096, by rfl⟩ : syracuseStep 2198795 = 3298193) B3298193
theorem B7420949 : Blo 2197435 7420949 := bbase (se 6 (by rfl) ⟨173928, by rfl⟩ : syracuseStep 7420949 = 347857) (by norm_num)
theorem B4947299 : Blo 2197435 4947299 := bstep (se 1 (by rfl) ⟨3710474, by rfl⟩ : syracuseStep 4947299 = 7420949) B7420949
theorem B3298199 : Blo 2197435 3298199 := bstep (se 1 (by rfl) ⟨2473649, by rfl⟩ : syracuseStep 3298199 = 4947299) B4947299
theorem B2198799 : Blo 2197435 2198799 := bstep (se 1 (by rfl) ⟨1649099, by rfl⟩ : syracuseStep 2198799 = 3298199) B3298199
theorem B3298205 : Blo 2197435 3298205 := bbase (se 3 (by rfl) ⟨618413, by rfl⟩ : syracuseStep 3298205 = 1236827) (by norm_num)
theorem B2198803 : Blo 2197435 2198803 := bstep (se 1 (by rfl) ⟨1649102, by rfl⟩ : syracuseStep 2198803 = 3298205) B3298205
theorem B4947317 : Blo 2197435 4947317 := bbase (se 5 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 4947317 = 463811) (by norm_num)
theorem B3298211 : Blo 2197435 3298211 := bstep (se 1 (by rfl) ⟨2473658, by rfl⟩ : syracuseStep 3298211 = 4947317) B4947317
theorem B2198807 : Blo 2197435 2198807 := bstep (se 1 (by rfl) ⟨1649105, by rfl⟩ : syracuseStep 2198807 = 3298211) B3298211
theorem B10029653 : Blo 2197435 10029653 := bbase (se 8 (by rfl) ⟨58767, by rfl⟩ : syracuseStep 10029653 = 117535) (by norm_num)
theorem B6686435 : Blo 2197435 6686435 := bstep (se 1 (by rfl) ⟨5014826, by rfl⟩ : syracuseStep 6686435 = 10029653) B10029653
theorem B17830493 : Blo 2197435 17830493 := bstep (se 3 (by rfl) ⟨3343217, by rfl⟩ : syracuseStep 17830493 = 6686435) B6686435
theorem B11886995 : Blo 2197435 11886995 := bstep (se 1 (by rfl) ⟨8915246, by rfl⟩ : syracuseStep 11886995 = 17830493) B17830493
theorem B7924663 : Blo 2197435 7924663 := bstep (se 1 (by rfl) ⟨5943497, by rfl⟩ : syracuseStep 7924663 = 11886995) B11886995
theorem B10566217 : Blo 2197435 10566217 := bstep (se 2 (by rfl) ⟨3962331, by rfl⟩ : syracuseStep 10566217 = 7924663) B7924663
theorem B14088289 : Blo 2197435 14088289 := bstep (se 2 (by rfl) ⟨5283108, by rfl⟩ : syracuseStep 14088289 = 10566217) B10566217
theorem B18784385 : Blo 2197435 18784385 := bstep (se 2 (by rfl) ⟨7044144, by rfl⟩ : syracuseStep 18784385 = 14088289) B14088289
theorem B12522923 : Blo 2197435 12522923 := bstep (se 1 (by rfl) ⟨9392192, by rfl⟩ : syracuseStep 12522923 = 18784385) B18784385
theorem B8348615 : Blo 2197435 8348615 := bstep (se 1 (by rfl) ⟨6261461, by rfl⟩ : syracuseStep 8348615 = 12522923) B12522923
theorem B5565743 : Blo 2197435 5565743 := bstep (se 1 (by rfl) ⟨4174307, by rfl⟩ : syracuseStep 5565743 = 8348615) B8348615
theorem B3710495 : Blo 2197435 3710495 := bstep (se 1 (by rfl) ⟨2782871, by rfl⟩ : syracuseStep 3710495 = 5565743) B5565743
theorem B2473663 : Blo 2197435 2473663 := bstep (se 1 (by rfl) ⟨1855247, by rfl⟩ : syracuseStep 2473663 = 3710495) B3710495
theorem B3298217 : Blo 2197435 3298217 := bstep (se 2 (by rfl) ⟨1236831, by rfl⟩ : syracuseStep 3298217 = 2473663) B2473663
theorem B2198811 : Blo 2197435 2198811 := bstep (se 1 (by rfl) ⟨1649108, by rfl⟩ : syracuseStep 2198811 = 3298217) B3298217
theorem B8348629 : Blo 2197435 8348629 := bbase (se 7 (by rfl) ⟨97835, by rfl⟩ : syracuseStep 8348629 = 195671) (by norm_num)
theorem B11131505 : Blo 2197435 11131505 := bstep (se 2 (by rfl) ⟨4174314, by rfl⟩ : syracuseStep 11131505 = 8348629) B8348629
theorem B7421003 : Blo 2197435 7421003 := bstep (se 1 (by rfl) ⟨5565752, by rfl⟩ : syracuseStep 7421003 = 11131505) B11131505
theorem B4947335 : Blo 2197435 4947335 := bstep (se 1 (by rfl) ⟨3710501, by rfl⟩ : syracuseStep 4947335 = 7421003) B7421003
theorem B3298223 : Blo 2197435 3298223 := bstep (se 1 (by rfl) ⟨2473667, by rfl⟩ : syracuseStep 3298223 = 4947335) B4947335
theorem B2198815 : Blo 2197435 2198815 := bstep (se 1 (by rfl) ⟨1649111, by rfl⟩ : syracuseStep 2198815 = 3298223) B3298223
theorem B3298229 : Blo 2197435 3298229 := bbase (se 5 (by rfl) ⟨154604, by rfl⟩ : syracuseStep 3298229 = 309209) (by norm_num)
theorem B2198819 : Blo 2197435 2198819 := bstep (se 1 (by rfl) ⟨1649114, by rfl⟩ : syracuseStep 2198819 = 3298229) B3298229
theorem B5565773 : Blo 2197435 5565773 := bbase (se 3 (by rfl) ⟨1043582, by rfl⟩ : syracuseStep 5565773 = 2087165) (by norm_num)
theorem B3710515 : Blo 2197435 3710515 := bstep (se 1 (by rfl) ⟨2782886, by rfl⟩ : syracuseStep 3710515 = 5565773) B5565773
theorem B4947353 : Blo 2197435 4947353 := bstep (se 2 (by rfl) ⟨1855257, by rfl⟩ : syracuseStep 4947353 = 3710515) B3710515
theorem B3298235 : Blo 2197435 3298235 := bstep (se 1 (by rfl) ⟨2473676, by rfl⟩ : syracuseStep 3298235 = 4947353) B4947353
theorem B2198823 : Blo 2197435 2198823 := bstep (se 1 (by rfl) ⟨1649117, by rfl⟩ : syracuseStep 2198823 = 3298235) B3298235
theorem B2473681 : Blo 2197435 2473681 := bbase (se 2 (by rfl) ⟨927630, by rfl⟩ : syracuseStep 2473681 = 1855261) (by norm_num)
theorem B3298241 : Blo 2197435 3298241 := bstep (se 2 (by rfl) ⟨1236840, by rfl⟩ : syracuseStep 3298241 = 2473681) B2473681
theorem B2198827 : Blo 2197435 2198827 := bstep (se 1 (by rfl) ⟨1649120, by rfl⟩ : syracuseStep 2198827 = 3298241) B3298241
theorem B5283157 : Blo 2197435 5283157 := bbase (se 11 (by rfl) ⟨3869, by rfl⟩ : syracuseStep 5283157 = 7739) (by norm_num)
theorem B7044209 : Blo 2197435 7044209 := bstep (se 2 (by rfl) ⟨2641578, by rfl⟩ : syracuseStep 7044209 = 5283157) B5283157
theorem B4696139 : Blo 2197435 4696139 := bstep (se 1 (by rfl) ⟨3522104, by rfl⟩ : syracuseStep 4696139 = 7044209) B7044209
theorem B3130759 : Blo 2197435 3130759 := bstep (se 1 (by rfl) ⟨2348069, by rfl⟩ : syracuseStep 3130759 = 4696139) B4696139
theorem B4174345 : Blo 2197435 4174345 := bstep (se 2 (by rfl) ⟨1565379, by rfl⟩ : syracuseStep 4174345 = 3130759) B3130759
theorem B5565793 : Blo 2197435 5565793 := bstep (se 2 (by rfl) ⟨2087172, by rfl⟩ : syracuseStep 5565793 = 4174345) B4174345
theorem B7421057 : Blo 2197435 7421057 := bstep (se 2 (by rfl) ⟨2782896, by rfl⟩ : syracuseStep 7421057 = 5565793) B5565793
theorem B4947371 : Blo 2197435 4947371 := bstep (se 1 (by rfl) ⟨3710528, by rfl⟩ : syracuseStep 4947371 = 7421057) B7421057
theorem B3298247 : Blo 2197435 3298247 := bstep (se 1 (by rfl) ⟨2473685, by rfl⟩ : syracuseStep 3298247 = 4947371) B4947371
theorem B2198831 : Blo 2197435 2198831 := bstep (se 1 (by rfl) ⟨1649123, by rfl⟩ : syracuseStep 2198831 = 3298247) B3298247
theorem B3298253 : Blo 2197435 3298253 := bbase (se 3 (by rfl) ⟨618422, by rfl⟩ : syracuseStep 3298253 = 1236845) (by norm_num)
theorem B2198835 : Blo 2197435 2198835 := bstep (se 1 (by rfl) ⟨1649126, by rfl⟩ : syracuseStep 2198835 = 3298253) B3298253
theorem B4947389 : Blo 2197435 4947389 := bbase (se 3 (by rfl) ⟨927635, by rfl⟩ : syracuseStep 4947389 = 1855271) (by norm_num)
theorem B3298259 : Blo 2197435 3298259 := bstep (se 1 (by rfl) ⟨2473694, by rfl⟩ : syracuseStep 3298259 = 4947389) B4947389
theorem B2198839 : Blo 2197435 2198839 := bstep (se 1 (by rfl) ⟨1649129, by rfl⟩ : syracuseStep 2198839 = 3298259) B3298259
theorem B3710549 : Blo 2197435 3710549 := bbase (se 8 (by rfl) ⟨21741, by rfl⟩ : syracuseStep 3710549 = 43483) (by norm_num)
theorem B2473699 : Blo 2197435 2473699 := bstep (se 1 (by rfl) ⟨1855274, by rfl⟩ : syracuseStep 2473699 = 3710549) B3710549
theorem B3298265 : Blo 2197435 3298265 := bstep (se 2 (by rfl) ⟨1236849, by rfl⟩ : syracuseStep 3298265 = 2473699) B2473699
theorem B2198843 : Blo 2197435 2198843 := bstep (se 1 (by rfl) ⟨1649132, by rfl⟩ : syracuseStep 2198843 = 3298265) B3298265
theorem B10566389 : Blo 2197435 10566389 := bbase (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) (by norm_num)
theorem B7044259 : Blo 2197435 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B9392345 : Blo 2197435 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B6261563 : Blo 2197435 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B16697501 : Blo 2197435 16697501 := bstep (se 3 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 16697501 = 6261563) B6261563
theorem B11131667 : Blo 2197435 11131667 := bstep (se 1 (by rfl) ⟨8348750, by rfl⟩ : syracuseStep 11131667 = 16697501) B16697501
theorem B7421111 : Blo 2197435 7421111 := bstep (se 1 (by rfl) ⟨5565833, by rfl⟩ : syracuseStep 7421111 = 11131667) B11131667
theorem B4947407 : Blo 2197435 4947407 := bstep (se 1 (by rfl) ⟨3710555, by rfl⟩ : syracuseStep 4947407 = 7421111) B7421111
theorem B3298271 : Blo 2197435 3298271 := bstep (se 1 (by rfl) ⟨2473703, by rfl⟩ : syracuseStep 3298271 = 4947407) B4947407
theorem B2198847 : Blo 2197435 2198847 := bstep (se 1 (by rfl) ⟨1649135, by rfl⟩ : syracuseStep 2198847 = 3298271) B3298271
theorem B3298277 : Blo 2197435 3298277 := bbase (se 4 (by rfl) ⟨309213, by rfl⟩ : syracuseStep 3298277 = 618427) (by norm_num)
theorem B2198851 : Blo 2197435 2198851 := bstep (se 1 (by rfl) ⟨1649138, by rfl⟩ : syracuseStep 2198851 = 3298277) B3298277
theorem B3343285 : Blo 2197435 3343285 := bbase (se 5 (by rfl) ⟨156716, by rfl⟩ : syracuseStep 3343285 = 313433) (by norm_num)
theorem B17830853 : Blo 2197435 17830853 := bstep (se 4 (by rfl) ⟨1671642, by rfl⟩ : syracuseStep 17830853 = 3343285) B3343285
theorem B11887235 : Blo 2197435 11887235 := bstep (se 1 (by rfl) ⟨8915426, by rfl⟩ : syracuseStep 11887235 = 17830853) B17830853
theorem B7924823 : Blo 2197435 7924823 := bstep (se 1 (by rfl) ⟨5943617, by rfl⟩ : syracuseStep 7924823 = 11887235) B11887235
theorem B5283215 : Blo 2197435 5283215 := bstep (se 1 (by rfl) ⟨3962411, by rfl⟩ : syracuseStep 5283215 = 7924823) B7924823
theorem B3522143 : Blo 2197435 3522143 := bstep (se 1 (by rfl) ⟨2641607, by rfl⟩ : syracuseStep 3522143 = 5283215) B5283215
theorem B9392381 : Blo 2197435 9392381 := bstep (se 3 (by rfl) ⟨1761071, by rfl⟩ : syracuseStep 9392381 = 3522143) B3522143
theorem B6261587 : Blo 2197435 6261587 := bstep (se 1 (by rfl) ⟨4696190, by rfl⟩ : syracuseStep 6261587 = 9392381) B9392381
theorem B4174391 : Blo 2197435 4174391 := bstep (se 1 (by rfl) ⟨3130793, by rfl⟩ : syracuseStep 4174391 = 6261587) B6261587
theorem B2782927 : Blo 2197435 2782927 := bstep (se 1 (by rfl) ⟨2087195, by rfl⟩ : syracuseStep 2782927 = 4174391) B4174391
theorem B3710569 : Blo 2197435 3710569 := bstep (se 2 (by rfl) ⟨1391463, by rfl⟩ : syracuseStep 3710569 = 2782927) B2782927
theorem B4947425 : Blo 2197435 4947425 := bstep (se 2 (by rfl) ⟨1855284, by rfl⟩ : syracuseStep 4947425 = 3710569) B3710569
theorem B3298283 : Blo 2197435 3298283 := bstep (se 1 (by rfl) ⟨2473712, by rfl⟩ : syracuseStep 3298283 = 4947425) B4947425
theorem B2198855 : Blo 2197435 2198855 := bstep (se 1 (by rfl) ⟨1649141, by rfl⟩ : syracuseStep 2198855 = 3298283) B3298283
theorem B2473717 : Blo 2197435 2473717 := bbase (se 5 (by rfl) ⟨115955, by rfl⟩ : syracuseStep 2473717 = 231911) (by norm_num)
theorem B3298289 : Blo 2197435 3298289 := bstep (se 2 (by rfl) ⟨1236858, by rfl⟩ : syracuseStep 3298289 = 2473717) B2473717
theorem B2198859 : Blo 2197435 2198859 := bstep (se 1 (by rfl) ⟨1649144, by rfl⟩ : syracuseStep 2198859 = 3298289) B3298289
theorem B2782937 : Blo 2197435 2782937 := bbase (se 2 (by rfl) ⟨1043601, by rfl⟩ : syracuseStep 2782937 = 2087203) (by norm_num)
theorem B7421165 : Blo 2197435 7421165 := bstep (se 3 (by rfl) ⟨1391468, by rfl⟩ : syracuseStep 7421165 = 2782937) B2782937
theorem B4947443 : Blo 2197435 4947443 := bstep (se 1 (by rfl) ⟨3710582, by rfl⟩ : syracuseStep 4947443 = 7421165) B7421165
theorem B3298295 : Blo 2197435 3298295 := bstep (se 1 (by rfl) ⟨2473721, by rfl⟩ : syracuseStep 3298295 = 4947443) B4947443
theorem B2198863 : Blo 2197435 2198863 := bstep (se 1 (by rfl) ⟨1649147, by rfl⟩ : syracuseStep 2198863 = 3298295) B3298295
theorem B3298301 : Blo 2197435 3298301 := bbase (se 3 (by rfl) ⟨618431, by rfl⟩ : syracuseStep 3298301 = 1236863) (by norm_num)
theorem B2198867 : Blo 2197435 2198867 := bstep (se 1 (by rfl) ⟨1649150, by rfl⟩ : syracuseStep 2198867 = 3298301) B3298301
theorem B4947461 : Blo 2197435 4947461 := bbase (se 4 (by rfl) ⟨463824, by rfl⟩ : syracuseStep 4947461 = 927649) (by norm_num)
theorem B3298307 : Blo 2197435 3298307 := bstep (se 1 (by rfl) ⟨2473730, by rfl⟩ : syracuseStep 3298307 = 4947461) B4947461
theorem B2198871 : Blo 2197435 2198871 := bstep (se 1 (by rfl) ⟨1649153, by rfl⟩ : syracuseStep 2198871 = 3298307) B3298307
theorem B4174429 : Blo 2197435 4174429 := bbase (se 3 (by rfl) ⟨782705, by rfl⟩ : syracuseStep 4174429 = 1565411) (by norm_num)
theorem B5565905 : Blo 2197435 5565905 := bstep (se 2 (by rfl) ⟨2087214, by rfl⟩ : syracuseStep 5565905 = 4174429) B4174429
theorem B3710603 : Blo 2197435 3710603 := bstep (se 1 (by rfl) ⟨2782952, by rfl⟩ : syracuseStep 3710603 = 5565905) B5565905
theorem B2473735 : Blo 2197435 2473735 := bstep (se 1 (by rfl) ⟨1855301, by rfl⟩ : syracuseStep 2473735 = 3710603) B3710603
theorem B3298313 : Blo 2197435 3298313 := bstep (se 2 (by rfl) ⟨1236867, by rfl⟩ : syracuseStep 3298313 = 2473735) B2473735
theorem B2198875 : Blo 2197435 2198875 := bstep (se 1 (by rfl) ⟨1649156, by rfl⟩ : syracuseStep 2198875 = 3298313) B3298313
theorem B11131829 : Blo 2197435 11131829 := bbase (se 5 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 11131829 = 1043609) (by norm_num)
theorem B7421219 : Blo 2197435 7421219 := bstep (se 1 (by rfl) ⟨5565914, by rfl⟩ : syracuseStep 7421219 = 11131829) B11131829
theorem B4947479 : Blo 2197435 4947479 := bstep (se 1 (by rfl) ⟨3710609, by rfl⟩ : syracuseStep 4947479 = 7421219) B7421219
theorem B3298319 : Blo 2197435 3298319 := bstep (se 1 (by rfl) ⟨2473739, by rfl⟩ : syracuseStep 3298319 = 4947479) B4947479
theorem B2198879 : Blo 2197435 2198879 := bstep (se 1 (by rfl) ⟨1649159, by rfl⟩ : syracuseStep 2198879 = 3298319) B3298319
theorem B3298325 : Blo 2197435 3298325 := bbase (se 6 (by rfl) ⟨77304, by rfl⟩ : syracuseStep 3298325 = 154609) (by norm_num)
theorem B2198883 : Blo 2197435 2198883 := bstep (se 1 (by rfl) ⟨1649162, by rfl⟩ : syracuseStep 2198883 = 3298325) B3298325
theorem B11283749 : Blo 2197435 11283749 := bbase (se 4 (by rfl) ⟨1057851, by rfl⟩ : syracuseStep 11283749 = 2115703) (by norm_num)
theorem B7522499 : Blo 2197435 7522499 := bstep (se 1 (by rfl) ⟨5641874, by rfl⟩ : syracuseStep 7522499 = 11283749) B11283749
theorem B5014999 : Blo 2197435 5014999 := bstep (se 1 (by rfl) ⟨3761249, by rfl⟩ : syracuseStep 5014999 = 7522499) B7522499
theorem B26746661 : Blo 2197435 26746661 := bstep (se 4 (by rfl) ⟨2507499, by rfl⟩ : syracuseStep 26746661 = 5014999) B5014999
theorem B17831107 : Blo 2197435 17831107 := bstep (se 1 (by rfl) ⟨13373330, by rfl⟩ : syracuseStep 17831107 = 26746661) B26746661
theorem B23774809 : Blo 2197435 23774809 := bstep (se 2 (by rfl) ⟨8915553, by rfl⟩ : syracuseStep 23774809 = 17831107) B17831107
theorem B31699745 : Blo 2197435 31699745 := bstep (se 2 (by rfl) ⟨11887404, by rfl⟩ : syracuseStep 31699745 = 23774809) B23774809
theorem B21133163 : Blo 2197435 21133163 := bstep (se 1 (by rfl) ⟨15849872, by rfl⟩ : syracuseStep 21133163 = 31699745) B31699745
theorem B14088775 : Blo 2197435 14088775 := bstep (se 1 (by rfl) ⟨10566581, by rfl⟩ : syracuseStep 14088775 = 21133163) B21133163
theorem B18785033 : Blo 2197435 18785033 := bstep (se 2 (by rfl) ⟨7044387, by rfl⟩ : syracuseStep 18785033 = 14088775) B14088775
theorem B12523355 : Blo 2197435 12523355 := bstep (se 1 (by rfl) ⟨9392516, by rfl⟩ : syracuseStep 12523355 = 18785033) B18785033
theorem B8348903 : Blo 2197435 8348903 := bstep (se 1 (by rfl) ⟨6261677, by rfl⟩ : syracuseStep 8348903 = 12523355) B12523355
theorem B5565935 : Blo 2197435 5565935 := bstep (se 1 (by rfl) ⟨4174451, by rfl⟩ : syracuseStep 5565935 = 8348903) B8348903
theorem B3710623 : Blo 2197435 3710623 := bstep (se 1 (by rfl) ⟨2782967, by rfl⟩ : syracuseStep 3710623 = 5565935) B5565935
theorem B4947497 : Blo 2197435 4947497 := bstep (se 2 (by rfl) ⟨1855311, by rfl⟩ : syracuseStep 4947497 = 3710623) B3710623
theorem B3298331 : Blo 2197435 3298331 := bstep (se 1 (by rfl) ⟨2473748, by rfl⟩ : syracuseStep 3298331 = 4947497) B4947497
theorem B2198887 : Blo 2197435 2198887 := bstep (se 1 (by rfl) ⟨1649165, by rfl⟩ : syracuseStep 2198887 = 3298331) B3298331
theorem B2473753 : Blo 2197435 2473753 := bbase (se 2 (by rfl) ⟨927657, by rfl⟩ : syracuseStep 2473753 = 1855315) (by norm_num)
theorem B3298337 : Blo 2197435 3298337 := bstep (se 2 (by rfl) ⟨1236876, by rfl⟩ : syracuseStep 3298337 = 2473753) B2473753
theorem B2198891 : Blo 2197435 2198891 := bstep (se 1 (by rfl) ⟨1649168, by rfl⟩ : syracuseStep 2198891 = 3298337) B3298337
theorem B8348933 : Blo 2197435 8348933 := bbase (se 4 (by rfl) ⟨782712, by rfl⟩ : syracuseStep 8348933 = 1565425) (by norm_num)
theorem B5565955 : Blo 2197435 5565955 := bstep (se 1 (by rfl) ⟨4174466, by rfl⟩ : syracuseStep 5565955 = 8348933) B8348933
theorem B7421273 : Blo 2197435 7421273 := bstep (se 2 (by rfl) ⟨2782977, by rfl⟩ : syracuseStep 7421273 = 5565955) B5565955
theorem B4947515 : Blo 2197435 4947515 := bstep (se 1 (by rfl) ⟨3710636, by rfl⟩ : syracuseStep 4947515 = 7421273) B7421273
theorem B3298343 : Blo 2197435 3298343 := bstep (se 1 (by rfl) ⟨2473757, by rfl⟩ : syracuseStep 3298343 = 4947515) B4947515
theorem B2198895 : Blo 2197435 2198895 := bstep (se 1 (by rfl) ⟨1649171, by rfl⟩ : syracuseStep 2198895 = 3298343) B3298343
theorem B3298349 : Blo 2197435 3298349 := bbase (se 3 (by rfl) ⟨618440, by rfl⟩ : syracuseStep 3298349 = 1236881) (by norm_num)
theorem B2198899 : Blo 2197435 2198899 := bstep (se 1 (by rfl) ⟨1649174, by rfl⟩ : syracuseStep 2198899 = 3298349) B3298349
theorem B4947533 : Blo 2197435 4947533 := bbase (se 3 (by rfl) ⟨927662, by rfl⟩ : syracuseStep 4947533 = 1855325) (by norm_num)
theorem B3298355 : Blo 2197435 3298355 := bstep (se 1 (by rfl) ⟨2473766, by rfl⟩ : syracuseStep 3298355 = 4947533) B4947533
theorem B2198903 : Blo 2197435 2198903 := bstep (se 1 (by rfl) ⟨1649177, by rfl⟩ : syracuseStep 2198903 = 3298355) B3298355
theorem B2782993 : Blo 2197435 2782993 := bbase (se 2 (by rfl) ⟨1043622, by rfl⟩ : syracuseStep 2782993 = 2087245) (by norm_num)
theorem B3710657 : Blo 2197435 3710657 := bstep (se 2 (by rfl) ⟨1391496, by rfl⟩ : syracuseStep 3710657 = 2782993) B2782993
theorem B2473771 : Blo 2197435 2473771 := bstep (se 1 (by rfl) ⟨1855328, by rfl⟩ : syracuseStep 2473771 = 3710657) B3710657
theorem B3298361 : Blo 2197435 3298361 := bstep (se 2 (by rfl) ⟨1236885, by rfl⟩ : syracuseStep 3298361 = 2473771) B2473771
theorem B2198907 : Blo 2197435 2198907 := bstep (se 1 (by rfl) ⟨1649180, by rfl⟩ : syracuseStep 2198907 = 3298361) B3298361
theorem B4696309 : Blo 2197435 4696309 := bbase (se 5 (by rfl) ⟨220139, by rfl⟩ : syracuseStep 4696309 = 440279) (by norm_num)
theorem B25046981 : Blo 2197435 25046981 := bstep (se 4 (by rfl) ⟨2348154, by rfl⟩ : syracuseStep 25046981 = 4696309) B4696309
theorem B16697987 : Blo 2197435 16697987 := bstep (se 1 (by rfl) ⟨12523490, by rfl⟩ : syracuseStep 16697987 = 25046981) B25046981
theorem B11131991 : Blo 2197435 11131991 := bstep (se 1 (by rfl) ⟨8348993, by rfl⟩ : syracuseStep 11131991 = 16697987) B16697987
theorem B7421327 : Blo 2197435 7421327 := bstep (se 1 (by rfl) ⟨5565995, by rfl⟩ : syracuseStep 7421327 = 11131991) B11131991
theorem B4947551 : Blo 2197435 4947551 := bstep (se 1 (by rfl) ⟨3710663, by rfl⟩ : syracuseStep 4947551 = 7421327) B7421327
theorem B3298367 : Blo 2197435 3298367 := bstep (se 1 (by rfl) ⟨2473775, by rfl⟩ : syracuseStep 3298367 = 4947551) B4947551
theorem B2198911 : Blo 2197435 2198911 := bstep (se 1 (by rfl) ⟨1649183, by rfl⟩ : syracuseStep 2198911 = 3298367) B3298367
theorem B3298373 : Blo 2197435 3298373 := bbase (se 4 (by rfl) ⟨309222, by rfl⟩ : syracuseStep 3298373 = 618445) (by norm_num)
theorem B2198915 : Blo 2197435 2198915 := bstep (se 1 (by rfl) ⟨1649186, by rfl⟩ : syracuseStep 2198915 = 3298373) B3298373
theorem B3710677 : Blo 2197435 3710677 := bbase (se 7 (by rfl) ⟨43484, by rfl⟩ : syracuseStep 3710677 = 86969) (by norm_num)
theorem B4947569 : Blo 2197435 4947569 := bstep (se 2 (by rfl) ⟨1855338, by rfl⟩ : syracuseStep 4947569 = 3710677) B3710677
theorem B3298379 : Blo 2197435 3298379 := bstep (se 1 (by rfl) ⟨2473784, by rfl⟩ : syracuseStep 3298379 = 4947569) B4947569
theorem B2198919 : Blo 2197435 2198919 := bstep (se 1 (by rfl) ⟨1649189, by rfl⟩ : syracuseStep 2198919 = 3298379) B3298379
theorem B2473789 : Blo 2197435 2473789 := bbase (se 3 (by rfl) ⟨463835, by rfl⟩ : syracuseStep 2473789 = 927671) (by norm_num)
theorem B3298385 : Blo 2197435 3298385 := bstep (se 2 (by rfl) ⟨1236894, by rfl⟩ : syracuseStep 3298385 = 2473789) B2473789
theorem B2198923 : Blo 2197435 2198923 := bstep (se 1 (by rfl) ⟨1649192, by rfl⟩ : syracuseStep 2198923 = 3298385) B3298385
theorem B7421381 : Blo 2197435 7421381 := bbase (se 4 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 7421381 = 1391509) (by norm_num)
theorem B4947587 : Blo 2197435 4947587 := bstep (se 1 (by rfl) ⟨3710690, by rfl⟩ : syracuseStep 4947587 = 7421381) B7421381
theorem B3298391 : Blo 2197435 3298391 := bstep (se 1 (by rfl) ⟨2473793, by rfl⟩ : syracuseStep 3298391 = 4947587) B4947587
theorem B2198927 : Blo 2197435 2198927 := bstep (se 1 (by rfl) ⟨1649195, by rfl⟩ : syracuseStep 2198927 = 3298391) B3298391
theorem B3298397 : Blo 2197435 3298397 := bbase (se 3 (by rfl) ⟨618449, by rfl⟩ : syracuseStep 3298397 = 1236899) (by norm_num)
theorem B2198931 : Blo 2197435 2198931 := bstep (se 1 (by rfl) ⟨1649198, by rfl⟩ : syracuseStep 2198931 = 3298397) B3298397
theorem B4947605 : Blo 2197435 4947605 := bbase (se 6 (by rfl) ⟨115959, by rfl⟩ : syracuseStep 4947605 = 231919) (by norm_num)
theorem B3298403 : Blo 2197435 3298403 := bstep (se 1 (by rfl) ⟨2473802, by rfl⟩ : syracuseStep 3298403 = 4947605) B4947605
theorem B2198935 : Blo 2197435 2198935 := bstep (se 1 (by rfl) ⟨1649201, by rfl⟩ : syracuseStep 2198935 = 3298403) B3298403
theorem B2348185 : Blo 2197435 2348185 := bbase (se 2 (by rfl) ⟨880569, by rfl⟩ : syracuseStep 2348185 = 1761139) (by norm_num)
theorem B3130913 : Blo 2197435 3130913 := bstep (se 2 (by rfl) ⟨1174092, by rfl⟩ : syracuseStep 3130913 = 2348185) B2348185
theorem B8349101 : Blo 2197435 8349101 := bstep (se 3 (by rfl) ⟨1565456, by rfl⟩ : syracuseStep 8349101 = 3130913) B3130913
theorem B5566067 : Blo 2197435 5566067 := bstep (se 1 (by rfl) ⟨4174550, by rfl⟩ : syracuseStep 5566067 = 8349101) B8349101
theorem B3710711 : Blo 2197435 3710711 := bstep (se 1 (by rfl) ⟨2783033, by rfl⟩ : syracuseStep 3710711 = 5566067) B5566067
theorem B2473807 : Blo 2197435 2473807 := bstep (se 1 (by rfl) ⟨1855355, by rfl⟩ : syracuseStep 2473807 = 3710711) B3710711
theorem B3298409 : Blo 2197435 3298409 := bstep (se 2 (by rfl) ⟨1236903, by rfl⟩ : syracuseStep 3298409 = 2473807) B2473807
theorem B2198939 : Blo 2197435 2198939 := bstep (se 1 (by rfl) ⟨1649204, by rfl⟩ : syracuseStep 2198939 = 3298409) B3298409
theorem B6686837 : Blo 2197435 6686837 := bbase (se 5 (by rfl) ⟨313445, by rfl⟩ : syracuseStep 6686837 = 626891) (by norm_num)
theorem B4457891 : Blo 2197435 4457891 := bstep (se 1 (by rfl) ⟨3343418, by rfl⟩ : syracuseStep 4457891 = 6686837) B6686837
theorem B2971927 : Blo 2197435 2971927 := bstep (se 1 (by rfl) ⟨2228945, by rfl⟩ : syracuseStep 2971927 = 4457891) B4457891
theorem B3962569 : Blo 2197435 3962569 := bstep (se 2 (by rfl) ⟨1485963, by rfl⟩ : syracuseStep 3962569 = 2971927) B2971927
theorem B5283425 : Blo 2197435 5283425 := bstep (se 2 (by rfl) ⟨1981284, by rfl⟩ : syracuseStep 5283425 = 3962569) B3962569
theorem B14089133 : Blo 2197435 14089133 := bstep (se 3 (by rfl) ⟨2641712, by rfl⟩ : syracuseStep 14089133 = 5283425) B5283425
theorem B9392755 : Blo 2197435 9392755 := bstep (se 1 (by rfl) ⟨7044566, by rfl⟩ : syracuseStep 9392755 = 14089133) B14089133
theorem B12523673 : Blo 2197435 12523673 := bstep (se 2 (by rfl) ⟨4696377, by rfl⟩ : syracuseStep 12523673 = 9392755) B9392755
theorem B8349115 : Blo 2197435 8349115 := bstep (se 1 (by rfl) ⟨6261836, by rfl⟩ : syracuseStep 8349115 = 12523673) B12523673
theorem B11132153 : Blo 2197435 11132153 := bstep (se 2 (by rfl) ⟨4174557, by rfl⟩ : syracuseStep 11132153 = 8349115) B8349115
theorem B7421435 : Blo 2197435 7421435 := bstep (se 1 (by rfl) ⟨5566076, by rfl⟩ : syracuseStep 7421435 = 11132153) B11132153
theorem B4947623 : Blo 2197435 4947623 := bstep (se 1 (by rfl) ⟨3710717, by rfl⟩ : syracuseStep 4947623 = 7421435) B7421435
theorem B3298415 : Blo 2197435 3298415 := bstep (se 1 (by rfl) ⟨2473811, by rfl⟩ : syracuseStep 3298415 = 4947623) B4947623
theorem B2198943 : Blo 2197435 2198943 := bstep (se 1 (by rfl) ⟨1649207, by rfl⟩ : syracuseStep 2198943 = 3298415) B3298415
theorem B3298421 : Blo 2197435 3298421 := bbase (se 5 (by rfl) ⟨154613, by rfl⟩ : syracuseStep 3298421 = 309227) (by norm_num)
theorem B2198947 : Blo 2197435 2198947 := bstep (se 1 (by rfl) ⟨1649210, by rfl⟩ : syracuseStep 2198947 = 3298421) B3298421
theorem B4174573 : Blo 2197435 4174573 := bbase (se 3 (by rfl) ⟨782732, by rfl⟩ : syracuseStep 4174573 = 1565465) (by norm_num)
theorem B5566097 : Blo 2197435 5566097 := bstep (se 2 (by rfl) ⟨2087286, by rfl⟩ : syracuseStep 5566097 = 4174573) B4174573
theorem B3710731 : Blo 2197435 3710731 := bstep (se 1 (by rfl) ⟨2783048, by rfl⟩ : syracuseStep 3710731 = 5566097) B5566097
theorem B4947641 : Blo 2197435 4947641 := bstep (se 2 (by rfl) ⟨1855365, by rfl⟩ : syracuseStep 4947641 = 3710731) B3710731
theorem B3298427 : Blo 2197435 3298427 := bstep (se 1 (by rfl) ⟨2473820, by rfl⟩ : syracuseStep 3298427 = 4947641) B4947641
theorem B2198951 : Blo 2197435 2198951 := bstep (se 1 (by rfl) ⟨1649213, by rfl⟩ : syracuseStep 2198951 = 3298427) B3298427
theorem B2473825 : Blo 2197435 2473825 := bbase (se 2 (by rfl) ⟨927684, by rfl⟩ : syracuseStep 2473825 = 1855369) (by norm_num)
theorem B3298433 : Blo 2197435 3298433 := bstep (se 2 (by rfl) ⟨1236912, by rfl⟩ : syracuseStep 3298433 = 2473825) B2473825
theorem B2198955 : Blo 2197435 2198955 := bstep (se 1 (by rfl) ⟨1649216, by rfl⟩ : syracuseStep 2198955 = 3298433) B3298433
theorem B5566117 : Blo 2197435 5566117 := bbase (se 4 (by rfl) ⟨521823, by rfl⟩ : syracuseStep 5566117 = 1043647) (by norm_num)
theorem B7421489 : Blo 2197435 7421489 := bstep (se 2 (by rfl) ⟨2783058, by rfl⟩ : syracuseStep 7421489 = 5566117) B5566117
theorem B4947659 : Blo 2197435 4947659 := bstep (se 1 (by rfl) ⟨3710744, by rfl⟩ : syracuseStep 4947659 = 7421489) B7421489
theorem B3298439 : Blo 2197435 3298439 := bstep (se 1 (by rfl) ⟨2473829, by rfl⟩ : syracuseStep 3298439 = 4947659) B4947659
theorem B2198959 : Blo 2197435 2198959 := bstep (se 1 (by rfl) ⟨1649219, by rfl⟩ : syracuseStep 2198959 = 3298439) B3298439
theorem B3298445 : Blo 2197435 3298445 := bbase (se 3 (by rfl) ⟨618458, by rfl⟩ : syracuseStep 3298445 = 1236917) (by norm_num)
theorem B2198963 : Blo 2197435 2198963 := bstep (se 1 (by rfl) ⟨1649222, by rfl⟩ : syracuseStep 2198963 = 3298445) B3298445
theorem B4947677 : Blo 2197435 4947677 := bbase (se 3 (by rfl) ⟨927689, by rfl⟩ : syracuseStep 4947677 = 1855379) (by norm_num)
theorem B3298451 : Blo 2197435 3298451 := bstep (se 1 (by rfl) ⟨2473838, by rfl⟩ : syracuseStep 3298451 = 4947677) B4947677
theorem B2198967 : Blo 2197435 2198967 := bstep (se 1 (by rfl) ⟨1649225, by rfl⟩ : syracuseStep 2198967 = 3298451) B3298451
theorem B3710765 : Blo 2197435 3710765 := bbase (se 3 (by rfl) ⟨695768, by rfl⟩ : syracuseStep 3710765 = 1391537) (by norm_num)
theorem B2473843 : Blo 2197435 2473843 := bstep (se 1 (by rfl) ⟨1855382, by rfl⟩ : syracuseStep 2473843 = 3710765) B3710765
theorem B3298457 : Blo 2197435 3298457 := bstep (se 2 (by rfl) ⟨1236921, by rfl⟩ : syracuseStep 3298457 = 2473843) B2473843
theorem B2198971 : Blo 2197435 2198971 := bstep (se 1 (by rfl) ⟨1649228, by rfl⟩ : syracuseStep 2198971 = 3298457) B3298457
theorem B27112661 : Blo 2197435 27112661 := bbase (se 7 (by rfl) ⟨317726, by rfl⟩ : syracuseStep 27112661 = 635453) (by norm_num)
theorem B18075107 : Blo 2197435 18075107 := bstep (se 1 (by rfl) ⟨13556330, by rfl⟩ : syracuseStep 18075107 = 27112661) B27112661
theorem B48200285 : Blo 2197435 48200285 := bstep (se 3 (by rfl) ⟨9037553, by rfl⟩ : syracuseStep 48200285 = 18075107) B18075107
theorem B32133523 : Blo 2197435 32133523 := bstep (se 1 (by rfl) ⟨24100142, by rfl⟩ : syracuseStep 32133523 = 48200285) B48200285
theorem B42844697 : Blo 2197435 42844697 := bstep (se 2 (by rfl) ⟨16066761, by rfl⟩ : syracuseStep 42844697 = 32133523) B32133523
theorem B28563131 : Blo 2197435 28563131 := bstep (se 1 (by rfl) ⟨21422348, by rfl⟩ : syracuseStep 28563131 = 42844697) B42844697
theorem B19042087 : Blo 2197435 19042087 := bstep (se 1 (by rfl) ⟨14281565, by rfl⟩ : syracuseStep 19042087 = 28563131) B28563131
theorem B25389449 : Blo 2197435 25389449 := bstep (se 2 (by rfl) ⟨9521043, by rfl⟩ : syracuseStep 25389449 = 19042087) B19042087
theorem B16926299 : Blo 2197435 16926299 := bstep (se 1 (by rfl) ⟨12694724, by rfl⟩ : syracuseStep 16926299 = 25389449) B25389449
theorem B11284199 : Blo 2197435 11284199 := bstep (se 1 (by rfl) ⟨8463149, by rfl⟩ : syracuseStep 11284199 = 16926299) B16926299
theorem B7522799 : Blo 2197435 7522799 := bstep (se 1 (by rfl) ⟨5642099, by rfl⟩ : syracuseStep 7522799 = 11284199) B11284199
theorem B20060797 : Blo 2197435 20060797 := bstep (se 3 (by rfl) ⟨3761399, by rfl⟩ : syracuseStep 20060797 = 7522799) B7522799
theorem B26747729 : Blo 2197435 26747729 := bstep (se 2 (by rfl) ⟨10030398, by rfl⟩ : syracuseStep 26747729 = 20060797) B20060797
theorem B17831819 : Blo 2197435 17831819 := bstep (se 1 (by rfl) ⟨13373864, by rfl⟩ : syracuseStep 17831819 = 26747729) B26747729
theorem B11887879 : Blo 2197435 11887879 := bstep (se 1 (by rfl) ⟨8915909, by rfl⟩ : syracuseStep 11887879 = 17831819) B17831819
theorem B15850505 : Blo 2197435 15850505 := bstep (se 2 (by rfl) ⟨5943939, by rfl⟩ : syracuseStep 15850505 = 11887879) B11887879
theorem B42268013 : Blo 2197435 42268013 := bstep (se 3 (by rfl) ⟨7925252, by rfl⟩ : syracuseStep 42268013 = 15850505) B15850505
theorem B28178675 : Blo 2197435 28178675 := bstep (se 1 (by rfl) ⟨21134006, by rfl⟩ : syracuseStep 28178675 = 42268013) B42268013
theorem B18785783 : Blo 2197435 18785783 := bstep (se 1 (by rfl) ⟨14089337, by rfl⟩ : syracuseStep 18785783 = 28178675) B28178675
theorem B12523855 : Blo 2197435 12523855 := bstep (se 1 (by rfl) ⟨9392891, by rfl⟩ : syracuseStep 12523855 = 18785783) B18785783
theorem B16698473 : Blo 2197435 16698473 := bstep (se 2 (by rfl) ⟨6261927, by rfl⟩ : syracuseStep 16698473 = 12523855) B12523855
theorem B11132315 : Blo 2197435 11132315 := bstep (se 1 (by rfl) ⟨8349236, by rfl⟩ : syracuseStep 11132315 = 16698473) B16698473
theorem B7421543 : Blo 2197435 7421543 := bstep (se 1 (by rfl) ⟨5566157, by rfl⟩ : syracuseStep 7421543 = 11132315) B11132315
theorem B4947695 : Blo 2197435 4947695 := bstep (se 1 (by rfl) ⟨3710771, by rfl⟩ : syracuseStep 4947695 = 7421543) B7421543
theorem B3298463 : Blo 2197435 3298463 := bstep (se 1 (by rfl) ⟨2473847, by rfl⟩ : syracuseStep 3298463 = 4947695) B4947695
theorem B2198975 : Blo 2197435 2198975 := bstep (se 1 (by rfl) ⟨1649231, by rfl⟩ : syracuseStep 2198975 = 3298463) B3298463
theorem B3298469 : Blo 2197435 3298469 := bbase (se 4 (by rfl) ⟨309231, by rfl⟩ : syracuseStep 3298469 = 618463) (by norm_num)
theorem B2198979 : Blo 2197435 2198979 := bstep (se 1 (by rfl) ⟨1649234, by rfl⟩ : syracuseStep 2198979 = 3298469) B3298469
theorem B2783089 : Blo 2197435 2783089 := bbase (se 2 (by rfl) ⟨1043658, by rfl⟩ : syracuseStep 2783089 = 2087317) (by norm_num)
theorem B3710785 : Blo 2197435 3710785 := bstep (se 2 (by rfl) ⟨1391544, by rfl⟩ : syracuseStep 3710785 = 2783089) B2783089
theorem B4947713 : Blo 2197435 4947713 := bstep (se 2 (by rfl) ⟨1855392, by rfl⟩ : syracuseStep 4947713 = 3710785) B3710785
theorem B3298475 : Blo 2197435 3298475 := bstep (se 1 (by rfl) ⟨2473856, by rfl⟩ : syracuseStep 3298475 = 4947713) B4947713
theorem B2198983 : Blo 2197435 2198983 := bstep (se 1 (by rfl) ⟨1649237, by rfl⟩ : syracuseStep 2198983 = 3298475) B3298475
theorem B2473861 : Blo 2197435 2473861 := bbase (se 4 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 2473861 = 463849) (by norm_num)
theorem B3298481 : Blo 2197435 3298481 := bstep (se 2 (by rfl) ⟨1236930, by rfl⟩ : syracuseStep 3298481 = 2473861) B2473861
theorem B2198987 : Blo 2197435 2198987 := bstep (se 1 (by rfl) ⟨1649240, by rfl⟩ : syracuseStep 2198987 = 3298481) B3298481
theorem B3343493 : Blo 2197435 3343493 := bbase (se 4 (by rfl) ⟨313452, by rfl⟩ : syracuseStep 3343493 = 626905) (by norm_num)
theorem B2228995 : Blo 2197435 2228995 := bstep (se 1 (by rfl) ⟨1671746, by rfl⟩ : syracuseStep 2228995 = 3343493) B3343493
theorem B2971993 : Blo 2197435 2971993 := bstep (se 2 (by rfl) ⟨1114497, by rfl⟩ : syracuseStep 2971993 = 2228995) B2228995
theorem B3962657 : Blo 2197435 3962657 := bstep (se 2 (by rfl) ⟨1485996, by rfl⟩ : syracuseStep 3962657 = 2971993) B2971993
theorem B2641771 : Blo 2197435 2641771 := bstep (se 1 (by rfl) ⟨1981328, by rfl⟩ : syracuseStep 2641771 = 3962657) B3962657
theorem B3522361 : Blo 2197435 3522361 := bstep (se 2 (by rfl) ⟨1320885, by rfl⟩ : syracuseStep 3522361 = 2641771) B2641771
theorem B4696481 : Blo 2197435 4696481 := bstep (se 2 (by rfl) ⟨1761180, by rfl⟩ : syracuseStep 4696481 = 3522361) B3522361
theorem B3130987 : Blo 2197435 3130987 := bstep (se 1 (by rfl) ⟨2348240, by rfl⟩ : syracuseStep 3130987 = 4696481) B4696481
theorem B4174649 : Blo 2197435 4174649 := bstep (se 2 (by rfl) ⟨1565493, by rfl⟩ : syracuseStep 4174649 = 3130987) B3130987
theorem B2783099 : Blo 2197435 2783099 := bstep (se 1 (by rfl) ⟨2087324, by rfl⟩ : syracuseStep 2783099 = 4174649) B4174649
theorem B7421597 : Blo 2197435 7421597 := bstep (se 3 (by rfl) ⟨1391549, by rfl⟩ : syracuseStep 7421597 = 2783099) B2783099
theorem B4947731 : Blo 2197435 4947731 := bstep (se 1 (by rfl) ⟨3710798, by rfl⟩ : syracuseStep 4947731 = 7421597) B7421597
theorem B3298487 : Blo 2197435 3298487 := bstep (se 1 (by rfl) ⟨2473865, by rfl⟩ : syracuseStep 3298487 = 4947731) B4947731
theorem B2198991 : Blo 2197435 2198991 := bstep (se 1 (by rfl) ⟨1649243, by rfl⟩ : syracuseStep 2198991 = 3298487) B3298487
theorem B3298493 : Blo 2197435 3298493 := bbase (se 3 (by rfl) ⟨618467, by rfl⟩ : syracuseStep 3298493 = 1236935) (by norm_num)
theorem B2198995 : Blo 2197435 2198995 := bstep (se 1 (by rfl) ⟨1649246, by rfl⟩ : syracuseStep 2198995 = 3298493) B3298493
theorem B4947749 : Blo 2197435 4947749 := bbase (se 4 (by rfl) ⟨463851, by rfl⟩ : syracuseStep 4947749 = 927703) (by norm_num)
theorem B3298499 : Blo 2197435 3298499 := bstep (se 1 (by rfl) ⟨2473874, by rfl⟩ : syracuseStep 3298499 = 4947749) B4947749
theorem B2198999 : Blo 2197435 2198999 := bstep (se 1 (by rfl) ⟨1649249, by rfl⟩ : syracuseStep 2198999 = 3298499) B3298499
theorem B5566229 : Blo 2197435 5566229 := bbase (se 6 (by rfl) ⟨130458, by rfl⟩ : syracuseStep 5566229 = 260917) (by norm_num)
theorem B3710819 : Blo 2197435 3710819 := bstep (se 1 (by rfl) ⟨2783114, by rfl⟩ : syracuseStep 3710819 = 5566229) B5566229
theorem B2473879 : Blo 2197435 2473879 := bstep (se 1 (by rfl) ⟨1855409, by rfl⟩ : syracuseStep 2473879 = 3710819) B3710819
theorem B3298505 : Blo 2197435 3298505 := bstep (se 2 (by rfl) ⟨1236939, by rfl⟩ : syracuseStep 3298505 = 2473879) B2473879
theorem B2199003 : Blo 2197435 2199003 := bstep (se 1 (by rfl) ⟨1649252, by rfl⟩ : syracuseStep 2199003 = 3298505) B3298505
theorem B9393029 : Blo 2197435 9393029 := bbase (se 4 (by rfl) ⟨880596, by rfl⟩ : syracuseStep 9393029 = 1761193) (by norm_num)
theorem B6262019 : Blo 2197435 6262019 := bstep (se 1 (by rfl) ⟨4696514, by rfl⟩ : syracuseStep 6262019 = 9393029) B9393029
theorem B4174679 : Blo 2197435 4174679 := bstep (se 1 (by rfl) ⟨3131009, by rfl⟩ : syracuseStep 4174679 = 6262019) B6262019
theorem B11132477 : Blo 2197435 11132477 := bstep (se 3 (by rfl) ⟨2087339, by rfl⟩ : syracuseStep 11132477 = 4174679) B4174679
theorem B7421651 : Blo 2197435 7421651 := bstep (se 1 (by rfl) ⟨5566238, by rfl⟩ : syracuseStep 7421651 = 11132477) B11132477
theorem B4947767 : Blo 2197435 4947767 := bstep (se 1 (by rfl) ⟨3710825, by rfl⟩ : syracuseStep 4947767 = 7421651) B7421651
theorem B3298511 : Blo 2197435 3298511 := bstep (se 1 (by rfl) ⟨2473883, by rfl⟩ : syracuseStep 3298511 = 4947767) B4947767
theorem B2199007 : Blo 2197435 2199007 := bstep (se 1 (by rfl) ⟨1649255, by rfl⟩ : syracuseStep 2199007 = 3298511) B3298511
theorem B3298517 : Blo 2197435 3298517 := bbase (se 7 (by rfl) ⟨38654, by rfl⟩ : syracuseStep 3298517 = 77309) (by norm_num)
theorem B2199011 : Blo 2197435 2199011 := bstep (se 1 (by rfl) ⟨1649258, by rfl⟩ : syracuseStep 2199011 = 3298517) B3298517
theorem B3131021 : Blo 2197435 3131021 := bbase (se 3 (by rfl) ⟨587066, by rfl⟩ : syracuseStep 3131021 = 1174133) (by norm_num)
theorem B8349389 : Blo 2197435 8349389 := bstep (se 3 (by rfl) ⟨1565510, by rfl⟩ : syracuseStep 8349389 = 3131021) B3131021
theorem B5566259 : Blo 2197435 5566259 := bstep (se 1 (by rfl) ⟨4174694, by rfl⟩ : syracuseStep 5566259 = 8349389) B8349389
theorem B3710839 : Blo 2197435 3710839 := bstep (se 1 (by rfl) ⟨2783129, by rfl⟩ : syracuseStep 3710839 = 5566259) B5566259
theorem B4947785 : Blo 2197435 4947785 := bstep (se 2 (by rfl) ⟨1855419, by rfl⟩ : syracuseStep 4947785 = 3710839) B3710839
theorem B3298523 : Blo 2197435 3298523 := bstep (se 1 (by rfl) ⟨2473892, by rfl⟩ : syracuseStep 3298523 = 4947785) B4947785
theorem B2199015 : Blo 2197435 2199015 := bstep (se 1 (by rfl) ⟨1649261, by rfl⟩ : syracuseStep 2199015 = 3298523) B3298523
theorem B2473897 : Blo 2197435 2473897 := bbase (se 2 (by rfl) ⟨927711, by rfl⟩ : syracuseStep 2473897 = 1855423) (by norm_num)
theorem B3298529 : Blo 2197435 3298529 := bstep (se 2 (by rfl) ⟨1236948, by rfl⟩ : syracuseStep 3298529 = 2473897) B2473897
theorem B2199019 : Blo 2197435 2199019 := bstep (se 1 (by rfl) ⟨1649264, by rfl⟩ : syracuseStep 2199019 = 3298529) B3298529
theorem B4458053 : Blo 2197435 4458053 := bbase (se 4 (by rfl) ⟨417942, by rfl⟩ : syracuseStep 4458053 = 835885) (by norm_num)
theorem B2972035 : Blo 2197435 2972035 := bstep (se 1 (by rfl) ⟨2229026, by rfl⟩ : syracuseStep 2972035 = 4458053) B4458053
theorem B15850853 : Blo 2197435 15850853 := bstep (se 4 (by rfl) ⟨1486017, by rfl⟩ : syracuseStep 15850853 = 2972035) B2972035
theorem B10567235 : Blo 2197435 10567235 := bstep (se 1 (by rfl) ⟨7925426, by rfl⟩ : syracuseStep 10567235 = 15850853) B15850853
theorem B7044823 : Blo 2197435 7044823 := bstep (se 1 (by rfl) ⟨5283617, by rfl⟩ : syracuseStep 7044823 = 10567235) B10567235
theorem B9393097 : Blo 2197435 9393097 := bstep (se 2 (by rfl) ⟨3522411, by rfl⟩ : syracuseStep 9393097 = 7044823) B7044823
theorem B12524129 : Blo 2197435 12524129 := bstep (se 2 (by rfl) ⟨4696548, by rfl⟩ : syracuseStep 12524129 = 9393097) B9393097
theorem B8349419 : Blo 2197435 8349419 := bstep (se 1 (by rfl) ⟨6262064, by rfl⟩ : syracuseStep 8349419 = 12524129) B12524129
theorem B5566279 : Blo 2197435 5566279 := bstep (se 1 (by rfl) ⟨4174709, by rfl⟩ : syracuseStep 5566279 = 8349419) B8349419
theorem B7421705 : Blo 2197435 7421705 := bstep (se 2 (by rfl) ⟨2783139, by rfl⟩ : syracuseStep 7421705 = 5566279) B5566279
theorem B4947803 : Blo 2197435 4947803 := bstep (se 1 (by rfl) ⟨3710852, by rfl⟩ : syracuseStep 4947803 = 7421705) B7421705
theorem B3298535 : Blo 2197435 3298535 := bstep (se 1 (by rfl) ⟨2473901, by rfl⟩ : syracuseStep 3298535 = 4947803) B4947803
theorem B2199023 : Blo 2197435 2199023 := bstep (se 1 (by rfl) ⟨1649267, by rfl⟩ : syracuseStep 2199023 = 3298535) B3298535
theorem B3298541 : Blo 2197435 3298541 := bbase (se 3 (by rfl) ⟨618476, by rfl⟩ : syracuseStep 3298541 = 1236953) (by norm_num)
theorem B2199027 : Blo 2197435 2199027 := bstep (se 1 (by rfl) ⟨1649270, by rfl⟩ : syracuseStep 2199027 = 3298541) B3298541
theorem B4947821 : Blo 2197435 4947821 := bbase (se 3 (by rfl) ⟨927716, by rfl⟩ : syracuseStep 4947821 = 1855433) (by norm_num)
theorem B3298547 : Blo 2197435 3298547 := bstep (se 1 (by rfl) ⟨2473910, by rfl⟩ : syracuseStep 3298547 = 4947821) B4947821
theorem B2199031 : Blo 2197435 2199031 := bstep (se 1 (by rfl) ⟨1649273, by rfl⟩ : syracuseStep 2199031 = 3298547) B3298547
theorem B4174733 : Blo 2197435 4174733 := bbase (se 3 (by rfl) ⟨782762, by rfl⟩ : syracuseStep 4174733 = 1565525) (by norm_num)
theorem B2783155 : Blo 2197435 2783155 := bstep (se 1 (by rfl) ⟨2087366, by rfl⟩ : syracuseStep 2783155 = 4174733) B4174733
theorem B3710873 : Blo 2197435 3710873 := bstep (se 2 (by rfl) ⟨1391577, by rfl⟩ : syracuseStep 3710873 = 2783155) B2783155
theorem B2473915 : Blo 2197435 2473915 := bstep (se 1 (by rfl) ⟨1855436, by rfl⟩ : syracuseStep 2473915 = 3710873) B3710873
theorem B3298553 : Blo 2197435 3298553 := bstep (se 2 (by rfl) ⟨1236957, by rfl⟩ : syracuseStep 3298553 = 2473915) B2473915
theorem B2199035 : Blo 2197435 2199035 := bstep (se 1 (by rfl) ⟨1649276, by rfl⟩ : syracuseStep 2199035 = 3298553) B3298553
theorem B15046037 : Blo 2197435 15046037 := bbase (se 6 (by rfl) ⟨352641, by rfl⟩ : syracuseStep 15046037 = 705283) (by norm_num)
theorem B10030691 : Blo 2197435 10030691 := bstep (se 1 (by rfl) ⟨7523018, by rfl⟩ : syracuseStep 10030691 = 15046037) B15046037
theorem B6687127 : Blo 2197435 6687127 := bstep (se 1 (by rfl) ⟨5015345, by rfl⟩ : syracuseStep 6687127 = 10030691) B10030691
theorem B8916169 : Blo 2197435 8916169 := bstep (se 2 (by rfl) ⟨3343563, by rfl⟩ : syracuseStep 8916169 = 6687127) B6687127
theorem B11888225 : Blo 2197435 11888225 := bstep (se 2 (by rfl) ⟨4458084, by rfl⟩ : syracuseStep 11888225 = 8916169) B8916169
theorem B7925483 : Blo 2197435 7925483 := bstep (se 1 (by rfl) ⟨5944112, by rfl⟩ : syracuseStep 7925483 = 11888225) B11888225
theorem B21134621 : Blo 2197435 21134621 := bstep (se 3 (by rfl) ⟨3962741, by rfl⟩ : syracuseStep 21134621 = 7925483) B7925483
theorem B56358989 : Blo 2197435 56358989 := bstep (se 3 (by rfl) ⟨10567310, by rfl⟩ : syracuseStep 56358989 = 21134621) B21134621
theorem B37572659 : Blo 2197435 37572659 := bstep (se 1 (by rfl) ⟨28179494, by rfl⟩ : syracuseStep 37572659 = 56358989) B56358989
theorem B25048439 : Blo 2197435 25048439 := bstep (se 1 (by rfl) ⟨18786329, by rfl⟩ : syracuseStep 25048439 = 37572659) B37572659
theorem B16698959 : Blo 2197435 16698959 := bstep (se 1 (by rfl) ⟨12524219, by rfl⟩ : syracuseStep 16698959 = 25048439) B25048439
theorem B11132639 : Blo 2197435 11132639 := bstep (se 1 (by rfl) ⟨8349479, by rfl⟩ : syracuseStep 11132639 = 16698959) B16698959
theorem B7421759 : Blo 2197435 7421759 := bstep (se 1 (by rfl) ⟨5566319, by rfl⟩ : syracuseStep 7421759 = 11132639) B11132639
theorem B4947839 : Blo 2197435 4947839 := bstep (se 1 (by rfl) ⟨3710879, by rfl⟩ : syracuseStep 4947839 = 7421759) B7421759
theorem B3298559 : Blo 2197435 3298559 := bstep (se 1 (by rfl) ⟨2473919, by rfl⟩ : syracuseStep 3298559 = 4947839) B4947839
theorem B2199039 : Blo 2197435 2199039 := bstep (se 1 (by rfl) ⟨1649279, by rfl⟩ : syracuseStep 2199039 = 3298559) B3298559
theorem B3298565 : Blo 2197435 3298565 := bbase (se 4 (by rfl) ⟨309240, by rfl⟩ : syracuseStep 3298565 = 618481) (by norm_num)
theorem B2199043 : Blo 2197435 2199043 := bstep (se 1 (by rfl) ⟨1649282, by rfl⟩ : syracuseStep 2199043 = 3298565) B3298565
theorem B3710893 : Blo 2197435 3710893 := bbase (se 3 (by rfl) ⟨695792, by rfl⟩ : syracuseStep 3710893 = 1391585) (by norm_num)
theorem B4947857 : Blo 2197435 4947857 := bstep (se 2 (by rfl) ⟨1855446, by rfl⟩ : syracuseStep 4947857 = 3710893) B3710893
theorem B3298571 : Blo 2197435 3298571 := bstep (se 1 (by rfl) ⟨2473928, by rfl⟩ : syracuseStep 3298571 = 4947857) B4947857
theorem B2199047 : Blo 2197435 2199047 := bstep (se 1 (by rfl) ⟨1649285, by rfl⟩ : syracuseStep 2199047 = 3298571) B3298571
theorem B2473933 : Blo 2197435 2473933 := bbase (se 3 (by rfl) ⟨463862, by rfl⟩ : syracuseStep 2473933 = 927725) (by norm_num)
theorem B3298577 : Blo 2197435 3298577 := bstep (se 2 (by rfl) ⟨1236966, by rfl⟩ : syracuseStep 3298577 = 2473933) B2473933
theorem B2199051 : Blo 2197435 2199051 := bstep (se 1 (by rfl) ⟨1649288, by rfl⟩ : syracuseStep 2199051 = 3298577) B3298577
theorem B7421813 : Blo 2197435 7421813 := bbase (se 5 (by rfl) ⟨347897, by rfl⟩ : syracuseStep 7421813 = 695795) (by norm_num)
theorem B4947875 : Blo 2197435 4947875 := bstep (se 1 (by rfl) ⟨3710906, by rfl⟩ : syracuseStep 4947875 = 7421813) B7421813
theorem B3298583 : Blo 2197435 3298583 := bstep (se 1 (by rfl) ⟨2473937, by rfl⟩ : syracuseStep 3298583 = 4947875) B4947875
theorem B2199055 : Blo 2197435 2199055 := bstep (se 1 (by rfl) ⟨1649291, by rfl⟩ : syracuseStep 2199055 = 3298583) B3298583
theorem B3298589 : Blo 2197435 3298589 := bbase (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) (by norm_num)
theorem B2199059 : Blo 2197435 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B4947893 : Blo 2197435 4947893 := bbase (se 5 (by rfl) ⟨231932, by rfl⟩ : syracuseStep 4947893 = 463865) (by norm_num)
theorem B3298595 : Blo 2197435 3298595 := bstep (se 1 (by rfl) ⟨2473946, by rfl⟩ : syracuseStep 3298595 = 4947893) B4947893
theorem B2199063 : Blo 2197435 2199063 := bstep (se 1 (by rfl) ⟨1649297, by rfl⟩ : syracuseStep 2199063 = 3298595) B3298595
theorem B7044965 : Blo 2197435 7044965 := bbase (se 4 (by rfl) ⟨660465, by rfl⟩ : syracuseStep 7044965 = 1320931) (by norm_num)
theorem B4696643 : Blo 2197435 4696643 := bstep (se 1 (by rfl) ⟨3522482, by rfl⟩ : syracuseStep 4696643 = 7044965) B7044965
theorem B12524381 : Blo 2197435 12524381 := bstep (se 3 (by rfl) ⟨2348321, by rfl⟩ : syracuseStep 12524381 = 4696643) B4696643
theorem B8349587 : Blo 2197435 8349587 := bstep (se 1 (by rfl) ⟨6262190, by rfl⟩ : syracuseStep 8349587 = 12524381) B12524381
theorem B5566391 : Blo 2197435 5566391 := bstep (se 1 (by rfl) ⟨4174793, by rfl⟩ : syracuseStep 5566391 = 8349587) B8349587
theorem B3710927 : Blo 2197435 3710927 := bstep (se 1 (by rfl) ⟨2783195, by rfl⟩ : syracuseStep 3710927 = 5566391) B5566391
theorem B2473951 : Blo 2197435 2473951 := bstep (se 1 (by rfl) ⟨1855463, by rfl⟩ : syracuseStep 2473951 = 3710927) B3710927
theorem B3298601 : Blo 2197435 3298601 := bstep (se 2 (by rfl) ⟨1236975, by rfl⟩ : syracuseStep 3298601 = 2473951) B2473951
theorem B2199067 : Blo 2197435 2199067 := bstep (se 1 (by rfl) ⟨1649300, by rfl⟩ : syracuseStep 2199067 = 3298601) B3298601
theorem B5283733 : Blo 2197435 5283733 := bbase (se 6 (by rfl) ⟨123837, by rfl⟩ : syracuseStep 5283733 = 247675) (by norm_num)
theorem B7044977 : Blo 2197435 7044977 := bstep (se 2 (by rfl) ⟨2641866, by rfl⟩ : syracuseStep 7044977 = 5283733) B5283733
theorem B4696651 : Blo 2197435 4696651 := bstep (se 1 (by rfl) ⟨3522488, by rfl⟩ : syracuseStep 4696651 = 7044977) B7044977
theorem B6262201 : Blo 2197435 6262201 := bstep (se 2 (by rfl) ⟨2348325, by rfl⟩ : syracuseStep 6262201 = 4696651) B4696651
theorem B8349601 : Blo 2197435 8349601 := bstep (se 2 (by rfl) ⟨3131100, by rfl⟩ : syracuseStep 8349601 = 6262201) B6262201
theorem B11132801 : Blo 2197435 11132801 := bstep (se 2 (by rfl) ⟨4174800, by rfl⟩ : syracuseStep 11132801 = 8349601) B8349601
theorem B7421867 : Blo 2197435 7421867 := bstep (se 1 (by rfl) ⟨5566400, by rfl⟩ : syracuseStep 7421867 = 11132801) B11132801
theorem B4947911 : Blo 2197435 4947911 := bstep (se 1 (by rfl) ⟨3710933, by rfl⟩ : syracuseStep 4947911 = 7421867) B7421867
theorem B3298607 : Blo 2197435 3298607 := bstep (se 1 (by rfl) ⟨2473955, by rfl⟩ : syracuseStep 3298607 = 4947911) B4947911
theorem B2199071 : Blo 2197435 2199071 := bstep (se 1 (by rfl) ⟨1649303, by rfl⟩ : syracuseStep 2199071 = 3298607) B3298607
theorem B3298613 : Blo 2197435 3298613 := bbase (se 5 (by rfl) ⟨154622, by rfl⟩ : syracuseStep 3298613 = 309245) (by norm_num)
theorem B2199075 : Blo 2197435 2199075 := bstep (se 1 (by rfl) ⟨1649306, by rfl⟩ : syracuseStep 2199075 = 3298613) B3298613
theorem B5566421 : Blo 2197435 5566421 := bbase (se 7 (by rfl) ⟨65231, by rfl⟩ : syracuseStep 5566421 = 130463) (by norm_num)
theorem B3710947 : Blo 2197435 3710947 := bstep (se 1 (by rfl) ⟨2783210, by rfl⟩ : syracuseStep 3710947 = 5566421) B5566421
theorem B4947929 : Blo 2197435 4947929 := bstep (se 2 (by rfl) ⟨1855473, by rfl⟩ : syracuseStep 4947929 = 3710947) B3710947
theorem B3298619 : Blo 2197435 3298619 := bstep (se 1 (by rfl) ⟨2473964, by rfl⟩ : syracuseStep 3298619 = 4947929) B4947929
theorem B2199079 : Blo 2197435 2199079 := bstep (se 1 (by rfl) ⟨1649309, by rfl⟩ : syracuseStep 2199079 = 3298619) B3298619
theorem B2473969 : Blo 2197435 2473969 := bbase (se 2 (by rfl) ⟨927738, by rfl⟩ : syracuseStep 2473969 = 1855477) (by norm_num)
theorem B3298625 : Blo 2197435 3298625 := bstep (se 2 (by rfl) ⟨1236984, by rfl⟩ : syracuseStep 3298625 = 2473969) B2473969
theorem B2199083 : Blo 2197435 2199083 := bstep (se 1 (by rfl) ⟨1649312, by rfl⟩ : syracuseStep 2199083 = 3298625) B3298625
theorem B3343637 : Blo 2197435 3343637 := bbase (se 6 (by rfl) ⟨78366, by rfl⟩ : syracuseStep 3343637 = 156733) (by norm_num)
theorem B8916365 : Blo 2197435 8916365 := bstep (se 3 (by rfl) ⟨1671818, by rfl⟩ : syracuseStep 8916365 = 3343637) B3343637
theorem B23776973 : Blo 2197435 23776973 := bstep (se 3 (by rfl) ⟨4458182, by rfl⟩ : syracuseStep 23776973 = 8916365) B8916365
theorem B15851315 : Blo 2197435 15851315 := bstep (se 1 (by rfl) ⟨11888486, by rfl⟩ : syracuseStep 15851315 = 23776973) B23776973
theorem B10567543 : Blo 2197435 10567543 := bstep (se 1 (by rfl) ⟨7925657, by rfl⟩ : syracuseStep 10567543 = 15851315) B15851315
theorem B14090057 : Blo 2197435 14090057 := bstep (se 2 (by rfl) ⟨5283771, by rfl⟩ : syracuseStep 14090057 = 10567543) B10567543
theorem B9393371 : Blo 2197435 9393371 := bstep (se 1 (by rfl) ⟨7045028, by rfl⟩ : syracuseStep 9393371 = 14090057) B14090057
theorem B6262247 : Blo 2197435 6262247 := bstep (se 1 (by rfl) ⟨4696685, by rfl⟩ : syracuseStep 6262247 = 9393371) B9393371
theorem B4174831 : Blo 2197435 4174831 := bstep (se 1 (by rfl) ⟨3131123, by rfl⟩ : syracuseStep 4174831 = 6262247) B6262247
theorem B5566441 : Blo 2197435 5566441 := bstep (se 2 (by rfl) ⟨2087415, by rfl⟩ : syracuseStep 5566441 = 4174831) B4174831
theorem B7421921 : Blo 2197435 7421921 := bstep (se 2 (by rfl) ⟨2783220, by rfl⟩ : syracuseStep 7421921 = 5566441) B5566441
theorem B4947947 : Blo 2197435 4947947 := bstep (se 1 (by rfl) ⟨3710960, by rfl⟩ : syracuseStep 4947947 = 7421921) B7421921
theorem B3298631 : Blo 2197435 3298631 := bstep (se 1 (by rfl) ⟨2473973, by rfl⟩ : syracuseStep 3298631 = 4947947) B4947947
theorem B2199087 : Blo 2197435 2199087 := bstep (se 1 (by rfl) ⟨1649315, by rfl⟩ : syracuseStep 2199087 = 3298631) B3298631
theorem B3298637 : Blo 2197435 3298637 := bbase (se 3 (by rfl) ⟨618494, by rfl⟩ : syracuseStep 3298637 = 1236989) (by norm_num)
theorem B2199091 : Blo 2197435 2199091 := bstep (se 1 (by rfl) ⟨1649318, by rfl⟩ : syracuseStep 2199091 = 3298637) B3298637
theorem B4947965 : Blo 2197435 4947965 := bbase (se 3 (by rfl) ⟨927743, by rfl⟩ : syracuseStep 4947965 = 1855487) (by norm_num)
theorem B3298643 : Blo 2197435 3298643 := bstep (se 1 (by rfl) ⟨2473982, by rfl⟩ : syracuseStep 3298643 = 4947965) B4947965
theorem B2199095 : Blo 2197435 2199095 := bstep (se 1 (by rfl) ⟨1649321, by rfl⟩ : syracuseStep 2199095 = 3298643) B3298643
theorem B3710981 : Blo 2197435 3710981 := bbase (se 4 (by rfl) ⟨347904, by rfl⟩ : syracuseStep 3710981 = 695809) (by norm_num)
theorem B2473987 : Blo 2197435 2473987 := bstep (se 1 (by rfl) ⟨1855490, by rfl⟩ : syracuseStep 2473987 = 3710981) B3710981
theorem B3298649 : Blo 2197435 3298649 := bstep (se 2 (by rfl) ⟨1236993, by rfl⟩ : syracuseStep 3298649 = 2473987) B2473987
theorem B2199099 : Blo 2197435 2199099 := bstep (se 1 (by rfl) ⟨1649324, by rfl⟩ : syracuseStep 2199099 = 3298649) B3298649
theorem B16699445 : Blo 2197435 16699445 := bbase (se 5 (by rfl) ⟨782786, by rfl⟩ : syracuseStep 16699445 = 1565573) (by norm_num)
theorem B11132963 : Blo 2197435 11132963 := bstep (se 1 (by rfl) ⟨8349722, by rfl⟩ : syracuseStep 11132963 = 16699445) B16699445
theorem B7421975 : Blo 2197435 7421975 := bstep (se 1 (by rfl) ⟨5566481, by rfl⟩ : syracuseStep 7421975 = 11132963) B11132963
theorem B4947983 : Blo 2197435 4947983 := bstep (se 1 (by rfl) ⟨3710987, by rfl⟩ : syracuseStep 4947983 = 7421975) B7421975
theorem B3298655 : Blo 2197435 3298655 := bstep (se 1 (by rfl) ⟨2473991, by rfl⟩ : syracuseStep 3298655 = 4947983) B4947983
theorem B2199103 : Blo 2197435 2199103 := bstep (se 1 (by rfl) ⟨1649327, by rfl⟩ : syracuseStep 2199103 = 3298655) B3298655
theorem B3298661 : Blo 2197435 3298661 := bbase (se 4 (by rfl) ⟨309249, by rfl⟩ : syracuseStep 3298661 = 618499) (by norm_num)
theorem B2199107 : Blo 2197435 2199107 := bstep (se 1 (by rfl) ⟨1649330, by rfl⟩ : syracuseStep 2199107 = 3298661) B3298661
theorem B4174877 : Blo 2197435 4174877 := bbase (se 3 (by rfl) ⟨782789, by rfl⟩ : syracuseStep 4174877 = 1565579) (by norm_num)
theorem B2783251 : Blo 2197435 2783251 := bstep (se 1 (by rfl) ⟨2087438, by rfl⟩ : syracuseStep 2783251 = 4174877) B4174877
theorem B3711001 : Blo 2197435 3711001 := bstep (se 2 (by rfl) ⟨1391625, by rfl⟩ : syracuseStep 3711001 = 2783251) B2783251
theorem B4948001 : Blo 2197435 4948001 := bstep (se 2 (by rfl) ⟨1855500, by rfl⟩ : syracuseStep 4948001 = 3711001) B3711001
theorem B3298667 : Blo 2197435 3298667 := bstep (se 1 (by rfl) ⟨2474000, by rfl⟩ : syracuseStep 3298667 = 4948001) B4948001
theorem B2199111 : Blo 2197435 2199111 := bstep (se 1 (by rfl) ⟨1649333, by rfl⟩ : syracuseStep 2199111 = 3298667) B3298667
theorem B2474005 : Blo 2197435 2474005 := bbase (se 6 (by rfl) ⟨57984, by rfl⟩ : syracuseStep 2474005 = 115969) (by norm_num)
theorem B3298673 : Blo 2197435 3298673 := bstep (se 2 (by rfl) ⟨1237002, by rfl⟩ : syracuseStep 3298673 = 2474005) B2474005
theorem B2199115 : Blo 2197435 2199115 := bstep (se 1 (by rfl) ⟨1649336, by rfl⟩ : syracuseStep 2199115 = 3298673) B3298673
theorem B2783261 : Blo 2197435 2783261 := bbase (se 3 (by rfl) ⟨521861, by rfl⟩ : syracuseStep 2783261 = 1043723) (by norm_num)
theorem B7422029 : Blo 2197435 7422029 := bstep (se 3 (by rfl) ⟨1391630, by rfl⟩ : syracuseStep 7422029 = 2783261) B2783261
theorem B4948019 : Blo 2197435 4948019 := bstep (se 1 (by rfl) ⟨3711014, by rfl⟩ : syracuseStep 4948019 = 7422029) B7422029
theorem B3298679 : Blo 2197435 3298679 := bstep (se 1 (by rfl) ⟨2474009, by rfl⟩ : syracuseStep 3298679 = 4948019) B4948019
theorem B2199119 : Blo 2197435 2199119 := bstep (se 1 (by rfl) ⟨1649339, by rfl⟩ : syracuseStep 2199119 = 3298679) B3298679
theorem B3298685 : Blo 2197435 3298685 := bbase (se 3 (by rfl) ⟨618503, by rfl⟩ : syracuseStep 3298685 = 1237007) (by norm_num)
theorem B2199123 : Blo 2197435 2199123 := bstep (se 1 (by rfl) ⟨1649342, by rfl⟩ : syracuseStep 2199123 = 3298685) B3298685
theorem B4948037 : Blo 2197435 4948037 := bbase (se 4 (by rfl) ⟨463878, by rfl⟩ : syracuseStep 4948037 = 927757) (by norm_num)
theorem B3298691 : Blo 2197435 3298691 := bstep (se 1 (by rfl) ⟨2474018, by rfl⟩ : syracuseStep 3298691 = 4948037) B4948037
theorem B2199127 : Blo 2197435 2199127 := bstep (se 1 (by rfl) ⟨1649345, by rfl⟩ : syracuseStep 2199127 = 3298691) B3298691
theorem B6262373 : Blo 2197435 6262373 := bbase (se 4 (by rfl) ⟨587097, by rfl⟩ : syracuseStep 6262373 = 1174195) (by norm_num)
theorem B4174915 : Blo 2197435 4174915 := bstep (se 1 (by rfl) ⟨3131186, by rfl⟩ : syracuseStep 4174915 = 6262373) B6262373
theorem B5566553 : Blo 2197435 5566553 := bstep (se 2 (by rfl) ⟨2087457, by rfl⟩ : syracuseStep 5566553 = 4174915) B4174915
theorem B3711035 : Blo 2197435 3711035 := bstep (se 1 (by rfl) ⟨2783276, by rfl⟩ : syracuseStep 3711035 = 5566553) B5566553
theorem B2474023 : Blo 2197435 2474023 := bstep (se 1 (by rfl) ⟨1855517, by rfl⟩ : syracuseStep 2474023 = 3711035) B3711035
theorem B3298697 : Blo 2197435 3298697 := bstep (se 2 (by rfl) ⟨1237011, by rfl⟩ : syracuseStep 3298697 = 2474023) B2474023
theorem B2199131 : Blo 2197435 2199131 := bstep (se 1 (by rfl) ⟨1649348, by rfl⟩ : syracuseStep 2199131 = 3298697) B3298697
theorem B11133125 : Blo 2197435 11133125 := bbase (se 4 (by rfl) ⟨1043730, by rfl⟩ : syracuseStep 11133125 = 2087461) (by norm_num)
theorem B7422083 : Blo 2197435 7422083 := bstep (se 1 (by rfl) ⟨5566562, by rfl⟩ : syracuseStep 7422083 = 11133125) B11133125
theorem B4948055 : Blo 2197435 4948055 := bstep (se 1 (by rfl) ⟨3711041, by rfl⟩ : syracuseStep 4948055 = 7422083) B7422083
theorem B3298703 : Blo 2197435 3298703 := bstep (se 1 (by rfl) ⟨2474027, by rfl⟩ : syracuseStep 3298703 = 4948055) B4948055
theorem B2199135 : Blo 2197435 2199135 := bstep (se 1 (by rfl) ⟨1649351, by rfl⟩ : syracuseStep 2199135 = 3298703) B3298703
theorem B3298709 : Blo 2197435 3298709 := bbase (se 6 (by rfl) ⟨77313, by rfl⟩ : syracuseStep 3298709 = 154627) (by norm_num)
theorem B2199139 : Blo 2197435 2199139 := bstep (se 1 (by rfl) ⟨1649354, by rfl⟩ : syracuseStep 2199139 = 3298709) B3298709
theorem B4696805 : Blo 2197435 4696805 := bbase (se 4 (by rfl) ⟨440325, by rfl⟩ : syracuseStep 4696805 = 880651) (by norm_num)
theorem B12524813 : Blo 2197435 12524813 := bstep (se 3 (by rfl) ⟨2348402, by rfl⟩ : syracuseStep 12524813 = 4696805) B4696805
theorem B8349875 : Blo 2197435 8349875 := bstep (se 1 (by rfl) ⟨6262406, by rfl⟩ : syracuseStep 8349875 = 12524813) B12524813
theorem B5566583 : Blo 2197435 5566583 := bstep (se 1 (by rfl) ⟨4174937, by rfl⟩ : syracuseStep 5566583 = 8349875) B8349875
theorem B3711055 : Blo 2197435 3711055 := bstep (se 1 (by rfl) ⟨2783291, by rfl⟩ : syracuseStep 3711055 = 5566583) B5566583
theorem B4948073 : Blo 2197435 4948073 := bstep (se 2 (by rfl) ⟨1855527, by rfl⟩ : syracuseStep 4948073 = 3711055) B3711055
theorem B3298715 : Blo 2197435 3298715 := bstep (se 1 (by rfl) ⟨2474036, by rfl⟩ : syracuseStep 3298715 = 4948073) B4948073
theorem B2199143 : Blo 2197435 2199143 := bstep (se 1 (by rfl) ⟨1649357, by rfl⟩ : syracuseStep 2199143 = 3298715) B3298715
theorem B2474041 : Blo 2197435 2474041 := bbase (se 2 (by rfl) ⟨927765, by rfl⟩ : syracuseStep 2474041 = 1855531) (by norm_num)
theorem B3298721 : Blo 2197435 3298721 := bstep (se 2 (by rfl) ⟨1237020, by rfl⟩ : syracuseStep 3298721 = 2474041) B2474041
theorem B2199147 : Blo 2197435 2199147 := bstep (se 1 (by rfl) ⟨1649360, by rfl⟩ : syracuseStep 2199147 = 3298721) B3298721
theorem B2229157 : Blo 2197435 2229157 := bbase (se 4 (by rfl) ⟨208983, by rfl⟩ : syracuseStep 2229157 = 417967) (by norm_num)
theorem B2972209 : Blo 2197435 2972209 := bstep (se 2 (by rfl) ⟨1114578, by rfl⟩ : syracuseStep 2972209 = 2229157) B2229157
theorem B3962945 : Blo 2197435 3962945 := bstep (se 2 (by rfl) ⟨1486104, by rfl⟩ : syracuseStep 3962945 = 2972209) B2972209
theorem B2641963 : Blo 2197435 2641963 := bstep (se 1 (by rfl) ⟨1981472, by rfl⟩ : syracuseStep 2641963 = 3962945) B3962945
theorem B3522617 : Blo 2197435 3522617 := bstep (se 2 (by rfl) ⟨1320981, by rfl⟩ : syracuseStep 3522617 = 2641963) B2641963
theorem B2348411 : Blo 2197435 2348411 := bstep (se 1 (by rfl) ⟨1761308, by rfl⟩ : syracuseStep 2348411 = 3522617) B3522617
theorem B6262429 : Blo 2197435 6262429 := bstep (se 3 (by rfl) ⟨1174205, by rfl⟩ : syracuseStep 6262429 = 2348411) B2348411
theorem B8349905 : Blo 2197435 8349905 := bstep (se 2 (by rfl) ⟨3131214, by rfl⟩ : syracuseStep 8349905 = 6262429) B6262429
theorem B5566603 : Blo 2197435 5566603 := bstep (se 1 (by rfl) ⟨4174952, by rfl⟩ : syracuseStep 5566603 = 8349905) B8349905
theorem B7422137 : Blo 2197435 7422137 := bstep (se 2 (by rfl) ⟨2783301, by rfl⟩ : syracuseStep 7422137 = 5566603) B5566603
theorem B4948091 : Blo 2197435 4948091 := bstep (se 1 (by rfl) ⟨3711068, by rfl⟩ : syracuseStep 4948091 = 7422137) B7422137
theorem B3298727 : Blo 2197435 3298727 := bstep (se 1 (by rfl) ⟨2474045, by rfl⟩ : syracuseStep 3298727 = 4948091) B4948091
theorem B2199151 : Blo 2197435 2199151 := bstep (se 1 (by rfl) ⟨1649363, by rfl⟩ : syracuseStep 2199151 = 3298727) B3298727
theorem B3298733 : Blo 2197435 3298733 := bbase (se 3 (by rfl) ⟨618512, by rfl⟩ : syracuseStep 3298733 = 1237025) (by norm_num)
theorem B2199155 : Blo 2197435 2199155 := bstep (se 1 (by rfl) ⟨1649366, by rfl⟩ : syracuseStep 2199155 = 3298733) B3298733
theorem B4948109 : Blo 2197435 4948109 := bbase (se 3 (by rfl) ⟨927770, by rfl⟩ : syracuseStep 4948109 = 1855541) (by norm_num)
theorem B3298739 : Blo 2197435 3298739 := bstep (se 1 (by rfl) ⟨2474054, by rfl⟩ : syracuseStep 3298739 = 4948109) B4948109
theorem B2199159 : Blo 2197435 2199159 := bstep (se 1 (by rfl) ⟨1649369, by rfl⟩ : syracuseStep 2199159 = 3298739) B3298739
theorem B2783317 : Blo 2197435 2783317 := bbase (se 8 (by rfl) ⟨16308, by rfl⟩ : syracuseStep 2783317 = 32617) (by norm_num)
theorem B3711089 : Blo 2197435 3711089 := bstep (se 2 (by rfl) ⟨1391658, by rfl⟩ : syracuseStep 3711089 = 2783317) B2783317
theorem B2474059 : Blo 2197435 2474059 := bstep (se 1 (by rfl) ⟨1855544, by rfl⟩ : syracuseStep 2474059 = 3711089) B3711089
theorem B3298745 : Blo 2197435 3298745 := bstep (se 2 (by rfl) ⟨1237029, by rfl⟩ : syracuseStep 3298745 = 2474059) B2474059
theorem B2199163 : Blo 2197435 2199163 := bstep (se 1 (by rfl) ⟨1649372, by rfl⟩ : syracuseStep 2199163 = 3298745) B3298745
theorem B9038341 : Blo 2197435 9038341 := bbase (se 4 (by rfl) ⟨847344, by rfl⟩ : syracuseStep 9038341 = 1694689) (by norm_num)
theorem B48204485 : Blo 2197435 48204485 := bstep (se 4 (by rfl) ⟨4519170, by rfl⟩ : syracuseStep 48204485 = 9038341) B9038341
theorem B32136323 : Blo 2197435 32136323 := bstep (se 1 (by rfl) ⟨24102242, by rfl⟩ : syracuseStep 32136323 = 48204485) B48204485
theorem B85696861 : Blo 2197435 85696861 := bstep (se 3 (by rfl) ⟨16068161, by rfl⟩ : syracuseStep 85696861 = 32136323) B32136323
theorem B114262481 : Blo 2197435 114262481 := bstep (se 2 (by rfl) ⟨42848430, by rfl⟩ : syracuseStep 114262481 = 85696861) B85696861
theorem B76174987 : Blo 2197435 76174987 := bstep (se 1 (by rfl) ⟨57131240, by rfl⟩ : syracuseStep 76174987 = 114262481) B114262481
theorem B101566649 : Blo 2197435 101566649 := bstep (se 2 (by rfl) ⟨38087493, by rfl⟩ : syracuseStep 101566649 = 76174987) B76174987
theorem B67711099 : Blo 2197435 67711099 := bstep (se 1 (by rfl) ⟨50783324, by rfl⟩ : syracuseStep 67711099 = 101566649) B101566649
theorem B90281465 : Blo 2197435 90281465 := bstep (se 2 (by rfl) ⟨33855549, by rfl⟩ : syracuseStep 90281465 = 67711099) B67711099
theorem B60187643 : Blo 2197435 60187643 := bstep (se 1 (by rfl) ⟨45140732, by rfl⟩ : syracuseStep 60187643 = 90281465) B90281465
theorem B40125095 : Blo 2197435 40125095 := bstep (se 1 (by rfl) ⟨30093821, by rfl⟩ : syracuseStep 40125095 = 60187643) B60187643
theorem B26750063 : Blo 2197435 26750063 := bstep (se 1 (by rfl) ⟨20062547, by rfl⟩ : syracuseStep 26750063 = 40125095) B40125095
theorem B17833375 : Blo 2197435 17833375 := bstep (se 1 (by rfl) ⟨13375031, by rfl⟩ : syracuseStep 17833375 = 26750063) B26750063
theorem B95111333 : Blo 2197435 95111333 := bstep (se 4 (by rfl) ⟨8916687, by rfl⟩ : syracuseStep 95111333 = 17833375) B17833375
theorem B63407555 : Blo 2197435 63407555 := bstep (se 1 (by rfl) ⟨47555666, by rfl⟩ : syracuseStep 63407555 = 95111333) B95111333
theorem B42271703 : Blo 2197435 42271703 := bstep (se 1 (by rfl) ⟨31703777, by rfl⟩ : syracuseStep 42271703 = 63407555) B63407555
theorem B28181135 : Blo 2197435 28181135 := bstep (se 1 (by rfl) ⟨21135851, by rfl⟩ : syracuseStep 28181135 = 42271703) B42271703
theorem B18787423 : Blo 2197435 18787423 := bstep (se 1 (by rfl) ⟨14090567, by rfl⟩ : syracuseStep 18787423 = 28181135) B28181135
theorem B25049897 : Blo 2197435 25049897 := bstep (se 2 (by rfl) ⟨9393711, by rfl⟩ : syracuseStep 25049897 = 18787423) B18787423
theorem B16699931 : Blo 2197435 16699931 := bstep (se 1 (by rfl) ⟨12524948, by rfl⟩ : syracuseStep 16699931 = 25049897) B25049897
theorem B11133287 : Blo 2197435 11133287 := bstep (se 1 (by rfl) ⟨8349965, by rfl⟩ : syracuseStep 11133287 = 16699931) B16699931
theorem B7422191 : Blo 2197435 7422191 := bstep (se 1 (by rfl) ⟨5566643, by rfl⟩ : syracuseStep 7422191 = 11133287) B11133287
theorem B4948127 : Blo 2197435 4948127 := bstep (se 1 (by rfl) ⟨3711095, by rfl⟩ : syracuseStep 4948127 = 7422191) B7422191
theorem B3298751 : Blo 2197435 3298751 := bstep (se 1 (by rfl) ⟨2474063, by rfl⟩ : syracuseStep 3298751 = 4948127) B4948127
theorem B2199167 : Blo 2197435 2199167 := bstep (se 1 (by rfl) ⟨1649375, by rfl⟩ : syracuseStep 2199167 = 3298751) B3298751
theorem B3298757 : Blo 2197435 3298757 := bbase (se 4 (by rfl) ⟨309258, by rfl⟩ : syracuseStep 3298757 = 618517) (by norm_num)
theorem B2199171 : Blo 2197435 2199171 := bstep (se 1 (by rfl) ⟨1649378, by rfl⟩ : syracuseStep 2199171 = 3298757) B3298757
theorem B3711109 : Blo 2197435 3711109 := bbase (se 4 (by rfl) ⟨347916, by rfl⟩ : syracuseStep 3711109 = 695833) (by norm_num)
theorem B4948145 : Blo 2197435 4948145 := bstep (se 2 (by rfl) ⟨1855554, by rfl⟩ : syracuseStep 4948145 = 3711109) B3711109
theorem B3298763 : Blo 2197435 3298763 := bstep (se 1 (by rfl) ⟨2474072, by rfl⟩ : syracuseStep 3298763 = 4948145) B4948145
theorem B2199175 : Blo 2197435 2199175 := bstep (se 1 (by rfl) ⟨1649381, by rfl⟩ : syracuseStep 2199175 = 3298763) B3298763
theorem B2474077 : Blo 2197435 2474077 := bbase (se 3 (by rfl) ⟨463889, by rfl⟩ : syracuseStep 2474077 = 927779) (by norm_num)
theorem B3298769 : Blo 2197435 3298769 := bstep (se 2 (by rfl) ⟨1237038, by rfl⟩ : syracuseStep 3298769 = 2474077) B2474077
theorem B2199179 : Blo 2197435 2199179 := bstep (se 1 (by rfl) ⟨1649384, by rfl⟩ : syracuseStep 2199179 = 3298769) B3298769
theorem B7422245 : Blo 2197435 7422245 := bbase (se 4 (by rfl) ⟨695835, by rfl⟩ : syracuseStep 7422245 = 1391671) (by norm_num)
theorem B4948163 : Blo 2197435 4948163 := bstep (se 1 (by rfl) ⟨3711122, by rfl⟩ : syracuseStep 4948163 = 7422245) B7422245
theorem B3298775 : Blo 2197435 3298775 := bstep (se 1 (by rfl) ⟨2474081, by rfl⟩ : syracuseStep 3298775 = 4948163) B4948163
theorem B2199183 : Blo 2197435 2199183 := bstep (se 1 (by rfl) ⟨1649387, by rfl⟩ : syracuseStep 2199183 = 3298775) B3298775
theorem B3298781 : Blo 2197435 3298781 := bbase (se 3 (by rfl) ⟨618521, by rfl⟩ : syracuseStep 3298781 = 1237043) (by norm_num)
theorem B2199187 : Blo 2197435 2199187 := bstep (se 1 (by rfl) ⟨1649390, by rfl⟩ : syracuseStep 2199187 = 3298781) B3298781
theorem B4948181 : Blo 2197435 4948181 := bbase (se 7 (by rfl) ⟨57986, by rfl⟩ : syracuseStep 4948181 = 115973) (by norm_num)
theorem B3298787 : Blo 2197435 3298787 := bstep (se 1 (by rfl) ⟨2474090, by rfl⟩ : syracuseStep 3298787 = 4948181) B4948181
theorem B2199191 : Blo 2197435 2199191 := bstep (se 1 (by rfl) ⟨1649393, by rfl⟩ : syracuseStep 2199191 = 3298787) B3298787
theorem B19303829 : Blo 2197435 19303829 := bbase (se 6 (by rfl) ⟨452433, by rfl⟩ : syracuseStep 19303829 = 904867) (by norm_num)
theorem B12869219 : Blo 2197435 12869219 := bstep (se 1 (by rfl) ⟨9651914, by rfl⟩ : syracuseStep 12869219 = 19303829) B19303829
theorem B8579479 : Blo 2197435 8579479 := bstep (se 1 (by rfl) ⟨6434609, by rfl⟩ : syracuseStep 8579479 = 12869219) B12869219
theorem B11439305 : Blo 2197435 11439305 := bstep (se 2 (by rfl) ⟨4289739, by rfl⟩ : syracuseStep 11439305 = 8579479) B8579479
theorem B7626203 : Blo 2197435 7626203 := bstep (se 1 (by rfl) ⟨5719652, by rfl⟩ : syracuseStep 7626203 = 11439305) B11439305
theorem B5084135 : Blo 2197435 5084135 := bstep (se 1 (by rfl) ⟨3813101, by rfl⟩ : syracuseStep 5084135 = 7626203) B7626203
theorem B3389423 : Blo 2197435 3389423 := bstep (se 1 (by rfl) ⟨2542067, by rfl⟩ : syracuseStep 3389423 = 5084135) B5084135
theorem B9038461 : Blo 2197435 9038461 := bstep (se 3 (by rfl) ⟨1694711, by rfl⟩ : syracuseStep 9038461 = 3389423) B3389423
theorem B12051281 : Blo 2197435 12051281 := bstep (se 2 (by rfl) ⟨4519230, by rfl⟩ : syracuseStep 12051281 = 9038461) B9038461
theorem B32136749 : Blo 2197435 32136749 := bstep (se 3 (by rfl) ⟨6025640, by rfl⟩ : syracuseStep 32136749 = 12051281) B12051281
theorem B21424499 : Blo 2197435 21424499 := bstep (se 1 (by rfl) ⟨16068374, by rfl⟩ : syracuseStep 21424499 = 32136749) B32136749
theorem B14282999 : Blo 2197435 14282999 := bstep (se 1 (by rfl) ⟨10712249, by rfl⟩ : syracuseStep 14282999 = 21424499) B21424499
theorem B9521999 : Blo 2197435 9521999 := bstep (se 1 (by rfl) ⟨7141499, by rfl⟩ : syracuseStep 9521999 = 14282999) B14282999
theorem B6347999 : Blo 2197435 6347999 := bstep (se 1 (by rfl) ⟨4760999, by rfl⟩ : syracuseStep 6347999 = 9521999) B9521999
theorem B4231999 : Blo 2197435 4231999 := bstep (se 1 (by rfl) ⟨3173999, by rfl⟩ : syracuseStep 4231999 = 6347999) B6347999
theorem B5642665 : Blo 2197435 5642665 := bstep (se 2 (by rfl) ⟨2115999, by rfl⟩ : syracuseStep 5642665 = 4231999) B4231999
theorem B120376853 : Blo 2197435 120376853 := bstep (se 6 (by rfl) ⟨2821332, by rfl⟩ : syracuseStep 120376853 = 5642665) B5642665
theorem B80251235 : Blo 2197435 80251235 := bstep (se 1 (by rfl) ⟨60188426, by rfl⟩ : syracuseStep 80251235 = 120376853) B120376853
theorem B53500823 : Blo 2197435 53500823 := bstep (se 1 (by rfl) ⟨40125617, by rfl⟩ : syracuseStep 53500823 = 80251235) B80251235
theorem B35667215 : Blo 2197435 35667215 := bstep (se 1 (by rfl) ⟨26750411, by rfl⟩ : syracuseStep 35667215 = 53500823) B53500823
theorem B23778143 : Blo 2197435 23778143 := bstep (se 1 (by rfl) ⟨17833607, by rfl⟩ : syracuseStep 23778143 = 35667215) B35667215
theorem B15852095 : Blo 2197435 15852095 := bstep (se 1 (by rfl) ⟨11889071, by rfl⟩ : syracuseStep 15852095 = 23778143) B23778143
theorem B10568063 : Blo 2197435 10568063 := bstep (se 1 (by rfl) ⟨7926047, by rfl⟩ : syracuseStep 10568063 = 15852095) B15852095
theorem B7045375 : Blo 2197435 7045375 := bstep (se 1 (by rfl) ⟨5284031, by rfl⟩ : syracuseStep 7045375 = 10568063) B10568063
theorem B9393833 : Blo 2197435 9393833 := bstep (se 2 (by rfl) ⟨3522687, by rfl⟩ : syracuseStep 9393833 = 7045375) B7045375
theorem B6262555 : Blo 2197435 6262555 := bstep (se 1 (by rfl) ⟨4696916, by rfl⟩ : syracuseStep 6262555 = 9393833) B9393833
theorem B8350073 : Blo 2197435 8350073 := bstep (se 2 (by rfl) ⟨3131277, by rfl⟩ : syracuseStep 8350073 = 6262555) B6262555
theorem B5566715 : Blo 2197435 5566715 := bstep (se 1 (by rfl) ⟨4175036, by rfl⟩ : syracuseStep 5566715 = 8350073) B8350073
theorem B3711143 : Blo 2197435 3711143 := bstep (se 1 (by rfl) ⟨2783357, by rfl⟩ : syracuseStep 3711143 = 5566715) B5566715
theorem B2474095 : Blo 2197435 2474095 := bstep (se 1 (by rfl) ⟨1855571, by rfl⟩ : syracuseStep 2474095 = 3711143) B3711143
theorem B3298793 : Blo 2197435 3298793 := bstep (se 2 (by rfl) ⟨1237047, by rfl⟩ : syracuseStep 3298793 = 2474095) B2474095
theorem B2199195 : Blo 2197435 2199195 := bstep (se 1 (by rfl) ⟨1649396, by rfl⟩ : syracuseStep 2199195 = 3298793) B3298793
theorem B14090773 : Blo 2197435 14090773 := bbase (se 6 (by rfl) ⟨330252, by rfl⟩ : syracuseStep 14090773 = 660505) (by norm_num)
theorem B18787697 : Blo 2197435 18787697 := bstep (se 2 (by rfl) ⟨7045386, by rfl⟩ : syracuseStep 18787697 = 14090773) B14090773
theorem B12525131 : Blo 2197435 12525131 := bstep (se 1 (by rfl) ⟨9393848, by rfl⟩ : syracuseStep 12525131 = 18787697) B18787697
theorem B8350087 : Blo 2197435 8350087 := bstep (se 1 (by rfl) ⟨6262565, by rfl⟩ : syracuseStep 8350087 = 12525131) B12525131
theorem B11133449 : Blo 2197435 11133449 := bstep (se 2 (by rfl) ⟨4175043, by rfl⟩ : syracuseStep 11133449 = 8350087) B8350087
theorem B7422299 : Blo 2197435 7422299 := bstep (se 1 (by rfl) ⟨5566724, by rfl⟩ : syracuseStep 7422299 = 11133449) B11133449
theorem B4948199 : Blo 2197435 4948199 := bstep (se 1 (by rfl) ⟨3711149, by rfl⟩ : syracuseStep 4948199 = 7422299) B7422299
theorem B3298799 : Blo 2197435 3298799 := bstep (se 1 (by rfl) ⟨2474099, by rfl⟩ : syracuseStep 3298799 = 4948199) B4948199
theorem B2199199 : Blo 2197435 2199199 := bstep (se 1 (by rfl) ⟨1649399, by rfl⟩ : syracuseStep 2199199 = 3298799) B3298799
theorem B3298805 : Blo 2197435 3298805 := bbase (se 5 (by rfl) ⟨154631, by rfl⟩ : syracuseStep 3298805 = 309263) (by norm_num)
theorem B2199203 : Blo 2197435 2199203 := bstep (se 1 (by rfl) ⟨1649402, by rfl⟩ : syracuseStep 2199203 = 3298805) B3298805
theorem B5284061 : Blo 2197435 5284061 := bbase (se 3 (by rfl) ⟨990761, by rfl⟩ : syracuseStep 5284061 = 1981523) (by norm_num)
theorem B3522707 : Blo 2197435 3522707 := bstep (se 1 (by rfl) ⟨2642030, by rfl⟩ : syracuseStep 3522707 = 5284061) B5284061
theorem B2348471 : Blo 2197435 2348471 := bstep (se 1 (by rfl) ⟨1761353, by rfl⟩ : syracuseStep 2348471 = 3522707) B3522707
theorem B6262589 : Blo 2197435 6262589 := bstep (se 3 (by rfl) ⟨1174235, by rfl⟩ : syracuseStep 6262589 = 2348471) B2348471
theorem B4175059 : Blo 2197435 4175059 := bstep (se 1 (by rfl) ⟨3131294, by rfl⟩ : syracuseStep 4175059 = 6262589) B6262589
theorem B5566745 : Blo 2197435 5566745 := bstep (se 2 (by rfl) ⟨2087529, by rfl⟩ : syracuseStep 5566745 = 4175059) B4175059
theorem B3711163 : Blo 2197435 3711163 := bstep (se 1 (by rfl) ⟨2783372, by rfl⟩ : syracuseStep 3711163 = 5566745) B5566745
theorem B4948217 : Blo 2197435 4948217 := bstep (se 2 (by rfl) ⟨1855581, by rfl⟩ : syracuseStep 4948217 = 3711163) B3711163
theorem B3298811 : Blo 2197435 3298811 := bstep (se 1 (by rfl) ⟨2474108, by rfl⟩ : syracuseStep 3298811 = 4948217) B4948217
theorem B2199207 : Blo 2197435 2199207 := bstep (se 1 (by rfl) ⟨1649405, by rfl⟩ : syracuseStep 2199207 = 3298811) B3298811
theorem B2474113 : Blo 2197435 2474113 := bbase (se 2 (by rfl) ⟨927792, by rfl⟩ : syracuseStep 2474113 = 1855585) (by norm_num)
theorem B3298817 : Blo 2197435 3298817 := bstep (se 2 (by rfl) ⟨1237056, by rfl⟩ : syracuseStep 3298817 = 2474113) B2474113
theorem B2199211 : Blo 2197435 2199211 := bstep (se 1 (by rfl) ⟨1649408, by rfl⟩ : syracuseStep 2199211 = 3298817) B3298817
theorem B5566765 : Blo 2197435 5566765 := bbase (se 3 (by rfl) ⟨1043768, by rfl⟩ : syracuseStep 5566765 = 2087537) (by norm_num)
theorem B7422353 : Blo 2197435 7422353 := bstep (se 2 (by rfl) ⟨2783382, by rfl⟩ : syracuseStep 7422353 = 5566765) B5566765
theorem B4948235 : Blo 2197435 4948235 := bstep (se 1 (by rfl) ⟨3711176, by rfl⟩ : syracuseStep 4948235 = 7422353) B7422353
theorem B3298823 : Blo 2197435 3298823 := bstep (se 1 (by rfl) ⟨2474117, by rfl⟩ : syracuseStep 3298823 = 4948235) B4948235
theorem B2199215 : Blo 2197435 2199215 := bstep (se 1 (by rfl) ⟨1649411, by rfl⟩ : syracuseStep 2199215 = 3298823) B3298823
theorem B3298829 : Blo 2197435 3298829 := bbase (se 3 (by rfl) ⟨618530, by rfl⟩ : syracuseStep 3298829 = 1237061) (by norm_num)
theorem B2199219 : Blo 2197435 2199219 := bstep (se 1 (by rfl) ⟨1649414, by rfl⟩ : syracuseStep 2199219 = 3298829) B3298829
theorem B4948253 : Blo 2197435 4948253 := bbase (se 3 (by rfl) ⟨927797, by rfl⟩ : syracuseStep 4948253 = 1855595) (by norm_num)
theorem B3298835 : Blo 2197435 3298835 := bstep (se 1 (by rfl) ⟨2474126, by rfl⟩ : syracuseStep 3298835 = 4948253) B4948253
theorem B2199223 : Blo 2197435 2199223 := bstep (se 1 (by rfl) ⟨1649417, by rfl⟩ : syracuseStep 2199223 = 3298835) B3298835
theorem B3711197 : Blo 2197435 3711197 := bbase (se 3 (by rfl) ⟨695849, by rfl⟩ : syracuseStep 3711197 = 1391699) (by norm_num)
theorem B2474131 : Blo 2197435 2474131 := bstep (se 1 (by rfl) ⟨1855598, by rfl⟩ : syracuseStep 2474131 = 3711197) B3711197
theorem B3298841 : Blo 2197435 3298841 := bstep (se 2 (by rfl) ⟨1237065, by rfl⟩ : syracuseStep 3298841 = 2474131) B2474131
theorem B2199227 : Blo 2197435 2199227 := bstep (se 1 (by rfl) ⟨1649420, by rfl⟩ : syracuseStep 2199227 = 3298841) B3298841
theorem B5284117 : Blo 2197435 5284117 := bbase (se 6 (by rfl) ⟨123846, by rfl⟩ : syracuseStep 5284117 = 247693) (by norm_num)
theorem B7045489 : Blo 2197435 7045489 := bstep (se 2 (by rfl) ⟨2642058, by rfl⟩ : syracuseStep 7045489 = 5284117) B5284117
theorem B9393985 : Blo 2197435 9393985 := bstep (se 2 (by rfl) ⟨3522744, by rfl⟩ : syracuseStep 9393985 = 7045489) B7045489
theorem B12525313 : Blo 2197435 12525313 := bstep (se 2 (by rfl) ⟨4696992, by rfl⟩ : syracuseStep 12525313 = 9393985) B9393985
theorem B16700417 : Blo 2197435 16700417 := bstep (se 2 (by rfl) ⟨6262656, by rfl⟩ : syracuseStep 16700417 = 12525313) B12525313
theorem B11133611 : Blo 2197435 11133611 := bstep (se 1 (by rfl) ⟨8350208, by rfl⟩ : syracuseStep 11133611 = 16700417) B16700417
theorem B7422407 : Blo 2197435 7422407 := bstep (se 1 (by rfl) ⟨5566805, by rfl⟩ : syracuseStep 7422407 = 11133611) B11133611
theorem B4948271 : Blo 2197435 4948271 := bstep (se 1 (by rfl) ⟨3711203, by rfl⟩ : syracuseStep 4948271 = 7422407) B7422407
theorem B3298847 : Blo 2197435 3298847 := bstep (se 1 (by rfl) ⟨2474135, by rfl⟩ : syracuseStep 3298847 = 4948271) B4948271
theorem B2199231 : Blo 2197435 2199231 := bstep (se 1 (by rfl) ⟨1649423, by rfl⟩ : syracuseStep 2199231 = 3298847) B3298847
theorem B3298853 : Blo 2197435 3298853 := bbase (se 4 (by rfl) ⟨309267, by rfl⟩ : syracuseStep 3298853 = 618535) (by norm_num)
theorem B2199235 : Blo 2197435 2199235 := bstep (se 1 (by rfl) ⟨1649426, by rfl⟩ : syracuseStep 2199235 = 3298853) B3298853
theorem B2783413 : Blo 2197435 2783413 := bbase (se 5 (by rfl) ⟨130472, by rfl⟩ : syracuseStep 2783413 = 260945) (by norm_num)
theorem B3711217 : Blo 2197435 3711217 := bstep (se 2 (by rfl) ⟨1391706, by rfl⟩ : syracuseStep 3711217 = 2783413) B2783413
theorem B4948289 : Blo 2197435 4948289 := bstep (se 2 (by rfl) ⟨1855608, by rfl⟩ : syracuseStep 4948289 = 3711217) B3711217
theorem B3298859 : Blo 2197435 3298859 := bstep (se 1 (by rfl) ⟨2474144, by rfl⟩ : syracuseStep 3298859 = 4948289) B4948289
theorem B2199239 : Blo 2197435 2199239 := bstep (se 1 (by rfl) ⟨1649429, by rfl⟩ : syracuseStep 2199239 = 3298859) B3298859
theorem B2474149 : Blo 2197435 2474149 := bbase (se 4 (by rfl) ⟨231951, by rfl⟩ : syracuseStep 2474149 = 463903) (by norm_num)
theorem B3298865 : Blo 2197435 3298865 := bstep (se 2 (by rfl) ⟨1237074, by rfl⟩ : syracuseStep 3298865 = 2474149) B2474149
theorem B2199243 : Blo 2197435 2199243 := bstep (se 1 (by rfl) ⟨1649432, by rfl⟩ : syracuseStep 2199243 = 3298865) B3298865
theorem B15852469 : Blo 2197435 15852469 := bbase (se 5 (by rfl) ⟨743084, by rfl⟩ : syracuseStep 15852469 = 1486169) (by norm_num)
theorem B21136625 : Blo 2197435 21136625 := bstep (se 2 (by rfl) ⟨7926234, by rfl⟩ : syracuseStep 21136625 = 15852469) B15852469
theorem B14091083 : Blo 2197435 14091083 := bstep (se 1 (by rfl) ⟨10568312, by rfl⟩ : syracuseStep 14091083 = 21136625) B21136625
theorem B9394055 : Blo 2197435 9394055 := bstep (se 1 (by rfl) ⟨7045541, by rfl⟩ : syracuseStep 9394055 = 14091083) B14091083
theorem B6262703 : Blo 2197435 6262703 := bstep (se 1 (by rfl) ⟨4697027, by rfl⟩ : syracuseStep 6262703 = 9394055) B9394055
theorem B4175135 : Blo 2197435 4175135 := bstep (se 1 (by rfl) ⟨3131351, by rfl⟩ : syracuseStep 4175135 = 6262703) B6262703
theorem B2783423 : Blo 2197435 2783423 := bstep (se 1 (by rfl) ⟨2087567, by rfl⟩ : syracuseStep 2783423 = 4175135) B4175135
theorem B7422461 : Blo 2197435 7422461 := bstep (se 3 (by rfl) ⟨1391711, by rfl⟩ : syracuseStep 7422461 = 2783423) B2783423
theorem B4948307 : Blo 2197435 4948307 := bstep (se 1 (by rfl) ⟨3711230, by rfl⟩ : syracuseStep 4948307 = 7422461) B7422461
theorem B3298871 : Blo 2197435 3298871 := bstep (se 1 (by rfl) ⟨2474153, by rfl⟩ : syracuseStep 3298871 = 4948307) B4948307
theorem B2199247 : Blo 2197435 2199247 := bstep (se 1 (by rfl) ⟨1649435, by rfl⟩ : syracuseStep 2199247 = 3298871) B3298871
theorem B3298877 : Blo 2197435 3298877 := bbase (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) (by norm_num)
theorem B2199251 : Blo 2197435 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B4948325 : Blo 2197435 4948325 := bbase (se 4 (by rfl) ⟨463905, by rfl⟩ : syracuseStep 4948325 = 927811) (by norm_num)
theorem B3298883 : Blo 2197435 3298883 := bstep (se 1 (by rfl) ⟨2474162, by rfl⟩ : syracuseStep 3298883 = 4948325) B4948325
theorem B2199255 : Blo 2197435 2199255 := bstep (se 1 (by rfl) ⟨1649441, by rfl⟩ : syracuseStep 2199255 = 3298883) B3298883
theorem B5566877 : Blo 2197435 5566877 := bbase (se 3 (by rfl) ⟨1043789, by rfl⟩ : syracuseStep 5566877 = 2087579) (by norm_num)
theorem B3711251 : Blo 2197435 3711251 := bstep (se 1 (by rfl) ⟨2783438, by rfl⟩ : syracuseStep 3711251 = 5566877) B5566877
theorem B2474167 : Blo 2197435 2474167 := bstep (se 1 (by rfl) ⟨1855625, by rfl⟩ : syracuseStep 2474167 = 3711251) B3711251
theorem B3298889 : Blo 2197435 3298889 := bstep (se 2 (by rfl) ⟨1237083, by rfl⟩ : syracuseStep 3298889 = 2474167) B2474167
theorem B2199259 : Blo 2197435 2199259 := bstep (se 1 (by rfl) ⟨1649444, by rfl⟩ : syracuseStep 2199259 = 3298889) B3298889
theorem B4175165 : Blo 2197435 4175165 := bbase (se 3 (by rfl) ⟨782843, by rfl⟩ : syracuseStep 4175165 = 1565687) (by norm_num)
theorem B11133773 : Blo 2197435 11133773 := bstep (se 3 (by rfl) ⟨2087582, by rfl⟩ : syracuseStep 11133773 = 4175165) B4175165
theorem B7422515 : Blo 2197435 7422515 := bstep (se 1 (by rfl) ⟨5566886, by rfl⟩ : syracuseStep 7422515 = 11133773) B11133773
theorem B4948343 : Blo 2197435 4948343 := bstep (se 1 (by rfl) ⟨3711257, by rfl⟩ : syracuseStep 4948343 = 7422515) B7422515
theorem B3298895 : Blo 2197435 3298895 := bstep (se 1 (by rfl) ⟨2474171, by rfl⟩ : syracuseStep 3298895 = 4948343) B4948343
theorem B2199263 : Blo 2197435 2199263 := bstep (se 1 (by rfl) ⟨1649447, by rfl⟩ : syracuseStep 2199263 = 3298895) B3298895
theorem B3298901 : Blo 2197435 3298901 := bbase (se 8 (by rfl) ⟨19329, by rfl⟩ : syracuseStep 3298901 = 38659) (by norm_num)
theorem B2199267 : Blo 2197435 2199267 := bstep (se 1 (by rfl) ⟨1649450, by rfl⟩ : syracuseStep 2199267 = 3298901) B3298901
theorem B4458557 : Blo 2197435 4458557 := bbase (se 3 (by rfl) ⟨835979, by rfl⟩ : syracuseStep 4458557 = 1671959) (by norm_num)
theorem B2972371 : Blo 2197435 2972371 := bstep (se 1 (by rfl) ⟨2229278, by rfl⟩ : syracuseStep 2972371 = 4458557) B4458557
theorem B3963161 : Blo 2197435 3963161 := bstep (se 2 (by rfl) ⟨1486185, by rfl⟩ : syracuseStep 3963161 = 2972371) B2972371
theorem B2642107 : Blo 2197435 2642107 := bstep (se 1 (by rfl) ⟨1981580, by rfl⟩ : syracuseStep 2642107 = 3963161) B3963161
theorem B3522809 : Blo 2197435 3522809 := bstep (se 2 (by rfl) ⟨1321053, by rfl⟩ : syracuseStep 3522809 = 2642107) B2642107
theorem B9394157 : Blo 2197435 9394157 := bstep (se 3 (by rfl) ⟨1761404, by rfl⟩ : syracuseStep 9394157 = 3522809) B3522809
theorem B6262771 : Blo 2197435 6262771 := bstep (se 1 (by rfl) ⟨4697078, by rfl⟩ : syracuseStep 6262771 = 9394157) B9394157
theorem B8350361 : Blo 2197435 8350361 := bstep (se 2 (by rfl) ⟨3131385, by rfl⟩ : syracuseStep 8350361 = 6262771) B6262771
theorem B5566907 : Blo 2197435 5566907 := bstep (se 1 (by rfl) ⟨4175180, by rfl⟩ : syracuseStep 5566907 = 8350361) B8350361
theorem B3711271 : Blo 2197435 3711271 := bstep (se 1 (by rfl) ⟨2783453, by rfl⟩ : syracuseStep 3711271 = 5566907) B5566907
theorem B4948361 : Blo 2197435 4948361 := bstep (se 2 (by rfl) ⟨1855635, by rfl⟩ : syracuseStep 4948361 = 3711271) B3711271
theorem B3298907 : Blo 2197435 3298907 := bstep (se 1 (by rfl) ⟨2474180, by rfl⟩ : syracuseStep 3298907 = 4948361) B4948361
theorem B2199271 : Blo 2197435 2199271 := bstep (se 1 (by rfl) ⟨1649453, by rfl⟩ : syracuseStep 2199271 = 3298907) B3298907
theorem B2474185 : Blo 2197435 2474185 := bbase (se 2 (by rfl) ⟨927819, by rfl⟩ : syracuseStep 2474185 = 1855639) (by norm_num)
theorem B3298913 : Blo 2197435 3298913 := bstep (se 2 (by rfl) ⟨1237092, by rfl⟩ : syracuseStep 3298913 = 2474185) B2474185
theorem B2199275 : Blo 2197435 2199275 := bstep (se 1 (by rfl) ⟨1649456, by rfl⟩ : syracuseStep 2199275 = 3298913) B3298913
theorem B2972381 : Blo 2197435 2972381 := bbase (se 3 (by rfl) ⟨557321, by rfl⟩ : syracuseStep 2972381 = 1114643) (by norm_num)
theorem B7926349 : Blo 2197435 7926349 := bstep (se 3 (by rfl) ⟨1486190, by rfl⟩ : syracuseStep 7926349 = 2972381) B2972381
theorem B10568465 : Blo 2197435 10568465 := bstep (se 2 (by rfl) ⟨3963174, by rfl⟩ : syracuseStep 10568465 = 7926349) B7926349
theorem B7045643 : Blo 2197435 7045643 := bstep (se 1 (by rfl) ⟨5284232, by rfl⟩ : syracuseStep 7045643 = 10568465) B10568465
theorem B18788381 : Blo 2197435 18788381 := bstep (se 3 (by rfl) ⟨3522821, by rfl⟩ : syracuseStep 18788381 = 7045643) B7045643
theorem B12525587 : Blo 2197435 12525587 := bstep (se 1 (by rfl) ⟨9394190, by rfl⟩ : syracuseStep 12525587 = 18788381) B18788381
theorem B8350391 : Blo 2197435 8350391 := bstep (se 1 (by rfl) ⟨6262793, by rfl⟩ : syracuseStep 8350391 = 12525587) B12525587
theorem B5566927 : Blo 2197435 5566927 := bstep (se 1 (by rfl) ⟨4175195, by rfl⟩ : syracuseStep 5566927 = 8350391) B8350391
theorem B7422569 : Blo 2197435 7422569 := bstep (se 2 (by rfl) ⟨2783463, by rfl⟩ : syracuseStep 7422569 = 5566927) B5566927
theorem B4948379 : Blo 2197435 4948379 := bstep (se 1 (by rfl) ⟨3711284, by rfl⟩ : syracuseStep 4948379 = 7422569) B7422569
theorem B3298919 : Blo 2197435 3298919 := bstep (se 1 (by rfl) ⟨2474189, by rfl⟩ : syracuseStep 3298919 = 4948379) B4948379
theorem B2199279 : Blo 2197435 2199279 := bstep (se 1 (by rfl) ⟨1649459, by rfl⟩ : syracuseStep 2199279 = 3298919) B3298919
theorem B3298925 : Blo 2197435 3298925 := bbase (se 3 (by rfl) ⟨618548, by rfl⟩ : syracuseStep 3298925 = 1237097) (by norm_num)
theorem B2199283 : Blo 2197435 2199283 := bstep (se 1 (by rfl) ⟨1649462, by rfl⟩ : syracuseStep 2199283 = 3298925) B3298925
theorem B4948397 : Blo 2197435 4948397 := bbase (se 3 (by rfl) ⟨927824, by rfl⟩ : syracuseStep 4948397 = 1855649) (by norm_num)
theorem B3298931 : Blo 2197435 3298931 := bstep (se 1 (by rfl) ⟨2474198, by rfl⟩ : syracuseStep 3298931 = 4948397) B4948397
theorem B2199287 : Blo 2197435 2199287 := bstep (se 1 (by rfl) ⟨1649465, by rfl⟩ : syracuseStep 2199287 = 3298931) B3298931
theorem B2348561 : Blo 2197435 2348561 := bbase (se 2 (by rfl) ⟨880710, by rfl⟩ : syracuseStep 2348561 = 1761421) (by norm_num)
theorem B6262829 : Blo 2197435 6262829 := bstep (se 3 (by rfl) ⟨1174280, by rfl⟩ : syracuseStep 6262829 = 2348561) B2348561
theorem B4175219 : Blo 2197435 4175219 := bstep (se 1 (by rfl) ⟨3131414, by rfl⟩ : syracuseStep 4175219 = 6262829) B6262829
theorem B2783479 : Blo 2197435 2783479 := bstep (se 1 (by rfl) ⟨2087609, by rfl⟩ : syracuseStep 2783479 = 4175219) B4175219
theorem B3711305 : Blo 2197435 3711305 := bstep (se 2 (by rfl) ⟨1391739, by rfl⟩ : syracuseStep 3711305 = 2783479) B2783479
theorem B2474203 : Blo 2197435 2474203 := bstep (se 1 (by rfl) ⟨1855652, by rfl⟩ : syracuseStep 2474203 = 3711305) B3711305
theorem B3298937 : Blo 2197435 3298937 := bstep (se 2 (by rfl) ⟨1237101, by rfl⟩ : syracuseStep 3298937 = 2474203) B2474203
theorem B2199291 : Blo 2197435 2199291 := bstep (se 1 (by rfl) ⟨1649468, by rfl⟩ : syracuseStep 2199291 = 3298937) B3298937
theorem B32205397 : Blo 2197435 32205397 := bbase (se 8 (by rfl) ⟨188703, by rfl⟩ : syracuseStep 32205397 = 377407) (by norm_num)
theorem B42940529 : Blo 2197435 42940529 := bstep (se 2 (by rfl) ⟨16102698, by rfl⟩ : syracuseStep 42940529 = 32205397) B32205397
theorem B28627019 : Blo 2197435 28627019 := bstep (se 1 (by rfl) ⟨21470264, by rfl⟩ : syracuseStep 28627019 = 42940529) B42940529
theorem B19084679 : Blo 2197435 19084679 := bstep (se 1 (by rfl) ⟨14313509, by rfl⟩ : syracuseStep 19084679 = 28627019) B28627019
theorem B12723119 : Blo 2197435 12723119 := bstep (se 1 (by rfl) ⟨9542339, by rfl⟩ : syracuseStep 12723119 = 19084679) B19084679
theorem B8482079 : Blo 2197435 8482079 := bstep (se 1 (by rfl) ⟨6361559, by rfl⟩ : syracuseStep 8482079 = 12723119) B12723119
theorem B5654719 : Blo 2197435 5654719 := bstep (se 1 (by rfl) ⟨4241039, by rfl⟩ : syracuseStep 5654719 = 8482079) B8482079
theorem B7539625 : Blo 2197435 7539625 := bstep (se 2 (by rfl) ⟨2827359, by rfl⟩ : syracuseStep 7539625 = 5654719) B5654719
theorem B10052833 : Blo 2197435 10052833 := bstep (se 2 (by rfl) ⟨3769812, by rfl⟩ : syracuseStep 10052833 = 7539625) B7539625
theorem B13403777 : Blo 2197435 13403777 := bstep (se 2 (by rfl) ⟨5026416, by rfl⟩ : syracuseStep 13403777 = 10052833) B10052833
theorem B142973621 : Blo 2197435 142973621 := bstep (se 5 (by rfl) ⟨6701888, by rfl⟩ : syracuseStep 142973621 = 13403777) B13403777
theorem B95315747 : Blo 2197435 95315747 := bstep (se 1 (by rfl) ⟨71486810, by rfl⟩ : syracuseStep 95315747 = 142973621) B142973621
theorem B1016701301 : Blo 2197435 1016701301 := bstep (se 5 (by rfl) ⟨47657873, by rfl⟩ : syracuseStep 1016701301 = 95315747) B95315747
theorem B677800867 : Blo 2197435 677800867 := bstep (se 1 (by rfl) ⟨508350650, by rfl⟩ : syracuseStep 677800867 = 1016701301) B1016701301
theorem B903734489 : Blo 2197435 903734489 := bstep (se 2 (by rfl) ⟨338900433, by rfl⟩ : syracuseStep 903734489 = 677800867) B677800867
theorem B602489659 : Blo 2197435 602489659 := bstep (se 1 (by rfl) ⟨451867244, by rfl⟩ : syracuseStep 602489659 = 903734489) B903734489
theorem B803319545 : Blo 2197435 803319545 := bstep (se 2 (by rfl) ⟨301244829, by rfl⟩ : syracuseStep 803319545 = 602489659) B602489659
theorem B2142185453 : Blo 2197435 2142185453 := bstep (se 3 (by rfl) ⟨401659772, by rfl⟩ : syracuseStep 2142185453 = 803319545) B803319545
theorem B1428123635 : Blo 2197435 1428123635 := bstep (se 1 (by rfl) ⟨1071092726, by rfl⟩ : syracuseStep 1428123635 = 2142185453) B2142185453
theorem B952082423 : Blo 2197435 952082423 := bstep (se 1 (by rfl) ⟨714061817, by rfl⟩ : syracuseStep 952082423 = 1428123635) B1428123635
theorem B634721615 : Blo 2197435 634721615 := bstep (se 1 (by rfl) ⟨476041211, by rfl⟩ : syracuseStep 634721615 = 952082423) B952082423
theorem B423147743 : Blo 2197435 423147743 := bstep (se 1 (by rfl) ⟨317360807, by rfl⟩ : syracuseStep 423147743 = 634721615) B634721615
theorem B282098495 : Blo 2197435 282098495 := bstep (se 1 (by rfl) ⟨211573871, by rfl⟩ : syracuseStep 282098495 = 423147743) B423147743
theorem B752262653 : Blo 2197435 752262653 := bstep (se 3 (by rfl) ⟨141049247, by rfl⟩ : syracuseStep 752262653 = 282098495) B282098495
theorem B501508435 : Blo 2197435 501508435 := bstep (se 1 (by rfl) ⟨376131326, by rfl⟩ : syracuseStep 501508435 = 752262653) B752262653
theorem B668677913 : Blo 2197435 668677913 := bstep (se 2 (by rfl) ⟨250754217, by rfl⟩ : syracuseStep 668677913 = 501508435) B501508435
theorem B445785275 : Blo 2197435 445785275 := bstep (se 1 (by rfl) ⟨334338956, by rfl⟩ : syracuseStep 445785275 = 668677913) B668677913
theorem B297190183 : Blo 2197435 297190183 := bstep (se 1 (by rfl) ⟨222892637, by rfl⟩ : syracuseStep 297190183 = 445785275) B445785275
theorem B396253577 : Blo 2197435 396253577 := bstep (se 2 (by rfl) ⟨148595091, by rfl⟩ : syracuseStep 396253577 = 297190183) B297190183
theorem B1056676205 : Blo 2197435 1056676205 := bstep (se 3 (by rfl) ⟨198126788, by rfl⟩ : syracuseStep 1056676205 = 396253577) B396253577
theorem B2817803213 : Blo 2197435 2817803213 := bstep (se 3 (by rfl) ⟨528338102, by rfl⟩ : syracuseStep 2817803213 = 1056676205) B1056676205
theorem B1878535475 : Blo 2197435 1878535475 := bstep (se 1 (by rfl) ⟨1408901606, by rfl⟩ : syracuseStep 1878535475 = 2817803213) B2817803213
theorem B1252356983 : Blo 2197435 1252356983 := bstep (se 1 (by rfl) ⟨939267737, by rfl⟩ : syracuseStep 1252356983 = 1878535475) B1878535475
theorem B834904655 : Blo 2197435 834904655 := bstep (se 1 (by rfl) ⟨626178491, by rfl⟩ : syracuseStep 834904655 = 1252356983) B1252356983
theorem B556603103 : Blo 2197435 556603103 := bstep (se 1 (by rfl) ⟨417452327, by rfl⟩ : syracuseStep 556603103 = 834904655) B834904655
theorem B371068735 : Blo 2197435 371068735 := bstep (se 1 (by rfl) ⟨278301551, by rfl⟩ : syracuseStep 371068735 = 556603103) B556603103
theorem B494758313 : Blo 2197435 494758313 := bstep (se 2 (by rfl) ⟨185534367, by rfl⟩ : syracuseStep 494758313 = 371068735) B371068735
theorem B329838875 : Blo 2197435 329838875 := bstep (se 1 (by rfl) ⟨247379156, by rfl⟩ : syracuseStep 329838875 = 494758313) B494758313
theorem B219892583 : Blo 2197435 219892583 := bstep (se 1 (by rfl) ⟨164919437, by rfl⟩ : syracuseStep 219892583 = 329838875) B329838875
theorem B146595055 : Blo 2197435 146595055 := bstep (se 1 (by rfl) ⟨109946291, by rfl⟩ : syracuseStep 146595055 = 219892583) B219892583
theorem B195460073 : Blo 2197435 195460073 := bstep (se 2 (by rfl) ⟨73297527, by rfl⟩ : syracuseStep 195460073 = 146595055) B146595055
theorem B130306715 : Blo 2197435 130306715 := bstep (se 1 (by rfl) ⟨97730036, by rfl⟩ : syracuseStep 130306715 = 195460073) B195460073
theorem B86871143 : Blo 2197435 86871143 := bstep (se 1 (by rfl) ⟨65153357, by rfl⟩ : syracuseStep 86871143 = 130306715) B130306715
theorem B231656381 : Blo 2197435 231656381 := bstep (se 3 (by rfl) ⟨43435571, by rfl⟩ : syracuseStep 231656381 = 86871143) B86871143
theorem B154437587 : Blo 2197435 154437587 := bstep (se 1 (by rfl) ⟨115828190, by rfl⟩ : syracuseStep 154437587 = 231656381) B231656381
theorem B102958391 : Blo 2197435 102958391 := bstep (se 1 (by rfl) ⟨77218793, by rfl⟩ : syracuseStep 102958391 = 154437587) B154437587
theorem B68638927 : Blo 2197435 68638927 := bstep (se 1 (by rfl) ⟨51479195, by rfl⟩ : syracuseStep 68638927 = 102958391) B102958391
theorem B91518569 : Blo 2197435 91518569 := bstep (se 2 (by rfl) ⟨34319463, by rfl⟩ : syracuseStep 91518569 = 68638927) B68638927
theorem B61012379 : Blo 2197435 61012379 := bstep (se 1 (by rfl) ⟨45759284, by rfl⟩ : syracuseStep 61012379 = 91518569) B91518569
theorem B162699677 : Blo 2197435 162699677 := bstep (se 3 (by rfl) ⟨30506189, by rfl⟩ : syracuseStep 162699677 = 61012379) B61012379
theorem B108466451 : Blo 2197435 108466451 := bstep (se 1 (by rfl) ⟨81349838, by rfl⟩ : syracuseStep 108466451 = 162699677) B162699677
theorem B72310967 : Blo 2197435 72310967 := bstep (se 1 (by rfl) ⟨54233225, by rfl⟩ : syracuseStep 72310967 = 108466451) B108466451
theorem B48207311 : Blo 2197435 48207311 := bstep (se 1 (by rfl) ⟨36155483, by rfl⟩ : syracuseStep 48207311 = 72310967) B72310967
theorem B32138207 : Blo 2197435 32138207 := bstep (se 1 (by rfl) ⟨24103655, by rfl⟩ : syracuseStep 32138207 = 48207311) B48207311
theorem B21425471 : Blo 2197435 21425471 := bstep (se 1 (by rfl) ⟨16069103, by rfl⟩ : syracuseStep 21425471 = 32138207) B32138207
theorem B14283647 : Blo 2197435 14283647 := bstep (se 1 (by rfl) ⟨10712735, by rfl⟩ : syracuseStep 14283647 = 21425471) B21425471
theorem B9522431 : Blo 2197435 9522431 := bstep (se 1 (by rfl) ⟨7141823, by rfl⟩ : syracuseStep 9522431 = 14283647) B14283647
theorem B6348287 : Blo 2197435 6348287 := bstep (se 1 (by rfl) ⟨4761215, by rfl⟩ : syracuseStep 6348287 = 9522431) B9522431
theorem B4232191 : Blo 2197435 4232191 := bstep (se 1 (by rfl) ⟨3174143, by rfl⟩ : syracuseStep 4232191 = 6348287) B6348287
theorem B5642921 : Blo 2197435 5642921 := bstep (se 2 (by rfl) ⟨2116095, by rfl⟩ : syracuseStep 5642921 = 4232191) B4232191
theorem B3761947 : Blo 2197435 3761947 := bstep (se 1 (by rfl) ⟨2821460, by rfl⟩ : syracuseStep 3761947 = 5642921) B5642921
theorem B5015929 : Blo 2197435 5015929 := bstep (se 2 (by rfl) ⟨1880973, by rfl⟩ : syracuseStep 5015929 = 3761947) B3761947
theorem B6687905 : Blo 2197435 6687905 := bstep (se 2 (by rfl) ⟨2507964, by rfl⟩ : syracuseStep 6687905 = 5015929) B5015929
theorem B17834413 : Blo 2197435 17834413 := bstep (se 3 (by rfl) ⟨3343952, by rfl⟩ : syracuseStep 17834413 = 6687905) B6687905
theorem B23779217 : Blo 2197435 23779217 := bstep (se 2 (by rfl) ⟨8917206, by rfl⟩ : syracuseStep 23779217 = 17834413) B17834413
theorem B63411245 : Blo 2197435 63411245 := bstep (se 3 (by rfl) ⟨11889608, by rfl⟩ : syracuseStep 63411245 = 23779217) B23779217
theorem B42274163 : Blo 2197435 42274163 := bstep (se 1 (by rfl) ⟨31705622, by rfl⟩ : syracuseStep 42274163 = 63411245) B63411245
theorem B28182775 : Blo 2197435 28182775 := bstep (se 1 (by rfl) ⟨21137081, by rfl⟩ : syracuseStep 28182775 = 42274163) B42274163
theorem B37577033 : Blo 2197435 37577033 := bstep (se 2 (by rfl) ⟨14091387, by rfl⟩ : syracuseStep 37577033 = 28182775) B28182775
theorem B25051355 : Blo 2197435 25051355 := bstep (se 1 (by rfl) ⟨18788516, by rfl⟩ : syracuseStep 25051355 = 37577033) B37577033
theorem B16700903 : Blo 2197435 16700903 := bstep (se 1 (by rfl) ⟨12525677, by rfl⟩ : syracuseStep 16700903 = 25051355) B25051355
theorem B11133935 : Blo 2197435 11133935 := bstep (se 1 (by rfl) ⟨8350451, by rfl⟩ : syracuseStep 11133935 = 16700903) B16700903
theorem B7422623 : Blo 2197435 7422623 := bstep (se 1 (by rfl) ⟨5566967, by rfl⟩ : syracuseStep 7422623 = 11133935) B11133935
theorem B4948415 : Blo 2197435 4948415 := bstep (se 1 (by rfl) ⟨3711311, by rfl⟩ : syracuseStep 4948415 = 7422623) B7422623
theorem B3298943 : Blo 2197435 3298943 := bstep (se 1 (by rfl) ⟨2474207, by rfl⟩ : syracuseStep 3298943 = 4948415) B4948415
theorem B2199295 : Blo 2197435 2199295 := bstep (se 1 (by rfl) ⟨1649471, by rfl⟩ : syracuseStep 2199295 = 3298943) B3298943
theorem B3298949 : Blo 2197435 3298949 := bbase (se 4 (by rfl) ⟨309276, by rfl⟩ : syracuseStep 3298949 = 618553) (by norm_num)
theorem B2199299 : Blo 2197435 2199299 := bstep (se 1 (by rfl) ⟨1649474, by rfl⟩ : syracuseStep 2199299 = 3298949) B3298949
theorem B3711325 : Blo 2197435 3711325 := bbase (se 3 (by rfl) ⟨695873, by rfl⟩ : syracuseStep 3711325 = 1391747) (by norm_num)
theorem B4948433 : Blo 2197435 4948433 := bstep (se 2 (by rfl) ⟨1855662, by rfl⟩ : syracuseStep 4948433 = 3711325) B3711325
theorem B3298955 : Blo 2197435 3298955 := bstep (se 1 (by rfl) ⟨2474216, by rfl⟩ : syracuseStep 3298955 = 4948433) B4948433
theorem B2199303 : Blo 2197435 2199303 := bstep (se 1 (by rfl) ⟨1649477, by rfl⟩ : syracuseStep 2199303 = 3298955) B3298955
theorem B2474221 : Blo 2197435 2474221 := bbase (se 3 (by rfl) ⟨463916, by rfl⟩ : syracuseStep 2474221 = 927833) (by norm_num)
theorem B3298961 : Blo 2197435 3298961 := bstep (se 2 (by rfl) ⟨1237110, by rfl⟩ : syracuseStep 3298961 = 2474221) B2474221
theorem B2199307 : Blo 2197435 2199307 := bstep (se 1 (by rfl) ⟨1649480, by rfl⟩ : syracuseStep 2199307 = 3298961) B3298961
theorem B7422677 : Blo 2197435 7422677 := bbase (se 7 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 7422677 = 173969) (by norm_num)
theorem B4948451 : Blo 2197435 4948451 := bstep (se 1 (by rfl) ⟨3711338, by rfl⟩ : syracuseStep 4948451 = 7422677) B7422677
theorem B3298967 : Blo 2197435 3298967 := bstep (se 1 (by rfl) ⟨2474225, by rfl⟩ : syracuseStep 3298967 = 4948451) B4948451
theorem B2199311 : Blo 2197435 2199311 := bstep (se 1 (by rfl) ⟨1649483, by rfl⟩ : syracuseStep 2199311 = 3298967) B3298967
theorem B3298973 : Blo 2197435 3298973 := bbase (se 3 (by rfl) ⟨618557, by rfl⟩ : syracuseStep 3298973 = 1237115) (by norm_num)
theorem B2199315 : Blo 2197435 2199315 := bstep (se 1 (by rfl) ⟨1649486, by rfl⟩ : syracuseStep 2199315 = 3298973) B3298973
theorem B4948469 : Blo 2197435 4948469 := bbase (se 5 (by rfl) ⟨231959, by rfl⟩ : syracuseStep 4948469 = 463919) (by norm_num)
theorem B3298979 : Blo 2197435 3298979 := bstep (se 1 (by rfl) ⟨2474234, by rfl⟩ : syracuseStep 3298979 = 4948469) B4948469
theorem B2199319 : Blo 2197435 2199319 := bstep (se 1 (by rfl) ⟨1649489, by rfl⟩ : syracuseStep 2199319 = 3298979) B3298979
theorem B42274709 : Blo 2197435 42274709 := bbase (se 6 (by rfl) ⟨990813, by rfl⟩ : syracuseStep 42274709 = 1981627) (by norm_num)
theorem B28183139 : Blo 2197435 28183139 := bstep (se 1 (by rfl) ⟨21137354, by rfl⟩ : syracuseStep 28183139 = 42274709) B42274709
theorem B18788759 : Blo 2197435 18788759 := bstep (se 1 (by rfl) ⟨14091569, by rfl⟩ : syracuseStep 18788759 = 28183139) B28183139
theorem B12525839 : Blo 2197435 12525839 := bstep (se 1 (by rfl) ⟨9394379, by rfl⟩ : syracuseStep 12525839 = 18788759) B18788759
theorem B8350559 : Blo 2197435 8350559 := bstep (se 1 (by rfl) ⟨6262919, by rfl⟩ : syracuseStep 8350559 = 12525839) B12525839
theorem B5567039 : Blo 2197435 5567039 := bstep (se 1 (by rfl) ⟨4175279, by rfl⟩ : syracuseStep 5567039 = 8350559) B8350559
theorem B3711359 : Blo 2197435 3711359 := bstep (se 1 (by rfl) ⟨2783519, by rfl⟩ : syracuseStep 3711359 = 5567039) B5567039
theorem B2474239 : Blo 2197435 2474239 := bstep (se 1 (by rfl) ⟨1855679, by rfl⟩ : syracuseStep 2474239 = 3711359) B3711359
theorem B3298985 : Blo 2197435 3298985 := bstep (se 2 (by rfl) ⟨1237119, by rfl⟩ : syracuseStep 3298985 = 2474239) B2474239
theorem B2199323 : Blo 2197435 2199323 := bstep (se 1 (by rfl) ⟨1649492, by rfl⟩ : syracuseStep 2199323 = 3298985) B3298985
theorem B5284349 : Blo 2197435 5284349 := bbase (se 3 (by rfl) ⟨990815, by rfl⟩ : syracuseStep 5284349 = 1981631) (by norm_num)
theorem B3522899 : Blo 2197435 3522899 := bstep (se 1 (by rfl) ⟨2642174, by rfl⟩ : syracuseStep 3522899 = 5284349) B5284349
theorem B2348599 : Blo 2197435 2348599 := bstep (se 1 (by rfl) ⟨1761449, by rfl⟩ : syracuseStep 2348599 = 3522899) B3522899
theorem B3131465 : Blo 2197435 3131465 := bstep (se 2 (by rfl) ⟨1174299, by rfl⟩ : syracuseStep 3131465 = 2348599) B2348599
theorem B8350573 : Blo 2197435 8350573 := bstep (se 3 (by rfl) ⟨1565732, by rfl⟩ : syracuseStep 8350573 = 3131465) B3131465
theorem B11134097 : Blo 2197435 11134097 := bstep (se 2 (by rfl) ⟨4175286, by rfl⟩ : syracuseStep 11134097 = 8350573) B8350573
theorem B7422731 : Blo 2197435 7422731 := bstep (se 1 (by rfl) ⟨5567048, by rfl⟩ : syracuseStep 7422731 = 11134097) B11134097
theorem B4948487 : Blo 2197435 4948487 := bstep (se 1 (by rfl) ⟨3711365, by rfl⟩ : syracuseStep 4948487 = 7422731) B7422731
theorem B3298991 : Blo 2197435 3298991 := bstep (se 1 (by rfl) ⟨2474243, by rfl⟩ : syracuseStep 3298991 = 4948487) B4948487
theorem B2199327 : Blo 2197435 2199327 := bstep (se 1 (by rfl) ⟨1649495, by rfl⟩ : syracuseStep 2199327 = 3298991) B3298991
theorem B3298997 : Blo 2197435 3298997 := bbase (se 5 (by rfl) ⟨154640, by rfl⟩ : syracuseStep 3298997 = 309281) (by norm_num)
theorem B2199331 : Blo 2197435 2199331 := bstep (se 1 (by rfl) ⟨1649498, by rfl⟩ : syracuseStep 2199331 = 3298997) B3298997
theorem B5567069 : Blo 2197435 5567069 := bbase (se 3 (by rfl) ⟨1043825, by rfl⟩ : syracuseStep 5567069 = 2087651) (by norm_num)
theorem B3711379 : Blo 2197435 3711379 := bstep (se 1 (by rfl) ⟨2783534, by rfl⟩ : syracuseStep 3711379 = 5567069) B5567069
theorem B4948505 : Blo 2197435 4948505 := bstep (se 2 (by rfl) ⟨1855689, by rfl⟩ : syracuseStep 4948505 = 3711379) B3711379
theorem B3299003 : Blo 2197435 3299003 := bstep (se 1 (by rfl) ⟨2474252, by rfl⟩ : syracuseStep 3299003 = 4948505) B4948505
theorem B2199335 : Blo 2197435 2199335 := bstep (se 1 (by rfl) ⟨1649501, by rfl⟩ : syracuseStep 2199335 = 3299003) B3299003
theorem B2474257 : Blo 2197435 2474257 := bbase (se 2 (by rfl) ⟨927846, by rfl⟩ : syracuseStep 2474257 = 1855693) (by norm_num)
theorem B3299009 : Blo 2197435 3299009 := bstep (se 2 (by rfl) ⟨1237128, by rfl⟩ : syracuseStep 3299009 = 2474257) B2474257
theorem B2199339 : Blo 2197435 2199339 := bstep (se 1 (by rfl) ⟨1649504, by rfl⟩ : syracuseStep 2199339 = 3299009) B3299009
theorem B4175317 : Blo 2197435 4175317 := bbase (se 7 (by rfl) ⟨48929, by rfl⟩ : syracuseStep 4175317 = 97859) (by norm_num)
theorem B5567089 : Blo 2197435 5567089 := bstep (se 2 (by rfl) ⟨2087658, by rfl⟩ : syracuseStep 5567089 = 4175317) B4175317
theorem B7422785 : Blo 2197435 7422785 := bstep (se 2 (by rfl) ⟨2783544, by rfl⟩ : syracuseStep 7422785 = 5567089) B5567089
theorem B4948523 : Blo 2197435 4948523 := bstep (se 1 (by rfl) ⟨3711392, by rfl⟩ : syracuseStep 4948523 = 7422785) B7422785
theorem B3299015 : Blo 2197435 3299015 := bstep (se 1 (by rfl) ⟨2474261, by rfl⟩ : syracuseStep 3299015 = 4948523) B4948523
theorem B2199343 : Blo 2197435 2199343 := bstep (se 1 (by rfl) ⟨1649507, by rfl⟩ : syracuseStep 2199343 = 3299015) B3299015
theorem B3299021 : Blo 2197435 3299021 := bbase (se 3 (by rfl) ⟨618566, by rfl⟩ : syracuseStep 3299021 = 1237133) (by norm_num)
theorem B2199347 : Blo 2197435 2199347 := bstep (se 1 (by rfl) ⟨1649510, by rfl⟩ : syracuseStep 2199347 = 3299021) B3299021
theorem B4948541 : Blo 2197435 4948541 := bbase (se 3 (by rfl) ⟨927851, by rfl⟩ : syracuseStep 4948541 = 1855703) (by norm_num)
theorem B3299027 : Blo 2197435 3299027 := bstep (se 1 (by rfl) ⟨2474270, by rfl⟩ : syracuseStep 3299027 = 4948541) B4948541
theorem B2199351 : Blo 2197435 2199351 := bstep (se 1 (by rfl) ⟨1649513, by rfl⟩ : syracuseStep 2199351 = 3299027) B3299027
theorem B3711413 : Blo 2197435 3711413 := bbase (se 5 (by rfl) ⟨173972, by rfl⟩ : syracuseStep 3711413 = 347945) (by norm_num)
theorem B2474275 : Blo 2197435 2474275 := bstep (se 1 (by rfl) ⟨1855706, by rfl⟩ : syracuseStep 2474275 = 3711413) B3711413
theorem B3299033 : Blo 2197435 3299033 := bstep (se 2 (by rfl) ⟨1237137, by rfl⟩ : syracuseStep 3299033 = 2474275) B2474275
theorem B2199355 : Blo 2197435 2199355 := bstep (se 1 (by rfl) ⟨1649516, by rfl⟩ : syracuseStep 2199355 = 3299033) B3299033
theorem B2348633 : Blo 2197435 2348633 := bbase (se 2 (by rfl) ⟨880737, by rfl⟩ : syracuseStep 2348633 = 1761475) (by norm_num)
theorem B6263021 : Blo 2197435 6263021 := bstep (se 3 (by rfl) ⟨1174316, by rfl⟩ : syracuseStep 6263021 = 2348633) B2348633
theorem B16701389 : Blo 2197435 16701389 := bstep (se 3 (by rfl) ⟨3131510, by rfl⟩ : syracuseStep 16701389 = 6263021) B6263021
theorem B11134259 : Blo 2197435 11134259 := bstep (se 1 (by rfl) ⟨8350694, by rfl⟩ : syracuseStep 11134259 = 16701389) B16701389
theorem B7422839 : Blo 2197435 7422839 := bstep (se 1 (by rfl) ⟨5567129, by rfl⟩ : syracuseStep 7422839 = 11134259) B11134259
theorem B4948559 : Blo 2197435 4948559 := bstep (se 1 (by rfl) ⟨3711419, by rfl⟩ : syracuseStep 4948559 = 7422839) B7422839
theorem B3299039 : Blo 2197435 3299039 := bstep (se 1 (by rfl) ⟨2474279, by rfl⟩ : syracuseStep 3299039 = 4948559) B4948559
theorem B2199359 : Blo 2197435 2199359 := bstep (se 1 (by rfl) ⟨1649519, by rfl⟩ : syracuseStep 2199359 = 3299039) B3299039
theorem B3299045 : Blo 2197435 3299045 := bbase (se 4 (by rfl) ⟨309285, by rfl⟩ : syracuseStep 3299045 = 618571) (by norm_num)
theorem B2199363 : Blo 2197435 2199363 := bstep (se 1 (by rfl) ⟨1649522, by rfl⟩ : syracuseStep 2199363 = 3299045) B3299045
theorem B6263045 : Blo 2197435 6263045 := bbase (se 4 (by rfl) ⟨587160, by rfl⟩ : syracuseStep 6263045 = 1174321) (by norm_num)
theorem B4175363 : Blo 2197435 4175363 := bstep (se 1 (by rfl) ⟨3131522, by rfl⟩ : syracuseStep 4175363 = 6263045) B6263045
theorem B2783575 : Blo 2197435 2783575 := bstep (se 1 (by rfl) ⟨2087681, by rfl⟩ : syracuseStep 2783575 = 4175363) B4175363
theorem B3711433 : Blo 2197435 3711433 := bstep (se 2 (by rfl) ⟨1391787, by rfl⟩ : syracuseStep 3711433 = 2783575) B2783575
theorem B4948577 : Blo 2197435 4948577 := bstep (se 2 (by rfl) ⟨1855716, by rfl⟩ : syracuseStep 4948577 = 3711433) B3711433
theorem B3299051 : Blo 2197435 3299051 := bstep (se 1 (by rfl) ⟨2474288, by rfl⟩ : syracuseStep 3299051 = 4948577) B4948577
theorem B2199367 : Blo 2197435 2199367 := bstep (se 1 (by rfl) ⟨1649525, by rfl⟩ : syracuseStep 2199367 = 3299051) B3299051
theorem B2474293 : Blo 2197435 2474293 := bbase (se 5 (by rfl) ⟨115982, by rfl⟩ : syracuseStep 2474293 = 231965) (by norm_num)
theorem B3299057 : Blo 2197435 3299057 := bstep (se 2 (by rfl) ⟨1237146, by rfl⟩ : syracuseStep 3299057 = 2474293) B2474293
theorem B2199371 : Blo 2197435 2199371 := bstep (se 1 (by rfl) ⟨1649528, by rfl⟩ : syracuseStep 2199371 = 3299057) B3299057
theorem B2783585 : Blo 2197435 2783585 := bbase (se 2 (by rfl) ⟨1043844, by rfl⟩ : syracuseStep 2783585 = 2087689) (by norm_num)
theorem B7422893 : Blo 2197435 7422893 := bstep (se 3 (by rfl) ⟨1391792, by rfl⟩ : syracuseStep 7422893 = 2783585) B2783585
theorem B4948595 : Blo 2197435 4948595 := bstep (se 1 (by rfl) ⟨3711446, by rfl⟩ : syracuseStep 4948595 = 7422893) B7422893
theorem B3299063 : Blo 2197435 3299063 := bstep (se 1 (by rfl) ⟨2474297, by rfl⟩ : syracuseStep 3299063 = 4948595) B4948595
theorem B2199375 : Blo 2197435 2199375 := bstep (se 1 (by rfl) ⟨1649531, by rfl⟩ : syracuseStep 2199375 = 3299063) B3299063
theorem B3299069 : Blo 2197435 3299069 := bbase (se 3 (by rfl) ⟨618575, by rfl⟩ : syracuseStep 3299069 = 1237151) (by norm_num)
theorem B2199379 : Blo 2197435 2199379 := bstep (se 1 (by rfl) ⟨1649534, by rfl⟩ : syracuseStep 2199379 = 3299069) B3299069
theorem B4948613 : Blo 2197435 4948613 := bbase (se 4 (by rfl) ⟨463932, by rfl⟩ : syracuseStep 4948613 = 927865) (by norm_num)
theorem B3299075 : Blo 2197435 3299075 := bstep (se 1 (by rfl) ⟨2474306, by rfl⟩ : syracuseStep 3299075 = 4948613) B4948613
theorem B2199383 : Blo 2197435 2199383 := bstep (se 1 (by rfl) ⟨1649537, by rfl⟩ : syracuseStep 2199383 = 3299075) B3299075
theorem B228547925 : Blo 2197435 228547925 := bbase (se 11 (by rfl) ⟨167393, by rfl⟩ : syracuseStep 228547925 = 334787) (by norm_num)
theorem B152365283 : Blo 2197435 152365283 := bstep (se 1 (by rfl) ⟨114273962, by rfl⟩ : syracuseStep 152365283 = 228547925) B228547925
theorem B101576855 : Blo 2197435 101576855 := bstep (se 1 (by rfl) ⟨76182641, by rfl⟩ : syracuseStep 101576855 = 152365283) B152365283
theorem B67717903 : Blo 2197435 67717903 := bstep (se 1 (by rfl) ⟨50788427, by rfl⟩ : syracuseStep 67717903 = 101576855) B101576855
theorem B90290537 : Blo 2197435 90290537 := bstep (se 2 (by rfl) ⟨33858951, by rfl⟩ : syracuseStep 90290537 = 67717903) B67717903
theorem B60193691 : Blo 2197435 60193691 := bstep (se 1 (by rfl) ⟨45145268, by rfl⟩ : syracuseStep 60193691 = 90290537) B90290537
theorem B40129127 : Blo 2197435 40129127 := bstep (se 1 (by rfl) ⟨30096845, by rfl⟩ : syracuseStep 40129127 = 60193691) B60193691
theorem B26752751 : Blo 2197435 26752751 := bstep (se 1 (by rfl) ⟨20064563, by rfl⟩ : syracuseStep 26752751 = 40129127) B40129127
theorem B17835167 : Blo 2197435 17835167 := bstep (se 1 (by rfl) ⟨13376375, by rfl⟩ : syracuseStep 17835167 = 26752751) B26752751
theorem B11890111 : Blo 2197435 11890111 := bstep (se 1 (by rfl) ⟨8917583, by rfl⟩ : syracuseStep 11890111 = 17835167) B17835167
theorem B15853481 : Blo 2197435 15853481 := bstep (se 2 (by rfl) ⟨5945055, by rfl⟩ : syracuseStep 15853481 = 11890111) B11890111
theorem B10568987 : Blo 2197435 10568987 := bstep (se 1 (by rfl) ⟨7926740, by rfl⟩ : syracuseStep 10568987 = 15853481) B15853481
theorem B7045991 : Blo 2197435 7045991 := bstep (se 1 (by rfl) ⟨5284493, by rfl⟩ : syracuseStep 7045991 = 10568987) B10568987
theorem B4697327 : Blo 2197435 4697327 := bstep (se 1 (by rfl) ⟨3522995, by rfl⟩ : syracuseStep 4697327 = 7045991) B7045991
theorem B3131551 : Blo 2197435 3131551 := bstep (se 1 (by rfl) ⟨2348663, by rfl⟩ : syracuseStep 3131551 = 4697327) B4697327
theorem B4175401 : Blo 2197435 4175401 := bstep (se 2 (by rfl) ⟨1565775, by rfl⟩ : syracuseStep 4175401 = 3131551) B3131551
theorem B5567201 : Blo 2197435 5567201 := bstep (se 2 (by rfl) ⟨2087700, by rfl⟩ : syracuseStep 5567201 = 4175401) B4175401
theorem B3711467 : Blo 2197435 3711467 := bstep (se 1 (by rfl) ⟨2783600, by rfl⟩ : syracuseStep 3711467 = 5567201) B5567201
theorem B2474311 : Blo 2197435 2474311 := bstep (se 1 (by rfl) ⟨1855733, by rfl⟩ : syracuseStep 2474311 = 3711467) B3711467
theorem B3299081 : Blo 2197435 3299081 := bstep (se 2 (by rfl) ⟨1237155, by rfl⟩ : syracuseStep 3299081 = 2474311) B2474311
theorem B2199387 : Blo 2197435 2199387 := bstep (se 1 (by rfl) ⟨1649540, by rfl⟩ : syracuseStep 2199387 = 3299081) B3299081
theorem B11134421 : Blo 2197435 11134421 := bbase (se 7 (by rfl) ⟨130481, by rfl⟩ : syracuseStep 11134421 = 260963) (by norm_num)
theorem B7422947 : Blo 2197435 7422947 := bstep (se 1 (by rfl) ⟨5567210, by rfl⟩ : syracuseStep 7422947 = 11134421) B11134421
theorem B4948631 : Blo 2197435 4948631 := bstep (se 1 (by rfl) ⟨3711473, by rfl⟩ : syracuseStep 4948631 = 7422947) B7422947
theorem B3299087 : Blo 2197435 3299087 := bstep (se 1 (by rfl) ⟨2474315, by rfl⟩ : syracuseStep 3299087 = 4948631) B4948631
theorem B2199391 : Blo 2197435 2199391 := bstep (se 1 (by rfl) ⟨1649543, by rfl⟩ : syracuseStep 2199391 = 3299087) B3299087
theorem B3299093 : Blo 2197435 3299093 := bbase (se 6 (by rfl) ⟨77322, by rfl⟩ : syracuseStep 3299093 = 154645) (by norm_num)
theorem B2199395 : Blo 2197435 2199395 := bstep (se 1 (by rfl) ⟨1649546, by rfl⟩ : syracuseStep 2199395 = 3299093) B3299093
theorem B3482861 : Blo 2197435 3482861 := bbase (se 3 (by rfl) ⟨653036, by rfl⟩ : syracuseStep 3482861 = 1306073) (by norm_num)
theorem B9287629 : Blo 2197435 9287629 := bstep (se 3 (by rfl) ⟨1741430, by rfl⟩ : syracuseStep 9287629 = 3482861) B3482861
theorem B49534021 : Blo 2197435 49534021 := bstep (se 4 (by rfl) ⟨4643814, by rfl⟩ : syracuseStep 49534021 = 9287629) B9287629
theorem B264181445 : Blo 2197435 264181445 := bstep (se 4 (by rfl) ⟨24767010, by rfl⟩ : syracuseStep 264181445 = 49534021) B49534021
theorem B176120963 : Blo 2197435 176120963 := bstep (se 1 (by rfl) ⟨132090722, by rfl⟩ : syracuseStep 176120963 = 264181445) B264181445
theorem B117413975 : Blo 2197435 117413975 := bstep (se 1 (by rfl) ⟨88060481, by rfl⟩ : syracuseStep 117413975 = 176120963) B176120963
theorem B78275983 : Blo 2197435 78275983 := bstep (se 1 (by rfl) ⟨58706987, by rfl⟩ : syracuseStep 78275983 = 117413975) B117413975
theorem B104367977 : Blo 2197435 104367977 := bstep (se 2 (by rfl) ⟨39137991, by rfl⟩ : syracuseStep 104367977 = 78275983) B78275983
theorem B69578651 : Blo 2197435 69578651 := bstep (se 1 (by rfl) ⟨52183988, by rfl⟩ : syracuseStep 69578651 = 104367977) B104367977
theorem B46385767 : Blo 2197435 46385767 := bstep (se 1 (by rfl) ⟨34789325, by rfl⟩ : syracuseStep 46385767 = 69578651) B69578651
theorem B247390757 : Blo 2197435 247390757 := bstep (se 4 (by rfl) ⟨23192883, by rfl⟩ : syracuseStep 247390757 = 46385767) B46385767
theorem B164927171 : Blo 2197435 164927171 := bstep (se 1 (by rfl) ⟨123695378, by rfl⟩ : syracuseStep 164927171 = 247390757) B247390757
theorem B109951447 : Blo 2197435 109951447 := bstep (se 1 (by rfl) ⟨82463585, by rfl⟩ : syracuseStep 109951447 = 164927171) B164927171
theorem B146601929 : Blo 2197435 146601929 := bstep (se 2 (by rfl) ⟨54975723, by rfl⟩ : syracuseStep 146601929 = 109951447) B109951447
theorem B97734619 : Blo 2197435 97734619 := bstep (se 1 (by rfl) ⟨73300964, by rfl⟩ : syracuseStep 97734619 = 146601929) B146601929
theorem B521251301 : Blo 2197435 521251301 := bstep (se 4 (by rfl) ⟨48867309, by rfl⟩ : syracuseStep 521251301 = 97734619) B97734619
theorem B347500867 : Blo 2197435 347500867 := bstep (se 1 (by rfl) ⟨260625650, by rfl⟩ : syracuseStep 347500867 = 521251301) B521251301
theorem B463334489 : Blo 2197435 463334489 := bstep (se 2 (by rfl) ⟨173750433, by rfl⟩ : syracuseStep 463334489 = 347500867) B347500867
theorem B308889659 : Blo 2197435 308889659 := bstep (se 1 (by rfl) ⟨231667244, by rfl⟩ : syracuseStep 308889659 = 463334489) B463334489
theorem B823705757 : Blo 2197435 823705757 := bstep (se 3 (by rfl) ⟨154444829, by rfl⟩ : syracuseStep 823705757 = 308889659) B308889659
theorem B549137171 : Blo 2197435 549137171 := bstep (se 1 (by rfl) ⟨411852878, by rfl⟩ : syracuseStep 549137171 = 823705757) B823705757
theorem B1464365789 : Blo 2197435 1464365789 := bstep (se 3 (by rfl) ⟨274568585, by rfl⟩ : syracuseStep 1464365789 = 549137171) B549137171
theorem B976243859 : Blo 2197435 976243859 := bstep (se 1 (by rfl) ⟨732182894, by rfl⟩ : syracuseStep 976243859 = 1464365789) B1464365789
theorem B650829239 : Blo 2197435 650829239 := bstep (se 1 (by rfl) ⟨488121929, by rfl⟩ : syracuseStep 650829239 = 976243859) B976243859
theorem B433886159 : Blo 2197435 433886159 := bstep (se 1 (by rfl) ⟨325414619, by rfl⟩ : syracuseStep 433886159 = 650829239) B650829239
theorem B289257439 : Blo 2197435 289257439 := bstep (se 1 (by rfl) ⟨216943079, by rfl⟩ : syracuseStep 289257439 = 433886159) B433886159
theorem B385676585 : Blo 2197435 385676585 := bstep (se 2 (by rfl) ⟨144628719, by rfl⟩ : syracuseStep 385676585 = 289257439) B289257439
theorem B257117723 : Blo 2197435 257117723 := bstep (se 1 (by rfl) ⟨192838292, by rfl⟩ : syracuseStep 257117723 = 385676585) B385676585
theorem B171411815 : Blo 2197435 171411815 := bstep (se 1 (by rfl) ⟨128558861, by rfl⟩ : syracuseStep 171411815 = 257117723) B257117723
theorem B457098173 : Blo 2197435 457098173 := bstep (se 3 (by rfl) ⟨85705907, by rfl⟩ : syracuseStep 457098173 = 171411815) B171411815
theorem B304732115 : Blo 2197435 304732115 := bstep (se 1 (by rfl) ⟨228549086, by rfl⟩ : syracuseStep 304732115 = 457098173) B457098173
theorem B203154743 : Blo 2197435 203154743 := bstep (se 1 (by rfl) ⟨152366057, by rfl⟩ : syracuseStep 203154743 = 304732115) B304732115
theorem B135436495 : Blo 2197435 135436495 := bstep (se 1 (by rfl) ⟨101577371, by rfl⟩ : syracuseStep 135436495 = 203154743) B203154743
theorem B180581993 : Blo 2197435 180581993 := bstep (se 2 (by rfl) ⟨67718247, by rfl⟩ : syracuseStep 180581993 = 135436495) B135436495
theorem B120387995 : Blo 2197435 120387995 := bstep (se 1 (by rfl) ⟨90290996, by rfl⟩ : syracuseStep 120387995 = 180581993) B180581993
theorem B80258663 : Blo 2197435 80258663 := bstep (se 1 (by rfl) ⟨60193997, by rfl⟩ : syracuseStep 80258663 = 120387995) B120387995
theorem B53505775 : Blo 2197435 53505775 := bstep (se 1 (by rfl) ⟨40129331, by rfl⟩ : syracuseStep 53505775 = 80258663) B80258663
theorem B71341033 : Blo 2197435 71341033 := bstep (se 2 (by rfl) ⟨26752887, by rfl⟩ : syracuseStep 71341033 = 53505775) B53505775
theorem B95121377 : Blo 2197435 95121377 := bstep (se 2 (by rfl) ⟨35670516, by rfl⟩ : syracuseStep 95121377 = 71341033) B71341033
theorem B63414251 : Blo 2197435 63414251 := bstep (se 1 (by rfl) ⟨47560688, by rfl⟩ : syracuseStep 63414251 = 95121377) B95121377
theorem B42276167 : Blo 2197435 42276167 := bstep (se 1 (by rfl) ⟨31707125, by rfl⟩ : syracuseStep 42276167 = 63414251) B63414251
theorem B28184111 : Blo 2197435 28184111 := bstep (se 1 (by rfl) ⟨21138083, by rfl⟩ : syracuseStep 28184111 = 42276167) B42276167
theorem B18789407 : Blo 2197435 18789407 := bstep (se 1 (by rfl) ⟨14092055, by rfl⟩ : syracuseStep 18789407 = 28184111) B28184111
theorem B12526271 : Blo 2197435 12526271 := bstep (se 1 (by rfl) ⟨9394703, by rfl⟩ : syracuseStep 12526271 = 18789407) B18789407
theorem B8350847 : Blo 2197435 8350847 := bstep (se 1 (by rfl) ⟨6263135, by rfl⟩ : syracuseStep 8350847 = 12526271) B12526271
theorem B5567231 : Blo 2197435 5567231 := bstep (se 1 (by rfl) ⟨4175423, by rfl⟩ : syracuseStep 5567231 = 8350847) B8350847
theorem B3711487 : Blo 2197435 3711487 := bstep (se 1 (by rfl) ⟨2783615, by rfl⟩ : syracuseStep 3711487 = 5567231) B5567231
theorem B4948649 : Blo 2197435 4948649 := bstep (se 2 (by rfl) ⟨1855743, by rfl⟩ : syracuseStep 4948649 = 3711487) B3711487
theorem B3299099 : Blo 2197435 3299099 := bstep (se 1 (by rfl) ⟨2474324, by rfl⟩ : syracuseStep 3299099 = 4948649) B4948649
theorem B2199399 : Blo 2197435 2199399 := bstep (se 1 (by rfl) ⟨1649549, by rfl⟩ : syracuseStep 2199399 = 3299099) B3299099
theorem B2474329 : Blo 2197435 2474329 := bbase (se 2 (by rfl) ⟨927873, by rfl⟩ : syracuseStep 2474329 = 1855747) (by norm_num)
theorem B3299105 : Blo 2197435 3299105 := bstep (se 2 (by rfl) ⟨1237164, by rfl⟩ : syracuseStep 3299105 = 2474329) B2474329
theorem B2199403 : Blo 2197435 2199403 := bstep (se 1 (by rfl) ⟨1649552, by rfl⟩ : syracuseStep 2199403 = 3299105) B3299105
theorem B5284541 : Blo 2197435 5284541 := bbase (se 3 (by rfl) ⟨990851, by rfl⟩ : syracuseStep 5284541 = 1981703) (by norm_num)
theorem B3523027 : Blo 2197435 3523027 := bstep (se 1 (by rfl) ⟨2642270, by rfl⟩ : syracuseStep 3523027 = 5284541) B5284541
theorem B4697369 : Blo 2197435 4697369 := bstep (se 2 (by rfl) ⟨1761513, by rfl⟩ : syracuseStep 4697369 = 3523027) B3523027
theorem B3131579 : Blo 2197435 3131579 := bstep (se 1 (by rfl) ⟨2348684, by rfl⟩ : syracuseStep 3131579 = 4697369) B4697369
theorem B8350877 : Blo 2197435 8350877 := bstep (se 3 (by rfl) ⟨1565789, by rfl⟩ : syracuseStep 8350877 = 3131579) B3131579
theorem B5567251 : Blo 2197435 5567251 := bstep (se 1 (by rfl) ⟨4175438, by rfl⟩ : syracuseStep 5567251 = 8350877) B8350877
theorem B7423001 : Blo 2197435 7423001 := bstep (se 2 (by rfl) ⟨2783625, by rfl⟩ : syracuseStep 7423001 = 5567251) B5567251
theorem B4948667 : Blo 2197435 4948667 := bstep (se 1 (by rfl) ⟨3711500, by rfl⟩ : syracuseStep 4948667 = 7423001) B7423001
theorem B3299111 : Blo 2197435 3299111 := bstep (se 1 (by rfl) ⟨2474333, by rfl⟩ : syracuseStep 3299111 = 4948667) B4948667
theorem B2199407 : Blo 2197435 2199407 := bstep (se 1 (by rfl) ⟨1649555, by rfl⟩ : syracuseStep 2199407 = 3299111) B3299111
theorem B3299117 : Blo 2197435 3299117 := bbase (se 3 (by rfl) ⟨618584, by rfl⟩ : syracuseStep 3299117 = 1237169) (by norm_num)
theorem B2199411 : Blo 2197435 2199411 := bstep (se 1 (by rfl) ⟨1649558, by rfl⟩ : syracuseStep 2199411 = 3299117) B3299117
theorem B4948685 : Blo 2197435 4948685 := bbase (se 3 (by rfl) ⟨927878, by rfl⟩ : syracuseStep 4948685 = 1855757) (by norm_num)
theorem B3299123 : Blo 2197435 3299123 := bstep (se 1 (by rfl) ⟨2474342, by rfl⟩ : syracuseStep 3299123 = 4948685) B4948685
theorem B2199415 : Blo 2197435 2199415 := bstep (se 1 (by rfl) ⟨1649561, by rfl⟩ : syracuseStep 2199415 = 3299123) B3299123
theorem B2783641 : Blo 2197435 2783641 := bbase (se 2 (by rfl) ⟨1043865, by rfl⟩ : syracuseStep 2783641 = 2087731) (by norm_num)
theorem B3711521 : Blo 2197435 3711521 := bstep (se 2 (by rfl) ⟨1391820, by rfl⟩ : syracuseStep 3711521 = 2783641) B2783641
theorem B2474347 : Blo 2197435 2474347 := bstep (se 1 (by rfl) ⟨1855760, by rfl⟩ : syracuseStep 2474347 = 3711521) B3711521
theorem B3299129 : Blo 2197435 3299129 := bstep (se 2 (by rfl) ⟨1237173, by rfl⟩ : syracuseStep 3299129 = 2474347) B2474347
theorem B2199419 : Blo 2197435 2199419 := bstep (se 1 (by rfl) ⟨1649564, by rfl⟩ : syracuseStep 2199419 = 3299129) B3299129
theorem B9394805 : Blo 2197435 9394805 := bbase (se 5 (by rfl) ⟨440381, by rfl⟩ : syracuseStep 9394805 = 880763) (by norm_num)
theorem B25052813 : Blo 2197435 25052813 := bstep (se 3 (by rfl) ⟨4697402, by rfl⟩ : syracuseStep 25052813 = 9394805) B9394805
theorem B16701875 : Blo 2197435 16701875 := bstep (se 1 (by rfl) ⟨12526406, by rfl⟩ : syracuseStep 16701875 = 25052813) B25052813
theorem B11134583 : Blo 2197435 11134583 := bstep (se 1 (by rfl) ⟨8350937, by rfl⟩ : syracuseStep 11134583 = 16701875) B16701875
theorem B7423055 : Blo 2197435 7423055 := bstep (se 1 (by rfl) ⟨5567291, by rfl⟩ : syracuseStep 7423055 = 11134583) B11134583
theorem B4948703 : Blo 2197435 4948703 := bstep (se 1 (by rfl) ⟨3711527, by rfl⟩ : syracuseStep 4948703 = 7423055) B7423055
theorem B3299135 : Blo 2197435 3299135 := bstep (se 1 (by rfl) ⟨2474351, by rfl⟩ : syracuseStep 3299135 = 4948703) B4948703
theorem B2199423 : Blo 2197435 2199423 := bstep (se 1 (by rfl) ⟨1649567, by rfl⟩ : syracuseStep 2199423 = 3299135) B3299135
theorem B3299141 : Blo 2197435 3299141 := bbase (se 4 (by rfl) ⟨309294, by rfl⟩ : syracuseStep 3299141 = 618589) (by norm_num)
theorem B2199427 : Blo 2197435 2199427 := bstep (se 1 (by rfl) ⟨1649570, by rfl⟩ : syracuseStep 2199427 = 3299141) B3299141
theorem B3711541 : Blo 2197435 3711541 := bbase (se 5 (by rfl) ⟨173978, by rfl⟩ : syracuseStep 3711541 = 347957) (by norm_num)
theorem B4948721 : Blo 2197435 4948721 := bstep (se 2 (by rfl) ⟨1855770, by rfl⟩ : syracuseStep 4948721 = 3711541) B3711541
theorem B3299147 : Blo 2197435 3299147 := bstep (se 1 (by rfl) ⟨2474360, by rfl⟩ : syracuseStep 3299147 = 4948721) B4948721
theorem B2199431 : Blo 2197435 2199431 := bstep (se 1 (by rfl) ⟨1649573, by rfl⟩ : syracuseStep 2199431 = 3299147) B3299147
theorem B2474365 : Blo 2197435 2474365 := bbase (se 3 (by rfl) ⟨463943, by rfl⟩ : syracuseStep 2474365 = 927887) (by norm_num)
theorem B3299153 : Blo 2197435 3299153 := bstep (se 2 (by rfl) ⟨1237182, by rfl⟩ : syracuseStep 3299153 = 2474365) B2474365
theorem B2199435 : Blo 2197435 2199435 := bstep (se 1 (by rfl) ⟨1649576, by rfl⟩ : syracuseStep 2199435 = 3299153) B3299153
theorem C0 (j : ℕ) (h1 : 549358 ≤ j) (h2 : j ≤ 549858) : Blo 2197435 (4 * j + 3) := by
  interval_cases j
  · exact B2197435
  · exact B2197439
  · exact B2197443
  · exact B2197447
  · exact B2197451
  · exact B2197455
  · exact B2197459
  · exact B2197463
  · exact B2197467
  · exact B2197471
  · exact B2197475
  · exact B2197479
  · exact B2197483
  · exact B2197487
  · exact B2197491
  · exact B2197495
  · exact B2197499
  · exact B2197503
  · exact B2197507
  · exact B2197511
  · exact B2197515
  · exact B2197519
  · exact B2197523
  · exact B2197527
  · exact B2197531
  · exact B2197535
  · exact B2197539
  · exact B2197543
  · exact B2197547
  · exact B2197551
  · exact B2197555
  · exact B2197559
  · exact B2197563
  · exact B2197567
  · exact B2197571
  · exact B2197575
  · exact B2197579
  · exact B2197583
  · exact B2197587
  · exact B2197591
  · exact B2197595
  · exact B2197599
  · exact B2197603
  · exact B2197607
  · exact B2197611
  · exact B2197615
  · exact B2197619
  · exact B2197623
  · exact B2197627
  · exact B2197631
  · exact B2197635
  · exact B2197639
  · exact B2197643
  · exact B2197647
  · exact B2197651
  · exact B2197655
  · exact B2197659
  · exact B2197663
  · exact B2197667
  · exact B2197671
  · exact B2197675
  · exact B2197679
  · exact B2197683
  · exact B2197687
  · exact B2197691
  · exact B2197695
  · exact B2197699
  · exact B2197703
  · exact B2197707
  · exact B2197711
  · exact B2197715
  · exact B2197719
  · exact B2197723
  · exact B2197727
  · exact B2197731
  · exact B2197735
  · exact B2197739
  · exact B2197743
  · exact B2197747
  · exact B2197751
  · exact B2197755
  · exact B2197759
  · exact B2197763
  · exact B2197767
  · exact B2197771
  · exact B2197775
  · exact B2197779
  · exact B2197783
  · exact B2197787
  · exact B2197791
  · exact B2197795
  · exact B2197799
  · exact B2197803
  · exact B2197807
  · exact B2197811
  · exact B2197815
  · exact B2197819
  · exact B2197823
  · exact B2197827
  · exact B2197831
  · exact B2197835
  · exact B2197839
  · exact B2197843
  · exact B2197847
  · exact B2197851
  · exact B2197855
  · exact B2197859
  · exact B2197863
  · exact B2197867
  · exact B2197871
  · exact B2197875
  · exact B2197879
  · exact B2197883
  · exact B2197887
  · exact B2197891
  · exact B2197895
  · exact B2197899
  · exact B2197903
  · exact B2197907
  · exact B2197911
  · exact B2197915
  · exact B2197919
  · exact B2197923
  · exact B2197927
  · exact B2197931
  · exact B2197935
  · exact B2197939
  · exact B2197943
  · exact B2197947
  · exact B2197951
  · exact B2197955
  · exact B2197959
  · exact B2197963
  · exact B2197967
  · exact B2197971
  · exact B2197975
  · exact B2197979
  · exact B2197983
  · exact B2197987
  · exact B2197991
  · exact B2197995
  · exact B2197999
  · exact B2198003
  · exact B2198007
  · exact B2198011
  · exact B2198015
  · exact B2198019
  · exact B2198023
  · exact B2198027
  · exact B2198031
  · exact B2198035
  · exact B2198039
  · exact B2198043
  · exact B2198047
  · exact B2198051
  · exact B2198055
  · exact B2198059
  · exact B2198063
  · exact B2198067
  · exact B2198071
  · exact B2198075
  · exact B2198079
  · exact B2198083
  · exact B2198087
  · exact B2198091
  · exact B2198095
  · exact B2198099
  · exact B2198103
  · exact B2198107
  · exact B2198111
  · exact B2198115
  · exact B2198119
  · exact B2198123
  · exact B2198127
  · exact B2198131
  · exact B2198135
  · exact B2198139
  · exact B2198143
  · exact B2198147
  · exact B2198151
  · exact B2198155
  · exact B2198159
  · exact B2198163
  · exact B2198167
  · exact B2198171
  · exact B2198175
  · exact B2198179
  · exact B2198183
  · exact B2198187
  · exact B2198191
  · exact B2198195
  · exact B2198199
  · exact B2198203
  · exact B2198207
  · exact B2198211
  · exact B2198215
  · exact B2198219
  · exact B2198223
  · exact B2198227
  · exact B2198231
  · exact B2198235
  · exact B2198239
  · exact B2198243
  · exact B2198247
  · exact B2198251
  · exact B2198255
  · exact B2198259
  · exact B2198263
  · exact B2198267
  · exact B2198271
  · exact B2198275
  · exact B2198279
  · exact B2198283
  · exact B2198287
  · exact B2198291
  · exact B2198295
  · exact B2198299
  · exact B2198303
  · exact B2198307
  · exact B2198311
  · exact B2198315
  · exact B2198319
  · exact B2198323
  · exact B2198327
  · exact B2198331
  · exact B2198335
  · exact B2198339
  · exact B2198343
  · exact B2198347
  · exact B2198351
  · exact B2198355
  · exact B2198359
  · exact B2198363
  · exact B2198367
  · exact B2198371
  · exact B2198375
  · exact B2198379
  · exact B2198383
  · exact B2198387
  · exact B2198391
  · exact B2198395
  · exact B2198399
  · exact B2198403
  · exact B2198407
  · exact B2198411
  · exact B2198415
  · exact B2198419
  · exact B2198423
  · exact B2198427
  · exact B2198431
  · exact B2198435
  · exact B2198439
  · exact B2198443
  · exact B2198447
  · exact B2198451
  · exact B2198455
  · exact B2198459
  · exact B2198463
  · exact B2198467
  · exact B2198471
  · exact B2198475
  · exact B2198479
  · exact B2198483
  · exact B2198487
  · exact B2198491
  · exact B2198495
  · exact B2198499
  · exact B2198503
  · exact B2198507
  · exact B2198511
  · exact B2198515
  · exact B2198519
  · exact B2198523
  · exact B2198527
  · exact B2198531
  · exact B2198535
  · exact B2198539
  · exact B2198543
  · exact B2198547
  · exact B2198551
  · exact B2198555
  · exact B2198559
  · exact B2198563
  · exact B2198567
  · exact B2198571
  · exact B2198575
  · exact B2198579
  · exact B2198583
  · exact B2198587
  · exact B2198591
  · exact B2198595
  · exact B2198599
  · exact B2198603
  · exact B2198607
  · exact B2198611
  · exact B2198615
  · exact B2198619
  · exact B2198623
  · exact B2198627
  · exact B2198631
  · exact B2198635
  · exact B2198639
  · exact B2198643
  · exact B2198647
  · exact B2198651
  · exact B2198655
  · exact B2198659
  · exact B2198663
  · exact B2198667
  · exact B2198671
  · exact B2198675
  · exact B2198679
  · exact B2198683
  · exact B2198687
  · exact B2198691
  · exact B2198695
  · exact B2198699
  · exact B2198703
  · exact B2198707
  · exact B2198711
  · exact B2198715
  · exact B2198719
  · exact B2198723
  · exact B2198727
  · exact B2198731
  · exact B2198735
  · exact B2198739
  · exact B2198743
  · exact B2198747
  · exact B2198751
  · exact B2198755
  · exact B2198759
  · exact B2198763
  · exact B2198767
  · exact B2198771
  · exact B2198775
  · exact B2198779
  · exact B2198783
  · exact B2198787
  · exact B2198791
  · exact B2198795
  · exact B2198799
  · exact B2198803
  · exact B2198807
  · exact B2198811
  · exact B2198815
  · exact B2198819
  · exact B2198823
  · exact B2198827
  · exact B2198831
  · exact B2198835
  · exact B2198839
  · exact B2198843
  · exact B2198847
  · exact B2198851
  · exact B2198855
  · exact B2198859
  · exact B2198863
  · exact B2198867
  · exact B2198871
  · exact B2198875
  · exact B2198879
  · exact B2198883
  · exact B2198887
  · exact B2198891
  · exact B2198895
  · exact B2198899
  · exact B2198903
  · exact B2198907
  · exact B2198911
  · exact B2198915
  · exact B2198919
  · exact B2198923
  · exact B2198927
  · exact B2198931
  · exact B2198935
  · exact B2198939
  · exact B2198943
  · exact B2198947
  · exact B2198951
  · exact B2198955
  · exact B2198959
  · exact B2198963
  · exact B2198967
  · exact B2198971
  · exact B2198975
  · exact B2198979
  · exact B2198983
  · exact B2198987
  · exact B2198991
  · exact B2198995
  · exact B2198999
  · exact B2199003
  · exact B2199007
  · exact B2199011
  · exact B2199015
  · exact B2199019
  · exact B2199023
  · exact B2199027
  · exact B2199031
  · exact B2199035
  · exact B2199039
  · exact B2199043
  · exact B2199047
  · exact B2199051
  · exact B2199055
  · exact B2199059
  · exact B2199063
  · exact B2199067
  · exact B2199071
  · exact B2199075
  · exact B2199079
  · exact B2199083
  · exact B2199087
  · exact B2199091
  · exact B2199095
  · exact B2199099
  · exact B2199103
  · exact B2199107
  · exact B2199111
  · exact B2199115
  · exact B2199119
  · exact B2199123
  · exact B2199127
  · exact B2199131
  · exact B2199135
  · exact B2199139
  · exact B2199143
  · exact B2199147
  · exact B2199151
  · exact B2199155
  · exact B2199159
  · exact B2199163
  · exact B2199167
  · exact B2199171
  · exact B2199175
  · exact B2199179
  · exact B2199183
  · exact B2199187
  · exact B2199191
  · exact B2199195
  · exact B2199199
  · exact B2199203
  · exact B2199207
  · exact B2199211
  · exact B2199215
  · exact B2199219
  · exact B2199223
  · exact B2199227
  · exact B2199231
  · exact B2199235
  · exact B2199239
  · exact B2199243
  · exact B2199247
  · exact B2199251
  · exact B2199255
  · exact B2199259
  · exact B2199263
  · exact B2199267
  · exact B2199271
  · exact B2199275
  · exact B2199279
  · exact B2199283
  · exact B2199287
  · exact B2199291
  · exact B2199295
  · exact B2199299
  · exact B2199303
  · exact B2199307
  · exact B2199311
  · exact B2199315
  · exact B2199319
  · exact B2199323
  · exact B2199327
  · exact B2199331
  · exact B2199335
  · exact B2199339
  · exact B2199343
  · exact B2199347
  · exact B2199351
  · exact B2199355
  · exact B2199359
  · exact B2199363
  · exact B2199367
  · exact B2199371
  · exact B2199375
  · exact B2199379
  · exact B2199383
  · exact B2199387
  · exact B2199391
  · exact B2199395
  · exact B2199399
  · exact B2199403
  · exact B2199407
  · exact B2199411
  · exact B2199415
  · exact B2199419
  · exact B2199423
  · exact B2199427
  · exact B2199431
  · exact B2199435
theorem solution (m : ℕ) (hlo : 2197435 ≤ m) (hhi : m ≤ 2199435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 549358 ≤ j := by omega
    have hj2 : j ≤ 549858 := by omega
    have hb : Blo 2197435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
