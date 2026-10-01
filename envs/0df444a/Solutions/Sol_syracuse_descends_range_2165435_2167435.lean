-- Prove2me | solution 1 for syracuse_descends_range_2165435_2167435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:41.835039+00:00
-- url     : https://prove2.me/submissions/3ba56060-3669-4b08-a41b-51cbb0f7d72f

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

theorem B3654173 : Blo 2165435 3654173 := bbase (se 3 (by rfl) ⟨685157, by rfl⟩ : syracuseStep 3654173 = 1370315) (by norm_num)
theorem B2436115 : Blo 2165435 2436115 := bstep (se 1 (by rfl) ⟨1827086, by rfl⟩ : syracuseStep 2436115 = 3654173) B3654173
theorem B3248153 : Blo 2165435 3248153 := bstep (se 2 (by rfl) ⟨1218057, by rfl⟩ : syracuseStep 3248153 = 2436115) B2436115
theorem B2165435 : Blo 2165435 2165435 := bstep (se 1 (by rfl) ⟨1624076, by rfl⟩ : syracuseStep 2165435 = 3248153) B3248153
theorem B11706581 : Blo 2165435 11706581 := bbase (se 7 (by rfl) ⟨137186, by rfl⟩ : syracuseStep 11706581 = 274373) (by norm_num)
theorem B7804387 : Blo 2165435 7804387 := bstep (se 1 (by rfl) ⟨5853290, by rfl⟩ : syracuseStep 7804387 = 11706581) B11706581
theorem B10405849 : Blo 2165435 10405849 := bstep (se 2 (by rfl) ⟨3902193, by rfl⟩ : syracuseStep 10405849 = 7804387) B7804387
theorem B13874465 : Blo 2165435 13874465 := bstep (se 2 (by rfl) ⟨5202924, by rfl⟩ : syracuseStep 13874465 = 10405849) B10405849
theorem B9249643 : Blo 2165435 9249643 := bstep (se 1 (by rfl) ⟨6937232, by rfl⟩ : syracuseStep 9249643 = 13874465) B13874465
theorem B12332857 : Blo 2165435 12332857 := bstep (se 2 (by rfl) ⟨4624821, by rfl⟩ : syracuseStep 12332857 = 9249643) B9249643
theorem B16443809 : Blo 2165435 16443809 := bstep (se 2 (by rfl) ⟨6166428, by rfl⟩ : syracuseStep 16443809 = 12332857) B12332857
theorem B10962539 : Blo 2165435 10962539 := bstep (se 1 (by rfl) ⟨8221904, by rfl⟩ : syracuseStep 10962539 = 16443809) B16443809
theorem B7308359 : Blo 2165435 7308359 := bstep (se 1 (by rfl) ⟨5481269, by rfl⟩ : syracuseStep 7308359 = 10962539) B10962539
theorem B4872239 : Blo 2165435 4872239 := bstep (se 1 (by rfl) ⟨3654179, by rfl⟩ : syracuseStep 4872239 = 7308359) B7308359
theorem B3248159 : Blo 2165435 3248159 := bstep (se 1 (by rfl) ⟨2436119, by rfl⟩ : syracuseStep 3248159 = 4872239) B4872239
theorem B2165439 : Blo 2165435 2165439 := bstep (se 1 (by rfl) ⟨1624079, by rfl⟩ : syracuseStep 2165439 = 3248159) B3248159
theorem B3248165 : Blo 2165435 3248165 := bbase (se 4 (by rfl) ⟨304515, by rfl⟩ : syracuseStep 3248165 = 609031) (by norm_num)
theorem B2165443 : Blo 2165435 2165443 := bstep (se 1 (by rfl) ⟨1624082, by rfl⟩ : syracuseStep 2165443 = 3248165) B3248165
theorem B2740645 : Blo 2165435 2740645 := bbase (se 4 (by rfl) ⟨256935, by rfl⟩ : syracuseStep 2740645 = 513871) (by norm_num)
theorem B3654193 : Blo 2165435 3654193 := bstep (se 2 (by rfl) ⟨1370322, by rfl⟩ : syracuseStep 3654193 = 2740645) B2740645
theorem B4872257 : Blo 2165435 4872257 := bstep (se 2 (by rfl) ⟨1827096, by rfl⟩ : syracuseStep 4872257 = 3654193) B3654193
theorem B3248171 : Blo 2165435 3248171 := bstep (se 1 (by rfl) ⟨2436128, by rfl⟩ : syracuseStep 3248171 = 4872257) B4872257
theorem B2165447 : Blo 2165435 2165447 := bstep (se 1 (by rfl) ⟨1624085, by rfl⟩ : syracuseStep 2165447 = 3248171) B3248171
theorem B2436133 : Blo 2165435 2436133 := bbase (se 4 (by rfl) ⟨228387, by rfl⟩ : syracuseStep 2436133 = 456775) (by norm_num)
theorem B3248177 : Blo 2165435 3248177 := bstep (se 2 (by rfl) ⟨1218066, by rfl⟩ : syracuseStep 3248177 = 2436133) B2436133
theorem B2165451 : Blo 2165435 2165451 := bstep (se 1 (by rfl) ⟨1624088, by rfl⟩ : syracuseStep 2165451 = 3248177) B3248177
theorem B6937285 : Blo 2165435 6937285 := bbase (se 4 (by rfl) ⟨650370, by rfl⟩ : syracuseStep 6937285 = 1300741) (by norm_num)
theorem B9249713 : Blo 2165435 9249713 := bstep (se 2 (by rfl) ⟨3468642, by rfl⟩ : syracuseStep 9249713 = 6937285) B6937285
theorem B6166475 : Blo 2165435 6166475 := bstep (se 1 (by rfl) ⟨4624856, by rfl⟩ : syracuseStep 6166475 = 9249713) B9249713
theorem B4110983 : Blo 2165435 4110983 := bstep (se 1 (by rfl) ⟨3083237, by rfl⟩ : syracuseStep 4110983 = 6166475) B6166475
theorem B2740655 : Blo 2165435 2740655 := bstep (se 1 (by rfl) ⟨2055491, by rfl⟩ : syracuseStep 2740655 = 4110983) B4110983
theorem B7308413 : Blo 2165435 7308413 := bstep (se 3 (by rfl) ⟨1370327, by rfl⟩ : syracuseStep 7308413 = 2740655) B2740655
theorem B4872275 : Blo 2165435 4872275 := bstep (se 1 (by rfl) ⟨3654206, by rfl⟩ : syracuseStep 4872275 = 7308413) B7308413
theorem B3248183 : Blo 2165435 3248183 := bstep (se 1 (by rfl) ⟨2436137, by rfl⟩ : syracuseStep 3248183 = 4872275) B4872275
theorem B2165455 : Blo 2165435 2165455 := bstep (se 1 (by rfl) ⟨1624091, by rfl⟩ : syracuseStep 2165455 = 3248183) B3248183
theorem B3248189 : Blo 2165435 3248189 := bbase (se 3 (by rfl) ⟨609035, by rfl⟩ : syracuseStep 3248189 = 1218071) (by norm_num)
theorem B2165459 : Blo 2165435 2165459 := bstep (se 1 (by rfl) ⟨1624094, by rfl⟩ : syracuseStep 2165459 = 3248189) B3248189
theorem B4872293 : Blo 2165435 4872293 := bbase (se 4 (by rfl) ⟨456777, by rfl⟩ : syracuseStep 4872293 = 913555) (by norm_num)
theorem B3248195 : Blo 2165435 3248195 := bstep (se 1 (by rfl) ⟨2436146, by rfl⟩ : syracuseStep 3248195 = 4872293) B4872293
theorem B2165463 : Blo 2165435 2165463 := bstep (se 1 (by rfl) ⟨1624097, by rfl⟩ : syracuseStep 2165463 = 3248195) B3248195
theorem B5481341 : Blo 2165435 5481341 := bbase (se 3 (by rfl) ⟨1027751, by rfl⟩ : syracuseStep 5481341 = 2055503) (by norm_num)
theorem B3654227 : Blo 2165435 3654227 := bstep (se 1 (by rfl) ⟨2740670, by rfl⟩ : syracuseStep 3654227 = 5481341) B5481341
theorem B2436151 : Blo 2165435 2436151 := bstep (se 1 (by rfl) ⟨1827113, by rfl⟩ : syracuseStep 2436151 = 3654227) B3654227
theorem B3248201 : Blo 2165435 3248201 := bstep (se 2 (by rfl) ⟨1218075, by rfl⟩ : syracuseStep 3248201 = 2436151) B2436151
theorem B2165467 : Blo 2165435 2165467 := bstep (se 1 (by rfl) ⟨1624100, by rfl⟩ : syracuseStep 2165467 = 3248201) B3248201
theorem B4111013 : Blo 2165435 4111013 := bbase (se 4 (by rfl) ⟨385407, by rfl⟩ : syracuseStep 4111013 = 770815) (by norm_num)
theorem B10962701 : Blo 2165435 10962701 := bstep (se 3 (by rfl) ⟨2055506, by rfl⟩ : syracuseStep 10962701 = 4111013) B4111013
theorem B7308467 : Blo 2165435 7308467 := bstep (se 1 (by rfl) ⟨5481350, by rfl⟩ : syracuseStep 7308467 = 10962701) B10962701
theorem B4872311 : Blo 2165435 4872311 := bstep (se 1 (by rfl) ⟨3654233, by rfl⟩ : syracuseStep 4872311 = 7308467) B7308467
theorem B3248207 : Blo 2165435 3248207 := bstep (se 1 (by rfl) ⟨2436155, by rfl⟩ : syracuseStep 3248207 = 4872311) B4872311
theorem B2165471 : Blo 2165435 2165471 := bstep (se 1 (by rfl) ⟨1624103, by rfl⟩ : syracuseStep 2165471 = 3248207) B3248207
theorem B3248213 : Blo 2165435 3248213 := bbase (se 8 (by rfl) ⟨19032, by rfl⟩ : syracuseStep 3248213 = 38065) (by norm_num)
theorem B2165475 : Blo 2165435 2165475 := bstep (se 1 (by rfl) ⟨1624106, by rfl⟩ : syracuseStep 2165475 = 3248213) B3248213
theorem B20812085 : Blo 2165435 20812085 := bbase (se 5 (by rfl) ⟨975566, by rfl⟩ : syracuseStep 20812085 = 1951133) (by norm_num)
theorem B13874723 : Blo 2165435 13874723 := bstep (se 1 (by rfl) ⟨10406042, by rfl⟩ : syracuseStep 13874723 = 20812085) B20812085
theorem B9249815 : Blo 2165435 9249815 := bstep (se 1 (by rfl) ⟨6937361, by rfl⟩ : syracuseStep 9249815 = 13874723) B13874723
theorem B6166543 : Blo 2165435 6166543 := bstep (se 1 (by rfl) ⟨4624907, by rfl⟩ : syracuseStep 6166543 = 9249815) B9249815
theorem B8222057 : Blo 2165435 8222057 := bstep (se 2 (by rfl) ⟨3083271, by rfl⟩ : syracuseStep 8222057 = 6166543) B6166543
theorem B5481371 : Blo 2165435 5481371 := bstep (se 1 (by rfl) ⟨4111028, by rfl⟩ : syracuseStep 5481371 = 8222057) B8222057
theorem B3654247 : Blo 2165435 3654247 := bstep (se 1 (by rfl) ⟨2740685, by rfl⟩ : syracuseStep 3654247 = 5481371) B5481371
theorem B4872329 : Blo 2165435 4872329 := bstep (se 2 (by rfl) ⟨1827123, by rfl⟩ : syracuseStep 4872329 = 3654247) B3654247
theorem B3248219 : Blo 2165435 3248219 := bstep (se 1 (by rfl) ⟨2436164, by rfl⟩ : syracuseStep 3248219 = 4872329) B4872329
theorem B2165479 : Blo 2165435 2165479 := bstep (se 1 (by rfl) ⟨1624109, by rfl⟩ : syracuseStep 2165479 = 3248219) B3248219
theorem B2436169 : Blo 2165435 2436169 := bbase (se 2 (by rfl) ⟨913563, by rfl⟩ : syracuseStep 2436169 = 1827127) (by norm_num)
theorem B3248225 : Blo 2165435 3248225 := bstep (se 2 (by rfl) ⟨1218084, by rfl⟩ : syracuseStep 3248225 = 2436169) B2436169
theorem B2165483 : Blo 2165435 2165483 := bstep (se 1 (by rfl) ⟨1624112, by rfl⟩ : syracuseStep 2165483 = 3248225) B3248225
theorem B13874773 : Blo 2165435 13874773 := bbase (se 8 (by rfl) ⟨81297, by rfl⟩ : syracuseStep 13874773 = 162595) (by norm_num)
theorem B18499697 : Blo 2165435 18499697 := bstep (se 2 (by rfl) ⟨6937386, by rfl⟩ : syracuseStep 18499697 = 13874773) B13874773
theorem B12333131 : Blo 2165435 12333131 := bstep (se 1 (by rfl) ⟨9249848, by rfl⟩ : syracuseStep 12333131 = 18499697) B18499697
theorem B8222087 : Blo 2165435 8222087 := bstep (se 1 (by rfl) ⟨6166565, by rfl⟩ : syracuseStep 8222087 = 12333131) B12333131
theorem B5481391 : Blo 2165435 5481391 := bstep (se 1 (by rfl) ⟨4111043, by rfl⟩ : syracuseStep 5481391 = 8222087) B8222087
theorem B7308521 : Blo 2165435 7308521 := bstep (se 2 (by rfl) ⟨2740695, by rfl⟩ : syracuseStep 7308521 = 5481391) B5481391
theorem B4872347 : Blo 2165435 4872347 := bstep (se 1 (by rfl) ⟨3654260, by rfl⟩ : syracuseStep 4872347 = 7308521) B7308521
theorem B3248231 : Blo 2165435 3248231 := bstep (se 1 (by rfl) ⟨2436173, by rfl⟩ : syracuseStep 3248231 = 4872347) B4872347
theorem B2165487 : Blo 2165435 2165487 := bstep (se 1 (by rfl) ⟨1624115, by rfl⟩ : syracuseStep 2165487 = 3248231) B3248231
theorem B3248237 : Blo 2165435 3248237 := bbase (se 3 (by rfl) ⟨609044, by rfl⟩ : syracuseStep 3248237 = 1218089) (by norm_num)
theorem B2165491 : Blo 2165435 2165491 := bstep (se 1 (by rfl) ⟨1624118, by rfl⟩ : syracuseStep 2165491 = 3248237) B3248237
theorem B4872365 : Blo 2165435 4872365 := bbase (se 3 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 4872365 = 1827137) (by norm_num)
theorem B3248243 : Blo 2165435 3248243 := bstep (se 1 (by rfl) ⟨2436182, by rfl⟩ : syracuseStep 3248243 = 4872365) B4872365
theorem B2165495 : Blo 2165435 2165495 := bstep (se 1 (by rfl) ⟨1624121, by rfl⟩ : syracuseStep 2165495 = 3248243) B3248243
theorem B19755413 : Blo 2165435 19755413 := bbase (se 6 (by rfl) ⟨463017, by rfl⟩ : syracuseStep 19755413 = 926035) (by norm_num)
theorem B13170275 : Blo 2165435 13170275 := bstep (se 1 (by rfl) ⟨9877706, by rfl⟩ : syracuseStep 13170275 = 19755413) B19755413
theorem B8780183 : Blo 2165435 8780183 := bstep (se 1 (by rfl) ⟨6585137, by rfl⟩ : syracuseStep 8780183 = 13170275) B13170275
theorem B5853455 : Blo 2165435 5853455 := bstep (se 1 (by rfl) ⟨4390091, by rfl⟩ : syracuseStep 5853455 = 8780183) B8780183
theorem B3902303 : Blo 2165435 3902303 := bstep (se 1 (by rfl) ⟨2926727, by rfl⟩ : syracuseStep 3902303 = 5853455) B5853455
theorem B10406141 : Blo 2165435 10406141 := bstep (se 3 (by rfl) ⟨1951151, by rfl⟩ : syracuseStep 10406141 = 3902303) B3902303
theorem B6937427 : Blo 2165435 6937427 := bstep (se 1 (by rfl) ⟨5203070, by rfl⟩ : syracuseStep 6937427 = 10406141) B10406141
theorem B4624951 : Blo 2165435 4624951 := bstep (se 1 (by rfl) ⟨3468713, by rfl⟩ : syracuseStep 4624951 = 6937427) B6937427
theorem B6166601 : Blo 2165435 6166601 := bstep (se 2 (by rfl) ⟨2312475, by rfl⟩ : syracuseStep 6166601 = 4624951) B4624951
theorem B4111067 : Blo 2165435 4111067 := bstep (se 1 (by rfl) ⟨3083300, by rfl⟩ : syracuseStep 4111067 = 6166601) B6166601
theorem B2740711 : Blo 2165435 2740711 := bstep (se 1 (by rfl) ⟨2055533, by rfl⟩ : syracuseStep 2740711 = 4111067) B4111067
theorem B3654281 : Blo 2165435 3654281 := bstep (se 2 (by rfl) ⟨1370355, by rfl⟩ : syracuseStep 3654281 = 2740711) B2740711
theorem B2436187 : Blo 2165435 2436187 := bstep (se 1 (by rfl) ⟨1827140, by rfl⟩ : syracuseStep 2436187 = 3654281) B3654281
theorem B3248249 : Blo 2165435 3248249 := bstep (se 2 (by rfl) ⟨1218093, by rfl⟩ : syracuseStep 3248249 = 2436187) B2436187
theorem B2165499 : Blo 2165435 2165499 := bstep (se 1 (by rfl) ⟨1624124, by rfl⟩ : syracuseStep 2165499 = 3248249) B3248249
theorem B3902309 : Blo 2165435 3902309 := bbase (se 4 (by rfl) ⟨365841, by rfl⟩ : syracuseStep 3902309 = 731683) (by norm_num)
theorem B2601539 : Blo 2165435 2601539 := bstep (se 1 (by rfl) ⟨1951154, by rfl⟩ : syracuseStep 2601539 = 3902309) B3902309
theorem B27749749 : Blo 2165435 27749749 := bstep (se 5 (by rfl) ⟨1300769, by rfl⟩ : syracuseStep 27749749 = 2601539) B2601539
theorem B36999665 : Blo 2165435 36999665 := bstep (se 2 (by rfl) ⟨13874874, by rfl⟩ : syracuseStep 36999665 = 27749749) B27749749
theorem B24666443 : Blo 2165435 24666443 := bstep (se 1 (by rfl) ⟨18499832, by rfl⟩ : syracuseStep 24666443 = 36999665) B36999665
theorem B16444295 : Blo 2165435 16444295 := bstep (se 1 (by rfl) ⟨12333221, by rfl⟩ : syracuseStep 16444295 = 24666443) B24666443
theorem B10962863 : Blo 2165435 10962863 := bstep (se 1 (by rfl) ⟨8222147, by rfl⟩ : syracuseStep 10962863 = 16444295) B16444295
theorem B7308575 : Blo 2165435 7308575 := bstep (se 1 (by rfl) ⟨5481431, by rfl⟩ : syracuseStep 7308575 = 10962863) B10962863
theorem B4872383 : Blo 2165435 4872383 := bstep (se 1 (by rfl) ⟨3654287, by rfl⟩ : syracuseStep 4872383 = 7308575) B7308575
theorem B3248255 : Blo 2165435 3248255 := bstep (se 1 (by rfl) ⟨2436191, by rfl⟩ : syracuseStep 3248255 = 4872383) B4872383
theorem B2165503 : Blo 2165435 2165503 := bstep (se 1 (by rfl) ⟨1624127, by rfl⟩ : syracuseStep 2165503 = 3248255) B3248255
theorem B3248261 : Blo 2165435 3248261 := bbase (se 4 (by rfl) ⟨304524, by rfl⟩ : syracuseStep 3248261 = 609049) (by norm_num)
theorem B2165507 : Blo 2165435 2165507 := bstep (se 1 (by rfl) ⟨1624130, by rfl⟩ : syracuseStep 2165507 = 3248261) B3248261
theorem B3654301 : Blo 2165435 3654301 := bbase (se 3 (by rfl) ⟨685181, by rfl⟩ : syracuseStep 3654301 = 1370363) (by norm_num)
theorem B4872401 : Blo 2165435 4872401 := bstep (se 2 (by rfl) ⟨1827150, by rfl⟩ : syracuseStep 4872401 = 3654301) B3654301
theorem B3248267 : Blo 2165435 3248267 := bstep (se 1 (by rfl) ⟨2436200, by rfl⟩ : syracuseStep 3248267 = 4872401) B4872401
theorem B2165511 : Blo 2165435 2165511 := bstep (se 1 (by rfl) ⟨1624133, by rfl⟩ : syracuseStep 2165511 = 3248267) B3248267
theorem B2436205 : Blo 2165435 2436205 := bbase (se 3 (by rfl) ⟨456788, by rfl⟩ : syracuseStep 2436205 = 913577) (by norm_num)
theorem B3248273 : Blo 2165435 3248273 := bstep (se 2 (by rfl) ⟨1218102, by rfl⟩ : syracuseStep 3248273 = 2436205) B2436205
theorem B2165515 : Blo 2165435 2165515 := bstep (se 1 (by rfl) ⟨1624136, by rfl⟩ : syracuseStep 2165515 = 3248273) B3248273
theorem B7308629 : Blo 2165435 7308629 := bbase (se 12 (by rfl) ⟨2676, by rfl⟩ : syracuseStep 7308629 = 5353) (by norm_num)
theorem B4872419 : Blo 2165435 4872419 := bstep (se 1 (by rfl) ⟨3654314, by rfl⟩ : syracuseStep 4872419 = 7308629) B7308629
theorem B3248279 : Blo 2165435 3248279 := bstep (se 1 (by rfl) ⟨2436209, by rfl⟩ : syracuseStep 3248279 = 4872419) B4872419
theorem B2165519 : Blo 2165435 2165519 := bstep (se 1 (by rfl) ⟨1624139, by rfl⟩ : syracuseStep 2165519 = 3248279) B3248279
theorem B3248285 : Blo 2165435 3248285 := bbase (se 3 (by rfl) ⟨609053, by rfl⟩ : syracuseStep 3248285 = 1218107) (by norm_num)
theorem B2165523 : Blo 2165435 2165523 := bstep (se 1 (by rfl) ⟨1624142, by rfl⟩ : syracuseStep 2165523 = 3248285) B3248285
theorem B4872437 : Blo 2165435 4872437 := bbase (se 5 (by rfl) ⟨228395, by rfl⟩ : syracuseStep 4872437 = 456791) (by norm_num)
theorem B3248291 : Blo 2165435 3248291 := bstep (se 1 (by rfl) ⟨2436218, by rfl⟩ : syracuseStep 3248291 = 4872437) B4872437
theorem B2165527 : Blo 2165435 2165527 := bstep (se 1 (by rfl) ⟨1624145, by rfl⟩ : syracuseStep 2165527 = 3248291) B3248291
theorem B2778145 : Blo 2165435 2778145 := bbase (se 2 (by rfl) ⟨1041804, by rfl⟩ : syracuseStep 2778145 = 2083609) (by norm_num)
theorem B14816773 : Blo 2165435 14816773 := bstep (se 4 (by rfl) ⟨1389072, by rfl⟩ : syracuseStep 14816773 = 2778145) B2778145
theorem B79022789 : Blo 2165435 79022789 := bstep (se 4 (by rfl) ⟨7408386, by rfl⟩ : syracuseStep 79022789 = 14816773) B14816773
theorem B52681859 : Blo 2165435 52681859 := bstep (se 1 (by rfl) ⟨39511394, by rfl⟩ : syracuseStep 52681859 = 79022789) B79022789
theorem B35121239 : Blo 2165435 35121239 := bstep (se 1 (by rfl) ⟨26340929, by rfl⟩ : syracuseStep 35121239 = 52681859) B52681859
theorem B23414159 : Blo 2165435 23414159 := bstep (se 1 (by rfl) ⟨17560619, by rfl⟩ : syracuseStep 23414159 = 35121239) B35121239
theorem B15609439 : Blo 2165435 15609439 := bstep (se 1 (by rfl) ⟨11707079, by rfl⟩ : syracuseStep 15609439 = 23414159) B23414159
theorem B20812585 : Blo 2165435 20812585 := bstep (se 2 (by rfl) ⟨7804719, by rfl⟩ : syracuseStep 20812585 = 15609439) B15609439
theorem B27750113 : Blo 2165435 27750113 := bstep (se 2 (by rfl) ⟨10406292, by rfl⟩ : syracuseStep 27750113 = 20812585) B20812585
theorem B18500075 : Blo 2165435 18500075 := bstep (se 1 (by rfl) ⟨13875056, by rfl⟩ : syracuseStep 18500075 = 27750113) B27750113
theorem B12333383 : Blo 2165435 12333383 := bstep (se 1 (by rfl) ⟨9250037, by rfl⟩ : syracuseStep 12333383 = 18500075) B18500075
theorem B8222255 : Blo 2165435 8222255 := bstep (se 1 (by rfl) ⟨6166691, by rfl⟩ : syracuseStep 8222255 = 12333383) B12333383
theorem B5481503 : Blo 2165435 5481503 := bstep (se 1 (by rfl) ⟨4111127, by rfl⟩ : syracuseStep 5481503 = 8222255) B8222255
theorem B3654335 : Blo 2165435 3654335 := bstep (se 1 (by rfl) ⟨2740751, by rfl⟩ : syracuseStep 3654335 = 5481503) B5481503
theorem B2436223 : Blo 2165435 2436223 := bstep (se 1 (by rfl) ⟨1827167, by rfl⟩ : syracuseStep 2436223 = 3654335) B3654335
theorem B3248297 : Blo 2165435 3248297 := bstep (se 2 (by rfl) ⟨1218111, by rfl⟩ : syracuseStep 3248297 = 2436223) B2436223
theorem B2165531 : Blo 2165435 2165531 := bstep (se 1 (by rfl) ⟨1624148, by rfl⟩ : syracuseStep 2165531 = 3248297) B3248297
theorem B6937541 : Blo 2165435 6937541 := bbase (se 4 (by rfl) ⟨650394, by rfl⟩ : syracuseStep 6937541 = 1300789) (by norm_num)
theorem B4625027 : Blo 2165435 4625027 := bstep (se 1 (by rfl) ⟨3468770, by rfl⟩ : syracuseStep 4625027 = 6937541) B6937541
theorem B3083351 : Blo 2165435 3083351 := bstep (se 1 (by rfl) ⟨2312513, by rfl⟩ : syracuseStep 3083351 = 4625027) B4625027
theorem B8222269 : Blo 2165435 8222269 := bstep (se 3 (by rfl) ⟨1541675, by rfl⟩ : syracuseStep 8222269 = 3083351) B3083351
theorem B10963025 : Blo 2165435 10963025 := bstep (se 2 (by rfl) ⟨4111134, by rfl⟩ : syracuseStep 10963025 = 8222269) B8222269
theorem B7308683 : Blo 2165435 7308683 := bstep (se 1 (by rfl) ⟨5481512, by rfl⟩ : syracuseStep 7308683 = 10963025) B10963025
theorem B4872455 : Blo 2165435 4872455 := bstep (se 1 (by rfl) ⟨3654341, by rfl⟩ : syracuseStep 4872455 = 7308683) B7308683
theorem B3248303 : Blo 2165435 3248303 := bstep (se 1 (by rfl) ⟨2436227, by rfl⟩ : syracuseStep 3248303 = 4872455) B4872455
theorem B2165535 : Blo 2165435 2165535 := bstep (se 1 (by rfl) ⟨1624151, by rfl⟩ : syracuseStep 2165535 = 3248303) B3248303
theorem B3248309 : Blo 2165435 3248309 := bbase (se 5 (by rfl) ⟨152264, by rfl⟩ : syracuseStep 3248309 = 304529) (by norm_num)
theorem B2165539 : Blo 2165435 2165539 := bstep (se 1 (by rfl) ⟨1624154, by rfl⟩ : syracuseStep 2165539 = 3248309) B3248309
theorem B5481533 : Blo 2165435 5481533 := bbase (se 3 (by rfl) ⟨1027787, by rfl⟩ : syracuseStep 5481533 = 2055575) (by norm_num)
theorem B3654355 : Blo 2165435 3654355 := bstep (se 1 (by rfl) ⟨2740766, by rfl⟩ : syracuseStep 3654355 = 5481533) B5481533
theorem B4872473 : Blo 2165435 4872473 := bstep (se 2 (by rfl) ⟨1827177, by rfl⟩ : syracuseStep 4872473 = 3654355) B3654355
theorem B3248315 : Blo 2165435 3248315 := bstep (se 1 (by rfl) ⟨2436236, by rfl⟩ : syracuseStep 3248315 = 4872473) B4872473
theorem B2165543 : Blo 2165435 2165543 := bstep (se 1 (by rfl) ⟨1624157, by rfl⟩ : syracuseStep 2165543 = 3248315) B3248315
theorem B2436241 : Blo 2165435 2436241 := bbase (se 2 (by rfl) ⟨913590, by rfl⟩ : syracuseStep 2436241 = 1827181) (by norm_num)
theorem B3248321 : Blo 2165435 3248321 := bstep (se 2 (by rfl) ⟨1218120, by rfl⟩ : syracuseStep 3248321 = 2436241) B2436241
theorem B2165547 : Blo 2165435 2165547 := bstep (se 1 (by rfl) ⟨1624160, by rfl⟩ : syracuseStep 2165547 = 3248321) B3248321
theorem B4111165 : Blo 2165435 4111165 := bbase (se 3 (by rfl) ⟨770843, by rfl⟩ : syracuseStep 4111165 = 1541687) (by norm_num)
theorem B5481553 : Blo 2165435 5481553 := bstep (se 2 (by rfl) ⟨2055582, by rfl⟩ : syracuseStep 5481553 = 4111165) B4111165
theorem B7308737 : Blo 2165435 7308737 := bstep (se 2 (by rfl) ⟨2740776, by rfl⟩ : syracuseStep 7308737 = 5481553) B5481553
theorem B4872491 : Blo 2165435 4872491 := bstep (se 1 (by rfl) ⟨3654368, by rfl⟩ : syracuseStep 4872491 = 7308737) B7308737
theorem B3248327 : Blo 2165435 3248327 := bstep (se 1 (by rfl) ⟨2436245, by rfl⟩ : syracuseStep 3248327 = 4872491) B4872491
theorem B2165551 : Blo 2165435 2165551 := bstep (se 1 (by rfl) ⟨1624163, by rfl⟩ : syracuseStep 2165551 = 3248327) B3248327
theorem B3248333 : Blo 2165435 3248333 := bbase (se 3 (by rfl) ⟨609062, by rfl⟩ : syracuseStep 3248333 = 1218125) (by norm_num)
theorem B2165555 : Blo 2165435 2165555 := bstep (se 1 (by rfl) ⟨1624166, by rfl⟩ : syracuseStep 2165555 = 3248333) B3248333
theorem B4872509 : Blo 2165435 4872509 := bbase (se 3 (by rfl) ⟨913595, by rfl⟩ : syracuseStep 4872509 = 1827191) (by norm_num)
theorem B3248339 : Blo 2165435 3248339 := bstep (se 1 (by rfl) ⟨2436254, by rfl⟩ : syracuseStep 3248339 = 4872509) B4872509
theorem B2165559 : Blo 2165435 2165559 := bstep (se 1 (by rfl) ⟨1624169, by rfl⟩ : syracuseStep 2165559 = 3248339) B3248339
theorem B3654389 : Blo 2165435 3654389 := bbase (se 5 (by rfl) ⟨171299, by rfl⟩ : syracuseStep 3654389 = 342599) (by norm_num)
theorem B2436259 : Blo 2165435 2436259 := bstep (se 1 (by rfl) ⟨1827194, by rfl⟩ : syracuseStep 2436259 = 3654389) B3654389
theorem B3248345 : Blo 2165435 3248345 := bstep (se 2 (by rfl) ⟨1218129, by rfl⟩ : syracuseStep 3248345 = 2436259) B2436259
theorem B2165563 : Blo 2165435 2165563 := bstep (se 1 (by rfl) ⟨1624172, by rfl⟩ : syracuseStep 2165563 = 3248345) B3248345
theorem B5853637 : Blo 2165435 5853637 := bbase (se 4 (by rfl) ⟨548778, by rfl⟩ : syracuseStep 5853637 = 1097557) (by norm_num)
theorem B7804849 : Blo 2165435 7804849 := bstep (se 2 (by rfl) ⟨2926818, by rfl⟩ : syracuseStep 7804849 = 5853637) B5853637
theorem B10406465 : Blo 2165435 10406465 := bstep (se 2 (by rfl) ⟨3902424, by rfl⟩ : syracuseStep 10406465 = 7804849) B7804849
theorem B6937643 : Blo 2165435 6937643 := bstep (se 1 (by rfl) ⟨5203232, by rfl⟩ : syracuseStep 6937643 = 10406465) B10406465
theorem B4625095 : Blo 2165435 4625095 := bstep (se 1 (by rfl) ⟨3468821, by rfl⟩ : syracuseStep 4625095 = 6937643) B6937643
theorem B6166793 : Blo 2165435 6166793 := bstep (se 2 (by rfl) ⟨2312547, by rfl⟩ : syracuseStep 6166793 = 4625095) B4625095
theorem B16444781 : Blo 2165435 16444781 := bstep (se 3 (by rfl) ⟨3083396, by rfl⟩ : syracuseStep 16444781 = 6166793) B6166793
theorem B10963187 : Blo 2165435 10963187 := bstep (se 1 (by rfl) ⟨8222390, by rfl⟩ : syracuseStep 10963187 = 16444781) B16444781
theorem B7308791 : Blo 2165435 7308791 := bstep (se 1 (by rfl) ⟨5481593, by rfl⟩ : syracuseStep 7308791 = 10963187) B10963187
theorem B4872527 : Blo 2165435 4872527 := bstep (se 1 (by rfl) ⟨3654395, by rfl⟩ : syracuseStep 4872527 = 7308791) B7308791
theorem B3248351 : Blo 2165435 3248351 := bstep (se 1 (by rfl) ⟨2436263, by rfl⟩ : syracuseStep 3248351 = 4872527) B4872527
theorem B2165567 : Blo 2165435 2165567 := bstep (se 1 (by rfl) ⟨1624175, by rfl⟩ : syracuseStep 2165567 = 3248351) B3248351
theorem B3248357 : Blo 2165435 3248357 := bbase (se 4 (by rfl) ⟨304533, by rfl⟩ : syracuseStep 3248357 = 609067) (by norm_num)
theorem B2165571 : Blo 2165435 2165571 := bstep (se 1 (by rfl) ⟨1624178, by rfl⟩ : syracuseStep 2165571 = 3248357) B3248357
theorem B5203253 : Blo 2165435 5203253 := bbase (se 5 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 5203253 = 487805) (by norm_num)
theorem B3468835 : Blo 2165435 3468835 := bstep (se 1 (by rfl) ⟨2601626, by rfl⟩ : syracuseStep 3468835 = 5203253) B5203253
theorem B4625113 : Blo 2165435 4625113 := bstep (se 2 (by rfl) ⟨1734417, by rfl⟩ : syracuseStep 4625113 = 3468835) B3468835
theorem B6166817 : Blo 2165435 6166817 := bstep (se 2 (by rfl) ⟨2312556, by rfl⟩ : syracuseStep 6166817 = 4625113) B4625113
theorem B4111211 : Blo 2165435 4111211 := bstep (se 1 (by rfl) ⟨3083408, by rfl⟩ : syracuseStep 4111211 = 6166817) B6166817
theorem B2740807 : Blo 2165435 2740807 := bstep (se 1 (by rfl) ⟨2055605, by rfl⟩ : syracuseStep 2740807 = 4111211) B4111211
theorem B3654409 : Blo 2165435 3654409 := bstep (se 2 (by rfl) ⟨1370403, by rfl⟩ : syracuseStep 3654409 = 2740807) B2740807
theorem B4872545 : Blo 2165435 4872545 := bstep (se 2 (by rfl) ⟨1827204, by rfl⟩ : syracuseStep 4872545 = 3654409) B3654409
theorem B3248363 : Blo 2165435 3248363 := bstep (se 1 (by rfl) ⟨2436272, by rfl⟩ : syracuseStep 3248363 = 4872545) B4872545
theorem B2165575 : Blo 2165435 2165575 := bstep (se 1 (by rfl) ⟨1624181, by rfl⟩ : syracuseStep 2165575 = 3248363) B3248363
theorem B2436277 : Blo 2165435 2436277 := bbase (se 5 (by rfl) ⟨114200, by rfl⟩ : syracuseStep 2436277 = 228401) (by norm_num)
theorem B3248369 : Blo 2165435 3248369 := bstep (se 2 (by rfl) ⟨1218138, by rfl⟩ : syracuseStep 3248369 = 2436277) B2436277
theorem B2165579 : Blo 2165435 2165579 := bstep (se 1 (by rfl) ⟨1624184, by rfl⟩ : syracuseStep 2165579 = 3248369) B3248369
theorem B2740817 : Blo 2165435 2740817 := bbase (se 2 (by rfl) ⟨1027806, by rfl⟩ : syracuseStep 2740817 = 2055613) (by norm_num)
theorem B7308845 : Blo 2165435 7308845 := bstep (se 3 (by rfl) ⟨1370408, by rfl⟩ : syracuseStep 7308845 = 2740817) B2740817
theorem B4872563 : Blo 2165435 4872563 := bstep (se 1 (by rfl) ⟨3654422, by rfl⟩ : syracuseStep 4872563 = 7308845) B7308845
theorem B3248375 : Blo 2165435 3248375 := bstep (se 1 (by rfl) ⟨2436281, by rfl⟩ : syracuseStep 3248375 = 4872563) B4872563
theorem B2165583 : Blo 2165435 2165583 := bstep (se 1 (by rfl) ⟨1624187, by rfl⟩ : syracuseStep 2165583 = 3248375) B3248375
theorem B3248381 : Blo 2165435 3248381 := bbase (se 3 (by rfl) ⟨609071, by rfl⟩ : syracuseStep 3248381 = 1218143) (by norm_num)
theorem B2165587 : Blo 2165435 2165587 := bstep (se 1 (by rfl) ⟨1624190, by rfl⟩ : syracuseStep 2165587 = 3248381) B3248381
theorem B4872581 : Blo 2165435 4872581 := bbase (se 4 (by rfl) ⟨456804, by rfl⟩ : syracuseStep 4872581 = 913609) (by norm_num)
theorem B3248387 : Blo 2165435 3248387 := bstep (se 1 (by rfl) ⟨2436290, by rfl⟩ : syracuseStep 3248387 = 4872581) B4872581
theorem B2165591 : Blo 2165435 2165591 := bstep (se 1 (by rfl) ⟨1624193, by rfl⟩ : syracuseStep 2165591 = 3248387) B3248387
theorem B3083437 : Blo 2165435 3083437 := bbase (se 3 (by rfl) ⟨578144, by rfl⟩ : syracuseStep 3083437 = 1156289) (by norm_num)
theorem B4111249 : Blo 2165435 4111249 := bstep (se 2 (by rfl) ⟨1541718, by rfl⟩ : syracuseStep 4111249 = 3083437) B3083437
theorem B5481665 : Blo 2165435 5481665 := bstep (se 2 (by rfl) ⟨2055624, by rfl⟩ : syracuseStep 5481665 = 4111249) B4111249
theorem B3654443 : Blo 2165435 3654443 := bstep (se 1 (by rfl) ⟨2740832, by rfl⟩ : syracuseStep 3654443 = 5481665) B5481665
theorem B2436295 : Blo 2165435 2436295 := bstep (se 1 (by rfl) ⟨1827221, by rfl⟩ : syracuseStep 2436295 = 3654443) B3654443
theorem B3248393 : Blo 2165435 3248393 := bstep (se 2 (by rfl) ⟨1218147, by rfl⟩ : syracuseStep 3248393 = 2436295) B2436295
theorem B2165595 : Blo 2165435 2165595 := bstep (se 1 (by rfl) ⟨1624196, by rfl⟩ : syracuseStep 2165595 = 3248393) B3248393
theorem B10963349 : Blo 2165435 10963349 := bbase (se 6 (by rfl) ⟨256953, by rfl⟩ : syracuseStep 10963349 = 513907) (by norm_num)
theorem B7308899 : Blo 2165435 7308899 := bstep (se 1 (by rfl) ⟨5481674, by rfl⟩ : syracuseStep 7308899 = 10963349) B10963349
theorem B4872599 : Blo 2165435 4872599 := bstep (se 1 (by rfl) ⟨3654449, by rfl⟩ : syracuseStep 4872599 = 7308899) B7308899
theorem B3248399 : Blo 2165435 3248399 := bstep (se 1 (by rfl) ⟨2436299, by rfl⟩ : syracuseStep 3248399 = 4872599) B4872599
theorem B2165599 : Blo 2165435 2165599 := bstep (se 1 (by rfl) ⟨1624199, by rfl⟩ : syracuseStep 2165599 = 3248399) B3248399
theorem B3248405 : Blo 2165435 3248405 := bbase (se 6 (by rfl) ⟨76134, by rfl⟩ : syracuseStep 3248405 = 152269) (by norm_num)
theorem B2165603 : Blo 2165435 2165603 := bstep (se 1 (by rfl) ⟨1624202, by rfl⟩ : syracuseStep 2165603 = 3248405) B3248405
theorem B4390309 : Blo 2165435 4390309 := bbase (se 4 (by rfl) ⟨411591, by rfl⟩ : syracuseStep 4390309 = 823183) (by norm_num)
theorem B5853745 : Blo 2165435 5853745 := bstep (se 2 (by rfl) ⟨2195154, by rfl⟩ : syracuseStep 5853745 = 4390309) B4390309
theorem B7804993 : Blo 2165435 7804993 := bstep (se 2 (by rfl) ⟨2926872, by rfl⟩ : syracuseStep 7804993 = 5853745) B5853745
theorem B10406657 : Blo 2165435 10406657 := bstep (se 2 (by rfl) ⟨3902496, by rfl⟩ : syracuseStep 10406657 = 7804993) B7804993
theorem B27751085 : Blo 2165435 27751085 := bstep (se 3 (by rfl) ⟨5203328, by rfl⟩ : syracuseStep 27751085 = 10406657) B10406657
theorem B18500723 : Blo 2165435 18500723 := bstep (se 1 (by rfl) ⟨13875542, by rfl⟩ : syracuseStep 18500723 = 27751085) B27751085
theorem B12333815 : Blo 2165435 12333815 := bstep (se 1 (by rfl) ⟨9250361, by rfl⟩ : syracuseStep 12333815 = 18500723) B18500723
theorem B8222543 : Blo 2165435 8222543 := bstep (se 1 (by rfl) ⟨6166907, by rfl⟩ : syracuseStep 8222543 = 12333815) B12333815
theorem B5481695 : Blo 2165435 5481695 := bstep (se 1 (by rfl) ⟨4111271, by rfl⟩ : syracuseStep 5481695 = 8222543) B8222543
theorem B3654463 : Blo 2165435 3654463 := bstep (se 1 (by rfl) ⟨2740847, by rfl⟩ : syracuseStep 3654463 = 5481695) B5481695
theorem B4872617 : Blo 2165435 4872617 := bstep (se 2 (by rfl) ⟨1827231, by rfl⟩ : syracuseStep 4872617 = 3654463) B3654463
theorem B3248411 : Blo 2165435 3248411 := bstep (se 1 (by rfl) ⟨2436308, by rfl⟩ : syracuseStep 3248411 = 4872617) B4872617
theorem B2165607 : Blo 2165435 2165607 := bstep (se 1 (by rfl) ⟨1624205, by rfl⟩ : syracuseStep 2165607 = 3248411) B3248411
theorem B2436313 : Blo 2165435 2436313 := bbase (se 2 (by rfl) ⟨913617, by rfl⟩ : syracuseStep 2436313 = 1827235) (by norm_num)
theorem B3248417 : Blo 2165435 3248417 := bstep (se 2 (by rfl) ⟨1218156, by rfl⟩ : syracuseStep 3248417 = 2436313) B2436313
theorem B2165611 : Blo 2165435 2165611 := bstep (se 1 (by rfl) ⟨1624208, by rfl⟩ : syracuseStep 2165611 = 3248417) B3248417
theorem B5203349 : Blo 2165435 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B3468899 : Blo 2165435 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B2312599 : Blo 2165435 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B3083465 : Blo 2165435 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B8222573 : Blo 2165435 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B5481715 : Blo 2165435 5481715 := bstep (se 1 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 5481715 = 8222573) B8222573
theorem B7308953 : Blo 2165435 7308953 := bstep (se 2 (by rfl) ⟨2740857, by rfl⟩ : syracuseStep 7308953 = 5481715) B5481715
theorem B4872635 : Blo 2165435 4872635 := bstep (se 1 (by rfl) ⟨3654476, by rfl⟩ : syracuseStep 4872635 = 7308953) B7308953
theorem B3248423 : Blo 2165435 3248423 := bstep (se 1 (by rfl) ⟨2436317, by rfl⟩ : syracuseStep 3248423 = 4872635) B4872635
theorem B2165615 : Blo 2165435 2165615 := bstep (se 1 (by rfl) ⟨1624211, by rfl⟩ : syracuseStep 2165615 = 3248423) B3248423
theorem B3248429 : Blo 2165435 3248429 := bbase (se 3 (by rfl) ⟨609080, by rfl⟩ : syracuseStep 3248429 = 1218161) (by norm_num)
theorem B2165619 : Blo 2165435 2165619 := bstep (se 1 (by rfl) ⟨1624214, by rfl⟩ : syracuseStep 2165619 = 3248429) B3248429
theorem B4872653 : Blo 2165435 4872653 := bbase (se 3 (by rfl) ⟨913622, by rfl⟩ : syracuseStep 4872653 = 1827245) (by norm_num)
theorem B3248435 : Blo 2165435 3248435 := bstep (se 1 (by rfl) ⟨2436326, by rfl⟩ : syracuseStep 3248435 = 4872653) B4872653
theorem B2165623 : Blo 2165435 2165623 := bstep (se 1 (by rfl) ⟨1624217, by rfl⟩ : syracuseStep 2165623 = 3248435) B3248435
theorem B2740873 : Blo 2165435 2740873 := bbase (se 2 (by rfl) ⟨1027827, by rfl⟩ : syracuseStep 2740873 = 2055655) (by norm_num)
theorem B3654497 : Blo 2165435 3654497 := bstep (se 2 (by rfl) ⟨1370436, by rfl⟩ : syracuseStep 3654497 = 2740873) B2740873
theorem B2436331 : Blo 2165435 2436331 := bstep (se 1 (by rfl) ⟨1827248, by rfl⟩ : syracuseStep 2436331 = 3654497) B3654497
theorem B3248441 : Blo 2165435 3248441 := bstep (se 2 (by rfl) ⟨1218165, by rfl⟩ : syracuseStep 3248441 = 2436331) B2436331
theorem B2165627 : Blo 2165435 2165627 := bstep (se 1 (by rfl) ⟨1624220, by rfl⟩ : syracuseStep 2165627 = 3248441) B3248441
theorem B47469397 : Blo 2165435 47469397 := bbase (se 9 (by rfl) ⟨139070, by rfl⟩ : syracuseStep 47469397 = 278141) (by norm_num)
theorem B63292529 : Blo 2165435 63292529 := bstep (se 2 (by rfl) ⟨23734698, by rfl⟩ : syracuseStep 63292529 = 47469397) B47469397
theorem B42195019 : Blo 2165435 42195019 := bstep (se 1 (by rfl) ⟨31646264, by rfl⟩ : syracuseStep 42195019 = 63292529) B63292529
theorem B56260025 : Blo 2165435 56260025 := bstep (se 2 (by rfl) ⟨21097509, by rfl⟩ : syracuseStep 56260025 = 42195019) B42195019
theorem B37506683 : Blo 2165435 37506683 := bstep (se 1 (by rfl) ⟨28130012, by rfl⟩ : syracuseStep 37506683 = 56260025) B56260025
theorem B100017821 : Blo 2165435 100017821 := bstep (se 3 (by rfl) ⟨18753341, by rfl⟩ : syracuseStep 100017821 = 37506683) B37506683
theorem B66678547 : Blo 2165435 66678547 := bstep (se 1 (by rfl) ⟨50008910, by rfl⟩ : syracuseStep 66678547 = 100017821) B100017821
theorem B88904729 : Blo 2165435 88904729 := bstep (se 2 (by rfl) ⟨33339273, by rfl⟩ : syracuseStep 88904729 = 66678547) B66678547
theorem B59269819 : Blo 2165435 59269819 := bstep (se 1 (by rfl) ⟨44452364, by rfl⟩ : syracuseStep 59269819 = 88904729) B88904729
theorem B79026425 : Blo 2165435 79026425 := bstep (se 2 (by rfl) ⟨29634909, by rfl⟩ : syracuseStep 79026425 = 59269819) B59269819
theorem B52684283 : Blo 2165435 52684283 := bstep (se 1 (by rfl) ⟨39513212, by rfl⟩ : syracuseStep 52684283 = 79026425) B79026425
theorem B35122855 : Blo 2165435 35122855 := bstep (se 1 (by rfl) ⟨26342141, by rfl⟩ : syracuseStep 35122855 = 52684283) B52684283
theorem B46830473 : Blo 2165435 46830473 := bstep (se 2 (by rfl) ⟨17561427, by rfl⟩ : syracuseStep 46830473 = 35122855) B35122855
theorem B31220315 : Blo 2165435 31220315 := bstep (se 1 (by rfl) ⟨23415236, by rfl⟩ : syracuseStep 31220315 = 46830473) B46830473
theorem B20813543 : Blo 2165435 20813543 := bstep (se 1 (by rfl) ⟨15610157, by rfl⟩ : syracuseStep 20813543 = 31220315) B31220315
theorem B13875695 : Blo 2165435 13875695 := bstep (se 1 (by rfl) ⟨10406771, by rfl⟩ : syracuseStep 13875695 = 20813543) B20813543
theorem B9250463 : Blo 2165435 9250463 := bstep (se 1 (by rfl) ⟨6937847, by rfl⟩ : syracuseStep 9250463 = 13875695) B13875695
theorem B24667901 : Blo 2165435 24667901 := bstep (se 3 (by rfl) ⟨4625231, by rfl⟩ : syracuseStep 24667901 = 9250463) B9250463
theorem B16445267 : Blo 2165435 16445267 := bstep (se 1 (by rfl) ⟨12333950, by rfl⟩ : syracuseStep 16445267 = 24667901) B24667901
theorem B10963511 : Blo 2165435 10963511 := bstep (se 1 (by rfl) ⟨8222633, by rfl⟩ : syracuseStep 10963511 = 16445267) B16445267
theorem B7309007 : Blo 2165435 7309007 := bstep (se 1 (by rfl) ⟨5481755, by rfl⟩ : syracuseStep 7309007 = 10963511) B10963511
theorem B4872671 : Blo 2165435 4872671 := bstep (se 1 (by rfl) ⟨3654503, by rfl⟩ : syracuseStep 4872671 = 7309007) B7309007
theorem B3248447 : Blo 2165435 3248447 := bstep (se 1 (by rfl) ⟨2436335, by rfl⟩ : syracuseStep 3248447 = 4872671) B4872671
theorem B2165631 : Blo 2165435 2165631 := bstep (se 1 (by rfl) ⟨1624223, by rfl⟩ : syracuseStep 2165631 = 3248447) B3248447
theorem B3248453 : Blo 2165435 3248453 := bbase (se 4 (by rfl) ⟨304542, by rfl⟩ : syracuseStep 3248453 = 609085) (by norm_num)
theorem B2165635 : Blo 2165435 2165635 := bstep (se 1 (by rfl) ⟨1624226, by rfl⟩ : syracuseStep 2165635 = 3248453) B3248453
theorem B3654517 : Blo 2165435 3654517 := bbase (se 5 (by rfl) ⟨171305, by rfl⟩ : syracuseStep 3654517 = 342611) (by norm_num)
theorem B4872689 : Blo 2165435 4872689 := bstep (se 2 (by rfl) ⟨1827258, by rfl⟩ : syracuseStep 4872689 = 3654517) B3654517
theorem B3248459 : Blo 2165435 3248459 := bstep (se 1 (by rfl) ⟨2436344, by rfl⟩ : syracuseStep 3248459 = 4872689) B4872689
theorem B2165639 : Blo 2165435 2165639 := bstep (se 1 (by rfl) ⟨1624229, by rfl⟩ : syracuseStep 2165639 = 3248459) B3248459
theorem B2436349 : Blo 2165435 2436349 := bbase (se 3 (by rfl) ⟨456815, by rfl⟩ : syracuseStep 2436349 = 913631) (by norm_num)
theorem B3248465 : Blo 2165435 3248465 := bstep (se 2 (by rfl) ⟨1218174, by rfl⟩ : syracuseStep 3248465 = 2436349) B2436349
theorem B2165643 : Blo 2165435 2165643 := bstep (se 1 (by rfl) ⟨1624232, by rfl⟩ : syracuseStep 2165643 = 3248465) B3248465
theorem B7309061 : Blo 2165435 7309061 := bbase (se 4 (by rfl) ⟨685224, by rfl⟩ : syracuseStep 7309061 = 1370449) (by norm_num)
theorem B4872707 : Blo 2165435 4872707 := bstep (se 1 (by rfl) ⟨3654530, by rfl⟩ : syracuseStep 4872707 = 7309061) B7309061
theorem B3248471 : Blo 2165435 3248471 := bstep (se 1 (by rfl) ⟨2436353, by rfl⟩ : syracuseStep 3248471 = 4872707) B4872707
theorem B2165647 : Blo 2165435 2165647 := bstep (se 1 (by rfl) ⟨1624235, by rfl⟩ : syracuseStep 2165647 = 3248471) B3248471
theorem B3248477 : Blo 2165435 3248477 := bbase (se 3 (by rfl) ⟨609089, by rfl⟩ : syracuseStep 3248477 = 1218179) (by norm_num)
theorem B2165651 : Blo 2165435 2165651 := bstep (se 1 (by rfl) ⟨1624238, by rfl⟩ : syracuseStep 2165651 = 3248477) B3248477
theorem B4872725 : Blo 2165435 4872725 := bbase (se 6 (by rfl) ⟨114204, by rfl⟩ : syracuseStep 4872725 = 228409) (by norm_num)
theorem B3248483 : Blo 2165435 3248483 := bstep (se 1 (by rfl) ⟨2436362, by rfl⟩ : syracuseStep 3248483 = 4872725) B4872725
theorem B2165655 : Blo 2165435 2165655 := bstep (se 1 (by rfl) ⟨1624241, by rfl⟩ : syracuseStep 2165655 = 3248483) B3248483
theorem B8222741 : Blo 2165435 8222741 := bbase (se 6 (by rfl) ⟨192720, by rfl⟩ : syracuseStep 8222741 = 385441) (by norm_num)
theorem B5481827 : Blo 2165435 5481827 := bstep (se 1 (by rfl) ⟨4111370, by rfl⟩ : syracuseStep 5481827 = 8222741) B8222741
theorem B3654551 : Blo 2165435 3654551 := bstep (se 1 (by rfl) ⟨2740913, by rfl⟩ : syracuseStep 3654551 = 5481827) B5481827
theorem B2436367 : Blo 2165435 2436367 := bstep (se 1 (by rfl) ⟨1827275, by rfl⟩ : syracuseStep 2436367 = 3654551) B3654551
theorem B3248489 : Blo 2165435 3248489 := bstep (se 2 (by rfl) ⟨1218183, by rfl⟩ : syracuseStep 3248489 = 2436367) B2436367
theorem B2165659 : Blo 2165435 2165659 := bstep (se 1 (by rfl) ⟨1624244, by rfl⟩ : syracuseStep 2165659 = 3248489) B3248489
theorem B12334133 : Blo 2165435 12334133 := bbase (se 5 (by rfl) ⟨578162, by rfl⟩ : syracuseStep 12334133 = 1156325) (by norm_num)
theorem B8222755 : Blo 2165435 8222755 := bstep (se 1 (by rfl) ⟨6167066, by rfl⟩ : syracuseStep 8222755 = 12334133) B12334133
theorem B10963673 : Blo 2165435 10963673 := bstep (se 2 (by rfl) ⟨4111377, by rfl⟩ : syracuseStep 10963673 = 8222755) B8222755
theorem B7309115 : Blo 2165435 7309115 := bstep (se 1 (by rfl) ⟨5481836, by rfl⟩ : syracuseStep 7309115 = 10963673) B10963673
theorem B4872743 : Blo 2165435 4872743 := bstep (se 1 (by rfl) ⟨3654557, by rfl⟩ : syracuseStep 4872743 = 7309115) B7309115
theorem B3248495 : Blo 2165435 3248495 := bstep (se 1 (by rfl) ⟨2436371, by rfl⟩ : syracuseStep 3248495 = 4872743) B4872743
theorem B2165663 : Blo 2165435 2165663 := bstep (se 1 (by rfl) ⟨1624247, by rfl⟩ : syracuseStep 2165663 = 3248495) B3248495
theorem B3248501 : Blo 2165435 3248501 := bbase (se 5 (by rfl) ⟨152273, by rfl⟩ : syracuseStep 3248501 = 304547) (by norm_num)
theorem B2165667 : Blo 2165435 2165667 := bstep (se 1 (by rfl) ⟨1624250, by rfl⟩ : syracuseStep 2165667 = 3248501) B3248501
theorem B3468989 : Blo 2165435 3468989 := bbase (se 3 (by rfl) ⟨650435, by rfl⟩ : syracuseStep 3468989 = 1300871) (by norm_num)
theorem B2312659 : Blo 2165435 2312659 := bstep (se 1 (by rfl) ⟨1734494, by rfl⟩ : syracuseStep 2312659 = 3468989) B3468989
theorem B3083545 : Blo 2165435 3083545 := bstep (se 2 (by rfl) ⟨1156329, by rfl⟩ : syracuseStep 3083545 = 2312659) B2312659
theorem B4111393 : Blo 2165435 4111393 := bstep (se 2 (by rfl) ⟨1541772, by rfl⟩ : syracuseStep 4111393 = 3083545) B3083545
theorem B5481857 : Blo 2165435 5481857 := bstep (se 2 (by rfl) ⟨2055696, by rfl⟩ : syracuseStep 5481857 = 4111393) B4111393
theorem B3654571 : Blo 2165435 3654571 := bstep (se 1 (by rfl) ⟨2740928, by rfl⟩ : syracuseStep 3654571 = 5481857) B5481857
theorem B4872761 : Blo 2165435 4872761 := bstep (se 2 (by rfl) ⟨1827285, by rfl⟩ : syracuseStep 4872761 = 3654571) B3654571
theorem B3248507 : Blo 2165435 3248507 := bstep (se 1 (by rfl) ⟨2436380, by rfl⟩ : syracuseStep 3248507 = 4872761) B4872761
theorem B2165671 : Blo 2165435 2165671 := bstep (se 1 (by rfl) ⟨1624253, by rfl⟩ : syracuseStep 2165671 = 3248507) B3248507
theorem B2436385 : Blo 2165435 2436385 := bbase (se 2 (by rfl) ⟨913644, by rfl⟩ : syracuseStep 2436385 = 1827289) (by norm_num)
theorem B3248513 : Blo 2165435 3248513 := bstep (se 2 (by rfl) ⟨1218192, by rfl⟩ : syracuseStep 3248513 = 2436385) B2436385
theorem B2165675 : Blo 2165435 2165675 := bstep (se 1 (by rfl) ⟨1624256, by rfl⟩ : syracuseStep 2165675 = 3248513) B3248513
theorem B5481877 : Blo 2165435 5481877 := bbase (se 6 (by rfl) ⟨128481, by rfl⟩ : syracuseStep 5481877 = 256963) (by norm_num)
theorem B7309169 : Blo 2165435 7309169 := bstep (se 2 (by rfl) ⟨2740938, by rfl⟩ : syracuseStep 7309169 = 5481877) B5481877
theorem B4872779 : Blo 2165435 4872779 := bstep (se 1 (by rfl) ⟨3654584, by rfl⟩ : syracuseStep 4872779 = 7309169) B7309169
theorem B3248519 : Blo 2165435 3248519 := bstep (se 1 (by rfl) ⟨2436389, by rfl⟩ : syracuseStep 3248519 = 4872779) B4872779
theorem B2165679 : Blo 2165435 2165679 := bstep (se 1 (by rfl) ⟨1624259, by rfl⟩ : syracuseStep 2165679 = 3248519) B3248519
theorem B3248525 : Blo 2165435 3248525 := bbase (se 3 (by rfl) ⟨609098, by rfl⟩ : syracuseStep 3248525 = 1218197) (by norm_num)
theorem B2165683 : Blo 2165435 2165683 := bstep (se 1 (by rfl) ⟨1624262, by rfl⟩ : syracuseStep 2165683 = 3248525) B3248525
theorem B4872797 : Blo 2165435 4872797 := bbase (se 3 (by rfl) ⟨913649, by rfl⟩ : syracuseStep 4872797 = 1827299) (by norm_num)
theorem B3248531 : Blo 2165435 3248531 := bstep (se 1 (by rfl) ⟨2436398, by rfl⟩ : syracuseStep 3248531 = 4872797) B4872797
theorem B2165687 : Blo 2165435 2165687 := bstep (se 1 (by rfl) ⟨1624265, by rfl⟩ : syracuseStep 2165687 = 3248531) B3248531
theorem B3654605 : Blo 2165435 3654605 := bbase (se 3 (by rfl) ⟨685238, by rfl⟩ : syracuseStep 3654605 = 1370477) (by norm_num)
theorem B2436403 : Blo 2165435 2436403 := bstep (se 1 (by rfl) ⟨1827302, by rfl⟩ : syracuseStep 2436403 = 3654605) B3654605
theorem B3248537 : Blo 2165435 3248537 := bstep (se 2 (by rfl) ⟨1218201, by rfl⟩ : syracuseStep 3248537 = 2436403) B2436403
theorem B2165691 : Blo 2165435 2165691 := bstep (se 1 (by rfl) ⟨1624268, by rfl⟩ : syracuseStep 2165691 = 3248537) B3248537
theorem B9376949 : Blo 2165435 9376949 := bbase (se 5 (by rfl) ⟨439544, by rfl⟩ : syracuseStep 9376949 = 879089) (by norm_num)
theorem B6251299 : Blo 2165435 6251299 := bstep (se 1 (by rfl) ⟨4688474, by rfl⟩ : syracuseStep 6251299 = 9376949) B9376949
theorem B33340261 : Blo 2165435 33340261 := bstep (se 4 (by rfl) ⟨3125649, by rfl⟩ : syracuseStep 33340261 = 6251299) B6251299
theorem B44453681 : Blo 2165435 44453681 := bstep (se 2 (by rfl) ⟨16670130, by rfl⟩ : syracuseStep 44453681 = 33340261) B33340261
theorem B29635787 : Blo 2165435 29635787 := bstep (se 1 (by rfl) ⟨22226840, by rfl⟩ : syracuseStep 29635787 = 44453681) B44453681
theorem B19757191 : Blo 2165435 19757191 := bstep (se 1 (by rfl) ⟨14817893, by rfl⟩ : syracuseStep 19757191 = 29635787) B29635787
theorem B26342921 : Blo 2165435 26342921 := bstep (se 2 (by rfl) ⟨9878595, by rfl⟩ : syracuseStep 26342921 = 19757191) B19757191
theorem B17561947 : Blo 2165435 17561947 := bstep (se 1 (by rfl) ⟨13171460, by rfl⟩ : syracuseStep 17561947 = 26342921) B26342921
theorem B23415929 : Blo 2165435 23415929 := bstep (se 2 (by rfl) ⟨8780973, by rfl⟩ : syracuseStep 23415929 = 17561947) B17561947
theorem B15610619 : Blo 2165435 15610619 := bstep (se 1 (by rfl) ⟨11707964, by rfl⟩ : syracuseStep 15610619 = 23415929) B23415929
theorem B10407079 : Blo 2165435 10407079 := bstep (se 1 (by rfl) ⟨7805309, by rfl⟩ : syracuseStep 10407079 = 15610619) B15610619
theorem B13876105 : Blo 2165435 13876105 := bstep (se 2 (by rfl) ⟨5203539, by rfl⟩ : syracuseStep 13876105 = 10407079) B10407079
theorem B18501473 : Blo 2165435 18501473 := bstep (se 2 (by rfl) ⟨6938052, by rfl⟩ : syracuseStep 18501473 = 13876105) B13876105
theorem B12334315 : Blo 2165435 12334315 := bstep (se 1 (by rfl) ⟨9250736, by rfl⟩ : syracuseStep 12334315 = 18501473) B18501473
theorem B16445753 : Blo 2165435 16445753 := bstep (se 2 (by rfl) ⟨6167157, by rfl⟩ : syracuseStep 16445753 = 12334315) B12334315
theorem B10963835 : Blo 2165435 10963835 := bstep (se 1 (by rfl) ⟨8222876, by rfl⟩ : syracuseStep 10963835 = 16445753) B16445753
theorem B7309223 : Blo 2165435 7309223 := bstep (se 1 (by rfl) ⟨5481917, by rfl⟩ : syracuseStep 7309223 = 10963835) B10963835
theorem B4872815 : Blo 2165435 4872815 := bstep (se 1 (by rfl) ⟨3654611, by rfl⟩ : syracuseStep 4872815 = 7309223) B7309223
theorem B3248543 : Blo 2165435 3248543 := bstep (se 1 (by rfl) ⟨2436407, by rfl⟩ : syracuseStep 3248543 = 4872815) B4872815
theorem B2165695 : Blo 2165435 2165695 := bstep (se 1 (by rfl) ⟨1624271, by rfl⟩ : syracuseStep 2165695 = 3248543) B3248543
theorem B3248549 : Blo 2165435 3248549 := bbase (se 4 (by rfl) ⟨304551, by rfl⟩ : syracuseStep 3248549 = 609103) (by norm_num)
theorem B2165699 : Blo 2165435 2165699 := bstep (se 1 (by rfl) ⟨1624274, by rfl⟩ : syracuseStep 2165699 = 3248549) B3248549
theorem B2740969 : Blo 2165435 2740969 := bbase (se 2 (by rfl) ⟨1027863, by rfl⟩ : syracuseStep 2740969 = 2055727) (by norm_num)
theorem B3654625 : Blo 2165435 3654625 := bstep (se 2 (by rfl) ⟨1370484, by rfl⟩ : syracuseStep 3654625 = 2740969) B2740969
theorem B4872833 : Blo 2165435 4872833 := bstep (se 2 (by rfl) ⟨1827312, by rfl⟩ : syracuseStep 4872833 = 3654625) B3654625
theorem B3248555 : Blo 2165435 3248555 := bstep (se 1 (by rfl) ⟨2436416, by rfl⟩ : syracuseStep 3248555 = 4872833) B4872833
theorem B2165703 : Blo 2165435 2165703 := bstep (se 1 (by rfl) ⟨1624277, by rfl⟩ : syracuseStep 2165703 = 3248555) B3248555
theorem B2436421 : Blo 2165435 2436421 := bbase (se 4 (by rfl) ⟨228414, by rfl⟩ : syracuseStep 2436421 = 456829) (by norm_num)
theorem B3248561 : Blo 2165435 3248561 := bstep (se 2 (by rfl) ⟨1218210, by rfl⟩ : syracuseStep 3248561 = 2436421) B2436421
theorem B2165707 : Blo 2165435 2165707 := bstep (se 1 (by rfl) ⟨1624280, by rfl⟩ : syracuseStep 2165707 = 3248561) B3248561
theorem B4111469 : Blo 2165435 4111469 := bbase (se 3 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 4111469 = 1541801) (by norm_num)
theorem B2740979 : Blo 2165435 2740979 := bstep (se 1 (by rfl) ⟨2055734, by rfl⟩ : syracuseStep 2740979 = 4111469) B4111469
theorem B7309277 : Blo 2165435 7309277 := bstep (se 3 (by rfl) ⟨1370489, by rfl⟩ : syracuseStep 7309277 = 2740979) B2740979
theorem B4872851 : Blo 2165435 4872851 := bstep (se 1 (by rfl) ⟨3654638, by rfl⟩ : syracuseStep 4872851 = 7309277) B7309277
theorem B3248567 : Blo 2165435 3248567 := bstep (se 1 (by rfl) ⟨2436425, by rfl⟩ : syracuseStep 3248567 = 4872851) B4872851
theorem B2165711 : Blo 2165435 2165711 := bstep (se 1 (by rfl) ⟨1624283, by rfl⟩ : syracuseStep 2165711 = 3248567) B3248567
theorem B3248573 : Blo 2165435 3248573 := bbase (se 3 (by rfl) ⟨609107, by rfl⟩ : syracuseStep 3248573 = 1218215) (by norm_num)
theorem B2165715 : Blo 2165435 2165715 := bstep (se 1 (by rfl) ⟨1624286, by rfl⟩ : syracuseStep 2165715 = 3248573) B3248573
theorem B4872869 : Blo 2165435 4872869 := bbase (se 4 (by rfl) ⟨456831, by rfl⟩ : syracuseStep 4872869 = 913663) (by norm_num)
theorem B3248579 : Blo 2165435 3248579 := bstep (se 1 (by rfl) ⟨2436434, by rfl⟩ : syracuseStep 3248579 = 4872869) B4872869
theorem B2165719 : Blo 2165435 2165719 := bstep (se 1 (by rfl) ⟨1624289, by rfl⟩ : syracuseStep 2165719 = 3248579) B3248579
theorem B5481989 : Blo 2165435 5481989 := bbase (se 4 (by rfl) ⟨513936, by rfl⟩ : syracuseStep 5481989 = 1027873) (by norm_num)
theorem B3654659 : Blo 2165435 3654659 := bstep (se 1 (by rfl) ⟨2740994, by rfl⟩ : syracuseStep 3654659 = 5481989) B5481989
theorem B2436439 : Blo 2165435 2436439 := bstep (se 1 (by rfl) ⟨1827329, by rfl⟩ : syracuseStep 2436439 = 3654659) B3654659
theorem B3248585 : Blo 2165435 3248585 := bstep (se 2 (by rfl) ⟨1218219, by rfl⟩ : syracuseStep 3248585 = 2436439) B2436439
theorem B2165723 : Blo 2165435 2165723 := bstep (se 1 (by rfl) ⟨1624292, by rfl⟩ : syracuseStep 2165723 = 3248585) B3248585
theorem B4625437 : Blo 2165435 4625437 := bbase (se 3 (by rfl) ⟨867269, by rfl⟩ : syracuseStep 4625437 = 1734539) (by norm_num)
theorem B6167249 : Blo 2165435 6167249 := bstep (se 2 (by rfl) ⟨2312718, by rfl⟩ : syracuseStep 6167249 = 4625437) B4625437
theorem B4111499 : Blo 2165435 4111499 := bstep (se 1 (by rfl) ⟨3083624, by rfl⟩ : syracuseStep 4111499 = 6167249) B6167249
theorem B10963997 : Blo 2165435 10963997 := bstep (se 3 (by rfl) ⟨2055749, by rfl⟩ : syracuseStep 10963997 = 4111499) B4111499
theorem B7309331 : Blo 2165435 7309331 := bstep (se 1 (by rfl) ⟨5481998, by rfl⟩ : syracuseStep 7309331 = 10963997) B10963997
theorem B4872887 : Blo 2165435 4872887 := bstep (se 1 (by rfl) ⟨3654665, by rfl⟩ : syracuseStep 4872887 = 7309331) B7309331
theorem B3248591 : Blo 2165435 3248591 := bstep (se 1 (by rfl) ⟨2436443, by rfl⟩ : syracuseStep 3248591 = 4872887) B4872887
theorem B2165727 : Blo 2165435 2165727 := bstep (se 1 (by rfl) ⟨1624295, by rfl⟩ : syracuseStep 2165727 = 3248591) B3248591
theorem B3248597 : Blo 2165435 3248597 := bbase (se 7 (by rfl) ⟨38069, by rfl⟩ : syracuseStep 3248597 = 76139) (by norm_num)
theorem B2165731 : Blo 2165435 2165731 := bstep (se 1 (by rfl) ⟨1624298, by rfl⟩ : syracuseStep 2165731 = 3248597) B3248597
theorem B8223029 : Blo 2165435 8223029 := bbase (se 5 (by rfl) ⟨385454, by rfl⟩ : syracuseStep 8223029 = 770909) (by norm_num)
theorem B5482019 : Blo 2165435 5482019 := bstep (se 1 (by rfl) ⟨4111514, by rfl⟩ : syracuseStep 5482019 = 8223029) B8223029
theorem B3654679 : Blo 2165435 3654679 := bstep (se 1 (by rfl) ⟨2741009, by rfl⟩ : syracuseStep 3654679 = 5482019) B5482019
theorem B4872905 : Blo 2165435 4872905 := bstep (se 2 (by rfl) ⟨1827339, by rfl⟩ : syracuseStep 4872905 = 3654679) B3654679
theorem B3248603 : Blo 2165435 3248603 := bstep (se 1 (by rfl) ⟨2436452, by rfl⟩ : syracuseStep 3248603 = 4872905) B4872905
theorem B2165735 : Blo 2165435 2165735 := bstep (se 1 (by rfl) ⟨1624301, by rfl⟩ : syracuseStep 2165735 = 3248603) B3248603
theorem B2436457 : Blo 2165435 2436457 := bbase (se 2 (by rfl) ⟨913671, by rfl⟩ : syracuseStep 2436457 = 1827343) (by norm_num)
theorem B3248609 : Blo 2165435 3248609 := bstep (se 2 (by rfl) ⟨1218228, by rfl⟩ : syracuseStep 3248609 = 2436457) B2436457
theorem B2165739 : Blo 2165435 2165739 := bstep (se 1 (by rfl) ⟨1624304, by rfl⟩ : syracuseStep 2165739 = 3248609) B3248609
theorem B6585877 : Blo 2165435 6585877 := bbase (se 6 (by rfl) ⟨154356, by rfl⟩ : syracuseStep 6585877 = 308713) (by norm_num)
theorem B35124677 : Blo 2165435 35124677 := bstep (se 4 (by rfl) ⟨3292938, by rfl⟩ : syracuseStep 35124677 = 6585877) B6585877
theorem B23416451 : Blo 2165435 23416451 := bstep (se 1 (by rfl) ⟨17562338, by rfl⟩ : syracuseStep 23416451 = 35124677) B35124677
theorem B15610967 : Blo 2165435 15610967 := bstep (se 1 (by rfl) ⟨11708225, by rfl⟩ : syracuseStep 15610967 = 23416451) B23416451
theorem B10407311 : Blo 2165435 10407311 := bstep (se 1 (by rfl) ⟨7805483, by rfl⟩ : syracuseStep 10407311 = 15610967) B15610967
theorem B6938207 : Blo 2165435 6938207 := bstep (se 1 (by rfl) ⟨5203655, by rfl⟩ : syracuseStep 6938207 = 10407311) B10407311
theorem B4625471 : Blo 2165435 4625471 := bstep (se 1 (by rfl) ⟨3469103, by rfl⟩ : syracuseStep 4625471 = 6938207) B6938207
theorem B12334589 : Blo 2165435 12334589 := bstep (se 3 (by rfl) ⟨2312735, by rfl⟩ : syracuseStep 12334589 = 4625471) B4625471
theorem B8223059 : Blo 2165435 8223059 := bstep (se 1 (by rfl) ⟨6167294, by rfl⟩ : syracuseStep 8223059 = 12334589) B12334589
theorem B5482039 : Blo 2165435 5482039 := bstep (se 1 (by rfl) ⟨4111529, by rfl⟩ : syracuseStep 5482039 = 8223059) B8223059
theorem B7309385 : Blo 2165435 7309385 := bstep (se 2 (by rfl) ⟨2741019, by rfl⟩ : syracuseStep 7309385 = 5482039) B5482039
theorem B4872923 : Blo 2165435 4872923 := bstep (se 1 (by rfl) ⟨3654692, by rfl⟩ : syracuseStep 4872923 = 7309385) B7309385
theorem B3248615 : Blo 2165435 3248615 := bstep (se 1 (by rfl) ⟨2436461, by rfl⟩ : syracuseStep 3248615 = 4872923) B4872923
theorem B2165743 : Blo 2165435 2165743 := bstep (se 1 (by rfl) ⟨1624307, by rfl⟩ : syracuseStep 2165743 = 3248615) B3248615
theorem B3248621 : Blo 2165435 3248621 := bbase (se 3 (by rfl) ⟨609116, by rfl⟩ : syracuseStep 3248621 = 1218233) (by norm_num)
theorem B2165747 : Blo 2165435 2165747 := bstep (se 1 (by rfl) ⟨1624310, by rfl⟩ : syracuseStep 2165747 = 3248621) B3248621
theorem B4872941 : Blo 2165435 4872941 := bbase (se 3 (by rfl) ⟨913676, by rfl⟩ : syracuseStep 4872941 = 1827353) (by norm_num)
theorem B3248627 : Blo 2165435 3248627 := bstep (se 1 (by rfl) ⟨2436470, by rfl⟩ : syracuseStep 3248627 = 4872941) B4872941
theorem B2165751 : Blo 2165435 2165751 := bstep (se 1 (by rfl) ⟨1624313, by rfl⟩ : syracuseStep 2165751 = 3248627) B3248627
theorem B2312749 : Blo 2165435 2312749 := bbase (se 3 (by rfl) ⟨433640, by rfl⟩ : syracuseStep 2312749 = 867281) (by norm_num)
theorem B3083665 : Blo 2165435 3083665 := bstep (se 2 (by rfl) ⟨1156374, by rfl⟩ : syracuseStep 3083665 = 2312749) B2312749
theorem B4111553 : Blo 2165435 4111553 := bstep (se 2 (by rfl) ⟨1541832, by rfl⟩ : syracuseStep 4111553 = 3083665) B3083665
theorem B2741035 : Blo 2165435 2741035 := bstep (se 1 (by rfl) ⟨2055776, by rfl⟩ : syracuseStep 2741035 = 4111553) B4111553
theorem B3654713 : Blo 2165435 3654713 := bstep (se 2 (by rfl) ⟨1370517, by rfl⟩ : syracuseStep 3654713 = 2741035) B2741035
theorem B2436475 : Blo 2165435 2436475 := bstep (se 1 (by rfl) ⟨1827356, by rfl⟩ : syracuseStep 2436475 = 3654713) B3654713
theorem B3248633 : Blo 2165435 3248633 := bstep (se 2 (by rfl) ⟨1218237, by rfl⟩ : syracuseStep 3248633 = 2436475) B2436475
theorem B2165755 : Blo 2165435 2165755 := bstep (se 1 (by rfl) ⟨1624316, by rfl⟩ : syracuseStep 2165755 = 3248633) B3248633
theorem B2778437 : Blo 2165435 2778437 := bbase (se 4 (by rfl) ⟨260478, by rfl⟩ : syracuseStep 2778437 = 520957) (by norm_num)
theorem B7409165 : Blo 2165435 7409165 := bstep (se 3 (by rfl) ⟨1389218, by rfl⟩ : syracuseStep 7409165 = 2778437) B2778437
theorem B19757773 : Blo 2165435 19757773 := bstep (se 3 (by rfl) ⟨3704582, by rfl⟩ : syracuseStep 19757773 = 7409165) B7409165
theorem B26343697 : Blo 2165435 26343697 := bstep (se 2 (by rfl) ⟨9878886, by rfl⟩ : syracuseStep 26343697 = 19757773) B19757773
theorem B35124929 : Blo 2165435 35124929 := bstep (se 2 (by rfl) ⟨13171848, by rfl⟩ : syracuseStep 35124929 = 26343697) B26343697
theorem B23416619 : Blo 2165435 23416619 := bstep (se 1 (by rfl) ⟨17562464, by rfl⟩ : syracuseStep 23416619 = 35124929) B35124929
theorem B62444317 : Blo 2165435 62444317 := bstep (se 3 (by rfl) ⟨11708309, by rfl⟩ : syracuseStep 62444317 = 23416619) B23416619
theorem B83259089 : Blo 2165435 83259089 := bstep (se 2 (by rfl) ⟨31222158, by rfl⟩ : syracuseStep 83259089 = 62444317) B62444317
theorem B55506059 : Blo 2165435 55506059 := bstep (se 1 (by rfl) ⟨41629544, by rfl⟩ : syracuseStep 55506059 = 83259089) B83259089
theorem B37004039 : Blo 2165435 37004039 := bstep (se 1 (by rfl) ⟨27753029, by rfl⟩ : syracuseStep 37004039 = 55506059) B55506059
theorem B24669359 : Blo 2165435 24669359 := bstep (se 1 (by rfl) ⟨18502019, by rfl⟩ : syracuseStep 24669359 = 37004039) B37004039
theorem B16446239 : Blo 2165435 16446239 := bstep (se 1 (by rfl) ⟨12334679, by rfl⟩ : syracuseStep 16446239 = 24669359) B24669359
theorem B10964159 : Blo 2165435 10964159 := bstep (se 1 (by rfl) ⟨8223119, by rfl⟩ : syracuseStep 10964159 = 16446239) B16446239
theorem B7309439 : Blo 2165435 7309439 := bstep (se 1 (by rfl) ⟨5482079, by rfl⟩ : syracuseStep 7309439 = 10964159) B10964159
theorem B4872959 : Blo 2165435 4872959 := bstep (se 1 (by rfl) ⟨3654719, by rfl⟩ : syracuseStep 4872959 = 7309439) B7309439
theorem B3248639 : Blo 2165435 3248639 := bstep (se 1 (by rfl) ⟨2436479, by rfl⟩ : syracuseStep 3248639 = 4872959) B4872959
theorem B2165759 : Blo 2165435 2165759 := bstep (se 1 (by rfl) ⟨1624319, by rfl⟩ : syracuseStep 2165759 = 3248639) B3248639
theorem B3248645 : Blo 2165435 3248645 := bbase (se 4 (by rfl) ⟨304560, by rfl⟩ : syracuseStep 3248645 = 609121) (by norm_num)
theorem B2165763 : Blo 2165435 2165763 := bstep (se 1 (by rfl) ⟨1624322, by rfl⟩ : syracuseStep 2165763 = 3248645) B3248645
theorem B3654733 : Blo 2165435 3654733 := bbase (se 3 (by rfl) ⟨685262, by rfl⟩ : syracuseStep 3654733 = 1370525) (by norm_num)
theorem B4872977 : Blo 2165435 4872977 := bstep (se 2 (by rfl) ⟨1827366, by rfl⟩ : syracuseStep 4872977 = 3654733) B3654733
theorem B3248651 : Blo 2165435 3248651 := bstep (se 1 (by rfl) ⟨2436488, by rfl⟩ : syracuseStep 3248651 = 4872977) B4872977
theorem B2165767 : Blo 2165435 2165767 := bstep (se 1 (by rfl) ⟨1624325, by rfl⟩ : syracuseStep 2165767 = 3248651) B3248651
theorem B2436493 : Blo 2165435 2436493 := bbase (se 3 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 2436493 = 913685) (by norm_num)
theorem B3248657 : Blo 2165435 3248657 := bstep (se 2 (by rfl) ⟨1218246, by rfl⟩ : syracuseStep 3248657 = 2436493) B2436493
theorem B2165771 : Blo 2165435 2165771 := bstep (se 1 (by rfl) ⟨1624328, by rfl⟩ : syracuseStep 2165771 = 3248657) B3248657
theorem B7309493 : Blo 2165435 7309493 := bbase (se 5 (by rfl) ⟨342632, by rfl⟩ : syracuseStep 7309493 = 685265) (by norm_num)
theorem B4872995 : Blo 2165435 4872995 := bstep (se 1 (by rfl) ⟨3654746, by rfl⟩ : syracuseStep 4872995 = 7309493) B7309493
theorem B3248663 : Blo 2165435 3248663 := bstep (se 1 (by rfl) ⟨2436497, by rfl⟩ : syracuseStep 3248663 = 4872995) B4872995
theorem B2165775 : Blo 2165435 2165775 := bstep (se 1 (by rfl) ⟨1624331, by rfl⟩ : syracuseStep 2165775 = 3248663) B3248663
theorem B3248669 : Blo 2165435 3248669 := bbase (se 3 (by rfl) ⟨609125, by rfl⟩ : syracuseStep 3248669 = 1218251) (by norm_num)
theorem B2165779 : Blo 2165435 2165779 := bstep (se 1 (by rfl) ⟨1624334, by rfl⟩ : syracuseStep 2165779 = 3248669) B3248669
theorem B4873013 : Blo 2165435 4873013 := bbase (se 5 (by rfl) ⟨228422, by rfl⟩ : syracuseStep 4873013 = 456845) (by norm_num)
theorem B3248675 : Blo 2165435 3248675 := bstep (se 1 (by rfl) ⟨2436506, by rfl⟩ : syracuseStep 3248675 = 4873013) B4873013
theorem B2165783 : Blo 2165435 2165783 := bstep (se 1 (by rfl) ⟨1624337, by rfl⟩ : syracuseStep 2165783 = 3248675) B3248675
theorem B15611285 : Blo 2165435 15611285 := bbase (se 6 (by rfl) ⟨365889, by rfl⟩ : syracuseStep 15611285 = 731779) (by norm_num)
theorem B10407523 : Blo 2165435 10407523 := bstep (se 1 (by rfl) ⟨7805642, by rfl⟩ : syracuseStep 10407523 = 15611285) B15611285
theorem B13876697 : Blo 2165435 13876697 := bstep (se 2 (by rfl) ⟨5203761, by rfl⟩ : syracuseStep 13876697 = 10407523) B10407523
theorem B9251131 : Blo 2165435 9251131 := bstep (se 1 (by rfl) ⟨6938348, by rfl⟩ : syracuseStep 9251131 = 13876697) B13876697
theorem B12334841 : Blo 2165435 12334841 := bstep (se 2 (by rfl) ⟨4625565, by rfl⟩ : syracuseStep 12334841 = 9251131) B9251131
theorem B8223227 : Blo 2165435 8223227 := bstep (se 1 (by rfl) ⟨6167420, by rfl⟩ : syracuseStep 8223227 = 12334841) B12334841
theorem B5482151 : Blo 2165435 5482151 := bstep (se 1 (by rfl) ⟨4111613, by rfl⟩ : syracuseStep 5482151 = 8223227) B8223227
theorem B3654767 : Blo 2165435 3654767 := bstep (se 1 (by rfl) ⟨2741075, by rfl⟩ : syracuseStep 3654767 = 5482151) B5482151
theorem B2436511 : Blo 2165435 2436511 := bstep (se 1 (by rfl) ⟨1827383, by rfl⟩ : syracuseStep 2436511 = 3654767) B3654767
theorem B3248681 : Blo 2165435 3248681 := bstep (se 2 (by rfl) ⟨1218255, by rfl⟩ : syracuseStep 3248681 = 2436511) B2436511
theorem B2165787 : Blo 2165435 2165787 := bstep (se 1 (by rfl) ⟨1624340, by rfl⟩ : syracuseStep 2165787 = 3248681) B3248681
theorem B10407541 : Blo 2165435 10407541 := bbase (se 5 (by rfl) ⟨487853, by rfl⟩ : syracuseStep 10407541 = 975707) (by norm_num)
theorem B13876721 : Blo 2165435 13876721 := bstep (se 2 (by rfl) ⟨5203770, by rfl⟩ : syracuseStep 13876721 = 10407541) B10407541
theorem B9251147 : Blo 2165435 9251147 := bstep (se 1 (by rfl) ⟨6938360, by rfl⟩ : syracuseStep 9251147 = 13876721) B13876721
theorem B6167431 : Blo 2165435 6167431 := bstep (se 1 (by rfl) ⟨4625573, by rfl⟩ : syracuseStep 6167431 = 9251147) B9251147
theorem B8223241 : Blo 2165435 8223241 := bstep (se 2 (by rfl) ⟨3083715, by rfl⟩ : syracuseStep 8223241 = 6167431) B6167431
theorem B10964321 : Blo 2165435 10964321 := bstep (se 2 (by rfl) ⟨4111620, by rfl⟩ : syracuseStep 10964321 = 8223241) B8223241
theorem B7309547 : Blo 2165435 7309547 := bstep (se 1 (by rfl) ⟨5482160, by rfl⟩ : syracuseStep 7309547 = 10964321) B10964321
theorem B4873031 : Blo 2165435 4873031 := bstep (se 1 (by rfl) ⟨3654773, by rfl⟩ : syracuseStep 4873031 = 7309547) B7309547
theorem B3248687 : Blo 2165435 3248687 := bstep (se 1 (by rfl) ⟨2436515, by rfl⟩ : syracuseStep 3248687 = 4873031) B4873031
theorem B2165791 : Blo 2165435 2165791 := bstep (se 1 (by rfl) ⟨1624343, by rfl⟩ : syracuseStep 2165791 = 3248687) B3248687
theorem B3248693 : Blo 2165435 3248693 := bbase (se 5 (by rfl) ⟨152282, by rfl⟩ : syracuseStep 3248693 = 304565) (by norm_num)
theorem B2165795 : Blo 2165435 2165795 := bstep (se 1 (by rfl) ⟨1624346, by rfl⟩ : syracuseStep 2165795 = 3248693) B3248693
theorem B5482181 : Blo 2165435 5482181 := bbase (se 4 (by rfl) ⟨513954, by rfl⟩ : syracuseStep 5482181 = 1027909) (by norm_num)
theorem B3654787 : Blo 2165435 3654787 := bstep (se 1 (by rfl) ⟨2741090, by rfl⟩ : syracuseStep 3654787 = 5482181) B5482181
theorem B4873049 : Blo 2165435 4873049 := bstep (se 2 (by rfl) ⟨1827393, by rfl⟩ : syracuseStep 4873049 = 3654787) B3654787
theorem B3248699 : Blo 2165435 3248699 := bstep (se 1 (by rfl) ⟨2436524, by rfl⟩ : syracuseStep 3248699 = 4873049) B4873049
theorem B2165799 : Blo 2165435 2165799 := bstep (se 1 (by rfl) ⟨1624349, by rfl⟩ : syracuseStep 2165799 = 3248699) B3248699
theorem B2436529 : Blo 2165435 2436529 := bbase (se 2 (by rfl) ⟨913698, by rfl⟩ : syracuseStep 2436529 = 1827397) (by norm_num)
theorem B3248705 : Blo 2165435 3248705 := bstep (se 2 (by rfl) ⟨1218264, by rfl⟩ : syracuseStep 3248705 = 2436529) B2436529
theorem B2165803 : Blo 2165435 2165803 := bstep (se 1 (by rfl) ⟨1624352, by rfl⟩ : syracuseStep 2165803 = 3248705) B3248705
theorem B6167477 : Blo 2165435 6167477 := bbase (se 5 (by rfl) ⟨289100, by rfl⟩ : syracuseStep 6167477 = 578201) (by norm_num)
theorem B4111651 : Blo 2165435 4111651 := bstep (se 1 (by rfl) ⟨3083738, by rfl⟩ : syracuseStep 4111651 = 6167477) B6167477
theorem B5482201 : Blo 2165435 5482201 := bstep (se 2 (by rfl) ⟨2055825, by rfl⟩ : syracuseStep 5482201 = 4111651) B4111651
theorem B7309601 : Blo 2165435 7309601 := bstep (se 2 (by rfl) ⟨2741100, by rfl⟩ : syracuseStep 7309601 = 5482201) B5482201
theorem B4873067 : Blo 2165435 4873067 := bstep (se 1 (by rfl) ⟨3654800, by rfl⟩ : syracuseStep 4873067 = 7309601) B7309601
theorem B3248711 : Blo 2165435 3248711 := bstep (se 1 (by rfl) ⟨2436533, by rfl⟩ : syracuseStep 3248711 = 4873067) B4873067
theorem B2165807 : Blo 2165435 2165807 := bstep (se 1 (by rfl) ⟨1624355, by rfl⟩ : syracuseStep 2165807 = 3248711) B3248711
theorem B3248717 : Blo 2165435 3248717 := bbase (se 3 (by rfl) ⟨609134, by rfl⟩ : syracuseStep 3248717 = 1218269) (by norm_num)
theorem B2165811 : Blo 2165435 2165811 := bstep (se 1 (by rfl) ⟨1624358, by rfl⟩ : syracuseStep 2165811 = 3248717) B3248717
theorem B4873085 : Blo 2165435 4873085 := bbase (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) (by norm_num)
theorem B3248723 : Blo 2165435 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B2165815 : Blo 2165435 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B3654821 : Blo 2165435 3654821 := bbase (se 4 (by rfl) ⟨342639, by rfl⟩ : syracuseStep 3654821 = 685279) (by norm_num)
theorem B2436547 : Blo 2165435 2436547 := bstep (se 1 (by rfl) ⟨1827410, by rfl⟩ : syracuseStep 2436547 = 3654821) B3654821
theorem B3248729 : Blo 2165435 3248729 := bstep (se 2 (by rfl) ⟨1218273, by rfl⟩ : syracuseStep 3248729 = 2436547) B2436547
theorem B2165819 : Blo 2165435 2165819 := bstep (se 1 (by rfl) ⟨1624364, by rfl⟩ : syracuseStep 2165819 = 3248729) B3248729
theorem B2312821 : Blo 2165435 2312821 := bbase (se 5 (by rfl) ⟨108413, by rfl⟩ : syracuseStep 2312821 = 216827) (by norm_num)
theorem B3083761 : Blo 2165435 3083761 := bstep (se 2 (by rfl) ⟨1156410, by rfl⟩ : syracuseStep 3083761 = 2312821) B2312821
theorem B16446725 : Blo 2165435 16446725 := bstep (se 4 (by rfl) ⟨1541880, by rfl⟩ : syracuseStep 16446725 = 3083761) B3083761
theorem B10964483 : Blo 2165435 10964483 := bstep (se 1 (by rfl) ⟨8223362, by rfl⟩ : syracuseStep 10964483 = 16446725) B16446725
theorem B7309655 : Blo 2165435 7309655 := bstep (se 1 (by rfl) ⟨5482241, by rfl⟩ : syracuseStep 7309655 = 10964483) B10964483
theorem B4873103 : Blo 2165435 4873103 := bstep (se 1 (by rfl) ⟨3654827, by rfl⟩ : syracuseStep 4873103 = 7309655) B7309655
theorem B3248735 : Blo 2165435 3248735 := bstep (se 1 (by rfl) ⟨2436551, by rfl⟩ : syracuseStep 3248735 = 4873103) B4873103
theorem B2165823 : Blo 2165435 2165823 := bstep (se 1 (by rfl) ⟨1624367, by rfl⟩ : syracuseStep 2165823 = 3248735) B3248735
theorem B3248741 : Blo 2165435 3248741 := bbase (se 4 (by rfl) ⟨304569, by rfl⟩ : syracuseStep 3248741 = 609139) (by norm_num)
theorem B2165827 : Blo 2165435 2165827 := bstep (se 1 (by rfl) ⟨1624370, by rfl⟩ : syracuseStep 2165827 = 3248741) B3248741
theorem B3083773 : Blo 2165435 3083773 := bbase (se 3 (by rfl) ⟨578207, by rfl⟩ : syracuseStep 3083773 = 1156415) (by norm_num)
theorem B4111697 : Blo 2165435 4111697 := bstep (se 2 (by rfl) ⟨1541886, by rfl⟩ : syracuseStep 4111697 = 3083773) B3083773
theorem B2741131 : Blo 2165435 2741131 := bstep (se 1 (by rfl) ⟨2055848, by rfl⟩ : syracuseStep 2741131 = 4111697) B4111697
theorem B3654841 : Blo 2165435 3654841 := bstep (se 2 (by rfl) ⟨1370565, by rfl⟩ : syracuseStep 3654841 = 2741131) B2741131
theorem B4873121 : Blo 2165435 4873121 := bstep (se 2 (by rfl) ⟨1827420, by rfl⟩ : syracuseStep 4873121 = 3654841) B3654841
theorem B3248747 : Blo 2165435 3248747 := bstep (se 1 (by rfl) ⟨2436560, by rfl⟩ : syracuseStep 3248747 = 4873121) B4873121
theorem B2165831 : Blo 2165435 2165831 := bstep (se 1 (by rfl) ⟨1624373, by rfl⟩ : syracuseStep 2165831 = 3248747) B3248747
theorem B2436565 : Blo 2165435 2436565 := bbase (se 7 (by rfl) ⟨28553, by rfl⟩ : syracuseStep 2436565 = 57107) (by norm_num)
theorem B3248753 : Blo 2165435 3248753 := bstep (se 2 (by rfl) ⟨1218282, by rfl⟩ : syracuseStep 3248753 = 2436565) B2436565
theorem B2165835 : Blo 2165435 2165835 := bstep (se 1 (by rfl) ⟨1624376, by rfl⟩ : syracuseStep 2165835 = 3248753) B3248753
theorem B2741141 : Blo 2165435 2741141 := bbase (se 6 (by rfl) ⟨64245, by rfl⟩ : syracuseStep 2741141 = 128491) (by norm_num)
theorem B7309709 : Blo 2165435 7309709 := bstep (se 3 (by rfl) ⟨1370570, by rfl⟩ : syracuseStep 7309709 = 2741141) B2741141
theorem B4873139 : Blo 2165435 4873139 := bstep (se 1 (by rfl) ⟨3654854, by rfl⟩ : syracuseStep 4873139 = 7309709) B7309709
theorem B3248759 : Blo 2165435 3248759 := bstep (se 1 (by rfl) ⟨2436569, by rfl⟩ : syracuseStep 3248759 = 4873139) B4873139
theorem B2165839 : Blo 2165435 2165839 := bstep (se 1 (by rfl) ⟨1624379, by rfl⟩ : syracuseStep 2165839 = 3248759) B3248759
theorem B3248765 : Blo 2165435 3248765 := bbase (se 3 (by rfl) ⟨609143, by rfl⟩ : syracuseStep 3248765 = 1218287) (by norm_num)
theorem B2165843 : Blo 2165435 2165843 := bstep (se 1 (by rfl) ⟨1624382, by rfl⟩ : syracuseStep 2165843 = 3248765) B3248765
theorem B4873157 : Blo 2165435 4873157 := bbase (se 4 (by rfl) ⟨456858, by rfl⟩ : syracuseStep 4873157 = 913717) (by norm_num)
theorem B3248771 : Blo 2165435 3248771 := bstep (se 1 (by rfl) ⟨2436578, by rfl⟩ : syracuseStep 3248771 = 4873157) B4873157
theorem B2165847 : Blo 2165435 2165847 := bstep (se 1 (by rfl) ⟨1624385, by rfl⟩ : syracuseStep 2165847 = 3248771) B3248771
theorem B3469277 : Blo 2165435 3469277 := bbase (se 3 (by rfl) ⟨650489, by rfl⟩ : syracuseStep 3469277 = 1300979) (by norm_num)
theorem B9251405 : Blo 2165435 9251405 := bstep (se 3 (by rfl) ⟨1734638, by rfl⟩ : syracuseStep 9251405 = 3469277) B3469277
theorem B6167603 : Blo 2165435 6167603 := bstep (se 1 (by rfl) ⟨4625702, by rfl⟩ : syracuseStep 6167603 = 9251405) B9251405
theorem B4111735 : Blo 2165435 4111735 := bstep (se 1 (by rfl) ⟨3083801, by rfl⟩ : syracuseStep 4111735 = 6167603) B6167603
theorem B5482313 : Blo 2165435 5482313 := bstep (se 2 (by rfl) ⟨2055867, by rfl⟩ : syracuseStep 5482313 = 4111735) B4111735
theorem B3654875 : Blo 2165435 3654875 := bstep (se 1 (by rfl) ⟨2741156, by rfl⟩ : syracuseStep 3654875 = 5482313) B5482313
theorem B2436583 : Blo 2165435 2436583 := bstep (se 1 (by rfl) ⟨1827437, by rfl⟩ : syracuseStep 2436583 = 3654875) B3654875
theorem B3248777 : Blo 2165435 3248777 := bstep (se 2 (by rfl) ⟨1218291, by rfl⟩ : syracuseStep 3248777 = 2436583) B2436583
theorem B2165851 : Blo 2165435 2165851 := bstep (se 1 (by rfl) ⟨1624388, by rfl⟩ : syracuseStep 2165851 = 3248777) B3248777
theorem B10964645 : Blo 2165435 10964645 := bbase (se 4 (by rfl) ⟨1027935, by rfl⟩ : syracuseStep 10964645 = 2055871) (by norm_num)
theorem B7309763 : Blo 2165435 7309763 := bstep (se 1 (by rfl) ⟨5482322, by rfl⟩ : syracuseStep 7309763 = 10964645) B10964645
theorem B4873175 : Blo 2165435 4873175 := bstep (se 1 (by rfl) ⟨3654881, by rfl⟩ : syracuseStep 4873175 = 7309763) B7309763
theorem B3248783 : Blo 2165435 3248783 := bstep (se 1 (by rfl) ⟨2436587, by rfl⟩ : syracuseStep 3248783 = 4873175) B4873175
theorem B2165855 : Blo 2165435 2165855 := bstep (se 1 (by rfl) ⟨1624391, by rfl⟩ : syracuseStep 2165855 = 3248783) B3248783
theorem B3248789 : Blo 2165435 3248789 := bbase (se 6 (by rfl) ⟨76143, by rfl⟩ : syracuseStep 3248789 = 152287) (by norm_num)
theorem B2165859 : Blo 2165435 2165859 := bstep (se 1 (by rfl) ⟨1624394, by rfl⟩ : syracuseStep 2165859 = 3248789) B3248789
theorem B9505621 : Blo 2165435 9505621 := bbase (se 9 (by rfl) ⟨27848, by rfl⟩ : syracuseStep 9505621 = 55697) (by norm_num)
theorem B12674161 : Blo 2165435 12674161 := bstep (se 2 (by rfl) ⟨4752810, by rfl⟩ : syracuseStep 12674161 = 9505621) B9505621
theorem B16898881 : Blo 2165435 16898881 := bstep (se 2 (by rfl) ⟨6337080, by rfl⟩ : syracuseStep 16898881 = 12674161) B12674161
theorem B22531841 : Blo 2165435 22531841 := bstep (se 2 (by rfl) ⟨8449440, by rfl⟩ : syracuseStep 22531841 = 16898881) B16898881
theorem B15021227 : Blo 2165435 15021227 := bstep (se 1 (by rfl) ⟨11265920, by rfl⟩ : syracuseStep 15021227 = 22531841) B22531841
theorem B40056605 : Blo 2165435 40056605 := bstep (se 3 (by rfl) ⟨7510613, by rfl⟩ : syracuseStep 40056605 = 15021227) B15021227
theorem B26704403 : Blo 2165435 26704403 := bstep (se 1 (by rfl) ⟨20028302, by rfl⟩ : syracuseStep 26704403 = 40056605) B40056605
theorem B17802935 : Blo 2165435 17802935 := bstep (se 1 (by rfl) ⟨13352201, by rfl⟩ : syracuseStep 17802935 = 26704403) B26704403
theorem B11868623 : Blo 2165435 11868623 := bstep (se 1 (by rfl) ⟨8901467, by rfl⟩ : syracuseStep 11868623 = 17802935) B17802935
theorem B7912415 : Blo 2165435 7912415 := bstep (se 1 (by rfl) ⟨5934311, by rfl⟩ : syracuseStep 7912415 = 11868623) B11868623
theorem B5274943 : Blo 2165435 5274943 := bstep (se 1 (by rfl) ⟨3956207, by rfl⟩ : syracuseStep 5274943 = 7912415) B7912415
theorem B28133029 : Blo 2165435 28133029 := bstep (se 4 (by rfl) ⟨2637471, by rfl⟩ : syracuseStep 28133029 = 5274943) B5274943
theorem B37510705 : Blo 2165435 37510705 := bstep (se 2 (by rfl) ⟨14066514, by rfl⟩ : syracuseStep 37510705 = 28133029) B28133029
theorem B50014273 : Blo 2165435 50014273 := bstep (se 2 (by rfl) ⟨18755352, by rfl⟩ : syracuseStep 50014273 = 37510705) B37510705
theorem B66685697 : Blo 2165435 66685697 := bstep (se 2 (by rfl) ⟨25007136, by rfl⟩ : syracuseStep 66685697 = 50014273) B50014273
theorem B44457131 : Blo 2165435 44457131 := bstep (se 1 (by rfl) ⟨33342848, by rfl⟩ : syracuseStep 44457131 = 66685697) B66685697
theorem B118552349 : Blo 2165435 118552349 := bstep (se 3 (by rfl) ⟨22228565, by rfl⟩ : syracuseStep 118552349 = 44457131) B44457131
theorem B79034899 : Blo 2165435 79034899 := bstep (se 1 (by rfl) ⟨59276174, by rfl⟩ : syracuseStep 79034899 = 118552349) B118552349
theorem B105379865 : Blo 2165435 105379865 := bstep (se 2 (by rfl) ⟨39517449, by rfl⟩ : syracuseStep 105379865 = 79034899) B79034899
theorem B70253243 : Blo 2165435 70253243 := bstep (se 1 (by rfl) ⟨52689932, by rfl⟩ : syracuseStep 70253243 = 105379865) B105379865
theorem B46835495 : Blo 2165435 46835495 := bstep (se 1 (by rfl) ⟨35126621, by rfl⟩ : syracuseStep 46835495 = 70253243) B70253243
theorem B31223663 : Blo 2165435 31223663 := bstep (se 1 (by rfl) ⟨23417747, by rfl⟩ : syracuseStep 31223663 = 46835495) B46835495
theorem B20815775 : Blo 2165435 20815775 := bstep (se 1 (by rfl) ⟨15611831, by rfl⟩ : syracuseStep 20815775 = 31223663) B31223663
theorem B13877183 : Blo 2165435 13877183 := bstep (se 1 (by rfl) ⟨10407887, by rfl⟩ : syracuseStep 13877183 = 20815775) B20815775
theorem B9251455 : Blo 2165435 9251455 := bstep (se 1 (by rfl) ⟨6938591, by rfl⟩ : syracuseStep 9251455 = 13877183) B13877183
theorem B12335273 : Blo 2165435 12335273 := bstep (se 2 (by rfl) ⟨4625727, by rfl⟩ : syracuseStep 12335273 = 9251455) B9251455
theorem B8223515 : Blo 2165435 8223515 := bstep (se 1 (by rfl) ⟨6167636, by rfl⟩ : syracuseStep 8223515 = 12335273) B12335273
theorem B5482343 : Blo 2165435 5482343 := bstep (se 1 (by rfl) ⟨4111757, by rfl⟩ : syracuseStep 5482343 = 8223515) B8223515
theorem B3654895 : Blo 2165435 3654895 := bstep (se 1 (by rfl) ⟨2741171, by rfl⟩ : syracuseStep 3654895 = 5482343) B5482343
theorem B4873193 : Blo 2165435 4873193 := bstep (se 2 (by rfl) ⟨1827447, by rfl⟩ : syracuseStep 4873193 = 3654895) B3654895
theorem B3248795 : Blo 2165435 3248795 := bstep (se 1 (by rfl) ⟨2436596, by rfl⟩ : syracuseStep 3248795 = 4873193) B4873193
theorem B2165863 : Blo 2165435 2165863 := bstep (se 1 (by rfl) ⟨1624397, by rfl⟩ : syracuseStep 2165863 = 3248795) B3248795
theorem B2436601 : Blo 2165435 2436601 := bbase (se 2 (by rfl) ⟨913725, by rfl⟩ : syracuseStep 2436601 = 1827451) (by norm_num)
theorem B3248801 : Blo 2165435 3248801 := bstep (se 2 (by rfl) ⟨1218300, by rfl⟩ : syracuseStep 3248801 = 2436601) B2436601
theorem B2165867 : Blo 2165435 2165867 := bstep (se 1 (by rfl) ⟨1624400, by rfl⟩ : syracuseStep 2165867 = 3248801) B3248801
theorem B5274965 : Blo 2165435 5274965 := bbase (se 11 (by rfl) ⟨3863, by rfl⟩ : syracuseStep 5274965 = 7727) (by norm_num)
theorem B3516643 : Blo 2165435 3516643 := bstep (se 1 (by rfl) ⟨2637482, by rfl⟩ : syracuseStep 3516643 = 5274965) B5274965
theorem B4688857 : Blo 2165435 4688857 := bstep (se 2 (by rfl) ⟨1758321, by rfl⟩ : syracuseStep 4688857 = 3516643) B3516643
theorem B25007237 : Blo 2165435 25007237 := bstep (se 4 (by rfl) ⟨2344428, by rfl⟩ : syracuseStep 25007237 = 4688857) B4688857
theorem B16671491 : Blo 2165435 16671491 := bstep (se 1 (by rfl) ⟨12503618, by rfl⟩ : syracuseStep 16671491 = 25007237) B25007237
theorem B11114327 : Blo 2165435 11114327 := bstep (se 1 (by rfl) ⟨8335745, by rfl⟩ : syracuseStep 11114327 = 16671491) B16671491
theorem B7409551 : Blo 2165435 7409551 := bstep (se 1 (by rfl) ⟨5557163, by rfl⟩ : syracuseStep 7409551 = 11114327) B11114327
theorem B9879401 : Blo 2165435 9879401 := bstep (se 2 (by rfl) ⟨3704775, by rfl⟩ : syracuseStep 9879401 = 7409551) B7409551
theorem B6586267 : Blo 2165435 6586267 := bstep (se 1 (by rfl) ⟨4939700, by rfl⟩ : syracuseStep 6586267 = 9879401) B9879401
theorem B8781689 : Blo 2165435 8781689 := bstep (se 2 (by rfl) ⟨3293133, by rfl⟩ : syracuseStep 8781689 = 6586267) B6586267
theorem B5854459 : Blo 2165435 5854459 := bstep (se 1 (by rfl) ⟨4390844, by rfl⟩ : syracuseStep 5854459 = 8781689) B8781689
theorem B7805945 : Blo 2165435 7805945 := bstep (se 2 (by rfl) ⟨2927229, by rfl⟩ : syracuseStep 7805945 = 5854459) B5854459
theorem B5203963 : Blo 2165435 5203963 := bstep (se 1 (by rfl) ⟨3902972, by rfl⟩ : syracuseStep 5203963 = 7805945) B7805945
theorem B6938617 : Blo 2165435 6938617 := bstep (se 2 (by rfl) ⟨2601981, by rfl⟩ : syracuseStep 6938617 = 5203963) B5203963
theorem B9251489 : Blo 2165435 9251489 := bstep (se 2 (by rfl) ⟨3469308, by rfl⟩ : syracuseStep 9251489 = 6938617) B6938617
theorem B6167659 : Blo 2165435 6167659 := bstep (se 1 (by rfl) ⟨4625744, by rfl⟩ : syracuseStep 6167659 = 9251489) B9251489
theorem B8223545 : Blo 2165435 8223545 := bstep (se 2 (by rfl) ⟨3083829, by rfl⟩ : syracuseStep 8223545 = 6167659) B6167659
theorem B5482363 : Blo 2165435 5482363 := bstep (se 1 (by rfl) ⟨4111772, by rfl⟩ : syracuseStep 5482363 = 8223545) B8223545
theorem B7309817 : Blo 2165435 7309817 := bstep (se 2 (by rfl) ⟨2741181, by rfl⟩ : syracuseStep 7309817 = 5482363) B5482363
theorem B4873211 : Blo 2165435 4873211 := bstep (se 1 (by rfl) ⟨3654908, by rfl⟩ : syracuseStep 4873211 = 7309817) B7309817
theorem B3248807 : Blo 2165435 3248807 := bstep (se 1 (by rfl) ⟨2436605, by rfl⟩ : syracuseStep 3248807 = 4873211) B4873211
theorem B2165871 : Blo 2165435 2165871 := bstep (se 1 (by rfl) ⟨1624403, by rfl⟩ : syracuseStep 2165871 = 3248807) B3248807
theorem B3248813 : Blo 2165435 3248813 := bbase (se 3 (by rfl) ⟨609152, by rfl⟩ : syracuseStep 3248813 = 1218305) (by norm_num)
theorem B2165875 : Blo 2165435 2165875 := bstep (se 1 (by rfl) ⟨1624406, by rfl⟩ : syracuseStep 2165875 = 3248813) B3248813
theorem B4873229 : Blo 2165435 4873229 := bbase (se 3 (by rfl) ⟨913730, by rfl⟩ : syracuseStep 4873229 = 1827461) (by norm_num)
theorem B3248819 : Blo 2165435 3248819 := bstep (se 1 (by rfl) ⟨2436614, by rfl⟩ : syracuseStep 3248819 = 4873229) B4873229
theorem B2165879 : Blo 2165435 2165879 := bstep (se 1 (by rfl) ⟨1624409, by rfl⟩ : syracuseStep 2165879 = 3248819) B3248819
theorem B2741197 : Blo 2165435 2741197 := bbase (se 3 (by rfl) ⟨513974, by rfl⟩ : syracuseStep 2741197 = 1027949) (by norm_num)
theorem B3654929 : Blo 2165435 3654929 := bstep (se 2 (by rfl) ⟨1370598, by rfl⟩ : syracuseStep 3654929 = 2741197) B2741197
theorem B2436619 : Blo 2165435 2436619 := bstep (se 1 (by rfl) ⟨1827464, by rfl⟩ : syracuseStep 2436619 = 3654929) B3654929
theorem B3248825 : Blo 2165435 3248825 := bstep (se 2 (by rfl) ⟨1218309, by rfl⟩ : syracuseStep 3248825 = 2436619) B2436619
theorem B2165883 : Blo 2165435 2165883 := bstep (se 1 (by rfl) ⟨1624412, by rfl⟩ : syracuseStep 2165883 = 3248825) B3248825
theorem B5854501 : Blo 2165435 5854501 := bbase (se 4 (by rfl) ⟨548859, by rfl⟩ : syracuseStep 5854501 = 1097719) (by norm_num)
theorem B31224005 : Blo 2165435 31224005 := bstep (se 4 (by rfl) ⟨2927250, by rfl⟩ : syracuseStep 31224005 = 5854501) B5854501
theorem B20816003 : Blo 2165435 20816003 := bstep (se 1 (by rfl) ⟨15612002, by rfl⟩ : syracuseStep 20816003 = 31224005) B31224005
theorem B13877335 : Blo 2165435 13877335 := bstep (se 1 (by rfl) ⟨10408001, by rfl⟩ : syracuseStep 13877335 = 20816003) B20816003
theorem B18503113 : Blo 2165435 18503113 := bstep (se 2 (by rfl) ⟨6938667, by rfl⟩ : syracuseStep 18503113 = 13877335) B13877335
theorem B24670817 : Blo 2165435 24670817 := bstep (se 2 (by rfl) ⟨9251556, by rfl⟩ : syracuseStep 24670817 = 18503113) B18503113
theorem B16447211 : Blo 2165435 16447211 := bstep (se 1 (by rfl) ⟨12335408, by rfl⟩ : syracuseStep 16447211 = 24670817) B24670817
theorem B10964807 : Blo 2165435 10964807 := bstep (se 1 (by rfl) ⟨8223605, by rfl⟩ : syracuseStep 10964807 = 16447211) B16447211
theorem B7309871 : Blo 2165435 7309871 := bstep (se 1 (by rfl) ⟨5482403, by rfl⟩ : syracuseStep 7309871 = 10964807) B10964807
theorem B4873247 : Blo 2165435 4873247 := bstep (se 1 (by rfl) ⟨3654935, by rfl⟩ : syracuseStep 4873247 = 7309871) B7309871
theorem B3248831 : Blo 2165435 3248831 := bstep (se 1 (by rfl) ⟨2436623, by rfl⟩ : syracuseStep 3248831 = 4873247) B4873247
theorem B2165887 : Blo 2165435 2165887 := bstep (se 1 (by rfl) ⟨1624415, by rfl⟩ : syracuseStep 2165887 = 3248831) B3248831
theorem B3248837 : Blo 2165435 3248837 := bbase (se 4 (by rfl) ⟨304578, by rfl⟩ : syracuseStep 3248837 = 609157) (by norm_num)
theorem B2165891 : Blo 2165435 2165891 := bstep (se 1 (by rfl) ⟨1624418, by rfl⟩ : syracuseStep 2165891 = 3248837) B3248837
theorem B3654949 : Blo 2165435 3654949 := bbase (se 4 (by rfl) ⟨342651, by rfl⟩ : syracuseStep 3654949 = 685303) (by norm_num)
theorem B4873265 : Blo 2165435 4873265 := bstep (se 2 (by rfl) ⟨1827474, by rfl⟩ : syracuseStep 4873265 = 3654949) B3654949
theorem B3248843 : Blo 2165435 3248843 := bstep (se 1 (by rfl) ⟨2436632, by rfl⟩ : syracuseStep 3248843 = 4873265) B4873265
theorem B2165895 : Blo 2165435 2165895 := bstep (se 1 (by rfl) ⟨1624421, by rfl⟩ : syracuseStep 2165895 = 3248843) B3248843
theorem B2436637 : Blo 2165435 2436637 := bbase (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) (by norm_num)
theorem B3248849 : Blo 2165435 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B2165899 : Blo 2165435 2165899 := bstep (se 1 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 2165899 = 3248849) B3248849
theorem B7309925 : Blo 2165435 7309925 := bbase (se 4 (by rfl) ⟨685305, by rfl⟩ : syracuseStep 7309925 = 1370611) (by norm_num)
theorem B4873283 : Blo 2165435 4873283 := bstep (se 1 (by rfl) ⟨3654962, by rfl⟩ : syracuseStep 4873283 = 7309925) B7309925
theorem B3248855 : Blo 2165435 3248855 := bstep (se 1 (by rfl) ⟨2436641, by rfl⟩ : syracuseStep 3248855 = 4873283) B4873283
theorem B2165903 : Blo 2165435 2165903 := bstep (se 1 (by rfl) ⟨1624427, by rfl⟩ : syracuseStep 2165903 = 3248855) B3248855
theorem B3248861 : Blo 2165435 3248861 := bbase (se 3 (by rfl) ⟨609161, by rfl⟩ : syracuseStep 3248861 = 1218323) (by norm_num)
theorem B2165907 : Blo 2165435 2165907 := bstep (se 1 (by rfl) ⟨1624430, by rfl⟩ : syracuseStep 2165907 = 3248861) B3248861
theorem B4873301 : Blo 2165435 4873301 := bbase (se 8 (by rfl) ⟨28554, by rfl⟩ : syracuseStep 4873301 = 57109) (by norm_num)
theorem B3248867 : Blo 2165435 3248867 := bstep (se 1 (by rfl) ⟨2436650, by rfl⟩ : syracuseStep 3248867 = 4873301) B4873301
theorem B2165911 : Blo 2165435 2165911 := bstep (se 1 (by rfl) ⟨1624433, by rfl⟩ : syracuseStep 2165911 = 3248867) B3248867
theorem B2469901 : Blo 2165435 2469901 := bbase (se 3 (by rfl) ⟨463106, by rfl⟩ : syracuseStep 2469901 = 926213) (by norm_num)
theorem B3293201 : Blo 2165435 3293201 := bstep (se 2 (by rfl) ⟨1234950, by rfl⟩ : syracuseStep 3293201 = 2469901) B2469901
theorem B2195467 : Blo 2165435 2195467 := bstep (se 1 (by rfl) ⟨1646600, by rfl⟩ : syracuseStep 2195467 = 3293201) B3293201
theorem B11709157 : Blo 2165435 11709157 := bstep (se 4 (by rfl) ⟨1097733, by rfl⟩ : syracuseStep 11709157 = 2195467) B2195467
theorem B15612209 : Blo 2165435 15612209 := bstep (se 2 (by rfl) ⟨5854578, by rfl⟩ : syracuseStep 15612209 = 11709157) B11709157
theorem B10408139 : Blo 2165435 10408139 := bstep (se 1 (by rfl) ⟨7806104, by rfl⟩ : syracuseStep 10408139 = 15612209) B15612209
theorem B6938759 : Blo 2165435 6938759 := bstep (se 1 (by rfl) ⟨5204069, by rfl⟩ : syracuseStep 6938759 = 10408139) B10408139
theorem B4625839 : Blo 2165435 4625839 := bstep (se 1 (by rfl) ⟨3469379, by rfl⟩ : syracuseStep 4625839 = 6938759) B6938759
theorem B6167785 : Blo 2165435 6167785 := bstep (se 2 (by rfl) ⟨2312919, by rfl⟩ : syracuseStep 6167785 = 4625839) B4625839
theorem B8223713 : Blo 2165435 8223713 := bstep (se 2 (by rfl) ⟨3083892, by rfl⟩ : syracuseStep 8223713 = 6167785) B6167785
theorem B5482475 : Blo 2165435 5482475 := bstep (se 1 (by rfl) ⟨4111856, by rfl⟩ : syracuseStep 5482475 = 8223713) B8223713
theorem B3654983 : Blo 2165435 3654983 := bstep (se 1 (by rfl) ⟨2741237, by rfl⟩ : syracuseStep 3654983 = 5482475) B5482475
theorem B2436655 : Blo 2165435 2436655 := bstep (se 1 (by rfl) ⟨1827491, by rfl⟩ : syracuseStep 2436655 = 3654983) B3654983
theorem B3248873 : Blo 2165435 3248873 := bstep (se 2 (by rfl) ⟨1218327, by rfl⟩ : syracuseStep 3248873 = 2436655) B2436655
theorem B2165915 : Blo 2165435 2165915 := bstep (se 1 (by rfl) ⟨1624436, by rfl⟩ : syracuseStep 2165915 = 3248873) B3248873
theorem B5557285 : Blo 2165435 5557285 := bbase (se 4 (by rfl) ⟨520995, by rfl⟩ : syracuseStep 5557285 = 1041991) (by norm_num)
theorem B7409713 : Blo 2165435 7409713 := bstep (se 2 (by rfl) ⟨2778642, by rfl⟩ : syracuseStep 7409713 = 5557285) B5557285
theorem B9879617 : Blo 2165435 9879617 := bstep (se 2 (by rfl) ⟨3704856, by rfl⟩ : syracuseStep 9879617 = 7409713) B7409713
theorem B26345645 : Blo 2165435 26345645 := bstep (se 3 (by rfl) ⟨4939808, by rfl⟩ : syracuseStep 26345645 = 9879617) B9879617
theorem B17563763 : Blo 2165435 17563763 := bstep (se 1 (by rfl) ⟨13172822, by rfl⟩ : syracuseStep 17563763 = 26345645) B26345645
theorem B46836701 : Blo 2165435 46836701 := bstep (se 3 (by rfl) ⟨8781881, by rfl⟩ : syracuseStep 46836701 = 17563763) B17563763
theorem B31224467 : Blo 2165435 31224467 := bstep (se 1 (by rfl) ⟨23418350, by rfl⟩ : syracuseStep 31224467 = 46836701) B46836701
theorem B20816311 : Blo 2165435 20816311 := bstep (se 1 (by rfl) ⟨15612233, by rfl⟩ : syracuseStep 20816311 = 31224467) B31224467
theorem B27755081 : Blo 2165435 27755081 := bstep (se 2 (by rfl) ⟨10408155, by rfl⟩ : syracuseStep 27755081 = 20816311) B20816311
theorem B18503387 : Blo 2165435 18503387 := bstep (se 1 (by rfl) ⟨13877540, by rfl⟩ : syracuseStep 18503387 = 27755081) B27755081
theorem B12335591 : Blo 2165435 12335591 := bstep (se 1 (by rfl) ⟨9251693, by rfl⟩ : syracuseStep 12335591 = 18503387) B18503387
theorem B8223727 : Blo 2165435 8223727 := bstep (se 1 (by rfl) ⟨6167795, by rfl⟩ : syracuseStep 8223727 = 12335591) B12335591
theorem B10964969 : Blo 2165435 10964969 := bstep (se 2 (by rfl) ⟨4111863, by rfl⟩ : syracuseStep 10964969 = 8223727) B8223727
theorem B7309979 : Blo 2165435 7309979 := bstep (se 1 (by rfl) ⟨5482484, by rfl⟩ : syracuseStep 7309979 = 10964969) B10964969
theorem B4873319 : Blo 2165435 4873319 := bstep (se 1 (by rfl) ⟨3654989, by rfl⟩ : syracuseStep 4873319 = 7309979) B7309979
theorem B3248879 : Blo 2165435 3248879 := bstep (se 1 (by rfl) ⟨2436659, by rfl⟩ : syracuseStep 3248879 = 4873319) B4873319
theorem B2165919 : Blo 2165435 2165919 := bstep (se 1 (by rfl) ⟨1624439, by rfl⟩ : syracuseStep 2165919 = 3248879) B3248879
theorem B3248885 : Blo 2165435 3248885 := bbase (se 5 (by rfl) ⟨152291, by rfl⟩ : syracuseStep 3248885 = 304583) (by norm_num)
theorem B2165923 : Blo 2165435 2165923 := bstep (se 1 (by rfl) ⟨1624442, by rfl⟩ : syracuseStep 2165923 = 3248885) B3248885
theorem B2602049 : Blo 2165435 2602049 := bbase (se 2 (by rfl) ⟨975768, by rfl⟩ : syracuseStep 2602049 = 1951537) (by norm_num)
theorem B6938797 : Blo 2165435 6938797 := bstep (se 3 (by rfl) ⟨1301024, by rfl⟩ : syracuseStep 6938797 = 2602049) B2602049
theorem B9251729 : Blo 2165435 9251729 := bstep (se 2 (by rfl) ⟨3469398, by rfl⟩ : syracuseStep 9251729 = 6938797) B6938797
theorem B6167819 : Blo 2165435 6167819 := bstep (se 1 (by rfl) ⟨4625864, by rfl⟩ : syracuseStep 6167819 = 9251729) B9251729
theorem B4111879 : Blo 2165435 4111879 := bstep (se 1 (by rfl) ⟨3083909, by rfl⟩ : syracuseStep 4111879 = 6167819) B6167819
theorem B5482505 : Blo 2165435 5482505 := bstep (se 2 (by rfl) ⟨2055939, by rfl⟩ : syracuseStep 5482505 = 4111879) B4111879
theorem B3655003 : Blo 2165435 3655003 := bstep (se 1 (by rfl) ⟨2741252, by rfl⟩ : syracuseStep 3655003 = 5482505) B5482505
theorem B4873337 : Blo 2165435 4873337 := bstep (se 2 (by rfl) ⟨1827501, by rfl⟩ : syracuseStep 4873337 = 3655003) B3655003
theorem B3248891 : Blo 2165435 3248891 := bstep (se 1 (by rfl) ⟨2436668, by rfl⟩ : syracuseStep 3248891 = 4873337) B4873337
theorem B2165927 : Blo 2165435 2165927 := bstep (se 1 (by rfl) ⟨1624445, by rfl⟩ : syracuseStep 2165927 = 3248891) B3248891
theorem B2436673 : Blo 2165435 2436673 := bbase (se 2 (by rfl) ⟨913752, by rfl⟩ : syracuseStep 2436673 = 1827505) (by norm_num)
theorem B3248897 : Blo 2165435 3248897 := bstep (se 2 (by rfl) ⟨1218336, by rfl⟩ : syracuseStep 3248897 = 2436673) B2436673
theorem B2165931 : Blo 2165435 2165931 := bstep (se 1 (by rfl) ⟨1624448, by rfl⟩ : syracuseStep 2165931 = 3248897) B3248897
theorem B5482525 : Blo 2165435 5482525 := bbase (se 3 (by rfl) ⟨1027973, by rfl⟩ : syracuseStep 5482525 = 2055947) (by norm_num)
theorem B7310033 : Blo 2165435 7310033 := bstep (se 2 (by rfl) ⟨2741262, by rfl⟩ : syracuseStep 7310033 = 5482525) B5482525
theorem B4873355 : Blo 2165435 4873355 := bstep (se 1 (by rfl) ⟨3655016, by rfl⟩ : syracuseStep 4873355 = 7310033) B7310033
theorem B3248903 : Blo 2165435 3248903 := bstep (se 1 (by rfl) ⟨2436677, by rfl⟩ : syracuseStep 3248903 = 4873355) B4873355
theorem B2165935 : Blo 2165435 2165935 := bstep (se 1 (by rfl) ⟨1624451, by rfl⟩ : syracuseStep 2165935 = 3248903) B3248903
theorem B3248909 : Blo 2165435 3248909 := bbase (se 3 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 3248909 = 1218341) (by norm_num)
theorem B2165939 : Blo 2165435 2165939 := bstep (se 1 (by rfl) ⟨1624454, by rfl⟩ : syracuseStep 2165939 = 3248909) B3248909
theorem B4873373 : Blo 2165435 4873373 := bbase (se 3 (by rfl) ⟨913757, by rfl⟩ : syracuseStep 4873373 = 1827515) (by norm_num)
theorem B3248915 : Blo 2165435 3248915 := bstep (se 1 (by rfl) ⟨2436686, by rfl⟩ : syracuseStep 3248915 = 4873373) B4873373
theorem B2165943 : Blo 2165435 2165943 := bstep (se 1 (by rfl) ⟨1624457, by rfl⟩ : syracuseStep 2165943 = 3248915) B3248915
theorem B3655037 : Blo 2165435 3655037 := bbase (se 3 (by rfl) ⟨685319, by rfl⟩ : syracuseStep 3655037 = 1370639) (by norm_num)
theorem B2436691 : Blo 2165435 2436691 := bstep (se 1 (by rfl) ⟨1827518, by rfl⟩ : syracuseStep 2436691 = 3655037) B3655037
theorem B3248921 : Blo 2165435 3248921 := bstep (se 2 (by rfl) ⟨1218345, by rfl⟩ : syracuseStep 3248921 = 2436691) B2436691
theorem B2165947 : Blo 2165435 2165947 := bstep (se 1 (by rfl) ⟨1624460, by rfl⟩ : syracuseStep 2165947 = 3248921) B3248921
theorem B7912741 : Blo 2165435 7912741 := bbase (se 4 (by rfl) ⟨741819, by rfl⟩ : syracuseStep 7912741 = 1483639) (by norm_num)
theorem B10550321 : Blo 2165435 10550321 := bstep (se 2 (by rfl) ⟨3956370, by rfl⟩ : syracuseStep 10550321 = 7912741) B7912741
theorem B7033547 : Blo 2165435 7033547 := bstep (se 1 (by rfl) ⟨5275160, by rfl⟩ : syracuseStep 7033547 = 10550321) B10550321
theorem B4689031 : Blo 2165435 4689031 := bstep (se 1 (by rfl) ⟨3516773, by rfl⟩ : syracuseStep 4689031 = 7033547) B7033547
theorem B6252041 : Blo 2165435 6252041 := bstep (se 2 (by rfl) ⟨2344515, by rfl⟩ : syracuseStep 6252041 = 4689031) B4689031
theorem B4168027 : Blo 2165435 4168027 := bstep (se 1 (by rfl) ⟨3126020, by rfl⟩ : syracuseStep 4168027 = 6252041) B6252041
theorem B5557369 : Blo 2165435 5557369 := bstep (se 2 (by rfl) ⟨2084013, by rfl⟩ : syracuseStep 5557369 = 4168027) B4168027
theorem B7409825 : Blo 2165435 7409825 := bstep (se 2 (by rfl) ⟨2778684, by rfl⟩ : syracuseStep 7409825 = 5557369) B5557369
theorem B4939883 : Blo 2165435 4939883 := bstep (se 1 (by rfl) ⟨3704912, by rfl⟩ : syracuseStep 4939883 = 7409825) B7409825
theorem B3293255 : Blo 2165435 3293255 := bstep (se 1 (by rfl) ⟨2469941, by rfl⟩ : syracuseStep 3293255 = 4939883) B4939883
theorem B8782013 : Blo 2165435 8782013 := bstep (se 3 (by rfl) ⟨1646627, by rfl⟩ : syracuseStep 8782013 = 3293255) B3293255
theorem B5854675 : Blo 2165435 5854675 := bstep (se 1 (by rfl) ⟨4391006, by rfl⟩ : syracuseStep 5854675 = 8782013) B8782013
theorem B7806233 : Blo 2165435 7806233 := bstep (se 2 (by rfl) ⟨2927337, by rfl⟩ : syracuseStep 7806233 = 5854675) B5854675
theorem B5204155 : Blo 2165435 5204155 := bstep (se 1 (by rfl) ⟨3903116, by rfl⟩ : syracuseStep 5204155 = 7806233) B7806233
theorem B6938873 : Blo 2165435 6938873 := bstep (se 2 (by rfl) ⟨2602077, by rfl⟩ : syracuseStep 6938873 = 5204155) B5204155
theorem B4625915 : Blo 2165435 4625915 := bstep (se 1 (by rfl) ⟨3469436, by rfl⟩ : syracuseStep 4625915 = 6938873) B6938873
theorem B12335773 : Blo 2165435 12335773 := bstep (se 3 (by rfl) ⟨2312957, by rfl⟩ : syracuseStep 12335773 = 4625915) B4625915
theorem B16447697 : Blo 2165435 16447697 := bstep (se 2 (by rfl) ⟨6167886, by rfl⟩ : syracuseStep 16447697 = 12335773) B12335773
theorem B10965131 : Blo 2165435 10965131 := bstep (se 1 (by rfl) ⟨8223848, by rfl⟩ : syracuseStep 10965131 = 16447697) B16447697
theorem B7310087 : Blo 2165435 7310087 := bstep (se 1 (by rfl) ⟨5482565, by rfl⟩ : syracuseStep 7310087 = 10965131) B10965131
theorem B4873391 : Blo 2165435 4873391 := bstep (se 1 (by rfl) ⟨3655043, by rfl⟩ : syracuseStep 4873391 = 7310087) B7310087
theorem B3248927 : Blo 2165435 3248927 := bstep (se 1 (by rfl) ⟨2436695, by rfl⟩ : syracuseStep 3248927 = 4873391) B4873391
theorem B2165951 : Blo 2165435 2165951 := bstep (se 1 (by rfl) ⟨1624463, by rfl⟩ : syracuseStep 2165951 = 3248927) B3248927
theorem B3248933 : Blo 2165435 3248933 := bbase (se 4 (by rfl) ⟨304587, by rfl⟩ : syracuseStep 3248933 = 609175) (by norm_num)
theorem B2165955 : Blo 2165435 2165955 := bstep (se 1 (by rfl) ⟨1624466, by rfl⟩ : syracuseStep 2165955 = 3248933) B3248933
theorem B2741293 : Blo 2165435 2741293 := bbase (se 3 (by rfl) ⟨513992, by rfl⟩ : syracuseStep 2741293 = 1027985) (by norm_num)
theorem B3655057 : Blo 2165435 3655057 := bstep (se 2 (by rfl) ⟨1370646, by rfl⟩ : syracuseStep 3655057 = 2741293) B2741293
theorem B4873409 : Blo 2165435 4873409 := bstep (se 2 (by rfl) ⟨1827528, by rfl⟩ : syracuseStep 4873409 = 3655057) B3655057
theorem B3248939 : Blo 2165435 3248939 := bstep (se 1 (by rfl) ⟨2436704, by rfl⟩ : syracuseStep 3248939 = 4873409) B4873409
theorem B2165959 : Blo 2165435 2165959 := bstep (se 1 (by rfl) ⟨1624469, by rfl⟩ : syracuseStep 2165959 = 3248939) B3248939
theorem B2436709 : Blo 2165435 2436709 := bbase (se 4 (by rfl) ⟨228441, by rfl⟩ : syracuseStep 2436709 = 456883) (by norm_num)
theorem B3248945 : Blo 2165435 3248945 := bstep (se 2 (by rfl) ⟨1218354, by rfl⟩ : syracuseStep 3248945 = 2436709) B2436709
theorem B2165963 : Blo 2165435 2165963 := bstep (se 1 (by rfl) ⟨1624472, by rfl⟩ : syracuseStep 2165963 = 3248945) B3248945
theorem B7806293 : Blo 2165435 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B5204195 : Blo 2165435 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B3469463 : Blo 2165435 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B2312975 : Blo 2165435 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B6167933 : Blo 2165435 6167933 := bstep (se 3 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 6167933 = 2312975) B2312975
theorem B4111955 : Blo 2165435 4111955 := bstep (se 1 (by rfl) ⟨3083966, by rfl⟩ : syracuseStep 4111955 = 6167933) B6167933
theorem B2741303 : Blo 2165435 2741303 := bstep (se 1 (by rfl) ⟨2055977, by rfl⟩ : syracuseStep 2741303 = 4111955) B4111955
theorem B7310141 : Blo 2165435 7310141 := bstep (se 3 (by rfl) ⟨1370651, by rfl⟩ : syracuseStep 7310141 = 2741303) B2741303
theorem B4873427 : Blo 2165435 4873427 := bstep (se 1 (by rfl) ⟨3655070, by rfl⟩ : syracuseStep 4873427 = 7310141) B7310141
theorem B3248951 : Blo 2165435 3248951 := bstep (se 1 (by rfl) ⟨2436713, by rfl⟩ : syracuseStep 3248951 = 4873427) B4873427
theorem B2165967 : Blo 2165435 2165967 := bstep (se 1 (by rfl) ⟨1624475, by rfl⟩ : syracuseStep 2165967 = 3248951) B3248951
theorem B3248957 : Blo 2165435 3248957 := bbase (se 3 (by rfl) ⟨609179, by rfl⟩ : syracuseStep 3248957 = 1218359) (by norm_num)
theorem B2165971 : Blo 2165435 2165971 := bstep (se 1 (by rfl) ⟨1624478, by rfl⟩ : syracuseStep 2165971 = 3248957) B3248957
theorem B4873445 : Blo 2165435 4873445 := bbase (se 4 (by rfl) ⟨456885, by rfl⟩ : syracuseStep 4873445 = 913771) (by norm_num)
theorem B3248963 : Blo 2165435 3248963 := bstep (se 1 (by rfl) ⟨2436722, by rfl⟩ : syracuseStep 3248963 = 4873445) B4873445
theorem B2165975 : Blo 2165435 2165975 := bstep (se 1 (by rfl) ⟨1624481, by rfl⟩ : syracuseStep 2165975 = 3248963) B3248963
theorem B5482637 : Blo 2165435 5482637 := bbase (se 3 (by rfl) ⟨1027994, by rfl⟩ : syracuseStep 5482637 = 2055989) (by norm_num)
theorem B3655091 : Blo 2165435 3655091 := bstep (se 1 (by rfl) ⟨2741318, by rfl⟩ : syracuseStep 3655091 = 5482637) B5482637
theorem B2436727 : Blo 2165435 2436727 := bstep (se 1 (by rfl) ⟨1827545, by rfl⟩ : syracuseStep 2436727 = 3655091) B3655091
theorem B3248969 : Blo 2165435 3248969 := bstep (se 2 (by rfl) ⟨1218363, by rfl⟩ : syracuseStep 3248969 = 2436727) B2436727
theorem B2165979 : Blo 2165435 2165979 := bstep (se 1 (by rfl) ⟨1624484, by rfl⟩ : syracuseStep 2165979 = 3248969) B3248969
theorem B3083989 : Blo 2165435 3083989 := bbase (se 7 (by rfl) ⟨36140, by rfl⟩ : syracuseStep 3083989 = 72281) (by norm_num)
theorem B4111985 : Blo 2165435 4111985 := bstep (se 2 (by rfl) ⟨1541994, by rfl⟩ : syracuseStep 4111985 = 3083989) B3083989
theorem B10965293 : Blo 2165435 10965293 := bstep (se 3 (by rfl) ⟨2055992, by rfl⟩ : syracuseStep 10965293 = 4111985) B4111985
theorem B7310195 : Blo 2165435 7310195 := bstep (se 1 (by rfl) ⟨5482646, by rfl⟩ : syracuseStep 7310195 = 10965293) B10965293
theorem B4873463 : Blo 2165435 4873463 := bstep (se 1 (by rfl) ⟨3655097, by rfl⟩ : syracuseStep 4873463 = 7310195) B7310195
theorem B3248975 : Blo 2165435 3248975 := bstep (se 1 (by rfl) ⟨2436731, by rfl⟩ : syracuseStep 3248975 = 4873463) B4873463
theorem B2165983 : Blo 2165435 2165983 := bstep (se 1 (by rfl) ⟨1624487, by rfl⟩ : syracuseStep 2165983 = 3248975) B3248975
theorem B3248981 : Blo 2165435 3248981 := bbase (se 9 (by rfl) ⟨9518, by rfl⟩ : syracuseStep 3248981 = 19037) (by norm_num)
theorem B2165987 : Blo 2165435 2165987 := bstep (se 1 (by rfl) ⟨1624490, by rfl⟩ : syracuseStep 2165987 = 3248981) B3248981
theorem B3469501 : Blo 2165435 3469501 := bbase (se 3 (by rfl) ⟨650531, by rfl⟩ : syracuseStep 3469501 = 1301063) (by norm_num)
theorem B4626001 : Blo 2165435 4626001 := bstep (se 2 (by rfl) ⟨1734750, by rfl⟩ : syracuseStep 4626001 = 3469501) B3469501
theorem B6168001 : Blo 2165435 6168001 := bstep (se 2 (by rfl) ⟨2313000, by rfl⟩ : syracuseStep 6168001 = 4626001) B4626001
theorem B8224001 : Blo 2165435 8224001 := bstep (se 2 (by rfl) ⟨3084000, by rfl⟩ : syracuseStep 8224001 = 6168001) B6168001
theorem B5482667 : Blo 2165435 5482667 := bstep (se 1 (by rfl) ⟨4112000, by rfl⟩ : syracuseStep 5482667 = 8224001) B8224001
theorem B3655111 : Blo 2165435 3655111 := bstep (se 1 (by rfl) ⟨2741333, by rfl⟩ : syracuseStep 3655111 = 5482667) B5482667
theorem B4873481 : Blo 2165435 4873481 := bstep (se 2 (by rfl) ⟨1827555, by rfl⟩ : syracuseStep 4873481 = 3655111) B3655111
theorem B3248987 : Blo 2165435 3248987 := bstep (se 1 (by rfl) ⟨2436740, by rfl⟩ : syracuseStep 3248987 = 4873481) B4873481
theorem B2165991 : Blo 2165435 2165991 := bstep (se 1 (by rfl) ⟨1624493, by rfl⟩ : syracuseStep 2165991 = 3248987) B3248987
theorem B2436745 : Blo 2165435 2436745 := bbase (se 2 (by rfl) ⟨913779, by rfl⟩ : syracuseStep 2436745 = 1827559) (by norm_num)
theorem B3248993 : Blo 2165435 3248993 := bstep (se 2 (by rfl) ⟨1218372, by rfl⟩ : syracuseStep 3248993 = 2436745) B2436745
theorem B2165995 : Blo 2165435 2165995 := bstep (se 1 (by rfl) ⟨1624496, by rfl⟩ : syracuseStep 2165995 = 3248993) B3248993
theorem B31225621 : Blo 2165435 31225621 := bbase (se 6 (by rfl) ⟨731850, by rfl⟩ : syracuseStep 31225621 = 1463701) (by norm_num)
theorem B41634161 : Blo 2165435 41634161 := bstep (se 2 (by rfl) ⟨15612810, by rfl⟩ : syracuseStep 41634161 = 31225621) B31225621
theorem B27756107 : Blo 2165435 27756107 := bstep (se 1 (by rfl) ⟨20817080, by rfl⟩ : syracuseStep 27756107 = 41634161) B41634161
theorem B18504071 : Blo 2165435 18504071 := bstep (se 1 (by rfl) ⟨13878053, by rfl⟩ : syracuseStep 18504071 = 27756107) B27756107
theorem B12336047 : Blo 2165435 12336047 := bstep (se 1 (by rfl) ⟨9252035, by rfl⟩ : syracuseStep 12336047 = 18504071) B18504071
theorem B8224031 : Blo 2165435 8224031 := bstep (se 1 (by rfl) ⟨6168023, by rfl⟩ : syracuseStep 8224031 = 12336047) B12336047
theorem B5482687 : Blo 2165435 5482687 := bstep (se 1 (by rfl) ⟨4112015, by rfl⟩ : syracuseStep 5482687 = 8224031) B8224031
theorem B7310249 : Blo 2165435 7310249 := bstep (se 2 (by rfl) ⟨2741343, by rfl⟩ : syracuseStep 7310249 = 5482687) B5482687
theorem B4873499 : Blo 2165435 4873499 := bstep (se 1 (by rfl) ⟨3655124, by rfl⟩ : syracuseStep 4873499 = 7310249) B7310249
theorem B3248999 : Blo 2165435 3248999 := bstep (se 1 (by rfl) ⟨2436749, by rfl⟩ : syracuseStep 3248999 = 4873499) B4873499
theorem B2165999 : Blo 2165435 2165999 := bstep (se 1 (by rfl) ⟨1624499, by rfl⟩ : syracuseStep 2165999 = 3248999) B3248999
theorem B3249005 : Blo 2165435 3249005 := bbase (se 3 (by rfl) ⟨609188, by rfl⟩ : syracuseStep 3249005 = 1218377) (by norm_num)
theorem B2166003 : Blo 2165435 2166003 := bstep (se 1 (by rfl) ⟨1624502, by rfl⟩ : syracuseStep 2166003 = 3249005) B3249005
theorem B4873517 : Blo 2165435 4873517 := bbase (se 3 (by rfl) ⟨913784, by rfl⟩ : syracuseStep 4873517 = 1827569) (by norm_num)
theorem B3249011 : Blo 2165435 3249011 := bstep (se 1 (by rfl) ⟨2436758, by rfl⟩ : syracuseStep 3249011 = 4873517) B4873517
theorem B2166007 : Blo 2165435 2166007 := bstep (se 1 (by rfl) ⟨1624505, by rfl⟩ : syracuseStep 2166007 = 3249011) B3249011
theorem B4940021 : Blo 2165435 4940021 := bbase (se 5 (by rfl) ⟨231563, by rfl⟩ : syracuseStep 4940021 = 463127) (by norm_num)
theorem B3293347 : Blo 2165435 3293347 := bstep (se 1 (by rfl) ⟨2470010, by rfl⟩ : syracuseStep 3293347 = 4940021) B4940021
theorem B4391129 : Blo 2165435 4391129 := bstep (se 2 (by rfl) ⟨1646673, by rfl⟩ : syracuseStep 4391129 = 3293347) B3293347
theorem B11709677 : Blo 2165435 11709677 := bstep (se 3 (by rfl) ⟨2195564, by rfl⟩ : syracuseStep 11709677 = 4391129) B4391129
theorem B7806451 : Blo 2165435 7806451 := bstep (se 1 (by rfl) ⟨5854838, by rfl⟩ : syracuseStep 7806451 = 11709677) B11709677
theorem B10408601 : Blo 2165435 10408601 := bstep (se 2 (by rfl) ⟨3903225, by rfl⟩ : syracuseStep 10408601 = 7806451) B7806451
theorem B6939067 : Blo 2165435 6939067 := bstep (se 1 (by rfl) ⟨5204300, by rfl⟩ : syracuseStep 6939067 = 10408601) B10408601
theorem B9252089 : Blo 2165435 9252089 := bstep (se 2 (by rfl) ⟨3469533, by rfl⟩ : syracuseStep 9252089 = 6939067) B6939067
theorem B6168059 : Blo 2165435 6168059 := bstep (se 1 (by rfl) ⟨4626044, by rfl⟩ : syracuseStep 6168059 = 9252089) B9252089
theorem B4112039 : Blo 2165435 4112039 := bstep (se 1 (by rfl) ⟨3084029, by rfl⟩ : syracuseStep 4112039 = 6168059) B6168059
theorem B2741359 : Blo 2165435 2741359 := bstep (se 1 (by rfl) ⟨2056019, by rfl⟩ : syracuseStep 2741359 = 4112039) B4112039
theorem B3655145 : Blo 2165435 3655145 := bstep (se 2 (by rfl) ⟨1370679, by rfl⟩ : syracuseStep 3655145 = 2741359) B2741359
theorem B2436763 : Blo 2165435 2436763 := bstep (se 1 (by rfl) ⟨1827572, by rfl⟩ : syracuseStep 2436763 = 3655145) B3655145
theorem B3249017 : Blo 2165435 3249017 := bstep (se 2 (by rfl) ⟨1218381, by rfl⟩ : syracuseStep 3249017 = 2436763) B2436763
theorem B2166011 : Blo 2165435 2166011 := bstep (se 1 (by rfl) ⟨1624508, by rfl⟩ : syracuseStep 2166011 = 3249017) B3249017
theorem B7613621 : Blo 2165435 7613621 := bbase (se 5 (by rfl) ⟨356888, by rfl⟩ : syracuseStep 7613621 = 713777) (by norm_num)
theorem B5075747 : Blo 2165435 5075747 := bstep (se 1 (by rfl) ⟨3806810, by rfl⟩ : syracuseStep 5075747 = 7613621) B7613621
theorem B3383831 : Blo 2165435 3383831 := bstep (se 1 (by rfl) ⟨2537873, by rfl⟩ : syracuseStep 3383831 = 5075747) B5075747
theorem B2255887 : Blo 2165435 2255887 := bstep (se 1 (by rfl) ⟨1691915, by rfl⟩ : syracuseStep 2255887 = 3383831) B3383831
theorem B3007849 : Blo 2165435 3007849 := bstep (se 2 (by rfl) ⟨1127943, by rfl⟩ : syracuseStep 3007849 = 2255887) B2255887
theorem B4010465 : Blo 2165435 4010465 := bstep (se 2 (by rfl) ⟨1503924, by rfl⟩ : syracuseStep 4010465 = 3007849) B3007849
theorem B10694573 : Blo 2165435 10694573 := bstep (se 3 (by rfl) ⟨2005232, by rfl⟩ : syracuseStep 10694573 = 4010465) B4010465
theorem B7129715 : Blo 2165435 7129715 := bstep (se 1 (by rfl) ⟨5347286, by rfl⟩ : syracuseStep 7129715 = 10694573) B10694573
theorem B19012573 : Blo 2165435 19012573 := bstep (se 3 (by rfl) ⟨3564857, by rfl⟩ : syracuseStep 19012573 = 7129715) B7129715
theorem B25350097 : Blo 2165435 25350097 := bstep (se 2 (by rfl) ⟨9506286, by rfl⟩ : syracuseStep 25350097 = 19012573) B19012573
theorem B33800129 : Blo 2165435 33800129 := bstep (se 2 (by rfl) ⟨12675048, by rfl⟩ : syracuseStep 33800129 = 25350097) B25350097
theorem B22533419 : Blo 2165435 22533419 := bstep (se 1 (by rfl) ⟨16900064, by rfl⟩ : syracuseStep 22533419 = 33800129) B33800129
theorem B15022279 : Blo 2165435 15022279 := bstep (se 1 (by rfl) ⟨11266709, by rfl⟩ : syracuseStep 15022279 = 22533419) B22533419
theorem B80118821 : Blo 2165435 80118821 := bstep (se 4 (by rfl) ⟨7511139, by rfl⟩ : syracuseStep 80118821 = 15022279) B15022279
theorem B53412547 : Blo 2165435 53412547 := bstep (se 1 (by rfl) ⟨40059410, by rfl⟩ : syracuseStep 53412547 = 80118821) B80118821
theorem B71216729 : Blo 2165435 71216729 := bstep (se 2 (by rfl) ⟨26706273, by rfl⟩ : syracuseStep 71216729 = 53412547) B53412547
theorem B47477819 : Blo 2165435 47477819 := bstep (se 1 (by rfl) ⟨35608364, by rfl⟩ : syracuseStep 47477819 = 71216729) B71216729
theorem B31651879 : Blo 2165435 31651879 := bstep (se 1 (by rfl) ⟨23738909, by rfl⟩ : syracuseStep 31651879 = 47477819) B47477819
theorem B42202505 : Blo 2165435 42202505 := bstep (se 2 (by rfl) ⟨15825939, by rfl⟩ : syracuseStep 42202505 = 31651879) B31651879
theorem B112540013 : Blo 2165435 112540013 := bstep (se 3 (by rfl) ⟨21101252, by rfl⟩ : syracuseStep 112540013 = 42202505) B42202505
theorem B75026675 : Blo 2165435 75026675 := bstep (se 1 (by rfl) ⟨56270006, by rfl⟩ : syracuseStep 75026675 = 112540013) B112540013
theorem B50017783 : Blo 2165435 50017783 := bstep (se 1 (by rfl) ⟨37513337, by rfl⟩ : syracuseStep 50017783 = 75026675) B75026675
theorem B66690377 : Blo 2165435 66690377 := bstep (se 2 (by rfl) ⟨25008891, by rfl⟩ : syracuseStep 66690377 = 50017783) B50017783
theorem B44460251 : Blo 2165435 44460251 := bstep (se 1 (by rfl) ⟨33345188, by rfl⟩ : syracuseStep 44460251 = 66690377) B66690377
theorem B29640167 : Blo 2165435 29640167 := bstep (se 1 (by rfl) ⟨22230125, by rfl⟩ : syracuseStep 29640167 = 44460251) B44460251
theorem B19760111 : Blo 2165435 19760111 := bstep (se 1 (by rfl) ⟨14820083, by rfl⟩ : syracuseStep 19760111 = 29640167) B29640167
theorem B13173407 : Blo 2165435 13173407 := bstep (se 1 (by rfl) ⟨9880055, by rfl⟩ : syracuseStep 13173407 = 19760111) B19760111
theorem B8782271 : Blo 2165435 8782271 := bstep (se 1 (by rfl) ⟨6586703, by rfl⟩ : syracuseStep 8782271 = 13173407) B13173407
theorem B5854847 : Blo 2165435 5854847 := bstep (se 1 (by rfl) ⟨4391135, by rfl⟩ : syracuseStep 5854847 = 8782271) B8782271
theorem B15612925 : Blo 2165435 15612925 := bstep (se 3 (by rfl) ⟨2927423, by rfl⟩ : syracuseStep 15612925 = 5854847) B5854847
theorem B20817233 : Blo 2165435 20817233 := bstep (se 2 (by rfl) ⟨7806462, by rfl⟩ : syracuseStep 20817233 = 15612925) B15612925
theorem B13878155 : Blo 2165435 13878155 := bstep (se 1 (by rfl) ⟨10408616, by rfl⟩ : syracuseStep 13878155 = 20817233) B20817233
theorem B37008413 : Blo 2165435 37008413 := bstep (se 3 (by rfl) ⟨6939077, by rfl⟩ : syracuseStep 37008413 = 13878155) B13878155
theorem B24672275 : Blo 2165435 24672275 := bstep (se 1 (by rfl) ⟨18504206, by rfl⟩ : syracuseStep 24672275 = 37008413) B37008413
theorem B16448183 : Blo 2165435 16448183 := bstep (se 1 (by rfl) ⟨12336137, by rfl⟩ : syracuseStep 16448183 = 24672275) B24672275
theorem B10965455 : Blo 2165435 10965455 := bstep (se 1 (by rfl) ⟨8224091, by rfl⟩ : syracuseStep 10965455 = 16448183) B16448183
theorem B7310303 : Blo 2165435 7310303 := bstep (se 1 (by rfl) ⟨5482727, by rfl⟩ : syracuseStep 7310303 = 10965455) B10965455
theorem B4873535 : Blo 2165435 4873535 := bstep (se 1 (by rfl) ⟨3655151, by rfl⟩ : syracuseStep 4873535 = 7310303) B7310303
theorem B3249023 : Blo 2165435 3249023 := bstep (se 1 (by rfl) ⟨2436767, by rfl⟩ : syracuseStep 3249023 = 4873535) B4873535
theorem B2166015 : Blo 2165435 2166015 := bstep (se 1 (by rfl) ⟨1624511, by rfl⟩ : syracuseStep 2166015 = 3249023) B3249023
theorem B3249029 : Blo 2165435 3249029 := bbase (se 4 (by rfl) ⟨304596, by rfl⟩ : syracuseStep 3249029 = 609193) (by norm_num)
theorem B2166019 : Blo 2165435 2166019 := bstep (se 1 (by rfl) ⟨1624514, by rfl⟩ : syracuseStep 2166019 = 3249029) B3249029
theorem B3655165 : Blo 2165435 3655165 := bbase (se 3 (by rfl) ⟨685343, by rfl⟩ : syracuseStep 3655165 = 1370687) (by norm_num)
theorem B4873553 : Blo 2165435 4873553 := bstep (se 2 (by rfl) ⟨1827582, by rfl⟩ : syracuseStep 4873553 = 3655165) B3655165
theorem B3249035 : Blo 2165435 3249035 := bstep (se 1 (by rfl) ⟨2436776, by rfl⟩ : syracuseStep 3249035 = 4873553) B4873553
theorem B2166023 : Blo 2165435 2166023 := bstep (se 1 (by rfl) ⟨1624517, by rfl⟩ : syracuseStep 2166023 = 3249035) B3249035
theorem B2436781 : Blo 2165435 2436781 := bbase (se 3 (by rfl) ⟨456896, by rfl⟩ : syracuseStep 2436781 = 913793) (by norm_num)
theorem B3249041 : Blo 2165435 3249041 := bstep (se 2 (by rfl) ⟨1218390, by rfl⟩ : syracuseStep 3249041 = 2436781) B2436781
theorem B2166027 : Blo 2165435 2166027 := bstep (se 1 (by rfl) ⟨1624520, by rfl⟩ : syracuseStep 2166027 = 3249041) B3249041
theorem B7310357 : Blo 2165435 7310357 := bbase (se 6 (by rfl) ⟨171336, by rfl⟩ : syracuseStep 7310357 = 342673) (by norm_num)
theorem B4873571 : Blo 2165435 4873571 := bstep (se 1 (by rfl) ⟨3655178, by rfl⟩ : syracuseStep 4873571 = 7310357) B7310357
theorem B3249047 : Blo 2165435 3249047 := bstep (se 1 (by rfl) ⟨2436785, by rfl⟩ : syracuseStep 3249047 = 4873571) B4873571
theorem B2166031 : Blo 2165435 2166031 := bstep (se 1 (by rfl) ⟨1624523, by rfl⟩ : syracuseStep 2166031 = 3249047) B3249047
theorem B3249053 : Blo 2165435 3249053 := bbase (se 3 (by rfl) ⟨609197, by rfl⟩ : syracuseStep 3249053 = 1218395) (by norm_num)
theorem B2166035 : Blo 2165435 2166035 := bstep (se 1 (by rfl) ⟨1624526, by rfl⟩ : syracuseStep 2166035 = 3249053) B3249053
theorem B4873589 : Blo 2165435 4873589 := bbase (se 5 (by rfl) ⟨228449, by rfl⟩ : syracuseStep 4873589 = 456899) (by norm_num)
theorem B3249059 : Blo 2165435 3249059 := bstep (se 1 (by rfl) ⟨2436794, by rfl⟩ : syracuseStep 3249059 = 4873589) B4873589
theorem B2166039 : Blo 2165435 2166039 := bstep (se 1 (by rfl) ⟨1624529, by rfl⟩ : syracuseStep 2166039 = 3249059) B3249059
theorem B7806565 : Blo 2165435 7806565 := bbase (se 4 (by rfl) ⟨731865, by rfl⟩ : syracuseStep 7806565 = 1463731) (by norm_num)
theorem B10408753 : Blo 2165435 10408753 := bstep (se 2 (by rfl) ⟨3903282, by rfl⟩ : syracuseStep 10408753 = 7806565) B7806565
theorem B13878337 : Blo 2165435 13878337 := bstep (se 2 (by rfl) ⟨5204376, by rfl⟩ : syracuseStep 13878337 = 10408753) B10408753
theorem B18504449 : Blo 2165435 18504449 := bstep (se 2 (by rfl) ⟨6939168, by rfl⟩ : syracuseStep 18504449 = 13878337) B13878337
theorem B12336299 : Blo 2165435 12336299 := bstep (se 1 (by rfl) ⟨9252224, by rfl⟩ : syracuseStep 12336299 = 18504449) B18504449
theorem B8224199 : Blo 2165435 8224199 := bstep (se 1 (by rfl) ⟨6168149, by rfl⟩ : syracuseStep 8224199 = 12336299) B12336299
theorem B5482799 : Blo 2165435 5482799 := bstep (se 1 (by rfl) ⟨4112099, by rfl⟩ : syracuseStep 5482799 = 8224199) B8224199
theorem B3655199 : Blo 2165435 3655199 := bstep (se 1 (by rfl) ⟨2741399, by rfl⟩ : syracuseStep 3655199 = 5482799) B5482799
theorem B2436799 : Blo 2165435 2436799 := bstep (se 1 (by rfl) ⟨1827599, by rfl⟩ : syracuseStep 2436799 = 3655199) B3655199
theorem B3249065 : Blo 2165435 3249065 := bstep (se 2 (by rfl) ⟨1218399, by rfl⟩ : syracuseStep 3249065 = 2436799) B2436799
theorem B2166043 : Blo 2165435 2166043 := bstep (se 1 (by rfl) ⟨1624532, by rfl⟩ : syracuseStep 2166043 = 3249065) B3249065
theorem B8224213 : Blo 2165435 8224213 := bbase (se 7 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 8224213 = 192755) (by norm_num)
theorem B10965617 : Blo 2165435 10965617 := bstep (se 2 (by rfl) ⟨4112106, by rfl⟩ : syracuseStep 10965617 = 8224213) B8224213
theorem B7310411 : Blo 2165435 7310411 := bstep (se 1 (by rfl) ⟨5482808, by rfl⟩ : syracuseStep 7310411 = 10965617) B10965617
theorem B4873607 : Blo 2165435 4873607 := bstep (se 1 (by rfl) ⟨3655205, by rfl⟩ : syracuseStep 4873607 = 7310411) B7310411
theorem B3249071 : Blo 2165435 3249071 := bstep (se 1 (by rfl) ⟨2436803, by rfl⟩ : syracuseStep 3249071 = 4873607) B4873607
theorem B2166047 : Blo 2165435 2166047 := bstep (se 1 (by rfl) ⟨1624535, by rfl⟩ : syracuseStep 2166047 = 3249071) B3249071
theorem B3249077 : Blo 2165435 3249077 := bbase (se 5 (by rfl) ⟨152300, by rfl⟩ : syracuseStep 3249077 = 304601) (by norm_num)
theorem B2166051 : Blo 2165435 2166051 := bstep (se 1 (by rfl) ⟨1624538, by rfl⟩ : syracuseStep 2166051 = 3249077) B3249077
theorem B5482829 : Blo 2165435 5482829 := bbase (se 3 (by rfl) ⟨1028030, by rfl⟩ : syracuseStep 5482829 = 2056061) (by norm_num)
theorem B3655219 : Blo 2165435 3655219 := bstep (se 1 (by rfl) ⟨2741414, by rfl⟩ : syracuseStep 3655219 = 5482829) B5482829
theorem B4873625 : Blo 2165435 4873625 := bstep (se 2 (by rfl) ⟨1827609, by rfl⟩ : syracuseStep 4873625 = 3655219) B3655219
theorem B3249083 : Blo 2165435 3249083 := bstep (se 1 (by rfl) ⟨2436812, by rfl⟩ : syracuseStep 3249083 = 4873625) B4873625
theorem B2166055 : Blo 2165435 2166055 := bstep (se 1 (by rfl) ⟨1624541, by rfl⟩ : syracuseStep 2166055 = 3249083) B3249083
theorem B2436817 : Blo 2165435 2436817 := bbase (se 2 (by rfl) ⟨913806, by rfl⟩ : syracuseStep 2436817 = 1827613) (by norm_num)
theorem B3249089 : Blo 2165435 3249089 := bstep (se 2 (by rfl) ⟨1218408, by rfl⟩ : syracuseStep 3249089 = 2436817) B2436817
theorem B2166059 : Blo 2165435 2166059 := bstep (se 1 (by rfl) ⟨1624544, by rfl⟩ : syracuseStep 2166059 = 3249089) B3249089
theorem B8782469 : Blo 2165435 8782469 := bbase (se 4 (by rfl) ⟨823356, by rfl⟩ : syracuseStep 8782469 = 1646713) (by norm_num)
theorem B5854979 : Blo 2165435 5854979 := bstep (se 1 (by rfl) ⟨4391234, by rfl⟩ : syracuseStep 5854979 = 8782469) B8782469
theorem B3903319 : Blo 2165435 3903319 := bstep (se 1 (by rfl) ⟨2927489, by rfl⟩ : syracuseStep 3903319 = 5854979) B5854979
theorem B5204425 : Blo 2165435 5204425 := bstep (se 2 (by rfl) ⟨1951659, by rfl⟩ : syracuseStep 5204425 = 3903319) B3903319
theorem B6939233 : Blo 2165435 6939233 := bstep (se 2 (by rfl) ⟨2602212, by rfl⟩ : syracuseStep 6939233 = 5204425) B5204425
theorem B4626155 : Blo 2165435 4626155 := bstep (se 1 (by rfl) ⟨3469616, by rfl⟩ : syracuseStep 4626155 = 6939233) B6939233
theorem B3084103 : Blo 2165435 3084103 := bstep (se 1 (by rfl) ⟨2313077, by rfl⟩ : syracuseStep 3084103 = 4626155) B4626155
theorem B4112137 : Blo 2165435 4112137 := bstep (se 2 (by rfl) ⟨1542051, by rfl⟩ : syracuseStep 4112137 = 3084103) B3084103
theorem B5482849 : Blo 2165435 5482849 := bstep (se 2 (by rfl) ⟨2056068, by rfl⟩ : syracuseStep 5482849 = 4112137) B4112137
theorem B7310465 : Blo 2165435 7310465 := bstep (se 2 (by rfl) ⟨2741424, by rfl⟩ : syracuseStep 7310465 = 5482849) B5482849
theorem B4873643 : Blo 2165435 4873643 := bstep (se 1 (by rfl) ⟨3655232, by rfl⟩ : syracuseStep 4873643 = 7310465) B7310465
theorem B3249095 : Blo 2165435 3249095 := bstep (se 1 (by rfl) ⟨2436821, by rfl⟩ : syracuseStep 3249095 = 4873643) B4873643
theorem B2166063 : Blo 2165435 2166063 := bstep (se 1 (by rfl) ⟨1624547, by rfl⟩ : syracuseStep 2166063 = 3249095) B3249095
theorem B3249101 : Blo 2165435 3249101 := bbase (se 3 (by rfl) ⟨609206, by rfl⟩ : syracuseStep 3249101 = 1218413) (by norm_num)
theorem B2166067 : Blo 2165435 2166067 := bstep (se 1 (by rfl) ⟨1624550, by rfl⟩ : syracuseStep 2166067 = 3249101) B3249101
theorem B4873661 : Blo 2165435 4873661 := bbase (se 3 (by rfl) ⟨913811, by rfl⟩ : syracuseStep 4873661 = 1827623) (by norm_num)
theorem B3249107 : Blo 2165435 3249107 := bstep (se 1 (by rfl) ⟨2436830, by rfl⟩ : syracuseStep 3249107 = 4873661) B4873661
theorem B2166071 : Blo 2165435 2166071 := bstep (se 1 (by rfl) ⟨1624553, by rfl⟩ : syracuseStep 2166071 = 3249107) B3249107
theorem B3655253 : Blo 2165435 3655253 := bbase (se 8 (by rfl) ⟨21417, by rfl⟩ : syracuseStep 3655253 = 42835) (by norm_num)
theorem B2436835 : Blo 2165435 2436835 := bstep (se 1 (by rfl) ⟨1827626, by rfl⟩ : syracuseStep 2436835 = 3655253) B3655253
theorem B3249113 : Blo 2165435 3249113 := bstep (se 2 (by rfl) ⟨1218417, by rfl⟩ : syracuseStep 3249113 = 2436835) B2436835
theorem B2166075 : Blo 2165435 2166075 := bstep (se 1 (by rfl) ⟨1624556, by rfl⟩ : syracuseStep 2166075 = 3249113) B3249113
theorem B2195633 : Blo 2165435 2195633 := bbase (se 2 (by rfl) ⟨823362, by rfl⟩ : syracuseStep 2195633 = 1646725) (by norm_num)
theorem B5855021 : Blo 2165435 5855021 := bstep (se 3 (by rfl) ⟨1097816, by rfl⟩ : syracuseStep 5855021 = 2195633) B2195633
theorem B3903347 : Blo 2165435 3903347 := bstep (se 1 (by rfl) ⟨2927510, by rfl⟩ : syracuseStep 3903347 = 5855021) B5855021
theorem B10408925 : Blo 2165435 10408925 := bstep (se 3 (by rfl) ⟨1951673, by rfl⟩ : syracuseStep 10408925 = 3903347) B3903347
theorem B6939283 : Blo 2165435 6939283 := bstep (se 1 (by rfl) ⟨5204462, by rfl⟩ : syracuseStep 6939283 = 10408925) B10408925
theorem B9252377 : Blo 2165435 9252377 := bstep (se 2 (by rfl) ⟨3469641, by rfl⟩ : syracuseStep 9252377 = 6939283) B6939283
theorem B6168251 : Blo 2165435 6168251 := bstep (se 1 (by rfl) ⟨4626188, by rfl⟩ : syracuseStep 6168251 = 9252377) B9252377
theorem B16448669 : Blo 2165435 16448669 := bstep (se 3 (by rfl) ⟨3084125, by rfl⟩ : syracuseStep 16448669 = 6168251) B6168251
theorem B10965779 : Blo 2165435 10965779 := bstep (se 1 (by rfl) ⟨8224334, by rfl⟩ : syracuseStep 10965779 = 16448669) B16448669
theorem B7310519 : Blo 2165435 7310519 := bstep (se 1 (by rfl) ⟨5482889, by rfl⟩ : syracuseStep 7310519 = 10965779) B10965779
theorem B4873679 : Blo 2165435 4873679 := bstep (se 1 (by rfl) ⟨3655259, by rfl⟩ : syracuseStep 4873679 = 7310519) B7310519
theorem B3249119 : Blo 2165435 3249119 := bstep (se 1 (by rfl) ⟨2436839, by rfl⟩ : syracuseStep 3249119 = 4873679) B4873679
theorem B2166079 : Blo 2165435 2166079 := bstep (se 1 (by rfl) ⟨1624559, by rfl⟩ : syracuseStep 2166079 = 3249119) B3249119
theorem B3249125 : Blo 2165435 3249125 := bbase (se 4 (by rfl) ⟨304605, by rfl⟩ : syracuseStep 3249125 = 609211) (by norm_num)
theorem B2166083 : Blo 2165435 2166083 := bstep (se 1 (by rfl) ⟨1624562, by rfl⟩ : syracuseStep 2166083 = 3249125) B3249125
theorem B7806725 : Blo 2165435 7806725 := bbase (se 4 (by rfl) ⟨731880, by rfl⟩ : syracuseStep 7806725 = 1463761) (by norm_num)
theorem B5204483 : Blo 2165435 5204483 := bstep (se 1 (by rfl) ⟨3903362, by rfl⟩ : syracuseStep 5204483 = 7806725) B7806725
theorem B3469655 : Blo 2165435 3469655 := bstep (se 1 (by rfl) ⟨2602241, by rfl⟩ : syracuseStep 3469655 = 5204483) B5204483
theorem B9252413 : Blo 2165435 9252413 := bstep (se 3 (by rfl) ⟨1734827, by rfl⟩ : syracuseStep 9252413 = 3469655) B3469655
theorem B6168275 : Blo 2165435 6168275 := bstep (se 1 (by rfl) ⟨4626206, by rfl⟩ : syracuseStep 6168275 = 9252413) B9252413
theorem B4112183 : Blo 2165435 4112183 := bstep (se 1 (by rfl) ⟨3084137, by rfl⟩ : syracuseStep 4112183 = 6168275) B6168275
theorem B2741455 : Blo 2165435 2741455 := bstep (se 1 (by rfl) ⟨2056091, by rfl⟩ : syracuseStep 2741455 = 4112183) B4112183
theorem B3655273 : Blo 2165435 3655273 := bstep (se 2 (by rfl) ⟨1370727, by rfl⟩ : syracuseStep 3655273 = 2741455) B2741455
theorem B4873697 : Blo 2165435 4873697 := bstep (se 2 (by rfl) ⟨1827636, by rfl⟩ : syracuseStep 4873697 = 3655273) B3655273
theorem B3249131 : Blo 2165435 3249131 := bstep (se 1 (by rfl) ⟨2436848, by rfl⟩ : syracuseStep 3249131 = 4873697) B4873697
theorem B2166087 : Blo 2165435 2166087 := bstep (se 1 (by rfl) ⟨1624565, by rfl⟩ : syracuseStep 2166087 = 3249131) B3249131
theorem B2436853 : Blo 2165435 2436853 := bbase (se 5 (by rfl) ⟨114227, by rfl⟩ : syracuseStep 2436853 = 228455) (by norm_num)
theorem B3249137 : Blo 2165435 3249137 := bstep (se 2 (by rfl) ⟨1218426, by rfl⟩ : syracuseStep 3249137 = 2436853) B2436853
theorem B2166091 : Blo 2165435 2166091 := bstep (se 1 (by rfl) ⟨1624568, by rfl⟩ : syracuseStep 2166091 = 3249137) B3249137
theorem B2741465 : Blo 2165435 2741465 := bbase (se 2 (by rfl) ⟨1028049, by rfl⟩ : syracuseStep 2741465 = 2056099) (by norm_num)
theorem B7310573 : Blo 2165435 7310573 := bstep (se 3 (by rfl) ⟨1370732, by rfl⟩ : syracuseStep 7310573 = 2741465) B2741465
theorem B4873715 : Blo 2165435 4873715 := bstep (se 1 (by rfl) ⟨3655286, by rfl⟩ : syracuseStep 4873715 = 7310573) B7310573
theorem B3249143 : Blo 2165435 3249143 := bstep (se 1 (by rfl) ⟨2436857, by rfl⟩ : syracuseStep 3249143 = 4873715) B4873715
theorem B2166095 : Blo 2165435 2166095 := bstep (se 1 (by rfl) ⟨1624571, by rfl⟩ : syracuseStep 2166095 = 3249143) B3249143
theorem B3249149 : Blo 2165435 3249149 := bbase (se 3 (by rfl) ⟨609215, by rfl⟩ : syracuseStep 3249149 = 1218431) (by norm_num)
theorem B2166099 : Blo 2165435 2166099 := bstep (se 1 (by rfl) ⟨1624574, by rfl⟩ : syracuseStep 2166099 = 3249149) B3249149
theorem B4873733 : Blo 2165435 4873733 := bbase (se 4 (by rfl) ⟨456912, by rfl⟩ : syracuseStep 4873733 = 913825) (by norm_num)
theorem B3249155 : Blo 2165435 3249155 := bstep (se 1 (by rfl) ⟨2436866, by rfl⟩ : syracuseStep 3249155 = 4873733) B4873733
theorem B2166103 : Blo 2165435 2166103 := bstep (se 1 (by rfl) ⟨1624577, by rfl⟩ : syracuseStep 2166103 = 3249155) B3249155
theorem B4112221 : Blo 2165435 4112221 := bbase (se 3 (by rfl) ⟨771041, by rfl⟩ : syracuseStep 4112221 = 1542083) (by norm_num)
theorem B5482961 : Blo 2165435 5482961 := bstep (se 2 (by rfl) ⟨2056110, by rfl⟩ : syracuseStep 5482961 = 4112221) B4112221
theorem B3655307 : Blo 2165435 3655307 := bstep (se 1 (by rfl) ⟨2741480, by rfl⟩ : syracuseStep 3655307 = 5482961) B5482961
theorem B2436871 : Blo 2165435 2436871 := bstep (se 1 (by rfl) ⟨1827653, by rfl⟩ : syracuseStep 2436871 = 3655307) B3655307
theorem B3249161 : Blo 2165435 3249161 := bstep (se 2 (by rfl) ⟨1218435, by rfl⟩ : syracuseStep 3249161 = 2436871) B2436871
theorem B2166107 : Blo 2165435 2166107 := bstep (se 1 (by rfl) ⟨1624580, by rfl⟩ : syracuseStep 2166107 = 3249161) B3249161
theorem B10965941 : Blo 2165435 10965941 := bbase (se 5 (by rfl) ⟨514028, by rfl⟩ : syracuseStep 10965941 = 1028057) (by norm_num)
theorem B7310627 : Blo 2165435 7310627 := bstep (se 1 (by rfl) ⟨5482970, by rfl⟩ : syracuseStep 7310627 = 10965941) B10965941
theorem B4873751 : Blo 2165435 4873751 := bstep (se 1 (by rfl) ⟨3655313, by rfl⟩ : syracuseStep 4873751 = 7310627) B7310627
theorem B3249167 : Blo 2165435 3249167 := bstep (se 1 (by rfl) ⟨2436875, by rfl⟩ : syracuseStep 3249167 = 4873751) B4873751
theorem B2166111 : Blo 2165435 2166111 := bstep (se 1 (by rfl) ⟨1624583, by rfl⟩ : syracuseStep 2166111 = 3249167) B3249167
theorem B3249173 : Blo 2165435 3249173 := bbase (se 6 (by rfl) ⟨76152, by rfl⟩ : syracuseStep 3249173 = 152305) (by norm_num)
theorem B2166115 : Blo 2165435 2166115 := bstep (se 1 (by rfl) ⟨1624586, by rfl⟩ : syracuseStep 2166115 = 3249173) B3249173
theorem B35130773 : Blo 2165435 35130773 := bbase (se 6 (by rfl) ⟨823377, by rfl⟩ : syracuseStep 35130773 = 1646755) (by norm_num)
theorem B23420515 : Blo 2165435 23420515 := bstep (se 1 (by rfl) ⟨17565386, by rfl⟩ : syracuseStep 23420515 = 35130773) B35130773
theorem B31227353 : Blo 2165435 31227353 := bstep (se 2 (by rfl) ⟨11710257, by rfl⟩ : syracuseStep 31227353 = 23420515) B23420515
theorem B20818235 : Blo 2165435 20818235 := bstep (se 1 (by rfl) ⟨15613676, by rfl⟩ : syracuseStep 20818235 = 31227353) B31227353
theorem B13878823 : Blo 2165435 13878823 := bstep (se 1 (by rfl) ⟨10409117, by rfl⟩ : syracuseStep 13878823 = 20818235) B20818235
theorem B18505097 : Blo 2165435 18505097 := bstep (se 2 (by rfl) ⟨6939411, by rfl⟩ : syracuseStep 18505097 = 13878823) B13878823
theorem B12336731 : Blo 2165435 12336731 := bstep (se 1 (by rfl) ⟨9252548, by rfl⟩ : syracuseStep 12336731 = 18505097) B18505097
theorem B8224487 : Blo 2165435 8224487 := bstep (se 1 (by rfl) ⟨6168365, by rfl⟩ : syracuseStep 8224487 = 12336731) B12336731
theorem B5482991 : Blo 2165435 5482991 := bstep (se 1 (by rfl) ⟨4112243, by rfl⟩ : syracuseStep 5482991 = 8224487) B8224487
theorem B3655327 : Blo 2165435 3655327 := bstep (se 1 (by rfl) ⟨2741495, by rfl⟩ : syracuseStep 3655327 = 5482991) B5482991
theorem B4873769 : Blo 2165435 4873769 := bstep (se 2 (by rfl) ⟨1827663, by rfl⟩ : syracuseStep 4873769 = 3655327) B3655327
theorem B3249179 : Blo 2165435 3249179 := bstep (se 1 (by rfl) ⟨2436884, by rfl⟩ : syracuseStep 3249179 = 4873769) B4873769
theorem B2166119 : Blo 2165435 2166119 := bstep (se 1 (by rfl) ⟨1624589, by rfl⟩ : syracuseStep 2166119 = 3249179) B3249179
theorem B2436889 : Blo 2165435 2436889 := bbase (se 2 (by rfl) ⟨913833, by rfl⟩ : syracuseStep 2436889 = 1827667) (by norm_num)
theorem B3249185 : Blo 2165435 3249185 := bstep (se 2 (by rfl) ⟨1218444, by rfl⟩ : syracuseStep 3249185 = 2436889) B2436889
theorem B2166123 : Blo 2165435 2166123 := bstep (se 1 (by rfl) ⟨1624592, by rfl⟩ : syracuseStep 2166123 = 3249185) B3249185
theorem B8224517 : Blo 2165435 8224517 := bbase (se 4 (by rfl) ⟨771048, by rfl⟩ : syracuseStep 8224517 = 1542097) (by norm_num)
theorem B5483011 : Blo 2165435 5483011 := bstep (se 1 (by rfl) ⟨4112258, by rfl⟩ : syracuseStep 5483011 = 8224517) B8224517
theorem B7310681 : Blo 2165435 7310681 := bstep (se 2 (by rfl) ⟨2741505, by rfl⟩ : syracuseStep 7310681 = 5483011) B5483011
theorem B4873787 : Blo 2165435 4873787 := bstep (se 1 (by rfl) ⟨3655340, by rfl⟩ : syracuseStep 4873787 = 7310681) B7310681
theorem B3249191 : Blo 2165435 3249191 := bstep (se 1 (by rfl) ⟨2436893, by rfl⟩ : syracuseStep 3249191 = 4873787) B4873787
theorem B2166127 : Blo 2165435 2166127 := bstep (se 1 (by rfl) ⟨1624595, by rfl⟩ : syracuseStep 2166127 = 3249191) B3249191
theorem B3249197 : Blo 2165435 3249197 := bbase (se 3 (by rfl) ⟨609224, by rfl⟩ : syracuseStep 3249197 = 1218449) (by norm_num)
theorem B2166131 : Blo 2165435 2166131 := bstep (se 1 (by rfl) ⟨1624598, by rfl⟩ : syracuseStep 2166131 = 3249197) B3249197
theorem B4873805 : Blo 2165435 4873805 := bbase (se 3 (by rfl) ⟨913838, by rfl⟩ : syracuseStep 4873805 = 1827677) (by norm_num)
theorem B3249203 : Blo 2165435 3249203 := bstep (se 1 (by rfl) ⟨2436902, by rfl⟩ : syracuseStep 3249203 = 4873805) B4873805
theorem B2166135 : Blo 2165435 2166135 := bstep (se 1 (by rfl) ⟨1624601, by rfl⟩ : syracuseStep 2166135 = 3249203) B3249203
theorem B2741521 : Blo 2165435 2741521 := bbase (se 2 (by rfl) ⟨1028070, by rfl⟩ : syracuseStep 2741521 = 2056141) (by norm_num)
theorem B3655361 : Blo 2165435 3655361 := bstep (se 2 (by rfl) ⟨1370760, by rfl⟩ : syracuseStep 3655361 = 2741521) B2741521
theorem B2436907 : Blo 2165435 2436907 := bstep (se 1 (by rfl) ⟨1827680, by rfl⟩ : syracuseStep 2436907 = 3655361) B3655361
theorem B3249209 : Blo 2165435 3249209 := bstep (se 2 (by rfl) ⟨1218453, by rfl⟩ : syracuseStep 3249209 = 2436907) B2436907
theorem B2166139 : Blo 2165435 2166139 := bstep (se 1 (by rfl) ⟨1624604, by rfl⟩ : syracuseStep 2166139 = 3249209) B3249209
theorem B4626325 : Blo 2165435 4626325 := bbase (se 6 (by rfl) ⟨108429, by rfl⟩ : syracuseStep 4626325 = 216859) (by norm_num)
theorem B24673733 : Blo 2165435 24673733 := bstep (se 4 (by rfl) ⟨2313162, by rfl⟩ : syracuseStep 24673733 = 4626325) B4626325
theorem B16449155 : Blo 2165435 16449155 := bstep (se 1 (by rfl) ⟨12336866, by rfl⟩ : syracuseStep 16449155 = 24673733) B24673733
theorem B10966103 : Blo 2165435 10966103 := bstep (se 1 (by rfl) ⟨8224577, by rfl⟩ : syracuseStep 10966103 = 16449155) B16449155
theorem B7310735 : Blo 2165435 7310735 := bstep (se 1 (by rfl) ⟨5483051, by rfl⟩ : syracuseStep 7310735 = 10966103) B10966103
theorem B4873823 : Blo 2165435 4873823 := bstep (se 1 (by rfl) ⟨3655367, by rfl⟩ : syracuseStep 4873823 = 7310735) B7310735
theorem B3249215 : Blo 2165435 3249215 := bstep (se 1 (by rfl) ⟨2436911, by rfl⟩ : syracuseStep 3249215 = 4873823) B4873823
theorem B2166143 : Blo 2165435 2166143 := bstep (se 1 (by rfl) ⟨1624607, by rfl⟩ : syracuseStep 2166143 = 3249215) B3249215
theorem B3249221 : Blo 2165435 3249221 := bbase (se 4 (by rfl) ⟨304614, by rfl⟩ : syracuseStep 3249221 = 609229) (by norm_num)
theorem B2166147 : Blo 2165435 2166147 := bstep (se 1 (by rfl) ⟨1624610, by rfl⟩ : syracuseStep 2166147 = 3249221) B3249221
theorem B3655381 : Blo 2165435 3655381 := bbase (se 7 (by rfl) ⟨42836, by rfl⟩ : syracuseStep 3655381 = 85673) (by norm_num)
theorem B4873841 : Blo 2165435 4873841 := bstep (se 2 (by rfl) ⟨1827690, by rfl⟩ : syracuseStep 4873841 = 3655381) B3655381
theorem B3249227 : Blo 2165435 3249227 := bstep (se 1 (by rfl) ⟨2436920, by rfl⟩ : syracuseStep 3249227 = 4873841) B4873841
theorem B2166151 : Blo 2165435 2166151 := bstep (se 1 (by rfl) ⟨1624613, by rfl⟩ : syracuseStep 2166151 = 3249227) B3249227
theorem B2436925 : Blo 2165435 2436925 := bbase (se 3 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 2436925 = 913847) (by norm_num)
theorem B3249233 : Blo 2165435 3249233 := bstep (se 2 (by rfl) ⟨1218462, by rfl⟩ : syracuseStep 3249233 = 2436925) B2436925
theorem B2166155 : Blo 2165435 2166155 := bstep (se 1 (by rfl) ⟨1624616, by rfl⟩ : syracuseStep 2166155 = 3249233) B3249233
theorem B7310789 : Blo 2165435 7310789 := bbase (se 4 (by rfl) ⟨685386, by rfl⟩ : syracuseStep 7310789 = 1370773) (by norm_num)
theorem B4873859 : Blo 2165435 4873859 := bstep (se 1 (by rfl) ⟨3655394, by rfl⟩ : syracuseStep 4873859 = 7310789) B7310789
theorem B3249239 : Blo 2165435 3249239 := bstep (se 1 (by rfl) ⟨2436929, by rfl⟩ : syracuseStep 3249239 = 4873859) B4873859
theorem B2166159 : Blo 2165435 2166159 := bstep (se 1 (by rfl) ⟨1624619, by rfl⟩ : syracuseStep 2166159 = 3249239) B3249239
theorem B3249245 : Blo 2165435 3249245 := bbase (se 3 (by rfl) ⟨609233, by rfl⟩ : syracuseStep 3249245 = 1218467) (by norm_num)
theorem B2166163 : Blo 2165435 2166163 := bstep (se 1 (by rfl) ⟨1624622, by rfl⟩ : syracuseStep 2166163 = 3249245) B3249245
theorem B4873877 : Blo 2165435 4873877 := bbase (se 6 (by rfl) ⟨114231, by rfl⟩ : syracuseStep 4873877 = 228463) (by norm_num)
theorem B3249251 : Blo 2165435 3249251 := bstep (se 1 (by rfl) ⟨2436938, by rfl⟩ : syracuseStep 3249251 = 4873877) B4873877
theorem B2166167 : Blo 2165435 2166167 := bstep (se 1 (by rfl) ⟨1624625, by rfl⟩ : syracuseStep 2166167 = 3249251) B3249251
theorem B2313193 : Blo 2165435 2313193 := bbase (se 2 (by rfl) ⟨867447, by rfl⟩ : syracuseStep 2313193 = 1734895) (by norm_num)
theorem B3084257 : Blo 2165435 3084257 := bstep (se 2 (by rfl) ⟨1156596, by rfl⟩ : syracuseStep 3084257 = 2313193) B2313193
theorem B8224685 : Blo 2165435 8224685 := bstep (se 3 (by rfl) ⟨1542128, by rfl⟩ : syracuseStep 8224685 = 3084257) B3084257
theorem B5483123 : Blo 2165435 5483123 := bstep (se 1 (by rfl) ⟨4112342, by rfl⟩ : syracuseStep 5483123 = 8224685) B8224685
theorem B3655415 : Blo 2165435 3655415 := bstep (se 1 (by rfl) ⟨2741561, by rfl⟩ : syracuseStep 3655415 = 5483123) B5483123
theorem B2436943 : Blo 2165435 2436943 := bstep (se 1 (by rfl) ⟨1827707, by rfl⟩ : syracuseStep 2436943 = 3655415) B3655415
theorem B3249257 : Blo 2165435 3249257 := bstep (se 2 (by rfl) ⟨1218471, by rfl⟩ : syracuseStep 3249257 = 2436943) B2436943
theorem B2166171 : Blo 2165435 2166171 := bstep (se 1 (by rfl) ⟨1624628, by rfl⟩ : syracuseStep 2166171 = 3249257) B3249257
theorem B5204693 : Blo 2165435 5204693 := bbase (se 7 (by rfl) ⟨60992, by rfl⟩ : syracuseStep 5204693 = 121985) (by norm_num)
theorem B13879181 : Blo 2165435 13879181 := bstep (se 3 (by rfl) ⟨2602346, by rfl⟩ : syracuseStep 13879181 = 5204693) B5204693
theorem B9252787 : Blo 2165435 9252787 := bstep (se 1 (by rfl) ⟨6939590, by rfl⟩ : syracuseStep 9252787 = 13879181) B13879181
theorem B12337049 : Blo 2165435 12337049 := bstep (se 2 (by rfl) ⟨4626393, by rfl⟩ : syracuseStep 12337049 = 9252787) B9252787
theorem B8224699 : Blo 2165435 8224699 := bstep (se 1 (by rfl) ⟨6168524, by rfl⟩ : syracuseStep 8224699 = 12337049) B12337049
theorem B10966265 : Blo 2165435 10966265 := bstep (se 2 (by rfl) ⟨4112349, by rfl⟩ : syracuseStep 10966265 = 8224699) B8224699
theorem B7310843 : Blo 2165435 7310843 := bstep (se 1 (by rfl) ⟨5483132, by rfl⟩ : syracuseStep 7310843 = 10966265) B10966265
theorem B4873895 : Blo 2165435 4873895 := bstep (se 1 (by rfl) ⟨3655421, by rfl⟩ : syracuseStep 4873895 = 7310843) B7310843
theorem B3249263 : Blo 2165435 3249263 := bstep (se 1 (by rfl) ⟨2436947, by rfl⟩ : syracuseStep 3249263 = 4873895) B4873895
theorem B2166175 : Blo 2165435 2166175 := bstep (se 1 (by rfl) ⟨1624631, by rfl⟩ : syracuseStep 2166175 = 3249263) B3249263
theorem B3249269 : Blo 2165435 3249269 := bbase (se 5 (by rfl) ⟨152309, by rfl⟩ : syracuseStep 3249269 = 304619) (by norm_num)
theorem B2166179 : Blo 2165435 2166179 := bstep (se 1 (by rfl) ⟨1624634, by rfl⟩ : syracuseStep 2166179 = 3249269) B3249269
theorem B4112365 : Blo 2165435 4112365 := bbase (se 3 (by rfl) ⟨771068, by rfl⟩ : syracuseStep 4112365 = 1542137) (by norm_num)
theorem B5483153 : Blo 2165435 5483153 := bstep (se 2 (by rfl) ⟨2056182, by rfl⟩ : syracuseStep 5483153 = 4112365) B4112365
theorem B3655435 : Blo 2165435 3655435 := bstep (se 1 (by rfl) ⟨2741576, by rfl⟩ : syracuseStep 3655435 = 5483153) B5483153
theorem B4873913 : Blo 2165435 4873913 := bstep (se 2 (by rfl) ⟨1827717, by rfl⟩ : syracuseStep 4873913 = 3655435) B3655435
theorem B3249275 : Blo 2165435 3249275 := bstep (se 1 (by rfl) ⟨2436956, by rfl⟩ : syracuseStep 3249275 = 4873913) B4873913
theorem B2166183 : Blo 2165435 2166183 := bstep (se 1 (by rfl) ⟨1624637, by rfl⟩ : syracuseStep 2166183 = 3249275) B3249275
theorem B2436961 : Blo 2165435 2436961 := bbase (se 2 (by rfl) ⟨913860, by rfl⟩ : syracuseStep 2436961 = 1827721) (by norm_num)
theorem B3249281 : Blo 2165435 3249281 := bstep (se 2 (by rfl) ⟨1218480, by rfl⟩ : syracuseStep 3249281 = 2436961) B2436961
theorem B2166187 : Blo 2165435 2166187 := bstep (se 1 (by rfl) ⟨1624640, by rfl⟩ : syracuseStep 2166187 = 3249281) B3249281
theorem B5483173 : Blo 2165435 5483173 := bbase (se 4 (by rfl) ⟨514047, by rfl⟩ : syracuseStep 5483173 = 1028095) (by norm_num)
theorem B7310897 : Blo 2165435 7310897 := bstep (se 2 (by rfl) ⟨2741586, by rfl⟩ : syracuseStep 7310897 = 5483173) B5483173
theorem B4873931 : Blo 2165435 4873931 := bstep (se 1 (by rfl) ⟨3655448, by rfl⟩ : syracuseStep 4873931 = 7310897) B7310897
theorem B3249287 : Blo 2165435 3249287 := bstep (se 1 (by rfl) ⟨2436965, by rfl⟩ : syracuseStep 3249287 = 4873931) B4873931
theorem B2166191 : Blo 2165435 2166191 := bstep (se 1 (by rfl) ⟨1624643, by rfl⟩ : syracuseStep 2166191 = 3249287) B3249287
theorem B3249293 : Blo 2165435 3249293 := bbase (se 3 (by rfl) ⟨609242, by rfl⟩ : syracuseStep 3249293 = 1218485) (by norm_num)
theorem B2166195 : Blo 2165435 2166195 := bstep (se 1 (by rfl) ⟨1624646, by rfl⟩ : syracuseStep 2166195 = 3249293) B3249293
theorem B4873949 : Blo 2165435 4873949 := bbase (se 3 (by rfl) ⟨913865, by rfl⟩ : syracuseStep 4873949 = 1827731) (by norm_num)
theorem B3249299 : Blo 2165435 3249299 := bstep (se 1 (by rfl) ⟨2436974, by rfl⟩ : syracuseStep 3249299 = 4873949) B4873949
theorem B2166199 : Blo 2165435 2166199 := bstep (se 1 (by rfl) ⟨1624649, by rfl⟩ : syracuseStep 2166199 = 3249299) B3249299
theorem B3655469 : Blo 2165435 3655469 := bbase (se 3 (by rfl) ⟨685400, by rfl⟩ : syracuseStep 3655469 = 1370801) (by norm_num)
theorem B2436979 : Blo 2165435 2436979 := bstep (se 1 (by rfl) ⟨1827734, by rfl⟩ : syracuseStep 2436979 = 3655469) B3655469
theorem B3249305 : Blo 2165435 3249305 := bstep (se 2 (by rfl) ⟨1218489, by rfl⟩ : syracuseStep 3249305 = 2436979) B2436979
theorem B2166203 : Blo 2165435 2166203 := bstep (se 1 (by rfl) ⟨1624652, by rfl⟩ : syracuseStep 2166203 = 3249305) B3249305
theorem B4391525 : Blo 2165435 4391525 := bbase (se 4 (by rfl) ⟨411705, by rfl⟩ : syracuseStep 4391525 = 823411) (by norm_num)
theorem B2927683 : Blo 2165435 2927683 := bstep (se 1 (by rfl) ⟨2195762, by rfl⟩ : syracuseStep 2927683 = 4391525) B4391525
theorem B15614309 : Blo 2165435 15614309 := bstep (se 4 (by rfl) ⟨1463841, by rfl⟩ : syracuseStep 15614309 = 2927683) B2927683
theorem B41638157 : Blo 2165435 41638157 := bstep (se 3 (by rfl) ⟨7807154, by rfl⟩ : syracuseStep 41638157 = 15614309) B15614309
theorem B27758771 : Blo 2165435 27758771 := bstep (se 1 (by rfl) ⟨20819078, by rfl⟩ : syracuseStep 27758771 = 41638157) B41638157
theorem B18505847 : Blo 2165435 18505847 := bstep (se 1 (by rfl) ⟨13879385, by rfl⟩ : syracuseStep 18505847 = 27758771) B27758771
theorem B12337231 : Blo 2165435 12337231 := bstep (se 1 (by rfl) ⟨9252923, by rfl⟩ : syracuseStep 12337231 = 18505847) B18505847
theorem B16449641 : Blo 2165435 16449641 := bstep (se 2 (by rfl) ⟨6168615, by rfl⟩ : syracuseStep 16449641 = 12337231) B12337231
theorem B10966427 : Blo 2165435 10966427 := bstep (se 1 (by rfl) ⟨8224820, by rfl⟩ : syracuseStep 10966427 = 16449641) B16449641
theorem B7310951 : Blo 2165435 7310951 := bstep (se 1 (by rfl) ⟨5483213, by rfl⟩ : syracuseStep 7310951 = 10966427) B10966427
theorem B4873967 : Blo 2165435 4873967 := bstep (se 1 (by rfl) ⟨3655475, by rfl⟩ : syracuseStep 4873967 = 7310951) B7310951
theorem B3249311 : Blo 2165435 3249311 := bstep (se 1 (by rfl) ⟨2436983, by rfl⟩ : syracuseStep 3249311 = 4873967) B4873967
theorem B2166207 : Blo 2165435 2166207 := bstep (se 1 (by rfl) ⟨1624655, by rfl⟩ : syracuseStep 2166207 = 3249311) B3249311
theorem B3249317 : Blo 2165435 3249317 := bbase (se 4 (by rfl) ⟨304623, by rfl⟩ : syracuseStep 3249317 = 609247) (by norm_num)
theorem B2166211 : Blo 2165435 2166211 := bstep (se 1 (by rfl) ⟨1624658, by rfl⟩ : syracuseStep 2166211 = 3249317) B3249317
theorem B2741617 : Blo 2165435 2741617 := bbase (se 2 (by rfl) ⟨1028106, by rfl⟩ : syracuseStep 2741617 = 2056213) (by norm_num)
theorem B3655489 : Blo 2165435 3655489 := bstep (se 2 (by rfl) ⟨1370808, by rfl⟩ : syracuseStep 3655489 = 2741617) B2741617
theorem B4873985 : Blo 2165435 4873985 := bstep (se 2 (by rfl) ⟨1827744, by rfl⟩ : syracuseStep 4873985 = 3655489) B3655489
theorem B3249323 : Blo 2165435 3249323 := bstep (se 1 (by rfl) ⟨2436992, by rfl⟩ : syracuseStep 3249323 = 4873985) B4873985
theorem B2166215 : Blo 2165435 2166215 := bstep (se 1 (by rfl) ⟨1624661, by rfl⟩ : syracuseStep 2166215 = 3249323) B3249323
theorem B2436997 : Blo 2165435 2436997 := bbase (se 4 (by rfl) ⟨228468, by rfl⟩ : syracuseStep 2436997 = 456937) (by norm_num)
theorem B3249329 : Blo 2165435 3249329 := bstep (se 2 (by rfl) ⟨1218498, by rfl⟩ : syracuseStep 3249329 = 2436997) B2436997
theorem B2166219 : Blo 2165435 2166219 := bstep (se 1 (by rfl) ⟨1624664, by rfl⟩ : syracuseStep 2166219 = 3249329) B3249329
theorem B2602405 : Blo 2165435 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B3469873 : Blo 2165435 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B4626497 : Blo 2165435 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B3084331 : Blo 2165435 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B4112441 : Blo 2165435 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B2741627 : Blo 2165435 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B7311005 : Blo 2165435 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B4874003 : Blo 2165435 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B3249335 : Blo 2165435 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B2166223 : Blo 2165435 2166223 := bstep (se 1 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 2166223 = 3249335) B3249335
theorem B3249341 : Blo 2165435 3249341 := bbase (se 3 (by rfl) ⟨609251, by rfl⟩ : syracuseStep 3249341 = 1218503) (by norm_num)
theorem B2166227 : Blo 2165435 2166227 := bstep (se 1 (by rfl) ⟨1624670, by rfl⟩ : syracuseStep 2166227 = 3249341) B3249341
theorem B4874021 : Blo 2165435 4874021 := bbase (se 4 (by rfl) ⟨456939, by rfl⟩ : syracuseStep 4874021 = 913879) (by norm_num)
theorem B3249347 : Blo 2165435 3249347 := bstep (se 1 (by rfl) ⟨2437010, by rfl⟩ : syracuseStep 3249347 = 4874021) B4874021
theorem B2166231 : Blo 2165435 2166231 := bstep (se 1 (by rfl) ⟨1624673, by rfl⟩ : syracuseStep 2166231 = 3249347) B3249347
theorem B5483285 : Blo 2165435 5483285 := bbase (se 6 (by rfl) ⟨128514, by rfl⟩ : syracuseStep 5483285 = 257029) (by norm_num)
theorem B3655523 : Blo 2165435 3655523 := bstep (se 1 (by rfl) ⟨2741642, by rfl⟩ : syracuseStep 3655523 = 5483285) B5483285
theorem B2437015 : Blo 2165435 2437015 := bstep (se 1 (by rfl) ⟨1827761, by rfl⟩ : syracuseStep 2437015 = 3655523) B3655523
theorem B3249353 : Blo 2165435 3249353 := bstep (se 2 (by rfl) ⟨1218507, by rfl⟩ : syracuseStep 3249353 = 2437015) B2437015
theorem B2166235 : Blo 2165435 2166235 := bstep (se 1 (by rfl) ⟨1624676, by rfl⟩ : syracuseStep 2166235 = 3249353) B3249353
theorem B9253061 : Blo 2165435 9253061 := bbase (se 4 (by rfl) ⟨867474, by rfl⟩ : syracuseStep 9253061 = 1734949) (by norm_num)
theorem B6168707 : Blo 2165435 6168707 := bstep (se 1 (by rfl) ⟨4626530, by rfl⟩ : syracuseStep 6168707 = 9253061) B9253061
theorem B4112471 : Blo 2165435 4112471 := bstep (se 1 (by rfl) ⟨3084353, by rfl⟩ : syracuseStep 4112471 = 6168707) B6168707
theorem B10966589 : Blo 2165435 10966589 := bstep (se 3 (by rfl) ⟨2056235, by rfl⟩ : syracuseStep 10966589 = 4112471) B4112471
theorem B7311059 : Blo 2165435 7311059 := bstep (se 1 (by rfl) ⟨5483294, by rfl⟩ : syracuseStep 7311059 = 10966589) B10966589
theorem B4874039 : Blo 2165435 4874039 := bstep (se 1 (by rfl) ⟨3655529, by rfl⟩ : syracuseStep 4874039 = 7311059) B7311059
theorem B3249359 : Blo 2165435 3249359 := bstep (se 1 (by rfl) ⟨2437019, by rfl⟩ : syracuseStep 3249359 = 4874039) B4874039
theorem B2166239 : Blo 2165435 2166239 := bstep (se 1 (by rfl) ⟨1624679, by rfl⟩ : syracuseStep 2166239 = 3249359) B3249359
theorem B3249365 : Blo 2165435 3249365 := bbase (se 7 (by rfl) ⟨38078, by rfl⟩ : syracuseStep 3249365 = 76157) (by norm_num)
theorem B2166243 : Blo 2165435 2166243 := bstep (se 1 (by rfl) ⟨1624682, by rfl⟩ : syracuseStep 2166243 = 3249365) B3249365
theorem B3084365 : Blo 2165435 3084365 := bbase (se 3 (by rfl) ⟨578318, by rfl⟩ : syracuseStep 3084365 = 1156637) (by norm_num)
theorem B8224973 : Blo 2165435 8224973 := bstep (se 3 (by rfl) ⟨1542182, by rfl⟩ : syracuseStep 8224973 = 3084365) B3084365
theorem B5483315 : Blo 2165435 5483315 := bstep (se 1 (by rfl) ⟨4112486, by rfl⟩ : syracuseStep 5483315 = 8224973) B8224973
theorem B3655543 : Blo 2165435 3655543 := bstep (se 1 (by rfl) ⟨2741657, by rfl⟩ : syracuseStep 3655543 = 5483315) B5483315
theorem B4874057 : Blo 2165435 4874057 := bstep (se 2 (by rfl) ⟨1827771, by rfl⟩ : syracuseStep 4874057 = 3655543) B3655543
theorem B3249371 : Blo 2165435 3249371 := bstep (se 1 (by rfl) ⟨2437028, by rfl⟩ : syracuseStep 3249371 = 4874057) B4874057
theorem B2166247 : Blo 2165435 2166247 := bstep (se 1 (by rfl) ⟨1624685, by rfl⟩ : syracuseStep 2166247 = 3249371) B3249371
theorem B2437033 : Blo 2165435 2437033 := bbase (se 2 (by rfl) ⟨913887, by rfl⟩ : syracuseStep 2437033 = 1827775) (by norm_num)
theorem B3249377 : Blo 2165435 3249377 := bstep (se 2 (by rfl) ⟨1218516, by rfl⟩ : syracuseStep 3249377 = 2437033) B2437033
theorem B2166251 : Blo 2165435 2166251 := bstep (se 1 (by rfl) ⟨1624688, by rfl⟩ : syracuseStep 2166251 = 3249377) B3249377
theorem B3293717 : Blo 2165435 3293717 := bbase (se 6 (by rfl) ⟨77196, by rfl⟩ : syracuseStep 3293717 = 154393) (by norm_num)
theorem B8783245 : Blo 2165435 8783245 := bstep (se 3 (by rfl) ⟨1646858, by rfl⟩ : syracuseStep 8783245 = 3293717) B3293717
theorem B11710993 : Blo 2165435 11710993 := bstep (se 2 (by rfl) ⟨4391622, by rfl⟩ : syracuseStep 11710993 = 8783245) B8783245
theorem B15614657 : Blo 2165435 15614657 := bstep (se 2 (by rfl) ⟨5855496, by rfl⟩ : syracuseStep 15614657 = 11710993) B11710993
theorem B10409771 : Blo 2165435 10409771 := bstep (se 1 (by rfl) ⟨7807328, by rfl⟩ : syracuseStep 10409771 = 15614657) B15614657
theorem B6939847 : Blo 2165435 6939847 := bstep (se 1 (by rfl) ⟨5204885, by rfl⟩ : syracuseStep 6939847 = 10409771) B10409771
theorem B9253129 : Blo 2165435 9253129 := bstep (se 2 (by rfl) ⟨3469923, by rfl⟩ : syracuseStep 9253129 = 6939847) B6939847
theorem B12337505 : Blo 2165435 12337505 := bstep (se 2 (by rfl) ⟨4626564, by rfl⟩ : syracuseStep 12337505 = 9253129) B9253129
theorem B8225003 : Blo 2165435 8225003 := bstep (se 1 (by rfl) ⟨6168752, by rfl⟩ : syracuseStep 8225003 = 12337505) B12337505
theorem B5483335 : Blo 2165435 5483335 := bstep (se 1 (by rfl) ⟨4112501, by rfl⟩ : syracuseStep 5483335 = 8225003) B8225003
theorem B7311113 : Blo 2165435 7311113 := bstep (se 2 (by rfl) ⟨2741667, by rfl⟩ : syracuseStep 7311113 = 5483335) B5483335
theorem B4874075 : Blo 2165435 4874075 := bstep (se 1 (by rfl) ⟨3655556, by rfl⟩ : syracuseStep 4874075 = 7311113) B7311113
theorem B3249383 : Blo 2165435 3249383 := bstep (se 1 (by rfl) ⟨2437037, by rfl⟩ : syracuseStep 3249383 = 4874075) B4874075
theorem B2166255 : Blo 2165435 2166255 := bstep (se 1 (by rfl) ⟨1624691, by rfl⟩ : syracuseStep 2166255 = 3249383) B3249383
theorem B3249389 : Blo 2165435 3249389 := bbase (se 3 (by rfl) ⟨609260, by rfl⟩ : syracuseStep 3249389 = 1218521) (by norm_num)
theorem B2166259 : Blo 2165435 2166259 := bstep (se 1 (by rfl) ⟨1624694, by rfl⟩ : syracuseStep 2166259 = 3249389) B3249389
theorem B4874093 : Blo 2165435 4874093 := bbase (se 3 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 4874093 = 1827785) (by norm_num)
theorem B3249395 : Blo 2165435 3249395 := bstep (se 1 (by rfl) ⟨2437046, by rfl⟩ : syracuseStep 3249395 = 4874093) B4874093
theorem B2166263 : Blo 2165435 2166263 := bstep (se 1 (by rfl) ⟨1624697, by rfl⟩ : syracuseStep 2166263 = 3249395) B3249395
theorem B4112525 : Blo 2165435 4112525 := bbase (se 3 (by rfl) ⟨771098, by rfl⟩ : syracuseStep 4112525 = 1542197) (by norm_num)
theorem B2741683 : Blo 2165435 2741683 := bstep (se 1 (by rfl) ⟨2056262, by rfl⟩ : syracuseStep 2741683 = 4112525) B4112525
theorem B3655577 : Blo 2165435 3655577 := bstep (se 2 (by rfl) ⟨1370841, by rfl⟩ : syracuseStep 3655577 = 2741683) B2741683
theorem B2437051 : Blo 2165435 2437051 := bstep (se 1 (by rfl) ⟨1827788, by rfl⟩ : syracuseStep 2437051 = 3655577) B3655577
theorem B3249401 : Blo 2165435 3249401 := bstep (se 2 (by rfl) ⟨1218525, by rfl⟩ : syracuseStep 3249401 = 2437051) B2437051
theorem B2166267 : Blo 2165435 2166267 := bstep (se 1 (by rfl) ⟨1624700, by rfl⟩ : syracuseStep 2166267 = 3249401) B3249401
theorem B3293741 : Blo 2165435 3293741 := bbase (se 3 (by rfl) ⟨617576, by rfl⟩ : syracuseStep 3293741 = 1235153) (by norm_num)
theorem B8783309 : Blo 2165435 8783309 := bstep (se 3 (by rfl) ⟨1646870, by rfl⟩ : syracuseStep 8783309 = 3293741) B3293741
theorem B5855539 : Blo 2165435 5855539 := bstep (se 1 (by rfl) ⟨4391654, by rfl⟩ : syracuseStep 5855539 = 8783309) B8783309
theorem B7807385 : Blo 2165435 7807385 := bstep (se 2 (by rfl) ⟨2927769, by rfl⟩ : syracuseStep 7807385 = 5855539) B5855539
theorem B20819693 : Blo 2165435 20819693 := bstep (se 3 (by rfl) ⟨3903692, by rfl⟩ : syracuseStep 20819693 = 7807385) B7807385
theorem B55519181 : Blo 2165435 55519181 := bstep (se 3 (by rfl) ⟨10409846, by rfl⟩ : syracuseStep 55519181 = 20819693) B20819693
theorem B37012787 : Blo 2165435 37012787 := bstep (se 1 (by rfl) ⟨27759590, by rfl⟩ : syracuseStep 37012787 = 55519181) B55519181
theorem B24675191 : Blo 2165435 24675191 := bstep (se 1 (by rfl) ⟨18506393, by rfl⟩ : syracuseStep 24675191 = 37012787) B37012787
theorem B16450127 : Blo 2165435 16450127 := bstep (se 1 (by rfl) ⟨12337595, by rfl⟩ : syracuseStep 16450127 = 24675191) B24675191
theorem B10966751 : Blo 2165435 10966751 := bstep (se 1 (by rfl) ⟨8225063, by rfl⟩ : syracuseStep 10966751 = 16450127) B16450127
theorem B7311167 : Blo 2165435 7311167 := bstep (se 1 (by rfl) ⟨5483375, by rfl⟩ : syracuseStep 7311167 = 10966751) B10966751
theorem B4874111 : Blo 2165435 4874111 := bstep (se 1 (by rfl) ⟨3655583, by rfl⟩ : syracuseStep 4874111 = 7311167) B7311167
theorem B3249407 : Blo 2165435 3249407 := bstep (se 1 (by rfl) ⟨2437055, by rfl⟩ : syracuseStep 3249407 = 4874111) B4874111
theorem B2166271 : Blo 2165435 2166271 := bstep (se 1 (by rfl) ⟨1624703, by rfl⟩ : syracuseStep 2166271 = 3249407) B3249407
theorem B3249413 : Blo 2165435 3249413 := bbase (se 4 (by rfl) ⟨304632, by rfl⟩ : syracuseStep 3249413 = 609265) (by norm_num)
theorem B2166275 : Blo 2165435 2166275 := bstep (se 1 (by rfl) ⟨1624706, by rfl⟩ : syracuseStep 2166275 = 3249413) B3249413
theorem B3655597 : Blo 2165435 3655597 := bbase (se 3 (by rfl) ⟨685424, by rfl⟩ : syracuseStep 3655597 = 1370849) (by norm_num)
theorem B4874129 : Blo 2165435 4874129 := bstep (se 2 (by rfl) ⟨1827798, by rfl⟩ : syracuseStep 4874129 = 3655597) B3655597
theorem B3249419 : Blo 2165435 3249419 := bstep (se 1 (by rfl) ⟨2437064, by rfl⟩ : syracuseStep 3249419 = 4874129) B4874129
theorem B2166279 : Blo 2165435 2166279 := bstep (se 1 (by rfl) ⟨1624709, by rfl⟩ : syracuseStep 2166279 = 3249419) B3249419
theorem B2437069 : Blo 2165435 2437069 := bbase (se 3 (by rfl) ⟨456950, by rfl⟩ : syracuseStep 2437069 = 913901) (by norm_num)
theorem B3249425 : Blo 2165435 3249425 := bstep (se 2 (by rfl) ⟨1218534, by rfl⟩ : syracuseStep 3249425 = 2437069) B2437069
theorem B2166283 : Blo 2165435 2166283 := bstep (se 1 (by rfl) ⟨1624712, by rfl⟩ : syracuseStep 2166283 = 3249425) B3249425
theorem B7311221 : Blo 2165435 7311221 := bbase (se 5 (by rfl) ⟨342713, by rfl⟩ : syracuseStep 7311221 = 685427) (by norm_num)
theorem B4874147 : Blo 2165435 4874147 := bstep (se 1 (by rfl) ⟨3655610, by rfl⟩ : syracuseStep 4874147 = 7311221) B7311221
theorem B3249431 : Blo 2165435 3249431 := bstep (se 1 (by rfl) ⟨2437073, by rfl⟩ : syracuseStep 3249431 = 4874147) B4874147
theorem B2166287 : Blo 2165435 2166287 := bstep (se 1 (by rfl) ⟨1624715, by rfl⟩ : syracuseStep 2166287 = 3249431) B3249431
theorem B3249437 : Blo 2165435 3249437 := bbase (se 3 (by rfl) ⟨609269, by rfl⟩ : syracuseStep 3249437 = 1218539) (by norm_num)
theorem B2166291 : Blo 2165435 2166291 := bstep (se 1 (by rfl) ⟨1624718, by rfl⟩ : syracuseStep 2166291 = 3249437) B3249437
theorem B4874165 : Blo 2165435 4874165 := bbase (se 5 (by rfl) ⟨228476, by rfl⟩ : syracuseStep 4874165 = 456953) (by norm_num)
theorem B3249443 : Blo 2165435 3249443 := bstep (se 1 (by rfl) ⟨2437082, by rfl⟩ : syracuseStep 3249443 = 4874165) B4874165
theorem B2166295 : Blo 2165435 2166295 := bstep (se 1 (by rfl) ⟨1624721, by rfl⟩ : syracuseStep 2166295 = 3249443) B3249443
theorem B6939989 : Blo 2165435 6939989 := bbase (se 12 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 6939989 = 5083) (by norm_num)
theorem B4626659 : Blo 2165435 4626659 := bstep (se 1 (by rfl) ⟨3469994, by rfl⟩ : syracuseStep 4626659 = 6939989) B6939989
theorem B12337757 : Blo 2165435 12337757 := bstep (se 3 (by rfl) ⟨2313329, by rfl⟩ : syracuseStep 12337757 = 4626659) B4626659
theorem B8225171 : Blo 2165435 8225171 := bstep (se 1 (by rfl) ⟨6168878, by rfl⟩ : syracuseStep 8225171 = 12337757) B12337757
theorem B5483447 : Blo 2165435 5483447 := bstep (se 1 (by rfl) ⟨4112585, by rfl⟩ : syracuseStep 5483447 = 8225171) B8225171
theorem B3655631 : Blo 2165435 3655631 := bstep (se 1 (by rfl) ⟨2741723, by rfl⟩ : syracuseStep 3655631 = 5483447) B5483447
theorem B2437087 : Blo 2165435 2437087 := bstep (se 1 (by rfl) ⟨1827815, by rfl⟩ : syracuseStep 2437087 = 3655631) B3655631
theorem B3249449 : Blo 2165435 3249449 := bstep (se 2 (by rfl) ⟨1218543, by rfl⟩ : syracuseStep 3249449 = 2437087) B2437087
theorem B2166299 : Blo 2165435 2166299 := bstep (se 1 (by rfl) ⟨1624724, by rfl⟩ : syracuseStep 2166299 = 3249449) B3249449
theorem B2344897 : Blo 2165435 2344897 := bbase (se 2 (by rfl) ⟨879336, by rfl⟩ : syracuseStep 2344897 = 1758673) (by norm_num)
theorem B3126529 : Blo 2165435 3126529 := bstep (se 2 (by rfl) ⟨1172448, by rfl⟩ : syracuseStep 3126529 = 2344897) B2344897
theorem B4168705 : Blo 2165435 4168705 := bstep (se 2 (by rfl) ⟨1563264, by rfl⟩ : syracuseStep 4168705 = 3126529) B3126529
theorem B5558273 : Blo 2165435 5558273 := bstep (se 2 (by rfl) ⟨2084352, by rfl⟩ : syracuseStep 5558273 = 4168705) B4168705
theorem B3705515 : Blo 2165435 3705515 := bstep (se 1 (by rfl) ⟨2779136, by rfl⟩ : syracuseStep 3705515 = 5558273) B5558273
theorem B2470343 : Blo 2165435 2470343 := bstep (se 1 (by rfl) ⟨1852757, by rfl⟩ : syracuseStep 2470343 = 3705515) B3705515
theorem B6587581 : Blo 2165435 6587581 := bstep (se 3 (by rfl) ⟨1235171, by rfl⟩ : syracuseStep 6587581 = 2470343) B2470343
theorem B8783441 : Blo 2165435 8783441 := bstep (se 2 (by rfl) ⟨3293790, by rfl⟩ : syracuseStep 8783441 = 6587581) B6587581
theorem B5855627 : Blo 2165435 5855627 := bstep (se 1 (by rfl) ⟨4391720, by rfl⟩ : syracuseStep 5855627 = 8783441) B8783441
theorem B3903751 : Blo 2165435 3903751 := bstep (se 1 (by rfl) ⟨2927813, by rfl⟩ : syracuseStep 3903751 = 5855627) B5855627
theorem B5205001 : Blo 2165435 5205001 := bstep (se 2 (by rfl) ⟨1951875, by rfl⟩ : syracuseStep 5205001 = 3903751) B3903751
theorem B6940001 : Blo 2165435 6940001 := bstep (se 2 (by rfl) ⟨2602500, by rfl⟩ : syracuseStep 6940001 = 5205001) B5205001
theorem B4626667 : Blo 2165435 4626667 := bstep (se 1 (by rfl) ⟨3470000, by rfl⟩ : syracuseStep 4626667 = 6940001) B6940001
theorem B6168889 : Blo 2165435 6168889 := bstep (se 2 (by rfl) ⟨2313333, by rfl⟩ : syracuseStep 6168889 = 4626667) B4626667
theorem B8225185 : Blo 2165435 8225185 := bstep (se 2 (by rfl) ⟨3084444, by rfl⟩ : syracuseStep 8225185 = 6168889) B6168889
theorem B10966913 : Blo 2165435 10966913 := bstep (se 2 (by rfl) ⟨4112592, by rfl⟩ : syracuseStep 10966913 = 8225185) B8225185
theorem B7311275 : Blo 2165435 7311275 := bstep (se 1 (by rfl) ⟨5483456, by rfl⟩ : syracuseStep 7311275 = 10966913) B10966913
theorem B4874183 : Blo 2165435 4874183 := bstep (se 1 (by rfl) ⟨3655637, by rfl⟩ : syracuseStep 4874183 = 7311275) B7311275
theorem B3249455 : Blo 2165435 3249455 := bstep (se 1 (by rfl) ⟨2437091, by rfl⟩ : syracuseStep 3249455 = 4874183) B4874183
theorem B2166303 : Blo 2165435 2166303 := bstep (se 1 (by rfl) ⟨1624727, by rfl⟩ : syracuseStep 2166303 = 3249455) B3249455
theorem B3249461 : Blo 2165435 3249461 := bbase (se 5 (by rfl) ⟨152318, by rfl⟩ : syracuseStep 3249461 = 304637) (by norm_num)
theorem B2166307 : Blo 2165435 2166307 := bstep (se 1 (by rfl) ⟨1624730, by rfl⟩ : syracuseStep 2166307 = 3249461) B3249461
theorem B5483477 : Blo 2165435 5483477 := bbase (se 7 (by rfl) ⟨64259, by rfl⟩ : syracuseStep 5483477 = 128519) (by norm_num)
theorem B3655651 : Blo 2165435 3655651 := bstep (se 1 (by rfl) ⟨2741738, by rfl⟩ : syracuseStep 3655651 = 5483477) B5483477
theorem B4874201 : Blo 2165435 4874201 := bstep (se 2 (by rfl) ⟨1827825, by rfl⟩ : syracuseStep 4874201 = 3655651) B3655651
theorem B3249467 : Blo 2165435 3249467 := bstep (se 1 (by rfl) ⟨2437100, by rfl⟩ : syracuseStep 3249467 = 4874201) B4874201
theorem B2166311 : Blo 2165435 2166311 := bstep (se 1 (by rfl) ⟨1624733, by rfl⟩ : syracuseStep 2166311 = 3249467) B3249467
theorem B2437105 : Blo 2165435 2437105 := bbase (se 2 (by rfl) ⟨913914, by rfl⟩ : syracuseStep 2437105 = 1827829) (by norm_num)
theorem B3249473 : Blo 2165435 3249473 := bstep (se 2 (by rfl) ⟨1218552, by rfl⟩ : syracuseStep 3249473 = 2437105) B2437105
theorem B2166315 : Blo 2165435 2166315 := bstep (se 1 (by rfl) ⟨1624736, by rfl⟩ : syracuseStep 2166315 = 3249473) B3249473
theorem B14822165 : Blo 2165435 14822165 := bbase (se 6 (by rfl) ⟨347394, by rfl⟩ : syracuseStep 14822165 = 694789) (by norm_num)
theorem B9881443 : Blo 2165435 9881443 := bstep (se 1 (by rfl) ⟨7411082, by rfl⟩ : syracuseStep 9881443 = 14822165) B14822165
theorem B52701029 : Blo 2165435 52701029 := bstep (se 4 (by rfl) ⟨4940721, by rfl⟩ : syracuseStep 52701029 = 9881443) B9881443
theorem B35134019 : Blo 2165435 35134019 := bstep (se 1 (by rfl) ⟨26350514, by rfl⟩ : syracuseStep 35134019 = 52701029) B52701029
theorem B23422679 : Blo 2165435 23422679 := bstep (se 1 (by rfl) ⟨17567009, by rfl⟩ : syracuseStep 23422679 = 35134019) B35134019
theorem B15615119 : Blo 2165435 15615119 := bstep (se 1 (by rfl) ⟨11711339, by rfl⟩ : syracuseStep 15615119 = 23422679) B23422679
theorem B10410079 : Blo 2165435 10410079 := bstep (se 1 (by rfl) ⟨7807559, by rfl⟩ : syracuseStep 10410079 = 15615119) B15615119
theorem B13880105 : Blo 2165435 13880105 := bstep (se 2 (by rfl) ⟨5205039, by rfl⟩ : syracuseStep 13880105 = 10410079) B10410079
theorem B9253403 : Blo 2165435 9253403 := bstep (se 1 (by rfl) ⟨6940052, by rfl⟩ : syracuseStep 9253403 = 13880105) B13880105
theorem B6168935 : Blo 2165435 6168935 := bstep (se 1 (by rfl) ⟨4626701, by rfl⟩ : syracuseStep 6168935 = 9253403) B9253403
theorem B4112623 : Blo 2165435 4112623 := bstep (se 1 (by rfl) ⟨3084467, by rfl⟩ : syracuseStep 4112623 = 6168935) B6168935
theorem B5483497 : Blo 2165435 5483497 := bstep (se 2 (by rfl) ⟨2056311, by rfl⟩ : syracuseStep 5483497 = 4112623) B4112623
theorem B7311329 : Blo 2165435 7311329 := bstep (se 2 (by rfl) ⟨2741748, by rfl⟩ : syracuseStep 7311329 = 5483497) B5483497
theorem B4874219 : Blo 2165435 4874219 := bstep (se 1 (by rfl) ⟨3655664, by rfl⟩ : syracuseStep 4874219 = 7311329) B7311329
theorem B3249479 : Blo 2165435 3249479 := bstep (se 1 (by rfl) ⟨2437109, by rfl⟩ : syracuseStep 3249479 = 4874219) B4874219
theorem B2166319 : Blo 2165435 2166319 := bstep (se 1 (by rfl) ⟨1624739, by rfl⟩ : syracuseStep 2166319 = 3249479) B3249479
theorem B3249485 : Blo 2165435 3249485 := bbase (se 3 (by rfl) ⟨609278, by rfl⟩ : syracuseStep 3249485 = 1218557) (by norm_num)
theorem B2166323 : Blo 2165435 2166323 := bstep (se 1 (by rfl) ⟨1624742, by rfl⟩ : syracuseStep 2166323 = 3249485) B3249485
theorem B4874237 : Blo 2165435 4874237 := bbase (se 3 (by rfl) ⟨913919, by rfl⟩ : syracuseStep 4874237 = 1827839) (by norm_num)
theorem B3249491 : Blo 2165435 3249491 := bstep (se 1 (by rfl) ⟨2437118, by rfl⟩ : syracuseStep 3249491 = 4874237) B4874237
theorem B2166327 : Blo 2165435 2166327 := bstep (se 1 (by rfl) ⟨1624745, by rfl⟩ : syracuseStep 2166327 = 3249491) B3249491
theorem B3655685 : Blo 2165435 3655685 := bbase (se 4 (by rfl) ⟨342720, by rfl⟩ : syracuseStep 3655685 = 685441) (by norm_num)
theorem B2437123 : Blo 2165435 2437123 := bstep (se 1 (by rfl) ⟨1827842, by rfl⟩ : syracuseStep 2437123 = 3655685) B3655685
theorem B3249497 : Blo 2165435 3249497 := bstep (se 2 (by rfl) ⟨1218561, by rfl⟩ : syracuseStep 3249497 = 2437123) B2437123
theorem B2166331 : Blo 2165435 2166331 := bstep (se 1 (by rfl) ⟨1624748, by rfl⟩ : syracuseStep 2166331 = 3249497) B3249497
theorem B16450613 : Blo 2165435 16450613 := bbase (se 5 (by rfl) ⟨771122, by rfl⟩ : syracuseStep 16450613 = 1542245) (by norm_num)
theorem B10967075 : Blo 2165435 10967075 := bstep (se 1 (by rfl) ⟨8225306, by rfl⟩ : syracuseStep 10967075 = 16450613) B16450613
theorem B7311383 : Blo 2165435 7311383 := bstep (se 1 (by rfl) ⟨5483537, by rfl⟩ : syracuseStep 7311383 = 10967075) B10967075
theorem B4874255 : Blo 2165435 4874255 := bstep (se 1 (by rfl) ⟨3655691, by rfl⟩ : syracuseStep 4874255 = 7311383) B7311383
theorem B3249503 : Blo 2165435 3249503 := bstep (se 1 (by rfl) ⟨2437127, by rfl⟩ : syracuseStep 3249503 = 4874255) B4874255
theorem B2166335 : Blo 2165435 2166335 := bstep (se 1 (by rfl) ⟨1624751, by rfl⟩ : syracuseStep 2166335 = 3249503) B3249503
theorem B3249509 : Blo 2165435 3249509 := bbase (se 4 (by rfl) ⟨304641, by rfl⟩ : syracuseStep 3249509 = 609283) (by norm_num)
theorem B2166339 : Blo 2165435 2166339 := bstep (se 1 (by rfl) ⟨1624754, by rfl⟩ : syracuseStep 2166339 = 3249509) B3249509
theorem B4112669 : Blo 2165435 4112669 := bbase (se 3 (by rfl) ⟨771125, by rfl⟩ : syracuseStep 4112669 = 1542251) (by norm_num)
theorem B2741779 : Blo 2165435 2741779 := bstep (se 1 (by rfl) ⟨2056334, by rfl⟩ : syracuseStep 2741779 = 4112669) B4112669
theorem B3655705 : Blo 2165435 3655705 := bstep (se 2 (by rfl) ⟨1370889, by rfl⟩ : syracuseStep 3655705 = 2741779) B2741779
theorem B4874273 : Blo 2165435 4874273 := bstep (se 2 (by rfl) ⟨1827852, by rfl⟩ : syracuseStep 4874273 = 3655705) B3655705
theorem B3249515 : Blo 2165435 3249515 := bstep (se 1 (by rfl) ⟨2437136, by rfl⟩ : syracuseStep 3249515 = 4874273) B4874273
theorem B2166343 : Blo 2165435 2166343 := bstep (se 1 (by rfl) ⟨1624757, by rfl⟩ : syracuseStep 2166343 = 3249515) B3249515
theorem B2437141 : Blo 2165435 2437141 := bbase (se 6 (by rfl) ⟨57120, by rfl⟩ : syracuseStep 2437141 = 114241) (by norm_num)
theorem B3249521 : Blo 2165435 3249521 := bstep (se 2 (by rfl) ⟨1218570, by rfl⟩ : syracuseStep 3249521 = 2437141) B2437141
theorem B2166347 : Blo 2165435 2166347 := bstep (se 1 (by rfl) ⟨1624760, by rfl⟩ : syracuseStep 2166347 = 3249521) B3249521
theorem B2741789 : Blo 2165435 2741789 := bbase (se 3 (by rfl) ⟨514085, by rfl⟩ : syracuseStep 2741789 = 1028171) (by norm_num)
theorem B7311437 : Blo 2165435 7311437 := bstep (se 3 (by rfl) ⟨1370894, by rfl⟩ : syracuseStep 7311437 = 2741789) B2741789
theorem B4874291 : Blo 2165435 4874291 := bstep (se 1 (by rfl) ⟨3655718, by rfl⟩ : syracuseStep 4874291 = 7311437) B7311437
theorem B3249527 : Blo 2165435 3249527 := bstep (se 1 (by rfl) ⟨2437145, by rfl⟩ : syracuseStep 3249527 = 4874291) B4874291
theorem B2166351 : Blo 2165435 2166351 := bstep (se 1 (by rfl) ⟨1624763, by rfl⟩ : syracuseStep 2166351 = 3249527) B3249527
theorem B3249533 : Blo 2165435 3249533 := bbase (se 3 (by rfl) ⟨609287, by rfl⟩ : syracuseStep 3249533 = 1218575) (by norm_num)
theorem B2166355 : Blo 2165435 2166355 := bstep (se 1 (by rfl) ⟨1624766, by rfl⟩ : syracuseStep 2166355 = 3249533) B3249533
theorem B4874309 : Blo 2165435 4874309 := bbase (se 4 (by rfl) ⟨456966, by rfl⟩ : syracuseStep 4874309 = 913933) (by norm_num)
theorem B3249539 : Blo 2165435 3249539 := bstep (se 1 (by rfl) ⟨2437154, by rfl⟩ : syracuseStep 3249539 = 4874309) B4874309
theorem B2166359 : Blo 2165435 2166359 := bstep (se 1 (by rfl) ⟨1624769, by rfl⟩ : syracuseStep 2166359 = 3249539) B3249539
theorem B6169061 : Blo 2165435 6169061 := bbase (se 4 (by rfl) ⟨578349, by rfl⟩ : syracuseStep 6169061 = 1156699) (by norm_num)
theorem B4112707 : Blo 2165435 4112707 := bstep (se 1 (by rfl) ⟨3084530, by rfl⟩ : syracuseStep 4112707 = 6169061) B6169061
theorem B5483609 : Blo 2165435 5483609 := bstep (se 2 (by rfl) ⟨2056353, by rfl⟩ : syracuseStep 5483609 = 4112707) B4112707
theorem B3655739 : Blo 2165435 3655739 := bstep (se 1 (by rfl) ⟨2741804, by rfl⟩ : syracuseStep 3655739 = 5483609) B5483609
theorem B2437159 : Blo 2165435 2437159 := bstep (se 1 (by rfl) ⟨1827869, by rfl⟩ : syracuseStep 2437159 = 3655739) B3655739
theorem B3249545 : Blo 2165435 3249545 := bstep (se 2 (by rfl) ⟨1218579, by rfl⟩ : syracuseStep 3249545 = 2437159) B2437159
theorem B2166363 : Blo 2165435 2166363 := bstep (se 1 (by rfl) ⟨1624772, by rfl⟩ : syracuseStep 2166363 = 3249545) B3249545
theorem B10967237 : Blo 2165435 10967237 := bbase (se 4 (by rfl) ⟨1028178, by rfl⟩ : syracuseStep 10967237 = 2056357) (by norm_num)
theorem B7311491 : Blo 2165435 7311491 := bstep (se 1 (by rfl) ⟨5483618, by rfl⟩ : syracuseStep 7311491 = 10967237) B10967237
theorem B4874327 : Blo 2165435 4874327 := bstep (se 1 (by rfl) ⟨3655745, by rfl⟩ : syracuseStep 4874327 = 7311491) B7311491
theorem B3249551 : Blo 2165435 3249551 := bstep (se 1 (by rfl) ⟨2437163, by rfl⟩ : syracuseStep 3249551 = 4874327) B4874327
theorem B2166367 : Blo 2165435 2166367 := bstep (se 1 (by rfl) ⟨1624775, by rfl⟩ : syracuseStep 2166367 = 3249551) B3249551
theorem B3249557 : Blo 2165435 3249557 := bbase (se 6 (by rfl) ⟨76161, by rfl⟩ : syracuseStep 3249557 = 152323) (by norm_num)
theorem B2166371 : Blo 2165435 2166371 := bstep (se 1 (by rfl) ⟨1624778, by rfl⟩ : syracuseStep 2166371 = 3249557) B3249557
theorem B4626821 : Blo 2165435 4626821 := bbase (se 4 (by rfl) ⟨433764, by rfl⟩ : syracuseStep 4626821 = 867529) (by norm_num)
theorem B12338189 : Blo 2165435 12338189 := bstep (se 3 (by rfl) ⟨2313410, by rfl⟩ : syracuseStep 12338189 = 4626821) B4626821
theorem B8225459 : Blo 2165435 8225459 := bstep (se 1 (by rfl) ⟨6169094, by rfl⟩ : syracuseStep 8225459 = 12338189) B12338189
theorem B5483639 : Blo 2165435 5483639 := bstep (se 1 (by rfl) ⟨4112729, by rfl⟩ : syracuseStep 5483639 = 8225459) B8225459
theorem B3655759 : Blo 2165435 3655759 := bstep (se 1 (by rfl) ⟨2741819, by rfl⟩ : syracuseStep 3655759 = 5483639) B5483639
theorem B4874345 : Blo 2165435 4874345 := bstep (se 2 (by rfl) ⟨1827879, by rfl⟩ : syracuseStep 4874345 = 3655759) B3655759
theorem B3249563 : Blo 2165435 3249563 := bstep (se 1 (by rfl) ⟨2437172, by rfl⟩ : syracuseStep 3249563 = 4874345) B4874345
theorem B2166375 : Blo 2165435 2166375 := bstep (se 1 (by rfl) ⟨1624781, by rfl⟩ : syracuseStep 2166375 = 3249563) B3249563
theorem B2437177 : Blo 2165435 2437177 := bbase (se 2 (by rfl) ⟨913941, by rfl⟩ : syracuseStep 2437177 = 1827883) (by norm_num)
theorem B3249569 : Blo 2165435 3249569 := bstep (se 2 (by rfl) ⟨1218588, by rfl⟩ : syracuseStep 3249569 = 2437177) B2437177
theorem B2166379 : Blo 2165435 2166379 := bstep (se 1 (by rfl) ⟨1624784, by rfl⟩ : syracuseStep 2166379 = 3249569) B3249569
theorem B2602597 : Blo 2165435 2602597 := bbase (se 4 (by rfl) ⟨243993, by rfl⟩ : syracuseStep 2602597 = 487987) (by norm_num)
theorem B3470129 : Blo 2165435 3470129 := bstep (se 2 (by rfl) ⟨1301298, by rfl⟩ : syracuseStep 3470129 = 2602597) B2602597
theorem B2313419 : Blo 2165435 2313419 := bstep (se 1 (by rfl) ⟨1735064, by rfl⟩ : syracuseStep 2313419 = 3470129) B3470129
theorem B6169117 : Blo 2165435 6169117 := bstep (se 3 (by rfl) ⟨1156709, by rfl⟩ : syracuseStep 6169117 = 2313419) B2313419
theorem B8225489 : Blo 2165435 8225489 := bstep (se 2 (by rfl) ⟨3084558, by rfl⟩ : syracuseStep 8225489 = 6169117) B6169117
theorem B5483659 : Blo 2165435 5483659 := bstep (se 1 (by rfl) ⟨4112744, by rfl⟩ : syracuseStep 5483659 = 8225489) B8225489
theorem B7311545 : Blo 2165435 7311545 := bstep (se 2 (by rfl) ⟨2741829, by rfl⟩ : syracuseStep 7311545 = 5483659) B5483659
theorem B4874363 : Blo 2165435 4874363 := bstep (se 1 (by rfl) ⟨3655772, by rfl⟩ : syracuseStep 4874363 = 7311545) B7311545
theorem B3249575 : Blo 2165435 3249575 := bstep (se 1 (by rfl) ⟨2437181, by rfl⟩ : syracuseStep 3249575 = 4874363) B4874363
theorem B2166383 : Blo 2165435 2166383 := bstep (se 1 (by rfl) ⟨1624787, by rfl⟩ : syracuseStep 2166383 = 3249575) B3249575
theorem B3249581 : Blo 2165435 3249581 := bbase (se 3 (by rfl) ⟨609296, by rfl⟩ : syracuseStep 3249581 = 1218593) (by norm_num)
theorem B2166387 : Blo 2165435 2166387 := bstep (se 1 (by rfl) ⟨1624790, by rfl⟩ : syracuseStep 2166387 = 3249581) B3249581
theorem B4874381 : Blo 2165435 4874381 := bbase (se 3 (by rfl) ⟨913946, by rfl⟩ : syracuseStep 4874381 = 1827893) (by norm_num)
theorem B3249587 : Blo 2165435 3249587 := bstep (se 1 (by rfl) ⟨2437190, by rfl⟩ : syracuseStep 3249587 = 4874381) B4874381
theorem B2166391 : Blo 2165435 2166391 := bstep (se 1 (by rfl) ⟨1624793, by rfl⟩ : syracuseStep 2166391 = 3249587) B3249587
theorem B2741845 : Blo 2165435 2741845 := bbase (se 8 (by rfl) ⟨16065, by rfl⟩ : syracuseStep 2741845 = 32131) (by norm_num)
theorem B3655793 : Blo 2165435 3655793 := bstep (se 2 (by rfl) ⟨1370922, by rfl⟩ : syracuseStep 3655793 = 2741845) B2741845
theorem B2437195 : Blo 2165435 2437195 := bstep (se 1 (by rfl) ⟨1827896, by rfl⟩ : syracuseStep 2437195 = 3655793) B3655793
theorem B3249593 : Blo 2165435 3249593 := bstep (se 2 (by rfl) ⟨1218597, by rfl⟩ : syracuseStep 3249593 = 2437195) B2437195
theorem B2166395 : Blo 2165435 2166395 := bstep (se 1 (by rfl) ⟨1624796, by rfl⟩ : syracuseStep 2166395 = 3249593) B3249593
theorem B31657493 : Blo 2165435 31657493 := bbase (se 6 (by rfl) ⟨741972, by rfl⟩ : syracuseStep 31657493 = 1483945) (by norm_num)
theorem B21104995 : Blo 2165435 21104995 := bstep (se 1 (by rfl) ⟨15828746, by rfl⟩ : syracuseStep 21104995 = 31657493) B31657493
theorem B28139993 : Blo 2165435 28139993 := bstep (se 2 (by rfl) ⟨10552497, by rfl⟩ : syracuseStep 28139993 = 21104995) B21104995
theorem B18759995 : Blo 2165435 18759995 := bstep (se 1 (by rfl) ⟨14069996, by rfl⟩ : syracuseStep 18759995 = 28139993) B28139993
theorem B12506663 : Blo 2165435 12506663 := bstep (se 1 (by rfl) ⟨9379997, by rfl⟩ : syracuseStep 12506663 = 18759995) B18759995
theorem B8337775 : Blo 2165435 8337775 := bstep (se 1 (by rfl) ⟨6253331, by rfl⟩ : syracuseStep 8337775 = 12506663) B12506663
theorem B11117033 : Blo 2165435 11117033 := bstep (se 2 (by rfl) ⟨4168887, by rfl⟩ : syracuseStep 11117033 = 8337775) B8337775
theorem B7411355 : Blo 2165435 7411355 := bstep (se 1 (by rfl) ⟨5558516, by rfl⟩ : syracuseStep 7411355 = 11117033) B11117033
theorem B4940903 : Blo 2165435 4940903 := bstep (se 1 (by rfl) ⟨3705677, by rfl⟩ : syracuseStep 4940903 = 7411355) B7411355
theorem B13175741 : Blo 2165435 13175741 := bstep (se 3 (by rfl) ⟨2470451, by rfl⟩ : syracuseStep 13175741 = 4940903) B4940903
theorem B35135309 : Blo 2165435 35135309 := bstep (se 3 (by rfl) ⟨6587870, by rfl⟩ : syracuseStep 35135309 = 13175741) B13175741
theorem B93694157 : Blo 2165435 93694157 := bstep (se 3 (by rfl) ⟨17567654, by rfl⟩ : syracuseStep 93694157 = 35135309) B35135309
theorem B62462771 : Blo 2165435 62462771 := bstep (se 1 (by rfl) ⟨46847078, by rfl⟩ : syracuseStep 62462771 = 93694157) B93694157
theorem B41641847 : Blo 2165435 41641847 := bstep (se 1 (by rfl) ⟨31231385, by rfl⟩ : syracuseStep 41641847 = 62462771) B62462771
theorem B27761231 : Blo 2165435 27761231 := bstep (se 1 (by rfl) ⟨20820923, by rfl⟩ : syracuseStep 27761231 = 41641847) B41641847
theorem B18507487 : Blo 2165435 18507487 := bstep (se 1 (by rfl) ⟨13880615, by rfl⟩ : syracuseStep 18507487 = 27761231) B27761231
theorem B24676649 : Blo 2165435 24676649 := bstep (se 2 (by rfl) ⟨9253743, by rfl⟩ : syracuseStep 24676649 = 18507487) B18507487
theorem B16451099 : Blo 2165435 16451099 := bstep (se 1 (by rfl) ⟨12338324, by rfl⟩ : syracuseStep 16451099 = 24676649) B24676649
theorem B10967399 : Blo 2165435 10967399 := bstep (se 1 (by rfl) ⟨8225549, by rfl⟩ : syracuseStep 10967399 = 16451099) B16451099
theorem B7311599 : Blo 2165435 7311599 := bstep (se 1 (by rfl) ⟨5483699, by rfl⟩ : syracuseStep 7311599 = 10967399) B10967399
theorem B4874399 : Blo 2165435 4874399 := bstep (se 1 (by rfl) ⟨3655799, by rfl⟩ : syracuseStep 4874399 = 7311599) B7311599
theorem B3249599 : Blo 2165435 3249599 := bstep (se 1 (by rfl) ⟨2437199, by rfl⟩ : syracuseStep 3249599 = 4874399) B4874399
theorem B2166399 : Blo 2165435 2166399 := bstep (se 1 (by rfl) ⟨1624799, by rfl⟩ : syracuseStep 2166399 = 3249599) B3249599
theorem B3249605 : Blo 2165435 3249605 := bbase (se 4 (by rfl) ⟨304650, by rfl⟩ : syracuseStep 3249605 = 609301) (by norm_num)
theorem B2166403 : Blo 2165435 2166403 := bstep (se 1 (by rfl) ⟨1624802, by rfl⟩ : syracuseStep 2166403 = 3249605) B3249605
theorem B3655813 : Blo 2165435 3655813 := bbase (se 4 (by rfl) ⟨342732, by rfl⟩ : syracuseStep 3655813 = 685465) (by norm_num)
theorem B4874417 : Blo 2165435 4874417 := bstep (se 2 (by rfl) ⟨1827906, by rfl⟩ : syracuseStep 4874417 = 3655813) B3655813
theorem B3249611 : Blo 2165435 3249611 := bstep (se 1 (by rfl) ⟨2437208, by rfl⟩ : syracuseStep 3249611 = 4874417) B4874417
theorem B2166407 : Blo 2165435 2166407 := bstep (se 1 (by rfl) ⟨1624805, by rfl⟩ : syracuseStep 2166407 = 3249611) B3249611
theorem B2437213 : Blo 2165435 2437213 := bbase (se 3 (by rfl) ⟨456977, by rfl⟩ : syracuseStep 2437213 = 913955) (by norm_num)
theorem B3249617 : Blo 2165435 3249617 := bstep (se 2 (by rfl) ⟨1218606, by rfl⟩ : syracuseStep 3249617 = 2437213) B2437213
theorem B2166411 : Blo 2165435 2166411 := bstep (se 1 (by rfl) ⟨1624808, by rfl⟩ : syracuseStep 2166411 = 3249617) B3249617
theorem B7311653 : Blo 2165435 7311653 := bbase (se 4 (by rfl) ⟨685467, by rfl⟩ : syracuseStep 7311653 = 1370935) (by norm_num)
theorem B4874435 : Blo 2165435 4874435 := bstep (se 1 (by rfl) ⟨3655826, by rfl⟩ : syracuseStep 4874435 = 7311653) B7311653
theorem B3249623 : Blo 2165435 3249623 := bstep (se 1 (by rfl) ⟨2437217, by rfl⟩ : syracuseStep 3249623 = 4874435) B4874435
theorem B2166415 : Blo 2165435 2166415 := bstep (se 1 (by rfl) ⟨1624811, by rfl⟩ : syracuseStep 2166415 = 3249623) B3249623
theorem B3249629 : Blo 2165435 3249629 := bbase (se 3 (by rfl) ⟨609305, by rfl⟩ : syracuseStep 3249629 = 1218611) (by norm_num)
theorem B2166419 : Blo 2165435 2166419 := bstep (se 1 (by rfl) ⟨1624814, by rfl⟩ : syracuseStep 2166419 = 3249629) B3249629
theorem B4874453 : Blo 2165435 4874453 := bbase (se 7 (by rfl) ⟨57122, by rfl⟩ : syracuseStep 4874453 = 114245) (by norm_num)
theorem B3249635 : Blo 2165435 3249635 := bstep (se 1 (by rfl) ⟨2437226, by rfl⟩ : syracuseStep 3249635 = 4874453) B4874453
theorem B2166423 : Blo 2165435 2166423 := bstep (se 1 (by rfl) ⟨1624817, by rfl⟩ : syracuseStep 2166423 = 3249635) B3249635
theorem B9637829 : Blo 2165435 9637829 := bbase (se 4 (by rfl) ⟨903546, by rfl⟩ : syracuseStep 9637829 = 1807093) (by norm_num)
theorem B6425219 : Blo 2165435 6425219 := bstep (se 1 (by rfl) ⟨4818914, by rfl⟩ : syracuseStep 6425219 = 9637829) B9637829
theorem B4283479 : Blo 2165435 4283479 := bstep (se 1 (by rfl) ⟨3212609, by rfl⟩ : syracuseStep 4283479 = 6425219) B6425219
theorem B5711305 : Blo 2165435 5711305 := bstep (se 2 (by rfl) ⟨2141739, by rfl⟩ : syracuseStep 5711305 = 4283479) B4283479
theorem B7615073 : Blo 2165435 7615073 := bstep (se 2 (by rfl) ⟨2855652, by rfl⟩ : syracuseStep 7615073 = 5711305) B5711305
theorem B20306861 : Blo 2165435 20306861 := bstep (se 3 (by rfl) ⟨3807536, by rfl⟩ : syracuseStep 20306861 = 7615073) B7615073
theorem B13537907 : Blo 2165435 13537907 := bstep (se 1 (by rfl) ⟨10153430, by rfl⟩ : syracuseStep 13537907 = 20306861) B20306861
theorem B9025271 : Blo 2165435 9025271 := bstep (se 1 (by rfl) ⟨6768953, by rfl⟩ : syracuseStep 9025271 = 13537907) B13537907
theorem B6016847 : Blo 2165435 6016847 := bstep (se 1 (by rfl) ⟨4512635, by rfl⟩ : syracuseStep 6016847 = 9025271) B9025271
theorem B64179701 : Blo 2165435 64179701 := bstep (se 5 (by rfl) ⟨3008423, by rfl⟩ : syracuseStep 64179701 = 6016847) B6016847
theorem B42786467 : Blo 2165435 42786467 := bstep (se 1 (by rfl) ⟨32089850, by rfl⟩ : syracuseStep 42786467 = 64179701) B64179701
theorem B28524311 : Blo 2165435 28524311 := bstep (se 1 (by rfl) ⟨21393233, by rfl⟩ : syracuseStep 28524311 = 42786467) B42786467
theorem B19016207 : Blo 2165435 19016207 := bstep (se 1 (by rfl) ⟨14262155, by rfl⟩ : syracuseStep 19016207 = 28524311) B28524311
theorem B12677471 : Blo 2165435 12677471 := bstep (se 1 (by rfl) ⟨9508103, by rfl⟩ : syracuseStep 12677471 = 19016207) B19016207
theorem B8451647 : Blo 2165435 8451647 := bstep (se 1 (by rfl) ⟨6338735, by rfl⟩ : syracuseStep 8451647 = 12677471) B12677471
theorem B5634431 : Blo 2165435 5634431 := bstep (se 1 (by rfl) ⟨4225823, by rfl⟩ : syracuseStep 5634431 = 8451647) B8451647
theorem B3756287 : Blo 2165435 3756287 := bstep (se 1 (by rfl) ⟨2817215, by rfl⟩ : syracuseStep 3756287 = 5634431) B5634431
theorem B2504191 : Blo 2165435 2504191 := bstep (se 1 (by rfl) ⟨1878143, by rfl⟩ : syracuseStep 2504191 = 3756287) B3756287
theorem B3338921 : Blo 2165435 3338921 := bstep (se 2 (by rfl) ⟨1252095, by rfl⟩ : syracuseStep 3338921 = 2504191) B2504191
theorem B8903789 : Blo 2165435 8903789 := bstep (se 3 (by rfl) ⟨1669460, by rfl⟩ : syracuseStep 8903789 = 3338921) B3338921
theorem B5935859 : Blo 2165435 5935859 := bstep (se 1 (by rfl) ⟨4451894, by rfl⟩ : syracuseStep 5935859 = 8903789) B8903789
theorem B3957239 : Blo 2165435 3957239 := bstep (se 1 (by rfl) ⟨2967929, by rfl⟩ : syracuseStep 3957239 = 5935859) B5935859
theorem B2638159 : Blo 2165435 2638159 := bstep (se 1 (by rfl) ⟨1978619, by rfl⟩ : syracuseStep 2638159 = 3957239) B3957239
theorem B14070181 : Blo 2165435 14070181 := bstep (se 4 (by rfl) ⟨1319079, by rfl⟩ : syracuseStep 14070181 = 2638159) B2638159
theorem B18760241 : Blo 2165435 18760241 := bstep (se 2 (by rfl) ⟨7035090, by rfl⟩ : syracuseStep 18760241 = 14070181) B14070181
theorem B12506827 : Blo 2165435 12506827 := bstep (se 1 (by rfl) ⟨9380120, by rfl⟩ : syracuseStep 12506827 = 18760241) B18760241
theorem B16675769 : Blo 2165435 16675769 := bstep (se 2 (by rfl) ⟨6253413, by rfl⟩ : syracuseStep 16675769 = 12506827) B12506827
theorem B11117179 : Blo 2165435 11117179 := bstep (se 1 (by rfl) ⟨8337884, by rfl⟩ : syracuseStep 11117179 = 16675769) B16675769
theorem B59291621 : Blo 2165435 59291621 := bstep (se 4 (by rfl) ⟨5558589, by rfl⟩ : syracuseStep 59291621 = 11117179) B11117179
theorem B39527747 : Blo 2165435 39527747 := bstep (se 1 (by rfl) ⟨29645810, by rfl⟩ : syracuseStep 39527747 = 59291621) B59291621
theorem B26351831 : Blo 2165435 26351831 := bstep (se 1 (by rfl) ⟨19763873, by rfl⟩ : syracuseStep 26351831 = 39527747) B39527747
theorem B17567887 : Blo 2165435 17567887 := bstep (se 1 (by rfl) ⟨13175915, by rfl⟩ : syracuseStep 17567887 = 26351831) B26351831
theorem B23423849 : Blo 2165435 23423849 := bstep (se 2 (by rfl) ⟨8783943, by rfl⟩ : syracuseStep 23423849 = 17567887) B17567887
theorem B15615899 : Blo 2165435 15615899 := bstep (se 1 (by rfl) ⟨11711924, by rfl⟩ : syracuseStep 15615899 = 23423849) B23423849
theorem B10410599 : Blo 2165435 10410599 := bstep (se 1 (by rfl) ⟨7807949, by rfl⟩ : syracuseStep 10410599 = 15615899) B15615899
theorem B6940399 : Blo 2165435 6940399 := bstep (se 1 (by rfl) ⟨5205299, by rfl⟩ : syracuseStep 6940399 = 10410599) B10410599
theorem B9253865 : Blo 2165435 9253865 := bstep (se 2 (by rfl) ⟨3470199, by rfl⟩ : syracuseStep 9253865 = 6940399) B6940399
theorem B6169243 : Blo 2165435 6169243 := bstep (se 1 (by rfl) ⟨4626932, by rfl⟩ : syracuseStep 6169243 = 9253865) B9253865
theorem B8225657 : Blo 2165435 8225657 := bstep (se 2 (by rfl) ⟨3084621, by rfl⟩ : syracuseStep 8225657 = 6169243) B6169243
theorem B5483771 : Blo 2165435 5483771 := bstep (se 1 (by rfl) ⟨4112828, by rfl⟩ : syracuseStep 5483771 = 8225657) B8225657
theorem B3655847 : Blo 2165435 3655847 := bstep (se 1 (by rfl) ⟨2741885, by rfl⟩ : syracuseStep 3655847 = 5483771) B5483771
theorem B2437231 : Blo 2165435 2437231 := bstep (se 1 (by rfl) ⟨1827923, by rfl⟩ : syracuseStep 2437231 = 3655847) B3655847
theorem B3249641 : Blo 2165435 3249641 := bstep (se 2 (by rfl) ⟨1218615, by rfl⟩ : syracuseStep 3249641 = 2437231) B2437231
theorem B2166427 : Blo 2165435 2166427 := bstep (se 1 (by rfl) ⟨1624820, by rfl⟩ : syracuseStep 2166427 = 3249641) B3249641
theorem B13880821 : Blo 2165435 13880821 := bbase (se 5 (by rfl) ⟨650663, by rfl⟩ : syracuseStep 13880821 = 1301327) (by norm_num)
theorem B18507761 : Blo 2165435 18507761 := bstep (se 2 (by rfl) ⟨6940410, by rfl⟩ : syracuseStep 18507761 = 13880821) B13880821
theorem B12338507 : Blo 2165435 12338507 := bstep (se 1 (by rfl) ⟨9253880, by rfl⟩ : syracuseStep 12338507 = 18507761) B18507761
theorem B8225671 : Blo 2165435 8225671 := bstep (se 1 (by rfl) ⟨6169253, by rfl⟩ : syracuseStep 8225671 = 12338507) B12338507
theorem B10967561 : Blo 2165435 10967561 := bstep (se 2 (by rfl) ⟨4112835, by rfl⟩ : syracuseStep 10967561 = 8225671) B8225671
theorem B7311707 : Blo 2165435 7311707 := bstep (se 1 (by rfl) ⟨5483780, by rfl⟩ : syracuseStep 7311707 = 10967561) B10967561
theorem B4874471 : Blo 2165435 4874471 := bstep (se 1 (by rfl) ⟨3655853, by rfl⟩ : syracuseStep 4874471 = 7311707) B7311707
theorem B3249647 : Blo 2165435 3249647 := bstep (se 1 (by rfl) ⟨2437235, by rfl⟩ : syracuseStep 3249647 = 4874471) B4874471
theorem B2166431 : Blo 2165435 2166431 := bstep (se 1 (by rfl) ⟨1624823, by rfl⟩ : syracuseStep 2166431 = 3249647) B3249647
theorem B3249653 : Blo 2165435 3249653 := bbase (se 5 (by rfl) ⟨152327, by rfl⟩ : syracuseStep 3249653 = 304655) (by norm_num)
theorem B2166435 : Blo 2165435 2166435 := bstep (se 1 (by rfl) ⟨1624826, by rfl⟩ : syracuseStep 2166435 = 3249653) B3249653
theorem B3903997 : Blo 2165435 3903997 := bbase (se 3 (by rfl) ⟨731999, by rfl⟩ : syracuseStep 3903997 = 1463999) (by norm_num)
theorem B5205329 : Blo 2165435 5205329 := bstep (se 2 (by rfl) ⟨1951998, by rfl⟩ : syracuseStep 5205329 = 3903997) B3903997
theorem B3470219 : Blo 2165435 3470219 := bstep (se 1 (by rfl) ⟨2602664, by rfl⟩ : syracuseStep 3470219 = 5205329) B5205329
theorem B2313479 : Blo 2165435 2313479 := bstep (se 1 (by rfl) ⟨1735109, by rfl⟩ : syracuseStep 2313479 = 3470219) B3470219
theorem B6169277 : Blo 2165435 6169277 := bstep (se 3 (by rfl) ⟨1156739, by rfl⟩ : syracuseStep 6169277 = 2313479) B2313479
theorem B4112851 : Blo 2165435 4112851 := bstep (se 1 (by rfl) ⟨3084638, by rfl⟩ : syracuseStep 4112851 = 6169277) B6169277
theorem B5483801 : Blo 2165435 5483801 := bstep (se 2 (by rfl) ⟨2056425, by rfl⟩ : syracuseStep 5483801 = 4112851) B4112851
theorem B3655867 : Blo 2165435 3655867 := bstep (se 1 (by rfl) ⟨2741900, by rfl⟩ : syracuseStep 3655867 = 5483801) B5483801
theorem B4874489 : Blo 2165435 4874489 := bstep (se 2 (by rfl) ⟨1827933, by rfl⟩ : syracuseStep 4874489 = 3655867) B3655867
theorem B3249659 : Blo 2165435 3249659 := bstep (se 1 (by rfl) ⟨2437244, by rfl⟩ : syracuseStep 3249659 = 4874489) B4874489
theorem B2166439 : Blo 2165435 2166439 := bstep (se 1 (by rfl) ⟨1624829, by rfl⟩ : syracuseStep 2166439 = 3249659) B3249659
theorem B2437249 : Blo 2165435 2437249 := bbase (se 2 (by rfl) ⟨913968, by rfl⟩ : syracuseStep 2437249 = 1827937) (by norm_num)
theorem B3249665 : Blo 2165435 3249665 := bstep (se 2 (by rfl) ⟨1218624, by rfl⟩ : syracuseStep 3249665 = 2437249) B2437249
theorem B2166443 : Blo 2165435 2166443 := bstep (se 1 (by rfl) ⟨1624832, by rfl⟩ : syracuseStep 2166443 = 3249665) B3249665
theorem B5483821 : Blo 2165435 5483821 := bbase (se 3 (by rfl) ⟨1028216, by rfl⟩ : syracuseStep 5483821 = 2056433) (by norm_num)
theorem B7311761 : Blo 2165435 7311761 := bstep (se 2 (by rfl) ⟨2741910, by rfl⟩ : syracuseStep 7311761 = 5483821) B5483821
theorem B4874507 : Blo 2165435 4874507 := bstep (se 1 (by rfl) ⟨3655880, by rfl⟩ : syracuseStep 4874507 = 7311761) B7311761
theorem B3249671 : Blo 2165435 3249671 := bstep (se 1 (by rfl) ⟨2437253, by rfl⟩ : syracuseStep 3249671 = 4874507) B4874507
theorem B2166447 : Blo 2165435 2166447 := bstep (se 1 (by rfl) ⟨1624835, by rfl⟩ : syracuseStep 2166447 = 3249671) B3249671
theorem B3249677 : Blo 2165435 3249677 := bbase (se 3 (by rfl) ⟨609314, by rfl⟩ : syracuseStep 3249677 = 1218629) (by norm_num)
theorem B2166451 : Blo 2165435 2166451 := bstep (se 1 (by rfl) ⟨1624838, by rfl⟩ : syracuseStep 2166451 = 3249677) B3249677
theorem B4874525 : Blo 2165435 4874525 := bbase (se 3 (by rfl) ⟨913973, by rfl⟩ : syracuseStep 4874525 = 1827947) (by norm_num)
theorem B3249683 : Blo 2165435 3249683 := bstep (se 1 (by rfl) ⟨2437262, by rfl⟩ : syracuseStep 3249683 = 4874525) B4874525
theorem B2166455 : Blo 2165435 2166455 := bstep (se 1 (by rfl) ⟨1624841, by rfl⟩ : syracuseStep 2166455 = 3249683) B3249683
theorem B3655901 : Blo 2165435 3655901 := bbase (se 3 (by rfl) ⟨685481, by rfl⟩ : syracuseStep 3655901 = 1370963) (by norm_num)
theorem B2437267 : Blo 2165435 2437267 := bstep (se 1 (by rfl) ⟨1827950, by rfl⟩ : syracuseStep 2437267 = 3655901) B3655901
theorem B3249689 : Blo 2165435 3249689 := bstep (se 2 (by rfl) ⟨1218633, by rfl⟩ : syracuseStep 3249689 = 2437267) B2437267
theorem B2166459 : Blo 2165435 2166459 := bstep (se 1 (by rfl) ⟨1624844, by rfl⟩ : syracuseStep 2166459 = 3249689) B3249689
theorem B9882101 : Blo 2165435 9882101 := bbase (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) (by norm_num)
theorem B6588067 : Blo 2165435 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B8784089 : Blo 2165435 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B5856059 : Blo 2165435 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B3904039 : Blo 2165435 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B5205385 : Blo 2165435 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B6940513 : Blo 2165435 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B9254017 : Blo 2165435 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B12338689 : Blo 2165435 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B16451585 : Blo 2165435 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B10967723 : Blo 2165435 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B7311815 : Blo 2165435 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B4874543 : Blo 2165435 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B3249695 : Blo 2165435 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B2166463 : Blo 2165435 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B3249701 : Blo 2165435 3249701 := bbase (se 4 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 3249701 = 609319) (by norm_num)
theorem B2166467 : Blo 2165435 2166467 := bstep (se 1 (by rfl) ⟨1624850, by rfl⟩ : syracuseStep 2166467 = 3249701) B3249701
theorem B2741941 : Blo 2165435 2741941 := bbase (se 5 (by rfl) ⟨128528, by rfl⟩ : syracuseStep 2741941 = 257057) (by norm_num)
theorem B3655921 : Blo 2165435 3655921 := bstep (se 2 (by rfl) ⟨1370970, by rfl⟩ : syracuseStep 3655921 = 2741941) B2741941
theorem B4874561 : Blo 2165435 4874561 := bstep (se 2 (by rfl) ⟨1827960, by rfl⟩ : syracuseStep 4874561 = 3655921) B3655921
theorem B3249707 : Blo 2165435 3249707 := bstep (se 1 (by rfl) ⟨2437280, by rfl⟩ : syracuseStep 3249707 = 4874561) B4874561
theorem B2166471 : Blo 2165435 2166471 := bstep (se 1 (by rfl) ⟨1624853, by rfl⟩ : syracuseStep 2166471 = 3249707) B3249707
theorem B2437285 : Blo 2165435 2437285 := bbase (se 4 (by rfl) ⟨228495, by rfl⟩ : syracuseStep 2437285 = 456991) (by norm_num)
theorem B3249713 : Blo 2165435 3249713 := bstep (se 2 (by rfl) ⟨1218642, by rfl⟩ : syracuseStep 3249713 = 2437285) B2437285
theorem B2166475 : Blo 2165435 2166475 := bstep (se 1 (by rfl) ⟨1624856, by rfl⟩ : syracuseStep 2166475 = 3249713) B3249713
theorem B4392077 : Blo 2165435 4392077 := bbase (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) (by norm_num)
theorem B11712205 : Blo 2165435 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B15616273 : Blo 2165435 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B20821697 : Blo 2165435 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B13881131 : Blo 2165435 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B9254087 : Blo 2165435 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B6169391 : Blo 2165435 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B4112927 : Blo 2165435 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B2741951 : Blo 2165435 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B7311869 : Blo 2165435 7311869 := bstep (se 3 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 7311869 = 2741951) B2741951
theorem B4874579 : Blo 2165435 4874579 := bstep (se 1 (by rfl) ⟨3655934, by rfl⟩ : syracuseStep 4874579 = 7311869) B7311869
theorem B3249719 : Blo 2165435 3249719 := bstep (se 1 (by rfl) ⟨2437289, by rfl⟩ : syracuseStep 3249719 = 4874579) B4874579
theorem B2166479 : Blo 2165435 2166479 := bstep (se 1 (by rfl) ⟨1624859, by rfl⟩ : syracuseStep 2166479 = 3249719) B3249719
theorem B3249725 : Blo 2165435 3249725 := bbase (se 3 (by rfl) ⟨609323, by rfl⟩ : syracuseStep 3249725 = 1218647) (by norm_num)
theorem B2166483 : Blo 2165435 2166483 := bstep (se 1 (by rfl) ⟨1624862, by rfl⟩ : syracuseStep 2166483 = 3249725) B3249725
theorem B4874597 : Blo 2165435 4874597 := bbase (se 4 (by rfl) ⟨456993, by rfl⟩ : syracuseStep 4874597 = 913987) (by norm_num)
theorem B3249731 : Blo 2165435 3249731 := bstep (se 1 (by rfl) ⟨2437298, by rfl⟩ : syracuseStep 3249731 = 4874597) B4874597
theorem B2166487 : Blo 2165435 2166487 := bstep (se 1 (by rfl) ⟨1624865, by rfl⟩ : syracuseStep 2166487 = 3249731) B3249731
theorem B5483933 : Blo 2165435 5483933 := bbase (se 3 (by rfl) ⟨1028237, by rfl⟩ : syracuseStep 5483933 = 2056475) (by norm_num)
theorem B3655955 : Blo 2165435 3655955 := bstep (se 1 (by rfl) ⟨2741966, by rfl⟩ : syracuseStep 3655955 = 5483933) B5483933
theorem B2437303 : Blo 2165435 2437303 := bstep (se 1 (by rfl) ⟨1827977, by rfl⟩ : syracuseStep 2437303 = 3655955) B3655955
theorem B3249737 : Blo 2165435 3249737 := bstep (se 2 (by rfl) ⟨1218651, by rfl⟩ : syracuseStep 3249737 = 2437303) B2437303
theorem B2166491 : Blo 2165435 2166491 := bstep (se 1 (by rfl) ⟨1624868, by rfl⟩ : syracuseStep 2166491 = 3249737) B3249737
theorem B4112957 : Blo 2165435 4112957 := bbase (se 3 (by rfl) ⟨771179, by rfl⟩ : syracuseStep 4112957 = 1542359) (by norm_num)
theorem B10967885 : Blo 2165435 10967885 := bstep (se 3 (by rfl) ⟨2056478, by rfl⟩ : syracuseStep 10967885 = 4112957) B4112957
theorem B7311923 : Blo 2165435 7311923 := bstep (se 1 (by rfl) ⟨5483942, by rfl⟩ : syracuseStep 7311923 = 10967885) B10967885
theorem B4874615 : Blo 2165435 4874615 := bstep (se 1 (by rfl) ⟨3655961, by rfl⟩ : syracuseStep 4874615 = 7311923) B7311923
theorem B3249743 : Blo 2165435 3249743 := bstep (se 1 (by rfl) ⟨2437307, by rfl⟩ : syracuseStep 3249743 = 4874615) B4874615
theorem B2166495 : Blo 2165435 2166495 := bstep (se 1 (by rfl) ⟨1624871, by rfl⟩ : syracuseStep 2166495 = 3249743) B3249743
theorem B3249749 : Blo 2165435 3249749 := bbase (se 8 (by rfl) ⟨19041, by rfl⟩ : syracuseStep 3249749 = 38083) (by norm_num)
theorem B2166499 : Blo 2165435 2166499 := bstep (se 1 (by rfl) ⟨1624874, by rfl⟩ : syracuseStep 2166499 = 3249749) B3249749
theorem B2602741 : Blo 2165435 2602741 := bbase (se 5 (by rfl) ⟨122003, by rfl⟩ : syracuseStep 2602741 = 244007) (by norm_num)
theorem B3470321 : Blo 2165435 3470321 := bstep (se 2 (by rfl) ⟨1301370, by rfl⟩ : syracuseStep 3470321 = 2602741) B2602741
theorem B9254189 : Blo 2165435 9254189 := bstep (se 3 (by rfl) ⟨1735160, by rfl⟩ : syracuseStep 9254189 = 3470321) B3470321
theorem B6169459 : Blo 2165435 6169459 := bstep (se 1 (by rfl) ⟨4627094, by rfl⟩ : syracuseStep 6169459 = 9254189) B9254189
theorem B8225945 : Blo 2165435 8225945 := bstep (se 2 (by rfl) ⟨3084729, by rfl⟩ : syracuseStep 8225945 = 6169459) B6169459
theorem B5483963 : Blo 2165435 5483963 := bstep (se 1 (by rfl) ⟨4112972, by rfl⟩ : syracuseStep 5483963 = 8225945) B8225945
theorem B3655975 : Blo 2165435 3655975 := bstep (se 1 (by rfl) ⟨2741981, by rfl⟩ : syracuseStep 3655975 = 5483963) B5483963
theorem B4874633 : Blo 2165435 4874633 := bstep (se 2 (by rfl) ⟨1827987, by rfl⟩ : syracuseStep 4874633 = 3655975) B3655975
theorem B3249755 : Blo 2165435 3249755 := bstep (se 1 (by rfl) ⟨2437316, by rfl⟩ : syracuseStep 3249755 = 4874633) B4874633
theorem B2166503 : Blo 2165435 2166503 := bstep (se 1 (by rfl) ⟨1624877, by rfl⟩ : syracuseStep 2166503 = 3249755) B3249755
theorem B2437321 : Blo 2165435 2437321 := bbase (se 2 (by rfl) ⟨913995, by rfl⟩ : syracuseStep 2437321 = 1827991) (by norm_num)
theorem B3249761 : Blo 2165435 3249761 := bstep (se 2 (by rfl) ⟨1218660, by rfl⟩ : syracuseStep 3249761 = 2437321) B2437321
theorem B2166507 : Blo 2165435 2166507 := bstep (se 1 (by rfl) ⟨1624880, by rfl⟩ : syracuseStep 2166507 = 3249761) B3249761
theorem B2377117 : Blo 2165435 2377117 := bbase (se 3 (by rfl) ⟨445709, by rfl⟩ : syracuseStep 2377117 = 891419) (by norm_num)
theorem B3169489 : Blo 2165435 3169489 := bstep (se 2 (by rfl) ⟨1188558, by rfl⟩ : syracuseStep 3169489 = 2377117) B2377117
theorem B4225985 : Blo 2165435 4225985 := bstep (se 2 (by rfl) ⟨1584744, by rfl⟩ : syracuseStep 4225985 = 3169489) B3169489
theorem B2817323 : Blo 2165435 2817323 := bstep (se 1 (by rfl) ⟨2112992, by rfl⟩ : syracuseStep 2817323 = 4225985) B4225985
theorem B30051445 : Blo 2165435 30051445 := bstep (se 5 (by rfl) ⟨1408661, by rfl⟩ : syracuseStep 30051445 = 2817323) B2817323
theorem B40068593 : Blo 2165435 40068593 := bstep (se 2 (by rfl) ⟨15025722, by rfl⟩ : syracuseStep 40068593 = 30051445) B30051445
theorem B26712395 : Blo 2165435 26712395 := bstep (se 1 (by rfl) ⟨20034296, by rfl⟩ : syracuseStep 26712395 = 40068593) B40068593
theorem B17808263 : Blo 2165435 17808263 := bstep (se 1 (by rfl) ⟨13356197, by rfl⟩ : syracuseStep 17808263 = 26712395) B26712395
theorem B11872175 : Blo 2165435 11872175 := bstep (se 1 (by rfl) ⟨8904131, by rfl⟩ : syracuseStep 11872175 = 17808263) B17808263
theorem B31659133 : Blo 2165435 31659133 := bstep (se 3 (by rfl) ⟨5936087, by rfl⟩ : syracuseStep 31659133 = 11872175) B11872175
theorem B42212177 : Blo 2165435 42212177 := bstep (se 2 (by rfl) ⟨15829566, by rfl⟩ : syracuseStep 42212177 = 31659133) B31659133
theorem B28141451 : Blo 2165435 28141451 := bstep (se 1 (by rfl) ⟨21106088, by rfl⟩ : syracuseStep 28141451 = 42212177) B42212177
theorem B18760967 : Blo 2165435 18760967 := bstep (se 1 (by rfl) ⟨14070725, by rfl⟩ : syracuseStep 18760967 = 28141451) B28141451
theorem B12507311 : Blo 2165435 12507311 := bstep (se 1 (by rfl) ⟨9380483, by rfl⟩ : syracuseStep 12507311 = 18760967) B18760967
theorem B33352829 : Blo 2165435 33352829 := bstep (se 3 (by rfl) ⟨6253655, by rfl⟩ : syracuseStep 33352829 = 12507311) B12507311
theorem B22235219 : Blo 2165435 22235219 := bstep (se 1 (by rfl) ⟨16676414, by rfl⟩ : syracuseStep 22235219 = 33352829) B33352829
theorem B14823479 : Blo 2165435 14823479 := bstep (se 1 (by rfl) ⟨11117609, by rfl⟩ : syracuseStep 14823479 = 22235219) B22235219
theorem B9882319 : Blo 2165435 9882319 := bstep (se 1 (by rfl) ⟨7411739, by rfl⟩ : syracuseStep 9882319 = 14823479) B14823479
theorem B13176425 : Blo 2165435 13176425 := bstep (se 2 (by rfl) ⟨4941159, by rfl⟩ : syracuseStep 13176425 = 9882319) B9882319
theorem B8784283 : Blo 2165435 8784283 := bstep (se 1 (by rfl) ⟨6588212, by rfl⟩ : syracuseStep 8784283 = 13176425) B13176425
theorem B11712377 : Blo 2165435 11712377 := bstep (se 2 (by rfl) ⟨4392141, by rfl⟩ : syracuseStep 11712377 = 8784283) B8784283
theorem B7808251 : Blo 2165435 7808251 := bstep (se 1 (by rfl) ⟨5856188, by rfl⟩ : syracuseStep 7808251 = 11712377) B11712377
theorem B10411001 : Blo 2165435 10411001 := bstep (se 2 (by rfl) ⟨3904125, by rfl⟩ : syracuseStep 10411001 = 7808251) B7808251
theorem B6940667 : Blo 2165435 6940667 := bstep (se 1 (by rfl) ⟨5205500, by rfl⟩ : syracuseStep 6940667 = 10411001) B10411001
theorem B18508445 : Blo 2165435 18508445 := bstep (se 3 (by rfl) ⟨3470333, by rfl⟩ : syracuseStep 18508445 = 6940667) B6940667
theorem B12338963 : Blo 2165435 12338963 := bstep (se 1 (by rfl) ⟨9254222, by rfl⟩ : syracuseStep 12338963 = 18508445) B18508445
theorem B8225975 : Blo 2165435 8225975 := bstep (se 1 (by rfl) ⟨6169481, by rfl⟩ : syracuseStep 8225975 = 12338963) B12338963
theorem B5483983 : Blo 2165435 5483983 := bstep (se 1 (by rfl) ⟨4112987, by rfl⟩ : syracuseStep 5483983 = 8225975) B8225975
theorem B7311977 : Blo 2165435 7311977 := bstep (se 2 (by rfl) ⟨2741991, by rfl⟩ : syracuseStep 7311977 = 5483983) B5483983
theorem B4874651 : Blo 2165435 4874651 := bstep (se 1 (by rfl) ⟨3655988, by rfl⟩ : syracuseStep 4874651 = 7311977) B7311977
theorem B3249767 : Blo 2165435 3249767 := bstep (se 1 (by rfl) ⟨2437325, by rfl⟩ : syracuseStep 3249767 = 4874651) B4874651
theorem B2166511 : Blo 2165435 2166511 := bstep (se 1 (by rfl) ⟨1624883, by rfl⟩ : syracuseStep 2166511 = 3249767) B3249767
theorem B3249773 : Blo 2165435 3249773 := bbase (se 3 (by rfl) ⟨609332, by rfl⟩ : syracuseStep 3249773 = 1218665) (by norm_num)
theorem B2166515 : Blo 2165435 2166515 := bstep (se 1 (by rfl) ⟨1624886, by rfl⟩ : syracuseStep 2166515 = 3249773) B3249773
theorem B4874669 : Blo 2165435 4874669 := bbase (se 3 (by rfl) ⟨914000, by rfl⟩ : syracuseStep 4874669 = 1828001) (by norm_num)
theorem B3249779 : Blo 2165435 3249779 := bstep (se 1 (by rfl) ⟨2437334, by rfl⟩ : syracuseStep 3249779 = 4874669) B4874669
theorem B2166519 : Blo 2165435 2166519 := bstep (se 1 (by rfl) ⟨1624889, by rfl⟩ : syracuseStep 2166519 = 3249779) B3249779
theorem B2313569 : Blo 2165435 2313569 := bbase (se 2 (by rfl) ⟨867588, by rfl⟩ : syracuseStep 2313569 = 1735177) (by norm_num)
theorem B6169517 : Blo 2165435 6169517 := bstep (se 3 (by rfl) ⟨1156784, by rfl⟩ : syracuseStep 6169517 = 2313569) B2313569
theorem B4113011 : Blo 2165435 4113011 := bstep (se 1 (by rfl) ⟨3084758, by rfl⟩ : syracuseStep 4113011 = 6169517) B6169517
theorem B2742007 : Blo 2165435 2742007 := bstep (se 1 (by rfl) ⟨2056505, by rfl⟩ : syracuseStep 2742007 = 4113011) B4113011
theorem B3656009 : Blo 2165435 3656009 := bstep (se 2 (by rfl) ⟨1371003, by rfl⟩ : syracuseStep 3656009 = 2742007) B2742007
theorem B2437339 : Blo 2165435 2437339 := bstep (se 1 (by rfl) ⟨1828004, by rfl⟩ : syracuseStep 2437339 = 3656009) B3656009
theorem B3249785 : Blo 2165435 3249785 := bstep (se 2 (by rfl) ⟨1218669, by rfl⟩ : syracuseStep 3249785 = 2437339) B2437339
theorem B2166523 : Blo 2165435 2166523 := bstep (se 1 (by rfl) ⟨1624892, by rfl⟩ : syracuseStep 2166523 = 3249785) B3249785
theorem B16676533 : Blo 2165435 16676533 := bbase (se 5 (by rfl) ⟨781712, by rfl⟩ : syracuseStep 16676533 = 1563425) (by norm_num)
theorem B88941509 : Blo 2165435 88941509 := bstep (se 4 (by rfl) ⟨8338266, by rfl⟩ : syracuseStep 88941509 = 16676533) B16676533
theorem B59294339 : Blo 2165435 59294339 := bstep (se 1 (by rfl) ⟨44470754, by rfl⟩ : syracuseStep 59294339 = 88941509) B88941509
theorem B39529559 : Blo 2165435 39529559 := bstep (se 1 (by rfl) ⟨29647169, by rfl⟩ : syracuseStep 39529559 = 59294339) B59294339
theorem B26353039 : Blo 2165435 26353039 := bstep (se 1 (by rfl) ⟨19764779, by rfl⟩ : syracuseStep 26353039 = 39529559) B39529559
theorem B35137385 : Blo 2165435 35137385 := bstep (se 2 (by rfl) ⟨13176519, by rfl⟩ : syracuseStep 35137385 = 26353039) B26353039
theorem B23424923 : Blo 2165435 23424923 := bstep (se 1 (by rfl) ⟨17568692, by rfl⟩ : syracuseStep 23424923 = 35137385) B35137385
theorem B62466461 : Blo 2165435 62466461 := bstep (se 3 (by rfl) ⟨11712461, by rfl⟩ : syracuseStep 62466461 = 23424923) B23424923
theorem B41644307 : Blo 2165435 41644307 := bstep (se 1 (by rfl) ⟨31233230, by rfl⟩ : syracuseStep 41644307 = 62466461) B62466461
theorem B27762871 : Blo 2165435 27762871 := bstep (se 1 (by rfl) ⟨20822153, by rfl⟩ : syracuseStep 27762871 = 41644307) B41644307
theorem B37017161 : Blo 2165435 37017161 := bstep (se 2 (by rfl) ⟨13881435, by rfl⟩ : syracuseStep 37017161 = 27762871) B27762871
theorem B24678107 : Blo 2165435 24678107 := bstep (se 1 (by rfl) ⟨18508580, by rfl⟩ : syracuseStep 24678107 = 37017161) B37017161
theorem B16452071 : Blo 2165435 16452071 := bstep (se 1 (by rfl) ⟨12339053, by rfl⟩ : syracuseStep 16452071 = 24678107) B24678107
theorem B10968047 : Blo 2165435 10968047 := bstep (se 1 (by rfl) ⟨8226035, by rfl⟩ : syracuseStep 10968047 = 16452071) B16452071
theorem B7312031 : Blo 2165435 7312031 := bstep (se 1 (by rfl) ⟨5484023, by rfl⟩ : syracuseStep 7312031 = 10968047) B10968047
theorem B4874687 : Blo 2165435 4874687 := bstep (se 1 (by rfl) ⟨3656015, by rfl⟩ : syracuseStep 4874687 = 7312031) B7312031
theorem B3249791 : Blo 2165435 3249791 := bstep (se 1 (by rfl) ⟨2437343, by rfl⟩ : syracuseStep 3249791 = 4874687) B4874687
theorem B2166527 : Blo 2165435 2166527 := bstep (se 1 (by rfl) ⟨1624895, by rfl⟩ : syracuseStep 2166527 = 3249791) B3249791
theorem B3249797 : Blo 2165435 3249797 := bbase (se 4 (by rfl) ⟨304668, by rfl⟩ : syracuseStep 3249797 = 609337) (by norm_num)
theorem B2166531 : Blo 2165435 2166531 := bstep (se 1 (by rfl) ⟨1624898, by rfl⟩ : syracuseStep 2166531 = 3249797) B3249797
theorem B3656029 : Blo 2165435 3656029 := bbase (se 3 (by rfl) ⟨685505, by rfl⟩ : syracuseStep 3656029 = 1371011) (by norm_num)
theorem B4874705 : Blo 2165435 4874705 := bstep (se 2 (by rfl) ⟨1828014, by rfl⟩ : syracuseStep 4874705 = 3656029) B3656029
theorem B3249803 : Blo 2165435 3249803 := bstep (se 1 (by rfl) ⟨2437352, by rfl⟩ : syracuseStep 3249803 = 4874705) B4874705
theorem B2166535 : Blo 2165435 2166535 := bstep (se 1 (by rfl) ⟨1624901, by rfl⟩ : syracuseStep 2166535 = 3249803) B3249803
theorem B2437357 : Blo 2165435 2437357 := bbase (se 3 (by rfl) ⟨457004, by rfl⟩ : syracuseStep 2437357 = 914009) (by norm_num)
theorem B3249809 : Blo 2165435 3249809 := bstep (se 2 (by rfl) ⟨1218678, by rfl⟩ : syracuseStep 3249809 = 2437357) B2437357
theorem B2166539 : Blo 2165435 2166539 := bstep (se 1 (by rfl) ⟨1624904, by rfl⟩ : syracuseStep 2166539 = 3249809) B3249809
theorem B7312085 : Blo 2165435 7312085 := bbase (se 7 (by rfl) ⟨85688, by rfl⟩ : syracuseStep 7312085 = 171377) (by norm_num)
theorem B4874723 : Blo 2165435 4874723 := bstep (se 1 (by rfl) ⟨3656042, by rfl⟩ : syracuseStep 4874723 = 7312085) B7312085
theorem B3249815 : Blo 2165435 3249815 := bstep (se 1 (by rfl) ⟨2437361, by rfl⟩ : syracuseStep 3249815 = 4874723) B4874723
theorem B2166543 : Blo 2165435 2166543 := bstep (se 1 (by rfl) ⟨1624907, by rfl⟩ : syracuseStep 2166543 = 3249815) B3249815
theorem B3249821 : Blo 2165435 3249821 := bbase (se 3 (by rfl) ⟨609341, by rfl⟩ : syracuseStep 3249821 = 1218683) (by norm_num)
theorem B2166547 : Blo 2165435 2166547 := bstep (se 1 (by rfl) ⟨1624910, by rfl⟩ : syracuseStep 2166547 = 3249821) B3249821
theorem B4874741 : Blo 2165435 4874741 := bbase (se 5 (by rfl) ⟨228503, by rfl⟩ : syracuseStep 4874741 = 457007) (by norm_num)
theorem B3249827 : Blo 2165435 3249827 := bstep (se 1 (by rfl) ⟨2437370, by rfl⟩ : syracuseStep 3249827 = 4874741) B4874741
theorem B2166551 : Blo 2165435 2166551 := bstep (se 1 (by rfl) ⟨1624913, by rfl⟩ : syracuseStep 2166551 = 3249827) B3249827
theorem B3904205 : Blo 2165435 3904205 := bbase (se 3 (by rfl) ⟨732038, by rfl⟩ : syracuseStep 3904205 = 1464077) (by norm_num)
theorem B41644853 : Blo 2165435 41644853 := bstep (se 5 (by rfl) ⟨1952102, by rfl⟩ : syracuseStep 41644853 = 3904205) B3904205
theorem B27763235 : Blo 2165435 27763235 := bstep (se 1 (by rfl) ⟨20822426, by rfl⟩ : syracuseStep 27763235 = 41644853) B41644853
theorem B18508823 : Blo 2165435 18508823 := bstep (se 1 (by rfl) ⟨13881617, by rfl⟩ : syracuseStep 18508823 = 27763235) B27763235
theorem B12339215 : Blo 2165435 12339215 := bstep (se 1 (by rfl) ⟨9254411, by rfl⟩ : syracuseStep 12339215 = 18508823) B18508823
theorem B8226143 : Blo 2165435 8226143 := bstep (se 1 (by rfl) ⟨6169607, by rfl⟩ : syracuseStep 8226143 = 12339215) B12339215
theorem B5484095 : Blo 2165435 5484095 := bstep (se 1 (by rfl) ⟨4113071, by rfl⟩ : syracuseStep 5484095 = 8226143) B8226143
theorem B3656063 : Blo 2165435 3656063 := bstep (se 1 (by rfl) ⟨2742047, by rfl⟩ : syracuseStep 3656063 = 5484095) B5484095
theorem B2437375 : Blo 2165435 2437375 := bstep (se 1 (by rfl) ⟨1828031, by rfl⟩ : syracuseStep 2437375 = 3656063) B3656063
theorem B3249833 : Blo 2165435 3249833 := bstep (se 2 (by rfl) ⟨1218687, by rfl⟩ : syracuseStep 3249833 = 2437375) B2437375
theorem B2166555 : Blo 2165435 2166555 := bstep (se 1 (by rfl) ⟨1624916, by rfl⟩ : syracuseStep 2166555 = 3249833) B3249833
theorem B3904213 : Blo 2165435 3904213 := bbase (se 7 (by rfl) ⟨45752, by rfl⟩ : syracuseStep 3904213 = 91505) (by norm_num)
theorem B5205617 : Blo 2165435 5205617 := bstep (se 2 (by rfl) ⟨1952106, by rfl⟩ : syracuseStep 5205617 = 3904213) B3904213
theorem B3470411 : Blo 2165435 3470411 := bstep (se 1 (by rfl) ⟨2602808, by rfl⟩ : syracuseStep 3470411 = 5205617) B5205617
theorem B2313607 : Blo 2165435 2313607 := bstep (se 1 (by rfl) ⟨1735205, by rfl⟩ : syracuseStep 2313607 = 3470411) B3470411
theorem B3084809 : Blo 2165435 3084809 := bstep (se 2 (by rfl) ⟨1156803, by rfl⟩ : syracuseStep 3084809 = 2313607) B2313607
theorem B8226157 : Blo 2165435 8226157 := bstep (se 3 (by rfl) ⟨1542404, by rfl⟩ : syracuseStep 8226157 = 3084809) B3084809
theorem B10968209 : Blo 2165435 10968209 := bstep (se 2 (by rfl) ⟨4113078, by rfl⟩ : syracuseStep 10968209 = 8226157) B8226157
theorem B7312139 : Blo 2165435 7312139 := bstep (se 1 (by rfl) ⟨5484104, by rfl⟩ : syracuseStep 7312139 = 10968209) B10968209
theorem B4874759 : Blo 2165435 4874759 := bstep (se 1 (by rfl) ⟨3656069, by rfl⟩ : syracuseStep 4874759 = 7312139) B7312139
theorem B3249839 : Blo 2165435 3249839 := bstep (se 1 (by rfl) ⟨2437379, by rfl⟩ : syracuseStep 3249839 = 4874759) B4874759
theorem B2166559 : Blo 2165435 2166559 := bstep (se 1 (by rfl) ⟨1624919, by rfl⟩ : syracuseStep 2166559 = 3249839) B3249839
theorem B3249845 : Blo 2165435 3249845 := bbase (se 5 (by rfl) ⟨152336, by rfl⟩ : syracuseStep 3249845 = 304673) (by norm_num)
theorem B2166563 : Blo 2165435 2166563 := bstep (se 1 (by rfl) ⟨1624922, by rfl⟩ : syracuseStep 2166563 = 3249845) B3249845
theorem B5484125 : Blo 2165435 5484125 := bbase (se 3 (by rfl) ⟨1028273, by rfl⟩ : syracuseStep 5484125 = 2056547) (by norm_num)
theorem B3656083 : Blo 2165435 3656083 := bstep (se 1 (by rfl) ⟨2742062, by rfl⟩ : syracuseStep 3656083 = 5484125) B5484125
theorem B4874777 : Blo 2165435 4874777 := bstep (se 2 (by rfl) ⟨1828041, by rfl⟩ : syracuseStep 4874777 = 3656083) B3656083
theorem B3249851 : Blo 2165435 3249851 := bstep (se 1 (by rfl) ⟨2437388, by rfl⟩ : syracuseStep 3249851 = 4874777) B4874777
theorem B2166567 : Blo 2165435 2166567 := bstep (se 1 (by rfl) ⟨1624925, by rfl⟩ : syracuseStep 2166567 = 3249851) B3249851
theorem B2437393 : Blo 2165435 2437393 := bbase (se 2 (by rfl) ⟨914022, by rfl⟩ : syracuseStep 2437393 = 1828045) (by norm_num)
theorem B3249857 : Blo 2165435 3249857 := bstep (se 2 (by rfl) ⟨1218696, by rfl⟩ : syracuseStep 3249857 = 2437393) B2437393
theorem B2166571 : Blo 2165435 2166571 := bstep (se 1 (by rfl) ⟨1624928, by rfl⟩ : syracuseStep 2166571 = 3249857) B3249857
theorem B4113109 : Blo 2165435 4113109 := bbase (se 7 (by rfl) ⟨48200, by rfl⟩ : syracuseStep 4113109 = 96401) (by norm_num)
theorem B5484145 : Blo 2165435 5484145 := bstep (se 2 (by rfl) ⟨2056554, by rfl⟩ : syracuseStep 5484145 = 4113109) B4113109
theorem B7312193 : Blo 2165435 7312193 := bstep (se 2 (by rfl) ⟨2742072, by rfl⟩ : syracuseStep 7312193 = 5484145) B5484145
theorem B4874795 : Blo 2165435 4874795 := bstep (se 1 (by rfl) ⟨3656096, by rfl⟩ : syracuseStep 4874795 = 7312193) B7312193
theorem B3249863 : Blo 2165435 3249863 := bstep (se 1 (by rfl) ⟨2437397, by rfl⟩ : syracuseStep 3249863 = 4874795) B4874795
theorem B2166575 : Blo 2165435 2166575 := bstep (se 1 (by rfl) ⟨1624931, by rfl⟩ : syracuseStep 2166575 = 3249863) B3249863
theorem B3249869 : Blo 2165435 3249869 := bbase (se 3 (by rfl) ⟨609350, by rfl⟩ : syracuseStep 3249869 = 1218701) (by norm_num)
theorem B2166579 : Blo 2165435 2166579 := bstep (se 1 (by rfl) ⟨1624934, by rfl⟩ : syracuseStep 2166579 = 3249869) B3249869
theorem B4874813 : Blo 2165435 4874813 := bbase (se 3 (by rfl) ⟨914027, by rfl⟩ : syracuseStep 4874813 = 1828055) (by norm_num)
theorem B3249875 : Blo 2165435 3249875 := bstep (se 1 (by rfl) ⟨2437406, by rfl⟩ : syracuseStep 3249875 = 4874813) B4874813
theorem B2166583 : Blo 2165435 2166583 := bstep (se 1 (by rfl) ⟨1624937, by rfl⟩ : syracuseStep 2166583 = 3249875) B3249875
theorem B3656117 : Blo 2165435 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B2437411 : Blo 2165435 2437411 := bstep (se 1 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 2437411 = 3656117) B3656117
theorem B3249881 : Blo 2165435 3249881 := bstep (se 2 (by rfl) ⟨1218705, by rfl⟩ : syracuseStep 3249881 = 2437411) B2437411
theorem B2166587 : Blo 2165435 2166587 := bstep (se 1 (by rfl) ⟨1624940, by rfl⟩ : syracuseStep 2166587 = 3249881) B3249881
theorem B2313641 : Blo 2165435 2313641 := bbase (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) (by norm_num)
theorem B6169709 : Blo 2165435 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B16452557 : Blo 2165435 16452557 := bstep (se 3 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 16452557 = 6169709) B6169709
theorem B10968371 : Blo 2165435 10968371 := bstep (se 1 (by rfl) ⟨8226278, by rfl⟩ : syracuseStep 10968371 = 16452557) B16452557
theorem B7312247 : Blo 2165435 7312247 := bstep (se 1 (by rfl) ⟨5484185, by rfl⟩ : syracuseStep 7312247 = 10968371) B10968371
theorem B4874831 : Blo 2165435 4874831 := bstep (se 1 (by rfl) ⟨3656123, by rfl⟩ : syracuseStep 4874831 = 7312247) B7312247
theorem B3249887 : Blo 2165435 3249887 := bstep (se 1 (by rfl) ⟨2437415, by rfl⟩ : syracuseStep 3249887 = 4874831) B4874831
theorem B2166591 : Blo 2165435 2166591 := bstep (se 1 (by rfl) ⟨1624943, by rfl⟩ : syracuseStep 2166591 = 3249887) B3249887
theorem B3249893 : Blo 2165435 3249893 := bbase (se 4 (by rfl) ⟨304677, by rfl⟩ : syracuseStep 3249893 = 609355) (by norm_num)
theorem B2166595 : Blo 2165435 2166595 := bstep (se 1 (by rfl) ⟨1624946, by rfl⟩ : syracuseStep 2166595 = 3249893) B3249893
theorem B6169733 : Blo 2165435 6169733 := bbase (se 4 (by rfl) ⟨578412, by rfl⟩ : syracuseStep 6169733 = 1156825) (by norm_num)
theorem B4113155 : Blo 2165435 4113155 := bstep (se 1 (by rfl) ⟨3084866, by rfl⟩ : syracuseStep 4113155 = 6169733) B6169733
theorem B2742103 : Blo 2165435 2742103 := bstep (se 1 (by rfl) ⟨2056577, by rfl⟩ : syracuseStep 2742103 = 4113155) B4113155
theorem B3656137 : Blo 2165435 3656137 := bstep (se 2 (by rfl) ⟨1371051, by rfl⟩ : syracuseStep 3656137 = 2742103) B2742103
theorem B4874849 : Blo 2165435 4874849 := bstep (se 2 (by rfl) ⟨1828068, by rfl⟩ : syracuseStep 4874849 = 3656137) B3656137
theorem B3249899 : Blo 2165435 3249899 := bstep (se 1 (by rfl) ⟨2437424, by rfl⟩ : syracuseStep 3249899 = 4874849) B4874849
theorem B2166599 : Blo 2165435 2166599 := bstep (se 1 (by rfl) ⟨1624949, by rfl⟩ : syracuseStep 2166599 = 3249899) B3249899
theorem B2437429 : Blo 2165435 2437429 := bbase (se 5 (by rfl) ⟨114254, by rfl⟩ : syracuseStep 2437429 = 228509) (by norm_num)
theorem B3249905 : Blo 2165435 3249905 := bstep (se 2 (by rfl) ⟨1218714, by rfl⟩ : syracuseStep 3249905 = 2437429) B2437429
theorem B2166603 : Blo 2165435 2166603 := bstep (se 1 (by rfl) ⟨1624952, by rfl⟩ : syracuseStep 2166603 = 3249905) B3249905
theorem B2742113 : Blo 2165435 2742113 := bbase (se 2 (by rfl) ⟨1028292, by rfl⟩ : syracuseStep 2742113 = 2056585) (by norm_num)
theorem B7312301 : Blo 2165435 7312301 := bstep (se 3 (by rfl) ⟨1371056, by rfl⟩ : syracuseStep 7312301 = 2742113) B2742113
theorem B4874867 : Blo 2165435 4874867 := bstep (se 1 (by rfl) ⟨3656150, by rfl⟩ : syracuseStep 4874867 = 7312301) B7312301
theorem B3249911 : Blo 2165435 3249911 := bstep (se 1 (by rfl) ⟨2437433, by rfl⟩ : syracuseStep 3249911 = 4874867) B4874867
theorem B2166607 : Blo 2165435 2166607 := bstep (se 1 (by rfl) ⟨1624955, by rfl⟩ : syracuseStep 2166607 = 3249911) B3249911
theorem B3249917 : Blo 2165435 3249917 := bbase (se 3 (by rfl) ⟨609359, by rfl⟩ : syracuseStep 3249917 = 1218719) (by norm_num)
theorem B2166611 : Blo 2165435 2166611 := bstep (se 1 (by rfl) ⟨1624958, by rfl⟩ : syracuseStep 2166611 = 3249917) B3249917
theorem B4874885 : Blo 2165435 4874885 := bbase (se 4 (by rfl) ⟨457020, by rfl⟩ : syracuseStep 4874885 = 914041) (by norm_num)
theorem B3249923 : Blo 2165435 3249923 := bstep (se 1 (by rfl) ⟨2437442, by rfl⟩ : syracuseStep 3249923 = 4874885) B4874885
theorem B2166615 : Blo 2165435 2166615 := bstep (se 1 (by rfl) ⟨1624961, by rfl⟩ : syracuseStep 2166615 = 3249923) B3249923
theorem B2196181 : Blo 2165435 2196181 := bbase (se 7 (by rfl) ⟨25736, by rfl⟩ : syracuseStep 2196181 = 51473) (by norm_num)
theorem B2928241 : Blo 2165435 2928241 := bstep (se 2 (by rfl) ⟨1098090, by rfl⟩ : syracuseStep 2928241 = 2196181) B2196181
theorem B15617285 : Blo 2165435 15617285 := bstep (se 4 (by rfl) ⟨1464120, by rfl⟩ : syracuseStep 15617285 = 2928241) B2928241
theorem B10411523 : Blo 2165435 10411523 := bstep (se 1 (by rfl) ⟨7808642, by rfl⟩ : syracuseStep 10411523 = 15617285) B15617285
theorem B6941015 : Blo 2165435 6941015 := bstep (se 1 (by rfl) ⟨5205761, by rfl⟩ : syracuseStep 6941015 = 10411523) B10411523
theorem B4627343 : Blo 2165435 4627343 := bstep (se 1 (by rfl) ⟨3470507, by rfl⟩ : syracuseStep 4627343 = 6941015) B6941015
theorem B3084895 : Blo 2165435 3084895 := bstep (se 1 (by rfl) ⟨2313671, by rfl⟩ : syracuseStep 3084895 = 4627343) B4627343
theorem B4113193 : Blo 2165435 4113193 := bstep (se 2 (by rfl) ⟨1542447, by rfl⟩ : syracuseStep 4113193 = 3084895) B3084895
theorem B5484257 : Blo 2165435 5484257 := bstep (se 2 (by rfl) ⟨2056596, by rfl⟩ : syracuseStep 5484257 = 4113193) B4113193
theorem B3656171 : Blo 2165435 3656171 := bstep (se 1 (by rfl) ⟨2742128, by rfl⟩ : syracuseStep 3656171 = 5484257) B5484257
theorem B2437447 : Blo 2165435 2437447 := bstep (se 1 (by rfl) ⟨1828085, by rfl⟩ : syracuseStep 2437447 = 3656171) B3656171
theorem B3249929 : Blo 2165435 3249929 := bstep (se 2 (by rfl) ⟨1218723, by rfl⟩ : syracuseStep 3249929 = 2437447) B2437447
theorem B2166619 : Blo 2165435 2166619 := bstep (se 1 (by rfl) ⟨1624964, by rfl⟩ : syracuseStep 2166619 = 3249929) B3249929
theorem B10968533 : Blo 2165435 10968533 := bbase (se 7 (by rfl) ⟨128537, by rfl⟩ : syracuseStep 10968533 = 257075) (by norm_num)
theorem B7312355 : Blo 2165435 7312355 := bstep (se 1 (by rfl) ⟨5484266, by rfl⟩ : syracuseStep 7312355 = 10968533) B10968533
theorem B4874903 : Blo 2165435 4874903 := bstep (se 1 (by rfl) ⟨3656177, by rfl⟩ : syracuseStep 4874903 = 7312355) B7312355
theorem B3249935 : Blo 2165435 3249935 := bstep (se 1 (by rfl) ⟨2437451, by rfl⟩ : syracuseStep 3249935 = 4874903) B4874903
theorem B2166623 : Blo 2165435 2166623 := bstep (se 1 (by rfl) ⟨1624967, by rfl⟩ : syracuseStep 2166623 = 3249935) B3249935
theorem B3249941 : Blo 2165435 3249941 := bbase (se 6 (by rfl) ⟨76170, by rfl⟩ : syracuseStep 3249941 = 152341) (by norm_num)
theorem B2166627 : Blo 2165435 2166627 := bstep (se 1 (by rfl) ⟨1624970, by rfl⟩ : syracuseStep 2166627 = 3249941) B3249941
theorem B90159317 : Blo 2165435 90159317 := bbase (se 7 (by rfl) ⟨1056554, by rfl⟩ : syracuseStep 90159317 = 2113109) (by norm_num)
theorem B60106211 : Blo 2165435 60106211 := bstep (se 1 (by rfl) ⟨45079658, by rfl⟩ : syracuseStep 60106211 = 90159317) B90159317
theorem B40070807 : Blo 2165435 40070807 := bstep (se 1 (by rfl) ⟨30053105, by rfl⟩ : syracuseStep 40070807 = 60106211) B60106211
theorem B26713871 : Blo 2165435 26713871 := bstep (se 1 (by rfl) ⟨20035403, by rfl⟩ : syracuseStep 26713871 = 40070807) B40070807
theorem B17809247 : Blo 2165435 17809247 := bstep (se 1 (by rfl) ⟨13356935, by rfl⟩ : syracuseStep 17809247 = 26713871) B26713871
theorem B11872831 : Blo 2165435 11872831 := bstep (se 1 (by rfl) ⟨8904623, by rfl⟩ : syracuseStep 11872831 = 17809247) B17809247
theorem B15830441 : Blo 2165435 15830441 := bstep (se 2 (by rfl) ⟨5936415, by rfl⟩ : syracuseStep 15830441 = 11872831) B11872831
theorem B10553627 : Blo 2165435 10553627 := bstep (se 1 (by rfl) ⟨7915220, by rfl⟩ : syracuseStep 10553627 = 15830441) B15830441
theorem B7035751 : Blo 2165435 7035751 := bstep (se 1 (by rfl) ⟨5276813, by rfl⟩ : syracuseStep 7035751 = 10553627) B10553627
theorem B37524005 : Blo 2165435 37524005 := bstep (se 4 (by rfl) ⟨3517875, by rfl⟩ : syracuseStep 37524005 = 7035751) B7035751
theorem B25016003 : Blo 2165435 25016003 := bstep (se 1 (by rfl) ⟨18762002, by rfl⟩ : syracuseStep 25016003 = 37524005) B37524005
theorem B16677335 : Blo 2165435 16677335 := bstep (se 1 (by rfl) ⟨12508001, by rfl⟩ : syracuseStep 16677335 = 25016003) B25016003
theorem B44472893 : Blo 2165435 44472893 := bstep (se 3 (by rfl) ⟨8338667, by rfl⟩ : syracuseStep 44472893 = 16677335) B16677335
theorem B118594381 : Blo 2165435 118594381 := bstep (se 3 (by rfl) ⟨22236446, by rfl⟩ : syracuseStep 118594381 = 44472893) B44472893
theorem B158125841 : Blo 2165435 158125841 := bstep (se 2 (by rfl) ⟨59297190, by rfl⟩ : syracuseStep 158125841 = 118594381) B118594381
theorem B105417227 : Blo 2165435 105417227 := bstep (se 1 (by rfl) ⟨79062920, by rfl⟩ : syracuseStep 105417227 = 158125841) B158125841
theorem B70278151 : Blo 2165435 70278151 := bstep (se 1 (by rfl) ⟨52708613, by rfl⟩ : syracuseStep 70278151 = 105417227) B105417227
theorem B93704201 : Blo 2165435 93704201 := bstep (se 2 (by rfl) ⟨35139075, by rfl⟩ : syracuseStep 93704201 = 70278151) B70278151
theorem B62469467 : Blo 2165435 62469467 := bstep (se 1 (by rfl) ⟨46852100, by rfl⟩ : syracuseStep 62469467 = 93704201) B93704201
theorem B41646311 : Blo 2165435 41646311 := bstep (se 1 (by rfl) ⟨31234733, by rfl⟩ : syracuseStep 41646311 = 62469467) B62469467
theorem B27764207 : Blo 2165435 27764207 := bstep (se 1 (by rfl) ⟨20823155, by rfl⟩ : syracuseStep 27764207 = 41646311) B41646311
theorem B18509471 : Blo 2165435 18509471 := bstep (se 1 (by rfl) ⟨13882103, by rfl⟩ : syracuseStep 18509471 = 27764207) B27764207
theorem B12339647 : Blo 2165435 12339647 := bstep (se 1 (by rfl) ⟨9254735, by rfl⟩ : syracuseStep 12339647 = 18509471) B18509471
theorem B8226431 : Blo 2165435 8226431 := bstep (se 1 (by rfl) ⟨6169823, by rfl⟩ : syracuseStep 8226431 = 12339647) B12339647
theorem B5484287 : Blo 2165435 5484287 := bstep (se 1 (by rfl) ⟨4113215, by rfl⟩ : syracuseStep 5484287 = 8226431) B8226431
theorem B3656191 : Blo 2165435 3656191 := bstep (se 1 (by rfl) ⟨2742143, by rfl⟩ : syracuseStep 3656191 = 5484287) B5484287
theorem B4874921 : Blo 2165435 4874921 := bstep (se 2 (by rfl) ⟨1828095, by rfl⟩ : syracuseStep 4874921 = 3656191) B3656191
theorem B3249947 : Blo 2165435 3249947 := bstep (se 1 (by rfl) ⟨2437460, by rfl⟩ : syracuseStep 3249947 = 4874921) B4874921
theorem B2166631 : Blo 2165435 2166631 := bstep (se 1 (by rfl) ⟨1624973, by rfl⟩ : syracuseStep 2166631 = 3249947) B3249947
theorem B2437465 : Blo 2165435 2437465 := bbase (se 2 (by rfl) ⟨914049, by rfl⟩ : syracuseStep 2437465 = 1828099) (by norm_num)
theorem B3249953 : Blo 2165435 3249953 := bstep (se 2 (by rfl) ⟨1218732, by rfl⟩ : syracuseStep 3249953 = 2437465) B2437465
theorem B2166635 : Blo 2165435 2166635 := bstep (se 1 (by rfl) ⟨1624976, by rfl⟩ : syracuseStep 2166635 = 3249953) B3249953
theorem B3904357 : Blo 2165435 3904357 := bbase (se 4 (by rfl) ⟨366033, by rfl⟩ : syracuseStep 3904357 = 732067) (by norm_num)
theorem B5205809 : Blo 2165435 5205809 := bstep (se 2 (by rfl) ⟨1952178, by rfl⟩ : syracuseStep 5205809 = 3904357) B3904357
theorem B3470539 : Blo 2165435 3470539 := bstep (se 1 (by rfl) ⟨2602904, by rfl⟩ : syracuseStep 3470539 = 5205809) B5205809
theorem B4627385 : Blo 2165435 4627385 := bstep (se 2 (by rfl) ⟨1735269, by rfl⟩ : syracuseStep 4627385 = 3470539) B3470539
theorem B3084923 : Blo 2165435 3084923 := bstep (se 1 (by rfl) ⟨2313692, by rfl⟩ : syracuseStep 3084923 = 4627385) B4627385
theorem B8226461 : Blo 2165435 8226461 := bstep (se 3 (by rfl) ⟨1542461, by rfl⟩ : syracuseStep 8226461 = 3084923) B3084923
theorem B5484307 : Blo 2165435 5484307 := bstep (se 1 (by rfl) ⟨4113230, by rfl⟩ : syracuseStep 5484307 = 8226461) B8226461
theorem B7312409 : Blo 2165435 7312409 := bstep (se 2 (by rfl) ⟨2742153, by rfl⟩ : syracuseStep 7312409 = 5484307) B5484307
theorem B4874939 : Blo 2165435 4874939 := bstep (se 1 (by rfl) ⟨3656204, by rfl⟩ : syracuseStep 4874939 = 7312409) B7312409
theorem B3249959 : Blo 2165435 3249959 := bstep (se 1 (by rfl) ⟨2437469, by rfl⟩ : syracuseStep 3249959 = 4874939) B4874939
theorem B2166639 : Blo 2165435 2166639 := bstep (se 1 (by rfl) ⟨1624979, by rfl⟩ : syracuseStep 2166639 = 3249959) B3249959
theorem B3249965 : Blo 2165435 3249965 := bbase (se 3 (by rfl) ⟨609368, by rfl⟩ : syracuseStep 3249965 = 1218737) (by norm_num)
theorem B2166643 : Blo 2165435 2166643 := bstep (se 1 (by rfl) ⟨1624982, by rfl⟩ : syracuseStep 2166643 = 3249965) B3249965
theorem B4874957 : Blo 2165435 4874957 := bbase (se 3 (by rfl) ⟨914054, by rfl⟩ : syracuseStep 4874957 = 1828109) (by norm_num)
theorem B3249971 : Blo 2165435 3249971 := bstep (se 1 (by rfl) ⟨2437478, by rfl⟩ : syracuseStep 3249971 = 4874957) B4874957
theorem B2166647 : Blo 2165435 2166647 := bstep (se 1 (by rfl) ⟨1624985, by rfl⟩ : syracuseStep 2166647 = 3249971) B3249971
theorem B2742169 : Blo 2165435 2742169 := bbase (se 2 (by rfl) ⟨1028313, by rfl⟩ : syracuseStep 2742169 = 2056627) (by norm_num)
theorem B3656225 : Blo 2165435 3656225 := bstep (se 2 (by rfl) ⟨1371084, by rfl⟩ : syracuseStep 3656225 = 2742169) B2742169
theorem B2437483 : Blo 2165435 2437483 := bstep (se 1 (by rfl) ⟨1828112, by rfl⟩ : syracuseStep 2437483 = 3656225) B3656225
theorem B3249977 : Blo 2165435 3249977 := bstep (se 2 (by rfl) ⟨1218741, by rfl⟩ : syracuseStep 3249977 = 2437483) B2437483
theorem B2166651 : Blo 2165435 2166651 := bstep (se 1 (by rfl) ⟨1624988, by rfl⟩ : syracuseStep 2166651 = 3249977) B3249977
theorem B9254837 : Blo 2165435 9254837 := bbase (se 5 (by rfl) ⟨433820, by rfl⟩ : syracuseStep 9254837 = 867641) (by norm_num)
theorem B24679565 : Blo 2165435 24679565 := bstep (se 3 (by rfl) ⟨4627418, by rfl⟩ : syracuseStep 24679565 = 9254837) B9254837
theorem B16453043 : Blo 2165435 16453043 := bstep (se 1 (by rfl) ⟨12339782, by rfl⟩ : syracuseStep 16453043 = 24679565) B24679565
theorem B10968695 : Blo 2165435 10968695 := bstep (se 1 (by rfl) ⟨8226521, by rfl⟩ : syracuseStep 10968695 = 16453043) B16453043
theorem B7312463 : Blo 2165435 7312463 := bstep (se 1 (by rfl) ⟨5484347, by rfl⟩ : syracuseStep 7312463 = 10968695) B10968695
theorem B4874975 : Blo 2165435 4874975 := bstep (se 1 (by rfl) ⟨3656231, by rfl⟩ : syracuseStep 4874975 = 7312463) B7312463
theorem B3249983 : Blo 2165435 3249983 := bstep (se 1 (by rfl) ⟨2437487, by rfl⟩ : syracuseStep 3249983 = 4874975) B4874975
theorem B2166655 : Blo 2165435 2166655 := bstep (se 1 (by rfl) ⟨1624991, by rfl⟩ : syracuseStep 2166655 = 3249983) B3249983
theorem B3249989 : Blo 2165435 3249989 := bbase (se 4 (by rfl) ⟨304686, by rfl⟩ : syracuseStep 3249989 = 609373) (by norm_num)
theorem B2166659 : Blo 2165435 2166659 := bstep (se 1 (by rfl) ⟨1624994, by rfl⟩ : syracuseStep 2166659 = 3249989) B3249989
theorem B3656245 : Blo 2165435 3656245 := bbase (se 5 (by rfl) ⟨171386, by rfl⟩ : syracuseStep 3656245 = 342773) (by norm_num)
theorem B4874993 : Blo 2165435 4874993 := bstep (se 2 (by rfl) ⟨1828122, by rfl⟩ : syracuseStep 4874993 = 3656245) B3656245
theorem B3249995 : Blo 2165435 3249995 := bstep (se 1 (by rfl) ⟨2437496, by rfl⟩ : syracuseStep 3249995 = 4874993) B4874993
theorem B2166663 : Blo 2165435 2166663 := bstep (se 1 (by rfl) ⟨1624997, by rfl⟩ : syracuseStep 2166663 = 3249995) B3249995
theorem B2437501 : Blo 2165435 2437501 := bbase (se 3 (by rfl) ⟨457031, by rfl⟩ : syracuseStep 2437501 = 914063) (by norm_num)
theorem B3250001 : Blo 2165435 3250001 := bstep (se 2 (by rfl) ⟨1218750, by rfl⟩ : syracuseStep 3250001 = 2437501) B2437501
theorem B2166667 : Blo 2165435 2166667 := bstep (se 1 (by rfl) ⟨1625000, by rfl⟩ : syracuseStep 2166667 = 3250001) B3250001
theorem B7312517 : Blo 2165435 7312517 := bbase (se 4 (by rfl) ⟨685548, by rfl⟩ : syracuseStep 7312517 = 1371097) (by norm_num)
theorem B4875011 : Blo 2165435 4875011 := bstep (se 1 (by rfl) ⟨3656258, by rfl⟩ : syracuseStep 4875011 = 7312517) B7312517
theorem B3250007 : Blo 2165435 3250007 := bstep (se 1 (by rfl) ⟨2437505, by rfl⟩ : syracuseStep 3250007 = 4875011) B4875011
theorem B2166671 : Blo 2165435 2166671 := bstep (se 1 (by rfl) ⟨1625003, by rfl⟩ : syracuseStep 2166671 = 3250007) B3250007
theorem B3250013 : Blo 2165435 3250013 := bbase (se 3 (by rfl) ⟨609377, by rfl⟩ : syracuseStep 3250013 = 1218755) (by norm_num)
theorem B2166675 : Blo 2165435 2166675 := bstep (se 1 (by rfl) ⟨1625006, by rfl⟩ : syracuseStep 2166675 = 3250013) B3250013
theorem B4875029 : Blo 2165435 4875029 := bbase (se 6 (by rfl) ⟨114258, by rfl⟩ : syracuseStep 4875029 = 228517) (by norm_num)
theorem B3250019 : Blo 2165435 3250019 := bstep (se 1 (by rfl) ⟨2437514, by rfl⟩ : syracuseStep 3250019 = 4875029) B4875029
theorem B2166679 : Blo 2165435 2166679 := bstep (se 1 (by rfl) ⟨1625009, by rfl⟩ : syracuseStep 2166679 = 3250019) B3250019
theorem B8226629 : Blo 2165435 8226629 := bbase (se 4 (by rfl) ⟨771246, by rfl⟩ : syracuseStep 8226629 = 1542493) (by norm_num)
theorem B5484419 : Blo 2165435 5484419 := bstep (se 1 (by rfl) ⟨4113314, by rfl⟩ : syracuseStep 5484419 = 8226629) B8226629
theorem B3656279 : Blo 2165435 3656279 := bstep (se 1 (by rfl) ⟨2742209, by rfl⟩ : syracuseStep 3656279 = 5484419) B5484419
theorem B2437519 : Blo 2165435 2437519 := bstep (se 1 (by rfl) ⟨1828139, by rfl⟩ : syracuseStep 2437519 = 3656279) B3656279
theorem B3250025 : Blo 2165435 3250025 := bstep (se 2 (by rfl) ⟨1218759, by rfl⟩ : syracuseStep 3250025 = 2437519) B2437519
theorem B2166683 : Blo 2165435 2166683 := bstep (se 1 (by rfl) ⟨1625012, by rfl⟩ : syracuseStep 2166683 = 3250025) B3250025
theorem B29649365 : Blo 2165435 29649365 := bbase (se 7 (by rfl) ⟨347453, by rfl⟩ : syracuseStep 29649365 = 694907) (by norm_num)
theorem B19766243 : Blo 2165435 19766243 := bstep (se 1 (by rfl) ⟨14824682, by rfl⟩ : syracuseStep 19766243 = 29649365) B29649365
theorem B13177495 : Blo 2165435 13177495 := bstep (se 1 (by rfl) ⟨9883121, by rfl⟩ : syracuseStep 13177495 = 19766243) B19766243
theorem B17569993 : Blo 2165435 17569993 := bstep (se 2 (by rfl) ⟨6588747, by rfl⟩ : syracuseStep 17569993 = 13177495) B13177495
theorem B23426657 : Blo 2165435 23426657 := bstep (se 2 (by rfl) ⟨8784996, by rfl⟩ : syracuseStep 23426657 = 17569993) B17569993
theorem B15617771 : Blo 2165435 15617771 := bstep (se 1 (by rfl) ⟨11713328, by rfl⟩ : syracuseStep 15617771 = 23426657) B23426657
theorem B10411847 : Blo 2165435 10411847 := bstep (se 1 (by rfl) ⟨7808885, by rfl⟩ : syracuseStep 10411847 = 15617771) B15617771
theorem B6941231 : Blo 2165435 6941231 := bstep (se 1 (by rfl) ⟨5205923, by rfl⟩ : syracuseStep 6941231 = 10411847) B10411847
theorem B4627487 : Blo 2165435 4627487 := bstep (se 1 (by rfl) ⟨3470615, by rfl⟩ : syracuseStep 4627487 = 6941231) B6941231
theorem B12339965 : Blo 2165435 12339965 := bstep (se 3 (by rfl) ⟨2313743, by rfl⟩ : syracuseStep 12339965 = 4627487) B4627487
theorem B8226643 : Blo 2165435 8226643 := bstep (se 1 (by rfl) ⟨6169982, by rfl⟩ : syracuseStep 8226643 = 12339965) B12339965
theorem B10968857 : Blo 2165435 10968857 := bstep (se 2 (by rfl) ⟨4113321, by rfl⟩ : syracuseStep 10968857 = 8226643) B8226643
theorem B7312571 : Blo 2165435 7312571 := bstep (se 1 (by rfl) ⟨5484428, by rfl⟩ : syracuseStep 7312571 = 10968857) B10968857
theorem B4875047 : Blo 2165435 4875047 := bstep (se 1 (by rfl) ⟨3656285, by rfl⟩ : syracuseStep 4875047 = 7312571) B7312571
theorem B3250031 : Blo 2165435 3250031 := bstep (se 1 (by rfl) ⟨2437523, by rfl⟩ : syracuseStep 3250031 = 4875047) B4875047
theorem B2166687 : Blo 2165435 2166687 := bstep (se 1 (by rfl) ⟨1625015, by rfl⟩ : syracuseStep 2166687 = 3250031) B3250031
theorem B3250037 : Blo 2165435 3250037 := bbase (se 5 (by rfl) ⟨152345, by rfl⟩ : syracuseStep 3250037 = 304691) (by norm_num)
theorem B2166691 : Blo 2165435 2166691 := bstep (se 1 (by rfl) ⟨1625018, by rfl⟩ : syracuseStep 2166691 = 3250037) B3250037
theorem B3470629 : Blo 2165435 3470629 := bbase (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) (by norm_num)
theorem B4627505 : Blo 2165435 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B3085003 : Blo 2165435 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B4113337 : Blo 2165435 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B5484449 : Blo 2165435 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B3656299 : Blo 2165435 3656299 := bstep (se 1 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 3656299 = 5484449) B5484449
theorem B4875065 : Blo 2165435 4875065 := bstep (se 2 (by rfl) ⟨1828149, by rfl⟩ : syracuseStep 4875065 = 3656299) B3656299
theorem B3250043 : Blo 2165435 3250043 := bstep (se 1 (by rfl) ⟨2437532, by rfl⟩ : syracuseStep 3250043 = 4875065) B4875065
theorem B2166695 : Blo 2165435 2166695 := bstep (se 1 (by rfl) ⟨1625021, by rfl⟩ : syracuseStep 2166695 = 3250043) B3250043
theorem B2437537 : Blo 2165435 2437537 := bbase (se 2 (by rfl) ⟨914076, by rfl⟩ : syracuseStep 2437537 = 1828153) (by norm_num)
theorem B3250049 : Blo 2165435 3250049 := bstep (se 2 (by rfl) ⟨1218768, by rfl⟩ : syracuseStep 3250049 = 2437537) B2437537
theorem B2166699 : Blo 2165435 2166699 := bstep (se 1 (by rfl) ⟨1625024, by rfl⟩ : syracuseStep 2166699 = 3250049) B3250049
theorem B5484469 : Blo 2165435 5484469 := bbase (se 5 (by rfl) ⟨257084, by rfl⟩ : syracuseStep 5484469 = 514169) (by norm_num)
theorem B7312625 : Blo 2165435 7312625 := bstep (se 2 (by rfl) ⟨2742234, by rfl⟩ : syracuseStep 7312625 = 5484469) B5484469
theorem B4875083 : Blo 2165435 4875083 := bstep (se 1 (by rfl) ⟨3656312, by rfl⟩ : syracuseStep 4875083 = 7312625) B7312625
theorem B3250055 : Blo 2165435 3250055 := bstep (se 1 (by rfl) ⟨2437541, by rfl⟩ : syracuseStep 3250055 = 4875083) B4875083
theorem B2166703 : Blo 2165435 2166703 := bstep (se 1 (by rfl) ⟨1625027, by rfl⟩ : syracuseStep 2166703 = 3250055) B3250055
theorem B3250061 : Blo 2165435 3250061 := bbase (se 3 (by rfl) ⟨609386, by rfl⟩ : syracuseStep 3250061 = 1218773) (by norm_num)
theorem B2166707 : Blo 2165435 2166707 := bstep (se 1 (by rfl) ⟨1625030, by rfl⟩ : syracuseStep 2166707 = 3250061) B3250061
theorem B4875101 : Blo 2165435 4875101 := bbase (se 3 (by rfl) ⟨914081, by rfl⟩ : syracuseStep 4875101 = 1828163) (by norm_num)
theorem B3250067 : Blo 2165435 3250067 := bstep (se 1 (by rfl) ⟨2437550, by rfl⟩ : syracuseStep 3250067 = 4875101) B4875101
theorem B2166711 : Blo 2165435 2166711 := bstep (se 1 (by rfl) ⟨1625033, by rfl⟩ : syracuseStep 2166711 = 3250067) B3250067
theorem B3656333 : Blo 2165435 3656333 := bbase (se 3 (by rfl) ⟨685562, by rfl⟩ : syracuseStep 3656333 = 1371125) (by norm_num)
theorem B2437555 : Blo 2165435 2437555 := bstep (se 1 (by rfl) ⟨1828166, by rfl⟩ : syracuseStep 2437555 = 3656333) B3656333
theorem B3250073 : Blo 2165435 3250073 := bstep (se 2 (by rfl) ⟨1218777, by rfl⟩ : syracuseStep 3250073 = 2437555) B2437555
theorem B2166715 : Blo 2165435 2166715 := bstep (se 1 (by rfl) ⟨1625036, by rfl⟩ : syracuseStep 2166715 = 3250073) B3250073
theorem B6941333 : Blo 2165435 6941333 := bbase (se 6 (by rfl) ⟨162687, by rfl⟩ : syracuseStep 6941333 = 325375) (by norm_num)
theorem B18510221 : Blo 2165435 18510221 := bstep (se 3 (by rfl) ⟨3470666, by rfl⟩ : syracuseStep 18510221 = 6941333) B6941333
theorem B12340147 : Blo 2165435 12340147 := bstep (se 1 (by rfl) ⟨9255110, by rfl⟩ : syracuseStep 12340147 = 18510221) B18510221
theorem B16453529 : Blo 2165435 16453529 := bstep (se 2 (by rfl) ⟨6170073, by rfl⟩ : syracuseStep 16453529 = 12340147) B12340147
theorem B10969019 : Blo 2165435 10969019 := bstep (se 1 (by rfl) ⟨8226764, by rfl⟩ : syracuseStep 10969019 = 16453529) B16453529
theorem B7312679 : Blo 2165435 7312679 := bstep (se 1 (by rfl) ⟨5484509, by rfl⟩ : syracuseStep 7312679 = 10969019) B10969019
theorem B4875119 : Blo 2165435 4875119 := bstep (se 1 (by rfl) ⟨3656339, by rfl⟩ : syracuseStep 4875119 = 7312679) B7312679
theorem B3250079 : Blo 2165435 3250079 := bstep (se 1 (by rfl) ⟨2437559, by rfl⟩ : syracuseStep 3250079 = 4875119) B4875119
theorem B2166719 : Blo 2165435 2166719 := bstep (se 1 (by rfl) ⟨1625039, by rfl⟩ : syracuseStep 2166719 = 3250079) B3250079
theorem B3250085 : Blo 2165435 3250085 := bbase (se 4 (by rfl) ⟨304695, by rfl⟩ : syracuseStep 3250085 = 609391) (by norm_num)
theorem B2166723 : Blo 2165435 2166723 := bstep (se 1 (by rfl) ⟨1625042, by rfl⟩ : syracuseStep 2166723 = 3250085) B3250085
theorem B2742265 : Blo 2165435 2742265 := bbase (se 2 (by rfl) ⟨1028349, by rfl⟩ : syracuseStep 2742265 = 2056699) (by norm_num)
theorem B3656353 : Blo 2165435 3656353 := bstep (se 2 (by rfl) ⟨1371132, by rfl⟩ : syracuseStep 3656353 = 2742265) B2742265
theorem B4875137 : Blo 2165435 4875137 := bstep (se 2 (by rfl) ⟨1828176, by rfl⟩ : syracuseStep 4875137 = 3656353) B3656353
theorem B3250091 : Blo 2165435 3250091 := bstep (se 1 (by rfl) ⟨2437568, by rfl⟩ : syracuseStep 3250091 = 4875137) B4875137
theorem B2166727 : Blo 2165435 2166727 := bstep (se 1 (by rfl) ⟨1625045, by rfl⟩ : syracuseStep 2166727 = 3250091) B3250091
theorem B2437573 : Blo 2165435 2437573 := bbase (se 4 (by rfl) ⟨228522, by rfl⟩ : syracuseStep 2437573 = 457045) (by norm_num)
theorem B3250097 : Blo 2165435 3250097 := bstep (se 2 (by rfl) ⟨1218786, by rfl⟩ : syracuseStep 3250097 = 2437573) B2437573
theorem B2166731 : Blo 2165435 2166731 := bstep (se 1 (by rfl) ⟨1625048, by rfl⟩ : syracuseStep 2166731 = 3250097) B3250097
theorem B4113413 : Blo 2165435 4113413 := bbase (se 4 (by rfl) ⟨385632, by rfl⟩ : syracuseStep 4113413 = 771265) (by norm_num)
theorem B2742275 : Blo 2165435 2742275 := bstep (se 1 (by rfl) ⟨2056706, by rfl⟩ : syracuseStep 2742275 = 4113413) B4113413
theorem B7312733 : Blo 2165435 7312733 := bstep (se 3 (by rfl) ⟨1371137, by rfl⟩ : syracuseStep 7312733 = 2742275) B2742275
theorem B4875155 : Blo 2165435 4875155 := bstep (se 1 (by rfl) ⟨3656366, by rfl⟩ : syracuseStep 4875155 = 7312733) B7312733
theorem B3250103 : Blo 2165435 3250103 := bstep (se 1 (by rfl) ⟨2437577, by rfl⟩ : syracuseStep 3250103 = 4875155) B4875155
theorem B2166735 : Blo 2165435 2166735 := bstep (se 1 (by rfl) ⟨1625051, by rfl⟩ : syracuseStep 2166735 = 3250103) B3250103
theorem B3250109 : Blo 2165435 3250109 := bbase (se 3 (by rfl) ⟨609395, by rfl⟩ : syracuseStep 3250109 = 1218791) (by norm_num)
theorem B2166739 : Blo 2165435 2166739 := bstep (se 1 (by rfl) ⟨1625054, by rfl⟩ : syracuseStep 2166739 = 3250109) B3250109
theorem B4875173 : Blo 2165435 4875173 := bbase (se 4 (by rfl) ⟨457047, by rfl⟩ : syracuseStep 4875173 = 914095) (by norm_num)
theorem B3250115 : Blo 2165435 3250115 := bstep (se 1 (by rfl) ⟨2437586, by rfl⟩ : syracuseStep 3250115 = 4875173) B4875173
theorem B2166743 : Blo 2165435 2166743 := bstep (se 1 (by rfl) ⟨1625057, by rfl⟩ : syracuseStep 2166743 = 3250115) B3250115
theorem B5484581 : Blo 2165435 5484581 := bbase (se 4 (by rfl) ⟨514179, by rfl⟩ : syracuseStep 5484581 = 1028359) (by norm_num)
theorem B3656387 : Blo 2165435 3656387 := bstep (se 1 (by rfl) ⟨2742290, by rfl⟩ : syracuseStep 3656387 = 5484581) B5484581
theorem B2437591 : Blo 2165435 2437591 := bstep (se 1 (by rfl) ⟨1828193, by rfl⟩ : syracuseStep 2437591 = 3656387) B3656387
theorem B3250121 : Blo 2165435 3250121 := bstep (se 2 (by rfl) ⟨1218795, by rfl⟩ : syracuseStep 3250121 = 2437591) B2437591
theorem B2166747 : Blo 2165435 2166747 := bstep (se 1 (by rfl) ⟨1625060, by rfl⟩ : syracuseStep 2166747 = 3250121) B3250121
theorem B6170165 : Blo 2165435 6170165 := bbase (se 5 (by rfl) ⟨289226, by rfl⟩ : syracuseStep 6170165 = 578453) (by norm_num)
theorem B4113443 : Blo 2165435 4113443 := bstep (se 1 (by rfl) ⟨3085082, by rfl⟩ : syracuseStep 4113443 = 6170165) B6170165
theorem B10969181 : Blo 2165435 10969181 := bstep (se 3 (by rfl) ⟨2056721, by rfl⟩ : syracuseStep 10969181 = 4113443) B4113443
theorem B7312787 : Blo 2165435 7312787 := bstep (se 1 (by rfl) ⟨5484590, by rfl⟩ : syracuseStep 7312787 = 10969181) B10969181
theorem B4875191 : Blo 2165435 4875191 := bstep (se 1 (by rfl) ⟨3656393, by rfl⟩ : syracuseStep 4875191 = 7312787) B7312787
theorem B3250127 : Blo 2165435 3250127 := bstep (se 1 (by rfl) ⟨2437595, by rfl⟩ : syracuseStep 3250127 = 4875191) B4875191
theorem B2166751 : Blo 2165435 2166751 := bstep (se 1 (by rfl) ⟨1625063, by rfl⟩ : syracuseStep 2166751 = 3250127) B3250127
theorem B3250133 : Blo 2165435 3250133 := bbase (se 7 (by rfl) ⟨38087, by rfl⟩ : syracuseStep 3250133 = 76175) (by norm_num)
theorem B2166755 : Blo 2165435 2166755 := bstep (se 1 (by rfl) ⟨1625066, by rfl⟩ : syracuseStep 2166755 = 3250133) B3250133
theorem B8226917 : Blo 2165435 8226917 := bbase (se 4 (by rfl) ⟨771273, by rfl⟩ : syracuseStep 8226917 = 1542547) (by norm_num)
theorem B5484611 : Blo 2165435 5484611 := bstep (se 1 (by rfl) ⟨4113458, by rfl⟩ : syracuseStep 5484611 = 8226917) B8226917
theorem B3656407 : Blo 2165435 3656407 := bstep (se 1 (by rfl) ⟨2742305, by rfl⟩ : syracuseStep 3656407 = 5484611) B5484611
theorem B4875209 : Blo 2165435 4875209 := bstep (se 2 (by rfl) ⟨1828203, by rfl⟩ : syracuseStep 4875209 = 3656407) B3656407
theorem B3250139 : Blo 2165435 3250139 := bstep (se 1 (by rfl) ⟨2437604, by rfl⟩ : syracuseStep 3250139 = 4875209) B4875209
theorem B2166759 : Blo 2165435 2166759 := bstep (se 1 (by rfl) ⟨1625069, by rfl⟩ : syracuseStep 2166759 = 3250139) B3250139
theorem B2437609 : Blo 2165435 2437609 := bbase (se 2 (by rfl) ⟨914103, by rfl⟩ : syracuseStep 2437609 = 1828207) (by norm_num)
theorem B3250145 : Blo 2165435 3250145 := bstep (se 2 (by rfl) ⟨1218804, by rfl⟩ : syracuseStep 3250145 = 2437609) B2437609
theorem B2166763 : Blo 2165435 2166763 := bstep (se 1 (by rfl) ⟨1625072, by rfl⟩ : syracuseStep 2166763 = 3250145) B3250145
theorem B2313829 : Blo 2165435 2313829 := bbase (se 4 (by rfl) ⟨216921, by rfl⟩ : syracuseStep 2313829 = 433843) (by norm_num)
theorem B12340421 : Blo 2165435 12340421 := bstep (se 4 (by rfl) ⟨1156914, by rfl⟩ : syracuseStep 12340421 = 2313829) B2313829
theorem B8226947 : Blo 2165435 8226947 := bstep (se 1 (by rfl) ⟨6170210, by rfl⟩ : syracuseStep 8226947 = 12340421) B12340421
theorem B5484631 : Blo 2165435 5484631 := bstep (se 1 (by rfl) ⟨4113473, by rfl⟩ : syracuseStep 5484631 = 8226947) B8226947
theorem B7312841 : Blo 2165435 7312841 := bstep (se 2 (by rfl) ⟨2742315, by rfl⟩ : syracuseStep 7312841 = 5484631) B5484631
theorem B4875227 : Blo 2165435 4875227 := bstep (se 1 (by rfl) ⟨3656420, by rfl⟩ : syracuseStep 4875227 = 7312841) B7312841
theorem B3250151 : Blo 2165435 3250151 := bstep (se 1 (by rfl) ⟨2437613, by rfl⟩ : syracuseStep 3250151 = 4875227) B4875227
theorem B2166767 : Blo 2165435 2166767 := bstep (se 1 (by rfl) ⟨1625075, by rfl⟩ : syracuseStep 2166767 = 3250151) B3250151
theorem B3250157 : Blo 2165435 3250157 := bbase (se 3 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 3250157 = 1218809) (by norm_num)
theorem B2166771 : Blo 2165435 2166771 := bstep (se 1 (by rfl) ⟨1625078, by rfl⟩ : syracuseStep 2166771 = 3250157) B3250157
theorem B4875245 : Blo 2165435 4875245 := bbase (se 3 (by rfl) ⟨914108, by rfl⟩ : syracuseStep 4875245 = 1828217) (by norm_num)
theorem B3250163 : Blo 2165435 3250163 := bstep (se 1 (by rfl) ⟨2437622, by rfl⟩ : syracuseStep 3250163 = 4875245) B4875245
theorem B2166775 : Blo 2165435 2166775 := bstep (se 1 (by rfl) ⟨1625081, by rfl⟩ : syracuseStep 2166775 = 3250163) B3250163
theorem B4627685 : Blo 2165435 4627685 := bbase (se 4 (by rfl) ⟨433845, by rfl⟩ : syracuseStep 4627685 = 867691) (by norm_num)
theorem B3085123 : Blo 2165435 3085123 := bstep (se 1 (by rfl) ⟨2313842, by rfl⟩ : syracuseStep 3085123 = 4627685) B4627685
theorem B4113497 : Blo 2165435 4113497 := bstep (se 2 (by rfl) ⟨1542561, by rfl⟩ : syracuseStep 4113497 = 3085123) B3085123
theorem B2742331 : Blo 2165435 2742331 := bstep (se 1 (by rfl) ⟨2056748, by rfl⟩ : syracuseStep 2742331 = 4113497) B4113497
theorem B3656441 : Blo 2165435 3656441 := bstep (se 2 (by rfl) ⟨1371165, by rfl⟩ : syracuseStep 3656441 = 2742331) B2742331
theorem B2437627 : Blo 2165435 2437627 := bstep (se 1 (by rfl) ⟨1828220, by rfl⟩ : syracuseStep 2437627 = 3656441) B3656441
theorem B3250169 : Blo 2165435 3250169 := bstep (se 2 (by rfl) ⟨1218813, by rfl⟩ : syracuseStep 3250169 = 2437627) B2437627
theorem B2166779 : Blo 2165435 2166779 := bstep (se 1 (by rfl) ⟨1625084, by rfl⟩ : syracuseStep 2166779 = 3250169) B3250169
theorem B187421525 : Blo 2165435 187421525 := bbase (se 9 (by rfl) ⟨549086, by rfl⟩ : syracuseStep 187421525 = 1098173) (by norm_num)
theorem B124947683 : Blo 2165435 124947683 := bstep (se 1 (by rfl) ⟨93710762, by rfl⟩ : syracuseStep 124947683 = 187421525) B187421525
theorem B83298455 : Blo 2165435 83298455 := bstep (se 1 (by rfl) ⟨62473841, by rfl⟩ : syracuseStep 83298455 = 124947683) B124947683
theorem B55532303 : Blo 2165435 55532303 := bstep (se 1 (by rfl) ⟨41649227, by rfl⟩ : syracuseStep 55532303 = 83298455) B83298455
theorem B37021535 : Blo 2165435 37021535 := bstep (se 1 (by rfl) ⟨27766151, by rfl⟩ : syracuseStep 37021535 = 55532303) B55532303
theorem B24681023 : Blo 2165435 24681023 := bstep (se 1 (by rfl) ⟨18510767, by rfl⟩ : syracuseStep 24681023 = 37021535) B37021535
theorem B16454015 : Blo 2165435 16454015 := bstep (se 1 (by rfl) ⟨12340511, by rfl⟩ : syracuseStep 16454015 = 24681023) B24681023
theorem B10969343 : Blo 2165435 10969343 := bstep (se 1 (by rfl) ⟨8227007, by rfl⟩ : syracuseStep 10969343 = 16454015) B16454015
theorem B7312895 : Blo 2165435 7312895 := bstep (se 1 (by rfl) ⟨5484671, by rfl⟩ : syracuseStep 7312895 = 10969343) B10969343
theorem B4875263 : Blo 2165435 4875263 := bstep (se 1 (by rfl) ⟨3656447, by rfl⟩ : syracuseStep 4875263 = 7312895) B7312895
theorem B3250175 : Blo 2165435 3250175 := bstep (se 1 (by rfl) ⟨2437631, by rfl⟩ : syracuseStep 3250175 = 4875263) B4875263
theorem B2166783 : Blo 2165435 2166783 := bstep (se 1 (by rfl) ⟨1625087, by rfl⟩ : syracuseStep 2166783 = 3250175) B3250175
theorem B3250181 : Blo 2165435 3250181 := bbase (se 4 (by rfl) ⟨304704, by rfl⟩ : syracuseStep 3250181 = 609409) (by norm_num)
theorem B2166787 : Blo 2165435 2166787 := bstep (se 1 (by rfl) ⟨1625090, by rfl⟩ : syracuseStep 2166787 = 3250181) B3250181
theorem B3656461 : Blo 2165435 3656461 := bbase (se 3 (by rfl) ⟨685586, by rfl⟩ : syracuseStep 3656461 = 1371173) (by norm_num)
theorem B4875281 : Blo 2165435 4875281 := bstep (se 2 (by rfl) ⟨1828230, by rfl⟩ : syracuseStep 4875281 = 3656461) B3656461
theorem B3250187 : Blo 2165435 3250187 := bstep (se 1 (by rfl) ⟨2437640, by rfl⟩ : syracuseStep 3250187 = 4875281) B4875281
theorem B2166791 : Blo 2165435 2166791 := bstep (se 1 (by rfl) ⟨1625093, by rfl⟩ : syracuseStep 2166791 = 3250187) B3250187
theorem B2437645 : Blo 2165435 2437645 := bbase (se 3 (by rfl) ⟨457058, by rfl⟩ : syracuseStep 2437645 = 914117) (by norm_num)
theorem B3250193 : Blo 2165435 3250193 := bstep (se 2 (by rfl) ⟨1218822, by rfl⟩ : syracuseStep 3250193 = 2437645) B2437645
theorem B2166795 : Blo 2165435 2166795 := bstep (se 1 (by rfl) ⟨1625096, by rfl⟩ : syracuseStep 2166795 = 3250193) B3250193
theorem B7312949 : Blo 2165435 7312949 := bbase (se 5 (by rfl) ⟨342794, by rfl⟩ : syracuseStep 7312949 = 685589) (by norm_num)
theorem B4875299 : Blo 2165435 4875299 := bstep (se 1 (by rfl) ⟨3656474, by rfl⟩ : syracuseStep 4875299 = 7312949) B7312949
theorem B3250199 : Blo 2165435 3250199 := bstep (se 1 (by rfl) ⟨2437649, by rfl⟩ : syracuseStep 3250199 = 4875299) B4875299
theorem B2166799 : Blo 2165435 2166799 := bstep (se 1 (by rfl) ⟨1625099, by rfl⟩ : syracuseStep 2166799 = 3250199) B3250199
theorem B3250205 : Blo 2165435 3250205 := bbase (se 3 (by rfl) ⟨609413, by rfl⟩ : syracuseStep 3250205 = 1218827) (by norm_num)
theorem B2166803 : Blo 2165435 2166803 := bstep (se 1 (by rfl) ⟨1625102, by rfl⟩ : syracuseStep 2166803 = 3250205) B3250205
theorem B4875317 : Blo 2165435 4875317 := bbase (se 5 (by rfl) ⟨228530, by rfl⟩ : syracuseStep 4875317 = 457061) (by norm_num)
theorem B3250211 : Blo 2165435 3250211 := bstep (se 1 (by rfl) ⟨2437658, by rfl⟩ : syracuseStep 3250211 = 4875317) B4875317
theorem B2166807 : Blo 2165435 2166807 := bstep (se 1 (by rfl) ⟨1625105, by rfl⟩ : syracuseStep 2166807 = 3250211) B3250211
theorem B8339365 : Blo 2165435 8339365 := bbase (se 4 (by rfl) ⟨781815, by rfl⟩ : syracuseStep 8339365 = 1563631) (by norm_num)
theorem B11119153 : Blo 2165435 11119153 := bstep (se 2 (by rfl) ⟨4169682, by rfl⟩ : syracuseStep 11119153 = 8339365) B8339365
theorem B14825537 : Blo 2165435 14825537 := bstep (se 2 (by rfl) ⟨5559576, by rfl⟩ : syracuseStep 14825537 = 11119153) B11119153
theorem B9883691 : Blo 2165435 9883691 := bstep (se 1 (by rfl) ⟨7412768, by rfl⟩ : syracuseStep 9883691 = 14825537) B14825537
theorem B6589127 : Blo 2165435 6589127 := bstep (se 1 (by rfl) ⟨4941845, by rfl⟩ : syracuseStep 6589127 = 9883691) B9883691
theorem B4392751 : Blo 2165435 4392751 := bstep (se 1 (by rfl) ⟨3294563, by rfl⟩ : syracuseStep 4392751 = 6589127) B6589127
theorem B5857001 : Blo 2165435 5857001 := bstep (se 2 (by rfl) ⟨2196375, by rfl⟩ : syracuseStep 5857001 = 4392751) B4392751
theorem B3904667 : Blo 2165435 3904667 := bstep (se 1 (by rfl) ⟨2928500, by rfl⟩ : syracuseStep 3904667 = 5857001) B5857001
theorem B2603111 : Blo 2165435 2603111 := bstep (se 1 (by rfl) ⟨1952333, by rfl⟩ : syracuseStep 2603111 = 3904667) B3904667
theorem B6941629 : Blo 2165435 6941629 := bstep (se 3 (by rfl) ⟨1301555, by rfl⟩ : syracuseStep 6941629 = 2603111) B2603111
theorem B9255505 : Blo 2165435 9255505 := bstep (se 2 (by rfl) ⟨3470814, by rfl⟩ : syracuseStep 9255505 = 6941629) B6941629
theorem B12340673 : Blo 2165435 12340673 := bstep (se 2 (by rfl) ⟨4627752, by rfl⟩ : syracuseStep 12340673 = 9255505) B9255505
theorem B8227115 : Blo 2165435 8227115 := bstep (se 1 (by rfl) ⟨6170336, by rfl⟩ : syracuseStep 8227115 = 12340673) B12340673
theorem B5484743 : Blo 2165435 5484743 := bstep (se 1 (by rfl) ⟨4113557, by rfl⟩ : syracuseStep 5484743 = 8227115) B8227115
theorem B3656495 : Blo 2165435 3656495 := bstep (se 1 (by rfl) ⟨2742371, by rfl⟩ : syracuseStep 3656495 = 5484743) B5484743
theorem B2437663 : Blo 2165435 2437663 := bstep (se 1 (by rfl) ⟨1828247, by rfl⟩ : syracuseStep 2437663 = 3656495) B3656495
theorem B3250217 : Blo 2165435 3250217 := bstep (se 2 (by rfl) ⟨1218831, by rfl⟩ : syracuseStep 3250217 = 2437663) B2437663
theorem B2166811 : Blo 2165435 2166811 := bstep (se 1 (by rfl) ⟨1625108, by rfl⟩ : syracuseStep 2166811 = 3250217) B3250217
theorem B8339381 : Blo 2165435 8339381 := bbase (se 5 (by rfl) ⟨390908, by rfl⟩ : syracuseStep 8339381 = 781817) (by norm_num)
theorem B5559587 : Blo 2165435 5559587 := bstep (se 1 (by rfl) ⟨4169690, by rfl⟩ : syracuseStep 5559587 = 8339381) B8339381
theorem B3706391 : Blo 2165435 3706391 := bstep (se 1 (by rfl) ⟨2779793, by rfl⟩ : syracuseStep 3706391 = 5559587) B5559587
theorem B2470927 : Blo 2165435 2470927 := bstep (se 1 (by rfl) ⟨1853195, by rfl⟩ : syracuseStep 2470927 = 3706391) B3706391
theorem B3294569 : Blo 2165435 3294569 := bstep (se 2 (by rfl) ⟨1235463, by rfl⟩ : syracuseStep 3294569 = 2470927) B2470927
theorem B2196379 : Blo 2165435 2196379 := bstep (se 1 (by rfl) ⟨1647284, by rfl⟩ : syracuseStep 2196379 = 3294569) B3294569
theorem B11714021 : Blo 2165435 11714021 := bstep (se 4 (by rfl) ⟨1098189, by rfl⟩ : syracuseStep 11714021 = 2196379) B2196379
theorem B7809347 : Blo 2165435 7809347 := bstep (se 1 (by rfl) ⟨5857010, by rfl⟩ : syracuseStep 7809347 = 11714021) B11714021
theorem B5206231 : Blo 2165435 5206231 := bstep (se 1 (by rfl) ⟨3904673, by rfl⟩ : syracuseStep 5206231 = 7809347) B7809347
theorem B6941641 : Blo 2165435 6941641 := bstep (se 2 (by rfl) ⟨2603115, by rfl⟩ : syracuseStep 6941641 = 5206231) B5206231
theorem B9255521 : Blo 2165435 9255521 := bstep (se 2 (by rfl) ⟨3470820, by rfl⟩ : syracuseStep 9255521 = 6941641) B6941641
theorem B6170347 : Blo 2165435 6170347 := bstep (se 1 (by rfl) ⟨4627760, by rfl⟩ : syracuseStep 6170347 = 9255521) B9255521
theorem B8227129 : Blo 2165435 8227129 := bstep (se 2 (by rfl) ⟨3085173, by rfl⟩ : syracuseStep 8227129 = 6170347) B6170347
theorem B10969505 : Blo 2165435 10969505 := bstep (se 2 (by rfl) ⟨4113564, by rfl⟩ : syracuseStep 10969505 = 8227129) B8227129
theorem B7313003 : Blo 2165435 7313003 := bstep (se 1 (by rfl) ⟨5484752, by rfl⟩ : syracuseStep 7313003 = 10969505) B10969505
theorem B4875335 : Blo 2165435 4875335 := bstep (se 1 (by rfl) ⟨3656501, by rfl⟩ : syracuseStep 4875335 = 7313003) B7313003
theorem B3250223 : Blo 2165435 3250223 := bstep (se 1 (by rfl) ⟨2437667, by rfl⟩ : syracuseStep 3250223 = 4875335) B4875335
theorem B2166815 : Blo 2165435 2166815 := bstep (se 1 (by rfl) ⟨1625111, by rfl⟩ : syracuseStep 2166815 = 3250223) B3250223
theorem B3250229 : Blo 2165435 3250229 := bbase (se 5 (by rfl) ⟨152354, by rfl⟩ : syracuseStep 3250229 = 304709) (by norm_num)
theorem B2166819 : Blo 2165435 2166819 := bstep (se 1 (by rfl) ⟨1625114, by rfl⟩ : syracuseStep 2166819 = 3250229) B3250229
theorem B5484773 : Blo 2165435 5484773 := bbase (se 4 (by rfl) ⟨514197, by rfl⟩ : syracuseStep 5484773 = 1028395) (by norm_num)
theorem B3656515 : Blo 2165435 3656515 := bstep (se 1 (by rfl) ⟨2742386, by rfl⟩ : syracuseStep 3656515 = 5484773) B5484773
theorem B4875353 : Blo 2165435 4875353 := bstep (se 2 (by rfl) ⟨1828257, by rfl⟩ : syracuseStep 4875353 = 3656515) B3656515
theorem B3250235 : Blo 2165435 3250235 := bstep (se 1 (by rfl) ⟨2437676, by rfl⟩ : syracuseStep 3250235 = 4875353) B4875353
theorem B2166823 : Blo 2165435 2166823 := bstep (se 1 (by rfl) ⟨1625117, by rfl⟩ : syracuseStep 2166823 = 3250235) B3250235
theorem B2437681 : Blo 2165435 2437681 := bbase (se 2 (by rfl) ⟨914130, by rfl⟩ : syracuseStep 2437681 = 1828261) (by norm_num)
theorem B3250241 : Blo 2165435 3250241 := bstep (se 2 (by rfl) ⟨1218840, by rfl⟩ : syracuseStep 3250241 = 2437681) B2437681
theorem B2166827 : Blo 2165435 2166827 := bstep (se 1 (by rfl) ⟨1625120, by rfl⟩ : syracuseStep 2166827 = 3250241) B3250241
theorem B6254581 : Blo 2165435 6254581 := bbase (se 5 (by rfl) ⟨293183, by rfl⟩ : syracuseStep 6254581 = 586367) (by norm_num)
theorem B8339441 : Blo 2165435 8339441 := bstep (se 2 (by rfl) ⟨3127290, by rfl⟩ : syracuseStep 8339441 = 6254581) B6254581
theorem B22238509 : Blo 2165435 22238509 := bstep (se 3 (by rfl) ⟨4169720, by rfl⟩ : syracuseStep 22238509 = 8339441) B8339441
theorem B29651345 : Blo 2165435 29651345 := bstep (se 2 (by rfl) ⟨11119254, by rfl⟩ : syracuseStep 29651345 = 22238509) B22238509
theorem B19767563 : Blo 2165435 19767563 := bstep (se 1 (by rfl) ⟨14825672, by rfl⟩ : syracuseStep 19767563 = 29651345) B29651345
theorem B13178375 : Blo 2165435 13178375 := bstep (se 1 (by rfl) ⟨9883781, by rfl⟩ : syracuseStep 13178375 = 19767563) B19767563
theorem B8785583 : Blo 2165435 8785583 := bstep (se 1 (by rfl) ⟨6589187, by rfl⟩ : syracuseStep 8785583 = 13178375) B13178375
theorem B5857055 : Blo 2165435 5857055 := bstep (se 1 (by rfl) ⟨4392791, by rfl⟩ : syracuseStep 5857055 = 8785583) B8785583
theorem B3904703 : Blo 2165435 3904703 := bstep (se 1 (by rfl) ⟨2928527, by rfl⟩ : syracuseStep 3904703 = 5857055) B5857055
theorem B2603135 : Blo 2165435 2603135 := bstep (se 1 (by rfl) ⟨1952351, by rfl⟩ : syracuseStep 2603135 = 3904703) B3904703
theorem B6941693 : Blo 2165435 6941693 := bstep (se 3 (by rfl) ⟨1301567, by rfl⟩ : syracuseStep 6941693 = 2603135) B2603135
theorem B4627795 : Blo 2165435 4627795 := bstep (se 1 (by rfl) ⟨3470846, by rfl⟩ : syracuseStep 4627795 = 6941693) B6941693
theorem B6170393 : Blo 2165435 6170393 := bstep (se 2 (by rfl) ⟨2313897, by rfl⟩ : syracuseStep 6170393 = 4627795) B4627795
theorem B4113595 : Blo 2165435 4113595 := bstep (se 1 (by rfl) ⟨3085196, by rfl⟩ : syracuseStep 4113595 = 6170393) B6170393
theorem B5484793 : Blo 2165435 5484793 := bstep (se 2 (by rfl) ⟨2056797, by rfl⟩ : syracuseStep 5484793 = 4113595) B4113595
theorem B7313057 : Blo 2165435 7313057 := bstep (se 2 (by rfl) ⟨2742396, by rfl⟩ : syracuseStep 7313057 = 5484793) B5484793
theorem B4875371 : Blo 2165435 4875371 := bstep (se 1 (by rfl) ⟨3656528, by rfl⟩ : syracuseStep 4875371 = 7313057) B7313057
theorem B3250247 : Blo 2165435 3250247 := bstep (se 1 (by rfl) ⟨2437685, by rfl⟩ : syracuseStep 3250247 = 4875371) B4875371
theorem B2166831 : Blo 2165435 2166831 := bstep (se 1 (by rfl) ⟨1625123, by rfl⟩ : syracuseStep 2166831 = 3250247) B3250247
theorem B3250253 : Blo 2165435 3250253 := bbase (se 3 (by rfl) ⟨609422, by rfl⟩ : syracuseStep 3250253 = 1218845) (by norm_num)
theorem B2166835 : Blo 2165435 2166835 := bstep (se 1 (by rfl) ⟨1625126, by rfl⟩ : syracuseStep 2166835 = 3250253) B3250253
theorem B4875389 : Blo 2165435 4875389 := bbase (se 3 (by rfl) ⟨914135, by rfl⟩ : syracuseStep 4875389 = 1828271) (by norm_num)
theorem B3250259 : Blo 2165435 3250259 := bstep (se 1 (by rfl) ⟨2437694, by rfl⟩ : syracuseStep 3250259 = 4875389) B4875389
theorem B2166839 : Blo 2165435 2166839 := bstep (se 1 (by rfl) ⟨1625129, by rfl⟩ : syracuseStep 2166839 = 3250259) B3250259
theorem B3656549 : Blo 2165435 3656549 := bbase (se 4 (by rfl) ⟨342801, by rfl⟩ : syracuseStep 3656549 = 685603) (by norm_num)
theorem B2437699 : Blo 2165435 2437699 := bstep (se 1 (by rfl) ⟨1828274, by rfl⟩ : syracuseStep 2437699 = 3656549) B3656549
theorem B3250265 : Blo 2165435 3250265 := bstep (se 2 (by rfl) ⟨1218849, by rfl⟩ : syracuseStep 3250265 = 2437699) B2437699
theorem B2166843 : Blo 2165435 2166843 := bstep (se 1 (by rfl) ⟨1625132, by rfl⟩ : syracuseStep 2166843 = 3250265) B3250265
theorem B4627829 : Blo 2165435 4627829 := bbase (se 5 (by rfl) ⟨216929, by rfl⟩ : syracuseStep 4627829 = 433859) (by norm_num)
theorem B3085219 : Blo 2165435 3085219 := bstep (se 1 (by rfl) ⟨2313914, by rfl⟩ : syracuseStep 3085219 = 4627829) B4627829
theorem B16454501 : Blo 2165435 16454501 := bstep (se 4 (by rfl) ⟨1542609, by rfl⟩ : syracuseStep 16454501 = 3085219) B3085219
theorem B10969667 : Blo 2165435 10969667 := bstep (se 1 (by rfl) ⟨8227250, by rfl⟩ : syracuseStep 10969667 = 16454501) B16454501
theorem B7313111 : Blo 2165435 7313111 := bstep (se 1 (by rfl) ⟨5484833, by rfl⟩ : syracuseStep 7313111 = 10969667) B10969667
theorem B4875407 : Blo 2165435 4875407 := bstep (se 1 (by rfl) ⟨3656555, by rfl⟩ : syracuseStep 4875407 = 7313111) B7313111
theorem B3250271 : Blo 2165435 3250271 := bstep (se 1 (by rfl) ⟨2437703, by rfl⟩ : syracuseStep 3250271 = 4875407) B4875407
theorem B2166847 : Blo 2165435 2166847 := bstep (se 1 (by rfl) ⟨1625135, by rfl⟩ : syracuseStep 2166847 = 3250271) B3250271
theorem B3250277 : Blo 2165435 3250277 := bbase (se 4 (by rfl) ⟨304713, by rfl⟩ : syracuseStep 3250277 = 609427) (by norm_num)
theorem B2166851 : Blo 2165435 2166851 := bstep (se 1 (by rfl) ⟨1625138, by rfl⟩ : syracuseStep 2166851 = 3250277) B3250277
theorem B7809493 : Blo 2165435 7809493 := bbase (se 7 (by rfl) ⟨91517, by rfl⟩ : syracuseStep 7809493 = 183035) (by norm_num)
theorem B10412657 : Blo 2165435 10412657 := bstep (se 2 (by rfl) ⟨3904746, by rfl⟩ : syracuseStep 10412657 = 7809493) B7809493
theorem B6941771 : Blo 2165435 6941771 := bstep (se 1 (by rfl) ⟨5206328, by rfl⟩ : syracuseStep 6941771 = 10412657) B10412657
theorem B4627847 : Blo 2165435 4627847 := bstep (se 1 (by rfl) ⟨3470885, by rfl⟩ : syracuseStep 4627847 = 6941771) B6941771
theorem B3085231 : Blo 2165435 3085231 := bstep (se 1 (by rfl) ⟨2313923, by rfl⟩ : syracuseStep 3085231 = 4627847) B4627847
theorem B4113641 : Blo 2165435 4113641 := bstep (se 2 (by rfl) ⟨1542615, by rfl⟩ : syracuseStep 4113641 = 3085231) B3085231
theorem B2742427 : Blo 2165435 2742427 := bstep (se 1 (by rfl) ⟨2056820, by rfl⟩ : syracuseStep 2742427 = 4113641) B4113641
theorem B3656569 : Blo 2165435 3656569 := bstep (se 2 (by rfl) ⟨1371213, by rfl⟩ : syracuseStep 3656569 = 2742427) B2742427
theorem B4875425 : Blo 2165435 4875425 := bstep (se 2 (by rfl) ⟨1828284, by rfl⟩ : syracuseStep 4875425 = 3656569) B3656569
theorem B3250283 : Blo 2165435 3250283 := bstep (se 1 (by rfl) ⟨2437712, by rfl⟩ : syracuseStep 3250283 = 4875425) B4875425
theorem B2166855 : Blo 2165435 2166855 := bstep (se 1 (by rfl) ⟨1625141, by rfl⟩ : syracuseStep 2166855 = 3250283) B3250283
theorem B2437717 : Blo 2165435 2437717 := bbase (se 8 (by rfl) ⟨14283, by rfl⟩ : syracuseStep 2437717 = 28567) (by norm_num)
theorem B3250289 : Blo 2165435 3250289 := bstep (se 2 (by rfl) ⟨1218858, by rfl⟩ : syracuseStep 3250289 = 2437717) B2437717
theorem B2166859 : Blo 2165435 2166859 := bstep (se 1 (by rfl) ⟨1625144, by rfl⟩ : syracuseStep 2166859 = 3250289) B3250289
theorem B2742437 : Blo 2165435 2742437 := bbase (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) (by norm_num)
theorem B7313165 : Blo 2165435 7313165 := bstep (se 3 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 7313165 = 2742437) B2742437
theorem B4875443 : Blo 2165435 4875443 := bstep (se 1 (by rfl) ⟨3656582, by rfl⟩ : syracuseStep 4875443 = 7313165) B7313165
theorem B3250295 : Blo 2165435 3250295 := bstep (se 1 (by rfl) ⟨2437721, by rfl⟩ : syracuseStep 3250295 = 4875443) B4875443
theorem B2166863 : Blo 2165435 2166863 := bstep (se 1 (by rfl) ⟨1625147, by rfl⟩ : syracuseStep 2166863 = 3250295) B3250295
theorem B3250301 : Blo 2165435 3250301 := bbase (se 3 (by rfl) ⟨609431, by rfl⟩ : syracuseStep 3250301 = 1218863) (by norm_num)
theorem B2166867 : Blo 2165435 2166867 := bstep (se 1 (by rfl) ⟨1625150, by rfl⟩ : syracuseStep 2166867 = 3250301) B3250301
theorem B4875461 : Blo 2165435 4875461 := bbase (se 4 (by rfl) ⟨457074, by rfl⟩ : syracuseStep 4875461 = 914149) (by norm_num)
theorem B3250307 : Blo 2165435 3250307 := bstep (se 1 (by rfl) ⟨2437730, by rfl⟩ : syracuseStep 3250307 = 4875461) B4875461
theorem B2166871 : Blo 2165435 2166871 := bstep (se 1 (by rfl) ⟨1625153, by rfl⟩ : syracuseStep 2166871 = 3250307) B3250307
theorem B13883669 : Blo 2165435 13883669 := bbase (se 6 (by rfl) ⟨325398, by rfl⟩ : syracuseStep 13883669 = 650797) (by norm_num)
theorem B9255779 : Blo 2165435 9255779 := bstep (se 1 (by rfl) ⟨6941834, by rfl⟩ : syracuseStep 9255779 = 13883669) B13883669
theorem B6170519 : Blo 2165435 6170519 := bstep (se 1 (by rfl) ⟨4627889, by rfl⟩ : syracuseStep 6170519 = 9255779) B9255779
theorem B4113679 : Blo 2165435 4113679 := bstep (se 1 (by rfl) ⟨3085259, by rfl⟩ : syracuseStep 4113679 = 6170519) B6170519
theorem B5484905 : Blo 2165435 5484905 := bstep (se 2 (by rfl) ⟨2056839, by rfl⟩ : syracuseStep 5484905 = 4113679) B4113679
theorem B3656603 : Blo 2165435 3656603 := bstep (se 1 (by rfl) ⟨2742452, by rfl⟩ : syracuseStep 3656603 = 5484905) B5484905
theorem B2437735 : Blo 2165435 2437735 := bstep (se 1 (by rfl) ⟨1828301, by rfl⟩ : syracuseStep 2437735 = 3656603) B3656603
theorem B3250313 : Blo 2165435 3250313 := bstep (se 2 (by rfl) ⟨1218867, by rfl⟩ : syracuseStep 3250313 = 2437735) B2437735
theorem B2166875 : Blo 2165435 2166875 := bstep (se 1 (by rfl) ⟨1625156, by rfl⟩ : syracuseStep 2166875 = 3250313) B3250313
theorem B10969829 : Blo 2165435 10969829 := bbase (se 4 (by rfl) ⟨1028421, by rfl⟩ : syracuseStep 10969829 = 2056843) (by norm_num)
theorem B7313219 : Blo 2165435 7313219 := bstep (se 1 (by rfl) ⟨5484914, by rfl⟩ : syracuseStep 7313219 = 10969829) B10969829
theorem B4875479 : Blo 2165435 4875479 := bstep (se 1 (by rfl) ⟨3656609, by rfl⟩ : syracuseStep 4875479 = 7313219) B7313219
theorem B3250319 : Blo 2165435 3250319 := bstep (se 1 (by rfl) ⟨2437739, by rfl⟩ : syracuseStep 3250319 = 4875479) B4875479
theorem B2166879 : Blo 2165435 2166879 := bstep (se 1 (by rfl) ⟨1625159, by rfl⟩ : syracuseStep 2166879 = 3250319) B3250319
theorem B3250325 : Blo 2165435 3250325 := bbase (se 6 (by rfl) ⟨76179, by rfl⟩ : syracuseStep 3250325 = 152359) (by norm_num)
theorem B2166883 : Blo 2165435 2166883 := bstep (se 1 (by rfl) ⟨1625162, by rfl⟩ : syracuseStep 2166883 = 3250325) B3250325
theorem B9255829 : Blo 2165435 9255829 := bbase (se 6 (by rfl) ⟨216933, by rfl⟩ : syracuseStep 9255829 = 433867) (by norm_num)
theorem B12341105 : Blo 2165435 12341105 := bstep (se 2 (by rfl) ⟨4627914, by rfl⟩ : syracuseStep 12341105 = 9255829) B9255829
theorem B8227403 : Blo 2165435 8227403 := bstep (se 1 (by rfl) ⟨6170552, by rfl⟩ : syracuseStep 8227403 = 12341105) B12341105
theorem B5484935 : Blo 2165435 5484935 := bstep (se 1 (by rfl) ⟨4113701, by rfl⟩ : syracuseStep 5484935 = 8227403) B8227403
theorem B3656623 : Blo 2165435 3656623 := bstep (se 1 (by rfl) ⟨2742467, by rfl⟩ : syracuseStep 3656623 = 5484935) B5484935
theorem B4875497 : Blo 2165435 4875497 := bstep (se 2 (by rfl) ⟨1828311, by rfl⟩ : syracuseStep 4875497 = 3656623) B3656623
theorem B3250331 : Blo 2165435 3250331 := bstep (se 1 (by rfl) ⟨2437748, by rfl⟩ : syracuseStep 3250331 = 4875497) B4875497
theorem B2166887 : Blo 2165435 2166887 := bstep (se 1 (by rfl) ⟨1625165, by rfl⟩ : syracuseStep 2166887 = 3250331) B3250331
theorem B2437753 : Blo 2165435 2437753 := bbase (se 2 (by rfl) ⟨914157, by rfl⟩ : syracuseStep 2437753 = 1828315) (by norm_num)
theorem B3250337 : Blo 2165435 3250337 := bstep (se 2 (by rfl) ⟨1218876, by rfl⟩ : syracuseStep 3250337 = 2437753) B2437753
theorem B2166891 : Blo 2165435 2166891 := bstep (se 1 (by rfl) ⟨1625168, by rfl⟩ : syracuseStep 2166891 = 3250337) B3250337
theorem B11714453 : Blo 2165435 11714453 := bbase (se 6 (by rfl) ⟨274557, by rfl⟩ : syracuseStep 11714453 = 549115) (by norm_num)
theorem B7809635 : Blo 2165435 7809635 := bstep (se 1 (by rfl) ⟨5857226, by rfl⟩ : syracuseStep 7809635 = 11714453) B11714453
theorem B20825693 : Blo 2165435 20825693 := bstep (se 3 (by rfl) ⟨3904817, by rfl⟩ : syracuseStep 20825693 = 7809635) B7809635
theorem B13883795 : Blo 2165435 13883795 := bstep (se 1 (by rfl) ⟨10412846, by rfl⟩ : syracuseStep 13883795 = 20825693) B20825693
theorem B9255863 : Blo 2165435 9255863 := bstep (se 1 (by rfl) ⟨6941897, by rfl⟩ : syracuseStep 9255863 = 13883795) B13883795
theorem B6170575 : Blo 2165435 6170575 := bstep (se 1 (by rfl) ⟨4627931, by rfl⟩ : syracuseStep 6170575 = 9255863) B9255863
theorem B8227433 : Blo 2165435 8227433 := bstep (se 2 (by rfl) ⟨3085287, by rfl⟩ : syracuseStep 8227433 = 6170575) B6170575
theorem B5484955 : Blo 2165435 5484955 := bstep (se 1 (by rfl) ⟨4113716, by rfl⟩ : syracuseStep 5484955 = 8227433) B8227433
theorem B7313273 : Blo 2165435 7313273 := bstep (se 2 (by rfl) ⟨2742477, by rfl⟩ : syracuseStep 7313273 = 5484955) B5484955
theorem B4875515 : Blo 2165435 4875515 := bstep (se 1 (by rfl) ⟨3656636, by rfl⟩ : syracuseStep 4875515 = 7313273) B7313273
theorem B3250343 : Blo 2165435 3250343 := bstep (se 1 (by rfl) ⟨2437757, by rfl⟩ : syracuseStep 3250343 = 4875515) B4875515
theorem B2166895 : Blo 2165435 2166895 := bstep (se 1 (by rfl) ⟨1625171, by rfl⟩ : syracuseStep 2166895 = 3250343) B3250343
theorem B3250349 : Blo 2165435 3250349 := bbase (se 3 (by rfl) ⟨609440, by rfl⟩ : syracuseStep 3250349 = 1218881) (by norm_num)
theorem B2166899 : Blo 2165435 2166899 := bstep (se 1 (by rfl) ⟨1625174, by rfl⟩ : syracuseStep 2166899 = 3250349) B3250349
theorem B4875533 : Blo 2165435 4875533 := bbase (se 3 (by rfl) ⟨914162, by rfl⟩ : syracuseStep 4875533 = 1828325) (by norm_num)
theorem B3250355 : Blo 2165435 3250355 := bstep (se 1 (by rfl) ⟨2437766, by rfl⟩ : syracuseStep 3250355 = 4875533) B4875533
theorem B2166903 : Blo 2165435 2166903 := bstep (se 1 (by rfl) ⟨1625177, by rfl⟩ : syracuseStep 2166903 = 3250355) B3250355
theorem B2742493 : Blo 2165435 2742493 := bbase (se 3 (by rfl) ⟨514217, by rfl⟩ : syracuseStep 2742493 = 1028435) (by norm_num)
theorem B3656657 : Blo 2165435 3656657 := bstep (se 2 (by rfl) ⟨1371246, by rfl⟩ : syracuseStep 3656657 = 2742493) B2742493
theorem B2437771 : Blo 2165435 2437771 := bstep (se 1 (by rfl) ⟨1828328, by rfl⟩ : syracuseStep 2437771 = 3656657) B3656657
theorem B3250361 : Blo 2165435 3250361 := bstep (se 2 (by rfl) ⟨1218885, by rfl⟩ : syracuseStep 3250361 = 2437771) B2437771
theorem B2166907 : Blo 2165435 2166907 := bstep (se 1 (by rfl) ⟨1625180, by rfl⟩ : syracuseStep 2166907 = 3250361) B3250361
theorem B18511861 : Blo 2165435 18511861 := bbase (se 5 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 18511861 = 1735487) (by norm_num)
theorem B24682481 : Blo 2165435 24682481 := bstep (se 2 (by rfl) ⟨9255930, by rfl⟩ : syracuseStep 24682481 = 18511861) B18511861
theorem B16454987 : Blo 2165435 16454987 := bstep (se 1 (by rfl) ⟨12341240, by rfl⟩ : syracuseStep 16454987 = 24682481) B24682481
theorem B10969991 : Blo 2165435 10969991 := bstep (se 1 (by rfl) ⟨8227493, by rfl⟩ : syracuseStep 10969991 = 16454987) B16454987
theorem B7313327 : Blo 2165435 7313327 := bstep (se 1 (by rfl) ⟨5484995, by rfl⟩ : syracuseStep 7313327 = 10969991) B10969991
theorem B4875551 : Blo 2165435 4875551 := bstep (se 1 (by rfl) ⟨3656663, by rfl⟩ : syracuseStep 4875551 = 7313327) B7313327
theorem B3250367 : Blo 2165435 3250367 := bstep (se 1 (by rfl) ⟨2437775, by rfl⟩ : syracuseStep 3250367 = 4875551) B4875551
theorem B2166911 : Blo 2165435 2166911 := bstep (se 1 (by rfl) ⟨1625183, by rfl⟩ : syracuseStep 2166911 = 3250367) B3250367
theorem B3250373 : Blo 2165435 3250373 := bbase (se 4 (by rfl) ⟨304722, by rfl⟩ : syracuseStep 3250373 = 609445) (by norm_num)
theorem B2166915 : Blo 2165435 2166915 := bstep (se 1 (by rfl) ⟨1625186, by rfl⟩ : syracuseStep 2166915 = 3250373) B3250373
theorem B3656677 : Blo 2165435 3656677 := bbase (se 4 (by rfl) ⟨342813, by rfl⟩ : syracuseStep 3656677 = 685627) (by norm_num)
theorem B4875569 : Blo 2165435 4875569 := bstep (se 2 (by rfl) ⟨1828338, by rfl⟩ : syracuseStep 4875569 = 3656677) B3656677
theorem B3250379 : Blo 2165435 3250379 := bstep (se 1 (by rfl) ⟨2437784, by rfl⟩ : syracuseStep 3250379 = 4875569) B4875569
theorem B2166919 : Blo 2165435 2166919 := bstep (se 1 (by rfl) ⟨1625189, by rfl⟩ : syracuseStep 2166919 = 3250379) B3250379
theorem B2437789 : Blo 2165435 2437789 := bbase (se 3 (by rfl) ⟨457085, by rfl⟩ : syracuseStep 2437789 = 914171) (by norm_num)
theorem B3250385 : Blo 2165435 3250385 := bstep (se 2 (by rfl) ⟨1218894, by rfl⟩ : syracuseStep 3250385 = 2437789) B2437789
theorem B2166923 : Blo 2165435 2166923 := bstep (se 1 (by rfl) ⟨1625192, by rfl⟩ : syracuseStep 2166923 = 3250385) B3250385
theorem B7313381 : Blo 2165435 7313381 := bbase (se 4 (by rfl) ⟨685629, by rfl⟩ : syracuseStep 7313381 = 1371259) (by norm_num)
theorem B4875587 : Blo 2165435 4875587 := bstep (se 1 (by rfl) ⟨3656690, by rfl⟩ : syracuseStep 4875587 = 7313381) B7313381
theorem B3250391 : Blo 2165435 3250391 := bstep (se 1 (by rfl) ⟨2437793, by rfl⟩ : syracuseStep 3250391 = 4875587) B4875587
theorem B2166927 : Blo 2165435 2166927 := bstep (se 1 (by rfl) ⟨1625195, by rfl⟩ : syracuseStep 2166927 = 3250391) B3250391
theorem B3250397 : Blo 2165435 3250397 := bbase (se 3 (by rfl) ⟨609449, by rfl⟩ : syracuseStep 3250397 = 1218899) (by norm_num)
theorem B2166931 : Blo 2165435 2166931 := bstep (se 1 (by rfl) ⟨1625198, by rfl⟩ : syracuseStep 2166931 = 3250397) B3250397
theorem B4875605 : Blo 2165435 4875605 := bbase (se 12 (by rfl) ⟨1785, by rfl⟩ : syracuseStep 4875605 = 3571) (by norm_num)
theorem B3250403 : Blo 2165435 3250403 := bstep (se 1 (by rfl) ⟨2437802, by rfl⟩ : syracuseStep 3250403 = 4875605) B4875605
theorem B2166935 : Blo 2165435 2166935 := bstep (se 1 (by rfl) ⟨1625201, by rfl⟩ : syracuseStep 2166935 = 3250403) B3250403
theorem B2314013 : Blo 2165435 2314013 := bbase (se 3 (by rfl) ⟨433877, by rfl⟩ : syracuseStep 2314013 = 867755) (by norm_num)
theorem B6170701 : Blo 2165435 6170701 := bstep (se 3 (by rfl) ⟨1157006, by rfl⟩ : syracuseStep 6170701 = 2314013) B2314013
theorem B8227601 : Blo 2165435 8227601 := bstep (se 2 (by rfl) ⟨3085350, by rfl⟩ : syracuseStep 8227601 = 6170701) B6170701
theorem B5485067 : Blo 2165435 5485067 := bstep (se 1 (by rfl) ⟨4113800, by rfl⟩ : syracuseStep 5485067 = 8227601) B8227601
theorem B3656711 : Blo 2165435 3656711 := bstep (se 1 (by rfl) ⟨2742533, by rfl⟩ : syracuseStep 3656711 = 5485067) B5485067
theorem B2437807 : Blo 2165435 2437807 := bstep (se 1 (by rfl) ⟨1828355, by rfl⟩ : syracuseStep 2437807 = 3656711) B3656711
theorem B3250409 : Blo 2165435 3250409 := bstep (se 2 (by rfl) ⟨1218903, by rfl⟩ : syracuseStep 3250409 = 2437807) B2437807
theorem B2166939 : Blo 2165435 2166939 := bstep (se 1 (by rfl) ⟨1625204, by rfl⟩ : syracuseStep 2166939 = 3250409) B3250409
theorem B26358101 : Blo 2165435 26358101 := bbase (se 10 (by rfl) ⟨38610, by rfl⟩ : syracuseStep 26358101 = 77221) (by norm_num)
theorem B17572067 : Blo 2165435 17572067 := bstep (se 1 (by rfl) ⟨13179050, by rfl⟩ : syracuseStep 17572067 = 26358101) B26358101
theorem B11714711 : Blo 2165435 11714711 := bstep (se 1 (by rfl) ⟨8786033, by rfl⟩ : syracuseStep 11714711 = 17572067) B17572067
theorem B31239229 : Blo 2165435 31239229 := bstep (se 3 (by rfl) ⟨5857355, by rfl⟩ : syracuseStep 31239229 = 11714711) B11714711
theorem B41652305 : Blo 2165435 41652305 := bstep (se 2 (by rfl) ⟨15619614, by rfl⟩ : syracuseStep 41652305 = 31239229) B31239229
theorem B27768203 : Blo 2165435 27768203 := bstep (se 1 (by rfl) ⟨20826152, by rfl⟩ : syracuseStep 27768203 = 41652305) B41652305
theorem B18512135 : Blo 2165435 18512135 := bstep (se 1 (by rfl) ⟨13884101, by rfl⟩ : syracuseStep 18512135 = 27768203) B27768203
theorem B12341423 : Blo 2165435 12341423 := bstep (se 1 (by rfl) ⟨9256067, by rfl⟩ : syracuseStep 12341423 = 18512135) B18512135
theorem B8227615 : Blo 2165435 8227615 := bstep (se 1 (by rfl) ⟨6170711, by rfl⟩ : syracuseStep 8227615 = 12341423) B12341423
theorem B10970153 : Blo 2165435 10970153 := bstep (se 2 (by rfl) ⟨4113807, by rfl⟩ : syracuseStep 10970153 = 8227615) B8227615
theorem B7313435 : Blo 2165435 7313435 := bstep (se 1 (by rfl) ⟨5485076, by rfl⟩ : syracuseStep 7313435 = 10970153) B10970153
theorem B4875623 : Blo 2165435 4875623 := bstep (se 1 (by rfl) ⟨3656717, by rfl⟩ : syracuseStep 4875623 = 7313435) B7313435
theorem B3250415 : Blo 2165435 3250415 := bstep (se 1 (by rfl) ⟨2437811, by rfl⟩ : syracuseStep 3250415 = 4875623) B4875623
theorem B2166943 : Blo 2165435 2166943 := bstep (se 1 (by rfl) ⟨1625207, by rfl⟩ : syracuseStep 2166943 = 3250415) B3250415
theorem B3250421 : Blo 2165435 3250421 := bbase (se 5 (by rfl) ⟨152363, by rfl⟩ : syracuseStep 3250421 = 304727) (by norm_num)
theorem B2166947 : Blo 2165435 2166947 := bstep (se 1 (by rfl) ⟨1625210, by rfl⟩ : syracuseStep 2166947 = 3250421) B3250421
theorem B33814741 : Blo 2165435 33814741 := bbase (se 7 (by rfl) ⟨396266, by rfl⟩ : syracuseStep 33814741 = 792533) (by norm_num)
theorem B45086321 : Blo 2165435 45086321 := bstep (se 2 (by rfl) ⟨16907370, by rfl⟩ : syracuseStep 45086321 = 33814741) B33814741
theorem B120230189 : Blo 2165435 120230189 := bstep (se 3 (by rfl) ⟨22543160, by rfl⟩ : syracuseStep 120230189 = 45086321) B45086321
theorem B80153459 : Blo 2165435 80153459 := bstep (se 1 (by rfl) ⟨60115094, by rfl⟩ : syracuseStep 80153459 = 120230189) B120230189
theorem B53435639 : Blo 2165435 53435639 := bstep (se 1 (by rfl) ⟨40076729, by rfl⟩ : syracuseStep 53435639 = 80153459) B80153459
theorem B35623759 : Blo 2165435 35623759 := bstep (se 1 (by rfl) ⟨26717819, by rfl⟩ : syracuseStep 35623759 = 53435639) B53435639
theorem B47498345 : Blo 2165435 47498345 := bstep (se 2 (by rfl) ⟨17811879, by rfl⟩ : syracuseStep 47498345 = 35623759) B35623759
theorem B31665563 : Blo 2165435 31665563 := bstep (se 1 (by rfl) ⟨23749172, by rfl⟩ : syracuseStep 31665563 = 47498345) B47498345
theorem B21110375 : Blo 2165435 21110375 := bstep (se 1 (by rfl) ⟨15832781, by rfl⟩ : syracuseStep 21110375 = 31665563) B31665563
theorem B14073583 : Blo 2165435 14073583 := bstep (se 1 (by rfl) ⟨10555187, by rfl⟩ : syracuseStep 14073583 = 21110375) B21110375
theorem B18764777 : Blo 2165435 18764777 := bstep (se 2 (by rfl) ⟨7036791, by rfl⟩ : syracuseStep 18764777 = 14073583) B14073583
theorem B12509851 : Blo 2165435 12509851 := bstep (se 1 (by rfl) ⟨9382388, by rfl⟩ : syracuseStep 12509851 = 18764777) B18764777
theorem B16679801 : Blo 2165435 16679801 := bstep (se 2 (by rfl) ⟨6254925, by rfl⟩ : syracuseStep 16679801 = 12509851) B12509851
theorem B44479469 : Blo 2165435 44479469 := bstep (se 3 (by rfl) ⟨8339900, by rfl⟩ : syracuseStep 44479469 = 16679801) B16679801
theorem B29652979 : Blo 2165435 29652979 := bstep (se 1 (by rfl) ⟨22239734, by rfl⟩ : syracuseStep 29652979 = 44479469) B44479469
theorem B39537305 : Blo 2165435 39537305 := bstep (se 2 (by rfl) ⟨14826489, by rfl⟩ : syracuseStep 39537305 = 29652979) B29652979
theorem B26358203 : Blo 2165435 26358203 := bstep (se 1 (by rfl) ⟨19768652, by rfl⟩ : syracuseStep 26358203 = 39537305) B39537305
theorem B17572135 : Blo 2165435 17572135 := bstep (se 1 (by rfl) ⟨13179101, by rfl⟩ : syracuseStep 17572135 = 26358203) B26358203
theorem B23429513 : Blo 2165435 23429513 := bstep (se 2 (by rfl) ⟨8786067, by rfl⟩ : syracuseStep 23429513 = 17572135) B17572135
theorem B15619675 : Blo 2165435 15619675 := bstep (se 1 (by rfl) ⟨11714756, by rfl⟩ : syracuseStep 15619675 = 23429513) B23429513
theorem B20826233 : Blo 2165435 20826233 := bstep (se 2 (by rfl) ⟨7809837, by rfl⟩ : syracuseStep 20826233 = 15619675) B15619675
theorem B13884155 : Blo 2165435 13884155 := bstep (se 1 (by rfl) ⟨10413116, by rfl⟩ : syracuseStep 13884155 = 20826233) B20826233
theorem B9256103 : Blo 2165435 9256103 := bstep (se 1 (by rfl) ⟨6942077, by rfl⟩ : syracuseStep 9256103 = 13884155) B13884155
theorem B6170735 : Blo 2165435 6170735 := bstep (se 1 (by rfl) ⟨4628051, by rfl⟩ : syracuseStep 6170735 = 9256103) B9256103
theorem B4113823 : Blo 2165435 4113823 := bstep (se 1 (by rfl) ⟨3085367, by rfl⟩ : syracuseStep 4113823 = 6170735) B6170735
theorem B5485097 : Blo 2165435 5485097 := bstep (se 2 (by rfl) ⟨2056911, by rfl⟩ : syracuseStep 5485097 = 4113823) B4113823
theorem B3656731 : Blo 2165435 3656731 := bstep (se 1 (by rfl) ⟨2742548, by rfl⟩ : syracuseStep 3656731 = 5485097) B5485097
theorem B4875641 : Blo 2165435 4875641 := bstep (se 2 (by rfl) ⟨1828365, by rfl⟩ : syracuseStep 4875641 = 3656731) B3656731
theorem B3250427 : Blo 2165435 3250427 := bstep (se 1 (by rfl) ⟨2437820, by rfl⟩ : syracuseStep 3250427 = 4875641) B4875641
theorem B2166951 : Blo 2165435 2166951 := bstep (se 1 (by rfl) ⟨1625213, by rfl⟩ : syracuseStep 2166951 = 3250427) B3250427
theorem B2437825 : Blo 2165435 2437825 := bbase (se 2 (by rfl) ⟨914184, by rfl⟩ : syracuseStep 2437825 = 1828369) (by norm_num)
theorem B3250433 : Blo 2165435 3250433 := bstep (se 2 (by rfl) ⟨1218912, by rfl⟩ : syracuseStep 3250433 = 2437825) B2437825
theorem B2166955 : Blo 2165435 2166955 := bstep (se 1 (by rfl) ⟨1625216, by rfl⟩ : syracuseStep 2166955 = 3250433) B3250433
theorem B5485117 : Blo 2165435 5485117 := bbase (se 3 (by rfl) ⟨1028459, by rfl⟩ : syracuseStep 5485117 = 2056919) (by norm_num)
theorem B7313489 : Blo 2165435 7313489 := bstep (se 2 (by rfl) ⟨2742558, by rfl⟩ : syracuseStep 7313489 = 5485117) B5485117
theorem B4875659 : Blo 2165435 4875659 := bstep (se 1 (by rfl) ⟨3656744, by rfl⟩ : syracuseStep 4875659 = 7313489) B7313489
theorem B3250439 : Blo 2165435 3250439 := bstep (se 1 (by rfl) ⟨2437829, by rfl⟩ : syracuseStep 3250439 = 4875659) B4875659
theorem B2166959 : Blo 2165435 2166959 := bstep (se 1 (by rfl) ⟨1625219, by rfl⟩ : syracuseStep 2166959 = 3250439) B3250439
theorem B3250445 : Blo 2165435 3250445 := bbase (se 3 (by rfl) ⟨609458, by rfl⟩ : syracuseStep 3250445 = 1218917) (by norm_num)
theorem B2166963 : Blo 2165435 2166963 := bstep (se 1 (by rfl) ⟨1625222, by rfl⟩ : syracuseStep 2166963 = 3250445) B3250445
theorem B4875677 : Blo 2165435 4875677 := bbase (se 3 (by rfl) ⟨914189, by rfl⟩ : syracuseStep 4875677 = 1828379) (by norm_num)
theorem B3250451 : Blo 2165435 3250451 := bstep (se 1 (by rfl) ⟨2437838, by rfl⟩ : syracuseStep 3250451 = 4875677) B4875677
theorem B2166967 : Blo 2165435 2166967 := bstep (se 1 (by rfl) ⟨1625225, by rfl⟩ : syracuseStep 2166967 = 3250451) B3250451
theorem B3656765 : Blo 2165435 3656765 := bbase (se 3 (by rfl) ⟨685643, by rfl⟩ : syracuseStep 3656765 = 1371287) (by norm_num)
theorem B2437843 : Blo 2165435 2437843 := bstep (se 1 (by rfl) ⟨1828382, by rfl⟩ : syracuseStep 2437843 = 3656765) B3656765
theorem B3250457 : Blo 2165435 3250457 := bstep (se 2 (by rfl) ⟨1218921, by rfl⟩ : syracuseStep 3250457 = 2437843) B2437843
theorem B2166971 : Blo 2165435 2166971 := bstep (se 1 (by rfl) ⟨1625228, by rfl⟩ : syracuseStep 2166971 = 3250457) B3250457
theorem B3471077 : Blo 2165435 3471077 := bbase (se 4 (by rfl) ⟨325413, by rfl⟩ : syracuseStep 3471077 = 650827) (by norm_num)
theorem B2314051 : Blo 2165435 2314051 := bstep (se 1 (by rfl) ⟨1735538, by rfl⟩ : syracuseStep 2314051 = 3471077) B3471077
theorem B12341605 : Blo 2165435 12341605 := bstep (se 4 (by rfl) ⟨1157025, by rfl⟩ : syracuseStep 12341605 = 2314051) B2314051
theorem B16455473 : Blo 2165435 16455473 := bstep (se 2 (by rfl) ⟨6170802, by rfl⟩ : syracuseStep 16455473 = 12341605) B12341605
theorem B10970315 : Blo 2165435 10970315 := bstep (se 1 (by rfl) ⟨8227736, by rfl⟩ : syracuseStep 10970315 = 16455473) B16455473
theorem B7313543 : Blo 2165435 7313543 := bstep (se 1 (by rfl) ⟨5485157, by rfl⟩ : syracuseStep 7313543 = 10970315) B10970315
theorem B4875695 : Blo 2165435 4875695 := bstep (se 1 (by rfl) ⟨3656771, by rfl⟩ : syracuseStep 4875695 = 7313543) B7313543
theorem B3250463 : Blo 2165435 3250463 := bstep (se 1 (by rfl) ⟨2437847, by rfl⟩ : syracuseStep 3250463 = 4875695) B4875695
theorem B2166975 : Blo 2165435 2166975 := bstep (se 1 (by rfl) ⟨1625231, by rfl⟩ : syracuseStep 2166975 = 3250463) B3250463
theorem B3250469 : Blo 2165435 3250469 := bbase (se 4 (by rfl) ⟨304731, by rfl⟩ : syracuseStep 3250469 = 609463) (by norm_num)
theorem B2166979 : Blo 2165435 2166979 := bstep (se 1 (by rfl) ⟨1625234, by rfl⟩ : syracuseStep 2166979 = 3250469) B3250469
theorem B2742589 : Blo 2165435 2742589 := bbase (se 3 (by rfl) ⟨514235, by rfl⟩ : syracuseStep 2742589 = 1028471) (by norm_num)
theorem B3656785 : Blo 2165435 3656785 := bstep (se 2 (by rfl) ⟨1371294, by rfl⟩ : syracuseStep 3656785 = 2742589) B2742589
theorem B4875713 : Blo 2165435 4875713 := bstep (se 2 (by rfl) ⟨1828392, by rfl⟩ : syracuseStep 4875713 = 3656785) B3656785
theorem B3250475 : Blo 2165435 3250475 := bstep (se 1 (by rfl) ⟨2437856, by rfl⟩ : syracuseStep 3250475 = 4875713) B4875713
theorem B2166983 : Blo 2165435 2166983 := bstep (se 1 (by rfl) ⟨1625237, by rfl⟩ : syracuseStep 2166983 = 3250475) B3250475
theorem B2437861 : Blo 2165435 2437861 := bbase (se 4 (by rfl) ⟨228549, by rfl⟩ : syracuseStep 2437861 = 457099) (by norm_num)
theorem B3250481 : Blo 2165435 3250481 := bstep (se 2 (by rfl) ⟨1218930, by rfl⟩ : syracuseStep 3250481 = 2437861) B2437861
theorem B2166987 : Blo 2165435 2166987 := bstep (se 1 (by rfl) ⟨1625240, by rfl⟩ : syracuseStep 2166987 = 3250481) B3250481
theorem B14073845 : Blo 2165435 14073845 := bbase (se 5 (by rfl) ⟨659711, by rfl⟩ : syracuseStep 14073845 = 1319423) (by norm_num)
theorem B37530253 : Blo 2165435 37530253 := bstep (se 3 (by rfl) ⟨7036922, by rfl⟩ : syracuseStep 37530253 = 14073845) B14073845
theorem B50040337 : Blo 2165435 50040337 := bstep (se 2 (by rfl) ⟨18765126, by rfl⟩ : syracuseStep 50040337 = 37530253) B37530253
theorem B66720449 : Blo 2165435 66720449 := bstep (se 2 (by rfl) ⟨25020168, by rfl⟩ : syracuseStep 66720449 = 50040337) B50040337
theorem B44480299 : Blo 2165435 44480299 := bstep (se 1 (by rfl) ⟨33360224, by rfl⟩ : syracuseStep 44480299 = 66720449) B66720449
theorem B59307065 : Blo 2165435 59307065 := bstep (se 2 (by rfl) ⟨22240149, by rfl⟩ : syracuseStep 59307065 = 44480299) B44480299
theorem B39538043 : Blo 2165435 39538043 := bstep (se 1 (by rfl) ⟨29653532, by rfl⟩ : syracuseStep 39538043 = 59307065) B59307065
theorem B26358695 : Blo 2165435 26358695 := bstep (se 1 (by rfl) ⟨19769021, by rfl⟩ : syracuseStep 26358695 = 39538043) B39538043
theorem B17572463 : Blo 2165435 17572463 := bstep (se 1 (by rfl) ⟨13179347, by rfl⟩ : syracuseStep 17572463 = 26358695) B26358695
theorem B11714975 : Blo 2165435 11714975 := bstep (se 1 (by rfl) ⟨8786231, by rfl⟩ : syracuseStep 11714975 = 17572463) B17572463
theorem B7809983 : Blo 2165435 7809983 := bstep (se 1 (by rfl) ⟨5857487, by rfl⟩ : syracuseStep 7809983 = 11714975) B11714975
theorem B5206655 : Blo 2165435 5206655 := bstep (se 1 (by rfl) ⟨3904991, by rfl⟩ : syracuseStep 5206655 = 7809983) B7809983
theorem B3471103 : Blo 2165435 3471103 := bstep (se 1 (by rfl) ⟨2603327, by rfl⟩ : syracuseStep 3471103 = 5206655) B5206655
theorem B4628137 : Blo 2165435 4628137 := bstep (se 2 (by rfl) ⟨1735551, by rfl⟩ : syracuseStep 4628137 = 3471103) B3471103
theorem B6170849 : Blo 2165435 6170849 := bstep (se 2 (by rfl) ⟨2314068, by rfl⟩ : syracuseStep 6170849 = 4628137) B4628137
theorem B4113899 : Blo 2165435 4113899 := bstep (se 1 (by rfl) ⟨3085424, by rfl⟩ : syracuseStep 4113899 = 6170849) B6170849
theorem B2742599 : Blo 2165435 2742599 := bstep (se 1 (by rfl) ⟨2056949, by rfl⟩ : syracuseStep 2742599 = 4113899) B4113899
theorem B7313597 : Blo 2165435 7313597 := bstep (se 3 (by rfl) ⟨1371299, by rfl⟩ : syracuseStep 7313597 = 2742599) B2742599
theorem B4875731 : Blo 2165435 4875731 := bstep (se 1 (by rfl) ⟨3656798, by rfl⟩ : syracuseStep 4875731 = 7313597) B7313597
theorem B3250487 : Blo 2165435 3250487 := bstep (se 1 (by rfl) ⟨2437865, by rfl⟩ : syracuseStep 3250487 = 4875731) B4875731
theorem B2166991 : Blo 2165435 2166991 := bstep (se 1 (by rfl) ⟨1625243, by rfl⟩ : syracuseStep 2166991 = 3250487) B3250487
theorem B3250493 : Blo 2165435 3250493 := bbase (se 3 (by rfl) ⟨609467, by rfl⟩ : syracuseStep 3250493 = 1218935) (by norm_num)
theorem B2166995 : Blo 2165435 2166995 := bstep (se 1 (by rfl) ⟨1625246, by rfl⟩ : syracuseStep 2166995 = 3250493) B3250493
theorem B4875749 : Blo 2165435 4875749 := bbase (se 4 (by rfl) ⟨457101, by rfl⟩ : syracuseStep 4875749 = 914203) (by norm_num)
theorem B3250499 : Blo 2165435 3250499 := bstep (se 1 (by rfl) ⟨2437874, by rfl⟩ : syracuseStep 3250499 = 4875749) B4875749
theorem B2166999 : Blo 2165435 2166999 := bstep (se 1 (by rfl) ⟨1625249, by rfl⟩ : syracuseStep 2166999 = 3250499) B3250499
theorem B5485229 : Blo 2165435 5485229 := bbase (se 3 (by rfl) ⟨1028480, by rfl⟩ : syracuseStep 5485229 = 2056961) (by norm_num)
theorem B3656819 : Blo 2165435 3656819 := bstep (se 1 (by rfl) ⟨2742614, by rfl⟩ : syracuseStep 3656819 = 5485229) B5485229
theorem B2437879 : Blo 2165435 2437879 := bstep (se 1 (by rfl) ⟨1828409, by rfl⟩ : syracuseStep 2437879 = 3656819) B3656819
theorem B3250505 : Blo 2165435 3250505 := bstep (se 2 (by rfl) ⟨1218939, by rfl⟩ : syracuseStep 3250505 = 2437879) B2437879
theorem B2167003 : Blo 2165435 2167003 := bstep (se 1 (by rfl) ⟨1625252, by rfl⟩ : syracuseStep 2167003 = 3250505) B3250505
theorem B5206693 : Blo 2165435 5206693 := bbase (se 4 (by rfl) ⟨488127, by rfl⟩ : syracuseStep 5206693 = 976255) (by norm_num)
theorem B6942257 : Blo 2165435 6942257 := bstep (se 2 (by rfl) ⟨2603346, by rfl⟩ : syracuseStep 6942257 = 5206693) B5206693
theorem B4628171 : Blo 2165435 4628171 := bstep (se 1 (by rfl) ⟨3471128, by rfl⟩ : syracuseStep 4628171 = 6942257) B6942257
theorem B3085447 : Blo 2165435 3085447 := bstep (se 1 (by rfl) ⟨2314085, by rfl⟩ : syracuseStep 3085447 = 4628171) B4628171
theorem B4113929 : Blo 2165435 4113929 := bstep (se 2 (by rfl) ⟨1542723, by rfl⟩ : syracuseStep 4113929 = 3085447) B3085447
theorem B10970477 : Blo 2165435 10970477 := bstep (se 3 (by rfl) ⟨2056964, by rfl⟩ : syracuseStep 10970477 = 4113929) B4113929
theorem B7313651 : Blo 2165435 7313651 := bstep (se 1 (by rfl) ⟨5485238, by rfl⟩ : syracuseStep 7313651 = 10970477) B10970477
theorem B4875767 : Blo 2165435 4875767 := bstep (se 1 (by rfl) ⟨3656825, by rfl⟩ : syracuseStep 4875767 = 7313651) B7313651
theorem B3250511 : Blo 2165435 3250511 := bstep (se 1 (by rfl) ⟨2437883, by rfl⟩ : syracuseStep 3250511 = 4875767) B4875767
theorem B2167007 : Blo 2165435 2167007 := bstep (se 1 (by rfl) ⟨1625255, by rfl⟩ : syracuseStep 2167007 = 3250511) B3250511
theorem B3250517 : Blo 2165435 3250517 := bbase (se 10 (by rfl) ⟨4761, by rfl⟩ : syracuseStep 3250517 = 9523) (by norm_num)
theorem B2167011 : Blo 2165435 2167011 := bstep (se 1 (by rfl) ⟨1625258, by rfl⟩ : syracuseStep 2167011 = 3250517) B3250517
theorem B6170917 : Blo 2165435 6170917 := bbase (se 4 (by rfl) ⟨578523, by rfl⟩ : syracuseStep 6170917 = 1157047) (by norm_num)
theorem B8227889 : Blo 2165435 8227889 := bstep (se 2 (by rfl) ⟨3085458, by rfl⟩ : syracuseStep 8227889 = 6170917) B6170917
theorem B5485259 : Blo 2165435 5485259 := bstep (se 1 (by rfl) ⟨4113944, by rfl⟩ : syracuseStep 5485259 = 8227889) B8227889
theorem B3656839 : Blo 2165435 3656839 := bstep (se 1 (by rfl) ⟨2742629, by rfl⟩ : syracuseStep 3656839 = 5485259) B5485259
theorem B4875785 : Blo 2165435 4875785 := bstep (se 2 (by rfl) ⟨1828419, by rfl⟩ : syracuseStep 4875785 = 3656839) B3656839
theorem B3250523 : Blo 2165435 3250523 := bstep (se 1 (by rfl) ⟨2437892, by rfl⟩ : syracuseStep 3250523 = 4875785) B4875785
theorem B2167015 : Blo 2165435 2167015 := bstep (se 1 (by rfl) ⟨1625261, by rfl⟩ : syracuseStep 2167015 = 3250523) B3250523
theorem B2437897 : Blo 2165435 2437897 := bbase (se 2 (by rfl) ⟨914211, by rfl⟩ : syracuseStep 2437897 = 1828423) (by norm_num)
theorem B3250529 : Blo 2165435 3250529 := bstep (se 2 (by rfl) ⟨1218948, by rfl⟩ : syracuseStep 3250529 = 2437897) B2437897
theorem B2167019 : Blo 2165435 2167019 := bstep (se 1 (by rfl) ⟨1625264, by rfl⟩ : syracuseStep 2167019 = 3250529) B3250529
theorem B10413461 : Blo 2165435 10413461 := bbase (se 6 (by rfl) ⟨244065, by rfl⟩ : syracuseStep 10413461 = 488131) (by norm_num)
theorem B27769229 : Blo 2165435 27769229 := bstep (se 3 (by rfl) ⟨5206730, by rfl⟩ : syracuseStep 27769229 = 10413461) B10413461
theorem B18512819 : Blo 2165435 18512819 := bstep (se 1 (by rfl) ⟨13884614, by rfl⟩ : syracuseStep 18512819 = 27769229) B27769229
theorem B12341879 : Blo 2165435 12341879 := bstep (se 1 (by rfl) ⟨9256409, by rfl⟩ : syracuseStep 12341879 = 18512819) B18512819
theorem B8227919 : Blo 2165435 8227919 := bstep (se 1 (by rfl) ⟨6170939, by rfl⟩ : syracuseStep 8227919 = 12341879) B12341879
theorem B5485279 : Blo 2165435 5485279 := bstep (se 1 (by rfl) ⟨4113959, by rfl⟩ : syracuseStep 5485279 = 8227919) B8227919
theorem B7313705 : Blo 2165435 7313705 := bstep (se 2 (by rfl) ⟨2742639, by rfl⟩ : syracuseStep 7313705 = 5485279) B5485279
theorem B4875803 : Blo 2165435 4875803 := bstep (se 1 (by rfl) ⟨3656852, by rfl⟩ : syracuseStep 4875803 = 7313705) B7313705
theorem B3250535 : Blo 2165435 3250535 := bstep (se 1 (by rfl) ⟨2437901, by rfl⟩ : syracuseStep 3250535 = 4875803) B4875803
theorem B2167023 : Blo 2165435 2167023 := bstep (se 1 (by rfl) ⟨1625267, by rfl⟩ : syracuseStep 2167023 = 3250535) B3250535
theorem B3250541 : Blo 2165435 3250541 := bbase (se 3 (by rfl) ⟨609476, by rfl⟩ : syracuseStep 3250541 = 1218953) (by norm_num)
theorem B2167027 : Blo 2165435 2167027 := bstep (se 1 (by rfl) ⟨1625270, by rfl⟩ : syracuseStep 2167027 = 3250541) B3250541
theorem B4875821 : Blo 2165435 4875821 := bbase (se 3 (by rfl) ⟨914216, by rfl⟩ : syracuseStep 4875821 = 1828433) (by norm_num)
theorem B3250547 : Blo 2165435 3250547 := bstep (se 1 (by rfl) ⟨2437910, by rfl⟩ : syracuseStep 3250547 = 4875821) B4875821
theorem B2167031 : Blo 2165435 2167031 := bstep (se 1 (by rfl) ⟨1625273, by rfl⟩ : syracuseStep 2167031 = 3250547) B3250547
theorem B4393205 : Blo 2165435 4393205 := bbase (se 5 (by rfl) ⟨205931, by rfl⟩ : syracuseStep 4393205 = 411863) (by norm_num)
theorem B2928803 : Blo 2165435 2928803 := bstep (se 1 (by rfl) ⟨2196602, by rfl⟩ : syracuseStep 2928803 = 4393205) B4393205
theorem B31240565 : Blo 2165435 31240565 := bstep (se 5 (by rfl) ⟨1464401, by rfl⟩ : syracuseStep 31240565 = 2928803) B2928803
theorem B20827043 : Blo 2165435 20827043 := bstep (se 1 (by rfl) ⟨15620282, by rfl⟩ : syracuseStep 20827043 = 31240565) B31240565
theorem B13884695 : Blo 2165435 13884695 := bstep (se 1 (by rfl) ⟨10413521, by rfl⟩ : syracuseStep 13884695 = 20827043) B20827043
theorem B9256463 : Blo 2165435 9256463 := bstep (se 1 (by rfl) ⟨6942347, by rfl⟩ : syracuseStep 9256463 = 13884695) B13884695
theorem B6170975 : Blo 2165435 6170975 := bstep (se 1 (by rfl) ⟨4628231, by rfl⟩ : syracuseStep 6170975 = 9256463) B9256463
theorem B4113983 : Blo 2165435 4113983 := bstep (se 1 (by rfl) ⟨3085487, by rfl⟩ : syracuseStep 4113983 = 6170975) B6170975
theorem B2742655 : Blo 2165435 2742655 := bstep (se 1 (by rfl) ⟨2056991, by rfl⟩ : syracuseStep 2742655 = 4113983) B4113983
theorem B3656873 : Blo 2165435 3656873 := bstep (se 2 (by rfl) ⟨1371327, by rfl⟩ : syracuseStep 3656873 = 2742655) B2742655
theorem B2437915 : Blo 2165435 2437915 := bstep (se 1 (by rfl) ⟨1828436, by rfl⟩ : syracuseStep 2437915 = 3656873) B3656873
theorem B3250553 : Blo 2165435 3250553 := bstep (se 2 (by rfl) ⟨1218957, by rfl⟩ : syracuseStep 3250553 = 2437915) B2437915
theorem B2167035 : Blo 2165435 2167035 := bstep (se 1 (by rfl) ⟨1625276, by rfl⟩ : syracuseStep 2167035 = 3250553) B3250553
theorem B3905077 : Blo 2165435 3905077 := bbase (se 5 (by rfl) ⟨183050, by rfl⟩ : syracuseStep 3905077 = 366101) (by norm_num)
theorem B5206769 : Blo 2165435 5206769 := bstep (se 2 (by rfl) ⟨1952538, by rfl⟩ : syracuseStep 5206769 = 3905077) B3905077
theorem B3471179 : Blo 2165435 3471179 := bstep (se 1 (by rfl) ⟨2603384, by rfl⟩ : syracuseStep 3471179 = 5206769) B5206769
theorem B37025909 : Blo 2165435 37025909 := bstep (se 5 (by rfl) ⟨1735589, by rfl⟩ : syracuseStep 37025909 = 3471179) B3471179
theorem B24683939 : Blo 2165435 24683939 := bstep (se 1 (by rfl) ⟨18512954, by rfl⟩ : syracuseStep 24683939 = 37025909) B37025909
theorem B16455959 : Blo 2165435 16455959 := bstep (se 1 (by rfl) ⟨12341969, by rfl⟩ : syracuseStep 16455959 = 24683939) B24683939
theorem B10970639 : Blo 2165435 10970639 := bstep (se 1 (by rfl) ⟨8227979, by rfl⟩ : syracuseStep 10970639 = 16455959) B16455959
theorem B7313759 : Blo 2165435 7313759 := bstep (se 1 (by rfl) ⟨5485319, by rfl⟩ : syracuseStep 7313759 = 10970639) B10970639
theorem B4875839 : Blo 2165435 4875839 := bstep (se 1 (by rfl) ⟨3656879, by rfl⟩ : syracuseStep 4875839 = 7313759) B7313759
theorem B3250559 : Blo 2165435 3250559 := bstep (se 1 (by rfl) ⟨2437919, by rfl⟩ : syracuseStep 3250559 = 4875839) B4875839
theorem B2167039 : Blo 2165435 2167039 := bstep (se 1 (by rfl) ⟨1625279, by rfl⟩ : syracuseStep 2167039 = 3250559) B3250559
theorem B3250565 : Blo 2165435 3250565 := bbase (se 4 (by rfl) ⟨304740, by rfl⟩ : syracuseStep 3250565 = 609481) (by norm_num)
theorem B2167043 : Blo 2165435 2167043 := bstep (se 1 (by rfl) ⟨1625282, by rfl⟩ : syracuseStep 2167043 = 3250565) B3250565
theorem B3656893 : Blo 2165435 3656893 := bbase (se 3 (by rfl) ⟨685667, by rfl⟩ : syracuseStep 3656893 = 1371335) (by norm_num)
theorem B4875857 : Blo 2165435 4875857 := bstep (se 2 (by rfl) ⟨1828446, by rfl⟩ : syracuseStep 4875857 = 3656893) B3656893
theorem B3250571 : Blo 2165435 3250571 := bstep (se 1 (by rfl) ⟨2437928, by rfl⟩ : syracuseStep 3250571 = 4875857) B4875857
theorem B2167047 : Blo 2165435 2167047 := bstep (se 1 (by rfl) ⟨1625285, by rfl⟩ : syracuseStep 2167047 = 3250571) B3250571
theorem B2437933 : Blo 2165435 2437933 := bbase (se 3 (by rfl) ⟨457112, by rfl⟩ : syracuseStep 2437933 = 914225) (by norm_num)
theorem B3250577 : Blo 2165435 3250577 := bstep (se 2 (by rfl) ⟨1218966, by rfl⟩ : syracuseStep 3250577 = 2437933) B2437933
theorem B2167051 : Blo 2165435 2167051 := bstep (se 1 (by rfl) ⟨1625288, by rfl⟩ : syracuseStep 2167051 = 3250577) B3250577
theorem B7313813 : Blo 2165435 7313813 := bbase (se 6 (by rfl) ⟨171417, by rfl⟩ : syracuseStep 7313813 = 342835) (by norm_num)
theorem B4875875 : Blo 2165435 4875875 := bstep (se 1 (by rfl) ⟨3656906, by rfl⟩ : syracuseStep 4875875 = 7313813) B7313813
theorem B3250583 : Blo 2165435 3250583 := bstep (se 1 (by rfl) ⟨2437937, by rfl⟩ : syracuseStep 3250583 = 4875875) B4875875
theorem B2167055 : Blo 2165435 2167055 := bstep (se 1 (by rfl) ⟨1625291, by rfl⟩ : syracuseStep 2167055 = 3250583) B3250583
theorem B3250589 : Blo 2165435 3250589 := bbase (se 3 (by rfl) ⟨609485, by rfl⟩ : syracuseStep 3250589 = 1218971) (by norm_num)
theorem B2167059 : Blo 2165435 2167059 := bstep (se 1 (by rfl) ⟨1625294, by rfl⟩ : syracuseStep 2167059 = 3250589) B3250589
theorem B4875893 : Blo 2165435 4875893 := bbase (se 5 (by rfl) ⟨228557, by rfl⟩ : syracuseStep 4875893 = 457115) (by norm_num)
theorem B3250595 : Blo 2165435 3250595 := bstep (se 1 (by rfl) ⟨2437946, by rfl⟩ : syracuseStep 3250595 = 4875893) B4875893
theorem B2167063 : Blo 2165435 2167063 := bstep (se 1 (by rfl) ⟨1625297, by rfl⟩ : syracuseStep 2167063 = 3250595) B3250595
theorem B5206837 : Blo 2165435 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B6942449 : Blo 2165435 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B18513197 : Blo 2165435 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B12342131 : Blo 2165435 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B8228087 : Blo 2165435 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B5485391 : Blo 2165435 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B3656927 : Blo 2165435 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B2437951 : Blo 2165435 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B3250601 : Blo 2165435 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B2167067 : Blo 2165435 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B8228101 : Blo 2165435 8228101 := bbase (se 4 (by rfl) ⟨771384, by rfl⟩ : syracuseStep 8228101 = 1542769) (by norm_num)
theorem B10970801 : Blo 2165435 10970801 := bstep (se 2 (by rfl) ⟨4114050, by rfl⟩ : syracuseStep 10970801 = 8228101) B8228101
theorem B7313867 : Blo 2165435 7313867 := bstep (se 1 (by rfl) ⟨5485400, by rfl⟩ : syracuseStep 7313867 = 10970801) B10970801
theorem B4875911 : Blo 2165435 4875911 := bstep (se 1 (by rfl) ⟨3656933, by rfl⟩ : syracuseStep 4875911 = 7313867) B7313867
theorem B3250607 : Blo 2165435 3250607 := bstep (se 1 (by rfl) ⟨2437955, by rfl⟩ : syracuseStep 3250607 = 4875911) B4875911
theorem B2167071 : Blo 2165435 2167071 := bstep (se 1 (by rfl) ⟨1625303, by rfl⟩ : syracuseStep 2167071 = 3250607) B3250607
theorem B3250613 : Blo 2165435 3250613 := bbase (se 5 (by rfl) ⟨152372, by rfl⟩ : syracuseStep 3250613 = 304745) (by norm_num)
theorem B2167075 : Blo 2165435 2167075 := bstep (se 1 (by rfl) ⟨1625306, by rfl⟩ : syracuseStep 2167075 = 3250613) B3250613
theorem B5485421 : Blo 2165435 5485421 := bbase (se 3 (by rfl) ⟨1028516, by rfl⟩ : syracuseStep 5485421 = 2057033) (by norm_num)
theorem B3656947 : Blo 2165435 3656947 := bstep (se 1 (by rfl) ⟨2742710, by rfl⟩ : syracuseStep 3656947 = 5485421) B5485421
theorem B4875929 : Blo 2165435 4875929 := bstep (se 2 (by rfl) ⟨1828473, by rfl⟩ : syracuseStep 4875929 = 3656947) B3656947
theorem B3250619 : Blo 2165435 3250619 := bstep (se 1 (by rfl) ⟨2437964, by rfl⟩ : syracuseStep 3250619 = 4875929) B4875929
theorem B2167079 : Blo 2165435 2167079 := bstep (se 1 (by rfl) ⟨1625309, by rfl⟩ : syracuseStep 2167079 = 3250619) B3250619
theorem B2437969 : Blo 2165435 2437969 := bbase (se 2 (by rfl) ⟨914238, by rfl⟩ : syracuseStep 2437969 = 1828477) (by norm_num)
theorem B3250625 : Blo 2165435 3250625 := bstep (se 2 (by rfl) ⟨1218984, by rfl⟩ : syracuseStep 3250625 = 2437969) B2437969
theorem B2167083 : Blo 2165435 2167083 := bstep (se 1 (by rfl) ⟨1625312, by rfl⟩ : syracuseStep 2167083 = 3250625) B3250625
theorem B3905165 : Blo 2165435 3905165 := bbase (se 3 (by rfl) ⟨732218, by rfl⟩ : syracuseStep 3905165 = 1464437) (by norm_num)
theorem B2603443 : Blo 2165435 2603443 := bstep (se 1 (by rfl) ⟨1952582, by rfl⟩ : syracuseStep 2603443 = 3905165) B3905165
theorem B3471257 : Blo 2165435 3471257 := bstep (se 2 (by rfl) ⟨1301721, by rfl⟩ : syracuseStep 3471257 = 2603443) B2603443
theorem B2314171 : Blo 2165435 2314171 := bstep (se 1 (by rfl) ⟨1735628, by rfl⟩ : syracuseStep 2314171 = 3471257) B3471257
theorem B3085561 : Blo 2165435 3085561 := bstep (se 2 (by rfl) ⟨1157085, by rfl⟩ : syracuseStep 3085561 = 2314171) B2314171
theorem B4114081 : Blo 2165435 4114081 := bstep (se 2 (by rfl) ⟨1542780, by rfl⟩ : syracuseStep 4114081 = 3085561) B3085561
theorem B5485441 : Blo 2165435 5485441 := bstep (se 2 (by rfl) ⟨2057040, by rfl⟩ : syracuseStep 5485441 = 4114081) B4114081
theorem B7313921 : Blo 2165435 7313921 := bstep (se 2 (by rfl) ⟨2742720, by rfl⟩ : syracuseStep 7313921 = 5485441) B5485441
theorem B4875947 : Blo 2165435 4875947 := bstep (se 1 (by rfl) ⟨3656960, by rfl⟩ : syracuseStep 4875947 = 7313921) B7313921
theorem B3250631 : Blo 2165435 3250631 := bstep (se 1 (by rfl) ⟨2437973, by rfl⟩ : syracuseStep 3250631 = 4875947) B4875947
theorem B2167087 : Blo 2165435 2167087 := bstep (se 1 (by rfl) ⟨1625315, by rfl⟩ : syracuseStep 2167087 = 3250631) B3250631
theorem B3250637 : Blo 2165435 3250637 := bbase (se 3 (by rfl) ⟨609494, by rfl⟩ : syracuseStep 3250637 = 1218989) (by norm_num)
theorem B2167091 : Blo 2165435 2167091 := bstep (se 1 (by rfl) ⟨1625318, by rfl⟩ : syracuseStep 2167091 = 3250637) B3250637
theorem B4875965 : Blo 2165435 4875965 := bbase (se 3 (by rfl) ⟨914243, by rfl⟩ : syracuseStep 4875965 = 1828487) (by norm_num)
theorem B3250643 : Blo 2165435 3250643 := bstep (se 1 (by rfl) ⟨2437982, by rfl⟩ : syracuseStep 3250643 = 4875965) B4875965
theorem B2167095 : Blo 2165435 2167095 := bstep (se 1 (by rfl) ⟨1625321, by rfl⟩ : syracuseStep 2167095 = 3250643) B3250643
theorem B3656981 : Blo 2165435 3656981 := bbase (se 6 (by rfl) ⟨85710, by rfl⟩ : syracuseStep 3656981 = 171421) (by norm_num)
theorem B2437987 : Blo 2165435 2437987 := bstep (se 1 (by rfl) ⟨1828490, by rfl⟩ : syracuseStep 2437987 = 3656981) B3656981
theorem B3250649 : Blo 2165435 3250649 := bstep (se 2 (by rfl) ⟨1218993, by rfl⟩ : syracuseStep 3250649 = 2437987) B2437987
theorem B2167099 : Blo 2165435 2167099 := bstep (se 1 (by rfl) ⟨1625324, by rfl⟩ : syracuseStep 2167099 = 3250649) B3250649
theorem B17573365 : Blo 2165435 17573365 := bbase (se 5 (by rfl) ⟨823751, by rfl⟩ : syracuseStep 17573365 = 1647503) (by norm_num)
theorem B23431153 : Blo 2165435 23431153 := bstep (se 2 (by rfl) ⟨8786682, by rfl⟩ : syracuseStep 23431153 = 17573365) B17573365
theorem B31241537 : Blo 2165435 31241537 := bstep (se 2 (by rfl) ⟨11715576, by rfl⟩ : syracuseStep 31241537 = 23431153) B23431153
theorem B20827691 : Blo 2165435 20827691 := bstep (se 1 (by rfl) ⟨15620768, by rfl⟩ : syracuseStep 20827691 = 31241537) B31241537
theorem B13885127 : Blo 2165435 13885127 := bstep (se 1 (by rfl) ⟨10413845, by rfl⟩ : syracuseStep 13885127 = 20827691) B20827691
theorem B9256751 : Blo 2165435 9256751 := bstep (se 1 (by rfl) ⟨6942563, by rfl⟩ : syracuseStep 9256751 = 13885127) B13885127
theorem B6171167 : Blo 2165435 6171167 := bstep (se 1 (by rfl) ⟨4628375, by rfl⟩ : syracuseStep 6171167 = 9256751) B9256751
theorem B16456445 : Blo 2165435 16456445 := bstep (se 3 (by rfl) ⟨3085583, by rfl⟩ : syracuseStep 16456445 = 6171167) B6171167
theorem B10970963 : Blo 2165435 10970963 := bstep (se 1 (by rfl) ⟨8228222, by rfl⟩ : syracuseStep 10970963 = 16456445) B16456445
theorem B7313975 : Blo 2165435 7313975 := bstep (se 1 (by rfl) ⟨5485481, by rfl⟩ : syracuseStep 7313975 = 10970963) B10970963
theorem B4875983 : Blo 2165435 4875983 := bstep (se 1 (by rfl) ⟨3656987, by rfl⟩ : syracuseStep 4875983 = 7313975) B7313975
theorem B3250655 : Blo 2165435 3250655 := bstep (se 1 (by rfl) ⟨2437991, by rfl⟩ : syracuseStep 3250655 = 4875983) B4875983
theorem B2167103 : Blo 2165435 2167103 := bstep (se 1 (by rfl) ⟨1625327, by rfl⟩ : syracuseStep 2167103 = 3250655) B3250655
theorem B3250661 : Blo 2165435 3250661 := bbase (se 4 (by rfl) ⟨304749, by rfl⟩ : syracuseStep 3250661 = 609499) (by norm_num)
theorem B2167107 : Blo 2165435 2167107 := bstep (se 1 (by rfl) ⟨1625330, by rfl⟩ : syracuseStep 2167107 = 3250661) B3250661
theorem B2638993 : Blo 2165435 2638993 := bbase (se 2 (by rfl) ⟨989622, by rfl⟩ : syracuseStep 2638993 = 1979245) (by norm_num)
theorem B3518657 : Blo 2165435 3518657 := bstep (se 2 (by rfl) ⟨1319496, by rfl⟩ : syracuseStep 3518657 = 2638993) B2638993
theorem B2345771 : Blo 2165435 2345771 := bstep (se 1 (by rfl) ⟨1759328, by rfl⟩ : syracuseStep 2345771 = 3518657) B3518657
theorem B6255389 : Blo 2165435 6255389 := bstep (se 3 (by rfl) ⟨1172885, by rfl⟩ : syracuseStep 6255389 = 2345771) B2345771
theorem B4170259 : Blo 2165435 4170259 := bstep (se 1 (by rfl) ⟨3127694, by rfl⟩ : syracuseStep 4170259 = 6255389) B6255389
theorem B5560345 : Blo 2165435 5560345 := bstep (se 2 (by rfl) ⟨2085129, by rfl⟩ : syracuseStep 5560345 = 4170259) B4170259
theorem B29655173 : Blo 2165435 29655173 := bstep (se 4 (by rfl) ⟨2780172, by rfl⟩ : syracuseStep 29655173 = 5560345) B5560345
theorem B19770115 : Blo 2165435 19770115 := bstep (se 1 (by rfl) ⟨14827586, by rfl⟩ : syracuseStep 19770115 = 29655173) B29655173
theorem B26360153 : Blo 2165435 26360153 := bstep (se 2 (by rfl) ⟨9885057, by rfl⟩ : syracuseStep 26360153 = 19770115) B19770115
theorem B17573435 : Blo 2165435 17573435 := bstep (se 1 (by rfl) ⟨13180076, by rfl⟩ : syracuseStep 17573435 = 26360153) B26360153
theorem B11715623 : Blo 2165435 11715623 := bstep (se 1 (by rfl) ⟨8786717, by rfl⟩ : syracuseStep 11715623 = 17573435) B17573435
theorem B7810415 : Blo 2165435 7810415 := bstep (se 1 (by rfl) ⟨5857811, by rfl⟩ : syracuseStep 7810415 = 11715623) B11715623
theorem B5206943 : Blo 2165435 5206943 := bstep (se 1 (by rfl) ⟨3905207, by rfl⟩ : syracuseStep 5206943 = 7810415) B7810415
theorem B13885181 : Blo 2165435 13885181 := bstep (se 3 (by rfl) ⟨2603471, by rfl⟩ : syracuseStep 13885181 = 5206943) B5206943
theorem B9256787 : Blo 2165435 9256787 := bstep (se 1 (by rfl) ⟨6942590, by rfl⟩ : syracuseStep 9256787 = 13885181) B13885181
theorem B6171191 : Blo 2165435 6171191 := bstep (se 1 (by rfl) ⟨4628393, by rfl⟩ : syracuseStep 6171191 = 9256787) B9256787
theorem B4114127 : Blo 2165435 4114127 := bstep (se 1 (by rfl) ⟨3085595, by rfl⟩ : syracuseStep 4114127 = 6171191) B6171191
theorem B2742751 : Blo 2165435 2742751 := bstep (se 1 (by rfl) ⟨2057063, by rfl⟩ : syracuseStep 2742751 = 4114127) B4114127
theorem B3657001 : Blo 2165435 3657001 := bstep (se 2 (by rfl) ⟨1371375, by rfl⟩ : syracuseStep 3657001 = 2742751) B2742751
theorem B4876001 : Blo 2165435 4876001 := bstep (se 2 (by rfl) ⟨1828500, by rfl⟩ : syracuseStep 4876001 = 3657001) B3657001
theorem B3250667 : Blo 2165435 3250667 := bstep (se 1 (by rfl) ⟨2438000, by rfl⟩ : syracuseStep 3250667 = 4876001) B4876001
theorem B2167111 : Blo 2165435 2167111 := bstep (se 1 (by rfl) ⟨1625333, by rfl⟩ : syracuseStep 2167111 = 3250667) B3250667
theorem B2438005 : Blo 2165435 2438005 := bbase (se 5 (by rfl) ⟨114281, by rfl⟩ : syracuseStep 2438005 = 228563) (by norm_num)
theorem B3250673 : Blo 2165435 3250673 := bstep (se 2 (by rfl) ⟨1219002, by rfl⟩ : syracuseStep 3250673 = 2438005) B2438005
theorem B2167115 : Blo 2165435 2167115 := bstep (se 1 (by rfl) ⟨1625336, by rfl⟩ : syracuseStep 2167115 = 3250673) B3250673
theorem B2742761 : Blo 2165435 2742761 := bbase (se 2 (by rfl) ⟨1028535, by rfl⟩ : syracuseStep 2742761 = 2057071) (by norm_num)
theorem B7314029 : Blo 2165435 7314029 := bstep (se 3 (by rfl) ⟨1371380, by rfl⟩ : syracuseStep 7314029 = 2742761) B2742761
theorem B4876019 : Blo 2165435 4876019 := bstep (se 1 (by rfl) ⟨3657014, by rfl⟩ : syracuseStep 4876019 = 7314029) B7314029
theorem B3250679 : Blo 2165435 3250679 := bstep (se 1 (by rfl) ⟨2438009, by rfl⟩ : syracuseStep 3250679 = 4876019) B4876019
theorem B2167119 : Blo 2165435 2167119 := bstep (se 1 (by rfl) ⟨1625339, by rfl⟩ : syracuseStep 2167119 = 3250679) B3250679
theorem B3250685 : Blo 2165435 3250685 := bbase (se 3 (by rfl) ⟨609503, by rfl⟩ : syracuseStep 3250685 = 1219007) (by norm_num)
theorem B2167123 : Blo 2165435 2167123 := bstep (se 1 (by rfl) ⟨1625342, by rfl⟩ : syracuseStep 2167123 = 3250685) B3250685
theorem B4876037 : Blo 2165435 4876037 := bbase (se 4 (by rfl) ⟨457128, by rfl⟩ : syracuseStep 4876037 = 914257) (by norm_num)
theorem B3250691 : Blo 2165435 3250691 := bstep (se 1 (by rfl) ⟨2438018, by rfl⟩ : syracuseStep 3250691 = 4876037) B4876037
theorem B2167127 : Blo 2165435 2167127 := bstep (se 1 (by rfl) ⟨1625345, by rfl⟩ : syracuseStep 2167127 = 3250691) B3250691
theorem B4114165 : Blo 2165435 4114165 := bbase (se 5 (by rfl) ⟨192851, by rfl⟩ : syracuseStep 4114165 = 385703) (by norm_num)
theorem B5485553 : Blo 2165435 5485553 := bstep (se 2 (by rfl) ⟨2057082, by rfl⟩ : syracuseStep 5485553 = 4114165) B4114165
theorem B3657035 : Blo 2165435 3657035 := bstep (se 1 (by rfl) ⟨2742776, by rfl⟩ : syracuseStep 3657035 = 5485553) B5485553
theorem B2438023 : Blo 2165435 2438023 := bstep (se 1 (by rfl) ⟨1828517, by rfl⟩ : syracuseStep 2438023 = 3657035) B3657035
theorem B3250697 : Blo 2165435 3250697 := bstep (se 2 (by rfl) ⟨1219011, by rfl⟩ : syracuseStep 3250697 = 2438023) B2438023
theorem B2167131 : Blo 2165435 2167131 := bstep (se 1 (by rfl) ⟨1625348, by rfl⟩ : syracuseStep 2167131 = 3250697) B3250697
theorem B10971125 : Blo 2165435 10971125 := bbase (se 5 (by rfl) ⟨514271, by rfl⟩ : syracuseStep 10971125 = 1028543) (by norm_num)
theorem B7314083 : Blo 2165435 7314083 := bstep (se 1 (by rfl) ⟨5485562, by rfl⟩ : syracuseStep 7314083 = 10971125) B10971125
theorem B4876055 : Blo 2165435 4876055 := bstep (se 1 (by rfl) ⟨3657041, by rfl⟩ : syracuseStep 4876055 = 7314083) B7314083
theorem B3250703 : Blo 2165435 3250703 := bstep (se 1 (by rfl) ⟨2438027, by rfl⟩ : syracuseStep 3250703 = 4876055) B4876055
theorem B2167135 : Blo 2165435 2167135 := bstep (se 1 (by rfl) ⟨1625351, by rfl⟩ : syracuseStep 2167135 = 3250703) B3250703
theorem B3250709 : Blo 2165435 3250709 := bbase (se 6 (by rfl) ⟨76188, by rfl⟩ : syracuseStep 3250709 = 152377) (by norm_num)
theorem B2167139 : Blo 2165435 2167139 := bstep (se 1 (by rfl) ⟨1625354, by rfl⟩ : syracuseStep 2167139 = 3250709) B3250709
theorem B18513845 : Blo 2165435 18513845 := bbase (se 5 (by rfl) ⟨867836, by rfl⟩ : syracuseStep 18513845 = 1735673) (by norm_num)
theorem B12342563 : Blo 2165435 12342563 := bstep (se 1 (by rfl) ⟨9256922, by rfl⟩ : syracuseStep 12342563 = 18513845) B18513845
theorem B8228375 : Blo 2165435 8228375 := bstep (se 1 (by rfl) ⟨6171281, by rfl⟩ : syracuseStep 8228375 = 12342563) B12342563
theorem B5485583 : Blo 2165435 5485583 := bstep (se 1 (by rfl) ⟨4114187, by rfl⟩ : syracuseStep 5485583 = 8228375) B8228375
theorem B3657055 : Blo 2165435 3657055 := bstep (se 1 (by rfl) ⟨2742791, by rfl⟩ : syracuseStep 3657055 = 5485583) B5485583
theorem B4876073 : Blo 2165435 4876073 := bstep (se 2 (by rfl) ⟨1828527, by rfl⟩ : syracuseStep 4876073 = 3657055) B3657055
theorem B3250715 : Blo 2165435 3250715 := bstep (se 1 (by rfl) ⟨2438036, by rfl⟩ : syracuseStep 3250715 = 4876073) B4876073
theorem B2167143 : Blo 2165435 2167143 := bstep (se 1 (by rfl) ⟨1625357, by rfl⟩ : syracuseStep 2167143 = 3250715) B3250715
theorem B2438041 : Blo 2165435 2438041 := bbase (se 2 (by rfl) ⟨914265, by rfl⟩ : syracuseStep 2438041 = 1828531) (by norm_num)
theorem B3250721 : Blo 2165435 3250721 := bstep (se 2 (by rfl) ⟨1219020, by rfl⟩ : syracuseStep 3250721 = 2438041) B2438041
theorem B2167147 : Blo 2165435 2167147 := bstep (se 1 (by rfl) ⟨1625360, by rfl⟩ : syracuseStep 2167147 = 3250721) B3250721
theorem B8228405 : Blo 2165435 8228405 := bbase (se 5 (by rfl) ⟨385706, by rfl⟩ : syracuseStep 8228405 = 771413) (by norm_num)
theorem B5485603 : Blo 2165435 5485603 := bstep (se 1 (by rfl) ⟨4114202, by rfl⟩ : syracuseStep 5485603 = 8228405) B8228405
theorem B7314137 : Blo 2165435 7314137 := bstep (se 2 (by rfl) ⟨2742801, by rfl⟩ : syracuseStep 7314137 = 5485603) B5485603
theorem B4876091 : Blo 2165435 4876091 := bstep (se 1 (by rfl) ⟨3657068, by rfl⟩ : syracuseStep 4876091 = 7314137) B7314137
theorem B3250727 : Blo 2165435 3250727 := bstep (se 1 (by rfl) ⟨2438045, by rfl⟩ : syracuseStep 3250727 = 4876091) B4876091
theorem B2167151 : Blo 2165435 2167151 := bstep (se 1 (by rfl) ⟨1625363, by rfl⟩ : syracuseStep 2167151 = 3250727) B3250727
theorem B3250733 : Blo 2165435 3250733 := bbase (se 3 (by rfl) ⟨609512, by rfl⟩ : syracuseStep 3250733 = 1219025) (by norm_num)
theorem B2167155 : Blo 2165435 2167155 := bstep (se 1 (by rfl) ⟨1625366, by rfl⟩ : syracuseStep 2167155 = 3250733) B3250733
theorem B4876109 : Blo 2165435 4876109 := bbase (se 3 (by rfl) ⟨914270, by rfl⟩ : syracuseStep 4876109 = 1828541) (by norm_num)
theorem B3250739 : Blo 2165435 3250739 := bstep (se 1 (by rfl) ⟨2438054, by rfl⟩ : syracuseStep 3250739 = 4876109) B4876109
theorem B2167159 : Blo 2165435 2167159 := bstep (se 1 (by rfl) ⟨1625369, by rfl⟩ : syracuseStep 2167159 = 3250739) B3250739
theorem B2742817 : Blo 2165435 2742817 := bbase (se 2 (by rfl) ⟨1028556, by rfl⟩ : syracuseStep 2742817 = 2057113) (by norm_num)
theorem B3657089 : Blo 2165435 3657089 := bstep (se 2 (by rfl) ⟨1371408, by rfl⟩ : syracuseStep 3657089 = 2742817) B2742817
theorem B2438059 : Blo 2165435 2438059 := bstep (se 1 (by rfl) ⟨1828544, by rfl⟩ : syracuseStep 2438059 = 3657089) B3657089
theorem B3250745 : Blo 2165435 3250745 := bstep (se 2 (by rfl) ⟨1219029, by rfl⟩ : syracuseStep 3250745 = 2438059) B2438059
theorem B2167163 : Blo 2165435 2167163 := bstep (se 1 (by rfl) ⟨1625372, by rfl⟩ : syracuseStep 2167163 = 3250745) B3250745
theorem B24685397 : Blo 2165435 24685397 := bbase (se 9 (by rfl) ⟨72320, by rfl⟩ : syracuseStep 24685397 = 144641) (by norm_num)
theorem B16456931 : Blo 2165435 16456931 := bstep (se 1 (by rfl) ⟨12342698, by rfl⟩ : syracuseStep 16456931 = 24685397) B24685397
theorem B10971287 : Blo 2165435 10971287 := bstep (se 1 (by rfl) ⟨8228465, by rfl⟩ : syracuseStep 10971287 = 16456931) B16456931
theorem B7314191 : Blo 2165435 7314191 := bstep (se 1 (by rfl) ⟨5485643, by rfl⟩ : syracuseStep 7314191 = 10971287) B10971287
theorem B4876127 : Blo 2165435 4876127 := bstep (se 1 (by rfl) ⟨3657095, by rfl⟩ : syracuseStep 4876127 = 7314191) B7314191
theorem B3250751 : Blo 2165435 3250751 := bstep (se 1 (by rfl) ⟨2438063, by rfl⟩ : syracuseStep 3250751 = 4876127) B4876127
theorem B2167167 : Blo 2165435 2167167 := bstep (se 1 (by rfl) ⟨1625375, by rfl⟩ : syracuseStep 2167167 = 3250751) B3250751
theorem B3250757 : Blo 2165435 3250757 := bbase (se 4 (by rfl) ⟨304758, by rfl⟩ : syracuseStep 3250757 = 609517) (by norm_num)
theorem B2167171 : Blo 2165435 2167171 := bstep (se 1 (by rfl) ⟨1625378, by rfl⟩ : syracuseStep 2167171 = 3250757) B3250757
theorem B3657109 : Blo 2165435 3657109 := bbase (se 6 (by rfl) ⟨85713, by rfl⟩ : syracuseStep 3657109 = 171427) (by norm_num)
theorem B4876145 : Blo 2165435 4876145 := bstep (se 2 (by rfl) ⟨1828554, by rfl⟩ : syracuseStep 4876145 = 3657109) B3657109
theorem B3250763 : Blo 2165435 3250763 := bstep (se 1 (by rfl) ⟨2438072, by rfl⟩ : syracuseStep 3250763 = 4876145) B4876145
theorem B2167175 : Blo 2165435 2167175 := bstep (se 1 (by rfl) ⟨1625381, by rfl⟩ : syracuseStep 2167175 = 3250763) B3250763
theorem B2438077 : Blo 2165435 2438077 := bbase (se 3 (by rfl) ⟨457139, by rfl⟩ : syracuseStep 2438077 = 914279) (by norm_num)
theorem B3250769 : Blo 2165435 3250769 := bstep (se 2 (by rfl) ⟨1219038, by rfl⟩ : syracuseStep 3250769 = 2438077) B2438077
theorem B2167179 : Blo 2165435 2167179 := bstep (se 1 (by rfl) ⟨1625384, by rfl⟩ : syracuseStep 2167179 = 3250769) B3250769
theorem B7314245 : Blo 2165435 7314245 := bbase (se 4 (by rfl) ⟨685710, by rfl⟩ : syracuseStep 7314245 = 1371421) (by norm_num)
theorem B4876163 : Blo 2165435 4876163 := bstep (se 1 (by rfl) ⟨3657122, by rfl⟩ : syracuseStep 4876163 = 7314245) B7314245
theorem B3250775 : Blo 2165435 3250775 := bstep (se 1 (by rfl) ⟨2438081, by rfl⟩ : syracuseStep 3250775 = 4876163) B4876163
theorem B2167183 : Blo 2165435 2167183 := bstep (se 1 (by rfl) ⟨1625387, by rfl⟩ : syracuseStep 2167183 = 3250775) B3250775
theorem B3250781 : Blo 2165435 3250781 := bbase (se 3 (by rfl) ⟨609521, by rfl⟩ : syracuseStep 3250781 = 1219043) (by norm_num)
theorem B2167187 : Blo 2165435 2167187 := bstep (se 1 (by rfl) ⟨1625390, by rfl⟩ : syracuseStep 2167187 = 3250781) B3250781
theorem B4876181 : Blo 2165435 4876181 := bbase (se 6 (by rfl) ⟨114285, by rfl⟩ : syracuseStep 4876181 = 228571) (by norm_num)
theorem B3250787 : Blo 2165435 3250787 := bstep (se 1 (by rfl) ⟨2438090, by rfl⟩ : syracuseStep 3250787 = 4876181) B4876181
theorem B2167191 : Blo 2165435 2167191 := bstep (se 1 (by rfl) ⟨1625393, by rfl⟩ : syracuseStep 2167191 = 3250787) B3250787
theorem B4628573 : Blo 2165435 4628573 := bbase (se 3 (by rfl) ⟨867857, by rfl⟩ : syracuseStep 4628573 = 1735715) (by norm_num)
theorem B3085715 : Blo 2165435 3085715 := bstep (se 1 (by rfl) ⟨2314286, by rfl⟩ : syracuseStep 3085715 = 4628573) B4628573
theorem B8228573 : Blo 2165435 8228573 := bstep (se 3 (by rfl) ⟨1542857, by rfl⟩ : syracuseStep 8228573 = 3085715) B3085715
theorem B5485715 : Blo 2165435 5485715 := bstep (se 1 (by rfl) ⟨4114286, by rfl⟩ : syracuseStep 5485715 = 8228573) B8228573
theorem B3657143 : Blo 2165435 3657143 := bstep (se 1 (by rfl) ⟨2742857, by rfl⟩ : syracuseStep 3657143 = 5485715) B5485715
theorem B2438095 : Blo 2165435 2438095 := bstep (se 1 (by rfl) ⟨1828571, by rfl⟩ : syracuseStep 2438095 = 3657143) B3657143
theorem B3250793 : Blo 2165435 3250793 := bstep (se 2 (by rfl) ⟨1219047, by rfl⟩ : syracuseStep 3250793 = 2438095) B2438095
theorem B2167195 : Blo 2165435 2167195 := bstep (se 1 (by rfl) ⟨1625396, by rfl⟩ : syracuseStep 2167195 = 3250793) B3250793
theorem B15621461 : Blo 2165435 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B10414307 : Blo 2165435 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B6942871 : Blo 2165435 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B9257161 : Blo 2165435 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B12342881 : Blo 2165435 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B8228587 : Blo 2165435 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B10971449 : Blo 2165435 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B7314299 : Blo 2165435 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B4876199 : Blo 2165435 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B3250799 : Blo 2165435 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B2167199 : Blo 2165435 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B3250805 : Blo 2165435 3250805 := bbase (se 5 (by rfl) ⟨152381, by rfl⟩ : syracuseStep 3250805 = 304763) (by norm_num)
theorem B2167203 : Blo 2165435 2167203 := bstep (se 1 (by rfl) ⟨1625402, by rfl⟩ : syracuseStep 2167203 = 3250805) B3250805
theorem B4114309 : Blo 2165435 4114309 := bbase (se 4 (by rfl) ⟨385716, by rfl⟩ : syracuseStep 4114309 = 771433) (by norm_num)
theorem B5485745 : Blo 2165435 5485745 := bstep (se 2 (by rfl) ⟨2057154, by rfl⟩ : syracuseStep 5485745 = 4114309) B4114309
theorem B3657163 : Blo 2165435 3657163 := bstep (se 1 (by rfl) ⟨2742872, by rfl⟩ : syracuseStep 3657163 = 5485745) B5485745
theorem B4876217 : Blo 2165435 4876217 := bstep (se 2 (by rfl) ⟨1828581, by rfl⟩ : syracuseStep 4876217 = 3657163) B3657163
theorem B3250811 : Blo 2165435 3250811 := bstep (se 1 (by rfl) ⟨2438108, by rfl⟩ : syracuseStep 3250811 = 4876217) B4876217
theorem B2167207 : Blo 2165435 2167207 := bstep (se 1 (by rfl) ⟨1625405, by rfl⟩ : syracuseStep 2167207 = 3250811) B3250811
theorem B2438113 : Blo 2165435 2438113 := bbase (se 2 (by rfl) ⟨914292, by rfl⟩ : syracuseStep 2438113 = 1828585) (by norm_num)
theorem B3250817 : Blo 2165435 3250817 := bstep (se 2 (by rfl) ⟨1219056, by rfl⟩ : syracuseStep 3250817 = 2438113) B2438113
theorem B2167211 : Blo 2165435 2167211 := bstep (se 1 (by rfl) ⟨1625408, by rfl⟩ : syracuseStep 2167211 = 3250817) B3250817
theorem B5485765 : Blo 2165435 5485765 := bbase (se 4 (by rfl) ⟨514290, by rfl⟩ : syracuseStep 5485765 = 1028581) (by norm_num)
theorem B7314353 : Blo 2165435 7314353 := bstep (se 2 (by rfl) ⟨2742882, by rfl⟩ : syracuseStep 7314353 = 5485765) B5485765
theorem B4876235 : Blo 2165435 4876235 := bstep (se 1 (by rfl) ⟨3657176, by rfl⟩ : syracuseStep 4876235 = 7314353) B7314353
theorem B3250823 : Blo 2165435 3250823 := bstep (se 1 (by rfl) ⟨2438117, by rfl⟩ : syracuseStep 3250823 = 4876235) B4876235
theorem B2167215 : Blo 2165435 2167215 := bstep (se 1 (by rfl) ⟨1625411, by rfl⟩ : syracuseStep 2167215 = 3250823) B3250823
theorem B3250829 : Blo 2165435 3250829 := bbase (se 3 (by rfl) ⟨609530, by rfl⟩ : syracuseStep 3250829 = 1219061) (by norm_num)
theorem B2167219 : Blo 2165435 2167219 := bstep (se 1 (by rfl) ⟨1625414, by rfl⟩ : syracuseStep 2167219 = 3250829) B3250829
theorem B4876253 : Blo 2165435 4876253 := bbase (se 3 (by rfl) ⟨914297, by rfl⟩ : syracuseStep 4876253 = 1828595) (by norm_num)
theorem B3250835 : Blo 2165435 3250835 := bstep (se 1 (by rfl) ⟨2438126, by rfl⟩ : syracuseStep 3250835 = 4876253) B4876253
theorem B2167223 : Blo 2165435 2167223 := bstep (se 1 (by rfl) ⟨1625417, by rfl⟩ : syracuseStep 2167223 = 3250835) B3250835
theorem B3657197 : Blo 2165435 3657197 := bbase (se 3 (by rfl) ⟨685724, by rfl⟩ : syracuseStep 3657197 = 1371449) (by norm_num)
theorem B2438131 : Blo 2165435 2438131 := bstep (se 1 (by rfl) ⟨1828598, by rfl⟩ : syracuseStep 2438131 = 3657197) B3657197
theorem B3250841 : Blo 2165435 3250841 := bstep (se 2 (by rfl) ⟨1219065, by rfl⟩ : syracuseStep 3250841 = 2438131) B2438131
theorem B2167227 : Blo 2165435 2167227 := bstep (se 1 (by rfl) ⟨1625420, by rfl⟩ : syracuseStep 2167227 = 3250841) B3250841
theorem B2471401 : Blo 2165435 2471401 := bbase (se 2 (by rfl) ⟨926775, by rfl⟩ : syracuseStep 2471401 = 1853551) (by norm_num)
theorem B13180805 : Blo 2165435 13180805 := bstep (se 4 (by rfl) ⟨1235700, by rfl⟩ : syracuseStep 13180805 = 2471401) B2471401
theorem B8787203 : Blo 2165435 8787203 := bstep (se 1 (by rfl) ⟨6590402, by rfl⟩ : syracuseStep 8787203 = 13180805) B13180805
theorem B5858135 : Blo 2165435 5858135 := bstep (se 1 (by rfl) ⟨4393601, by rfl⟩ : syracuseStep 5858135 = 8787203) B8787203
theorem B3905423 : Blo 2165435 3905423 := bstep (se 1 (by rfl) ⟨2929067, by rfl⟩ : syracuseStep 3905423 = 5858135) B5858135
theorem B2603615 : Blo 2165435 2603615 := bstep (se 1 (by rfl) ⟨1952711, by rfl⟩ : syracuseStep 2603615 = 3905423) B3905423
theorem B27771893 : Blo 2165435 27771893 := bstep (se 5 (by rfl) ⟨1301807, by rfl⟩ : syracuseStep 27771893 = 2603615) B2603615
theorem B18514595 : Blo 2165435 18514595 := bstep (se 1 (by rfl) ⟨13885946, by rfl⟩ : syracuseStep 18514595 = 27771893) B27771893
theorem B12343063 : Blo 2165435 12343063 := bstep (se 1 (by rfl) ⟨9257297, by rfl⟩ : syracuseStep 12343063 = 18514595) B18514595
theorem B16457417 : Blo 2165435 16457417 := bstep (se 2 (by rfl) ⟨6171531, by rfl⟩ : syracuseStep 16457417 = 12343063) B12343063
theorem B10971611 : Blo 2165435 10971611 := bstep (se 1 (by rfl) ⟨8228708, by rfl⟩ : syracuseStep 10971611 = 16457417) B16457417
theorem B7314407 : Blo 2165435 7314407 := bstep (se 1 (by rfl) ⟨5485805, by rfl⟩ : syracuseStep 7314407 = 10971611) B10971611
theorem B4876271 : Blo 2165435 4876271 := bstep (se 1 (by rfl) ⟨3657203, by rfl⟩ : syracuseStep 4876271 = 7314407) B7314407
theorem B3250847 : Blo 2165435 3250847 := bstep (se 1 (by rfl) ⟨2438135, by rfl⟩ : syracuseStep 3250847 = 4876271) B4876271
theorem B2167231 : Blo 2165435 2167231 := bstep (se 1 (by rfl) ⟨1625423, by rfl⟩ : syracuseStep 2167231 = 3250847) B3250847
theorem B3250853 : Blo 2165435 3250853 := bbase (se 4 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 3250853 = 609535) (by norm_num)
theorem B2167235 : Blo 2165435 2167235 := bstep (se 1 (by rfl) ⟨1625426, by rfl⟩ : syracuseStep 2167235 = 3250853) B3250853
theorem B2742913 : Blo 2165435 2742913 := bbase (se 2 (by rfl) ⟨1028592, by rfl⟩ : syracuseStep 2742913 = 2057185) (by norm_num)
theorem B3657217 : Blo 2165435 3657217 := bstep (se 2 (by rfl) ⟨1371456, by rfl⟩ : syracuseStep 3657217 = 2742913) B2742913
theorem B4876289 : Blo 2165435 4876289 := bstep (se 2 (by rfl) ⟨1828608, by rfl⟩ : syracuseStep 4876289 = 3657217) B3657217
theorem B3250859 : Blo 2165435 3250859 := bstep (se 1 (by rfl) ⟨2438144, by rfl⟩ : syracuseStep 3250859 = 4876289) B4876289
theorem B2167239 : Blo 2165435 2167239 := bstep (se 1 (by rfl) ⟨1625429, by rfl⟩ : syracuseStep 2167239 = 3250859) B3250859
theorem B2438149 : Blo 2165435 2438149 := bbase (se 4 (by rfl) ⟨228576, by rfl⟩ : syracuseStep 2438149 = 457153) (by norm_num)
theorem B3250865 : Blo 2165435 3250865 := bstep (se 2 (by rfl) ⟨1219074, by rfl⟩ : syracuseStep 3250865 = 2438149) B2438149
theorem B2167243 : Blo 2165435 2167243 := bstep (se 1 (by rfl) ⟨1625432, by rfl⟩ : syracuseStep 2167243 = 3250865) B3250865
theorem B3085789 : Blo 2165435 3085789 := bbase (se 3 (by rfl) ⟨578585, by rfl⟩ : syracuseStep 3085789 = 1157171) (by norm_num)
theorem B4114385 : Blo 2165435 4114385 := bstep (se 2 (by rfl) ⟨1542894, by rfl⟩ : syracuseStep 4114385 = 3085789) B3085789
theorem B2742923 : Blo 2165435 2742923 := bstep (se 1 (by rfl) ⟨2057192, by rfl⟩ : syracuseStep 2742923 = 4114385) B4114385
theorem B7314461 : Blo 2165435 7314461 := bstep (se 3 (by rfl) ⟨1371461, by rfl⟩ : syracuseStep 7314461 = 2742923) B2742923
theorem B4876307 : Blo 2165435 4876307 := bstep (se 1 (by rfl) ⟨3657230, by rfl⟩ : syracuseStep 4876307 = 7314461) B7314461
theorem B3250871 : Blo 2165435 3250871 := bstep (se 1 (by rfl) ⟨2438153, by rfl⟩ : syracuseStep 3250871 = 4876307) B4876307
theorem B2167247 : Blo 2165435 2167247 := bstep (se 1 (by rfl) ⟨1625435, by rfl⟩ : syracuseStep 2167247 = 3250871) B3250871
theorem B3250877 : Blo 2165435 3250877 := bbase (se 3 (by rfl) ⟨609539, by rfl⟩ : syracuseStep 3250877 = 1219079) (by norm_num)
theorem B2167251 : Blo 2165435 2167251 := bstep (se 1 (by rfl) ⟨1625438, by rfl⟩ : syracuseStep 2167251 = 3250877) B3250877
theorem B4876325 : Blo 2165435 4876325 := bbase (se 4 (by rfl) ⟨457155, by rfl⟩ : syracuseStep 4876325 = 914311) (by norm_num)
theorem B3250883 : Blo 2165435 3250883 := bstep (se 1 (by rfl) ⟨2438162, by rfl⟩ : syracuseStep 3250883 = 4876325) B4876325
theorem B2167255 : Blo 2165435 2167255 := bstep (se 1 (by rfl) ⟨1625441, by rfl⟩ : syracuseStep 2167255 = 3250883) B3250883
theorem B5485877 : Blo 2165435 5485877 := bbase (se 5 (by rfl) ⟨257150, by rfl⟩ : syracuseStep 5485877 = 514301) (by norm_num)
theorem B3657251 : Blo 2165435 3657251 := bstep (se 1 (by rfl) ⟨2742938, by rfl⟩ : syracuseStep 3657251 = 5485877) B5485877
theorem B2438167 : Blo 2165435 2438167 := bstep (se 1 (by rfl) ⟨1828625, by rfl⟩ : syracuseStep 2438167 = 3657251) B3657251
theorem B3250889 : Blo 2165435 3250889 := bstep (se 2 (by rfl) ⟨1219083, by rfl⟩ : syracuseStep 3250889 = 2438167) B2438167
theorem B2167259 : Blo 2165435 2167259 := bstep (se 1 (by rfl) ⟨1625444, by rfl⟩ : syracuseStep 2167259 = 3250889) B3250889
theorem B2196833 : Blo 2165435 2196833 := bbase (se 2 (by rfl) ⟨823812, by rfl⟩ : syracuseStep 2196833 = 1647625) (by norm_num)
theorem B23432885 : Blo 2165435 23432885 := bstep (se 5 (by rfl) ⟨1098416, by rfl⟩ : syracuseStep 23432885 = 2196833) B2196833
theorem B15621923 : Blo 2165435 15621923 := bstep (se 1 (by rfl) ⟨11716442, by rfl⟩ : syracuseStep 15621923 = 23432885) B23432885
theorem B10414615 : Blo 2165435 10414615 := bstep (se 1 (by rfl) ⟨7810961, by rfl⟩ : syracuseStep 10414615 = 15621923) B15621923
theorem B13886153 : Blo 2165435 13886153 := bstep (se 2 (by rfl) ⟨5207307, by rfl⟩ : syracuseStep 13886153 = 10414615) B10414615
theorem B9257435 : Blo 2165435 9257435 := bstep (se 1 (by rfl) ⟨6943076, by rfl⟩ : syracuseStep 9257435 = 13886153) B13886153
theorem B6171623 : Blo 2165435 6171623 := bstep (se 1 (by rfl) ⟨4628717, by rfl⟩ : syracuseStep 6171623 = 9257435) B9257435
theorem B4114415 : Blo 2165435 4114415 := bstep (se 1 (by rfl) ⟨3085811, by rfl⟩ : syracuseStep 4114415 = 6171623) B6171623
theorem B10971773 : Blo 2165435 10971773 := bstep (se 3 (by rfl) ⟨2057207, by rfl⟩ : syracuseStep 10971773 = 4114415) B4114415
theorem B7314515 : Blo 2165435 7314515 := bstep (se 1 (by rfl) ⟨5485886, by rfl⟩ : syracuseStep 7314515 = 10971773) B10971773
theorem B4876343 : Blo 2165435 4876343 := bstep (se 1 (by rfl) ⟨3657257, by rfl⟩ : syracuseStep 4876343 = 7314515) B7314515
theorem B3250895 : Blo 2165435 3250895 := bstep (se 1 (by rfl) ⟨2438171, by rfl⟩ : syracuseStep 3250895 = 4876343) B4876343
theorem B2167263 : Blo 2165435 2167263 := bstep (se 1 (by rfl) ⟨1625447, by rfl⟩ : syracuseStep 2167263 = 3250895) B3250895
theorem B3250901 : Blo 2165435 3250901 := bbase (se 7 (by rfl) ⟨38096, by rfl⟩ : syracuseStep 3250901 = 76193) (by norm_num)
theorem B2167267 : Blo 2165435 2167267 := bstep (se 1 (by rfl) ⟨1625450, by rfl⟩ : syracuseStep 2167267 = 3250901) B3250901
theorem B79086293 : Blo 2165435 79086293 := bbase (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) (by norm_num)
theorem B52724195 : Blo 2165435 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B35149463 : Blo 2165435 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B23432975 : Blo 2165435 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B15621983 : Blo 2165435 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B10414655 : Blo 2165435 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B6943103 : Blo 2165435 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B4628735 : Blo 2165435 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B3085823 : Blo 2165435 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B8228861 : Blo 2165435 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B5485907 : Blo 2165435 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B3657271 : Blo 2165435 3657271 := bstep (se 1 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 3657271 = 5485907) B5485907
theorem B4876361 : Blo 2165435 4876361 := bstep (se 2 (by rfl) ⟨1828635, by rfl⟩ : syracuseStep 4876361 = 3657271) B3657271
theorem B3250907 : Blo 2165435 3250907 := bstep (se 1 (by rfl) ⟨2438180, by rfl⟩ : syracuseStep 3250907 = 4876361) B4876361
theorem B2167271 : Blo 2165435 2167271 := bstep (se 1 (by rfl) ⟨1625453, by rfl⟩ : syracuseStep 2167271 = 3250907) B3250907
theorem B2438185 : Blo 2165435 2438185 := bbase (se 2 (by rfl) ⟨914319, by rfl⟩ : syracuseStep 2438185 = 1828639) (by norm_num)
theorem B3250913 : Blo 2165435 3250913 := bstep (se 2 (by rfl) ⟨1219092, by rfl⟩ : syracuseStep 3250913 = 2438185) B2438185
theorem B2167275 : Blo 2165435 2167275 := bstep (se 1 (by rfl) ⟨1625456, by rfl⟩ : syracuseStep 2167275 = 3250913) B3250913
theorem B4453645 : Blo 2165435 4453645 := bbase (se 3 (by rfl) ⟨835058, by rfl⟩ : syracuseStep 4453645 = 1670117) (by norm_num)
theorem B5938193 : Blo 2165435 5938193 := bstep (se 2 (by rfl) ⟨2226822, by rfl⟩ : syracuseStep 5938193 = 4453645) B4453645
theorem B3958795 : Blo 2165435 3958795 := bstep (se 1 (by rfl) ⟨2969096, by rfl⟩ : syracuseStep 3958795 = 5938193) B5938193
theorem B5278393 : Blo 2165435 5278393 := bstep (se 2 (by rfl) ⟨1979397, by rfl⟩ : syracuseStep 5278393 = 3958795) B3958795
theorem B7037857 : Blo 2165435 7037857 := bstep (se 2 (by rfl) ⟨2639196, by rfl⟩ : syracuseStep 7037857 = 5278393) B5278393
theorem B9383809 : Blo 2165435 9383809 := bstep (se 2 (by rfl) ⟨3518928, by rfl⟩ : syracuseStep 9383809 = 7037857) B7037857
theorem B12511745 : Blo 2165435 12511745 := bstep (se 2 (by rfl) ⟨4691904, by rfl⟩ : syracuseStep 12511745 = 9383809) B9383809
theorem B8341163 : Blo 2165435 8341163 := bstep (se 1 (by rfl) ⟨6255872, by rfl⟩ : syracuseStep 8341163 = 12511745) B12511745
theorem B5560775 : Blo 2165435 5560775 := bstep (se 1 (by rfl) ⟨4170581, by rfl⟩ : syracuseStep 5560775 = 8341163) B8341163
theorem B3707183 : Blo 2165435 3707183 := bstep (se 1 (by rfl) ⟨2780387, by rfl⟩ : syracuseStep 3707183 = 5560775) B5560775
theorem B9885821 : Blo 2165435 9885821 := bstep (se 3 (by rfl) ⟨1853591, by rfl⟩ : syracuseStep 9885821 = 3707183) B3707183
theorem B26362189 : Blo 2165435 26362189 := bstep (se 3 (by rfl) ⟨4942910, by rfl⟩ : syracuseStep 26362189 = 9885821) B9885821
theorem B35149585 : Blo 2165435 35149585 := bstep (se 2 (by rfl) ⟨13181094, by rfl⟩ : syracuseStep 35149585 = 26362189) B26362189
theorem B46866113 : Blo 2165435 46866113 := bstep (se 2 (by rfl) ⟨17574792, by rfl⟩ : syracuseStep 46866113 = 35149585) B35149585
theorem B31244075 : Blo 2165435 31244075 := bstep (se 1 (by rfl) ⟨23433056, by rfl⟩ : syracuseStep 31244075 = 46866113) B46866113
theorem B20829383 : Blo 2165435 20829383 := bstep (se 1 (by rfl) ⟨15622037, by rfl⟩ : syracuseStep 20829383 = 31244075) B31244075
theorem B13886255 : Blo 2165435 13886255 := bstep (se 1 (by rfl) ⟨10414691, by rfl⟩ : syracuseStep 13886255 = 20829383) B20829383
theorem B9257503 : Blo 2165435 9257503 := bstep (se 1 (by rfl) ⟨6943127, by rfl⟩ : syracuseStep 9257503 = 13886255) B13886255
theorem B12343337 : Blo 2165435 12343337 := bstep (se 2 (by rfl) ⟨4628751, by rfl⟩ : syracuseStep 12343337 = 9257503) B9257503
theorem B8228891 : Blo 2165435 8228891 := bstep (se 1 (by rfl) ⟨6171668, by rfl⟩ : syracuseStep 8228891 = 12343337) B12343337
theorem B5485927 : Blo 2165435 5485927 := bstep (se 1 (by rfl) ⟨4114445, by rfl⟩ : syracuseStep 5485927 = 8228891) B8228891
theorem B7314569 : Blo 2165435 7314569 := bstep (se 2 (by rfl) ⟨2742963, by rfl⟩ : syracuseStep 7314569 = 5485927) B5485927
theorem B4876379 : Blo 2165435 4876379 := bstep (se 1 (by rfl) ⟨3657284, by rfl⟩ : syracuseStep 4876379 = 7314569) B7314569
theorem B3250919 : Blo 2165435 3250919 := bstep (se 1 (by rfl) ⟨2438189, by rfl⟩ : syracuseStep 3250919 = 4876379) B4876379
theorem B2167279 : Blo 2165435 2167279 := bstep (se 1 (by rfl) ⟨1625459, by rfl⟩ : syracuseStep 2167279 = 3250919) B3250919
theorem B3250925 : Blo 2165435 3250925 := bbase (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) (by norm_num)
theorem B2167283 : Blo 2165435 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B4876397 : Blo 2165435 4876397 := bbase (se 3 (by rfl) ⟨914324, by rfl⟩ : syracuseStep 4876397 = 1828649) (by norm_num)
theorem B3250931 : Blo 2165435 3250931 := bstep (se 1 (by rfl) ⟨2438198, by rfl⟩ : syracuseStep 3250931 = 4876397) B4876397
theorem B2167287 : Blo 2165435 2167287 := bstep (se 1 (by rfl) ⟨1625465, by rfl⟩ : syracuseStep 2167287 = 3250931) B3250931
theorem B4114469 : Blo 2165435 4114469 := bbase (se 4 (by rfl) ⟨385731, by rfl⟩ : syracuseStep 4114469 = 771463) (by norm_num)
theorem B2742979 : Blo 2165435 2742979 := bstep (se 1 (by rfl) ⟨2057234, by rfl⟩ : syracuseStep 2742979 = 4114469) B4114469
theorem B3657305 : Blo 2165435 3657305 := bstep (se 2 (by rfl) ⟨1371489, by rfl⟩ : syracuseStep 3657305 = 2742979) B2742979
theorem B2438203 : Blo 2165435 2438203 := bstep (se 1 (by rfl) ⟨1828652, by rfl⟩ : syracuseStep 2438203 = 3657305) B3657305
theorem B3250937 : Blo 2165435 3250937 := bstep (se 2 (by rfl) ⟨1219101, by rfl⟩ : syracuseStep 3250937 = 2438203) B2438203
theorem B2167291 : Blo 2165435 2167291 := bstep (se 1 (by rfl) ⟨1625468, by rfl⟩ : syracuseStep 2167291 = 3250937) B3250937
theorem B9885893 : Blo 2165435 9885893 := bbase (se 4 (by rfl) ⟨926802, by rfl⟩ : syracuseStep 9885893 = 1853605) (by norm_num)
theorem B26362381 : Blo 2165435 26362381 := bstep (se 3 (by rfl) ⟨4942946, by rfl⟩ : syracuseStep 26362381 = 9885893) B9885893
theorem B35149841 : Blo 2165435 35149841 := bstep (se 2 (by rfl) ⟨13181190, by rfl⟩ : syracuseStep 35149841 = 26362381) B26362381
theorem B23433227 : Blo 2165435 23433227 := bstep (se 1 (by rfl) ⟨17574920, by rfl⟩ : syracuseStep 23433227 = 35149841) B35149841
theorem B15622151 : Blo 2165435 15622151 := bstep (se 1 (by rfl) ⟨11716613, by rfl⟩ : syracuseStep 15622151 = 23433227) B23433227
theorem B41659069 : Blo 2165435 41659069 := bstep (se 3 (by rfl) ⟨7811075, by rfl⟩ : syracuseStep 41659069 = 15622151) B15622151
theorem B55545425 : Blo 2165435 55545425 := bstep (se 2 (by rfl) ⟨20829534, by rfl⟩ : syracuseStep 55545425 = 41659069) B41659069
theorem B37030283 : Blo 2165435 37030283 := bstep (se 1 (by rfl) ⟨27772712, by rfl⟩ : syracuseStep 37030283 = 55545425) B55545425
theorem B24686855 : Blo 2165435 24686855 := bstep (se 1 (by rfl) ⟨18515141, by rfl⟩ : syracuseStep 24686855 = 37030283) B37030283
theorem B16457903 : Blo 2165435 16457903 := bstep (se 1 (by rfl) ⟨12343427, by rfl⟩ : syracuseStep 16457903 = 24686855) B24686855
theorem B10971935 : Blo 2165435 10971935 := bstep (se 1 (by rfl) ⟨8228951, by rfl⟩ : syracuseStep 10971935 = 16457903) B16457903
theorem B7314623 : Blo 2165435 7314623 := bstep (se 1 (by rfl) ⟨5485967, by rfl⟩ : syracuseStep 7314623 = 10971935) B10971935
theorem B4876415 : Blo 2165435 4876415 := bstep (se 1 (by rfl) ⟨3657311, by rfl⟩ : syracuseStep 4876415 = 7314623) B7314623
theorem B3250943 : Blo 2165435 3250943 := bstep (se 1 (by rfl) ⟨2438207, by rfl⟩ : syracuseStep 3250943 = 4876415) B4876415
theorem B2167295 : Blo 2165435 2167295 := bstep (se 1 (by rfl) ⟨1625471, by rfl⟩ : syracuseStep 2167295 = 3250943) B3250943
theorem B3250949 : Blo 2165435 3250949 := bbase (se 4 (by rfl) ⟨304776, by rfl⟩ : syracuseStep 3250949 = 609553) (by norm_num)
theorem B2167299 : Blo 2165435 2167299 := bstep (se 1 (by rfl) ⟨1625474, by rfl⟩ : syracuseStep 2167299 = 3250949) B3250949
theorem B3657325 : Blo 2165435 3657325 := bbase (se 3 (by rfl) ⟨685748, by rfl⟩ : syracuseStep 3657325 = 1371497) (by norm_num)
theorem B4876433 : Blo 2165435 4876433 := bstep (se 2 (by rfl) ⟨1828662, by rfl⟩ : syracuseStep 4876433 = 3657325) B3657325
theorem B3250955 : Blo 2165435 3250955 := bstep (se 1 (by rfl) ⟨2438216, by rfl⟩ : syracuseStep 3250955 = 4876433) B4876433
theorem B2167303 : Blo 2165435 2167303 := bstep (se 1 (by rfl) ⟨1625477, by rfl⟩ : syracuseStep 2167303 = 3250955) B3250955
theorem B2438221 : Blo 2165435 2438221 := bbase (se 3 (by rfl) ⟨457166, by rfl⟩ : syracuseStep 2438221 = 914333) (by norm_num)
theorem B3250961 : Blo 2165435 3250961 := bstep (se 2 (by rfl) ⟨1219110, by rfl⟩ : syracuseStep 3250961 = 2438221) B2438221
theorem B2167307 : Blo 2165435 2167307 := bstep (se 1 (by rfl) ⟨1625480, by rfl⟩ : syracuseStep 2167307 = 3250961) B3250961
theorem B7314677 : Blo 2165435 7314677 := bbase (se 5 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 7314677 = 685751) (by norm_num)
theorem B4876451 : Blo 2165435 4876451 := bstep (se 1 (by rfl) ⟨3657338, by rfl⟩ : syracuseStep 4876451 = 7314677) B7314677
theorem B3250967 : Blo 2165435 3250967 := bstep (se 1 (by rfl) ⟨2438225, by rfl⟩ : syracuseStep 3250967 = 4876451) B4876451
theorem B2167311 : Blo 2165435 2167311 := bstep (se 1 (by rfl) ⟨1625483, by rfl⟩ : syracuseStep 2167311 = 3250967) B3250967
theorem B3250973 : Blo 2165435 3250973 := bbase (se 3 (by rfl) ⟨609557, by rfl⟩ : syracuseStep 3250973 = 1219115) (by norm_num)
theorem B2167315 : Blo 2165435 2167315 := bstep (se 1 (by rfl) ⟨1625486, by rfl⟩ : syracuseStep 2167315 = 3250973) B3250973
theorem B4876469 : Blo 2165435 4876469 := bbase (se 5 (by rfl) ⟨228584, by rfl⟩ : syracuseStep 4876469 = 457169) (by norm_num)
theorem B3250979 : Blo 2165435 3250979 := bstep (se 1 (by rfl) ⟨2438234, by rfl⟩ : syracuseStep 3250979 = 4876469) B4876469
theorem B2167319 : Blo 2165435 2167319 := bstep (se 1 (by rfl) ⟨1625489, by rfl⟩ : syracuseStep 2167319 = 3250979) B3250979
theorem B5207453 : Blo 2165435 5207453 := bbase (se 3 (by rfl) ⟨976397, by rfl⟩ : syracuseStep 5207453 = 1952795) (by norm_num)
theorem B3471635 : Blo 2165435 3471635 := bstep (se 1 (by rfl) ⟨2603726, by rfl⟩ : syracuseStep 3471635 = 5207453) B5207453
theorem B2314423 : Blo 2165435 2314423 := bstep (se 1 (by rfl) ⟨1735817, by rfl⟩ : syracuseStep 2314423 = 3471635) B3471635
theorem B12343589 : Blo 2165435 12343589 := bstep (se 4 (by rfl) ⟨1157211, by rfl⟩ : syracuseStep 12343589 = 2314423) B2314423
theorem B8229059 : Blo 2165435 8229059 := bstep (se 1 (by rfl) ⟨6171794, by rfl⟩ : syracuseStep 8229059 = 12343589) B12343589
theorem B5486039 : Blo 2165435 5486039 := bstep (se 1 (by rfl) ⟨4114529, by rfl⟩ : syracuseStep 5486039 = 8229059) B8229059
theorem B3657359 : Blo 2165435 3657359 := bstep (se 1 (by rfl) ⟨2743019, by rfl⟩ : syracuseStep 3657359 = 5486039) B5486039
theorem B2438239 : Blo 2165435 2438239 := bstep (se 1 (by rfl) ⟨1828679, by rfl⟩ : syracuseStep 2438239 = 3657359) B3657359
theorem B3250985 : Blo 2165435 3250985 := bstep (se 2 (by rfl) ⟨1219119, by rfl⟩ : syracuseStep 3250985 = 2438239) B2438239
theorem B2167323 : Blo 2165435 2167323 := bstep (se 1 (by rfl) ⟨1625492, by rfl⟩ : syracuseStep 2167323 = 3250985) B3250985
theorem B3905597 : Blo 2165435 3905597 := bbase (se 3 (by rfl) ⟨732299, by rfl⟩ : syracuseStep 3905597 = 1464599) (by norm_num)
theorem B2603731 : Blo 2165435 2603731 := bstep (se 1 (by rfl) ⟨1952798, by rfl⟩ : syracuseStep 2603731 = 3905597) B3905597
theorem B3471641 : Blo 2165435 3471641 := bstep (se 2 (by rfl) ⟨1301865, by rfl⟩ : syracuseStep 3471641 = 2603731) B2603731
theorem B2314427 : Blo 2165435 2314427 := bstep (se 1 (by rfl) ⟨1735820, by rfl⟩ : syracuseStep 2314427 = 3471641) B3471641
theorem B6171805 : Blo 2165435 6171805 := bstep (se 3 (by rfl) ⟨1157213, by rfl⟩ : syracuseStep 6171805 = 2314427) B2314427
theorem B8229073 : Blo 2165435 8229073 := bstep (se 2 (by rfl) ⟨3085902, by rfl⟩ : syracuseStep 8229073 = 6171805) B6171805
theorem B10972097 : Blo 2165435 10972097 := bstep (se 2 (by rfl) ⟨4114536, by rfl⟩ : syracuseStep 10972097 = 8229073) B8229073
theorem B7314731 : Blo 2165435 7314731 := bstep (se 1 (by rfl) ⟨5486048, by rfl⟩ : syracuseStep 7314731 = 10972097) B10972097
theorem B4876487 : Blo 2165435 4876487 := bstep (se 1 (by rfl) ⟨3657365, by rfl⟩ : syracuseStep 4876487 = 7314731) B7314731
theorem B3250991 : Blo 2165435 3250991 := bstep (se 1 (by rfl) ⟨2438243, by rfl⟩ : syracuseStep 3250991 = 4876487) B4876487
theorem B2167327 : Blo 2165435 2167327 := bstep (se 1 (by rfl) ⟨1625495, by rfl⟩ : syracuseStep 2167327 = 3250991) B3250991
theorem B3250997 : Blo 2165435 3250997 := bbase (se 5 (by rfl) ⟨152390, by rfl⟩ : syracuseStep 3250997 = 304781) (by norm_num)
theorem B2167331 : Blo 2165435 2167331 := bstep (se 1 (by rfl) ⟨1625498, by rfl⟩ : syracuseStep 2167331 = 3250997) B3250997
theorem B5486069 : Blo 2165435 5486069 := bbase (se 5 (by rfl) ⟨257159, by rfl⟩ : syracuseStep 5486069 = 514319) (by norm_num)
theorem B3657379 : Blo 2165435 3657379 := bstep (se 1 (by rfl) ⟨2743034, by rfl⟩ : syracuseStep 3657379 = 5486069) B5486069
theorem B4876505 : Blo 2165435 4876505 := bstep (se 2 (by rfl) ⟨1828689, by rfl⟩ : syracuseStep 4876505 = 3657379) B3657379
theorem B3251003 : Blo 2165435 3251003 := bstep (se 1 (by rfl) ⟨2438252, by rfl⟩ : syracuseStep 3251003 = 4876505) B4876505
theorem B2167335 : Blo 2165435 2167335 := bstep (se 1 (by rfl) ⟨1625501, by rfl⟩ : syracuseStep 2167335 = 3251003) B3251003
theorem B2438257 : Blo 2165435 2438257 := bbase (se 2 (by rfl) ⟨914346, by rfl⟩ : syracuseStep 2438257 = 1828693) (by norm_num)
theorem B3251009 : Blo 2165435 3251009 := bstep (se 2 (by rfl) ⟨1219128, by rfl⟩ : syracuseStep 3251009 = 2438257) B2438257
theorem B2167339 : Blo 2165435 2167339 := bstep (se 1 (by rfl) ⟨1625504, by rfl⟩ : syracuseStep 2167339 = 3251009) B3251009
theorem B6943333 : Blo 2165435 6943333 := bbase (se 4 (by rfl) ⟨650937, by rfl⟩ : syracuseStep 6943333 = 1301875) (by norm_num)
theorem B9257777 : Blo 2165435 9257777 := bstep (se 2 (by rfl) ⟨3471666, by rfl⟩ : syracuseStep 9257777 = 6943333) B6943333
theorem B6171851 : Blo 2165435 6171851 := bstep (se 1 (by rfl) ⟨4628888, by rfl⟩ : syracuseStep 6171851 = 9257777) B9257777
theorem B4114567 : Blo 2165435 4114567 := bstep (se 1 (by rfl) ⟨3085925, by rfl⟩ : syracuseStep 4114567 = 6171851) B6171851
theorem B5486089 : Blo 2165435 5486089 := bstep (se 2 (by rfl) ⟨2057283, by rfl⟩ : syracuseStep 5486089 = 4114567) B4114567
theorem B7314785 : Blo 2165435 7314785 := bstep (se 2 (by rfl) ⟨2743044, by rfl⟩ : syracuseStep 7314785 = 5486089) B5486089
theorem B4876523 : Blo 2165435 4876523 := bstep (se 1 (by rfl) ⟨3657392, by rfl⟩ : syracuseStep 4876523 = 7314785) B7314785
theorem B3251015 : Blo 2165435 3251015 := bstep (se 1 (by rfl) ⟨2438261, by rfl⟩ : syracuseStep 3251015 = 4876523) B4876523
theorem B2167343 : Blo 2165435 2167343 := bstep (se 1 (by rfl) ⟨1625507, by rfl⟩ : syracuseStep 2167343 = 3251015) B3251015
theorem B3251021 : Blo 2165435 3251021 := bbase (se 3 (by rfl) ⟨609566, by rfl⟩ : syracuseStep 3251021 = 1219133) (by norm_num)
theorem B2167347 : Blo 2165435 2167347 := bstep (se 1 (by rfl) ⟨1625510, by rfl⟩ : syracuseStep 2167347 = 3251021) B3251021
theorem B4876541 : Blo 2165435 4876541 := bbase (se 3 (by rfl) ⟨914351, by rfl⟩ : syracuseStep 4876541 = 1828703) (by norm_num)
theorem B3251027 : Blo 2165435 3251027 := bstep (se 1 (by rfl) ⟨2438270, by rfl⟩ : syracuseStep 3251027 = 4876541) B4876541
theorem B2167351 : Blo 2165435 2167351 := bstep (se 1 (by rfl) ⟨1625513, by rfl⟩ : syracuseStep 2167351 = 3251027) B3251027
theorem B3657413 : Blo 2165435 3657413 := bbase (se 4 (by rfl) ⟨342882, by rfl⟩ : syracuseStep 3657413 = 685765) (by norm_num)
theorem B2438275 : Blo 2165435 2438275 := bstep (se 1 (by rfl) ⟨1828706, by rfl⟩ : syracuseStep 2438275 = 3657413) B3657413
theorem B3251033 : Blo 2165435 3251033 := bstep (se 2 (by rfl) ⟨1219137, by rfl⟩ : syracuseStep 3251033 = 2438275) B2438275
theorem B2167355 : Blo 2165435 2167355 := bstep (se 1 (by rfl) ⟨1625516, by rfl⟩ : syracuseStep 2167355 = 3251033) B3251033
theorem B16458389 : Blo 2165435 16458389 := bbase (se 6 (by rfl) ⟨385743, by rfl⟩ : syracuseStep 16458389 = 771487) (by norm_num)
theorem B10972259 : Blo 2165435 10972259 := bstep (se 1 (by rfl) ⟨8229194, by rfl⟩ : syracuseStep 10972259 = 16458389) B16458389
theorem B7314839 : Blo 2165435 7314839 := bstep (se 1 (by rfl) ⟨5486129, by rfl⟩ : syracuseStep 7314839 = 10972259) B10972259
theorem B4876559 : Blo 2165435 4876559 := bstep (se 1 (by rfl) ⟨3657419, by rfl⟩ : syracuseStep 4876559 = 7314839) B7314839
theorem B3251039 : Blo 2165435 3251039 := bstep (se 1 (by rfl) ⟨2438279, by rfl⟩ : syracuseStep 3251039 = 4876559) B4876559
theorem B2167359 : Blo 2165435 2167359 := bstep (se 1 (by rfl) ⟨1625519, by rfl⟩ : syracuseStep 2167359 = 3251039) B3251039
theorem B3251045 : Blo 2165435 3251045 := bbase (se 4 (by rfl) ⟨304785, by rfl⟩ : syracuseStep 3251045 = 609571) (by norm_num)
theorem B2167363 : Blo 2165435 2167363 := bstep (se 1 (by rfl) ⟨1625522, by rfl⟩ : syracuseStep 2167363 = 3251045) B3251045
theorem B4114613 : Blo 2165435 4114613 := bbase (se 5 (by rfl) ⟨192872, by rfl⟩ : syracuseStep 4114613 = 385745) (by norm_num)
theorem B2743075 : Blo 2165435 2743075 := bstep (se 1 (by rfl) ⟨2057306, by rfl⟩ : syracuseStep 2743075 = 4114613) B4114613
theorem B3657433 : Blo 2165435 3657433 := bstep (se 2 (by rfl) ⟨1371537, by rfl⟩ : syracuseStep 3657433 = 2743075) B2743075
theorem B4876577 : Blo 2165435 4876577 := bstep (se 2 (by rfl) ⟨1828716, by rfl⟩ : syracuseStep 4876577 = 3657433) B3657433
theorem B3251051 : Blo 2165435 3251051 := bstep (se 1 (by rfl) ⟨2438288, by rfl⟩ : syracuseStep 3251051 = 4876577) B4876577
theorem B2167367 : Blo 2165435 2167367 := bstep (se 1 (by rfl) ⟨1625525, by rfl⟩ : syracuseStep 2167367 = 3251051) B3251051
theorem B2438293 : Blo 2165435 2438293 := bbase (se 6 (by rfl) ⟨57147, by rfl⟩ : syracuseStep 2438293 = 114295) (by norm_num)
theorem B3251057 : Blo 2165435 3251057 := bstep (se 2 (by rfl) ⟨1219146, by rfl⟩ : syracuseStep 3251057 = 2438293) B2438293
theorem B2167371 : Blo 2165435 2167371 := bstep (se 1 (by rfl) ⟨1625528, by rfl⟩ : syracuseStep 2167371 = 3251057) B3251057
theorem B2743085 : Blo 2165435 2743085 := bbase (se 3 (by rfl) ⟨514328, by rfl⟩ : syracuseStep 2743085 = 1028657) (by norm_num)
theorem B7314893 : Blo 2165435 7314893 := bstep (se 3 (by rfl) ⟨1371542, by rfl⟩ : syracuseStep 7314893 = 2743085) B2743085
theorem B4876595 : Blo 2165435 4876595 := bstep (se 1 (by rfl) ⟨3657446, by rfl⟩ : syracuseStep 4876595 = 7314893) B7314893
theorem B3251063 : Blo 2165435 3251063 := bstep (se 1 (by rfl) ⟨2438297, by rfl⟩ : syracuseStep 3251063 = 4876595) B4876595
theorem B2167375 : Blo 2165435 2167375 := bstep (se 1 (by rfl) ⟨1625531, by rfl⟩ : syracuseStep 2167375 = 3251063) B3251063
theorem B3251069 : Blo 2165435 3251069 := bbase (se 3 (by rfl) ⟨609575, by rfl⟩ : syracuseStep 3251069 = 1219151) (by norm_num)
theorem B2167379 : Blo 2165435 2167379 := bstep (se 1 (by rfl) ⟨1625534, by rfl⟩ : syracuseStep 2167379 = 3251069) B3251069
theorem B4876613 : Blo 2165435 4876613 := bbase (se 4 (by rfl) ⟨457182, by rfl⟩ : syracuseStep 4876613 = 914365) (by norm_num)
theorem B3251075 : Blo 2165435 3251075 := bstep (se 1 (by rfl) ⟨2438306, by rfl⟩ : syracuseStep 3251075 = 4876613) B4876613
theorem B2167383 : Blo 2165435 2167383 := bstep (se 1 (by rfl) ⟨1625537, by rfl⟩ : syracuseStep 2167383 = 3251075) B3251075
theorem B9029269 : Blo 2165435 9029269 := bbase (se 6 (by rfl) ⟨211623, by rfl⟩ : syracuseStep 9029269 = 423247) (by norm_num)
theorem B12039025 : Blo 2165435 12039025 := bstep (se 2 (by rfl) ⟨4514634, by rfl⟩ : syracuseStep 12039025 = 9029269) B9029269
theorem B16052033 : Blo 2165435 16052033 := bstep (se 2 (by rfl) ⟨6019512, by rfl⟩ : syracuseStep 16052033 = 12039025) B12039025
theorem B42805421 : Blo 2165435 42805421 := bstep (se 3 (by rfl) ⟨8026016, by rfl⟩ : syracuseStep 42805421 = 16052033) B16052033
theorem B28536947 : Blo 2165435 28536947 := bstep (se 1 (by rfl) ⟨21402710, by rfl⟩ : syracuseStep 28536947 = 42805421) B42805421
theorem B19024631 : Blo 2165435 19024631 := bstep (se 1 (by rfl) ⟨14268473, by rfl⟩ : syracuseStep 19024631 = 28536947) B28536947
theorem B12683087 : Blo 2165435 12683087 := bstep (se 1 (by rfl) ⟨9512315, by rfl⟩ : syracuseStep 12683087 = 19024631) B19024631
theorem B8455391 : Blo 2165435 8455391 := bstep (se 1 (by rfl) ⟨6341543, by rfl⟩ : syracuseStep 8455391 = 12683087) B12683087
theorem B5636927 : Blo 2165435 5636927 := bstep (se 1 (by rfl) ⟨4227695, by rfl⟩ : syracuseStep 5636927 = 8455391) B8455391
theorem B3757951 : Blo 2165435 3757951 := bstep (se 1 (by rfl) ⟨2818463, by rfl⟩ : syracuseStep 3757951 = 5636927) B5636927
theorem B20042405 : Blo 2165435 20042405 := bstep (se 4 (by rfl) ⟨1878975, by rfl⟩ : syracuseStep 20042405 = 3757951) B3757951
theorem B13361603 : Blo 2165435 13361603 := bstep (se 1 (by rfl) ⟨10021202, by rfl⟩ : syracuseStep 13361603 = 20042405) B20042405
theorem B35630941 : Blo 2165435 35630941 := bstep (se 3 (by rfl) ⟨6680801, by rfl⟩ : syracuseStep 35630941 = 13361603) B13361603
theorem B47507921 : Blo 2165435 47507921 := bstep (se 2 (by rfl) ⟨17815470, by rfl⟩ : syracuseStep 47507921 = 35630941) B35630941
theorem B31671947 : Blo 2165435 31671947 := bstep (se 1 (by rfl) ⟨23753960, by rfl⟩ : syracuseStep 31671947 = 47507921) B47507921
theorem B21114631 : Blo 2165435 21114631 := bstep (se 1 (by rfl) ⟨15835973, by rfl⟩ : syracuseStep 21114631 = 31671947) B31671947
theorem B28152841 : Blo 2165435 28152841 := bstep (se 2 (by rfl) ⟨10557315, by rfl⟩ : syracuseStep 28152841 = 21114631) B21114631
theorem B37537121 : Blo 2165435 37537121 := bstep (se 2 (by rfl) ⟨14076420, by rfl⟩ : syracuseStep 37537121 = 28152841) B28152841
theorem B25024747 : Blo 2165435 25024747 := bstep (se 1 (by rfl) ⟨18768560, by rfl⟩ : syracuseStep 25024747 = 37537121) B37537121
theorem B33366329 : Blo 2165435 33366329 := bstep (se 2 (by rfl) ⟨12512373, by rfl⟩ : syracuseStep 33366329 = 25024747) B25024747
theorem B22244219 : Blo 2165435 22244219 := bstep (se 1 (by rfl) ⟨16683164, by rfl⟩ : syracuseStep 22244219 = 33366329) B33366329
theorem B14829479 : Blo 2165435 14829479 := bstep (se 1 (by rfl) ⟨11122109, by rfl⟩ : syracuseStep 14829479 = 22244219) B22244219
theorem B9886319 : Blo 2165435 9886319 := bstep (se 1 (by rfl) ⟨7414739, by rfl⟩ : syracuseStep 9886319 = 14829479) B14829479
theorem B6590879 : Blo 2165435 6590879 := bstep (se 1 (by rfl) ⟨4943159, by rfl⟩ : syracuseStep 6590879 = 9886319) B9886319
theorem B4393919 : Blo 2165435 4393919 := bstep (se 1 (by rfl) ⟨3295439, by rfl⟩ : syracuseStep 4393919 = 6590879) B6590879
theorem B2929279 : Blo 2165435 2929279 := bstep (se 1 (by rfl) ⟨2196959, by rfl⟩ : syracuseStep 2929279 = 4393919) B4393919
theorem B3905705 : Blo 2165435 3905705 := bstep (se 2 (by rfl) ⟨1464639, by rfl⟩ : syracuseStep 3905705 = 2929279) B2929279
theorem B10415213 : Blo 2165435 10415213 := bstep (se 3 (by rfl) ⟨1952852, by rfl⟩ : syracuseStep 10415213 = 3905705) B3905705
theorem B6943475 : Blo 2165435 6943475 := bstep (se 1 (by rfl) ⟨5207606, by rfl⟩ : syracuseStep 6943475 = 10415213) B10415213
theorem B4628983 : Blo 2165435 4628983 := bstep (se 1 (by rfl) ⟨3471737, by rfl⟩ : syracuseStep 4628983 = 6943475) B6943475
theorem B6171977 : Blo 2165435 6171977 := bstep (se 2 (by rfl) ⟨2314491, by rfl⟩ : syracuseStep 6171977 = 4628983) B4628983
theorem B4114651 : Blo 2165435 4114651 := bstep (se 1 (by rfl) ⟨3085988, by rfl⟩ : syracuseStep 4114651 = 6171977) B6171977
theorem B5486201 : Blo 2165435 5486201 := bstep (se 2 (by rfl) ⟨2057325, by rfl⟩ : syracuseStep 5486201 = 4114651) B4114651
theorem B3657467 : Blo 2165435 3657467 := bstep (se 1 (by rfl) ⟨2743100, by rfl⟩ : syracuseStep 3657467 = 5486201) B5486201
theorem B2438311 : Blo 2165435 2438311 := bstep (se 1 (by rfl) ⟨1828733, by rfl⟩ : syracuseStep 2438311 = 3657467) B3657467
theorem B3251081 : Blo 2165435 3251081 := bstep (se 2 (by rfl) ⟨1219155, by rfl⟩ : syracuseStep 3251081 = 2438311) B2438311
theorem B2167387 : Blo 2165435 2167387 := bstep (se 1 (by rfl) ⟨1625540, by rfl⟩ : syracuseStep 2167387 = 3251081) B3251081
theorem B10972421 : Blo 2165435 10972421 := bbase (se 4 (by rfl) ⟨1028664, by rfl⟩ : syracuseStep 10972421 = 2057329) (by norm_num)
theorem B7314947 : Blo 2165435 7314947 := bstep (se 1 (by rfl) ⟨5486210, by rfl⟩ : syracuseStep 7314947 = 10972421) B10972421
theorem B4876631 : Blo 2165435 4876631 := bstep (se 1 (by rfl) ⟨3657473, by rfl⟩ : syracuseStep 4876631 = 7314947) B7314947
theorem B3251087 : Blo 2165435 3251087 := bstep (se 1 (by rfl) ⟨2438315, by rfl⟩ : syracuseStep 3251087 = 4876631) B4876631
theorem B2167391 : Blo 2165435 2167391 := bstep (se 1 (by rfl) ⟨1625543, by rfl⟩ : syracuseStep 2167391 = 3251087) B3251087
theorem B3251093 : Blo 2165435 3251093 := bbase (se 6 (by rfl) ⟨76197, by rfl⟩ : syracuseStep 3251093 = 152395) (by norm_num)
theorem B2167395 : Blo 2165435 2167395 := bstep (se 1 (by rfl) ⟨1625546, by rfl⟩ : syracuseStep 2167395 = 3251093) B3251093
theorem B12344021 : Blo 2165435 12344021 := bbase (se 7 (by rfl) ⟨144656, by rfl⟩ : syracuseStep 12344021 = 289313) (by norm_num)
theorem B8229347 : Blo 2165435 8229347 := bstep (se 1 (by rfl) ⟨6172010, by rfl⟩ : syracuseStep 8229347 = 12344021) B12344021
theorem B5486231 : Blo 2165435 5486231 := bstep (se 1 (by rfl) ⟨4114673, by rfl⟩ : syracuseStep 5486231 = 8229347) B8229347
theorem B3657487 : Blo 2165435 3657487 := bstep (se 1 (by rfl) ⟨2743115, by rfl⟩ : syracuseStep 3657487 = 5486231) B5486231
theorem B4876649 : Blo 2165435 4876649 := bstep (se 2 (by rfl) ⟨1828743, by rfl⟩ : syracuseStep 4876649 = 3657487) B3657487
theorem B3251099 : Blo 2165435 3251099 := bstep (se 1 (by rfl) ⟨2438324, by rfl⟩ : syracuseStep 3251099 = 4876649) B4876649
theorem B2167399 : Blo 2165435 2167399 := bstep (se 1 (by rfl) ⟨1625549, by rfl⟩ : syracuseStep 2167399 = 3251099) B3251099
theorem B2438329 : Blo 2165435 2438329 := bbase (se 2 (by rfl) ⟨914373, by rfl⟩ : syracuseStep 2438329 = 1828747) (by norm_num)
theorem B3251105 : Blo 2165435 3251105 := bstep (se 2 (by rfl) ⟨1219164, by rfl⟩ : syracuseStep 3251105 = 2438329) B2438329
theorem B2167403 : Blo 2165435 2167403 := bstep (se 1 (by rfl) ⟨1625552, by rfl⟩ : syracuseStep 2167403 = 3251105) B3251105
theorem B3905741 : Blo 2165435 3905741 := bbase (se 3 (by rfl) ⟨732326, by rfl⟩ : syracuseStep 3905741 = 1464653) (by norm_num)
theorem B2603827 : Blo 2165435 2603827 := bstep (se 1 (by rfl) ⟨1952870, by rfl⟩ : syracuseStep 2603827 = 3905741) B3905741
theorem B3471769 : Blo 2165435 3471769 := bstep (se 2 (by rfl) ⟨1301913, by rfl⟩ : syracuseStep 3471769 = 2603827) B2603827
theorem B4629025 : Blo 2165435 4629025 := bstep (se 2 (by rfl) ⟨1735884, by rfl⟩ : syracuseStep 4629025 = 3471769) B3471769
theorem B6172033 : Blo 2165435 6172033 := bstep (se 2 (by rfl) ⟨2314512, by rfl⟩ : syracuseStep 6172033 = 4629025) B4629025
theorem B8229377 : Blo 2165435 8229377 := bstep (se 2 (by rfl) ⟨3086016, by rfl⟩ : syracuseStep 8229377 = 6172033) B6172033
theorem B5486251 : Blo 2165435 5486251 := bstep (se 1 (by rfl) ⟨4114688, by rfl⟩ : syracuseStep 5486251 = 8229377) B8229377
theorem B7315001 : Blo 2165435 7315001 := bstep (se 2 (by rfl) ⟨2743125, by rfl⟩ : syracuseStep 7315001 = 5486251) B5486251
theorem B4876667 : Blo 2165435 4876667 := bstep (se 1 (by rfl) ⟨3657500, by rfl⟩ : syracuseStep 4876667 = 7315001) B7315001
theorem B3251111 : Blo 2165435 3251111 := bstep (se 1 (by rfl) ⟨2438333, by rfl⟩ : syracuseStep 3251111 = 4876667) B4876667
theorem B2167407 : Blo 2165435 2167407 := bstep (se 1 (by rfl) ⟨1625555, by rfl⟩ : syracuseStep 2167407 = 3251111) B3251111
theorem B3251117 : Blo 2165435 3251117 := bbase (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) (by norm_num)
theorem B2167411 : Blo 2165435 2167411 := bstep (se 1 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 2167411 = 3251117) B3251117
theorem B4876685 : Blo 2165435 4876685 := bbase (se 3 (by rfl) ⟨914378, by rfl⟩ : syracuseStep 4876685 = 1828757) (by norm_num)
theorem B3251123 : Blo 2165435 3251123 := bstep (se 1 (by rfl) ⟨2438342, by rfl⟩ : syracuseStep 3251123 = 4876685) B4876685
theorem B2167415 : Blo 2165435 2167415 := bstep (se 1 (by rfl) ⟨1625561, by rfl⟩ : syracuseStep 2167415 = 3251123) B3251123
theorem B2743141 : Blo 2165435 2743141 := bbase (se 4 (by rfl) ⟨257169, by rfl⟩ : syracuseStep 2743141 = 514339) (by norm_num)
theorem B3657521 : Blo 2165435 3657521 := bstep (se 2 (by rfl) ⟨1371570, by rfl⟩ : syracuseStep 3657521 = 2743141) B2743141
theorem B2438347 : Blo 2165435 2438347 := bstep (se 1 (by rfl) ⟨1828760, by rfl⟩ : syracuseStep 2438347 = 3657521) B3657521
theorem B3251129 : Blo 2165435 3251129 := bstep (se 2 (by rfl) ⟨1219173, by rfl⟩ : syracuseStep 3251129 = 2438347) B2438347
theorem B2167419 : Blo 2165435 2167419 := bstep (se 1 (by rfl) ⟨1625564, by rfl⟩ : syracuseStep 2167419 = 3251129) B3251129
theorem B3295493 : Blo 2165435 3295493 := bbase (se 4 (by rfl) ⟨308952, by rfl⟩ : syracuseStep 3295493 = 617905) (by norm_num)
theorem B2196995 : Blo 2165435 2196995 := bstep (se 1 (by rfl) ⟨1647746, by rfl⟩ : syracuseStep 2196995 = 3295493) B3295493
theorem B5858653 : Blo 2165435 5858653 := bstep (se 3 (by rfl) ⟨1098497, by rfl⟩ : syracuseStep 5858653 = 2196995) B2196995
theorem B7811537 : Blo 2165435 7811537 := bstep (se 2 (by rfl) ⟨2929326, by rfl⟩ : syracuseStep 7811537 = 5858653) B5858653
theorem B20830765 : Blo 2165435 20830765 := bstep (se 3 (by rfl) ⟨3905768, by rfl⟩ : syracuseStep 20830765 = 7811537) B7811537
theorem B27774353 : Blo 2165435 27774353 := bstep (se 2 (by rfl) ⟨10415382, by rfl⟩ : syracuseStep 27774353 = 20830765) B20830765
theorem B18516235 : Blo 2165435 18516235 := bstep (se 1 (by rfl) ⟨13887176, by rfl⟩ : syracuseStep 18516235 = 27774353) B27774353
theorem B24688313 : Blo 2165435 24688313 := bstep (se 2 (by rfl) ⟨9258117, by rfl⟩ : syracuseStep 24688313 = 18516235) B18516235
theorem B16458875 : Blo 2165435 16458875 := bstep (se 1 (by rfl) ⟨12344156, by rfl⟩ : syracuseStep 16458875 = 24688313) B24688313
theorem B10972583 : Blo 2165435 10972583 := bstep (se 1 (by rfl) ⟨8229437, by rfl⟩ : syracuseStep 10972583 = 16458875) B16458875
theorem B7315055 : Blo 2165435 7315055 := bstep (se 1 (by rfl) ⟨5486291, by rfl⟩ : syracuseStep 7315055 = 10972583) B10972583
theorem B4876703 : Blo 2165435 4876703 := bstep (se 1 (by rfl) ⟨3657527, by rfl⟩ : syracuseStep 4876703 = 7315055) B7315055
theorem B3251135 : Blo 2165435 3251135 := bstep (se 1 (by rfl) ⟨2438351, by rfl⟩ : syracuseStep 3251135 = 4876703) B4876703
theorem B2167423 : Blo 2165435 2167423 := bstep (se 1 (by rfl) ⟨1625567, by rfl⟩ : syracuseStep 2167423 = 3251135) B3251135
theorem B3251141 : Blo 2165435 3251141 := bbase (se 4 (by rfl) ⟨304794, by rfl⟩ : syracuseStep 3251141 = 609589) (by norm_num)
theorem B2167427 : Blo 2165435 2167427 := bstep (se 1 (by rfl) ⟨1625570, by rfl⟩ : syracuseStep 2167427 = 3251141) B3251141
theorem B3657541 : Blo 2165435 3657541 := bbase (se 4 (by rfl) ⟨342894, by rfl⟩ : syracuseStep 3657541 = 685789) (by norm_num)
theorem B4876721 : Blo 2165435 4876721 := bstep (se 2 (by rfl) ⟨1828770, by rfl⟩ : syracuseStep 4876721 = 3657541) B3657541
theorem B3251147 : Blo 2165435 3251147 := bstep (se 1 (by rfl) ⟨2438360, by rfl⟩ : syracuseStep 3251147 = 4876721) B4876721
theorem B2167431 : Blo 2165435 2167431 := bstep (se 1 (by rfl) ⟨1625573, by rfl⟩ : syracuseStep 2167431 = 3251147) B3251147
theorem B2438365 : Blo 2165435 2438365 := bbase (se 3 (by rfl) ⟨457193, by rfl⟩ : syracuseStep 2438365 = 914387) (by norm_num)
theorem B3251153 : Blo 2165435 3251153 := bstep (se 2 (by rfl) ⟨1219182, by rfl⟩ : syracuseStep 3251153 = 2438365) B2438365
theorem B2167435 : Blo 2165435 2167435 := bstep (se 1 (by rfl) ⟨1625576, by rfl⟩ : syracuseStep 2167435 = 3251153) B3251153
theorem C0 (j : ℕ) (h1 : 541358 ≤ j) (h2 : j ≤ 541858) : Blo 2165435 (4 * j + 3) := by
  interval_cases j
  · exact B2165435
  · exact B2165439
  · exact B2165443
  · exact B2165447
  · exact B2165451
  · exact B2165455
  · exact B2165459
  · exact B2165463
  · exact B2165467
  · exact B2165471
  · exact B2165475
  · exact B2165479
  · exact B2165483
  · exact B2165487
  · exact B2165491
  · exact B2165495
  · exact B2165499
  · exact B2165503
  · exact B2165507
  · exact B2165511
  · exact B2165515
  · exact B2165519
  · exact B2165523
  · exact B2165527
  · exact B2165531
  · exact B2165535
  · exact B2165539
  · exact B2165543
  · exact B2165547
  · exact B2165551
  · exact B2165555
  · exact B2165559
  · exact B2165563
  · exact B2165567
  · exact B2165571
  · exact B2165575
  · exact B2165579
  · exact B2165583
  · exact B2165587
  · exact B2165591
  · exact B2165595
  · exact B2165599
  · exact B2165603
  · exact B2165607
  · exact B2165611
  · exact B2165615
  · exact B2165619
  · exact B2165623
  · exact B2165627
  · exact B2165631
  · exact B2165635
  · exact B2165639
  · exact B2165643
  · exact B2165647
  · exact B2165651
  · exact B2165655
  · exact B2165659
  · exact B2165663
  · exact B2165667
  · exact B2165671
  · exact B2165675
  · exact B2165679
  · exact B2165683
  · exact B2165687
  · exact B2165691
  · exact B2165695
  · exact B2165699
  · exact B2165703
  · exact B2165707
  · exact B2165711
  · exact B2165715
  · exact B2165719
  · exact B2165723
  · exact B2165727
  · exact B2165731
  · exact B2165735
  · exact B2165739
  · exact B2165743
  · exact B2165747
  · exact B2165751
  · exact B2165755
  · exact B2165759
  · exact B2165763
  · exact B2165767
  · exact B2165771
  · exact B2165775
  · exact B2165779
  · exact B2165783
  · exact B2165787
  · exact B2165791
  · exact B2165795
  · exact B2165799
  · exact B2165803
  · exact B2165807
  · exact B2165811
  · exact B2165815
  · exact B2165819
  · exact B2165823
  · exact B2165827
  · exact B2165831
  · exact B2165835
  · exact B2165839
  · exact B2165843
  · exact B2165847
  · exact B2165851
  · exact B2165855
  · exact B2165859
  · exact B2165863
  · exact B2165867
  · exact B2165871
  · exact B2165875
  · exact B2165879
  · exact B2165883
  · exact B2165887
  · exact B2165891
  · exact B2165895
  · exact B2165899
  · exact B2165903
  · exact B2165907
  · exact B2165911
  · exact B2165915
  · exact B2165919
  · exact B2165923
  · exact B2165927
  · exact B2165931
  · exact B2165935
  · exact B2165939
  · exact B2165943
  · exact B2165947
  · exact B2165951
  · exact B2165955
  · exact B2165959
  · exact B2165963
  · exact B2165967
  · exact B2165971
  · exact B2165975
  · exact B2165979
  · exact B2165983
  · exact B2165987
  · exact B2165991
  · exact B2165995
  · exact B2165999
  · exact B2166003
  · exact B2166007
  · exact B2166011
  · exact B2166015
  · exact B2166019
  · exact B2166023
  · exact B2166027
  · exact B2166031
  · exact B2166035
  · exact B2166039
  · exact B2166043
  · exact B2166047
  · exact B2166051
  · exact B2166055
  · exact B2166059
  · exact B2166063
  · exact B2166067
  · exact B2166071
  · exact B2166075
  · exact B2166079
  · exact B2166083
  · exact B2166087
  · exact B2166091
  · exact B2166095
  · exact B2166099
  · exact B2166103
  · exact B2166107
  · exact B2166111
  · exact B2166115
  · exact B2166119
  · exact B2166123
  · exact B2166127
  · exact B2166131
  · exact B2166135
  · exact B2166139
  · exact B2166143
  · exact B2166147
  · exact B2166151
  · exact B2166155
  · exact B2166159
  · exact B2166163
  · exact B2166167
  · exact B2166171
  · exact B2166175
  · exact B2166179
  · exact B2166183
  · exact B2166187
  · exact B2166191
  · exact B2166195
  · exact B2166199
  · exact B2166203
  · exact B2166207
  · exact B2166211
  · exact B2166215
  · exact B2166219
  · exact B2166223
  · exact B2166227
  · exact B2166231
  · exact B2166235
  · exact B2166239
  · exact B2166243
  · exact B2166247
  · exact B2166251
  · exact B2166255
  · exact B2166259
  · exact B2166263
  · exact B2166267
  · exact B2166271
  · exact B2166275
  · exact B2166279
  · exact B2166283
  · exact B2166287
  · exact B2166291
  · exact B2166295
  · exact B2166299
  · exact B2166303
  · exact B2166307
  · exact B2166311
  · exact B2166315
  · exact B2166319
  · exact B2166323
  · exact B2166327
  · exact B2166331
  · exact B2166335
  · exact B2166339
  · exact B2166343
  · exact B2166347
  · exact B2166351
  · exact B2166355
  · exact B2166359
  · exact B2166363
  · exact B2166367
  · exact B2166371
  · exact B2166375
  · exact B2166379
  · exact B2166383
  · exact B2166387
  · exact B2166391
  · exact B2166395
  · exact B2166399
  · exact B2166403
  · exact B2166407
  · exact B2166411
  · exact B2166415
  · exact B2166419
  · exact B2166423
  · exact B2166427
  · exact B2166431
  · exact B2166435
  · exact B2166439
  · exact B2166443
  · exact B2166447
  · exact B2166451
  · exact B2166455
  · exact B2166459
  · exact B2166463
  · exact B2166467
  · exact B2166471
  · exact B2166475
  · exact B2166479
  · exact B2166483
  · exact B2166487
  · exact B2166491
  · exact B2166495
  · exact B2166499
  · exact B2166503
  · exact B2166507
  · exact B2166511
  · exact B2166515
  · exact B2166519
  · exact B2166523
  · exact B2166527
  · exact B2166531
  · exact B2166535
  · exact B2166539
  · exact B2166543
  · exact B2166547
  · exact B2166551
  · exact B2166555
  · exact B2166559
  · exact B2166563
  · exact B2166567
  · exact B2166571
  · exact B2166575
  · exact B2166579
  · exact B2166583
  · exact B2166587
  · exact B2166591
  · exact B2166595
  · exact B2166599
  · exact B2166603
  · exact B2166607
  · exact B2166611
  · exact B2166615
  · exact B2166619
  · exact B2166623
  · exact B2166627
  · exact B2166631
  · exact B2166635
  · exact B2166639
  · exact B2166643
  · exact B2166647
  · exact B2166651
  · exact B2166655
  · exact B2166659
  · exact B2166663
  · exact B2166667
  · exact B2166671
  · exact B2166675
  · exact B2166679
  · exact B2166683
  · exact B2166687
  · exact B2166691
  · exact B2166695
  · exact B2166699
  · exact B2166703
  · exact B2166707
  · exact B2166711
  · exact B2166715
  · exact B2166719
  · exact B2166723
  · exact B2166727
  · exact B2166731
  · exact B2166735
  · exact B2166739
  · exact B2166743
  · exact B2166747
  · exact B2166751
  · exact B2166755
  · exact B2166759
  · exact B2166763
  · exact B2166767
  · exact B2166771
  · exact B2166775
  · exact B2166779
  · exact B2166783
  · exact B2166787
  · exact B2166791
  · exact B2166795
  · exact B2166799
  · exact B2166803
  · exact B2166807
  · exact B2166811
  · exact B2166815
  · exact B2166819
  · exact B2166823
  · exact B2166827
  · exact B2166831
  · exact B2166835
  · exact B2166839
  · exact B2166843
  · exact B2166847
  · exact B2166851
  · exact B2166855
  · exact B2166859
  · exact B2166863
  · exact B2166867
  · exact B2166871
  · exact B2166875
  · exact B2166879
  · exact B2166883
  · exact B2166887
  · exact B2166891
  · exact B2166895
  · exact B2166899
  · exact B2166903
  · exact B2166907
  · exact B2166911
  · exact B2166915
  · exact B2166919
  · exact B2166923
  · exact B2166927
  · exact B2166931
  · exact B2166935
  · exact B2166939
  · exact B2166943
  · exact B2166947
  · exact B2166951
  · exact B2166955
  · exact B2166959
  · exact B2166963
  · exact B2166967
  · exact B2166971
  · exact B2166975
  · exact B2166979
  · exact B2166983
  · exact B2166987
  · exact B2166991
  · exact B2166995
  · exact B2166999
  · exact B2167003
  · exact B2167007
  · exact B2167011
  · exact B2167015
  · exact B2167019
  · exact B2167023
  · exact B2167027
  · exact B2167031
  · exact B2167035
  · exact B2167039
  · exact B2167043
  · exact B2167047
  · exact B2167051
  · exact B2167055
  · exact B2167059
  · exact B2167063
  · exact B2167067
  · exact B2167071
  · exact B2167075
  · exact B2167079
  · exact B2167083
  · exact B2167087
  · exact B2167091
  · exact B2167095
  · exact B2167099
  · exact B2167103
  · exact B2167107
  · exact B2167111
  · exact B2167115
  · exact B2167119
  · exact B2167123
  · exact B2167127
  · exact B2167131
  · exact B2167135
  · exact B2167139
  · exact B2167143
  · exact B2167147
  · exact B2167151
  · exact B2167155
  · exact B2167159
  · exact B2167163
  · exact B2167167
  · exact B2167171
  · exact B2167175
  · exact B2167179
  · exact B2167183
  · exact B2167187
  · exact B2167191
  · exact B2167195
  · exact B2167199
  · exact B2167203
  · exact B2167207
  · exact B2167211
  · exact B2167215
  · exact B2167219
  · exact B2167223
  · exact B2167227
  · exact B2167231
  · exact B2167235
  · exact B2167239
  · exact B2167243
  · exact B2167247
  · exact B2167251
  · exact B2167255
  · exact B2167259
  · exact B2167263
  · exact B2167267
  · exact B2167271
  · exact B2167275
  · exact B2167279
  · exact B2167283
  · exact B2167287
  · exact B2167291
  · exact B2167295
  · exact B2167299
  · exact B2167303
  · exact B2167307
  · exact B2167311
  · exact B2167315
  · exact B2167319
  · exact B2167323
  · exact B2167327
  · exact B2167331
  · exact B2167335
  · exact B2167339
  · exact B2167343
  · exact B2167347
  · exact B2167351
  · exact B2167355
  · exact B2167359
  · exact B2167363
  · exact B2167367
  · exact B2167371
  · exact B2167375
  · exact B2167379
  · exact B2167383
  · exact B2167387
  · exact B2167391
  · exact B2167395
  · exact B2167399
  · exact B2167403
  · exact B2167407
  · exact B2167411
  · exact B2167415
  · exact B2167419
  · exact B2167423
  · exact B2167427
  · exact B2167431
  · exact B2167435
theorem solution (m : ℕ) (hlo : 2165435 ≤ m) (hhi : m ≤ 2167435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 541358 ≤ j := by omega
    have hj2 : j ≤ 541858 := by omega
    have hb : Blo 2165435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
