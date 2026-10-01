-- Prove2me | solution 1 for syracuse_descends_range_1933435_1935435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:24.502754+00:00
-- url     : https://prove2.me/submissions/d18fda96-8b33-41e5-8c78-d76adce5ebff

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

theorem B2447005 : Blo 1933435 2447005 := bbase (se 3 (by rfl) ⟨458813, by rfl⟩ : syracuseStep 2447005 = 917627) (by norm_num)
theorem B3262673 : Blo 1933435 3262673 := bstep (se 2 (by rfl) ⟨1223502, by rfl⟩ : syracuseStep 3262673 = 2447005) B2447005
theorem B2175115 : Blo 1933435 2175115 := bstep (se 1 (by rfl) ⟨1631336, by rfl⟩ : syracuseStep 2175115 = 3262673) B3262673
theorem B2900153 : Blo 1933435 2900153 := bstep (se 2 (by rfl) ⟨1087557, by rfl⟩ : syracuseStep 2900153 = 2175115) B2175115
theorem B1933435 : Blo 1933435 1933435 := bstep (se 1 (by rfl) ⟨1450076, by rfl⟩ : syracuseStep 1933435 = 2900153) B2900153
theorem B3096997 : Blo 1933435 3096997 := bbase (se 4 (by rfl) ⟨290343, by rfl⟩ : syracuseStep 3096997 = 580687) (by norm_num)
theorem B16517317 : Blo 1933435 16517317 := bstep (se 4 (by rfl) ⟨1548498, by rfl⟩ : syracuseStep 16517317 = 3096997) B3096997
theorem B22023089 : Blo 1933435 22023089 := bstep (se 2 (by rfl) ⟨8258658, by rfl⟩ : syracuseStep 22023089 = 16517317) B16517317
theorem B14682059 : Blo 1933435 14682059 := bstep (se 1 (by rfl) ⟨11011544, by rfl⟩ : syracuseStep 14682059 = 22023089) B22023089
theorem B9788039 : Blo 1933435 9788039 := bstep (se 1 (by rfl) ⟨7341029, by rfl⟩ : syracuseStep 9788039 = 14682059) B14682059
theorem B6525359 : Blo 1933435 6525359 := bstep (se 1 (by rfl) ⟨4894019, by rfl⟩ : syracuseStep 6525359 = 9788039) B9788039
theorem B4350239 : Blo 1933435 4350239 := bstep (se 1 (by rfl) ⟨3262679, by rfl⟩ : syracuseStep 4350239 = 6525359) B6525359
theorem B2900159 : Blo 1933435 2900159 := bstep (se 1 (by rfl) ⟨2175119, by rfl⟩ : syracuseStep 2900159 = 4350239) B4350239
theorem B1933439 : Blo 1933435 1933439 := bstep (se 1 (by rfl) ⟨1450079, by rfl⟩ : syracuseStep 1933439 = 2900159) B2900159
theorem B2900165 : Blo 1933435 2900165 := bbase (se 4 (by rfl) ⟨271890, by rfl⟩ : syracuseStep 2900165 = 543781) (by norm_num)
theorem B1933443 : Blo 1933435 1933443 := bstep (se 1 (by rfl) ⟨1450082, by rfl⟩ : syracuseStep 1933443 = 2900165) B2900165
theorem B3262693 : Blo 1933435 3262693 := bbase (se 4 (by rfl) ⟨305877, by rfl⟩ : syracuseStep 3262693 = 611755) (by norm_num)
theorem B4350257 : Blo 1933435 4350257 := bstep (se 2 (by rfl) ⟨1631346, by rfl⟩ : syracuseStep 4350257 = 3262693) B3262693
theorem B2900171 : Blo 1933435 2900171 := bstep (se 1 (by rfl) ⟨2175128, by rfl⟩ : syracuseStep 2900171 = 4350257) B4350257
theorem B1933447 : Blo 1933435 1933447 := bstep (se 1 (by rfl) ⟨1450085, by rfl⟩ : syracuseStep 1933447 = 2900171) B2900171
theorem B2175133 : Blo 1933435 2175133 := bbase (se 3 (by rfl) ⟨407837, by rfl⟩ : syracuseStep 2175133 = 815675) (by norm_num)
theorem B2900177 : Blo 1933435 2900177 := bstep (se 2 (by rfl) ⟨1087566, by rfl⟩ : syracuseStep 2900177 = 2175133) B2175133
theorem B1933451 : Blo 1933435 1933451 := bstep (se 1 (by rfl) ⟨1450088, by rfl⟩ : syracuseStep 1933451 = 2900177) B2900177
theorem B6525413 : Blo 1933435 6525413 := bbase (se 4 (by rfl) ⟨611757, by rfl⟩ : syracuseStep 6525413 = 1223515) (by norm_num)
theorem B4350275 : Blo 1933435 4350275 := bstep (se 1 (by rfl) ⟨3262706, by rfl⟩ : syracuseStep 4350275 = 6525413) B6525413
theorem B2900183 : Blo 1933435 2900183 := bstep (se 1 (by rfl) ⟨2175137, by rfl⟩ : syracuseStep 2900183 = 4350275) B4350275
theorem B1933455 : Blo 1933435 1933455 := bstep (se 1 (by rfl) ⟨1450091, by rfl⟩ : syracuseStep 1933455 = 2900183) B2900183
theorem B2900189 : Blo 1933435 2900189 := bbase (se 3 (by rfl) ⟨543785, by rfl⟩ : syracuseStep 2900189 = 1087571) (by norm_num)
theorem B1933459 : Blo 1933435 1933459 := bstep (se 1 (by rfl) ⟨1450094, by rfl⟩ : syracuseStep 1933459 = 2900189) B2900189
theorem B4350293 : Blo 1933435 4350293 := bbase (se 10 (by rfl) ⟨6372, by rfl⟩ : syracuseStep 4350293 = 12745) (by norm_num)
theorem B2900195 : Blo 1933435 2900195 := bstep (se 1 (by rfl) ⟨2175146, by rfl⟩ : syracuseStep 2900195 = 4350293) B4350293
theorem B1933463 : Blo 1933435 1933463 := bstep (se 1 (by rfl) ⟨1450097, by rfl⟩ : syracuseStep 1933463 = 2900195) B2900195
theorem B4645565 : Blo 1933435 4645565 := bbase (se 3 (by rfl) ⟨871043, by rfl⟩ : syracuseStep 4645565 = 1742087) (by norm_num)
theorem B3097043 : Blo 1933435 3097043 := bstep (se 1 (by rfl) ⟨2322782, by rfl⟩ : syracuseStep 3097043 = 4645565) B4645565
theorem B2064695 : Blo 1933435 2064695 := bstep (se 1 (by rfl) ⟨1548521, by rfl⟩ : syracuseStep 2064695 = 3097043) B3097043
theorem B5505853 : Blo 1933435 5505853 := bstep (se 3 (by rfl) ⟨1032347, by rfl⟩ : syracuseStep 5505853 = 2064695) B2064695
theorem B7341137 : Blo 1933435 7341137 := bstep (se 2 (by rfl) ⟨2752926, by rfl⟩ : syracuseStep 7341137 = 5505853) B5505853
theorem B4894091 : Blo 1933435 4894091 := bstep (se 1 (by rfl) ⟨3670568, by rfl⟩ : syracuseStep 4894091 = 7341137) B7341137
theorem B3262727 : Blo 1933435 3262727 := bstep (se 1 (by rfl) ⟨2447045, by rfl⟩ : syracuseStep 3262727 = 4894091) B4894091
theorem B2175151 : Blo 1933435 2175151 := bstep (se 1 (by rfl) ⟨1631363, by rfl⟩ : syracuseStep 2175151 = 3262727) B3262727
theorem B2900201 : Blo 1933435 2900201 := bstep (se 2 (by rfl) ⟨1087575, by rfl⟩ : syracuseStep 2900201 = 2175151) B2175151
theorem B1933467 : Blo 1933435 1933467 := bstep (se 1 (by rfl) ⟨1450100, by rfl⟩ : syracuseStep 1933467 = 2900201) B2900201
theorem B2480437 : Blo 1933435 2480437 := bbase (se 5 (by rfl) ⟨116270, by rfl⟩ : syracuseStep 2480437 = 232541) (by norm_num)
theorem B3307249 : Blo 1933435 3307249 := bstep (se 2 (by rfl) ⟨1240218, by rfl⟩ : syracuseStep 3307249 = 2480437) B2480437
theorem B17638661 : Blo 1933435 17638661 := bstep (se 4 (by rfl) ⟨1653624, by rfl⟩ : syracuseStep 17638661 = 3307249) B3307249
theorem B11759107 : Blo 1933435 11759107 := bstep (se 1 (by rfl) ⟨8819330, by rfl⟩ : syracuseStep 11759107 = 17638661) B17638661
theorem B15678809 : Blo 1933435 15678809 := bstep (se 2 (by rfl) ⟨5879553, by rfl⟩ : syracuseStep 15678809 = 11759107) B11759107
theorem B10452539 : Blo 1933435 10452539 := bstep (se 1 (by rfl) ⟨7839404, by rfl⟩ : syracuseStep 10452539 = 15678809) B15678809
theorem B6968359 : Blo 1933435 6968359 := bstep (se 1 (by rfl) ⟨5226269, by rfl⟩ : syracuseStep 6968359 = 10452539) B10452539
theorem B37164581 : Blo 1933435 37164581 := bstep (se 4 (by rfl) ⟨3484179, by rfl⟩ : syracuseStep 37164581 = 6968359) B6968359
theorem B24776387 : Blo 1933435 24776387 := bstep (se 1 (by rfl) ⟨18582290, by rfl⟩ : syracuseStep 24776387 = 37164581) B37164581
theorem B16517591 : Blo 1933435 16517591 := bstep (se 1 (by rfl) ⟨12388193, by rfl⟩ : syracuseStep 16517591 = 24776387) B24776387
theorem B11011727 : Blo 1933435 11011727 := bstep (se 1 (by rfl) ⟨8258795, by rfl⟩ : syracuseStep 11011727 = 16517591) B16517591
theorem B7341151 : Blo 1933435 7341151 := bstep (se 1 (by rfl) ⟨5505863, by rfl⟩ : syracuseStep 7341151 = 11011727) B11011727
theorem B9788201 : Blo 1933435 9788201 := bstep (se 2 (by rfl) ⟨3670575, by rfl⟩ : syracuseStep 9788201 = 7341151) B7341151
theorem B6525467 : Blo 1933435 6525467 := bstep (se 1 (by rfl) ⟨4894100, by rfl⟩ : syracuseStep 6525467 = 9788201) B9788201
theorem B4350311 : Blo 1933435 4350311 := bstep (se 1 (by rfl) ⟨3262733, by rfl⟩ : syracuseStep 4350311 = 6525467) B6525467
theorem B2900207 : Blo 1933435 2900207 := bstep (se 1 (by rfl) ⟨2175155, by rfl⟩ : syracuseStep 2900207 = 4350311) B4350311
theorem B1933471 : Blo 1933435 1933471 := bstep (se 1 (by rfl) ⟨1450103, by rfl⟩ : syracuseStep 1933471 = 2900207) B2900207
theorem B2900213 : Blo 1933435 2900213 := bbase (se 5 (by rfl) ⟨135947, by rfl⟩ : syracuseStep 2900213 = 271895) (by norm_num)
theorem B1933475 : Blo 1933435 1933475 := bstep (se 1 (by rfl) ⟨1450106, by rfl⟩ : syracuseStep 1933475 = 2900213) B2900213
theorem B27873557 : Blo 1933435 27873557 := bbase (se 6 (by rfl) ⟨653286, by rfl⟩ : syracuseStep 27873557 = 1306573) (by norm_num)
theorem B18582371 : Blo 1933435 18582371 := bstep (se 1 (by rfl) ⟨13936778, by rfl⟩ : syracuseStep 18582371 = 27873557) B27873557
theorem B12388247 : Blo 1933435 12388247 := bstep (se 1 (by rfl) ⟨9291185, by rfl⟩ : syracuseStep 12388247 = 18582371) B18582371
theorem B8258831 : Blo 1933435 8258831 := bstep (se 1 (by rfl) ⟨6194123, by rfl⟩ : syracuseStep 8258831 = 12388247) B12388247
theorem B5505887 : Blo 1933435 5505887 := bstep (se 1 (by rfl) ⟨4129415, by rfl⟩ : syracuseStep 5505887 = 8258831) B8258831
theorem B3670591 : Blo 1933435 3670591 := bstep (se 1 (by rfl) ⟨2752943, by rfl⟩ : syracuseStep 3670591 = 5505887) B5505887
theorem B4894121 : Blo 1933435 4894121 := bstep (se 2 (by rfl) ⟨1835295, by rfl⟩ : syracuseStep 4894121 = 3670591) B3670591
theorem B3262747 : Blo 1933435 3262747 := bstep (se 1 (by rfl) ⟨2447060, by rfl⟩ : syracuseStep 3262747 = 4894121) B4894121
theorem B4350329 : Blo 1933435 4350329 := bstep (se 2 (by rfl) ⟨1631373, by rfl⟩ : syracuseStep 4350329 = 3262747) B3262747
theorem B2900219 : Blo 1933435 2900219 := bstep (se 1 (by rfl) ⟨2175164, by rfl⟩ : syracuseStep 2900219 = 4350329) B4350329
theorem B1933479 : Blo 1933435 1933479 := bstep (se 1 (by rfl) ⟨1450109, by rfl⟩ : syracuseStep 1933479 = 2900219) B2900219
theorem B2175169 : Blo 1933435 2175169 := bbase (se 2 (by rfl) ⟨815688, by rfl⟩ : syracuseStep 2175169 = 1631377) (by norm_num)
theorem B2900225 : Blo 1933435 2900225 := bstep (se 2 (by rfl) ⟨1087584, by rfl⟩ : syracuseStep 2900225 = 2175169) B2175169
theorem B1933483 : Blo 1933435 1933483 := bstep (se 1 (by rfl) ⟨1450112, by rfl⟩ : syracuseStep 1933483 = 2900225) B2900225
theorem B4894141 : Blo 1933435 4894141 := bbase (se 3 (by rfl) ⟨917651, by rfl⟩ : syracuseStep 4894141 = 1835303) (by norm_num)
theorem B6525521 : Blo 1933435 6525521 := bstep (se 2 (by rfl) ⟨2447070, by rfl⟩ : syracuseStep 6525521 = 4894141) B4894141
theorem B4350347 : Blo 1933435 4350347 := bstep (se 1 (by rfl) ⟨3262760, by rfl⟩ : syracuseStep 4350347 = 6525521) B6525521
theorem B2900231 : Blo 1933435 2900231 := bstep (se 1 (by rfl) ⟨2175173, by rfl⟩ : syracuseStep 2900231 = 4350347) B4350347
theorem B1933487 : Blo 1933435 1933487 := bstep (se 1 (by rfl) ⟨1450115, by rfl⟩ : syracuseStep 1933487 = 2900231) B2900231
theorem B2900237 : Blo 1933435 2900237 := bbase (se 3 (by rfl) ⟨543794, by rfl⟩ : syracuseStep 2900237 = 1087589) (by norm_num)
theorem B1933491 : Blo 1933435 1933491 := bstep (se 1 (by rfl) ⟨1450118, by rfl⟩ : syracuseStep 1933491 = 2900237) B2900237
theorem B4350365 : Blo 1933435 4350365 := bbase (se 3 (by rfl) ⟨815693, by rfl⟩ : syracuseStep 4350365 = 1631387) (by norm_num)
theorem B2900243 : Blo 1933435 2900243 := bstep (se 1 (by rfl) ⟨2175182, by rfl⟩ : syracuseStep 2900243 = 4350365) B4350365
theorem B1933495 : Blo 1933435 1933495 := bstep (se 1 (by rfl) ⟨1450121, by rfl⟩ : syracuseStep 1933495 = 2900243) B2900243
theorem B3262781 : Blo 1933435 3262781 := bbase (se 3 (by rfl) ⟨611771, by rfl⟩ : syracuseStep 3262781 = 1223543) (by norm_num)
theorem B2175187 : Blo 1933435 2175187 := bstep (se 1 (by rfl) ⟨1631390, by rfl⟩ : syracuseStep 2175187 = 3262781) B3262781
theorem B2900249 : Blo 1933435 2900249 := bstep (se 2 (by rfl) ⟨1087593, by rfl⟩ : syracuseStep 2900249 = 2175187) B2175187
theorem B1933499 : Blo 1933435 1933499 := bstep (se 1 (by rfl) ⟨1450124, by rfl⟩ : syracuseStep 1933499 = 2900249) B2900249
theorem B2064733 : Blo 1933435 2064733 := bbase (se 3 (by rfl) ⟨387137, by rfl⟩ : syracuseStep 2064733 = 774275) (by norm_num)
theorem B11011909 : Blo 1933435 11011909 := bstep (se 4 (by rfl) ⟨1032366, by rfl⟩ : syracuseStep 11011909 = 2064733) B2064733
theorem B14682545 : Blo 1933435 14682545 := bstep (se 2 (by rfl) ⟨5505954, by rfl⟩ : syracuseStep 14682545 = 11011909) B11011909
theorem B9788363 : Blo 1933435 9788363 := bstep (se 1 (by rfl) ⟨7341272, by rfl⟩ : syracuseStep 9788363 = 14682545) B14682545
theorem B6525575 : Blo 1933435 6525575 := bstep (se 1 (by rfl) ⟨4894181, by rfl⟩ : syracuseStep 6525575 = 9788363) B9788363
theorem B4350383 : Blo 1933435 4350383 := bstep (se 1 (by rfl) ⟨3262787, by rfl⟩ : syracuseStep 4350383 = 6525575) B6525575
theorem B2900255 : Blo 1933435 2900255 := bstep (se 1 (by rfl) ⟨2175191, by rfl⟩ : syracuseStep 2900255 = 4350383) B4350383
theorem B1933503 : Blo 1933435 1933503 := bstep (se 1 (by rfl) ⟨1450127, by rfl⟩ : syracuseStep 1933503 = 2900255) B2900255
theorem B2900261 : Blo 1933435 2900261 := bbase (se 4 (by rfl) ⟨271899, by rfl⟩ : syracuseStep 2900261 = 543799) (by norm_num)
theorem B1933507 : Blo 1933435 1933507 := bstep (se 1 (by rfl) ⟨1450130, by rfl⟩ : syracuseStep 1933507 = 2900261) B2900261
theorem B2447101 : Blo 1933435 2447101 := bbase (se 3 (by rfl) ⟨458831, by rfl⟩ : syracuseStep 2447101 = 917663) (by norm_num)
theorem B3262801 : Blo 1933435 3262801 := bstep (se 2 (by rfl) ⟨1223550, by rfl⟩ : syracuseStep 3262801 = 2447101) B2447101
theorem B4350401 : Blo 1933435 4350401 := bstep (se 2 (by rfl) ⟨1631400, by rfl⟩ : syracuseStep 4350401 = 3262801) B3262801
theorem B2900267 : Blo 1933435 2900267 := bstep (se 1 (by rfl) ⟨2175200, by rfl⟩ : syracuseStep 2900267 = 4350401) B4350401
theorem B1933511 : Blo 1933435 1933511 := bstep (se 1 (by rfl) ⟨1450133, by rfl⟩ : syracuseStep 1933511 = 2900267) B2900267
theorem B2175205 : Blo 1933435 2175205 := bbase (se 4 (by rfl) ⟨203925, by rfl⟩ : syracuseStep 2175205 = 407851) (by norm_num)
theorem B2900273 : Blo 1933435 2900273 := bstep (se 2 (by rfl) ⟨1087602, by rfl⟩ : syracuseStep 2900273 = 2175205) B2175205
theorem B1933515 : Blo 1933435 1933515 := bstep (se 1 (by rfl) ⟨1450136, by rfl⟩ : syracuseStep 1933515 = 2900273) B2900273
theorem B4129501 : Blo 1933435 4129501 := bbase (se 3 (by rfl) ⟨774281, by rfl⟩ : syracuseStep 4129501 = 1548563) (by norm_num)
theorem B5506001 : Blo 1933435 5506001 := bstep (se 2 (by rfl) ⟨2064750, by rfl⟩ : syracuseStep 5506001 = 4129501) B4129501
theorem B3670667 : Blo 1933435 3670667 := bstep (se 1 (by rfl) ⟨2753000, by rfl⟩ : syracuseStep 3670667 = 5506001) B5506001
theorem B2447111 : Blo 1933435 2447111 := bstep (se 1 (by rfl) ⟨1835333, by rfl⟩ : syracuseStep 2447111 = 3670667) B3670667
theorem B6525629 : Blo 1933435 6525629 := bstep (se 3 (by rfl) ⟨1223555, by rfl⟩ : syracuseStep 6525629 = 2447111) B2447111
theorem B4350419 : Blo 1933435 4350419 := bstep (se 1 (by rfl) ⟨3262814, by rfl⟩ : syracuseStep 4350419 = 6525629) B6525629
theorem B2900279 : Blo 1933435 2900279 := bstep (se 1 (by rfl) ⟨2175209, by rfl⟩ : syracuseStep 2900279 = 4350419) B4350419
theorem B1933519 : Blo 1933435 1933519 := bstep (se 1 (by rfl) ⟨1450139, by rfl⟩ : syracuseStep 1933519 = 2900279) B2900279
theorem B2900285 : Blo 1933435 2900285 := bbase (se 3 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 2900285 = 1087607) (by norm_num)
theorem B1933523 : Blo 1933435 1933523 := bstep (se 1 (by rfl) ⟨1450142, by rfl⟩ : syracuseStep 1933523 = 2900285) B2900285
theorem B4350437 : Blo 1933435 4350437 := bbase (se 4 (by rfl) ⟨407853, by rfl⟩ : syracuseStep 4350437 = 815707) (by norm_num)
theorem B2900291 : Blo 1933435 2900291 := bstep (se 1 (by rfl) ⟨2175218, by rfl⟩ : syracuseStep 2900291 = 4350437) B4350437
theorem B1933527 : Blo 1933435 1933527 := bstep (se 1 (by rfl) ⟨1450145, by rfl⟩ : syracuseStep 1933527 = 2900291) B2900291
theorem B4894253 : Blo 1933435 4894253 := bbase (se 3 (by rfl) ⟨917672, by rfl⟩ : syracuseStep 4894253 = 1835345) (by norm_num)
theorem B3262835 : Blo 1933435 3262835 := bstep (se 1 (by rfl) ⟨2447126, by rfl⟩ : syracuseStep 3262835 = 4894253) B4894253
theorem B2175223 : Blo 1933435 2175223 := bstep (se 1 (by rfl) ⟨1631417, by rfl⟩ : syracuseStep 2175223 = 3262835) B3262835
theorem B2900297 : Blo 1933435 2900297 := bstep (se 2 (by rfl) ⟨1087611, by rfl⟩ : syracuseStep 2900297 = 2175223) B2175223
theorem B1933531 : Blo 1933435 1933531 := bstep (se 1 (by rfl) ⟨1450148, by rfl⟩ : syracuseStep 1933531 = 2900297) B2900297
theorem B4185877 : Blo 1933435 4185877 := bbase (se 6 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 4185877 = 196213) (by norm_num)
theorem B5581169 : Blo 1933435 5581169 := bstep (se 2 (by rfl) ⟨2092938, by rfl⟩ : syracuseStep 5581169 = 4185877) B4185877
theorem B3720779 : Blo 1933435 3720779 := bstep (se 1 (by rfl) ⟨2790584, by rfl⟩ : syracuseStep 3720779 = 5581169) B5581169
theorem B39688309 : Blo 1933435 39688309 := bstep (se 5 (by rfl) ⟨1860389, by rfl⟩ : syracuseStep 39688309 = 3720779) B3720779
theorem B52917745 : Blo 1933435 52917745 := bstep (se 2 (by rfl) ⟨19844154, by rfl⟩ : syracuseStep 52917745 = 39688309) B39688309
theorem B70556993 : Blo 1933435 70556993 := bstep (se 2 (by rfl) ⟨26458872, by rfl⟩ : syracuseStep 70556993 = 52917745) B52917745
theorem B47037995 : Blo 1933435 47037995 := bstep (se 1 (by rfl) ⟨35278496, by rfl⟩ : syracuseStep 47037995 = 70556993) B70556993
theorem B31358663 : Blo 1933435 31358663 := bstep (se 1 (by rfl) ⟨23518997, by rfl⟩ : syracuseStep 31358663 = 47037995) B47037995
theorem B20905775 : Blo 1933435 20905775 := bstep (se 1 (by rfl) ⟨15679331, by rfl⟩ : syracuseStep 20905775 = 31358663) B31358663
theorem B13937183 : Blo 1933435 13937183 := bstep (se 1 (by rfl) ⟨10452887, by rfl⟩ : syracuseStep 13937183 = 20905775) B20905775
theorem B9291455 : Blo 1933435 9291455 := bstep (se 1 (by rfl) ⟨6968591, by rfl⟩ : syracuseStep 9291455 = 13937183) B13937183
theorem B6194303 : Blo 1933435 6194303 := bstep (se 1 (by rfl) ⟨4645727, by rfl⟩ : syracuseStep 6194303 = 9291455) B9291455
theorem B4129535 : Blo 1933435 4129535 := bstep (se 1 (by rfl) ⟨3097151, by rfl⟩ : syracuseStep 4129535 = 6194303) B6194303
theorem B2753023 : Blo 1933435 2753023 := bstep (se 1 (by rfl) ⟨2064767, by rfl⟩ : syracuseStep 2753023 = 4129535) B4129535
theorem B3670697 : Blo 1933435 3670697 := bstep (se 2 (by rfl) ⟨1376511, by rfl⟩ : syracuseStep 3670697 = 2753023) B2753023
theorem B9788525 : Blo 1933435 9788525 := bstep (se 3 (by rfl) ⟨1835348, by rfl⟩ : syracuseStep 9788525 = 3670697) B3670697
theorem B6525683 : Blo 1933435 6525683 := bstep (se 1 (by rfl) ⟨4894262, by rfl⟩ : syracuseStep 6525683 = 9788525) B9788525
theorem B4350455 : Blo 1933435 4350455 := bstep (se 1 (by rfl) ⟨3262841, by rfl⟩ : syracuseStep 4350455 = 6525683) B6525683
theorem B2900303 : Blo 1933435 2900303 := bstep (se 1 (by rfl) ⟨2175227, by rfl⟩ : syracuseStep 2900303 = 4350455) B4350455
theorem B1933535 : Blo 1933435 1933535 := bstep (se 1 (by rfl) ⟨1450151, by rfl⟩ : syracuseStep 1933535 = 2900303) B2900303
theorem B2900309 : Blo 1933435 2900309 := bbase (se 10 (by rfl) ⟨4248, by rfl⟩ : syracuseStep 2900309 = 8497) (by norm_num)
theorem B1933539 : Blo 1933435 1933539 := bstep (se 1 (by rfl) ⟨1450154, by rfl⟩ : syracuseStep 1933539 = 2900309) B2900309
theorem B5506069 : Blo 1933435 5506069 := bbase (se 6 (by rfl) ⟨129048, by rfl⟩ : syracuseStep 5506069 = 258097) (by norm_num)
theorem B7341425 : Blo 1933435 7341425 := bstep (se 2 (by rfl) ⟨2753034, by rfl⟩ : syracuseStep 7341425 = 5506069) B5506069
theorem B4894283 : Blo 1933435 4894283 := bstep (se 1 (by rfl) ⟨3670712, by rfl⟩ : syracuseStep 4894283 = 7341425) B7341425
theorem B3262855 : Blo 1933435 3262855 := bstep (se 1 (by rfl) ⟨2447141, by rfl⟩ : syracuseStep 3262855 = 4894283) B4894283
theorem B4350473 : Blo 1933435 4350473 := bstep (se 2 (by rfl) ⟨1631427, by rfl⟩ : syracuseStep 4350473 = 3262855) B3262855
theorem B2900315 : Blo 1933435 2900315 := bstep (se 1 (by rfl) ⟨2175236, by rfl⟩ : syracuseStep 2900315 = 4350473) B4350473
theorem B1933543 : Blo 1933435 1933543 := bstep (se 1 (by rfl) ⟨1450157, by rfl⟩ : syracuseStep 1933543 = 2900315) B2900315
theorem B2175241 : Blo 1933435 2175241 := bbase (se 2 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 2175241 = 1631431) (by norm_num)
theorem B2900321 : Blo 1933435 2900321 := bstep (se 2 (by rfl) ⟨1087620, by rfl⟩ : syracuseStep 2900321 = 2175241) B2175241
theorem B1933547 : Blo 1933435 1933547 := bstep (se 1 (by rfl) ⟨1450160, by rfl⟩ : syracuseStep 1933547 = 2900321) B2900321
theorem B4645765 : Blo 1933435 4645765 := bbase (se 4 (by rfl) ⟨435540, by rfl⟩ : syracuseStep 4645765 = 871081) (by norm_num)
theorem B24777413 : Blo 1933435 24777413 := bstep (se 4 (by rfl) ⟨2322882, by rfl⟩ : syracuseStep 24777413 = 4645765) B4645765
theorem B16518275 : Blo 1933435 16518275 := bstep (se 1 (by rfl) ⟨12388706, by rfl⟩ : syracuseStep 16518275 = 24777413) B24777413
theorem B11012183 : Blo 1933435 11012183 := bstep (se 1 (by rfl) ⟨8259137, by rfl⟩ : syracuseStep 11012183 = 16518275) B16518275
theorem B7341455 : Blo 1933435 7341455 := bstep (se 1 (by rfl) ⟨5506091, by rfl⟩ : syracuseStep 7341455 = 11012183) B11012183
theorem B4894303 : Blo 1933435 4894303 := bstep (se 1 (by rfl) ⟨3670727, by rfl⟩ : syracuseStep 4894303 = 7341455) B7341455
theorem B6525737 : Blo 1933435 6525737 := bstep (se 2 (by rfl) ⟨2447151, by rfl⟩ : syracuseStep 6525737 = 4894303) B4894303
theorem B4350491 : Blo 1933435 4350491 := bstep (se 1 (by rfl) ⟨3262868, by rfl⟩ : syracuseStep 4350491 = 6525737) B6525737
theorem B2900327 : Blo 1933435 2900327 := bstep (se 1 (by rfl) ⟨2175245, by rfl⟩ : syracuseStep 2900327 = 4350491) B4350491
theorem B1933551 : Blo 1933435 1933551 := bstep (se 1 (by rfl) ⟨1450163, by rfl⟩ : syracuseStep 1933551 = 2900327) B2900327
theorem B2900333 : Blo 1933435 2900333 := bbase (se 3 (by rfl) ⟨543812, by rfl⟩ : syracuseStep 2900333 = 1087625) (by norm_num)
theorem B1933555 : Blo 1933435 1933555 := bstep (se 1 (by rfl) ⟨1450166, by rfl⟩ : syracuseStep 1933555 = 2900333) B2900333
theorem B4350509 : Blo 1933435 4350509 := bbase (se 3 (by rfl) ⟨815720, by rfl⟩ : syracuseStep 4350509 = 1631441) (by norm_num)
theorem B2900339 : Blo 1933435 2900339 := bstep (se 1 (by rfl) ⟨2175254, by rfl⟩ : syracuseStep 2900339 = 4350509) B4350509
theorem B1933559 : Blo 1933435 1933559 := bstep (se 1 (by rfl) ⟨1450169, by rfl⟩ : syracuseStep 1933559 = 2900339) B2900339
theorem B6968693 : Blo 1933435 6968693 := bbase (se 5 (by rfl) ⟨326657, by rfl⟩ : syracuseStep 6968693 = 653315) (by norm_num)
theorem B18583181 : Blo 1933435 18583181 := bstep (se 3 (by rfl) ⟨3484346, by rfl⟩ : syracuseStep 18583181 = 6968693) B6968693
theorem B12388787 : Blo 1933435 12388787 := bstep (se 1 (by rfl) ⟨9291590, by rfl⟩ : syracuseStep 12388787 = 18583181) B18583181
theorem B8259191 : Blo 1933435 8259191 := bstep (se 1 (by rfl) ⟨6194393, by rfl⟩ : syracuseStep 8259191 = 12388787) B12388787
theorem B5506127 : Blo 1933435 5506127 := bstep (se 1 (by rfl) ⟨4129595, by rfl⟩ : syracuseStep 5506127 = 8259191) B8259191
theorem B3670751 : Blo 1933435 3670751 := bstep (se 1 (by rfl) ⟨2753063, by rfl⟩ : syracuseStep 3670751 = 5506127) B5506127
theorem B2447167 : Blo 1933435 2447167 := bstep (se 1 (by rfl) ⟨1835375, by rfl⟩ : syracuseStep 2447167 = 3670751) B3670751
theorem B3262889 : Blo 1933435 3262889 := bstep (se 2 (by rfl) ⟨1223583, by rfl⟩ : syracuseStep 3262889 = 2447167) B2447167
theorem B2175259 : Blo 1933435 2175259 := bstep (se 1 (by rfl) ⟨1631444, by rfl⟩ : syracuseStep 2175259 = 3262889) B3262889
theorem B2900345 : Blo 1933435 2900345 := bstep (se 2 (by rfl) ⟨1087629, by rfl⟩ : syracuseStep 2900345 = 2175259) B2175259
theorem B1933563 : Blo 1933435 1933563 := bstep (se 1 (by rfl) ⟨1450172, by rfl⟩ : syracuseStep 1933563 = 2900345) B2900345
theorem B33036821 : Blo 1933435 33036821 := bbase (se 6 (by rfl) ⟨774300, by rfl⟩ : syracuseStep 33036821 = 1548601) (by norm_num)
theorem B22024547 : Blo 1933435 22024547 := bstep (se 1 (by rfl) ⟨16518410, by rfl⟩ : syracuseStep 22024547 = 33036821) B33036821
theorem B14683031 : Blo 1933435 14683031 := bstep (se 1 (by rfl) ⟨11012273, by rfl⟩ : syracuseStep 14683031 = 22024547) B22024547
theorem B9788687 : Blo 1933435 9788687 := bstep (se 1 (by rfl) ⟨7341515, by rfl⟩ : syracuseStep 9788687 = 14683031) B14683031
theorem B6525791 : Blo 1933435 6525791 := bstep (se 1 (by rfl) ⟨4894343, by rfl⟩ : syracuseStep 6525791 = 9788687) B9788687
theorem B4350527 : Blo 1933435 4350527 := bstep (se 1 (by rfl) ⟨3262895, by rfl⟩ : syracuseStep 4350527 = 6525791) B6525791
theorem B2900351 : Blo 1933435 2900351 := bstep (se 1 (by rfl) ⟨2175263, by rfl⟩ : syracuseStep 2900351 = 4350527) B4350527
theorem B1933567 : Blo 1933435 1933567 := bstep (se 1 (by rfl) ⟨1450175, by rfl⟩ : syracuseStep 1933567 = 2900351) B2900351
theorem B2900357 : Blo 1933435 2900357 := bbase (se 4 (by rfl) ⟨271908, by rfl⟩ : syracuseStep 2900357 = 543817) (by norm_num)
theorem B1933571 : Blo 1933435 1933571 := bstep (se 1 (by rfl) ⟨1450178, by rfl⟩ : syracuseStep 1933571 = 2900357) B2900357
theorem B3262909 : Blo 1933435 3262909 := bbase (se 3 (by rfl) ⟨611795, by rfl⟩ : syracuseStep 3262909 = 1223591) (by norm_num)
theorem B4350545 : Blo 1933435 4350545 := bstep (se 2 (by rfl) ⟨1631454, by rfl⟩ : syracuseStep 4350545 = 3262909) B3262909
theorem B2900363 : Blo 1933435 2900363 := bstep (se 1 (by rfl) ⟨2175272, by rfl⟩ : syracuseStep 2900363 = 4350545) B4350545
theorem B1933575 : Blo 1933435 1933575 := bstep (se 1 (by rfl) ⟨1450181, by rfl⟩ : syracuseStep 1933575 = 2900363) B2900363
theorem B2175277 : Blo 1933435 2175277 := bbase (se 3 (by rfl) ⟨407864, by rfl⟩ : syracuseStep 2175277 = 815729) (by norm_num)
theorem B2900369 : Blo 1933435 2900369 := bstep (se 2 (by rfl) ⟨1087638, by rfl⟩ : syracuseStep 2900369 = 2175277) B2175277
theorem B1933579 : Blo 1933435 1933579 := bstep (se 1 (by rfl) ⟨1450184, by rfl⟩ : syracuseStep 1933579 = 2900369) B2900369
theorem B6525845 : Blo 1933435 6525845 := bbase (se 6 (by rfl) ⟨152949, by rfl⟩ : syracuseStep 6525845 = 305899) (by norm_num)
theorem B4350563 : Blo 1933435 4350563 := bstep (se 1 (by rfl) ⟨3262922, by rfl⟩ : syracuseStep 4350563 = 6525845) B6525845
theorem B2900375 : Blo 1933435 2900375 := bstep (se 1 (by rfl) ⟨2175281, by rfl⟩ : syracuseStep 2900375 = 4350563) B4350563
theorem B1933583 : Blo 1933435 1933583 := bstep (se 1 (by rfl) ⟨1450187, by rfl⟩ : syracuseStep 1933583 = 2900375) B2900375
theorem B2900381 : Blo 1933435 2900381 := bbase (se 3 (by rfl) ⟨543821, by rfl⟩ : syracuseStep 2900381 = 1087643) (by norm_num)
theorem B1933587 : Blo 1933435 1933587 := bstep (se 1 (by rfl) ⟨1450190, by rfl⟩ : syracuseStep 1933587 = 2900381) B2900381
theorem B4350581 : Blo 1933435 4350581 := bbase (se 5 (by rfl) ⟨203933, by rfl⟩ : syracuseStep 4350581 = 407867) (by norm_num)
theorem B2900387 : Blo 1933435 2900387 := bstep (se 1 (by rfl) ⟨2175290, by rfl⟩ : syracuseStep 2900387 = 4350581) B4350581
theorem B1933591 : Blo 1933435 1933591 := bstep (se 1 (by rfl) ⟨1450193, by rfl⟩ : syracuseStep 1933591 = 2900387) B2900387
theorem B9418517 : Blo 1933435 9418517 := bbase (se 6 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 9418517 = 441493) (by norm_num)
theorem B6279011 : Blo 1933435 6279011 := bstep (se 1 (by rfl) ⟨4709258, by rfl⟩ : syracuseStep 6279011 = 9418517) B9418517
theorem B4186007 : Blo 1933435 4186007 := bstep (se 1 (by rfl) ⟨3139505, by rfl⟩ : syracuseStep 4186007 = 6279011) B6279011
theorem B2790671 : Blo 1933435 2790671 := bstep (se 1 (by rfl) ⟨2093003, by rfl⟩ : syracuseStep 2790671 = 4186007) B4186007
theorem B7441789 : Blo 1933435 7441789 := bstep (se 3 (by rfl) ⟨1395335, by rfl⟩ : syracuseStep 7441789 = 2790671) B2790671
theorem B9922385 : Blo 1933435 9922385 := bstep (se 2 (by rfl) ⟨3720894, by rfl⟩ : syracuseStep 9922385 = 7441789) B7441789
theorem B26459693 : Blo 1933435 26459693 := bstep (se 3 (by rfl) ⟨4961192, by rfl⟩ : syracuseStep 26459693 = 9922385) B9922385
theorem B17639795 : Blo 1933435 17639795 := bstep (se 1 (by rfl) ⟨13229846, by rfl⟩ : syracuseStep 17639795 = 26459693) B26459693
theorem B47039453 : Blo 1933435 47039453 := bstep (se 3 (by rfl) ⟨8819897, by rfl⟩ : syracuseStep 47039453 = 17639795) B17639795
theorem B31359635 : Blo 1933435 31359635 := bstep (se 1 (by rfl) ⟨23519726, by rfl⟩ : syracuseStep 31359635 = 47039453) B47039453
theorem B20906423 : Blo 1933435 20906423 := bstep (se 1 (by rfl) ⟨15679817, by rfl⟩ : syracuseStep 20906423 = 31359635) B31359635
theorem B13937615 : Blo 1933435 13937615 := bstep (se 1 (by rfl) ⟨10453211, by rfl⟩ : syracuseStep 13937615 = 20906423) B20906423
theorem B9291743 : Blo 1933435 9291743 := bstep (se 1 (by rfl) ⟨6968807, by rfl⟩ : syracuseStep 9291743 = 13937615) B13937615
theorem B6194495 : Blo 1933435 6194495 := bstep (se 1 (by rfl) ⟨4645871, by rfl⟩ : syracuseStep 6194495 = 9291743) B9291743
theorem B16518653 : Blo 1933435 16518653 := bstep (se 3 (by rfl) ⟨3097247, by rfl⟩ : syracuseStep 16518653 = 6194495) B6194495
theorem B11012435 : Blo 1933435 11012435 := bstep (se 1 (by rfl) ⟨8259326, by rfl⟩ : syracuseStep 11012435 = 16518653) B16518653
theorem B7341623 : Blo 1933435 7341623 := bstep (se 1 (by rfl) ⟨5506217, by rfl⟩ : syracuseStep 7341623 = 11012435) B11012435
theorem B4894415 : Blo 1933435 4894415 := bstep (se 1 (by rfl) ⟨3670811, by rfl⟩ : syracuseStep 4894415 = 7341623) B7341623
theorem B3262943 : Blo 1933435 3262943 := bstep (se 1 (by rfl) ⟨2447207, by rfl⟩ : syracuseStep 3262943 = 4894415) B4894415
theorem B2175295 : Blo 1933435 2175295 := bstep (se 1 (by rfl) ⟨1631471, by rfl⟩ : syracuseStep 2175295 = 3262943) B3262943
theorem B2900393 : Blo 1933435 2900393 := bstep (se 2 (by rfl) ⟨1087647, by rfl⟩ : syracuseStep 2900393 = 2175295) B2175295
theorem B1933595 : Blo 1933435 1933595 := bstep (se 1 (by rfl) ⟨1450196, by rfl⟩ : syracuseStep 1933595 = 2900393) B2900393
theorem B7341637 : Blo 1933435 7341637 := bbase (se 4 (by rfl) ⟨688278, by rfl⟩ : syracuseStep 7341637 = 1376557) (by norm_num)
theorem B9788849 : Blo 1933435 9788849 := bstep (se 2 (by rfl) ⟨3670818, by rfl⟩ : syracuseStep 9788849 = 7341637) B7341637
theorem B6525899 : Blo 1933435 6525899 := bstep (se 1 (by rfl) ⟨4894424, by rfl⟩ : syracuseStep 6525899 = 9788849) B9788849
theorem B4350599 : Blo 1933435 4350599 := bstep (se 1 (by rfl) ⟨3262949, by rfl⟩ : syracuseStep 4350599 = 6525899) B6525899
theorem B2900399 : Blo 1933435 2900399 := bstep (se 1 (by rfl) ⟨2175299, by rfl⟩ : syracuseStep 2900399 = 4350599) B4350599
theorem B1933599 : Blo 1933435 1933599 := bstep (se 1 (by rfl) ⟨1450199, by rfl⟩ : syracuseStep 1933599 = 2900399) B2900399
theorem B2900405 : Blo 1933435 2900405 := bbase (se 5 (by rfl) ⟨135956, by rfl⟩ : syracuseStep 2900405 = 271913) (by norm_num)
theorem B1933603 : Blo 1933435 1933603 := bstep (se 1 (by rfl) ⟨1450202, by rfl⟩ : syracuseStep 1933603 = 2900405) B2900405
theorem B4894445 : Blo 1933435 4894445 := bbase (se 3 (by rfl) ⟨917708, by rfl⟩ : syracuseStep 4894445 = 1835417) (by norm_num)
theorem B3262963 : Blo 1933435 3262963 := bstep (se 1 (by rfl) ⟨2447222, by rfl⟩ : syracuseStep 3262963 = 4894445) B4894445
theorem B4350617 : Blo 1933435 4350617 := bstep (se 2 (by rfl) ⟨1631481, by rfl⟩ : syracuseStep 4350617 = 3262963) B3262963
theorem B2900411 : Blo 1933435 2900411 := bstep (se 1 (by rfl) ⟨2175308, by rfl⟩ : syracuseStep 2900411 = 4350617) B4350617
theorem B1933607 : Blo 1933435 1933607 := bstep (se 1 (by rfl) ⟨1450205, by rfl⟩ : syracuseStep 1933607 = 2900411) B2900411
theorem B2175313 : Blo 1933435 2175313 := bbase (se 2 (by rfl) ⟨815742, by rfl⟩ : syracuseStep 2175313 = 1631485) (by norm_num)
theorem B2900417 : Blo 1933435 2900417 := bstep (se 2 (by rfl) ⟨1087656, by rfl⟩ : syracuseStep 2900417 = 2175313) B2175313
theorem B1933611 : Blo 1933435 1933611 := bstep (se 1 (by rfl) ⟨1450208, by rfl⟩ : syracuseStep 1933611 = 2900417) B2900417
theorem B2064853 : Blo 1933435 2064853 := bbase (se 7 (by rfl) ⟨24197, by rfl⟩ : syracuseStep 2064853 = 48395) (by norm_num)
theorem B2753137 : Blo 1933435 2753137 := bstep (se 2 (by rfl) ⟨1032426, by rfl⟩ : syracuseStep 2753137 = 2064853) B2064853
theorem B3670849 : Blo 1933435 3670849 := bstep (se 2 (by rfl) ⟨1376568, by rfl⟩ : syracuseStep 3670849 = 2753137) B2753137
theorem B4894465 : Blo 1933435 4894465 := bstep (se 2 (by rfl) ⟨1835424, by rfl⟩ : syracuseStep 4894465 = 3670849) B3670849
theorem B6525953 : Blo 1933435 6525953 := bstep (se 2 (by rfl) ⟨2447232, by rfl⟩ : syracuseStep 6525953 = 4894465) B4894465
theorem B4350635 : Blo 1933435 4350635 := bstep (se 1 (by rfl) ⟨3262976, by rfl⟩ : syracuseStep 4350635 = 6525953) B6525953
theorem B2900423 : Blo 1933435 2900423 := bstep (se 1 (by rfl) ⟨2175317, by rfl⟩ : syracuseStep 2900423 = 4350635) B4350635
theorem B1933615 : Blo 1933435 1933615 := bstep (se 1 (by rfl) ⟨1450211, by rfl⟩ : syracuseStep 1933615 = 2900423) B2900423
theorem B2900429 : Blo 1933435 2900429 := bbase (se 3 (by rfl) ⟨543830, by rfl⟩ : syracuseStep 2900429 = 1087661) (by norm_num)
theorem B1933619 : Blo 1933435 1933619 := bstep (se 1 (by rfl) ⟨1450214, by rfl⟩ : syracuseStep 1933619 = 2900429) B2900429
theorem B4350653 : Blo 1933435 4350653 := bbase (se 3 (by rfl) ⟨815747, by rfl⟩ : syracuseStep 4350653 = 1631495) (by norm_num)
theorem B2900435 : Blo 1933435 2900435 := bstep (se 1 (by rfl) ⟨2175326, by rfl⟩ : syracuseStep 2900435 = 4350653) B4350653
theorem B1933623 : Blo 1933435 1933623 := bstep (se 1 (by rfl) ⟨1450217, by rfl⟩ : syracuseStep 1933623 = 2900435) B2900435
theorem B3262997 : Blo 1933435 3262997 := bbase (se 6 (by rfl) ⟨76476, by rfl⟩ : syracuseStep 3262997 = 152953) (by norm_num)
theorem B2175331 : Blo 1933435 2175331 := bstep (se 1 (by rfl) ⟨1631498, by rfl⟩ : syracuseStep 2175331 = 3262997) B3262997
theorem B2900441 : Blo 1933435 2900441 := bstep (se 2 (by rfl) ⟨1087665, by rfl⟩ : syracuseStep 2900441 = 2175331) B2175331
theorem B1933627 : Blo 1933435 1933627 := bstep (se 1 (by rfl) ⟨1450220, by rfl⟩ : syracuseStep 1933627 = 2900441) B2900441
theorem B18583829 : Blo 1933435 18583829 := bbase (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) (by norm_num)
theorem B12389219 : Blo 1933435 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B8259479 : Blo 1933435 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B5506319 : Blo 1933435 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B14683517 : Blo 1933435 14683517 := bstep (se 3 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 14683517 = 5506319) B5506319
theorem B9789011 : Blo 1933435 9789011 := bstep (se 1 (by rfl) ⟨7341758, by rfl⟩ : syracuseStep 9789011 = 14683517) B14683517
theorem B6526007 : Blo 1933435 6526007 := bstep (se 1 (by rfl) ⟨4894505, by rfl⟩ : syracuseStep 6526007 = 9789011) B9789011
theorem B4350671 : Blo 1933435 4350671 := bstep (se 1 (by rfl) ⟨3263003, by rfl⟩ : syracuseStep 4350671 = 6526007) B6526007
theorem B2900447 : Blo 1933435 2900447 := bstep (se 1 (by rfl) ⟨2175335, by rfl⟩ : syracuseStep 2900447 = 4350671) B4350671
theorem B1933631 : Blo 1933435 1933631 := bstep (se 1 (by rfl) ⟨1450223, by rfl⟩ : syracuseStep 1933631 = 2900447) B2900447
theorem B2900453 : Blo 1933435 2900453 := bbase (se 4 (by rfl) ⟨271917, by rfl⟩ : syracuseStep 2900453 = 543835) (by norm_num)
theorem B1933635 : Blo 1933435 1933635 := bstep (se 1 (by rfl) ⟨1450226, by rfl⟩ : syracuseStep 1933635 = 2900453) B2900453
theorem B5226725 : Blo 1933435 5226725 := bbase (se 4 (by rfl) ⟨490005, by rfl⟩ : syracuseStep 5226725 = 980011) (by norm_num)
theorem B13937933 : Blo 1933435 13937933 := bstep (se 3 (by rfl) ⟨2613362, by rfl⟩ : syracuseStep 13937933 = 5226725) B5226725
theorem B9291955 : Blo 1933435 9291955 := bstep (se 1 (by rfl) ⟨6968966, by rfl⟩ : syracuseStep 9291955 = 13937933) B13937933
theorem B12389273 : Blo 1933435 12389273 := bstep (se 2 (by rfl) ⟨4645977, by rfl⟩ : syracuseStep 12389273 = 9291955) B9291955
theorem B8259515 : Blo 1933435 8259515 := bstep (se 1 (by rfl) ⟨6194636, by rfl⟩ : syracuseStep 8259515 = 12389273) B12389273
theorem B5506343 : Blo 1933435 5506343 := bstep (se 1 (by rfl) ⟨4129757, by rfl⟩ : syracuseStep 5506343 = 8259515) B8259515
theorem B3670895 : Blo 1933435 3670895 := bstep (se 1 (by rfl) ⟨2753171, by rfl⟩ : syracuseStep 3670895 = 5506343) B5506343
theorem B2447263 : Blo 1933435 2447263 := bstep (se 1 (by rfl) ⟨1835447, by rfl⟩ : syracuseStep 2447263 = 3670895) B3670895
theorem B3263017 : Blo 1933435 3263017 := bstep (se 2 (by rfl) ⟨1223631, by rfl⟩ : syracuseStep 3263017 = 2447263) B2447263
theorem B4350689 : Blo 1933435 4350689 := bstep (se 2 (by rfl) ⟨1631508, by rfl⟩ : syracuseStep 4350689 = 3263017) B3263017
theorem B2900459 : Blo 1933435 2900459 := bstep (se 1 (by rfl) ⟨2175344, by rfl⟩ : syracuseStep 2900459 = 4350689) B4350689
theorem B1933639 : Blo 1933435 1933639 := bstep (se 1 (by rfl) ⟨1450229, by rfl⟩ : syracuseStep 1933639 = 2900459) B2900459
theorem B2175349 : Blo 1933435 2175349 := bbase (se 5 (by rfl) ⟨101969, by rfl⟩ : syracuseStep 2175349 = 203939) (by norm_num)
theorem B2900465 : Blo 1933435 2900465 := bstep (se 2 (by rfl) ⟨1087674, by rfl⟩ : syracuseStep 2900465 = 2175349) B2175349
theorem B1933643 : Blo 1933435 1933643 := bstep (se 1 (by rfl) ⟨1450232, by rfl⟩ : syracuseStep 1933643 = 2900465) B2900465
theorem B2447273 : Blo 1933435 2447273 := bbase (se 2 (by rfl) ⟨917727, by rfl⟩ : syracuseStep 2447273 = 1835455) (by norm_num)
theorem B6526061 : Blo 1933435 6526061 := bstep (se 3 (by rfl) ⟨1223636, by rfl⟩ : syracuseStep 6526061 = 2447273) B2447273
theorem B4350707 : Blo 1933435 4350707 := bstep (se 1 (by rfl) ⟨3263030, by rfl⟩ : syracuseStep 4350707 = 6526061) B6526061
theorem B2900471 : Blo 1933435 2900471 := bstep (se 1 (by rfl) ⟨2175353, by rfl⟩ : syracuseStep 2900471 = 4350707) B4350707
theorem B1933647 : Blo 1933435 1933647 := bstep (se 1 (by rfl) ⟨1450235, by rfl⟩ : syracuseStep 1933647 = 2900471) B2900471
theorem B2900477 : Blo 1933435 2900477 := bbase (se 3 (by rfl) ⟨543839, by rfl⟩ : syracuseStep 2900477 = 1087679) (by norm_num)
theorem B1933651 : Blo 1933435 1933651 := bstep (se 1 (by rfl) ⟨1450238, by rfl⟩ : syracuseStep 1933651 = 2900477) B2900477
theorem B4350725 : Blo 1933435 4350725 := bbase (se 4 (by rfl) ⟨407880, by rfl⟩ : syracuseStep 4350725 = 815761) (by norm_num)
theorem B2900483 : Blo 1933435 2900483 := bstep (se 1 (by rfl) ⟨2175362, by rfl⟩ : syracuseStep 2900483 = 4350725) B4350725
theorem B1933655 : Blo 1933435 1933655 := bstep (se 1 (by rfl) ⟨1450241, by rfl⟩ : syracuseStep 1933655 = 2900483) B2900483
theorem B3670933 : Blo 1933435 3670933 := bbase (se 6 (by rfl) ⟨86037, by rfl⟩ : syracuseStep 3670933 = 172075) (by norm_num)
theorem B4894577 : Blo 1933435 4894577 := bstep (se 2 (by rfl) ⟨1835466, by rfl⟩ : syracuseStep 4894577 = 3670933) B3670933
theorem B3263051 : Blo 1933435 3263051 := bstep (se 1 (by rfl) ⟨2447288, by rfl⟩ : syracuseStep 3263051 = 4894577) B4894577
theorem B2175367 : Blo 1933435 2175367 := bstep (se 1 (by rfl) ⟨1631525, by rfl⟩ : syracuseStep 2175367 = 3263051) B3263051
theorem B2900489 : Blo 1933435 2900489 := bstep (se 2 (by rfl) ⟨1087683, by rfl⟩ : syracuseStep 2900489 = 2175367) B2175367
theorem B1933659 : Blo 1933435 1933659 := bstep (se 1 (by rfl) ⟨1450244, by rfl⟩ : syracuseStep 1933659 = 2900489) B2900489
theorem B9789173 : Blo 1933435 9789173 := bbase (se 5 (by rfl) ⟨458867, by rfl⟩ : syracuseStep 9789173 = 917735) (by norm_num)
theorem B6526115 : Blo 1933435 6526115 := bstep (se 1 (by rfl) ⟨4894586, by rfl⟩ : syracuseStep 6526115 = 9789173) B9789173
theorem B4350743 : Blo 1933435 4350743 := bstep (se 1 (by rfl) ⟨3263057, by rfl⟩ : syracuseStep 4350743 = 6526115) B6526115
theorem B2900495 : Blo 1933435 2900495 := bstep (se 1 (by rfl) ⟨2175371, by rfl⟩ : syracuseStep 2900495 = 4350743) B4350743
theorem B1933663 : Blo 1933435 1933663 := bstep (se 1 (by rfl) ⟨1450247, by rfl⟩ : syracuseStep 1933663 = 2900495) B2900495
theorem B2900501 : Blo 1933435 2900501 := bbase (se 6 (by rfl) ⟨67980, by rfl⟩ : syracuseStep 2900501 = 135961) (by norm_num)
theorem B1933667 : Blo 1933435 1933667 := bstep (se 1 (by rfl) ⟨1450250, by rfl⟩ : syracuseStep 1933667 = 2900501) B2900501
theorem B3484541 : Blo 1933435 3484541 := bbase (se 3 (by rfl) ⟨653351, by rfl⟩ : syracuseStep 3484541 = 1306703) (by norm_num)
theorem B2323027 : Blo 1933435 2323027 := bstep (se 1 (by rfl) ⟨1742270, by rfl⟩ : syracuseStep 2323027 = 3484541) B3484541
theorem B3097369 : Blo 1933435 3097369 := bstep (se 2 (by rfl) ⟨1161513, by rfl⟩ : syracuseStep 3097369 = 2323027) B2323027
theorem B16519301 : Blo 1933435 16519301 := bstep (se 4 (by rfl) ⟨1548684, by rfl⟩ : syracuseStep 16519301 = 3097369) B3097369
theorem B11012867 : Blo 1933435 11012867 := bstep (se 1 (by rfl) ⟨8259650, by rfl⟩ : syracuseStep 11012867 = 16519301) B16519301
theorem B7341911 : Blo 1933435 7341911 := bstep (se 1 (by rfl) ⟨5506433, by rfl⟩ : syracuseStep 7341911 = 11012867) B11012867
theorem B4894607 : Blo 1933435 4894607 := bstep (se 1 (by rfl) ⟨3670955, by rfl⟩ : syracuseStep 4894607 = 7341911) B7341911
theorem B3263071 : Blo 1933435 3263071 := bstep (se 1 (by rfl) ⟨2447303, by rfl⟩ : syracuseStep 3263071 = 4894607) B4894607
theorem B4350761 : Blo 1933435 4350761 := bstep (se 2 (by rfl) ⟨1631535, by rfl⟩ : syracuseStep 4350761 = 3263071) B3263071
theorem B2900507 : Blo 1933435 2900507 := bstep (se 1 (by rfl) ⟨2175380, by rfl⟩ : syracuseStep 2900507 = 4350761) B4350761
theorem B1933671 : Blo 1933435 1933671 := bstep (se 1 (by rfl) ⟨1450253, by rfl⟩ : syracuseStep 1933671 = 2900507) B2900507
theorem B2175385 : Blo 1933435 2175385 := bbase (se 2 (by rfl) ⟨815769, by rfl⟩ : syracuseStep 2175385 = 1631539) (by norm_num)
theorem B2900513 : Blo 1933435 2900513 := bstep (se 2 (by rfl) ⟨1087692, by rfl⟩ : syracuseStep 2900513 = 2175385) B2175385
theorem B1933675 : Blo 1933435 1933675 := bstep (se 1 (by rfl) ⟨1450256, by rfl⟩ : syracuseStep 1933675 = 2900513) B2900513
theorem B7341941 : Blo 1933435 7341941 := bbase (se 5 (by rfl) ⟨344153, by rfl⟩ : syracuseStep 7341941 = 688307) (by norm_num)
theorem B4894627 : Blo 1933435 4894627 := bstep (se 1 (by rfl) ⟨3670970, by rfl⟩ : syracuseStep 4894627 = 7341941) B7341941
theorem B6526169 : Blo 1933435 6526169 := bstep (se 2 (by rfl) ⟨2447313, by rfl⟩ : syracuseStep 6526169 = 4894627) B4894627
theorem B4350779 : Blo 1933435 4350779 := bstep (se 1 (by rfl) ⟨3263084, by rfl⟩ : syracuseStep 4350779 = 6526169) B6526169
theorem B2900519 : Blo 1933435 2900519 := bstep (se 1 (by rfl) ⟨2175389, by rfl⟩ : syracuseStep 2900519 = 4350779) B4350779
theorem B1933679 : Blo 1933435 1933679 := bstep (se 1 (by rfl) ⟨1450259, by rfl⟩ : syracuseStep 1933679 = 2900519) B2900519
theorem B2900525 : Blo 1933435 2900525 := bbase (se 3 (by rfl) ⟨543848, by rfl⟩ : syracuseStep 2900525 = 1087697) (by norm_num)
theorem B1933683 : Blo 1933435 1933683 := bstep (se 1 (by rfl) ⟨1450262, by rfl⟩ : syracuseStep 1933683 = 2900525) B2900525
theorem B4350797 : Blo 1933435 4350797 := bbase (se 3 (by rfl) ⟨815774, by rfl⟩ : syracuseStep 4350797 = 1631549) (by norm_num)
theorem B2900531 : Blo 1933435 2900531 := bstep (se 1 (by rfl) ⟨2175398, by rfl⟩ : syracuseStep 2900531 = 4350797) B4350797
theorem B1933687 : Blo 1933435 1933687 := bstep (se 1 (by rfl) ⟨1450265, by rfl⟩ : syracuseStep 1933687 = 2900531) B2900531
theorem B2447329 : Blo 1933435 2447329 := bbase (se 2 (by rfl) ⟨917748, by rfl⟩ : syracuseStep 2447329 = 1835497) (by norm_num)
theorem B3263105 : Blo 1933435 3263105 := bstep (se 2 (by rfl) ⟨1223664, by rfl⟩ : syracuseStep 3263105 = 2447329) B2447329
theorem B2175403 : Blo 1933435 2175403 := bstep (se 1 (by rfl) ⟨1631552, by rfl⟩ : syracuseStep 2175403 = 3263105) B3263105
theorem B2900537 : Blo 1933435 2900537 := bstep (se 2 (by rfl) ⟨1087701, by rfl⟩ : syracuseStep 2900537 = 2175403) B2175403
theorem B1933691 : Blo 1933435 1933691 := bstep (se 1 (by rfl) ⟨1450268, by rfl⟩ : syracuseStep 1933691 = 2900537) B2900537
theorem B22026005 : Blo 1933435 22026005 := bbase (se 6 (by rfl) ⟨516234, by rfl⟩ : syracuseStep 22026005 = 1032469) (by norm_num)
theorem B14684003 : Blo 1933435 14684003 := bstep (se 1 (by rfl) ⟨11013002, by rfl⟩ : syracuseStep 14684003 = 22026005) B22026005
theorem B9789335 : Blo 1933435 9789335 := bstep (se 1 (by rfl) ⟨7342001, by rfl⟩ : syracuseStep 9789335 = 14684003) B14684003
theorem B6526223 : Blo 1933435 6526223 := bstep (se 1 (by rfl) ⟨4894667, by rfl⟩ : syracuseStep 6526223 = 9789335) B9789335
theorem B4350815 : Blo 1933435 4350815 := bstep (se 1 (by rfl) ⟨3263111, by rfl⟩ : syracuseStep 4350815 = 6526223) B6526223
theorem B2900543 : Blo 1933435 2900543 := bstep (se 1 (by rfl) ⟨2175407, by rfl⟩ : syracuseStep 2900543 = 4350815) B4350815
theorem B1933695 : Blo 1933435 1933695 := bstep (se 1 (by rfl) ⟨1450271, by rfl⟩ : syracuseStep 1933695 = 2900543) B2900543
theorem B2900549 : Blo 1933435 2900549 := bbase (se 4 (by rfl) ⟨271926, by rfl⟩ : syracuseStep 2900549 = 543853) (by norm_num)
theorem B1933699 : Blo 1933435 1933699 := bstep (se 1 (by rfl) ⟨1450274, by rfl⟩ : syracuseStep 1933699 = 2900549) B2900549
theorem B3263125 : Blo 1933435 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B4350833 : Blo 1933435 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B2900555 : Blo 1933435 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B1933703 : Blo 1933435 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B2175421 : Blo 1933435 2175421 := bbase (se 3 (by rfl) ⟨407891, by rfl⟩ : syracuseStep 2175421 = 815783) (by norm_num)
theorem B2900561 : Blo 1933435 2900561 := bstep (se 2 (by rfl) ⟨1087710, by rfl⟩ : syracuseStep 2900561 = 2175421) B2175421
theorem B1933707 : Blo 1933435 1933707 := bstep (se 1 (by rfl) ⟨1450280, by rfl⟩ : syracuseStep 1933707 = 2900561) B2900561
theorem B6526277 : Blo 1933435 6526277 := bbase (se 4 (by rfl) ⟨611838, by rfl⟩ : syracuseStep 6526277 = 1223677) (by norm_num)
theorem B4350851 : Blo 1933435 4350851 := bstep (se 1 (by rfl) ⟨3263138, by rfl⟩ : syracuseStep 4350851 = 6526277) B6526277
theorem B2900567 : Blo 1933435 2900567 := bstep (se 1 (by rfl) ⟨2175425, by rfl⟩ : syracuseStep 2900567 = 4350851) B4350851
theorem B1933711 : Blo 1933435 1933711 := bstep (se 1 (by rfl) ⟨1450283, by rfl⟩ : syracuseStep 1933711 = 2900567) B2900567
theorem B2900573 : Blo 1933435 2900573 := bbase (se 3 (by rfl) ⟨543857, by rfl⟩ : syracuseStep 2900573 = 1087715) (by norm_num)
theorem B1933715 : Blo 1933435 1933715 := bstep (se 1 (by rfl) ⟨1450286, by rfl⟩ : syracuseStep 1933715 = 2900573) B2900573
theorem B4350869 : Blo 1933435 4350869 := bbase (se 6 (by rfl) ⟨101973, by rfl⟩ : syracuseStep 4350869 = 203947) (by norm_num)
theorem B2900579 : Blo 1933435 2900579 := bstep (se 1 (by rfl) ⟨2175434, by rfl⟩ : syracuseStep 2900579 = 4350869) B4350869
theorem B1933719 : Blo 1933435 1933719 := bstep (se 1 (by rfl) ⟨1450289, by rfl⟩ : syracuseStep 1933719 = 2900579) B2900579
theorem B3097453 : Blo 1933435 3097453 := bbase (se 3 (by rfl) ⟨580772, by rfl⟩ : syracuseStep 3097453 = 1161545) (by norm_num)
theorem B4129937 : Blo 1933435 4129937 := bstep (se 2 (by rfl) ⟨1548726, by rfl⟩ : syracuseStep 4129937 = 3097453) B3097453
theorem B2753291 : Blo 1933435 2753291 := bstep (se 1 (by rfl) ⟨2064968, by rfl⟩ : syracuseStep 2753291 = 4129937) B4129937
theorem B7342109 : Blo 1933435 7342109 := bstep (se 3 (by rfl) ⟨1376645, by rfl⟩ : syracuseStep 7342109 = 2753291) B2753291
theorem B4894739 : Blo 1933435 4894739 := bstep (se 1 (by rfl) ⟨3671054, by rfl⟩ : syracuseStep 4894739 = 7342109) B7342109
theorem B3263159 : Blo 1933435 3263159 := bstep (se 1 (by rfl) ⟨2447369, by rfl⟩ : syracuseStep 3263159 = 4894739) B4894739
theorem B2175439 : Blo 1933435 2175439 := bstep (se 1 (by rfl) ⟨1631579, by rfl⟩ : syracuseStep 2175439 = 3263159) B3263159
theorem B2900585 : Blo 1933435 2900585 := bstep (se 2 (by rfl) ⟨1087719, by rfl⟩ : syracuseStep 2900585 = 2175439) B2175439
theorem B1933723 : Blo 1933435 1933723 := bstep (se 1 (by rfl) ⟨1450292, by rfl⟩ : syracuseStep 1933723 = 2900585) B2900585
theorem B6194917 : Blo 1933435 6194917 := bbase (se 4 (by rfl) ⟨580773, by rfl⟩ : syracuseStep 6194917 = 1161547) (by norm_num)
theorem B8259889 : Blo 1933435 8259889 := bstep (se 2 (by rfl) ⟨3097458, by rfl⟩ : syracuseStep 8259889 = 6194917) B6194917
theorem B11013185 : Blo 1933435 11013185 := bstep (se 2 (by rfl) ⟨4129944, by rfl⟩ : syracuseStep 11013185 = 8259889) B8259889
theorem B7342123 : Blo 1933435 7342123 := bstep (se 1 (by rfl) ⟨5506592, by rfl⟩ : syracuseStep 7342123 = 11013185) B11013185
theorem B9789497 : Blo 1933435 9789497 := bstep (se 2 (by rfl) ⟨3671061, by rfl⟩ : syracuseStep 9789497 = 7342123) B7342123
theorem B6526331 : Blo 1933435 6526331 := bstep (se 1 (by rfl) ⟨4894748, by rfl⟩ : syracuseStep 6526331 = 9789497) B9789497
theorem B4350887 : Blo 1933435 4350887 := bstep (se 1 (by rfl) ⟨3263165, by rfl⟩ : syracuseStep 4350887 = 6526331) B6526331
theorem B2900591 : Blo 1933435 2900591 := bstep (se 1 (by rfl) ⟨2175443, by rfl⟩ : syracuseStep 2900591 = 4350887) B4350887
theorem B1933727 : Blo 1933435 1933727 := bstep (se 1 (by rfl) ⟨1450295, by rfl⟩ : syracuseStep 1933727 = 2900591) B2900591
theorem B2900597 : Blo 1933435 2900597 := bbase (se 5 (by rfl) ⟨135965, by rfl⟩ : syracuseStep 2900597 = 271931) (by norm_num)
theorem B1933731 : Blo 1933435 1933731 := bstep (se 1 (by rfl) ⟨1450298, by rfl⟩ : syracuseStep 1933731 = 2900597) B2900597
theorem B3671077 : Blo 1933435 3671077 := bbase (se 4 (by rfl) ⟨344163, by rfl⟩ : syracuseStep 3671077 = 688327) (by norm_num)
theorem B4894769 : Blo 1933435 4894769 := bstep (se 2 (by rfl) ⟨1835538, by rfl⟩ : syracuseStep 4894769 = 3671077) B3671077
theorem B3263179 : Blo 1933435 3263179 := bstep (se 1 (by rfl) ⟨2447384, by rfl⟩ : syracuseStep 3263179 = 4894769) B4894769
theorem B4350905 : Blo 1933435 4350905 := bstep (se 2 (by rfl) ⟨1631589, by rfl⟩ : syracuseStep 4350905 = 3263179) B3263179
theorem B2900603 : Blo 1933435 2900603 := bstep (se 1 (by rfl) ⟨2175452, by rfl⟩ : syracuseStep 2900603 = 4350905) B4350905
theorem B1933735 : Blo 1933435 1933735 := bstep (se 1 (by rfl) ⟨1450301, by rfl⟩ : syracuseStep 1933735 = 2900603) B2900603
theorem B2175457 : Blo 1933435 2175457 := bbase (se 2 (by rfl) ⟨815796, by rfl⟩ : syracuseStep 2175457 = 1631593) (by norm_num)
theorem B2900609 : Blo 1933435 2900609 := bstep (se 2 (by rfl) ⟨1087728, by rfl⟩ : syracuseStep 2900609 = 2175457) B2175457
theorem B1933739 : Blo 1933435 1933739 := bstep (se 1 (by rfl) ⟨1450304, by rfl⟩ : syracuseStep 1933739 = 2900609) B2900609
theorem B4894789 : Blo 1933435 4894789 := bbase (se 4 (by rfl) ⟨458886, by rfl⟩ : syracuseStep 4894789 = 917773) (by norm_num)
theorem B6526385 : Blo 1933435 6526385 := bstep (se 2 (by rfl) ⟨2447394, by rfl⟩ : syracuseStep 6526385 = 4894789) B4894789
theorem B4350923 : Blo 1933435 4350923 := bstep (se 1 (by rfl) ⟨3263192, by rfl⟩ : syracuseStep 4350923 = 6526385) B6526385
theorem B2900615 : Blo 1933435 2900615 := bstep (se 1 (by rfl) ⟨2175461, by rfl⟩ : syracuseStep 2900615 = 4350923) B4350923
theorem B1933743 : Blo 1933435 1933743 := bstep (se 1 (by rfl) ⟨1450307, by rfl⟩ : syracuseStep 1933743 = 2900615) B2900615
theorem B2900621 : Blo 1933435 2900621 := bbase (se 3 (by rfl) ⟨543866, by rfl⟩ : syracuseStep 2900621 = 1087733) (by norm_num)
theorem B1933747 : Blo 1933435 1933747 := bstep (se 1 (by rfl) ⟨1450310, by rfl⟩ : syracuseStep 1933747 = 2900621) B2900621
theorem B4350941 : Blo 1933435 4350941 := bbase (se 3 (by rfl) ⟨815801, by rfl⟩ : syracuseStep 4350941 = 1631603) (by norm_num)
theorem B2900627 : Blo 1933435 2900627 := bstep (se 1 (by rfl) ⟨2175470, by rfl⟩ : syracuseStep 2900627 = 4350941) B4350941
theorem B1933751 : Blo 1933435 1933751 := bstep (se 1 (by rfl) ⟨1450313, by rfl⟩ : syracuseStep 1933751 = 2900627) B2900627
theorem B3263213 : Blo 1933435 3263213 := bbase (se 3 (by rfl) ⟨611852, by rfl⟩ : syracuseStep 3263213 = 1223705) (by norm_num)
theorem B2175475 : Blo 1933435 2175475 := bstep (se 1 (by rfl) ⟨1631606, by rfl⟩ : syracuseStep 2175475 = 3263213) B3263213
theorem B2900633 : Blo 1933435 2900633 := bstep (se 2 (by rfl) ⟨1087737, by rfl⟩ : syracuseStep 2900633 = 2175475) B2175475
theorem B1933755 : Blo 1933435 1933755 := bstep (se 1 (by rfl) ⟨1450316, by rfl⟩ : syracuseStep 1933755 = 2900633) B2900633
theorem B6969397 : Blo 1933435 6969397 := bbase (se 5 (by rfl) ⟨326690, by rfl⟩ : syracuseStep 6969397 = 653381) (by norm_num)
theorem B9292529 : Blo 1933435 9292529 := bstep (se 2 (by rfl) ⟨3484698, by rfl⟩ : syracuseStep 9292529 = 6969397) B6969397
theorem B24780077 : Blo 1933435 24780077 := bstep (se 3 (by rfl) ⟨4646264, by rfl⟩ : syracuseStep 24780077 = 9292529) B9292529
theorem B16520051 : Blo 1933435 16520051 := bstep (se 1 (by rfl) ⟨12390038, by rfl⟩ : syracuseStep 16520051 = 24780077) B24780077
theorem B11013367 : Blo 1933435 11013367 := bstep (se 1 (by rfl) ⟨8260025, by rfl⟩ : syracuseStep 11013367 = 16520051) B16520051
theorem B14684489 : Blo 1933435 14684489 := bstep (se 2 (by rfl) ⟨5506683, by rfl⟩ : syracuseStep 14684489 = 11013367) B11013367
theorem B9789659 : Blo 1933435 9789659 := bstep (se 1 (by rfl) ⟨7342244, by rfl⟩ : syracuseStep 9789659 = 14684489) B14684489
theorem B6526439 : Blo 1933435 6526439 := bstep (se 1 (by rfl) ⟨4894829, by rfl⟩ : syracuseStep 6526439 = 9789659) B9789659
theorem B4350959 : Blo 1933435 4350959 := bstep (se 1 (by rfl) ⟨3263219, by rfl⟩ : syracuseStep 4350959 = 6526439) B6526439
theorem B2900639 : Blo 1933435 2900639 := bstep (se 1 (by rfl) ⟨2175479, by rfl⟩ : syracuseStep 2900639 = 4350959) B4350959
theorem B1933759 : Blo 1933435 1933759 := bstep (se 1 (by rfl) ⟨1450319, by rfl⟩ : syracuseStep 1933759 = 2900639) B2900639
theorem B2900645 : Blo 1933435 2900645 := bbase (se 4 (by rfl) ⟨271935, by rfl⟩ : syracuseStep 2900645 = 543871) (by norm_num)
theorem B1933763 : Blo 1933435 1933763 := bstep (se 1 (by rfl) ⟨1450322, by rfl⟩ : syracuseStep 1933763 = 2900645) B2900645
theorem B2447425 : Blo 1933435 2447425 := bbase (se 2 (by rfl) ⟨917784, by rfl⟩ : syracuseStep 2447425 = 1835569) (by norm_num)
theorem B3263233 : Blo 1933435 3263233 := bstep (se 2 (by rfl) ⟨1223712, by rfl⟩ : syracuseStep 3263233 = 2447425) B2447425
theorem B4350977 : Blo 1933435 4350977 := bstep (se 2 (by rfl) ⟨1631616, by rfl⟩ : syracuseStep 4350977 = 3263233) B3263233
theorem B2900651 : Blo 1933435 2900651 := bstep (se 1 (by rfl) ⟨2175488, by rfl⟩ : syracuseStep 2900651 = 4350977) B4350977
theorem B1933767 : Blo 1933435 1933767 := bstep (se 1 (by rfl) ⟨1450325, by rfl⟩ : syracuseStep 1933767 = 2900651) B2900651
theorem B2175493 : Blo 1933435 2175493 := bbase (se 4 (by rfl) ⟨203952, by rfl⟩ : syracuseStep 2175493 = 407905) (by norm_num)
theorem B2900657 : Blo 1933435 2900657 := bstep (se 2 (by rfl) ⟨1087746, by rfl⟩ : syracuseStep 2900657 = 2175493) B2175493
theorem B1933771 : Blo 1933435 1933771 := bstep (se 1 (by rfl) ⟨1450328, by rfl⟩ : syracuseStep 1933771 = 2900657) B2900657
theorem B2753365 : Blo 1933435 2753365 := bbase (se 9 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 2753365 = 16133) (by norm_num)
theorem B3671153 : Blo 1933435 3671153 := bstep (se 2 (by rfl) ⟨1376682, by rfl⟩ : syracuseStep 3671153 = 2753365) B2753365
theorem B2447435 : Blo 1933435 2447435 := bstep (se 1 (by rfl) ⟨1835576, by rfl⟩ : syracuseStep 2447435 = 3671153) B3671153
theorem B6526493 : Blo 1933435 6526493 := bstep (se 3 (by rfl) ⟨1223717, by rfl⟩ : syracuseStep 6526493 = 2447435) B2447435
theorem B4350995 : Blo 1933435 4350995 := bstep (se 1 (by rfl) ⟨3263246, by rfl⟩ : syracuseStep 4350995 = 6526493) B6526493
theorem B2900663 : Blo 1933435 2900663 := bstep (se 1 (by rfl) ⟨2175497, by rfl⟩ : syracuseStep 2900663 = 4350995) B4350995
theorem B1933775 : Blo 1933435 1933775 := bstep (se 1 (by rfl) ⟨1450331, by rfl⟩ : syracuseStep 1933775 = 2900663) B2900663
theorem B2900669 : Blo 1933435 2900669 := bbase (se 3 (by rfl) ⟨543875, by rfl⟩ : syracuseStep 2900669 = 1087751) (by norm_num)
theorem B1933779 : Blo 1933435 1933779 := bstep (se 1 (by rfl) ⟨1450334, by rfl⟩ : syracuseStep 1933779 = 2900669) B2900669
theorem B4351013 : Blo 1933435 4351013 := bbase (se 4 (by rfl) ⟨407907, by rfl⟩ : syracuseStep 4351013 = 815815) (by norm_num)
theorem B2900675 : Blo 1933435 2900675 := bstep (se 1 (by rfl) ⟨2175506, by rfl⟩ : syracuseStep 2900675 = 4351013) B4351013
theorem B1933783 : Blo 1933435 1933783 := bstep (se 1 (by rfl) ⟨1450337, by rfl⟩ : syracuseStep 1933783 = 2900675) B2900675
theorem B4894901 : Blo 1933435 4894901 := bbase (se 5 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 4894901 = 458897) (by norm_num)
theorem B3263267 : Blo 1933435 3263267 := bstep (se 1 (by rfl) ⟨2447450, by rfl⟩ : syracuseStep 3263267 = 4894901) B4894901
theorem B2175511 : Blo 1933435 2175511 := bstep (se 1 (by rfl) ⟨1631633, by rfl⟩ : syracuseStep 2175511 = 3263267) B3263267
theorem B2900681 : Blo 1933435 2900681 := bstep (se 2 (by rfl) ⟨1087755, by rfl⟩ : syracuseStep 2900681 = 2175511) B2175511
theorem B1933787 : Blo 1933435 1933787 := bstep (se 1 (by rfl) ⟨1450340, by rfl⟩ : syracuseStep 1933787 = 2900681) B2900681
theorem B3484757 : Blo 1933435 3484757 := bbase (se 8 (by rfl) ⟨20418, by rfl⟩ : syracuseStep 3484757 = 40837) (by norm_num)
theorem B2323171 : Blo 1933435 2323171 := bstep (se 1 (by rfl) ⟨1742378, by rfl⟩ : syracuseStep 2323171 = 3484757) B3484757
theorem B12390245 : Blo 1933435 12390245 := bstep (se 4 (by rfl) ⟨1161585, by rfl⟩ : syracuseStep 12390245 = 2323171) B2323171
theorem B8260163 : Blo 1933435 8260163 := bstep (se 1 (by rfl) ⟨6195122, by rfl⟩ : syracuseStep 8260163 = 12390245) B12390245
theorem B5506775 : Blo 1933435 5506775 := bstep (se 1 (by rfl) ⟨4130081, by rfl⟩ : syracuseStep 5506775 = 8260163) B8260163
theorem B3671183 : Blo 1933435 3671183 := bstep (se 1 (by rfl) ⟨2753387, by rfl⟩ : syracuseStep 3671183 = 5506775) B5506775
theorem B9789821 : Blo 1933435 9789821 := bstep (se 3 (by rfl) ⟨1835591, by rfl⟩ : syracuseStep 9789821 = 3671183) B3671183
theorem B6526547 : Blo 1933435 6526547 := bstep (se 1 (by rfl) ⟨4894910, by rfl⟩ : syracuseStep 6526547 = 9789821) B9789821
theorem B4351031 : Blo 1933435 4351031 := bstep (se 1 (by rfl) ⟨3263273, by rfl⟩ : syracuseStep 4351031 = 6526547) B6526547
theorem B2900687 : Blo 1933435 2900687 := bstep (se 1 (by rfl) ⟨2175515, by rfl⟩ : syracuseStep 2900687 = 4351031) B4351031
theorem B1933791 : Blo 1933435 1933791 := bstep (se 1 (by rfl) ⟨1450343, by rfl⟩ : syracuseStep 1933791 = 2900687) B2900687
theorem B2900693 : Blo 1933435 2900693 := bbase (se 7 (by rfl) ⟨33992, by rfl⟩ : syracuseStep 2900693 = 67985) (by norm_num)
theorem B1933795 : Blo 1933435 1933795 := bstep (se 1 (by rfl) ⟨1450346, by rfl⟩ : syracuseStep 1933795 = 2900693) B2900693
theorem B2323181 : Blo 1933435 2323181 := bbase (se 3 (by rfl) ⟨435596, by rfl⟩ : syracuseStep 2323181 = 871193) (by norm_num)
theorem B6195149 : Blo 1933435 6195149 := bstep (se 3 (by rfl) ⟨1161590, by rfl⟩ : syracuseStep 6195149 = 2323181) B2323181
theorem B4130099 : Blo 1933435 4130099 := bstep (se 1 (by rfl) ⟨3097574, by rfl⟩ : syracuseStep 4130099 = 6195149) B6195149
theorem B2753399 : Blo 1933435 2753399 := bstep (se 1 (by rfl) ⟨2065049, by rfl⟩ : syracuseStep 2753399 = 4130099) B4130099
theorem B7342397 : Blo 1933435 7342397 := bstep (se 3 (by rfl) ⟨1376699, by rfl⟩ : syracuseStep 7342397 = 2753399) B2753399
theorem B4894931 : Blo 1933435 4894931 := bstep (se 1 (by rfl) ⟨3671198, by rfl⟩ : syracuseStep 4894931 = 7342397) B7342397
theorem B3263287 : Blo 1933435 3263287 := bstep (se 1 (by rfl) ⟨2447465, by rfl⟩ : syracuseStep 3263287 = 4894931) B4894931
theorem B4351049 : Blo 1933435 4351049 := bstep (se 2 (by rfl) ⟨1631643, by rfl⟩ : syracuseStep 4351049 = 3263287) B3263287
theorem B2900699 : Blo 1933435 2900699 := bstep (se 1 (by rfl) ⟨2175524, by rfl⟩ : syracuseStep 2900699 = 4351049) B4351049
theorem B1933799 : Blo 1933435 1933799 := bstep (se 1 (by rfl) ⟨1450349, by rfl⟩ : syracuseStep 1933799 = 2900699) B2900699
theorem B2175529 : Blo 1933435 2175529 := bbase (se 2 (by rfl) ⟨815823, by rfl⟩ : syracuseStep 2175529 = 1631647) (by norm_num)
theorem B2900705 : Blo 1933435 2900705 := bstep (se 2 (by rfl) ⟨1087764, by rfl⟩ : syracuseStep 2900705 = 2175529) B2175529
theorem B1933803 : Blo 1933435 1933803 := bstep (se 1 (by rfl) ⟨1450352, by rfl⟩ : syracuseStep 1933803 = 2900705) B2900705
theorem B2613589 : Blo 1933435 2613589 := bbase (se 10 (by rfl) ⟨3828, by rfl⟩ : syracuseStep 2613589 = 7657) (by norm_num)
theorem B13939141 : Blo 1933435 13939141 := bstep (se 4 (by rfl) ⟨1306794, by rfl⟩ : syracuseStep 13939141 = 2613589) B2613589
theorem B18585521 : Blo 1933435 18585521 := bstep (se 2 (by rfl) ⟨6969570, by rfl⟩ : syracuseStep 18585521 = 13939141) B13939141
theorem B12390347 : Blo 1933435 12390347 := bstep (se 1 (by rfl) ⟨9292760, by rfl⟩ : syracuseStep 12390347 = 18585521) B18585521
theorem B8260231 : Blo 1933435 8260231 := bstep (se 1 (by rfl) ⟨6195173, by rfl⟩ : syracuseStep 8260231 = 12390347) B12390347
theorem B11013641 : Blo 1933435 11013641 := bstep (se 2 (by rfl) ⟨4130115, by rfl⟩ : syracuseStep 11013641 = 8260231) B8260231
theorem B7342427 : Blo 1933435 7342427 := bstep (se 1 (by rfl) ⟨5506820, by rfl⟩ : syracuseStep 7342427 = 11013641) B11013641
theorem B4894951 : Blo 1933435 4894951 := bstep (se 1 (by rfl) ⟨3671213, by rfl⟩ : syracuseStep 4894951 = 7342427) B7342427
theorem B6526601 : Blo 1933435 6526601 := bstep (se 2 (by rfl) ⟨2447475, by rfl⟩ : syracuseStep 6526601 = 4894951) B4894951
theorem B4351067 : Blo 1933435 4351067 := bstep (se 1 (by rfl) ⟨3263300, by rfl⟩ : syracuseStep 4351067 = 6526601) B6526601
theorem B2900711 : Blo 1933435 2900711 := bstep (se 1 (by rfl) ⟨2175533, by rfl⟩ : syracuseStep 2900711 = 4351067) B4351067
theorem B1933807 : Blo 1933435 1933807 := bstep (se 1 (by rfl) ⟨1450355, by rfl⟩ : syracuseStep 1933807 = 2900711) B2900711
theorem B2900717 : Blo 1933435 2900717 := bbase (se 3 (by rfl) ⟨543884, by rfl⟩ : syracuseStep 2900717 = 1087769) (by norm_num)
theorem B1933811 : Blo 1933435 1933811 := bstep (se 1 (by rfl) ⟨1450358, by rfl⟩ : syracuseStep 1933811 = 2900717) B2900717
theorem B4351085 : Blo 1933435 4351085 := bbase (se 3 (by rfl) ⟨815828, by rfl⟩ : syracuseStep 4351085 = 1631657) (by norm_num)
theorem B2900723 : Blo 1933435 2900723 := bstep (se 1 (by rfl) ⟨2175542, by rfl⟩ : syracuseStep 2900723 = 4351085) B4351085
theorem B1933815 : Blo 1933435 1933815 := bstep (se 1 (by rfl) ⟨1450361, by rfl⟩ : syracuseStep 1933815 = 2900723) B2900723
theorem B3671237 : Blo 1933435 3671237 := bbase (se 4 (by rfl) ⟨344178, by rfl⟩ : syracuseStep 3671237 = 688357) (by norm_num)
theorem B2447491 : Blo 1933435 2447491 := bstep (se 1 (by rfl) ⟨1835618, by rfl⟩ : syracuseStep 2447491 = 3671237) B3671237
theorem B3263321 : Blo 1933435 3263321 := bstep (se 2 (by rfl) ⟨1223745, by rfl⟩ : syracuseStep 3263321 = 2447491) B2447491
theorem B2175547 : Blo 1933435 2175547 := bstep (se 1 (by rfl) ⟨1631660, by rfl⟩ : syracuseStep 2175547 = 3263321) B3263321
theorem B2900729 : Blo 1933435 2900729 := bstep (se 2 (by rfl) ⟨1087773, by rfl⟩ : syracuseStep 2900729 = 2175547) B2175547
theorem B1933819 : Blo 1933435 1933819 := bstep (se 1 (by rfl) ⟨1450364, by rfl⟩ : syracuseStep 1933819 = 2900729) B2900729
theorem B6279749 : Blo 1933435 6279749 := bbase (se 4 (by rfl) ⟨588726, by rfl⟩ : syracuseStep 6279749 = 1177453) (by norm_num)
theorem B4186499 : Blo 1933435 4186499 := bstep (se 1 (by rfl) ⟨3139874, by rfl⟩ : syracuseStep 4186499 = 6279749) B6279749
theorem B11163997 : Blo 1933435 11163997 := bstep (se 3 (by rfl) ⟨2093249, by rfl⟩ : syracuseStep 11163997 = 4186499) B4186499
theorem B59541317 : Blo 1933435 59541317 := bstep (se 4 (by rfl) ⟨5581998, by rfl⟩ : syracuseStep 59541317 = 11163997) B11163997
theorem B39694211 : Blo 1933435 39694211 := bstep (se 1 (by rfl) ⟨29770658, by rfl⟩ : syracuseStep 39694211 = 59541317) B59541317
theorem B26462807 : Blo 1933435 26462807 := bstep (se 1 (by rfl) ⟨19847105, by rfl⟩ : syracuseStep 26462807 = 39694211) B39694211
theorem B17641871 : Blo 1933435 17641871 := bstep (se 1 (by rfl) ⟨13231403, by rfl⟩ : syracuseStep 17641871 = 26462807) B26462807
theorem B11761247 : Blo 1933435 11761247 := bstep (se 1 (by rfl) ⟨8820935, by rfl⟩ : syracuseStep 11761247 = 17641871) B17641871
theorem B7840831 : Blo 1933435 7840831 := bstep (se 1 (by rfl) ⟨5880623, by rfl⟩ : syracuseStep 7840831 = 11761247) B11761247
theorem B10454441 : Blo 1933435 10454441 := bstep (se 2 (by rfl) ⟨3920415, by rfl⟩ : syracuseStep 10454441 = 7840831) B7840831
theorem B27878509 : Blo 1933435 27878509 := bstep (se 3 (by rfl) ⟨5227220, by rfl⟩ : syracuseStep 27878509 = 10454441) B10454441
theorem B37171345 : Blo 1933435 37171345 := bstep (se 2 (by rfl) ⟨13939254, by rfl⟩ : syracuseStep 37171345 = 27878509) B27878509
theorem B49561793 : Blo 1933435 49561793 := bstep (se 2 (by rfl) ⟨18585672, by rfl⟩ : syracuseStep 49561793 = 37171345) B37171345
theorem B33041195 : Blo 1933435 33041195 := bstep (se 1 (by rfl) ⟨24780896, by rfl⟩ : syracuseStep 33041195 = 49561793) B49561793
theorem B22027463 : Blo 1933435 22027463 := bstep (se 1 (by rfl) ⟨16520597, by rfl⟩ : syracuseStep 22027463 = 33041195) B33041195
theorem B14684975 : Blo 1933435 14684975 := bstep (se 1 (by rfl) ⟨11013731, by rfl⟩ : syracuseStep 14684975 = 22027463) B22027463
theorem B9789983 : Blo 1933435 9789983 := bstep (se 1 (by rfl) ⟨7342487, by rfl⟩ : syracuseStep 9789983 = 14684975) B14684975
theorem B6526655 : Blo 1933435 6526655 := bstep (se 1 (by rfl) ⟨4894991, by rfl⟩ : syracuseStep 6526655 = 9789983) B9789983
theorem B4351103 : Blo 1933435 4351103 := bstep (se 1 (by rfl) ⟨3263327, by rfl⟩ : syracuseStep 4351103 = 6526655) B6526655
theorem B2900735 : Blo 1933435 2900735 := bstep (se 1 (by rfl) ⟨2175551, by rfl⟩ : syracuseStep 2900735 = 4351103) B4351103
theorem B1933823 : Blo 1933435 1933823 := bstep (se 1 (by rfl) ⟨1450367, by rfl⟩ : syracuseStep 1933823 = 2900735) B2900735
theorem B2900741 : Blo 1933435 2900741 := bbase (se 4 (by rfl) ⟨271944, by rfl⟩ : syracuseStep 2900741 = 543889) (by norm_num)
theorem B1933827 : Blo 1933435 1933827 := bstep (se 1 (by rfl) ⟨1450370, by rfl⟩ : syracuseStep 1933827 = 2900741) B2900741
theorem B3263341 : Blo 1933435 3263341 := bbase (se 3 (by rfl) ⟨611876, by rfl⟩ : syracuseStep 3263341 = 1223753) (by norm_num)
theorem B4351121 : Blo 1933435 4351121 := bstep (se 2 (by rfl) ⟨1631670, by rfl⟩ : syracuseStep 4351121 = 3263341) B3263341
theorem B2900747 : Blo 1933435 2900747 := bstep (se 1 (by rfl) ⟨2175560, by rfl⟩ : syracuseStep 2900747 = 4351121) B4351121
theorem B1933831 : Blo 1933435 1933831 := bstep (se 1 (by rfl) ⟨1450373, by rfl⟩ : syracuseStep 1933831 = 2900747) B2900747
theorem B2175565 : Blo 1933435 2175565 := bbase (se 3 (by rfl) ⟨407918, by rfl⟩ : syracuseStep 2175565 = 815837) (by norm_num)
theorem B2900753 : Blo 1933435 2900753 := bstep (se 2 (by rfl) ⟨1087782, by rfl⟩ : syracuseStep 2900753 = 2175565) B2175565
theorem B1933835 : Blo 1933435 1933835 := bstep (se 1 (by rfl) ⟨1450376, by rfl⟩ : syracuseStep 1933835 = 2900753) B2900753
theorem B6526709 : Blo 1933435 6526709 := bbase (se 5 (by rfl) ⟨305939, by rfl⟩ : syracuseStep 6526709 = 611879) (by norm_num)
theorem B4351139 : Blo 1933435 4351139 := bstep (se 1 (by rfl) ⟨3263354, by rfl⟩ : syracuseStep 4351139 = 6526709) B6526709
theorem B2900759 : Blo 1933435 2900759 := bstep (se 1 (by rfl) ⟨2175569, by rfl⟩ : syracuseStep 2900759 = 4351139) B4351139
theorem B1933839 : Blo 1933435 1933839 := bstep (se 1 (by rfl) ⟨1450379, by rfl⟩ : syracuseStep 1933839 = 2900759) B2900759
theorem B2900765 : Blo 1933435 2900765 := bbase (se 3 (by rfl) ⟨543893, by rfl⟩ : syracuseStep 2900765 = 1087787) (by norm_num)
theorem B1933843 : Blo 1933435 1933843 := bstep (se 1 (by rfl) ⟨1450382, by rfl⟩ : syracuseStep 1933843 = 2900765) B2900765
theorem B4351157 : Blo 1933435 4351157 := bbase (se 5 (by rfl) ⟨203960, by rfl⟩ : syracuseStep 4351157 = 407921) (by norm_num)
theorem B2900771 : Blo 1933435 2900771 := bstep (se 1 (by rfl) ⟨2175578, by rfl⟩ : syracuseStep 2900771 = 4351157) B4351157
theorem B1933847 : Blo 1933435 1933847 := bstep (se 1 (by rfl) ⟨1450385, by rfl⟩ : syracuseStep 1933847 = 2900771) B2900771
theorem B2065105 : Blo 1933435 2065105 := bbase (se 2 (by rfl) ⟨774414, by rfl⟩ : syracuseStep 2065105 = 1548829) (by norm_num)
theorem B11013893 : Blo 1933435 11013893 := bstep (se 4 (by rfl) ⟨1032552, by rfl⟩ : syracuseStep 11013893 = 2065105) B2065105
theorem B7342595 : Blo 1933435 7342595 := bstep (se 1 (by rfl) ⟨5506946, by rfl⟩ : syracuseStep 7342595 = 11013893) B11013893
theorem B4895063 : Blo 1933435 4895063 := bstep (se 1 (by rfl) ⟨3671297, by rfl⟩ : syracuseStep 4895063 = 7342595) B7342595
theorem B3263375 : Blo 1933435 3263375 := bstep (se 1 (by rfl) ⟨2447531, by rfl⟩ : syracuseStep 3263375 = 4895063) B4895063
theorem B2175583 : Blo 1933435 2175583 := bstep (se 1 (by rfl) ⟨1631687, by rfl⟩ : syracuseStep 2175583 = 3263375) B3263375
theorem B2900777 : Blo 1933435 2900777 := bstep (se 2 (by rfl) ⟨1087791, by rfl⟩ : syracuseStep 2900777 = 2175583) B2175583
theorem B1933851 : Blo 1933435 1933851 := bstep (se 1 (by rfl) ⟨1450388, by rfl⟩ : syracuseStep 1933851 = 2900777) B2900777
theorem B2065109 : Blo 1933435 2065109 := bbase (se 7 (by rfl) ⟨24200, by rfl⟩ : syracuseStep 2065109 = 48401) (by norm_num)
theorem B5506957 : Blo 1933435 5506957 := bstep (se 3 (by rfl) ⟨1032554, by rfl⟩ : syracuseStep 5506957 = 2065109) B2065109
theorem B7342609 : Blo 1933435 7342609 := bstep (se 2 (by rfl) ⟨2753478, by rfl⟩ : syracuseStep 7342609 = 5506957) B5506957
theorem B9790145 : Blo 1933435 9790145 := bstep (se 2 (by rfl) ⟨3671304, by rfl⟩ : syracuseStep 9790145 = 7342609) B7342609
theorem B6526763 : Blo 1933435 6526763 := bstep (se 1 (by rfl) ⟨4895072, by rfl⟩ : syracuseStep 6526763 = 9790145) B9790145
theorem B4351175 : Blo 1933435 4351175 := bstep (se 1 (by rfl) ⟨3263381, by rfl⟩ : syracuseStep 4351175 = 6526763) B6526763
theorem B2900783 : Blo 1933435 2900783 := bstep (se 1 (by rfl) ⟨2175587, by rfl⟩ : syracuseStep 2900783 = 4351175) B4351175
theorem B1933855 : Blo 1933435 1933855 := bstep (se 1 (by rfl) ⟨1450391, by rfl⟩ : syracuseStep 1933855 = 2900783) B2900783
theorem B2900789 : Blo 1933435 2900789 := bbase (se 5 (by rfl) ⟨135974, by rfl⟩ : syracuseStep 2900789 = 271949) (by norm_num)
theorem B1933859 : Blo 1933435 1933859 := bstep (se 1 (by rfl) ⟨1450394, by rfl⟩ : syracuseStep 1933859 = 2900789) B2900789
theorem B4895093 : Blo 1933435 4895093 := bbase (se 5 (by rfl) ⟨229457, by rfl⟩ : syracuseStep 4895093 = 458915) (by norm_num)
theorem B3263395 : Blo 1933435 3263395 := bstep (se 1 (by rfl) ⟨2447546, by rfl⟩ : syracuseStep 3263395 = 4895093) B4895093
theorem B4351193 : Blo 1933435 4351193 := bstep (se 2 (by rfl) ⟨1631697, by rfl⟩ : syracuseStep 4351193 = 3263395) B3263395
theorem B2900795 : Blo 1933435 2900795 := bstep (se 1 (by rfl) ⟨2175596, by rfl⟩ : syracuseStep 2900795 = 4351193) B4351193
theorem B1933863 : Blo 1933435 1933863 := bstep (se 1 (by rfl) ⟨1450397, by rfl⟩ : syracuseStep 1933863 = 2900795) B2900795
theorem B2175601 : Blo 1933435 2175601 := bbase (se 2 (by rfl) ⟨815850, by rfl⟩ : syracuseStep 2175601 = 1631701) (by norm_num)
theorem B2900801 : Blo 1933435 2900801 := bstep (se 2 (by rfl) ⟨1087800, by rfl⟩ : syracuseStep 2900801 = 2175601) B2175601
theorem B1933867 : Blo 1933435 1933867 := bstep (se 1 (by rfl) ⟨1450400, by rfl⟩ : syracuseStep 1933867 = 2900801) B2900801
theorem B3484901 : Blo 1933435 3484901 := bbase (se 4 (by rfl) ⟨326709, by rfl⟩ : syracuseStep 3484901 = 653419) (by norm_num)
theorem B9293069 : Blo 1933435 9293069 := bstep (se 3 (by rfl) ⟨1742450, by rfl⟩ : syracuseStep 9293069 = 3484901) B3484901
theorem B6195379 : Blo 1933435 6195379 := bstep (se 1 (by rfl) ⟨4646534, by rfl⟩ : syracuseStep 6195379 = 9293069) B9293069
theorem B8260505 : Blo 1933435 8260505 := bstep (se 2 (by rfl) ⟨3097689, by rfl⟩ : syracuseStep 8260505 = 6195379) B6195379
theorem B5507003 : Blo 1933435 5507003 := bstep (se 1 (by rfl) ⟨4130252, by rfl⟩ : syracuseStep 5507003 = 8260505) B8260505
theorem B3671335 : Blo 1933435 3671335 := bstep (se 1 (by rfl) ⟨2753501, by rfl⟩ : syracuseStep 3671335 = 5507003) B5507003
theorem B4895113 : Blo 1933435 4895113 := bstep (se 2 (by rfl) ⟨1835667, by rfl⟩ : syracuseStep 4895113 = 3671335) B3671335
theorem B6526817 : Blo 1933435 6526817 := bstep (se 2 (by rfl) ⟨2447556, by rfl⟩ : syracuseStep 6526817 = 4895113) B4895113
theorem B4351211 : Blo 1933435 4351211 := bstep (se 1 (by rfl) ⟨3263408, by rfl⟩ : syracuseStep 4351211 = 6526817) B6526817
theorem B2900807 : Blo 1933435 2900807 := bstep (se 1 (by rfl) ⟨2175605, by rfl⟩ : syracuseStep 2900807 = 4351211) B4351211
theorem B1933871 : Blo 1933435 1933871 := bstep (se 1 (by rfl) ⟨1450403, by rfl⟩ : syracuseStep 1933871 = 2900807) B2900807
theorem B2900813 : Blo 1933435 2900813 := bbase (se 3 (by rfl) ⟨543902, by rfl⟩ : syracuseStep 2900813 = 1087805) (by norm_num)
theorem B1933875 : Blo 1933435 1933875 := bstep (se 1 (by rfl) ⟨1450406, by rfl⟩ : syracuseStep 1933875 = 2900813) B2900813
theorem B4351229 : Blo 1933435 4351229 := bbase (se 3 (by rfl) ⟨815855, by rfl⟩ : syracuseStep 4351229 = 1631711) (by norm_num)
theorem B2900819 : Blo 1933435 2900819 := bstep (se 1 (by rfl) ⟨2175614, by rfl⟩ : syracuseStep 2900819 = 4351229) B4351229
theorem B1933879 : Blo 1933435 1933879 := bstep (se 1 (by rfl) ⟨1450409, by rfl⟩ : syracuseStep 1933879 = 2900819) B2900819
theorem B3263429 : Blo 1933435 3263429 := bbase (se 4 (by rfl) ⟨305946, by rfl⟩ : syracuseStep 3263429 = 611893) (by norm_num)
theorem B2175619 : Blo 1933435 2175619 := bstep (se 1 (by rfl) ⟨1631714, by rfl⟩ : syracuseStep 2175619 = 3263429) B3263429
theorem B2900825 : Blo 1933435 2900825 := bstep (se 2 (by rfl) ⟨1087809, by rfl⟩ : syracuseStep 2900825 = 2175619) B2175619
theorem B1933883 : Blo 1933435 1933883 := bstep (se 1 (by rfl) ⟨1450412, by rfl⟩ : syracuseStep 1933883 = 2900825) B2900825
theorem B14685461 : Blo 1933435 14685461 := bbase (se 6 (by rfl) ⟨344190, by rfl⟩ : syracuseStep 14685461 = 688381) (by norm_num)
theorem B9790307 : Blo 1933435 9790307 := bstep (se 1 (by rfl) ⟨7342730, by rfl⟩ : syracuseStep 9790307 = 14685461) B14685461
theorem B6526871 : Blo 1933435 6526871 := bstep (se 1 (by rfl) ⟨4895153, by rfl⟩ : syracuseStep 6526871 = 9790307) B9790307
theorem B4351247 : Blo 1933435 4351247 := bstep (se 1 (by rfl) ⟨3263435, by rfl⟩ : syracuseStep 4351247 = 6526871) B6526871
theorem B2900831 : Blo 1933435 2900831 := bstep (se 1 (by rfl) ⟨2175623, by rfl⟩ : syracuseStep 2900831 = 4351247) B4351247
theorem B1933887 : Blo 1933435 1933887 := bstep (se 1 (by rfl) ⟨1450415, by rfl⟩ : syracuseStep 1933887 = 2900831) B2900831
theorem B2900837 : Blo 1933435 2900837 := bbase (se 4 (by rfl) ⟨271953, by rfl⟩ : syracuseStep 2900837 = 543907) (by norm_num)
theorem B1933891 : Blo 1933435 1933891 := bstep (se 1 (by rfl) ⟨1450418, by rfl⟩ : syracuseStep 1933891 = 2900837) B2900837
theorem B3671381 : Blo 1933435 3671381 := bbase (se 12 (by rfl) ⟨1344, by rfl⟩ : syracuseStep 3671381 = 2689) (by norm_num)
theorem B2447587 : Blo 1933435 2447587 := bstep (se 1 (by rfl) ⟨1835690, by rfl⟩ : syracuseStep 2447587 = 3671381) B3671381
theorem B3263449 : Blo 1933435 3263449 := bstep (se 2 (by rfl) ⟨1223793, by rfl⟩ : syracuseStep 3263449 = 2447587) B2447587
theorem B4351265 : Blo 1933435 4351265 := bstep (se 2 (by rfl) ⟨1631724, by rfl⟩ : syracuseStep 4351265 = 3263449) B3263449
theorem B2900843 : Blo 1933435 2900843 := bstep (se 1 (by rfl) ⟨2175632, by rfl⟩ : syracuseStep 2900843 = 4351265) B4351265
theorem B1933895 : Blo 1933435 1933895 := bstep (se 1 (by rfl) ⟨1450421, by rfl⟩ : syracuseStep 1933895 = 2900843) B2900843
theorem B2175637 : Blo 1933435 2175637 := bbase (se 6 (by rfl) ⟨50991, by rfl⟩ : syracuseStep 2175637 = 101983) (by norm_num)
theorem B2900849 : Blo 1933435 2900849 := bstep (se 2 (by rfl) ⟨1087818, by rfl⟩ : syracuseStep 2900849 = 2175637) B2175637
theorem B1933899 : Blo 1933435 1933899 := bstep (se 1 (by rfl) ⟨1450424, by rfl⟩ : syracuseStep 1933899 = 2900849) B2900849
theorem B2447597 : Blo 1933435 2447597 := bbase (se 3 (by rfl) ⟨458924, by rfl⟩ : syracuseStep 2447597 = 917849) (by norm_num)
theorem B6526925 : Blo 1933435 6526925 := bstep (se 3 (by rfl) ⟨1223798, by rfl⟩ : syracuseStep 6526925 = 2447597) B2447597
theorem B4351283 : Blo 1933435 4351283 := bstep (se 1 (by rfl) ⟨3263462, by rfl⟩ : syracuseStep 4351283 = 6526925) B6526925
theorem B2900855 : Blo 1933435 2900855 := bstep (se 1 (by rfl) ⟨2175641, by rfl⟩ : syracuseStep 2900855 = 4351283) B4351283
theorem B1933903 : Blo 1933435 1933903 := bstep (se 1 (by rfl) ⟨1450427, by rfl⟩ : syracuseStep 1933903 = 2900855) B2900855
theorem B2900861 : Blo 1933435 2900861 := bbase (se 3 (by rfl) ⟨543911, by rfl⟩ : syracuseStep 2900861 = 1087823) (by norm_num)
theorem B1933907 : Blo 1933435 1933907 := bstep (se 1 (by rfl) ⟨1450430, by rfl⟩ : syracuseStep 1933907 = 2900861) B2900861
theorem B4351301 : Blo 1933435 4351301 := bbase (se 4 (by rfl) ⟨407934, by rfl⟩ : syracuseStep 4351301 = 815869) (by norm_num)
theorem B2900867 : Blo 1933435 2900867 := bstep (se 1 (by rfl) ⟨2175650, by rfl⟩ : syracuseStep 2900867 = 4351301) B4351301
theorem B1933911 : Blo 1933435 1933911 := bstep (se 1 (by rfl) ⟨1450433, by rfl⟩ : syracuseStep 1933911 = 2900867) B2900867
theorem B3484981 : Blo 1933435 3484981 := bbase (se 5 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 3484981 = 326717) (by norm_num)
theorem B4646641 : Blo 1933435 4646641 := bstep (se 2 (by rfl) ⟨1742490, by rfl⟩ : syracuseStep 4646641 = 3484981) B3484981
theorem B6195521 : Blo 1933435 6195521 := bstep (se 2 (by rfl) ⟨2323320, by rfl⟩ : syracuseStep 6195521 = 4646641) B4646641
theorem B4130347 : Blo 1933435 4130347 := bstep (se 1 (by rfl) ⟨3097760, by rfl⟩ : syracuseStep 4130347 = 6195521) B6195521
theorem B5507129 : Blo 1933435 5507129 := bstep (se 2 (by rfl) ⟨2065173, by rfl⟩ : syracuseStep 5507129 = 4130347) B4130347
theorem B3671419 : Blo 1933435 3671419 := bstep (se 1 (by rfl) ⟨2753564, by rfl⟩ : syracuseStep 3671419 = 5507129) B5507129
theorem B4895225 : Blo 1933435 4895225 := bstep (se 2 (by rfl) ⟨1835709, by rfl⟩ : syracuseStep 4895225 = 3671419) B3671419
theorem B3263483 : Blo 1933435 3263483 := bstep (se 1 (by rfl) ⟨2447612, by rfl⟩ : syracuseStep 3263483 = 4895225) B4895225
theorem B2175655 : Blo 1933435 2175655 := bstep (se 1 (by rfl) ⟨1631741, by rfl⟩ : syracuseStep 2175655 = 3263483) B3263483
theorem B2900873 : Blo 1933435 2900873 := bstep (se 2 (by rfl) ⟨1087827, by rfl⟩ : syracuseStep 2900873 = 2175655) B2175655
theorem B1933915 : Blo 1933435 1933915 := bstep (se 1 (by rfl) ⟨1450436, by rfl⟩ : syracuseStep 1933915 = 2900873) B2900873
theorem B9790469 : Blo 1933435 9790469 := bbase (se 4 (by rfl) ⟨917856, by rfl⟩ : syracuseStep 9790469 = 1835713) (by norm_num)
theorem B6526979 : Blo 1933435 6526979 := bstep (se 1 (by rfl) ⟨4895234, by rfl⟩ : syracuseStep 6526979 = 9790469) B9790469
theorem B4351319 : Blo 1933435 4351319 := bstep (se 1 (by rfl) ⟨3263489, by rfl⟩ : syracuseStep 4351319 = 6526979) B6526979
theorem B2900879 : Blo 1933435 2900879 := bstep (se 1 (by rfl) ⟨2175659, by rfl⟩ : syracuseStep 2900879 = 4351319) B4351319
theorem B1933919 : Blo 1933435 1933919 := bstep (se 1 (by rfl) ⟨1450439, by rfl⟩ : syracuseStep 1933919 = 2900879) B2900879
theorem B2900885 : Blo 1933435 2900885 := bbase (se 6 (by rfl) ⟨67989, by rfl⟩ : syracuseStep 2900885 = 135979) (by norm_num)
theorem B1933923 : Blo 1933435 1933923 := bstep (se 1 (by rfl) ⟨1450442, by rfl⟩ : syracuseStep 1933923 = 2900885) B2900885
theorem B11014325 : Blo 1933435 11014325 := bbase (se 5 (by rfl) ⟨516296, by rfl⟩ : syracuseStep 11014325 = 1032593) (by norm_num)
theorem B7342883 : Blo 1933435 7342883 := bstep (se 1 (by rfl) ⟨5507162, by rfl⟩ : syracuseStep 7342883 = 11014325) B11014325
theorem B4895255 : Blo 1933435 4895255 := bstep (se 1 (by rfl) ⟨3671441, by rfl⟩ : syracuseStep 4895255 = 7342883) B7342883
theorem B3263503 : Blo 1933435 3263503 := bstep (se 1 (by rfl) ⟨2447627, by rfl⟩ : syracuseStep 3263503 = 4895255) B4895255
theorem B4351337 : Blo 1933435 4351337 := bstep (se 2 (by rfl) ⟨1631751, by rfl⟩ : syracuseStep 4351337 = 3263503) B3263503
theorem B2900891 : Blo 1933435 2900891 := bstep (se 1 (by rfl) ⟨2175668, by rfl⟩ : syracuseStep 2900891 = 4351337) B4351337
theorem B1933927 : Blo 1933435 1933927 := bstep (se 1 (by rfl) ⟨1450445, by rfl⟩ : syracuseStep 1933927 = 2900891) B2900891
theorem B2175673 : Blo 1933435 2175673 := bbase (se 2 (by rfl) ⟨815877, by rfl⟩ : syracuseStep 2175673 = 1631755) (by norm_num)
theorem B2900897 : Blo 1933435 2900897 := bstep (se 2 (by rfl) ⟨1087836, by rfl⟩ : syracuseStep 2900897 = 2175673) B2175673
theorem B1933931 : Blo 1933435 1933931 := bstep (se 1 (by rfl) ⟨1450448, by rfl⟩ : syracuseStep 1933931 = 2900897) B2900897
theorem B4130389 : Blo 1933435 4130389 := bbase (se 8 (by rfl) ⟨24201, by rfl⟩ : syracuseStep 4130389 = 48403) (by norm_num)
theorem B5507185 : Blo 1933435 5507185 := bstep (se 2 (by rfl) ⟨2065194, by rfl⟩ : syracuseStep 5507185 = 4130389) B4130389
theorem B7342913 : Blo 1933435 7342913 := bstep (se 2 (by rfl) ⟨2753592, by rfl⟩ : syracuseStep 7342913 = 5507185) B5507185
theorem B4895275 : Blo 1933435 4895275 := bstep (se 1 (by rfl) ⟨3671456, by rfl⟩ : syracuseStep 4895275 = 7342913) B7342913
theorem B6527033 : Blo 1933435 6527033 := bstep (se 2 (by rfl) ⟨2447637, by rfl⟩ : syracuseStep 6527033 = 4895275) B4895275
theorem B4351355 : Blo 1933435 4351355 := bstep (se 1 (by rfl) ⟨3263516, by rfl⟩ : syracuseStep 4351355 = 6527033) B6527033
theorem B2900903 : Blo 1933435 2900903 := bstep (se 1 (by rfl) ⟨2175677, by rfl⟩ : syracuseStep 2900903 = 4351355) B4351355
theorem B1933935 : Blo 1933435 1933935 := bstep (se 1 (by rfl) ⟨1450451, by rfl⟩ : syracuseStep 1933935 = 2900903) B2900903
theorem B2900909 : Blo 1933435 2900909 := bbase (se 3 (by rfl) ⟨543920, by rfl⟩ : syracuseStep 2900909 = 1087841) (by norm_num)
theorem B1933939 : Blo 1933435 1933939 := bstep (se 1 (by rfl) ⟨1450454, by rfl⟩ : syracuseStep 1933939 = 2900909) B2900909
theorem B4351373 : Blo 1933435 4351373 := bbase (se 3 (by rfl) ⟨815882, by rfl⟩ : syracuseStep 4351373 = 1631765) (by norm_num)
theorem B2900915 : Blo 1933435 2900915 := bstep (se 1 (by rfl) ⟨2175686, by rfl⟩ : syracuseStep 2900915 = 4351373) B4351373
theorem B1933943 : Blo 1933435 1933943 := bstep (se 1 (by rfl) ⟨1450457, by rfl⟩ : syracuseStep 1933943 = 2900915) B2900915
theorem B2447653 : Blo 1933435 2447653 := bbase (se 4 (by rfl) ⟨229467, by rfl⟩ : syracuseStep 2447653 = 458935) (by norm_num)
theorem B3263537 : Blo 1933435 3263537 := bstep (se 2 (by rfl) ⟨1223826, by rfl⟩ : syracuseStep 3263537 = 2447653) B2447653
theorem B2175691 : Blo 1933435 2175691 := bstep (se 1 (by rfl) ⟨1631768, by rfl⟩ : syracuseStep 2175691 = 3263537) B3263537
theorem B2900921 : Blo 1933435 2900921 := bstep (se 2 (by rfl) ⟨1087845, by rfl⟩ : syracuseStep 2900921 = 2175691) B2175691
theorem B1933947 : Blo 1933435 1933947 := bstep (se 1 (by rfl) ⟨1450460, by rfl⟩ : syracuseStep 1933947 = 2900921) B2900921
theorem B5881013 : Blo 1933435 5881013 := bbase (se 5 (by rfl) ⟨275672, by rfl⟩ : syracuseStep 5881013 = 551345) (by norm_num)
theorem B3920675 : Blo 1933435 3920675 := bstep (se 1 (by rfl) ⟨2940506, by rfl⟩ : syracuseStep 3920675 = 5881013) B5881013
theorem B41820533 : Blo 1933435 41820533 := bstep (se 5 (by rfl) ⟨1960337, by rfl⟩ : syracuseStep 41820533 = 3920675) B3920675
theorem B27880355 : Blo 1933435 27880355 := bstep (se 1 (by rfl) ⟨20910266, by rfl⟩ : syracuseStep 27880355 = 41820533) B41820533
theorem B18586903 : Blo 1933435 18586903 := bstep (se 1 (by rfl) ⟨13940177, by rfl⟩ : syracuseStep 18586903 = 27880355) B27880355
theorem B24782537 : Blo 1933435 24782537 := bstep (se 2 (by rfl) ⟨9293451, by rfl⟩ : syracuseStep 24782537 = 18586903) B18586903
theorem B16521691 : Blo 1933435 16521691 := bstep (se 1 (by rfl) ⟨12391268, by rfl⟩ : syracuseStep 16521691 = 24782537) B24782537
theorem B22028921 : Blo 1933435 22028921 := bstep (se 2 (by rfl) ⟨8260845, by rfl⟩ : syracuseStep 22028921 = 16521691) B16521691
theorem B14685947 : Blo 1933435 14685947 := bstep (se 1 (by rfl) ⟨11014460, by rfl⟩ : syracuseStep 14685947 = 22028921) B22028921
theorem B9790631 : Blo 1933435 9790631 := bstep (se 1 (by rfl) ⟨7342973, by rfl⟩ : syracuseStep 9790631 = 14685947) B14685947
theorem B6527087 : Blo 1933435 6527087 := bstep (se 1 (by rfl) ⟨4895315, by rfl⟩ : syracuseStep 6527087 = 9790631) B9790631
theorem B4351391 : Blo 1933435 4351391 := bstep (se 1 (by rfl) ⟨3263543, by rfl⟩ : syracuseStep 4351391 = 6527087) B6527087
theorem B2900927 : Blo 1933435 2900927 := bstep (se 1 (by rfl) ⟨2175695, by rfl⟩ : syracuseStep 2900927 = 4351391) B4351391
theorem B1933951 : Blo 1933435 1933951 := bstep (se 1 (by rfl) ⟨1450463, by rfl⟩ : syracuseStep 1933951 = 2900927) B2900927
theorem B2900933 : Blo 1933435 2900933 := bbase (se 4 (by rfl) ⟨271962, by rfl⟩ : syracuseStep 2900933 = 543925) (by norm_num)
theorem B1933955 : Blo 1933435 1933955 := bstep (se 1 (by rfl) ⟨1450466, by rfl⟩ : syracuseStep 1933955 = 2900933) B2900933
theorem B3263557 : Blo 1933435 3263557 := bbase (se 4 (by rfl) ⟨305958, by rfl⟩ : syracuseStep 3263557 = 611917) (by norm_num)
theorem B4351409 : Blo 1933435 4351409 := bstep (se 2 (by rfl) ⟨1631778, by rfl⟩ : syracuseStep 4351409 = 3263557) B3263557
theorem B2900939 : Blo 1933435 2900939 := bstep (se 1 (by rfl) ⟨2175704, by rfl⟩ : syracuseStep 2900939 = 4351409) B4351409
theorem B1933959 : Blo 1933435 1933959 := bstep (se 1 (by rfl) ⟨1450469, by rfl⟩ : syracuseStep 1933959 = 2900939) B2900939
theorem B2175709 : Blo 1933435 2175709 := bbase (se 3 (by rfl) ⟨407945, by rfl⟩ : syracuseStep 2175709 = 815891) (by norm_num)
theorem B2900945 : Blo 1933435 2900945 := bstep (se 2 (by rfl) ⟨1087854, by rfl⟩ : syracuseStep 2900945 = 2175709) B2175709
theorem B1933963 : Blo 1933435 1933963 := bstep (se 1 (by rfl) ⟨1450472, by rfl⟩ : syracuseStep 1933963 = 2900945) B2900945
theorem B6527141 : Blo 1933435 6527141 := bbase (se 4 (by rfl) ⟨611919, by rfl⟩ : syracuseStep 6527141 = 1223839) (by norm_num)
theorem B4351427 : Blo 1933435 4351427 := bstep (se 1 (by rfl) ⟨3263570, by rfl⟩ : syracuseStep 4351427 = 6527141) B6527141
theorem B2900951 : Blo 1933435 2900951 := bstep (se 1 (by rfl) ⟨2175713, by rfl⟩ : syracuseStep 2900951 = 4351427) B4351427
theorem B1933967 : Blo 1933435 1933967 := bstep (se 1 (by rfl) ⟨1450475, by rfl⟩ : syracuseStep 1933967 = 2900951) B2900951
theorem B2900957 : Blo 1933435 2900957 := bbase (se 3 (by rfl) ⟨543929, by rfl⟩ : syracuseStep 2900957 = 1087859) (by norm_num)
theorem B1933971 : Blo 1933435 1933971 := bstep (se 1 (by rfl) ⟨1450478, by rfl⟩ : syracuseStep 1933971 = 2900957) B2900957
theorem B4351445 : Blo 1933435 4351445 := bbase (se 7 (by rfl) ⟨50993, by rfl⟩ : syracuseStep 4351445 = 101987) (by norm_num)
theorem B2900963 : Blo 1933435 2900963 := bstep (se 1 (by rfl) ⟨2175722, by rfl⟩ : syracuseStep 2900963 = 4351445) B4351445
theorem B1933975 : Blo 1933435 1933975 := bstep (se 1 (by rfl) ⟨1450481, by rfl⟩ : syracuseStep 1933975 = 2900963) B2900963
theorem B3399005 : Blo 1933435 3399005 := bbase (se 3 (by rfl) ⟨637313, by rfl⟩ : syracuseStep 3399005 = 1274627) (by norm_num)
theorem B2266003 : Blo 1933435 2266003 := bstep (se 1 (by rfl) ⟨1699502, by rfl⟩ : syracuseStep 2266003 = 3399005) B3399005
theorem B3021337 : Blo 1933435 3021337 := bstep (se 2 (by rfl) ⟨1133001, by rfl⟩ : syracuseStep 3021337 = 2266003) B2266003
theorem B4028449 : Blo 1933435 4028449 := bstep (se 2 (by rfl) ⟨1510668, by rfl⟩ : syracuseStep 4028449 = 3021337) B3021337
theorem B5371265 : Blo 1933435 5371265 := bstep (se 2 (by rfl) ⟨2014224, by rfl⟩ : syracuseStep 5371265 = 4028449) B4028449
theorem B3580843 : Blo 1933435 3580843 := bstep (se 1 (by rfl) ⟨2685632, by rfl⟩ : syracuseStep 3580843 = 5371265) B5371265
theorem B4774457 : Blo 1933435 4774457 := bstep (se 2 (by rfl) ⟨1790421, by rfl⟩ : syracuseStep 4774457 = 3580843) B3580843
theorem B3182971 : Blo 1933435 3182971 := bstep (se 1 (by rfl) ⟨2387228, by rfl⟩ : syracuseStep 3182971 = 4774457) B4774457
theorem B4243961 : Blo 1933435 4243961 := bstep (se 2 (by rfl) ⟨1591485, by rfl⟩ : syracuseStep 4243961 = 3182971) B3182971
theorem B11317229 : Blo 1933435 11317229 := bstep (se 3 (by rfl) ⟨2121980, by rfl⟩ : syracuseStep 11317229 = 4243961) B4243961
theorem B7544819 : Blo 1933435 7544819 := bstep (se 1 (by rfl) ⟨5658614, by rfl⟩ : syracuseStep 7544819 = 11317229) B11317229
theorem B5029879 : Blo 1933435 5029879 := bstep (se 1 (by rfl) ⟨3772409, by rfl⟩ : syracuseStep 5029879 = 7544819) B7544819
theorem B6706505 : Blo 1933435 6706505 := bstep (se 2 (by rfl) ⟨2514939, by rfl⟩ : syracuseStep 6706505 = 5029879) B5029879
theorem B4471003 : Blo 1933435 4471003 := bstep (se 1 (by rfl) ⟨3353252, by rfl⟩ : syracuseStep 4471003 = 6706505) B6706505
theorem B5961337 : Blo 1933435 5961337 := bstep (se 2 (by rfl) ⟨2235501, by rfl⟩ : syracuseStep 5961337 = 4471003) B4471003
theorem B127175189 : Blo 1933435 127175189 := bstep (se 6 (by rfl) ⟨2980668, by rfl⟩ : syracuseStep 127175189 = 5961337) B5961337
theorem B339133837 : Blo 1933435 339133837 := bstep (se 3 (by rfl) ⟨63587594, by rfl⟩ : syracuseStep 339133837 = 127175189) B127175189
theorem B452178449 : Blo 1933435 452178449 := bstep (se 2 (by rfl) ⟨169566918, by rfl⟩ : syracuseStep 452178449 = 339133837) B339133837
theorem B301452299 : Blo 1933435 301452299 := bstep (se 1 (by rfl) ⟨226089224, by rfl⟩ : syracuseStep 301452299 = 452178449) B452178449
theorem B200968199 : Blo 1933435 200968199 := bstep (se 1 (by rfl) ⟨150726149, by rfl⟩ : syracuseStep 200968199 = 301452299) B301452299
theorem B133978799 : Blo 1933435 133978799 := bstep (se 1 (by rfl) ⟨100484099, by rfl⟩ : syracuseStep 133978799 = 200968199) B200968199
theorem B89319199 : Blo 1933435 89319199 := bstep (se 1 (by rfl) ⟨66989399, by rfl⟩ : syracuseStep 89319199 = 133978799) B133978799
theorem B119092265 : Blo 1933435 119092265 := bstep (se 2 (by rfl) ⟨44659599, by rfl⟩ : syracuseStep 119092265 = 89319199) B89319199
theorem B79394843 : Blo 1933435 79394843 := bstep (se 1 (by rfl) ⟨59546132, by rfl⟩ : syracuseStep 79394843 = 119092265) B119092265
theorem B52929895 : Blo 1933435 52929895 := bstep (se 1 (by rfl) ⟨39697421, by rfl⟩ : syracuseStep 52929895 = 79394843) B79394843
theorem B70573193 : Blo 1933435 70573193 := bstep (se 2 (by rfl) ⟨26464947, by rfl⟩ : syracuseStep 70573193 = 52929895) B52929895
theorem B47048795 : Blo 1933435 47048795 := bstep (se 1 (by rfl) ⟨35286596, by rfl⟩ : syracuseStep 47048795 = 70573193) B70573193
theorem B31365863 : Blo 1933435 31365863 := bstep (se 1 (by rfl) ⟨23524397, by rfl⟩ : syracuseStep 31365863 = 47048795) B47048795
theorem B20910575 : Blo 1933435 20910575 := bstep (se 1 (by rfl) ⟨15682931, by rfl⟩ : syracuseStep 20910575 = 31365863) B31365863
theorem B13940383 : Blo 1933435 13940383 := bstep (se 1 (by rfl) ⟨10455287, by rfl⟩ : syracuseStep 13940383 = 20910575) B20910575
theorem B18587177 : Blo 1933435 18587177 := bstep (se 2 (by rfl) ⟨6970191, by rfl⟩ : syracuseStep 18587177 = 13940383) B13940383
theorem B12391451 : Blo 1933435 12391451 := bstep (se 1 (by rfl) ⟨9293588, by rfl⟩ : syracuseStep 12391451 = 18587177) B18587177
theorem B8260967 : Blo 1933435 8260967 := bstep (se 1 (by rfl) ⟨6195725, by rfl⟩ : syracuseStep 8260967 = 12391451) B12391451
theorem B5507311 : Blo 1933435 5507311 := bstep (se 1 (by rfl) ⟨4130483, by rfl⟩ : syracuseStep 5507311 = 8260967) B8260967
theorem B7343081 : Blo 1933435 7343081 := bstep (se 2 (by rfl) ⟨2753655, by rfl⟩ : syracuseStep 7343081 = 5507311) B5507311
theorem B4895387 : Blo 1933435 4895387 := bstep (se 1 (by rfl) ⟨3671540, by rfl⟩ : syracuseStep 4895387 = 7343081) B7343081
theorem B3263591 : Blo 1933435 3263591 := bstep (se 1 (by rfl) ⟨2447693, by rfl⟩ : syracuseStep 3263591 = 4895387) B4895387
theorem B2175727 : Blo 1933435 2175727 := bstep (se 1 (by rfl) ⟨1631795, by rfl⟩ : syracuseStep 2175727 = 3263591) B3263591
theorem B2900969 : Blo 1933435 2900969 := bstep (se 2 (by rfl) ⟨1087863, by rfl⟩ : syracuseStep 2900969 = 2175727) B2175727
theorem B1933979 : Blo 1933435 1933979 := bstep (se 1 (by rfl) ⟨1450484, by rfl⟩ : syracuseStep 1933979 = 2900969) B2900969
theorem B3920741 : Blo 1933435 3920741 := bbase (se 4 (by rfl) ⟨367569, by rfl⟩ : syracuseStep 3920741 = 735139) (by norm_num)
theorem B2613827 : Blo 1933435 2613827 := bstep (se 1 (by rfl) ⟨1960370, by rfl⟩ : syracuseStep 2613827 = 3920741) B3920741
theorem B6970205 : Blo 1933435 6970205 := bstep (se 3 (by rfl) ⟨1306913, by rfl⟩ : syracuseStep 6970205 = 2613827) B2613827
theorem B4646803 : Blo 1933435 4646803 := bstep (se 1 (by rfl) ⟨3485102, by rfl⟩ : syracuseStep 4646803 = 6970205) B6970205
theorem B6195737 : Blo 1933435 6195737 := bstep (se 2 (by rfl) ⟨2323401, by rfl⟩ : syracuseStep 6195737 = 4646803) B4646803
theorem B16521965 : Blo 1933435 16521965 := bstep (se 3 (by rfl) ⟨3097868, by rfl⟩ : syracuseStep 16521965 = 6195737) B6195737
theorem B11014643 : Blo 1933435 11014643 := bstep (se 1 (by rfl) ⟨8260982, by rfl⟩ : syracuseStep 11014643 = 16521965) B16521965
theorem B7343095 : Blo 1933435 7343095 := bstep (se 1 (by rfl) ⟨5507321, by rfl⟩ : syracuseStep 7343095 = 11014643) B11014643
theorem B9790793 : Blo 1933435 9790793 := bstep (se 2 (by rfl) ⟨3671547, by rfl⟩ : syracuseStep 9790793 = 7343095) B7343095
theorem B6527195 : Blo 1933435 6527195 := bstep (se 1 (by rfl) ⟨4895396, by rfl⟩ : syracuseStep 6527195 = 9790793) B9790793
theorem B4351463 : Blo 1933435 4351463 := bstep (se 1 (by rfl) ⟨3263597, by rfl⟩ : syracuseStep 4351463 = 6527195) B6527195
theorem B2900975 : Blo 1933435 2900975 := bstep (se 1 (by rfl) ⟨2175731, by rfl⟩ : syracuseStep 2900975 = 4351463) B4351463
theorem B1933983 : Blo 1933435 1933983 := bstep (se 1 (by rfl) ⟨1450487, by rfl⟩ : syracuseStep 1933983 = 2900975) B2900975
theorem B2900981 : Blo 1933435 2900981 := bbase (se 5 (by rfl) ⟨135983, by rfl⟩ : syracuseStep 2900981 = 271967) (by norm_num)
theorem B1933987 : Blo 1933435 1933987 := bstep (se 1 (by rfl) ⟨1450490, by rfl⟩ : syracuseStep 1933987 = 2900981) B2900981
theorem B4130509 : Blo 1933435 4130509 := bbase (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) (by norm_num)
theorem B5507345 : Blo 1933435 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B3671563 : Blo 1933435 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B4895417 : Blo 1933435 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B3263611 : Blo 1933435 3263611 := bstep (se 1 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 3263611 = 4895417) B4895417
theorem B4351481 : Blo 1933435 4351481 := bstep (se 2 (by rfl) ⟨1631805, by rfl⟩ : syracuseStep 4351481 = 3263611) B3263611
theorem B2900987 : Blo 1933435 2900987 := bstep (se 1 (by rfl) ⟨2175740, by rfl⟩ : syracuseStep 2900987 = 4351481) B4351481
theorem B1933991 : Blo 1933435 1933991 := bstep (se 1 (by rfl) ⟨1450493, by rfl⟩ : syracuseStep 1933991 = 2900987) B2900987
theorem B2175745 : Blo 1933435 2175745 := bbase (se 2 (by rfl) ⟨815904, by rfl⟩ : syracuseStep 2175745 = 1631809) (by norm_num)
theorem B2900993 : Blo 1933435 2900993 := bstep (se 2 (by rfl) ⟨1087872, by rfl⟩ : syracuseStep 2900993 = 2175745) B2175745
theorem B1933995 : Blo 1933435 1933995 := bstep (se 1 (by rfl) ⟨1450496, by rfl⟩ : syracuseStep 1933995 = 2900993) B2900993
theorem B4895437 : Blo 1933435 4895437 := bbase (se 3 (by rfl) ⟨917894, by rfl⟩ : syracuseStep 4895437 = 1835789) (by norm_num)
theorem B6527249 : Blo 1933435 6527249 := bstep (se 2 (by rfl) ⟨2447718, by rfl⟩ : syracuseStep 6527249 = 4895437) B4895437
theorem B4351499 : Blo 1933435 4351499 := bstep (se 1 (by rfl) ⟨3263624, by rfl⟩ : syracuseStep 4351499 = 6527249) B6527249
theorem B2900999 : Blo 1933435 2900999 := bstep (se 1 (by rfl) ⟨2175749, by rfl⟩ : syracuseStep 2900999 = 4351499) B4351499
theorem B1933999 : Blo 1933435 1933999 := bstep (se 1 (by rfl) ⟨1450499, by rfl⟩ : syracuseStep 1933999 = 2900999) B2900999
theorem B2901005 : Blo 1933435 2901005 := bbase (se 3 (by rfl) ⟨543938, by rfl⟩ : syracuseStep 2901005 = 1087877) (by norm_num)
theorem B1934003 : Blo 1933435 1934003 := bstep (se 1 (by rfl) ⟨1450502, by rfl⟩ : syracuseStep 1934003 = 2901005) B2901005
theorem B4351517 : Blo 1933435 4351517 := bbase (se 3 (by rfl) ⟨815909, by rfl⟩ : syracuseStep 4351517 = 1631819) (by norm_num)
theorem B2901011 : Blo 1933435 2901011 := bstep (se 1 (by rfl) ⟨2175758, by rfl⟩ : syracuseStep 2901011 = 4351517) B4351517
theorem B1934007 : Blo 1933435 1934007 := bstep (se 1 (by rfl) ⟨1450505, by rfl⟩ : syracuseStep 1934007 = 2901011) B2901011
theorem B3263645 : Blo 1933435 3263645 := bbase (se 3 (by rfl) ⟨611933, by rfl⟩ : syracuseStep 3263645 = 1223867) (by norm_num)
theorem B2175763 : Blo 1933435 2175763 := bstep (se 1 (by rfl) ⟨1631822, by rfl⟩ : syracuseStep 2175763 = 3263645) B3263645
theorem B2901017 : Blo 1933435 2901017 := bstep (se 2 (by rfl) ⟨1087881, by rfl⟩ : syracuseStep 2901017 = 2175763) B2175763
theorem B1934011 : Blo 1933435 1934011 := bstep (se 1 (by rfl) ⟨1450508, by rfl⟩ : syracuseStep 1934011 = 2901017) B2901017
theorem B8373829 : Blo 1933435 8373829 := bbase (se 4 (by rfl) ⟨785046, by rfl⟩ : syracuseStep 8373829 = 1570093) (by norm_num)
theorem B11165105 : Blo 1933435 11165105 := bstep (se 2 (by rfl) ⟨4186914, by rfl⟩ : syracuseStep 11165105 = 8373829) B8373829
theorem B29773613 : Blo 1933435 29773613 := bstep (se 3 (by rfl) ⟨5582552, by rfl⟩ : syracuseStep 29773613 = 11165105) B11165105
theorem B79396301 : Blo 1933435 79396301 := bstep (se 3 (by rfl) ⟨14886806, by rfl⟩ : syracuseStep 79396301 = 29773613) B29773613
theorem B211723469 : Blo 1933435 211723469 := bstep (se 3 (by rfl) ⟨39698150, by rfl⟩ : syracuseStep 211723469 = 79396301) B79396301
theorem B141148979 : Blo 1933435 141148979 := bstep (se 1 (by rfl) ⟨105861734, by rfl⟩ : syracuseStep 141148979 = 211723469) B211723469
theorem B94099319 : Blo 1933435 94099319 := bstep (se 1 (by rfl) ⟨70574489, by rfl⟩ : syracuseStep 94099319 = 141148979) B141148979
theorem B62732879 : Blo 1933435 62732879 := bstep (se 1 (by rfl) ⟨47049659, by rfl⟩ : syracuseStep 62732879 = 94099319) B94099319
theorem B41821919 : Blo 1933435 41821919 := bstep (se 1 (by rfl) ⟨31366439, by rfl⟩ : syracuseStep 41821919 = 62732879) B62732879
theorem B27881279 : Blo 1933435 27881279 := bstep (se 1 (by rfl) ⟨20910959, by rfl⟩ : syracuseStep 27881279 = 41821919) B41821919
theorem B18587519 : Blo 1933435 18587519 := bstep (se 1 (by rfl) ⟨13940639, by rfl⟩ : syracuseStep 18587519 = 27881279) B27881279
theorem B12391679 : Blo 1933435 12391679 := bstep (se 1 (by rfl) ⟨9293759, by rfl⟩ : syracuseStep 12391679 = 18587519) B18587519
theorem B8261119 : Blo 1933435 8261119 := bstep (se 1 (by rfl) ⟨6195839, by rfl⟩ : syracuseStep 8261119 = 12391679) B12391679
theorem B11014825 : Blo 1933435 11014825 := bstep (se 2 (by rfl) ⟨4130559, by rfl⟩ : syracuseStep 11014825 = 8261119) B8261119
theorem B14686433 : Blo 1933435 14686433 := bstep (se 2 (by rfl) ⟨5507412, by rfl⟩ : syracuseStep 14686433 = 11014825) B11014825
theorem B9790955 : Blo 1933435 9790955 := bstep (se 1 (by rfl) ⟨7343216, by rfl⟩ : syracuseStep 9790955 = 14686433) B14686433
theorem B6527303 : Blo 1933435 6527303 := bstep (se 1 (by rfl) ⟨4895477, by rfl⟩ : syracuseStep 6527303 = 9790955) B9790955
theorem B4351535 : Blo 1933435 4351535 := bstep (se 1 (by rfl) ⟨3263651, by rfl⟩ : syracuseStep 4351535 = 6527303) B6527303
theorem B2901023 : Blo 1933435 2901023 := bstep (se 1 (by rfl) ⟨2175767, by rfl⟩ : syracuseStep 2901023 = 4351535) B4351535
theorem B1934015 : Blo 1933435 1934015 := bstep (se 1 (by rfl) ⟨1450511, by rfl⟩ : syracuseStep 1934015 = 2901023) B2901023
theorem B2901029 : Blo 1933435 2901029 := bbase (se 4 (by rfl) ⟨271971, by rfl⟩ : syracuseStep 2901029 = 543943) (by norm_num)
theorem B1934019 : Blo 1933435 1934019 := bstep (se 1 (by rfl) ⟨1450514, by rfl⟩ : syracuseStep 1934019 = 2901029) B2901029
theorem B2447749 : Blo 1933435 2447749 := bbase (se 4 (by rfl) ⟨229476, by rfl⟩ : syracuseStep 2447749 = 458953) (by norm_num)
theorem B3263665 : Blo 1933435 3263665 := bstep (se 2 (by rfl) ⟨1223874, by rfl⟩ : syracuseStep 3263665 = 2447749) B2447749
theorem B4351553 : Blo 1933435 4351553 := bstep (se 2 (by rfl) ⟨1631832, by rfl⟩ : syracuseStep 4351553 = 3263665) B3263665
theorem B2901035 : Blo 1933435 2901035 := bstep (se 1 (by rfl) ⟨2175776, by rfl⟩ : syracuseStep 2901035 = 4351553) B4351553
theorem B1934023 : Blo 1933435 1934023 := bstep (se 1 (by rfl) ⟨1450517, by rfl⟩ : syracuseStep 1934023 = 2901035) B2901035
theorem B2175781 : Blo 1933435 2175781 := bbase (se 4 (by rfl) ⟨203979, by rfl⟩ : syracuseStep 2175781 = 407959) (by norm_num)
theorem B2901041 : Blo 1933435 2901041 := bstep (se 2 (by rfl) ⟨1087890, by rfl⟩ : syracuseStep 2901041 = 2175781) B2175781
theorem B1934027 : Blo 1933435 1934027 := bstep (se 1 (by rfl) ⟨1450520, by rfl⟩ : syracuseStep 1934027 = 2901041) B2901041
theorem B8261189 : Blo 1933435 8261189 := bbase (se 4 (by rfl) ⟨774486, by rfl⟩ : syracuseStep 8261189 = 1548973) (by norm_num)
theorem B5507459 : Blo 1933435 5507459 := bstep (se 1 (by rfl) ⟨4130594, by rfl⟩ : syracuseStep 5507459 = 8261189) B8261189
theorem B3671639 : Blo 1933435 3671639 := bstep (se 1 (by rfl) ⟨2753729, by rfl⟩ : syracuseStep 3671639 = 5507459) B5507459
theorem B2447759 : Blo 1933435 2447759 := bstep (se 1 (by rfl) ⟨1835819, by rfl⟩ : syracuseStep 2447759 = 3671639) B3671639
theorem B6527357 : Blo 1933435 6527357 := bstep (se 3 (by rfl) ⟨1223879, by rfl⟩ : syracuseStep 6527357 = 2447759) B2447759
theorem B4351571 : Blo 1933435 4351571 := bstep (se 1 (by rfl) ⟨3263678, by rfl⟩ : syracuseStep 4351571 = 6527357) B6527357
theorem B2901047 : Blo 1933435 2901047 := bstep (se 1 (by rfl) ⟨2175785, by rfl⟩ : syracuseStep 2901047 = 4351571) B4351571
theorem B1934031 : Blo 1933435 1934031 := bstep (se 1 (by rfl) ⟨1450523, by rfl⟩ : syracuseStep 1934031 = 2901047) B2901047
theorem B2901053 : Blo 1933435 2901053 := bbase (se 3 (by rfl) ⟨543947, by rfl⟩ : syracuseStep 2901053 = 1087895) (by norm_num)
theorem B1934035 : Blo 1933435 1934035 := bstep (se 1 (by rfl) ⟨1450526, by rfl⟩ : syracuseStep 1934035 = 2901053) B2901053
theorem B4351589 : Blo 1933435 4351589 := bbase (se 4 (by rfl) ⟨407961, by rfl⟩ : syracuseStep 4351589 = 815923) (by norm_num)
theorem B2901059 : Blo 1933435 2901059 := bstep (se 1 (by rfl) ⟨2175794, by rfl⟩ : syracuseStep 2901059 = 4351589) B4351589
theorem B1934039 : Blo 1933435 1934039 := bstep (se 1 (by rfl) ⟨1450529, by rfl⟩ : syracuseStep 1934039 = 2901059) B2901059
theorem B4895549 : Blo 1933435 4895549 := bbase (se 3 (by rfl) ⟨917915, by rfl⟩ : syracuseStep 4895549 = 1835831) (by norm_num)
theorem B3263699 : Blo 1933435 3263699 := bstep (se 1 (by rfl) ⟨2447774, by rfl⟩ : syracuseStep 3263699 = 4895549) B4895549
theorem B2175799 : Blo 1933435 2175799 := bstep (se 1 (by rfl) ⟨1631849, by rfl⟩ : syracuseStep 2175799 = 3263699) B3263699
theorem B2901065 : Blo 1933435 2901065 := bstep (se 2 (by rfl) ⟨1087899, by rfl⟩ : syracuseStep 2901065 = 2175799) B2175799
theorem B1934043 : Blo 1933435 1934043 := bstep (se 1 (by rfl) ⟨1450532, by rfl⟩ : syracuseStep 1934043 = 2901065) B2901065
theorem B3671669 : Blo 1933435 3671669 := bbase (se 5 (by rfl) ⟨172109, by rfl⟩ : syracuseStep 3671669 = 344219) (by norm_num)
theorem B9791117 : Blo 1933435 9791117 := bstep (se 3 (by rfl) ⟨1835834, by rfl⟩ : syracuseStep 9791117 = 3671669) B3671669
theorem B6527411 : Blo 1933435 6527411 := bstep (se 1 (by rfl) ⟨4895558, by rfl⟩ : syracuseStep 6527411 = 9791117) B9791117
theorem B4351607 : Blo 1933435 4351607 := bstep (se 1 (by rfl) ⟨3263705, by rfl⟩ : syracuseStep 4351607 = 6527411) B6527411
theorem B2901071 : Blo 1933435 2901071 := bstep (se 1 (by rfl) ⟨2175803, by rfl⟩ : syracuseStep 2901071 = 4351607) B4351607
theorem B1934047 : Blo 1933435 1934047 := bstep (se 1 (by rfl) ⟨1450535, by rfl⟩ : syracuseStep 1934047 = 2901071) B2901071
theorem B2901077 : Blo 1933435 2901077 := bbase (se 8 (by rfl) ⟨16998, by rfl⟩ : syracuseStep 2901077 = 33997) (by norm_num)
theorem B1934051 : Blo 1933435 1934051 := bstep (se 1 (by rfl) ⟨1450538, by rfl⟩ : syracuseStep 1934051 = 2901077) B2901077
theorem B3721781 : Blo 1933435 3721781 := bbase (se 5 (by rfl) ⟨174458, by rfl⟩ : syracuseStep 3721781 = 348917) (by norm_num)
theorem B2481187 : Blo 1933435 2481187 := bstep (se 1 (by rfl) ⟨1860890, by rfl⟩ : syracuseStep 2481187 = 3721781) B3721781
theorem B3308249 : Blo 1933435 3308249 := bstep (se 2 (by rfl) ⟨1240593, by rfl⟩ : syracuseStep 3308249 = 2481187) B2481187
theorem B8821997 : Blo 1933435 8821997 := bstep (se 3 (by rfl) ⟨1654124, by rfl⟩ : syracuseStep 8821997 = 3308249) B3308249
theorem B5881331 : Blo 1933435 5881331 := bstep (se 1 (by rfl) ⟨4410998, by rfl⟩ : syracuseStep 5881331 = 8821997) B8821997
theorem B3920887 : Blo 1933435 3920887 := bstep (se 1 (by rfl) ⟨2940665, by rfl⟩ : syracuseStep 3920887 = 5881331) B5881331
theorem B5227849 : Blo 1933435 5227849 := bstep (se 2 (by rfl) ⟨1960443, by rfl⟩ : syracuseStep 5227849 = 3920887) B3920887
theorem B6970465 : Blo 1933435 6970465 := bstep (se 2 (by rfl) ⟨2613924, by rfl⟩ : syracuseStep 6970465 = 5227849) B5227849
theorem B9293953 : Blo 1933435 9293953 := bstep (se 2 (by rfl) ⟨3485232, by rfl⟩ : syracuseStep 9293953 = 6970465) B6970465
theorem B12391937 : Blo 1933435 12391937 := bstep (se 2 (by rfl) ⟨4646976, by rfl⟩ : syracuseStep 12391937 = 9293953) B9293953
theorem B8261291 : Blo 1933435 8261291 := bstep (se 1 (by rfl) ⟨6195968, by rfl⟩ : syracuseStep 8261291 = 12391937) B12391937
theorem B5507527 : Blo 1933435 5507527 := bstep (se 1 (by rfl) ⟨4130645, by rfl⟩ : syracuseStep 5507527 = 8261291) B8261291
theorem B7343369 : Blo 1933435 7343369 := bstep (se 2 (by rfl) ⟨2753763, by rfl⟩ : syracuseStep 7343369 = 5507527) B5507527
theorem B4895579 : Blo 1933435 4895579 := bstep (se 1 (by rfl) ⟨3671684, by rfl⟩ : syracuseStep 4895579 = 7343369) B7343369
theorem B3263719 : Blo 1933435 3263719 := bstep (se 1 (by rfl) ⟨2447789, by rfl⟩ : syracuseStep 3263719 = 4895579) B4895579
theorem B4351625 : Blo 1933435 4351625 := bstep (se 2 (by rfl) ⟨1631859, by rfl⟩ : syracuseStep 4351625 = 3263719) B3263719
theorem B2901083 : Blo 1933435 2901083 := bstep (se 1 (by rfl) ⟨2175812, by rfl⟩ : syracuseStep 2901083 = 4351625) B4351625
theorem B1934055 : Blo 1933435 1934055 := bstep (se 1 (by rfl) ⟨1450541, by rfl⟩ : syracuseStep 1934055 = 2901083) B2901083
theorem B2175817 : Blo 1933435 2175817 := bbase (se 2 (by rfl) ⟨815931, by rfl⟩ : syracuseStep 2175817 = 1631863) (by norm_num)
theorem B2901089 : Blo 1933435 2901089 := bstep (se 2 (by rfl) ⟨1087908, by rfl⟩ : syracuseStep 2901089 = 2175817) B2175817
theorem B1934059 : Blo 1933435 1934059 := bstep (se 1 (by rfl) ⟨1450544, by rfl⟩ : syracuseStep 1934059 = 2901089) B2901089
theorem B2481197 : Blo 1933435 2481197 := bbase (se 3 (by rfl) ⟨465224, by rfl⟩ : syracuseStep 2481197 = 930449) (by norm_num)
theorem B6616525 : Blo 1933435 6616525 := bstep (se 3 (by rfl) ⟨1240598, by rfl⟩ : syracuseStep 6616525 = 2481197) B2481197
theorem B8822033 : Blo 1933435 8822033 := bstep (se 2 (by rfl) ⟨3308262, by rfl⟩ : syracuseStep 8822033 = 6616525) B6616525
theorem B5881355 : Blo 1933435 5881355 := bstep (se 1 (by rfl) ⟨4411016, by rfl⟩ : syracuseStep 5881355 = 8822033) B8822033
theorem B3920903 : Blo 1933435 3920903 := bstep (se 1 (by rfl) ⟨2940677, by rfl⟩ : syracuseStep 3920903 = 5881355) B5881355
theorem B2613935 : Blo 1933435 2613935 := bstep (se 1 (by rfl) ⟨1960451, by rfl⟩ : syracuseStep 2613935 = 3920903) B3920903
theorem B6970493 : Blo 1933435 6970493 := bstep (se 3 (by rfl) ⟨1306967, by rfl⟩ : syracuseStep 6970493 = 2613935) B2613935
theorem B18587981 : Blo 1933435 18587981 := bstep (se 3 (by rfl) ⟨3485246, by rfl⟩ : syracuseStep 18587981 = 6970493) B6970493
theorem B12391987 : Blo 1933435 12391987 := bstep (se 1 (by rfl) ⟨9293990, by rfl⟩ : syracuseStep 12391987 = 18587981) B18587981
theorem B16522649 : Blo 1933435 16522649 := bstep (se 2 (by rfl) ⟨6195993, by rfl⟩ : syracuseStep 16522649 = 12391987) B12391987
theorem B11015099 : Blo 1933435 11015099 := bstep (se 1 (by rfl) ⟨8261324, by rfl⟩ : syracuseStep 11015099 = 16522649) B16522649
theorem B7343399 : Blo 1933435 7343399 := bstep (se 1 (by rfl) ⟨5507549, by rfl⟩ : syracuseStep 7343399 = 11015099) B11015099
theorem B4895599 : Blo 1933435 4895599 := bstep (se 1 (by rfl) ⟨3671699, by rfl⟩ : syracuseStep 4895599 = 7343399) B7343399
theorem B6527465 : Blo 1933435 6527465 := bstep (se 2 (by rfl) ⟨2447799, by rfl⟩ : syracuseStep 6527465 = 4895599) B4895599
theorem B4351643 : Blo 1933435 4351643 := bstep (se 1 (by rfl) ⟨3263732, by rfl⟩ : syracuseStep 4351643 = 6527465) B6527465
theorem B2901095 : Blo 1933435 2901095 := bstep (se 1 (by rfl) ⟨2175821, by rfl⟩ : syracuseStep 2901095 = 4351643) B4351643
theorem B1934063 : Blo 1933435 1934063 := bstep (se 1 (by rfl) ⟨1450547, by rfl⟩ : syracuseStep 1934063 = 2901095) B2901095
theorem B2901101 : Blo 1933435 2901101 := bbase (se 3 (by rfl) ⟨543956, by rfl⟩ : syracuseStep 2901101 = 1087913) (by norm_num)
theorem B1934067 : Blo 1933435 1934067 := bstep (se 1 (by rfl) ⟨1450550, by rfl⟩ : syracuseStep 1934067 = 2901101) B2901101
theorem B4351661 : Blo 1933435 4351661 := bbase (se 3 (by rfl) ⟨815936, by rfl⟩ : syracuseStep 4351661 = 1631873) (by norm_num)
theorem B2901107 : Blo 1933435 2901107 := bstep (se 1 (by rfl) ⟨2175830, by rfl⟩ : syracuseStep 2901107 = 4351661) B4351661
theorem B1934071 : Blo 1933435 1934071 := bstep (se 1 (by rfl) ⟨1450553, by rfl⟩ : syracuseStep 1934071 = 2901107) B2901107
theorem B2323513 : Blo 1933435 2323513 := bbase (se 2 (by rfl) ⟨871317, by rfl⟩ : syracuseStep 2323513 = 1742635) (by norm_num)
theorem B3098017 : Blo 1933435 3098017 := bstep (se 2 (by rfl) ⟨1161756, by rfl⟩ : syracuseStep 3098017 = 2323513) B2323513
theorem B4130689 : Blo 1933435 4130689 := bstep (se 2 (by rfl) ⟨1549008, by rfl⟩ : syracuseStep 4130689 = 3098017) B3098017
theorem B5507585 : Blo 1933435 5507585 := bstep (se 2 (by rfl) ⟨2065344, by rfl⟩ : syracuseStep 5507585 = 4130689) B4130689
theorem B3671723 : Blo 1933435 3671723 := bstep (se 1 (by rfl) ⟨2753792, by rfl⟩ : syracuseStep 3671723 = 5507585) B5507585
theorem B2447815 : Blo 1933435 2447815 := bstep (se 1 (by rfl) ⟨1835861, by rfl⟩ : syracuseStep 2447815 = 3671723) B3671723
theorem B3263753 : Blo 1933435 3263753 := bstep (se 2 (by rfl) ⟨1223907, by rfl⟩ : syracuseStep 3263753 = 2447815) B2447815
theorem B2175835 : Blo 1933435 2175835 := bstep (se 1 (by rfl) ⟨1631876, by rfl⟩ : syracuseStep 2175835 = 3263753) B3263753
theorem B2901113 : Blo 1933435 2901113 := bstep (se 2 (by rfl) ⟨1087917, by rfl⟩ : syracuseStep 2901113 = 2175835) B2175835
theorem B1934075 : Blo 1933435 1934075 := bstep (se 1 (by rfl) ⟨1450556, by rfl⟩ : syracuseStep 1934075 = 2901113) B2901113
theorem B9924869 : Blo 1933435 9924869 := bbase (se 4 (by rfl) ⟨930456, by rfl⟩ : syracuseStep 9924869 = 1860913) (by norm_num)
theorem B6616579 : Blo 1933435 6616579 := bstep (se 1 (by rfl) ⟨4962434, by rfl⟩ : syracuseStep 6616579 = 9924869) B9924869
theorem B8822105 : Blo 1933435 8822105 := bstep (se 2 (by rfl) ⟨3308289, by rfl⟩ : syracuseStep 8822105 = 6616579) B6616579
theorem B5881403 : Blo 1933435 5881403 := bstep (se 1 (by rfl) ⟨4411052, by rfl⟩ : syracuseStep 5881403 = 8822105) B8822105
theorem B3920935 : Blo 1933435 3920935 := bstep (se 1 (by rfl) ⟨2940701, by rfl⟩ : syracuseStep 3920935 = 5881403) B5881403
theorem B5227913 : Blo 1933435 5227913 := bstep (se 2 (by rfl) ⟨1960467, by rfl⟩ : syracuseStep 5227913 = 3920935) B3920935
theorem B3485275 : Blo 1933435 3485275 := bstep (se 1 (by rfl) ⟨2613956, by rfl⟩ : syracuseStep 3485275 = 5227913) B5227913
theorem B18588133 : Blo 1933435 18588133 := bstep (se 4 (by rfl) ⟨1742637, by rfl⟩ : syracuseStep 18588133 = 3485275) B3485275
theorem B24784177 : Blo 1933435 24784177 := bstep (se 2 (by rfl) ⟨9294066, by rfl⟩ : syracuseStep 24784177 = 18588133) B18588133
theorem B33045569 : Blo 1933435 33045569 := bstep (se 2 (by rfl) ⟨12392088, by rfl⟩ : syracuseStep 33045569 = 24784177) B24784177
theorem B22030379 : Blo 1933435 22030379 := bstep (se 1 (by rfl) ⟨16522784, by rfl⟩ : syracuseStep 22030379 = 33045569) B33045569
theorem B14686919 : Blo 1933435 14686919 := bstep (se 1 (by rfl) ⟨11015189, by rfl⟩ : syracuseStep 14686919 = 22030379) B22030379
theorem B9791279 : Blo 1933435 9791279 := bstep (se 1 (by rfl) ⟨7343459, by rfl⟩ : syracuseStep 9791279 = 14686919) B14686919
theorem B6527519 : Blo 1933435 6527519 := bstep (se 1 (by rfl) ⟨4895639, by rfl⟩ : syracuseStep 6527519 = 9791279) B9791279
theorem B4351679 : Blo 1933435 4351679 := bstep (se 1 (by rfl) ⟨3263759, by rfl⟩ : syracuseStep 4351679 = 6527519) B6527519
theorem B2901119 : Blo 1933435 2901119 := bstep (se 1 (by rfl) ⟨2175839, by rfl⟩ : syracuseStep 2901119 = 4351679) B4351679
theorem B1934079 : Blo 1933435 1934079 := bstep (se 1 (by rfl) ⟨1450559, by rfl⟩ : syracuseStep 1934079 = 2901119) B2901119
theorem B2901125 : Blo 1933435 2901125 := bbase (se 4 (by rfl) ⟨271980, by rfl⟩ : syracuseStep 2901125 = 543961) (by norm_num)
theorem B1934083 : Blo 1933435 1934083 := bstep (se 1 (by rfl) ⟨1450562, by rfl⟩ : syracuseStep 1934083 = 2901125) B2901125
theorem B3263773 : Blo 1933435 3263773 := bbase (se 3 (by rfl) ⟨611957, by rfl⟩ : syracuseStep 3263773 = 1223915) (by norm_num)
theorem B4351697 : Blo 1933435 4351697 := bstep (se 2 (by rfl) ⟨1631886, by rfl⟩ : syracuseStep 4351697 = 3263773) B3263773
theorem B2901131 : Blo 1933435 2901131 := bstep (se 1 (by rfl) ⟨2175848, by rfl⟩ : syracuseStep 2901131 = 4351697) B4351697
theorem B1934087 : Blo 1933435 1934087 := bstep (se 1 (by rfl) ⟨1450565, by rfl⟩ : syracuseStep 1934087 = 2901131) B2901131
theorem B2175853 : Blo 1933435 2175853 := bbase (se 3 (by rfl) ⟨407972, by rfl⟩ : syracuseStep 2175853 = 815945) (by norm_num)
theorem B2901137 : Blo 1933435 2901137 := bstep (se 2 (by rfl) ⟨1087926, by rfl⟩ : syracuseStep 2901137 = 2175853) B2175853
theorem B1934091 : Blo 1933435 1934091 := bstep (se 1 (by rfl) ⟨1450568, by rfl⟩ : syracuseStep 1934091 = 2901137) B2901137
theorem B6527573 : Blo 1933435 6527573 := bbase (se 8 (by rfl) ⟨38247, by rfl⟩ : syracuseStep 6527573 = 76495) (by norm_num)
theorem B4351715 : Blo 1933435 4351715 := bstep (se 1 (by rfl) ⟨3263786, by rfl⟩ : syracuseStep 4351715 = 6527573) B6527573
theorem B2901143 : Blo 1933435 2901143 := bstep (se 1 (by rfl) ⟨2175857, by rfl⟩ : syracuseStep 2901143 = 4351715) B4351715
theorem B1934095 : Blo 1933435 1934095 := bstep (se 1 (by rfl) ⟨1450571, by rfl⟩ : syracuseStep 1934095 = 2901143) B2901143
theorem B2901149 : Blo 1933435 2901149 := bbase (se 3 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 2901149 = 1087931) (by norm_num)
theorem B1934099 : Blo 1933435 1934099 := bstep (se 1 (by rfl) ⟨1450574, by rfl⟩ : syracuseStep 1934099 = 2901149) B2901149
theorem B4351733 : Blo 1933435 4351733 := bbase (se 5 (by rfl) ⟨203987, by rfl⟩ : syracuseStep 4351733 = 407975) (by norm_num)
theorem B2901155 : Blo 1933435 2901155 := bstep (se 1 (by rfl) ⟨2175866, by rfl⟩ : syracuseStep 2901155 = 4351733) B4351733
theorem B1934103 : Blo 1933435 1934103 := bstep (se 1 (by rfl) ⟨1450577, by rfl⟩ : syracuseStep 1934103 = 2901155) B2901155
theorem B9925013 : Blo 1933435 9925013 := bbase (se 6 (by rfl) ⟨232617, by rfl⟩ : syracuseStep 9925013 = 465235) (by norm_num)
theorem B6616675 : Blo 1933435 6616675 := bstep (se 1 (by rfl) ⟨4962506, by rfl⟩ : syracuseStep 6616675 = 9925013) B9925013
theorem B8822233 : Blo 1933435 8822233 := bstep (se 2 (by rfl) ⟨3308337, by rfl⟩ : syracuseStep 8822233 = 6616675) B6616675
theorem B11762977 : Blo 1933435 11762977 := bstep (se 2 (by rfl) ⟨4411116, by rfl⟩ : syracuseStep 11762977 = 8822233) B8822233
theorem B15683969 : Blo 1933435 15683969 := bstep (se 2 (by rfl) ⟨5881488, by rfl⟩ : syracuseStep 15683969 = 11762977) B11762977
theorem B10455979 : Blo 1933435 10455979 := bstep (se 1 (by rfl) ⟨7841984, by rfl⟩ : syracuseStep 10455979 = 15683969) B15683969
theorem B13941305 : Blo 1933435 13941305 := bstep (se 2 (by rfl) ⟨5227989, by rfl⟩ : syracuseStep 13941305 = 10455979) B10455979
theorem B9294203 : Blo 1933435 9294203 := bstep (se 1 (by rfl) ⟨6970652, by rfl⟩ : syracuseStep 9294203 = 13941305) B13941305
theorem B24784541 : Blo 1933435 24784541 := bstep (se 3 (by rfl) ⟨4647101, by rfl⟩ : syracuseStep 24784541 = 9294203) B9294203
theorem B16523027 : Blo 1933435 16523027 := bstep (se 1 (by rfl) ⟨12392270, by rfl⟩ : syracuseStep 16523027 = 24784541) B24784541
theorem B11015351 : Blo 1933435 11015351 := bstep (se 1 (by rfl) ⟨8261513, by rfl⟩ : syracuseStep 11015351 = 16523027) B16523027
theorem B7343567 : Blo 1933435 7343567 := bstep (se 1 (by rfl) ⟨5507675, by rfl⟩ : syracuseStep 7343567 = 11015351) B11015351
theorem B4895711 : Blo 1933435 4895711 := bstep (se 1 (by rfl) ⟨3671783, by rfl⟩ : syracuseStep 4895711 = 7343567) B7343567
theorem B3263807 : Blo 1933435 3263807 := bstep (se 1 (by rfl) ⟨2447855, by rfl⟩ : syracuseStep 3263807 = 4895711) B4895711
theorem B2175871 : Blo 1933435 2175871 := bstep (se 1 (by rfl) ⟨1631903, by rfl⟩ : syracuseStep 2175871 = 3263807) B3263807
theorem B2901161 : Blo 1933435 2901161 := bstep (se 2 (by rfl) ⟨1087935, by rfl⟩ : syracuseStep 2901161 = 2175871) B2175871
theorem B1934107 : Blo 1933435 1934107 := bstep (se 1 (by rfl) ⟨1450580, by rfl⟩ : syracuseStep 1934107 = 2901161) B2901161
theorem B4130765 : Blo 1933435 4130765 := bbase (se 3 (by rfl) ⟨774518, by rfl⟩ : syracuseStep 4130765 = 1549037) (by norm_num)
theorem B2753843 : Blo 1933435 2753843 := bstep (se 1 (by rfl) ⟨2065382, by rfl⟩ : syracuseStep 2753843 = 4130765) B4130765
theorem B7343581 : Blo 1933435 7343581 := bstep (se 3 (by rfl) ⟨1376921, by rfl⟩ : syracuseStep 7343581 = 2753843) B2753843
theorem B9791441 : Blo 1933435 9791441 := bstep (se 2 (by rfl) ⟨3671790, by rfl⟩ : syracuseStep 9791441 = 7343581) B7343581
theorem B6527627 : Blo 1933435 6527627 := bstep (se 1 (by rfl) ⟨4895720, by rfl⟩ : syracuseStep 6527627 = 9791441) B9791441
theorem B4351751 : Blo 1933435 4351751 := bstep (se 1 (by rfl) ⟨3263813, by rfl⟩ : syracuseStep 4351751 = 6527627) B6527627
theorem B2901167 : Blo 1933435 2901167 := bstep (se 1 (by rfl) ⟨2175875, by rfl⟩ : syracuseStep 2901167 = 4351751) B4351751
theorem B1934111 : Blo 1933435 1934111 := bstep (se 1 (by rfl) ⟨1450583, by rfl⟩ : syracuseStep 1934111 = 2901167) B2901167
theorem B2901173 : Blo 1933435 2901173 := bbase (se 5 (by rfl) ⟨135992, by rfl⟩ : syracuseStep 2901173 = 271985) (by norm_num)
theorem B1934115 : Blo 1933435 1934115 := bstep (se 1 (by rfl) ⟨1450586, by rfl⟩ : syracuseStep 1934115 = 2901173) B2901173
theorem B4895741 : Blo 1933435 4895741 := bbase (se 3 (by rfl) ⟨917951, by rfl⟩ : syracuseStep 4895741 = 1835903) (by norm_num)
theorem B3263827 : Blo 1933435 3263827 := bstep (se 1 (by rfl) ⟨2447870, by rfl⟩ : syracuseStep 3263827 = 4895741) B4895741
theorem B4351769 : Blo 1933435 4351769 := bstep (se 2 (by rfl) ⟨1631913, by rfl⟩ : syracuseStep 4351769 = 3263827) B3263827
theorem B2901179 : Blo 1933435 2901179 := bstep (se 1 (by rfl) ⟨2175884, by rfl⟩ : syracuseStep 2901179 = 4351769) B4351769
theorem B1934119 : Blo 1933435 1934119 := bstep (se 1 (by rfl) ⟨1450589, by rfl⟩ : syracuseStep 1934119 = 2901179) B2901179
theorem B2175889 : Blo 1933435 2175889 := bbase (se 2 (by rfl) ⟨815958, by rfl⟩ : syracuseStep 2175889 = 1631917) (by norm_num)
theorem B2901185 : Blo 1933435 2901185 := bstep (se 2 (by rfl) ⟨1087944, by rfl⟩ : syracuseStep 2901185 = 2175889) B2175889
theorem B1934123 : Blo 1933435 1934123 := bstep (se 1 (by rfl) ⟨1450592, by rfl⟩ : syracuseStep 1934123 = 2901185) B2901185
theorem B3671821 : Blo 1933435 3671821 := bbase (se 3 (by rfl) ⟨688466, by rfl⟩ : syracuseStep 3671821 = 1376933) (by norm_num)
theorem B4895761 : Blo 1933435 4895761 := bstep (se 2 (by rfl) ⟨1835910, by rfl⟩ : syracuseStep 4895761 = 3671821) B3671821
theorem B6527681 : Blo 1933435 6527681 := bstep (se 2 (by rfl) ⟨2447880, by rfl⟩ : syracuseStep 6527681 = 4895761) B4895761
theorem B4351787 : Blo 1933435 4351787 := bstep (se 1 (by rfl) ⟨3263840, by rfl⟩ : syracuseStep 4351787 = 6527681) B6527681
theorem B2901191 : Blo 1933435 2901191 := bstep (se 1 (by rfl) ⟨2175893, by rfl⟩ : syracuseStep 2901191 = 4351787) B4351787
theorem B1934127 : Blo 1933435 1934127 := bstep (se 1 (by rfl) ⟨1450595, by rfl⟩ : syracuseStep 1934127 = 2901191) B2901191
theorem B2901197 : Blo 1933435 2901197 := bbase (se 3 (by rfl) ⟨543974, by rfl⟩ : syracuseStep 2901197 = 1087949) (by norm_num)
theorem B1934131 : Blo 1933435 1934131 := bstep (se 1 (by rfl) ⟨1450598, by rfl⟩ : syracuseStep 1934131 = 2901197) B2901197
theorem B4351805 : Blo 1933435 4351805 := bbase (se 3 (by rfl) ⟨815963, by rfl⟩ : syracuseStep 4351805 = 1631927) (by norm_num)
theorem B2901203 : Blo 1933435 2901203 := bstep (se 1 (by rfl) ⟨2175902, by rfl⟩ : syracuseStep 2901203 = 4351805) B4351805
theorem B1934135 : Blo 1933435 1934135 := bstep (se 1 (by rfl) ⟨1450601, by rfl⟩ : syracuseStep 1934135 = 2901203) B2901203
theorem B3263861 : Blo 1933435 3263861 := bbase (se 5 (by rfl) ⟨152993, by rfl⟩ : syracuseStep 3263861 = 305987) (by norm_num)
theorem B2175907 : Blo 1933435 2175907 := bstep (se 1 (by rfl) ⟨1631930, by rfl⟩ : syracuseStep 2175907 = 3263861) B3263861
theorem B2901209 : Blo 1933435 2901209 := bstep (se 2 (by rfl) ⟨1087953, by rfl⟩ : syracuseStep 2901209 = 2175907) B2175907
theorem B1934139 : Blo 1933435 1934139 := bstep (se 1 (by rfl) ⟨1450604, by rfl⟩ : syracuseStep 1934139 = 2901209) B2901209
theorem B3098125 : Blo 1933435 3098125 := bbase (se 3 (by rfl) ⟨580898, by rfl⟩ : syracuseStep 3098125 = 1161797) (by norm_num)
theorem B4130833 : Blo 1933435 4130833 := bstep (se 2 (by rfl) ⟨1549062, by rfl⟩ : syracuseStep 4130833 = 3098125) B3098125
theorem B5507777 : Blo 1933435 5507777 := bstep (se 2 (by rfl) ⟨2065416, by rfl⟩ : syracuseStep 5507777 = 4130833) B4130833
theorem B14687405 : Blo 1933435 14687405 := bstep (se 3 (by rfl) ⟨2753888, by rfl⟩ : syracuseStep 14687405 = 5507777) B5507777
theorem B9791603 : Blo 1933435 9791603 := bstep (se 1 (by rfl) ⟨7343702, by rfl⟩ : syracuseStep 9791603 = 14687405) B14687405
theorem B6527735 : Blo 1933435 6527735 := bstep (se 1 (by rfl) ⟨4895801, by rfl⟩ : syracuseStep 6527735 = 9791603) B9791603
theorem B4351823 : Blo 1933435 4351823 := bstep (se 1 (by rfl) ⟨3263867, by rfl⟩ : syracuseStep 4351823 = 6527735) B6527735
theorem B2901215 : Blo 1933435 2901215 := bstep (se 1 (by rfl) ⟨2175911, by rfl⟩ : syracuseStep 2901215 = 4351823) B4351823
theorem B1934143 : Blo 1933435 1934143 := bstep (se 1 (by rfl) ⟨1450607, by rfl⟩ : syracuseStep 1934143 = 2901215) B2901215
theorem B2901221 : Blo 1933435 2901221 := bbase (se 4 (by rfl) ⟨271989, by rfl⟩ : syracuseStep 2901221 = 543979) (by norm_num)
theorem B1934147 : Blo 1933435 1934147 := bstep (se 1 (by rfl) ⟨1450610, by rfl⟩ : syracuseStep 1934147 = 2901221) B2901221
theorem B6196277 : Blo 1933435 6196277 := bbase (se 5 (by rfl) ⟨290450, by rfl⟩ : syracuseStep 6196277 = 580901) (by norm_num)
theorem B4130851 : Blo 1933435 4130851 := bstep (se 1 (by rfl) ⟨3098138, by rfl⟩ : syracuseStep 4130851 = 6196277) B6196277
theorem B5507801 : Blo 1933435 5507801 := bstep (se 2 (by rfl) ⟨2065425, by rfl⟩ : syracuseStep 5507801 = 4130851) B4130851
theorem B3671867 : Blo 1933435 3671867 := bstep (se 1 (by rfl) ⟨2753900, by rfl⟩ : syracuseStep 3671867 = 5507801) B5507801
theorem B2447911 : Blo 1933435 2447911 := bstep (se 1 (by rfl) ⟨1835933, by rfl⟩ : syracuseStep 2447911 = 3671867) B3671867
theorem B3263881 : Blo 1933435 3263881 := bstep (se 2 (by rfl) ⟨1223955, by rfl⟩ : syracuseStep 3263881 = 2447911) B2447911
theorem B4351841 : Blo 1933435 4351841 := bstep (se 2 (by rfl) ⟨1631940, by rfl⟩ : syracuseStep 4351841 = 3263881) B3263881
theorem B2901227 : Blo 1933435 2901227 := bstep (se 1 (by rfl) ⟨2175920, by rfl⟩ : syracuseStep 2901227 = 4351841) B4351841
theorem B1934151 : Blo 1933435 1934151 := bstep (se 1 (by rfl) ⟨1450613, by rfl⟩ : syracuseStep 1934151 = 2901227) B2901227
theorem B2175925 : Blo 1933435 2175925 := bbase (se 5 (by rfl) ⟨101996, by rfl⟩ : syracuseStep 2175925 = 203993) (by norm_num)
theorem B2901233 : Blo 1933435 2901233 := bstep (se 2 (by rfl) ⟨1087962, by rfl⟩ : syracuseStep 2901233 = 2175925) B2175925
theorem B1934155 : Blo 1933435 1934155 := bstep (se 1 (by rfl) ⟨1450616, by rfl⟩ : syracuseStep 1934155 = 2901233) B2901233
theorem B2447921 : Blo 1933435 2447921 := bbase (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) (by norm_num)
theorem B6527789 : Blo 1933435 6527789 := bstep (se 3 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 6527789 = 2447921) B2447921
theorem B4351859 : Blo 1933435 4351859 := bstep (se 1 (by rfl) ⟨3263894, by rfl⟩ : syracuseStep 4351859 = 6527789) B6527789
theorem B2901239 : Blo 1933435 2901239 := bstep (se 1 (by rfl) ⟨2175929, by rfl⟩ : syracuseStep 2901239 = 4351859) B4351859
theorem B1934159 : Blo 1933435 1934159 := bstep (se 1 (by rfl) ⟨1450619, by rfl⟩ : syracuseStep 1934159 = 2901239) B2901239
theorem B2901245 : Blo 1933435 2901245 := bbase (se 3 (by rfl) ⟨543983, by rfl⟩ : syracuseStep 2901245 = 1087967) (by norm_num)
theorem B1934163 : Blo 1933435 1934163 := bstep (se 1 (by rfl) ⟨1450622, by rfl⟩ : syracuseStep 1934163 = 2901245) B2901245
theorem B4351877 : Blo 1933435 4351877 := bbase (se 4 (by rfl) ⟨407988, by rfl⟩ : syracuseStep 4351877 = 815977) (by norm_num)
theorem B2901251 : Blo 1933435 2901251 := bstep (se 1 (by rfl) ⟨2175938, by rfl⟩ : syracuseStep 2901251 = 4351877) B4351877
theorem B1934167 : Blo 1933435 1934167 := bstep (se 1 (by rfl) ⟨1450625, by rfl⟩ : syracuseStep 1934167 = 2901251) B2901251
theorem B5228165 : Blo 1933435 5228165 := bbase (se 4 (by rfl) ⟨490140, by rfl⟩ : syracuseStep 5228165 = 980281) (by norm_num)
theorem B3485443 : Blo 1933435 3485443 := bstep (se 1 (by rfl) ⟨2614082, by rfl⟩ : syracuseStep 3485443 = 5228165) B5228165
theorem B4647257 : Blo 1933435 4647257 := bstep (se 2 (by rfl) ⟨1742721, by rfl⟩ : syracuseStep 4647257 = 3485443) B3485443
theorem B3098171 : Blo 1933435 3098171 := bstep (se 1 (by rfl) ⟨2323628, by rfl⟩ : syracuseStep 3098171 = 4647257) B4647257
theorem B2065447 : Blo 1933435 2065447 := bstep (se 1 (by rfl) ⟨1549085, by rfl⟩ : syracuseStep 2065447 = 3098171) B3098171
theorem B2753929 : Blo 1933435 2753929 := bstep (se 2 (by rfl) ⟨1032723, by rfl⟩ : syracuseStep 2753929 = 2065447) B2065447
theorem B3671905 : Blo 1933435 3671905 := bstep (se 2 (by rfl) ⟨1376964, by rfl⟩ : syracuseStep 3671905 = 2753929) B2753929
theorem B4895873 : Blo 1933435 4895873 := bstep (se 2 (by rfl) ⟨1835952, by rfl⟩ : syracuseStep 4895873 = 3671905) B3671905
theorem B3263915 : Blo 1933435 3263915 := bstep (se 1 (by rfl) ⟨2447936, by rfl⟩ : syracuseStep 3263915 = 4895873) B4895873
theorem B2175943 : Blo 1933435 2175943 := bstep (se 1 (by rfl) ⟨1631957, by rfl⟩ : syracuseStep 2175943 = 3263915) B3263915
theorem B2901257 : Blo 1933435 2901257 := bstep (se 2 (by rfl) ⟨1087971, by rfl⟩ : syracuseStep 2901257 = 2175943) B2175943
theorem B1934171 : Blo 1933435 1934171 := bstep (se 1 (by rfl) ⟨1450628, by rfl⟩ : syracuseStep 1934171 = 2901257) B2901257
theorem B9791765 : Blo 1933435 9791765 := bbase (se 6 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 9791765 = 458989) (by norm_num)
theorem B6527843 : Blo 1933435 6527843 := bstep (se 1 (by rfl) ⟨4895882, by rfl⟩ : syracuseStep 6527843 = 9791765) B9791765
theorem B4351895 : Blo 1933435 4351895 := bstep (se 1 (by rfl) ⟨3263921, by rfl⟩ : syracuseStep 4351895 = 6527843) B6527843
theorem B2901263 : Blo 1933435 2901263 := bstep (se 1 (by rfl) ⟨2175947, by rfl⟩ : syracuseStep 2901263 = 4351895) B4351895
theorem B1934175 : Blo 1933435 1934175 := bstep (se 1 (by rfl) ⟨1450631, by rfl⟩ : syracuseStep 1934175 = 2901263) B2901263
theorem B2901269 : Blo 1933435 2901269 := bbase (se 6 (by rfl) ⟨67998, by rfl⟩ : syracuseStep 2901269 = 135997) (by norm_num)
theorem B1934179 : Blo 1933435 1934179 := bstep (se 1 (by rfl) ⟨1450634, by rfl⟩ : syracuseStep 1934179 = 2901269) B2901269
theorem B3974645 : Blo 1933435 3974645 := bbase (se 5 (by rfl) ⟨186311, by rfl⟩ : syracuseStep 3974645 = 372623) (by norm_num)
theorem B2649763 : Blo 1933435 2649763 := bstep (se 1 (by rfl) ⟨1987322, by rfl⟩ : syracuseStep 2649763 = 3974645) B3974645
theorem B14132069 : Blo 1933435 14132069 := bstep (se 4 (by rfl) ⟨1324881, by rfl⟩ : syracuseStep 14132069 = 2649763) B2649763
theorem B9421379 : Blo 1933435 9421379 := bstep (se 1 (by rfl) ⟨7066034, by rfl⟩ : syracuseStep 9421379 = 14132069) B14132069
theorem B6280919 : Blo 1933435 6280919 := bstep (se 1 (by rfl) ⟨4710689, by rfl⟩ : syracuseStep 6280919 = 9421379) B9421379
theorem B4187279 : Blo 1933435 4187279 := bstep (se 1 (by rfl) ⟨3140459, by rfl⟩ : syracuseStep 4187279 = 6280919) B6280919
theorem B2791519 : Blo 1933435 2791519 := bstep (se 1 (by rfl) ⟨2093639, by rfl⟩ : syracuseStep 2791519 = 4187279) B4187279
theorem B59552405 : Blo 1933435 59552405 := bstep (se 6 (by rfl) ⟨1395759, by rfl⟩ : syracuseStep 59552405 = 2791519) B2791519
theorem B39701603 : Blo 1933435 39701603 := bstep (se 1 (by rfl) ⟨29776202, by rfl⟩ : syracuseStep 39701603 = 59552405) B59552405
theorem B26467735 : Blo 1933435 26467735 := bstep (se 1 (by rfl) ⟨19850801, by rfl⟩ : syracuseStep 26467735 = 39701603) B39701603
theorem B35290313 : Blo 1933435 35290313 := bstep (se 2 (by rfl) ⟨13233867, by rfl⟩ : syracuseStep 35290313 = 26467735) B26467735
theorem B23526875 : Blo 1933435 23526875 := bstep (se 1 (by rfl) ⟨17645156, by rfl⟩ : syracuseStep 23526875 = 35290313) B35290313
theorem B62738333 : Blo 1933435 62738333 := bstep (se 3 (by rfl) ⟨11763437, by rfl⟩ : syracuseStep 62738333 = 23526875) B23526875
theorem B41825555 : Blo 1933435 41825555 := bstep (se 1 (by rfl) ⟨31369166, by rfl⟩ : syracuseStep 41825555 = 62738333) B62738333
theorem B27883703 : Blo 1933435 27883703 := bstep (se 1 (by rfl) ⟨20912777, by rfl⟩ : syracuseStep 27883703 = 41825555) B41825555
theorem B18589135 : Blo 1933435 18589135 := bstep (se 1 (by rfl) ⟨13941851, by rfl⟩ : syracuseStep 18589135 = 27883703) B27883703
theorem B24785513 : Blo 1933435 24785513 := bstep (se 2 (by rfl) ⟨9294567, by rfl⟩ : syracuseStep 24785513 = 18589135) B18589135
theorem B16523675 : Blo 1933435 16523675 := bstep (se 1 (by rfl) ⟨12392756, by rfl⟩ : syracuseStep 16523675 = 24785513) B24785513
theorem B11015783 : Blo 1933435 11015783 := bstep (se 1 (by rfl) ⟨8261837, by rfl⟩ : syracuseStep 11015783 = 16523675) B16523675
theorem B7343855 : Blo 1933435 7343855 := bstep (se 1 (by rfl) ⟨5507891, by rfl⟩ : syracuseStep 7343855 = 11015783) B11015783
theorem B4895903 : Blo 1933435 4895903 := bstep (se 1 (by rfl) ⟨3671927, by rfl⟩ : syracuseStep 4895903 = 7343855) B7343855
theorem B3263935 : Blo 1933435 3263935 := bstep (se 1 (by rfl) ⟨2447951, by rfl⟩ : syracuseStep 3263935 = 4895903) B4895903
theorem B4351913 : Blo 1933435 4351913 := bstep (se 2 (by rfl) ⟨1631967, by rfl⟩ : syracuseStep 4351913 = 3263935) B3263935
theorem B2901275 : Blo 1933435 2901275 := bstep (se 1 (by rfl) ⟨2175956, by rfl⟩ : syracuseStep 2901275 = 4351913) B4351913
theorem B1934183 : Blo 1933435 1934183 := bstep (se 1 (by rfl) ⟨1450637, by rfl⟩ : syracuseStep 1934183 = 2901275) B2901275
theorem B2175961 : Blo 1933435 2175961 := bbase (se 2 (by rfl) ⟨815985, by rfl⟩ : syracuseStep 2175961 = 1631971) (by norm_num)
theorem B2901281 : Blo 1933435 2901281 := bstep (se 2 (by rfl) ⟨1087980, by rfl⟩ : syracuseStep 2901281 = 2175961) B2175961
theorem B1934187 : Blo 1933435 1934187 := bstep (se 1 (by rfl) ⟨1450640, by rfl⟩ : syracuseStep 1934187 = 2901281) B2901281
theorem B2753957 : Blo 1933435 2753957 := bbase (se 4 (by rfl) ⟨258183, by rfl⟩ : syracuseStep 2753957 = 516367) (by norm_num)
theorem B7343885 : Blo 1933435 7343885 := bstep (se 3 (by rfl) ⟨1376978, by rfl⟩ : syracuseStep 7343885 = 2753957) B2753957
theorem B4895923 : Blo 1933435 4895923 := bstep (se 1 (by rfl) ⟨3671942, by rfl⟩ : syracuseStep 4895923 = 7343885) B7343885
theorem B6527897 : Blo 1933435 6527897 := bstep (se 2 (by rfl) ⟨2447961, by rfl⟩ : syracuseStep 6527897 = 4895923) B4895923
theorem B4351931 : Blo 1933435 4351931 := bstep (se 1 (by rfl) ⟨3263948, by rfl⟩ : syracuseStep 4351931 = 6527897) B6527897
theorem B2901287 : Blo 1933435 2901287 := bstep (se 1 (by rfl) ⟨2175965, by rfl⟩ : syracuseStep 2901287 = 4351931) B4351931
theorem B1934191 : Blo 1933435 1934191 := bstep (se 1 (by rfl) ⟨1450643, by rfl⟩ : syracuseStep 1934191 = 2901287) B2901287
theorem B2901293 : Blo 1933435 2901293 := bbase (se 3 (by rfl) ⟨543992, by rfl⟩ : syracuseStep 2901293 = 1087985) (by norm_num)
theorem B1934195 : Blo 1933435 1934195 := bstep (se 1 (by rfl) ⟨1450646, by rfl⟩ : syracuseStep 1934195 = 2901293) B2901293
theorem B4351949 : Blo 1933435 4351949 := bbase (se 3 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 4351949 = 1631981) (by norm_num)
theorem B2901299 : Blo 1933435 2901299 := bstep (se 1 (by rfl) ⟨2175974, by rfl⟩ : syracuseStep 2901299 = 4351949) B4351949
theorem B1934199 : Blo 1933435 1934199 := bstep (se 1 (by rfl) ⟨1450649, by rfl⟩ : syracuseStep 1934199 = 2901299) B2901299
theorem B2447977 : Blo 1933435 2447977 := bbase (se 2 (by rfl) ⟨917991, by rfl⟩ : syracuseStep 2447977 = 1835983) (by norm_num)
theorem B3263969 : Blo 1933435 3263969 := bstep (se 2 (by rfl) ⟨1223988, by rfl⟩ : syracuseStep 3263969 = 2447977) B2447977
theorem B2175979 : Blo 1933435 2175979 := bstep (se 1 (by rfl) ⟨1631984, by rfl⟩ : syracuseStep 2175979 = 3263969) B3263969
theorem B2901305 : Blo 1933435 2901305 := bstep (se 2 (by rfl) ⟨1087989, by rfl⟩ : syracuseStep 2901305 = 2175979) B2175979
theorem B1934203 : Blo 1933435 1934203 := bstep (se 1 (by rfl) ⟨1450652, by rfl⟩ : syracuseStep 1934203 = 2901305) B2901305
theorem B4647341 : Blo 1933435 4647341 := bbase (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) (by norm_num)
theorem B12392909 : Blo 1933435 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B8261939 : Blo 1933435 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B22031837 : Blo 1933435 22031837 := bstep (se 3 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 22031837 = 8261939) B8261939
theorem B14687891 : Blo 1933435 14687891 := bstep (se 1 (by rfl) ⟨11015918, by rfl⟩ : syracuseStep 14687891 = 22031837) B22031837
theorem B9791927 : Blo 1933435 9791927 := bstep (se 1 (by rfl) ⟨7343945, by rfl⟩ : syracuseStep 9791927 = 14687891) B14687891
theorem B6527951 : Blo 1933435 6527951 := bstep (se 1 (by rfl) ⟨4895963, by rfl⟩ : syracuseStep 6527951 = 9791927) B9791927
theorem B4351967 : Blo 1933435 4351967 := bstep (se 1 (by rfl) ⟨3263975, by rfl⟩ : syracuseStep 4351967 = 6527951) B6527951
theorem B2901311 : Blo 1933435 2901311 := bstep (se 1 (by rfl) ⟨2175983, by rfl⟩ : syracuseStep 2901311 = 4351967) B4351967
theorem B1934207 : Blo 1933435 1934207 := bstep (se 1 (by rfl) ⟨1450655, by rfl⟩ : syracuseStep 1934207 = 2901311) B2901311
theorem B2901317 : Blo 1933435 2901317 := bbase (se 4 (by rfl) ⟨271998, by rfl⟩ : syracuseStep 2901317 = 543997) (by norm_num)
theorem B1934211 : Blo 1933435 1934211 := bstep (se 1 (by rfl) ⟨1450658, by rfl⟩ : syracuseStep 1934211 = 2901317) B2901317
theorem B3263989 : Blo 1933435 3263989 := bbase (se 5 (by rfl) ⟨152999, by rfl⟩ : syracuseStep 3263989 = 305999) (by norm_num)
theorem B4351985 : Blo 1933435 4351985 := bstep (se 2 (by rfl) ⟨1631994, by rfl⟩ : syracuseStep 4351985 = 3263989) B3263989
theorem B2901323 : Blo 1933435 2901323 := bstep (se 1 (by rfl) ⟨2175992, by rfl⟩ : syracuseStep 2901323 = 4351985) B4351985
theorem B1934215 : Blo 1933435 1934215 := bstep (se 1 (by rfl) ⟨1450661, by rfl⟩ : syracuseStep 1934215 = 2901323) B2901323
theorem B2175997 : Blo 1933435 2175997 := bbase (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) (by norm_num)
theorem B2901329 : Blo 1933435 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B1934219 : Blo 1933435 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B6528005 : Blo 1933435 6528005 := bbase (se 4 (by rfl) ⟨612000, by rfl⟩ : syracuseStep 6528005 = 1224001) (by norm_num)
theorem B4352003 : Blo 1933435 4352003 := bstep (se 1 (by rfl) ⟨3264002, by rfl⟩ : syracuseStep 4352003 = 6528005) B6528005
theorem B2901335 : Blo 1933435 2901335 := bstep (se 1 (by rfl) ⟨2176001, by rfl⟩ : syracuseStep 2901335 = 4352003) B4352003
theorem B1934223 : Blo 1933435 1934223 := bstep (se 1 (by rfl) ⟨1450667, by rfl⟩ : syracuseStep 1934223 = 2901335) B2901335
theorem B2901341 : Blo 1933435 2901341 := bbase (se 3 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 2901341 = 1088003) (by norm_num)
theorem B1934227 : Blo 1933435 1934227 := bstep (se 1 (by rfl) ⟨1450670, by rfl⟩ : syracuseStep 1934227 = 2901341) B2901341
theorem B4352021 : Blo 1933435 4352021 := bbase (se 6 (by rfl) ⟨102000, by rfl⟩ : syracuseStep 4352021 = 204001) (by norm_num)
theorem B2901347 : Blo 1933435 2901347 := bstep (se 1 (by rfl) ⟨2176010, by rfl⟩ : syracuseStep 2901347 = 4352021) B4352021
theorem B1934231 : Blo 1933435 1934231 := bstep (se 1 (by rfl) ⟨1450673, by rfl⟩ : syracuseStep 1934231 = 2901347) B2901347
theorem B7344053 : Blo 1933435 7344053 := bbase (se 5 (by rfl) ⟨344252, by rfl⟩ : syracuseStep 7344053 = 688505) (by norm_num)
theorem B4896035 : Blo 1933435 4896035 := bstep (se 1 (by rfl) ⟨3672026, by rfl⟩ : syracuseStep 4896035 = 7344053) B7344053
theorem B3264023 : Blo 1933435 3264023 := bstep (se 1 (by rfl) ⟨2448017, by rfl⟩ : syracuseStep 3264023 = 4896035) B4896035
theorem B2176015 : Blo 1933435 2176015 := bstep (se 1 (by rfl) ⟨1632011, by rfl⟩ : syracuseStep 2176015 = 3264023) B3264023
theorem B2901353 : Blo 1933435 2901353 := bstep (se 2 (by rfl) ⟨1088007, by rfl⟩ : syracuseStep 2901353 = 2176015) B2176015
theorem B1934235 : Blo 1933435 1934235 := bstep (se 1 (by rfl) ⟨1450676, by rfl⟩ : syracuseStep 1934235 = 2901353) B2901353
theorem B8822837 : Blo 1933435 8822837 := bbase (se 5 (by rfl) ⟨413570, by rfl⟩ : syracuseStep 8822837 = 827141) (by norm_num)
theorem B5881891 : Blo 1933435 5881891 := bstep (se 1 (by rfl) ⟨4411418, by rfl⟩ : syracuseStep 5881891 = 8822837) B8822837
theorem B7842521 : Blo 1933435 7842521 := bstep (se 2 (by rfl) ⟨2940945, by rfl⟩ : syracuseStep 7842521 = 5881891) B5881891
theorem B5228347 : Blo 1933435 5228347 := bstep (se 1 (by rfl) ⟨3921260, by rfl⟩ : syracuseStep 5228347 = 7842521) B7842521
theorem B6971129 : Blo 1933435 6971129 := bstep (se 2 (by rfl) ⟨2614173, by rfl⟩ : syracuseStep 6971129 = 5228347) B5228347
theorem B4647419 : Blo 1933435 4647419 := bstep (se 1 (by rfl) ⟨3485564, by rfl⟩ : syracuseStep 4647419 = 6971129) B6971129
theorem B3098279 : Blo 1933435 3098279 := bstep (se 1 (by rfl) ⟨2323709, by rfl⟩ : syracuseStep 3098279 = 4647419) B4647419
theorem B2065519 : Blo 1933435 2065519 := bstep (se 1 (by rfl) ⟨1549139, by rfl⟩ : syracuseStep 2065519 = 3098279) B3098279
theorem B11016101 : Blo 1933435 11016101 := bstep (se 4 (by rfl) ⟨1032759, by rfl⟩ : syracuseStep 11016101 = 2065519) B2065519
theorem B7344067 : Blo 1933435 7344067 := bstep (se 1 (by rfl) ⟨5508050, by rfl⟩ : syracuseStep 7344067 = 11016101) B11016101
theorem B9792089 : Blo 1933435 9792089 := bstep (se 2 (by rfl) ⟨3672033, by rfl⟩ : syracuseStep 9792089 = 7344067) B7344067
theorem B6528059 : Blo 1933435 6528059 := bstep (se 1 (by rfl) ⟨4896044, by rfl⟩ : syracuseStep 6528059 = 9792089) B9792089
theorem B4352039 : Blo 1933435 4352039 := bstep (se 1 (by rfl) ⟨3264029, by rfl⟩ : syracuseStep 4352039 = 6528059) B6528059
theorem B2901359 : Blo 1933435 2901359 := bstep (se 1 (by rfl) ⟨2176019, by rfl⟩ : syracuseStep 2901359 = 4352039) B4352039
theorem B1934239 : Blo 1933435 1934239 := bstep (se 1 (by rfl) ⟨1450679, by rfl⟩ : syracuseStep 1934239 = 2901359) B2901359
theorem B2901365 : Blo 1933435 2901365 := bbase (se 5 (by rfl) ⟨136001, by rfl⟩ : syracuseStep 2901365 = 272003) (by norm_num)
theorem B1934243 : Blo 1933435 1934243 := bstep (se 1 (by rfl) ⟨1450682, by rfl⟩ : syracuseStep 1934243 = 2901365) B2901365
theorem B2754037 : Blo 1933435 2754037 := bbase (se 5 (by rfl) ⟨129095, by rfl⟩ : syracuseStep 2754037 = 258191) (by norm_num)
theorem B3672049 : Blo 1933435 3672049 := bstep (se 2 (by rfl) ⟨1377018, by rfl⟩ : syracuseStep 3672049 = 2754037) B2754037
theorem B4896065 : Blo 1933435 4896065 := bstep (se 2 (by rfl) ⟨1836024, by rfl⟩ : syracuseStep 4896065 = 3672049) B3672049
theorem B3264043 : Blo 1933435 3264043 := bstep (se 1 (by rfl) ⟨2448032, by rfl⟩ : syracuseStep 3264043 = 4896065) B4896065
theorem B4352057 : Blo 1933435 4352057 := bstep (se 2 (by rfl) ⟨1632021, by rfl⟩ : syracuseStep 4352057 = 3264043) B3264043
theorem B2901371 : Blo 1933435 2901371 := bstep (se 1 (by rfl) ⟨2176028, by rfl⟩ : syracuseStep 2901371 = 4352057) B4352057
theorem B1934247 : Blo 1933435 1934247 := bstep (se 1 (by rfl) ⟨1450685, by rfl⟩ : syracuseStep 1934247 = 2901371) B2901371
theorem B2176033 : Blo 1933435 2176033 := bbase (se 2 (by rfl) ⟨816012, by rfl⟩ : syracuseStep 2176033 = 1632025) (by norm_num)
theorem B2901377 : Blo 1933435 2901377 := bstep (se 2 (by rfl) ⟨1088016, by rfl⟩ : syracuseStep 2901377 = 2176033) B2176033
theorem B1934251 : Blo 1933435 1934251 := bstep (se 1 (by rfl) ⟨1450688, by rfl⟩ : syracuseStep 1934251 = 2901377) B2901377
theorem B4896085 : Blo 1933435 4896085 := bbase (se 13 (by rfl) ⟨896, by rfl⟩ : syracuseStep 4896085 = 1793) (by norm_num)
theorem B6528113 : Blo 1933435 6528113 := bstep (se 2 (by rfl) ⟨2448042, by rfl⟩ : syracuseStep 6528113 = 4896085) B4896085
theorem B4352075 : Blo 1933435 4352075 := bstep (se 1 (by rfl) ⟨3264056, by rfl⟩ : syracuseStep 4352075 = 6528113) B6528113
theorem B2901383 : Blo 1933435 2901383 := bstep (se 1 (by rfl) ⟨2176037, by rfl⟩ : syracuseStep 2901383 = 4352075) B4352075
theorem B1934255 : Blo 1933435 1934255 := bstep (se 1 (by rfl) ⟨1450691, by rfl⟩ : syracuseStep 1934255 = 2901383) B2901383
theorem B2901389 : Blo 1933435 2901389 := bbase (se 3 (by rfl) ⟨544010, by rfl⟩ : syracuseStep 2901389 = 1088021) (by norm_num)
theorem B1934259 : Blo 1933435 1934259 := bstep (se 1 (by rfl) ⟨1450694, by rfl⟩ : syracuseStep 1934259 = 2901389) B2901389
theorem B4352093 : Blo 1933435 4352093 := bbase (se 3 (by rfl) ⟨816017, by rfl⟩ : syracuseStep 4352093 = 1632035) (by norm_num)
theorem B2901395 : Blo 1933435 2901395 := bstep (se 1 (by rfl) ⟨2176046, by rfl⟩ : syracuseStep 2901395 = 4352093) B4352093
theorem B1934263 : Blo 1933435 1934263 := bstep (se 1 (by rfl) ⟨1450697, by rfl⟩ : syracuseStep 1934263 = 2901395) B2901395
theorem B3264077 : Blo 1933435 3264077 := bbase (se 3 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 3264077 = 1224029) (by norm_num)
theorem B2176051 : Blo 1933435 2176051 := bstep (se 1 (by rfl) ⟨1632038, by rfl⟩ : syracuseStep 2176051 = 3264077) B3264077
theorem B2901401 : Blo 1933435 2901401 := bstep (se 2 (by rfl) ⟨1088025, by rfl⟩ : syracuseStep 2901401 = 2176051) B2176051
theorem B1934267 : Blo 1933435 1934267 := bstep (se 1 (by rfl) ⟨1450700, by rfl⟩ : syracuseStep 1934267 = 2901401) B2901401
theorem B2151257 : Blo 1933435 2151257 := bbase (se 2 (by rfl) ⟨806721, by rfl⟩ : syracuseStep 2151257 = 1613443) (by norm_num)
theorem B5736685 : Blo 1933435 5736685 := bstep (se 3 (by rfl) ⟨1075628, by rfl⟩ : syracuseStep 5736685 = 2151257) B2151257
theorem B7648913 : Blo 1933435 7648913 := bstep (se 2 (by rfl) ⟨2868342, by rfl⟩ : syracuseStep 7648913 = 5736685) B5736685
theorem B5099275 : Blo 1933435 5099275 := bstep (se 1 (by rfl) ⟨3824456, by rfl⟩ : syracuseStep 5099275 = 7648913) B7648913
theorem B6799033 : Blo 1933435 6799033 := bstep (se 2 (by rfl) ⟨2549637, by rfl⟩ : syracuseStep 6799033 = 5099275) B5099275
theorem B9065377 : Blo 1933435 9065377 := bstep (se 2 (by rfl) ⟨3399516, by rfl⟩ : syracuseStep 9065377 = 6799033) B6799033
theorem B48348677 : Blo 1933435 48348677 := bstep (se 4 (by rfl) ⟨4532688, by rfl⟩ : syracuseStep 48348677 = 9065377) B9065377
theorem B32232451 : Blo 1933435 32232451 := bstep (se 1 (by rfl) ⟨24174338, by rfl⟩ : syracuseStep 32232451 = 48348677) B48348677
theorem B42976601 : Blo 1933435 42976601 := bstep (se 2 (by rfl) ⟨16116225, by rfl⟩ : syracuseStep 42976601 = 32232451) B32232451
theorem B28651067 : Blo 1933435 28651067 := bstep (se 1 (by rfl) ⟨21488300, by rfl⟩ : syracuseStep 28651067 = 42976601) B42976601
theorem B19100711 : Blo 1933435 19100711 := bstep (se 1 (by rfl) ⟨14325533, by rfl⟩ : syracuseStep 19100711 = 28651067) B28651067
theorem B50935229 : Blo 1933435 50935229 := bstep (se 3 (by rfl) ⟨9550355, by rfl⟩ : syracuseStep 50935229 = 19100711) B19100711
theorem B33956819 : Blo 1933435 33956819 := bstep (se 1 (by rfl) ⟨25467614, by rfl⟩ : syracuseStep 33956819 = 50935229) B50935229
theorem B22637879 : Blo 1933435 22637879 := bstep (se 1 (by rfl) ⟨16978409, by rfl⟩ : syracuseStep 22637879 = 33956819) B33956819
theorem B15091919 : Blo 1933435 15091919 := bstep (se 1 (by rfl) ⟨11318939, by rfl⟩ : syracuseStep 15091919 = 22637879) B22637879
theorem B10061279 : Blo 1933435 10061279 := bstep (se 1 (by rfl) ⟨7545959, by rfl⟩ : syracuseStep 10061279 = 15091919) B15091919
theorem B6707519 : Blo 1933435 6707519 := bstep (se 1 (by rfl) ⟨5030639, by rfl⟩ : syracuseStep 6707519 = 10061279) B10061279
theorem B4471679 : Blo 1933435 4471679 := bstep (se 1 (by rfl) ⟨3353759, by rfl⟩ : syracuseStep 4471679 = 6707519) B6707519
theorem B2981119 : Blo 1933435 2981119 := bstep (se 1 (by rfl) ⟨2235839, by rfl⟩ : syracuseStep 2981119 = 4471679) B4471679
theorem B3974825 : Blo 1933435 3974825 := bstep (se 2 (by rfl) ⟨1490559, by rfl⟩ : syracuseStep 3974825 = 2981119) B2981119
theorem B2649883 : Blo 1933435 2649883 := bstep (se 1 (by rfl) ⟨1987412, by rfl⟩ : syracuseStep 2649883 = 3974825) B3974825
theorem B3533177 : Blo 1933435 3533177 := bstep (se 2 (by rfl) ⟨1324941, by rfl⟩ : syracuseStep 3533177 = 2649883) B2649883
theorem B9421805 : Blo 1933435 9421805 := bstep (se 3 (by rfl) ⟨1766588, by rfl⟩ : syracuseStep 9421805 = 3533177) B3533177
theorem B25124813 : Blo 1933435 25124813 := bstep (se 3 (by rfl) ⟨4710902, by rfl⟩ : syracuseStep 25124813 = 9421805) B9421805
theorem B16749875 : Blo 1933435 16749875 := bstep (se 1 (by rfl) ⟨12562406, by rfl⟩ : syracuseStep 16749875 = 25124813) B25124813
theorem B11166583 : Blo 1933435 11166583 := bstep (se 1 (by rfl) ⟨8374937, by rfl⟩ : syracuseStep 11166583 = 16749875) B16749875
theorem B14888777 : Blo 1933435 14888777 := bstep (se 2 (by rfl) ⟨5583291, by rfl⟩ : syracuseStep 14888777 = 11166583) B11166583
theorem B158813621 : Blo 1933435 158813621 := bstep (se 5 (by rfl) ⟨7444388, by rfl⟩ : syracuseStep 158813621 = 14888777) B14888777
theorem B105875747 : Blo 1933435 105875747 := bstep (se 1 (by rfl) ⟨79406810, by rfl⟩ : syracuseStep 105875747 = 158813621) B158813621
theorem B70583831 : Blo 1933435 70583831 := bstep (se 1 (by rfl) ⟨52937873, by rfl⟩ : syracuseStep 70583831 = 105875747) B105875747
theorem B47055887 : Blo 1933435 47055887 := bstep (se 1 (by rfl) ⟨35291915, by rfl⟩ : syracuseStep 47055887 = 70583831) B70583831
theorem B31370591 : Blo 1933435 31370591 := bstep (se 1 (by rfl) ⟨23527943, by rfl⟩ : syracuseStep 31370591 = 47055887) B47055887
theorem B20913727 : Blo 1933435 20913727 := bstep (se 1 (by rfl) ⟨15685295, by rfl⟩ : syracuseStep 20913727 = 31370591) B31370591
theorem B27884969 : Blo 1933435 27884969 := bstep (se 2 (by rfl) ⟨10456863, by rfl⟩ : syracuseStep 27884969 = 20913727) B20913727
theorem B18589979 : Blo 1933435 18589979 := bstep (se 1 (by rfl) ⟨13942484, by rfl⟩ : syracuseStep 18589979 = 27884969) B27884969
theorem B12393319 : Blo 1933435 12393319 := bstep (se 1 (by rfl) ⟨9294989, by rfl⟩ : syracuseStep 12393319 = 18589979) B18589979
theorem B16524425 : Blo 1933435 16524425 := bstep (se 2 (by rfl) ⟨6196659, by rfl⟩ : syracuseStep 16524425 = 12393319) B12393319
theorem B11016283 : Blo 1933435 11016283 := bstep (se 1 (by rfl) ⟨8262212, by rfl⟩ : syracuseStep 11016283 = 16524425) B16524425
theorem B14688377 : Blo 1933435 14688377 := bstep (se 2 (by rfl) ⟨5508141, by rfl⟩ : syracuseStep 14688377 = 11016283) B11016283
theorem B9792251 : Blo 1933435 9792251 := bstep (se 1 (by rfl) ⟨7344188, by rfl⟩ : syracuseStep 9792251 = 14688377) B14688377
theorem B6528167 : Blo 1933435 6528167 := bstep (se 1 (by rfl) ⟨4896125, by rfl⟩ : syracuseStep 6528167 = 9792251) B9792251
theorem B4352111 : Blo 1933435 4352111 := bstep (se 1 (by rfl) ⟨3264083, by rfl⟩ : syracuseStep 4352111 = 6528167) B6528167
theorem B2901407 : Blo 1933435 2901407 := bstep (se 1 (by rfl) ⟨2176055, by rfl⟩ : syracuseStep 2901407 = 4352111) B4352111
theorem B1934271 : Blo 1933435 1934271 := bstep (se 1 (by rfl) ⟨1450703, by rfl⟩ : syracuseStep 1934271 = 2901407) B2901407
theorem B2901413 : Blo 1933435 2901413 := bbase (se 4 (by rfl) ⟨272007, by rfl⟩ : syracuseStep 2901413 = 544015) (by norm_num)
theorem B1934275 : Blo 1933435 1934275 := bstep (se 1 (by rfl) ⟨1450706, by rfl⟩ : syracuseStep 1934275 = 2901413) B2901413
theorem B2448073 : Blo 1933435 2448073 := bbase (se 2 (by rfl) ⟨918027, by rfl⟩ : syracuseStep 2448073 = 1836055) (by norm_num)
theorem B3264097 : Blo 1933435 3264097 := bstep (se 2 (by rfl) ⟨1224036, by rfl⟩ : syracuseStep 3264097 = 2448073) B2448073
theorem B4352129 : Blo 1933435 4352129 := bstep (se 2 (by rfl) ⟨1632048, by rfl⟩ : syracuseStep 4352129 = 3264097) B3264097
theorem B2901419 : Blo 1933435 2901419 := bstep (se 1 (by rfl) ⟨2176064, by rfl⟩ : syracuseStep 2901419 = 4352129) B4352129
theorem B1934279 : Blo 1933435 1934279 := bstep (se 1 (by rfl) ⟨1450709, by rfl⟩ : syracuseStep 1934279 = 2901419) B2901419
theorem B2176069 : Blo 1933435 2176069 := bbase (se 4 (by rfl) ⟨204006, by rfl⟩ : syracuseStep 2176069 = 408013) (by norm_num)
theorem B2901425 : Blo 1933435 2901425 := bstep (se 2 (by rfl) ⟨1088034, by rfl⟩ : syracuseStep 2901425 = 2176069) B2176069
theorem B1934283 : Blo 1933435 1934283 := bstep (se 1 (by rfl) ⟨1450712, by rfl⟩ : syracuseStep 1934283 = 2901425) B2901425
theorem B3672125 : Blo 1933435 3672125 := bbase (se 3 (by rfl) ⟨688523, by rfl⟩ : syracuseStep 3672125 = 1377047) (by norm_num)
theorem B2448083 : Blo 1933435 2448083 := bstep (se 1 (by rfl) ⟨1836062, by rfl⟩ : syracuseStep 2448083 = 3672125) B3672125
theorem B6528221 : Blo 1933435 6528221 := bstep (se 3 (by rfl) ⟨1224041, by rfl⟩ : syracuseStep 6528221 = 2448083) B2448083
theorem B4352147 : Blo 1933435 4352147 := bstep (se 1 (by rfl) ⟨3264110, by rfl⟩ : syracuseStep 4352147 = 6528221) B6528221
theorem B2901431 : Blo 1933435 2901431 := bstep (se 1 (by rfl) ⟨2176073, by rfl⟩ : syracuseStep 2901431 = 4352147) B4352147
theorem B1934287 : Blo 1933435 1934287 := bstep (se 1 (by rfl) ⟨1450715, by rfl⟩ : syracuseStep 1934287 = 2901431) B2901431
theorem B2901437 : Blo 1933435 2901437 := bbase (se 3 (by rfl) ⟨544019, by rfl⟩ : syracuseStep 2901437 = 1088039) (by norm_num)
theorem B1934291 : Blo 1933435 1934291 := bstep (se 1 (by rfl) ⟨1450718, by rfl⟩ : syracuseStep 1934291 = 2901437) B2901437
theorem B4352165 : Blo 1933435 4352165 := bbase (se 4 (by rfl) ⟨408015, by rfl⟩ : syracuseStep 4352165 = 816031) (by norm_num)
theorem B2901443 : Blo 1933435 2901443 := bstep (se 1 (by rfl) ⟨2176082, by rfl⟩ : syracuseStep 2901443 = 4352165) B4352165
theorem B1934295 : Blo 1933435 1934295 := bstep (se 1 (by rfl) ⟨1450721, by rfl⟩ : syracuseStep 1934295 = 2901443) B2901443
theorem B4896197 : Blo 1933435 4896197 := bbase (se 4 (by rfl) ⟨459018, by rfl⟩ : syracuseStep 4896197 = 918037) (by norm_num)
theorem B3264131 : Blo 1933435 3264131 := bstep (se 1 (by rfl) ⟨2448098, by rfl⟩ : syracuseStep 3264131 = 4896197) B4896197
theorem B2176087 : Blo 1933435 2176087 := bstep (se 1 (by rfl) ⟨1632065, by rfl⟩ : syracuseStep 2176087 = 3264131) B3264131
theorem B2901449 : Blo 1933435 2901449 := bstep (se 2 (by rfl) ⟨1088043, by rfl⟩ : syracuseStep 2901449 = 2176087) B2176087
theorem B1934299 : Blo 1933435 1934299 := bstep (se 1 (by rfl) ⟨1450724, by rfl⟩ : syracuseStep 1934299 = 2901449) B2901449
theorem B2791693 : Blo 1933435 2791693 := bbase (se 3 (by rfl) ⟨523442, by rfl⟩ : syracuseStep 2791693 = 1046885) (by norm_num)
theorem B3722257 : Blo 1933435 3722257 := bstep (se 2 (by rfl) ⟨1395846, by rfl⟩ : syracuseStep 3722257 = 2791693) B2791693
theorem B19852037 : Blo 1933435 19852037 := bstep (se 4 (by rfl) ⟨1861128, by rfl⟩ : syracuseStep 19852037 = 3722257) B3722257
theorem B13234691 : Blo 1933435 13234691 := bstep (se 1 (by rfl) ⟨9926018, by rfl⟩ : syracuseStep 13234691 = 19852037) B19852037
theorem B35292509 : Blo 1933435 35292509 := bstep (se 3 (by rfl) ⟨6617345, by rfl⟩ : syracuseStep 35292509 = 13234691) B13234691
theorem B23528339 : Blo 1933435 23528339 := bstep (se 1 (by rfl) ⟨17646254, by rfl⟩ : syracuseStep 23528339 = 35292509) B35292509
theorem B15685559 : Blo 1933435 15685559 := bstep (se 1 (by rfl) ⟨11764169, by rfl⟩ : syracuseStep 15685559 = 23528339) B23528339
theorem B10457039 : Blo 1933435 10457039 := bstep (se 1 (by rfl) ⟨7842779, by rfl⟩ : syracuseStep 10457039 = 15685559) B15685559
theorem B6971359 : Blo 1933435 6971359 := bstep (se 1 (by rfl) ⟨5228519, by rfl⟩ : syracuseStep 6971359 = 10457039) B10457039
theorem B9295145 : Blo 1933435 9295145 := bstep (se 2 (by rfl) ⟨3485679, by rfl⟩ : syracuseStep 9295145 = 6971359) B6971359
theorem B6196763 : Blo 1933435 6196763 := bstep (se 1 (by rfl) ⟨4647572, by rfl⟩ : syracuseStep 6196763 = 9295145) B9295145
theorem B4131175 : Blo 1933435 4131175 := bstep (se 1 (by rfl) ⟨3098381, by rfl⟩ : syracuseStep 4131175 = 6196763) B6196763
theorem B5508233 : Blo 1933435 5508233 := bstep (se 2 (by rfl) ⟨2065587, by rfl⟩ : syracuseStep 5508233 = 4131175) B4131175
theorem B3672155 : Blo 1933435 3672155 := bstep (se 1 (by rfl) ⟨2754116, by rfl⟩ : syracuseStep 3672155 = 5508233) B5508233
theorem B9792413 : Blo 1933435 9792413 := bstep (se 3 (by rfl) ⟨1836077, by rfl⟩ : syracuseStep 9792413 = 3672155) B3672155
theorem B6528275 : Blo 1933435 6528275 := bstep (se 1 (by rfl) ⟨4896206, by rfl⟩ : syracuseStep 6528275 = 9792413) B9792413
theorem B4352183 : Blo 1933435 4352183 := bstep (se 1 (by rfl) ⟨3264137, by rfl⟩ : syracuseStep 4352183 = 6528275) B6528275
theorem B2901455 : Blo 1933435 2901455 := bstep (se 1 (by rfl) ⟨2176091, by rfl⟩ : syracuseStep 2901455 = 4352183) B4352183
theorem B1934303 : Blo 1933435 1934303 := bstep (se 1 (by rfl) ⟨1450727, by rfl⟩ : syracuseStep 1934303 = 2901455) B2901455
theorem B2901461 : Blo 1933435 2901461 := bbase (se 7 (by rfl) ⟨34001, by rfl⟩ : syracuseStep 2901461 = 68003) (by norm_num)
theorem B1934307 : Blo 1933435 1934307 := bstep (se 1 (by rfl) ⟨1450730, by rfl⟩ : syracuseStep 1934307 = 2901461) B2901461
theorem B7344341 : Blo 1933435 7344341 := bbase (se 7 (by rfl) ⟨86066, by rfl⟩ : syracuseStep 7344341 = 172133) (by norm_num)
theorem B4896227 : Blo 1933435 4896227 := bstep (se 1 (by rfl) ⟨3672170, by rfl⟩ : syracuseStep 4896227 = 7344341) B7344341
theorem B3264151 : Blo 1933435 3264151 := bstep (se 1 (by rfl) ⟨2448113, by rfl⟩ : syracuseStep 3264151 = 4896227) B4896227
theorem B4352201 : Blo 1933435 4352201 := bstep (se 2 (by rfl) ⟨1632075, by rfl⟩ : syracuseStep 4352201 = 3264151) B3264151
theorem B2901467 : Blo 1933435 2901467 := bstep (se 1 (by rfl) ⟨2176100, by rfl⟩ : syracuseStep 2901467 = 4352201) B4352201
theorem B1934311 : Blo 1933435 1934311 := bstep (se 1 (by rfl) ⟨1450733, by rfl⟩ : syracuseStep 1934311 = 2901467) B2901467
theorem B2176105 : Blo 1933435 2176105 := bbase (se 2 (by rfl) ⟨816039, by rfl⟩ : syracuseStep 2176105 = 1632079) (by norm_num)
theorem B2901473 : Blo 1933435 2901473 := bstep (se 2 (by rfl) ⟨1088052, by rfl⟩ : syracuseStep 2901473 = 2176105) B2176105
theorem B1934315 : Blo 1933435 1934315 := bstep (se 1 (by rfl) ⟨1450736, by rfl⟩ : syracuseStep 1934315 = 2901473) B2901473
theorem B3308701 : Blo 1933435 3308701 := bbase (se 3 (by rfl) ⟨620381, by rfl⟩ : syracuseStep 3308701 = 1240763) (by norm_num)
theorem B4411601 : Blo 1933435 4411601 := bstep (se 2 (by rfl) ⟨1654350, by rfl⟩ : syracuseStep 4411601 = 3308701) B3308701
theorem B2941067 : Blo 1933435 2941067 := bstep (se 1 (by rfl) ⟨2205800, by rfl⟩ : syracuseStep 2941067 = 4411601) B4411601
theorem B7842845 : Blo 1933435 7842845 := bstep (se 3 (by rfl) ⟨1470533, by rfl⟩ : syracuseStep 7842845 = 2941067) B2941067
theorem B5228563 : Blo 1933435 5228563 := bstep (se 1 (by rfl) ⟨3921422, by rfl⟩ : syracuseStep 5228563 = 7842845) B7842845
theorem B6971417 : Blo 1933435 6971417 := bstep (se 2 (by rfl) ⟨2614281, by rfl⟩ : syracuseStep 6971417 = 5228563) B5228563
theorem B4647611 : Blo 1933435 4647611 := bstep (se 1 (by rfl) ⟨3485708, by rfl⟩ : syracuseStep 4647611 = 6971417) B6971417
theorem B3098407 : Blo 1933435 3098407 := bstep (se 1 (by rfl) ⟨2323805, by rfl⟩ : syracuseStep 3098407 = 4647611) B4647611
theorem B4131209 : Blo 1933435 4131209 := bstep (se 2 (by rfl) ⟨1549203, by rfl⟩ : syracuseStep 4131209 = 3098407) B3098407
theorem B11016557 : Blo 1933435 11016557 := bstep (se 3 (by rfl) ⟨2065604, by rfl⟩ : syracuseStep 11016557 = 4131209) B4131209
theorem B7344371 : Blo 1933435 7344371 := bstep (se 1 (by rfl) ⟨5508278, by rfl⟩ : syracuseStep 7344371 = 11016557) B11016557
theorem B4896247 : Blo 1933435 4896247 := bstep (se 1 (by rfl) ⟨3672185, by rfl⟩ : syracuseStep 4896247 = 7344371) B7344371
theorem B6528329 : Blo 1933435 6528329 := bstep (se 2 (by rfl) ⟨2448123, by rfl⟩ : syracuseStep 6528329 = 4896247) B4896247
theorem B4352219 : Blo 1933435 4352219 := bstep (se 1 (by rfl) ⟨3264164, by rfl⟩ : syracuseStep 4352219 = 6528329) B6528329
theorem B2901479 : Blo 1933435 2901479 := bstep (se 1 (by rfl) ⟨2176109, by rfl⟩ : syracuseStep 2901479 = 4352219) B4352219
theorem B1934319 : Blo 1933435 1934319 := bstep (se 1 (by rfl) ⟨1450739, by rfl⟩ : syracuseStep 1934319 = 2901479) B2901479
theorem B2901485 : Blo 1933435 2901485 := bbase (se 3 (by rfl) ⟨544028, by rfl⟩ : syracuseStep 2901485 = 1088057) (by norm_num)
theorem B1934323 : Blo 1933435 1934323 := bstep (se 1 (by rfl) ⟨1450742, by rfl⟩ : syracuseStep 1934323 = 2901485) B2901485
theorem B4352237 : Blo 1933435 4352237 := bbase (se 3 (by rfl) ⟨816044, by rfl⟩ : syracuseStep 4352237 = 1632089) (by norm_num)
theorem B2901491 : Blo 1933435 2901491 := bstep (se 1 (by rfl) ⟨2176118, by rfl⟩ : syracuseStep 2901491 = 4352237) B4352237
theorem B1934327 : Blo 1933435 1934327 := bstep (se 1 (by rfl) ⟨1450745, by rfl⟩ : syracuseStep 1934327 = 2901491) B2901491
theorem B2754157 : Blo 1933435 2754157 := bbase (se 3 (by rfl) ⟨516404, by rfl⟩ : syracuseStep 2754157 = 1032809) (by norm_num)
theorem B3672209 : Blo 1933435 3672209 := bstep (se 2 (by rfl) ⟨1377078, by rfl⟩ : syracuseStep 3672209 = 2754157) B2754157
theorem B2448139 : Blo 1933435 2448139 := bstep (se 1 (by rfl) ⟨1836104, by rfl⟩ : syracuseStep 2448139 = 3672209) B3672209
theorem B3264185 : Blo 1933435 3264185 := bstep (se 2 (by rfl) ⟨1224069, by rfl⟩ : syracuseStep 3264185 = 2448139) B2448139
theorem B2176123 : Blo 1933435 2176123 := bstep (se 1 (by rfl) ⟨1632092, by rfl⟩ : syracuseStep 2176123 = 3264185) B3264185
theorem B2901497 : Blo 1933435 2901497 := bstep (se 2 (by rfl) ⟨1088061, by rfl⟩ : syracuseStep 2901497 = 2176123) B2176123
theorem B1934331 : Blo 1933435 1934331 := bstep (se 1 (by rfl) ⟨1450748, by rfl⟩ : syracuseStep 1934331 = 2901497) B2901497
theorem B21199765 : Blo 1933435 21199765 := bbase (se 6 (by rfl) ⟨496869, by rfl⟩ : syracuseStep 21199765 = 993739) (by norm_num)
theorem B28266353 : Blo 1933435 28266353 := bstep (se 2 (by rfl) ⟨10599882, by rfl⟩ : syracuseStep 28266353 = 21199765) B21199765
theorem B18844235 : Blo 1933435 18844235 := bstep (se 1 (by rfl) ⟨14133176, by rfl⟩ : syracuseStep 18844235 = 28266353) B28266353
theorem B12562823 : Blo 1933435 12562823 := bstep (se 1 (by rfl) ⟨9422117, by rfl⟩ : syracuseStep 12562823 = 18844235) B18844235
theorem B33500861 : Blo 1933435 33500861 := bstep (se 3 (by rfl) ⟨6281411, by rfl⟩ : syracuseStep 33500861 = 12562823) B12562823
theorem B22333907 : Blo 1933435 22333907 := bstep (se 1 (by rfl) ⟨16750430, by rfl⟩ : syracuseStep 22333907 = 33500861) B33500861
theorem B14889271 : Blo 1933435 14889271 := bstep (se 1 (by rfl) ⟨11166953, by rfl⟩ : syracuseStep 14889271 = 22333907) B22333907
theorem B19852361 : Blo 1933435 19852361 := bstep (se 2 (by rfl) ⟨7444635, by rfl⟩ : syracuseStep 19852361 = 14889271) B14889271
theorem B13234907 : Blo 1933435 13234907 := bstep (se 1 (by rfl) ⟨9926180, by rfl⟩ : syracuseStep 13234907 = 19852361) B19852361
theorem B8823271 : Blo 1933435 8823271 := bstep (se 1 (by rfl) ⟨6617453, by rfl⟩ : syracuseStep 8823271 = 13234907) B13234907
theorem B11764361 : Blo 1933435 11764361 := bstep (se 2 (by rfl) ⟨4411635, by rfl⟩ : syracuseStep 11764361 = 8823271) B8823271
theorem B7842907 : Blo 1933435 7842907 := bstep (se 1 (by rfl) ⟨5882180, by rfl⟩ : syracuseStep 7842907 = 11764361) B11764361
theorem B10457209 : Blo 1933435 10457209 := bstep (se 2 (by rfl) ⟨3921453, by rfl⟩ : syracuseStep 10457209 = 7842907) B7842907
theorem B13942945 : Blo 1933435 13942945 := bstep (se 2 (by rfl) ⟨5228604, by rfl⟩ : syracuseStep 13942945 = 10457209) B10457209
theorem B74362373 : Blo 1933435 74362373 := bstep (se 4 (by rfl) ⟨6971472, by rfl⟩ : syracuseStep 74362373 = 13942945) B13942945
theorem B49574915 : Blo 1933435 49574915 := bstep (se 1 (by rfl) ⟨37181186, by rfl⟩ : syracuseStep 49574915 = 74362373) B74362373
theorem B33049943 : Blo 1933435 33049943 := bstep (se 1 (by rfl) ⟨24787457, by rfl⟩ : syracuseStep 33049943 = 49574915) B49574915
theorem B22033295 : Blo 1933435 22033295 := bstep (se 1 (by rfl) ⟨16524971, by rfl⟩ : syracuseStep 22033295 = 33049943) B33049943
theorem B14688863 : Blo 1933435 14688863 := bstep (se 1 (by rfl) ⟨11016647, by rfl⟩ : syracuseStep 14688863 = 22033295) B22033295
theorem B9792575 : Blo 1933435 9792575 := bstep (se 1 (by rfl) ⟨7344431, by rfl⟩ : syracuseStep 9792575 = 14688863) B14688863
theorem B6528383 : Blo 1933435 6528383 := bstep (se 1 (by rfl) ⟨4896287, by rfl⟩ : syracuseStep 6528383 = 9792575) B9792575
theorem B4352255 : Blo 1933435 4352255 := bstep (se 1 (by rfl) ⟨3264191, by rfl⟩ : syracuseStep 4352255 = 6528383) B6528383
theorem B2901503 : Blo 1933435 2901503 := bstep (se 1 (by rfl) ⟨2176127, by rfl⟩ : syracuseStep 2901503 = 4352255) B4352255
theorem B1934335 : Blo 1933435 1934335 := bstep (se 1 (by rfl) ⟨1450751, by rfl⟩ : syracuseStep 1934335 = 2901503) B2901503
theorem B2901509 : Blo 1933435 2901509 := bbase (se 4 (by rfl) ⟨272016, by rfl⟩ : syracuseStep 2901509 = 544033) (by norm_num)
theorem B1934339 : Blo 1933435 1934339 := bstep (se 1 (by rfl) ⟨1450754, by rfl⟩ : syracuseStep 1934339 = 2901509) B2901509
theorem B3264205 : Blo 1933435 3264205 := bbase (se 3 (by rfl) ⟨612038, by rfl⟩ : syracuseStep 3264205 = 1224077) (by norm_num)
theorem B4352273 : Blo 1933435 4352273 := bstep (se 2 (by rfl) ⟨1632102, by rfl⟩ : syracuseStep 4352273 = 3264205) B3264205
theorem B2901515 : Blo 1933435 2901515 := bstep (se 1 (by rfl) ⟨2176136, by rfl⟩ : syracuseStep 2901515 = 4352273) B4352273
theorem B1934343 : Blo 1933435 1934343 := bstep (se 1 (by rfl) ⟨1450757, by rfl⟩ : syracuseStep 1934343 = 2901515) B2901515
theorem B2176141 : Blo 1933435 2176141 := bbase (se 3 (by rfl) ⟨408026, by rfl⟩ : syracuseStep 2176141 = 816053) (by norm_num)
theorem B2901521 : Blo 1933435 2901521 := bstep (se 2 (by rfl) ⟨1088070, by rfl⟩ : syracuseStep 2901521 = 2176141) B2176141
theorem B1934347 : Blo 1933435 1934347 := bstep (se 1 (by rfl) ⟨1450760, by rfl⟩ : syracuseStep 1934347 = 2901521) B2901521
theorem B6528437 : Blo 1933435 6528437 := bbase (se 5 (by rfl) ⟨306020, by rfl⟩ : syracuseStep 6528437 = 612041) (by norm_num)
theorem B4352291 : Blo 1933435 4352291 := bstep (se 1 (by rfl) ⟨3264218, by rfl⟩ : syracuseStep 4352291 = 6528437) B6528437
theorem B2901527 : Blo 1933435 2901527 := bstep (se 1 (by rfl) ⟨2176145, by rfl⟩ : syracuseStep 2901527 = 4352291) B4352291
theorem B1934351 : Blo 1933435 1934351 := bstep (se 1 (by rfl) ⟨1450763, by rfl⟩ : syracuseStep 1934351 = 2901527) B2901527
theorem B2901533 : Blo 1933435 2901533 := bbase (se 3 (by rfl) ⟨544037, by rfl⟩ : syracuseStep 2901533 = 1088075) (by norm_num)
theorem B1934355 : Blo 1933435 1934355 := bstep (se 1 (by rfl) ⟨1450766, by rfl⟩ : syracuseStep 1934355 = 2901533) B2901533
theorem B4352309 : Blo 1933435 4352309 := bbase (se 5 (by rfl) ⟨204014, by rfl⟩ : syracuseStep 4352309 = 408029) (by norm_num)
theorem B2901539 : Blo 1933435 2901539 := bstep (se 1 (by rfl) ⟨2176154, by rfl⟩ : syracuseStep 2901539 = 4352309) B4352309
theorem B1934359 : Blo 1933435 1934359 := bstep (se 1 (by rfl) ⟨1450769, by rfl⟩ : syracuseStep 1934359 = 2901539) B2901539
theorem B7066693 : Blo 1933435 7066693 := bbase (se 4 (by rfl) ⟨662502, by rfl⟩ : syracuseStep 7066693 = 1325005) (by norm_num)
theorem B9422257 : Blo 1933435 9422257 := bstep (se 2 (by rfl) ⟨3533346, by rfl⟩ : syracuseStep 9422257 = 7066693) B7066693
theorem B12563009 : Blo 1933435 12563009 := bstep (se 2 (by rfl) ⟨4711128, by rfl⟩ : syracuseStep 12563009 = 9422257) B9422257
theorem B8375339 : Blo 1933435 8375339 := bstep (se 1 (by rfl) ⟨6281504, by rfl⟩ : syracuseStep 8375339 = 12563009) B12563009
theorem B22334237 : Blo 1933435 22334237 := bstep (se 3 (by rfl) ⟨4187669, by rfl⟩ : syracuseStep 22334237 = 8375339) B8375339
theorem B14889491 : Blo 1933435 14889491 := bstep (se 1 (by rfl) ⟨11167118, by rfl⟩ : syracuseStep 14889491 = 22334237) B22334237
theorem B9926327 : Blo 1933435 9926327 := bstep (se 1 (by rfl) ⟨7444745, by rfl⟩ : syracuseStep 9926327 = 14889491) B14889491
theorem B6617551 : Blo 1933435 6617551 := bstep (se 1 (by rfl) ⟨4963163, by rfl⟩ : syracuseStep 6617551 = 9926327) B9926327
theorem B8823401 : Blo 1933435 8823401 := bstep (se 2 (by rfl) ⟨3308775, by rfl⟩ : syracuseStep 8823401 = 6617551) B6617551
theorem B5882267 : Blo 1933435 5882267 := bstep (se 1 (by rfl) ⟨4411700, by rfl⟩ : syracuseStep 5882267 = 8823401) B8823401
theorem B15686045 : Blo 1933435 15686045 := bstep (se 3 (by rfl) ⟨2941133, by rfl⟩ : syracuseStep 15686045 = 5882267) B5882267
theorem B10457363 : Blo 1933435 10457363 := bstep (se 1 (by rfl) ⟨7843022, by rfl⟩ : syracuseStep 10457363 = 15686045) B15686045
theorem B27886301 : Blo 1933435 27886301 := bstep (se 3 (by rfl) ⟨5228681, by rfl⟩ : syracuseStep 27886301 = 10457363) B10457363
theorem B18590867 : Blo 1933435 18590867 := bstep (se 1 (by rfl) ⟨13943150, by rfl⟩ : syracuseStep 18590867 = 27886301) B27886301
theorem B12393911 : Blo 1933435 12393911 := bstep (se 1 (by rfl) ⟨9295433, by rfl⟩ : syracuseStep 12393911 = 18590867) B18590867
theorem B8262607 : Blo 1933435 8262607 := bstep (se 1 (by rfl) ⟨6196955, by rfl⟩ : syracuseStep 8262607 = 12393911) B12393911
theorem B11016809 : Blo 1933435 11016809 := bstep (se 2 (by rfl) ⟨4131303, by rfl⟩ : syracuseStep 11016809 = 8262607) B8262607
theorem B7344539 : Blo 1933435 7344539 := bstep (se 1 (by rfl) ⟨5508404, by rfl⟩ : syracuseStep 7344539 = 11016809) B11016809
theorem B4896359 : Blo 1933435 4896359 := bstep (se 1 (by rfl) ⟨3672269, by rfl⟩ : syracuseStep 4896359 = 7344539) B7344539
theorem B3264239 : Blo 1933435 3264239 := bstep (se 1 (by rfl) ⟨2448179, by rfl⟩ : syracuseStep 3264239 = 4896359) B4896359
theorem B2176159 : Blo 1933435 2176159 := bstep (se 1 (by rfl) ⟨1632119, by rfl⟩ : syracuseStep 2176159 = 3264239) B3264239
theorem B2901545 : Blo 1933435 2901545 := bstep (se 2 (by rfl) ⟨1088079, by rfl⟩ : syracuseStep 2901545 = 2176159) B2176159
theorem B1934363 : Blo 1933435 1934363 := bstep (se 1 (by rfl) ⟨1450772, by rfl⟩ : syracuseStep 1934363 = 2901545) B2901545
theorem B16750709 : Blo 1933435 16750709 := bbase (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) (by norm_num)
theorem B11167139 : Blo 1933435 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B7444759 : Blo 1933435 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B9926345 : Blo 1933435 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B26470253 : Blo 1933435 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B17646835 : Blo 1933435 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B23529113 : Blo 1933435 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B15686075 : Blo 1933435 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B41829533 : Blo 1933435 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B27886355 : Blo 1933435 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B18590903 : Blo 1933435 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B12393935 : Blo 1933435 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B8262623 : Blo 1933435 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B5508415 : Blo 1933435 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B7344553 : Blo 1933435 7344553 := bstep (se 2 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 7344553 = 5508415) B5508415
theorem B9792737 : Blo 1933435 9792737 := bstep (se 2 (by rfl) ⟨3672276, by rfl⟩ : syracuseStep 9792737 = 7344553) B7344553
theorem B6528491 : Blo 1933435 6528491 := bstep (se 1 (by rfl) ⟨4896368, by rfl⟩ : syracuseStep 6528491 = 9792737) B9792737
theorem B4352327 : Blo 1933435 4352327 := bstep (se 1 (by rfl) ⟨3264245, by rfl⟩ : syracuseStep 4352327 = 6528491) B6528491
theorem B2901551 : Blo 1933435 2901551 := bstep (se 1 (by rfl) ⟨2176163, by rfl⟩ : syracuseStep 2901551 = 4352327) B4352327
theorem B1934367 : Blo 1933435 1934367 := bstep (se 1 (by rfl) ⟨1450775, by rfl⟩ : syracuseStep 1934367 = 2901551) B2901551
theorem B2901557 : Blo 1933435 2901557 := bbase (se 5 (by rfl) ⟨136010, by rfl⟩ : syracuseStep 2901557 = 272021) (by norm_num)
theorem B1934371 : Blo 1933435 1934371 := bstep (se 1 (by rfl) ⟨1450778, by rfl⟩ : syracuseStep 1934371 = 2901557) B2901557
theorem B4896389 : Blo 1933435 4896389 := bbase (se 4 (by rfl) ⟨459036, by rfl⟩ : syracuseStep 4896389 = 918073) (by norm_num)
theorem B3264259 : Blo 1933435 3264259 := bstep (se 1 (by rfl) ⟨2448194, by rfl⟩ : syracuseStep 3264259 = 4896389) B4896389
theorem B4352345 : Blo 1933435 4352345 := bstep (se 2 (by rfl) ⟨1632129, by rfl⟩ : syracuseStep 4352345 = 3264259) B3264259
theorem B2901563 : Blo 1933435 2901563 := bstep (se 1 (by rfl) ⟨2176172, by rfl⟩ : syracuseStep 2901563 = 4352345) B4352345
theorem B1934375 : Blo 1933435 1934375 := bstep (se 1 (by rfl) ⟨1450781, by rfl⟩ : syracuseStep 1934375 = 2901563) B2901563
theorem B2176177 : Blo 1933435 2176177 := bbase (se 2 (by rfl) ⟨816066, by rfl⟩ : syracuseStep 2176177 = 1632133) (by norm_num)
theorem B2901569 : Blo 1933435 2901569 := bstep (se 2 (by rfl) ⟨1088088, by rfl⟩ : syracuseStep 2901569 = 2176177) B2176177
theorem B1934379 : Blo 1933435 1934379 := bstep (se 1 (by rfl) ⟨1450784, by rfl⟩ : syracuseStep 1934379 = 2901569) B2901569
theorem B2065673 : Blo 1933435 2065673 := bbase (se 2 (by rfl) ⟨774627, by rfl⟩ : syracuseStep 2065673 = 1549255) (by norm_num)
theorem B5508461 : Blo 1933435 5508461 := bstep (se 3 (by rfl) ⟨1032836, by rfl⟩ : syracuseStep 5508461 = 2065673) B2065673
theorem B3672307 : Blo 1933435 3672307 := bstep (se 1 (by rfl) ⟨2754230, by rfl⟩ : syracuseStep 3672307 = 5508461) B5508461
theorem B4896409 : Blo 1933435 4896409 := bstep (se 2 (by rfl) ⟨1836153, by rfl⟩ : syracuseStep 4896409 = 3672307) B3672307
theorem B6528545 : Blo 1933435 6528545 := bstep (se 2 (by rfl) ⟨2448204, by rfl⟩ : syracuseStep 6528545 = 4896409) B4896409
theorem B4352363 : Blo 1933435 4352363 := bstep (se 1 (by rfl) ⟨3264272, by rfl⟩ : syracuseStep 4352363 = 6528545) B6528545
theorem B2901575 : Blo 1933435 2901575 := bstep (se 1 (by rfl) ⟨2176181, by rfl⟩ : syracuseStep 2901575 = 4352363) B4352363
theorem B1934383 : Blo 1933435 1934383 := bstep (se 1 (by rfl) ⟨1450787, by rfl⟩ : syracuseStep 1934383 = 2901575) B2901575
theorem B2901581 : Blo 1933435 2901581 := bbase (se 3 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 2901581 = 1088093) (by norm_num)
theorem B1934387 : Blo 1933435 1934387 := bstep (se 1 (by rfl) ⟨1450790, by rfl⟩ : syracuseStep 1934387 = 2901581) B2901581
theorem B4352381 : Blo 1933435 4352381 := bbase (se 3 (by rfl) ⟨816071, by rfl⟩ : syracuseStep 4352381 = 1632143) (by norm_num)
theorem B2901587 : Blo 1933435 2901587 := bstep (se 1 (by rfl) ⟨2176190, by rfl⟩ : syracuseStep 2901587 = 4352381) B4352381
theorem B1934391 : Blo 1933435 1934391 := bstep (se 1 (by rfl) ⟨1450793, by rfl⟩ : syracuseStep 1934391 = 2901587) B2901587
theorem B3264293 : Blo 1933435 3264293 := bbase (se 4 (by rfl) ⟨306027, by rfl⟩ : syracuseStep 3264293 = 612055) (by norm_num)
theorem B2176195 : Blo 1933435 2176195 := bstep (se 1 (by rfl) ⟨1632146, by rfl⟩ : syracuseStep 2176195 = 3264293) B3264293
theorem B2901593 : Blo 1933435 2901593 := bstep (se 2 (by rfl) ⟨1088097, by rfl⟩ : syracuseStep 2901593 = 2176195) B2176195
theorem B1934395 : Blo 1933435 1934395 := bstep (se 1 (by rfl) ⟨1450796, by rfl⟩ : syracuseStep 1934395 = 2901593) B2901593
theorem B2754253 : Blo 1933435 2754253 := bbase (se 3 (by rfl) ⟨516422, by rfl⟩ : syracuseStep 2754253 = 1032845) (by norm_num)
theorem B14689349 : Blo 1933435 14689349 := bstep (se 4 (by rfl) ⟨1377126, by rfl⟩ : syracuseStep 14689349 = 2754253) B2754253
theorem B9792899 : Blo 1933435 9792899 := bstep (se 1 (by rfl) ⟨7344674, by rfl⟩ : syracuseStep 9792899 = 14689349) B14689349
theorem B6528599 : Blo 1933435 6528599 := bstep (se 1 (by rfl) ⟨4896449, by rfl⟩ : syracuseStep 6528599 = 9792899) B9792899
theorem B4352399 : Blo 1933435 4352399 := bstep (se 1 (by rfl) ⟨3264299, by rfl⟩ : syracuseStep 4352399 = 6528599) B6528599
theorem B2901599 : Blo 1933435 2901599 := bstep (se 1 (by rfl) ⟨2176199, by rfl⟩ : syracuseStep 2901599 = 4352399) B4352399
theorem B1934399 : Blo 1933435 1934399 := bstep (se 1 (by rfl) ⟨1450799, by rfl⟩ : syracuseStep 1934399 = 2901599) B2901599
theorem B2901605 : Blo 1933435 2901605 := bbase (se 4 (by rfl) ⟨272025, by rfl⟩ : syracuseStep 2901605 = 544051) (by norm_num)
theorem B1934403 : Blo 1933435 1934403 := bstep (se 1 (by rfl) ⟨1450802, by rfl⟩ : syracuseStep 1934403 = 2901605) B2901605
theorem B3098549 : Blo 1933435 3098549 := bbase (se 5 (by rfl) ⟨145244, by rfl⟩ : syracuseStep 3098549 = 290489) (by norm_num)
theorem B2065699 : Blo 1933435 2065699 := bstep (se 1 (by rfl) ⟨1549274, by rfl⟩ : syracuseStep 2065699 = 3098549) B3098549
theorem B2754265 : Blo 1933435 2754265 := bstep (se 2 (by rfl) ⟨1032849, by rfl⟩ : syracuseStep 2754265 = 2065699) B2065699
theorem B3672353 : Blo 1933435 3672353 := bstep (se 2 (by rfl) ⟨1377132, by rfl⟩ : syracuseStep 3672353 = 2754265) B2754265
theorem B2448235 : Blo 1933435 2448235 := bstep (se 1 (by rfl) ⟨1836176, by rfl⟩ : syracuseStep 2448235 = 3672353) B3672353
theorem B3264313 : Blo 1933435 3264313 := bstep (se 2 (by rfl) ⟨1224117, by rfl⟩ : syracuseStep 3264313 = 2448235) B2448235
theorem B4352417 : Blo 1933435 4352417 := bstep (se 2 (by rfl) ⟨1632156, by rfl⟩ : syracuseStep 4352417 = 3264313) B3264313
theorem B2901611 : Blo 1933435 2901611 := bstep (se 1 (by rfl) ⟨2176208, by rfl⟩ : syracuseStep 2901611 = 4352417) B4352417
theorem B1934407 : Blo 1933435 1934407 := bstep (se 1 (by rfl) ⟨1450805, by rfl⟩ : syracuseStep 1934407 = 2901611) B2901611
theorem B2176213 : Blo 1933435 2176213 := bbase (se 7 (by rfl) ⟨25502, by rfl⟩ : syracuseStep 2176213 = 51005) (by norm_num)
theorem B2901617 : Blo 1933435 2901617 := bstep (se 2 (by rfl) ⟨1088106, by rfl⟩ : syracuseStep 2901617 = 2176213) B2176213
theorem B1934411 : Blo 1933435 1934411 := bstep (se 1 (by rfl) ⟨1450808, by rfl⟩ : syracuseStep 1934411 = 2901617) B2901617
theorem B2448245 : Blo 1933435 2448245 := bbase (se 5 (by rfl) ⟨114761, by rfl⟩ : syracuseStep 2448245 = 229523) (by norm_num)
theorem B6528653 : Blo 1933435 6528653 := bstep (se 3 (by rfl) ⟨1224122, by rfl⟩ : syracuseStep 6528653 = 2448245) B2448245
theorem B4352435 : Blo 1933435 4352435 := bstep (se 1 (by rfl) ⟨3264326, by rfl⟩ : syracuseStep 4352435 = 6528653) B6528653
theorem B2901623 : Blo 1933435 2901623 := bstep (se 1 (by rfl) ⟨2176217, by rfl⟩ : syracuseStep 2901623 = 4352435) B4352435
theorem B1934415 : Blo 1933435 1934415 := bstep (se 1 (by rfl) ⟨1450811, by rfl⟩ : syracuseStep 1934415 = 2901623) B2901623
theorem B2901629 : Blo 1933435 2901629 := bbase (se 3 (by rfl) ⟨544055, by rfl⟩ : syracuseStep 2901629 = 1088111) (by norm_num)
theorem B1934419 : Blo 1933435 1934419 := bstep (se 1 (by rfl) ⟨1450814, by rfl⟩ : syracuseStep 1934419 = 2901629) B2901629
theorem B4352453 : Blo 1933435 4352453 := bbase (se 4 (by rfl) ⟨408042, by rfl⟩ : syracuseStep 4352453 = 816085) (by norm_num)
theorem B2901635 : Blo 1933435 2901635 := bstep (se 1 (by rfl) ⟨2176226, by rfl⟩ : syracuseStep 2901635 = 4352453) B4352453
theorem B1934423 : Blo 1933435 1934423 := bstep (se 1 (by rfl) ⟨1450817, by rfl⟩ : syracuseStep 1934423 = 2901635) B2901635
theorem B3183709 : Blo 1933435 3183709 := bbase (se 3 (by rfl) ⟨596945, by rfl⟩ : syracuseStep 3183709 = 1193891) (by norm_num)
theorem B4244945 : Blo 1933435 4244945 := bstep (se 2 (by rfl) ⟨1591854, by rfl⟩ : syracuseStep 4244945 = 3183709) B3183709
theorem B11319853 : Blo 1933435 11319853 := bstep (se 3 (by rfl) ⟨2122472, by rfl⟩ : syracuseStep 11319853 = 4244945) B4244945
theorem B15093137 : Blo 1933435 15093137 := bstep (se 2 (by rfl) ⟨5659926, by rfl⟩ : syracuseStep 15093137 = 11319853) B11319853
theorem B10062091 : Blo 1933435 10062091 := bstep (se 1 (by rfl) ⟨7546568, by rfl⟩ : syracuseStep 10062091 = 15093137) B15093137
theorem B13416121 : Blo 1933435 13416121 := bstep (se 2 (by rfl) ⟨5031045, by rfl⟩ : syracuseStep 13416121 = 10062091) B10062091
theorem B17888161 : Blo 1933435 17888161 := bstep (se 2 (by rfl) ⟨6708060, by rfl⟩ : syracuseStep 17888161 = 13416121) B13416121
theorem B23850881 : Blo 1933435 23850881 := bstep (se 2 (by rfl) ⟨8944080, by rfl⟩ : syracuseStep 23850881 = 17888161) B17888161
theorem B15900587 : Blo 1933435 15900587 := bstep (se 1 (by rfl) ⟨11925440, by rfl⟩ : syracuseStep 15900587 = 23850881) B23850881
theorem B10600391 : Blo 1933435 10600391 := bstep (se 1 (by rfl) ⟨7950293, by rfl⟩ : syracuseStep 10600391 = 15900587) B15900587
theorem B7066927 : Blo 1933435 7066927 := bstep (se 1 (by rfl) ⟨5300195, by rfl⟩ : syracuseStep 7066927 = 10600391) B10600391
theorem B9422569 : Blo 1933435 9422569 := bstep (se 2 (by rfl) ⟨3533463, by rfl⟩ : syracuseStep 9422569 = 7066927) B7066927
theorem B12563425 : Blo 1933435 12563425 := bstep (se 2 (by rfl) ⟨4711284, by rfl⟩ : syracuseStep 12563425 = 9422569) B9422569
theorem B16751233 : Blo 1933435 16751233 := bstep (se 2 (by rfl) ⟨6281712, by rfl⟩ : syracuseStep 16751233 = 12563425) B12563425
theorem B22334977 : Blo 1933435 22334977 := bstep (se 2 (by rfl) ⟨8375616, by rfl⟩ : syracuseStep 22334977 = 16751233) B16751233
theorem B29779969 : Blo 1933435 29779969 := bstep (se 2 (by rfl) ⟨11167488, by rfl⟩ : syracuseStep 29779969 = 22334977) B22334977
theorem B39706625 : Blo 1933435 39706625 := bstep (se 2 (by rfl) ⟨14889984, by rfl⟩ : syracuseStep 39706625 = 29779969) B29779969
theorem B26471083 : Blo 1933435 26471083 := bstep (se 1 (by rfl) ⟨19853312, by rfl⟩ : syracuseStep 26471083 = 39706625) B39706625
theorem B35294777 : Blo 1933435 35294777 := bstep (se 2 (by rfl) ⟨13235541, by rfl⟩ : syracuseStep 35294777 = 26471083) B26471083
theorem B23529851 : Blo 1933435 23529851 := bstep (se 1 (by rfl) ⟨17647388, by rfl⟩ : syracuseStep 23529851 = 35294777) B35294777
theorem B15686567 : Blo 1933435 15686567 := bstep (se 1 (by rfl) ⟨11764925, by rfl⟩ : syracuseStep 15686567 = 23529851) B23529851
theorem B10457711 : Blo 1933435 10457711 := bstep (se 1 (by rfl) ⟨7843283, by rfl⟩ : syracuseStep 10457711 = 15686567) B15686567
theorem B6971807 : Blo 1933435 6971807 := bstep (se 1 (by rfl) ⟨5228855, by rfl⟩ : syracuseStep 6971807 = 10457711) B10457711
theorem B4647871 : Blo 1933435 4647871 := bstep (se 1 (by rfl) ⟨3485903, by rfl⟩ : syracuseStep 4647871 = 6971807) B6971807
theorem B6197161 : Blo 1933435 6197161 := bstep (se 2 (by rfl) ⟨2323935, by rfl⟩ : syracuseStep 6197161 = 4647871) B4647871
theorem B8262881 : Blo 1933435 8262881 := bstep (se 2 (by rfl) ⟨3098580, by rfl⟩ : syracuseStep 8262881 = 6197161) B6197161
theorem B5508587 : Blo 1933435 5508587 := bstep (se 1 (by rfl) ⟨4131440, by rfl⟩ : syracuseStep 5508587 = 8262881) B8262881
theorem B3672391 : Blo 1933435 3672391 := bstep (se 1 (by rfl) ⟨2754293, by rfl⟩ : syracuseStep 3672391 = 5508587) B5508587
theorem B4896521 : Blo 1933435 4896521 := bstep (se 2 (by rfl) ⟨1836195, by rfl⟩ : syracuseStep 4896521 = 3672391) B3672391
theorem B3264347 : Blo 1933435 3264347 := bstep (se 1 (by rfl) ⟨2448260, by rfl⟩ : syracuseStep 3264347 = 4896521) B4896521
theorem B2176231 : Blo 1933435 2176231 := bstep (se 1 (by rfl) ⟨1632173, by rfl⟩ : syracuseStep 2176231 = 3264347) B3264347
theorem B2901641 : Blo 1933435 2901641 := bstep (se 2 (by rfl) ⟨1088115, by rfl⟩ : syracuseStep 2901641 = 2176231) B2176231
theorem B1934427 : Blo 1933435 1934427 := bstep (se 1 (by rfl) ⟨1450820, by rfl⟩ : syracuseStep 1934427 = 2901641) B2901641
theorem B9793061 : Blo 1933435 9793061 := bbase (se 4 (by rfl) ⟨918099, by rfl⟩ : syracuseStep 9793061 = 1836199) (by norm_num)
theorem B6528707 : Blo 1933435 6528707 := bstep (se 1 (by rfl) ⟨4896530, by rfl⟩ : syracuseStep 6528707 = 9793061) B9793061
theorem B4352471 : Blo 1933435 4352471 := bstep (se 1 (by rfl) ⟨3264353, by rfl⟩ : syracuseStep 4352471 = 6528707) B6528707
theorem B2901647 : Blo 1933435 2901647 := bstep (se 1 (by rfl) ⟨2176235, by rfl⟩ : syracuseStep 2901647 = 4352471) B4352471
theorem B1934431 : Blo 1933435 1934431 := bstep (se 1 (by rfl) ⟨1450823, by rfl⟩ : syracuseStep 1934431 = 2901647) B2901647
theorem B2901653 : Blo 1933435 2901653 := bbase (se 6 (by rfl) ⟨68007, by rfl⟩ : syracuseStep 2901653 = 136015) (by norm_num)
theorem B1934435 : Blo 1933435 1934435 := bstep (se 1 (by rfl) ⟨1450826, by rfl⟩ : syracuseStep 1934435 = 2901653) B2901653
theorem B2205937 : Blo 1933435 2205937 := bbase (se 2 (by rfl) ⟨827226, by rfl⟩ : syracuseStep 2205937 = 1654453) (by norm_num)
theorem B11764997 : Blo 1933435 11764997 := bstep (se 4 (by rfl) ⟨1102968, by rfl⟩ : syracuseStep 11764997 = 2205937) B2205937
theorem B7843331 : Blo 1933435 7843331 := bstep (se 1 (by rfl) ⟨5882498, by rfl⟩ : syracuseStep 7843331 = 11764997) B11764997
theorem B5228887 : Blo 1933435 5228887 := bstep (se 1 (by rfl) ⟨3921665, by rfl⟩ : syracuseStep 5228887 = 7843331) B7843331
theorem B6971849 : Blo 1933435 6971849 := bstep (se 2 (by rfl) ⟨2614443, by rfl⟩ : syracuseStep 6971849 = 5228887) B5228887
theorem B4647899 : Blo 1933435 4647899 := bstep (se 1 (by rfl) ⟨3485924, by rfl⟩ : syracuseStep 4647899 = 6971849) B6971849
theorem B12394397 : Blo 1933435 12394397 := bstep (se 3 (by rfl) ⟨2323949, by rfl⟩ : syracuseStep 12394397 = 4647899) B4647899
theorem B8262931 : Blo 1933435 8262931 := bstep (se 1 (by rfl) ⟨6197198, by rfl⟩ : syracuseStep 8262931 = 12394397) B12394397
theorem B11017241 : Blo 1933435 11017241 := bstep (se 2 (by rfl) ⟨4131465, by rfl⟩ : syracuseStep 11017241 = 8262931) B8262931
theorem B7344827 : Blo 1933435 7344827 := bstep (se 1 (by rfl) ⟨5508620, by rfl⟩ : syracuseStep 7344827 = 11017241) B11017241
theorem B4896551 : Blo 1933435 4896551 := bstep (se 1 (by rfl) ⟨3672413, by rfl⟩ : syracuseStep 4896551 = 7344827) B7344827
theorem B3264367 : Blo 1933435 3264367 := bstep (se 1 (by rfl) ⟨2448275, by rfl⟩ : syracuseStep 3264367 = 4896551) B4896551
theorem B4352489 : Blo 1933435 4352489 := bstep (se 2 (by rfl) ⟨1632183, by rfl⟩ : syracuseStep 4352489 = 3264367) B3264367
theorem B2901659 : Blo 1933435 2901659 := bstep (se 1 (by rfl) ⟨2176244, by rfl⟩ : syracuseStep 2901659 = 4352489) B4352489
theorem B1934439 : Blo 1933435 1934439 := bstep (se 1 (by rfl) ⟨1450829, by rfl⟩ : syracuseStep 1934439 = 2901659) B2901659
theorem B2176249 : Blo 1933435 2176249 := bbase (se 2 (by rfl) ⟨816093, by rfl⟩ : syracuseStep 2176249 = 1632187) (by norm_num)
theorem B2901665 : Blo 1933435 2901665 := bstep (se 2 (by rfl) ⟨1088124, by rfl⟩ : syracuseStep 2901665 = 2176249) B2176249
theorem B1934443 : Blo 1933435 1934443 := bstep (se 1 (by rfl) ⟨1450832, by rfl⟩ : syracuseStep 1934443 = 2901665) B2901665
theorem B8262965 : Blo 1933435 8262965 := bbase (se 5 (by rfl) ⟨387326, by rfl⟩ : syracuseStep 8262965 = 774653) (by norm_num)
theorem B5508643 : Blo 1933435 5508643 := bstep (se 1 (by rfl) ⟨4131482, by rfl⟩ : syracuseStep 5508643 = 8262965) B8262965
theorem B7344857 : Blo 1933435 7344857 := bstep (se 2 (by rfl) ⟨2754321, by rfl⟩ : syracuseStep 7344857 = 5508643) B5508643
theorem B4896571 : Blo 1933435 4896571 := bstep (se 1 (by rfl) ⟨3672428, by rfl⟩ : syracuseStep 4896571 = 7344857) B7344857
theorem B6528761 : Blo 1933435 6528761 := bstep (se 2 (by rfl) ⟨2448285, by rfl⟩ : syracuseStep 6528761 = 4896571) B4896571
theorem B4352507 : Blo 1933435 4352507 := bstep (se 1 (by rfl) ⟨3264380, by rfl⟩ : syracuseStep 4352507 = 6528761) B6528761
theorem B2901671 : Blo 1933435 2901671 := bstep (se 1 (by rfl) ⟨2176253, by rfl⟩ : syracuseStep 2901671 = 4352507) B4352507
theorem B1934447 : Blo 1933435 1934447 := bstep (se 1 (by rfl) ⟨1450835, by rfl⟩ : syracuseStep 1934447 = 2901671) B2901671
theorem B2901677 : Blo 1933435 2901677 := bbase (se 3 (by rfl) ⟨544064, by rfl⟩ : syracuseStep 2901677 = 1088129) (by norm_num)
theorem B1934451 : Blo 1933435 1934451 := bstep (se 1 (by rfl) ⟨1450838, by rfl⟩ : syracuseStep 1934451 = 2901677) B2901677
theorem B4352525 : Blo 1933435 4352525 := bbase (se 3 (by rfl) ⟨816098, by rfl⟩ : syracuseStep 4352525 = 1632197) (by norm_num)
theorem B2901683 : Blo 1933435 2901683 := bstep (se 1 (by rfl) ⟨2176262, by rfl⟩ : syracuseStep 2901683 = 4352525) B4352525
theorem B1934455 : Blo 1933435 1934455 := bstep (se 1 (by rfl) ⟨1450841, by rfl⟩ : syracuseStep 1934455 = 2901683) B2901683
theorem B2448301 : Blo 1933435 2448301 := bbase (se 3 (by rfl) ⟨459056, by rfl⟩ : syracuseStep 2448301 = 918113) (by norm_num)
theorem B3264401 : Blo 1933435 3264401 := bstep (se 2 (by rfl) ⟨1224150, by rfl⟩ : syracuseStep 3264401 = 2448301) B2448301
theorem B2176267 : Blo 1933435 2176267 := bstep (se 1 (by rfl) ⟨1632200, by rfl⟩ : syracuseStep 2176267 = 3264401) B3264401
theorem B2901689 : Blo 1933435 2901689 := bstep (se 2 (by rfl) ⟨1088133, by rfl⟩ : syracuseStep 2901689 = 2176267) B2176267
theorem B1934459 : Blo 1933435 1934459 := bstep (se 1 (by rfl) ⟨1450844, by rfl⟩ : syracuseStep 1934459 = 2901689) B2901689
theorem B12394549 : Blo 1933435 12394549 := bbase (se 5 (by rfl) ⟨580994, by rfl⟩ : syracuseStep 12394549 = 1161989) (by norm_num)
theorem B16526065 : Blo 1933435 16526065 := bstep (se 2 (by rfl) ⟨6197274, by rfl⟩ : syracuseStep 16526065 = 12394549) B12394549
theorem B22034753 : Blo 1933435 22034753 := bstep (se 2 (by rfl) ⟨8263032, by rfl⟩ : syracuseStep 22034753 = 16526065) B16526065
theorem B14689835 : Blo 1933435 14689835 := bstep (se 1 (by rfl) ⟨11017376, by rfl⟩ : syracuseStep 14689835 = 22034753) B22034753
theorem B9793223 : Blo 1933435 9793223 := bstep (se 1 (by rfl) ⟨7344917, by rfl⟩ : syracuseStep 9793223 = 14689835) B14689835
theorem B6528815 : Blo 1933435 6528815 := bstep (se 1 (by rfl) ⟨4896611, by rfl⟩ : syracuseStep 6528815 = 9793223) B9793223
theorem B4352543 : Blo 1933435 4352543 := bstep (se 1 (by rfl) ⟨3264407, by rfl⟩ : syracuseStep 4352543 = 6528815) B6528815
theorem B2901695 : Blo 1933435 2901695 := bstep (se 1 (by rfl) ⟨2176271, by rfl⟩ : syracuseStep 2901695 = 4352543) B4352543
theorem B1934463 : Blo 1933435 1934463 := bstep (se 1 (by rfl) ⟨1450847, by rfl⟩ : syracuseStep 1934463 = 2901695) B2901695
theorem B2901701 : Blo 1933435 2901701 := bbase (se 4 (by rfl) ⟨272034, by rfl⟩ : syracuseStep 2901701 = 544069) (by norm_num)
theorem B1934467 : Blo 1933435 1934467 := bstep (se 1 (by rfl) ⟨1450850, by rfl⟩ : syracuseStep 1934467 = 2901701) B2901701
theorem B3264421 : Blo 1933435 3264421 := bbase (se 4 (by rfl) ⟨306039, by rfl⟩ : syracuseStep 3264421 = 612079) (by norm_num)
theorem B4352561 : Blo 1933435 4352561 := bstep (se 2 (by rfl) ⟨1632210, by rfl⟩ : syracuseStep 4352561 = 3264421) B3264421
theorem B2901707 : Blo 1933435 2901707 := bstep (se 1 (by rfl) ⟨2176280, by rfl⟩ : syracuseStep 2901707 = 4352561) B4352561
theorem B1934471 : Blo 1933435 1934471 := bstep (se 1 (by rfl) ⟨1450853, by rfl⟩ : syracuseStep 1934471 = 2901707) B2901707
theorem B2176285 : Blo 1933435 2176285 := bbase (se 3 (by rfl) ⟨408053, by rfl⟩ : syracuseStep 2176285 = 816107) (by norm_num)
theorem B2901713 : Blo 1933435 2901713 := bstep (se 2 (by rfl) ⟨1088142, by rfl⟩ : syracuseStep 2901713 = 2176285) B2176285
theorem B1934475 : Blo 1933435 1934475 := bstep (se 1 (by rfl) ⟨1450856, by rfl⟩ : syracuseStep 1934475 = 2901713) B2901713
theorem B6528869 : Blo 1933435 6528869 := bbase (se 4 (by rfl) ⟨612081, by rfl⟩ : syracuseStep 6528869 = 1224163) (by norm_num)
theorem B4352579 : Blo 1933435 4352579 := bstep (se 1 (by rfl) ⟨3264434, by rfl⟩ : syracuseStep 4352579 = 6528869) B6528869
theorem B2901719 : Blo 1933435 2901719 := bstep (se 1 (by rfl) ⟨2176289, by rfl⟩ : syracuseStep 2901719 = 4352579) B4352579
theorem B1934479 : Blo 1933435 1934479 := bstep (se 1 (by rfl) ⟨1450859, by rfl⟩ : syracuseStep 1934479 = 2901719) B2901719
theorem B2901725 : Blo 1933435 2901725 := bbase (se 3 (by rfl) ⟨544073, by rfl⟩ : syracuseStep 2901725 = 1088147) (by norm_num)
theorem B1934483 : Blo 1933435 1934483 := bstep (se 1 (by rfl) ⟨1450862, by rfl⟩ : syracuseStep 1934483 = 2901725) B2901725
theorem B4352597 : Blo 1933435 4352597 := bbase (se 8 (by rfl) ⟨25503, by rfl⟩ : syracuseStep 4352597 = 51007) (by norm_num)
theorem B2901731 : Blo 1933435 2901731 := bstep (se 1 (by rfl) ⟨2176298, by rfl⟩ : syracuseStep 2901731 = 4352597) B4352597
theorem B1934487 : Blo 1933435 1934487 := bstep (se 1 (by rfl) ⟨1450865, by rfl⟩ : syracuseStep 1934487 = 2901731) B2901731
theorem B5229029 : Blo 1933435 5229029 := bbase (se 4 (by rfl) ⟨490221, by rfl⟩ : syracuseStep 5229029 = 980443) (by norm_num)
theorem B3486019 : Blo 1933435 3486019 := bstep (se 1 (by rfl) ⟨2614514, by rfl⟩ : syracuseStep 3486019 = 5229029) B5229029
theorem B4648025 : Blo 1933435 4648025 := bstep (se 2 (by rfl) ⟨1743009, by rfl⟩ : syracuseStep 4648025 = 3486019) B3486019
theorem B3098683 : Blo 1933435 3098683 := bstep (se 1 (by rfl) ⟨2324012, by rfl⟩ : syracuseStep 3098683 = 4648025) B4648025
theorem B4131577 : Blo 1933435 4131577 := bstep (se 2 (by rfl) ⟨1549341, by rfl⟩ : syracuseStep 4131577 = 3098683) B3098683
theorem B5508769 : Blo 1933435 5508769 := bstep (se 2 (by rfl) ⟨2065788, by rfl⟩ : syracuseStep 5508769 = 4131577) B4131577
theorem B7345025 : Blo 1933435 7345025 := bstep (se 2 (by rfl) ⟨2754384, by rfl⟩ : syracuseStep 7345025 = 5508769) B5508769
theorem B4896683 : Blo 1933435 4896683 := bstep (se 1 (by rfl) ⟨3672512, by rfl⟩ : syracuseStep 4896683 = 7345025) B7345025
theorem B3264455 : Blo 1933435 3264455 := bstep (se 1 (by rfl) ⟨2448341, by rfl⟩ : syracuseStep 3264455 = 4896683) B4896683
theorem B2176303 : Blo 1933435 2176303 := bstep (se 1 (by rfl) ⟨1632227, by rfl⟩ : syracuseStep 2176303 = 3264455) B3264455
theorem B2901737 : Blo 1933435 2901737 := bstep (se 2 (by rfl) ⟨1088151, by rfl⟩ : syracuseStep 2901737 = 2176303) B2176303
theorem B1934491 : Blo 1933435 1934491 := bstep (se 1 (by rfl) ⟨1450868, by rfl⟩ : syracuseStep 1934491 = 2901737) B2901737
theorem B2206001 : Blo 1933435 2206001 := bbase (se 2 (by rfl) ⟨827250, by rfl⟩ : syracuseStep 2206001 = 1654501) (by norm_num)
theorem B5882669 : Blo 1933435 5882669 := bstep (se 3 (by rfl) ⟨1103000, by rfl⟩ : syracuseStep 5882669 = 2206001) B2206001
theorem B3921779 : Blo 1933435 3921779 := bstep (se 1 (by rfl) ⟨2941334, by rfl⟩ : syracuseStep 3921779 = 5882669) B5882669
theorem B2614519 : Blo 1933435 2614519 := bstep (se 1 (by rfl) ⟨1960889, by rfl⟩ : syracuseStep 2614519 = 3921779) B3921779
theorem B3486025 : Blo 1933435 3486025 := bstep (se 2 (by rfl) ⟨1307259, by rfl⟩ : syracuseStep 3486025 = 2614519) B2614519
theorem B4648033 : Blo 1933435 4648033 := bstep (se 2 (by rfl) ⟨1743012, by rfl⟩ : syracuseStep 4648033 = 3486025) B3486025
theorem B24789509 : Blo 1933435 24789509 := bstep (se 4 (by rfl) ⟨2324016, by rfl⟩ : syracuseStep 24789509 = 4648033) B4648033
theorem B16526339 : Blo 1933435 16526339 := bstep (se 1 (by rfl) ⟨12394754, by rfl⟩ : syracuseStep 16526339 = 24789509) B24789509
theorem B11017559 : Blo 1933435 11017559 := bstep (se 1 (by rfl) ⟨8263169, by rfl⟩ : syracuseStep 11017559 = 16526339) B16526339
theorem B7345039 : Blo 1933435 7345039 := bstep (se 1 (by rfl) ⟨5508779, by rfl⟩ : syracuseStep 7345039 = 11017559) B11017559
theorem B9793385 : Blo 1933435 9793385 := bstep (se 2 (by rfl) ⟨3672519, by rfl⟩ : syracuseStep 9793385 = 7345039) B7345039
theorem B6528923 : Blo 1933435 6528923 := bstep (se 1 (by rfl) ⟨4896692, by rfl⟩ : syracuseStep 6528923 = 9793385) B9793385
theorem B4352615 : Blo 1933435 4352615 := bstep (se 1 (by rfl) ⟨3264461, by rfl⟩ : syracuseStep 4352615 = 6528923) B6528923
theorem B2901743 : Blo 1933435 2901743 := bstep (se 1 (by rfl) ⟨2176307, by rfl⟩ : syracuseStep 2901743 = 4352615) B4352615
theorem B1934495 : Blo 1933435 1934495 := bstep (se 1 (by rfl) ⟨1450871, by rfl⟩ : syracuseStep 1934495 = 2901743) B2901743
theorem B2901749 : Blo 1933435 2901749 := bbase (se 5 (by rfl) ⟨136019, by rfl⟩ : syracuseStep 2901749 = 272039) (by norm_num)
theorem B1934499 : Blo 1933435 1934499 := bstep (se 1 (by rfl) ⟨1450874, by rfl⟩ : syracuseStep 1934499 = 2901749) B2901749
theorem B8263205 : Blo 1933435 8263205 := bbase (se 4 (by rfl) ⟨774675, by rfl⟩ : syracuseStep 8263205 = 1549351) (by norm_num)
theorem B5508803 : Blo 1933435 5508803 := bstep (se 1 (by rfl) ⟨4131602, by rfl⟩ : syracuseStep 5508803 = 8263205) B8263205
theorem B3672535 : Blo 1933435 3672535 := bstep (se 1 (by rfl) ⟨2754401, by rfl⟩ : syracuseStep 3672535 = 5508803) B5508803
theorem B4896713 : Blo 1933435 4896713 := bstep (se 2 (by rfl) ⟨1836267, by rfl⟩ : syracuseStep 4896713 = 3672535) B3672535
theorem B3264475 : Blo 1933435 3264475 := bstep (se 1 (by rfl) ⟨2448356, by rfl⟩ : syracuseStep 3264475 = 4896713) B4896713
theorem B4352633 : Blo 1933435 4352633 := bstep (se 2 (by rfl) ⟨1632237, by rfl⟩ : syracuseStep 4352633 = 3264475) B3264475
theorem B2901755 : Blo 1933435 2901755 := bstep (se 1 (by rfl) ⟨2176316, by rfl⟩ : syracuseStep 2901755 = 4352633) B4352633
theorem B1934503 : Blo 1933435 1934503 := bstep (se 1 (by rfl) ⟨1450877, by rfl⟩ : syracuseStep 1934503 = 2901755) B2901755
theorem B2176321 : Blo 1933435 2176321 := bbase (se 2 (by rfl) ⟨816120, by rfl⟩ : syracuseStep 2176321 = 1632241) (by norm_num)
theorem B2901761 : Blo 1933435 2901761 := bstep (se 2 (by rfl) ⟨1088160, by rfl⟩ : syracuseStep 2901761 = 2176321) B2176321
theorem B1934507 : Blo 1933435 1934507 := bstep (se 1 (by rfl) ⟨1450880, by rfl⟩ : syracuseStep 1934507 = 2901761) B2901761
theorem B4896733 : Blo 1933435 4896733 := bbase (se 3 (by rfl) ⟨918137, by rfl⟩ : syracuseStep 4896733 = 1836275) (by norm_num)
theorem B6528977 : Blo 1933435 6528977 := bstep (se 2 (by rfl) ⟨2448366, by rfl⟩ : syracuseStep 6528977 = 4896733) B4896733
theorem B4352651 : Blo 1933435 4352651 := bstep (se 1 (by rfl) ⟨3264488, by rfl⟩ : syracuseStep 4352651 = 6528977) B6528977
theorem B2901767 : Blo 1933435 2901767 := bstep (se 1 (by rfl) ⟨2176325, by rfl⟩ : syracuseStep 2901767 = 4352651) B4352651
theorem B1934511 : Blo 1933435 1934511 := bstep (se 1 (by rfl) ⟨1450883, by rfl⟩ : syracuseStep 1934511 = 2901767) B2901767
theorem B2901773 : Blo 1933435 2901773 := bbase (se 3 (by rfl) ⟨544082, by rfl⟩ : syracuseStep 2901773 = 1088165) (by norm_num)
theorem B1934515 : Blo 1933435 1934515 := bstep (se 1 (by rfl) ⟨1450886, by rfl⟩ : syracuseStep 1934515 = 2901773) B2901773
theorem B4352669 : Blo 1933435 4352669 := bbase (se 3 (by rfl) ⟨816125, by rfl⟩ : syracuseStep 4352669 = 1632251) (by norm_num)
theorem B2901779 : Blo 1933435 2901779 := bstep (se 1 (by rfl) ⟨2176334, by rfl⟩ : syracuseStep 2901779 = 4352669) B4352669
theorem B1934519 : Blo 1933435 1934519 := bstep (se 1 (by rfl) ⟨1450889, by rfl⟩ : syracuseStep 1934519 = 2901779) B2901779
theorem B3264509 : Blo 1933435 3264509 := bbase (se 3 (by rfl) ⟨612095, by rfl⟩ : syracuseStep 3264509 = 1224191) (by norm_num)
theorem B2176339 : Blo 1933435 2176339 := bstep (se 1 (by rfl) ⟨1632254, by rfl⟩ : syracuseStep 2176339 = 3264509) B3264509
theorem B2901785 : Blo 1933435 2901785 := bstep (se 2 (by rfl) ⟨1088169, by rfl⟩ : syracuseStep 2901785 = 2176339) B2176339
theorem B1934523 : Blo 1933435 1934523 := bstep (se 1 (by rfl) ⟨1450892, by rfl⟩ : syracuseStep 1934523 = 2901785) B2901785
theorem B4131653 : Blo 1933435 4131653 := bbase (se 4 (by rfl) ⟨387342, by rfl⟩ : syracuseStep 4131653 = 774685) (by norm_num)
theorem B11017741 : Blo 1933435 11017741 := bstep (se 3 (by rfl) ⟨2065826, by rfl⟩ : syracuseStep 11017741 = 4131653) B4131653
theorem B14690321 : Blo 1933435 14690321 := bstep (se 2 (by rfl) ⟨5508870, by rfl⟩ : syracuseStep 14690321 = 11017741) B11017741
theorem B9793547 : Blo 1933435 9793547 := bstep (se 1 (by rfl) ⟨7345160, by rfl⟩ : syracuseStep 9793547 = 14690321) B14690321
theorem B6529031 : Blo 1933435 6529031 := bstep (se 1 (by rfl) ⟨4896773, by rfl⟩ : syracuseStep 6529031 = 9793547) B9793547
theorem B4352687 : Blo 1933435 4352687 := bstep (se 1 (by rfl) ⟨3264515, by rfl⟩ : syracuseStep 4352687 = 6529031) B6529031
theorem B2901791 : Blo 1933435 2901791 := bstep (se 1 (by rfl) ⟨2176343, by rfl⟩ : syracuseStep 2901791 = 4352687) B4352687
theorem B1934527 : Blo 1933435 1934527 := bstep (se 1 (by rfl) ⟨1450895, by rfl⟩ : syracuseStep 1934527 = 2901791) B2901791
theorem B2901797 : Blo 1933435 2901797 := bbase (se 4 (by rfl) ⟨272043, by rfl⟩ : syracuseStep 2901797 = 544087) (by norm_num)
theorem B1934531 : Blo 1933435 1934531 := bstep (se 1 (by rfl) ⟨1450898, by rfl⟩ : syracuseStep 1934531 = 2901797) B2901797
theorem B2448397 : Blo 1933435 2448397 := bbase (se 3 (by rfl) ⟨459074, by rfl⟩ : syracuseStep 2448397 = 918149) (by norm_num)
theorem B3264529 : Blo 1933435 3264529 := bstep (se 2 (by rfl) ⟨1224198, by rfl⟩ : syracuseStep 3264529 = 2448397) B2448397
theorem B4352705 : Blo 1933435 4352705 := bstep (se 2 (by rfl) ⟨1632264, by rfl⟩ : syracuseStep 4352705 = 3264529) B3264529
theorem B2901803 : Blo 1933435 2901803 := bstep (se 1 (by rfl) ⟨2176352, by rfl⟩ : syracuseStep 2901803 = 4352705) B4352705
theorem B1934535 : Blo 1933435 1934535 := bstep (se 1 (by rfl) ⟨1450901, by rfl⟩ : syracuseStep 1934535 = 2901803) B2901803
theorem B2176357 : Blo 1933435 2176357 := bbase (se 4 (by rfl) ⟨204033, by rfl⟩ : syracuseStep 2176357 = 408067) (by norm_num)
theorem B2901809 : Blo 1933435 2901809 := bstep (se 2 (by rfl) ⟨1088178, by rfl⟩ : syracuseStep 2901809 = 2176357) B2176357
theorem B1934539 : Blo 1933435 1934539 := bstep (se 1 (by rfl) ⟨1450904, by rfl⟩ : syracuseStep 1934539 = 2901809) B2901809
theorem B5508917 : Blo 1933435 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B3672611 : Blo 1933435 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B2448407 : Blo 1933435 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B6529085 : Blo 1933435 6529085 := bstep (se 3 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 6529085 = 2448407) B2448407
theorem B4352723 : Blo 1933435 4352723 := bstep (se 1 (by rfl) ⟨3264542, by rfl⟩ : syracuseStep 4352723 = 6529085) B6529085
theorem B2901815 : Blo 1933435 2901815 := bstep (se 1 (by rfl) ⟨2176361, by rfl⟩ : syracuseStep 2901815 = 4352723) B4352723
theorem B1934543 : Blo 1933435 1934543 := bstep (se 1 (by rfl) ⟨1450907, by rfl⟩ : syracuseStep 1934543 = 2901815) B2901815
theorem B2901821 : Blo 1933435 2901821 := bbase (se 3 (by rfl) ⟨544091, by rfl⟩ : syracuseStep 2901821 = 1088183) (by norm_num)
theorem B1934547 : Blo 1933435 1934547 := bstep (se 1 (by rfl) ⟨1450910, by rfl⟩ : syracuseStep 1934547 = 2901821) B2901821
theorem B4352741 : Blo 1933435 4352741 := bbase (se 4 (by rfl) ⟨408069, by rfl⟩ : syracuseStep 4352741 = 816139) (by norm_num)
theorem B2901827 : Blo 1933435 2901827 := bstep (se 1 (by rfl) ⟨2176370, by rfl⟩ : syracuseStep 2901827 = 4352741) B4352741
theorem B1934551 : Blo 1933435 1934551 := bstep (se 1 (by rfl) ⟨1450913, by rfl⟩ : syracuseStep 1934551 = 2901827) B2901827
theorem B4896845 : Blo 1933435 4896845 := bbase (se 3 (by rfl) ⟨918158, by rfl⟩ : syracuseStep 4896845 = 1836317) (by norm_num)
theorem B3264563 : Blo 1933435 3264563 := bstep (se 1 (by rfl) ⟨2448422, by rfl⟩ : syracuseStep 3264563 = 4896845) B4896845
theorem B2176375 : Blo 1933435 2176375 := bstep (se 1 (by rfl) ⟨1632281, by rfl⟩ : syracuseStep 2176375 = 3264563) B3264563
theorem B2901833 : Blo 1933435 2901833 := bstep (se 2 (by rfl) ⟨1088187, by rfl⟩ : syracuseStep 2901833 = 2176375) B2176375
theorem B1934555 : Blo 1933435 1934555 := bstep (se 1 (by rfl) ⟨1450916, by rfl⟩ : syracuseStep 1934555 = 2901833) B2901833
theorem B2065861 : Blo 1933435 2065861 := bbase (se 4 (by rfl) ⟨193674, by rfl⟩ : syracuseStep 2065861 = 387349) (by norm_num)
theorem B2754481 : Blo 1933435 2754481 := bstep (se 2 (by rfl) ⟨1032930, by rfl⟩ : syracuseStep 2754481 = 2065861) B2065861
theorem B3672641 : Blo 1933435 3672641 := bstep (se 2 (by rfl) ⟨1377240, by rfl⟩ : syracuseStep 3672641 = 2754481) B2754481
theorem B9793709 : Blo 1933435 9793709 := bstep (se 3 (by rfl) ⟨1836320, by rfl⟩ : syracuseStep 9793709 = 3672641) B3672641
theorem B6529139 : Blo 1933435 6529139 := bstep (se 1 (by rfl) ⟨4896854, by rfl⟩ : syracuseStep 6529139 = 9793709) B9793709
theorem B4352759 : Blo 1933435 4352759 := bstep (se 1 (by rfl) ⟨3264569, by rfl⟩ : syracuseStep 4352759 = 6529139) B6529139
theorem B2901839 : Blo 1933435 2901839 := bstep (se 1 (by rfl) ⟨2176379, by rfl⟩ : syracuseStep 2901839 = 4352759) B4352759
theorem B1934559 : Blo 1933435 1934559 := bstep (se 1 (by rfl) ⟨1450919, by rfl⟩ : syracuseStep 1934559 = 2901839) B2901839
theorem B2901845 : Blo 1933435 2901845 := bbase (se 9 (by rfl) ⟨8501, by rfl⟩ : syracuseStep 2901845 = 17003) (by norm_num)
theorem B1934563 : Blo 1933435 1934563 := bstep (se 1 (by rfl) ⟨1450922, by rfl⟩ : syracuseStep 1934563 = 2901845) B2901845
theorem B15687701 : Blo 1933435 15687701 := bbase (se 6 (by rfl) ⟨367680, by rfl⟩ : syracuseStep 15687701 = 735361) (by norm_num)
theorem B10458467 : Blo 1933435 10458467 := bstep (se 1 (by rfl) ⟨7843850, by rfl⟩ : syracuseStep 10458467 = 15687701) B15687701
theorem B6972311 : Blo 1933435 6972311 := bstep (se 1 (by rfl) ⟨5229233, by rfl⟩ : syracuseStep 6972311 = 10458467) B10458467
theorem B4648207 : Blo 1933435 4648207 := bstep (se 1 (by rfl) ⟨3486155, by rfl⟩ : syracuseStep 4648207 = 6972311) B6972311
theorem B6197609 : Blo 1933435 6197609 := bstep (se 2 (by rfl) ⟨2324103, by rfl⟩ : syracuseStep 6197609 = 4648207) B4648207
theorem B4131739 : Blo 1933435 4131739 := bstep (se 1 (by rfl) ⟨3098804, by rfl⟩ : syracuseStep 4131739 = 6197609) B6197609
theorem B5508985 : Blo 1933435 5508985 := bstep (se 2 (by rfl) ⟨2065869, by rfl⟩ : syracuseStep 5508985 = 4131739) B4131739
theorem B7345313 : Blo 1933435 7345313 := bstep (se 2 (by rfl) ⟨2754492, by rfl⟩ : syracuseStep 7345313 = 5508985) B5508985
theorem B4896875 : Blo 1933435 4896875 := bstep (se 1 (by rfl) ⟨3672656, by rfl⟩ : syracuseStep 4896875 = 7345313) B7345313
theorem B3264583 : Blo 1933435 3264583 := bstep (se 1 (by rfl) ⟨2448437, by rfl⟩ : syracuseStep 3264583 = 4896875) B4896875
theorem B4352777 : Blo 1933435 4352777 := bstep (se 2 (by rfl) ⟨1632291, by rfl⟩ : syracuseStep 4352777 = 3264583) B3264583
theorem B2901851 : Blo 1933435 2901851 := bstep (se 1 (by rfl) ⟨2176388, by rfl⟩ : syracuseStep 2901851 = 4352777) B4352777
theorem B1934567 : Blo 1933435 1934567 := bstep (se 1 (by rfl) ⟨1450925, by rfl⟩ : syracuseStep 1934567 = 2901851) B2901851
theorem B2176393 : Blo 1933435 2176393 := bbase (se 2 (by rfl) ⟨816147, by rfl⟩ : syracuseStep 2176393 = 1632295) (by norm_num)
theorem B2901857 : Blo 1933435 2901857 := bstep (se 2 (by rfl) ⟨1088196, by rfl⟩ : syracuseStep 2901857 = 2176393) B2176393
theorem B1934571 : Blo 1933435 1934571 := bstep (se 1 (by rfl) ⟨1450928, by rfl⟩ : syracuseStep 1934571 = 2901857) B2901857
theorem B9927413 : Blo 1933435 9927413 := bbase (se 5 (by rfl) ⟨465347, by rfl⟩ : syracuseStep 9927413 = 930695) (by norm_num)
theorem B6618275 : Blo 1933435 6618275 := bstep (se 1 (by rfl) ⟨4963706, by rfl⟩ : syracuseStep 6618275 = 9927413) B9927413
theorem B4412183 : Blo 1933435 4412183 := bstep (se 1 (by rfl) ⟨3309137, by rfl⟩ : syracuseStep 4412183 = 6618275) B6618275
theorem B11765821 : Blo 1933435 11765821 := bstep (se 3 (by rfl) ⟨2206091, by rfl⟩ : syracuseStep 11765821 = 4412183) B4412183
theorem B15687761 : Blo 1933435 15687761 := bstep (se 2 (by rfl) ⟨5882910, by rfl⟩ : syracuseStep 15687761 = 11765821) B11765821
theorem B41834029 : Blo 1933435 41834029 := bstep (se 3 (by rfl) ⟨7843880, by rfl⟩ : syracuseStep 41834029 = 15687761) B15687761
theorem B55778705 : Blo 1933435 55778705 := bstep (se 2 (by rfl) ⟨20917014, by rfl⟩ : syracuseStep 55778705 = 41834029) B41834029
theorem B37185803 : Blo 1933435 37185803 := bstep (se 1 (by rfl) ⟨27889352, by rfl⟩ : syracuseStep 37185803 = 55778705) B55778705
theorem B24790535 : Blo 1933435 24790535 := bstep (se 1 (by rfl) ⟨18592901, by rfl⟩ : syracuseStep 24790535 = 37185803) B37185803
theorem B16527023 : Blo 1933435 16527023 := bstep (se 1 (by rfl) ⟨12395267, by rfl⟩ : syracuseStep 16527023 = 24790535) B24790535
theorem B11018015 : Blo 1933435 11018015 := bstep (se 1 (by rfl) ⟨8263511, by rfl⟩ : syracuseStep 11018015 = 16527023) B16527023
theorem B7345343 : Blo 1933435 7345343 := bstep (se 1 (by rfl) ⟨5509007, by rfl⟩ : syracuseStep 7345343 = 11018015) B11018015
theorem B4896895 : Blo 1933435 4896895 := bstep (se 1 (by rfl) ⟨3672671, by rfl⟩ : syracuseStep 4896895 = 7345343) B7345343
theorem B6529193 : Blo 1933435 6529193 := bstep (se 2 (by rfl) ⟨2448447, by rfl⟩ : syracuseStep 6529193 = 4896895) B4896895
theorem B4352795 : Blo 1933435 4352795 := bstep (se 1 (by rfl) ⟨3264596, by rfl⟩ : syracuseStep 4352795 = 6529193) B6529193
theorem B2901863 : Blo 1933435 2901863 := bstep (se 1 (by rfl) ⟨2176397, by rfl⟩ : syracuseStep 2901863 = 4352795) B4352795
theorem B1934575 : Blo 1933435 1934575 := bstep (se 1 (by rfl) ⟨1450931, by rfl⟩ : syracuseStep 1934575 = 2901863) B2901863
theorem B2901869 : Blo 1933435 2901869 := bbase (se 3 (by rfl) ⟨544100, by rfl⟩ : syracuseStep 2901869 = 1088201) (by norm_num)
theorem B1934579 : Blo 1933435 1934579 := bstep (se 1 (by rfl) ⟨1450934, by rfl⟩ : syracuseStep 1934579 = 2901869) B2901869
theorem B4352813 : Blo 1933435 4352813 := bbase (se 3 (by rfl) ⟨816152, by rfl⟩ : syracuseStep 4352813 = 1632305) (by norm_num)
theorem B2901875 : Blo 1933435 2901875 := bstep (se 1 (by rfl) ⟨2176406, by rfl⟩ : syracuseStep 2901875 = 4352813) B4352813
theorem B1934583 : Blo 1933435 1934583 := bstep (se 1 (by rfl) ⟨1450937, by rfl⟩ : syracuseStep 1934583 = 2901875) B2901875
theorem B3098837 : Blo 1933435 3098837 := bbase (se 7 (by rfl) ⟨36314, by rfl⟩ : syracuseStep 3098837 = 72629) (by norm_num)
theorem B8263565 : Blo 1933435 8263565 := bstep (se 3 (by rfl) ⟨1549418, by rfl⟩ : syracuseStep 8263565 = 3098837) B3098837
theorem B5509043 : Blo 1933435 5509043 := bstep (se 1 (by rfl) ⟨4131782, by rfl⟩ : syracuseStep 5509043 = 8263565) B8263565
theorem B3672695 : Blo 1933435 3672695 := bstep (se 1 (by rfl) ⟨2754521, by rfl⟩ : syracuseStep 3672695 = 5509043) B5509043
theorem B2448463 : Blo 1933435 2448463 := bstep (se 1 (by rfl) ⟨1836347, by rfl⟩ : syracuseStep 2448463 = 3672695) B3672695
theorem B3264617 : Blo 1933435 3264617 := bstep (se 2 (by rfl) ⟨1224231, by rfl⟩ : syracuseStep 3264617 = 2448463) B2448463
theorem B2176411 : Blo 1933435 2176411 := bstep (se 1 (by rfl) ⟨1632308, by rfl⟩ : syracuseStep 2176411 = 3264617) B3264617
theorem B2901881 : Blo 1933435 2901881 := bstep (se 2 (by rfl) ⟨1088205, by rfl⟩ : syracuseStep 2901881 = 2176411) B2176411
theorem B1934587 : Blo 1933435 1934587 := bstep (se 1 (by rfl) ⟨1450940, by rfl⟩ : syracuseStep 1934587 = 2901881) B2901881
theorem B7445621 : Blo 1933435 7445621 := bbase (se 5 (by rfl) ⟨349013, by rfl⟩ : syracuseStep 7445621 = 698027) (by norm_num)
theorem B19854989 : Blo 1933435 19854989 := bstep (se 3 (by rfl) ⟨3722810, by rfl⟩ : syracuseStep 19854989 = 7445621) B7445621
theorem B13236659 : Blo 1933435 13236659 := bstep (se 1 (by rfl) ⟨9927494, by rfl⟩ : syracuseStep 13236659 = 19854989) B19854989
theorem B8824439 : Blo 1933435 8824439 := bstep (se 1 (by rfl) ⟨6618329, by rfl⟩ : syracuseStep 8824439 = 13236659) B13236659
theorem B5882959 : Blo 1933435 5882959 := bstep (se 1 (by rfl) ⟨4412219, by rfl⟩ : syracuseStep 5882959 = 8824439) B8824439
theorem B31375781 : Blo 1933435 31375781 := bstep (se 4 (by rfl) ⟨2941479, by rfl⟩ : syracuseStep 31375781 = 5882959) B5882959
theorem B20917187 : Blo 1933435 20917187 := bstep (se 1 (by rfl) ⟨15687890, by rfl⟩ : syracuseStep 20917187 = 31375781) B31375781
theorem B13944791 : Blo 1933435 13944791 := bstep (se 1 (by rfl) ⟨10458593, by rfl⟩ : syracuseStep 13944791 = 20917187) B20917187
theorem B9296527 : Blo 1933435 9296527 := bstep (se 1 (by rfl) ⟨6972395, by rfl⟩ : syracuseStep 9296527 = 13944791) B13944791
theorem B12395369 : Blo 1933435 12395369 := bstep (se 2 (by rfl) ⟨4648263, by rfl⟩ : syracuseStep 12395369 = 9296527) B9296527
theorem B33054317 : Blo 1933435 33054317 := bstep (se 3 (by rfl) ⟨6197684, by rfl⟩ : syracuseStep 33054317 = 12395369) B12395369
theorem B22036211 : Blo 1933435 22036211 := bstep (se 1 (by rfl) ⟨16527158, by rfl⟩ : syracuseStep 22036211 = 33054317) B33054317
theorem B14690807 : Blo 1933435 14690807 := bstep (se 1 (by rfl) ⟨11018105, by rfl⟩ : syracuseStep 14690807 = 22036211) B22036211
theorem B9793871 : Blo 1933435 9793871 := bstep (se 1 (by rfl) ⟨7345403, by rfl⟩ : syracuseStep 9793871 = 14690807) B14690807
theorem B6529247 : Blo 1933435 6529247 := bstep (se 1 (by rfl) ⟨4896935, by rfl⟩ : syracuseStep 6529247 = 9793871) B9793871
theorem B4352831 : Blo 1933435 4352831 := bstep (se 1 (by rfl) ⟨3264623, by rfl⟩ : syracuseStep 4352831 = 6529247) B6529247
theorem B2901887 : Blo 1933435 2901887 := bstep (se 1 (by rfl) ⟨2176415, by rfl⟩ : syracuseStep 2901887 = 4352831) B4352831
theorem B1934591 : Blo 1933435 1934591 := bstep (se 1 (by rfl) ⟨1450943, by rfl⟩ : syracuseStep 1934591 = 2901887) B2901887
theorem B2901893 : Blo 1933435 2901893 := bbase (se 4 (by rfl) ⟨272052, by rfl⟩ : syracuseStep 2901893 = 544105) (by norm_num)
theorem B1934595 : Blo 1933435 1934595 := bstep (se 1 (by rfl) ⟨1450946, by rfl⟩ : syracuseStep 1934595 = 2901893) B2901893
theorem B3264637 : Blo 1933435 3264637 := bbase (se 3 (by rfl) ⟨612119, by rfl⟩ : syracuseStep 3264637 = 1224239) (by norm_num)
theorem B4352849 : Blo 1933435 4352849 := bstep (se 2 (by rfl) ⟨1632318, by rfl⟩ : syracuseStep 4352849 = 3264637) B3264637
theorem B2901899 : Blo 1933435 2901899 := bstep (se 1 (by rfl) ⟨2176424, by rfl⟩ : syracuseStep 2901899 = 4352849) B4352849
theorem B1934599 : Blo 1933435 1934599 := bstep (se 1 (by rfl) ⟨1450949, by rfl⟩ : syracuseStep 1934599 = 2901899) B2901899
theorem B2176429 : Blo 1933435 2176429 := bbase (se 3 (by rfl) ⟨408080, by rfl⟩ : syracuseStep 2176429 = 816161) (by norm_num)
theorem B2901905 : Blo 1933435 2901905 := bstep (se 2 (by rfl) ⟨1088214, by rfl⟩ : syracuseStep 2901905 = 2176429) B2176429
theorem B1934603 : Blo 1933435 1934603 := bstep (se 1 (by rfl) ⟨1450952, by rfl⟩ : syracuseStep 1934603 = 2901905) B2901905
theorem B6529301 : Blo 1933435 6529301 := bbase (se 6 (by rfl) ⟨153030, by rfl⟩ : syracuseStep 6529301 = 306061) (by norm_num)
theorem B4352867 : Blo 1933435 4352867 := bstep (se 1 (by rfl) ⟨3264650, by rfl⟩ : syracuseStep 4352867 = 6529301) B6529301
theorem B2901911 : Blo 1933435 2901911 := bstep (se 1 (by rfl) ⟨2176433, by rfl⟩ : syracuseStep 2901911 = 4352867) B4352867
theorem B1934607 : Blo 1933435 1934607 := bstep (se 1 (by rfl) ⟨1450955, by rfl⟩ : syracuseStep 1934607 = 2901911) B2901911
theorem B2901917 : Blo 1933435 2901917 := bbase (se 3 (by rfl) ⟨544109, by rfl⟩ : syracuseStep 2901917 = 1088219) (by norm_num)
theorem B1934611 : Blo 1933435 1934611 := bstep (se 1 (by rfl) ⟨1450958, by rfl⟩ : syracuseStep 1934611 = 2901917) B2901917
theorem B4352885 : Blo 1933435 4352885 := bbase (se 5 (by rfl) ⟨204041, by rfl⟩ : syracuseStep 4352885 = 408083) (by norm_num)
theorem B2901923 : Blo 1933435 2901923 := bstep (se 1 (by rfl) ⟨2176442, by rfl⟩ : syracuseStep 2901923 = 4352885) B4352885
theorem B1934615 : Blo 1933435 1934615 := bstep (se 1 (by rfl) ⟨1450961, by rfl⟩ : syracuseStep 1934615 = 2901923) B2901923
theorem B22641941 : Blo 1933435 22641941 := bbase (se 6 (by rfl) ⟨530670, by rfl⟩ : syracuseStep 22641941 = 1061341) (by norm_num)
theorem B60378509 : Blo 1933435 60378509 := bstep (se 3 (by rfl) ⟨11320970, by rfl⟩ : syracuseStep 60378509 = 22641941) B22641941
theorem B40252339 : Blo 1933435 40252339 := bstep (se 1 (by rfl) ⟨30189254, by rfl⟩ : syracuseStep 40252339 = 60378509) B60378509
theorem B53669785 : Blo 1933435 53669785 := bstep (se 2 (by rfl) ⟨20126169, by rfl⟩ : syracuseStep 53669785 = 40252339) B40252339
theorem B71559713 : Blo 1933435 71559713 := bstep (se 2 (by rfl) ⟨26834892, by rfl⟩ : syracuseStep 71559713 = 53669785) B53669785
theorem B190825901 : Blo 1933435 190825901 := bstep (se 3 (by rfl) ⟨35779856, by rfl⟩ : syracuseStep 190825901 = 71559713) B71559713
theorem B127217267 : Blo 1933435 127217267 := bstep (se 1 (by rfl) ⟨95412950, by rfl⟩ : syracuseStep 127217267 = 190825901) B190825901
theorem B84811511 : Blo 1933435 84811511 := bstep (se 1 (by rfl) ⟨63608633, by rfl⟩ : syracuseStep 84811511 = 127217267) B127217267
theorem B56541007 : Blo 1933435 56541007 := bstep (se 1 (by rfl) ⟨42405755, by rfl⟩ : syracuseStep 56541007 = 84811511) B84811511
theorem B75388009 : Blo 1933435 75388009 := bstep (se 2 (by rfl) ⟨28270503, by rfl⟩ : syracuseStep 75388009 = 56541007) B56541007
theorem B100517345 : Blo 1933435 100517345 := bstep (se 2 (by rfl) ⟨37694004, by rfl⟩ : syracuseStep 100517345 = 75388009) B75388009
theorem B67011563 : Blo 1933435 67011563 := bstep (se 1 (by rfl) ⟨50258672, by rfl⟩ : syracuseStep 67011563 = 100517345) B100517345
theorem B178697501 : Blo 1933435 178697501 := bstep (se 3 (by rfl) ⟨33505781, by rfl⟩ : syracuseStep 178697501 = 67011563) B67011563
theorem B119131667 : Blo 1933435 119131667 := bstep (se 1 (by rfl) ⟨89348750, by rfl⟩ : syracuseStep 119131667 = 178697501) B178697501
theorem B79421111 : Blo 1933435 79421111 := bstep (se 1 (by rfl) ⟨59565833, by rfl⟩ : syracuseStep 79421111 = 119131667) B119131667
theorem B52947407 : Blo 1933435 52947407 := bstep (se 1 (by rfl) ⟨39710555, by rfl⟩ : syracuseStep 52947407 = 79421111) B79421111
theorem B35298271 : Blo 1933435 35298271 := bstep (se 1 (by rfl) ⟨26473703, by rfl⟩ : syracuseStep 35298271 = 52947407) B52947407
theorem B47064361 : Blo 1933435 47064361 := bstep (se 2 (by rfl) ⟨17649135, by rfl⟩ : syracuseStep 47064361 = 35298271) B35298271
theorem B62752481 : Blo 1933435 62752481 := bstep (se 2 (by rfl) ⟨23532180, by rfl⟩ : syracuseStep 62752481 = 47064361) B47064361
theorem B41834987 : Blo 1933435 41834987 := bstep (se 1 (by rfl) ⟨31376240, by rfl⟩ : syracuseStep 41834987 = 62752481) B62752481
theorem B27889991 : Blo 1933435 27889991 := bstep (se 1 (by rfl) ⟨20917493, by rfl⟩ : syracuseStep 27889991 = 41834987) B41834987
theorem B18593327 : Blo 1933435 18593327 := bstep (se 1 (by rfl) ⟨13944995, by rfl⟩ : syracuseStep 18593327 = 27889991) B27889991
theorem B12395551 : Blo 1933435 12395551 := bstep (se 1 (by rfl) ⟨9296663, by rfl⟩ : syracuseStep 12395551 = 18593327) B18593327
theorem B16527401 : Blo 1933435 16527401 := bstep (se 2 (by rfl) ⟨6197775, by rfl⟩ : syracuseStep 16527401 = 12395551) B12395551
theorem B11018267 : Blo 1933435 11018267 := bstep (se 1 (by rfl) ⟨8263700, by rfl⟩ : syracuseStep 11018267 = 16527401) B16527401
theorem B7345511 : Blo 1933435 7345511 := bstep (se 1 (by rfl) ⟨5509133, by rfl⟩ : syracuseStep 7345511 = 11018267) B11018267
theorem B4897007 : Blo 1933435 4897007 := bstep (se 1 (by rfl) ⟨3672755, by rfl⟩ : syracuseStep 4897007 = 7345511) B7345511
theorem B3264671 : Blo 1933435 3264671 := bstep (se 1 (by rfl) ⟨2448503, by rfl⟩ : syracuseStep 3264671 = 4897007) B4897007
theorem B2176447 : Blo 1933435 2176447 := bstep (se 1 (by rfl) ⟨1632335, by rfl⟩ : syracuseStep 2176447 = 3264671) B3264671
theorem B2901929 : Blo 1933435 2901929 := bstep (se 2 (by rfl) ⟨1088223, by rfl⟩ : syracuseStep 2901929 = 2176447) B2176447
theorem B1934619 : Blo 1933435 1934619 := bstep (se 1 (by rfl) ⟨1450964, by rfl⟩ : syracuseStep 1934619 = 2901929) B2901929
theorem B7345525 : Blo 1933435 7345525 := bbase (se 5 (by rfl) ⟨344321, by rfl⟩ : syracuseStep 7345525 = 688643) (by norm_num)
theorem B9794033 : Blo 1933435 9794033 := bstep (se 2 (by rfl) ⟨3672762, by rfl⟩ : syracuseStep 9794033 = 7345525) B7345525
theorem B6529355 : Blo 1933435 6529355 := bstep (se 1 (by rfl) ⟨4897016, by rfl⟩ : syracuseStep 6529355 = 9794033) B9794033
theorem B4352903 : Blo 1933435 4352903 := bstep (se 1 (by rfl) ⟨3264677, by rfl⟩ : syracuseStep 4352903 = 6529355) B6529355
theorem B2901935 : Blo 1933435 2901935 := bstep (se 1 (by rfl) ⟨2176451, by rfl⟩ : syracuseStep 2901935 = 4352903) B4352903
theorem B1934623 : Blo 1933435 1934623 := bstep (se 1 (by rfl) ⟨1450967, by rfl⟩ : syracuseStep 1934623 = 2901935) B2901935
theorem B2901941 : Blo 1933435 2901941 := bbase (se 5 (by rfl) ⟨136028, by rfl⟩ : syracuseStep 2901941 = 272057) (by norm_num)
theorem B1934627 : Blo 1933435 1934627 := bstep (se 1 (by rfl) ⟨1450970, by rfl⟩ : syracuseStep 1934627 = 2901941) B2901941
theorem B4897037 : Blo 1933435 4897037 := bbase (se 3 (by rfl) ⟨918194, by rfl⟩ : syracuseStep 4897037 = 1836389) (by norm_num)
theorem B3264691 : Blo 1933435 3264691 := bstep (se 1 (by rfl) ⟨2448518, by rfl⟩ : syracuseStep 3264691 = 4897037) B4897037
theorem B4352921 : Blo 1933435 4352921 := bstep (se 2 (by rfl) ⟨1632345, by rfl⟩ : syracuseStep 4352921 = 3264691) B3264691
theorem B2901947 : Blo 1933435 2901947 := bstep (se 1 (by rfl) ⟨2176460, by rfl⟩ : syracuseStep 2901947 = 4352921) B4352921
theorem B1934631 : Blo 1933435 1934631 := bstep (se 1 (by rfl) ⟨1450973, by rfl⟩ : syracuseStep 1934631 = 2901947) B2901947
theorem B2176465 : Blo 1933435 2176465 := bbase (se 2 (by rfl) ⟨816174, by rfl⟩ : syracuseStep 2176465 = 1632349) (by norm_num)
theorem B2901953 : Blo 1933435 2901953 := bstep (se 2 (by rfl) ⟨1088232, by rfl⟩ : syracuseStep 2901953 = 2176465) B2176465
theorem B1934635 : Blo 1933435 1934635 := bstep (se 1 (by rfl) ⟨1450976, by rfl⟩ : syracuseStep 1934635 = 2901953) B2901953
theorem B4131893 : Blo 1933435 4131893 := bbase (se 5 (by rfl) ⟨193682, by rfl⟩ : syracuseStep 4131893 = 387365) (by norm_num)
theorem B2754595 : Blo 1933435 2754595 := bstep (se 1 (by rfl) ⟨2065946, by rfl⟩ : syracuseStep 2754595 = 4131893) B4131893
theorem B3672793 : Blo 1933435 3672793 := bstep (se 2 (by rfl) ⟨1377297, by rfl⟩ : syracuseStep 3672793 = 2754595) B2754595
theorem B4897057 : Blo 1933435 4897057 := bstep (se 2 (by rfl) ⟨1836396, by rfl⟩ : syracuseStep 4897057 = 3672793) B3672793
theorem B6529409 : Blo 1933435 6529409 := bstep (se 2 (by rfl) ⟨2448528, by rfl⟩ : syracuseStep 6529409 = 4897057) B4897057
theorem B4352939 : Blo 1933435 4352939 := bstep (se 1 (by rfl) ⟨3264704, by rfl⟩ : syracuseStep 4352939 = 6529409) B6529409
theorem B2901959 : Blo 1933435 2901959 := bstep (se 1 (by rfl) ⟨2176469, by rfl⟩ : syracuseStep 2901959 = 4352939) B4352939
theorem B1934639 : Blo 1933435 1934639 := bstep (se 1 (by rfl) ⟨1450979, by rfl⟩ : syracuseStep 1934639 = 2901959) B2901959
theorem B2901965 : Blo 1933435 2901965 := bbase (se 3 (by rfl) ⟨544118, by rfl⟩ : syracuseStep 2901965 = 1088237) (by norm_num)
theorem B1934643 : Blo 1933435 1934643 := bstep (se 1 (by rfl) ⟨1450982, by rfl⟩ : syracuseStep 1934643 = 2901965) B2901965
theorem B4352957 : Blo 1933435 4352957 := bbase (se 3 (by rfl) ⟨816179, by rfl⟩ : syracuseStep 4352957 = 1632359) (by norm_num)
theorem B2901971 : Blo 1933435 2901971 := bstep (se 1 (by rfl) ⟨2176478, by rfl⟩ : syracuseStep 2901971 = 4352957) B4352957
theorem B1934647 : Blo 1933435 1934647 := bstep (se 1 (by rfl) ⟨1450985, by rfl⟩ : syracuseStep 1934647 = 2901971) B2901971
theorem B3264725 : Blo 1933435 3264725 := bbase (se 7 (by rfl) ⟨38258, by rfl⟩ : syracuseStep 3264725 = 76517) (by norm_num)
theorem B2176483 : Blo 1933435 2176483 := bstep (se 1 (by rfl) ⟨1632362, by rfl⟩ : syracuseStep 2176483 = 3264725) B3264725
theorem B2901977 : Blo 1933435 2901977 := bstep (se 2 (by rfl) ⟨1088241, by rfl⟩ : syracuseStep 2901977 = 2176483) B2176483
theorem B1934651 : Blo 1933435 1934651 := bstep (se 1 (by rfl) ⟨1450988, by rfl⟩ : syracuseStep 1934651 = 2901977) B2901977
theorem B2324209 : Blo 1933435 2324209 := bbase (se 2 (by rfl) ⟨871578, by rfl⟩ : syracuseStep 2324209 = 1743157) (by norm_num)
theorem B3098945 : Blo 1933435 3098945 := bstep (se 2 (by rfl) ⟨1162104, by rfl⟩ : syracuseStep 3098945 = 2324209) B2324209
theorem B8263853 : Blo 1933435 8263853 := bstep (se 3 (by rfl) ⟨1549472, by rfl⟩ : syracuseStep 8263853 = 3098945) B3098945
theorem B5509235 : Blo 1933435 5509235 := bstep (se 1 (by rfl) ⟨4131926, by rfl⟩ : syracuseStep 5509235 = 8263853) B8263853
theorem B14691293 : Blo 1933435 14691293 := bstep (se 3 (by rfl) ⟨2754617, by rfl⟩ : syracuseStep 14691293 = 5509235) B5509235
theorem B9794195 : Blo 1933435 9794195 := bstep (se 1 (by rfl) ⟨7345646, by rfl⟩ : syracuseStep 9794195 = 14691293) B14691293
theorem B6529463 : Blo 1933435 6529463 := bstep (se 1 (by rfl) ⟨4897097, by rfl⟩ : syracuseStep 6529463 = 9794195) B9794195
theorem B4352975 : Blo 1933435 4352975 := bstep (se 1 (by rfl) ⟨3264731, by rfl⟩ : syracuseStep 4352975 = 6529463) B6529463
theorem B2901983 : Blo 1933435 2901983 := bstep (se 1 (by rfl) ⟨2176487, by rfl⟩ : syracuseStep 2901983 = 4352975) B4352975
theorem B1934655 : Blo 1933435 1934655 := bstep (se 1 (by rfl) ⟨1450991, by rfl⟩ : syracuseStep 1934655 = 2901983) B2901983
theorem B2901989 : Blo 1933435 2901989 := bbase (se 4 (by rfl) ⟨272061, by rfl⟩ : syracuseStep 2901989 = 544123) (by norm_num)
theorem B1934659 : Blo 1933435 1934659 := bstep (se 1 (by rfl) ⟨1450994, by rfl⟩ : syracuseStep 1934659 = 2901989) B2901989
theorem B6618581 : Blo 1933435 6618581 := bbase (se 7 (by rfl) ⟨77561, by rfl⟩ : syracuseStep 6618581 = 155123) (by norm_num)
theorem B4412387 : Blo 1933435 4412387 := bstep (se 1 (by rfl) ⟨3309290, by rfl⟩ : syracuseStep 4412387 = 6618581) B6618581
theorem B2941591 : Blo 1933435 2941591 := bstep (se 1 (by rfl) ⟨2206193, by rfl⟩ : syracuseStep 2941591 = 4412387) B4412387
theorem B3922121 : Blo 1933435 3922121 := bstep (se 2 (by rfl) ⟨1470795, by rfl⟩ : syracuseStep 3922121 = 2941591) B2941591
theorem B2614747 : Blo 1933435 2614747 := bstep (se 1 (by rfl) ⟨1961060, by rfl⟩ : syracuseStep 2614747 = 3922121) B3922121
theorem B3486329 : Blo 1933435 3486329 := bstep (se 2 (by rfl) ⟨1307373, by rfl⟩ : syracuseStep 3486329 = 2614747) B2614747
theorem B2324219 : Blo 1933435 2324219 := bstep (se 1 (by rfl) ⟨1743164, by rfl⟩ : syracuseStep 2324219 = 3486329) B3486329
theorem B6197917 : Blo 1933435 6197917 := bstep (se 3 (by rfl) ⟨1162109, by rfl⟩ : syracuseStep 6197917 = 2324219) B2324219
theorem B8263889 : Blo 1933435 8263889 := bstep (se 2 (by rfl) ⟨3098958, by rfl⟩ : syracuseStep 8263889 = 6197917) B6197917
theorem B5509259 : Blo 1933435 5509259 := bstep (se 1 (by rfl) ⟨4131944, by rfl⟩ : syracuseStep 5509259 = 8263889) B8263889
theorem B3672839 : Blo 1933435 3672839 := bstep (se 1 (by rfl) ⟨2754629, by rfl⟩ : syracuseStep 3672839 = 5509259) B5509259
theorem B2448559 : Blo 1933435 2448559 := bstep (se 1 (by rfl) ⟨1836419, by rfl⟩ : syracuseStep 2448559 = 3672839) B3672839
theorem B3264745 : Blo 1933435 3264745 := bstep (se 2 (by rfl) ⟨1224279, by rfl⟩ : syracuseStep 3264745 = 2448559) B2448559
theorem B4352993 : Blo 1933435 4352993 := bstep (se 2 (by rfl) ⟨1632372, by rfl⟩ : syracuseStep 4352993 = 3264745) B3264745
theorem B2901995 : Blo 1933435 2901995 := bstep (se 1 (by rfl) ⟨2176496, by rfl⟩ : syracuseStep 2901995 = 4352993) B4352993
theorem B1934663 : Blo 1933435 1934663 := bstep (se 1 (by rfl) ⟨1450997, by rfl⟩ : syracuseStep 1934663 = 2901995) B2901995
theorem B2176501 : Blo 1933435 2176501 := bbase (se 5 (by rfl) ⟨102023, by rfl⟩ : syracuseStep 2176501 = 204047) (by norm_num)
theorem B2902001 : Blo 1933435 2902001 := bstep (se 2 (by rfl) ⟨1088250, by rfl⟩ : syracuseStep 2902001 = 2176501) B2176501
theorem B1934667 : Blo 1933435 1934667 := bstep (se 1 (by rfl) ⟨1451000, by rfl⟩ : syracuseStep 1934667 = 2902001) B2902001
theorem B2448569 : Blo 1933435 2448569 := bbase (se 2 (by rfl) ⟨918213, by rfl⟩ : syracuseStep 2448569 = 1836427) (by norm_num)
theorem B6529517 : Blo 1933435 6529517 := bstep (se 3 (by rfl) ⟨1224284, by rfl⟩ : syracuseStep 6529517 = 2448569) B2448569
theorem B4353011 : Blo 1933435 4353011 := bstep (se 1 (by rfl) ⟨3264758, by rfl⟩ : syracuseStep 4353011 = 6529517) B6529517
theorem B2902007 : Blo 1933435 2902007 := bstep (se 1 (by rfl) ⟨2176505, by rfl⟩ : syracuseStep 2902007 = 4353011) B4353011
theorem B1934671 : Blo 1933435 1934671 := bstep (se 1 (by rfl) ⟨1451003, by rfl⟩ : syracuseStep 1934671 = 2902007) B2902007
theorem B2902013 : Blo 1933435 2902013 := bbase (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) (by norm_num)
theorem B1934675 : Blo 1933435 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B4353029 : Blo 1933435 4353029 := bbase (se 4 (by rfl) ⟨408096, by rfl⟩ : syracuseStep 4353029 = 816193) (by norm_num)
theorem B2902019 : Blo 1933435 2902019 := bstep (se 1 (by rfl) ⟨2176514, by rfl⟩ : syracuseStep 2902019 = 4353029) B4353029
theorem B1934679 : Blo 1933435 1934679 := bstep (se 1 (by rfl) ⟨1451009, by rfl⟩ : syracuseStep 1934679 = 2902019) B2902019
theorem B3672877 : Blo 1933435 3672877 := bbase (se 3 (by rfl) ⟨688664, by rfl⟩ : syracuseStep 3672877 = 1377329) (by norm_num)
theorem B4897169 : Blo 1933435 4897169 := bstep (se 2 (by rfl) ⟨1836438, by rfl⟩ : syracuseStep 4897169 = 3672877) B3672877
theorem B3264779 : Blo 1933435 3264779 := bstep (se 1 (by rfl) ⟨2448584, by rfl⟩ : syracuseStep 3264779 = 4897169) B4897169
theorem B2176519 : Blo 1933435 2176519 := bstep (se 1 (by rfl) ⟨1632389, by rfl⟩ : syracuseStep 2176519 = 3264779) B3264779
theorem B2902025 : Blo 1933435 2902025 := bstep (se 2 (by rfl) ⟨1088259, by rfl⟩ : syracuseStep 2902025 = 2176519) B2176519
theorem B1934683 : Blo 1933435 1934683 := bstep (se 1 (by rfl) ⟨1451012, by rfl⟩ : syracuseStep 1934683 = 2902025) B2902025
theorem B9794357 : Blo 1933435 9794357 := bbase (se 5 (by rfl) ⟨459110, by rfl⟩ : syracuseStep 9794357 = 918221) (by norm_num)
theorem B6529571 : Blo 1933435 6529571 := bstep (se 1 (by rfl) ⟨4897178, by rfl⟩ : syracuseStep 6529571 = 9794357) B9794357
theorem B4353047 : Blo 1933435 4353047 := bstep (se 1 (by rfl) ⟨3264785, by rfl⟩ : syracuseStep 4353047 = 6529571) B6529571
theorem B2902031 : Blo 1933435 2902031 := bstep (se 1 (by rfl) ⟨2176523, by rfl⟩ : syracuseStep 2902031 = 4353047) B4353047
theorem B1934687 : Blo 1933435 1934687 := bstep (se 1 (by rfl) ⟨1451015, by rfl⟩ : syracuseStep 1934687 = 2902031) B2902031
theorem B2902037 : Blo 1933435 2902037 := bbase (se 6 (by rfl) ⟨68016, by rfl⟩ : syracuseStep 2902037 = 136033) (by norm_num)
theorem B1934691 : Blo 1933435 1934691 := bstep (se 1 (by rfl) ⟨1451018, by rfl⟩ : syracuseStep 1934691 = 2902037) B2902037
theorem B2324257 : Blo 1933435 2324257 := bbase (se 2 (by rfl) ⟨871596, by rfl⟩ : syracuseStep 2324257 = 1743193) (by norm_num)
theorem B12396037 : Blo 1933435 12396037 := bstep (se 4 (by rfl) ⟨1162128, by rfl⟩ : syracuseStep 12396037 = 2324257) B2324257
theorem B16528049 : Blo 1933435 16528049 := bstep (se 2 (by rfl) ⟨6198018, by rfl⟩ : syracuseStep 16528049 = 12396037) B12396037
theorem B11018699 : Blo 1933435 11018699 := bstep (se 1 (by rfl) ⟨8264024, by rfl⟩ : syracuseStep 11018699 = 16528049) B16528049
theorem B7345799 : Blo 1933435 7345799 := bstep (se 1 (by rfl) ⟨5509349, by rfl⟩ : syracuseStep 7345799 = 11018699) B11018699
theorem B4897199 : Blo 1933435 4897199 := bstep (se 1 (by rfl) ⟨3672899, by rfl⟩ : syracuseStep 4897199 = 7345799) B7345799
theorem B3264799 : Blo 1933435 3264799 := bstep (se 1 (by rfl) ⟨2448599, by rfl⟩ : syracuseStep 3264799 = 4897199) B4897199
theorem B4353065 : Blo 1933435 4353065 := bstep (se 2 (by rfl) ⟨1632399, by rfl⟩ : syracuseStep 4353065 = 3264799) B3264799
theorem B2902043 : Blo 1933435 2902043 := bstep (se 1 (by rfl) ⟨2176532, by rfl⟩ : syracuseStep 2902043 = 4353065) B4353065
theorem B1934695 : Blo 1933435 1934695 := bstep (se 1 (by rfl) ⟨1451021, by rfl⟩ : syracuseStep 1934695 = 2902043) B2902043
theorem B2176537 : Blo 1933435 2176537 := bbase (se 2 (by rfl) ⟨816201, by rfl⟩ : syracuseStep 2176537 = 1632403) (by norm_num)
theorem B2902049 : Blo 1933435 2902049 := bstep (se 2 (by rfl) ⟨1088268, by rfl⟩ : syracuseStep 2902049 = 2176537) B2176537
theorem B1934699 : Blo 1933435 1934699 := bstep (se 1 (by rfl) ⟨1451024, by rfl⟩ : syracuseStep 1934699 = 2902049) B2902049
theorem B7345829 : Blo 1933435 7345829 := bbase (se 4 (by rfl) ⟨688671, by rfl⟩ : syracuseStep 7345829 = 1377343) (by norm_num)
theorem B4897219 : Blo 1933435 4897219 := bstep (se 1 (by rfl) ⟨3672914, by rfl⟩ : syracuseStep 4897219 = 7345829) B7345829
theorem B6529625 : Blo 1933435 6529625 := bstep (se 2 (by rfl) ⟨2448609, by rfl⟩ : syracuseStep 6529625 = 4897219) B4897219
theorem B4353083 : Blo 1933435 4353083 := bstep (se 1 (by rfl) ⟨3264812, by rfl⟩ : syracuseStep 4353083 = 6529625) B6529625
theorem B2902055 : Blo 1933435 2902055 := bstep (se 1 (by rfl) ⟨2176541, by rfl⟩ : syracuseStep 2902055 = 4353083) B4353083
theorem B1934703 : Blo 1933435 1934703 := bstep (se 1 (by rfl) ⟨1451027, by rfl⟩ : syracuseStep 1934703 = 2902055) B2902055
theorem B2902061 : Blo 1933435 2902061 := bbase (se 3 (by rfl) ⟨544136, by rfl⟩ : syracuseStep 2902061 = 1088273) (by norm_num)
theorem B1934707 : Blo 1933435 1934707 := bstep (se 1 (by rfl) ⟨1451030, by rfl⟩ : syracuseStep 1934707 = 2902061) B2902061
theorem B4353101 : Blo 1933435 4353101 := bbase (se 3 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 4353101 = 1632413) (by norm_num)
theorem B2902067 : Blo 1933435 2902067 := bstep (se 1 (by rfl) ⟨2176550, by rfl⟩ : syracuseStep 2902067 = 4353101) B4353101
theorem B1934711 : Blo 1933435 1934711 := bstep (se 1 (by rfl) ⟨1451033, by rfl⟩ : syracuseStep 1934711 = 2902067) B2902067
theorem B2448625 : Blo 1933435 2448625 := bbase (se 2 (by rfl) ⟨918234, by rfl⟩ : syracuseStep 2448625 = 1836469) (by norm_num)
theorem B3264833 : Blo 1933435 3264833 := bstep (se 2 (by rfl) ⟨1224312, by rfl⟩ : syracuseStep 3264833 = 2448625) B2448625
theorem B2176555 : Blo 1933435 2176555 := bstep (se 1 (by rfl) ⟨1632416, by rfl⟩ : syracuseStep 2176555 = 3264833) B3264833
theorem B2902073 : Blo 1933435 2902073 := bstep (se 2 (by rfl) ⟨1088277, by rfl⟩ : syracuseStep 2902073 = 2176555) B2176555
theorem B1934715 : Blo 1933435 1934715 := bstep (se 1 (by rfl) ⟨1451036, by rfl⟩ : syracuseStep 1934715 = 2902073) B2902073
theorem B5883349 : Blo 1933435 5883349 := bbase (se 7 (by rfl) ⟨68945, by rfl⟩ : syracuseStep 5883349 = 137891) (by norm_num)
theorem B7844465 : Blo 1933435 7844465 := bstep (se 2 (by rfl) ⟨2941674, by rfl⟩ : syracuseStep 7844465 = 5883349) B5883349
theorem B20918573 : Blo 1933435 20918573 := bstep (se 3 (by rfl) ⟨3922232, by rfl⟩ : syracuseStep 20918573 = 7844465) B7844465
theorem B13945715 : Blo 1933435 13945715 := bstep (se 1 (by rfl) ⟨10459286, by rfl⟩ : syracuseStep 13945715 = 20918573) B20918573
theorem B9297143 : Blo 1933435 9297143 := bstep (se 1 (by rfl) ⟨6972857, by rfl⟩ : syracuseStep 9297143 = 13945715) B13945715
theorem B6198095 : Blo 1933435 6198095 := bstep (se 1 (by rfl) ⟨4648571, by rfl⟩ : syracuseStep 6198095 = 9297143) B9297143
theorem B4132063 : Blo 1933435 4132063 := bstep (se 1 (by rfl) ⟨3099047, by rfl⟩ : syracuseStep 4132063 = 6198095) B6198095
theorem B22037669 : Blo 1933435 22037669 := bstep (se 4 (by rfl) ⟨2066031, by rfl⟩ : syracuseStep 22037669 = 4132063) B4132063
theorem B14691779 : Blo 1933435 14691779 := bstep (se 1 (by rfl) ⟨11018834, by rfl⟩ : syracuseStep 14691779 = 22037669) B22037669
theorem B9794519 : Blo 1933435 9794519 := bstep (se 1 (by rfl) ⟨7345889, by rfl⟩ : syracuseStep 9794519 = 14691779) B14691779
theorem B6529679 : Blo 1933435 6529679 := bstep (se 1 (by rfl) ⟨4897259, by rfl⟩ : syracuseStep 6529679 = 9794519) B9794519
theorem B4353119 : Blo 1933435 4353119 := bstep (se 1 (by rfl) ⟨3264839, by rfl⟩ : syracuseStep 4353119 = 6529679) B6529679
theorem B2902079 : Blo 1933435 2902079 := bstep (se 1 (by rfl) ⟨2176559, by rfl⟩ : syracuseStep 2902079 = 4353119) B4353119
theorem B1934719 : Blo 1933435 1934719 := bstep (se 1 (by rfl) ⟨1451039, by rfl⟩ : syracuseStep 1934719 = 2902079) B2902079
theorem B2902085 : Blo 1933435 2902085 := bbase (se 4 (by rfl) ⟨272070, by rfl⟩ : syracuseStep 2902085 = 544141) (by norm_num)
theorem B1934723 : Blo 1933435 1934723 := bstep (se 1 (by rfl) ⟨1451042, by rfl⟩ : syracuseStep 1934723 = 2902085) B2902085
theorem B3264853 : Blo 1933435 3264853 := bbase (se 10 (by rfl) ⟨4782, by rfl⟩ : syracuseStep 3264853 = 9565) (by norm_num)
theorem B4353137 : Blo 1933435 4353137 := bstep (se 2 (by rfl) ⟨1632426, by rfl⟩ : syracuseStep 4353137 = 3264853) B3264853
theorem B2902091 : Blo 1933435 2902091 := bstep (se 1 (by rfl) ⟨2176568, by rfl⟩ : syracuseStep 2902091 = 4353137) B4353137
theorem B1934727 : Blo 1933435 1934727 := bstep (se 1 (by rfl) ⟨1451045, by rfl⟩ : syracuseStep 1934727 = 2902091) B2902091
theorem B2176573 : Blo 1933435 2176573 := bbase (se 3 (by rfl) ⟨408107, by rfl⟩ : syracuseStep 2176573 = 816215) (by norm_num)
theorem B2902097 : Blo 1933435 2902097 := bstep (se 2 (by rfl) ⟨1088286, by rfl⟩ : syracuseStep 2902097 = 2176573) B2176573
theorem B1934731 : Blo 1933435 1934731 := bstep (se 1 (by rfl) ⟨1451048, by rfl⟩ : syracuseStep 1934731 = 2902097) B2902097
theorem B6529733 : Blo 1933435 6529733 := bbase (se 4 (by rfl) ⟨612162, by rfl⟩ : syracuseStep 6529733 = 1224325) (by norm_num)
theorem B4353155 : Blo 1933435 4353155 := bstep (se 1 (by rfl) ⟨3264866, by rfl⟩ : syracuseStep 4353155 = 6529733) B6529733
theorem B2902103 : Blo 1933435 2902103 := bstep (se 1 (by rfl) ⟨2176577, by rfl⟩ : syracuseStep 2902103 = 4353155) B4353155
theorem B1934735 : Blo 1933435 1934735 := bstep (se 1 (by rfl) ⟨1451051, by rfl⟩ : syracuseStep 1934735 = 2902103) B2902103
theorem B2902109 : Blo 1933435 2902109 := bbase (se 3 (by rfl) ⟨544145, by rfl⟩ : syracuseStep 2902109 = 1088291) (by norm_num)
theorem B1934739 : Blo 1933435 1934739 := bstep (se 1 (by rfl) ⟨1451054, by rfl⟩ : syracuseStep 1934739 = 2902109) B2902109
theorem B4353173 : Blo 1933435 4353173 := bbase (se 6 (by rfl) ⟨102027, by rfl⟩ : syracuseStep 4353173 = 204055) (by norm_num)
theorem B2902115 : Blo 1933435 2902115 := bstep (se 1 (by rfl) ⟨2176586, by rfl⟩ : syracuseStep 2902115 = 4353173) B4353173
theorem B1934743 : Blo 1933435 1934743 := bstep (se 1 (by rfl) ⟨1451057, by rfl⟩ : syracuseStep 1934743 = 2902115) B2902115
theorem B2754749 : Blo 1933435 2754749 := bbase (se 3 (by rfl) ⟨516515, by rfl⟩ : syracuseStep 2754749 = 1033031) (by norm_num)
theorem B7345997 : Blo 1933435 7345997 := bstep (se 3 (by rfl) ⟨1377374, by rfl⟩ : syracuseStep 7345997 = 2754749) B2754749
theorem B4897331 : Blo 1933435 4897331 := bstep (se 1 (by rfl) ⟨3672998, by rfl⟩ : syracuseStep 4897331 = 7345997) B7345997
theorem B3264887 : Blo 1933435 3264887 := bstep (se 1 (by rfl) ⟨2448665, by rfl⟩ : syracuseStep 3264887 = 4897331) B4897331
theorem B2176591 : Blo 1933435 2176591 := bstep (se 1 (by rfl) ⟨1632443, by rfl⟩ : syracuseStep 2176591 = 3264887) B3264887
theorem B2902121 : Blo 1933435 2902121 := bstep (se 2 (by rfl) ⟨1088295, by rfl⟩ : syracuseStep 2902121 = 2176591) B2176591
theorem B1934747 : Blo 1933435 1934747 := bstep (se 1 (by rfl) ⟨1451060, by rfl⟩ : syracuseStep 1934747 = 2902121) B2902121
theorem B6368485 : Blo 1933435 6368485 := bbase (se 4 (by rfl) ⟨597045, by rfl⟩ : syracuseStep 6368485 = 1194091) (by norm_num)
theorem B8491313 : Blo 1933435 8491313 := bstep (se 2 (by rfl) ⟨3184242, by rfl⟩ : syracuseStep 8491313 = 6368485) B6368485
theorem B5660875 : Blo 1933435 5660875 := bstep (se 1 (by rfl) ⟨4245656, by rfl⟩ : syracuseStep 5660875 = 8491313) B8491313
theorem B7547833 : Blo 1933435 7547833 := bstep (se 2 (by rfl) ⟨2830437, by rfl⟩ : syracuseStep 7547833 = 5660875) B5660875
theorem B10063777 : Blo 1933435 10063777 := bstep (se 2 (by rfl) ⟨3773916, by rfl⟩ : syracuseStep 10063777 = 7547833) B7547833
theorem B13418369 : Blo 1933435 13418369 := bstep (se 2 (by rfl) ⟨5031888, by rfl⟩ : syracuseStep 13418369 = 10063777) B10063777
theorem B8945579 : Blo 1933435 8945579 := bstep (se 1 (by rfl) ⟨6709184, by rfl⟩ : syracuseStep 8945579 = 13418369) B13418369
theorem B5963719 : Blo 1933435 5963719 := bstep (se 1 (by rfl) ⟨4472789, by rfl⟩ : syracuseStep 5963719 = 8945579) B8945579
theorem B7951625 : Blo 1933435 7951625 := bstep (se 2 (by rfl) ⟨2981859, by rfl⟩ : syracuseStep 7951625 = 5963719) B5963719
theorem B5301083 : Blo 1933435 5301083 := bstep (se 1 (by rfl) ⟨3975812, by rfl⟩ : syracuseStep 5301083 = 7951625) B7951625
theorem B14136221 : Blo 1933435 14136221 := bstep (se 3 (by rfl) ⟨2650541, by rfl⟩ : syracuseStep 14136221 = 5301083) B5301083
theorem B37696589 : Blo 1933435 37696589 := bstep (se 3 (by rfl) ⟨7068110, by rfl⟩ : syracuseStep 37696589 = 14136221) B14136221
theorem B25131059 : Blo 1933435 25131059 := bstep (se 1 (by rfl) ⟨18848294, by rfl⟩ : syracuseStep 25131059 = 37696589) B37696589
theorem B16754039 : Blo 1933435 16754039 := bstep (se 1 (by rfl) ⟨12565529, by rfl⟩ : syracuseStep 16754039 = 25131059) B25131059
theorem B11169359 : Blo 1933435 11169359 := bstep (se 1 (by rfl) ⟨8377019, by rfl⟩ : syracuseStep 11169359 = 16754039) B16754039
theorem B7446239 : Blo 1933435 7446239 := bstep (se 1 (by rfl) ⟨5584679, by rfl⟩ : syracuseStep 7446239 = 11169359) B11169359
theorem B4964159 : Blo 1933435 4964159 := bstep (se 1 (by rfl) ⟨3723119, by rfl⟩ : syracuseStep 4964159 = 7446239) B7446239
theorem B3309439 : Blo 1933435 3309439 := bstep (se 1 (by rfl) ⟨2482079, by rfl⟩ : syracuseStep 3309439 = 4964159) B4964159
theorem B4412585 : Blo 1933435 4412585 := bstep (se 2 (by rfl) ⟨1654719, by rfl⟩ : syracuseStep 4412585 = 3309439) B3309439
theorem B2941723 : Blo 1933435 2941723 := bstep (se 1 (by rfl) ⟨2206292, by rfl⟩ : syracuseStep 2941723 = 4412585) B4412585
theorem B15689189 : Blo 1933435 15689189 := bstep (se 4 (by rfl) ⟨1470861, by rfl⟩ : syracuseStep 15689189 = 2941723) B2941723
theorem B10459459 : Blo 1933435 10459459 := bstep (se 1 (by rfl) ⟨7844594, by rfl⟩ : syracuseStep 10459459 = 15689189) B15689189
theorem B13945945 : Blo 1933435 13945945 := bstep (se 2 (by rfl) ⟨5229729, by rfl⟩ : syracuseStep 13945945 = 10459459) B10459459
theorem B18594593 : Blo 1933435 18594593 := bstep (se 2 (by rfl) ⟨6972972, by rfl⟩ : syracuseStep 18594593 = 13945945) B13945945
theorem B12396395 : Blo 1933435 12396395 := bstep (se 1 (by rfl) ⟨9297296, by rfl⟩ : syracuseStep 12396395 = 18594593) B18594593
theorem B8264263 : Blo 1933435 8264263 := bstep (se 1 (by rfl) ⟨6198197, by rfl⟩ : syracuseStep 8264263 = 12396395) B12396395
theorem B11019017 : Blo 1933435 11019017 := bstep (se 2 (by rfl) ⟨4132131, by rfl⟩ : syracuseStep 11019017 = 8264263) B8264263
theorem B7346011 : Blo 1933435 7346011 := bstep (se 1 (by rfl) ⟨5509508, by rfl⟩ : syracuseStep 7346011 = 11019017) B11019017
theorem B9794681 : Blo 1933435 9794681 := bstep (se 2 (by rfl) ⟨3673005, by rfl⟩ : syracuseStep 9794681 = 7346011) B7346011
theorem B6529787 : Blo 1933435 6529787 := bstep (se 1 (by rfl) ⟨4897340, by rfl⟩ : syracuseStep 6529787 = 9794681) B9794681
theorem B4353191 : Blo 1933435 4353191 := bstep (se 1 (by rfl) ⟨3264893, by rfl⟩ : syracuseStep 4353191 = 6529787) B6529787
theorem B2902127 : Blo 1933435 2902127 := bstep (se 1 (by rfl) ⟨2176595, by rfl⟩ : syracuseStep 2902127 = 4353191) B4353191
theorem B1934751 : Blo 1933435 1934751 := bstep (se 1 (by rfl) ⟨1451063, by rfl⟩ : syracuseStep 1934751 = 2902127) B2902127
theorem B2902133 : Blo 1933435 2902133 := bbase (se 5 (by rfl) ⟨136037, by rfl⟩ : syracuseStep 2902133 = 272075) (by norm_num)
theorem B1934755 : Blo 1933435 1934755 := bstep (se 1 (by rfl) ⟨1451066, by rfl⟩ : syracuseStep 1934755 = 2902133) B2902133
theorem B3673021 : Blo 1933435 3673021 := bbase (se 3 (by rfl) ⟨688691, by rfl⟩ : syracuseStep 3673021 = 1377383) (by norm_num)
theorem B4897361 : Blo 1933435 4897361 := bstep (se 2 (by rfl) ⟨1836510, by rfl⟩ : syracuseStep 4897361 = 3673021) B3673021
theorem B3264907 : Blo 1933435 3264907 := bstep (se 1 (by rfl) ⟨2448680, by rfl⟩ : syracuseStep 3264907 = 4897361) B4897361
theorem B4353209 : Blo 1933435 4353209 := bstep (se 2 (by rfl) ⟨1632453, by rfl⟩ : syracuseStep 4353209 = 3264907) B3264907
theorem B2902139 : Blo 1933435 2902139 := bstep (se 1 (by rfl) ⟨2176604, by rfl⟩ : syracuseStep 2902139 = 4353209) B4353209
theorem B1934759 : Blo 1933435 1934759 := bstep (se 1 (by rfl) ⟨1451069, by rfl⟩ : syracuseStep 1934759 = 2902139) B2902139
theorem B2176609 : Blo 1933435 2176609 := bbase (se 2 (by rfl) ⟨816228, by rfl⟩ : syracuseStep 2176609 = 1632457) (by norm_num)
theorem B2902145 : Blo 1933435 2902145 := bstep (se 2 (by rfl) ⟨1088304, by rfl⟩ : syracuseStep 2902145 = 2176609) B2176609
theorem B1934763 : Blo 1933435 1934763 := bstep (se 1 (by rfl) ⟨1451072, by rfl⟩ : syracuseStep 1934763 = 2902145) B2902145
theorem B4897381 : Blo 1933435 4897381 := bbase (se 4 (by rfl) ⟨459129, by rfl⟩ : syracuseStep 4897381 = 918259) (by norm_num)
theorem B6529841 : Blo 1933435 6529841 := bstep (se 2 (by rfl) ⟨2448690, by rfl⟩ : syracuseStep 6529841 = 4897381) B4897381
theorem B4353227 : Blo 1933435 4353227 := bstep (se 1 (by rfl) ⟨3264920, by rfl⟩ : syracuseStep 4353227 = 6529841) B6529841
theorem B2902151 : Blo 1933435 2902151 := bstep (se 1 (by rfl) ⟨2176613, by rfl⟩ : syracuseStep 2902151 = 4353227) B4353227
theorem B1934767 : Blo 1933435 1934767 := bstep (se 1 (by rfl) ⟨1451075, by rfl⟩ : syracuseStep 1934767 = 2902151) B2902151
theorem B2902157 : Blo 1933435 2902157 := bbase (se 3 (by rfl) ⟨544154, by rfl⟩ : syracuseStep 2902157 = 1088309) (by norm_num)
theorem B1934771 : Blo 1933435 1934771 := bstep (se 1 (by rfl) ⟨1451078, by rfl⟩ : syracuseStep 1934771 = 2902157) B2902157
theorem B4353245 : Blo 1933435 4353245 := bbase (se 3 (by rfl) ⟨816233, by rfl⟩ : syracuseStep 4353245 = 1632467) (by norm_num)
theorem B2902163 : Blo 1933435 2902163 := bstep (se 1 (by rfl) ⟨2176622, by rfl⟩ : syracuseStep 2902163 = 4353245) B4353245
theorem B1934775 : Blo 1933435 1934775 := bstep (se 1 (by rfl) ⟨1451081, by rfl⟩ : syracuseStep 1934775 = 2902163) B2902163
theorem B3264941 : Blo 1933435 3264941 := bbase (se 3 (by rfl) ⟨612176, by rfl⟩ : syracuseStep 3264941 = 1224353) (by norm_num)
theorem B2176627 : Blo 1933435 2176627 := bstep (se 1 (by rfl) ⟨1632470, by rfl⟩ : syracuseStep 2176627 = 3264941) B3264941
theorem B2902169 : Blo 1933435 2902169 := bstep (se 2 (by rfl) ⟨1088313, by rfl⟩ : syracuseStep 2902169 = 2176627) B2176627
theorem B1934779 : Blo 1933435 1934779 := bstep (se 1 (by rfl) ⟨1451084, by rfl⟩ : syracuseStep 1934779 = 2902169) B2902169
theorem B2981909 : Blo 1933435 2981909 := bbase (se 6 (by rfl) ⟨69888, by rfl⟩ : syracuseStep 2981909 = 139777) (by norm_num)
theorem B1987939 : Blo 1933435 1987939 := bstep (se 1 (by rfl) ⟨1490954, by rfl⟩ : syracuseStep 1987939 = 2981909) B2981909
theorem B2650585 : Blo 1933435 2650585 := bstep (se 2 (by rfl) ⟨993969, by rfl⟩ : syracuseStep 2650585 = 1987939) B1987939
theorem B3534113 : Blo 1933435 3534113 := bstep (se 2 (by rfl) ⟨1325292, by rfl⟩ : syracuseStep 3534113 = 2650585) B2650585
theorem B2356075 : Blo 1933435 2356075 := bstep (se 1 (by rfl) ⟨1767056, by rfl⟩ : syracuseStep 2356075 = 3534113) B3534113
theorem B3141433 : Blo 1933435 3141433 := bstep (se 2 (by rfl) ⟨1178037, by rfl⟩ : syracuseStep 3141433 = 2356075) B2356075
theorem B4188577 : Blo 1933435 4188577 := bstep (se 2 (by rfl) ⟨1570716, by rfl⟩ : syracuseStep 4188577 = 3141433) B3141433
theorem B5584769 : Blo 1933435 5584769 := bstep (se 2 (by rfl) ⟨2094288, by rfl⟩ : syracuseStep 5584769 = 4188577) B4188577
theorem B238283477 : Blo 1933435 238283477 := bstep (se 7 (by rfl) ⟨2792384, by rfl⟩ : syracuseStep 238283477 = 5584769) B5584769
theorem B158855651 : Blo 1933435 158855651 := bstep (se 1 (by rfl) ⟨119141738, by rfl⟩ : syracuseStep 158855651 = 238283477) B238283477
theorem B105903767 : Blo 1933435 105903767 := bstep (se 1 (by rfl) ⟨79427825, by rfl⟩ : syracuseStep 105903767 = 158855651) B158855651
theorem B70602511 : Blo 1933435 70602511 := bstep (se 1 (by rfl) ⟨52951883, by rfl⟩ : syracuseStep 70602511 = 105903767) B105903767
theorem B94136681 : Blo 1933435 94136681 := bstep (se 2 (by rfl) ⟨35301255, by rfl⟩ : syracuseStep 94136681 = 70602511) B70602511
theorem B62757787 : Blo 1933435 62757787 := bstep (se 1 (by rfl) ⟨47068340, by rfl⟩ : syracuseStep 62757787 = 94136681) B94136681
theorem B83677049 : Blo 1933435 83677049 := bstep (se 2 (by rfl) ⟨31378893, by rfl⟩ : syracuseStep 83677049 = 62757787) B62757787
theorem B55784699 : Blo 1933435 55784699 := bstep (se 1 (by rfl) ⟨41838524, by rfl⟩ : syracuseStep 55784699 = 83677049) B83677049
theorem B37189799 : Blo 1933435 37189799 := bstep (se 1 (by rfl) ⟨27892349, by rfl⟩ : syracuseStep 37189799 = 55784699) B55784699
theorem B24793199 : Blo 1933435 24793199 := bstep (se 1 (by rfl) ⟨18594899, by rfl⟩ : syracuseStep 24793199 = 37189799) B37189799
theorem B16528799 : Blo 1933435 16528799 := bstep (se 1 (by rfl) ⟨12396599, by rfl⟩ : syracuseStep 16528799 = 24793199) B24793199
theorem B11019199 : Blo 1933435 11019199 := bstep (se 1 (by rfl) ⟨8264399, by rfl⟩ : syracuseStep 11019199 = 16528799) B16528799
theorem B14692265 : Blo 1933435 14692265 := bstep (se 2 (by rfl) ⟨5509599, by rfl⟩ : syracuseStep 14692265 = 11019199) B11019199
theorem B9794843 : Blo 1933435 9794843 := bstep (se 1 (by rfl) ⟨7346132, by rfl⟩ : syracuseStep 9794843 = 14692265) B14692265
theorem B6529895 : Blo 1933435 6529895 := bstep (se 1 (by rfl) ⟨4897421, by rfl⟩ : syracuseStep 6529895 = 9794843) B9794843
theorem B4353263 : Blo 1933435 4353263 := bstep (se 1 (by rfl) ⟨3264947, by rfl⟩ : syracuseStep 4353263 = 6529895) B6529895
theorem B2902175 : Blo 1933435 2902175 := bstep (se 1 (by rfl) ⟨2176631, by rfl⟩ : syracuseStep 2902175 = 4353263) B4353263
theorem B1934783 : Blo 1933435 1934783 := bstep (se 1 (by rfl) ⟨1451087, by rfl⟩ : syracuseStep 1934783 = 2902175) B2902175
theorem B2902181 : Blo 1933435 2902181 := bbase (se 4 (by rfl) ⟨272079, by rfl⟩ : syracuseStep 2902181 = 544159) (by norm_num)
theorem B1934787 : Blo 1933435 1934787 := bstep (se 1 (by rfl) ⟨1451090, by rfl⟩ : syracuseStep 1934787 = 2902181) B2902181
theorem B2448721 : Blo 1933435 2448721 := bbase (se 2 (by rfl) ⟨918270, by rfl⟩ : syracuseStep 2448721 = 1836541) (by norm_num)
theorem B3264961 : Blo 1933435 3264961 := bstep (se 2 (by rfl) ⟨1224360, by rfl⟩ : syracuseStep 3264961 = 2448721) B2448721
theorem B4353281 : Blo 1933435 4353281 := bstep (se 2 (by rfl) ⟨1632480, by rfl⟩ : syracuseStep 4353281 = 3264961) B3264961
theorem B2902187 : Blo 1933435 2902187 := bstep (se 1 (by rfl) ⟨2176640, by rfl⟩ : syracuseStep 2902187 = 4353281) B4353281
theorem B1934791 : Blo 1933435 1934791 := bstep (se 1 (by rfl) ⟨1451093, by rfl⟩ : syracuseStep 1934791 = 2902187) B2902187
theorem B2176645 : Blo 1933435 2176645 := bbase (se 4 (by rfl) ⟨204060, by rfl⟩ : syracuseStep 2176645 = 408121) (by norm_num)
theorem B2902193 : Blo 1933435 2902193 := bstep (se 2 (by rfl) ⟨1088322, by rfl⟩ : syracuseStep 2902193 = 2176645) B2176645
theorem B1934795 : Blo 1933435 1934795 := bstep (se 1 (by rfl) ⟨1451096, by rfl⟩ : syracuseStep 1934795 = 2902193) B2902193
theorem B4648765 : Blo 1933435 4648765 := bbase (se 3 (by rfl) ⟨871643, by rfl⟩ : syracuseStep 4648765 = 1743287) (by norm_num)
theorem B6198353 : Blo 1933435 6198353 := bstep (se 2 (by rfl) ⟨2324382, by rfl⟩ : syracuseStep 6198353 = 4648765) B4648765
theorem B4132235 : Blo 1933435 4132235 := bstep (se 1 (by rfl) ⟨3099176, by rfl⟩ : syracuseStep 4132235 = 6198353) B6198353
theorem B2754823 : Blo 1933435 2754823 := bstep (se 1 (by rfl) ⟨2066117, by rfl⟩ : syracuseStep 2754823 = 4132235) B4132235
theorem B3673097 : Blo 1933435 3673097 := bstep (se 2 (by rfl) ⟨1377411, by rfl⟩ : syracuseStep 3673097 = 2754823) B2754823
theorem B2448731 : Blo 1933435 2448731 := bstep (se 1 (by rfl) ⟨1836548, by rfl⟩ : syracuseStep 2448731 = 3673097) B3673097
theorem B6529949 : Blo 1933435 6529949 := bstep (se 3 (by rfl) ⟨1224365, by rfl⟩ : syracuseStep 6529949 = 2448731) B2448731
theorem B4353299 : Blo 1933435 4353299 := bstep (se 1 (by rfl) ⟨3264974, by rfl⟩ : syracuseStep 4353299 = 6529949) B6529949
theorem B2902199 : Blo 1933435 2902199 := bstep (se 1 (by rfl) ⟨2176649, by rfl⟩ : syracuseStep 2902199 = 4353299) B4353299
theorem B1934799 : Blo 1933435 1934799 := bstep (se 1 (by rfl) ⟨1451099, by rfl⟩ : syracuseStep 1934799 = 2902199) B2902199
theorem B2902205 : Blo 1933435 2902205 := bbase (se 3 (by rfl) ⟨544163, by rfl⟩ : syracuseStep 2902205 = 1088327) (by norm_num)
theorem B1934803 : Blo 1933435 1934803 := bstep (se 1 (by rfl) ⟨1451102, by rfl⟩ : syracuseStep 1934803 = 2902205) B2902205
theorem B4353317 : Blo 1933435 4353317 := bbase (se 4 (by rfl) ⟨408123, by rfl⟩ : syracuseStep 4353317 = 816247) (by norm_num)
theorem B2902211 : Blo 1933435 2902211 := bstep (se 1 (by rfl) ⟨2176658, by rfl⟩ : syracuseStep 2902211 = 4353317) B4353317
theorem B1934807 : Blo 1933435 1934807 := bstep (se 1 (by rfl) ⟨1451105, by rfl⟩ : syracuseStep 1934807 = 2902211) B2902211
theorem B4897493 : Blo 1933435 4897493 := bbase (se 7 (by rfl) ⟨57392, by rfl⟩ : syracuseStep 4897493 = 114785) (by norm_num)
theorem B3264995 : Blo 1933435 3264995 := bstep (se 1 (by rfl) ⟨2448746, by rfl⟩ : syracuseStep 3264995 = 4897493) B4897493
theorem B2176663 : Blo 1933435 2176663 := bstep (se 1 (by rfl) ⟨1632497, by rfl⟩ : syracuseStep 2176663 = 3264995) B3264995
theorem B2902217 : Blo 1933435 2902217 := bstep (se 2 (by rfl) ⟨1088331, by rfl⟩ : syracuseStep 2902217 = 2176663) B2176663
theorem B1934811 : Blo 1933435 1934811 := bstep (se 1 (by rfl) ⟨1451108, by rfl⟩ : syracuseStep 1934811 = 2902217) B2902217
theorem B9297605 : Blo 1933435 9297605 := bbase (se 4 (by rfl) ⟨871650, by rfl⟩ : syracuseStep 9297605 = 1743301) (by norm_num)
theorem B6198403 : Blo 1933435 6198403 := bstep (se 1 (by rfl) ⟨4648802, by rfl⟩ : syracuseStep 6198403 = 9297605) B9297605
theorem B8264537 : Blo 1933435 8264537 := bstep (se 2 (by rfl) ⟨3099201, by rfl⟩ : syracuseStep 8264537 = 6198403) B6198403
theorem B5509691 : Blo 1933435 5509691 := bstep (se 1 (by rfl) ⟨4132268, by rfl⟩ : syracuseStep 5509691 = 8264537) B8264537
theorem B3673127 : Blo 1933435 3673127 := bstep (se 1 (by rfl) ⟨2754845, by rfl⟩ : syracuseStep 3673127 = 5509691) B5509691
theorem B9795005 : Blo 1933435 9795005 := bstep (se 3 (by rfl) ⟨1836563, by rfl⟩ : syracuseStep 9795005 = 3673127) B3673127
theorem B6530003 : Blo 1933435 6530003 := bstep (se 1 (by rfl) ⟨4897502, by rfl⟩ : syracuseStep 6530003 = 9795005) B9795005
theorem B4353335 : Blo 1933435 4353335 := bstep (se 1 (by rfl) ⟨3265001, by rfl⟩ : syracuseStep 4353335 = 6530003) B6530003
theorem B2902223 : Blo 1933435 2902223 := bstep (se 1 (by rfl) ⟨2176667, by rfl⟩ : syracuseStep 2902223 = 4353335) B4353335
theorem B1934815 : Blo 1933435 1934815 := bstep (se 1 (by rfl) ⟨1451111, by rfl⟩ : syracuseStep 1934815 = 2902223) B2902223
theorem B2902229 : Blo 1933435 2902229 := bbase (se 7 (by rfl) ⟨34010, by rfl⟩ : syracuseStep 2902229 = 68021) (by norm_num)
theorem B1934819 : Blo 1933435 1934819 := bstep (se 1 (by rfl) ⟨1451114, by rfl⟩ : syracuseStep 1934819 = 2902229) B2902229
theorem B3922445 : Blo 1933435 3922445 := bbase (se 3 (by rfl) ⟨735458, by rfl⟩ : syracuseStep 3922445 = 1470917) (by norm_num)
theorem B10459853 : Blo 1933435 10459853 := bstep (se 3 (by rfl) ⟨1961222, by rfl⟩ : syracuseStep 10459853 = 3922445) B3922445
theorem B6973235 : Blo 1933435 6973235 := bstep (se 1 (by rfl) ⟨5229926, by rfl⟩ : syracuseStep 6973235 = 10459853) B10459853
theorem B4648823 : Blo 1933435 4648823 := bstep (se 1 (by rfl) ⟨3486617, by rfl⟩ : syracuseStep 4648823 = 6973235) B6973235
theorem B3099215 : Blo 1933435 3099215 := bstep (se 1 (by rfl) ⟨2324411, by rfl⟩ : syracuseStep 3099215 = 4648823) B4648823
theorem B2066143 : Blo 1933435 2066143 := bstep (se 1 (by rfl) ⟨1549607, by rfl⟩ : syracuseStep 2066143 = 3099215) B3099215
theorem B2754857 : Blo 1933435 2754857 := bstep (se 2 (by rfl) ⟨1033071, by rfl⟩ : syracuseStep 2754857 = 2066143) B2066143
theorem B7346285 : Blo 1933435 7346285 := bstep (se 3 (by rfl) ⟨1377428, by rfl⟩ : syracuseStep 7346285 = 2754857) B2754857
theorem B4897523 : Blo 1933435 4897523 := bstep (se 1 (by rfl) ⟨3673142, by rfl⟩ : syracuseStep 4897523 = 7346285) B7346285
theorem B3265015 : Blo 1933435 3265015 := bstep (se 1 (by rfl) ⟨2448761, by rfl⟩ : syracuseStep 3265015 = 4897523) B4897523
theorem B4353353 : Blo 1933435 4353353 := bstep (se 2 (by rfl) ⟨1632507, by rfl⟩ : syracuseStep 4353353 = 3265015) B3265015
theorem B2902235 : Blo 1933435 2902235 := bstep (se 1 (by rfl) ⟨2176676, by rfl⟩ : syracuseStep 2902235 = 4353353) B4353353
theorem B1934823 : Blo 1933435 1934823 := bstep (se 1 (by rfl) ⟨1451117, by rfl⟩ : syracuseStep 1934823 = 2902235) B2902235
theorem B2176681 : Blo 1933435 2176681 := bbase (se 2 (by rfl) ⟨816255, by rfl⟩ : syracuseStep 2176681 = 1632511) (by norm_num)
theorem B2902241 : Blo 1933435 2902241 := bstep (se 2 (by rfl) ⟨1088340, by rfl⟩ : syracuseStep 2902241 = 2176681) B2176681
theorem B1934827 : Blo 1933435 1934827 := bstep (se 1 (by rfl) ⟨1451120, by rfl⟩ : syracuseStep 1934827 = 2902241) B2902241
theorem B4964365 : Blo 1933435 4964365 := bbase (se 3 (by rfl) ⟨930818, by rfl⟩ : syracuseStep 4964365 = 1861637) (by norm_num)
theorem B6619153 : Blo 1933435 6619153 := bstep (se 2 (by rfl) ⟨2482182, by rfl⟩ : syracuseStep 6619153 = 4964365) B4964365
theorem B8825537 : Blo 1933435 8825537 := bstep (se 2 (by rfl) ⟨3309576, by rfl⟩ : syracuseStep 8825537 = 6619153) B6619153
theorem B5883691 : Blo 1933435 5883691 := bstep (se 1 (by rfl) ⟨4412768, by rfl⟩ : syracuseStep 5883691 = 8825537) B8825537
theorem B7844921 : Blo 1933435 7844921 := bstep (se 2 (by rfl) ⟨2941845, by rfl⟩ : syracuseStep 7844921 = 5883691) B5883691
theorem B5229947 : Blo 1933435 5229947 := bstep (se 1 (by rfl) ⟨3922460, by rfl⟩ : syracuseStep 5229947 = 7844921) B7844921
theorem B3486631 : Blo 1933435 3486631 := bstep (se 1 (by rfl) ⟨2614973, by rfl⟩ : syracuseStep 3486631 = 5229947) B5229947
theorem B4648841 : Blo 1933435 4648841 := bstep (se 2 (by rfl) ⟨1743315, by rfl⟩ : syracuseStep 4648841 = 3486631) B3486631
theorem B3099227 : Blo 1933435 3099227 := bstep (se 1 (by rfl) ⟨2324420, by rfl⟩ : syracuseStep 3099227 = 4648841) B4648841
theorem B8264605 : Blo 1933435 8264605 := bstep (se 3 (by rfl) ⟨1549613, by rfl⟩ : syracuseStep 8264605 = 3099227) B3099227
theorem B11019473 : Blo 1933435 11019473 := bstep (se 2 (by rfl) ⟨4132302, by rfl⟩ : syracuseStep 11019473 = 8264605) B8264605
theorem B7346315 : Blo 1933435 7346315 := bstep (se 1 (by rfl) ⟨5509736, by rfl⟩ : syracuseStep 7346315 = 11019473) B11019473
theorem B4897543 : Blo 1933435 4897543 := bstep (se 1 (by rfl) ⟨3673157, by rfl⟩ : syracuseStep 4897543 = 7346315) B7346315
theorem B6530057 : Blo 1933435 6530057 := bstep (se 2 (by rfl) ⟨2448771, by rfl⟩ : syracuseStep 6530057 = 4897543) B4897543
theorem B4353371 : Blo 1933435 4353371 := bstep (se 1 (by rfl) ⟨3265028, by rfl⟩ : syracuseStep 4353371 = 6530057) B6530057
theorem B2902247 : Blo 1933435 2902247 := bstep (se 1 (by rfl) ⟨2176685, by rfl⟩ : syracuseStep 2902247 = 4353371) B4353371
theorem B1934831 : Blo 1933435 1934831 := bstep (se 1 (by rfl) ⟨1451123, by rfl⟩ : syracuseStep 1934831 = 2902247) B2902247
theorem B2902253 : Blo 1933435 2902253 := bbase (se 3 (by rfl) ⟨544172, by rfl⟩ : syracuseStep 2902253 = 1088345) (by norm_num)
theorem B1934835 : Blo 1933435 1934835 := bstep (se 1 (by rfl) ⟨1451126, by rfl⟩ : syracuseStep 1934835 = 2902253) B2902253
theorem B4353389 : Blo 1933435 4353389 := bbase (se 3 (by rfl) ⟨816260, by rfl⟩ : syracuseStep 4353389 = 1632521) (by norm_num)
theorem B2902259 : Blo 1933435 2902259 := bstep (se 1 (by rfl) ⟨2176694, by rfl⟩ : syracuseStep 2902259 = 4353389) B4353389
theorem B1934839 : Blo 1933435 1934839 := bstep (se 1 (by rfl) ⟨1451129, by rfl⟩ : syracuseStep 1934839 = 2902259) B2902259
theorem B3673181 : Blo 1933435 3673181 := bbase (se 3 (by rfl) ⟨688721, by rfl⟩ : syracuseStep 3673181 = 1377443) (by norm_num)
theorem B2448787 : Blo 1933435 2448787 := bstep (se 1 (by rfl) ⟨1836590, by rfl⟩ : syracuseStep 2448787 = 3673181) B3673181
theorem B3265049 : Blo 1933435 3265049 := bstep (se 2 (by rfl) ⟨1224393, by rfl⟩ : syracuseStep 3265049 = 2448787) B2448787
theorem B2176699 : Blo 1933435 2176699 := bstep (se 1 (by rfl) ⟨1632524, by rfl⟩ : syracuseStep 2176699 = 3265049) B3265049
theorem B2902265 : Blo 1933435 2902265 := bstep (se 2 (by rfl) ⟨1088349, by rfl⟩ : syracuseStep 2902265 = 2176699) B2176699
theorem B1934843 : Blo 1933435 1934843 := bstep (se 1 (by rfl) ⟨1451132, by rfl⟩ : syracuseStep 1934843 = 2902265) B2902265
theorem B5229989 : Blo 1933435 5229989 := bbase (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) (by norm_num)
theorem B3486659 : Blo 1933435 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B9297757 : Blo 1933435 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B49588037 : Blo 1933435 49588037 := bstep (se 4 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 49588037 = 9297757) B9297757
theorem B33058691 : Blo 1933435 33058691 := bstep (se 1 (by rfl) ⟨24794018, by rfl⟩ : syracuseStep 33058691 = 49588037) B49588037
theorem B22039127 : Blo 1933435 22039127 := bstep (se 1 (by rfl) ⟨16529345, by rfl⟩ : syracuseStep 22039127 = 33058691) B33058691
theorem B14692751 : Blo 1933435 14692751 := bstep (se 1 (by rfl) ⟨11019563, by rfl⟩ : syracuseStep 14692751 = 22039127) B22039127
theorem B9795167 : Blo 1933435 9795167 := bstep (se 1 (by rfl) ⟨7346375, by rfl⟩ : syracuseStep 9795167 = 14692751) B14692751
theorem B6530111 : Blo 1933435 6530111 := bstep (se 1 (by rfl) ⟨4897583, by rfl⟩ : syracuseStep 6530111 = 9795167) B9795167
theorem B4353407 : Blo 1933435 4353407 := bstep (se 1 (by rfl) ⟨3265055, by rfl⟩ : syracuseStep 4353407 = 6530111) B6530111
theorem B2902271 : Blo 1933435 2902271 := bstep (se 1 (by rfl) ⟨2176703, by rfl⟩ : syracuseStep 2902271 = 4353407) B4353407
theorem B1934847 : Blo 1933435 1934847 := bstep (se 1 (by rfl) ⟨1451135, by rfl⟩ : syracuseStep 1934847 = 2902271) B2902271
theorem B2902277 : Blo 1933435 2902277 := bbase (se 4 (by rfl) ⟨272088, by rfl⟩ : syracuseStep 2902277 = 544177) (by norm_num)
theorem B1934851 : Blo 1933435 1934851 := bstep (se 1 (by rfl) ⟨1451138, by rfl⟩ : syracuseStep 1934851 = 2902277) B2902277
theorem B3265069 : Blo 1933435 3265069 := bbase (se 3 (by rfl) ⟨612200, by rfl⟩ : syracuseStep 3265069 = 1224401) (by norm_num)
theorem B4353425 : Blo 1933435 4353425 := bstep (se 2 (by rfl) ⟨1632534, by rfl⟩ : syracuseStep 4353425 = 3265069) B3265069
theorem B2902283 : Blo 1933435 2902283 := bstep (se 1 (by rfl) ⟨2176712, by rfl⟩ : syracuseStep 2902283 = 4353425) B4353425
theorem B1934855 : Blo 1933435 1934855 := bstep (se 1 (by rfl) ⟨1451141, by rfl⟩ : syracuseStep 1934855 = 2902283) B2902283
theorem B2176717 : Blo 1933435 2176717 := bbase (se 3 (by rfl) ⟨408134, by rfl⟩ : syracuseStep 2176717 = 816269) (by norm_num)
theorem B2902289 : Blo 1933435 2902289 := bstep (se 2 (by rfl) ⟨1088358, by rfl⟩ : syracuseStep 2902289 = 2176717) B2176717
theorem B1934859 : Blo 1933435 1934859 := bstep (se 1 (by rfl) ⟨1451144, by rfl⟩ : syracuseStep 1934859 = 2902289) B2902289
theorem B6530165 : Blo 1933435 6530165 := bbase (se 5 (by rfl) ⟨306101, by rfl⟩ : syracuseStep 6530165 = 612203) (by norm_num)
theorem B4353443 : Blo 1933435 4353443 := bstep (se 1 (by rfl) ⟨3265082, by rfl⟩ : syracuseStep 4353443 = 6530165) B6530165
theorem B2902295 : Blo 1933435 2902295 := bstep (se 1 (by rfl) ⟨2176721, by rfl⟩ : syracuseStep 2902295 = 4353443) B4353443
theorem B1934863 : Blo 1933435 1934863 := bstep (se 1 (by rfl) ⟨1451147, by rfl⟩ : syracuseStep 1934863 = 2902295) B2902295
theorem B2902301 : Blo 1933435 2902301 := bbase (se 3 (by rfl) ⟨544181, by rfl⟩ : syracuseStep 2902301 = 1088363) (by norm_num)
theorem B1934867 : Blo 1933435 1934867 := bstep (se 1 (by rfl) ⟨1451150, by rfl⟩ : syracuseStep 1934867 = 2902301) B2902301
theorem B4353461 : Blo 1933435 4353461 := bbase (se 5 (by rfl) ⟨204068, by rfl⟩ : syracuseStep 4353461 = 408137) (by norm_num)
theorem B2902307 : Blo 1933435 2902307 := bstep (se 1 (by rfl) ⟨2176730, by rfl⟩ : syracuseStep 2902307 = 4353461) B4353461
theorem B1934871 : Blo 1933435 1934871 := bstep (se 1 (by rfl) ⟨1451153, by rfl⟩ : syracuseStep 1934871 = 2902307) B2902307
theorem B4132397 : Blo 1933435 4132397 := bbase (se 3 (by rfl) ⟨774824, by rfl⟩ : syracuseStep 4132397 = 1549649) (by norm_num)
theorem B11019725 : Blo 1933435 11019725 := bstep (se 3 (by rfl) ⟨2066198, by rfl⟩ : syracuseStep 11019725 = 4132397) B4132397
theorem B7346483 : Blo 1933435 7346483 := bstep (se 1 (by rfl) ⟨5509862, by rfl⟩ : syracuseStep 7346483 = 11019725) B11019725
theorem B4897655 : Blo 1933435 4897655 := bstep (se 1 (by rfl) ⟨3673241, by rfl⟩ : syracuseStep 4897655 = 7346483) B7346483
theorem B3265103 : Blo 1933435 3265103 := bstep (se 1 (by rfl) ⟨2448827, by rfl⟩ : syracuseStep 3265103 = 4897655) B4897655
theorem B2176735 : Blo 1933435 2176735 := bstep (se 1 (by rfl) ⟨1632551, by rfl⟩ : syracuseStep 2176735 = 3265103) B3265103
theorem B2902313 : Blo 1933435 2902313 := bstep (se 2 (by rfl) ⟨1088367, by rfl⟩ : syracuseStep 2902313 = 2176735) B2176735
theorem B1934875 : Blo 1933435 1934875 := bstep (se 1 (by rfl) ⟨1451156, by rfl⟩ : syracuseStep 1934875 = 2902313) B2902313
theorem B4132405 : Blo 1933435 4132405 := bbase (se 5 (by rfl) ⟨193706, by rfl⟩ : syracuseStep 4132405 = 387413) (by norm_num)
theorem B5509873 : Blo 1933435 5509873 := bstep (se 2 (by rfl) ⟨2066202, by rfl⟩ : syracuseStep 5509873 = 4132405) B4132405
theorem B7346497 : Blo 1933435 7346497 := bstep (se 2 (by rfl) ⟨2754936, by rfl⟩ : syracuseStep 7346497 = 5509873) B5509873
theorem B9795329 : Blo 1933435 9795329 := bstep (se 2 (by rfl) ⟨3673248, by rfl⟩ : syracuseStep 9795329 = 7346497) B7346497
theorem B6530219 : Blo 1933435 6530219 := bstep (se 1 (by rfl) ⟨4897664, by rfl⟩ : syracuseStep 6530219 = 9795329) B9795329
theorem B4353479 : Blo 1933435 4353479 := bstep (se 1 (by rfl) ⟨3265109, by rfl⟩ : syracuseStep 4353479 = 6530219) B6530219
theorem B2902319 : Blo 1933435 2902319 := bstep (se 1 (by rfl) ⟨2176739, by rfl⟩ : syracuseStep 2902319 = 4353479) B4353479
theorem B1934879 : Blo 1933435 1934879 := bstep (se 1 (by rfl) ⟨1451159, by rfl⟩ : syracuseStep 1934879 = 2902319) B2902319
theorem B2902325 : Blo 1933435 2902325 := bbase (se 5 (by rfl) ⟨136046, by rfl⟩ : syracuseStep 2902325 = 272093) (by norm_num)
theorem B1934883 : Blo 1933435 1934883 := bstep (se 1 (by rfl) ⟨1451162, by rfl⟩ : syracuseStep 1934883 = 2902325) B2902325
theorem B4897685 : Blo 1933435 4897685 := bbase (se 6 (by rfl) ⟨114789, by rfl⟩ : syracuseStep 4897685 = 229579) (by norm_num)
theorem B3265123 : Blo 1933435 3265123 := bstep (se 1 (by rfl) ⟨2448842, by rfl⟩ : syracuseStep 3265123 = 4897685) B4897685
theorem B4353497 : Blo 1933435 4353497 := bstep (se 2 (by rfl) ⟨1632561, by rfl⟩ : syracuseStep 4353497 = 3265123) B3265123
theorem B2902331 : Blo 1933435 2902331 := bstep (se 1 (by rfl) ⟨2176748, by rfl⟩ : syracuseStep 2902331 = 4353497) B4353497
theorem B1934887 : Blo 1933435 1934887 := bstep (se 1 (by rfl) ⟨1451165, by rfl⟩ : syracuseStep 1934887 = 2902331) B2902331
theorem B2176753 : Blo 1933435 2176753 := bbase (se 2 (by rfl) ⟨816282, by rfl⟩ : syracuseStep 2176753 = 1632565) (by norm_num)
theorem B2902337 : Blo 1933435 2902337 := bstep (se 2 (by rfl) ⟨1088376, by rfl⟩ : syracuseStep 2902337 = 2176753) B2176753
theorem B1934891 : Blo 1933435 1934891 := bstep (se 1 (by rfl) ⟨1451168, by rfl⟩ : syracuseStep 1934891 = 2902337) B2902337
theorem B13238741 : Blo 1933435 13238741 := bbase (se 7 (by rfl) ⟨155141, by rfl⟩ : syracuseStep 13238741 = 310283) (by norm_num)
theorem B8825827 : Blo 1933435 8825827 := bstep (se 1 (by rfl) ⟨6619370, by rfl⟩ : syracuseStep 8825827 = 13238741) B13238741
theorem B11767769 : Blo 1933435 11767769 := bstep (se 2 (by rfl) ⟨4412913, by rfl⟩ : syracuseStep 11767769 = 8825827) B8825827
theorem B7845179 : Blo 1933435 7845179 := bstep (se 1 (by rfl) ⟨5883884, by rfl⟩ : syracuseStep 7845179 = 11767769) B11767769
theorem B20920477 : Blo 1933435 20920477 := bstep (se 3 (by rfl) ⟨3922589, by rfl⟩ : syracuseStep 20920477 = 7845179) B7845179
theorem B27893969 : Blo 1933435 27893969 := bstep (se 2 (by rfl) ⟨10460238, by rfl⟩ : syracuseStep 27893969 = 20920477) B20920477
theorem B18595979 : Blo 1933435 18595979 := bstep (se 1 (by rfl) ⟨13946984, by rfl⟩ : syracuseStep 18595979 = 27893969) B27893969
theorem B12397319 : Blo 1933435 12397319 := bstep (se 1 (by rfl) ⟨9297989, by rfl⟩ : syracuseStep 12397319 = 18595979) B18595979
theorem B8264879 : Blo 1933435 8264879 := bstep (se 1 (by rfl) ⟨6198659, by rfl⟩ : syracuseStep 8264879 = 12397319) B12397319
theorem B5509919 : Blo 1933435 5509919 := bstep (se 1 (by rfl) ⟨4132439, by rfl⟩ : syracuseStep 5509919 = 8264879) B8264879
theorem B3673279 : Blo 1933435 3673279 := bstep (se 1 (by rfl) ⟨2754959, by rfl⟩ : syracuseStep 3673279 = 5509919) B5509919
theorem B4897705 : Blo 1933435 4897705 := bstep (se 2 (by rfl) ⟨1836639, by rfl⟩ : syracuseStep 4897705 = 3673279) B3673279
theorem B6530273 : Blo 1933435 6530273 := bstep (se 2 (by rfl) ⟨2448852, by rfl⟩ : syracuseStep 6530273 = 4897705) B4897705
theorem B4353515 : Blo 1933435 4353515 := bstep (se 1 (by rfl) ⟨3265136, by rfl⟩ : syracuseStep 4353515 = 6530273) B6530273
theorem B2902343 : Blo 1933435 2902343 := bstep (se 1 (by rfl) ⟨2176757, by rfl⟩ : syracuseStep 2902343 = 4353515) B4353515
theorem B1934895 : Blo 1933435 1934895 := bstep (se 1 (by rfl) ⟨1451171, by rfl⟩ : syracuseStep 1934895 = 2902343) B2902343
theorem B2902349 : Blo 1933435 2902349 := bbase (se 3 (by rfl) ⟨544190, by rfl⟩ : syracuseStep 2902349 = 1088381) (by norm_num)
theorem B1934899 : Blo 1933435 1934899 := bstep (se 1 (by rfl) ⟨1451174, by rfl⟩ : syracuseStep 1934899 = 2902349) B2902349
theorem B4353533 : Blo 1933435 4353533 := bbase (se 3 (by rfl) ⟨816287, by rfl⟩ : syracuseStep 4353533 = 1632575) (by norm_num)
theorem B2902355 : Blo 1933435 2902355 := bstep (se 1 (by rfl) ⟨2176766, by rfl⟩ : syracuseStep 2902355 = 4353533) B4353533
theorem B1934903 : Blo 1933435 1934903 := bstep (se 1 (by rfl) ⟨1451177, by rfl⟩ : syracuseStep 1934903 = 2902355) B2902355
theorem B3265157 : Blo 1933435 3265157 := bbase (se 4 (by rfl) ⟨306108, by rfl⟩ : syracuseStep 3265157 = 612217) (by norm_num)
theorem B2176771 : Blo 1933435 2176771 := bstep (se 1 (by rfl) ⟨1632578, by rfl⟩ : syracuseStep 2176771 = 3265157) B3265157
theorem B2902361 : Blo 1933435 2902361 := bstep (se 2 (by rfl) ⟨1088385, by rfl⟩ : syracuseStep 2902361 = 2176771) B2176771
theorem B1934907 : Blo 1933435 1934907 := bstep (se 1 (by rfl) ⟨1451180, by rfl⟩ : syracuseStep 1934907 = 2902361) B2902361
theorem B14693237 : Blo 1933435 14693237 := bbase (se 5 (by rfl) ⟨688745, by rfl⟩ : syracuseStep 14693237 = 1377491) (by norm_num)
theorem B9795491 : Blo 1933435 9795491 := bstep (se 1 (by rfl) ⟨7346618, by rfl⟩ : syracuseStep 9795491 = 14693237) B14693237
theorem B6530327 : Blo 1933435 6530327 := bstep (se 1 (by rfl) ⟨4897745, by rfl⟩ : syracuseStep 6530327 = 9795491) B9795491
theorem B4353551 : Blo 1933435 4353551 := bstep (se 1 (by rfl) ⟨3265163, by rfl⟩ : syracuseStep 4353551 = 6530327) B6530327
theorem B2902367 : Blo 1933435 2902367 := bstep (se 1 (by rfl) ⟨2176775, by rfl⟩ : syracuseStep 2902367 = 4353551) B4353551
theorem B1934911 : Blo 1933435 1934911 := bstep (se 1 (by rfl) ⟨1451183, by rfl⟩ : syracuseStep 1934911 = 2902367) B2902367
theorem B2902373 : Blo 1933435 2902373 := bbase (se 4 (by rfl) ⟨272097, by rfl⟩ : syracuseStep 2902373 = 544195) (by norm_num)
theorem B1934915 : Blo 1933435 1934915 := bstep (se 1 (by rfl) ⟨1451186, by rfl⟩ : syracuseStep 1934915 = 2902373) B2902373
theorem B3673325 : Blo 1933435 3673325 := bbase (se 3 (by rfl) ⟨688748, by rfl⟩ : syracuseStep 3673325 = 1377497) (by norm_num)
theorem B2448883 : Blo 1933435 2448883 := bstep (se 1 (by rfl) ⟨1836662, by rfl⟩ : syracuseStep 2448883 = 3673325) B3673325
theorem B3265177 : Blo 1933435 3265177 := bstep (se 2 (by rfl) ⟨1224441, by rfl⟩ : syracuseStep 3265177 = 2448883) B2448883
theorem B4353569 : Blo 1933435 4353569 := bstep (se 2 (by rfl) ⟨1632588, by rfl⟩ : syracuseStep 4353569 = 3265177) B3265177
theorem B2902379 : Blo 1933435 2902379 := bstep (se 1 (by rfl) ⟨2176784, by rfl⟩ : syracuseStep 2902379 = 4353569) B4353569
theorem B1934919 : Blo 1933435 1934919 := bstep (se 1 (by rfl) ⟨1451189, by rfl⟩ : syracuseStep 1934919 = 2902379) B2902379
theorem B2176789 : Blo 1933435 2176789 := bbase (se 6 (by rfl) ⟨51018, by rfl⟩ : syracuseStep 2176789 = 102037) (by norm_num)
theorem B2902385 : Blo 1933435 2902385 := bstep (se 2 (by rfl) ⟨1088394, by rfl⟩ : syracuseStep 2902385 = 2176789) B2176789
theorem B1934923 : Blo 1933435 1934923 := bstep (se 1 (by rfl) ⟨1451192, by rfl⟩ : syracuseStep 1934923 = 2902385) B2902385
theorem B2448893 : Blo 1933435 2448893 := bbase (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) (by norm_num)
theorem B6530381 : Blo 1933435 6530381 := bstep (se 3 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 6530381 = 2448893) B2448893
theorem B4353587 : Blo 1933435 4353587 := bstep (se 1 (by rfl) ⟨3265190, by rfl⟩ : syracuseStep 4353587 = 6530381) B6530381
theorem B2902391 : Blo 1933435 2902391 := bstep (se 1 (by rfl) ⟨2176793, by rfl⟩ : syracuseStep 2902391 = 4353587) B4353587
theorem B1934927 : Blo 1933435 1934927 := bstep (se 1 (by rfl) ⟨1451195, by rfl⟩ : syracuseStep 1934927 = 2902391) B2902391
theorem B2902397 : Blo 1933435 2902397 := bbase (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) (by norm_num)
theorem B1934931 : Blo 1933435 1934931 := bstep (se 1 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 1934931 = 2902397) B2902397
theorem B4353605 : Blo 1933435 4353605 := bbase (se 4 (by rfl) ⟨408150, by rfl⟩ : syracuseStep 4353605 = 816301) (by norm_num)
theorem B2902403 : Blo 1933435 2902403 := bstep (se 1 (by rfl) ⟨2176802, by rfl⟩ : syracuseStep 2902403 = 4353605) B4353605
theorem B1934935 : Blo 1933435 1934935 := bstep (se 1 (by rfl) ⟨1451201, by rfl⟩ : syracuseStep 1934935 = 2902403) B2902403
theorem B4964645 : Blo 1933435 4964645 := bbase (se 4 (by rfl) ⟨465435, by rfl⟩ : syracuseStep 4964645 = 930871) (by norm_num)
theorem B3309763 : Blo 1933435 3309763 := bstep (se 1 (by rfl) ⟨2482322, by rfl⟩ : syracuseStep 3309763 = 4964645) B4964645
theorem B4413017 : Blo 1933435 4413017 := bstep (se 2 (by rfl) ⟨1654881, by rfl⟩ : syracuseStep 4413017 = 3309763) B3309763
theorem B2942011 : Blo 1933435 2942011 := bstep (se 1 (by rfl) ⟨2206508, by rfl⟩ : syracuseStep 2942011 = 4413017) B4413017
theorem B3922681 : Blo 1933435 3922681 := bstep (se 2 (by rfl) ⟨1471005, by rfl⟩ : syracuseStep 3922681 = 2942011) B2942011
theorem B5230241 : Blo 1933435 5230241 := bstep (se 2 (by rfl) ⟨1961340, by rfl⟩ : syracuseStep 5230241 = 3922681) B3922681
theorem B3486827 : Blo 1933435 3486827 := bstep (se 1 (by rfl) ⟨2615120, by rfl⟩ : syracuseStep 3486827 = 5230241) B5230241
theorem B2324551 : Blo 1933435 2324551 := bstep (se 1 (by rfl) ⟨1743413, by rfl⟩ : syracuseStep 2324551 = 3486827) B3486827
theorem B3099401 : Blo 1933435 3099401 := bstep (se 2 (by rfl) ⟨1162275, by rfl⟩ : syracuseStep 3099401 = 2324551) B2324551
theorem B2066267 : Blo 1933435 2066267 := bstep (se 1 (by rfl) ⟨1549700, by rfl⟩ : syracuseStep 2066267 = 3099401) B3099401
theorem B5510045 : Blo 1933435 5510045 := bstep (se 3 (by rfl) ⟨1033133, by rfl⟩ : syracuseStep 5510045 = 2066267) B2066267
theorem B3673363 : Blo 1933435 3673363 := bstep (se 1 (by rfl) ⟨2755022, by rfl⟩ : syracuseStep 3673363 = 5510045) B5510045
theorem B4897817 : Blo 1933435 4897817 := bstep (se 2 (by rfl) ⟨1836681, by rfl⟩ : syracuseStep 4897817 = 3673363) B3673363
theorem B3265211 : Blo 1933435 3265211 := bstep (se 1 (by rfl) ⟨2448908, by rfl⟩ : syracuseStep 3265211 = 4897817) B4897817
theorem B2176807 : Blo 1933435 2176807 := bstep (se 1 (by rfl) ⟨1632605, by rfl⟩ : syracuseStep 2176807 = 3265211) B3265211
theorem B2902409 : Blo 1933435 2902409 := bstep (se 2 (by rfl) ⟨1088403, by rfl⟩ : syracuseStep 2902409 = 2176807) B2176807
theorem B1934939 : Blo 1933435 1934939 := bstep (se 1 (by rfl) ⟨1451204, by rfl⟩ : syracuseStep 1934939 = 2902409) B2902409
theorem B9795653 : Blo 1933435 9795653 := bbase (se 4 (by rfl) ⟨918342, by rfl⟩ : syracuseStep 9795653 = 1836685) (by norm_num)
theorem B6530435 : Blo 1933435 6530435 := bstep (se 1 (by rfl) ⟨4897826, by rfl⟩ : syracuseStep 6530435 = 9795653) B9795653
theorem B4353623 : Blo 1933435 4353623 := bstep (se 1 (by rfl) ⟨3265217, by rfl⟩ : syracuseStep 4353623 = 6530435) B6530435
theorem B2902415 : Blo 1933435 2902415 := bstep (se 1 (by rfl) ⟨2176811, by rfl⟩ : syracuseStep 2902415 = 4353623) B4353623
theorem B1934943 : Blo 1933435 1934943 := bstep (se 1 (by rfl) ⟨1451207, by rfl⟩ : syracuseStep 1934943 = 2902415) B2902415
theorem B2902421 : Blo 1933435 2902421 := bbase (se 6 (by rfl) ⟨68025, by rfl⟩ : syracuseStep 2902421 = 136051) (by norm_num)
theorem B1934947 : Blo 1933435 1934947 := bstep (se 1 (by rfl) ⟨1451210, by rfl⟩ : syracuseStep 1934947 = 2902421) B2902421
theorem B28661141 : Blo 1933435 28661141 := bbase (se 6 (by rfl) ⟨671745, by rfl⟩ : syracuseStep 28661141 = 1343491) (by norm_num)
theorem B19107427 : Blo 1933435 19107427 := bstep (se 1 (by rfl) ⟨14330570, by rfl⟩ : syracuseStep 19107427 = 28661141) B28661141
theorem B25476569 : Blo 1933435 25476569 := bstep (se 2 (by rfl) ⟨9553713, by rfl⟩ : syracuseStep 25476569 = 19107427) B19107427
theorem B16984379 : Blo 1933435 16984379 := bstep (se 1 (by rfl) ⟨12738284, by rfl⟩ : syracuseStep 16984379 = 25476569) B25476569
theorem B11322919 : Blo 1933435 11322919 := bstep (se 1 (by rfl) ⟨8492189, by rfl⟩ : syracuseStep 11322919 = 16984379) B16984379
theorem B15097225 : Blo 1933435 15097225 := bstep (se 2 (by rfl) ⟨5661459, by rfl⟩ : syracuseStep 15097225 = 11322919) B11322919
theorem B20129633 : Blo 1933435 20129633 := bstep (se 2 (by rfl) ⟨7548612, by rfl⟩ : syracuseStep 20129633 = 15097225) B15097225
theorem B13419755 : Blo 1933435 13419755 := bstep (se 1 (by rfl) ⟨10064816, by rfl⟩ : syracuseStep 13419755 = 20129633) B20129633
theorem B8946503 : Blo 1933435 8946503 := bstep (se 1 (by rfl) ⟨6709877, by rfl⟩ : syracuseStep 8946503 = 13419755) B13419755
theorem B5964335 : Blo 1933435 5964335 := bstep (se 1 (by rfl) ⟨4473251, by rfl⟩ : syracuseStep 5964335 = 8946503) B8946503
theorem B3976223 : Blo 1933435 3976223 := bstep (se 1 (by rfl) ⟨2982167, by rfl⟩ : syracuseStep 3976223 = 5964335) B5964335
theorem B10603261 : Blo 1933435 10603261 := bstep (se 3 (by rfl) ⟨1988111, by rfl⟩ : syracuseStep 10603261 = 3976223) B3976223
theorem B14137681 : Blo 1933435 14137681 := bstep (se 2 (by rfl) ⟨5301630, by rfl⟩ : syracuseStep 14137681 = 10603261) B10603261
theorem B18850241 : Blo 1933435 18850241 := bstep (se 2 (by rfl) ⟨7068840, by rfl⟩ : syracuseStep 18850241 = 14137681) B14137681
theorem B12566827 : Blo 1933435 12566827 := bstep (se 1 (by rfl) ⟨9425120, by rfl⟩ : syracuseStep 12566827 = 18850241) B18850241
theorem B16755769 : Blo 1933435 16755769 := bstep (se 2 (by rfl) ⟨6283413, by rfl⟩ : syracuseStep 16755769 = 12566827) B12566827
theorem B22341025 : Blo 1933435 22341025 := bstep (se 2 (by rfl) ⟨8377884, by rfl⟩ : syracuseStep 22341025 = 16755769) B16755769
theorem B29788033 : Blo 1933435 29788033 := bstep (se 2 (by rfl) ⟨11170512, by rfl⟩ : syracuseStep 29788033 = 22341025) B22341025
theorem B39717377 : Blo 1933435 39717377 := bstep (se 2 (by rfl) ⟨14894016, by rfl⟩ : syracuseStep 39717377 = 29788033) B29788033
theorem B26478251 : Blo 1933435 26478251 := bstep (se 1 (by rfl) ⟨19858688, by rfl⟩ : syracuseStep 26478251 = 39717377) B39717377
theorem B17652167 : Blo 1933435 17652167 := bstep (se 1 (by rfl) ⟨13239125, by rfl⟩ : syracuseStep 17652167 = 26478251) B26478251
theorem B11768111 : Blo 1933435 11768111 := bstep (se 1 (by rfl) ⟨8826083, by rfl⟩ : syracuseStep 11768111 = 17652167) B17652167
theorem B7845407 : Blo 1933435 7845407 := bstep (se 1 (by rfl) ⟨5884055, by rfl⟩ : syracuseStep 7845407 = 11768111) B11768111
theorem B5230271 : Blo 1933435 5230271 := bstep (se 1 (by rfl) ⟨3922703, by rfl⟩ : syracuseStep 5230271 = 7845407) B7845407
theorem B13947389 : Blo 1933435 13947389 := bstep (se 3 (by rfl) ⟨2615135, by rfl⟩ : syracuseStep 13947389 = 5230271) B5230271
theorem B9298259 : Blo 1933435 9298259 := bstep (se 1 (by rfl) ⟨6973694, by rfl⟩ : syracuseStep 9298259 = 13947389) B13947389
theorem B6198839 : Blo 1933435 6198839 := bstep (se 1 (by rfl) ⟨4649129, by rfl⟩ : syracuseStep 6198839 = 9298259) B9298259
theorem B4132559 : Blo 1933435 4132559 := bstep (se 1 (by rfl) ⟨3099419, by rfl⟩ : syracuseStep 4132559 = 6198839) B6198839
theorem B11020157 : Blo 1933435 11020157 := bstep (se 3 (by rfl) ⟨2066279, by rfl⟩ : syracuseStep 11020157 = 4132559) B4132559
theorem B7346771 : Blo 1933435 7346771 := bstep (se 1 (by rfl) ⟨5510078, by rfl⟩ : syracuseStep 7346771 = 11020157) B11020157
theorem B4897847 : Blo 1933435 4897847 := bstep (se 1 (by rfl) ⟨3673385, by rfl⟩ : syracuseStep 4897847 = 7346771) B7346771
theorem B3265231 : Blo 1933435 3265231 := bstep (se 1 (by rfl) ⟨2448923, by rfl⟩ : syracuseStep 3265231 = 4897847) B4897847
theorem B4353641 : Blo 1933435 4353641 := bstep (se 2 (by rfl) ⟨1632615, by rfl⟩ : syracuseStep 4353641 = 3265231) B3265231
theorem B2902427 : Blo 1933435 2902427 := bstep (se 1 (by rfl) ⟨2176820, by rfl⟩ : syracuseStep 2902427 = 4353641) B4353641
theorem B1934951 : Blo 1933435 1934951 := bstep (se 1 (by rfl) ⟨1451213, by rfl⟩ : syracuseStep 1934951 = 2902427) B2902427
theorem B2176825 : Blo 1933435 2176825 := bbase (se 2 (by rfl) ⟨816309, by rfl⟩ : syracuseStep 2176825 = 1632619) (by norm_num)
theorem B2902433 : Blo 1933435 2902433 := bstep (se 2 (by rfl) ⟨1088412, by rfl⟩ : syracuseStep 2902433 = 2176825) B2176825
theorem B1934955 : Blo 1933435 1934955 := bstep (se 1 (by rfl) ⟨1451216, by rfl⟩ : syracuseStep 1934955 = 2902433) B2902433
theorem B5510101 : Blo 1933435 5510101 := bbase (se 7 (by rfl) ⟨64571, by rfl⟩ : syracuseStep 5510101 = 129143) (by norm_num)
theorem B7346801 : Blo 1933435 7346801 := bstep (se 2 (by rfl) ⟨2755050, by rfl⟩ : syracuseStep 7346801 = 5510101) B5510101
theorem B4897867 : Blo 1933435 4897867 := bstep (se 1 (by rfl) ⟨3673400, by rfl⟩ : syracuseStep 4897867 = 7346801) B7346801
theorem B6530489 : Blo 1933435 6530489 := bstep (se 2 (by rfl) ⟨2448933, by rfl⟩ : syracuseStep 6530489 = 4897867) B4897867
theorem B4353659 : Blo 1933435 4353659 := bstep (se 1 (by rfl) ⟨3265244, by rfl⟩ : syracuseStep 4353659 = 6530489) B6530489
theorem B2902439 : Blo 1933435 2902439 := bstep (se 1 (by rfl) ⟨2176829, by rfl⟩ : syracuseStep 2902439 = 4353659) B4353659
theorem B1934959 : Blo 1933435 1934959 := bstep (se 1 (by rfl) ⟨1451219, by rfl⟩ : syracuseStep 1934959 = 2902439) B2902439
theorem B2902445 : Blo 1933435 2902445 := bbase (se 3 (by rfl) ⟨544208, by rfl⟩ : syracuseStep 2902445 = 1088417) (by norm_num)
theorem B1934963 : Blo 1933435 1934963 := bstep (se 1 (by rfl) ⟨1451222, by rfl⟩ : syracuseStep 1934963 = 2902445) B2902445
theorem B4353677 : Blo 1933435 4353677 := bbase (se 3 (by rfl) ⟨816314, by rfl⟩ : syracuseStep 4353677 = 1632629) (by norm_num)
theorem B2902451 : Blo 1933435 2902451 := bstep (se 1 (by rfl) ⟨2176838, by rfl⟩ : syracuseStep 2902451 = 4353677) B4353677
theorem B1934967 : Blo 1933435 1934967 := bstep (se 1 (by rfl) ⟨1451225, by rfl⟩ : syracuseStep 1934967 = 2902451) B2902451
theorem B2448949 : Blo 1933435 2448949 := bbase (se 5 (by rfl) ⟨114794, by rfl⟩ : syracuseStep 2448949 = 229589) (by norm_num)
theorem B3265265 : Blo 1933435 3265265 := bstep (se 2 (by rfl) ⟨1224474, by rfl⟩ : syracuseStep 3265265 = 2448949) B2448949
theorem B2176843 : Blo 1933435 2176843 := bstep (se 1 (by rfl) ⟨1632632, by rfl⟩ : syracuseStep 2176843 = 3265265) B3265265
theorem B2902457 : Blo 1933435 2902457 := bstep (se 2 (by rfl) ⟨1088421, by rfl⟩ : syracuseStep 2902457 = 2176843) B2176843
theorem B1934971 : Blo 1933435 1934971 := bstep (se 1 (by rfl) ⟨1451228, by rfl⟩ : syracuseStep 1934971 = 2902457) B2902457
theorem B2356309 : Blo 1933435 2356309 := bbase (se 8 (by rfl) ⟨13806, by rfl⟩ : syracuseStep 2356309 = 27613) (by norm_num)
theorem B12566981 : Blo 1933435 12566981 := bstep (se 4 (by rfl) ⟨1178154, by rfl⟩ : syracuseStep 12566981 = 2356309) B2356309
theorem B8377987 : Blo 1933435 8377987 := bstep (se 1 (by rfl) ⟨6283490, by rfl⟩ : syracuseStep 8377987 = 12566981) B12566981
theorem B11170649 : Blo 1933435 11170649 := bstep (se 2 (by rfl) ⟨4188993, by rfl⟩ : syracuseStep 11170649 = 8377987) B8377987
theorem B29788397 : Blo 1933435 29788397 := bstep (se 3 (by rfl) ⟨5585324, by rfl⟩ : syracuseStep 29788397 = 11170649) B11170649
theorem B19858931 : Blo 1933435 19858931 := bstep (se 1 (by rfl) ⟨14894198, by rfl⟩ : syracuseStep 19858931 = 29788397) B29788397
theorem B13239287 : Blo 1933435 13239287 := bstep (se 1 (by rfl) ⟨9929465, by rfl⟩ : syracuseStep 13239287 = 19858931) B19858931
theorem B8826191 : Blo 1933435 8826191 := bstep (se 1 (by rfl) ⟨6619643, by rfl⟩ : syracuseStep 8826191 = 13239287) B13239287
theorem B5884127 : Blo 1933435 5884127 := bstep (se 1 (by rfl) ⟨4413095, by rfl⟩ : syracuseStep 5884127 = 8826191) B8826191
theorem B3922751 : Blo 1933435 3922751 := bstep (se 1 (by rfl) ⟨2942063, by rfl⟩ : syracuseStep 3922751 = 5884127) B5884127
theorem B10460669 : Blo 1933435 10460669 := bstep (se 3 (by rfl) ⟨1961375, by rfl⟩ : syracuseStep 10460669 = 3922751) B3922751
theorem B27895117 : Blo 1933435 27895117 := bstep (se 3 (by rfl) ⟨5230334, by rfl⟩ : syracuseStep 27895117 = 10460669) B10460669
theorem B37193489 : Blo 1933435 37193489 := bstep (se 2 (by rfl) ⟨13947558, by rfl⟩ : syracuseStep 37193489 = 27895117) B27895117
theorem B24795659 : Blo 1933435 24795659 := bstep (se 1 (by rfl) ⟨18596744, by rfl⟩ : syracuseStep 24795659 = 37193489) B37193489
theorem B16530439 : Blo 1933435 16530439 := bstep (se 1 (by rfl) ⟨12397829, by rfl⟩ : syracuseStep 16530439 = 24795659) B24795659
theorem B22040585 : Blo 1933435 22040585 := bstep (se 2 (by rfl) ⟨8265219, by rfl⟩ : syracuseStep 22040585 = 16530439) B16530439
theorem B14693723 : Blo 1933435 14693723 := bstep (se 1 (by rfl) ⟨11020292, by rfl⟩ : syracuseStep 14693723 = 22040585) B22040585
theorem B9795815 : Blo 1933435 9795815 := bstep (se 1 (by rfl) ⟨7346861, by rfl⟩ : syracuseStep 9795815 = 14693723) B14693723
theorem B6530543 : Blo 1933435 6530543 := bstep (se 1 (by rfl) ⟨4897907, by rfl⟩ : syracuseStep 6530543 = 9795815) B9795815
theorem B4353695 : Blo 1933435 4353695 := bstep (se 1 (by rfl) ⟨3265271, by rfl⟩ : syracuseStep 4353695 = 6530543) B6530543
theorem B2902463 : Blo 1933435 2902463 := bstep (se 1 (by rfl) ⟨2176847, by rfl⟩ : syracuseStep 2902463 = 4353695) B4353695
theorem B1934975 : Blo 1933435 1934975 := bstep (se 1 (by rfl) ⟨1451231, by rfl⟩ : syracuseStep 1934975 = 2902463) B2902463
theorem B2902469 : Blo 1933435 2902469 := bbase (se 4 (by rfl) ⟨272106, by rfl⟩ : syracuseStep 2902469 = 544213) (by norm_num)
theorem B1934979 : Blo 1933435 1934979 := bstep (se 1 (by rfl) ⟨1451234, by rfl⟩ : syracuseStep 1934979 = 2902469) B2902469
theorem B3265285 : Blo 1933435 3265285 := bbase (se 4 (by rfl) ⟨306120, by rfl⟩ : syracuseStep 3265285 = 612241) (by norm_num)
theorem B4353713 : Blo 1933435 4353713 := bstep (se 2 (by rfl) ⟨1632642, by rfl⟩ : syracuseStep 4353713 = 3265285) B3265285
theorem B2902475 : Blo 1933435 2902475 := bstep (se 1 (by rfl) ⟨2176856, by rfl⟩ : syracuseStep 2902475 = 4353713) B4353713
theorem B1934983 : Blo 1933435 1934983 := bstep (se 1 (by rfl) ⟨1451237, by rfl⟩ : syracuseStep 1934983 = 2902475) B2902475
theorem B2176861 : Blo 1933435 2176861 := bbase (se 3 (by rfl) ⟨408161, by rfl⟩ : syracuseStep 2176861 = 816323) (by norm_num)
theorem B2902481 : Blo 1933435 2902481 := bstep (se 2 (by rfl) ⟨1088430, by rfl⟩ : syracuseStep 2902481 = 2176861) B2176861
theorem B1934987 : Blo 1933435 1934987 := bstep (se 1 (by rfl) ⟨1451240, by rfl⟩ : syracuseStep 1934987 = 2902481) B2902481
theorem B6530597 : Blo 1933435 6530597 := bbase (se 4 (by rfl) ⟨612243, by rfl⟩ : syracuseStep 6530597 = 1224487) (by norm_num)
theorem B4353731 : Blo 1933435 4353731 := bstep (se 1 (by rfl) ⟨3265298, by rfl⟩ : syracuseStep 4353731 = 6530597) B6530597
theorem B2902487 : Blo 1933435 2902487 := bstep (se 1 (by rfl) ⟨2176865, by rfl⟩ : syracuseStep 2902487 = 4353731) B4353731
theorem B1934991 : Blo 1933435 1934991 := bstep (se 1 (by rfl) ⟨1451243, by rfl⟩ : syracuseStep 1934991 = 2902487) B2902487
theorem B2902493 : Blo 1933435 2902493 := bbase (se 3 (by rfl) ⟨544217, by rfl⟩ : syracuseStep 2902493 = 1088435) (by norm_num)
theorem B1934995 : Blo 1933435 1934995 := bstep (se 1 (by rfl) ⟨1451246, by rfl⟩ : syracuseStep 1934995 = 2902493) B2902493
theorem B4353749 : Blo 1933435 4353749 := bbase (se 7 (by rfl) ⟨51020, by rfl⟩ : syracuseStep 4353749 = 102041) (by norm_num)
theorem B2902499 : Blo 1933435 2902499 := bstep (se 1 (by rfl) ⟨2176874, by rfl⟩ : syracuseStep 2902499 = 4353749) B4353749
theorem B1934999 : Blo 1933435 1934999 := bstep (se 1 (by rfl) ⟨1451249, by rfl⟩ : syracuseStep 1934999 = 2902499) B2902499
theorem B3534517 : Blo 1933435 3534517 := bbase (se 5 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 3534517 = 331361) (by norm_num)
theorem B4712689 : Blo 1933435 4712689 := bstep (se 2 (by rfl) ⟨1767258, by rfl⟩ : syracuseStep 4712689 = 3534517) B3534517
theorem B6283585 : Blo 1933435 6283585 := bstep (se 2 (by rfl) ⟨2356344, by rfl⟩ : syracuseStep 6283585 = 4712689) B4712689
theorem B8378113 : Blo 1933435 8378113 := bstep (se 2 (by rfl) ⟨3141792, by rfl⟩ : syracuseStep 8378113 = 6283585) B6283585
theorem B11170817 : Blo 1933435 11170817 := bstep (se 2 (by rfl) ⟨4189056, by rfl⟩ : syracuseStep 11170817 = 8378113) B8378113
theorem B7447211 : Blo 1933435 7447211 := bstep (se 1 (by rfl) ⟨5585408, by rfl⟩ : syracuseStep 7447211 = 11170817) B11170817
theorem B4964807 : Blo 1933435 4964807 := bstep (se 1 (by rfl) ⟨3723605, by rfl⟩ : syracuseStep 4964807 = 7447211) B7447211
theorem B3309871 : Blo 1933435 3309871 := bstep (se 1 (by rfl) ⟨2482403, by rfl⟩ : syracuseStep 3309871 = 4964807) B4964807
theorem B4413161 : Blo 1933435 4413161 := bstep (se 2 (by rfl) ⟨1654935, by rfl⟩ : syracuseStep 4413161 = 3309871) B3309871
theorem B11768429 : Blo 1933435 11768429 := bstep (se 3 (by rfl) ⟨2206580, by rfl⟩ : syracuseStep 11768429 = 4413161) B4413161
theorem B7845619 : Blo 1933435 7845619 := bstep (se 1 (by rfl) ⟨5884214, by rfl⟩ : syracuseStep 7845619 = 11768429) B11768429
theorem B10460825 : Blo 1933435 10460825 := bstep (se 2 (by rfl) ⟨3922809, by rfl⟩ : syracuseStep 10460825 = 7845619) B7845619
theorem B6973883 : Blo 1933435 6973883 := bstep (se 1 (by rfl) ⟨5230412, by rfl⟩ : syracuseStep 6973883 = 10460825) B10460825
theorem B4649255 : Blo 1933435 4649255 := bstep (se 1 (by rfl) ⟨3486941, by rfl⟩ : syracuseStep 4649255 = 6973883) B6973883
theorem B3099503 : Blo 1933435 3099503 := bstep (se 1 (by rfl) ⟨2324627, by rfl⟩ : syracuseStep 3099503 = 4649255) B4649255
theorem B8265341 : Blo 1933435 8265341 := bstep (se 3 (by rfl) ⟨1549751, by rfl⟩ : syracuseStep 8265341 = 3099503) B3099503
theorem B5510227 : Blo 1933435 5510227 := bstep (se 1 (by rfl) ⟨4132670, by rfl⟩ : syracuseStep 5510227 = 8265341) B8265341
theorem B7346969 : Blo 1933435 7346969 := bstep (se 2 (by rfl) ⟨2755113, by rfl⟩ : syracuseStep 7346969 = 5510227) B5510227
theorem B4897979 : Blo 1933435 4897979 := bstep (se 1 (by rfl) ⟨3673484, by rfl⟩ : syracuseStep 4897979 = 7346969) B7346969
theorem B3265319 : Blo 1933435 3265319 := bstep (se 1 (by rfl) ⟨2448989, by rfl⟩ : syracuseStep 3265319 = 4897979) B4897979
theorem B2176879 : Blo 1933435 2176879 := bstep (se 1 (by rfl) ⟨1632659, by rfl⟩ : syracuseStep 2176879 = 3265319) B3265319
theorem B2902505 : Blo 1933435 2902505 := bstep (se 2 (by rfl) ⟨1088439, by rfl⟩ : syracuseStep 2902505 = 2176879) B2176879
theorem B1935003 : Blo 1933435 1935003 := bstep (se 1 (by rfl) ⟨1451252, by rfl⟩ : syracuseStep 1935003 = 2902505) B2902505
theorem B7069045 : Blo 1933435 7069045 := bbase (se 5 (by rfl) ⟨331361, by rfl⟩ : syracuseStep 7069045 = 662723) (by norm_num)
theorem B9425393 : Blo 1933435 9425393 := bstep (se 2 (by rfl) ⟨3534522, by rfl⟩ : syracuseStep 9425393 = 7069045) B7069045
theorem B6283595 : Blo 1933435 6283595 := bstep (se 1 (by rfl) ⟨4712696, by rfl⟩ : syracuseStep 6283595 = 9425393) B9425393
theorem B16756253 : Blo 1933435 16756253 := bstep (se 3 (by rfl) ⟨3141797, by rfl⟩ : syracuseStep 16756253 = 6283595) B6283595
theorem B11170835 : Blo 1933435 11170835 := bstep (se 1 (by rfl) ⟨8378126, by rfl⟩ : syracuseStep 11170835 = 16756253) B16756253
theorem B7447223 : Blo 1933435 7447223 := bstep (se 1 (by rfl) ⟨5585417, by rfl⟩ : syracuseStep 7447223 = 11170835) B11170835
theorem B4964815 : Blo 1933435 4964815 := bstep (se 1 (by rfl) ⟨3723611, by rfl⟩ : syracuseStep 4964815 = 7447223) B7447223
theorem B6619753 : Blo 1933435 6619753 := bstep (se 2 (by rfl) ⟨2482407, by rfl⟩ : syracuseStep 6619753 = 4964815) B4964815
theorem B8826337 : Blo 1933435 8826337 := bstep (se 2 (by rfl) ⟨3309876, by rfl⟩ : syracuseStep 8826337 = 6619753) B6619753
theorem B11768449 : Blo 1933435 11768449 := bstep (se 2 (by rfl) ⟨4413168, by rfl⟩ : syracuseStep 11768449 = 8826337) B8826337
theorem B15691265 : Blo 1933435 15691265 := bstep (se 2 (by rfl) ⟨5884224, by rfl⟩ : syracuseStep 15691265 = 11768449) B11768449
theorem B10460843 : Blo 1933435 10460843 := bstep (se 1 (by rfl) ⟨7845632, by rfl⟩ : syracuseStep 10460843 = 15691265) B15691265
theorem B6973895 : Blo 1933435 6973895 := bstep (se 1 (by rfl) ⟨5230421, by rfl⟩ : syracuseStep 6973895 = 10460843) B10460843
theorem B18597053 : Blo 1933435 18597053 := bstep (se 3 (by rfl) ⟨3486947, by rfl⟩ : syracuseStep 18597053 = 6973895) B6973895
theorem B12398035 : Blo 1933435 12398035 := bstep (se 1 (by rfl) ⟨9298526, by rfl⟩ : syracuseStep 12398035 = 18597053) B18597053
theorem B16530713 : Blo 1933435 16530713 := bstep (se 2 (by rfl) ⟨6199017, by rfl⟩ : syracuseStep 16530713 = 12398035) B12398035
theorem B11020475 : Blo 1933435 11020475 := bstep (se 1 (by rfl) ⟨8265356, by rfl⟩ : syracuseStep 11020475 = 16530713) B16530713
theorem B7346983 : Blo 1933435 7346983 := bstep (se 1 (by rfl) ⟨5510237, by rfl⟩ : syracuseStep 7346983 = 11020475) B11020475
theorem B9795977 : Blo 1933435 9795977 := bstep (se 2 (by rfl) ⟨3673491, by rfl⟩ : syracuseStep 9795977 = 7346983) B7346983
theorem B6530651 : Blo 1933435 6530651 := bstep (se 1 (by rfl) ⟨4897988, by rfl⟩ : syracuseStep 6530651 = 9795977) B9795977
theorem B4353767 : Blo 1933435 4353767 := bstep (se 1 (by rfl) ⟨3265325, by rfl⟩ : syracuseStep 4353767 = 6530651) B6530651
theorem B2902511 : Blo 1933435 2902511 := bstep (se 1 (by rfl) ⟨2176883, by rfl⟩ : syracuseStep 2902511 = 4353767) B4353767
theorem B1935007 : Blo 1933435 1935007 := bstep (se 1 (by rfl) ⟨1451255, by rfl⟩ : syracuseStep 1935007 = 2902511) B2902511
theorem B2902517 : Blo 1933435 2902517 := bbase (se 5 (by rfl) ⟨136055, by rfl⟩ : syracuseStep 2902517 = 272111) (by norm_num)
theorem B1935011 : Blo 1933435 1935011 := bstep (se 1 (by rfl) ⟨1451258, by rfl⟩ : syracuseStep 1935011 = 2902517) B2902517
theorem B5510261 : Blo 1933435 5510261 := bbase (se 5 (by rfl) ⟨258293, by rfl⟩ : syracuseStep 5510261 = 516587) (by norm_num)
theorem B3673507 : Blo 1933435 3673507 := bstep (se 1 (by rfl) ⟨2755130, by rfl⟩ : syracuseStep 3673507 = 5510261) B5510261
theorem B4898009 : Blo 1933435 4898009 := bstep (se 2 (by rfl) ⟨1836753, by rfl⟩ : syracuseStep 4898009 = 3673507) B3673507
theorem B3265339 : Blo 1933435 3265339 := bstep (se 1 (by rfl) ⟨2449004, by rfl⟩ : syracuseStep 3265339 = 4898009) B4898009
theorem B4353785 : Blo 1933435 4353785 := bstep (se 2 (by rfl) ⟨1632669, by rfl⟩ : syracuseStep 4353785 = 3265339) B3265339
theorem B2902523 : Blo 1933435 2902523 := bstep (se 1 (by rfl) ⟨2176892, by rfl⟩ : syracuseStep 2902523 = 4353785) B4353785
theorem B1935015 : Blo 1933435 1935015 := bstep (se 1 (by rfl) ⟨1451261, by rfl⟩ : syracuseStep 1935015 = 2902523) B2902523
theorem B2176897 : Blo 1933435 2176897 := bbase (se 2 (by rfl) ⟨816336, by rfl⟩ : syracuseStep 2176897 = 1632673) (by norm_num)
theorem B2902529 : Blo 1933435 2902529 := bstep (se 2 (by rfl) ⟨1088448, by rfl⟩ : syracuseStep 2902529 = 2176897) B2176897
theorem B1935019 : Blo 1933435 1935019 := bstep (se 1 (by rfl) ⟨1451264, by rfl⟩ : syracuseStep 1935019 = 2902529) B2902529
theorem B4898029 : Blo 1933435 4898029 := bbase (se 3 (by rfl) ⟨918380, by rfl⟩ : syracuseStep 4898029 = 1836761) (by norm_num)
theorem B6530705 : Blo 1933435 6530705 := bstep (se 2 (by rfl) ⟨2449014, by rfl⟩ : syracuseStep 6530705 = 4898029) B4898029
theorem B4353803 : Blo 1933435 4353803 := bstep (se 1 (by rfl) ⟨3265352, by rfl⟩ : syracuseStep 4353803 = 6530705) B6530705
theorem B2902535 : Blo 1933435 2902535 := bstep (se 1 (by rfl) ⟨2176901, by rfl⟩ : syracuseStep 2902535 = 4353803) B4353803
theorem B1935023 : Blo 1933435 1935023 := bstep (se 1 (by rfl) ⟨1451267, by rfl⟩ : syracuseStep 1935023 = 2902535) B2902535
theorem B2902541 : Blo 1933435 2902541 := bbase (se 3 (by rfl) ⟨544226, by rfl⟩ : syracuseStep 2902541 = 1088453) (by norm_num)
theorem B1935027 : Blo 1933435 1935027 := bstep (se 1 (by rfl) ⟨1451270, by rfl⟩ : syracuseStep 1935027 = 2902541) B2902541
theorem B4353821 : Blo 1933435 4353821 := bbase (se 3 (by rfl) ⟨816341, by rfl⟩ : syracuseStep 4353821 = 1632683) (by norm_num)
theorem B2902547 : Blo 1933435 2902547 := bstep (se 1 (by rfl) ⟨2176910, by rfl⟩ : syracuseStep 2902547 = 4353821) B4353821
theorem B1935031 : Blo 1933435 1935031 := bstep (se 1 (by rfl) ⟨1451273, by rfl⟩ : syracuseStep 1935031 = 2902547) B2902547
theorem B3265373 : Blo 1933435 3265373 := bbase (se 3 (by rfl) ⟨612257, by rfl⟩ : syracuseStep 3265373 = 1224515) (by norm_num)
theorem B2176915 : Blo 1933435 2176915 := bstep (se 1 (by rfl) ⟨1632686, by rfl⟩ : syracuseStep 2176915 = 3265373) B3265373
theorem B2902553 : Blo 1933435 2902553 := bstep (se 2 (by rfl) ⟨1088457, by rfl⟩ : syracuseStep 2902553 = 2176915) B2176915
theorem B1935035 : Blo 1933435 1935035 := bstep (se 1 (by rfl) ⟨1451276, by rfl⟩ : syracuseStep 1935035 = 2902553) B2902553
theorem B8265493 : Blo 1933435 8265493 := bbase (se 6 (by rfl) ⟨193722, by rfl⟩ : syracuseStep 8265493 = 387445) (by norm_num)
theorem B11020657 : Blo 1933435 11020657 := bstep (se 2 (by rfl) ⟨4132746, by rfl⟩ : syracuseStep 11020657 = 8265493) B8265493
theorem B14694209 : Blo 1933435 14694209 := bstep (se 2 (by rfl) ⟨5510328, by rfl⟩ : syracuseStep 14694209 = 11020657) B11020657
theorem B9796139 : Blo 1933435 9796139 := bstep (se 1 (by rfl) ⟨7347104, by rfl⟩ : syracuseStep 9796139 = 14694209) B14694209
theorem B6530759 : Blo 1933435 6530759 := bstep (se 1 (by rfl) ⟨4898069, by rfl⟩ : syracuseStep 6530759 = 9796139) B9796139
theorem B4353839 : Blo 1933435 4353839 := bstep (se 1 (by rfl) ⟨3265379, by rfl⟩ : syracuseStep 4353839 = 6530759) B6530759
theorem B2902559 : Blo 1933435 2902559 := bstep (se 1 (by rfl) ⟨2176919, by rfl⟩ : syracuseStep 2902559 = 4353839) B4353839
theorem B1935039 : Blo 1933435 1935039 := bstep (se 1 (by rfl) ⟨1451279, by rfl⟩ : syracuseStep 1935039 = 2902559) B2902559
theorem B2902565 : Blo 1933435 2902565 := bbase (se 4 (by rfl) ⟨272115, by rfl⟩ : syracuseStep 2902565 = 544231) (by norm_num)
theorem B1935043 : Blo 1933435 1935043 := bstep (se 1 (by rfl) ⟨1451282, by rfl⟩ : syracuseStep 1935043 = 2902565) B2902565
theorem B2449045 : Blo 1933435 2449045 := bbase (se 6 (by rfl) ⟨57399, by rfl⟩ : syracuseStep 2449045 = 114799) (by norm_num)
theorem B3265393 : Blo 1933435 3265393 := bstep (se 2 (by rfl) ⟨1224522, by rfl⟩ : syracuseStep 3265393 = 2449045) B2449045
theorem B4353857 : Blo 1933435 4353857 := bstep (se 2 (by rfl) ⟨1632696, by rfl⟩ : syracuseStep 4353857 = 3265393) B3265393
theorem B2902571 : Blo 1933435 2902571 := bstep (se 1 (by rfl) ⟨2176928, by rfl⟩ : syracuseStep 2902571 = 4353857) B4353857
theorem B1935047 : Blo 1933435 1935047 := bstep (se 1 (by rfl) ⟨1451285, by rfl⟩ : syracuseStep 1935047 = 2902571) B2902571
theorem B2176933 : Blo 1933435 2176933 := bbase (se 4 (by rfl) ⟨204087, by rfl⟩ : syracuseStep 2176933 = 408175) (by norm_num)
theorem B2902577 : Blo 1933435 2902577 := bstep (se 2 (by rfl) ⟨1088466, by rfl⟩ : syracuseStep 2902577 = 2176933) B2176933
theorem B1935051 : Blo 1933435 1935051 := bstep (se 1 (by rfl) ⟨1451288, by rfl⟩ : syracuseStep 1935051 = 2902577) B2902577
theorem B8492645 : Blo 1933435 8492645 := bbase (se 4 (by rfl) ⟨796185, by rfl⟩ : syracuseStep 8492645 = 1592371) (by norm_num)
theorem B22647053 : Blo 1933435 22647053 := bstep (se 3 (by rfl) ⟨4246322, by rfl⟩ : syracuseStep 22647053 = 8492645) B8492645
theorem B15098035 : Blo 1933435 15098035 := bstep (se 1 (by rfl) ⟨11323526, by rfl⟩ : syracuseStep 15098035 = 22647053) B22647053
theorem B20130713 : Blo 1933435 20130713 := bstep (se 2 (by rfl) ⟨7549017, by rfl⟩ : syracuseStep 20130713 = 15098035) B15098035
theorem B13420475 : Blo 1933435 13420475 := bstep (se 1 (by rfl) ⟨10065356, by rfl⟩ : syracuseStep 13420475 = 20130713) B20130713
theorem B8946983 : Blo 1933435 8946983 := bstep (se 1 (by rfl) ⟨6710237, by rfl⟩ : syracuseStep 8946983 = 13420475) B13420475
theorem B23858621 : Blo 1933435 23858621 := bstep (se 3 (by rfl) ⟨4473491, by rfl⟩ : syracuseStep 23858621 = 8946983) B8946983
theorem B15905747 : Blo 1933435 15905747 := bstep (se 1 (by rfl) ⟨11929310, by rfl⟩ : syracuseStep 15905747 = 23858621) B23858621
theorem B10603831 : Blo 1933435 10603831 := bstep (se 1 (by rfl) ⟨7952873, by rfl⟩ : syracuseStep 10603831 = 15905747) B15905747
theorem B14138441 : Blo 1933435 14138441 := bstep (se 2 (by rfl) ⟨5301915, by rfl⟩ : syracuseStep 14138441 = 10603831) B10603831
theorem B9425627 : Blo 1933435 9425627 := bstep (se 1 (by rfl) ⟨7069220, by rfl⟩ : syracuseStep 9425627 = 14138441) B14138441
theorem B6283751 : Blo 1933435 6283751 := bstep (se 1 (by rfl) ⟨4712813, by rfl⟩ : syracuseStep 6283751 = 9425627) B9425627
theorem B16756669 : Blo 1933435 16756669 := bstep (se 3 (by rfl) ⟨3141875, by rfl⟩ : syracuseStep 16756669 = 6283751) B6283751
theorem B22342225 : Blo 1933435 22342225 := bstep (se 2 (by rfl) ⟨8378334, by rfl⟩ : syracuseStep 22342225 = 16756669) B16756669
theorem B29789633 : Blo 1933435 29789633 := bstep (se 2 (by rfl) ⟨11171112, by rfl⟩ : syracuseStep 29789633 = 22342225) B22342225
theorem B19859755 : Blo 1933435 19859755 := bstep (se 1 (by rfl) ⟨14894816, by rfl⟩ : syracuseStep 19859755 = 29789633) B29789633
theorem B26479673 : Blo 1933435 26479673 := bstep (se 2 (by rfl) ⟨9929877, by rfl⟩ : syracuseStep 26479673 = 19859755) B19859755
theorem B17653115 : Blo 1933435 17653115 := bstep (se 1 (by rfl) ⟨13239836, by rfl⟩ : syracuseStep 17653115 = 26479673) B26479673
theorem B11768743 : Blo 1933435 11768743 := bstep (se 1 (by rfl) ⟨8826557, by rfl⟩ : syracuseStep 11768743 = 17653115) B17653115
theorem B15691657 : Blo 1933435 15691657 := bstep (se 2 (by rfl) ⟨5884371, by rfl⟩ : syracuseStep 15691657 = 11768743) B11768743
theorem B20922209 : Blo 1933435 20922209 := bstep (se 2 (by rfl) ⟨7845828, by rfl⟩ : syracuseStep 20922209 = 15691657) B15691657
theorem B13948139 : Blo 1933435 13948139 := bstep (se 1 (by rfl) ⟨10461104, by rfl⟩ : syracuseStep 13948139 = 20922209) B20922209
theorem B9298759 : Blo 1933435 9298759 := bstep (se 1 (by rfl) ⟨6974069, by rfl⟩ : syracuseStep 9298759 = 13948139) B13948139
theorem B12398345 : Blo 1933435 12398345 := bstep (se 2 (by rfl) ⟨4649379, by rfl⟩ : syracuseStep 12398345 = 9298759) B9298759
theorem B8265563 : Blo 1933435 8265563 := bstep (se 1 (by rfl) ⟨6199172, by rfl⟩ : syracuseStep 8265563 = 12398345) B12398345
theorem B5510375 : Blo 1933435 5510375 := bstep (se 1 (by rfl) ⟨4132781, by rfl⟩ : syracuseStep 5510375 = 8265563) B8265563
theorem B3673583 : Blo 1933435 3673583 := bstep (se 1 (by rfl) ⟨2755187, by rfl⟩ : syracuseStep 3673583 = 5510375) B5510375
theorem B2449055 : Blo 1933435 2449055 := bstep (se 1 (by rfl) ⟨1836791, by rfl⟩ : syracuseStep 2449055 = 3673583) B3673583
theorem B6530813 : Blo 1933435 6530813 := bstep (se 3 (by rfl) ⟨1224527, by rfl⟩ : syracuseStep 6530813 = 2449055) B2449055
theorem B4353875 : Blo 1933435 4353875 := bstep (se 1 (by rfl) ⟨3265406, by rfl⟩ : syracuseStep 4353875 = 6530813) B6530813
theorem B2902583 : Blo 1933435 2902583 := bstep (se 1 (by rfl) ⟨2176937, by rfl⟩ : syracuseStep 2902583 = 4353875) B4353875
theorem B1935055 : Blo 1933435 1935055 := bstep (se 1 (by rfl) ⟨1451291, by rfl⟩ : syracuseStep 1935055 = 2902583) B2902583
theorem B2902589 : Blo 1933435 2902589 := bbase (se 3 (by rfl) ⟨544235, by rfl⟩ : syracuseStep 2902589 = 1088471) (by norm_num)
theorem B1935059 : Blo 1933435 1935059 := bstep (se 1 (by rfl) ⟨1451294, by rfl⟩ : syracuseStep 1935059 = 2902589) B2902589
theorem B4353893 : Blo 1933435 4353893 := bbase (se 4 (by rfl) ⟨408177, by rfl⟩ : syracuseStep 4353893 = 816355) (by norm_num)
theorem B2902595 : Blo 1933435 2902595 := bstep (se 1 (by rfl) ⟨2176946, by rfl⟩ : syracuseStep 2902595 = 4353893) B4353893
theorem B1935063 : Blo 1933435 1935063 := bstep (se 1 (by rfl) ⟨1451297, by rfl⟩ : syracuseStep 1935063 = 2902595) B2902595
theorem B4898141 : Blo 1933435 4898141 := bbase (se 3 (by rfl) ⟨918401, by rfl⟩ : syracuseStep 4898141 = 1836803) (by norm_num)
theorem B3265427 : Blo 1933435 3265427 := bstep (se 1 (by rfl) ⟨2449070, by rfl⟩ : syracuseStep 3265427 = 4898141) B4898141
theorem B2176951 : Blo 1933435 2176951 := bstep (se 1 (by rfl) ⟨1632713, by rfl⟩ : syracuseStep 2176951 = 3265427) B3265427
theorem B2902601 : Blo 1933435 2902601 := bstep (se 2 (by rfl) ⟨1088475, by rfl⟩ : syracuseStep 2902601 = 2176951) B2176951
theorem B1935067 : Blo 1933435 1935067 := bstep (se 1 (by rfl) ⟨1451300, by rfl⟩ : syracuseStep 1935067 = 2902601) B2902601
theorem B3673613 : Blo 1933435 3673613 := bbase (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) (by norm_num)
theorem B9796301 : Blo 1933435 9796301 := bstep (se 3 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 9796301 = 3673613) B3673613
theorem B6530867 : Blo 1933435 6530867 := bstep (se 1 (by rfl) ⟨4898150, by rfl⟩ : syracuseStep 6530867 = 9796301) B9796301
theorem B4353911 : Blo 1933435 4353911 := bstep (se 1 (by rfl) ⟨3265433, by rfl⟩ : syracuseStep 4353911 = 6530867) B6530867
theorem B2902607 : Blo 1933435 2902607 := bstep (se 1 (by rfl) ⟨2176955, by rfl⟩ : syracuseStep 2902607 = 4353911) B4353911
theorem B1935071 : Blo 1933435 1935071 := bstep (se 1 (by rfl) ⟨1451303, by rfl⟩ : syracuseStep 1935071 = 2902607) B2902607
theorem B2902613 : Blo 1933435 2902613 := bbase (se 8 (by rfl) ⟨17007, by rfl⟩ : syracuseStep 2902613 = 34015) (by norm_num)
theorem B1935075 : Blo 1933435 1935075 := bstep (se 1 (by rfl) ⟨1451306, by rfl⟩ : syracuseStep 1935075 = 2902613) B2902613
theorem B4649437 : Blo 1933435 4649437 := bbase (se 3 (by rfl) ⟨871769, by rfl⟩ : syracuseStep 4649437 = 1743539) (by norm_num)
theorem B6199249 : Blo 1933435 6199249 := bstep (se 2 (by rfl) ⟨2324718, by rfl⟩ : syracuseStep 6199249 = 4649437) B4649437
theorem B8265665 : Blo 1933435 8265665 := bstep (se 2 (by rfl) ⟨3099624, by rfl⟩ : syracuseStep 8265665 = 6199249) B6199249
theorem B5510443 : Blo 1933435 5510443 := bstep (se 1 (by rfl) ⟨4132832, by rfl⟩ : syracuseStep 5510443 = 8265665) B8265665
theorem B7347257 : Blo 1933435 7347257 := bstep (se 2 (by rfl) ⟨2755221, by rfl⟩ : syracuseStep 7347257 = 5510443) B5510443
theorem B4898171 : Blo 1933435 4898171 := bstep (se 1 (by rfl) ⟨3673628, by rfl⟩ : syracuseStep 4898171 = 7347257) B7347257
theorem B3265447 : Blo 1933435 3265447 := bstep (se 1 (by rfl) ⟨2449085, by rfl⟩ : syracuseStep 3265447 = 4898171) B4898171
theorem B4353929 : Blo 1933435 4353929 := bstep (se 2 (by rfl) ⟨1632723, by rfl⟩ : syracuseStep 4353929 = 3265447) B3265447
theorem B2902619 : Blo 1933435 2902619 := bstep (se 1 (by rfl) ⟨2176964, by rfl⟩ : syracuseStep 2902619 = 4353929) B4353929
theorem B1935079 : Blo 1933435 1935079 := bstep (se 1 (by rfl) ⟨1451309, by rfl⟩ : syracuseStep 1935079 = 2902619) B2902619
theorem B2176969 : Blo 1933435 2176969 := bbase (se 2 (by rfl) ⟨816363, by rfl⟩ : syracuseStep 2176969 = 1632727) (by norm_num)
theorem B2902625 : Blo 1933435 2902625 := bstep (se 2 (by rfl) ⟨1088484, by rfl⟩ : syracuseStep 2902625 = 2176969) B2176969
theorem B1935083 : Blo 1933435 1935083 := bstep (se 1 (by rfl) ⟨1451312, by rfl⟩ : syracuseStep 1935083 = 2902625) B2902625
theorem B3099637 : Blo 1933435 3099637 := bbase (se 5 (by rfl) ⟨145295, by rfl⟩ : syracuseStep 3099637 = 290591) (by norm_num)
theorem B16531397 : Blo 1933435 16531397 := bstep (se 4 (by rfl) ⟨1549818, by rfl⟩ : syracuseStep 16531397 = 3099637) B3099637
theorem B11020931 : Blo 1933435 11020931 := bstep (se 1 (by rfl) ⟨8265698, by rfl⟩ : syracuseStep 11020931 = 16531397) B16531397
theorem B7347287 : Blo 1933435 7347287 := bstep (se 1 (by rfl) ⟨5510465, by rfl⟩ : syracuseStep 7347287 = 11020931) B11020931
theorem B4898191 : Blo 1933435 4898191 := bstep (se 1 (by rfl) ⟨3673643, by rfl⟩ : syracuseStep 4898191 = 7347287) B7347287
theorem B6530921 : Blo 1933435 6530921 := bstep (se 2 (by rfl) ⟨2449095, by rfl⟩ : syracuseStep 6530921 = 4898191) B4898191
theorem B4353947 : Blo 1933435 4353947 := bstep (se 1 (by rfl) ⟨3265460, by rfl⟩ : syracuseStep 4353947 = 6530921) B6530921
theorem B2902631 : Blo 1933435 2902631 := bstep (se 1 (by rfl) ⟨2176973, by rfl⟩ : syracuseStep 2902631 = 4353947) B4353947
theorem B1935087 : Blo 1933435 1935087 := bstep (se 1 (by rfl) ⟨1451315, by rfl⟩ : syracuseStep 1935087 = 2902631) B2902631
theorem B2902637 : Blo 1933435 2902637 := bbase (se 3 (by rfl) ⟨544244, by rfl⟩ : syracuseStep 2902637 = 1088489) (by norm_num)
theorem B1935091 : Blo 1933435 1935091 := bstep (se 1 (by rfl) ⟨1451318, by rfl⟩ : syracuseStep 1935091 = 2902637) B2902637
theorem B4353965 : Blo 1933435 4353965 := bbase (se 3 (by rfl) ⟨816368, by rfl⟩ : syracuseStep 4353965 = 1632737) (by norm_num)
theorem B2902643 : Blo 1933435 2902643 := bstep (se 1 (by rfl) ⟨2176982, by rfl⟩ : syracuseStep 2902643 = 4353965) B4353965
theorem B1935095 : Blo 1933435 1935095 := bstep (se 1 (by rfl) ⟨1451321, by rfl⟩ : syracuseStep 1935095 = 2902643) B2902643
theorem B5510501 : Blo 1933435 5510501 := bbase (se 4 (by rfl) ⟨516609, by rfl⟩ : syracuseStep 5510501 = 1033219) (by norm_num)
theorem B3673667 : Blo 1933435 3673667 := bstep (se 1 (by rfl) ⟨2755250, by rfl⟩ : syracuseStep 3673667 = 5510501) B5510501
theorem B2449111 : Blo 1933435 2449111 := bstep (se 1 (by rfl) ⟨1836833, by rfl⟩ : syracuseStep 2449111 = 3673667) B3673667
theorem B3265481 : Blo 1933435 3265481 := bstep (se 2 (by rfl) ⟨1224555, by rfl⟩ : syracuseStep 3265481 = 2449111) B2449111
theorem B2176987 : Blo 1933435 2176987 := bstep (se 1 (by rfl) ⟨1632740, by rfl⟩ : syracuseStep 2176987 = 3265481) B3265481
theorem B2902649 : Blo 1933435 2902649 := bstep (se 2 (by rfl) ⟨1088493, by rfl⟩ : syracuseStep 2902649 = 2176987) B2176987
theorem B1935099 : Blo 1933435 1935099 := bstep (se 1 (by rfl) ⟨1451324, by rfl⟩ : syracuseStep 1935099 = 2902649) B2902649
theorem B7846021 : Blo 1933435 7846021 := bbase (se 4 (by rfl) ⟨735564, by rfl⟩ : syracuseStep 7846021 = 1471129) (by norm_num)
theorem B10461361 : Blo 1933435 10461361 := bstep (se 2 (by rfl) ⟨3923010, by rfl⟩ : syracuseStep 10461361 = 7846021) B7846021
theorem B13948481 : Blo 1933435 13948481 := bstep (se 2 (by rfl) ⟨5230680, by rfl⟩ : syracuseStep 13948481 = 10461361) B10461361
theorem B37195949 : Blo 1933435 37195949 := bstep (se 3 (by rfl) ⟨6974240, by rfl⟩ : syracuseStep 37195949 = 13948481) B13948481
theorem B24797299 : Blo 1933435 24797299 := bstep (se 1 (by rfl) ⟨18597974, by rfl⟩ : syracuseStep 24797299 = 37195949) B37195949
theorem B33063065 : Blo 1933435 33063065 := bstep (se 2 (by rfl) ⟨12398649, by rfl⟩ : syracuseStep 33063065 = 24797299) B24797299
theorem B22042043 : Blo 1933435 22042043 := bstep (se 1 (by rfl) ⟨16531532, by rfl⟩ : syracuseStep 22042043 = 33063065) B33063065
theorem B14694695 : Blo 1933435 14694695 := bstep (se 1 (by rfl) ⟨11021021, by rfl⟩ : syracuseStep 14694695 = 22042043) B22042043
theorem B9796463 : Blo 1933435 9796463 := bstep (se 1 (by rfl) ⟨7347347, by rfl⟩ : syracuseStep 9796463 = 14694695) B14694695
theorem B6530975 : Blo 1933435 6530975 := bstep (se 1 (by rfl) ⟨4898231, by rfl⟩ : syracuseStep 6530975 = 9796463) B9796463
theorem B4353983 : Blo 1933435 4353983 := bstep (se 1 (by rfl) ⟨3265487, by rfl⟩ : syracuseStep 4353983 = 6530975) B6530975
theorem B2902655 : Blo 1933435 2902655 := bstep (se 1 (by rfl) ⟨2176991, by rfl⟩ : syracuseStep 2902655 = 4353983) B4353983
theorem B1935103 : Blo 1933435 1935103 := bstep (se 1 (by rfl) ⟨1451327, by rfl⟩ : syracuseStep 1935103 = 2902655) B2902655
theorem B2902661 : Blo 1933435 2902661 := bbase (se 4 (by rfl) ⟨272124, by rfl⟩ : syracuseStep 2902661 = 544249) (by norm_num)
theorem B1935107 : Blo 1933435 1935107 := bstep (se 1 (by rfl) ⟨1451330, by rfl⟩ : syracuseStep 1935107 = 2902661) B2902661
theorem B3265501 : Blo 1933435 3265501 := bbase (se 3 (by rfl) ⟨612281, by rfl⟩ : syracuseStep 3265501 = 1224563) (by norm_num)
theorem B4354001 : Blo 1933435 4354001 := bstep (se 2 (by rfl) ⟨1632750, by rfl⟩ : syracuseStep 4354001 = 3265501) B3265501
theorem B2902667 : Blo 1933435 2902667 := bstep (se 1 (by rfl) ⟨2177000, by rfl⟩ : syracuseStep 2902667 = 4354001) B4354001
theorem B1935111 : Blo 1933435 1935111 := bstep (se 1 (by rfl) ⟨1451333, by rfl⟩ : syracuseStep 1935111 = 2902667) B2902667
theorem B2177005 : Blo 1933435 2177005 := bbase (se 3 (by rfl) ⟨408188, by rfl⟩ : syracuseStep 2177005 = 816377) (by norm_num)
theorem B2902673 : Blo 1933435 2902673 := bstep (se 2 (by rfl) ⟨1088502, by rfl⟩ : syracuseStep 2902673 = 2177005) B2177005
theorem B1935115 : Blo 1933435 1935115 := bstep (se 1 (by rfl) ⟨1451336, by rfl⟩ : syracuseStep 1935115 = 2902673) B2902673
theorem B6531029 : Blo 1933435 6531029 := bbase (se 7 (by rfl) ⟨76535, by rfl⟩ : syracuseStep 6531029 = 153071) (by norm_num)
theorem B4354019 : Blo 1933435 4354019 := bstep (se 1 (by rfl) ⟨3265514, by rfl⟩ : syracuseStep 4354019 = 6531029) B6531029
theorem B2902679 : Blo 1933435 2902679 := bstep (se 1 (by rfl) ⟨2177009, by rfl⟩ : syracuseStep 2902679 = 4354019) B4354019
theorem B1935119 : Blo 1933435 1935119 := bstep (se 1 (by rfl) ⟨1451339, by rfl⟩ : syracuseStep 1935119 = 2902679) B2902679
theorem B2902685 : Blo 1933435 2902685 := bbase (se 3 (by rfl) ⟨544253, by rfl⟩ : syracuseStep 2902685 = 1088507) (by norm_num)
theorem B1935123 : Blo 1933435 1935123 := bstep (se 1 (by rfl) ⟨1451342, by rfl⟩ : syracuseStep 1935123 = 2902685) B2902685
theorem B4354037 : Blo 1933435 4354037 := bbase (se 5 (by rfl) ⟨204095, by rfl⟩ : syracuseStep 4354037 = 408191) (by norm_num)
theorem B2902691 : Blo 1933435 2902691 := bstep (se 1 (by rfl) ⟨2177018, by rfl⟩ : syracuseStep 2902691 = 4354037) B4354037
theorem B1935127 : Blo 1933435 1935127 := bstep (se 1 (by rfl) ⟨1451345, by rfl⟩ : syracuseStep 1935127 = 2902691) B2902691
theorem B2516437 : Blo 1933435 2516437 := bbase (se 7 (by rfl) ⟨29489, by rfl⟩ : syracuseStep 2516437 = 58979) (by norm_num)
theorem B13420997 : Blo 1933435 13420997 := bstep (se 4 (by rfl) ⟨1258218, by rfl⟩ : syracuseStep 13420997 = 2516437) B2516437
theorem B8947331 : Blo 1933435 8947331 := bstep (se 1 (by rfl) ⟨6710498, by rfl⟩ : syracuseStep 8947331 = 13420997) B13420997
theorem B95438197 : Blo 1933435 95438197 := bstep (se 5 (by rfl) ⟨4473665, by rfl⟩ : syracuseStep 95438197 = 8947331) B8947331
theorem B127250929 : Blo 1933435 127250929 := bstep (se 2 (by rfl) ⟨47719098, by rfl⟩ : syracuseStep 127250929 = 95438197) B95438197
theorem B169667905 : Blo 1933435 169667905 := bstep (se 2 (by rfl) ⟨63625464, by rfl⟩ : syracuseStep 169667905 = 127250929) B127250929
theorem B226223873 : Blo 1933435 226223873 := bstep (se 2 (by rfl) ⟨84833952, by rfl⟩ : syracuseStep 226223873 = 169667905) B169667905
theorem B150815915 : Blo 1933435 150815915 := bstep (se 1 (by rfl) ⟨113111936, by rfl⟩ : syracuseStep 150815915 = 226223873) B226223873
theorem B100543943 : Blo 1933435 100543943 := bstep (se 1 (by rfl) ⟨75407957, by rfl⟩ : syracuseStep 100543943 = 150815915) B150815915
theorem B67029295 : Blo 1933435 67029295 := bstep (se 1 (by rfl) ⟨50271971, by rfl⟩ : syracuseStep 67029295 = 100543943) B100543943
theorem B89372393 : Blo 1933435 89372393 := bstep (se 2 (by rfl) ⟨33514647, by rfl⟩ : syracuseStep 89372393 = 67029295) B67029295
theorem B59581595 : Blo 1933435 59581595 := bstep (se 1 (by rfl) ⟨44686196, by rfl⟩ : syracuseStep 59581595 = 89372393) B89372393
theorem B158884253 : Blo 1933435 158884253 := bstep (se 3 (by rfl) ⟨29790797, by rfl⟩ : syracuseStep 158884253 = 59581595) B59581595
theorem B105922835 : Blo 1933435 105922835 := bstep (se 1 (by rfl) ⟨79442126, by rfl⟩ : syracuseStep 105922835 = 158884253) B158884253
theorem B70615223 : Blo 1933435 70615223 := bstep (se 1 (by rfl) ⟨52961417, by rfl⟩ : syracuseStep 70615223 = 105922835) B105922835
theorem B47076815 : Blo 1933435 47076815 := bstep (se 1 (by rfl) ⟨35307611, by rfl⟩ : syracuseStep 47076815 = 70615223) B70615223
theorem B125538173 : Blo 1933435 125538173 := bstep (se 3 (by rfl) ⟨23538407, by rfl⟩ : syracuseStep 125538173 = 47076815) B47076815
theorem B83692115 : Blo 1933435 83692115 := bstep (se 1 (by rfl) ⟨62769086, by rfl⟩ : syracuseStep 83692115 = 125538173) B125538173
theorem B55794743 : Blo 1933435 55794743 := bstep (se 1 (by rfl) ⟨41846057, by rfl⟩ : syracuseStep 55794743 = 83692115) B83692115
theorem B37196495 : Blo 1933435 37196495 := bstep (se 1 (by rfl) ⟨27897371, by rfl⟩ : syracuseStep 37196495 = 55794743) B55794743
theorem B24797663 : Blo 1933435 24797663 := bstep (se 1 (by rfl) ⟨18598247, by rfl⟩ : syracuseStep 24797663 = 37196495) B37196495
theorem B16531775 : Blo 1933435 16531775 := bstep (se 1 (by rfl) ⟨12398831, by rfl⟩ : syracuseStep 16531775 = 24797663) B24797663
theorem B11021183 : Blo 1933435 11021183 := bstep (se 1 (by rfl) ⟨8265887, by rfl⟩ : syracuseStep 11021183 = 16531775) B16531775
theorem B7347455 : Blo 1933435 7347455 := bstep (se 1 (by rfl) ⟨5510591, by rfl⟩ : syracuseStep 7347455 = 11021183) B11021183
theorem B4898303 : Blo 1933435 4898303 := bstep (se 1 (by rfl) ⟨3673727, by rfl⟩ : syracuseStep 4898303 = 7347455) B7347455
theorem B3265535 : Blo 1933435 3265535 := bstep (se 1 (by rfl) ⟨2449151, by rfl⟩ : syracuseStep 3265535 = 4898303) B4898303
theorem B2177023 : Blo 1933435 2177023 := bstep (se 1 (by rfl) ⟨1632767, by rfl⟩ : syracuseStep 2177023 = 3265535) B3265535
theorem B2902697 : Blo 1933435 2902697 := bstep (se 2 (by rfl) ⟨1088511, by rfl⟩ : syracuseStep 2902697 = 2177023) B2177023
theorem B1935131 : Blo 1933435 1935131 := bstep (se 1 (by rfl) ⟨1451348, by rfl⟩ : syracuseStep 1935131 = 2902697) B2902697
theorem B2755301 : Blo 1933435 2755301 := bbase (se 4 (by rfl) ⟨258309, by rfl⟩ : syracuseStep 2755301 = 516619) (by norm_num)
theorem B7347469 : Blo 1933435 7347469 := bstep (se 3 (by rfl) ⟨1377650, by rfl⟩ : syracuseStep 7347469 = 2755301) B2755301
theorem B9796625 : Blo 1933435 9796625 := bstep (se 2 (by rfl) ⟨3673734, by rfl⟩ : syracuseStep 9796625 = 7347469) B7347469
theorem B6531083 : Blo 1933435 6531083 := bstep (se 1 (by rfl) ⟨4898312, by rfl⟩ : syracuseStep 6531083 = 9796625) B9796625
theorem B4354055 : Blo 1933435 4354055 := bstep (se 1 (by rfl) ⟨3265541, by rfl⟩ : syracuseStep 4354055 = 6531083) B6531083
theorem B2902703 : Blo 1933435 2902703 := bstep (se 1 (by rfl) ⟨2177027, by rfl⟩ : syracuseStep 2902703 = 4354055) B4354055
theorem B1935135 : Blo 1933435 1935135 := bstep (se 1 (by rfl) ⟨1451351, by rfl⟩ : syracuseStep 1935135 = 2902703) B2902703
theorem B2902709 : Blo 1933435 2902709 := bbase (se 5 (by rfl) ⟨136064, by rfl⟩ : syracuseStep 2902709 = 272129) (by norm_num)
theorem B1935139 : Blo 1933435 1935139 := bstep (se 1 (by rfl) ⟨1451354, by rfl⟩ : syracuseStep 1935139 = 2902709) B2902709
theorem B4898333 : Blo 1933435 4898333 := bbase (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) (by norm_num)
theorem B3265555 : Blo 1933435 3265555 := bstep (se 1 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 3265555 = 4898333) B4898333
theorem B4354073 : Blo 1933435 4354073 := bstep (se 2 (by rfl) ⟨1632777, by rfl⟩ : syracuseStep 4354073 = 3265555) B3265555
theorem B2902715 : Blo 1933435 2902715 := bstep (se 1 (by rfl) ⟨2177036, by rfl⟩ : syracuseStep 2902715 = 4354073) B4354073
theorem B1935143 : Blo 1933435 1935143 := bstep (se 1 (by rfl) ⟨1451357, by rfl⟩ : syracuseStep 1935143 = 2902715) B2902715
theorem B2177041 : Blo 1933435 2177041 := bbase (se 2 (by rfl) ⟨816390, by rfl⟩ : syracuseStep 2177041 = 1632781) (by norm_num)
theorem B2902721 : Blo 1933435 2902721 := bstep (se 2 (by rfl) ⟨1088520, by rfl⟩ : syracuseStep 2902721 = 2177041) B2177041
theorem B1935147 : Blo 1933435 1935147 := bstep (se 1 (by rfl) ⟨1451360, by rfl⟩ : syracuseStep 1935147 = 2902721) B2902721
theorem B3673765 : Blo 1933435 3673765 := bbase (se 4 (by rfl) ⟨344415, by rfl⟩ : syracuseStep 3673765 = 688831) (by norm_num)
theorem B4898353 : Blo 1933435 4898353 := bstep (se 2 (by rfl) ⟨1836882, by rfl⟩ : syracuseStep 4898353 = 3673765) B3673765
theorem B6531137 : Blo 1933435 6531137 := bstep (se 2 (by rfl) ⟨2449176, by rfl⟩ : syracuseStep 6531137 = 4898353) B4898353
theorem B4354091 : Blo 1933435 4354091 := bstep (se 1 (by rfl) ⟨3265568, by rfl⟩ : syracuseStep 4354091 = 6531137) B6531137
theorem B2902727 : Blo 1933435 2902727 := bstep (se 1 (by rfl) ⟨2177045, by rfl⟩ : syracuseStep 2902727 = 4354091) B4354091
theorem B1935151 : Blo 1933435 1935151 := bstep (se 1 (by rfl) ⟨1451363, by rfl⟩ : syracuseStep 1935151 = 2902727) B2902727
theorem B2902733 : Blo 1933435 2902733 := bbase (se 3 (by rfl) ⟨544262, by rfl⟩ : syracuseStep 2902733 = 1088525) (by norm_num)
theorem B1935155 : Blo 1933435 1935155 := bstep (se 1 (by rfl) ⟨1451366, by rfl⟩ : syracuseStep 1935155 = 2902733) B2902733
theorem B4354109 : Blo 1933435 4354109 := bbase (se 3 (by rfl) ⟨816395, by rfl⟩ : syracuseStep 4354109 = 1632791) (by norm_num)
theorem B2902739 : Blo 1933435 2902739 := bstep (se 1 (by rfl) ⟨2177054, by rfl⟩ : syracuseStep 2902739 = 4354109) B4354109
theorem B1935159 : Blo 1933435 1935159 := bstep (se 1 (by rfl) ⟨1451369, by rfl⟩ : syracuseStep 1935159 = 2902739) B2902739
theorem B3265589 : Blo 1933435 3265589 := bbase (se 5 (by rfl) ⟨153074, by rfl⟩ : syracuseStep 3265589 = 306149) (by norm_num)
theorem B2177059 : Blo 1933435 2177059 := bstep (se 1 (by rfl) ⟨1632794, by rfl⟩ : syracuseStep 2177059 = 3265589) B3265589
theorem B2902745 : Blo 1933435 2902745 := bstep (se 2 (by rfl) ⟨1088529, by rfl⟩ : syracuseStep 2902745 = 2177059) B2177059
theorem B1935163 : Blo 1933435 1935163 := bstep (se 1 (by rfl) ⟨1451372, by rfl⟩ : syracuseStep 1935163 = 2902745) B2902745
theorem B5510693 : Blo 1933435 5510693 := bbase (se 4 (by rfl) ⟨516627, by rfl⟩ : syracuseStep 5510693 = 1033255) (by norm_num)
theorem B14695181 : Blo 1933435 14695181 := bstep (se 3 (by rfl) ⟨2755346, by rfl⟩ : syracuseStep 14695181 = 5510693) B5510693
theorem B9796787 : Blo 1933435 9796787 := bstep (se 1 (by rfl) ⟨7347590, by rfl⟩ : syracuseStep 9796787 = 14695181) B14695181
theorem B6531191 : Blo 1933435 6531191 := bstep (se 1 (by rfl) ⟨4898393, by rfl⟩ : syracuseStep 6531191 = 9796787) B9796787
theorem B4354127 : Blo 1933435 4354127 := bstep (se 1 (by rfl) ⟨3265595, by rfl⟩ : syracuseStep 4354127 = 6531191) B6531191
theorem B2902751 : Blo 1933435 2902751 := bstep (se 1 (by rfl) ⟨2177063, by rfl⟩ : syracuseStep 2902751 = 4354127) B4354127
theorem B1935167 : Blo 1933435 1935167 := bstep (se 1 (by rfl) ⟨1451375, by rfl⟩ : syracuseStep 1935167 = 2902751) B2902751
theorem B2902757 : Blo 1933435 2902757 := bbase (se 4 (by rfl) ⟨272133, by rfl⟩ : syracuseStep 2902757 = 544267) (by norm_num)
theorem B1935171 : Blo 1933435 1935171 := bstep (se 1 (by rfl) ⟨1451378, by rfl⟩ : syracuseStep 1935171 = 2902757) B2902757
theorem B4649669 : Blo 1933435 4649669 := bbase (se 4 (by rfl) ⟨435906, by rfl⟩ : syracuseStep 4649669 = 871813) (by norm_num)
theorem B3099779 : Blo 1933435 3099779 := bstep (se 1 (by rfl) ⟨2324834, by rfl⟩ : syracuseStep 3099779 = 4649669) B4649669
theorem B2066519 : Blo 1933435 2066519 := bstep (se 1 (by rfl) ⟨1549889, by rfl⟩ : syracuseStep 2066519 = 3099779) B3099779
theorem B5510717 : Blo 1933435 5510717 := bstep (se 3 (by rfl) ⟨1033259, by rfl⟩ : syracuseStep 5510717 = 2066519) B2066519
theorem B3673811 : Blo 1933435 3673811 := bstep (se 1 (by rfl) ⟨2755358, by rfl⟩ : syracuseStep 3673811 = 5510717) B5510717
theorem B2449207 : Blo 1933435 2449207 := bstep (se 1 (by rfl) ⟨1836905, by rfl⟩ : syracuseStep 2449207 = 3673811) B3673811
theorem B3265609 : Blo 1933435 3265609 := bstep (se 2 (by rfl) ⟨1224603, by rfl⟩ : syracuseStep 3265609 = 2449207) B2449207
theorem B4354145 : Blo 1933435 4354145 := bstep (se 2 (by rfl) ⟨1632804, by rfl⟩ : syracuseStep 4354145 = 3265609) B3265609
theorem B2902763 : Blo 1933435 2902763 := bstep (se 1 (by rfl) ⟨2177072, by rfl⟩ : syracuseStep 2902763 = 4354145) B4354145
theorem B1935175 : Blo 1933435 1935175 := bstep (se 1 (by rfl) ⟨1451381, by rfl⟩ : syracuseStep 1935175 = 2902763) B2902763
theorem B2177077 : Blo 1933435 2177077 := bbase (se 5 (by rfl) ⟨102050, by rfl⟩ : syracuseStep 2177077 = 204101) (by norm_num)
theorem B2902769 : Blo 1933435 2902769 := bstep (se 2 (by rfl) ⟨1088538, by rfl⟩ : syracuseStep 2902769 = 2177077) B2177077
theorem B1935179 : Blo 1933435 1935179 := bstep (se 1 (by rfl) ⟨1451384, by rfl⟩ : syracuseStep 1935179 = 2902769) B2902769
theorem B2449217 : Blo 1933435 2449217 := bbase (se 2 (by rfl) ⟨918456, by rfl⟩ : syracuseStep 2449217 = 1836913) (by norm_num)
theorem B6531245 : Blo 1933435 6531245 := bstep (se 3 (by rfl) ⟨1224608, by rfl⟩ : syracuseStep 6531245 = 2449217) B2449217
theorem B4354163 : Blo 1933435 4354163 := bstep (se 1 (by rfl) ⟨3265622, by rfl⟩ : syracuseStep 4354163 = 6531245) B6531245
theorem B2902775 : Blo 1933435 2902775 := bstep (se 1 (by rfl) ⟨2177081, by rfl⟩ : syracuseStep 2902775 = 4354163) B4354163
theorem B1935183 : Blo 1933435 1935183 := bstep (se 1 (by rfl) ⟨1451387, by rfl⟩ : syracuseStep 1935183 = 2902775) B2902775
theorem B2902781 : Blo 1933435 2902781 := bbase (se 3 (by rfl) ⟨544271, by rfl⟩ : syracuseStep 2902781 = 1088543) (by norm_num)
theorem B1935187 : Blo 1933435 1935187 := bstep (se 1 (by rfl) ⟨1451390, by rfl⟩ : syracuseStep 1935187 = 2902781) B2902781
theorem B4354181 : Blo 1933435 4354181 := bbase (se 4 (by rfl) ⟨408204, by rfl⟩ : syracuseStep 4354181 = 816409) (by norm_num)
theorem B2902787 : Blo 1933435 2902787 := bstep (se 1 (by rfl) ⟨2177090, by rfl⟩ : syracuseStep 2902787 = 4354181) B4354181
theorem B1935191 : Blo 1933435 1935191 := bstep (se 1 (by rfl) ⟨1451393, by rfl⟩ : syracuseStep 1935191 = 2902787) B2902787
theorem B4649717 : Blo 1933435 4649717 := bbase (se 5 (by rfl) ⟨217955, by rfl⟩ : syracuseStep 4649717 = 435911) (by norm_num)
theorem B3099811 : Blo 1933435 3099811 := bstep (se 1 (by rfl) ⟨2324858, by rfl⟩ : syracuseStep 3099811 = 4649717) B4649717
theorem B4133081 : Blo 1933435 4133081 := bstep (se 2 (by rfl) ⟨1549905, by rfl⟩ : syracuseStep 4133081 = 3099811) B3099811
theorem B2755387 : Blo 1933435 2755387 := bstep (se 1 (by rfl) ⟨2066540, by rfl⟩ : syracuseStep 2755387 = 4133081) B4133081
theorem B3673849 : Blo 1933435 3673849 := bstep (se 2 (by rfl) ⟨1377693, by rfl⟩ : syracuseStep 3673849 = 2755387) B2755387
theorem B4898465 : Blo 1933435 4898465 := bstep (se 2 (by rfl) ⟨1836924, by rfl⟩ : syracuseStep 4898465 = 3673849) B3673849
theorem B3265643 : Blo 1933435 3265643 := bstep (se 1 (by rfl) ⟨2449232, by rfl⟩ : syracuseStep 3265643 = 4898465) B4898465
theorem B2177095 : Blo 1933435 2177095 := bstep (se 1 (by rfl) ⟨1632821, by rfl⟩ : syracuseStep 2177095 = 3265643) B3265643
theorem B2902793 : Blo 1933435 2902793 := bstep (se 2 (by rfl) ⟨1088547, by rfl⟩ : syracuseStep 2902793 = 2177095) B2177095
theorem B1935195 : Blo 1933435 1935195 := bstep (se 1 (by rfl) ⟨1451396, by rfl⟩ : syracuseStep 1935195 = 2902793) B2902793
theorem B9796949 : Blo 1933435 9796949 := bbase (se 11 (by rfl) ⟨7175, by rfl⟩ : syracuseStep 9796949 = 14351) (by norm_num)
theorem B6531299 : Blo 1933435 6531299 := bstep (se 1 (by rfl) ⟨4898474, by rfl⟩ : syracuseStep 6531299 = 9796949) B9796949
theorem B4354199 : Blo 1933435 4354199 := bstep (se 1 (by rfl) ⟨3265649, by rfl⟩ : syracuseStep 4354199 = 6531299) B6531299
theorem B2902799 : Blo 1933435 2902799 := bstep (se 1 (by rfl) ⟨2177099, by rfl⟩ : syracuseStep 2902799 = 4354199) B4354199
theorem B1935199 : Blo 1933435 1935199 := bstep (se 1 (by rfl) ⟨1451399, by rfl⟩ : syracuseStep 1935199 = 2902799) B2902799
theorem B2902805 : Blo 1933435 2902805 := bbase (se 6 (by rfl) ⟨68034, by rfl⟩ : syracuseStep 2902805 = 136069) (by norm_num)
theorem B1935203 : Blo 1933435 1935203 := bstep (se 1 (by rfl) ⟨1451402, by rfl⟩ : syracuseStep 1935203 = 2902805) B2902805
theorem B6620437 : Blo 1933435 6620437 := bbase (se 6 (by rfl) ⟨155166, by rfl⟩ : syracuseStep 6620437 = 310333) (by norm_num)
theorem B35308997 : Blo 1933435 35308997 := bstep (se 4 (by rfl) ⟨3310218, by rfl⟩ : syracuseStep 35308997 = 6620437) B6620437
theorem B23539331 : Blo 1933435 23539331 := bstep (se 1 (by rfl) ⟨17654498, by rfl⟩ : syracuseStep 23539331 = 35308997) B35308997
theorem B15692887 : Blo 1933435 15692887 := bstep (se 1 (by rfl) ⟨11769665, by rfl⟩ : syracuseStep 15692887 = 23539331) B23539331
theorem B20923849 : Blo 1933435 20923849 := bstep (se 2 (by rfl) ⟨7846443, by rfl⟩ : syracuseStep 20923849 = 15692887) B15692887
theorem B27898465 : Blo 1933435 27898465 := bstep (se 2 (by rfl) ⟨10461924, by rfl⟩ : syracuseStep 27898465 = 20923849) B20923849
theorem B37197953 : Blo 1933435 37197953 := bstep (se 2 (by rfl) ⟨13949232, by rfl⟩ : syracuseStep 37197953 = 27898465) B27898465
theorem B24798635 : Blo 1933435 24798635 := bstep (se 1 (by rfl) ⟨18598976, by rfl⟩ : syracuseStep 24798635 = 37197953) B37197953
theorem B16532423 : Blo 1933435 16532423 := bstep (se 1 (by rfl) ⟨12399317, by rfl⟩ : syracuseStep 16532423 = 24798635) B24798635
theorem B11021615 : Blo 1933435 11021615 := bstep (se 1 (by rfl) ⟨8266211, by rfl⟩ : syracuseStep 11021615 = 16532423) B16532423
theorem B7347743 : Blo 1933435 7347743 := bstep (se 1 (by rfl) ⟨5510807, by rfl⟩ : syracuseStep 7347743 = 11021615) B11021615
theorem B4898495 : Blo 1933435 4898495 := bstep (se 1 (by rfl) ⟨3673871, by rfl⟩ : syracuseStep 4898495 = 7347743) B7347743
theorem B3265663 : Blo 1933435 3265663 := bstep (se 1 (by rfl) ⟨2449247, by rfl⟩ : syracuseStep 3265663 = 4898495) B4898495
theorem B4354217 : Blo 1933435 4354217 := bstep (se 2 (by rfl) ⟨1632831, by rfl⟩ : syracuseStep 4354217 = 3265663) B3265663
theorem B2902811 : Blo 1933435 2902811 := bstep (se 1 (by rfl) ⟨2177108, by rfl⟩ : syracuseStep 2902811 = 4354217) B4354217
theorem B1935207 : Blo 1933435 1935207 := bstep (se 1 (by rfl) ⟨1451405, by rfl⟩ : syracuseStep 1935207 = 2902811) B2902811
theorem B2177113 : Blo 1933435 2177113 := bbase (se 2 (by rfl) ⟨816417, by rfl⟩ : syracuseStep 2177113 = 1632835) (by norm_num)
theorem B2902817 : Blo 1933435 2902817 := bstep (se 2 (by rfl) ⟨1088556, by rfl⟩ : syracuseStep 2902817 = 2177113) B2177113
theorem B1935211 : Blo 1933435 1935211 := bstep (se 1 (by rfl) ⟨1451408, by rfl⟩ : syracuseStep 1935211 = 2902817) B2902817
theorem B6199685 : Blo 1933435 6199685 := bbase (se 4 (by rfl) ⟨581220, by rfl⟩ : syracuseStep 6199685 = 1162441) (by norm_num)
theorem B4133123 : Blo 1933435 4133123 := bstep (se 1 (by rfl) ⟨3099842, by rfl⟩ : syracuseStep 4133123 = 6199685) B6199685
theorem B2755415 : Blo 1933435 2755415 := bstep (se 1 (by rfl) ⟨2066561, by rfl⟩ : syracuseStep 2755415 = 4133123) B4133123
theorem B7347773 : Blo 1933435 7347773 := bstep (se 3 (by rfl) ⟨1377707, by rfl⟩ : syracuseStep 7347773 = 2755415) B2755415
theorem B4898515 : Blo 1933435 4898515 := bstep (se 1 (by rfl) ⟨3673886, by rfl⟩ : syracuseStep 4898515 = 7347773) B7347773
theorem B6531353 : Blo 1933435 6531353 := bstep (se 2 (by rfl) ⟨2449257, by rfl⟩ : syracuseStep 6531353 = 4898515) B4898515
theorem B4354235 : Blo 1933435 4354235 := bstep (se 1 (by rfl) ⟨3265676, by rfl⟩ : syracuseStep 4354235 = 6531353) B6531353
theorem B2902823 : Blo 1933435 2902823 := bstep (se 1 (by rfl) ⟨2177117, by rfl⟩ : syracuseStep 2902823 = 4354235) B4354235
theorem B1935215 : Blo 1933435 1935215 := bstep (se 1 (by rfl) ⟨1451411, by rfl⟩ : syracuseStep 1935215 = 2902823) B2902823
theorem B2902829 : Blo 1933435 2902829 := bbase (se 3 (by rfl) ⟨544280, by rfl⟩ : syracuseStep 2902829 = 1088561) (by norm_num)
theorem B1935219 : Blo 1933435 1935219 := bstep (se 1 (by rfl) ⟨1451414, by rfl⟩ : syracuseStep 1935219 = 2902829) B2902829
theorem B4354253 : Blo 1933435 4354253 := bbase (se 3 (by rfl) ⟨816422, by rfl⟩ : syracuseStep 4354253 = 1632845) (by norm_num)
theorem B2902835 : Blo 1933435 2902835 := bstep (se 1 (by rfl) ⟨2177126, by rfl⟩ : syracuseStep 2902835 = 4354253) B4354253
theorem B1935223 : Blo 1933435 1935223 := bstep (se 1 (by rfl) ⟨1451417, by rfl⟩ : syracuseStep 1935223 = 2902835) B2902835
theorem B2449273 : Blo 1933435 2449273 := bbase (se 2 (by rfl) ⟨918477, by rfl⟩ : syracuseStep 2449273 = 1836955) (by norm_num)
theorem B3265697 : Blo 1933435 3265697 := bstep (se 2 (by rfl) ⟨1224636, by rfl⟩ : syracuseStep 3265697 = 2449273) B2449273
theorem B2177131 : Blo 1933435 2177131 := bstep (se 1 (by rfl) ⟨1632848, by rfl⟩ : syracuseStep 2177131 = 3265697) B3265697
theorem B2902841 : Blo 1933435 2902841 := bstep (se 2 (by rfl) ⟨1088565, by rfl⟩ : syracuseStep 2902841 = 2177131) B2177131
theorem B1935227 : Blo 1933435 1935227 := bstep (se 1 (by rfl) ⟨1451420, by rfl⟩ : syracuseStep 1935227 = 2902841) B2902841
theorem B2942453 : Blo 1933435 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B7846541 : Blo 1933435 7846541 := bstep (se 3 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 7846541 = 2942453) B2942453
theorem B5231027 : Blo 1933435 5231027 := bstep (se 1 (by rfl) ⟨3923270, by rfl⟩ : syracuseStep 5231027 = 7846541) B7846541
theorem B13949405 : Blo 1933435 13949405 := bstep (se 3 (by rfl) ⟨2615513, by rfl⟩ : syracuseStep 13949405 = 5231027) B5231027
theorem B9299603 : Blo 1933435 9299603 := bstep (se 1 (by rfl) ⟨6974702, by rfl⟩ : syracuseStep 9299603 = 13949405) B13949405
theorem B6199735 : Blo 1933435 6199735 := bstep (se 1 (by rfl) ⟨4649801, by rfl⟩ : syracuseStep 6199735 = 9299603) B9299603
theorem B8266313 : Blo 1933435 8266313 := bstep (se 2 (by rfl) ⟨3099867, by rfl⟩ : syracuseStep 8266313 = 6199735) B6199735
theorem B22043501 : Blo 1933435 22043501 := bstep (se 3 (by rfl) ⟨4133156, by rfl⟩ : syracuseStep 22043501 = 8266313) B8266313
theorem B14695667 : Blo 1933435 14695667 := bstep (se 1 (by rfl) ⟨11021750, by rfl⟩ : syracuseStep 14695667 = 22043501) B22043501
theorem B9797111 : Blo 1933435 9797111 := bstep (se 1 (by rfl) ⟨7347833, by rfl⟩ : syracuseStep 9797111 = 14695667) B14695667
theorem B6531407 : Blo 1933435 6531407 := bstep (se 1 (by rfl) ⟨4898555, by rfl⟩ : syracuseStep 6531407 = 9797111) B9797111
theorem B4354271 : Blo 1933435 4354271 := bstep (se 1 (by rfl) ⟨3265703, by rfl⟩ : syracuseStep 4354271 = 6531407) B6531407
theorem B2902847 : Blo 1933435 2902847 := bstep (se 1 (by rfl) ⟨2177135, by rfl⟩ : syracuseStep 2902847 = 4354271) B4354271
theorem B1935231 : Blo 1933435 1935231 := bstep (se 1 (by rfl) ⟨1451423, by rfl⟩ : syracuseStep 1935231 = 2902847) B2902847
theorem B2902853 : Blo 1933435 2902853 := bbase (se 4 (by rfl) ⟨272142, by rfl⟩ : syracuseStep 2902853 = 544285) (by norm_num)
theorem B1935235 : Blo 1933435 1935235 := bstep (se 1 (by rfl) ⟨1451426, by rfl⟩ : syracuseStep 1935235 = 2902853) B2902853
theorem B3265717 : Blo 1933435 3265717 := bbase (se 5 (by rfl) ⟨153080, by rfl⟩ : syracuseStep 3265717 = 306161) (by norm_num)
theorem B4354289 : Blo 1933435 4354289 := bstep (se 2 (by rfl) ⟨1632858, by rfl⟩ : syracuseStep 4354289 = 3265717) B3265717
theorem B2902859 : Blo 1933435 2902859 := bstep (se 1 (by rfl) ⟨2177144, by rfl⟩ : syracuseStep 2902859 = 4354289) B4354289
theorem B1935239 : Blo 1933435 1935239 := bstep (se 1 (by rfl) ⟨1451429, by rfl⟩ : syracuseStep 1935239 = 2902859) B2902859
theorem B2177149 : Blo 1933435 2177149 := bbase (se 3 (by rfl) ⟨408215, by rfl⟩ : syracuseStep 2177149 = 816431) (by norm_num)
theorem B2902865 : Blo 1933435 2902865 := bstep (se 2 (by rfl) ⟨1088574, by rfl⟩ : syracuseStep 2902865 = 2177149) B2177149
theorem B1935243 : Blo 1933435 1935243 := bstep (se 1 (by rfl) ⟨1451432, by rfl⟩ : syracuseStep 1935243 = 2902865) B2902865
theorem B6531461 : Blo 1933435 6531461 := bbase (se 4 (by rfl) ⟨612324, by rfl⟩ : syracuseStep 6531461 = 1224649) (by norm_num)
theorem B4354307 : Blo 1933435 4354307 := bstep (se 1 (by rfl) ⟨3265730, by rfl⟩ : syracuseStep 4354307 = 6531461) B6531461
theorem B2902871 : Blo 1933435 2902871 := bstep (se 1 (by rfl) ⟨2177153, by rfl⟩ : syracuseStep 2902871 = 4354307) B4354307
theorem B1935247 : Blo 1933435 1935247 := bstep (se 1 (by rfl) ⟨1451435, by rfl⟩ : syracuseStep 1935247 = 2902871) B2902871
theorem B2902877 : Blo 1933435 2902877 := bbase (se 3 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 2902877 = 1088579) (by norm_num)
theorem B1935251 : Blo 1933435 1935251 := bstep (se 1 (by rfl) ⟨1451438, by rfl⟩ : syracuseStep 1935251 = 2902877) B2902877
theorem B4354325 : Blo 1933435 4354325 := bbase (se 6 (by rfl) ⟨102054, by rfl⟩ : syracuseStep 4354325 = 204109) (by norm_num)
theorem B2902883 : Blo 1933435 2902883 := bstep (se 1 (by rfl) ⟨2177162, by rfl⟩ : syracuseStep 2902883 = 4354325) B4354325
theorem B1935255 : Blo 1933435 1935255 := bstep (se 1 (by rfl) ⟨1451441, by rfl⟩ : syracuseStep 1935255 = 2902883) B2902883
theorem B7347941 : Blo 1933435 7347941 := bbase (se 4 (by rfl) ⟨688869, by rfl⟩ : syracuseStep 7347941 = 1377739) (by norm_num)
theorem B4898627 : Blo 1933435 4898627 := bstep (se 1 (by rfl) ⟨3673970, by rfl⟩ : syracuseStep 4898627 = 7347941) B7347941
theorem B3265751 : Blo 1933435 3265751 := bstep (se 1 (by rfl) ⟨2449313, by rfl⟩ : syracuseStep 3265751 = 4898627) B4898627
theorem B2177167 : Blo 1933435 2177167 := bstep (se 1 (by rfl) ⟨1632875, by rfl⟩ : syracuseStep 2177167 = 3265751) B3265751
theorem B2902889 : Blo 1933435 2902889 := bstep (se 2 (by rfl) ⟨1088583, by rfl⟩ : syracuseStep 2902889 = 2177167) B2177167
theorem B1935259 : Blo 1933435 1935259 := bstep (se 1 (by rfl) ⟨1451444, by rfl⟩ : syracuseStep 1935259 = 2902889) B2902889
theorem B10462229 : Blo 1933435 10462229 := bbase (se 6 (by rfl) ⟨245208, by rfl⟩ : syracuseStep 10462229 = 490417) (by norm_num)
theorem B6974819 : Blo 1933435 6974819 := bstep (se 1 (by rfl) ⟨5231114, by rfl⟩ : syracuseStep 6974819 = 10462229) B10462229
theorem B4649879 : Blo 1933435 4649879 := bstep (se 1 (by rfl) ⟨3487409, by rfl⟩ : syracuseStep 4649879 = 6974819) B6974819
theorem B3099919 : Blo 1933435 3099919 := bstep (se 1 (by rfl) ⟨2324939, by rfl⟩ : syracuseStep 3099919 = 4649879) B4649879
theorem B4133225 : Blo 1933435 4133225 := bstep (se 2 (by rfl) ⟨1549959, by rfl⟩ : syracuseStep 4133225 = 3099919) B3099919
theorem B11021933 : Blo 1933435 11021933 := bstep (se 3 (by rfl) ⟨2066612, by rfl⟩ : syracuseStep 11021933 = 4133225) B4133225
theorem B7347955 : Blo 1933435 7347955 := bstep (se 1 (by rfl) ⟨5510966, by rfl⟩ : syracuseStep 7347955 = 11021933) B11021933
theorem B9797273 : Blo 1933435 9797273 := bstep (se 2 (by rfl) ⟨3673977, by rfl⟩ : syracuseStep 9797273 = 7347955) B7347955
theorem B6531515 : Blo 1933435 6531515 := bstep (se 1 (by rfl) ⟨4898636, by rfl⟩ : syracuseStep 6531515 = 9797273) B9797273
theorem B4354343 : Blo 1933435 4354343 := bstep (se 1 (by rfl) ⟨3265757, by rfl⟩ : syracuseStep 4354343 = 6531515) B6531515
theorem B2902895 : Blo 1933435 2902895 := bstep (se 1 (by rfl) ⟨2177171, by rfl⟩ : syracuseStep 2902895 = 4354343) B4354343
theorem B1935263 : Blo 1933435 1935263 := bstep (se 1 (by rfl) ⟨1451447, by rfl⟩ : syracuseStep 1935263 = 2902895) B2902895
theorem B2902901 : Blo 1933435 2902901 := bbase (se 5 (by rfl) ⟨136073, by rfl⟩ : syracuseStep 2902901 = 272147) (by norm_num)
theorem B1935267 : Blo 1933435 1935267 := bstep (se 1 (by rfl) ⟨1451450, by rfl⟩ : syracuseStep 1935267 = 2902901) B2902901
theorem B4413773 : Blo 1933435 4413773 := bbase (se 3 (by rfl) ⟨827582, by rfl⟩ : syracuseStep 4413773 = 1655165) (by norm_num)
theorem B2942515 : Blo 1933435 2942515 := bstep (se 1 (by rfl) ⟨2206886, by rfl⟩ : syracuseStep 2942515 = 4413773) B4413773
theorem B3923353 : Blo 1933435 3923353 := bstep (se 2 (by rfl) ⟨1471257, by rfl⟩ : syracuseStep 3923353 = 2942515) B2942515
theorem B5231137 : Blo 1933435 5231137 := bstep (se 2 (by rfl) ⟨1961676, by rfl⟩ : syracuseStep 5231137 = 3923353) B3923353
theorem B6974849 : Blo 1933435 6974849 := bstep (se 2 (by rfl) ⟨2615568, by rfl⟩ : syracuseStep 6974849 = 5231137) B5231137
theorem B4649899 : Blo 1933435 4649899 := bstep (se 1 (by rfl) ⟨3487424, by rfl⟩ : syracuseStep 4649899 = 6974849) B6974849
theorem B6199865 : Blo 1933435 6199865 := bstep (se 2 (by rfl) ⟨2324949, by rfl⟩ : syracuseStep 6199865 = 4649899) B4649899
theorem B4133243 : Blo 1933435 4133243 := bstep (se 1 (by rfl) ⟨3099932, by rfl⟩ : syracuseStep 4133243 = 6199865) B6199865
theorem B2755495 : Blo 1933435 2755495 := bstep (se 1 (by rfl) ⟨2066621, by rfl⟩ : syracuseStep 2755495 = 4133243) B4133243
theorem B3673993 : Blo 1933435 3673993 := bstep (se 2 (by rfl) ⟨1377747, by rfl⟩ : syracuseStep 3673993 = 2755495) B2755495
theorem B4898657 : Blo 1933435 4898657 := bstep (se 2 (by rfl) ⟨1836996, by rfl⟩ : syracuseStep 4898657 = 3673993) B3673993
theorem B3265771 : Blo 1933435 3265771 := bstep (se 1 (by rfl) ⟨2449328, by rfl⟩ : syracuseStep 3265771 = 4898657) B4898657
theorem B4354361 : Blo 1933435 4354361 := bstep (se 2 (by rfl) ⟨1632885, by rfl⟩ : syracuseStep 4354361 = 3265771) B3265771
theorem B2902907 : Blo 1933435 2902907 := bstep (se 1 (by rfl) ⟨2177180, by rfl⟩ : syracuseStep 2902907 = 4354361) B4354361
theorem B1935271 : Blo 1933435 1935271 := bstep (se 1 (by rfl) ⟨1451453, by rfl⟩ : syracuseStep 1935271 = 2902907) B2902907
theorem B2177185 : Blo 1933435 2177185 := bbase (se 2 (by rfl) ⟨816444, by rfl⟩ : syracuseStep 2177185 = 1632889) (by norm_num)
theorem B2902913 : Blo 1933435 2902913 := bstep (se 2 (by rfl) ⟨1088592, by rfl⟩ : syracuseStep 2902913 = 2177185) B2177185
theorem B1935275 : Blo 1933435 1935275 := bstep (se 1 (by rfl) ⟨1451456, by rfl⟩ : syracuseStep 1935275 = 2902913) B2902913
theorem B4898677 : Blo 1933435 4898677 := bbase (se 5 (by rfl) ⟨229625, by rfl⟩ : syracuseStep 4898677 = 459251) (by norm_num)
theorem B6531569 : Blo 1933435 6531569 := bstep (se 2 (by rfl) ⟨2449338, by rfl⟩ : syracuseStep 6531569 = 4898677) B4898677
theorem B4354379 : Blo 1933435 4354379 := bstep (se 1 (by rfl) ⟨3265784, by rfl⟩ : syracuseStep 4354379 = 6531569) B6531569
theorem B2902919 : Blo 1933435 2902919 := bstep (se 1 (by rfl) ⟨2177189, by rfl⟩ : syracuseStep 2902919 = 4354379) B4354379
theorem B1935279 : Blo 1933435 1935279 := bstep (se 1 (by rfl) ⟨1451459, by rfl⟩ : syracuseStep 1935279 = 2902919) B2902919
theorem B2902925 : Blo 1933435 2902925 := bbase (se 3 (by rfl) ⟨544298, by rfl⟩ : syracuseStep 2902925 = 1088597) (by norm_num)
theorem B1935283 : Blo 1933435 1935283 := bstep (se 1 (by rfl) ⟨1451462, by rfl⟩ : syracuseStep 1935283 = 2902925) B2902925
theorem B4354397 : Blo 1933435 4354397 := bbase (se 3 (by rfl) ⟨816449, by rfl⟩ : syracuseStep 4354397 = 1632899) (by norm_num)
theorem B2902931 : Blo 1933435 2902931 := bstep (se 1 (by rfl) ⟨2177198, by rfl⟩ : syracuseStep 2902931 = 4354397) B4354397
theorem B1935287 : Blo 1933435 1935287 := bstep (se 1 (by rfl) ⟨1451465, by rfl⟩ : syracuseStep 1935287 = 2902931) B2902931
theorem B3265805 : Blo 1933435 3265805 := bbase (se 3 (by rfl) ⟨612338, by rfl⟩ : syracuseStep 3265805 = 1224677) (by norm_num)
theorem B2177203 : Blo 1933435 2177203 := bstep (se 1 (by rfl) ⟨1632902, by rfl⟩ : syracuseStep 2177203 = 3265805) B3265805
theorem B2902937 : Blo 1933435 2902937 := bstep (se 2 (by rfl) ⟨1088601, by rfl⟩ : syracuseStep 2902937 = 2177203) B2177203
theorem B1935291 : Blo 1933435 1935291 := bstep (se 1 (by rfl) ⟨1451468, by rfl⟩ : syracuseStep 1935291 = 2902937) B2902937
theorem B16533173 : Blo 1933435 16533173 := bbase (se 5 (by rfl) ⟨774992, by rfl⟩ : syracuseStep 16533173 = 1549985) (by norm_num)
theorem B11022115 : Blo 1933435 11022115 := bstep (se 1 (by rfl) ⟨8266586, by rfl⟩ : syracuseStep 11022115 = 16533173) B16533173
theorem B14696153 : Blo 1933435 14696153 := bstep (se 2 (by rfl) ⟨5511057, by rfl⟩ : syracuseStep 14696153 = 11022115) B11022115
theorem B9797435 : Blo 1933435 9797435 := bstep (se 1 (by rfl) ⟨7348076, by rfl⟩ : syracuseStep 9797435 = 14696153) B14696153
theorem B6531623 : Blo 1933435 6531623 := bstep (se 1 (by rfl) ⟨4898717, by rfl⟩ : syracuseStep 6531623 = 9797435) B9797435
theorem B4354415 : Blo 1933435 4354415 := bstep (se 1 (by rfl) ⟨3265811, by rfl⟩ : syracuseStep 4354415 = 6531623) B6531623
theorem B2902943 : Blo 1933435 2902943 := bstep (se 1 (by rfl) ⟨2177207, by rfl⟩ : syracuseStep 2902943 = 4354415) B4354415
theorem B1935295 : Blo 1933435 1935295 := bstep (se 1 (by rfl) ⟨1451471, by rfl⟩ : syracuseStep 1935295 = 2902943) B2902943
theorem B2902949 : Blo 1933435 2902949 := bbase (se 4 (by rfl) ⟨272151, by rfl⟩ : syracuseStep 2902949 = 544303) (by norm_num)
theorem B1935299 : Blo 1933435 1935299 := bstep (se 1 (by rfl) ⟨1451474, by rfl⟩ : syracuseStep 1935299 = 2902949) B2902949
theorem B2449369 : Blo 1933435 2449369 := bbase (se 2 (by rfl) ⟨918513, by rfl⟩ : syracuseStep 2449369 = 1837027) (by norm_num)
theorem B3265825 : Blo 1933435 3265825 := bstep (se 2 (by rfl) ⟨1224684, by rfl⟩ : syracuseStep 3265825 = 2449369) B2449369
theorem B4354433 : Blo 1933435 4354433 := bstep (se 2 (by rfl) ⟨1632912, by rfl⟩ : syracuseStep 4354433 = 3265825) B3265825
theorem B2902955 : Blo 1933435 2902955 := bstep (se 1 (by rfl) ⟨2177216, by rfl⟩ : syracuseStep 2902955 = 4354433) B4354433
theorem B1935303 : Blo 1933435 1935303 := bstep (se 1 (by rfl) ⟨1451477, by rfl⟩ : syracuseStep 1935303 = 2902955) B2902955
theorem B2177221 : Blo 1933435 2177221 := bbase (se 4 (by rfl) ⟨204114, by rfl⟩ : syracuseStep 2177221 = 408229) (by norm_num)
theorem B2902961 : Blo 1933435 2902961 := bstep (se 2 (by rfl) ⟨1088610, by rfl⟩ : syracuseStep 2902961 = 2177221) B2177221
theorem B1935307 : Blo 1933435 1935307 := bstep (se 1 (by rfl) ⟨1451480, by rfl⟩ : syracuseStep 1935307 = 2902961) B2902961
theorem B3674069 : Blo 1933435 3674069 := bbase (se 7 (by rfl) ⟨43055, by rfl⟩ : syracuseStep 3674069 = 86111) (by norm_num)
theorem B2449379 : Blo 1933435 2449379 := bstep (se 1 (by rfl) ⟨1837034, by rfl⟩ : syracuseStep 2449379 = 3674069) B3674069
theorem B6531677 : Blo 1933435 6531677 := bstep (se 3 (by rfl) ⟨1224689, by rfl⟩ : syracuseStep 6531677 = 2449379) B2449379
theorem B4354451 : Blo 1933435 4354451 := bstep (se 1 (by rfl) ⟨3265838, by rfl⟩ : syracuseStep 4354451 = 6531677) B6531677
theorem B2902967 : Blo 1933435 2902967 := bstep (se 1 (by rfl) ⟨2177225, by rfl⟩ : syracuseStep 2902967 = 4354451) B4354451
theorem B1935311 : Blo 1933435 1935311 := bstep (se 1 (by rfl) ⟨1451483, by rfl⟩ : syracuseStep 1935311 = 2902967) B2902967
theorem B2902973 : Blo 1933435 2902973 := bbase (se 3 (by rfl) ⟨544307, by rfl⟩ : syracuseStep 2902973 = 1088615) (by norm_num)
theorem B1935315 : Blo 1933435 1935315 := bstep (se 1 (by rfl) ⟨1451486, by rfl⟩ : syracuseStep 1935315 = 2902973) B2902973
theorem B4354469 : Blo 1933435 4354469 := bbase (se 4 (by rfl) ⟨408231, by rfl⟩ : syracuseStep 4354469 = 816463) (by norm_num)
theorem B2902979 : Blo 1933435 2902979 := bstep (se 1 (by rfl) ⟨2177234, by rfl⟩ : syracuseStep 2902979 = 4354469) B4354469
theorem B1935319 : Blo 1933435 1935319 := bstep (se 1 (by rfl) ⟨1451489, by rfl⟩ : syracuseStep 1935319 = 2902979) B2902979
theorem B4898789 : Blo 1933435 4898789 := bbase (se 4 (by rfl) ⟨459261, by rfl⟩ : syracuseStep 4898789 = 918523) (by norm_num)
theorem B3265859 : Blo 1933435 3265859 := bstep (se 1 (by rfl) ⟨2449394, by rfl⟩ : syracuseStep 3265859 = 4898789) B4898789
theorem B2177239 : Blo 1933435 2177239 := bstep (se 1 (by rfl) ⟨1632929, by rfl⟩ : syracuseStep 2177239 = 3265859) B3265859
theorem B2902985 : Blo 1933435 2902985 := bstep (se 2 (by rfl) ⟨1088619, by rfl⟩ : syracuseStep 2902985 = 2177239) B2177239
theorem B1935323 : Blo 1933435 1935323 := bstep (se 1 (by rfl) ⟨1451492, by rfl⟩ : syracuseStep 1935323 = 2902985) B2902985
theorem B2066681 : Blo 1933435 2066681 := bbase (se 2 (by rfl) ⟨775005, by rfl⟩ : syracuseStep 2066681 = 1550011) (by norm_num)
theorem B5511149 : Blo 1933435 5511149 := bstep (se 3 (by rfl) ⟨1033340, by rfl⟩ : syracuseStep 5511149 = 2066681) B2066681
theorem B3674099 : Blo 1933435 3674099 := bstep (se 1 (by rfl) ⟨2755574, by rfl⟩ : syracuseStep 3674099 = 5511149) B5511149
theorem B9797597 : Blo 1933435 9797597 := bstep (se 3 (by rfl) ⟨1837049, by rfl⟩ : syracuseStep 9797597 = 3674099) B3674099
theorem B6531731 : Blo 1933435 6531731 := bstep (se 1 (by rfl) ⟨4898798, by rfl⟩ : syracuseStep 6531731 = 9797597) B9797597
theorem B4354487 : Blo 1933435 4354487 := bstep (se 1 (by rfl) ⟨3265865, by rfl⟩ : syracuseStep 4354487 = 6531731) B6531731
theorem B2902991 : Blo 1933435 2902991 := bstep (se 1 (by rfl) ⟨2177243, by rfl⟩ : syracuseStep 2902991 = 4354487) B4354487
theorem B1935327 : Blo 1933435 1935327 := bstep (se 1 (by rfl) ⟨1451495, by rfl⟩ : syracuseStep 1935327 = 2902991) B2902991
theorem B2902997 : Blo 1933435 2902997 := bbase (se 7 (by rfl) ⟨34019, by rfl⟩ : syracuseStep 2902997 = 68039) (by norm_num)
theorem B1935331 : Blo 1933435 1935331 := bstep (se 1 (by rfl) ⟨1451498, by rfl⟩ : syracuseStep 1935331 = 2902997) B2902997
theorem B7348229 : Blo 1933435 7348229 := bbase (se 4 (by rfl) ⟨688896, by rfl⟩ : syracuseStep 7348229 = 1377793) (by norm_num)
theorem B4898819 : Blo 1933435 4898819 := bstep (se 1 (by rfl) ⟨3674114, by rfl⟩ : syracuseStep 4898819 = 7348229) B7348229
theorem B3265879 : Blo 1933435 3265879 := bstep (se 1 (by rfl) ⟨2449409, by rfl⟩ : syracuseStep 3265879 = 4898819) B4898819
theorem B4354505 : Blo 1933435 4354505 := bstep (se 2 (by rfl) ⟨1632939, by rfl⟩ : syracuseStep 4354505 = 3265879) B3265879
theorem B2903003 : Blo 1933435 2903003 := bstep (se 1 (by rfl) ⟨2177252, by rfl⟩ : syracuseStep 2903003 = 4354505) B4354505
theorem B1935335 : Blo 1933435 1935335 := bstep (se 1 (by rfl) ⟨1451501, by rfl⟩ : syracuseStep 1935335 = 2903003) B2903003
theorem B2177257 : Blo 1933435 2177257 := bbase (se 2 (by rfl) ⟨816471, by rfl⟩ : syracuseStep 2177257 = 1632943) (by norm_num)
theorem B2903009 : Blo 1933435 2903009 := bstep (se 2 (by rfl) ⟨1088628, by rfl⟩ : syracuseStep 2903009 = 2177257) B2177257
theorem B1935339 : Blo 1933435 1935339 := bstep (se 1 (by rfl) ⟨1451504, by rfl⟩ : syracuseStep 1935339 = 2903009) B2903009
theorem B11022389 : Blo 1933435 11022389 := bbase (se 5 (by rfl) ⟨516674, by rfl⟩ : syracuseStep 11022389 = 1033349) (by norm_num)
theorem B7348259 : Blo 1933435 7348259 := bstep (se 1 (by rfl) ⟨5511194, by rfl⟩ : syracuseStep 7348259 = 11022389) B11022389
theorem B4898839 : Blo 1933435 4898839 := bstep (se 1 (by rfl) ⟨3674129, by rfl⟩ : syracuseStep 4898839 = 7348259) B7348259
theorem B6531785 : Blo 1933435 6531785 := bstep (se 2 (by rfl) ⟨2449419, by rfl⟩ : syracuseStep 6531785 = 4898839) B4898839
theorem B4354523 : Blo 1933435 4354523 := bstep (se 1 (by rfl) ⟨3265892, by rfl⟩ : syracuseStep 4354523 = 6531785) B6531785
theorem B2903015 : Blo 1933435 2903015 := bstep (se 1 (by rfl) ⟨2177261, by rfl⟩ : syracuseStep 2903015 = 4354523) B4354523
theorem B1935343 : Blo 1933435 1935343 := bstep (se 1 (by rfl) ⟨1451507, by rfl⟩ : syracuseStep 1935343 = 2903015) B2903015
theorem B2903021 : Blo 1933435 2903021 := bbase (se 3 (by rfl) ⟨544316, by rfl⟩ : syracuseStep 2903021 = 1088633) (by norm_num)
theorem B1935347 : Blo 1933435 1935347 := bstep (se 1 (by rfl) ⟨1451510, by rfl⟩ : syracuseStep 1935347 = 2903021) B2903021
theorem B4354541 : Blo 1933435 4354541 := bbase (se 3 (by rfl) ⟨816476, by rfl⟩ : syracuseStep 4354541 = 1632953) (by norm_num)
theorem B2903027 : Blo 1933435 2903027 := bstep (se 1 (by rfl) ⟨2177270, by rfl⟩ : syracuseStep 2903027 = 4354541) B4354541
theorem B1935351 : Blo 1933435 1935351 := bstep (se 1 (by rfl) ⟨1451513, by rfl⟩ : syracuseStep 1935351 = 2903027) B2903027
theorem B5302741 : Blo 1933435 5302741 := bbase (se 7 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 5302741 = 124283) (by norm_num)
theorem B7070321 : Blo 1933435 7070321 := bstep (se 2 (by rfl) ⟨2651370, by rfl⟩ : syracuseStep 7070321 = 5302741) B5302741
theorem B4713547 : Blo 1933435 4713547 := bstep (se 1 (by rfl) ⟨3535160, by rfl⟩ : syracuseStep 4713547 = 7070321) B7070321
theorem B6284729 : Blo 1933435 6284729 := bstep (se 2 (by rfl) ⟨2356773, by rfl⟩ : syracuseStep 6284729 = 4713547) B4713547
theorem B4189819 : Blo 1933435 4189819 := bstep (se 1 (by rfl) ⟨3142364, by rfl⟩ : syracuseStep 4189819 = 6284729) B6284729
theorem B5586425 : Blo 1933435 5586425 := bstep (se 2 (by rfl) ⟨2094909, by rfl⟩ : syracuseStep 5586425 = 4189819) B4189819
theorem B3724283 : Blo 1933435 3724283 := bstep (se 1 (by rfl) ⟨2793212, by rfl⟩ : syracuseStep 3724283 = 5586425) B5586425
theorem B2482855 : Blo 1933435 2482855 := bstep (se 1 (by rfl) ⟨1862141, by rfl⟩ : syracuseStep 2482855 = 3724283) B3724283
theorem B13241893 : Blo 1933435 13241893 := bstep (se 4 (by rfl) ⟨1241427, by rfl⟩ : syracuseStep 13241893 = 2482855) B2482855
theorem B17655857 : Blo 1933435 17655857 := bstep (se 2 (by rfl) ⟨6620946, by rfl⟩ : syracuseStep 17655857 = 13241893) B13241893
theorem B11770571 : Blo 1933435 11770571 := bstep (se 1 (by rfl) ⟨8827928, by rfl⟩ : syracuseStep 11770571 = 17655857) B17655857
theorem B7847047 : Blo 1933435 7847047 := bstep (se 1 (by rfl) ⟨5885285, by rfl⟩ : syracuseStep 7847047 = 11770571) B11770571
theorem B10462729 : Blo 1933435 10462729 := bstep (se 2 (by rfl) ⟨3923523, by rfl⟩ : syracuseStep 10462729 = 7847047) B7847047
theorem B13950305 : Blo 1933435 13950305 := bstep (se 2 (by rfl) ⟨5231364, by rfl⟩ : syracuseStep 13950305 = 10462729) B10462729
theorem B9300203 : Blo 1933435 9300203 := bstep (se 1 (by rfl) ⟨6975152, by rfl⟩ : syracuseStep 9300203 = 13950305) B13950305
theorem B6200135 : Blo 1933435 6200135 := bstep (se 1 (by rfl) ⟨4650101, by rfl⟩ : syracuseStep 6200135 = 9300203) B9300203
theorem B4133423 : Blo 1933435 4133423 := bstep (se 1 (by rfl) ⟨3100067, by rfl⟩ : syracuseStep 4133423 = 6200135) B6200135
theorem B2755615 : Blo 1933435 2755615 := bstep (se 1 (by rfl) ⟨2066711, by rfl⟩ : syracuseStep 2755615 = 4133423) B4133423
theorem B3674153 : Blo 1933435 3674153 := bstep (se 2 (by rfl) ⟨1377807, by rfl⟩ : syracuseStep 3674153 = 2755615) B2755615
theorem B2449435 : Blo 1933435 2449435 := bstep (se 1 (by rfl) ⟨1837076, by rfl⟩ : syracuseStep 2449435 = 3674153) B3674153
theorem B3265913 : Blo 1933435 3265913 := bstep (se 2 (by rfl) ⟨1224717, by rfl⟩ : syracuseStep 3265913 = 2449435) B2449435
theorem B2177275 : Blo 1933435 2177275 := bstep (se 1 (by rfl) ⟨1632956, by rfl⟩ : syracuseStep 2177275 = 3265913) B3265913
theorem B2903033 : Blo 1933435 2903033 := bstep (se 2 (by rfl) ⟨1088637, by rfl⟩ : syracuseStep 2903033 = 2177275) B2177275
theorem B1935355 : Blo 1933435 1935355 := bstep (se 1 (by rfl) ⟨1451516, by rfl⟩ : syracuseStep 1935355 = 2903033) B2903033
theorem B2094913 : Blo 1933435 2094913 := bbase (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) (by norm_num)
theorem B2793217 : Blo 1933435 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B3724289 : Blo 1933435 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B2482859 : Blo 1933435 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B6620957 : Blo 1933435 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B4413971 : Blo 1933435 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B2942647 : Blo 1933435 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B15694117 : Blo 1933435 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B83701957 : Blo 1933435 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B111602609 : Blo 1933435 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B74401739 : Blo 1933435 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B49601159 : Blo 1933435 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B33067439 : Blo 1933435 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B22044959 : Blo 1933435 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B14696639 : Blo 1933435 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B9797759 : Blo 1933435 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B6531839 : Blo 1933435 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B4354559 : Blo 1933435 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B2903039 : Blo 1933435 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B1935359 : Blo 1933435 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B2903045 : Blo 1933435 2903045 := bbase (se 4 (by rfl) ⟨272160, by rfl⟩ : syracuseStep 2903045 = 544321) (by norm_num)
theorem B1935363 : Blo 1933435 1935363 := bstep (se 1 (by rfl) ⟨1451522, by rfl⟩ : syracuseStep 1935363 = 2903045) B2903045
theorem B3265933 : Blo 1933435 3265933 := bbase (se 3 (by rfl) ⟨612362, by rfl⟩ : syracuseStep 3265933 = 1224725) (by norm_num)
theorem B4354577 : Blo 1933435 4354577 := bstep (se 2 (by rfl) ⟨1632966, by rfl⟩ : syracuseStep 4354577 = 3265933) B3265933
theorem B2903051 : Blo 1933435 2903051 := bstep (se 1 (by rfl) ⟨2177288, by rfl⟩ : syracuseStep 2903051 = 4354577) B4354577
theorem B1935367 : Blo 1933435 1935367 := bstep (se 1 (by rfl) ⟨1451525, by rfl⟩ : syracuseStep 1935367 = 2903051) B2903051
theorem B2177293 : Blo 1933435 2177293 := bbase (se 3 (by rfl) ⟨408242, by rfl⟩ : syracuseStep 2177293 = 816485) (by norm_num)
theorem B2903057 : Blo 1933435 2903057 := bstep (se 2 (by rfl) ⟨1088646, by rfl⟩ : syracuseStep 2903057 = 2177293) B2177293
theorem B1935371 : Blo 1933435 1935371 := bstep (se 1 (by rfl) ⟨1451528, by rfl⟩ : syracuseStep 1935371 = 2903057) B2903057
theorem B6531893 : Blo 1933435 6531893 := bbase (se 5 (by rfl) ⟨306182, by rfl⟩ : syracuseStep 6531893 = 612365) (by norm_num)
theorem B4354595 : Blo 1933435 4354595 := bstep (se 1 (by rfl) ⟨3265946, by rfl⟩ : syracuseStep 4354595 = 6531893) B6531893
theorem B2903063 : Blo 1933435 2903063 := bstep (se 1 (by rfl) ⟨2177297, by rfl⟩ : syracuseStep 2903063 = 4354595) B4354595
theorem B1935375 : Blo 1933435 1935375 := bstep (se 1 (by rfl) ⟨1451531, by rfl⟩ : syracuseStep 1935375 = 2903063) B2903063
theorem B2903069 : Blo 1933435 2903069 := bbase (se 3 (by rfl) ⟨544325, by rfl⟩ : syracuseStep 2903069 = 1088651) (by norm_num)
theorem B1935379 : Blo 1933435 1935379 := bstep (se 1 (by rfl) ⟨1451534, by rfl⟩ : syracuseStep 1935379 = 2903069) B2903069
theorem B4354613 : Blo 1933435 4354613 := bbase (se 5 (by rfl) ⟨204122, by rfl⟩ : syracuseStep 4354613 = 408245) (by norm_num)
theorem B2903075 : Blo 1933435 2903075 := bstep (se 1 (by rfl) ⟨2177306, by rfl⟩ : syracuseStep 2903075 = 4354613) B4354613
theorem B1935383 : Blo 1933435 1935383 := bstep (se 1 (by rfl) ⟨1451537, by rfl⟩ : syracuseStep 1935383 = 2903075) B2903075
theorem B8266981 : Blo 1933435 8266981 := bbase (se 4 (by rfl) ⟨775029, by rfl⟩ : syracuseStep 8266981 = 1550059) (by norm_num)
theorem B11022641 : Blo 1933435 11022641 := bstep (se 2 (by rfl) ⟨4133490, by rfl⟩ : syracuseStep 11022641 = 8266981) B8266981
theorem B7348427 : Blo 1933435 7348427 := bstep (se 1 (by rfl) ⟨5511320, by rfl⟩ : syracuseStep 7348427 = 11022641) B11022641
theorem B4898951 : Blo 1933435 4898951 := bstep (se 1 (by rfl) ⟨3674213, by rfl⟩ : syracuseStep 4898951 = 7348427) B7348427
theorem B3265967 : Blo 1933435 3265967 := bstep (se 1 (by rfl) ⟨2449475, by rfl⟩ : syracuseStep 3265967 = 4898951) B4898951
theorem B2177311 : Blo 1933435 2177311 := bstep (se 1 (by rfl) ⟨1632983, by rfl⟩ : syracuseStep 2177311 = 3265967) B3265967
theorem B2903081 : Blo 1933435 2903081 := bstep (se 2 (by rfl) ⟨1088655, by rfl⟩ : syracuseStep 2903081 = 2177311) B2177311
theorem B1935387 : Blo 1933435 1935387 := bstep (se 1 (by rfl) ⟨1451540, by rfl⟩ : syracuseStep 1935387 = 2903081) B2903081
theorem B8266997 : Blo 1933435 8266997 := bbase (se 5 (by rfl) ⟨387515, by rfl⟩ : syracuseStep 8266997 = 775031) (by norm_num)
theorem B5511331 : Blo 1933435 5511331 := bstep (se 1 (by rfl) ⟨4133498, by rfl⟩ : syracuseStep 5511331 = 8266997) B8266997
theorem B7348441 : Blo 1933435 7348441 := bstep (se 2 (by rfl) ⟨2755665, by rfl⟩ : syracuseStep 7348441 = 5511331) B5511331
theorem B9797921 : Blo 1933435 9797921 := bstep (se 2 (by rfl) ⟨3674220, by rfl⟩ : syracuseStep 9797921 = 7348441) B7348441
theorem B6531947 : Blo 1933435 6531947 := bstep (se 1 (by rfl) ⟨4898960, by rfl⟩ : syracuseStep 6531947 = 9797921) B9797921
theorem B4354631 : Blo 1933435 4354631 := bstep (se 1 (by rfl) ⟨3265973, by rfl⟩ : syracuseStep 4354631 = 6531947) B6531947
theorem B2903087 : Blo 1933435 2903087 := bstep (se 1 (by rfl) ⟨2177315, by rfl⟩ : syracuseStep 2903087 = 4354631) B4354631
theorem B1935391 : Blo 1933435 1935391 := bstep (se 1 (by rfl) ⟨1451543, by rfl⟩ : syracuseStep 1935391 = 2903087) B2903087
theorem B2903093 : Blo 1933435 2903093 := bbase (se 5 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 2903093 = 272165) (by norm_num)
theorem B1935395 : Blo 1933435 1935395 := bstep (se 1 (by rfl) ⟨1451546, by rfl⟩ : syracuseStep 1935395 = 2903093) B2903093
theorem B4898981 : Blo 1933435 4898981 := bbase (se 4 (by rfl) ⟨459279, by rfl⟩ : syracuseStep 4898981 = 918559) (by norm_num)
theorem B3265987 : Blo 1933435 3265987 := bstep (se 1 (by rfl) ⟨2449490, by rfl⟩ : syracuseStep 3265987 = 4898981) B4898981
theorem B4354649 : Blo 1933435 4354649 := bstep (se 2 (by rfl) ⟨1632993, by rfl⟩ : syracuseStep 4354649 = 3265987) B3265987
theorem B2903099 : Blo 1933435 2903099 := bstep (se 1 (by rfl) ⟨2177324, by rfl⟩ : syracuseStep 2903099 = 4354649) B4354649
theorem B1935399 : Blo 1933435 1935399 := bstep (se 1 (by rfl) ⟨1451549, by rfl⟩ : syracuseStep 1935399 = 2903099) B2903099
theorem B2177329 : Blo 1933435 2177329 := bbase (se 2 (by rfl) ⟨816498, by rfl⟩ : syracuseStep 2177329 = 1632997) (by norm_num)
theorem B2903105 : Blo 1933435 2903105 := bstep (se 2 (by rfl) ⟨1088664, by rfl⟩ : syracuseStep 2903105 = 2177329) B2177329
theorem B1935403 : Blo 1933435 1935403 := bstep (se 1 (by rfl) ⟨1451552, by rfl⟩ : syracuseStep 1935403 = 2903105) B2903105
theorem B4133533 : Blo 1933435 4133533 := bbase (se 3 (by rfl) ⟨775037, by rfl⟩ : syracuseStep 4133533 = 1550075) (by norm_num)
theorem B5511377 : Blo 1933435 5511377 := bstep (se 2 (by rfl) ⟨2066766, by rfl⟩ : syracuseStep 5511377 = 4133533) B4133533
theorem B3674251 : Blo 1933435 3674251 := bstep (se 1 (by rfl) ⟨2755688, by rfl⟩ : syracuseStep 3674251 = 5511377) B5511377
theorem B4899001 : Blo 1933435 4899001 := bstep (se 2 (by rfl) ⟨1837125, by rfl⟩ : syracuseStep 4899001 = 3674251) B3674251
theorem B6532001 : Blo 1933435 6532001 := bstep (se 2 (by rfl) ⟨2449500, by rfl⟩ : syracuseStep 6532001 = 4899001) B4899001
theorem B4354667 : Blo 1933435 4354667 := bstep (se 1 (by rfl) ⟨3266000, by rfl⟩ : syracuseStep 4354667 = 6532001) B6532001
theorem B2903111 : Blo 1933435 2903111 := bstep (se 1 (by rfl) ⟨2177333, by rfl⟩ : syracuseStep 2903111 = 4354667) B4354667
theorem B1935407 : Blo 1933435 1935407 := bstep (se 1 (by rfl) ⟨1451555, by rfl⟩ : syracuseStep 1935407 = 2903111) B2903111
theorem B2903117 : Blo 1933435 2903117 := bbase (se 3 (by rfl) ⟨544334, by rfl⟩ : syracuseStep 2903117 = 1088669) (by norm_num)
theorem B1935411 : Blo 1933435 1935411 := bstep (se 1 (by rfl) ⟨1451558, by rfl⟩ : syracuseStep 1935411 = 2903117) B2903117
theorem B4354685 : Blo 1933435 4354685 := bbase (se 3 (by rfl) ⟨816503, by rfl⟩ : syracuseStep 4354685 = 1633007) (by norm_num)
theorem B2903123 : Blo 1933435 2903123 := bstep (se 1 (by rfl) ⟨2177342, by rfl⟩ : syracuseStep 2903123 = 4354685) B4354685
theorem B1935415 : Blo 1933435 1935415 := bstep (se 1 (by rfl) ⟨1451561, by rfl⟩ : syracuseStep 1935415 = 2903123) B2903123
theorem B3266021 : Blo 1933435 3266021 := bbase (se 4 (by rfl) ⟨306189, by rfl⟩ : syracuseStep 3266021 = 612379) (by norm_num)
theorem B2177347 : Blo 1933435 2177347 := bstep (se 1 (by rfl) ⟨1633010, by rfl⟩ : syracuseStep 2177347 = 3266021) B3266021
theorem B2903129 : Blo 1933435 2903129 := bstep (se 2 (by rfl) ⟨1088673, by rfl⟩ : syracuseStep 2903129 = 2177347) B2177347
theorem B1935419 : Blo 1933435 1935419 := bstep (se 1 (by rfl) ⟨1451564, by rfl⟩ : syracuseStep 1935419 = 2903129) B2903129
theorem B39727061 : Blo 1933435 39727061 := bbase (se 7 (by rfl) ⟨465551, by rfl⟩ : syracuseStep 39727061 = 931103) (by norm_num)
theorem B26484707 : Blo 1933435 26484707 := bstep (se 1 (by rfl) ⟨19863530, by rfl⟩ : syracuseStep 26484707 = 39727061) B39727061
theorem B17656471 : Blo 1933435 17656471 := bstep (se 1 (by rfl) ⟨13242353, by rfl⟩ : syracuseStep 17656471 = 26484707) B26484707
theorem B23541961 : Blo 1933435 23541961 := bstep (se 2 (by rfl) ⟨8828235, by rfl⟩ : syracuseStep 23541961 = 17656471) B17656471
theorem B31389281 : Blo 1933435 31389281 := bstep (se 2 (by rfl) ⟨11770980, by rfl⟩ : syracuseStep 31389281 = 23541961) B23541961
theorem B20926187 : Blo 1933435 20926187 := bstep (se 1 (by rfl) ⟨15694640, by rfl⟩ : syracuseStep 20926187 = 31389281) B31389281
theorem B13950791 : Blo 1933435 13950791 := bstep (se 1 (by rfl) ⟨10463093, by rfl⟩ : syracuseStep 13950791 = 20926187) B20926187
theorem B9300527 : Blo 1933435 9300527 := bstep (se 1 (by rfl) ⟨6975395, by rfl⟩ : syracuseStep 9300527 = 13950791) B13950791
theorem B6200351 : Blo 1933435 6200351 := bstep (se 1 (by rfl) ⟨4650263, by rfl⟩ : syracuseStep 6200351 = 9300527) B9300527
theorem B4133567 : Blo 1933435 4133567 := bstep (se 1 (by rfl) ⟨3100175, by rfl⟩ : syracuseStep 4133567 = 6200351) B6200351
theorem B2755711 : Blo 1933435 2755711 := bstep (se 1 (by rfl) ⟨2066783, by rfl⟩ : syracuseStep 2755711 = 4133567) B4133567
theorem B14697125 : Blo 1933435 14697125 := bstep (se 4 (by rfl) ⟨1377855, by rfl⟩ : syracuseStep 14697125 = 2755711) B2755711
theorem B9798083 : Blo 1933435 9798083 := bstep (se 1 (by rfl) ⟨7348562, by rfl⟩ : syracuseStep 9798083 = 14697125) B14697125
theorem B6532055 : Blo 1933435 6532055 := bstep (se 1 (by rfl) ⟨4899041, by rfl⟩ : syracuseStep 6532055 = 9798083) B9798083
theorem B4354703 : Blo 1933435 4354703 := bstep (se 1 (by rfl) ⟨3266027, by rfl⟩ : syracuseStep 4354703 = 6532055) B6532055
theorem B2903135 : Blo 1933435 2903135 := bstep (se 1 (by rfl) ⟨2177351, by rfl⟩ : syracuseStep 2903135 = 4354703) B4354703
theorem B1935423 : Blo 1933435 1935423 := bstep (se 1 (by rfl) ⟨1451567, by rfl⟩ : syracuseStep 1935423 = 2903135) B2903135
theorem B2903141 : Blo 1933435 2903141 := bbase (se 4 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 2903141 = 544339) (by norm_num)
theorem B1935427 : Blo 1933435 1935427 := bstep (se 1 (by rfl) ⟨1451570, by rfl⟩ : syracuseStep 1935427 = 2903141) B2903141
theorem B3100189 : Blo 1933435 3100189 := bbase (se 3 (by rfl) ⟨581285, by rfl⟩ : syracuseStep 3100189 = 1162571) (by norm_num)
theorem B4133585 : Blo 1933435 4133585 := bstep (se 2 (by rfl) ⟨1550094, by rfl⟩ : syracuseStep 4133585 = 3100189) B3100189
theorem B2755723 : Blo 1933435 2755723 := bstep (se 1 (by rfl) ⟨2066792, by rfl⟩ : syracuseStep 2755723 = 4133585) B4133585
theorem B3674297 : Blo 1933435 3674297 := bstep (se 2 (by rfl) ⟨1377861, by rfl⟩ : syracuseStep 3674297 = 2755723) B2755723
theorem B2449531 : Blo 1933435 2449531 := bstep (se 1 (by rfl) ⟨1837148, by rfl⟩ : syracuseStep 2449531 = 3674297) B3674297
theorem B3266041 : Blo 1933435 3266041 := bstep (se 2 (by rfl) ⟨1224765, by rfl⟩ : syracuseStep 3266041 = 2449531) B2449531
theorem B4354721 : Blo 1933435 4354721 := bstep (se 2 (by rfl) ⟨1633020, by rfl⟩ : syracuseStep 4354721 = 3266041) B3266041
theorem B2903147 : Blo 1933435 2903147 := bstep (se 1 (by rfl) ⟨2177360, by rfl⟩ : syracuseStep 2903147 = 4354721) B4354721
theorem B1935431 : Blo 1933435 1935431 := bstep (se 1 (by rfl) ⟨1451573, by rfl⟩ : syracuseStep 1935431 = 2903147) B2903147
theorem B2177365 : Blo 1933435 2177365 := bbase (se 10 (by rfl) ⟨3189, by rfl⟩ : syracuseStep 2177365 = 6379) (by norm_num)
theorem B2903153 : Blo 1933435 2903153 := bstep (se 2 (by rfl) ⟨1088682, by rfl⟩ : syracuseStep 2903153 = 2177365) B2177365
theorem B1935435 : Blo 1933435 1935435 := bstep (se 1 (by rfl) ⟨1451576, by rfl⟩ : syracuseStep 1935435 = 2903153) B2903153
theorem C0 (j : ℕ) (h1 : 483358 ≤ j) (h2 : j ≤ 483858) : Blo 1933435 (4 * j + 3) := by
  interval_cases j
  · exact B1933435
  · exact B1933439
  · exact B1933443
  · exact B1933447
  · exact B1933451
  · exact B1933455
  · exact B1933459
  · exact B1933463
  · exact B1933467
  · exact B1933471
  · exact B1933475
  · exact B1933479
  · exact B1933483
  · exact B1933487
  · exact B1933491
  · exact B1933495
  · exact B1933499
  · exact B1933503
  · exact B1933507
  · exact B1933511
  · exact B1933515
  · exact B1933519
  · exact B1933523
  · exact B1933527
  · exact B1933531
  · exact B1933535
  · exact B1933539
  · exact B1933543
  · exact B1933547
  · exact B1933551
  · exact B1933555
  · exact B1933559
  · exact B1933563
  · exact B1933567
  · exact B1933571
  · exact B1933575
  · exact B1933579
  · exact B1933583
  · exact B1933587
  · exact B1933591
  · exact B1933595
  · exact B1933599
  · exact B1933603
  · exact B1933607
  · exact B1933611
  · exact B1933615
  · exact B1933619
  · exact B1933623
  · exact B1933627
  · exact B1933631
  · exact B1933635
  · exact B1933639
  · exact B1933643
  · exact B1933647
  · exact B1933651
  · exact B1933655
  · exact B1933659
  · exact B1933663
  · exact B1933667
  · exact B1933671
  · exact B1933675
  · exact B1933679
  · exact B1933683
  · exact B1933687
  · exact B1933691
  · exact B1933695
  · exact B1933699
  · exact B1933703
  · exact B1933707
  · exact B1933711
  · exact B1933715
  · exact B1933719
  · exact B1933723
  · exact B1933727
  · exact B1933731
  · exact B1933735
  · exact B1933739
  · exact B1933743
  · exact B1933747
  · exact B1933751
  · exact B1933755
  · exact B1933759
  · exact B1933763
  · exact B1933767
  · exact B1933771
  · exact B1933775
  · exact B1933779
  · exact B1933783
  · exact B1933787
  · exact B1933791
  · exact B1933795
  · exact B1933799
  · exact B1933803
  · exact B1933807
  · exact B1933811
  · exact B1933815
  · exact B1933819
  · exact B1933823
  · exact B1933827
  · exact B1933831
  · exact B1933835
  · exact B1933839
  · exact B1933843
  · exact B1933847
  · exact B1933851
  · exact B1933855
  · exact B1933859
  · exact B1933863
  · exact B1933867
  · exact B1933871
  · exact B1933875
  · exact B1933879
  · exact B1933883
  · exact B1933887
  · exact B1933891
  · exact B1933895
  · exact B1933899
  · exact B1933903
  · exact B1933907
  · exact B1933911
  · exact B1933915
  · exact B1933919
  · exact B1933923
  · exact B1933927
  · exact B1933931
  · exact B1933935
  · exact B1933939
  · exact B1933943
  · exact B1933947
  · exact B1933951
  · exact B1933955
  · exact B1933959
  · exact B1933963
  · exact B1933967
  · exact B1933971
  · exact B1933975
  · exact B1933979
  · exact B1933983
  · exact B1933987
  · exact B1933991
  · exact B1933995
  · exact B1933999
  · exact B1934003
  · exact B1934007
  · exact B1934011
  · exact B1934015
  · exact B1934019
  · exact B1934023
  · exact B1934027
  · exact B1934031
  · exact B1934035
  · exact B1934039
  · exact B1934043
  · exact B1934047
  · exact B1934051
  · exact B1934055
  · exact B1934059
  · exact B1934063
  · exact B1934067
  · exact B1934071
  · exact B1934075
  · exact B1934079
  · exact B1934083
  · exact B1934087
  · exact B1934091
  · exact B1934095
  · exact B1934099
  · exact B1934103
  · exact B1934107
  · exact B1934111
  · exact B1934115
  · exact B1934119
  · exact B1934123
  · exact B1934127
  · exact B1934131
  · exact B1934135
  · exact B1934139
  · exact B1934143
  · exact B1934147
  · exact B1934151
  · exact B1934155
  · exact B1934159
  · exact B1934163
  · exact B1934167
  · exact B1934171
  · exact B1934175
  · exact B1934179
  · exact B1934183
  · exact B1934187
  · exact B1934191
  · exact B1934195
  · exact B1934199
  · exact B1934203
  · exact B1934207
  · exact B1934211
  · exact B1934215
  · exact B1934219
  · exact B1934223
  · exact B1934227
  · exact B1934231
  · exact B1934235
  · exact B1934239
  · exact B1934243
  · exact B1934247
  · exact B1934251
  · exact B1934255
  · exact B1934259
  · exact B1934263
  · exact B1934267
  · exact B1934271
  · exact B1934275
  · exact B1934279
  · exact B1934283
  · exact B1934287
  · exact B1934291
  · exact B1934295
  · exact B1934299
  · exact B1934303
  · exact B1934307
  · exact B1934311
  · exact B1934315
  · exact B1934319
  · exact B1934323
  · exact B1934327
  · exact B1934331
  · exact B1934335
  · exact B1934339
  · exact B1934343
  · exact B1934347
  · exact B1934351
  · exact B1934355
  · exact B1934359
  · exact B1934363
  · exact B1934367
  · exact B1934371
  · exact B1934375
  · exact B1934379
  · exact B1934383
  · exact B1934387
  · exact B1934391
  · exact B1934395
  · exact B1934399
  · exact B1934403
  · exact B1934407
  · exact B1934411
  · exact B1934415
  · exact B1934419
  · exact B1934423
  · exact B1934427
  · exact B1934431
  · exact B1934435
  · exact B1934439
  · exact B1934443
  · exact B1934447
  · exact B1934451
  · exact B1934455
  · exact B1934459
  · exact B1934463
  · exact B1934467
  · exact B1934471
  · exact B1934475
  · exact B1934479
  · exact B1934483
  · exact B1934487
  · exact B1934491
  · exact B1934495
  · exact B1934499
  · exact B1934503
  · exact B1934507
  · exact B1934511
  · exact B1934515
  · exact B1934519
  · exact B1934523
  · exact B1934527
  · exact B1934531
  · exact B1934535
  · exact B1934539
  · exact B1934543
  · exact B1934547
  · exact B1934551
  · exact B1934555
  · exact B1934559
  · exact B1934563
  · exact B1934567
  · exact B1934571
  · exact B1934575
  · exact B1934579
  · exact B1934583
  · exact B1934587
  · exact B1934591
  · exact B1934595
  · exact B1934599
  · exact B1934603
  · exact B1934607
  · exact B1934611
  · exact B1934615
  · exact B1934619
  · exact B1934623
  · exact B1934627
  · exact B1934631
  · exact B1934635
  · exact B1934639
  · exact B1934643
  · exact B1934647
  · exact B1934651
  · exact B1934655
  · exact B1934659
  · exact B1934663
  · exact B1934667
  · exact B1934671
  · exact B1934675
  · exact B1934679
  · exact B1934683
  · exact B1934687
  · exact B1934691
  · exact B1934695
  · exact B1934699
  · exact B1934703
  · exact B1934707
  · exact B1934711
  · exact B1934715
  · exact B1934719
  · exact B1934723
  · exact B1934727
  · exact B1934731
  · exact B1934735
  · exact B1934739
  · exact B1934743
  · exact B1934747
  · exact B1934751
  · exact B1934755
  · exact B1934759
  · exact B1934763
  · exact B1934767
  · exact B1934771
  · exact B1934775
  · exact B1934779
  · exact B1934783
  · exact B1934787
  · exact B1934791
  · exact B1934795
  · exact B1934799
  · exact B1934803
  · exact B1934807
  · exact B1934811
  · exact B1934815
  · exact B1934819
  · exact B1934823
  · exact B1934827
  · exact B1934831
  · exact B1934835
  · exact B1934839
  · exact B1934843
  · exact B1934847
  · exact B1934851
  · exact B1934855
  · exact B1934859
  · exact B1934863
  · exact B1934867
  · exact B1934871
  · exact B1934875
  · exact B1934879
  · exact B1934883
  · exact B1934887
  · exact B1934891
  · exact B1934895
  · exact B1934899
  · exact B1934903
  · exact B1934907
  · exact B1934911
  · exact B1934915
  · exact B1934919
  · exact B1934923
  · exact B1934927
  · exact B1934931
  · exact B1934935
  · exact B1934939
  · exact B1934943
  · exact B1934947
  · exact B1934951
  · exact B1934955
  · exact B1934959
  · exact B1934963
  · exact B1934967
  · exact B1934971
  · exact B1934975
  · exact B1934979
  · exact B1934983
  · exact B1934987
  · exact B1934991
  · exact B1934995
  · exact B1934999
  · exact B1935003
  · exact B1935007
  · exact B1935011
  · exact B1935015
  · exact B1935019
  · exact B1935023
  · exact B1935027
  · exact B1935031
  · exact B1935035
  · exact B1935039
  · exact B1935043
  · exact B1935047
  · exact B1935051
  · exact B1935055
  · exact B1935059
  · exact B1935063
  · exact B1935067
  · exact B1935071
  · exact B1935075
  · exact B1935079
  · exact B1935083
  · exact B1935087
  · exact B1935091
  · exact B1935095
  · exact B1935099
  · exact B1935103
  · exact B1935107
  · exact B1935111
  · exact B1935115
  · exact B1935119
  · exact B1935123
  · exact B1935127
  · exact B1935131
  · exact B1935135
  · exact B1935139
  · exact B1935143
  · exact B1935147
  · exact B1935151
  · exact B1935155
  · exact B1935159
  · exact B1935163
  · exact B1935167
  · exact B1935171
  · exact B1935175
  · exact B1935179
  · exact B1935183
  · exact B1935187
  · exact B1935191
  · exact B1935195
  · exact B1935199
  · exact B1935203
  · exact B1935207
  · exact B1935211
  · exact B1935215
  · exact B1935219
  · exact B1935223
  · exact B1935227
  · exact B1935231
  · exact B1935235
  · exact B1935239
  · exact B1935243
  · exact B1935247
  · exact B1935251
  · exact B1935255
  · exact B1935259
  · exact B1935263
  · exact B1935267
  · exact B1935271
  · exact B1935275
  · exact B1935279
  · exact B1935283
  · exact B1935287
  · exact B1935291
  · exact B1935295
  · exact B1935299
  · exact B1935303
  · exact B1935307
  · exact B1935311
  · exact B1935315
  · exact B1935319
  · exact B1935323
  · exact B1935327
  · exact B1935331
  · exact B1935335
  · exact B1935339
  · exact B1935343
  · exact B1935347
  · exact B1935351
  · exact B1935355
  · exact B1935359
  · exact B1935363
  · exact B1935367
  · exact B1935371
  · exact B1935375
  · exact B1935379
  · exact B1935383
  · exact B1935387
  · exact B1935391
  · exact B1935395
  · exact B1935399
  · exact B1935403
  · exact B1935407
  · exact B1935411
  · exact B1935415
  · exact B1935419
  · exact B1935423
  · exact B1935427
  · exact B1935431
  · exact B1935435
theorem solution (m : ℕ) (hlo : 1933435 ≤ m) (hhi : m ≤ 1935435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 483358 ≤ j := by omega
    have hj2 : j ≤ 483858 := by omega
    have hb : Blo 1933435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
