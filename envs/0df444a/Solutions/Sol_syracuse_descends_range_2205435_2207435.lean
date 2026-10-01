-- Prove2me | solution 1 for syracuse_descends_range_2205435_2207435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:23.55465+00:00
-- url     : https://prove2.me/submissions/a49ad031-a6e5-4143-b188-e67231f34c74

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

theorem B6280325 : Blo 2205435 6280325 := bbase (se 4 (by rfl) ⟨588780, by rfl⟩ : syracuseStep 6280325 = 1177561) (by norm_num)
theorem B4186883 : Blo 2205435 4186883 := bstep (se 1 (by rfl) ⟨3140162, by rfl⟩ : syracuseStep 4186883 = 6280325) B6280325
theorem B2791255 : Blo 2205435 2791255 := bstep (se 1 (by rfl) ⟨2093441, by rfl⟩ : syracuseStep 2791255 = 4186883) B4186883
theorem B3721673 : Blo 2205435 3721673 := bstep (se 2 (by rfl) ⟨1395627, by rfl⟩ : syracuseStep 3721673 = 2791255) B2791255
theorem B2481115 : Blo 2205435 2481115 := bstep (se 1 (by rfl) ⟨1860836, by rfl⟩ : syracuseStep 2481115 = 3721673) B3721673
theorem B3308153 : Blo 2205435 3308153 := bstep (se 2 (by rfl) ⟨1240557, by rfl⟩ : syracuseStep 3308153 = 2481115) B2481115
theorem B2205435 : Blo 2205435 2205435 := bstep (se 1 (by rfl) ⟨1654076, by rfl⟩ : syracuseStep 2205435 = 3308153) B3308153
theorem B7948549 : Blo 2205435 7948549 := bbase (se 4 (by rfl) ⟨745176, by rfl⟩ : syracuseStep 7948549 = 1490353) (by norm_num)
theorem B42392261 : Blo 2205435 42392261 := bstep (se 4 (by rfl) ⟨3974274, by rfl⟩ : syracuseStep 42392261 = 7948549) B7948549
theorem B28261507 : Blo 2205435 28261507 := bstep (se 1 (by rfl) ⟨21196130, by rfl⟩ : syracuseStep 28261507 = 42392261) B42392261
theorem B37682009 : Blo 2205435 37682009 := bstep (se 2 (by rfl) ⟨14130753, by rfl⟩ : syracuseStep 37682009 = 28261507) B28261507
theorem B25121339 : Blo 2205435 25121339 := bstep (se 1 (by rfl) ⟨18841004, by rfl⟩ : syracuseStep 25121339 = 37682009) B37682009
theorem B16747559 : Blo 2205435 16747559 := bstep (se 1 (by rfl) ⟨12560669, by rfl⟩ : syracuseStep 16747559 = 25121339) B25121339
theorem B11165039 : Blo 2205435 11165039 := bstep (se 1 (by rfl) ⟨8373779, by rfl⟩ : syracuseStep 11165039 = 16747559) B16747559
theorem B7443359 : Blo 2205435 7443359 := bstep (se 1 (by rfl) ⟨5582519, by rfl⟩ : syracuseStep 7443359 = 11165039) B11165039
theorem B4962239 : Blo 2205435 4962239 := bstep (se 1 (by rfl) ⟨3721679, by rfl⟩ : syracuseStep 4962239 = 7443359) B7443359
theorem B3308159 : Blo 2205435 3308159 := bstep (se 1 (by rfl) ⟨2481119, by rfl⟩ : syracuseStep 3308159 = 4962239) B4962239
theorem B2205439 : Blo 2205435 2205439 := bstep (se 1 (by rfl) ⟨1654079, by rfl⟩ : syracuseStep 2205439 = 3308159) B3308159
theorem B3308165 : Blo 2205435 3308165 := bbase (se 4 (by rfl) ⟨310140, by rfl⟩ : syracuseStep 3308165 = 620281) (by norm_num)
theorem B2205443 : Blo 2205435 2205443 := bstep (se 1 (by rfl) ⟨1654082, by rfl⟩ : syracuseStep 2205443 = 3308165) B3308165
theorem B3721693 : Blo 2205435 3721693 := bbase (se 3 (by rfl) ⟨697817, by rfl⟩ : syracuseStep 3721693 = 1395635) (by norm_num)
theorem B4962257 : Blo 2205435 4962257 := bstep (se 2 (by rfl) ⟨1860846, by rfl⟩ : syracuseStep 4962257 = 3721693) B3721693
theorem B3308171 : Blo 2205435 3308171 := bstep (se 1 (by rfl) ⟨2481128, by rfl⟩ : syracuseStep 3308171 = 4962257) B4962257
theorem B2205447 : Blo 2205435 2205447 := bstep (se 1 (by rfl) ⟨1654085, by rfl⟩ : syracuseStep 2205447 = 3308171) B3308171
theorem B2481133 : Blo 2205435 2481133 := bbase (se 3 (by rfl) ⟨465212, by rfl⟩ : syracuseStep 2481133 = 930425) (by norm_num)
theorem B3308177 : Blo 2205435 3308177 := bstep (se 2 (by rfl) ⟨1240566, by rfl⟩ : syracuseStep 3308177 = 2481133) B2481133
theorem B2205451 : Blo 2205435 2205451 := bstep (se 1 (by rfl) ⟨1654088, by rfl⟩ : syracuseStep 2205451 = 3308177) B3308177
theorem B7443413 : Blo 2205435 7443413 := bbase (se 7 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 7443413 = 174455) (by norm_num)
theorem B4962275 : Blo 2205435 4962275 := bstep (se 1 (by rfl) ⟨3721706, by rfl⟩ : syracuseStep 4962275 = 7443413) B7443413
theorem B3308183 : Blo 2205435 3308183 := bstep (se 1 (by rfl) ⟨2481137, by rfl⟩ : syracuseStep 3308183 = 4962275) B4962275
theorem B2205455 : Blo 2205435 2205455 := bstep (se 1 (by rfl) ⟨1654091, by rfl⟩ : syracuseStep 2205455 = 3308183) B3308183
theorem B3308189 : Blo 2205435 3308189 := bbase (se 3 (by rfl) ⟨620285, by rfl⟩ : syracuseStep 3308189 = 1240571) (by norm_num)
theorem B2205459 : Blo 2205435 2205459 := bstep (se 1 (by rfl) ⟨1654094, by rfl⟩ : syracuseStep 2205459 = 3308189) B3308189
theorem B4962293 : Blo 2205435 4962293 := bbase (se 5 (by rfl) ⟨232607, by rfl⟩ : syracuseStep 4962293 = 465215) (by norm_num)
theorem B3308195 : Blo 2205435 3308195 := bstep (se 1 (by rfl) ⟨2481146, by rfl⟩ : syracuseStep 3308195 = 4962293) B4962293
theorem B2205463 : Blo 2205435 2205463 := bstep (se 1 (by rfl) ⟨1654097, by rfl⟩ : syracuseStep 2205463 = 3308195) B3308195
theorem B4028549 : Blo 2205435 4028549 := bbase (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) (by norm_num)
theorem B10742797 : Blo 2205435 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B14323729 : Blo 2205435 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B19098305 : Blo 2205435 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B12732203 : Blo 2205435 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B33952541 : Blo 2205435 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B90540109 : Blo 2205435 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B120720145 : Blo 2205435 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B160960193 : Blo 2205435 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B107306795 : Blo 2205435 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B71537863 : Blo 2205435 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B95383817 : Blo 2205435 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B63589211 : Blo 2205435 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B42392807 : Blo 2205435 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B28261871 : Blo 2205435 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B18841247 : Blo 2205435 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B12560831 : Blo 2205435 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B8373887 : Blo 2205435 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B5582591 : Blo 2205435 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B3721727 : Blo 2205435 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B2481151 : Blo 2205435 2481151 := bstep (se 1 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 2481151 = 3721727) B3721727
theorem B3308201 : Blo 2205435 3308201 := bstep (se 2 (by rfl) ⟨1240575, by rfl⟩ : syracuseStep 3308201 = 2481151) B2481151
theorem B2205467 : Blo 2205435 2205467 := bstep (se 1 (by rfl) ⟨1654100, by rfl⟩ : syracuseStep 2205467 = 3308201) B3308201
theorem B3140213 : Blo 2205435 3140213 := bbase (se 5 (by rfl) ⟨147197, by rfl⟩ : syracuseStep 3140213 = 294395) (by norm_num)
theorem B8373901 : Blo 2205435 8373901 := bstep (se 3 (by rfl) ⟨1570106, by rfl⟩ : syracuseStep 8373901 = 3140213) B3140213
theorem B11165201 : Blo 2205435 11165201 := bstep (se 2 (by rfl) ⟨4186950, by rfl⟩ : syracuseStep 11165201 = 8373901) B8373901
theorem B7443467 : Blo 2205435 7443467 := bstep (se 1 (by rfl) ⟨5582600, by rfl⟩ : syracuseStep 7443467 = 11165201) B11165201
theorem B4962311 : Blo 2205435 4962311 := bstep (se 1 (by rfl) ⟨3721733, by rfl⟩ : syracuseStep 4962311 = 7443467) B7443467
theorem B3308207 : Blo 2205435 3308207 := bstep (se 1 (by rfl) ⟨2481155, by rfl⟩ : syracuseStep 3308207 = 4962311) B4962311
theorem B2205471 : Blo 2205435 2205471 := bstep (se 1 (by rfl) ⟨1654103, by rfl⟩ : syracuseStep 2205471 = 3308207) B3308207
theorem B3308213 : Blo 2205435 3308213 := bbase (se 5 (by rfl) ⟨155072, by rfl⟩ : syracuseStep 3308213 = 310145) (by norm_num)
theorem B2205475 : Blo 2205435 2205475 := bstep (se 1 (by rfl) ⟨1654106, by rfl⟩ : syracuseStep 2205475 = 3308213) B3308213
theorem B5582621 : Blo 2205435 5582621 := bbase (se 3 (by rfl) ⟨1046741, by rfl⟩ : syracuseStep 5582621 = 2093483) (by norm_num)
theorem B3721747 : Blo 2205435 3721747 := bstep (se 1 (by rfl) ⟨2791310, by rfl⟩ : syracuseStep 3721747 = 5582621) B5582621
theorem B4962329 : Blo 2205435 4962329 := bstep (se 2 (by rfl) ⟨1860873, by rfl⟩ : syracuseStep 4962329 = 3721747) B3721747
theorem B3308219 : Blo 2205435 3308219 := bstep (se 1 (by rfl) ⟨2481164, by rfl⟩ : syracuseStep 3308219 = 4962329) B4962329
theorem B2205479 : Blo 2205435 2205479 := bstep (se 1 (by rfl) ⟨1654109, by rfl⟩ : syracuseStep 2205479 = 3308219) B3308219
theorem B2481169 : Blo 2205435 2481169 := bbase (se 2 (by rfl) ⟨930438, by rfl⟩ : syracuseStep 2481169 = 1860877) (by norm_num)
theorem B3308225 : Blo 2205435 3308225 := bstep (se 2 (by rfl) ⟨1240584, by rfl⟩ : syracuseStep 3308225 = 2481169) B2481169
theorem B2205483 : Blo 2205435 2205483 := bstep (se 1 (by rfl) ⟨1654112, by rfl⟩ : syracuseStep 2205483 = 3308225) B3308225
theorem B4186981 : Blo 2205435 4186981 := bbase (se 4 (by rfl) ⟨392529, by rfl⟩ : syracuseStep 4186981 = 785059) (by norm_num)
theorem B5582641 : Blo 2205435 5582641 := bstep (se 2 (by rfl) ⟨2093490, by rfl⟩ : syracuseStep 5582641 = 4186981) B4186981
theorem B7443521 : Blo 2205435 7443521 := bstep (se 2 (by rfl) ⟨2791320, by rfl⟩ : syracuseStep 7443521 = 5582641) B5582641
theorem B4962347 : Blo 2205435 4962347 := bstep (se 1 (by rfl) ⟨3721760, by rfl⟩ : syracuseStep 4962347 = 7443521) B7443521
theorem B3308231 : Blo 2205435 3308231 := bstep (se 1 (by rfl) ⟨2481173, by rfl⟩ : syracuseStep 3308231 = 4962347) B4962347
theorem B2205487 : Blo 2205435 2205487 := bstep (se 1 (by rfl) ⟨1654115, by rfl⟩ : syracuseStep 2205487 = 3308231) B3308231
theorem B3308237 : Blo 2205435 3308237 := bbase (se 3 (by rfl) ⟨620294, by rfl⟩ : syracuseStep 3308237 = 1240589) (by norm_num)
theorem B2205491 : Blo 2205435 2205491 := bstep (se 1 (by rfl) ⟨1654118, by rfl⟩ : syracuseStep 2205491 = 3308237) B3308237
theorem B4962365 : Blo 2205435 4962365 := bbase (se 3 (by rfl) ⟨930443, by rfl⟩ : syracuseStep 4962365 = 1860887) (by norm_num)
theorem B3308243 : Blo 2205435 3308243 := bstep (se 1 (by rfl) ⟨2481182, by rfl⟩ : syracuseStep 3308243 = 4962365) B4962365
theorem B2205495 : Blo 2205435 2205495 := bstep (se 1 (by rfl) ⟨1654121, by rfl⟩ : syracuseStep 2205495 = 3308243) B3308243
theorem B3721781 : Blo 2205435 3721781 := bbase (se 5 (by rfl) ⟨174458, by rfl⟩ : syracuseStep 3721781 = 348917) (by norm_num)
theorem B2481187 : Blo 2205435 2481187 := bstep (se 1 (by rfl) ⟨1860890, by rfl⟩ : syracuseStep 2481187 = 3721781) B3721781
theorem B3308249 : Blo 2205435 3308249 := bstep (se 2 (by rfl) ⟨1240593, by rfl⟩ : syracuseStep 3308249 = 2481187) B2481187
theorem B2205499 : Blo 2205435 2205499 := bstep (se 1 (by rfl) ⟨1654124, by rfl⟩ : syracuseStep 2205499 = 3308249) B3308249
theorem B6280517 : Blo 2205435 6280517 := bbase (se 4 (by rfl) ⟨588798, by rfl⟩ : syracuseStep 6280517 = 1177597) (by norm_num)
theorem B16748045 : Blo 2205435 16748045 := bstep (se 3 (by rfl) ⟨3140258, by rfl⟩ : syracuseStep 16748045 = 6280517) B6280517
theorem B11165363 : Blo 2205435 11165363 := bstep (se 1 (by rfl) ⟨8374022, by rfl⟩ : syracuseStep 11165363 = 16748045) B16748045
theorem B7443575 : Blo 2205435 7443575 := bstep (se 1 (by rfl) ⟨5582681, by rfl⟩ : syracuseStep 7443575 = 11165363) B11165363
theorem B4962383 : Blo 2205435 4962383 := bstep (se 1 (by rfl) ⟨3721787, by rfl⟩ : syracuseStep 4962383 = 7443575) B7443575
theorem B3308255 : Blo 2205435 3308255 := bstep (se 1 (by rfl) ⟨2481191, by rfl⟩ : syracuseStep 3308255 = 4962383) B4962383
theorem B2205503 : Blo 2205435 2205503 := bstep (se 1 (by rfl) ⟨1654127, by rfl⟩ : syracuseStep 2205503 = 3308255) B3308255
theorem B3308261 : Blo 2205435 3308261 := bbase (se 4 (by rfl) ⟨310149, by rfl⟩ : syracuseStep 3308261 = 620299) (by norm_num)
theorem B2205507 : Blo 2205435 2205507 := bstep (se 1 (by rfl) ⟨1654130, by rfl⟩ : syracuseStep 2205507 = 3308261) B3308261
theorem B3532805 : Blo 2205435 3532805 := bbase (se 4 (by rfl) ⟨331200, by rfl⟩ : syracuseStep 3532805 = 662401) (by norm_num)
theorem B2355203 : Blo 2205435 2355203 := bstep (se 1 (by rfl) ⟨1766402, by rfl⟩ : syracuseStep 2355203 = 3532805) B3532805
theorem B6280541 : Blo 2205435 6280541 := bstep (se 3 (by rfl) ⟨1177601, by rfl⟩ : syracuseStep 6280541 = 2355203) B2355203
theorem B4187027 : Blo 2205435 4187027 := bstep (se 1 (by rfl) ⟨3140270, by rfl⟩ : syracuseStep 4187027 = 6280541) B6280541
theorem B2791351 : Blo 2205435 2791351 := bstep (se 1 (by rfl) ⟨2093513, by rfl⟩ : syracuseStep 2791351 = 4187027) B4187027
theorem B3721801 : Blo 2205435 3721801 := bstep (se 2 (by rfl) ⟨1395675, by rfl⟩ : syracuseStep 3721801 = 2791351) B2791351
theorem B4962401 : Blo 2205435 4962401 := bstep (se 2 (by rfl) ⟨1860900, by rfl⟩ : syracuseStep 4962401 = 3721801) B3721801
theorem B3308267 : Blo 2205435 3308267 := bstep (se 1 (by rfl) ⟨2481200, by rfl⟩ : syracuseStep 3308267 = 4962401) B4962401
theorem B2205511 : Blo 2205435 2205511 := bstep (se 1 (by rfl) ⟨1654133, by rfl⟩ : syracuseStep 2205511 = 3308267) B3308267
theorem B2481205 : Blo 2205435 2481205 := bbase (se 5 (by rfl) ⟨116306, by rfl⟩ : syracuseStep 2481205 = 232613) (by norm_num)
theorem B3308273 : Blo 2205435 3308273 := bstep (se 2 (by rfl) ⟨1240602, by rfl⟩ : syracuseStep 3308273 = 2481205) B2481205
theorem B2205515 : Blo 2205435 2205515 := bstep (se 1 (by rfl) ⟨1654136, by rfl⟩ : syracuseStep 2205515 = 3308273) B3308273
theorem B2791361 : Blo 2205435 2791361 := bbase (se 2 (by rfl) ⟨1046760, by rfl⟩ : syracuseStep 2791361 = 2093521) (by norm_num)
theorem B7443629 : Blo 2205435 7443629 := bstep (se 3 (by rfl) ⟨1395680, by rfl⟩ : syracuseStep 7443629 = 2791361) B2791361
theorem B4962419 : Blo 2205435 4962419 := bstep (se 1 (by rfl) ⟨3721814, by rfl⟩ : syracuseStep 4962419 = 7443629) B7443629
theorem B3308279 : Blo 2205435 3308279 := bstep (se 1 (by rfl) ⟨2481209, by rfl⟩ : syracuseStep 3308279 = 4962419) B4962419
theorem B2205519 : Blo 2205435 2205519 := bstep (se 1 (by rfl) ⟨1654139, by rfl⟩ : syracuseStep 2205519 = 3308279) B3308279
theorem B3308285 : Blo 2205435 3308285 := bbase (se 3 (by rfl) ⟨620303, by rfl⟩ : syracuseStep 3308285 = 1240607) (by norm_num)
theorem B2205523 : Blo 2205435 2205523 := bstep (se 1 (by rfl) ⟨1654142, by rfl⟩ : syracuseStep 2205523 = 3308285) B3308285
theorem B4962437 : Blo 2205435 4962437 := bbase (se 4 (by rfl) ⟨465228, by rfl⟩ : syracuseStep 4962437 = 930457) (by norm_num)
theorem B3308291 : Blo 2205435 3308291 := bstep (se 1 (by rfl) ⟨2481218, by rfl⟩ : syracuseStep 3308291 = 4962437) B4962437
theorem B2205527 : Blo 2205435 2205527 := bstep (se 1 (by rfl) ⟨1654145, by rfl⟩ : syracuseStep 2205527 = 3308291) B3308291
theorem B3532837 : Blo 2205435 3532837 := bbase (se 4 (by rfl) ⟨331203, by rfl⟩ : syracuseStep 3532837 = 662407) (by norm_num)
theorem B4710449 : Blo 2205435 4710449 := bstep (se 2 (by rfl) ⟨1766418, by rfl⟩ : syracuseStep 4710449 = 3532837) B3532837
theorem B3140299 : Blo 2205435 3140299 := bstep (se 1 (by rfl) ⟨2355224, by rfl⟩ : syracuseStep 3140299 = 4710449) B4710449
theorem B4187065 : Blo 2205435 4187065 := bstep (se 2 (by rfl) ⟨1570149, by rfl⟩ : syracuseStep 4187065 = 3140299) B3140299
theorem B5582753 : Blo 2205435 5582753 := bstep (se 2 (by rfl) ⟨2093532, by rfl⟩ : syracuseStep 5582753 = 4187065) B4187065
theorem B3721835 : Blo 2205435 3721835 := bstep (se 1 (by rfl) ⟨2791376, by rfl⟩ : syracuseStep 3721835 = 5582753) B5582753
theorem B2481223 : Blo 2205435 2481223 := bstep (se 1 (by rfl) ⟨1860917, by rfl⟩ : syracuseStep 2481223 = 3721835) B3721835
theorem B3308297 : Blo 2205435 3308297 := bstep (se 2 (by rfl) ⟨1240611, by rfl⟩ : syracuseStep 3308297 = 2481223) B2481223
theorem B2205531 : Blo 2205435 2205531 := bstep (se 1 (by rfl) ⟨1654148, by rfl⟩ : syracuseStep 2205531 = 3308297) B3308297
theorem B11165525 : Blo 2205435 11165525 := bbase (se 9 (by rfl) ⟨32711, by rfl⟩ : syracuseStep 11165525 = 65423) (by norm_num)
theorem B7443683 : Blo 2205435 7443683 := bstep (se 1 (by rfl) ⟨5582762, by rfl⟩ : syracuseStep 7443683 = 11165525) B11165525
theorem B4962455 : Blo 2205435 4962455 := bstep (se 1 (by rfl) ⟨3721841, by rfl⟩ : syracuseStep 4962455 = 7443683) B7443683
theorem B3308303 : Blo 2205435 3308303 := bstep (se 1 (by rfl) ⟨2481227, by rfl⟩ : syracuseStep 3308303 = 4962455) B4962455
theorem B2205535 : Blo 2205435 2205535 := bstep (se 1 (by rfl) ⟨1654151, by rfl⟩ : syracuseStep 2205535 = 3308303) B3308303
theorem B3308309 : Blo 2205435 3308309 := bbase (se 6 (by rfl) ⟨77538, by rfl⟩ : syracuseStep 3308309 = 155077) (by norm_num)
theorem B2205539 : Blo 2205435 2205539 := bstep (se 1 (by rfl) ⟨1654154, by rfl⟩ : syracuseStep 2205539 = 3308309) B3308309
theorem B7545269 : Blo 2205435 7545269 := bbase (se 5 (by rfl) ⟨353684, by rfl⟩ : syracuseStep 7545269 = 707369) (by norm_num)
theorem B20120717 : Blo 2205435 20120717 := bstep (se 3 (by rfl) ⟨3772634, by rfl⟩ : syracuseStep 20120717 = 7545269) B7545269
theorem B13413811 : Blo 2205435 13413811 := bstep (se 1 (by rfl) ⟨10060358, by rfl⟩ : syracuseStep 13413811 = 20120717) B20120717
theorem B17885081 : Blo 2205435 17885081 := bstep (se 2 (by rfl) ⟨6706905, by rfl⟩ : syracuseStep 17885081 = 13413811) B13413811
theorem B47693549 : Blo 2205435 47693549 := bstep (se 3 (by rfl) ⟨8942540, by rfl⟩ : syracuseStep 47693549 = 17885081) B17885081
theorem B31795699 : Blo 2205435 31795699 := bstep (se 1 (by rfl) ⟨23846774, by rfl⟩ : syracuseStep 31795699 = 47693549) B47693549
theorem B42394265 : Blo 2205435 42394265 := bstep (se 2 (by rfl) ⟨15897849, by rfl⟩ : syracuseStep 42394265 = 31795699) B31795699
theorem B28262843 : Blo 2205435 28262843 := bstep (se 1 (by rfl) ⟨21197132, by rfl⟩ : syracuseStep 28262843 = 42394265) B42394265
theorem B18841895 : Blo 2205435 18841895 := bstep (se 1 (by rfl) ⟨14131421, by rfl⟩ : syracuseStep 18841895 = 28262843) B28262843
theorem B12561263 : Blo 2205435 12561263 := bstep (se 1 (by rfl) ⟨9420947, by rfl⟩ : syracuseStep 12561263 = 18841895) B18841895
theorem B8374175 : Blo 2205435 8374175 := bstep (se 1 (by rfl) ⟨6280631, by rfl⟩ : syracuseStep 8374175 = 12561263) B12561263
theorem B5582783 : Blo 2205435 5582783 := bstep (se 1 (by rfl) ⟨4187087, by rfl⟩ : syracuseStep 5582783 = 8374175) B8374175
theorem B3721855 : Blo 2205435 3721855 := bstep (se 1 (by rfl) ⟨2791391, by rfl⟩ : syracuseStep 3721855 = 5582783) B5582783
theorem B4962473 : Blo 2205435 4962473 := bstep (se 2 (by rfl) ⟨1860927, by rfl⟩ : syracuseStep 4962473 = 3721855) B3721855
theorem B3308315 : Blo 2205435 3308315 := bstep (se 1 (by rfl) ⟨2481236, by rfl⟩ : syracuseStep 3308315 = 4962473) B4962473
theorem B2205543 : Blo 2205435 2205543 := bstep (se 1 (by rfl) ⟨1654157, by rfl⟩ : syracuseStep 2205543 = 3308315) B3308315
theorem B2481241 : Blo 2205435 2481241 := bbase (se 2 (by rfl) ⟨930465, by rfl⟩ : syracuseStep 2481241 = 1860931) (by norm_num)
theorem B3308321 : Blo 2205435 3308321 := bstep (se 2 (by rfl) ⟨1240620, by rfl⟩ : syracuseStep 3308321 = 2481241) B2481241
theorem B2205547 : Blo 2205435 2205547 := bstep (se 1 (by rfl) ⟨1654160, by rfl⟩ : syracuseStep 2205547 = 3308321) B3308321
theorem B9188261 : Blo 2205435 9188261 := bbase (se 4 (by rfl) ⟨861399, by rfl⟩ : syracuseStep 9188261 = 1722799) (by norm_num)
theorem B6125507 : Blo 2205435 6125507 := bstep (se 1 (by rfl) ⟨4594130, by rfl⟩ : syracuseStep 6125507 = 9188261) B9188261
theorem B4083671 : Blo 2205435 4083671 := bstep (se 1 (by rfl) ⟨3062753, by rfl⟩ : syracuseStep 4083671 = 6125507) B6125507
theorem B2722447 : Blo 2205435 2722447 := bstep (se 1 (by rfl) ⟨2041835, by rfl⟩ : syracuseStep 2722447 = 4083671) B4083671
theorem B3629929 : Blo 2205435 3629929 := bstep (se 2 (by rfl) ⟨1361223, by rfl⟩ : syracuseStep 3629929 = 2722447) B2722447
theorem B4839905 : Blo 2205435 4839905 := bstep (se 2 (by rfl) ⟨1814964, by rfl⟩ : syracuseStep 4839905 = 3629929) B3629929
theorem B3226603 : Blo 2205435 3226603 := bstep (se 1 (by rfl) ⟨2419952, by rfl⟩ : syracuseStep 3226603 = 4839905) B4839905
theorem B4302137 : Blo 2205435 4302137 := bstep (se 2 (by rfl) ⟨1613301, by rfl⟩ : syracuseStep 4302137 = 3226603) B3226603
theorem B2868091 : Blo 2205435 2868091 := bstep (se 1 (by rfl) ⟨2151068, by rfl⟩ : syracuseStep 2868091 = 4302137) B4302137
theorem B61185941 : Blo 2205435 61185941 := bstep (se 6 (by rfl) ⟨1434045, by rfl⟩ : syracuseStep 61185941 = 2868091) B2868091
theorem B40790627 : Blo 2205435 40790627 := bstep (se 1 (by rfl) ⟨30592970, by rfl⟩ : syracuseStep 40790627 = 61185941) B61185941
theorem B27193751 : Blo 2205435 27193751 := bstep (se 1 (by rfl) ⟨20395313, by rfl⟩ : syracuseStep 27193751 = 40790627) B40790627
theorem B18129167 : Blo 2205435 18129167 := bstep (se 1 (by rfl) ⟨13596875, by rfl⟩ : syracuseStep 18129167 = 27193751) B27193751
theorem B12086111 : Blo 2205435 12086111 := bstep (se 1 (by rfl) ⟨9064583, by rfl⟩ : syracuseStep 12086111 = 18129167) B18129167
theorem B8057407 : Blo 2205435 8057407 := bstep (se 1 (by rfl) ⟨6043055, by rfl⟩ : syracuseStep 8057407 = 12086111) B12086111
theorem B10743209 : Blo 2205435 10743209 := bstep (se 2 (by rfl) ⟨4028703, by rfl⟩ : syracuseStep 10743209 = 8057407) B8057407
theorem B7162139 : Blo 2205435 7162139 := bstep (se 1 (by rfl) ⟨5371604, by rfl⟩ : syracuseStep 7162139 = 10743209) B10743209
theorem B19099037 : Blo 2205435 19099037 := bstep (se 3 (by rfl) ⟨3581069, by rfl⟩ : syracuseStep 19099037 = 7162139) B7162139
theorem B50930765 : Blo 2205435 50930765 := bstep (se 3 (by rfl) ⟨9549518, by rfl⟩ : syracuseStep 50930765 = 19099037) B19099037
theorem B33953843 : Blo 2205435 33953843 := bstep (se 1 (by rfl) ⟨25465382, by rfl⟩ : syracuseStep 33953843 = 50930765) B50930765
theorem B22635895 : Blo 2205435 22635895 := bstep (se 1 (by rfl) ⟨16976921, by rfl⟩ : syracuseStep 22635895 = 33953843) B33953843
theorem B30181193 : Blo 2205435 30181193 := bstep (se 2 (by rfl) ⟨11317947, by rfl⟩ : syracuseStep 30181193 = 22635895) B22635895
theorem B20120795 : Blo 2205435 20120795 := bstep (se 1 (by rfl) ⟨15090596, by rfl⟩ : syracuseStep 20120795 = 30181193) B30181193
theorem B13413863 : Blo 2205435 13413863 := bstep (se 1 (by rfl) ⟨10060397, by rfl⟩ : syracuseStep 13413863 = 20120795) B20120795
theorem B8942575 : Blo 2205435 8942575 := bstep (se 1 (by rfl) ⟨6706931, by rfl⟩ : syracuseStep 8942575 = 13413863) B13413863
theorem B11923433 : Blo 2205435 11923433 := bstep (se 2 (by rfl) ⟨4471287, by rfl⟩ : syracuseStep 11923433 = 8942575) B8942575
theorem B7948955 : Blo 2205435 7948955 := bstep (se 1 (by rfl) ⟨5961716, by rfl⟩ : syracuseStep 7948955 = 11923433) B11923433
theorem B5299303 : Blo 2205435 5299303 := bstep (se 1 (by rfl) ⟨3974477, by rfl⟩ : syracuseStep 5299303 = 7948955) B7948955
theorem B7065737 : Blo 2205435 7065737 := bstep (se 2 (by rfl) ⟨2649651, by rfl⟩ : syracuseStep 7065737 = 5299303) B5299303
theorem B4710491 : Blo 2205435 4710491 := bstep (se 1 (by rfl) ⟨3532868, by rfl⟩ : syracuseStep 4710491 = 7065737) B7065737
theorem B3140327 : Blo 2205435 3140327 := bstep (se 1 (by rfl) ⟨2355245, by rfl⟩ : syracuseStep 3140327 = 4710491) B4710491
theorem B8374205 : Blo 2205435 8374205 := bstep (se 3 (by rfl) ⟨1570163, by rfl⟩ : syracuseStep 8374205 = 3140327) B3140327
theorem B5582803 : Blo 2205435 5582803 := bstep (se 1 (by rfl) ⟨4187102, by rfl⟩ : syracuseStep 5582803 = 8374205) B8374205
theorem B7443737 : Blo 2205435 7443737 := bstep (se 2 (by rfl) ⟨2791401, by rfl⟩ : syracuseStep 7443737 = 5582803) B5582803
theorem B4962491 : Blo 2205435 4962491 := bstep (se 1 (by rfl) ⟨3721868, by rfl⟩ : syracuseStep 4962491 = 7443737) B7443737
theorem B3308327 : Blo 2205435 3308327 := bstep (se 1 (by rfl) ⟨2481245, by rfl⟩ : syracuseStep 3308327 = 4962491) B4962491
theorem B2205551 : Blo 2205435 2205551 := bstep (se 1 (by rfl) ⟨1654163, by rfl⟩ : syracuseStep 2205551 = 3308327) B3308327
theorem B3308333 : Blo 2205435 3308333 := bbase (se 3 (by rfl) ⟨620312, by rfl⟩ : syracuseStep 3308333 = 1240625) (by norm_num)
theorem B2205555 : Blo 2205435 2205555 := bstep (se 1 (by rfl) ⟨1654166, by rfl⟩ : syracuseStep 2205555 = 3308333) B3308333
theorem B4962509 : Blo 2205435 4962509 := bbase (se 3 (by rfl) ⟨930470, by rfl⟩ : syracuseStep 4962509 = 1860941) (by norm_num)
theorem B3308339 : Blo 2205435 3308339 := bstep (se 1 (by rfl) ⟨2481254, by rfl⟩ : syracuseStep 3308339 = 4962509) B4962509
theorem B2205559 : Blo 2205435 2205559 := bstep (se 1 (by rfl) ⟨1654169, by rfl⟩ : syracuseStep 2205559 = 3308339) B3308339
theorem B2791417 : Blo 2205435 2791417 := bbase (se 2 (by rfl) ⟨1046781, by rfl⟩ : syracuseStep 2791417 = 2093563) (by norm_num)
theorem B3721889 : Blo 2205435 3721889 := bstep (se 2 (by rfl) ⟨1395708, by rfl⟩ : syracuseStep 3721889 = 2791417) B2791417
theorem B2481259 : Blo 2205435 2481259 := bstep (se 1 (by rfl) ⟨1860944, by rfl⟩ : syracuseStep 2481259 = 3721889) B3721889
theorem B3308345 : Blo 2205435 3308345 := bstep (se 2 (by rfl) ⟨1240629, by rfl⟩ : syracuseStep 3308345 = 2481259) B2481259
theorem B2205563 : Blo 2205435 2205563 := bstep (se 1 (by rfl) ⟨1654172, by rfl⟩ : syracuseStep 2205563 = 3308345) B3308345
theorem B10060469 : Blo 2205435 10060469 := bbase (se 5 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 10060469 = 943169) (by norm_num)
theorem B6706979 : Blo 2205435 6706979 := bstep (se 1 (by rfl) ⟨5030234, by rfl⟩ : syracuseStep 6706979 = 10060469) B10060469
theorem B4471319 : Blo 2205435 4471319 := bstep (se 1 (by rfl) ⟨3353489, by rfl⟩ : syracuseStep 4471319 = 6706979) B6706979
theorem B11923517 : Blo 2205435 11923517 := bstep (se 3 (by rfl) ⟨2235659, by rfl⟩ : syracuseStep 11923517 = 4471319) B4471319
theorem B7949011 : Blo 2205435 7949011 := bstep (se 1 (by rfl) ⟨5961758, by rfl⟩ : syracuseStep 7949011 = 11923517) B11923517
theorem B10598681 : Blo 2205435 10598681 := bstep (se 2 (by rfl) ⟨3974505, by rfl⟩ : syracuseStep 10598681 = 7949011) B7949011
theorem B7065787 : Blo 2205435 7065787 := bstep (se 1 (by rfl) ⟨5299340, by rfl⟩ : syracuseStep 7065787 = 10598681) B10598681
theorem B9421049 : Blo 2205435 9421049 := bstep (se 2 (by rfl) ⟨3532893, by rfl⟩ : syracuseStep 9421049 = 7065787) B7065787
theorem B25122797 : Blo 2205435 25122797 := bstep (se 3 (by rfl) ⟨4710524, by rfl⟩ : syracuseStep 25122797 = 9421049) B9421049
theorem B16748531 : Blo 2205435 16748531 := bstep (se 1 (by rfl) ⟨12561398, by rfl⟩ : syracuseStep 16748531 = 25122797) B25122797
theorem B11165687 : Blo 2205435 11165687 := bstep (se 1 (by rfl) ⟨8374265, by rfl⟩ : syracuseStep 11165687 = 16748531) B16748531
theorem B7443791 : Blo 2205435 7443791 := bstep (se 1 (by rfl) ⟨5582843, by rfl⟩ : syracuseStep 7443791 = 11165687) B11165687
theorem B4962527 : Blo 2205435 4962527 := bstep (se 1 (by rfl) ⟨3721895, by rfl⟩ : syracuseStep 4962527 = 7443791) B7443791
theorem B3308351 : Blo 2205435 3308351 := bstep (se 1 (by rfl) ⟨2481263, by rfl⟩ : syracuseStep 3308351 = 4962527) B4962527
theorem B2205567 : Blo 2205435 2205567 := bstep (se 1 (by rfl) ⟨1654175, by rfl⟩ : syracuseStep 2205567 = 3308351) B3308351
theorem B3308357 : Blo 2205435 3308357 := bbase (se 4 (by rfl) ⟨310158, by rfl⟩ : syracuseStep 3308357 = 620317) (by norm_num)
theorem B2205571 : Blo 2205435 2205571 := bstep (se 1 (by rfl) ⟨1654178, by rfl⟩ : syracuseStep 2205571 = 3308357) B3308357
theorem B3721909 : Blo 2205435 3721909 := bbase (se 5 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 3721909 = 348929) (by norm_num)
theorem B4962545 : Blo 2205435 4962545 := bstep (se 2 (by rfl) ⟨1860954, by rfl⟩ : syracuseStep 4962545 = 3721909) B3721909
theorem B3308363 : Blo 2205435 3308363 := bstep (se 1 (by rfl) ⟨2481272, by rfl⟩ : syracuseStep 3308363 = 4962545) B4962545
theorem B2205575 : Blo 2205435 2205575 := bstep (se 1 (by rfl) ⟨1654181, by rfl⟩ : syracuseStep 2205575 = 3308363) B3308363
theorem B2481277 : Blo 2205435 2481277 := bbase (se 3 (by rfl) ⟨465239, by rfl⟩ : syracuseStep 2481277 = 930479) (by norm_num)
theorem B3308369 : Blo 2205435 3308369 := bstep (se 2 (by rfl) ⟨1240638, by rfl⟩ : syracuseStep 3308369 = 2481277) B2481277
theorem B2205579 : Blo 2205435 2205579 := bstep (se 1 (by rfl) ⟨1654184, by rfl⟩ : syracuseStep 2205579 = 3308369) B3308369
theorem B7443845 : Blo 2205435 7443845 := bbase (se 4 (by rfl) ⟨697860, by rfl⟩ : syracuseStep 7443845 = 1395721) (by norm_num)
theorem B4962563 : Blo 2205435 4962563 := bstep (se 1 (by rfl) ⟨3721922, by rfl⟩ : syracuseStep 4962563 = 7443845) B7443845
theorem B3308375 : Blo 2205435 3308375 := bstep (se 1 (by rfl) ⟨2481281, by rfl⟩ : syracuseStep 3308375 = 4962563) B4962563
theorem B2205583 : Blo 2205435 2205583 := bstep (se 1 (by rfl) ⟨1654187, by rfl⟩ : syracuseStep 2205583 = 3308375) B3308375
theorem B3308381 : Blo 2205435 3308381 := bbase (se 3 (by rfl) ⟨620321, by rfl⟩ : syracuseStep 3308381 = 1240643) (by norm_num)
theorem B2205587 : Blo 2205435 2205587 := bstep (se 1 (by rfl) ⟨1654190, by rfl⟩ : syracuseStep 2205587 = 3308381) B3308381
theorem B4962581 : Blo 2205435 4962581 := bbase (se 6 (by rfl) ⟨116310, by rfl⟩ : syracuseStep 4962581 = 232621) (by norm_num)
theorem B3308387 : Blo 2205435 3308387 := bstep (se 1 (by rfl) ⟨2481290, by rfl⟩ : syracuseStep 3308387 = 4962581) B4962581
theorem B2205591 : Blo 2205435 2205591 := bstep (se 1 (by rfl) ⟨1654193, by rfl⟩ : syracuseStep 2205591 = 3308387) B3308387
theorem B8374373 : Blo 2205435 8374373 := bbase (se 4 (by rfl) ⟨785097, by rfl⟩ : syracuseStep 8374373 = 1570195) (by norm_num)
theorem B5582915 : Blo 2205435 5582915 := bstep (se 1 (by rfl) ⟨4187186, by rfl⟩ : syracuseStep 5582915 = 8374373) B8374373
theorem B3721943 : Blo 2205435 3721943 := bstep (se 1 (by rfl) ⟨2791457, by rfl⟩ : syracuseStep 3721943 = 5582915) B5582915
theorem B2481295 : Blo 2205435 2481295 := bstep (se 1 (by rfl) ⟨1860971, by rfl⟩ : syracuseStep 2481295 = 3721943) B3721943
theorem B3308393 : Blo 2205435 3308393 := bstep (se 2 (by rfl) ⟨1240647, by rfl⟩ : syracuseStep 3308393 = 2481295) B2481295
theorem B2205595 : Blo 2205435 2205595 := bstep (se 1 (by rfl) ⟨1654196, by rfl⟩ : syracuseStep 2205595 = 3308393) B3308393
theorem B2649709 : Blo 2205435 2649709 := bbase (se 3 (by rfl) ⟨496820, by rfl⟩ : syracuseStep 2649709 = 993641) (by norm_num)
theorem B3532945 : Blo 2205435 3532945 := bstep (se 2 (by rfl) ⟨1324854, by rfl⟩ : syracuseStep 3532945 = 2649709) B2649709
theorem B4710593 : Blo 2205435 4710593 := bstep (se 2 (by rfl) ⟨1766472, by rfl⟩ : syracuseStep 4710593 = 3532945) B3532945
theorem B12561581 : Blo 2205435 12561581 := bstep (se 3 (by rfl) ⟨2355296, by rfl⟩ : syracuseStep 12561581 = 4710593) B4710593
theorem B8374387 : Blo 2205435 8374387 := bstep (se 1 (by rfl) ⟨6280790, by rfl⟩ : syracuseStep 8374387 = 12561581) B12561581
theorem B11165849 : Blo 2205435 11165849 := bstep (se 2 (by rfl) ⟨4187193, by rfl⟩ : syracuseStep 11165849 = 8374387) B8374387
theorem B7443899 : Blo 2205435 7443899 := bstep (se 1 (by rfl) ⟨5582924, by rfl⟩ : syracuseStep 7443899 = 11165849) B11165849
theorem B4962599 : Blo 2205435 4962599 := bstep (se 1 (by rfl) ⟨3721949, by rfl⟩ : syracuseStep 4962599 = 7443899) B7443899
theorem B3308399 : Blo 2205435 3308399 := bstep (se 1 (by rfl) ⟨2481299, by rfl⟩ : syracuseStep 3308399 = 4962599) B4962599
theorem B2205599 : Blo 2205435 2205599 := bstep (se 1 (by rfl) ⟨1654199, by rfl⟩ : syracuseStep 2205599 = 3308399) B3308399
theorem B3308405 : Blo 2205435 3308405 := bbase (se 5 (by rfl) ⟨155081, by rfl⟩ : syracuseStep 3308405 = 310163) (by norm_num)
theorem B2205603 : Blo 2205435 2205603 := bstep (se 1 (by rfl) ⟨1654202, by rfl⟩ : syracuseStep 2205603 = 3308405) B3308405
theorem B2235701 : Blo 2205435 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B5961869 : Blo 2205435 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B3974579 : Blo 2205435 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B2649719 : Blo 2205435 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B7065917 : Blo 2205435 7065917 := bstep (se 3 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 7065917 = 2649719) B2649719
theorem B4710611 : Blo 2205435 4710611 := bstep (se 1 (by rfl) ⟨3532958, by rfl⟩ : syracuseStep 4710611 = 7065917) B7065917
theorem B3140407 : Blo 2205435 3140407 := bstep (se 1 (by rfl) ⟨2355305, by rfl⟩ : syracuseStep 3140407 = 4710611) B4710611
theorem B4187209 : Blo 2205435 4187209 := bstep (se 2 (by rfl) ⟨1570203, by rfl⟩ : syracuseStep 4187209 = 3140407) B3140407
theorem B5582945 : Blo 2205435 5582945 := bstep (se 2 (by rfl) ⟨2093604, by rfl⟩ : syracuseStep 5582945 = 4187209) B4187209
theorem B3721963 : Blo 2205435 3721963 := bstep (se 1 (by rfl) ⟨2791472, by rfl⟩ : syracuseStep 3721963 = 5582945) B5582945
theorem B4962617 : Blo 2205435 4962617 := bstep (se 2 (by rfl) ⟨1860981, by rfl⟩ : syracuseStep 4962617 = 3721963) B3721963
theorem B3308411 : Blo 2205435 3308411 := bstep (se 1 (by rfl) ⟨2481308, by rfl⟩ : syracuseStep 3308411 = 4962617) B4962617
theorem B2205607 : Blo 2205435 2205607 := bstep (se 1 (by rfl) ⟨1654205, by rfl⟩ : syracuseStep 2205607 = 3308411) B3308411
theorem B2481313 : Blo 2205435 2481313 := bbase (se 2 (by rfl) ⟨930492, by rfl⟩ : syracuseStep 2481313 = 1860985) (by norm_num)
theorem B3308417 : Blo 2205435 3308417 := bstep (se 2 (by rfl) ⟨1240656, by rfl⟩ : syracuseStep 3308417 = 2481313) B2481313
theorem B2205611 : Blo 2205435 2205611 := bstep (se 1 (by rfl) ⟨1654208, by rfl⟩ : syracuseStep 2205611 = 3308417) B3308417
theorem B5582965 : Blo 2205435 5582965 := bbase (se 5 (by rfl) ⟨261701, by rfl⟩ : syracuseStep 5582965 = 523403) (by norm_num)
theorem B7443953 : Blo 2205435 7443953 := bstep (se 2 (by rfl) ⟨2791482, by rfl⟩ : syracuseStep 7443953 = 5582965) B5582965
theorem B4962635 : Blo 2205435 4962635 := bstep (se 1 (by rfl) ⟨3721976, by rfl⟩ : syracuseStep 4962635 = 7443953) B7443953
theorem B3308423 : Blo 2205435 3308423 := bstep (se 1 (by rfl) ⟨2481317, by rfl⟩ : syracuseStep 3308423 = 4962635) B4962635
theorem B2205615 : Blo 2205435 2205615 := bstep (se 1 (by rfl) ⟨1654211, by rfl⟩ : syracuseStep 2205615 = 3308423) B3308423
theorem B3308429 : Blo 2205435 3308429 := bbase (se 3 (by rfl) ⟨620330, by rfl⟩ : syracuseStep 3308429 = 1240661) (by norm_num)
theorem B2205619 : Blo 2205435 2205619 := bstep (se 1 (by rfl) ⟨1654214, by rfl⟩ : syracuseStep 2205619 = 3308429) B3308429
theorem B4962653 : Blo 2205435 4962653 := bbase (se 3 (by rfl) ⟨930497, by rfl⟩ : syracuseStep 4962653 = 1860995) (by norm_num)
theorem B3308435 : Blo 2205435 3308435 := bstep (se 1 (by rfl) ⟨2481326, by rfl⟩ : syracuseStep 3308435 = 4962653) B4962653
theorem B2205623 : Blo 2205435 2205623 := bstep (se 1 (by rfl) ⟨1654217, by rfl⟩ : syracuseStep 2205623 = 3308435) B3308435
theorem B3721997 : Blo 2205435 3721997 := bbase (se 3 (by rfl) ⟨697874, by rfl⟩ : syracuseStep 3721997 = 1395749) (by norm_num)
theorem B2481331 : Blo 2205435 2481331 := bstep (se 1 (by rfl) ⟨1860998, by rfl⟩ : syracuseStep 2481331 = 3721997) B3721997
theorem B3308441 : Blo 2205435 3308441 := bstep (se 2 (by rfl) ⟨1240665, by rfl⟩ : syracuseStep 3308441 = 2481331) B2481331
theorem B2205627 : Blo 2205435 2205627 := bstep (se 1 (by rfl) ⟨1654220, by rfl⟩ : syracuseStep 2205627 = 3308441) B3308441
theorem B18842645 : Blo 2205435 18842645 := bbase (se 6 (by rfl) ⟨441624, by rfl⟩ : syracuseStep 18842645 = 883249) (by norm_num)
theorem B12561763 : Blo 2205435 12561763 := bstep (se 1 (by rfl) ⟨9421322, by rfl⟩ : syracuseStep 12561763 = 18842645) B18842645
theorem B16749017 : Blo 2205435 16749017 := bstep (se 2 (by rfl) ⟨6280881, by rfl⟩ : syracuseStep 16749017 = 12561763) B12561763
theorem B11166011 : Blo 2205435 11166011 := bstep (se 1 (by rfl) ⟨8374508, by rfl⟩ : syracuseStep 11166011 = 16749017) B16749017
theorem B7444007 : Blo 2205435 7444007 := bstep (se 1 (by rfl) ⟨5583005, by rfl⟩ : syracuseStep 7444007 = 11166011) B11166011
theorem B4962671 : Blo 2205435 4962671 := bstep (se 1 (by rfl) ⟨3722003, by rfl⟩ : syracuseStep 4962671 = 7444007) B7444007
theorem B3308447 : Blo 2205435 3308447 := bstep (se 1 (by rfl) ⟨2481335, by rfl⟩ : syracuseStep 3308447 = 4962671) B4962671
theorem B2205631 : Blo 2205435 2205631 := bstep (se 1 (by rfl) ⟨1654223, by rfl⟩ : syracuseStep 2205631 = 3308447) B3308447
theorem B3308453 : Blo 2205435 3308453 := bbase (se 4 (by rfl) ⟨310167, by rfl⟩ : syracuseStep 3308453 = 620335) (by norm_num)
theorem B2205635 : Blo 2205435 2205635 := bstep (se 1 (by rfl) ⟨1654226, by rfl⟩ : syracuseStep 2205635 = 3308453) B3308453
theorem B2791513 : Blo 2205435 2791513 := bbase (se 2 (by rfl) ⟨1046817, by rfl⟩ : syracuseStep 2791513 = 2093635) (by norm_num)
theorem B3722017 : Blo 2205435 3722017 := bstep (se 2 (by rfl) ⟨1395756, by rfl⟩ : syracuseStep 3722017 = 2791513) B2791513
theorem B4962689 : Blo 2205435 4962689 := bstep (se 2 (by rfl) ⟨1861008, by rfl⟩ : syracuseStep 4962689 = 3722017) B3722017
theorem B3308459 : Blo 2205435 3308459 := bstep (se 1 (by rfl) ⟨2481344, by rfl⟩ : syracuseStep 3308459 = 4962689) B4962689
theorem B2205639 : Blo 2205435 2205639 := bstep (se 1 (by rfl) ⟨1654229, by rfl⟩ : syracuseStep 2205639 = 3308459) B3308459
theorem B2481349 : Blo 2205435 2481349 := bbase (se 4 (by rfl) ⟨232626, by rfl⟩ : syracuseStep 2481349 = 465253) (by norm_num)
theorem B3308465 : Blo 2205435 3308465 := bstep (se 2 (by rfl) ⟨1240674, by rfl⟩ : syracuseStep 3308465 = 2481349) B2481349
theorem B2205643 : Blo 2205435 2205643 := bstep (se 1 (by rfl) ⟨1654232, by rfl⟩ : syracuseStep 2205643 = 3308465) B3308465
theorem B4187285 : Blo 2205435 4187285 := bbase (se 6 (by rfl) ⟨98139, by rfl⟩ : syracuseStep 4187285 = 196279) (by norm_num)
theorem B2791523 : Blo 2205435 2791523 := bstep (se 1 (by rfl) ⟨2093642, by rfl⟩ : syracuseStep 2791523 = 4187285) B4187285
theorem B7444061 : Blo 2205435 7444061 := bstep (se 3 (by rfl) ⟨1395761, by rfl⟩ : syracuseStep 7444061 = 2791523) B2791523
theorem B4962707 : Blo 2205435 4962707 := bstep (se 1 (by rfl) ⟨3722030, by rfl⟩ : syracuseStep 4962707 = 7444061) B7444061
theorem B3308471 : Blo 2205435 3308471 := bstep (se 1 (by rfl) ⟨2481353, by rfl⟩ : syracuseStep 3308471 = 4962707) B4962707
theorem B2205647 : Blo 2205435 2205647 := bstep (se 1 (by rfl) ⟨1654235, by rfl⟩ : syracuseStep 2205647 = 3308471) B3308471
theorem B3308477 : Blo 2205435 3308477 := bbase (se 3 (by rfl) ⟨620339, by rfl⟩ : syracuseStep 3308477 = 1240679) (by norm_num)
theorem B2205651 : Blo 2205435 2205651 := bstep (se 1 (by rfl) ⟨1654238, by rfl⟩ : syracuseStep 2205651 = 3308477) B3308477
theorem B4962725 : Blo 2205435 4962725 := bbase (se 4 (by rfl) ⟨465255, by rfl⟩ : syracuseStep 4962725 = 930511) (by norm_num)
theorem B3308483 : Blo 2205435 3308483 := bstep (se 1 (by rfl) ⟨2481362, by rfl⟩ : syracuseStep 3308483 = 4962725) B4962725
theorem B2205655 : Blo 2205435 2205655 := bstep (se 1 (by rfl) ⟨1654241, by rfl⟩ : syracuseStep 2205655 = 3308483) B3308483
theorem B5583077 : Blo 2205435 5583077 := bbase (se 4 (by rfl) ⟨523413, by rfl⟩ : syracuseStep 5583077 = 1046827) (by norm_num)
theorem B3722051 : Blo 2205435 3722051 := bstep (se 1 (by rfl) ⟨2791538, by rfl⟩ : syracuseStep 3722051 = 5583077) B5583077
theorem B2481367 : Blo 2205435 2481367 := bstep (se 1 (by rfl) ⟨1861025, by rfl⟩ : syracuseStep 2481367 = 3722051) B3722051
theorem B3308489 : Blo 2205435 3308489 := bstep (se 2 (by rfl) ⟨1240683, by rfl⟩ : syracuseStep 3308489 = 2481367) B2481367
theorem B2205659 : Blo 2205435 2205659 := bstep (se 1 (by rfl) ⟨1654244, by rfl⟩ : syracuseStep 2205659 = 3308489) B3308489
theorem B2355365 : Blo 2205435 2355365 := bbase (se 4 (by rfl) ⟨220815, by rfl⟩ : syracuseStep 2355365 = 441631) (by norm_num)
theorem B6280973 : Blo 2205435 6280973 := bstep (se 3 (by rfl) ⟨1177682, by rfl⟩ : syracuseStep 6280973 = 2355365) B2355365
theorem B4187315 : Blo 2205435 4187315 := bstep (se 1 (by rfl) ⟨3140486, by rfl⟩ : syracuseStep 4187315 = 6280973) B6280973
theorem B11166173 : Blo 2205435 11166173 := bstep (se 3 (by rfl) ⟨2093657, by rfl⟩ : syracuseStep 11166173 = 4187315) B4187315
theorem B7444115 : Blo 2205435 7444115 := bstep (se 1 (by rfl) ⟨5583086, by rfl⟩ : syracuseStep 7444115 = 11166173) B11166173
theorem B4962743 : Blo 2205435 4962743 := bstep (se 1 (by rfl) ⟨3722057, by rfl⟩ : syracuseStep 4962743 = 7444115) B7444115
theorem B3308495 : Blo 2205435 3308495 := bstep (se 1 (by rfl) ⟨2481371, by rfl⟩ : syracuseStep 3308495 = 4962743) B4962743
theorem B2205663 : Blo 2205435 2205663 := bstep (se 1 (by rfl) ⟨1654247, by rfl⟩ : syracuseStep 2205663 = 3308495) B3308495
theorem B3308501 : Blo 2205435 3308501 := bbase (se 7 (by rfl) ⟨38771, by rfl⟩ : syracuseStep 3308501 = 77543) (by norm_num)
theorem B2205667 : Blo 2205435 2205667 := bstep (se 1 (by rfl) ⟨1654250, by rfl⟩ : syracuseStep 2205667 = 3308501) B3308501
theorem B8374661 : Blo 2205435 8374661 := bbase (se 4 (by rfl) ⟨785124, by rfl⟩ : syracuseStep 8374661 = 1570249) (by norm_num)
theorem B5583107 : Blo 2205435 5583107 := bstep (se 1 (by rfl) ⟨4187330, by rfl⟩ : syracuseStep 5583107 = 8374661) B8374661
theorem B3722071 : Blo 2205435 3722071 := bstep (se 1 (by rfl) ⟨2791553, by rfl⟩ : syracuseStep 3722071 = 5583107) B5583107
theorem B4962761 : Blo 2205435 4962761 := bstep (se 2 (by rfl) ⟨1861035, by rfl⟩ : syracuseStep 4962761 = 3722071) B3722071
theorem B3308507 : Blo 2205435 3308507 := bstep (se 1 (by rfl) ⟨2481380, by rfl⟩ : syracuseStep 3308507 = 4962761) B4962761
theorem B2205671 : Blo 2205435 2205671 := bstep (se 1 (by rfl) ⟨1654253, by rfl⟩ : syracuseStep 2205671 = 3308507) B3308507
theorem B2481385 : Blo 2205435 2481385 := bbase (se 2 (by rfl) ⟨930519, by rfl⟩ : syracuseStep 2481385 = 1861039) (by norm_num)
theorem B3308513 : Blo 2205435 3308513 := bstep (se 2 (by rfl) ⟨1240692, by rfl⟩ : syracuseStep 3308513 = 2481385) B2481385
theorem B2205675 : Blo 2205435 2205675 := bstep (se 1 (by rfl) ⟨1654256, by rfl⟩ : syracuseStep 2205675 = 3308513) B3308513
theorem B12562037 : Blo 2205435 12562037 := bbase (se 5 (by rfl) ⟨588845, by rfl⟩ : syracuseStep 12562037 = 1177691) (by norm_num)
theorem B8374691 : Blo 2205435 8374691 := bstep (se 1 (by rfl) ⟨6281018, by rfl⟩ : syracuseStep 8374691 = 12562037) B12562037
theorem B5583127 : Blo 2205435 5583127 := bstep (se 1 (by rfl) ⟨4187345, by rfl⟩ : syracuseStep 5583127 = 8374691) B8374691
theorem B7444169 : Blo 2205435 7444169 := bstep (se 2 (by rfl) ⟨2791563, by rfl⟩ : syracuseStep 7444169 = 5583127) B5583127
theorem B4962779 : Blo 2205435 4962779 := bstep (se 1 (by rfl) ⟨3722084, by rfl⟩ : syracuseStep 4962779 = 7444169) B7444169
theorem B3308519 : Blo 2205435 3308519 := bstep (se 1 (by rfl) ⟨2481389, by rfl⟩ : syracuseStep 3308519 = 4962779) B4962779
theorem B2205679 : Blo 2205435 2205679 := bstep (se 1 (by rfl) ⟨1654259, by rfl⟩ : syracuseStep 2205679 = 3308519) B3308519
theorem B3308525 : Blo 2205435 3308525 := bbase (se 3 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 3308525 = 1240697) (by norm_num)
theorem B2205683 : Blo 2205435 2205683 := bstep (se 1 (by rfl) ⟨1654262, by rfl⟩ : syracuseStep 2205683 = 3308525) B3308525
theorem B4962797 : Blo 2205435 4962797 := bbase (se 3 (by rfl) ⟨930524, by rfl⟩ : syracuseStep 4962797 = 1861049) (by norm_num)
theorem B3308531 : Blo 2205435 3308531 := bstep (se 1 (by rfl) ⟨2481398, by rfl⟩ : syracuseStep 3308531 = 4962797) B4962797
theorem B2205687 : Blo 2205435 2205687 := bstep (se 1 (by rfl) ⟨1654265, by rfl⟩ : syracuseStep 2205687 = 3308531) B3308531
theorem B7949461 : Blo 2205435 7949461 := bbase (se 6 (by rfl) ⟨186315, by rfl⟩ : syracuseStep 7949461 = 372631) (by norm_num)
theorem B10599281 : Blo 2205435 10599281 := bstep (se 2 (by rfl) ⟨3974730, by rfl⟩ : syracuseStep 10599281 = 7949461) B7949461
theorem B7066187 : Blo 2205435 7066187 := bstep (se 1 (by rfl) ⟨5299640, by rfl⟩ : syracuseStep 7066187 = 10599281) B10599281
theorem B4710791 : Blo 2205435 4710791 := bstep (se 1 (by rfl) ⟨3533093, by rfl⟩ : syracuseStep 4710791 = 7066187) B7066187
theorem B3140527 : Blo 2205435 3140527 := bstep (se 1 (by rfl) ⟨2355395, by rfl⟩ : syracuseStep 3140527 = 4710791) B4710791
theorem B4187369 : Blo 2205435 4187369 := bstep (se 2 (by rfl) ⟨1570263, by rfl⟩ : syracuseStep 4187369 = 3140527) B3140527
theorem B2791579 : Blo 2205435 2791579 := bstep (se 1 (by rfl) ⟨2093684, by rfl⟩ : syracuseStep 2791579 = 4187369) B4187369
theorem B3722105 : Blo 2205435 3722105 := bstep (se 2 (by rfl) ⟨1395789, by rfl⟩ : syracuseStep 3722105 = 2791579) B2791579
theorem B2481403 : Blo 2205435 2481403 := bstep (se 1 (by rfl) ⟨1861052, by rfl⟩ : syracuseStep 2481403 = 3722105) B3722105
theorem B3308537 : Blo 2205435 3308537 := bstep (se 2 (by rfl) ⟨1240701, by rfl⟩ : syracuseStep 3308537 = 2481403) B2481403
theorem B2205691 : Blo 2205435 2205691 := bstep (se 1 (by rfl) ⟨1654268, by rfl⟩ : syracuseStep 2205691 = 3308537) B3308537
theorem B11473109 : Blo 2205435 11473109 := bbase (se 7 (by rfl) ⟨134450, by rfl⟩ : syracuseStep 11473109 = 268901) (by norm_num)
theorem B7648739 : Blo 2205435 7648739 := bstep (se 1 (by rfl) ⟨5736554, by rfl⟩ : syracuseStep 7648739 = 11473109) B11473109
theorem B5099159 : Blo 2205435 5099159 := bstep (se 1 (by rfl) ⟨3824369, by rfl⟩ : syracuseStep 5099159 = 7648739) B7648739
theorem B13597757 : Blo 2205435 13597757 := bstep (se 3 (by rfl) ⟨2549579, by rfl⟩ : syracuseStep 13597757 = 5099159) B5099159
theorem B9065171 : Blo 2205435 9065171 := bstep (se 1 (by rfl) ⟨6798878, by rfl⟩ : syracuseStep 9065171 = 13597757) B13597757
theorem B6043447 : Blo 2205435 6043447 := bstep (se 1 (by rfl) ⟨4532585, by rfl⟩ : syracuseStep 6043447 = 9065171) B9065171
theorem B8057929 : Blo 2205435 8057929 := bstep (se 2 (by rfl) ⟨3021723, by rfl⟩ : syracuseStep 8057929 = 6043447) B6043447
theorem B10743905 : Blo 2205435 10743905 := bstep (se 2 (by rfl) ⟨4028964, by rfl⟩ : syracuseStep 10743905 = 8057929) B8057929
theorem B28650413 : Blo 2205435 28650413 := bstep (se 3 (by rfl) ⟨5371952, by rfl⟩ : syracuseStep 28650413 = 10743905) B10743905
theorem B19100275 : Blo 2205435 19100275 := bstep (se 1 (by rfl) ⟨14325206, by rfl⟩ : syracuseStep 19100275 = 28650413) B28650413
theorem B101868133 : Blo 2205435 101868133 := bstep (se 4 (by rfl) ⟨9550137, by rfl⟩ : syracuseStep 101868133 = 19100275) B19100275
theorem B135824177 : Blo 2205435 135824177 := bstep (se 2 (by rfl) ⟨50934066, by rfl⟩ : syracuseStep 135824177 = 101868133) B101868133
theorem B90549451 : Blo 2205435 90549451 := bstep (se 1 (by rfl) ⟨67912088, by rfl⟩ : syracuseStep 90549451 = 135824177) B135824177
theorem B120732601 : Blo 2205435 120732601 := bstep (se 2 (by rfl) ⟨45274725, by rfl⟩ : syracuseStep 120732601 = 90549451) B90549451
theorem B160976801 : Blo 2205435 160976801 := bstep (se 2 (by rfl) ⟨60366300, by rfl⟩ : syracuseStep 160976801 = 120732601) B120732601
theorem B107317867 : Blo 2205435 107317867 := bstep (se 1 (by rfl) ⟨80488400, by rfl⟩ : syracuseStep 107317867 = 160976801) B160976801
theorem B143090489 : Blo 2205435 143090489 := bstep (se 2 (by rfl) ⟨53658933, by rfl⟩ : syracuseStep 143090489 = 107317867) B107317867
theorem B95393659 : Blo 2205435 95393659 := bstep (se 1 (by rfl) ⟨71545244, by rfl⟩ : syracuseStep 95393659 = 143090489) B143090489
theorem B127191545 : Blo 2205435 127191545 := bstep (se 2 (by rfl) ⟨47696829, by rfl⟩ : syracuseStep 127191545 = 95393659) B95393659
theorem B84794363 : Blo 2205435 84794363 := bstep (se 1 (by rfl) ⟨63595772, by rfl⟩ : syracuseStep 84794363 = 127191545) B127191545
theorem B56529575 : Blo 2205435 56529575 := bstep (se 1 (by rfl) ⟨42397181, by rfl⟩ : syracuseStep 56529575 = 84794363) B84794363
theorem B37686383 : Blo 2205435 37686383 := bstep (se 1 (by rfl) ⟨28264787, by rfl⟩ : syracuseStep 37686383 = 56529575) B56529575
theorem B25124255 : Blo 2205435 25124255 := bstep (se 1 (by rfl) ⟨18843191, by rfl⟩ : syracuseStep 25124255 = 37686383) B37686383
theorem B16749503 : Blo 2205435 16749503 := bstep (se 1 (by rfl) ⟨12562127, by rfl⟩ : syracuseStep 16749503 = 25124255) B25124255
theorem B11166335 : Blo 2205435 11166335 := bstep (se 1 (by rfl) ⟨8374751, by rfl⟩ : syracuseStep 11166335 = 16749503) B16749503
theorem B7444223 : Blo 2205435 7444223 := bstep (se 1 (by rfl) ⟨5583167, by rfl⟩ : syracuseStep 7444223 = 11166335) B11166335
theorem B4962815 : Blo 2205435 4962815 := bstep (se 1 (by rfl) ⟨3722111, by rfl⟩ : syracuseStep 4962815 = 7444223) B7444223
theorem B3308543 : Blo 2205435 3308543 := bstep (se 1 (by rfl) ⟨2481407, by rfl⟩ : syracuseStep 3308543 = 4962815) B4962815
theorem B2205695 : Blo 2205435 2205695 := bstep (se 1 (by rfl) ⟨1654271, by rfl⟩ : syracuseStep 2205695 = 3308543) B3308543
theorem B3308549 : Blo 2205435 3308549 := bbase (se 4 (by rfl) ⟨310176, by rfl⟩ : syracuseStep 3308549 = 620353) (by norm_num)
theorem B2205699 : Blo 2205435 2205699 := bstep (se 1 (by rfl) ⟨1654274, by rfl⟩ : syracuseStep 2205699 = 3308549) B3308549
theorem B3722125 : Blo 2205435 3722125 := bbase (se 3 (by rfl) ⟨697898, by rfl⟩ : syracuseStep 3722125 = 1395797) (by norm_num)
theorem B4962833 : Blo 2205435 4962833 := bstep (se 2 (by rfl) ⟨1861062, by rfl⟩ : syracuseStep 4962833 = 3722125) B3722125
theorem B3308555 : Blo 2205435 3308555 := bstep (se 1 (by rfl) ⟨2481416, by rfl⟩ : syracuseStep 3308555 = 4962833) B4962833
theorem B2205703 : Blo 2205435 2205703 := bstep (se 1 (by rfl) ⟨1654277, by rfl⟩ : syracuseStep 2205703 = 3308555) B3308555
theorem B2481421 : Blo 2205435 2481421 := bbase (se 3 (by rfl) ⟨465266, by rfl⟩ : syracuseStep 2481421 = 930533) (by norm_num)
theorem B3308561 : Blo 2205435 3308561 := bstep (se 2 (by rfl) ⟨1240710, by rfl⟩ : syracuseStep 3308561 = 2481421) B2481421
theorem B2205707 : Blo 2205435 2205707 := bstep (se 1 (by rfl) ⟨1654280, by rfl⟩ : syracuseStep 2205707 = 3308561) B3308561
theorem B7444277 : Blo 2205435 7444277 := bbase (se 5 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 7444277 = 697901) (by norm_num)
theorem B4962851 : Blo 2205435 4962851 := bstep (se 1 (by rfl) ⟨3722138, by rfl⟩ : syracuseStep 4962851 = 7444277) B7444277
theorem B3308567 : Blo 2205435 3308567 := bstep (se 1 (by rfl) ⟨2481425, by rfl⟩ : syracuseStep 3308567 = 4962851) B4962851
theorem B2205711 : Blo 2205435 2205711 := bstep (se 1 (by rfl) ⟨1654283, by rfl⟩ : syracuseStep 2205711 = 3308567) B3308567
theorem B3308573 : Blo 2205435 3308573 := bbase (se 3 (by rfl) ⟨620357, by rfl⟩ : syracuseStep 3308573 = 1240715) (by norm_num)
theorem B2205715 : Blo 2205435 2205715 := bstep (se 1 (by rfl) ⟨1654286, by rfl⟩ : syracuseStep 2205715 = 3308573) B3308573
theorem B4962869 : Blo 2205435 4962869 := bbase (se 5 (by rfl) ⟨232634, by rfl⟩ : syracuseStep 4962869 = 465269) (by norm_num)
theorem B3308579 : Blo 2205435 3308579 := bstep (se 1 (by rfl) ⟨2481434, by rfl⟩ : syracuseStep 3308579 = 4962869) B4962869
theorem B2205719 : Blo 2205435 2205719 := bstep (se 1 (by rfl) ⟨1654289, by rfl⟩ : syracuseStep 2205719 = 3308579) B3308579
theorem B9421717 : Blo 2205435 9421717 := bbase (se 6 (by rfl) ⟨220821, by rfl⟩ : syracuseStep 9421717 = 441643) (by norm_num)
theorem B12562289 : Blo 2205435 12562289 := bstep (se 2 (by rfl) ⟨4710858, by rfl⟩ : syracuseStep 12562289 = 9421717) B9421717
theorem B8374859 : Blo 2205435 8374859 := bstep (se 1 (by rfl) ⟨6281144, by rfl⟩ : syracuseStep 8374859 = 12562289) B12562289
theorem B5583239 : Blo 2205435 5583239 := bstep (se 1 (by rfl) ⟨4187429, by rfl⟩ : syracuseStep 5583239 = 8374859) B8374859
theorem B3722159 : Blo 2205435 3722159 := bstep (se 1 (by rfl) ⟨2791619, by rfl⟩ : syracuseStep 3722159 = 5583239) B5583239
theorem B2481439 : Blo 2205435 2481439 := bstep (se 1 (by rfl) ⟨1861079, by rfl⟩ : syracuseStep 2481439 = 3722159) B3722159
theorem B3308585 : Blo 2205435 3308585 := bstep (se 2 (by rfl) ⟨1240719, by rfl⟩ : syracuseStep 3308585 = 2481439) B2481439
theorem B2205723 : Blo 2205435 2205723 := bstep (se 1 (by rfl) ⟨1654292, by rfl⟩ : syracuseStep 2205723 = 3308585) B3308585
theorem B9421733 : Blo 2205435 9421733 := bbase (se 4 (by rfl) ⟨883287, by rfl⟩ : syracuseStep 9421733 = 1766575) (by norm_num)
theorem B6281155 : Blo 2205435 6281155 := bstep (se 1 (by rfl) ⟨4710866, by rfl⟩ : syracuseStep 6281155 = 9421733) B9421733
theorem B8374873 : Blo 2205435 8374873 := bstep (se 2 (by rfl) ⟨3140577, by rfl⟩ : syracuseStep 8374873 = 6281155) B6281155
theorem B11166497 : Blo 2205435 11166497 := bstep (se 2 (by rfl) ⟨4187436, by rfl⟩ : syracuseStep 11166497 = 8374873) B8374873
theorem B7444331 : Blo 2205435 7444331 := bstep (se 1 (by rfl) ⟨5583248, by rfl⟩ : syracuseStep 7444331 = 11166497) B11166497
theorem B4962887 : Blo 2205435 4962887 := bstep (se 1 (by rfl) ⟨3722165, by rfl⟩ : syracuseStep 4962887 = 7444331) B7444331
theorem B3308591 : Blo 2205435 3308591 := bstep (se 1 (by rfl) ⟨2481443, by rfl⟩ : syracuseStep 3308591 = 4962887) B4962887
theorem B2205727 : Blo 2205435 2205727 := bstep (se 1 (by rfl) ⟨1654295, by rfl⟩ : syracuseStep 2205727 = 3308591) B3308591
theorem B3308597 : Blo 2205435 3308597 := bbase (se 5 (by rfl) ⟨155090, by rfl⟩ : syracuseStep 3308597 = 310181) (by norm_num)
theorem B2205731 : Blo 2205435 2205731 := bstep (se 1 (by rfl) ⟨1654298, by rfl⟩ : syracuseStep 2205731 = 3308597) B3308597
theorem B5583269 : Blo 2205435 5583269 := bbase (se 4 (by rfl) ⟨523431, by rfl⟩ : syracuseStep 5583269 = 1046863) (by norm_num)
theorem B3722179 : Blo 2205435 3722179 := bstep (se 1 (by rfl) ⟨2791634, by rfl⟩ : syracuseStep 3722179 = 5583269) B5583269
theorem B4962905 : Blo 2205435 4962905 := bstep (se 2 (by rfl) ⟨1861089, by rfl⟩ : syracuseStep 4962905 = 3722179) B3722179
theorem B3308603 : Blo 2205435 3308603 := bstep (se 1 (by rfl) ⟨2481452, by rfl⟩ : syracuseStep 3308603 = 4962905) B4962905
theorem B2205735 : Blo 2205435 2205735 := bstep (se 1 (by rfl) ⟨1654301, by rfl⟩ : syracuseStep 2205735 = 3308603) B3308603
theorem B2481457 : Blo 2205435 2481457 := bbase (se 2 (by rfl) ⟨930546, by rfl⟩ : syracuseStep 2481457 = 1861093) (by norm_num)
theorem B3308609 : Blo 2205435 3308609 := bstep (se 2 (by rfl) ⟨1240728, by rfl⟩ : syracuseStep 3308609 = 2481457) B2481457
theorem B2205739 : Blo 2205435 2205739 := bstep (se 1 (by rfl) ⟨1654304, by rfl⟩ : syracuseStep 2205739 = 3308609) B3308609
theorem B4710901 : Blo 2205435 4710901 := bbase (se 5 (by rfl) ⟨220823, by rfl⟩ : syracuseStep 4710901 = 441647) (by norm_num)
theorem B6281201 : Blo 2205435 6281201 := bstep (se 2 (by rfl) ⟨2355450, by rfl⟩ : syracuseStep 6281201 = 4710901) B4710901
theorem B4187467 : Blo 2205435 4187467 := bstep (se 1 (by rfl) ⟨3140600, by rfl⟩ : syracuseStep 4187467 = 6281201) B6281201
theorem B5583289 : Blo 2205435 5583289 := bstep (se 2 (by rfl) ⟨2093733, by rfl⟩ : syracuseStep 5583289 = 4187467) B4187467
theorem B7444385 : Blo 2205435 7444385 := bstep (se 2 (by rfl) ⟨2791644, by rfl⟩ : syracuseStep 7444385 = 5583289) B5583289
theorem B4962923 : Blo 2205435 4962923 := bstep (se 1 (by rfl) ⟨3722192, by rfl⟩ : syracuseStep 4962923 = 7444385) B7444385
theorem B3308615 : Blo 2205435 3308615 := bstep (se 1 (by rfl) ⟨2481461, by rfl⟩ : syracuseStep 3308615 = 4962923) B4962923
theorem B2205743 : Blo 2205435 2205743 := bstep (se 1 (by rfl) ⟨1654307, by rfl⟩ : syracuseStep 2205743 = 3308615) B3308615
theorem B3308621 : Blo 2205435 3308621 := bbase (se 3 (by rfl) ⟨620366, by rfl⟩ : syracuseStep 3308621 = 1240733) (by norm_num)
theorem B2205747 : Blo 2205435 2205747 := bstep (se 1 (by rfl) ⟨1654310, by rfl⟩ : syracuseStep 2205747 = 3308621) B3308621
theorem B4962941 : Blo 2205435 4962941 := bbase (se 3 (by rfl) ⟨930551, by rfl⟩ : syracuseStep 4962941 = 1861103) (by norm_num)
theorem B3308627 : Blo 2205435 3308627 := bstep (se 1 (by rfl) ⟨2481470, by rfl⟩ : syracuseStep 3308627 = 4962941) B4962941
theorem B2205751 : Blo 2205435 2205751 := bstep (se 1 (by rfl) ⟨1654313, by rfl⟩ : syracuseStep 2205751 = 3308627) B3308627
theorem B3722213 : Blo 2205435 3722213 := bbase (se 4 (by rfl) ⟨348957, by rfl⟩ : syracuseStep 3722213 = 697915) (by norm_num)
theorem B2481475 : Blo 2205435 2481475 := bstep (se 1 (by rfl) ⟨1861106, by rfl⟩ : syracuseStep 2481475 = 3722213) B3722213
theorem B3308633 : Blo 2205435 3308633 := bstep (se 2 (by rfl) ⟨1240737, by rfl⟩ : syracuseStep 3308633 = 2481475) B2481475
theorem B2205755 : Blo 2205435 2205755 := bstep (se 1 (by rfl) ⟨1654316, by rfl⟩ : syracuseStep 2205755 = 3308633) B3308633
theorem B10599605 : Blo 2205435 10599605 := bbase (se 5 (by rfl) ⟨496856, by rfl⟩ : syracuseStep 10599605 = 993713) (by norm_num)
theorem B7066403 : Blo 2205435 7066403 := bstep (se 1 (by rfl) ⟨5299802, by rfl⟩ : syracuseStep 7066403 = 10599605) B10599605
theorem B4710935 : Blo 2205435 4710935 := bstep (se 1 (by rfl) ⟨3533201, by rfl⟩ : syracuseStep 4710935 = 7066403) B7066403
theorem B3140623 : Blo 2205435 3140623 := bstep (se 1 (by rfl) ⟨2355467, by rfl⟩ : syracuseStep 3140623 = 4710935) B4710935
theorem B16749989 : Blo 2205435 16749989 := bstep (se 4 (by rfl) ⟨1570311, by rfl⟩ : syracuseStep 16749989 = 3140623) B3140623
theorem B11166659 : Blo 2205435 11166659 := bstep (se 1 (by rfl) ⟨8374994, by rfl⟩ : syracuseStep 11166659 = 16749989) B16749989
theorem B7444439 : Blo 2205435 7444439 := bstep (se 1 (by rfl) ⟨5583329, by rfl⟩ : syracuseStep 7444439 = 11166659) B11166659
theorem B4962959 : Blo 2205435 4962959 := bstep (se 1 (by rfl) ⟨3722219, by rfl⟩ : syracuseStep 4962959 = 7444439) B7444439
theorem B3308639 : Blo 2205435 3308639 := bstep (se 1 (by rfl) ⟨2481479, by rfl⟩ : syracuseStep 3308639 = 4962959) B4962959
theorem B2205759 : Blo 2205435 2205759 := bstep (se 1 (by rfl) ⟨1654319, by rfl⟩ : syracuseStep 2205759 = 3308639) B3308639
theorem B3308645 : Blo 2205435 3308645 := bbase (se 4 (by rfl) ⟨310185, by rfl⟩ : syracuseStep 3308645 = 620371) (by norm_num)
theorem B2205763 : Blo 2205435 2205763 := bstep (se 1 (by rfl) ⟨1654322, by rfl⟩ : syracuseStep 2205763 = 3308645) B3308645
theorem B2549665 : Blo 2205435 2549665 := bbase (se 2 (by rfl) ⟨956124, by rfl⟩ : syracuseStep 2549665 = 1912249) (by norm_num)
theorem B3399553 : Blo 2205435 3399553 := bstep (se 2 (by rfl) ⟨1274832, by rfl⟩ : syracuseStep 3399553 = 2549665) B2549665
theorem B18130949 : Blo 2205435 18130949 := bstep (se 4 (by rfl) ⟨1699776, by rfl⟩ : syracuseStep 18130949 = 3399553) B3399553
theorem B12087299 : Blo 2205435 12087299 := bstep (se 1 (by rfl) ⟨9065474, by rfl⟩ : syracuseStep 12087299 = 18130949) B18130949
theorem B8058199 : Blo 2205435 8058199 := bstep (se 1 (by rfl) ⟨6043649, by rfl⟩ : syracuseStep 8058199 = 12087299) B12087299
theorem B10744265 : Blo 2205435 10744265 := bstep (se 2 (by rfl) ⟨4029099, by rfl⟩ : syracuseStep 10744265 = 8058199) B8058199
theorem B7162843 : Blo 2205435 7162843 := bstep (se 1 (by rfl) ⟨5372132, by rfl⟩ : syracuseStep 7162843 = 10744265) B10744265
theorem B9550457 : Blo 2205435 9550457 := bstep (se 2 (by rfl) ⟨3581421, by rfl⟩ : syracuseStep 9550457 = 7162843) B7162843
theorem B6366971 : Blo 2205435 6366971 := bstep (se 1 (by rfl) ⟨4775228, by rfl⟩ : syracuseStep 6366971 = 9550457) B9550457
theorem B4244647 : Blo 2205435 4244647 := bstep (se 1 (by rfl) ⟨3183485, by rfl⟩ : syracuseStep 4244647 = 6366971) B6366971
theorem B5659529 : Blo 2205435 5659529 := bstep (se 2 (by rfl) ⟨2122323, by rfl⟩ : syracuseStep 5659529 = 4244647) B4244647
theorem B15092077 : Blo 2205435 15092077 := bstep (se 3 (by rfl) ⟨2829764, by rfl⟩ : syracuseStep 15092077 = 5659529) B5659529
theorem B20122769 : Blo 2205435 20122769 := bstep (se 2 (by rfl) ⟨7546038, by rfl⟩ : syracuseStep 20122769 = 15092077) B15092077
theorem B13415179 : Blo 2205435 13415179 := bstep (se 1 (by rfl) ⟨10061384, by rfl⟩ : syracuseStep 13415179 = 20122769) B20122769
theorem B17886905 : Blo 2205435 17886905 := bstep (se 2 (by rfl) ⟨6707589, by rfl⟩ : syracuseStep 17886905 = 13415179) B13415179
theorem B11924603 : Blo 2205435 11924603 := bstep (se 1 (by rfl) ⟨8943452, by rfl⟩ : syracuseStep 11924603 = 17886905) B17886905
theorem B7949735 : Blo 2205435 7949735 := bstep (se 1 (by rfl) ⟨5962301, by rfl⟩ : syracuseStep 7949735 = 11924603) B11924603
theorem B5299823 : Blo 2205435 5299823 := bstep (se 1 (by rfl) ⟨3974867, by rfl⟩ : syracuseStep 5299823 = 7949735) B7949735
theorem B3533215 : Blo 2205435 3533215 := bstep (se 1 (by rfl) ⟨2649911, by rfl⟩ : syracuseStep 3533215 = 5299823) B5299823
theorem B4710953 : Blo 2205435 4710953 := bstep (se 2 (by rfl) ⟨1766607, by rfl⟩ : syracuseStep 4710953 = 3533215) B3533215
theorem B3140635 : Blo 2205435 3140635 := bstep (se 1 (by rfl) ⟨2355476, by rfl⟩ : syracuseStep 3140635 = 4710953) B4710953
theorem B4187513 : Blo 2205435 4187513 := bstep (se 2 (by rfl) ⟨1570317, by rfl⟩ : syracuseStep 4187513 = 3140635) B3140635
theorem B2791675 : Blo 2205435 2791675 := bstep (se 1 (by rfl) ⟨2093756, by rfl⟩ : syracuseStep 2791675 = 4187513) B4187513
theorem B3722233 : Blo 2205435 3722233 := bstep (se 2 (by rfl) ⟨1395837, by rfl⟩ : syracuseStep 3722233 = 2791675) B2791675
theorem B4962977 : Blo 2205435 4962977 := bstep (se 2 (by rfl) ⟨1861116, by rfl⟩ : syracuseStep 4962977 = 3722233) B3722233
theorem B3308651 : Blo 2205435 3308651 := bstep (se 1 (by rfl) ⟨2481488, by rfl⟩ : syracuseStep 3308651 = 4962977) B4962977
theorem B2205767 : Blo 2205435 2205767 := bstep (se 1 (by rfl) ⟨1654325, by rfl⟩ : syracuseStep 2205767 = 3308651) B3308651
theorem B2481493 : Blo 2205435 2481493 := bbase (se 11 (by rfl) ⟨1817, by rfl⟩ : syracuseStep 2481493 = 3635) (by norm_num)
theorem B3308657 : Blo 2205435 3308657 := bstep (se 2 (by rfl) ⟨1240746, by rfl⟩ : syracuseStep 3308657 = 2481493) B2481493
theorem B2205771 : Blo 2205435 2205771 := bstep (se 1 (by rfl) ⟨1654328, by rfl⟩ : syracuseStep 2205771 = 3308657) B3308657
theorem B2791685 : Blo 2205435 2791685 := bbase (se 4 (by rfl) ⟨261720, by rfl⟩ : syracuseStep 2791685 = 523441) (by norm_num)
theorem B7444493 : Blo 2205435 7444493 := bstep (se 3 (by rfl) ⟨1395842, by rfl⟩ : syracuseStep 7444493 = 2791685) B2791685
theorem B4962995 : Blo 2205435 4962995 := bstep (se 1 (by rfl) ⟨3722246, by rfl⟩ : syracuseStep 4962995 = 7444493) B7444493
theorem B3308663 : Blo 2205435 3308663 := bstep (se 1 (by rfl) ⟨2481497, by rfl⟩ : syracuseStep 3308663 = 4962995) B4962995
theorem B2205775 : Blo 2205435 2205775 := bstep (se 1 (by rfl) ⟨1654331, by rfl⟩ : syracuseStep 2205775 = 3308663) B3308663
theorem B3308669 : Blo 2205435 3308669 := bbase (se 3 (by rfl) ⟨620375, by rfl⟩ : syracuseStep 3308669 = 1240751) (by norm_num)
theorem B2205779 : Blo 2205435 2205779 := bstep (se 1 (by rfl) ⟨1654334, by rfl⟩ : syracuseStep 2205779 = 3308669) B3308669
theorem B4963013 : Blo 2205435 4963013 := bbase (se 4 (by rfl) ⟨465282, by rfl⟩ : syracuseStep 4963013 = 930565) (by norm_num)
theorem B3308675 : Blo 2205435 3308675 := bstep (se 1 (by rfl) ⟨2481506, by rfl⟩ : syracuseStep 3308675 = 4963013) B4963013
theorem B2205783 : Blo 2205435 2205783 := bstep (se 1 (by rfl) ⟨1654337, by rfl⟩ : syracuseStep 2205783 = 3308675) B3308675
theorem B3581453 : Blo 2205435 3581453 := bbase (se 3 (by rfl) ⟨671522, by rfl⟩ : syracuseStep 3581453 = 1343045) (by norm_num)
theorem B9550541 : Blo 2205435 9550541 := bstep (se 3 (by rfl) ⟨1790726, by rfl⟩ : syracuseStep 9550541 = 3581453) B3581453
theorem B6367027 : Blo 2205435 6367027 := bstep (se 1 (by rfl) ⟨4775270, by rfl⟩ : syracuseStep 6367027 = 9550541) B9550541
theorem B8489369 : Blo 2205435 8489369 := bstep (se 2 (by rfl) ⟨3183513, by rfl⟩ : syracuseStep 8489369 = 6367027) B6367027
theorem B5659579 : Blo 2205435 5659579 := bstep (se 1 (by rfl) ⟨4244684, by rfl⟩ : syracuseStep 5659579 = 8489369) B8489369
theorem B7546105 : Blo 2205435 7546105 := bstep (se 2 (by rfl) ⟨2829789, by rfl⟩ : syracuseStep 7546105 = 5659579) B5659579
theorem B40245893 : Blo 2205435 40245893 := bstep (se 4 (by rfl) ⟨3773052, by rfl⟩ : syracuseStep 40245893 = 7546105) B7546105
theorem B26830595 : Blo 2205435 26830595 := bstep (se 1 (by rfl) ⟨20122946, by rfl⟩ : syracuseStep 26830595 = 40245893) B40245893
theorem B17887063 : Blo 2205435 17887063 := bstep (se 1 (by rfl) ⟨13415297, by rfl⟩ : syracuseStep 17887063 = 26830595) B26830595
theorem B23849417 : Blo 2205435 23849417 := bstep (se 2 (by rfl) ⟨8943531, by rfl⟩ : syracuseStep 23849417 = 17887063) B17887063
theorem B15899611 : Blo 2205435 15899611 := bstep (se 1 (by rfl) ⟨11924708, by rfl⟩ : syracuseStep 15899611 = 23849417) B23849417
theorem B21199481 : Blo 2205435 21199481 := bstep (se 2 (by rfl) ⟨7949805, by rfl⟩ : syracuseStep 21199481 = 15899611) B15899611
theorem B14132987 : Blo 2205435 14132987 := bstep (se 1 (by rfl) ⟨10599740, by rfl⟩ : syracuseStep 14132987 = 21199481) B21199481
theorem B9421991 : Blo 2205435 9421991 := bstep (se 1 (by rfl) ⟨7066493, by rfl⟩ : syracuseStep 9421991 = 14132987) B14132987
theorem B6281327 : Blo 2205435 6281327 := bstep (se 1 (by rfl) ⟨4710995, by rfl⟩ : syracuseStep 6281327 = 9421991) B9421991
theorem B4187551 : Blo 2205435 4187551 := bstep (se 1 (by rfl) ⟨3140663, by rfl⟩ : syracuseStep 4187551 = 6281327) B6281327
theorem B5583401 : Blo 2205435 5583401 := bstep (se 2 (by rfl) ⟨2093775, by rfl⟩ : syracuseStep 5583401 = 4187551) B4187551
theorem B3722267 : Blo 2205435 3722267 := bstep (se 1 (by rfl) ⟨2791700, by rfl⟩ : syracuseStep 3722267 = 5583401) B5583401
theorem B2481511 : Blo 2205435 2481511 := bstep (se 1 (by rfl) ⟨1861133, by rfl⟩ : syracuseStep 2481511 = 3722267) B3722267
theorem B3308681 : Blo 2205435 3308681 := bstep (se 2 (by rfl) ⟨1240755, by rfl⟩ : syracuseStep 3308681 = 2481511) B2481511
theorem B2205787 : Blo 2205435 2205787 := bstep (se 1 (by rfl) ⟨1654340, by rfl⟩ : syracuseStep 2205787 = 3308681) B3308681
theorem B11166821 : Blo 2205435 11166821 := bbase (se 4 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 11166821 = 2093779) (by norm_num)
theorem B7444547 : Blo 2205435 7444547 := bstep (se 1 (by rfl) ⟨5583410, by rfl⟩ : syracuseStep 7444547 = 11166821) B11166821
theorem B4963031 : Blo 2205435 4963031 := bstep (se 1 (by rfl) ⟨3722273, by rfl⟩ : syracuseStep 4963031 = 7444547) B7444547
theorem B3308687 : Blo 2205435 3308687 := bstep (se 1 (by rfl) ⟨2481515, by rfl⟩ : syracuseStep 3308687 = 4963031) B4963031
theorem B2205791 : Blo 2205435 2205791 := bstep (se 1 (by rfl) ⟨1654343, by rfl⟩ : syracuseStep 2205791 = 3308687) B3308687
theorem B3308693 : Blo 2205435 3308693 := bbase (se 6 (by rfl) ⟨77547, by rfl⟩ : syracuseStep 3308693 = 155095) (by norm_num)
theorem B2205795 : Blo 2205435 2205795 := bstep (se 1 (by rfl) ⟨1654346, by rfl⟩ : syracuseStep 2205795 = 3308693) B3308693
theorem B10599797 : Blo 2205435 10599797 := bbase (se 5 (by rfl) ⟨496865, by rfl⟩ : syracuseStep 10599797 = 993731) (by norm_num)
theorem B7066531 : Blo 2205435 7066531 := bstep (se 1 (by rfl) ⟨5299898, by rfl⟩ : syracuseStep 7066531 = 10599797) B10599797
theorem B9422041 : Blo 2205435 9422041 := bstep (se 2 (by rfl) ⟨3533265, by rfl⟩ : syracuseStep 9422041 = 7066531) B7066531
theorem B12562721 : Blo 2205435 12562721 := bstep (se 2 (by rfl) ⟨4711020, by rfl⟩ : syracuseStep 12562721 = 9422041) B9422041
theorem B8375147 : Blo 2205435 8375147 := bstep (se 1 (by rfl) ⟨6281360, by rfl⟩ : syracuseStep 8375147 = 12562721) B12562721
theorem B5583431 : Blo 2205435 5583431 := bstep (se 1 (by rfl) ⟨4187573, by rfl⟩ : syracuseStep 5583431 = 8375147) B8375147
theorem B3722287 : Blo 2205435 3722287 := bstep (se 1 (by rfl) ⟨2791715, by rfl⟩ : syracuseStep 3722287 = 5583431) B5583431
theorem B4963049 : Blo 2205435 4963049 := bstep (se 2 (by rfl) ⟨1861143, by rfl⟩ : syracuseStep 4963049 = 3722287) B3722287
theorem B3308699 : Blo 2205435 3308699 := bstep (se 1 (by rfl) ⟨2481524, by rfl⟩ : syracuseStep 3308699 = 4963049) B4963049
theorem B2205799 : Blo 2205435 2205799 := bstep (se 1 (by rfl) ⟨1654349, by rfl⟩ : syracuseStep 2205799 = 3308699) B3308699
theorem B2481529 : Blo 2205435 2481529 := bbase (se 2 (by rfl) ⟨930573, by rfl⟩ : syracuseStep 2481529 = 1861147) (by norm_num)
theorem B3308705 : Blo 2205435 3308705 := bstep (se 2 (by rfl) ⟨1240764, by rfl⟩ : syracuseStep 3308705 = 2481529) B2481529
theorem B2205803 : Blo 2205435 2205803 := bstep (se 1 (by rfl) ⟨1654352, by rfl⟩ : syracuseStep 2205803 = 3308705) B3308705
theorem B8058341 : Blo 2205435 8058341 := bbase (se 4 (by rfl) ⟨755469, by rfl⟩ : syracuseStep 8058341 = 1510939) (by norm_num)
theorem B5372227 : Blo 2205435 5372227 := bstep (se 1 (by rfl) ⟨4029170, by rfl⟩ : syracuseStep 5372227 = 8058341) B8058341
theorem B28651877 : Blo 2205435 28651877 := bstep (se 4 (by rfl) ⟨2686113, by rfl⟩ : syracuseStep 28651877 = 5372227) B5372227
theorem B19101251 : Blo 2205435 19101251 := bstep (se 1 (by rfl) ⟨14325938, by rfl⟩ : syracuseStep 19101251 = 28651877) B28651877
theorem B12734167 : Blo 2205435 12734167 := bstep (se 1 (by rfl) ⟨9550625, by rfl⟩ : syracuseStep 12734167 = 19101251) B19101251
theorem B16978889 : Blo 2205435 16978889 := bstep (se 2 (by rfl) ⟨6367083, by rfl⟩ : syracuseStep 16978889 = 12734167) B12734167
theorem B11319259 : Blo 2205435 11319259 := bstep (se 1 (by rfl) ⟨8489444, by rfl⟩ : syracuseStep 11319259 = 16978889) B16978889
theorem B15092345 : Blo 2205435 15092345 := bstep (se 2 (by rfl) ⟨5659629, by rfl⟩ : syracuseStep 15092345 = 11319259) B11319259
theorem B40246253 : Blo 2205435 40246253 := bstep (se 3 (by rfl) ⟨7546172, by rfl⟩ : syracuseStep 40246253 = 15092345) B15092345
theorem B26830835 : Blo 2205435 26830835 := bstep (se 1 (by rfl) ⟨20123126, by rfl⟩ : syracuseStep 26830835 = 40246253) B40246253
theorem B17887223 : Blo 2205435 17887223 := bstep (se 1 (by rfl) ⟨13415417, by rfl⟩ : syracuseStep 17887223 = 26830835) B26830835
theorem B11924815 : Blo 2205435 11924815 := bstep (se 1 (by rfl) ⟨8943611, by rfl⟩ : syracuseStep 11924815 = 17887223) B17887223
theorem B15899753 : Blo 2205435 15899753 := bstep (se 2 (by rfl) ⟨5962407, by rfl⟩ : syracuseStep 15899753 = 11924815) B11924815
theorem B10599835 : Blo 2205435 10599835 := bstep (se 1 (by rfl) ⟨7949876, by rfl⟩ : syracuseStep 10599835 = 15899753) B15899753
theorem B14133113 : Blo 2205435 14133113 := bstep (se 2 (by rfl) ⟨5299917, by rfl⟩ : syracuseStep 14133113 = 10599835) B10599835
theorem B9422075 : Blo 2205435 9422075 := bstep (se 1 (by rfl) ⟨7066556, by rfl⟩ : syracuseStep 9422075 = 14133113) B14133113
theorem B6281383 : Blo 2205435 6281383 := bstep (se 1 (by rfl) ⟨4711037, by rfl⟩ : syracuseStep 6281383 = 9422075) B9422075
theorem B8375177 : Blo 2205435 8375177 := bstep (se 2 (by rfl) ⟨3140691, by rfl⟩ : syracuseStep 8375177 = 6281383) B6281383
theorem B5583451 : Blo 2205435 5583451 := bstep (se 1 (by rfl) ⟨4187588, by rfl⟩ : syracuseStep 5583451 = 8375177) B8375177
theorem B7444601 : Blo 2205435 7444601 := bstep (se 2 (by rfl) ⟨2791725, by rfl⟩ : syracuseStep 7444601 = 5583451) B5583451
theorem B4963067 : Blo 2205435 4963067 := bstep (se 1 (by rfl) ⟨3722300, by rfl⟩ : syracuseStep 4963067 = 7444601) B7444601
theorem B3308711 : Blo 2205435 3308711 := bstep (se 1 (by rfl) ⟨2481533, by rfl⟩ : syracuseStep 3308711 = 4963067) B4963067
theorem B2205807 : Blo 2205435 2205807 := bstep (se 1 (by rfl) ⟨1654355, by rfl⟩ : syracuseStep 2205807 = 3308711) B3308711
theorem B3308717 : Blo 2205435 3308717 := bbase (se 3 (by rfl) ⟨620384, by rfl⟩ : syracuseStep 3308717 = 1240769) (by norm_num)
theorem B2205811 : Blo 2205435 2205811 := bstep (se 1 (by rfl) ⟨1654358, by rfl⟩ : syracuseStep 2205811 = 3308717) B3308717
theorem B4963085 : Blo 2205435 4963085 := bbase (se 3 (by rfl) ⟨930578, by rfl⟩ : syracuseStep 4963085 = 1861157) (by norm_num)
theorem B3308723 : Blo 2205435 3308723 := bstep (se 1 (by rfl) ⟨2481542, by rfl⟩ : syracuseStep 3308723 = 4963085) B4963085
theorem B2205815 : Blo 2205435 2205815 := bstep (se 1 (by rfl) ⟨1654361, by rfl⟩ : syracuseStep 2205815 = 3308723) B3308723
theorem B2791741 : Blo 2205435 2791741 := bbase (se 3 (by rfl) ⟨523451, by rfl⟩ : syracuseStep 2791741 = 1046903) (by norm_num)
theorem B3722321 : Blo 2205435 3722321 := bstep (se 2 (by rfl) ⟨1395870, by rfl⟩ : syracuseStep 3722321 = 2791741) B2791741
theorem B2481547 : Blo 2205435 2481547 := bstep (se 1 (by rfl) ⟨1861160, by rfl⟩ : syracuseStep 2481547 = 3722321) B3722321
theorem B3308729 : Blo 2205435 3308729 := bstep (se 2 (by rfl) ⟨1240773, by rfl⟩ : syracuseStep 3308729 = 2481547) B2481547
theorem B2205819 : Blo 2205435 2205819 := bstep (se 1 (by rfl) ⟨1654364, by rfl⟩ : syracuseStep 2205819 = 3308729) B3308729
theorem B3183565 : Blo 2205435 3183565 := bbase (se 3 (by rfl) ⟨596918, by rfl⟩ : syracuseStep 3183565 = 1193837) (by norm_num)
theorem B4244753 : Blo 2205435 4244753 := bstep (se 2 (by rfl) ⟨1591782, by rfl⟩ : syracuseStep 4244753 = 3183565) B3183565
theorem B2829835 : Blo 2205435 2829835 := bstep (se 1 (by rfl) ⟨2122376, by rfl⟩ : syracuseStep 2829835 = 4244753) B4244753
theorem B15092453 : Blo 2205435 15092453 := bstep (se 4 (by rfl) ⟨1414917, by rfl⟩ : syracuseStep 15092453 = 2829835) B2829835
theorem B40246541 : Blo 2205435 40246541 := bstep (se 3 (by rfl) ⟨7546226, by rfl⟩ : syracuseStep 40246541 = 15092453) B15092453
theorem B26831027 : Blo 2205435 26831027 := bstep (se 1 (by rfl) ⟨20123270, by rfl⟩ : syracuseStep 26831027 = 40246541) B40246541
theorem B17887351 : Blo 2205435 17887351 := bstep (se 1 (by rfl) ⟨13415513, by rfl⟩ : syracuseStep 17887351 = 26831027) B26831027
theorem B23849801 : Blo 2205435 23849801 := bstep (se 2 (by rfl) ⟨8943675, by rfl⟩ : syracuseStep 23849801 = 17887351) B17887351
theorem B15899867 : Blo 2205435 15899867 := bstep (se 1 (by rfl) ⟨11924900, by rfl⟩ : syracuseStep 15899867 = 23849801) B23849801
theorem B10599911 : Blo 2205435 10599911 := bstep (se 1 (by rfl) ⟨7949933, by rfl⟩ : syracuseStep 10599911 = 15899867) B15899867
theorem B7066607 : Blo 2205435 7066607 := bstep (se 1 (by rfl) ⟨5299955, by rfl⟩ : syracuseStep 7066607 = 10599911) B10599911
theorem B18844285 : Blo 2205435 18844285 := bstep (se 3 (by rfl) ⟨3533303, by rfl⟩ : syracuseStep 18844285 = 7066607) B7066607
theorem B25125713 : Blo 2205435 25125713 := bstep (se 2 (by rfl) ⟨9422142, by rfl⟩ : syracuseStep 25125713 = 18844285) B18844285
theorem B16750475 : Blo 2205435 16750475 := bstep (se 1 (by rfl) ⟨12562856, by rfl⟩ : syracuseStep 16750475 = 25125713) B25125713
theorem B11166983 : Blo 2205435 11166983 := bstep (se 1 (by rfl) ⟨8375237, by rfl⟩ : syracuseStep 11166983 = 16750475) B16750475
theorem B7444655 : Blo 2205435 7444655 := bstep (se 1 (by rfl) ⟨5583491, by rfl⟩ : syracuseStep 7444655 = 11166983) B11166983
theorem B4963103 : Blo 2205435 4963103 := bstep (se 1 (by rfl) ⟨3722327, by rfl⟩ : syracuseStep 4963103 = 7444655) B7444655
theorem B3308735 : Blo 2205435 3308735 := bstep (se 1 (by rfl) ⟨2481551, by rfl⟩ : syracuseStep 3308735 = 4963103) B4963103
theorem B2205823 : Blo 2205435 2205823 := bstep (se 1 (by rfl) ⟨1654367, by rfl⟩ : syracuseStep 2205823 = 3308735) B3308735
theorem B3308741 : Blo 2205435 3308741 := bbase (se 4 (by rfl) ⟨310194, by rfl⟩ : syracuseStep 3308741 = 620389) (by norm_num)
theorem B2205827 : Blo 2205435 2205827 := bstep (se 1 (by rfl) ⟨1654370, by rfl⟩ : syracuseStep 2205827 = 3308741) B3308741
theorem B3722341 : Blo 2205435 3722341 := bbase (se 4 (by rfl) ⟨348969, by rfl⟩ : syracuseStep 3722341 = 697939) (by norm_num)
theorem B4963121 : Blo 2205435 4963121 := bstep (se 2 (by rfl) ⟨1861170, by rfl⟩ : syracuseStep 4963121 = 3722341) B3722341
theorem B3308747 : Blo 2205435 3308747 := bstep (se 1 (by rfl) ⟨2481560, by rfl⟩ : syracuseStep 3308747 = 4963121) B4963121
theorem B2205831 : Blo 2205435 2205831 := bstep (se 1 (by rfl) ⟨1654373, by rfl⟩ : syracuseStep 2205831 = 3308747) B3308747
theorem B2481565 : Blo 2205435 2481565 := bbase (se 3 (by rfl) ⟨465293, by rfl⟩ : syracuseStep 2481565 = 930587) (by norm_num)
theorem B3308753 : Blo 2205435 3308753 := bstep (se 2 (by rfl) ⟨1240782, by rfl⟩ : syracuseStep 3308753 = 2481565) B2481565
theorem B2205835 : Blo 2205435 2205835 := bstep (se 1 (by rfl) ⟨1654376, by rfl⟩ : syracuseStep 2205835 = 3308753) B3308753
theorem B7444709 : Blo 2205435 7444709 := bbase (se 4 (by rfl) ⟨697941, by rfl⟩ : syracuseStep 7444709 = 1395883) (by norm_num)
theorem B4963139 : Blo 2205435 4963139 := bstep (se 1 (by rfl) ⟨3722354, by rfl⟩ : syracuseStep 4963139 = 7444709) B7444709
theorem B3308759 : Blo 2205435 3308759 := bstep (se 1 (by rfl) ⟨2481569, by rfl⟩ : syracuseStep 3308759 = 4963139) B4963139
theorem B2205839 : Blo 2205435 2205839 := bstep (se 1 (by rfl) ⟨1654379, by rfl⟩ : syracuseStep 2205839 = 3308759) B3308759
theorem B3308765 : Blo 2205435 3308765 := bbase (se 3 (by rfl) ⟨620393, by rfl⟩ : syracuseStep 3308765 = 1240787) (by norm_num)
theorem B2205843 : Blo 2205435 2205843 := bstep (se 1 (by rfl) ⟨1654382, by rfl⟩ : syracuseStep 2205843 = 3308765) B3308765
theorem B4963157 : Blo 2205435 4963157 := bbase (se 9 (by rfl) ⟨14540, by rfl⟩ : syracuseStep 4963157 = 29081) (by norm_num)
theorem B3308771 : Blo 2205435 3308771 := bstep (se 1 (by rfl) ⟨2481578, by rfl⟩ : syracuseStep 3308771 = 4963157) B4963157
theorem B2205847 : Blo 2205435 2205847 := bstep (se 1 (by rfl) ⟨1654385, by rfl⟩ : syracuseStep 2205847 = 3308771) B3308771
theorem B6281509 : Blo 2205435 6281509 := bbase (se 4 (by rfl) ⟨588891, by rfl⟩ : syracuseStep 6281509 = 1177783) (by norm_num)
theorem B8375345 : Blo 2205435 8375345 := bstep (se 2 (by rfl) ⟨3140754, by rfl⟩ : syracuseStep 8375345 = 6281509) B6281509
theorem B5583563 : Blo 2205435 5583563 := bstep (se 1 (by rfl) ⟨4187672, by rfl⟩ : syracuseStep 5583563 = 8375345) B8375345
theorem B3722375 : Blo 2205435 3722375 := bstep (se 1 (by rfl) ⟨2791781, by rfl⟩ : syracuseStep 3722375 = 5583563) B5583563
theorem B2481583 : Blo 2205435 2481583 := bstep (se 1 (by rfl) ⟨1861187, by rfl⟩ : syracuseStep 2481583 = 3722375) B3722375
theorem B3308777 : Blo 2205435 3308777 := bstep (se 2 (by rfl) ⟨1240791, by rfl⟩ : syracuseStep 3308777 = 2481583) B2481583
theorem B2205851 : Blo 2205435 2205851 := bstep (se 1 (by rfl) ⟨1654388, by rfl⟩ : syracuseStep 2205851 = 3308777) B3308777
theorem B4532917 : Blo 2205435 4532917 := bbase (se 5 (by rfl) ⟨212480, by rfl⟩ : syracuseStep 4532917 = 424961) (by norm_num)
theorem B6043889 : Blo 2205435 6043889 := bstep (se 2 (by rfl) ⟨2266458, by rfl⟩ : syracuseStep 6043889 = 4532917) B4532917
theorem B4029259 : Blo 2205435 4029259 := bstep (se 1 (by rfl) ⟨3021944, by rfl⟩ : syracuseStep 4029259 = 6043889) B6043889
theorem B5372345 : Blo 2205435 5372345 := bstep (se 2 (by rfl) ⟨2014629, by rfl⟩ : syracuseStep 5372345 = 4029259) B4029259
theorem B14326253 : Blo 2205435 14326253 := bstep (se 3 (by rfl) ⟨2686172, by rfl⟩ : syracuseStep 14326253 = 5372345) B5372345
theorem B9550835 : Blo 2205435 9550835 := bstep (se 1 (by rfl) ⟨7163126, by rfl⟩ : syracuseStep 9550835 = 14326253) B14326253
theorem B6367223 : Blo 2205435 6367223 := bstep (se 1 (by rfl) ⟨4775417, by rfl⟩ : syracuseStep 6367223 = 9550835) B9550835
theorem B4244815 : Blo 2205435 4244815 := bstep (se 1 (by rfl) ⟨3183611, by rfl⟩ : syracuseStep 4244815 = 6367223) B6367223
theorem B5659753 : Blo 2205435 5659753 := bstep (se 2 (by rfl) ⟨2122407, by rfl⟩ : syracuseStep 5659753 = 4244815) B4244815
theorem B7546337 : Blo 2205435 7546337 := bstep (se 2 (by rfl) ⟨2829876, by rfl⟩ : syracuseStep 7546337 = 5659753) B5659753
theorem B5030891 : Blo 2205435 5030891 := bstep (se 1 (by rfl) ⟨3773168, by rfl⟩ : syracuseStep 5030891 = 7546337) B7546337
theorem B3353927 : Blo 2205435 3353927 := bstep (se 1 (by rfl) ⟨2515445, by rfl⟩ : syracuseStep 3353927 = 5030891) B5030891
theorem B8943805 : Blo 2205435 8943805 := bstep (se 3 (by rfl) ⟨1676963, by rfl⟩ : syracuseStep 8943805 = 3353927) B3353927
theorem B11925073 : Blo 2205435 11925073 := bstep (se 2 (by rfl) ⟨4471902, by rfl⟩ : syracuseStep 11925073 = 8943805) B8943805
theorem B63600389 : Blo 2205435 63600389 := bstep (se 4 (by rfl) ⟨5962536, by rfl⟩ : syracuseStep 63600389 = 11925073) B11925073
theorem B42400259 : Blo 2205435 42400259 := bstep (se 1 (by rfl) ⟨31800194, by rfl⟩ : syracuseStep 42400259 = 63600389) B63600389
theorem B28266839 : Blo 2205435 28266839 := bstep (se 1 (by rfl) ⟨21200129, by rfl⟩ : syracuseStep 28266839 = 42400259) B42400259
theorem B18844559 : Blo 2205435 18844559 := bstep (se 1 (by rfl) ⟨14133419, by rfl⟩ : syracuseStep 18844559 = 28266839) B28266839
theorem B12563039 : Blo 2205435 12563039 := bstep (se 1 (by rfl) ⟨9422279, by rfl⟩ : syracuseStep 12563039 = 18844559) B18844559
theorem B8375359 : Blo 2205435 8375359 := bstep (se 1 (by rfl) ⟨6281519, by rfl⟩ : syracuseStep 8375359 = 12563039) B12563039
theorem B11167145 : Blo 2205435 11167145 := bstep (se 2 (by rfl) ⟨4187679, by rfl⟩ : syracuseStep 11167145 = 8375359) B8375359
theorem B7444763 : Blo 2205435 7444763 := bstep (se 1 (by rfl) ⟨5583572, by rfl⟩ : syracuseStep 7444763 = 11167145) B11167145
theorem B4963175 : Blo 2205435 4963175 := bstep (se 1 (by rfl) ⟨3722381, by rfl⟩ : syracuseStep 4963175 = 7444763) B7444763
theorem B3308783 : Blo 2205435 3308783 := bstep (se 1 (by rfl) ⟨2481587, by rfl⟩ : syracuseStep 3308783 = 4963175) B4963175
theorem B2205855 : Blo 2205435 2205855 := bstep (se 1 (by rfl) ⟨1654391, by rfl⟩ : syracuseStep 2205855 = 3308783) B3308783
theorem B3308789 : Blo 2205435 3308789 := bbase (se 5 (by rfl) ⟨155099, by rfl⟩ : syracuseStep 3308789 = 310199) (by norm_num)
theorem B2205859 : Blo 2205435 2205859 := bstep (se 1 (by rfl) ⟨1654394, by rfl⟩ : syracuseStep 2205859 = 3308789) B3308789
theorem B188627285 : Blo 2205435 188627285 := bbase (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) (by norm_num)
theorem B125751523 : Blo 2205435 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B167668697 : Blo 2205435 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B111779131 : Blo 2205435 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B149038841 : Blo 2205435 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B99359227 : Blo 2205435 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B529915877 : Blo 2205435 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B353277251 : Blo 2205435 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B235518167 : Blo 2205435 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B157012111 : Blo 2205435 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B837397925 : Blo 2205435 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B558265283 : Blo 2205435 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B372176855 : Blo 2205435 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B248117903 : Blo 2205435 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B165411935 : Blo 2205435 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B110274623 : Blo 2205435 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B73516415 : Blo 2205435 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B196043773 : Blo 2205435 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B261391697 : Blo 2205435 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B174261131 : Blo 2205435 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B116174087 : Blo 2205435 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B77449391 : Blo 2205435 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B51632927 : Blo 2205435 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B34421951 : Blo 2205435 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B22947967 : Blo 2205435 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B122389157 : Blo 2205435 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B81592771 : Blo 2205435 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B108790361 : Blo 2205435 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B72526907 : Blo 2205435 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B48351271 : Blo 2205435 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B64468361 : Blo 2205435 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B42978907 : Blo 2205435 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B229220837 : Blo 2205435 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B152813891 : Blo 2205435 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B101875927 : Blo 2205435 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B135834569 : Blo 2205435 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B90556379 : Blo 2205435 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B60370919 : Blo 2205435 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B40247279 : Blo 2205435 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B26831519 : Blo 2205435 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B17887679 : Blo 2205435 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B11925119 : Blo 2205435 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B7950079 : Blo 2205435 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B10600105 : Blo 2205435 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B14133473 : Blo 2205435 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B9422315 : Blo 2205435 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B6281543 : Blo 2205435 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B4187695 : Blo 2205435 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B5583593 : Blo 2205435 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B3722395 : Blo 2205435 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B4963193 : Blo 2205435 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B3308795 : Blo 2205435 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 2205435 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B2481601 : Blo 2205435 2481601 := bbase (se 2 (by rfl) ⟨930600, by rfl⟩ : syracuseStep 2481601 = 1861201) (by norm_num)
theorem B3308801 : Blo 2205435 3308801 := bstep (se 2 (by rfl) ⟨1240800, by rfl⟩ : syracuseStep 3308801 = 2481601) B2481601
theorem B2205867 : Blo 2205435 2205867 := bstep (se 1 (by rfl) ⟨1654400, by rfl⟩ : syracuseStep 2205867 = 3308801) B3308801
theorem B5583613 : Blo 2205435 5583613 := bbase (se 3 (by rfl) ⟨1046927, by rfl⟩ : syracuseStep 5583613 = 2093855) (by norm_num)
theorem B7444817 : Blo 2205435 7444817 := bstep (se 2 (by rfl) ⟨2791806, by rfl⟩ : syracuseStep 7444817 = 5583613) B5583613
theorem B4963211 : Blo 2205435 4963211 := bstep (se 1 (by rfl) ⟨3722408, by rfl⟩ : syracuseStep 4963211 = 7444817) B7444817
theorem B3308807 : Blo 2205435 3308807 := bstep (se 1 (by rfl) ⟨2481605, by rfl⟩ : syracuseStep 3308807 = 4963211) B4963211
theorem B2205871 : Blo 2205435 2205871 := bstep (se 1 (by rfl) ⟨1654403, by rfl⟩ : syracuseStep 2205871 = 3308807) B3308807
theorem B3308813 : Blo 2205435 3308813 := bbase (se 3 (by rfl) ⟨620402, by rfl⟩ : syracuseStep 3308813 = 1240805) (by norm_num)
theorem B2205875 : Blo 2205435 2205875 := bstep (se 1 (by rfl) ⟨1654406, by rfl⟩ : syracuseStep 2205875 = 3308813) B3308813
theorem B4963229 : Blo 2205435 4963229 := bbase (se 3 (by rfl) ⟨930605, by rfl⟩ : syracuseStep 4963229 = 1861211) (by norm_num)
theorem B3308819 : Blo 2205435 3308819 := bstep (se 1 (by rfl) ⟨2481614, by rfl⟩ : syracuseStep 3308819 = 4963229) B4963229
theorem B2205879 : Blo 2205435 2205879 := bstep (se 1 (by rfl) ⟨1654409, by rfl⟩ : syracuseStep 2205879 = 3308819) B3308819
theorem B3722429 : Blo 2205435 3722429 := bbase (se 3 (by rfl) ⟨697955, by rfl⟩ : syracuseStep 3722429 = 1395911) (by norm_num)
theorem B2481619 : Blo 2205435 2481619 := bstep (se 1 (by rfl) ⟨1861214, by rfl⟩ : syracuseStep 2481619 = 3722429) B3722429
theorem B3308825 : Blo 2205435 3308825 := bstep (se 2 (by rfl) ⟨1240809, by rfl⟩ : syracuseStep 3308825 = 2481619) B2481619
theorem B2205883 : Blo 2205435 2205883 := bstep (se 1 (by rfl) ⟨1654412, by rfl⟩ : syracuseStep 2205883 = 3308825) B3308825
theorem B12563221 : Blo 2205435 12563221 := bbase (se 6 (by rfl) ⟨294450, by rfl⟩ : syracuseStep 12563221 = 588901) (by norm_num)
theorem B16750961 : Blo 2205435 16750961 := bstep (se 2 (by rfl) ⟨6281610, by rfl⟩ : syracuseStep 16750961 = 12563221) B12563221
theorem B11167307 : Blo 2205435 11167307 := bstep (se 1 (by rfl) ⟨8375480, by rfl⟩ : syracuseStep 11167307 = 16750961) B16750961
theorem B7444871 : Blo 2205435 7444871 := bstep (se 1 (by rfl) ⟨5583653, by rfl⟩ : syracuseStep 7444871 = 11167307) B11167307
theorem B4963247 : Blo 2205435 4963247 := bstep (se 1 (by rfl) ⟨3722435, by rfl⟩ : syracuseStep 4963247 = 7444871) B7444871
theorem B3308831 : Blo 2205435 3308831 := bstep (se 1 (by rfl) ⟨2481623, by rfl⟩ : syracuseStep 3308831 = 4963247) B4963247
theorem B2205887 : Blo 2205435 2205887 := bstep (se 1 (by rfl) ⟨1654415, by rfl⟩ : syracuseStep 2205887 = 3308831) B3308831
theorem B3308837 : Blo 2205435 3308837 := bbase (se 4 (by rfl) ⟨310203, by rfl⟩ : syracuseStep 3308837 = 620407) (by norm_num)
theorem B2205891 : Blo 2205435 2205891 := bstep (se 1 (by rfl) ⟨1654418, by rfl⟩ : syracuseStep 2205891 = 3308837) B3308837
theorem B2791837 : Blo 2205435 2791837 := bbase (se 3 (by rfl) ⟨523469, by rfl⟩ : syracuseStep 2791837 = 1046939) (by norm_num)
theorem B3722449 : Blo 2205435 3722449 := bstep (se 2 (by rfl) ⟨1395918, by rfl⟩ : syracuseStep 3722449 = 2791837) B2791837
theorem B4963265 : Blo 2205435 4963265 := bstep (se 2 (by rfl) ⟨1861224, by rfl⟩ : syracuseStep 4963265 = 3722449) B3722449
theorem B3308843 : Blo 2205435 3308843 := bstep (se 1 (by rfl) ⟨2481632, by rfl⟩ : syracuseStep 3308843 = 4963265) B4963265
theorem B2205895 : Blo 2205435 2205895 := bstep (se 1 (by rfl) ⟨1654421, by rfl⟩ : syracuseStep 2205895 = 3308843) B3308843
theorem B2481637 : Blo 2205435 2481637 := bbase (se 4 (by rfl) ⟨232653, by rfl⟩ : syracuseStep 2481637 = 465307) (by norm_num)
theorem B3308849 : Blo 2205435 3308849 := bstep (se 2 (by rfl) ⟨1240818, by rfl⟩ : syracuseStep 3308849 = 2481637) B2481637
theorem B2205899 : Blo 2205435 2205899 := bstep (se 1 (by rfl) ⟨1654424, by rfl⟩ : syracuseStep 2205899 = 3308849) B3308849
theorem B5300149 : Blo 2205435 5300149 := bbase (se 5 (by rfl) ⟨248444, by rfl⟩ : syracuseStep 5300149 = 496889) (by norm_num)
theorem B7066865 : Blo 2205435 7066865 := bstep (se 2 (by rfl) ⟨2650074, by rfl⟩ : syracuseStep 7066865 = 5300149) B5300149
theorem B4711243 : Blo 2205435 4711243 := bstep (se 1 (by rfl) ⟨3533432, by rfl⟩ : syracuseStep 4711243 = 7066865) B7066865
theorem B6281657 : Blo 2205435 6281657 := bstep (se 2 (by rfl) ⟨2355621, by rfl⟩ : syracuseStep 6281657 = 4711243) B4711243
theorem B4187771 : Blo 2205435 4187771 := bstep (se 1 (by rfl) ⟨3140828, by rfl⟩ : syracuseStep 4187771 = 6281657) B6281657
theorem B2791847 : Blo 2205435 2791847 := bstep (se 1 (by rfl) ⟨2093885, by rfl⟩ : syracuseStep 2791847 = 4187771) B4187771
theorem B7444925 : Blo 2205435 7444925 := bstep (se 3 (by rfl) ⟨1395923, by rfl⟩ : syracuseStep 7444925 = 2791847) B2791847
theorem B4963283 : Blo 2205435 4963283 := bstep (se 1 (by rfl) ⟨3722462, by rfl⟩ : syracuseStep 4963283 = 7444925) B7444925
theorem B3308855 : Blo 2205435 3308855 := bstep (se 1 (by rfl) ⟨2481641, by rfl⟩ : syracuseStep 3308855 = 4963283) B4963283
theorem B2205903 : Blo 2205435 2205903 := bstep (se 1 (by rfl) ⟨1654427, by rfl⟩ : syracuseStep 2205903 = 3308855) B3308855
theorem B3308861 : Blo 2205435 3308861 := bbase (se 3 (by rfl) ⟨620411, by rfl⟩ : syracuseStep 3308861 = 1240823) (by norm_num)
theorem B2205907 : Blo 2205435 2205907 := bstep (se 1 (by rfl) ⟨1654430, by rfl⟩ : syracuseStep 2205907 = 3308861) B3308861
theorem B4963301 : Blo 2205435 4963301 := bbase (se 4 (by rfl) ⟨465309, by rfl⟩ : syracuseStep 4963301 = 930619) (by norm_num)
theorem B3308867 : Blo 2205435 3308867 := bstep (se 1 (by rfl) ⟨2481650, by rfl⟩ : syracuseStep 3308867 = 4963301) B4963301
theorem B2205911 : Blo 2205435 2205911 := bstep (se 1 (by rfl) ⟨1654433, by rfl⟩ : syracuseStep 2205911 = 3308867) B3308867
theorem B5583725 : Blo 2205435 5583725 := bbase (se 3 (by rfl) ⟨1046948, by rfl⟩ : syracuseStep 5583725 = 2093897) (by norm_num)
theorem B3722483 : Blo 2205435 3722483 := bstep (se 1 (by rfl) ⟨2791862, by rfl⟩ : syracuseStep 3722483 = 5583725) B5583725
theorem B2481655 : Blo 2205435 2481655 := bstep (se 1 (by rfl) ⟨1861241, by rfl⟩ : syracuseStep 2481655 = 3722483) B3722483
theorem B3308873 : Blo 2205435 3308873 := bstep (se 2 (by rfl) ⟨1240827, by rfl⟩ : syracuseStep 3308873 = 2481655) B2481655
theorem B2205915 : Blo 2205435 2205915 := bstep (se 1 (by rfl) ⟨1654436, by rfl⟩ : syracuseStep 2205915 = 3308873) B3308873
theorem B4711277 : Blo 2205435 4711277 := bbase (se 3 (by rfl) ⟨883364, by rfl⟩ : syracuseStep 4711277 = 1766729) (by norm_num)
theorem B3140851 : Blo 2205435 3140851 := bstep (se 1 (by rfl) ⟨2355638, by rfl⟩ : syracuseStep 3140851 = 4711277) B4711277
theorem B4187801 : Blo 2205435 4187801 := bstep (se 2 (by rfl) ⟨1570425, by rfl⟩ : syracuseStep 4187801 = 3140851) B3140851
theorem B11167469 : Blo 2205435 11167469 := bstep (se 3 (by rfl) ⟨2093900, by rfl⟩ : syracuseStep 11167469 = 4187801) B4187801
theorem B7444979 : Blo 2205435 7444979 := bstep (se 1 (by rfl) ⟨5583734, by rfl⟩ : syracuseStep 7444979 = 11167469) B11167469
theorem B4963319 : Blo 2205435 4963319 := bstep (se 1 (by rfl) ⟨3722489, by rfl⟩ : syracuseStep 4963319 = 7444979) B7444979
theorem B3308879 : Blo 2205435 3308879 := bstep (se 1 (by rfl) ⟨2481659, by rfl⟩ : syracuseStep 3308879 = 4963319) B4963319
theorem B2205919 : Blo 2205435 2205919 := bstep (se 1 (by rfl) ⟨1654439, by rfl⟩ : syracuseStep 2205919 = 3308879) B3308879
theorem B3308885 : Blo 2205435 3308885 := bbase (se 11 (by rfl) ⟨2423, by rfl⟩ : syracuseStep 3308885 = 4847) (by norm_num)
theorem B2205923 : Blo 2205435 2205923 := bstep (se 1 (by rfl) ⟨1654442, by rfl⟩ : syracuseStep 2205923 = 3308885) B3308885
theorem B8489909 : Blo 2205435 8489909 := bbase (se 5 (by rfl) ⟨397964, by rfl⟩ : syracuseStep 8489909 = 795929) (by norm_num)
theorem B5659939 : Blo 2205435 5659939 := bstep (se 1 (by rfl) ⟨4244954, by rfl⟩ : syracuseStep 5659939 = 8489909) B8489909
theorem B30186341 : Blo 2205435 30186341 := bstep (se 4 (by rfl) ⟨2829969, by rfl⟩ : syracuseStep 30186341 = 5659939) B5659939
theorem B20124227 : Blo 2205435 20124227 := bstep (se 1 (by rfl) ⟨15093170, by rfl⟩ : syracuseStep 20124227 = 30186341) B30186341
theorem B13416151 : Blo 2205435 13416151 := bstep (se 1 (by rfl) ⟨10062113, by rfl⟩ : syracuseStep 13416151 = 20124227) B20124227
theorem B17888201 : Blo 2205435 17888201 := bstep (se 2 (by rfl) ⟨6708075, by rfl⟩ : syracuseStep 17888201 = 13416151) B13416151
theorem B11925467 : Blo 2205435 11925467 := bstep (se 1 (by rfl) ⟨8944100, by rfl⟩ : syracuseStep 11925467 = 17888201) B17888201
theorem B7950311 : Blo 2205435 7950311 := bstep (se 1 (by rfl) ⟨5962733, by rfl⟩ : syracuseStep 7950311 = 11925467) B11925467
theorem B5300207 : Blo 2205435 5300207 := bstep (se 1 (by rfl) ⟨3975155, by rfl⟩ : syracuseStep 5300207 = 7950311) B7950311
theorem B3533471 : Blo 2205435 3533471 := bstep (se 1 (by rfl) ⟨2650103, by rfl⟩ : syracuseStep 3533471 = 5300207) B5300207
theorem B2355647 : Blo 2205435 2355647 := bstep (se 1 (by rfl) ⟨1766735, by rfl⟩ : syracuseStep 2355647 = 3533471) B3533471
theorem B6281725 : Blo 2205435 6281725 := bstep (se 3 (by rfl) ⟨1177823, by rfl⟩ : syracuseStep 6281725 = 2355647) B2355647
theorem B8375633 : Blo 2205435 8375633 := bstep (se 2 (by rfl) ⟨3140862, by rfl⟩ : syracuseStep 8375633 = 6281725) B6281725
theorem B5583755 : Blo 2205435 5583755 := bstep (se 1 (by rfl) ⟨4187816, by rfl⟩ : syracuseStep 5583755 = 8375633) B8375633
theorem B3722503 : Blo 2205435 3722503 := bstep (se 1 (by rfl) ⟨2791877, by rfl⟩ : syracuseStep 3722503 = 5583755) B5583755
theorem B4963337 : Blo 2205435 4963337 := bstep (se 2 (by rfl) ⟨1861251, by rfl⟩ : syracuseStep 4963337 = 3722503) B3722503
theorem B3308891 : Blo 2205435 3308891 := bstep (se 1 (by rfl) ⟨2481668, by rfl⟩ : syracuseStep 3308891 = 4963337) B4963337
theorem B2205927 : Blo 2205435 2205927 := bstep (se 1 (by rfl) ⟨1654445, by rfl⟩ : syracuseStep 2205927 = 3308891) B3308891
theorem B2481673 : Blo 2205435 2481673 := bbase (se 2 (by rfl) ⟨930627, by rfl⟩ : syracuseStep 2481673 = 1861255) (by norm_num)
theorem B3308897 : Blo 2205435 3308897 := bstep (se 2 (by rfl) ⟨1240836, by rfl⟩ : syracuseStep 3308897 = 2481673) B2481673
theorem B2205931 : Blo 2205435 2205931 := bstep (se 1 (by rfl) ⟨1654448, by rfl⟩ : syracuseStep 2205931 = 3308897) B3308897
theorem B2515537 : Blo 2205435 2515537 := bbase (se 2 (by rfl) ⟨943326, by rfl⟩ : syracuseStep 2515537 = 1886653) (by norm_num)
theorem B3354049 : Blo 2205435 3354049 := bstep (se 2 (by rfl) ⟨1257768, by rfl⟩ : syracuseStep 3354049 = 2515537) B2515537
theorem B4472065 : Blo 2205435 4472065 := bstep (se 2 (by rfl) ⟨1677024, by rfl⟩ : syracuseStep 4472065 = 3354049) B3354049
theorem B5962753 : Blo 2205435 5962753 := bstep (se 2 (by rfl) ⟨2236032, by rfl⟩ : syracuseStep 5962753 = 4472065) B4472065
theorem B31801349 : Blo 2205435 31801349 := bstep (se 4 (by rfl) ⟨2981376, by rfl⟩ : syracuseStep 31801349 = 5962753) B5962753
theorem B21200899 : Blo 2205435 21200899 := bstep (se 1 (by rfl) ⟨15900674, by rfl⟩ : syracuseStep 21200899 = 31801349) B31801349
theorem B28267865 : Blo 2205435 28267865 := bstep (se 2 (by rfl) ⟨10600449, by rfl⟩ : syracuseStep 28267865 = 21200899) B21200899
theorem B18845243 : Blo 2205435 18845243 := bstep (se 1 (by rfl) ⟨14133932, by rfl⟩ : syracuseStep 18845243 = 28267865) B28267865
theorem B12563495 : Blo 2205435 12563495 := bstep (se 1 (by rfl) ⟨9422621, by rfl⟩ : syracuseStep 12563495 = 18845243) B18845243
theorem B8375663 : Blo 2205435 8375663 := bstep (se 1 (by rfl) ⟨6281747, by rfl⟩ : syracuseStep 8375663 = 12563495) B12563495
theorem B5583775 : Blo 2205435 5583775 := bstep (se 1 (by rfl) ⟨4187831, by rfl⟩ : syracuseStep 5583775 = 8375663) B8375663
theorem B7445033 : Blo 2205435 7445033 := bstep (se 2 (by rfl) ⟨2791887, by rfl⟩ : syracuseStep 7445033 = 5583775) B5583775
theorem B4963355 : Blo 2205435 4963355 := bstep (se 1 (by rfl) ⟨3722516, by rfl⟩ : syracuseStep 4963355 = 7445033) B7445033
theorem B3308903 : Blo 2205435 3308903 := bstep (se 1 (by rfl) ⟨2481677, by rfl⟩ : syracuseStep 3308903 = 4963355) B4963355
theorem B2205935 : Blo 2205435 2205935 := bstep (se 1 (by rfl) ⟨1654451, by rfl⟩ : syracuseStep 2205935 = 3308903) B3308903
theorem B3308909 : Blo 2205435 3308909 := bbase (se 3 (by rfl) ⟨620420, by rfl⟩ : syracuseStep 3308909 = 1240841) (by norm_num)
theorem B2205939 : Blo 2205435 2205939 := bstep (se 1 (by rfl) ⟨1654454, by rfl⟩ : syracuseStep 2205939 = 3308909) B3308909
theorem B4963373 : Blo 2205435 4963373 := bbase (se 3 (by rfl) ⟨930632, by rfl⟩ : syracuseStep 4963373 = 1861265) (by norm_num)
theorem B3308915 : Blo 2205435 3308915 := bstep (se 1 (by rfl) ⟨2481686, by rfl⟩ : syracuseStep 3308915 = 4963373) B4963373
theorem B2205943 : Blo 2205435 2205943 := bstep (se 1 (by rfl) ⟨1654457, by rfl⟩ : syracuseStep 2205943 = 3308915) B3308915
theorem B2686285 : Blo 2205435 2686285 := bbase (se 3 (by rfl) ⟨503678, by rfl⟩ : syracuseStep 2686285 = 1007357) (by norm_num)
theorem B3581713 : Blo 2205435 3581713 := bstep (se 2 (by rfl) ⟨1343142, by rfl⟩ : syracuseStep 3581713 = 2686285) B2686285
theorem B4775617 : Blo 2205435 4775617 := bstep (se 2 (by rfl) ⟨1790856, by rfl⟩ : syracuseStep 4775617 = 3581713) B3581713
theorem B25469957 : Blo 2205435 25469957 := bstep (se 4 (by rfl) ⟨2387808, by rfl⟩ : syracuseStep 25469957 = 4775617) B4775617
theorem B16979971 : Blo 2205435 16979971 := bstep (se 1 (by rfl) ⟨12734978, by rfl⟩ : syracuseStep 16979971 = 25469957) B25469957
theorem B22639961 : Blo 2205435 22639961 := bstep (se 2 (by rfl) ⟨8489985, by rfl⟩ : syracuseStep 22639961 = 16979971) B16979971
theorem B15093307 : Blo 2205435 15093307 := bstep (se 1 (by rfl) ⟨11319980, by rfl⟩ : syracuseStep 15093307 = 22639961) B22639961
theorem B20124409 : Blo 2205435 20124409 := bstep (se 2 (by rfl) ⟨7546653, by rfl⟩ : syracuseStep 20124409 = 15093307) B15093307
theorem B26832545 : Blo 2205435 26832545 := bstep (se 2 (by rfl) ⟨10062204, by rfl⟩ : syracuseStep 26832545 = 20124409) B20124409
theorem B17888363 : Blo 2205435 17888363 := bstep (se 1 (by rfl) ⟨13416272, by rfl⟩ : syracuseStep 17888363 = 26832545) B26832545
theorem B11925575 : Blo 2205435 11925575 := bstep (se 1 (by rfl) ⟨8944181, by rfl⟩ : syracuseStep 11925575 = 17888363) B17888363
theorem B7950383 : Blo 2205435 7950383 := bstep (se 1 (by rfl) ⟨5962787, by rfl⟩ : syracuseStep 7950383 = 11925575) B11925575
theorem B5300255 : Blo 2205435 5300255 := bstep (se 1 (by rfl) ⟨3975191, by rfl⟩ : syracuseStep 5300255 = 7950383) B7950383
theorem B14134013 : Blo 2205435 14134013 := bstep (se 3 (by rfl) ⟨2650127, by rfl⟩ : syracuseStep 14134013 = 5300255) B5300255
theorem B9422675 : Blo 2205435 9422675 := bstep (se 1 (by rfl) ⟨7067006, by rfl⟩ : syracuseStep 9422675 = 14134013) B14134013
theorem B6281783 : Blo 2205435 6281783 := bstep (se 1 (by rfl) ⟨4711337, by rfl⟩ : syracuseStep 6281783 = 9422675) B9422675
theorem B4187855 : Blo 2205435 4187855 := bstep (se 1 (by rfl) ⟨3140891, by rfl⟩ : syracuseStep 4187855 = 6281783) B6281783
theorem B2791903 : Blo 2205435 2791903 := bstep (se 1 (by rfl) ⟨2093927, by rfl⟩ : syracuseStep 2791903 = 4187855) B4187855
theorem B3722537 : Blo 2205435 3722537 := bstep (se 2 (by rfl) ⟨1395951, by rfl⟩ : syracuseStep 3722537 = 2791903) B2791903
theorem B2481691 : Blo 2205435 2481691 := bstep (se 1 (by rfl) ⟨1861268, by rfl⟩ : syracuseStep 2481691 = 3722537) B3722537
theorem B3308921 : Blo 2205435 3308921 := bstep (se 2 (by rfl) ⟨1240845, by rfl⟩ : syracuseStep 3308921 = 2481691) B2481691
theorem B2205947 : Blo 2205435 2205947 := bstep (se 1 (by rfl) ⟨1654460, by rfl⟩ : syracuseStep 2205947 = 3308921) B3308921
theorem B3773333 : Blo 2205435 3773333 := bbase (se 6 (by rfl) ⟨88437, by rfl⟩ : syracuseStep 3773333 = 176875) (by norm_num)
theorem B2515555 : Blo 2205435 2515555 := bstep (se 1 (by rfl) ⟨1886666, by rfl⟩ : syracuseStep 2515555 = 3773333) B3773333
theorem B13416293 : Blo 2205435 13416293 := bstep (se 4 (by rfl) ⟨1257777, by rfl⟩ : syracuseStep 13416293 = 2515555) B2515555
theorem B8944195 : Blo 2205435 8944195 := bstep (se 1 (by rfl) ⟨6708146, by rfl⟩ : syracuseStep 8944195 = 13416293) B13416293
theorem B11925593 : Blo 2205435 11925593 := bstep (se 2 (by rfl) ⟨4472097, by rfl⟩ : syracuseStep 11925593 = 8944195) B8944195
theorem B7950395 : Blo 2205435 7950395 := bstep (se 1 (by rfl) ⟨5962796, by rfl⟩ : syracuseStep 7950395 = 11925593) B11925593
theorem B5300263 : Blo 2205435 5300263 := bstep (se 1 (by rfl) ⟨3975197, by rfl⟩ : syracuseStep 5300263 = 7950395) B7950395
theorem B7067017 : Blo 2205435 7067017 := bstep (se 2 (by rfl) ⟨2650131, by rfl⟩ : syracuseStep 7067017 = 5300263) B5300263
theorem B37690757 : Blo 2205435 37690757 := bstep (se 4 (by rfl) ⟨3533508, by rfl⟩ : syracuseStep 37690757 = 7067017) B7067017
theorem B25127171 : Blo 2205435 25127171 := bstep (se 1 (by rfl) ⟨18845378, by rfl⟩ : syracuseStep 25127171 = 37690757) B37690757
theorem B16751447 : Blo 2205435 16751447 := bstep (se 1 (by rfl) ⟨12563585, by rfl⟩ : syracuseStep 16751447 = 25127171) B25127171
theorem B11167631 : Blo 2205435 11167631 := bstep (se 1 (by rfl) ⟨8375723, by rfl⟩ : syracuseStep 11167631 = 16751447) B16751447
theorem B7445087 : Blo 2205435 7445087 := bstep (se 1 (by rfl) ⟨5583815, by rfl⟩ : syracuseStep 7445087 = 11167631) B11167631
theorem B4963391 : Blo 2205435 4963391 := bstep (se 1 (by rfl) ⟨3722543, by rfl⟩ : syracuseStep 4963391 = 7445087) B7445087
theorem B3308927 : Blo 2205435 3308927 := bstep (se 1 (by rfl) ⟨2481695, by rfl⟩ : syracuseStep 3308927 = 4963391) B4963391
theorem B2205951 : Blo 2205435 2205951 := bstep (se 1 (by rfl) ⟨1654463, by rfl⟩ : syracuseStep 2205951 = 3308927) B3308927
theorem B3308933 : Blo 2205435 3308933 := bbase (se 4 (by rfl) ⟨310212, by rfl⟩ : syracuseStep 3308933 = 620425) (by norm_num)
theorem B2205955 : Blo 2205435 2205955 := bstep (se 1 (by rfl) ⟨1654466, by rfl⟩ : syracuseStep 2205955 = 3308933) B3308933
theorem B3722557 : Blo 2205435 3722557 := bbase (se 3 (by rfl) ⟨697979, by rfl⟩ : syracuseStep 3722557 = 1395959) (by norm_num)
theorem B4963409 : Blo 2205435 4963409 := bstep (se 2 (by rfl) ⟨1861278, by rfl⟩ : syracuseStep 4963409 = 3722557) B3722557
theorem B3308939 : Blo 2205435 3308939 := bstep (se 1 (by rfl) ⟨2481704, by rfl⟩ : syracuseStep 3308939 = 4963409) B4963409
theorem B2205959 : Blo 2205435 2205959 := bstep (se 1 (by rfl) ⟨1654469, by rfl⟩ : syracuseStep 2205959 = 3308939) B3308939
theorem B2481709 : Blo 2205435 2481709 := bbase (se 3 (by rfl) ⟨465320, by rfl⟩ : syracuseStep 2481709 = 930641) (by norm_num)
theorem B3308945 : Blo 2205435 3308945 := bstep (se 2 (by rfl) ⟨1240854, by rfl⟩ : syracuseStep 3308945 = 2481709) B2481709
theorem B2205963 : Blo 2205435 2205963 := bstep (se 1 (by rfl) ⟨1654472, by rfl⟩ : syracuseStep 2205963 = 3308945) B3308945
theorem B7445141 : Blo 2205435 7445141 := bbase (se 6 (by rfl) ⟨174495, by rfl⟩ : syracuseStep 7445141 = 348991) (by norm_num)
theorem B4963427 : Blo 2205435 4963427 := bstep (se 1 (by rfl) ⟨3722570, by rfl⟩ : syracuseStep 4963427 = 7445141) B7445141
theorem B3308951 : Blo 2205435 3308951 := bstep (se 1 (by rfl) ⟨2481713, by rfl⟩ : syracuseStep 3308951 = 4963427) B4963427
theorem B2205967 : Blo 2205435 2205967 := bstep (se 1 (by rfl) ⟨1654475, by rfl⟩ : syracuseStep 2205967 = 3308951) B3308951
theorem B3308957 : Blo 2205435 3308957 := bbase (se 3 (by rfl) ⟨620429, by rfl⟩ : syracuseStep 3308957 = 1240859) (by norm_num)
theorem B2205971 : Blo 2205435 2205971 := bstep (se 1 (by rfl) ⟨1654478, by rfl⟩ : syracuseStep 2205971 = 3308957) B3308957
theorem B4963445 : Blo 2205435 4963445 := bbase (se 5 (by rfl) ⟨232661, by rfl⟩ : syracuseStep 4963445 = 465323) (by norm_num)
theorem B3308963 : Blo 2205435 3308963 := bstep (se 1 (by rfl) ⟨2481722, by rfl⟩ : syracuseStep 3308963 = 4963445) B4963445
theorem B2205975 : Blo 2205435 2205975 := bstep (se 1 (by rfl) ⟨1654481, by rfl⟩ : syracuseStep 2205975 = 3308963) B3308963
theorem B18845621 : Blo 2205435 18845621 := bbase (se 5 (by rfl) ⟨883388, by rfl⟩ : syracuseStep 18845621 = 1766777) (by norm_num)
theorem B12563747 : Blo 2205435 12563747 := bstep (se 1 (by rfl) ⟨9422810, by rfl⟩ : syracuseStep 12563747 = 18845621) B18845621
theorem B8375831 : Blo 2205435 8375831 := bstep (se 1 (by rfl) ⟨6281873, by rfl⟩ : syracuseStep 8375831 = 12563747) B12563747
theorem B5583887 : Blo 2205435 5583887 := bstep (se 1 (by rfl) ⟨4187915, by rfl⟩ : syracuseStep 5583887 = 8375831) B8375831
theorem B3722591 : Blo 2205435 3722591 := bstep (se 1 (by rfl) ⟨2791943, by rfl⟩ : syracuseStep 3722591 = 5583887) B5583887
theorem B2481727 : Blo 2205435 2481727 := bstep (se 1 (by rfl) ⟨1861295, by rfl⟩ : syracuseStep 2481727 = 3722591) B3722591
theorem B3308969 : Blo 2205435 3308969 := bstep (se 2 (by rfl) ⟨1240863, by rfl⟩ : syracuseStep 3308969 = 2481727) B2481727
theorem B2205979 : Blo 2205435 2205979 := bstep (se 1 (by rfl) ⟨1654484, by rfl⟩ : syracuseStep 2205979 = 3308969) B3308969
theorem B8375845 : Blo 2205435 8375845 := bbase (se 4 (by rfl) ⟨785235, by rfl⟩ : syracuseStep 8375845 = 1570471) (by norm_num)
theorem B11167793 : Blo 2205435 11167793 := bstep (se 2 (by rfl) ⟨4187922, by rfl⟩ : syracuseStep 11167793 = 8375845) B8375845
theorem B7445195 : Blo 2205435 7445195 := bstep (se 1 (by rfl) ⟨5583896, by rfl⟩ : syracuseStep 7445195 = 11167793) B11167793
theorem B4963463 : Blo 2205435 4963463 := bstep (se 1 (by rfl) ⟨3722597, by rfl⟩ : syracuseStep 4963463 = 7445195) B7445195
theorem B3308975 : Blo 2205435 3308975 := bstep (se 1 (by rfl) ⟨2481731, by rfl⟩ : syracuseStep 3308975 = 4963463) B4963463
theorem B2205983 : Blo 2205435 2205983 := bstep (se 1 (by rfl) ⟨1654487, by rfl⟩ : syracuseStep 2205983 = 3308975) B3308975
theorem B3308981 : Blo 2205435 3308981 := bbase (se 5 (by rfl) ⟨155108, by rfl⟩ : syracuseStep 3308981 = 310217) (by norm_num)
theorem B2205987 : Blo 2205435 2205987 := bstep (se 1 (by rfl) ⟨1654490, by rfl⟩ : syracuseStep 2205987 = 3308981) B3308981
theorem B5583917 : Blo 2205435 5583917 := bbase (se 3 (by rfl) ⟨1046984, by rfl⟩ : syracuseStep 5583917 = 2093969) (by norm_num)
theorem B3722611 : Blo 2205435 3722611 := bstep (se 1 (by rfl) ⟨2791958, by rfl⟩ : syracuseStep 3722611 = 5583917) B5583917
theorem B4963481 : Blo 2205435 4963481 := bstep (se 2 (by rfl) ⟨1861305, by rfl⟩ : syracuseStep 4963481 = 3722611) B3722611
theorem B3308987 : Blo 2205435 3308987 := bstep (se 1 (by rfl) ⟨2481740, by rfl⟩ : syracuseStep 3308987 = 4963481) B4963481
theorem B2205991 : Blo 2205435 2205991 := bstep (se 1 (by rfl) ⟨1654493, by rfl⟩ : syracuseStep 2205991 = 3308987) B3308987
theorem B2481745 : Blo 2205435 2481745 := bbase (se 2 (by rfl) ⟨930654, by rfl⟩ : syracuseStep 2481745 = 1861309) (by norm_num)
theorem B3308993 : Blo 2205435 3308993 := bstep (se 2 (by rfl) ⟨1240872, by rfl⟩ : syracuseStep 3308993 = 2481745) B2481745
theorem B2205995 : Blo 2205435 2205995 := bstep (se 1 (by rfl) ⟨1654496, by rfl⟩ : syracuseStep 2205995 = 3308993) B3308993
theorem B3140965 : Blo 2205435 3140965 := bbase (se 4 (by rfl) ⟨294465, by rfl⟩ : syracuseStep 3140965 = 588931) (by norm_num)
theorem B4187953 : Blo 2205435 4187953 := bstep (se 2 (by rfl) ⟨1570482, by rfl⟩ : syracuseStep 4187953 = 3140965) B3140965
theorem B5583937 : Blo 2205435 5583937 := bstep (se 2 (by rfl) ⟨2093976, by rfl⟩ : syracuseStep 5583937 = 4187953) B4187953
theorem B7445249 : Blo 2205435 7445249 := bstep (se 2 (by rfl) ⟨2791968, by rfl⟩ : syracuseStep 7445249 = 5583937) B5583937
theorem B4963499 : Blo 2205435 4963499 := bstep (se 1 (by rfl) ⟨3722624, by rfl⟩ : syracuseStep 4963499 = 7445249) B7445249
theorem B3308999 : Blo 2205435 3308999 := bstep (se 1 (by rfl) ⟨2481749, by rfl⟩ : syracuseStep 3308999 = 4963499) B4963499
theorem B2205999 : Blo 2205435 2205999 := bstep (se 1 (by rfl) ⟨1654499, by rfl⟩ : syracuseStep 2205999 = 3308999) B3308999
theorem B3309005 : Blo 2205435 3309005 := bbase (se 3 (by rfl) ⟨620438, by rfl⟩ : syracuseStep 3309005 = 1240877) (by norm_num)
theorem B2206003 : Blo 2205435 2206003 := bstep (se 1 (by rfl) ⟨1654502, by rfl⟩ : syracuseStep 2206003 = 3309005) B3309005
theorem B4963517 : Blo 2205435 4963517 := bbase (se 3 (by rfl) ⟨930659, by rfl⟩ : syracuseStep 4963517 = 1861319) (by norm_num)
theorem B3309011 : Blo 2205435 3309011 := bstep (se 1 (by rfl) ⟨2481758, by rfl⟩ : syracuseStep 3309011 = 4963517) B4963517
theorem B2206007 : Blo 2205435 2206007 := bstep (se 1 (by rfl) ⟨1654505, by rfl⟩ : syracuseStep 2206007 = 3309011) B3309011
theorem B3722645 : Blo 2205435 3722645 := bbase (se 6 (by rfl) ⟨87249, by rfl⟩ : syracuseStep 3722645 = 174499) (by norm_num)
theorem B2481763 : Blo 2205435 2481763 := bstep (se 1 (by rfl) ⟨1861322, by rfl⟩ : syracuseStep 2481763 = 3722645) B3722645
theorem B3309017 : Blo 2205435 3309017 := bstep (se 2 (by rfl) ⟨1240881, by rfl⟩ : syracuseStep 3309017 = 2481763) B2481763
theorem B2206011 : Blo 2205435 2206011 := bstep (se 1 (by rfl) ⟨1654508, by rfl⟩ : syracuseStep 2206011 = 3309017) B3309017
theorem B2981485 : Blo 2205435 2981485 := bbase (se 3 (by rfl) ⟨559028, by rfl⟩ : syracuseStep 2981485 = 1118057) (by norm_num)
theorem B3975313 : Blo 2205435 3975313 := bstep (se 2 (by rfl) ⟨1490742, by rfl⟩ : syracuseStep 3975313 = 2981485) B2981485
theorem B5300417 : Blo 2205435 5300417 := bstep (se 2 (by rfl) ⟨1987656, by rfl⟩ : syracuseStep 5300417 = 3975313) B3975313
theorem B14134445 : Blo 2205435 14134445 := bstep (se 3 (by rfl) ⟨2650208, by rfl⟩ : syracuseStep 14134445 = 5300417) B5300417
theorem B9422963 : Blo 2205435 9422963 := bstep (se 1 (by rfl) ⟨7067222, by rfl⟩ : syracuseStep 9422963 = 14134445) B14134445
theorem B6281975 : Blo 2205435 6281975 := bstep (se 1 (by rfl) ⟨4711481, by rfl⟩ : syracuseStep 6281975 = 9422963) B9422963
theorem B16751933 : Blo 2205435 16751933 := bstep (se 3 (by rfl) ⟨3140987, by rfl⟩ : syracuseStep 16751933 = 6281975) B6281975
theorem B11167955 : Blo 2205435 11167955 := bstep (se 1 (by rfl) ⟨8375966, by rfl⟩ : syracuseStep 11167955 = 16751933) B16751933
theorem B7445303 : Blo 2205435 7445303 := bstep (se 1 (by rfl) ⟨5583977, by rfl⟩ : syracuseStep 7445303 = 11167955) B11167955
theorem B4963535 : Blo 2205435 4963535 := bstep (se 1 (by rfl) ⟨3722651, by rfl⟩ : syracuseStep 4963535 = 7445303) B7445303
theorem B3309023 : Blo 2205435 3309023 := bstep (se 1 (by rfl) ⟨2481767, by rfl⟩ : syracuseStep 3309023 = 4963535) B4963535
theorem B2206015 : Blo 2205435 2206015 := bstep (se 1 (by rfl) ⟨1654511, by rfl⟩ : syracuseStep 2206015 = 3309023) B3309023
theorem B3309029 : Blo 2205435 3309029 := bbase (se 4 (by rfl) ⟨310221, by rfl⟩ : syracuseStep 3309029 = 620443) (by norm_num)
theorem B2206019 : Blo 2205435 2206019 := bstep (se 1 (by rfl) ⟨1654514, by rfl⟩ : syracuseStep 2206019 = 3309029) B3309029
theorem B21201749 : Blo 2205435 21201749 := bbase (se 9 (by rfl) ⟨62114, by rfl⟩ : syracuseStep 21201749 = 124229) (by norm_num)
theorem B14134499 : Blo 2205435 14134499 := bstep (se 1 (by rfl) ⟨10600874, by rfl⟩ : syracuseStep 14134499 = 21201749) B21201749
theorem B9422999 : Blo 2205435 9422999 := bstep (se 1 (by rfl) ⟨7067249, by rfl⟩ : syracuseStep 9422999 = 14134499) B14134499
theorem B6281999 : Blo 2205435 6281999 := bstep (se 1 (by rfl) ⟨4711499, by rfl⟩ : syracuseStep 6281999 = 9422999) B9422999
theorem B4187999 : Blo 2205435 4187999 := bstep (se 1 (by rfl) ⟨3140999, by rfl⟩ : syracuseStep 4187999 = 6281999) B6281999
theorem B2791999 : Blo 2205435 2791999 := bstep (se 1 (by rfl) ⟨2093999, by rfl⟩ : syracuseStep 2791999 = 4187999) B4187999
theorem B3722665 : Blo 2205435 3722665 := bstep (se 2 (by rfl) ⟨1395999, by rfl⟩ : syracuseStep 3722665 = 2791999) B2791999
theorem B4963553 : Blo 2205435 4963553 := bstep (se 2 (by rfl) ⟨1861332, by rfl⟩ : syracuseStep 4963553 = 3722665) B3722665
theorem B3309035 : Blo 2205435 3309035 := bstep (se 1 (by rfl) ⟨2481776, by rfl⟩ : syracuseStep 3309035 = 4963553) B4963553
theorem B2206023 : Blo 2205435 2206023 := bstep (se 1 (by rfl) ⟨1654517, by rfl⟩ : syracuseStep 2206023 = 3309035) B3309035
theorem B2481781 : Blo 2205435 2481781 := bbase (se 5 (by rfl) ⟨116333, by rfl⟩ : syracuseStep 2481781 = 232667) (by norm_num)
theorem B3309041 : Blo 2205435 3309041 := bstep (se 2 (by rfl) ⟨1240890, by rfl⟩ : syracuseStep 3309041 = 2481781) B2481781
theorem B2206027 : Blo 2205435 2206027 := bstep (se 1 (by rfl) ⟨1654520, by rfl⟩ : syracuseStep 2206027 = 3309041) B3309041
theorem B2792009 : Blo 2205435 2792009 := bbase (se 2 (by rfl) ⟨1047003, by rfl⟩ : syracuseStep 2792009 = 2094007) (by norm_num)
theorem B7445357 : Blo 2205435 7445357 := bstep (se 3 (by rfl) ⟨1396004, by rfl⟩ : syracuseStep 7445357 = 2792009) B2792009
theorem B4963571 : Blo 2205435 4963571 := bstep (se 1 (by rfl) ⟨3722678, by rfl⟩ : syracuseStep 4963571 = 7445357) B7445357
theorem B3309047 : Blo 2205435 3309047 := bstep (se 1 (by rfl) ⟨2481785, by rfl⟩ : syracuseStep 3309047 = 4963571) B4963571
theorem B2206031 : Blo 2205435 2206031 := bstep (se 1 (by rfl) ⟨1654523, by rfl⟩ : syracuseStep 2206031 = 3309047) B3309047
theorem B3309053 : Blo 2205435 3309053 := bbase (se 3 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 3309053 = 1240895) (by norm_num)
theorem B2206035 : Blo 2205435 2206035 := bstep (se 1 (by rfl) ⟨1654526, by rfl⟩ : syracuseStep 2206035 = 3309053) B3309053
theorem B4963589 : Blo 2205435 4963589 := bbase (se 4 (by rfl) ⟨465336, by rfl⟩ : syracuseStep 4963589 = 930673) (by norm_num)
theorem B3309059 : Blo 2205435 3309059 := bstep (se 1 (by rfl) ⟨2481794, by rfl⟩ : syracuseStep 3309059 = 4963589) B4963589
theorem B2206039 : Blo 2205435 2206039 := bstep (se 1 (by rfl) ⟨1654529, by rfl⟩ : syracuseStep 2206039 = 3309059) B3309059
theorem B4188037 : Blo 2205435 4188037 := bbase (se 4 (by rfl) ⟨392628, by rfl⟩ : syracuseStep 4188037 = 785257) (by norm_num)
theorem B5584049 : Blo 2205435 5584049 := bstep (se 2 (by rfl) ⟨2094018, by rfl⟩ : syracuseStep 5584049 = 4188037) B4188037
theorem B3722699 : Blo 2205435 3722699 := bstep (se 1 (by rfl) ⟨2792024, by rfl⟩ : syracuseStep 3722699 = 5584049) B5584049
theorem B2481799 : Blo 2205435 2481799 := bstep (se 1 (by rfl) ⟨1861349, by rfl⟩ : syracuseStep 2481799 = 3722699) B3722699
theorem B3309065 : Blo 2205435 3309065 := bstep (se 2 (by rfl) ⟨1240899, by rfl⟩ : syracuseStep 3309065 = 2481799) B2481799
theorem B2206043 : Blo 2205435 2206043 := bstep (se 1 (by rfl) ⟨1654532, by rfl⟩ : syracuseStep 2206043 = 3309065) B3309065
theorem B11168117 : Blo 2205435 11168117 := bbase (se 5 (by rfl) ⟨523505, by rfl⟩ : syracuseStep 11168117 = 1047011) (by norm_num)
theorem B7445411 : Blo 2205435 7445411 := bstep (se 1 (by rfl) ⟨5584058, by rfl⟩ : syracuseStep 7445411 = 11168117) B11168117
theorem B4963607 : Blo 2205435 4963607 := bstep (se 1 (by rfl) ⟨3722705, by rfl⟩ : syracuseStep 4963607 = 7445411) B7445411
theorem B3309071 : Blo 2205435 3309071 := bstep (se 1 (by rfl) ⟨2481803, by rfl⟩ : syracuseStep 3309071 = 4963607) B4963607
theorem B2206047 : Blo 2205435 2206047 := bstep (se 1 (by rfl) ⟨1654535, by rfl⟩ : syracuseStep 2206047 = 3309071) B3309071
theorem B3309077 : Blo 2205435 3309077 := bbase (se 6 (by rfl) ⟨77556, by rfl⟩ : syracuseStep 3309077 = 155113) (by norm_num)
theorem B2206051 : Blo 2205435 2206051 := bstep (se 1 (by rfl) ⟨1654538, by rfl⟩ : syracuseStep 2206051 = 3309077) B3309077
theorem B4472309 : Blo 2205435 4472309 := bbase (se 5 (by rfl) ⟨209639, by rfl⟩ : syracuseStep 4472309 = 419279) (by norm_num)
theorem B2981539 : Blo 2205435 2981539 := bstep (se 1 (by rfl) ⟨2236154, by rfl⟩ : syracuseStep 2981539 = 4472309) B4472309
theorem B15901541 : Blo 2205435 15901541 := bstep (se 4 (by rfl) ⟨1490769, by rfl⟩ : syracuseStep 15901541 = 2981539) B2981539
theorem B10601027 : Blo 2205435 10601027 := bstep (se 1 (by rfl) ⟨7950770, by rfl⟩ : syracuseStep 10601027 = 15901541) B15901541
theorem B7067351 : Blo 2205435 7067351 := bstep (se 1 (by rfl) ⟨5300513, by rfl⟩ : syracuseStep 7067351 = 10601027) B10601027
theorem B18846269 : Blo 2205435 18846269 := bstep (se 3 (by rfl) ⟨3533675, by rfl⟩ : syracuseStep 18846269 = 7067351) B7067351
theorem B12564179 : Blo 2205435 12564179 := bstep (se 1 (by rfl) ⟨9423134, by rfl⟩ : syracuseStep 12564179 = 18846269) B18846269
theorem B8376119 : Blo 2205435 8376119 := bstep (se 1 (by rfl) ⟨6282089, by rfl⟩ : syracuseStep 8376119 = 12564179) B12564179
theorem B5584079 : Blo 2205435 5584079 := bstep (se 1 (by rfl) ⟨4188059, by rfl⟩ : syracuseStep 5584079 = 8376119) B8376119
theorem B3722719 : Blo 2205435 3722719 := bstep (se 1 (by rfl) ⟨2792039, by rfl⟩ : syracuseStep 3722719 = 5584079) B5584079
theorem B4963625 : Blo 2205435 4963625 := bstep (se 2 (by rfl) ⟨1861359, by rfl⟩ : syracuseStep 4963625 = 3722719) B3722719
theorem B3309083 : Blo 2205435 3309083 := bstep (se 1 (by rfl) ⟨2481812, by rfl⟩ : syracuseStep 3309083 = 4963625) B4963625
theorem B2206055 : Blo 2205435 2206055 := bstep (se 1 (by rfl) ⟨1654541, by rfl⟩ : syracuseStep 2206055 = 3309083) B3309083
theorem B2481817 : Blo 2205435 2481817 := bbase (se 2 (by rfl) ⟨930681, by rfl⟩ : syracuseStep 2481817 = 1861363) (by norm_num)
theorem B3309089 : Blo 2205435 3309089 := bstep (se 2 (by rfl) ⟨1240908, by rfl⟩ : syracuseStep 3309089 = 2481817) B2481817
theorem B2206059 : Blo 2205435 2206059 := bstep (se 1 (by rfl) ⟨1654544, by rfl⟩ : syracuseStep 2206059 = 3309089) B3309089
theorem B8376149 : Blo 2205435 8376149 := bbase (se 9 (by rfl) ⟨24539, by rfl⟩ : syracuseStep 8376149 = 49079) (by norm_num)
theorem B5584099 : Blo 2205435 5584099 := bstep (se 1 (by rfl) ⟨4188074, by rfl⟩ : syracuseStep 5584099 = 8376149) B8376149
theorem B7445465 : Blo 2205435 7445465 := bstep (se 2 (by rfl) ⟨2792049, by rfl⟩ : syracuseStep 7445465 = 5584099) B5584099
theorem B4963643 : Blo 2205435 4963643 := bstep (se 1 (by rfl) ⟨3722732, by rfl⟩ : syracuseStep 4963643 = 7445465) B7445465
theorem B3309095 : Blo 2205435 3309095 := bstep (se 1 (by rfl) ⟨2481821, by rfl⟩ : syracuseStep 3309095 = 4963643) B4963643
theorem B2206063 : Blo 2205435 2206063 := bstep (se 1 (by rfl) ⟨1654547, by rfl⟩ : syracuseStep 2206063 = 3309095) B3309095
theorem B3309101 : Blo 2205435 3309101 := bbase (se 3 (by rfl) ⟨620456, by rfl⟩ : syracuseStep 3309101 = 1240913) (by norm_num)
theorem B2206067 : Blo 2205435 2206067 := bstep (se 1 (by rfl) ⟨1654550, by rfl⟩ : syracuseStep 2206067 = 3309101) B3309101
theorem B4963661 : Blo 2205435 4963661 := bbase (se 3 (by rfl) ⟨930686, by rfl⟩ : syracuseStep 4963661 = 1861373) (by norm_num)
theorem B3309107 : Blo 2205435 3309107 := bstep (se 1 (by rfl) ⟨2481830, by rfl⟩ : syracuseStep 3309107 = 4963661) B4963661
theorem B2206071 : Blo 2205435 2206071 := bstep (se 1 (by rfl) ⟨1654553, by rfl⟩ : syracuseStep 2206071 = 3309107) B3309107
theorem B2792065 : Blo 2205435 2792065 := bbase (se 2 (by rfl) ⟨1047024, by rfl⟩ : syracuseStep 2792065 = 2094049) (by norm_num)
theorem B3722753 : Blo 2205435 3722753 := bstep (se 2 (by rfl) ⟨1396032, by rfl⟩ : syracuseStep 3722753 = 2792065) B2792065
theorem B2481835 : Blo 2205435 2481835 := bstep (se 1 (by rfl) ⟨1861376, by rfl⟩ : syracuseStep 2481835 = 3722753) B3722753
theorem B3309113 : Blo 2205435 3309113 := bstep (se 2 (by rfl) ⟨1240917, by rfl⟩ : syracuseStep 3309113 = 2481835) B2481835
theorem B2206075 : Blo 2205435 2206075 := bstep (se 1 (by rfl) ⟨1654556, by rfl⟩ : syracuseStep 2206075 = 3309113) B3309113
theorem B2355809 : Blo 2205435 2355809 := bbase (se 2 (by rfl) ⟨883428, by rfl⟩ : syracuseStep 2355809 = 1766857) (by norm_num)
theorem B25128629 : Blo 2205435 25128629 := bstep (se 5 (by rfl) ⟨1177904, by rfl⟩ : syracuseStep 25128629 = 2355809) B2355809
theorem B16752419 : Blo 2205435 16752419 := bstep (se 1 (by rfl) ⟨12564314, by rfl⟩ : syracuseStep 16752419 = 25128629) B25128629
theorem B11168279 : Blo 2205435 11168279 := bstep (se 1 (by rfl) ⟨8376209, by rfl⟩ : syracuseStep 11168279 = 16752419) B16752419
theorem B7445519 : Blo 2205435 7445519 := bstep (se 1 (by rfl) ⟨5584139, by rfl⟩ : syracuseStep 7445519 = 11168279) B11168279
theorem B4963679 : Blo 2205435 4963679 := bstep (se 1 (by rfl) ⟨3722759, by rfl⟩ : syracuseStep 4963679 = 7445519) B7445519
theorem B3309119 : Blo 2205435 3309119 := bstep (se 1 (by rfl) ⟨2481839, by rfl⟩ : syracuseStep 3309119 = 4963679) B4963679
theorem B2206079 : Blo 2205435 2206079 := bstep (se 1 (by rfl) ⟨1654559, by rfl⟩ : syracuseStep 2206079 = 3309119) B3309119
theorem B3309125 : Blo 2205435 3309125 := bbase (se 4 (by rfl) ⟨310230, by rfl⟩ : syracuseStep 3309125 = 620461) (by norm_num)
theorem B2206083 : Blo 2205435 2206083 := bstep (se 1 (by rfl) ⟨1654562, by rfl⟩ : syracuseStep 2206083 = 3309125) B3309125
theorem B3722773 : Blo 2205435 3722773 := bbase (se 6 (by rfl) ⟨87252, by rfl⟩ : syracuseStep 3722773 = 174505) (by norm_num)
theorem B4963697 : Blo 2205435 4963697 := bstep (se 2 (by rfl) ⟨1861386, by rfl⟩ : syracuseStep 4963697 = 3722773) B3722773
theorem B3309131 : Blo 2205435 3309131 := bstep (se 1 (by rfl) ⟨2481848, by rfl⟩ : syracuseStep 3309131 = 4963697) B4963697
theorem B2206087 : Blo 2205435 2206087 := bstep (se 1 (by rfl) ⟨1654565, by rfl⟩ : syracuseStep 2206087 = 3309131) B3309131
theorem B2481853 : Blo 2205435 2481853 := bbase (se 3 (by rfl) ⟨465347, by rfl⟩ : syracuseStep 2481853 = 930695) (by norm_num)
theorem B3309137 : Blo 2205435 3309137 := bstep (se 2 (by rfl) ⟨1240926, by rfl⟩ : syracuseStep 3309137 = 2481853) B2481853
theorem B2206091 : Blo 2205435 2206091 := bstep (se 1 (by rfl) ⟨1654568, by rfl⟩ : syracuseStep 2206091 = 3309137) B3309137
theorem B7445573 : Blo 2205435 7445573 := bbase (se 4 (by rfl) ⟨698022, by rfl⟩ : syracuseStep 7445573 = 1396045) (by norm_num)
theorem B4963715 : Blo 2205435 4963715 := bstep (se 1 (by rfl) ⟨3722786, by rfl⟩ : syracuseStep 4963715 = 7445573) B7445573
theorem B3309143 : Blo 2205435 3309143 := bstep (se 1 (by rfl) ⟨2481857, by rfl⟩ : syracuseStep 3309143 = 4963715) B4963715
theorem B2206095 : Blo 2205435 2206095 := bstep (se 1 (by rfl) ⟨1654571, by rfl⟩ : syracuseStep 2206095 = 3309143) B3309143
theorem B3309149 : Blo 2205435 3309149 := bbase (se 3 (by rfl) ⟨620465, by rfl⟩ : syracuseStep 3309149 = 1240931) (by norm_num)
theorem B2206099 : Blo 2205435 2206099 := bstep (se 1 (by rfl) ⟨1654574, by rfl⟩ : syracuseStep 2206099 = 3309149) B3309149
theorem B4963733 : Blo 2205435 4963733 := bbase (se 6 (by rfl) ⟨116337, by rfl⟩ : syracuseStep 4963733 = 232675) (by norm_num)
theorem B3309155 : Blo 2205435 3309155 := bstep (se 1 (by rfl) ⟨2481866, by rfl⟩ : syracuseStep 3309155 = 4963733) B4963733
theorem B2206103 : Blo 2205435 2206103 := bstep (se 1 (by rfl) ⟨1654577, by rfl⟩ : syracuseStep 2206103 = 3309155) B3309155
theorem B10339397 : Blo 2205435 10339397 := bbase (se 4 (by rfl) ⟨969318, by rfl⟩ : syracuseStep 10339397 = 1938637) (by norm_num)
theorem B6892931 : Blo 2205435 6892931 := bstep (se 1 (by rfl) ⟨5169698, by rfl⟩ : syracuseStep 6892931 = 10339397) B10339397
theorem B4595287 : Blo 2205435 4595287 := bstep (se 1 (by rfl) ⟨3446465, by rfl⟩ : syracuseStep 4595287 = 6892931) B6892931
theorem B6127049 : Blo 2205435 6127049 := bstep (se 2 (by rfl) ⟨2297643, by rfl⟩ : syracuseStep 6127049 = 4595287) B4595287
theorem B16338797 : Blo 2205435 16338797 := bstep (se 3 (by rfl) ⟨3063524, by rfl⟩ : syracuseStep 16338797 = 6127049) B6127049
theorem B10892531 : Blo 2205435 10892531 := bstep (se 1 (by rfl) ⟨8169398, by rfl⟩ : syracuseStep 10892531 = 16338797) B16338797
theorem B7261687 : Blo 2205435 7261687 := bstep (se 1 (by rfl) ⟨5446265, by rfl⟩ : syracuseStep 7261687 = 10892531) B10892531
theorem B9682249 : Blo 2205435 9682249 := bstep (se 2 (by rfl) ⟨3630843, by rfl⟩ : syracuseStep 9682249 = 7261687) B7261687
theorem B12909665 : Blo 2205435 12909665 := bstep (se 2 (by rfl) ⟨4841124, by rfl⟩ : syracuseStep 12909665 = 9682249) B9682249
theorem B34425773 : Blo 2205435 34425773 := bstep (se 3 (by rfl) ⟨6454832, by rfl⟩ : syracuseStep 34425773 = 12909665) B12909665
theorem B22950515 : Blo 2205435 22950515 := bstep (se 1 (by rfl) ⟨17212886, by rfl⟩ : syracuseStep 22950515 = 34425773) B34425773
theorem B15300343 : Blo 2205435 15300343 := bstep (se 1 (by rfl) ⟨11475257, by rfl⟩ : syracuseStep 15300343 = 22950515) B22950515
theorem B20400457 : Blo 2205435 20400457 := bstep (se 2 (by rfl) ⟨7650171, by rfl⟩ : syracuseStep 20400457 = 15300343) B15300343
theorem B27200609 : Blo 2205435 27200609 := bstep (se 2 (by rfl) ⟨10200228, by rfl⟩ : syracuseStep 27200609 = 20400457) B20400457
theorem B18133739 : Blo 2205435 18133739 := bstep (se 1 (by rfl) ⟨13600304, by rfl⟩ : syracuseStep 18133739 = 27200609) B27200609
theorem B12089159 : Blo 2205435 12089159 := bstep (se 1 (by rfl) ⟨9066869, by rfl⟩ : syracuseStep 12089159 = 18133739) B18133739
theorem B8059439 : Blo 2205435 8059439 := bstep (se 1 (by rfl) ⟨6044579, by rfl⟩ : syracuseStep 8059439 = 12089159) B12089159
theorem B5372959 : Blo 2205435 5372959 := bstep (se 1 (by rfl) ⟨4029719, by rfl⟩ : syracuseStep 5372959 = 8059439) B8059439
theorem B7163945 : Blo 2205435 7163945 := bstep (se 2 (by rfl) ⟨2686479, by rfl⟩ : syracuseStep 7163945 = 5372959) B5372959
theorem B4775963 : Blo 2205435 4775963 := bstep (se 1 (by rfl) ⟨3581972, by rfl⟩ : syracuseStep 4775963 = 7163945) B7163945
theorem B12735901 : Blo 2205435 12735901 := bstep (se 3 (by rfl) ⟨2387981, by rfl⟩ : syracuseStep 12735901 = 4775963) B4775963
theorem B16981201 : Blo 2205435 16981201 := bstep (se 2 (by rfl) ⟨6367950, by rfl⟩ : syracuseStep 16981201 = 12735901) B12735901
theorem B22641601 : Blo 2205435 22641601 := bstep (se 2 (by rfl) ⟨8490600, by rfl⟩ : syracuseStep 22641601 = 16981201) B16981201
theorem B30188801 : Blo 2205435 30188801 := bstep (se 2 (by rfl) ⟨11320800, by rfl⟩ : syracuseStep 30188801 = 22641601) B22641601
theorem B80503469 : Blo 2205435 80503469 := bstep (se 3 (by rfl) ⟨15094400, by rfl⟩ : syracuseStep 80503469 = 30188801) B30188801
theorem B53668979 : Blo 2205435 53668979 := bstep (se 1 (by rfl) ⟨40251734, by rfl⟩ : syracuseStep 53668979 = 80503469) B80503469
theorem B35779319 : Blo 2205435 35779319 := bstep (se 1 (by rfl) ⟨26834489, by rfl⟩ : syracuseStep 35779319 = 53668979) B53668979
theorem B23852879 : Blo 2205435 23852879 := bstep (se 1 (by rfl) ⟨17889659, by rfl⟩ : syracuseStep 23852879 = 35779319) B35779319
theorem B15901919 : Blo 2205435 15901919 := bstep (se 1 (by rfl) ⟨11926439, by rfl⟩ : syracuseStep 15901919 = 23852879) B23852879
theorem B10601279 : Blo 2205435 10601279 := bstep (se 1 (by rfl) ⟨7950959, by rfl⟩ : syracuseStep 10601279 = 15901919) B15901919
theorem B7067519 : Blo 2205435 7067519 := bstep (se 1 (by rfl) ⟨5300639, by rfl⟩ : syracuseStep 7067519 = 10601279) B10601279
theorem B4711679 : Blo 2205435 4711679 := bstep (se 1 (by rfl) ⟨3533759, by rfl⟩ : syracuseStep 4711679 = 7067519) B7067519
theorem B3141119 : Blo 2205435 3141119 := bstep (se 1 (by rfl) ⟨2355839, by rfl⟩ : syracuseStep 3141119 = 4711679) B4711679
theorem B8376317 : Blo 2205435 8376317 := bstep (se 3 (by rfl) ⟨1570559, by rfl⟩ : syracuseStep 8376317 = 3141119) B3141119
theorem B5584211 : Blo 2205435 5584211 := bstep (se 1 (by rfl) ⟨4188158, by rfl⟩ : syracuseStep 5584211 = 8376317) B8376317
theorem B3722807 : Blo 2205435 3722807 := bstep (se 1 (by rfl) ⟨2792105, by rfl⟩ : syracuseStep 3722807 = 5584211) B5584211
theorem B2481871 : Blo 2205435 2481871 := bstep (se 1 (by rfl) ⟨1861403, by rfl⟩ : syracuseStep 2481871 = 3722807) B3722807
theorem B3309161 : Blo 2205435 3309161 := bstep (se 2 (by rfl) ⟨1240935, by rfl⟩ : syracuseStep 3309161 = 2481871) B2481871
theorem B2206107 : Blo 2205435 2206107 := bstep (se 1 (by rfl) ⟨1654580, by rfl⟩ : syracuseStep 2206107 = 3309161) B3309161
theorem B3533765 : Blo 2205435 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B9423373 : Blo 2205435 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B12564497 : Blo 2205435 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B8376331 : Blo 2205435 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B11168441 : Blo 2205435 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B7445627 : Blo 2205435 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B4963751 : Blo 2205435 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B3309167 : Blo 2205435 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B2206111 : Blo 2205435 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B3309173 : Blo 2205435 3309173 := bbase (se 5 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 3309173 = 310235) (by norm_num)
theorem B2206115 : Blo 2205435 2206115 := bstep (se 1 (by rfl) ⟨1654586, by rfl⟩ : syracuseStep 2206115 = 3309173) B3309173
theorem B4188181 : Blo 2205435 4188181 := bbase (se 6 (by rfl) ⟨98160, by rfl⟩ : syracuseStep 4188181 = 196321) (by norm_num)
theorem B5584241 : Blo 2205435 5584241 := bstep (se 2 (by rfl) ⟨2094090, by rfl⟩ : syracuseStep 5584241 = 4188181) B4188181
theorem B3722827 : Blo 2205435 3722827 := bstep (se 1 (by rfl) ⟨2792120, by rfl⟩ : syracuseStep 3722827 = 5584241) B5584241
theorem B4963769 : Blo 2205435 4963769 := bstep (se 2 (by rfl) ⟨1861413, by rfl⟩ : syracuseStep 4963769 = 3722827) B3722827
theorem B3309179 : Blo 2205435 3309179 := bstep (se 1 (by rfl) ⟨2481884, by rfl⟩ : syracuseStep 3309179 = 4963769) B4963769
theorem B2206119 : Blo 2205435 2206119 := bstep (se 1 (by rfl) ⟨1654589, by rfl⟩ : syracuseStep 2206119 = 3309179) B3309179
theorem B2481889 : Blo 2205435 2481889 := bbase (se 2 (by rfl) ⟨930708, by rfl⟩ : syracuseStep 2481889 = 1861417) (by norm_num)
theorem B3309185 : Blo 2205435 3309185 := bstep (se 2 (by rfl) ⟨1240944, by rfl⟩ : syracuseStep 3309185 = 2481889) B2481889
theorem B2206123 : Blo 2205435 2206123 := bstep (se 1 (by rfl) ⟨1654592, by rfl⟩ : syracuseStep 2206123 = 3309185) B3309185
theorem B5584261 : Blo 2205435 5584261 := bbase (se 4 (by rfl) ⟨523524, by rfl⟩ : syracuseStep 5584261 = 1047049) (by norm_num)
theorem B7445681 : Blo 2205435 7445681 := bstep (se 2 (by rfl) ⟨2792130, by rfl⟩ : syracuseStep 7445681 = 5584261) B5584261
theorem B4963787 : Blo 2205435 4963787 := bstep (se 1 (by rfl) ⟨3722840, by rfl⟩ : syracuseStep 4963787 = 7445681) B7445681
theorem B3309191 : Blo 2205435 3309191 := bstep (se 1 (by rfl) ⟨2481893, by rfl⟩ : syracuseStep 3309191 = 4963787) B4963787
theorem B2206127 : Blo 2205435 2206127 := bstep (se 1 (by rfl) ⟨1654595, by rfl⟩ : syracuseStep 2206127 = 3309191) B3309191
theorem B3309197 : Blo 2205435 3309197 := bbase (se 3 (by rfl) ⟨620474, by rfl⟩ : syracuseStep 3309197 = 1240949) (by norm_num)
theorem B2206131 : Blo 2205435 2206131 := bstep (se 1 (by rfl) ⟨1654598, by rfl⟩ : syracuseStep 2206131 = 3309197) B3309197
theorem B4963805 : Blo 2205435 4963805 := bbase (se 3 (by rfl) ⟨930713, by rfl⟩ : syracuseStep 4963805 = 1861427) (by norm_num)
theorem B3309203 : Blo 2205435 3309203 := bstep (se 1 (by rfl) ⟨2481902, by rfl⟩ : syracuseStep 3309203 = 4963805) B4963805
theorem B2206135 : Blo 2205435 2206135 := bstep (se 1 (by rfl) ⟨1654601, by rfl⟩ : syracuseStep 2206135 = 3309203) B3309203
theorem B3722861 : Blo 2205435 3722861 := bbase (se 3 (by rfl) ⟨698036, by rfl⟩ : syracuseStep 3722861 = 1396073) (by norm_num)
theorem B2481907 : Blo 2205435 2481907 := bstep (se 1 (by rfl) ⟨1861430, by rfl⟩ : syracuseStep 2481907 = 3722861) B3722861
theorem B3309209 : Blo 2205435 3309209 := bstep (se 2 (by rfl) ⟨1240953, by rfl⟩ : syracuseStep 3309209 = 2481907) B2481907
theorem B2206139 : Blo 2205435 2206139 := bstep (se 1 (by rfl) ⟨1654604, by rfl⟩ : syracuseStep 2206139 = 3309209) B3309209
theorem B3354365 : Blo 2205435 3354365 := bbase (se 3 (by rfl) ⟨628943, by rfl⟩ : syracuseStep 3354365 = 1257887) (by norm_num)
theorem B8944973 : Blo 2205435 8944973 := bstep (se 3 (by rfl) ⟨1677182, by rfl⟩ : syracuseStep 8944973 = 3354365) B3354365
theorem B5963315 : Blo 2205435 5963315 := bstep (se 1 (by rfl) ⟨4472486, by rfl⟩ : syracuseStep 5963315 = 8944973) B8944973
theorem B15902173 : Blo 2205435 15902173 := bstep (se 3 (by rfl) ⟨2981657, by rfl⟩ : syracuseStep 15902173 = 5963315) B5963315
theorem B21202897 : Blo 2205435 21202897 := bstep (se 2 (by rfl) ⟨7951086, by rfl⟩ : syracuseStep 21202897 = 15902173) B15902173
theorem B28270529 : Blo 2205435 28270529 := bstep (se 2 (by rfl) ⟨10601448, by rfl⟩ : syracuseStep 28270529 = 21202897) B21202897
theorem B18847019 : Blo 2205435 18847019 := bstep (se 1 (by rfl) ⟨14135264, by rfl⟩ : syracuseStep 18847019 = 28270529) B28270529
theorem B12564679 : Blo 2205435 12564679 := bstep (se 1 (by rfl) ⟨9423509, by rfl⟩ : syracuseStep 12564679 = 18847019) B18847019
theorem B16752905 : Blo 2205435 16752905 := bstep (se 2 (by rfl) ⟨6282339, by rfl⟩ : syracuseStep 16752905 = 12564679) B12564679
theorem B11168603 : Blo 2205435 11168603 := bstep (se 1 (by rfl) ⟨8376452, by rfl⟩ : syracuseStep 11168603 = 16752905) B16752905
theorem B7445735 : Blo 2205435 7445735 := bstep (se 1 (by rfl) ⟨5584301, by rfl⟩ : syracuseStep 7445735 = 11168603) B11168603
theorem B4963823 : Blo 2205435 4963823 := bstep (se 1 (by rfl) ⟨3722867, by rfl⟩ : syracuseStep 4963823 = 7445735) B7445735
theorem B3309215 : Blo 2205435 3309215 := bstep (se 1 (by rfl) ⟨2481911, by rfl⟩ : syracuseStep 3309215 = 4963823) B4963823
theorem B2206143 : Blo 2205435 2206143 := bstep (se 1 (by rfl) ⟨1654607, by rfl⟩ : syracuseStep 2206143 = 3309215) B3309215
theorem B3309221 : Blo 2205435 3309221 := bbase (se 4 (by rfl) ⟨310239, by rfl⟩ : syracuseStep 3309221 = 620479) (by norm_num)
theorem B2206147 : Blo 2205435 2206147 := bstep (se 1 (by rfl) ⟨1654610, by rfl⟩ : syracuseStep 2206147 = 3309221) B3309221
theorem B2792161 : Blo 2205435 2792161 := bbase (se 2 (by rfl) ⟨1047060, by rfl⟩ : syracuseStep 2792161 = 2094121) (by norm_num)
theorem B3722881 : Blo 2205435 3722881 := bstep (se 2 (by rfl) ⟨1396080, by rfl⟩ : syracuseStep 3722881 = 2792161) B2792161
theorem B4963841 : Blo 2205435 4963841 := bstep (se 2 (by rfl) ⟨1861440, by rfl⟩ : syracuseStep 4963841 = 3722881) B3722881
theorem B3309227 : Blo 2205435 3309227 := bstep (se 1 (by rfl) ⟨2481920, by rfl⟩ : syracuseStep 3309227 = 4963841) B4963841
theorem B2206151 : Blo 2205435 2206151 := bstep (se 1 (by rfl) ⟨1654613, by rfl⟩ : syracuseStep 2206151 = 3309227) B3309227
theorem B2481925 : Blo 2205435 2481925 := bbase (se 4 (by rfl) ⟨232680, by rfl⟩ : syracuseStep 2481925 = 465361) (by norm_num)
theorem B3309233 : Blo 2205435 3309233 := bstep (se 2 (by rfl) ⟨1240962, by rfl⟩ : syracuseStep 3309233 = 2481925) B2481925
theorem B2206155 : Blo 2205435 2206155 := bstep (se 1 (by rfl) ⟨1654616, by rfl⟩ : syracuseStep 2206155 = 3309233) B3309233
theorem B5300765 : Blo 2205435 5300765 := bbase (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) (by norm_num)
theorem B3533843 : Blo 2205435 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B2355895 : Blo 2205435 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B3141193 : Blo 2205435 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B4188257 : Blo 2205435 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B2792171 : Blo 2205435 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B7445789 : Blo 2205435 7445789 := bstep (se 3 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 7445789 = 2792171) B2792171
theorem B4963859 : Blo 2205435 4963859 := bstep (se 1 (by rfl) ⟨3722894, by rfl⟩ : syracuseStep 4963859 = 7445789) B7445789
theorem B3309239 : Blo 2205435 3309239 := bstep (se 1 (by rfl) ⟨2481929, by rfl⟩ : syracuseStep 3309239 = 4963859) B4963859
theorem B2206159 : Blo 2205435 2206159 := bstep (se 1 (by rfl) ⟨1654619, by rfl⟩ : syracuseStep 2206159 = 3309239) B3309239
theorem B3309245 : Blo 2205435 3309245 := bbase (se 3 (by rfl) ⟨620483, by rfl⟩ : syracuseStep 3309245 = 1240967) (by norm_num)
theorem B2206163 : Blo 2205435 2206163 := bstep (se 1 (by rfl) ⟨1654622, by rfl⟩ : syracuseStep 2206163 = 3309245) B3309245
theorem B4963877 : Blo 2205435 4963877 := bbase (se 4 (by rfl) ⟨465363, by rfl⟩ : syracuseStep 4963877 = 930727) (by norm_num)
theorem B3309251 : Blo 2205435 3309251 := bstep (se 1 (by rfl) ⟨2481938, by rfl⟩ : syracuseStep 3309251 = 4963877) B4963877
theorem B2206167 : Blo 2205435 2206167 := bstep (se 1 (by rfl) ⟨1654625, by rfl⟩ : syracuseStep 2206167 = 3309251) B3309251
theorem B5584373 : Blo 2205435 5584373 := bbase (se 5 (by rfl) ⟨261767, by rfl⟩ : syracuseStep 5584373 = 523535) (by norm_num)
theorem B3722915 : Blo 2205435 3722915 := bstep (se 1 (by rfl) ⟨2792186, by rfl⟩ : syracuseStep 3722915 = 5584373) B5584373
theorem B2481943 : Blo 2205435 2481943 := bstep (se 1 (by rfl) ⟨1861457, by rfl⟩ : syracuseStep 2481943 = 3722915) B3722915
theorem B3309257 : Blo 2205435 3309257 := bstep (se 2 (by rfl) ⟨1240971, by rfl⟩ : syracuseStep 3309257 = 2481943) B2481943
theorem B2206171 : Blo 2205435 2206171 := bstep (se 1 (by rfl) ⟨1654628, by rfl⟩ : syracuseStep 2206171 = 3309257) B3309257
theorem B19104437 : Blo 2205435 19104437 := bbase (se 5 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 19104437 = 1791041) (by norm_num)
theorem B12736291 : Blo 2205435 12736291 := bstep (se 1 (by rfl) ⟨9552218, by rfl⟩ : syracuseStep 12736291 = 19104437) B19104437
theorem B16981721 : Blo 2205435 16981721 := bstep (se 2 (by rfl) ⟨6368145, by rfl⟩ : syracuseStep 16981721 = 12736291) B12736291
theorem B11321147 : Blo 2205435 11321147 := bstep (se 1 (by rfl) ⟨8490860, by rfl⟩ : syracuseStep 11321147 = 16981721) B16981721
theorem B30189725 : Blo 2205435 30189725 := bstep (se 3 (by rfl) ⟨5660573, by rfl⟩ : syracuseStep 30189725 = 11321147) B11321147
theorem B20126483 : Blo 2205435 20126483 := bstep (se 1 (by rfl) ⟨15094862, by rfl⟩ : syracuseStep 20126483 = 30189725) B30189725
theorem B13417655 : Blo 2205435 13417655 := bstep (se 1 (by rfl) ⟨10063241, by rfl⟩ : syracuseStep 13417655 = 20126483) B20126483
theorem B35780413 : Blo 2205435 35780413 := bstep (se 3 (by rfl) ⟨6708827, by rfl⟩ : syracuseStep 35780413 = 13417655) B13417655
theorem B47707217 : Blo 2205435 47707217 := bstep (se 2 (by rfl) ⟨17890206, by rfl⟩ : syracuseStep 47707217 = 35780413) B35780413
theorem B31804811 : Blo 2205435 31804811 := bstep (se 1 (by rfl) ⟨23853608, by rfl⟩ : syracuseStep 31804811 = 47707217) B47707217
theorem B21203207 : Blo 2205435 21203207 := bstep (se 1 (by rfl) ⟨15902405, by rfl⟩ : syracuseStep 21203207 = 31804811) B31804811
theorem B14135471 : Blo 2205435 14135471 := bstep (se 1 (by rfl) ⟨10601603, by rfl⟩ : syracuseStep 14135471 = 21203207) B21203207
theorem B9423647 : Blo 2205435 9423647 := bstep (se 1 (by rfl) ⟨7067735, by rfl⟩ : syracuseStep 9423647 = 14135471) B14135471
theorem B6282431 : Blo 2205435 6282431 := bstep (se 1 (by rfl) ⟨4711823, by rfl⟩ : syracuseStep 6282431 = 9423647) B9423647
theorem B4188287 : Blo 2205435 4188287 := bstep (se 1 (by rfl) ⟨3141215, by rfl⟩ : syracuseStep 4188287 = 6282431) B6282431
theorem B11168765 : Blo 2205435 11168765 := bstep (se 3 (by rfl) ⟨2094143, by rfl⟩ : syracuseStep 11168765 = 4188287) B4188287
theorem B7445843 : Blo 2205435 7445843 := bstep (se 1 (by rfl) ⟨5584382, by rfl⟩ : syracuseStep 7445843 = 11168765) B11168765
theorem B4963895 : Blo 2205435 4963895 := bstep (se 1 (by rfl) ⟨3722921, by rfl⟩ : syracuseStep 4963895 = 7445843) B7445843
theorem B3309263 : Blo 2205435 3309263 := bstep (se 1 (by rfl) ⟨2481947, by rfl⟩ : syracuseStep 3309263 = 4963895) B4963895
theorem B2206175 : Blo 2205435 2206175 := bstep (se 1 (by rfl) ⟨1654631, by rfl⟩ : syracuseStep 2206175 = 3309263) B3309263
theorem B3309269 : Blo 2205435 3309269 := bbase (se 7 (by rfl) ⟨38780, by rfl⟩ : syracuseStep 3309269 = 77561) (by norm_num)
theorem B2206179 : Blo 2205435 2206179 := bstep (se 1 (by rfl) ⟨1654634, by rfl⟩ : syracuseStep 2206179 = 3309269) B3309269
theorem B2236285 : Blo 2205435 2236285 := bbase (se 3 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 2236285 = 838607) (by norm_num)
theorem B2981713 : Blo 2205435 2981713 := bstep (se 2 (by rfl) ⟨1118142, by rfl⟩ : syracuseStep 2981713 = 2236285) B2236285
theorem B3975617 : Blo 2205435 3975617 := bstep (se 2 (by rfl) ⟨1490856, by rfl⟩ : syracuseStep 3975617 = 2981713) B2981713
theorem B2650411 : Blo 2205435 2650411 := bstep (se 1 (by rfl) ⟨1987808, by rfl⟩ : syracuseStep 2650411 = 3975617) B3975617
theorem B3533881 : Blo 2205435 3533881 := bstep (se 2 (by rfl) ⟨1325205, by rfl⟩ : syracuseStep 3533881 = 2650411) B2650411
theorem B4711841 : Blo 2205435 4711841 := bstep (se 2 (by rfl) ⟨1766940, by rfl⟩ : syracuseStep 4711841 = 3533881) B3533881
theorem B3141227 : Blo 2205435 3141227 := bstep (se 1 (by rfl) ⟨2355920, by rfl⟩ : syracuseStep 3141227 = 4711841) B4711841
theorem B8376605 : Blo 2205435 8376605 := bstep (se 3 (by rfl) ⟨1570613, by rfl⟩ : syracuseStep 8376605 = 3141227) B3141227
theorem B5584403 : Blo 2205435 5584403 := bstep (se 1 (by rfl) ⟨4188302, by rfl⟩ : syracuseStep 5584403 = 8376605) B8376605
theorem B3722935 : Blo 2205435 3722935 := bstep (se 1 (by rfl) ⟨2792201, by rfl⟩ : syracuseStep 3722935 = 5584403) B5584403
theorem B4963913 : Blo 2205435 4963913 := bstep (se 2 (by rfl) ⟨1861467, by rfl⟩ : syracuseStep 4963913 = 3722935) B3722935
theorem B3309275 : Blo 2205435 3309275 := bstep (se 1 (by rfl) ⟨2481956, by rfl⟩ : syracuseStep 3309275 = 4963913) B4963913
theorem B2206183 : Blo 2205435 2206183 := bstep (se 1 (by rfl) ⟨1654637, by rfl⟩ : syracuseStep 2206183 = 3309275) B3309275
theorem B2481961 : Blo 2205435 2481961 := bbase (se 2 (by rfl) ⟨930735, by rfl⟩ : syracuseStep 2481961 = 1861471) (by norm_num)
theorem B3309281 : Blo 2205435 3309281 := bstep (se 2 (by rfl) ⟨1240980, by rfl⟩ : syracuseStep 3309281 = 2481961) B2481961
theorem B2206187 : Blo 2205435 2206187 := bstep (se 1 (by rfl) ⟨1654640, by rfl⟩ : syracuseStep 2206187 = 3309281) B3309281
theorem B14135573 : Blo 2205435 14135573 := bbase (se 6 (by rfl) ⟨331302, by rfl⟩ : syracuseStep 14135573 = 662605) (by norm_num)
theorem B9423715 : Blo 2205435 9423715 := bstep (se 1 (by rfl) ⟨7067786, by rfl⟩ : syracuseStep 9423715 = 14135573) B14135573
theorem B12564953 : Blo 2205435 12564953 := bstep (se 2 (by rfl) ⟨4711857, by rfl⟩ : syracuseStep 12564953 = 9423715) B9423715
theorem B8376635 : Blo 2205435 8376635 := bstep (se 1 (by rfl) ⟨6282476, by rfl⟩ : syracuseStep 8376635 = 12564953) B12564953
theorem B5584423 : Blo 2205435 5584423 := bstep (se 1 (by rfl) ⟨4188317, by rfl⟩ : syracuseStep 5584423 = 8376635) B8376635
theorem B7445897 : Blo 2205435 7445897 := bstep (se 2 (by rfl) ⟨2792211, by rfl⟩ : syracuseStep 7445897 = 5584423) B5584423
theorem B4963931 : Blo 2205435 4963931 := bstep (se 1 (by rfl) ⟨3722948, by rfl⟩ : syracuseStep 4963931 = 7445897) B7445897
theorem B3309287 : Blo 2205435 3309287 := bstep (se 1 (by rfl) ⟨2481965, by rfl⟩ : syracuseStep 3309287 = 4963931) B4963931
theorem B2206191 : Blo 2205435 2206191 := bstep (se 1 (by rfl) ⟨1654643, by rfl⟩ : syracuseStep 2206191 = 3309287) B3309287
theorem B3309293 : Blo 2205435 3309293 := bbase (se 3 (by rfl) ⟨620492, by rfl⟩ : syracuseStep 3309293 = 1240985) (by norm_num)
theorem B2206195 : Blo 2205435 2206195 := bstep (se 1 (by rfl) ⟨1654646, by rfl⟩ : syracuseStep 2206195 = 3309293) B3309293
theorem B4963949 : Blo 2205435 4963949 := bbase (se 3 (by rfl) ⟨930740, by rfl⟩ : syracuseStep 4963949 = 1861481) (by norm_num)
theorem B3309299 : Blo 2205435 3309299 := bstep (se 1 (by rfl) ⟨2481974, by rfl⟩ : syracuseStep 3309299 = 4963949) B4963949
theorem B2206199 : Blo 2205435 2206199 := bstep (se 1 (by rfl) ⟨1654649, by rfl⟩ : syracuseStep 2206199 = 3309299) B3309299
theorem B4188341 : Blo 2205435 4188341 := bbase (se 5 (by rfl) ⟨196328, by rfl⟩ : syracuseStep 4188341 = 392657) (by norm_num)
theorem B2792227 : Blo 2205435 2792227 := bstep (se 1 (by rfl) ⟨2094170, by rfl⟩ : syracuseStep 2792227 = 4188341) B4188341
theorem B3722969 : Blo 2205435 3722969 := bstep (se 2 (by rfl) ⟨1396113, by rfl⟩ : syracuseStep 3722969 = 2792227) B2792227
theorem B2481979 : Blo 2205435 2481979 := bstep (se 1 (by rfl) ⟨1861484, by rfl⟩ : syracuseStep 2481979 = 3722969) B3722969
theorem B3309305 : Blo 2205435 3309305 := bstep (se 2 (by rfl) ⟨1240989, by rfl⟩ : syracuseStep 3309305 = 2481979) B2481979
theorem B2206203 : Blo 2205435 2206203 := bstep (se 1 (by rfl) ⟨1654652, by rfl⟩ : syracuseStep 2206203 = 3309305) B3309305
theorem B3582133 : Blo 2205435 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B19104709 : Blo 2205435 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B25472945 : Blo 2205435 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B67927853 : Blo 2205435 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B181140941 : Blo 2205435 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B120760627 : Blo 2205435 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B161014169 : Blo 2205435 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B107342779 : Blo 2205435 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B143123705 : Blo 2205435 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B95415803 : Blo 2205435 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B63610535 : Blo 2205435 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B42407023 : Blo 2205435 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B56542697 : Blo 2205435 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B37695131 : Blo 2205435 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B25130087 : Blo 2205435 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B16753391 : Blo 2205435 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B11168927 : Blo 2205435 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B7445951 : Blo 2205435 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B4963967 : Blo 2205435 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B3309311 : Blo 2205435 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B2206207 : Blo 2205435 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B3309317 : Blo 2205435 3309317 := bbase (se 4 (by rfl) ⟨310248, by rfl⟩ : syracuseStep 3309317 = 620497) (by norm_num)
theorem B2206211 : Blo 2205435 2206211 := bstep (se 1 (by rfl) ⟨1654658, by rfl⟩ : syracuseStep 2206211 = 3309317) B3309317
theorem B3722989 : Blo 2205435 3722989 := bbase (se 3 (by rfl) ⟨698060, by rfl⟩ : syracuseStep 3722989 = 1396121) (by norm_num)
theorem B4963985 : Blo 2205435 4963985 := bstep (se 2 (by rfl) ⟨1861494, by rfl⟩ : syracuseStep 4963985 = 3722989) B3722989
theorem B3309323 : Blo 2205435 3309323 := bstep (se 1 (by rfl) ⟨2481992, by rfl⟩ : syracuseStep 3309323 = 4963985) B4963985
theorem B2206215 : Blo 2205435 2206215 := bstep (se 1 (by rfl) ⟨1654661, by rfl⟩ : syracuseStep 2206215 = 3309323) B3309323
theorem B2481997 : Blo 2205435 2481997 := bbase (se 3 (by rfl) ⟨465374, by rfl⟩ : syracuseStep 2481997 = 930749) (by norm_num)
theorem B3309329 : Blo 2205435 3309329 := bstep (se 2 (by rfl) ⟨1240998, by rfl⟩ : syracuseStep 3309329 = 2481997) B2481997
theorem B2206219 : Blo 2205435 2206219 := bstep (se 1 (by rfl) ⟨1654664, by rfl⟩ : syracuseStep 2206219 = 3309329) B3309329
theorem B7446005 : Blo 2205435 7446005 := bbase (se 5 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 7446005 = 698063) (by norm_num)
theorem B4964003 : Blo 2205435 4964003 := bstep (se 1 (by rfl) ⟨3723002, by rfl⟩ : syracuseStep 4964003 = 7446005) B7446005
theorem B3309335 : Blo 2205435 3309335 := bstep (se 1 (by rfl) ⟨2482001, by rfl⟩ : syracuseStep 3309335 = 4964003) B4964003
theorem B2206223 : Blo 2205435 2206223 := bstep (se 1 (by rfl) ⟨1654667, by rfl⟩ : syracuseStep 2206223 = 3309335) B3309335
theorem B3309341 : Blo 2205435 3309341 := bbase (se 3 (by rfl) ⟨620501, by rfl⟩ : syracuseStep 3309341 = 1241003) (by norm_num)
theorem B2206227 : Blo 2205435 2206227 := bstep (se 1 (by rfl) ⟨1654670, by rfl⟩ : syracuseStep 2206227 = 3309341) B3309341
theorem B4964021 : Blo 2205435 4964021 := bbase (se 5 (by rfl) ⟨232688, by rfl⟩ : syracuseStep 4964021 = 465377) (by norm_num)
theorem B3309347 : Blo 2205435 3309347 := bstep (se 1 (by rfl) ⟨2482010, by rfl⟩ : syracuseStep 3309347 = 4964021) B4964021
theorem B2206231 : Blo 2205435 2206231 := bstep (se 1 (by rfl) ⟨1654673, by rfl⟩ : syracuseStep 2206231 = 3309347) B3309347
theorem B12565205 : Blo 2205435 12565205 := bbase (se 7 (by rfl) ⟨147248, by rfl⟩ : syracuseStep 12565205 = 294497) (by norm_num)
theorem B8376803 : Blo 2205435 8376803 := bstep (se 1 (by rfl) ⟨6282602, by rfl⟩ : syracuseStep 8376803 = 12565205) B12565205
theorem B5584535 : Blo 2205435 5584535 := bstep (se 1 (by rfl) ⟨4188401, by rfl⟩ : syracuseStep 5584535 = 8376803) B8376803
theorem B3723023 : Blo 2205435 3723023 := bstep (se 1 (by rfl) ⟨2792267, by rfl⟩ : syracuseStep 3723023 = 5584535) B5584535
theorem B2482015 : Blo 2205435 2482015 := bstep (se 1 (by rfl) ⟨1861511, by rfl⟩ : syracuseStep 2482015 = 3723023) B3723023
theorem B3309353 : Blo 2205435 3309353 := bstep (se 2 (by rfl) ⟨1241007, by rfl⟩ : syracuseStep 3309353 = 2482015) B2482015
theorem B2206235 : Blo 2205435 2206235 := bstep (se 1 (by rfl) ⟨1654676, by rfl⟩ : syracuseStep 2206235 = 3309353) B3309353
theorem B6282613 : Blo 2205435 6282613 := bbase (se 5 (by rfl) ⟨294497, by rfl⟩ : syracuseStep 6282613 = 588995) (by norm_num)
theorem B8376817 : Blo 2205435 8376817 := bstep (se 2 (by rfl) ⟨3141306, by rfl⟩ : syracuseStep 8376817 = 6282613) B6282613
theorem B11169089 : Blo 2205435 11169089 := bstep (se 2 (by rfl) ⟨4188408, by rfl⟩ : syracuseStep 11169089 = 8376817) B8376817
theorem B7446059 : Blo 2205435 7446059 := bstep (se 1 (by rfl) ⟨5584544, by rfl⟩ : syracuseStep 7446059 = 11169089) B11169089
theorem B4964039 : Blo 2205435 4964039 := bstep (se 1 (by rfl) ⟨3723029, by rfl⟩ : syracuseStep 4964039 = 7446059) B7446059
theorem B3309359 : Blo 2205435 3309359 := bstep (se 1 (by rfl) ⟨2482019, by rfl⟩ : syracuseStep 3309359 = 4964039) B4964039
theorem B2206239 : Blo 2205435 2206239 := bstep (se 1 (by rfl) ⟨1654679, by rfl⟩ : syracuseStep 2206239 = 3309359) B3309359
theorem B3309365 : Blo 2205435 3309365 := bbase (se 5 (by rfl) ⟨155126, by rfl⟩ : syracuseStep 3309365 = 310253) (by norm_num)
theorem B2206243 : Blo 2205435 2206243 := bstep (se 1 (by rfl) ⟨1654682, by rfl⟩ : syracuseStep 2206243 = 3309365) B3309365
theorem B5584565 : Blo 2205435 5584565 := bbase (se 5 (by rfl) ⟨261776, by rfl⟩ : syracuseStep 5584565 = 523553) (by norm_num)
theorem B3723043 : Blo 2205435 3723043 := bstep (se 1 (by rfl) ⟨2792282, by rfl⟩ : syracuseStep 3723043 = 5584565) B5584565
theorem B4964057 : Blo 2205435 4964057 := bstep (se 2 (by rfl) ⟨1861521, by rfl⟩ : syracuseStep 4964057 = 3723043) B3723043
theorem B3309371 : Blo 2205435 3309371 := bstep (se 1 (by rfl) ⟨2482028, by rfl⟩ : syracuseStep 3309371 = 4964057) B4964057
theorem B2206247 : Blo 2205435 2206247 := bstep (se 1 (by rfl) ⟨1654685, by rfl⟩ : syracuseStep 2206247 = 3309371) B3309371
theorem B2482033 : Blo 2205435 2482033 := bbase (se 2 (by rfl) ⟨930762, by rfl⟩ : syracuseStep 2482033 = 1861525) (by norm_num)
theorem B3309377 : Blo 2205435 3309377 := bstep (se 2 (by rfl) ⟨1241016, by rfl⟩ : syracuseStep 3309377 = 2482033) B2482033
theorem B2206251 : Blo 2205435 2206251 := bstep (se 1 (by rfl) ⟨1654688, by rfl⟩ : syracuseStep 2206251 = 3309377) B3309377
theorem B9423989 : Blo 2205435 9423989 := bbase (se 5 (by rfl) ⟨441749, by rfl⟩ : syracuseStep 9423989 = 883499) (by norm_num)
theorem B6282659 : Blo 2205435 6282659 := bstep (se 1 (by rfl) ⟨4711994, by rfl⟩ : syracuseStep 6282659 = 9423989) B9423989
theorem B4188439 : Blo 2205435 4188439 := bstep (se 1 (by rfl) ⟨3141329, by rfl⟩ : syracuseStep 4188439 = 6282659) B6282659
theorem B5584585 : Blo 2205435 5584585 := bstep (se 2 (by rfl) ⟨2094219, by rfl⟩ : syracuseStep 5584585 = 4188439) B4188439
theorem B7446113 : Blo 2205435 7446113 := bstep (se 2 (by rfl) ⟨2792292, by rfl⟩ : syracuseStep 7446113 = 5584585) B5584585
theorem B4964075 : Blo 2205435 4964075 := bstep (se 1 (by rfl) ⟨3723056, by rfl⟩ : syracuseStep 4964075 = 7446113) B7446113
theorem B3309383 : Blo 2205435 3309383 := bstep (se 1 (by rfl) ⟨2482037, by rfl⟩ : syracuseStep 3309383 = 4964075) B4964075
theorem B2206255 : Blo 2205435 2206255 := bstep (se 1 (by rfl) ⟨1654691, by rfl⟩ : syracuseStep 2206255 = 3309383) B3309383
theorem B3309389 : Blo 2205435 3309389 := bbase (se 3 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 3309389 = 1241021) (by norm_num)
theorem B2206259 : Blo 2205435 2206259 := bstep (se 1 (by rfl) ⟨1654694, by rfl⟩ : syracuseStep 2206259 = 3309389) B3309389
theorem B4964093 : Blo 2205435 4964093 := bbase (se 3 (by rfl) ⟨930767, by rfl⟩ : syracuseStep 4964093 = 1861535) (by norm_num)
theorem B3309395 : Blo 2205435 3309395 := bstep (se 1 (by rfl) ⟨2482046, by rfl⟩ : syracuseStep 3309395 = 4964093) B4964093
theorem B2206263 : Blo 2205435 2206263 := bstep (se 1 (by rfl) ⟨1654697, by rfl⟩ : syracuseStep 2206263 = 3309395) B3309395
theorem B3723077 : Blo 2205435 3723077 := bbase (se 4 (by rfl) ⟨349038, by rfl⟩ : syracuseStep 3723077 = 698077) (by norm_num)
theorem B2482051 : Blo 2205435 2482051 := bstep (se 1 (by rfl) ⟨1861538, by rfl⟩ : syracuseStep 2482051 = 3723077) B3723077
theorem B3309401 : Blo 2205435 3309401 := bstep (se 2 (by rfl) ⟨1241025, by rfl⟩ : syracuseStep 3309401 = 2482051) B2482051
theorem B2206267 : Blo 2205435 2206267 := bstep (se 1 (by rfl) ⟨1654700, by rfl⟩ : syracuseStep 2206267 = 3309401) B3309401
theorem B16753877 : Blo 2205435 16753877 := bbase (se 7 (by rfl) ⟨196334, by rfl⟩ : syracuseStep 16753877 = 392669) (by norm_num)
theorem B11169251 : Blo 2205435 11169251 := bstep (se 1 (by rfl) ⟨8376938, by rfl⟩ : syracuseStep 11169251 = 16753877) B16753877
theorem B7446167 : Blo 2205435 7446167 := bstep (se 1 (by rfl) ⟨5584625, by rfl⟩ : syracuseStep 7446167 = 11169251) B11169251
theorem B4964111 : Blo 2205435 4964111 := bstep (se 1 (by rfl) ⟨3723083, by rfl⟩ : syracuseStep 4964111 = 7446167) B7446167
theorem B3309407 : Blo 2205435 3309407 := bstep (se 1 (by rfl) ⟨2482055, by rfl⟩ : syracuseStep 3309407 = 4964111) B4964111
theorem B2206271 : Blo 2205435 2206271 := bstep (se 1 (by rfl) ⟨1654703, by rfl⟩ : syracuseStep 2206271 = 3309407) B3309407
theorem B3309413 : Blo 2205435 3309413 := bbase (se 4 (by rfl) ⟨310257, by rfl⟩ : syracuseStep 3309413 = 620515) (by norm_num)
theorem B2206275 : Blo 2205435 2206275 := bstep (se 1 (by rfl) ⟨1654706, by rfl⟩ : syracuseStep 2206275 = 3309413) B3309413
theorem B4188485 : Blo 2205435 4188485 := bbase (se 4 (by rfl) ⟨392670, by rfl⟩ : syracuseStep 4188485 = 785341) (by norm_num)
theorem B2792323 : Blo 2205435 2792323 := bstep (se 1 (by rfl) ⟨2094242, by rfl⟩ : syracuseStep 2792323 = 4188485) B4188485
theorem B3723097 : Blo 2205435 3723097 := bstep (se 2 (by rfl) ⟨1396161, by rfl⟩ : syracuseStep 3723097 = 2792323) B2792323
theorem B4964129 : Blo 2205435 4964129 := bstep (se 2 (by rfl) ⟨1861548, by rfl⟩ : syracuseStep 4964129 = 3723097) B3723097
theorem B3309419 : Blo 2205435 3309419 := bstep (se 1 (by rfl) ⟨2482064, by rfl⟩ : syracuseStep 3309419 = 4964129) B4964129
theorem B2206279 : Blo 2205435 2206279 := bstep (se 1 (by rfl) ⟨1654709, by rfl⟩ : syracuseStep 2206279 = 3309419) B3309419
theorem B2482069 : Blo 2205435 2482069 := bbase (se 6 (by rfl) ⟨58173, by rfl⟩ : syracuseStep 2482069 = 116347) (by norm_num)
theorem B3309425 : Blo 2205435 3309425 := bstep (se 2 (by rfl) ⟨1241034, by rfl⟩ : syracuseStep 3309425 = 2482069) B2482069
theorem B2206283 : Blo 2205435 2206283 := bstep (se 1 (by rfl) ⟨1654712, by rfl⟩ : syracuseStep 2206283 = 3309425) B3309425
theorem B2792333 : Blo 2205435 2792333 := bbase (se 3 (by rfl) ⟨523562, by rfl⟩ : syracuseStep 2792333 = 1047125) (by norm_num)
theorem B7446221 : Blo 2205435 7446221 := bstep (se 3 (by rfl) ⟨1396166, by rfl⟩ : syracuseStep 7446221 = 2792333) B2792333
theorem B4964147 : Blo 2205435 4964147 := bstep (se 1 (by rfl) ⟨3723110, by rfl⟩ : syracuseStep 4964147 = 7446221) B7446221
theorem B3309431 : Blo 2205435 3309431 := bstep (se 1 (by rfl) ⟨2482073, by rfl⟩ : syracuseStep 3309431 = 4964147) B4964147
theorem B2206287 : Blo 2205435 2206287 := bstep (se 1 (by rfl) ⟨1654715, by rfl⟩ : syracuseStep 2206287 = 3309431) B3309431
theorem B3309437 : Blo 2205435 3309437 := bbase (se 3 (by rfl) ⟨620519, by rfl⟩ : syracuseStep 3309437 = 1241039) (by norm_num)
theorem B2206291 : Blo 2205435 2206291 := bstep (se 1 (by rfl) ⟨1654718, by rfl⟩ : syracuseStep 2206291 = 3309437) B3309437
theorem B4964165 : Blo 2205435 4964165 := bbase (se 4 (by rfl) ⟨465390, by rfl⟩ : syracuseStep 4964165 = 930781) (by norm_num)
theorem B3309443 : Blo 2205435 3309443 := bstep (se 1 (by rfl) ⟨2482082, by rfl⟩ : syracuseStep 3309443 = 4964165) B4964165
theorem B2206295 : Blo 2205435 2206295 := bstep (se 1 (by rfl) ⟨1654721, by rfl⟩ : syracuseStep 2206295 = 3309443) B3309443
theorem B5301101 : Blo 2205435 5301101 := bbase (se 3 (by rfl) ⟨993956, by rfl⟩ : syracuseStep 5301101 = 1987913) (by norm_num)
theorem B3534067 : Blo 2205435 3534067 := bstep (se 1 (by rfl) ⟨2650550, by rfl⟩ : syracuseStep 3534067 = 5301101) B5301101
theorem B4712089 : Blo 2205435 4712089 := bstep (se 2 (by rfl) ⟨1767033, by rfl⟩ : syracuseStep 4712089 = 3534067) B3534067
theorem B6282785 : Blo 2205435 6282785 := bstep (se 2 (by rfl) ⟨2356044, by rfl⟩ : syracuseStep 6282785 = 4712089) B4712089
theorem B4188523 : Blo 2205435 4188523 := bstep (se 1 (by rfl) ⟨3141392, by rfl⟩ : syracuseStep 4188523 = 6282785) B6282785
theorem B5584697 : Blo 2205435 5584697 := bstep (se 2 (by rfl) ⟨2094261, by rfl⟩ : syracuseStep 5584697 = 4188523) B4188523
theorem B3723131 : Blo 2205435 3723131 := bstep (se 1 (by rfl) ⟨2792348, by rfl⟩ : syracuseStep 3723131 = 5584697) B5584697
theorem B2482087 : Blo 2205435 2482087 := bstep (se 1 (by rfl) ⟨1861565, by rfl⟩ : syracuseStep 2482087 = 3723131) B3723131
theorem B3309449 : Blo 2205435 3309449 := bstep (se 2 (by rfl) ⟨1241043, by rfl⟩ : syracuseStep 3309449 = 2482087) B2482087
theorem B2206299 : Blo 2205435 2206299 := bstep (se 1 (by rfl) ⟨1654724, by rfl⟩ : syracuseStep 2206299 = 3309449) B3309449
theorem B11169413 : Blo 2205435 11169413 := bbase (se 4 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 11169413 = 2094265) (by norm_num)
theorem B7446275 : Blo 2205435 7446275 := bstep (se 1 (by rfl) ⟨5584706, by rfl⟩ : syracuseStep 7446275 = 11169413) B11169413
theorem B4964183 : Blo 2205435 4964183 := bstep (se 1 (by rfl) ⟨3723137, by rfl⟩ : syracuseStep 4964183 = 7446275) B7446275
theorem B3309455 : Blo 2205435 3309455 := bstep (se 1 (by rfl) ⟨2482091, by rfl⟩ : syracuseStep 3309455 = 4964183) B4964183
theorem B2206303 : Blo 2205435 2206303 := bstep (se 1 (by rfl) ⟨1654727, by rfl⟩ : syracuseStep 2206303 = 3309455) B3309455
theorem B3309461 : Blo 2205435 3309461 := bbase (se 6 (by rfl) ⟨77565, by rfl⟩ : syracuseStep 3309461 = 155131) (by norm_num)
theorem B2206307 : Blo 2205435 2206307 := bstep (se 1 (by rfl) ⟨1654730, by rfl⟩ : syracuseStep 2206307 = 3309461) B3309461
theorem B2356057 : Blo 2205435 2356057 := bbase (se 2 (by rfl) ⟨883521, by rfl⟩ : syracuseStep 2356057 = 1767043) (by norm_num)
theorem B12565637 : Blo 2205435 12565637 := bstep (se 4 (by rfl) ⟨1178028, by rfl⟩ : syracuseStep 12565637 = 2356057) B2356057
theorem B8377091 : Blo 2205435 8377091 := bstep (se 1 (by rfl) ⟨6282818, by rfl⟩ : syracuseStep 8377091 = 12565637) B12565637
theorem B5584727 : Blo 2205435 5584727 := bstep (se 1 (by rfl) ⟨4188545, by rfl⟩ : syracuseStep 5584727 = 8377091) B8377091
theorem B3723151 : Blo 2205435 3723151 := bstep (se 1 (by rfl) ⟨2792363, by rfl⟩ : syracuseStep 3723151 = 5584727) B5584727
theorem B4964201 : Blo 2205435 4964201 := bstep (se 2 (by rfl) ⟨1861575, by rfl⟩ : syracuseStep 4964201 = 3723151) B3723151
theorem B3309467 : Blo 2205435 3309467 := bstep (se 1 (by rfl) ⟨2482100, by rfl⟩ : syracuseStep 3309467 = 4964201) B4964201
theorem B2206311 : Blo 2205435 2206311 := bstep (se 1 (by rfl) ⟨1654733, by rfl⟩ : syracuseStep 2206311 = 3309467) B3309467
theorem B2482105 : Blo 2205435 2482105 := bbase (se 2 (by rfl) ⟨930789, by rfl⟩ : syracuseStep 2482105 = 1861579) (by norm_num)
theorem B3309473 : Blo 2205435 3309473 := bstep (se 2 (by rfl) ⟨1241052, by rfl⟩ : syracuseStep 3309473 = 2482105) B2482105
theorem B2206315 : Blo 2205435 2206315 := bstep (se 1 (by rfl) ⟨1654736, by rfl⟩ : syracuseStep 2206315 = 3309473) B3309473
theorem B7068197 : Blo 2205435 7068197 := bbase (se 4 (by rfl) ⟨662643, by rfl⟩ : syracuseStep 7068197 = 1325287) (by norm_num)
theorem B4712131 : Blo 2205435 4712131 := bstep (se 1 (by rfl) ⟨3534098, by rfl⟩ : syracuseStep 4712131 = 7068197) B7068197
theorem B6282841 : Blo 2205435 6282841 := bstep (se 2 (by rfl) ⟨2356065, by rfl⟩ : syracuseStep 6282841 = 4712131) B4712131
theorem B8377121 : Blo 2205435 8377121 := bstep (se 2 (by rfl) ⟨3141420, by rfl⟩ : syracuseStep 8377121 = 6282841) B6282841
theorem B5584747 : Blo 2205435 5584747 := bstep (se 1 (by rfl) ⟨4188560, by rfl⟩ : syracuseStep 5584747 = 8377121) B8377121
theorem B7446329 : Blo 2205435 7446329 := bstep (se 2 (by rfl) ⟨2792373, by rfl⟩ : syracuseStep 7446329 = 5584747) B5584747
theorem B4964219 : Blo 2205435 4964219 := bstep (se 1 (by rfl) ⟨3723164, by rfl⟩ : syracuseStep 4964219 = 7446329) B7446329
theorem B3309479 : Blo 2205435 3309479 := bstep (se 1 (by rfl) ⟨2482109, by rfl⟩ : syracuseStep 3309479 = 4964219) B4964219
theorem B2206319 : Blo 2205435 2206319 := bstep (se 1 (by rfl) ⟨1654739, by rfl⟩ : syracuseStep 2206319 = 3309479) B3309479
theorem B3309485 : Blo 2205435 3309485 := bbase (se 3 (by rfl) ⟨620528, by rfl⟩ : syracuseStep 3309485 = 1241057) (by norm_num)
theorem B2206323 : Blo 2205435 2206323 := bstep (se 1 (by rfl) ⟨1654742, by rfl⟩ : syracuseStep 2206323 = 3309485) B3309485
theorem B4964237 : Blo 2205435 4964237 := bbase (se 3 (by rfl) ⟨930794, by rfl⟩ : syracuseStep 4964237 = 1861589) (by norm_num)
theorem B3309491 : Blo 2205435 3309491 := bstep (se 1 (by rfl) ⟨2482118, by rfl⟩ : syracuseStep 3309491 = 4964237) B4964237
theorem B2206327 : Blo 2205435 2206327 := bstep (se 1 (by rfl) ⟨1654745, by rfl⟩ : syracuseStep 2206327 = 3309491) B3309491
theorem B2792389 : Blo 2205435 2792389 := bbase (se 4 (by rfl) ⟨261786, by rfl⟩ : syracuseStep 2792389 = 523573) (by norm_num)
theorem B3723185 : Blo 2205435 3723185 := bstep (se 2 (by rfl) ⟨1396194, by rfl⟩ : syracuseStep 3723185 = 2792389) B2792389
theorem B2482123 : Blo 2205435 2482123 := bstep (se 1 (by rfl) ⟨1861592, by rfl⟩ : syracuseStep 2482123 = 3723185) B3723185
theorem B3309497 : Blo 2205435 3309497 := bstep (se 2 (by rfl) ⟨1241061, by rfl⟩ : syracuseStep 3309497 = 2482123) B2482123
theorem B2206331 : Blo 2205435 2206331 := bstep (se 1 (by rfl) ⟨1654748, by rfl⟩ : syracuseStep 2206331 = 3309497) B3309497
theorem B2981917 : Blo 2205435 2981917 := bbase (se 3 (by rfl) ⟨559109, by rfl⟩ : syracuseStep 2981917 = 1118219) (by norm_num)
theorem B15903557 : Blo 2205435 15903557 := bstep (se 4 (by rfl) ⟨1490958, by rfl⟩ : syracuseStep 15903557 = 2981917) B2981917
theorem B10602371 : Blo 2205435 10602371 := bstep (se 1 (by rfl) ⟨7951778, by rfl⟩ : syracuseStep 10602371 = 15903557) B15903557
theorem B28272989 : Blo 2205435 28272989 := bstep (se 3 (by rfl) ⟨5301185, by rfl⟩ : syracuseStep 28272989 = 10602371) B10602371
theorem B18848659 : Blo 2205435 18848659 := bstep (se 1 (by rfl) ⟨14136494, by rfl⟩ : syracuseStep 18848659 = 28272989) B28272989
theorem B25131545 : Blo 2205435 25131545 := bstep (se 2 (by rfl) ⟨9424329, by rfl⟩ : syracuseStep 25131545 = 18848659) B18848659
theorem B16754363 : Blo 2205435 16754363 := bstep (se 1 (by rfl) ⟨12565772, by rfl⟩ : syracuseStep 16754363 = 25131545) B25131545
theorem B11169575 : Blo 2205435 11169575 := bstep (se 1 (by rfl) ⟨8377181, by rfl⟩ : syracuseStep 11169575 = 16754363) B16754363
theorem B7446383 : Blo 2205435 7446383 := bstep (se 1 (by rfl) ⟨5584787, by rfl⟩ : syracuseStep 7446383 = 11169575) B11169575
theorem B4964255 : Blo 2205435 4964255 := bstep (se 1 (by rfl) ⟨3723191, by rfl⟩ : syracuseStep 4964255 = 7446383) B7446383
theorem B3309503 : Blo 2205435 3309503 := bstep (se 1 (by rfl) ⟨2482127, by rfl⟩ : syracuseStep 3309503 = 4964255) B4964255
theorem B2206335 : Blo 2205435 2206335 := bstep (se 1 (by rfl) ⟨1654751, by rfl⟩ : syracuseStep 2206335 = 3309503) B3309503
theorem B3309509 : Blo 2205435 3309509 := bbase (se 4 (by rfl) ⟨310266, by rfl⟩ : syracuseStep 3309509 = 620533) (by norm_num)
theorem B2206339 : Blo 2205435 2206339 := bstep (se 1 (by rfl) ⟨1654754, by rfl⟩ : syracuseStep 2206339 = 3309509) B3309509
theorem B3723205 : Blo 2205435 3723205 := bbase (se 4 (by rfl) ⟨349050, by rfl⟩ : syracuseStep 3723205 = 698101) (by norm_num)
theorem B4964273 : Blo 2205435 4964273 := bstep (se 2 (by rfl) ⟨1861602, by rfl⟩ : syracuseStep 4964273 = 3723205) B3723205
theorem B3309515 : Blo 2205435 3309515 := bstep (se 1 (by rfl) ⟨2482136, by rfl⟩ : syracuseStep 3309515 = 4964273) B4964273
theorem B2206343 : Blo 2205435 2206343 := bstep (se 1 (by rfl) ⟨1654757, by rfl⟩ : syracuseStep 2206343 = 3309515) B3309515
theorem B2482141 : Blo 2205435 2482141 := bbase (se 3 (by rfl) ⟨465401, by rfl⟩ : syracuseStep 2482141 = 930803) (by norm_num)
theorem B3309521 : Blo 2205435 3309521 := bstep (se 2 (by rfl) ⟨1241070, by rfl⟩ : syracuseStep 3309521 = 2482141) B2482141
theorem B2206347 : Blo 2205435 2206347 := bstep (se 1 (by rfl) ⟨1654760, by rfl⟩ : syracuseStep 2206347 = 3309521) B3309521
theorem B7446437 : Blo 2205435 7446437 := bbase (se 4 (by rfl) ⟨698103, by rfl⟩ : syracuseStep 7446437 = 1396207) (by norm_num)
theorem B4964291 : Blo 2205435 4964291 := bstep (se 1 (by rfl) ⟨3723218, by rfl⟩ : syracuseStep 4964291 = 7446437) B7446437
theorem B3309527 : Blo 2205435 3309527 := bstep (se 1 (by rfl) ⟨2482145, by rfl⟩ : syracuseStep 3309527 = 4964291) B4964291
theorem B2206351 : Blo 2205435 2206351 := bstep (se 1 (by rfl) ⟨1654763, by rfl⟩ : syracuseStep 2206351 = 3309527) B3309527
theorem B3309533 : Blo 2205435 3309533 := bbase (se 3 (by rfl) ⟨620537, by rfl⟩ : syracuseStep 3309533 = 1241075) (by norm_num)
theorem B2206355 : Blo 2205435 2206355 := bstep (se 1 (by rfl) ⟨1654766, by rfl⟩ : syracuseStep 2206355 = 3309533) B3309533
theorem B4964309 : Blo 2205435 4964309 := bbase (se 7 (by rfl) ⟨58175, by rfl⟩ : syracuseStep 4964309 = 116351) (by norm_num)
theorem B3309539 : Blo 2205435 3309539 := bstep (se 1 (by rfl) ⟨2482154, by rfl⟩ : syracuseStep 3309539 = 4964309) B4964309
theorem B2206359 : Blo 2205435 2206359 := bstep (se 1 (by rfl) ⟨1654769, by rfl⟩ : syracuseStep 2206359 = 3309539) B3309539
theorem B3975941 : Blo 2205435 3975941 := bbase (se 4 (by rfl) ⟨372744, by rfl⟩ : syracuseStep 3975941 = 745489) (by norm_num)
theorem B2650627 : Blo 2205435 2650627 := bstep (se 1 (by rfl) ⟨1987970, by rfl⟩ : syracuseStep 2650627 = 3975941) B3975941
theorem B14136677 : Blo 2205435 14136677 := bstep (se 4 (by rfl) ⟨1325313, by rfl⟩ : syracuseStep 14136677 = 2650627) B2650627
theorem B9424451 : Blo 2205435 9424451 := bstep (se 1 (by rfl) ⟨7068338, by rfl⟩ : syracuseStep 9424451 = 14136677) B14136677
theorem B6282967 : Blo 2205435 6282967 := bstep (se 1 (by rfl) ⟨4712225, by rfl⟩ : syracuseStep 6282967 = 9424451) B9424451
theorem B8377289 : Blo 2205435 8377289 := bstep (se 2 (by rfl) ⟨3141483, by rfl⟩ : syracuseStep 8377289 = 6282967) B6282967
theorem B5584859 : Blo 2205435 5584859 := bstep (se 1 (by rfl) ⟨4188644, by rfl⟩ : syracuseStep 5584859 = 8377289) B8377289
theorem B3723239 : Blo 2205435 3723239 := bstep (se 1 (by rfl) ⟨2792429, by rfl⟩ : syracuseStep 3723239 = 5584859) B5584859
theorem B2482159 : Blo 2205435 2482159 := bstep (se 1 (by rfl) ⟨1861619, by rfl⟩ : syracuseStep 2482159 = 3723239) B3723239
theorem B3309545 : Blo 2205435 3309545 := bstep (se 2 (by rfl) ⟨1241079, by rfl⟩ : syracuseStep 3309545 = 2482159) B2482159
theorem B2206363 : Blo 2205435 2206363 := bstep (se 1 (by rfl) ⟨1654772, by rfl⟩ : syracuseStep 2206363 = 3309545) B3309545
theorem B17891765 : Blo 2205435 17891765 := bbase (se 5 (by rfl) ⟨838676, by rfl⟩ : syracuseStep 17891765 = 1677353) (by norm_num)
theorem B11927843 : Blo 2205435 11927843 := bstep (se 1 (by rfl) ⟨8945882, by rfl⟩ : syracuseStep 11927843 = 17891765) B17891765
theorem B7951895 : Blo 2205435 7951895 := bstep (se 1 (by rfl) ⟨5963921, by rfl⟩ : syracuseStep 7951895 = 11927843) B11927843
theorem B5301263 : Blo 2205435 5301263 := bstep (se 1 (by rfl) ⟨3975947, by rfl⟩ : syracuseStep 5301263 = 7951895) B7951895
theorem B3534175 : Blo 2205435 3534175 := bstep (se 1 (by rfl) ⟨2650631, by rfl⟩ : syracuseStep 3534175 = 5301263) B5301263
theorem B18848933 : Blo 2205435 18848933 := bstep (se 4 (by rfl) ⟨1767087, by rfl⟩ : syracuseStep 18848933 = 3534175) B3534175
theorem B12565955 : Blo 2205435 12565955 := bstep (se 1 (by rfl) ⟨9424466, by rfl⟩ : syracuseStep 12565955 = 18848933) B18848933
theorem B8377303 : Blo 2205435 8377303 := bstep (se 1 (by rfl) ⟨6282977, by rfl⟩ : syracuseStep 8377303 = 12565955) B12565955
theorem B11169737 : Blo 2205435 11169737 := bstep (se 2 (by rfl) ⟨4188651, by rfl⟩ : syracuseStep 11169737 = 8377303) B8377303
theorem B7446491 : Blo 2205435 7446491 := bstep (se 1 (by rfl) ⟨5584868, by rfl⟩ : syracuseStep 7446491 = 11169737) B11169737
theorem B4964327 : Blo 2205435 4964327 := bstep (se 1 (by rfl) ⟨3723245, by rfl⟩ : syracuseStep 4964327 = 7446491) B7446491
theorem B3309551 : Blo 2205435 3309551 := bstep (se 1 (by rfl) ⟨2482163, by rfl⟩ : syracuseStep 3309551 = 4964327) B4964327
theorem B2206367 : Blo 2205435 2206367 := bstep (se 1 (by rfl) ⟨1654775, by rfl⟩ : syracuseStep 2206367 = 3309551) B3309551
theorem B3309557 : Blo 2205435 3309557 := bbase (se 5 (by rfl) ⟨155135, by rfl⟩ : syracuseStep 3309557 = 310271) (by norm_num)
theorem B2206371 : Blo 2205435 2206371 := bstep (se 1 (by rfl) ⟨1654778, by rfl⟩ : syracuseStep 2206371 = 3309557) B3309557
theorem B7951925 : Blo 2205435 7951925 := bbase (se 5 (by rfl) ⟨372746, by rfl⟩ : syracuseStep 7951925 = 745493) (by norm_num)
theorem B5301283 : Blo 2205435 5301283 := bstep (se 1 (by rfl) ⟨3975962, by rfl⟩ : syracuseStep 5301283 = 7951925) B7951925
theorem B7068377 : Blo 2205435 7068377 := bstep (se 2 (by rfl) ⟨2650641, by rfl⟩ : syracuseStep 7068377 = 5301283) B5301283
theorem B4712251 : Blo 2205435 4712251 := bstep (se 1 (by rfl) ⟨3534188, by rfl⟩ : syracuseStep 4712251 = 7068377) B7068377
theorem B6283001 : Blo 2205435 6283001 := bstep (se 2 (by rfl) ⟨2356125, by rfl⟩ : syracuseStep 6283001 = 4712251) B4712251
theorem B4188667 : Blo 2205435 4188667 := bstep (se 1 (by rfl) ⟨3141500, by rfl⟩ : syracuseStep 4188667 = 6283001) B6283001
theorem B5584889 : Blo 2205435 5584889 := bstep (se 2 (by rfl) ⟨2094333, by rfl⟩ : syracuseStep 5584889 = 4188667) B4188667
theorem B3723259 : Blo 2205435 3723259 := bstep (se 1 (by rfl) ⟨2792444, by rfl⟩ : syracuseStep 3723259 = 5584889) B5584889
theorem B4964345 : Blo 2205435 4964345 := bstep (se 2 (by rfl) ⟨1861629, by rfl⟩ : syracuseStep 4964345 = 3723259) B3723259
theorem B3309563 : Blo 2205435 3309563 := bstep (se 1 (by rfl) ⟨2482172, by rfl⟩ : syracuseStep 3309563 = 4964345) B4964345
theorem B2206375 : Blo 2205435 2206375 := bstep (se 1 (by rfl) ⟨1654781, by rfl⟩ : syracuseStep 2206375 = 3309563) B3309563
theorem B2482177 : Blo 2205435 2482177 := bbase (se 2 (by rfl) ⟨930816, by rfl⟩ : syracuseStep 2482177 = 1861633) (by norm_num)
theorem B3309569 : Blo 2205435 3309569 := bstep (se 2 (by rfl) ⟨1241088, by rfl⟩ : syracuseStep 3309569 = 2482177) B2482177
theorem B2206379 : Blo 2205435 2206379 := bstep (se 1 (by rfl) ⟨1654784, by rfl⟩ : syracuseStep 2206379 = 3309569) B3309569
theorem B5584909 : Blo 2205435 5584909 := bbase (se 3 (by rfl) ⟨1047170, by rfl⟩ : syracuseStep 5584909 = 2094341) (by norm_num)
theorem B7446545 : Blo 2205435 7446545 := bstep (se 2 (by rfl) ⟨2792454, by rfl⟩ : syracuseStep 7446545 = 5584909) B5584909
theorem B4964363 : Blo 2205435 4964363 := bstep (se 1 (by rfl) ⟨3723272, by rfl⟩ : syracuseStep 4964363 = 7446545) B7446545
theorem B3309575 : Blo 2205435 3309575 := bstep (se 1 (by rfl) ⟨2482181, by rfl⟩ : syracuseStep 3309575 = 4964363) B4964363
theorem B2206383 : Blo 2205435 2206383 := bstep (se 1 (by rfl) ⟨1654787, by rfl⟩ : syracuseStep 2206383 = 3309575) B3309575
theorem B3309581 : Blo 2205435 3309581 := bbase (se 3 (by rfl) ⟨620546, by rfl⟩ : syracuseStep 3309581 = 1241093) (by norm_num)
theorem B2206387 : Blo 2205435 2206387 := bstep (se 1 (by rfl) ⟨1654790, by rfl⟩ : syracuseStep 2206387 = 3309581) B3309581
theorem B4964381 : Blo 2205435 4964381 := bbase (se 3 (by rfl) ⟨930821, by rfl⟩ : syracuseStep 4964381 = 1861643) (by norm_num)
theorem B3309587 : Blo 2205435 3309587 := bstep (se 1 (by rfl) ⟨2482190, by rfl⟩ : syracuseStep 3309587 = 4964381) B4964381
theorem B2206391 : Blo 2205435 2206391 := bstep (se 1 (by rfl) ⟨1654793, by rfl⟩ : syracuseStep 2206391 = 3309587) B3309587
theorem B3723293 : Blo 2205435 3723293 := bbase (se 3 (by rfl) ⟨698117, by rfl⟩ : syracuseStep 3723293 = 1396235) (by norm_num)
theorem B2482195 : Blo 2205435 2482195 := bstep (se 1 (by rfl) ⟨1861646, by rfl⟩ : syracuseStep 2482195 = 3723293) B3723293
theorem B3309593 : Blo 2205435 3309593 := bstep (se 2 (by rfl) ⟨1241097, by rfl⟩ : syracuseStep 3309593 = 2482195) B2482195
theorem B2206395 : Blo 2205435 2206395 := bstep (se 1 (by rfl) ⟨1654796, by rfl⟩ : syracuseStep 2206395 = 3309593) B3309593
theorem B16983445 : Blo 2205435 16983445 := bbase (se 6 (by rfl) ⟨398049, by rfl⟩ : syracuseStep 16983445 = 796099) (by norm_num)
theorem B22644593 : Blo 2205435 22644593 := bstep (se 2 (by rfl) ⟨8491722, by rfl⟩ : syracuseStep 22644593 = 16983445) B16983445
theorem B15096395 : Blo 2205435 15096395 := bstep (se 1 (by rfl) ⟨11322296, by rfl⟩ : syracuseStep 15096395 = 22644593) B22644593
theorem B10064263 : Blo 2205435 10064263 := bstep (se 1 (by rfl) ⟨7548197, by rfl⟩ : syracuseStep 10064263 = 15096395) B15096395
theorem B13419017 : Blo 2205435 13419017 := bstep (se 2 (by rfl) ⟨5032131, by rfl⟩ : syracuseStep 13419017 = 10064263) B10064263
theorem B8946011 : Blo 2205435 8946011 := bstep (se 1 (by rfl) ⟨6709508, by rfl⟩ : syracuseStep 8946011 = 13419017) B13419017
theorem B23856029 : Blo 2205435 23856029 := bstep (se 3 (by rfl) ⟨4473005, by rfl⟩ : syracuseStep 23856029 = 8946011) B8946011
theorem B15904019 : Blo 2205435 15904019 := bstep (se 1 (by rfl) ⟨11928014, by rfl⟩ : syracuseStep 15904019 = 23856029) B23856029
theorem B10602679 : Blo 2205435 10602679 := bstep (se 1 (by rfl) ⟨7952009, by rfl⟩ : syracuseStep 10602679 = 15904019) B15904019
theorem B14136905 : Blo 2205435 14136905 := bstep (se 2 (by rfl) ⟨5301339, by rfl⟩ : syracuseStep 14136905 = 10602679) B10602679
theorem B9424603 : Blo 2205435 9424603 := bstep (se 1 (by rfl) ⟨7068452, by rfl⟩ : syracuseStep 9424603 = 14136905) B14136905
theorem B12566137 : Blo 2205435 12566137 := bstep (se 2 (by rfl) ⟨4712301, by rfl⟩ : syracuseStep 12566137 = 9424603) B9424603
theorem B16754849 : Blo 2205435 16754849 := bstep (se 2 (by rfl) ⟨6283068, by rfl⟩ : syracuseStep 16754849 = 12566137) B12566137
theorem B11169899 : Blo 2205435 11169899 := bstep (se 1 (by rfl) ⟨8377424, by rfl⟩ : syracuseStep 11169899 = 16754849) B16754849
theorem B7446599 : Blo 2205435 7446599 := bstep (se 1 (by rfl) ⟨5584949, by rfl⟩ : syracuseStep 7446599 = 11169899) B11169899
theorem B4964399 : Blo 2205435 4964399 := bstep (se 1 (by rfl) ⟨3723299, by rfl⟩ : syracuseStep 4964399 = 7446599) B7446599
theorem B3309599 : Blo 2205435 3309599 := bstep (se 1 (by rfl) ⟨2482199, by rfl⟩ : syracuseStep 3309599 = 4964399) B4964399
theorem B2206399 : Blo 2205435 2206399 := bstep (se 1 (by rfl) ⟨1654799, by rfl⟩ : syracuseStep 2206399 = 3309599) B3309599
theorem B3309605 : Blo 2205435 3309605 := bbase (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) (by norm_num)
theorem B2206403 : Blo 2205435 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B2792485 : Blo 2205435 2792485 := bbase (se 4 (by rfl) ⟨261795, by rfl⟩ : syracuseStep 2792485 = 523591) (by norm_num)
theorem B3723313 : Blo 2205435 3723313 := bstep (se 2 (by rfl) ⟨1396242, by rfl⟩ : syracuseStep 3723313 = 2792485) B2792485
theorem B4964417 : Blo 2205435 4964417 := bstep (se 2 (by rfl) ⟨1861656, by rfl⟩ : syracuseStep 4964417 = 3723313) B3723313
theorem B3309611 : Blo 2205435 3309611 := bstep (se 1 (by rfl) ⟨2482208, by rfl⟩ : syracuseStep 3309611 = 4964417) B4964417
theorem B2206407 : Blo 2205435 2206407 := bstep (se 1 (by rfl) ⟨1654805, by rfl⟩ : syracuseStep 2206407 = 3309611) B3309611
theorem B2482213 : Blo 2205435 2482213 := bbase (se 4 (by rfl) ⟨232707, by rfl⟩ : syracuseStep 2482213 = 465415) (by norm_num)
theorem B3309617 : Blo 2205435 3309617 := bstep (se 2 (by rfl) ⟨1241106, by rfl⟩ : syracuseStep 3309617 = 2482213) B2482213
theorem B2206411 : Blo 2205435 2206411 := bstep (se 1 (by rfl) ⟨1654808, by rfl⟩ : syracuseStep 2206411 = 3309617) B3309617
theorem B7952069 : Blo 2205435 7952069 := bbase (se 4 (by rfl) ⟨745506, by rfl⟩ : syracuseStep 7952069 = 1491013) (by norm_num)
theorem B5301379 : Blo 2205435 5301379 := bstep (se 1 (by rfl) ⟨3976034, by rfl⟩ : syracuseStep 5301379 = 7952069) B7952069
theorem B7068505 : Blo 2205435 7068505 := bstep (se 2 (by rfl) ⟨2650689, by rfl⟩ : syracuseStep 7068505 = 5301379) B5301379
theorem B9424673 : Blo 2205435 9424673 := bstep (se 2 (by rfl) ⟨3534252, by rfl⟩ : syracuseStep 9424673 = 7068505) B7068505
theorem B6283115 : Blo 2205435 6283115 := bstep (se 1 (by rfl) ⟨4712336, by rfl⟩ : syracuseStep 6283115 = 9424673) B9424673
theorem B4188743 : Blo 2205435 4188743 := bstep (se 1 (by rfl) ⟨3141557, by rfl⟩ : syracuseStep 4188743 = 6283115) B6283115
theorem B2792495 : Blo 2205435 2792495 := bstep (se 1 (by rfl) ⟨2094371, by rfl⟩ : syracuseStep 2792495 = 4188743) B4188743
theorem B7446653 : Blo 2205435 7446653 := bstep (se 3 (by rfl) ⟨1396247, by rfl⟩ : syracuseStep 7446653 = 2792495) B2792495
theorem B4964435 : Blo 2205435 4964435 := bstep (se 1 (by rfl) ⟨3723326, by rfl⟩ : syracuseStep 4964435 = 7446653) B7446653
theorem B3309623 : Blo 2205435 3309623 := bstep (se 1 (by rfl) ⟨2482217, by rfl⟩ : syracuseStep 3309623 = 4964435) B4964435
theorem B2206415 : Blo 2205435 2206415 := bstep (se 1 (by rfl) ⟨1654811, by rfl⟩ : syracuseStep 2206415 = 3309623) B3309623
theorem B3309629 : Blo 2205435 3309629 := bbase (se 3 (by rfl) ⟨620555, by rfl⟩ : syracuseStep 3309629 = 1241111) (by norm_num)
theorem B2206419 : Blo 2205435 2206419 := bstep (se 1 (by rfl) ⟨1654814, by rfl⟩ : syracuseStep 2206419 = 3309629) B3309629
theorem B4964453 : Blo 2205435 4964453 := bbase (se 4 (by rfl) ⟨465417, by rfl⟩ : syracuseStep 4964453 = 930835) (by norm_num)
theorem B3309635 : Blo 2205435 3309635 := bstep (se 1 (by rfl) ⟨2482226, by rfl⟩ : syracuseStep 3309635 = 4964453) B4964453
theorem B2206423 : Blo 2205435 2206423 := bstep (se 1 (by rfl) ⟨1654817, by rfl⟩ : syracuseStep 2206423 = 3309635) B3309635
theorem B5585021 : Blo 2205435 5585021 := bbase (se 3 (by rfl) ⟨1047191, by rfl⟩ : syracuseStep 5585021 = 2094383) (by norm_num)
theorem B3723347 : Blo 2205435 3723347 := bstep (se 1 (by rfl) ⟨2792510, by rfl⟩ : syracuseStep 3723347 = 5585021) B5585021
theorem B2482231 : Blo 2205435 2482231 := bstep (se 1 (by rfl) ⟨1861673, by rfl⟩ : syracuseStep 2482231 = 3723347) B3723347
theorem B3309641 : Blo 2205435 3309641 := bstep (se 2 (by rfl) ⟨1241115, by rfl⟩ : syracuseStep 3309641 = 2482231) B2482231
theorem B2206427 : Blo 2205435 2206427 := bstep (se 1 (by rfl) ⟨1654820, by rfl⟩ : syracuseStep 2206427 = 3309641) B3309641
theorem B4188773 : Blo 2205435 4188773 := bbase (se 4 (by rfl) ⟨392697, by rfl⟩ : syracuseStep 4188773 = 785395) (by norm_num)
theorem B11170061 : Blo 2205435 11170061 := bstep (se 3 (by rfl) ⟨2094386, by rfl⟩ : syracuseStep 11170061 = 4188773) B4188773
theorem B7446707 : Blo 2205435 7446707 := bstep (se 1 (by rfl) ⟨5585030, by rfl⟩ : syracuseStep 7446707 = 11170061) B11170061
theorem B4964471 : Blo 2205435 4964471 := bstep (se 1 (by rfl) ⟨3723353, by rfl⟩ : syracuseStep 4964471 = 7446707) B7446707
theorem B3309647 : Blo 2205435 3309647 := bstep (se 1 (by rfl) ⟨2482235, by rfl⟩ : syracuseStep 3309647 = 4964471) B4964471
theorem B2206431 : Blo 2205435 2206431 := bstep (se 1 (by rfl) ⟨1654823, by rfl⟩ : syracuseStep 2206431 = 3309647) B3309647
theorem B3309653 : Blo 2205435 3309653 := bbase (se 8 (by rfl) ⟨19392, by rfl⟩ : syracuseStep 3309653 = 38785) (by norm_num)
theorem B2206435 : Blo 2205435 2206435 := bstep (se 1 (by rfl) ⟨1654826, by rfl⟩ : syracuseStep 2206435 = 3309653) B3309653
theorem B15904309 : Blo 2205435 15904309 := bbase (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) (by norm_num)
theorem B21205745 : Blo 2205435 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B14137163 : Blo 2205435 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B9424775 : Blo 2205435 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B6283183 : Blo 2205435 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B8377577 : Blo 2205435 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B5585051 : Blo 2205435 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B3723367 : Blo 2205435 3723367 := bstep (se 1 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 3723367 = 5585051) B5585051
theorem B4964489 : Blo 2205435 4964489 := bstep (se 2 (by rfl) ⟨1861683, by rfl⟩ : syracuseStep 4964489 = 3723367) B3723367
theorem B3309659 : Blo 2205435 3309659 := bstep (se 1 (by rfl) ⟨2482244, by rfl⟩ : syracuseStep 3309659 = 4964489) B4964489
theorem B2206439 : Blo 2205435 2206439 := bstep (se 1 (by rfl) ⟨1654829, by rfl⟩ : syracuseStep 2206439 = 3309659) B3309659
theorem B2482249 : Blo 2205435 2482249 := bbase (se 2 (by rfl) ⟨930843, by rfl⟩ : syracuseStep 2482249 = 1861687) (by norm_num)
theorem B3309665 : Blo 2205435 3309665 := bstep (se 2 (by rfl) ⟨1241124, by rfl⟩ : syracuseStep 3309665 = 2482249) B2482249
theorem B2206443 : Blo 2205435 2206443 := bstep (se 1 (by rfl) ⟨1654832, by rfl⟩ : syracuseStep 2206443 = 3309665) B3309665
theorem B15096725 : Blo 2205435 15096725 := bbase (se 6 (by rfl) ⟨353829, by rfl⟩ : syracuseStep 15096725 = 707659) (by norm_num)
theorem B10064483 : Blo 2205435 10064483 := bstep (se 1 (by rfl) ⟨7548362, by rfl⟩ : syracuseStep 10064483 = 15096725) B15096725
theorem B6709655 : Blo 2205435 6709655 := bstep (se 1 (by rfl) ⟨5032241, by rfl⟩ : syracuseStep 6709655 = 10064483) B10064483
theorem B17892413 : Blo 2205435 17892413 := bstep (se 3 (by rfl) ⟨3354827, by rfl⟩ : syracuseStep 17892413 = 6709655) B6709655
theorem B11928275 : Blo 2205435 11928275 := bstep (se 1 (by rfl) ⟨8946206, by rfl⟩ : syracuseStep 11928275 = 17892413) B17892413
theorem B7952183 : Blo 2205435 7952183 := bstep (se 1 (by rfl) ⟨5964137, by rfl⟩ : syracuseStep 7952183 = 11928275) B11928275
theorem B5301455 : Blo 2205435 5301455 := bstep (se 1 (by rfl) ⟨3976091, by rfl⟩ : syracuseStep 5301455 = 7952183) B7952183
theorem B14137213 : Blo 2205435 14137213 := bstep (se 3 (by rfl) ⟨2650727, by rfl⟩ : syracuseStep 14137213 = 5301455) B5301455
theorem B18849617 : Blo 2205435 18849617 := bstep (se 2 (by rfl) ⟨7068606, by rfl⟩ : syracuseStep 18849617 = 14137213) B14137213
theorem B12566411 : Blo 2205435 12566411 := bstep (se 1 (by rfl) ⟨9424808, by rfl⟩ : syracuseStep 12566411 = 18849617) B18849617
theorem B8377607 : Blo 2205435 8377607 := bstep (se 1 (by rfl) ⟨6283205, by rfl⟩ : syracuseStep 8377607 = 12566411) B12566411
theorem B5585071 : Blo 2205435 5585071 := bstep (se 1 (by rfl) ⟨4188803, by rfl⟩ : syracuseStep 5585071 = 8377607) B8377607
theorem B7446761 : Blo 2205435 7446761 := bstep (se 2 (by rfl) ⟨2792535, by rfl⟩ : syracuseStep 7446761 = 5585071) B5585071
theorem B4964507 : Blo 2205435 4964507 := bstep (se 1 (by rfl) ⟨3723380, by rfl⟩ : syracuseStep 4964507 = 7446761) B7446761
theorem B3309671 : Blo 2205435 3309671 := bstep (se 1 (by rfl) ⟨2482253, by rfl⟩ : syracuseStep 3309671 = 4964507) B4964507
theorem B2206447 : Blo 2205435 2206447 := bstep (se 1 (by rfl) ⟨1654835, by rfl⟩ : syracuseStep 2206447 = 3309671) B3309671
theorem B3309677 : Blo 2205435 3309677 := bbase (se 3 (by rfl) ⟨620564, by rfl⟩ : syracuseStep 3309677 = 1241129) (by norm_num)
theorem B2206451 : Blo 2205435 2206451 := bstep (se 1 (by rfl) ⟨1654838, by rfl⟩ : syracuseStep 2206451 = 3309677) B3309677
theorem B4964525 : Blo 2205435 4964525 := bbase (se 3 (by rfl) ⟨930848, by rfl⟩ : syracuseStep 4964525 = 1861697) (by norm_num)
theorem B3309683 : Blo 2205435 3309683 := bstep (se 1 (by rfl) ⟨2482262, by rfl⟩ : syracuseStep 3309683 = 4964525) B4964525
theorem B2206455 : Blo 2205435 2206455 := bstep (se 1 (by rfl) ⟨1654841, by rfl⟩ : syracuseStep 2206455 = 3309683) B3309683
theorem B10747637 : Blo 2205435 10747637 := bbase (se 5 (by rfl) ⟨503795, by rfl⟩ : syracuseStep 10747637 = 1007591) (by norm_num)
theorem B7165091 : Blo 2205435 7165091 := bstep (se 1 (by rfl) ⟨5373818, by rfl⟩ : syracuseStep 7165091 = 10747637) B10747637
theorem B4776727 : Blo 2205435 4776727 := bstep (se 1 (by rfl) ⟨3582545, by rfl⟩ : syracuseStep 4776727 = 7165091) B7165091
theorem B6368969 : Blo 2205435 6368969 := bstep (se 2 (by rfl) ⟨2388363, by rfl⟩ : syracuseStep 6368969 = 4776727) B4776727
theorem B4245979 : Blo 2205435 4245979 := bstep (se 1 (by rfl) ⟨3184484, by rfl⟩ : syracuseStep 4245979 = 6368969) B6368969
theorem B5661305 : Blo 2205435 5661305 := bstep (se 2 (by rfl) ⟨2122989, by rfl⟩ : syracuseStep 5661305 = 4245979) B4245979
theorem B3774203 : Blo 2205435 3774203 := bstep (se 1 (by rfl) ⟨2830652, by rfl⟩ : syracuseStep 3774203 = 5661305) B5661305
theorem B2516135 : Blo 2205435 2516135 := bstep (se 1 (by rfl) ⟨1887101, by rfl⟩ : syracuseStep 2516135 = 3774203) B3774203
theorem B26838773 : Blo 2205435 26838773 := bstep (se 5 (by rfl) ⟨1258067, by rfl⟩ : syracuseStep 26838773 = 2516135) B2516135
theorem B17892515 : Blo 2205435 17892515 := bstep (se 1 (by rfl) ⟨13419386, by rfl⟩ : syracuseStep 17892515 = 26838773) B26838773
theorem B11928343 : Blo 2205435 11928343 := bstep (se 1 (by rfl) ⟨8946257, by rfl⟩ : syracuseStep 11928343 = 17892515) B17892515
theorem B15904457 : Blo 2205435 15904457 := bstep (se 2 (by rfl) ⟨5964171, by rfl⟩ : syracuseStep 15904457 = 11928343) B11928343
theorem B10602971 : Blo 2205435 10602971 := bstep (se 1 (by rfl) ⟨7952228, by rfl⟩ : syracuseStep 10602971 = 15904457) B15904457
theorem B7068647 : Blo 2205435 7068647 := bstep (se 1 (by rfl) ⟨5301485, by rfl⟩ : syracuseStep 7068647 = 10602971) B10602971
theorem B4712431 : Blo 2205435 4712431 := bstep (se 1 (by rfl) ⟨3534323, by rfl⟩ : syracuseStep 4712431 = 7068647) B7068647
theorem B6283241 : Blo 2205435 6283241 := bstep (se 2 (by rfl) ⟨2356215, by rfl⟩ : syracuseStep 6283241 = 4712431) B4712431
theorem B4188827 : Blo 2205435 4188827 := bstep (se 1 (by rfl) ⟨3141620, by rfl⟩ : syracuseStep 4188827 = 6283241) B6283241
theorem B2792551 : Blo 2205435 2792551 := bstep (se 1 (by rfl) ⟨2094413, by rfl⟩ : syracuseStep 2792551 = 4188827) B4188827
theorem B3723401 : Blo 2205435 3723401 := bstep (se 2 (by rfl) ⟨1396275, by rfl⟩ : syracuseStep 3723401 = 2792551) B2792551
theorem B2482267 : Blo 2205435 2482267 := bstep (se 1 (by rfl) ⟨1861700, by rfl⟩ : syracuseStep 2482267 = 3723401) B3723401
theorem B3309689 : Blo 2205435 3309689 := bstep (se 2 (by rfl) ⟨1241133, by rfl⟩ : syracuseStep 3309689 = 2482267) B2482267
theorem B2206459 : Blo 2205435 2206459 := bstep (se 1 (by rfl) ⟨1654844, by rfl⟩ : syracuseStep 2206459 = 3309689) B3309689
theorem B5301493 : Blo 2205435 5301493 := bbase (se 5 (by rfl) ⟨248507, by rfl⟩ : syracuseStep 5301493 = 497015) (by norm_num)
theorem B28274629 : Blo 2205435 28274629 := bstep (se 4 (by rfl) ⟨2650746, by rfl⟩ : syracuseStep 28274629 = 5301493) B5301493
theorem B37699505 : Blo 2205435 37699505 := bstep (se 2 (by rfl) ⟨14137314, by rfl⟩ : syracuseStep 37699505 = 28274629) B28274629
theorem B25133003 : Blo 2205435 25133003 := bstep (se 1 (by rfl) ⟨18849752, by rfl⟩ : syracuseStep 25133003 = 37699505) B37699505
theorem B16755335 : Blo 2205435 16755335 := bstep (se 1 (by rfl) ⟨12566501, by rfl⟩ : syracuseStep 16755335 = 25133003) B25133003
theorem B11170223 : Blo 2205435 11170223 := bstep (se 1 (by rfl) ⟨8377667, by rfl⟩ : syracuseStep 11170223 = 16755335) B16755335
theorem B7446815 : Blo 2205435 7446815 := bstep (se 1 (by rfl) ⟨5585111, by rfl⟩ : syracuseStep 7446815 = 11170223) B11170223
theorem B4964543 : Blo 2205435 4964543 := bstep (se 1 (by rfl) ⟨3723407, by rfl⟩ : syracuseStep 4964543 = 7446815) B7446815
theorem B3309695 : Blo 2205435 3309695 := bstep (se 1 (by rfl) ⟨2482271, by rfl⟩ : syracuseStep 3309695 = 4964543) B4964543
theorem B2206463 : Blo 2205435 2206463 := bstep (se 1 (by rfl) ⟨1654847, by rfl⟩ : syracuseStep 2206463 = 3309695) B3309695
theorem B3309701 : Blo 2205435 3309701 := bbase (se 4 (by rfl) ⟨310284, by rfl⟩ : syracuseStep 3309701 = 620569) (by norm_num)
theorem B2206467 : Blo 2205435 2206467 := bstep (se 1 (by rfl) ⟨1654850, by rfl⟩ : syracuseStep 2206467 = 3309701) B3309701
theorem B3723421 : Blo 2205435 3723421 := bbase (se 3 (by rfl) ⟨698141, by rfl⟩ : syracuseStep 3723421 = 1396283) (by norm_num)
theorem B4964561 : Blo 2205435 4964561 := bstep (se 2 (by rfl) ⟨1861710, by rfl⟩ : syracuseStep 4964561 = 3723421) B3723421
theorem B3309707 : Blo 2205435 3309707 := bstep (se 1 (by rfl) ⟨2482280, by rfl⟩ : syracuseStep 3309707 = 4964561) B4964561
theorem B2206471 : Blo 2205435 2206471 := bstep (se 1 (by rfl) ⟨1654853, by rfl⟩ : syracuseStep 2206471 = 3309707) B3309707
theorem B2482285 : Blo 2205435 2482285 := bbase (se 3 (by rfl) ⟨465428, by rfl⟩ : syracuseStep 2482285 = 930857) (by norm_num)
theorem B3309713 : Blo 2205435 3309713 := bstep (se 2 (by rfl) ⟨1241142, by rfl⟩ : syracuseStep 3309713 = 2482285) B2482285
theorem B2206475 : Blo 2205435 2206475 := bstep (se 1 (by rfl) ⟨1654856, by rfl⟩ : syracuseStep 2206475 = 3309713) B3309713
theorem B7446869 : Blo 2205435 7446869 := bbase (se 10 (by rfl) ⟨10908, by rfl⟩ : syracuseStep 7446869 = 21817) (by norm_num)
theorem B4964579 : Blo 2205435 4964579 := bstep (se 1 (by rfl) ⟨3723434, by rfl⟩ : syracuseStep 4964579 = 7446869) B7446869
theorem B3309719 : Blo 2205435 3309719 := bstep (se 1 (by rfl) ⟨2482289, by rfl⟩ : syracuseStep 3309719 = 4964579) B4964579
theorem B2206479 : Blo 2205435 2206479 := bstep (se 1 (by rfl) ⟨1654859, by rfl⟩ : syracuseStep 2206479 = 3309719) B3309719
theorem B3309725 : Blo 2205435 3309725 := bbase (se 3 (by rfl) ⟨620573, by rfl⟩ : syracuseStep 3309725 = 1241147) (by norm_num)
theorem B2206483 : Blo 2205435 2206483 := bstep (se 1 (by rfl) ⟨1654862, by rfl⟩ : syracuseStep 2206483 = 3309725) B3309725
theorem B4964597 : Blo 2205435 4964597 := bbase (se 5 (by rfl) ⟨232715, by rfl⟩ : syracuseStep 4964597 = 465431) (by norm_num)
theorem B3309731 : Blo 2205435 3309731 := bstep (se 1 (by rfl) ⟨2482298, by rfl⟩ : syracuseStep 3309731 = 4964597) B4964597
theorem B2206487 : Blo 2205435 2206487 := bstep (se 1 (by rfl) ⟨1654865, by rfl⟩ : syracuseStep 2206487 = 3309731) B3309731
theorem B11322773 : Blo 2205435 11322773 := bbase (se 6 (by rfl) ⟨265377, by rfl⟩ : syracuseStep 11322773 = 530755) (by norm_num)
theorem B7548515 : Blo 2205435 7548515 := bstep (se 1 (by rfl) ⟨5661386, by rfl⟩ : syracuseStep 7548515 = 11322773) B11322773
theorem B5032343 : Blo 2205435 5032343 := bstep (se 1 (by rfl) ⟨3774257, by rfl⟩ : syracuseStep 5032343 = 7548515) B7548515
theorem B3354895 : Blo 2205435 3354895 := bstep (se 1 (by rfl) ⟨2516171, by rfl⟩ : syracuseStep 3354895 = 5032343) B5032343
theorem B4473193 : Blo 2205435 4473193 := bstep (se 2 (by rfl) ⟨1677447, by rfl⟩ : syracuseStep 4473193 = 3354895) B3354895
theorem B5964257 : Blo 2205435 5964257 := bstep (se 2 (by rfl) ⟨2236596, by rfl⟩ : syracuseStep 5964257 = 4473193) B4473193
theorem B3976171 : Blo 2205435 3976171 := bstep (se 1 (by rfl) ⟨2982128, by rfl⟩ : syracuseStep 3976171 = 5964257) B5964257
theorem B21206245 : Blo 2205435 21206245 := bstep (se 4 (by rfl) ⟨1988085, by rfl⟩ : syracuseStep 21206245 = 3976171) B3976171
theorem B28274993 : Blo 2205435 28274993 := bstep (se 2 (by rfl) ⟨10603122, by rfl⟩ : syracuseStep 28274993 = 21206245) B21206245
theorem B18849995 : Blo 2205435 18849995 := bstep (se 1 (by rfl) ⟨14137496, by rfl⟩ : syracuseStep 18849995 = 28274993) B28274993
theorem B12566663 : Blo 2205435 12566663 := bstep (se 1 (by rfl) ⟨9424997, by rfl⟩ : syracuseStep 12566663 = 18849995) B18849995
theorem B8377775 : Blo 2205435 8377775 := bstep (se 1 (by rfl) ⟨6283331, by rfl⟩ : syracuseStep 8377775 = 12566663) B12566663
theorem B5585183 : Blo 2205435 5585183 := bstep (se 1 (by rfl) ⟨4188887, by rfl⟩ : syracuseStep 5585183 = 8377775) B8377775
theorem B3723455 : Blo 2205435 3723455 := bstep (se 1 (by rfl) ⟨2792591, by rfl⟩ : syracuseStep 3723455 = 5585183) B5585183
theorem B2482303 : Blo 2205435 2482303 := bstep (se 1 (by rfl) ⟨1861727, by rfl⟩ : syracuseStep 2482303 = 3723455) B3723455
theorem B3309737 : Blo 2205435 3309737 := bstep (se 2 (by rfl) ⟨1241151, by rfl⟩ : syracuseStep 3309737 = 2482303) B2482303
theorem B2206491 : Blo 2205435 2206491 := bstep (se 1 (by rfl) ⟨1654868, by rfl⟩ : syracuseStep 2206491 = 3309737) B3309737
theorem B7952357 : Blo 2205435 7952357 := bbase (se 4 (by rfl) ⟨745533, by rfl⟩ : syracuseStep 7952357 = 1491067) (by norm_num)
theorem B5301571 : Blo 2205435 5301571 := bstep (se 1 (by rfl) ⟨3976178, by rfl⟩ : syracuseStep 5301571 = 7952357) B7952357
theorem B7068761 : Blo 2205435 7068761 := bstep (se 2 (by rfl) ⟨2650785, by rfl⟩ : syracuseStep 7068761 = 5301571) B5301571
theorem B4712507 : Blo 2205435 4712507 := bstep (se 1 (by rfl) ⟨3534380, by rfl⟩ : syracuseStep 4712507 = 7068761) B7068761
theorem B3141671 : Blo 2205435 3141671 := bstep (se 1 (by rfl) ⟨2356253, by rfl⟩ : syracuseStep 3141671 = 4712507) B4712507
theorem B8377789 : Blo 2205435 8377789 := bstep (se 3 (by rfl) ⟨1570835, by rfl⟩ : syracuseStep 8377789 = 3141671) B3141671
theorem B11170385 : Blo 2205435 11170385 := bstep (se 2 (by rfl) ⟨4188894, by rfl⟩ : syracuseStep 11170385 = 8377789) B8377789
theorem B7446923 : Blo 2205435 7446923 := bstep (se 1 (by rfl) ⟨5585192, by rfl⟩ : syracuseStep 7446923 = 11170385) B11170385
theorem B4964615 : Blo 2205435 4964615 := bstep (se 1 (by rfl) ⟨3723461, by rfl⟩ : syracuseStep 4964615 = 7446923) B7446923
theorem B3309743 : Blo 2205435 3309743 := bstep (se 1 (by rfl) ⟨2482307, by rfl⟩ : syracuseStep 3309743 = 4964615) B4964615
theorem B2206495 : Blo 2205435 2206495 := bstep (se 1 (by rfl) ⟨1654871, by rfl⟩ : syracuseStep 2206495 = 3309743) B3309743
theorem B3309749 : Blo 2205435 3309749 := bbase (se 5 (by rfl) ⟨155144, by rfl⟩ : syracuseStep 3309749 = 310289) (by norm_num)
theorem B2206499 : Blo 2205435 2206499 := bstep (se 1 (by rfl) ⟨1654874, by rfl⟩ : syracuseStep 2206499 = 3309749) B3309749
theorem B5585213 : Blo 2205435 5585213 := bbase (se 3 (by rfl) ⟨1047227, by rfl⟩ : syracuseStep 5585213 = 2094455) (by norm_num)
theorem B3723475 : Blo 2205435 3723475 := bstep (se 1 (by rfl) ⟨2792606, by rfl⟩ : syracuseStep 3723475 = 5585213) B5585213
theorem B4964633 : Blo 2205435 4964633 := bstep (se 2 (by rfl) ⟨1861737, by rfl⟩ : syracuseStep 4964633 = 3723475) B3723475
theorem B3309755 : Blo 2205435 3309755 := bstep (se 1 (by rfl) ⟨2482316, by rfl⟩ : syracuseStep 3309755 = 4964633) B4964633
theorem B2206503 : Blo 2205435 2206503 := bstep (se 1 (by rfl) ⟨1654877, by rfl⟩ : syracuseStep 2206503 = 3309755) B3309755
theorem B2482321 : Blo 2205435 2482321 := bbase (se 2 (by rfl) ⟨930870, by rfl⟩ : syracuseStep 2482321 = 1861741) (by norm_num)
theorem B3309761 : Blo 2205435 3309761 := bstep (se 2 (by rfl) ⟨1241160, by rfl⟩ : syracuseStep 3309761 = 2482321) B2482321
theorem B2206507 : Blo 2205435 2206507 := bstep (se 1 (by rfl) ⟨1654880, by rfl⟩ : syracuseStep 2206507 = 3309761) B3309761
theorem B4188925 : Blo 2205435 4188925 := bbase (se 3 (by rfl) ⟨785423, by rfl⟩ : syracuseStep 4188925 = 1570847) (by norm_num)
theorem B5585233 : Blo 2205435 5585233 := bstep (se 2 (by rfl) ⟨2094462, by rfl⟩ : syracuseStep 5585233 = 4188925) B4188925
theorem B7446977 : Blo 2205435 7446977 := bstep (se 2 (by rfl) ⟨2792616, by rfl⟩ : syracuseStep 7446977 = 5585233) B5585233
theorem B4964651 : Blo 2205435 4964651 := bstep (se 1 (by rfl) ⟨3723488, by rfl⟩ : syracuseStep 4964651 = 7446977) B7446977
theorem B3309767 : Blo 2205435 3309767 := bstep (se 1 (by rfl) ⟨2482325, by rfl⟩ : syracuseStep 3309767 = 4964651) B4964651
theorem B2206511 : Blo 2205435 2206511 := bstep (se 1 (by rfl) ⟨1654883, by rfl⟩ : syracuseStep 2206511 = 3309767) B3309767
theorem B3309773 : Blo 2205435 3309773 := bbase (se 3 (by rfl) ⟨620582, by rfl⟩ : syracuseStep 3309773 = 1241165) (by norm_num)
theorem B2206515 : Blo 2205435 2206515 := bstep (se 1 (by rfl) ⟨1654886, by rfl⟩ : syracuseStep 2206515 = 3309773) B3309773
theorem B4964669 : Blo 2205435 4964669 := bbase (se 3 (by rfl) ⟨930875, by rfl⟩ : syracuseStep 4964669 = 1861751) (by norm_num)
theorem B3309779 : Blo 2205435 3309779 := bstep (se 1 (by rfl) ⟨2482334, by rfl⟩ : syracuseStep 3309779 = 4964669) B4964669
theorem B2206519 : Blo 2205435 2206519 := bstep (se 1 (by rfl) ⟨1654889, by rfl⟩ : syracuseStep 2206519 = 3309779) B3309779
theorem B3723509 : Blo 2205435 3723509 := bbase (se 5 (by rfl) ⟨174539, by rfl⟩ : syracuseStep 3723509 = 349079) (by norm_num)
theorem B2482339 : Blo 2205435 2482339 := bstep (se 1 (by rfl) ⟨1861754, by rfl⟩ : syracuseStep 2482339 = 3723509) B3723509
theorem B3309785 : Blo 2205435 3309785 := bstep (se 2 (by rfl) ⟨1241169, by rfl⟩ : syracuseStep 3309785 = 2482339) B2482339
theorem B2206523 : Blo 2205435 2206523 := bstep (se 1 (by rfl) ⟨1654892, by rfl⟩ : syracuseStep 2206523 = 3309785) B3309785
theorem B6801445 : Blo 2205435 6801445 := bbase (se 4 (by rfl) ⟨637635, by rfl⟩ : syracuseStep 6801445 = 1275271) (by norm_num)
theorem B9068593 : Blo 2205435 9068593 := bstep (se 2 (by rfl) ⟨3400722, by rfl⟩ : syracuseStep 9068593 = 6801445) B6801445
theorem B12091457 : Blo 2205435 12091457 := bstep (se 2 (by rfl) ⟨4534296, by rfl⟩ : syracuseStep 12091457 = 9068593) B9068593
theorem B8060971 : Blo 2205435 8060971 := bstep (se 1 (by rfl) ⟨6045728, by rfl⟩ : syracuseStep 8060971 = 12091457) B12091457
theorem B10747961 : Blo 2205435 10747961 := bstep (se 2 (by rfl) ⟨4030485, by rfl⟩ : syracuseStep 10747961 = 8060971) B8060971
theorem B7165307 : Blo 2205435 7165307 := bstep (se 1 (by rfl) ⟨5373980, by rfl⟩ : syracuseStep 7165307 = 10747961) B10747961
theorem B19107485 : Blo 2205435 19107485 := bstep (se 3 (by rfl) ⟨3582653, by rfl⟩ : syracuseStep 19107485 = 7165307) B7165307
theorem B12738323 : Blo 2205435 12738323 := bstep (se 1 (by rfl) ⟨9553742, by rfl⟩ : syracuseStep 12738323 = 19107485) B19107485
theorem B33968861 : Blo 2205435 33968861 := bstep (se 3 (by rfl) ⟨6369161, by rfl⟩ : syracuseStep 33968861 = 12738323) B12738323
theorem B22645907 : Blo 2205435 22645907 := bstep (se 1 (by rfl) ⟨16984430, by rfl⟩ : syracuseStep 22645907 = 33968861) B33968861
theorem B15097271 : Blo 2205435 15097271 := bstep (se 1 (by rfl) ⟨11322953, by rfl⟩ : syracuseStep 15097271 = 22645907) B22645907
theorem B40259389 : Blo 2205435 40259389 := bstep (se 3 (by rfl) ⟨7548635, by rfl⟩ : syracuseStep 40259389 = 15097271) B15097271
theorem B53679185 : Blo 2205435 53679185 := bstep (se 2 (by rfl) ⟨20129694, by rfl⟩ : syracuseStep 53679185 = 40259389) B40259389
theorem B35786123 : Blo 2205435 35786123 := bstep (se 1 (by rfl) ⟨26839592, by rfl⟩ : syracuseStep 35786123 = 53679185) B53679185
theorem B23857415 : Blo 2205435 23857415 := bstep (se 1 (by rfl) ⟨17893061, by rfl⟩ : syracuseStep 23857415 = 35786123) B35786123
theorem B15904943 : Blo 2205435 15904943 := bstep (se 1 (by rfl) ⟨11928707, by rfl⟩ : syracuseStep 15904943 = 23857415) B23857415
theorem B10603295 : Blo 2205435 10603295 := bstep (se 1 (by rfl) ⟨7952471, by rfl⟩ : syracuseStep 10603295 = 15904943) B15904943
theorem B7068863 : Blo 2205435 7068863 := bstep (se 1 (by rfl) ⟨5301647, by rfl⟩ : syracuseStep 7068863 = 10603295) B10603295
theorem B4712575 : Blo 2205435 4712575 := bstep (se 1 (by rfl) ⟨3534431, by rfl⟩ : syracuseStep 4712575 = 7068863) B7068863
theorem B6283433 : Blo 2205435 6283433 := bstep (se 2 (by rfl) ⟨2356287, by rfl⟩ : syracuseStep 6283433 = 4712575) B4712575
theorem B16755821 : Blo 2205435 16755821 := bstep (se 3 (by rfl) ⟨3141716, by rfl⟩ : syracuseStep 16755821 = 6283433) B6283433
theorem B11170547 : Blo 2205435 11170547 := bstep (se 1 (by rfl) ⟨8377910, by rfl⟩ : syracuseStep 11170547 = 16755821) B16755821
theorem B7447031 : Blo 2205435 7447031 := bstep (se 1 (by rfl) ⟨5585273, by rfl⟩ : syracuseStep 7447031 = 11170547) B11170547
theorem B4964687 : Blo 2205435 4964687 := bstep (se 1 (by rfl) ⟨3723515, by rfl⟩ : syracuseStep 4964687 = 7447031) B7447031
theorem B3309791 : Blo 2205435 3309791 := bstep (se 1 (by rfl) ⟨2482343, by rfl⟩ : syracuseStep 3309791 = 4964687) B4964687
theorem B2206527 : Blo 2205435 2206527 := bstep (se 1 (by rfl) ⟨1654895, by rfl⟩ : syracuseStep 2206527 = 3309791) B3309791
theorem B3309797 : Blo 2205435 3309797 := bbase (se 4 (by rfl) ⟨310293, by rfl⟩ : syracuseStep 3309797 = 620587) (by norm_num)
theorem B2206531 : Blo 2205435 2206531 := bstep (se 1 (by rfl) ⟨1654898, by rfl⟩ : syracuseStep 2206531 = 3309797) B3309797
theorem B3534445 : Blo 2205435 3534445 := bbase (se 3 (by rfl) ⟨662708, by rfl⟩ : syracuseStep 3534445 = 1325417) (by norm_num)
theorem B4712593 : Blo 2205435 4712593 := bstep (se 2 (by rfl) ⟨1767222, by rfl⟩ : syracuseStep 4712593 = 3534445) B3534445
theorem B6283457 : Blo 2205435 6283457 := bstep (se 2 (by rfl) ⟨2356296, by rfl⟩ : syracuseStep 6283457 = 4712593) B4712593
theorem B4188971 : Blo 2205435 4188971 := bstep (se 1 (by rfl) ⟨3141728, by rfl⟩ : syracuseStep 4188971 = 6283457) B6283457
theorem B2792647 : Blo 2205435 2792647 := bstep (se 1 (by rfl) ⟨2094485, by rfl⟩ : syracuseStep 2792647 = 4188971) B4188971
theorem B3723529 : Blo 2205435 3723529 := bstep (se 2 (by rfl) ⟨1396323, by rfl⟩ : syracuseStep 3723529 = 2792647) B2792647
theorem B4964705 : Blo 2205435 4964705 := bstep (se 2 (by rfl) ⟨1861764, by rfl⟩ : syracuseStep 4964705 = 3723529) B3723529
theorem B3309803 : Blo 2205435 3309803 := bstep (se 1 (by rfl) ⟨2482352, by rfl⟩ : syracuseStep 3309803 = 4964705) B4964705
theorem B2206535 : Blo 2205435 2206535 := bstep (se 1 (by rfl) ⟨1654901, by rfl⟩ : syracuseStep 2206535 = 3309803) B3309803
theorem B2482357 : Blo 2205435 2482357 := bbase (se 5 (by rfl) ⟨116360, by rfl⟩ : syracuseStep 2482357 = 232721) (by norm_num)
theorem B3309809 : Blo 2205435 3309809 := bstep (se 2 (by rfl) ⟨1241178, by rfl⟩ : syracuseStep 3309809 = 2482357) B2482357
theorem B2206539 : Blo 2205435 2206539 := bstep (se 1 (by rfl) ⟨1654904, by rfl⟩ : syracuseStep 2206539 = 3309809) B3309809
theorem B2792657 : Blo 2205435 2792657 := bbase (se 2 (by rfl) ⟨1047246, by rfl⟩ : syracuseStep 2792657 = 2094493) (by norm_num)
theorem B7447085 : Blo 2205435 7447085 := bstep (se 3 (by rfl) ⟨1396328, by rfl⟩ : syracuseStep 7447085 = 2792657) B2792657
theorem B4964723 : Blo 2205435 4964723 := bstep (se 1 (by rfl) ⟨3723542, by rfl⟩ : syracuseStep 4964723 = 7447085) B7447085
theorem B3309815 : Blo 2205435 3309815 := bstep (se 1 (by rfl) ⟨2482361, by rfl⟩ : syracuseStep 3309815 = 4964723) B4964723
theorem B2206543 : Blo 2205435 2206543 := bstep (se 1 (by rfl) ⟨1654907, by rfl⟩ : syracuseStep 2206543 = 3309815) B3309815
theorem B3309821 : Blo 2205435 3309821 := bbase (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) (by norm_num)
theorem B2206547 : Blo 2205435 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B4964741 : Blo 2205435 4964741 := bbase (se 4 (by rfl) ⟨465444, by rfl⟩ : syracuseStep 4964741 = 930889) (by norm_num)
theorem B3309827 : Blo 2205435 3309827 := bstep (se 1 (by rfl) ⟨2482370, by rfl⟩ : syracuseStep 3309827 = 4964741) B4964741
theorem B2206551 : Blo 2205435 2206551 := bstep (se 1 (by rfl) ⟨1654913, by rfl⟩ : syracuseStep 2206551 = 3309827) B3309827
theorem B3141757 : Blo 2205435 3141757 := bbase (se 3 (by rfl) ⟨589079, by rfl⟩ : syracuseStep 3141757 = 1178159) (by norm_num)
theorem B4189009 : Blo 2205435 4189009 := bstep (se 2 (by rfl) ⟨1570878, by rfl⟩ : syracuseStep 4189009 = 3141757) B3141757
theorem B5585345 : Blo 2205435 5585345 := bstep (se 2 (by rfl) ⟨2094504, by rfl⟩ : syracuseStep 5585345 = 4189009) B4189009
theorem B3723563 : Blo 2205435 3723563 := bstep (se 1 (by rfl) ⟨2792672, by rfl⟩ : syracuseStep 3723563 = 5585345) B5585345
theorem B2482375 : Blo 2205435 2482375 := bstep (se 1 (by rfl) ⟨1861781, by rfl⟩ : syracuseStep 2482375 = 3723563) B3723563
theorem B3309833 : Blo 2205435 3309833 := bstep (se 2 (by rfl) ⟨1241187, by rfl⟩ : syracuseStep 3309833 = 2482375) B2482375
theorem B2206555 : Blo 2205435 2206555 := bstep (se 1 (by rfl) ⟨1654916, by rfl⟩ : syracuseStep 2206555 = 3309833) B3309833
theorem B11170709 : Blo 2205435 11170709 := bbase (se 6 (by rfl) ⟨261813, by rfl⟩ : syracuseStep 11170709 = 523627) (by norm_num)
theorem B7447139 : Blo 2205435 7447139 := bstep (se 1 (by rfl) ⟨5585354, by rfl⟩ : syracuseStep 7447139 = 11170709) B11170709
theorem B4964759 : Blo 2205435 4964759 := bstep (se 1 (by rfl) ⟨3723569, by rfl⟩ : syracuseStep 4964759 = 7447139) B7447139
theorem B3309839 : Blo 2205435 3309839 := bstep (se 1 (by rfl) ⟨2482379, by rfl⟩ : syracuseStep 3309839 = 4964759) B4964759
theorem B2206559 : Blo 2205435 2206559 := bstep (se 1 (by rfl) ⟨1654919, by rfl⟩ : syracuseStep 2206559 = 3309839) B3309839
theorem B3309845 : Blo 2205435 3309845 := bbase (se 6 (by rfl) ⟨77574, by rfl⟩ : syracuseStep 3309845 = 155149) (by norm_num)
theorem B2206563 : Blo 2205435 2206563 := bstep (se 1 (by rfl) ⟨1654922, by rfl⟩ : syracuseStep 2206563 = 3309845) B3309845
theorem B2723701 : Blo 2205435 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B3631601 : Blo 2205435 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B2421067 : Blo 2205435 2421067 := bstep (se 1 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 2421067 = 3631601) B3631601
theorem B3228089 : Blo 2205435 3228089 := bstep (se 2 (by rfl) ⟨1210533, by rfl⟩ : syracuseStep 3228089 = 2421067) B2421067
theorem B8608237 : Blo 2205435 8608237 := bstep (se 3 (by rfl) ⟨1614044, by rfl⟩ : syracuseStep 8608237 = 3228089) B3228089
theorem B45910597 : Blo 2205435 45910597 := bstep (se 4 (by rfl) ⟨4304118, by rfl⟩ : syracuseStep 45910597 = 8608237) B8608237
theorem B61214129 : Blo 2205435 61214129 := bstep (se 2 (by rfl) ⟨22955298, by rfl⟩ : syracuseStep 61214129 = 45910597) B45910597
theorem B40809419 : Blo 2205435 40809419 := bstep (se 1 (by rfl) ⟨30607064, by rfl⟩ : syracuseStep 40809419 = 61214129) B61214129
theorem B27206279 : Blo 2205435 27206279 := bstep (se 1 (by rfl) ⟨20404709, by rfl⟩ : syracuseStep 27206279 = 40809419) B40809419
theorem B18137519 : Blo 2205435 18137519 := bstep (se 1 (by rfl) ⟨13603139, by rfl⟩ : syracuseStep 18137519 = 27206279) B27206279
theorem B12091679 : Blo 2205435 12091679 := bstep (se 1 (by rfl) ⟨9068759, by rfl⟩ : syracuseStep 12091679 = 18137519) B18137519
theorem B8061119 : Blo 2205435 8061119 := bstep (se 1 (by rfl) ⟨6045839, by rfl⟩ : syracuseStep 8061119 = 12091679) B12091679
theorem B5374079 : Blo 2205435 5374079 := bstep (se 1 (by rfl) ⟨4030559, by rfl⟩ : syracuseStep 5374079 = 8061119) B8061119
theorem B3582719 : Blo 2205435 3582719 := bstep (se 1 (by rfl) ⟨2687039, by rfl⟩ : syracuseStep 3582719 = 5374079) B5374079
theorem B2388479 : Blo 2205435 2388479 := bstep (se 1 (by rfl) ⟨1791359, by rfl⟩ : syracuseStep 2388479 = 3582719) B3582719
theorem B6369277 : Blo 2205435 6369277 := bstep (se 3 (by rfl) ⟨1194239, by rfl⟩ : syracuseStep 6369277 = 2388479) B2388479
theorem B8492369 : Blo 2205435 8492369 := bstep (se 2 (by rfl) ⟨3184638, by rfl⟩ : syracuseStep 8492369 = 6369277) B6369277
theorem B22646317 : Blo 2205435 22646317 := bstep (se 3 (by rfl) ⟨4246184, by rfl⟩ : syracuseStep 22646317 = 8492369) B8492369
theorem B30195089 : Blo 2205435 30195089 := bstep (se 2 (by rfl) ⟨11323158, by rfl⟩ : syracuseStep 30195089 = 22646317) B22646317
theorem B20130059 : Blo 2205435 20130059 := bstep (se 1 (by rfl) ⟨15097544, by rfl⟩ : syracuseStep 20130059 = 30195089) B30195089
theorem B53680157 : Blo 2205435 53680157 := bstep (se 3 (by rfl) ⟨10065029, by rfl⟩ : syracuseStep 53680157 = 20130059) B20130059
theorem B35786771 : Blo 2205435 35786771 := bstep (se 1 (by rfl) ⟨26840078, by rfl⟩ : syracuseStep 35786771 = 53680157) B53680157
theorem B23857847 : Blo 2205435 23857847 := bstep (se 1 (by rfl) ⟨17893385, by rfl⟩ : syracuseStep 23857847 = 35786771) B35786771
theorem B15905231 : Blo 2205435 15905231 := bstep (se 1 (by rfl) ⟨11928923, by rfl⟩ : syracuseStep 15905231 = 23857847) B23857847
theorem B10603487 : Blo 2205435 10603487 := bstep (se 1 (by rfl) ⟨7952615, by rfl⟩ : syracuseStep 10603487 = 15905231) B15905231
theorem B28275965 : Blo 2205435 28275965 := bstep (se 3 (by rfl) ⟨5301743, by rfl⟩ : syracuseStep 28275965 = 10603487) B10603487
theorem B18850643 : Blo 2205435 18850643 := bstep (se 1 (by rfl) ⟨14137982, by rfl⟩ : syracuseStep 18850643 = 28275965) B28275965
theorem B12567095 : Blo 2205435 12567095 := bstep (se 1 (by rfl) ⟨9425321, by rfl⟩ : syracuseStep 12567095 = 18850643) B18850643
theorem B8378063 : Blo 2205435 8378063 := bstep (se 1 (by rfl) ⟨6283547, by rfl⟩ : syracuseStep 8378063 = 12567095) B12567095
theorem B5585375 : Blo 2205435 5585375 := bstep (se 1 (by rfl) ⟨4189031, by rfl⟩ : syracuseStep 5585375 = 8378063) B8378063
theorem B3723583 : Blo 2205435 3723583 := bstep (se 1 (by rfl) ⟨2792687, by rfl⟩ : syracuseStep 3723583 = 5585375) B5585375
theorem B4964777 : Blo 2205435 4964777 := bstep (se 2 (by rfl) ⟨1861791, by rfl⟩ : syracuseStep 4964777 = 3723583) B3723583
theorem B3309851 : Blo 2205435 3309851 := bstep (se 1 (by rfl) ⟨2482388, by rfl⟩ : syracuseStep 3309851 = 4964777) B4964777
theorem B2206567 : Blo 2205435 2206567 := bstep (se 1 (by rfl) ⟨1654925, by rfl⟩ : syracuseStep 2206567 = 3309851) B3309851
theorem B2482393 : Blo 2205435 2482393 := bbase (se 2 (by rfl) ⟨930897, by rfl⟩ : syracuseStep 2482393 = 1861795) (by norm_num)
theorem B3309857 : Blo 2205435 3309857 := bstep (se 2 (by rfl) ⟨1241196, by rfl⟩ : syracuseStep 3309857 = 2482393) B2482393
theorem B2206571 : Blo 2205435 2206571 := bstep (se 1 (by rfl) ⟨1654928, by rfl⟩ : syracuseStep 2206571 = 3309857) B3309857
theorem B3534509 : Blo 2205435 3534509 := bbase (se 3 (by rfl) ⟨662720, by rfl⟩ : syracuseStep 3534509 = 1325441) (by norm_num)
theorem B2356339 : Blo 2205435 2356339 := bstep (se 1 (by rfl) ⟨1767254, by rfl⟩ : syracuseStep 2356339 = 3534509) B3534509
theorem B3141785 : Blo 2205435 3141785 := bstep (se 2 (by rfl) ⟨1178169, by rfl⟩ : syracuseStep 3141785 = 2356339) B2356339
theorem B8378093 : Blo 2205435 8378093 := bstep (se 3 (by rfl) ⟨1570892, by rfl⟩ : syracuseStep 8378093 = 3141785) B3141785
theorem B5585395 : Blo 2205435 5585395 := bstep (se 1 (by rfl) ⟨4189046, by rfl⟩ : syracuseStep 5585395 = 8378093) B8378093
theorem B7447193 : Blo 2205435 7447193 := bstep (se 2 (by rfl) ⟨2792697, by rfl⟩ : syracuseStep 7447193 = 5585395) B5585395
theorem B4964795 : Blo 2205435 4964795 := bstep (se 1 (by rfl) ⟨3723596, by rfl⟩ : syracuseStep 4964795 = 7447193) B7447193
theorem B3309863 : Blo 2205435 3309863 := bstep (se 1 (by rfl) ⟨2482397, by rfl⟩ : syracuseStep 3309863 = 4964795) B4964795
theorem B2206575 : Blo 2205435 2206575 := bstep (se 1 (by rfl) ⟨1654931, by rfl⟩ : syracuseStep 2206575 = 3309863) B3309863
theorem B3309869 : Blo 2205435 3309869 := bbase (se 3 (by rfl) ⟨620600, by rfl⟩ : syracuseStep 3309869 = 1241201) (by norm_num)
theorem B2206579 : Blo 2205435 2206579 := bstep (se 1 (by rfl) ⟨1654934, by rfl⟩ : syracuseStep 2206579 = 3309869) B3309869
theorem B4964813 : Blo 2205435 4964813 := bbase (se 3 (by rfl) ⟨930902, by rfl⟩ : syracuseStep 4964813 = 1861805) (by norm_num)
theorem B3309875 : Blo 2205435 3309875 := bstep (se 1 (by rfl) ⟨2482406, by rfl⟩ : syracuseStep 3309875 = 4964813) B4964813
theorem B2206583 : Blo 2205435 2206583 := bstep (se 1 (by rfl) ⟨1654937, by rfl⟩ : syracuseStep 2206583 = 3309875) B3309875
theorem B2792713 : Blo 2205435 2792713 := bbase (se 2 (by rfl) ⟨1047267, by rfl⟩ : syracuseStep 2792713 = 2094535) (by norm_num)
theorem B3723617 : Blo 2205435 3723617 := bstep (se 2 (by rfl) ⟨1396356, by rfl⟩ : syracuseStep 3723617 = 2792713) B2792713
theorem B2482411 : Blo 2205435 2482411 := bstep (se 1 (by rfl) ⟨1861808, by rfl⟩ : syracuseStep 2482411 = 3723617) B3723617
theorem B3309881 : Blo 2205435 3309881 := bstep (se 2 (by rfl) ⟨1241205, by rfl⟩ : syracuseStep 3309881 = 2482411) B2482411
theorem B2206587 : Blo 2205435 2206587 := bstep (se 1 (by rfl) ⟨1654940, by rfl⟩ : syracuseStep 2206587 = 3309881) B3309881
theorem B2516285 : Blo 2205435 2516285 := bbase (se 3 (by rfl) ⟨471803, by rfl⟩ : syracuseStep 2516285 = 943607) (by norm_num)
theorem B6710093 : Blo 2205435 6710093 := bstep (se 3 (by rfl) ⟨1258142, by rfl⟩ : syracuseStep 6710093 = 2516285) B2516285
theorem B4473395 : Blo 2205435 4473395 := bstep (se 1 (by rfl) ⟨3355046, by rfl⟩ : syracuseStep 4473395 = 6710093) B6710093
theorem B2982263 : Blo 2205435 2982263 := bstep (se 1 (by rfl) ⟨2236697, by rfl⟩ : syracuseStep 2982263 = 4473395) B4473395
theorem B31810805 : Blo 2205435 31810805 := bstep (se 5 (by rfl) ⟨1491131, by rfl⟩ : syracuseStep 31810805 = 2982263) B2982263
theorem B21207203 : Blo 2205435 21207203 := bstep (se 1 (by rfl) ⟨15905402, by rfl⟩ : syracuseStep 21207203 = 31810805) B31810805
theorem B14138135 : Blo 2205435 14138135 := bstep (se 1 (by rfl) ⟨10603601, by rfl⟩ : syracuseStep 14138135 = 21207203) B21207203
theorem B9425423 : Blo 2205435 9425423 := bstep (se 1 (by rfl) ⟨7069067, by rfl⟩ : syracuseStep 9425423 = 14138135) B14138135
theorem B25134461 : Blo 2205435 25134461 := bstep (se 3 (by rfl) ⟨4712711, by rfl⟩ : syracuseStep 25134461 = 9425423) B9425423
theorem B16756307 : Blo 2205435 16756307 := bstep (se 1 (by rfl) ⟨12567230, by rfl⟩ : syracuseStep 16756307 = 25134461) B25134461
theorem B11170871 : Blo 2205435 11170871 := bstep (se 1 (by rfl) ⟨8378153, by rfl⟩ : syracuseStep 11170871 = 16756307) B16756307
theorem B7447247 : Blo 2205435 7447247 := bstep (se 1 (by rfl) ⟨5585435, by rfl⟩ : syracuseStep 7447247 = 11170871) B11170871
theorem B4964831 : Blo 2205435 4964831 := bstep (se 1 (by rfl) ⟨3723623, by rfl⟩ : syracuseStep 4964831 = 7447247) B7447247
theorem B3309887 : Blo 2205435 3309887 := bstep (se 1 (by rfl) ⟨2482415, by rfl⟩ : syracuseStep 3309887 = 4964831) B4964831
theorem B2206591 : Blo 2205435 2206591 := bstep (se 1 (by rfl) ⟨1654943, by rfl⟩ : syracuseStep 2206591 = 3309887) B3309887
theorem B3309893 : Blo 2205435 3309893 := bbase (se 4 (by rfl) ⟨310302, by rfl⟩ : syracuseStep 3309893 = 620605) (by norm_num)
theorem B2206595 : Blo 2205435 2206595 := bstep (se 1 (by rfl) ⟨1654946, by rfl⟩ : syracuseStep 2206595 = 3309893) B3309893
theorem B3723637 : Blo 2205435 3723637 := bbase (se 5 (by rfl) ⟨174545, by rfl⟩ : syracuseStep 3723637 = 349091) (by norm_num)
theorem B4964849 : Blo 2205435 4964849 := bstep (se 2 (by rfl) ⟨1861818, by rfl⟩ : syracuseStep 4964849 = 3723637) B3723637
theorem B3309899 : Blo 2205435 3309899 := bstep (se 1 (by rfl) ⟨2482424, by rfl⟩ : syracuseStep 3309899 = 4964849) B4964849
theorem B2206599 : Blo 2205435 2206599 := bstep (se 1 (by rfl) ⟨1654949, by rfl⟩ : syracuseStep 2206599 = 3309899) B3309899
theorem B2482429 : Blo 2205435 2482429 := bbase (se 3 (by rfl) ⟨465455, by rfl⟩ : syracuseStep 2482429 = 930911) (by norm_num)
theorem B3309905 : Blo 2205435 3309905 := bstep (se 2 (by rfl) ⟨1241214, by rfl⟩ : syracuseStep 3309905 = 2482429) B2482429
theorem B2206603 : Blo 2205435 2206603 := bstep (se 1 (by rfl) ⟨1654952, by rfl⟩ : syracuseStep 2206603 = 3309905) B3309905
theorem B7447301 : Blo 2205435 7447301 := bbase (se 4 (by rfl) ⟨698184, by rfl⟩ : syracuseStep 7447301 = 1396369) (by norm_num)
theorem B4964867 : Blo 2205435 4964867 := bstep (se 1 (by rfl) ⟨3723650, by rfl⟩ : syracuseStep 4964867 = 7447301) B7447301
theorem B3309911 : Blo 2205435 3309911 := bstep (se 1 (by rfl) ⟨2482433, by rfl⟩ : syracuseStep 3309911 = 4964867) B4964867
theorem B2206607 : Blo 2205435 2206607 := bstep (se 1 (by rfl) ⟨1654955, by rfl⟩ : syracuseStep 2206607 = 3309911) B3309911
theorem B3309917 : Blo 2205435 3309917 := bbase (se 3 (by rfl) ⟨620609, by rfl⟩ : syracuseStep 3309917 = 1241219) (by norm_num)
theorem B2206611 : Blo 2205435 2206611 := bstep (se 1 (by rfl) ⟨1654958, by rfl⟩ : syracuseStep 2206611 = 3309917) B3309917
theorem B4964885 : Blo 2205435 4964885 := bbase (se 6 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 4964885 = 232729) (by norm_num)
theorem B3309923 : Blo 2205435 3309923 := bstep (se 1 (by rfl) ⟨2482442, by rfl⟩ : syracuseStep 3309923 = 4964885) B4964885
theorem B2206615 : Blo 2205435 2206615 := bstep (se 1 (by rfl) ⟨1654961, by rfl⟩ : syracuseStep 2206615 = 3309923) B3309923
theorem B8378261 : Blo 2205435 8378261 := bbase (se 6 (by rfl) ⟨196365, by rfl⟩ : syracuseStep 8378261 = 392731) (by norm_num)
theorem B5585507 : Blo 2205435 5585507 := bstep (se 1 (by rfl) ⟨4189130, by rfl⟩ : syracuseStep 5585507 = 8378261) B8378261
theorem B3723671 : Blo 2205435 3723671 := bstep (se 1 (by rfl) ⟨2792753, by rfl⟩ : syracuseStep 3723671 = 5585507) B5585507
theorem B2482447 : Blo 2205435 2482447 := bstep (se 1 (by rfl) ⟨1861835, by rfl⟩ : syracuseStep 2482447 = 3723671) B3723671
theorem B3309929 : Blo 2205435 3309929 := bstep (se 2 (by rfl) ⟨1241223, by rfl⟩ : syracuseStep 3309929 = 2482447) B2482447
theorem B2206619 : Blo 2205435 2206619 := bstep (se 1 (by rfl) ⟨1654964, by rfl⟩ : syracuseStep 2206619 = 3309929) B3309929
theorem B12567413 : Blo 2205435 12567413 := bbase (se 5 (by rfl) ⟨589097, by rfl⟩ : syracuseStep 12567413 = 1178195) (by norm_num)
theorem B8378275 : Blo 2205435 8378275 := bstep (se 1 (by rfl) ⟨6283706, by rfl⟩ : syracuseStep 8378275 = 12567413) B12567413
theorem B11171033 : Blo 2205435 11171033 := bstep (se 2 (by rfl) ⟨4189137, by rfl⟩ : syracuseStep 11171033 = 8378275) B8378275
theorem B7447355 : Blo 2205435 7447355 := bstep (se 1 (by rfl) ⟨5585516, by rfl⟩ : syracuseStep 7447355 = 11171033) B11171033
theorem B4964903 : Blo 2205435 4964903 := bstep (se 1 (by rfl) ⟨3723677, by rfl⟩ : syracuseStep 4964903 = 7447355) B7447355
theorem B3309935 : Blo 2205435 3309935 := bstep (se 1 (by rfl) ⟨2482451, by rfl⟩ : syracuseStep 3309935 = 4964903) B4964903
theorem B2206623 : Blo 2205435 2206623 := bstep (se 1 (by rfl) ⟨1654967, by rfl⟩ : syracuseStep 2206623 = 3309935) B3309935
theorem B3309941 : Blo 2205435 3309941 := bbase (se 5 (by rfl) ⟨155153, by rfl⟩ : syracuseStep 3309941 = 310307) (by norm_num)
theorem B2206627 : Blo 2205435 2206627 := bstep (se 1 (by rfl) ⟨1654970, by rfl⟩ : syracuseStep 2206627 = 3309941) B3309941
theorem B3355109 : Blo 2205435 3355109 := bbase (se 4 (by rfl) ⟨314541, by rfl⟩ : syracuseStep 3355109 = 629083) (by norm_num)
theorem B2236739 : Blo 2205435 2236739 := bstep (se 1 (by rfl) ⟨1677554, by rfl⟩ : syracuseStep 2236739 = 3355109) B3355109
theorem B5964637 : Blo 2205435 5964637 := bstep (se 3 (by rfl) ⟨1118369, by rfl⟩ : syracuseStep 5964637 = 2236739) B2236739
theorem B7952849 : Blo 2205435 7952849 := bstep (se 2 (by rfl) ⟨2982318, by rfl⟩ : syracuseStep 7952849 = 5964637) B5964637
theorem B5301899 : Blo 2205435 5301899 := bstep (se 1 (by rfl) ⟨3976424, by rfl⟩ : syracuseStep 5301899 = 7952849) B7952849
theorem B3534599 : Blo 2205435 3534599 := bstep (se 1 (by rfl) ⟨2650949, by rfl⟩ : syracuseStep 3534599 = 5301899) B5301899
theorem B2356399 : Blo 2205435 2356399 := bstep (se 1 (by rfl) ⟨1767299, by rfl⟩ : syracuseStep 2356399 = 3534599) B3534599
theorem B3141865 : Blo 2205435 3141865 := bstep (se 2 (by rfl) ⟨1178199, by rfl⟩ : syracuseStep 3141865 = 2356399) B2356399
theorem B4189153 : Blo 2205435 4189153 := bstep (se 2 (by rfl) ⟨1570932, by rfl⟩ : syracuseStep 4189153 = 3141865) B3141865
theorem B5585537 : Blo 2205435 5585537 := bstep (se 2 (by rfl) ⟨2094576, by rfl⟩ : syracuseStep 5585537 = 4189153) B4189153
theorem B3723691 : Blo 2205435 3723691 := bstep (se 1 (by rfl) ⟨2792768, by rfl⟩ : syracuseStep 3723691 = 5585537) B5585537
theorem B4964921 : Blo 2205435 4964921 := bstep (se 2 (by rfl) ⟨1861845, by rfl⟩ : syracuseStep 4964921 = 3723691) B3723691
theorem B3309947 : Blo 2205435 3309947 := bstep (se 1 (by rfl) ⟨2482460, by rfl⟩ : syracuseStep 3309947 = 4964921) B4964921
theorem B2206631 : Blo 2205435 2206631 := bstep (se 1 (by rfl) ⟨1654973, by rfl⟩ : syracuseStep 2206631 = 3309947) B3309947
theorem B2482465 : Blo 2205435 2482465 := bbase (se 2 (by rfl) ⟨930924, by rfl⟩ : syracuseStep 2482465 = 1861849) (by norm_num)
theorem B3309953 : Blo 2205435 3309953 := bstep (se 2 (by rfl) ⟨1241232, by rfl⟩ : syracuseStep 3309953 = 2482465) B2482465
theorem B2206635 : Blo 2205435 2206635 := bstep (se 1 (by rfl) ⟨1654976, by rfl⟩ : syracuseStep 2206635 = 3309953) B3309953
theorem B5585557 : Blo 2205435 5585557 := bbase (se 6 (by rfl) ⟨130911, by rfl⟩ : syracuseStep 5585557 = 261823) (by norm_num)
theorem B7447409 : Blo 2205435 7447409 := bstep (se 2 (by rfl) ⟨2792778, by rfl⟩ : syracuseStep 7447409 = 5585557) B5585557
theorem B4964939 : Blo 2205435 4964939 := bstep (se 1 (by rfl) ⟨3723704, by rfl⟩ : syracuseStep 4964939 = 7447409) B7447409
theorem B3309959 : Blo 2205435 3309959 := bstep (se 1 (by rfl) ⟨2482469, by rfl⟩ : syracuseStep 3309959 = 4964939) B4964939
theorem B2206639 : Blo 2205435 2206639 := bstep (se 1 (by rfl) ⟨1654979, by rfl⟩ : syracuseStep 2206639 = 3309959) B3309959
theorem B3309965 : Blo 2205435 3309965 := bbase (se 3 (by rfl) ⟨620618, by rfl⟩ : syracuseStep 3309965 = 1241237) (by norm_num)
theorem B2206643 : Blo 2205435 2206643 := bstep (se 1 (by rfl) ⟨1654982, by rfl⟩ : syracuseStep 2206643 = 3309965) B3309965
theorem B4964957 : Blo 2205435 4964957 := bbase (se 3 (by rfl) ⟨930929, by rfl⟩ : syracuseStep 4964957 = 1861859) (by norm_num)
theorem B3309971 : Blo 2205435 3309971 := bstep (se 1 (by rfl) ⟨2482478, by rfl⟩ : syracuseStep 3309971 = 4964957) B4964957
theorem B2206647 : Blo 2205435 2206647 := bstep (se 1 (by rfl) ⟨1654985, by rfl⟩ : syracuseStep 2206647 = 3309971) B3309971
theorem B3723725 : Blo 2205435 3723725 := bbase (se 3 (by rfl) ⟨698198, by rfl⟩ : syracuseStep 3723725 = 1396397) (by norm_num)
theorem B2482483 : Blo 2205435 2482483 := bstep (se 1 (by rfl) ⟨1861862, by rfl⟩ : syracuseStep 2482483 = 3723725) B3723725
theorem B3309977 : Blo 2205435 3309977 := bstep (se 2 (by rfl) ⟨1241241, by rfl⟩ : syracuseStep 3309977 = 2482483) B2482483
theorem B2206651 : Blo 2205435 2206651 := bstep (se 1 (by rfl) ⟨1654988, by rfl⟩ : syracuseStep 2206651 = 3309977) B3309977
theorem B10603909 : Blo 2205435 10603909 := bbase (se 4 (by rfl) ⟨994116, by rfl⟩ : syracuseStep 10603909 = 1988233) (by norm_num)
theorem B14138545 : Blo 2205435 14138545 := bstep (se 2 (by rfl) ⟨5301954, by rfl⟩ : syracuseStep 14138545 = 10603909) B10603909
theorem B18851393 : Blo 2205435 18851393 := bstep (se 2 (by rfl) ⟨7069272, by rfl⟩ : syracuseStep 18851393 = 14138545) B14138545
theorem B12567595 : Blo 2205435 12567595 := bstep (se 1 (by rfl) ⟨9425696, by rfl⟩ : syracuseStep 12567595 = 18851393) B18851393
theorem B16756793 : Blo 2205435 16756793 := bstep (se 2 (by rfl) ⟨6283797, by rfl⟩ : syracuseStep 16756793 = 12567595) B12567595
theorem B11171195 : Blo 2205435 11171195 := bstep (se 1 (by rfl) ⟨8378396, by rfl⟩ : syracuseStep 11171195 = 16756793) B16756793
theorem B7447463 : Blo 2205435 7447463 := bstep (se 1 (by rfl) ⟨5585597, by rfl⟩ : syracuseStep 7447463 = 11171195) B11171195
theorem B4964975 : Blo 2205435 4964975 := bstep (se 1 (by rfl) ⟨3723731, by rfl⟩ : syracuseStep 4964975 = 7447463) B7447463
theorem B3309983 : Blo 2205435 3309983 := bstep (se 1 (by rfl) ⟨2482487, by rfl⟩ : syracuseStep 3309983 = 4964975) B4964975
theorem B2206655 : Blo 2205435 2206655 := bstep (se 1 (by rfl) ⟨1654991, by rfl⟩ : syracuseStep 2206655 = 3309983) B3309983
theorem B3309989 : Blo 2205435 3309989 := bbase (se 4 (by rfl) ⟨310311, by rfl⟩ : syracuseStep 3309989 = 620623) (by norm_num)
theorem B2206659 : Blo 2205435 2206659 := bstep (se 1 (by rfl) ⟨1654994, by rfl⟩ : syracuseStep 2206659 = 3309989) B3309989
theorem B2792809 : Blo 2205435 2792809 := bbase (se 2 (by rfl) ⟨1047303, by rfl⟩ : syracuseStep 2792809 = 2094607) (by norm_num)
theorem B3723745 : Blo 2205435 3723745 := bstep (se 2 (by rfl) ⟨1396404, by rfl⟩ : syracuseStep 3723745 = 2792809) B2792809
theorem B4964993 : Blo 2205435 4964993 := bstep (se 2 (by rfl) ⟨1861872, by rfl⟩ : syracuseStep 4964993 = 3723745) B3723745
theorem B3309995 : Blo 2205435 3309995 := bstep (se 1 (by rfl) ⟨2482496, by rfl⟩ : syracuseStep 3309995 = 4964993) B4964993
theorem B2206663 : Blo 2205435 2206663 := bstep (se 1 (by rfl) ⟨1654997, by rfl⟩ : syracuseStep 2206663 = 3309995) B3309995
theorem B2482501 : Blo 2205435 2482501 := bbase (se 4 (by rfl) ⟨232734, by rfl⟩ : syracuseStep 2482501 = 465469) (by norm_num)
theorem B3310001 : Blo 2205435 3310001 := bstep (se 2 (by rfl) ⟨1241250, by rfl⟩ : syracuseStep 3310001 = 2482501) B2482501
theorem B2206667 : Blo 2205435 2206667 := bstep (se 1 (by rfl) ⟨1655000, by rfl⟩ : syracuseStep 2206667 = 3310001) B3310001
theorem B4189229 : Blo 2205435 4189229 := bbase (se 3 (by rfl) ⟨785480, by rfl⟩ : syracuseStep 4189229 = 1570961) (by norm_num)
theorem B2792819 : Blo 2205435 2792819 := bstep (se 1 (by rfl) ⟨2094614, by rfl⟩ : syracuseStep 2792819 = 4189229) B4189229
theorem B7447517 : Blo 2205435 7447517 := bstep (se 3 (by rfl) ⟨1396409, by rfl⟩ : syracuseStep 7447517 = 2792819) B2792819
theorem B4965011 : Blo 2205435 4965011 := bstep (se 1 (by rfl) ⟨3723758, by rfl⟩ : syracuseStep 4965011 = 7447517) B7447517
theorem B3310007 : Blo 2205435 3310007 := bstep (se 1 (by rfl) ⟨2482505, by rfl⟩ : syracuseStep 3310007 = 4965011) B4965011
theorem B2206671 : Blo 2205435 2206671 := bstep (se 1 (by rfl) ⟨1655003, by rfl⟩ : syracuseStep 2206671 = 3310007) B3310007
theorem B3310013 : Blo 2205435 3310013 := bbase (se 3 (by rfl) ⟨620627, by rfl⟩ : syracuseStep 3310013 = 1241255) (by norm_num)
theorem B2206675 : Blo 2205435 2206675 := bstep (se 1 (by rfl) ⟨1655006, by rfl⟩ : syracuseStep 2206675 = 3310013) B3310013
theorem B4965029 : Blo 2205435 4965029 := bbase (se 4 (by rfl) ⟨465471, by rfl⟩ : syracuseStep 4965029 = 930943) (by norm_num)
theorem B3310019 : Blo 2205435 3310019 := bstep (se 1 (by rfl) ⟨2482514, by rfl⟩ : syracuseStep 3310019 = 4965029) B4965029
theorem B2206679 : Blo 2205435 2206679 := bstep (se 1 (by rfl) ⟨1655009, by rfl⟩ : syracuseStep 2206679 = 3310019) B3310019
theorem B5585669 : Blo 2205435 5585669 := bbase (se 4 (by rfl) ⟨523656, by rfl⟩ : syracuseStep 5585669 = 1047313) (by norm_num)
theorem B3723779 : Blo 2205435 3723779 := bstep (se 1 (by rfl) ⟨2792834, by rfl⟩ : syracuseStep 3723779 = 5585669) B5585669
theorem B2482519 : Blo 2205435 2482519 := bstep (se 1 (by rfl) ⟨1861889, by rfl⟩ : syracuseStep 2482519 = 3723779) B3723779
theorem B3310025 : Blo 2205435 3310025 := bstep (se 2 (by rfl) ⟨1241259, by rfl⟩ : syracuseStep 3310025 = 2482519) B2482519
theorem B2206683 : Blo 2205435 2206683 := bstep (se 1 (by rfl) ⟨1655012, by rfl⟩ : syracuseStep 2206683 = 3310025) B3310025
theorem B4712917 : Blo 2205435 4712917 := bbase (se 7 (by rfl) ⟨55229, by rfl⟩ : syracuseStep 4712917 = 110459) (by norm_num)
theorem B6283889 : Blo 2205435 6283889 := bstep (se 2 (by rfl) ⟨2356458, by rfl⟩ : syracuseStep 6283889 = 4712917) B4712917
theorem B4189259 : Blo 2205435 4189259 := bstep (se 1 (by rfl) ⟨3141944, by rfl⟩ : syracuseStep 4189259 = 6283889) B6283889
theorem B11171357 : Blo 2205435 11171357 := bstep (se 3 (by rfl) ⟨2094629, by rfl⟩ : syracuseStep 11171357 = 4189259) B4189259
theorem B7447571 : Blo 2205435 7447571 := bstep (se 1 (by rfl) ⟨5585678, by rfl⟩ : syracuseStep 7447571 = 11171357) B11171357
theorem B4965047 : Blo 2205435 4965047 := bstep (se 1 (by rfl) ⟨3723785, by rfl⟩ : syracuseStep 4965047 = 7447571) B7447571
theorem B3310031 : Blo 2205435 3310031 := bstep (se 1 (by rfl) ⟨2482523, by rfl⟩ : syracuseStep 3310031 = 4965047) B4965047
theorem B2206687 : Blo 2205435 2206687 := bstep (se 1 (by rfl) ⟨1655015, by rfl⟩ : syracuseStep 2206687 = 3310031) B3310031
theorem B3310037 : Blo 2205435 3310037 := bbase (se 7 (by rfl) ⟨38789, by rfl⟩ : syracuseStep 3310037 = 77579) (by norm_num)
theorem B2206691 : Blo 2205435 2206691 := bstep (se 1 (by rfl) ⟨1655018, by rfl⟩ : syracuseStep 2206691 = 3310037) B3310037
theorem B8378549 : Blo 2205435 8378549 := bbase (se 5 (by rfl) ⟨392744, by rfl⟩ : syracuseStep 8378549 = 785489) (by norm_num)
theorem B5585699 : Blo 2205435 5585699 := bstep (se 1 (by rfl) ⟨4189274, by rfl⟩ : syracuseStep 5585699 = 8378549) B8378549
theorem B3723799 : Blo 2205435 3723799 := bstep (se 1 (by rfl) ⟨2792849, by rfl⟩ : syracuseStep 3723799 = 5585699) B5585699
theorem B4965065 : Blo 2205435 4965065 := bstep (se 2 (by rfl) ⟨1861899, by rfl⟩ : syracuseStep 4965065 = 3723799) B3723799
theorem B3310043 : Blo 2205435 3310043 := bstep (se 1 (by rfl) ⟨2482532, by rfl⟩ : syracuseStep 3310043 = 4965065) B4965065
theorem B2206695 : Blo 2205435 2206695 := bstep (se 1 (by rfl) ⟨1655021, by rfl⟩ : syracuseStep 2206695 = 3310043) B3310043
theorem B2482537 : Blo 2205435 2482537 := bbase (se 2 (by rfl) ⟨930951, by rfl⟩ : syracuseStep 2482537 = 1861903) (by norm_num)
theorem B3310049 : Blo 2205435 3310049 := bstep (se 2 (by rfl) ⟨1241268, by rfl⟩ : syracuseStep 3310049 = 2482537) B2482537
theorem B2206699 : Blo 2205435 2206699 := bstep (se 1 (by rfl) ⟨1655024, by rfl⟩ : syracuseStep 2206699 = 3310049) B3310049
theorem B10065653 : Blo 2205435 10065653 := bbase (se 5 (by rfl) ⟨471827, by rfl⟩ : syracuseStep 10065653 = 943655) (by norm_num)
theorem B6710435 : Blo 2205435 6710435 := bstep (se 1 (by rfl) ⟨5032826, by rfl⟩ : syracuseStep 6710435 = 10065653) B10065653
theorem B4473623 : Blo 2205435 4473623 := bstep (se 1 (by rfl) ⟨3355217, by rfl⟩ : syracuseStep 4473623 = 6710435) B6710435
theorem B2982415 : Blo 2205435 2982415 := bstep (se 1 (by rfl) ⟨2236811, by rfl⟩ : syracuseStep 2982415 = 4473623) B4473623
theorem B3976553 : Blo 2205435 3976553 := bstep (se 2 (by rfl) ⟨1491207, by rfl⟩ : syracuseStep 3976553 = 2982415) B2982415
theorem B10604141 : Blo 2205435 10604141 := bstep (se 3 (by rfl) ⟨1988276, by rfl⟩ : syracuseStep 10604141 = 3976553) B3976553
theorem B7069427 : Blo 2205435 7069427 := bstep (se 1 (by rfl) ⟨5302070, by rfl⟩ : syracuseStep 7069427 = 10604141) B10604141
theorem B4712951 : Blo 2205435 4712951 := bstep (se 1 (by rfl) ⟨3534713, by rfl⟩ : syracuseStep 4712951 = 7069427) B7069427
theorem B12567869 : Blo 2205435 12567869 := bstep (se 3 (by rfl) ⟨2356475, by rfl⟩ : syracuseStep 12567869 = 4712951) B4712951
theorem B8378579 : Blo 2205435 8378579 := bstep (se 1 (by rfl) ⟨6283934, by rfl⟩ : syracuseStep 8378579 = 12567869) B12567869
theorem B5585719 : Blo 2205435 5585719 := bstep (se 1 (by rfl) ⟨4189289, by rfl⟩ : syracuseStep 5585719 = 8378579) B8378579
theorem B7447625 : Blo 2205435 7447625 := bstep (se 2 (by rfl) ⟨2792859, by rfl⟩ : syracuseStep 7447625 = 5585719) B5585719
theorem B4965083 : Blo 2205435 4965083 := bstep (se 1 (by rfl) ⟨3723812, by rfl⟩ : syracuseStep 4965083 = 7447625) B7447625
theorem B3310055 : Blo 2205435 3310055 := bstep (se 1 (by rfl) ⟨2482541, by rfl⟩ : syracuseStep 3310055 = 4965083) B4965083
theorem B2206703 : Blo 2205435 2206703 := bstep (se 1 (by rfl) ⟨1655027, by rfl⟩ : syracuseStep 2206703 = 3310055) B3310055
theorem B3310061 : Blo 2205435 3310061 := bbase (se 3 (by rfl) ⟨620636, by rfl⟩ : syracuseStep 3310061 = 1241273) (by norm_num)
theorem B2206707 : Blo 2205435 2206707 := bstep (se 1 (by rfl) ⟨1655030, by rfl⟩ : syracuseStep 2206707 = 3310061) B3310061
theorem B4965101 : Blo 2205435 4965101 := bbase (se 3 (by rfl) ⟨930956, by rfl⟩ : syracuseStep 4965101 = 1861913) (by norm_num)
theorem B3310067 : Blo 2205435 3310067 := bstep (se 1 (by rfl) ⟨2482550, by rfl⟩ : syracuseStep 3310067 = 4965101) B4965101
theorem B2206711 : Blo 2205435 2206711 := bstep (se 1 (by rfl) ⟨1655033, by rfl⟩ : syracuseStep 2206711 = 3310067) B3310067
theorem B2356489 : Blo 2205435 2356489 := bbase (se 2 (by rfl) ⟨883683, by rfl⟩ : syracuseStep 2356489 = 1767367) (by norm_num)
theorem B3141985 : Blo 2205435 3141985 := bstep (se 2 (by rfl) ⟨1178244, by rfl⟩ : syracuseStep 3141985 = 2356489) B2356489
theorem B4189313 : Blo 2205435 4189313 := bstep (se 2 (by rfl) ⟨1570992, by rfl⟩ : syracuseStep 4189313 = 3141985) B3141985
theorem B2792875 : Blo 2205435 2792875 := bstep (se 1 (by rfl) ⟨2094656, by rfl⟩ : syracuseStep 2792875 = 4189313) B4189313
theorem B3723833 : Blo 2205435 3723833 := bstep (se 2 (by rfl) ⟨1396437, by rfl⟩ : syracuseStep 3723833 = 2792875) B2792875
theorem B2482555 : Blo 2205435 2482555 := bstep (se 1 (by rfl) ⟨1861916, by rfl⟩ : syracuseStep 2482555 = 3723833) B3723833
theorem B3310073 : Blo 2205435 3310073 := bstep (se 2 (by rfl) ⟨1241277, by rfl⟩ : syracuseStep 3310073 = 2482555) B2482555
theorem B2206715 : Blo 2205435 2206715 := bstep (se 1 (by rfl) ⟨1655036, by rfl⟩ : syracuseStep 2206715 = 3310073) B3310073
theorem B3582965 : Blo 2205435 3582965 := bbase (se 5 (by rfl) ⟨167951, by rfl⟩ : syracuseStep 3582965 = 335903) (by norm_num)
theorem B9554573 : Blo 2205435 9554573 := bstep (se 3 (by rfl) ⟨1791482, by rfl⟩ : syracuseStep 9554573 = 3582965) B3582965
theorem B6369715 : Blo 2205435 6369715 := bstep (se 1 (by rfl) ⟨4777286, by rfl⟩ : syracuseStep 6369715 = 9554573) B9554573
theorem B8492953 : Blo 2205435 8492953 := bstep (se 2 (by rfl) ⟨3184857, by rfl⟩ : syracuseStep 8492953 = 6369715) B6369715
theorem B11323937 : Blo 2205435 11323937 := bstep (se 2 (by rfl) ⟨4246476, by rfl⟩ : syracuseStep 11323937 = 8492953) B8492953
theorem B7549291 : Blo 2205435 7549291 := bstep (se 1 (by rfl) ⟨5661968, by rfl⟩ : syracuseStep 7549291 = 11323937) B11323937
theorem B40262885 : Blo 2205435 40262885 := bstep (se 4 (by rfl) ⟨3774645, by rfl⟩ : syracuseStep 40262885 = 7549291) B7549291
theorem B26841923 : Blo 2205435 26841923 := bstep (se 1 (by rfl) ⟨20131442, by rfl⟩ : syracuseStep 26841923 = 40262885) B40262885
theorem B17894615 : Blo 2205435 17894615 := bstep (se 1 (by rfl) ⟨13420961, by rfl⟩ : syracuseStep 17894615 = 26841923) B26841923
theorem B47718973 : Blo 2205435 47718973 := bstep (se 3 (by rfl) ⟨8947307, by rfl⟩ : syracuseStep 47718973 = 17894615) B17894615
theorem B63625297 : Blo 2205435 63625297 := bstep (se 2 (by rfl) ⟨23859486, by rfl⟩ : syracuseStep 63625297 = 47718973) B47718973
theorem B84833729 : Blo 2205435 84833729 := bstep (se 2 (by rfl) ⟨31812648, by rfl⟩ : syracuseStep 84833729 = 63625297) B63625297
theorem B56555819 : Blo 2205435 56555819 := bstep (se 1 (by rfl) ⟨42416864, by rfl⟩ : syracuseStep 56555819 = 84833729) B84833729
theorem B37703879 : Blo 2205435 37703879 := bstep (se 1 (by rfl) ⟨28277909, by rfl⟩ : syracuseStep 37703879 = 56555819) B56555819
theorem B25135919 : Blo 2205435 25135919 := bstep (se 1 (by rfl) ⟨18851939, by rfl⟩ : syracuseStep 25135919 = 37703879) B37703879
theorem B16757279 : Blo 2205435 16757279 := bstep (se 1 (by rfl) ⟨12567959, by rfl⟩ : syracuseStep 16757279 = 25135919) B25135919
theorem B11171519 : Blo 2205435 11171519 := bstep (se 1 (by rfl) ⟨8378639, by rfl⟩ : syracuseStep 11171519 = 16757279) B16757279
theorem B7447679 : Blo 2205435 7447679 := bstep (se 1 (by rfl) ⟨5585759, by rfl⟩ : syracuseStep 7447679 = 11171519) B11171519
theorem B4965119 : Blo 2205435 4965119 := bstep (se 1 (by rfl) ⟨3723839, by rfl⟩ : syracuseStep 4965119 = 7447679) B7447679
theorem B3310079 : Blo 2205435 3310079 := bstep (se 1 (by rfl) ⟨2482559, by rfl⟩ : syracuseStep 3310079 = 4965119) B4965119
theorem B2206719 : Blo 2205435 2206719 := bstep (se 1 (by rfl) ⟨1655039, by rfl⟩ : syracuseStep 2206719 = 3310079) B3310079
theorem B3310085 : Blo 2205435 3310085 := bbase (se 4 (by rfl) ⟨310320, by rfl⟩ : syracuseStep 3310085 = 620641) (by norm_num)
theorem B2206723 : Blo 2205435 2206723 := bstep (se 1 (by rfl) ⟨1655042, by rfl⟩ : syracuseStep 2206723 = 3310085) B3310085
theorem B3723853 : Blo 2205435 3723853 := bbase (se 3 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 3723853 = 1396445) (by norm_num)
theorem B4965137 : Blo 2205435 4965137 := bstep (se 2 (by rfl) ⟨1861926, by rfl⟩ : syracuseStep 4965137 = 3723853) B3723853
theorem B3310091 : Blo 2205435 3310091 := bstep (se 1 (by rfl) ⟨2482568, by rfl⟩ : syracuseStep 3310091 = 4965137) B4965137
theorem B2206727 : Blo 2205435 2206727 := bstep (se 1 (by rfl) ⟨1655045, by rfl⟩ : syracuseStep 2206727 = 3310091) B3310091
theorem B2482573 : Blo 2205435 2482573 := bbase (se 3 (by rfl) ⟨465482, by rfl⟩ : syracuseStep 2482573 = 930965) (by norm_num)
theorem B3310097 : Blo 2205435 3310097 := bstep (se 2 (by rfl) ⟨1241286, by rfl⟩ : syracuseStep 3310097 = 2482573) B2482573
theorem B2206731 : Blo 2205435 2206731 := bstep (se 1 (by rfl) ⟨1655048, by rfl⟩ : syracuseStep 2206731 = 3310097) B3310097
theorem B7447733 : Blo 2205435 7447733 := bbase (se 5 (by rfl) ⟨349112, by rfl⟩ : syracuseStep 7447733 = 698225) (by norm_num)
theorem B4965155 : Blo 2205435 4965155 := bstep (se 1 (by rfl) ⟨3723866, by rfl⟩ : syracuseStep 4965155 = 7447733) B7447733
theorem B3310103 : Blo 2205435 3310103 := bstep (se 1 (by rfl) ⟨2482577, by rfl⟩ : syracuseStep 3310103 = 4965155) B4965155
theorem B2206735 : Blo 2205435 2206735 := bstep (se 1 (by rfl) ⟨1655051, by rfl⟩ : syracuseStep 2206735 = 3310103) B3310103
theorem B3310109 : Blo 2205435 3310109 := bbase (se 3 (by rfl) ⟨620645, by rfl⟩ : syracuseStep 3310109 = 1241291) (by norm_num)
theorem B2206739 : Blo 2205435 2206739 := bstep (se 1 (by rfl) ⟨1655054, by rfl⟩ : syracuseStep 2206739 = 3310109) B3310109
theorem B4965173 : Blo 2205435 4965173 := bbase (se 5 (by rfl) ⟨232742, by rfl⟩ : syracuseStep 4965173 = 465485) (by norm_num)
theorem B3310115 : Blo 2205435 3310115 := bstep (se 1 (by rfl) ⟨2482586, by rfl⟩ : syracuseStep 3310115 = 4965173) B4965173
theorem B2206743 : Blo 2205435 2206743 := bstep (se 1 (by rfl) ⟨1655057, by rfl⟩ : syracuseStep 2206743 = 3310115) B3310115
theorem B5964949 : Blo 2205435 5964949 := bbase (se 6 (by rfl) ⟨139803, by rfl⟩ : syracuseStep 5964949 = 279607) (by norm_num)
theorem B7953265 : Blo 2205435 7953265 := bstep (se 2 (by rfl) ⟨2982474, by rfl⟩ : syracuseStep 7953265 = 5964949) B5964949
theorem B10604353 : Blo 2205435 10604353 := bstep (se 2 (by rfl) ⟨3976632, by rfl⟩ : syracuseStep 10604353 = 7953265) B7953265
theorem B14139137 : Blo 2205435 14139137 := bstep (se 2 (by rfl) ⟨5302176, by rfl⟩ : syracuseStep 14139137 = 10604353) B10604353
theorem B9426091 : Blo 2205435 9426091 := bstep (se 1 (by rfl) ⟨7069568, by rfl⟩ : syracuseStep 9426091 = 14139137) B14139137
theorem B12568121 : Blo 2205435 12568121 := bstep (se 2 (by rfl) ⟨4713045, by rfl⟩ : syracuseStep 12568121 = 9426091) B9426091
theorem B8378747 : Blo 2205435 8378747 := bstep (se 1 (by rfl) ⟨6284060, by rfl⟩ : syracuseStep 8378747 = 12568121) B12568121
theorem B5585831 : Blo 2205435 5585831 := bstep (se 1 (by rfl) ⟨4189373, by rfl⟩ : syracuseStep 5585831 = 8378747) B8378747
theorem B3723887 : Blo 2205435 3723887 := bstep (se 1 (by rfl) ⟨2792915, by rfl⟩ : syracuseStep 3723887 = 5585831) B5585831
theorem B2482591 : Blo 2205435 2482591 := bstep (se 1 (by rfl) ⟨1861943, by rfl⟩ : syracuseStep 2482591 = 3723887) B3723887
theorem B3310121 : Blo 2205435 3310121 := bstep (se 2 (by rfl) ⟨1241295, by rfl⟩ : syracuseStep 3310121 = 2482591) B2482591
theorem B2206747 : Blo 2205435 2206747 := bstep (se 1 (by rfl) ⟨1655060, by rfl⟩ : syracuseStep 2206747 = 3310121) B3310121
theorem B10203205 : Blo 2205435 10203205 := bbase (se 4 (by rfl) ⟨956550, by rfl⟩ : syracuseStep 10203205 = 1913101) (by norm_num)
theorem B13604273 : Blo 2205435 13604273 := bstep (se 2 (by rfl) ⟨5101602, by rfl⟩ : syracuseStep 13604273 = 10203205) B10203205
theorem B9069515 : Blo 2205435 9069515 := bstep (se 1 (by rfl) ⟨6802136, by rfl⟩ : syracuseStep 9069515 = 13604273) B13604273
theorem B6046343 : Blo 2205435 6046343 := bstep (se 1 (by rfl) ⟨4534757, by rfl⟩ : syracuseStep 6046343 = 9069515) B9069515
theorem B4030895 : Blo 2205435 4030895 := bstep (se 1 (by rfl) ⟨3023171, by rfl⟩ : syracuseStep 4030895 = 6046343) B6046343
theorem B2687263 : Blo 2205435 2687263 := bstep (se 1 (by rfl) ⟨2015447, by rfl⟩ : syracuseStep 2687263 = 4030895) B4030895
theorem B14332069 : Blo 2205435 14332069 := bstep (se 4 (by rfl) ⟨1343631, by rfl⟩ : syracuseStep 14332069 = 2687263) B2687263
theorem B76437701 : Blo 2205435 76437701 := bstep (se 4 (by rfl) ⟨7166034, by rfl⟩ : syracuseStep 76437701 = 14332069) B14332069
theorem B50958467 : Blo 2205435 50958467 := bstep (se 1 (by rfl) ⟨38218850, by rfl⟩ : syracuseStep 50958467 = 76437701) B76437701
theorem B33972311 : Blo 2205435 33972311 := bstep (se 1 (by rfl) ⟨25479233, by rfl⟩ : syracuseStep 33972311 = 50958467) B50958467
theorem B22648207 : Blo 2205435 22648207 := bstep (se 1 (by rfl) ⟨16986155, by rfl⟩ : syracuseStep 22648207 = 33972311) B33972311
theorem B30197609 : Blo 2205435 30197609 := bstep (se 2 (by rfl) ⟨11324103, by rfl⟩ : syracuseStep 30197609 = 22648207) B22648207
theorem B20131739 : Blo 2205435 20131739 := bstep (se 1 (by rfl) ⟨15098804, by rfl⟩ : syracuseStep 20131739 = 30197609) B30197609
theorem B13421159 : Blo 2205435 13421159 := bstep (se 1 (by rfl) ⟨10065869, by rfl⟩ : syracuseStep 13421159 = 20131739) B20131739
theorem B8947439 : Blo 2205435 8947439 := bstep (se 1 (by rfl) ⟨6710579, by rfl⟩ : syracuseStep 8947439 = 13421159) B13421159
theorem B5964959 : Blo 2205435 5964959 := bstep (se 1 (by rfl) ⟨4473719, by rfl⟩ : syracuseStep 5964959 = 8947439) B8947439
theorem B15906557 : Blo 2205435 15906557 := bstep (se 3 (by rfl) ⟨2982479, by rfl⟩ : syracuseStep 15906557 = 5964959) B5964959
theorem B10604371 : Blo 2205435 10604371 := bstep (se 1 (by rfl) ⟨7953278, by rfl⟩ : syracuseStep 10604371 = 15906557) B15906557
theorem B14139161 : Blo 2205435 14139161 := bstep (se 2 (by rfl) ⟨5302185, by rfl⟩ : syracuseStep 14139161 = 10604371) B10604371
theorem B9426107 : Blo 2205435 9426107 := bstep (se 1 (by rfl) ⟨7069580, by rfl⟩ : syracuseStep 9426107 = 14139161) B14139161
theorem B6284071 : Blo 2205435 6284071 := bstep (se 1 (by rfl) ⟨4713053, by rfl⟩ : syracuseStep 6284071 = 9426107) B9426107
theorem B8378761 : Blo 2205435 8378761 := bstep (se 2 (by rfl) ⟨3142035, by rfl⟩ : syracuseStep 8378761 = 6284071) B6284071
theorem B11171681 : Blo 2205435 11171681 := bstep (se 2 (by rfl) ⟨4189380, by rfl⟩ : syracuseStep 11171681 = 8378761) B8378761
theorem B7447787 : Blo 2205435 7447787 := bstep (se 1 (by rfl) ⟨5585840, by rfl⟩ : syracuseStep 7447787 = 11171681) B11171681
theorem B4965191 : Blo 2205435 4965191 := bstep (se 1 (by rfl) ⟨3723893, by rfl⟩ : syracuseStep 4965191 = 7447787) B7447787
theorem B3310127 : Blo 2205435 3310127 := bstep (se 1 (by rfl) ⟨2482595, by rfl⟩ : syracuseStep 3310127 = 4965191) B4965191
theorem B2206751 : Blo 2205435 2206751 := bstep (se 1 (by rfl) ⟨1655063, by rfl⟩ : syracuseStep 2206751 = 3310127) B3310127
theorem B3310133 : Blo 2205435 3310133 := bbase (se 5 (by rfl) ⟨155162, by rfl⟩ : syracuseStep 3310133 = 310325) (by norm_num)
theorem B2206755 : Blo 2205435 2206755 := bstep (se 1 (by rfl) ⟨1655066, by rfl⟩ : syracuseStep 2206755 = 3310133) B3310133
theorem B5585861 : Blo 2205435 5585861 := bbase (se 4 (by rfl) ⟨523674, by rfl⟩ : syracuseStep 5585861 = 1047349) (by norm_num)
theorem B3723907 : Blo 2205435 3723907 := bstep (se 1 (by rfl) ⟨2792930, by rfl⟩ : syracuseStep 3723907 = 5585861) B5585861
theorem B4965209 : Blo 2205435 4965209 := bstep (se 2 (by rfl) ⟨1861953, by rfl⟩ : syracuseStep 4965209 = 3723907) B3723907
theorem B3310139 : Blo 2205435 3310139 := bstep (se 1 (by rfl) ⟨2482604, by rfl⟩ : syracuseStep 3310139 = 4965209) B4965209
theorem B2206759 : Blo 2205435 2206759 := bstep (se 1 (by rfl) ⟨1655069, by rfl⟩ : syracuseStep 2206759 = 3310139) B3310139
theorem B2482609 : Blo 2205435 2482609 := bbase (se 2 (by rfl) ⟨930978, by rfl⟩ : syracuseStep 2482609 = 1861957) (by norm_num)
theorem B3310145 : Blo 2205435 3310145 := bstep (se 2 (by rfl) ⟨1241304, by rfl⟩ : syracuseStep 3310145 = 2482609) B2482609
theorem B2206763 : Blo 2205435 2206763 := bstep (se 1 (by rfl) ⟨1655072, by rfl⟩ : syracuseStep 2206763 = 3310145) B3310145
theorem B6284117 : Blo 2205435 6284117 := bbase (se 9 (by rfl) ⟨18410, by rfl⟩ : syracuseStep 6284117 = 36821) (by norm_num)
theorem B4189411 : Blo 2205435 4189411 := bstep (se 1 (by rfl) ⟨3142058, by rfl⟩ : syracuseStep 4189411 = 6284117) B6284117
theorem B5585881 : Blo 2205435 5585881 := bstep (se 2 (by rfl) ⟨2094705, by rfl⟩ : syracuseStep 5585881 = 4189411) B4189411
theorem B7447841 : Blo 2205435 7447841 := bstep (se 2 (by rfl) ⟨2792940, by rfl⟩ : syracuseStep 7447841 = 5585881) B5585881
theorem B4965227 : Blo 2205435 4965227 := bstep (se 1 (by rfl) ⟨3723920, by rfl⟩ : syracuseStep 4965227 = 7447841) B7447841
theorem B3310151 : Blo 2205435 3310151 := bstep (se 1 (by rfl) ⟨2482613, by rfl⟩ : syracuseStep 3310151 = 4965227) B4965227
theorem B2206767 : Blo 2205435 2206767 := bstep (se 1 (by rfl) ⟨1655075, by rfl⟩ : syracuseStep 2206767 = 3310151) B3310151
theorem B3310157 : Blo 2205435 3310157 := bbase (se 3 (by rfl) ⟨620654, by rfl⟩ : syracuseStep 3310157 = 1241309) (by norm_num)
theorem B2206771 : Blo 2205435 2206771 := bstep (se 1 (by rfl) ⟨1655078, by rfl⟩ : syracuseStep 2206771 = 3310157) B3310157
theorem B4965245 : Blo 2205435 4965245 := bbase (se 3 (by rfl) ⟨930983, by rfl⟩ : syracuseStep 4965245 = 1861967) (by norm_num)
theorem B3310163 : Blo 2205435 3310163 := bstep (se 1 (by rfl) ⟨2482622, by rfl⟩ : syracuseStep 3310163 = 4965245) B4965245
theorem B2206775 : Blo 2205435 2206775 := bstep (se 1 (by rfl) ⟨1655081, by rfl⟩ : syracuseStep 2206775 = 3310163) B3310163
theorem B3723941 : Blo 2205435 3723941 := bbase (se 4 (by rfl) ⟨349119, by rfl⟩ : syracuseStep 3723941 = 698239) (by norm_num)
theorem B2482627 : Blo 2205435 2482627 := bstep (se 1 (by rfl) ⟨1861970, by rfl⟩ : syracuseStep 2482627 = 3723941) B3723941
theorem B3310169 : Blo 2205435 3310169 := bstep (se 2 (by rfl) ⟨1241313, by rfl⟩ : syracuseStep 3310169 = 2482627) B2482627
theorem B2206779 : Blo 2205435 2206779 := bstep (se 1 (by rfl) ⟨1655084, by rfl⟩ : syracuseStep 2206779 = 3310169) B3310169
theorem B2356561 : Blo 2205435 2356561 := bbase (se 2 (by rfl) ⟨883710, by rfl⟩ : syracuseStep 2356561 = 1767421) (by norm_num)
theorem B3142081 : Blo 2205435 3142081 := bstep (se 2 (by rfl) ⟨1178280, by rfl⟩ : syracuseStep 3142081 = 2356561) B2356561
theorem B16757765 : Blo 2205435 16757765 := bstep (se 4 (by rfl) ⟨1571040, by rfl⟩ : syracuseStep 16757765 = 3142081) B3142081
theorem B11171843 : Blo 2205435 11171843 := bstep (se 1 (by rfl) ⟨8378882, by rfl⟩ : syracuseStep 11171843 = 16757765) B16757765
theorem B7447895 : Blo 2205435 7447895 := bstep (se 1 (by rfl) ⟨5585921, by rfl⟩ : syracuseStep 7447895 = 11171843) B11171843
theorem B4965263 : Blo 2205435 4965263 := bstep (se 1 (by rfl) ⟨3723947, by rfl⟩ : syracuseStep 4965263 = 7447895) B7447895
theorem B3310175 : Blo 2205435 3310175 := bstep (se 1 (by rfl) ⟨2482631, by rfl⟩ : syracuseStep 3310175 = 4965263) B4965263
theorem B2206783 : Blo 2205435 2206783 := bstep (se 1 (by rfl) ⟨1655087, by rfl⟩ : syracuseStep 2206783 = 3310175) B3310175
theorem B3310181 : Blo 2205435 3310181 := bbase (se 4 (by rfl) ⟨310329, by rfl⟩ : syracuseStep 3310181 = 620659) (by norm_num)
theorem B2206787 : Blo 2205435 2206787 := bstep (se 1 (by rfl) ⟨1655090, by rfl⟩ : syracuseStep 2206787 = 3310181) B3310181
theorem B3142093 : Blo 2205435 3142093 := bbase (se 3 (by rfl) ⟨589142, by rfl⟩ : syracuseStep 3142093 = 1178285) (by norm_num)
theorem B4189457 : Blo 2205435 4189457 := bstep (se 2 (by rfl) ⟨1571046, by rfl⟩ : syracuseStep 4189457 = 3142093) B3142093
theorem B2792971 : Blo 2205435 2792971 := bstep (se 1 (by rfl) ⟨2094728, by rfl⟩ : syracuseStep 2792971 = 4189457) B4189457
theorem B3723961 : Blo 2205435 3723961 := bstep (se 2 (by rfl) ⟨1396485, by rfl⟩ : syracuseStep 3723961 = 2792971) B2792971
theorem B4965281 : Blo 2205435 4965281 := bstep (se 2 (by rfl) ⟨1861980, by rfl⟩ : syracuseStep 4965281 = 3723961) B3723961
theorem B3310187 : Blo 2205435 3310187 := bstep (se 1 (by rfl) ⟨2482640, by rfl⟩ : syracuseStep 3310187 = 4965281) B4965281
theorem B2206791 : Blo 2205435 2206791 := bstep (se 1 (by rfl) ⟨1655093, by rfl⟩ : syracuseStep 2206791 = 3310187) B3310187
theorem B2482645 : Blo 2205435 2482645 := bbase (se 7 (by rfl) ⟨29093, by rfl⟩ : syracuseStep 2482645 = 58187) (by norm_num)
theorem B3310193 : Blo 2205435 3310193 := bstep (se 2 (by rfl) ⟨1241322, by rfl⟩ : syracuseStep 3310193 = 2482645) B2482645
theorem B2206795 : Blo 2205435 2206795 := bstep (se 1 (by rfl) ⟨1655096, by rfl⟩ : syracuseStep 2206795 = 3310193) B3310193
theorem B2792981 : Blo 2205435 2792981 := bbase (se 6 (by rfl) ⟨65460, by rfl⟩ : syracuseStep 2792981 = 130921) (by norm_num)
theorem B7447949 : Blo 2205435 7447949 := bstep (se 3 (by rfl) ⟨1396490, by rfl⟩ : syracuseStep 7447949 = 2792981) B2792981
theorem B4965299 : Blo 2205435 4965299 := bstep (se 1 (by rfl) ⟨3723974, by rfl⟩ : syracuseStep 4965299 = 7447949) B7447949
theorem B3310199 : Blo 2205435 3310199 := bstep (se 1 (by rfl) ⟨2482649, by rfl⟩ : syracuseStep 3310199 = 4965299) B4965299
theorem B2206799 : Blo 2205435 2206799 := bstep (se 1 (by rfl) ⟨1655099, by rfl⟩ : syracuseStep 2206799 = 3310199) B3310199
theorem B3310205 : Blo 2205435 3310205 := bbase (se 3 (by rfl) ⟨620663, by rfl⟩ : syracuseStep 3310205 = 1241327) (by norm_num)
theorem B2206803 : Blo 2205435 2206803 := bstep (se 1 (by rfl) ⟨1655102, by rfl⟩ : syracuseStep 2206803 = 3310205) B3310205
theorem B4965317 : Blo 2205435 4965317 := bbase (se 4 (by rfl) ⟨465498, by rfl⟩ : syracuseStep 4965317 = 930997) (by norm_num)
theorem B3310211 : Blo 2205435 3310211 := bstep (se 1 (by rfl) ⟨2482658, by rfl⟩ : syracuseStep 3310211 = 4965317) B4965317
theorem B2206807 : Blo 2205435 2206807 := bstep (se 1 (by rfl) ⟨1655105, by rfl⟩ : syracuseStep 2206807 = 3310211) B3310211
theorem B8947685 : Blo 2205435 8947685 := bbase (se 4 (by rfl) ⟨838845, by rfl⟩ : syracuseStep 8947685 = 1677691) (by norm_num)
theorem B5965123 : Blo 2205435 5965123 := bstep (se 1 (by rfl) ⟨4473842, by rfl⟩ : syracuseStep 5965123 = 8947685) B8947685
theorem B7953497 : Blo 2205435 7953497 := bstep (se 2 (by rfl) ⟨2982561, by rfl⟩ : syracuseStep 7953497 = 5965123) B5965123
theorem B5302331 : Blo 2205435 5302331 := bstep (se 1 (by rfl) ⟨3976748, by rfl⟩ : syracuseStep 5302331 = 7953497) B7953497
theorem B3534887 : Blo 2205435 3534887 := bstep (se 1 (by rfl) ⟨2651165, by rfl⟩ : syracuseStep 3534887 = 5302331) B5302331
theorem B9426365 : Blo 2205435 9426365 := bstep (se 3 (by rfl) ⟨1767443, by rfl⟩ : syracuseStep 9426365 = 3534887) B3534887
theorem B6284243 : Blo 2205435 6284243 := bstep (se 1 (by rfl) ⟨4713182, by rfl⟩ : syracuseStep 6284243 = 9426365) B9426365
theorem B4189495 : Blo 2205435 4189495 := bstep (se 1 (by rfl) ⟨3142121, by rfl⟩ : syracuseStep 4189495 = 6284243) B6284243
theorem B5585993 : Blo 2205435 5585993 := bstep (se 2 (by rfl) ⟨2094747, by rfl⟩ : syracuseStep 5585993 = 4189495) B4189495
theorem B3723995 : Blo 2205435 3723995 := bstep (se 1 (by rfl) ⟨2792996, by rfl⟩ : syracuseStep 3723995 = 5585993) B5585993
theorem B2482663 : Blo 2205435 2482663 := bstep (se 1 (by rfl) ⟨1861997, by rfl⟩ : syracuseStep 2482663 = 3723995) B3723995
theorem B3310217 : Blo 2205435 3310217 := bstep (se 2 (by rfl) ⟨1241331, by rfl⟩ : syracuseStep 3310217 = 2482663) B2482663
theorem B2206811 : Blo 2205435 2206811 := bstep (se 1 (by rfl) ⟨1655108, by rfl⟩ : syracuseStep 2206811 = 3310217) B3310217
theorem B11172005 : Blo 2205435 11172005 := bbase (se 4 (by rfl) ⟨1047375, by rfl⟩ : syracuseStep 11172005 = 2094751) (by norm_num)
theorem B7448003 : Blo 2205435 7448003 := bstep (se 1 (by rfl) ⟨5586002, by rfl⟩ : syracuseStep 7448003 = 11172005) B11172005
theorem B4965335 : Blo 2205435 4965335 := bstep (se 1 (by rfl) ⟨3724001, by rfl⟩ : syracuseStep 4965335 = 7448003) B7448003
theorem B3310223 : Blo 2205435 3310223 := bstep (se 1 (by rfl) ⟨2482667, by rfl⟩ : syracuseStep 3310223 = 4965335) B4965335
theorem B2206815 : Blo 2205435 2206815 := bstep (se 1 (by rfl) ⟨1655111, by rfl⟩ : syracuseStep 2206815 = 3310223) B3310223
theorem B3310229 : Blo 2205435 3310229 := bbase (se 6 (by rfl) ⟨77583, by rfl⟩ : syracuseStep 3310229 = 155167) (by norm_num)
theorem B2206819 : Blo 2205435 2206819 := bstep (se 1 (by rfl) ⟨1655114, by rfl⟩ : syracuseStep 2206819 = 3310229) B3310229
theorem B40264789 : Blo 2205435 40264789 := bbase (se 8 (by rfl) ⟨235926, by rfl⟩ : syracuseStep 40264789 = 471853) (by norm_num)
theorem B53686385 : Blo 2205435 53686385 := bstep (se 2 (by rfl) ⟨20132394, by rfl⟩ : syracuseStep 53686385 = 40264789) B40264789
theorem B35790923 : Blo 2205435 35790923 := bstep (se 1 (by rfl) ⟨26843192, by rfl⟩ : syracuseStep 35790923 = 53686385) B53686385
theorem B23860615 : Blo 2205435 23860615 := bstep (se 1 (by rfl) ⟨17895461, by rfl⟩ : syracuseStep 23860615 = 35790923) B35790923
theorem B31814153 : Blo 2205435 31814153 := bstep (se 2 (by rfl) ⟨11930307, by rfl⟩ : syracuseStep 31814153 = 23860615) B23860615
theorem B21209435 : Blo 2205435 21209435 := bstep (se 1 (by rfl) ⟨15907076, by rfl⟩ : syracuseStep 21209435 = 31814153) B31814153
theorem B14139623 : Blo 2205435 14139623 := bstep (se 1 (by rfl) ⟨10604717, by rfl⟩ : syracuseStep 14139623 = 21209435) B21209435
theorem B9426415 : Blo 2205435 9426415 := bstep (se 1 (by rfl) ⟨7069811, by rfl⟩ : syracuseStep 9426415 = 14139623) B14139623
theorem B12568553 : Blo 2205435 12568553 := bstep (se 2 (by rfl) ⟨4713207, by rfl⟩ : syracuseStep 12568553 = 9426415) B9426415
theorem B8379035 : Blo 2205435 8379035 := bstep (se 1 (by rfl) ⟨6284276, by rfl⟩ : syracuseStep 8379035 = 12568553) B12568553
theorem B5586023 : Blo 2205435 5586023 := bstep (se 1 (by rfl) ⟨4189517, by rfl⟩ : syracuseStep 5586023 = 8379035) B8379035
theorem B3724015 : Blo 2205435 3724015 := bstep (se 1 (by rfl) ⟨2793011, by rfl⟩ : syracuseStep 3724015 = 5586023) B5586023
theorem B4965353 : Blo 2205435 4965353 := bstep (se 2 (by rfl) ⟨1862007, by rfl⟩ : syracuseStep 4965353 = 3724015) B3724015
theorem B3310235 : Blo 2205435 3310235 := bstep (se 1 (by rfl) ⟨2482676, by rfl⟩ : syracuseStep 3310235 = 4965353) B4965353
theorem B2206823 : Blo 2205435 2206823 := bstep (se 1 (by rfl) ⟨1655117, by rfl⟩ : syracuseStep 2206823 = 3310235) B3310235
theorem B2482681 : Blo 2205435 2482681 := bbase (se 2 (by rfl) ⟨931005, by rfl⟩ : syracuseStep 2482681 = 1862011) (by norm_num)
theorem B3310241 : Blo 2205435 3310241 := bstep (se 2 (by rfl) ⟨1241340, by rfl⟩ : syracuseStep 3310241 = 2482681) B2482681
theorem B2206827 : Blo 2205435 2206827 := bstep (se 1 (by rfl) ⟨1655120, by rfl⟩ : syracuseStep 2206827 = 3310241) B3310241
theorem B2651189 : Blo 2205435 2651189 := bbase (se 5 (by rfl) ⟨124274, by rfl⟩ : syracuseStep 2651189 = 248549) (by norm_num)
theorem B7069837 : Blo 2205435 7069837 := bstep (se 3 (by rfl) ⟨1325594, by rfl⟩ : syracuseStep 7069837 = 2651189) B2651189
theorem B9426449 : Blo 2205435 9426449 := bstep (se 2 (by rfl) ⟨3534918, by rfl⟩ : syracuseStep 9426449 = 7069837) B7069837
theorem B6284299 : Blo 2205435 6284299 := bstep (se 1 (by rfl) ⟨4713224, by rfl⟩ : syracuseStep 6284299 = 9426449) B9426449
theorem B8379065 : Blo 2205435 8379065 := bstep (se 2 (by rfl) ⟨3142149, by rfl⟩ : syracuseStep 8379065 = 6284299) B6284299
theorem B5586043 : Blo 2205435 5586043 := bstep (se 1 (by rfl) ⟨4189532, by rfl⟩ : syracuseStep 5586043 = 8379065) B8379065
theorem B7448057 : Blo 2205435 7448057 := bstep (se 2 (by rfl) ⟨2793021, by rfl⟩ : syracuseStep 7448057 = 5586043) B5586043
theorem B4965371 : Blo 2205435 4965371 := bstep (se 1 (by rfl) ⟨3724028, by rfl⟩ : syracuseStep 4965371 = 7448057) B7448057
theorem B3310247 : Blo 2205435 3310247 := bstep (se 1 (by rfl) ⟨2482685, by rfl⟩ : syracuseStep 3310247 = 4965371) B4965371
theorem B2206831 : Blo 2205435 2206831 := bstep (se 1 (by rfl) ⟨1655123, by rfl⟩ : syracuseStep 2206831 = 3310247) B3310247
theorem B3310253 : Blo 2205435 3310253 := bbase (se 3 (by rfl) ⟨620672, by rfl⟩ : syracuseStep 3310253 = 1241345) (by norm_num)
theorem B2206835 : Blo 2205435 2206835 := bstep (se 1 (by rfl) ⟨1655126, by rfl⟩ : syracuseStep 2206835 = 3310253) B3310253
theorem B4965389 : Blo 2205435 4965389 := bbase (se 3 (by rfl) ⟨931010, by rfl⟩ : syracuseStep 4965389 = 1862021) (by norm_num)
theorem B3310259 : Blo 2205435 3310259 := bstep (se 1 (by rfl) ⟨2482694, by rfl⟩ : syracuseStep 3310259 = 4965389) B4965389
theorem B2206839 : Blo 2205435 2206839 := bstep (se 1 (by rfl) ⟨1655129, by rfl⟩ : syracuseStep 2206839 = 3310259) B3310259
theorem B2793037 : Blo 2205435 2793037 := bbase (se 3 (by rfl) ⟨523694, by rfl⟩ : syracuseStep 2793037 = 1047389) (by norm_num)
theorem B3724049 : Blo 2205435 3724049 := bstep (se 2 (by rfl) ⟨1396518, by rfl⟩ : syracuseStep 3724049 = 2793037) B2793037
theorem B2482699 : Blo 2205435 2482699 := bstep (se 1 (by rfl) ⟨1862024, by rfl⟩ : syracuseStep 2482699 = 3724049) B3724049
theorem B3310265 : Blo 2205435 3310265 := bstep (se 2 (by rfl) ⟨1241349, by rfl⟩ : syracuseStep 3310265 = 2482699) B2482699
theorem B2206843 : Blo 2205435 2206843 := bstep (se 1 (by rfl) ⟨1655132, by rfl⟩ : syracuseStep 2206843 = 3310265) B3310265
theorem B6370085 : Blo 2205435 6370085 := bbase (se 4 (by rfl) ⟨597195, by rfl⟩ : syracuseStep 6370085 = 1194391) (by norm_num)
theorem B4246723 : Blo 2205435 4246723 := bstep (se 1 (by rfl) ⟨3185042, by rfl⟩ : syracuseStep 4246723 = 6370085) B6370085
theorem B5662297 : Blo 2205435 5662297 := bstep (se 2 (by rfl) ⟨2123361, by rfl⟩ : syracuseStep 5662297 = 4246723) B4246723
theorem B7549729 : Blo 2205435 7549729 := bstep (se 2 (by rfl) ⟨2831148, by rfl⟩ : syracuseStep 7549729 = 5662297) B5662297
theorem B161060885 : Blo 2205435 161060885 := bstep (se 6 (by rfl) ⟨3774864, by rfl⟩ : syracuseStep 161060885 = 7549729) B7549729
theorem B107373923 : Blo 2205435 107373923 := bstep (se 1 (by rfl) ⟨80530442, by rfl⟩ : syracuseStep 107373923 = 161060885) B161060885
theorem B71582615 : Blo 2205435 71582615 := bstep (se 1 (by rfl) ⟨53686961, by rfl⟩ : syracuseStep 71582615 = 107373923) B107373923
theorem B47721743 : Blo 2205435 47721743 := bstep (se 1 (by rfl) ⟨35791307, by rfl⟩ : syracuseStep 47721743 = 71582615) B71582615
theorem B31814495 : Blo 2205435 31814495 := bstep (se 1 (by rfl) ⟨23860871, by rfl⟩ : syracuseStep 31814495 = 47721743) B47721743
theorem B21209663 : Blo 2205435 21209663 := bstep (se 1 (by rfl) ⟨15907247, by rfl⟩ : syracuseStep 21209663 = 31814495) B31814495
theorem B14139775 : Blo 2205435 14139775 := bstep (se 1 (by rfl) ⟨10604831, by rfl⟩ : syracuseStep 14139775 = 21209663) B21209663
theorem B18853033 : Blo 2205435 18853033 := bstep (se 2 (by rfl) ⟨7069887, by rfl⟩ : syracuseStep 18853033 = 14139775) B14139775
theorem B25137377 : Blo 2205435 25137377 := bstep (se 2 (by rfl) ⟨9426516, by rfl⟩ : syracuseStep 25137377 = 18853033) B18853033
theorem B16758251 : Blo 2205435 16758251 := bstep (se 1 (by rfl) ⟨12568688, by rfl⟩ : syracuseStep 16758251 = 25137377) B25137377
theorem B11172167 : Blo 2205435 11172167 := bstep (se 1 (by rfl) ⟨8379125, by rfl⟩ : syracuseStep 11172167 = 16758251) B16758251
theorem B7448111 : Blo 2205435 7448111 := bstep (se 1 (by rfl) ⟨5586083, by rfl⟩ : syracuseStep 7448111 = 11172167) B11172167
theorem B4965407 : Blo 2205435 4965407 := bstep (se 1 (by rfl) ⟨3724055, by rfl⟩ : syracuseStep 4965407 = 7448111) B7448111
theorem B3310271 : Blo 2205435 3310271 := bstep (se 1 (by rfl) ⟨2482703, by rfl⟩ : syracuseStep 3310271 = 4965407) B4965407
theorem B2206847 : Blo 2205435 2206847 := bstep (se 1 (by rfl) ⟨1655135, by rfl⟩ : syracuseStep 2206847 = 3310271) B3310271
theorem B3310277 : Blo 2205435 3310277 := bbase (se 4 (by rfl) ⟨310338, by rfl⟩ : syracuseStep 3310277 = 620677) (by norm_num)
theorem B2206851 : Blo 2205435 2206851 := bstep (se 1 (by rfl) ⟨1655138, by rfl⟩ : syracuseStep 2206851 = 3310277) B3310277
theorem B3724069 : Blo 2205435 3724069 := bbase (se 4 (by rfl) ⟨349131, by rfl⟩ : syracuseStep 3724069 = 698263) (by norm_num)
theorem B4965425 : Blo 2205435 4965425 := bstep (se 2 (by rfl) ⟨1862034, by rfl⟩ : syracuseStep 4965425 = 3724069) B3724069
theorem B3310283 : Blo 2205435 3310283 := bstep (se 1 (by rfl) ⟨2482712, by rfl⟩ : syracuseStep 3310283 = 4965425) B4965425
theorem B2206855 : Blo 2205435 2206855 := bstep (se 1 (by rfl) ⟨1655141, by rfl⟩ : syracuseStep 2206855 = 3310283) B3310283
theorem B2482717 : Blo 2205435 2482717 := bbase (se 3 (by rfl) ⟨465509, by rfl⟩ : syracuseStep 2482717 = 931019) (by norm_num)
theorem B3310289 : Blo 2205435 3310289 := bstep (se 2 (by rfl) ⟨1241358, by rfl⟩ : syracuseStep 3310289 = 2482717) B2482717
theorem B2206859 : Blo 2205435 2206859 := bstep (se 1 (by rfl) ⟨1655144, by rfl⟩ : syracuseStep 2206859 = 3310289) B3310289
theorem B7448165 : Blo 2205435 7448165 := bbase (se 4 (by rfl) ⟨698265, by rfl⟩ : syracuseStep 7448165 = 1396531) (by norm_num)
theorem B4965443 : Blo 2205435 4965443 := bstep (se 1 (by rfl) ⟨3724082, by rfl⟩ : syracuseStep 4965443 = 7448165) B7448165
theorem B3310295 : Blo 2205435 3310295 := bstep (se 1 (by rfl) ⟨2482721, by rfl⟩ : syracuseStep 3310295 = 4965443) B4965443
theorem B2206863 : Blo 2205435 2206863 := bstep (se 1 (by rfl) ⟨1655147, by rfl⟩ : syracuseStep 2206863 = 3310295) B3310295
theorem B3310301 : Blo 2205435 3310301 := bbase (se 3 (by rfl) ⟨620681, by rfl⟩ : syracuseStep 3310301 = 1241363) (by norm_num)
theorem B2206867 : Blo 2205435 2206867 := bstep (se 1 (by rfl) ⟨1655150, by rfl⟩ : syracuseStep 2206867 = 3310301) B3310301
theorem B4965461 : Blo 2205435 4965461 := bbase (se 8 (by rfl) ⟨29094, by rfl⟩ : syracuseStep 4965461 = 58189) (by norm_num)
theorem B3310307 : Blo 2205435 3310307 := bstep (se 1 (by rfl) ⟨2482730, by rfl⟩ : syracuseStep 3310307 = 4965461) B4965461
theorem B2206871 : Blo 2205435 2206871 := bstep (se 1 (by rfl) ⟨1655153, by rfl⟩ : syracuseStep 2206871 = 3310307) B3310307
theorem B5374829 : Blo 2205435 5374829 := bbase (se 3 (by rfl) ⟨1007780, by rfl⟩ : syracuseStep 5374829 = 2015561) (by norm_num)
theorem B14332877 : Blo 2205435 14332877 := bstep (se 3 (by rfl) ⟨2687414, by rfl⟩ : syracuseStep 14332877 = 5374829) B5374829
theorem B9555251 : Blo 2205435 9555251 := bstep (se 1 (by rfl) ⟨7166438, by rfl⟩ : syracuseStep 9555251 = 14332877) B14332877
theorem B25480669 : Blo 2205435 25480669 := bstep (se 3 (by rfl) ⟨4777625, by rfl⟩ : syracuseStep 25480669 = 9555251) B9555251
theorem B33974225 : Blo 2205435 33974225 := bstep (se 2 (by rfl) ⟨12740334, by rfl⟩ : syracuseStep 33974225 = 25480669) B25480669
theorem B22649483 : Blo 2205435 22649483 := bstep (se 1 (by rfl) ⟨16987112, by rfl⟩ : syracuseStep 22649483 = 33974225) B33974225
theorem B60398621 : Blo 2205435 60398621 := bstep (se 3 (by rfl) ⟨11324741, by rfl⟩ : syracuseStep 60398621 = 22649483) B22649483
theorem B40265747 : Blo 2205435 40265747 := bstep (se 1 (by rfl) ⟨30199310, by rfl⟩ : syracuseStep 40265747 = 60398621) B60398621
theorem B26843831 : Blo 2205435 26843831 := bstep (se 1 (by rfl) ⟨20132873, by rfl⟩ : syracuseStep 26843831 = 40265747) B40265747
theorem B17895887 : Blo 2205435 17895887 := bstep (se 1 (by rfl) ⟨13421915, by rfl⟩ : syracuseStep 17895887 = 26843831) B26843831
theorem B11930591 : Blo 2205435 11930591 := bstep (se 1 (by rfl) ⟨8947943, by rfl⟩ : syracuseStep 11930591 = 17895887) B17895887
theorem B7953727 : Blo 2205435 7953727 := bstep (se 1 (by rfl) ⟨5965295, by rfl⟩ : syracuseStep 7953727 = 11930591) B11930591
theorem B10604969 : Blo 2205435 10604969 := bstep (se 2 (by rfl) ⟨3976863, by rfl⟩ : syracuseStep 10604969 = 7953727) B7953727
theorem B7069979 : Blo 2205435 7069979 := bstep (se 1 (by rfl) ⟨5302484, by rfl⟩ : syracuseStep 7069979 = 10604969) B10604969
theorem B4713319 : Blo 2205435 4713319 := bstep (se 1 (by rfl) ⟨3534989, by rfl⟩ : syracuseStep 4713319 = 7069979) B7069979
theorem B6284425 : Blo 2205435 6284425 := bstep (se 2 (by rfl) ⟨2356659, by rfl⟩ : syracuseStep 6284425 = 4713319) B4713319
theorem B8379233 : Blo 2205435 8379233 := bstep (se 2 (by rfl) ⟨3142212, by rfl⟩ : syracuseStep 8379233 = 6284425) B6284425
theorem B5586155 : Blo 2205435 5586155 := bstep (se 1 (by rfl) ⟨4189616, by rfl⟩ : syracuseStep 5586155 = 8379233) B8379233
theorem B3724103 : Blo 2205435 3724103 := bstep (se 1 (by rfl) ⟨2793077, by rfl⟩ : syracuseStep 3724103 = 5586155) B5586155
theorem B2482735 : Blo 2205435 2482735 := bstep (se 1 (by rfl) ⟨1862051, by rfl⟩ : syracuseStep 2482735 = 3724103) B3724103
theorem B3310313 : Blo 2205435 3310313 := bstep (se 2 (by rfl) ⟨1241367, by rfl⟩ : syracuseStep 3310313 = 2482735) B2482735
theorem B2206875 : Blo 2205435 2206875 := bstep (se 1 (by rfl) ⟨1655156, by rfl⟩ : syracuseStep 2206875 = 3310313) B3310313
theorem B8947957 : Blo 2205435 8947957 := bbase (se 5 (by rfl) ⟨419435, by rfl⟩ : syracuseStep 8947957 = 838871) (by norm_num)
theorem B11930609 : Blo 2205435 11930609 := bstep (se 2 (by rfl) ⟨4473978, by rfl⟩ : syracuseStep 11930609 = 8947957) B8947957
theorem B31814957 : Blo 2205435 31814957 := bstep (se 3 (by rfl) ⟨5965304, by rfl⟩ : syracuseStep 31814957 = 11930609) B11930609
theorem B21209971 : Blo 2205435 21209971 := bstep (se 1 (by rfl) ⟨15907478, by rfl⟩ : syracuseStep 21209971 = 31814957) B31814957
theorem B28279961 : Blo 2205435 28279961 := bstep (se 2 (by rfl) ⟨10604985, by rfl⟩ : syracuseStep 28279961 = 21209971) B21209971
theorem B18853307 : Blo 2205435 18853307 := bstep (se 1 (by rfl) ⟨14139980, by rfl⟩ : syracuseStep 18853307 = 28279961) B28279961
theorem B12568871 : Blo 2205435 12568871 := bstep (se 1 (by rfl) ⟨9426653, by rfl⟩ : syracuseStep 12568871 = 18853307) B18853307
theorem B8379247 : Blo 2205435 8379247 := bstep (se 1 (by rfl) ⟨6284435, by rfl⟩ : syracuseStep 8379247 = 12568871) B12568871
theorem B11172329 : Blo 2205435 11172329 := bstep (se 2 (by rfl) ⟨4189623, by rfl⟩ : syracuseStep 11172329 = 8379247) B8379247
theorem B7448219 : Blo 2205435 7448219 := bstep (se 1 (by rfl) ⟨5586164, by rfl⟩ : syracuseStep 7448219 = 11172329) B11172329
theorem B4965479 : Blo 2205435 4965479 := bstep (se 1 (by rfl) ⟨3724109, by rfl⟩ : syracuseStep 4965479 = 7448219) B7448219
theorem B3310319 : Blo 2205435 3310319 := bstep (se 1 (by rfl) ⟨2482739, by rfl⟩ : syracuseStep 3310319 = 4965479) B4965479
theorem B2206879 : Blo 2205435 2206879 := bstep (se 1 (by rfl) ⟨1655159, by rfl⟩ : syracuseStep 2206879 = 3310319) B3310319
theorem B3310325 : Blo 2205435 3310325 := bbase (se 5 (by rfl) ⟨155171, by rfl⟩ : syracuseStep 3310325 = 310343) (by norm_num)
theorem B2206883 : Blo 2205435 2206883 := bstep (se 1 (by rfl) ⟨1655162, by rfl⟩ : syracuseStep 2206883 = 3310325) B3310325
theorem B3976885 : Blo 2205435 3976885 := bbase (se 5 (by rfl) ⟨186416, by rfl⟩ : syracuseStep 3976885 = 372833) (by norm_num)
theorem B5302513 : Blo 2205435 5302513 := bstep (se 2 (by rfl) ⟨1988442, by rfl⟩ : syracuseStep 5302513 = 3976885) B3976885
theorem B7070017 : Blo 2205435 7070017 := bstep (se 2 (by rfl) ⟨2651256, by rfl⟩ : syracuseStep 7070017 = 5302513) B5302513
theorem B9426689 : Blo 2205435 9426689 := bstep (se 2 (by rfl) ⟨3535008, by rfl⟩ : syracuseStep 9426689 = 7070017) B7070017
theorem B6284459 : Blo 2205435 6284459 := bstep (se 1 (by rfl) ⟨4713344, by rfl⟩ : syracuseStep 6284459 = 9426689) B9426689
theorem B4189639 : Blo 2205435 4189639 := bstep (se 1 (by rfl) ⟨3142229, by rfl⟩ : syracuseStep 4189639 = 6284459) B6284459
theorem B5586185 : Blo 2205435 5586185 := bstep (se 2 (by rfl) ⟨2094819, by rfl⟩ : syracuseStep 5586185 = 4189639) B4189639
theorem B3724123 : Blo 2205435 3724123 := bstep (se 1 (by rfl) ⟨2793092, by rfl⟩ : syracuseStep 3724123 = 5586185) B5586185
theorem B4965497 : Blo 2205435 4965497 := bstep (se 2 (by rfl) ⟨1862061, by rfl⟩ : syracuseStep 4965497 = 3724123) B3724123
theorem B3310331 : Blo 2205435 3310331 := bstep (se 1 (by rfl) ⟨2482748, by rfl⟩ : syracuseStep 3310331 = 4965497) B4965497
theorem B2206887 : Blo 2205435 2206887 := bstep (se 1 (by rfl) ⟨1655165, by rfl⟩ : syracuseStep 2206887 = 3310331) B3310331
theorem B2482753 : Blo 2205435 2482753 := bbase (se 2 (by rfl) ⟨931032, by rfl⟩ : syracuseStep 2482753 = 1862065) (by norm_num)
theorem B3310337 : Blo 2205435 3310337 := bstep (se 2 (by rfl) ⟨1241376, by rfl⟩ : syracuseStep 3310337 = 2482753) B2482753
theorem B2206891 : Blo 2205435 2206891 := bstep (se 1 (by rfl) ⟨1655168, by rfl⟩ : syracuseStep 2206891 = 3310337) B3310337
theorem B5586205 : Blo 2205435 5586205 := bbase (se 3 (by rfl) ⟨1047413, by rfl⟩ : syracuseStep 5586205 = 2094827) (by norm_num)
theorem B7448273 : Blo 2205435 7448273 := bstep (se 2 (by rfl) ⟨2793102, by rfl⟩ : syracuseStep 7448273 = 5586205) B5586205
theorem B4965515 : Blo 2205435 4965515 := bstep (se 1 (by rfl) ⟨3724136, by rfl⟩ : syracuseStep 4965515 = 7448273) B7448273
theorem B3310343 : Blo 2205435 3310343 := bstep (se 1 (by rfl) ⟨2482757, by rfl⟩ : syracuseStep 3310343 = 4965515) B4965515
theorem B2206895 : Blo 2205435 2206895 := bstep (se 1 (by rfl) ⟨1655171, by rfl⟩ : syracuseStep 2206895 = 3310343) B3310343
theorem B3310349 : Blo 2205435 3310349 := bbase (se 3 (by rfl) ⟨620690, by rfl⟩ : syracuseStep 3310349 = 1241381) (by norm_num)
theorem B2206899 : Blo 2205435 2206899 := bstep (se 1 (by rfl) ⟨1655174, by rfl⟩ : syracuseStep 2206899 = 3310349) B3310349
theorem B4965533 : Blo 2205435 4965533 := bbase (se 3 (by rfl) ⟨931037, by rfl⟩ : syracuseStep 4965533 = 1862075) (by norm_num)
theorem B3310355 : Blo 2205435 3310355 := bstep (se 1 (by rfl) ⟨2482766, by rfl⟩ : syracuseStep 3310355 = 4965533) B4965533
theorem B2206903 : Blo 2205435 2206903 := bstep (se 1 (by rfl) ⟨1655177, by rfl⟩ : syracuseStep 2206903 = 3310355) B3310355
theorem B3724157 : Blo 2205435 3724157 := bbase (se 3 (by rfl) ⟨698279, by rfl⟩ : syracuseStep 3724157 = 1396559) (by norm_num)
theorem B2482771 : Blo 2205435 2482771 := bstep (se 1 (by rfl) ⟨1862078, by rfl⟩ : syracuseStep 2482771 = 3724157) B3724157
theorem B3310361 : Blo 2205435 3310361 := bstep (se 2 (by rfl) ⟨1241385, by rfl⟩ : syracuseStep 3310361 = 2482771) B2482771
theorem B2206907 : Blo 2205435 2206907 := bstep (se 1 (by rfl) ⟨1655180, by rfl⟩ : syracuseStep 2206907 = 3310361) B3310361
theorem B2651285 : Blo 2205435 2651285 := bbase (se 6 (by rfl) ⟨62139, by rfl⟩ : syracuseStep 2651285 = 124279) (by norm_num)
theorem B7070093 : Blo 2205435 7070093 := bstep (se 3 (by rfl) ⟨1325642, by rfl⟩ : syracuseStep 7070093 = 2651285) B2651285
theorem B4713395 : Blo 2205435 4713395 := bstep (se 1 (by rfl) ⟨3535046, by rfl⟩ : syracuseStep 4713395 = 7070093) B7070093
theorem B12569053 : Blo 2205435 12569053 := bstep (se 3 (by rfl) ⟨2356697, by rfl⟩ : syracuseStep 12569053 = 4713395) B4713395
theorem B16758737 : Blo 2205435 16758737 := bstep (se 2 (by rfl) ⟨6284526, by rfl⟩ : syracuseStep 16758737 = 12569053) B12569053
theorem B11172491 : Blo 2205435 11172491 := bstep (se 1 (by rfl) ⟨8379368, by rfl⟩ : syracuseStep 11172491 = 16758737) B16758737
theorem B7448327 : Blo 2205435 7448327 := bstep (se 1 (by rfl) ⟨5586245, by rfl⟩ : syracuseStep 7448327 = 11172491) B11172491
theorem B4965551 : Blo 2205435 4965551 := bstep (se 1 (by rfl) ⟨3724163, by rfl⟩ : syracuseStep 4965551 = 7448327) B7448327
theorem B3310367 : Blo 2205435 3310367 := bstep (se 1 (by rfl) ⟨2482775, by rfl⟩ : syracuseStep 3310367 = 4965551) B4965551
theorem B2206911 : Blo 2205435 2206911 := bstep (se 1 (by rfl) ⟨1655183, by rfl⟩ : syracuseStep 2206911 = 3310367) B3310367
theorem B3310373 : Blo 2205435 3310373 := bbase (se 4 (by rfl) ⟨310347, by rfl⟩ : syracuseStep 3310373 = 620695) (by norm_num)
theorem B2206915 : Blo 2205435 2206915 := bstep (se 1 (by rfl) ⟨1655186, by rfl⟩ : syracuseStep 2206915 = 3310373) B3310373
theorem B2793133 : Blo 2205435 2793133 := bbase (se 3 (by rfl) ⟨523712, by rfl⟩ : syracuseStep 2793133 = 1047425) (by norm_num)
theorem B3724177 : Blo 2205435 3724177 := bstep (se 2 (by rfl) ⟨1396566, by rfl⟩ : syracuseStep 3724177 = 2793133) B2793133
theorem B4965569 : Blo 2205435 4965569 := bstep (se 2 (by rfl) ⟨1862088, by rfl⟩ : syracuseStep 4965569 = 3724177) B3724177
theorem B3310379 : Blo 2205435 3310379 := bstep (se 1 (by rfl) ⟨2482784, by rfl⟩ : syracuseStep 3310379 = 4965569) B4965569
theorem B2206919 : Blo 2205435 2206919 := bstep (se 1 (by rfl) ⟨1655189, by rfl⟩ : syracuseStep 2206919 = 3310379) B3310379
theorem B2482789 : Blo 2205435 2482789 := bbase (se 4 (by rfl) ⟨232761, by rfl⟩ : syracuseStep 2482789 = 465523) (by norm_num)
theorem B3310385 : Blo 2205435 3310385 := bstep (se 2 (by rfl) ⟨1241394, by rfl⟩ : syracuseStep 3310385 = 2482789) B2482789
theorem B2206923 : Blo 2205435 2206923 := bstep (se 1 (by rfl) ⟨1655192, by rfl⟩ : syracuseStep 2206923 = 3310385) B3310385
theorem B2651305 : Blo 2205435 2651305 := bbase (se 2 (by rfl) ⟨994239, by rfl⟩ : syracuseStep 2651305 = 1988479) (by norm_num)
theorem B3535073 : Blo 2205435 3535073 := bstep (se 2 (by rfl) ⟨1325652, by rfl⟩ : syracuseStep 3535073 = 2651305) B2651305
theorem B2356715 : Blo 2205435 2356715 := bstep (se 1 (by rfl) ⟨1767536, by rfl⟩ : syracuseStep 2356715 = 3535073) B3535073
theorem B6284573 : Blo 2205435 6284573 := bstep (se 3 (by rfl) ⟨1178357, by rfl⟩ : syracuseStep 6284573 = 2356715) B2356715
theorem B4189715 : Blo 2205435 4189715 := bstep (se 1 (by rfl) ⟨3142286, by rfl⟩ : syracuseStep 4189715 = 6284573) B6284573
theorem B2793143 : Blo 2205435 2793143 := bstep (se 1 (by rfl) ⟨2094857, by rfl⟩ : syracuseStep 2793143 = 4189715) B4189715
theorem B7448381 : Blo 2205435 7448381 := bstep (se 3 (by rfl) ⟨1396571, by rfl⟩ : syracuseStep 7448381 = 2793143) B2793143
theorem B4965587 : Blo 2205435 4965587 := bstep (se 1 (by rfl) ⟨3724190, by rfl⟩ : syracuseStep 4965587 = 7448381) B7448381
theorem B3310391 : Blo 2205435 3310391 := bstep (se 1 (by rfl) ⟨2482793, by rfl⟩ : syracuseStep 3310391 = 4965587) B4965587
theorem B2206927 : Blo 2205435 2206927 := bstep (se 1 (by rfl) ⟨1655195, by rfl⟩ : syracuseStep 2206927 = 3310391) B3310391
theorem B3310397 : Blo 2205435 3310397 := bbase (se 3 (by rfl) ⟨620699, by rfl⟩ : syracuseStep 3310397 = 1241399) (by norm_num)
theorem B2206931 : Blo 2205435 2206931 := bstep (se 1 (by rfl) ⟨1655198, by rfl⟩ : syracuseStep 2206931 = 3310397) B3310397
theorem B4965605 : Blo 2205435 4965605 := bbase (se 4 (by rfl) ⟨465525, by rfl⟩ : syracuseStep 4965605 = 931051) (by norm_num)
theorem B3310403 : Blo 2205435 3310403 := bstep (se 1 (by rfl) ⟨2482802, by rfl⟩ : syracuseStep 3310403 = 4965605) B4965605
theorem B2206935 : Blo 2205435 2206935 := bstep (se 1 (by rfl) ⟨1655201, by rfl⟩ : syracuseStep 2206935 = 3310403) B3310403
theorem B5586317 : Blo 2205435 5586317 := bbase (se 3 (by rfl) ⟨1047434, by rfl⟩ : syracuseStep 5586317 = 2094869) (by norm_num)
theorem B3724211 : Blo 2205435 3724211 := bstep (se 1 (by rfl) ⟨2793158, by rfl⟩ : syracuseStep 3724211 = 5586317) B5586317
theorem B2482807 : Blo 2205435 2482807 := bstep (se 1 (by rfl) ⟨1862105, by rfl⟩ : syracuseStep 2482807 = 3724211) B3724211
theorem B3310409 : Blo 2205435 3310409 := bstep (se 2 (by rfl) ⟨1241403, by rfl⟩ : syracuseStep 3310409 = 2482807) B2482807
theorem B2206939 : Blo 2205435 2206939 := bstep (se 1 (by rfl) ⟨1655204, by rfl⟩ : syracuseStep 2206939 = 3310409) B3310409
theorem B3142309 : Blo 2205435 3142309 := bbase (se 4 (by rfl) ⟨294591, by rfl⟩ : syracuseStep 3142309 = 589183) (by norm_num)
theorem B4189745 : Blo 2205435 4189745 := bstep (se 2 (by rfl) ⟨1571154, by rfl⟩ : syracuseStep 4189745 = 3142309) B3142309
theorem B11172653 : Blo 2205435 11172653 := bstep (se 3 (by rfl) ⟨2094872, by rfl⟩ : syracuseStep 11172653 = 4189745) B4189745
theorem B7448435 : Blo 2205435 7448435 := bstep (se 1 (by rfl) ⟨5586326, by rfl⟩ : syracuseStep 7448435 = 11172653) B11172653
theorem B4965623 : Blo 2205435 4965623 := bstep (se 1 (by rfl) ⟨3724217, by rfl⟩ : syracuseStep 4965623 = 7448435) B7448435
theorem B3310415 : Blo 2205435 3310415 := bstep (se 1 (by rfl) ⟨2482811, by rfl⟩ : syracuseStep 3310415 = 4965623) B4965623
theorem B2206943 : Blo 2205435 2206943 := bstep (se 1 (by rfl) ⟨1655207, by rfl⟩ : syracuseStep 2206943 = 3310415) B3310415
theorem B3310421 : Blo 2205435 3310421 := bbase (se 9 (by rfl) ⟨9698, by rfl⟩ : syracuseStep 3310421 = 19397) (by norm_num)
theorem B2206947 : Blo 2205435 2206947 := bstep (se 1 (by rfl) ⟨1655210, by rfl⟩ : syracuseStep 2206947 = 3310421) B3310421
theorem B3775045 : Blo 2205435 3775045 := bbase (se 4 (by rfl) ⟨353910, by rfl⟩ : syracuseStep 3775045 = 707821) (by norm_num)
theorem B5033393 : Blo 2205435 5033393 := bstep (se 2 (by rfl) ⟨1887522, by rfl⟩ : syracuseStep 5033393 = 3775045) B3775045
theorem B3355595 : Blo 2205435 3355595 := bstep (se 1 (by rfl) ⟨2516696, by rfl⟩ : syracuseStep 3355595 = 5033393) B5033393
theorem B2237063 : Blo 2205435 2237063 := bstep (se 1 (by rfl) ⟨1677797, by rfl⟩ : syracuseStep 2237063 = 3355595) B3355595
theorem B5965501 : Blo 2205435 5965501 := bstep (se 3 (by rfl) ⟨1118531, by rfl⟩ : syracuseStep 5965501 = 2237063) B2237063
theorem B7954001 : Blo 2205435 7954001 := bstep (se 2 (by rfl) ⟨2982750, by rfl⟩ : syracuseStep 7954001 = 5965501) B5965501
theorem B5302667 : Blo 2205435 5302667 := bstep (se 1 (by rfl) ⟨3977000, by rfl⟩ : syracuseStep 5302667 = 7954001) B7954001
theorem B3535111 : Blo 2205435 3535111 := bstep (se 1 (by rfl) ⟨2651333, by rfl⟩ : syracuseStep 3535111 = 5302667) B5302667
theorem B4713481 : Blo 2205435 4713481 := bstep (se 2 (by rfl) ⟨1767555, by rfl⟩ : syracuseStep 4713481 = 3535111) B3535111
theorem B6284641 : Blo 2205435 6284641 := bstep (se 2 (by rfl) ⟨2356740, by rfl⟩ : syracuseStep 6284641 = 4713481) B4713481
theorem B8379521 : Blo 2205435 8379521 := bstep (se 2 (by rfl) ⟨3142320, by rfl⟩ : syracuseStep 8379521 = 6284641) B6284641
theorem B5586347 : Blo 2205435 5586347 := bstep (se 1 (by rfl) ⟨4189760, by rfl⟩ : syracuseStep 5586347 = 8379521) B8379521
theorem B3724231 : Blo 2205435 3724231 := bstep (se 1 (by rfl) ⟨2793173, by rfl⟩ : syracuseStep 3724231 = 5586347) B5586347
theorem B4965641 : Blo 2205435 4965641 := bstep (se 2 (by rfl) ⟨1862115, by rfl⟩ : syracuseStep 4965641 = 3724231) B3724231
theorem B3310427 : Blo 2205435 3310427 := bstep (se 1 (by rfl) ⟨2482820, by rfl⟩ : syracuseStep 3310427 = 4965641) B4965641
theorem B2206951 : Blo 2205435 2206951 := bstep (se 1 (by rfl) ⟨1655213, by rfl⟩ : syracuseStep 2206951 = 3310427) B3310427
theorem B2482825 : Blo 2205435 2482825 := bbase (se 2 (by rfl) ⟨931059, by rfl⟩ : syracuseStep 2482825 = 1862119) (by norm_num)
theorem B3310433 : Blo 2205435 3310433 := bstep (se 2 (by rfl) ⟨1241412, by rfl⟩ : syracuseStep 3310433 = 2482825) B2482825
theorem B2206955 : Blo 2205435 2206955 := bstep (se 1 (by rfl) ⟨1655216, by rfl⟩ : syracuseStep 2206955 = 3310433) B3310433
theorem B8493877 : Blo 2205435 8493877 := bbase (se 5 (by rfl) ⟨398150, by rfl⟩ : syracuseStep 8493877 = 796301) (by norm_num)
theorem B11325169 : Blo 2205435 11325169 := bstep (se 2 (by rfl) ⟨4246938, by rfl⟩ : syracuseStep 11325169 = 8493877) B8493877
theorem B15100225 : Blo 2205435 15100225 := bstep (se 2 (by rfl) ⟨5662584, by rfl⟩ : syracuseStep 15100225 = 11325169) B11325169
theorem B80534533 : Blo 2205435 80534533 := bstep (se 4 (by rfl) ⟨7550112, by rfl⟩ : syracuseStep 80534533 = 15100225) B15100225
theorem B107379377 : Blo 2205435 107379377 := bstep (se 2 (by rfl) ⟨40267266, by rfl⟩ : syracuseStep 107379377 = 80534533) B80534533
theorem B71586251 : Blo 2205435 71586251 := bstep (se 1 (by rfl) ⟨53689688, by rfl⟩ : syracuseStep 71586251 = 107379377) B107379377
theorem B47724167 : Blo 2205435 47724167 := bstep (se 1 (by rfl) ⟨35793125, by rfl⟩ : syracuseStep 47724167 = 71586251) B71586251
theorem B31816111 : Blo 2205435 31816111 := bstep (se 1 (by rfl) ⟨23862083, by rfl⟩ : syracuseStep 31816111 = 47724167) B47724167
theorem B42421481 : Blo 2205435 42421481 := bstep (se 2 (by rfl) ⟨15908055, by rfl⟩ : syracuseStep 42421481 = 31816111) B31816111
theorem B28280987 : Blo 2205435 28280987 := bstep (se 1 (by rfl) ⟨21210740, by rfl⟩ : syracuseStep 28280987 = 42421481) B42421481
theorem B18853991 : Blo 2205435 18853991 := bstep (se 1 (by rfl) ⟨14140493, by rfl⟩ : syracuseStep 18853991 = 28280987) B28280987
theorem B12569327 : Blo 2205435 12569327 := bstep (se 1 (by rfl) ⟨9426995, by rfl⟩ : syracuseStep 12569327 = 18853991) B18853991
theorem B8379551 : Blo 2205435 8379551 := bstep (se 1 (by rfl) ⟨6284663, by rfl⟩ : syracuseStep 8379551 = 12569327) B12569327
theorem B5586367 : Blo 2205435 5586367 := bstep (se 1 (by rfl) ⟨4189775, by rfl⟩ : syracuseStep 5586367 = 8379551) B8379551
theorem B7448489 : Blo 2205435 7448489 := bstep (se 2 (by rfl) ⟨2793183, by rfl⟩ : syracuseStep 7448489 = 5586367) B5586367
theorem B4965659 : Blo 2205435 4965659 := bstep (se 1 (by rfl) ⟨3724244, by rfl⟩ : syracuseStep 4965659 = 7448489) B7448489
theorem B3310439 : Blo 2205435 3310439 := bstep (se 1 (by rfl) ⟨2482829, by rfl⟩ : syracuseStep 3310439 = 4965659) B4965659
theorem B2206959 : Blo 2205435 2206959 := bstep (se 1 (by rfl) ⟨1655219, by rfl⟩ : syracuseStep 2206959 = 3310439) B3310439
theorem B3310445 : Blo 2205435 3310445 := bbase (se 3 (by rfl) ⟨620708, by rfl⟩ : syracuseStep 3310445 = 1241417) (by norm_num)
theorem B2206963 : Blo 2205435 2206963 := bstep (se 1 (by rfl) ⟨1655222, by rfl⟩ : syracuseStep 2206963 = 3310445) B3310445
theorem B4965677 : Blo 2205435 4965677 := bbase (se 3 (by rfl) ⟨931064, by rfl⟩ : syracuseStep 4965677 = 1862129) (by norm_num)
theorem B3310451 : Blo 2205435 3310451 := bstep (se 1 (by rfl) ⟨2482838, by rfl⟩ : syracuseStep 3310451 = 4965677) B4965677
theorem B2206967 : Blo 2205435 2206967 := bstep (se 1 (by rfl) ⟨1655225, by rfl⟩ : syracuseStep 2206967 = 3310451) B3310451
theorem B6046949 : Blo 2205435 6046949 := bbase (se 4 (by rfl) ⟨566901, by rfl⟩ : syracuseStep 6046949 = 1133803) (by norm_num)
theorem B4031299 : Blo 2205435 4031299 := bstep (se 1 (by rfl) ⟨3023474, by rfl⟩ : syracuseStep 4031299 = 6046949) B6046949
theorem B21500261 : Blo 2205435 21500261 := bstep (se 4 (by rfl) ⟨2015649, by rfl⟩ : syracuseStep 21500261 = 4031299) B4031299
theorem B14333507 : Blo 2205435 14333507 := bstep (se 1 (by rfl) ⟨10750130, by rfl⟩ : syracuseStep 14333507 = 21500261) B21500261
theorem B9555671 : Blo 2205435 9555671 := bstep (se 1 (by rfl) ⟨7166753, by rfl⟩ : syracuseStep 9555671 = 14333507) B14333507
theorem B6370447 : Blo 2205435 6370447 := bstep (se 1 (by rfl) ⟨4777835, by rfl⟩ : syracuseStep 6370447 = 9555671) B9555671
theorem B8493929 : Blo 2205435 8493929 := bstep (se 2 (by rfl) ⟨3185223, by rfl⟩ : syracuseStep 8493929 = 6370447) B6370447
theorem B5662619 : Blo 2205435 5662619 := bstep (se 1 (by rfl) ⟨4246964, by rfl⟩ : syracuseStep 5662619 = 8493929) B8493929
theorem B3775079 : Blo 2205435 3775079 := bstep (se 1 (by rfl) ⟨2831309, by rfl⟩ : syracuseStep 3775079 = 5662619) B5662619
theorem B2516719 : Blo 2205435 2516719 := bstep (se 1 (by rfl) ⟨1887539, by rfl⟩ : syracuseStep 2516719 = 3775079) B3775079
theorem B3355625 : Blo 2205435 3355625 := bstep (se 2 (by rfl) ⟨1258359, by rfl⟩ : syracuseStep 3355625 = 2516719) B2516719
theorem B8948333 : Blo 2205435 8948333 := bstep (se 3 (by rfl) ⟨1677812, by rfl⟩ : syracuseStep 8948333 = 3355625) B3355625
theorem B23862221 : Blo 2205435 23862221 := bstep (se 3 (by rfl) ⟨4474166, by rfl⟩ : syracuseStep 23862221 = 8948333) B8948333
theorem B15908147 : Blo 2205435 15908147 := bstep (se 1 (by rfl) ⟨11931110, by rfl⟩ : syracuseStep 15908147 = 23862221) B23862221
theorem B10605431 : Blo 2205435 10605431 := bstep (se 1 (by rfl) ⟨7954073, by rfl⟩ : syracuseStep 10605431 = 15908147) B15908147
theorem B7070287 : Blo 2205435 7070287 := bstep (se 1 (by rfl) ⟨5302715, by rfl⟩ : syracuseStep 7070287 = 10605431) B10605431
theorem B9427049 : Blo 2205435 9427049 := bstep (se 2 (by rfl) ⟨3535143, by rfl⟩ : syracuseStep 9427049 = 7070287) B7070287
theorem B6284699 : Blo 2205435 6284699 := bstep (se 1 (by rfl) ⟨4713524, by rfl⟩ : syracuseStep 6284699 = 9427049) B9427049
theorem B4189799 : Blo 2205435 4189799 := bstep (se 1 (by rfl) ⟨3142349, by rfl⟩ : syracuseStep 4189799 = 6284699) B6284699
theorem B2793199 : Blo 2205435 2793199 := bstep (se 1 (by rfl) ⟨2094899, by rfl⟩ : syracuseStep 2793199 = 4189799) B4189799
theorem B3724265 : Blo 2205435 3724265 := bstep (se 2 (by rfl) ⟨1396599, by rfl⟩ : syracuseStep 3724265 = 2793199) B2793199
theorem B2482843 : Blo 2205435 2482843 := bstep (se 1 (by rfl) ⟨1862132, by rfl⟩ : syracuseStep 2482843 = 3724265) B3724265
theorem B3310457 : Blo 2205435 3310457 := bstep (se 2 (by rfl) ⟨1241421, by rfl⟩ : syracuseStep 3310457 = 2482843) B2482843
theorem B2206971 : Blo 2205435 2206971 := bstep (se 1 (by rfl) ⟨1655228, by rfl⟩ : syracuseStep 2206971 = 3310457) B3310457
theorem B7954085 : Blo 2205435 7954085 := bbase (se 4 (by rfl) ⟨745695, by rfl⟩ : syracuseStep 7954085 = 1491391) (by norm_num)
theorem B21210893 : Blo 2205435 21210893 := bstep (se 3 (by rfl) ⟨3977042, by rfl⟩ : syracuseStep 21210893 = 7954085) B7954085
theorem B14140595 : Blo 2205435 14140595 := bstep (se 1 (by rfl) ⟨10605446, by rfl⟩ : syracuseStep 14140595 = 21210893) B21210893
theorem B37708253 : Blo 2205435 37708253 := bstep (se 3 (by rfl) ⟨7070297, by rfl⟩ : syracuseStep 37708253 = 14140595) B14140595
theorem B25138835 : Blo 2205435 25138835 := bstep (se 1 (by rfl) ⟨18854126, by rfl⟩ : syracuseStep 25138835 = 37708253) B37708253
theorem B16759223 : Blo 2205435 16759223 := bstep (se 1 (by rfl) ⟨12569417, by rfl⟩ : syracuseStep 16759223 = 25138835) B25138835
theorem B11172815 : Blo 2205435 11172815 := bstep (se 1 (by rfl) ⟨8379611, by rfl⟩ : syracuseStep 11172815 = 16759223) B16759223
theorem B7448543 : Blo 2205435 7448543 := bstep (se 1 (by rfl) ⟨5586407, by rfl⟩ : syracuseStep 7448543 = 11172815) B11172815
theorem B4965695 : Blo 2205435 4965695 := bstep (se 1 (by rfl) ⟨3724271, by rfl⟩ : syracuseStep 4965695 = 7448543) B7448543
theorem B3310463 : Blo 2205435 3310463 := bstep (se 1 (by rfl) ⟨2482847, by rfl⟩ : syracuseStep 3310463 = 4965695) B4965695
theorem B2206975 : Blo 2205435 2206975 := bstep (se 1 (by rfl) ⟨1655231, by rfl⟩ : syracuseStep 2206975 = 3310463) B3310463
theorem B3310469 : Blo 2205435 3310469 := bbase (se 4 (by rfl) ⟨310356, by rfl⟩ : syracuseStep 3310469 = 620713) (by norm_num)
theorem B2206979 : Blo 2205435 2206979 := bstep (se 1 (by rfl) ⟨1655234, by rfl⟩ : syracuseStep 2206979 = 3310469) B3310469
theorem B3724285 : Blo 2205435 3724285 := bbase (se 3 (by rfl) ⟨698303, by rfl⟩ : syracuseStep 3724285 = 1396607) (by norm_num)
theorem B4965713 : Blo 2205435 4965713 := bstep (se 2 (by rfl) ⟨1862142, by rfl⟩ : syracuseStep 4965713 = 3724285) B3724285
theorem B3310475 : Blo 2205435 3310475 := bstep (se 1 (by rfl) ⟨2482856, by rfl⟩ : syracuseStep 3310475 = 4965713) B4965713
theorem B2206983 : Blo 2205435 2206983 := bstep (se 1 (by rfl) ⟨1655237, by rfl⟩ : syracuseStep 2206983 = 3310475) B3310475
theorem B2482861 : Blo 2205435 2482861 := bbase (se 3 (by rfl) ⟨465536, by rfl⟩ : syracuseStep 2482861 = 931073) (by norm_num)
theorem B3310481 : Blo 2205435 3310481 := bstep (se 2 (by rfl) ⟨1241430, by rfl⟩ : syracuseStep 3310481 = 2482861) B2482861
theorem B2206987 : Blo 2205435 2206987 := bstep (se 1 (by rfl) ⟨1655240, by rfl⟩ : syracuseStep 2206987 = 3310481) B3310481
theorem B7448597 : Blo 2205435 7448597 := bbase (se 6 (by rfl) ⟨174576, by rfl⟩ : syracuseStep 7448597 = 349153) (by norm_num)
theorem B4965731 : Blo 2205435 4965731 := bstep (se 1 (by rfl) ⟨3724298, by rfl⟩ : syracuseStep 4965731 = 7448597) B7448597
theorem B3310487 : Blo 2205435 3310487 := bstep (se 1 (by rfl) ⟨2482865, by rfl⟩ : syracuseStep 3310487 = 4965731) B4965731
theorem B2206991 : Blo 2205435 2206991 := bstep (se 1 (by rfl) ⟨1655243, by rfl⟩ : syracuseStep 2206991 = 3310487) B3310487
theorem B3310493 : Blo 2205435 3310493 := bbase (se 3 (by rfl) ⟨620717, by rfl⟩ : syracuseStep 3310493 = 1241435) (by norm_num)
theorem B2206995 : Blo 2205435 2206995 := bstep (se 1 (by rfl) ⟨1655246, by rfl⟩ : syracuseStep 2206995 = 3310493) B3310493
theorem B4965749 : Blo 2205435 4965749 := bbase (se 5 (by rfl) ⟨232769, by rfl⟩ : syracuseStep 4965749 = 465539) (by norm_num)
theorem B3310499 : Blo 2205435 3310499 := bstep (se 1 (by rfl) ⟨2482874, by rfl⟩ : syracuseStep 3310499 = 4965749) B4965749
theorem B2206999 : Blo 2205435 2206999 := bstep (se 1 (by rfl) ⟨1655249, by rfl⟩ : syracuseStep 2206999 = 3310499) B3310499
theorem B3775133 : Blo 2205435 3775133 := bbase (se 3 (by rfl) ⟨707837, by rfl⟩ : syracuseStep 3775133 = 1415675) (by norm_num)
theorem B2516755 : Blo 2205435 2516755 := bstep (se 1 (by rfl) ⟨1887566, by rfl⟩ : syracuseStep 2516755 = 3775133) B3775133
theorem B3355673 : Blo 2205435 3355673 := bstep (se 2 (by rfl) ⟨1258377, by rfl⟩ : syracuseStep 3355673 = 2516755) B2516755
theorem B35793845 : Blo 2205435 35793845 := bstep (se 5 (by rfl) ⟨1677836, by rfl⟩ : syracuseStep 35793845 = 3355673) B3355673
theorem B23862563 : Blo 2205435 23862563 := bstep (se 1 (by rfl) ⟨17896922, by rfl⟩ : syracuseStep 23862563 = 35793845) B35793845
theorem B15908375 : Blo 2205435 15908375 := bstep (se 1 (by rfl) ⟨11931281, by rfl⟩ : syracuseStep 15908375 = 23862563) B23862563
theorem B10605583 : Blo 2205435 10605583 := bstep (se 1 (by rfl) ⟨7954187, by rfl⟩ : syracuseStep 10605583 = 15908375) B15908375
theorem B14140777 : Blo 2205435 14140777 := bstep (se 2 (by rfl) ⟨5302791, by rfl⟩ : syracuseStep 14140777 = 10605583) B10605583
theorem B18854369 : Blo 2205435 18854369 := bstep (se 2 (by rfl) ⟨7070388, by rfl⟩ : syracuseStep 18854369 = 14140777) B14140777
theorem B12569579 : Blo 2205435 12569579 := bstep (se 1 (by rfl) ⟨9427184, by rfl⟩ : syracuseStep 12569579 = 18854369) B18854369
theorem B8379719 : Blo 2205435 8379719 := bstep (se 1 (by rfl) ⟨6284789, by rfl⟩ : syracuseStep 8379719 = 12569579) B12569579
theorem B5586479 : Blo 2205435 5586479 := bstep (se 1 (by rfl) ⟨4189859, by rfl⟩ : syracuseStep 5586479 = 8379719) B8379719
theorem B3724319 : Blo 2205435 3724319 := bstep (se 1 (by rfl) ⟨2793239, by rfl⟩ : syracuseStep 3724319 = 5586479) B5586479
theorem B2482879 : Blo 2205435 2482879 := bstep (se 1 (by rfl) ⟨1862159, by rfl⟩ : syracuseStep 2482879 = 3724319) B3724319
theorem B3310505 : Blo 2205435 3310505 := bstep (se 2 (by rfl) ⟨1241439, by rfl⟩ : syracuseStep 3310505 = 2482879) B2482879
theorem B2207003 : Blo 2205435 2207003 := bstep (se 1 (by rfl) ⟨1655252, by rfl⟩ : syracuseStep 2207003 = 3310505) B3310505
theorem B8379733 : Blo 2205435 8379733 := bbase (se 11 (by rfl) ⟨6137, by rfl⟩ : syracuseStep 8379733 = 12275) (by norm_num)
theorem B11172977 : Blo 2205435 11172977 := bstep (se 2 (by rfl) ⟨4189866, by rfl⟩ : syracuseStep 11172977 = 8379733) B8379733
theorem B7448651 : Blo 2205435 7448651 := bstep (se 1 (by rfl) ⟨5586488, by rfl⟩ : syracuseStep 7448651 = 11172977) B11172977
theorem B4965767 : Blo 2205435 4965767 := bstep (se 1 (by rfl) ⟨3724325, by rfl⟩ : syracuseStep 4965767 = 7448651) B7448651
theorem B3310511 : Blo 2205435 3310511 := bstep (se 1 (by rfl) ⟨2482883, by rfl⟩ : syracuseStep 3310511 = 4965767) B4965767
theorem B2207007 : Blo 2205435 2207007 := bstep (se 1 (by rfl) ⟨1655255, by rfl⟩ : syracuseStep 2207007 = 3310511) B3310511
theorem B3310517 : Blo 2205435 3310517 := bbase (se 5 (by rfl) ⟨155180, by rfl⟩ : syracuseStep 3310517 = 310361) (by norm_num)
theorem B2207011 : Blo 2205435 2207011 := bstep (se 1 (by rfl) ⟨1655258, by rfl⟩ : syracuseStep 2207011 = 3310517) B3310517
theorem B5586509 : Blo 2205435 5586509 := bbase (se 3 (by rfl) ⟨1047470, by rfl⟩ : syracuseStep 5586509 = 2094941) (by norm_num)
theorem B3724339 : Blo 2205435 3724339 := bstep (se 1 (by rfl) ⟨2793254, by rfl⟩ : syracuseStep 3724339 = 5586509) B5586509
theorem B4965785 : Blo 2205435 4965785 := bstep (se 2 (by rfl) ⟨1862169, by rfl⟩ : syracuseStep 4965785 = 3724339) B3724339
theorem B3310523 : Blo 2205435 3310523 := bstep (se 1 (by rfl) ⟨2482892, by rfl⟩ : syracuseStep 3310523 = 4965785) B4965785
theorem B2207015 : Blo 2205435 2207015 := bstep (se 1 (by rfl) ⟨1655261, by rfl⟩ : syracuseStep 2207015 = 3310523) B3310523
theorem B2482897 : Blo 2205435 2482897 := bbase (se 2 (by rfl) ⟨931086, by rfl⟩ : syracuseStep 2482897 = 1862173) (by norm_num)
theorem B3310529 : Blo 2205435 3310529 := bstep (se 2 (by rfl) ⟨1241448, by rfl⟩ : syracuseStep 3310529 = 2482897) B2482897
theorem B2207019 : Blo 2205435 2207019 := bstep (se 1 (by rfl) ⟨1655264, by rfl⟩ : syracuseStep 2207019 = 3310529) B3310529
theorem B7070453 : Blo 2205435 7070453 := bbase (se 5 (by rfl) ⟨331427, by rfl⟩ : syracuseStep 7070453 = 662855) (by norm_num)
theorem B4713635 : Blo 2205435 4713635 := bstep (se 1 (by rfl) ⟨3535226, by rfl⟩ : syracuseStep 4713635 = 7070453) B7070453
theorem B3142423 : Blo 2205435 3142423 := bstep (se 1 (by rfl) ⟨2356817, by rfl⟩ : syracuseStep 3142423 = 4713635) B4713635
theorem B4189897 : Blo 2205435 4189897 := bstep (se 2 (by rfl) ⟨1571211, by rfl⟩ : syracuseStep 4189897 = 3142423) B3142423
theorem B5586529 : Blo 2205435 5586529 := bstep (se 2 (by rfl) ⟨2094948, by rfl⟩ : syracuseStep 5586529 = 4189897) B4189897
theorem B7448705 : Blo 2205435 7448705 := bstep (se 2 (by rfl) ⟨2793264, by rfl⟩ : syracuseStep 7448705 = 5586529) B5586529
theorem B4965803 : Blo 2205435 4965803 := bstep (se 1 (by rfl) ⟨3724352, by rfl⟩ : syracuseStep 4965803 = 7448705) B7448705
theorem B3310535 : Blo 2205435 3310535 := bstep (se 1 (by rfl) ⟨2482901, by rfl⟩ : syracuseStep 3310535 = 4965803) B4965803
theorem B2207023 : Blo 2205435 2207023 := bstep (se 1 (by rfl) ⟨1655267, by rfl⟩ : syracuseStep 2207023 = 3310535) B3310535
theorem B3310541 : Blo 2205435 3310541 := bbase (se 3 (by rfl) ⟨620726, by rfl⟩ : syracuseStep 3310541 = 1241453) (by norm_num)
theorem B2207027 : Blo 2205435 2207027 := bstep (se 1 (by rfl) ⟨1655270, by rfl⟩ : syracuseStep 2207027 = 3310541) B3310541
theorem B4965821 : Blo 2205435 4965821 := bbase (se 3 (by rfl) ⟨931091, by rfl⟩ : syracuseStep 4965821 = 1862183) (by norm_num)
theorem B3310547 : Blo 2205435 3310547 := bstep (se 1 (by rfl) ⟨2482910, by rfl⟩ : syracuseStep 3310547 = 4965821) B4965821
theorem B2207031 : Blo 2205435 2207031 := bstep (se 1 (by rfl) ⟨1655273, by rfl⟩ : syracuseStep 2207031 = 3310547) B3310547
theorem B3724373 : Blo 2205435 3724373 := bbase (se 8 (by rfl) ⟨21822, by rfl⟩ : syracuseStep 3724373 = 43645) (by norm_num)
theorem B2482915 : Blo 2205435 2482915 := bstep (se 1 (by rfl) ⟨1862186, by rfl⟩ : syracuseStep 2482915 = 3724373) B3724373
theorem B3310553 : Blo 2205435 3310553 := bstep (se 2 (by rfl) ⟨1241457, by rfl⟩ : syracuseStep 3310553 = 2482915) B2482915
theorem B2207035 : Blo 2205435 2207035 := bstep (se 1 (by rfl) ⟨1655276, by rfl⟩ : syracuseStep 2207035 = 3310553) B3310553
theorem B4723525 : Blo 2205435 4723525 := bbase (se 4 (by rfl) ⟨442830, by rfl⟩ : syracuseStep 4723525 = 885661) (by norm_num)
theorem B25192133 : Blo 2205435 25192133 := bstep (se 4 (by rfl) ⟨2361762, by rfl⟩ : syracuseStep 25192133 = 4723525) B4723525
theorem B16794755 : Blo 2205435 16794755 := bstep (se 1 (by rfl) ⟨12596066, by rfl⟩ : syracuseStep 16794755 = 25192133) B25192133
theorem B11196503 : Blo 2205435 11196503 := bstep (se 1 (by rfl) ⟨8397377, by rfl⟩ : syracuseStep 11196503 = 16794755) B16794755
theorem B7464335 : Blo 2205435 7464335 := bstep (se 1 (by rfl) ⟨5598251, by rfl⟩ : syracuseStep 7464335 = 11196503) B11196503
theorem B79619573 : Blo 2205435 79619573 := bstep (se 5 (by rfl) ⟨3732167, by rfl⟩ : syracuseStep 79619573 = 7464335) B7464335
theorem B53079715 : Blo 2205435 53079715 := bstep (se 1 (by rfl) ⟨39809786, by rfl⟩ : syracuseStep 53079715 = 79619573) B79619573
theorem B70772953 : Blo 2205435 70772953 := bstep (se 2 (by rfl) ⟨26539857, by rfl⟩ : syracuseStep 70772953 = 53079715) B53079715
theorem B94363937 : Blo 2205435 94363937 := bstep (se 2 (by rfl) ⟨35386476, by rfl⟩ : syracuseStep 94363937 = 70772953) B70772953
theorem B62909291 : Blo 2205435 62909291 := bstep (se 1 (by rfl) ⟨47181968, by rfl⟩ : syracuseStep 62909291 = 94363937) B94363937
theorem B41939527 : Blo 2205435 41939527 := bstep (se 1 (by rfl) ⟨31454645, by rfl⟩ : syracuseStep 41939527 = 62909291) B62909291
theorem B55919369 : Blo 2205435 55919369 := bstep (se 2 (by rfl) ⟨20969763, by rfl⟩ : syracuseStep 55919369 = 41939527) B41939527
theorem B149118317 : Blo 2205435 149118317 := bstep (se 3 (by rfl) ⟨27959684, by rfl⟩ : syracuseStep 149118317 = 55919369) B55919369
theorem B99412211 : Blo 2205435 99412211 := bstep (se 1 (by rfl) ⟨74559158, by rfl⟩ : syracuseStep 99412211 = 149118317) B149118317
theorem B66274807 : Blo 2205435 66274807 := bstep (se 1 (by rfl) ⟨49706105, by rfl⟩ : syracuseStep 66274807 = 99412211) B99412211
theorem B88366409 : Blo 2205435 88366409 := bstep (se 2 (by rfl) ⟨33137403, by rfl⟩ : syracuseStep 88366409 = 66274807) B66274807
theorem B58910939 : Blo 2205435 58910939 := bstep (se 1 (by rfl) ⟨44183204, by rfl⟩ : syracuseStep 58910939 = 88366409) B88366409
theorem B39273959 : Blo 2205435 39273959 := bstep (se 1 (by rfl) ⟨29455469, by rfl⟩ : syracuseStep 39273959 = 58910939) B58910939
theorem B26182639 : Blo 2205435 26182639 := bstep (se 1 (by rfl) ⟨19636979, by rfl⟩ : syracuseStep 26182639 = 39273959) B39273959
theorem B34910185 : Blo 2205435 34910185 := bstep (se 2 (by rfl) ⟨13091319, by rfl⟩ : syracuseStep 34910185 = 26182639) B26182639
theorem B46546913 : Blo 2205435 46546913 := bstep (se 2 (by rfl) ⟨17455092, by rfl⟩ : syracuseStep 46546913 = 34910185) B34910185
theorem B31031275 : Blo 2205435 31031275 := bstep (se 1 (by rfl) ⟨23273456, by rfl⟩ : syracuseStep 31031275 = 46546913) B46546913
theorem B41375033 : Blo 2205435 41375033 := bstep (se 2 (by rfl) ⟨15515637, by rfl⟩ : syracuseStep 41375033 = 31031275) B31031275
theorem B27583355 : Blo 2205435 27583355 := bstep (se 1 (by rfl) ⟨20687516, by rfl⟩ : syracuseStep 27583355 = 41375033) B41375033
theorem B73555613 : Blo 2205435 73555613 := bstep (se 3 (by rfl) ⟨13791677, by rfl⟩ : syracuseStep 73555613 = 27583355) B27583355
theorem B49037075 : Blo 2205435 49037075 := bstep (se 1 (by rfl) ⟨36777806, by rfl⟩ : syracuseStep 49037075 = 73555613) B73555613
theorem B32691383 : Blo 2205435 32691383 := bstep (se 1 (by rfl) ⟨24518537, by rfl⟩ : syracuseStep 32691383 = 49037075) B49037075
theorem B21794255 : Blo 2205435 21794255 := bstep (se 1 (by rfl) ⟨16345691, by rfl⟩ : syracuseStep 21794255 = 32691383) B32691383
theorem B14529503 : Blo 2205435 14529503 := bstep (se 1 (by rfl) ⟨10897127, by rfl⟩ : syracuseStep 14529503 = 21794255) B21794255
theorem B38745341 : Blo 2205435 38745341 := bstep (se 3 (by rfl) ⟨7264751, by rfl⟩ : syracuseStep 38745341 = 14529503) B14529503
theorem B25830227 : Blo 2205435 25830227 := bstep (se 1 (by rfl) ⟨19372670, by rfl⟩ : syracuseStep 25830227 = 38745341) B38745341
theorem B17220151 : Blo 2205435 17220151 := bstep (se 1 (by rfl) ⟨12915113, by rfl⟩ : syracuseStep 17220151 = 25830227) B25830227
theorem B22960201 : Blo 2205435 22960201 := bstep (se 2 (by rfl) ⟨8610075, by rfl⟩ : syracuseStep 22960201 = 17220151) B17220151
theorem B30613601 : Blo 2205435 30613601 := bstep (se 2 (by rfl) ⟨11480100, by rfl⟩ : syracuseStep 30613601 = 22960201) B22960201
theorem B20409067 : Blo 2205435 20409067 := bstep (se 1 (by rfl) ⟨15306800, by rfl⟩ : syracuseStep 20409067 = 30613601) B30613601
theorem B108848357 : Blo 2205435 108848357 := bstep (se 4 (by rfl) ⟨10204533, by rfl⟩ : syracuseStep 108848357 = 20409067) B20409067
theorem B72565571 : Blo 2205435 72565571 := bstep (se 1 (by rfl) ⟨54424178, by rfl⟩ : syracuseStep 72565571 = 108848357) B108848357
theorem B193508189 : Blo 2205435 193508189 := bstep (se 3 (by rfl) ⟨36282785, by rfl⟩ : syracuseStep 193508189 = 72565571) B72565571
theorem B129005459 : Blo 2205435 129005459 := bstep (se 1 (by rfl) ⟨96754094, by rfl⟩ : syracuseStep 129005459 = 193508189) B193508189
theorem B86003639 : Blo 2205435 86003639 := bstep (se 1 (by rfl) ⟨64502729, by rfl⟩ : syracuseStep 86003639 = 129005459) B129005459
theorem B57335759 : Blo 2205435 57335759 := bstep (se 1 (by rfl) ⟨43001819, by rfl⟩ : syracuseStep 57335759 = 86003639) B86003639
theorem B38223839 : Blo 2205435 38223839 := bstep (se 1 (by rfl) ⟨28667879, by rfl⟩ : syracuseStep 38223839 = 57335759) B57335759
theorem B25482559 : Blo 2205435 25482559 := bstep (se 1 (by rfl) ⟨19111919, by rfl⟩ : syracuseStep 25482559 = 38223839) B38223839
theorem B33976745 : Blo 2205435 33976745 := bstep (se 2 (by rfl) ⟨12741279, by rfl⟩ : syracuseStep 33976745 = 25482559) B25482559
theorem B22651163 : Blo 2205435 22651163 := bstep (se 1 (by rfl) ⟨16988372, by rfl⟩ : syracuseStep 22651163 = 33976745) B33976745
theorem B15100775 : Blo 2205435 15100775 := bstep (se 1 (by rfl) ⟨11325581, by rfl⟩ : syracuseStep 15100775 = 22651163) B22651163
theorem B10067183 : Blo 2205435 10067183 := bstep (se 1 (by rfl) ⟨7550387, by rfl⟩ : syracuseStep 10067183 = 15100775) B15100775
theorem B6711455 : Blo 2205435 6711455 := bstep (se 1 (by rfl) ⟨5033591, by rfl⟩ : syracuseStep 6711455 = 10067183) B10067183
theorem B17897213 : Blo 2205435 17897213 := bstep (se 3 (by rfl) ⟨3355727, by rfl⟩ : syracuseStep 17897213 = 6711455) B6711455
theorem B11931475 : Blo 2205435 11931475 := bstep (se 1 (by rfl) ⟨8948606, by rfl⟩ : syracuseStep 11931475 = 17897213) B17897213
theorem B15908633 : Blo 2205435 15908633 := bstep (se 2 (by rfl) ⟨5965737, by rfl⟩ : syracuseStep 15908633 = 11931475) B11931475
theorem B10605755 : Blo 2205435 10605755 := bstep (se 1 (by rfl) ⟨7954316, by rfl⟩ : syracuseStep 10605755 = 15908633) B15908633
theorem B7070503 : Blo 2205435 7070503 := bstep (se 1 (by rfl) ⟨5302877, by rfl⟩ : syracuseStep 7070503 = 10605755) B10605755
theorem B9427337 : Blo 2205435 9427337 := bstep (se 2 (by rfl) ⟨3535251, by rfl⟩ : syracuseStep 9427337 = 7070503) B7070503
theorem B6284891 : Blo 2205435 6284891 := bstep (se 1 (by rfl) ⟨4713668, by rfl⟩ : syracuseStep 6284891 = 9427337) B9427337
theorem B16759709 : Blo 2205435 16759709 := bstep (se 3 (by rfl) ⟨3142445, by rfl⟩ : syracuseStep 16759709 = 6284891) B6284891
theorem B11173139 : Blo 2205435 11173139 := bstep (se 1 (by rfl) ⟨8379854, by rfl⟩ : syracuseStep 11173139 = 16759709) B16759709
theorem B7448759 : Blo 2205435 7448759 := bstep (se 1 (by rfl) ⟨5586569, by rfl⟩ : syracuseStep 7448759 = 11173139) B11173139
theorem B4965839 : Blo 2205435 4965839 := bstep (se 1 (by rfl) ⟨3724379, by rfl⟩ : syracuseStep 4965839 = 7448759) B7448759
theorem B3310559 : Blo 2205435 3310559 := bstep (se 1 (by rfl) ⟨2482919, by rfl⟩ : syracuseStep 3310559 = 4965839) B4965839
theorem B2207039 : Blo 2205435 2207039 := bstep (se 1 (by rfl) ⟨1655279, by rfl⟩ : syracuseStep 2207039 = 3310559) B3310559
theorem B3310565 : Blo 2205435 3310565 := bbase (se 4 (by rfl) ⟨310365, by rfl⟩ : syracuseStep 3310565 = 620731) (by norm_num)
theorem B2207043 : Blo 2205435 2207043 := bstep (se 1 (by rfl) ⟨1655282, by rfl⟩ : syracuseStep 2207043 = 3310565) B3310565
theorem B2651449 : Blo 2205435 2651449 := bbase (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) (by norm_num)
theorem B3535265 : Blo 2205435 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B9427373 : Blo 2205435 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B6284915 : Blo 2205435 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B4189943 : Blo 2205435 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B2793295 : Blo 2205435 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B3724393 : Blo 2205435 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B4965857 : Blo 2205435 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B3310571 : Blo 2205435 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B2207047 : Blo 2205435 2207047 := bstep (se 1 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 2207047 = 3310571) B3310571
theorem B2482933 : Blo 2205435 2482933 := bbase (se 5 (by rfl) ⟨116387, by rfl⟩ : syracuseStep 2482933 = 232775) (by norm_num)
theorem B3310577 : Blo 2205435 3310577 := bstep (se 2 (by rfl) ⟨1241466, by rfl⟩ : syracuseStep 3310577 = 2482933) B2482933
theorem B2207051 : Blo 2205435 2207051 := bstep (se 1 (by rfl) ⟨1655288, by rfl⟩ : syracuseStep 2207051 = 3310577) B3310577
theorem B2793305 : Blo 2205435 2793305 := bbase (se 2 (by rfl) ⟨1047489, by rfl⟩ : syracuseStep 2793305 = 2094979) (by norm_num)
theorem B7448813 : Blo 2205435 7448813 := bstep (se 3 (by rfl) ⟨1396652, by rfl⟩ : syracuseStep 7448813 = 2793305) B2793305
theorem B4965875 : Blo 2205435 4965875 := bstep (se 1 (by rfl) ⟨3724406, by rfl⟩ : syracuseStep 4965875 = 7448813) B7448813
theorem B3310583 : Blo 2205435 3310583 := bstep (se 1 (by rfl) ⟨2482937, by rfl⟩ : syracuseStep 3310583 = 4965875) B4965875
theorem B2207055 : Blo 2205435 2207055 := bstep (se 1 (by rfl) ⟨1655291, by rfl⟩ : syracuseStep 2207055 = 3310583) B3310583
theorem B3310589 : Blo 2205435 3310589 := bbase (se 3 (by rfl) ⟨620735, by rfl⟩ : syracuseStep 3310589 = 1241471) (by norm_num)
theorem B2207059 : Blo 2205435 2207059 := bstep (se 1 (by rfl) ⟨1655294, by rfl⟩ : syracuseStep 2207059 = 3310589) B3310589
theorem B4965893 : Blo 2205435 4965893 := bbase (se 4 (by rfl) ⟨465552, by rfl⟩ : syracuseStep 4965893 = 931105) (by norm_num)
theorem B3310595 : Blo 2205435 3310595 := bstep (se 1 (by rfl) ⟨2482946, by rfl⟩ : syracuseStep 3310595 = 4965893) B4965893
theorem B2207063 : Blo 2205435 2207063 := bstep (se 1 (by rfl) ⟨1655297, by rfl⟩ : syracuseStep 2207063 = 3310595) B3310595
theorem B4189981 : Blo 2205435 4189981 := bbase (se 3 (by rfl) ⟨785621, by rfl⟩ : syracuseStep 4189981 = 1571243) (by norm_num)
theorem B5586641 : Blo 2205435 5586641 := bstep (se 2 (by rfl) ⟨2094990, by rfl⟩ : syracuseStep 5586641 = 4189981) B4189981
theorem B3724427 : Blo 2205435 3724427 := bstep (se 1 (by rfl) ⟨2793320, by rfl⟩ : syracuseStep 3724427 = 5586641) B5586641
theorem B2482951 : Blo 2205435 2482951 := bstep (se 1 (by rfl) ⟨1862213, by rfl⟩ : syracuseStep 2482951 = 3724427) B3724427
theorem B3310601 : Blo 2205435 3310601 := bstep (se 2 (by rfl) ⟨1241475, by rfl⟩ : syracuseStep 3310601 = 2482951) B2482951
theorem B2207067 : Blo 2205435 2207067 := bstep (se 1 (by rfl) ⟨1655300, by rfl⟩ : syracuseStep 2207067 = 3310601) B3310601
theorem B11173301 : Blo 2205435 11173301 := bbase (se 5 (by rfl) ⟨523748, by rfl⟩ : syracuseStep 11173301 = 1047497) (by norm_num)
theorem B7448867 : Blo 2205435 7448867 := bstep (se 1 (by rfl) ⟨5586650, by rfl⟩ : syracuseStep 7448867 = 11173301) B11173301
theorem B4965911 : Blo 2205435 4965911 := bstep (se 1 (by rfl) ⟨3724433, by rfl⟩ : syracuseStep 4965911 = 7448867) B7448867
theorem B3310607 : Blo 2205435 3310607 := bstep (se 1 (by rfl) ⟨2482955, by rfl⟩ : syracuseStep 3310607 = 4965911) B4965911
theorem B2207071 : Blo 2205435 2207071 := bstep (se 1 (by rfl) ⟨1655303, by rfl⟩ : syracuseStep 2207071 = 3310607) B3310607
theorem B3310613 : Blo 2205435 3310613 := bbase (se 6 (by rfl) ⟨77592, by rfl⟩ : syracuseStep 3310613 = 155185) (by norm_num)
theorem B2207075 : Blo 2205435 2207075 := bstep (se 1 (by rfl) ⟨1655306, by rfl⟩ : syracuseStep 2207075 = 3310613) B3310613
theorem B10067365 : Blo 2205435 10067365 := bbase (se 4 (by rfl) ⟨943815, by rfl⟩ : syracuseStep 10067365 = 1887631) (by norm_num)
theorem B13423153 : Blo 2205435 13423153 := bstep (se 2 (by rfl) ⟨5033682, by rfl⟩ : syracuseStep 13423153 = 10067365) B10067365
theorem B17897537 : Blo 2205435 17897537 := bstep (se 2 (by rfl) ⟨6711576, by rfl⟩ : syracuseStep 17897537 = 13423153) B13423153
theorem B47726765 : Blo 2205435 47726765 := bstep (se 3 (by rfl) ⟨8948768, by rfl⟩ : syracuseStep 47726765 = 17897537) B17897537
theorem B31817843 : Blo 2205435 31817843 := bstep (se 1 (by rfl) ⟨23863382, by rfl⟩ : syracuseStep 31817843 = 47726765) B47726765
theorem B21211895 : Blo 2205435 21211895 := bstep (se 1 (by rfl) ⟨15908921, by rfl⟩ : syracuseStep 21211895 = 31817843) B31817843
theorem B14141263 : Blo 2205435 14141263 := bstep (se 1 (by rfl) ⟨10605947, by rfl⟩ : syracuseStep 14141263 = 21211895) B21211895
theorem B18855017 : Blo 2205435 18855017 := bstep (se 2 (by rfl) ⟨7070631, by rfl⟩ : syracuseStep 18855017 = 14141263) B14141263
theorem B12570011 : Blo 2205435 12570011 := bstep (se 1 (by rfl) ⟨9427508, by rfl⟩ : syracuseStep 12570011 = 18855017) B18855017
theorem B8380007 : Blo 2205435 8380007 := bstep (se 1 (by rfl) ⟨6285005, by rfl⟩ : syracuseStep 8380007 = 12570011) B12570011
theorem B5586671 : Blo 2205435 5586671 := bstep (se 1 (by rfl) ⟨4190003, by rfl⟩ : syracuseStep 5586671 = 8380007) B8380007
theorem B3724447 : Blo 2205435 3724447 := bstep (se 1 (by rfl) ⟨2793335, by rfl⟩ : syracuseStep 3724447 = 5586671) B5586671
theorem B4965929 : Blo 2205435 4965929 := bstep (se 2 (by rfl) ⟨1862223, by rfl⟩ : syracuseStep 4965929 = 3724447) B3724447
theorem B3310619 : Blo 2205435 3310619 := bstep (se 1 (by rfl) ⟨2482964, by rfl⟩ : syracuseStep 3310619 = 4965929) B4965929
theorem B2207079 : Blo 2205435 2207079 := bstep (se 1 (by rfl) ⟨1655309, by rfl⟩ : syracuseStep 2207079 = 3310619) B3310619
theorem B2482969 : Blo 2205435 2482969 := bbase (se 2 (by rfl) ⟨931113, by rfl⟩ : syracuseStep 2482969 = 1862227) (by norm_num)
theorem B3310625 : Blo 2205435 3310625 := bstep (se 2 (by rfl) ⟨1241484, by rfl⟩ : syracuseStep 3310625 = 2482969) B2482969
theorem B2207083 : Blo 2205435 2207083 := bstep (se 1 (by rfl) ⟨1655312, by rfl⟩ : syracuseStep 2207083 = 3310625) B3310625
theorem B8380037 : Blo 2205435 8380037 := bbase (se 4 (by rfl) ⟨785628, by rfl⟩ : syracuseStep 8380037 = 1571257) (by norm_num)
theorem B5586691 : Blo 2205435 5586691 := bstep (se 1 (by rfl) ⟨4190018, by rfl⟩ : syracuseStep 5586691 = 8380037) B8380037
theorem B7448921 : Blo 2205435 7448921 := bstep (se 2 (by rfl) ⟨2793345, by rfl⟩ : syracuseStep 7448921 = 5586691) B5586691
theorem B4965947 : Blo 2205435 4965947 := bstep (se 1 (by rfl) ⟨3724460, by rfl⟩ : syracuseStep 4965947 = 7448921) B7448921
theorem B3310631 : Blo 2205435 3310631 := bstep (se 1 (by rfl) ⟨2482973, by rfl⟩ : syracuseStep 3310631 = 4965947) B4965947
theorem B2207087 : Blo 2205435 2207087 := bstep (se 1 (by rfl) ⟨1655315, by rfl⟩ : syracuseStep 2207087 = 3310631) B3310631
theorem B3310637 : Blo 2205435 3310637 := bbase (se 3 (by rfl) ⟨620744, by rfl⟩ : syracuseStep 3310637 = 1241489) (by norm_num)
theorem B2207091 : Blo 2205435 2207091 := bstep (se 1 (by rfl) ⟨1655318, by rfl⟩ : syracuseStep 2207091 = 3310637) B3310637
theorem B4965965 : Blo 2205435 4965965 := bbase (se 3 (by rfl) ⟨931118, by rfl⟩ : syracuseStep 4965965 = 1862237) (by norm_num)
theorem B3310643 : Blo 2205435 3310643 := bstep (se 1 (by rfl) ⟨2482982, by rfl⟩ : syracuseStep 3310643 = 4965965) B4965965
theorem B2207095 : Blo 2205435 2207095 := bstep (se 1 (by rfl) ⟨1655321, by rfl⟩ : syracuseStep 2207095 = 3310643) B3310643
theorem B2793361 : Blo 2205435 2793361 := bbase (se 2 (by rfl) ⟨1047510, by rfl⟩ : syracuseStep 2793361 = 2095021) (by norm_num)
theorem B3724481 : Blo 2205435 3724481 := bstep (se 2 (by rfl) ⟨1396680, by rfl⟩ : syracuseStep 3724481 = 2793361) B2793361
theorem B2482987 : Blo 2205435 2482987 := bstep (se 1 (by rfl) ⟨1862240, by rfl⟩ : syracuseStep 2482987 = 3724481) B3724481
theorem B3310649 : Blo 2205435 3310649 := bstep (se 2 (by rfl) ⟨1241493, by rfl⟩ : syracuseStep 3310649 = 2482987) B2482987
theorem B2207099 : Blo 2205435 2207099 := bstep (se 1 (by rfl) ⟨1655324, by rfl⟩ : syracuseStep 2207099 = 3310649) B3310649
theorem B4713805 : Blo 2205435 4713805 := bbase (se 3 (by rfl) ⟨883838, by rfl⟩ : syracuseStep 4713805 = 1767677) (by norm_num)
theorem B25140293 : Blo 2205435 25140293 := bstep (se 4 (by rfl) ⟨2356902, by rfl⟩ : syracuseStep 25140293 = 4713805) B4713805
theorem B16760195 : Blo 2205435 16760195 := bstep (se 1 (by rfl) ⟨12570146, by rfl⟩ : syracuseStep 16760195 = 25140293) B25140293
theorem B11173463 : Blo 2205435 11173463 := bstep (se 1 (by rfl) ⟨8380097, by rfl⟩ : syracuseStep 11173463 = 16760195) B16760195
theorem B7448975 : Blo 2205435 7448975 := bstep (se 1 (by rfl) ⟨5586731, by rfl⟩ : syracuseStep 7448975 = 11173463) B11173463
theorem B4965983 : Blo 2205435 4965983 := bstep (se 1 (by rfl) ⟨3724487, by rfl⟩ : syracuseStep 4965983 = 7448975) B7448975
theorem B3310655 : Blo 2205435 3310655 := bstep (se 1 (by rfl) ⟨2482991, by rfl⟩ : syracuseStep 3310655 = 4965983) B4965983
theorem B2207103 : Blo 2205435 2207103 := bstep (se 1 (by rfl) ⟨1655327, by rfl⟩ : syracuseStep 2207103 = 3310655) B3310655
theorem B3310661 : Blo 2205435 3310661 := bbase (se 4 (by rfl) ⟨310374, by rfl⟩ : syracuseStep 3310661 = 620749) (by norm_num)
theorem B2207107 : Blo 2205435 2207107 := bstep (se 1 (by rfl) ⟨1655330, by rfl⟩ : syracuseStep 2207107 = 3310661) B3310661
theorem B3724501 : Blo 2205435 3724501 := bbase (se 7 (by rfl) ⟨43646, by rfl⟩ : syracuseStep 3724501 = 87293) (by norm_num)
theorem B4966001 : Blo 2205435 4966001 := bstep (se 2 (by rfl) ⟨1862250, by rfl⟩ : syracuseStep 4966001 = 3724501) B3724501
theorem B3310667 : Blo 2205435 3310667 := bstep (se 1 (by rfl) ⟨2483000, by rfl⟩ : syracuseStep 3310667 = 4966001) B4966001
theorem B2207111 : Blo 2205435 2207111 := bstep (se 1 (by rfl) ⟨1655333, by rfl⟩ : syracuseStep 2207111 = 3310667) B3310667
theorem B2483005 : Blo 2205435 2483005 := bbase (se 3 (by rfl) ⟨465563, by rfl⟩ : syracuseStep 2483005 = 931127) (by norm_num)
theorem B3310673 : Blo 2205435 3310673 := bstep (se 2 (by rfl) ⟨1241502, by rfl⟩ : syracuseStep 3310673 = 2483005) B2483005
theorem B2207115 : Blo 2205435 2207115 := bstep (se 1 (by rfl) ⟨1655336, by rfl⟩ : syracuseStep 2207115 = 3310673) B3310673
theorem B7449029 : Blo 2205435 7449029 := bbase (se 4 (by rfl) ⟨698346, by rfl⟩ : syracuseStep 7449029 = 1396693) (by norm_num)
theorem B4966019 : Blo 2205435 4966019 := bstep (se 1 (by rfl) ⟨3724514, by rfl⟩ : syracuseStep 4966019 = 7449029) B7449029
theorem B3310679 : Blo 2205435 3310679 := bstep (se 1 (by rfl) ⟨2483009, by rfl⟩ : syracuseStep 3310679 = 4966019) B4966019
theorem B2207119 : Blo 2205435 2207119 := bstep (se 1 (by rfl) ⟨1655339, by rfl⟩ : syracuseStep 2207119 = 3310679) B3310679
theorem B3310685 : Blo 2205435 3310685 := bbase (se 3 (by rfl) ⟨620753, by rfl⟩ : syracuseStep 3310685 = 1241507) (by norm_num)
theorem B2207123 : Blo 2205435 2207123 := bstep (se 1 (by rfl) ⟨1655342, by rfl⟩ : syracuseStep 2207123 = 3310685) B3310685
theorem B4966037 : Blo 2205435 4966037 := bbase (se 6 (by rfl) ⟨116391, by rfl⟩ : syracuseStep 4966037 = 232783) (by norm_num)
theorem B3310691 : Blo 2205435 3310691 := bstep (se 1 (by rfl) ⟨2483018, by rfl⟩ : syracuseStep 3310691 = 4966037) B4966037
theorem B2207127 : Blo 2205435 2207127 := bstep (se 1 (by rfl) ⟨1655345, by rfl⟩ : syracuseStep 2207127 = 3310691) B3310691
theorem B2356933 : Blo 2205435 2356933 := bbase (se 4 (by rfl) ⟨220962, by rfl⟩ : syracuseStep 2356933 = 441925) (by norm_num)
theorem B3142577 : Blo 2205435 3142577 := bstep (se 2 (by rfl) ⟨1178466, by rfl⟩ : syracuseStep 3142577 = 2356933) B2356933
theorem B8380205 : Blo 2205435 8380205 := bstep (se 3 (by rfl) ⟨1571288, by rfl⟩ : syracuseStep 8380205 = 3142577) B3142577
theorem B5586803 : Blo 2205435 5586803 := bstep (se 1 (by rfl) ⟨4190102, by rfl⟩ : syracuseStep 5586803 = 8380205) B8380205
theorem B3724535 : Blo 2205435 3724535 := bstep (se 1 (by rfl) ⟨2793401, by rfl⟩ : syracuseStep 3724535 = 5586803) B5586803
theorem B2483023 : Blo 2205435 2483023 := bstep (se 1 (by rfl) ⟨1862267, by rfl⟩ : syracuseStep 2483023 = 3724535) B3724535
theorem B3310697 : Blo 2205435 3310697 := bstep (se 2 (by rfl) ⟨1241511, by rfl⟩ : syracuseStep 3310697 = 2483023) B2483023
theorem B2207131 : Blo 2205435 2207131 := bstep (se 1 (by rfl) ⟨1655348, by rfl⟩ : syracuseStep 2207131 = 3310697) B3310697
theorem B14141621 : Blo 2205435 14141621 := bbase (se 5 (by rfl) ⟨662888, by rfl⟩ : syracuseStep 14141621 = 1325777) (by norm_num)
theorem B9427747 : Blo 2205435 9427747 := bstep (se 1 (by rfl) ⟨7070810, by rfl⟩ : syracuseStep 9427747 = 14141621) B14141621
theorem B12570329 : Blo 2205435 12570329 := bstep (se 2 (by rfl) ⟨4713873, by rfl⟩ : syracuseStep 12570329 = 9427747) B9427747
theorem B8380219 : Blo 2205435 8380219 := bstep (se 1 (by rfl) ⟨6285164, by rfl⟩ : syracuseStep 8380219 = 12570329) B12570329
theorem B11173625 : Blo 2205435 11173625 := bstep (se 2 (by rfl) ⟨4190109, by rfl⟩ : syracuseStep 11173625 = 8380219) B8380219
theorem B7449083 : Blo 2205435 7449083 := bstep (se 1 (by rfl) ⟨5586812, by rfl⟩ : syracuseStep 7449083 = 11173625) B11173625
theorem B4966055 : Blo 2205435 4966055 := bstep (se 1 (by rfl) ⟨3724541, by rfl⟩ : syracuseStep 4966055 = 7449083) B7449083
theorem B3310703 : Blo 2205435 3310703 := bstep (se 1 (by rfl) ⟨2483027, by rfl⟩ : syracuseStep 3310703 = 4966055) B4966055
theorem B2207135 : Blo 2205435 2207135 := bstep (se 1 (by rfl) ⟨1655351, by rfl⟩ : syracuseStep 2207135 = 3310703) B3310703
theorem B3310709 : Blo 2205435 3310709 := bbase (se 5 (by rfl) ⟨155189, by rfl⟩ : syracuseStep 3310709 = 310379) (by norm_num)
theorem B2207139 : Blo 2205435 2207139 := bstep (se 1 (by rfl) ⟨1655354, by rfl⟩ : syracuseStep 2207139 = 3310709) B3310709
theorem B4190125 : Blo 2205435 4190125 := bbase (se 3 (by rfl) ⟨785648, by rfl⟩ : syracuseStep 4190125 = 1571297) (by norm_num)
theorem B5586833 : Blo 2205435 5586833 := bstep (se 2 (by rfl) ⟨2095062, by rfl⟩ : syracuseStep 5586833 = 4190125) B4190125
theorem B3724555 : Blo 2205435 3724555 := bstep (se 1 (by rfl) ⟨2793416, by rfl⟩ : syracuseStep 3724555 = 5586833) B5586833
theorem B4966073 : Blo 2205435 4966073 := bstep (se 2 (by rfl) ⟨1862277, by rfl⟩ : syracuseStep 4966073 = 3724555) B3724555
theorem B3310715 : Blo 2205435 3310715 := bstep (se 1 (by rfl) ⟨2483036, by rfl⟩ : syracuseStep 3310715 = 4966073) B4966073
theorem B2207143 : Blo 2205435 2207143 := bstep (se 1 (by rfl) ⟨1655357, by rfl⟩ : syracuseStep 2207143 = 3310715) B3310715
theorem B2483041 : Blo 2205435 2483041 := bbase (se 2 (by rfl) ⟨931140, by rfl⟩ : syracuseStep 2483041 = 1862281) (by norm_num)
theorem B3310721 : Blo 2205435 3310721 := bstep (se 2 (by rfl) ⟨1241520, by rfl⟩ : syracuseStep 3310721 = 2483041) B2483041
theorem B2207147 : Blo 2205435 2207147 := bstep (se 1 (by rfl) ⟨1655360, by rfl⟩ : syracuseStep 2207147 = 3310721) B3310721
theorem B5586853 : Blo 2205435 5586853 := bbase (se 4 (by rfl) ⟨523767, by rfl⟩ : syracuseStep 5586853 = 1047535) (by norm_num)
theorem B7449137 : Blo 2205435 7449137 := bstep (se 2 (by rfl) ⟨2793426, by rfl⟩ : syracuseStep 7449137 = 5586853) B5586853
theorem B4966091 : Blo 2205435 4966091 := bstep (se 1 (by rfl) ⟨3724568, by rfl⟩ : syracuseStep 4966091 = 7449137) B7449137
theorem B3310727 : Blo 2205435 3310727 := bstep (se 1 (by rfl) ⟨2483045, by rfl⟩ : syracuseStep 3310727 = 4966091) B4966091
theorem B2207151 : Blo 2205435 2207151 := bstep (se 1 (by rfl) ⟨1655363, by rfl⟩ : syracuseStep 2207151 = 3310727) B3310727
theorem B3310733 : Blo 2205435 3310733 := bbase (se 3 (by rfl) ⟨620762, by rfl⟩ : syracuseStep 3310733 = 1241525) (by norm_num)
theorem B2207155 : Blo 2205435 2207155 := bstep (se 1 (by rfl) ⟨1655366, by rfl⟩ : syracuseStep 2207155 = 3310733) B3310733
theorem B4966109 : Blo 2205435 4966109 := bbase (se 3 (by rfl) ⟨931145, by rfl⟩ : syracuseStep 4966109 = 1862291) (by norm_num)
theorem B3310739 : Blo 2205435 3310739 := bstep (se 1 (by rfl) ⟨2483054, by rfl⟩ : syracuseStep 3310739 = 4966109) B4966109
theorem B2207159 : Blo 2205435 2207159 := bstep (se 1 (by rfl) ⟨1655369, by rfl⟩ : syracuseStep 2207159 = 3310739) B3310739
theorem B3724589 : Blo 2205435 3724589 := bbase (se 3 (by rfl) ⟨698360, by rfl⟩ : syracuseStep 3724589 = 1396721) (by norm_num)
theorem B2483059 : Blo 2205435 2483059 := bstep (se 1 (by rfl) ⟨1862294, by rfl⟩ : syracuseStep 2483059 = 3724589) B3724589
theorem B3310745 : Blo 2205435 3310745 := bstep (se 2 (by rfl) ⟨1241529, by rfl⟩ : syracuseStep 3310745 = 2483059) B2483059
theorem B2207163 : Blo 2205435 2207163 := bstep (se 1 (by rfl) ⟨1655372, by rfl⟩ : syracuseStep 2207163 = 3310745) B3310745
theorem B8949125 : Blo 2205435 8949125 := bbase (se 4 (by rfl) ⟨838980, by rfl⟩ : syracuseStep 8949125 = 1677961) (by norm_num)
theorem B5966083 : Blo 2205435 5966083 := bstep (se 1 (by rfl) ⟨4474562, by rfl⟩ : syracuseStep 5966083 = 8949125) B8949125
theorem B7954777 : Blo 2205435 7954777 := bstep (se 2 (by rfl) ⟨2983041, by rfl⟩ : syracuseStep 7954777 = 5966083) B5966083
theorem B42425477 : Blo 2205435 42425477 := bstep (se 4 (by rfl) ⟨3977388, by rfl⟩ : syracuseStep 42425477 = 7954777) B7954777
theorem B28283651 : Blo 2205435 28283651 := bstep (se 1 (by rfl) ⟨21212738, by rfl⟩ : syracuseStep 28283651 = 42425477) B42425477
theorem B18855767 : Blo 2205435 18855767 := bstep (se 1 (by rfl) ⟨14141825, by rfl⟩ : syracuseStep 18855767 = 28283651) B28283651
theorem B12570511 : Blo 2205435 12570511 := bstep (se 1 (by rfl) ⟨9427883, by rfl⟩ : syracuseStep 12570511 = 18855767) B18855767
theorem B16760681 : Blo 2205435 16760681 := bstep (se 2 (by rfl) ⟨6285255, by rfl⟩ : syracuseStep 16760681 = 12570511) B12570511
theorem B11173787 : Blo 2205435 11173787 := bstep (se 1 (by rfl) ⟨8380340, by rfl⟩ : syracuseStep 11173787 = 16760681) B16760681
theorem B7449191 : Blo 2205435 7449191 := bstep (se 1 (by rfl) ⟨5586893, by rfl⟩ : syracuseStep 7449191 = 11173787) B11173787
theorem B4966127 : Blo 2205435 4966127 := bstep (se 1 (by rfl) ⟨3724595, by rfl⟩ : syracuseStep 4966127 = 7449191) B7449191
theorem B3310751 : Blo 2205435 3310751 := bstep (se 1 (by rfl) ⟨2483063, by rfl⟩ : syracuseStep 3310751 = 4966127) B4966127
theorem B2207167 : Blo 2205435 2207167 := bstep (se 1 (by rfl) ⟨1655375, by rfl⟩ : syracuseStep 2207167 = 3310751) B3310751
theorem B3310757 : Blo 2205435 3310757 := bbase (se 4 (by rfl) ⟨310383, by rfl⟩ : syracuseStep 3310757 = 620767) (by norm_num)
theorem B2207171 : Blo 2205435 2207171 := bstep (se 1 (by rfl) ⟨1655378, by rfl⟩ : syracuseStep 2207171 = 3310757) B3310757
theorem B2793457 : Blo 2205435 2793457 := bbase (se 2 (by rfl) ⟨1047546, by rfl⟩ : syracuseStep 2793457 = 2095093) (by norm_num)
theorem B3724609 : Blo 2205435 3724609 := bstep (se 2 (by rfl) ⟨1396728, by rfl⟩ : syracuseStep 3724609 = 2793457) B2793457
theorem B4966145 : Blo 2205435 4966145 := bstep (se 2 (by rfl) ⟨1862304, by rfl⟩ : syracuseStep 4966145 = 3724609) B3724609
theorem B3310763 : Blo 2205435 3310763 := bstep (se 1 (by rfl) ⟨2483072, by rfl⟩ : syracuseStep 3310763 = 4966145) B4966145
theorem B2207175 : Blo 2205435 2207175 := bstep (se 1 (by rfl) ⟨1655381, by rfl⟩ : syracuseStep 2207175 = 3310763) B3310763
theorem B2483077 : Blo 2205435 2483077 := bbase (se 4 (by rfl) ⟨232788, by rfl⟩ : syracuseStep 2483077 = 465577) (by norm_num)
theorem B3310769 : Blo 2205435 3310769 := bstep (se 2 (by rfl) ⟨1241538, by rfl⟩ : syracuseStep 3310769 = 2483077) B2483077
theorem B2207179 : Blo 2205435 2207179 := bstep (se 1 (by rfl) ⟨1655384, by rfl⟩ : syracuseStep 2207179 = 3310769) B3310769
theorem B4474597 : Blo 2205435 4474597 := bbase (se 4 (by rfl) ⟨419493, by rfl⟩ : syracuseStep 4474597 = 838987) (by norm_num)
theorem B5966129 : Blo 2205435 5966129 := bstep (se 2 (by rfl) ⟨2237298, by rfl⟩ : syracuseStep 5966129 = 4474597) B4474597
theorem B3977419 : Blo 2205435 3977419 := bstep (se 1 (by rfl) ⟨2983064, by rfl⟩ : syracuseStep 3977419 = 5966129) B5966129
theorem B5303225 : Blo 2205435 5303225 := bstep (se 2 (by rfl) ⟨1988709, by rfl⟩ : syracuseStep 5303225 = 3977419) B3977419
theorem B3535483 : Blo 2205435 3535483 := bstep (se 1 (by rfl) ⟨2651612, by rfl⟩ : syracuseStep 3535483 = 5303225) B5303225
theorem B4713977 : Blo 2205435 4713977 := bstep (se 2 (by rfl) ⟨1767741, by rfl⟩ : syracuseStep 4713977 = 3535483) B3535483
theorem B3142651 : Blo 2205435 3142651 := bstep (se 1 (by rfl) ⟨2356988, by rfl⟩ : syracuseStep 3142651 = 4713977) B4713977
theorem B4190201 : Blo 2205435 4190201 := bstep (se 2 (by rfl) ⟨1571325, by rfl⟩ : syracuseStep 4190201 = 3142651) B3142651
theorem B2793467 : Blo 2205435 2793467 := bstep (se 1 (by rfl) ⟨2095100, by rfl⟩ : syracuseStep 2793467 = 4190201) B4190201
theorem B7449245 : Blo 2205435 7449245 := bstep (se 3 (by rfl) ⟨1396733, by rfl⟩ : syracuseStep 7449245 = 2793467) B2793467
theorem B4966163 : Blo 2205435 4966163 := bstep (se 1 (by rfl) ⟨3724622, by rfl⟩ : syracuseStep 4966163 = 7449245) B7449245
theorem B3310775 : Blo 2205435 3310775 := bstep (se 1 (by rfl) ⟨2483081, by rfl⟩ : syracuseStep 3310775 = 4966163) B4966163
theorem B2207183 : Blo 2205435 2207183 := bstep (se 1 (by rfl) ⟨1655387, by rfl⟩ : syracuseStep 2207183 = 3310775) B3310775
theorem B3310781 : Blo 2205435 3310781 := bbase (se 3 (by rfl) ⟨620771, by rfl⟩ : syracuseStep 3310781 = 1241543) (by norm_num)
theorem B2207187 : Blo 2205435 2207187 := bstep (se 1 (by rfl) ⟨1655390, by rfl⟩ : syracuseStep 2207187 = 3310781) B3310781
theorem B4966181 : Blo 2205435 4966181 := bbase (se 4 (by rfl) ⟨465579, by rfl⟩ : syracuseStep 4966181 = 931159) (by norm_num)
theorem B3310787 : Blo 2205435 3310787 := bstep (se 1 (by rfl) ⟨2483090, by rfl⟩ : syracuseStep 3310787 = 4966181) B4966181
theorem B2207191 : Blo 2205435 2207191 := bstep (se 1 (by rfl) ⟨1655393, by rfl⟩ : syracuseStep 2207191 = 3310787) B3310787
theorem B5586965 : Blo 2205435 5586965 := bbase (se 6 (by rfl) ⟨130944, by rfl⟩ : syracuseStep 5586965 = 261889) (by norm_num)
theorem B3724643 : Blo 2205435 3724643 := bstep (se 1 (by rfl) ⟨2793482, by rfl⟩ : syracuseStep 3724643 = 5586965) B5586965
theorem B2483095 : Blo 2205435 2483095 := bstep (se 1 (by rfl) ⟨1862321, by rfl⟩ : syracuseStep 2483095 = 3724643) B3724643
theorem B3310793 : Blo 2205435 3310793 := bstep (se 2 (by rfl) ⟨1241547, by rfl⟩ : syracuseStep 3310793 = 2483095) B2483095
theorem B2207195 : Blo 2205435 2207195 := bstep (se 1 (by rfl) ⟨1655396, by rfl⟩ : syracuseStep 2207195 = 3310793) B3310793
theorem B9428021 : Blo 2205435 9428021 := bbase (se 5 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 9428021 = 883877) (by norm_num)
theorem B6285347 : Blo 2205435 6285347 := bstep (se 1 (by rfl) ⟨4714010, by rfl⟩ : syracuseStep 6285347 = 9428021) B9428021
theorem B4190231 : Blo 2205435 4190231 := bstep (se 1 (by rfl) ⟨3142673, by rfl⟩ : syracuseStep 4190231 = 6285347) B6285347
theorem B11173949 : Blo 2205435 11173949 := bstep (se 3 (by rfl) ⟨2095115, by rfl⟩ : syracuseStep 11173949 = 4190231) B4190231
theorem B7449299 : Blo 2205435 7449299 := bstep (se 1 (by rfl) ⟨5586974, by rfl⟩ : syracuseStep 7449299 = 11173949) B11173949
theorem B4966199 : Blo 2205435 4966199 := bstep (se 1 (by rfl) ⟨3724649, by rfl⟩ : syracuseStep 4966199 = 7449299) B7449299
theorem B3310799 : Blo 2205435 3310799 := bstep (se 1 (by rfl) ⟨2483099, by rfl⟩ : syracuseStep 3310799 = 4966199) B4966199
theorem B2207199 : Blo 2205435 2207199 := bstep (se 1 (by rfl) ⟨1655399, by rfl⟩ : syracuseStep 2207199 = 3310799) B3310799
theorem B3310805 : Blo 2205435 3310805 := bbase (se 7 (by rfl) ⟨38798, by rfl⟩ : syracuseStep 3310805 = 77597) (by norm_num)
theorem B2207203 : Blo 2205435 2207203 := bstep (se 1 (by rfl) ⟨1655402, by rfl⟩ : syracuseStep 2207203 = 3310805) B3310805
theorem B3142685 : Blo 2205435 3142685 := bbase (se 3 (by rfl) ⟨589253, by rfl⟩ : syracuseStep 3142685 = 1178507) (by norm_num)
theorem B8380493 : Blo 2205435 8380493 := bstep (se 3 (by rfl) ⟨1571342, by rfl⟩ : syracuseStep 8380493 = 3142685) B3142685
theorem B5586995 : Blo 2205435 5586995 := bstep (se 1 (by rfl) ⟨4190246, by rfl⟩ : syracuseStep 5586995 = 8380493) B8380493
theorem B3724663 : Blo 2205435 3724663 := bstep (se 1 (by rfl) ⟨2793497, by rfl⟩ : syracuseStep 3724663 = 5586995) B5586995
theorem B4966217 : Blo 2205435 4966217 := bstep (se 2 (by rfl) ⟨1862331, by rfl⟩ : syracuseStep 4966217 = 3724663) B3724663
theorem B3310811 : Blo 2205435 3310811 := bstep (se 1 (by rfl) ⟨2483108, by rfl⟩ : syracuseStep 3310811 = 4966217) B4966217
theorem B2207207 : Blo 2205435 2207207 := bstep (se 1 (by rfl) ⟨1655405, by rfl⟩ : syracuseStep 2207207 = 3310811) B3310811
theorem B2483113 : Blo 2205435 2483113 := bbase (se 2 (by rfl) ⟨931167, by rfl⟩ : syracuseStep 2483113 = 1862335) (by norm_num)
theorem B3310817 : Blo 2205435 3310817 := bstep (se 2 (by rfl) ⟨1241556, by rfl⟩ : syracuseStep 3310817 = 2483113) B2483113
theorem B2207211 : Blo 2205435 2207211 := bstep (se 1 (by rfl) ⟨1655408, by rfl⟩ : syracuseStep 2207211 = 3310817) B3310817
theorem B2389181 : Blo 2205435 2389181 := bbase (se 3 (by rfl) ⟨447971, by rfl⟩ : syracuseStep 2389181 = 895943) (by norm_num)
theorem B6371149 : Blo 2205435 6371149 := bstep (se 3 (by rfl) ⟨1194590, by rfl⟩ : syracuseStep 6371149 = 2389181) B2389181
theorem B8494865 : Blo 2205435 8494865 := bstep (se 2 (by rfl) ⟨3185574, by rfl⟩ : syracuseStep 8494865 = 6371149) B6371149
theorem B5663243 : Blo 2205435 5663243 := bstep (se 1 (by rfl) ⟨4247432, by rfl⟩ : syracuseStep 5663243 = 8494865) B8494865
theorem B3775495 : Blo 2205435 3775495 := bstep (se 1 (by rfl) ⟨2831621, by rfl⟩ : syracuseStep 3775495 = 5663243) B5663243
theorem B5033993 : Blo 2205435 5033993 := bstep (se 2 (by rfl) ⟨1887747, by rfl⟩ : syracuseStep 5033993 = 3775495) B3775495
theorem B13423981 : Blo 2205435 13423981 := bstep (se 3 (by rfl) ⟨2516996, by rfl⟩ : syracuseStep 13423981 = 5033993) B5033993
theorem B17898641 : Blo 2205435 17898641 := bstep (se 2 (by rfl) ⟨6711990, by rfl⟩ : syracuseStep 17898641 = 13423981) B13423981
theorem B11932427 : Blo 2205435 11932427 := bstep (se 1 (by rfl) ⟨8949320, by rfl⟩ : syracuseStep 11932427 = 17898641) B17898641
theorem B7954951 : Blo 2205435 7954951 := bstep (se 1 (by rfl) ⟨5966213, by rfl⟩ : syracuseStep 7954951 = 11932427) B11932427
theorem B10606601 : Blo 2205435 10606601 := bstep (se 2 (by rfl) ⟨3977475, by rfl⟩ : syracuseStep 10606601 = 7954951) B7954951
theorem B7071067 : Blo 2205435 7071067 := bstep (se 1 (by rfl) ⟨5303300, by rfl⟩ : syracuseStep 7071067 = 10606601) B10606601
theorem B9428089 : Blo 2205435 9428089 := bstep (se 2 (by rfl) ⟨3535533, by rfl⟩ : syracuseStep 9428089 = 7071067) B7071067
theorem B12570785 : Blo 2205435 12570785 := bstep (se 2 (by rfl) ⟨4714044, by rfl⟩ : syracuseStep 12570785 = 9428089) B9428089
theorem B8380523 : Blo 2205435 8380523 := bstep (se 1 (by rfl) ⟨6285392, by rfl⟩ : syracuseStep 8380523 = 12570785) B12570785
theorem B5587015 : Blo 2205435 5587015 := bstep (se 1 (by rfl) ⟨4190261, by rfl⟩ : syracuseStep 5587015 = 8380523) B8380523
theorem B7449353 : Blo 2205435 7449353 := bstep (se 2 (by rfl) ⟨2793507, by rfl⟩ : syracuseStep 7449353 = 5587015) B5587015
theorem B4966235 : Blo 2205435 4966235 := bstep (se 1 (by rfl) ⟨3724676, by rfl⟩ : syracuseStep 4966235 = 7449353) B7449353
theorem B3310823 : Blo 2205435 3310823 := bstep (se 1 (by rfl) ⟨2483117, by rfl⟩ : syracuseStep 3310823 = 4966235) B4966235
theorem B2207215 : Blo 2205435 2207215 := bstep (se 1 (by rfl) ⟨1655411, by rfl⟩ : syracuseStep 2207215 = 3310823) B3310823
theorem B3310829 : Blo 2205435 3310829 := bbase (se 3 (by rfl) ⟨620780, by rfl⟩ : syracuseStep 3310829 = 1241561) (by norm_num)
theorem B2207219 : Blo 2205435 2207219 := bstep (se 1 (by rfl) ⟨1655414, by rfl⟩ : syracuseStep 2207219 = 3310829) B3310829
theorem B4966253 : Blo 2205435 4966253 := bbase (se 3 (by rfl) ⟨931172, by rfl⟩ : syracuseStep 4966253 = 1862345) (by norm_num)
theorem B3310835 : Blo 2205435 3310835 := bstep (se 1 (by rfl) ⟨2483126, by rfl⟩ : syracuseStep 3310835 = 4966253) B4966253
theorem B2207223 : Blo 2205435 2207223 := bstep (se 1 (by rfl) ⟨1655417, by rfl⟩ : syracuseStep 2207223 = 3310835) B3310835
theorem B4190285 : Blo 2205435 4190285 := bbase (se 3 (by rfl) ⟨785678, by rfl⟩ : syracuseStep 4190285 = 1571357) (by norm_num)
theorem B2793523 : Blo 2205435 2793523 := bstep (se 1 (by rfl) ⟨2095142, by rfl⟩ : syracuseStep 2793523 = 4190285) B4190285
theorem B3724697 : Blo 2205435 3724697 := bstep (se 2 (by rfl) ⟨1396761, by rfl⟩ : syracuseStep 3724697 = 2793523) B2793523
theorem B2483131 : Blo 2205435 2483131 := bstep (se 1 (by rfl) ⟨1862348, by rfl⟩ : syracuseStep 2483131 = 3724697) B3724697
theorem B3310841 : Blo 2205435 3310841 := bstep (se 2 (by rfl) ⟨1241565, by rfl⟩ : syracuseStep 3310841 = 2483131) B2483131
theorem B2207227 : Blo 2205435 2207227 := bstep (se 1 (by rfl) ⟨1655420, by rfl⟩ : syracuseStep 2207227 = 3310841) B3310841
theorem B5449037 : Blo 2205435 5449037 := bbase (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) (by norm_num)
theorem B14530765 : Blo 2205435 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B19374353 : Blo 2205435 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B12916235 : Blo 2205435 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B8610823 : Blo 2205435 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B11481097 : Blo 2205435 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B15308129 : Blo 2205435 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B40821677 : Blo 2205435 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B27214451 : Blo 2205435 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B18142967 : Blo 2205435 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B48381245 : Blo 2205435 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B32254163 : Blo 2205435 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B21502775 : Blo 2205435 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B14335183 : Blo 2205435 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B19113577 : Blo 2205435 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B101939077 : Blo 2205435 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B135918769 : Blo 2205435 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B181225025 : Blo 2205435 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B120816683 : Blo 2205435 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B80544455 : Blo 2205435 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B53696303 : Blo 2205435 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B35797535 : Blo 2205435 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B23865023 : Blo 2205435 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B15910015 : Blo 2205435 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B21213353 : Blo 2205435 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B56568941 : Blo 2205435 56568941 := bstep (se 3 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 56568941 = 21213353) B21213353
theorem B37712627 : Blo 2205435 37712627 := bstep (se 1 (by rfl) ⟨28284470, by rfl⟩ : syracuseStep 37712627 = 56568941) B56568941
theorem B25141751 : Blo 2205435 25141751 := bstep (se 1 (by rfl) ⟨18856313, by rfl⟩ : syracuseStep 25141751 = 37712627) B37712627
theorem B16761167 : Blo 2205435 16761167 := bstep (se 1 (by rfl) ⟨12570875, by rfl⟩ : syracuseStep 16761167 = 25141751) B25141751
theorem B11174111 : Blo 2205435 11174111 := bstep (se 1 (by rfl) ⟨8380583, by rfl⟩ : syracuseStep 11174111 = 16761167) B16761167
theorem B7449407 : Blo 2205435 7449407 := bstep (se 1 (by rfl) ⟨5587055, by rfl⟩ : syracuseStep 7449407 = 11174111) B11174111
theorem B4966271 : Blo 2205435 4966271 := bstep (se 1 (by rfl) ⟨3724703, by rfl⟩ : syracuseStep 4966271 = 7449407) B7449407
theorem B3310847 : Blo 2205435 3310847 := bstep (se 1 (by rfl) ⟨2483135, by rfl⟩ : syracuseStep 3310847 = 4966271) B4966271
theorem B2207231 : Blo 2205435 2207231 := bstep (se 1 (by rfl) ⟨1655423, by rfl⟩ : syracuseStep 2207231 = 3310847) B3310847
theorem B3310853 : Blo 2205435 3310853 := bbase (se 4 (by rfl) ⟨310392, by rfl⟩ : syracuseStep 3310853 = 620785) (by norm_num)
theorem B2207235 : Blo 2205435 2207235 := bstep (se 1 (by rfl) ⟨1655426, by rfl⟩ : syracuseStep 2207235 = 3310853) B3310853
theorem B3724717 : Blo 2205435 3724717 := bbase (se 3 (by rfl) ⟨698384, by rfl⟩ : syracuseStep 3724717 = 1396769) (by norm_num)
theorem B4966289 : Blo 2205435 4966289 := bstep (se 2 (by rfl) ⟨1862358, by rfl⟩ : syracuseStep 4966289 = 3724717) B3724717
theorem B3310859 : Blo 2205435 3310859 := bstep (se 1 (by rfl) ⟨2483144, by rfl⟩ : syracuseStep 3310859 = 4966289) B4966289
theorem B2207239 : Blo 2205435 2207239 := bstep (se 1 (by rfl) ⟨1655429, by rfl⟩ : syracuseStep 2207239 = 3310859) B3310859
theorem B2483149 : Blo 2205435 2483149 := bbase (se 3 (by rfl) ⟨465590, by rfl⟩ : syracuseStep 2483149 = 931181) (by norm_num)
theorem B3310865 : Blo 2205435 3310865 := bstep (se 2 (by rfl) ⟨1241574, by rfl⟩ : syracuseStep 3310865 = 2483149) B2483149
theorem B2207243 : Blo 2205435 2207243 := bstep (se 1 (by rfl) ⟨1655432, by rfl⟩ : syracuseStep 2207243 = 3310865) B3310865
theorem B7449461 : Blo 2205435 7449461 := bbase (se 5 (by rfl) ⟨349193, by rfl⟩ : syracuseStep 7449461 = 698387) (by norm_num)
theorem B4966307 : Blo 2205435 4966307 := bstep (se 1 (by rfl) ⟨3724730, by rfl⟩ : syracuseStep 4966307 = 7449461) B7449461
theorem B3310871 : Blo 2205435 3310871 := bstep (se 1 (by rfl) ⟨2483153, by rfl⟩ : syracuseStep 3310871 = 4966307) B4966307
theorem B2207247 : Blo 2205435 2207247 := bstep (se 1 (by rfl) ⟨1655435, by rfl⟩ : syracuseStep 2207247 = 3310871) B3310871
theorem B3310877 : Blo 2205435 3310877 := bbase (se 3 (by rfl) ⟨620789, by rfl⟩ : syracuseStep 3310877 = 1241579) (by norm_num)
theorem B2207251 : Blo 2205435 2207251 := bstep (se 1 (by rfl) ⟨1655438, by rfl⟩ : syracuseStep 2207251 = 3310877) B3310877
theorem B4966325 : Blo 2205435 4966325 := bbase (se 5 (by rfl) ⟨232796, by rfl⟩ : syracuseStep 4966325 = 465593) (by norm_num)
theorem B3310883 : Blo 2205435 3310883 := bstep (se 1 (by rfl) ⟨2483162, by rfl⟩ : syracuseStep 3310883 = 4966325) B4966325
theorem B2207255 : Blo 2205435 2207255 := bstep (se 1 (by rfl) ⟨1655441, by rfl⟩ : syracuseStep 2207255 = 3310883) B3310883
theorem B16990069 : Blo 2205435 16990069 := bbase (se 5 (by rfl) ⟨796409, by rfl⟩ : syracuseStep 16990069 = 1592819) (by norm_num)
theorem B22653425 : Blo 2205435 22653425 := bstep (se 2 (by rfl) ⟨8495034, by rfl⟩ : syracuseStep 22653425 = 16990069) B16990069
theorem B15102283 : Blo 2205435 15102283 := bstep (se 1 (by rfl) ⟨11326712, by rfl⟩ : syracuseStep 15102283 = 22653425) B22653425
theorem B20136377 : Blo 2205435 20136377 := bstep (se 2 (by rfl) ⟨7551141, by rfl⟩ : syracuseStep 20136377 = 15102283) B15102283
theorem B13424251 : Blo 2205435 13424251 := bstep (se 1 (by rfl) ⟨10068188, by rfl⟩ : syracuseStep 13424251 = 20136377) B20136377
theorem B17899001 : Blo 2205435 17899001 := bstep (se 2 (by rfl) ⟨6712125, by rfl⟩ : syracuseStep 17899001 = 13424251) B13424251
theorem B11932667 : Blo 2205435 11932667 := bstep (se 1 (by rfl) ⟨8949500, by rfl⟩ : syracuseStep 11932667 = 17899001) B17899001
theorem B7955111 : Blo 2205435 7955111 := bstep (se 1 (by rfl) ⟨5966333, by rfl⟩ : syracuseStep 7955111 = 11932667) B11932667
theorem B5303407 : Blo 2205435 5303407 := bstep (se 1 (by rfl) ⟨3977555, by rfl⟩ : syracuseStep 5303407 = 7955111) B7955111
theorem B7071209 : Blo 2205435 7071209 := bstep (se 2 (by rfl) ⟨2651703, by rfl⟩ : syracuseStep 7071209 = 5303407) B5303407
theorem B4714139 : Blo 2205435 4714139 := bstep (se 1 (by rfl) ⟨3535604, by rfl⟩ : syracuseStep 4714139 = 7071209) B7071209
theorem B12571037 : Blo 2205435 12571037 := bstep (se 3 (by rfl) ⟨2357069, by rfl⟩ : syracuseStep 12571037 = 4714139) B4714139
theorem B8380691 : Blo 2205435 8380691 := bstep (se 1 (by rfl) ⟨6285518, by rfl⟩ : syracuseStep 8380691 = 12571037) B12571037
theorem B5587127 : Blo 2205435 5587127 := bstep (se 1 (by rfl) ⟨4190345, by rfl⟩ : syracuseStep 5587127 = 8380691) B8380691
theorem B3724751 : Blo 2205435 3724751 := bstep (se 1 (by rfl) ⟨2793563, by rfl⟩ : syracuseStep 3724751 = 5587127) B5587127
theorem B2483167 : Blo 2205435 2483167 := bstep (se 1 (by rfl) ⟨1862375, by rfl⟩ : syracuseStep 2483167 = 3724751) B3724751
theorem B3310889 : Blo 2205435 3310889 := bstep (se 2 (by rfl) ⟨1241583, by rfl⟩ : syracuseStep 3310889 = 2483167) B2483167
theorem B2207259 : Blo 2205435 2207259 := bstep (se 1 (by rfl) ⟨1655444, by rfl⟩ : syracuseStep 2207259 = 3310889) B3310889
theorem B7071221 : Blo 2205435 7071221 := bbase (se 5 (by rfl) ⟨331463, by rfl⟩ : syracuseStep 7071221 = 662927) (by norm_num)
theorem B4714147 : Blo 2205435 4714147 := bstep (se 1 (by rfl) ⟨3535610, by rfl⟩ : syracuseStep 4714147 = 7071221) B7071221
theorem B6285529 : Blo 2205435 6285529 := bstep (se 2 (by rfl) ⟨2357073, by rfl⟩ : syracuseStep 6285529 = 4714147) B4714147
theorem B8380705 : Blo 2205435 8380705 := bstep (se 2 (by rfl) ⟨3142764, by rfl⟩ : syracuseStep 8380705 = 6285529) B6285529
theorem B11174273 : Blo 2205435 11174273 := bstep (se 2 (by rfl) ⟨4190352, by rfl⟩ : syracuseStep 11174273 = 8380705) B8380705
theorem B7449515 : Blo 2205435 7449515 := bstep (se 1 (by rfl) ⟨5587136, by rfl⟩ : syracuseStep 7449515 = 11174273) B11174273
theorem B4966343 : Blo 2205435 4966343 := bstep (se 1 (by rfl) ⟨3724757, by rfl⟩ : syracuseStep 4966343 = 7449515) B7449515
theorem B3310895 : Blo 2205435 3310895 := bstep (se 1 (by rfl) ⟨2483171, by rfl⟩ : syracuseStep 3310895 = 4966343) B4966343
theorem B2207263 : Blo 2205435 2207263 := bstep (se 1 (by rfl) ⟨1655447, by rfl⟩ : syracuseStep 2207263 = 3310895) B3310895
theorem B3310901 : Blo 2205435 3310901 := bbase (se 5 (by rfl) ⟨155198, by rfl⟩ : syracuseStep 3310901 = 310397) (by norm_num)
theorem B2207267 : Blo 2205435 2207267 := bstep (se 1 (by rfl) ⟨1655450, by rfl⟩ : syracuseStep 2207267 = 3310901) B3310901
theorem B5587157 : Blo 2205435 5587157 := bbase (se 7 (by rfl) ⟨65474, by rfl⟩ : syracuseStep 5587157 = 130949) (by norm_num)
theorem B3724771 : Blo 2205435 3724771 := bstep (se 1 (by rfl) ⟨2793578, by rfl⟩ : syracuseStep 3724771 = 5587157) B5587157
theorem B4966361 : Blo 2205435 4966361 := bstep (se 2 (by rfl) ⟨1862385, by rfl⟩ : syracuseStep 4966361 = 3724771) B3724771
theorem B3310907 : Blo 2205435 3310907 := bstep (se 1 (by rfl) ⟨2483180, by rfl⟩ : syracuseStep 3310907 = 4966361) B4966361
theorem B2207271 : Blo 2205435 2207271 := bstep (se 1 (by rfl) ⟨1655453, by rfl⟩ : syracuseStep 2207271 = 3310907) B3310907
theorem B2483185 : Blo 2205435 2483185 := bbase (se 2 (by rfl) ⟨931194, by rfl⟩ : syracuseStep 2483185 = 1862389) (by norm_num)
theorem B3310913 : Blo 2205435 3310913 := bstep (se 2 (by rfl) ⟨1241592, by rfl⟩ : syracuseStep 3310913 = 2483185) B2483185
theorem B2207275 : Blo 2205435 2207275 := bstep (se 1 (by rfl) ⟨1655456, by rfl⟩ : syracuseStep 2207275 = 3310913) B3310913
theorem B3356093 : Blo 2205435 3356093 := bbase (se 3 (by rfl) ⟨629267, by rfl⟩ : syracuseStep 3356093 = 1258535) (by norm_num)
theorem B8949581 : Blo 2205435 8949581 := bstep (se 3 (by rfl) ⟨1678046, by rfl⟩ : syracuseStep 8949581 = 3356093) B3356093
theorem B5966387 : Blo 2205435 5966387 := bstep (se 1 (by rfl) ⟨4474790, by rfl⟩ : syracuseStep 5966387 = 8949581) B8949581
theorem B3977591 : Blo 2205435 3977591 := bstep (se 1 (by rfl) ⟨2983193, by rfl⟩ : syracuseStep 3977591 = 5966387) B5966387
theorem B10606909 : Blo 2205435 10606909 := bstep (se 3 (by rfl) ⟨1988795, by rfl⟩ : syracuseStep 10606909 = 3977591) B3977591
theorem B14142545 : Blo 2205435 14142545 := bstep (se 2 (by rfl) ⟨5303454, by rfl⟩ : syracuseStep 14142545 = 10606909) B10606909
theorem B9428363 : Blo 2205435 9428363 := bstep (se 1 (by rfl) ⟨7071272, by rfl⟩ : syracuseStep 9428363 = 14142545) B14142545
theorem B6285575 : Blo 2205435 6285575 := bstep (se 1 (by rfl) ⟨4714181, by rfl⟩ : syracuseStep 6285575 = 9428363) B9428363
theorem B4190383 : Blo 2205435 4190383 := bstep (se 1 (by rfl) ⟨3142787, by rfl⟩ : syracuseStep 4190383 = 6285575) B6285575
theorem B5587177 : Blo 2205435 5587177 := bstep (se 2 (by rfl) ⟨2095191, by rfl⟩ : syracuseStep 5587177 = 4190383) B4190383
theorem B7449569 : Blo 2205435 7449569 := bstep (se 2 (by rfl) ⟨2793588, by rfl⟩ : syracuseStep 7449569 = 5587177) B5587177
theorem B4966379 : Blo 2205435 4966379 := bstep (se 1 (by rfl) ⟨3724784, by rfl⟩ : syracuseStep 4966379 = 7449569) B7449569
theorem B3310919 : Blo 2205435 3310919 := bstep (se 1 (by rfl) ⟨2483189, by rfl⟩ : syracuseStep 3310919 = 4966379) B4966379
theorem B2207279 : Blo 2205435 2207279 := bstep (se 1 (by rfl) ⟨1655459, by rfl⟩ : syracuseStep 2207279 = 3310919) B3310919
theorem B3310925 : Blo 2205435 3310925 := bbase (se 3 (by rfl) ⟨620798, by rfl⟩ : syracuseStep 3310925 = 1241597) (by norm_num)
theorem B2207283 : Blo 2205435 2207283 := bstep (se 1 (by rfl) ⟨1655462, by rfl⟩ : syracuseStep 2207283 = 3310925) B3310925
theorem B4966397 : Blo 2205435 4966397 := bbase (se 3 (by rfl) ⟨931199, by rfl⟩ : syracuseStep 4966397 = 1862399) (by norm_num)
theorem B3310931 : Blo 2205435 3310931 := bstep (se 1 (by rfl) ⟨2483198, by rfl⟩ : syracuseStep 3310931 = 4966397) B4966397
theorem B2207287 : Blo 2205435 2207287 := bstep (se 1 (by rfl) ⟨1655465, by rfl⟩ : syracuseStep 2207287 = 3310931) B3310931
theorem B3724805 : Blo 2205435 3724805 := bbase (se 4 (by rfl) ⟨349200, by rfl⟩ : syracuseStep 3724805 = 698401) (by norm_num)
theorem B2483203 : Blo 2205435 2483203 := bstep (se 1 (by rfl) ⟨1862402, by rfl⟩ : syracuseStep 2483203 = 3724805) B3724805
theorem B3310937 : Blo 2205435 3310937 := bstep (se 2 (by rfl) ⟨1241601, by rfl⟩ : syracuseStep 3310937 = 2483203) B2483203
theorem B2207291 : Blo 2205435 2207291 := bstep (se 1 (by rfl) ⟨1655468, by rfl⟩ : syracuseStep 2207291 = 3310937) B3310937
theorem B16761653 : Blo 2205435 16761653 := bbase (se 5 (by rfl) ⟨785702, by rfl⟩ : syracuseStep 16761653 = 1571405) (by norm_num)
theorem B11174435 : Blo 2205435 11174435 := bstep (se 1 (by rfl) ⟨8380826, by rfl⟩ : syracuseStep 11174435 = 16761653) B16761653
theorem B7449623 : Blo 2205435 7449623 := bstep (se 1 (by rfl) ⟨5587217, by rfl⟩ : syracuseStep 7449623 = 11174435) B11174435
theorem B4966415 : Blo 2205435 4966415 := bstep (se 1 (by rfl) ⟨3724811, by rfl⟩ : syracuseStep 4966415 = 7449623) B7449623
theorem B3310943 : Blo 2205435 3310943 := bstep (se 1 (by rfl) ⟨2483207, by rfl⟩ : syracuseStep 3310943 = 4966415) B4966415
theorem B2207295 : Blo 2205435 2207295 := bstep (se 1 (by rfl) ⟨1655471, by rfl⟩ : syracuseStep 2207295 = 3310943) B3310943
theorem B3310949 : Blo 2205435 3310949 := bbase (se 4 (by rfl) ⟨310401, by rfl⟩ : syracuseStep 3310949 = 620803) (by norm_num)
theorem B2207299 : Blo 2205435 2207299 := bstep (se 1 (by rfl) ⟨1655474, by rfl⟩ : syracuseStep 2207299 = 3310949) B3310949
theorem B4190429 : Blo 2205435 4190429 := bbase (se 3 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 4190429 = 1571411) (by norm_num)
theorem B2793619 : Blo 2205435 2793619 := bstep (se 1 (by rfl) ⟨2095214, by rfl⟩ : syracuseStep 2793619 = 4190429) B4190429
theorem B3724825 : Blo 2205435 3724825 := bstep (se 2 (by rfl) ⟨1396809, by rfl⟩ : syracuseStep 3724825 = 2793619) B2793619
theorem B4966433 : Blo 2205435 4966433 := bstep (se 2 (by rfl) ⟨1862412, by rfl⟩ : syracuseStep 4966433 = 3724825) B3724825
theorem B3310955 : Blo 2205435 3310955 := bstep (se 1 (by rfl) ⟨2483216, by rfl⟩ : syracuseStep 3310955 = 4966433) B4966433
theorem B2207303 : Blo 2205435 2207303 := bstep (se 1 (by rfl) ⟨1655477, by rfl⟩ : syracuseStep 2207303 = 3310955) B3310955
theorem B2483221 : Blo 2205435 2483221 := bbase (se 6 (by rfl) ⟨58200, by rfl⟩ : syracuseStep 2483221 = 116401) (by norm_num)
theorem B3310961 : Blo 2205435 3310961 := bstep (se 2 (by rfl) ⟨1241610, by rfl⟩ : syracuseStep 3310961 = 2483221) B2483221
theorem B2207307 : Blo 2205435 2207307 := bstep (se 1 (by rfl) ⟨1655480, by rfl⟩ : syracuseStep 2207307 = 3310961) B3310961
theorem B2793629 : Blo 2205435 2793629 := bbase (se 3 (by rfl) ⟨523805, by rfl⟩ : syracuseStep 2793629 = 1047611) (by norm_num)
theorem B7449677 : Blo 2205435 7449677 := bstep (se 3 (by rfl) ⟨1396814, by rfl⟩ : syracuseStep 7449677 = 2793629) B2793629
theorem B4966451 : Blo 2205435 4966451 := bstep (se 1 (by rfl) ⟨3724838, by rfl⟩ : syracuseStep 4966451 = 7449677) B7449677
theorem B3310967 : Blo 2205435 3310967 := bstep (se 1 (by rfl) ⟨2483225, by rfl⟩ : syracuseStep 3310967 = 4966451) B4966451
theorem B2207311 : Blo 2205435 2207311 := bstep (se 1 (by rfl) ⟨1655483, by rfl⟩ : syracuseStep 2207311 = 3310967) B3310967
theorem B3310973 : Blo 2205435 3310973 := bbase (se 3 (by rfl) ⟨620807, by rfl⟩ : syracuseStep 3310973 = 1241615) (by norm_num)
theorem B2207315 : Blo 2205435 2207315 := bstep (se 1 (by rfl) ⟨1655486, by rfl⟩ : syracuseStep 2207315 = 3310973) B3310973
theorem B4966469 : Blo 2205435 4966469 := bbase (se 4 (by rfl) ⟨465606, by rfl⟩ : syracuseStep 4966469 = 931213) (by norm_num)
theorem B3310979 : Blo 2205435 3310979 := bstep (se 1 (by rfl) ⟨2483234, by rfl⟩ : syracuseStep 3310979 = 4966469) B4966469
theorem B2207319 : Blo 2205435 2207319 := bstep (se 1 (by rfl) ⟨1655489, by rfl⟩ : syracuseStep 2207319 = 3310979) B3310979
theorem B6285701 : Blo 2205435 6285701 := bbase (se 4 (by rfl) ⟨589284, by rfl⟩ : syracuseStep 6285701 = 1178569) (by norm_num)
theorem B4190467 : Blo 2205435 4190467 := bstep (se 1 (by rfl) ⟨3142850, by rfl⟩ : syracuseStep 4190467 = 6285701) B6285701
theorem B5587289 : Blo 2205435 5587289 := bstep (se 2 (by rfl) ⟨2095233, by rfl⟩ : syracuseStep 5587289 = 4190467) B4190467
theorem B3724859 : Blo 2205435 3724859 := bstep (se 1 (by rfl) ⟨2793644, by rfl⟩ : syracuseStep 3724859 = 5587289) B5587289
theorem B2483239 : Blo 2205435 2483239 := bstep (se 1 (by rfl) ⟨1862429, by rfl⟩ : syracuseStep 2483239 = 3724859) B3724859
theorem B3310985 : Blo 2205435 3310985 := bstep (se 2 (by rfl) ⟨1241619, by rfl⟩ : syracuseStep 3310985 = 2483239) B2483239
theorem B2207323 : Blo 2205435 2207323 := bstep (se 1 (by rfl) ⟨1655492, by rfl⟩ : syracuseStep 2207323 = 3310985) B3310985
theorem B11174597 : Blo 2205435 11174597 := bbase (se 4 (by rfl) ⟨1047618, by rfl⟩ : syracuseStep 11174597 = 2095237) (by norm_num)
theorem B7449731 : Blo 2205435 7449731 := bstep (se 1 (by rfl) ⟨5587298, by rfl⟩ : syracuseStep 7449731 = 11174597) B11174597
theorem B4966487 : Blo 2205435 4966487 := bstep (se 1 (by rfl) ⟨3724865, by rfl⟩ : syracuseStep 4966487 = 7449731) B7449731
theorem B3310991 : Blo 2205435 3310991 := bstep (se 1 (by rfl) ⟨2483243, by rfl⟩ : syracuseStep 3310991 = 4966487) B4966487
theorem B2207327 : Blo 2205435 2207327 := bstep (se 1 (by rfl) ⟨1655495, by rfl⟩ : syracuseStep 2207327 = 3310991) B3310991
theorem B3310997 : Blo 2205435 3310997 := bbase (se 6 (by rfl) ⟨77601, by rfl⟩ : syracuseStep 3310997 = 155203) (by norm_num)
theorem B2207331 : Blo 2205435 2207331 := bstep (se 1 (by rfl) ⟨1655498, by rfl⟩ : syracuseStep 2207331 = 3310997) B3310997
theorem B4714301 : Blo 2205435 4714301 := bbase (se 3 (by rfl) ⟨883931, by rfl⟩ : syracuseStep 4714301 = 1767863) (by norm_num)
theorem B12571469 : Blo 2205435 12571469 := bstep (se 3 (by rfl) ⟨2357150, by rfl⟩ : syracuseStep 12571469 = 4714301) B4714301
theorem B8380979 : Blo 2205435 8380979 := bstep (se 1 (by rfl) ⟨6285734, by rfl⟩ : syracuseStep 8380979 = 12571469) B12571469
theorem B5587319 : Blo 2205435 5587319 := bstep (se 1 (by rfl) ⟨4190489, by rfl⟩ : syracuseStep 5587319 = 8380979) B8380979
theorem B3724879 : Blo 2205435 3724879 := bstep (se 1 (by rfl) ⟨2793659, by rfl⟩ : syracuseStep 3724879 = 5587319) B5587319
theorem B4966505 : Blo 2205435 4966505 := bstep (se 2 (by rfl) ⟨1862439, by rfl⟩ : syracuseStep 4966505 = 3724879) B3724879
theorem B3311003 : Blo 2205435 3311003 := bstep (se 1 (by rfl) ⟨2483252, by rfl⟩ : syracuseStep 3311003 = 4966505) B4966505
theorem B2207335 : Blo 2205435 2207335 := bstep (se 1 (by rfl) ⟨1655501, by rfl⟩ : syracuseStep 2207335 = 3311003) B3311003
theorem B2483257 : Blo 2205435 2483257 := bbase (se 2 (by rfl) ⟨931221, by rfl⟩ : syracuseStep 2483257 = 1862443) (by norm_num)
theorem B3311009 : Blo 2205435 3311009 := bstep (se 2 (by rfl) ⟨1241628, by rfl⟩ : syracuseStep 3311009 = 2483257) B2483257
theorem B2207339 : Blo 2205435 2207339 := bstep (se 1 (by rfl) ⟨1655504, by rfl⟩ : syracuseStep 2207339 = 3311009) B3311009
theorem B8063957 : Blo 2205435 8063957 := bbase (se 7 (by rfl) ⟨94499, by rfl⟩ : syracuseStep 8063957 = 188999) (by norm_num)
theorem B5375971 : Blo 2205435 5375971 := bstep (se 1 (by rfl) ⟨4031978, by rfl⟩ : syracuseStep 5375971 = 8063957) B8063957
theorem B7167961 : Blo 2205435 7167961 := bstep (se 2 (by rfl) ⟨2687985, by rfl⟩ : syracuseStep 7167961 = 5375971) B5375971
theorem B9557281 : Blo 2205435 9557281 := bstep (se 2 (by rfl) ⟨3583980, by rfl⟩ : syracuseStep 9557281 = 7167961) B7167961
theorem B12743041 : Blo 2205435 12743041 := bstep (se 2 (by rfl) ⟨4778640, by rfl⟩ : syracuseStep 12743041 = 9557281) B9557281
theorem B16990721 : Blo 2205435 16990721 := bstep (se 2 (by rfl) ⟨6371520, by rfl⟩ : syracuseStep 16990721 = 12743041) B12743041
theorem B11327147 : Blo 2205435 11327147 := bstep (se 1 (by rfl) ⟨8495360, by rfl⟩ : syracuseStep 11327147 = 16990721) B16990721
theorem B7551431 : Blo 2205435 7551431 := bstep (se 1 (by rfl) ⟨5663573, by rfl⟩ : syracuseStep 7551431 = 11327147) B11327147
theorem B5034287 : Blo 2205435 5034287 := bstep (se 1 (by rfl) ⟨3775715, by rfl⟩ : syracuseStep 5034287 = 7551431) B7551431
theorem B3356191 : Blo 2205435 3356191 := bstep (se 1 (by rfl) ⟨2517143, by rfl⟩ : syracuseStep 3356191 = 5034287) B5034287
theorem B4474921 : Blo 2205435 4474921 := bstep (se 2 (by rfl) ⟨1678095, by rfl⟩ : syracuseStep 4474921 = 3356191) B3356191
theorem B5966561 : Blo 2205435 5966561 := bstep (se 2 (by rfl) ⟨2237460, by rfl⟩ : syracuseStep 5966561 = 4474921) B4474921
theorem B3977707 : Blo 2205435 3977707 := bstep (se 1 (by rfl) ⟨2983280, by rfl⟩ : syracuseStep 3977707 = 5966561) B5966561
theorem B5303609 : Blo 2205435 5303609 := bstep (se 2 (by rfl) ⟨1988853, by rfl⟩ : syracuseStep 5303609 = 3977707) B3977707
theorem B3535739 : Blo 2205435 3535739 := bstep (se 1 (by rfl) ⟨2651804, by rfl⟩ : syracuseStep 3535739 = 5303609) B5303609
theorem B2357159 : Blo 2205435 2357159 := bstep (se 1 (by rfl) ⟨1767869, by rfl⟩ : syracuseStep 2357159 = 3535739) B3535739
theorem B6285757 : Blo 2205435 6285757 := bstep (se 3 (by rfl) ⟨1178579, by rfl⟩ : syracuseStep 6285757 = 2357159) B2357159
theorem B8381009 : Blo 2205435 8381009 := bstep (se 2 (by rfl) ⟨3142878, by rfl⟩ : syracuseStep 8381009 = 6285757) B6285757
theorem B5587339 : Blo 2205435 5587339 := bstep (se 1 (by rfl) ⟨4190504, by rfl⟩ : syracuseStep 5587339 = 8381009) B8381009
theorem B7449785 : Blo 2205435 7449785 := bstep (se 2 (by rfl) ⟨2793669, by rfl⟩ : syracuseStep 7449785 = 5587339) B5587339
theorem B4966523 : Blo 2205435 4966523 := bstep (se 1 (by rfl) ⟨3724892, by rfl⟩ : syracuseStep 4966523 = 7449785) B7449785
theorem B3311015 : Blo 2205435 3311015 := bstep (se 1 (by rfl) ⟨2483261, by rfl⟩ : syracuseStep 3311015 = 4966523) B4966523
theorem B2207343 : Blo 2205435 2207343 := bstep (se 1 (by rfl) ⟨1655507, by rfl⟩ : syracuseStep 2207343 = 3311015) B3311015
theorem B3311021 : Blo 2205435 3311021 := bbase (se 3 (by rfl) ⟨620816, by rfl⟩ : syracuseStep 3311021 = 1241633) (by norm_num)
theorem B2207347 : Blo 2205435 2207347 := bstep (se 1 (by rfl) ⟨1655510, by rfl⟩ : syracuseStep 2207347 = 3311021) B3311021
theorem B4966541 : Blo 2205435 4966541 := bbase (se 3 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 4966541 = 1862453) (by norm_num)
theorem B3311027 : Blo 2205435 3311027 := bstep (se 1 (by rfl) ⟨2483270, by rfl⟩ : syracuseStep 3311027 = 4966541) B4966541
theorem B2207351 : Blo 2205435 2207351 := bstep (se 1 (by rfl) ⟨1655513, by rfl⟩ : syracuseStep 2207351 = 3311027) B3311027
theorem B2793685 : Blo 2205435 2793685 := bbase (se 7 (by rfl) ⟨32738, by rfl⟩ : syracuseStep 2793685 = 65477) (by norm_num)
theorem B3724913 : Blo 2205435 3724913 := bstep (se 2 (by rfl) ⟨1396842, by rfl⟩ : syracuseStep 3724913 = 2793685) B2793685
theorem B2483275 : Blo 2205435 2483275 := bstep (se 1 (by rfl) ⟨1862456, by rfl⟩ : syracuseStep 2483275 = 3724913) B3724913
theorem B3311033 : Blo 2205435 3311033 := bstep (se 2 (by rfl) ⟨1241637, by rfl⟩ : syracuseStep 3311033 = 2483275) B2483275
theorem B2207355 : Blo 2205435 2207355 := bstep (se 1 (by rfl) ⟨1655516, by rfl⟩ : syracuseStep 2207355 = 3311033) B3311033
theorem B7364933 : Blo 2205435 7364933 := bbase (se 4 (by rfl) ⟨690462, by rfl⟩ : syracuseStep 7364933 = 1380925) (by norm_num)
theorem B4909955 : Blo 2205435 4909955 := bstep (se 1 (by rfl) ⟨3682466, by rfl⟩ : syracuseStep 4909955 = 7364933) B7364933
theorem B13093213 : Blo 2205435 13093213 := bstep (se 3 (by rfl) ⟨2454977, by rfl⟩ : syracuseStep 13093213 = 4909955) B4909955
theorem B17457617 : Blo 2205435 17457617 := bstep (se 2 (by rfl) ⟨6546606, by rfl⟩ : syracuseStep 17457617 = 13093213) B13093213
theorem B11638411 : Blo 2205435 11638411 := bstep (se 1 (by rfl) ⟨8728808, by rfl⟩ : syracuseStep 11638411 = 17457617) B17457617
theorem B62071525 : Blo 2205435 62071525 := bstep (se 4 (by rfl) ⟨5819205, by rfl⟩ : syracuseStep 62071525 = 11638411) B11638411
theorem B82762033 : Blo 2205435 82762033 := bstep (se 2 (by rfl) ⟨31035762, by rfl⟩ : syracuseStep 82762033 = 62071525) B62071525
theorem B110349377 : Blo 2205435 110349377 := bstep (se 2 (by rfl) ⟨41381016, by rfl⟩ : syracuseStep 110349377 = 82762033) B82762033
theorem B73566251 : Blo 2205435 73566251 := bstep (se 1 (by rfl) ⟨55174688, by rfl⟩ : syracuseStep 73566251 = 110349377) B110349377
theorem B49044167 : Blo 2205435 49044167 := bstep (se 1 (by rfl) ⟨36783125, by rfl⟩ : syracuseStep 49044167 = 73566251) B73566251
theorem B32696111 : Blo 2205435 32696111 := bstep (se 1 (by rfl) ⟨24522083, by rfl⟩ : syracuseStep 32696111 = 49044167) B49044167
theorem B21797407 : Blo 2205435 21797407 := bstep (se 1 (by rfl) ⟨16348055, by rfl⟩ : syracuseStep 21797407 = 32696111) B32696111
theorem B29063209 : Blo 2205435 29063209 := bstep (se 2 (by rfl) ⟨10898703, by rfl⟩ : syracuseStep 29063209 = 21797407) B21797407
theorem B38750945 : Blo 2205435 38750945 := bstep (se 2 (by rfl) ⟨14531604, by rfl⟩ : syracuseStep 38750945 = 29063209) B29063209
theorem B103335853 : Blo 2205435 103335853 := bstep (se 3 (by rfl) ⟨19375472, by rfl⟩ : syracuseStep 103335853 = 38750945) B38750945
theorem B137781137 : Blo 2205435 137781137 := bstep (se 2 (by rfl) ⟨51667926, by rfl⟩ : syracuseStep 137781137 = 103335853) B103335853
theorem B91854091 : Blo 2205435 91854091 := bstep (se 1 (by rfl) ⟨68890568, by rfl⟩ : syracuseStep 91854091 = 137781137) B137781137
theorem B122472121 : Blo 2205435 122472121 := bstep (se 2 (by rfl) ⟨45927045, by rfl⟩ : syracuseStep 122472121 = 91854091) B91854091
theorem B163296161 : Blo 2205435 163296161 := bstep (se 2 (by rfl) ⟨61236060, by rfl⟩ : syracuseStep 163296161 = 122472121) B122472121
theorem B108864107 : Blo 2205435 108864107 := bstep (se 1 (by rfl) ⟨81648080, by rfl⟩ : syracuseStep 108864107 = 163296161) B163296161
theorem B72576071 : Blo 2205435 72576071 := bstep (se 1 (by rfl) ⟨54432053, by rfl⟩ : syracuseStep 72576071 = 108864107) B108864107
theorem B48384047 : Blo 2205435 48384047 := bstep (se 1 (by rfl) ⟨36288035, by rfl⟩ : syracuseStep 48384047 = 72576071) B72576071
theorem B32256031 : Blo 2205435 32256031 := bstep (se 1 (by rfl) ⟨24192023, by rfl⟩ : syracuseStep 32256031 = 48384047) B48384047
theorem B43008041 : Blo 2205435 43008041 := bstep (se 2 (by rfl) ⟨16128015, by rfl⟩ : syracuseStep 43008041 = 32256031) B32256031
theorem B114688109 : Blo 2205435 114688109 := bstep (se 3 (by rfl) ⟨21504020, by rfl⟩ : syracuseStep 114688109 = 43008041) B43008041
theorem B76458739 : Blo 2205435 76458739 := bstep (se 1 (by rfl) ⟨57344054, by rfl⟩ : syracuseStep 76458739 = 114688109) B114688109
theorem B101944985 : Blo 2205435 101944985 := bstep (se 2 (by rfl) ⟨38229369, by rfl⟩ : syracuseStep 101944985 = 76458739) B76458739
theorem B271853293 : Blo 2205435 271853293 := bstep (se 3 (by rfl) ⟨50972492, by rfl⟩ : syracuseStep 271853293 = 101944985) B101944985
theorem B362471057 : Blo 2205435 362471057 := bstep (se 2 (by rfl) ⟨135926646, by rfl⟩ : syracuseStep 362471057 = 271853293) B271853293
theorem B241647371 : Blo 2205435 241647371 := bstep (se 1 (by rfl) ⟨181235528, by rfl⟩ : syracuseStep 241647371 = 362471057) B362471057
theorem B161098247 : Blo 2205435 161098247 := bstep (se 1 (by rfl) ⟨120823685, by rfl⟩ : syracuseStep 161098247 = 241647371) B241647371
theorem B107398831 : Blo 2205435 107398831 := bstep (se 1 (by rfl) ⟨80549123, by rfl⟩ : syracuseStep 107398831 = 161098247) B161098247
theorem B143198441 : Blo 2205435 143198441 := bstep (se 2 (by rfl) ⟨53699415, by rfl⟩ : syracuseStep 143198441 = 107398831) B107398831
theorem B95465627 : Blo 2205435 95465627 := bstep (se 1 (by rfl) ⟨71599220, by rfl⟩ : syracuseStep 95465627 = 143198441) B143198441
theorem B63643751 : Blo 2205435 63643751 := bstep (se 1 (by rfl) ⟨47732813, by rfl⟩ : syracuseStep 63643751 = 95465627) B95465627
theorem B42429167 : Blo 2205435 42429167 := bstep (se 1 (by rfl) ⟨31821875, by rfl⟩ : syracuseStep 42429167 = 63643751) B63643751
theorem B28286111 : Blo 2205435 28286111 := bstep (se 1 (by rfl) ⟨21214583, by rfl⟩ : syracuseStep 28286111 = 42429167) B42429167
theorem B18857407 : Blo 2205435 18857407 := bstep (se 1 (by rfl) ⟨14143055, by rfl⟩ : syracuseStep 18857407 = 28286111) B28286111
theorem B25143209 : Blo 2205435 25143209 := bstep (se 2 (by rfl) ⟨9428703, by rfl⟩ : syracuseStep 25143209 = 18857407) B18857407
theorem B16762139 : Blo 2205435 16762139 := bstep (se 1 (by rfl) ⟨12571604, by rfl⟩ : syracuseStep 16762139 = 25143209) B25143209
theorem B11174759 : Blo 2205435 11174759 := bstep (se 1 (by rfl) ⟨8381069, by rfl⟩ : syracuseStep 11174759 = 16762139) B16762139
theorem B7449839 : Blo 2205435 7449839 := bstep (se 1 (by rfl) ⟨5587379, by rfl⟩ : syracuseStep 7449839 = 11174759) B11174759
theorem B4966559 : Blo 2205435 4966559 := bstep (se 1 (by rfl) ⟨3724919, by rfl⟩ : syracuseStep 4966559 = 7449839) B7449839
theorem B3311039 : Blo 2205435 3311039 := bstep (se 1 (by rfl) ⟨2483279, by rfl⟩ : syracuseStep 3311039 = 4966559) B4966559
theorem B2207359 : Blo 2205435 2207359 := bstep (se 1 (by rfl) ⟨1655519, by rfl⟩ : syracuseStep 2207359 = 3311039) B3311039
theorem B3311045 : Blo 2205435 3311045 := bbase (se 4 (by rfl) ⟨310410, by rfl⟩ : syracuseStep 3311045 = 620821) (by norm_num)
theorem B2207363 : Blo 2205435 2207363 := bstep (se 1 (by rfl) ⟨1655522, by rfl⟩ : syracuseStep 2207363 = 3311045) B3311045
theorem B3724933 : Blo 2205435 3724933 := bbase (se 4 (by rfl) ⟨349212, by rfl⟩ : syracuseStep 3724933 = 698425) (by norm_num)
theorem B4966577 : Blo 2205435 4966577 := bstep (se 2 (by rfl) ⟨1862466, by rfl⟩ : syracuseStep 4966577 = 3724933) B3724933
theorem B3311051 : Blo 2205435 3311051 := bstep (se 1 (by rfl) ⟨2483288, by rfl⟩ : syracuseStep 3311051 = 4966577) B4966577
theorem B2207367 : Blo 2205435 2207367 := bstep (se 1 (by rfl) ⟨1655525, by rfl⟩ : syracuseStep 2207367 = 3311051) B3311051
theorem B2483293 : Blo 2205435 2483293 := bbase (se 3 (by rfl) ⟨465617, by rfl⟩ : syracuseStep 2483293 = 931235) (by norm_num)
theorem B3311057 : Blo 2205435 3311057 := bstep (se 2 (by rfl) ⟨1241646, by rfl⟩ : syracuseStep 3311057 = 2483293) B2483293
theorem B2207371 : Blo 2205435 2207371 := bstep (se 1 (by rfl) ⟨1655528, by rfl⟩ : syracuseStep 2207371 = 3311057) B3311057
theorem B7449893 : Blo 2205435 7449893 := bbase (se 4 (by rfl) ⟨698427, by rfl⟩ : syracuseStep 7449893 = 1396855) (by norm_num)
theorem B4966595 : Blo 2205435 4966595 := bstep (se 1 (by rfl) ⟨3724946, by rfl⟩ : syracuseStep 4966595 = 7449893) B7449893
theorem B3311063 : Blo 2205435 3311063 := bstep (se 1 (by rfl) ⟨2483297, by rfl⟩ : syracuseStep 3311063 = 4966595) B4966595
theorem B2207375 : Blo 2205435 2207375 := bstep (se 1 (by rfl) ⟨1655531, by rfl⟩ : syracuseStep 2207375 = 3311063) B3311063
theorem B3311069 : Blo 2205435 3311069 := bbase (se 3 (by rfl) ⟨620825, by rfl⟩ : syracuseStep 3311069 = 1241651) (by norm_num)
theorem B2207379 : Blo 2205435 2207379 := bstep (se 1 (by rfl) ⟨1655534, by rfl⟩ : syracuseStep 2207379 = 3311069) B3311069
theorem B4966613 : Blo 2205435 4966613 := bbase (se 7 (by rfl) ⟨58202, by rfl⟩ : syracuseStep 4966613 = 116405) (by norm_num)
theorem B3311075 : Blo 2205435 3311075 := bstep (se 1 (by rfl) ⟨2483306, by rfl⟩ : syracuseStep 3311075 = 4966613) B4966613
theorem B2207383 : Blo 2205435 2207383 := bstep (se 1 (by rfl) ⟨1655537, by rfl⟩ : syracuseStep 2207383 = 3311075) B3311075
theorem B10607429 : Blo 2205435 10607429 := bbase (se 4 (by rfl) ⟨994446, by rfl⟩ : syracuseStep 10607429 = 1988893) (by norm_num)
theorem B7071619 : Blo 2205435 7071619 := bstep (se 1 (by rfl) ⟨5303714, by rfl⟩ : syracuseStep 7071619 = 10607429) B10607429
theorem B9428825 : Blo 2205435 9428825 := bstep (se 2 (by rfl) ⟨3535809, by rfl⟩ : syracuseStep 9428825 = 7071619) B7071619
theorem B6285883 : Blo 2205435 6285883 := bstep (se 1 (by rfl) ⟨4714412, by rfl⟩ : syracuseStep 6285883 = 9428825) B9428825
theorem B8381177 : Blo 2205435 8381177 := bstep (se 2 (by rfl) ⟨3142941, by rfl⟩ : syracuseStep 8381177 = 6285883) B6285883
theorem B5587451 : Blo 2205435 5587451 := bstep (se 1 (by rfl) ⟨4190588, by rfl⟩ : syracuseStep 5587451 = 8381177) B8381177
theorem B3724967 : Blo 2205435 3724967 := bstep (se 1 (by rfl) ⟨2793725, by rfl⟩ : syracuseStep 3724967 = 5587451) B5587451
theorem B2483311 : Blo 2205435 2483311 := bstep (se 1 (by rfl) ⟨1862483, by rfl⟩ : syracuseStep 2483311 = 3724967) B3724967
theorem B3311081 : Blo 2205435 3311081 := bstep (se 2 (by rfl) ⟨1241655, by rfl⟩ : syracuseStep 3311081 = 2483311) B2483311
theorem B2207387 : Blo 2205435 2207387 := bstep (se 1 (by rfl) ⟨1655540, by rfl⟩ : syracuseStep 2207387 = 3311081) B3311081
theorem B2268037 : Blo 2205435 2268037 := bbase (se 4 (by rfl) ⟨212628, by rfl⟩ : syracuseStep 2268037 = 425257) (by norm_num)
theorem B3024049 : Blo 2205435 3024049 := bstep (se 2 (by rfl) ⟨1134018, by rfl⟩ : syracuseStep 3024049 = 2268037) B2268037
theorem B4032065 : Blo 2205435 4032065 := bstep (se 2 (by rfl) ⟨1512024, by rfl⟩ : syracuseStep 4032065 = 3024049) B3024049
theorem B10752173 : Blo 2205435 10752173 := bstep (se 3 (by rfl) ⟨2016032, by rfl⟩ : syracuseStep 10752173 = 4032065) B4032065
theorem B7168115 : Blo 2205435 7168115 := bstep (se 1 (by rfl) ⟨5376086, by rfl⟩ : syracuseStep 7168115 = 10752173) B10752173
theorem B19114973 : Blo 2205435 19114973 := bstep (se 3 (by rfl) ⟨3584057, by rfl⟩ : syracuseStep 19114973 = 7168115) B7168115
theorem B12743315 : Blo 2205435 12743315 := bstep (se 1 (by rfl) ⟨9557486, by rfl⟩ : syracuseStep 12743315 = 19114973) B19114973
theorem B8495543 : Blo 2205435 8495543 := bstep (se 1 (by rfl) ⟨6371657, by rfl⟩ : syracuseStep 8495543 = 12743315) B12743315
theorem B5663695 : Blo 2205435 5663695 := bstep (se 1 (by rfl) ⟨4247771, by rfl⟩ : syracuseStep 5663695 = 8495543) B8495543
theorem B7551593 : Blo 2205435 7551593 := bstep (se 2 (by rfl) ⟨2831847, by rfl⟩ : syracuseStep 7551593 = 5663695) B5663695
theorem B5034395 : Blo 2205435 5034395 := bstep (se 1 (by rfl) ⟨3775796, by rfl⟩ : syracuseStep 5034395 = 7551593) B7551593
theorem B3356263 : Blo 2205435 3356263 := bstep (se 1 (by rfl) ⟨2517197, by rfl⟩ : syracuseStep 3356263 = 5034395) B5034395
theorem B4475017 : Blo 2205435 4475017 := bstep (se 2 (by rfl) ⟨1678131, by rfl⟩ : syracuseStep 4475017 = 3356263) B3356263
theorem B5966689 : Blo 2205435 5966689 := bstep (se 2 (by rfl) ⟨2237508, by rfl⟩ : syracuseStep 5966689 = 4475017) B4475017
theorem B7955585 : Blo 2205435 7955585 := bstep (se 2 (by rfl) ⟨2983344, by rfl⟩ : syracuseStep 7955585 = 5966689) B5966689
theorem B5303723 : Blo 2205435 5303723 := bstep (se 1 (by rfl) ⟨3977792, by rfl⟩ : syracuseStep 5303723 = 7955585) B7955585
theorem B14143261 : Blo 2205435 14143261 := bstep (se 3 (by rfl) ⟨2651861, by rfl⟩ : syracuseStep 14143261 = 5303723) B5303723
theorem B18857681 : Blo 2205435 18857681 := bstep (se 2 (by rfl) ⟨7071630, by rfl⟩ : syracuseStep 18857681 = 14143261) B14143261
theorem B12571787 : Blo 2205435 12571787 := bstep (se 1 (by rfl) ⟨9428840, by rfl⟩ : syracuseStep 12571787 = 18857681) B18857681
theorem B8381191 : Blo 2205435 8381191 := bstep (se 1 (by rfl) ⟨6285893, by rfl⟩ : syracuseStep 8381191 = 12571787) B12571787
theorem B11174921 : Blo 2205435 11174921 := bstep (se 2 (by rfl) ⟨4190595, by rfl⟩ : syracuseStep 11174921 = 8381191) B8381191
theorem B7449947 : Blo 2205435 7449947 := bstep (se 1 (by rfl) ⟨5587460, by rfl⟩ : syracuseStep 7449947 = 11174921) B11174921
theorem B4966631 : Blo 2205435 4966631 := bstep (se 1 (by rfl) ⟨3724973, by rfl⟩ : syracuseStep 4966631 = 7449947) B7449947
theorem B3311087 : Blo 2205435 3311087 := bstep (se 1 (by rfl) ⟨2483315, by rfl⟩ : syracuseStep 3311087 = 4966631) B4966631
theorem B2207391 : Blo 2205435 2207391 := bstep (se 1 (by rfl) ⟨1655543, by rfl⟩ : syracuseStep 2207391 = 3311087) B3311087
theorem B3311093 : Blo 2205435 3311093 := bbase (se 5 (by rfl) ⟨155207, by rfl⟩ : syracuseStep 3311093 = 310415) (by norm_num)
theorem B2207395 : Blo 2205435 2207395 := bstep (se 1 (by rfl) ⟨1655546, by rfl⟩ : syracuseStep 2207395 = 3311093) B3311093
theorem B3535829 : Blo 2205435 3535829 := bbase (se 7 (by rfl) ⟨41435, by rfl⟩ : syracuseStep 3535829 = 82871) (by norm_num)
theorem B2357219 : Blo 2205435 2357219 := bstep (se 1 (by rfl) ⟨1767914, by rfl⟩ : syracuseStep 2357219 = 3535829) B3535829
theorem B6285917 : Blo 2205435 6285917 := bstep (se 3 (by rfl) ⟨1178609, by rfl⟩ : syracuseStep 6285917 = 2357219) B2357219
theorem B4190611 : Blo 2205435 4190611 := bstep (se 1 (by rfl) ⟨3142958, by rfl⟩ : syracuseStep 4190611 = 6285917) B6285917
theorem B5587481 : Blo 2205435 5587481 := bstep (se 2 (by rfl) ⟨2095305, by rfl⟩ : syracuseStep 5587481 = 4190611) B4190611
theorem B3724987 : Blo 2205435 3724987 := bstep (se 1 (by rfl) ⟨2793740, by rfl⟩ : syracuseStep 3724987 = 5587481) B5587481
theorem B4966649 : Blo 2205435 4966649 := bstep (se 2 (by rfl) ⟨1862493, by rfl⟩ : syracuseStep 4966649 = 3724987) B3724987
theorem B3311099 : Blo 2205435 3311099 := bstep (se 1 (by rfl) ⟨2483324, by rfl⟩ : syracuseStep 3311099 = 4966649) B4966649
theorem B2207399 : Blo 2205435 2207399 := bstep (se 1 (by rfl) ⟨1655549, by rfl⟩ : syracuseStep 2207399 = 3311099) B3311099
theorem B2483329 : Blo 2205435 2483329 := bbase (se 2 (by rfl) ⟨931248, by rfl⟩ : syracuseStep 2483329 = 1862497) (by norm_num)
theorem B3311105 : Blo 2205435 3311105 := bstep (se 2 (by rfl) ⟨1241664, by rfl⟩ : syracuseStep 3311105 = 2483329) B2483329
theorem B2207403 : Blo 2205435 2207403 := bstep (se 1 (by rfl) ⟨1655552, by rfl⟩ : syracuseStep 2207403 = 3311105) B3311105
theorem B5587501 : Blo 2205435 5587501 := bbase (se 3 (by rfl) ⟨1047656, by rfl⟩ : syracuseStep 5587501 = 2095313) (by norm_num)
theorem B7450001 : Blo 2205435 7450001 := bstep (se 2 (by rfl) ⟨2793750, by rfl⟩ : syracuseStep 7450001 = 5587501) B5587501
theorem B4966667 : Blo 2205435 4966667 := bstep (se 1 (by rfl) ⟨3725000, by rfl⟩ : syracuseStep 4966667 = 7450001) B7450001
theorem B3311111 : Blo 2205435 3311111 := bstep (se 1 (by rfl) ⟨2483333, by rfl⟩ : syracuseStep 3311111 = 4966667) B4966667
theorem B2207407 : Blo 2205435 2207407 := bstep (se 1 (by rfl) ⟨1655555, by rfl⟩ : syracuseStep 2207407 = 3311111) B3311111
theorem B3311117 : Blo 2205435 3311117 := bbase (se 3 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 3311117 = 1241669) (by norm_num)
theorem B2207411 : Blo 2205435 2207411 := bstep (se 1 (by rfl) ⟨1655558, by rfl⟩ : syracuseStep 2207411 = 3311117) B3311117
theorem B4966685 : Blo 2205435 4966685 := bbase (se 3 (by rfl) ⟨931253, by rfl⟩ : syracuseStep 4966685 = 1862507) (by norm_num)
theorem B3311123 : Blo 2205435 3311123 := bstep (se 1 (by rfl) ⟨2483342, by rfl⟩ : syracuseStep 3311123 = 4966685) B4966685
theorem B2207415 : Blo 2205435 2207415 := bstep (se 1 (by rfl) ⟨1655561, by rfl⟩ : syracuseStep 2207415 = 3311123) B3311123
theorem B3725021 : Blo 2205435 3725021 := bbase (se 3 (by rfl) ⟨698441, by rfl⟩ : syracuseStep 3725021 = 1396883) (by norm_num)
theorem B2483347 : Blo 2205435 2483347 := bstep (se 1 (by rfl) ⟨1862510, by rfl⟩ : syracuseStep 2483347 = 3725021) B3725021
theorem B3311129 : Blo 2205435 3311129 := bstep (se 2 (by rfl) ⟨1241673, by rfl⟩ : syracuseStep 3311129 = 2483347) B2483347
theorem B2207419 : Blo 2205435 2207419 := bstep (se 1 (by rfl) ⟨1655564, by rfl⟩ : syracuseStep 2207419 = 3311129) B3311129
theorem B7071733 : Blo 2205435 7071733 := bbase (se 5 (by rfl) ⟨331487, by rfl⟩ : syracuseStep 7071733 = 662975) (by norm_num)
theorem B9428977 : Blo 2205435 9428977 := bstep (se 2 (by rfl) ⟨3535866, by rfl⟩ : syracuseStep 9428977 = 7071733) B7071733
theorem B12571969 : Blo 2205435 12571969 := bstep (se 2 (by rfl) ⟨4714488, by rfl⟩ : syracuseStep 12571969 = 9428977) B9428977
theorem B16762625 : Blo 2205435 16762625 := bstep (se 2 (by rfl) ⟨6285984, by rfl⟩ : syracuseStep 16762625 = 12571969) B12571969
theorem B11175083 : Blo 2205435 11175083 := bstep (se 1 (by rfl) ⟨8381312, by rfl⟩ : syracuseStep 11175083 = 16762625) B16762625
theorem B7450055 : Blo 2205435 7450055 := bstep (se 1 (by rfl) ⟨5587541, by rfl⟩ : syracuseStep 7450055 = 11175083) B11175083
theorem B4966703 : Blo 2205435 4966703 := bstep (se 1 (by rfl) ⟨3725027, by rfl⟩ : syracuseStep 4966703 = 7450055) B7450055
theorem B3311135 : Blo 2205435 3311135 := bstep (se 1 (by rfl) ⟨2483351, by rfl⟩ : syracuseStep 3311135 = 4966703) B4966703
theorem B2207423 : Blo 2205435 2207423 := bstep (se 1 (by rfl) ⟨1655567, by rfl⟩ : syracuseStep 2207423 = 3311135) B3311135
theorem B3311141 : Blo 2205435 3311141 := bbase (se 4 (by rfl) ⟨310419, by rfl⟩ : syracuseStep 3311141 = 620839) (by norm_num)
theorem B2207427 : Blo 2205435 2207427 := bstep (se 1 (by rfl) ⟨1655570, by rfl⟩ : syracuseStep 2207427 = 3311141) B3311141
theorem B2793781 : Blo 2205435 2793781 := bbase (se 5 (by rfl) ⟨130958, by rfl⟩ : syracuseStep 2793781 = 261917) (by norm_num)
theorem B3725041 : Blo 2205435 3725041 := bstep (se 2 (by rfl) ⟨1396890, by rfl⟩ : syracuseStep 3725041 = 2793781) B2793781
theorem B4966721 : Blo 2205435 4966721 := bstep (se 2 (by rfl) ⟨1862520, by rfl⟩ : syracuseStep 4966721 = 3725041) B3725041
theorem B3311147 : Blo 2205435 3311147 := bstep (se 1 (by rfl) ⟨2483360, by rfl⟩ : syracuseStep 3311147 = 4966721) B4966721
theorem B2207431 : Blo 2205435 2207431 := bstep (se 1 (by rfl) ⟨1655573, by rfl⟩ : syracuseStep 2207431 = 3311147) B3311147
theorem B2483365 : Blo 2205435 2483365 := bbase (se 4 (by rfl) ⟨232815, by rfl⟩ : syracuseStep 2483365 = 465631) (by norm_num)
theorem B3311153 : Blo 2205435 3311153 := bstep (se 2 (by rfl) ⟨1241682, by rfl⟩ : syracuseStep 3311153 = 2483365) B2483365
theorem B2207435 : Blo 2205435 2207435 := bstep (se 1 (by rfl) ⟨1655576, by rfl⟩ : syracuseStep 2207435 = 3311153) B3311153
theorem C0 (j : ℕ) (h1 : 551358 ≤ j) (h2 : j ≤ 551858) : Blo 2205435 (4 * j + 3) := by
  interval_cases j
  · exact B2205435
  · exact B2205439
  · exact B2205443
  · exact B2205447
  · exact B2205451
  · exact B2205455
  · exact B2205459
  · exact B2205463
  · exact B2205467
  · exact B2205471
  · exact B2205475
  · exact B2205479
  · exact B2205483
  · exact B2205487
  · exact B2205491
  · exact B2205495
  · exact B2205499
  · exact B2205503
  · exact B2205507
  · exact B2205511
  · exact B2205515
  · exact B2205519
  · exact B2205523
  · exact B2205527
  · exact B2205531
  · exact B2205535
  · exact B2205539
  · exact B2205543
  · exact B2205547
  · exact B2205551
  · exact B2205555
  · exact B2205559
  · exact B2205563
  · exact B2205567
  · exact B2205571
  · exact B2205575
  · exact B2205579
  · exact B2205583
  · exact B2205587
  · exact B2205591
  · exact B2205595
  · exact B2205599
  · exact B2205603
  · exact B2205607
  · exact B2205611
  · exact B2205615
  · exact B2205619
  · exact B2205623
  · exact B2205627
  · exact B2205631
  · exact B2205635
  · exact B2205639
  · exact B2205643
  · exact B2205647
  · exact B2205651
  · exact B2205655
  · exact B2205659
  · exact B2205663
  · exact B2205667
  · exact B2205671
  · exact B2205675
  · exact B2205679
  · exact B2205683
  · exact B2205687
  · exact B2205691
  · exact B2205695
  · exact B2205699
  · exact B2205703
  · exact B2205707
  · exact B2205711
  · exact B2205715
  · exact B2205719
  · exact B2205723
  · exact B2205727
  · exact B2205731
  · exact B2205735
  · exact B2205739
  · exact B2205743
  · exact B2205747
  · exact B2205751
  · exact B2205755
  · exact B2205759
  · exact B2205763
  · exact B2205767
  · exact B2205771
  · exact B2205775
  · exact B2205779
  · exact B2205783
  · exact B2205787
  · exact B2205791
  · exact B2205795
  · exact B2205799
  · exact B2205803
  · exact B2205807
  · exact B2205811
  · exact B2205815
  · exact B2205819
  · exact B2205823
  · exact B2205827
  · exact B2205831
  · exact B2205835
  · exact B2205839
  · exact B2205843
  · exact B2205847
  · exact B2205851
  · exact B2205855
  · exact B2205859
  · exact B2205863
  · exact B2205867
  · exact B2205871
  · exact B2205875
  · exact B2205879
  · exact B2205883
  · exact B2205887
  · exact B2205891
  · exact B2205895
  · exact B2205899
  · exact B2205903
  · exact B2205907
  · exact B2205911
  · exact B2205915
  · exact B2205919
  · exact B2205923
  · exact B2205927
  · exact B2205931
  · exact B2205935
  · exact B2205939
  · exact B2205943
  · exact B2205947
  · exact B2205951
  · exact B2205955
  · exact B2205959
  · exact B2205963
  · exact B2205967
  · exact B2205971
  · exact B2205975
  · exact B2205979
  · exact B2205983
  · exact B2205987
  · exact B2205991
  · exact B2205995
  · exact B2205999
  · exact B2206003
  · exact B2206007
  · exact B2206011
  · exact B2206015
  · exact B2206019
  · exact B2206023
  · exact B2206027
  · exact B2206031
  · exact B2206035
  · exact B2206039
  · exact B2206043
  · exact B2206047
  · exact B2206051
  · exact B2206055
  · exact B2206059
  · exact B2206063
  · exact B2206067
  · exact B2206071
  · exact B2206075
  · exact B2206079
  · exact B2206083
  · exact B2206087
  · exact B2206091
  · exact B2206095
  · exact B2206099
  · exact B2206103
  · exact B2206107
  · exact B2206111
  · exact B2206115
  · exact B2206119
  · exact B2206123
  · exact B2206127
  · exact B2206131
  · exact B2206135
  · exact B2206139
  · exact B2206143
  · exact B2206147
  · exact B2206151
  · exact B2206155
  · exact B2206159
  · exact B2206163
  · exact B2206167
  · exact B2206171
  · exact B2206175
  · exact B2206179
  · exact B2206183
  · exact B2206187
  · exact B2206191
  · exact B2206195
  · exact B2206199
  · exact B2206203
  · exact B2206207
  · exact B2206211
  · exact B2206215
  · exact B2206219
  · exact B2206223
  · exact B2206227
  · exact B2206231
  · exact B2206235
  · exact B2206239
  · exact B2206243
  · exact B2206247
  · exact B2206251
  · exact B2206255
  · exact B2206259
  · exact B2206263
  · exact B2206267
  · exact B2206271
  · exact B2206275
  · exact B2206279
  · exact B2206283
  · exact B2206287
  · exact B2206291
  · exact B2206295
  · exact B2206299
  · exact B2206303
  · exact B2206307
  · exact B2206311
  · exact B2206315
  · exact B2206319
  · exact B2206323
  · exact B2206327
  · exact B2206331
  · exact B2206335
  · exact B2206339
  · exact B2206343
  · exact B2206347
  · exact B2206351
  · exact B2206355
  · exact B2206359
  · exact B2206363
  · exact B2206367
  · exact B2206371
  · exact B2206375
  · exact B2206379
  · exact B2206383
  · exact B2206387
  · exact B2206391
  · exact B2206395
  · exact B2206399
  · exact B2206403
  · exact B2206407
  · exact B2206411
  · exact B2206415
  · exact B2206419
  · exact B2206423
  · exact B2206427
  · exact B2206431
  · exact B2206435
  · exact B2206439
  · exact B2206443
  · exact B2206447
  · exact B2206451
  · exact B2206455
  · exact B2206459
  · exact B2206463
  · exact B2206467
  · exact B2206471
  · exact B2206475
  · exact B2206479
  · exact B2206483
  · exact B2206487
  · exact B2206491
  · exact B2206495
  · exact B2206499
  · exact B2206503
  · exact B2206507
  · exact B2206511
  · exact B2206515
  · exact B2206519
  · exact B2206523
  · exact B2206527
  · exact B2206531
  · exact B2206535
  · exact B2206539
  · exact B2206543
  · exact B2206547
  · exact B2206551
  · exact B2206555
  · exact B2206559
  · exact B2206563
  · exact B2206567
  · exact B2206571
  · exact B2206575
  · exact B2206579
  · exact B2206583
  · exact B2206587
  · exact B2206591
  · exact B2206595
  · exact B2206599
  · exact B2206603
  · exact B2206607
  · exact B2206611
  · exact B2206615
  · exact B2206619
  · exact B2206623
  · exact B2206627
  · exact B2206631
  · exact B2206635
  · exact B2206639
  · exact B2206643
  · exact B2206647
  · exact B2206651
  · exact B2206655
  · exact B2206659
  · exact B2206663
  · exact B2206667
  · exact B2206671
  · exact B2206675
  · exact B2206679
  · exact B2206683
  · exact B2206687
  · exact B2206691
  · exact B2206695
  · exact B2206699
  · exact B2206703
  · exact B2206707
  · exact B2206711
  · exact B2206715
  · exact B2206719
  · exact B2206723
  · exact B2206727
  · exact B2206731
  · exact B2206735
  · exact B2206739
  · exact B2206743
  · exact B2206747
  · exact B2206751
  · exact B2206755
  · exact B2206759
  · exact B2206763
  · exact B2206767
  · exact B2206771
  · exact B2206775
  · exact B2206779
  · exact B2206783
  · exact B2206787
  · exact B2206791
  · exact B2206795
  · exact B2206799
  · exact B2206803
  · exact B2206807
  · exact B2206811
  · exact B2206815
  · exact B2206819
  · exact B2206823
  · exact B2206827
  · exact B2206831
  · exact B2206835
  · exact B2206839
  · exact B2206843
  · exact B2206847
  · exact B2206851
  · exact B2206855
  · exact B2206859
  · exact B2206863
  · exact B2206867
  · exact B2206871
  · exact B2206875
  · exact B2206879
  · exact B2206883
  · exact B2206887
  · exact B2206891
  · exact B2206895
  · exact B2206899
  · exact B2206903
  · exact B2206907
  · exact B2206911
  · exact B2206915
  · exact B2206919
  · exact B2206923
  · exact B2206927
  · exact B2206931
  · exact B2206935
  · exact B2206939
  · exact B2206943
  · exact B2206947
  · exact B2206951
  · exact B2206955
  · exact B2206959
  · exact B2206963
  · exact B2206967
  · exact B2206971
  · exact B2206975
  · exact B2206979
  · exact B2206983
  · exact B2206987
  · exact B2206991
  · exact B2206995
  · exact B2206999
  · exact B2207003
  · exact B2207007
  · exact B2207011
  · exact B2207015
  · exact B2207019
  · exact B2207023
  · exact B2207027
  · exact B2207031
  · exact B2207035
  · exact B2207039
  · exact B2207043
  · exact B2207047
  · exact B2207051
  · exact B2207055
  · exact B2207059
  · exact B2207063
  · exact B2207067
  · exact B2207071
  · exact B2207075
  · exact B2207079
  · exact B2207083
  · exact B2207087
  · exact B2207091
  · exact B2207095
  · exact B2207099
  · exact B2207103
  · exact B2207107
  · exact B2207111
  · exact B2207115
  · exact B2207119
  · exact B2207123
  · exact B2207127
  · exact B2207131
  · exact B2207135
  · exact B2207139
  · exact B2207143
  · exact B2207147
  · exact B2207151
  · exact B2207155
  · exact B2207159
  · exact B2207163
  · exact B2207167
  · exact B2207171
  · exact B2207175
  · exact B2207179
  · exact B2207183
  · exact B2207187
  · exact B2207191
  · exact B2207195
  · exact B2207199
  · exact B2207203
  · exact B2207207
  · exact B2207211
  · exact B2207215
  · exact B2207219
  · exact B2207223
  · exact B2207227
  · exact B2207231
  · exact B2207235
  · exact B2207239
  · exact B2207243
  · exact B2207247
  · exact B2207251
  · exact B2207255
  · exact B2207259
  · exact B2207263
  · exact B2207267
  · exact B2207271
  · exact B2207275
  · exact B2207279
  · exact B2207283
  · exact B2207287
  · exact B2207291
  · exact B2207295
  · exact B2207299
  · exact B2207303
  · exact B2207307
  · exact B2207311
  · exact B2207315
  · exact B2207319
  · exact B2207323
  · exact B2207327
  · exact B2207331
  · exact B2207335
  · exact B2207339
  · exact B2207343
  · exact B2207347
  · exact B2207351
  · exact B2207355
  · exact B2207359
  · exact B2207363
  · exact B2207367
  · exact B2207371
  · exact B2207375
  · exact B2207379
  · exact B2207383
  · exact B2207387
  · exact B2207391
  · exact B2207395
  · exact B2207399
  · exact B2207403
  · exact B2207407
  · exact B2207411
  · exact B2207415
  · exact B2207419
  · exact B2207423
  · exact B2207427
  · exact B2207431
  · exact B2207435
theorem solution (m : ℕ) (hlo : 2205435 ≤ m) (hhi : m ≤ 2207435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 551358 ≤ j := by omega
    have hj2 : j ≤ 551858 := by omega
    have hb : Blo 2205435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
