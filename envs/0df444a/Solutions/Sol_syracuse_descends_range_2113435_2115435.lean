-- Prove2me | solution 1 for syracuse_descends_range_2113435_2115435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:49.615039+00:00
-- url     : https://prove2.me/submissions/7f8b1fd7-a6ac-420e-9332-136a5a234334

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

theorem B8024453 : Blo 2113435 8024453 := bbase (se 4 (by rfl) ⟨752292, by rfl⟩ : syracuseStep 8024453 = 1504585) (by norm_num)
theorem B5349635 : Blo 2113435 5349635 := bstep (se 1 (by rfl) ⟨4012226, by rfl⟩ : syracuseStep 5349635 = 8024453) B8024453
theorem B3566423 : Blo 2113435 3566423 := bstep (se 1 (by rfl) ⟨2674817, by rfl⟩ : syracuseStep 3566423 = 5349635) B5349635
theorem B2377615 : Blo 2113435 2377615 := bstep (se 1 (by rfl) ⟨1783211, by rfl⟩ : syracuseStep 2377615 = 3566423) B3566423
theorem B3170153 : Blo 2113435 3170153 := bstep (se 2 (by rfl) ⟨1188807, by rfl⟩ : syracuseStep 3170153 = 2377615) B2377615
theorem B2113435 : Blo 2113435 2113435 := bstep (se 1 (by rfl) ⟨1585076, by rfl⟩ : syracuseStep 2113435 = 3170153) B3170153
theorem B6770645 : Blo 2113435 6770645 := bbase (se 7 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 6770645 = 158687) (by norm_num)
theorem B4513763 : Blo 2113435 4513763 := bstep (se 1 (by rfl) ⟨3385322, by rfl⟩ : syracuseStep 4513763 = 6770645) B6770645
theorem B12036701 : Blo 2113435 12036701 := bstep (se 3 (by rfl) ⟨2256881, by rfl⟩ : syracuseStep 12036701 = 4513763) B4513763
theorem B8024467 : Blo 2113435 8024467 := bstep (se 1 (by rfl) ⟨6018350, by rfl⟩ : syracuseStep 8024467 = 12036701) B12036701
theorem B10699289 : Blo 2113435 10699289 := bstep (se 2 (by rfl) ⟨4012233, by rfl⟩ : syracuseStep 10699289 = 8024467) B8024467
theorem B7132859 : Blo 2113435 7132859 := bstep (se 1 (by rfl) ⟨5349644, by rfl⟩ : syracuseStep 7132859 = 10699289) B10699289
theorem B4755239 : Blo 2113435 4755239 := bstep (se 1 (by rfl) ⟨3566429, by rfl⟩ : syracuseStep 4755239 = 7132859) B7132859
theorem B3170159 : Blo 2113435 3170159 := bstep (se 1 (by rfl) ⟨2377619, by rfl⟩ : syracuseStep 3170159 = 4755239) B4755239
theorem B2113439 : Blo 2113435 2113439 := bstep (se 1 (by rfl) ⟨1585079, by rfl⟩ : syracuseStep 2113439 = 3170159) B3170159
theorem B3170165 : Blo 2113435 3170165 := bbase (se 5 (by rfl) ⟨148601, by rfl⟩ : syracuseStep 3170165 = 297203) (by norm_num)
theorem B2113443 : Blo 2113435 2113443 := bstep (se 1 (by rfl) ⟨1585082, by rfl⟩ : syracuseStep 2113443 = 3170165) B3170165
theorem B4513781 : Blo 2113435 4513781 := bbase (se 5 (by rfl) ⟨211583, by rfl⟩ : syracuseStep 4513781 = 423167) (by norm_num)
theorem B3009187 : Blo 2113435 3009187 := bstep (se 1 (by rfl) ⟨2256890, by rfl⟩ : syracuseStep 3009187 = 4513781) B4513781
theorem B4012249 : Blo 2113435 4012249 := bstep (se 2 (by rfl) ⟨1504593, by rfl⟩ : syracuseStep 4012249 = 3009187) B3009187
theorem B5349665 : Blo 2113435 5349665 := bstep (se 2 (by rfl) ⟨2006124, by rfl⟩ : syracuseStep 5349665 = 4012249) B4012249
theorem B3566443 : Blo 2113435 3566443 := bstep (se 1 (by rfl) ⟨2674832, by rfl⟩ : syracuseStep 3566443 = 5349665) B5349665
theorem B4755257 : Blo 2113435 4755257 := bstep (se 2 (by rfl) ⟨1783221, by rfl⟩ : syracuseStep 4755257 = 3566443) B3566443
theorem B3170171 : Blo 2113435 3170171 := bstep (se 1 (by rfl) ⟨2377628, by rfl⟩ : syracuseStep 3170171 = 4755257) B4755257
theorem B2113447 : Blo 2113435 2113447 := bstep (se 1 (by rfl) ⟨1585085, by rfl⟩ : syracuseStep 2113447 = 3170171) B3170171
theorem B2377633 : Blo 2113435 2377633 := bbase (se 2 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 2377633 = 1783225) (by norm_num)
theorem B3170177 : Blo 2113435 3170177 := bstep (se 2 (by rfl) ⟨1188816, by rfl⟩ : syracuseStep 3170177 = 2377633) B2377633
theorem B2113451 : Blo 2113435 2113451 := bstep (se 1 (by rfl) ⟨1585088, by rfl⟩ : syracuseStep 2113451 = 3170177) B3170177
theorem B5349685 : Blo 2113435 5349685 := bbase (se 5 (by rfl) ⟨250766, by rfl⟩ : syracuseStep 5349685 = 501533) (by norm_num)
theorem B7132913 : Blo 2113435 7132913 := bstep (se 2 (by rfl) ⟨2674842, by rfl⟩ : syracuseStep 7132913 = 5349685) B5349685
theorem B4755275 : Blo 2113435 4755275 := bstep (se 1 (by rfl) ⟨3566456, by rfl⟩ : syracuseStep 4755275 = 7132913) B7132913
theorem B3170183 : Blo 2113435 3170183 := bstep (se 1 (by rfl) ⟨2377637, by rfl⟩ : syracuseStep 3170183 = 4755275) B4755275
theorem B2113455 : Blo 2113435 2113455 := bstep (se 1 (by rfl) ⟨1585091, by rfl⟩ : syracuseStep 2113455 = 3170183) B3170183
theorem B3170189 : Blo 2113435 3170189 := bbase (se 3 (by rfl) ⟨594410, by rfl⟩ : syracuseStep 3170189 = 1188821) (by norm_num)
theorem B2113459 : Blo 2113435 2113459 := bstep (se 1 (by rfl) ⟨1585094, by rfl⟩ : syracuseStep 2113459 = 3170189) B3170189
theorem B4755293 : Blo 2113435 4755293 := bbase (se 3 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 4755293 = 1783235) (by norm_num)
theorem B3170195 : Blo 2113435 3170195 := bstep (se 1 (by rfl) ⟨2377646, by rfl⟩ : syracuseStep 3170195 = 4755293) B4755293
theorem B2113463 : Blo 2113435 2113463 := bstep (se 1 (by rfl) ⟨1585097, by rfl⟩ : syracuseStep 2113463 = 3170195) B3170195
theorem B3566477 : Blo 2113435 3566477 := bbase (se 3 (by rfl) ⟨668714, by rfl⟩ : syracuseStep 3566477 = 1337429) (by norm_num)
theorem B2377651 : Blo 2113435 2377651 := bstep (se 1 (by rfl) ⟨1783238, by rfl⟩ : syracuseStep 2377651 = 3566477) B3566477
theorem B3170201 : Blo 2113435 3170201 := bstep (se 2 (by rfl) ⟨1188825, by rfl⟩ : syracuseStep 3170201 = 2377651) B2377651
theorem B2113467 : Blo 2113435 2113467 := bstep (se 1 (by rfl) ⟨1585100, by rfl⟩ : syracuseStep 2113467 = 3170201) B3170201
theorem B3213461 : Blo 2113435 3213461 := bbase (se 6 (by rfl) ⟨75315, by rfl⟩ : syracuseStep 3213461 = 150631) (by norm_num)
theorem B2142307 : Blo 2113435 2142307 := bstep (se 1 (by rfl) ⟨1606730, by rfl⟩ : syracuseStep 2142307 = 3213461) B3213461
theorem B11425637 : Blo 2113435 11425637 := bstep (se 4 (by rfl) ⟨1071153, by rfl⟩ : syracuseStep 11425637 = 2142307) B2142307
theorem B7617091 : Blo 2113435 7617091 := bstep (se 1 (by rfl) ⟨5712818, by rfl⟩ : syracuseStep 7617091 = 11425637) B11425637
theorem B10156121 : Blo 2113435 10156121 := bstep (se 2 (by rfl) ⟨3808545, by rfl⟩ : syracuseStep 10156121 = 7617091) B7617091
theorem B6770747 : Blo 2113435 6770747 := bstep (se 1 (by rfl) ⟨5078060, by rfl⟩ : syracuseStep 6770747 = 10156121) B10156121
theorem B18055325 : Blo 2113435 18055325 := bstep (se 3 (by rfl) ⟨3385373, by rfl⟩ : syracuseStep 18055325 = 6770747) B6770747
theorem B12036883 : Blo 2113435 12036883 := bstep (se 1 (by rfl) ⟨9027662, by rfl⟩ : syracuseStep 12036883 = 18055325) B18055325
theorem B16049177 : Blo 2113435 16049177 := bstep (se 2 (by rfl) ⟨6018441, by rfl⟩ : syracuseStep 16049177 = 12036883) B12036883
theorem B10699451 : Blo 2113435 10699451 := bstep (se 1 (by rfl) ⟨8024588, by rfl⟩ : syracuseStep 10699451 = 16049177) B16049177
theorem B7132967 : Blo 2113435 7132967 := bstep (se 1 (by rfl) ⟨5349725, by rfl⟩ : syracuseStep 7132967 = 10699451) B10699451
theorem B4755311 : Blo 2113435 4755311 := bstep (se 1 (by rfl) ⟨3566483, by rfl⟩ : syracuseStep 4755311 = 7132967) B7132967
theorem B3170207 : Blo 2113435 3170207 := bstep (se 1 (by rfl) ⟨2377655, by rfl⟩ : syracuseStep 3170207 = 4755311) B4755311
theorem B2113471 : Blo 2113435 2113471 := bstep (se 1 (by rfl) ⟨1585103, by rfl⟩ : syracuseStep 2113471 = 3170207) B3170207
theorem B3170213 : Blo 2113435 3170213 := bbase (se 4 (by rfl) ⟨297207, by rfl⟩ : syracuseStep 3170213 = 594415) (by norm_num)
theorem B2113475 : Blo 2113435 2113475 := bstep (se 1 (by rfl) ⟨1585106, by rfl⟩ : syracuseStep 2113475 = 3170213) B3170213
theorem B2674873 : Blo 2113435 2674873 := bbase (se 2 (by rfl) ⟨1003077, by rfl⟩ : syracuseStep 2674873 = 2006155) (by norm_num)
theorem B3566497 : Blo 2113435 3566497 := bstep (se 2 (by rfl) ⟨1337436, by rfl⟩ : syracuseStep 3566497 = 2674873) B2674873
theorem B4755329 : Blo 2113435 4755329 := bstep (se 2 (by rfl) ⟨1783248, by rfl⟩ : syracuseStep 4755329 = 3566497) B3566497
theorem B3170219 : Blo 2113435 3170219 := bstep (se 1 (by rfl) ⟨2377664, by rfl⟩ : syracuseStep 3170219 = 4755329) B4755329
theorem B2113479 : Blo 2113435 2113479 := bstep (se 1 (by rfl) ⟨1585109, by rfl⟩ : syracuseStep 2113479 = 3170219) B3170219
theorem B2377669 : Blo 2113435 2377669 := bbase (se 4 (by rfl) ⟨222906, by rfl⟩ : syracuseStep 2377669 = 445813) (by norm_num)
theorem B3170225 : Blo 2113435 3170225 := bstep (se 2 (by rfl) ⟨1188834, by rfl⟩ : syracuseStep 3170225 = 2377669) B2377669
theorem B2113483 : Blo 2113435 2113483 := bstep (se 1 (by rfl) ⟨1585112, by rfl⟩ : syracuseStep 2113483 = 3170225) B3170225
theorem B4012325 : Blo 2113435 4012325 := bbase (se 4 (by rfl) ⟨376155, by rfl⟩ : syracuseStep 4012325 = 752311) (by norm_num)
theorem B2674883 : Blo 2113435 2674883 := bstep (se 1 (by rfl) ⟨2006162, by rfl⟩ : syracuseStep 2674883 = 4012325) B4012325
theorem B7133021 : Blo 2113435 7133021 := bstep (se 3 (by rfl) ⟨1337441, by rfl⟩ : syracuseStep 7133021 = 2674883) B2674883
theorem B4755347 : Blo 2113435 4755347 := bstep (se 1 (by rfl) ⟨3566510, by rfl⟩ : syracuseStep 4755347 = 7133021) B7133021
theorem B3170231 : Blo 2113435 3170231 := bstep (se 1 (by rfl) ⟨2377673, by rfl⟩ : syracuseStep 3170231 = 4755347) B4755347
theorem B2113487 : Blo 2113435 2113487 := bstep (se 1 (by rfl) ⟨1585115, by rfl⟩ : syracuseStep 2113487 = 3170231) B3170231
theorem B3170237 : Blo 2113435 3170237 := bbase (se 3 (by rfl) ⟨594419, by rfl⟩ : syracuseStep 3170237 = 1188839) (by norm_num)
theorem B2113491 : Blo 2113435 2113491 := bstep (se 1 (by rfl) ⟨1585118, by rfl⟩ : syracuseStep 2113491 = 3170237) B3170237
theorem B4755365 : Blo 2113435 4755365 := bbase (se 4 (by rfl) ⟨445815, by rfl⟩ : syracuseStep 4755365 = 891631) (by norm_num)
theorem B3170243 : Blo 2113435 3170243 := bstep (se 1 (by rfl) ⟨2377682, by rfl⟩ : syracuseStep 3170243 = 4755365) B4755365
theorem B2113495 : Blo 2113435 2113495 := bstep (se 1 (by rfl) ⟨1585121, by rfl⟩ : syracuseStep 2113495 = 3170243) B3170243
theorem B5349797 : Blo 2113435 5349797 := bbase (se 4 (by rfl) ⟨501543, by rfl⟩ : syracuseStep 5349797 = 1003087) (by norm_num)
theorem B3566531 : Blo 2113435 3566531 := bstep (se 1 (by rfl) ⟨2674898, by rfl⟩ : syracuseStep 3566531 = 5349797) B5349797
theorem B2377687 : Blo 2113435 2377687 := bstep (se 1 (by rfl) ⟨1783265, by rfl⟩ : syracuseStep 2377687 = 3566531) B3566531
theorem B3170249 : Blo 2113435 3170249 := bstep (se 2 (by rfl) ⟨1188843, by rfl⟩ : syracuseStep 3170249 = 2377687) B2377687
theorem B2113499 : Blo 2113435 2113499 := bstep (se 1 (by rfl) ⟨1585124, by rfl⟩ : syracuseStep 2113499 = 3170249) B3170249
theorem B6018533 : Blo 2113435 6018533 := bbase (se 4 (by rfl) ⟨564237, by rfl⟩ : syracuseStep 6018533 = 1128475) (by norm_num)
theorem B4012355 : Blo 2113435 4012355 := bstep (se 1 (by rfl) ⟨3009266, by rfl⟩ : syracuseStep 4012355 = 6018533) B6018533
theorem B10699613 : Blo 2113435 10699613 := bstep (se 3 (by rfl) ⟨2006177, by rfl⟩ : syracuseStep 10699613 = 4012355) B4012355
theorem B7133075 : Blo 2113435 7133075 := bstep (se 1 (by rfl) ⟨5349806, by rfl⟩ : syracuseStep 7133075 = 10699613) B10699613
theorem B4755383 : Blo 2113435 4755383 := bstep (se 1 (by rfl) ⟨3566537, by rfl⟩ : syracuseStep 4755383 = 7133075) B7133075
theorem B3170255 : Blo 2113435 3170255 := bstep (se 1 (by rfl) ⟨2377691, by rfl⟩ : syracuseStep 3170255 = 4755383) B4755383
theorem B2113503 : Blo 2113435 2113503 := bstep (se 1 (by rfl) ⟨1585127, by rfl⟩ : syracuseStep 2113503 = 3170255) B3170255
theorem B3170261 : Blo 2113435 3170261 := bbase (se 7 (by rfl) ⟨37151, by rfl⟩ : syracuseStep 3170261 = 74303) (by norm_num)
theorem B2113507 : Blo 2113435 2113507 := bstep (se 1 (by rfl) ⟨1585130, by rfl⟩ : syracuseStep 2113507 = 3170261) B3170261
theorem B8024741 : Blo 2113435 8024741 := bbase (se 4 (by rfl) ⟨752319, by rfl⟩ : syracuseStep 8024741 = 1504639) (by norm_num)
theorem B5349827 : Blo 2113435 5349827 := bstep (se 1 (by rfl) ⟨4012370, by rfl⟩ : syracuseStep 5349827 = 8024741) B8024741
theorem B3566551 : Blo 2113435 3566551 := bstep (se 1 (by rfl) ⟨2674913, by rfl⟩ : syracuseStep 3566551 = 5349827) B5349827
theorem B4755401 : Blo 2113435 4755401 := bstep (se 2 (by rfl) ⟨1783275, by rfl⟩ : syracuseStep 4755401 = 3566551) B3566551
theorem B3170267 : Blo 2113435 3170267 := bstep (se 1 (by rfl) ⟨2377700, by rfl⟩ : syracuseStep 3170267 = 4755401) B4755401
theorem B2113511 : Blo 2113435 2113511 := bstep (se 1 (by rfl) ⟨1585133, by rfl⟩ : syracuseStep 2113511 = 3170267) B3170267
theorem B2377705 : Blo 2113435 2377705 := bbase (se 2 (by rfl) ⟨891639, by rfl⟩ : syracuseStep 2377705 = 1783279) (by norm_num)
theorem B3170273 : Blo 2113435 3170273 := bstep (se 2 (by rfl) ⟨1188852, by rfl⟩ : syracuseStep 3170273 = 2377705) B2377705
theorem B2113515 : Blo 2113435 2113515 := bstep (se 1 (by rfl) ⟨1585136, by rfl⟩ : syracuseStep 2113515 = 3170273) B3170273
theorem B6863285 : Blo 2113435 6863285 := bbase (se 5 (by rfl) ⟨321716, by rfl⟩ : syracuseStep 6863285 = 643433) (by norm_num)
theorem B4575523 : Blo 2113435 4575523 := bstep (se 1 (by rfl) ⟨3431642, by rfl⟩ : syracuseStep 4575523 = 6863285) B6863285
theorem B6100697 : Blo 2113435 6100697 := bstep (se 2 (by rfl) ⟨2287761, by rfl⟩ : syracuseStep 6100697 = 4575523) B4575523
theorem B16268525 : Blo 2113435 16268525 := bstep (se 3 (by rfl) ⟨3050348, by rfl⟩ : syracuseStep 16268525 = 6100697) B6100697
theorem B10845683 : Blo 2113435 10845683 := bstep (se 1 (by rfl) ⟨8134262, by rfl⟩ : syracuseStep 10845683 = 16268525) B16268525
theorem B7230455 : Blo 2113435 7230455 := bstep (se 1 (by rfl) ⟨5422841, by rfl⟩ : syracuseStep 7230455 = 10845683) B10845683
theorem B4820303 : Blo 2113435 4820303 := bstep (se 1 (by rfl) ⟨3615227, by rfl⟩ : syracuseStep 4820303 = 7230455) B7230455
theorem B3213535 : Blo 2113435 3213535 := bstep (se 1 (by rfl) ⟨2410151, by rfl⟩ : syracuseStep 3213535 = 4820303) B4820303
theorem B4284713 : Blo 2113435 4284713 := bstep (se 2 (by rfl) ⟨1606767, by rfl⟩ : syracuseStep 4284713 = 3213535) B3213535
theorem B2856475 : Blo 2113435 2856475 := bstep (se 1 (by rfl) ⟨2142356, by rfl⟩ : syracuseStep 2856475 = 4284713) B4284713
theorem B3808633 : Blo 2113435 3808633 := bstep (se 2 (by rfl) ⟨1428237, by rfl⟩ : syracuseStep 3808633 = 2856475) B2856475
theorem B5078177 : Blo 2113435 5078177 := bstep (se 2 (by rfl) ⟨1904316, by rfl⟩ : syracuseStep 5078177 = 3808633) B3808633
theorem B3385451 : Blo 2113435 3385451 := bstep (se 1 (by rfl) ⟨2539088, by rfl⟩ : syracuseStep 3385451 = 5078177) B5078177
theorem B2256967 : Blo 2113435 2256967 := bstep (se 1 (by rfl) ⟨1692725, by rfl⟩ : syracuseStep 2256967 = 3385451) B3385451
theorem B12037157 : Blo 2113435 12037157 := bstep (se 4 (by rfl) ⟨1128483, by rfl⟩ : syracuseStep 12037157 = 2256967) B2256967
theorem B8024771 : Blo 2113435 8024771 := bstep (se 1 (by rfl) ⟨6018578, by rfl⟩ : syracuseStep 8024771 = 12037157) B12037157
theorem B5349847 : Blo 2113435 5349847 := bstep (se 1 (by rfl) ⟨4012385, by rfl⟩ : syracuseStep 5349847 = 8024771) B8024771
theorem B7133129 : Blo 2113435 7133129 := bstep (se 2 (by rfl) ⟨2674923, by rfl⟩ : syracuseStep 7133129 = 5349847) B5349847
theorem B4755419 : Blo 2113435 4755419 := bstep (se 1 (by rfl) ⟨3566564, by rfl⟩ : syracuseStep 4755419 = 7133129) B7133129
theorem B3170279 : Blo 2113435 3170279 := bstep (se 1 (by rfl) ⟨2377709, by rfl⟩ : syracuseStep 3170279 = 4755419) B4755419
theorem B2113519 : Blo 2113435 2113519 := bstep (se 1 (by rfl) ⟨1585139, by rfl⟩ : syracuseStep 2113519 = 3170279) B3170279
theorem B3170285 : Blo 2113435 3170285 := bbase (se 3 (by rfl) ⟨594428, by rfl⟩ : syracuseStep 3170285 = 1188857) (by norm_num)
theorem B2113523 : Blo 2113435 2113523 := bstep (se 1 (by rfl) ⟨1585142, by rfl⟩ : syracuseStep 2113523 = 3170285) B3170285
theorem B4755437 : Blo 2113435 4755437 := bbase (se 3 (by rfl) ⟨891644, by rfl⟩ : syracuseStep 4755437 = 1783289) (by norm_num)
theorem B3170291 : Blo 2113435 3170291 := bstep (se 1 (by rfl) ⟨2377718, by rfl⟩ : syracuseStep 3170291 = 4755437) B4755437
theorem B2113527 : Blo 2113435 2113527 := bstep (se 1 (by rfl) ⟨1585145, by rfl⟩ : syracuseStep 2113527 = 3170291) B3170291
theorem B13029589 : Blo 2113435 13029589 := bbase (se 7 (by rfl) ⟨152690, by rfl⟩ : syracuseStep 13029589 = 305381) (by norm_num)
theorem B69491141 : Blo 2113435 69491141 := bstep (se 4 (by rfl) ⟨6514794, by rfl⟩ : syracuseStep 69491141 = 13029589) B13029589
theorem B46327427 : Blo 2113435 46327427 := bstep (se 1 (by rfl) ⟨34745570, by rfl⟩ : syracuseStep 46327427 = 69491141) B69491141
theorem B30884951 : Blo 2113435 30884951 := bstep (se 1 (by rfl) ⟨23163713, by rfl⟩ : syracuseStep 30884951 = 46327427) B46327427
theorem B20589967 : Blo 2113435 20589967 := bstep (se 1 (by rfl) ⟨15442475, by rfl⟩ : syracuseStep 20589967 = 30884951) B30884951
theorem B27453289 : Blo 2113435 27453289 := bstep (se 2 (by rfl) ⟨10294983, by rfl⟩ : syracuseStep 27453289 = 20589967) B20589967
theorem B36604385 : Blo 2113435 36604385 := bstep (se 2 (by rfl) ⟨13726644, by rfl⟩ : syracuseStep 36604385 = 27453289) B27453289
theorem B24402923 : Blo 2113435 24402923 := bstep (se 1 (by rfl) ⟨18302192, by rfl⟩ : syracuseStep 24402923 = 36604385) B36604385
theorem B16268615 : Blo 2113435 16268615 := bstep (se 1 (by rfl) ⟨12201461, by rfl⟩ : syracuseStep 16268615 = 24402923) B24402923
theorem B10845743 : Blo 2113435 10845743 := bstep (se 1 (by rfl) ⟨8134307, by rfl⟩ : syracuseStep 10845743 = 16268615) B16268615
theorem B28921981 : Blo 2113435 28921981 := bstep (se 3 (by rfl) ⟨5422871, by rfl⟩ : syracuseStep 28921981 = 10845743) B10845743
theorem B38562641 : Blo 2113435 38562641 := bstep (se 2 (by rfl) ⟨14460990, by rfl⟩ : syracuseStep 38562641 = 28921981) B28921981
theorem B25708427 : Blo 2113435 25708427 := bstep (se 1 (by rfl) ⟨19281320, by rfl⟩ : syracuseStep 25708427 = 38562641) B38562641
theorem B17138951 : Blo 2113435 17138951 := bstep (se 1 (by rfl) ⟨12854213, by rfl⟩ : syracuseStep 17138951 = 25708427) B25708427
theorem B11425967 : Blo 2113435 11425967 := bstep (se 1 (by rfl) ⟨8569475, by rfl⟩ : syracuseStep 11425967 = 17138951) B17138951
theorem B7617311 : Blo 2113435 7617311 := bstep (se 1 (by rfl) ⟨5712983, by rfl⟩ : syracuseStep 7617311 = 11425967) B11425967
theorem B5078207 : Blo 2113435 5078207 := bstep (se 1 (by rfl) ⟨3808655, by rfl⟩ : syracuseStep 5078207 = 7617311) B7617311
theorem B3385471 : Blo 2113435 3385471 := bstep (se 1 (by rfl) ⟨2539103, by rfl⟩ : syracuseStep 3385471 = 5078207) B5078207
theorem B4513961 : Blo 2113435 4513961 := bstep (se 2 (by rfl) ⟨1692735, by rfl⟩ : syracuseStep 4513961 = 3385471) B3385471
theorem B3009307 : Blo 2113435 3009307 := bstep (se 1 (by rfl) ⟨2256980, by rfl⟩ : syracuseStep 3009307 = 4513961) B4513961
theorem B4012409 : Blo 2113435 4012409 := bstep (se 2 (by rfl) ⟨1504653, by rfl⟩ : syracuseStep 4012409 = 3009307) B3009307
theorem B2674939 : Blo 2113435 2674939 := bstep (se 1 (by rfl) ⟨2006204, by rfl⟩ : syracuseStep 2674939 = 4012409) B4012409
theorem B3566585 : Blo 2113435 3566585 := bstep (se 2 (by rfl) ⟨1337469, by rfl⟩ : syracuseStep 3566585 = 2674939) B2674939
theorem B2377723 : Blo 2113435 2377723 := bstep (se 1 (by rfl) ⟨1783292, by rfl⟩ : syracuseStep 2377723 = 3566585) B3566585
theorem B3170297 : Blo 2113435 3170297 := bstep (se 2 (by rfl) ⟨1188861, by rfl⟩ : syracuseStep 3170297 = 2377723) B2377723
theorem B2113531 : Blo 2113435 2113531 := bstep (se 1 (by rfl) ⟨1585148, by rfl⟩ : syracuseStep 2113531 = 3170297) B3170297
theorem B4952765 : Blo 2113435 4952765 := bbase (se 3 (by rfl) ⟨928643, by rfl⟩ : syracuseStep 4952765 = 1857287) (by norm_num)
theorem B3301843 : Blo 2113435 3301843 := bstep (se 1 (by rfl) ⟨2476382, by rfl⟩ : syracuseStep 3301843 = 4952765) B4952765
theorem B4402457 : Blo 2113435 4402457 := bstep (se 2 (by rfl) ⟨1650921, by rfl⟩ : syracuseStep 4402457 = 3301843) B3301843
theorem B2934971 : Blo 2113435 2934971 := bstep (se 1 (by rfl) ⟨2201228, by rfl⟩ : syracuseStep 2934971 = 4402457) B4402457
theorem B31306357 : Blo 2113435 31306357 := bstep (se 5 (by rfl) ⟨1467485, by rfl⟩ : syracuseStep 31306357 = 2934971) B2934971
theorem B166967237 : Blo 2113435 166967237 := bstep (se 4 (by rfl) ⟨15653178, by rfl⟩ : syracuseStep 166967237 = 31306357) B31306357
theorem B445245965 : Blo 2113435 445245965 := bstep (se 3 (by rfl) ⟨83483618, by rfl⟩ : syracuseStep 445245965 = 166967237) B166967237
theorem B18997161173 : Blo 2113435 18997161173 := bstep (se 7 (by rfl) ⟨222622982, by rfl⟩ : syracuseStep 18997161173 = 445245965) B445245965
theorem B12664774115 : Blo 2113435 12664774115 := bstep (se 1 (by rfl) ⟨9498580586, by rfl⟩ : syracuseStep 12664774115 = 18997161173) B18997161173
theorem B8443182743 : Blo 2113435 8443182743 := bstep (se 1 (by rfl) ⟨6332387057, by rfl⟩ : syracuseStep 8443182743 = 12664774115) B12664774115
theorem B5628788495 : Blo 2113435 5628788495 := bstep (se 1 (by rfl) ⟨4221591371, by rfl⟩ : syracuseStep 5628788495 = 8443182743) B8443182743
theorem B3752525663 : Blo 2113435 3752525663 := bstep (se 1 (by rfl) ⟨2814394247, by rfl⟩ : syracuseStep 3752525663 = 5628788495) B5628788495
theorem B2501683775 : Blo 2113435 2501683775 := bstep (se 1 (by rfl) ⟨1876262831, by rfl⟩ : syracuseStep 2501683775 = 3752525663) B3752525663
theorem B1667789183 : Blo 2113435 1667789183 := bstep (se 1 (by rfl) ⟨1250841887, by rfl⟩ : syracuseStep 1667789183 = 2501683775) B2501683775
theorem B1111859455 : Blo 2113435 1111859455 := bstep (se 1 (by rfl) ⟨833894591, by rfl⟩ : syracuseStep 1111859455 = 1667789183) B1667789183
theorem B1482479273 : Blo 2113435 1482479273 := bstep (se 2 (by rfl) ⟨555929727, by rfl⟩ : syracuseStep 1482479273 = 1111859455) B1111859455
theorem B988319515 : Blo 2113435 988319515 := bstep (se 1 (by rfl) ⟨741239636, by rfl⟩ : syracuseStep 988319515 = 1482479273) B1482479273
theorem B1317759353 : Blo 2113435 1317759353 := bstep (se 2 (by rfl) ⟨494159757, by rfl⟩ : syracuseStep 1317759353 = 988319515) B988319515
theorem B878506235 : Blo 2113435 878506235 := bstep (se 1 (by rfl) ⟨658879676, by rfl⟩ : syracuseStep 878506235 = 1317759353) B1317759353
theorem B585670823 : Blo 2113435 585670823 := bstep (se 1 (by rfl) ⟨439253117, by rfl⟩ : syracuseStep 585670823 = 878506235) B878506235
theorem B390447215 : Blo 2113435 390447215 := bstep (se 1 (by rfl) ⟨292835411, by rfl⟩ : syracuseStep 390447215 = 585670823) B585670823
theorem B260298143 : Blo 2113435 260298143 := bstep (se 1 (by rfl) ⟨195223607, by rfl⟩ : syracuseStep 260298143 = 390447215) B390447215
theorem B173532095 : Blo 2113435 173532095 := bstep (se 1 (by rfl) ⟨130149071, by rfl⟩ : syracuseStep 173532095 = 260298143) B260298143
theorem B115688063 : Blo 2113435 115688063 := bstep (se 1 (by rfl) ⟨86766047, by rfl⟩ : syracuseStep 115688063 = 173532095) B173532095
theorem B77125375 : Blo 2113435 77125375 := bstep (se 1 (by rfl) ⟨57844031, by rfl⟩ : syracuseStep 77125375 = 115688063) B115688063
theorem B411335333 : Blo 2113435 411335333 := bstep (se 4 (by rfl) ⟨38562687, by rfl⟩ : syracuseStep 411335333 = 77125375) B77125375
theorem B274223555 : Blo 2113435 274223555 := bstep (se 1 (by rfl) ⟨205667666, by rfl⟩ : syracuseStep 274223555 = 411335333) B411335333
theorem B182815703 : Blo 2113435 182815703 := bstep (se 1 (by rfl) ⟨137111777, by rfl⟩ : syracuseStep 182815703 = 274223555) B274223555
theorem B121877135 : Blo 2113435 121877135 := bstep (se 1 (by rfl) ⟨91407851, by rfl⟩ : syracuseStep 121877135 = 182815703) B182815703
theorem B81251423 : Blo 2113435 81251423 := bstep (se 1 (by rfl) ⟨60938567, by rfl⟩ : syracuseStep 81251423 = 121877135) B121877135
theorem B54167615 : Blo 2113435 54167615 := bstep (se 1 (by rfl) ⟨40625711, by rfl⟩ : syracuseStep 54167615 = 81251423) B81251423
theorem B36111743 : Blo 2113435 36111743 := bstep (se 1 (by rfl) ⟨27083807, by rfl⟩ : syracuseStep 36111743 = 54167615) B54167615
theorem B24074495 : Blo 2113435 24074495 := bstep (se 1 (by rfl) ⟨18055871, by rfl⟩ : syracuseStep 24074495 = 36111743) B36111743
theorem B16049663 : Blo 2113435 16049663 := bstep (se 1 (by rfl) ⟨12037247, by rfl⟩ : syracuseStep 16049663 = 24074495) B24074495
theorem B10699775 : Blo 2113435 10699775 := bstep (se 1 (by rfl) ⟨8024831, by rfl⟩ : syracuseStep 10699775 = 16049663) B16049663
theorem B7133183 : Blo 2113435 7133183 := bstep (se 1 (by rfl) ⟨5349887, by rfl⟩ : syracuseStep 7133183 = 10699775) B10699775
theorem B4755455 : Blo 2113435 4755455 := bstep (se 1 (by rfl) ⟨3566591, by rfl⟩ : syracuseStep 4755455 = 7133183) B7133183
theorem B3170303 : Blo 2113435 3170303 := bstep (se 1 (by rfl) ⟨2377727, by rfl⟩ : syracuseStep 3170303 = 4755455) B4755455
theorem B2113535 : Blo 2113435 2113535 := bstep (se 1 (by rfl) ⟨1585151, by rfl⟩ : syracuseStep 2113535 = 3170303) B3170303
theorem B3170309 : Blo 2113435 3170309 := bbase (se 4 (by rfl) ⟨297216, by rfl⟩ : syracuseStep 3170309 = 594433) (by norm_num)
theorem B2113539 : Blo 2113435 2113539 := bstep (se 1 (by rfl) ⟨1585154, by rfl⟩ : syracuseStep 2113539 = 3170309) B3170309
theorem B3566605 : Blo 2113435 3566605 := bbase (se 3 (by rfl) ⟨668738, by rfl⟩ : syracuseStep 3566605 = 1337477) (by norm_num)
theorem B4755473 : Blo 2113435 4755473 := bstep (se 2 (by rfl) ⟨1783302, by rfl⟩ : syracuseStep 4755473 = 3566605) B3566605
theorem B3170315 : Blo 2113435 3170315 := bstep (se 1 (by rfl) ⟨2377736, by rfl⟩ : syracuseStep 3170315 = 4755473) B4755473
theorem B2113543 : Blo 2113435 2113543 := bstep (se 1 (by rfl) ⟨1585157, by rfl⟩ : syracuseStep 2113543 = 3170315) B3170315
theorem B2377741 : Blo 2113435 2377741 := bbase (se 3 (by rfl) ⟨445826, by rfl⟩ : syracuseStep 2377741 = 891653) (by norm_num)
theorem B3170321 : Blo 2113435 3170321 := bstep (se 2 (by rfl) ⟨1188870, by rfl⟩ : syracuseStep 3170321 = 2377741) B2377741
theorem B2113547 : Blo 2113435 2113547 := bstep (se 1 (by rfl) ⟨1585160, by rfl⟩ : syracuseStep 2113547 = 3170321) B3170321
theorem B7133237 : Blo 2113435 7133237 := bbase (se 5 (by rfl) ⟨334370, by rfl⟩ : syracuseStep 7133237 = 668741) (by norm_num)
theorem B4755491 : Blo 2113435 4755491 := bstep (se 1 (by rfl) ⟨3566618, by rfl⟩ : syracuseStep 4755491 = 7133237) B7133237
theorem B3170327 : Blo 2113435 3170327 := bstep (se 1 (by rfl) ⟨2377745, by rfl⟩ : syracuseStep 3170327 = 4755491) B4755491
theorem B2113551 : Blo 2113435 2113551 := bstep (se 1 (by rfl) ⟨1585163, by rfl⟩ : syracuseStep 2113551 = 3170327) B3170327
theorem B3170333 : Blo 2113435 3170333 := bbase (se 3 (by rfl) ⟨594437, by rfl⟩ : syracuseStep 3170333 = 1188875) (by norm_num)
theorem B2113555 : Blo 2113435 2113555 := bstep (se 1 (by rfl) ⟨1585166, by rfl⟩ : syracuseStep 2113555 = 3170333) B3170333
theorem B4755509 : Blo 2113435 4755509 := bbase (se 5 (by rfl) ⟨222914, by rfl⟩ : syracuseStep 4755509 = 445829) (by norm_num)
theorem B3170339 : Blo 2113435 3170339 := bstep (se 1 (by rfl) ⟨2377754, by rfl⟩ : syracuseStep 3170339 = 4755509) B4755509
theorem B2113559 : Blo 2113435 2113559 := bstep (se 1 (by rfl) ⟨1585169, by rfl⟩ : syracuseStep 2113559 = 3170339) B3170339
theorem B10156565 : Blo 2113435 10156565 := bbase (se 6 (by rfl) ⟨238044, by rfl⟩ : syracuseStep 10156565 = 476089) (by norm_num)
theorem B6771043 : Blo 2113435 6771043 := bstep (se 1 (by rfl) ⟨5078282, by rfl⟩ : syracuseStep 6771043 = 10156565) B10156565
theorem B9028057 : Blo 2113435 9028057 := bstep (se 2 (by rfl) ⟨3385521, by rfl⟩ : syracuseStep 9028057 = 6771043) B6771043
theorem B12037409 : Blo 2113435 12037409 := bstep (se 2 (by rfl) ⟨4514028, by rfl⟩ : syracuseStep 12037409 = 9028057) B9028057
theorem B8024939 : Blo 2113435 8024939 := bstep (se 1 (by rfl) ⟨6018704, by rfl⟩ : syracuseStep 8024939 = 12037409) B12037409
theorem B5349959 : Blo 2113435 5349959 := bstep (se 1 (by rfl) ⟨4012469, by rfl⟩ : syracuseStep 5349959 = 8024939) B8024939
theorem B3566639 : Blo 2113435 3566639 := bstep (se 1 (by rfl) ⟨2674979, by rfl⟩ : syracuseStep 3566639 = 5349959) B5349959
theorem B2377759 : Blo 2113435 2377759 := bstep (se 1 (by rfl) ⟨1783319, by rfl⟩ : syracuseStep 2377759 = 3566639) B3566639
theorem B3170345 : Blo 2113435 3170345 := bstep (se 2 (by rfl) ⟨1188879, by rfl⟩ : syracuseStep 3170345 = 2377759) B2377759
theorem B2113563 : Blo 2113435 2113563 := bstep (se 1 (by rfl) ⟨1585172, by rfl⟩ : syracuseStep 2113563 = 3170345) B3170345
theorem B2410205 : Blo 2113435 2410205 := bbase (se 3 (by rfl) ⟨451913, by rfl⟩ : syracuseStep 2410205 = 903827) (by norm_num)
theorem B25708853 : Blo 2113435 25708853 := bstep (se 5 (by rfl) ⟨1205102, by rfl⟩ : syracuseStep 25708853 = 2410205) B2410205
theorem B17139235 : Blo 2113435 17139235 := bstep (se 1 (by rfl) ⟨12854426, by rfl⟩ : syracuseStep 17139235 = 25708853) B25708853
theorem B22852313 : Blo 2113435 22852313 := bstep (se 2 (by rfl) ⟨8569617, by rfl⟩ : syracuseStep 22852313 = 17139235) B17139235
theorem B15234875 : Blo 2113435 15234875 := bstep (se 1 (by rfl) ⟨11426156, by rfl⟩ : syracuseStep 15234875 = 22852313) B22852313
theorem B10156583 : Blo 2113435 10156583 := bstep (se 1 (by rfl) ⟨7617437, by rfl⟩ : syracuseStep 10156583 = 15234875) B15234875
theorem B6771055 : Blo 2113435 6771055 := bstep (se 1 (by rfl) ⟨5078291, by rfl⟩ : syracuseStep 6771055 = 10156583) B10156583
theorem B9028073 : Blo 2113435 9028073 := bstep (se 2 (by rfl) ⟨3385527, by rfl⟩ : syracuseStep 9028073 = 6771055) B6771055
theorem B6018715 : Blo 2113435 6018715 := bstep (se 1 (by rfl) ⟨4514036, by rfl⟩ : syracuseStep 6018715 = 9028073) B9028073
theorem B8024953 : Blo 2113435 8024953 := bstep (se 2 (by rfl) ⟨3009357, by rfl⟩ : syracuseStep 8024953 = 6018715) B6018715
theorem B10699937 : Blo 2113435 10699937 := bstep (se 2 (by rfl) ⟨4012476, by rfl⟩ : syracuseStep 10699937 = 8024953) B8024953
theorem B7133291 : Blo 2113435 7133291 := bstep (se 1 (by rfl) ⟨5349968, by rfl⟩ : syracuseStep 7133291 = 10699937) B10699937
theorem B4755527 : Blo 2113435 4755527 := bstep (se 1 (by rfl) ⟨3566645, by rfl⟩ : syracuseStep 4755527 = 7133291) B7133291
theorem B3170351 : Blo 2113435 3170351 := bstep (se 1 (by rfl) ⟨2377763, by rfl⟩ : syracuseStep 3170351 = 4755527) B4755527
theorem B2113567 : Blo 2113435 2113567 := bstep (se 1 (by rfl) ⟨1585175, by rfl⟩ : syracuseStep 2113567 = 3170351) B3170351
theorem B3170357 : Blo 2113435 3170357 := bbase (se 5 (by rfl) ⟨148610, by rfl⟩ : syracuseStep 3170357 = 297221) (by norm_num)
theorem B2113571 : Blo 2113435 2113571 := bstep (se 1 (by rfl) ⟨1585178, by rfl⟩ : syracuseStep 2113571 = 3170357) B3170357
theorem B5349989 : Blo 2113435 5349989 := bbase (se 4 (by rfl) ⟨501561, by rfl⟩ : syracuseStep 5349989 = 1003123) (by norm_num)
theorem B3566659 : Blo 2113435 3566659 := bstep (se 1 (by rfl) ⟨2674994, by rfl⟩ : syracuseStep 3566659 = 5349989) B5349989
theorem B4755545 : Blo 2113435 4755545 := bstep (se 2 (by rfl) ⟨1783329, by rfl⟩ : syracuseStep 4755545 = 3566659) B3566659
theorem B3170363 : Blo 2113435 3170363 := bstep (se 1 (by rfl) ⟨2377772, by rfl⟩ : syracuseStep 3170363 = 4755545) B4755545
theorem B2113575 : Blo 2113435 2113575 := bstep (se 1 (by rfl) ⟨1585181, by rfl⟩ : syracuseStep 2113575 = 3170363) B3170363
theorem B2377777 : Blo 2113435 2377777 := bbase (se 2 (by rfl) ⟨891666, by rfl⟩ : syracuseStep 2377777 = 1783333) (by norm_num)
theorem B3170369 : Blo 2113435 3170369 := bstep (se 2 (by rfl) ⟨1188888, by rfl⟩ : syracuseStep 3170369 = 2377777) B2377777
theorem B2113579 : Blo 2113435 2113579 := bstep (se 1 (by rfl) ⟨1585184, by rfl⟩ : syracuseStep 2113579 = 3170369) B3170369
theorem B10156661 : Blo 2113435 10156661 := bbase (se 5 (by rfl) ⟨476093, by rfl⟩ : syracuseStep 10156661 = 952187) (by norm_num)
theorem B6771107 : Blo 2113435 6771107 := bstep (se 1 (by rfl) ⟨5078330, by rfl⟩ : syracuseStep 6771107 = 10156661) B10156661
theorem B4514071 : Blo 2113435 4514071 := bstep (se 1 (by rfl) ⟨3385553, by rfl⟩ : syracuseStep 4514071 = 6771107) B6771107
theorem B6018761 : Blo 2113435 6018761 := bstep (se 2 (by rfl) ⟨2257035, by rfl⟩ : syracuseStep 6018761 = 4514071) B4514071
theorem B4012507 : Blo 2113435 4012507 := bstep (se 1 (by rfl) ⟨3009380, by rfl⟩ : syracuseStep 4012507 = 6018761) B6018761
theorem B5350009 : Blo 2113435 5350009 := bstep (se 2 (by rfl) ⟨2006253, by rfl⟩ : syracuseStep 5350009 = 4012507) B4012507
theorem B7133345 : Blo 2113435 7133345 := bstep (se 2 (by rfl) ⟨2675004, by rfl⟩ : syracuseStep 7133345 = 5350009) B5350009
theorem B4755563 : Blo 2113435 4755563 := bstep (se 1 (by rfl) ⟨3566672, by rfl⟩ : syracuseStep 4755563 = 7133345) B7133345
theorem B3170375 : Blo 2113435 3170375 := bstep (se 1 (by rfl) ⟨2377781, by rfl⟩ : syracuseStep 3170375 = 4755563) B4755563
theorem B2113583 : Blo 2113435 2113583 := bstep (se 1 (by rfl) ⟨1585187, by rfl⟩ : syracuseStep 2113583 = 3170375) B3170375
theorem B3170381 : Blo 2113435 3170381 := bbase (se 3 (by rfl) ⟨594446, by rfl⟩ : syracuseStep 3170381 = 1188893) (by norm_num)
theorem B2113587 : Blo 2113435 2113587 := bstep (se 1 (by rfl) ⟨1585190, by rfl⟩ : syracuseStep 2113587 = 3170381) B3170381
theorem B4755581 : Blo 2113435 4755581 := bbase (se 3 (by rfl) ⟨891671, by rfl⟩ : syracuseStep 4755581 = 1783343) (by norm_num)
theorem B3170387 : Blo 2113435 3170387 := bstep (se 1 (by rfl) ⟨2377790, by rfl⟩ : syracuseStep 3170387 = 4755581) B4755581
theorem B2113591 : Blo 2113435 2113591 := bstep (se 1 (by rfl) ⟨1585193, by rfl⟩ : syracuseStep 2113591 = 3170387) B3170387
theorem B3566693 : Blo 2113435 3566693 := bbase (se 4 (by rfl) ⟨334377, by rfl⟩ : syracuseStep 3566693 = 668755) (by norm_num)
theorem B2377795 : Blo 2113435 2377795 := bstep (se 1 (by rfl) ⟨1783346, by rfl⟩ : syracuseStep 2377795 = 3566693) B3566693
theorem B3170393 : Blo 2113435 3170393 := bstep (se 2 (by rfl) ⟨1188897, by rfl⟩ : syracuseStep 3170393 = 2377795) B2377795
theorem B2113595 : Blo 2113435 2113595 := bstep (se 1 (by rfl) ⟨1585196, by rfl⟩ : syracuseStep 2113595 = 3170393) B3170393
theorem B4820485 : Blo 2113435 4820485 := bbase (se 4 (by rfl) ⟨451920, by rfl⟩ : syracuseStep 4820485 = 903841) (by norm_num)
theorem B6427313 : Blo 2113435 6427313 := bstep (se 2 (by rfl) ⟨2410242, by rfl⟩ : syracuseStep 6427313 = 4820485) B4820485
theorem B4284875 : Blo 2113435 4284875 := bstep (se 1 (by rfl) ⟨3213656, by rfl⟩ : syracuseStep 4284875 = 6427313) B6427313
theorem B2856583 : Blo 2113435 2856583 := bstep (se 1 (by rfl) ⟨2142437, by rfl⟩ : syracuseStep 2856583 = 4284875) B4284875
theorem B3808777 : Blo 2113435 3808777 := bstep (se 2 (by rfl) ⟨1428291, by rfl⟩ : syracuseStep 3808777 = 2856583) B2856583
theorem B5078369 : Blo 2113435 5078369 := bstep (se 2 (by rfl) ⟨1904388, by rfl⟩ : syracuseStep 5078369 = 3808777) B3808777
theorem B3385579 : Blo 2113435 3385579 := bstep (se 1 (by rfl) ⟨2539184, by rfl⟩ : syracuseStep 3385579 = 5078369) B5078369
theorem B4514105 : Blo 2113435 4514105 := bstep (se 2 (by rfl) ⟨1692789, by rfl⟩ : syracuseStep 4514105 = 3385579) B3385579
theorem B3009403 : Blo 2113435 3009403 := bstep (se 1 (by rfl) ⟨2257052, by rfl⟩ : syracuseStep 3009403 = 4514105) B4514105
theorem B16050149 : Blo 2113435 16050149 := bstep (se 4 (by rfl) ⟨1504701, by rfl⟩ : syracuseStep 16050149 = 3009403) B3009403
theorem B10700099 : Blo 2113435 10700099 := bstep (se 1 (by rfl) ⟨8025074, by rfl⟩ : syracuseStep 10700099 = 16050149) B16050149
theorem B7133399 : Blo 2113435 7133399 := bstep (se 1 (by rfl) ⟨5350049, by rfl⟩ : syracuseStep 7133399 = 10700099) B10700099
theorem B4755599 : Blo 2113435 4755599 := bstep (se 1 (by rfl) ⟨3566699, by rfl⟩ : syracuseStep 4755599 = 7133399) B7133399
theorem B3170399 : Blo 2113435 3170399 := bstep (se 1 (by rfl) ⟨2377799, by rfl⟩ : syracuseStep 3170399 = 4755599) B4755599
theorem B2113599 : Blo 2113435 2113599 := bstep (se 1 (by rfl) ⟨1585199, by rfl⟩ : syracuseStep 2113599 = 3170399) B3170399
theorem B3170405 : Blo 2113435 3170405 := bbase (se 4 (by rfl) ⟨297225, by rfl⟩ : syracuseStep 3170405 = 594451) (by norm_num)
theorem B2113603 : Blo 2113435 2113603 := bstep (se 1 (by rfl) ⟨1585202, by rfl⟩ : syracuseStep 2113603 = 3170405) B3170405
theorem B5078389 : Blo 2113435 5078389 := bbase (se 5 (by rfl) ⟨238049, by rfl⟩ : syracuseStep 5078389 = 476099) (by norm_num)
theorem B6771185 : Blo 2113435 6771185 := bstep (se 2 (by rfl) ⟨2539194, by rfl⟩ : syracuseStep 6771185 = 5078389) B5078389
theorem B4514123 : Blo 2113435 4514123 := bstep (se 1 (by rfl) ⟨3385592, by rfl⟩ : syracuseStep 4514123 = 6771185) B6771185
theorem B3009415 : Blo 2113435 3009415 := bstep (se 1 (by rfl) ⟨2257061, by rfl⟩ : syracuseStep 3009415 = 4514123) B4514123
theorem B4012553 : Blo 2113435 4012553 := bstep (se 2 (by rfl) ⟨1504707, by rfl⟩ : syracuseStep 4012553 = 3009415) B3009415
theorem B2675035 : Blo 2113435 2675035 := bstep (se 1 (by rfl) ⟨2006276, by rfl⟩ : syracuseStep 2675035 = 4012553) B4012553
theorem B3566713 : Blo 2113435 3566713 := bstep (se 2 (by rfl) ⟨1337517, by rfl⟩ : syracuseStep 3566713 = 2675035) B2675035
theorem B4755617 : Blo 2113435 4755617 := bstep (se 2 (by rfl) ⟨1783356, by rfl⟩ : syracuseStep 4755617 = 3566713) B3566713
theorem B3170411 : Blo 2113435 3170411 := bstep (se 1 (by rfl) ⟨2377808, by rfl⟩ : syracuseStep 3170411 = 4755617) B4755617
theorem B2113607 : Blo 2113435 2113607 := bstep (se 1 (by rfl) ⟨1585205, by rfl⟩ : syracuseStep 2113607 = 3170411) B3170411
theorem B2377813 : Blo 2113435 2377813 := bbase (se 8 (by rfl) ⟨13932, by rfl⟩ : syracuseStep 2377813 = 27865) (by norm_num)
theorem B3170417 : Blo 2113435 3170417 := bstep (se 2 (by rfl) ⟨1188906, by rfl⟩ : syracuseStep 3170417 = 2377813) B2377813
theorem B2113611 : Blo 2113435 2113611 := bstep (se 1 (by rfl) ⟨1585208, by rfl⟩ : syracuseStep 2113611 = 3170417) B3170417
theorem B2675045 : Blo 2113435 2675045 := bbase (se 4 (by rfl) ⟨250785, by rfl⟩ : syracuseStep 2675045 = 501571) (by norm_num)
theorem B7133453 : Blo 2113435 7133453 := bstep (se 3 (by rfl) ⟨1337522, by rfl⟩ : syracuseStep 7133453 = 2675045) B2675045
theorem B4755635 : Blo 2113435 4755635 := bstep (se 1 (by rfl) ⟨3566726, by rfl⟩ : syracuseStep 4755635 = 7133453) B7133453
theorem B3170423 : Blo 2113435 3170423 := bstep (se 1 (by rfl) ⟨2377817, by rfl⟩ : syracuseStep 3170423 = 4755635) B4755635
theorem B2113615 : Blo 2113435 2113615 := bstep (se 1 (by rfl) ⟨1585211, by rfl⟩ : syracuseStep 2113615 = 3170423) B3170423
theorem B3170429 : Blo 2113435 3170429 := bbase (se 3 (by rfl) ⟨594455, by rfl⟩ : syracuseStep 3170429 = 1188911) (by norm_num)
theorem B2113619 : Blo 2113435 2113619 := bstep (se 1 (by rfl) ⟨1585214, by rfl⟩ : syracuseStep 2113619 = 3170429) B3170429
theorem B4755653 : Blo 2113435 4755653 := bbase (se 4 (by rfl) ⟨445842, by rfl⟩ : syracuseStep 4755653 = 891685) (by norm_num)
theorem B3170435 : Blo 2113435 3170435 := bstep (se 1 (by rfl) ⟨2377826, by rfl⟩ : syracuseStep 3170435 = 4755653) B4755653
theorem B2113623 : Blo 2113435 2113623 := bstep (se 1 (by rfl) ⟨1585217, by rfl⟩ : syracuseStep 2113623 = 3170435) B3170435
theorem B6427397 : Blo 2113435 6427397 := bbase (se 4 (by rfl) ⟨602568, by rfl⟩ : syracuseStep 6427397 = 1205137) (by norm_num)
theorem B17139725 : Blo 2113435 17139725 := bstep (se 3 (by rfl) ⟨3213698, by rfl⟩ : syracuseStep 17139725 = 6427397) B6427397
theorem B11426483 : Blo 2113435 11426483 := bstep (se 1 (by rfl) ⟨8569862, by rfl⟩ : syracuseStep 11426483 = 17139725) B17139725
theorem B7617655 : Blo 2113435 7617655 := bstep (se 1 (by rfl) ⟨5713241, by rfl⟩ : syracuseStep 7617655 = 11426483) B11426483
theorem B10156873 : Blo 2113435 10156873 := bstep (se 2 (by rfl) ⟨3808827, by rfl⟩ : syracuseStep 10156873 = 7617655) B7617655
theorem B13542497 : Blo 2113435 13542497 := bstep (se 2 (by rfl) ⟨5078436, by rfl⟩ : syracuseStep 13542497 = 10156873) B10156873
theorem B9028331 : Blo 2113435 9028331 := bstep (se 1 (by rfl) ⟨6771248, by rfl⟩ : syracuseStep 9028331 = 13542497) B13542497
theorem B6018887 : Blo 2113435 6018887 := bstep (se 1 (by rfl) ⟨4514165, by rfl⟩ : syracuseStep 6018887 = 9028331) B9028331
theorem B4012591 : Blo 2113435 4012591 := bstep (se 1 (by rfl) ⟨3009443, by rfl⟩ : syracuseStep 4012591 = 6018887) B6018887
theorem B5350121 : Blo 2113435 5350121 := bstep (se 2 (by rfl) ⟨2006295, by rfl⟩ : syracuseStep 5350121 = 4012591) B4012591
theorem B3566747 : Blo 2113435 3566747 := bstep (se 1 (by rfl) ⟨2675060, by rfl⟩ : syracuseStep 3566747 = 5350121) B5350121
theorem B2377831 : Blo 2113435 2377831 := bstep (se 1 (by rfl) ⟨1783373, by rfl⟩ : syracuseStep 2377831 = 3566747) B3566747
theorem B3170441 : Blo 2113435 3170441 := bstep (se 2 (by rfl) ⟨1188915, by rfl⟩ : syracuseStep 3170441 = 2377831) B2377831
theorem B2113627 : Blo 2113435 2113627 := bstep (se 1 (by rfl) ⟨1585220, by rfl⟩ : syracuseStep 2113627 = 3170441) B3170441
theorem B10700261 : Blo 2113435 10700261 := bbase (se 4 (by rfl) ⟨1003149, by rfl⟩ : syracuseStep 10700261 = 2006299) (by norm_num)
theorem B7133507 : Blo 2113435 7133507 := bstep (se 1 (by rfl) ⟨5350130, by rfl⟩ : syracuseStep 7133507 = 10700261) B10700261
theorem B4755671 : Blo 2113435 4755671 := bstep (se 1 (by rfl) ⟨3566753, by rfl⟩ : syracuseStep 4755671 = 7133507) B7133507
theorem B3170447 : Blo 2113435 3170447 := bstep (se 1 (by rfl) ⟨2377835, by rfl⟩ : syracuseStep 3170447 = 4755671) B4755671
theorem B2113631 : Blo 2113435 2113631 := bstep (se 1 (by rfl) ⟨1585223, by rfl⟩ : syracuseStep 2113631 = 3170447) B3170447
theorem B3170453 : Blo 2113435 3170453 := bbase (se 6 (by rfl) ⟨74307, by rfl⟩ : syracuseStep 3170453 = 148615) (by norm_num)
theorem B2113635 : Blo 2113435 2113635 := bstep (se 1 (by rfl) ⟨1585226, by rfl⟩ : syracuseStep 2113635 = 3170453) B3170453
theorem B2856637 : Blo 2113435 2856637 := bbase (se 3 (by rfl) ⟨535619, by rfl⟩ : syracuseStep 2856637 = 1071239) (by norm_num)
theorem B3808849 : Blo 2113435 3808849 := bstep (se 2 (by rfl) ⟨1428318, by rfl⟩ : syracuseStep 3808849 = 2856637) B2856637
theorem B5078465 : Blo 2113435 5078465 := bstep (se 2 (by rfl) ⟨1904424, by rfl⟩ : syracuseStep 5078465 = 3808849) B3808849
theorem B3385643 : Blo 2113435 3385643 := bstep (se 1 (by rfl) ⟨2539232, by rfl⟩ : syracuseStep 3385643 = 5078465) B5078465
theorem B9028381 : Blo 2113435 9028381 := bstep (se 3 (by rfl) ⟨1692821, by rfl⟩ : syracuseStep 9028381 = 3385643) B3385643
theorem B12037841 : Blo 2113435 12037841 := bstep (se 2 (by rfl) ⟨4514190, by rfl⟩ : syracuseStep 12037841 = 9028381) B9028381
theorem B8025227 : Blo 2113435 8025227 := bstep (se 1 (by rfl) ⟨6018920, by rfl⟩ : syracuseStep 8025227 = 12037841) B12037841
theorem B5350151 : Blo 2113435 5350151 := bstep (se 1 (by rfl) ⟨4012613, by rfl⟩ : syracuseStep 5350151 = 8025227) B8025227
theorem B3566767 : Blo 2113435 3566767 := bstep (se 1 (by rfl) ⟨2675075, by rfl⟩ : syracuseStep 3566767 = 5350151) B5350151
theorem B4755689 : Blo 2113435 4755689 := bstep (se 2 (by rfl) ⟨1783383, by rfl⟩ : syracuseStep 4755689 = 3566767) B3566767
theorem B3170459 : Blo 2113435 3170459 := bstep (se 1 (by rfl) ⟨2377844, by rfl⟩ : syracuseStep 3170459 = 4755689) B4755689
theorem B2113639 : Blo 2113435 2113639 := bstep (se 1 (by rfl) ⟨1585229, by rfl⟩ : syracuseStep 2113639 = 3170459) B3170459
theorem B2377849 : Blo 2113435 2377849 := bbase (se 2 (by rfl) ⟨891693, by rfl⟩ : syracuseStep 2377849 = 1783387) (by norm_num)
theorem B3170465 : Blo 2113435 3170465 := bstep (se 2 (by rfl) ⟨1188924, by rfl⟩ : syracuseStep 3170465 = 2377849) B2377849
theorem B2113643 : Blo 2113435 2113643 := bstep (se 1 (by rfl) ⟨1585232, by rfl⟩ : syracuseStep 2113643 = 3170465) B3170465
theorem B2824093 : Blo 2113435 2824093 := bbase (se 3 (by rfl) ⟨529517, by rfl⟩ : syracuseStep 2824093 = 1059035) (by norm_num)
theorem B3765457 : Blo 2113435 3765457 := bstep (se 2 (by rfl) ⟨1412046, by rfl⟩ : syracuseStep 3765457 = 2824093) B2824093
theorem B20082437 : Blo 2113435 20082437 := bstep (se 4 (by rfl) ⟨1882728, by rfl⟩ : syracuseStep 20082437 = 3765457) B3765457
theorem B13388291 : Blo 2113435 13388291 := bstep (se 1 (by rfl) ⟨10041218, by rfl⟩ : syracuseStep 13388291 = 20082437) B20082437
theorem B8925527 : Blo 2113435 8925527 := bstep (se 1 (by rfl) ⟨6694145, by rfl⟩ : syracuseStep 8925527 = 13388291) B13388291
theorem B5950351 : Blo 2113435 5950351 := bstep (se 1 (by rfl) ⟨4462763, by rfl⟩ : syracuseStep 5950351 = 8925527) B8925527
theorem B7933801 : Blo 2113435 7933801 := bstep (se 2 (by rfl) ⟨2975175, by rfl⟩ : syracuseStep 7933801 = 5950351) B5950351
theorem B10578401 : Blo 2113435 10578401 := bstep (se 2 (by rfl) ⟨3966900, by rfl⟩ : syracuseStep 10578401 = 7933801) B7933801
theorem B7052267 : Blo 2113435 7052267 := bstep (se 1 (by rfl) ⟨5289200, by rfl⟩ : syracuseStep 7052267 = 10578401) B10578401
theorem B4701511 : Blo 2113435 4701511 := bstep (se 1 (by rfl) ⟨3526133, by rfl⟩ : syracuseStep 4701511 = 7052267) B7052267
theorem B6268681 : Blo 2113435 6268681 := bstep (se 2 (by rfl) ⟨2350755, by rfl⟩ : syracuseStep 6268681 = 4701511) B4701511
theorem B8358241 : Blo 2113435 8358241 := bstep (se 2 (by rfl) ⟨3134340, by rfl⟩ : syracuseStep 8358241 = 6268681) B6268681
theorem B11144321 : Blo 2113435 11144321 := bstep (se 2 (by rfl) ⟨4179120, by rfl⟩ : syracuseStep 11144321 = 8358241) B8358241
theorem B7429547 : Blo 2113435 7429547 := bstep (se 1 (by rfl) ⟨5572160, by rfl⟩ : syracuseStep 7429547 = 11144321) B11144321
theorem B4953031 : Blo 2113435 4953031 := bstep (se 1 (by rfl) ⟨3714773, by rfl⟩ : syracuseStep 4953031 = 7429547) B7429547
theorem B26416165 : Blo 2113435 26416165 := bstep (se 4 (by rfl) ⟨2476515, by rfl⟩ : syracuseStep 26416165 = 4953031) B4953031
theorem B35221553 : Blo 2113435 35221553 := bstep (se 2 (by rfl) ⟨13208082, by rfl⟩ : syracuseStep 35221553 = 26416165) B26416165
theorem B23481035 : Blo 2113435 23481035 := bstep (se 1 (by rfl) ⟨17610776, by rfl⟩ : syracuseStep 23481035 = 35221553) B35221553
theorem B15654023 : Blo 2113435 15654023 := bstep (se 1 (by rfl) ⟨11740517, by rfl⟩ : syracuseStep 15654023 = 23481035) B23481035
theorem B10436015 : Blo 2113435 10436015 := bstep (se 1 (by rfl) ⟨7827011, by rfl⟩ : syracuseStep 10436015 = 15654023) B15654023
theorem B6957343 : Blo 2113435 6957343 := bstep (se 1 (by rfl) ⟨5218007, by rfl⟩ : syracuseStep 6957343 = 10436015) B10436015
theorem B9276457 : Blo 2113435 9276457 := bstep (se 2 (by rfl) ⟨3478671, by rfl⟩ : syracuseStep 9276457 = 6957343) B6957343
theorem B12368609 : Blo 2113435 12368609 := bstep (se 2 (by rfl) ⟨4638228, by rfl⟩ : syracuseStep 12368609 = 9276457) B9276457
theorem B8245739 : Blo 2113435 8245739 := bstep (se 1 (by rfl) ⟨6184304, by rfl⟩ : syracuseStep 8245739 = 12368609) B12368609
theorem B5497159 : Blo 2113435 5497159 := bstep (se 1 (by rfl) ⟨4122869, by rfl⟩ : syracuseStep 5497159 = 8245739) B8245739
theorem B7329545 : Blo 2113435 7329545 := bstep (se 2 (by rfl) ⟨2748579, by rfl⟩ : syracuseStep 7329545 = 5497159) B5497159
theorem B4886363 : Blo 2113435 4886363 := bstep (se 1 (by rfl) ⟨3664772, by rfl⟩ : syracuseStep 4886363 = 7329545) B7329545
theorem B13030301 : Blo 2113435 13030301 := bstep (se 3 (by rfl) ⟨2443181, by rfl⟩ : syracuseStep 13030301 = 4886363) B4886363
theorem B8686867 : Blo 2113435 8686867 := bstep (se 1 (by rfl) ⟨6515150, by rfl⟩ : syracuseStep 8686867 = 13030301) B13030301
theorem B11582489 : Blo 2113435 11582489 := bstep (se 2 (by rfl) ⟨4343433, by rfl⟩ : syracuseStep 11582489 = 8686867) B8686867
theorem B7721659 : Blo 2113435 7721659 := bstep (se 1 (by rfl) ⟨5791244, by rfl⟩ : syracuseStep 7721659 = 11582489) B11582489
theorem B10295545 : Blo 2113435 10295545 := bstep (se 2 (by rfl) ⟨3860829, by rfl⟩ : syracuseStep 10295545 = 7721659) B7721659
theorem B13727393 : Blo 2113435 13727393 := bstep (se 2 (by rfl) ⟨5147772, by rfl⟩ : syracuseStep 13727393 = 10295545) B10295545
theorem B9151595 : Blo 2113435 9151595 := bstep (se 1 (by rfl) ⟨6863696, by rfl⟩ : syracuseStep 9151595 = 13727393) B13727393
theorem B6101063 : Blo 2113435 6101063 := bstep (se 1 (by rfl) ⟨4575797, by rfl⟩ : syracuseStep 6101063 = 9151595) B9151595
theorem B4067375 : Blo 2113435 4067375 := bstep (se 1 (by rfl) ⟨3050531, by rfl⟩ : syracuseStep 4067375 = 6101063) B6101063
theorem B10846333 : Blo 2113435 10846333 := bstep (se 3 (by rfl) ⟨2033687, by rfl⟩ : syracuseStep 10846333 = 4067375) B4067375
theorem B14461777 : Blo 2113435 14461777 := bstep (se 2 (by rfl) ⟨5423166, by rfl⟩ : syracuseStep 14461777 = 10846333) B10846333
theorem B19282369 : Blo 2113435 19282369 := bstep (se 2 (by rfl) ⟨7230888, by rfl⟩ : syracuseStep 19282369 = 14461777) B14461777
theorem B25709825 : Blo 2113435 25709825 := bstep (se 2 (by rfl) ⟨9641184, by rfl⟩ : syracuseStep 25709825 = 19282369) B19282369
theorem B68559533 : Blo 2113435 68559533 := bstep (se 3 (by rfl) ⟨12854912, by rfl⟩ : syracuseStep 68559533 = 25709825) B25709825
theorem B45706355 : Blo 2113435 45706355 := bstep (se 1 (by rfl) ⟨34279766, by rfl⟩ : syracuseStep 45706355 = 68559533) B68559533
theorem B30470903 : Blo 2113435 30470903 := bstep (se 1 (by rfl) ⟨22853177, by rfl⟩ : syracuseStep 30470903 = 45706355) B45706355
theorem B20313935 : Blo 2113435 20313935 := bstep (se 1 (by rfl) ⟨15235451, by rfl⟩ : syracuseStep 20313935 = 30470903) B30470903
theorem B13542623 : Blo 2113435 13542623 := bstep (se 1 (by rfl) ⟨10156967, by rfl⟩ : syracuseStep 13542623 = 20313935) B20313935
theorem B9028415 : Blo 2113435 9028415 := bstep (se 1 (by rfl) ⟨6771311, by rfl⟩ : syracuseStep 9028415 = 13542623) B13542623
theorem B6018943 : Blo 2113435 6018943 := bstep (se 1 (by rfl) ⟨4514207, by rfl⟩ : syracuseStep 6018943 = 9028415) B9028415
theorem B8025257 : Blo 2113435 8025257 := bstep (se 2 (by rfl) ⟨3009471, by rfl⟩ : syracuseStep 8025257 = 6018943) B6018943
theorem B5350171 : Blo 2113435 5350171 := bstep (se 1 (by rfl) ⟨4012628, by rfl⟩ : syracuseStep 5350171 = 8025257) B8025257
theorem B7133561 : Blo 2113435 7133561 := bstep (se 2 (by rfl) ⟨2675085, by rfl⟩ : syracuseStep 7133561 = 5350171) B5350171
theorem B4755707 : Blo 2113435 4755707 := bstep (se 1 (by rfl) ⟨3566780, by rfl⟩ : syracuseStep 4755707 = 7133561) B7133561
theorem B3170471 : Blo 2113435 3170471 := bstep (se 1 (by rfl) ⟨2377853, by rfl⟩ : syracuseStep 3170471 = 4755707) B4755707
theorem B2113647 : Blo 2113435 2113647 := bstep (se 1 (by rfl) ⟨1585235, by rfl⟩ : syracuseStep 2113647 = 3170471) B3170471
theorem B3170477 : Blo 2113435 3170477 := bbase (se 3 (by rfl) ⟨594464, by rfl⟩ : syracuseStep 3170477 = 1188929) (by norm_num)
theorem B2113651 : Blo 2113435 2113651 := bstep (se 1 (by rfl) ⟨1585238, by rfl⟩ : syracuseStep 2113651 = 3170477) B3170477
theorem B4755725 : Blo 2113435 4755725 := bbase (se 3 (by rfl) ⟨891698, by rfl⟩ : syracuseStep 4755725 = 1783397) (by norm_num)
theorem B3170483 : Blo 2113435 3170483 := bstep (se 1 (by rfl) ⟨2377862, by rfl⟩ : syracuseStep 3170483 = 4755725) B4755725
theorem B2113655 : Blo 2113435 2113655 := bstep (se 1 (by rfl) ⟨1585241, by rfl⟩ : syracuseStep 2113655 = 3170483) B3170483
theorem B2675101 : Blo 2113435 2675101 := bbase (se 3 (by rfl) ⟨501581, by rfl⟩ : syracuseStep 2675101 = 1003163) (by norm_num)
theorem B3566801 : Blo 2113435 3566801 := bstep (se 2 (by rfl) ⟨1337550, by rfl⟩ : syracuseStep 3566801 = 2675101) B2675101
theorem B2377867 : Blo 2113435 2377867 := bstep (se 1 (by rfl) ⟨1783400, by rfl⟩ : syracuseStep 2377867 = 3566801) B3566801
theorem B3170489 : Blo 2113435 3170489 := bstep (se 2 (by rfl) ⟨1188933, by rfl⟩ : syracuseStep 3170489 = 2377867) B2377867
theorem B2113659 : Blo 2113435 2113659 := bstep (se 1 (by rfl) ⟨1585244, by rfl⟩ : syracuseStep 2113659 = 3170489) B3170489
theorem B2539261 : Blo 2113435 2539261 := bbase (se 3 (by rfl) ⟨476111, by rfl⟩ : syracuseStep 2539261 = 952223) (by norm_num)
theorem B3385681 : Blo 2113435 3385681 := bstep (se 2 (by rfl) ⟨1269630, by rfl⟩ : syracuseStep 3385681 = 2539261) B2539261
theorem B18056965 : Blo 2113435 18056965 := bstep (se 4 (by rfl) ⟨1692840, by rfl⟩ : syracuseStep 18056965 = 3385681) B3385681
theorem B24075953 : Blo 2113435 24075953 := bstep (se 2 (by rfl) ⟨9028482, by rfl⟩ : syracuseStep 24075953 = 18056965) B18056965
theorem B16050635 : Blo 2113435 16050635 := bstep (se 1 (by rfl) ⟨12037976, by rfl⟩ : syracuseStep 16050635 = 24075953) B24075953
theorem B10700423 : Blo 2113435 10700423 := bstep (se 1 (by rfl) ⟨8025317, by rfl⟩ : syracuseStep 10700423 = 16050635) B16050635
theorem B7133615 : Blo 2113435 7133615 := bstep (se 1 (by rfl) ⟨5350211, by rfl⟩ : syracuseStep 7133615 = 10700423) B10700423
theorem B4755743 : Blo 2113435 4755743 := bstep (se 1 (by rfl) ⟨3566807, by rfl⟩ : syracuseStep 4755743 = 7133615) B7133615
theorem B3170495 : Blo 2113435 3170495 := bstep (se 1 (by rfl) ⟨2377871, by rfl⟩ : syracuseStep 3170495 = 4755743) B4755743
theorem B2113663 : Blo 2113435 2113663 := bstep (se 1 (by rfl) ⟨1585247, by rfl⟩ : syracuseStep 2113663 = 3170495) B3170495
theorem B3170501 : Blo 2113435 3170501 := bbase (se 4 (by rfl) ⟨297234, by rfl⟩ : syracuseStep 3170501 = 594469) (by norm_num)
theorem B2113667 : Blo 2113435 2113667 := bstep (se 1 (by rfl) ⟨1585250, by rfl⟩ : syracuseStep 2113667 = 3170501) B3170501
theorem B3566821 : Blo 2113435 3566821 := bbase (se 4 (by rfl) ⟨334389, by rfl⟩ : syracuseStep 3566821 = 668779) (by norm_num)
theorem B4755761 : Blo 2113435 4755761 := bstep (se 2 (by rfl) ⟨1783410, by rfl⟩ : syracuseStep 4755761 = 3566821) B3566821
theorem B3170507 : Blo 2113435 3170507 := bstep (se 1 (by rfl) ⟨2377880, by rfl⟩ : syracuseStep 3170507 = 4755761) B4755761
theorem B2113671 : Blo 2113435 2113671 := bstep (se 1 (by rfl) ⟨1585253, by rfl⟩ : syracuseStep 2113671 = 3170507) B3170507
theorem B2377885 : Blo 2113435 2377885 := bbase (se 3 (by rfl) ⟨445853, by rfl⟩ : syracuseStep 2377885 = 891707) (by norm_num)
theorem B3170513 : Blo 2113435 3170513 := bstep (se 2 (by rfl) ⟨1188942, by rfl⟩ : syracuseStep 3170513 = 2377885) B2377885
theorem B2113675 : Blo 2113435 2113675 := bstep (se 1 (by rfl) ⟨1585256, by rfl⟩ : syracuseStep 2113675 = 3170513) B3170513
theorem B7133669 : Blo 2113435 7133669 := bbase (se 4 (by rfl) ⟨668781, by rfl⟩ : syracuseStep 7133669 = 1337563) (by norm_num)
theorem B4755779 : Blo 2113435 4755779 := bstep (se 1 (by rfl) ⟨3566834, by rfl⟩ : syracuseStep 4755779 = 7133669) B7133669
theorem B3170519 : Blo 2113435 3170519 := bstep (se 1 (by rfl) ⟨2377889, by rfl⟩ : syracuseStep 3170519 = 4755779) B4755779
theorem B2113679 : Blo 2113435 2113679 := bstep (se 1 (by rfl) ⟨1585259, by rfl⟩ : syracuseStep 2113679 = 3170519) B3170519
theorem B3170525 : Blo 2113435 3170525 := bbase (se 3 (by rfl) ⟨594473, by rfl⟩ : syracuseStep 3170525 = 1188947) (by norm_num)
theorem B2113683 : Blo 2113435 2113683 := bstep (se 1 (by rfl) ⟨1585262, by rfl⟩ : syracuseStep 2113683 = 3170525) B3170525
theorem B4755797 : Blo 2113435 4755797 := bbase (se 10 (by rfl) ⟨6966, by rfl⟩ : syracuseStep 4755797 = 13933) (by norm_num)
theorem B3170531 : Blo 2113435 3170531 := bstep (se 1 (by rfl) ⟨2377898, by rfl⟩ : syracuseStep 3170531 = 4755797) B4755797
theorem B2113687 : Blo 2113435 2113687 := bstep (se 1 (by rfl) ⟨1585265, by rfl⟩ : syracuseStep 2113687 = 3170531) B3170531
theorem B2711641 : Blo 2113435 2711641 := bbase (se 2 (by rfl) ⟨1016865, by rfl⟩ : syracuseStep 2711641 = 2033731) (by norm_num)
theorem B3615521 : Blo 2113435 3615521 := bstep (se 2 (by rfl) ⟨1355820, by rfl⟩ : syracuseStep 3615521 = 2711641) B2711641
theorem B38565557 : Blo 2113435 38565557 := bstep (se 5 (by rfl) ⟨1807760, by rfl⟩ : syracuseStep 38565557 = 3615521) B3615521
theorem B25710371 : Blo 2113435 25710371 := bstep (se 1 (by rfl) ⟨19282778, by rfl⟩ : syracuseStep 25710371 = 38565557) B38565557
theorem B17140247 : Blo 2113435 17140247 := bstep (se 1 (by rfl) ⟨12855185, by rfl⟩ : syracuseStep 17140247 = 25710371) B25710371
theorem B11426831 : Blo 2113435 11426831 := bstep (se 1 (by rfl) ⟨8570123, by rfl⟩ : syracuseStep 11426831 = 17140247) B17140247
theorem B7617887 : Blo 2113435 7617887 := bstep (se 1 (by rfl) ⟨5713415, by rfl⟩ : syracuseStep 7617887 = 11426831) B11426831
theorem B5078591 : Blo 2113435 5078591 := bstep (se 1 (by rfl) ⟨3808943, by rfl⟩ : syracuseStep 5078591 = 7617887) B7617887
theorem B3385727 : Blo 2113435 3385727 := bstep (se 1 (by rfl) ⟨2539295, by rfl⟩ : syracuseStep 3385727 = 5078591) B5078591
theorem B2257151 : Blo 2113435 2257151 := bstep (se 1 (by rfl) ⟨1692863, by rfl⟩ : syracuseStep 2257151 = 3385727) B3385727
theorem B6019069 : Blo 2113435 6019069 := bstep (se 3 (by rfl) ⟨1128575, by rfl⟩ : syracuseStep 6019069 = 2257151) B2257151
theorem B8025425 : Blo 2113435 8025425 := bstep (se 2 (by rfl) ⟨3009534, by rfl⟩ : syracuseStep 8025425 = 6019069) B6019069
theorem B5350283 : Blo 2113435 5350283 := bstep (se 1 (by rfl) ⟨4012712, by rfl⟩ : syracuseStep 5350283 = 8025425) B8025425
theorem B3566855 : Blo 2113435 3566855 := bstep (se 1 (by rfl) ⟨2675141, by rfl⟩ : syracuseStep 3566855 = 5350283) B5350283
theorem B2377903 : Blo 2113435 2377903 := bstep (se 1 (by rfl) ⟨1783427, by rfl⟩ : syracuseStep 2377903 = 3566855) B3566855
theorem B3170537 : Blo 2113435 3170537 := bstep (se 2 (by rfl) ⟨1188951, by rfl⟩ : syracuseStep 3170537 = 2377903) B2377903
theorem B2113691 : Blo 2113435 2113691 := bstep (se 1 (by rfl) ⟨1585268, by rfl⟩ : syracuseStep 2113691 = 3170537) B3170537
theorem B3808949 : Blo 2113435 3808949 := bbase (se 5 (by rfl) ⟨178544, by rfl⟩ : syracuseStep 3808949 = 357089) (by norm_num)
theorem B40628789 : Blo 2113435 40628789 := bstep (se 5 (by rfl) ⟨1904474, by rfl⟩ : syracuseStep 40628789 = 3808949) B3808949
theorem B27085859 : Blo 2113435 27085859 := bstep (se 1 (by rfl) ⟨20314394, by rfl⟩ : syracuseStep 27085859 = 40628789) B40628789
theorem B18057239 : Blo 2113435 18057239 := bstep (se 1 (by rfl) ⟨13542929, by rfl⟩ : syracuseStep 18057239 = 27085859) B27085859
theorem B12038159 : Blo 2113435 12038159 := bstep (se 1 (by rfl) ⟨9028619, by rfl⟩ : syracuseStep 12038159 = 18057239) B18057239
theorem B8025439 : Blo 2113435 8025439 := bstep (se 1 (by rfl) ⟨6019079, by rfl⟩ : syracuseStep 8025439 = 12038159) B12038159
theorem B10700585 : Blo 2113435 10700585 := bstep (se 2 (by rfl) ⟨4012719, by rfl⟩ : syracuseStep 10700585 = 8025439) B8025439
theorem B7133723 : Blo 2113435 7133723 := bstep (se 1 (by rfl) ⟨5350292, by rfl⟩ : syracuseStep 7133723 = 10700585) B10700585
theorem B4755815 : Blo 2113435 4755815 := bstep (se 1 (by rfl) ⟨3566861, by rfl⟩ : syracuseStep 4755815 = 7133723) B7133723
theorem B3170543 : Blo 2113435 3170543 := bstep (se 1 (by rfl) ⟨2377907, by rfl⟩ : syracuseStep 3170543 = 4755815) B4755815
theorem B2113695 : Blo 2113435 2113695 := bstep (se 1 (by rfl) ⟨1585271, by rfl⟩ : syracuseStep 2113695 = 3170543) B3170543
theorem B3170549 : Blo 2113435 3170549 := bbase (se 5 (by rfl) ⟨148619, by rfl⟩ : syracuseStep 3170549 = 297239) (by norm_num)
theorem B2113699 : Blo 2113435 2113699 := bstep (se 1 (by rfl) ⟨1585274, by rfl⟩ : syracuseStep 2113699 = 3170549) B3170549
theorem B4343549 : Blo 2113435 4343549 := bbase (se 3 (by rfl) ⟨814415, by rfl⟩ : syracuseStep 4343549 = 1628831) (by norm_num)
theorem B11582797 : Blo 2113435 11582797 := bstep (se 3 (by rfl) ⟨2171774, by rfl⟩ : syracuseStep 11582797 = 4343549) B4343549
theorem B15443729 : Blo 2113435 15443729 := bstep (se 2 (by rfl) ⟨5791398, by rfl⟩ : syracuseStep 15443729 = 11582797) B11582797
theorem B10295819 : Blo 2113435 10295819 := bstep (se 1 (by rfl) ⟨7721864, by rfl⟩ : syracuseStep 10295819 = 15443729) B15443729
theorem B6863879 : Blo 2113435 6863879 := bstep (se 1 (by rfl) ⟨5147909, by rfl⟩ : syracuseStep 6863879 = 10295819) B10295819
theorem B18303677 : Blo 2113435 18303677 := bstep (se 3 (by rfl) ⟨3431939, by rfl⟩ : syracuseStep 18303677 = 6863879) B6863879
theorem B12202451 : Blo 2113435 12202451 := bstep (se 1 (by rfl) ⟨9151838, by rfl⟩ : syracuseStep 12202451 = 18303677) B18303677
theorem B8134967 : Blo 2113435 8134967 := bstep (se 1 (by rfl) ⟨6101225, by rfl⟩ : syracuseStep 8134967 = 12202451) B12202451
theorem B5423311 : Blo 2113435 5423311 := bstep (se 1 (by rfl) ⟨4067483, by rfl⟩ : syracuseStep 5423311 = 8134967) B8134967
theorem B7231081 : Blo 2113435 7231081 := bstep (se 2 (by rfl) ⟨2711655, by rfl⟩ : syracuseStep 7231081 = 5423311) B5423311
theorem B9641441 : Blo 2113435 9641441 := bstep (se 2 (by rfl) ⟨3615540, by rfl⟩ : syracuseStep 9641441 = 7231081) B7231081
theorem B25710509 : Blo 2113435 25710509 := bstep (se 3 (by rfl) ⟨4820720, by rfl⟩ : syracuseStep 25710509 = 9641441) B9641441
theorem B17140339 : Blo 2113435 17140339 := bstep (se 1 (by rfl) ⟨12855254, by rfl⟩ : syracuseStep 17140339 = 25710509) B25710509
theorem B22853785 : Blo 2113435 22853785 := bstep (se 2 (by rfl) ⟨8570169, by rfl⟩ : syracuseStep 22853785 = 17140339) B17140339
theorem B30471713 : Blo 2113435 30471713 := bstep (se 2 (by rfl) ⟨11426892, by rfl⟩ : syracuseStep 30471713 = 22853785) B22853785
theorem B20314475 : Blo 2113435 20314475 := bstep (se 1 (by rfl) ⟨15235856, by rfl⟩ : syracuseStep 20314475 = 30471713) B30471713
theorem B13542983 : Blo 2113435 13542983 := bstep (se 1 (by rfl) ⟨10157237, by rfl⟩ : syracuseStep 13542983 = 20314475) B20314475
theorem B9028655 : Blo 2113435 9028655 := bstep (se 1 (by rfl) ⟨6771491, by rfl⟩ : syracuseStep 9028655 = 13542983) B13542983
theorem B6019103 : Blo 2113435 6019103 := bstep (se 1 (by rfl) ⟨4514327, by rfl⟩ : syracuseStep 6019103 = 9028655) B9028655
theorem B4012735 : Blo 2113435 4012735 := bstep (se 1 (by rfl) ⟨3009551, by rfl⟩ : syracuseStep 4012735 = 6019103) B6019103
theorem B5350313 : Blo 2113435 5350313 := bstep (se 2 (by rfl) ⟨2006367, by rfl⟩ : syracuseStep 5350313 = 4012735) B4012735
theorem B3566875 : Blo 2113435 3566875 := bstep (se 1 (by rfl) ⟨2675156, by rfl⟩ : syracuseStep 3566875 = 5350313) B5350313
theorem B4755833 : Blo 2113435 4755833 := bstep (se 2 (by rfl) ⟨1783437, by rfl⟩ : syracuseStep 4755833 = 3566875) B3566875
theorem B3170555 : Blo 2113435 3170555 := bstep (se 1 (by rfl) ⟨2377916, by rfl⟩ : syracuseStep 3170555 = 4755833) B4755833
theorem B2113703 : Blo 2113435 2113703 := bstep (se 1 (by rfl) ⟨1585277, by rfl⟩ : syracuseStep 2113703 = 3170555) B3170555
theorem B2377921 : Blo 2113435 2377921 := bbase (se 2 (by rfl) ⟨891720, by rfl⟩ : syracuseStep 2377921 = 1783441) (by norm_num)
theorem B3170561 : Blo 2113435 3170561 := bstep (se 2 (by rfl) ⟨1188960, by rfl⟩ : syracuseStep 3170561 = 2377921) B2377921
theorem B2113707 : Blo 2113435 2113707 := bstep (se 1 (by rfl) ⟨1585280, by rfl⟩ : syracuseStep 2113707 = 3170561) B3170561
theorem B5350333 : Blo 2113435 5350333 := bbase (se 3 (by rfl) ⟨1003187, by rfl⟩ : syracuseStep 5350333 = 2006375) (by norm_num)
theorem B7133777 : Blo 2113435 7133777 := bstep (se 2 (by rfl) ⟨2675166, by rfl⟩ : syracuseStep 7133777 = 5350333) B5350333
theorem B4755851 : Blo 2113435 4755851 := bstep (se 1 (by rfl) ⟨3566888, by rfl⟩ : syracuseStep 4755851 = 7133777) B7133777
theorem B3170567 : Blo 2113435 3170567 := bstep (se 1 (by rfl) ⟨2377925, by rfl⟩ : syracuseStep 3170567 = 4755851) B4755851
theorem B2113711 : Blo 2113435 2113711 := bstep (se 1 (by rfl) ⟨1585283, by rfl⟩ : syracuseStep 2113711 = 3170567) B3170567
theorem B3170573 : Blo 2113435 3170573 := bbase (se 3 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 3170573 = 1188965) (by norm_num)
theorem B2113715 : Blo 2113435 2113715 := bstep (se 1 (by rfl) ⟨1585286, by rfl⟩ : syracuseStep 2113715 = 3170573) B3170573
theorem B4755869 : Blo 2113435 4755869 := bbase (se 3 (by rfl) ⟨891725, by rfl⟩ : syracuseStep 4755869 = 1783451) (by norm_num)
theorem B3170579 : Blo 2113435 3170579 := bstep (se 1 (by rfl) ⟨2377934, by rfl⟩ : syracuseStep 3170579 = 4755869) B4755869
theorem B2113719 : Blo 2113435 2113719 := bstep (se 1 (by rfl) ⟨1585289, by rfl⟩ : syracuseStep 2113719 = 3170579) B3170579
theorem B3566909 : Blo 2113435 3566909 := bbase (se 3 (by rfl) ⟨668795, by rfl⟩ : syracuseStep 3566909 = 1337591) (by norm_num)
theorem B2377939 : Blo 2113435 2377939 := bstep (se 1 (by rfl) ⟨1783454, by rfl⟩ : syracuseStep 2377939 = 3566909) B3566909
theorem B3170585 : Blo 2113435 3170585 := bstep (se 2 (by rfl) ⟨1188969, by rfl⟩ : syracuseStep 3170585 = 2377939) B2377939
theorem B2113723 : Blo 2113435 2113723 := bstep (se 1 (by rfl) ⟨1585292, by rfl⟩ : syracuseStep 2113723 = 3170585) B3170585
theorem B2257189 : Blo 2113435 2257189 := bbase (se 4 (by rfl) ⟨211611, by rfl⟩ : syracuseStep 2257189 = 423223) (by norm_num)
theorem B12038341 : Blo 2113435 12038341 := bstep (se 4 (by rfl) ⟨1128594, by rfl⟩ : syracuseStep 12038341 = 2257189) B2257189
theorem B16051121 : Blo 2113435 16051121 := bstep (se 2 (by rfl) ⟨6019170, by rfl⟩ : syracuseStep 16051121 = 12038341) B12038341
theorem B10700747 : Blo 2113435 10700747 := bstep (se 1 (by rfl) ⟨8025560, by rfl⟩ : syracuseStep 10700747 = 16051121) B16051121
theorem B7133831 : Blo 2113435 7133831 := bstep (se 1 (by rfl) ⟨5350373, by rfl⟩ : syracuseStep 7133831 = 10700747) B10700747
theorem B4755887 : Blo 2113435 4755887 := bstep (se 1 (by rfl) ⟨3566915, by rfl⟩ : syracuseStep 4755887 = 7133831) B7133831
theorem B3170591 : Blo 2113435 3170591 := bstep (se 1 (by rfl) ⟨2377943, by rfl⟩ : syracuseStep 3170591 = 4755887) B4755887
theorem B2113727 : Blo 2113435 2113727 := bstep (se 1 (by rfl) ⟨1585295, by rfl⟩ : syracuseStep 2113727 = 3170591) B3170591
theorem B3170597 : Blo 2113435 3170597 := bbase (se 4 (by rfl) ⟨297243, by rfl⟩ : syracuseStep 3170597 = 594487) (by norm_num)
theorem B2113731 : Blo 2113435 2113731 := bstep (se 1 (by rfl) ⟨1585298, by rfl⟩ : syracuseStep 2113731 = 3170597) B3170597
theorem B2675197 : Blo 2113435 2675197 := bbase (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) (by norm_num)
theorem B3566929 : Blo 2113435 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B4755905 : Blo 2113435 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B3170603 : Blo 2113435 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B2113735 : Blo 2113435 2113735 := bstep (se 1 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 2113735 = 3170603) B3170603
theorem B2377957 : Blo 2113435 2377957 := bbase (se 4 (by rfl) ⟨222933, by rfl⟩ : syracuseStep 2377957 = 445867) (by norm_num)
theorem B3170609 : Blo 2113435 3170609 := bstep (se 2 (by rfl) ⟨1188978, by rfl⟩ : syracuseStep 3170609 = 2377957) B2377957
theorem B2113739 : Blo 2113435 2113739 := bstep (se 1 (by rfl) ⟨1585304, by rfl⟩ : syracuseStep 2113739 = 3170609) B3170609
theorem B4514413 : Blo 2113435 4514413 := bbase (se 3 (by rfl) ⟨846452, by rfl⟩ : syracuseStep 4514413 = 1692905) (by norm_num)
theorem B6019217 : Blo 2113435 6019217 := bstep (se 2 (by rfl) ⟨2257206, by rfl⟩ : syracuseStep 6019217 = 4514413) B4514413
theorem B4012811 : Blo 2113435 4012811 := bstep (se 1 (by rfl) ⟨3009608, by rfl⟩ : syracuseStep 4012811 = 6019217) B6019217
theorem B2675207 : Blo 2113435 2675207 := bstep (se 1 (by rfl) ⟨2006405, by rfl⟩ : syracuseStep 2675207 = 4012811) B4012811
theorem B7133885 : Blo 2113435 7133885 := bstep (se 3 (by rfl) ⟨1337603, by rfl⟩ : syracuseStep 7133885 = 2675207) B2675207
theorem B4755923 : Blo 2113435 4755923 := bstep (se 1 (by rfl) ⟨3566942, by rfl⟩ : syracuseStep 4755923 = 7133885) B7133885
theorem B3170615 : Blo 2113435 3170615 := bstep (se 1 (by rfl) ⟨2377961, by rfl⟩ : syracuseStep 3170615 = 4755923) B4755923
theorem B2113743 : Blo 2113435 2113743 := bstep (se 1 (by rfl) ⟨1585307, by rfl⟩ : syracuseStep 2113743 = 3170615) B3170615
theorem B3170621 : Blo 2113435 3170621 := bbase (se 3 (by rfl) ⟨594491, by rfl⟩ : syracuseStep 3170621 = 1188983) (by norm_num)
theorem B2113747 : Blo 2113435 2113747 := bstep (se 1 (by rfl) ⟨1585310, by rfl⟩ : syracuseStep 2113747 = 3170621) B3170621
theorem B4755941 : Blo 2113435 4755941 := bbase (se 4 (by rfl) ⟨445869, by rfl⟩ : syracuseStep 4755941 = 891739) (by norm_num)
theorem B3170627 : Blo 2113435 3170627 := bstep (se 1 (by rfl) ⟨2377970, by rfl⟩ : syracuseStep 3170627 = 4755941) B4755941
theorem B2113751 : Blo 2113435 2113751 := bstep (se 1 (by rfl) ⟨1585313, by rfl⟩ : syracuseStep 2113751 = 3170627) B3170627
theorem B5350445 : Blo 2113435 5350445 := bbase (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) (by norm_num)
theorem B3566963 : Blo 2113435 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B2377975 : Blo 2113435 2377975 := bstep (se 1 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 2377975 = 3566963) B3566963
theorem B3170633 : Blo 2113435 3170633 := bstep (se 2 (by rfl) ⟨1188987, by rfl⟩ : syracuseStep 3170633 = 2377975) B2377975
theorem B2113755 : Blo 2113435 2113755 := bstep (se 1 (by rfl) ⟨1585316, by rfl⟩ : syracuseStep 2113755 = 3170633) B3170633
theorem B14462549 : Blo 2113435 14462549 := bbase (se 8 (by rfl) ⟨84741, by rfl⟩ : syracuseStep 14462549 = 169483) (by norm_num)
theorem B9641699 : Blo 2113435 9641699 := bstep (se 1 (by rfl) ⟨7231274, by rfl⟩ : syracuseStep 9641699 = 14462549) B14462549
theorem B6427799 : Blo 2113435 6427799 := bstep (se 1 (by rfl) ⟨4820849, by rfl⟩ : syracuseStep 6427799 = 9641699) B9641699
theorem B4285199 : Blo 2113435 4285199 := bstep (se 1 (by rfl) ⟨3213899, by rfl⟩ : syracuseStep 4285199 = 6427799) B6427799
theorem B2856799 : Blo 2113435 2856799 := bstep (se 1 (by rfl) ⟨2142599, by rfl⟩ : syracuseStep 2856799 = 4285199) B4285199
theorem B15236261 : Blo 2113435 15236261 := bstep (se 4 (by rfl) ⟨1428399, by rfl⟩ : syracuseStep 15236261 = 2856799) B2856799
theorem B10157507 : Blo 2113435 10157507 := bstep (se 1 (by rfl) ⟨7618130, by rfl⟩ : syracuseStep 10157507 = 15236261) B15236261
theorem B6771671 : Blo 2113435 6771671 := bstep (se 1 (by rfl) ⟨5078753, by rfl⟩ : syracuseStep 6771671 = 10157507) B10157507
theorem B4514447 : Blo 2113435 4514447 := bstep (se 1 (by rfl) ⟨3385835, by rfl⟩ : syracuseStep 4514447 = 6771671) B6771671
theorem B3009631 : Blo 2113435 3009631 := bstep (se 1 (by rfl) ⟨2257223, by rfl⟩ : syracuseStep 3009631 = 4514447) B4514447
theorem B4012841 : Blo 2113435 4012841 := bstep (se 2 (by rfl) ⟨1504815, by rfl⟩ : syracuseStep 4012841 = 3009631) B3009631
theorem B10700909 : Blo 2113435 10700909 := bstep (se 3 (by rfl) ⟨2006420, by rfl⟩ : syracuseStep 10700909 = 4012841) B4012841
theorem B7133939 : Blo 2113435 7133939 := bstep (se 1 (by rfl) ⟨5350454, by rfl⟩ : syracuseStep 7133939 = 10700909) B10700909
theorem B4755959 : Blo 2113435 4755959 := bstep (se 1 (by rfl) ⟨3566969, by rfl⟩ : syracuseStep 4755959 = 7133939) B7133939
theorem B3170639 : Blo 2113435 3170639 := bstep (se 1 (by rfl) ⟨2377979, by rfl⟩ : syracuseStep 3170639 = 4755959) B4755959
theorem B2113759 : Blo 2113435 2113759 := bstep (se 1 (by rfl) ⟨1585319, by rfl⟩ : syracuseStep 2113759 = 3170639) B3170639
theorem B3170645 : Blo 2113435 3170645 := bbase (se 10 (by rfl) ⟨4644, by rfl⟩ : syracuseStep 3170645 = 9289) (by norm_num)
theorem B2113763 : Blo 2113435 2113763 := bstep (se 1 (by rfl) ⟨1585322, by rfl⟩ : syracuseStep 2113763 = 3170645) B3170645
theorem B6019285 : Blo 2113435 6019285 := bbase (se 7 (by rfl) ⟨70538, by rfl⟩ : syracuseStep 6019285 = 141077) (by norm_num)
theorem B8025713 : Blo 2113435 8025713 := bstep (se 2 (by rfl) ⟨3009642, by rfl⟩ : syracuseStep 8025713 = 6019285) B6019285
theorem B5350475 : Blo 2113435 5350475 := bstep (se 1 (by rfl) ⟨4012856, by rfl⟩ : syracuseStep 5350475 = 8025713) B8025713
theorem B3566983 : Blo 2113435 3566983 := bstep (se 1 (by rfl) ⟨2675237, by rfl⟩ : syracuseStep 3566983 = 5350475) B5350475
theorem B4755977 : Blo 2113435 4755977 := bstep (se 2 (by rfl) ⟨1783491, by rfl⟩ : syracuseStep 4755977 = 3566983) B3566983
theorem B3170651 : Blo 2113435 3170651 := bstep (se 1 (by rfl) ⟨2377988, by rfl⟩ : syracuseStep 3170651 = 4755977) B4755977
theorem B2113767 : Blo 2113435 2113767 := bstep (se 1 (by rfl) ⟨1585325, by rfl⟩ : syracuseStep 2113767 = 3170651) B3170651
theorem B2377993 : Blo 2113435 2377993 := bbase (se 2 (by rfl) ⟨891747, by rfl⟩ : syracuseStep 2377993 = 1783495) (by norm_num)
theorem B3170657 : Blo 2113435 3170657 := bstep (se 2 (by rfl) ⟨1188996, by rfl⟩ : syracuseStep 3170657 = 2377993) B2377993
theorem B2113771 : Blo 2113435 2113771 := bstep (se 1 (by rfl) ⟨1585328, by rfl⟩ : syracuseStep 2113771 = 3170657) B3170657
theorem B4820885 : Blo 2113435 4820885 := bbase (se 6 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 4820885 = 225979) (by norm_num)
theorem B3213923 : Blo 2113435 3213923 := bstep (se 1 (by rfl) ⟨2410442, by rfl⟩ : syracuseStep 3213923 = 4820885) B4820885
theorem B8570461 : Blo 2113435 8570461 := bstep (se 3 (by rfl) ⟨1606961, by rfl⟩ : syracuseStep 8570461 = 3213923) B3213923
theorem B11427281 : Blo 2113435 11427281 := bstep (se 2 (by rfl) ⟨4285230, by rfl⟩ : syracuseStep 11427281 = 8570461) B8570461
theorem B7618187 : Blo 2113435 7618187 := bstep (se 1 (by rfl) ⟨5713640, by rfl⟩ : syracuseStep 7618187 = 11427281) B11427281
theorem B5078791 : Blo 2113435 5078791 := bstep (se 1 (by rfl) ⟨3809093, by rfl⟩ : syracuseStep 5078791 = 7618187) B7618187
theorem B27086885 : Blo 2113435 27086885 := bstep (se 4 (by rfl) ⟨2539395, by rfl⟩ : syracuseStep 27086885 = 5078791) B5078791
theorem B18057923 : Blo 2113435 18057923 := bstep (se 1 (by rfl) ⟨13543442, by rfl⟩ : syracuseStep 18057923 = 27086885) B27086885
theorem B12038615 : Blo 2113435 12038615 := bstep (se 1 (by rfl) ⟨9028961, by rfl⟩ : syracuseStep 12038615 = 18057923) B18057923
theorem B8025743 : Blo 2113435 8025743 := bstep (se 1 (by rfl) ⟨6019307, by rfl⟩ : syracuseStep 8025743 = 12038615) B12038615
theorem B5350495 : Blo 2113435 5350495 := bstep (se 1 (by rfl) ⟨4012871, by rfl⟩ : syracuseStep 5350495 = 8025743) B8025743
theorem B7133993 : Blo 2113435 7133993 := bstep (se 2 (by rfl) ⟨2675247, by rfl⟩ : syracuseStep 7133993 = 5350495) B5350495
theorem B4755995 : Blo 2113435 4755995 := bstep (se 1 (by rfl) ⟨3566996, by rfl⟩ : syracuseStep 4755995 = 7133993) B7133993
theorem B3170663 : Blo 2113435 3170663 := bstep (se 1 (by rfl) ⟨2377997, by rfl⟩ : syracuseStep 3170663 = 4755995) B4755995
theorem B2113775 : Blo 2113435 2113775 := bstep (se 1 (by rfl) ⟨1585331, by rfl⟩ : syracuseStep 2113775 = 3170663) B3170663
theorem B3170669 : Blo 2113435 3170669 := bbase (se 3 (by rfl) ⟨594500, by rfl⟩ : syracuseStep 3170669 = 1189001) (by norm_num)
theorem B2113779 : Blo 2113435 2113779 := bstep (se 1 (by rfl) ⟨1585334, by rfl⟩ : syracuseStep 2113779 = 3170669) B3170669
theorem B4756013 : Blo 2113435 4756013 := bbase (se 3 (by rfl) ⟨891752, by rfl⟩ : syracuseStep 4756013 = 1783505) (by norm_num)
theorem B3170675 : Blo 2113435 3170675 := bstep (se 1 (by rfl) ⟨2378006, by rfl⟩ : syracuseStep 3170675 = 4756013) B4756013
theorem B2113783 : Blo 2113435 2113783 := bstep (se 1 (by rfl) ⟨1585337, by rfl⟩ : syracuseStep 2113783 = 3170675) B3170675
theorem B20315285 : Blo 2113435 20315285 := bbase (se 6 (by rfl) ⟨476139, by rfl⟩ : syracuseStep 20315285 = 952279) (by norm_num)
theorem B13543523 : Blo 2113435 13543523 := bstep (se 1 (by rfl) ⟨10157642, by rfl⟩ : syracuseStep 13543523 = 20315285) B20315285
theorem B9029015 : Blo 2113435 9029015 := bstep (se 1 (by rfl) ⟨6771761, by rfl⟩ : syracuseStep 9029015 = 13543523) B13543523
theorem B6019343 : Blo 2113435 6019343 := bstep (se 1 (by rfl) ⟨4514507, by rfl⟩ : syracuseStep 6019343 = 9029015) B9029015
theorem B4012895 : Blo 2113435 4012895 := bstep (se 1 (by rfl) ⟨3009671, by rfl⟩ : syracuseStep 4012895 = 6019343) B6019343
theorem B2675263 : Blo 2113435 2675263 := bstep (se 1 (by rfl) ⟨2006447, by rfl⟩ : syracuseStep 2675263 = 4012895) B4012895
theorem B3567017 : Blo 2113435 3567017 := bstep (se 2 (by rfl) ⟨1337631, by rfl⟩ : syracuseStep 3567017 = 2675263) B2675263
theorem B2378011 : Blo 2113435 2378011 := bstep (se 1 (by rfl) ⟨1783508, by rfl⟩ : syracuseStep 2378011 = 3567017) B3567017
theorem B3170681 : Blo 2113435 3170681 := bstep (se 2 (by rfl) ⟨1189005, by rfl⟩ : syracuseStep 3170681 = 2378011) B2378011
theorem B2113787 : Blo 2113435 2113787 := bstep (se 1 (by rfl) ⟨1585340, by rfl⟩ : syracuseStep 2113787 = 3170681) B3170681
theorem B36116117 : Blo 2113435 36116117 := bbase (se 6 (by rfl) ⟨846471, by rfl⟩ : syracuseStep 36116117 = 1692943) (by norm_num)
theorem B24077411 : Blo 2113435 24077411 := bstep (se 1 (by rfl) ⟨18058058, by rfl⟩ : syracuseStep 24077411 = 36116117) B36116117
theorem B16051607 : Blo 2113435 16051607 := bstep (se 1 (by rfl) ⟨12038705, by rfl⟩ : syracuseStep 16051607 = 24077411) B24077411
theorem B10701071 : Blo 2113435 10701071 := bstep (se 1 (by rfl) ⟨8025803, by rfl⟩ : syracuseStep 10701071 = 16051607) B16051607
theorem B7134047 : Blo 2113435 7134047 := bstep (se 1 (by rfl) ⟨5350535, by rfl⟩ : syracuseStep 7134047 = 10701071) B10701071
theorem B4756031 : Blo 2113435 4756031 := bstep (se 1 (by rfl) ⟨3567023, by rfl⟩ : syracuseStep 4756031 = 7134047) B7134047
theorem B3170687 : Blo 2113435 3170687 := bstep (se 1 (by rfl) ⟨2378015, by rfl⟩ : syracuseStep 3170687 = 4756031) B4756031
theorem B2113791 : Blo 2113435 2113791 := bstep (se 1 (by rfl) ⟨1585343, by rfl⟩ : syracuseStep 2113791 = 3170687) B3170687
theorem B3170693 : Blo 2113435 3170693 := bbase (se 4 (by rfl) ⟨297252, by rfl⟩ : syracuseStep 3170693 = 594505) (by norm_num)
theorem B2113795 : Blo 2113435 2113795 := bstep (se 1 (by rfl) ⟨1585346, by rfl⟩ : syracuseStep 2113795 = 3170693) B3170693
theorem B3567037 : Blo 2113435 3567037 := bbase (se 3 (by rfl) ⟨668819, by rfl⟩ : syracuseStep 3567037 = 1337639) (by norm_num)
theorem B4756049 : Blo 2113435 4756049 := bstep (se 2 (by rfl) ⟨1783518, by rfl⟩ : syracuseStep 4756049 = 3567037) B3567037
theorem B3170699 : Blo 2113435 3170699 := bstep (se 1 (by rfl) ⟨2378024, by rfl⟩ : syracuseStep 3170699 = 4756049) B4756049
theorem B2113799 : Blo 2113435 2113799 := bstep (se 1 (by rfl) ⟨1585349, by rfl⟩ : syracuseStep 2113799 = 3170699) B3170699
theorem B2378029 : Blo 2113435 2378029 := bbase (se 3 (by rfl) ⟨445880, by rfl⟩ : syracuseStep 2378029 = 891761) (by norm_num)
theorem B3170705 : Blo 2113435 3170705 := bstep (se 2 (by rfl) ⟨1189014, by rfl⟩ : syracuseStep 3170705 = 2378029) B2378029
theorem B2113803 : Blo 2113435 2113803 := bstep (se 1 (by rfl) ⟨1585352, by rfl⟩ : syracuseStep 2113803 = 3170705) B3170705
theorem B7134101 : Blo 2113435 7134101 := bbase (se 6 (by rfl) ⟨167205, by rfl⟩ : syracuseStep 7134101 = 334411) (by norm_num)
theorem B4756067 : Blo 2113435 4756067 := bstep (se 1 (by rfl) ⟨3567050, by rfl⟩ : syracuseStep 4756067 = 7134101) B7134101
theorem B3170711 : Blo 2113435 3170711 := bstep (se 1 (by rfl) ⟨2378033, by rfl⟩ : syracuseStep 3170711 = 4756067) B4756067
theorem B2113807 : Blo 2113435 2113807 := bstep (se 1 (by rfl) ⟨1585355, by rfl⟩ : syracuseStep 2113807 = 3170711) B3170711
theorem B3170717 : Blo 2113435 3170717 := bbase (se 3 (by rfl) ⟨594509, by rfl⟩ : syracuseStep 3170717 = 1189019) (by norm_num)
theorem B2113811 : Blo 2113435 2113811 := bstep (se 1 (by rfl) ⟨1585358, by rfl⟩ : syracuseStep 2113811 = 3170717) B3170717
theorem B4756085 : Blo 2113435 4756085 := bbase (se 5 (by rfl) ⟨222941, by rfl⟩ : syracuseStep 4756085 = 445883) (by norm_num)
theorem B3170723 : Blo 2113435 3170723 := bstep (se 1 (by rfl) ⟨2378042, by rfl⟩ : syracuseStep 3170723 = 4756085) B4756085
theorem B2113815 : Blo 2113435 2113815 := bstep (se 1 (by rfl) ⟨1585361, by rfl⟩ : syracuseStep 2113815 = 3170723) B3170723
theorem B15236693 : Blo 2113435 15236693 := bbase (se 8 (by rfl) ⟨89277, by rfl⟩ : syracuseStep 15236693 = 178555) (by norm_num)
theorem B10157795 : Blo 2113435 10157795 := bstep (se 1 (by rfl) ⟨7618346, by rfl⟩ : syracuseStep 10157795 = 15236693) B15236693
theorem B6771863 : Blo 2113435 6771863 := bstep (se 1 (by rfl) ⟨5078897, by rfl⟩ : syracuseStep 6771863 = 10157795) B10157795
theorem B18058301 : Blo 2113435 18058301 := bstep (se 3 (by rfl) ⟨3385931, by rfl⟩ : syracuseStep 18058301 = 6771863) B6771863
theorem B12038867 : Blo 2113435 12038867 := bstep (se 1 (by rfl) ⟨9029150, by rfl⟩ : syracuseStep 12038867 = 18058301) B18058301
theorem B8025911 : Blo 2113435 8025911 := bstep (se 1 (by rfl) ⟨6019433, by rfl⟩ : syracuseStep 8025911 = 12038867) B12038867
theorem B5350607 : Blo 2113435 5350607 := bstep (se 1 (by rfl) ⟨4012955, by rfl⟩ : syracuseStep 5350607 = 8025911) B8025911
theorem B3567071 : Blo 2113435 3567071 := bstep (se 1 (by rfl) ⟨2675303, by rfl⟩ : syracuseStep 3567071 = 5350607) B5350607
theorem B2378047 : Blo 2113435 2378047 := bstep (se 1 (by rfl) ⟨1783535, by rfl⟩ : syracuseStep 2378047 = 3567071) B3567071
theorem B3170729 : Blo 2113435 3170729 := bstep (se 2 (by rfl) ⟨1189023, by rfl⟩ : syracuseStep 3170729 = 2378047) B2378047
theorem B2113819 : Blo 2113435 2113819 := bstep (se 1 (by rfl) ⟨1585364, by rfl⟩ : syracuseStep 2113819 = 3170729) B3170729
theorem B8025925 : Blo 2113435 8025925 := bbase (se 4 (by rfl) ⟨752430, by rfl⟩ : syracuseStep 8025925 = 1504861) (by norm_num)
theorem B10701233 : Blo 2113435 10701233 := bstep (se 2 (by rfl) ⟨4012962, by rfl⟩ : syracuseStep 10701233 = 8025925) B8025925
theorem B7134155 : Blo 2113435 7134155 := bstep (se 1 (by rfl) ⟨5350616, by rfl⟩ : syracuseStep 7134155 = 10701233) B10701233
theorem B4756103 : Blo 2113435 4756103 := bstep (se 1 (by rfl) ⟨3567077, by rfl⟩ : syracuseStep 4756103 = 7134155) B7134155
theorem B3170735 : Blo 2113435 3170735 := bstep (se 1 (by rfl) ⟨2378051, by rfl⟩ : syracuseStep 3170735 = 4756103) B4756103
theorem B2113823 : Blo 2113435 2113823 := bstep (se 1 (by rfl) ⟨1585367, by rfl⟩ : syracuseStep 2113823 = 3170735) B3170735
theorem B3170741 : Blo 2113435 3170741 := bbase (se 5 (by rfl) ⟨148628, by rfl⟩ : syracuseStep 3170741 = 297257) (by norm_num)
theorem B2113827 : Blo 2113435 2113827 := bstep (se 1 (by rfl) ⟨1585370, by rfl⟩ : syracuseStep 2113827 = 3170741) B3170741
theorem B5350637 : Blo 2113435 5350637 := bbase (se 3 (by rfl) ⟨1003244, by rfl⟩ : syracuseStep 5350637 = 2006489) (by norm_num)
theorem B3567091 : Blo 2113435 3567091 := bstep (se 1 (by rfl) ⟨2675318, by rfl⟩ : syracuseStep 3567091 = 5350637) B5350637
theorem B4756121 : Blo 2113435 4756121 := bstep (se 2 (by rfl) ⟨1783545, by rfl⟩ : syracuseStep 4756121 = 3567091) B3567091
theorem B3170747 : Blo 2113435 3170747 := bstep (se 1 (by rfl) ⟨2378060, by rfl⟩ : syracuseStep 3170747 = 4756121) B4756121
theorem B2113831 : Blo 2113435 2113831 := bstep (se 1 (by rfl) ⟨1585373, by rfl⟩ : syracuseStep 2113831 = 3170747) B3170747
theorem B2378065 : Blo 2113435 2378065 := bbase (se 2 (by rfl) ⟨891774, by rfl⟩ : syracuseStep 2378065 = 1783549) (by norm_num)
theorem B3170753 : Blo 2113435 3170753 := bstep (se 2 (by rfl) ⟨1189032, by rfl⟩ : syracuseStep 3170753 = 2378065) B2378065
theorem B2113835 : Blo 2113435 2113835 := bstep (se 1 (by rfl) ⟨1585376, by rfl⟩ : syracuseStep 2113835 = 3170753) B3170753
theorem B2257309 : Blo 2113435 2257309 := bbase (se 3 (by rfl) ⟨423245, by rfl⟩ : syracuseStep 2257309 = 846491) (by norm_num)
theorem B3009745 : Blo 2113435 3009745 := bstep (se 2 (by rfl) ⟨1128654, by rfl⟩ : syracuseStep 3009745 = 2257309) B2257309
theorem B4012993 : Blo 2113435 4012993 := bstep (se 2 (by rfl) ⟨1504872, by rfl⟩ : syracuseStep 4012993 = 3009745) B3009745
theorem B5350657 : Blo 2113435 5350657 := bstep (se 2 (by rfl) ⟨2006496, by rfl⟩ : syracuseStep 5350657 = 4012993) B4012993
theorem B7134209 : Blo 2113435 7134209 := bstep (se 2 (by rfl) ⟨2675328, by rfl⟩ : syracuseStep 7134209 = 5350657) B5350657
theorem B4756139 : Blo 2113435 4756139 := bstep (se 1 (by rfl) ⟨3567104, by rfl⟩ : syracuseStep 4756139 = 7134209) B7134209
theorem B3170759 : Blo 2113435 3170759 := bstep (se 1 (by rfl) ⟨2378069, by rfl⟩ : syracuseStep 3170759 = 4756139) B4756139
theorem B2113839 : Blo 2113435 2113839 := bstep (se 1 (by rfl) ⟨1585379, by rfl⟩ : syracuseStep 2113839 = 3170759) B3170759
theorem B3170765 : Blo 2113435 3170765 := bbase (se 3 (by rfl) ⟨594518, by rfl⟩ : syracuseStep 3170765 = 1189037) (by norm_num)
theorem B2113843 : Blo 2113435 2113843 := bstep (se 1 (by rfl) ⟨1585382, by rfl⟩ : syracuseStep 2113843 = 3170765) B3170765
theorem B4756157 : Blo 2113435 4756157 := bbase (se 3 (by rfl) ⟨891779, by rfl⟩ : syracuseStep 4756157 = 1783559) (by norm_num)
theorem B3170771 : Blo 2113435 3170771 := bstep (se 1 (by rfl) ⟨2378078, by rfl⟩ : syracuseStep 3170771 = 4756157) B4756157
theorem B2113847 : Blo 2113435 2113847 := bstep (se 1 (by rfl) ⟨1585385, by rfl⟩ : syracuseStep 2113847 = 3170771) B3170771
theorem B3567125 : Blo 2113435 3567125 := bbase (se 6 (by rfl) ⟨83604, by rfl⟩ : syracuseStep 3567125 = 167209) (by norm_num)
theorem B2378083 : Blo 2113435 2378083 := bstep (se 1 (by rfl) ⟨1783562, by rfl⟩ : syracuseStep 2378083 = 3567125) B3567125
theorem B3170777 : Blo 2113435 3170777 := bstep (se 2 (by rfl) ⟨1189041, by rfl⟩ : syracuseStep 3170777 = 2378083) B2378083
theorem B2113851 : Blo 2113435 2113851 := bstep (se 1 (by rfl) ⟨1585388, by rfl⟩ : syracuseStep 2113851 = 3170777) B3170777
theorem B5423701 : Blo 2113435 5423701 := bbase (se 8 (by rfl) ⟨31779, by rfl⟩ : syracuseStep 5423701 = 63559) (by norm_num)
theorem B7231601 : Blo 2113435 7231601 := bstep (se 2 (by rfl) ⟨2711850, by rfl⟩ : syracuseStep 7231601 = 5423701) B5423701
theorem B4821067 : Blo 2113435 4821067 := bstep (se 1 (by rfl) ⟨3615800, by rfl⟩ : syracuseStep 4821067 = 7231601) B7231601
theorem B6428089 : Blo 2113435 6428089 := bstep (se 2 (by rfl) ⟨2410533, by rfl⟩ : syracuseStep 6428089 = 4821067) B4821067
theorem B8570785 : Blo 2113435 8570785 := bstep (se 2 (by rfl) ⟨3214044, by rfl⟩ : syracuseStep 8570785 = 6428089) B6428089
theorem B11427713 : Blo 2113435 11427713 := bstep (se 2 (by rfl) ⟨4285392, by rfl⟩ : syracuseStep 11427713 = 8570785) B8570785
theorem B7618475 : Blo 2113435 7618475 := bstep (se 1 (by rfl) ⟨5713856, by rfl⟩ : syracuseStep 7618475 = 11427713) B11427713
theorem B20315933 : Blo 2113435 20315933 := bstep (se 3 (by rfl) ⟨3809237, by rfl⟩ : syracuseStep 20315933 = 7618475) B7618475
theorem B13543955 : Blo 2113435 13543955 := bstep (se 1 (by rfl) ⟨10157966, by rfl⟩ : syracuseStep 13543955 = 20315933) B20315933
theorem B9029303 : Blo 2113435 9029303 := bstep (se 1 (by rfl) ⟨6771977, by rfl⟩ : syracuseStep 9029303 = 13543955) B13543955
theorem B6019535 : Blo 2113435 6019535 := bstep (se 1 (by rfl) ⟨4514651, by rfl⟩ : syracuseStep 6019535 = 9029303) B9029303
theorem B16052093 : Blo 2113435 16052093 := bstep (se 3 (by rfl) ⟨3009767, by rfl⟩ : syracuseStep 16052093 = 6019535) B6019535
theorem B10701395 : Blo 2113435 10701395 := bstep (se 1 (by rfl) ⟨8026046, by rfl⟩ : syracuseStep 10701395 = 16052093) B16052093
theorem B7134263 : Blo 2113435 7134263 := bstep (se 1 (by rfl) ⟨5350697, by rfl⟩ : syracuseStep 7134263 = 10701395) B10701395
theorem B4756175 : Blo 2113435 4756175 := bstep (se 1 (by rfl) ⟨3567131, by rfl⟩ : syracuseStep 4756175 = 7134263) B7134263
theorem B3170783 : Blo 2113435 3170783 := bstep (se 1 (by rfl) ⟨2378087, by rfl⟩ : syracuseStep 3170783 = 4756175) B4756175
theorem B2113855 : Blo 2113435 2113855 := bstep (se 1 (by rfl) ⟨1585391, by rfl⟩ : syracuseStep 2113855 = 3170783) B3170783
theorem B3170789 : Blo 2113435 3170789 := bbase (se 4 (by rfl) ⟨297261, by rfl⟩ : syracuseStep 3170789 = 594523) (by norm_num)
theorem B2113859 : Blo 2113435 2113859 := bstep (se 1 (by rfl) ⟨1585394, by rfl⟩ : syracuseStep 2113859 = 3170789) B3170789
theorem B5148301 : Blo 2113435 5148301 := bbase (se 3 (by rfl) ⟨965306, by rfl⟩ : syracuseStep 5148301 = 1930613) (by norm_num)
theorem B6864401 : Blo 2113435 6864401 := bstep (se 2 (by rfl) ⟨2574150, by rfl⟩ : syracuseStep 6864401 = 5148301) B5148301
theorem B4576267 : Blo 2113435 4576267 := bstep (se 1 (by rfl) ⟨3432200, by rfl⟩ : syracuseStep 4576267 = 6864401) B6864401
theorem B6101689 : Blo 2113435 6101689 := bstep (se 2 (by rfl) ⟨2288133, by rfl⟩ : syracuseStep 6101689 = 4576267) B4576267
theorem B8135585 : Blo 2113435 8135585 := bstep (se 2 (by rfl) ⟨3050844, by rfl⟩ : syracuseStep 8135585 = 6101689) B6101689
theorem B5423723 : Blo 2113435 5423723 := bstep (se 1 (by rfl) ⟨4067792, by rfl⟩ : syracuseStep 5423723 = 8135585) B8135585
theorem B3615815 : Blo 2113435 3615815 := bstep (se 1 (by rfl) ⟨2711861, by rfl⟩ : syracuseStep 3615815 = 5423723) B5423723
theorem B2410543 : Blo 2113435 2410543 := bstep (se 1 (by rfl) ⟨1807907, by rfl⟩ : syracuseStep 2410543 = 3615815) B3615815
theorem B12856229 : Blo 2113435 12856229 := bstep (se 4 (by rfl) ⟨1205271, by rfl⟩ : syracuseStep 12856229 = 2410543) B2410543
theorem B8570819 : Blo 2113435 8570819 := bstep (se 1 (by rfl) ⟨6428114, by rfl⟩ : syracuseStep 8570819 = 12856229) B12856229
theorem B22855517 : Blo 2113435 22855517 := bstep (se 3 (by rfl) ⟨4285409, by rfl⟩ : syracuseStep 22855517 = 8570819) B8570819
theorem B15237011 : Blo 2113435 15237011 := bstep (se 1 (by rfl) ⟨11427758, by rfl⟩ : syracuseStep 15237011 = 22855517) B22855517
theorem B10158007 : Blo 2113435 10158007 := bstep (se 1 (by rfl) ⟨7618505, by rfl⟩ : syracuseStep 10158007 = 15237011) B15237011
theorem B13544009 : Blo 2113435 13544009 := bstep (se 2 (by rfl) ⟨5079003, by rfl⟩ : syracuseStep 13544009 = 10158007) B10158007
theorem B9029339 : Blo 2113435 9029339 := bstep (se 1 (by rfl) ⟨6772004, by rfl⟩ : syracuseStep 9029339 = 13544009) B13544009
theorem B6019559 : Blo 2113435 6019559 := bstep (se 1 (by rfl) ⟨4514669, by rfl⟩ : syracuseStep 6019559 = 9029339) B9029339
theorem B4013039 : Blo 2113435 4013039 := bstep (se 1 (by rfl) ⟨3009779, by rfl⟩ : syracuseStep 4013039 = 6019559) B6019559
theorem B2675359 : Blo 2113435 2675359 := bstep (se 1 (by rfl) ⟨2006519, by rfl⟩ : syracuseStep 2675359 = 4013039) B4013039
theorem B3567145 : Blo 2113435 3567145 := bstep (se 2 (by rfl) ⟨1337679, by rfl⟩ : syracuseStep 3567145 = 2675359) B2675359
theorem B4756193 : Blo 2113435 4756193 := bstep (se 2 (by rfl) ⟨1783572, by rfl⟩ : syracuseStep 4756193 = 3567145) B3567145
theorem B3170795 : Blo 2113435 3170795 := bstep (se 1 (by rfl) ⟨2378096, by rfl⟩ : syracuseStep 3170795 = 4756193) B4756193
theorem B2113863 : Blo 2113435 2113863 := bstep (se 1 (by rfl) ⟨1585397, by rfl⟩ : syracuseStep 2113863 = 3170795) B3170795
theorem B2378101 : Blo 2113435 2378101 := bbase (se 5 (by rfl) ⟨111473, by rfl⟩ : syracuseStep 2378101 = 222947) (by norm_num)
theorem B3170801 : Blo 2113435 3170801 := bstep (se 2 (by rfl) ⟨1189050, by rfl⟩ : syracuseStep 3170801 = 2378101) B2378101
theorem B2113867 : Blo 2113435 2113867 := bstep (se 1 (by rfl) ⟨1585400, by rfl⟩ : syracuseStep 2113867 = 3170801) B3170801
theorem B2675369 : Blo 2113435 2675369 := bbase (se 2 (by rfl) ⟨1003263, by rfl⟩ : syracuseStep 2675369 = 2006527) (by norm_num)
theorem B7134317 : Blo 2113435 7134317 := bstep (se 3 (by rfl) ⟨1337684, by rfl⟩ : syracuseStep 7134317 = 2675369) B2675369
theorem B4756211 : Blo 2113435 4756211 := bstep (se 1 (by rfl) ⟨3567158, by rfl⟩ : syracuseStep 4756211 = 7134317) B7134317
theorem B3170807 : Blo 2113435 3170807 := bstep (se 1 (by rfl) ⟨2378105, by rfl⟩ : syracuseStep 3170807 = 4756211) B4756211
theorem B2113871 : Blo 2113435 2113871 := bstep (se 1 (by rfl) ⟨1585403, by rfl⟩ : syracuseStep 2113871 = 3170807) B3170807
theorem B3170813 : Blo 2113435 3170813 := bbase (se 3 (by rfl) ⟨594527, by rfl⟩ : syracuseStep 3170813 = 1189055) (by norm_num)
theorem B2113875 : Blo 2113435 2113875 := bstep (se 1 (by rfl) ⟨1585406, by rfl⟩ : syracuseStep 2113875 = 3170813) B3170813
theorem B4756229 : Blo 2113435 4756229 := bbase (se 4 (by rfl) ⟨445896, by rfl⟩ : syracuseStep 4756229 = 891793) (by norm_num)
theorem B3170819 : Blo 2113435 3170819 := bstep (se 1 (by rfl) ⟨2378114, by rfl⟩ : syracuseStep 3170819 = 4756229) B4756229
theorem B2113879 : Blo 2113435 2113879 := bstep (se 1 (by rfl) ⟨1585409, by rfl⟩ : syracuseStep 2113879 = 3170819) B3170819
theorem B4013077 : Blo 2113435 4013077 := bbase (se 6 (by rfl) ⟨94056, by rfl⟩ : syracuseStep 4013077 = 188113) (by norm_num)
theorem B5350769 : Blo 2113435 5350769 := bstep (se 2 (by rfl) ⟨2006538, by rfl⟩ : syracuseStep 5350769 = 4013077) B4013077
theorem B3567179 : Blo 2113435 3567179 := bstep (se 1 (by rfl) ⟨2675384, by rfl⟩ : syracuseStep 3567179 = 5350769) B5350769
theorem B2378119 : Blo 2113435 2378119 := bstep (se 1 (by rfl) ⟨1783589, by rfl⟩ : syracuseStep 2378119 = 3567179) B3567179
theorem B3170825 : Blo 2113435 3170825 := bstep (se 2 (by rfl) ⟨1189059, by rfl⟩ : syracuseStep 3170825 = 2378119) B2378119
theorem B2113883 : Blo 2113435 2113883 := bstep (se 1 (by rfl) ⟨1585412, by rfl⟩ : syracuseStep 2113883 = 3170825) B3170825
theorem B10701557 : Blo 2113435 10701557 := bbase (se 5 (by rfl) ⟨501635, by rfl⟩ : syracuseStep 10701557 = 1003271) (by norm_num)
theorem B7134371 : Blo 2113435 7134371 := bstep (se 1 (by rfl) ⟨5350778, by rfl⟩ : syracuseStep 7134371 = 10701557) B10701557
theorem B4756247 : Blo 2113435 4756247 := bstep (se 1 (by rfl) ⟨3567185, by rfl⟩ : syracuseStep 4756247 = 7134371) B7134371
theorem B3170831 : Blo 2113435 3170831 := bstep (se 1 (by rfl) ⟨2378123, by rfl⟩ : syracuseStep 3170831 = 4756247) B4756247
theorem B2113887 : Blo 2113435 2113887 := bstep (se 1 (by rfl) ⟨1585415, by rfl⟩ : syracuseStep 2113887 = 3170831) B3170831
theorem B3170837 : Blo 2113435 3170837 := bbase (se 6 (by rfl) ⟨74316, by rfl⟩ : syracuseStep 3170837 = 148633) (by norm_num)
theorem B2113891 : Blo 2113435 2113891 := bstep (se 1 (by rfl) ⟨1585418, by rfl⟩ : syracuseStep 2113891 = 3170837) B3170837
theorem B3386053 : Blo 2113435 3386053 := bbase (se 4 (by rfl) ⟨317442, by rfl⟩ : syracuseStep 3386053 = 634885) (by norm_num)
theorem B18058949 : Blo 2113435 18058949 := bstep (se 4 (by rfl) ⟨1693026, by rfl⟩ : syracuseStep 18058949 = 3386053) B3386053
theorem B12039299 : Blo 2113435 12039299 := bstep (se 1 (by rfl) ⟨9029474, by rfl⟩ : syracuseStep 12039299 = 18058949) B18058949
theorem B8026199 : Blo 2113435 8026199 := bstep (se 1 (by rfl) ⟨6019649, by rfl⟩ : syracuseStep 8026199 = 12039299) B12039299
theorem B5350799 : Blo 2113435 5350799 := bstep (se 1 (by rfl) ⟨4013099, by rfl⟩ : syracuseStep 5350799 = 8026199) B8026199
theorem B3567199 : Blo 2113435 3567199 := bstep (se 1 (by rfl) ⟨2675399, by rfl⟩ : syracuseStep 3567199 = 5350799) B5350799
theorem B4756265 : Blo 2113435 4756265 := bstep (se 2 (by rfl) ⟨1783599, by rfl⟩ : syracuseStep 4756265 = 3567199) B3567199
theorem B3170843 : Blo 2113435 3170843 := bstep (se 1 (by rfl) ⟨2378132, by rfl⟩ : syracuseStep 3170843 = 4756265) B4756265
theorem B2113895 : Blo 2113435 2113895 := bstep (se 1 (by rfl) ⟨1585421, by rfl⟩ : syracuseStep 2113895 = 3170843) B3170843
theorem B2378137 : Blo 2113435 2378137 := bbase (se 2 (by rfl) ⟨891801, by rfl⟩ : syracuseStep 2378137 = 1783603) (by norm_num)
theorem B3170849 : Blo 2113435 3170849 := bstep (se 2 (by rfl) ⟨1189068, by rfl⟩ : syracuseStep 3170849 = 2378137) B2378137
theorem B2113899 : Blo 2113435 2113899 := bstep (se 1 (by rfl) ⟨1585424, by rfl⟩ : syracuseStep 2113899 = 3170849) B3170849
theorem B8026229 : Blo 2113435 8026229 := bbase (se 5 (by rfl) ⟨376229, by rfl⟩ : syracuseStep 8026229 = 752459) (by norm_num)
theorem B5350819 : Blo 2113435 5350819 := bstep (se 1 (by rfl) ⟨4013114, by rfl⟩ : syracuseStep 5350819 = 8026229) B8026229
theorem B7134425 : Blo 2113435 7134425 := bstep (se 2 (by rfl) ⟨2675409, by rfl⟩ : syracuseStep 7134425 = 5350819) B5350819
theorem B4756283 : Blo 2113435 4756283 := bstep (se 1 (by rfl) ⟨3567212, by rfl⟩ : syracuseStep 4756283 = 7134425) B7134425
theorem B3170855 : Blo 2113435 3170855 := bstep (se 1 (by rfl) ⟨2378141, by rfl⟩ : syracuseStep 3170855 = 4756283) B4756283
theorem B2113903 : Blo 2113435 2113903 := bstep (se 1 (by rfl) ⟨1585427, by rfl⟩ : syracuseStep 2113903 = 3170855) B3170855
theorem B3170861 : Blo 2113435 3170861 := bbase (se 3 (by rfl) ⟨594536, by rfl⟩ : syracuseStep 3170861 = 1189073) (by norm_num)
theorem B2113907 : Blo 2113435 2113907 := bstep (se 1 (by rfl) ⟨1585430, by rfl⟩ : syracuseStep 2113907 = 3170861) B3170861
theorem B4756301 : Blo 2113435 4756301 := bbase (se 3 (by rfl) ⟨891806, by rfl⟩ : syracuseStep 4756301 = 1783613) (by norm_num)
theorem B3170867 : Blo 2113435 3170867 := bstep (se 1 (by rfl) ⟨2378150, by rfl⟩ : syracuseStep 3170867 = 4756301) B4756301
theorem B2113911 : Blo 2113435 2113911 := bstep (se 1 (by rfl) ⟨1585433, by rfl⟩ : syracuseStep 2113911 = 3170867) B3170867
theorem B2675425 : Blo 2113435 2675425 := bbase (se 2 (by rfl) ⟨1003284, by rfl⟩ : syracuseStep 2675425 = 2006569) (by norm_num)
theorem B3567233 : Blo 2113435 3567233 := bstep (se 2 (by rfl) ⟨1337712, by rfl⟩ : syracuseStep 3567233 = 2675425) B2675425
theorem B2378155 : Blo 2113435 2378155 := bstep (se 1 (by rfl) ⟨1783616, by rfl⟩ : syracuseStep 2378155 = 3567233) B3567233
theorem B3170873 : Blo 2113435 3170873 := bstep (se 2 (by rfl) ⟨1189077, by rfl⟩ : syracuseStep 3170873 = 2378155) B2378155
theorem B2113915 : Blo 2113435 2113915 := bstep (se 1 (by rfl) ⟨1585436, by rfl⟩ : syracuseStep 2113915 = 3170873) B3170873
theorem B24078869 : Blo 2113435 24078869 := bbase (se 6 (by rfl) ⟨564348, by rfl⟩ : syracuseStep 24078869 = 1128697) (by norm_num)
theorem B16052579 : Blo 2113435 16052579 := bstep (se 1 (by rfl) ⟨12039434, by rfl⟩ : syracuseStep 16052579 = 24078869) B24078869
theorem B10701719 : Blo 2113435 10701719 := bstep (se 1 (by rfl) ⟨8026289, by rfl⟩ : syracuseStep 10701719 = 16052579) B16052579
theorem B7134479 : Blo 2113435 7134479 := bstep (se 1 (by rfl) ⟨5350859, by rfl⟩ : syracuseStep 7134479 = 10701719) B10701719
theorem B4756319 : Blo 2113435 4756319 := bstep (se 1 (by rfl) ⟨3567239, by rfl⟩ : syracuseStep 4756319 = 7134479) B7134479
theorem B3170879 : Blo 2113435 3170879 := bstep (se 1 (by rfl) ⟨2378159, by rfl⟩ : syracuseStep 3170879 = 4756319) B4756319
theorem B2113919 : Blo 2113435 2113919 := bstep (se 1 (by rfl) ⟨1585439, by rfl⟩ : syracuseStep 2113919 = 3170879) B3170879
theorem B3170885 : Blo 2113435 3170885 := bbase (se 4 (by rfl) ⟨297270, by rfl⟩ : syracuseStep 3170885 = 594541) (by norm_num)
theorem B2113923 : Blo 2113435 2113923 := bstep (se 1 (by rfl) ⟨1585442, by rfl⟩ : syracuseStep 2113923 = 3170885) B3170885
theorem B3567253 : Blo 2113435 3567253 := bbase (se 6 (by rfl) ⟨83607, by rfl⟩ : syracuseStep 3567253 = 167215) (by norm_num)
theorem B4756337 : Blo 2113435 4756337 := bstep (se 2 (by rfl) ⟨1783626, by rfl⟩ : syracuseStep 4756337 = 3567253) B3567253
theorem B3170891 : Blo 2113435 3170891 := bstep (se 1 (by rfl) ⟨2378168, by rfl⟩ : syracuseStep 3170891 = 4756337) B4756337
theorem B2113927 : Blo 2113435 2113927 := bstep (se 1 (by rfl) ⟨1585445, by rfl⟩ : syracuseStep 2113927 = 3170891) B3170891
theorem B2378173 : Blo 2113435 2378173 := bbase (se 3 (by rfl) ⟨445907, by rfl⟩ : syracuseStep 2378173 = 891815) (by norm_num)
theorem B3170897 : Blo 2113435 3170897 := bstep (se 2 (by rfl) ⟨1189086, by rfl⟩ : syracuseStep 3170897 = 2378173) B2378173
theorem B2113931 : Blo 2113435 2113931 := bstep (se 1 (by rfl) ⟨1585448, by rfl⟩ : syracuseStep 2113931 = 3170897) B3170897
theorem B7134533 : Blo 2113435 7134533 := bbase (se 4 (by rfl) ⟨668862, by rfl⟩ : syracuseStep 7134533 = 1337725) (by norm_num)
theorem B4756355 : Blo 2113435 4756355 := bstep (se 1 (by rfl) ⟨3567266, by rfl⟩ : syracuseStep 4756355 = 7134533) B7134533
theorem B3170903 : Blo 2113435 3170903 := bstep (se 1 (by rfl) ⟨2378177, by rfl⟩ : syracuseStep 3170903 = 4756355) B4756355
theorem B2113935 : Blo 2113435 2113935 := bstep (se 1 (by rfl) ⟨1585451, by rfl⟩ : syracuseStep 2113935 = 3170903) B3170903
theorem B3170909 : Blo 2113435 3170909 := bbase (se 3 (by rfl) ⟨594545, by rfl⟩ : syracuseStep 3170909 = 1189091) (by norm_num)
theorem B2113939 : Blo 2113435 2113939 := bstep (se 1 (by rfl) ⟨1585454, by rfl⟩ : syracuseStep 2113939 = 3170909) B3170909
theorem B4756373 : Blo 2113435 4756373 := bbase (se 6 (by rfl) ⟨111477, by rfl⟩ : syracuseStep 4756373 = 222955) (by norm_num)
theorem B3170915 : Blo 2113435 3170915 := bstep (se 1 (by rfl) ⟨2378186, by rfl⟩ : syracuseStep 3170915 = 4756373) B4756373
theorem B2113943 : Blo 2113435 2113943 := bstep (se 1 (by rfl) ⟨1585457, by rfl⟩ : syracuseStep 2113943 = 3170915) B3170915
theorem B3809405 : Blo 2113435 3809405 := bbase (se 3 (by rfl) ⟨714263, by rfl⟩ : syracuseStep 3809405 = 1428527) (by norm_num)
theorem B2539603 : Blo 2113435 2539603 := bstep (se 1 (by rfl) ⟨1904702, by rfl⟩ : syracuseStep 2539603 = 3809405) B3809405
theorem B3386137 : Blo 2113435 3386137 := bstep (se 2 (by rfl) ⟨1269801, by rfl⟩ : syracuseStep 3386137 = 2539603) B2539603
theorem B4514849 : Blo 2113435 4514849 := bstep (se 2 (by rfl) ⟨1693068, by rfl⟩ : syracuseStep 4514849 = 3386137) B3386137
theorem B3009899 : Blo 2113435 3009899 := bstep (se 1 (by rfl) ⟨2257424, by rfl⟩ : syracuseStep 3009899 = 4514849) B4514849
theorem B8026397 : Blo 2113435 8026397 := bstep (se 3 (by rfl) ⟨1504949, by rfl⟩ : syracuseStep 8026397 = 3009899) B3009899
theorem B5350931 : Blo 2113435 5350931 := bstep (se 1 (by rfl) ⟨4013198, by rfl⟩ : syracuseStep 5350931 = 8026397) B8026397
theorem B3567287 : Blo 2113435 3567287 := bstep (se 1 (by rfl) ⟨2675465, by rfl⟩ : syracuseStep 3567287 = 5350931) B5350931
theorem B2378191 : Blo 2113435 2378191 := bstep (se 1 (by rfl) ⟨1783643, by rfl⟩ : syracuseStep 2378191 = 3567287) B3567287
theorem B3170921 : Blo 2113435 3170921 := bstep (se 2 (by rfl) ⟨1189095, by rfl⟩ : syracuseStep 3170921 = 2378191) B2378191
theorem B2113947 : Blo 2113435 2113947 := bstep (se 1 (by rfl) ⟨1585460, by rfl⟩ : syracuseStep 2113947 = 3170921) B3170921
theorem B5714117 : Blo 2113435 5714117 := bbase (se 4 (by rfl) ⟨535698, by rfl⟩ : syracuseStep 5714117 = 1071397) (by norm_num)
theorem B3809411 : Blo 2113435 3809411 := bstep (se 1 (by rfl) ⟨2857058, by rfl⟩ : syracuseStep 3809411 = 5714117) B5714117
theorem B2539607 : Blo 2113435 2539607 := bstep (se 1 (by rfl) ⟨1904705, by rfl⟩ : syracuseStep 2539607 = 3809411) B3809411
theorem B6772285 : Blo 2113435 6772285 := bstep (se 3 (by rfl) ⟨1269803, by rfl⟩ : syracuseStep 6772285 = 2539607) B2539607
theorem B9029713 : Blo 2113435 9029713 := bstep (se 2 (by rfl) ⟨3386142, by rfl⟩ : syracuseStep 9029713 = 6772285) B6772285
theorem B12039617 : Blo 2113435 12039617 := bstep (se 2 (by rfl) ⟨4514856, by rfl⟩ : syracuseStep 12039617 = 9029713) B9029713
theorem B8026411 : Blo 2113435 8026411 := bstep (se 1 (by rfl) ⟨6019808, by rfl⟩ : syracuseStep 8026411 = 12039617) B12039617
theorem B10701881 : Blo 2113435 10701881 := bstep (se 2 (by rfl) ⟨4013205, by rfl⟩ : syracuseStep 10701881 = 8026411) B8026411
theorem B7134587 : Blo 2113435 7134587 := bstep (se 1 (by rfl) ⟨5350940, by rfl⟩ : syracuseStep 7134587 = 10701881) B10701881
theorem B4756391 : Blo 2113435 4756391 := bstep (se 1 (by rfl) ⟨3567293, by rfl⟩ : syracuseStep 4756391 = 7134587) B7134587
theorem B3170927 : Blo 2113435 3170927 := bstep (se 1 (by rfl) ⟨2378195, by rfl⟩ : syracuseStep 3170927 = 4756391) B4756391
theorem B2113951 : Blo 2113435 2113951 := bstep (se 1 (by rfl) ⟨1585463, by rfl⟩ : syracuseStep 2113951 = 3170927) B3170927
theorem B3170933 : Blo 2113435 3170933 := bbase (se 5 (by rfl) ⟨148637, by rfl⟩ : syracuseStep 3170933 = 297275) (by norm_num)
theorem B2113955 : Blo 2113435 2113955 := bstep (se 1 (by rfl) ⟨1585466, by rfl⟩ : syracuseStep 2113955 = 3170933) B3170933
theorem B4013221 : Blo 2113435 4013221 := bbase (se 4 (by rfl) ⟨376239, by rfl⟩ : syracuseStep 4013221 = 752479) (by norm_num)
theorem B5350961 : Blo 2113435 5350961 := bstep (se 2 (by rfl) ⟨2006610, by rfl⟩ : syracuseStep 5350961 = 4013221) B4013221
theorem B3567307 : Blo 2113435 3567307 := bstep (se 1 (by rfl) ⟨2675480, by rfl⟩ : syracuseStep 3567307 = 5350961) B5350961
theorem B4756409 : Blo 2113435 4756409 := bstep (se 2 (by rfl) ⟨1783653, by rfl⟩ : syracuseStep 4756409 = 3567307) B3567307
theorem B3170939 : Blo 2113435 3170939 := bstep (se 1 (by rfl) ⟨2378204, by rfl⟩ : syracuseStep 3170939 = 4756409) B4756409
theorem B2113959 : Blo 2113435 2113959 := bstep (se 1 (by rfl) ⟨1585469, by rfl⟩ : syracuseStep 2113959 = 3170939) B3170939
theorem B2378209 : Blo 2113435 2378209 := bbase (se 2 (by rfl) ⟨891828, by rfl⟩ : syracuseStep 2378209 = 1783657) (by norm_num)
theorem B3170945 : Blo 2113435 3170945 := bstep (se 2 (by rfl) ⟨1189104, by rfl⟩ : syracuseStep 3170945 = 2378209) B2378209
theorem B2113963 : Blo 2113435 2113963 := bstep (se 1 (by rfl) ⟨1585472, by rfl⟩ : syracuseStep 2113963 = 3170945) B3170945
theorem B5350981 : Blo 2113435 5350981 := bbase (se 4 (by rfl) ⟨501654, by rfl⟩ : syracuseStep 5350981 = 1003309) (by norm_num)
theorem B7134641 : Blo 2113435 7134641 := bstep (se 2 (by rfl) ⟨2675490, by rfl⟩ : syracuseStep 7134641 = 5350981) B5350981
theorem B4756427 : Blo 2113435 4756427 := bstep (se 1 (by rfl) ⟨3567320, by rfl⟩ : syracuseStep 4756427 = 7134641) B7134641
theorem B3170951 : Blo 2113435 3170951 := bstep (se 1 (by rfl) ⟨2378213, by rfl⟩ : syracuseStep 3170951 = 4756427) B4756427
theorem B2113967 : Blo 2113435 2113967 := bstep (se 1 (by rfl) ⟨1585475, by rfl⟩ : syracuseStep 2113967 = 3170951) B3170951
theorem B3170957 : Blo 2113435 3170957 := bbase (se 3 (by rfl) ⟨594554, by rfl⟩ : syracuseStep 3170957 = 1189109) (by norm_num)
theorem B2113971 : Blo 2113435 2113971 := bstep (se 1 (by rfl) ⟨1585478, by rfl⟩ : syracuseStep 2113971 = 3170957) B3170957
theorem B4756445 : Blo 2113435 4756445 := bbase (se 3 (by rfl) ⟨891833, by rfl⟩ : syracuseStep 4756445 = 1783667) (by norm_num)
theorem B3170963 : Blo 2113435 3170963 := bstep (se 1 (by rfl) ⟨2378222, by rfl⟩ : syracuseStep 3170963 = 4756445) B4756445
theorem B2113975 : Blo 2113435 2113975 := bstep (se 1 (by rfl) ⟨1585481, by rfl⟩ : syracuseStep 2113975 = 3170963) B3170963
theorem B3567341 : Blo 2113435 3567341 := bbase (se 3 (by rfl) ⟨668876, by rfl⟩ : syracuseStep 3567341 = 1337753) (by norm_num)
theorem B2378227 : Blo 2113435 2378227 := bstep (se 1 (by rfl) ⟨1783670, by rfl⟩ : syracuseStep 2378227 = 3567341) B3567341
theorem B3170969 : Blo 2113435 3170969 := bstep (se 2 (by rfl) ⟨1189113, by rfl⟩ : syracuseStep 3170969 = 2378227) B2378227
theorem B2113979 : Blo 2113435 2113979 := bstep (se 1 (by rfl) ⟨1585484, by rfl⟩ : syracuseStep 2113979 = 3170969) B3170969
theorem B10158581 : Blo 2113435 10158581 := bbase (se 5 (by rfl) ⟨476183, by rfl⟩ : syracuseStep 10158581 = 952367) (by norm_num)
theorem B27089549 : Blo 2113435 27089549 := bstep (se 3 (by rfl) ⟨5079290, by rfl⟩ : syracuseStep 27089549 = 10158581) B10158581
theorem B18059699 : Blo 2113435 18059699 := bstep (se 1 (by rfl) ⟨13544774, by rfl⟩ : syracuseStep 18059699 = 27089549) B27089549
theorem B12039799 : Blo 2113435 12039799 := bstep (se 1 (by rfl) ⟨9029849, by rfl⟩ : syracuseStep 12039799 = 18059699) B18059699
theorem B16053065 : Blo 2113435 16053065 := bstep (se 2 (by rfl) ⟨6019899, by rfl⟩ : syracuseStep 16053065 = 12039799) B12039799
theorem B10702043 : Blo 2113435 10702043 := bstep (se 1 (by rfl) ⟨8026532, by rfl⟩ : syracuseStep 10702043 = 16053065) B16053065
theorem B7134695 : Blo 2113435 7134695 := bstep (se 1 (by rfl) ⟨5351021, by rfl⟩ : syracuseStep 7134695 = 10702043) B10702043
theorem B4756463 : Blo 2113435 4756463 := bstep (se 1 (by rfl) ⟨3567347, by rfl⟩ : syracuseStep 4756463 = 7134695) B7134695
theorem B3170975 : Blo 2113435 3170975 := bstep (se 1 (by rfl) ⟨2378231, by rfl⟩ : syracuseStep 3170975 = 4756463) B4756463
theorem B2113983 : Blo 2113435 2113983 := bstep (se 1 (by rfl) ⟨1585487, by rfl⟩ : syracuseStep 2113983 = 3170975) B3170975
theorem B3170981 : Blo 2113435 3170981 := bbase (se 4 (by rfl) ⟨297279, by rfl⟩ : syracuseStep 3170981 = 594559) (by norm_num)
theorem B2113987 : Blo 2113435 2113987 := bstep (se 1 (by rfl) ⟨1585490, by rfl⟩ : syracuseStep 2113987 = 3170981) B3170981
theorem B2675521 : Blo 2113435 2675521 := bbase (se 2 (by rfl) ⟨1003320, by rfl⟩ : syracuseStep 2675521 = 2006641) (by norm_num)
theorem B3567361 : Blo 2113435 3567361 := bstep (se 2 (by rfl) ⟨1337760, by rfl⟩ : syracuseStep 3567361 = 2675521) B2675521
theorem B4756481 : Blo 2113435 4756481 := bstep (se 2 (by rfl) ⟨1783680, by rfl⟩ : syracuseStep 4756481 = 3567361) B3567361
theorem B3170987 : Blo 2113435 3170987 := bstep (se 1 (by rfl) ⟨2378240, by rfl⟩ : syracuseStep 3170987 = 4756481) B4756481
theorem B2113991 : Blo 2113435 2113991 := bstep (se 1 (by rfl) ⟨1585493, by rfl⟩ : syracuseStep 2113991 = 3170987) B3170987
theorem B2378245 : Blo 2113435 2378245 := bbase (se 4 (by rfl) ⟨222960, by rfl⟩ : syracuseStep 2378245 = 445921) (by norm_num)
theorem B3170993 : Blo 2113435 3170993 := bstep (se 2 (by rfl) ⟨1189122, by rfl⟩ : syracuseStep 3170993 = 2378245) B2378245
theorem B2113995 : Blo 2113435 2113995 := bstep (se 1 (by rfl) ⟨1585496, by rfl⟩ : syracuseStep 2113995 = 3170993) B3170993
theorem B3009973 : Blo 2113435 3009973 := bbase (se 5 (by rfl) ⟨141092, by rfl⟩ : syracuseStep 3009973 = 282185) (by norm_num)
theorem B4013297 : Blo 2113435 4013297 := bstep (se 2 (by rfl) ⟨1504986, by rfl⟩ : syracuseStep 4013297 = 3009973) B3009973
theorem B2675531 : Blo 2113435 2675531 := bstep (se 1 (by rfl) ⟨2006648, by rfl⟩ : syracuseStep 2675531 = 4013297) B4013297
theorem B7134749 : Blo 2113435 7134749 := bstep (se 3 (by rfl) ⟨1337765, by rfl⟩ : syracuseStep 7134749 = 2675531) B2675531
theorem B4756499 : Blo 2113435 4756499 := bstep (se 1 (by rfl) ⟨3567374, by rfl⟩ : syracuseStep 4756499 = 7134749) B7134749
theorem B3170999 : Blo 2113435 3170999 := bstep (se 1 (by rfl) ⟨2378249, by rfl⟩ : syracuseStep 3170999 = 4756499) B4756499
theorem B2113999 : Blo 2113435 2113999 := bstep (se 1 (by rfl) ⟨1585499, by rfl⟩ : syracuseStep 2113999 = 3170999) B3170999
theorem B3171005 : Blo 2113435 3171005 := bbase (se 3 (by rfl) ⟨594563, by rfl⟩ : syracuseStep 3171005 = 1189127) (by norm_num)
theorem B2114003 : Blo 2113435 2114003 := bstep (se 1 (by rfl) ⟨1585502, by rfl⟩ : syracuseStep 2114003 = 3171005) B3171005
theorem B4756517 : Blo 2113435 4756517 := bbase (se 4 (by rfl) ⟨445923, by rfl⟩ : syracuseStep 4756517 = 891847) (by norm_num)
theorem B3171011 : Blo 2113435 3171011 := bstep (se 1 (by rfl) ⟨2378258, by rfl⟩ : syracuseStep 3171011 = 4756517) B4756517
theorem B2114007 : Blo 2113435 2114007 := bstep (se 1 (by rfl) ⟨1585505, by rfl⟩ : syracuseStep 2114007 = 3171011) B3171011
theorem B5351093 : Blo 2113435 5351093 := bbase (se 5 (by rfl) ⟨250832, by rfl⟩ : syracuseStep 5351093 = 501665) (by norm_num)
theorem B3567395 : Blo 2113435 3567395 := bstep (se 1 (by rfl) ⟨2675546, by rfl⟩ : syracuseStep 3567395 = 5351093) B5351093
theorem B2378263 : Blo 2113435 2378263 := bstep (se 1 (by rfl) ⟨1783697, by rfl⟩ : syracuseStep 2378263 = 3567395) B3567395
theorem B3171017 : Blo 2113435 3171017 := bstep (se 2 (by rfl) ⟨1189131, by rfl⟩ : syracuseStep 3171017 = 2378263) B2378263
theorem B2114011 : Blo 2113435 2114011 := bstep (se 1 (by rfl) ⟨1585508, by rfl⟩ : syracuseStep 2114011 = 3171017) B3171017
theorem B13544981 : Blo 2113435 13544981 := bbase (se 6 (by rfl) ⟨317460, by rfl⟩ : syracuseStep 13544981 = 634921) (by norm_num)
theorem B9029987 : Blo 2113435 9029987 := bstep (se 1 (by rfl) ⟨6772490, by rfl⟩ : syracuseStep 9029987 = 13544981) B13544981
theorem B6019991 : Blo 2113435 6019991 := bstep (se 1 (by rfl) ⟨4514993, by rfl⟩ : syracuseStep 6019991 = 9029987) B9029987
theorem B4013327 : Blo 2113435 4013327 := bstep (se 1 (by rfl) ⟨3009995, by rfl⟩ : syracuseStep 4013327 = 6019991) B6019991
theorem B10702205 : Blo 2113435 10702205 := bstep (se 3 (by rfl) ⟨2006663, by rfl⟩ : syracuseStep 10702205 = 4013327) B4013327
theorem B7134803 : Blo 2113435 7134803 := bstep (se 1 (by rfl) ⟨5351102, by rfl⟩ : syracuseStep 7134803 = 10702205) B10702205
theorem B4756535 : Blo 2113435 4756535 := bstep (se 1 (by rfl) ⟨3567401, by rfl⟩ : syracuseStep 4756535 = 7134803) B7134803
theorem B3171023 : Blo 2113435 3171023 := bstep (se 1 (by rfl) ⟨2378267, by rfl⟩ : syracuseStep 3171023 = 4756535) B4756535
theorem B2114015 : Blo 2113435 2114015 := bstep (se 1 (by rfl) ⟨1585511, by rfl⟩ : syracuseStep 2114015 = 3171023) B3171023
theorem B3171029 : Blo 2113435 3171029 := bbase (se 7 (by rfl) ⟨37160, by rfl⟩ : syracuseStep 3171029 = 74321) (by norm_num)
theorem B2114019 : Blo 2113435 2114019 := bstep (se 1 (by rfl) ⟨1585514, by rfl⟩ : syracuseStep 2114019 = 3171029) B3171029
theorem B6772517 : Blo 2113435 6772517 := bbase (se 4 (by rfl) ⟨634923, by rfl⟩ : syracuseStep 6772517 = 1269847) (by norm_num)
theorem B4515011 : Blo 2113435 4515011 := bstep (se 1 (by rfl) ⟨3386258, by rfl⟩ : syracuseStep 4515011 = 6772517) B6772517
theorem B3010007 : Blo 2113435 3010007 := bstep (se 1 (by rfl) ⟨2257505, by rfl⟩ : syracuseStep 3010007 = 4515011) B4515011
theorem B8026685 : Blo 2113435 8026685 := bstep (se 3 (by rfl) ⟨1505003, by rfl⟩ : syracuseStep 8026685 = 3010007) B3010007
theorem B5351123 : Blo 2113435 5351123 := bstep (se 1 (by rfl) ⟨4013342, by rfl⟩ : syracuseStep 5351123 = 8026685) B8026685
theorem B3567415 : Blo 2113435 3567415 := bstep (se 1 (by rfl) ⟨2675561, by rfl⟩ : syracuseStep 3567415 = 5351123) B5351123
theorem B4756553 : Blo 2113435 4756553 := bstep (se 2 (by rfl) ⟨1783707, by rfl⟩ : syracuseStep 4756553 = 3567415) B3567415
theorem B3171035 : Blo 2113435 3171035 := bstep (se 1 (by rfl) ⟨2378276, by rfl⟩ : syracuseStep 3171035 = 4756553) B4756553
theorem B2114023 : Blo 2113435 2114023 := bstep (se 1 (by rfl) ⟨1585517, by rfl⟩ : syracuseStep 2114023 = 3171035) B3171035
theorem B2378281 : Blo 2113435 2378281 := bbase (se 2 (by rfl) ⟨891855, by rfl⟩ : syracuseStep 2378281 = 1783711) (by norm_num)
theorem B3171041 : Blo 2113435 3171041 := bstep (se 2 (by rfl) ⟨1189140, by rfl⟩ : syracuseStep 3171041 = 2378281) B2378281
theorem B2114027 : Blo 2113435 2114027 := bstep (se 1 (by rfl) ⟨1585520, by rfl⟩ : syracuseStep 2114027 = 3171041) B3171041
theorem B17142997 : Blo 2113435 17142997 := bbase (se 7 (by rfl) ⟨200894, by rfl⟩ : syracuseStep 17142997 = 401789) (by norm_num)
theorem B22857329 : Blo 2113435 22857329 := bstep (se 2 (by rfl) ⟨8571498, by rfl⟩ : syracuseStep 22857329 = 17142997) B17142997
theorem B15238219 : Blo 2113435 15238219 := bstep (se 1 (by rfl) ⟨11428664, by rfl⟩ : syracuseStep 15238219 = 22857329) B22857329
theorem B20317625 : Blo 2113435 20317625 := bstep (se 2 (by rfl) ⟨7619109, by rfl⟩ : syracuseStep 20317625 = 15238219) B15238219
theorem B13545083 : Blo 2113435 13545083 := bstep (se 1 (by rfl) ⟨10158812, by rfl⟩ : syracuseStep 13545083 = 20317625) B20317625
theorem B9030055 : Blo 2113435 9030055 := bstep (se 1 (by rfl) ⟨6772541, by rfl⟩ : syracuseStep 9030055 = 13545083) B13545083
theorem B12040073 : Blo 2113435 12040073 := bstep (se 2 (by rfl) ⟨4515027, by rfl⟩ : syracuseStep 12040073 = 9030055) B9030055
theorem B8026715 : Blo 2113435 8026715 := bstep (se 1 (by rfl) ⟨6020036, by rfl⟩ : syracuseStep 8026715 = 12040073) B12040073
theorem B5351143 : Blo 2113435 5351143 := bstep (se 1 (by rfl) ⟨4013357, by rfl⟩ : syracuseStep 5351143 = 8026715) B8026715
theorem B7134857 : Blo 2113435 7134857 := bstep (se 2 (by rfl) ⟨2675571, by rfl⟩ : syracuseStep 7134857 = 5351143) B5351143
theorem B4756571 : Blo 2113435 4756571 := bstep (se 1 (by rfl) ⟨3567428, by rfl⟩ : syracuseStep 4756571 = 7134857) B7134857
theorem B3171047 : Blo 2113435 3171047 := bstep (se 1 (by rfl) ⟨2378285, by rfl⟩ : syracuseStep 3171047 = 4756571) B4756571
theorem B2114031 : Blo 2113435 2114031 := bstep (se 1 (by rfl) ⟨1585523, by rfl⟩ : syracuseStep 2114031 = 3171047) B3171047
theorem B3171053 : Blo 2113435 3171053 := bbase (se 3 (by rfl) ⟨594572, by rfl⟩ : syracuseStep 3171053 = 1189145) (by norm_num)
theorem B2114035 : Blo 2113435 2114035 := bstep (se 1 (by rfl) ⟨1585526, by rfl⟩ : syracuseStep 2114035 = 3171053) B3171053
theorem B4756589 : Blo 2113435 4756589 := bbase (se 3 (by rfl) ⟨891860, by rfl⟩ : syracuseStep 4756589 = 1783721) (by norm_num)
theorem B3171059 : Blo 2113435 3171059 := bstep (se 1 (by rfl) ⟨2378294, by rfl⟩ : syracuseStep 3171059 = 4756589) B4756589
theorem B2114039 : Blo 2113435 2114039 := bstep (se 1 (by rfl) ⟨1585529, by rfl⟩ : syracuseStep 2114039 = 3171059) B3171059
theorem B4013381 : Blo 2113435 4013381 := bbase (se 4 (by rfl) ⟨376254, by rfl⟩ : syracuseStep 4013381 = 752509) (by norm_num)
theorem B2675587 : Blo 2113435 2675587 := bstep (se 1 (by rfl) ⟨2006690, by rfl⟩ : syracuseStep 2675587 = 4013381) B4013381
theorem B3567449 : Blo 2113435 3567449 := bstep (se 2 (by rfl) ⟨1337793, by rfl⟩ : syracuseStep 3567449 = 2675587) B2675587
theorem B2378299 : Blo 2113435 2378299 := bstep (se 1 (by rfl) ⟨1783724, by rfl⟩ : syracuseStep 2378299 = 3567449) B3567449
theorem B3171065 : Blo 2113435 3171065 := bstep (se 2 (by rfl) ⟨1189149, by rfl⟩ : syracuseStep 3171065 = 2378299) B2378299
theorem B2114043 : Blo 2113435 2114043 := bstep (se 1 (by rfl) ⟨1585532, by rfl⟩ : syracuseStep 2114043 = 3171065) B3171065
theorem B4953965 : Blo 2113435 4953965 := bbase (se 3 (by rfl) ⟨928868, by rfl⟩ : syracuseStep 4953965 = 1857737) (by norm_num)
theorem B13210573 : Blo 2113435 13210573 := bstep (se 3 (by rfl) ⟨2476982, by rfl⟩ : syracuseStep 13210573 = 4953965) B4953965
theorem B17614097 : Blo 2113435 17614097 := bstep (se 2 (by rfl) ⟨6605286, by rfl⟩ : syracuseStep 17614097 = 13210573) B13210573
theorem B11742731 : Blo 2113435 11742731 := bstep (se 1 (by rfl) ⟨8807048, by rfl⟩ : syracuseStep 11742731 = 17614097) B17614097
theorem B7828487 : Blo 2113435 7828487 := bstep (se 1 (by rfl) ⟨5871365, by rfl⟩ : syracuseStep 7828487 = 11742731) B11742731
theorem B5218991 : Blo 2113435 5218991 := bstep (se 1 (by rfl) ⟨3914243, by rfl⟩ : syracuseStep 5218991 = 7828487) B7828487
theorem B3479327 : Blo 2113435 3479327 := bstep (se 1 (by rfl) ⟨2609495, by rfl⟩ : syracuseStep 3479327 = 5218991) B5218991
theorem B37112821 : Blo 2113435 37112821 := bstep (se 5 (by rfl) ⟨1739663, by rfl⟩ : syracuseStep 37112821 = 3479327) B3479327
theorem B197935045 : Blo 2113435 197935045 := bstep (se 4 (by rfl) ⟨18556410, by rfl⟩ : syracuseStep 197935045 = 37112821) B37112821
theorem B1055653573 : Blo 2113435 1055653573 := bstep (se 4 (by rfl) ⟨98967522, by rfl⟩ : syracuseStep 1055653573 = 197935045) B197935045
theorem B1407538097 : Blo 2113435 1407538097 := bstep (se 2 (by rfl) ⟨527826786, by rfl⟩ : syracuseStep 1407538097 = 1055653573) B1055653573
theorem B938358731 : Blo 2113435 938358731 := bstep (se 1 (by rfl) ⟨703769048, by rfl⟩ : syracuseStep 938358731 = 1407538097) B1407538097
theorem B625572487 : Blo 2113435 625572487 := bstep (se 1 (by rfl) ⟨469179365, by rfl⟩ : syracuseStep 625572487 = 938358731) B938358731
theorem B3336386597 : Blo 2113435 3336386597 := bstep (se 4 (by rfl) ⟨312786243, by rfl⟩ : syracuseStep 3336386597 = 625572487) B625572487
theorem B2224257731 : Blo 2113435 2224257731 := bstep (se 1 (by rfl) ⟨1668193298, by rfl⟩ : syracuseStep 2224257731 = 3336386597) B3336386597
theorem B1482838487 : Blo 2113435 1482838487 := bstep (se 1 (by rfl) ⟨1112128865, by rfl⟩ : syracuseStep 1482838487 = 2224257731) B2224257731
theorem B988558991 : Blo 2113435 988558991 := bstep (se 1 (by rfl) ⟨741419243, by rfl⟩ : syracuseStep 988558991 = 1482838487) B1482838487
theorem B659039327 : Blo 2113435 659039327 := bstep (se 1 (by rfl) ⟨494279495, by rfl⟩ : syracuseStep 659039327 = 988558991) B988558991
theorem B439359551 : Blo 2113435 439359551 := bstep (se 1 (by rfl) ⟨329519663, by rfl⟩ : syracuseStep 439359551 = 659039327) B659039327
theorem B292906367 : Blo 2113435 292906367 := bstep (se 1 (by rfl) ⟨219679775, by rfl⟩ : syracuseStep 292906367 = 439359551) B439359551
theorem B195270911 : Blo 2113435 195270911 := bstep (se 1 (by rfl) ⟨146453183, by rfl⟩ : syracuseStep 195270911 = 292906367) B292906367
theorem B130180607 : Blo 2113435 130180607 := bstep (se 1 (by rfl) ⟨97635455, by rfl⟩ : syracuseStep 130180607 = 195270911) B195270911
theorem B86787071 : Blo 2113435 86787071 := bstep (se 1 (by rfl) ⟨65090303, by rfl⟩ : syracuseStep 86787071 = 130180607) B130180607
theorem B57858047 : Blo 2113435 57858047 := bstep (se 1 (by rfl) ⟨43393535, by rfl⟩ : syracuseStep 57858047 = 86787071) B86787071
theorem B38572031 : Blo 2113435 38572031 := bstep (se 1 (by rfl) ⟨28929023, by rfl⟩ : syracuseStep 38572031 = 57858047) B57858047
theorem B25714687 : Blo 2113435 25714687 := bstep (se 1 (by rfl) ⟨19286015, by rfl⟩ : syracuseStep 25714687 = 38572031) B38572031
theorem B34286249 : Blo 2113435 34286249 := bstep (se 2 (by rfl) ⟨12857343, by rfl⟩ : syracuseStep 34286249 = 25714687) B25714687
theorem B22857499 : Blo 2113435 22857499 := bstep (se 1 (by rfl) ⟨17143124, by rfl⟩ : syracuseStep 22857499 = 34286249) B34286249
theorem B30476665 : Blo 2113435 30476665 := bstep (se 2 (by rfl) ⟨11428749, by rfl⟩ : syracuseStep 30476665 = 22857499) B22857499
theorem B40635553 : Blo 2113435 40635553 := bstep (se 2 (by rfl) ⟨15238332, by rfl⟩ : syracuseStep 40635553 = 30476665) B30476665
theorem B54180737 : Blo 2113435 54180737 := bstep (se 2 (by rfl) ⟨20317776, by rfl⟩ : syracuseStep 54180737 = 40635553) B40635553
theorem B36120491 : Blo 2113435 36120491 := bstep (se 1 (by rfl) ⟨27090368, by rfl⟩ : syracuseStep 36120491 = 54180737) B54180737
theorem B24080327 : Blo 2113435 24080327 := bstep (se 1 (by rfl) ⟨18060245, by rfl⟩ : syracuseStep 24080327 = 36120491) B36120491
theorem B16053551 : Blo 2113435 16053551 := bstep (se 1 (by rfl) ⟨12040163, by rfl⟩ : syracuseStep 16053551 = 24080327) B24080327
theorem B10702367 : Blo 2113435 10702367 := bstep (se 1 (by rfl) ⟨8026775, by rfl⟩ : syracuseStep 10702367 = 16053551) B16053551
theorem B7134911 : Blo 2113435 7134911 := bstep (se 1 (by rfl) ⟨5351183, by rfl⟩ : syracuseStep 7134911 = 10702367) B10702367
theorem B4756607 : Blo 2113435 4756607 := bstep (se 1 (by rfl) ⟨3567455, by rfl⟩ : syracuseStep 4756607 = 7134911) B7134911
theorem B3171071 : Blo 2113435 3171071 := bstep (se 1 (by rfl) ⟨2378303, by rfl⟩ : syracuseStep 3171071 = 4756607) B4756607
theorem B2114047 : Blo 2113435 2114047 := bstep (se 1 (by rfl) ⟨1585535, by rfl⟩ : syracuseStep 2114047 = 3171071) B3171071
theorem B3171077 : Blo 2113435 3171077 := bbase (se 4 (by rfl) ⟨297288, by rfl⟩ : syracuseStep 3171077 = 594577) (by norm_num)
theorem B2114051 : Blo 2113435 2114051 := bstep (se 1 (by rfl) ⟨1585538, by rfl⟩ : syracuseStep 2114051 = 3171077) B3171077
theorem B3567469 : Blo 2113435 3567469 := bbase (se 3 (by rfl) ⟨668900, by rfl⟩ : syracuseStep 3567469 = 1337801) (by norm_num)
theorem B4756625 : Blo 2113435 4756625 := bstep (se 2 (by rfl) ⟨1783734, by rfl⟩ : syracuseStep 4756625 = 3567469) B3567469
theorem B3171083 : Blo 2113435 3171083 := bstep (se 1 (by rfl) ⟨2378312, by rfl⟩ : syracuseStep 3171083 = 4756625) B4756625
theorem B2114055 : Blo 2113435 2114055 := bstep (se 1 (by rfl) ⟨1585541, by rfl⟩ : syracuseStep 2114055 = 3171083) B3171083
theorem B2378317 : Blo 2113435 2378317 := bbase (se 3 (by rfl) ⟨445934, by rfl⟩ : syracuseStep 2378317 = 891869) (by norm_num)
theorem B3171089 : Blo 2113435 3171089 := bstep (se 2 (by rfl) ⟨1189158, by rfl⟩ : syracuseStep 3171089 = 2378317) B2378317
theorem B2114059 : Blo 2113435 2114059 := bstep (se 1 (by rfl) ⟨1585544, by rfl⟩ : syracuseStep 2114059 = 3171089) B3171089
theorem B7134965 : Blo 2113435 7134965 := bbase (se 5 (by rfl) ⟨334451, by rfl⟩ : syracuseStep 7134965 = 668903) (by norm_num)
theorem B4756643 : Blo 2113435 4756643 := bstep (se 1 (by rfl) ⟨3567482, by rfl⟩ : syracuseStep 4756643 = 7134965) B7134965
theorem B3171095 : Blo 2113435 3171095 := bstep (se 1 (by rfl) ⟨2378321, by rfl⟩ : syracuseStep 3171095 = 4756643) B4756643
theorem B2114063 : Blo 2113435 2114063 := bstep (se 1 (by rfl) ⟨1585547, by rfl⟩ : syracuseStep 2114063 = 3171095) B3171095
theorem B3171101 : Blo 2113435 3171101 := bbase (se 3 (by rfl) ⟨594581, by rfl⟩ : syracuseStep 3171101 = 1189163) (by norm_num)
theorem B2114067 : Blo 2113435 2114067 := bstep (se 1 (by rfl) ⟨1585550, by rfl⟩ : syracuseStep 2114067 = 3171101) B3171101
theorem B4756661 : Blo 2113435 4756661 := bbase (se 5 (by rfl) ⟨222968, by rfl⟩ : syracuseStep 4756661 = 445937) (by norm_num)
theorem B3171107 : Blo 2113435 3171107 := bstep (se 1 (by rfl) ⟨2378330, by rfl⟩ : syracuseStep 3171107 = 4756661) B4756661
theorem B2114071 : Blo 2113435 2114071 := bstep (se 1 (by rfl) ⟨1585553, by rfl⟩ : syracuseStep 2114071 = 3171107) B3171107
theorem B2257561 : Blo 2113435 2257561 := bbase (se 2 (by rfl) ⟨846585, by rfl⟩ : syracuseStep 2257561 = 1693171) (by norm_num)
theorem B12040325 : Blo 2113435 12040325 := bstep (se 4 (by rfl) ⟨1128780, by rfl⟩ : syracuseStep 12040325 = 2257561) B2257561
theorem B8026883 : Blo 2113435 8026883 := bstep (se 1 (by rfl) ⟨6020162, by rfl⟩ : syracuseStep 8026883 = 12040325) B12040325
theorem B5351255 : Blo 2113435 5351255 := bstep (se 1 (by rfl) ⟨4013441, by rfl⟩ : syracuseStep 5351255 = 8026883) B8026883
theorem B3567503 : Blo 2113435 3567503 := bstep (se 1 (by rfl) ⟨2675627, by rfl⟩ : syracuseStep 3567503 = 5351255) B5351255
theorem B2378335 : Blo 2113435 2378335 := bstep (se 1 (by rfl) ⟨1783751, by rfl⟩ : syracuseStep 2378335 = 3567503) B3567503
theorem B3171113 : Blo 2113435 3171113 := bstep (se 2 (by rfl) ⟨1189167, by rfl⟩ : syracuseStep 3171113 = 2378335) B2378335
theorem B2114075 : Blo 2113435 2114075 := bstep (se 1 (by rfl) ⟨1585556, by rfl⟩ : syracuseStep 2114075 = 3171113) B3171113
theorem B2257565 : Blo 2113435 2257565 := bbase (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) (by norm_num)
theorem B6020173 : Blo 2113435 6020173 := bstep (se 3 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 6020173 = 2257565) B2257565
theorem B8026897 : Blo 2113435 8026897 := bstep (se 2 (by rfl) ⟨3010086, by rfl⟩ : syracuseStep 8026897 = 6020173) B6020173
theorem B10702529 : Blo 2113435 10702529 := bstep (se 2 (by rfl) ⟨4013448, by rfl⟩ : syracuseStep 10702529 = 8026897) B8026897
theorem B7135019 : Blo 2113435 7135019 := bstep (se 1 (by rfl) ⟨5351264, by rfl⟩ : syracuseStep 7135019 = 10702529) B10702529
theorem B4756679 : Blo 2113435 4756679 := bstep (se 1 (by rfl) ⟨3567509, by rfl⟩ : syracuseStep 4756679 = 7135019) B7135019
theorem B3171119 : Blo 2113435 3171119 := bstep (se 1 (by rfl) ⟨2378339, by rfl⟩ : syracuseStep 3171119 = 4756679) B4756679
theorem B2114079 : Blo 2113435 2114079 := bstep (se 1 (by rfl) ⟨1585559, by rfl⟩ : syracuseStep 2114079 = 3171119) B3171119
theorem B3171125 : Blo 2113435 3171125 := bbase (se 5 (by rfl) ⟨148646, by rfl⟩ : syracuseStep 3171125 = 297293) (by norm_num)
theorem B2114083 : Blo 2113435 2114083 := bstep (se 1 (by rfl) ⟨1585562, by rfl⟩ : syracuseStep 2114083 = 3171125) B3171125
theorem B5351285 : Blo 2113435 5351285 := bbase (se 5 (by rfl) ⟨250841, by rfl⟩ : syracuseStep 5351285 = 501683) (by norm_num)
theorem B3567523 : Blo 2113435 3567523 := bstep (se 1 (by rfl) ⟨2675642, by rfl⟩ : syracuseStep 3567523 = 5351285) B5351285
theorem B4756697 : Blo 2113435 4756697 := bstep (se 2 (by rfl) ⟨1783761, by rfl⟩ : syracuseStep 4756697 = 3567523) B3567523
theorem B3171131 : Blo 2113435 3171131 := bstep (se 1 (by rfl) ⟨2378348, by rfl⟩ : syracuseStep 3171131 = 4756697) B4756697
theorem B2114087 : Blo 2113435 2114087 := bstep (se 1 (by rfl) ⟨1585565, by rfl⟩ : syracuseStep 2114087 = 3171131) B3171131
theorem B2378353 : Blo 2113435 2378353 := bbase (se 2 (by rfl) ⟨891882, by rfl⟩ : syracuseStep 2378353 = 1783765) (by norm_num)
theorem B3171137 : Blo 2113435 3171137 := bstep (se 2 (by rfl) ⟨1189176, by rfl⟩ : syracuseStep 3171137 = 2378353) B2378353
theorem B2114091 : Blo 2113435 2114091 := bstep (se 1 (by rfl) ⟨1585568, by rfl⟩ : syracuseStep 2114091 = 3171137) B3171137
theorem B2857253 : Blo 2113435 2857253 := bbase (se 4 (by rfl) ⟨267867, by rfl⟩ : syracuseStep 2857253 = 535735) (by norm_num)
theorem B7619341 : Blo 2113435 7619341 := bstep (se 3 (by rfl) ⟨1428626, by rfl⟩ : syracuseStep 7619341 = 2857253) B2857253
theorem B10159121 : Blo 2113435 10159121 := bstep (se 2 (by rfl) ⟨3809670, by rfl⟩ : syracuseStep 10159121 = 7619341) B7619341
theorem B6772747 : Blo 2113435 6772747 := bstep (se 1 (by rfl) ⟨5079560, by rfl⟩ : syracuseStep 6772747 = 10159121) B10159121
theorem B9030329 : Blo 2113435 9030329 := bstep (se 2 (by rfl) ⟨3386373, by rfl⟩ : syracuseStep 9030329 = 6772747) B6772747
theorem B6020219 : Blo 2113435 6020219 := bstep (se 1 (by rfl) ⟨4515164, by rfl⟩ : syracuseStep 6020219 = 9030329) B9030329
theorem B4013479 : Blo 2113435 4013479 := bstep (se 1 (by rfl) ⟨3010109, by rfl⟩ : syracuseStep 4013479 = 6020219) B6020219
theorem B5351305 : Blo 2113435 5351305 := bstep (se 2 (by rfl) ⟨2006739, by rfl⟩ : syracuseStep 5351305 = 4013479) B4013479
theorem B7135073 : Blo 2113435 7135073 := bstep (se 2 (by rfl) ⟨2675652, by rfl⟩ : syracuseStep 7135073 = 5351305) B5351305
theorem B4756715 : Blo 2113435 4756715 := bstep (se 1 (by rfl) ⟨3567536, by rfl⟩ : syracuseStep 4756715 = 7135073) B7135073
theorem B3171143 : Blo 2113435 3171143 := bstep (se 1 (by rfl) ⟨2378357, by rfl⟩ : syracuseStep 3171143 = 4756715) B4756715
theorem B2114095 : Blo 2113435 2114095 := bstep (se 1 (by rfl) ⟨1585571, by rfl⟩ : syracuseStep 2114095 = 3171143) B3171143
theorem B3171149 : Blo 2113435 3171149 := bbase (se 3 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 3171149 = 1189181) (by norm_num)
theorem B2114099 : Blo 2113435 2114099 := bstep (se 1 (by rfl) ⟨1585574, by rfl⟩ : syracuseStep 2114099 = 3171149) B3171149
theorem B4756733 : Blo 2113435 4756733 := bbase (se 3 (by rfl) ⟨891887, by rfl⟩ : syracuseStep 4756733 = 1783775) (by norm_num)
theorem B3171155 : Blo 2113435 3171155 := bstep (se 1 (by rfl) ⟨2378366, by rfl⟩ : syracuseStep 3171155 = 4756733) B4756733
theorem B2114103 : Blo 2113435 2114103 := bstep (se 1 (by rfl) ⟨1585577, by rfl⟩ : syracuseStep 2114103 = 3171155) B3171155
theorem B3567557 : Blo 2113435 3567557 := bbase (se 4 (by rfl) ⟨334458, by rfl⟩ : syracuseStep 3567557 = 668917) (by norm_num)
theorem B2378371 : Blo 2113435 2378371 := bstep (se 1 (by rfl) ⟨1783778, by rfl⟩ : syracuseStep 2378371 = 3567557) B3567557
theorem B3171161 : Blo 2113435 3171161 := bstep (se 2 (by rfl) ⟨1189185, by rfl⟩ : syracuseStep 3171161 = 2378371) B2378371
theorem B2114107 : Blo 2113435 2114107 := bstep (se 1 (by rfl) ⟨1585580, by rfl⟩ : syracuseStep 2114107 = 3171161) B3171161
theorem B16054037 : Blo 2113435 16054037 := bbase (se 6 (by rfl) ⟨376266, by rfl⟩ : syracuseStep 16054037 = 752533) (by norm_num)
theorem B10702691 : Blo 2113435 10702691 := bstep (se 1 (by rfl) ⟨8027018, by rfl⟩ : syracuseStep 10702691 = 16054037) B16054037
theorem B7135127 : Blo 2113435 7135127 := bstep (se 1 (by rfl) ⟨5351345, by rfl⟩ : syracuseStep 7135127 = 10702691) B10702691
theorem B4756751 : Blo 2113435 4756751 := bstep (se 1 (by rfl) ⟨3567563, by rfl⟩ : syracuseStep 4756751 = 7135127) B7135127
theorem B3171167 : Blo 2113435 3171167 := bstep (se 1 (by rfl) ⟨2378375, by rfl⟩ : syracuseStep 3171167 = 4756751) B4756751
theorem B2114111 : Blo 2113435 2114111 := bstep (se 1 (by rfl) ⟨1585583, by rfl⟩ : syracuseStep 2114111 = 3171167) B3171167
theorem B3171173 : Blo 2113435 3171173 := bbase (se 4 (by rfl) ⟨297297, by rfl⟩ : syracuseStep 3171173 = 594595) (by norm_num)
theorem B2114115 : Blo 2113435 2114115 := bstep (se 1 (by rfl) ⟨1585586, by rfl⟩ : syracuseStep 2114115 = 3171173) B3171173
theorem B4013525 : Blo 2113435 4013525 := bbase (se 7 (by rfl) ⟨47033, by rfl⟩ : syracuseStep 4013525 = 94067) (by norm_num)
theorem B2675683 : Blo 2113435 2675683 := bstep (se 1 (by rfl) ⟨2006762, by rfl⟩ : syracuseStep 2675683 = 4013525) B4013525
theorem B3567577 : Blo 2113435 3567577 := bstep (se 2 (by rfl) ⟨1337841, by rfl⟩ : syracuseStep 3567577 = 2675683) B2675683
theorem B4756769 : Blo 2113435 4756769 := bstep (se 2 (by rfl) ⟨1783788, by rfl⟩ : syracuseStep 4756769 = 3567577) B3567577
theorem B3171179 : Blo 2113435 3171179 := bstep (se 1 (by rfl) ⟨2378384, by rfl⟩ : syracuseStep 3171179 = 4756769) B4756769
theorem B2114119 : Blo 2113435 2114119 := bstep (se 1 (by rfl) ⟨1585589, by rfl⟩ : syracuseStep 2114119 = 3171179) B3171179
theorem B2378389 : Blo 2113435 2378389 := bbase (se 6 (by rfl) ⟨55743, by rfl⟩ : syracuseStep 2378389 = 111487) (by norm_num)
theorem B3171185 : Blo 2113435 3171185 := bstep (se 2 (by rfl) ⟨1189194, by rfl⟩ : syracuseStep 3171185 = 2378389) B2378389
theorem B2114123 : Blo 2113435 2114123 := bstep (se 1 (by rfl) ⟨1585592, by rfl⟩ : syracuseStep 2114123 = 3171185) B3171185
theorem B2675693 : Blo 2113435 2675693 := bbase (se 3 (by rfl) ⟨501692, by rfl⟩ : syracuseStep 2675693 = 1003385) (by norm_num)
theorem B7135181 : Blo 2113435 7135181 := bstep (se 3 (by rfl) ⟨1337846, by rfl⟩ : syracuseStep 7135181 = 2675693) B2675693
theorem B4756787 : Blo 2113435 4756787 := bstep (se 1 (by rfl) ⟨3567590, by rfl⟩ : syracuseStep 4756787 = 7135181) B7135181
theorem B3171191 : Blo 2113435 3171191 := bstep (se 1 (by rfl) ⟨2378393, by rfl⟩ : syracuseStep 3171191 = 4756787) B4756787
theorem B2114127 : Blo 2113435 2114127 := bstep (se 1 (by rfl) ⟨1585595, by rfl⟩ : syracuseStep 2114127 = 3171191) B3171191
theorem B3171197 : Blo 2113435 3171197 := bbase (se 3 (by rfl) ⟨594599, by rfl⟩ : syracuseStep 3171197 = 1189199) (by norm_num)
theorem B2114131 : Blo 2113435 2114131 := bstep (se 1 (by rfl) ⟨1585598, by rfl⟩ : syracuseStep 2114131 = 3171197) B3171197
theorem B4756805 : Blo 2113435 4756805 := bbase (se 4 (by rfl) ⟨445950, by rfl⟩ : syracuseStep 4756805 = 891901) (by norm_num)
theorem B3171203 : Blo 2113435 3171203 := bstep (se 1 (by rfl) ⟨2378402, by rfl⟩ : syracuseStep 3171203 = 4756805) B4756805
theorem B2114135 : Blo 2113435 2114135 := bstep (se 1 (by rfl) ⟨1585601, by rfl⟩ : syracuseStep 2114135 = 3171203) B3171203
theorem B2142985 : Blo 2113435 2142985 := bbase (se 2 (by rfl) ⟨803619, by rfl⟩ : syracuseStep 2142985 = 1607239) (by norm_num)
theorem B2857313 : Blo 2113435 2857313 := bstep (se 2 (by rfl) ⟨1071492, by rfl⟩ : syracuseStep 2857313 = 2142985) B2142985
theorem B7619501 : Blo 2113435 7619501 := bstep (se 3 (by rfl) ⟨1428656, by rfl⟩ : syracuseStep 7619501 = 2857313) B2857313
theorem B5079667 : Blo 2113435 5079667 := bstep (se 1 (by rfl) ⟨3809750, by rfl⟩ : syracuseStep 5079667 = 7619501) B7619501
theorem B6772889 : Blo 2113435 6772889 := bstep (se 2 (by rfl) ⟨2539833, by rfl⟩ : syracuseStep 6772889 = 5079667) B5079667
theorem B4515259 : Blo 2113435 4515259 := bstep (se 1 (by rfl) ⟨3386444, by rfl⟩ : syracuseStep 4515259 = 6772889) B6772889
theorem B6020345 : Blo 2113435 6020345 := bstep (se 2 (by rfl) ⟨2257629, by rfl⟩ : syracuseStep 6020345 = 4515259) B4515259
theorem B4013563 : Blo 2113435 4013563 := bstep (se 1 (by rfl) ⟨3010172, by rfl⟩ : syracuseStep 4013563 = 6020345) B6020345
theorem B5351417 : Blo 2113435 5351417 := bstep (se 2 (by rfl) ⟨2006781, by rfl⟩ : syracuseStep 5351417 = 4013563) B4013563
theorem B3567611 : Blo 2113435 3567611 := bstep (se 1 (by rfl) ⟨2675708, by rfl⟩ : syracuseStep 3567611 = 5351417) B5351417
theorem B2378407 : Blo 2113435 2378407 := bstep (se 1 (by rfl) ⟨1783805, by rfl⟩ : syracuseStep 2378407 = 3567611) B3567611
theorem B3171209 : Blo 2113435 3171209 := bstep (se 2 (by rfl) ⟨1189203, by rfl⟩ : syracuseStep 3171209 = 2378407) B2378407
theorem B2114139 : Blo 2113435 2114139 := bstep (se 1 (by rfl) ⟨1585604, by rfl⟩ : syracuseStep 2114139 = 3171209) B3171209
theorem B10702853 : Blo 2113435 10702853 := bbase (se 4 (by rfl) ⟨1003392, by rfl⟩ : syracuseStep 10702853 = 2006785) (by norm_num)
theorem B7135235 : Blo 2113435 7135235 := bstep (se 1 (by rfl) ⟨5351426, by rfl⟩ : syracuseStep 7135235 = 10702853) B10702853
theorem B4756823 : Blo 2113435 4756823 := bstep (se 1 (by rfl) ⟨3567617, by rfl⟩ : syracuseStep 4756823 = 7135235) B7135235
theorem B3171215 : Blo 2113435 3171215 := bstep (se 1 (by rfl) ⟨2378411, by rfl⟩ : syracuseStep 3171215 = 4756823) B4756823
theorem B2114143 : Blo 2113435 2114143 := bstep (se 1 (by rfl) ⟨1585607, by rfl⟩ : syracuseStep 2114143 = 3171215) B3171215
theorem B3171221 : Blo 2113435 3171221 := bbase (se 6 (by rfl) ⟨74325, by rfl⟩ : syracuseStep 3171221 = 148651) (by norm_num)
theorem B2114147 : Blo 2113435 2114147 := bstep (se 1 (by rfl) ⟨1585610, by rfl⟩ : syracuseStep 2114147 = 3171221) B3171221
theorem B12040757 : Blo 2113435 12040757 := bbase (se 5 (by rfl) ⟨564410, by rfl⟩ : syracuseStep 12040757 = 1128821) (by norm_num)
theorem B8027171 : Blo 2113435 8027171 := bstep (se 1 (by rfl) ⟨6020378, by rfl⟩ : syracuseStep 8027171 = 12040757) B12040757
theorem B5351447 : Blo 2113435 5351447 := bstep (se 1 (by rfl) ⟨4013585, by rfl⟩ : syracuseStep 5351447 = 8027171) B8027171
theorem B3567631 : Blo 2113435 3567631 := bstep (se 1 (by rfl) ⟨2675723, by rfl⟩ : syracuseStep 3567631 = 5351447) B5351447
theorem B4756841 : Blo 2113435 4756841 := bstep (se 2 (by rfl) ⟨1783815, by rfl⟩ : syracuseStep 4756841 = 3567631) B3567631
theorem B3171227 : Blo 2113435 3171227 := bstep (se 1 (by rfl) ⟨2378420, by rfl⟩ : syracuseStep 3171227 = 4756841) B4756841
theorem B2114151 : Blo 2113435 2114151 := bstep (se 1 (by rfl) ⟨1585613, by rfl⟩ : syracuseStep 2114151 = 3171227) B3171227
theorem B2378425 : Blo 2113435 2378425 := bbase (se 2 (by rfl) ⟨891909, by rfl⟩ : syracuseStep 2378425 = 1783819) (by norm_num)
theorem B3171233 : Blo 2113435 3171233 := bstep (se 2 (by rfl) ⟨1189212, by rfl⟩ : syracuseStep 3171233 = 2378425) B2378425
theorem B2114155 : Blo 2113435 2114155 := bstep (se 1 (by rfl) ⟨1585616, by rfl⟩ : syracuseStep 2114155 = 3171233) B3171233
theorem B4515301 : Blo 2113435 4515301 := bbase (se 4 (by rfl) ⟨423309, by rfl⟩ : syracuseStep 4515301 = 846619) (by norm_num)
theorem B6020401 : Blo 2113435 6020401 := bstep (se 2 (by rfl) ⟨2257650, by rfl⟩ : syracuseStep 6020401 = 4515301) B4515301
theorem B8027201 : Blo 2113435 8027201 := bstep (se 2 (by rfl) ⟨3010200, by rfl⟩ : syracuseStep 8027201 = 6020401) B6020401
theorem B5351467 : Blo 2113435 5351467 := bstep (se 1 (by rfl) ⟨4013600, by rfl⟩ : syracuseStep 5351467 = 8027201) B8027201
theorem B7135289 : Blo 2113435 7135289 := bstep (se 2 (by rfl) ⟨2675733, by rfl⟩ : syracuseStep 7135289 = 5351467) B5351467
theorem B4756859 : Blo 2113435 4756859 := bstep (se 1 (by rfl) ⟨3567644, by rfl⟩ : syracuseStep 4756859 = 7135289) B7135289
theorem B3171239 : Blo 2113435 3171239 := bstep (se 1 (by rfl) ⟨2378429, by rfl⟩ : syracuseStep 3171239 = 4756859) B4756859
theorem B2114159 : Blo 2113435 2114159 := bstep (se 1 (by rfl) ⟨1585619, by rfl⟩ : syracuseStep 2114159 = 3171239) B3171239
theorem B3171245 : Blo 2113435 3171245 := bbase (se 3 (by rfl) ⟨594608, by rfl⟩ : syracuseStep 3171245 = 1189217) (by norm_num)
theorem B2114163 : Blo 2113435 2114163 := bstep (se 1 (by rfl) ⟨1585622, by rfl⟩ : syracuseStep 2114163 = 3171245) B3171245
theorem B4756877 : Blo 2113435 4756877 := bbase (se 3 (by rfl) ⟨891914, by rfl⟩ : syracuseStep 4756877 = 1783829) (by norm_num)
theorem B3171251 : Blo 2113435 3171251 := bstep (se 1 (by rfl) ⟨2378438, by rfl⟩ : syracuseStep 3171251 = 4756877) B4756877
theorem B2114167 : Blo 2113435 2114167 := bstep (se 1 (by rfl) ⟨1585625, by rfl⟩ : syracuseStep 2114167 = 3171251) B3171251
theorem B2675749 : Blo 2113435 2675749 := bbase (se 4 (by rfl) ⟨250851, by rfl⟩ : syracuseStep 2675749 = 501703) (by norm_num)
theorem B3567665 : Blo 2113435 3567665 := bstep (se 2 (by rfl) ⟨1337874, by rfl⟩ : syracuseStep 3567665 = 2675749) B2675749
theorem B2378443 : Blo 2113435 2378443 := bstep (se 1 (by rfl) ⟨1783832, by rfl⟩ : syracuseStep 2378443 = 3567665) B3567665
theorem B3171257 : Blo 2113435 3171257 := bstep (se 2 (by rfl) ⟨1189221, by rfl⟩ : syracuseStep 3171257 = 2378443) B2378443
theorem B2114171 : Blo 2113435 2114171 := bstep (se 1 (by rfl) ⟨1585628, by rfl⟩ : syracuseStep 2114171 = 3171257) B3171257
theorem B3258389 : Blo 2113435 3258389 := bbase (se 6 (by rfl) ⟨76368, by rfl⟩ : syracuseStep 3258389 = 152737) (by norm_num)
theorem B2172259 : Blo 2113435 2172259 := bstep (se 1 (by rfl) ⟨1629194, by rfl⟩ : syracuseStep 2172259 = 3258389) B3258389
theorem B2896345 : Blo 2113435 2896345 := bstep (se 2 (by rfl) ⟨1086129, by rfl⟩ : syracuseStep 2896345 = 2172259) B2172259
theorem B3861793 : Blo 2113435 3861793 := bstep (se 2 (by rfl) ⟨1448172, by rfl⟩ : syracuseStep 3861793 = 2896345) B2896345
theorem B5149057 : Blo 2113435 5149057 := bstep (se 2 (by rfl) ⟨1930896, by rfl⟩ : syracuseStep 5149057 = 3861793) B3861793
theorem B6865409 : Blo 2113435 6865409 := bstep (se 2 (by rfl) ⟨2574528, by rfl⟩ : syracuseStep 6865409 = 5149057) B5149057
theorem B18307757 : Blo 2113435 18307757 := bstep (se 3 (by rfl) ⟨3432704, by rfl⟩ : syracuseStep 18307757 = 6865409) B6865409
theorem B12205171 : Blo 2113435 12205171 := bstep (se 1 (by rfl) ⟨9153878, by rfl⟩ : syracuseStep 12205171 = 18307757) B18307757
theorem B65094245 : Blo 2113435 65094245 := bstep (se 4 (by rfl) ⟨6102585, by rfl⟩ : syracuseStep 65094245 = 12205171) B12205171
theorem B43396163 : Blo 2113435 43396163 := bstep (se 1 (by rfl) ⟨32547122, by rfl⟩ : syracuseStep 43396163 = 65094245) B65094245
theorem B28930775 : Blo 2113435 28930775 := bstep (se 1 (by rfl) ⟨21698081, by rfl⟩ : syracuseStep 28930775 = 43396163) B43396163
theorem B77148733 : Blo 2113435 77148733 := bstep (se 3 (by rfl) ⟨14465387, by rfl⟩ : syracuseStep 77148733 = 28930775) B28930775
theorem B102864977 : Blo 2113435 102864977 := bstep (se 2 (by rfl) ⟨38574366, by rfl⟩ : syracuseStep 102864977 = 77148733) B77148733
theorem B68576651 : Blo 2113435 68576651 := bstep (se 1 (by rfl) ⟨51432488, by rfl⟩ : syracuseStep 68576651 = 102864977) B102864977
theorem B45717767 : Blo 2113435 45717767 := bstep (se 1 (by rfl) ⟨34288325, by rfl⟩ : syracuseStep 45717767 = 68576651) B68576651
theorem B30478511 : Blo 2113435 30478511 := bstep (se 1 (by rfl) ⟨22858883, by rfl⟩ : syracuseStep 30478511 = 45717767) B45717767
theorem B20319007 : Blo 2113435 20319007 := bstep (se 1 (by rfl) ⟨15239255, by rfl⟩ : syracuseStep 20319007 = 30478511) B30478511
theorem B27092009 : Blo 2113435 27092009 := bstep (se 2 (by rfl) ⟨10159503, by rfl⟩ : syracuseStep 27092009 = 20319007) B20319007
theorem B18061339 : Blo 2113435 18061339 := bstep (se 1 (by rfl) ⟨13546004, by rfl⟩ : syracuseStep 18061339 = 27092009) B27092009
theorem B24081785 : Blo 2113435 24081785 := bstep (se 2 (by rfl) ⟨9030669, by rfl⟩ : syracuseStep 24081785 = 18061339) B18061339
theorem B16054523 : Blo 2113435 16054523 := bstep (se 1 (by rfl) ⟨12040892, by rfl⟩ : syracuseStep 16054523 = 24081785) B24081785
theorem B10703015 : Blo 2113435 10703015 := bstep (se 1 (by rfl) ⟨8027261, by rfl⟩ : syracuseStep 10703015 = 16054523) B16054523
theorem B7135343 : Blo 2113435 7135343 := bstep (se 1 (by rfl) ⟨5351507, by rfl⟩ : syracuseStep 7135343 = 10703015) B10703015
theorem B4756895 : Blo 2113435 4756895 := bstep (se 1 (by rfl) ⟨3567671, by rfl⟩ : syracuseStep 4756895 = 7135343) B7135343
theorem B3171263 : Blo 2113435 3171263 := bstep (se 1 (by rfl) ⟨2378447, by rfl⟩ : syracuseStep 3171263 = 4756895) B4756895
theorem B2114175 : Blo 2113435 2114175 := bstep (se 1 (by rfl) ⟨1585631, by rfl⟩ : syracuseStep 2114175 = 3171263) B3171263
theorem B3171269 : Blo 2113435 3171269 := bbase (se 4 (by rfl) ⟨297306, by rfl⟩ : syracuseStep 3171269 = 594613) (by norm_num)
theorem B2114179 : Blo 2113435 2114179 := bstep (se 1 (by rfl) ⟨1585634, by rfl⟩ : syracuseStep 2114179 = 3171269) B3171269
theorem B3567685 : Blo 2113435 3567685 := bbase (se 4 (by rfl) ⟨334470, by rfl⟩ : syracuseStep 3567685 = 668941) (by norm_num)
theorem B4756913 : Blo 2113435 4756913 := bstep (se 2 (by rfl) ⟨1783842, by rfl⟩ : syracuseStep 4756913 = 3567685) B3567685
theorem B3171275 : Blo 2113435 3171275 := bstep (se 1 (by rfl) ⟨2378456, by rfl⟩ : syracuseStep 3171275 = 4756913) B4756913
theorem B2114183 : Blo 2113435 2114183 := bstep (se 1 (by rfl) ⟨1585637, by rfl⟩ : syracuseStep 2114183 = 3171275) B3171275
theorem B2378461 : Blo 2113435 2378461 := bbase (se 3 (by rfl) ⟨445961, by rfl⟩ : syracuseStep 2378461 = 891923) (by norm_num)
theorem B3171281 : Blo 2113435 3171281 := bstep (se 2 (by rfl) ⟨1189230, by rfl⟩ : syracuseStep 3171281 = 2378461) B2378461
theorem B2114187 : Blo 2113435 2114187 := bstep (se 1 (by rfl) ⟨1585640, by rfl⟩ : syracuseStep 2114187 = 3171281) B3171281
theorem B7135397 : Blo 2113435 7135397 := bbase (se 4 (by rfl) ⟨668943, by rfl⟩ : syracuseStep 7135397 = 1337887) (by norm_num)
theorem B4756931 : Blo 2113435 4756931 := bstep (se 1 (by rfl) ⟨3567698, by rfl⟩ : syracuseStep 4756931 = 7135397) B7135397
theorem B3171287 : Blo 2113435 3171287 := bstep (se 1 (by rfl) ⟨2378465, by rfl⟩ : syracuseStep 3171287 = 4756931) B4756931
theorem B2114191 : Blo 2113435 2114191 := bstep (se 1 (by rfl) ⟨1585643, by rfl⟩ : syracuseStep 2114191 = 3171287) B3171287
theorem B3171293 : Blo 2113435 3171293 := bbase (se 3 (by rfl) ⟨594617, by rfl⟩ : syracuseStep 3171293 = 1189235) (by norm_num)
theorem B2114195 : Blo 2113435 2114195 := bstep (se 1 (by rfl) ⟨1585646, by rfl⟩ : syracuseStep 2114195 = 3171293) B3171293
theorem B4756949 : Blo 2113435 4756949 := bbase (se 7 (by rfl) ⟨55745, by rfl⟩ : syracuseStep 4756949 = 111491) (by norm_num)
theorem B3171299 : Blo 2113435 3171299 := bstep (se 1 (by rfl) ⟨2378474, by rfl⟩ : syracuseStep 3171299 = 4756949) B4756949
theorem B2114199 : Blo 2113435 2114199 := bstep (se 1 (by rfl) ⟨1585649, by rfl⟩ : syracuseStep 2114199 = 3171299) B3171299
theorem B3616397 : Blo 2113435 3616397 := bbase (se 3 (by rfl) ⟨678074, by rfl⟩ : syracuseStep 3616397 = 1356149) (by norm_num)
theorem B2410931 : Blo 2113435 2410931 := bstep (se 1 (by rfl) ⟨1808198, by rfl⟩ : syracuseStep 2410931 = 3616397) B3616397
theorem B6429149 : Blo 2113435 6429149 := bstep (se 3 (by rfl) ⟨1205465, by rfl⟩ : syracuseStep 6429149 = 2410931) B2410931
theorem B4286099 : Blo 2113435 4286099 := bstep (se 1 (by rfl) ⟨3214574, by rfl⟩ : syracuseStep 4286099 = 6429149) B6429149
theorem B2857399 : Blo 2113435 2857399 := bstep (se 1 (by rfl) ⟨2143049, by rfl⟩ : syracuseStep 2857399 = 4286099) B4286099
theorem B15239461 : Blo 2113435 15239461 := bstep (se 4 (by rfl) ⟨1428699, by rfl⟩ : syracuseStep 15239461 = 2857399) B2857399
theorem B20319281 : Blo 2113435 20319281 := bstep (se 2 (by rfl) ⟨7619730, by rfl⟩ : syracuseStep 20319281 = 15239461) B15239461
theorem B13546187 : Blo 2113435 13546187 := bstep (se 1 (by rfl) ⟨10159640, by rfl⟩ : syracuseStep 13546187 = 20319281) B20319281
theorem B9030791 : Blo 2113435 9030791 := bstep (se 1 (by rfl) ⟨6773093, by rfl⟩ : syracuseStep 9030791 = 13546187) B13546187
theorem B6020527 : Blo 2113435 6020527 := bstep (se 1 (by rfl) ⟨4515395, by rfl⟩ : syracuseStep 6020527 = 9030791) B9030791
theorem B8027369 : Blo 2113435 8027369 := bstep (se 2 (by rfl) ⟨3010263, by rfl⟩ : syracuseStep 8027369 = 6020527) B6020527
theorem B5351579 : Blo 2113435 5351579 := bstep (se 1 (by rfl) ⟨4013684, by rfl⟩ : syracuseStep 5351579 = 8027369) B8027369
theorem B3567719 : Blo 2113435 3567719 := bstep (se 1 (by rfl) ⟨2675789, by rfl⟩ : syracuseStep 3567719 = 5351579) B5351579
theorem B2378479 : Blo 2113435 2378479 := bstep (se 1 (by rfl) ⟨1783859, by rfl⟩ : syracuseStep 2378479 = 3567719) B3567719
theorem B3171305 : Blo 2113435 3171305 := bstep (se 2 (by rfl) ⟨1189239, by rfl⟩ : syracuseStep 3171305 = 2378479) B2378479
theorem B2114203 : Blo 2113435 2114203 := bstep (se 1 (by rfl) ⟨1585652, by rfl⟩ : syracuseStep 2114203 = 3171305) B3171305
theorem B5079829 : Blo 2113435 5079829 := bbase (se 6 (by rfl) ⟨119058, by rfl⟩ : syracuseStep 5079829 = 238117) (by norm_num)
theorem B6773105 : Blo 2113435 6773105 := bstep (se 2 (by rfl) ⟨2539914, by rfl⟩ : syracuseStep 6773105 = 5079829) B5079829
theorem B18061613 : Blo 2113435 18061613 := bstep (se 3 (by rfl) ⟨3386552, by rfl⟩ : syracuseStep 18061613 = 6773105) B6773105
theorem B12041075 : Blo 2113435 12041075 := bstep (se 1 (by rfl) ⟨9030806, by rfl⟩ : syracuseStep 12041075 = 18061613) B18061613
theorem B8027383 : Blo 2113435 8027383 := bstep (se 1 (by rfl) ⟨6020537, by rfl⟩ : syracuseStep 8027383 = 12041075) B12041075
theorem B10703177 : Blo 2113435 10703177 := bstep (se 2 (by rfl) ⟨4013691, by rfl⟩ : syracuseStep 10703177 = 8027383) B8027383
theorem B7135451 : Blo 2113435 7135451 := bstep (se 1 (by rfl) ⟨5351588, by rfl⟩ : syracuseStep 7135451 = 10703177) B10703177
theorem B4756967 : Blo 2113435 4756967 := bstep (se 1 (by rfl) ⟨3567725, by rfl⟩ : syracuseStep 4756967 = 7135451) B7135451
theorem B3171311 : Blo 2113435 3171311 := bstep (se 1 (by rfl) ⟨2378483, by rfl⟩ : syracuseStep 3171311 = 4756967) B4756967
theorem B2114207 : Blo 2113435 2114207 := bstep (se 1 (by rfl) ⟨1585655, by rfl⟩ : syracuseStep 2114207 = 3171311) B3171311
theorem B3171317 : Blo 2113435 3171317 := bbase (se 5 (by rfl) ⟨148655, by rfl⟩ : syracuseStep 3171317 = 297311) (by norm_num)
theorem B2114211 : Blo 2113435 2114211 := bstep (se 1 (by rfl) ⟨1585658, by rfl⟩ : syracuseStep 2114211 = 3171317) B3171317
theorem B4515421 : Blo 2113435 4515421 := bbase (se 3 (by rfl) ⟨846641, by rfl⟩ : syracuseStep 4515421 = 1693283) (by norm_num)
theorem B6020561 : Blo 2113435 6020561 := bstep (se 2 (by rfl) ⟨2257710, by rfl⟩ : syracuseStep 6020561 = 4515421) B4515421
theorem B4013707 : Blo 2113435 4013707 := bstep (se 1 (by rfl) ⟨3010280, by rfl⟩ : syracuseStep 4013707 = 6020561) B6020561
theorem B5351609 : Blo 2113435 5351609 := bstep (se 2 (by rfl) ⟨2006853, by rfl⟩ : syracuseStep 5351609 = 4013707) B4013707
theorem B3567739 : Blo 2113435 3567739 := bstep (se 1 (by rfl) ⟨2675804, by rfl⟩ : syracuseStep 3567739 = 5351609) B5351609
theorem B4756985 : Blo 2113435 4756985 := bstep (se 2 (by rfl) ⟨1783869, by rfl⟩ : syracuseStep 4756985 = 3567739) B3567739
theorem B3171323 : Blo 2113435 3171323 := bstep (se 1 (by rfl) ⟨2378492, by rfl⟩ : syracuseStep 3171323 = 4756985) B4756985
theorem B2114215 : Blo 2113435 2114215 := bstep (se 1 (by rfl) ⟨1585661, by rfl⟩ : syracuseStep 2114215 = 3171323) B3171323
theorem B2378497 : Blo 2113435 2378497 := bbase (se 2 (by rfl) ⟨891936, by rfl⟩ : syracuseStep 2378497 = 1783873) (by norm_num)
theorem B3171329 : Blo 2113435 3171329 := bstep (se 2 (by rfl) ⟨1189248, by rfl⟩ : syracuseStep 3171329 = 2378497) B2378497
theorem B2114219 : Blo 2113435 2114219 := bstep (se 1 (by rfl) ⟨1585664, by rfl⟩ : syracuseStep 2114219 = 3171329) B3171329
theorem B5351629 : Blo 2113435 5351629 := bbase (se 3 (by rfl) ⟨1003430, by rfl⟩ : syracuseStep 5351629 = 2006861) (by norm_num)
theorem B7135505 : Blo 2113435 7135505 := bstep (se 2 (by rfl) ⟨2675814, by rfl⟩ : syracuseStep 7135505 = 5351629) B5351629
theorem B4757003 : Blo 2113435 4757003 := bstep (se 1 (by rfl) ⟨3567752, by rfl⟩ : syracuseStep 4757003 = 7135505) B7135505
theorem B3171335 : Blo 2113435 3171335 := bstep (se 1 (by rfl) ⟨2378501, by rfl⟩ : syracuseStep 3171335 = 4757003) B4757003
theorem B2114223 : Blo 2113435 2114223 := bstep (se 1 (by rfl) ⟨1585667, by rfl⟩ : syracuseStep 2114223 = 3171335) B3171335
theorem B3171341 : Blo 2113435 3171341 := bbase (se 3 (by rfl) ⟨594626, by rfl⟩ : syracuseStep 3171341 = 1189253) (by norm_num)
theorem B2114227 : Blo 2113435 2114227 := bstep (se 1 (by rfl) ⟨1585670, by rfl⟩ : syracuseStep 2114227 = 3171341) B3171341
theorem B4757021 : Blo 2113435 4757021 := bbase (se 3 (by rfl) ⟨891941, by rfl⟩ : syracuseStep 4757021 = 1783883) (by norm_num)
theorem B3171347 : Blo 2113435 3171347 := bstep (se 1 (by rfl) ⟨2378510, by rfl⟩ : syracuseStep 3171347 = 4757021) B4757021
theorem B2114231 : Blo 2113435 2114231 := bstep (se 1 (by rfl) ⟨1585673, by rfl⟩ : syracuseStep 2114231 = 3171347) B3171347
theorem B3567773 : Blo 2113435 3567773 := bbase (se 3 (by rfl) ⟨668957, by rfl⟩ : syracuseStep 3567773 = 1337915) (by norm_num)
theorem B2378515 : Blo 2113435 2378515 := bstep (se 1 (by rfl) ⟨1783886, by rfl⟩ : syracuseStep 2378515 = 3567773) B3567773
theorem B3171353 : Blo 2113435 3171353 := bstep (se 2 (by rfl) ⟨1189257, by rfl⟩ : syracuseStep 3171353 = 2378515) B2378515
theorem B2114235 : Blo 2113435 2114235 := bstep (se 1 (by rfl) ⟨1585676, by rfl⟩ : syracuseStep 2114235 = 3171353) B3171353
theorem B34289365 : Blo 2113435 34289365 := bbase (se 7 (by rfl) ⟨401828, by rfl⟩ : syracuseStep 34289365 = 803657) (by norm_num)
theorem B45719153 : Blo 2113435 45719153 := bstep (se 2 (by rfl) ⟨17144682, by rfl⟩ : syracuseStep 45719153 = 34289365) B34289365
theorem B30479435 : Blo 2113435 30479435 := bstep (se 1 (by rfl) ⟨22859576, by rfl⟩ : syracuseStep 30479435 = 45719153) B45719153
theorem B20319623 : Blo 2113435 20319623 := bstep (se 1 (by rfl) ⟨15239717, by rfl⟩ : syracuseStep 20319623 = 30479435) B30479435
theorem B13546415 : Blo 2113435 13546415 := bstep (se 1 (by rfl) ⟨10159811, by rfl⟩ : syracuseStep 13546415 = 20319623) B20319623
theorem B9030943 : Blo 2113435 9030943 := bstep (se 1 (by rfl) ⟨6773207, by rfl⟩ : syracuseStep 9030943 = 13546415) B13546415
theorem B12041257 : Blo 2113435 12041257 := bstep (se 2 (by rfl) ⟨4515471, by rfl⟩ : syracuseStep 12041257 = 9030943) B9030943
theorem B16055009 : Blo 2113435 16055009 := bstep (se 2 (by rfl) ⟨6020628, by rfl⟩ : syracuseStep 16055009 = 12041257) B12041257
theorem B10703339 : Blo 2113435 10703339 := bstep (se 1 (by rfl) ⟨8027504, by rfl⟩ : syracuseStep 10703339 = 16055009) B16055009
theorem B7135559 : Blo 2113435 7135559 := bstep (se 1 (by rfl) ⟨5351669, by rfl⟩ : syracuseStep 7135559 = 10703339) B10703339
theorem B4757039 : Blo 2113435 4757039 := bstep (se 1 (by rfl) ⟨3567779, by rfl⟩ : syracuseStep 4757039 = 7135559) B7135559
theorem B3171359 : Blo 2113435 3171359 := bstep (se 1 (by rfl) ⟨2378519, by rfl⟩ : syracuseStep 3171359 = 4757039) B4757039
theorem B2114239 : Blo 2113435 2114239 := bstep (se 1 (by rfl) ⟨1585679, by rfl⟩ : syracuseStep 2114239 = 3171359) B3171359
theorem B3171365 : Blo 2113435 3171365 := bbase (se 4 (by rfl) ⟨297315, by rfl⟩ : syracuseStep 3171365 = 594631) (by norm_num)
theorem B2114243 : Blo 2113435 2114243 := bstep (se 1 (by rfl) ⟨1585682, by rfl⟩ : syracuseStep 2114243 = 3171365) B3171365
theorem B2675845 : Blo 2113435 2675845 := bbase (se 4 (by rfl) ⟨250860, by rfl⟩ : syracuseStep 2675845 = 501721) (by norm_num)
theorem B3567793 : Blo 2113435 3567793 := bstep (se 2 (by rfl) ⟨1337922, by rfl⟩ : syracuseStep 3567793 = 2675845) B2675845
theorem B4757057 : Blo 2113435 4757057 := bstep (se 2 (by rfl) ⟨1783896, by rfl⟩ : syracuseStep 4757057 = 3567793) B3567793
theorem B3171371 : Blo 2113435 3171371 := bstep (se 1 (by rfl) ⟨2378528, by rfl⟩ : syracuseStep 3171371 = 4757057) B4757057
theorem B2114247 : Blo 2113435 2114247 := bstep (se 1 (by rfl) ⟨1585685, by rfl⟩ : syracuseStep 2114247 = 3171371) B3171371
theorem B2378533 : Blo 2113435 2378533 := bbase (se 4 (by rfl) ⟨222987, by rfl⟩ : syracuseStep 2378533 = 445975) (by norm_num)
theorem B3171377 : Blo 2113435 3171377 := bstep (se 2 (by rfl) ⟨1189266, by rfl⟩ : syracuseStep 3171377 = 2378533) B2378533
theorem B2114251 : Blo 2113435 2114251 := bstep (se 1 (by rfl) ⟨1585688, by rfl⟩ : syracuseStep 2114251 = 3171377) B3171377
theorem B9031013 : Blo 2113435 9031013 := bbase (se 4 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 9031013 = 1693315) (by norm_num)
theorem B6020675 : Blo 2113435 6020675 := bstep (se 1 (by rfl) ⟨4515506, by rfl⟩ : syracuseStep 6020675 = 9031013) B9031013
theorem B4013783 : Blo 2113435 4013783 := bstep (se 1 (by rfl) ⟨3010337, by rfl⟩ : syracuseStep 4013783 = 6020675) B6020675
theorem B2675855 : Blo 2113435 2675855 := bstep (se 1 (by rfl) ⟨2006891, by rfl⟩ : syracuseStep 2675855 = 4013783) B4013783
theorem B7135613 : Blo 2113435 7135613 := bstep (se 3 (by rfl) ⟨1337927, by rfl⟩ : syracuseStep 7135613 = 2675855) B2675855
theorem B4757075 : Blo 2113435 4757075 := bstep (se 1 (by rfl) ⟨3567806, by rfl⟩ : syracuseStep 4757075 = 7135613) B7135613
theorem B3171383 : Blo 2113435 3171383 := bstep (se 1 (by rfl) ⟨2378537, by rfl⟩ : syracuseStep 3171383 = 4757075) B4757075
theorem B2114255 : Blo 2113435 2114255 := bstep (se 1 (by rfl) ⟨1585691, by rfl⟩ : syracuseStep 2114255 = 3171383) B3171383
theorem B3171389 : Blo 2113435 3171389 := bbase (se 3 (by rfl) ⟨594635, by rfl⟩ : syracuseStep 3171389 = 1189271) (by norm_num)
theorem B2114259 : Blo 2113435 2114259 := bstep (se 1 (by rfl) ⟨1585694, by rfl⟩ : syracuseStep 2114259 = 3171389) B3171389
theorem B4757093 : Blo 2113435 4757093 := bbase (se 4 (by rfl) ⟨445977, by rfl⟩ : syracuseStep 4757093 = 891955) (by norm_num)
theorem B3171395 : Blo 2113435 3171395 := bstep (se 1 (by rfl) ⟨2378546, by rfl⟩ : syracuseStep 3171395 = 4757093) B4757093
theorem B2114263 : Blo 2113435 2114263 := bstep (se 1 (by rfl) ⟨1585697, by rfl⟩ : syracuseStep 2114263 = 3171395) B3171395
theorem B5351741 : Blo 2113435 5351741 := bbase (se 3 (by rfl) ⟨1003451, by rfl⟩ : syracuseStep 5351741 = 2006903) (by norm_num)
theorem B3567827 : Blo 2113435 3567827 := bstep (se 1 (by rfl) ⟨2675870, by rfl⟩ : syracuseStep 3567827 = 5351741) B5351741
theorem B2378551 : Blo 2113435 2378551 := bstep (se 1 (by rfl) ⟨1783913, by rfl⟩ : syracuseStep 2378551 = 3567827) B3567827
theorem B3171401 : Blo 2113435 3171401 := bstep (se 2 (by rfl) ⟨1189275, by rfl⟩ : syracuseStep 3171401 = 2378551) B2378551
theorem B2114267 : Blo 2113435 2114267 := bstep (se 1 (by rfl) ⟨1585700, by rfl⟩ : syracuseStep 2114267 = 3171401) B3171401
theorem B4013813 : Blo 2113435 4013813 := bbase (se 5 (by rfl) ⟨188147, by rfl⟩ : syracuseStep 4013813 = 376295) (by norm_num)
theorem B10703501 : Blo 2113435 10703501 := bstep (se 3 (by rfl) ⟨2006906, by rfl⟩ : syracuseStep 10703501 = 4013813) B4013813
theorem B7135667 : Blo 2113435 7135667 := bstep (se 1 (by rfl) ⟨5351750, by rfl⟩ : syracuseStep 7135667 = 10703501) B10703501
theorem B4757111 : Blo 2113435 4757111 := bstep (se 1 (by rfl) ⟨3567833, by rfl⟩ : syracuseStep 4757111 = 7135667) B7135667
theorem B3171407 : Blo 2113435 3171407 := bstep (se 1 (by rfl) ⟨2378555, by rfl⟩ : syracuseStep 3171407 = 4757111) B4757111
theorem B2114271 : Blo 2113435 2114271 := bstep (se 1 (by rfl) ⟨1585703, by rfl⟩ : syracuseStep 2114271 = 3171407) B3171407
theorem B3171413 : Blo 2113435 3171413 := bbase (se 8 (by rfl) ⟨18582, by rfl⟩ : syracuseStep 3171413 = 37165) (by norm_num)
theorem B2114275 : Blo 2113435 2114275 := bstep (se 1 (by rfl) ⟨1585706, by rfl⟩ : syracuseStep 2114275 = 3171413) B3171413
theorem B10160005 : Blo 2113435 10160005 := bbase (se 4 (by rfl) ⟨952500, by rfl⟩ : syracuseStep 10160005 = 1905001) (by norm_num)
theorem B13546673 : Blo 2113435 13546673 := bstep (se 2 (by rfl) ⟨5080002, by rfl⟩ : syracuseStep 13546673 = 10160005) B10160005
theorem B9031115 : Blo 2113435 9031115 := bstep (se 1 (by rfl) ⟨6773336, by rfl⟩ : syracuseStep 9031115 = 13546673) B13546673
theorem B6020743 : Blo 2113435 6020743 := bstep (se 1 (by rfl) ⟨4515557, by rfl⟩ : syracuseStep 6020743 = 9031115) B9031115
theorem B8027657 : Blo 2113435 8027657 := bstep (se 2 (by rfl) ⟨3010371, by rfl⟩ : syracuseStep 8027657 = 6020743) B6020743
theorem B5351771 : Blo 2113435 5351771 := bstep (se 1 (by rfl) ⟨4013828, by rfl⟩ : syracuseStep 5351771 = 8027657) B8027657
theorem B3567847 : Blo 2113435 3567847 := bstep (se 1 (by rfl) ⟨2675885, by rfl⟩ : syracuseStep 3567847 = 5351771) B5351771
theorem B4757129 : Blo 2113435 4757129 := bstep (se 2 (by rfl) ⟨1783923, by rfl⟩ : syracuseStep 4757129 = 3567847) B3567847
theorem B3171419 : Blo 2113435 3171419 := bstep (se 1 (by rfl) ⟨2378564, by rfl⟩ : syracuseStep 3171419 = 4757129) B4757129
theorem B2114279 : Blo 2113435 2114279 := bstep (se 1 (by rfl) ⟨1585709, by rfl⟩ : syracuseStep 2114279 = 3171419) B3171419
theorem B2378569 : Blo 2113435 2378569 := bbase (se 2 (by rfl) ⟨891963, by rfl⟩ : syracuseStep 2378569 = 1783927) (by norm_num)
theorem B3171425 : Blo 2113435 3171425 := bstep (se 2 (by rfl) ⟨1189284, by rfl⟩ : syracuseStep 3171425 = 2378569) B2378569
theorem B2114283 : Blo 2113435 2114283 := bstep (se 1 (by rfl) ⟨1585712, by rfl⟩ : syracuseStep 2114283 = 3171425) B3171425
theorem B20320085 : Blo 2113435 20320085 := bbase (se 9 (by rfl) ⟨59531, by rfl⟩ : syracuseStep 20320085 = 119063) (by norm_num)
theorem B13546723 : Blo 2113435 13546723 := bstep (se 1 (by rfl) ⟨10160042, by rfl⟩ : syracuseStep 13546723 = 20320085) B20320085
theorem B18062297 : Blo 2113435 18062297 := bstep (se 2 (by rfl) ⟨6773361, by rfl⟩ : syracuseStep 18062297 = 13546723) B13546723
theorem B12041531 : Blo 2113435 12041531 := bstep (se 1 (by rfl) ⟨9031148, by rfl⟩ : syracuseStep 12041531 = 18062297) B18062297
theorem B8027687 : Blo 2113435 8027687 := bstep (se 1 (by rfl) ⟨6020765, by rfl⟩ : syracuseStep 8027687 = 12041531) B12041531
theorem B5351791 : Blo 2113435 5351791 := bstep (se 1 (by rfl) ⟨4013843, by rfl⟩ : syracuseStep 5351791 = 8027687) B8027687
theorem B7135721 : Blo 2113435 7135721 := bstep (se 2 (by rfl) ⟨2675895, by rfl⟩ : syracuseStep 7135721 = 5351791) B5351791
theorem B4757147 : Blo 2113435 4757147 := bstep (se 1 (by rfl) ⟨3567860, by rfl⟩ : syracuseStep 4757147 = 7135721) B7135721
theorem B3171431 : Blo 2113435 3171431 := bstep (se 1 (by rfl) ⟨2378573, by rfl⟩ : syracuseStep 3171431 = 4757147) B4757147
theorem B2114287 : Blo 2113435 2114287 := bstep (se 1 (by rfl) ⟨1585715, by rfl⟩ : syracuseStep 2114287 = 3171431) B3171431
theorem B3171437 : Blo 2113435 3171437 := bbase (se 3 (by rfl) ⟨594644, by rfl⟩ : syracuseStep 3171437 = 1189289) (by norm_num)
theorem B2114291 : Blo 2113435 2114291 := bstep (se 1 (by rfl) ⟨1585718, by rfl⟩ : syracuseStep 2114291 = 3171437) B3171437
theorem B4757165 : Blo 2113435 4757165 := bbase (se 3 (by rfl) ⟨891968, by rfl⟩ : syracuseStep 4757165 = 1783937) (by norm_num)
theorem B3171443 : Blo 2113435 3171443 := bstep (se 1 (by rfl) ⟨2378582, by rfl⟩ : syracuseStep 3171443 = 4757165) B4757165
theorem B2114295 : Blo 2113435 2114295 := bstep (se 1 (by rfl) ⟨1585721, by rfl⟩ : syracuseStep 2114295 = 3171443) B3171443
theorem B3386701 : Blo 2113435 3386701 := bbase (se 3 (by rfl) ⟨635006, by rfl⟩ : syracuseStep 3386701 = 1270013) (by norm_num)
theorem B4515601 : Blo 2113435 4515601 := bstep (se 2 (by rfl) ⟨1693350, by rfl⟩ : syracuseStep 4515601 = 3386701) B3386701
theorem B6020801 : Blo 2113435 6020801 := bstep (se 2 (by rfl) ⟨2257800, by rfl⟩ : syracuseStep 6020801 = 4515601) B4515601
theorem B4013867 : Blo 2113435 4013867 := bstep (se 1 (by rfl) ⟨3010400, by rfl⟩ : syracuseStep 4013867 = 6020801) B6020801
theorem B2675911 : Blo 2113435 2675911 := bstep (se 1 (by rfl) ⟨2006933, by rfl⟩ : syracuseStep 2675911 = 4013867) B4013867
theorem B3567881 : Blo 2113435 3567881 := bstep (se 2 (by rfl) ⟨1337955, by rfl⟩ : syracuseStep 3567881 = 2675911) B2675911
theorem B2378587 : Blo 2113435 2378587 := bstep (se 1 (by rfl) ⟨1783940, by rfl⟩ : syracuseStep 2378587 = 3567881) B3567881
theorem B3171449 : Blo 2113435 3171449 := bstep (se 2 (by rfl) ⟨1189293, by rfl⟩ : syracuseStep 3171449 = 2378587) B2378587
theorem B2114299 : Blo 2113435 2114299 := bstep (se 1 (by rfl) ⟨1585724, by rfl⟩ : syracuseStep 2114299 = 3171449) B3171449
theorem B2712425 : Blo 2113435 2712425 := bbase (se 2 (by rfl) ⟨1017159, by rfl⟩ : syracuseStep 2712425 = 2034319) (by norm_num)
theorem B7233133 : Blo 2113435 7233133 := bstep (se 3 (by rfl) ⟨1356212, by rfl⟩ : syracuseStep 7233133 = 2712425) B2712425
theorem B9644177 : Blo 2113435 9644177 := bstep (se 2 (by rfl) ⟨3616566, by rfl⟩ : syracuseStep 9644177 = 7233133) B7233133
theorem B6429451 : Blo 2113435 6429451 := bstep (se 1 (by rfl) ⟨4822088, by rfl⟩ : syracuseStep 6429451 = 9644177) B9644177
theorem B8572601 : Blo 2113435 8572601 := bstep (se 2 (by rfl) ⟨3214725, by rfl⟩ : syracuseStep 8572601 = 6429451) B6429451
theorem B5715067 : Blo 2113435 5715067 := bstep (se 1 (by rfl) ⟨4286300, by rfl⟩ : syracuseStep 5715067 = 8572601) B8572601
theorem B7620089 : Blo 2113435 7620089 := bstep (se 2 (by rfl) ⟨2857533, by rfl⟩ : syracuseStep 7620089 = 5715067) B5715067
theorem B20320237 : Blo 2113435 20320237 := bstep (se 3 (by rfl) ⟨3810044, by rfl⟩ : syracuseStep 20320237 = 7620089) B7620089
theorem B27093649 : Blo 2113435 27093649 := bstep (se 2 (by rfl) ⟨10160118, by rfl⟩ : syracuseStep 27093649 = 20320237) B20320237
theorem B36124865 : Blo 2113435 36124865 := bstep (se 2 (by rfl) ⟨13546824, by rfl⟩ : syracuseStep 36124865 = 27093649) B27093649
theorem B24083243 : Blo 2113435 24083243 := bstep (se 1 (by rfl) ⟨18062432, by rfl⟩ : syracuseStep 24083243 = 36124865) B36124865
theorem B16055495 : Blo 2113435 16055495 := bstep (se 1 (by rfl) ⟨12041621, by rfl⟩ : syracuseStep 16055495 = 24083243) B24083243
theorem B10703663 : Blo 2113435 10703663 := bstep (se 1 (by rfl) ⟨8027747, by rfl⟩ : syracuseStep 10703663 = 16055495) B16055495
theorem B7135775 : Blo 2113435 7135775 := bstep (se 1 (by rfl) ⟨5351831, by rfl⟩ : syracuseStep 7135775 = 10703663) B10703663
theorem B4757183 : Blo 2113435 4757183 := bstep (se 1 (by rfl) ⟨3567887, by rfl⟩ : syracuseStep 4757183 = 7135775) B7135775
theorem B3171455 : Blo 2113435 3171455 := bstep (se 1 (by rfl) ⟨2378591, by rfl⟩ : syracuseStep 3171455 = 4757183) B4757183
theorem B2114303 : Blo 2113435 2114303 := bstep (se 1 (by rfl) ⟨1585727, by rfl⟩ : syracuseStep 2114303 = 3171455) B3171455
theorem B3171461 : Blo 2113435 3171461 := bbase (se 4 (by rfl) ⟨297324, by rfl⟩ : syracuseStep 3171461 = 594649) (by norm_num)
theorem B2114307 : Blo 2113435 2114307 := bstep (se 1 (by rfl) ⟨1585730, by rfl⟩ : syracuseStep 2114307 = 3171461) B3171461
theorem B3567901 : Blo 2113435 3567901 := bbase (se 3 (by rfl) ⟨668981, by rfl⟩ : syracuseStep 3567901 = 1337963) (by norm_num)
theorem B4757201 : Blo 2113435 4757201 := bstep (se 2 (by rfl) ⟨1783950, by rfl⟩ : syracuseStep 4757201 = 3567901) B3567901
theorem B3171467 : Blo 2113435 3171467 := bstep (se 1 (by rfl) ⟨2378600, by rfl⟩ : syracuseStep 3171467 = 4757201) B4757201
theorem B2114311 : Blo 2113435 2114311 := bstep (se 1 (by rfl) ⟨1585733, by rfl⟩ : syracuseStep 2114311 = 3171467) B3171467
theorem B2378605 : Blo 2113435 2378605 := bbase (se 3 (by rfl) ⟨445988, by rfl⟩ : syracuseStep 2378605 = 891977) (by norm_num)
theorem B3171473 : Blo 2113435 3171473 := bstep (se 2 (by rfl) ⟨1189302, by rfl⟩ : syracuseStep 3171473 = 2378605) B2378605
theorem B2114315 : Blo 2113435 2114315 := bstep (se 1 (by rfl) ⟨1585736, by rfl⟩ : syracuseStep 2114315 = 3171473) B3171473
theorem B7135829 : Blo 2113435 7135829 := bbase (se 8 (by rfl) ⟨41811, by rfl⟩ : syracuseStep 7135829 = 83623) (by norm_num)
theorem B4757219 : Blo 2113435 4757219 := bstep (se 1 (by rfl) ⟨3567914, by rfl⟩ : syracuseStep 4757219 = 7135829) B7135829
theorem B3171479 : Blo 2113435 3171479 := bstep (se 1 (by rfl) ⟨2378609, by rfl⟩ : syracuseStep 3171479 = 4757219) B4757219
theorem B2114319 : Blo 2113435 2114319 := bstep (se 1 (by rfl) ⟨1585739, by rfl⟩ : syracuseStep 2114319 = 3171479) B3171479
theorem B3171485 : Blo 2113435 3171485 := bbase (se 3 (by rfl) ⟨594653, by rfl⟩ : syracuseStep 3171485 = 1189307) (by norm_num)
theorem B2114323 : Blo 2113435 2114323 := bstep (se 1 (by rfl) ⟨1585742, by rfl⟩ : syracuseStep 2114323 = 3171485) B3171485
theorem B4757237 : Blo 2113435 4757237 := bbase (se 5 (by rfl) ⟨222995, by rfl⟩ : syracuseStep 4757237 = 445991) (by norm_num)
theorem B3171491 : Blo 2113435 3171491 := bstep (se 1 (by rfl) ⟨2378618, by rfl⟩ : syracuseStep 3171491 = 4757237) B4757237
theorem B2114327 : Blo 2113435 2114327 := bstep (se 1 (by rfl) ⟨1585745, by rfl⟩ : syracuseStep 2114327 = 3171491) B3171491
theorem B20088917 : Blo 2113435 20088917 := bbase (se 8 (by rfl) ⟨117708, by rfl⟩ : syracuseStep 20088917 = 235417) (by norm_num)
theorem B13392611 : Blo 2113435 13392611 := bstep (se 1 (by rfl) ⟨10044458, by rfl⟩ : syracuseStep 13392611 = 20088917) B20088917
theorem B8928407 : Blo 2113435 8928407 := bstep (se 1 (by rfl) ⟨6696305, by rfl⟩ : syracuseStep 8928407 = 13392611) B13392611
theorem B5952271 : Blo 2113435 5952271 := bstep (se 1 (by rfl) ⟨4464203, by rfl⟩ : syracuseStep 5952271 = 8928407) B8928407
theorem B7936361 : Blo 2113435 7936361 := bstep (se 2 (by rfl) ⟨2976135, by rfl⟩ : syracuseStep 7936361 = 5952271) B5952271
theorem B84654517 : Blo 2113435 84654517 := bstep (se 5 (by rfl) ⟨3968180, by rfl⟩ : syracuseStep 84654517 = 7936361) B7936361
theorem B112872689 : Blo 2113435 112872689 := bstep (se 2 (by rfl) ⟨42327258, by rfl⟩ : syracuseStep 112872689 = 84654517) B84654517
theorem B75248459 : Blo 2113435 75248459 := bstep (se 1 (by rfl) ⟨56436344, by rfl⟩ : syracuseStep 75248459 = 112872689) B112872689
theorem B50165639 : Blo 2113435 50165639 := bstep (se 1 (by rfl) ⟨37624229, by rfl⟩ : syracuseStep 50165639 = 75248459) B75248459
theorem B33443759 : Blo 2113435 33443759 := bstep (se 1 (by rfl) ⟨25082819, by rfl⟩ : syracuseStep 33443759 = 50165639) B50165639
theorem B22295839 : Blo 2113435 22295839 := bstep (se 1 (by rfl) ⟨16721879, by rfl⟩ : syracuseStep 22295839 = 33443759) B33443759
theorem B29727785 : Blo 2113435 29727785 := bstep (se 2 (by rfl) ⟨11147919, by rfl⟩ : syracuseStep 29727785 = 22295839) B22295839
theorem B19818523 : Blo 2113435 19818523 := bstep (se 1 (by rfl) ⟨14863892, by rfl⟩ : syracuseStep 19818523 = 29727785) B29727785
theorem B105698789 : Blo 2113435 105698789 := bstep (se 4 (by rfl) ⟨9909261, by rfl⟩ : syracuseStep 105698789 = 19818523) B19818523
theorem B70465859 : Blo 2113435 70465859 := bstep (se 1 (by rfl) ⟨52849394, by rfl⟩ : syracuseStep 70465859 = 105698789) B105698789
theorem B46977239 : Blo 2113435 46977239 := bstep (se 1 (by rfl) ⟨35232929, by rfl⟩ : syracuseStep 46977239 = 70465859) B70465859
theorem B31318159 : Blo 2113435 31318159 := bstep (se 1 (by rfl) ⟨23488619, by rfl⟩ : syracuseStep 31318159 = 46977239) B46977239
theorem B41757545 : Blo 2113435 41757545 := bstep (se 2 (by rfl) ⟨15659079, by rfl⟩ : syracuseStep 41757545 = 31318159) B31318159
theorem B111353453 : Blo 2113435 111353453 := bstep (se 3 (by rfl) ⟨20878772, by rfl⟩ : syracuseStep 111353453 = 41757545) B41757545
theorem B74235635 : Blo 2113435 74235635 := bstep (se 1 (by rfl) ⟨55676726, by rfl⟩ : syracuseStep 74235635 = 111353453) B111353453
theorem B49490423 : Blo 2113435 49490423 := bstep (se 1 (by rfl) ⟨37117817, by rfl⟩ : syracuseStep 49490423 = 74235635) B74235635
theorem B32993615 : Blo 2113435 32993615 := bstep (se 1 (by rfl) ⟨24745211, by rfl⟩ : syracuseStep 32993615 = 49490423) B49490423
theorem B87982973 : Blo 2113435 87982973 := bstep (se 3 (by rfl) ⟨16496807, by rfl⟩ : syracuseStep 87982973 = 32993615) B32993615
theorem B58655315 : Blo 2113435 58655315 := bstep (se 1 (by rfl) ⟨43991486, by rfl⟩ : syracuseStep 58655315 = 87982973) B87982973
theorem B39103543 : Blo 2113435 39103543 := bstep (se 1 (by rfl) ⟨29327657, by rfl⟩ : syracuseStep 39103543 = 58655315) B58655315
theorem B208552229 : Blo 2113435 208552229 := bstep (se 4 (by rfl) ⟨19551771, by rfl⟩ : syracuseStep 208552229 = 39103543) B39103543
theorem B139034819 : Blo 2113435 139034819 := bstep (se 1 (by rfl) ⟨104276114, by rfl⟩ : syracuseStep 139034819 = 208552229) B208552229
theorem B92689879 : Blo 2113435 92689879 := bstep (se 1 (by rfl) ⟨69517409, by rfl⟩ : syracuseStep 92689879 = 139034819) B139034819
theorem B123586505 : Blo 2113435 123586505 := bstep (se 2 (by rfl) ⟨46344939, by rfl⟩ : syracuseStep 123586505 = 92689879) B92689879
theorem B82391003 : Blo 2113435 82391003 := bstep (se 1 (by rfl) ⟨61793252, by rfl⟩ : syracuseStep 82391003 = 123586505) B123586505
theorem B54927335 : Blo 2113435 54927335 := bstep (se 1 (by rfl) ⟨41195501, by rfl⟩ : syracuseStep 54927335 = 82391003) B82391003
theorem B36618223 : Blo 2113435 36618223 := bstep (se 1 (by rfl) ⟨27463667, by rfl⟩ : syracuseStep 36618223 = 54927335) B54927335
theorem B48824297 : Blo 2113435 48824297 := bstep (se 2 (by rfl) ⟨18309111, by rfl⟩ : syracuseStep 48824297 = 36618223) B36618223
theorem B32549531 : Blo 2113435 32549531 := bstep (se 1 (by rfl) ⟨24412148, by rfl⟩ : syracuseStep 32549531 = 48824297) B48824297
theorem B86798749 : Blo 2113435 86798749 := bstep (se 3 (by rfl) ⟨16274765, by rfl⟩ : syracuseStep 86798749 = 32549531) B32549531
theorem B115731665 : Blo 2113435 115731665 := bstep (se 2 (by rfl) ⟨43399374, by rfl⟩ : syracuseStep 115731665 = 86798749) B86798749
theorem B77154443 : Blo 2113435 77154443 := bstep (se 1 (by rfl) ⟨57865832, by rfl⟩ : syracuseStep 77154443 = 115731665) B115731665
theorem B51436295 : Blo 2113435 51436295 := bstep (se 1 (by rfl) ⟨38577221, by rfl⟩ : syracuseStep 51436295 = 77154443) B77154443
theorem B34290863 : Blo 2113435 34290863 := bstep (se 1 (by rfl) ⟨25718147, by rfl⟩ : syracuseStep 34290863 = 51436295) B51436295
theorem B22860575 : Blo 2113435 22860575 := bstep (se 1 (by rfl) ⟨17145431, by rfl⟩ : syracuseStep 22860575 = 34290863) B34290863
theorem B15240383 : Blo 2113435 15240383 := bstep (se 1 (by rfl) ⟨11430287, by rfl⟩ : syracuseStep 15240383 = 22860575) B22860575
theorem B10160255 : Blo 2113435 10160255 := bstep (se 1 (by rfl) ⟨7620191, by rfl⟩ : syracuseStep 10160255 = 15240383) B15240383
theorem B27094013 : Blo 2113435 27094013 := bstep (se 3 (by rfl) ⟨5080127, by rfl⟩ : syracuseStep 27094013 = 10160255) B10160255
theorem B18062675 : Blo 2113435 18062675 := bstep (se 1 (by rfl) ⟨13547006, by rfl⟩ : syracuseStep 18062675 = 27094013) B27094013
theorem B12041783 : Blo 2113435 12041783 := bstep (se 1 (by rfl) ⟨9031337, by rfl⟩ : syracuseStep 12041783 = 18062675) B18062675
theorem B8027855 : Blo 2113435 8027855 := bstep (se 1 (by rfl) ⟨6020891, by rfl⟩ : syracuseStep 8027855 = 12041783) B12041783
theorem B5351903 : Blo 2113435 5351903 := bstep (se 1 (by rfl) ⟨4013927, by rfl⟩ : syracuseStep 5351903 = 8027855) B8027855
theorem B3567935 : Blo 2113435 3567935 := bstep (se 1 (by rfl) ⟨2675951, by rfl⟩ : syracuseStep 3567935 = 5351903) B5351903
theorem B2378623 : Blo 2113435 2378623 := bstep (se 1 (by rfl) ⟨1783967, by rfl⟩ : syracuseStep 2378623 = 3567935) B3567935
theorem B3171497 : Blo 2113435 3171497 := bstep (se 2 (by rfl) ⟨1189311, by rfl⟩ : syracuseStep 3171497 = 2378623) B2378623
theorem B2114331 : Blo 2113435 2114331 := bstep (se 1 (by rfl) ⟨1585748, by rfl⟩ : syracuseStep 2114331 = 3171497) B3171497
theorem B4515677 : Blo 2113435 4515677 := bbase (se 3 (by rfl) ⟨846689, by rfl⟩ : syracuseStep 4515677 = 1693379) (by norm_num)
theorem B3010451 : Blo 2113435 3010451 := bstep (se 1 (by rfl) ⟨2257838, by rfl⟩ : syracuseStep 3010451 = 4515677) B4515677
theorem B8027869 : Blo 2113435 8027869 := bstep (se 3 (by rfl) ⟨1505225, by rfl⟩ : syracuseStep 8027869 = 3010451) B3010451
theorem B10703825 : Blo 2113435 10703825 := bstep (se 2 (by rfl) ⟨4013934, by rfl⟩ : syracuseStep 10703825 = 8027869) B8027869
theorem B7135883 : Blo 2113435 7135883 := bstep (se 1 (by rfl) ⟨5351912, by rfl⟩ : syracuseStep 7135883 = 10703825) B10703825
theorem B4757255 : Blo 2113435 4757255 := bstep (se 1 (by rfl) ⟨3567941, by rfl⟩ : syracuseStep 4757255 = 7135883) B7135883
theorem B3171503 : Blo 2113435 3171503 := bstep (se 1 (by rfl) ⟨2378627, by rfl⟩ : syracuseStep 3171503 = 4757255) B4757255
theorem B2114335 : Blo 2113435 2114335 := bstep (se 1 (by rfl) ⟨1585751, by rfl⟩ : syracuseStep 2114335 = 3171503) B3171503
theorem B3171509 : Blo 2113435 3171509 := bbase (se 5 (by rfl) ⟨148664, by rfl⟩ : syracuseStep 3171509 = 297329) (by norm_num)
theorem B2114339 : Blo 2113435 2114339 := bstep (se 1 (by rfl) ⟨1585754, by rfl⟩ : syracuseStep 2114339 = 3171509) B3171509
theorem B5351933 : Blo 2113435 5351933 := bbase (se 3 (by rfl) ⟨1003487, by rfl⟩ : syracuseStep 5351933 = 2006975) (by norm_num)
theorem B3567955 : Blo 2113435 3567955 := bstep (se 1 (by rfl) ⟨2675966, by rfl⟩ : syracuseStep 3567955 = 5351933) B5351933
theorem B4757273 : Blo 2113435 4757273 := bstep (se 2 (by rfl) ⟨1783977, by rfl⟩ : syracuseStep 4757273 = 3567955) B3567955
theorem B3171515 : Blo 2113435 3171515 := bstep (se 1 (by rfl) ⟨2378636, by rfl⟩ : syracuseStep 3171515 = 4757273) B4757273
theorem B2114343 : Blo 2113435 2114343 := bstep (se 1 (by rfl) ⟨1585757, by rfl⟩ : syracuseStep 2114343 = 3171515) B3171515
theorem B2378641 : Blo 2113435 2378641 := bbase (se 2 (by rfl) ⟨891990, by rfl⟩ : syracuseStep 2378641 = 1783981) (by norm_num)
theorem B3171521 : Blo 2113435 3171521 := bstep (se 2 (by rfl) ⟨1189320, by rfl⟩ : syracuseStep 3171521 = 2378641) B2378641
theorem B2114347 : Blo 2113435 2114347 := bstep (se 1 (by rfl) ⟨1585760, by rfl⟩ : syracuseStep 2114347 = 3171521) B3171521
theorem B4013965 : Blo 2113435 4013965 := bbase (se 3 (by rfl) ⟨752618, by rfl⟩ : syracuseStep 4013965 = 1505237) (by norm_num)
theorem B5351953 : Blo 2113435 5351953 := bstep (se 2 (by rfl) ⟨2006982, by rfl⟩ : syracuseStep 5351953 = 4013965) B4013965
theorem B7135937 : Blo 2113435 7135937 := bstep (se 2 (by rfl) ⟨2675976, by rfl⟩ : syracuseStep 7135937 = 5351953) B5351953
theorem B4757291 : Blo 2113435 4757291 := bstep (se 1 (by rfl) ⟨3567968, by rfl⟩ : syracuseStep 4757291 = 7135937) B7135937
theorem B3171527 : Blo 2113435 3171527 := bstep (se 1 (by rfl) ⟨2378645, by rfl⟩ : syracuseStep 3171527 = 4757291) B4757291
theorem B2114351 : Blo 2113435 2114351 := bstep (se 1 (by rfl) ⟨1585763, by rfl⟩ : syracuseStep 2114351 = 3171527) B3171527
theorem B3171533 : Blo 2113435 3171533 := bbase (se 3 (by rfl) ⟨594662, by rfl⟩ : syracuseStep 3171533 = 1189325) (by norm_num)
theorem B2114355 : Blo 2113435 2114355 := bstep (se 1 (by rfl) ⟨1585766, by rfl⟩ : syracuseStep 2114355 = 3171533) B3171533
theorem B4757309 : Blo 2113435 4757309 := bbase (se 3 (by rfl) ⟨891995, by rfl⟩ : syracuseStep 4757309 = 1783991) (by norm_num)
theorem B3171539 : Blo 2113435 3171539 := bstep (se 1 (by rfl) ⟨2378654, by rfl⟩ : syracuseStep 3171539 = 4757309) B4757309
theorem B2114359 : Blo 2113435 2114359 := bstep (se 1 (by rfl) ⟨1585769, by rfl⟩ : syracuseStep 2114359 = 3171539) B3171539
theorem B3567989 : Blo 2113435 3567989 := bbase (se 5 (by rfl) ⟨167249, by rfl⟩ : syracuseStep 3567989 = 334499) (by norm_num)
theorem B2378659 : Blo 2113435 2378659 := bstep (se 1 (by rfl) ⟨1783994, by rfl⟩ : syracuseStep 2378659 = 3567989) B3567989
theorem B3171545 : Blo 2113435 3171545 := bstep (se 2 (by rfl) ⟨1189329, by rfl⟩ : syracuseStep 3171545 = 2378659) B2378659
theorem B2114363 : Blo 2113435 2114363 := bstep (se 1 (by rfl) ⟨1585772, by rfl⟩ : syracuseStep 2114363 = 3171545) B3171545
theorem B2857621 : Blo 2113435 2857621 := bbase (se 6 (by rfl) ⟨66975, by rfl⟩ : syracuseStep 2857621 = 133951) (by norm_num)
theorem B3810161 : Blo 2113435 3810161 := bstep (se 2 (by rfl) ⟨1428810, by rfl⟩ : syracuseStep 3810161 = 2857621) B2857621
theorem B2540107 : Blo 2113435 2540107 := bstep (se 1 (by rfl) ⟨1905080, by rfl⟩ : syracuseStep 2540107 = 3810161) B3810161
theorem B3386809 : Blo 2113435 3386809 := bstep (se 2 (by rfl) ⟨1270053, by rfl⟩ : syracuseStep 3386809 = 2540107) B2540107
theorem B4515745 : Blo 2113435 4515745 := bstep (se 2 (by rfl) ⟨1693404, by rfl⟩ : syracuseStep 4515745 = 3386809) B3386809
theorem B6020993 : Blo 2113435 6020993 := bstep (se 2 (by rfl) ⟨2257872, by rfl⟩ : syracuseStep 6020993 = 4515745) B4515745
theorem B16055981 : Blo 2113435 16055981 := bstep (se 3 (by rfl) ⟨3010496, by rfl⟩ : syracuseStep 16055981 = 6020993) B6020993
theorem B10703987 : Blo 2113435 10703987 := bstep (se 1 (by rfl) ⟨8027990, by rfl⟩ : syracuseStep 10703987 = 16055981) B16055981
theorem B7135991 : Blo 2113435 7135991 := bstep (se 1 (by rfl) ⟨5351993, by rfl⟩ : syracuseStep 7135991 = 10703987) B10703987
theorem B4757327 : Blo 2113435 4757327 := bstep (se 1 (by rfl) ⟨3567995, by rfl⟩ : syracuseStep 4757327 = 7135991) B7135991
theorem B3171551 : Blo 2113435 3171551 := bstep (se 1 (by rfl) ⟨2378663, by rfl⟩ : syracuseStep 3171551 = 4757327) B4757327
theorem B2114367 : Blo 2113435 2114367 := bstep (se 1 (by rfl) ⟨1585775, by rfl⟩ : syracuseStep 2114367 = 3171551) B3171551
theorem B3171557 : Blo 2113435 3171557 := bbase (se 4 (by rfl) ⟨297333, by rfl⟩ : syracuseStep 3171557 = 594667) (by norm_num)
theorem B2114371 : Blo 2113435 2114371 := bstep (se 1 (by rfl) ⟨1585778, by rfl⟩ : syracuseStep 2114371 = 3171557) B3171557
theorem B2540117 : Blo 2113435 2540117 := bbase (se 8 (by rfl) ⟨14883, by rfl⟩ : syracuseStep 2540117 = 29767) (by norm_num)
theorem B6773645 : Blo 2113435 6773645 := bstep (se 3 (by rfl) ⟨1270058, by rfl⟩ : syracuseStep 6773645 = 2540117) B2540117
theorem B4515763 : Blo 2113435 4515763 := bstep (se 1 (by rfl) ⟨3386822, by rfl⟩ : syracuseStep 4515763 = 6773645) B6773645
theorem B6021017 : Blo 2113435 6021017 := bstep (se 2 (by rfl) ⟨2257881, by rfl⟩ : syracuseStep 6021017 = 4515763) B4515763
theorem B4014011 : Blo 2113435 4014011 := bstep (se 1 (by rfl) ⟨3010508, by rfl⟩ : syracuseStep 4014011 = 6021017) B6021017
theorem B2676007 : Blo 2113435 2676007 := bstep (se 1 (by rfl) ⟨2007005, by rfl⟩ : syracuseStep 2676007 = 4014011) B4014011
theorem B3568009 : Blo 2113435 3568009 := bstep (se 2 (by rfl) ⟨1338003, by rfl⟩ : syracuseStep 3568009 = 2676007) B2676007
theorem B4757345 : Blo 2113435 4757345 := bstep (se 2 (by rfl) ⟨1784004, by rfl⟩ : syracuseStep 4757345 = 3568009) B3568009
theorem B3171563 : Blo 2113435 3171563 := bstep (se 1 (by rfl) ⟨2378672, by rfl⟩ : syracuseStep 3171563 = 4757345) B4757345
theorem B2114375 : Blo 2113435 2114375 := bstep (se 1 (by rfl) ⟨1585781, by rfl⟩ : syracuseStep 2114375 = 3171563) B3171563
theorem B2378677 : Blo 2113435 2378677 := bbase (se 5 (by rfl) ⟨111500, by rfl⟩ : syracuseStep 2378677 = 223001) (by norm_num)
theorem B3171569 : Blo 2113435 3171569 := bstep (se 2 (by rfl) ⟨1189338, by rfl⟩ : syracuseStep 3171569 = 2378677) B2378677
theorem B2114379 : Blo 2113435 2114379 := bstep (se 1 (by rfl) ⟨1585784, by rfl⟩ : syracuseStep 2114379 = 3171569) B3171569
theorem B2676017 : Blo 2113435 2676017 := bbase (se 2 (by rfl) ⟨1003506, by rfl⟩ : syracuseStep 2676017 = 2007013) (by norm_num)
theorem B7136045 : Blo 2113435 7136045 := bstep (se 3 (by rfl) ⟨1338008, by rfl⟩ : syracuseStep 7136045 = 2676017) B2676017
theorem B4757363 : Blo 2113435 4757363 := bstep (se 1 (by rfl) ⟨3568022, by rfl⟩ : syracuseStep 4757363 = 7136045) B7136045
theorem B3171575 : Blo 2113435 3171575 := bstep (se 1 (by rfl) ⟨2378681, by rfl⟩ : syracuseStep 3171575 = 4757363) B4757363
theorem B2114383 : Blo 2113435 2114383 := bstep (se 1 (by rfl) ⟨1585787, by rfl⟩ : syracuseStep 2114383 = 3171575) B3171575
theorem B3171581 : Blo 2113435 3171581 := bbase (se 3 (by rfl) ⟨594671, by rfl⟩ : syracuseStep 3171581 = 1189343) (by norm_num)
theorem B2114387 : Blo 2113435 2114387 := bstep (se 1 (by rfl) ⟨1585790, by rfl⟩ : syracuseStep 2114387 = 3171581) B3171581
theorem B4757381 : Blo 2113435 4757381 := bbase (se 4 (by rfl) ⟨446004, by rfl⟩ : syracuseStep 4757381 = 892009) (by norm_num)
theorem B3171587 : Blo 2113435 3171587 := bstep (se 1 (by rfl) ⟨2378690, by rfl⟩ : syracuseStep 3171587 = 4757381) B4757381
theorem B2114391 : Blo 2113435 2114391 := bstep (se 1 (by rfl) ⟨1585793, by rfl⟩ : syracuseStep 2114391 = 3171587) B3171587
theorem B4822301 : Blo 2113435 4822301 := bbase (se 3 (by rfl) ⟨904181, by rfl⟩ : syracuseStep 4822301 = 1808363) (by norm_num)
theorem B12859469 : Blo 2113435 12859469 := bstep (se 3 (by rfl) ⟨2411150, by rfl⟩ : syracuseStep 12859469 = 4822301) B4822301
theorem B8572979 : Blo 2113435 8572979 := bstep (se 1 (by rfl) ⟨6429734, by rfl⟩ : syracuseStep 8572979 = 12859469) B12859469
theorem B5715319 : Blo 2113435 5715319 := bstep (se 1 (by rfl) ⟨4286489, by rfl⟩ : syracuseStep 5715319 = 8572979) B8572979
theorem B7620425 : Blo 2113435 7620425 := bstep (se 2 (by rfl) ⟨2857659, by rfl⟩ : syracuseStep 7620425 = 5715319) B5715319
theorem B5080283 : Blo 2113435 5080283 := bstep (se 1 (by rfl) ⟨3810212, by rfl⟩ : syracuseStep 5080283 = 7620425) B7620425
theorem B3386855 : Blo 2113435 3386855 := bstep (se 1 (by rfl) ⟨2540141, by rfl⟩ : syracuseStep 3386855 = 5080283) B5080283
theorem B2257903 : Blo 2113435 2257903 := bstep (se 1 (by rfl) ⟨1693427, by rfl⟩ : syracuseStep 2257903 = 3386855) B3386855
theorem B3010537 : Blo 2113435 3010537 := bstep (se 2 (by rfl) ⟨1128951, by rfl⟩ : syracuseStep 3010537 = 2257903) B2257903
theorem B4014049 : Blo 2113435 4014049 := bstep (se 2 (by rfl) ⟨1505268, by rfl⟩ : syracuseStep 4014049 = 3010537) B3010537
theorem B5352065 : Blo 2113435 5352065 := bstep (se 2 (by rfl) ⟨2007024, by rfl⟩ : syracuseStep 5352065 = 4014049) B4014049
theorem B3568043 : Blo 2113435 3568043 := bstep (se 1 (by rfl) ⟨2676032, by rfl⟩ : syracuseStep 3568043 = 5352065) B5352065
theorem B2378695 : Blo 2113435 2378695 := bstep (se 1 (by rfl) ⟨1784021, by rfl⟩ : syracuseStep 2378695 = 3568043) B3568043
theorem B3171593 : Blo 2113435 3171593 := bstep (se 2 (by rfl) ⟨1189347, by rfl⟩ : syracuseStep 3171593 = 2378695) B2378695
theorem B2114395 : Blo 2113435 2114395 := bstep (se 1 (by rfl) ⟨1585796, by rfl⟩ : syracuseStep 2114395 = 3171593) B3171593
theorem B10704149 : Blo 2113435 10704149 := bbase (se 6 (by rfl) ⟨250878, by rfl⟩ : syracuseStep 10704149 = 501757) (by norm_num)
theorem B7136099 : Blo 2113435 7136099 := bstep (se 1 (by rfl) ⟨5352074, by rfl⟩ : syracuseStep 7136099 = 10704149) B10704149
theorem B4757399 : Blo 2113435 4757399 := bstep (se 1 (by rfl) ⟨3568049, by rfl⟩ : syracuseStep 4757399 = 7136099) B7136099
theorem B3171599 : Blo 2113435 3171599 := bstep (se 1 (by rfl) ⟨2378699, by rfl⟩ : syracuseStep 3171599 = 4757399) B4757399
theorem B2114399 : Blo 2113435 2114399 := bstep (se 1 (by rfl) ⟨1585799, by rfl⟩ : syracuseStep 2114399 = 3171599) B3171599
theorem B3171605 : Blo 2113435 3171605 := bbase (se 6 (by rfl) ⟨74334, by rfl⟩ : syracuseStep 3171605 = 148669) (by norm_num)
theorem B2114403 : Blo 2113435 2114403 := bstep (se 1 (by rfl) ⟨1585802, by rfl⟩ : syracuseStep 2114403 = 3171605) B3171605
theorem B9154885 : Blo 2113435 9154885 := bbase (se 4 (by rfl) ⟨858270, by rfl⟩ : syracuseStep 9154885 = 1716541) (by norm_num)
theorem B12206513 : Blo 2113435 12206513 := bstep (se 2 (by rfl) ⟨4577442, by rfl⟩ : syracuseStep 12206513 = 9154885) B9154885
theorem B8137675 : Blo 2113435 8137675 := bstep (se 1 (by rfl) ⟨6103256, by rfl⟩ : syracuseStep 8137675 = 12206513) B12206513
theorem B43400933 : Blo 2113435 43400933 := bstep (se 4 (by rfl) ⟨4068837, by rfl⟩ : syracuseStep 43400933 = 8137675) B8137675
theorem B28933955 : Blo 2113435 28933955 := bstep (se 1 (by rfl) ⟨21700466, by rfl⟩ : syracuseStep 28933955 = 43400933) B43400933
theorem B19289303 : Blo 2113435 19289303 := bstep (se 1 (by rfl) ⟨14466977, by rfl⟩ : syracuseStep 19289303 = 28933955) B28933955
theorem B12859535 : Blo 2113435 12859535 := bstep (se 1 (by rfl) ⟨9644651, by rfl⟩ : syracuseStep 12859535 = 19289303) B19289303
theorem B8573023 : Blo 2113435 8573023 := bstep (se 1 (by rfl) ⟨6429767, by rfl⟩ : syracuseStep 8573023 = 12859535) B12859535
theorem B45722789 : Blo 2113435 45722789 := bstep (se 4 (by rfl) ⟨4286511, by rfl⟩ : syracuseStep 45722789 = 8573023) B8573023
theorem B30481859 : Blo 2113435 30481859 := bstep (se 1 (by rfl) ⟨22861394, by rfl⟩ : syracuseStep 30481859 = 45722789) B45722789
theorem B20321239 : Blo 2113435 20321239 := bstep (se 1 (by rfl) ⟨15240929, by rfl⟩ : syracuseStep 20321239 = 30481859) B30481859
theorem B27094985 : Blo 2113435 27094985 := bstep (se 2 (by rfl) ⟨10160619, by rfl⟩ : syracuseStep 27094985 = 20321239) B20321239
theorem B18063323 : Blo 2113435 18063323 := bstep (se 1 (by rfl) ⟨13547492, by rfl⟩ : syracuseStep 18063323 = 27094985) B27094985
theorem B12042215 : Blo 2113435 12042215 := bstep (se 1 (by rfl) ⟨9031661, by rfl⟩ : syracuseStep 12042215 = 18063323) B18063323
theorem B8028143 : Blo 2113435 8028143 := bstep (se 1 (by rfl) ⟨6021107, by rfl⟩ : syracuseStep 8028143 = 12042215) B12042215
theorem B5352095 : Blo 2113435 5352095 := bstep (se 1 (by rfl) ⟨4014071, by rfl⟩ : syracuseStep 5352095 = 8028143) B8028143
theorem B3568063 : Blo 2113435 3568063 := bstep (se 1 (by rfl) ⟨2676047, by rfl⟩ : syracuseStep 3568063 = 5352095) B5352095
theorem B4757417 : Blo 2113435 4757417 := bstep (se 2 (by rfl) ⟨1784031, by rfl⟩ : syracuseStep 4757417 = 3568063) B3568063
theorem B3171611 : Blo 2113435 3171611 := bstep (se 1 (by rfl) ⟨2378708, by rfl⟩ : syracuseStep 3171611 = 4757417) B4757417
theorem B2114407 : Blo 2113435 2114407 := bstep (se 1 (by rfl) ⟨1585805, by rfl⟩ : syracuseStep 2114407 = 3171611) B3171611
theorem B2378713 : Blo 2113435 2378713 := bbase (se 2 (by rfl) ⟨892017, by rfl⟩ : syracuseStep 2378713 = 1784035) (by norm_num)
theorem B3171617 : Blo 2113435 3171617 := bstep (se 2 (by rfl) ⟨1189356, by rfl⟩ : syracuseStep 3171617 = 2378713) B2378713
theorem B2114411 : Blo 2113435 2114411 := bstep (se 1 (by rfl) ⟨1585808, by rfl⟩ : syracuseStep 2114411 = 3171617) B3171617
theorem B3010565 : Blo 2113435 3010565 := bbase (se 4 (by rfl) ⟨282240, by rfl⟩ : syracuseStep 3010565 = 564481) (by norm_num)
theorem B8028173 : Blo 2113435 8028173 := bstep (se 3 (by rfl) ⟨1505282, by rfl⟩ : syracuseStep 8028173 = 3010565) B3010565
theorem B5352115 : Blo 2113435 5352115 := bstep (se 1 (by rfl) ⟨4014086, by rfl⟩ : syracuseStep 5352115 = 8028173) B8028173
theorem B7136153 : Blo 2113435 7136153 := bstep (se 2 (by rfl) ⟨2676057, by rfl⟩ : syracuseStep 7136153 = 5352115) B5352115
theorem B4757435 : Blo 2113435 4757435 := bstep (se 1 (by rfl) ⟨3568076, by rfl⟩ : syracuseStep 4757435 = 7136153) B7136153
theorem B3171623 : Blo 2113435 3171623 := bstep (se 1 (by rfl) ⟨2378717, by rfl⟩ : syracuseStep 3171623 = 4757435) B4757435
theorem B2114415 : Blo 2113435 2114415 := bstep (se 1 (by rfl) ⟨1585811, by rfl⟩ : syracuseStep 2114415 = 3171623) B3171623
theorem B3171629 : Blo 2113435 3171629 := bbase (se 3 (by rfl) ⟨594680, by rfl⟩ : syracuseStep 3171629 = 1189361) (by norm_num)
theorem B2114419 : Blo 2113435 2114419 := bstep (se 1 (by rfl) ⟨1585814, by rfl⟩ : syracuseStep 2114419 = 3171629) B3171629
theorem B4757453 : Blo 2113435 4757453 := bbase (se 3 (by rfl) ⟨892022, by rfl⟩ : syracuseStep 4757453 = 1784045) (by norm_num)
theorem B3171635 : Blo 2113435 3171635 := bstep (se 1 (by rfl) ⟨2378726, by rfl⟩ : syracuseStep 3171635 = 4757453) B4757453
theorem B2114423 : Blo 2113435 2114423 := bstep (se 1 (by rfl) ⟨1585817, by rfl⟩ : syracuseStep 2114423 = 3171635) B3171635
theorem B2676073 : Blo 2113435 2676073 := bbase (se 2 (by rfl) ⟨1003527, by rfl⟩ : syracuseStep 2676073 = 2007055) (by norm_num)
theorem B3568097 : Blo 2113435 3568097 := bstep (se 2 (by rfl) ⟨1338036, by rfl⟩ : syracuseStep 3568097 = 2676073) B2676073
theorem B2378731 : Blo 2113435 2378731 := bstep (se 1 (by rfl) ⟨1784048, by rfl⟩ : syracuseStep 2378731 = 3568097) B3568097
theorem B3171641 : Blo 2113435 3171641 := bstep (se 2 (by rfl) ⟨1189365, by rfl⟩ : syracuseStep 3171641 = 2378731) B2378731
theorem B2114427 : Blo 2113435 2114427 := bstep (se 1 (by rfl) ⟨1585820, by rfl⟩ : syracuseStep 2114427 = 3171641) B3171641
theorem B10850357 : Blo 2113435 10850357 := bbase (se 5 (by rfl) ⟨508610, by rfl⟩ : syracuseStep 10850357 = 1017221) (by norm_num)
theorem B7233571 : Blo 2113435 7233571 := bstep (se 1 (by rfl) ⟨5425178, by rfl⟩ : syracuseStep 7233571 = 10850357) B10850357
theorem B9644761 : Blo 2113435 9644761 := bstep (se 2 (by rfl) ⟨3616785, by rfl⟩ : syracuseStep 9644761 = 7233571) B7233571
theorem B12859681 : Blo 2113435 12859681 := bstep (se 2 (by rfl) ⟨4822380, by rfl⟩ : syracuseStep 12859681 = 9644761) B9644761
theorem B17146241 : Blo 2113435 17146241 := bstep (se 2 (by rfl) ⟨6429840, by rfl⟩ : syracuseStep 17146241 = 12859681) B12859681
theorem B11430827 : Blo 2113435 11430827 := bstep (se 1 (by rfl) ⟨8573120, by rfl⟩ : syracuseStep 11430827 = 17146241) B17146241
theorem B7620551 : Blo 2113435 7620551 := bstep (se 1 (by rfl) ⟨5715413, by rfl⟩ : syracuseStep 7620551 = 11430827) B11430827
theorem B5080367 : Blo 2113435 5080367 := bstep (se 1 (by rfl) ⟨3810275, by rfl⟩ : syracuseStep 5080367 = 7620551) B7620551
theorem B13547645 : Blo 2113435 13547645 := bstep (se 3 (by rfl) ⟨2540183, by rfl⟩ : syracuseStep 13547645 = 5080367) B5080367
theorem B9031763 : Blo 2113435 9031763 := bstep (se 1 (by rfl) ⟨6773822, by rfl⟩ : syracuseStep 9031763 = 13547645) B13547645
theorem B24084701 : Blo 2113435 24084701 := bstep (se 3 (by rfl) ⟨4515881, by rfl⟩ : syracuseStep 24084701 = 9031763) B9031763
theorem B16056467 : Blo 2113435 16056467 := bstep (se 1 (by rfl) ⟨12042350, by rfl⟩ : syracuseStep 16056467 = 24084701) B24084701
theorem B10704311 : Blo 2113435 10704311 := bstep (se 1 (by rfl) ⟨8028233, by rfl⟩ : syracuseStep 10704311 = 16056467) B16056467
theorem B7136207 : Blo 2113435 7136207 := bstep (se 1 (by rfl) ⟨5352155, by rfl⟩ : syracuseStep 7136207 = 10704311) B10704311
theorem B4757471 : Blo 2113435 4757471 := bstep (se 1 (by rfl) ⟨3568103, by rfl⟩ : syracuseStep 4757471 = 7136207) B7136207
theorem B3171647 : Blo 2113435 3171647 := bstep (se 1 (by rfl) ⟨2378735, by rfl⟩ : syracuseStep 3171647 = 4757471) B4757471
theorem B2114431 : Blo 2113435 2114431 := bstep (se 1 (by rfl) ⟨1585823, by rfl⟩ : syracuseStep 2114431 = 3171647) B3171647
theorem B3171653 : Blo 2113435 3171653 := bbase (se 4 (by rfl) ⟨297342, by rfl⟩ : syracuseStep 3171653 = 594685) (by norm_num)
theorem B2114435 : Blo 2113435 2114435 := bstep (se 1 (by rfl) ⟨1585826, by rfl⟩ : syracuseStep 2114435 = 3171653) B3171653
theorem B3568117 : Blo 2113435 3568117 := bbase (se 5 (by rfl) ⟨167255, by rfl⟩ : syracuseStep 3568117 = 334511) (by norm_num)
theorem B4757489 : Blo 2113435 4757489 := bstep (se 2 (by rfl) ⟨1784058, by rfl⟩ : syracuseStep 4757489 = 3568117) B3568117
theorem B3171659 : Blo 2113435 3171659 := bstep (se 1 (by rfl) ⟨2378744, by rfl⟩ : syracuseStep 3171659 = 4757489) B4757489
theorem B2114439 : Blo 2113435 2114439 := bstep (se 1 (by rfl) ⟨1585829, by rfl⟩ : syracuseStep 2114439 = 3171659) B3171659
theorem B2378749 : Blo 2113435 2378749 := bbase (se 3 (by rfl) ⟨446015, by rfl⟩ : syracuseStep 2378749 = 892031) (by norm_num)
theorem B3171665 : Blo 2113435 3171665 := bstep (se 2 (by rfl) ⟨1189374, by rfl⟩ : syracuseStep 3171665 = 2378749) B2378749
theorem B2114443 : Blo 2113435 2114443 := bstep (se 1 (by rfl) ⟨1585832, by rfl⟩ : syracuseStep 2114443 = 3171665) B3171665
theorem B7136261 : Blo 2113435 7136261 := bbase (se 4 (by rfl) ⟨669024, by rfl⟩ : syracuseStep 7136261 = 1338049) (by norm_num)
theorem B4757507 : Blo 2113435 4757507 := bstep (se 1 (by rfl) ⟨3568130, by rfl⟩ : syracuseStep 4757507 = 7136261) B7136261
theorem B3171671 : Blo 2113435 3171671 := bstep (se 1 (by rfl) ⟨2378753, by rfl⟩ : syracuseStep 3171671 = 4757507) B4757507
theorem B2114447 : Blo 2113435 2114447 := bstep (se 1 (by rfl) ⟨1585835, by rfl⟩ : syracuseStep 2114447 = 3171671) B3171671
theorem B3171677 : Blo 2113435 3171677 := bbase (se 3 (by rfl) ⟨594689, by rfl⟩ : syracuseStep 3171677 = 1189379) (by norm_num)
theorem B2114451 : Blo 2113435 2114451 := bstep (se 1 (by rfl) ⟨1585838, by rfl⟩ : syracuseStep 2114451 = 3171677) B3171677
theorem B4757525 : Blo 2113435 4757525 := bbase (se 6 (by rfl) ⟨111504, by rfl⟩ : syracuseStep 4757525 = 223009) (by norm_num)
theorem B3171683 : Blo 2113435 3171683 := bstep (se 1 (by rfl) ⟨2378762, by rfl⟩ : syracuseStep 3171683 = 4757525) B4757525
theorem B2114455 : Blo 2113435 2114455 := bstep (se 1 (by rfl) ⟨1585841, by rfl⟩ : syracuseStep 2114455 = 3171683) B3171683
theorem B8028341 : Blo 2113435 8028341 := bbase (se 5 (by rfl) ⟨376328, by rfl⟩ : syracuseStep 8028341 = 752657) (by norm_num)
theorem B5352227 : Blo 2113435 5352227 := bstep (se 1 (by rfl) ⟨4014170, by rfl⟩ : syracuseStep 5352227 = 8028341) B8028341
theorem B3568151 : Blo 2113435 3568151 := bstep (se 1 (by rfl) ⟨2676113, by rfl⟩ : syracuseStep 3568151 = 5352227) B5352227
theorem B2378767 : Blo 2113435 2378767 := bstep (se 1 (by rfl) ⟨1784075, by rfl⟩ : syracuseStep 2378767 = 3568151) B3568151
theorem B3171689 : Blo 2113435 3171689 := bstep (se 2 (by rfl) ⟨1189383, by rfl⟩ : syracuseStep 3171689 = 2378767) B2378767
theorem B2114459 : Blo 2113435 2114459 := bstep (se 1 (by rfl) ⟨1585844, by rfl⟩ : syracuseStep 2114459 = 3171689) B3171689
theorem B5080445 : Blo 2113435 5080445 := bbase (se 3 (by rfl) ⟨952583, by rfl⟩ : syracuseStep 5080445 = 1905167) (by norm_num)
theorem B3386963 : Blo 2113435 3386963 := bstep (se 1 (by rfl) ⟨2540222, by rfl⟩ : syracuseStep 3386963 = 5080445) B5080445
theorem B2257975 : Blo 2113435 2257975 := bstep (se 1 (by rfl) ⟨1693481, by rfl⟩ : syracuseStep 2257975 = 3386963) B3386963
theorem B12042533 : Blo 2113435 12042533 := bstep (se 4 (by rfl) ⟨1128987, by rfl⟩ : syracuseStep 12042533 = 2257975) B2257975
theorem B8028355 : Blo 2113435 8028355 := bstep (se 1 (by rfl) ⟨6021266, by rfl⟩ : syracuseStep 8028355 = 12042533) B12042533
theorem B10704473 : Blo 2113435 10704473 := bstep (se 2 (by rfl) ⟨4014177, by rfl⟩ : syracuseStep 10704473 = 8028355) B8028355
theorem B7136315 : Blo 2113435 7136315 := bstep (se 1 (by rfl) ⟨5352236, by rfl⟩ : syracuseStep 7136315 = 10704473) B10704473
theorem B4757543 : Blo 2113435 4757543 := bstep (se 1 (by rfl) ⟨3568157, by rfl⟩ : syracuseStep 4757543 = 7136315) B7136315
theorem B3171695 : Blo 2113435 3171695 := bstep (se 1 (by rfl) ⟨2378771, by rfl⟩ : syracuseStep 3171695 = 4757543) B4757543
theorem B2114463 : Blo 2113435 2114463 := bstep (se 1 (by rfl) ⟨1585847, by rfl⟩ : syracuseStep 2114463 = 3171695) B3171695
theorem B3171701 : Blo 2113435 3171701 := bbase (se 5 (by rfl) ⟨148673, by rfl⟩ : syracuseStep 3171701 = 297347) (by norm_num)
theorem B2114467 : Blo 2113435 2114467 := bstep (se 1 (by rfl) ⟨1585850, by rfl⟩ : syracuseStep 2114467 = 3171701) B3171701
theorem B3010645 : Blo 2113435 3010645 := bbase (se 8 (by rfl) ⟨17640, by rfl⟩ : syracuseStep 3010645 = 35281) (by norm_num)
theorem B4014193 : Blo 2113435 4014193 := bstep (se 2 (by rfl) ⟨1505322, by rfl⟩ : syracuseStep 4014193 = 3010645) B3010645
theorem B5352257 : Blo 2113435 5352257 := bstep (se 2 (by rfl) ⟨2007096, by rfl⟩ : syracuseStep 5352257 = 4014193) B4014193
theorem B3568171 : Blo 2113435 3568171 := bstep (se 1 (by rfl) ⟨2676128, by rfl⟩ : syracuseStep 3568171 = 5352257) B5352257
theorem B4757561 : Blo 2113435 4757561 := bstep (se 2 (by rfl) ⟨1784085, by rfl⟩ : syracuseStep 4757561 = 3568171) B3568171
theorem B3171707 : Blo 2113435 3171707 := bstep (se 1 (by rfl) ⟨2378780, by rfl⟩ : syracuseStep 3171707 = 4757561) B4757561
theorem B2114471 : Blo 2113435 2114471 := bstep (se 1 (by rfl) ⟨1585853, by rfl⟩ : syracuseStep 2114471 = 3171707) B3171707
theorem B2378785 : Blo 2113435 2378785 := bbase (se 2 (by rfl) ⟨892044, by rfl⟩ : syracuseStep 2378785 = 1784089) (by norm_num)
theorem B3171713 : Blo 2113435 3171713 := bstep (se 2 (by rfl) ⟨1189392, by rfl⟩ : syracuseStep 3171713 = 2378785) B2378785
theorem B2114475 : Blo 2113435 2114475 := bstep (se 1 (by rfl) ⟨1585856, by rfl⟩ : syracuseStep 2114475 = 3171713) B3171713
theorem B5352277 : Blo 2113435 5352277 := bbase (se 9 (by rfl) ⟨15680, by rfl⟩ : syracuseStep 5352277 = 31361) (by norm_num)
theorem B7136369 : Blo 2113435 7136369 := bstep (se 2 (by rfl) ⟨2676138, by rfl⟩ : syracuseStep 7136369 = 5352277) B5352277
theorem B4757579 : Blo 2113435 4757579 := bstep (se 1 (by rfl) ⟨3568184, by rfl⟩ : syracuseStep 4757579 = 7136369) B7136369
theorem B3171719 : Blo 2113435 3171719 := bstep (se 1 (by rfl) ⟨2378789, by rfl⟩ : syracuseStep 3171719 = 4757579) B4757579
theorem B2114479 : Blo 2113435 2114479 := bstep (se 1 (by rfl) ⟨1585859, by rfl⟩ : syracuseStep 2114479 = 3171719) B3171719
theorem B3171725 : Blo 2113435 3171725 := bbase (se 3 (by rfl) ⟨594698, by rfl⟩ : syracuseStep 3171725 = 1189397) (by norm_num)
theorem B2114483 : Blo 2113435 2114483 := bstep (se 1 (by rfl) ⟨1585862, by rfl⟩ : syracuseStep 2114483 = 3171725) B3171725
theorem B4757597 : Blo 2113435 4757597 := bbase (se 3 (by rfl) ⟨892049, by rfl⟩ : syracuseStep 4757597 = 1784099) (by norm_num)
theorem B3171731 : Blo 2113435 3171731 := bstep (se 1 (by rfl) ⟨2378798, by rfl⟩ : syracuseStep 3171731 = 4757597) B4757597
theorem B2114487 : Blo 2113435 2114487 := bstep (se 1 (by rfl) ⟨1585865, by rfl⟩ : syracuseStep 2114487 = 3171731) B3171731
theorem B3568205 : Blo 2113435 3568205 := bbase (se 3 (by rfl) ⟨669038, by rfl⟩ : syracuseStep 3568205 = 1338077) (by norm_num)
theorem B2378803 : Blo 2113435 2378803 := bstep (se 1 (by rfl) ⟨1784102, by rfl⟩ : syracuseStep 2378803 = 3568205) B3568205
theorem B3171737 : Blo 2113435 3171737 := bstep (se 2 (by rfl) ⟨1189401, by rfl⟩ : syracuseStep 3171737 = 2378803) B2378803
theorem B2114491 : Blo 2113435 2114491 := bstep (se 1 (by rfl) ⟨1585868, by rfl⟩ : syracuseStep 2114491 = 3171737) B3171737
theorem B2143345 : Blo 2113435 2143345 := bbase (se 2 (by rfl) ⟨803754, by rfl⟩ : syracuseStep 2143345 = 1607509) (by norm_num)
theorem B2857793 : Blo 2113435 2857793 := bstep (se 2 (by rfl) ⟨1071672, by rfl⟩ : syracuseStep 2857793 = 2143345) B2143345
theorem B30483125 : Blo 2113435 30483125 := bstep (se 5 (by rfl) ⟨1428896, by rfl⟩ : syracuseStep 30483125 = 2857793) B2857793
theorem B20322083 : Blo 2113435 20322083 := bstep (se 1 (by rfl) ⟨15241562, by rfl⟩ : syracuseStep 20322083 = 30483125) B30483125
theorem B13548055 : Blo 2113435 13548055 := bstep (se 1 (by rfl) ⟨10161041, by rfl⟩ : syracuseStep 13548055 = 20322083) B20322083
theorem B18064073 : Blo 2113435 18064073 := bstep (se 2 (by rfl) ⟨6774027, by rfl⟩ : syracuseStep 18064073 = 13548055) B13548055
theorem B12042715 : Blo 2113435 12042715 := bstep (se 1 (by rfl) ⟨9032036, by rfl⟩ : syracuseStep 12042715 = 18064073) B18064073
theorem B16056953 : Blo 2113435 16056953 := bstep (se 2 (by rfl) ⟨6021357, by rfl⟩ : syracuseStep 16056953 = 12042715) B12042715
theorem B10704635 : Blo 2113435 10704635 := bstep (se 1 (by rfl) ⟨8028476, by rfl⟩ : syracuseStep 10704635 = 16056953) B16056953
theorem B7136423 : Blo 2113435 7136423 := bstep (se 1 (by rfl) ⟨5352317, by rfl⟩ : syracuseStep 7136423 = 10704635) B10704635
theorem B4757615 : Blo 2113435 4757615 := bstep (se 1 (by rfl) ⟨3568211, by rfl⟩ : syracuseStep 4757615 = 7136423) B7136423
theorem B3171743 : Blo 2113435 3171743 := bstep (se 1 (by rfl) ⟨2378807, by rfl⟩ : syracuseStep 3171743 = 4757615) B4757615
theorem B2114495 : Blo 2113435 2114495 := bstep (se 1 (by rfl) ⟨1585871, by rfl⟩ : syracuseStep 2114495 = 3171743) B3171743
theorem B3171749 : Blo 2113435 3171749 := bbase (se 4 (by rfl) ⟨297351, by rfl⟩ : syracuseStep 3171749 = 594703) (by norm_num)
theorem B2114499 : Blo 2113435 2114499 := bstep (se 1 (by rfl) ⟨1585874, by rfl⟩ : syracuseStep 2114499 = 3171749) B3171749
theorem B2676169 : Blo 2113435 2676169 := bbase (se 2 (by rfl) ⟨1003563, by rfl⟩ : syracuseStep 2676169 = 2007127) (by norm_num)
theorem B3568225 : Blo 2113435 3568225 := bstep (se 2 (by rfl) ⟨1338084, by rfl⟩ : syracuseStep 3568225 = 2676169) B2676169
theorem B4757633 : Blo 2113435 4757633 := bstep (se 2 (by rfl) ⟨1784112, by rfl⟩ : syracuseStep 4757633 = 3568225) B3568225
theorem B3171755 : Blo 2113435 3171755 := bstep (se 1 (by rfl) ⟨2378816, by rfl⟩ : syracuseStep 3171755 = 4757633) B4757633
theorem B2114503 : Blo 2113435 2114503 := bstep (se 1 (by rfl) ⟨1585877, by rfl⟩ : syracuseStep 2114503 = 3171755) B3171755
theorem B2378821 : Blo 2113435 2378821 := bbase (se 4 (by rfl) ⟨223014, by rfl⟩ : syracuseStep 2378821 = 446029) (by norm_num)
theorem B3171761 : Blo 2113435 3171761 := bstep (se 2 (by rfl) ⟨1189410, by rfl⟩ : syracuseStep 3171761 = 2378821) B2378821
theorem B2114507 : Blo 2113435 2114507 := bstep (se 1 (by rfl) ⟨1585880, by rfl⟩ : syracuseStep 2114507 = 3171761) B3171761
theorem B4014269 : Blo 2113435 4014269 := bbase (se 3 (by rfl) ⟨752675, by rfl⟩ : syracuseStep 4014269 = 1505351) (by norm_num)
theorem B2676179 : Blo 2113435 2676179 := bstep (se 1 (by rfl) ⟨2007134, by rfl⟩ : syracuseStep 2676179 = 4014269) B4014269
theorem B7136477 : Blo 2113435 7136477 := bstep (se 3 (by rfl) ⟨1338089, by rfl⟩ : syracuseStep 7136477 = 2676179) B2676179
theorem B4757651 : Blo 2113435 4757651 := bstep (se 1 (by rfl) ⟨3568238, by rfl⟩ : syracuseStep 4757651 = 7136477) B7136477
theorem B3171767 : Blo 2113435 3171767 := bstep (se 1 (by rfl) ⟨2378825, by rfl⟩ : syracuseStep 3171767 = 4757651) B4757651
theorem B2114511 : Blo 2113435 2114511 := bstep (se 1 (by rfl) ⟨1585883, by rfl⟩ : syracuseStep 2114511 = 3171767) B3171767
theorem B3171773 : Blo 2113435 3171773 := bbase (se 3 (by rfl) ⟨594707, by rfl⟩ : syracuseStep 3171773 = 1189415) (by norm_num)
theorem B2114515 : Blo 2113435 2114515 := bstep (se 1 (by rfl) ⟨1585886, by rfl⟩ : syracuseStep 2114515 = 3171773) B3171773
theorem B4757669 : Blo 2113435 4757669 := bbase (se 4 (by rfl) ⟨446031, by rfl⟩ : syracuseStep 4757669 = 892063) (by norm_num)
theorem B3171779 : Blo 2113435 3171779 := bstep (se 1 (by rfl) ⟨2378834, by rfl⟩ : syracuseStep 3171779 = 4757669) B4757669
theorem B2114519 : Blo 2113435 2114519 := bstep (se 1 (by rfl) ⟨1585889, by rfl⟩ : syracuseStep 2114519 = 3171779) B3171779
theorem B5352389 : Blo 2113435 5352389 := bbase (se 4 (by rfl) ⟨501786, by rfl⟩ : syracuseStep 5352389 = 1003573) (by norm_num)
theorem B3568259 : Blo 2113435 3568259 := bstep (se 1 (by rfl) ⟨2676194, by rfl⟩ : syracuseStep 3568259 = 5352389) B5352389
theorem B2378839 : Blo 2113435 2378839 := bstep (se 1 (by rfl) ⟨1784129, by rfl⟩ : syracuseStep 2378839 = 3568259) B3568259
theorem B3171785 : Blo 2113435 3171785 := bstep (se 2 (by rfl) ⟨1189419, by rfl⟩ : syracuseStep 3171785 = 2378839) B2378839
theorem B2114523 : Blo 2113435 2114523 := bstep (se 1 (by rfl) ⟨1585892, by rfl⟩ : syracuseStep 2114523 = 3171785) B3171785
theorem B2857837 : Blo 2113435 2857837 := bbase (se 3 (by rfl) ⟨535844, by rfl⟩ : syracuseStep 2857837 = 1071689) (by norm_num)
theorem B3810449 : Blo 2113435 3810449 := bstep (se 2 (by rfl) ⟨1428918, by rfl⟩ : syracuseStep 3810449 = 2857837) B2857837
theorem B10161197 : Blo 2113435 10161197 := bstep (se 3 (by rfl) ⟨1905224, by rfl⟩ : syracuseStep 10161197 = 3810449) B3810449
theorem B6774131 : Blo 2113435 6774131 := bstep (se 1 (by rfl) ⟨5080598, by rfl⟩ : syracuseStep 6774131 = 10161197) B10161197
theorem B4516087 : Blo 2113435 4516087 := bstep (se 1 (by rfl) ⟨3387065, by rfl⟩ : syracuseStep 4516087 = 6774131) B6774131
theorem B6021449 : Blo 2113435 6021449 := bstep (se 2 (by rfl) ⟨2258043, by rfl⟩ : syracuseStep 6021449 = 4516087) B4516087
theorem B4014299 : Blo 2113435 4014299 := bstep (se 1 (by rfl) ⟨3010724, by rfl⟩ : syracuseStep 4014299 = 6021449) B6021449
theorem B10704797 : Blo 2113435 10704797 := bstep (se 3 (by rfl) ⟨2007149, by rfl⟩ : syracuseStep 10704797 = 4014299) B4014299
theorem B7136531 : Blo 2113435 7136531 := bstep (se 1 (by rfl) ⟨5352398, by rfl⟩ : syracuseStep 7136531 = 10704797) B10704797
theorem B4757687 : Blo 2113435 4757687 := bstep (se 1 (by rfl) ⟨3568265, by rfl⟩ : syracuseStep 4757687 = 7136531) B7136531
theorem B3171791 : Blo 2113435 3171791 := bstep (se 1 (by rfl) ⟨2378843, by rfl⟩ : syracuseStep 3171791 = 4757687) B4757687
theorem B2114527 : Blo 2113435 2114527 := bstep (se 1 (by rfl) ⟨1585895, by rfl⟩ : syracuseStep 2114527 = 3171791) B3171791
theorem B3171797 : Blo 2113435 3171797 := bbase (se 7 (by rfl) ⟨37169, by rfl⟩ : syracuseStep 3171797 = 74339) (by norm_num)
theorem B2114531 : Blo 2113435 2114531 := bstep (se 1 (by rfl) ⟨1585898, by rfl⟩ : syracuseStep 2114531 = 3171797) B3171797
theorem B8028629 : Blo 2113435 8028629 := bbase (se 7 (by rfl) ⟨94085, by rfl⟩ : syracuseStep 8028629 = 188171) (by norm_num)
theorem B5352419 : Blo 2113435 5352419 := bstep (se 1 (by rfl) ⟨4014314, by rfl⟩ : syracuseStep 5352419 = 8028629) B8028629
theorem B3568279 : Blo 2113435 3568279 := bstep (se 1 (by rfl) ⟨2676209, by rfl⟩ : syracuseStep 3568279 = 5352419) B5352419
theorem B4757705 : Blo 2113435 4757705 := bstep (se 2 (by rfl) ⟨1784139, by rfl⟩ : syracuseStep 4757705 = 3568279) B3568279
theorem B3171803 : Blo 2113435 3171803 := bstep (se 1 (by rfl) ⟨2378852, by rfl⟩ : syracuseStep 3171803 = 4757705) B4757705
theorem B2114535 : Blo 2113435 2114535 := bstep (se 1 (by rfl) ⟨1585901, by rfl⟩ : syracuseStep 2114535 = 3171803) B3171803
theorem B2378857 : Blo 2113435 2378857 := bbase (se 2 (by rfl) ⟨892071, by rfl⟩ : syracuseStep 2378857 = 1784143) (by norm_num)
theorem B3171809 : Blo 2113435 3171809 := bstep (se 2 (by rfl) ⟨1189428, by rfl⟩ : syracuseStep 3171809 = 2378857) B2378857
theorem B2114539 : Blo 2113435 2114539 := bstep (se 1 (by rfl) ⟨1585904, by rfl⟩ : syracuseStep 2114539 = 3171809) B3171809
theorem B5080637 : Blo 2113435 5080637 := bbase (se 3 (by rfl) ⟨952619, by rfl⟩ : syracuseStep 5080637 = 1905239) (by norm_num)
theorem B3387091 : Blo 2113435 3387091 := bstep (se 1 (by rfl) ⟨2540318, by rfl⟩ : syracuseStep 3387091 = 5080637) B5080637
theorem B4516121 : Blo 2113435 4516121 := bstep (se 2 (by rfl) ⟨1693545, by rfl⟩ : syracuseStep 4516121 = 3387091) B3387091
theorem B12042989 : Blo 2113435 12042989 := bstep (se 3 (by rfl) ⟨2258060, by rfl⟩ : syracuseStep 12042989 = 4516121) B4516121
theorem B8028659 : Blo 2113435 8028659 := bstep (se 1 (by rfl) ⟨6021494, by rfl⟩ : syracuseStep 8028659 = 12042989) B12042989
theorem B5352439 : Blo 2113435 5352439 := bstep (se 1 (by rfl) ⟨4014329, by rfl⟩ : syracuseStep 5352439 = 8028659) B8028659
theorem B7136585 : Blo 2113435 7136585 := bstep (se 2 (by rfl) ⟨2676219, by rfl⟩ : syracuseStep 7136585 = 5352439) B5352439
theorem B4757723 : Blo 2113435 4757723 := bstep (se 1 (by rfl) ⟨3568292, by rfl⟩ : syracuseStep 4757723 = 7136585) B7136585
theorem B3171815 : Blo 2113435 3171815 := bstep (se 1 (by rfl) ⟨2378861, by rfl⟩ : syracuseStep 3171815 = 4757723) B4757723
theorem B2114543 : Blo 2113435 2114543 := bstep (se 1 (by rfl) ⟨1585907, by rfl⟩ : syracuseStep 2114543 = 3171815) B3171815
theorem B3171821 : Blo 2113435 3171821 := bbase (se 3 (by rfl) ⟨594716, by rfl⟩ : syracuseStep 3171821 = 1189433) (by norm_num)
theorem B2114547 : Blo 2113435 2114547 := bstep (se 1 (by rfl) ⟨1585910, by rfl⟩ : syracuseStep 2114547 = 3171821) B3171821
theorem B4757741 : Blo 2113435 4757741 := bbase (se 3 (by rfl) ⟨892076, by rfl⟩ : syracuseStep 4757741 = 1784153) (by norm_num)
theorem B3171827 : Blo 2113435 3171827 := bstep (se 1 (by rfl) ⟨2378870, by rfl⟩ : syracuseStep 3171827 = 4757741) B4757741
theorem B2114551 : Blo 2113435 2114551 := bstep (se 1 (by rfl) ⟨1585913, by rfl⟩ : syracuseStep 2114551 = 3171827) B3171827
theorem B3010765 : Blo 2113435 3010765 := bbase (se 3 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 3010765 = 1129037) (by norm_num)
theorem B4014353 : Blo 2113435 4014353 := bstep (se 2 (by rfl) ⟨1505382, by rfl⟩ : syracuseStep 4014353 = 3010765) B3010765
theorem B2676235 : Blo 2113435 2676235 := bstep (se 1 (by rfl) ⟨2007176, by rfl⟩ : syracuseStep 2676235 = 4014353) B4014353
theorem B3568313 : Blo 2113435 3568313 := bstep (se 2 (by rfl) ⟨1338117, by rfl⟩ : syracuseStep 3568313 = 2676235) B2676235
theorem B2378875 : Blo 2113435 2378875 := bstep (se 1 (by rfl) ⟨1784156, by rfl⟩ : syracuseStep 2378875 = 3568313) B3568313
theorem B3171833 : Blo 2113435 3171833 := bstep (se 2 (by rfl) ⟨1189437, by rfl⟩ : syracuseStep 3171833 = 2378875) B2378875
theorem B2114555 : Blo 2113435 2114555 := bstep (se 1 (by rfl) ⟨1585916, by rfl⟩ : syracuseStep 2114555 = 3171833) B3171833
theorem B36622165 : Blo 2113435 36622165 := bbase (se 9 (by rfl) ⟨107291, by rfl⟩ : syracuseStep 36622165 = 214583) (by norm_num)
theorem B48829553 : Blo 2113435 48829553 := bstep (se 2 (by rfl) ⟨18311082, by rfl⟩ : syracuseStep 48829553 = 36622165) B36622165
theorem B32553035 : Blo 2113435 32553035 := bstep (se 1 (by rfl) ⟨24414776, by rfl⟩ : syracuseStep 32553035 = 48829553) B48829553
theorem B21702023 : Blo 2113435 21702023 := bstep (se 1 (by rfl) ⟨16276517, by rfl⟩ : syracuseStep 21702023 = 32553035) B32553035
theorem B14468015 : Blo 2113435 14468015 := bstep (se 1 (by rfl) ⟨10851011, by rfl⟩ : syracuseStep 14468015 = 21702023) B21702023
theorem B38581373 : Blo 2113435 38581373 := bstep (se 3 (by rfl) ⟨7234007, by rfl⟩ : syracuseStep 38581373 = 14468015) B14468015
theorem B25720915 : Blo 2113435 25720915 := bstep (se 1 (by rfl) ⟨19290686, by rfl⟩ : syracuseStep 25720915 = 38581373) B38581373
theorem B34294553 : Blo 2113435 34294553 := bstep (se 2 (by rfl) ⟨12860457, by rfl⟩ : syracuseStep 34294553 = 25720915) B25720915
theorem B22863035 : Blo 2113435 22863035 := bstep (se 1 (by rfl) ⟨17147276, by rfl⟩ : syracuseStep 22863035 = 34294553) B34294553
theorem B15242023 : Blo 2113435 15242023 := bstep (se 1 (by rfl) ⟨11431517, by rfl⟩ : syracuseStep 15242023 = 22863035) B22863035
theorem B81290789 : Blo 2113435 81290789 := bstep (se 4 (by rfl) ⟨7621011, by rfl⟩ : syracuseStep 81290789 = 15242023) B15242023
theorem B54193859 : Blo 2113435 54193859 := bstep (se 1 (by rfl) ⟨40645394, by rfl⟩ : syracuseStep 54193859 = 81290789) B81290789
theorem B36129239 : Blo 2113435 36129239 := bstep (se 1 (by rfl) ⟨27096929, by rfl⟩ : syracuseStep 36129239 = 54193859) B54193859
theorem B24086159 : Blo 2113435 24086159 := bstep (se 1 (by rfl) ⟨18064619, by rfl⟩ : syracuseStep 24086159 = 36129239) B36129239
theorem B16057439 : Blo 2113435 16057439 := bstep (se 1 (by rfl) ⟨12043079, by rfl⟩ : syracuseStep 16057439 = 24086159) B24086159
theorem B10704959 : Blo 2113435 10704959 := bstep (se 1 (by rfl) ⟨8028719, by rfl⟩ : syracuseStep 10704959 = 16057439) B16057439
theorem B7136639 : Blo 2113435 7136639 := bstep (se 1 (by rfl) ⟨5352479, by rfl⟩ : syracuseStep 7136639 = 10704959) B10704959
theorem B4757759 : Blo 2113435 4757759 := bstep (se 1 (by rfl) ⟨3568319, by rfl⟩ : syracuseStep 4757759 = 7136639) B7136639
theorem B3171839 : Blo 2113435 3171839 := bstep (se 1 (by rfl) ⟨2378879, by rfl⟩ : syracuseStep 3171839 = 4757759) B4757759
theorem B2114559 : Blo 2113435 2114559 := bstep (se 1 (by rfl) ⟨1585919, by rfl⟩ : syracuseStep 2114559 = 3171839) B3171839
theorem B3171845 : Blo 2113435 3171845 := bbase (se 4 (by rfl) ⟨297360, by rfl⟩ : syracuseStep 3171845 = 594721) (by norm_num)
theorem B2114563 : Blo 2113435 2114563 := bstep (se 1 (by rfl) ⟨1585922, by rfl⟩ : syracuseStep 2114563 = 3171845) B3171845
theorem B3568333 : Blo 2113435 3568333 := bbase (se 3 (by rfl) ⟨669062, by rfl⟩ : syracuseStep 3568333 = 1338125) (by norm_num)
theorem B4757777 : Blo 2113435 4757777 := bstep (se 2 (by rfl) ⟨1784166, by rfl⟩ : syracuseStep 4757777 = 3568333) B3568333
theorem B3171851 : Blo 2113435 3171851 := bstep (se 1 (by rfl) ⟨2378888, by rfl⟩ : syracuseStep 3171851 = 4757777) B4757777
theorem B2114567 : Blo 2113435 2114567 := bstep (se 1 (by rfl) ⟨1585925, by rfl⟩ : syracuseStep 2114567 = 3171851) B3171851
theorem B2378893 : Blo 2113435 2378893 := bbase (se 3 (by rfl) ⟨446042, by rfl⟩ : syracuseStep 2378893 = 892085) (by norm_num)
theorem B3171857 : Blo 2113435 3171857 := bstep (se 2 (by rfl) ⟨1189446, by rfl⟩ : syracuseStep 3171857 = 2378893) B2378893
theorem B2114571 : Blo 2113435 2114571 := bstep (se 1 (by rfl) ⟨1585928, by rfl⟩ : syracuseStep 2114571 = 3171857) B3171857
theorem B7136693 : Blo 2113435 7136693 := bbase (se 5 (by rfl) ⟨334532, by rfl⟩ : syracuseStep 7136693 = 669065) (by norm_num)
theorem B4757795 : Blo 2113435 4757795 := bstep (se 1 (by rfl) ⟨3568346, by rfl⟩ : syracuseStep 4757795 = 7136693) B7136693
theorem B3171863 : Blo 2113435 3171863 := bstep (se 1 (by rfl) ⟨2378897, by rfl⟩ : syracuseStep 3171863 = 4757795) B4757795
theorem B2114575 : Blo 2113435 2114575 := bstep (se 1 (by rfl) ⟨1585931, by rfl⟩ : syracuseStep 2114575 = 3171863) B3171863
theorem B3171869 : Blo 2113435 3171869 := bbase (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) (by norm_num)
theorem B2114579 : Blo 2113435 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B4757813 : Blo 2113435 4757813 := bbase (se 5 (by rfl) ⟨223022, by rfl⟩ : syracuseStep 4757813 = 446045) (by norm_num)
theorem B3171875 : Blo 2113435 3171875 := bstep (se 1 (by rfl) ⟨2378906, by rfl⟩ : syracuseStep 3171875 = 4757813) B4757813
theorem B2114583 : Blo 2113435 2114583 := bstep (se 1 (by rfl) ⟨1585937, by rfl⟩ : syracuseStep 2114583 = 3171875) B3171875
theorem B4238021 : Blo 2113435 4238021 := bbase (se 4 (by rfl) ⟨397314, by rfl⟩ : syracuseStep 4238021 = 794629) (by norm_num)
theorem B11301389 : Blo 2113435 11301389 := bstep (se 3 (by rfl) ⟨2119010, by rfl⟩ : syracuseStep 11301389 = 4238021) B4238021
theorem B7534259 : Blo 2113435 7534259 := bstep (se 1 (by rfl) ⟨5650694, by rfl⟩ : syracuseStep 7534259 = 11301389) B11301389
theorem B5022839 : Blo 2113435 5022839 := bstep (se 1 (by rfl) ⟨3767129, by rfl⟩ : syracuseStep 5022839 = 7534259) B7534259
theorem B3348559 : Blo 2113435 3348559 := bstep (se 1 (by rfl) ⟨2511419, by rfl⟩ : syracuseStep 3348559 = 5022839) B5022839
theorem B17858981 : Blo 2113435 17858981 := bstep (se 4 (by rfl) ⟨1674279, by rfl⟩ : syracuseStep 17858981 = 3348559) B3348559
theorem B11905987 : Blo 2113435 11905987 := bstep (se 1 (by rfl) ⟨8929490, by rfl⟩ : syracuseStep 11905987 = 17858981) B17858981
theorem B15874649 : Blo 2113435 15874649 := bstep (se 2 (by rfl) ⟨5952993, by rfl⟩ : syracuseStep 15874649 = 11905987) B11905987
theorem B10583099 : Blo 2113435 10583099 := bstep (se 1 (by rfl) ⟨7937324, by rfl⟩ : syracuseStep 10583099 = 15874649) B15874649
theorem B7055399 : Blo 2113435 7055399 := bstep (se 1 (by rfl) ⟨5291549, by rfl⟩ : syracuseStep 7055399 = 10583099) B10583099
theorem B4703599 : Blo 2113435 4703599 := bstep (se 1 (by rfl) ⟨3527699, by rfl⟩ : syracuseStep 4703599 = 7055399) B7055399
theorem B25085861 : Blo 2113435 25085861 := bstep (se 4 (by rfl) ⟨2351799, by rfl⟩ : syracuseStep 25085861 = 4703599) B4703599
theorem B16723907 : Blo 2113435 16723907 := bstep (se 1 (by rfl) ⟨12542930, by rfl⟩ : syracuseStep 16723907 = 25085861) B25085861
theorem B11149271 : Blo 2113435 11149271 := bstep (se 1 (by rfl) ⟨8361953, by rfl⟩ : syracuseStep 11149271 = 16723907) B16723907
theorem B7432847 : Blo 2113435 7432847 := bstep (se 1 (by rfl) ⟨5574635, by rfl⟩ : syracuseStep 7432847 = 11149271) B11149271
theorem B4955231 : Blo 2113435 4955231 := bstep (se 1 (by rfl) ⟨3716423, by rfl⟩ : syracuseStep 4955231 = 7432847) B7432847
theorem B13213949 : Blo 2113435 13213949 := bstep (se 3 (by rfl) ⟨2477615, by rfl⟩ : syracuseStep 13213949 = 4955231) B4955231
theorem B35237197 : Blo 2113435 35237197 := bstep (se 3 (by rfl) ⟨6606974, by rfl⟩ : syracuseStep 35237197 = 13213949) B13213949
theorem B46982929 : Blo 2113435 46982929 := bstep (se 2 (by rfl) ⟨17618598, by rfl⟩ : syracuseStep 46982929 = 35237197) B35237197
theorem B62643905 : Blo 2113435 62643905 := bstep (se 2 (by rfl) ⟨23491464, by rfl⟩ : syracuseStep 62643905 = 46982929) B46982929
theorem B41762603 : Blo 2113435 41762603 := bstep (se 1 (by rfl) ⟨31321952, by rfl⟩ : syracuseStep 41762603 = 62643905) B62643905
theorem B27841735 : Blo 2113435 27841735 := bstep (se 1 (by rfl) ⟨20881301, by rfl⟩ : syracuseStep 27841735 = 41762603) B41762603
theorem B37122313 : Blo 2113435 37122313 := bstep (se 2 (by rfl) ⟨13920867, by rfl⟩ : syracuseStep 37122313 = 27841735) B27841735
theorem B49496417 : Blo 2113435 49496417 := bstep (se 2 (by rfl) ⟨18561156, by rfl⟩ : syracuseStep 49496417 = 37122313) B37122313
theorem B32997611 : Blo 2113435 32997611 := bstep (se 1 (by rfl) ⟨24748208, by rfl⟩ : syracuseStep 32997611 = 49496417) B49496417
theorem B21998407 : Blo 2113435 21998407 := bstep (se 1 (by rfl) ⟨16498805, by rfl⟩ : syracuseStep 21998407 = 32997611) B32997611
theorem B29331209 : Blo 2113435 29331209 := bstep (se 2 (by rfl) ⟨10999203, by rfl⟩ : syracuseStep 29331209 = 21998407) B21998407
theorem B19554139 : Blo 2113435 19554139 := bstep (se 1 (by rfl) ⟨14665604, by rfl⟩ : syracuseStep 19554139 = 29331209) B29331209
theorem B104288741 : Blo 2113435 104288741 := bstep (se 4 (by rfl) ⟨9777069, by rfl⟩ : syracuseStep 104288741 = 19554139) B19554139
theorem B69525827 : Blo 2113435 69525827 := bstep (se 1 (by rfl) ⟨52144370, by rfl⟩ : syracuseStep 69525827 = 104288741) B104288741
theorem B46350551 : Blo 2113435 46350551 := bstep (se 1 (by rfl) ⟨34762913, by rfl⟩ : syracuseStep 46350551 = 69525827) B69525827
theorem B30900367 : Blo 2113435 30900367 := bstep (se 1 (by rfl) ⟨23175275, by rfl⟩ : syracuseStep 30900367 = 46350551) B46350551
theorem B41200489 : Blo 2113435 41200489 := bstep (se 2 (by rfl) ⟨15450183, by rfl⟩ : syracuseStep 41200489 = 30900367) B30900367
theorem B54933985 : Blo 2113435 54933985 := bstep (se 2 (by rfl) ⟨20600244, by rfl⟩ : syracuseStep 54933985 = 41200489) B41200489
theorem B73245313 : Blo 2113435 73245313 := bstep (se 2 (by rfl) ⟨27466992, by rfl⟩ : syracuseStep 73245313 = 54933985) B54933985
theorem B97660417 : Blo 2113435 97660417 := bstep (se 2 (by rfl) ⟨36622656, by rfl⟩ : syracuseStep 97660417 = 73245313) B73245313
theorem B130213889 : Blo 2113435 130213889 := bstep (se 2 (by rfl) ⟨48830208, by rfl⟩ : syracuseStep 130213889 = 97660417) B97660417
theorem B86809259 : Blo 2113435 86809259 := bstep (se 1 (by rfl) ⟨65106944, by rfl⟩ : syracuseStep 86809259 = 130213889) B130213889
theorem B57872839 : Blo 2113435 57872839 := bstep (se 1 (by rfl) ⟨43404629, by rfl⟩ : syracuseStep 57872839 = 86809259) B86809259
theorem B77163785 : Blo 2113435 77163785 := bstep (se 2 (by rfl) ⟨28936419, by rfl⟩ : syracuseStep 77163785 = 57872839) B57872839
theorem B51442523 : Blo 2113435 51442523 := bstep (se 1 (by rfl) ⟨38581892, by rfl⟩ : syracuseStep 51442523 = 77163785) B77163785
theorem B34295015 : Blo 2113435 34295015 := bstep (se 1 (by rfl) ⟨25721261, by rfl⟩ : syracuseStep 34295015 = 51442523) B51442523
theorem B22863343 : Blo 2113435 22863343 := bstep (se 1 (by rfl) ⟨17147507, by rfl⟩ : syracuseStep 22863343 = 34295015) B34295015
theorem B30484457 : Blo 2113435 30484457 := bstep (se 2 (by rfl) ⟨11431671, by rfl⟩ : syracuseStep 30484457 = 22863343) B22863343
theorem B20322971 : Blo 2113435 20322971 := bstep (se 1 (by rfl) ⟨15242228, by rfl⟩ : syracuseStep 20322971 = 30484457) B30484457
theorem B13548647 : Blo 2113435 13548647 := bstep (se 1 (by rfl) ⟨10161485, by rfl⟩ : syracuseStep 13548647 = 20322971) B20322971
theorem B9032431 : Blo 2113435 9032431 := bstep (se 1 (by rfl) ⟨6774323, by rfl⟩ : syracuseStep 9032431 = 13548647) B13548647
theorem B12043241 : Blo 2113435 12043241 := bstep (se 2 (by rfl) ⟨4516215, by rfl⟩ : syracuseStep 12043241 = 9032431) B9032431
theorem B8028827 : Blo 2113435 8028827 := bstep (se 1 (by rfl) ⟨6021620, by rfl⟩ : syracuseStep 8028827 = 12043241) B12043241
theorem B5352551 : Blo 2113435 5352551 := bstep (se 1 (by rfl) ⟨4014413, by rfl⟩ : syracuseStep 5352551 = 8028827) B8028827
theorem B3568367 : Blo 2113435 3568367 := bstep (se 1 (by rfl) ⟨2676275, by rfl⟩ : syracuseStep 3568367 = 5352551) B5352551
theorem B2378911 : Blo 2113435 2378911 := bstep (se 1 (by rfl) ⟨1784183, by rfl⟩ : syracuseStep 2378911 = 3568367) B3568367
theorem B3171881 : Blo 2113435 3171881 := bstep (se 2 (by rfl) ⟨1189455, by rfl⟩ : syracuseStep 3171881 = 2378911) B2378911
theorem B2114587 : Blo 2113435 2114587 := bstep (se 1 (by rfl) ⟨1585940, by rfl⟩ : syracuseStep 2114587 = 3171881) B3171881
theorem B23175317 : Blo 2113435 23175317 := bbase (se 6 (by rfl) ⟨543171, by rfl⟩ : syracuseStep 23175317 = 1086343) (by norm_num)
theorem B15450211 : Blo 2113435 15450211 := bstep (se 1 (by rfl) ⟨11587658, by rfl⟩ : syracuseStep 15450211 = 23175317) B23175317
theorem B20600281 : Blo 2113435 20600281 := bstep (se 2 (by rfl) ⟨7725105, by rfl⟩ : syracuseStep 20600281 = 15450211) B15450211
theorem B27467041 : Blo 2113435 27467041 := bstep (se 2 (by rfl) ⟨10300140, by rfl⟩ : syracuseStep 27467041 = 20600281) B20600281
theorem B36622721 : Blo 2113435 36622721 := bstep (se 2 (by rfl) ⟨13733520, by rfl⟩ : syracuseStep 36622721 = 27467041) B27467041
theorem B24415147 : Blo 2113435 24415147 := bstep (se 1 (by rfl) ⟨18311360, by rfl⟩ : syracuseStep 24415147 = 36622721) B36622721
theorem B130214117 : Blo 2113435 130214117 := bstep (se 4 (by rfl) ⟨12207573, by rfl⟩ : syracuseStep 130214117 = 24415147) B24415147
theorem B86809411 : Blo 2113435 86809411 := bstep (se 1 (by rfl) ⟨65107058, by rfl⟩ : syracuseStep 86809411 = 130214117) B130214117
theorem B115745881 : Blo 2113435 115745881 := bstep (se 2 (by rfl) ⟨43404705, by rfl⟩ : syracuseStep 115745881 = 86809411) B86809411
theorem B154327841 : Blo 2113435 154327841 := bstep (se 2 (by rfl) ⟨57872940, by rfl⟩ : syracuseStep 154327841 = 115745881) B115745881
theorem B102885227 : Blo 2113435 102885227 := bstep (se 1 (by rfl) ⟨77163920, by rfl⟩ : syracuseStep 102885227 = 154327841) B154327841
theorem B68590151 : Blo 2113435 68590151 := bstep (se 1 (by rfl) ⟨51442613, by rfl⟩ : syracuseStep 68590151 = 102885227) B102885227
theorem B45726767 : Blo 2113435 45726767 := bstep (se 1 (by rfl) ⟨34295075, by rfl⟩ : syracuseStep 45726767 = 68590151) B68590151
theorem B30484511 : Blo 2113435 30484511 := bstep (se 1 (by rfl) ⟨22863383, by rfl⟩ : syracuseStep 30484511 = 45726767) B45726767
theorem B20323007 : Blo 2113435 20323007 := bstep (se 1 (by rfl) ⟨15242255, by rfl⟩ : syracuseStep 20323007 = 30484511) B30484511
theorem B13548671 : Blo 2113435 13548671 := bstep (se 1 (by rfl) ⟨10161503, by rfl⟩ : syracuseStep 13548671 = 20323007) B20323007
theorem B9032447 : Blo 2113435 9032447 := bstep (se 1 (by rfl) ⟨6774335, by rfl⟩ : syracuseStep 9032447 = 13548671) B13548671
theorem B6021631 : Blo 2113435 6021631 := bstep (se 1 (by rfl) ⟨4516223, by rfl⟩ : syracuseStep 6021631 = 9032447) B9032447
theorem B8028841 : Blo 2113435 8028841 := bstep (se 2 (by rfl) ⟨3010815, by rfl⟩ : syracuseStep 8028841 = 6021631) B6021631
theorem B10705121 : Blo 2113435 10705121 := bstep (se 2 (by rfl) ⟨4014420, by rfl⟩ : syracuseStep 10705121 = 8028841) B8028841
theorem B7136747 : Blo 2113435 7136747 := bstep (se 1 (by rfl) ⟨5352560, by rfl⟩ : syracuseStep 7136747 = 10705121) B10705121
theorem B4757831 : Blo 2113435 4757831 := bstep (se 1 (by rfl) ⟨3568373, by rfl⟩ : syracuseStep 4757831 = 7136747) B7136747
theorem B3171887 : Blo 2113435 3171887 := bstep (se 1 (by rfl) ⟨2378915, by rfl⟩ : syracuseStep 3171887 = 4757831) B4757831
theorem B2114591 : Blo 2113435 2114591 := bstep (se 1 (by rfl) ⟨1585943, by rfl⟩ : syracuseStep 2114591 = 3171887) B3171887
theorem B3171893 : Blo 2113435 3171893 := bbase (se 5 (by rfl) ⟨148682, by rfl⟩ : syracuseStep 3171893 = 297365) (by norm_num)
theorem B2114595 : Blo 2113435 2114595 := bstep (se 1 (by rfl) ⟨1585946, by rfl⟩ : syracuseStep 2114595 = 3171893) B3171893
theorem B5352581 : Blo 2113435 5352581 := bbase (se 4 (by rfl) ⟨501804, by rfl⟩ : syracuseStep 5352581 = 1003609) (by norm_num)
theorem B3568387 : Blo 2113435 3568387 := bstep (se 1 (by rfl) ⟨2676290, by rfl⟩ : syracuseStep 3568387 = 5352581) B5352581
theorem B4757849 : Blo 2113435 4757849 := bstep (se 2 (by rfl) ⟨1784193, by rfl⟩ : syracuseStep 4757849 = 3568387) B3568387
theorem B3171899 : Blo 2113435 3171899 := bstep (se 1 (by rfl) ⟨2378924, by rfl⟩ : syracuseStep 3171899 = 4757849) B4757849
theorem B2114599 : Blo 2113435 2114599 := bstep (se 1 (by rfl) ⟨1585949, by rfl⟩ : syracuseStep 2114599 = 3171899) B3171899
theorem B2378929 : Blo 2113435 2378929 := bbase (se 2 (by rfl) ⟨892098, by rfl⟩ : syracuseStep 2378929 = 1784197) (by norm_num)
theorem B3171905 : Blo 2113435 3171905 := bstep (se 2 (by rfl) ⟨1189464, by rfl⟩ : syracuseStep 3171905 = 2378929) B2378929
theorem B2114603 : Blo 2113435 2114603 := bstep (se 1 (by rfl) ⟨1585952, by rfl⟩ : syracuseStep 2114603 = 3171905) B3171905
theorem B2258129 : Blo 2113435 2258129 := bbase (se 2 (by rfl) ⟨846798, by rfl⟩ : syracuseStep 2258129 = 1693597) (by norm_num)
theorem B6021677 : Blo 2113435 6021677 := bstep (se 3 (by rfl) ⟨1129064, by rfl⟩ : syracuseStep 6021677 = 2258129) B2258129
theorem B4014451 : Blo 2113435 4014451 := bstep (se 1 (by rfl) ⟨3010838, by rfl⟩ : syracuseStep 4014451 = 6021677) B6021677
theorem B5352601 : Blo 2113435 5352601 := bstep (se 2 (by rfl) ⟨2007225, by rfl⟩ : syracuseStep 5352601 = 4014451) B4014451
theorem B7136801 : Blo 2113435 7136801 := bstep (se 2 (by rfl) ⟨2676300, by rfl⟩ : syracuseStep 7136801 = 5352601) B5352601
theorem B4757867 : Blo 2113435 4757867 := bstep (se 1 (by rfl) ⟨3568400, by rfl⟩ : syracuseStep 4757867 = 7136801) B7136801
theorem B3171911 : Blo 2113435 3171911 := bstep (se 1 (by rfl) ⟨2378933, by rfl⟩ : syracuseStep 3171911 = 4757867) B4757867
theorem B2114607 : Blo 2113435 2114607 := bstep (se 1 (by rfl) ⟨1585955, by rfl⟩ : syracuseStep 2114607 = 3171911) B3171911
theorem B3171917 : Blo 2113435 3171917 := bbase (se 3 (by rfl) ⟨594734, by rfl⟩ : syracuseStep 3171917 = 1189469) (by norm_num)
theorem B2114611 : Blo 2113435 2114611 := bstep (se 1 (by rfl) ⟨1585958, by rfl⟩ : syracuseStep 2114611 = 3171917) B3171917
theorem B4757885 : Blo 2113435 4757885 := bbase (se 3 (by rfl) ⟨892103, by rfl⟩ : syracuseStep 4757885 = 1784207) (by norm_num)
theorem B3171923 : Blo 2113435 3171923 := bstep (se 1 (by rfl) ⟨2378942, by rfl⟩ : syracuseStep 3171923 = 4757885) B4757885
theorem B2114615 : Blo 2113435 2114615 := bstep (se 1 (by rfl) ⟨1585961, by rfl⟩ : syracuseStep 2114615 = 3171923) B3171923
theorem B3568421 : Blo 2113435 3568421 := bbase (se 4 (by rfl) ⟨334539, by rfl⟩ : syracuseStep 3568421 = 669079) (by norm_num)
theorem B2378947 : Blo 2113435 2378947 := bstep (se 1 (by rfl) ⟨1784210, by rfl⟩ : syracuseStep 2378947 = 3568421) B3568421
theorem B3171929 : Blo 2113435 3171929 := bstep (se 2 (by rfl) ⟨1189473, by rfl⟩ : syracuseStep 3171929 = 2378947) B2378947
theorem B2114619 : Blo 2113435 2114619 := bstep (se 1 (by rfl) ⟨1585964, by rfl⟩ : syracuseStep 2114619 = 3171929) B3171929
theorem B3010861 : Blo 2113435 3010861 := bbase (se 3 (by rfl) ⟨564536, by rfl⟩ : syracuseStep 3010861 = 1129073) (by norm_num)
theorem B16057925 : Blo 2113435 16057925 := bstep (se 4 (by rfl) ⟨1505430, by rfl⟩ : syracuseStep 16057925 = 3010861) B3010861
theorem B10705283 : Blo 2113435 10705283 := bstep (se 1 (by rfl) ⟨8028962, by rfl⟩ : syracuseStep 10705283 = 16057925) B16057925
theorem B7136855 : Blo 2113435 7136855 := bstep (se 1 (by rfl) ⟨5352641, by rfl⟩ : syracuseStep 7136855 = 10705283) B10705283
theorem B4757903 : Blo 2113435 4757903 := bstep (se 1 (by rfl) ⟨3568427, by rfl⟩ : syracuseStep 4757903 = 7136855) B7136855
theorem B3171935 : Blo 2113435 3171935 := bstep (se 1 (by rfl) ⟨2378951, by rfl⟩ : syracuseStep 3171935 = 4757903) B4757903
theorem B2114623 : Blo 2113435 2114623 := bstep (se 1 (by rfl) ⟨1585967, by rfl⟩ : syracuseStep 2114623 = 3171935) B3171935
theorem B3171941 : Blo 2113435 3171941 := bbase (se 4 (by rfl) ⟨297369, by rfl⟩ : syracuseStep 3171941 = 594739) (by norm_num)
theorem B2114627 : Blo 2113435 2114627 := bstep (se 1 (by rfl) ⟨1585970, by rfl⟩ : syracuseStep 2114627 = 3171941) B3171941
theorem B2540425 : Blo 2113435 2540425 := bbase (se 2 (by rfl) ⟨952659, by rfl⟩ : syracuseStep 2540425 = 1905319) (by norm_num)
theorem B3387233 : Blo 2113435 3387233 := bstep (se 2 (by rfl) ⟨1270212, by rfl⟩ : syracuseStep 3387233 = 2540425) B2540425
theorem B2258155 : Blo 2113435 2258155 := bstep (se 1 (by rfl) ⟨1693616, by rfl⟩ : syracuseStep 2258155 = 3387233) B3387233
theorem B3010873 : Blo 2113435 3010873 := bstep (se 2 (by rfl) ⟨1129077, by rfl⟩ : syracuseStep 3010873 = 2258155) B2258155
theorem B4014497 : Blo 2113435 4014497 := bstep (se 2 (by rfl) ⟨1505436, by rfl⟩ : syracuseStep 4014497 = 3010873) B3010873
theorem B2676331 : Blo 2113435 2676331 := bstep (se 1 (by rfl) ⟨2007248, by rfl⟩ : syracuseStep 2676331 = 4014497) B4014497
theorem B3568441 : Blo 2113435 3568441 := bstep (se 2 (by rfl) ⟨1338165, by rfl⟩ : syracuseStep 3568441 = 2676331) B2676331
theorem B4757921 : Blo 2113435 4757921 := bstep (se 2 (by rfl) ⟨1784220, by rfl⟩ : syracuseStep 4757921 = 3568441) B3568441
theorem B3171947 : Blo 2113435 3171947 := bstep (se 1 (by rfl) ⟨2378960, by rfl⟩ : syracuseStep 3171947 = 4757921) B4757921
theorem B2114631 : Blo 2113435 2114631 := bstep (se 1 (by rfl) ⟨1585973, by rfl⟩ : syracuseStep 2114631 = 3171947) B3171947
theorem B2378965 : Blo 2113435 2378965 := bbase (se 7 (by rfl) ⟨27878, by rfl⟩ : syracuseStep 2378965 = 55757) (by norm_num)
theorem B3171953 : Blo 2113435 3171953 := bstep (se 2 (by rfl) ⟨1189482, by rfl⟩ : syracuseStep 3171953 = 2378965) B2378965
theorem B2114635 : Blo 2113435 2114635 := bstep (se 1 (by rfl) ⟨1585976, by rfl⟩ : syracuseStep 2114635 = 3171953) B3171953
theorem B2676341 : Blo 2113435 2676341 := bbase (se 5 (by rfl) ⟨125453, by rfl⟩ : syracuseStep 2676341 = 250907) (by norm_num)
theorem B7136909 : Blo 2113435 7136909 := bstep (se 3 (by rfl) ⟨1338170, by rfl⟩ : syracuseStep 7136909 = 2676341) B2676341
theorem B4757939 : Blo 2113435 4757939 := bstep (se 1 (by rfl) ⟨3568454, by rfl⟩ : syracuseStep 4757939 = 7136909) B7136909
theorem B3171959 : Blo 2113435 3171959 := bstep (se 1 (by rfl) ⟨2378969, by rfl⟩ : syracuseStep 3171959 = 4757939) B4757939
theorem B2114639 : Blo 2113435 2114639 := bstep (se 1 (by rfl) ⟨1585979, by rfl⟩ : syracuseStep 2114639 = 3171959) B3171959
theorem B3171965 : Blo 2113435 3171965 := bbase (se 3 (by rfl) ⟨594743, by rfl⟩ : syracuseStep 3171965 = 1189487) (by norm_num)
theorem B2114643 : Blo 2113435 2114643 := bstep (se 1 (by rfl) ⟨1585982, by rfl⟩ : syracuseStep 2114643 = 3171965) B3171965
theorem B4757957 : Blo 2113435 4757957 := bbase (se 4 (by rfl) ⟨446058, by rfl⟩ : syracuseStep 4757957 = 892117) (by norm_num)
theorem B3171971 : Blo 2113435 3171971 := bstep (se 1 (by rfl) ⟨2378978, by rfl⟩ : syracuseStep 3171971 = 4757957) B4757957
theorem B2114647 : Blo 2113435 2114647 := bstep (se 1 (by rfl) ⟨1585985, by rfl⟩ : syracuseStep 2114647 = 3171971) B3171971
theorem B2858005 : Blo 2113435 2858005 := bbase (se 6 (by rfl) ⟨66984, by rfl⟩ : syracuseStep 2858005 = 133969) (by norm_num)
theorem B3810673 : Blo 2113435 3810673 := bstep (se 2 (by rfl) ⟨1429002, by rfl⟩ : syracuseStep 3810673 = 2858005) B2858005
theorem B5080897 : Blo 2113435 5080897 := bstep (se 2 (by rfl) ⟨1905336, by rfl⟩ : syracuseStep 5080897 = 3810673) B3810673
theorem B6774529 : Blo 2113435 6774529 := bstep (se 2 (by rfl) ⟨2540448, by rfl⟩ : syracuseStep 6774529 = 5080897) B5080897
theorem B9032705 : Blo 2113435 9032705 := bstep (se 2 (by rfl) ⟨3387264, by rfl⟩ : syracuseStep 9032705 = 6774529) B6774529
theorem B6021803 : Blo 2113435 6021803 := bstep (se 1 (by rfl) ⟨4516352, by rfl⟩ : syracuseStep 6021803 = 9032705) B9032705
theorem B4014535 : Blo 2113435 4014535 := bstep (se 1 (by rfl) ⟨3010901, by rfl⟩ : syracuseStep 4014535 = 6021803) B6021803
theorem B5352713 : Blo 2113435 5352713 := bstep (se 2 (by rfl) ⟨2007267, by rfl⟩ : syracuseStep 5352713 = 4014535) B4014535
theorem B3568475 : Blo 2113435 3568475 := bstep (se 1 (by rfl) ⟨2676356, by rfl⟩ : syracuseStep 3568475 = 5352713) B5352713
theorem B2378983 : Blo 2113435 2378983 := bstep (se 1 (by rfl) ⟨1784237, by rfl⟩ : syracuseStep 2378983 = 3568475) B3568475
theorem B3171977 : Blo 2113435 3171977 := bstep (se 2 (by rfl) ⟨1189491, by rfl⟩ : syracuseStep 3171977 = 2378983) B2378983
theorem B2114651 : Blo 2113435 2114651 := bstep (se 1 (by rfl) ⟨1585988, by rfl⟩ : syracuseStep 2114651 = 3171977) B3171977
theorem B10705445 : Blo 2113435 10705445 := bbase (se 4 (by rfl) ⟨1003635, by rfl⟩ : syracuseStep 10705445 = 2007271) (by norm_num)
theorem B7136963 : Blo 2113435 7136963 := bstep (se 1 (by rfl) ⟨5352722, by rfl⟩ : syracuseStep 7136963 = 10705445) B10705445
theorem B4757975 : Blo 2113435 4757975 := bstep (se 1 (by rfl) ⟨3568481, by rfl⟩ : syracuseStep 4757975 = 7136963) B7136963
theorem B3171983 : Blo 2113435 3171983 := bstep (se 1 (by rfl) ⟨2378987, by rfl⟩ : syracuseStep 3171983 = 4757975) B4757975
theorem B2114655 : Blo 2113435 2114655 := bstep (se 1 (by rfl) ⟨1585991, by rfl⟩ : syracuseStep 2114655 = 3171983) B3171983
theorem B3171989 : Blo 2113435 3171989 := bbase (se 6 (by rfl) ⟨74343, by rfl⟩ : syracuseStep 3171989 = 148687) (by norm_num)
theorem B2114659 : Blo 2113435 2114659 := bstep (se 1 (by rfl) ⟨1585994, by rfl⟩ : syracuseStep 2114659 = 3171989) B3171989
theorem B5080925 : Blo 2113435 5080925 := bbase (se 3 (by rfl) ⟨952673, by rfl⟩ : syracuseStep 5080925 = 1905347) (by norm_num)
theorem B13549133 : Blo 2113435 13549133 := bstep (se 3 (by rfl) ⟨2540462, by rfl⟩ : syracuseStep 13549133 = 5080925) B5080925
theorem B9032755 : Blo 2113435 9032755 := bstep (se 1 (by rfl) ⟨6774566, by rfl⟩ : syracuseStep 9032755 = 13549133) B13549133
theorem B12043673 : Blo 2113435 12043673 := bstep (se 2 (by rfl) ⟨4516377, by rfl⟩ : syracuseStep 12043673 = 9032755) B9032755
theorem B8029115 : Blo 2113435 8029115 := bstep (se 1 (by rfl) ⟨6021836, by rfl⟩ : syracuseStep 8029115 = 12043673) B12043673
theorem B5352743 : Blo 2113435 5352743 := bstep (se 1 (by rfl) ⟨4014557, by rfl⟩ : syracuseStep 5352743 = 8029115) B8029115
theorem B3568495 : Blo 2113435 3568495 := bstep (se 1 (by rfl) ⟨2676371, by rfl⟩ : syracuseStep 3568495 = 5352743) B5352743
theorem B4757993 : Blo 2113435 4757993 := bstep (se 2 (by rfl) ⟨1784247, by rfl⟩ : syracuseStep 4757993 = 3568495) B3568495
theorem B3171995 : Blo 2113435 3171995 := bstep (se 1 (by rfl) ⟨2378996, by rfl⟩ : syracuseStep 3171995 = 4757993) B4757993
theorem B2114663 : Blo 2113435 2114663 := bstep (se 1 (by rfl) ⟨1585997, by rfl⟩ : syracuseStep 2114663 = 3171995) B3171995
theorem B2379001 : Blo 2113435 2379001 := bbase (se 2 (by rfl) ⟨892125, by rfl⟩ : syracuseStep 2379001 = 1784251) (by norm_num)
theorem B3172001 : Blo 2113435 3172001 := bstep (se 2 (by rfl) ⟨1189500, by rfl⟩ : syracuseStep 3172001 = 2379001) B2379001
theorem B2114667 : Blo 2113435 2114667 := bstep (se 1 (by rfl) ⟨1586000, by rfl⟩ : syracuseStep 2114667 = 3172001) B3172001
theorem B9032789 : Blo 2113435 9032789 := bbase (se 8 (by rfl) ⟨52926, by rfl⟩ : syracuseStep 9032789 = 105853) (by norm_num)
theorem B6021859 : Blo 2113435 6021859 := bstep (se 1 (by rfl) ⟨4516394, by rfl⟩ : syracuseStep 6021859 = 9032789) B9032789
theorem B8029145 : Blo 2113435 8029145 := bstep (se 2 (by rfl) ⟨3010929, by rfl⟩ : syracuseStep 8029145 = 6021859) B6021859
theorem B5352763 : Blo 2113435 5352763 := bstep (se 1 (by rfl) ⟨4014572, by rfl⟩ : syracuseStep 5352763 = 8029145) B8029145
theorem B7137017 : Blo 2113435 7137017 := bstep (se 2 (by rfl) ⟨2676381, by rfl⟩ : syracuseStep 7137017 = 5352763) B5352763
theorem B4758011 : Blo 2113435 4758011 := bstep (se 1 (by rfl) ⟨3568508, by rfl⟩ : syracuseStep 4758011 = 7137017) B7137017
theorem B3172007 : Blo 2113435 3172007 := bstep (se 1 (by rfl) ⟨2379005, by rfl⟩ : syracuseStep 3172007 = 4758011) B4758011
theorem B2114671 : Blo 2113435 2114671 := bstep (se 1 (by rfl) ⟨1586003, by rfl⟩ : syracuseStep 2114671 = 3172007) B3172007
theorem B3172013 : Blo 2113435 3172013 := bbase (se 3 (by rfl) ⟨594752, by rfl⟩ : syracuseStep 3172013 = 1189505) (by norm_num)
theorem B2114675 : Blo 2113435 2114675 := bstep (se 1 (by rfl) ⟨1586006, by rfl⟩ : syracuseStep 2114675 = 3172013) B3172013
theorem B4758029 : Blo 2113435 4758029 := bbase (se 3 (by rfl) ⟨892130, by rfl⟩ : syracuseStep 4758029 = 1784261) (by norm_num)
theorem B3172019 : Blo 2113435 3172019 := bstep (se 1 (by rfl) ⟨2379014, by rfl⟩ : syracuseStep 3172019 = 4758029) B4758029
theorem B2114679 : Blo 2113435 2114679 := bstep (se 1 (by rfl) ⟨1586009, by rfl⟩ : syracuseStep 2114679 = 3172019) B3172019
theorem B2676397 : Blo 2113435 2676397 := bbase (se 3 (by rfl) ⟨501824, by rfl⟩ : syracuseStep 2676397 = 1003649) (by norm_num)
theorem B3568529 : Blo 2113435 3568529 := bstep (se 2 (by rfl) ⟨1338198, by rfl⟩ : syracuseStep 3568529 = 2676397) B2676397
theorem B2379019 : Blo 2113435 2379019 := bstep (se 1 (by rfl) ⟨1784264, by rfl⟩ : syracuseStep 2379019 = 3568529) B3568529
theorem B3172025 : Blo 2113435 3172025 := bstep (se 2 (by rfl) ⟨1189509, by rfl⟩ : syracuseStep 3172025 = 2379019) B2379019
theorem B2114683 : Blo 2113435 2114683 := bstep (se 1 (by rfl) ⟨1586012, by rfl⟩ : syracuseStep 2114683 = 3172025) B3172025
theorem B2858053 : Blo 2113435 2858053 := bbase (se 4 (by rfl) ⟨267942, by rfl⟩ : syracuseStep 2858053 = 535885) (by norm_num)
theorem B3810737 : Blo 2113435 3810737 := bstep (se 2 (by rfl) ⟨1429026, by rfl⟩ : syracuseStep 3810737 = 2858053) B2858053
theorem B2540491 : Blo 2113435 2540491 := bstep (se 1 (by rfl) ⟨1905368, by rfl⟩ : syracuseStep 2540491 = 3810737) B3810737
theorem B13549285 : Blo 2113435 13549285 := bstep (se 4 (by rfl) ⟨1270245, by rfl⟩ : syracuseStep 13549285 = 2540491) B2540491
theorem B18065713 : Blo 2113435 18065713 := bstep (se 2 (by rfl) ⟨6774642, by rfl⟩ : syracuseStep 18065713 = 13549285) B13549285
theorem B24087617 : Blo 2113435 24087617 := bstep (se 2 (by rfl) ⟨9032856, by rfl⟩ : syracuseStep 24087617 = 18065713) B18065713
theorem B16058411 : Blo 2113435 16058411 := bstep (se 1 (by rfl) ⟨12043808, by rfl⟩ : syracuseStep 16058411 = 24087617) B24087617
theorem B10705607 : Blo 2113435 10705607 := bstep (se 1 (by rfl) ⟨8029205, by rfl⟩ : syracuseStep 10705607 = 16058411) B16058411
theorem B7137071 : Blo 2113435 7137071 := bstep (se 1 (by rfl) ⟨5352803, by rfl⟩ : syracuseStep 7137071 = 10705607) B10705607
theorem B4758047 : Blo 2113435 4758047 := bstep (se 1 (by rfl) ⟨3568535, by rfl⟩ : syracuseStep 4758047 = 7137071) B7137071
theorem B3172031 : Blo 2113435 3172031 := bstep (se 1 (by rfl) ⟨2379023, by rfl⟩ : syracuseStep 3172031 = 4758047) B4758047
theorem B2114687 : Blo 2113435 2114687 := bstep (se 1 (by rfl) ⟨1586015, by rfl⟩ : syracuseStep 2114687 = 3172031) B3172031
theorem B3172037 : Blo 2113435 3172037 := bbase (se 4 (by rfl) ⟨297378, by rfl⟩ : syracuseStep 3172037 = 594757) (by norm_num)
theorem B2114691 : Blo 2113435 2114691 := bstep (se 1 (by rfl) ⟨1586018, by rfl⟩ : syracuseStep 2114691 = 3172037) B3172037
theorem B3568549 : Blo 2113435 3568549 := bbase (se 4 (by rfl) ⟨334551, by rfl⟩ : syracuseStep 3568549 = 669103) (by norm_num)
theorem B4758065 : Blo 2113435 4758065 := bstep (se 2 (by rfl) ⟨1784274, by rfl⟩ : syracuseStep 4758065 = 3568549) B3568549
theorem B3172043 : Blo 2113435 3172043 := bstep (se 1 (by rfl) ⟨2379032, by rfl⟩ : syracuseStep 3172043 = 4758065) B4758065
theorem B2114695 : Blo 2113435 2114695 := bstep (se 1 (by rfl) ⟨1586021, by rfl⟩ : syracuseStep 2114695 = 3172043) B3172043
theorem B2379037 : Blo 2113435 2379037 := bbase (se 3 (by rfl) ⟨446069, by rfl⟩ : syracuseStep 2379037 = 892139) (by norm_num)
theorem B3172049 : Blo 2113435 3172049 := bstep (se 2 (by rfl) ⟨1189518, by rfl⟩ : syracuseStep 3172049 = 2379037) B2379037
theorem B2114699 : Blo 2113435 2114699 := bstep (se 1 (by rfl) ⟨1586024, by rfl⟩ : syracuseStep 2114699 = 3172049) B3172049
theorem B7137125 : Blo 2113435 7137125 := bbase (se 4 (by rfl) ⟨669105, by rfl⟩ : syracuseStep 7137125 = 1338211) (by norm_num)
theorem B4758083 : Blo 2113435 4758083 := bstep (se 1 (by rfl) ⟨3568562, by rfl⟩ : syracuseStep 4758083 = 7137125) B7137125
theorem B3172055 : Blo 2113435 3172055 := bstep (se 1 (by rfl) ⟨2379041, by rfl⟩ : syracuseStep 3172055 = 4758083) B4758083
theorem B2114703 : Blo 2113435 2114703 := bstep (se 1 (by rfl) ⟨1586027, by rfl⟩ : syracuseStep 2114703 = 3172055) B3172055
theorem B3172061 : Blo 2113435 3172061 := bbase (se 3 (by rfl) ⟨594761, by rfl⟩ : syracuseStep 3172061 = 1189523) (by norm_num)
theorem B2114707 : Blo 2113435 2114707 := bstep (se 1 (by rfl) ⟨1586030, by rfl⟩ : syracuseStep 2114707 = 3172061) B3172061
theorem B4758101 : Blo 2113435 4758101 := bbase (se 8 (by rfl) ⟨27879, by rfl⟩ : syracuseStep 4758101 = 55759) (by norm_num)
theorem B3172067 : Blo 2113435 3172067 := bstep (se 1 (by rfl) ⟨2379050, by rfl⟩ : syracuseStep 3172067 = 4758101) B4758101
theorem B2114711 : Blo 2113435 2114711 := bstep (se 1 (by rfl) ⟨1586033, by rfl⟩ : syracuseStep 2114711 = 3172067) B3172067
theorem B2575189 : Blo 2113435 2575189 := bbase (se 9 (by rfl) ⟨7544, by rfl⟩ : syracuseStep 2575189 = 15089) (by norm_num)
theorem B3433585 : Blo 2113435 3433585 := bstep (se 2 (by rfl) ⟨1287594, by rfl⟩ : syracuseStep 3433585 = 2575189) B2575189
theorem B4578113 : Blo 2113435 4578113 := bstep (se 2 (by rfl) ⟨1716792, by rfl⟩ : syracuseStep 4578113 = 3433585) B3433585
theorem B3052075 : Blo 2113435 3052075 := bstep (se 1 (by rfl) ⟨2289056, by rfl⟩ : syracuseStep 3052075 = 4578113) B4578113
theorem B4069433 : Blo 2113435 4069433 := bstep (se 2 (by rfl) ⟨1526037, by rfl⟩ : syracuseStep 4069433 = 3052075) B3052075
theorem B2712955 : Blo 2113435 2712955 := bstep (se 1 (by rfl) ⟨2034716, by rfl⟩ : syracuseStep 2712955 = 4069433) B4069433
theorem B3617273 : Blo 2113435 3617273 := bstep (se 2 (by rfl) ⟨1356477, by rfl⟩ : syracuseStep 3617273 = 2712955) B2712955
theorem B2411515 : Blo 2113435 2411515 := bstep (se 1 (by rfl) ⟨1808636, by rfl⟩ : syracuseStep 2411515 = 3617273) B3617273
theorem B12861413 : Blo 2113435 12861413 := bstep (se 4 (by rfl) ⟨1205757, by rfl⟩ : syracuseStep 12861413 = 2411515) B2411515
theorem B8574275 : Blo 2113435 8574275 := bstep (se 1 (by rfl) ⟨6430706, by rfl⟩ : syracuseStep 8574275 = 12861413) B12861413
theorem B5716183 : Blo 2113435 5716183 := bstep (se 1 (by rfl) ⟨4287137, by rfl⟩ : syracuseStep 5716183 = 8574275) B8574275
theorem B7621577 : Blo 2113435 7621577 := bstep (se 2 (by rfl) ⟨2858091, by rfl⟩ : syracuseStep 7621577 = 5716183) B5716183
theorem B5081051 : Blo 2113435 5081051 := bstep (se 1 (by rfl) ⟨3810788, by rfl⟩ : syracuseStep 5081051 = 7621577) B7621577
theorem B3387367 : Blo 2113435 3387367 := bstep (se 1 (by rfl) ⟨2540525, by rfl⟩ : syracuseStep 3387367 = 5081051) B5081051
theorem B4516489 : Blo 2113435 4516489 := bstep (se 2 (by rfl) ⟨1693683, by rfl⟩ : syracuseStep 4516489 = 3387367) B3387367
theorem B6021985 : Blo 2113435 6021985 := bstep (se 2 (by rfl) ⟨2258244, by rfl⟩ : syracuseStep 6021985 = 4516489) B4516489
theorem B8029313 : Blo 2113435 8029313 := bstep (se 2 (by rfl) ⟨3010992, by rfl⟩ : syracuseStep 8029313 = 6021985) B6021985
theorem B5352875 : Blo 2113435 5352875 := bstep (se 1 (by rfl) ⟨4014656, by rfl⟩ : syracuseStep 5352875 = 8029313) B8029313
theorem B3568583 : Blo 2113435 3568583 := bstep (se 1 (by rfl) ⟨2676437, by rfl⟩ : syracuseStep 3568583 = 5352875) B5352875
theorem B2379055 : Blo 2113435 2379055 := bstep (se 1 (by rfl) ⟨1784291, by rfl⟩ : syracuseStep 2379055 = 3568583) B3568583
theorem B3172073 : Blo 2113435 3172073 := bstep (se 2 (by rfl) ⟨1189527, by rfl⟩ : syracuseStep 3172073 = 2379055) B2379055
theorem B2114715 : Blo 2113435 2114715 := bstep (se 1 (by rfl) ⟨1586036, by rfl⟩ : syracuseStep 2114715 = 3172073) B3172073
theorem B7621589 : Blo 2113435 7621589 := bbase (se 7 (by rfl) ⟨89315, by rfl⟩ : syracuseStep 7621589 = 178631) (by norm_num)
theorem B5081059 : Blo 2113435 5081059 := bstep (se 1 (by rfl) ⟨3810794, by rfl⟩ : syracuseStep 5081059 = 7621589) B7621589
theorem B27098981 : Blo 2113435 27098981 := bstep (se 4 (by rfl) ⟨2540529, by rfl⟩ : syracuseStep 27098981 = 5081059) B5081059
theorem B18065987 : Blo 2113435 18065987 := bstep (se 1 (by rfl) ⟨13549490, by rfl⟩ : syracuseStep 18065987 = 27098981) B27098981
theorem B12043991 : Blo 2113435 12043991 := bstep (se 1 (by rfl) ⟨9032993, by rfl⟩ : syracuseStep 12043991 = 18065987) B18065987
theorem B8029327 : Blo 2113435 8029327 := bstep (se 1 (by rfl) ⟨6021995, by rfl⟩ : syracuseStep 8029327 = 12043991) B12043991
theorem B10705769 : Blo 2113435 10705769 := bstep (se 2 (by rfl) ⟨4014663, by rfl⟩ : syracuseStep 10705769 = 8029327) B8029327
theorem B7137179 : Blo 2113435 7137179 := bstep (se 1 (by rfl) ⟨5352884, by rfl⟩ : syracuseStep 7137179 = 10705769) B10705769
theorem B4758119 : Blo 2113435 4758119 := bstep (se 1 (by rfl) ⟨3568589, by rfl⟩ : syracuseStep 4758119 = 7137179) B7137179
theorem B3172079 : Blo 2113435 3172079 := bstep (se 1 (by rfl) ⟨2379059, by rfl⟩ : syracuseStep 3172079 = 4758119) B4758119
theorem B2114719 : Blo 2113435 2114719 := bstep (se 1 (by rfl) ⟨1586039, by rfl⟩ : syracuseStep 2114719 = 3172079) B3172079
theorem B3172085 : Blo 2113435 3172085 := bbase (se 5 (by rfl) ⟨148691, by rfl⟩ : syracuseStep 3172085 = 297383) (by norm_num)
theorem B2114723 : Blo 2113435 2114723 := bstep (se 1 (by rfl) ⟨1586042, by rfl⟩ : syracuseStep 2114723 = 3172085) B3172085
theorem B9033029 : Blo 2113435 9033029 := bbase (se 4 (by rfl) ⟨846846, by rfl⟩ : syracuseStep 9033029 = 1693693) (by norm_num)
theorem B6022019 : Blo 2113435 6022019 := bstep (se 1 (by rfl) ⟨4516514, by rfl⟩ : syracuseStep 6022019 = 9033029) B9033029
theorem B4014679 : Blo 2113435 4014679 := bstep (se 1 (by rfl) ⟨3011009, by rfl⟩ : syracuseStep 4014679 = 6022019) B6022019
theorem B5352905 : Blo 2113435 5352905 := bstep (se 2 (by rfl) ⟨2007339, by rfl⟩ : syracuseStep 5352905 = 4014679) B4014679
theorem B3568603 : Blo 2113435 3568603 := bstep (se 1 (by rfl) ⟨2676452, by rfl⟩ : syracuseStep 3568603 = 5352905) B5352905
theorem B4758137 : Blo 2113435 4758137 := bstep (se 2 (by rfl) ⟨1784301, by rfl⟩ : syracuseStep 4758137 = 3568603) B3568603
theorem B3172091 : Blo 2113435 3172091 := bstep (se 1 (by rfl) ⟨2379068, by rfl⟩ : syracuseStep 3172091 = 4758137) B4758137
theorem B2114727 : Blo 2113435 2114727 := bstep (se 1 (by rfl) ⟨1586045, by rfl⟩ : syracuseStep 2114727 = 3172091) B3172091
theorem B2379073 : Blo 2113435 2379073 := bbase (se 2 (by rfl) ⟨892152, by rfl⟩ : syracuseStep 2379073 = 1784305) (by norm_num)
theorem B3172097 : Blo 2113435 3172097 := bstep (se 2 (by rfl) ⟨1189536, by rfl⟩ : syracuseStep 3172097 = 2379073) B2379073
theorem B2114731 : Blo 2113435 2114731 := bstep (se 1 (by rfl) ⟨1586048, by rfl⟩ : syracuseStep 2114731 = 3172097) B3172097
theorem B5352925 : Blo 2113435 5352925 := bbase (se 3 (by rfl) ⟨1003673, by rfl⟩ : syracuseStep 5352925 = 2007347) (by norm_num)
theorem B7137233 : Blo 2113435 7137233 := bstep (se 2 (by rfl) ⟨2676462, by rfl⟩ : syracuseStep 7137233 = 5352925) B5352925
theorem B4758155 : Blo 2113435 4758155 := bstep (se 1 (by rfl) ⟨3568616, by rfl⟩ : syracuseStep 4758155 = 7137233) B7137233
theorem B3172103 : Blo 2113435 3172103 := bstep (se 1 (by rfl) ⟨2379077, by rfl⟩ : syracuseStep 3172103 = 4758155) B4758155
theorem B2114735 : Blo 2113435 2114735 := bstep (se 1 (by rfl) ⟨1586051, by rfl⟩ : syracuseStep 2114735 = 3172103) B3172103
theorem B3172109 : Blo 2113435 3172109 := bbase (se 3 (by rfl) ⟨594770, by rfl⟩ : syracuseStep 3172109 = 1189541) (by norm_num)
theorem B2114739 : Blo 2113435 2114739 := bstep (se 1 (by rfl) ⟨1586054, by rfl⟩ : syracuseStep 2114739 = 3172109) B3172109
theorem B4758173 : Blo 2113435 4758173 := bbase (se 3 (by rfl) ⟨892157, by rfl⟩ : syracuseStep 4758173 = 1784315) (by norm_num)
theorem B3172115 : Blo 2113435 3172115 := bstep (se 1 (by rfl) ⟨2379086, by rfl⟩ : syracuseStep 3172115 = 4758173) B4758173
theorem B2114743 : Blo 2113435 2114743 := bstep (se 1 (by rfl) ⟨1586057, by rfl⟩ : syracuseStep 2114743 = 3172115) B3172115
theorem B3568637 : Blo 2113435 3568637 := bbase (se 3 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 3568637 = 1338239) (by norm_num)
theorem B2379091 : Blo 2113435 2379091 := bstep (se 1 (by rfl) ⟨1784318, by rfl⟩ : syracuseStep 2379091 = 3568637) B3568637
theorem B3172121 : Blo 2113435 3172121 := bstep (se 2 (by rfl) ⟨1189545, by rfl⟩ : syracuseStep 3172121 = 2379091) B2379091
theorem B2114747 : Blo 2113435 2114747 := bstep (se 1 (by rfl) ⟨1586060, by rfl⟩ : syracuseStep 2114747 = 3172121) B3172121
theorem B4516565 : Blo 2113435 4516565 := bbase (se 7 (by rfl) ⟨52928, by rfl⟩ : syracuseStep 4516565 = 105857) (by norm_num)
theorem B12044173 : Blo 2113435 12044173 := bstep (se 3 (by rfl) ⟨2258282, by rfl⟩ : syracuseStep 12044173 = 4516565) B4516565
theorem B16058897 : Blo 2113435 16058897 := bstep (se 2 (by rfl) ⟨6022086, by rfl⟩ : syracuseStep 16058897 = 12044173) B12044173
theorem B10705931 : Blo 2113435 10705931 := bstep (se 1 (by rfl) ⟨8029448, by rfl⟩ : syracuseStep 10705931 = 16058897) B16058897
theorem B7137287 : Blo 2113435 7137287 := bstep (se 1 (by rfl) ⟨5352965, by rfl⟩ : syracuseStep 7137287 = 10705931) B10705931
theorem B4758191 : Blo 2113435 4758191 := bstep (se 1 (by rfl) ⟨3568643, by rfl⟩ : syracuseStep 4758191 = 7137287) B7137287
theorem B3172127 : Blo 2113435 3172127 := bstep (se 1 (by rfl) ⟨2379095, by rfl⟩ : syracuseStep 3172127 = 4758191) B4758191
theorem B2114751 : Blo 2113435 2114751 := bstep (se 1 (by rfl) ⟨1586063, by rfl⟩ : syracuseStep 2114751 = 3172127) B3172127
theorem B3172133 : Blo 2113435 3172133 := bbase (se 4 (by rfl) ⟨297387, by rfl⟩ : syracuseStep 3172133 = 594775) (by norm_num)
theorem B2114755 : Blo 2113435 2114755 := bstep (se 1 (by rfl) ⟨1586066, by rfl⟩ : syracuseStep 2114755 = 3172133) B3172133
theorem B2676493 : Blo 2113435 2676493 := bbase (se 3 (by rfl) ⟨501842, by rfl⟩ : syracuseStep 2676493 = 1003685) (by norm_num)
theorem B3568657 : Blo 2113435 3568657 := bstep (se 2 (by rfl) ⟨1338246, by rfl⟩ : syracuseStep 3568657 = 2676493) B2676493
theorem B4758209 : Blo 2113435 4758209 := bstep (se 2 (by rfl) ⟨1784328, by rfl⟩ : syracuseStep 4758209 = 3568657) B3568657
theorem B3172139 : Blo 2113435 3172139 := bstep (se 1 (by rfl) ⟨2379104, by rfl⟩ : syracuseStep 3172139 = 4758209) B4758209
theorem B2114759 : Blo 2113435 2114759 := bstep (se 1 (by rfl) ⟨1586069, by rfl⟩ : syracuseStep 2114759 = 3172139) B3172139
theorem B2379109 : Blo 2113435 2379109 := bbase (se 4 (by rfl) ⟨223041, by rfl⟩ : syracuseStep 2379109 = 446083) (by norm_num)
theorem B3172145 : Blo 2113435 3172145 := bstep (se 2 (by rfl) ⟨1189554, by rfl⟩ : syracuseStep 3172145 = 2379109) B2379109
theorem B2114763 : Blo 2113435 2114763 := bstep (se 1 (by rfl) ⟨1586072, by rfl⟩ : syracuseStep 2114763 = 3172145) B3172145
theorem B6022133 : Blo 2113435 6022133 := bbase (se 5 (by rfl) ⟨282287, by rfl⟩ : syracuseStep 6022133 = 564575) (by norm_num)
theorem B4014755 : Blo 2113435 4014755 := bstep (se 1 (by rfl) ⟨3011066, by rfl⟩ : syracuseStep 4014755 = 6022133) B6022133
theorem B2676503 : Blo 2113435 2676503 := bstep (se 1 (by rfl) ⟨2007377, by rfl⟩ : syracuseStep 2676503 = 4014755) B4014755
theorem B7137341 : Blo 2113435 7137341 := bstep (se 3 (by rfl) ⟨1338251, by rfl⟩ : syracuseStep 7137341 = 2676503) B2676503
theorem B4758227 : Blo 2113435 4758227 := bstep (se 1 (by rfl) ⟨3568670, by rfl⟩ : syracuseStep 4758227 = 7137341) B7137341
theorem B3172151 : Blo 2113435 3172151 := bstep (se 1 (by rfl) ⟨2379113, by rfl⟩ : syracuseStep 3172151 = 4758227) B4758227
theorem B2114767 : Blo 2113435 2114767 := bstep (se 1 (by rfl) ⟨1586075, by rfl⟩ : syracuseStep 2114767 = 3172151) B3172151
theorem B3172157 : Blo 2113435 3172157 := bbase (se 3 (by rfl) ⟨594779, by rfl⟩ : syracuseStep 3172157 = 1189559) (by norm_num)
theorem B2114771 : Blo 2113435 2114771 := bstep (se 1 (by rfl) ⟨1586078, by rfl⟩ : syracuseStep 2114771 = 3172157) B3172157
theorem B4758245 : Blo 2113435 4758245 := bbase (se 4 (by rfl) ⟨446085, by rfl⟩ : syracuseStep 4758245 = 892171) (by norm_num)
theorem B3172163 : Blo 2113435 3172163 := bstep (se 1 (by rfl) ⟨2379122, by rfl⟩ : syracuseStep 3172163 = 4758245) B4758245
theorem B2114775 : Blo 2113435 2114775 := bstep (se 1 (by rfl) ⟨1586081, by rfl⟩ : syracuseStep 2114775 = 3172163) B3172163
theorem B5353037 : Blo 2113435 5353037 := bbase (se 3 (by rfl) ⟨1003694, by rfl⟩ : syracuseStep 5353037 = 2007389) (by norm_num)
theorem B3568691 : Blo 2113435 3568691 := bstep (se 1 (by rfl) ⟨2676518, by rfl⟩ : syracuseStep 3568691 = 5353037) B5353037
theorem B2379127 : Blo 2113435 2379127 := bstep (se 1 (by rfl) ⟨1784345, by rfl⟩ : syracuseStep 2379127 = 3568691) B3568691
theorem B3172169 : Blo 2113435 3172169 := bstep (se 2 (by rfl) ⟨1189563, by rfl⟩ : syracuseStep 3172169 = 2379127) B2379127
theorem B2114779 : Blo 2113435 2114779 := bstep (se 1 (by rfl) ⟨1586084, by rfl⟩ : syracuseStep 2114779 = 3172169) B3172169
theorem B2258317 : Blo 2113435 2258317 := bbase (se 3 (by rfl) ⟨423434, by rfl⟩ : syracuseStep 2258317 = 846869) (by norm_num)
theorem B3011089 : Blo 2113435 3011089 := bstep (se 2 (by rfl) ⟨1129158, by rfl⟩ : syracuseStep 3011089 = 2258317) B2258317
theorem B4014785 : Blo 2113435 4014785 := bstep (se 2 (by rfl) ⟨1505544, by rfl⟩ : syracuseStep 4014785 = 3011089) B3011089
theorem B10706093 : Blo 2113435 10706093 := bstep (se 3 (by rfl) ⟨2007392, by rfl⟩ : syracuseStep 10706093 = 4014785) B4014785
theorem B7137395 : Blo 2113435 7137395 := bstep (se 1 (by rfl) ⟨5353046, by rfl⟩ : syracuseStep 7137395 = 10706093) B10706093
theorem B4758263 : Blo 2113435 4758263 := bstep (se 1 (by rfl) ⟨3568697, by rfl⟩ : syracuseStep 4758263 = 7137395) B7137395
theorem B3172175 : Blo 2113435 3172175 := bstep (se 1 (by rfl) ⟨2379131, by rfl⟩ : syracuseStep 3172175 = 4758263) B4758263
theorem B2114783 : Blo 2113435 2114783 := bstep (se 1 (by rfl) ⟨1586087, by rfl⟩ : syracuseStep 2114783 = 3172175) B3172175
theorem B3172181 : Blo 2113435 3172181 := bbase (se 9 (by rfl) ⟨9293, by rfl⟩ : syracuseStep 3172181 = 18587) (by norm_num)
theorem B2114787 : Blo 2113435 2114787 := bstep (se 1 (by rfl) ⟨1586090, by rfl⟩ : syracuseStep 2114787 = 3172181) B3172181
theorem B3810925 : Blo 2113435 3810925 := bbase (se 3 (by rfl) ⟨714548, by rfl⟩ : syracuseStep 3810925 = 1429097) (by norm_num)
theorem B5081233 : Blo 2113435 5081233 := bstep (se 2 (by rfl) ⟨1905462, by rfl⟩ : syracuseStep 5081233 = 3810925) B3810925
theorem B6774977 : Blo 2113435 6774977 := bstep (se 2 (by rfl) ⟨2540616, by rfl⟩ : syracuseStep 6774977 = 5081233) B5081233
theorem B4516651 : Blo 2113435 4516651 := bstep (se 1 (by rfl) ⟨3387488, by rfl⟩ : syracuseStep 4516651 = 6774977) B6774977
theorem B6022201 : Blo 2113435 6022201 := bstep (se 2 (by rfl) ⟨2258325, by rfl⟩ : syracuseStep 6022201 = 4516651) B4516651
theorem B8029601 : Blo 2113435 8029601 := bstep (se 2 (by rfl) ⟨3011100, by rfl⟩ : syracuseStep 8029601 = 6022201) B6022201
theorem B5353067 : Blo 2113435 5353067 := bstep (se 1 (by rfl) ⟨4014800, by rfl⟩ : syracuseStep 5353067 = 8029601) B8029601
theorem B3568711 : Blo 2113435 3568711 := bstep (se 1 (by rfl) ⟨2676533, by rfl⟩ : syracuseStep 3568711 = 5353067) B5353067
theorem B4758281 : Blo 2113435 4758281 := bstep (se 2 (by rfl) ⟨1784355, by rfl⟩ : syracuseStep 4758281 = 3568711) B3568711
theorem B3172187 : Blo 2113435 3172187 := bstep (se 1 (by rfl) ⟨2379140, by rfl⟩ : syracuseStep 3172187 = 4758281) B4758281
theorem B2114791 : Blo 2113435 2114791 := bstep (se 1 (by rfl) ⟨1586093, by rfl⟩ : syracuseStep 2114791 = 3172187) B3172187
theorem B2379145 : Blo 2113435 2379145 := bbase (se 2 (by rfl) ⟨892179, by rfl⟩ : syracuseStep 2379145 = 1784359) (by norm_num)
theorem B3172193 : Blo 2113435 3172193 := bstep (se 2 (by rfl) ⟨1189572, by rfl⟩ : syracuseStep 3172193 = 2379145) B2379145
theorem B2114795 : Blo 2113435 2114795 := bstep (se 1 (by rfl) ⟨1586096, by rfl⟩ : syracuseStep 2114795 = 3172193) B3172193
theorem B3480565 : Blo 2113435 3480565 := bbase (se 5 (by rfl) ⟨163151, by rfl⟩ : syracuseStep 3480565 = 326303) (by norm_num)
theorem B4640753 : Blo 2113435 4640753 := bstep (se 2 (by rfl) ⟨1740282, by rfl⟩ : syracuseStep 4640753 = 3480565) B3480565
theorem B792021845 : Blo 2113435 792021845 := bstep (se 9 (by rfl) ⟨2320376, by rfl⟩ : syracuseStep 792021845 = 4640753) B4640753
theorem B2112058253 : Blo 2113435 2112058253 := bstep (se 3 (by rfl) ⟨396010922, by rfl⟩ : syracuseStep 2112058253 = 792021845) B792021845
theorem B1408038835 : Blo 2113435 1408038835 := bstep (se 1 (by rfl) ⟨1056029126, by rfl⟩ : syracuseStep 1408038835 = 2112058253) B2112058253
theorem B1877385113 : Blo 2113435 1877385113 := bstep (se 2 (by rfl) ⟨704019417, by rfl⟩ : syracuseStep 1877385113 = 1408038835) B1408038835
theorem B1251590075 : Blo 2113435 1251590075 := bstep (se 1 (by rfl) ⟨938692556, by rfl⟩ : syracuseStep 1251590075 = 1877385113) B1877385113
theorem B834393383 : Blo 2113435 834393383 := bstep (se 1 (by rfl) ⟨625795037, by rfl⟩ : syracuseStep 834393383 = 1251590075) B1251590075
theorem B556262255 : Blo 2113435 556262255 := bstep (se 1 (by rfl) ⟨417196691, by rfl⟩ : syracuseStep 556262255 = 834393383) B834393383
theorem B370841503 : Blo 2113435 370841503 := bstep (se 1 (by rfl) ⟨278131127, by rfl⟩ : syracuseStep 370841503 = 556262255) B556262255
theorem B494455337 : Blo 2113435 494455337 := bstep (se 2 (by rfl) ⟨185420751, by rfl⟩ : syracuseStep 494455337 = 370841503) B370841503
theorem B329636891 : Blo 2113435 329636891 := bstep (se 1 (by rfl) ⟨247227668, by rfl⟩ : syracuseStep 329636891 = 494455337) B494455337
theorem B879031709 : Blo 2113435 879031709 := bstep (se 3 (by rfl) ⟨164818445, by rfl⟩ : syracuseStep 879031709 = 329636891) B329636891
theorem B586021139 : Blo 2113435 586021139 := bstep (se 1 (by rfl) ⟨439515854, by rfl⟩ : syracuseStep 586021139 = 879031709) B879031709
theorem B390680759 : Blo 2113435 390680759 := bstep (se 1 (by rfl) ⟨293010569, by rfl⟩ : syracuseStep 390680759 = 586021139) B586021139
theorem B260453839 : Blo 2113435 260453839 := bstep (se 1 (by rfl) ⟨195340379, by rfl⟩ : syracuseStep 260453839 = 390680759) B390680759
theorem B347271785 : Blo 2113435 347271785 := bstep (se 2 (by rfl) ⟨130226919, by rfl⟩ : syracuseStep 347271785 = 260453839) B260453839
theorem B231514523 : Blo 2113435 231514523 := bstep (se 1 (by rfl) ⟨173635892, by rfl⟩ : syracuseStep 231514523 = 347271785) B347271785
theorem B154343015 : Blo 2113435 154343015 := bstep (se 1 (by rfl) ⟨115757261, by rfl⟩ : syracuseStep 154343015 = 231514523) B231514523
theorem B102895343 : Blo 2113435 102895343 := bstep (se 1 (by rfl) ⟨77171507, by rfl⟩ : syracuseStep 102895343 = 154343015) B154343015
theorem B68596895 : Blo 2113435 68596895 := bstep (se 1 (by rfl) ⟨51447671, by rfl⟩ : syracuseStep 68596895 = 102895343) B102895343
theorem B45731263 : Blo 2113435 45731263 := bstep (se 1 (by rfl) ⟨34298447, by rfl⟩ : syracuseStep 45731263 = 68596895) B68596895
theorem B60975017 : Blo 2113435 60975017 := bstep (se 2 (by rfl) ⟨22865631, by rfl⟩ : syracuseStep 60975017 = 45731263) B45731263
theorem B40650011 : Blo 2113435 40650011 := bstep (se 1 (by rfl) ⟨30487508, by rfl⟩ : syracuseStep 40650011 = 60975017) B60975017
theorem B27100007 : Blo 2113435 27100007 := bstep (se 1 (by rfl) ⟨20325005, by rfl⟩ : syracuseStep 27100007 = 40650011) B40650011
theorem B18066671 : Blo 2113435 18066671 := bstep (se 1 (by rfl) ⟨13550003, by rfl⟩ : syracuseStep 18066671 = 27100007) B27100007
theorem B12044447 : Blo 2113435 12044447 := bstep (se 1 (by rfl) ⟨9033335, by rfl⟩ : syracuseStep 12044447 = 18066671) B18066671
theorem B8029631 : Blo 2113435 8029631 := bstep (se 1 (by rfl) ⟨6022223, by rfl⟩ : syracuseStep 8029631 = 12044447) B12044447
theorem B5353087 : Blo 2113435 5353087 := bstep (se 1 (by rfl) ⟨4014815, by rfl⟩ : syracuseStep 5353087 = 8029631) B8029631
theorem B7137449 : Blo 2113435 7137449 := bstep (se 2 (by rfl) ⟨2676543, by rfl⟩ : syracuseStep 7137449 = 5353087) B5353087
theorem B4758299 : Blo 2113435 4758299 := bstep (se 1 (by rfl) ⟨3568724, by rfl⟩ : syracuseStep 4758299 = 7137449) B7137449
theorem B3172199 : Blo 2113435 3172199 := bstep (se 1 (by rfl) ⟨2379149, by rfl⟩ : syracuseStep 3172199 = 4758299) B4758299
theorem B2114799 : Blo 2113435 2114799 := bstep (se 1 (by rfl) ⟨1586099, by rfl⟩ : syracuseStep 2114799 = 3172199) B3172199
theorem B3172205 : Blo 2113435 3172205 := bbase (se 3 (by rfl) ⟨594788, by rfl⟩ : syracuseStep 3172205 = 1189577) (by norm_num)
theorem B2114803 : Blo 2113435 2114803 := bstep (se 1 (by rfl) ⟨1586102, by rfl⟩ : syracuseStep 2114803 = 3172205) B3172205
theorem B4758317 : Blo 2113435 4758317 := bbase (se 3 (by rfl) ⟨892184, by rfl⟩ : syracuseStep 4758317 = 1784369) (by norm_num)
theorem B3172211 : Blo 2113435 3172211 := bstep (se 1 (by rfl) ⟨2379158, by rfl⟩ : syracuseStep 3172211 = 4758317) B4758317
theorem B2114807 : Blo 2113435 2114807 := bstep (se 1 (by rfl) ⟨1586105, by rfl⟩ : syracuseStep 2114807 = 3172211) B3172211
theorem B2540641 : Blo 2113435 2540641 := bbase (se 2 (by rfl) ⟨952740, by rfl⟩ : syracuseStep 2540641 = 1905481) (by norm_num)
theorem B3387521 : Blo 2113435 3387521 := bstep (se 2 (by rfl) ⟨1270320, by rfl⟩ : syracuseStep 3387521 = 2540641) B2540641
theorem B9033389 : Blo 2113435 9033389 := bstep (se 3 (by rfl) ⟨1693760, by rfl⟩ : syracuseStep 9033389 = 3387521) B3387521
theorem B6022259 : Blo 2113435 6022259 := bstep (se 1 (by rfl) ⟨4516694, by rfl⟩ : syracuseStep 6022259 = 9033389) B9033389
theorem B4014839 : Blo 2113435 4014839 := bstep (se 1 (by rfl) ⟨3011129, by rfl⟩ : syracuseStep 4014839 = 6022259) B6022259
theorem B2676559 : Blo 2113435 2676559 := bstep (se 1 (by rfl) ⟨2007419, by rfl⟩ : syracuseStep 2676559 = 4014839) B4014839
theorem B3568745 : Blo 2113435 3568745 := bstep (se 2 (by rfl) ⟨1338279, by rfl⟩ : syracuseStep 3568745 = 2676559) B2676559
theorem B2379163 : Blo 2113435 2379163 := bstep (se 1 (by rfl) ⟨1784372, by rfl⟩ : syracuseStep 2379163 = 3568745) B3568745
theorem B3172217 : Blo 2113435 3172217 := bstep (se 2 (by rfl) ⟨1189581, by rfl⟩ : syracuseStep 3172217 = 2379163) B2379163
theorem B2114811 : Blo 2113435 2114811 := bstep (se 1 (by rfl) ⟨1586108, by rfl⟩ : syracuseStep 2114811 = 3172217) B3172217
theorem B8574677 : Blo 2113435 8574677 := bbase (se 7 (by rfl) ⟨100484, by rfl⟩ : syracuseStep 8574677 = 200969) (by norm_num)
theorem B5716451 : Blo 2113435 5716451 := bstep (se 1 (by rfl) ⟨4287338, by rfl⟩ : syracuseStep 5716451 = 8574677) B8574677
theorem B15243869 : Blo 2113435 15243869 := bstep (se 3 (by rfl) ⟨2858225, by rfl⟩ : syracuseStep 15243869 = 5716451) B5716451
theorem B10162579 : Blo 2113435 10162579 := bstep (se 1 (by rfl) ⟨7621934, by rfl⟩ : syracuseStep 10162579 = 15243869) B15243869
theorem B13550105 : Blo 2113435 13550105 := bstep (se 2 (by rfl) ⟨5081289, by rfl⟩ : syracuseStep 13550105 = 10162579) B10162579
theorem B36133613 : Blo 2113435 36133613 := bstep (se 3 (by rfl) ⟨6775052, by rfl⟩ : syracuseStep 36133613 = 13550105) B13550105
theorem B24089075 : Blo 2113435 24089075 := bstep (se 1 (by rfl) ⟨18066806, by rfl⟩ : syracuseStep 24089075 = 36133613) B36133613
theorem B16059383 : Blo 2113435 16059383 := bstep (se 1 (by rfl) ⟨12044537, by rfl⟩ : syracuseStep 16059383 = 24089075) B24089075
theorem B10706255 : Blo 2113435 10706255 := bstep (se 1 (by rfl) ⟨8029691, by rfl⟩ : syracuseStep 10706255 = 16059383) B16059383
theorem B7137503 : Blo 2113435 7137503 := bstep (se 1 (by rfl) ⟨5353127, by rfl⟩ : syracuseStep 7137503 = 10706255) B10706255
theorem B4758335 : Blo 2113435 4758335 := bstep (se 1 (by rfl) ⟨3568751, by rfl⟩ : syracuseStep 4758335 = 7137503) B7137503
theorem B3172223 : Blo 2113435 3172223 := bstep (se 1 (by rfl) ⟨2379167, by rfl⟩ : syracuseStep 3172223 = 4758335) B4758335
theorem B2114815 : Blo 2113435 2114815 := bstep (se 1 (by rfl) ⟨1586111, by rfl⟩ : syracuseStep 2114815 = 3172223) B3172223
theorem B3172229 : Blo 2113435 3172229 := bbase (se 4 (by rfl) ⟨297396, by rfl⟩ : syracuseStep 3172229 = 594793) (by norm_num)
theorem B2114819 : Blo 2113435 2114819 := bstep (se 1 (by rfl) ⟨1586114, by rfl⟩ : syracuseStep 2114819 = 3172229) B3172229
theorem B3568765 : Blo 2113435 3568765 := bbase (se 3 (by rfl) ⟨669143, by rfl⟩ : syracuseStep 3568765 = 1338287) (by norm_num)
theorem B4758353 : Blo 2113435 4758353 := bstep (se 2 (by rfl) ⟨1784382, by rfl⟩ : syracuseStep 4758353 = 3568765) B3568765
theorem B3172235 : Blo 2113435 3172235 := bstep (se 1 (by rfl) ⟨2379176, by rfl⟩ : syracuseStep 3172235 = 4758353) B4758353
theorem B2114823 : Blo 2113435 2114823 := bstep (se 1 (by rfl) ⟨1586117, by rfl⟩ : syracuseStep 2114823 = 3172235) B3172235
theorem B2379181 : Blo 2113435 2379181 := bbase (se 3 (by rfl) ⟨446096, by rfl⟩ : syracuseStep 2379181 = 892193) (by norm_num)
theorem B3172241 : Blo 2113435 3172241 := bstep (se 2 (by rfl) ⟨1189590, by rfl⟩ : syracuseStep 3172241 = 2379181) B2379181
theorem B2114827 : Blo 2113435 2114827 := bstep (se 1 (by rfl) ⟨1586120, by rfl⟩ : syracuseStep 2114827 = 3172241) B3172241
theorem B7137557 : Blo 2113435 7137557 := bbase (se 6 (by rfl) ⟨167286, by rfl⟩ : syracuseStep 7137557 = 334573) (by norm_num)
theorem B4758371 : Blo 2113435 4758371 := bstep (se 1 (by rfl) ⟨3568778, by rfl⟩ : syracuseStep 4758371 = 7137557) B7137557
theorem B3172247 : Blo 2113435 3172247 := bstep (se 1 (by rfl) ⟨2379185, by rfl⟩ : syracuseStep 3172247 = 4758371) B4758371
theorem B2114831 : Blo 2113435 2114831 := bstep (se 1 (by rfl) ⟨1586123, by rfl⟩ : syracuseStep 2114831 = 3172247) B3172247
theorem B3172253 : Blo 2113435 3172253 := bbase (se 3 (by rfl) ⟨594797, by rfl⟩ : syracuseStep 3172253 = 1189595) (by norm_num)
theorem B2114835 : Blo 2113435 2114835 := bstep (se 1 (by rfl) ⟨1586126, by rfl⟩ : syracuseStep 2114835 = 3172253) B3172253
theorem B4758389 : Blo 2113435 4758389 := bbase (se 5 (by rfl) ⟨223049, by rfl⟩ : syracuseStep 4758389 = 446099) (by norm_num)
theorem B3172259 : Blo 2113435 3172259 := bstep (se 1 (by rfl) ⟨2379194, by rfl⟩ : syracuseStep 3172259 = 4758389) B4758389
theorem B2114839 : Blo 2113435 2114839 := bstep (se 1 (by rfl) ⟨1586129, by rfl⟩ : syracuseStep 2114839 = 3172259) B3172259
theorem B9156773 : Blo 2113435 9156773 := bbase (se 4 (by rfl) ⟨858447, by rfl⟩ : syracuseStep 9156773 = 1716895) (by norm_num)
theorem B24418061 : Blo 2113435 24418061 := bstep (se 3 (by rfl) ⟨4578386, by rfl⟩ : syracuseStep 24418061 = 9156773) B9156773
theorem B16278707 : Blo 2113435 16278707 := bstep (se 1 (by rfl) ⟨12209030, by rfl⟩ : syracuseStep 16278707 = 24418061) B24418061
theorem B10852471 : Blo 2113435 10852471 := bstep (se 1 (by rfl) ⟨8139353, by rfl⟩ : syracuseStep 10852471 = 16278707) B16278707
theorem B57879845 : Blo 2113435 57879845 := bstep (se 4 (by rfl) ⟨5426235, by rfl⟩ : syracuseStep 57879845 = 10852471) B10852471
theorem B38586563 : Blo 2113435 38586563 := bstep (se 1 (by rfl) ⟨28939922, by rfl⟩ : syracuseStep 38586563 = 57879845) B57879845
theorem B25724375 : Blo 2113435 25724375 := bstep (se 1 (by rfl) ⟨19293281, by rfl⟩ : syracuseStep 25724375 = 38586563) B38586563
theorem B17149583 : Blo 2113435 17149583 := bstep (se 1 (by rfl) ⟨12862187, by rfl⟩ : syracuseStep 17149583 = 25724375) B25724375
theorem B45732221 : Blo 2113435 45732221 := bstep (se 3 (by rfl) ⟨8574791, by rfl⟩ : syracuseStep 45732221 = 17149583) B17149583
theorem B30488147 : Blo 2113435 30488147 := bstep (se 1 (by rfl) ⟨22866110, by rfl⟩ : syracuseStep 30488147 = 45732221) B45732221
theorem B20325431 : Blo 2113435 20325431 := bstep (se 1 (by rfl) ⟨15244073, by rfl⟩ : syracuseStep 20325431 = 30488147) B30488147
theorem B13550287 : Blo 2113435 13550287 := bstep (se 1 (by rfl) ⟨10162715, by rfl⟩ : syracuseStep 13550287 = 20325431) B20325431
theorem B18067049 : Blo 2113435 18067049 := bstep (se 2 (by rfl) ⟨6775143, by rfl⟩ : syracuseStep 18067049 = 13550287) B13550287
theorem B12044699 : Blo 2113435 12044699 := bstep (se 1 (by rfl) ⟨9033524, by rfl⟩ : syracuseStep 12044699 = 18067049) B18067049
theorem B8029799 : Blo 2113435 8029799 := bstep (se 1 (by rfl) ⟨6022349, by rfl⟩ : syracuseStep 8029799 = 12044699) B12044699
theorem B5353199 : Blo 2113435 5353199 := bstep (se 1 (by rfl) ⟨4014899, by rfl⟩ : syracuseStep 5353199 = 8029799) B8029799
theorem B3568799 : Blo 2113435 3568799 := bstep (se 1 (by rfl) ⟨2676599, by rfl⟩ : syracuseStep 3568799 = 5353199) B5353199
theorem B2379199 : Blo 2113435 2379199 := bstep (se 1 (by rfl) ⟨1784399, by rfl⟩ : syracuseStep 2379199 = 3568799) B3568799
theorem B3172265 : Blo 2113435 3172265 := bstep (se 2 (by rfl) ⟨1189599, by rfl⟩ : syracuseStep 3172265 = 2379199) B2379199
theorem B2114843 : Blo 2113435 2114843 := bstep (se 1 (by rfl) ⟨1586132, by rfl⟩ : syracuseStep 2114843 = 3172265) B3172265
theorem B8029813 : Blo 2113435 8029813 := bbase (se 5 (by rfl) ⟨376397, by rfl⟩ : syracuseStep 8029813 = 752795) (by norm_num)
theorem B10706417 : Blo 2113435 10706417 := bstep (se 2 (by rfl) ⟨4014906, by rfl⟩ : syracuseStep 10706417 = 8029813) B8029813
theorem B7137611 : Blo 2113435 7137611 := bstep (se 1 (by rfl) ⟨5353208, by rfl⟩ : syracuseStep 7137611 = 10706417) B10706417
theorem B4758407 : Blo 2113435 4758407 := bstep (se 1 (by rfl) ⟨3568805, by rfl⟩ : syracuseStep 4758407 = 7137611) B7137611
theorem B3172271 : Blo 2113435 3172271 := bstep (se 1 (by rfl) ⟨2379203, by rfl⟩ : syracuseStep 3172271 = 4758407) B4758407
theorem B2114847 : Blo 2113435 2114847 := bstep (se 1 (by rfl) ⟨1586135, by rfl⟩ : syracuseStep 2114847 = 3172271) B3172271
theorem B3172277 : Blo 2113435 3172277 := bbase (se 5 (by rfl) ⟨148700, by rfl⟩ : syracuseStep 3172277 = 297401) (by norm_num)
theorem B2114851 : Blo 2113435 2114851 := bstep (se 1 (by rfl) ⟨1586138, by rfl⟩ : syracuseStep 2114851 = 3172277) B3172277
theorem B5353229 : Blo 2113435 5353229 := bbase (se 3 (by rfl) ⟨1003730, by rfl⟩ : syracuseStep 5353229 = 2007461) (by norm_num)
theorem B3568819 : Blo 2113435 3568819 := bstep (se 1 (by rfl) ⟨2676614, by rfl⟩ : syracuseStep 3568819 = 5353229) B5353229
theorem B4758425 : Blo 2113435 4758425 := bstep (se 2 (by rfl) ⟨1784409, by rfl⟩ : syracuseStep 4758425 = 3568819) B3568819
theorem B3172283 : Blo 2113435 3172283 := bstep (se 1 (by rfl) ⟨2379212, by rfl⟩ : syracuseStep 3172283 = 4758425) B4758425
theorem B2114855 : Blo 2113435 2114855 := bstep (se 1 (by rfl) ⟨1586141, by rfl⟩ : syracuseStep 2114855 = 3172283) B3172283
theorem B2379217 : Blo 2113435 2379217 := bbase (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) (by norm_num)
theorem B3172289 : Blo 2113435 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B2114859 : Blo 2113435 2114859 := bstep (se 1 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 2114859 = 3172289) B3172289
theorem B4516805 : Blo 2113435 4516805 := bbase (se 4 (by rfl) ⟨423450, by rfl⟩ : syracuseStep 4516805 = 846901) (by norm_num)
theorem B3011203 : Blo 2113435 3011203 := bstep (se 1 (by rfl) ⟨2258402, by rfl⟩ : syracuseStep 3011203 = 4516805) B4516805
theorem B4014937 : Blo 2113435 4014937 := bstep (se 2 (by rfl) ⟨1505601, by rfl⟩ : syracuseStep 4014937 = 3011203) B3011203
theorem B5353249 : Blo 2113435 5353249 := bstep (se 2 (by rfl) ⟨2007468, by rfl⟩ : syracuseStep 5353249 = 4014937) B4014937
theorem B7137665 : Blo 2113435 7137665 := bstep (se 2 (by rfl) ⟨2676624, by rfl⟩ : syracuseStep 7137665 = 5353249) B5353249
theorem B4758443 : Blo 2113435 4758443 := bstep (se 1 (by rfl) ⟨3568832, by rfl⟩ : syracuseStep 4758443 = 7137665) B7137665
theorem B3172295 : Blo 2113435 3172295 := bstep (se 1 (by rfl) ⟨2379221, by rfl⟩ : syracuseStep 3172295 = 4758443) B4758443
theorem B2114863 : Blo 2113435 2114863 := bstep (se 1 (by rfl) ⟨1586147, by rfl⟩ : syracuseStep 2114863 = 3172295) B3172295
theorem B3172301 : Blo 2113435 3172301 := bbase (se 3 (by rfl) ⟨594806, by rfl⟩ : syracuseStep 3172301 = 1189613) (by norm_num)
theorem B2114867 : Blo 2113435 2114867 := bstep (se 1 (by rfl) ⟨1586150, by rfl⟩ : syracuseStep 2114867 = 3172301) B3172301
theorem B4758461 : Blo 2113435 4758461 := bbase (se 3 (by rfl) ⟨892211, by rfl⟩ : syracuseStep 4758461 = 1784423) (by norm_num)
theorem B3172307 : Blo 2113435 3172307 := bstep (se 1 (by rfl) ⟨2379230, by rfl⟩ : syracuseStep 3172307 = 4758461) B4758461
theorem B2114871 : Blo 2113435 2114871 := bstep (se 1 (by rfl) ⟨1586153, by rfl⟩ : syracuseStep 2114871 = 3172307) B3172307
theorem B3568853 : Blo 2113435 3568853 := bbase (se 7 (by rfl) ⟨41822, by rfl⟩ : syracuseStep 3568853 = 83645) (by norm_num)
theorem B2379235 : Blo 2113435 2379235 := bstep (se 1 (by rfl) ⟨1784426, by rfl⟩ : syracuseStep 2379235 = 3568853) B3568853
theorem B3172313 : Blo 2113435 3172313 := bstep (se 2 (by rfl) ⟨1189617, by rfl⟩ : syracuseStep 3172313 = 2379235) B2379235
theorem B2114875 : Blo 2113435 2114875 := bstep (se 1 (by rfl) ⟨1586156, by rfl⟩ : syracuseStep 2114875 = 3172313) B3172313
theorem B3387629 : Blo 2113435 3387629 := bbase (se 3 (by rfl) ⟨635180, by rfl⟩ : syracuseStep 3387629 = 1270361) (by norm_num)
theorem B9033677 : Blo 2113435 9033677 := bstep (se 3 (by rfl) ⟨1693814, by rfl⟩ : syracuseStep 9033677 = 3387629) B3387629
theorem B6022451 : Blo 2113435 6022451 := bstep (se 1 (by rfl) ⟨4516838, by rfl⟩ : syracuseStep 6022451 = 9033677) B9033677
theorem B16059869 : Blo 2113435 16059869 := bstep (se 3 (by rfl) ⟨3011225, by rfl⟩ : syracuseStep 16059869 = 6022451) B6022451
theorem B10706579 : Blo 2113435 10706579 := bstep (se 1 (by rfl) ⟨8029934, by rfl⟩ : syracuseStep 10706579 = 16059869) B16059869
theorem B7137719 : Blo 2113435 7137719 := bstep (se 1 (by rfl) ⟨5353289, by rfl⟩ : syracuseStep 7137719 = 10706579) B10706579
theorem B4758479 : Blo 2113435 4758479 := bstep (se 1 (by rfl) ⟨3568859, by rfl⟩ : syracuseStep 4758479 = 7137719) B7137719
theorem B3172319 : Blo 2113435 3172319 := bstep (se 1 (by rfl) ⟨2379239, by rfl⟩ : syracuseStep 3172319 = 4758479) B4758479
theorem B2114879 : Blo 2113435 2114879 := bstep (se 1 (by rfl) ⟨1586159, by rfl⟩ : syracuseStep 2114879 = 3172319) B3172319
theorem B3172325 : Blo 2113435 3172325 := bbase (se 4 (by rfl) ⟨297405, by rfl⟩ : syracuseStep 3172325 = 594811) (by norm_num)
theorem B2114883 : Blo 2113435 2114883 := bstep (se 1 (by rfl) ⟨1586162, by rfl⟩ : syracuseStep 2114883 = 3172325) B3172325
theorem B6775285 : Blo 2113435 6775285 := bbase (se 5 (by rfl) ⟨317591, by rfl⟩ : syracuseStep 6775285 = 635183) (by norm_num)
theorem B9033713 : Blo 2113435 9033713 := bstep (se 2 (by rfl) ⟨3387642, by rfl⟩ : syracuseStep 9033713 = 6775285) B6775285
theorem B6022475 : Blo 2113435 6022475 := bstep (se 1 (by rfl) ⟨4516856, by rfl⟩ : syracuseStep 6022475 = 9033713) B9033713
theorem B4014983 : Blo 2113435 4014983 := bstep (se 1 (by rfl) ⟨3011237, by rfl⟩ : syracuseStep 4014983 = 6022475) B6022475
theorem B2676655 : Blo 2113435 2676655 := bstep (se 1 (by rfl) ⟨2007491, by rfl⟩ : syracuseStep 2676655 = 4014983) B4014983
theorem B3568873 : Blo 2113435 3568873 := bstep (se 2 (by rfl) ⟨1338327, by rfl⟩ : syracuseStep 3568873 = 2676655) B2676655
theorem B4758497 : Blo 2113435 4758497 := bstep (se 2 (by rfl) ⟨1784436, by rfl⟩ : syracuseStep 4758497 = 3568873) B3568873
theorem B3172331 : Blo 2113435 3172331 := bstep (se 1 (by rfl) ⟨2379248, by rfl⟩ : syracuseStep 3172331 = 4758497) B4758497
theorem B2114887 : Blo 2113435 2114887 := bstep (se 1 (by rfl) ⟨1586165, by rfl⟩ : syracuseStep 2114887 = 3172331) B3172331
theorem B2379253 : Blo 2113435 2379253 := bbase (se 5 (by rfl) ⟨111527, by rfl⟩ : syracuseStep 2379253 = 223055) (by norm_num)
theorem B3172337 : Blo 2113435 3172337 := bstep (se 2 (by rfl) ⟨1189626, by rfl⟩ : syracuseStep 3172337 = 2379253) B2379253
theorem B2114891 : Blo 2113435 2114891 := bstep (se 1 (by rfl) ⟨1586168, by rfl⟩ : syracuseStep 2114891 = 3172337) B3172337
theorem B2676665 : Blo 2113435 2676665 := bbase (se 2 (by rfl) ⟨1003749, by rfl⟩ : syracuseStep 2676665 = 2007499) (by norm_num)
theorem B7137773 : Blo 2113435 7137773 := bstep (se 3 (by rfl) ⟨1338332, by rfl⟩ : syracuseStep 7137773 = 2676665) B2676665
theorem B4758515 : Blo 2113435 4758515 := bstep (se 1 (by rfl) ⟨3568886, by rfl⟩ : syracuseStep 4758515 = 7137773) B7137773
theorem B3172343 : Blo 2113435 3172343 := bstep (se 1 (by rfl) ⟨2379257, by rfl⟩ : syracuseStep 3172343 = 4758515) B4758515
theorem B2114895 : Blo 2113435 2114895 := bstep (se 1 (by rfl) ⟨1586171, by rfl⟩ : syracuseStep 2114895 = 3172343) B3172343
theorem B3172349 : Blo 2113435 3172349 := bbase (se 3 (by rfl) ⟨594815, by rfl⟩ : syracuseStep 3172349 = 1189631) (by norm_num)
theorem B2114899 : Blo 2113435 2114899 := bstep (se 1 (by rfl) ⟨1586174, by rfl⟩ : syracuseStep 2114899 = 3172349) B3172349
theorem B4758533 : Blo 2113435 4758533 := bbase (se 4 (by rfl) ⟨446112, by rfl⟩ : syracuseStep 4758533 = 892225) (by norm_num)
theorem B3172355 : Blo 2113435 3172355 := bstep (se 1 (by rfl) ⟨2379266, by rfl⟩ : syracuseStep 3172355 = 4758533) B4758533
theorem B2114903 : Blo 2113435 2114903 := bstep (se 1 (by rfl) ⟨1586177, by rfl⟩ : syracuseStep 2114903 = 3172355) B3172355
theorem B4015021 : Blo 2113435 4015021 := bbase (se 3 (by rfl) ⟨752816, by rfl⟩ : syracuseStep 4015021 = 1505633) (by norm_num)
theorem B5353361 : Blo 2113435 5353361 := bstep (se 2 (by rfl) ⟨2007510, by rfl⟩ : syracuseStep 5353361 = 4015021) B4015021
theorem B3568907 : Blo 2113435 3568907 := bstep (se 1 (by rfl) ⟨2676680, by rfl⟩ : syracuseStep 3568907 = 5353361) B5353361
theorem B2379271 : Blo 2113435 2379271 := bstep (se 1 (by rfl) ⟨1784453, by rfl⟩ : syracuseStep 2379271 = 3568907) B3568907
theorem B3172361 : Blo 2113435 3172361 := bstep (se 2 (by rfl) ⟨1189635, by rfl⟩ : syracuseStep 3172361 = 2379271) B2379271
theorem B2114907 : Blo 2113435 2114907 := bstep (se 1 (by rfl) ⟨1586180, by rfl⟩ : syracuseStep 2114907 = 3172361) B3172361
theorem B10706741 : Blo 2113435 10706741 := bbase (se 5 (by rfl) ⟨501878, by rfl⟩ : syracuseStep 10706741 = 1003757) (by norm_num)
theorem B7137827 : Blo 2113435 7137827 := bstep (se 1 (by rfl) ⟨5353370, by rfl⟩ : syracuseStep 7137827 = 10706741) B10706741
theorem B4758551 : Blo 2113435 4758551 := bstep (se 1 (by rfl) ⟨3568913, by rfl⟩ : syracuseStep 4758551 = 7137827) B7137827
theorem B3172367 : Blo 2113435 3172367 := bstep (se 1 (by rfl) ⟨2379275, by rfl⟩ : syracuseStep 3172367 = 4758551) B4758551
theorem B2114911 : Blo 2113435 2114911 := bstep (se 1 (by rfl) ⟨1586183, by rfl⟩ : syracuseStep 2114911 = 3172367) B3172367
theorem B3172373 : Blo 2113435 3172373 := bbase (se 6 (by rfl) ⟨74352, by rfl⟩ : syracuseStep 3172373 = 148705) (by norm_num)
theorem B2114915 : Blo 2113435 2114915 := bstep (se 1 (by rfl) ⟨1586186, by rfl⟩ : syracuseStep 2114915 = 3172373) B3172373
theorem B13550773 : Blo 2113435 13550773 := bbase (se 5 (by rfl) ⟨635192, by rfl⟩ : syracuseStep 13550773 = 1270385) (by norm_num)
theorem B18067697 : Blo 2113435 18067697 := bstep (se 2 (by rfl) ⟨6775386, by rfl⟩ : syracuseStep 18067697 = 13550773) B13550773
theorem B12045131 : Blo 2113435 12045131 := bstep (se 1 (by rfl) ⟨9033848, by rfl⟩ : syracuseStep 12045131 = 18067697) B18067697
theorem B8030087 : Blo 2113435 8030087 := bstep (se 1 (by rfl) ⟨6022565, by rfl⟩ : syracuseStep 8030087 = 12045131) B12045131
theorem B5353391 : Blo 2113435 5353391 := bstep (se 1 (by rfl) ⟨4015043, by rfl⟩ : syracuseStep 5353391 = 8030087) B8030087
theorem B3568927 : Blo 2113435 3568927 := bstep (se 1 (by rfl) ⟨2676695, by rfl⟩ : syracuseStep 3568927 = 5353391) B5353391
theorem B4758569 : Blo 2113435 4758569 := bstep (se 2 (by rfl) ⟨1784463, by rfl⟩ : syracuseStep 4758569 = 3568927) B3568927
theorem B3172379 : Blo 2113435 3172379 := bstep (se 1 (by rfl) ⟨2379284, by rfl⟩ : syracuseStep 3172379 = 4758569) B4758569
theorem B2114919 : Blo 2113435 2114919 := bstep (se 1 (by rfl) ⟨1586189, by rfl⟩ : syracuseStep 2114919 = 3172379) B3172379
theorem B2379289 : Blo 2113435 2379289 := bbase (se 2 (by rfl) ⟨892233, by rfl⟩ : syracuseStep 2379289 = 1784467) (by norm_num)
theorem B3172385 : Blo 2113435 3172385 := bstep (se 2 (by rfl) ⟨1189644, by rfl⟩ : syracuseStep 3172385 = 2379289) B2379289
theorem B2114923 : Blo 2113435 2114923 := bstep (se 1 (by rfl) ⟨1586192, by rfl⟩ : syracuseStep 2114923 = 3172385) B3172385
theorem B8030117 : Blo 2113435 8030117 := bbase (se 4 (by rfl) ⟨752823, by rfl⟩ : syracuseStep 8030117 = 1505647) (by norm_num)
theorem B5353411 : Blo 2113435 5353411 := bstep (se 1 (by rfl) ⟨4015058, by rfl⟩ : syracuseStep 5353411 = 8030117) B8030117
theorem B7137881 : Blo 2113435 7137881 := bstep (se 2 (by rfl) ⟨2676705, by rfl⟩ : syracuseStep 7137881 = 5353411) B5353411
theorem B4758587 : Blo 2113435 4758587 := bstep (se 1 (by rfl) ⟨3568940, by rfl⟩ : syracuseStep 4758587 = 7137881) B7137881
theorem B3172391 : Blo 2113435 3172391 := bstep (se 1 (by rfl) ⟨2379293, by rfl⟩ : syracuseStep 3172391 = 4758587) B4758587
theorem B2114927 : Blo 2113435 2114927 := bstep (se 1 (by rfl) ⟨1586195, by rfl⟩ : syracuseStep 2114927 = 3172391) B3172391
theorem B3172397 : Blo 2113435 3172397 := bbase (se 3 (by rfl) ⟨594824, by rfl⟩ : syracuseStep 3172397 = 1189649) (by norm_num)
theorem B2114931 : Blo 2113435 2114931 := bstep (se 1 (by rfl) ⟨1586198, by rfl⟩ : syracuseStep 2114931 = 3172397) B3172397
theorem B4758605 : Blo 2113435 4758605 := bbase (se 3 (by rfl) ⟨892238, by rfl⟩ : syracuseStep 4758605 = 1784477) (by norm_num)
theorem B3172403 : Blo 2113435 3172403 := bstep (se 1 (by rfl) ⟨2379302, by rfl⟩ : syracuseStep 3172403 = 4758605) B4758605
theorem B2114935 : Blo 2113435 2114935 := bstep (se 1 (by rfl) ⟨1586201, by rfl⟩ : syracuseStep 2114935 = 3172403) B3172403
theorem B2676721 : Blo 2113435 2676721 := bbase (se 2 (by rfl) ⟨1003770, by rfl⟩ : syracuseStep 2676721 = 2007541) (by norm_num)
theorem B3568961 : Blo 2113435 3568961 := bstep (se 2 (by rfl) ⟨1338360, by rfl⟩ : syracuseStep 3568961 = 2676721) B2676721
theorem B2379307 : Blo 2113435 2379307 := bstep (se 1 (by rfl) ⟨1784480, by rfl⟩ : syracuseStep 2379307 = 3568961) B3568961
theorem B3172409 : Blo 2113435 3172409 := bstep (se 2 (by rfl) ⟨1189653, by rfl⟩ : syracuseStep 3172409 = 2379307) B2379307
theorem B2114939 : Blo 2113435 2114939 := bstep (se 1 (by rfl) ⟨1586204, by rfl⟩ : syracuseStep 2114939 = 3172409) B3172409
theorem B14470645 : Blo 2113435 14470645 := bbase (se 5 (by rfl) ⟨678311, by rfl⟩ : syracuseStep 14470645 = 1356623) (by norm_num)
theorem B19294193 : Blo 2113435 19294193 := bstep (se 2 (by rfl) ⟨7235322, by rfl⟩ : syracuseStep 19294193 = 14470645) B14470645
theorem B12862795 : Blo 2113435 12862795 := bstep (se 1 (by rfl) ⟨9647096, by rfl⟩ : syracuseStep 12862795 = 19294193) B19294193
theorem B17150393 : Blo 2113435 17150393 := bstep (se 2 (by rfl) ⟨6431397, by rfl⟩ : syracuseStep 17150393 = 12862795) B12862795
theorem B11433595 : Blo 2113435 11433595 := bstep (se 1 (by rfl) ⟨8575196, by rfl⟩ : syracuseStep 11433595 = 17150393) B17150393
theorem B15244793 : Blo 2113435 15244793 := bstep (se 2 (by rfl) ⟨5716797, by rfl⟩ : syracuseStep 15244793 = 11433595) B11433595
theorem B10163195 : Blo 2113435 10163195 := bstep (se 1 (by rfl) ⟨7622396, by rfl⟩ : syracuseStep 10163195 = 15244793) B15244793
theorem B6775463 : Blo 2113435 6775463 := bstep (se 1 (by rfl) ⟨5081597, by rfl⟩ : syracuseStep 6775463 = 10163195) B10163195
theorem B4516975 : Blo 2113435 4516975 := bstep (se 1 (by rfl) ⟨3387731, by rfl⟩ : syracuseStep 4516975 = 6775463) B6775463
theorem B24090533 : Blo 2113435 24090533 := bstep (se 4 (by rfl) ⟨2258487, by rfl⟩ : syracuseStep 24090533 = 4516975) B4516975
theorem B16060355 : Blo 2113435 16060355 := bstep (se 1 (by rfl) ⟨12045266, by rfl⟩ : syracuseStep 16060355 = 24090533) B24090533
theorem B10706903 : Blo 2113435 10706903 := bstep (se 1 (by rfl) ⟨8030177, by rfl⟩ : syracuseStep 10706903 = 16060355) B16060355
theorem B7137935 : Blo 2113435 7137935 := bstep (se 1 (by rfl) ⟨5353451, by rfl⟩ : syracuseStep 7137935 = 10706903) B10706903
theorem B4758623 : Blo 2113435 4758623 := bstep (se 1 (by rfl) ⟨3568967, by rfl⟩ : syracuseStep 4758623 = 7137935) B7137935
theorem B3172415 : Blo 2113435 3172415 := bstep (se 1 (by rfl) ⟨2379311, by rfl⟩ : syracuseStep 3172415 = 4758623) B4758623
theorem B2114943 : Blo 2113435 2114943 := bstep (se 1 (by rfl) ⟨1586207, by rfl⟩ : syracuseStep 2114943 = 3172415) B3172415
theorem B3172421 : Blo 2113435 3172421 := bbase (se 4 (by rfl) ⟨297414, by rfl⟩ : syracuseStep 3172421 = 594829) (by norm_num)
theorem B2114947 : Blo 2113435 2114947 := bstep (se 1 (by rfl) ⟨1586210, by rfl⟩ : syracuseStep 2114947 = 3172421) B3172421
theorem B3568981 : Blo 2113435 3568981 := bbase (se 13 (by rfl) ⟨653, by rfl⟩ : syracuseStep 3568981 = 1307) (by norm_num)
theorem B4758641 : Blo 2113435 4758641 := bstep (se 2 (by rfl) ⟨1784490, by rfl⟩ : syracuseStep 4758641 = 3568981) B3568981
theorem B3172427 : Blo 2113435 3172427 := bstep (se 1 (by rfl) ⟨2379320, by rfl⟩ : syracuseStep 3172427 = 4758641) B4758641
theorem B2114951 : Blo 2113435 2114951 := bstep (se 1 (by rfl) ⟨1586213, by rfl⟩ : syracuseStep 2114951 = 3172427) B3172427
theorem B2379325 : Blo 2113435 2379325 := bbase (se 3 (by rfl) ⟨446123, by rfl⟩ : syracuseStep 2379325 = 892247) (by norm_num)
theorem B3172433 : Blo 2113435 3172433 := bstep (se 2 (by rfl) ⟨1189662, by rfl⟩ : syracuseStep 3172433 = 2379325) B2379325
theorem B2114955 : Blo 2113435 2114955 := bstep (se 1 (by rfl) ⟨1586216, by rfl⟩ : syracuseStep 2114955 = 3172433) B3172433
theorem B7137989 : Blo 2113435 7137989 := bbase (se 4 (by rfl) ⟨669186, by rfl⟩ : syracuseStep 7137989 = 1338373) (by norm_num)
theorem B4758659 : Blo 2113435 4758659 := bstep (se 1 (by rfl) ⟨3568994, by rfl⟩ : syracuseStep 4758659 = 7137989) B7137989
theorem B3172439 : Blo 2113435 3172439 := bstep (se 1 (by rfl) ⟨2379329, by rfl⟩ : syracuseStep 3172439 = 4758659) B4758659
theorem B2114959 : Blo 2113435 2114959 := bstep (se 1 (by rfl) ⟨1586219, by rfl⟩ : syracuseStep 2114959 = 3172439) B3172439
theorem B3172445 : Blo 2113435 3172445 := bbase (se 3 (by rfl) ⟨594833, by rfl⟩ : syracuseStep 3172445 = 1189667) (by norm_num)
theorem B2114963 : Blo 2113435 2114963 := bstep (se 1 (by rfl) ⟨1586222, by rfl⟩ : syracuseStep 2114963 = 3172445) B3172445
theorem B4758677 : Blo 2113435 4758677 := bbase (se 6 (by rfl) ⟨111531, by rfl⟩ : syracuseStep 4758677 = 223063) (by norm_num)
theorem B3172451 : Blo 2113435 3172451 := bstep (se 1 (by rfl) ⟨2379338, by rfl⟩ : syracuseStep 3172451 = 4758677) B4758677
theorem B2114967 : Blo 2113435 2114967 := bstep (se 1 (by rfl) ⟨1586225, by rfl⟩ : syracuseStep 2114967 = 3172451) B3172451
theorem B3011357 : Blo 2113435 3011357 := bbase (se 3 (by rfl) ⟨564629, by rfl⟩ : syracuseStep 3011357 = 1129259) (by norm_num)
theorem B8030285 : Blo 2113435 8030285 := bstep (se 3 (by rfl) ⟨1505678, by rfl⟩ : syracuseStep 8030285 = 3011357) B3011357
theorem B5353523 : Blo 2113435 5353523 := bstep (se 1 (by rfl) ⟨4015142, by rfl⟩ : syracuseStep 5353523 = 8030285) B8030285
theorem B3569015 : Blo 2113435 3569015 := bstep (se 1 (by rfl) ⟨2676761, by rfl⟩ : syracuseStep 3569015 = 5353523) B5353523
theorem B2379343 : Blo 2113435 2379343 := bstep (se 1 (by rfl) ⟨1784507, by rfl⟩ : syracuseStep 2379343 = 3569015) B3569015
theorem B3172457 : Blo 2113435 3172457 := bstep (se 2 (by rfl) ⟨1189671, by rfl⟩ : syracuseStep 3172457 = 2379343) B2379343
theorem B2114971 : Blo 2113435 2114971 := bstep (se 1 (by rfl) ⟨1586228, by rfl⟩ : syracuseStep 2114971 = 3172457) B3172457
theorem B16955189 : Blo 2113435 16955189 := bbase (se 5 (by rfl) ⟨794774, by rfl⟩ : syracuseStep 16955189 = 1589549) (by norm_num)
theorem B11303459 : Blo 2113435 11303459 := bstep (se 1 (by rfl) ⟨8477594, by rfl⟩ : syracuseStep 11303459 = 16955189) B16955189
theorem B7535639 : Blo 2113435 7535639 := bstep (se 1 (by rfl) ⟨5651729, by rfl⟩ : syracuseStep 7535639 = 11303459) B11303459
theorem B20095037 : Blo 2113435 20095037 := bstep (se 3 (by rfl) ⟨3767819, by rfl⟩ : syracuseStep 20095037 = 7535639) B7535639
theorem B13396691 : Blo 2113435 13396691 := bstep (se 1 (by rfl) ⟨10047518, by rfl⟩ : syracuseStep 13396691 = 20095037) B20095037
theorem B35724509 : Blo 2113435 35724509 := bstep (se 3 (by rfl) ⟨6698345, by rfl⟩ : syracuseStep 35724509 = 13396691) B13396691
theorem B23816339 : Blo 2113435 23816339 := bstep (se 1 (by rfl) ⟨17862254, by rfl⟩ : syracuseStep 23816339 = 35724509) B35724509
theorem B15877559 : Blo 2113435 15877559 := bstep (se 1 (by rfl) ⟨11908169, by rfl⟩ : syracuseStep 15877559 = 23816339) B23816339
theorem B10585039 : Blo 2113435 10585039 := bstep (se 1 (by rfl) ⟨7938779, by rfl⟩ : syracuseStep 10585039 = 15877559) B15877559
theorem B14113385 : Blo 2113435 14113385 := bstep (se 2 (by rfl) ⟨5292519, by rfl⟩ : syracuseStep 14113385 = 10585039) B10585039
theorem B9408923 : Blo 2113435 9408923 := bstep (se 1 (by rfl) ⟨7056692, by rfl⟩ : syracuseStep 9408923 = 14113385) B14113385
theorem B6272615 : Blo 2113435 6272615 := bstep (se 1 (by rfl) ⟨4704461, by rfl⟩ : syracuseStep 6272615 = 9408923) B9408923
theorem B4181743 : Blo 2113435 4181743 := bstep (se 1 (by rfl) ⟨3136307, by rfl⟩ : syracuseStep 4181743 = 6272615) B6272615
theorem B5575657 : Blo 2113435 5575657 := bstep (se 2 (by rfl) ⟨2090871, by rfl⟩ : syracuseStep 5575657 = 4181743) B4181743
theorem B7434209 : Blo 2113435 7434209 := bstep (se 2 (by rfl) ⟨2787828, by rfl⟩ : syracuseStep 7434209 = 5575657) B5575657
theorem B317192917 : Blo 2113435 317192917 := bstep (se 7 (by rfl) ⟨3717104, by rfl⟩ : syracuseStep 317192917 = 7434209) B7434209
theorem B422923889 : Blo 2113435 422923889 := bstep (se 2 (by rfl) ⟨158596458, by rfl⟩ : syracuseStep 422923889 = 317192917) B317192917
theorem B281949259 : Blo 2113435 281949259 := bstep (se 1 (by rfl) ⟨211461944, by rfl⟩ : syracuseStep 281949259 = 422923889) B422923889
theorem B375932345 : Blo 2113435 375932345 := bstep (se 2 (by rfl) ⟨140974629, by rfl⟩ : syracuseStep 375932345 = 281949259) B281949259
theorem B1002486253 : Blo 2113435 1002486253 := bstep (se 3 (by rfl) ⟨187966172, by rfl⟩ : syracuseStep 1002486253 = 375932345) B375932345
theorem B1336648337 : Blo 2113435 1336648337 := bstep (se 2 (by rfl) ⟨501243126, by rfl⟩ : syracuseStep 1336648337 = 1002486253) B1002486253
theorem B891098891 : Blo 2113435 891098891 := bstep (se 1 (by rfl) ⟨668324168, by rfl⟩ : syracuseStep 891098891 = 1336648337) B1336648337
theorem B594065927 : Blo 2113435 594065927 := bstep (se 1 (by rfl) ⟨445549445, by rfl⟩ : syracuseStep 594065927 = 891098891) B891098891
theorem B396043951 : Blo 2113435 396043951 := bstep (se 1 (by rfl) ⟨297032963, by rfl⟩ : syracuseStep 396043951 = 594065927) B594065927
theorem B528058601 : Blo 2113435 528058601 := bstep (se 2 (by rfl) ⟨198021975, by rfl⟩ : syracuseStep 528058601 = 396043951) B396043951
theorem B352039067 : Blo 2113435 352039067 := bstep (se 1 (by rfl) ⟨264029300, by rfl⟩ : syracuseStep 352039067 = 528058601) B528058601
theorem B234692711 : Blo 2113435 234692711 := bstep (se 1 (by rfl) ⟨176019533, by rfl⟩ : syracuseStep 234692711 = 352039067) B352039067
theorem B156461807 : Blo 2113435 156461807 := bstep (se 1 (by rfl) ⟨117346355, by rfl⟩ : syracuseStep 156461807 = 234692711) B234692711
theorem B104307871 : Blo 2113435 104307871 := bstep (se 1 (by rfl) ⟨78230903, by rfl⟩ : syracuseStep 104307871 = 156461807) B156461807
theorem B139077161 : Blo 2113435 139077161 := bstep (se 2 (by rfl) ⟨52153935, by rfl⟩ : syracuseStep 139077161 = 104307871) B104307871
theorem B92718107 : Blo 2113435 92718107 := bstep (se 1 (by rfl) ⟨69538580, by rfl⟩ : syracuseStep 92718107 = 139077161) B139077161
theorem B61812071 : Blo 2113435 61812071 := bstep (se 1 (by rfl) ⟨46359053, by rfl⟩ : syracuseStep 61812071 = 92718107) B92718107
theorem B41208047 : Blo 2113435 41208047 := bstep (se 1 (by rfl) ⟨30906035, by rfl⟩ : syracuseStep 41208047 = 61812071) B61812071
theorem B27472031 : Blo 2113435 27472031 := bstep (se 1 (by rfl) ⟨20604023, by rfl⟩ : syracuseStep 27472031 = 41208047) B41208047
theorem B18314687 : Blo 2113435 18314687 := bstep (se 1 (by rfl) ⟨13736015, by rfl⟩ : syracuseStep 18314687 = 27472031) B27472031
theorem B12209791 : Blo 2113435 12209791 := bstep (se 1 (by rfl) ⟨9157343, by rfl⟩ : syracuseStep 12209791 = 18314687) B18314687
theorem B16279721 : Blo 2113435 16279721 := bstep (se 2 (by rfl) ⟨6104895, by rfl⟩ : syracuseStep 16279721 = 12209791) B12209791
theorem B10853147 : Blo 2113435 10853147 := bstep (se 1 (by rfl) ⟨8139860, by rfl⟩ : syracuseStep 10853147 = 16279721) B16279721
theorem B28941725 : Blo 2113435 28941725 := bstep (se 3 (by rfl) ⟨5426573, by rfl⟩ : syracuseStep 28941725 = 10853147) B10853147
theorem B77177933 : Blo 2113435 77177933 := bstep (se 3 (by rfl) ⟨14470862, by rfl⟩ : syracuseStep 77177933 = 28941725) B28941725
theorem B51451955 : Blo 2113435 51451955 := bstep (se 1 (by rfl) ⟨38588966, by rfl⟩ : syracuseStep 51451955 = 77177933) B77177933
theorem B34301303 : Blo 2113435 34301303 := bstep (se 1 (by rfl) ⟨25725977, by rfl⟩ : syracuseStep 34301303 = 51451955) B51451955
theorem B22867535 : Blo 2113435 22867535 := bstep (se 1 (by rfl) ⟨17150651, by rfl⟩ : syracuseStep 22867535 = 34301303) B34301303
theorem B15245023 : Blo 2113435 15245023 := bstep (se 1 (by rfl) ⟨11433767, by rfl⟩ : syracuseStep 15245023 = 22867535) B22867535
theorem B20326697 : Blo 2113435 20326697 := bstep (se 2 (by rfl) ⟨7622511, by rfl⟩ : syracuseStep 20326697 = 15245023) B15245023
theorem B13551131 : Blo 2113435 13551131 := bstep (se 1 (by rfl) ⟨10163348, by rfl⟩ : syracuseStep 13551131 = 20326697) B20326697
theorem B9034087 : Blo 2113435 9034087 := bstep (se 1 (by rfl) ⟨6775565, by rfl⟩ : syracuseStep 9034087 = 13551131) B13551131
theorem B12045449 : Blo 2113435 12045449 := bstep (se 2 (by rfl) ⟨4517043, by rfl⟩ : syracuseStep 12045449 = 9034087) B9034087
theorem B8030299 : Blo 2113435 8030299 := bstep (se 1 (by rfl) ⟨6022724, by rfl⟩ : syracuseStep 8030299 = 12045449) B12045449
theorem B10707065 : Blo 2113435 10707065 := bstep (se 2 (by rfl) ⟨4015149, by rfl⟩ : syracuseStep 10707065 = 8030299) B8030299
theorem B7138043 : Blo 2113435 7138043 := bstep (se 1 (by rfl) ⟨5353532, by rfl⟩ : syracuseStep 7138043 = 10707065) B10707065
theorem B4758695 : Blo 2113435 4758695 := bstep (se 1 (by rfl) ⟨3569021, by rfl⟩ : syracuseStep 4758695 = 7138043) B7138043
theorem B3172463 : Blo 2113435 3172463 := bstep (se 1 (by rfl) ⟨2379347, by rfl⟩ : syracuseStep 3172463 = 4758695) B4758695
theorem B2114975 : Blo 2113435 2114975 := bstep (se 1 (by rfl) ⟨1586231, by rfl⟩ : syracuseStep 2114975 = 3172463) B3172463
theorem B3172469 : Blo 2113435 3172469 := bbase (se 5 (by rfl) ⟨148709, by rfl⟩ : syracuseStep 3172469 = 297419) (by norm_num)
theorem B2114979 : Blo 2113435 2114979 := bstep (se 1 (by rfl) ⟨1586234, by rfl⟩ : syracuseStep 2114979 = 3172469) B3172469
theorem B4015165 : Blo 2113435 4015165 := bbase (se 3 (by rfl) ⟨752843, by rfl⟩ : syracuseStep 4015165 = 1505687) (by norm_num)
theorem B5353553 : Blo 2113435 5353553 := bstep (se 2 (by rfl) ⟨2007582, by rfl⟩ : syracuseStep 5353553 = 4015165) B4015165
theorem B3569035 : Blo 2113435 3569035 := bstep (se 1 (by rfl) ⟨2676776, by rfl⟩ : syracuseStep 3569035 = 5353553) B5353553
theorem B4758713 : Blo 2113435 4758713 := bstep (se 2 (by rfl) ⟨1784517, by rfl⟩ : syracuseStep 4758713 = 3569035) B3569035
theorem B3172475 : Blo 2113435 3172475 := bstep (se 1 (by rfl) ⟨2379356, by rfl⟩ : syracuseStep 3172475 = 4758713) B4758713
theorem B2114983 : Blo 2113435 2114983 := bstep (se 1 (by rfl) ⟨1586237, by rfl⟩ : syracuseStep 2114983 = 3172475) B3172475
theorem B2379361 : Blo 2113435 2379361 := bbase (se 2 (by rfl) ⟨892260, by rfl⟩ : syracuseStep 2379361 = 1784521) (by norm_num)
theorem B3172481 : Blo 2113435 3172481 := bstep (se 2 (by rfl) ⟨1189680, by rfl⟩ : syracuseStep 3172481 = 2379361) B2379361
theorem B2114987 : Blo 2113435 2114987 := bstep (se 1 (by rfl) ⟨1586240, by rfl⟩ : syracuseStep 2114987 = 3172481) B3172481
theorem B5353573 : Blo 2113435 5353573 := bbase (se 4 (by rfl) ⟨501897, by rfl⟩ : syracuseStep 5353573 = 1003795) (by norm_num)
theorem B7138097 : Blo 2113435 7138097 := bstep (se 2 (by rfl) ⟨2676786, by rfl⟩ : syracuseStep 7138097 = 5353573) B5353573
theorem B4758731 : Blo 2113435 4758731 := bstep (se 1 (by rfl) ⟨3569048, by rfl⟩ : syracuseStep 4758731 = 7138097) B7138097
theorem B3172487 : Blo 2113435 3172487 := bstep (se 1 (by rfl) ⟨2379365, by rfl⟩ : syracuseStep 3172487 = 4758731) B4758731
theorem B2114991 : Blo 2113435 2114991 := bstep (se 1 (by rfl) ⟨1586243, by rfl⟩ : syracuseStep 2114991 = 3172487) B3172487
theorem B3172493 : Blo 2113435 3172493 := bbase (se 3 (by rfl) ⟨594842, by rfl⟩ : syracuseStep 3172493 = 1189685) (by norm_num)
theorem B2114995 : Blo 2113435 2114995 := bstep (se 1 (by rfl) ⟨1586246, by rfl⟩ : syracuseStep 2114995 = 3172493) B3172493
theorem B4758749 : Blo 2113435 4758749 := bbase (se 3 (by rfl) ⟨892265, by rfl⟩ : syracuseStep 4758749 = 1784531) (by norm_num)
theorem B3172499 : Blo 2113435 3172499 := bstep (se 1 (by rfl) ⟨2379374, by rfl⟩ : syracuseStep 3172499 = 4758749) B4758749
theorem B2114999 : Blo 2113435 2114999 := bstep (se 1 (by rfl) ⟨1586249, by rfl⟩ : syracuseStep 2114999 = 3172499) B3172499
theorem B3569069 : Blo 2113435 3569069 := bbase (se 3 (by rfl) ⟨669200, by rfl⟩ : syracuseStep 3569069 = 1338401) (by norm_num)
theorem B2379379 : Blo 2113435 2379379 := bstep (se 1 (by rfl) ⟨1784534, by rfl⟩ : syracuseStep 2379379 = 3569069) B3569069
theorem B3172505 : Blo 2113435 3172505 := bstep (se 2 (by rfl) ⟨1189689, by rfl⟩ : syracuseStep 3172505 = 2379379) B2379379
theorem B2115003 : Blo 2113435 2115003 := bstep (se 1 (by rfl) ⟨1586252, by rfl⟩ : syracuseStep 2115003 = 3172505) B3172505
theorem B2444753 : Blo 2113435 2444753 := bbase (se 2 (by rfl) ⟨916782, by rfl⟩ : syracuseStep 2444753 = 1833565) (by norm_num)
theorem B6519341 : Blo 2113435 6519341 := bstep (se 3 (by rfl) ⟨1222376, by rfl⟩ : syracuseStep 6519341 = 2444753) B2444753
theorem B4346227 : Blo 2113435 4346227 := bstep (se 1 (by rfl) ⟨3259670, by rfl⟩ : syracuseStep 4346227 = 6519341) B6519341
theorem B5794969 : Blo 2113435 5794969 := bstep (se 2 (by rfl) ⟨2173113, by rfl⟩ : syracuseStep 5794969 = 4346227) B4346227
theorem B7726625 : Blo 2113435 7726625 := bstep (se 2 (by rfl) ⟨2897484, by rfl⟩ : syracuseStep 7726625 = 5794969) B5794969
theorem B5151083 : Blo 2113435 5151083 := bstep (se 1 (by rfl) ⟨3863312, by rfl⟩ : syracuseStep 5151083 = 7726625) B7726625
theorem B54944885 : Blo 2113435 54944885 := bstep (se 5 (by rfl) ⟨2575541, by rfl⟩ : syracuseStep 54944885 = 5151083) B5151083
theorem B36629923 : Blo 2113435 36629923 := bstep (se 1 (by rfl) ⟨27472442, by rfl⟩ : syracuseStep 36629923 = 54944885) B54944885
theorem B48839897 : Blo 2113435 48839897 := bstep (se 2 (by rfl) ⟨18314961, by rfl⟩ : syracuseStep 48839897 = 36629923) B36629923
theorem B32559931 : Blo 2113435 32559931 := bstep (se 1 (by rfl) ⟨24419948, by rfl⟩ : syracuseStep 32559931 = 48839897) B48839897
theorem B43413241 : Blo 2113435 43413241 := bstep (se 2 (by rfl) ⟨16279965, by rfl⟩ : syracuseStep 43413241 = 32559931) B32559931
theorem B57884321 : Blo 2113435 57884321 := bstep (se 2 (by rfl) ⟨21706620, by rfl⟩ : syracuseStep 57884321 = 43413241) B43413241
theorem B38589547 : Blo 2113435 38589547 := bstep (se 1 (by rfl) ⟨28942160, by rfl⟩ : syracuseStep 38589547 = 57884321) B57884321
theorem B51452729 : Blo 2113435 51452729 := bstep (se 2 (by rfl) ⟨19294773, by rfl⟩ : syracuseStep 51452729 = 38589547) B38589547
theorem B34301819 : Blo 2113435 34301819 := bstep (se 1 (by rfl) ⟨25726364, by rfl⟩ : syracuseStep 34301819 = 51452729) B51452729
theorem B91471517 : Blo 2113435 91471517 := bstep (se 3 (by rfl) ⟨17150909, by rfl⟩ : syracuseStep 91471517 = 34301819) B34301819
theorem B60981011 : Blo 2113435 60981011 := bstep (se 1 (by rfl) ⟨45735758, by rfl⟩ : syracuseStep 60981011 = 91471517) B91471517
theorem B40654007 : Blo 2113435 40654007 := bstep (se 1 (by rfl) ⟨30490505, by rfl⟩ : syracuseStep 40654007 = 60981011) B60981011
theorem B27102671 : Blo 2113435 27102671 := bstep (se 1 (by rfl) ⟨20327003, by rfl⟩ : syracuseStep 27102671 = 40654007) B40654007
theorem B18068447 : Blo 2113435 18068447 := bstep (se 1 (by rfl) ⟨13551335, by rfl⟩ : syracuseStep 18068447 = 27102671) B27102671
theorem B12045631 : Blo 2113435 12045631 := bstep (se 1 (by rfl) ⟨9034223, by rfl⟩ : syracuseStep 12045631 = 18068447) B18068447
theorem B16060841 : Blo 2113435 16060841 := bstep (se 2 (by rfl) ⟨6022815, by rfl⟩ : syracuseStep 16060841 = 12045631) B12045631
theorem B10707227 : Blo 2113435 10707227 := bstep (se 1 (by rfl) ⟨8030420, by rfl⟩ : syracuseStep 10707227 = 16060841) B16060841
theorem B7138151 : Blo 2113435 7138151 := bstep (se 1 (by rfl) ⟨5353613, by rfl⟩ : syracuseStep 7138151 = 10707227) B10707227
theorem B4758767 : Blo 2113435 4758767 := bstep (se 1 (by rfl) ⟨3569075, by rfl⟩ : syracuseStep 4758767 = 7138151) B7138151
theorem B3172511 : Blo 2113435 3172511 := bstep (se 1 (by rfl) ⟨2379383, by rfl⟩ : syracuseStep 3172511 = 4758767) B4758767
theorem B2115007 : Blo 2113435 2115007 := bstep (se 1 (by rfl) ⟨1586255, by rfl⟩ : syracuseStep 2115007 = 3172511) B3172511
theorem B3172517 : Blo 2113435 3172517 := bbase (se 4 (by rfl) ⟨297423, by rfl⟩ : syracuseStep 3172517 = 594847) (by norm_num)
theorem B2115011 : Blo 2113435 2115011 := bstep (se 1 (by rfl) ⟨1586258, by rfl⟩ : syracuseStep 2115011 = 3172517) B3172517
theorem B2676817 : Blo 2113435 2676817 := bbase (se 2 (by rfl) ⟨1003806, by rfl⟩ : syracuseStep 2676817 = 2007613) (by norm_num)
theorem B3569089 : Blo 2113435 3569089 := bstep (se 2 (by rfl) ⟨1338408, by rfl⟩ : syracuseStep 3569089 = 2676817) B2676817
theorem B4758785 : Blo 2113435 4758785 := bstep (se 2 (by rfl) ⟨1784544, by rfl⟩ : syracuseStep 4758785 = 3569089) B3569089
theorem B3172523 : Blo 2113435 3172523 := bstep (se 1 (by rfl) ⟨2379392, by rfl⟩ : syracuseStep 3172523 = 4758785) B4758785
theorem B2115015 : Blo 2113435 2115015 := bstep (se 1 (by rfl) ⟨1586261, by rfl⟩ : syracuseStep 2115015 = 3172523) B3172523
theorem B2379397 : Blo 2113435 2379397 := bbase (se 4 (by rfl) ⟨223068, by rfl⟩ : syracuseStep 2379397 = 446137) (by norm_num)
theorem B3172529 : Blo 2113435 3172529 := bstep (se 2 (by rfl) ⟨1189698, by rfl⟩ : syracuseStep 3172529 = 2379397) B2379397
theorem B2115019 : Blo 2113435 2115019 := bstep (se 1 (by rfl) ⟨1586264, by rfl⟩ : syracuseStep 2115019 = 3172529) B3172529
theorem B5151125 : Blo 2113435 5151125 := bbase (se 6 (by rfl) ⟨120729, by rfl⟩ : syracuseStep 5151125 = 241459) (by norm_num)
theorem B3434083 : Blo 2113435 3434083 := bstep (se 1 (by rfl) ⟨2575562, by rfl⟩ : syracuseStep 3434083 = 5151125) B5151125
theorem B18315109 : Blo 2113435 18315109 := bstep (se 4 (by rfl) ⟨1717041, by rfl⟩ : syracuseStep 18315109 = 3434083) B3434083
theorem B24420145 : Blo 2113435 24420145 := bstep (se 2 (by rfl) ⟨9157554, by rfl⟩ : syracuseStep 24420145 = 18315109) B18315109
theorem B32560193 : Blo 2113435 32560193 := bstep (se 2 (by rfl) ⟨12210072, by rfl⟩ : syracuseStep 32560193 = 24420145) B24420145
theorem B21706795 : Blo 2113435 21706795 := bstep (se 1 (by rfl) ⟨16280096, by rfl⟩ : syracuseStep 21706795 = 32560193) B32560193
theorem B28942393 : Blo 2113435 28942393 := bstep (se 2 (by rfl) ⟨10853397, by rfl⟩ : syracuseStep 28942393 = 21706795) B21706795
theorem B38589857 : Blo 2113435 38589857 := bstep (se 2 (by rfl) ⟨14471196, by rfl⟩ : syracuseStep 38589857 = 28942393) B28942393
theorem B25726571 : Blo 2113435 25726571 := bstep (se 1 (by rfl) ⟨19294928, by rfl⟩ : syracuseStep 25726571 = 38589857) B38589857
theorem B17151047 : Blo 2113435 17151047 := bstep (se 1 (by rfl) ⟨12863285, by rfl⟩ : syracuseStep 17151047 = 25726571) B25726571
theorem B11434031 : Blo 2113435 11434031 := bstep (se 1 (by rfl) ⟨8575523, by rfl⟩ : syracuseStep 11434031 = 17151047) B17151047
theorem B7622687 : Blo 2113435 7622687 := bstep (se 1 (by rfl) ⟨5717015, by rfl⟩ : syracuseStep 7622687 = 11434031) B11434031
theorem B5081791 : Blo 2113435 5081791 := bstep (se 1 (by rfl) ⟨3811343, by rfl⟩ : syracuseStep 5081791 = 7622687) B7622687
theorem B6775721 : Blo 2113435 6775721 := bstep (se 2 (by rfl) ⟨2540895, by rfl⟩ : syracuseStep 6775721 = 5081791) B5081791
theorem B4517147 : Blo 2113435 4517147 := bstep (se 1 (by rfl) ⟨3387860, by rfl⟩ : syracuseStep 4517147 = 6775721) B6775721
theorem B3011431 : Blo 2113435 3011431 := bstep (se 1 (by rfl) ⟨2258573, by rfl⟩ : syracuseStep 3011431 = 4517147) B4517147
theorem B4015241 : Blo 2113435 4015241 := bstep (se 2 (by rfl) ⟨1505715, by rfl⟩ : syracuseStep 4015241 = 3011431) B3011431
theorem B2676827 : Blo 2113435 2676827 := bstep (se 1 (by rfl) ⟨2007620, by rfl⟩ : syracuseStep 2676827 = 4015241) B4015241
theorem B7138205 : Blo 2113435 7138205 := bstep (se 3 (by rfl) ⟨1338413, by rfl⟩ : syracuseStep 7138205 = 2676827) B2676827
theorem B4758803 : Blo 2113435 4758803 := bstep (se 1 (by rfl) ⟨3569102, by rfl⟩ : syracuseStep 4758803 = 7138205) B7138205
theorem B3172535 : Blo 2113435 3172535 := bstep (se 1 (by rfl) ⟨2379401, by rfl⟩ : syracuseStep 3172535 = 4758803) B4758803
theorem B2115023 : Blo 2113435 2115023 := bstep (se 1 (by rfl) ⟨1586267, by rfl⟩ : syracuseStep 2115023 = 3172535) B3172535
theorem B3172541 : Blo 2113435 3172541 := bbase (se 3 (by rfl) ⟨594851, by rfl⟩ : syracuseStep 3172541 = 1189703) (by norm_num)
theorem B2115027 : Blo 2113435 2115027 := bstep (se 1 (by rfl) ⟨1586270, by rfl⟩ : syracuseStep 2115027 = 3172541) B3172541
theorem B4758821 : Blo 2113435 4758821 := bbase (se 4 (by rfl) ⟨446139, by rfl⟩ : syracuseStep 4758821 = 892279) (by norm_num)
theorem B3172547 : Blo 2113435 3172547 := bstep (se 1 (by rfl) ⟨2379410, by rfl⟩ : syracuseStep 3172547 = 4758821) B4758821
theorem B2115031 : Blo 2113435 2115031 := bstep (se 1 (by rfl) ⟨1586273, by rfl⟩ : syracuseStep 2115031 = 3172547) B3172547
theorem B5353685 : Blo 2113435 5353685 := bbase (se 7 (by rfl) ⟨62738, by rfl⟩ : syracuseStep 5353685 = 125477) (by norm_num)
theorem B3569123 : Blo 2113435 3569123 := bstep (se 1 (by rfl) ⟨2676842, by rfl⟩ : syracuseStep 3569123 = 5353685) B5353685
theorem B2379415 : Blo 2113435 2379415 := bstep (se 1 (by rfl) ⟨1784561, by rfl⟩ : syracuseStep 2379415 = 3569123) B3569123
theorem B3172553 : Blo 2113435 3172553 := bstep (se 2 (by rfl) ⟨1189707, by rfl⟩ : syracuseStep 3172553 = 2379415) B2379415
theorem B2115035 : Blo 2113435 2115035 := bstep (se 1 (by rfl) ⟨1586276, by rfl⟩ : syracuseStep 2115035 = 3172553) B3172553
theorem B3215845 : Blo 2113435 3215845 := bbase (se 4 (by rfl) ⟨301485, by rfl⟩ : syracuseStep 3215845 = 602971) (by norm_num)
theorem B17151173 : Blo 2113435 17151173 := bstep (se 4 (by rfl) ⟨1607922, by rfl⟩ : syracuseStep 17151173 = 3215845) B3215845
theorem B11434115 : Blo 2113435 11434115 := bstep (se 1 (by rfl) ⟨8575586, by rfl⟩ : syracuseStep 11434115 = 17151173) B17151173
theorem B7622743 : Blo 2113435 7622743 := bstep (se 1 (by rfl) ⟨5717057, by rfl⟩ : syracuseStep 7622743 = 11434115) B11434115
theorem B10163657 : Blo 2113435 10163657 := bstep (se 2 (by rfl) ⟨3811371, by rfl⟩ : syracuseStep 10163657 = 7622743) B7622743
theorem B6775771 : Blo 2113435 6775771 := bstep (se 1 (by rfl) ⟨5081828, by rfl⟩ : syracuseStep 6775771 = 10163657) B10163657
theorem B9034361 : Blo 2113435 9034361 := bstep (se 2 (by rfl) ⟨3387885, by rfl⟩ : syracuseStep 9034361 = 6775771) B6775771
theorem B6022907 : Blo 2113435 6022907 := bstep (se 1 (by rfl) ⟨4517180, by rfl⟩ : syracuseStep 6022907 = 9034361) B9034361
theorem B4015271 : Blo 2113435 4015271 := bstep (se 1 (by rfl) ⟨3011453, by rfl⟩ : syracuseStep 4015271 = 6022907) B6022907
theorem B10707389 : Blo 2113435 10707389 := bstep (se 3 (by rfl) ⟨2007635, by rfl⟩ : syracuseStep 10707389 = 4015271) B4015271
theorem B7138259 : Blo 2113435 7138259 := bstep (se 1 (by rfl) ⟨5353694, by rfl⟩ : syracuseStep 7138259 = 10707389) B10707389
theorem B4758839 : Blo 2113435 4758839 := bstep (se 1 (by rfl) ⟨3569129, by rfl⟩ : syracuseStep 4758839 = 7138259) B7138259
theorem B3172559 : Blo 2113435 3172559 := bstep (se 1 (by rfl) ⟨2379419, by rfl⟩ : syracuseStep 3172559 = 4758839) B4758839
theorem B2115039 : Blo 2113435 2115039 := bstep (se 1 (by rfl) ⟨1586279, by rfl⟩ : syracuseStep 2115039 = 3172559) B3172559
theorem B3172565 : Blo 2113435 3172565 := bbase (se 7 (by rfl) ⟨37178, by rfl⟩ : syracuseStep 3172565 = 74357) (by norm_num)
theorem B2115043 : Blo 2113435 2115043 := bstep (se 1 (by rfl) ⟨1586282, by rfl⟩ : syracuseStep 2115043 = 3172565) B3172565
theorem B6431717 : Blo 2113435 6431717 := bbase (se 4 (by rfl) ⟨602973, by rfl⟩ : syracuseStep 6431717 = 1205947) (by norm_num)
theorem B4287811 : Blo 2113435 4287811 := bstep (se 1 (by rfl) ⟨3215858, by rfl⟩ : syracuseStep 4287811 = 6431717) B6431717
theorem B5717081 : Blo 2113435 5717081 := bstep (se 2 (by rfl) ⟨2143905, by rfl⟩ : syracuseStep 5717081 = 4287811) B4287811
theorem B3811387 : Blo 2113435 3811387 := bstep (se 1 (by rfl) ⟨2858540, by rfl⟩ : syracuseStep 3811387 = 5717081) B5717081
theorem B5081849 : Blo 2113435 5081849 := bstep (se 2 (by rfl) ⟨1905693, by rfl⟩ : syracuseStep 5081849 = 3811387) B3811387
theorem B3387899 : Blo 2113435 3387899 := bstep (se 1 (by rfl) ⟨2540924, by rfl⟩ : syracuseStep 3387899 = 5081849) B5081849
theorem B2258599 : Blo 2113435 2258599 := bstep (se 1 (by rfl) ⟨1693949, by rfl⟩ : syracuseStep 2258599 = 3387899) B3387899
theorem B3011465 : Blo 2113435 3011465 := bstep (se 2 (by rfl) ⟨1129299, by rfl⟩ : syracuseStep 3011465 = 2258599) B2258599
theorem B8030573 : Blo 2113435 8030573 := bstep (se 3 (by rfl) ⟨1505732, by rfl⟩ : syracuseStep 8030573 = 3011465) B3011465
theorem B5353715 : Blo 2113435 5353715 := bstep (se 1 (by rfl) ⟨4015286, by rfl⟩ : syracuseStep 5353715 = 8030573) B8030573
theorem B3569143 : Blo 2113435 3569143 := bstep (se 1 (by rfl) ⟨2676857, by rfl⟩ : syracuseStep 3569143 = 5353715) B5353715
theorem B4758857 : Blo 2113435 4758857 := bstep (se 2 (by rfl) ⟨1784571, by rfl⟩ : syracuseStep 4758857 = 3569143) B3569143
theorem B3172571 : Blo 2113435 3172571 := bstep (se 1 (by rfl) ⟨2379428, by rfl⟩ : syracuseStep 3172571 = 4758857) B4758857
theorem B2115047 : Blo 2113435 2115047 := bstep (se 1 (by rfl) ⟨1586285, by rfl⟩ : syracuseStep 2115047 = 3172571) B3172571
theorem B2379433 : Blo 2113435 2379433 := bbase (se 2 (by rfl) ⟨892287, by rfl⟩ : syracuseStep 2379433 = 1784575) (by norm_num)
theorem B3172577 : Blo 2113435 3172577 := bstep (se 2 (by rfl) ⟨1189716, by rfl⟩ : syracuseStep 3172577 = 2379433) B2379433
theorem B2115051 : Blo 2113435 2115051 := bstep (se 1 (by rfl) ⟨1586288, by rfl⟩ : syracuseStep 2115051 = 3172577) B3172577
theorem B2143913 : Blo 2113435 2143913 := bbase (se 2 (by rfl) ⟨803967, by rfl⟩ : syracuseStep 2143913 = 1607935) (by norm_num)
theorem B5717101 : Blo 2113435 5717101 := bstep (se 3 (by rfl) ⟨1071956, by rfl⟩ : syracuseStep 5717101 = 2143913) B2143913
theorem B7622801 : Blo 2113435 7622801 := bstep (se 2 (by rfl) ⟨2858550, by rfl⟩ : syracuseStep 7622801 = 5717101) B5717101
theorem B5081867 : Blo 2113435 5081867 := bstep (se 1 (by rfl) ⟨3811400, by rfl⟩ : syracuseStep 5081867 = 7622801) B7622801
theorem B3387911 : Blo 2113435 3387911 := bstep (se 1 (by rfl) ⟨2540933, by rfl⟩ : syracuseStep 3387911 = 5081867) B5081867
theorem B9034429 : Blo 2113435 9034429 := bstep (se 3 (by rfl) ⟨1693955, by rfl⟩ : syracuseStep 9034429 = 3387911) B3387911
theorem B12045905 : Blo 2113435 12045905 := bstep (se 2 (by rfl) ⟨4517214, by rfl⟩ : syracuseStep 12045905 = 9034429) B9034429
theorem B8030603 : Blo 2113435 8030603 := bstep (se 1 (by rfl) ⟨6022952, by rfl⟩ : syracuseStep 8030603 = 12045905) B12045905
theorem B5353735 : Blo 2113435 5353735 := bstep (se 1 (by rfl) ⟨4015301, by rfl⟩ : syracuseStep 5353735 = 8030603) B8030603
theorem B7138313 : Blo 2113435 7138313 := bstep (se 2 (by rfl) ⟨2676867, by rfl⟩ : syracuseStep 7138313 = 5353735) B5353735
theorem B4758875 : Blo 2113435 4758875 := bstep (se 1 (by rfl) ⟨3569156, by rfl⟩ : syracuseStep 4758875 = 7138313) B7138313
theorem B3172583 : Blo 2113435 3172583 := bstep (se 1 (by rfl) ⟨2379437, by rfl⟩ : syracuseStep 3172583 = 4758875) B4758875
theorem B2115055 : Blo 2113435 2115055 := bstep (se 1 (by rfl) ⟨1586291, by rfl⟩ : syracuseStep 2115055 = 3172583) B3172583
theorem B3172589 : Blo 2113435 3172589 := bbase (se 3 (by rfl) ⟨594860, by rfl⟩ : syracuseStep 3172589 = 1189721) (by norm_num)
theorem B2115059 : Blo 2113435 2115059 := bstep (se 1 (by rfl) ⟨1586294, by rfl⟩ : syracuseStep 2115059 = 3172589) B3172589
theorem B4758893 : Blo 2113435 4758893 := bbase (se 3 (by rfl) ⟨892292, by rfl⟩ : syracuseStep 4758893 = 1784585) (by norm_num)
theorem B3172595 : Blo 2113435 3172595 := bstep (se 1 (by rfl) ⟨2379446, by rfl⟩ : syracuseStep 3172595 = 4758893) B4758893
theorem B2115063 : Blo 2113435 2115063 := bstep (se 1 (by rfl) ⟨1586297, by rfl⟩ : syracuseStep 2115063 = 3172595) B3172595
theorem B4015325 : Blo 2113435 4015325 := bbase (se 3 (by rfl) ⟨752873, by rfl⟩ : syracuseStep 4015325 = 1505747) (by norm_num)
theorem B2676883 : Blo 2113435 2676883 := bstep (se 1 (by rfl) ⟨2007662, by rfl⟩ : syracuseStep 2676883 = 4015325) B4015325
theorem B3569177 : Blo 2113435 3569177 := bstep (se 2 (by rfl) ⟨1338441, by rfl⟩ : syracuseStep 3569177 = 2676883) B2676883
theorem B2379451 : Blo 2113435 2379451 := bstep (se 1 (by rfl) ⟨1784588, by rfl⟩ : syracuseStep 2379451 = 3569177) B3569177
theorem B3172601 : Blo 2113435 3172601 := bstep (se 2 (by rfl) ⟨1189725, by rfl⟩ : syracuseStep 3172601 = 2379451) B2379451
theorem B2115067 : Blo 2113435 2115067 := bstep (se 1 (by rfl) ⟨1586300, by rfl⟩ : syracuseStep 2115067 = 3172601) B3172601
theorem B12863573 : Blo 2113435 12863573 := bbase (se 8 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 12863573 = 150745) (by norm_num)
theorem B8575715 : Blo 2113435 8575715 := bstep (se 1 (by rfl) ⟨6431786, by rfl⟩ : syracuseStep 8575715 = 12863573) B12863573
theorem B5717143 : Blo 2113435 5717143 := bstep (se 1 (by rfl) ⟨4287857, by rfl⟩ : syracuseStep 5717143 = 8575715) B8575715
theorem B7622857 : Blo 2113435 7622857 := bstep (se 2 (by rfl) ⟨2858571, by rfl⟩ : syracuseStep 7622857 = 5717143) B5717143
theorem B10163809 : Blo 2113435 10163809 := bstep (se 2 (by rfl) ⟨3811428, by rfl⟩ : syracuseStep 10163809 = 7622857) B7622857
theorem B54206981 : Blo 2113435 54206981 := bstep (se 4 (by rfl) ⟨5081904, by rfl⟩ : syracuseStep 54206981 = 10163809) B10163809
theorem B36137987 : Blo 2113435 36137987 := bstep (se 1 (by rfl) ⟨27103490, by rfl⟩ : syracuseStep 36137987 = 54206981) B54206981
theorem B24091991 : Blo 2113435 24091991 := bstep (se 1 (by rfl) ⟨18068993, by rfl⟩ : syracuseStep 24091991 = 36137987) B36137987
theorem B16061327 : Blo 2113435 16061327 := bstep (se 1 (by rfl) ⟨12045995, by rfl⟩ : syracuseStep 16061327 = 24091991) B24091991
theorem B10707551 : Blo 2113435 10707551 := bstep (se 1 (by rfl) ⟨8030663, by rfl⟩ : syracuseStep 10707551 = 16061327) B16061327
theorem B7138367 : Blo 2113435 7138367 := bstep (se 1 (by rfl) ⟨5353775, by rfl⟩ : syracuseStep 7138367 = 10707551) B10707551
theorem B4758911 : Blo 2113435 4758911 := bstep (se 1 (by rfl) ⟨3569183, by rfl⟩ : syracuseStep 4758911 = 7138367) B7138367
theorem B3172607 : Blo 2113435 3172607 := bstep (se 1 (by rfl) ⟨2379455, by rfl⟩ : syracuseStep 3172607 = 4758911) B4758911
theorem B2115071 : Blo 2113435 2115071 := bstep (se 1 (by rfl) ⟨1586303, by rfl⟩ : syracuseStep 2115071 = 3172607) B3172607
theorem B3172613 : Blo 2113435 3172613 := bbase (se 4 (by rfl) ⟨297432, by rfl⟩ : syracuseStep 3172613 = 594865) (by norm_num)
theorem B2115075 : Blo 2113435 2115075 := bstep (se 1 (by rfl) ⟨1586306, by rfl⟩ : syracuseStep 2115075 = 3172613) B3172613
theorem B3569197 : Blo 2113435 3569197 := bbase (se 3 (by rfl) ⟨669224, by rfl⟩ : syracuseStep 3569197 = 1338449) (by norm_num)
theorem B4758929 : Blo 2113435 4758929 := bstep (se 2 (by rfl) ⟨1784598, by rfl⟩ : syracuseStep 4758929 = 3569197) B3569197
theorem B3172619 : Blo 2113435 3172619 := bstep (se 1 (by rfl) ⟨2379464, by rfl⟩ : syracuseStep 3172619 = 4758929) B4758929
theorem B2115079 : Blo 2113435 2115079 := bstep (se 1 (by rfl) ⟨1586309, by rfl⟩ : syracuseStep 2115079 = 3172619) B3172619
theorem B2379469 : Blo 2113435 2379469 := bbase (se 3 (by rfl) ⟨446150, by rfl⟩ : syracuseStep 2379469 = 892301) (by norm_num)
theorem B3172625 : Blo 2113435 3172625 := bstep (se 2 (by rfl) ⟨1189734, by rfl⟩ : syracuseStep 3172625 = 2379469) B2379469
theorem B2115083 : Blo 2113435 2115083 := bstep (se 1 (by rfl) ⟨1586312, by rfl⟩ : syracuseStep 2115083 = 3172625) B3172625
theorem B7138421 : Blo 2113435 7138421 := bbase (se 5 (by rfl) ⟨334613, by rfl⟩ : syracuseStep 7138421 = 669227) (by norm_num)
theorem B4758947 : Blo 2113435 4758947 := bstep (se 1 (by rfl) ⟨3569210, by rfl⟩ : syracuseStep 4758947 = 7138421) B7138421
theorem B3172631 : Blo 2113435 3172631 := bstep (se 1 (by rfl) ⟨2379473, by rfl⟩ : syracuseStep 3172631 = 4758947) B4758947
theorem B2115087 : Blo 2113435 2115087 := bstep (se 1 (by rfl) ⟨1586315, by rfl⟩ : syracuseStep 2115087 = 3172631) B3172631
theorem B3172637 : Blo 2113435 3172637 := bbase (se 3 (by rfl) ⟨594869, by rfl⟩ : syracuseStep 3172637 = 1189739) (by norm_num)
theorem B2115091 : Blo 2113435 2115091 := bstep (se 1 (by rfl) ⟨1586318, by rfl⟩ : syracuseStep 2115091 = 3172637) B3172637
theorem B4758965 : Blo 2113435 4758965 := bbase (se 5 (by rfl) ⟨223076, by rfl⟩ : syracuseStep 4758965 = 446153) (by norm_num)
theorem B3172643 : Blo 2113435 3172643 := bstep (se 1 (by rfl) ⟨2379482, by rfl⟩ : syracuseStep 3172643 = 4758965) B4758965
theorem B2115095 : Blo 2113435 2115095 := bstep (se 1 (by rfl) ⟨1586321, by rfl⟩ : syracuseStep 2115095 = 3172643) B3172643
theorem B4517309 : Blo 2113435 4517309 := bbase (se 3 (by rfl) ⟨846995, by rfl⟩ : syracuseStep 4517309 = 1693991) (by norm_num)
theorem B12046157 : Blo 2113435 12046157 := bstep (se 3 (by rfl) ⟨2258654, by rfl⟩ : syracuseStep 12046157 = 4517309) B4517309
theorem B8030771 : Blo 2113435 8030771 := bstep (se 1 (by rfl) ⟨6023078, by rfl⟩ : syracuseStep 8030771 = 12046157) B12046157
theorem B5353847 : Blo 2113435 5353847 := bstep (se 1 (by rfl) ⟨4015385, by rfl⟩ : syracuseStep 5353847 = 8030771) B8030771
theorem B3569231 : Blo 2113435 3569231 := bstep (se 1 (by rfl) ⟨2676923, by rfl⟩ : syracuseStep 3569231 = 5353847) B5353847
theorem B2379487 : Blo 2113435 2379487 := bstep (se 1 (by rfl) ⟨1784615, by rfl⟩ : syracuseStep 2379487 = 3569231) B3569231
theorem B3172649 : Blo 2113435 3172649 := bstep (se 2 (by rfl) ⟨1189743, by rfl⟩ : syracuseStep 3172649 = 2379487) B2379487
theorem B2115099 : Blo 2113435 2115099 := bstep (se 1 (by rfl) ⟨1586324, by rfl⟩ : syracuseStep 2115099 = 3172649) B3172649
theorem B4517317 : Blo 2113435 4517317 := bbase (se 4 (by rfl) ⟨423498, by rfl⟩ : syracuseStep 4517317 = 846997) (by norm_num)
theorem B6023089 : Blo 2113435 6023089 := bstep (se 2 (by rfl) ⟨2258658, by rfl⟩ : syracuseStep 6023089 = 4517317) B4517317
theorem B8030785 : Blo 2113435 8030785 := bstep (se 2 (by rfl) ⟨3011544, by rfl⟩ : syracuseStep 8030785 = 6023089) B6023089
theorem B10707713 : Blo 2113435 10707713 := bstep (se 2 (by rfl) ⟨4015392, by rfl⟩ : syracuseStep 10707713 = 8030785) B8030785
theorem B7138475 : Blo 2113435 7138475 := bstep (se 1 (by rfl) ⟨5353856, by rfl⟩ : syracuseStep 7138475 = 10707713) B10707713
theorem B4758983 : Blo 2113435 4758983 := bstep (se 1 (by rfl) ⟨3569237, by rfl⟩ : syracuseStep 4758983 = 7138475) B7138475
theorem B3172655 : Blo 2113435 3172655 := bstep (se 1 (by rfl) ⟨2379491, by rfl⟩ : syracuseStep 3172655 = 4758983) B4758983
theorem B2115103 : Blo 2113435 2115103 := bstep (se 1 (by rfl) ⟨1586327, by rfl⟩ : syracuseStep 2115103 = 3172655) B3172655
theorem B3172661 : Blo 2113435 3172661 := bbase (se 5 (by rfl) ⟨148718, by rfl⟩ : syracuseStep 3172661 = 297437) (by norm_num)
theorem B2115107 : Blo 2113435 2115107 := bstep (se 1 (by rfl) ⟨1586330, by rfl⟩ : syracuseStep 2115107 = 3172661) B3172661
theorem B5353877 : Blo 2113435 5353877 := bbase (se 6 (by rfl) ⟨125481, by rfl⟩ : syracuseStep 5353877 = 250963) (by norm_num)
theorem B3569251 : Blo 2113435 3569251 := bstep (se 1 (by rfl) ⟨2676938, by rfl⟩ : syracuseStep 3569251 = 5353877) B5353877
theorem B4759001 : Blo 2113435 4759001 := bstep (se 2 (by rfl) ⟨1784625, by rfl⟩ : syracuseStep 4759001 = 3569251) B3569251
theorem B3172667 : Blo 2113435 3172667 := bstep (se 1 (by rfl) ⟨2379500, by rfl⟩ : syracuseStep 3172667 = 4759001) B4759001
theorem B2115111 : Blo 2113435 2115111 := bstep (se 1 (by rfl) ⟨1586333, by rfl⟩ : syracuseStep 2115111 = 3172667) B3172667
theorem B2379505 : Blo 2113435 2379505 := bbase (se 2 (by rfl) ⟨892314, by rfl⟩ : syracuseStep 2379505 = 1784629) (by norm_num)
theorem B3172673 : Blo 2113435 3172673 := bstep (se 2 (by rfl) ⟨1189752, by rfl⟩ : syracuseStep 3172673 = 2379505) B2379505
theorem B2115115 : Blo 2113435 2115115 := bstep (se 1 (by rfl) ⟨1586336, by rfl⟩ : syracuseStep 2115115 = 3172673) B3172673
theorem B2289493 : Blo 2113435 2289493 := bbase (se 9 (by rfl) ⟨6707, by rfl⟩ : syracuseStep 2289493 = 13415) (by norm_num)
theorem B3052657 : Blo 2113435 3052657 := bstep (se 2 (by rfl) ⟨1144746, by rfl⟩ : syracuseStep 3052657 = 2289493) B2289493
theorem B4070209 : Blo 2113435 4070209 := bstep (se 2 (by rfl) ⟨1526328, by rfl⟩ : syracuseStep 4070209 = 3052657) B3052657
theorem B5426945 : Blo 2113435 5426945 := bstep (se 2 (by rfl) ⟨2035104, by rfl⟩ : syracuseStep 5426945 = 4070209) B4070209
theorem B3617963 : Blo 2113435 3617963 := bstep (se 1 (by rfl) ⟨2713472, by rfl⟩ : syracuseStep 3617963 = 5426945) B5426945
theorem B2411975 : Blo 2113435 2411975 := bstep (se 1 (by rfl) ⟨1808981, by rfl⟩ : syracuseStep 2411975 = 3617963) B3617963
theorem B6431933 : Blo 2113435 6431933 := bstep (se 3 (by rfl) ⟨1205987, by rfl⟩ : syracuseStep 6431933 = 2411975) B2411975
theorem B17151821 : Blo 2113435 17151821 := bstep (se 3 (by rfl) ⟨3215966, by rfl⟩ : syracuseStep 17151821 = 6431933) B6431933
theorem B11434547 : Blo 2113435 11434547 := bstep (se 1 (by rfl) ⟨8575910, by rfl⟩ : syracuseStep 11434547 = 17151821) B17151821
theorem B30492125 : Blo 2113435 30492125 := bstep (se 3 (by rfl) ⟨5717273, by rfl⟩ : syracuseStep 30492125 = 11434547) B11434547
theorem B20328083 : Blo 2113435 20328083 := bstep (se 1 (by rfl) ⟨15246062, by rfl⟩ : syracuseStep 20328083 = 30492125) B30492125
theorem B13552055 : Blo 2113435 13552055 := bstep (se 1 (by rfl) ⟨10164041, by rfl⟩ : syracuseStep 13552055 = 20328083) B20328083
theorem B9034703 : Blo 2113435 9034703 := bstep (se 1 (by rfl) ⟨6776027, by rfl⟩ : syracuseStep 9034703 = 13552055) B13552055
theorem B6023135 : Blo 2113435 6023135 := bstep (se 1 (by rfl) ⟨4517351, by rfl⟩ : syracuseStep 6023135 = 9034703) B9034703
theorem B4015423 : Blo 2113435 4015423 := bstep (se 1 (by rfl) ⟨3011567, by rfl⟩ : syracuseStep 4015423 = 6023135) B6023135
theorem B5353897 : Blo 2113435 5353897 := bstep (se 2 (by rfl) ⟨2007711, by rfl⟩ : syracuseStep 5353897 = 4015423) B4015423
theorem B7138529 : Blo 2113435 7138529 := bstep (se 2 (by rfl) ⟨2676948, by rfl⟩ : syracuseStep 7138529 = 5353897) B5353897
theorem B4759019 : Blo 2113435 4759019 := bstep (se 1 (by rfl) ⟨3569264, by rfl⟩ : syracuseStep 4759019 = 7138529) B7138529
theorem B3172679 : Blo 2113435 3172679 := bstep (se 1 (by rfl) ⟨2379509, by rfl⟩ : syracuseStep 3172679 = 4759019) B4759019
theorem B2115119 : Blo 2113435 2115119 := bstep (se 1 (by rfl) ⟨1586339, by rfl⟩ : syracuseStep 2115119 = 3172679) B3172679
theorem B3172685 : Blo 2113435 3172685 := bbase (se 3 (by rfl) ⟨594878, by rfl⟩ : syracuseStep 3172685 = 1189757) (by norm_num)
theorem B2115123 : Blo 2113435 2115123 := bstep (se 1 (by rfl) ⟨1586342, by rfl⟩ : syracuseStep 2115123 = 3172685) B3172685
theorem B4759037 : Blo 2113435 4759037 := bbase (se 3 (by rfl) ⟨892319, by rfl⟩ : syracuseStep 4759037 = 1784639) (by norm_num)
theorem B3172691 : Blo 2113435 3172691 := bstep (se 1 (by rfl) ⟨2379518, by rfl⟩ : syracuseStep 3172691 = 4759037) B4759037
theorem B2115127 : Blo 2113435 2115127 := bstep (se 1 (by rfl) ⟨1586345, by rfl⟩ : syracuseStep 2115127 = 3172691) B3172691
theorem B3569285 : Blo 2113435 3569285 := bbase (se 4 (by rfl) ⟨334620, by rfl⟩ : syracuseStep 3569285 = 669241) (by norm_num)
theorem B2379523 : Blo 2113435 2379523 := bstep (se 1 (by rfl) ⟨1784642, by rfl⟩ : syracuseStep 2379523 = 3569285) B3569285
theorem B3172697 : Blo 2113435 3172697 := bstep (se 2 (by rfl) ⟨1189761, by rfl⟩ : syracuseStep 3172697 = 2379523) B2379523
theorem B2115131 : Blo 2113435 2115131 := bstep (se 1 (by rfl) ⟨1586348, by rfl⟩ : syracuseStep 2115131 = 3172697) B3172697
theorem B16061813 : Blo 2113435 16061813 := bbase (se 5 (by rfl) ⟨752897, by rfl⟩ : syracuseStep 16061813 = 1505795) (by norm_num)
theorem B10707875 : Blo 2113435 10707875 := bstep (se 1 (by rfl) ⟨8030906, by rfl⟩ : syracuseStep 10707875 = 16061813) B16061813
theorem B7138583 : Blo 2113435 7138583 := bstep (se 1 (by rfl) ⟨5353937, by rfl⟩ : syracuseStep 7138583 = 10707875) B10707875
theorem B4759055 : Blo 2113435 4759055 := bstep (se 1 (by rfl) ⟨3569291, by rfl⟩ : syracuseStep 4759055 = 7138583) B7138583
theorem B3172703 : Blo 2113435 3172703 := bstep (se 1 (by rfl) ⟨2379527, by rfl⟩ : syracuseStep 3172703 = 4759055) B4759055
theorem B2115135 : Blo 2113435 2115135 := bstep (se 1 (by rfl) ⟨1586351, by rfl⟩ : syracuseStep 2115135 = 3172703) B3172703
theorem B3172709 : Blo 2113435 3172709 := bbase (se 4 (by rfl) ⟨297441, by rfl⟩ : syracuseStep 3172709 = 594883) (by norm_num)
theorem B2115139 : Blo 2113435 2115139 := bstep (se 1 (by rfl) ⟨1586354, by rfl⟩ : syracuseStep 2115139 = 3172709) B3172709
theorem B4015469 : Blo 2113435 4015469 := bbase (se 3 (by rfl) ⟨752900, by rfl⟩ : syracuseStep 4015469 = 1505801) (by norm_num)
theorem B2676979 : Blo 2113435 2676979 := bstep (se 1 (by rfl) ⟨2007734, by rfl⟩ : syracuseStep 2676979 = 4015469) B4015469
theorem B3569305 : Blo 2113435 3569305 := bstep (se 2 (by rfl) ⟨1338489, by rfl⟩ : syracuseStep 3569305 = 2676979) B2676979
theorem B4759073 : Blo 2113435 4759073 := bstep (se 2 (by rfl) ⟨1784652, by rfl⟩ : syracuseStep 4759073 = 3569305) B3569305
theorem B3172715 : Blo 2113435 3172715 := bstep (se 1 (by rfl) ⟨2379536, by rfl⟩ : syracuseStep 3172715 = 4759073) B4759073
theorem B2115143 : Blo 2113435 2115143 := bstep (se 1 (by rfl) ⟨1586357, by rfl⟩ : syracuseStep 2115143 = 3172715) B3172715
theorem B2379541 : Blo 2113435 2379541 := bbase (se 6 (by rfl) ⟨55770, by rfl⟩ : syracuseStep 2379541 = 111541) (by norm_num)
theorem B3172721 : Blo 2113435 3172721 := bstep (se 2 (by rfl) ⟨1189770, by rfl⟩ : syracuseStep 3172721 = 2379541) B2379541
theorem B2115147 : Blo 2113435 2115147 := bstep (se 1 (by rfl) ⟨1586360, by rfl⟩ : syracuseStep 2115147 = 3172721) B3172721
theorem B2676989 : Blo 2113435 2676989 := bbase (se 3 (by rfl) ⟨501935, by rfl⟩ : syracuseStep 2676989 = 1003871) (by norm_num)
theorem B7138637 : Blo 2113435 7138637 := bstep (se 3 (by rfl) ⟨1338494, by rfl⟩ : syracuseStep 7138637 = 2676989) B2676989
theorem B4759091 : Blo 2113435 4759091 := bstep (se 1 (by rfl) ⟨3569318, by rfl⟩ : syracuseStep 4759091 = 7138637) B7138637
theorem B3172727 : Blo 2113435 3172727 := bstep (se 1 (by rfl) ⟨2379545, by rfl⟩ : syracuseStep 3172727 = 4759091) B4759091
theorem B2115151 : Blo 2113435 2115151 := bstep (se 1 (by rfl) ⟨1586363, by rfl⟩ : syracuseStep 2115151 = 3172727) B3172727
theorem B3172733 : Blo 2113435 3172733 := bbase (se 3 (by rfl) ⟨594887, by rfl⟩ : syracuseStep 3172733 = 1189775) (by norm_num)
theorem B2115155 : Blo 2113435 2115155 := bstep (se 1 (by rfl) ⟨1586366, by rfl⟩ : syracuseStep 2115155 = 3172733) B3172733
theorem B4759109 : Blo 2113435 4759109 := bbase (se 4 (by rfl) ⟨446166, by rfl⟩ : syracuseStep 4759109 = 892333) (by norm_num)
theorem B3172739 : Blo 2113435 3172739 := bstep (se 1 (by rfl) ⟨2379554, by rfl⟩ : syracuseStep 3172739 = 4759109) B4759109
theorem B2115159 : Blo 2113435 2115159 := bstep (se 1 (by rfl) ⟨1586369, by rfl⟩ : syracuseStep 2115159 = 3172739) B3172739
theorem B3388085 : Blo 2113435 3388085 := bbase (se 5 (by rfl) ⟨158816, by rfl⟩ : syracuseStep 3388085 = 317633) (by norm_num)
theorem B2258723 : Blo 2113435 2258723 := bstep (se 1 (by rfl) ⟨1694042, by rfl⟩ : syracuseStep 2258723 = 3388085) B3388085
theorem B6023261 : Blo 2113435 6023261 := bstep (se 3 (by rfl) ⟨1129361, by rfl⟩ : syracuseStep 6023261 = 2258723) B2258723
theorem B4015507 : Blo 2113435 4015507 := bstep (se 1 (by rfl) ⟨3011630, by rfl⟩ : syracuseStep 4015507 = 6023261) B6023261
theorem B5354009 : Blo 2113435 5354009 := bstep (se 2 (by rfl) ⟨2007753, by rfl⟩ : syracuseStep 5354009 = 4015507) B4015507
theorem B3569339 : Blo 2113435 3569339 := bstep (se 1 (by rfl) ⟨2677004, by rfl⟩ : syracuseStep 3569339 = 5354009) B5354009
theorem B2379559 : Blo 2113435 2379559 := bstep (se 1 (by rfl) ⟨1784669, by rfl⟩ : syracuseStep 2379559 = 3569339) B3569339
theorem B3172745 : Blo 2113435 3172745 := bstep (se 2 (by rfl) ⟨1189779, by rfl⟩ : syracuseStep 3172745 = 2379559) B2379559
theorem B2115163 : Blo 2113435 2115163 := bstep (se 1 (by rfl) ⟨1586372, by rfl⟩ : syracuseStep 2115163 = 3172745) B3172745
theorem B10708037 : Blo 2113435 10708037 := bbase (se 4 (by rfl) ⟨1003878, by rfl⟩ : syracuseStep 10708037 = 2007757) (by norm_num)
theorem B7138691 : Blo 2113435 7138691 := bstep (se 1 (by rfl) ⟨5354018, by rfl⟩ : syracuseStep 7138691 = 10708037) B10708037
theorem B4759127 : Blo 2113435 4759127 := bstep (se 1 (by rfl) ⟨3569345, by rfl⟩ : syracuseStep 4759127 = 7138691) B7138691
theorem B3172751 : Blo 2113435 3172751 := bstep (se 1 (by rfl) ⟨2379563, by rfl⟩ : syracuseStep 3172751 = 4759127) B4759127
theorem B2115167 : Blo 2113435 2115167 := bstep (se 1 (by rfl) ⟨1586375, by rfl⟩ : syracuseStep 2115167 = 3172751) B3172751
theorem B3172757 : Blo 2113435 3172757 := bbase (se 6 (by rfl) ⟨74361, by rfl⟩ : syracuseStep 3172757 = 148723) (by norm_num)
theorem B2115171 : Blo 2113435 2115171 := bstep (se 1 (by rfl) ⟨1586378, by rfl⟩ : syracuseStep 2115171 = 3172757) B3172757
theorem B4288069 : Blo 2113435 4288069 := bbase (se 4 (by rfl) ⟨402006, by rfl⟩ : syracuseStep 4288069 = 804013) (by norm_num)
theorem B22869701 : Blo 2113435 22869701 := bstep (se 4 (by rfl) ⟨2144034, by rfl⟩ : syracuseStep 22869701 = 4288069) B4288069
theorem B15246467 : Blo 2113435 15246467 := bstep (se 1 (by rfl) ⟨11434850, by rfl⟩ : syracuseStep 15246467 = 22869701) B22869701
theorem B10164311 : Blo 2113435 10164311 := bstep (se 1 (by rfl) ⟨7623233, by rfl⟩ : syracuseStep 10164311 = 15246467) B15246467
theorem B6776207 : Blo 2113435 6776207 := bstep (se 1 (by rfl) ⟨5082155, by rfl⟩ : syracuseStep 6776207 = 10164311) B10164311
theorem B4517471 : Blo 2113435 4517471 := bstep (se 1 (by rfl) ⟨3388103, by rfl⟩ : syracuseStep 4517471 = 6776207) B6776207
theorem B12046589 : Blo 2113435 12046589 := bstep (se 3 (by rfl) ⟨2258735, by rfl⟩ : syracuseStep 12046589 = 4517471) B4517471
theorem B8031059 : Blo 2113435 8031059 := bstep (se 1 (by rfl) ⟨6023294, by rfl⟩ : syracuseStep 8031059 = 12046589) B12046589
theorem B5354039 : Blo 2113435 5354039 := bstep (se 1 (by rfl) ⟨4015529, by rfl⟩ : syracuseStep 5354039 = 8031059) B8031059
theorem B3569359 : Blo 2113435 3569359 := bstep (se 1 (by rfl) ⟨2677019, by rfl⟩ : syracuseStep 3569359 = 5354039) B5354039
theorem B4759145 : Blo 2113435 4759145 := bstep (se 2 (by rfl) ⟨1784679, by rfl⟩ : syracuseStep 4759145 = 3569359) B3569359
theorem B3172763 : Blo 2113435 3172763 := bstep (se 1 (by rfl) ⟨2379572, by rfl⟩ : syracuseStep 3172763 = 4759145) B4759145
theorem B2115175 : Blo 2113435 2115175 := bstep (se 1 (by rfl) ⟨1586381, by rfl⟩ : syracuseStep 2115175 = 3172763) B3172763
theorem B2379577 : Blo 2113435 2379577 := bbase (se 2 (by rfl) ⟨892341, by rfl⟩ : syracuseStep 2379577 = 1784683) (by norm_num)
theorem B3172769 : Blo 2113435 3172769 := bstep (se 2 (by rfl) ⟨1189788, by rfl⟩ : syracuseStep 3172769 = 2379577) B2379577
theorem B2115179 : Blo 2113435 2115179 := bstep (se 1 (by rfl) ⟨1586384, by rfl⟩ : syracuseStep 2115179 = 3172769) B3172769
theorem B6023317 : Blo 2113435 6023317 := bbase (se 6 (by rfl) ⟨141171, by rfl⟩ : syracuseStep 6023317 = 282343) (by norm_num)
theorem B8031089 : Blo 2113435 8031089 := bstep (se 2 (by rfl) ⟨3011658, by rfl⟩ : syracuseStep 8031089 = 6023317) B6023317
theorem B5354059 : Blo 2113435 5354059 := bstep (se 1 (by rfl) ⟨4015544, by rfl⟩ : syracuseStep 5354059 = 8031089) B8031089
theorem B7138745 : Blo 2113435 7138745 := bstep (se 2 (by rfl) ⟨2677029, by rfl⟩ : syracuseStep 7138745 = 5354059) B5354059
theorem B4759163 : Blo 2113435 4759163 := bstep (se 1 (by rfl) ⟨3569372, by rfl⟩ : syracuseStep 4759163 = 7138745) B7138745
theorem B3172775 : Blo 2113435 3172775 := bstep (se 1 (by rfl) ⟨2379581, by rfl⟩ : syracuseStep 3172775 = 4759163) B4759163
theorem B2115183 : Blo 2113435 2115183 := bstep (se 1 (by rfl) ⟨1586387, by rfl⟩ : syracuseStep 2115183 = 3172775) B3172775
theorem B3172781 : Blo 2113435 3172781 := bbase (se 3 (by rfl) ⟨594896, by rfl⟩ : syracuseStep 3172781 = 1189793) (by norm_num)
theorem B2115187 : Blo 2113435 2115187 := bstep (se 1 (by rfl) ⟨1586390, by rfl⟩ : syracuseStep 2115187 = 3172781) B3172781
theorem B4759181 : Blo 2113435 4759181 := bbase (se 3 (by rfl) ⟨892346, by rfl⟩ : syracuseStep 4759181 = 1784693) (by norm_num)
theorem B3172787 : Blo 2113435 3172787 := bstep (se 1 (by rfl) ⟨2379590, by rfl⟩ : syracuseStep 3172787 = 4759181) B4759181
theorem B2115191 : Blo 2113435 2115191 := bstep (se 1 (by rfl) ⟨1586393, by rfl⟩ : syracuseStep 2115191 = 3172787) B3172787
theorem B2677045 : Blo 2113435 2677045 := bbase (se 5 (by rfl) ⟨125486, by rfl⟩ : syracuseStep 2677045 = 250973) (by norm_num)
theorem B3569393 : Blo 2113435 3569393 := bstep (se 2 (by rfl) ⟨1338522, by rfl⟩ : syracuseStep 3569393 = 2677045) B2677045
theorem B2379595 : Blo 2113435 2379595 := bstep (se 1 (by rfl) ⟨1784696, by rfl⟩ : syracuseStep 2379595 = 3569393) B3569393
theorem B3172793 : Blo 2113435 3172793 := bstep (se 2 (by rfl) ⟨1189797, by rfl⟩ : syracuseStep 3172793 = 2379595) B2379595
theorem B2115195 : Blo 2113435 2115195 := bstep (se 1 (by rfl) ⟨1586396, by rfl⟩ : syracuseStep 2115195 = 3172793) B3172793
theorem B4579157 : Blo 2113435 4579157 := bbase (se 9 (by rfl) ⟨13415, by rfl⟩ : syracuseStep 4579157 = 26831) (by norm_num)
theorem B3052771 : Blo 2113435 3052771 := bstep (se 1 (by rfl) ⟨2289578, by rfl⟩ : syracuseStep 3052771 = 4579157) B4579157
theorem B16281445 : Blo 2113435 16281445 := bstep (se 4 (by rfl) ⟨1526385, by rfl⟩ : syracuseStep 16281445 = 3052771) B3052771
theorem B21708593 : Blo 2113435 21708593 := bstep (se 2 (by rfl) ⟨8140722, by rfl⟩ : syracuseStep 21708593 = 16281445) B16281445
theorem B14472395 : Blo 2113435 14472395 := bstep (se 1 (by rfl) ⟨10854296, by rfl⟩ : syracuseStep 14472395 = 21708593) B21708593
theorem B9648263 : Blo 2113435 9648263 := bstep (se 1 (by rfl) ⟨7236197, by rfl⟩ : syracuseStep 9648263 = 14472395) B14472395
theorem B6432175 : Blo 2113435 6432175 := bstep (se 1 (by rfl) ⟨4824131, by rfl⟩ : syracuseStep 6432175 = 9648263) B9648263
theorem B34304933 : Blo 2113435 34304933 := bstep (se 4 (by rfl) ⟨3216087, by rfl⟩ : syracuseStep 34304933 = 6432175) B6432175
theorem B22869955 : Blo 2113435 22869955 := bstep (se 1 (by rfl) ⟨17152466, by rfl⟩ : syracuseStep 22869955 = 34304933) B34304933
theorem B30493273 : Blo 2113435 30493273 := bstep (se 2 (by rfl) ⟨11434977, by rfl⟩ : syracuseStep 30493273 = 22869955) B22869955
theorem B40657697 : Blo 2113435 40657697 := bstep (se 2 (by rfl) ⟨15246636, by rfl⟩ : syracuseStep 40657697 = 30493273) B30493273
theorem B27105131 : Blo 2113435 27105131 := bstep (se 1 (by rfl) ⟨20328848, by rfl⟩ : syracuseStep 27105131 = 40657697) B40657697
theorem B18070087 : Blo 2113435 18070087 := bstep (se 1 (by rfl) ⟨13552565, by rfl⟩ : syracuseStep 18070087 = 27105131) B27105131
theorem B24093449 : Blo 2113435 24093449 := bstep (se 2 (by rfl) ⟨9035043, by rfl⟩ : syracuseStep 24093449 = 18070087) B18070087
theorem B16062299 : Blo 2113435 16062299 := bstep (se 1 (by rfl) ⟨12046724, by rfl⟩ : syracuseStep 16062299 = 24093449) B24093449
theorem B10708199 : Blo 2113435 10708199 := bstep (se 1 (by rfl) ⟨8031149, by rfl⟩ : syracuseStep 10708199 = 16062299) B16062299
theorem B7138799 : Blo 2113435 7138799 := bstep (se 1 (by rfl) ⟨5354099, by rfl⟩ : syracuseStep 7138799 = 10708199) B10708199
theorem B4759199 : Blo 2113435 4759199 := bstep (se 1 (by rfl) ⟨3569399, by rfl⟩ : syracuseStep 4759199 = 7138799) B7138799
theorem B3172799 : Blo 2113435 3172799 := bstep (se 1 (by rfl) ⟨2379599, by rfl⟩ : syracuseStep 3172799 = 4759199) B4759199
theorem B2115199 : Blo 2113435 2115199 := bstep (se 1 (by rfl) ⟨1586399, by rfl⟩ : syracuseStep 2115199 = 3172799) B3172799
theorem B3172805 : Blo 2113435 3172805 := bbase (se 4 (by rfl) ⟨297450, by rfl⟩ : syracuseStep 3172805 = 594901) (by norm_num)
theorem B2115203 : Blo 2113435 2115203 := bstep (se 1 (by rfl) ⟨1586402, by rfl⟩ : syracuseStep 2115203 = 3172805) B3172805
theorem B3569413 : Blo 2113435 3569413 := bbase (se 4 (by rfl) ⟨334632, by rfl⟩ : syracuseStep 3569413 = 669265) (by norm_num)
theorem B4759217 : Blo 2113435 4759217 := bstep (se 2 (by rfl) ⟨1784706, by rfl⟩ : syracuseStep 4759217 = 3569413) B3569413
theorem B3172811 : Blo 2113435 3172811 := bstep (se 1 (by rfl) ⟨2379608, by rfl⟩ : syracuseStep 3172811 = 4759217) B4759217
theorem B2115207 : Blo 2113435 2115207 := bstep (se 1 (by rfl) ⟨1586405, by rfl⟩ : syracuseStep 2115207 = 3172811) B3172811
theorem B2379613 : Blo 2113435 2379613 := bbase (se 3 (by rfl) ⟨446177, by rfl⟩ : syracuseStep 2379613 = 892355) (by norm_num)
theorem B3172817 : Blo 2113435 3172817 := bstep (se 2 (by rfl) ⟨1189806, by rfl⟩ : syracuseStep 3172817 = 2379613) B2379613
theorem B2115211 : Blo 2113435 2115211 := bstep (se 1 (by rfl) ⟨1586408, by rfl⟩ : syracuseStep 2115211 = 3172817) B3172817
theorem B7138853 : Blo 2113435 7138853 := bbase (se 4 (by rfl) ⟨669267, by rfl⟩ : syracuseStep 7138853 = 1338535) (by norm_num)
theorem B4759235 : Blo 2113435 4759235 := bstep (se 1 (by rfl) ⟨3569426, by rfl⟩ : syracuseStep 4759235 = 7138853) B7138853
theorem B3172823 : Blo 2113435 3172823 := bstep (se 1 (by rfl) ⟨2379617, by rfl⟩ : syracuseStep 3172823 = 4759235) B4759235
theorem B2115215 : Blo 2113435 2115215 := bstep (se 1 (by rfl) ⟨1586411, by rfl⟩ : syracuseStep 2115215 = 3172823) B3172823
theorem B3172829 : Blo 2113435 3172829 := bbase (se 3 (by rfl) ⟨594905, by rfl⟩ : syracuseStep 3172829 = 1189811) (by norm_num)
theorem B2115219 : Blo 2113435 2115219 := bstep (se 1 (by rfl) ⟨1586414, by rfl⟩ : syracuseStep 2115219 = 3172829) B3172829
theorem B4759253 : Blo 2113435 4759253 := bbase (se 7 (by rfl) ⟨55772, by rfl⟩ : syracuseStep 4759253 = 111545) (by norm_num)
theorem B3172835 : Blo 2113435 3172835 := bstep (se 1 (by rfl) ⟨2379626, by rfl⟩ : syracuseStep 3172835 = 4759253) B4759253
theorem B2115223 : Blo 2113435 2115223 := bstep (se 1 (by rfl) ⟨1586417, by rfl⟩ : syracuseStep 2115223 = 3172835) B3172835
theorem B3052813 : Blo 2113435 3052813 := bbase (se 3 (by rfl) ⟨572402, by rfl⟩ : syracuseStep 3052813 = 1144805) (by norm_num)
theorem B4070417 : Blo 2113435 4070417 := bstep (se 2 (by rfl) ⟨1526406, by rfl⟩ : syracuseStep 4070417 = 3052813) B3052813
theorem B43417781 : Blo 2113435 43417781 := bstep (se 5 (by rfl) ⟨2035208, by rfl⟩ : syracuseStep 43417781 = 4070417) B4070417
theorem B28945187 : Blo 2113435 28945187 := bstep (se 1 (by rfl) ⟨21708890, by rfl⟩ : syracuseStep 28945187 = 43417781) B43417781
theorem B19296791 : Blo 2113435 19296791 := bstep (se 1 (by rfl) ⟨14472593, by rfl⟩ : syracuseStep 19296791 = 28945187) B28945187
theorem B12864527 : Blo 2113435 12864527 := bstep (se 1 (by rfl) ⟨9648395, by rfl⟩ : syracuseStep 12864527 = 19296791) B19296791
theorem B8576351 : Blo 2113435 8576351 := bstep (se 1 (by rfl) ⟨6432263, by rfl⟩ : syracuseStep 8576351 = 12864527) B12864527
theorem B5717567 : Blo 2113435 5717567 := bstep (se 1 (by rfl) ⟨4288175, by rfl⟩ : syracuseStep 5717567 = 8576351) B8576351
theorem B3811711 : Blo 2113435 3811711 := bstep (se 1 (by rfl) ⟨2858783, by rfl⟩ : syracuseStep 3811711 = 5717567) B5717567
theorem B5082281 : Blo 2113435 5082281 := bstep (se 2 (by rfl) ⟨1905855, by rfl⟩ : syracuseStep 5082281 = 3811711) B3811711
theorem B3388187 : Blo 2113435 3388187 := bstep (se 1 (by rfl) ⟨2541140, by rfl⟩ : syracuseStep 3388187 = 5082281) B5082281
theorem B9035165 : Blo 2113435 9035165 := bstep (se 3 (by rfl) ⟨1694093, by rfl⟩ : syracuseStep 9035165 = 3388187) B3388187
theorem B6023443 : Blo 2113435 6023443 := bstep (se 1 (by rfl) ⟨4517582, by rfl⟩ : syracuseStep 6023443 = 9035165) B9035165
theorem B8031257 : Blo 2113435 8031257 := bstep (se 2 (by rfl) ⟨3011721, by rfl⟩ : syracuseStep 8031257 = 6023443) B6023443
theorem B5354171 : Blo 2113435 5354171 := bstep (se 1 (by rfl) ⟨4015628, by rfl⟩ : syracuseStep 5354171 = 8031257) B8031257
theorem B3569447 : Blo 2113435 3569447 := bstep (se 1 (by rfl) ⟨2677085, by rfl⟩ : syracuseStep 3569447 = 5354171) B5354171
theorem B2379631 : Blo 2113435 2379631 := bstep (se 1 (by rfl) ⟨1784723, by rfl⟩ : syracuseStep 2379631 = 3569447) B3569447
theorem B3172841 : Blo 2113435 3172841 := bstep (se 2 (by rfl) ⟨1189815, by rfl⟩ : syracuseStep 3172841 = 2379631) B2379631
theorem B2115227 : Blo 2113435 2115227 := bstep (se 1 (by rfl) ⟨1586420, by rfl⟩ : syracuseStep 2115227 = 3172841) B3172841
theorem B3811717 : Blo 2113435 3811717 := bbase (se 4 (by rfl) ⟨357348, by rfl⟩ : syracuseStep 3811717 = 714697) (by norm_num)
theorem B20329157 : Blo 2113435 20329157 := bstep (se 4 (by rfl) ⟨1905858, by rfl⟩ : syracuseStep 20329157 = 3811717) B3811717
theorem B13552771 : Blo 2113435 13552771 := bstep (se 1 (by rfl) ⟨10164578, by rfl⟩ : syracuseStep 13552771 = 20329157) B20329157
theorem B18070361 : Blo 2113435 18070361 := bstep (se 2 (by rfl) ⟨6776385, by rfl⟩ : syracuseStep 18070361 = 13552771) B13552771
theorem B12046907 : Blo 2113435 12046907 := bstep (se 1 (by rfl) ⟨9035180, by rfl⟩ : syracuseStep 12046907 = 18070361) B18070361
theorem B8031271 : Blo 2113435 8031271 := bstep (se 1 (by rfl) ⟨6023453, by rfl⟩ : syracuseStep 8031271 = 12046907) B12046907
theorem B10708361 : Blo 2113435 10708361 := bstep (se 2 (by rfl) ⟨4015635, by rfl⟩ : syracuseStep 10708361 = 8031271) B8031271
theorem B7138907 : Blo 2113435 7138907 := bstep (se 1 (by rfl) ⟨5354180, by rfl⟩ : syracuseStep 7138907 = 10708361) B10708361
theorem B4759271 : Blo 2113435 4759271 := bstep (se 1 (by rfl) ⟨3569453, by rfl⟩ : syracuseStep 4759271 = 7138907) B7138907
theorem B3172847 : Blo 2113435 3172847 := bstep (se 1 (by rfl) ⟨2379635, by rfl⟩ : syracuseStep 3172847 = 4759271) B4759271
theorem B2115231 : Blo 2113435 2115231 := bstep (se 1 (by rfl) ⟨1586423, by rfl⟩ : syracuseStep 2115231 = 3172847) B3172847
theorem B3172853 : Blo 2113435 3172853 := bbase (se 5 (by rfl) ⟨148727, by rfl⟩ : syracuseStep 3172853 = 297455) (by norm_num)
theorem B2115235 : Blo 2113435 2115235 := bstep (se 1 (by rfl) ⟨1586426, by rfl⟩ : syracuseStep 2115235 = 3172853) B3172853
theorem B6023477 : Blo 2113435 6023477 := bbase (se 5 (by rfl) ⟨282350, by rfl⟩ : syracuseStep 6023477 = 564701) (by norm_num)
theorem B4015651 : Blo 2113435 4015651 := bstep (se 1 (by rfl) ⟨3011738, by rfl⟩ : syracuseStep 4015651 = 6023477) B6023477
theorem B5354201 : Blo 2113435 5354201 := bstep (se 2 (by rfl) ⟨2007825, by rfl⟩ : syracuseStep 5354201 = 4015651) B4015651
theorem B3569467 : Blo 2113435 3569467 := bstep (se 1 (by rfl) ⟨2677100, by rfl⟩ : syracuseStep 3569467 = 5354201) B5354201
theorem B4759289 : Blo 2113435 4759289 := bstep (se 2 (by rfl) ⟨1784733, by rfl⟩ : syracuseStep 4759289 = 3569467) B3569467
theorem B3172859 : Blo 2113435 3172859 := bstep (se 1 (by rfl) ⟨2379644, by rfl⟩ : syracuseStep 3172859 = 4759289) B4759289
theorem B2115239 : Blo 2113435 2115239 := bstep (se 1 (by rfl) ⟨1586429, by rfl⟩ : syracuseStep 2115239 = 3172859) B3172859
theorem B2379649 : Blo 2113435 2379649 := bbase (se 2 (by rfl) ⟨892368, by rfl⟩ : syracuseStep 2379649 = 1784737) (by norm_num)
theorem B3172865 : Blo 2113435 3172865 := bstep (se 2 (by rfl) ⟨1189824, by rfl⟩ : syracuseStep 3172865 = 2379649) B2379649
theorem B2115243 : Blo 2113435 2115243 := bstep (se 1 (by rfl) ⟨1586432, by rfl⟩ : syracuseStep 2115243 = 3172865) B3172865
theorem B5354221 : Blo 2113435 5354221 := bbase (se 3 (by rfl) ⟨1003916, by rfl⟩ : syracuseStep 5354221 = 2007833) (by norm_num)
theorem B7138961 : Blo 2113435 7138961 := bstep (se 2 (by rfl) ⟨2677110, by rfl⟩ : syracuseStep 7138961 = 5354221) B5354221
theorem B4759307 : Blo 2113435 4759307 := bstep (se 1 (by rfl) ⟨3569480, by rfl⟩ : syracuseStep 4759307 = 7138961) B7138961
theorem B3172871 : Blo 2113435 3172871 := bstep (se 1 (by rfl) ⟨2379653, by rfl⟩ : syracuseStep 3172871 = 4759307) B4759307
theorem B2115247 : Blo 2113435 2115247 := bstep (se 1 (by rfl) ⟨1586435, by rfl⟩ : syracuseStep 2115247 = 3172871) B3172871
theorem B3172877 : Blo 2113435 3172877 := bbase (se 3 (by rfl) ⟨594914, by rfl⟩ : syracuseStep 3172877 = 1189829) (by norm_num)
theorem B2115251 : Blo 2113435 2115251 := bstep (se 1 (by rfl) ⟨1586438, by rfl⟩ : syracuseStep 2115251 = 3172877) B3172877
theorem B4759325 : Blo 2113435 4759325 := bbase (se 3 (by rfl) ⟨892373, by rfl⟩ : syracuseStep 4759325 = 1784747) (by norm_num)
theorem B3172883 : Blo 2113435 3172883 := bstep (se 1 (by rfl) ⟨2379662, by rfl⟩ : syracuseStep 3172883 = 4759325) B4759325
theorem B2115255 : Blo 2113435 2115255 := bstep (se 1 (by rfl) ⟨1586441, by rfl⟩ : syracuseStep 2115255 = 3172883) B3172883
theorem B3569501 : Blo 2113435 3569501 := bbase (se 3 (by rfl) ⟨669281, by rfl⟩ : syracuseStep 3569501 = 1338563) (by norm_num)
theorem B2379667 : Blo 2113435 2379667 := bstep (se 1 (by rfl) ⟨1784750, by rfl⟩ : syracuseStep 2379667 = 3569501) B3569501
theorem B3172889 : Blo 2113435 3172889 := bstep (se 2 (by rfl) ⟨1189833, by rfl⟩ : syracuseStep 3172889 = 2379667) B2379667
theorem B2115259 : Blo 2113435 2115259 := bstep (se 1 (by rfl) ⟨1586444, by rfl⟩ : syracuseStep 2115259 = 3172889) B3172889
theorem B9035317 : Blo 2113435 9035317 := bbase (se 5 (by rfl) ⟨423530, by rfl⟩ : syracuseStep 9035317 = 847061) (by norm_num)
theorem B12047089 : Blo 2113435 12047089 := bstep (se 2 (by rfl) ⟨4517658, by rfl⟩ : syracuseStep 12047089 = 9035317) B9035317
theorem B16062785 : Blo 2113435 16062785 := bstep (se 2 (by rfl) ⟨6023544, by rfl⟩ : syracuseStep 16062785 = 12047089) B12047089
theorem B10708523 : Blo 2113435 10708523 := bstep (se 1 (by rfl) ⟨8031392, by rfl⟩ : syracuseStep 10708523 = 16062785) B16062785
theorem B7139015 : Blo 2113435 7139015 := bstep (se 1 (by rfl) ⟨5354261, by rfl⟩ : syracuseStep 7139015 = 10708523) B10708523
theorem B4759343 : Blo 2113435 4759343 := bstep (se 1 (by rfl) ⟨3569507, by rfl⟩ : syracuseStep 4759343 = 7139015) B7139015
theorem B3172895 : Blo 2113435 3172895 := bstep (se 1 (by rfl) ⟨2379671, by rfl⟩ : syracuseStep 3172895 = 4759343) B4759343
theorem B2115263 : Blo 2113435 2115263 := bstep (se 1 (by rfl) ⟨1586447, by rfl⟩ : syracuseStep 2115263 = 3172895) B3172895
theorem B3172901 : Blo 2113435 3172901 := bbase (se 4 (by rfl) ⟨297459, by rfl⟩ : syracuseStep 3172901 = 594919) (by norm_num)
theorem B2115267 : Blo 2113435 2115267 := bstep (se 1 (by rfl) ⟨1586450, by rfl⟩ : syracuseStep 2115267 = 3172901) B3172901
theorem B2677141 : Blo 2113435 2677141 := bbase (se 6 (by rfl) ⟨62745, by rfl⟩ : syracuseStep 2677141 = 125491) (by norm_num)
theorem B3569521 : Blo 2113435 3569521 := bstep (se 2 (by rfl) ⟨1338570, by rfl⟩ : syracuseStep 3569521 = 2677141) B2677141
theorem B4759361 : Blo 2113435 4759361 := bstep (se 2 (by rfl) ⟨1784760, by rfl⟩ : syracuseStep 4759361 = 3569521) B3569521
theorem B3172907 : Blo 2113435 3172907 := bstep (se 1 (by rfl) ⟨2379680, by rfl⟩ : syracuseStep 3172907 = 4759361) B4759361
theorem B2115271 : Blo 2113435 2115271 := bstep (se 1 (by rfl) ⟨1586453, by rfl⟩ : syracuseStep 2115271 = 3172907) B3172907
theorem B2379685 : Blo 2113435 2379685 := bbase (se 4 (by rfl) ⟨223095, by rfl⟩ : syracuseStep 2379685 = 446191) (by norm_num)
theorem B3172913 : Blo 2113435 3172913 := bstep (se 2 (by rfl) ⟨1189842, by rfl⟩ : syracuseStep 3172913 = 2379685) B2379685
theorem B2115275 : Blo 2113435 2115275 := bstep (se 1 (by rfl) ⟨1586456, by rfl⟩ : syracuseStep 2115275 = 3172913) B3172913
theorem B11435413 : Blo 2113435 11435413 := bbase (se 6 (by rfl) ⟨268017, by rfl⟩ : syracuseStep 11435413 = 536035) (by norm_num)
theorem B15247217 : Blo 2113435 15247217 := bstep (se 2 (by rfl) ⟨5717706, by rfl⟩ : syracuseStep 15247217 = 11435413) B11435413
theorem B10164811 : Blo 2113435 10164811 := bstep (se 1 (by rfl) ⟨7623608, by rfl⟩ : syracuseStep 10164811 = 15247217) B15247217
theorem B13553081 : Blo 2113435 13553081 := bstep (se 2 (by rfl) ⟨5082405, by rfl⟩ : syracuseStep 13553081 = 10164811) B10164811
theorem B9035387 : Blo 2113435 9035387 := bstep (se 1 (by rfl) ⟨6776540, by rfl⟩ : syracuseStep 9035387 = 13553081) B13553081
theorem B6023591 : Blo 2113435 6023591 := bstep (se 1 (by rfl) ⟨4517693, by rfl⟩ : syracuseStep 6023591 = 9035387) B9035387
theorem B4015727 : Blo 2113435 4015727 := bstep (se 1 (by rfl) ⟨3011795, by rfl⟩ : syracuseStep 4015727 = 6023591) B6023591
theorem B2677151 : Blo 2113435 2677151 := bstep (se 1 (by rfl) ⟨2007863, by rfl⟩ : syracuseStep 2677151 = 4015727) B4015727
theorem B7139069 : Blo 2113435 7139069 := bstep (se 3 (by rfl) ⟨1338575, by rfl⟩ : syracuseStep 7139069 = 2677151) B2677151
theorem B4759379 : Blo 2113435 4759379 := bstep (se 1 (by rfl) ⟨3569534, by rfl⟩ : syracuseStep 4759379 = 7139069) B7139069
theorem B3172919 : Blo 2113435 3172919 := bstep (se 1 (by rfl) ⟨2379689, by rfl⟩ : syracuseStep 3172919 = 4759379) B4759379
theorem B2115279 : Blo 2113435 2115279 := bstep (se 1 (by rfl) ⟨1586459, by rfl⟩ : syracuseStep 2115279 = 3172919) B3172919
theorem B3172925 : Blo 2113435 3172925 := bbase (se 3 (by rfl) ⟨594923, by rfl⟩ : syracuseStep 3172925 = 1189847) (by norm_num)
theorem B2115283 : Blo 2113435 2115283 := bstep (se 1 (by rfl) ⟨1586462, by rfl⟩ : syracuseStep 2115283 = 3172925) B3172925
theorem B4759397 : Blo 2113435 4759397 := bbase (se 4 (by rfl) ⟨446193, by rfl⟩ : syracuseStep 4759397 = 892387) (by norm_num)
theorem B3172931 : Blo 2113435 3172931 := bstep (se 1 (by rfl) ⟨2379698, by rfl⟩ : syracuseStep 3172931 = 4759397) B4759397
theorem B2115287 : Blo 2113435 2115287 := bstep (se 1 (by rfl) ⟨1586465, by rfl⟩ : syracuseStep 2115287 = 3172931) B3172931
theorem B5354333 : Blo 2113435 5354333 := bbase (se 3 (by rfl) ⟨1003937, by rfl⟩ : syracuseStep 5354333 = 2007875) (by norm_num)
theorem B3569555 : Blo 2113435 3569555 := bstep (se 1 (by rfl) ⟨2677166, by rfl⟩ : syracuseStep 3569555 = 5354333) B5354333
theorem B2379703 : Blo 2113435 2379703 := bstep (se 1 (by rfl) ⟨1784777, by rfl⟩ : syracuseStep 2379703 = 3569555) B3569555
theorem B3172937 : Blo 2113435 3172937 := bstep (se 2 (by rfl) ⟨1189851, by rfl⟩ : syracuseStep 3172937 = 2379703) B2379703
theorem B2115291 : Blo 2113435 2115291 := bstep (se 1 (by rfl) ⟨1586468, by rfl⟩ : syracuseStep 2115291 = 3172937) B3172937
theorem B4015757 : Blo 2113435 4015757 := bbase (se 3 (by rfl) ⟨752954, by rfl⟩ : syracuseStep 4015757 = 1505909) (by norm_num)
theorem B10708685 : Blo 2113435 10708685 := bstep (se 3 (by rfl) ⟨2007878, by rfl⟩ : syracuseStep 10708685 = 4015757) B4015757
theorem B7139123 : Blo 2113435 7139123 := bstep (se 1 (by rfl) ⟨5354342, by rfl⟩ : syracuseStep 7139123 = 10708685) B10708685
theorem B4759415 : Blo 2113435 4759415 := bstep (se 1 (by rfl) ⟨3569561, by rfl⟩ : syracuseStep 4759415 = 7139123) B7139123
theorem B3172943 : Blo 2113435 3172943 := bstep (se 1 (by rfl) ⟨2379707, by rfl⟩ : syracuseStep 3172943 = 4759415) B4759415
theorem B2115295 : Blo 2113435 2115295 := bstep (se 1 (by rfl) ⟨1586471, by rfl⟩ : syracuseStep 2115295 = 3172943) B3172943
theorem B3172949 : Blo 2113435 3172949 := bbase (se 8 (by rfl) ⟨18591, by rfl⟩ : syracuseStep 3172949 = 37183) (by norm_num)
theorem B2115299 : Blo 2113435 2115299 := bstep (se 1 (by rfl) ⟨1586474, by rfl⟩ : syracuseStep 2115299 = 3172949) B3172949
theorem B2412185 : Blo 2113435 2412185 := bbase (se 2 (by rfl) ⟨904569, by rfl⟩ : syracuseStep 2412185 = 1809139) (by norm_num)
theorem B25729973 : Blo 2113435 25729973 := bstep (se 5 (by rfl) ⟨1206092, by rfl⟩ : syracuseStep 25729973 = 2412185) B2412185
theorem B17153315 : Blo 2113435 17153315 := bstep (se 1 (by rfl) ⟨12864986, by rfl⟩ : syracuseStep 17153315 = 25729973) B25729973
theorem B11435543 : Blo 2113435 11435543 := bstep (se 1 (by rfl) ⟨8576657, by rfl⟩ : syracuseStep 11435543 = 17153315) B17153315
theorem B7623695 : Blo 2113435 7623695 := bstep (se 1 (by rfl) ⟨5717771, by rfl⟩ : syracuseStep 7623695 = 11435543) B11435543
theorem B5082463 : Blo 2113435 5082463 := bstep (se 1 (by rfl) ⟨3811847, by rfl⟩ : syracuseStep 5082463 = 7623695) B7623695
theorem B6776617 : Blo 2113435 6776617 := bstep (se 2 (by rfl) ⟨2541231, by rfl⟩ : syracuseStep 6776617 = 5082463) B5082463
theorem B9035489 : Blo 2113435 9035489 := bstep (se 2 (by rfl) ⟨3388308, by rfl⟩ : syracuseStep 9035489 = 6776617) B6776617
theorem B6023659 : Blo 2113435 6023659 := bstep (se 1 (by rfl) ⟨4517744, by rfl⟩ : syracuseStep 6023659 = 9035489) B9035489
theorem B8031545 : Blo 2113435 8031545 := bstep (se 2 (by rfl) ⟨3011829, by rfl⟩ : syracuseStep 8031545 = 6023659) B6023659
theorem B5354363 : Blo 2113435 5354363 := bstep (se 1 (by rfl) ⟨4015772, by rfl⟩ : syracuseStep 5354363 = 8031545) B8031545
theorem B3569575 : Blo 2113435 3569575 := bstep (se 1 (by rfl) ⟨2677181, by rfl⟩ : syracuseStep 3569575 = 5354363) B5354363
theorem B4759433 : Blo 2113435 4759433 := bstep (se 2 (by rfl) ⟨1784787, by rfl⟩ : syracuseStep 4759433 = 3569575) B3569575
theorem B3172955 : Blo 2113435 3172955 := bstep (se 1 (by rfl) ⟨2379716, by rfl⟩ : syracuseStep 3172955 = 4759433) B4759433
theorem B2115303 : Blo 2113435 2115303 := bstep (se 1 (by rfl) ⟨1586477, by rfl⟩ : syracuseStep 2115303 = 3172955) B3172955
theorem B2379721 : Blo 2113435 2379721 := bbase (se 2 (by rfl) ⟨892395, by rfl⟩ : syracuseStep 2379721 = 1784791) (by norm_num)
theorem B3172961 : Blo 2113435 3172961 := bstep (se 2 (by rfl) ⟨1189860, by rfl⟩ : syracuseStep 3172961 = 2379721) B2379721
theorem B2115307 : Blo 2113435 2115307 := bstep (se 1 (by rfl) ⟨1586480, by rfl⟩ : syracuseStep 2115307 = 3172961) B3172961
theorem B2541241 : Blo 2113435 2541241 := bbase (se 2 (by rfl) ⟨952965, by rfl⟩ : syracuseStep 2541241 = 1905931) (by norm_num)
theorem B3388321 : Blo 2113435 3388321 := bstep (se 2 (by rfl) ⟨1270620, by rfl⟩ : syracuseStep 3388321 = 2541241) B2541241
theorem B18071045 : Blo 2113435 18071045 := bstep (se 4 (by rfl) ⟨1694160, by rfl⟩ : syracuseStep 18071045 = 3388321) B3388321
theorem B12047363 : Blo 2113435 12047363 := bstep (se 1 (by rfl) ⟨9035522, by rfl⟩ : syracuseStep 12047363 = 18071045) B18071045
theorem B8031575 : Blo 2113435 8031575 := bstep (se 1 (by rfl) ⟨6023681, by rfl⟩ : syracuseStep 8031575 = 12047363) B12047363
theorem B5354383 : Blo 2113435 5354383 := bstep (se 1 (by rfl) ⟨4015787, by rfl⟩ : syracuseStep 5354383 = 8031575) B8031575
theorem B7139177 : Blo 2113435 7139177 := bstep (se 2 (by rfl) ⟨2677191, by rfl⟩ : syracuseStep 7139177 = 5354383) B5354383
theorem B4759451 : Blo 2113435 4759451 := bstep (se 1 (by rfl) ⟨3569588, by rfl⟩ : syracuseStep 4759451 = 7139177) B7139177
theorem B3172967 : Blo 2113435 3172967 := bstep (se 1 (by rfl) ⟨2379725, by rfl⟩ : syracuseStep 3172967 = 4759451) B4759451
theorem B2115311 : Blo 2113435 2115311 := bstep (se 1 (by rfl) ⟨1586483, by rfl⟩ : syracuseStep 2115311 = 3172967) B3172967
theorem B3172973 : Blo 2113435 3172973 := bbase (se 3 (by rfl) ⟨594932, by rfl⟩ : syracuseStep 3172973 = 1189865) (by norm_num)
theorem B2115315 : Blo 2113435 2115315 := bstep (se 1 (by rfl) ⟨1586486, by rfl⟩ : syracuseStep 2115315 = 3172973) B3172973
theorem B4759469 : Blo 2113435 4759469 := bbase (se 3 (by rfl) ⟨892400, by rfl⟩ : syracuseStep 4759469 = 1784801) (by norm_num)
theorem B3172979 : Blo 2113435 3172979 := bstep (se 1 (by rfl) ⟨2379734, by rfl⟩ : syracuseStep 3172979 = 4759469) B4759469
theorem B2115319 : Blo 2113435 2115319 := bstep (se 1 (by rfl) ⟨1586489, by rfl⟩ : syracuseStep 2115319 = 3172979) B3172979
theorem B6023717 : Blo 2113435 6023717 := bbase (se 4 (by rfl) ⟨564723, by rfl⟩ : syracuseStep 6023717 = 1129447) (by norm_num)
theorem B4015811 : Blo 2113435 4015811 := bstep (se 1 (by rfl) ⟨3011858, by rfl⟩ : syracuseStep 4015811 = 6023717) B6023717
theorem B2677207 : Blo 2113435 2677207 := bstep (se 1 (by rfl) ⟨2007905, by rfl⟩ : syracuseStep 2677207 = 4015811) B4015811
theorem B3569609 : Blo 2113435 3569609 := bstep (se 2 (by rfl) ⟨1338603, by rfl⟩ : syracuseStep 3569609 = 2677207) B2677207
theorem B2379739 : Blo 2113435 2379739 := bstep (se 1 (by rfl) ⟨1784804, by rfl⟩ : syracuseStep 2379739 = 3569609) B3569609
theorem B3172985 : Blo 2113435 3172985 := bstep (se 2 (by rfl) ⟨1189869, by rfl⟩ : syracuseStep 3172985 = 2379739) B2379739
theorem B2115323 : Blo 2113435 2115323 := bstep (se 1 (by rfl) ⟨1586492, by rfl⟩ : syracuseStep 2115323 = 3172985) B3172985
theorem B2320957 : Blo 2113435 2320957 := bbase (se 3 (by rfl) ⟨435179, by rfl⟩ : syracuseStep 2320957 = 870359) (by norm_num)
theorem B3094609 : Blo 2113435 3094609 := bstep (se 2 (by rfl) ⟨1160478, by rfl⟩ : syracuseStep 3094609 = 2320957) B2320957
theorem B4126145 : Blo 2113435 4126145 := bstep (se 2 (by rfl) ⟨1547304, by rfl⟩ : syracuseStep 4126145 = 3094609) B3094609
theorem B11003053 : Blo 2113435 11003053 := bstep (se 3 (by rfl) ⟨2063072, by rfl⟩ : syracuseStep 11003053 = 4126145) B4126145
theorem B14670737 : Blo 2113435 14670737 := bstep (se 2 (by rfl) ⟨5501526, by rfl⟩ : syracuseStep 14670737 = 11003053) B11003053
theorem B9780491 : Blo 2113435 9780491 := bstep (se 1 (by rfl) ⟨7335368, by rfl⟩ : syracuseStep 9780491 = 14670737) B14670737
theorem B6520327 : Blo 2113435 6520327 := bstep (se 1 (by rfl) ⟨4890245, by rfl⟩ : syracuseStep 6520327 = 9780491) B9780491
theorem B34775077 : Blo 2113435 34775077 := bstep (se 4 (by rfl) ⟨3260163, by rfl⟩ : syracuseStep 34775077 = 6520327) B6520327
theorem B46366769 : Blo 2113435 46366769 := bstep (se 2 (by rfl) ⟨17387538, by rfl⟩ : syracuseStep 46366769 = 34775077) B34775077
theorem B30911179 : Blo 2113435 30911179 := bstep (se 1 (by rfl) ⟨23183384, by rfl⟩ : syracuseStep 30911179 = 46366769) B46366769
theorem B41214905 : Blo 2113435 41214905 := bstep (se 2 (by rfl) ⟨15455589, by rfl⟩ : syracuseStep 41214905 = 30911179) B30911179
theorem B27476603 : Blo 2113435 27476603 := bstep (se 1 (by rfl) ⟨20607452, by rfl⟩ : syracuseStep 27476603 = 41214905) B41214905
theorem B18317735 : Blo 2113435 18317735 := bstep (se 1 (by rfl) ⟨13738301, by rfl⟩ : syracuseStep 18317735 = 27476603) B27476603
theorem B12211823 : Blo 2113435 12211823 := bstep (se 1 (by rfl) ⟨9158867, by rfl⟩ : syracuseStep 12211823 = 18317735) B18317735
theorem B8141215 : Blo 2113435 8141215 := bstep (se 1 (by rfl) ⟨6105911, by rfl⟩ : syracuseStep 8141215 = 12211823) B12211823
theorem B10854953 : Blo 2113435 10854953 := bstep (se 2 (by rfl) ⟨4070607, by rfl⟩ : syracuseStep 10854953 = 8141215) B8141215
theorem B7236635 : Blo 2113435 7236635 := bstep (se 1 (by rfl) ⟨5427476, by rfl⟩ : syracuseStep 7236635 = 10854953) B10854953
theorem B19297693 : Blo 2113435 19297693 := bstep (se 3 (by rfl) ⟨3618317, by rfl⟩ : syracuseStep 19297693 = 7236635) B7236635
theorem B25730257 : Blo 2113435 25730257 := bstep (se 2 (by rfl) ⟨9648846, by rfl⟩ : syracuseStep 25730257 = 19297693) B19297693
theorem B34307009 : Blo 2113435 34307009 := bstep (se 2 (by rfl) ⟨12865128, by rfl⟩ : syracuseStep 34307009 = 25730257) B25730257
theorem B22871339 : Blo 2113435 22871339 := bstep (se 1 (by rfl) ⟨17153504, by rfl⟩ : syracuseStep 22871339 = 34307009) B34307009
theorem B15247559 : Blo 2113435 15247559 := bstep (se 1 (by rfl) ⟨11435669, by rfl⟩ : syracuseStep 15247559 = 22871339) B22871339
theorem B40660157 : Blo 2113435 40660157 := bstep (se 3 (by rfl) ⟨7623779, by rfl⟩ : syracuseStep 40660157 = 15247559) B15247559
theorem B27106771 : Blo 2113435 27106771 := bstep (se 1 (by rfl) ⟨20330078, by rfl⟩ : syracuseStep 27106771 = 40660157) B40660157
theorem B36142361 : Blo 2113435 36142361 := bstep (se 2 (by rfl) ⟨13553385, by rfl⟩ : syracuseStep 36142361 = 27106771) B27106771
theorem B24094907 : Blo 2113435 24094907 := bstep (se 1 (by rfl) ⟨18071180, by rfl⟩ : syracuseStep 24094907 = 36142361) B36142361
theorem B16063271 : Blo 2113435 16063271 := bstep (se 1 (by rfl) ⟨12047453, by rfl⟩ : syracuseStep 16063271 = 24094907) B24094907
theorem B10708847 : Blo 2113435 10708847 := bstep (se 1 (by rfl) ⟨8031635, by rfl⟩ : syracuseStep 10708847 = 16063271) B16063271
theorem B7139231 : Blo 2113435 7139231 := bstep (se 1 (by rfl) ⟨5354423, by rfl⟩ : syracuseStep 7139231 = 10708847) B10708847
theorem B4759487 : Blo 2113435 4759487 := bstep (se 1 (by rfl) ⟨3569615, by rfl⟩ : syracuseStep 4759487 = 7139231) B7139231
theorem B3172991 : Blo 2113435 3172991 := bstep (se 1 (by rfl) ⟨2379743, by rfl⟩ : syracuseStep 3172991 = 4759487) B4759487
theorem B2115327 : Blo 2113435 2115327 := bstep (se 1 (by rfl) ⟨1586495, by rfl⟩ : syracuseStep 2115327 = 3172991) B3172991
theorem B3172997 : Blo 2113435 3172997 := bbase (se 4 (by rfl) ⟨297468, by rfl⟩ : syracuseStep 3172997 = 594937) (by norm_num)
theorem B2115331 : Blo 2113435 2115331 := bstep (se 1 (by rfl) ⟨1586498, by rfl⟩ : syracuseStep 2115331 = 3172997) B3172997
theorem B3569629 : Blo 2113435 3569629 := bbase (se 3 (by rfl) ⟨669305, by rfl⟩ : syracuseStep 3569629 = 1338611) (by norm_num)
theorem B4759505 : Blo 2113435 4759505 := bstep (se 2 (by rfl) ⟨1784814, by rfl⟩ : syracuseStep 4759505 = 3569629) B3569629
theorem B3173003 : Blo 2113435 3173003 := bstep (se 1 (by rfl) ⟨2379752, by rfl⟩ : syracuseStep 3173003 = 4759505) B4759505
theorem B2115335 : Blo 2113435 2115335 := bstep (se 1 (by rfl) ⟨1586501, by rfl⟩ : syracuseStep 2115335 = 3173003) B3173003
theorem B2379757 : Blo 2113435 2379757 := bbase (se 3 (by rfl) ⟨446204, by rfl⟩ : syracuseStep 2379757 = 892409) (by norm_num)
theorem B3173009 : Blo 2113435 3173009 := bstep (se 2 (by rfl) ⟨1189878, by rfl⟩ : syracuseStep 3173009 = 2379757) B2379757
theorem B2115339 : Blo 2113435 2115339 := bstep (se 1 (by rfl) ⟨1586504, by rfl⟩ : syracuseStep 2115339 = 3173009) B3173009
theorem B7139285 : Blo 2113435 7139285 := bbase (se 7 (by rfl) ⟨83663, by rfl⟩ : syracuseStep 7139285 = 167327) (by norm_num)
theorem B4759523 : Blo 2113435 4759523 := bstep (se 1 (by rfl) ⟨3569642, by rfl⟩ : syracuseStep 4759523 = 7139285) B7139285
theorem B3173015 : Blo 2113435 3173015 := bstep (se 1 (by rfl) ⟨2379761, by rfl⟩ : syracuseStep 3173015 = 4759523) B4759523
theorem B2115343 : Blo 2113435 2115343 := bstep (se 1 (by rfl) ⟨1586507, by rfl⟩ : syracuseStep 2115343 = 3173015) B3173015
theorem B3173021 : Blo 2113435 3173021 := bbase (se 3 (by rfl) ⟨594941, by rfl⟩ : syracuseStep 3173021 = 1189883) (by norm_num)
theorem B2115347 : Blo 2113435 2115347 := bstep (se 1 (by rfl) ⟨1586510, by rfl⟩ : syracuseStep 2115347 = 3173021) B3173021
theorem B4759541 : Blo 2113435 4759541 := bbase (se 5 (by rfl) ⟨223103, by rfl⟩ : syracuseStep 4759541 = 446207) (by norm_num)
theorem B3173027 : Blo 2113435 3173027 := bstep (se 1 (by rfl) ⟨2379770, by rfl⟩ : syracuseStep 3173027 = 4759541) B4759541
theorem B2115351 : Blo 2113435 2115351 := bstep (se 1 (by rfl) ⟨1586513, by rfl⟩ : syracuseStep 2115351 = 3173027) B3173027
theorem B7940213 : Blo 2113435 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B5293475 : Blo 2113435 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B3528983 : Blo 2113435 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B2352655 : Blo 2113435 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B12547493 : Blo 2113435 12547493 := bstep (se 4 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 12547493 = 2352655) B2352655
theorem B8364995 : Blo 2113435 8364995 := bstep (se 1 (by rfl) ⟨6273746, by rfl⟩ : syracuseStep 8364995 = 12547493) B12547493
theorem B5576663 : Blo 2113435 5576663 := bstep (se 1 (by rfl) ⟨4182497, by rfl⟩ : syracuseStep 5576663 = 8364995) B8364995
theorem B3717775 : Blo 2113435 3717775 := bstep (se 1 (by rfl) ⟨2788331, by rfl⟩ : syracuseStep 3717775 = 5576663) B5576663
theorem B4957033 : Blo 2113435 4957033 := bstep (se 2 (by rfl) ⟨1858887, by rfl⟩ : syracuseStep 4957033 = 3717775) B3717775
theorem B6609377 : Blo 2113435 6609377 := bstep (se 2 (by rfl) ⟨2478516, by rfl⟩ : syracuseStep 6609377 = 4957033) B4957033
theorem B4406251 : Blo 2113435 4406251 := bstep (se 1 (by rfl) ⟨3304688, by rfl⟩ : syracuseStep 4406251 = 6609377) B6609377
theorem B5875001 : Blo 2113435 5875001 := bstep (se 2 (by rfl) ⟨2203125, by rfl⟩ : syracuseStep 5875001 = 4406251) B4406251
theorem B3916667 : Blo 2113435 3916667 := bstep (se 1 (by rfl) ⟨2937500, by rfl⟩ : syracuseStep 3916667 = 5875001) B5875001
theorem B2611111 : Blo 2113435 2611111 := bstep (se 1 (by rfl) ⟨1958333, by rfl⟩ : syracuseStep 2611111 = 3916667) B3916667
theorem B3481481 : Blo 2113435 3481481 := bstep (se 2 (by rfl) ⟨1305555, by rfl⟩ : syracuseStep 3481481 = 2611111) B2611111
theorem B9283949 : Blo 2113435 9283949 := bstep (se 3 (by rfl) ⟨1740740, by rfl⟩ : syracuseStep 9283949 = 3481481) B3481481
theorem B6189299 : Blo 2113435 6189299 := bstep (se 1 (by rfl) ⟨4641974, by rfl⟩ : syracuseStep 6189299 = 9283949) B9283949
theorem B4126199 : Blo 2113435 4126199 := bstep (se 1 (by rfl) ⟨3094649, by rfl⟩ : syracuseStep 4126199 = 6189299) B6189299
theorem B44012789 : Blo 2113435 44012789 := bstep (se 5 (by rfl) ⟨2063099, by rfl⟩ : syracuseStep 44012789 = 4126199) B4126199
theorem B29341859 : Blo 2113435 29341859 := bstep (se 1 (by rfl) ⟨22006394, by rfl⟩ : syracuseStep 29341859 = 44012789) B44012789
theorem B78244957 : Blo 2113435 78244957 := bstep (se 3 (by rfl) ⟨14670929, by rfl⟩ : syracuseStep 78244957 = 29341859) B29341859
theorem B417306437 : Blo 2113435 417306437 := bstep (se 4 (by rfl) ⟨39122478, by rfl⟩ : syracuseStep 417306437 = 78244957) B78244957
theorem B278204291 : Blo 2113435 278204291 := bstep (se 1 (by rfl) ⟨208653218, by rfl⟩ : syracuseStep 278204291 = 417306437) B417306437
theorem B185469527 : Blo 2113435 185469527 := bstep (se 1 (by rfl) ⟨139102145, by rfl⟩ : syracuseStep 185469527 = 278204291) B278204291
theorem B123646351 : Blo 2113435 123646351 := bstep (se 1 (by rfl) ⟨92734763, by rfl⟩ : syracuseStep 123646351 = 185469527) B185469527
theorem B164861801 : Blo 2113435 164861801 := bstep (se 2 (by rfl) ⟨61823175, by rfl⟩ : syracuseStep 164861801 = 123646351) B123646351
theorem B109907867 : Blo 2113435 109907867 := bstep (se 1 (by rfl) ⟨82430900, by rfl⟩ : syracuseStep 109907867 = 164861801) B164861801
theorem B73271911 : Blo 2113435 73271911 := bstep (se 1 (by rfl) ⟨54953933, by rfl⟩ : syracuseStep 73271911 = 109907867) B109907867
theorem B97695881 : Blo 2113435 97695881 := bstep (se 2 (by rfl) ⟨36635955, by rfl⟩ : syracuseStep 97695881 = 73271911) B73271911
theorem B65130587 : Blo 2113435 65130587 := bstep (se 1 (by rfl) ⟨48847940, by rfl⟩ : syracuseStep 65130587 = 97695881) B97695881
theorem B43420391 : Blo 2113435 43420391 := bstep (se 1 (by rfl) ⟨32565293, by rfl⟩ : syracuseStep 43420391 = 65130587) B65130587
theorem B28946927 : Blo 2113435 28946927 := bstep (se 1 (by rfl) ⟨21710195, by rfl⟩ : syracuseStep 28946927 = 43420391) B43420391
theorem B77191805 : Blo 2113435 77191805 := bstep (se 3 (by rfl) ⟨14473463, by rfl⟩ : syracuseStep 77191805 = 28946927) B28946927
theorem B205844813 : Blo 2113435 205844813 := bstep (se 3 (by rfl) ⟨38595902, by rfl⟩ : syracuseStep 205844813 = 77191805) B77191805
theorem B137229875 : Blo 2113435 137229875 := bstep (se 1 (by rfl) ⟨102922406, by rfl⟩ : syracuseStep 137229875 = 205844813) B205844813
theorem B91486583 : Blo 2113435 91486583 := bstep (se 1 (by rfl) ⟨68614937, by rfl⟩ : syracuseStep 91486583 = 137229875) B137229875
theorem B60991055 : Blo 2113435 60991055 := bstep (se 1 (by rfl) ⟨45743291, by rfl⟩ : syracuseStep 60991055 = 91486583) B91486583
theorem B40660703 : Blo 2113435 40660703 := bstep (se 1 (by rfl) ⟨30495527, by rfl⟩ : syracuseStep 40660703 = 60991055) B60991055
theorem B27107135 : Blo 2113435 27107135 := bstep (se 1 (by rfl) ⟨20330351, by rfl⟩ : syracuseStep 27107135 = 40660703) B40660703
theorem B18071423 : Blo 2113435 18071423 := bstep (se 1 (by rfl) ⟨13553567, by rfl⟩ : syracuseStep 18071423 = 27107135) B27107135
theorem B12047615 : Blo 2113435 12047615 := bstep (se 1 (by rfl) ⟨9035711, by rfl⟩ : syracuseStep 12047615 = 18071423) B18071423
theorem B8031743 : Blo 2113435 8031743 := bstep (se 1 (by rfl) ⟨6023807, by rfl⟩ : syracuseStep 8031743 = 12047615) B12047615
theorem B5354495 : Blo 2113435 5354495 := bstep (se 1 (by rfl) ⟨4015871, by rfl⟩ : syracuseStep 5354495 = 8031743) B8031743
theorem B3569663 : Blo 2113435 3569663 := bstep (se 1 (by rfl) ⟨2677247, by rfl⟩ : syracuseStep 3569663 = 5354495) B5354495
theorem B2379775 : Blo 2113435 2379775 := bstep (se 1 (by rfl) ⟨1784831, by rfl⟩ : syracuseStep 2379775 = 3569663) B3569663
theorem B3173033 : Blo 2113435 3173033 := bstep (se 2 (by rfl) ⟨1189887, by rfl⟩ : syracuseStep 3173033 = 2379775) B2379775
theorem B2115355 : Blo 2113435 2115355 := bstep (se 1 (by rfl) ⟨1586516, by rfl⟩ : syracuseStep 2115355 = 3173033) B3173033
theorem B3011909 : Blo 2113435 3011909 := bbase (se 4 (by rfl) ⟨282366, by rfl⟩ : syracuseStep 3011909 = 564733) (by norm_num)
theorem B8031757 : Blo 2113435 8031757 := bstep (se 3 (by rfl) ⟨1505954, by rfl⟩ : syracuseStep 8031757 = 3011909) B3011909
theorem B10709009 : Blo 2113435 10709009 := bstep (se 2 (by rfl) ⟨4015878, by rfl⟩ : syracuseStep 10709009 = 8031757) B8031757
theorem B7139339 : Blo 2113435 7139339 := bstep (se 1 (by rfl) ⟨5354504, by rfl⟩ : syracuseStep 7139339 = 10709009) B10709009
theorem B4759559 : Blo 2113435 4759559 := bstep (se 1 (by rfl) ⟨3569669, by rfl⟩ : syracuseStep 4759559 = 7139339) B7139339
theorem B3173039 : Blo 2113435 3173039 := bstep (se 1 (by rfl) ⟨2379779, by rfl⟩ : syracuseStep 3173039 = 4759559) B4759559
theorem B2115359 : Blo 2113435 2115359 := bstep (se 1 (by rfl) ⟨1586519, by rfl⟩ : syracuseStep 2115359 = 3173039) B3173039
theorem B3173045 : Blo 2113435 3173045 := bbase (se 5 (by rfl) ⟨148736, by rfl⟩ : syracuseStep 3173045 = 297473) (by norm_num)
theorem B2115363 : Blo 2113435 2115363 := bstep (se 1 (by rfl) ⟨1586522, by rfl⟩ : syracuseStep 2115363 = 3173045) B3173045
theorem B5354525 : Blo 2113435 5354525 := bbase (se 3 (by rfl) ⟨1003973, by rfl⟩ : syracuseStep 5354525 = 2007947) (by norm_num)
theorem B3569683 : Blo 2113435 3569683 := bstep (se 1 (by rfl) ⟨2677262, by rfl⟩ : syracuseStep 3569683 = 5354525) B5354525
theorem B4759577 : Blo 2113435 4759577 := bstep (se 2 (by rfl) ⟨1784841, by rfl⟩ : syracuseStep 4759577 = 3569683) B3569683
theorem B3173051 : Blo 2113435 3173051 := bstep (se 1 (by rfl) ⟨2379788, by rfl⟩ : syracuseStep 3173051 = 4759577) B4759577
theorem B2115367 : Blo 2113435 2115367 := bstep (se 1 (by rfl) ⟨1586525, by rfl⟩ : syracuseStep 2115367 = 3173051) B3173051
theorem B2379793 : Blo 2113435 2379793 := bbase (se 2 (by rfl) ⟨892422, by rfl⟩ : syracuseStep 2379793 = 1784845) (by norm_num)
theorem B3173057 : Blo 2113435 3173057 := bstep (se 2 (by rfl) ⟨1189896, by rfl⟩ : syracuseStep 3173057 = 2379793) B2379793
theorem B2115371 : Blo 2113435 2115371 := bstep (se 1 (by rfl) ⟨1586528, by rfl⟩ : syracuseStep 2115371 = 3173057) B3173057
theorem B4015909 : Blo 2113435 4015909 := bbase (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) (by norm_num)
theorem B5354545 : Blo 2113435 5354545 := bstep (se 2 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 5354545 = 4015909) B4015909
theorem B7139393 : Blo 2113435 7139393 := bstep (se 2 (by rfl) ⟨2677272, by rfl⟩ : syracuseStep 7139393 = 5354545) B5354545
theorem B4759595 : Blo 2113435 4759595 := bstep (se 1 (by rfl) ⟨3569696, by rfl⟩ : syracuseStep 4759595 = 7139393) B7139393
theorem B3173063 : Blo 2113435 3173063 := bstep (se 1 (by rfl) ⟨2379797, by rfl⟩ : syracuseStep 3173063 = 4759595) B4759595
theorem B2115375 : Blo 2113435 2115375 := bstep (se 1 (by rfl) ⟨1586531, by rfl⟩ : syracuseStep 2115375 = 3173063) B3173063
theorem B3173069 : Blo 2113435 3173069 := bbase (se 3 (by rfl) ⟨594950, by rfl⟩ : syracuseStep 3173069 = 1189901) (by norm_num)
theorem B2115379 : Blo 2113435 2115379 := bstep (se 1 (by rfl) ⟨1586534, by rfl⟩ : syracuseStep 2115379 = 3173069) B3173069
theorem B4759613 : Blo 2113435 4759613 := bbase (se 3 (by rfl) ⟨892427, by rfl⟩ : syracuseStep 4759613 = 1784855) (by norm_num)
theorem B3173075 : Blo 2113435 3173075 := bstep (se 1 (by rfl) ⟨2379806, by rfl⟩ : syracuseStep 3173075 = 4759613) B4759613
theorem B2115383 : Blo 2113435 2115383 := bstep (se 1 (by rfl) ⟨1586537, by rfl⟩ : syracuseStep 2115383 = 3173075) B3173075
theorem B3569717 : Blo 2113435 3569717 := bbase (se 5 (by rfl) ⟨167330, by rfl⟩ : syracuseStep 3569717 = 334661) (by norm_num)
theorem B2379811 : Blo 2113435 2379811 := bstep (se 1 (by rfl) ⟨1784858, by rfl⟩ : syracuseStep 2379811 = 3569717) B3569717
theorem B3173081 : Blo 2113435 3173081 := bstep (se 2 (by rfl) ⟨1189905, by rfl⟩ : syracuseStep 3173081 = 2379811) B2379811
theorem B2115387 : Blo 2113435 2115387 := bstep (se 1 (by rfl) ⟨1586540, by rfl⟩ : syracuseStep 2115387 = 3173081) B3173081
theorem B6023909 : Blo 2113435 6023909 := bbase (se 4 (by rfl) ⟨564741, by rfl⟩ : syracuseStep 6023909 = 1129483) (by norm_num)
theorem B16063757 : Blo 2113435 16063757 := bstep (se 3 (by rfl) ⟨3011954, by rfl⟩ : syracuseStep 16063757 = 6023909) B6023909
theorem B10709171 : Blo 2113435 10709171 := bstep (se 1 (by rfl) ⟨8031878, by rfl⟩ : syracuseStep 10709171 = 16063757) B16063757
theorem B7139447 : Blo 2113435 7139447 := bstep (se 1 (by rfl) ⟨5354585, by rfl⟩ : syracuseStep 7139447 = 10709171) B10709171
theorem B4759631 : Blo 2113435 4759631 := bstep (se 1 (by rfl) ⟨3569723, by rfl⟩ : syracuseStep 4759631 = 7139447) B7139447
theorem B3173087 : Blo 2113435 3173087 := bstep (se 1 (by rfl) ⟨2379815, by rfl⟩ : syracuseStep 3173087 = 4759631) B4759631
theorem B2115391 : Blo 2113435 2115391 := bstep (se 1 (by rfl) ⟨1586543, by rfl⟩ : syracuseStep 2115391 = 3173087) B3173087
theorem B3173093 : Blo 2113435 3173093 := bbase (se 4 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 3173093 = 594955) (by norm_num)
theorem B2115395 : Blo 2113435 2115395 := bstep (se 1 (by rfl) ⟨1586546, by rfl⟩ : syracuseStep 2115395 = 3173093) B3173093
theorem B4070749 : Blo 2113435 4070749 := bbase (se 3 (by rfl) ⟨763265, by rfl⟩ : syracuseStep 4070749 = 1526531) (by norm_num)
theorem B5427665 : Blo 2113435 5427665 := bstep (se 2 (by rfl) ⟨2035374, by rfl⟩ : syracuseStep 5427665 = 4070749) B4070749
theorem B3618443 : Blo 2113435 3618443 := bstep (se 1 (by rfl) ⟨2713832, by rfl⟩ : syracuseStep 3618443 = 5427665) B5427665
theorem B9649181 : Blo 2113435 9649181 := bstep (se 3 (by rfl) ⟨1809221, by rfl⟩ : syracuseStep 9649181 = 3618443) B3618443
theorem B6432787 : Blo 2113435 6432787 := bstep (se 1 (by rfl) ⟨4824590, by rfl⟩ : syracuseStep 6432787 = 9649181) B9649181
theorem B8577049 : Blo 2113435 8577049 := bstep (se 2 (by rfl) ⟨3216393, by rfl⟩ : syracuseStep 8577049 = 6432787) B6432787
theorem B11436065 : Blo 2113435 11436065 := bstep (se 2 (by rfl) ⟨4288524, by rfl⟩ : syracuseStep 11436065 = 8577049) B8577049
theorem B7624043 : Blo 2113435 7624043 := bstep (se 1 (by rfl) ⟨5718032, by rfl⟩ : syracuseStep 7624043 = 11436065) B11436065
theorem B5082695 : Blo 2113435 5082695 := bstep (se 1 (by rfl) ⟨3812021, by rfl⟩ : syracuseStep 5082695 = 7624043) B7624043
theorem B3388463 : Blo 2113435 3388463 := bstep (se 1 (by rfl) ⟨2541347, by rfl⟩ : syracuseStep 3388463 = 5082695) B5082695
theorem B2258975 : Blo 2113435 2258975 := bstep (se 1 (by rfl) ⟨1694231, by rfl⟩ : syracuseStep 2258975 = 3388463) B3388463
theorem B6023933 : Blo 2113435 6023933 := bstep (se 3 (by rfl) ⟨1129487, by rfl⟩ : syracuseStep 6023933 = 2258975) B2258975
theorem B4015955 : Blo 2113435 4015955 := bstep (se 1 (by rfl) ⟨3011966, by rfl⟩ : syracuseStep 4015955 = 6023933) B6023933
theorem B2677303 : Blo 2113435 2677303 := bstep (se 1 (by rfl) ⟨2007977, by rfl⟩ : syracuseStep 2677303 = 4015955) B4015955
theorem B3569737 : Blo 2113435 3569737 := bstep (se 2 (by rfl) ⟨1338651, by rfl⟩ : syracuseStep 3569737 = 2677303) B2677303
theorem B4759649 : Blo 2113435 4759649 := bstep (se 2 (by rfl) ⟨1784868, by rfl⟩ : syracuseStep 4759649 = 3569737) B3569737
theorem B3173099 : Blo 2113435 3173099 := bstep (se 1 (by rfl) ⟨2379824, by rfl⟩ : syracuseStep 3173099 = 4759649) B4759649
theorem B2115399 : Blo 2113435 2115399 := bstep (se 1 (by rfl) ⟨1586549, by rfl⟩ : syracuseStep 2115399 = 3173099) B3173099
theorem B2379829 : Blo 2113435 2379829 := bbase (se 5 (by rfl) ⟨111554, by rfl⟩ : syracuseStep 2379829 = 223109) (by norm_num)
theorem B3173105 : Blo 2113435 3173105 := bstep (se 2 (by rfl) ⟨1189914, by rfl⟩ : syracuseStep 3173105 = 2379829) B2379829
theorem B2115403 : Blo 2113435 2115403 := bstep (se 1 (by rfl) ⟨1586552, by rfl⟩ : syracuseStep 2115403 = 3173105) B3173105
theorem B2677313 : Blo 2113435 2677313 := bbase (se 2 (by rfl) ⟨1003992, by rfl⟩ : syracuseStep 2677313 = 2007985) (by norm_num)
theorem B7139501 : Blo 2113435 7139501 := bstep (se 3 (by rfl) ⟨1338656, by rfl⟩ : syracuseStep 7139501 = 2677313) B2677313
theorem B4759667 : Blo 2113435 4759667 := bstep (se 1 (by rfl) ⟨3569750, by rfl⟩ : syracuseStep 4759667 = 7139501) B7139501
theorem B3173111 : Blo 2113435 3173111 := bstep (se 1 (by rfl) ⟨2379833, by rfl⟩ : syracuseStep 3173111 = 4759667) B4759667
theorem B2115407 : Blo 2113435 2115407 := bstep (se 1 (by rfl) ⟨1586555, by rfl⟩ : syracuseStep 2115407 = 3173111) B3173111
theorem B3173117 : Blo 2113435 3173117 := bbase (se 3 (by rfl) ⟨594959, by rfl⟩ : syracuseStep 3173117 = 1189919) (by norm_num)
theorem B2115411 : Blo 2113435 2115411 := bstep (se 1 (by rfl) ⟨1586558, by rfl⟩ : syracuseStep 2115411 = 3173117) B3173117
theorem B4759685 : Blo 2113435 4759685 := bbase (se 4 (by rfl) ⟨446220, by rfl⟩ : syracuseStep 4759685 = 892441) (by norm_num)
theorem B3173123 : Blo 2113435 3173123 := bstep (se 1 (by rfl) ⟨2379842, by rfl⟩ : syracuseStep 3173123 = 4759685) B4759685
theorem B2115415 : Blo 2113435 2115415 := bstep (se 1 (by rfl) ⟨1586561, by rfl⟩ : syracuseStep 2115415 = 3173123) B3173123
theorem B4288565 : Blo 2113435 4288565 := bbase (se 5 (by rfl) ⟨201026, by rfl⟩ : syracuseStep 4288565 = 402053) (by norm_num)
theorem B11436173 : Blo 2113435 11436173 := bstep (se 3 (by rfl) ⟨2144282, by rfl⟩ : syracuseStep 11436173 = 4288565) B4288565
theorem B7624115 : Blo 2113435 7624115 := bstep (se 1 (by rfl) ⟨5718086, by rfl⟩ : syracuseStep 7624115 = 11436173) B11436173
theorem B5082743 : Blo 2113435 5082743 := bstep (se 1 (by rfl) ⟨3812057, by rfl⟩ : syracuseStep 5082743 = 7624115) B7624115
theorem B3388495 : Blo 2113435 3388495 := bstep (se 1 (by rfl) ⟨2541371, by rfl⟩ : syracuseStep 3388495 = 5082743) B5082743
theorem B4517993 : Blo 2113435 4517993 := bstep (se 2 (by rfl) ⟨1694247, by rfl⟩ : syracuseStep 4517993 = 3388495) B3388495
theorem B3011995 : Blo 2113435 3011995 := bstep (se 1 (by rfl) ⟨2258996, by rfl⟩ : syracuseStep 3011995 = 4517993) B4517993
theorem B4015993 : Blo 2113435 4015993 := bstep (se 2 (by rfl) ⟨1505997, by rfl⟩ : syracuseStep 4015993 = 3011995) B3011995
theorem B5354657 : Blo 2113435 5354657 := bstep (se 2 (by rfl) ⟨2007996, by rfl⟩ : syracuseStep 5354657 = 4015993) B4015993
theorem B3569771 : Blo 2113435 3569771 := bstep (se 1 (by rfl) ⟨2677328, by rfl⟩ : syracuseStep 3569771 = 5354657) B5354657
theorem B2379847 : Blo 2113435 2379847 := bstep (se 1 (by rfl) ⟨1784885, by rfl⟩ : syracuseStep 2379847 = 3569771) B3569771
theorem B3173129 : Blo 2113435 3173129 := bstep (se 2 (by rfl) ⟨1189923, by rfl⟩ : syracuseStep 3173129 = 2379847) B2379847
theorem B2115419 : Blo 2113435 2115419 := bstep (se 1 (by rfl) ⟨1586564, by rfl⟩ : syracuseStep 2115419 = 3173129) B3173129
theorem B10709333 : Blo 2113435 10709333 := bbase (se 10 (by rfl) ⟨15687, by rfl⟩ : syracuseStep 10709333 = 31375) (by norm_num)
theorem B7139555 : Blo 2113435 7139555 := bstep (se 1 (by rfl) ⟨5354666, by rfl⟩ : syracuseStep 7139555 = 10709333) B10709333
theorem B4759703 : Blo 2113435 4759703 := bstep (se 1 (by rfl) ⟨3569777, by rfl⟩ : syracuseStep 4759703 = 7139555) B7139555
theorem B3173135 : Blo 2113435 3173135 := bstep (se 1 (by rfl) ⟨2379851, by rfl⟩ : syracuseStep 3173135 = 4759703) B4759703
theorem B2115423 : Blo 2113435 2115423 := bstep (se 1 (by rfl) ⟨1586567, by rfl⟩ : syracuseStep 2115423 = 3173135) B3173135
theorem B3173141 : Blo 2113435 3173141 := bbase (se 6 (by rfl) ⟨74370, by rfl⟩ : syracuseStep 3173141 = 148741) (by norm_num)
theorem B2115427 : Blo 2113435 2115427 := bstep (se 1 (by rfl) ⟨1586570, by rfl⟩ : syracuseStep 2115427 = 3173141) B3173141
theorem B19298645 : Blo 2113435 19298645 := bbase (se 10 (by rfl) ⟨28269, by rfl⟩ : syracuseStep 19298645 = 56539) (by norm_num)
theorem B12865763 : Blo 2113435 12865763 := bstep (se 1 (by rfl) ⟨9649322, by rfl⟩ : syracuseStep 12865763 = 19298645) B19298645
theorem B8577175 : Blo 2113435 8577175 := bstep (se 1 (by rfl) ⟨6432881, by rfl⟩ : syracuseStep 8577175 = 12865763) B12865763
theorem B11436233 : Blo 2113435 11436233 := bstep (se 2 (by rfl) ⟨4288587, by rfl⟩ : syracuseStep 11436233 = 8577175) B8577175
theorem B30496621 : Blo 2113435 30496621 := bstep (se 3 (by rfl) ⟨5718116, by rfl⟩ : syracuseStep 30496621 = 11436233) B11436233
theorem B40662161 : Blo 2113435 40662161 := bstep (se 2 (by rfl) ⟨15248310, by rfl⟩ : syracuseStep 40662161 = 30496621) B30496621
theorem B27108107 : Blo 2113435 27108107 := bstep (se 1 (by rfl) ⟨20331080, by rfl⟩ : syracuseStep 27108107 = 40662161) B40662161
theorem B18072071 : Blo 2113435 18072071 := bstep (se 1 (by rfl) ⟨13554053, by rfl⟩ : syracuseStep 18072071 = 27108107) B27108107
theorem B12048047 : Blo 2113435 12048047 := bstep (se 1 (by rfl) ⟨9036035, by rfl⟩ : syracuseStep 12048047 = 18072071) B18072071
theorem B8032031 : Blo 2113435 8032031 := bstep (se 1 (by rfl) ⟨6024023, by rfl⟩ : syracuseStep 8032031 = 12048047) B12048047
theorem B5354687 : Blo 2113435 5354687 := bstep (se 1 (by rfl) ⟨4016015, by rfl⟩ : syracuseStep 5354687 = 8032031) B8032031
theorem B3569791 : Blo 2113435 3569791 := bstep (se 1 (by rfl) ⟨2677343, by rfl⟩ : syracuseStep 3569791 = 5354687) B5354687
theorem B4759721 : Blo 2113435 4759721 := bstep (se 2 (by rfl) ⟨1784895, by rfl⟩ : syracuseStep 4759721 = 3569791) B3569791
theorem B3173147 : Blo 2113435 3173147 := bstep (se 1 (by rfl) ⟨2379860, by rfl⟩ : syracuseStep 3173147 = 4759721) B4759721
theorem B2115431 : Blo 2113435 2115431 := bstep (se 1 (by rfl) ⟨1586573, by rfl⟩ : syracuseStep 2115431 = 3173147) B3173147
theorem B2379865 : Blo 2113435 2379865 := bbase (se 2 (by rfl) ⟨892449, by rfl⟩ : syracuseStep 2379865 = 1784899) (by norm_num)
theorem B3173153 : Blo 2113435 3173153 := bstep (se 2 (by rfl) ⟨1189932, by rfl⟩ : syracuseStep 3173153 = 2379865) B2379865
theorem B2115435 : Blo 2113435 2115435 := bstep (se 1 (by rfl) ⟨1586576, by rfl⟩ : syracuseStep 2115435 = 3173153) B3173153
theorem C0 (j : ℕ) (h1 : 528358 ≤ j) (h2 : j ≤ 528858) : Blo 2113435 (4 * j + 3) := by
  interval_cases j
  · exact B2113435
  · exact B2113439
  · exact B2113443
  · exact B2113447
  · exact B2113451
  · exact B2113455
  · exact B2113459
  · exact B2113463
  · exact B2113467
  · exact B2113471
  · exact B2113475
  · exact B2113479
  · exact B2113483
  · exact B2113487
  · exact B2113491
  · exact B2113495
  · exact B2113499
  · exact B2113503
  · exact B2113507
  · exact B2113511
  · exact B2113515
  · exact B2113519
  · exact B2113523
  · exact B2113527
  · exact B2113531
  · exact B2113535
  · exact B2113539
  · exact B2113543
  · exact B2113547
  · exact B2113551
  · exact B2113555
  · exact B2113559
  · exact B2113563
  · exact B2113567
  · exact B2113571
  · exact B2113575
  · exact B2113579
  · exact B2113583
  · exact B2113587
  · exact B2113591
  · exact B2113595
  · exact B2113599
  · exact B2113603
  · exact B2113607
  · exact B2113611
  · exact B2113615
  · exact B2113619
  · exact B2113623
  · exact B2113627
  · exact B2113631
  · exact B2113635
  · exact B2113639
  · exact B2113643
  · exact B2113647
  · exact B2113651
  · exact B2113655
  · exact B2113659
  · exact B2113663
  · exact B2113667
  · exact B2113671
  · exact B2113675
  · exact B2113679
  · exact B2113683
  · exact B2113687
  · exact B2113691
  · exact B2113695
  · exact B2113699
  · exact B2113703
  · exact B2113707
  · exact B2113711
  · exact B2113715
  · exact B2113719
  · exact B2113723
  · exact B2113727
  · exact B2113731
  · exact B2113735
  · exact B2113739
  · exact B2113743
  · exact B2113747
  · exact B2113751
  · exact B2113755
  · exact B2113759
  · exact B2113763
  · exact B2113767
  · exact B2113771
  · exact B2113775
  · exact B2113779
  · exact B2113783
  · exact B2113787
  · exact B2113791
  · exact B2113795
  · exact B2113799
  · exact B2113803
  · exact B2113807
  · exact B2113811
  · exact B2113815
  · exact B2113819
  · exact B2113823
  · exact B2113827
  · exact B2113831
  · exact B2113835
  · exact B2113839
  · exact B2113843
  · exact B2113847
  · exact B2113851
  · exact B2113855
  · exact B2113859
  · exact B2113863
  · exact B2113867
  · exact B2113871
  · exact B2113875
  · exact B2113879
  · exact B2113883
  · exact B2113887
  · exact B2113891
  · exact B2113895
  · exact B2113899
  · exact B2113903
  · exact B2113907
  · exact B2113911
  · exact B2113915
  · exact B2113919
  · exact B2113923
  · exact B2113927
  · exact B2113931
  · exact B2113935
  · exact B2113939
  · exact B2113943
  · exact B2113947
  · exact B2113951
  · exact B2113955
  · exact B2113959
  · exact B2113963
  · exact B2113967
  · exact B2113971
  · exact B2113975
  · exact B2113979
  · exact B2113983
  · exact B2113987
  · exact B2113991
  · exact B2113995
  · exact B2113999
  · exact B2114003
  · exact B2114007
  · exact B2114011
  · exact B2114015
  · exact B2114019
  · exact B2114023
  · exact B2114027
  · exact B2114031
  · exact B2114035
  · exact B2114039
  · exact B2114043
  · exact B2114047
  · exact B2114051
  · exact B2114055
  · exact B2114059
  · exact B2114063
  · exact B2114067
  · exact B2114071
  · exact B2114075
  · exact B2114079
  · exact B2114083
  · exact B2114087
  · exact B2114091
  · exact B2114095
  · exact B2114099
  · exact B2114103
  · exact B2114107
  · exact B2114111
  · exact B2114115
  · exact B2114119
  · exact B2114123
  · exact B2114127
  · exact B2114131
  · exact B2114135
  · exact B2114139
  · exact B2114143
  · exact B2114147
  · exact B2114151
  · exact B2114155
  · exact B2114159
  · exact B2114163
  · exact B2114167
  · exact B2114171
  · exact B2114175
  · exact B2114179
  · exact B2114183
  · exact B2114187
  · exact B2114191
  · exact B2114195
  · exact B2114199
  · exact B2114203
  · exact B2114207
  · exact B2114211
  · exact B2114215
  · exact B2114219
  · exact B2114223
  · exact B2114227
  · exact B2114231
  · exact B2114235
  · exact B2114239
  · exact B2114243
  · exact B2114247
  · exact B2114251
  · exact B2114255
  · exact B2114259
  · exact B2114263
  · exact B2114267
  · exact B2114271
  · exact B2114275
  · exact B2114279
  · exact B2114283
  · exact B2114287
  · exact B2114291
  · exact B2114295
  · exact B2114299
  · exact B2114303
  · exact B2114307
  · exact B2114311
  · exact B2114315
  · exact B2114319
  · exact B2114323
  · exact B2114327
  · exact B2114331
  · exact B2114335
  · exact B2114339
  · exact B2114343
  · exact B2114347
  · exact B2114351
  · exact B2114355
  · exact B2114359
  · exact B2114363
  · exact B2114367
  · exact B2114371
  · exact B2114375
  · exact B2114379
  · exact B2114383
  · exact B2114387
  · exact B2114391
  · exact B2114395
  · exact B2114399
  · exact B2114403
  · exact B2114407
  · exact B2114411
  · exact B2114415
  · exact B2114419
  · exact B2114423
  · exact B2114427
  · exact B2114431
  · exact B2114435
  · exact B2114439
  · exact B2114443
  · exact B2114447
  · exact B2114451
  · exact B2114455
  · exact B2114459
  · exact B2114463
  · exact B2114467
  · exact B2114471
  · exact B2114475
  · exact B2114479
  · exact B2114483
  · exact B2114487
  · exact B2114491
  · exact B2114495
  · exact B2114499
  · exact B2114503
  · exact B2114507
  · exact B2114511
  · exact B2114515
  · exact B2114519
  · exact B2114523
  · exact B2114527
  · exact B2114531
  · exact B2114535
  · exact B2114539
  · exact B2114543
  · exact B2114547
  · exact B2114551
  · exact B2114555
  · exact B2114559
  · exact B2114563
  · exact B2114567
  · exact B2114571
  · exact B2114575
  · exact B2114579
  · exact B2114583
  · exact B2114587
  · exact B2114591
  · exact B2114595
  · exact B2114599
  · exact B2114603
  · exact B2114607
  · exact B2114611
  · exact B2114615
  · exact B2114619
  · exact B2114623
  · exact B2114627
  · exact B2114631
  · exact B2114635
  · exact B2114639
  · exact B2114643
  · exact B2114647
  · exact B2114651
  · exact B2114655
  · exact B2114659
  · exact B2114663
  · exact B2114667
  · exact B2114671
  · exact B2114675
  · exact B2114679
  · exact B2114683
  · exact B2114687
  · exact B2114691
  · exact B2114695
  · exact B2114699
  · exact B2114703
  · exact B2114707
  · exact B2114711
  · exact B2114715
  · exact B2114719
  · exact B2114723
  · exact B2114727
  · exact B2114731
  · exact B2114735
  · exact B2114739
  · exact B2114743
  · exact B2114747
  · exact B2114751
  · exact B2114755
  · exact B2114759
  · exact B2114763
  · exact B2114767
  · exact B2114771
  · exact B2114775
  · exact B2114779
  · exact B2114783
  · exact B2114787
  · exact B2114791
  · exact B2114795
  · exact B2114799
  · exact B2114803
  · exact B2114807
  · exact B2114811
  · exact B2114815
  · exact B2114819
  · exact B2114823
  · exact B2114827
  · exact B2114831
  · exact B2114835
  · exact B2114839
  · exact B2114843
  · exact B2114847
  · exact B2114851
  · exact B2114855
  · exact B2114859
  · exact B2114863
  · exact B2114867
  · exact B2114871
  · exact B2114875
  · exact B2114879
  · exact B2114883
  · exact B2114887
  · exact B2114891
  · exact B2114895
  · exact B2114899
  · exact B2114903
  · exact B2114907
  · exact B2114911
  · exact B2114915
  · exact B2114919
  · exact B2114923
  · exact B2114927
  · exact B2114931
  · exact B2114935
  · exact B2114939
  · exact B2114943
  · exact B2114947
  · exact B2114951
  · exact B2114955
  · exact B2114959
  · exact B2114963
  · exact B2114967
  · exact B2114971
  · exact B2114975
  · exact B2114979
  · exact B2114983
  · exact B2114987
  · exact B2114991
  · exact B2114995
  · exact B2114999
  · exact B2115003
  · exact B2115007
  · exact B2115011
  · exact B2115015
  · exact B2115019
  · exact B2115023
  · exact B2115027
  · exact B2115031
  · exact B2115035
  · exact B2115039
  · exact B2115043
  · exact B2115047
  · exact B2115051
  · exact B2115055
  · exact B2115059
  · exact B2115063
  · exact B2115067
  · exact B2115071
  · exact B2115075
  · exact B2115079
  · exact B2115083
  · exact B2115087
  · exact B2115091
  · exact B2115095
  · exact B2115099
  · exact B2115103
  · exact B2115107
  · exact B2115111
  · exact B2115115
  · exact B2115119
  · exact B2115123
  · exact B2115127
  · exact B2115131
  · exact B2115135
  · exact B2115139
  · exact B2115143
  · exact B2115147
  · exact B2115151
  · exact B2115155
  · exact B2115159
  · exact B2115163
  · exact B2115167
  · exact B2115171
  · exact B2115175
  · exact B2115179
  · exact B2115183
  · exact B2115187
  · exact B2115191
  · exact B2115195
  · exact B2115199
  · exact B2115203
  · exact B2115207
  · exact B2115211
  · exact B2115215
  · exact B2115219
  · exact B2115223
  · exact B2115227
  · exact B2115231
  · exact B2115235
  · exact B2115239
  · exact B2115243
  · exact B2115247
  · exact B2115251
  · exact B2115255
  · exact B2115259
  · exact B2115263
  · exact B2115267
  · exact B2115271
  · exact B2115275
  · exact B2115279
  · exact B2115283
  · exact B2115287
  · exact B2115291
  · exact B2115295
  · exact B2115299
  · exact B2115303
  · exact B2115307
  · exact B2115311
  · exact B2115315
  · exact B2115319
  · exact B2115323
  · exact B2115327
  · exact B2115331
  · exact B2115335
  · exact B2115339
  · exact B2115343
  · exact B2115347
  · exact B2115351
  · exact B2115355
  · exact B2115359
  · exact B2115363
  · exact B2115367
  · exact B2115371
  · exact B2115375
  · exact B2115379
  · exact B2115383
  · exact B2115387
  · exact B2115391
  · exact B2115395
  · exact B2115399
  · exact B2115403
  · exact B2115407
  · exact B2115411
  · exact B2115415
  · exact B2115419
  · exact B2115423
  · exact B2115427
  · exact B2115431
  · exact B2115435
theorem solution (m : ℕ) (hlo : 2113435 ≤ m) (hhi : m ≤ 2115435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 528358 ≤ j := by omega
    have hj2 : j ≤ 528858 := by omega
    have hb : Blo 2113435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
