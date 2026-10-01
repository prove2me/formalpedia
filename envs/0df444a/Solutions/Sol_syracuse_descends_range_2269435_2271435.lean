-- Prove2me | solution 1 for syracuse_descends_range_2269435_2271435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:26.058131+00:00
-- url     : https://prove2.me/submissions/f4a9fa61-0ed6-4a1a-a8c3-b33aa5321ff6

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

theorem B2331785 : Blo 2269435 2331785 := bbase (se 2 (by rfl) ⟨874419, by rfl⟩ : syracuseStep 2331785 = 1748839) (by norm_num)
theorem B6218093 : Blo 2269435 6218093 := bstep (se 3 (by rfl) ⟨1165892, by rfl⟩ : syracuseStep 6218093 = 2331785) B2331785
theorem B16581581 : Blo 2269435 16581581 := bstep (se 3 (by rfl) ⟨3109046, by rfl⟩ : syracuseStep 16581581 = 6218093) B6218093
theorem B11054387 : Blo 2269435 11054387 := bstep (se 1 (by rfl) ⟨8290790, by rfl⟩ : syracuseStep 11054387 = 16581581) B16581581
theorem B7369591 : Blo 2269435 7369591 := bstep (se 1 (by rfl) ⟨5527193, by rfl⟩ : syracuseStep 7369591 = 11054387) B11054387
theorem B9826121 : Blo 2269435 9826121 := bstep (se 2 (by rfl) ⟨3684795, by rfl⟩ : syracuseStep 9826121 = 7369591) B7369591
theorem B26202989 : Blo 2269435 26202989 := bstep (se 3 (by rfl) ⟨4913060, by rfl⟩ : syracuseStep 26202989 = 9826121) B9826121
theorem B17468659 : Blo 2269435 17468659 := bstep (se 1 (by rfl) ⟨13101494, by rfl⟩ : syracuseStep 17468659 = 26202989) B26202989
theorem B23291545 : Blo 2269435 23291545 := bstep (se 2 (by rfl) ⟨8734329, by rfl⟩ : syracuseStep 23291545 = 17468659) B17468659
theorem B31055393 : Blo 2269435 31055393 := bstep (se 2 (by rfl) ⟨11645772, by rfl⟩ : syracuseStep 31055393 = 23291545) B23291545
theorem B20703595 : Blo 2269435 20703595 := bstep (se 1 (by rfl) ⟨15527696, by rfl⟩ : syracuseStep 20703595 = 31055393) B31055393
theorem B27604793 : Blo 2269435 27604793 := bstep (se 2 (by rfl) ⟨10351797, by rfl⟩ : syracuseStep 27604793 = 20703595) B20703595
theorem B18403195 : Blo 2269435 18403195 := bstep (se 1 (by rfl) ⟨13802396, by rfl⟩ : syracuseStep 18403195 = 27604793) B27604793
theorem B24537593 : Blo 2269435 24537593 := bstep (se 2 (by rfl) ⟨9201597, by rfl⟩ : syracuseStep 24537593 = 18403195) B18403195
theorem B16358395 : Blo 2269435 16358395 := bstep (se 1 (by rfl) ⟨12268796, by rfl⟩ : syracuseStep 16358395 = 24537593) B24537593
theorem B21811193 : Blo 2269435 21811193 := bstep (se 2 (by rfl) ⟨8179197, by rfl⟩ : syracuseStep 21811193 = 16358395) B16358395
theorem B14540795 : Blo 2269435 14540795 := bstep (se 1 (by rfl) ⟨10905596, by rfl⟩ : syracuseStep 14540795 = 21811193) B21811193
theorem B9693863 : Blo 2269435 9693863 := bstep (se 1 (by rfl) ⟨7270397, by rfl⟩ : syracuseStep 9693863 = 14540795) B14540795
theorem B6462575 : Blo 2269435 6462575 := bstep (se 1 (by rfl) ⟨4846931, by rfl⟩ : syracuseStep 6462575 = 9693863) B9693863
theorem B4308383 : Blo 2269435 4308383 := bstep (se 1 (by rfl) ⟨3231287, by rfl⟩ : syracuseStep 4308383 = 6462575) B6462575
theorem B2872255 : Blo 2269435 2872255 := bstep (se 1 (by rfl) ⟨2154191, by rfl⟩ : syracuseStep 2872255 = 4308383) B4308383
theorem B3829673 : Blo 2269435 3829673 := bstep (se 2 (by rfl) ⟨1436127, by rfl⟩ : syracuseStep 3829673 = 2872255) B2872255
theorem B2553115 : Blo 2269435 2553115 := bstep (se 1 (by rfl) ⟨1914836, by rfl⟩ : syracuseStep 2553115 = 3829673) B3829673
theorem B3404153 : Blo 2269435 3404153 := bstep (se 2 (by rfl) ⟨1276557, by rfl⟩ : syracuseStep 3404153 = 2553115) B2553115
theorem B2269435 : Blo 2269435 2269435 := bstep (se 1 (by rfl) ⟨1702076, by rfl⟩ : syracuseStep 2269435 = 3404153) B3404153
theorem B38775509 : Blo 2269435 38775509 := bbase (se 7 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 38775509 = 908801) (by norm_num)
theorem B25850339 : Blo 2269435 25850339 := bstep (se 1 (by rfl) ⟨19387754, by rfl⟩ : syracuseStep 25850339 = 38775509) B38775509
theorem B17233559 : Blo 2269435 17233559 := bstep (se 1 (by rfl) ⟨12925169, by rfl⟩ : syracuseStep 17233559 = 25850339) B25850339
theorem B11489039 : Blo 2269435 11489039 := bstep (se 1 (by rfl) ⟨8616779, by rfl⟩ : syracuseStep 11489039 = 17233559) B17233559
theorem B7659359 : Blo 2269435 7659359 := bstep (se 1 (by rfl) ⟨5744519, by rfl⟩ : syracuseStep 7659359 = 11489039) B11489039
theorem B5106239 : Blo 2269435 5106239 := bstep (se 1 (by rfl) ⟨3829679, by rfl⟩ : syracuseStep 5106239 = 7659359) B7659359
theorem B3404159 : Blo 2269435 3404159 := bstep (se 1 (by rfl) ⟨2553119, by rfl⟩ : syracuseStep 3404159 = 5106239) B5106239
theorem B2269439 : Blo 2269435 2269439 := bstep (se 1 (by rfl) ⟨1702079, by rfl⟩ : syracuseStep 2269439 = 3404159) B3404159
theorem B3404165 : Blo 2269435 3404165 := bbase (se 4 (by rfl) ⟨319140, by rfl⟩ : syracuseStep 3404165 = 638281) (by norm_num)
theorem B2269443 : Blo 2269435 2269443 := bstep (se 1 (by rfl) ⟨1702082, by rfl⟩ : syracuseStep 2269443 = 3404165) B3404165
theorem B3829693 : Blo 2269435 3829693 := bbase (se 3 (by rfl) ⟨718067, by rfl⟩ : syracuseStep 3829693 = 1436135) (by norm_num)
theorem B5106257 : Blo 2269435 5106257 := bstep (se 2 (by rfl) ⟨1914846, by rfl⟩ : syracuseStep 5106257 = 3829693) B3829693
theorem B3404171 : Blo 2269435 3404171 := bstep (se 1 (by rfl) ⟨2553128, by rfl⟩ : syracuseStep 3404171 = 5106257) B5106257
theorem B2269447 : Blo 2269435 2269447 := bstep (se 1 (by rfl) ⟨1702085, by rfl⟩ : syracuseStep 2269447 = 3404171) B3404171
theorem B2553133 : Blo 2269435 2553133 := bbase (se 3 (by rfl) ⟨478712, by rfl⟩ : syracuseStep 2553133 = 957425) (by norm_num)
theorem B3404177 : Blo 2269435 3404177 := bstep (se 2 (by rfl) ⟨1276566, by rfl⟩ : syracuseStep 3404177 = 2553133) B2553133
theorem B2269451 : Blo 2269435 2269451 := bstep (se 1 (by rfl) ⟨1702088, by rfl⟩ : syracuseStep 2269451 = 3404177) B3404177
theorem B7659413 : Blo 2269435 7659413 := bbase (se 6 (by rfl) ⟨179517, by rfl⟩ : syracuseStep 7659413 = 359035) (by norm_num)
theorem B5106275 : Blo 2269435 5106275 := bstep (se 1 (by rfl) ⟨3829706, by rfl⟩ : syracuseStep 5106275 = 7659413) B7659413
theorem B3404183 : Blo 2269435 3404183 := bstep (se 1 (by rfl) ⟨2553137, by rfl⟩ : syracuseStep 3404183 = 5106275) B5106275
theorem B2269455 : Blo 2269435 2269455 := bstep (se 1 (by rfl) ⟨1702091, by rfl⟩ : syracuseStep 2269455 = 3404183) B3404183
theorem B3404189 : Blo 2269435 3404189 := bbase (se 3 (by rfl) ⟨638285, by rfl⟩ : syracuseStep 3404189 = 1276571) (by norm_num)
theorem B2269459 : Blo 2269435 2269459 := bstep (se 1 (by rfl) ⟨1702094, by rfl⟩ : syracuseStep 2269459 = 3404189) B3404189
theorem B5106293 : Blo 2269435 5106293 := bbase (se 5 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 5106293 = 478715) (by norm_num)
theorem B3404195 : Blo 2269435 3404195 := bstep (se 1 (by rfl) ⟨2553146, by rfl⟩ : syracuseStep 3404195 = 5106293) B5106293
theorem B2269463 : Blo 2269435 2269463 := bstep (se 1 (by rfl) ⟨1702097, by rfl⟩ : syracuseStep 2269463 = 3404195) B3404195
theorem B10905749 : Blo 2269435 10905749 := bbase (se 6 (by rfl) ⟨255603, by rfl⟩ : syracuseStep 10905749 = 511207) (by norm_num)
theorem B7270499 : Blo 2269435 7270499 := bstep (se 1 (by rfl) ⟨5452874, by rfl⟩ : syracuseStep 7270499 = 10905749) B10905749
theorem B19387997 : Blo 2269435 19387997 := bstep (se 3 (by rfl) ⟨3635249, by rfl⟩ : syracuseStep 19387997 = 7270499) B7270499
theorem B12925331 : Blo 2269435 12925331 := bstep (se 1 (by rfl) ⟨9693998, by rfl⟩ : syracuseStep 12925331 = 19387997) B19387997
theorem B8616887 : Blo 2269435 8616887 := bstep (se 1 (by rfl) ⟨6462665, by rfl⟩ : syracuseStep 8616887 = 12925331) B12925331
theorem B5744591 : Blo 2269435 5744591 := bstep (se 1 (by rfl) ⟨4308443, by rfl⟩ : syracuseStep 5744591 = 8616887) B8616887
theorem B3829727 : Blo 2269435 3829727 := bstep (se 1 (by rfl) ⟨2872295, by rfl⟩ : syracuseStep 3829727 = 5744591) B5744591
theorem B2553151 : Blo 2269435 2553151 := bstep (se 1 (by rfl) ⟨1914863, by rfl⟩ : syracuseStep 2553151 = 3829727) B3829727
theorem B3404201 : Blo 2269435 3404201 := bstep (se 2 (by rfl) ⟨1276575, by rfl⟩ : syracuseStep 3404201 = 2553151) B2553151
theorem B2269467 : Blo 2269435 2269467 := bstep (se 1 (by rfl) ⟨1702100, by rfl⟩ : syracuseStep 2269467 = 3404201) B3404201
theorem B8616901 : Blo 2269435 8616901 := bbase (se 4 (by rfl) ⟨807834, by rfl⟩ : syracuseStep 8616901 = 1615669) (by norm_num)
theorem B11489201 : Blo 2269435 11489201 := bstep (se 2 (by rfl) ⟨4308450, by rfl⟩ : syracuseStep 11489201 = 8616901) B8616901
theorem B7659467 : Blo 2269435 7659467 := bstep (se 1 (by rfl) ⟨5744600, by rfl⟩ : syracuseStep 7659467 = 11489201) B11489201
theorem B5106311 : Blo 2269435 5106311 := bstep (se 1 (by rfl) ⟨3829733, by rfl⟩ : syracuseStep 5106311 = 7659467) B7659467
theorem B3404207 : Blo 2269435 3404207 := bstep (se 1 (by rfl) ⟨2553155, by rfl⟩ : syracuseStep 3404207 = 5106311) B5106311
theorem B2269471 : Blo 2269435 2269471 := bstep (se 1 (by rfl) ⟨1702103, by rfl⟩ : syracuseStep 2269471 = 3404207) B3404207
theorem B3404213 : Blo 2269435 3404213 := bbase (se 5 (by rfl) ⟨159572, by rfl⟩ : syracuseStep 3404213 = 319145) (by norm_num)
theorem B2269475 : Blo 2269435 2269475 := bstep (se 1 (by rfl) ⟨1702106, by rfl⟩ : syracuseStep 2269475 = 3404213) B3404213
theorem B5744621 : Blo 2269435 5744621 := bbase (se 3 (by rfl) ⟨1077116, by rfl⟩ : syracuseStep 5744621 = 2154233) (by norm_num)
theorem B3829747 : Blo 2269435 3829747 := bstep (se 1 (by rfl) ⟨2872310, by rfl⟩ : syracuseStep 3829747 = 5744621) B5744621
theorem B5106329 : Blo 2269435 5106329 := bstep (se 2 (by rfl) ⟨1914873, by rfl⟩ : syracuseStep 5106329 = 3829747) B3829747
theorem B3404219 : Blo 2269435 3404219 := bstep (se 1 (by rfl) ⟨2553164, by rfl⟩ : syracuseStep 3404219 = 5106329) B5106329
theorem B2269479 : Blo 2269435 2269479 := bstep (se 1 (by rfl) ⟨1702109, by rfl⟩ : syracuseStep 2269479 = 3404219) B3404219
theorem B2553169 : Blo 2269435 2553169 := bbase (se 2 (by rfl) ⟨957438, by rfl⟩ : syracuseStep 2553169 = 1914877) (by norm_num)
theorem B3404225 : Blo 2269435 3404225 := bstep (se 2 (by rfl) ⟨1276584, by rfl⟩ : syracuseStep 3404225 = 2553169) B2553169
theorem B2269483 : Blo 2269435 2269483 := bstep (se 1 (by rfl) ⟨1702112, by rfl⟩ : syracuseStep 2269483 = 3404225) B3404225
theorem B2423521 : Blo 2269435 2423521 := bbase (se 2 (by rfl) ⟨908820, by rfl⟩ : syracuseStep 2423521 = 1817641) (by norm_num)
theorem B3231361 : Blo 2269435 3231361 := bstep (se 2 (by rfl) ⟨1211760, by rfl⟩ : syracuseStep 3231361 = 2423521) B2423521
theorem B4308481 : Blo 2269435 4308481 := bstep (se 2 (by rfl) ⟨1615680, by rfl⟩ : syracuseStep 4308481 = 3231361) B3231361
theorem B5744641 : Blo 2269435 5744641 := bstep (se 2 (by rfl) ⟨2154240, by rfl⟩ : syracuseStep 5744641 = 4308481) B4308481
theorem B7659521 : Blo 2269435 7659521 := bstep (se 2 (by rfl) ⟨2872320, by rfl⟩ : syracuseStep 7659521 = 5744641) B5744641
theorem B5106347 : Blo 2269435 5106347 := bstep (se 1 (by rfl) ⟨3829760, by rfl⟩ : syracuseStep 5106347 = 7659521) B7659521
theorem B3404231 : Blo 2269435 3404231 := bstep (se 1 (by rfl) ⟨2553173, by rfl⟩ : syracuseStep 3404231 = 5106347) B5106347
theorem B2269487 : Blo 2269435 2269487 := bstep (se 1 (by rfl) ⟨1702115, by rfl⟩ : syracuseStep 2269487 = 3404231) B3404231
theorem B3404237 : Blo 2269435 3404237 := bbase (se 3 (by rfl) ⟨638294, by rfl⟩ : syracuseStep 3404237 = 1276589) (by norm_num)
theorem B2269491 : Blo 2269435 2269491 := bstep (se 1 (by rfl) ⟨1702118, by rfl⟩ : syracuseStep 2269491 = 3404237) B3404237
theorem B5106365 : Blo 2269435 5106365 := bbase (se 3 (by rfl) ⟨957443, by rfl⟩ : syracuseStep 5106365 = 1914887) (by norm_num)
theorem B3404243 : Blo 2269435 3404243 := bstep (se 1 (by rfl) ⟨2553182, by rfl⟩ : syracuseStep 3404243 = 5106365) B5106365
theorem B2269495 : Blo 2269435 2269495 := bstep (se 1 (by rfl) ⟨1702121, by rfl⟩ : syracuseStep 2269495 = 3404243) B3404243
theorem B3829781 : Blo 2269435 3829781 := bbase (se 6 (by rfl) ⟨89760, by rfl⟩ : syracuseStep 3829781 = 179521) (by norm_num)
theorem B2553187 : Blo 2269435 2553187 := bstep (se 1 (by rfl) ⟨1914890, by rfl⟩ : syracuseStep 2553187 = 3829781) B3829781
theorem B3404249 : Blo 2269435 3404249 := bstep (se 2 (by rfl) ⟨1276593, by rfl⟩ : syracuseStep 3404249 = 2553187) B2553187
theorem B2269499 : Blo 2269435 2269499 := bstep (se 1 (by rfl) ⟨1702124, by rfl⟩ : syracuseStep 2269499 = 3404249) B3404249
theorem B13991125 : Blo 2269435 13991125 := bbase (se 7 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 13991125 = 327917) (by norm_num)
theorem B18654833 : Blo 2269435 18654833 := bstep (se 2 (by rfl) ⟨6995562, by rfl⟩ : syracuseStep 18654833 = 13991125) B13991125
theorem B49746221 : Blo 2269435 49746221 := bstep (se 3 (by rfl) ⟨9327416, by rfl⟩ : syracuseStep 49746221 = 18654833) B18654833
theorem B33164147 : Blo 2269435 33164147 := bstep (se 1 (by rfl) ⟨24873110, by rfl⟩ : syracuseStep 33164147 = 49746221) B49746221
theorem B22109431 : Blo 2269435 22109431 := bstep (se 1 (by rfl) ⟨16582073, by rfl⟩ : syracuseStep 22109431 = 33164147) B33164147
theorem B29479241 : Blo 2269435 29479241 := bstep (se 2 (by rfl) ⟨11054715, by rfl⟩ : syracuseStep 29479241 = 22109431) B22109431
theorem B19652827 : Blo 2269435 19652827 := bstep (se 1 (by rfl) ⟨14739620, by rfl⟩ : syracuseStep 19652827 = 29479241) B29479241
theorem B26203769 : Blo 2269435 26203769 := bstep (se 2 (by rfl) ⟨9826413, by rfl⟩ : syracuseStep 26203769 = 19652827) B19652827
theorem B17469179 : Blo 2269435 17469179 := bstep (se 1 (by rfl) ⟨13101884, by rfl⟩ : syracuseStep 17469179 = 26203769) B26203769
theorem B11646119 : Blo 2269435 11646119 := bstep (se 1 (by rfl) ⟨8734589, by rfl⟩ : syracuseStep 11646119 = 17469179) B17469179
theorem B31056317 : Blo 2269435 31056317 := bstep (se 3 (by rfl) ⟨5823059, by rfl⟩ : syracuseStep 31056317 = 11646119) B11646119
theorem B20704211 : Blo 2269435 20704211 := bstep (se 1 (by rfl) ⟨15528158, by rfl⟩ : syracuseStep 20704211 = 31056317) B31056317
theorem B13802807 : Blo 2269435 13802807 := bstep (se 1 (by rfl) ⟨10352105, by rfl⟩ : syracuseStep 13802807 = 20704211) B20704211
theorem B9201871 : Blo 2269435 9201871 := bstep (se 1 (by rfl) ⟨6901403, by rfl⟩ : syracuseStep 9201871 = 13802807) B13802807
theorem B12269161 : Blo 2269435 12269161 := bstep (se 2 (by rfl) ⟨4600935, by rfl⟩ : syracuseStep 12269161 = 9201871) B9201871
theorem B16358881 : Blo 2269435 16358881 := bstep (se 2 (by rfl) ⟨6134580, by rfl⟩ : syracuseStep 16358881 = 12269161) B12269161
theorem B21811841 : Blo 2269435 21811841 := bstep (se 2 (by rfl) ⟨8179440, by rfl⟩ : syracuseStep 21811841 = 16358881) B16358881
theorem B14541227 : Blo 2269435 14541227 := bstep (se 1 (by rfl) ⟨10905920, by rfl⟩ : syracuseStep 14541227 = 21811841) B21811841
theorem B9694151 : Blo 2269435 9694151 := bstep (se 1 (by rfl) ⟨7270613, by rfl⟩ : syracuseStep 9694151 = 14541227) B14541227
theorem B6462767 : Blo 2269435 6462767 := bstep (se 1 (by rfl) ⟨4847075, by rfl⟩ : syracuseStep 6462767 = 9694151) B9694151
theorem B17234045 : Blo 2269435 17234045 := bstep (se 3 (by rfl) ⟨3231383, by rfl⟩ : syracuseStep 17234045 = 6462767) B6462767
theorem B11489363 : Blo 2269435 11489363 := bstep (se 1 (by rfl) ⟨8617022, by rfl⟩ : syracuseStep 11489363 = 17234045) B17234045
theorem B7659575 : Blo 2269435 7659575 := bstep (se 1 (by rfl) ⟨5744681, by rfl⟩ : syracuseStep 7659575 = 11489363) B11489363
theorem B5106383 : Blo 2269435 5106383 := bstep (se 1 (by rfl) ⟨3829787, by rfl⟩ : syracuseStep 5106383 = 7659575) B7659575
theorem B3404255 : Blo 2269435 3404255 := bstep (se 1 (by rfl) ⟨2553191, by rfl⟩ : syracuseStep 3404255 = 5106383) B5106383
theorem B2269503 : Blo 2269435 2269503 := bstep (se 1 (by rfl) ⟨1702127, by rfl⟩ : syracuseStep 2269503 = 3404255) B3404255
theorem B3404261 : Blo 2269435 3404261 := bbase (se 4 (by rfl) ⟨319149, by rfl⟩ : syracuseStep 3404261 = 638299) (by norm_num)
theorem B2269507 : Blo 2269435 2269507 := bstep (se 1 (by rfl) ⟨1702130, by rfl⟩ : syracuseStep 2269507 = 3404261) B3404261
theorem B27605717 : Blo 2269435 27605717 := bbase (se 7 (by rfl) ⟨323504, by rfl⟩ : syracuseStep 27605717 = 647009) (by norm_num)
theorem B18403811 : Blo 2269435 18403811 := bstep (se 1 (by rfl) ⟨13802858, by rfl⟩ : syracuseStep 18403811 = 27605717) B27605717
theorem B12269207 : Blo 2269435 12269207 := bstep (se 1 (by rfl) ⟨9201905, by rfl⟩ : syracuseStep 12269207 = 18403811) B18403811
theorem B8179471 : Blo 2269435 8179471 := bstep (se 1 (by rfl) ⟨6134603, by rfl⟩ : syracuseStep 8179471 = 12269207) B12269207
theorem B10905961 : Blo 2269435 10905961 := bstep (se 2 (by rfl) ⟨4089735, by rfl⟩ : syracuseStep 10905961 = 8179471) B8179471
theorem B14541281 : Blo 2269435 14541281 := bstep (se 2 (by rfl) ⟨5452980, by rfl⟩ : syracuseStep 14541281 = 10905961) B10905961
theorem B9694187 : Blo 2269435 9694187 := bstep (se 1 (by rfl) ⟨7270640, by rfl⟩ : syracuseStep 9694187 = 14541281) B14541281
theorem B6462791 : Blo 2269435 6462791 := bstep (se 1 (by rfl) ⟨4847093, by rfl⟩ : syracuseStep 6462791 = 9694187) B9694187
theorem B4308527 : Blo 2269435 4308527 := bstep (se 1 (by rfl) ⟨3231395, by rfl⟩ : syracuseStep 4308527 = 6462791) B6462791
theorem B2872351 : Blo 2269435 2872351 := bstep (se 1 (by rfl) ⟨2154263, by rfl⟩ : syracuseStep 2872351 = 4308527) B4308527
theorem B3829801 : Blo 2269435 3829801 := bstep (se 2 (by rfl) ⟨1436175, by rfl⟩ : syracuseStep 3829801 = 2872351) B2872351
theorem B5106401 : Blo 2269435 5106401 := bstep (se 2 (by rfl) ⟨1914900, by rfl⟩ : syracuseStep 5106401 = 3829801) B3829801
theorem B3404267 : Blo 2269435 3404267 := bstep (se 1 (by rfl) ⟨2553200, by rfl⟩ : syracuseStep 3404267 = 5106401) B5106401
theorem B2269511 : Blo 2269435 2269511 := bstep (se 1 (by rfl) ⟨1702133, by rfl⟩ : syracuseStep 2269511 = 3404267) B3404267
theorem B2553205 : Blo 2269435 2553205 := bbase (se 5 (by rfl) ⟨119681, by rfl⟩ : syracuseStep 2553205 = 239363) (by norm_num)
theorem B3404273 : Blo 2269435 3404273 := bstep (se 2 (by rfl) ⟨1276602, by rfl⟩ : syracuseStep 3404273 = 2553205) B2553205
theorem B2269515 : Blo 2269435 2269515 := bstep (se 1 (by rfl) ⟨1702136, by rfl⟩ : syracuseStep 2269515 = 3404273) B3404273
theorem B2872361 : Blo 2269435 2872361 := bbase (se 2 (by rfl) ⟨1077135, by rfl⟩ : syracuseStep 2872361 = 2154271) (by norm_num)
theorem B7659629 : Blo 2269435 7659629 := bstep (se 3 (by rfl) ⟨1436180, by rfl⟩ : syracuseStep 7659629 = 2872361) B2872361
theorem B5106419 : Blo 2269435 5106419 := bstep (se 1 (by rfl) ⟨3829814, by rfl⟩ : syracuseStep 5106419 = 7659629) B7659629
theorem B3404279 : Blo 2269435 3404279 := bstep (se 1 (by rfl) ⟨2553209, by rfl⟩ : syracuseStep 3404279 = 5106419) B5106419
theorem B2269519 : Blo 2269435 2269519 := bstep (se 1 (by rfl) ⟨1702139, by rfl⟩ : syracuseStep 2269519 = 3404279) B3404279
theorem B3404285 : Blo 2269435 3404285 := bbase (se 3 (by rfl) ⟨638303, by rfl⟩ : syracuseStep 3404285 = 1276607) (by norm_num)
theorem B2269523 : Blo 2269435 2269523 := bstep (se 1 (by rfl) ⟨1702142, by rfl⟩ : syracuseStep 2269523 = 3404285) B3404285
theorem B5106437 : Blo 2269435 5106437 := bbase (se 4 (by rfl) ⟨478728, by rfl⟩ : syracuseStep 5106437 = 957457) (by norm_num)
theorem B3404291 : Blo 2269435 3404291 := bstep (se 1 (by rfl) ⟨2553218, by rfl⟩ : syracuseStep 3404291 = 5106437) B5106437
theorem B2269527 : Blo 2269435 2269527 := bstep (se 1 (by rfl) ⟨1702145, by rfl⟩ : syracuseStep 2269527 = 3404291) B3404291
theorem B4308565 : Blo 2269435 4308565 := bbase (se 8 (by rfl) ⟨25245, by rfl⟩ : syracuseStep 4308565 = 50491) (by norm_num)
theorem B5744753 : Blo 2269435 5744753 := bstep (se 2 (by rfl) ⟨2154282, by rfl⟩ : syracuseStep 5744753 = 4308565) B4308565
theorem B3829835 : Blo 2269435 3829835 := bstep (se 1 (by rfl) ⟨2872376, by rfl⟩ : syracuseStep 3829835 = 5744753) B5744753
theorem B2553223 : Blo 2269435 2553223 := bstep (se 1 (by rfl) ⟨1914917, by rfl⟩ : syracuseStep 2553223 = 3829835) B3829835
theorem B3404297 : Blo 2269435 3404297 := bstep (se 2 (by rfl) ⟨1276611, by rfl⟩ : syracuseStep 3404297 = 2553223) B2553223
theorem B2269531 : Blo 2269435 2269531 := bstep (se 1 (by rfl) ⟨1702148, by rfl⟩ : syracuseStep 2269531 = 3404297) B3404297
theorem B11489525 : Blo 2269435 11489525 := bbase (se 5 (by rfl) ⟨538571, by rfl⟩ : syracuseStep 11489525 = 1077143) (by norm_num)
theorem B7659683 : Blo 2269435 7659683 := bstep (se 1 (by rfl) ⟨5744762, by rfl⟩ : syracuseStep 7659683 = 11489525) B11489525
theorem B5106455 : Blo 2269435 5106455 := bstep (se 1 (by rfl) ⟨3829841, by rfl⟩ : syracuseStep 5106455 = 7659683) B7659683
theorem B3404303 : Blo 2269435 3404303 := bstep (se 1 (by rfl) ⟨2553227, by rfl⟩ : syracuseStep 3404303 = 5106455) B5106455
theorem B2269535 : Blo 2269435 2269535 := bstep (se 1 (by rfl) ⟨1702151, by rfl⟩ : syracuseStep 2269535 = 3404303) B3404303
theorem B3404309 : Blo 2269435 3404309 := bbase (se 6 (by rfl) ⟨79788, by rfl⟩ : syracuseStep 3404309 = 159577) (by norm_num)
theorem B2269539 : Blo 2269435 2269539 := bstep (se 1 (by rfl) ⟨1702154, by rfl⟩ : syracuseStep 2269539 = 3404309) B3404309
theorem B2300509 : Blo 2269435 2300509 := bbase (se 3 (by rfl) ⟨431345, by rfl⟩ : syracuseStep 2300509 = 862691) (by norm_num)
theorem B3067345 : Blo 2269435 3067345 := bstep (se 2 (by rfl) ⟨1150254, by rfl⟩ : syracuseStep 3067345 = 2300509) B2300509
theorem B4089793 : Blo 2269435 4089793 := bstep (se 2 (by rfl) ⟨1533672, by rfl⟩ : syracuseStep 4089793 = 3067345) B3067345
theorem B5453057 : Blo 2269435 5453057 := bstep (se 2 (by rfl) ⟨2044896, by rfl⟩ : syracuseStep 5453057 = 4089793) B4089793
theorem B3635371 : Blo 2269435 3635371 := bstep (se 1 (by rfl) ⟨2726528, by rfl⟩ : syracuseStep 3635371 = 5453057) B5453057
theorem B19388645 : Blo 2269435 19388645 := bstep (se 4 (by rfl) ⟨1817685, by rfl⟩ : syracuseStep 19388645 = 3635371) B3635371
theorem B12925763 : Blo 2269435 12925763 := bstep (se 1 (by rfl) ⟨9694322, by rfl⟩ : syracuseStep 12925763 = 19388645) B19388645
theorem B8617175 : Blo 2269435 8617175 := bstep (se 1 (by rfl) ⟨6462881, by rfl⟩ : syracuseStep 8617175 = 12925763) B12925763
theorem B5744783 : Blo 2269435 5744783 := bstep (se 1 (by rfl) ⟨4308587, by rfl⟩ : syracuseStep 5744783 = 8617175) B8617175
theorem B3829855 : Blo 2269435 3829855 := bstep (se 1 (by rfl) ⟨2872391, by rfl⟩ : syracuseStep 3829855 = 5744783) B5744783
theorem B5106473 : Blo 2269435 5106473 := bstep (se 2 (by rfl) ⟨1914927, by rfl⟩ : syracuseStep 5106473 = 3829855) B3829855
theorem B3404315 : Blo 2269435 3404315 := bstep (se 1 (by rfl) ⟨2553236, by rfl⟩ : syracuseStep 3404315 = 5106473) B5106473
theorem B2269543 : Blo 2269435 2269543 := bstep (se 1 (by rfl) ⟨1702157, by rfl⟩ : syracuseStep 2269543 = 3404315) B3404315
theorem B2553241 : Blo 2269435 2553241 := bbase (se 2 (by rfl) ⟨957465, by rfl⟩ : syracuseStep 2553241 = 1914931) (by norm_num)
theorem B3404321 : Blo 2269435 3404321 := bstep (se 2 (by rfl) ⟨1276620, by rfl⟩ : syracuseStep 3404321 = 2553241) B2553241
theorem B2269547 : Blo 2269435 2269547 := bstep (se 1 (by rfl) ⟨1702160, by rfl⟩ : syracuseStep 2269547 = 3404321) B3404321
theorem B8617205 : Blo 2269435 8617205 := bbase (se 5 (by rfl) ⟨403931, by rfl⟩ : syracuseStep 8617205 = 807863) (by norm_num)
theorem B5744803 : Blo 2269435 5744803 := bstep (se 1 (by rfl) ⟨4308602, by rfl⟩ : syracuseStep 5744803 = 8617205) B8617205
theorem B7659737 : Blo 2269435 7659737 := bstep (se 2 (by rfl) ⟨2872401, by rfl⟩ : syracuseStep 7659737 = 5744803) B5744803
theorem B5106491 : Blo 2269435 5106491 := bstep (se 1 (by rfl) ⟨3829868, by rfl⟩ : syracuseStep 5106491 = 7659737) B7659737
theorem B3404327 : Blo 2269435 3404327 := bstep (se 1 (by rfl) ⟨2553245, by rfl⟩ : syracuseStep 3404327 = 5106491) B5106491
theorem B2269551 : Blo 2269435 2269551 := bstep (se 1 (by rfl) ⟨1702163, by rfl⟩ : syracuseStep 2269551 = 3404327) B3404327
theorem B3404333 : Blo 2269435 3404333 := bbase (se 3 (by rfl) ⟨638312, by rfl⟩ : syracuseStep 3404333 = 1276625) (by norm_num)
theorem B2269555 : Blo 2269435 2269555 := bstep (se 1 (by rfl) ⟨1702166, by rfl⟩ : syracuseStep 2269555 = 3404333) B3404333
theorem B5106509 : Blo 2269435 5106509 := bbase (se 3 (by rfl) ⟨957470, by rfl⟩ : syracuseStep 5106509 = 1914941) (by norm_num)
theorem B3404339 : Blo 2269435 3404339 := bstep (se 1 (by rfl) ⟨2553254, by rfl⟩ : syracuseStep 3404339 = 5106509) B5106509
theorem B2269559 : Blo 2269435 2269559 := bstep (se 1 (by rfl) ⟨1702169, by rfl⟩ : syracuseStep 2269559 = 3404339) B3404339
theorem B2872417 : Blo 2269435 2872417 := bbase (se 2 (by rfl) ⟨1077156, by rfl⟩ : syracuseStep 2872417 = 2154313) (by norm_num)
theorem B3829889 : Blo 2269435 3829889 := bstep (se 2 (by rfl) ⟨1436208, by rfl⟩ : syracuseStep 3829889 = 2872417) B2872417
theorem B2553259 : Blo 2269435 2553259 := bstep (se 1 (by rfl) ⟨1914944, by rfl⟩ : syracuseStep 2553259 = 3829889) B3829889
theorem B3404345 : Blo 2269435 3404345 := bstep (se 2 (by rfl) ⟨1276629, by rfl⟩ : syracuseStep 3404345 = 2553259) B2553259
theorem B2269563 : Blo 2269435 2269563 := bstep (se 1 (by rfl) ⟨1702172, by rfl⟩ : syracuseStep 2269563 = 3404345) B3404345
theorem B25851797 : Blo 2269435 25851797 := bbase (se 6 (by rfl) ⟨605901, by rfl⟩ : syracuseStep 25851797 = 1211803) (by norm_num)
theorem B17234531 : Blo 2269435 17234531 := bstep (se 1 (by rfl) ⟨12925898, by rfl⟩ : syracuseStep 17234531 = 25851797) B25851797
theorem B11489687 : Blo 2269435 11489687 := bstep (se 1 (by rfl) ⟨8617265, by rfl⟩ : syracuseStep 11489687 = 17234531) B17234531
theorem B7659791 : Blo 2269435 7659791 := bstep (se 1 (by rfl) ⟨5744843, by rfl⟩ : syracuseStep 7659791 = 11489687) B11489687
theorem B5106527 : Blo 2269435 5106527 := bstep (se 1 (by rfl) ⟨3829895, by rfl⟩ : syracuseStep 5106527 = 7659791) B7659791
theorem B3404351 : Blo 2269435 3404351 := bstep (se 1 (by rfl) ⟨2553263, by rfl⟩ : syracuseStep 3404351 = 5106527) B5106527
theorem B2269567 : Blo 2269435 2269567 := bstep (se 1 (by rfl) ⟨1702175, by rfl⟩ : syracuseStep 2269567 = 3404351) B3404351
theorem B3404357 : Blo 2269435 3404357 := bbase (se 4 (by rfl) ⟨319158, by rfl⟩ : syracuseStep 3404357 = 638317) (by norm_num)
theorem B2269571 : Blo 2269435 2269571 := bstep (se 1 (by rfl) ⟨1702178, by rfl⟩ : syracuseStep 2269571 = 3404357) B3404357
theorem B3829909 : Blo 2269435 3829909 := bbase (se 6 (by rfl) ⟨89763, by rfl⟩ : syracuseStep 3829909 = 179527) (by norm_num)
theorem B5106545 : Blo 2269435 5106545 := bstep (se 2 (by rfl) ⟨1914954, by rfl⟩ : syracuseStep 5106545 = 3829909) B3829909
theorem B3404363 : Blo 2269435 3404363 := bstep (se 1 (by rfl) ⟨2553272, by rfl⟩ : syracuseStep 3404363 = 5106545) B5106545
theorem B2269575 : Blo 2269435 2269575 := bstep (se 1 (by rfl) ⟨1702181, by rfl⟩ : syracuseStep 2269575 = 3404363) B3404363
theorem B2553277 : Blo 2269435 2553277 := bbase (se 3 (by rfl) ⟨478739, by rfl⟩ : syracuseStep 2553277 = 957479) (by norm_num)
theorem B3404369 : Blo 2269435 3404369 := bstep (se 2 (by rfl) ⟨1276638, by rfl⟩ : syracuseStep 3404369 = 2553277) B2553277
theorem B2269579 : Blo 2269435 2269579 := bstep (se 1 (by rfl) ⟨1702184, by rfl⟩ : syracuseStep 2269579 = 3404369) B3404369
theorem B7659845 : Blo 2269435 7659845 := bbase (se 4 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 7659845 = 1436221) (by norm_num)
theorem B5106563 : Blo 2269435 5106563 := bstep (se 1 (by rfl) ⟨3829922, by rfl⟩ : syracuseStep 5106563 = 7659845) B7659845
theorem B3404375 : Blo 2269435 3404375 := bstep (se 1 (by rfl) ⟨2553281, by rfl⟩ : syracuseStep 3404375 = 5106563) B5106563
theorem B2269583 : Blo 2269435 2269583 := bstep (se 1 (by rfl) ⟨1702187, by rfl⟩ : syracuseStep 2269583 = 3404375) B3404375
theorem B3404381 : Blo 2269435 3404381 := bbase (se 3 (by rfl) ⟨638321, by rfl⟩ : syracuseStep 3404381 = 1276643) (by norm_num)
theorem B2269587 : Blo 2269435 2269587 := bstep (se 1 (by rfl) ⟨1702190, by rfl⟩ : syracuseStep 2269587 = 3404381) B3404381
theorem B5106581 : Blo 2269435 5106581 := bbase (se 6 (by rfl) ⟨119685, by rfl⟩ : syracuseStep 5106581 = 239371) (by norm_num)
theorem B3404387 : Blo 2269435 3404387 := bstep (se 1 (by rfl) ⟨2553290, by rfl⟩ : syracuseStep 3404387 = 5106581) B5106581
theorem B2269591 : Blo 2269435 2269591 := bstep (se 1 (by rfl) ⟨1702193, by rfl⟩ : syracuseStep 2269591 = 3404387) B3404387
theorem B3275605 : Blo 2269435 3275605 := bbase (se 9 (by rfl) ⟨9596, by rfl⟩ : syracuseStep 3275605 = 19193) (by norm_num)
theorem B17469893 : Blo 2269435 17469893 := bstep (se 4 (by rfl) ⟨1637802, by rfl⟩ : syracuseStep 17469893 = 3275605) B3275605
theorem B11646595 : Blo 2269435 11646595 := bstep (se 1 (by rfl) ⟨8734946, by rfl⟩ : syracuseStep 11646595 = 17469893) B17469893
theorem B62115173 : Blo 2269435 62115173 := bstep (se 4 (by rfl) ⟨5823297, by rfl⟩ : syracuseStep 62115173 = 11646595) B11646595
theorem B41410115 : Blo 2269435 41410115 := bstep (se 1 (by rfl) ⟨31057586, by rfl⟩ : syracuseStep 41410115 = 62115173) B62115173
theorem B27606743 : Blo 2269435 27606743 := bstep (se 1 (by rfl) ⟨20705057, by rfl⟩ : syracuseStep 27606743 = 41410115) B41410115
theorem B18404495 : Blo 2269435 18404495 := bstep (se 1 (by rfl) ⟨13803371, by rfl⟩ : syracuseStep 18404495 = 27606743) B27606743
theorem B12269663 : Blo 2269435 12269663 := bstep (se 1 (by rfl) ⟨9202247, by rfl⟩ : syracuseStep 12269663 = 18404495) B18404495
theorem B8179775 : Blo 2269435 8179775 := bstep (se 1 (by rfl) ⟨6134831, by rfl⟩ : syracuseStep 8179775 = 12269663) B12269663
theorem B5453183 : Blo 2269435 5453183 := bstep (se 1 (by rfl) ⟨4089887, by rfl⟩ : syracuseStep 5453183 = 8179775) B8179775
theorem B3635455 : Blo 2269435 3635455 := bstep (se 1 (by rfl) ⟨2726591, by rfl⟩ : syracuseStep 3635455 = 5453183) B5453183
theorem B4847273 : Blo 2269435 4847273 := bstep (se 2 (by rfl) ⟨1817727, by rfl⟩ : syracuseStep 4847273 = 3635455) B3635455
theorem B3231515 : Blo 2269435 3231515 := bstep (se 1 (by rfl) ⟨2423636, by rfl⟩ : syracuseStep 3231515 = 4847273) B4847273
theorem B8617373 : Blo 2269435 8617373 := bstep (se 3 (by rfl) ⟨1615757, by rfl⟩ : syracuseStep 8617373 = 3231515) B3231515
theorem B5744915 : Blo 2269435 5744915 := bstep (se 1 (by rfl) ⟨4308686, by rfl⟩ : syracuseStep 5744915 = 8617373) B8617373
theorem B3829943 : Blo 2269435 3829943 := bstep (se 1 (by rfl) ⟨2872457, by rfl⟩ : syracuseStep 3829943 = 5744915) B5744915
theorem B2553295 : Blo 2269435 2553295 := bstep (se 1 (by rfl) ⟨1914971, by rfl⟩ : syracuseStep 2553295 = 3829943) B3829943
theorem B3404393 : Blo 2269435 3404393 := bstep (se 2 (by rfl) ⟨1276647, by rfl⟩ : syracuseStep 3404393 = 2553295) B2553295
theorem B2269595 : Blo 2269435 2269595 := bstep (se 1 (by rfl) ⟨1702196, by rfl⟩ : syracuseStep 2269595 = 3404393) B3404393
theorem B9202261 : Blo 2269435 9202261 := bbase (se 8 (by rfl) ⟨53919, by rfl⟩ : syracuseStep 9202261 = 107839) (by norm_num)
theorem B12269681 : Blo 2269435 12269681 := bstep (se 2 (by rfl) ⟨4601130, by rfl⟩ : syracuseStep 12269681 = 9202261) B9202261
theorem B8179787 : Blo 2269435 8179787 := bstep (se 1 (by rfl) ⟨6134840, by rfl⟩ : syracuseStep 8179787 = 12269681) B12269681
theorem B5453191 : Blo 2269435 5453191 := bstep (se 1 (by rfl) ⟨4089893, by rfl⟩ : syracuseStep 5453191 = 8179787) B8179787
theorem B7270921 : Blo 2269435 7270921 := bstep (se 2 (by rfl) ⟨2726595, by rfl⟩ : syracuseStep 7270921 = 5453191) B5453191
theorem B9694561 : Blo 2269435 9694561 := bstep (se 2 (by rfl) ⟨3635460, by rfl⟩ : syracuseStep 9694561 = 7270921) B7270921
theorem B12926081 : Blo 2269435 12926081 := bstep (se 2 (by rfl) ⟨4847280, by rfl⟩ : syracuseStep 12926081 = 9694561) B9694561
theorem B8617387 : Blo 2269435 8617387 := bstep (se 1 (by rfl) ⟨6463040, by rfl⟩ : syracuseStep 8617387 = 12926081) B12926081
theorem B11489849 : Blo 2269435 11489849 := bstep (se 2 (by rfl) ⟨4308693, by rfl⟩ : syracuseStep 11489849 = 8617387) B8617387
theorem B7659899 : Blo 2269435 7659899 := bstep (se 1 (by rfl) ⟨5744924, by rfl⟩ : syracuseStep 7659899 = 11489849) B11489849
theorem B5106599 : Blo 2269435 5106599 := bstep (se 1 (by rfl) ⟨3829949, by rfl⟩ : syracuseStep 5106599 = 7659899) B7659899
theorem B3404399 : Blo 2269435 3404399 := bstep (se 1 (by rfl) ⟨2553299, by rfl⟩ : syracuseStep 3404399 = 5106599) B5106599
theorem B2269599 : Blo 2269435 2269599 := bstep (se 1 (by rfl) ⟨1702199, by rfl⟩ : syracuseStep 2269599 = 3404399) B3404399
theorem B3404405 : Blo 2269435 3404405 := bbase (se 5 (by rfl) ⟨159581, by rfl⟩ : syracuseStep 3404405 = 319163) (by norm_num)
theorem B2269603 : Blo 2269435 2269603 := bstep (se 1 (by rfl) ⟨1702202, by rfl⟩ : syracuseStep 2269603 = 3404405) B3404405
theorem B4308709 : Blo 2269435 4308709 := bbase (se 4 (by rfl) ⟨403941, by rfl⟩ : syracuseStep 4308709 = 807883) (by norm_num)
theorem B5744945 : Blo 2269435 5744945 := bstep (se 2 (by rfl) ⟨2154354, by rfl⟩ : syracuseStep 5744945 = 4308709) B4308709
theorem B3829963 : Blo 2269435 3829963 := bstep (se 1 (by rfl) ⟨2872472, by rfl⟩ : syracuseStep 3829963 = 5744945) B5744945
theorem B5106617 : Blo 2269435 5106617 := bstep (se 2 (by rfl) ⟨1914981, by rfl⟩ : syracuseStep 5106617 = 3829963) B3829963
theorem B3404411 : Blo 2269435 3404411 := bstep (se 1 (by rfl) ⟨2553308, by rfl⟩ : syracuseStep 3404411 = 5106617) B5106617
theorem B2269607 : Blo 2269435 2269607 := bstep (se 1 (by rfl) ⟨1702205, by rfl⟩ : syracuseStep 2269607 = 3404411) B3404411
theorem B2553313 : Blo 2269435 2553313 := bbase (se 2 (by rfl) ⟨957492, by rfl⟩ : syracuseStep 2553313 = 1914985) (by norm_num)
theorem B3404417 : Blo 2269435 3404417 := bstep (se 2 (by rfl) ⟨1276656, by rfl⟩ : syracuseStep 3404417 = 2553313) B2553313
theorem B2269611 : Blo 2269435 2269611 := bstep (se 1 (by rfl) ⟨1702208, by rfl⟩ : syracuseStep 2269611 = 3404417) B3404417
theorem B5744965 : Blo 2269435 5744965 := bbase (se 4 (by rfl) ⟨538590, by rfl⟩ : syracuseStep 5744965 = 1077181) (by norm_num)
theorem B7659953 : Blo 2269435 7659953 := bstep (se 2 (by rfl) ⟨2872482, by rfl⟩ : syracuseStep 7659953 = 5744965) B5744965
theorem B5106635 : Blo 2269435 5106635 := bstep (se 1 (by rfl) ⟨3829976, by rfl⟩ : syracuseStep 5106635 = 7659953) B7659953
theorem B3404423 : Blo 2269435 3404423 := bstep (se 1 (by rfl) ⟨2553317, by rfl⟩ : syracuseStep 3404423 = 5106635) B5106635
theorem B2269615 : Blo 2269435 2269615 := bstep (se 1 (by rfl) ⟨1702211, by rfl⟩ : syracuseStep 2269615 = 3404423) B3404423
theorem B3404429 : Blo 2269435 3404429 := bbase (se 3 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 3404429 = 1276661) (by norm_num)
theorem B2269619 : Blo 2269435 2269619 := bstep (se 1 (by rfl) ⟨1702214, by rfl⟩ : syracuseStep 2269619 = 3404429) B3404429
theorem B5106653 : Blo 2269435 5106653 := bbase (se 3 (by rfl) ⟨957497, by rfl⟩ : syracuseStep 5106653 = 1914995) (by norm_num)
theorem B3404435 : Blo 2269435 3404435 := bstep (se 1 (by rfl) ⟨2553326, by rfl⟩ : syracuseStep 3404435 = 5106653) B5106653
theorem B2269623 : Blo 2269435 2269623 := bstep (se 1 (by rfl) ⟨1702217, by rfl⟩ : syracuseStep 2269623 = 3404435) B3404435
theorem B3829997 : Blo 2269435 3829997 := bbase (se 3 (by rfl) ⟨718124, by rfl⟩ : syracuseStep 3829997 = 1436249) (by norm_num)
theorem B2553331 : Blo 2269435 2553331 := bstep (se 1 (by rfl) ⟨1914998, by rfl⟩ : syracuseStep 2553331 = 3829997) B3829997
theorem B3404441 : Blo 2269435 3404441 := bstep (se 2 (by rfl) ⟨1276665, by rfl⟩ : syracuseStep 3404441 = 2553331) B2553331
theorem B2269627 : Blo 2269435 2269627 := bstep (se 1 (by rfl) ⟨1702220, by rfl⟩ : syracuseStep 2269627 = 3404441) B3404441
theorem B22110677 : Blo 2269435 22110677 := bbase (se 7 (by rfl) ⟨259109, by rfl⟩ : syracuseStep 22110677 = 518219) (by norm_num)
theorem B14740451 : Blo 2269435 14740451 := bstep (se 1 (by rfl) ⟨11055338, by rfl⟩ : syracuseStep 14740451 = 22110677) B22110677
theorem B9826967 : Blo 2269435 9826967 := bstep (se 1 (by rfl) ⟨7370225, by rfl⟩ : syracuseStep 9826967 = 14740451) B14740451
theorem B26205245 : Blo 2269435 26205245 := bstep (se 3 (by rfl) ⟨4913483, by rfl⟩ : syracuseStep 26205245 = 9826967) B9826967
theorem B17470163 : Blo 2269435 17470163 := bstep (se 1 (by rfl) ⟨13102622, by rfl⟩ : syracuseStep 17470163 = 26205245) B26205245
theorem B11646775 : Blo 2269435 11646775 := bstep (se 1 (by rfl) ⟨8735081, by rfl⟩ : syracuseStep 11646775 = 17470163) B17470163
theorem B15529033 : Blo 2269435 15529033 := bstep (se 2 (by rfl) ⟨5823387, by rfl⟩ : syracuseStep 15529033 = 11646775) B11646775
theorem B20705377 : Blo 2269435 20705377 := bstep (se 2 (by rfl) ⟨7764516, by rfl⟩ : syracuseStep 20705377 = 15529033) B15529033
theorem B27607169 : Blo 2269435 27607169 := bstep (se 2 (by rfl) ⟨10352688, by rfl⟩ : syracuseStep 27607169 = 20705377) B20705377
theorem B18404779 : Blo 2269435 18404779 := bstep (se 1 (by rfl) ⟨13803584, by rfl⟩ : syracuseStep 18404779 = 27607169) B27607169
theorem B24539705 : Blo 2269435 24539705 := bstep (se 2 (by rfl) ⟨9202389, by rfl⟩ : syracuseStep 24539705 = 18404779) B18404779
theorem B16359803 : Blo 2269435 16359803 := bstep (se 1 (by rfl) ⟨12269852, by rfl⟩ : syracuseStep 16359803 = 24539705) B24539705
theorem B10906535 : Blo 2269435 10906535 := bstep (se 1 (by rfl) ⟨8179901, by rfl⟩ : syracuseStep 10906535 = 16359803) B16359803
theorem B29084093 : Blo 2269435 29084093 := bstep (se 3 (by rfl) ⟨5453267, by rfl⟩ : syracuseStep 29084093 = 10906535) B10906535
theorem B19389395 : Blo 2269435 19389395 := bstep (se 1 (by rfl) ⟨14542046, by rfl⟩ : syracuseStep 19389395 = 29084093) B29084093
theorem B12926263 : Blo 2269435 12926263 := bstep (se 1 (by rfl) ⟨9694697, by rfl⟩ : syracuseStep 12926263 = 19389395) B19389395
theorem B17235017 : Blo 2269435 17235017 := bstep (se 2 (by rfl) ⟨6463131, by rfl⟩ : syracuseStep 17235017 = 12926263) B12926263
theorem B11490011 : Blo 2269435 11490011 := bstep (se 1 (by rfl) ⟨8617508, by rfl⟩ : syracuseStep 11490011 = 17235017) B17235017
theorem B7660007 : Blo 2269435 7660007 := bstep (se 1 (by rfl) ⟨5745005, by rfl⟩ : syracuseStep 7660007 = 11490011) B11490011
theorem B5106671 : Blo 2269435 5106671 := bstep (se 1 (by rfl) ⟨3830003, by rfl⟩ : syracuseStep 5106671 = 7660007) B7660007
theorem B3404447 : Blo 2269435 3404447 := bstep (se 1 (by rfl) ⟨2553335, by rfl⟩ : syracuseStep 3404447 = 5106671) B5106671
theorem B2269631 : Blo 2269435 2269631 := bstep (se 1 (by rfl) ⟨1702223, by rfl⟩ : syracuseStep 2269631 = 3404447) B3404447
theorem B3404453 : Blo 2269435 3404453 := bbase (se 4 (by rfl) ⟨319167, by rfl⟩ : syracuseStep 3404453 = 638335) (by norm_num)
theorem B2269635 : Blo 2269435 2269635 := bstep (se 1 (by rfl) ⟨1702226, by rfl⟩ : syracuseStep 2269635 = 3404453) B3404453
theorem B2872513 : Blo 2269435 2872513 := bbase (se 2 (by rfl) ⟨1077192, by rfl⟩ : syracuseStep 2872513 = 2154385) (by norm_num)
theorem B3830017 : Blo 2269435 3830017 := bstep (se 2 (by rfl) ⟨1436256, by rfl⟩ : syracuseStep 3830017 = 2872513) B2872513
theorem B5106689 : Blo 2269435 5106689 := bstep (se 2 (by rfl) ⟨1915008, by rfl⟩ : syracuseStep 5106689 = 3830017) B3830017
theorem B3404459 : Blo 2269435 3404459 := bstep (se 1 (by rfl) ⟨2553344, by rfl⟩ : syracuseStep 3404459 = 5106689) B5106689
theorem B2269639 : Blo 2269435 2269639 := bstep (se 1 (by rfl) ⟨1702229, by rfl⟩ : syracuseStep 2269639 = 3404459) B3404459
theorem B2553349 : Blo 2269435 2553349 := bbase (se 4 (by rfl) ⟨239376, by rfl⟩ : syracuseStep 2553349 = 478753) (by norm_num)
theorem B3404465 : Blo 2269435 3404465 := bstep (se 2 (by rfl) ⟨1276674, by rfl⟩ : syracuseStep 3404465 = 2553349) B2553349
theorem B2269643 : Blo 2269435 2269643 := bstep (se 1 (by rfl) ⟨1702232, by rfl⟩ : syracuseStep 2269643 = 3404465) B3404465
theorem B3231589 : Blo 2269435 3231589 := bbase (se 4 (by rfl) ⟨302961, by rfl⟩ : syracuseStep 3231589 = 605923) (by norm_num)
theorem B4308785 : Blo 2269435 4308785 := bstep (se 2 (by rfl) ⟨1615794, by rfl⟩ : syracuseStep 4308785 = 3231589) B3231589
theorem B2872523 : Blo 2269435 2872523 := bstep (se 1 (by rfl) ⟨2154392, by rfl⟩ : syracuseStep 2872523 = 4308785) B4308785
theorem B7660061 : Blo 2269435 7660061 := bstep (se 3 (by rfl) ⟨1436261, by rfl⟩ : syracuseStep 7660061 = 2872523) B2872523
theorem B5106707 : Blo 2269435 5106707 := bstep (se 1 (by rfl) ⟨3830030, by rfl⟩ : syracuseStep 5106707 = 7660061) B7660061
theorem B3404471 : Blo 2269435 3404471 := bstep (se 1 (by rfl) ⟨2553353, by rfl⟩ : syracuseStep 3404471 = 5106707) B5106707
theorem B2269647 : Blo 2269435 2269647 := bstep (se 1 (by rfl) ⟨1702235, by rfl⟩ : syracuseStep 2269647 = 3404471) B3404471
theorem B3404477 : Blo 2269435 3404477 := bbase (se 3 (by rfl) ⟨638339, by rfl⟩ : syracuseStep 3404477 = 1276679) (by norm_num)
theorem B2269651 : Blo 2269435 2269651 := bstep (se 1 (by rfl) ⟨1702238, by rfl⟩ : syracuseStep 2269651 = 3404477) B3404477
theorem B5106725 : Blo 2269435 5106725 := bbase (se 4 (by rfl) ⟨478755, by rfl⟩ : syracuseStep 5106725 = 957511) (by norm_num)
theorem B3404483 : Blo 2269435 3404483 := bstep (se 1 (by rfl) ⟨2553362, by rfl⟩ : syracuseStep 3404483 = 5106725) B5106725
theorem B2269655 : Blo 2269435 2269655 := bstep (se 1 (by rfl) ⟨1702241, by rfl⟩ : syracuseStep 2269655 = 3404483) B3404483
theorem B5745077 : Blo 2269435 5745077 := bbase (se 5 (by rfl) ⟨269300, by rfl⟩ : syracuseStep 5745077 = 538601) (by norm_num)
theorem B3830051 : Blo 2269435 3830051 := bstep (se 1 (by rfl) ⟨2872538, by rfl⟩ : syracuseStep 3830051 = 5745077) B5745077
theorem B2553367 : Blo 2269435 2553367 := bstep (se 1 (by rfl) ⟨1915025, by rfl⟩ : syracuseStep 2553367 = 3830051) B3830051
theorem B3404489 : Blo 2269435 3404489 := bstep (se 2 (by rfl) ⟨1276683, by rfl⟩ : syracuseStep 3404489 = 2553367) B2553367
theorem B2269659 : Blo 2269435 2269659 := bstep (se 1 (by rfl) ⟨1702244, by rfl⟩ : syracuseStep 2269659 = 3404489) B3404489
theorem B4601261 : Blo 2269435 4601261 := bbase (se 3 (by rfl) ⟨862736, by rfl⟩ : syracuseStep 4601261 = 1725473) (by norm_num)
theorem B3067507 : Blo 2269435 3067507 := bstep (se 1 (by rfl) ⟨2300630, by rfl⟩ : syracuseStep 3067507 = 4601261) B4601261
theorem B4090009 : Blo 2269435 4090009 := bstep (se 2 (by rfl) ⟨1533753, by rfl⟩ : syracuseStep 4090009 = 3067507) B3067507
theorem B5453345 : Blo 2269435 5453345 := bstep (se 2 (by rfl) ⟨2045004, by rfl⟩ : syracuseStep 5453345 = 4090009) B4090009
theorem B14542253 : Blo 2269435 14542253 := bstep (se 3 (by rfl) ⟨2726672, by rfl⟩ : syracuseStep 14542253 = 5453345) B5453345
theorem B9694835 : Blo 2269435 9694835 := bstep (se 1 (by rfl) ⟨7271126, by rfl⟩ : syracuseStep 9694835 = 14542253) B14542253
theorem B6463223 : Blo 2269435 6463223 := bstep (se 1 (by rfl) ⟨4847417, by rfl⟩ : syracuseStep 6463223 = 9694835) B9694835
theorem B4308815 : Blo 2269435 4308815 := bstep (se 1 (by rfl) ⟨3231611, by rfl⟩ : syracuseStep 4308815 = 6463223) B6463223
theorem B11490173 : Blo 2269435 11490173 := bstep (se 3 (by rfl) ⟨2154407, by rfl⟩ : syracuseStep 11490173 = 4308815) B4308815
theorem B7660115 : Blo 2269435 7660115 := bstep (se 1 (by rfl) ⟨5745086, by rfl⟩ : syracuseStep 7660115 = 11490173) B11490173
theorem B5106743 : Blo 2269435 5106743 := bstep (se 1 (by rfl) ⟨3830057, by rfl⟩ : syracuseStep 5106743 = 7660115) B7660115
theorem B3404495 : Blo 2269435 3404495 := bstep (se 1 (by rfl) ⟨2553371, by rfl⟩ : syracuseStep 3404495 = 5106743) B5106743
theorem B2269663 : Blo 2269435 2269663 := bstep (se 1 (by rfl) ⟨1702247, by rfl⟩ : syracuseStep 2269663 = 3404495) B3404495
theorem B3404501 : Blo 2269435 3404501 := bbase (se 7 (by rfl) ⟨39896, by rfl⟩ : syracuseStep 3404501 = 79793) (by norm_num)
theorem B2269667 : Blo 2269435 2269667 := bstep (se 1 (by rfl) ⟨1702250, by rfl⟩ : syracuseStep 2269667 = 3404501) B3404501
theorem B5453365 : Blo 2269435 5453365 := bbase (se 5 (by rfl) ⟨255626, by rfl⟩ : syracuseStep 5453365 = 511253) (by norm_num)
theorem B7271153 : Blo 2269435 7271153 := bstep (se 2 (by rfl) ⟨2726682, by rfl⟩ : syracuseStep 7271153 = 5453365) B5453365
theorem B4847435 : Blo 2269435 4847435 := bstep (se 1 (by rfl) ⟨3635576, by rfl⟩ : syracuseStep 4847435 = 7271153) B7271153
theorem B3231623 : Blo 2269435 3231623 := bstep (se 1 (by rfl) ⟨2423717, by rfl⟩ : syracuseStep 3231623 = 4847435) B4847435
theorem B8617661 : Blo 2269435 8617661 := bstep (se 3 (by rfl) ⟨1615811, by rfl⟩ : syracuseStep 8617661 = 3231623) B3231623
theorem B5745107 : Blo 2269435 5745107 := bstep (se 1 (by rfl) ⟨4308830, by rfl⟩ : syracuseStep 5745107 = 8617661) B8617661
theorem B3830071 : Blo 2269435 3830071 := bstep (se 1 (by rfl) ⟨2872553, by rfl⟩ : syracuseStep 3830071 = 5745107) B5745107
theorem B5106761 : Blo 2269435 5106761 := bstep (se 2 (by rfl) ⟨1915035, by rfl⟩ : syracuseStep 5106761 = 3830071) B3830071
theorem B3404507 : Blo 2269435 3404507 := bstep (se 1 (by rfl) ⟨2553380, by rfl⟩ : syracuseStep 3404507 = 5106761) B5106761
theorem B2269671 : Blo 2269435 2269671 := bstep (se 1 (by rfl) ⟨1702253, by rfl⟩ : syracuseStep 2269671 = 3404507) B3404507
theorem B2553385 : Blo 2269435 2553385 := bbase (se 2 (by rfl) ⟨957519, by rfl⟩ : syracuseStep 2553385 = 1915039) (by norm_num)
theorem B3404513 : Blo 2269435 3404513 := bstep (se 2 (by rfl) ⟨1276692, by rfl⟩ : syracuseStep 3404513 = 2553385) B2553385
theorem B2269675 : Blo 2269435 2269675 := bstep (se 1 (by rfl) ⟨1702256, by rfl⟩ : syracuseStep 2269675 = 3404513) B3404513
theorem B3882341 : Blo 2269435 3882341 := bbase (se 4 (by rfl) ⟨363969, by rfl⟩ : syracuseStep 3882341 = 727939) (by norm_num)
theorem B10352909 : Blo 2269435 10352909 := bstep (se 3 (by rfl) ⟨1941170, by rfl⟩ : syracuseStep 10352909 = 3882341) B3882341
theorem B6901939 : Blo 2269435 6901939 := bstep (se 1 (by rfl) ⟨5176454, by rfl⟩ : syracuseStep 6901939 = 10352909) B10352909
theorem B9202585 : Blo 2269435 9202585 := bstep (se 2 (by rfl) ⟨3450969, by rfl⟩ : syracuseStep 9202585 = 6901939) B6901939
theorem B12270113 : Blo 2269435 12270113 := bstep (se 2 (by rfl) ⟨4601292, by rfl⟩ : syracuseStep 12270113 = 9202585) B9202585
theorem B8180075 : Blo 2269435 8180075 := bstep (se 1 (by rfl) ⟨6135056, by rfl⟩ : syracuseStep 8180075 = 12270113) B12270113
theorem B21813533 : Blo 2269435 21813533 := bstep (se 3 (by rfl) ⟨4090037, by rfl⟩ : syracuseStep 21813533 = 8180075) B8180075
theorem B14542355 : Blo 2269435 14542355 := bstep (se 1 (by rfl) ⟨10906766, by rfl⟩ : syracuseStep 14542355 = 21813533) B21813533
theorem B9694903 : Blo 2269435 9694903 := bstep (se 1 (by rfl) ⟨7271177, by rfl⟩ : syracuseStep 9694903 = 14542355) B14542355
theorem B12926537 : Blo 2269435 12926537 := bstep (se 2 (by rfl) ⟨4847451, by rfl⟩ : syracuseStep 12926537 = 9694903) B9694903
theorem B8617691 : Blo 2269435 8617691 := bstep (se 1 (by rfl) ⟨6463268, by rfl⟩ : syracuseStep 8617691 = 12926537) B12926537
theorem B5745127 : Blo 2269435 5745127 := bstep (se 1 (by rfl) ⟨4308845, by rfl⟩ : syracuseStep 5745127 = 8617691) B8617691
theorem B7660169 : Blo 2269435 7660169 := bstep (se 2 (by rfl) ⟨2872563, by rfl⟩ : syracuseStep 7660169 = 5745127) B5745127
theorem B5106779 : Blo 2269435 5106779 := bstep (se 1 (by rfl) ⟨3830084, by rfl⟩ : syracuseStep 5106779 = 7660169) B7660169
theorem B3404519 : Blo 2269435 3404519 := bstep (se 1 (by rfl) ⟨2553389, by rfl⟩ : syracuseStep 3404519 = 5106779) B5106779
theorem B2269679 : Blo 2269435 2269679 := bstep (se 1 (by rfl) ⟨1702259, by rfl⟩ : syracuseStep 2269679 = 3404519) B3404519
theorem B3404525 : Blo 2269435 3404525 := bbase (se 3 (by rfl) ⟨638348, by rfl⟩ : syracuseStep 3404525 = 1276697) (by norm_num)
theorem B2269683 : Blo 2269435 2269683 := bstep (se 1 (by rfl) ⟨1702262, by rfl⟩ : syracuseStep 2269683 = 3404525) B3404525
theorem B5106797 : Blo 2269435 5106797 := bbase (se 3 (by rfl) ⟨957524, by rfl⟩ : syracuseStep 5106797 = 1915049) (by norm_num)
theorem B3404531 : Blo 2269435 3404531 := bstep (se 1 (by rfl) ⟨2553398, by rfl⟩ : syracuseStep 3404531 = 5106797) B5106797
theorem B2269687 : Blo 2269435 2269687 := bstep (se 1 (by rfl) ⟨1702265, by rfl⟩ : syracuseStep 2269687 = 3404531) B3404531
theorem B4308869 : Blo 2269435 4308869 := bbase (se 4 (by rfl) ⟨403956, by rfl⟩ : syracuseStep 4308869 = 807913) (by norm_num)
theorem B2872579 : Blo 2269435 2872579 := bstep (se 1 (by rfl) ⟨2154434, by rfl⟩ : syracuseStep 2872579 = 4308869) B4308869
theorem B3830105 : Blo 2269435 3830105 := bstep (se 2 (by rfl) ⟨1436289, by rfl⟩ : syracuseStep 3830105 = 2872579) B2872579
theorem B2553403 : Blo 2269435 2553403 := bstep (se 1 (by rfl) ⟨1915052, by rfl⟩ : syracuseStep 2553403 = 3830105) B3830105
theorem B3404537 : Blo 2269435 3404537 := bstep (se 2 (by rfl) ⟨1276701, by rfl⟩ : syracuseStep 3404537 = 2553403) B2553403
theorem B2269691 : Blo 2269435 2269691 := bstep (se 1 (by rfl) ⟨1702268, by rfl⟩ : syracuseStep 2269691 = 3404537) B3404537
theorem B41976917 : Blo 2269435 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B27984611 : Blo 2269435 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B18656407 : Blo 2269435 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B24875209 : Blo 2269435 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B33166945 : Blo 2269435 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B44222593 : Blo 2269435 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B58963457 : Blo 2269435 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B39308971 : Blo 2269435 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B52411961 : Blo 2269435 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B34941307 : Blo 2269435 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B46588409 : Blo 2269435 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B31058939 : Blo 2269435 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B20705959 : Blo 2269435 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B110431781 : Blo 2269435 110431781 := bstep (se 4 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 110431781 = 20705959) B20705959
theorem B73621187 : Blo 2269435 73621187 := bstep (se 1 (by rfl) ⟨55215890, by rfl⟩ : syracuseStep 73621187 = 110431781) B110431781
theorem B49080791 : Blo 2269435 49080791 := bstep (se 1 (by rfl) ⟨36810593, by rfl⟩ : syracuseStep 49080791 = 73621187) B73621187
theorem B32720527 : Blo 2269435 32720527 := bstep (se 1 (by rfl) ⟨24540395, by rfl⟩ : syracuseStep 32720527 = 49080791) B49080791
theorem B43627369 : Blo 2269435 43627369 := bstep (se 2 (by rfl) ⟨16360263, by rfl⟩ : syracuseStep 43627369 = 32720527) B32720527
theorem B58169825 : Blo 2269435 58169825 := bstep (se 2 (by rfl) ⟨21813684, by rfl⟩ : syracuseStep 58169825 = 43627369) B43627369
theorem B38779883 : Blo 2269435 38779883 := bstep (se 1 (by rfl) ⟨29084912, by rfl⟩ : syracuseStep 38779883 = 58169825) B58169825
theorem B25853255 : Blo 2269435 25853255 := bstep (se 1 (by rfl) ⟨19389941, by rfl⟩ : syracuseStep 25853255 = 38779883) B38779883
theorem B17235503 : Blo 2269435 17235503 := bstep (se 1 (by rfl) ⟨12926627, by rfl⟩ : syracuseStep 17235503 = 25853255) B25853255
theorem B11490335 : Blo 2269435 11490335 := bstep (se 1 (by rfl) ⟨8617751, by rfl⟩ : syracuseStep 11490335 = 17235503) B17235503
theorem B7660223 : Blo 2269435 7660223 := bstep (se 1 (by rfl) ⟨5745167, by rfl⟩ : syracuseStep 7660223 = 11490335) B11490335
theorem B5106815 : Blo 2269435 5106815 := bstep (se 1 (by rfl) ⟨3830111, by rfl⟩ : syracuseStep 5106815 = 7660223) B7660223
theorem B3404543 : Blo 2269435 3404543 := bstep (se 1 (by rfl) ⟨2553407, by rfl⟩ : syracuseStep 3404543 = 5106815) B5106815
theorem B2269695 : Blo 2269435 2269695 := bstep (se 1 (by rfl) ⟨1702271, by rfl⟩ : syracuseStep 2269695 = 3404543) B3404543
theorem B3404549 : Blo 2269435 3404549 := bbase (se 4 (by rfl) ⟨319176, by rfl⟩ : syracuseStep 3404549 = 638353) (by norm_num)
theorem B2269699 : Blo 2269435 2269699 := bstep (se 1 (by rfl) ⟨1702274, by rfl⟩ : syracuseStep 2269699 = 3404549) B3404549
theorem B3830125 : Blo 2269435 3830125 := bbase (se 3 (by rfl) ⟨718148, by rfl⟩ : syracuseStep 3830125 = 1436297) (by norm_num)
theorem B5106833 : Blo 2269435 5106833 := bstep (se 2 (by rfl) ⟨1915062, by rfl⟩ : syracuseStep 5106833 = 3830125) B3830125
theorem B3404555 : Blo 2269435 3404555 := bstep (se 1 (by rfl) ⟨2553416, by rfl⟩ : syracuseStep 3404555 = 5106833) B5106833
theorem B2269703 : Blo 2269435 2269703 := bstep (se 1 (by rfl) ⟨1702277, by rfl⟩ : syracuseStep 2269703 = 3404555) B3404555
theorem B2553421 : Blo 2269435 2553421 := bbase (se 3 (by rfl) ⟨478766, by rfl⟩ : syracuseStep 2553421 = 957533) (by norm_num)
theorem B3404561 : Blo 2269435 3404561 := bstep (se 2 (by rfl) ⟨1276710, by rfl⟩ : syracuseStep 3404561 = 2553421) B2553421
theorem B2269707 : Blo 2269435 2269707 := bstep (se 1 (by rfl) ⟨1702280, by rfl⟩ : syracuseStep 2269707 = 3404561) B3404561
theorem B7660277 : Blo 2269435 7660277 := bbase (se 5 (by rfl) ⟨359075, by rfl⟩ : syracuseStep 7660277 = 718151) (by norm_num)
theorem B5106851 : Blo 2269435 5106851 := bstep (se 1 (by rfl) ⟨3830138, by rfl⟩ : syracuseStep 5106851 = 7660277) B7660277
theorem B3404567 : Blo 2269435 3404567 := bstep (se 1 (by rfl) ⟨2553425, by rfl⟩ : syracuseStep 3404567 = 5106851) B5106851
theorem B2269711 : Blo 2269435 2269711 := bstep (se 1 (by rfl) ⟨1702283, by rfl⟩ : syracuseStep 2269711 = 3404567) B3404567
theorem B3404573 : Blo 2269435 3404573 := bbase (se 3 (by rfl) ⟨638357, by rfl⟩ : syracuseStep 3404573 = 1276715) (by norm_num)
theorem B2269715 : Blo 2269435 2269715 := bstep (se 1 (by rfl) ⟨1702286, by rfl⟩ : syracuseStep 2269715 = 3404573) B3404573
theorem B5106869 : Blo 2269435 5106869 := bbase (se 5 (by rfl) ⟨239384, by rfl⟩ : syracuseStep 5106869 = 478769) (by norm_num)
theorem B3404579 : Blo 2269435 3404579 := bstep (se 1 (by rfl) ⟨2553434, by rfl⟩ : syracuseStep 3404579 = 5106869) B5106869
theorem B2269719 : Blo 2269435 2269719 := bstep (se 1 (by rfl) ⟨1702289, by rfl⟩ : syracuseStep 2269719 = 3404579) B3404579
theorem B2423773 : Blo 2269435 2423773 := bbase (se 3 (by rfl) ⟨454457, by rfl⟩ : syracuseStep 2423773 = 908915) (by norm_num)
theorem B12926789 : Blo 2269435 12926789 := bstep (se 4 (by rfl) ⟨1211886, by rfl⟩ : syracuseStep 12926789 = 2423773) B2423773
theorem B8617859 : Blo 2269435 8617859 := bstep (se 1 (by rfl) ⟨6463394, by rfl⟩ : syracuseStep 8617859 = 12926789) B12926789
theorem B5745239 : Blo 2269435 5745239 := bstep (se 1 (by rfl) ⟨4308929, by rfl⟩ : syracuseStep 5745239 = 8617859) B8617859
theorem B3830159 : Blo 2269435 3830159 := bstep (se 1 (by rfl) ⟨2872619, by rfl⟩ : syracuseStep 3830159 = 5745239) B5745239
theorem B2553439 : Blo 2269435 2553439 := bstep (se 1 (by rfl) ⟨1915079, by rfl⟩ : syracuseStep 2553439 = 3830159) B3830159
theorem B3404585 : Blo 2269435 3404585 := bstep (se 2 (by rfl) ⟨1276719, by rfl⟩ : syracuseStep 3404585 = 2553439) B2553439
theorem B2269723 : Blo 2269435 2269723 := bstep (se 1 (by rfl) ⟨1702292, by rfl⟩ : syracuseStep 2269723 = 3404585) B3404585
theorem B2423777 : Blo 2269435 2423777 := bbase (se 2 (by rfl) ⟨908916, by rfl⟩ : syracuseStep 2423777 = 1817833) (by norm_num)
theorem B6463405 : Blo 2269435 6463405 := bstep (se 3 (by rfl) ⟨1211888, by rfl⟩ : syracuseStep 6463405 = 2423777) B2423777
theorem B8617873 : Blo 2269435 8617873 := bstep (se 2 (by rfl) ⟨3231702, by rfl⟩ : syracuseStep 8617873 = 6463405) B6463405
theorem B11490497 : Blo 2269435 11490497 := bstep (se 2 (by rfl) ⟨4308936, by rfl⟩ : syracuseStep 11490497 = 8617873) B8617873
theorem B7660331 : Blo 2269435 7660331 := bstep (se 1 (by rfl) ⟨5745248, by rfl⟩ : syracuseStep 7660331 = 11490497) B11490497
theorem B5106887 : Blo 2269435 5106887 := bstep (se 1 (by rfl) ⟨3830165, by rfl⟩ : syracuseStep 5106887 = 7660331) B7660331
theorem B3404591 : Blo 2269435 3404591 := bstep (se 1 (by rfl) ⟨2553443, by rfl⟩ : syracuseStep 3404591 = 5106887) B5106887
theorem B2269727 : Blo 2269435 2269727 := bstep (se 1 (by rfl) ⟨1702295, by rfl⟩ : syracuseStep 2269727 = 3404591) B3404591
theorem B3404597 : Blo 2269435 3404597 := bbase (se 5 (by rfl) ⟨159590, by rfl⟩ : syracuseStep 3404597 = 319181) (by norm_num)
theorem B2269731 : Blo 2269435 2269731 := bstep (se 1 (by rfl) ⟨1702298, by rfl⟩ : syracuseStep 2269731 = 3404597) B3404597
theorem B5745269 : Blo 2269435 5745269 := bbase (se 5 (by rfl) ⟨269309, by rfl⟩ : syracuseStep 5745269 = 538619) (by norm_num)
theorem B3830179 : Blo 2269435 3830179 := bstep (se 1 (by rfl) ⟨2872634, by rfl⟩ : syracuseStep 3830179 = 5745269) B5745269
theorem B5106905 : Blo 2269435 5106905 := bstep (se 2 (by rfl) ⟨1915089, by rfl⟩ : syracuseStep 5106905 = 3830179) B3830179
theorem B3404603 : Blo 2269435 3404603 := bstep (se 1 (by rfl) ⟨2553452, by rfl⟩ : syracuseStep 3404603 = 5106905) B5106905
theorem B2269735 : Blo 2269435 2269735 := bstep (se 1 (by rfl) ⟨1702301, by rfl⟩ : syracuseStep 2269735 = 3404603) B3404603
theorem B2553457 : Blo 2269435 2553457 := bbase (se 2 (by rfl) ⟨957546, by rfl⟩ : syracuseStep 2553457 = 1915093) (by norm_num)
theorem B3404609 : Blo 2269435 3404609 := bstep (se 2 (by rfl) ⟨1276728, by rfl⟩ : syracuseStep 3404609 = 2553457) B2553457
theorem B2269739 : Blo 2269435 2269739 := bstep (se 1 (by rfl) ⟨1702304, by rfl⟩ : syracuseStep 2269739 = 3404609) B3404609
theorem B5823677 : Blo 2269435 5823677 := bbase (se 3 (by rfl) ⟨1091939, by rfl⟩ : syracuseStep 5823677 = 2183879) (by norm_num)
theorem B15529805 : Blo 2269435 15529805 := bstep (se 3 (by rfl) ⟨2911838, by rfl⟩ : syracuseStep 15529805 = 5823677) B5823677
theorem B10353203 : Blo 2269435 10353203 := bstep (se 1 (by rfl) ⟨7764902, by rfl⟩ : syracuseStep 10353203 = 15529805) B15529805
theorem B6902135 : Blo 2269435 6902135 := bstep (se 1 (by rfl) ⟨5176601, by rfl⟩ : syracuseStep 6902135 = 10353203) B10353203
theorem B4601423 : Blo 2269435 4601423 := bstep (se 1 (by rfl) ⟨3451067, by rfl⟩ : syracuseStep 4601423 = 6902135) B6902135
theorem B3067615 : Blo 2269435 3067615 := bstep (se 1 (by rfl) ⟨2300711, by rfl⟩ : syracuseStep 3067615 = 4601423) B4601423
theorem B16360613 : Blo 2269435 16360613 := bstep (se 4 (by rfl) ⟨1533807, by rfl⟩ : syracuseStep 16360613 = 3067615) B3067615
theorem B10907075 : Blo 2269435 10907075 := bstep (se 1 (by rfl) ⟨8180306, by rfl⟩ : syracuseStep 10907075 = 16360613) B16360613
theorem B7271383 : Blo 2269435 7271383 := bstep (se 1 (by rfl) ⟨5453537, by rfl⟩ : syracuseStep 7271383 = 10907075) B10907075
theorem B9695177 : Blo 2269435 9695177 := bstep (se 2 (by rfl) ⟨3635691, by rfl⟩ : syracuseStep 9695177 = 7271383) B7271383
theorem B6463451 : Blo 2269435 6463451 := bstep (se 1 (by rfl) ⟨4847588, by rfl⟩ : syracuseStep 6463451 = 9695177) B9695177
theorem B4308967 : Blo 2269435 4308967 := bstep (se 1 (by rfl) ⟨3231725, by rfl⟩ : syracuseStep 4308967 = 6463451) B6463451
theorem B5745289 : Blo 2269435 5745289 := bstep (se 2 (by rfl) ⟨2154483, by rfl⟩ : syracuseStep 5745289 = 4308967) B4308967
theorem B7660385 : Blo 2269435 7660385 := bstep (se 2 (by rfl) ⟨2872644, by rfl⟩ : syracuseStep 7660385 = 5745289) B5745289
theorem B5106923 : Blo 2269435 5106923 := bstep (se 1 (by rfl) ⟨3830192, by rfl⟩ : syracuseStep 5106923 = 7660385) B7660385
theorem B3404615 : Blo 2269435 3404615 := bstep (se 1 (by rfl) ⟨2553461, by rfl⟩ : syracuseStep 3404615 = 5106923) B5106923
theorem B2269743 : Blo 2269435 2269743 := bstep (se 1 (by rfl) ⟨1702307, by rfl⟩ : syracuseStep 2269743 = 3404615) B3404615
theorem B3404621 : Blo 2269435 3404621 := bbase (se 3 (by rfl) ⟨638366, by rfl⟩ : syracuseStep 3404621 = 1276733) (by norm_num)
theorem B2269747 : Blo 2269435 2269747 := bstep (se 1 (by rfl) ⟨1702310, by rfl⟩ : syracuseStep 2269747 = 3404621) B3404621
theorem B5106941 : Blo 2269435 5106941 := bbase (se 3 (by rfl) ⟨957551, by rfl⟩ : syracuseStep 5106941 = 1915103) (by norm_num)
theorem B3404627 : Blo 2269435 3404627 := bstep (se 1 (by rfl) ⟨2553470, by rfl⟩ : syracuseStep 3404627 = 5106941) B5106941
theorem B2269751 : Blo 2269435 2269751 := bstep (se 1 (by rfl) ⟨1702313, by rfl⟩ : syracuseStep 2269751 = 3404627) B3404627
theorem B3830213 : Blo 2269435 3830213 := bbase (se 4 (by rfl) ⟨359082, by rfl⟩ : syracuseStep 3830213 = 718165) (by norm_num)
theorem B2553475 : Blo 2269435 2553475 := bstep (se 1 (by rfl) ⟨1915106, by rfl⟩ : syracuseStep 2553475 = 3830213) B3830213
theorem B3404633 : Blo 2269435 3404633 := bstep (se 2 (by rfl) ⟨1276737, by rfl⟩ : syracuseStep 3404633 = 2553475) B2553475
theorem B2269755 : Blo 2269435 2269755 := bstep (se 1 (by rfl) ⟨1702316, by rfl⟩ : syracuseStep 2269755 = 3404633) B3404633
theorem B17235989 : Blo 2269435 17235989 := bbase (se 6 (by rfl) ⟨403968, by rfl⟩ : syracuseStep 17235989 = 807937) (by norm_num)
theorem B11490659 : Blo 2269435 11490659 := bstep (se 1 (by rfl) ⟨8617994, by rfl⟩ : syracuseStep 11490659 = 17235989) B17235989
theorem B7660439 : Blo 2269435 7660439 := bstep (se 1 (by rfl) ⟨5745329, by rfl⟩ : syracuseStep 7660439 = 11490659) B11490659
theorem B5106959 : Blo 2269435 5106959 := bstep (se 1 (by rfl) ⟨3830219, by rfl⟩ : syracuseStep 5106959 = 7660439) B7660439
theorem B3404639 : Blo 2269435 3404639 := bstep (se 1 (by rfl) ⟨2553479, by rfl⟩ : syracuseStep 3404639 = 5106959) B5106959
theorem B2269759 : Blo 2269435 2269759 := bstep (se 1 (by rfl) ⟨1702319, by rfl⟩ : syracuseStep 2269759 = 3404639) B3404639
theorem B3404645 : Blo 2269435 3404645 := bbase (se 4 (by rfl) ⟨319185, by rfl⟩ : syracuseStep 3404645 = 638371) (by norm_num)
theorem B2269763 : Blo 2269435 2269763 := bstep (se 1 (by rfl) ⟨1702322, by rfl⟩ : syracuseStep 2269763 = 3404645) B3404645
theorem B4309013 : Blo 2269435 4309013 := bbase (se 6 (by rfl) ⟨100992, by rfl⟩ : syracuseStep 4309013 = 201985) (by norm_num)
theorem B2872675 : Blo 2269435 2872675 := bstep (se 1 (by rfl) ⟨2154506, by rfl⟩ : syracuseStep 2872675 = 4309013) B4309013
theorem B3830233 : Blo 2269435 3830233 := bstep (se 2 (by rfl) ⟨1436337, by rfl⟩ : syracuseStep 3830233 = 2872675) B2872675
theorem B5106977 : Blo 2269435 5106977 := bstep (se 2 (by rfl) ⟨1915116, by rfl⟩ : syracuseStep 5106977 = 3830233) B3830233
theorem B3404651 : Blo 2269435 3404651 := bstep (se 1 (by rfl) ⟨2553488, by rfl⟩ : syracuseStep 3404651 = 5106977) B5106977
theorem B2269767 : Blo 2269435 2269767 := bstep (se 1 (by rfl) ⟨1702325, by rfl⟩ : syracuseStep 2269767 = 3404651) B3404651
theorem B2553493 : Blo 2269435 2553493 := bbase (se 6 (by rfl) ⟨59847, by rfl⟩ : syracuseStep 2553493 = 119695) (by norm_num)
theorem B3404657 : Blo 2269435 3404657 := bstep (se 2 (by rfl) ⟨1276746, by rfl⟩ : syracuseStep 3404657 = 2553493) B2553493
theorem B2269771 : Blo 2269435 2269771 := bstep (se 1 (by rfl) ⟨1702328, by rfl⟩ : syracuseStep 2269771 = 3404657) B3404657
theorem B2872685 : Blo 2269435 2872685 := bbase (se 3 (by rfl) ⟨538628, by rfl⟩ : syracuseStep 2872685 = 1077257) (by norm_num)
theorem B7660493 : Blo 2269435 7660493 := bstep (se 3 (by rfl) ⟨1436342, by rfl⟩ : syracuseStep 7660493 = 2872685) B2872685
theorem B5106995 : Blo 2269435 5106995 := bstep (se 1 (by rfl) ⟨3830246, by rfl⟩ : syracuseStep 5106995 = 7660493) B7660493
theorem B3404663 : Blo 2269435 3404663 := bstep (se 1 (by rfl) ⟨2553497, by rfl⟩ : syracuseStep 3404663 = 5106995) B5106995
theorem B2269775 : Blo 2269435 2269775 := bstep (se 1 (by rfl) ⟨1702331, by rfl⟩ : syracuseStep 2269775 = 3404663) B3404663
theorem B3404669 : Blo 2269435 3404669 := bbase (se 3 (by rfl) ⟨638375, by rfl⟩ : syracuseStep 3404669 = 1276751) (by norm_num)
theorem B2269779 : Blo 2269435 2269779 := bstep (se 1 (by rfl) ⟨1702334, by rfl⟩ : syracuseStep 2269779 = 3404669) B3404669
theorem B5107013 : Blo 2269435 5107013 := bbase (se 4 (by rfl) ⟨478782, by rfl⟩ : syracuseStep 5107013 = 957565) (by norm_num)
theorem B3404675 : Blo 2269435 3404675 := bstep (se 1 (by rfl) ⟨2553506, by rfl⟩ : syracuseStep 3404675 = 5107013) B5107013
theorem B2269783 : Blo 2269435 2269783 := bstep (se 1 (by rfl) ⟨1702337, by rfl⟩ : syracuseStep 2269783 = 3404675) B3404675
theorem B7271525 : Blo 2269435 7271525 := bbase (se 4 (by rfl) ⟨681705, by rfl⟩ : syracuseStep 7271525 = 1363411) (by norm_num)
theorem B4847683 : Blo 2269435 4847683 := bstep (se 1 (by rfl) ⟨3635762, by rfl⟩ : syracuseStep 4847683 = 7271525) B7271525
theorem B6463577 : Blo 2269435 6463577 := bstep (se 2 (by rfl) ⟨2423841, by rfl⟩ : syracuseStep 6463577 = 4847683) B4847683
theorem B4309051 : Blo 2269435 4309051 := bstep (se 1 (by rfl) ⟨3231788, by rfl⟩ : syracuseStep 4309051 = 6463577) B6463577
theorem B5745401 : Blo 2269435 5745401 := bstep (se 2 (by rfl) ⟨2154525, by rfl⟩ : syracuseStep 5745401 = 4309051) B4309051
theorem B3830267 : Blo 2269435 3830267 := bstep (se 1 (by rfl) ⟨2872700, by rfl⟩ : syracuseStep 3830267 = 5745401) B5745401
theorem B2553511 : Blo 2269435 2553511 := bstep (se 1 (by rfl) ⟨1915133, by rfl⟩ : syracuseStep 2553511 = 3830267) B3830267
theorem B3404681 : Blo 2269435 3404681 := bstep (se 2 (by rfl) ⟨1276755, by rfl⟩ : syracuseStep 3404681 = 2553511) B2553511
theorem B2269787 : Blo 2269435 2269787 := bstep (se 1 (by rfl) ⟨1702340, by rfl⟩ : syracuseStep 2269787 = 3404681) B3404681
theorem B11490821 : Blo 2269435 11490821 := bbase (se 4 (by rfl) ⟨1077264, by rfl⟩ : syracuseStep 11490821 = 2154529) (by norm_num)
theorem B7660547 : Blo 2269435 7660547 := bstep (se 1 (by rfl) ⟨5745410, by rfl⟩ : syracuseStep 7660547 = 11490821) B11490821
theorem B5107031 : Blo 2269435 5107031 := bstep (se 1 (by rfl) ⟨3830273, by rfl⟩ : syracuseStep 5107031 = 7660547) B7660547
theorem B3404687 : Blo 2269435 3404687 := bstep (se 1 (by rfl) ⟨2553515, by rfl⟩ : syracuseStep 3404687 = 5107031) B5107031
theorem B2269791 : Blo 2269435 2269791 := bstep (se 1 (by rfl) ⟨1702343, by rfl⟩ : syracuseStep 2269791 = 3404687) B3404687
theorem B3404693 : Blo 2269435 3404693 := bbase (se 6 (by rfl) ⟨79797, by rfl⟩ : syracuseStep 3404693 = 159595) (by norm_num)
theorem B2269795 : Blo 2269435 2269795 := bstep (se 1 (by rfl) ⟨1702346, by rfl⟩ : syracuseStep 2269795 = 3404693) B3404693
theorem B12927221 : Blo 2269435 12927221 := bbase (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) (by norm_num)
theorem B8618147 : Blo 2269435 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B5745431 : Blo 2269435 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B3830287 : Blo 2269435 3830287 := bstep (se 1 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 3830287 = 5745431) B5745431
theorem B5107049 : Blo 2269435 5107049 := bstep (se 2 (by rfl) ⟨1915143, by rfl⟩ : syracuseStep 5107049 = 3830287) B3830287
theorem B3404699 : Blo 2269435 3404699 := bstep (se 1 (by rfl) ⟨2553524, by rfl⟩ : syracuseStep 3404699 = 5107049) B5107049
theorem B2269799 : Blo 2269435 2269799 := bstep (se 1 (by rfl) ⟨1702349, by rfl⟩ : syracuseStep 2269799 = 3404699) B3404699
theorem B2553529 : Blo 2269435 2553529 := bbase (se 2 (by rfl) ⟨957573, by rfl⟩ : syracuseStep 2553529 = 1915147) (by norm_num)
theorem B3404705 : Blo 2269435 3404705 := bstep (se 2 (by rfl) ⟨1276764, by rfl⟩ : syracuseStep 3404705 = 2553529) B2553529
theorem B2269803 : Blo 2269435 2269803 := bstep (se 1 (by rfl) ⟨1702352, by rfl⟩ : syracuseStep 2269803 = 3404705) B3404705
theorem B4847725 : Blo 2269435 4847725 := bbase (se 3 (by rfl) ⟨908948, by rfl⟩ : syracuseStep 4847725 = 1817897) (by norm_num)
theorem B6463633 : Blo 2269435 6463633 := bstep (se 2 (by rfl) ⟨2423862, by rfl⟩ : syracuseStep 6463633 = 4847725) B4847725
theorem B8618177 : Blo 2269435 8618177 := bstep (se 2 (by rfl) ⟨3231816, by rfl⟩ : syracuseStep 8618177 = 6463633) B6463633
theorem B5745451 : Blo 2269435 5745451 := bstep (se 1 (by rfl) ⟨4309088, by rfl⟩ : syracuseStep 5745451 = 8618177) B8618177
theorem B7660601 : Blo 2269435 7660601 := bstep (se 2 (by rfl) ⟨2872725, by rfl⟩ : syracuseStep 7660601 = 5745451) B5745451
theorem B5107067 : Blo 2269435 5107067 := bstep (se 1 (by rfl) ⟨3830300, by rfl⟩ : syracuseStep 5107067 = 7660601) B7660601
theorem B3404711 : Blo 2269435 3404711 := bstep (se 1 (by rfl) ⟨2553533, by rfl⟩ : syracuseStep 3404711 = 5107067) B5107067
theorem B2269807 : Blo 2269435 2269807 := bstep (se 1 (by rfl) ⟨1702355, by rfl⟩ : syracuseStep 2269807 = 3404711) B3404711
theorem B3404717 : Blo 2269435 3404717 := bbase (se 3 (by rfl) ⟨638384, by rfl⟩ : syracuseStep 3404717 = 1276769) (by norm_num)
theorem B2269811 : Blo 2269435 2269811 := bstep (se 1 (by rfl) ⟨1702358, by rfl⟩ : syracuseStep 2269811 = 3404717) B3404717
theorem B5107085 : Blo 2269435 5107085 := bbase (se 3 (by rfl) ⟨957578, by rfl⟩ : syracuseStep 5107085 = 1915157) (by norm_num)
theorem B3404723 : Blo 2269435 3404723 := bstep (se 1 (by rfl) ⟨2553542, by rfl⟩ : syracuseStep 3404723 = 5107085) B5107085
theorem B2269815 : Blo 2269435 2269815 := bstep (se 1 (by rfl) ⟨1702361, by rfl⟩ : syracuseStep 2269815 = 3404723) B3404723
theorem B2872741 : Blo 2269435 2872741 := bbase (se 4 (by rfl) ⟨269319, by rfl⟩ : syracuseStep 2872741 = 538639) (by norm_num)
theorem B3830321 : Blo 2269435 3830321 := bstep (se 2 (by rfl) ⟨1436370, by rfl⟩ : syracuseStep 3830321 = 2872741) B2872741
theorem B2553547 : Blo 2269435 2553547 := bstep (se 1 (by rfl) ⟨1915160, by rfl⟩ : syracuseStep 2553547 = 3830321) B3830321
theorem B3404729 : Blo 2269435 3404729 := bstep (se 2 (by rfl) ⟨1276773, by rfl⟩ : syracuseStep 3404729 = 2553547) B2553547
theorem B2269819 : Blo 2269435 2269819 := bstep (se 1 (by rfl) ⟨1702364, by rfl⟩ : syracuseStep 2269819 = 3404729) B3404729
theorem B6135445 : Blo 2269435 6135445 := bbase (se 6 (by rfl) ⟨143799, by rfl⟩ : syracuseStep 6135445 = 287599) (by norm_num)
theorem B32722373 : Blo 2269435 32722373 := bstep (se 4 (by rfl) ⟨3067722, by rfl⟩ : syracuseStep 32722373 = 6135445) B6135445
theorem B21814915 : Blo 2269435 21814915 := bstep (se 1 (by rfl) ⟨16361186, by rfl⟩ : syracuseStep 21814915 = 32722373) B32722373
theorem B29086553 : Blo 2269435 29086553 := bstep (se 2 (by rfl) ⟨10907457, by rfl⟩ : syracuseStep 29086553 = 21814915) B21814915
theorem B19391035 : Blo 2269435 19391035 := bstep (se 1 (by rfl) ⟨14543276, by rfl⟩ : syracuseStep 19391035 = 29086553) B29086553
theorem B25854713 : Blo 2269435 25854713 := bstep (se 2 (by rfl) ⟨9695517, by rfl⟩ : syracuseStep 25854713 = 19391035) B19391035
theorem B17236475 : Blo 2269435 17236475 := bstep (se 1 (by rfl) ⟨12927356, by rfl⟩ : syracuseStep 17236475 = 25854713) B25854713
theorem B11490983 : Blo 2269435 11490983 := bstep (se 1 (by rfl) ⟨8618237, by rfl⟩ : syracuseStep 11490983 = 17236475) B17236475
theorem B7660655 : Blo 2269435 7660655 := bstep (se 1 (by rfl) ⟨5745491, by rfl⟩ : syracuseStep 7660655 = 11490983) B11490983
theorem B5107103 : Blo 2269435 5107103 := bstep (se 1 (by rfl) ⟨3830327, by rfl⟩ : syracuseStep 5107103 = 7660655) B7660655
theorem B3404735 : Blo 2269435 3404735 := bstep (se 1 (by rfl) ⟨2553551, by rfl⟩ : syracuseStep 3404735 = 5107103) B5107103
theorem B2269823 : Blo 2269435 2269823 := bstep (se 1 (by rfl) ⟨1702367, by rfl⟩ : syracuseStep 2269823 = 3404735) B3404735
theorem B3404741 : Blo 2269435 3404741 := bbase (se 4 (by rfl) ⟨319194, by rfl⟩ : syracuseStep 3404741 = 638389) (by norm_num)
theorem B2269827 : Blo 2269435 2269827 := bstep (se 1 (by rfl) ⟨1702370, by rfl⟩ : syracuseStep 2269827 = 3404741) B3404741
theorem B3830341 : Blo 2269435 3830341 := bbase (se 4 (by rfl) ⟨359094, by rfl⟩ : syracuseStep 3830341 = 718189) (by norm_num)
theorem B5107121 : Blo 2269435 5107121 := bstep (se 2 (by rfl) ⟨1915170, by rfl⟩ : syracuseStep 5107121 = 3830341) B3830341
theorem B3404747 : Blo 2269435 3404747 := bstep (se 1 (by rfl) ⟨2553560, by rfl⟩ : syracuseStep 3404747 = 5107121) B5107121
theorem B2269831 : Blo 2269435 2269831 := bstep (se 1 (by rfl) ⟨1702373, by rfl⟩ : syracuseStep 2269831 = 3404747) B3404747
theorem B2553565 : Blo 2269435 2553565 := bbase (se 3 (by rfl) ⟨478793, by rfl⟩ : syracuseStep 2553565 = 957587) (by norm_num)
theorem B3404753 : Blo 2269435 3404753 := bstep (se 2 (by rfl) ⟨1276782, by rfl⟩ : syracuseStep 3404753 = 2553565) B2553565
theorem B2269835 : Blo 2269435 2269835 := bstep (se 1 (by rfl) ⟨1702376, by rfl⟩ : syracuseStep 2269835 = 3404753) B3404753
theorem B7660709 : Blo 2269435 7660709 := bbase (se 4 (by rfl) ⟨718191, by rfl⟩ : syracuseStep 7660709 = 1436383) (by norm_num)
theorem B5107139 : Blo 2269435 5107139 := bstep (se 1 (by rfl) ⟨3830354, by rfl⟩ : syracuseStep 5107139 = 7660709) B7660709
theorem B3404759 : Blo 2269435 3404759 := bstep (se 1 (by rfl) ⟨2553569, by rfl⟩ : syracuseStep 3404759 = 5107139) B5107139
theorem B2269839 : Blo 2269435 2269839 := bstep (se 1 (by rfl) ⟨1702379, by rfl⟩ : syracuseStep 2269839 = 3404759) B3404759
theorem B3404765 : Blo 2269435 3404765 := bbase (se 3 (by rfl) ⟨638393, by rfl⟩ : syracuseStep 3404765 = 1276787) (by norm_num)
theorem B2269843 : Blo 2269435 2269843 := bstep (se 1 (by rfl) ⟨1702382, by rfl⟩ : syracuseStep 2269843 = 3404765) B3404765
theorem B5107157 : Blo 2269435 5107157 := bbase (se 7 (by rfl) ⟨59849, by rfl⟩ : syracuseStep 5107157 = 119699) (by norm_num)
theorem B3404771 : Blo 2269435 3404771 := bstep (se 1 (by rfl) ⟨2553578, by rfl⟩ : syracuseStep 3404771 = 5107157) B5107157
theorem B2269847 : Blo 2269435 2269847 := bstep (se 1 (by rfl) ⟨1702385, by rfl⟩ : syracuseStep 2269847 = 3404771) B3404771
theorem B21815189 : Blo 2269435 21815189 := bbase (se 6 (by rfl) ⟨511293, by rfl⟩ : syracuseStep 21815189 = 1022587) (by norm_num)
theorem B14543459 : Blo 2269435 14543459 := bstep (se 1 (by rfl) ⟨10907594, by rfl⟩ : syracuseStep 14543459 = 21815189) B21815189
theorem B9695639 : Blo 2269435 9695639 := bstep (se 1 (by rfl) ⟨7271729, by rfl⟩ : syracuseStep 9695639 = 14543459) B14543459
theorem B6463759 : Blo 2269435 6463759 := bstep (se 1 (by rfl) ⟨4847819, by rfl⟩ : syracuseStep 6463759 = 9695639) B9695639
theorem B8618345 : Blo 2269435 8618345 := bstep (se 2 (by rfl) ⟨3231879, by rfl⟩ : syracuseStep 8618345 = 6463759) B6463759
theorem B5745563 : Blo 2269435 5745563 := bstep (se 1 (by rfl) ⟨4309172, by rfl⟩ : syracuseStep 5745563 = 8618345) B8618345
theorem B3830375 : Blo 2269435 3830375 := bstep (se 1 (by rfl) ⟨2872781, by rfl⟩ : syracuseStep 3830375 = 5745563) B5745563
theorem B2553583 : Blo 2269435 2553583 := bstep (se 1 (by rfl) ⟨1915187, by rfl⟩ : syracuseStep 2553583 = 3830375) B3830375
theorem B3404777 : Blo 2269435 3404777 := bstep (se 2 (by rfl) ⟨1276791, by rfl⟩ : syracuseStep 3404777 = 2553583) B2553583
theorem B2269851 : Blo 2269435 2269851 := bstep (se 1 (by rfl) ⟨1702388, by rfl⟩ : syracuseStep 2269851 = 3404777) B3404777
theorem B2300825 : Blo 2269435 2300825 := bbase (se 2 (by rfl) ⟨862809, by rfl⟩ : syracuseStep 2300825 = 1725619) (by norm_num)
theorem B6135533 : Blo 2269435 6135533 := bstep (se 3 (by rfl) ⟨1150412, by rfl⟩ : syracuseStep 6135533 = 2300825) B2300825
theorem B4090355 : Blo 2269435 4090355 := bstep (se 1 (by rfl) ⟨3067766, by rfl⟩ : syracuseStep 4090355 = 6135533) B6135533
theorem B2726903 : Blo 2269435 2726903 := bstep (se 1 (by rfl) ⟨2045177, by rfl⟩ : syracuseStep 2726903 = 4090355) B4090355
theorem B7271741 : Blo 2269435 7271741 := bstep (se 3 (by rfl) ⟨1363451, by rfl⟩ : syracuseStep 7271741 = 2726903) B2726903
theorem B19391309 : Blo 2269435 19391309 := bstep (se 3 (by rfl) ⟨3635870, by rfl⟩ : syracuseStep 19391309 = 7271741) B7271741
theorem B12927539 : Blo 2269435 12927539 := bstep (se 1 (by rfl) ⟨9695654, by rfl⟩ : syracuseStep 12927539 = 19391309) B19391309
theorem B8618359 : Blo 2269435 8618359 := bstep (se 1 (by rfl) ⟨6463769, by rfl⟩ : syracuseStep 8618359 = 12927539) B12927539
theorem B11491145 : Blo 2269435 11491145 := bstep (se 2 (by rfl) ⟨4309179, by rfl⟩ : syracuseStep 11491145 = 8618359) B8618359
theorem B7660763 : Blo 2269435 7660763 := bstep (se 1 (by rfl) ⟨5745572, by rfl⟩ : syracuseStep 7660763 = 11491145) B11491145
theorem B5107175 : Blo 2269435 5107175 := bstep (se 1 (by rfl) ⟨3830381, by rfl⟩ : syracuseStep 5107175 = 7660763) B7660763
theorem B3404783 : Blo 2269435 3404783 := bstep (se 1 (by rfl) ⟨2553587, by rfl⟩ : syracuseStep 3404783 = 5107175) B5107175
theorem B2269855 : Blo 2269435 2269855 := bstep (se 1 (by rfl) ⟨1702391, by rfl⟩ : syracuseStep 2269855 = 3404783) B3404783
theorem B3404789 : Blo 2269435 3404789 := bbase (se 5 (by rfl) ⟨159599, by rfl⟩ : syracuseStep 3404789 = 319199) (by norm_num)
theorem B2269859 : Blo 2269435 2269859 := bstep (se 1 (by rfl) ⟨1702394, by rfl⟩ : syracuseStep 2269859 = 3404789) B3404789
theorem B4847845 : Blo 2269435 4847845 := bbase (se 4 (by rfl) ⟨454485, by rfl⟩ : syracuseStep 4847845 = 908971) (by norm_num)
theorem B6463793 : Blo 2269435 6463793 := bstep (se 2 (by rfl) ⟨2423922, by rfl⟩ : syracuseStep 6463793 = 4847845) B4847845
theorem B4309195 : Blo 2269435 4309195 := bstep (se 1 (by rfl) ⟨3231896, by rfl⟩ : syracuseStep 4309195 = 6463793) B6463793
theorem B5745593 : Blo 2269435 5745593 := bstep (se 2 (by rfl) ⟨2154597, by rfl⟩ : syracuseStep 5745593 = 4309195) B4309195
theorem B3830395 : Blo 2269435 3830395 := bstep (se 1 (by rfl) ⟨2872796, by rfl⟩ : syracuseStep 3830395 = 5745593) B5745593
theorem B5107193 : Blo 2269435 5107193 := bstep (se 2 (by rfl) ⟨1915197, by rfl⟩ : syracuseStep 5107193 = 3830395) B3830395
theorem B3404795 : Blo 2269435 3404795 := bstep (se 1 (by rfl) ⟨2553596, by rfl⟩ : syracuseStep 3404795 = 5107193) B5107193
theorem B2269863 : Blo 2269435 2269863 := bstep (se 1 (by rfl) ⟨1702397, by rfl⟩ : syracuseStep 2269863 = 3404795) B3404795
theorem B2553601 : Blo 2269435 2553601 := bbase (se 2 (by rfl) ⟨957600, by rfl⟩ : syracuseStep 2553601 = 1915201) (by norm_num)
theorem B3404801 : Blo 2269435 3404801 := bstep (se 2 (by rfl) ⟨1276800, by rfl⟩ : syracuseStep 3404801 = 2553601) B2553601
theorem B2269867 : Blo 2269435 2269867 := bstep (se 1 (by rfl) ⟨1702400, by rfl⟩ : syracuseStep 2269867 = 3404801) B3404801
theorem B5745613 : Blo 2269435 5745613 := bbase (se 3 (by rfl) ⟨1077302, by rfl⟩ : syracuseStep 5745613 = 2154605) (by norm_num)
theorem B7660817 : Blo 2269435 7660817 := bstep (se 2 (by rfl) ⟨2872806, by rfl⟩ : syracuseStep 7660817 = 5745613) B5745613
theorem B5107211 : Blo 2269435 5107211 := bstep (se 1 (by rfl) ⟨3830408, by rfl⟩ : syracuseStep 5107211 = 7660817) B7660817
theorem B3404807 : Blo 2269435 3404807 := bstep (se 1 (by rfl) ⟨2553605, by rfl⟩ : syracuseStep 3404807 = 5107211) B5107211
theorem B2269871 : Blo 2269435 2269871 := bstep (se 1 (by rfl) ⟨1702403, by rfl⟩ : syracuseStep 2269871 = 3404807) B3404807
theorem B3404813 : Blo 2269435 3404813 := bbase (se 3 (by rfl) ⟨638402, by rfl⟩ : syracuseStep 3404813 = 1276805) (by norm_num)
theorem B2269875 : Blo 2269435 2269875 := bstep (se 1 (by rfl) ⟨1702406, by rfl⟩ : syracuseStep 2269875 = 3404813) B3404813
theorem B5107229 : Blo 2269435 5107229 := bbase (se 3 (by rfl) ⟨957605, by rfl⟩ : syracuseStep 5107229 = 1915211) (by norm_num)
theorem B3404819 : Blo 2269435 3404819 := bstep (se 1 (by rfl) ⟨2553614, by rfl⟩ : syracuseStep 3404819 = 5107229) B5107229
theorem B2269879 : Blo 2269435 2269879 := bstep (se 1 (by rfl) ⟨1702409, by rfl⟩ : syracuseStep 2269879 = 3404819) B3404819
theorem B3830429 : Blo 2269435 3830429 := bbase (se 3 (by rfl) ⟨718205, by rfl⟩ : syracuseStep 3830429 = 1436411) (by norm_num)
theorem B2553619 : Blo 2269435 2553619 := bstep (se 1 (by rfl) ⟨1915214, by rfl⟩ : syracuseStep 2553619 = 3830429) B3830429
theorem B3404825 : Blo 2269435 3404825 := bstep (se 2 (by rfl) ⟨1276809, by rfl⟩ : syracuseStep 3404825 = 2553619) B2553619
theorem B2269883 : Blo 2269435 2269883 := bstep (se 1 (by rfl) ⟨1702412, by rfl⟩ : syracuseStep 2269883 = 3404825) B3404825
theorem B4146221 : Blo 2269435 4146221 := bbase (se 3 (by rfl) ⟨777416, by rfl⟩ : syracuseStep 4146221 = 1554833) (by norm_num)
theorem B2764147 : Blo 2269435 2764147 := bstep (se 1 (by rfl) ⟨2073110, by rfl⟩ : syracuseStep 2764147 = 4146221) B4146221
theorem B3685529 : Blo 2269435 3685529 := bstep (se 2 (by rfl) ⟨1382073, by rfl⟩ : syracuseStep 3685529 = 2764147) B2764147
theorem B2457019 : Blo 2269435 2457019 := bstep (se 1 (by rfl) ⟨1842764, by rfl⟩ : syracuseStep 2457019 = 3685529) B3685529
theorem B3276025 : Blo 2269435 3276025 := bstep (se 2 (by rfl) ⟨1228509, by rfl⟩ : syracuseStep 3276025 = 2457019) B2457019
theorem B17472133 : Blo 2269435 17472133 := bstep (se 4 (by rfl) ⟨1638012, by rfl⟩ : syracuseStep 17472133 = 3276025) B3276025
theorem B23296177 : Blo 2269435 23296177 := bstep (se 2 (by rfl) ⟨8736066, by rfl⟩ : syracuseStep 23296177 = 17472133) B17472133
theorem B31061569 : Blo 2269435 31061569 := bstep (se 2 (by rfl) ⟨11648088, by rfl⟩ : syracuseStep 31061569 = 23296177) B23296177
theorem B41415425 : Blo 2269435 41415425 := bstep (se 2 (by rfl) ⟨15530784, by rfl⟩ : syracuseStep 41415425 = 31061569) B31061569
theorem B27610283 : Blo 2269435 27610283 := bstep (se 1 (by rfl) ⟨20707712, by rfl⟩ : syracuseStep 27610283 = 41415425) B41415425
theorem B18406855 : Blo 2269435 18406855 := bstep (se 1 (by rfl) ⟨13805141, by rfl⟩ : syracuseStep 18406855 = 27610283) B27610283
theorem B24542473 : Blo 2269435 24542473 := bstep (se 2 (by rfl) ⟨9203427, by rfl⟩ : syracuseStep 24542473 = 18406855) B18406855
theorem B32723297 : Blo 2269435 32723297 := bstep (se 2 (by rfl) ⟨12271236, by rfl⟩ : syracuseStep 32723297 = 24542473) B24542473
theorem B21815531 : Blo 2269435 21815531 := bstep (se 1 (by rfl) ⟨16361648, by rfl⟩ : syracuseStep 21815531 = 32723297) B32723297
theorem B14543687 : Blo 2269435 14543687 := bstep (se 1 (by rfl) ⟨10907765, by rfl⟩ : syracuseStep 14543687 = 21815531) B21815531
theorem B9695791 : Blo 2269435 9695791 := bstep (se 1 (by rfl) ⟨7271843, by rfl⟩ : syracuseStep 9695791 = 14543687) B14543687
theorem B12927721 : Blo 2269435 12927721 := bstep (se 2 (by rfl) ⟨4847895, by rfl⟩ : syracuseStep 12927721 = 9695791) B9695791
theorem B17236961 : Blo 2269435 17236961 := bstep (se 2 (by rfl) ⟨6463860, by rfl⟩ : syracuseStep 17236961 = 12927721) B12927721
theorem B11491307 : Blo 2269435 11491307 := bstep (se 1 (by rfl) ⟨8618480, by rfl⟩ : syracuseStep 11491307 = 17236961) B17236961
theorem B7660871 : Blo 2269435 7660871 := bstep (se 1 (by rfl) ⟨5745653, by rfl⟩ : syracuseStep 7660871 = 11491307) B11491307
theorem B5107247 : Blo 2269435 5107247 := bstep (se 1 (by rfl) ⟨3830435, by rfl⟩ : syracuseStep 5107247 = 7660871) B7660871
theorem B3404831 : Blo 2269435 3404831 := bstep (se 1 (by rfl) ⟨2553623, by rfl⟩ : syracuseStep 3404831 = 5107247) B5107247
theorem B2269887 : Blo 2269435 2269887 := bstep (se 1 (by rfl) ⟨1702415, by rfl⟩ : syracuseStep 2269887 = 3404831) B3404831
theorem B3404837 : Blo 2269435 3404837 := bbase (se 4 (by rfl) ⟨319203, by rfl⟩ : syracuseStep 3404837 = 638407) (by norm_num)
theorem B2269891 : Blo 2269435 2269891 := bstep (se 1 (by rfl) ⟨1702418, by rfl⟩ : syracuseStep 2269891 = 3404837) B3404837
theorem B2872837 : Blo 2269435 2872837 := bbase (se 4 (by rfl) ⟨269328, by rfl⟩ : syracuseStep 2872837 = 538657) (by norm_num)
theorem B3830449 : Blo 2269435 3830449 := bstep (se 2 (by rfl) ⟨1436418, by rfl⟩ : syracuseStep 3830449 = 2872837) B2872837
theorem B5107265 : Blo 2269435 5107265 := bstep (se 2 (by rfl) ⟨1915224, by rfl⟩ : syracuseStep 5107265 = 3830449) B3830449
theorem B3404843 : Blo 2269435 3404843 := bstep (se 1 (by rfl) ⟨2553632, by rfl⟩ : syracuseStep 3404843 = 5107265) B5107265
theorem B2269895 : Blo 2269435 2269895 := bstep (se 1 (by rfl) ⟨1702421, by rfl⟩ : syracuseStep 2269895 = 3404843) B3404843
theorem B2553637 : Blo 2269435 2553637 := bbase (se 4 (by rfl) ⟨239403, by rfl⟩ : syracuseStep 2553637 = 478807) (by norm_num)
theorem B3404849 : Blo 2269435 3404849 := bstep (se 2 (by rfl) ⟨1276818, by rfl⟩ : syracuseStep 3404849 = 2553637) B2553637
theorem B2269899 : Blo 2269435 2269899 := bstep (se 1 (by rfl) ⟨1702424, by rfl⟩ : syracuseStep 2269899 = 3404849) B3404849
theorem B9695861 : Blo 2269435 9695861 := bbase (se 5 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 9695861 = 908987) (by norm_num)
theorem B6463907 : Blo 2269435 6463907 := bstep (se 1 (by rfl) ⟨4847930, by rfl⟩ : syracuseStep 6463907 = 9695861) B9695861
theorem B4309271 : Blo 2269435 4309271 := bstep (se 1 (by rfl) ⟨3231953, by rfl⟩ : syracuseStep 4309271 = 6463907) B6463907
theorem B2872847 : Blo 2269435 2872847 := bstep (se 1 (by rfl) ⟨2154635, by rfl⟩ : syracuseStep 2872847 = 4309271) B4309271
theorem B7660925 : Blo 2269435 7660925 := bstep (se 3 (by rfl) ⟨1436423, by rfl⟩ : syracuseStep 7660925 = 2872847) B2872847
theorem B5107283 : Blo 2269435 5107283 := bstep (se 1 (by rfl) ⟨3830462, by rfl⟩ : syracuseStep 5107283 = 7660925) B7660925
theorem B3404855 : Blo 2269435 3404855 := bstep (se 1 (by rfl) ⟨2553641, by rfl⟩ : syracuseStep 3404855 = 5107283) B5107283
theorem B2269903 : Blo 2269435 2269903 := bstep (se 1 (by rfl) ⟨1702427, by rfl⟩ : syracuseStep 2269903 = 3404855) B3404855
theorem B3404861 : Blo 2269435 3404861 := bbase (se 3 (by rfl) ⟨638411, by rfl⟩ : syracuseStep 3404861 = 1276823) (by norm_num)
theorem B2269907 : Blo 2269435 2269907 := bstep (se 1 (by rfl) ⟨1702430, by rfl⟩ : syracuseStep 2269907 = 3404861) B3404861
theorem B5107301 : Blo 2269435 5107301 := bbase (se 4 (by rfl) ⟨478809, by rfl⟩ : syracuseStep 5107301 = 957619) (by norm_num)
theorem B3404867 : Blo 2269435 3404867 := bstep (se 1 (by rfl) ⟨2553650, by rfl⟩ : syracuseStep 3404867 = 5107301) B5107301
theorem B2269911 : Blo 2269435 2269911 := bstep (se 1 (by rfl) ⟨1702433, by rfl⟩ : syracuseStep 2269911 = 3404867) B3404867
theorem B5745725 : Blo 2269435 5745725 := bbase (se 3 (by rfl) ⟨1077323, by rfl⟩ : syracuseStep 5745725 = 2154647) (by norm_num)
theorem B3830483 : Blo 2269435 3830483 := bstep (se 1 (by rfl) ⟨2872862, by rfl⟩ : syracuseStep 3830483 = 5745725) B5745725
theorem B2553655 : Blo 2269435 2553655 := bstep (se 1 (by rfl) ⟨1915241, by rfl⟩ : syracuseStep 2553655 = 3830483) B3830483
theorem B3404873 : Blo 2269435 3404873 := bstep (se 2 (by rfl) ⟨1276827, by rfl⟩ : syracuseStep 3404873 = 2553655) B2553655
theorem B2269915 : Blo 2269435 2269915 := bstep (se 1 (by rfl) ⟨1702436, by rfl⟩ : syracuseStep 2269915 = 3404873) B3404873
theorem B4309301 : Blo 2269435 4309301 := bbase (se 5 (by rfl) ⟨201998, by rfl⟩ : syracuseStep 4309301 = 403997) (by norm_num)
theorem B11491469 : Blo 2269435 11491469 := bstep (se 3 (by rfl) ⟨2154650, by rfl⟩ : syracuseStep 11491469 = 4309301) B4309301
theorem B7660979 : Blo 2269435 7660979 := bstep (se 1 (by rfl) ⟨5745734, by rfl⟩ : syracuseStep 7660979 = 11491469) B11491469
theorem B5107319 : Blo 2269435 5107319 := bstep (se 1 (by rfl) ⟨3830489, by rfl⟩ : syracuseStep 5107319 = 7660979) B7660979
theorem B3404879 : Blo 2269435 3404879 := bstep (se 1 (by rfl) ⟨2553659, by rfl⟩ : syracuseStep 3404879 = 5107319) B5107319
theorem B2269919 : Blo 2269435 2269919 := bstep (se 1 (by rfl) ⟨1702439, by rfl⟩ : syracuseStep 2269919 = 3404879) B3404879
theorem B3404885 : Blo 2269435 3404885 := bbase (se 8 (by rfl) ⟨19950, by rfl⟩ : syracuseStep 3404885 = 39901) (by norm_num)
theorem B2269923 : Blo 2269435 2269923 := bstep (se 1 (by rfl) ⟨1702442, by rfl⟩ : syracuseStep 2269923 = 3404885) B3404885
theorem B15531061 : Blo 2269435 15531061 := bbase (se 5 (by rfl) ⟨728018, by rfl⟩ : syracuseStep 15531061 = 1456037) (by norm_num)
theorem B20708081 : Blo 2269435 20708081 := bstep (se 2 (by rfl) ⟨7765530, by rfl⟩ : syracuseStep 20708081 = 15531061) B15531061
theorem B13805387 : Blo 2269435 13805387 := bstep (se 1 (by rfl) ⟨10354040, by rfl⟩ : syracuseStep 13805387 = 20708081) B20708081
theorem B9203591 : Blo 2269435 9203591 := bstep (se 1 (by rfl) ⟨6902693, by rfl⟩ : syracuseStep 9203591 = 13805387) B13805387
theorem B24542909 : Blo 2269435 24542909 := bstep (se 3 (by rfl) ⟨4601795, by rfl⟩ : syracuseStep 24542909 = 9203591) B9203591
theorem B16361939 : Blo 2269435 16361939 := bstep (se 1 (by rfl) ⟨12271454, by rfl⟩ : syracuseStep 16361939 = 24542909) B24542909
theorem B10907959 : Blo 2269435 10907959 := bstep (se 1 (by rfl) ⟨8180969, by rfl⟩ : syracuseStep 10907959 = 16361939) B16361939
theorem B14543945 : Blo 2269435 14543945 := bstep (se 2 (by rfl) ⟨5453979, by rfl⟩ : syracuseStep 14543945 = 10907959) B10907959
theorem B9695963 : Blo 2269435 9695963 := bstep (se 1 (by rfl) ⟨7271972, by rfl⟩ : syracuseStep 9695963 = 14543945) B14543945
theorem B6463975 : Blo 2269435 6463975 := bstep (se 1 (by rfl) ⟨4847981, by rfl⟩ : syracuseStep 6463975 = 9695963) B9695963
theorem B8618633 : Blo 2269435 8618633 := bstep (se 2 (by rfl) ⟨3231987, by rfl⟩ : syracuseStep 8618633 = 6463975) B6463975
theorem B5745755 : Blo 2269435 5745755 := bstep (se 1 (by rfl) ⟨4309316, by rfl⟩ : syracuseStep 5745755 = 8618633) B8618633
theorem B3830503 : Blo 2269435 3830503 := bstep (se 1 (by rfl) ⟨2872877, by rfl⟩ : syracuseStep 3830503 = 5745755) B5745755
theorem B5107337 : Blo 2269435 5107337 := bstep (se 2 (by rfl) ⟨1915251, by rfl⟩ : syracuseStep 5107337 = 3830503) B3830503
theorem B3404891 : Blo 2269435 3404891 := bstep (se 1 (by rfl) ⟨2553668, by rfl⟩ : syracuseStep 3404891 = 5107337) B5107337
theorem B2269927 : Blo 2269435 2269927 := bstep (se 1 (by rfl) ⟨1702445, by rfl⟩ : syracuseStep 2269927 = 3404891) B3404891
theorem B2553673 : Blo 2269435 2553673 := bbase (se 2 (by rfl) ⟨957627, by rfl⟩ : syracuseStep 2553673 = 1915255) (by norm_num)
theorem B3404897 : Blo 2269435 3404897 := bstep (se 2 (by rfl) ⟨1276836, by rfl⟩ : syracuseStep 3404897 = 2553673) B2553673
theorem B2269931 : Blo 2269435 2269931 := bstep (se 1 (by rfl) ⟨1702448, by rfl⟩ : syracuseStep 2269931 = 3404897) B3404897
theorem B11968357 : Blo 2269435 11968357 := bbase (se 4 (by rfl) ⟨1122033, by rfl⟩ : syracuseStep 11968357 = 2244067) (by norm_num)
theorem B15957809 : Blo 2269435 15957809 := bstep (se 2 (by rfl) ⟨5984178, by rfl⟩ : syracuseStep 15957809 = 11968357) B11968357
theorem B10638539 : Blo 2269435 10638539 := bstep (se 1 (by rfl) ⟨7978904, by rfl⟩ : syracuseStep 10638539 = 15957809) B15957809
theorem B7092359 : Blo 2269435 7092359 := bstep (se 1 (by rfl) ⟨5319269, by rfl⟩ : syracuseStep 7092359 = 10638539) B10638539
theorem B4728239 : Blo 2269435 4728239 := bstep (se 1 (by rfl) ⟨3546179, by rfl⟩ : syracuseStep 4728239 = 7092359) B7092359
theorem B3152159 : Blo 2269435 3152159 := bstep (se 1 (by rfl) ⟨2364119, by rfl⟩ : syracuseStep 3152159 = 4728239) B4728239
theorem B33623029 : Blo 2269435 33623029 := bstep (se 5 (by rfl) ⟨1576079, by rfl⟩ : syracuseStep 33623029 = 3152159) B3152159
theorem B44830705 : Blo 2269435 44830705 := bstep (se 2 (by rfl) ⟨16811514, by rfl⟩ : syracuseStep 44830705 = 33623029) B33623029
theorem B59774273 : Blo 2269435 59774273 := bstep (se 2 (by rfl) ⟨22415352, by rfl⟩ : syracuseStep 59774273 = 44830705) B44830705
theorem B39849515 : Blo 2269435 39849515 := bstep (se 1 (by rfl) ⟨29887136, by rfl⟩ : syracuseStep 39849515 = 59774273) B59774273
theorem B26566343 : Blo 2269435 26566343 := bstep (se 1 (by rfl) ⟨19924757, by rfl⟩ : syracuseStep 26566343 = 39849515) B39849515
theorem B17710895 : Blo 2269435 17710895 := bstep (se 1 (by rfl) ⟨13283171, by rfl⟩ : syracuseStep 17710895 = 26566343) B26566343
theorem B11807263 : Blo 2269435 11807263 := bstep (se 1 (by rfl) ⟨8855447, by rfl⟩ : syracuseStep 11807263 = 17710895) B17710895
theorem B15743017 : Blo 2269435 15743017 := bstep (se 2 (by rfl) ⟨5903631, by rfl⟩ : syracuseStep 15743017 = 11807263) B11807263
theorem B83962757 : Blo 2269435 83962757 := bstep (se 4 (by rfl) ⟨7871508, by rfl⟩ : syracuseStep 83962757 = 15743017) B15743017
theorem B55975171 : Blo 2269435 55975171 := bstep (se 1 (by rfl) ⟨41981378, by rfl⟩ : syracuseStep 55975171 = 83962757) B83962757
theorem B74633561 : Blo 2269435 74633561 := bstep (se 2 (by rfl) ⟨27987585, by rfl⟩ : syracuseStep 74633561 = 55975171) B55975171
theorem B49755707 : Blo 2269435 49755707 := bstep (se 1 (by rfl) ⟨37316780, by rfl⟩ : syracuseStep 49755707 = 74633561) B74633561
theorem B33170471 : Blo 2269435 33170471 := bstep (se 1 (by rfl) ⟨24877853, by rfl⟩ : syracuseStep 33170471 = 49755707) B49755707
theorem B22113647 : Blo 2269435 22113647 := bstep (se 1 (by rfl) ⟨16585235, by rfl⟩ : syracuseStep 22113647 = 33170471) B33170471
theorem B14742431 : Blo 2269435 14742431 := bstep (se 1 (by rfl) ⟨11056823, by rfl⟩ : syracuseStep 14742431 = 22113647) B22113647
theorem B9828287 : Blo 2269435 9828287 := bstep (se 1 (by rfl) ⟨7371215, by rfl⟩ : syracuseStep 9828287 = 14742431) B14742431
theorem B6552191 : Blo 2269435 6552191 := bstep (se 1 (by rfl) ⟨4914143, by rfl⟩ : syracuseStep 6552191 = 9828287) B9828287
theorem B4368127 : Blo 2269435 4368127 := bstep (se 1 (by rfl) ⟨3276095, by rfl⟩ : syracuseStep 4368127 = 6552191) B6552191
theorem B5824169 : Blo 2269435 5824169 := bstep (se 2 (by rfl) ⟨2184063, by rfl⟩ : syracuseStep 5824169 = 4368127) B4368127
theorem B3882779 : Blo 2269435 3882779 := bstep (se 1 (by rfl) ⟨2912084, by rfl⟩ : syracuseStep 3882779 = 5824169) B5824169
theorem B2588519 : Blo 2269435 2588519 := bstep (se 1 (by rfl) ⟨1941389, by rfl⟩ : syracuseStep 2588519 = 3882779) B3882779
theorem B6902717 : Blo 2269435 6902717 := bstep (se 3 (by rfl) ⟨1294259, by rfl⟩ : syracuseStep 6902717 = 2588519) B2588519
theorem B18407245 : Blo 2269435 18407245 := bstep (se 3 (by rfl) ⟨3451358, by rfl⟩ : syracuseStep 18407245 = 6902717) B6902717
theorem B24542993 : Blo 2269435 24542993 := bstep (se 2 (by rfl) ⟨9203622, by rfl⟩ : syracuseStep 24542993 = 18407245) B18407245
theorem B16361995 : Blo 2269435 16361995 := bstep (se 1 (by rfl) ⟨12271496, by rfl⟩ : syracuseStep 16361995 = 24542993) B24542993
theorem B21815993 : Blo 2269435 21815993 := bstep (se 2 (by rfl) ⟨8180997, by rfl⟩ : syracuseStep 21815993 = 16361995) B16361995
theorem B14543995 : Blo 2269435 14543995 := bstep (se 1 (by rfl) ⟨10907996, by rfl⟩ : syracuseStep 14543995 = 21815993) B21815993
theorem B19391993 : Blo 2269435 19391993 := bstep (se 2 (by rfl) ⟨7271997, by rfl⟩ : syracuseStep 19391993 = 14543995) B14543995
theorem B12927995 : Blo 2269435 12927995 := bstep (se 1 (by rfl) ⟨9695996, by rfl⟩ : syracuseStep 12927995 = 19391993) B19391993
theorem B8618663 : Blo 2269435 8618663 := bstep (se 1 (by rfl) ⟨6463997, by rfl⟩ : syracuseStep 8618663 = 12927995) B12927995
theorem B5745775 : Blo 2269435 5745775 := bstep (se 1 (by rfl) ⟨4309331, by rfl⟩ : syracuseStep 5745775 = 8618663) B8618663
theorem B7661033 : Blo 2269435 7661033 := bstep (se 2 (by rfl) ⟨2872887, by rfl⟩ : syracuseStep 7661033 = 5745775) B5745775
theorem B5107355 : Blo 2269435 5107355 := bstep (se 1 (by rfl) ⟨3830516, by rfl⟩ : syracuseStep 5107355 = 7661033) B7661033
theorem B3404903 : Blo 2269435 3404903 := bstep (se 1 (by rfl) ⟨2553677, by rfl⟩ : syracuseStep 3404903 = 5107355) B5107355
theorem B2269935 : Blo 2269435 2269935 := bstep (se 1 (by rfl) ⟨1702451, by rfl⟩ : syracuseStep 2269935 = 3404903) B3404903
theorem B3404909 : Blo 2269435 3404909 := bbase (se 3 (by rfl) ⟨638420, by rfl⟩ : syracuseStep 3404909 = 1276841) (by norm_num)
theorem B2269939 : Blo 2269435 2269939 := bstep (se 1 (by rfl) ⟨1702454, by rfl⟩ : syracuseStep 2269939 = 3404909) B3404909
theorem B5107373 : Blo 2269435 5107373 := bbase (se 3 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 5107373 = 1915265) (by norm_num)
theorem B3404915 : Blo 2269435 3404915 := bstep (se 1 (by rfl) ⟨2553686, by rfl⟩ : syracuseStep 3404915 = 5107373) B5107373
theorem B2269943 : Blo 2269435 2269943 := bstep (se 1 (by rfl) ⟨1702457, by rfl⟩ : syracuseStep 2269943 = 3404915) B3404915
theorem B5454029 : Blo 2269435 5454029 := bbase (se 3 (by rfl) ⟨1022630, by rfl⟩ : syracuseStep 5454029 = 2045261) (by norm_num)
theorem B3636019 : Blo 2269435 3636019 := bstep (se 1 (by rfl) ⟨2727014, by rfl⟩ : syracuseStep 3636019 = 5454029) B5454029
theorem B4848025 : Blo 2269435 4848025 := bstep (se 2 (by rfl) ⟨1818009, by rfl⟩ : syracuseStep 4848025 = 3636019) B3636019
theorem B6464033 : Blo 2269435 6464033 := bstep (se 2 (by rfl) ⟨2424012, by rfl⟩ : syracuseStep 6464033 = 4848025) B4848025
theorem B4309355 : Blo 2269435 4309355 := bstep (se 1 (by rfl) ⟨3232016, by rfl⟩ : syracuseStep 4309355 = 6464033) B6464033
theorem B2872903 : Blo 2269435 2872903 := bstep (se 1 (by rfl) ⟨2154677, by rfl⟩ : syracuseStep 2872903 = 4309355) B4309355
theorem B3830537 : Blo 2269435 3830537 := bstep (se 2 (by rfl) ⟨1436451, by rfl⟩ : syracuseStep 3830537 = 2872903) B2872903
theorem B2553691 : Blo 2269435 2553691 := bstep (se 1 (by rfl) ⟨1915268, by rfl⟩ : syracuseStep 2553691 = 3830537) B3830537
theorem B3404921 : Blo 2269435 3404921 := bstep (se 2 (by rfl) ⟨1276845, by rfl⟩ : syracuseStep 3404921 = 2553691) B2553691
theorem B2269947 : Blo 2269435 2269947 := bstep (se 1 (by rfl) ⟨1702460, by rfl⟩ : syracuseStep 2269947 = 3404921) B3404921
theorem B9962453 : Blo 2269435 9962453 := bbase (se 7 (by rfl) ⟨116747, by rfl⟩ : syracuseStep 9962453 = 233495) (by norm_num)
theorem B6641635 : Blo 2269435 6641635 := bstep (se 1 (by rfl) ⟨4981226, by rfl⟩ : syracuseStep 6641635 = 9962453) B9962453
theorem B8855513 : Blo 2269435 8855513 := bstep (se 2 (by rfl) ⟨3320817, by rfl⟩ : syracuseStep 8855513 = 6641635) B6641635
theorem B5903675 : Blo 2269435 5903675 := bstep (se 1 (by rfl) ⟨4427756, by rfl⟩ : syracuseStep 5903675 = 8855513) B8855513
theorem B3935783 : Blo 2269435 3935783 := bstep (se 1 (by rfl) ⟨2951837, by rfl⟩ : syracuseStep 3935783 = 5903675) B5903675
theorem B2623855 : Blo 2269435 2623855 := bstep (se 1 (by rfl) ⟨1967891, by rfl⟩ : syracuseStep 2623855 = 3935783) B3935783
theorem B3498473 : Blo 2269435 3498473 := bstep (se 2 (by rfl) ⟨1311927, by rfl⟩ : syracuseStep 3498473 = 2623855) B2623855
theorem B2332315 : Blo 2269435 2332315 := bstep (se 1 (by rfl) ⟨1749236, by rfl⟩ : syracuseStep 2332315 = 3498473) B3498473
theorem B3109753 : Blo 2269435 3109753 := bstep (se 2 (by rfl) ⟨1166157, by rfl⟩ : syracuseStep 3109753 = 2332315) B2332315
theorem B4146337 : Blo 2269435 4146337 := bstep (se 2 (by rfl) ⟨1554876, by rfl⟩ : syracuseStep 4146337 = 3109753) B3109753
theorem B5528449 : Blo 2269435 5528449 := bstep (se 2 (by rfl) ⟨2073168, by rfl⟩ : syracuseStep 5528449 = 4146337) B4146337
theorem B7371265 : Blo 2269435 7371265 := bstep (se 2 (by rfl) ⟨2764224, by rfl⟩ : syracuseStep 7371265 = 5528449) B5528449
theorem B9828353 : Blo 2269435 9828353 := bstep (se 2 (by rfl) ⟨3685632, by rfl⟩ : syracuseStep 9828353 = 7371265) B7371265
theorem B6552235 : Blo 2269435 6552235 := bstep (se 1 (by rfl) ⟨4914176, by rfl⟩ : syracuseStep 6552235 = 9828353) B9828353
theorem B34945253 : Blo 2269435 34945253 := bstep (se 4 (by rfl) ⟨3276117, by rfl⟩ : syracuseStep 34945253 = 6552235) B6552235
theorem B23296835 : Blo 2269435 23296835 := bstep (se 1 (by rfl) ⟨17472626, by rfl⟩ : syracuseStep 23296835 = 34945253) B34945253
theorem B15531223 : Blo 2269435 15531223 := bstep (se 1 (by rfl) ⟨11648417, by rfl⟩ : syracuseStep 15531223 = 23296835) B23296835
theorem B20708297 : Blo 2269435 20708297 := bstep (se 2 (by rfl) ⟨7765611, by rfl⟩ : syracuseStep 20708297 = 15531223) B15531223
theorem B13805531 : Blo 2269435 13805531 := bstep (se 1 (by rfl) ⟨10354148, by rfl⟩ : syracuseStep 13805531 = 20708297) B20708297
theorem B9203687 : Blo 2269435 9203687 := bstep (se 1 (by rfl) ⟨6902765, by rfl⟩ : syracuseStep 9203687 = 13805531) B13805531
theorem B6135791 : Blo 2269435 6135791 := bstep (se 1 (by rfl) ⟨4601843, by rfl⟩ : syracuseStep 6135791 = 9203687) B9203687
theorem B16362109 : Blo 2269435 16362109 := bstep (se 3 (by rfl) ⟨3067895, by rfl⟩ : syracuseStep 16362109 = 6135791) B6135791
theorem B21816145 : Blo 2269435 21816145 := bstep (se 2 (by rfl) ⟨8181054, by rfl⟩ : syracuseStep 21816145 = 16362109) B16362109
theorem B29088193 : Blo 2269435 29088193 := bstep (se 2 (by rfl) ⟨10908072, by rfl⟩ : syracuseStep 29088193 = 21816145) B21816145
theorem B38784257 : Blo 2269435 38784257 := bstep (se 2 (by rfl) ⟨14544096, by rfl⟩ : syracuseStep 38784257 = 29088193) B29088193
theorem B25856171 : Blo 2269435 25856171 := bstep (se 1 (by rfl) ⟨19392128, by rfl⟩ : syracuseStep 25856171 = 38784257) B38784257
theorem B17237447 : Blo 2269435 17237447 := bstep (se 1 (by rfl) ⟨12928085, by rfl⟩ : syracuseStep 17237447 = 25856171) B25856171
theorem B11491631 : Blo 2269435 11491631 := bstep (se 1 (by rfl) ⟨8618723, by rfl⟩ : syracuseStep 11491631 = 17237447) B17237447
theorem B7661087 : Blo 2269435 7661087 := bstep (se 1 (by rfl) ⟨5745815, by rfl⟩ : syracuseStep 7661087 = 11491631) B11491631
theorem B5107391 : Blo 2269435 5107391 := bstep (se 1 (by rfl) ⟨3830543, by rfl⟩ : syracuseStep 5107391 = 7661087) B7661087
theorem B3404927 : Blo 2269435 3404927 := bstep (se 1 (by rfl) ⟨2553695, by rfl⟩ : syracuseStep 3404927 = 5107391) B5107391
theorem B2269951 : Blo 2269435 2269951 := bstep (se 1 (by rfl) ⟨1702463, by rfl⟩ : syracuseStep 2269951 = 3404927) B3404927
theorem B3404933 : Blo 2269435 3404933 := bbase (se 4 (by rfl) ⟨319212, by rfl⟩ : syracuseStep 3404933 = 638425) (by norm_num)
theorem B2269955 : Blo 2269435 2269955 := bstep (se 1 (by rfl) ⟨1702466, by rfl⟩ : syracuseStep 2269955 = 3404933) B3404933
theorem B3830557 : Blo 2269435 3830557 := bbase (se 3 (by rfl) ⟨718229, by rfl⟩ : syracuseStep 3830557 = 1436459) (by norm_num)
theorem B5107409 : Blo 2269435 5107409 := bstep (se 2 (by rfl) ⟨1915278, by rfl⟩ : syracuseStep 5107409 = 3830557) B3830557
theorem B3404939 : Blo 2269435 3404939 := bstep (se 1 (by rfl) ⟨2553704, by rfl⟩ : syracuseStep 3404939 = 5107409) B5107409
theorem B2269959 : Blo 2269435 2269959 := bstep (se 1 (by rfl) ⟨1702469, by rfl⟩ : syracuseStep 2269959 = 3404939) B3404939
theorem B2553709 : Blo 2269435 2553709 := bbase (se 3 (by rfl) ⟨478820, by rfl⟩ : syracuseStep 2553709 = 957641) (by norm_num)
theorem B3404945 : Blo 2269435 3404945 := bstep (se 2 (by rfl) ⟨1276854, by rfl⟩ : syracuseStep 3404945 = 2553709) B2553709
theorem B2269963 : Blo 2269435 2269963 := bstep (se 1 (by rfl) ⟨1702472, by rfl⟩ : syracuseStep 2269963 = 3404945) B3404945
theorem B7661141 : Blo 2269435 7661141 := bbase (se 8 (by rfl) ⟨44889, by rfl⟩ : syracuseStep 7661141 = 89779) (by norm_num)
theorem B5107427 : Blo 2269435 5107427 := bstep (se 1 (by rfl) ⟨3830570, by rfl⟩ : syracuseStep 5107427 = 7661141) B7661141
theorem B3404951 : Blo 2269435 3404951 := bstep (se 1 (by rfl) ⟨2553713, by rfl⟩ : syracuseStep 3404951 = 5107427) B5107427
theorem B2269967 : Blo 2269435 2269967 := bstep (se 1 (by rfl) ⟨1702475, by rfl⟩ : syracuseStep 2269967 = 3404951) B3404951
theorem B3404957 : Blo 2269435 3404957 := bbase (se 3 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 3404957 = 1276859) (by norm_num)
theorem B2269971 : Blo 2269435 2269971 := bstep (se 1 (by rfl) ⟨1702478, by rfl⟩ : syracuseStep 2269971 = 3404957) B3404957
theorem B5107445 : Blo 2269435 5107445 := bbase (se 5 (by rfl) ⟨239411, by rfl⟩ : syracuseStep 5107445 = 478823) (by norm_num)
theorem B3404963 : Blo 2269435 3404963 := bstep (se 1 (by rfl) ⟨2553722, by rfl⟩ : syracuseStep 3404963 = 5107445) B5107445
theorem B2269975 : Blo 2269435 2269975 := bstep (se 1 (by rfl) ⟨1702481, by rfl⟩ : syracuseStep 2269975 = 3404963) B3404963
theorem B8181157 : Blo 2269435 8181157 := bbase (se 4 (by rfl) ⟨766983, by rfl⟩ : syracuseStep 8181157 = 1533967) (by norm_num)
theorem B10908209 : Blo 2269435 10908209 := bstep (se 2 (by rfl) ⟨4090578, by rfl⟩ : syracuseStep 10908209 = 8181157) B8181157
theorem B29088557 : Blo 2269435 29088557 := bstep (se 3 (by rfl) ⟨5454104, by rfl⟩ : syracuseStep 29088557 = 10908209) B10908209
theorem B19392371 : Blo 2269435 19392371 := bstep (se 1 (by rfl) ⟨14544278, by rfl⟩ : syracuseStep 19392371 = 29088557) B29088557
theorem B12928247 : Blo 2269435 12928247 := bstep (se 1 (by rfl) ⟨9696185, by rfl⟩ : syracuseStep 12928247 = 19392371) B19392371
theorem B8618831 : Blo 2269435 8618831 := bstep (se 1 (by rfl) ⟨6464123, by rfl⟩ : syracuseStep 8618831 = 12928247) B12928247
theorem B5745887 : Blo 2269435 5745887 := bstep (se 1 (by rfl) ⟨4309415, by rfl⟩ : syracuseStep 5745887 = 8618831) B8618831
theorem B3830591 : Blo 2269435 3830591 := bstep (se 1 (by rfl) ⟨2872943, by rfl⟩ : syracuseStep 3830591 = 5745887) B5745887
theorem B2553727 : Blo 2269435 2553727 := bstep (se 1 (by rfl) ⟨1915295, by rfl⟩ : syracuseStep 2553727 = 3830591) B3830591
theorem B3404969 : Blo 2269435 3404969 := bstep (se 2 (by rfl) ⟨1276863, by rfl⟩ : syracuseStep 3404969 = 2553727) B2553727
theorem B2269979 : Blo 2269435 2269979 := bstep (se 1 (by rfl) ⟨1702484, by rfl⟩ : syracuseStep 2269979 = 3404969) B3404969
theorem B4848101 : Blo 2269435 4848101 := bbase (se 4 (by rfl) ⟨454509, by rfl⟩ : syracuseStep 4848101 = 909019) (by norm_num)
theorem B3232067 : Blo 2269435 3232067 := bstep (se 1 (by rfl) ⟨2424050, by rfl⟩ : syracuseStep 3232067 = 4848101) B4848101
theorem B8618845 : Blo 2269435 8618845 := bstep (se 3 (by rfl) ⟨1616033, by rfl⟩ : syracuseStep 8618845 = 3232067) B3232067
theorem B11491793 : Blo 2269435 11491793 := bstep (se 2 (by rfl) ⟨4309422, by rfl⟩ : syracuseStep 11491793 = 8618845) B8618845
theorem B7661195 : Blo 2269435 7661195 := bstep (se 1 (by rfl) ⟨5745896, by rfl⟩ : syracuseStep 7661195 = 11491793) B11491793
theorem B5107463 : Blo 2269435 5107463 := bstep (se 1 (by rfl) ⟨3830597, by rfl⟩ : syracuseStep 5107463 = 7661195) B7661195
theorem B3404975 : Blo 2269435 3404975 := bstep (se 1 (by rfl) ⟨2553731, by rfl⟩ : syracuseStep 3404975 = 5107463) B5107463
theorem B2269983 : Blo 2269435 2269983 := bstep (se 1 (by rfl) ⟨1702487, by rfl⟩ : syracuseStep 2269983 = 3404975) B3404975
theorem B3404981 : Blo 2269435 3404981 := bbase (se 5 (by rfl) ⟨159608, by rfl⟩ : syracuseStep 3404981 = 319217) (by norm_num)
theorem B2269987 : Blo 2269435 2269987 := bstep (se 1 (by rfl) ⟨1702490, by rfl⟩ : syracuseStep 2269987 = 3404981) B3404981
theorem B5745917 : Blo 2269435 5745917 := bbase (se 3 (by rfl) ⟨1077359, by rfl⟩ : syracuseStep 5745917 = 2154719) (by norm_num)
theorem B3830611 : Blo 2269435 3830611 := bstep (se 1 (by rfl) ⟨2872958, by rfl⟩ : syracuseStep 3830611 = 5745917) B5745917
theorem B5107481 : Blo 2269435 5107481 := bstep (se 2 (by rfl) ⟨1915305, by rfl⟩ : syracuseStep 5107481 = 3830611) B3830611
theorem B3404987 : Blo 2269435 3404987 := bstep (se 1 (by rfl) ⟨2553740, by rfl⟩ : syracuseStep 3404987 = 5107481) B5107481
theorem B2269991 : Blo 2269435 2269991 := bstep (se 1 (by rfl) ⟨1702493, by rfl⟩ : syracuseStep 2269991 = 3404987) B3404987
theorem B2553745 : Blo 2269435 2553745 := bbase (se 2 (by rfl) ⟨957654, by rfl⟩ : syracuseStep 2553745 = 1915309) (by norm_num)
theorem B3404993 : Blo 2269435 3404993 := bstep (se 2 (by rfl) ⟨1276872, by rfl⟩ : syracuseStep 3404993 = 2553745) B2553745
theorem B2269995 : Blo 2269435 2269995 := bstep (se 1 (by rfl) ⟨1702496, by rfl⟩ : syracuseStep 2269995 = 3404993) B3404993
theorem B4309453 : Blo 2269435 4309453 := bbase (se 3 (by rfl) ⟨808022, by rfl⟩ : syracuseStep 4309453 = 1616045) (by norm_num)
theorem B5745937 : Blo 2269435 5745937 := bstep (se 2 (by rfl) ⟨2154726, by rfl⟩ : syracuseStep 5745937 = 4309453) B4309453
theorem B7661249 : Blo 2269435 7661249 := bstep (se 2 (by rfl) ⟨2872968, by rfl⟩ : syracuseStep 7661249 = 5745937) B5745937
theorem B5107499 : Blo 2269435 5107499 := bstep (se 1 (by rfl) ⟨3830624, by rfl⟩ : syracuseStep 5107499 = 7661249) B7661249
theorem B3404999 : Blo 2269435 3404999 := bstep (se 1 (by rfl) ⟨2553749, by rfl⟩ : syracuseStep 3404999 = 5107499) B5107499
theorem B2269999 : Blo 2269435 2269999 := bstep (se 1 (by rfl) ⟨1702499, by rfl⟩ : syracuseStep 2269999 = 3404999) B3404999
theorem B3405005 : Blo 2269435 3405005 := bbase (se 3 (by rfl) ⟨638438, by rfl⟩ : syracuseStep 3405005 = 1276877) (by norm_num)
theorem B2270003 : Blo 2269435 2270003 := bstep (se 1 (by rfl) ⟨1702502, by rfl⟩ : syracuseStep 2270003 = 3405005) B3405005
theorem B5107517 : Blo 2269435 5107517 := bbase (se 3 (by rfl) ⟨957659, by rfl⟩ : syracuseStep 5107517 = 1915319) (by norm_num)
theorem B3405011 : Blo 2269435 3405011 := bstep (se 1 (by rfl) ⟨2553758, by rfl⟩ : syracuseStep 3405011 = 5107517) B5107517
theorem B2270007 : Blo 2269435 2270007 := bstep (se 1 (by rfl) ⟨1702505, by rfl⟩ : syracuseStep 2270007 = 3405011) B3405011
theorem B3830645 : Blo 2269435 3830645 := bbase (se 5 (by rfl) ⟨179561, by rfl⟩ : syracuseStep 3830645 = 359123) (by norm_num)
theorem B2553763 : Blo 2269435 2553763 := bstep (se 1 (by rfl) ⟨1915322, by rfl⟩ : syracuseStep 2553763 = 3830645) B3830645
theorem B3405017 : Blo 2269435 3405017 := bstep (se 2 (by rfl) ⟨1276881, by rfl⟩ : syracuseStep 3405017 = 2553763) B2553763
theorem B2270011 : Blo 2269435 2270011 := bstep (se 1 (by rfl) ⟨1702508, by rfl⟩ : syracuseStep 2270011 = 3405017) B3405017
theorem B20708885 : Blo 2269435 20708885 := bbase (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) (by norm_num)
theorem B13805923 : Blo 2269435 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B18407897 : Blo 2269435 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B12271931 : Blo 2269435 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B8181287 : Blo 2269435 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B5454191 : Blo 2269435 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B3636127 : Blo 2269435 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B4848169 : Blo 2269435 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B6464225 : Blo 2269435 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B17237933 : Blo 2269435 17237933 := bstep (se 3 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 17237933 = 6464225) B6464225
theorem B11491955 : Blo 2269435 11491955 := bstep (se 1 (by rfl) ⟨8618966, by rfl⟩ : syracuseStep 11491955 = 17237933) B17237933
theorem B7661303 : Blo 2269435 7661303 := bstep (se 1 (by rfl) ⟨5745977, by rfl⟩ : syracuseStep 7661303 = 11491955) B11491955
theorem B5107535 : Blo 2269435 5107535 := bstep (se 1 (by rfl) ⟨3830651, by rfl⟩ : syracuseStep 5107535 = 7661303) B7661303
theorem B3405023 : Blo 2269435 3405023 := bstep (se 1 (by rfl) ⟨2553767, by rfl⟩ : syracuseStep 3405023 = 5107535) B5107535
theorem B2270015 : Blo 2269435 2270015 := bstep (se 1 (by rfl) ⟨1702511, by rfl⟩ : syracuseStep 2270015 = 3405023) B3405023
theorem B3405029 : Blo 2269435 3405029 := bbase (se 4 (by rfl) ⟨319221, by rfl⟩ : syracuseStep 3405029 = 638443) (by norm_num)
theorem B2270019 : Blo 2269435 2270019 := bstep (se 1 (by rfl) ⟨1702514, by rfl⟩ : syracuseStep 2270019 = 3405029) B3405029
theorem B8181317 : Blo 2269435 8181317 := bbase (se 4 (by rfl) ⟨766998, by rfl⟩ : syracuseStep 8181317 = 1533997) (by norm_num)
theorem B5454211 : Blo 2269435 5454211 := bstep (se 1 (by rfl) ⟨4090658, by rfl⟩ : syracuseStep 5454211 = 8181317) B8181317
theorem B7272281 : Blo 2269435 7272281 := bstep (se 2 (by rfl) ⟨2727105, by rfl⟩ : syracuseStep 7272281 = 5454211) B5454211
theorem B4848187 : Blo 2269435 4848187 := bstep (se 1 (by rfl) ⟨3636140, by rfl⟩ : syracuseStep 4848187 = 7272281) B7272281
theorem B6464249 : Blo 2269435 6464249 := bstep (se 2 (by rfl) ⟨2424093, by rfl⟩ : syracuseStep 6464249 = 4848187) B4848187
theorem B4309499 : Blo 2269435 4309499 := bstep (se 1 (by rfl) ⟨3232124, by rfl⟩ : syracuseStep 4309499 = 6464249) B6464249
theorem B2872999 : Blo 2269435 2872999 := bstep (se 1 (by rfl) ⟨2154749, by rfl⟩ : syracuseStep 2872999 = 4309499) B4309499
theorem B3830665 : Blo 2269435 3830665 := bstep (se 2 (by rfl) ⟨1436499, by rfl⟩ : syracuseStep 3830665 = 2872999) B2872999
theorem B5107553 : Blo 2269435 5107553 := bstep (se 2 (by rfl) ⟨1915332, by rfl⟩ : syracuseStep 5107553 = 3830665) B3830665
theorem B3405035 : Blo 2269435 3405035 := bstep (se 1 (by rfl) ⟨2553776, by rfl⟩ : syracuseStep 3405035 = 5107553) B5107553
theorem B2270023 : Blo 2269435 2270023 := bstep (se 1 (by rfl) ⟨1702517, by rfl⟩ : syracuseStep 2270023 = 3405035) B3405035
theorem B2553781 : Blo 2269435 2553781 := bbase (se 5 (by rfl) ⟨119708, by rfl⟩ : syracuseStep 2553781 = 239417) (by norm_num)
theorem B3405041 : Blo 2269435 3405041 := bstep (se 2 (by rfl) ⟨1276890, by rfl⟩ : syracuseStep 3405041 = 2553781) B2553781
theorem B2270027 : Blo 2269435 2270027 := bstep (se 1 (by rfl) ⟨1702520, by rfl⟩ : syracuseStep 2270027 = 3405041) B3405041
theorem B2873009 : Blo 2269435 2873009 := bbase (se 2 (by rfl) ⟨1077378, by rfl⟩ : syracuseStep 2873009 = 2154757) (by norm_num)
theorem B7661357 : Blo 2269435 7661357 := bstep (se 3 (by rfl) ⟨1436504, by rfl⟩ : syracuseStep 7661357 = 2873009) B2873009
theorem B5107571 : Blo 2269435 5107571 := bstep (se 1 (by rfl) ⟨3830678, by rfl⟩ : syracuseStep 5107571 = 7661357) B7661357
theorem B3405047 : Blo 2269435 3405047 := bstep (se 1 (by rfl) ⟨2553785, by rfl⟩ : syracuseStep 3405047 = 5107571) B5107571
theorem B2270031 : Blo 2269435 2270031 := bstep (se 1 (by rfl) ⟨1702523, by rfl⟩ : syracuseStep 2270031 = 3405047) B3405047
theorem B3405053 : Blo 2269435 3405053 := bbase (se 3 (by rfl) ⟨638447, by rfl⟩ : syracuseStep 3405053 = 1276895) (by norm_num)
theorem B2270035 : Blo 2269435 2270035 := bstep (se 1 (by rfl) ⟨1702526, by rfl⟩ : syracuseStep 2270035 = 3405053) B3405053
theorem B5107589 : Blo 2269435 5107589 := bbase (se 4 (by rfl) ⟨478836, by rfl⟩ : syracuseStep 5107589 = 957673) (by norm_num)
theorem B3405059 : Blo 2269435 3405059 := bstep (se 1 (by rfl) ⟨2553794, by rfl⟩ : syracuseStep 3405059 = 5107589) B5107589
theorem B2270039 : Blo 2269435 2270039 := bstep (se 1 (by rfl) ⟨1702529, by rfl⟩ : syracuseStep 2270039 = 3405059) B3405059
theorem B3636173 : Blo 2269435 3636173 := bbase (se 3 (by rfl) ⟨681782, by rfl⟩ : syracuseStep 3636173 = 1363565) (by norm_num)
theorem B2424115 : Blo 2269435 2424115 := bstep (se 1 (by rfl) ⟨1818086, by rfl⟩ : syracuseStep 2424115 = 3636173) B3636173
theorem B3232153 : Blo 2269435 3232153 := bstep (se 2 (by rfl) ⟨1212057, by rfl⟩ : syracuseStep 3232153 = 2424115) B2424115
theorem B4309537 : Blo 2269435 4309537 := bstep (se 2 (by rfl) ⟨1616076, by rfl⟩ : syracuseStep 4309537 = 3232153) B3232153
theorem B5746049 : Blo 2269435 5746049 := bstep (se 2 (by rfl) ⟨2154768, by rfl⟩ : syracuseStep 5746049 = 4309537) B4309537
theorem B3830699 : Blo 2269435 3830699 := bstep (se 1 (by rfl) ⟨2873024, by rfl⟩ : syracuseStep 3830699 = 5746049) B5746049
theorem B2553799 : Blo 2269435 2553799 := bstep (se 1 (by rfl) ⟨1915349, by rfl⟩ : syracuseStep 2553799 = 3830699) B3830699
theorem B3405065 : Blo 2269435 3405065 := bstep (se 2 (by rfl) ⟨1276899, by rfl⟩ : syracuseStep 3405065 = 2553799) B2553799
theorem B2270043 : Blo 2269435 2270043 := bstep (se 1 (by rfl) ⟨1702532, by rfl⟩ : syracuseStep 2270043 = 3405065) B3405065
theorem B11492117 : Blo 2269435 11492117 := bbase (se 6 (by rfl) ⟨269346, by rfl⟩ : syracuseStep 11492117 = 538693) (by norm_num)
theorem B7661411 : Blo 2269435 7661411 := bstep (se 1 (by rfl) ⟨5746058, by rfl⟩ : syracuseStep 7661411 = 11492117) B11492117
theorem B5107607 : Blo 2269435 5107607 := bstep (se 1 (by rfl) ⟨3830705, by rfl⟩ : syracuseStep 5107607 = 7661411) B7661411
theorem B3405071 : Blo 2269435 3405071 := bstep (se 1 (by rfl) ⟨2553803, by rfl⟩ : syracuseStep 3405071 = 5107607) B5107607
theorem B2270047 : Blo 2269435 2270047 := bstep (se 1 (by rfl) ⟨1702535, by rfl⟩ : syracuseStep 2270047 = 3405071) B3405071
theorem B3405077 : Blo 2269435 3405077 := bbase (se 6 (by rfl) ⟨79806, by rfl⟩ : syracuseStep 3405077 = 159613) (by norm_num)
theorem B2270051 : Blo 2269435 2270051 := bstep (se 1 (by rfl) ⟨1702538, by rfl⟩ : syracuseStep 2270051 = 3405077) B3405077
theorem B3451541 : Blo 2269435 3451541 := bbase (se 6 (by rfl) ⟨80895, by rfl⟩ : syracuseStep 3451541 = 161791) (by norm_num)
theorem B36816437 : Blo 2269435 36816437 := bstep (se 5 (by rfl) ⟨1725770, by rfl⟩ : syracuseStep 36816437 = 3451541) B3451541
theorem B24544291 : Blo 2269435 24544291 := bstep (se 1 (by rfl) ⟨18408218, by rfl⟩ : syracuseStep 24544291 = 36816437) B36816437
theorem B32725721 : Blo 2269435 32725721 := bstep (se 2 (by rfl) ⟨12272145, by rfl⟩ : syracuseStep 32725721 = 24544291) B24544291
theorem B21817147 : Blo 2269435 21817147 := bstep (se 1 (by rfl) ⟨16362860, by rfl⟩ : syracuseStep 21817147 = 32725721) B32725721
theorem B29089529 : Blo 2269435 29089529 := bstep (se 2 (by rfl) ⟨10908573, by rfl⟩ : syracuseStep 29089529 = 21817147) B21817147
theorem B19393019 : Blo 2269435 19393019 := bstep (se 1 (by rfl) ⟨14544764, by rfl⟩ : syracuseStep 19393019 = 29089529) B29089529
theorem B12928679 : Blo 2269435 12928679 := bstep (se 1 (by rfl) ⟨9696509, by rfl⟩ : syracuseStep 12928679 = 19393019) B19393019
theorem B8619119 : Blo 2269435 8619119 := bstep (se 1 (by rfl) ⟨6464339, by rfl⟩ : syracuseStep 8619119 = 12928679) B12928679
theorem B5746079 : Blo 2269435 5746079 := bstep (se 1 (by rfl) ⟨4309559, by rfl⟩ : syracuseStep 5746079 = 8619119) B8619119
theorem B3830719 : Blo 2269435 3830719 := bstep (se 1 (by rfl) ⟨2873039, by rfl⟩ : syracuseStep 3830719 = 5746079) B5746079
theorem B5107625 : Blo 2269435 5107625 := bstep (se 2 (by rfl) ⟨1915359, by rfl⟩ : syracuseStep 5107625 = 3830719) B3830719
theorem B3405083 : Blo 2269435 3405083 := bstep (se 1 (by rfl) ⟨2553812, by rfl⟩ : syracuseStep 3405083 = 5107625) B5107625
theorem B2270055 : Blo 2269435 2270055 := bstep (se 1 (by rfl) ⟨1702541, by rfl⟩ : syracuseStep 2270055 = 3405083) B3405083
theorem B2553817 : Blo 2269435 2553817 := bbase (se 2 (by rfl) ⟨957681, by rfl⟩ : syracuseStep 2553817 = 1915363) (by norm_num)
theorem B3405089 : Blo 2269435 3405089 := bstep (se 2 (by rfl) ⟨1276908, by rfl⟩ : syracuseStep 3405089 = 2553817) B2553817
theorem B2270059 : Blo 2269435 2270059 := bstep (se 1 (by rfl) ⟨1702544, by rfl⟩ : syracuseStep 2270059 = 3405089) B3405089
theorem B3232181 : Blo 2269435 3232181 := bbase (se 5 (by rfl) ⟨151508, by rfl⟩ : syracuseStep 3232181 = 303017) (by norm_num)
theorem B8619149 : Blo 2269435 8619149 := bstep (se 3 (by rfl) ⟨1616090, by rfl⟩ : syracuseStep 8619149 = 3232181) B3232181
theorem B5746099 : Blo 2269435 5746099 := bstep (se 1 (by rfl) ⟨4309574, by rfl⟩ : syracuseStep 5746099 = 8619149) B8619149
theorem B7661465 : Blo 2269435 7661465 := bstep (se 2 (by rfl) ⟨2873049, by rfl⟩ : syracuseStep 7661465 = 5746099) B5746099
theorem B5107643 : Blo 2269435 5107643 := bstep (se 1 (by rfl) ⟨3830732, by rfl⟩ : syracuseStep 5107643 = 7661465) B7661465
theorem B3405095 : Blo 2269435 3405095 := bstep (se 1 (by rfl) ⟨2553821, by rfl⟩ : syracuseStep 3405095 = 5107643) B5107643
theorem B2270063 : Blo 2269435 2270063 := bstep (se 1 (by rfl) ⟨1702547, by rfl⟩ : syracuseStep 2270063 = 3405095) B3405095
theorem B3405101 : Blo 2269435 3405101 := bbase (se 3 (by rfl) ⟨638456, by rfl⟩ : syracuseStep 3405101 = 1276913) (by norm_num)
theorem B2270067 : Blo 2269435 2270067 := bstep (se 1 (by rfl) ⟨1702550, by rfl⟩ : syracuseStep 2270067 = 3405101) B3405101
theorem B5107661 : Blo 2269435 5107661 := bbase (se 3 (by rfl) ⟨957686, by rfl⟩ : syracuseStep 5107661 = 1915373) (by norm_num)
theorem B3405107 : Blo 2269435 3405107 := bstep (se 1 (by rfl) ⟨2553830, by rfl⟩ : syracuseStep 3405107 = 5107661) B5107661
theorem B2270071 : Blo 2269435 2270071 := bstep (se 1 (by rfl) ⟨1702553, by rfl⟩ : syracuseStep 2270071 = 3405107) B3405107
theorem B2873065 : Blo 2269435 2873065 := bbase (se 2 (by rfl) ⟨1077399, by rfl⟩ : syracuseStep 2873065 = 2154799) (by norm_num)
theorem B3830753 : Blo 2269435 3830753 := bstep (se 2 (by rfl) ⟨1436532, by rfl⟩ : syracuseStep 3830753 = 2873065) B2873065
theorem B2553835 : Blo 2269435 2553835 := bstep (se 1 (by rfl) ⟨1915376, by rfl⟩ : syracuseStep 2553835 = 3830753) B3830753
theorem B3405113 : Blo 2269435 3405113 := bstep (se 2 (by rfl) ⟨1276917, by rfl⟩ : syracuseStep 3405113 = 2553835) B2553835
theorem B2270075 : Blo 2269435 2270075 := bstep (se 1 (by rfl) ⟨1702556, by rfl⟩ : syracuseStep 2270075 = 3405113) B3405113
theorem B14544917 : Blo 2269435 14544917 := bbase (se 6 (by rfl) ⟨340896, by rfl⟩ : syracuseStep 14544917 = 681793) (by norm_num)
theorem B9696611 : Blo 2269435 9696611 := bstep (se 1 (by rfl) ⟨7272458, by rfl⟩ : syracuseStep 9696611 = 14544917) B14544917
theorem B25857629 : Blo 2269435 25857629 := bstep (se 3 (by rfl) ⟨4848305, by rfl⟩ : syracuseStep 25857629 = 9696611) B9696611
theorem B17238419 : Blo 2269435 17238419 := bstep (se 1 (by rfl) ⟨12928814, by rfl⟩ : syracuseStep 17238419 = 25857629) B25857629
theorem B11492279 : Blo 2269435 11492279 := bstep (se 1 (by rfl) ⟨8619209, by rfl⟩ : syracuseStep 11492279 = 17238419) B17238419
theorem B7661519 : Blo 2269435 7661519 := bstep (se 1 (by rfl) ⟨5746139, by rfl⟩ : syracuseStep 7661519 = 11492279) B11492279
theorem B5107679 : Blo 2269435 5107679 := bstep (se 1 (by rfl) ⟨3830759, by rfl⟩ : syracuseStep 5107679 = 7661519) B7661519
theorem B3405119 : Blo 2269435 3405119 := bstep (se 1 (by rfl) ⟨2553839, by rfl⟩ : syracuseStep 3405119 = 5107679) B5107679
theorem B2270079 : Blo 2269435 2270079 := bstep (se 1 (by rfl) ⟨1702559, by rfl⟩ : syracuseStep 2270079 = 3405119) B3405119
theorem B3405125 : Blo 2269435 3405125 := bbase (se 4 (by rfl) ⟨319230, by rfl⟩ : syracuseStep 3405125 = 638461) (by norm_num)
theorem B2270083 : Blo 2269435 2270083 := bstep (se 1 (by rfl) ⟨1702562, by rfl⟩ : syracuseStep 2270083 = 3405125) B3405125
theorem B3830773 : Blo 2269435 3830773 := bbase (se 5 (by rfl) ⟨179567, by rfl⟩ : syracuseStep 3830773 = 359135) (by norm_num)
theorem B5107697 : Blo 2269435 5107697 := bstep (se 2 (by rfl) ⟨1915386, by rfl⟩ : syracuseStep 5107697 = 3830773) B3830773
theorem B3405131 : Blo 2269435 3405131 := bstep (se 1 (by rfl) ⟨2553848, by rfl⟩ : syracuseStep 3405131 = 5107697) B5107697
theorem B2270087 : Blo 2269435 2270087 := bstep (se 1 (by rfl) ⟨1702565, by rfl⟩ : syracuseStep 2270087 = 3405131) B3405131
theorem B2553853 : Blo 2269435 2553853 := bbase (se 3 (by rfl) ⟨478847, by rfl⟩ : syracuseStep 2553853 = 957695) (by norm_num)
theorem B3405137 : Blo 2269435 3405137 := bstep (se 2 (by rfl) ⟨1276926, by rfl⟩ : syracuseStep 3405137 = 2553853) B2553853
theorem B2270091 : Blo 2269435 2270091 := bstep (se 1 (by rfl) ⟨1702568, by rfl⟩ : syracuseStep 2270091 = 3405137) B3405137
theorem B7661573 : Blo 2269435 7661573 := bbase (se 4 (by rfl) ⟨718272, by rfl⟩ : syracuseStep 7661573 = 1436545) (by norm_num)
theorem B5107715 : Blo 2269435 5107715 := bstep (se 1 (by rfl) ⟨3830786, by rfl⟩ : syracuseStep 5107715 = 7661573) B7661573
theorem B3405143 : Blo 2269435 3405143 := bstep (se 1 (by rfl) ⟨2553857, by rfl⟩ : syracuseStep 3405143 = 5107715) B5107715
theorem B2270095 : Blo 2269435 2270095 := bstep (se 1 (by rfl) ⟨1702571, by rfl⟩ : syracuseStep 2270095 = 3405143) B3405143
theorem B3405149 : Blo 2269435 3405149 := bbase (se 3 (by rfl) ⟨638465, by rfl⟩ : syracuseStep 3405149 = 1276931) (by norm_num)
theorem B2270099 : Blo 2269435 2270099 := bstep (se 1 (by rfl) ⟨1702574, by rfl⟩ : syracuseStep 2270099 = 3405149) B3405149
theorem B5107733 : Blo 2269435 5107733 := bbase (se 6 (by rfl) ⟨119712, by rfl⟩ : syracuseStep 5107733 = 239425) (by norm_num)
theorem B3405155 : Blo 2269435 3405155 := bstep (se 1 (by rfl) ⟨2553866, by rfl⟩ : syracuseStep 3405155 = 5107733) B5107733
theorem B2270103 : Blo 2269435 2270103 := bstep (se 1 (by rfl) ⟨1702577, by rfl⟩ : syracuseStep 2270103 = 3405155) B3405155
theorem B8619317 : Blo 2269435 8619317 := bbase (se 5 (by rfl) ⟨404030, by rfl⟩ : syracuseStep 8619317 = 808061) (by norm_num)
theorem B5746211 : Blo 2269435 5746211 := bstep (se 1 (by rfl) ⟨4309658, by rfl⟩ : syracuseStep 5746211 = 8619317) B8619317
theorem B3830807 : Blo 2269435 3830807 := bstep (se 1 (by rfl) ⟨2873105, by rfl⟩ : syracuseStep 3830807 = 5746211) B5746211
theorem B2553871 : Blo 2269435 2553871 := bstep (se 1 (by rfl) ⟨1915403, by rfl⟩ : syracuseStep 2553871 = 3830807) B3830807
theorem B3405161 : Blo 2269435 3405161 := bstep (se 2 (by rfl) ⟨1276935, by rfl⟩ : syracuseStep 3405161 = 2553871) B2553871
theorem B2270107 : Blo 2269435 2270107 := bstep (se 1 (by rfl) ⟨1702580, by rfl⟩ : syracuseStep 2270107 = 3405161) B3405161
theorem B2301085 : Blo 2269435 2301085 := bbase (se 3 (by rfl) ⟨431453, by rfl⟩ : syracuseStep 2301085 = 862907) (by norm_num)
theorem B3068113 : Blo 2269435 3068113 := bstep (se 2 (by rfl) ⟨1150542, by rfl⟩ : syracuseStep 3068113 = 2301085) B2301085
theorem B4090817 : Blo 2269435 4090817 := bstep (se 2 (by rfl) ⟨1534056, by rfl⟩ : syracuseStep 4090817 = 3068113) B3068113
theorem B2727211 : Blo 2269435 2727211 := bstep (se 1 (by rfl) ⟨2045408, by rfl⟩ : syracuseStep 2727211 = 4090817) B4090817
theorem B3636281 : Blo 2269435 3636281 := bstep (se 2 (by rfl) ⟨1363605, by rfl⟩ : syracuseStep 3636281 = 2727211) B2727211
theorem B2424187 : Blo 2269435 2424187 := bstep (se 1 (by rfl) ⟨1818140, by rfl⟩ : syracuseStep 2424187 = 3636281) B3636281
theorem B12928997 : Blo 2269435 12928997 := bstep (se 4 (by rfl) ⟨1212093, by rfl⟩ : syracuseStep 12928997 = 2424187) B2424187
theorem B8619331 : Blo 2269435 8619331 := bstep (se 1 (by rfl) ⟨6464498, by rfl⟩ : syracuseStep 8619331 = 12928997) B12928997
theorem B11492441 : Blo 2269435 11492441 := bstep (se 2 (by rfl) ⟨4309665, by rfl⟩ : syracuseStep 11492441 = 8619331) B8619331
theorem B7661627 : Blo 2269435 7661627 := bstep (se 1 (by rfl) ⟨5746220, by rfl⟩ : syracuseStep 7661627 = 11492441) B11492441
theorem B5107751 : Blo 2269435 5107751 := bstep (se 1 (by rfl) ⟨3830813, by rfl⟩ : syracuseStep 5107751 = 7661627) B7661627
theorem B3405167 : Blo 2269435 3405167 := bstep (se 1 (by rfl) ⟨2553875, by rfl⟩ : syracuseStep 3405167 = 5107751) B5107751
theorem B2270111 : Blo 2269435 2270111 := bstep (se 1 (by rfl) ⟨1702583, by rfl⟩ : syracuseStep 2270111 = 3405167) B3405167
theorem B3405173 : Blo 2269435 3405173 := bbase (se 5 (by rfl) ⟨159617, by rfl⟩ : syracuseStep 3405173 = 319235) (by norm_num)
theorem B2270115 : Blo 2269435 2270115 := bstep (se 1 (by rfl) ⟨1702586, by rfl⟩ : syracuseStep 2270115 = 3405173) B3405173
theorem B3232261 : Blo 2269435 3232261 := bbase (se 4 (by rfl) ⟨303024, by rfl⟩ : syracuseStep 3232261 = 606049) (by norm_num)
theorem B4309681 : Blo 2269435 4309681 := bstep (se 2 (by rfl) ⟨1616130, by rfl⟩ : syracuseStep 4309681 = 3232261) B3232261
theorem B5746241 : Blo 2269435 5746241 := bstep (se 2 (by rfl) ⟨2154840, by rfl⟩ : syracuseStep 5746241 = 4309681) B4309681
theorem B3830827 : Blo 2269435 3830827 := bstep (se 1 (by rfl) ⟨2873120, by rfl⟩ : syracuseStep 3830827 = 5746241) B5746241
theorem B5107769 : Blo 2269435 5107769 := bstep (se 2 (by rfl) ⟨1915413, by rfl⟩ : syracuseStep 5107769 = 3830827) B3830827
theorem B3405179 : Blo 2269435 3405179 := bstep (se 1 (by rfl) ⟨2553884, by rfl⟩ : syracuseStep 3405179 = 5107769) B5107769
theorem B2270119 : Blo 2269435 2270119 := bstep (se 1 (by rfl) ⟨1702589, by rfl⟩ : syracuseStep 2270119 = 3405179) B3405179
theorem B2553889 : Blo 2269435 2553889 := bbase (se 2 (by rfl) ⟨957708, by rfl⟩ : syracuseStep 2553889 = 1915417) (by norm_num)
theorem B3405185 : Blo 2269435 3405185 := bstep (se 2 (by rfl) ⟨1276944, by rfl⟩ : syracuseStep 3405185 = 2553889) B2553889
theorem B2270123 : Blo 2269435 2270123 := bstep (se 1 (by rfl) ⟨1702592, by rfl⟩ : syracuseStep 2270123 = 3405185) B3405185
theorem B5746261 : Blo 2269435 5746261 := bbase (se 8 (by rfl) ⟨33669, by rfl⟩ : syracuseStep 5746261 = 67339) (by norm_num)
theorem B7661681 : Blo 2269435 7661681 := bstep (se 2 (by rfl) ⟨2873130, by rfl⟩ : syracuseStep 7661681 = 5746261) B5746261
theorem B5107787 : Blo 2269435 5107787 := bstep (se 1 (by rfl) ⟨3830840, by rfl⟩ : syracuseStep 5107787 = 7661681) B7661681
theorem B3405191 : Blo 2269435 3405191 := bstep (se 1 (by rfl) ⟨2553893, by rfl⟩ : syracuseStep 3405191 = 5107787) B5107787
theorem B2270127 : Blo 2269435 2270127 := bstep (se 1 (by rfl) ⟨1702595, by rfl⟩ : syracuseStep 2270127 = 3405191) B3405191
theorem B3405197 : Blo 2269435 3405197 := bbase (se 3 (by rfl) ⟨638474, by rfl⟩ : syracuseStep 3405197 = 1276949) (by norm_num)
theorem B2270131 : Blo 2269435 2270131 := bstep (se 1 (by rfl) ⟨1702598, by rfl⟩ : syracuseStep 2270131 = 3405197) B3405197
theorem B5107805 : Blo 2269435 5107805 := bbase (se 3 (by rfl) ⟨957713, by rfl⟩ : syracuseStep 5107805 = 1915427) (by norm_num)
theorem B3405203 : Blo 2269435 3405203 := bstep (se 1 (by rfl) ⟨2553902, by rfl⟩ : syracuseStep 3405203 = 5107805) B5107805
theorem B2270135 : Blo 2269435 2270135 := bstep (se 1 (by rfl) ⟨1702601, by rfl⟩ : syracuseStep 2270135 = 3405203) B3405203
theorem B3830861 : Blo 2269435 3830861 := bbase (se 3 (by rfl) ⟨718286, by rfl⟩ : syracuseStep 3830861 = 1436573) (by norm_num)
theorem B2553907 : Blo 2269435 2553907 := bstep (se 1 (by rfl) ⟨1915430, by rfl⟩ : syracuseStep 2553907 = 3830861) B3830861
theorem B3405209 : Blo 2269435 3405209 := bstep (se 2 (by rfl) ⟨1276953, by rfl⟩ : syracuseStep 3405209 = 2553907) B2553907
theorem B2270139 : Blo 2269435 2270139 := bstep (se 1 (by rfl) ⟨1702604, by rfl⟩ : syracuseStep 2270139 = 3405209) B3405209
theorem B6903349 : Blo 2269435 6903349 := bbase (se 5 (by rfl) ⟨323594, by rfl⟩ : syracuseStep 6903349 = 647189) (by norm_num)
theorem B36817861 : Blo 2269435 36817861 := bstep (se 4 (by rfl) ⟨3451674, by rfl⟩ : syracuseStep 36817861 = 6903349) B6903349
theorem B49090481 : Blo 2269435 49090481 := bstep (se 2 (by rfl) ⟨18408930, by rfl⟩ : syracuseStep 49090481 = 36817861) B36817861
theorem B32726987 : Blo 2269435 32726987 := bstep (se 1 (by rfl) ⟨24545240, by rfl⟩ : syracuseStep 32726987 = 49090481) B49090481
theorem B21817991 : Blo 2269435 21817991 := bstep (se 1 (by rfl) ⟨16363493, by rfl⟩ : syracuseStep 21817991 = 32726987) B32726987
theorem B14545327 : Blo 2269435 14545327 := bstep (se 1 (by rfl) ⟨10908995, by rfl⟩ : syracuseStep 14545327 = 21817991) B21817991
theorem B19393769 : Blo 2269435 19393769 := bstep (se 2 (by rfl) ⟨7272663, by rfl⟩ : syracuseStep 19393769 = 14545327) B14545327
theorem B12929179 : Blo 2269435 12929179 := bstep (se 1 (by rfl) ⟨9696884, by rfl⟩ : syracuseStep 12929179 = 19393769) B19393769
theorem B17238905 : Blo 2269435 17238905 := bstep (se 2 (by rfl) ⟨6464589, by rfl⟩ : syracuseStep 17238905 = 12929179) B12929179
theorem B11492603 : Blo 2269435 11492603 := bstep (se 1 (by rfl) ⟨8619452, by rfl⟩ : syracuseStep 11492603 = 17238905) B17238905
theorem B7661735 : Blo 2269435 7661735 := bstep (se 1 (by rfl) ⟨5746301, by rfl⟩ : syracuseStep 7661735 = 11492603) B11492603
theorem B5107823 : Blo 2269435 5107823 := bstep (se 1 (by rfl) ⟨3830867, by rfl⟩ : syracuseStep 5107823 = 7661735) B7661735
theorem B3405215 : Blo 2269435 3405215 := bstep (se 1 (by rfl) ⟨2553911, by rfl⟩ : syracuseStep 3405215 = 5107823) B5107823
theorem B2270143 : Blo 2269435 2270143 := bstep (se 1 (by rfl) ⟨1702607, by rfl⟩ : syracuseStep 2270143 = 3405215) B3405215
theorem B3405221 : Blo 2269435 3405221 := bbase (se 4 (by rfl) ⟨319239, by rfl⟩ : syracuseStep 3405221 = 638479) (by norm_num)
theorem B2270147 : Blo 2269435 2270147 := bstep (se 1 (by rfl) ⟨1702610, by rfl⟩ : syracuseStep 2270147 = 3405221) B3405221
theorem B2873161 : Blo 2269435 2873161 := bbase (se 2 (by rfl) ⟨1077435, by rfl⟩ : syracuseStep 2873161 = 2154871) (by norm_num)
theorem B3830881 : Blo 2269435 3830881 := bstep (se 2 (by rfl) ⟨1436580, by rfl⟩ : syracuseStep 3830881 = 2873161) B2873161
theorem B5107841 : Blo 2269435 5107841 := bstep (se 2 (by rfl) ⟨1915440, by rfl⟩ : syracuseStep 5107841 = 3830881) B3830881
theorem B3405227 : Blo 2269435 3405227 := bstep (se 1 (by rfl) ⟨2553920, by rfl⟩ : syracuseStep 3405227 = 5107841) B5107841
theorem B2270151 : Blo 2269435 2270151 := bstep (se 1 (by rfl) ⟨1702613, by rfl⟩ : syracuseStep 2270151 = 3405227) B3405227
theorem B2553925 : Blo 2269435 2553925 := bbase (se 4 (by rfl) ⟨239430, by rfl⟩ : syracuseStep 2553925 = 478861) (by norm_num)
theorem B3405233 : Blo 2269435 3405233 := bstep (se 2 (by rfl) ⟨1276962, by rfl⟩ : syracuseStep 3405233 = 2553925) B2553925
theorem B2270155 : Blo 2269435 2270155 := bstep (se 1 (by rfl) ⟨1702616, by rfl⟩ : syracuseStep 2270155 = 3405233) B3405233
theorem B4309757 : Blo 2269435 4309757 := bbase (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) (by norm_num)
theorem B2873171 : Blo 2269435 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B7661789 : Blo 2269435 7661789 := bstep (se 3 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 7661789 = 2873171) B2873171
theorem B5107859 : Blo 2269435 5107859 := bstep (se 1 (by rfl) ⟨3830894, by rfl⟩ : syracuseStep 5107859 = 7661789) B7661789
theorem B3405239 : Blo 2269435 3405239 := bstep (se 1 (by rfl) ⟨2553929, by rfl⟩ : syracuseStep 3405239 = 5107859) B5107859
theorem B2270159 : Blo 2269435 2270159 := bstep (se 1 (by rfl) ⟨1702619, by rfl⟩ : syracuseStep 2270159 = 3405239) B3405239
theorem B3405245 : Blo 2269435 3405245 := bbase (se 3 (by rfl) ⟨638483, by rfl⟩ : syracuseStep 3405245 = 1276967) (by norm_num)
theorem B2270163 : Blo 2269435 2270163 := bstep (se 1 (by rfl) ⟨1702622, by rfl⟩ : syracuseStep 2270163 = 3405245) B3405245
theorem B5107877 : Blo 2269435 5107877 := bbase (se 4 (by rfl) ⟨478863, by rfl⟩ : syracuseStep 5107877 = 957727) (by norm_num)
theorem B3405251 : Blo 2269435 3405251 := bstep (se 1 (by rfl) ⟨2553938, by rfl⟩ : syracuseStep 3405251 = 5107877) B5107877
theorem B2270167 : Blo 2269435 2270167 := bstep (se 1 (by rfl) ⟨1702625, by rfl⟩ : syracuseStep 2270167 = 3405251) B3405251
theorem B5746373 : Blo 2269435 5746373 := bbase (se 4 (by rfl) ⟨538722, by rfl⟩ : syracuseStep 5746373 = 1077445) (by norm_num)
theorem B3830915 : Blo 2269435 3830915 := bstep (se 1 (by rfl) ⟨2873186, by rfl⟩ : syracuseStep 3830915 = 5746373) B5746373
theorem B2553943 : Blo 2269435 2553943 := bstep (se 1 (by rfl) ⟨1915457, by rfl⟩ : syracuseStep 2553943 = 3830915) B3830915
theorem B3405257 : Blo 2269435 3405257 := bstep (se 2 (by rfl) ⟨1276971, by rfl⟩ : syracuseStep 3405257 = 2553943) B2553943
theorem B2270171 : Blo 2269435 2270171 := bstep (se 1 (by rfl) ⟨1702628, by rfl⟩ : syracuseStep 2270171 = 3405257) B3405257
theorem B44231957 : Blo 2269435 44231957 := bbase (se 6 (by rfl) ⟨1036686, by rfl⟩ : syracuseStep 44231957 = 2073373) (by norm_num)
theorem B29487971 : Blo 2269435 29487971 := bstep (se 1 (by rfl) ⟨22115978, by rfl⟩ : syracuseStep 29487971 = 44231957) B44231957
theorem B19658647 : Blo 2269435 19658647 := bstep (se 1 (by rfl) ⟨14743985, by rfl⟩ : syracuseStep 19658647 = 29487971) B29487971
theorem B26211529 : Blo 2269435 26211529 := bstep (se 2 (by rfl) ⟨9829323, by rfl⟩ : syracuseStep 26211529 = 19658647) B19658647
theorem B34948705 : Blo 2269435 34948705 := bstep (se 2 (by rfl) ⟨13105764, by rfl⟩ : syracuseStep 34948705 = 26211529) B26211529
theorem B46598273 : Blo 2269435 46598273 := bstep (se 2 (by rfl) ⟨17474352, by rfl⟩ : syracuseStep 46598273 = 34948705) B34948705
theorem B31065515 : Blo 2269435 31065515 := bstep (se 1 (by rfl) ⟨23299136, by rfl⟩ : syracuseStep 31065515 = 46598273) B46598273
theorem B20710343 : Blo 2269435 20710343 := bstep (se 1 (by rfl) ⟨15532757, by rfl⟩ : syracuseStep 20710343 = 31065515) B31065515
theorem B55227581 : Blo 2269435 55227581 := bstep (se 3 (by rfl) ⟨10355171, by rfl⟩ : syracuseStep 55227581 = 20710343) B20710343
theorem B36818387 : Blo 2269435 36818387 := bstep (se 1 (by rfl) ⟨27613790, by rfl⟩ : syracuseStep 36818387 = 55227581) B55227581
theorem B24545591 : Blo 2269435 24545591 := bstep (se 1 (by rfl) ⟨18409193, by rfl⟩ : syracuseStep 24545591 = 36818387) B36818387
theorem B16363727 : Blo 2269435 16363727 := bstep (se 1 (by rfl) ⟨12272795, by rfl⟩ : syracuseStep 16363727 = 24545591) B24545591
theorem B10909151 : Blo 2269435 10909151 := bstep (se 1 (by rfl) ⟨8181863, by rfl⟩ : syracuseStep 10909151 = 16363727) B16363727
theorem B7272767 : Blo 2269435 7272767 := bstep (se 1 (by rfl) ⟨5454575, by rfl⟩ : syracuseStep 7272767 = 10909151) B10909151
theorem B4848511 : Blo 2269435 4848511 := bstep (se 1 (by rfl) ⟨3636383, by rfl⟩ : syracuseStep 4848511 = 7272767) B7272767
theorem B6464681 : Blo 2269435 6464681 := bstep (se 2 (by rfl) ⟨2424255, by rfl⟩ : syracuseStep 6464681 = 4848511) B4848511
theorem B4309787 : Blo 2269435 4309787 := bstep (se 1 (by rfl) ⟨3232340, by rfl⟩ : syracuseStep 4309787 = 6464681) B6464681
theorem B11492765 : Blo 2269435 11492765 := bstep (se 3 (by rfl) ⟨2154893, by rfl⟩ : syracuseStep 11492765 = 4309787) B4309787
theorem B7661843 : Blo 2269435 7661843 := bstep (se 1 (by rfl) ⟨5746382, by rfl⟩ : syracuseStep 7661843 = 11492765) B11492765
theorem B5107895 : Blo 2269435 5107895 := bstep (se 1 (by rfl) ⟨3830921, by rfl⟩ : syracuseStep 5107895 = 7661843) B7661843
theorem B3405263 : Blo 2269435 3405263 := bstep (se 1 (by rfl) ⟨2553947, by rfl⟩ : syracuseStep 3405263 = 5107895) B5107895
theorem B2270175 : Blo 2269435 2270175 := bstep (se 1 (by rfl) ⟨1702631, by rfl⟩ : syracuseStep 2270175 = 3405263) B3405263
theorem B3405269 : Blo 2269435 3405269 := bbase (se 7 (by rfl) ⟨39905, by rfl⟩ : syracuseStep 3405269 = 79811) (by norm_num)
theorem B2270179 : Blo 2269435 2270179 := bstep (se 1 (by rfl) ⟨1702634, by rfl⟩ : syracuseStep 2270179 = 3405269) B3405269
theorem B8619605 : Blo 2269435 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B5746403 : Blo 2269435 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B3830935 : Blo 2269435 3830935 := bstep (se 1 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 3830935 = 5746403) B5746403
theorem B5107913 : Blo 2269435 5107913 := bstep (se 2 (by rfl) ⟨1915467, by rfl⟩ : syracuseStep 5107913 = 3830935) B3830935
theorem B3405275 : Blo 2269435 3405275 := bstep (se 1 (by rfl) ⟨2553956, by rfl⟩ : syracuseStep 3405275 = 5107913) B5107913
theorem B2270183 : Blo 2269435 2270183 := bstep (se 1 (by rfl) ⟨1702637, by rfl⟩ : syracuseStep 2270183 = 3405275) B3405275
theorem B2553961 : Blo 2269435 2553961 := bbase (se 2 (by rfl) ⟨957735, by rfl⟩ : syracuseStep 2553961 = 1915471) (by norm_num)
theorem B3405281 : Blo 2269435 3405281 := bstep (se 2 (by rfl) ⟨1276980, by rfl⟩ : syracuseStep 3405281 = 2553961) B2553961
theorem B2270187 : Blo 2269435 2270187 := bstep (se 1 (by rfl) ⟨1702640, by rfl⟩ : syracuseStep 2270187 = 3405281) B3405281
theorem B3068221 : Blo 2269435 3068221 := bbase (se 3 (by rfl) ⟨575291, by rfl⟩ : syracuseStep 3068221 = 1150583) (by norm_num)
theorem B4090961 : Blo 2269435 4090961 := bstep (se 2 (by rfl) ⟨1534110, by rfl⟩ : syracuseStep 4090961 = 3068221) B3068221
theorem B2727307 : Blo 2269435 2727307 := bstep (se 1 (by rfl) ⟨2045480, by rfl⟩ : syracuseStep 2727307 = 4090961) B4090961
theorem B3636409 : Blo 2269435 3636409 := bstep (se 2 (by rfl) ⟨1363653, by rfl⟩ : syracuseStep 3636409 = 2727307) B2727307
theorem B4848545 : Blo 2269435 4848545 := bstep (se 2 (by rfl) ⟨1818204, by rfl⟩ : syracuseStep 4848545 = 3636409) B3636409
theorem B12929453 : Blo 2269435 12929453 := bstep (se 3 (by rfl) ⟨2424272, by rfl⟩ : syracuseStep 12929453 = 4848545) B4848545
theorem B8619635 : Blo 2269435 8619635 := bstep (se 1 (by rfl) ⟨6464726, by rfl⟩ : syracuseStep 8619635 = 12929453) B12929453
theorem B5746423 : Blo 2269435 5746423 := bstep (se 1 (by rfl) ⟨4309817, by rfl⟩ : syracuseStep 5746423 = 8619635) B8619635
theorem B7661897 : Blo 2269435 7661897 := bstep (se 2 (by rfl) ⟨2873211, by rfl⟩ : syracuseStep 7661897 = 5746423) B5746423
theorem B5107931 : Blo 2269435 5107931 := bstep (se 1 (by rfl) ⟨3830948, by rfl⟩ : syracuseStep 5107931 = 7661897) B7661897
theorem B3405287 : Blo 2269435 3405287 := bstep (se 1 (by rfl) ⟨2553965, by rfl⟩ : syracuseStep 3405287 = 5107931) B5107931
theorem B2270191 : Blo 2269435 2270191 := bstep (se 1 (by rfl) ⟨1702643, by rfl⟩ : syracuseStep 2270191 = 3405287) B3405287
theorem B3405293 : Blo 2269435 3405293 := bbase (se 3 (by rfl) ⟨638492, by rfl⟩ : syracuseStep 3405293 = 1276985) (by norm_num)
theorem B2270195 : Blo 2269435 2270195 := bstep (se 1 (by rfl) ⟨1702646, by rfl⟩ : syracuseStep 2270195 = 3405293) B3405293
theorem B5107949 : Blo 2269435 5107949 := bbase (se 3 (by rfl) ⟨957740, by rfl⟩ : syracuseStep 5107949 = 1915481) (by norm_num)
theorem B3405299 : Blo 2269435 3405299 := bstep (se 1 (by rfl) ⟨2553974, by rfl⟩ : syracuseStep 3405299 = 5107949) B5107949
theorem B2270199 : Blo 2269435 2270199 := bstep (se 1 (by rfl) ⟨1702649, by rfl⟩ : syracuseStep 2270199 = 3405299) B3405299
theorem B3232381 : Blo 2269435 3232381 := bbase (se 3 (by rfl) ⟨606071, by rfl⟩ : syracuseStep 3232381 = 1212143) (by norm_num)
theorem B4309841 : Blo 2269435 4309841 := bstep (se 2 (by rfl) ⟨1616190, by rfl⟩ : syracuseStep 4309841 = 3232381) B3232381
theorem B2873227 : Blo 2269435 2873227 := bstep (se 1 (by rfl) ⟨2154920, by rfl⟩ : syracuseStep 2873227 = 4309841) B4309841
theorem B3830969 : Blo 2269435 3830969 := bstep (se 2 (by rfl) ⟨1436613, by rfl⟩ : syracuseStep 3830969 = 2873227) B2873227
theorem B2553979 : Blo 2269435 2553979 := bstep (se 1 (by rfl) ⟨1915484, by rfl⟩ : syracuseStep 2553979 = 3830969) B3830969
theorem B3405305 : Blo 2269435 3405305 := bstep (se 2 (by rfl) ⟨1276989, by rfl⟩ : syracuseStep 3405305 = 2553979) B2553979
theorem B2270203 : Blo 2269435 2270203 := bstep (se 1 (by rfl) ⟨1702652, by rfl⟩ : syracuseStep 2270203 = 3405305) B3405305
theorem B9204725 : Blo 2269435 9204725 := bbase (se 5 (by rfl) ⟨431471, by rfl⟩ : syracuseStep 9204725 = 862943) (by norm_num)
theorem B6136483 : Blo 2269435 6136483 := bstep (se 1 (by rfl) ⟨4602362, by rfl⟩ : syracuseStep 6136483 = 9204725) B9204725
theorem B8181977 : Blo 2269435 8181977 := bstep (se 2 (by rfl) ⟨3068241, by rfl⟩ : syracuseStep 8181977 = 6136483) B6136483
theorem B87274421 : Blo 2269435 87274421 := bstep (se 5 (by rfl) ⟨4090988, by rfl⟩ : syracuseStep 87274421 = 8181977) B8181977
theorem B58182947 : Blo 2269435 58182947 := bstep (se 1 (by rfl) ⟨43637210, by rfl⟩ : syracuseStep 58182947 = 87274421) B87274421
theorem B38788631 : Blo 2269435 38788631 := bstep (se 1 (by rfl) ⟨29091473, by rfl⟩ : syracuseStep 38788631 = 58182947) B58182947
theorem B25859087 : Blo 2269435 25859087 := bstep (se 1 (by rfl) ⟨19394315, by rfl⟩ : syracuseStep 25859087 = 38788631) B38788631
theorem B17239391 : Blo 2269435 17239391 := bstep (se 1 (by rfl) ⟨12929543, by rfl⟩ : syracuseStep 17239391 = 25859087) B25859087
theorem B11492927 : Blo 2269435 11492927 := bstep (se 1 (by rfl) ⟨8619695, by rfl⟩ : syracuseStep 11492927 = 17239391) B17239391
theorem B7661951 : Blo 2269435 7661951 := bstep (se 1 (by rfl) ⟨5746463, by rfl⟩ : syracuseStep 7661951 = 11492927) B11492927
theorem B5107967 : Blo 2269435 5107967 := bstep (se 1 (by rfl) ⟨3830975, by rfl⟩ : syracuseStep 5107967 = 7661951) B7661951
theorem B3405311 : Blo 2269435 3405311 := bstep (se 1 (by rfl) ⟨2553983, by rfl⟩ : syracuseStep 3405311 = 5107967) B5107967
theorem B2270207 : Blo 2269435 2270207 := bstep (se 1 (by rfl) ⟨1702655, by rfl⟩ : syracuseStep 2270207 = 3405311) B3405311
theorem B3405317 : Blo 2269435 3405317 := bbase (se 4 (by rfl) ⟨319248, by rfl⟩ : syracuseStep 3405317 = 638497) (by norm_num)
theorem B2270211 : Blo 2269435 2270211 := bstep (se 1 (by rfl) ⟨1702658, by rfl⟩ : syracuseStep 2270211 = 3405317) B3405317
theorem B3830989 : Blo 2269435 3830989 := bbase (se 3 (by rfl) ⟨718310, by rfl⟩ : syracuseStep 3830989 = 1436621) (by norm_num)
theorem B5107985 : Blo 2269435 5107985 := bstep (se 2 (by rfl) ⟨1915494, by rfl⟩ : syracuseStep 5107985 = 3830989) B3830989
theorem B3405323 : Blo 2269435 3405323 := bstep (se 1 (by rfl) ⟨2553992, by rfl⟩ : syracuseStep 3405323 = 5107985) B5107985
theorem B2270215 : Blo 2269435 2270215 := bstep (se 1 (by rfl) ⟨1702661, by rfl⟩ : syracuseStep 2270215 = 3405323) B3405323
theorem B2553997 : Blo 2269435 2553997 := bbase (se 3 (by rfl) ⟨478874, by rfl⟩ : syracuseStep 2553997 = 957749) (by norm_num)
theorem B3405329 : Blo 2269435 3405329 := bstep (se 2 (by rfl) ⟨1276998, by rfl⟩ : syracuseStep 3405329 = 2553997) B2553997
theorem B2270219 : Blo 2269435 2270219 := bstep (se 1 (by rfl) ⟨1702664, by rfl⟩ : syracuseStep 2270219 = 3405329) B3405329
theorem B7662005 : Blo 2269435 7662005 := bbase (se 5 (by rfl) ⟨359156, by rfl⟩ : syracuseStep 7662005 = 718313) (by norm_num)
theorem B5108003 : Blo 2269435 5108003 := bstep (se 1 (by rfl) ⟨3831002, by rfl⟩ : syracuseStep 5108003 = 7662005) B7662005
theorem B3405335 : Blo 2269435 3405335 := bstep (se 1 (by rfl) ⟨2554001, by rfl⟩ : syracuseStep 3405335 = 5108003) B5108003
theorem B2270223 : Blo 2269435 2270223 := bstep (se 1 (by rfl) ⟨1702667, by rfl⟩ : syracuseStep 2270223 = 3405335) B3405335
theorem B3405341 : Blo 2269435 3405341 := bbase (se 3 (by rfl) ⟨638501, by rfl⟩ : syracuseStep 3405341 = 1277003) (by norm_num)
theorem B2270227 : Blo 2269435 2270227 := bstep (se 1 (by rfl) ⟨1702670, by rfl⟩ : syracuseStep 2270227 = 3405341) B3405341
theorem B5108021 : Blo 2269435 5108021 := bbase (se 5 (by rfl) ⟨239438, by rfl⟩ : syracuseStep 5108021 = 478877) (by norm_num)
theorem B3405347 : Blo 2269435 3405347 := bstep (se 1 (by rfl) ⟨2554010, by rfl⟩ : syracuseStep 3405347 = 5108021) B5108021
theorem B2270231 : Blo 2269435 2270231 := bstep (se 1 (by rfl) ⟨1702673, by rfl⟩ : syracuseStep 2270231 = 3405347) B3405347
theorem B2802289 : Blo 2269435 2802289 := bbase (se 2 (by rfl) ⟨1050858, by rfl⟩ : syracuseStep 2802289 = 2101717) (by norm_num)
theorem B3736385 : Blo 2269435 3736385 := bstep (se 2 (by rfl) ⟨1401144, by rfl⟩ : syracuseStep 3736385 = 2802289) B2802289
theorem B2490923 : Blo 2269435 2490923 := bstep (se 1 (by rfl) ⟨1868192, by rfl⟩ : syracuseStep 2490923 = 3736385) B3736385
theorem B6642461 : Blo 2269435 6642461 := bstep (se 3 (by rfl) ⟨1245461, by rfl⟩ : syracuseStep 6642461 = 2490923) B2490923
theorem B4428307 : Blo 2269435 4428307 := bstep (se 1 (by rfl) ⟨3321230, by rfl⟩ : syracuseStep 4428307 = 6642461) B6642461
theorem B23617637 : Blo 2269435 23617637 := bstep (se 4 (by rfl) ⟨2214153, by rfl⟩ : syracuseStep 23617637 = 4428307) B4428307
theorem B15745091 : Blo 2269435 15745091 := bstep (se 1 (by rfl) ⟨11808818, by rfl⟩ : syracuseStep 15745091 = 23617637) B23617637
theorem B41986909 : Blo 2269435 41986909 := bstep (se 3 (by rfl) ⟨7872545, by rfl⟩ : syracuseStep 41986909 = 15745091) B15745091
theorem B55982545 : Blo 2269435 55982545 := bstep (se 2 (by rfl) ⟨20993454, by rfl⟩ : syracuseStep 55982545 = 41986909) B41986909
theorem B298573573 : Blo 2269435 298573573 := bstep (se 4 (by rfl) ⟨27991272, by rfl⟩ : syracuseStep 298573573 = 55982545) B55982545
theorem B398098097 : Blo 2269435 398098097 := bstep (se 2 (by rfl) ⟨149286786, by rfl⟩ : syracuseStep 398098097 = 298573573) B298573573
theorem B265398731 : Blo 2269435 265398731 := bstep (se 1 (by rfl) ⟨199049048, by rfl⟩ : syracuseStep 265398731 = 398098097) B398098097
theorem B176932487 : Blo 2269435 176932487 := bstep (se 1 (by rfl) ⟨132699365, by rfl⟩ : syracuseStep 176932487 = 265398731) B265398731
theorem B117954991 : Blo 2269435 117954991 := bstep (se 1 (by rfl) ⟨88466243, by rfl⟩ : syracuseStep 117954991 = 176932487) B176932487
theorem B157273321 : Blo 2269435 157273321 := bstep (se 2 (by rfl) ⟨58977495, by rfl⟩ : syracuseStep 157273321 = 117954991) B117954991
theorem B209697761 : Blo 2269435 209697761 := bstep (se 2 (by rfl) ⟨78636660, by rfl⟩ : syracuseStep 209697761 = 157273321) B157273321
theorem B559194029 : Blo 2269435 559194029 := bstep (se 3 (by rfl) ⟨104848880, by rfl⟩ : syracuseStep 559194029 = 209697761) B209697761
theorem B372796019 : Blo 2269435 372796019 := bstep (se 1 (by rfl) ⟨279597014, by rfl⟩ : syracuseStep 372796019 = 559194029) B559194029
theorem B248530679 : Blo 2269435 248530679 := bstep (se 1 (by rfl) ⟨186398009, by rfl⟩ : syracuseStep 248530679 = 372796019) B372796019
theorem B165687119 : Blo 2269435 165687119 := bstep (se 1 (by rfl) ⟨124265339, by rfl⟩ : syracuseStep 165687119 = 248530679) B248530679
theorem B110458079 : Blo 2269435 110458079 := bstep (se 1 (by rfl) ⟨82843559, by rfl⟩ : syracuseStep 110458079 = 165687119) B165687119
theorem B73638719 : Blo 2269435 73638719 := bstep (se 1 (by rfl) ⟨55229039, by rfl⟩ : syracuseStep 73638719 = 110458079) B110458079
theorem B49092479 : Blo 2269435 49092479 := bstep (se 1 (by rfl) ⟨36819359, by rfl⟩ : syracuseStep 49092479 = 73638719) B73638719
theorem B32728319 : Blo 2269435 32728319 := bstep (se 1 (by rfl) ⟨24546239, by rfl⟩ : syracuseStep 32728319 = 49092479) B49092479
theorem B21818879 : Blo 2269435 21818879 := bstep (se 1 (by rfl) ⟨16364159, by rfl⟩ : syracuseStep 21818879 = 32728319) B32728319
theorem B14545919 : Blo 2269435 14545919 := bstep (se 1 (by rfl) ⟨10909439, by rfl⟩ : syracuseStep 14545919 = 21818879) B21818879
theorem B9697279 : Blo 2269435 9697279 := bstep (se 1 (by rfl) ⟨7272959, by rfl⟩ : syracuseStep 9697279 = 14545919) B14545919
theorem B12929705 : Blo 2269435 12929705 := bstep (se 2 (by rfl) ⟨4848639, by rfl⟩ : syracuseStep 12929705 = 9697279) B9697279
theorem B8619803 : Blo 2269435 8619803 := bstep (se 1 (by rfl) ⟨6464852, by rfl⟩ : syracuseStep 8619803 = 12929705) B12929705
theorem B5746535 : Blo 2269435 5746535 := bstep (se 1 (by rfl) ⟨4309901, by rfl⟩ : syracuseStep 5746535 = 8619803) B8619803
theorem B3831023 : Blo 2269435 3831023 := bstep (se 1 (by rfl) ⟨2873267, by rfl⟩ : syracuseStep 3831023 = 5746535) B5746535
theorem B2554015 : Blo 2269435 2554015 := bstep (se 1 (by rfl) ⟨1915511, by rfl⟩ : syracuseStep 2554015 = 3831023) B3831023
theorem B3405353 : Blo 2269435 3405353 := bstep (se 2 (by rfl) ⟨1277007, by rfl⟩ : syracuseStep 3405353 = 2554015) B2554015
theorem B2270235 : Blo 2269435 2270235 := bstep (se 1 (by rfl) ⟨1702676, by rfl⟩ : syracuseStep 2270235 = 3405353) B3405353
theorem B3068285 : Blo 2269435 3068285 := bbase (se 3 (by rfl) ⟨575303, by rfl⟩ : syracuseStep 3068285 = 1150607) (by norm_num)
theorem B32728373 : Blo 2269435 32728373 := bstep (se 5 (by rfl) ⟨1534142, by rfl⟩ : syracuseStep 32728373 = 3068285) B3068285
theorem B21818915 : Blo 2269435 21818915 := bstep (se 1 (by rfl) ⟨16364186, by rfl⟩ : syracuseStep 21818915 = 32728373) B32728373
theorem B14545943 : Blo 2269435 14545943 := bstep (se 1 (by rfl) ⟨10909457, by rfl⟩ : syracuseStep 14545943 = 21818915) B21818915
theorem B9697295 : Blo 2269435 9697295 := bstep (se 1 (by rfl) ⟨7272971, by rfl⟩ : syracuseStep 9697295 = 14545943) B14545943
theorem B6464863 : Blo 2269435 6464863 := bstep (se 1 (by rfl) ⟨4848647, by rfl⟩ : syracuseStep 6464863 = 9697295) B9697295
theorem B8619817 : Blo 2269435 8619817 := bstep (se 2 (by rfl) ⟨3232431, by rfl⟩ : syracuseStep 8619817 = 6464863) B6464863
theorem B11493089 : Blo 2269435 11493089 := bstep (se 2 (by rfl) ⟨4309908, by rfl⟩ : syracuseStep 11493089 = 8619817) B8619817
theorem B7662059 : Blo 2269435 7662059 := bstep (se 1 (by rfl) ⟨5746544, by rfl⟩ : syracuseStep 7662059 = 11493089) B11493089
theorem B5108039 : Blo 2269435 5108039 := bstep (se 1 (by rfl) ⟨3831029, by rfl⟩ : syracuseStep 5108039 = 7662059) B7662059
theorem B3405359 : Blo 2269435 3405359 := bstep (se 1 (by rfl) ⟨2554019, by rfl⟩ : syracuseStep 3405359 = 5108039) B5108039
theorem B2270239 : Blo 2269435 2270239 := bstep (se 1 (by rfl) ⟨1702679, by rfl⟩ : syracuseStep 2270239 = 3405359) B3405359
theorem B3405365 : Blo 2269435 3405365 := bbase (se 5 (by rfl) ⟨159626, by rfl⟩ : syracuseStep 3405365 = 319253) (by norm_num)
theorem B2270243 : Blo 2269435 2270243 := bstep (se 1 (by rfl) ⟨1702682, by rfl⟩ : syracuseStep 2270243 = 3405365) B3405365
theorem B5746565 : Blo 2269435 5746565 := bbase (se 4 (by rfl) ⟨538740, by rfl⟩ : syracuseStep 5746565 = 1077481) (by norm_num)
theorem B3831043 : Blo 2269435 3831043 := bstep (se 1 (by rfl) ⟨2873282, by rfl⟩ : syracuseStep 3831043 = 5746565) B5746565
theorem B5108057 : Blo 2269435 5108057 := bstep (se 2 (by rfl) ⟨1915521, by rfl⟩ : syracuseStep 5108057 = 3831043) B3831043
theorem B3405371 : Blo 2269435 3405371 := bstep (se 1 (by rfl) ⟨2554028, by rfl⟩ : syracuseStep 3405371 = 5108057) B5108057
theorem B2270247 : Blo 2269435 2270247 := bstep (se 1 (by rfl) ⟨1702685, by rfl⟩ : syracuseStep 2270247 = 3405371) B3405371
theorem B2554033 : Blo 2269435 2554033 := bbase (se 2 (by rfl) ⟨957762, by rfl⟩ : syracuseStep 2554033 = 1915525) (by norm_num)
theorem B3405377 : Blo 2269435 3405377 := bstep (se 2 (by rfl) ⟨1277016, by rfl⟩ : syracuseStep 3405377 = 2554033) B2554033
theorem B2270251 : Blo 2269435 2270251 := bstep (se 1 (by rfl) ⟨1702688, by rfl⟩ : syracuseStep 2270251 = 3405377) B3405377
theorem B2424341 : Blo 2269435 2424341 := bbase (se 6 (by rfl) ⟨56820, by rfl⟩ : syracuseStep 2424341 = 113641) (by norm_num)
theorem B6464909 : Blo 2269435 6464909 := bstep (se 3 (by rfl) ⟨1212170, by rfl⟩ : syracuseStep 6464909 = 2424341) B2424341
theorem B4309939 : Blo 2269435 4309939 := bstep (se 1 (by rfl) ⟨3232454, by rfl⟩ : syracuseStep 4309939 = 6464909) B6464909
theorem B5746585 : Blo 2269435 5746585 := bstep (se 2 (by rfl) ⟨2154969, by rfl⟩ : syracuseStep 5746585 = 4309939) B4309939
theorem B7662113 : Blo 2269435 7662113 := bstep (se 2 (by rfl) ⟨2873292, by rfl⟩ : syracuseStep 7662113 = 5746585) B5746585
theorem B5108075 : Blo 2269435 5108075 := bstep (se 1 (by rfl) ⟨3831056, by rfl⟩ : syracuseStep 5108075 = 7662113) B7662113
theorem B3405383 : Blo 2269435 3405383 := bstep (se 1 (by rfl) ⟨2554037, by rfl⟩ : syracuseStep 3405383 = 5108075) B5108075
theorem B2270255 : Blo 2269435 2270255 := bstep (se 1 (by rfl) ⟨1702691, by rfl⟩ : syracuseStep 2270255 = 3405383) B3405383
theorem B3405389 : Blo 2269435 3405389 := bbase (se 3 (by rfl) ⟨638510, by rfl⟩ : syracuseStep 3405389 = 1277021) (by norm_num)
theorem B2270259 : Blo 2269435 2270259 := bstep (se 1 (by rfl) ⟨1702694, by rfl⟩ : syracuseStep 2270259 = 3405389) B3405389
theorem B5108093 : Blo 2269435 5108093 := bbase (se 3 (by rfl) ⟨957767, by rfl⟩ : syracuseStep 5108093 = 1915535) (by norm_num)
theorem B3405395 : Blo 2269435 3405395 := bstep (se 1 (by rfl) ⟨2554046, by rfl⟩ : syracuseStep 3405395 = 5108093) B5108093
theorem B2270263 : Blo 2269435 2270263 := bstep (se 1 (by rfl) ⟨1702697, by rfl⟩ : syracuseStep 2270263 = 3405395) B3405395
theorem B3831077 : Blo 2269435 3831077 := bbase (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) (by norm_num)
theorem B2554051 : Blo 2269435 2554051 := bstep (se 1 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 2554051 = 3831077) B3831077
theorem B3405401 : Blo 2269435 3405401 := bstep (se 2 (by rfl) ⟨1277025, by rfl⟩ : syracuseStep 3405401 = 2554051) B2554051
theorem B2270267 : Blo 2269435 2270267 := bstep (se 1 (by rfl) ⟨1702700, by rfl⟩ : syracuseStep 2270267 = 3405401) B3405401
theorem B3232477 : Blo 2269435 3232477 := bbase (se 3 (by rfl) ⟨606089, by rfl⟩ : syracuseStep 3232477 = 1212179) (by norm_num)
theorem B17239877 : Blo 2269435 17239877 := bstep (se 4 (by rfl) ⟨1616238, by rfl⟩ : syracuseStep 17239877 = 3232477) B3232477
theorem B11493251 : Blo 2269435 11493251 := bstep (se 1 (by rfl) ⟨8619938, by rfl⟩ : syracuseStep 11493251 = 17239877) B17239877
theorem B7662167 : Blo 2269435 7662167 := bstep (se 1 (by rfl) ⟨5746625, by rfl⟩ : syracuseStep 7662167 = 11493251) B11493251
theorem B5108111 : Blo 2269435 5108111 := bstep (se 1 (by rfl) ⟨3831083, by rfl⟩ : syracuseStep 5108111 = 7662167) B7662167
theorem B3405407 : Blo 2269435 3405407 := bstep (se 1 (by rfl) ⟨2554055, by rfl⟩ : syracuseStep 3405407 = 5108111) B5108111
theorem B2270271 : Blo 2269435 2270271 := bstep (se 1 (by rfl) ⟨1702703, by rfl⟩ : syracuseStep 2270271 = 3405407) B3405407
theorem B3405413 : Blo 2269435 3405413 := bbase (se 4 (by rfl) ⟨319257, by rfl⟩ : syracuseStep 3405413 = 638515) (by norm_num)
theorem B2270275 : Blo 2269435 2270275 := bstep (se 1 (by rfl) ⟨1702706, by rfl⟩ : syracuseStep 2270275 = 3405413) B3405413
theorem B9829781 : Blo 2269435 9829781 := bbase (se 6 (by rfl) ⟨230385, by rfl⟩ : syracuseStep 9829781 = 460771) (by norm_num)
theorem B6553187 : Blo 2269435 6553187 := bstep (se 1 (by rfl) ⟨4914890, by rfl⟩ : syracuseStep 6553187 = 9829781) B9829781
theorem B4368791 : Blo 2269435 4368791 := bstep (se 1 (by rfl) ⟨3276593, by rfl⟩ : syracuseStep 4368791 = 6553187) B6553187
theorem B2912527 : Blo 2269435 2912527 := bstep (se 1 (by rfl) ⟨2184395, by rfl⟩ : syracuseStep 2912527 = 4368791) B4368791
theorem B15533477 : Blo 2269435 15533477 := bstep (se 4 (by rfl) ⟨1456263, by rfl⟩ : syracuseStep 15533477 = 2912527) B2912527
theorem B10355651 : Blo 2269435 10355651 := bstep (se 1 (by rfl) ⟨7766738, by rfl⟩ : syracuseStep 10355651 = 15533477) B15533477
theorem B6903767 : Blo 2269435 6903767 := bstep (se 1 (by rfl) ⟨5177825, by rfl⟩ : syracuseStep 6903767 = 10355651) B10355651
theorem B4602511 : Blo 2269435 4602511 := bstep (se 1 (by rfl) ⟨3451883, by rfl⟩ : syracuseStep 4602511 = 6903767) B6903767
theorem B6136681 : Blo 2269435 6136681 := bstep (se 2 (by rfl) ⟨2301255, by rfl⟩ : syracuseStep 6136681 = 4602511) B4602511
theorem B8182241 : Blo 2269435 8182241 := bstep (se 2 (by rfl) ⟨3068340, by rfl⟩ : syracuseStep 8182241 = 6136681) B6136681
theorem B5454827 : Blo 2269435 5454827 := bstep (se 1 (by rfl) ⟨4091120, by rfl⟩ : syracuseStep 5454827 = 8182241) B8182241
theorem B3636551 : Blo 2269435 3636551 := bstep (se 1 (by rfl) ⟨2727413, by rfl⟩ : syracuseStep 3636551 = 5454827) B5454827
theorem B2424367 : Blo 2269435 2424367 := bstep (se 1 (by rfl) ⟨1818275, by rfl⟩ : syracuseStep 2424367 = 3636551) B3636551
theorem B3232489 : Blo 2269435 3232489 := bstep (se 2 (by rfl) ⟨1212183, by rfl⟩ : syracuseStep 3232489 = 2424367) B2424367
theorem B4309985 : Blo 2269435 4309985 := bstep (se 2 (by rfl) ⟨1616244, by rfl⟩ : syracuseStep 4309985 = 3232489) B3232489
theorem B2873323 : Blo 2269435 2873323 := bstep (se 1 (by rfl) ⟨2154992, by rfl⟩ : syracuseStep 2873323 = 4309985) B4309985
theorem B3831097 : Blo 2269435 3831097 := bstep (se 2 (by rfl) ⟨1436661, by rfl⟩ : syracuseStep 3831097 = 2873323) B2873323
theorem B5108129 : Blo 2269435 5108129 := bstep (se 2 (by rfl) ⟨1915548, by rfl⟩ : syracuseStep 5108129 = 3831097) B3831097
theorem B3405419 : Blo 2269435 3405419 := bstep (se 1 (by rfl) ⟨2554064, by rfl⟩ : syracuseStep 3405419 = 5108129) B5108129
theorem B2270279 : Blo 2269435 2270279 := bstep (se 1 (by rfl) ⟨1702709, by rfl⟩ : syracuseStep 2270279 = 3405419) B3405419
theorem B2554069 : Blo 2269435 2554069 := bbase (se 7 (by rfl) ⟨29930, by rfl⟩ : syracuseStep 2554069 = 59861) (by norm_num)
theorem B3405425 : Blo 2269435 3405425 := bstep (se 2 (by rfl) ⟨1277034, by rfl⟩ : syracuseStep 3405425 = 2554069) B2554069
theorem B2270283 : Blo 2269435 2270283 := bstep (se 1 (by rfl) ⟨1702712, by rfl⟩ : syracuseStep 2270283 = 3405425) B3405425
theorem B2873333 : Blo 2269435 2873333 := bbase (se 5 (by rfl) ⟨134687, by rfl⟩ : syracuseStep 2873333 = 269375) (by norm_num)
theorem B7662221 : Blo 2269435 7662221 := bstep (se 3 (by rfl) ⟨1436666, by rfl⟩ : syracuseStep 7662221 = 2873333) B2873333
theorem B5108147 : Blo 2269435 5108147 := bstep (se 1 (by rfl) ⟨3831110, by rfl⟩ : syracuseStep 5108147 = 7662221) B7662221
theorem B3405431 : Blo 2269435 3405431 := bstep (se 1 (by rfl) ⟨2554073, by rfl⟩ : syracuseStep 3405431 = 5108147) B5108147
theorem B2270287 : Blo 2269435 2270287 := bstep (se 1 (by rfl) ⟨1702715, by rfl⟩ : syracuseStep 2270287 = 3405431) B3405431
theorem B3405437 : Blo 2269435 3405437 := bbase (se 3 (by rfl) ⟨638519, by rfl⟩ : syracuseStep 3405437 = 1277039) (by norm_num)
theorem B2270291 : Blo 2269435 2270291 := bstep (se 1 (by rfl) ⟨1702718, by rfl⟩ : syracuseStep 2270291 = 3405437) B3405437
theorem B5108165 : Blo 2269435 5108165 := bbase (se 4 (by rfl) ⟨478890, by rfl⟩ : syracuseStep 5108165 = 957781) (by norm_num)
theorem B3405443 : Blo 2269435 3405443 := bstep (se 1 (by rfl) ⟨2554082, by rfl⟩ : syracuseStep 3405443 = 5108165) B5108165
theorem B2270295 : Blo 2269435 2270295 := bstep (se 1 (by rfl) ⟨1702721, by rfl⟩ : syracuseStep 2270295 = 3405443) B3405443
theorem B2727437 : Blo 2269435 2727437 := bbase (se 3 (by rfl) ⟨511394, by rfl⟩ : syracuseStep 2727437 = 1022789) (by norm_num)
theorem B7273165 : Blo 2269435 7273165 := bstep (se 3 (by rfl) ⟨1363718, by rfl⟩ : syracuseStep 7273165 = 2727437) B2727437
theorem B9697553 : Blo 2269435 9697553 := bstep (se 2 (by rfl) ⟨3636582, by rfl⟩ : syracuseStep 9697553 = 7273165) B7273165
theorem B6465035 : Blo 2269435 6465035 := bstep (se 1 (by rfl) ⟨4848776, by rfl⟩ : syracuseStep 6465035 = 9697553) B9697553
theorem B4310023 : Blo 2269435 4310023 := bstep (se 1 (by rfl) ⟨3232517, by rfl⟩ : syracuseStep 4310023 = 6465035) B6465035
theorem B5746697 : Blo 2269435 5746697 := bstep (se 2 (by rfl) ⟨2155011, by rfl⟩ : syracuseStep 5746697 = 4310023) B4310023
theorem B3831131 : Blo 2269435 3831131 := bstep (se 1 (by rfl) ⟨2873348, by rfl⟩ : syracuseStep 3831131 = 5746697) B5746697
theorem B2554087 : Blo 2269435 2554087 := bstep (se 1 (by rfl) ⟨1915565, by rfl⟩ : syracuseStep 2554087 = 3831131) B3831131
theorem B3405449 : Blo 2269435 3405449 := bstep (se 2 (by rfl) ⟨1277043, by rfl⟩ : syracuseStep 3405449 = 2554087) B2554087
theorem B2270299 : Blo 2269435 2270299 := bstep (se 1 (by rfl) ⟨1702724, by rfl⟩ : syracuseStep 2270299 = 3405449) B3405449
theorem B11493413 : Blo 2269435 11493413 := bbase (se 4 (by rfl) ⟨1077507, by rfl⟩ : syracuseStep 11493413 = 2155015) (by norm_num)
theorem B7662275 : Blo 2269435 7662275 := bstep (se 1 (by rfl) ⟨5746706, by rfl⟩ : syracuseStep 7662275 = 11493413) B11493413
theorem B5108183 : Blo 2269435 5108183 := bstep (se 1 (by rfl) ⟨3831137, by rfl⟩ : syracuseStep 5108183 = 7662275) B7662275
theorem B3405455 : Blo 2269435 3405455 := bstep (se 1 (by rfl) ⟨2554091, by rfl⟩ : syracuseStep 3405455 = 5108183) B5108183
theorem B2270303 : Blo 2269435 2270303 := bstep (se 1 (by rfl) ⟨1702727, by rfl⟩ : syracuseStep 2270303 = 3405455) B3405455
theorem B3405461 : Blo 2269435 3405461 := bbase (se 6 (by rfl) ⟨79815, by rfl⟩ : syracuseStep 3405461 = 159631) (by norm_num)
theorem B2270307 : Blo 2269435 2270307 := bstep (se 1 (by rfl) ⟨1702730, by rfl⟩ : syracuseStep 2270307 = 3405461) B3405461
theorem B6305365 : Blo 2269435 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B8407153 : Blo 2269435 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B11209537 : Blo 2269435 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B14946049 : Blo 2269435 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B19928065 : Blo 2269435 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B26570753 : Blo 2269435 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B17713835 : Blo 2269435 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B11809223 : Blo 2269435 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B7872815 : Blo 2269435 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B5248543 : Blo 2269435 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B6998057 : Blo 2269435 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B4665371 : Blo 2269435 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B12440989 : Blo 2269435 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B16587985 : Blo 2269435 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B22117313 : Blo 2269435 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B14744875 : Blo 2269435 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B19659833 : Blo 2269435 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B13106555 : Blo 2269435 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B8737703 : Blo 2269435 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B5825135 : Blo 2269435 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B15533693 : Blo 2269435 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B10355795 : Blo 2269435 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B6903863 : Blo 2269435 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B4602575 : Blo 2269435 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B3068383 : Blo 2269435 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B4091177 : Blo 2269435 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B2727451 : Blo 2269435 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B14546405 : Blo 2269435 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B9697603 : Blo 2269435 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B12930137 : Blo 2269435 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B8620091 : Blo 2269435 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B5746727 : Blo 2269435 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B3831151 : Blo 2269435 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B5108201 : Blo 2269435 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B3405467 : Blo 2269435 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B2270311 : Blo 2269435 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B2554105 : Blo 2269435 2554105 := bbase (se 2 (by rfl) ⟨957789, by rfl⟩ : syracuseStep 2554105 = 1915579) (by norm_num)
theorem B3405473 : Blo 2269435 3405473 := bstep (se 2 (by rfl) ⟨1277052, by rfl⟩ : syracuseStep 3405473 = 2554105) B2554105
theorem B2270315 : Blo 2269435 2270315 := bstep (se 1 (by rfl) ⟨1702736, by rfl⟩ : syracuseStep 2270315 = 3405473) B3405473
theorem B9697637 : Blo 2269435 9697637 := bbase (se 4 (by rfl) ⟨909153, by rfl⟩ : syracuseStep 9697637 = 1818307) (by norm_num)
theorem B6465091 : Blo 2269435 6465091 := bstep (se 1 (by rfl) ⟨4848818, by rfl⟩ : syracuseStep 6465091 = 9697637) B9697637
theorem B8620121 : Blo 2269435 8620121 := bstep (se 2 (by rfl) ⟨3232545, by rfl⟩ : syracuseStep 8620121 = 6465091) B6465091
theorem B5746747 : Blo 2269435 5746747 := bstep (se 1 (by rfl) ⟨4310060, by rfl⟩ : syracuseStep 5746747 = 8620121) B8620121
theorem B7662329 : Blo 2269435 7662329 := bstep (se 2 (by rfl) ⟨2873373, by rfl⟩ : syracuseStep 7662329 = 5746747) B5746747
theorem B5108219 : Blo 2269435 5108219 := bstep (se 1 (by rfl) ⟨3831164, by rfl⟩ : syracuseStep 5108219 = 7662329) B7662329
theorem B3405479 : Blo 2269435 3405479 := bstep (se 1 (by rfl) ⟨2554109, by rfl⟩ : syracuseStep 3405479 = 5108219) B5108219
theorem B2270319 : Blo 2269435 2270319 := bstep (se 1 (by rfl) ⟨1702739, by rfl⟩ : syracuseStep 2270319 = 3405479) B3405479
theorem B3405485 : Blo 2269435 3405485 := bbase (se 3 (by rfl) ⟨638528, by rfl⟩ : syracuseStep 3405485 = 1277057) (by norm_num)
theorem B2270323 : Blo 2269435 2270323 := bstep (se 1 (by rfl) ⟨1702742, by rfl⟩ : syracuseStep 2270323 = 3405485) B3405485
theorem B5108237 : Blo 2269435 5108237 := bbase (se 3 (by rfl) ⟨957794, by rfl⟩ : syracuseStep 5108237 = 1915589) (by norm_num)
theorem B3405491 : Blo 2269435 3405491 := bstep (se 1 (by rfl) ⟨2554118, by rfl⟩ : syracuseStep 3405491 = 5108237) B5108237
theorem B2270327 : Blo 2269435 2270327 := bstep (se 1 (by rfl) ⟨1702745, by rfl⟩ : syracuseStep 2270327 = 3405491) B3405491
theorem B2873389 : Blo 2269435 2873389 := bbase (se 3 (by rfl) ⟨538760, by rfl⟩ : syracuseStep 2873389 = 1077521) (by norm_num)
theorem B3831185 : Blo 2269435 3831185 := bstep (se 2 (by rfl) ⟨1436694, by rfl⟩ : syracuseStep 3831185 = 2873389) B2873389
theorem B2554123 : Blo 2269435 2554123 := bstep (se 1 (by rfl) ⟨1915592, by rfl⟩ : syracuseStep 2554123 = 3831185) B3831185
theorem B3405497 : Blo 2269435 3405497 := bstep (se 2 (by rfl) ⟨1277061, by rfl⟩ : syracuseStep 3405497 = 2554123) B2554123
theorem B2270331 : Blo 2269435 2270331 := bstep (se 1 (by rfl) ⟨1702748, by rfl⟩ : syracuseStep 2270331 = 3405497) B3405497
theorem B18238709 : Blo 2269435 18238709 := bbase (se 5 (by rfl) ⟨854939, by rfl⟩ : syracuseStep 18238709 = 1709879) (by norm_num)
theorem B48636557 : Blo 2269435 48636557 := bstep (se 3 (by rfl) ⟨9119354, by rfl⟩ : syracuseStep 48636557 = 18238709) B18238709
theorem B32424371 : Blo 2269435 32424371 := bstep (se 1 (by rfl) ⟨24318278, by rfl⟩ : syracuseStep 32424371 = 48636557) B48636557
theorem B21616247 : Blo 2269435 21616247 := bstep (se 1 (by rfl) ⟨16212185, by rfl⟩ : syracuseStep 21616247 = 32424371) B32424371
theorem B57643325 : Blo 2269435 57643325 := bstep (se 3 (by rfl) ⟨10808123, by rfl⟩ : syracuseStep 57643325 = 21616247) B21616247
theorem B38428883 : Blo 2269435 38428883 := bstep (se 1 (by rfl) ⟨28821662, by rfl⟩ : syracuseStep 38428883 = 57643325) B57643325
theorem B25619255 : Blo 2269435 25619255 := bstep (se 1 (by rfl) ⟨19214441, by rfl⟩ : syracuseStep 25619255 = 38428883) B38428883
theorem B17079503 : Blo 2269435 17079503 := bstep (se 1 (by rfl) ⟨12809627, by rfl⟩ : syracuseStep 17079503 = 25619255) B25619255
theorem B45545341 : Blo 2269435 45545341 := bstep (se 3 (by rfl) ⟨8539751, by rfl⟩ : syracuseStep 45545341 = 17079503) B17079503
theorem B60727121 : Blo 2269435 60727121 := bstep (se 2 (by rfl) ⟨22772670, by rfl⟩ : syracuseStep 60727121 = 45545341) B45545341
theorem B40484747 : Blo 2269435 40484747 := bstep (se 1 (by rfl) ⟨30363560, by rfl⟩ : syracuseStep 40484747 = 60727121) B60727121
theorem B107959325 : Blo 2269435 107959325 := bstep (se 3 (by rfl) ⟨20242373, by rfl⟩ : syracuseStep 107959325 = 40484747) B40484747
theorem B287891533 : Blo 2269435 287891533 := bstep (se 3 (by rfl) ⟨53979662, by rfl⟩ : syracuseStep 287891533 = 107959325) B107959325
theorem B383855377 : Blo 2269435 383855377 := bstep (se 2 (by rfl) ⟨143945766, by rfl⟩ : syracuseStep 383855377 = 287891533) B287891533
theorem B511807169 : Blo 2269435 511807169 := bstep (se 2 (by rfl) ⟨191927688, by rfl⟩ : syracuseStep 511807169 = 383855377) B383855377
theorem B341204779 : Blo 2269435 341204779 := bstep (se 1 (by rfl) ⟨255903584, by rfl⟩ : syracuseStep 341204779 = 511807169) B511807169
theorem B454939705 : Blo 2269435 454939705 := bstep (se 2 (by rfl) ⟨170602389, by rfl⟩ : syracuseStep 454939705 = 341204779) B341204779
theorem B2426345093 : Blo 2269435 2426345093 := bstep (se 4 (by rfl) ⟨227469852, by rfl⟩ : syracuseStep 2426345093 = 454939705) B454939705
theorem B1617563395 : Blo 2269435 1617563395 := bstep (se 1 (by rfl) ⟨1213172546, by rfl⟩ : syracuseStep 1617563395 = 2426345093) B2426345093
theorem B2156751193 : Blo 2269435 2156751193 := bstep (se 2 (by rfl) ⟨808781697, by rfl⟩ : syracuseStep 2156751193 = 1617563395) B1617563395
theorem B2875668257 : Blo 2269435 2875668257 := bstep (se 2 (by rfl) ⟨1078375596, by rfl⟩ : syracuseStep 2875668257 = 2156751193) B2156751193
theorem B1917112171 : Blo 2269435 1917112171 := bstep (se 1 (by rfl) ⟨1437834128, by rfl⟩ : syracuseStep 1917112171 = 2875668257) B2875668257
theorem B2556149561 : Blo 2269435 2556149561 := bstep (se 2 (by rfl) ⟨958556085, by rfl⟩ : syracuseStep 2556149561 = 1917112171) B1917112171
theorem B1704099707 : Blo 2269435 1704099707 := bstep (se 1 (by rfl) ⟨1278074780, by rfl⟩ : syracuseStep 1704099707 = 2556149561) B2556149561
theorem B1136066471 : Blo 2269435 1136066471 := bstep (se 1 (by rfl) ⟨852049853, by rfl⟩ : syracuseStep 1136066471 = 1704099707) B1704099707
theorem B757377647 : Blo 2269435 757377647 := bstep (se 1 (by rfl) ⟨568033235, by rfl⟩ : syracuseStep 757377647 = 1136066471) B1136066471
theorem B504918431 : Blo 2269435 504918431 := bstep (se 1 (by rfl) ⟨378688823, by rfl⟩ : syracuseStep 504918431 = 757377647) B757377647
theorem B336612287 : Blo 2269435 336612287 := bstep (se 1 (by rfl) ⟨252459215, by rfl⟩ : syracuseStep 336612287 = 504918431) B504918431
theorem B224408191 : Blo 2269435 224408191 := bstep (se 1 (by rfl) ⟨168306143, by rfl⟩ : syracuseStep 224408191 = 336612287) B336612287
theorem B299210921 : Blo 2269435 299210921 := bstep (se 2 (by rfl) ⟨112204095, by rfl⟩ : syracuseStep 299210921 = 224408191) B224408191
theorem B199473947 : Blo 2269435 199473947 := bstep (se 1 (by rfl) ⟨149605460, by rfl⟩ : syracuseStep 199473947 = 299210921) B299210921
theorem B132982631 : Blo 2269435 132982631 := bstep (se 1 (by rfl) ⟨99736973, by rfl⟩ : syracuseStep 132982631 = 199473947) B199473947
theorem B88655087 : Blo 2269435 88655087 := bstep (se 1 (by rfl) ⟨66491315, by rfl⟩ : syracuseStep 88655087 = 132982631) B132982631
theorem B59103391 : Blo 2269435 59103391 := bstep (se 1 (by rfl) ⟨44327543, by rfl⟩ : syracuseStep 59103391 = 88655087) B88655087
theorem B78804521 : Blo 2269435 78804521 := bstep (se 2 (by rfl) ⟨29551695, by rfl⟩ : syracuseStep 78804521 = 59103391) B59103391
theorem B52536347 : Blo 2269435 52536347 := bstep (se 1 (by rfl) ⟨39402260, by rfl⟩ : syracuseStep 52536347 = 78804521) B78804521
theorem B35024231 : Blo 2269435 35024231 := bstep (se 1 (by rfl) ⟨26268173, by rfl⟩ : syracuseStep 35024231 = 52536347) B52536347
theorem B23349487 : Blo 2269435 23349487 := bstep (se 1 (by rfl) ⟨17512115, by rfl⟩ : syracuseStep 23349487 = 35024231) B35024231
theorem B31132649 : Blo 2269435 31132649 := bstep (se 2 (by rfl) ⟨11674743, by rfl⟩ : syracuseStep 31132649 = 23349487) B23349487
theorem B20755099 : Blo 2269435 20755099 := bstep (se 1 (by rfl) ⟨15566324, by rfl⟩ : syracuseStep 20755099 = 31132649) B31132649
theorem B110693861 : Blo 2269435 110693861 := bstep (se 4 (by rfl) ⟨10377549, by rfl⟩ : syracuseStep 110693861 = 20755099) B20755099
theorem B73795907 : Blo 2269435 73795907 := bstep (se 1 (by rfl) ⟨55346930, by rfl⟩ : syracuseStep 73795907 = 110693861) B110693861
theorem B196789085 : Blo 2269435 196789085 := bstep (se 3 (by rfl) ⟨36897953, by rfl⟩ : syracuseStep 196789085 = 73795907) B73795907
theorem B131192723 : Blo 2269435 131192723 := bstep (se 1 (by rfl) ⟨98394542, by rfl⟩ : syracuseStep 131192723 = 196789085) B196789085
theorem B349847261 : Blo 2269435 349847261 := bstep (se 3 (by rfl) ⟨65596361, by rfl⟩ : syracuseStep 349847261 = 131192723) B131192723
theorem B233231507 : Blo 2269435 233231507 := bstep (se 1 (by rfl) ⟨174923630, by rfl⟩ : syracuseStep 233231507 = 349847261) B349847261
theorem B155487671 : Blo 2269435 155487671 := bstep (se 1 (by rfl) ⟨116615753, by rfl⟩ : syracuseStep 155487671 = 233231507) B233231507
theorem B103658447 : Blo 2269435 103658447 := bstep (se 1 (by rfl) ⟨77743835, by rfl⟩ : syracuseStep 103658447 = 155487671) B155487671
theorem B69105631 : Blo 2269435 69105631 := bstep (se 1 (by rfl) ⟨51829223, by rfl⟩ : syracuseStep 69105631 = 103658447) B103658447
theorem B92140841 : Blo 2269435 92140841 := bstep (se 2 (by rfl) ⟨34552815, by rfl⟩ : syracuseStep 92140841 = 69105631) B69105631
theorem B245708909 : Blo 2269435 245708909 := bstep (se 3 (by rfl) ⟨46070420, by rfl⟩ : syracuseStep 245708909 = 92140841) B92140841
theorem B163805939 : Blo 2269435 163805939 := bstep (se 1 (by rfl) ⟨122854454, by rfl⟩ : syracuseStep 163805939 = 245708909) B245708909
theorem B109203959 : Blo 2269435 109203959 := bstep (se 1 (by rfl) ⟨81902969, by rfl⟩ : syracuseStep 109203959 = 163805939) B163805939
theorem B72802639 : Blo 2269435 72802639 := bstep (se 1 (by rfl) ⟨54601979, by rfl⟩ : syracuseStep 72802639 = 109203959) B109203959
theorem B97070185 : Blo 2269435 97070185 := bstep (se 2 (by rfl) ⟨36401319, by rfl⟩ : syracuseStep 97070185 = 72802639) B72802639
theorem B129426913 : Blo 2269435 129426913 := bstep (se 2 (by rfl) ⟨48535092, by rfl⟩ : syracuseStep 129426913 = 97070185) B97070185
theorem B172569217 : Blo 2269435 172569217 := bstep (se 2 (by rfl) ⟨64713456, by rfl⟩ : syracuseStep 172569217 = 129426913) B129426913
theorem B230092289 : Blo 2269435 230092289 := bstep (se 2 (by rfl) ⟨86284608, by rfl⟩ : syracuseStep 230092289 = 172569217) B172569217
theorem B153394859 : Blo 2269435 153394859 := bstep (se 1 (by rfl) ⟨115046144, by rfl⟩ : syracuseStep 153394859 = 230092289) B230092289
theorem B102263239 : Blo 2269435 102263239 := bstep (se 1 (by rfl) ⟨76697429, by rfl⟩ : syracuseStep 102263239 = 153394859) B153394859
theorem B136350985 : Blo 2269435 136350985 := bstep (se 2 (by rfl) ⟨51131619, by rfl⟩ : syracuseStep 136350985 = 102263239) B102263239
theorem B181801313 : Blo 2269435 181801313 := bstep (se 2 (by rfl) ⟨68175492, by rfl⟩ : syracuseStep 181801313 = 136350985) B136350985
theorem B121200875 : Blo 2269435 121200875 := bstep (se 1 (by rfl) ⟨90900656, by rfl⟩ : syracuseStep 121200875 = 181801313) B181801313
theorem B80800583 : Blo 2269435 80800583 := bstep (se 1 (by rfl) ⟨60600437, by rfl⟩ : syracuseStep 80800583 = 121200875) B121200875
theorem B861872885 : Blo 2269435 861872885 := bstep (se 5 (by rfl) ⟨40400291, by rfl⟩ : syracuseStep 861872885 = 80800583) B80800583
theorem B574581923 : Blo 2269435 574581923 := bstep (se 1 (by rfl) ⟨430936442, by rfl⟩ : syracuseStep 574581923 = 861872885) B861872885
theorem B383054615 : Blo 2269435 383054615 := bstep (se 1 (by rfl) ⟨287290961, by rfl⟩ : syracuseStep 383054615 = 574581923) B574581923
theorem B255369743 : Blo 2269435 255369743 := bstep (se 1 (by rfl) ⟨191527307, by rfl⟩ : syracuseStep 255369743 = 383054615) B383054615
theorem B170246495 : Blo 2269435 170246495 := bstep (se 1 (by rfl) ⟨127684871, by rfl⟩ : syracuseStep 170246495 = 255369743) B255369743
theorem B453990653 : Blo 2269435 453990653 := bstep (se 3 (by rfl) ⟨85123247, by rfl⟩ : syracuseStep 453990653 = 170246495) B170246495
theorem B302660435 : Blo 2269435 302660435 := bstep (se 1 (by rfl) ⟨226995326, by rfl⟩ : syracuseStep 302660435 = 453990653) B453990653
theorem B807094493 : Blo 2269435 807094493 := bstep (se 3 (by rfl) ⟨151330217, by rfl⟩ : syracuseStep 807094493 = 302660435) B302660435
theorem B538062995 : Blo 2269435 538062995 := bstep (se 1 (by rfl) ⟨403547246, by rfl⟩ : syracuseStep 538062995 = 807094493) B807094493
theorem B358708663 : Blo 2269435 358708663 := bstep (se 1 (by rfl) ⟨269031497, by rfl⟩ : syracuseStep 358708663 = 538062995) B538062995
theorem B478278217 : Blo 2269435 478278217 := bstep (se 2 (by rfl) ⟨179354331, by rfl⟩ : syracuseStep 478278217 = 358708663) B358708663
theorem B637704289 : Blo 2269435 637704289 := bstep (se 2 (by rfl) ⟨239139108, by rfl⟩ : syracuseStep 637704289 = 478278217) B478278217
theorem B850272385 : Blo 2269435 850272385 := bstep (se 2 (by rfl) ⟨318852144, by rfl⟩ : syracuseStep 850272385 = 637704289) B637704289
theorem B1133696513 : Blo 2269435 1133696513 := bstep (se 2 (by rfl) ⟨425136192, by rfl⟩ : syracuseStep 1133696513 = 850272385) B850272385
theorem B755797675 : Blo 2269435 755797675 := bstep (se 1 (by rfl) ⟨566848256, by rfl⟩ : syracuseStep 755797675 = 1133696513) B1133696513
theorem B1007730233 : Blo 2269435 1007730233 := bstep (se 2 (by rfl) ⟨377898837, by rfl⟩ : syracuseStep 1007730233 = 755797675) B755797675
theorem B671820155 : Blo 2269435 671820155 := bstep (se 1 (by rfl) ⟨503865116, by rfl⟩ : syracuseStep 671820155 = 1007730233) B1007730233
theorem B447880103 : Blo 2269435 447880103 := bstep (se 1 (by rfl) ⟨335910077, by rfl⟩ : syracuseStep 447880103 = 671820155) B671820155
theorem B298586735 : Blo 2269435 298586735 := bstep (se 1 (by rfl) ⟨223940051, by rfl⟩ : syracuseStep 298586735 = 447880103) B447880103
theorem B199057823 : Blo 2269435 199057823 := bstep (se 1 (by rfl) ⟨149293367, by rfl⟩ : syracuseStep 199057823 = 298586735) B298586735
theorem B132705215 : Blo 2269435 132705215 := bstep (se 1 (by rfl) ⟨99528911, by rfl⟩ : syracuseStep 132705215 = 199057823) B199057823
theorem B88470143 : Blo 2269435 88470143 := bstep (se 1 (by rfl) ⟨66352607, by rfl⟩ : syracuseStep 88470143 = 132705215) B132705215
theorem B58980095 : Blo 2269435 58980095 := bstep (se 1 (by rfl) ⟨44235071, by rfl⟩ : syracuseStep 58980095 = 88470143) B88470143
theorem B39320063 : Blo 2269435 39320063 := bstep (se 1 (by rfl) ⟨29490047, by rfl⟩ : syracuseStep 39320063 = 58980095) B58980095
theorem B26213375 : Blo 2269435 26213375 := bstep (se 1 (by rfl) ⟨19660031, by rfl⟩ : syracuseStep 26213375 = 39320063) B39320063
theorem B17475583 : Blo 2269435 17475583 := bstep (se 1 (by rfl) ⟨13106687, by rfl⟩ : syracuseStep 17475583 = 26213375) B26213375
theorem B23300777 : Blo 2269435 23300777 := bstep (se 2 (by rfl) ⟨8737791, by rfl⟩ : syracuseStep 23300777 = 17475583) B17475583
theorem B15533851 : Blo 2269435 15533851 := bstep (se 1 (by rfl) ⟨11650388, by rfl⟩ : syracuseStep 15533851 = 23300777) B23300777
theorem B20711801 : Blo 2269435 20711801 := bstep (se 2 (by rfl) ⟨7766925, by rfl⟩ : syracuseStep 20711801 = 15533851) B15533851
theorem B13807867 : Blo 2269435 13807867 := bstep (se 1 (by rfl) ⟨10355900, by rfl⟩ : syracuseStep 13807867 = 20711801) B20711801
theorem B18410489 : Blo 2269435 18410489 := bstep (se 2 (by rfl) ⟨6903933, by rfl⟩ : syracuseStep 18410489 = 13807867) B13807867
theorem B12273659 : Blo 2269435 12273659 := bstep (se 1 (by rfl) ⟨9205244, by rfl⟩ : syracuseStep 12273659 = 18410489) B18410489
theorem B8182439 : Blo 2269435 8182439 := bstep (se 1 (by rfl) ⟨6136829, by rfl⟩ : syracuseStep 8182439 = 12273659) B12273659
theorem B5454959 : Blo 2269435 5454959 := bstep (se 1 (by rfl) ⟨4091219, by rfl⟩ : syracuseStep 5454959 = 8182439) B8182439
theorem B14546557 : Blo 2269435 14546557 := bstep (se 3 (by rfl) ⟨2727479, by rfl⟩ : syracuseStep 14546557 = 5454959) B5454959
theorem B19395409 : Blo 2269435 19395409 := bstep (se 2 (by rfl) ⟨7273278, by rfl⟩ : syracuseStep 19395409 = 14546557) B14546557
theorem B25860545 : Blo 2269435 25860545 := bstep (se 2 (by rfl) ⟨9697704, by rfl⟩ : syracuseStep 25860545 = 19395409) B19395409
theorem B17240363 : Blo 2269435 17240363 := bstep (se 1 (by rfl) ⟨12930272, by rfl⟩ : syracuseStep 17240363 = 25860545) B25860545
theorem B11493575 : Blo 2269435 11493575 := bstep (se 1 (by rfl) ⟨8620181, by rfl⟩ : syracuseStep 11493575 = 17240363) B17240363
theorem B7662383 : Blo 2269435 7662383 := bstep (se 1 (by rfl) ⟨5746787, by rfl⟩ : syracuseStep 7662383 = 11493575) B11493575
theorem B5108255 : Blo 2269435 5108255 := bstep (se 1 (by rfl) ⟨3831191, by rfl⟩ : syracuseStep 5108255 = 7662383) B7662383
theorem B3405503 : Blo 2269435 3405503 := bstep (se 1 (by rfl) ⟨2554127, by rfl⟩ : syracuseStep 3405503 = 5108255) B5108255
theorem B2270335 : Blo 2269435 2270335 := bstep (se 1 (by rfl) ⟨1702751, by rfl⟩ : syracuseStep 2270335 = 3405503) B3405503
theorem B3405509 : Blo 2269435 3405509 := bbase (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) (by norm_num)
theorem B2270339 : Blo 2269435 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B3831205 : Blo 2269435 3831205 := bbase (se 4 (by rfl) ⟨359175, by rfl⟩ : syracuseStep 3831205 = 718351) (by norm_num)
theorem B5108273 : Blo 2269435 5108273 := bstep (se 2 (by rfl) ⟨1915602, by rfl⟩ : syracuseStep 5108273 = 3831205) B3831205
theorem B3405515 : Blo 2269435 3405515 := bstep (se 1 (by rfl) ⟨2554136, by rfl⟩ : syracuseStep 3405515 = 5108273) B5108273
theorem B2270343 : Blo 2269435 2270343 := bstep (se 1 (by rfl) ⟨1702757, by rfl⟩ : syracuseStep 2270343 = 3405515) B3405515
theorem B2554141 : Blo 2269435 2554141 := bbase (se 3 (by rfl) ⟨478901, by rfl⟩ : syracuseStep 2554141 = 957803) (by norm_num)
theorem B3405521 : Blo 2269435 3405521 := bstep (se 2 (by rfl) ⟨1277070, by rfl⟩ : syracuseStep 3405521 = 2554141) B2554141
theorem B2270347 : Blo 2269435 2270347 := bstep (se 1 (by rfl) ⟨1702760, by rfl⟩ : syracuseStep 2270347 = 3405521) B3405521
theorem B7662437 : Blo 2269435 7662437 := bbase (se 4 (by rfl) ⟨718353, by rfl⟩ : syracuseStep 7662437 = 1436707) (by norm_num)
theorem B5108291 : Blo 2269435 5108291 := bstep (se 1 (by rfl) ⟨3831218, by rfl⟩ : syracuseStep 5108291 = 7662437) B7662437
theorem B3405527 : Blo 2269435 3405527 := bstep (se 1 (by rfl) ⟨2554145, by rfl⟩ : syracuseStep 3405527 = 5108291) B5108291
theorem B2270351 : Blo 2269435 2270351 := bstep (se 1 (by rfl) ⟨1702763, by rfl⟩ : syracuseStep 2270351 = 3405527) B3405527
theorem B3405533 : Blo 2269435 3405533 := bbase (se 3 (by rfl) ⟨638537, by rfl⟩ : syracuseStep 3405533 = 1277075) (by norm_num)
theorem B2270355 : Blo 2269435 2270355 := bstep (se 1 (by rfl) ⟨1702766, by rfl⟩ : syracuseStep 2270355 = 3405533) B3405533
theorem B5108309 : Blo 2269435 5108309 := bbase (se 8 (by rfl) ⟨29931, by rfl⟩ : syracuseStep 5108309 = 59863) (by norm_num)
theorem B3405539 : Blo 2269435 3405539 := bstep (se 1 (by rfl) ⟨2554154, by rfl⟩ : syracuseStep 3405539 = 5108309) B5108309
theorem B2270359 : Blo 2269435 2270359 := bstep (se 1 (by rfl) ⟨1702769, by rfl⟩ : syracuseStep 2270359 = 3405539) B3405539
theorem B3636685 : Blo 2269435 3636685 := bbase (se 3 (by rfl) ⟨681878, by rfl⟩ : syracuseStep 3636685 = 1363757) (by norm_num)
theorem B4848913 : Blo 2269435 4848913 := bstep (se 2 (by rfl) ⟨1818342, by rfl⟩ : syracuseStep 4848913 = 3636685) B3636685
theorem B6465217 : Blo 2269435 6465217 := bstep (se 2 (by rfl) ⟨2424456, by rfl⟩ : syracuseStep 6465217 = 4848913) B4848913
theorem B8620289 : Blo 2269435 8620289 := bstep (se 2 (by rfl) ⟨3232608, by rfl⟩ : syracuseStep 8620289 = 6465217) B6465217
theorem B5746859 : Blo 2269435 5746859 := bstep (se 1 (by rfl) ⟨4310144, by rfl⟩ : syracuseStep 5746859 = 8620289) B8620289
theorem B3831239 : Blo 2269435 3831239 := bstep (se 1 (by rfl) ⟨2873429, by rfl⟩ : syracuseStep 3831239 = 5746859) B5746859
theorem B2554159 : Blo 2269435 2554159 := bstep (se 1 (by rfl) ⟨1915619, by rfl⟩ : syracuseStep 2554159 = 3831239) B3831239
theorem B3405545 : Blo 2269435 3405545 := bstep (se 2 (by rfl) ⟨1277079, by rfl⟩ : syracuseStep 3405545 = 2554159) B2554159
theorem B2270363 : Blo 2269435 2270363 := bstep (se 1 (by rfl) ⟨1702772, by rfl⟩ : syracuseStep 2270363 = 3405545) B3405545
theorem B29093525 : Blo 2269435 29093525 := bbase (se 6 (by rfl) ⟨681879, by rfl⟩ : syracuseStep 29093525 = 1363759) (by norm_num)
theorem B19395683 : Blo 2269435 19395683 := bstep (se 1 (by rfl) ⟨14546762, by rfl⟩ : syracuseStep 19395683 = 29093525) B29093525
theorem B12930455 : Blo 2269435 12930455 := bstep (se 1 (by rfl) ⟨9697841, by rfl⟩ : syracuseStep 12930455 = 19395683) B19395683
theorem B8620303 : Blo 2269435 8620303 := bstep (se 1 (by rfl) ⟨6465227, by rfl⟩ : syracuseStep 8620303 = 12930455) B12930455
theorem B11493737 : Blo 2269435 11493737 := bstep (se 2 (by rfl) ⟨4310151, by rfl⟩ : syracuseStep 11493737 = 8620303) B8620303
theorem B7662491 : Blo 2269435 7662491 := bstep (se 1 (by rfl) ⟨5746868, by rfl⟩ : syracuseStep 7662491 = 11493737) B11493737
theorem B5108327 : Blo 2269435 5108327 := bstep (se 1 (by rfl) ⟨3831245, by rfl⟩ : syracuseStep 5108327 = 7662491) B7662491
theorem B3405551 : Blo 2269435 3405551 := bstep (se 1 (by rfl) ⟨2554163, by rfl⟩ : syracuseStep 3405551 = 5108327) B5108327
theorem B2270367 : Blo 2269435 2270367 := bstep (se 1 (by rfl) ⟨1702775, by rfl⟩ : syracuseStep 2270367 = 3405551) B3405551
theorem B3405557 : Blo 2269435 3405557 := bbase (se 5 (by rfl) ⟨159635, by rfl⟩ : syracuseStep 3405557 = 319271) (by norm_num)
theorem B2270371 : Blo 2269435 2270371 := bstep (se 1 (by rfl) ⟨1702778, by rfl⟩ : syracuseStep 2270371 = 3405557) B3405557
theorem B9697877 : Blo 2269435 9697877 := bbase (se 8 (by rfl) ⟨56823, by rfl⟩ : syracuseStep 9697877 = 113647) (by norm_num)
theorem B6465251 : Blo 2269435 6465251 := bstep (se 1 (by rfl) ⟨4848938, by rfl⟩ : syracuseStep 6465251 = 9697877) B9697877
theorem B4310167 : Blo 2269435 4310167 := bstep (se 1 (by rfl) ⟨3232625, by rfl⟩ : syracuseStep 4310167 = 6465251) B6465251
theorem B5746889 : Blo 2269435 5746889 := bstep (se 2 (by rfl) ⟨2155083, by rfl⟩ : syracuseStep 5746889 = 4310167) B4310167
theorem B3831259 : Blo 2269435 3831259 := bstep (se 1 (by rfl) ⟨2873444, by rfl⟩ : syracuseStep 3831259 = 5746889) B5746889
theorem B5108345 : Blo 2269435 5108345 := bstep (se 2 (by rfl) ⟨1915629, by rfl⟩ : syracuseStep 5108345 = 3831259) B3831259
theorem B3405563 : Blo 2269435 3405563 := bstep (se 1 (by rfl) ⟨2554172, by rfl⟩ : syracuseStep 3405563 = 5108345) B5108345
theorem B2270375 : Blo 2269435 2270375 := bstep (se 1 (by rfl) ⟨1702781, by rfl⟩ : syracuseStep 2270375 = 3405563) B3405563
theorem B2554177 : Blo 2269435 2554177 := bbase (se 2 (by rfl) ⟨957816, by rfl⟩ : syracuseStep 2554177 = 1915633) (by norm_num)
theorem B3405569 : Blo 2269435 3405569 := bstep (se 2 (by rfl) ⟨1277088, by rfl⟩ : syracuseStep 3405569 = 2554177) B2554177
theorem B2270379 : Blo 2269435 2270379 := bstep (se 1 (by rfl) ⟨1702784, by rfl⟩ : syracuseStep 2270379 = 3405569) B3405569
theorem B5746909 : Blo 2269435 5746909 := bbase (se 3 (by rfl) ⟨1077545, by rfl⟩ : syracuseStep 5746909 = 2155091) (by norm_num)
theorem B7662545 : Blo 2269435 7662545 := bstep (se 2 (by rfl) ⟨2873454, by rfl⟩ : syracuseStep 7662545 = 5746909) B5746909
theorem B5108363 : Blo 2269435 5108363 := bstep (se 1 (by rfl) ⟨3831272, by rfl⟩ : syracuseStep 5108363 = 7662545) B7662545
theorem B3405575 : Blo 2269435 3405575 := bstep (se 1 (by rfl) ⟨2554181, by rfl⟩ : syracuseStep 3405575 = 5108363) B5108363
theorem B2270383 : Blo 2269435 2270383 := bstep (se 1 (by rfl) ⟨1702787, by rfl⟩ : syracuseStep 2270383 = 3405575) B3405575
theorem B3405581 : Blo 2269435 3405581 := bbase (se 3 (by rfl) ⟨638546, by rfl⟩ : syracuseStep 3405581 = 1277093) (by norm_num)
theorem B2270387 : Blo 2269435 2270387 := bstep (se 1 (by rfl) ⟨1702790, by rfl⟩ : syracuseStep 2270387 = 3405581) B3405581
theorem B5108381 : Blo 2269435 5108381 := bbase (se 3 (by rfl) ⟨957821, by rfl⟩ : syracuseStep 5108381 = 1915643) (by norm_num)
theorem B3405587 : Blo 2269435 3405587 := bstep (se 1 (by rfl) ⟨2554190, by rfl⟩ : syracuseStep 3405587 = 5108381) B5108381
theorem B2270391 : Blo 2269435 2270391 := bstep (se 1 (by rfl) ⟨1702793, by rfl⟩ : syracuseStep 2270391 = 3405587) B3405587
theorem B3831293 : Blo 2269435 3831293 := bbase (se 3 (by rfl) ⟨718367, by rfl⟩ : syracuseStep 3831293 = 1436735) (by norm_num)
theorem B2554195 : Blo 2269435 2554195 := bstep (se 1 (by rfl) ⟨1915646, by rfl⟩ : syracuseStep 2554195 = 3831293) B3831293
theorem B3405593 : Blo 2269435 3405593 := bstep (se 2 (by rfl) ⟨1277097, by rfl⟩ : syracuseStep 3405593 = 2554195) B2554195
theorem B2270395 : Blo 2269435 2270395 := bstep (se 1 (by rfl) ⟨1702796, by rfl⟩ : syracuseStep 2270395 = 3405593) B3405593
theorem B4848989 : Blo 2269435 4848989 := bbase (se 3 (by rfl) ⟨909185, by rfl⟩ : syracuseStep 4848989 = 1818371) (by norm_num)
theorem B12930637 : Blo 2269435 12930637 := bstep (se 3 (by rfl) ⟨2424494, by rfl⟩ : syracuseStep 12930637 = 4848989) B4848989
theorem B17240849 : Blo 2269435 17240849 := bstep (se 2 (by rfl) ⟨6465318, by rfl⟩ : syracuseStep 17240849 = 12930637) B12930637
theorem B11493899 : Blo 2269435 11493899 := bstep (se 1 (by rfl) ⟨8620424, by rfl⟩ : syracuseStep 11493899 = 17240849) B17240849
theorem B7662599 : Blo 2269435 7662599 := bstep (se 1 (by rfl) ⟨5746949, by rfl⟩ : syracuseStep 7662599 = 11493899) B11493899
theorem B5108399 : Blo 2269435 5108399 := bstep (se 1 (by rfl) ⟨3831299, by rfl⟩ : syracuseStep 5108399 = 7662599) B7662599
theorem B3405599 : Blo 2269435 3405599 := bstep (se 1 (by rfl) ⟨2554199, by rfl⟩ : syracuseStep 3405599 = 5108399) B5108399
theorem B2270399 : Blo 2269435 2270399 := bstep (se 1 (by rfl) ⟨1702799, by rfl⟩ : syracuseStep 2270399 = 3405599) B3405599
theorem B3405605 : Blo 2269435 3405605 := bbase (se 4 (by rfl) ⟨319275, by rfl⟩ : syracuseStep 3405605 = 638551) (by norm_num)
theorem B2270403 : Blo 2269435 2270403 := bstep (se 1 (by rfl) ⟨1702802, by rfl⟩ : syracuseStep 2270403 = 3405605) B3405605
theorem B2873485 : Blo 2269435 2873485 := bbase (se 3 (by rfl) ⟨538778, by rfl⟩ : syracuseStep 2873485 = 1077557) (by norm_num)
theorem B3831313 : Blo 2269435 3831313 := bstep (se 2 (by rfl) ⟨1436742, by rfl⟩ : syracuseStep 3831313 = 2873485) B2873485
theorem B5108417 : Blo 2269435 5108417 := bstep (se 2 (by rfl) ⟨1915656, by rfl⟩ : syracuseStep 5108417 = 3831313) B3831313
theorem B3405611 : Blo 2269435 3405611 := bstep (se 1 (by rfl) ⟨2554208, by rfl⟩ : syracuseStep 3405611 = 5108417) B5108417
theorem B2270407 : Blo 2269435 2270407 := bstep (se 1 (by rfl) ⟨1702805, by rfl⟩ : syracuseStep 2270407 = 3405611) B3405611
theorem B2554213 : Blo 2269435 2554213 := bbase (se 4 (by rfl) ⟨239457, by rfl⟩ : syracuseStep 2554213 = 478915) (by norm_num)
theorem B3405617 : Blo 2269435 3405617 := bstep (se 2 (by rfl) ⟨1277106, by rfl⟩ : syracuseStep 3405617 = 2554213) B2554213
theorem B2270411 : Blo 2269435 2270411 := bstep (se 1 (by rfl) ⟨1702808, by rfl⟩ : syracuseStep 2270411 = 3405617) B3405617
theorem B6465365 : Blo 2269435 6465365 := bbase (se 9 (by rfl) ⟨18941, by rfl⟩ : syracuseStep 6465365 = 37883) (by norm_num)
theorem B4310243 : Blo 2269435 4310243 := bstep (se 1 (by rfl) ⟨3232682, by rfl⟩ : syracuseStep 4310243 = 6465365) B6465365
theorem B2873495 : Blo 2269435 2873495 := bstep (se 1 (by rfl) ⟨2155121, by rfl⟩ : syracuseStep 2873495 = 4310243) B4310243
theorem B7662653 : Blo 2269435 7662653 := bstep (se 3 (by rfl) ⟨1436747, by rfl⟩ : syracuseStep 7662653 = 2873495) B2873495
theorem B5108435 : Blo 2269435 5108435 := bstep (se 1 (by rfl) ⟨3831326, by rfl⟩ : syracuseStep 5108435 = 7662653) B7662653
theorem B3405623 : Blo 2269435 3405623 := bstep (se 1 (by rfl) ⟨2554217, by rfl⟩ : syracuseStep 3405623 = 5108435) B5108435
theorem B2270415 : Blo 2269435 2270415 := bstep (se 1 (by rfl) ⟨1702811, by rfl⟩ : syracuseStep 2270415 = 3405623) B3405623
theorem B3405629 : Blo 2269435 3405629 := bbase (se 3 (by rfl) ⟨638555, by rfl⟩ : syracuseStep 3405629 = 1277111) (by norm_num)
theorem B2270419 : Blo 2269435 2270419 := bstep (se 1 (by rfl) ⟨1702814, by rfl⟩ : syracuseStep 2270419 = 3405629) B3405629
theorem B5108453 : Blo 2269435 5108453 := bbase (se 4 (by rfl) ⟨478917, by rfl⟩ : syracuseStep 5108453 = 957835) (by norm_num)
theorem B3405635 : Blo 2269435 3405635 := bstep (se 1 (by rfl) ⟨2554226, by rfl⟩ : syracuseStep 3405635 = 5108453) B5108453
theorem B2270423 : Blo 2269435 2270423 := bstep (se 1 (by rfl) ⟨1702817, by rfl⟩ : syracuseStep 2270423 = 3405635) B3405635
theorem B5747021 : Blo 2269435 5747021 := bbase (se 3 (by rfl) ⟨1077566, by rfl⟩ : syracuseStep 5747021 = 2155133) (by norm_num)
theorem B3831347 : Blo 2269435 3831347 := bstep (se 1 (by rfl) ⟨2873510, by rfl⟩ : syracuseStep 3831347 = 5747021) B5747021
theorem B2554231 : Blo 2269435 2554231 := bstep (se 1 (by rfl) ⟨1915673, by rfl⟩ : syracuseStep 2554231 = 3831347) B3831347
theorem B3405641 : Blo 2269435 3405641 := bstep (se 2 (by rfl) ⟨1277115, by rfl⟩ : syracuseStep 3405641 = 2554231) B2554231
theorem B2270427 : Blo 2269435 2270427 := bstep (se 1 (by rfl) ⟨1702820, by rfl⟩ : syracuseStep 2270427 = 3405641) B3405641
theorem B2424529 : Blo 2269435 2424529 := bbase (se 2 (by rfl) ⟨909198, by rfl⟩ : syracuseStep 2424529 = 1818397) (by norm_num)
theorem B3232705 : Blo 2269435 3232705 := bstep (se 2 (by rfl) ⟨1212264, by rfl⟩ : syracuseStep 3232705 = 2424529) B2424529
theorem B4310273 : Blo 2269435 4310273 := bstep (se 2 (by rfl) ⟨1616352, by rfl⟩ : syracuseStep 4310273 = 3232705) B3232705
theorem B11494061 : Blo 2269435 11494061 := bstep (se 3 (by rfl) ⟨2155136, by rfl⟩ : syracuseStep 11494061 = 4310273) B4310273
theorem B7662707 : Blo 2269435 7662707 := bstep (se 1 (by rfl) ⟨5747030, by rfl⟩ : syracuseStep 7662707 = 11494061) B11494061
theorem B5108471 : Blo 2269435 5108471 := bstep (se 1 (by rfl) ⟨3831353, by rfl⟩ : syracuseStep 5108471 = 7662707) B7662707
theorem B3405647 : Blo 2269435 3405647 := bstep (se 1 (by rfl) ⟨2554235, by rfl⟩ : syracuseStep 3405647 = 5108471) B5108471
theorem B2270431 : Blo 2269435 2270431 := bstep (se 1 (by rfl) ⟨1702823, by rfl⟩ : syracuseStep 2270431 = 3405647) B3405647
theorem B3405653 : Blo 2269435 3405653 := bbase (se 9 (by rfl) ⟨9977, by rfl⟩ : syracuseStep 3405653 = 19955) (by norm_num)
theorem B2270435 : Blo 2269435 2270435 := bstep (se 1 (by rfl) ⟨1702826, by rfl⟩ : syracuseStep 2270435 = 3405653) B3405653
theorem B2727605 : Blo 2269435 2727605 := bbase (se 5 (by rfl) ⟨127856, by rfl⟩ : syracuseStep 2727605 = 255713) (by norm_num)
theorem B7273613 : Blo 2269435 7273613 := bstep (se 3 (by rfl) ⟨1363802, by rfl⟩ : syracuseStep 7273613 = 2727605) B2727605
theorem B4849075 : Blo 2269435 4849075 := bstep (se 1 (by rfl) ⟨3636806, by rfl⟩ : syracuseStep 4849075 = 7273613) B7273613
theorem B6465433 : Blo 2269435 6465433 := bstep (se 2 (by rfl) ⟨2424537, by rfl⟩ : syracuseStep 6465433 = 4849075) B4849075
theorem B8620577 : Blo 2269435 8620577 := bstep (se 2 (by rfl) ⟨3232716, by rfl⟩ : syracuseStep 8620577 = 6465433) B6465433
theorem B5747051 : Blo 2269435 5747051 := bstep (se 1 (by rfl) ⟨4310288, by rfl⟩ : syracuseStep 5747051 = 8620577) B8620577
theorem B3831367 : Blo 2269435 3831367 := bstep (se 1 (by rfl) ⟨2873525, by rfl⟩ : syracuseStep 3831367 = 5747051) B5747051
theorem B5108489 : Blo 2269435 5108489 := bstep (se 2 (by rfl) ⟨1915683, by rfl⟩ : syracuseStep 5108489 = 3831367) B3831367
theorem B3405659 : Blo 2269435 3405659 := bstep (se 1 (by rfl) ⟨2554244, by rfl⟩ : syracuseStep 3405659 = 5108489) B5108489
theorem B2270439 : Blo 2269435 2270439 := bstep (se 1 (by rfl) ⟨1702829, by rfl⟩ : syracuseStep 2270439 = 3405659) B3405659
theorem B2554249 : Blo 2269435 2554249 := bbase (se 2 (by rfl) ⟨957843, by rfl⟩ : syracuseStep 2554249 = 1915687) (by norm_num)
theorem B3405665 : Blo 2269435 3405665 := bstep (se 2 (by rfl) ⟨1277124, by rfl⟩ : syracuseStep 3405665 = 2554249) B2554249
theorem B2270443 : Blo 2269435 2270443 := bstep (se 1 (by rfl) ⟨1702832, by rfl⟩ : syracuseStep 2270443 = 3405665) B3405665
theorem B65462741 : Blo 2269435 65462741 := bbase (se 7 (by rfl) ⟨767141, by rfl⟩ : syracuseStep 65462741 = 1534283) (by norm_num)
theorem B43641827 : Blo 2269435 43641827 := bstep (se 1 (by rfl) ⟨32731370, by rfl⟩ : syracuseStep 43641827 = 65462741) B65462741
theorem B29094551 : Blo 2269435 29094551 := bstep (se 1 (by rfl) ⟨21820913, by rfl⟩ : syracuseStep 29094551 = 43641827) B43641827
theorem B19396367 : Blo 2269435 19396367 := bstep (se 1 (by rfl) ⟨14547275, by rfl⟩ : syracuseStep 19396367 = 29094551) B29094551
theorem B12930911 : Blo 2269435 12930911 := bstep (se 1 (by rfl) ⟨9698183, by rfl⟩ : syracuseStep 12930911 = 19396367) B19396367
theorem B8620607 : Blo 2269435 8620607 := bstep (se 1 (by rfl) ⟨6465455, by rfl⟩ : syracuseStep 8620607 = 12930911) B12930911
theorem B5747071 : Blo 2269435 5747071 := bstep (se 1 (by rfl) ⟨4310303, by rfl⟩ : syracuseStep 5747071 = 8620607) B8620607
theorem B7662761 : Blo 2269435 7662761 := bstep (se 2 (by rfl) ⟨2873535, by rfl⟩ : syracuseStep 7662761 = 5747071) B5747071
theorem B5108507 : Blo 2269435 5108507 := bstep (se 1 (by rfl) ⟨3831380, by rfl⟩ : syracuseStep 5108507 = 7662761) B7662761
theorem B3405671 : Blo 2269435 3405671 := bstep (se 1 (by rfl) ⟨2554253, by rfl⟩ : syracuseStep 3405671 = 5108507) B5108507
theorem B2270447 : Blo 2269435 2270447 := bstep (se 1 (by rfl) ⟨1702835, by rfl⟩ : syracuseStep 2270447 = 3405671) B3405671
theorem B3405677 : Blo 2269435 3405677 := bbase (se 3 (by rfl) ⟨638564, by rfl⟩ : syracuseStep 3405677 = 1277129) (by norm_num)
theorem B2270451 : Blo 2269435 2270451 := bstep (se 1 (by rfl) ⟨1702838, by rfl⟩ : syracuseStep 2270451 = 3405677) B3405677
theorem B5108525 : Blo 2269435 5108525 := bbase (se 3 (by rfl) ⟨957848, by rfl⟩ : syracuseStep 5108525 = 1915697) (by norm_num)
theorem B3405683 : Blo 2269435 3405683 := bstep (se 1 (by rfl) ⟨2554262, by rfl⟩ : syracuseStep 3405683 = 5108525) B5108525
theorem B2270455 : Blo 2269435 2270455 := bstep (se 1 (by rfl) ⟨1702841, by rfl⟩ : syracuseStep 2270455 = 3405683) B3405683
theorem B6220901 : Blo 2269435 6220901 := bbase (se 4 (by rfl) ⟨583209, by rfl⟩ : syracuseStep 6220901 = 1166419) (by norm_num)
theorem B16589069 : Blo 2269435 16589069 := bstep (se 3 (by rfl) ⟨3110450, by rfl⟩ : syracuseStep 16589069 = 6220901) B6220901
theorem B11059379 : Blo 2269435 11059379 := bstep (se 1 (by rfl) ⟨8294534, by rfl⟩ : syracuseStep 11059379 = 16589069) B16589069
theorem B7372919 : Blo 2269435 7372919 := bstep (se 1 (by rfl) ⟨5529689, by rfl⟩ : syracuseStep 7372919 = 11059379) B11059379
theorem B4915279 : Blo 2269435 4915279 := bstep (se 1 (by rfl) ⟨3686459, by rfl⟩ : syracuseStep 4915279 = 7372919) B7372919
theorem B6553705 : Blo 2269435 6553705 := bstep (se 2 (by rfl) ⟨2457639, by rfl⟩ : syracuseStep 6553705 = 4915279) B4915279
theorem B8738273 : Blo 2269435 8738273 := bstep (se 2 (by rfl) ⟨3276852, by rfl⟩ : syracuseStep 8738273 = 6553705) B6553705
theorem B5825515 : Blo 2269435 5825515 := bstep (se 1 (by rfl) ⟨4369136, by rfl⟩ : syracuseStep 5825515 = 8738273) B8738273
theorem B7767353 : Blo 2269435 7767353 := bstep (se 2 (by rfl) ⟨2912757, by rfl⟩ : syracuseStep 7767353 = 5825515) B5825515
theorem B20712941 : Blo 2269435 20712941 := bstep (se 3 (by rfl) ⟨3883676, by rfl⟩ : syracuseStep 20712941 = 7767353) B7767353
theorem B13808627 : Blo 2269435 13808627 := bstep (se 1 (by rfl) ⟨10356470, by rfl⟩ : syracuseStep 13808627 = 20712941) B20712941
theorem B9205751 : Blo 2269435 9205751 := bstep (se 1 (by rfl) ⟨6904313, by rfl⟩ : syracuseStep 9205751 = 13808627) B13808627
theorem B6137167 : Blo 2269435 6137167 := bstep (se 1 (by rfl) ⟨4602875, by rfl⟩ : syracuseStep 6137167 = 9205751) B9205751
theorem B8182889 : Blo 2269435 8182889 := bstep (se 2 (by rfl) ⟨3068583, by rfl⟩ : syracuseStep 8182889 = 6137167) B6137167
theorem B5455259 : Blo 2269435 5455259 := bstep (se 1 (by rfl) ⟨4091444, by rfl⟩ : syracuseStep 5455259 = 8182889) B8182889
theorem B3636839 : Blo 2269435 3636839 := bstep (se 1 (by rfl) ⟨2727629, by rfl⟩ : syracuseStep 3636839 = 5455259) B5455259
theorem B9698237 : Blo 2269435 9698237 := bstep (se 3 (by rfl) ⟨1818419, by rfl⟩ : syracuseStep 9698237 = 3636839) B3636839
theorem B6465491 : Blo 2269435 6465491 := bstep (se 1 (by rfl) ⟨4849118, by rfl⟩ : syracuseStep 6465491 = 9698237) B9698237
theorem B4310327 : Blo 2269435 4310327 := bstep (se 1 (by rfl) ⟨3232745, by rfl⟩ : syracuseStep 4310327 = 6465491) B6465491
theorem B2873551 : Blo 2269435 2873551 := bstep (se 1 (by rfl) ⟨2155163, by rfl⟩ : syracuseStep 2873551 = 4310327) B4310327
theorem B3831401 : Blo 2269435 3831401 := bstep (se 2 (by rfl) ⟨1436775, by rfl⟩ : syracuseStep 3831401 = 2873551) B2873551
theorem B2554267 : Blo 2269435 2554267 := bstep (se 1 (by rfl) ⟨1915700, by rfl⟩ : syracuseStep 2554267 = 3831401) B3831401
theorem B3405689 : Blo 2269435 3405689 := bstep (se 2 (by rfl) ⟨1277133, by rfl⟩ : syracuseStep 3405689 = 2554267) B2554267
theorem B2270459 : Blo 2269435 2270459 := bstep (se 1 (by rfl) ⟨1702844, by rfl⟩ : syracuseStep 2270459 = 3405689) B3405689
theorem B10910533 : Blo 2269435 10910533 := bbase (se 4 (by rfl) ⟨1022862, by rfl⟩ : syracuseStep 10910533 = 2045725) (by norm_num)
theorem B14547377 : Blo 2269435 14547377 := bstep (se 2 (by rfl) ⟨5455266, by rfl⟩ : syracuseStep 14547377 = 10910533) B10910533
theorem B38793005 : Blo 2269435 38793005 := bstep (se 3 (by rfl) ⟨7273688, by rfl⟩ : syracuseStep 38793005 = 14547377) B14547377
theorem B25862003 : Blo 2269435 25862003 := bstep (se 1 (by rfl) ⟨19396502, by rfl⟩ : syracuseStep 25862003 = 38793005) B38793005
theorem B17241335 : Blo 2269435 17241335 := bstep (se 1 (by rfl) ⟨12931001, by rfl⟩ : syracuseStep 17241335 = 25862003) B25862003
theorem B11494223 : Blo 2269435 11494223 := bstep (se 1 (by rfl) ⟨8620667, by rfl⟩ : syracuseStep 11494223 = 17241335) B17241335
theorem B7662815 : Blo 2269435 7662815 := bstep (se 1 (by rfl) ⟨5747111, by rfl⟩ : syracuseStep 7662815 = 11494223) B11494223
theorem B5108543 : Blo 2269435 5108543 := bstep (se 1 (by rfl) ⟨3831407, by rfl⟩ : syracuseStep 5108543 = 7662815) B7662815
theorem B3405695 : Blo 2269435 3405695 := bstep (se 1 (by rfl) ⟨2554271, by rfl⟩ : syracuseStep 3405695 = 5108543) B5108543
theorem B2270463 : Blo 2269435 2270463 := bstep (se 1 (by rfl) ⟨1702847, by rfl⟩ : syracuseStep 2270463 = 3405695) B3405695
theorem B3405701 : Blo 2269435 3405701 := bbase (se 4 (by rfl) ⟨319284, by rfl⟩ : syracuseStep 3405701 = 638569) (by norm_num)
theorem B2270467 : Blo 2269435 2270467 := bstep (se 1 (by rfl) ⟨1702850, by rfl⟩ : syracuseStep 2270467 = 3405701) B3405701
theorem B3831421 : Blo 2269435 3831421 := bbase (se 3 (by rfl) ⟨718391, by rfl⟩ : syracuseStep 3831421 = 1436783) (by norm_num)
theorem B5108561 : Blo 2269435 5108561 := bstep (se 2 (by rfl) ⟨1915710, by rfl⟩ : syracuseStep 5108561 = 3831421) B3831421
theorem B3405707 : Blo 2269435 3405707 := bstep (se 1 (by rfl) ⟨2554280, by rfl⟩ : syracuseStep 3405707 = 5108561) B5108561
theorem B2270471 : Blo 2269435 2270471 := bstep (se 1 (by rfl) ⟨1702853, by rfl⟩ : syracuseStep 2270471 = 3405707) B3405707
theorem B2554285 : Blo 2269435 2554285 := bbase (se 3 (by rfl) ⟨478928, by rfl⟩ : syracuseStep 2554285 = 957857) (by norm_num)
theorem B3405713 : Blo 2269435 3405713 := bstep (se 2 (by rfl) ⟨1277142, by rfl⟩ : syracuseStep 3405713 = 2554285) B2554285
theorem B2270475 : Blo 2269435 2270475 := bstep (se 1 (by rfl) ⟨1702856, by rfl⟩ : syracuseStep 2270475 = 3405713) B3405713
theorem B7662869 : Blo 2269435 7662869 := bbase (se 6 (by rfl) ⟨179598, by rfl⟩ : syracuseStep 7662869 = 359197) (by norm_num)
theorem B5108579 : Blo 2269435 5108579 := bstep (se 1 (by rfl) ⟨3831434, by rfl⟩ : syracuseStep 5108579 = 7662869) B7662869
theorem B3405719 : Blo 2269435 3405719 := bstep (se 1 (by rfl) ⟨2554289, by rfl⟩ : syracuseStep 3405719 = 5108579) B5108579
theorem B2270479 : Blo 2269435 2270479 := bstep (se 1 (by rfl) ⟨1702859, by rfl⟩ : syracuseStep 2270479 = 3405719) B3405719
theorem B3405725 : Blo 2269435 3405725 := bbase (se 3 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 3405725 = 1277147) (by norm_num)
theorem B2270483 : Blo 2269435 2270483 := bstep (se 1 (by rfl) ⟨1702862, by rfl⟩ : syracuseStep 2270483 = 3405725) B3405725
theorem B5108597 : Blo 2269435 5108597 := bbase (se 5 (by rfl) ⟨239465, by rfl⟩ : syracuseStep 5108597 = 478931) (by norm_num)
theorem B3405731 : Blo 2269435 3405731 := bstep (se 1 (by rfl) ⟨2554298, by rfl⟩ : syracuseStep 3405731 = 5108597) B5108597
theorem B2270487 : Blo 2269435 2270487 := bstep (se 1 (by rfl) ⟨1702865, by rfl⟩ : syracuseStep 2270487 = 3405731) B3405731
theorem B37325909 : Blo 2269435 37325909 := bbase (se 8 (by rfl) ⟨218706, by rfl⟩ : syracuseStep 37325909 = 437413) (by norm_num)
theorem B24883939 : Blo 2269435 24883939 := bstep (se 1 (by rfl) ⟨18662954, by rfl⟩ : syracuseStep 24883939 = 37325909) B37325909
theorem B33178585 : Blo 2269435 33178585 := bstep (se 2 (by rfl) ⟨12441969, by rfl⟩ : syracuseStep 33178585 = 24883939) B24883939
theorem B44238113 : Blo 2269435 44238113 := bstep (se 2 (by rfl) ⟨16589292, by rfl⟩ : syracuseStep 44238113 = 33178585) B33178585
theorem B29492075 : Blo 2269435 29492075 := bstep (se 1 (by rfl) ⟨22119056, by rfl⟩ : syracuseStep 29492075 = 44238113) B44238113
theorem B19661383 : Blo 2269435 19661383 := bstep (se 1 (by rfl) ⟨14746037, by rfl⟩ : syracuseStep 19661383 = 29492075) B29492075
theorem B26215177 : Blo 2269435 26215177 := bstep (se 2 (by rfl) ⟨9830691, by rfl⟩ : syracuseStep 26215177 = 19661383) B19661383
theorem B34953569 : Blo 2269435 34953569 := bstep (se 2 (by rfl) ⟨13107588, by rfl⟩ : syracuseStep 34953569 = 26215177) B26215177
theorem B23302379 : Blo 2269435 23302379 := bstep (se 1 (by rfl) ⟨17476784, by rfl⟩ : syracuseStep 23302379 = 34953569) B34953569
theorem B15534919 : Blo 2269435 15534919 := bstep (se 1 (by rfl) ⟨11651189, by rfl⟩ : syracuseStep 15534919 = 23302379) B23302379
theorem B82852901 : Blo 2269435 82852901 := bstep (se 4 (by rfl) ⟨7767459, by rfl⟩ : syracuseStep 82852901 = 15534919) B15534919
theorem B55235267 : Blo 2269435 55235267 := bstep (se 1 (by rfl) ⟨41426450, by rfl⟩ : syracuseStep 55235267 = 82852901) B82852901
theorem B36823511 : Blo 2269435 36823511 := bstep (se 1 (by rfl) ⟨27617633, by rfl⟩ : syracuseStep 36823511 = 55235267) B55235267
theorem B24549007 : Blo 2269435 24549007 := bstep (se 1 (by rfl) ⟨18411755, by rfl⟩ : syracuseStep 24549007 = 36823511) B36823511
theorem B32732009 : Blo 2269435 32732009 := bstep (se 2 (by rfl) ⟨12274503, by rfl⟩ : syracuseStep 32732009 = 24549007) B24549007
theorem B21821339 : Blo 2269435 21821339 := bstep (se 1 (by rfl) ⟨16366004, by rfl⟩ : syracuseStep 21821339 = 32732009) B32732009
theorem B14547559 : Blo 2269435 14547559 := bstep (se 1 (by rfl) ⟨10910669, by rfl⟩ : syracuseStep 14547559 = 21821339) B21821339
theorem B19396745 : Blo 2269435 19396745 := bstep (se 2 (by rfl) ⟨7273779, by rfl⟩ : syracuseStep 19396745 = 14547559) B14547559
theorem B12931163 : Blo 2269435 12931163 := bstep (se 1 (by rfl) ⟨9698372, by rfl⟩ : syracuseStep 12931163 = 19396745) B19396745
theorem B8620775 : Blo 2269435 8620775 := bstep (se 1 (by rfl) ⟨6465581, by rfl⟩ : syracuseStep 8620775 = 12931163) B12931163
theorem B5747183 : Blo 2269435 5747183 := bstep (se 1 (by rfl) ⟨4310387, by rfl⟩ : syracuseStep 5747183 = 8620775) B8620775
theorem B3831455 : Blo 2269435 3831455 := bstep (se 1 (by rfl) ⟨2873591, by rfl⟩ : syracuseStep 3831455 = 5747183) B5747183
theorem B2554303 : Blo 2269435 2554303 := bstep (se 1 (by rfl) ⟨1915727, by rfl⟩ : syracuseStep 2554303 = 3831455) B3831455
theorem B3405737 : Blo 2269435 3405737 := bstep (se 2 (by rfl) ⟨1277151, by rfl⟩ : syracuseStep 3405737 = 2554303) B2554303
theorem B2270491 : Blo 2269435 2270491 := bstep (se 1 (by rfl) ⟨1702868, by rfl⟩ : syracuseStep 2270491 = 3405737) B3405737
theorem B8620789 : Blo 2269435 8620789 := bbase (se 5 (by rfl) ⟨404099, by rfl⟩ : syracuseStep 8620789 = 808199) (by norm_num)
theorem B11494385 : Blo 2269435 11494385 := bstep (se 2 (by rfl) ⟨4310394, by rfl⟩ : syracuseStep 11494385 = 8620789) B8620789
theorem B7662923 : Blo 2269435 7662923 := bstep (se 1 (by rfl) ⟨5747192, by rfl⟩ : syracuseStep 7662923 = 11494385) B11494385
theorem B5108615 : Blo 2269435 5108615 := bstep (se 1 (by rfl) ⟨3831461, by rfl⟩ : syracuseStep 5108615 = 7662923) B7662923
theorem B3405743 : Blo 2269435 3405743 := bstep (se 1 (by rfl) ⟨2554307, by rfl⟩ : syracuseStep 3405743 = 5108615) B5108615
theorem B2270495 : Blo 2269435 2270495 := bstep (se 1 (by rfl) ⟨1702871, by rfl⟩ : syracuseStep 2270495 = 3405743) B3405743
theorem B3405749 : Blo 2269435 3405749 := bbase (se 5 (by rfl) ⟨159644, by rfl⟩ : syracuseStep 3405749 = 319289) (by norm_num)
theorem B2270499 : Blo 2269435 2270499 := bstep (se 1 (by rfl) ⟨1702874, by rfl⟩ : syracuseStep 2270499 = 3405749) B3405749
theorem B5747213 : Blo 2269435 5747213 := bbase (se 3 (by rfl) ⟨1077602, by rfl⟩ : syracuseStep 5747213 = 2155205) (by norm_num)
theorem B3831475 : Blo 2269435 3831475 := bstep (se 1 (by rfl) ⟨2873606, by rfl⟩ : syracuseStep 3831475 = 5747213) B5747213
theorem B5108633 : Blo 2269435 5108633 := bstep (se 2 (by rfl) ⟨1915737, by rfl⟩ : syracuseStep 5108633 = 3831475) B3831475
theorem B3405755 : Blo 2269435 3405755 := bstep (se 1 (by rfl) ⟨2554316, by rfl⟩ : syracuseStep 3405755 = 5108633) B5108633
theorem B2270503 : Blo 2269435 2270503 := bstep (se 1 (by rfl) ⟨1702877, by rfl⟩ : syracuseStep 2270503 = 3405755) B3405755
theorem B2554321 : Blo 2269435 2554321 := bbase (se 2 (by rfl) ⟨957870, by rfl⟩ : syracuseStep 2554321 = 1915741) (by norm_num)
theorem B3405761 : Blo 2269435 3405761 := bstep (se 2 (by rfl) ⟨1277160, by rfl⟩ : syracuseStep 3405761 = 2554321) B2554321
theorem B2270507 : Blo 2269435 2270507 := bstep (se 1 (by rfl) ⟨1702880, by rfl⟩ : syracuseStep 2270507 = 3405761) B3405761
theorem B4849229 : Blo 2269435 4849229 := bbase (se 3 (by rfl) ⟨909230, by rfl⟩ : syracuseStep 4849229 = 1818461) (by norm_num)
theorem B3232819 : Blo 2269435 3232819 := bstep (se 1 (by rfl) ⟨2424614, by rfl⟩ : syracuseStep 3232819 = 4849229) B4849229
theorem B4310425 : Blo 2269435 4310425 := bstep (se 2 (by rfl) ⟨1616409, by rfl⟩ : syracuseStep 4310425 = 3232819) B3232819
theorem B5747233 : Blo 2269435 5747233 := bstep (se 2 (by rfl) ⟨2155212, by rfl⟩ : syracuseStep 5747233 = 4310425) B4310425
theorem B7662977 : Blo 2269435 7662977 := bstep (se 2 (by rfl) ⟨2873616, by rfl⟩ : syracuseStep 7662977 = 5747233) B5747233
theorem B5108651 : Blo 2269435 5108651 := bstep (se 1 (by rfl) ⟨3831488, by rfl⟩ : syracuseStep 5108651 = 7662977) B7662977
theorem B3405767 : Blo 2269435 3405767 := bstep (se 1 (by rfl) ⟨2554325, by rfl⟩ : syracuseStep 3405767 = 5108651) B5108651
theorem B2270511 : Blo 2269435 2270511 := bstep (se 1 (by rfl) ⟨1702883, by rfl⟩ : syracuseStep 2270511 = 3405767) B3405767
theorem B3405773 : Blo 2269435 3405773 := bbase (se 3 (by rfl) ⟨638582, by rfl⟩ : syracuseStep 3405773 = 1277165) (by norm_num)
theorem B2270515 : Blo 2269435 2270515 := bstep (se 1 (by rfl) ⟨1702886, by rfl⟩ : syracuseStep 2270515 = 3405773) B3405773
theorem B5108669 : Blo 2269435 5108669 := bbase (se 3 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 5108669 = 1915751) (by norm_num)
theorem B3405779 : Blo 2269435 3405779 := bstep (se 1 (by rfl) ⟨2554334, by rfl⟩ : syracuseStep 3405779 = 5108669) B5108669
theorem B2270519 : Blo 2269435 2270519 := bstep (se 1 (by rfl) ⟨1702889, by rfl⟩ : syracuseStep 2270519 = 3405779) B3405779
theorem B3831509 : Blo 2269435 3831509 := bbase (se 7 (by rfl) ⟨44900, by rfl⟩ : syracuseStep 3831509 = 89801) (by norm_num)
theorem B2554339 : Blo 2269435 2554339 := bstep (se 1 (by rfl) ⟨1915754, by rfl⟩ : syracuseStep 2554339 = 3831509) B3831509
theorem B3405785 : Blo 2269435 3405785 := bstep (se 2 (by rfl) ⟨1277169, by rfl⟩ : syracuseStep 3405785 = 2554339) B2554339
theorem B2270523 : Blo 2269435 2270523 := bstep (se 1 (by rfl) ⟨1702892, by rfl⟩ : syracuseStep 2270523 = 3405785) B3405785
theorem B5455421 : Blo 2269435 5455421 := bbase (se 3 (by rfl) ⟨1022891, by rfl⟩ : syracuseStep 5455421 = 2045783) (by norm_num)
theorem B3636947 : Blo 2269435 3636947 := bstep (se 1 (by rfl) ⟨2727710, by rfl⟩ : syracuseStep 3636947 = 5455421) B5455421
theorem B9698525 : Blo 2269435 9698525 := bstep (se 3 (by rfl) ⟨1818473, by rfl⟩ : syracuseStep 9698525 = 3636947) B3636947
theorem B6465683 : Blo 2269435 6465683 := bstep (se 1 (by rfl) ⟨4849262, by rfl⟩ : syracuseStep 6465683 = 9698525) B9698525
theorem B17241821 : Blo 2269435 17241821 := bstep (se 3 (by rfl) ⟨3232841, by rfl⟩ : syracuseStep 17241821 = 6465683) B6465683
theorem B11494547 : Blo 2269435 11494547 := bstep (se 1 (by rfl) ⟨8620910, by rfl⟩ : syracuseStep 11494547 = 17241821) B17241821
theorem B7663031 : Blo 2269435 7663031 := bstep (se 1 (by rfl) ⟨5747273, by rfl⟩ : syracuseStep 7663031 = 11494547) B11494547
theorem B5108687 : Blo 2269435 5108687 := bstep (se 1 (by rfl) ⟨3831515, by rfl⟩ : syracuseStep 5108687 = 7663031) B7663031
theorem B3405791 : Blo 2269435 3405791 := bstep (se 1 (by rfl) ⟨2554343, by rfl⟩ : syracuseStep 3405791 = 5108687) B5108687
theorem B2270527 : Blo 2269435 2270527 := bstep (se 1 (by rfl) ⟨1702895, by rfl⟩ : syracuseStep 2270527 = 3405791) B3405791
theorem B3405797 : Blo 2269435 3405797 := bbase (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) (by norm_num)
theorem B2270531 : Blo 2269435 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B4091581 : Blo 2269435 4091581 := bbase (se 3 (by rfl) ⟨767171, by rfl⟩ : syracuseStep 4091581 = 1534343) (by norm_num)
theorem B5455441 : Blo 2269435 5455441 := bstep (se 2 (by rfl) ⟨2045790, by rfl⟩ : syracuseStep 5455441 = 4091581) B4091581
theorem B7273921 : Blo 2269435 7273921 := bstep (se 2 (by rfl) ⟨2727720, by rfl⟩ : syracuseStep 7273921 = 5455441) B5455441
theorem B9698561 : Blo 2269435 9698561 := bstep (se 2 (by rfl) ⟨3636960, by rfl⟩ : syracuseStep 9698561 = 7273921) B7273921
theorem B6465707 : Blo 2269435 6465707 := bstep (se 1 (by rfl) ⟨4849280, by rfl⟩ : syracuseStep 6465707 = 9698561) B9698561
theorem B4310471 : Blo 2269435 4310471 := bstep (se 1 (by rfl) ⟨3232853, by rfl⟩ : syracuseStep 4310471 = 6465707) B6465707
theorem B2873647 : Blo 2269435 2873647 := bstep (se 1 (by rfl) ⟨2155235, by rfl⟩ : syracuseStep 2873647 = 4310471) B4310471
theorem B3831529 : Blo 2269435 3831529 := bstep (se 2 (by rfl) ⟨1436823, by rfl⟩ : syracuseStep 3831529 = 2873647) B2873647
theorem B5108705 : Blo 2269435 5108705 := bstep (se 2 (by rfl) ⟨1915764, by rfl⟩ : syracuseStep 5108705 = 3831529) B3831529
theorem B3405803 : Blo 2269435 3405803 := bstep (se 1 (by rfl) ⟨2554352, by rfl⟩ : syracuseStep 3405803 = 5108705) B5108705
theorem B2270535 : Blo 2269435 2270535 := bstep (se 1 (by rfl) ⟨1702901, by rfl⟩ : syracuseStep 2270535 = 3405803) B3405803
theorem B2554357 : Blo 2269435 2554357 := bbase (se 5 (by rfl) ⟨119735, by rfl⟩ : syracuseStep 2554357 = 239471) (by norm_num)
theorem B3405809 : Blo 2269435 3405809 := bstep (se 2 (by rfl) ⟨1277178, by rfl⟩ : syracuseStep 3405809 = 2554357) B2554357
theorem B2270539 : Blo 2269435 2270539 := bstep (se 1 (by rfl) ⟨1702904, by rfl⟩ : syracuseStep 2270539 = 3405809) B3405809
theorem B2873657 : Blo 2269435 2873657 := bbase (se 2 (by rfl) ⟨1077621, by rfl⟩ : syracuseStep 2873657 = 2155243) (by norm_num)
theorem B7663085 : Blo 2269435 7663085 := bstep (se 3 (by rfl) ⟨1436828, by rfl⟩ : syracuseStep 7663085 = 2873657) B2873657
theorem B5108723 : Blo 2269435 5108723 := bstep (se 1 (by rfl) ⟨3831542, by rfl⟩ : syracuseStep 5108723 = 7663085) B7663085
theorem B3405815 : Blo 2269435 3405815 := bstep (se 1 (by rfl) ⟨2554361, by rfl⟩ : syracuseStep 3405815 = 5108723) B5108723
theorem B2270543 : Blo 2269435 2270543 := bstep (se 1 (by rfl) ⟨1702907, by rfl⟩ : syracuseStep 2270543 = 3405815) B3405815
theorem B3405821 : Blo 2269435 3405821 := bbase (se 3 (by rfl) ⟨638591, by rfl⟩ : syracuseStep 3405821 = 1277183) (by norm_num)
theorem B2270547 : Blo 2269435 2270547 := bstep (se 1 (by rfl) ⟨1702910, by rfl⟩ : syracuseStep 2270547 = 3405821) B3405821
theorem B5108741 : Blo 2269435 5108741 := bbase (se 4 (by rfl) ⟨478944, by rfl⟩ : syracuseStep 5108741 = 957889) (by norm_num)
theorem B3405827 : Blo 2269435 3405827 := bstep (se 1 (by rfl) ⟨2554370, by rfl⟩ : syracuseStep 3405827 = 5108741) B5108741
theorem B2270551 : Blo 2269435 2270551 := bstep (se 1 (by rfl) ⟨1702913, by rfl⟩ : syracuseStep 2270551 = 3405827) B3405827
theorem B4310509 : Blo 2269435 4310509 := bbase (se 3 (by rfl) ⟨808220, by rfl⟩ : syracuseStep 4310509 = 1616441) (by norm_num)
theorem B5747345 : Blo 2269435 5747345 := bstep (se 2 (by rfl) ⟨2155254, by rfl⟩ : syracuseStep 5747345 = 4310509) B4310509
theorem B3831563 : Blo 2269435 3831563 := bstep (se 1 (by rfl) ⟨2873672, by rfl⟩ : syracuseStep 3831563 = 5747345) B5747345
theorem B2554375 : Blo 2269435 2554375 := bstep (se 1 (by rfl) ⟨1915781, by rfl⟩ : syracuseStep 2554375 = 3831563) B3831563
theorem B3405833 : Blo 2269435 3405833 := bstep (se 2 (by rfl) ⟨1277187, by rfl⟩ : syracuseStep 3405833 = 2554375) B2554375
theorem B2270555 : Blo 2269435 2270555 := bstep (se 1 (by rfl) ⟨1702916, by rfl⟩ : syracuseStep 2270555 = 3405833) B3405833
theorem B11494709 : Blo 2269435 11494709 := bbase (se 5 (by rfl) ⟨538814, by rfl⟩ : syracuseStep 11494709 = 1077629) (by norm_num)
theorem B7663139 : Blo 2269435 7663139 := bstep (se 1 (by rfl) ⟨5747354, by rfl⟩ : syracuseStep 7663139 = 11494709) B11494709
theorem B5108759 : Blo 2269435 5108759 := bstep (se 1 (by rfl) ⟨3831569, by rfl⟩ : syracuseStep 5108759 = 7663139) B7663139
theorem B3405839 : Blo 2269435 3405839 := bstep (se 1 (by rfl) ⟨2554379, by rfl⟩ : syracuseStep 3405839 = 5108759) B5108759
theorem B2270559 : Blo 2269435 2270559 := bstep (se 1 (by rfl) ⟨1702919, by rfl⟩ : syracuseStep 2270559 = 3405839) B3405839
theorem B3405845 : Blo 2269435 3405845 := bbase (se 6 (by rfl) ⟨79824, by rfl⟩ : syracuseStep 3405845 = 159649) (by norm_num)
theorem B2270563 : Blo 2269435 2270563 := bstep (se 1 (by rfl) ⟨1702922, by rfl⟩ : syracuseStep 2270563 = 3405845) B3405845
theorem B5455517 : Blo 2269435 5455517 := bbase (se 3 (by rfl) ⟨1022909, by rfl⟩ : syracuseStep 5455517 = 2045819) (by norm_num)
theorem B14548045 : Blo 2269435 14548045 := bstep (se 3 (by rfl) ⟨2727758, by rfl⟩ : syracuseStep 14548045 = 5455517) B5455517
theorem B19397393 : Blo 2269435 19397393 := bstep (se 2 (by rfl) ⟨7274022, by rfl⟩ : syracuseStep 19397393 = 14548045) B14548045
theorem B12931595 : Blo 2269435 12931595 := bstep (se 1 (by rfl) ⟨9698696, by rfl⟩ : syracuseStep 12931595 = 19397393) B19397393
theorem B8621063 : Blo 2269435 8621063 := bstep (se 1 (by rfl) ⟨6465797, by rfl⟩ : syracuseStep 8621063 = 12931595) B12931595
theorem B5747375 : Blo 2269435 5747375 := bstep (se 1 (by rfl) ⟨4310531, by rfl⟩ : syracuseStep 5747375 = 8621063) B8621063
theorem B3831583 : Blo 2269435 3831583 := bstep (se 1 (by rfl) ⟨2873687, by rfl⟩ : syracuseStep 3831583 = 5747375) B5747375
theorem B5108777 : Blo 2269435 5108777 := bstep (se 2 (by rfl) ⟨1915791, by rfl⟩ : syracuseStep 5108777 = 3831583) B3831583
theorem B3405851 : Blo 2269435 3405851 := bstep (se 1 (by rfl) ⟨2554388, by rfl⟩ : syracuseStep 3405851 = 5108777) B5108777
theorem B2270567 : Blo 2269435 2270567 := bstep (se 1 (by rfl) ⟨1702925, by rfl⟩ : syracuseStep 2270567 = 3405851) B3405851
theorem B2554393 : Blo 2269435 2554393 := bbase (se 2 (by rfl) ⟨957897, by rfl⟩ : syracuseStep 2554393 = 1915795) (by norm_num)
theorem B3405857 : Blo 2269435 3405857 := bstep (se 2 (by rfl) ⟨1277196, by rfl⟩ : syracuseStep 3405857 = 2554393) B2554393
theorem B2270571 : Blo 2269435 2270571 := bstep (se 1 (by rfl) ⟨1702928, by rfl⟩ : syracuseStep 2270571 = 3405857) B3405857
theorem B8621093 : Blo 2269435 8621093 := bbase (se 4 (by rfl) ⟨808227, by rfl⟩ : syracuseStep 8621093 = 1616455) (by norm_num)
theorem B5747395 : Blo 2269435 5747395 := bstep (se 1 (by rfl) ⟨4310546, by rfl⟩ : syracuseStep 5747395 = 8621093) B8621093
theorem B7663193 : Blo 2269435 7663193 := bstep (se 2 (by rfl) ⟨2873697, by rfl⟩ : syracuseStep 7663193 = 5747395) B5747395
theorem B5108795 : Blo 2269435 5108795 := bstep (se 1 (by rfl) ⟨3831596, by rfl⟩ : syracuseStep 5108795 = 7663193) B7663193
theorem B3405863 : Blo 2269435 3405863 := bstep (se 1 (by rfl) ⟨2554397, by rfl⟩ : syracuseStep 3405863 = 5108795) B5108795
theorem B2270575 : Blo 2269435 2270575 := bstep (se 1 (by rfl) ⟨1702931, by rfl⟩ : syracuseStep 2270575 = 3405863) B3405863
theorem B3405869 : Blo 2269435 3405869 := bbase (se 3 (by rfl) ⟨638600, by rfl⟩ : syracuseStep 3405869 = 1277201) (by norm_num)
theorem B2270579 : Blo 2269435 2270579 := bstep (se 1 (by rfl) ⟨1702934, by rfl⟩ : syracuseStep 2270579 = 3405869) B3405869
theorem B5108813 : Blo 2269435 5108813 := bbase (se 3 (by rfl) ⟨957902, by rfl⟩ : syracuseStep 5108813 = 1915805) (by norm_num)
theorem B3405875 : Blo 2269435 3405875 := bstep (se 1 (by rfl) ⟨2554406, by rfl⟩ : syracuseStep 3405875 = 5108813) B5108813
theorem B2270583 : Blo 2269435 2270583 := bstep (se 1 (by rfl) ⟨1702937, by rfl⟩ : syracuseStep 2270583 = 3405875) B3405875
theorem B2873713 : Blo 2269435 2873713 := bbase (se 2 (by rfl) ⟨1077642, by rfl⟩ : syracuseStep 2873713 = 2155285) (by norm_num)
theorem B3831617 : Blo 2269435 3831617 := bstep (se 2 (by rfl) ⟨1436856, by rfl⟩ : syracuseStep 3831617 = 2873713) B2873713
theorem B2554411 : Blo 2269435 2554411 := bstep (se 1 (by rfl) ⟨1915808, by rfl⟩ : syracuseStep 2554411 = 3831617) B3831617
theorem B3405881 : Blo 2269435 3405881 := bstep (se 2 (by rfl) ⟨1277205, by rfl⟩ : syracuseStep 3405881 = 2554411) B2554411
theorem B2270587 : Blo 2269435 2270587 := bstep (se 1 (by rfl) ⟨1702940, by rfl⟩ : syracuseStep 2270587 = 3405881) B3405881
theorem B3452357 : Blo 2269435 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B2301571 : Blo 2269435 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B3068761 : Blo 2269435 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B4091681 : Blo 2269435 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B10911149 : Blo 2269435 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B7274099 : Blo 2269435 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B4849399 : Blo 2269435 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B25863461 : Blo 2269435 25863461 := bstep (se 4 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 25863461 = 4849399) B4849399
theorem B17242307 : Blo 2269435 17242307 := bstep (se 1 (by rfl) ⟨12931730, by rfl⟩ : syracuseStep 17242307 = 25863461) B25863461
theorem B11494871 : Blo 2269435 11494871 := bstep (se 1 (by rfl) ⟨8621153, by rfl⟩ : syracuseStep 11494871 = 17242307) B17242307
theorem B7663247 : Blo 2269435 7663247 := bstep (se 1 (by rfl) ⟨5747435, by rfl⟩ : syracuseStep 7663247 = 11494871) B11494871
theorem B5108831 : Blo 2269435 5108831 := bstep (se 1 (by rfl) ⟨3831623, by rfl⟩ : syracuseStep 5108831 = 7663247) B7663247
theorem B3405887 : Blo 2269435 3405887 := bstep (se 1 (by rfl) ⟨2554415, by rfl⟩ : syracuseStep 3405887 = 5108831) B5108831
theorem B2270591 : Blo 2269435 2270591 := bstep (se 1 (by rfl) ⟨1702943, by rfl⟩ : syracuseStep 2270591 = 3405887) B3405887
theorem B3405893 : Blo 2269435 3405893 := bbase (se 4 (by rfl) ⟨319302, by rfl⟩ : syracuseStep 3405893 = 638605) (by norm_num)
theorem B2270595 : Blo 2269435 2270595 := bstep (se 1 (by rfl) ⟨1702946, by rfl⟩ : syracuseStep 2270595 = 3405893) B3405893
theorem B3831637 : Blo 2269435 3831637 := bbase (se 9 (by rfl) ⟨11225, by rfl⟩ : syracuseStep 3831637 = 22451) (by norm_num)
theorem B5108849 : Blo 2269435 5108849 := bstep (se 2 (by rfl) ⟨1915818, by rfl⟩ : syracuseStep 5108849 = 3831637) B3831637
theorem B3405899 : Blo 2269435 3405899 := bstep (se 1 (by rfl) ⟨2554424, by rfl⟩ : syracuseStep 3405899 = 5108849) B5108849
theorem B2270599 : Blo 2269435 2270599 := bstep (se 1 (by rfl) ⟨1702949, by rfl⟩ : syracuseStep 2270599 = 3405899) B3405899
theorem B2554429 : Blo 2269435 2554429 := bbase (se 3 (by rfl) ⟨478955, by rfl⟩ : syracuseStep 2554429 = 957911) (by norm_num)
theorem B3405905 : Blo 2269435 3405905 := bstep (se 2 (by rfl) ⟨1277214, by rfl⟩ : syracuseStep 3405905 = 2554429) B2554429
theorem B2270603 : Blo 2269435 2270603 := bstep (se 1 (by rfl) ⟨1702952, by rfl⟩ : syracuseStep 2270603 = 3405905) B3405905
theorem B7663301 : Blo 2269435 7663301 := bbase (se 4 (by rfl) ⟨718434, by rfl⟩ : syracuseStep 7663301 = 1436869) (by norm_num)
theorem B5108867 : Blo 2269435 5108867 := bstep (se 1 (by rfl) ⟨3831650, by rfl⟩ : syracuseStep 5108867 = 7663301) B7663301
theorem B3405911 : Blo 2269435 3405911 := bstep (se 1 (by rfl) ⟨2554433, by rfl⟩ : syracuseStep 3405911 = 5108867) B5108867
theorem B2270607 : Blo 2269435 2270607 := bstep (se 1 (by rfl) ⟨1702955, by rfl⟩ : syracuseStep 2270607 = 3405911) B3405911
theorem B3405917 : Blo 2269435 3405917 := bbase (se 3 (by rfl) ⟨638609, by rfl⟩ : syracuseStep 3405917 = 1277219) (by norm_num)
theorem B2270611 : Blo 2269435 2270611 := bstep (se 1 (by rfl) ⟨1702958, by rfl⟩ : syracuseStep 2270611 = 3405917) B3405917
theorem B5108885 : Blo 2269435 5108885 := bbase (se 6 (by rfl) ⟨119739, by rfl⟩ : syracuseStep 5108885 = 239479) (by norm_num)
theorem B3405923 : Blo 2269435 3405923 := bstep (se 1 (by rfl) ⟨2554442, by rfl⟩ : syracuseStep 3405923 = 5108885) B5108885
theorem B2270615 : Blo 2269435 2270615 := bstep (se 1 (by rfl) ⟨1702961, by rfl⟩ : syracuseStep 2270615 = 3405923) B3405923
theorem B3232973 : Blo 2269435 3232973 := bbase (se 3 (by rfl) ⟨606182, by rfl⟩ : syracuseStep 3232973 = 1212365) (by norm_num)
theorem B8621261 : Blo 2269435 8621261 := bstep (se 3 (by rfl) ⟨1616486, by rfl⟩ : syracuseStep 8621261 = 3232973) B3232973
theorem B5747507 : Blo 2269435 5747507 := bstep (se 1 (by rfl) ⟨4310630, by rfl⟩ : syracuseStep 5747507 = 8621261) B8621261
theorem B3831671 : Blo 2269435 3831671 := bstep (se 1 (by rfl) ⟨2873753, by rfl⟩ : syracuseStep 3831671 = 5747507) B5747507
theorem B2554447 : Blo 2269435 2554447 := bstep (se 1 (by rfl) ⟨1915835, by rfl⟩ : syracuseStep 2554447 = 3831671) B3831671
theorem B3405929 : Blo 2269435 3405929 := bstep (se 2 (by rfl) ⟨1277223, by rfl⟩ : syracuseStep 3405929 = 2554447) B2554447
theorem B2270619 : Blo 2269435 2270619 := bstep (se 1 (by rfl) ⟨1702964, by rfl⟩ : syracuseStep 2270619 = 3405929) B3405929
theorem B8183477 : Blo 2269435 8183477 := bbase (se 5 (by rfl) ⟨383600, by rfl⟩ : syracuseStep 8183477 = 767201) (by norm_num)
theorem B21822605 : Blo 2269435 21822605 := bstep (se 3 (by rfl) ⟨4091738, by rfl⟩ : syracuseStep 21822605 = 8183477) B8183477
theorem B14548403 : Blo 2269435 14548403 := bstep (se 1 (by rfl) ⟨10911302, by rfl⟩ : syracuseStep 14548403 = 21822605) B21822605
theorem B9698935 : Blo 2269435 9698935 := bstep (se 1 (by rfl) ⟨7274201, by rfl⟩ : syracuseStep 9698935 = 14548403) B14548403
theorem B12931913 : Blo 2269435 12931913 := bstep (se 2 (by rfl) ⟨4849467, by rfl⟩ : syracuseStep 12931913 = 9698935) B9698935
theorem B8621275 : Blo 2269435 8621275 := bstep (se 1 (by rfl) ⟨6465956, by rfl⟩ : syracuseStep 8621275 = 12931913) B12931913
theorem B11495033 : Blo 2269435 11495033 := bstep (se 2 (by rfl) ⟨4310637, by rfl⟩ : syracuseStep 11495033 = 8621275) B8621275
theorem B7663355 : Blo 2269435 7663355 := bstep (se 1 (by rfl) ⟨5747516, by rfl⟩ : syracuseStep 7663355 = 11495033) B11495033
theorem B5108903 : Blo 2269435 5108903 := bstep (se 1 (by rfl) ⟨3831677, by rfl⟩ : syracuseStep 5108903 = 7663355) B7663355
theorem B3405935 : Blo 2269435 3405935 := bstep (se 1 (by rfl) ⟨2554451, by rfl⟩ : syracuseStep 3405935 = 5108903) B5108903
theorem B2270623 : Blo 2269435 2270623 := bstep (se 1 (by rfl) ⟨1702967, by rfl⟩ : syracuseStep 2270623 = 3405935) B3405935
theorem B3405941 : Blo 2269435 3405941 := bbase (se 5 (by rfl) ⟨159653, by rfl⟩ : syracuseStep 3405941 = 319307) (by norm_num)
theorem B2270627 : Blo 2269435 2270627 := bstep (se 1 (by rfl) ⟨1702970, by rfl⟩ : syracuseStep 2270627 = 3405941) B3405941
theorem B4310653 : Blo 2269435 4310653 := bbase (se 3 (by rfl) ⟨808247, by rfl⟩ : syracuseStep 4310653 = 1616495) (by norm_num)
theorem B5747537 : Blo 2269435 5747537 := bstep (se 2 (by rfl) ⟨2155326, by rfl⟩ : syracuseStep 5747537 = 4310653) B4310653
theorem B3831691 : Blo 2269435 3831691 := bstep (se 1 (by rfl) ⟨2873768, by rfl⟩ : syracuseStep 3831691 = 5747537) B5747537
theorem B5108921 : Blo 2269435 5108921 := bstep (se 2 (by rfl) ⟨1915845, by rfl⟩ : syracuseStep 5108921 = 3831691) B3831691
theorem B3405947 : Blo 2269435 3405947 := bstep (se 1 (by rfl) ⟨2554460, by rfl⟩ : syracuseStep 3405947 = 5108921) B5108921
theorem B2270631 : Blo 2269435 2270631 := bstep (se 1 (by rfl) ⟨1702973, by rfl⟩ : syracuseStep 2270631 = 3405947) B3405947
theorem B2554465 : Blo 2269435 2554465 := bbase (se 2 (by rfl) ⟨957924, by rfl⟩ : syracuseStep 2554465 = 1915849) (by norm_num)
theorem B3405953 : Blo 2269435 3405953 := bstep (se 2 (by rfl) ⟨1277232, by rfl⟩ : syracuseStep 3405953 = 2554465) B2554465
theorem B2270635 : Blo 2269435 2270635 := bstep (se 1 (by rfl) ⟨1702976, by rfl⟩ : syracuseStep 2270635 = 3405953) B3405953
theorem B5747557 : Blo 2269435 5747557 := bbase (se 4 (by rfl) ⟨538833, by rfl⟩ : syracuseStep 5747557 = 1077667) (by norm_num)
theorem B7663409 : Blo 2269435 7663409 := bstep (se 2 (by rfl) ⟨2873778, by rfl⟩ : syracuseStep 7663409 = 5747557) B5747557
theorem B5108939 : Blo 2269435 5108939 := bstep (se 1 (by rfl) ⟨3831704, by rfl⟩ : syracuseStep 5108939 = 7663409) B7663409
theorem B3405959 : Blo 2269435 3405959 := bstep (se 1 (by rfl) ⟨2554469, by rfl⟩ : syracuseStep 3405959 = 5108939) B5108939
theorem B2270639 : Blo 2269435 2270639 := bstep (se 1 (by rfl) ⟨1702979, by rfl⟩ : syracuseStep 2270639 = 3405959) B3405959
theorem B3405965 : Blo 2269435 3405965 := bbase (se 3 (by rfl) ⟨638618, by rfl⟩ : syracuseStep 3405965 = 1277237) (by norm_num)
theorem B2270643 : Blo 2269435 2270643 := bstep (se 1 (by rfl) ⟨1702982, by rfl⟩ : syracuseStep 2270643 = 3405965) B3405965
theorem B5108957 : Blo 2269435 5108957 := bbase (se 3 (by rfl) ⟨957929, by rfl⟩ : syracuseStep 5108957 = 1915859) (by norm_num)
theorem B3405971 : Blo 2269435 3405971 := bstep (se 1 (by rfl) ⟨2554478, by rfl⟩ : syracuseStep 3405971 = 5108957) B5108957
theorem B2270647 : Blo 2269435 2270647 := bstep (se 1 (by rfl) ⟨1702985, by rfl⟩ : syracuseStep 2270647 = 3405971) B3405971
theorem B3831725 : Blo 2269435 3831725 := bbase (se 3 (by rfl) ⟨718448, by rfl⟩ : syracuseStep 3831725 = 1436897) (by norm_num)
theorem B2554483 : Blo 2269435 2554483 := bstep (se 1 (by rfl) ⟨1915862, by rfl⟩ : syracuseStep 2554483 = 3831725) B3831725
theorem B3405977 : Blo 2269435 3405977 := bstep (se 2 (by rfl) ⟨1277241, by rfl⟩ : syracuseStep 3405977 = 2554483) B2554483
theorem B2270651 : Blo 2269435 2270651 := bstep (se 1 (by rfl) ⟨1702988, by rfl⟩ : syracuseStep 2270651 = 3405977) B3405977
theorem B2559829 : Blo 2269435 2559829 := bbase (se 9 (by rfl) ⟨7499, by rfl⟩ : syracuseStep 2559829 = 14999) (by norm_num)
theorem B3413105 : Blo 2269435 3413105 := bstep (se 2 (by rfl) ⟨1279914, by rfl⟩ : syracuseStep 3413105 = 2559829) B2559829
theorem B2275403 : Blo 2269435 2275403 := bstep (se 1 (by rfl) ⟨1706552, by rfl⟩ : syracuseStep 2275403 = 3413105) B3413105
theorem B24270965 : Blo 2269435 24270965 := bstep (se 5 (by rfl) ⟨1137701, by rfl⟩ : syracuseStep 24270965 = 2275403) B2275403
theorem B16180643 : Blo 2269435 16180643 := bstep (se 1 (by rfl) ⟨12135482, by rfl⟩ : syracuseStep 16180643 = 24270965) B24270965
theorem B10787095 : Blo 2269435 10787095 := bstep (se 1 (by rfl) ⟨8090321, by rfl⟩ : syracuseStep 10787095 = 16180643) B16180643
theorem B14382793 : Blo 2269435 14382793 := bstep (se 2 (by rfl) ⟨5393547, by rfl⟩ : syracuseStep 14382793 = 10787095) B10787095
theorem B19177057 : Blo 2269435 19177057 := bstep (se 2 (by rfl) ⟨7191396, by rfl⟩ : syracuseStep 19177057 = 14382793) B14382793
theorem B102277637 : Blo 2269435 102277637 := bstep (se 4 (by rfl) ⟨9588528, by rfl⟩ : syracuseStep 102277637 = 19177057) B19177057
theorem B68185091 : Blo 2269435 68185091 := bstep (se 1 (by rfl) ⟨51138818, by rfl⟩ : syracuseStep 68185091 = 102277637) B102277637
theorem B45456727 : Blo 2269435 45456727 := bstep (se 1 (by rfl) ⟨34092545, by rfl⟩ : syracuseStep 45456727 = 68185091) B68185091
theorem B60608969 : Blo 2269435 60608969 := bstep (se 2 (by rfl) ⟨22728363, by rfl⟩ : syracuseStep 60608969 = 45456727) B45456727
theorem B40405979 : Blo 2269435 40405979 := bstep (se 1 (by rfl) ⟨30304484, by rfl⟩ : syracuseStep 40405979 = 60608969) B60608969
theorem B107749277 : Blo 2269435 107749277 := bstep (se 3 (by rfl) ⟨20202989, by rfl⟩ : syracuseStep 107749277 = 40405979) B40405979
theorem B71832851 : Blo 2269435 71832851 := bstep (se 1 (by rfl) ⟨53874638, by rfl⟩ : syracuseStep 71832851 = 107749277) B107749277
theorem B47888567 : Blo 2269435 47888567 := bstep (se 1 (by rfl) ⟨35916425, by rfl⟩ : syracuseStep 47888567 = 71832851) B71832851
theorem B31925711 : Blo 2269435 31925711 := bstep (se 1 (by rfl) ⟨23944283, by rfl⟩ : syracuseStep 31925711 = 47888567) B47888567
theorem B85135229 : Blo 2269435 85135229 := bstep (se 3 (by rfl) ⟨15962855, by rfl⟩ : syracuseStep 85135229 = 31925711) B31925711
theorem B56756819 : Blo 2269435 56756819 := bstep (se 1 (by rfl) ⟨42567614, by rfl⟩ : syracuseStep 56756819 = 85135229) B85135229
theorem B151351517 : Blo 2269435 151351517 := bstep (se 3 (by rfl) ⟨28378409, by rfl⟩ : syracuseStep 151351517 = 56756819) B56756819
theorem B100901011 : Blo 2269435 100901011 := bstep (se 1 (by rfl) ⟨75675758, by rfl⟩ : syracuseStep 100901011 = 151351517) B151351517
theorem B134534681 : Blo 2269435 134534681 := bstep (se 2 (by rfl) ⟨50450505, by rfl⟩ : syracuseStep 134534681 = 100901011) B100901011
theorem B89689787 : Blo 2269435 89689787 := bstep (se 1 (by rfl) ⟨67267340, by rfl⟩ : syracuseStep 89689787 = 134534681) B134534681
theorem B59793191 : Blo 2269435 59793191 := bstep (se 1 (by rfl) ⟨44844893, by rfl⟩ : syracuseStep 59793191 = 89689787) B89689787
theorem B39862127 : Blo 2269435 39862127 := bstep (se 1 (by rfl) ⟨29896595, by rfl⟩ : syracuseStep 39862127 = 59793191) B59793191
theorem B26574751 : Blo 2269435 26574751 := bstep (se 1 (by rfl) ⟨19931063, by rfl⟩ : syracuseStep 26574751 = 39862127) B39862127
theorem B35433001 : Blo 2269435 35433001 := bstep (se 2 (by rfl) ⟨13287375, by rfl⟩ : syracuseStep 35433001 = 26574751) B26574751
theorem B188976005 : Blo 2269435 188976005 := bstep (se 4 (by rfl) ⟨17716500, by rfl⟩ : syracuseStep 188976005 = 35433001) B35433001
theorem B125984003 : Blo 2269435 125984003 := bstep (se 1 (by rfl) ⟨94488002, by rfl⟩ : syracuseStep 125984003 = 188976005) B188976005
theorem B1343829365 : Blo 2269435 1343829365 := bstep (se 5 (by rfl) ⟨62992001, by rfl⟩ : syracuseStep 1343829365 = 125984003) B125984003
theorem B895886243 : Blo 2269435 895886243 := bstep (se 1 (by rfl) ⟨671914682, by rfl⟩ : syracuseStep 895886243 = 1343829365) B1343829365
theorem B597257495 : Blo 2269435 597257495 := bstep (se 1 (by rfl) ⟨447943121, by rfl⟩ : syracuseStep 597257495 = 895886243) B895886243
theorem B398171663 : Blo 2269435 398171663 := bstep (se 1 (by rfl) ⟨298628747, by rfl⟩ : syracuseStep 398171663 = 597257495) B597257495
theorem B265447775 : Blo 2269435 265447775 := bstep (se 1 (by rfl) ⟨199085831, by rfl⟩ : syracuseStep 265447775 = 398171663) B398171663
theorem B176965183 : Blo 2269435 176965183 := bstep (se 1 (by rfl) ⟨132723887, by rfl⟩ : syracuseStep 176965183 = 265447775) B265447775
theorem B235953577 : Blo 2269435 235953577 := bstep (se 2 (by rfl) ⟨88482591, by rfl⟩ : syracuseStep 235953577 = 176965183) B176965183
theorem B314604769 : Blo 2269435 314604769 := bstep (se 2 (by rfl) ⟨117976788, by rfl⟩ : syracuseStep 314604769 = 235953577) B235953577
theorem B419473025 : Blo 2269435 419473025 := bstep (se 2 (by rfl) ⟨157302384, by rfl⟩ : syracuseStep 419473025 = 314604769) B314604769
theorem B279648683 : Blo 2269435 279648683 := bstep (se 1 (by rfl) ⟨209736512, by rfl⟩ : syracuseStep 279648683 = 419473025) B419473025
theorem B186432455 : Blo 2269435 186432455 := bstep (se 1 (by rfl) ⟨139824341, by rfl⟩ : syracuseStep 186432455 = 279648683) B279648683
theorem B497153213 : Blo 2269435 497153213 := bstep (se 3 (by rfl) ⟨93216227, by rfl⟩ : syracuseStep 497153213 = 186432455) B186432455
theorem B331435475 : Blo 2269435 331435475 := bstep (se 1 (by rfl) ⟨248576606, by rfl⟩ : syracuseStep 331435475 = 497153213) B497153213
theorem B220956983 : Blo 2269435 220956983 := bstep (se 1 (by rfl) ⟨165717737, by rfl⟩ : syracuseStep 220956983 = 331435475) B331435475
theorem B147304655 : Blo 2269435 147304655 := bstep (se 1 (by rfl) ⟨110478491, by rfl⟩ : syracuseStep 147304655 = 220956983) B220956983
theorem B98203103 : Blo 2269435 98203103 := bstep (se 1 (by rfl) ⟨73652327, by rfl⟩ : syracuseStep 98203103 = 147304655) B147304655
theorem B65468735 : Blo 2269435 65468735 := bstep (se 1 (by rfl) ⟨49101551, by rfl⟩ : syracuseStep 65468735 = 98203103) B98203103
theorem B43645823 : Blo 2269435 43645823 := bstep (se 1 (by rfl) ⟨32734367, by rfl⟩ : syracuseStep 43645823 = 65468735) B65468735
theorem B29097215 : Blo 2269435 29097215 := bstep (se 1 (by rfl) ⟨21822911, by rfl⟩ : syracuseStep 29097215 = 43645823) B43645823
theorem B19398143 : Blo 2269435 19398143 := bstep (se 1 (by rfl) ⟨14548607, by rfl⟩ : syracuseStep 19398143 = 29097215) B29097215
theorem B12932095 : Blo 2269435 12932095 := bstep (se 1 (by rfl) ⟨9699071, by rfl⟩ : syracuseStep 12932095 = 19398143) B19398143
theorem B17242793 : Blo 2269435 17242793 := bstep (se 2 (by rfl) ⟨6466047, by rfl⟩ : syracuseStep 17242793 = 12932095) B12932095
theorem B11495195 : Blo 2269435 11495195 := bstep (se 1 (by rfl) ⟨8621396, by rfl⟩ : syracuseStep 11495195 = 17242793) B17242793
theorem B7663463 : Blo 2269435 7663463 := bstep (se 1 (by rfl) ⟨5747597, by rfl⟩ : syracuseStep 7663463 = 11495195) B11495195
theorem B5108975 : Blo 2269435 5108975 := bstep (se 1 (by rfl) ⟨3831731, by rfl⟩ : syracuseStep 5108975 = 7663463) B7663463
theorem B3405983 : Blo 2269435 3405983 := bstep (se 1 (by rfl) ⟨2554487, by rfl⟩ : syracuseStep 3405983 = 5108975) B5108975
theorem B2270655 : Blo 2269435 2270655 := bstep (se 1 (by rfl) ⟨1702991, by rfl⟩ : syracuseStep 2270655 = 3405983) B3405983
theorem B3405989 : Blo 2269435 3405989 := bbase (se 4 (by rfl) ⟨319311, by rfl⟩ : syracuseStep 3405989 = 638623) (by norm_num)
theorem B2270659 : Blo 2269435 2270659 := bstep (se 1 (by rfl) ⟨1702994, by rfl⟩ : syracuseStep 2270659 = 3405989) B3405989
theorem B2873809 : Blo 2269435 2873809 := bbase (se 2 (by rfl) ⟨1077678, by rfl⟩ : syracuseStep 2873809 = 2155357) (by norm_num)
theorem B3831745 : Blo 2269435 3831745 := bstep (se 2 (by rfl) ⟨1436904, by rfl⟩ : syracuseStep 3831745 = 2873809) B2873809
theorem B5108993 : Blo 2269435 5108993 := bstep (se 2 (by rfl) ⟨1915872, by rfl⟩ : syracuseStep 5108993 = 3831745) B3831745
theorem B3405995 : Blo 2269435 3405995 := bstep (se 1 (by rfl) ⟨2554496, by rfl⟩ : syracuseStep 3405995 = 5108993) B5108993
theorem B2270663 : Blo 2269435 2270663 := bstep (se 1 (by rfl) ⟨1702997, by rfl⟩ : syracuseStep 2270663 = 3405995) B3405995
theorem B2554501 : Blo 2269435 2554501 := bbase (se 4 (by rfl) ⟨239484, by rfl⟩ : syracuseStep 2554501 = 478969) (by norm_num)
theorem B3406001 : Blo 2269435 3406001 := bstep (se 2 (by rfl) ⟨1277250, by rfl⟩ : syracuseStep 3406001 = 2554501) B2554501
theorem B2270667 : Blo 2269435 2270667 := bstep (se 1 (by rfl) ⟨1703000, by rfl⟩ : syracuseStep 2270667 = 3406001) B3406001
theorem B7274357 : Blo 2269435 7274357 := bbase (se 5 (by rfl) ⟨340985, by rfl⟩ : syracuseStep 7274357 = 681971) (by norm_num)
theorem B4849571 : Blo 2269435 4849571 := bstep (se 1 (by rfl) ⟨3637178, by rfl⟩ : syracuseStep 4849571 = 7274357) B7274357
theorem B3233047 : Blo 2269435 3233047 := bstep (se 1 (by rfl) ⟨2424785, by rfl⟩ : syracuseStep 3233047 = 4849571) B4849571
theorem B4310729 : Blo 2269435 4310729 := bstep (se 2 (by rfl) ⟨1616523, by rfl⟩ : syracuseStep 4310729 = 3233047) B3233047
theorem B2873819 : Blo 2269435 2873819 := bstep (se 1 (by rfl) ⟨2155364, by rfl⟩ : syracuseStep 2873819 = 4310729) B4310729
theorem B7663517 : Blo 2269435 7663517 := bstep (se 3 (by rfl) ⟨1436909, by rfl⟩ : syracuseStep 7663517 = 2873819) B2873819
theorem B5109011 : Blo 2269435 5109011 := bstep (se 1 (by rfl) ⟨3831758, by rfl⟩ : syracuseStep 5109011 = 7663517) B7663517
theorem B3406007 : Blo 2269435 3406007 := bstep (se 1 (by rfl) ⟨2554505, by rfl⟩ : syracuseStep 3406007 = 5109011) B5109011
theorem B2270671 : Blo 2269435 2270671 := bstep (se 1 (by rfl) ⟨1703003, by rfl⟩ : syracuseStep 2270671 = 3406007) B3406007
theorem B3406013 : Blo 2269435 3406013 := bbase (se 3 (by rfl) ⟨638627, by rfl⟩ : syracuseStep 3406013 = 1277255) (by norm_num)
theorem B2270675 : Blo 2269435 2270675 := bstep (se 1 (by rfl) ⟨1703006, by rfl⟩ : syracuseStep 2270675 = 3406013) B3406013
theorem B5109029 : Blo 2269435 5109029 := bbase (se 4 (by rfl) ⟨478971, by rfl⟩ : syracuseStep 5109029 = 957943) (by norm_num)
theorem B3406019 : Blo 2269435 3406019 := bstep (se 1 (by rfl) ⟨2554514, by rfl⟩ : syracuseStep 3406019 = 5109029) B5109029
theorem B2270679 : Blo 2269435 2270679 := bstep (se 1 (by rfl) ⟨1703009, by rfl⟩ : syracuseStep 2270679 = 3406019) B3406019
theorem B5747669 : Blo 2269435 5747669 := bbase (se 7 (by rfl) ⟨67355, by rfl⟩ : syracuseStep 5747669 = 134711) (by norm_num)
theorem B3831779 : Blo 2269435 3831779 := bstep (se 1 (by rfl) ⟨2873834, by rfl⟩ : syracuseStep 3831779 = 5747669) B5747669
theorem B2554519 : Blo 2269435 2554519 := bstep (se 1 (by rfl) ⟨1915889, by rfl⟩ : syracuseStep 2554519 = 3831779) B3831779
theorem B3406025 : Blo 2269435 3406025 := bstep (se 2 (by rfl) ⟨1277259, by rfl⟩ : syracuseStep 3406025 = 2554519) B2554519
theorem B2270683 : Blo 2269435 2270683 := bstep (se 1 (by rfl) ⟨1703012, by rfl⟩ : syracuseStep 2270683 = 3406025) B3406025
theorem B2913049 : Blo 2269435 2913049 := bbase (se 2 (by rfl) ⟨1092393, by rfl⟩ : syracuseStep 2913049 = 2184787) (by norm_num)
theorem B15536261 : Blo 2269435 15536261 := bstep (se 4 (by rfl) ⟨1456524, by rfl⟩ : syracuseStep 15536261 = 2913049) B2913049
theorem B10357507 : Blo 2269435 10357507 := bstep (se 1 (by rfl) ⟨7768130, by rfl⟩ : syracuseStep 10357507 = 15536261) B15536261
theorem B13810009 : Blo 2269435 13810009 := bstep (se 2 (by rfl) ⟨5178753, by rfl⟩ : syracuseStep 13810009 = 10357507) B10357507
theorem B18413345 : Blo 2269435 18413345 := bstep (se 2 (by rfl) ⟨6905004, by rfl⟩ : syracuseStep 18413345 = 13810009) B13810009
theorem B12275563 : Blo 2269435 12275563 := bstep (se 1 (by rfl) ⟨9206672, by rfl⟩ : syracuseStep 12275563 = 18413345) B18413345
theorem B16367417 : Blo 2269435 16367417 := bstep (se 2 (by rfl) ⟨6137781, by rfl⟩ : syracuseStep 16367417 = 12275563) B12275563
theorem B10911611 : Blo 2269435 10911611 := bstep (se 1 (by rfl) ⟨8183708, by rfl⟩ : syracuseStep 10911611 = 16367417) B16367417
theorem B7274407 : Blo 2269435 7274407 := bstep (se 1 (by rfl) ⟨5455805, by rfl⟩ : syracuseStep 7274407 = 10911611) B10911611
theorem B9699209 : Blo 2269435 9699209 := bstep (se 2 (by rfl) ⟨3637203, by rfl⟩ : syracuseStep 9699209 = 7274407) B7274407
theorem B6466139 : Blo 2269435 6466139 := bstep (se 1 (by rfl) ⟨4849604, by rfl⟩ : syracuseStep 6466139 = 9699209) B9699209
theorem B4310759 : Blo 2269435 4310759 := bstep (se 1 (by rfl) ⟨3233069, by rfl⟩ : syracuseStep 4310759 = 6466139) B6466139
theorem B11495357 : Blo 2269435 11495357 := bstep (se 3 (by rfl) ⟨2155379, by rfl⟩ : syracuseStep 11495357 = 4310759) B4310759
theorem B7663571 : Blo 2269435 7663571 := bstep (se 1 (by rfl) ⟨5747678, by rfl⟩ : syracuseStep 7663571 = 11495357) B11495357
theorem B5109047 : Blo 2269435 5109047 := bstep (se 1 (by rfl) ⟨3831785, by rfl⟩ : syracuseStep 5109047 = 7663571) B7663571
theorem B3406031 : Blo 2269435 3406031 := bstep (se 1 (by rfl) ⟨2554523, by rfl⟩ : syracuseStep 3406031 = 5109047) B5109047
theorem B2270687 : Blo 2269435 2270687 := bstep (se 1 (by rfl) ⟨1703015, by rfl⟩ : syracuseStep 2270687 = 3406031) B3406031
theorem B3406037 : Blo 2269435 3406037 := bbase (se 7 (by rfl) ⟨39914, by rfl⟩ : syracuseStep 3406037 = 79829) (by norm_num)
theorem B2270691 : Blo 2269435 2270691 := bstep (se 1 (by rfl) ⟨1703018, by rfl⟩ : syracuseStep 2270691 = 3406037) B3406037
theorem B2727913 : Blo 2269435 2727913 := bbase (se 2 (by rfl) ⟨1022967, by rfl⟩ : syracuseStep 2727913 = 2045935) (by norm_num)
theorem B3637217 : Blo 2269435 3637217 := bstep (se 2 (by rfl) ⟨1363956, by rfl⟩ : syracuseStep 3637217 = 2727913) B2727913
theorem B2424811 : Blo 2269435 2424811 := bstep (se 1 (by rfl) ⟨1818608, by rfl⟩ : syracuseStep 2424811 = 3637217) B3637217
theorem B3233081 : Blo 2269435 3233081 := bstep (se 2 (by rfl) ⟨1212405, by rfl⟩ : syracuseStep 3233081 = 2424811) B2424811
theorem B8621549 : Blo 2269435 8621549 := bstep (se 3 (by rfl) ⟨1616540, by rfl⟩ : syracuseStep 8621549 = 3233081) B3233081
theorem B5747699 : Blo 2269435 5747699 := bstep (se 1 (by rfl) ⟨4310774, by rfl⟩ : syracuseStep 5747699 = 8621549) B8621549
theorem B3831799 : Blo 2269435 3831799 := bstep (se 1 (by rfl) ⟨2873849, by rfl⟩ : syracuseStep 3831799 = 5747699) B5747699
theorem B5109065 : Blo 2269435 5109065 := bstep (se 2 (by rfl) ⟨1915899, by rfl⟩ : syracuseStep 5109065 = 3831799) B3831799
theorem B3406043 : Blo 2269435 3406043 := bstep (se 1 (by rfl) ⟨2554532, by rfl⟩ : syracuseStep 3406043 = 5109065) B5109065
theorem B2270695 : Blo 2269435 2270695 := bstep (se 1 (by rfl) ⟨1703021, by rfl⟩ : syracuseStep 2270695 = 3406043) B3406043
theorem B2554537 : Blo 2269435 2554537 := bbase (se 2 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 2554537 = 1915903) (by norm_num)
theorem B3406049 : Blo 2269435 3406049 := bstep (se 2 (by rfl) ⟨1277268, by rfl⟩ : syracuseStep 3406049 = 2554537) B2554537
theorem B2270699 : Blo 2269435 2270699 := bstep (se 1 (by rfl) ⟨1703024, by rfl⟩ : syracuseStep 2270699 = 3406049) B3406049
theorem B3637229 : Blo 2269435 3637229 := bbase (se 3 (by rfl) ⟨681980, by rfl⟩ : syracuseStep 3637229 = 1363961) (by norm_num)
theorem B9699277 : Blo 2269435 9699277 := bstep (se 3 (by rfl) ⟨1818614, by rfl⟩ : syracuseStep 9699277 = 3637229) B3637229
theorem B12932369 : Blo 2269435 12932369 := bstep (se 2 (by rfl) ⟨4849638, by rfl⟩ : syracuseStep 12932369 = 9699277) B9699277
theorem B8621579 : Blo 2269435 8621579 := bstep (se 1 (by rfl) ⟨6466184, by rfl⟩ : syracuseStep 8621579 = 12932369) B12932369
theorem B5747719 : Blo 2269435 5747719 := bstep (se 1 (by rfl) ⟨4310789, by rfl⟩ : syracuseStep 5747719 = 8621579) B8621579
theorem B7663625 : Blo 2269435 7663625 := bstep (se 2 (by rfl) ⟨2873859, by rfl⟩ : syracuseStep 7663625 = 5747719) B5747719
theorem B5109083 : Blo 2269435 5109083 := bstep (se 1 (by rfl) ⟨3831812, by rfl⟩ : syracuseStep 5109083 = 7663625) B7663625
theorem B3406055 : Blo 2269435 3406055 := bstep (se 1 (by rfl) ⟨2554541, by rfl⟩ : syracuseStep 3406055 = 5109083) B5109083
theorem B2270703 : Blo 2269435 2270703 := bstep (se 1 (by rfl) ⟨1703027, by rfl⟩ : syracuseStep 2270703 = 3406055) B3406055
theorem B3406061 : Blo 2269435 3406061 := bbase (se 3 (by rfl) ⟨638636, by rfl⟩ : syracuseStep 3406061 = 1277273) (by norm_num)
theorem B2270707 : Blo 2269435 2270707 := bstep (se 1 (by rfl) ⟨1703030, by rfl⟩ : syracuseStep 2270707 = 3406061) B3406061
theorem B5109101 : Blo 2269435 5109101 := bbase (se 3 (by rfl) ⟨957956, by rfl⟩ : syracuseStep 5109101 = 1915913) (by norm_num)
theorem B3406067 : Blo 2269435 3406067 := bstep (se 1 (by rfl) ⟨2554550, by rfl⟩ : syracuseStep 3406067 = 5109101) B5109101
theorem B2270711 : Blo 2269435 2270711 := bstep (se 1 (by rfl) ⟨1703033, by rfl⟩ : syracuseStep 2270711 = 3406067) B3406067
theorem B4310813 : Blo 2269435 4310813 := bbase (se 3 (by rfl) ⟨808277, by rfl⟩ : syracuseStep 4310813 = 1616555) (by norm_num)
theorem B2873875 : Blo 2269435 2873875 := bstep (se 1 (by rfl) ⟨2155406, by rfl⟩ : syracuseStep 2873875 = 4310813) B4310813
theorem B3831833 : Blo 2269435 3831833 := bstep (se 2 (by rfl) ⟨1436937, by rfl⟩ : syracuseStep 3831833 = 2873875) B2873875
theorem B2554555 : Blo 2269435 2554555 := bstep (se 1 (by rfl) ⟨1915916, by rfl⟩ : syracuseStep 2554555 = 3831833) B3831833
theorem B3406073 : Blo 2269435 3406073 := bstep (se 2 (by rfl) ⟨1277277, by rfl⟩ : syracuseStep 3406073 = 2554555) B2554555
theorem B2270715 : Blo 2269435 2270715 := bstep (se 1 (by rfl) ⟨1703036, by rfl⟩ : syracuseStep 2270715 = 3406073) B3406073
theorem B2589413 : Blo 2269435 2589413 := bbase (se 4 (by rfl) ⟨242757, by rfl⟩ : syracuseStep 2589413 = 485515) (by norm_num)
theorem B6905101 : Blo 2269435 6905101 := bstep (se 3 (by rfl) ⟨1294706, by rfl⟩ : syracuseStep 6905101 = 2589413) B2589413
theorem B9206801 : Blo 2269435 9206801 := bstep (se 2 (by rfl) ⟨3452550, by rfl⟩ : syracuseStep 9206801 = 6905101) B6905101
theorem B6137867 : Blo 2269435 6137867 := bstep (se 1 (by rfl) ⟨4603400, by rfl⟩ : syracuseStep 6137867 = 9206801) B9206801
theorem B16367645 : Blo 2269435 16367645 := bstep (se 3 (by rfl) ⟨3068933, by rfl⟩ : syracuseStep 16367645 = 6137867) B6137867
theorem B10911763 : Blo 2269435 10911763 := bstep (se 1 (by rfl) ⟨8183822, by rfl⟩ : syracuseStep 10911763 = 16367645) B16367645
theorem B58196069 : Blo 2269435 58196069 := bstep (se 4 (by rfl) ⟨5455881, by rfl⟩ : syracuseStep 58196069 = 10911763) B10911763
theorem B38797379 : Blo 2269435 38797379 := bstep (se 1 (by rfl) ⟨29098034, by rfl⟩ : syracuseStep 38797379 = 58196069) B58196069
theorem B25864919 : Blo 2269435 25864919 := bstep (se 1 (by rfl) ⟨19398689, by rfl⟩ : syracuseStep 25864919 = 38797379) B38797379
theorem B17243279 : Blo 2269435 17243279 := bstep (se 1 (by rfl) ⟨12932459, by rfl⟩ : syracuseStep 17243279 = 25864919) B25864919
theorem B11495519 : Blo 2269435 11495519 := bstep (se 1 (by rfl) ⟨8621639, by rfl⟩ : syracuseStep 11495519 = 17243279) B17243279
theorem B7663679 : Blo 2269435 7663679 := bstep (se 1 (by rfl) ⟨5747759, by rfl⟩ : syracuseStep 7663679 = 11495519) B11495519
theorem B5109119 : Blo 2269435 5109119 := bstep (se 1 (by rfl) ⟨3831839, by rfl⟩ : syracuseStep 5109119 = 7663679) B7663679
theorem B3406079 : Blo 2269435 3406079 := bstep (se 1 (by rfl) ⟨2554559, by rfl⟩ : syracuseStep 3406079 = 5109119) B5109119
theorem B2270719 : Blo 2269435 2270719 := bstep (se 1 (by rfl) ⟨1703039, by rfl⟩ : syracuseStep 2270719 = 3406079) B3406079
theorem B3406085 : Blo 2269435 3406085 := bbase (se 4 (by rfl) ⟨319320, by rfl⟩ : syracuseStep 3406085 = 638641) (by norm_num)
theorem B2270723 : Blo 2269435 2270723 := bstep (se 1 (by rfl) ⟨1703042, by rfl⟩ : syracuseStep 2270723 = 3406085) B3406085
theorem B3831853 : Blo 2269435 3831853 := bbase (se 3 (by rfl) ⟨718472, by rfl⟩ : syracuseStep 3831853 = 1436945) (by norm_num)
theorem B5109137 : Blo 2269435 5109137 := bstep (se 2 (by rfl) ⟨1915926, by rfl⟩ : syracuseStep 5109137 = 3831853) B3831853
theorem B3406091 : Blo 2269435 3406091 := bstep (se 1 (by rfl) ⟨2554568, by rfl⟩ : syracuseStep 3406091 = 5109137) B5109137
theorem B2270727 : Blo 2269435 2270727 := bstep (se 1 (by rfl) ⟨1703045, by rfl⟩ : syracuseStep 2270727 = 3406091) B3406091
theorem B2554573 : Blo 2269435 2554573 := bbase (se 3 (by rfl) ⟨478982, by rfl⟩ : syracuseStep 2554573 = 957965) (by norm_num)
theorem B3406097 : Blo 2269435 3406097 := bstep (se 2 (by rfl) ⟨1277286, by rfl⟩ : syracuseStep 3406097 = 2554573) B2554573
theorem B2270731 : Blo 2269435 2270731 := bstep (se 1 (by rfl) ⟨1703048, by rfl⟩ : syracuseStep 2270731 = 3406097) B3406097
theorem B7663733 : Blo 2269435 7663733 := bbase (se 5 (by rfl) ⟨359237, by rfl⟩ : syracuseStep 7663733 = 718475) (by norm_num)
theorem B5109155 : Blo 2269435 5109155 := bstep (se 1 (by rfl) ⟨3831866, by rfl⟩ : syracuseStep 5109155 = 7663733) B7663733
theorem B3406103 : Blo 2269435 3406103 := bstep (se 1 (by rfl) ⟨2554577, by rfl⟩ : syracuseStep 3406103 = 5109155) B5109155
theorem B2270735 : Blo 2269435 2270735 := bstep (se 1 (by rfl) ⟨1703051, by rfl⟩ : syracuseStep 2270735 = 3406103) B3406103
theorem B3406109 : Blo 2269435 3406109 := bbase (se 3 (by rfl) ⟨638645, by rfl⟩ : syracuseStep 3406109 = 1277291) (by norm_num)
theorem B2270739 : Blo 2269435 2270739 := bstep (se 1 (by rfl) ⟨1703054, by rfl⟩ : syracuseStep 2270739 = 3406109) B3406109
theorem B5109173 : Blo 2269435 5109173 := bbase (se 5 (by rfl) ⟨239492, by rfl⟩ : syracuseStep 5109173 = 478985) (by norm_num)
theorem B3406115 : Blo 2269435 3406115 := bstep (se 1 (by rfl) ⟨2554586, by rfl⟩ : syracuseStep 3406115 = 5109173) B5109173
theorem B2270743 : Blo 2269435 2270743 := bstep (se 1 (by rfl) ⟨1703057, by rfl⟩ : syracuseStep 2270743 = 3406115) B3406115
theorem B4849733 : Blo 2269435 4849733 := bbase (se 4 (by rfl) ⟨454662, by rfl⟩ : syracuseStep 4849733 = 909325) (by norm_num)
theorem B12932621 : Blo 2269435 12932621 := bstep (se 3 (by rfl) ⟨2424866, by rfl⟩ : syracuseStep 12932621 = 4849733) B4849733
theorem B8621747 : Blo 2269435 8621747 := bstep (se 1 (by rfl) ⟨6466310, by rfl⟩ : syracuseStep 8621747 = 12932621) B12932621
theorem B5747831 : Blo 2269435 5747831 := bstep (se 1 (by rfl) ⟨4310873, by rfl⟩ : syracuseStep 5747831 = 8621747) B8621747
theorem B3831887 : Blo 2269435 3831887 := bstep (se 1 (by rfl) ⟨2873915, by rfl⟩ : syracuseStep 3831887 = 5747831) B5747831
theorem B2554591 : Blo 2269435 2554591 := bstep (se 1 (by rfl) ⟨1915943, by rfl⟩ : syracuseStep 2554591 = 3831887) B3831887
theorem B3406121 : Blo 2269435 3406121 := bstep (se 2 (by rfl) ⟨1277295, by rfl⟩ : syracuseStep 3406121 = 2554591) B2554591
theorem B2270747 : Blo 2269435 2270747 := bstep (se 1 (by rfl) ⟨1703060, by rfl⟩ : syracuseStep 2270747 = 3406121) B3406121
theorem B4849741 : Blo 2269435 4849741 := bbase (se 3 (by rfl) ⟨909326, by rfl⟩ : syracuseStep 4849741 = 1818653) (by norm_num)
theorem B6466321 : Blo 2269435 6466321 := bstep (se 2 (by rfl) ⟨2424870, by rfl⟩ : syracuseStep 6466321 = 4849741) B4849741
theorem B8621761 : Blo 2269435 8621761 := bstep (se 2 (by rfl) ⟨3233160, by rfl⟩ : syracuseStep 8621761 = 6466321) B6466321
theorem B11495681 : Blo 2269435 11495681 := bstep (se 2 (by rfl) ⟨4310880, by rfl⟩ : syracuseStep 11495681 = 8621761) B8621761
theorem B7663787 : Blo 2269435 7663787 := bstep (se 1 (by rfl) ⟨5747840, by rfl⟩ : syracuseStep 7663787 = 11495681) B11495681
theorem B5109191 : Blo 2269435 5109191 := bstep (se 1 (by rfl) ⟨3831893, by rfl⟩ : syracuseStep 5109191 = 7663787) B7663787
theorem B3406127 : Blo 2269435 3406127 := bstep (se 1 (by rfl) ⟨2554595, by rfl⟩ : syracuseStep 3406127 = 5109191) B5109191
theorem B2270751 : Blo 2269435 2270751 := bstep (se 1 (by rfl) ⟨1703063, by rfl⟩ : syracuseStep 2270751 = 3406127) B3406127
theorem B3406133 : Blo 2269435 3406133 := bbase (se 5 (by rfl) ⟨159662, by rfl⟩ : syracuseStep 3406133 = 319325) (by norm_num)
theorem B2270755 : Blo 2269435 2270755 := bstep (se 1 (by rfl) ⟨1703066, by rfl⟩ : syracuseStep 2270755 = 3406133) B3406133
theorem B5747861 : Blo 2269435 5747861 := bbase (se 6 (by rfl) ⟨134715, by rfl⟩ : syracuseStep 5747861 = 269431) (by norm_num)
theorem B3831907 : Blo 2269435 3831907 := bstep (se 1 (by rfl) ⟨2873930, by rfl⟩ : syracuseStep 3831907 = 5747861) B5747861
theorem B5109209 : Blo 2269435 5109209 := bstep (se 2 (by rfl) ⟨1915953, by rfl⟩ : syracuseStep 5109209 = 3831907) B3831907
theorem B3406139 : Blo 2269435 3406139 := bstep (se 1 (by rfl) ⟨2554604, by rfl⟩ : syracuseStep 3406139 = 5109209) B5109209
theorem B2270759 : Blo 2269435 2270759 := bstep (se 1 (by rfl) ⟨1703069, by rfl⟩ : syracuseStep 2270759 = 3406139) B3406139
theorem B2554609 : Blo 2269435 2554609 := bbase (se 2 (by rfl) ⟨957978, by rfl⟩ : syracuseStep 2554609 = 1915957) (by norm_num)
theorem B3406145 : Blo 2269435 3406145 := bstep (se 2 (by rfl) ⟨1277304, by rfl⟩ : syracuseStep 3406145 = 2554609) B2554609
theorem B2270763 : Blo 2269435 2270763 := bstep (se 1 (by rfl) ⟨1703072, by rfl⟩ : syracuseStep 2270763 = 3406145) B3406145
theorem B2624797 : Blo 2269435 2624797 := bbase (se 3 (by rfl) ⟨492149, by rfl⟩ : syracuseStep 2624797 = 984299) (by norm_num)
theorem B13998917 : Blo 2269435 13998917 := bstep (se 4 (by rfl) ⟨1312398, by rfl⟩ : syracuseStep 13998917 = 2624797) B2624797
theorem B37330445 : Blo 2269435 37330445 := bstep (se 3 (by rfl) ⟨6999458, by rfl⟩ : syracuseStep 37330445 = 13998917) B13998917
theorem B24886963 : Blo 2269435 24886963 := bstep (se 1 (by rfl) ⟨18665222, by rfl⟩ : syracuseStep 24886963 = 37330445) B37330445
theorem B33182617 : Blo 2269435 33182617 := bstep (se 2 (by rfl) ⟨12443481, by rfl⟩ : syracuseStep 33182617 = 24886963) B24886963
theorem B44243489 : Blo 2269435 44243489 := bstep (se 2 (by rfl) ⟨16591308, by rfl⟩ : syracuseStep 44243489 = 33182617) B33182617
theorem B29495659 : Blo 2269435 29495659 := bstep (se 1 (by rfl) ⟨22121744, by rfl⟩ : syracuseStep 29495659 = 44243489) B44243489
theorem B39327545 : Blo 2269435 39327545 := bstep (se 2 (by rfl) ⟨14747829, by rfl⟩ : syracuseStep 39327545 = 29495659) B29495659
theorem B104873453 : Blo 2269435 104873453 := bstep (se 3 (by rfl) ⟨19663772, by rfl⟩ : syracuseStep 104873453 = 39327545) B39327545
theorem B69915635 : Blo 2269435 69915635 := bstep (se 1 (by rfl) ⟨52436726, by rfl⟩ : syracuseStep 69915635 = 104873453) B104873453
theorem B46610423 : Blo 2269435 46610423 := bstep (se 1 (by rfl) ⟨34957817, by rfl⟩ : syracuseStep 46610423 = 69915635) B69915635
theorem B31073615 : Blo 2269435 31073615 := bstep (se 1 (by rfl) ⟨23305211, by rfl⟩ : syracuseStep 31073615 = 46610423) B46610423
theorem B20715743 : Blo 2269435 20715743 := bstep (se 1 (by rfl) ⟨15536807, by rfl⟩ : syracuseStep 20715743 = 31073615) B31073615
theorem B13810495 : Blo 2269435 13810495 := bstep (se 1 (by rfl) ⟨10357871, by rfl⟩ : syracuseStep 13810495 = 20715743) B20715743
theorem B18413993 : Blo 2269435 18413993 := bstep (se 2 (by rfl) ⟨6905247, by rfl⟩ : syracuseStep 18413993 = 13810495) B13810495
theorem B49103981 : Blo 2269435 49103981 := bstep (se 3 (by rfl) ⟨9206996, by rfl⟩ : syracuseStep 49103981 = 18413993) B18413993
theorem B32735987 : Blo 2269435 32735987 := bstep (se 1 (by rfl) ⟨24551990, by rfl⟩ : syracuseStep 32735987 = 49103981) B49103981
theorem B21823991 : Blo 2269435 21823991 := bstep (se 1 (by rfl) ⟨16367993, by rfl⟩ : syracuseStep 21823991 = 32735987) B32735987
theorem B14549327 : Blo 2269435 14549327 := bstep (se 1 (by rfl) ⟨10911995, by rfl⟩ : syracuseStep 14549327 = 21823991) B21823991
theorem B9699551 : Blo 2269435 9699551 := bstep (se 1 (by rfl) ⟨7274663, by rfl⟩ : syracuseStep 9699551 = 14549327) B14549327
theorem B6466367 : Blo 2269435 6466367 := bstep (se 1 (by rfl) ⟨4849775, by rfl⟩ : syracuseStep 6466367 = 9699551) B9699551
theorem B4310911 : Blo 2269435 4310911 := bstep (se 1 (by rfl) ⟨3233183, by rfl⟩ : syracuseStep 4310911 = 6466367) B6466367
theorem B5747881 : Blo 2269435 5747881 := bstep (se 2 (by rfl) ⟨2155455, by rfl⟩ : syracuseStep 5747881 = 4310911) B4310911
theorem B7663841 : Blo 2269435 7663841 := bstep (se 2 (by rfl) ⟨2873940, by rfl⟩ : syracuseStep 7663841 = 5747881) B5747881
theorem B5109227 : Blo 2269435 5109227 := bstep (se 1 (by rfl) ⟨3831920, by rfl⟩ : syracuseStep 5109227 = 7663841) B7663841
theorem B3406151 : Blo 2269435 3406151 := bstep (se 1 (by rfl) ⟨2554613, by rfl⟩ : syracuseStep 3406151 = 5109227) B5109227
theorem B2270767 : Blo 2269435 2270767 := bstep (se 1 (by rfl) ⟨1703075, by rfl⟩ : syracuseStep 2270767 = 3406151) B3406151
theorem B3406157 : Blo 2269435 3406157 := bbase (se 3 (by rfl) ⟨638654, by rfl⟩ : syracuseStep 3406157 = 1277309) (by norm_num)
theorem B2270771 : Blo 2269435 2270771 := bstep (se 1 (by rfl) ⟨1703078, by rfl⟩ : syracuseStep 2270771 = 3406157) B3406157
theorem B5109245 : Blo 2269435 5109245 := bbase (se 3 (by rfl) ⟨957983, by rfl⟩ : syracuseStep 5109245 = 1915967) (by norm_num)
theorem B3406163 : Blo 2269435 3406163 := bstep (se 1 (by rfl) ⟨2554622, by rfl⟩ : syracuseStep 3406163 = 5109245) B5109245
theorem B2270775 : Blo 2269435 2270775 := bstep (se 1 (by rfl) ⟨1703081, by rfl⟩ : syracuseStep 2270775 = 3406163) B3406163
theorem B3831941 : Blo 2269435 3831941 := bbase (se 4 (by rfl) ⟨359244, by rfl⟩ : syracuseStep 3831941 = 718489) (by norm_num)
theorem B2554627 : Blo 2269435 2554627 := bstep (se 1 (by rfl) ⟨1915970, by rfl⟩ : syracuseStep 2554627 = 3831941) B3831941
theorem B3406169 : Blo 2269435 3406169 := bstep (se 2 (by rfl) ⟨1277313, by rfl⟩ : syracuseStep 3406169 = 2554627) B2554627
theorem B2270779 : Blo 2269435 2270779 := bstep (se 1 (by rfl) ⟨1703084, by rfl⟩ : syracuseStep 2270779 = 3406169) B3406169
theorem B17243765 : Blo 2269435 17243765 := bbase (se 5 (by rfl) ⟨808301, by rfl⟩ : syracuseStep 17243765 = 1616603) (by norm_num)
theorem B11495843 : Blo 2269435 11495843 := bstep (se 1 (by rfl) ⟨8621882, by rfl⟩ : syracuseStep 11495843 = 17243765) B17243765
theorem B7663895 : Blo 2269435 7663895 := bstep (se 1 (by rfl) ⟨5747921, by rfl⟩ : syracuseStep 7663895 = 11495843) B11495843
theorem B5109263 : Blo 2269435 5109263 := bstep (se 1 (by rfl) ⟨3831947, by rfl⟩ : syracuseStep 5109263 = 7663895) B7663895
theorem B3406175 : Blo 2269435 3406175 := bstep (se 1 (by rfl) ⟨2554631, by rfl⟩ : syracuseStep 3406175 = 5109263) B5109263
theorem B2270783 : Blo 2269435 2270783 := bstep (se 1 (by rfl) ⟨1703087, by rfl⟩ : syracuseStep 2270783 = 3406175) B3406175
theorem B3406181 : Blo 2269435 3406181 := bbase (se 4 (by rfl) ⟨319329, by rfl⟩ : syracuseStep 3406181 = 638659) (by norm_num)
theorem B2270787 : Blo 2269435 2270787 := bstep (se 1 (by rfl) ⟨1703090, by rfl⟩ : syracuseStep 2270787 = 3406181) B3406181
theorem B4310957 : Blo 2269435 4310957 := bbase (se 3 (by rfl) ⟨808304, by rfl⟩ : syracuseStep 4310957 = 1616609) (by norm_num)
theorem B2873971 : Blo 2269435 2873971 := bstep (se 1 (by rfl) ⟨2155478, by rfl⟩ : syracuseStep 2873971 = 4310957) B4310957
theorem B3831961 : Blo 2269435 3831961 := bstep (se 2 (by rfl) ⟨1436985, by rfl⟩ : syracuseStep 3831961 = 2873971) B2873971
theorem B5109281 : Blo 2269435 5109281 := bstep (se 2 (by rfl) ⟨1915980, by rfl⟩ : syracuseStep 5109281 = 3831961) B3831961
theorem B3406187 : Blo 2269435 3406187 := bstep (se 1 (by rfl) ⟨2554640, by rfl⟩ : syracuseStep 3406187 = 5109281) B5109281
theorem B2270791 : Blo 2269435 2270791 := bstep (se 1 (by rfl) ⟨1703093, by rfl⟩ : syracuseStep 2270791 = 3406187) B3406187
theorem B2554645 : Blo 2269435 2554645 := bbase (se 6 (by rfl) ⟨59874, by rfl⟩ : syracuseStep 2554645 = 119749) (by norm_num)
theorem B3406193 : Blo 2269435 3406193 := bstep (se 2 (by rfl) ⟨1277322, by rfl⟩ : syracuseStep 3406193 = 2554645) B2554645
theorem B2270795 : Blo 2269435 2270795 := bstep (se 1 (by rfl) ⟨1703096, by rfl⟩ : syracuseStep 2270795 = 3406193) B3406193
theorem B2873981 : Blo 2269435 2873981 := bbase (se 3 (by rfl) ⟨538871, by rfl⟩ : syracuseStep 2873981 = 1077743) (by norm_num)
theorem B7663949 : Blo 2269435 7663949 := bstep (se 3 (by rfl) ⟨1436990, by rfl⟩ : syracuseStep 7663949 = 2873981) B2873981
theorem B5109299 : Blo 2269435 5109299 := bstep (se 1 (by rfl) ⟨3831974, by rfl⟩ : syracuseStep 5109299 = 7663949) B7663949
theorem B3406199 : Blo 2269435 3406199 := bstep (se 1 (by rfl) ⟨2554649, by rfl⟩ : syracuseStep 3406199 = 5109299) B5109299
theorem B2270799 : Blo 2269435 2270799 := bstep (se 1 (by rfl) ⟨1703099, by rfl⟩ : syracuseStep 2270799 = 3406199) B3406199
theorem B3406205 : Blo 2269435 3406205 := bbase (se 3 (by rfl) ⟨638663, by rfl⟩ : syracuseStep 3406205 = 1277327) (by norm_num)
theorem B2270803 : Blo 2269435 2270803 := bstep (se 1 (by rfl) ⟨1703102, by rfl⟩ : syracuseStep 2270803 = 3406205) B3406205
theorem B5109317 : Blo 2269435 5109317 := bbase (se 4 (by rfl) ⟨478998, by rfl⟩ : syracuseStep 5109317 = 957997) (by norm_num)
theorem B3406211 : Blo 2269435 3406211 := bstep (se 1 (by rfl) ⟨2554658, by rfl⟩ : syracuseStep 3406211 = 5109317) B5109317
theorem B2270807 : Blo 2269435 2270807 := bstep (se 1 (by rfl) ⟨1703105, by rfl⟩ : syracuseStep 2270807 = 3406211) B3406211
theorem B2458021 : Blo 2269435 2458021 := bbase (se 4 (by rfl) ⟨230439, by rfl⟩ : syracuseStep 2458021 = 460879) (by norm_num)
theorem B3277361 : Blo 2269435 3277361 := bstep (se 2 (by rfl) ⟨1229010, by rfl⟩ : syracuseStep 3277361 = 2458021) B2458021
theorem B8739629 : Blo 2269435 8739629 := bstep (se 3 (by rfl) ⟨1638680, by rfl⟩ : syracuseStep 8739629 = 3277361) B3277361
theorem B5826419 : Blo 2269435 5826419 := bstep (se 1 (by rfl) ⟨4369814, by rfl⟩ : syracuseStep 5826419 = 8739629) B8739629
theorem B3884279 : Blo 2269435 3884279 := bstep (se 1 (by rfl) ⟨2913209, by rfl⟩ : syracuseStep 3884279 = 5826419) B5826419
theorem B10358077 : Blo 2269435 10358077 := bstep (se 3 (by rfl) ⟨1942139, by rfl⟩ : syracuseStep 10358077 = 3884279) B3884279
theorem B13810769 : Blo 2269435 13810769 := bstep (se 2 (by rfl) ⟨5179038, by rfl⟩ : syracuseStep 13810769 = 10358077) B10358077
theorem B9207179 : Blo 2269435 9207179 := bstep (se 1 (by rfl) ⟨6905384, by rfl⟩ : syracuseStep 9207179 = 13810769) B13810769
theorem B6138119 : Blo 2269435 6138119 := bstep (se 1 (by rfl) ⟨4603589, by rfl⟩ : syracuseStep 6138119 = 9207179) B9207179
theorem B4092079 : Blo 2269435 4092079 := bstep (se 1 (by rfl) ⟨3069059, by rfl⟩ : syracuseStep 4092079 = 6138119) B6138119
theorem B5456105 : Blo 2269435 5456105 := bstep (se 2 (by rfl) ⟨2046039, by rfl⟩ : syracuseStep 5456105 = 4092079) B4092079
theorem B3637403 : Blo 2269435 3637403 := bstep (se 1 (by rfl) ⟨2728052, by rfl⟩ : syracuseStep 3637403 = 5456105) B5456105
theorem B2424935 : Blo 2269435 2424935 := bstep (se 1 (by rfl) ⟨1818701, by rfl⟩ : syracuseStep 2424935 = 3637403) B3637403
theorem B6466493 : Blo 2269435 6466493 := bstep (se 3 (by rfl) ⟨1212467, by rfl⟩ : syracuseStep 6466493 = 2424935) B2424935
theorem B4310995 : Blo 2269435 4310995 := bstep (se 1 (by rfl) ⟨3233246, by rfl⟩ : syracuseStep 4310995 = 6466493) B6466493
theorem B5747993 : Blo 2269435 5747993 := bstep (se 2 (by rfl) ⟨2155497, by rfl⟩ : syracuseStep 5747993 = 4310995) B4310995
theorem B3831995 : Blo 2269435 3831995 := bstep (se 1 (by rfl) ⟨2873996, by rfl⟩ : syracuseStep 3831995 = 5747993) B5747993
theorem B2554663 : Blo 2269435 2554663 := bstep (se 1 (by rfl) ⟨1915997, by rfl⟩ : syracuseStep 2554663 = 3831995) B3831995
theorem B3406217 : Blo 2269435 3406217 := bstep (se 2 (by rfl) ⟨1277331, by rfl⟩ : syracuseStep 3406217 = 2554663) B2554663
theorem B2270811 : Blo 2269435 2270811 := bstep (se 1 (by rfl) ⟨1703108, by rfl⟩ : syracuseStep 2270811 = 3406217) B3406217
theorem B11496005 : Blo 2269435 11496005 := bbase (se 4 (by rfl) ⟨1077750, by rfl⟩ : syracuseStep 11496005 = 2155501) (by norm_num)
theorem B7664003 : Blo 2269435 7664003 := bstep (se 1 (by rfl) ⟨5748002, by rfl⟩ : syracuseStep 7664003 = 11496005) B11496005
theorem B5109335 : Blo 2269435 5109335 := bstep (se 1 (by rfl) ⟨3832001, by rfl⟩ : syracuseStep 5109335 = 7664003) B7664003
theorem B3406223 : Blo 2269435 3406223 := bstep (se 1 (by rfl) ⟨2554667, by rfl⟩ : syracuseStep 3406223 = 5109335) B5109335
theorem B2270815 : Blo 2269435 2270815 := bstep (se 1 (by rfl) ⟨1703111, by rfl⟩ : syracuseStep 2270815 = 3406223) B3406223
theorem B3406229 : Blo 2269435 3406229 := bbase (se 6 (by rfl) ⟨79833, by rfl⟩ : syracuseStep 3406229 = 159667) (by norm_num)
theorem B2270819 : Blo 2269435 2270819 := bstep (se 1 (by rfl) ⟨1703114, by rfl⟩ : syracuseStep 2270819 = 3406229) B3406229
theorem B13810837 : Blo 2269435 13810837 := bbase (se 6 (by rfl) ⟨323691, by rfl⟩ : syracuseStep 13810837 = 647383) (by norm_num)
theorem B18414449 : Blo 2269435 18414449 := bstep (se 2 (by rfl) ⟨6905418, by rfl⟩ : syracuseStep 18414449 = 13810837) B13810837
theorem B12276299 : Blo 2269435 12276299 := bstep (se 1 (by rfl) ⟨9207224, by rfl⟩ : syracuseStep 12276299 = 18414449) B18414449
theorem B8184199 : Blo 2269435 8184199 := bstep (se 1 (by rfl) ⟨6138149, by rfl⟩ : syracuseStep 8184199 = 12276299) B12276299
theorem B10912265 : Blo 2269435 10912265 := bstep (se 2 (by rfl) ⟨4092099, by rfl⟩ : syracuseStep 10912265 = 8184199) B8184199
theorem B7274843 : Blo 2269435 7274843 := bstep (se 1 (by rfl) ⟨5456132, by rfl⟩ : syracuseStep 7274843 = 10912265) B10912265
theorem B4849895 : Blo 2269435 4849895 := bstep (se 1 (by rfl) ⟨3637421, by rfl⟩ : syracuseStep 4849895 = 7274843) B7274843
theorem B12933053 : Blo 2269435 12933053 := bstep (se 3 (by rfl) ⟨2424947, by rfl⟩ : syracuseStep 12933053 = 4849895) B4849895
theorem B8622035 : Blo 2269435 8622035 := bstep (se 1 (by rfl) ⟨6466526, by rfl⟩ : syracuseStep 8622035 = 12933053) B12933053
theorem B5748023 : Blo 2269435 5748023 := bstep (se 1 (by rfl) ⟨4311017, by rfl⟩ : syracuseStep 5748023 = 8622035) B8622035
theorem B3832015 : Blo 2269435 3832015 := bstep (se 1 (by rfl) ⟨2874011, by rfl⟩ : syracuseStep 3832015 = 5748023) B5748023
theorem B5109353 : Blo 2269435 5109353 := bstep (se 2 (by rfl) ⟨1916007, by rfl⟩ : syracuseStep 5109353 = 3832015) B3832015
theorem B3406235 : Blo 2269435 3406235 := bstep (se 1 (by rfl) ⟨2554676, by rfl⟩ : syracuseStep 3406235 = 5109353) B5109353
theorem B2270823 : Blo 2269435 2270823 := bstep (se 1 (by rfl) ⟨1703117, by rfl⟩ : syracuseStep 2270823 = 3406235) B3406235
theorem B2554681 : Blo 2269435 2554681 := bbase (se 2 (by rfl) ⟨958005, by rfl⟩ : syracuseStep 2554681 = 1916011) (by norm_num)
theorem B3406241 : Blo 2269435 3406241 := bstep (se 2 (by rfl) ⟨1277340, by rfl⟩ : syracuseStep 3406241 = 2554681) B2554681
theorem B2270827 : Blo 2269435 2270827 := bstep (se 1 (by rfl) ⟨1703120, by rfl⟩ : syracuseStep 2270827 = 3406241) B3406241
theorem B6466549 : Blo 2269435 6466549 := bbase (se 5 (by rfl) ⟨303119, by rfl⟩ : syracuseStep 6466549 = 606239) (by norm_num)
theorem B8622065 : Blo 2269435 8622065 := bstep (se 2 (by rfl) ⟨3233274, by rfl⟩ : syracuseStep 8622065 = 6466549) B6466549
theorem B5748043 : Blo 2269435 5748043 := bstep (se 1 (by rfl) ⟨4311032, by rfl⟩ : syracuseStep 5748043 = 8622065) B8622065
theorem B7664057 : Blo 2269435 7664057 := bstep (se 2 (by rfl) ⟨2874021, by rfl⟩ : syracuseStep 7664057 = 5748043) B5748043
theorem B5109371 : Blo 2269435 5109371 := bstep (se 1 (by rfl) ⟨3832028, by rfl⟩ : syracuseStep 5109371 = 7664057) B7664057
theorem B3406247 : Blo 2269435 3406247 := bstep (se 1 (by rfl) ⟨2554685, by rfl⟩ : syracuseStep 3406247 = 5109371) B5109371
theorem B2270831 : Blo 2269435 2270831 := bstep (se 1 (by rfl) ⟨1703123, by rfl⟩ : syracuseStep 2270831 = 3406247) B3406247
theorem B3406253 : Blo 2269435 3406253 := bbase (se 3 (by rfl) ⟨638672, by rfl⟩ : syracuseStep 3406253 = 1277345) (by norm_num)
theorem B2270835 : Blo 2269435 2270835 := bstep (se 1 (by rfl) ⟨1703126, by rfl⟩ : syracuseStep 2270835 = 3406253) B3406253
theorem B5109389 : Blo 2269435 5109389 := bbase (se 3 (by rfl) ⟨958010, by rfl⟩ : syracuseStep 5109389 = 1916021) (by norm_num)
theorem B3406259 : Blo 2269435 3406259 := bstep (se 1 (by rfl) ⟨2554694, by rfl⟩ : syracuseStep 3406259 = 5109389) B5109389
theorem B2270839 : Blo 2269435 2270839 := bstep (se 1 (by rfl) ⟨1703129, by rfl⟩ : syracuseStep 2270839 = 3406259) B3406259
theorem B2874037 : Blo 2269435 2874037 := bbase (se 5 (by rfl) ⟨134720, by rfl⟩ : syracuseStep 2874037 = 269441) (by norm_num)
theorem B3832049 : Blo 2269435 3832049 := bstep (se 2 (by rfl) ⟨1437018, by rfl⟩ : syracuseStep 3832049 = 2874037) B2874037
theorem B2554699 : Blo 2269435 2554699 := bstep (se 1 (by rfl) ⟨1916024, by rfl⟩ : syracuseStep 2554699 = 3832049) B3832049
theorem B3406265 : Blo 2269435 3406265 := bstep (se 2 (by rfl) ⟨1277349, by rfl⟩ : syracuseStep 3406265 = 2554699) B2554699
theorem B2270843 : Blo 2269435 2270843 := bstep (se 1 (by rfl) ⟨1703132, by rfl⟩ : syracuseStep 2270843 = 3406265) B3406265
theorem B4147973 : Blo 2269435 4147973 := bbase (se 4 (by rfl) ⟨388872, by rfl⟩ : syracuseStep 4147973 = 777745) (by norm_num)
theorem B2765315 : Blo 2269435 2765315 := bstep (se 1 (by rfl) ⟨2073986, by rfl⟩ : syracuseStep 2765315 = 4147973) B4147973
theorem B7374173 : Blo 2269435 7374173 := bstep (se 3 (by rfl) ⟨1382657, by rfl⟩ : syracuseStep 7374173 = 2765315) B2765315
theorem B19664461 : Blo 2269435 19664461 := bstep (se 3 (by rfl) ⟨3687086, by rfl⟩ : syracuseStep 19664461 = 7374173) B7374173
theorem B104877125 : Blo 2269435 104877125 := bstep (se 4 (by rfl) ⟨9832230, by rfl⟩ : syracuseStep 104877125 = 19664461) B19664461
theorem B69918083 : Blo 2269435 69918083 := bstep (se 1 (by rfl) ⟨52438562, by rfl⟩ : syracuseStep 69918083 = 104877125) B104877125
theorem B46612055 : Blo 2269435 46612055 := bstep (se 1 (by rfl) ⟨34959041, by rfl⟩ : syracuseStep 46612055 = 69918083) B69918083
theorem B124298813 : Blo 2269435 124298813 := bstep (se 3 (by rfl) ⟨23306027, by rfl⟩ : syracuseStep 124298813 = 46612055) B46612055
theorem B82865875 : Blo 2269435 82865875 := bstep (se 1 (by rfl) ⟨62149406, by rfl⟩ : syracuseStep 82865875 = 124298813) B124298813
theorem B110487833 : Blo 2269435 110487833 := bstep (se 2 (by rfl) ⟨41432937, by rfl⟩ : syracuseStep 110487833 = 82865875) B82865875
theorem B73658555 : Blo 2269435 73658555 := bstep (se 1 (by rfl) ⟨55243916, by rfl⟩ : syracuseStep 73658555 = 110487833) B110487833
theorem B49105703 : Blo 2269435 49105703 := bstep (se 1 (by rfl) ⟨36829277, by rfl⟩ : syracuseStep 49105703 = 73658555) B73658555
theorem B32737135 : Blo 2269435 32737135 := bstep (se 1 (by rfl) ⟨24552851, by rfl⟩ : syracuseStep 32737135 = 49105703) B49105703
theorem B43649513 : Blo 2269435 43649513 := bstep (se 2 (by rfl) ⟨16368567, by rfl⟩ : syracuseStep 43649513 = 32737135) B32737135
theorem B29099675 : Blo 2269435 29099675 := bstep (se 1 (by rfl) ⟨21824756, by rfl⟩ : syracuseStep 29099675 = 43649513) B43649513
theorem B19399783 : Blo 2269435 19399783 := bstep (se 1 (by rfl) ⟨14549837, by rfl⟩ : syracuseStep 19399783 = 29099675) B29099675
theorem B25866377 : Blo 2269435 25866377 := bstep (se 2 (by rfl) ⟨9699891, by rfl⟩ : syracuseStep 25866377 = 19399783) B19399783
theorem B17244251 : Blo 2269435 17244251 := bstep (se 1 (by rfl) ⟨12933188, by rfl⟩ : syracuseStep 17244251 = 25866377) B25866377
theorem B11496167 : Blo 2269435 11496167 := bstep (se 1 (by rfl) ⟨8622125, by rfl⟩ : syracuseStep 11496167 = 17244251) B17244251
theorem B7664111 : Blo 2269435 7664111 := bstep (se 1 (by rfl) ⟨5748083, by rfl⟩ : syracuseStep 7664111 = 11496167) B11496167
theorem B5109407 : Blo 2269435 5109407 := bstep (se 1 (by rfl) ⟨3832055, by rfl⟩ : syracuseStep 5109407 = 7664111) B7664111
theorem B3406271 : Blo 2269435 3406271 := bstep (se 1 (by rfl) ⟨2554703, by rfl⟩ : syracuseStep 3406271 = 5109407) B5109407
theorem B2270847 : Blo 2269435 2270847 := bstep (se 1 (by rfl) ⟨1703135, by rfl⟩ : syracuseStep 2270847 = 3406271) B3406271
theorem B3406277 : Blo 2269435 3406277 := bbase (se 4 (by rfl) ⟨319338, by rfl⟩ : syracuseStep 3406277 = 638677) (by norm_num)
theorem B2270851 : Blo 2269435 2270851 := bstep (se 1 (by rfl) ⟨1703138, by rfl⟩ : syracuseStep 2270851 = 3406277) B3406277
theorem B3832069 : Blo 2269435 3832069 := bbase (se 4 (by rfl) ⟨359256, by rfl⟩ : syracuseStep 3832069 = 718513) (by norm_num)
theorem B5109425 : Blo 2269435 5109425 := bstep (se 2 (by rfl) ⟨1916034, by rfl⟩ : syracuseStep 5109425 = 3832069) B3832069
theorem B3406283 : Blo 2269435 3406283 := bstep (se 1 (by rfl) ⟨2554712, by rfl⟩ : syracuseStep 3406283 = 5109425) B5109425
theorem B2270855 : Blo 2269435 2270855 := bstep (se 1 (by rfl) ⟨1703141, by rfl⟩ : syracuseStep 2270855 = 3406283) B3406283
theorem B2554717 : Blo 2269435 2554717 := bbase (se 3 (by rfl) ⟨479009, by rfl⟩ : syracuseStep 2554717 = 958019) (by norm_num)
theorem B3406289 : Blo 2269435 3406289 := bstep (se 2 (by rfl) ⟨1277358, by rfl⟩ : syracuseStep 3406289 = 2554717) B2554717
theorem B2270859 : Blo 2269435 2270859 := bstep (se 1 (by rfl) ⟨1703144, by rfl⟩ : syracuseStep 2270859 = 3406289) B3406289
theorem B7664165 : Blo 2269435 7664165 := bbase (se 4 (by rfl) ⟨718515, by rfl⟩ : syracuseStep 7664165 = 1437031) (by norm_num)
theorem B5109443 : Blo 2269435 5109443 := bstep (se 1 (by rfl) ⟨3832082, by rfl⟩ : syracuseStep 5109443 = 7664165) B7664165
theorem B3406295 : Blo 2269435 3406295 := bstep (se 1 (by rfl) ⟨2554721, by rfl⟩ : syracuseStep 3406295 = 5109443) B5109443
theorem B2270863 : Blo 2269435 2270863 := bstep (se 1 (by rfl) ⟨1703147, by rfl⟩ : syracuseStep 2270863 = 3406295) B3406295
theorem B3406301 : Blo 2269435 3406301 := bbase (se 3 (by rfl) ⟨638681, by rfl⟩ : syracuseStep 3406301 = 1277363) (by norm_num)
theorem B2270867 : Blo 2269435 2270867 := bstep (se 1 (by rfl) ⟨1703150, by rfl⟩ : syracuseStep 2270867 = 3406301) B3406301
theorem B5109461 : Blo 2269435 5109461 := bbase (se 7 (by rfl) ⟨59876, by rfl⟩ : syracuseStep 5109461 = 119753) (by norm_num)
theorem B3406307 : Blo 2269435 3406307 := bstep (se 1 (by rfl) ⟨2554730, by rfl⟩ : syracuseStep 3406307 = 5109461) B5109461
theorem B2270871 : Blo 2269435 2270871 := bstep (se 1 (by rfl) ⟨1703153, by rfl⟩ : syracuseStep 2270871 = 3406307) B3406307
theorem B2728129 : Blo 2269435 2728129 := bbase (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) (by norm_num)
theorem B3637505 : Blo 2269435 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B9700013 : Blo 2269435 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B6466675 : Blo 2269435 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B8622233 : Blo 2269435 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B5748155 : Blo 2269435 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B3832103 : Blo 2269435 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B2554735 : Blo 2269435 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B3406313 : Blo 2269435 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B2270875 : Blo 2269435 2270875 := bstep (se 1 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 2270875 = 3406313) B3406313
theorem B12613877 : Blo 2269435 12613877 := bbase (se 5 (by rfl) ⟨591275, by rfl⟩ : syracuseStep 12613877 = 1182551) (by norm_num)
theorem B8409251 : Blo 2269435 8409251 := bstep (se 1 (by rfl) ⟨6306938, by rfl⟩ : syracuseStep 8409251 = 12613877) B12613877
theorem B5606167 : Blo 2269435 5606167 := bstep (se 1 (by rfl) ⟨4204625, by rfl⟩ : syracuseStep 5606167 = 8409251) B8409251
theorem B7474889 : Blo 2269435 7474889 := bstep (se 2 (by rfl) ⟨2803083, by rfl⟩ : syracuseStep 7474889 = 5606167) B5606167
theorem B19933037 : Blo 2269435 19933037 := bstep (se 3 (by rfl) ⟨3737444, by rfl⟩ : syracuseStep 19933037 = 7474889) B7474889
theorem B13288691 : Blo 2269435 13288691 := bstep (se 1 (by rfl) ⟨9966518, by rfl⟩ : syracuseStep 13288691 = 19933037) B19933037
theorem B8859127 : Blo 2269435 8859127 := bstep (se 1 (by rfl) ⟨6644345, by rfl⟩ : syracuseStep 8859127 = 13288691) B13288691
theorem B11812169 : Blo 2269435 11812169 := bstep (se 2 (by rfl) ⟨4429563, by rfl⟩ : syracuseStep 11812169 = 8859127) B8859127
theorem B7874779 : Blo 2269435 7874779 := bstep (se 1 (by rfl) ⟨5906084, by rfl⟩ : syracuseStep 7874779 = 11812169) B11812169
theorem B10499705 : Blo 2269435 10499705 := bstep (se 2 (by rfl) ⟨3937389, by rfl⟩ : syracuseStep 10499705 = 7874779) B7874779
theorem B6999803 : Blo 2269435 6999803 := bstep (se 1 (by rfl) ⟨5249852, by rfl⟩ : syracuseStep 6999803 = 10499705) B10499705
theorem B4666535 : Blo 2269435 4666535 := bstep (se 1 (by rfl) ⟨3499901, by rfl⟩ : syracuseStep 4666535 = 6999803) B6999803
theorem B49776373 : Blo 2269435 49776373 := bstep (se 5 (by rfl) ⟨2333267, by rfl⟩ : syracuseStep 49776373 = 4666535) B4666535
theorem B66368497 : Blo 2269435 66368497 := bstep (se 2 (by rfl) ⟨24888186, by rfl⟩ : syracuseStep 66368497 = 49776373) B49776373
theorem B88491329 : Blo 2269435 88491329 := bstep (se 2 (by rfl) ⟨33184248, by rfl⟩ : syracuseStep 88491329 = 66368497) B66368497
theorem B58994219 : Blo 2269435 58994219 := bstep (se 1 (by rfl) ⟨44245664, by rfl⟩ : syracuseStep 58994219 = 88491329) B88491329
theorem B39329479 : Blo 2269435 39329479 := bstep (se 1 (by rfl) ⟨29497109, by rfl⟩ : syracuseStep 39329479 = 58994219) B58994219
theorem B209757221 : Blo 2269435 209757221 := bstep (se 4 (by rfl) ⟨19664739, by rfl⟩ : syracuseStep 209757221 = 39329479) B39329479
theorem B139838147 : Blo 2269435 139838147 := bstep (se 1 (by rfl) ⟨104878610, by rfl⟩ : syracuseStep 139838147 = 209757221) B209757221
theorem B93225431 : Blo 2269435 93225431 := bstep (se 1 (by rfl) ⟨69919073, by rfl⟩ : syracuseStep 93225431 = 139838147) B139838147
theorem B62150287 : Blo 2269435 62150287 := bstep (se 1 (by rfl) ⟨46612715, by rfl⟩ : syracuseStep 62150287 = 93225431) B93225431
theorem B82867049 : Blo 2269435 82867049 := bstep (se 2 (by rfl) ⟨31075143, by rfl⟩ : syracuseStep 82867049 = 62150287) B62150287
theorem B55244699 : Blo 2269435 55244699 := bstep (se 1 (by rfl) ⟨41433524, by rfl⟩ : syracuseStep 55244699 = 82867049) B82867049
theorem B36829799 : Blo 2269435 36829799 := bstep (se 1 (by rfl) ⟨27622349, by rfl⟩ : syracuseStep 36829799 = 55244699) B55244699
theorem B24553199 : Blo 2269435 24553199 := bstep (se 1 (by rfl) ⟨18414899, by rfl⟩ : syracuseStep 24553199 = 36829799) B36829799
theorem B16368799 : Blo 2269435 16368799 := bstep (se 1 (by rfl) ⟨12276599, by rfl⟩ : syracuseStep 16368799 = 24553199) B24553199
theorem B21825065 : Blo 2269435 21825065 := bstep (se 2 (by rfl) ⟨8184399, by rfl⟩ : syracuseStep 21825065 = 16368799) B16368799
theorem B14550043 : Blo 2269435 14550043 := bstep (se 1 (by rfl) ⟨10912532, by rfl⟩ : syracuseStep 14550043 = 21825065) B21825065
theorem B19400057 : Blo 2269435 19400057 := bstep (se 2 (by rfl) ⟨7275021, by rfl⟩ : syracuseStep 19400057 = 14550043) B14550043
theorem B12933371 : Blo 2269435 12933371 := bstep (se 1 (by rfl) ⟨9700028, by rfl⟩ : syracuseStep 12933371 = 19400057) B19400057
theorem B8622247 : Blo 2269435 8622247 := bstep (se 1 (by rfl) ⟨6466685, by rfl⟩ : syracuseStep 8622247 = 12933371) B12933371
theorem B11496329 : Blo 2269435 11496329 := bstep (se 2 (by rfl) ⟨4311123, by rfl⟩ : syracuseStep 11496329 = 8622247) B8622247
theorem B7664219 : Blo 2269435 7664219 := bstep (se 1 (by rfl) ⟨5748164, by rfl⟩ : syracuseStep 7664219 = 11496329) B11496329
theorem B5109479 : Blo 2269435 5109479 := bstep (se 1 (by rfl) ⟨3832109, by rfl⟩ : syracuseStep 5109479 = 7664219) B7664219
theorem B3406319 : Blo 2269435 3406319 := bstep (se 1 (by rfl) ⟨2554739, by rfl⟩ : syracuseStep 3406319 = 5109479) B5109479
theorem B2270879 : Blo 2269435 2270879 := bstep (se 1 (by rfl) ⟨1703159, by rfl⟩ : syracuseStep 2270879 = 3406319) B3406319
theorem B3406325 : Blo 2269435 3406325 := bbase (se 5 (by rfl) ⟨159671, by rfl⟩ : syracuseStep 3406325 = 319343) (by norm_num)
theorem B2270883 : Blo 2269435 2270883 := bstep (se 1 (by rfl) ⟨1703162, by rfl⟩ : syracuseStep 2270883 = 3406325) B3406325
theorem B6466709 : Blo 2269435 6466709 := bbase (se 6 (by rfl) ⟨151563, by rfl⟩ : syracuseStep 6466709 = 303127) (by norm_num)
theorem B4311139 : Blo 2269435 4311139 := bstep (se 1 (by rfl) ⟨3233354, by rfl⟩ : syracuseStep 4311139 = 6466709) B6466709
theorem B5748185 : Blo 2269435 5748185 := bstep (se 2 (by rfl) ⟨2155569, by rfl⟩ : syracuseStep 5748185 = 4311139) B4311139
theorem B3832123 : Blo 2269435 3832123 := bstep (se 1 (by rfl) ⟨2874092, by rfl⟩ : syracuseStep 3832123 = 5748185) B5748185
theorem B5109497 : Blo 2269435 5109497 := bstep (se 2 (by rfl) ⟨1916061, by rfl⟩ : syracuseStep 5109497 = 3832123) B3832123
theorem B3406331 : Blo 2269435 3406331 := bstep (se 1 (by rfl) ⟨2554748, by rfl⟩ : syracuseStep 3406331 = 5109497) B5109497
theorem B2270887 : Blo 2269435 2270887 := bstep (se 1 (by rfl) ⟨1703165, by rfl⟩ : syracuseStep 2270887 = 3406331) B3406331
theorem B2554753 : Blo 2269435 2554753 := bbase (se 2 (by rfl) ⟨958032, by rfl⟩ : syracuseStep 2554753 = 1916065) (by norm_num)
theorem B3406337 : Blo 2269435 3406337 := bstep (se 2 (by rfl) ⟨1277376, by rfl⟩ : syracuseStep 3406337 = 2554753) B2554753
theorem B2270891 : Blo 2269435 2270891 := bstep (se 1 (by rfl) ⟨1703168, by rfl⟩ : syracuseStep 2270891 = 3406337) B3406337
theorem B5748205 : Blo 2269435 5748205 := bbase (se 3 (by rfl) ⟨1077788, by rfl⟩ : syracuseStep 5748205 = 2155577) (by norm_num)
theorem B7664273 : Blo 2269435 7664273 := bstep (se 2 (by rfl) ⟨2874102, by rfl⟩ : syracuseStep 7664273 = 5748205) B5748205
theorem B5109515 : Blo 2269435 5109515 := bstep (se 1 (by rfl) ⟨3832136, by rfl⟩ : syracuseStep 5109515 = 7664273) B7664273
theorem B3406343 : Blo 2269435 3406343 := bstep (se 1 (by rfl) ⟨2554757, by rfl⟩ : syracuseStep 3406343 = 5109515) B5109515
theorem B2270895 : Blo 2269435 2270895 := bstep (se 1 (by rfl) ⟨1703171, by rfl⟩ : syracuseStep 2270895 = 3406343) B3406343
theorem B3406349 : Blo 2269435 3406349 := bbase (se 3 (by rfl) ⟨638690, by rfl⟩ : syracuseStep 3406349 = 1277381) (by norm_num)
theorem B2270899 : Blo 2269435 2270899 := bstep (se 1 (by rfl) ⟨1703174, by rfl⟩ : syracuseStep 2270899 = 3406349) B3406349
theorem B5109533 : Blo 2269435 5109533 := bbase (se 3 (by rfl) ⟨958037, by rfl⟩ : syracuseStep 5109533 = 1916075) (by norm_num)
theorem B3406355 : Blo 2269435 3406355 := bstep (se 1 (by rfl) ⟨2554766, by rfl⟩ : syracuseStep 3406355 = 5109533) B5109533
theorem B2270903 : Blo 2269435 2270903 := bstep (se 1 (by rfl) ⟨1703177, by rfl⟩ : syracuseStep 2270903 = 3406355) B3406355
theorem B3832157 : Blo 2269435 3832157 := bbase (se 3 (by rfl) ⟨718529, by rfl⟩ : syracuseStep 3832157 = 1437059) (by norm_num)
theorem B2554771 : Blo 2269435 2554771 := bstep (se 1 (by rfl) ⟨1916078, by rfl⟩ : syracuseStep 2554771 = 3832157) B3832157
theorem B3406361 : Blo 2269435 3406361 := bstep (se 2 (by rfl) ⟨1277385, by rfl⟩ : syracuseStep 3406361 = 2554771) B2554771
theorem B2270907 : Blo 2269435 2270907 := bstep (se 1 (by rfl) ⟨1703180, by rfl⟩ : syracuseStep 2270907 = 3406361) B3406361
theorem B9700165 : Blo 2269435 9700165 := bbase (se 4 (by rfl) ⟨909390, by rfl⟩ : syracuseStep 9700165 = 1818781) (by norm_num)
theorem B12933553 : Blo 2269435 12933553 := bstep (se 2 (by rfl) ⟨4850082, by rfl⟩ : syracuseStep 12933553 = 9700165) B9700165
theorem B17244737 : Blo 2269435 17244737 := bstep (se 2 (by rfl) ⟨6466776, by rfl⟩ : syracuseStep 17244737 = 12933553) B12933553
theorem B11496491 : Blo 2269435 11496491 := bstep (se 1 (by rfl) ⟨8622368, by rfl⟩ : syracuseStep 11496491 = 17244737) B17244737
theorem B7664327 : Blo 2269435 7664327 := bstep (se 1 (by rfl) ⟨5748245, by rfl⟩ : syracuseStep 7664327 = 11496491) B11496491
theorem B5109551 : Blo 2269435 5109551 := bstep (se 1 (by rfl) ⟨3832163, by rfl⟩ : syracuseStep 5109551 = 7664327) B7664327
theorem B3406367 : Blo 2269435 3406367 := bstep (se 1 (by rfl) ⟨2554775, by rfl⟩ : syracuseStep 3406367 = 5109551) B5109551
theorem B2270911 : Blo 2269435 2270911 := bstep (se 1 (by rfl) ⟨1703183, by rfl⟩ : syracuseStep 2270911 = 3406367) B3406367
theorem B3406373 : Blo 2269435 3406373 := bbase (se 4 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 3406373 = 638695) (by norm_num)
theorem B2270915 : Blo 2269435 2270915 := bstep (se 1 (by rfl) ⟨1703186, by rfl⟩ : syracuseStep 2270915 = 3406373) B3406373
theorem B2874133 : Blo 2269435 2874133 := bbase (se 6 (by rfl) ⟨67362, by rfl⟩ : syracuseStep 2874133 = 134725) (by norm_num)
theorem B3832177 : Blo 2269435 3832177 := bstep (se 2 (by rfl) ⟨1437066, by rfl⟩ : syracuseStep 3832177 = 2874133) B2874133
theorem B5109569 : Blo 2269435 5109569 := bstep (se 2 (by rfl) ⟨1916088, by rfl⟩ : syracuseStep 5109569 = 3832177) B3832177
theorem B3406379 : Blo 2269435 3406379 := bstep (se 1 (by rfl) ⟨2554784, by rfl⟩ : syracuseStep 3406379 = 5109569) B5109569
theorem B2270919 : Blo 2269435 2270919 := bstep (se 1 (by rfl) ⟨1703189, by rfl⟩ : syracuseStep 2270919 = 3406379) B3406379
theorem B2554789 : Blo 2269435 2554789 := bbase (se 4 (by rfl) ⟨239511, by rfl⟩ : syracuseStep 2554789 = 479023) (by norm_num)
theorem B3406385 : Blo 2269435 3406385 := bstep (se 2 (by rfl) ⟨1277394, by rfl⟩ : syracuseStep 3406385 = 2554789) B2554789
theorem B2270923 : Blo 2269435 2270923 := bstep (se 1 (by rfl) ⟨1703192, by rfl⟩ : syracuseStep 2270923 = 3406385) B3406385
theorem B46613717 : Blo 2269435 46613717 := bbase (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) (by norm_num)
theorem B31075811 : Blo 2269435 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B20717207 : Blo 2269435 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B13811471 : Blo 2269435 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B9207647 : Blo 2269435 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B6138431 : Blo 2269435 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B4092287 : Blo 2269435 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B10912765 : Blo 2269435 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B14550353 : Blo 2269435 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B9700235 : Blo 2269435 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B6466823 : Blo 2269435 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B4311215 : Blo 2269435 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B2874143 : Blo 2269435 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B7664381 : Blo 2269435 7664381 := bstep (se 3 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 7664381 = 2874143) B2874143
theorem B5109587 : Blo 2269435 5109587 := bstep (se 1 (by rfl) ⟨3832190, by rfl⟩ : syracuseStep 5109587 = 7664381) B7664381
theorem B3406391 : Blo 2269435 3406391 := bstep (se 1 (by rfl) ⟨2554793, by rfl⟩ : syracuseStep 3406391 = 5109587) B5109587
theorem B2270927 : Blo 2269435 2270927 := bstep (se 1 (by rfl) ⟨1703195, by rfl⟩ : syracuseStep 2270927 = 3406391) B3406391
theorem B3406397 : Blo 2269435 3406397 := bbase (se 3 (by rfl) ⟨638699, by rfl⟩ : syracuseStep 3406397 = 1277399) (by norm_num)
theorem B2270931 : Blo 2269435 2270931 := bstep (se 1 (by rfl) ⟨1703198, by rfl⟩ : syracuseStep 2270931 = 3406397) B3406397
theorem B5109605 : Blo 2269435 5109605 := bbase (se 4 (by rfl) ⟨479025, by rfl⟩ : syracuseStep 5109605 = 958051) (by norm_num)
theorem B3406403 : Blo 2269435 3406403 := bstep (se 1 (by rfl) ⟨2554802, by rfl⟩ : syracuseStep 3406403 = 5109605) B5109605
theorem B2270935 : Blo 2269435 2270935 := bstep (se 1 (by rfl) ⟨1703201, by rfl⟩ : syracuseStep 2270935 = 3406403) B3406403
theorem B5748317 : Blo 2269435 5748317 := bbase (se 3 (by rfl) ⟨1077809, by rfl⟩ : syracuseStep 5748317 = 2155619) (by norm_num)
theorem B3832211 : Blo 2269435 3832211 := bstep (se 1 (by rfl) ⟨2874158, by rfl⟩ : syracuseStep 3832211 = 5748317) B5748317
theorem B2554807 : Blo 2269435 2554807 := bstep (se 1 (by rfl) ⟨1916105, by rfl⟩ : syracuseStep 2554807 = 3832211) B3832211
theorem B3406409 : Blo 2269435 3406409 := bstep (se 2 (by rfl) ⟨1277403, by rfl⟩ : syracuseStep 3406409 = 2554807) B2554807
theorem B2270939 : Blo 2269435 2270939 := bstep (se 1 (by rfl) ⟨1703204, by rfl⟩ : syracuseStep 2270939 = 3406409) B3406409
theorem B4311245 : Blo 2269435 4311245 := bbase (se 3 (by rfl) ⟨808358, by rfl⟩ : syracuseStep 4311245 = 1616717) (by norm_num)
theorem B11496653 : Blo 2269435 11496653 := bstep (se 3 (by rfl) ⟨2155622, by rfl⟩ : syracuseStep 11496653 = 4311245) B4311245
theorem B7664435 : Blo 2269435 7664435 := bstep (se 1 (by rfl) ⟨5748326, by rfl⟩ : syracuseStep 7664435 = 11496653) B11496653
theorem B5109623 : Blo 2269435 5109623 := bstep (se 1 (by rfl) ⟨3832217, by rfl⟩ : syracuseStep 5109623 = 7664435) B7664435
theorem B3406415 : Blo 2269435 3406415 := bstep (se 1 (by rfl) ⟨2554811, by rfl⟩ : syracuseStep 3406415 = 5109623) B5109623
theorem B2270943 : Blo 2269435 2270943 := bstep (se 1 (by rfl) ⟨1703207, by rfl⟩ : syracuseStep 2270943 = 3406415) B3406415
theorem B3406421 : Blo 2269435 3406421 := bbase (se 8 (by rfl) ⟨19959, by rfl⟩ : syracuseStep 3406421 = 39919) (by norm_num)
theorem B2270947 : Blo 2269435 2270947 := bstep (se 1 (by rfl) ⟨1703210, by rfl⟩ : syracuseStep 2270947 = 3406421) B3406421
theorem B7275253 : Blo 2269435 7275253 := bbase (se 5 (by rfl) ⟨341027, by rfl⟩ : syracuseStep 7275253 = 682055) (by norm_num)
theorem B9700337 : Blo 2269435 9700337 := bstep (se 2 (by rfl) ⟨3637626, by rfl⟩ : syracuseStep 9700337 = 7275253) B7275253
theorem B6466891 : Blo 2269435 6466891 := bstep (se 1 (by rfl) ⟨4850168, by rfl⟩ : syracuseStep 6466891 = 9700337) B9700337
theorem B8622521 : Blo 2269435 8622521 := bstep (se 2 (by rfl) ⟨3233445, by rfl⟩ : syracuseStep 8622521 = 6466891) B6466891
theorem B5748347 : Blo 2269435 5748347 := bstep (se 1 (by rfl) ⟨4311260, by rfl⟩ : syracuseStep 5748347 = 8622521) B8622521
theorem B3832231 : Blo 2269435 3832231 := bstep (se 1 (by rfl) ⟨2874173, by rfl⟩ : syracuseStep 3832231 = 5748347) B5748347
theorem B5109641 : Blo 2269435 5109641 := bstep (se 2 (by rfl) ⟨1916115, by rfl⟩ : syracuseStep 5109641 = 3832231) B3832231
theorem B3406427 : Blo 2269435 3406427 := bstep (se 1 (by rfl) ⟨2554820, by rfl⟩ : syracuseStep 3406427 = 5109641) B5109641
theorem B2270951 : Blo 2269435 2270951 := bstep (se 1 (by rfl) ⟨1703213, by rfl⟩ : syracuseStep 2270951 = 3406427) B3406427
theorem B2554825 : Blo 2269435 2554825 := bbase (se 2 (by rfl) ⟨958059, by rfl⟩ : syracuseStep 2554825 = 1916119) (by norm_num)
theorem B3406433 : Blo 2269435 3406433 := bstep (se 2 (by rfl) ⟨1277412, by rfl⟩ : syracuseStep 3406433 = 2554825) B2554825
theorem B2270955 : Blo 2269435 2270955 := bstep (se 1 (by rfl) ⟨1703216, by rfl⟩ : syracuseStep 2270955 = 3406433) B3406433
theorem B6138517 : Blo 2269435 6138517 := bbase (se 6 (by rfl) ⟨143871, by rfl⟩ : syracuseStep 6138517 = 287743) (by norm_num)
theorem B8184689 : Blo 2269435 8184689 := bstep (se 2 (by rfl) ⟨3069258, by rfl⟩ : syracuseStep 8184689 = 6138517) B6138517
theorem B5456459 : Blo 2269435 5456459 := bstep (se 1 (by rfl) ⟨4092344, by rfl⟩ : syracuseStep 5456459 = 8184689) B8184689
theorem B3637639 : Blo 2269435 3637639 := bstep (se 1 (by rfl) ⟨2728229, by rfl⟩ : syracuseStep 3637639 = 5456459) B5456459
theorem B19400741 : Blo 2269435 19400741 := bstep (se 4 (by rfl) ⟨1818819, by rfl⟩ : syracuseStep 19400741 = 3637639) B3637639
theorem B12933827 : Blo 2269435 12933827 := bstep (se 1 (by rfl) ⟨9700370, by rfl⟩ : syracuseStep 12933827 = 19400741) B19400741
theorem B8622551 : Blo 2269435 8622551 := bstep (se 1 (by rfl) ⟨6466913, by rfl⟩ : syracuseStep 8622551 = 12933827) B12933827
theorem B5748367 : Blo 2269435 5748367 := bstep (se 1 (by rfl) ⟨4311275, by rfl⟩ : syracuseStep 5748367 = 8622551) B8622551
theorem B7664489 : Blo 2269435 7664489 := bstep (se 2 (by rfl) ⟨2874183, by rfl⟩ : syracuseStep 7664489 = 5748367) B5748367
theorem B5109659 : Blo 2269435 5109659 := bstep (se 1 (by rfl) ⟨3832244, by rfl⟩ : syracuseStep 5109659 = 7664489) B7664489
theorem B3406439 : Blo 2269435 3406439 := bstep (se 1 (by rfl) ⟨2554829, by rfl⟩ : syracuseStep 3406439 = 5109659) B5109659
theorem B2270959 : Blo 2269435 2270959 := bstep (se 1 (by rfl) ⟨1703219, by rfl⟩ : syracuseStep 2270959 = 3406439) B3406439
theorem B3406445 : Blo 2269435 3406445 := bbase (se 3 (by rfl) ⟨638708, by rfl⟩ : syracuseStep 3406445 = 1277417) (by norm_num)
theorem B2270963 : Blo 2269435 2270963 := bstep (se 1 (by rfl) ⟨1703222, by rfl⟩ : syracuseStep 2270963 = 3406445) B3406445
theorem B5109677 : Blo 2269435 5109677 := bbase (se 3 (by rfl) ⟨958064, by rfl⟩ : syracuseStep 5109677 = 1916129) (by norm_num)
theorem B3406451 : Blo 2269435 3406451 := bstep (se 1 (by rfl) ⟨2554838, by rfl⟩ : syracuseStep 3406451 = 5109677) B5109677
theorem B2270967 : Blo 2269435 2270967 := bstep (se 1 (by rfl) ⟨1703225, by rfl⟩ : syracuseStep 2270967 = 3406451) B3406451
theorem B6466949 : Blo 2269435 6466949 := bbase (se 4 (by rfl) ⟨606276, by rfl⟩ : syracuseStep 6466949 = 1212553) (by norm_num)
theorem B4311299 : Blo 2269435 4311299 := bstep (se 1 (by rfl) ⟨3233474, by rfl⟩ : syracuseStep 4311299 = 6466949) B6466949
theorem B2874199 : Blo 2269435 2874199 := bstep (se 1 (by rfl) ⟨2155649, by rfl⟩ : syracuseStep 2874199 = 4311299) B4311299
theorem B3832265 : Blo 2269435 3832265 := bstep (se 2 (by rfl) ⟨1437099, by rfl⟩ : syracuseStep 3832265 = 2874199) B2874199
theorem B2554843 : Blo 2269435 2554843 := bstep (se 1 (by rfl) ⟨1916132, by rfl⟩ : syracuseStep 2554843 = 3832265) B3832265
theorem B3406457 : Blo 2269435 3406457 := bstep (se 2 (by rfl) ⟨1277421, by rfl⟩ : syracuseStep 3406457 = 2554843) B2554843
theorem B2270971 : Blo 2269435 2270971 := bstep (se 1 (by rfl) ⟨1703228, by rfl⟩ : syracuseStep 2270971 = 3406457) B3406457
theorem B10500149 : Blo 2269435 10500149 := bbase (se 5 (by rfl) ⟨492194, by rfl⟩ : syracuseStep 10500149 = 984389) (by norm_num)
theorem B28000397 : Blo 2269435 28000397 := bstep (se 3 (by rfl) ⟨5250074, by rfl⟩ : syracuseStep 28000397 = 10500149) B10500149
theorem B18666931 : Blo 2269435 18666931 := bstep (se 1 (by rfl) ⟨14000198, by rfl⟩ : syracuseStep 18666931 = 28000397) B28000397
theorem B24889241 : Blo 2269435 24889241 := bstep (se 2 (by rfl) ⟨9333465, by rfl⟩ : syracuseStep 24889241 = 18666931) B18666931
theorem B66371309 : Blo 2269435 66371309 := bstep (se 3 (by rfl) ⟨12444620, by rfl⟩ : syracuseStep 66371309 = 24889241) B24889241
theorem B44247539 : Blo 2269435 44247539 := bstep (se 1 (by rfl) ⟨33185654, by rfl⟩ : syracuseStep 44247539 = 66371309) B66371309
theorem B29498359 : Blo 2269435 29498359 := bstep (se 1 (by rfl) ⟨22123769, by rfl⟩ : syracuseStep 29498359 = 44247539) B44247539
theorem B39331145 : Blo 2269435 39331145 := bstep (se 2 (by rfl) ⟨14749179, by rfl⟩ : syracuseStep 39331145 = 29498359) B29498359
theorem B26220763 : Blo 2269435 26220763 := bstep (se 1 (by rfl) ⟨19665572, by rfl⟩ : syracuseStep 26220763 = 39331145) B39331145
theorem B34961017 : Blo 2269435 34961017 := bstep (se 2 (by rfl) ⟨13110381, by rfl⟩ : syracuseStep 34961017 = 26220763) B26220763
theorem B46614689 : Blo 2269435 46614689 := bstep (se 2 (by rfl) ⟨17480508, by rfl⟩ : syracuseStep 46614689 = 34961017) B34961017
theorem B31076459 : Blo 2269435 31076459 := bstep (se 1 (by rfl) ⟨23307344, by rfl⟩ : syracuseStep 31076459 = 46614689) B46614689
theorem B20717639 : Blo 2269435 20717639 := bstep (se 1 (by rfl) ⟨15538229, by rfl⟩ : syracuseStep 20717639 = 31076459) B31076459
theorem B13811759 : Blo 2269435 13811759 := bstep (se 1 (by rfl) ⟨10358819, by rfl⟩ : syracuseStep 13811759 = 20717639) B20717639
theorem B9207839 : Blo 2269435 9207839 := bstep (se 1 (by rfl) ⟨6905879, by rfl⟩ : syracuseStep 9207839 = 13811759) B13811759
theorem B6138559 : Blo 2269435 6138559 := bstep (se 1 (by rfl) ⟨4603919, by rfl⟩ : syracuseStep 6138559 = 9207839) B9207839
theorem B8184745 : Blo 2269435 8184745 := bstep (se 2 (by rfl) ⟨3069279, by rfl⟩ : syracuseStep 8184745 = 6138559) B6138559
theorem B43651973 : Blo 2269435 43651973 := bstep (se 4 (by rfl) ⟨4092372, by rfl⟩ : syracuseStep 43651973 = 8184745) B8184745
theorem B29101315 : Blo 2269435 29101315 := bstep (se 1 (by rfl) ⟨21825986, by rfl⟩ : syracuseStep 29101315 = 43651973) B43651973
theorem B38801753 : Blo 2269435 38801753 := bstep (se 2 (by rfl) ⟨14550657, by rfl⟩ : syracuseStep 38801753 = 29101315) B29101315
theorem B25867835 : Blo 2269435 25867835 := bstep (se 1 (by rfl) ⟨19400876, by rfl⟩ : syracuseStep 25867835 = 38801753) B38801753
theorem B17245223 : Blo 2269435 17245223 := bstep (se 1 (by rfl) ⟨12933917, by rfl⟩ : syracuseStep 17245223 = 25867835) B25867835
theorem B11496815 : Blo 2269435 11496815 := bstep (se 1 (by rfl) ⟨8622611, by rfl⟩ : syracuseStep 11496815 = 17245223) B17245223
theorem B7664543 : Blo 2269435 7664543 := bstep (se 1 (by rfl) ⟨5748407, by rfl⟩ : syracuseStep 7664543 = 11496815) B11496815
theorem B5109695 : Blo 2269435 5109695 := bstep (se 1 (by rfl) ⟨3832271, by rfl⟩ : syracuseStep 5109695 = 7664543) B7664543
theorem B3406463 : Blo 2269435 3406463 := bstep (se 1 (by rfl) ⟨2554847, by rfl⟩ : syracuseStep 3406463 = 5109695) B5109695
theorem B2270975 : Blo 2269435 2270975 := bstep (se 1 (by rfl) ⟨1703231, by rfl⟩ : syracuseStep 2270975 = 3406463) B3406463
theorem B3406469 : Blo 2269435 3406469 := bbase (se 4 (by rfl) ⟨319356, by rfl⟩ : syracuseStep 3406469 = 638713) (by norm_num)
theorem B2270979 : Blo 2269435 2270979 := bstep (se 1 (by rfl) ⟨1703234, by rfl⟩ : syracuseStep 2270979 = 3406469) B3406469
theorem B3832285 : Blo 2269435 3832285 := bbase (se 3 (by rfl) ⟨718553, by rfl⟩ : syracuseStep 3832285 = 1437107) (by norm_num)
theorem B5109713 : Blo 2269435 5109713 := bstep (se 2 (by rfl) ⟨1916142, by rfl⟩ : syracuseStep 5109713 = 3832285) B3832285
theorem B3406475 : Blo 2269435 3406475 := bstep (se 1 (by rfl) ⟨2554856, by rfl⟩ : syracuseStep 3406475 = 5109713) B5109713
theorem B2270983 : Blo 2269435 2270983 := bstep (se 1 (by rfl) ⟨1703237, by rfl⟩ : syracuseStep 2270983 = 3406475) B3406475
theorem B2554861 : Blo 2269435 2554861 := bbase (se 3 (by rfl) ⟨479036, by rfl⟩ : syracuseStep 2554861 = 958073) (by norm_num)
theorem B3406481 : Blo 2269435 3406481 := bstep (se 2 (by rfl) ⟨1277430, by rfl⟩ : syracuseStep 3406481 = 2554861) B2554861
theorem B2270987 : Blo 2269435 2270987 := bstep (se 1 (by rfl) ⟨1703240, by rfl⟩ : syracuseStep 2270987 = 3406481) B3406481
theorem B7664597 : Blo 2269435 7664597 := bbase (se 7 (by rfl) ⟨89819, by rfl⟩ : syracuseStep 7664597 = 179639) (by norm_num)
theorem B5109731 : Blo 2269435 5109731 := bstep (se 1 (by rfl) ⟨3832298, by rfl⟩ : syracuseStep 5109731 = 7664597) B7664597
theorem B3406487 : Blo 2269435 3406487 := bstep (se 1 (by rfl) ⟨2554865, by rfl⟩ : syracuseStep 3406487 = 5109731) B5109731
theorem B2270991 : Blo 2269435 2270991 := bstep (se 1 (by rfl) ⟨1703243, by rfl⟩ : syracuseStep 2270991 = 3406487) B3406487
theorem B3406493 : Blo 2269435 3406493 := bbase (se 3 (by rfl) ⟨638717, by rfl⟩ : syracuseStep 3406493 = 1277435) (by norm_num)
theorem B2270995 : Blo 2269435 2270995 := bstep (se 1 (by rfl) ⟨1703246, by rfl⟩ : syracuseStep 2270995 = 3406493) B3406493
theorem B5109749 : Blo 2269435 5109749 := bbase (se 5 (by rfl) ⟨239519, by rfl⟩ : syracuseStep 5109749 = 479039) (by norm_num)
theorem B3406499 : Blo 2269435 3406499 := bstep (se 1 (by rfl) ⟨2554874, by rfl⟩ : syracuseStep 3406499 = 5109749) B5109749
theorem B2270999 : Blo 2269435 2270999 := bstep (se 1 (by rfl) ⟨1703249, by rfl⟩ : syracuseStep 2270999 = 3406499) B3406499
theorem B4490245 : Blo 2269435 4490245 := bbase (se 4 (by rfl) ⟨420960, by rfl⟩ : syracuseStep 4490245 = 841921) (by norm_num)
theorem B5986993 : Blo 2269435 5986993 := bstep (se 2 (by rfl) ⟨2245122, by rfl⟩ : syracuseStep 5986993 = 4490245) B4490245
theorem B7982657 : Blo 2269435 7982657 := bstep (se 2 (by rfl) ⟨2993496, by rfl⟩ : syracuseStep 7982657 = 5986993) B5986993
theorem B5321771 : Blo 2269435 5321771 := bstep (se 1 (by rfl) ⟨3991328, by rfl⟩ : syracuseStep 5321771 = 7982657) B7982657
theorem B3547847 : Blo 2269435 3547847 := bstep (se 1 (by rfl) ⟨2660885, by rfl⟩ : syracuseStep 3547847 = 5321771) B5321771
theorem B9460925 : Blo 2269435 9460925 := bstep (se 3 (by rfl) ⟨1773923, by rfl⟩ : syracuseStep 9460925 = 3547847) B3547847
theorem B6307283 : Blo 2269435 6307283 := bstep (se 1 (by rfl) ⟨4730462, by rfl⟩ : syracuseStep 6307283 = 9460925) B9460925
theorem B4204855 : Blo 2269435 4204855 := bstep (se 1 (by rfl) ⟨3153641, by rfl⟩ : syracuseStep 4204855 = 6307283) B6307283
theorem B22425893 : Blo 2269435 22425893 := bstep (se 4 (by rfl) ⟨2102427, by rfl⟩ : syracuseStep 22425893 = 4204855) B4204855
theorem B14950595 : Blo 2269435 14950595 := bstep (se 1 (by rfl) ⟨11212946, by rfl⟩ : syracuseStep 14950595 = 22425893) B22425893
theorem B9967063 : Blo 2269435 9967063 := bstep (se 1 (by rfl) ⟨7475297, by rfl⟩ : syracuseStep 9967063 = 14950595) B14950595
theorem B13289417 : Blo 2269435 13289417 := bstep (se 2 (by rfl) ⟨4983531, by rfl⟩ : syracuseStep 13289417 = 9967063) B9967063
theorem B8859611 : Blo 2269435 8859611 := bstep (se 1 (by rfl) ⟨6644708, by rfl⟩ : syracuseStep 8859611 = 13289417) B13289417
theorem B5906407 : Blo 2269435 5906407 := bstep (se 1 (by rfl) ⟨4429805, by rfl⟩ : syracuseStep 5906407 = 8859611) B8859611
theorem B7875209 : Blo 2269435 7875209 := bstep (se 2 (by rfl) ⟨2953203, by rfl⟩ : syracuseStep 7875209 = 5906407) B5906407
theorem B21000557 : Blo 2269435 21000557 := bstep (se 3 (by rfl) ⟨3937604, by rfl⟩ : syracuseStep 21000557 = 7875209) B7875209
theorem B14000371 : Blo 2269435 14000371 := bstep (se 1 (by rfl) ⟨10500278, by rfl⟩ : syracuseStep 14000371 = 21000557) B21000557
theorem B74668645 : Blo 2269435 74668645 := bstep (se 4 (by rfl) ⟨7000185, by rfl⟩ : syracuseStep 74668645 = 14000371) B14000371
theorem B99558193 : Blo 2269435 99558193 := bstep (se 2 (by rfl) ⟨37334322, by rfl⟩ : syracuseStep 99558193 = 74668645) B74668645
theorem B132744257 : Blo 2269435 132744257 := bstep (se 2 (by rfl) ⟨49779096, by rfl⟩ : syracuseStep 132744257 = 99558193) B99558193
theorem B88496171 : Blo 2269435 88496171 := bstep (se 1 (by rfl) ⟨66372128, by rfl⟩ : syracuseStep 88496171 = 132744257) B132744257
theorem B58997447 : Blo 2269435 58997447 := bstep (se 1 (by rfl) ⟨44248085, by rfl⟩ : syracuseStep 58997447 = 88496171) B88496171
theorem B39331631 : Blo 2269435 39331631 := bstep (se 1 (by rfl) ⟨29498723, by rfl⟩ : syracuseStep 39331631 = 58997447) B58997447
theorem B26221087 : Blo 2269435 26221087 := bstep (se 1 (by rfl) ⟨19665815, by rfl⟩ : syracuseStep 26221087 = 39331631) B39331631
theorem B34961449 : Blo 2269435 34961449 := bstep (se 2 (by rfl) ⟨13110543, by rfl⟩ : syracuseStep 34961449 = 26221087) B26221087
theorem B46615265 : Blo 2269435 46615265 := bstep (se 2 (by rfl) ⟨17480724, by rfl⟩ : syracuseStep 46615265 = 34961449) B34961449
theorem B31076843 : Blo 2269435 31076843 := bstep (se 1 (by rfl) ⟨23307632, by rfl⟩ : syracuseStep 31076843 = 46615265) B46615265
theorem B82871581 : Blo 2269435 82871581 := bstep (se 3 (by rfl) ⟨15538421, by rfl⟩ : syracuseStep 82871581 = 31076843) B31076843
theorem B110495441 : Blo 2269435 110495441 := bstep (se 2 (by rfl) ⟨41435790, by rfl⟩ : syracuseStep 110495441 = 82871581) B82871581
theorem B73663627 : Blo 2269435 73663627 := bstep (se 1 (by rfl) ⟨55247720, by rfl⟩ : syracuseStep 73663627 = 110495441) B110495441
theorem B98218169 : Blo 2269435 98218169 := bstep (se 2 (by rfl) ⟨36831813, by rfl⟩ : syracuseStep 98218169 = 73663627) B73663627
theorem B65478779 : Blo 2269435 65478779 := bstep (se 1 (by rfl) ⟨49109084, by rfl⟩ : syracuseStep 65478779 = 98218169) B98218169
theorem B43652519 : Blo 2269435 43652519 := bstep (se 1 (by rfl) ⟨32739389, by rfl⟩ : syracuseStep 43652519 = 65478779) B65478779
theorem B29101679 : Blo 2269435 29101679 := bstep (se 1 (by rfl) ⟨21826259, by rfl⟩ : syracuseStep 29101679 = 43652519) B43652519
theorem B19401119 : Blo 2269435 19401119 := bstep (se 1 (by rfl) ⟨14550839, by rfl⟩ : syracuseStep 19401119 = 29101679) B29101679
theorem B12934079 : Blo 2269435 12934079 := bstep (se 1 (by rfl) ⟨9700559, by rfl⟩ : syracuseStep 12934079 = 19401119) B19401119
theorem B8622719 : Blo 2269435 8622719 := bstep (se 1 (by rfl) ⟨6467039, by rfl⟩ : syracuseStep 8622719 = 12934079) B12934079
theorem B5748479 : Blo 2269435 5748479 := bstep (se 1 (by rfl) ⟨4311359, by rfl⟩ : syracuseStep 5748479 = 8622719) B8622719
theorem B3832319 : Blo 2269435 3832319 := bstep (se 1 (by rfl) ⟨2874239, by rfl⟩ : syracuseStep 3832319 = 5748479) B5748479
theorem B2554879 : Blo 2269435 2554879 := bstep (se 1 (by rfl) ⟨1916159, by rfl⟩ : syracuseStep 2554879 = 3832319) B3832319
theorem B3406505 : Blo 2269435 3406505 := bstep (se 2 (by rfl) ⟨1277439, by rfl⟩ : syracuseStep 3406505 = 2554879) B2554879
theorem B2271003 : Blo 2269435 2271003 := bstep (se 1 (by rfl) ⟨1703252, by rfl⟩ : syracuseStep 2271003 = 3406505) B3406505
theorem B3233525 : Blo 2269435 3233525 := bbase (se 5 (by rfl) ⟨151571, by rfl⟩ : syracuseStep 3233525 = 303143) (by norm_num)
theorem B8622733 : Blo 2269435 8622733 := bstep (se 3 (by rfl) ⟨1616762, by rfl⟩ : syracuseStep 8622733 = 3233525) B3233525
theorem B11496977 : Blo 2269435 11496977 := bstep (se 2 (by rfl) ⟨4311366, by rfl⟩ : syracuseStep 11496977 = 8622733) B8622733
theorem B7664651 : Blo 2269435 7664651 := bstep (se 1 (by rfl) ⟨5748488, by rfl⟩ : syracuseStep 7664651 = 11496977) B11496977
theorem B5109767 : Blo 2269435 5109767 := bstep (se 1 (by rfl) ⟨3832325, by rfl⟩ : syracuseStep 5109767 = 7664651) B7664651
theorem B3406511 : Blo 2269435 3406511 := bstep (se 1 (by rfl) ⟨2554883, by rfl⟩ : syracuseStep 3406511 = 5109767) B5109767
theorem B2271007 : Blo 2269435 2271007 := bstep (se 1 (by rfl) ⟨1703255, by rfl⟩ : syracuseStep 2271007 = 3406511) B3406511
theorem B3406517 : Blo 2269435 3406517 := bbase (se 5 (by rfl) ⟨159680, by rfl⟩ : syracuseStep 3406517 = 319361) (by norm_num)
theorem B2271011 : Blo 2269435 2271011 := bstep (se 1 (by rfl) ⟨1703258, by rfl⟩ : syracuseStep 2271011 = 3406517) B3406517
theorem B5748509 : Blo 2269435 5748509 := bbase (se 3 (by rfl) ⟨1077845, by rfl⟩ : syracuseStep 5748509 = 2155691) (by norm_num)
theorem B3832339 : Blo 2269435 3832339 := bstep (se 1 (by rfl) ⟨2874254, by rfl⟩ : syracuseStep 3832339 = 5748509) B5748509
theorem B5109785 : Blo 2269435 5109785 := bstep (se 2 (by rfl) ⟨1916169, by rfl⟩ : syracuseStep 5109785 = 3832339) B3832339
theorem B3406523 : Blo 2269435 3406523 := bstep (se 1 (by rfl) ⟨2554892, by rfl⟩ : syracuseStep 3406523 = 5109785) B5109785
theorem B2271015 : Blo 2269435 2271015 := bstep (se 1 (by rfl) ⟨1703261, by rfl⟩ : syracuseStep 2271015 = 3406523) B3406523
theorem B2554897 : Blo 2269435 2554897 := bbase (se 2 (by rfl) ⟨958086, by rfl⟩ : syracuseStep 2554897 = 1916173) (by norm_num)
theorem B3406529 : Blo 2269435 3406529 := bstep (se 2 (by rfl) ⟨1277448, by rfl⟩ : syracuseStep 3406529 = 2554897) B2554897
theorem B2271019 : Blo 2269435 2271019 := bstep (se 1 (by rfl) ⟨1703264, by rfl⟩ : syracuseStep 2271019 = 3406529) B3406529
theorem B4311397 : Blo 2269435 4311397 := bbase (se 4 (by rfl) ⟨404193, by rfl⟩ : syracuseStep 4311397 = 808387) (by norm_num)
theorem B5748529 : Blo 2269435 5748529 := bstep (se 2 (by rfl) ⟨2155698, by rfl⟩ : syracuseStep 5748529 = 4311397) B4311397
theorem B7664705 : Blo 2269435 7664705 := bstep (se 2 (by rfl) ⟨2874264, by rfl⟩ : syracuseStep 7664705 = 5748529) B5748529
theorem B5109803 : Blo 2269435 5109803 := bstep (se 1 (by rfl) ⟨3832352, by rfl⟩ : syracuseStep 5109803 = 7664705) B7664705
theorem B3406535 : Blo 2269435 3406535 := bstep (se 1 (by rfl) ⟨2554901, by rfl⟩ : syracuseStep 3406535 = 5109803) B5109803
theorem B2271023 : Blo 2269435 2271023 := bstep (se 1 (by rfl) ⟨1703267, by rfl⟩ : syracuseStep 2271023 = 3406535) B3406535
theorem B3406541 : Blo 2269435 3406541 := bbase (se 3 (by rfl) ⟨638726, by rfl⟩ : syracuseStep 3406541 = 1277453) (by norm_num)
theorem B2271027 : Blo 2269435 2271027 := bstep (se 1 (by rfl) ⟨1703270, by rfl⟩ : syracuseStep 2271027 = 3406541) B3406541
theorem B5109821 : Blo 2269435 5109821 := bbase (se 3 (by rfl) ⟨958091, by rfl⟩ : syracuseStep 5109821 = 1916183) (by norm_num)
theorem B3406547 : Blo 2269435 3406547 := bstep (se 1 (by rfl) ⟨2554910, by rfl⟩ : syracuseStep 3406547 = 5109821) B5109821
theorem B2271031 : Blo 2269435 2271031 := bstep (se 1 (by rfl) ⟨1703273, by rfl⟩ : syracuseStep 2271031 = 3406547) B3406547
theorem B3832373 : Blo 2269435 3832373 := bbase (se 5 (by rfl) ⟨179642, by rfl⟩ : syracuseStep 3832373 = 359285) (by norm_num)
theorem B2554915 : Blo 2269435 2554915 := bstep (se 1 (by rfl) ⟨1916186, by rfl⟩ : syracuseStep 2554915 = 3832373) B3832373
theorem B3406553 : Blo 2269435 3406553 := bstep (se 2 (by rfl) ⟨1277457, by rfl⟩ : syracuseStep 3406553 = 2554915) B2554915
theorem B2271035 : Blo 2269435 2271035 := bstep (se 1 (by rfl) ⟨1703276, by rfl⟩ : syracuseStep 2271035 = 3406553) B3406553
theorem B6467141 : Blo 2269435 6467141 := bbase (se 4 (by rfl) ⟨606294, by rfl⟩ : syracuseStep 6467141 = 1212589) (by norm_num)
theorem B17245709 : Blo 2269435 17245709 := bstep (se 3 (by rfl) ⟨3233570, by rfl⟩ : syracuseStep 17245709 = 6467141) B6467141
theorem B11497139 : Blo 2269435 11497139 := bstep (se 1 (by rfl) ⟨8622854, by rfl⟩ : syracuseStep 11497139 = 17245709) B17245709
theorem B7664759 : Blo 2269435 7664759 := bstep (se 1 (by rfl) ⟨5748569, by rfl⟩ : syracuseStep 7664759 = 11497139) B11497139
theorem B5109839 : Blo 2269435 5109839 := bstep (se 1 (by rfl) ⟨3832379, by rfl⟩ : syracuseStep 5109839 = 7664759) B7664759
theorem B3406559 : Blo 2269435 3406559 := bstep (se 1 (by rfl) ⟨2554919, by rfl⟩ : syracuseStep 3406559 = 5109839) B5109839
theorem B2271039 : Blo 2269435 2271039 := bstep (se 1 (by rfl) ⟨1703279, by rfl⟩ : syracuseStep 2271039 = 3406559) B3406559
theorem B3406565 : Blo 2269435 3406565 := bbase (se 4 (by rfl) ⟨319365, by rfl⟩ : syracuseStep 3406565 = 638731) (by norm_num)
theorem B2271043 : Blo 2269435 2271043 := bstep (se 1 (by rfl) ⟨1703282, by rfl⟩ : syracuseStep 2271043 = 3406565) B3406565
theorem B3637781 : Blo 2269435 3637781 := bbase (se 6 (by rfl) ⟨85260, by rfl⟩ : syracuseStep 3637781 = 170521) (by norm_num)
theorem B2425187 : Blo 2269435 2425187 := bstep (se 1 (by rfl) ⟨1818890, by rfl⟩ : syracuseStep 2425187 = 3637781) B3637781
theorem B6467165 : Blo 2269435 6467165 := bstep (se 3 (by rfl) ⟨1212593, by rfl⟩ : syracuseStep 6467165 = 2425187) B2425187
theorem B4311443 : Blo 2269435 4311443 := bstep (se 1 (by rfl) ⟨3233582, by rfl⟩ : syracuseStep 4311443 = 6467165) B6467165
theorem B2874295 : Blo 2269435 2874295 := bstep (se 1 (by rfl) ⟨2155721, by rfl⟩ : syracuseStep 2874295 = 4311443) B4311443
theorem B3832393 : Blo 2269435 3832393 := bstep (se 2 (by rfl) ⟨1437147, by rfl⟩ : syracuseStep 3832393 = 2874295) B2874295
theorem B5109857 : Blo 2269435 5109857 := bstep (se 2 (by rfl) ⟨1916196, by rfl⟩ : syracuseStep 5109857 = 3832393) B3832393
theorem B3406571 : Blo 2269435 3406571 := bstep (se 1 (by rfl) ⟨2554928, by rfl⟩ : syracuseStep 3406571 = 5109857) B5109857
theorem B2271047 : Blo 2269435 2271047 := bstep (se 1 (by rfl) ⟨1703285, by rfl⟩ : syracuseStep 2271047 = 3406571) B3406571
theorem B2554933 : Blo 2269435 2554933 := bbase (se 5 (by rfl) ⟨119762, by rfl⟩ : syracuseStep 2554933 = 239525) (by norm_num)
theorem B3406577 : Blo 2269435 3406577 := bstep (se 2 (by rfl) ⟨1277466, by rfl⟩ : syracuseStep 3406577 = 2554933) B2554933
theorem B2271051 : Blo 2269435 2271051 := bstep (se 1 (by rfl) ⟨1703288, by rfl⟩ : syracuseStep 2271051 = 3406577) B3406577
theorem B2874305 : Blo 2269435 2874305 := bbase (se 2 (by rfl) ⟨1077864, by rfl⟩ : syracuseStep 2874305 = 2155729) (by norm_num)
theorem B7664813 : Blo 2269435 7664813 := bstep (se 3 (by rfl) ⟨1437152, by rfl⟩ : syracuseStep 7664813 = 2874305) B2874305
theorem B5109875 : Blo 2269435 5109875 := bstep (se 1 (by rfl) ⟨3832406, by rfl⟩ : syracuseStep 5109875 = 7664813) B7664813
theorem B3406583 : Blo 2269435 3406583 := bstep (se 1 (by rfl) ⟨2554937, by rfl⟩ : syracuseStep 3406583 = 5109875) B5109875
theorem B2271055 : Blo 2269435 2271055 := bstep (se 1 (by rfl) ⟨1703291, by rfl⟩ : syracuseStep 2271055 = 3406583) B3406583
theorem B3406589 : Blo 2269435 3406589 := bbase (se 3 (by rfl) ⟨638735, by rfl⟩ : syracuseStep 3406589 = 1277471) (by norm_num)
theorem B2271059 : Blo 2269435 2271059 := bstep (se 1 (by rfl) ⟨1703294, by rfl⟩ : syracuseStep 2271059 = 3406589) B3406589
theorem B5109893 : Blo 2269435 5109893 := bbase (se 4 (by rfl) ⟨479052, by rfl⟩ : syracuseStep 5109893 = 958105) (by norm_num)
theorem B3406595 : Blo 2269435 3406595 := bstep (se 1 (by rfl) ⟨2554946, by rfl⟩ : syracuseStep 3406595 = 5109893) B5109893
theorem B2271063 : Blo 2269435 2271063 := bstep (se 1 (by rfl) ⟨1703297, by rfl⟩ : syracuseStep 2271063 = 3406595) B3406595
theorem B3637813 : Blo 2269435 3637813 := bbase (se 5 (by rfl) ⟨170522, by rfl⟩ : syracuseStep 3637813 = 341045) (by norm_num)
theorem B4850417 : Blo 2269435 4850417 := bstep (se 2 (by rfl) ⟨1818906, by rfl⟩ : syracuseStep 4850417 = 3637813) B3637813
theorem B3233611 : Blo 2269435 3233611 := bstep (se 1 (by rfl) ⟨2425208, by rfl⟩ : syracuseStep 3233611 = 4850417) B4850417
theorem B4311481 : Blo 2269435 4311481 := bstep (se 2 (by rfl) ⟨1616805, by rfl⟩ : syracuseStep 4311481 = 3233611) B3233611
theorem B5748641 : Blo 2269435 5748641 := bstep (se 2 (by rfl) ⟨2155740, by rfl⟩ : syracuseStep 5748641 = 4311481) B4311481
theorem B3832427 : Blo 2269435 3832427 := bstep (se 1 (by rfl) ⟨2874320, by rfl⟩ : syracuseStep 3832427 = 5748641) B5748641
theorem B2554951 : Blo 2269435 2554951 := bstep (se 1 (by rfl) ⟨1916213, by rfl⟩ : syracuseStep 2554951 = 3832427) B3832427
theorem B3406601 : Blo 2269435 3406601 := bstep (se 2 (by rfl) ⟨1277475, by rfl⟩ : syracuseStep 3406601 = 2554951) B2554951
theorem B2271067 : Blo 2269435 2271067 := bstep (se 1 (by rfl) ⟨1703300, by rfl⟩ : syracuseStep 2271067 = 3406601) B3406601
theorem B11497301 : Blo 2269435 11497301 := bbase (se 9 (by rfl) ⟨33683, by rfl⟩ : syracuseStep 11497301 = 67367) (by norm_num)
theorem B7664867 : Blo 2269435 7664867 := bstep (se 1 (by rfl) ⟨5748650, by rfl⟩ : syracuseStep 7664867 = 11497301) B11497301
theorem B5109911 : Blo 2269435 5109911 := bstep (se 1 (by rfl) ⟨3832433, by rfl⟩ : syracuseStep 5109911 = 7664867) B7664867
theorem B3406607 : Blo 2269435 3406607 := bstep (se 1 (by rfl) ⟨2554955, by rfl⟩ : syracuseStep 3406607 = 5109911) B5109911
theorem B2271071 : Blo 2269435 2271071 := bstep (se 1 (by rfl) ⟨1703303, by rfl⟩ : syracuseStep 2271071 = 3406607) B3406607
theorem B3406613 : Blo 2269435 3406613 := bbase (se 6 (by rfl) ⟨79842, by rfl⟩ : syracuseStep 3406613 = 159685) (by norm_num)
theorem B2271075 : Blo 2269435 2271075 := bstep (se 1 (by rfl) ⟨1703306, by rfl⟩ : syracuseStep 2271075 = 3406613) B3406613
theorem B9208261 : Blo 2269435 9208261 := bbase (se 4 (by rfl) ⟨863274, by rfl⟩ : syracuseStep 9208261 = 1726549) (by norm_num)
theorem B49110725 : Blo 2269435 49110725 := bstep (se 4 (by rfl) ⟨4604130, by rfl⟩ : syracuseStep 49110725 = 9208261) B9208261
theorem B32740483 : Blo 2269435 32740483 := bstep (se 1 (by rfl) ⟨24555362, by rfl⟩ : syracuseStep 32740483 = 49110725) B49110725
theorem B43653977 : Blo 2269435 43653977 := bstep (se 2 (by rfl) ⟨16370241, by rfl⟩ : syracuseStep 43653977 = 32740483) B32740483
theorem B29102651 : Blo 2269435 29102651 := bstep (se 1 (by rfl) ⟨21826988, by rfl⟩ : syracuseStep 29102651 = 43653977) B43653977
theorem B19401767 : Blo 2269435 19401767 := bstep (se 1 (by rfl) ⟨14551325, by rfl⟩ : syracuseStep 19401767 = 29102651) B29102651
theorem B12934511 : Blo 2269435 12934511 := bstep (se 1 (by rfl) ⟨9700883, by rfl⟩ : syracuseStep 12934511 = 19401767) B19401767
theorem B8623007 : Blo 2269435 8623007 := bstep (se 1 (by rfl) ⟨6467255, by rfl⟩ : syracuseStep 8623007 = 12934511) B12934511
theorem B5748671 : Blo 2269435 5748671 := bstep (se 1 (by rfl) ⟨4311503, by rfl⟩ : syracuseStep 5748671 = 8623007) B8623007
theorem B3832447 : Blo 2269435 3832447 := bstep (se 1 (by rfl) ⟨2874335, by rfl⟩ : syracuseStep 3832447 = 5748671) B5748671
theorem B5109929 : Blo 2269435 5109929 := bstep (se 2 (by rfl) ⟨1916223, by rfl⟩ : syracuseStep 5109929 = 3832447) B3832447
theorem B3406619 : Blo 2269435 3406619 := bstep (se 1 (by rfl) ⟨2554964, by rfl⟩ : syracuseStep 3406619 = 5109929) B5109929
theorem B2271079 : Blo 2269435 2271079 := bstep (se 1 (by rfl) ⟨1703309, by rfl⟩ : syracuseStep 2271079 = 3406619) B3406619
theorem B2554969 : Blo 2269435 2554969 := bbase (se 2 (by rfl) ⟨958113, by rfl⟩ : syracuseStep 2554969 = 1916227) (by norm_num)
theorem B3406625 : Blo 2269435 3406625 := bstep (se 2 (by rfl) ⟨1277484, by rfl⟩ : syracuseStep 3406625 = 2554969) B2554969
theorem B2271083 : Blo 2269435 2271083 := bstep (se 1 (by rfl) ⟨1703312, by rfl⟩ : syracuseStep 2271083 = 3406625) B3406625
theorem B79739477 : Blo 2269435 79739477 := bbase (se 8 (by rfl) ⟨467223, by rfl⟩ : syracuseStep 79739477 = 934447) (by norm_num)
theorem B53159651 : Blo 2269435 53159651 := bstep (se 1 (by rfl) ⟨39869738, by rfl⟩ : syracuseStep 53159651 = 79739477) B79739477
theorem B35439767 : Blo 2269435 35439767 := bstep (se 1 (by rfl) ⟨26579825, by rfl⟩ : syracuseStep 35439767 = 53159651) B53159651
theorem B23626511 : Blo 2269435 23626511 := bstep (se 1 (by rfl) ⟨17719883, by rfl⟩ : syracuseStep 23626511 = 35439767) B35439767
theorem B15751007 : Blo 2269435 15751007 := bstep (se 1 (by rfl) ⟨11813255, by rfl⟩ : syracuseStep 15751007 = 23626511) B23626511
theorem B10500671 : Blo 2269435 10500671 := bstep (se 1 (by rfl) ⟨7875503, by rfl⟩ : syracuseStep 10500671 = 15751007) B15751007
theorem B7000447 : Blo 2269435 7000447 := bstep (se 1 (by rfl) ⟨5250335, by rfl⟩ : syracuseStep 7000447 = 10500671) B10500671
theorem B9333929 : Blo 2269435 9333929 := bstep (se 2 (by rfl) ⟨3500223, by rfl⟩ : syracuseStep 9333929 = 7000447) B7000447
theorem B6222619 : Blo 2269435 6222619 := bstep (se 1 (by rfl) ⟨4666964, by rfl⟩ : syracuseStep 6222619 = 9333929) B9333929
theorem B8296825 : Blo 2269435 8296825 := bstep (se 2 (by rfl) ⟨3111309, by rfl⟩ : syracuseStep 8296825 = 6222619) B6222619
theorem B11062433 : Blo 2269435 11062433 := bstep (se 2 (by rfl) ⟨4148412, by rfl⟩ : syracuseStep 11062433 = 8296825) B8296825
theorem B29499821 : Blo 2269435 29499821 := bstep (se 3 (by rfl) ⟨5531216, by rfl⟩ : syracuseStep 29499821 = 11062433) B11062433
theorem B19666547 : Blo 2269435 19666547 := bstep (se 1 (by rfl) ⟨14749910, by rfl⟩ : syracuseStep 19666547 = 29499821) B29499821
theorem B13111031 : Blo 2269435 13111031 := bstep (se 1 (by rfl) ⟨9833273, by rfl⟩ : syracuseStep 13111031 = 19666547) B19666547
theorem B34962749 : Blo 2269435 34962749 := bstep (se 3 (by rfl) ⟨6555515, by rfl⟩ : syracuseStep 34962749 = 13111031) B13111031
theorem B23308499 : Blo 2269435 23308499 := bstep (se 1 (by rfl) ⟨17481374, by rfl⟩ : syracuseStep 23308499 = 34962749) B34962749
theorem B62155997 : Blo 2269435 62155997 := bstep (se 3 (by rfl) ⟨11654249, by rfl⟩ : syracuseStep 62155997 = 23308499) B23308499
theorem B41437331 : Blo 2269435 41437331 := bstep (se 1 (by rfl) ⟨31077998, by rfl⟩ : syracuseStep 41437331 = 62155997) B62155997
theorem B27624887 : Blo 2269435 27624887 := bstep (se 1 (by rfl) ⟨20718665, by rfl⟩ : syracuseStep 27624887 = 41437331) B41437331
theorem B18416591 : Blo 2269435 18416591 := bstep (se 1 (by rfl) ⟨13812443, by rfl⟩ : syracuseStep 18416591 = 27624887) B27624887
theorem B12277727 : Blo 2269435 12277727 := bstep (se 1 (by rfl) ⟨9208295, by rfl⟩ : syracuseStep 12277727 = 18416591) B18416591
theorem B8185151 : Blo 2269435 8185151 := bstep (se 1 (by rfl) ⟨6138863, by rfl⟩ : syracuseStep 8185151 = 12277727) B12277727
theorem B5456767 : Blo 2269435 5456767 := bstep (se 1 (by rfl) ⟨4092575, by rfl⟩ : syracuseStep 5456767 = 8185151) B8185151
theorem B7275689 : Blo 2269435 7275689 := bstep (se 2 (by rfl) ⟨2728383, by rfl⟩ : syracuseStep 7275689 = 5456767) B5456767
theorem B4850459 : Blo 2269435 4850459 := bstep (se 1 (by rfl) ⟨3637844, by rfl⟩ : syracuseStep 4850459 = 7275689) B7275689
theorem B3233639 : Blo 2269435 3233639 := bstep (se 1 (by rfl) ⟨2425229, by rfl⟩ : syracuseStep 3233639 = 4850459) B4850459
theorem B8623037 : Blo 2269435 8623037 := bstep (se 3 (by rfl) ⟨1616819, by rfl⟩ : syracuseStep 8623037 = 3233639) B3233639
theorem B5748691 : Blo 2269435 5748691 := bstep (se 1 (by rfl) ⟨4311518, by rfl⟩ : syracuseStep 5748691 = 8623037) B8623037
theorem B7664921 : Blo 2269435 7664921 := bstep (se 2 (by rfl) ⟨2874345, by rfl⟩ : syracuseStep 7664921 = 5748691) B5748691
theorem B5109947 : Blo 2269435 5109947 := bstep (se 1 (by rfl) ⟨3832460, by rfl⟩ : syracuseStep 5109947 = 7664921) B7664921
theorem B3406631 : Blo 2269435 3406631 := bstep (se 1 (by rfl) ⟨2554973, by rfl⟩ : syracuseStep 3406631 = 5109947) B5109947
theorem B2271087 : Blo 2269435 2271087 := bstep (se 1 (by rfl) ⟨1703315, by rfl⟩ : syracuseStep 2271087 = 3406631) B3406631
theorem B3406637 : Blo 2269435 3406637 := bbase (se 3 (by rfl) ⟨638744, by rfl⟩ : syracuseStep 3406637 = 1277489) (by norm_num)
theorem B2271091 : Blo 2269435 2271091 := bstep (se 1 (by rfl) ⟨1703318, by rfl⟩ : syracuseStep 2271091 = 3406637) B3406637
theorem B5109965 : Blo 2269435 5109965 := bbase (se 3 (by rfl) ⟨958118, by rfl⟩ : syracuseStep 5109965 = 1916237) (by norm_num)
theorem B3406643 : Blo 2269435 3406643 := bstep (se 1 (by rfl) ⟨2554982, by rfl⟩ : syracuseStep 3406643 = 5109965) B5109965
theorem B2271095 : Blo 2269435 2271095 := bstep (se 1 (by rfl) ⟨1703321, by rfl⟩ : syracuseStep 2271095 = 3406643) B3406643
theorem B2874361 : Blo 2269435 2874361 := bbase (se 2 (by rfl) ⟨1077885, by rfl⟩ : syracuseStep 2874361 = 2155771) (by norm_num)
theorem B3832481 : Blo 2269435 3832481 := bstep (se 2 (by rfl) ⟨1437180, by rfl⟩ : syracuseStep 3832481 = 2874361) B2874361
theorem B2554987 : Blo 2269435 2554987 := bstep (se 1 (by rfl) ⟨1916240, by rfl⟩ : syracuseStep 2554987 = 3832481) B3832481
theorem B3406649 : Blo 2269435 3406649 := bstep (se 2 (by rfl) ⟨1277493, by rfl⟩ : syracuseStep 3406649 = 2554987) B2554987
theorem B2271099 : Blo 2269435 2271099 := bstep (se 1 (by rfl) ⟨1703324, by rfl⟩ : syracuseStep 2271099 = 3406649) B3406649
theorem B3937781 : Blo 2269435 3937781 := bbase (se 5 (by rfl) ⟨184583, by rfl⟩ : syracuseStep 3937781 = 369167) (by norm_num)
theorem B10500749 : Blo 2269435 10500749 := bstep (se 3 (by rfl) ⟨1968890, by rfl⟩ : syracuseStep 10500749 = 3937781) B3937781
theorem B7000499 : Blo 2269435 7000499 := bstep (se 1 (by rfl) ⟨5250374, by rfl⟩ : syracuseStep 7000499 = 10500749) B10500749
theorem B4666999 : Blo 2269435 4666999 := bstep (se 1 (by rfl) ⟨3500249, by rfl⟩ : syracuseStep 4666999 = 7000499) B7000499
theorem B6222665 : Blo 2269435 6222665 := bstep (se 2 (by rfl) ⟨2333499, by rfl⟩ : syracuseStep 6222665 = 4666999) B4666999
theorem B4148443 : Blo 2269435 4148443 := bstep (se 1 (by rfl) ⟨3111332, by rfl⟩ : syracuseStep 4148443 = 6222665) B6222665
theorem B5531257 : Blo 2269435 5531257 := bstep (se 2 (by rfl) ⟨2074221, by rfl⟩ : syracuseStep 5531257 = 4148443) B4148443
theorem B7375009 : Blo 2269435 7375009 := bstep (se 2 (by rfl) ⟨2765628, by rfl⟩ : syracuseStep 7375009 = 5531257) B5531257
theorem B9833345 : Blo 2269435 9833345 := bstep (se 2 (by rfl) ⟨3687504, by rfl⟩ : syracuseStep 9833345 = 7375009) B7375009
theorem B6555563 : Blo 2269435 6555563 := bstep (se 1 (by rfl) ⟨4916672, by rfl⟩ : syracuseStep 6555563 = 9833345) B9833345
theorem B4370375 : Blo 2269435 4370375 := bstep (se 1 (by rfl) ⟨3277781, by rfl⟩ : syracuseStep 4370375 = 6555563) B6555563
theorem B2913583 : Blo 2269435 2913583 := bstep (se 1 (by rfl) ⟨2185187, by rfl⟩ : syracuseStep 2913583 = 4370375) B4370375
theorem B3884777 : Blo 2269435 3884777 := bstep (se 2 (by rfl) ⟨1456791, by rfl⟩ : syracuseStep 3884777 = 2913583) B2913583
theorem B2589851 : Blo 2269435 2589851 := bstep (se 1 (by rfl) ⟨1942388, by rfl⟩ : syracuseStep 2589851 = 3884777) B3884777
theorem B6906269 : Blo 2269435 6906269 := bstep (se 3 (by rfl) ⟨1294925, by rfl⟩ : syracuseStep 6906269 = 2589851) B2589851
theorem B18416717 : Blo 2269435 18416717 := bstep (se 3 (by rfl) ⟨3453134, by rfl⟩ : syracuseStep 18416717 = 6906269) B6906269
theorem B12277811 : Blo 2269435 12277811 := bstep (se 1 (by rfl) ⟨9208358, by rfl⟩ : syracuseStep 12277811 = 18416717) B18416717
theorem B8185207 : Blo 2269435 8185207 := bstep (se 1 (by rfl) ⟨6138905, by rfl⟩ : syracuseStep 8185207 = 12277811) B12277811
theorem B10913609 : Blo 2269435 10913609 := bstep (se 2 (by rfl) ⟨4092603, by rfl⟩ : syracuseStep 10913609 = 8185207) B8185207
theorem B7275739 : Blo 2269435 7275739 := bstep (se 1 (by rfl) ⟨5456804, by rfl⟩ : syracuseStep 7275739 = 10913609) B10913609
theorem B9700985 : Blo 2269435 9700985 := bstep (se 2 (by rfl) ⟨3637869, by rfl⟩ : syracuseStep 9700985 = 7275739) B7275739
theorem B25869293 : Blo 2269435 25869293 := bstep (se 3 (by rfl) ⟨4850492, by rfl⟩ : syracuseStep 25869293 = 9700985) B9700985
theorem B17246195 : Blo 2269435 17246195 := bstep (se 1 (by rfl) ⟨12934646, by rfl⟩ : syracuseStep 17246195 = 25869293) B25869293
theorem B11497463 : Blo 2269435 11497463 := bstep (se 1 (by rfl) ⟨8623097, by rfl⟩ : syracuseStep 11497463 = 17246195) B17246195
theorem B7664975 : Blo 2269435 7664975 := bstep (se 1 (by rfl) ⟨5748731, by rfl⟩ : syracuseStep 7664975 = 11497463) B11497463
theorem B5109983 : Blo 2269435 5109983 := bstep (se 1 (by rfl) ⟨3832487, by rfl⟩ : syracuseStep 5109983 = 7664975) B7664975
theorem B3406655 : Blo 2269435 3406655 := bstep (se 1 (by rfl) ⟨2554991, by rfl⟩ : syracuseStep 3406655 = 5109983) B5109983
theorem B2271103 : Blo 2269435 2271103 := bstep (se 1 (by rfl) ⟨1703327, by rfl⟩ : syracuseStep 2271103 = 3406655) B3406655
theorem B3406661 : Blo 2269435 3406661 := bbase (se 4 (by rfl) ⟨319374, by rfl⟩ : syracuseStep 3406661 = 638749) (by norm_num)
theorem B2271107 : Blo 2269435 2271107 := bstep (se 1 (by rfl) ⟨1703330, by rfl⟩ : syracuseStep 2271107 = 3406661) B3406661
theorem B3832501 : Blo 2269435 3832501 := bbase (se 5 (by rfl) ⟨179648, by rfl⟩ : syracuseStep 3832501 = 359297) (by norm_num)
theorem B5110001 : Blo 2269435 5110001 := bstep (se 2 (by rfl) ⟨1916250, by rfl⟩ : syracuseStep 5110001 = 3832501) B3832501
theorem B3406667 : Blo 2269435 3406667 := bstep (se 1 (by rfl) ⟨2555000, by rfl⟩ : syracuseStep 3406667 = 5110001) B5110001
theorem B2271111 : Blo 2269435 2271111 := bstep (se 1 (by rfl) ⟨1703333, by rfl⟩ : syracuseStep 2271111 = 3406667) B3406667
theorem B2555005 : Blo 2269435 2555005 := bbase (se 3 (by rfl) ⟨479063, by rfl⟩ : syracuseStep 2555005 = 958127) (by norm_num)
theorem B3406673 : Blo 2269435 3406673 := bstep (se 2 (by rfl) ⟨1277502, by rfl⟩ : syracuseStep 3406673 = 2555005) B2555005
theorem B2271115 : Blo 2269435 2271115 := bstep (se 1 (by rfl) ⟨1703336, by rfl⟩ : syracuseStep 2271115 = 3406673) B3406673
theorem B7665029 : Blo 2269435 7665029 := bbase (se 4 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 7665029 = 1437193) (by norm_num)
theorem B5110019 : Blo 2269435 5110019 := bstep (se 1 (by rfl) ⟨3832514, by rfl⟩ : syracuseStep 5110019 = 7665029) B7665029
theorem B3406679 : Blo 2269435 3406679 := bstep (se 1 (by rfl) ⟨2555009, by rfl⟩ : syracuseStep 3406679 = 5110019) B5110019
theorem B2271119 : Blo 2269435 2271119 := bstep (se 1 (by rfl) ⟨1703339, by rfl⟩ : syracuseStep 2271119 = 3406679) B3406679
theorem B3406685 : Blo 2269435 3406685 := bbase (se 3 (by rfl) ⟨638753, by rfl⟩ : syracuseStep 3406685 = 1277507) (by norm_num)
theorem B2271123 : Blo 2269435 2271123 := bstep (se 1 (by rfl) ⟨1703342, by rfl⟩ : syracuseStep 2271123 = 3406685) B3406685
theorem B5110037 : Blo 2269435 5110037 := bbase (se 6 (by rfl) ⟨119766, by rfl⟩ : syracuseStep 5110037 = 239533) (by norm_num)
theorem B3406691 : Blo 2269435 3406691 := bstep (se 1 (by rfl) ⟨2555018, by rfl⟩ : syracuseStep 3406691 = 5110037) B5110037
theorem B2271127 : Blo 2269435 2271127 := bstep (se 1 (by rfl) ⟨1703345, by rfl⟩ : syracuseStep 2271127 = 3406691) B3406691
theorem B8623205 : Blo 2269435 8623205 := bbase (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) (by norm_num)
theorem B5748803 : Blo 2269435 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B3832535 : Blo 2269435 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B2555023 : Blo 2269435 2555023 := bstep (se 1 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 2555023 = 3832535) B3832535
theorem B3406697 : Blo 2269435 3406697 := bstep (se 2 (by rfl) ⟨1277511, by rfl⟩ : syracuseStep 3406697 = 2555023) B2555023
theorem B2271131 : Blo 2269435 2271131 := bstep (se 1 (by rfl) ⟨1703348, by rfl⟩ : syracuseStep 2271131 = 3406697) B3406697
theorem B2728441 : Blo 2269435 2728441 := bbase (se 2 (by rfl) ⟨1023165, by rfl⟩ : syracuseStep 2728441 = 2046331) (by norm_num)
theorem B3637921 : Blo 2269435 3637921 := bstep (se 2 (by rfl) ⟨1364220, by rfl⟩ : syracuseStep 3637921 = 2728441) B2728441
theorem B4850561 : Blo 2269435 4850561 := bstep (se 2 (by rfl) ⟨1818960, by rfl⟩ : syracuseStep 4850561 = 3637921) B3637921
theorem B12934829 : Blo 2269435 12934829 := bstep (se 3 (by rfl) ⟨2425280, by rfl⟩ : syracuseStep 12934829 = 4850561) B4850561
theorem B8623219 : Blo 2269435 8623219 := bstep (se 1 (by rfl) ⟨6467414, by rfl⟩ : syracuseStep 8623219 = 12934829) B12934829
theorem B11497625 : Blo 2269435 11497625 := bstep (se 2 (by rfl) ⟨4311609, by rfl⟩ : syracuseStep 11497625 = 8623219) B8623219
theorem B7665083 : Blo 2269435 7665083 := bstep (se 1 (by rfl) ⟨5748812, by rfl⟩ : syracuseStep 7665083 = 11497625) B11497625
theorem B5110055 : Blo 2269435 5110055 := bstep (se 1 (by rfl) ⟨3832541, by rfl⟩ : syracuseStep 5110055 = 7665083) B7665083
theorem B3406703 : Blo 2269435 3406703 := bstep (se 1 (by rfl) ⟨2555027, by rfl⟩ : syracuseStep 3406703 = 5110055) B5110055
theorem B2271135 : Blo 2269435 2271135 := bstep (se 1 (by rfl) ⟨1703351, by rfl⟩ : syracuseStep 2271135 = 3406703) B3406703
theorem B3406709 : Blo 2269435 3406709 := bbase (se 5 (by rfl) ⟨159689, by rfl⟩ : syracuseStep 3406709 = 319379) (by norm_num)
theorem B2271139 : Blo 2269435 2271139 := bstep (se 1 (by rfl) ⟨1703354, by rfl⟩ : syracuseStep 2271139 = 3406709) B3406709
theorem B4092677 : Blo 2269435 4092677 := bbase (se 4 (by rfl) ⟨383688, by rfl⟩ : syracuseStep 4092677 = 767377) (by norm_num)
theorem B2728451 : Blo 2269435 2728451 := bstep (se 1 (by rfl) ⟨2046338, by rfl⟩ : syracuseStep 2728451 = 4092677) B4092677
theorem B7275869 : Blo 2269435 7275869 := bstep (se 3 (by rfl) ⟨1364225, by rfl⟩ : syracuseStep 7275869 = 2728451) B2728451
theorem B4850579 : Blo 2269435 4850579 := bstep (se 1 (by rfl) ⟨3637934, by rfl⟩ : syracuseStep 4850579 = 7275869) B7275869
theorem B3233719 : Blo 2269435 3233719 := bstep (se 1 (by rfl) ⟨2425289, by rfl⟩ : syracuseStep 3233719 = 4850579) B4850579
theorem B4311625 : Blo 2269435 4311625 := bstep (se 2 (by rfl) ⟨1616859, by rfl⟩ : syracuseStep 4311625 = 3233719) B3233719
theorem B5748833 : Blo 2269435 5748833 := bstep (se 2 (by rfl) ⟨2155812, by rfl⟩ : syracuseStep 5748833 = 4311625) B4311625
theorem B3832555 : Blo 2269435 3832555 := bstep (se 1 (by rfl) ⟨2874416, by rfl⟩ : syracuseStep 3832555 = 5748833) B5748833
theorem B5110073 : Blo 2269435 5110073 := bstep (se 2 (by rfl) ⟨1916277, by rfl⟩ : syracuseStep 5110073 = 3832555) B3832555
theorem B3406715 : Blo 2269435 3406715 := bstep (se 1 (by rfl) ⟨2555036, by rfl⟩ : syracuseStep 3406715 = 5110073) B5110073
theorem B2271143 : Blo 2269435 2271143 := bstep (se 1 (by rfl) ⟨1703357, by rfl⟩ : syracuseStep 2271143 = 3406715) B3406715
theorem B2555041 : Blo 2269435 2555041 := bbase (se 2 (by rfl) ⟨958140, by rfl⟩ : syracuseStep 2555041 = 1916281) (by norm_num)
theorem B3406721 : Blo 2269435 3406721 := bstep (se 2 (by rfl) ⟨1277520, by rfl⟩ : syracuseStep 3406721 = 2555041) B2555041
theorem B2271147 : Blo 2269435 2271147 := bstep (se 1 (by rfl) ⟨1703360, by rfl⟩ : syracuseStep 2271147 = 3406721) B3406721
theorem B5748853 : Blo 2269435 5748853 := bbase (se 5 (by rfl) ⟨269477, by rfl⟩ : syracuseStep 5748853 = 538955) (by norm_num)
theorem B7665137 : Blo 2269435 7665137 := bstep (se 2 (by rfl) ⟨2874426, by rfl⟩ : syracuseStep 7665137 = 5748853) B5748853
theorem B5110091 : Blo 2269435 5110091 := bstep (se 1 (by rfl) ⟨3832568, by rfl⟩ : syracuseStep 5110091 = 7665137) B7665137
theorem B3406727 : Blo 2269435 3406727 := bstep (se 1 (by rfl) ⟨2555045, by rfl⟩ : syracuseStep 3406727 = 5110091) B5110091
theorem B2271151 : Blo 2269435 2271151 := bstep (se 1 (by rfl) ⟨1703363, by rfl⟩ : syracuseStep 2271151 = 3406727) B3406727
theorem B3406733 : Blo 2269435 3406733 := bbase (se 3 (by rfl) ⟨638762, by rfl⟩ : syracuseStep 3406733 = 1277525) (by norm_num)
theorem B2271155 : Blo 2269435 2271155 := bstep (se 1 (by rfl) ⟨1703366, by rfl⟩ : syracuseStep 2271155 = 3406733) B3406733
theorem B5110109 : Blo 2269435 5110109 := bbase (se 3 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 5110109 = 1916291) (by norm_num)
theorem B3406739 : Blo 2269435 3406739 := bstep (se 1 (by rfl) ⟨2555054, by rfl⟩ : syracuseStep 3406739 = 5110109) B5110109
theorem B2271159 : Blo 2269435 2271159 := bstep (se 1 (by rfl) ⟨1703369, by rfl⟩ : syracuseStep 2271159 = 3406739) B3406739
theorem B3832589 : Blo 2269435 3832589 := bbase (se 3 (by rfl) ⟨718610, by rfl⟩ : syracuseStep 3832589 = 1437221) (by norm_num)
theorem B2555059 : Blo 2269435 2555059 := bstep (se 1 (by rfl) ⟨1916294, by rfl⟩ : syracuseStep 2555059 = 3832589) B3832589
theorem B3406745 : Blo 2269435 3406745 := bstep (se 2 (by rfl) ⟨1277529, by rfl⟩ : syracuseStep 3406745 = 2555059) B2555059
theorem B2271163 : Blo 2269435 2271163 := bstep (se 1 (by rfl) ⟨1703372, by rfl⟩ : syracuseStep 2271163 = 3406745) B3406745
theorem B19402517 : Blo 2269435 19402517 := bbase (se 6 (by rfl) ⟨454746, by rfl⟩ : syracuseStep 19402517 = 909493) (by norm_num)
theorem B12935011 : Blo 2269435 12935011 := bstep (se 1 (by rfl) ⟨9701258, by rfl⟩ : syracuseStep 12935011 = 19402517) B19402517
theorem B17246681 : Blo 2269435 17246681 := bstep (se 2 (by rfl) ⟨6467505, by rfl⟩ : syracuseStep 17246681 = 12935011) B12935011
theorem B11497787 : Blo 2269435 11497787 := bstep (se 1 (by rfl) ⟨8623340, by rfl⟩ : syracuseStep 11497787 = 17246681) B17246681
theorem B7665191 : Blo 2269435 7665191 := bstep (se 1 (by rfl) ⟨5748893, by rfl⟩ : syracuseStep 7665191 = 11497787) B11497787
theorem B5110127 : Blo 2269435 5110127 := bstep (se 1 (by rfl) ⟨3832595, by rfl⟩ : syracuseStep 5110127 = 7665191) B7665191
theorem B3406751 : Blo 2269435 3406751 := bstep (se 1 (by rfl) ⟨2555063, by rfl⟩ : syracuseStep 3406751 = 5110127) B5110127
theorem B2271167 : Blo 2269435 2271167 := bstep (se 1 (by rfl) ⟨1703375, by rfl⟩ : syracuseStep 2271167 = 3406751) B3406751
theorem B3406757 : Blo 2269435 3406757 := bbase (se 4 (by rfl) ⟨319383, by rfl⟩ : syracuseStep 3406757 = 638767) (by norm_num)
theorem B2271171 : Blo 2269435 2271171 := bstep (se 1 (by rfl) ⟨1703378, by rfl⟩ : syracuseStep 2271171 = 3406757) B3406757
theorem B2874457 : Blo 2269435 2874457 := bbase (se 2 (by rfl) ⟨1077921, by rfl⟩ : syracuseStep 2874457 = 2155843) (by norm_num)
theorem B3832609 : Blo 2269435 3832609 := bstep (se 2 (by rfl) ⟨1437228, by rfl⟩ : syracuseStep 3832609 = 2874457) B2874457
theorem B5110145 : Blo 2269435 5110145 := bstep (se 2 (by rfl) ⟨1916304, by rfl⟩ : syracuseStep 5110145 = 3832609) B3832609
theorem B3406763 : Blo 2269435 3406763 := bstep (se 1 (by rfl) ⟨2555072, by rfl⟩ : syracuseStep 3406763 = 5110145) B5110145
theorem B2271175 : Blo 2269435 2271175 := bstep (se 1 (by rfl) ⟨1703381, by rfl⟩ : syracuseStep 2271175 = 3406763) B3406763
theorem B2555077 : Blo 2269435 2555077 := bbase (se 4 (by rfl) ⟨239538, by rfl⟩ : syracuseStep 2555077 = 479077) (by norm_num)
theorem B3406769 : Blo 2269435 3406769 := bstep (se 2 (by rfl) ⟨1277538, by rfl⟩ : syracuseStep 3406769 = 2555077) B2555077
theorem B2271179 : Blo 2269435 2271179 := bstep (se 1 (by rfl) ⟨1703384, by rfl⟩ : syracuseStep 2271179 = 3406769) B3406769
theorem B4311701 : Blo 2269435 4311701 := bbase (se 6 (by rfl) ⟨101055, by rfl⟩ : syracuseStep 4311701 = 202111) (by norm_num)
theorem B2874467 : Blo 2269435 2874467 := bstep (se 1 (by rfl) ⟨2155850, by rfl⟩ : syracuseStep 2874467 = 4311701) B4311701
theorem B7665245 : Blo 2269435 7665245 := bstep (se 3 (by rfl) ⟨1437233, by rfl⟩ : syracuseStep 7665245 = 2874467) B2874467
theorem B5110163 : Blo 2269435 5110163 := bstep (se 1 (by rfl) ⟨3832622, by rfl⟩ : syracuseStep 5110163 = 7665245) B7665245
theorem B3406775 : Blo 2269435 3406775 := bstep (se 1 (by rfl) ⟨2555081, by rfl⟩ : syracuseStep 3406775 = 5110163) B5110163
theorem B2271183 : Blo 2269435 2271183 := bstep (se 1 (by rfl) ⟨1703387, by rfl⟩ : syracuseStep 2271183 = 3406775) B3406775
theorem B3406781 : Blo 2269435 3406781 := bbase (se 3 (by rfl) ⟨638771, by rfl⟩ : syracuseStep 3406781 = 1277543) (by norm_num)
theorem B2271187 : Blo 2269435 2271187 := bstep (se 1 (by rfl) ⟨1703390, by rfl⟩ : syracuseStep 2271187 = 3406781) B3406781
theorem B5110181 : Blo 2269435 5110181 := bbase (se 4 (by rfl) ⟨479079, by rfl⟩ : syracuseStep 5110181 = 958159) (by norm_num)
theorem B3406787 : Blo 2269435 3406787 := bstep (se 1 (by rfl) ⟨2555090, by rfl⟩ : syracuseStep 3406787 = 5110181) B5110181
theorem B2271191 : Blo 2269435 2271191 := bstep (se 1 (by rfl) ⟨1703393, by rfl⟩ : syracuseStep 2271191 = 3406787) B3406787
theorem B5748965 : Blo 2269435 5748965 := bbase (se 4 (by rfl) ⟨538965, by rfl⟩ : syracuseStep 5748965 = 1077931) (by norm_num)
theorem B3832643 : Blo 2269435 3832643 := bstep (se 1 (by rfl) ⟨2874482, by rfl⟩ : syracuseStep 3832643 = 5748965) B5748965
theorem B2555095 : Blo 2269435 2555095 := bstep (se 1 (by rfl) ⟨1916321, by rfl⟩ : syracuseStep 2555095 = 3832643) B3832643
theorem B3406793 : Blo 2269435 3406793 := bstep (se 2 (by rfl) ⟨1277547, by rfl⟩ : syracuseStep 3406793 = 2555095) B2555095
theorem B2271195 : Blo 2269435 2271195 := bstep (se 1 (by rfl) ⟨1703396, by rfl⟩ : syracuseStep 2271195 = 3406793) B3406793
theorem B2425349 : Blo 2269435 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B6467597 : Blo 2269435 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B4311731 : Blo 2269435 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B11497949 : Blo 2269435 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B7665299 : Blo 2269435 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B5110199 : Blo 2269435 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B3406799 : Blo 2269435 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B2271199 : Blo 2269435 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B3406805 : Blo 2269435 3406805 := bbase (se 7 (by rfl) ⟨39923, by rfl⟩ : syracuseStep 3406805 = 79847) (by norm_num)
theorem B2271203 : Blo 2269435 2271203 := bstep (se 1 (by rfl) ⟨1703402, by rfl⟩ : syracuseStep 2271203 = 3406805) B3406805
theorem B8623493 : Blo 2269435 8623493 := bbase (se 4 (by rfl) ⟨808452, by rfl⟩ : syracuseStep 8623493 = 1616905) (by norm_num)
theorem B5748995 : Blo 2269435 5748995 := bstep (se 1 (by rfl) ⟨4311746, by rfl⟩ : syracuseStep 5748995 = 8623493) B8623493
theorem B3832663 : Blo 2269435 3832663 := bstep (se 1 (by rfl) ⟨2874497, by rfl⟩ : syracuseStep 3832663 = 5748995) B5748995
theorem B5110217 : Blo 2269435 5110217 := bstep (se 2 (by rfl) ⟨1916331, by rfl⟩ : syracuseStep 5110217 = 3832663) B3832663
theorem B3406811 : Blo 2269435 3406811 := bstep (se 1 (by rfl) ⟨2555108, by rfl⟩ : syracuseStep 3406811 = 5110217) B5110217
theorem B2271207 : Blo 2269435 2271207 := bstep (se 1 (by rfl) ⟨1703405, by rfl⟩ : syracuseStep 2271207 = 3406811) B3406811
theorem B2555113 : Blo 2269435 2555113 := bbase (se 2 (by rfl) ⟨958167, by rfl⟩ : syracuseStep 2555113 = 1916335) (by norm_num)
theorem B3406817 : Blo 2269435 3406817 := bstep (se 2 (by rfl) ⟨1277556, by rfl⟩ : syracuseStep 3406817 = 2555113) B2555113
theorem B2271211 : Blo 2269435 2271211 := bstep (se 1 (by rfl) ⟨1703408, by rfl⟩ : syracuseStep 2271211 = 3406817) B3406817
theorem B12935285 : Blo 2269435 12935285 := bbase (se 5 (by rfl) ⟨606341, by rfl⟩ : syracuseStep 12935285 = 1212683) (by norm_num)
theorem B8623523 : Blo 2269435 8623523 := bstep (se 1 (by rfl) ⟨6467642, by rfl⟩ : syracuseStep 8623523 = 12935285) B12935285
theorem B5749015 : Blo 2269435 5749015 := bstep (se 1 (by rfl) ⟨4311761, by rfl⟩ : syracuseStep 5749015 = 8623523) B8623523
theorem B7665353 : Blo 2269435 7665353 := bstep (se 2 (by rfl) ⟨2874507, by rfl⟩ : syracuseStep 7665353 = 5749015) B5749015
theorem B5110235 : Blo 2269435 5110235 := bstep (se 1 (by rfl) ⟨3832676, by rfl⟩ : syracuseStep 5110235 = 7665353) B7665353
theorem B3406823 : Blo 2269435 3406823 := bstep (se 1 (by rfl) ⟨2555117, by rfl⟩ : syracuseStep 3406823 = 5110235) B5110235
theorem B2271215 : Blo 2269435 2271215 := bstep (se 1 (by rfl) ⟨1703411, by rfl⟩ : syracuseStep 2271215 = 3406823) B3406823
theorem B3406829 : Blo 2269435 3406829 := bbase (se 3 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 3406829 = 1277561) (by norm_num)
theorem B2271219 : Blo 2269435 2271219 := bstep (se 1 (by rfl) ⟨1703414, by rfl⟩ : syracuseStep 2271219 = 3406829) B3406829
theorem B5110253 : Blo 2269435 5110253 := bbase (se 3 (by rfl) ⟨958172, by rfl⟩ : syracuseStep 5110253 = 1916345) (by norm_num)
theorem B3406835 : Blo 2269435 3406835 := bstep (se 1 (by rfl) ⟨2555126, by rfl⟩ : syracuseStep 3406835 = 5110253) B5110253
theorem B2271223 : Blo 2269435 2271223 := bstep (se 1 (by rfl) ⟨1703417, by rfl⟩ : syracuseStep 2271223 = 3406835) B3406835
theorem B8981381 : Blo 2269435 8981381 := bbase (se 4 (by rfl) ⟨842004, by rfl⟩ : syracuseStep 8981381 = 1684009) (by norm_num)
theorem B23950349 : Blo 2269435 23950349 := bstep (se 3 (by rfl) ⟨4490690, by rfl⟩ : syracuseStep 23950349 = 8981381) B8981381
theorem B15966899 : Blo 2269435 15966899 := bstep (se 1 (by rfl) ⟨11975174, by rfl⟩ : syracuseStep 15966899 = 23950349) B23950349
theorem B10644599 : Blo 2269435 10644599 := bstep (se 1 (by rfl) ⟨7983449, by rfl⟩ : syracuseStep 10644599 = 15966899) B15966899
theorem B28385597 : Blo 2269435 28385597 := bstep (se 3 (by rfl) ⟨5322299, by rfl⟩ : syracuseStep 28385597 = 10644599) B10644599
theorem B75694925 : Blo 2269435 75694925 := bstep (se 3 (by rfl) ⟨14192798, by rfl⟩ : syracuseStep 75694925 = 28385597) B28385597
theorem B50463283 : Blo 2269435 50463283 := bstep (se 1 (by rfl) ⟨37847462, by rfl⟩ : syracuseStep 50463283 = 75694925) B75694925
theorem B67284377 : Blo 2269435 67284377 := bstep (se 2 (by rfl) ⟨25231641, by rfl⟩ : syracuseStep 67284377 = 50463283) B50463283
theorem B44856251 : Blo 2269435 44856251 := bstep (se 1 (by rfl) ⟨33642188, by rfl⟩ : syracuseStep 44856251 = 67284377) B67284377
theorem B29904167 : Blo 2269435 29904167 := bstep (se 1 (by rfl) ⟨22428125, by rfl⟩ : syracuseStep 29904167 = 44856251) B44856251
theorem B79744445 : Blo 2269435 79744445 := bstep (se 3 (by rfl) ⟨14952083, by rfl⟩ : syracuseStep 79744445 = 29904167) B29904167
theorem B53162963 : Blo 2269435 53162963 := bstep (se 1 (by rfl) ⟨39872222, by rfl⟩ : syracuseStep 53162963 = 79744445) B79744445
theorem B35441975 : Blo 2269435 35441975 := bstep (se 1 (by rfl) ⟨26581481, by rfl⟩ : syracuseStep 35441975 = 53162963) B53162963
theorem B23627983 : Blo 2269435 23627983 := bstep (se 1 (by rfl) ⟨17720987, by rfl⟩ : syracuseStep 23627983 = 35441975) B35441975
theorem B31503977 : Blo 2269435 31503977 := bstep (se 2 (by rfl) ⟨11813991, by rfl⟩ : syracuseStep 31503977 = 23627983) B23627983
theorem B21002651 : Blo 2269435 21002651 := bstep (se 1 (by rfl) ⟨15751988, by rfl⟩ : syracuseStep 21002651 = 31503977) B31503977
theorem B14001767 : Blo 2269435 14001767 := bstep (se 1 (by rfl) ⟨10501325, by rfl⟩ : syracuseStep 14001767 = 21002651) B21002651
theorem B9334511 : Blo 2269435 9334511 := bstep (se 1 (by rfl) ⟨7000883, by rfl⟩ : syracuseStep 9334511 = 14001767) B14001767
theorem B6223007 : Blo 2269435 6223007 := bstep (se 1 (by rfl) ⟨4667255, by rfl⟩ : syracuseStep 6223007 = 9334511) B9334511
theorem B4148671 : Blo 2269435 4148671 := bstep (se 1 (by rfl) ⟨3111503, by rfl⟩ : syracuseStep 4148671 = 6223007) B6223007
theorem B5531561 : Blo 2269435 5531561 := bstep (se 2 (by rfl) ⟨2074335, by rfl⟩ : syracuseStep 5531561 = 4148671) B4148671
theorem B3687707 : Blo 2269435 3687707 := bstep (se 1 (by rfl) ⟨2765780, by rfl⟩ : syracuseStep 3687707 = 5531561) B5531561
theorem B9833885 : Blo 2269435 9833885 := bstep (se 3 (by rfl) ⟨1843853, by rfl⟩ : syracuseStep 9833885 = 3687707) B3687707
theorem B6555923 : Blo 2269435 6555923 := bstep (se 1 (by rfl) ⟨4916942, by rfl⟩ : syracuseStep 6555923 = 9833885) B9833885
theorem B4370615 : Blo 2269435 4370615 := bstep (se 1 (by rfl) ⟨3277961, by rfl⟩ : syracuseStep 4370615 = 6555923) B6555923
theorem B2913743 : Blo 2269435 2913743 := bstep (se 1 (by rfl) ⟨2185307, by rfl⟩ : syracuseStep 2913743 = 4370615) B4370615
theorem B7769981 : Blo 2269435 7769981 := bstep (se 3 (by rfl) ⟨1456871, by rfl⟩ : syracuseStep 7769981 = 2913743) B2913743
theorem B5179987 : Blo 2269435 5179987 := bstep (se 1 (by rfl) ⟨3884990, by rfl⟩ : syracuseStep 5179987 = 7769981) B7769981
theorem B6906649 : Blo 2269435 6906649 := bstep (se 2 (by rfl) ⟨2589993, by rfl⟩ : syracuseStep 6906649 = 5179987) B5179987
theorem B9208865 : Blo 2269435 9208865 := bstep (se 2 (by rfl) ⟨3453324, by rfl⟩ : syracuseStep 9208865 = 6906649) B6906649
theorem B6139243 : Blo 2269435 6139243 := bstep (se 1 (by rfl) ⟨4604432, by rfl⟩ : syracuseStep 6139243 = 9208865) B9208865
theorem B8185657 : Blo 2269435 8185657 := bstep (se 2 (by rfl) ⟨3069621, by rfl⟩ : syracuseStep 8185657 = 6139243) B6139243
theorem B10914209 : Blo 2269435 10914209 := bstep (se 2 (by rfl) ⟨4092828, by rfl⟩ : syracuseStep 10914209 = 8185657) B8185657
theorem B7276139 : Blo 2269435 7276139 := bstep (se 1 (by rfl) ⟨5457104, by rfl⟩ : syracuseStep 7276139 = 10914209) B10914209
theorem B4850759 : Blo 2269435 4850759 := bstep (se 1 (by rfl) ⟨3638069, by rfl⟩ : syracuseStep 4850759 = 7276139) B7276139
theorem B3233839 : Blo 2269435 3233839 := bstep (se 1 (by rfl) ⟨2425379, by rfl⟩ : syracuseStep 3233839 = 4850759) B4850759
theorem B4311785 : Blo 2269435 4311785 := bstep (se 2 (by rfl) ⟨1616919, by rfl⟩ : syracuseStep 4311785 = 3233839) B3233839
theorem B2874523 : Blo 2269435 2874523 := bstep (se 1 (by rfl) ⟨2155892, by rfl⟩ : syracuseStep 2874523 = 4311785) B4311785
theorem B3832697 : Blo 2269435 3832697 := bstep (se 2 (by rfl) ⟨1437261, by rfl⟩ : syracuseStep 3832697 = 2874523) B2874523
theorem B2555131 : Blo 2269435 2555131 := bstep (se 1 (by rfl) ⟨1916348, by rfl⟩ : syracuseStep 2555131 = 3832697) B3832697
theorem B3406841 : Blo 2269435 3406841 := bstep (se 2 (by rfl) ⟨1277565, by rfl⟩ : syracuseStep 3406841 = 2555131) B2555131
theorem B2271227 : Blo 2269435 2271227 := bstep (se 1 (by rfl) ⟨1703420, by rfl⟩ : syracuseStep 2271227 = 3406841) B3406841
theorem B31079957 : Blo 2269435 31079957 := bbase (se 6 (by rfl) ⟨728436, by rfl⟩ : syracuseStep 31079957 = 1456873) (by norm_num)
theorem B82879885 : Blo 2269435 82879885 := bstep (se 3 (by rfl) ⟨15539978, by rfl⟩ : syracuseStep 82879885 = 31079957) B31079957
theorem B110506513 : Blo 2269435 110506513 := bstep (se 2 (by rfl) ⟨41439942, by rfl⟩ : syracuseStep 110506513 = 82879885) B82879885
theorem B147342017 : Blo 2269435 147342017 := bstep (se 2 (by rfl) ⟨55253256, by rfl⟩ : syracuseStep 147342017 = 110506513) B110506513
theorem B98228011 : Blo 2269435 98228011 := bstep (se 1 (by rfl) ⟨73671008, by rfl⟩ : syracuseStep 98228011 = 147342017) B147342017
theorem B130970681 : Blo 2269435 130970681 := bstep (se 2 (by rfl) ⟨49114005, by rfl⟩ : syracuseStep 130970681 = 98228011) B98228011
theorem B87313787 : Blo 2269435 87313787 := bstep (se 1 (by rfl) ⟨65485340, by rfl⟩ : syracuseStep 87313787 = 130970681) B130970681
theorem B58209191 : Blo 2269435 58209191 := bstep (se 1 (by rfl) ⟨43656893, by rfl⟩ : syracuseStep 58209191 = 87313787) B87313787
theorem B38806127 : Blo 2269435 38806127 := bstep (se 1 (by rfl) ⟨29104595, by rfl⟩ : syracuseStep 38806127 = 58209191) B58209191
theorem B25870751 : Blo 2269435 25870751 := bstep (se 1 (by rfl) ⟨19403063, by rfl⟩ : syracuseStep 25870751 = 38806127) B38806127
theorem B17247167 : Blo 2269435 17247167 := bstep (se 1 (by rfl) ⟨12935375, by rfl⟩ : syracuseStep 17247167 = 25870751) B25870751
theorem B11498111 : Blo 2269435 11498111 := bstep (se 1 (by rfl) ⟨8623583, by rfl⟩ : syracuseStep 11498111 = 17247167) B17247167
theorem B7665407 : Blo 2269435 7665407 := bstep (se 1 (by rfl) ⟨5749055, by rfl⟩ : syracuseStep 7665407 = 11498111) B11498111
theorem B5110271 : Blo 2269435 5110271 := bstep (se 1 (by rfl) ⟨3832703, by rfl⟩ : syracuseStep 5110271 = 7665407) B7665407
theorem B3406847 : Blo 2269435 3406847 := bstep (se 1 (by rfl) ⟨2555135, by rfl⟩ : syracuseStep 3406847 = 5110271) B5110271
theorem B2271231 : Blo 2269435 2271231 := bstep (se 1 (by rfl) ⟨1703423, by rfl⟩ : syracuseStep 2271231 = 3406847) B3406847
theorem B3406853 : Blo 2269435 3406853 := bbase (se 4 (by rfl) ⟨319392, by rfl⟩ : syracuseStep 3406853 = 638785) (by norm_num)
theorem B2271235 : Blo 2269435 2271235 := bstep (se 1 (by rfl) ⟨1703426, by rfl⟩ : syracuseStep 2271235 = 3406853) B3406853
theorem B3832717 : Blo 2269435 3832717 := bbase (se 3 (by rfl) ⟨718634, by rfl⟩ : syracuseStep 3832717 = 1437269) (by norm_num)
theorem B5110289 : Blo 2269435 5110289 := bstep (se 2 (by rfl) ⟨1916358, by rfl⟩ : syracuseStep 5110289 = 3832717) B3832717
theorem B3406859 : Blo 2269435 3406859 := bstep (se 1 (by rfl) ⟨2555144, by rfl⟩ : syracuseStep 3406859 = 5110289) B5110289
theorem B2271239 : Blo 2269435 2271239 := bstep (se 1 (by rfl) ⟨1703429, by rfl⟩ : syracuseStep 2271239 = 3406859) B3406859
theorem B2555149 : Blo 2269435 2555149 := bbase (se 3 (by rfl) ⟨479090, by rfl⟩ : syracuseStep 2555149 = 958181) (by norm_num)
theorem B3406865 : Blo 2269435 3406865 := bstep (se 2 (by rfl) ⟨1277574, by rfl⟩ : syracuseStep 3406865 = 2555149) B2555149
theorem B2271243 : Blo 2269435 2271243 := bstep (se 1 (by rfl) ⟨1703432, by rfl⟩ : syracuseStep 2271243 = 3406865) B3406865
theorem B7665461 : Blo 2269435 7665461 := bbase (se 5 (by rfl) ⟨359318, by rfl⟩ : syracuseStep 7665461 = 718637) (by norm_num)
theorem B5110307 : Blo 2269435 5110307 := bstep (se 1 (by rfl) ⟨3832730, by rfl⟩ : syracuseStep 5110307 = 7665461) B7665461
theorem B3406871 : Blo 2269435 3406871 := bstep (se 1 (by rfl) ⟨2555153, by rfl⟩ : syracuseStep 3406871 = 5110307) B5110307
theorem B2271247 : Blo 2269435 2271247 := bstep (se 1 (by rfl) ⟨1703435, by rfl⟩ : syracuseStep 2271247 = 3406871) B3406871
theorem B3406877 : Blo 2269435 3406877 := bbase (se 3 (by rfl) ⟨638789, by rfl⟩ : syracuseStep 3406877 = 1277579) (by norm_num)
theorem B2271251 : Blo 2269435 2271251 := bstep (se 1 (by rfl) ⟨1703438, by rfl⟩ : syracuseStep 2271251 = 3406877) B3406877
theorem B5110325 : Blo 2269435 5110325 := bbase (se 5 (by rfl) ⟨239546, by rfl⟩ : syracuseStep 5110325 = 479093) (by norm_num)
theorem B3406883 : Blo 2269435 3406883 := bstep (se 1 (by rfl) ⟨2555162, by rfl⟩ : syracuseStep 3406883 = 5110325) B5110325
theorem B2271255 : Blo 2269435 2271255 := bstep (se 1 (by rfl) ⟨1703441, by rfl⟩ : syracuseStep 2271255 = 3406883) B3406883
theorem B9701653 : Blo 2269435 9701653 := bbase (se 6 (by rfl) ⟨227382, by rfl⟩ : syracuseStep 9701653 = 454765) (by norm_num)
theorem B12935537 : Blo 2269435 12935537 := bstep (se 2 (by rfl) ⟨4850826, by rfl⟩ : syracuseStep 12935537 = 9701653) B9701653
theorem B8623691 : Blo 2269435 8623691 := bstep (se 1 (by rfl) ⟨6467768, by rfl⟩ : syracuseStep 8623691 = 12935537) B12935537
theorem B5749127 : Blo 2269435 5749127 := bstep (se 1 (by rfl) ⟨4311845, by rfl⟩ : syracuseStep 5749127 = 8623691) B8623691
theorem B3832751 : Blo 2269435 3832751 := bstep (se 1 (by rfl) ⟨2874563, by rfl⟩ : syracuseStep 3832751 = 5749127) B5749127
theorem B2555167 : Blo 2269435 2555167 := bstep (se 1 (by rfl) ⟨1916375, by rfl⟩ : syracuseStep 2555167 = 3832751) B3832751
theorem B3406889 : Blo 2269435 3406889 := bstep (se 2 (by rfl) ⟨1277583, by rfl⟩ : syracuseStep 3406889 = 2555167) B2555167
theorem B2271259 : Blo 2269435 2271259 := bstep (se 1 (by rfl) ⟨1703444, by rfl⟩ : syracuseStep 2271259 = 3406889) B3406889
theorem B9701669 : Blo 2269435 9701669 := bbase (se 4 (by rfl) ⟨909531, by rfl⟩ : syracuseStep 9701669 = 1819063) (by norm_num)
theorem B6467779 : Blo 2269435 6467779 := bstep (se 1 (by rfl) ⟨4850834, by rfl⟩ : syracuseStep 6467779 = 9701669) B9701669
theorem B8623705 : Blo 2269435 8623705 := bstep (se 2 (by rfl) ⟨3233889, by rfl⟩ : syracuseStep 8623705 = 6467779) B6467779
theorem B11498273 : Blo 2269435 11498273 := bstep (se 2 (by rfl) ⟨4311852, by rfl⟩ : syracuseStep 11498273 = 8623705) B8623705
theorem B7665515 : Blo 2269435 7665515 := bstep (se 1 (by rfl) ⟨5749136, by rfl⟩ : syracuseStep 7665515 = 11498273) B11498273
theorem B5110343 : Blo 2269435 5110343 := bstep (se 1 (by rfl) ⟨3832757, by rfl⟩ : syracuseStep 5110343 = 7665515) B7665515
theorem B3406895 : Blo 2269435 3406895 := bstep (se 1 (by rfl) ⟨2555171, by rfl⟩ : syracuseStep 3406895 = 5110343) B5110343
theorem B2271263 : Blo 2269435 2271263 := bstep (se 1 (by rfl) ⟨1703447, by rfl⟩ : syracuseStep 2271263 = 3406895) B3406895
theorem B3406901 : Blo 2269435 3406901 := bbase (se 5 (by rfl) ⟨159698, by rfl⟩ : syracuseStep 3406901 = 319397) (by norm_num)
theorem B2271267 : Blo 2269435 2271267 := bstep (se 1 (by rfl) ⟨1703450, by rfl⟩ : syracuseStep 2271267 = 3406901) B3406901
theorem B5749157 : Blo 2269435 5749157 := bbase (se 4 (by rfl) ⟨538983, by rfl⟩ : syracuseStep 5749157 = 1077967) (by norm_num)
theorem B3832771 : Blo 2269435 3832771 := bstep (se 1 (by rfl) ⟨2874578, by rfl⟩ : syracuseStep 3832771 = 5749157) B5749157
theorem B5110361 : Blo 2269435 5110361 := bstep (se 2 (by rfl) ⟨1916385, by rfl⟩ : syracuseStep 5110361 = 3832771) B3832771
theorem B3406907 : Blo 2269435 3406907 := bstep (se 1 (by rfl) ⟨2555180, by rfl⟩ : syracuseStep 3406907 = 5110361) B5110361
theorem B2271271 : Blo 2269435 2271271 := bstep (se 1 (by rfl) ⟨1703453, by rfl⟩ : syracuseStep 2271271 = 3406907) B3406907
theorem B2555185 : Blo 2269435 2555185 := bbase (se 2 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 2555185 = 1916389) (by norm_num)
theorem B3406913 : Blo 2269435 3406913 := bstep (se 2 (by rfl) ⟨1277592, by rfl⟩ : syracuseStep 3406913 = 2555185) B2555185
theorem B2271275 : Blo 2269435 2271275 := bstep (se 1 (by rfl) ⟨1703456, by rfl⟩ : syracuseStep 2271275 = 3406913) B3406913
theorem B4850869 : Blo 2269435 4850869 := bbase (se 5 (by rfl) ⟨227384, by rfl⟩ : syracuseStep 4850869 = 454769) (by norm_num)
theorem B6467825 : Blo 2269435 6467825 := bstep (se 2 (by rfl) ⟨2425434, by rfl⟩ : syracuseStep 6467825 = 4850869) B4850869
theorem B4311883 : Blo 2269435 4311883 := bstep (se 1 (by rfl) ⟨3233912, by rfl⟩ : syracuseStep 4311883 = 6467825) B6467825
theorem B5749177 : Blo 2269435 5749177 := bstep (se 2 (by rfl) ⟨2155941, by rfl⟩ : syracuseStep 5749177 = 4311883) B4311883
theorem B7665569 : Blo 2269435 7665569 := bstep (se 2 (by rfl) ⟨2874588, by rfl⟩ : syracuseStep 7665569 = 5749177) B5749177
theorem B5110379 : Blo 2269435 5110379 := bstep (se 1 (by rfl) ⟨3832784, by rfl⟩ : syracuseStep 5110379 = 7665569) B7665569
theorem B3406919 : Blo 2269435 3406919 := bstep (se 1 (by rfl) ⟨2555189, by rfl⟩ : syracuseStep 3406919 = 5110379) B5110379
theorem B2271279 : Blo 2269435 2271279 := bstep (se 1 (by rfl) ⟨1703459, by rfl⟩ : syracuseStep 2271279 = 3406919) B3406919
theorem B3406925 : Blo 2269435 3406925 := bbase (se 3 (by rfl) ⟨638798, by rfl⟩ : syracuseStep 3406925 = 1277597) (by norm_num)
theorem B2271283 : Blo 2269435 2271283 := bstep (se 1 (by rfl) ⟨1703462, by rfl⟩ : syracuseStep 2271283 = 3406925) B3406925
theorem B5110397 : Blo 2269435 5110397 := bbase (se 3 (by rfl) ⟨958199, by rfl⟩ : syracuseStep 5110397 = 1916399) (by norm_num)
theorem B3406931 : Blo 2269435 3406931 := bstep (se 1 (by rfl) ⟨2555198, by rfl⟩ : syracuseStep 3406931 = 5110397) B5110397
theorem B2271287 : Blo 2269435 2271287 := bstep (se 1 (by rfl) ⟨1703465, by rfl⟩ : syracuseStep 2271287 = 3406931) B3406931
theorem B3832805 : Blo 2269435 3832805 := bbase (se 4 (by rfl) ⟨359325, by rfl⟩ : syracuseStep 3832805 = 718651) (by norm_num)
theorem B2555203 : Blo 2269435 2555203 := bstep (se 1 (by rfl) ⟨1916402, by rfl⟩ : syracuseStep 2555203 = 3832805) B3832805
theorem B3406937 : Blo 2269435 3406937 := bstep (se 2 (by rfl) ⟨1277601, by rfl⟩ : syracuseStep 3406937 = 2555203) B2555203
theorem B2271291 : Blo 2269435 2271291 := bstep (se 1 (by rfl) ⟨1703468, by rfl⟩ : syracuseStep 2271291 = 3406937) B3406937
theorem B10914533 : Blo 2269435 10914533 := bbase (se 4 (by rfl) ⟨1023237, by rfl⟩ : syracuseStep 10914533 = 2046475) (by norm_num)
theorem B7276355 : Blo 2269435 7276355 := bstep (se 1 (by rfl) ⟨5457266, by rfl⟩ : syracuseStep 7276355 = 10914533) B10914533
theorem B4850903 : Blo 2269435 4850903 := bstep (se 1 (by rfl) ⟨3638177, by rfl⟩ : syracuseStep 4850903 = 7276355) B7276355
theorem B3233935 : Blo 2269435 3233935 := bstep (se 1 (by rfl) ⟨2425451, by rfl⟩ : syracuseStep 3233935 = 4850903) B4850903
theorem B17247653 : Blo 2269435 17247653 := bstep (se 4 (by rfl) ⟨1616967, by rfl⟩ : syracuseStep 17247653 = 3233935) B3233935
theorem B11498435 : Blo 2269435 11498435 := bstep (se 1 (by rfl) ⟨8623826, by rfl⟩ : syracuseStep 11498435 = 17247653) B17247653
theorem B7665623 : Blo 2269435 7665623 := bstep (se 1 (by rfl) ⟨5749217, by rfl⟩ : syracuseStep 7665623 = 11498435) B11498435
theorem B5110415 : Blo 2269435 5110415 := bstep (se 1 (by rfl) ⟨3832811, by rfl⟩ : syracuseStep 5110415 = 7665623) B7665623
theorem B3406943 : Blo 2269435 3406943 := bstep (se 1 (by rfl) ⟨2555207, by rfl⟩ : syracuseStep 3406943 = 5110415) B5110415
theorem B2271295 : Blo 2269435 2271295 := bstep (se 1 (by rfl) ⟨1703471, by rfl⟩ : syracuseStep 2271295 = 3406943) B3406943
theorem B3406949 : Blo 2269435 3406949 := bbase (se 4 (by rfl) ⟨319401, by rfl⟩ : syracuseStep 3406949 = 638803) (by norm_num)
theorem B2271299 : Blo 2269435 2271299 := bstep (se 1 (by rfl) ⟨1703474, by rfl⟩ : syracuseStep 2271299 = 3406949) B3406949
theorem B9209173 : Blo 2269435 9209173 := bbase (se 12 (by rfl) ⟨3372, by rfl⟩ : syracuseStep 9209173 = 6745) (by norm_num)
theorem B12278897 : Blo 2269435 12278897 := bstep (se 2 (by rfl) ⟨4604586, by rfl⟩ : syracuseStep 12278897 = 9209173) B9209173
theorem B8185931 : Blo 2269435 8185931 := bstep (se 1 (by rfl) ⟨6139448, by rfl⟩ : syracuseStep 8185931 = 12278897) B12278897
theorem B5457287 : Blo 2269435 5457287 := bstep (se 1 (by rfl) ⟨4092965, by rfl⟩ : syracuseStep 5457287 = 8185931) B8185931
theorem B3638191 : Blo 2269435 3638191 := bstep (se 1 (by rfl) ⟨2728643, by rfl⟩ : syracuseStep 3638191 = 5457287) B5457287
theorem B4850921 : Blo 2269435 4850921 := bstep (se 2 (by rfl) ⟨1819095, by rfl⟩ : syracuseStep 4850921 = 3638191) B3638191
theorem B3233947 : Blo 2269435 3233947 := bstep (se 1 (by rfl) ⟨2425460, by rfl⟩ : syracuseStep 3233947 = 4850921) B4850921
theorem B4311929 : Blo 2269435 4311929 := bstep (se 2 (by rfl) ⟨1616973, by rfl⟩ : syracuseStep 4311929 = 3233947) B3233947
theorem B2874619 : Blo 2269435 2874619 := bstep (se 1 (by rfl) ⟨2155964, by rfl⟩ : syracuseStep 2874619 = 4311929) B4311929
theorem B3832825 : Blo 2269435 3832825 := bstep (se 2 (by rfl) ⟨1437309, by rfl⟩ : syracuseStep 3832825 = 2874619) B2874619
theorem B5110433 : Blo 2269435 5110433 := bstep (se 2 (by rfl) ⟨1916412, by rfl⟩ : syracuseStep 5110433 = 3832825) B3832825
theorem B3406955 : Blo 2269435 3406955 := bstep (se 1 (by rfl) ⟨2555216, by rfl⟩ : syracuseStep 3406955 = 5110433) B5110433
theorem B2271303 : Blo 2269435 2271303 := bstep (se 1 (by rfl) ⟨1703477, by rfl⟩ : syracuseStep 2271303 = 3406955) B3406955
theorem B2555221 : Blo 2269435 2555221 := bbase (se 11 (by rfl) ⟨1871, by rfl⟩ : syracuseStep 2555221 = 3743) (by norm_num)
theorem B3406961 : Blo 2269435 3406961 := bstep (se 2 (by rfl) ⟨1277610, by rfl⟩ : syracuseStep 3406961 = 2555221) B2555221
theorem B2271307 : Blo 2269435 2271307 := bstep (se 1 (by rfl) ⟨1703480, by rfl⟩ : syracuseStep 2271307 = 3406961) B3406961
theorem B2874629 : Blo 2269435 2874629 := bbase (se 4 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 2874629 = 538993) (by norm_num)
theorem B7665677 : Blo 2269435 7665677 := bstep (se 3 (by rfl) ⟨1437314, by rfl⟩ : syracuseStep 7665677 = 2874629) B2874629
theorem B5110451 : Blo 2269435 5110451 := bstep (se 1 (by rfl) ⟨3832838, by rfl⟩ : syracuseStep 5110451 = 7665677) B7665677
theorem B3406967 : Blo 2269435 3406967 := bstep (se 1 (by rfl) ⟨2555225, by rfl⟩ : syracuseStep 3406967 = 5110451) B5110451
theorem B2271311 : Blo 2269435 2271311 := bstep (se 1 (by rfl) ⟨1703483, by rfl⟩ : syracuseStep 2271311 = 3406967) B3406967
theorem B3406973 : Blo 2269435 3406973 := bbase (se 3 (by rfl) ⟨638807, by rfl⟩ : syracuseStep 3406973 = 1277615) (by norm_num)
theorem B2271315 : Blo 2269435 2271315 := bstep (se 1 (by rfl) ⟨1703486, by rfl⟩ : syracuseStep 2271315 = 3406973) B3406973
theorem B5110469 : Blo 2269435 5110469 := bbase (se 4 (by rfl) ⟨479106, by rfl⟩ : syracuseStep 5110469 = 958213) (by norm_num)
theorem B3406979 : Blo 2269435 3406979 := bstep (se 1 (by rfl) ⟨2555234, by rfl⟩ : syracuseStep 3406979 = 5110469) B5110469
theorem B2271319 : Blo 2269435 2271319 := bstep (se 1 (by rfl) ⟨1703489, by rfl⟩ : syracuseStep 2271319 = 3406979) B3406979
theorem B2302313 : Blo 2269435 2302313 := bbase (se 2 (by rfl) ⟨863367, by rfl⟩ : syracuseStep 2302313 = 1726735) (by norm_num)
theorem B24558005 : Blo 2269435 24558005 := bstep (se 5 (by rfl) ⟨1151156, by rfl⟩ : syracuseStep 24558005 = 2302313) B2302313
theorem B16372003 : Blo 2269435 16372003 := bstep (se 1 (by rfl) ⟨12279002, by rfl⟩ : syracuseStep 16372003 = 24558005) B24558005
theorem B21829337 : Blo 2269435 21829337 := bstep (se 2 (by rfl) ⟨8186001, by rfl⟩ : syracuseStep 21829337 = 16372003) B16372003
theorem B14552891 : Blo 2269435 14552891 := bstep (se 1 (by rfl) ⟨10914668, by rfl⟩ : syracuseStep 14552891 = 21829337) B21829337
theorem B9701927 : Blo 2269435 9701927 := bstep (se 1 (by rfl) ⟨7276445, by rfl⟩ : syracuseStep 9701927 = 14552891) B14552891
theorem B6467951 : Blo 2269435 6467951 := bstep (se 1 (by rfl) ⟨4850963, by rfl⟩ : syracuseStep 6467951 = 9701927) B9701927
theorem B4311967 : Blo 2269435 4311967 := bstep (se 1 (by rfl) ⟨3233975, by rfl⟩ : syracuseStep 4311967 = 6467951) B6467951
theorem B5749289 : Blo 2269435 5749289 := bstep (se 2 (by rfl) ⟨2155983, by rfl⟩ : syracuseStep 5749289 = 4311967) B4311967
theorem B3832859 : Blo 2269435 3832859 := bstep (se 1 (by rfl) ⟨2874644, by rfl⟩ : syracuseStep 3832859 = 5749289) B5749289
theorem B2555239 : Blo 2269435 2555239 := bstep (se 1 (by rfl) ⟨1916429, by rfl⟩ : syracuseStep 2555239 = 3832859) B3832859
theorem B3406985 : Blo 2269435 3406985 := bstep (se 2 (by rfl) ⟨1277619, by rfl⟩ : syracuseStep 3406985 = 2555239) B2555239
theorem B2271323 : Blo 2269435 2271323 := bstep (se 1 (by rfl) ⟨1703492, by rfl⟩ : syracuseStep 2271323 = 3406985) B3406985
theorem B11498597 : Blo 2269435 11498597 := bbase (se 4 (by rfl) ⟨1077993, by rfl⟩ : syracuseStep 11498597 = 2155987) (by norm_num)
theorem B7665731 : Blo 2269435 7665731 := bstep (se 1 (by rfl) ⟨5749298, by rfl⟩ : syracuseStep 7665731 = 11498597) B11498597
theorem B5110487 : Blo 2269435 5110487 := bstep (se 1 (by rfl) ⟨3832865, by rfl⟩ : syracuseStep 5110487 = 7665731) B7665731
theorem B3406991 : Blo 2269435 3406991 := bstep (se 1 (by rfl) ⟨2555243, by rfl⟩ : syracuseStep 3406991 = 5110487) B5110487
theorem B2271327 : Blo 2269435 2271327 := bstep (se 1 (by rfl) ⟨1703495, by rfl⟩ : syracuseStep 2271327 = 3406991) B3406991
theorem B3406997 : Blo 2269435 3406997 := bbase (se 6 (by rfl) ⟨79851, by rfl⟩ : syracuseStep 3406997 = 159703) (by norm_num)
theorem B2271331 : Blo 2269435 2271331 := bstep (se 1 (by rfl) ⟨1703498, by rfl⟩ : syracuseStep 2271331 = 3406997) B3406997
theorem B10914725 : Blo 2269435 10914725 := bbase (se 4 (by rfl) ⟨1023255, by rfl⟩ : syracuseStep 10914725 = 2046511) (by norm_num)
theorem B7276483 : Blo 2269435 7276483 := bstep (se 1 (by rfl) ⟨5457362, by rfl⟩ : syracuseStep 7276483 = 10914725) B10914725
theorem B9701977 : Blo 2269435 9701977 := bstep (se 2 (by rfl) ⟨3638241, by rfl⟩ : syracuseStep 9701977 = 7276483) B7276483
theorem B12935969 : Blo 2269435 12935969 := bstep (se 2 (by rfl) ⟨4850988, by rfl⟩ : syracuseStep 12935969 = 9701977) B9701977
theorem B8623979 : Blo 2269435 8623979 := bstep (se 1 (by rfl) ⟨6467984, by rfl⟩ : syracuseStep 8623979 = 12935969) B12935969
theorem B5749319 : Blo 2269435 5749319 := bstep (se 1 (by rfl) ⟨4311989, by rfl⟩ : syracuseStep 5749319 = 8623979) B8623979
theorem B3832879 : Blo 2269435 3832879 := bstep (se 1 (by rfl) ⟨2874659, by rfl⟩ : syracuseStep 3832879 = 5749319) B5749319
theorem B5110505 : Blo 2269435 5110505 := bstep (se 2 (by rfl) ⟨1916439, by rfl⟩ : syracuseStep 5110505 = 3832879) B3832879
theorem B3407003 : Blo 2269435 3407003 := bstep (se 1 (by rfl) ⟨2555252, by rfl⟩ : syracuseStep 3407003 = 5110505) B5110505
theorem B2271335 : Blo 2269435 2271335 := bstep (se 1 (by rfl) ⟨1703501, by rfl⟩ : syracuseStep 2271335 = 3407003) B3407003
theorem B2555257 : Blo 2269435 2555257 := bbase (se 2 (by rfl) ⟨958221, by rfl⟩ : syracuseStep 2555257 = 1916443) (by norm_num)
theorem B3407009 : Blo 2269435 3407009 := bstep (se 2 (by rfl) ⟨1277628, by rfl⟩ : syracuseStep 3407009 = 2555257) B2555257
theorem B2271339 : Blo 2269435 2271339 := bstep (se 1 (by rfl) ⟨1703504, by rfl⟩ : syracuseStep 2271339 = 3407009) B3407009
theorem B2302333 : Blo 2269435 2302333 := bbase (se 3 (by rfl) ⟨431687, by rfl⟩ : syracuseStep 2302333 = 863375) (by norm_num)
theorem B12279109 : Blo 2269435 12279109 := bstep (se 4 (by rfl) ⟨1151166, by rfl⟩ : syracuseStep 12279109 = 2302333) B2302333
theorem B16372145 : Blo 2269435 16372145 := bstep (se 2 (by rfl) ⟨6139554, by rfl⟩ : syracuseStep 16372145 = 12279109) B12279109
theorem B10914763 : Blo 2269435 10914763 := bstep (se 1 (by rfl) ⟨8186072, by rfl⟩ : syracuseStep 10914763 = 16372145) B16372145
theorem B14553017 : Blo 2269435 14553017 := bstep (se 2 (by rfl) ⟨5457381, by rfl⟩ : syracuseStep 14553017 = 10914763) B10914763
theorem B9702011 : Blo 2269435 9702011 := bstep (se 1 (by rfl) ⟨7276508, by rfl⟩ : syracuseStep 9702011 = 14553017) B14553017
theorem B6468007 : Blo 2269435 6468007 := bstep (se 1 (by rfl) ⟨4851005, by rfl⟩ : syracuseStep 6468007 = 9702011) B9702011
theorem B8624009 : Blo 2269435 8624009 := bstep (se 2 (by rfl) ⟨3234003, by rfl⟩ : syracuseStep 8624009 = 6468007) B6468007
theorem B5749339 : Blo 2269435 5749339 := bstep (se 1 (by rfl) ⟨4312004, by rfl⟩ : syracuseStep 5749339 = 8624009) B8624009
theorem B7665785 : Blo 2269435 7665785 := bstep (se 2 (by rfl) ⟨2874669, by rfl⟩ : syracuseStep 7665785 = 5749339) B5749339
theorem B5110523 : Blo 2269435 5110523 := bstep (se 1 (by rfl) ⟨3832892, by rfl⟩ : syracuseStep 5110523 = 7665785) B7665785
theorem B3407015 : Blo 2269435 3407015 := bstep (se 1 (by rfl) ⟨2555261, by rfl⟩ : syracuseStep 3407015 = 5110523) B5110523
theorem B2271343 : Blo 2269435 2271343 := bstep (se 1 (by rfl) ⟨1703507, by rfl⟩ : syracuseStep 2271343 = 3407015) B3407015
theorem B3407021 : Blo 2269435 3407021 := bbase (se 3 (by rfl) ⟨638816, by rfl⟩ : syracuseStep 3407021 = 1277633) (by norm_num)
theorem B2271347 : Blo 2269435 2271347 := bstep (se 1 (by rfl) ⟨1703510, by rfl⟩ : syracuseStep 2271347 = 3407021) B3407021
theorem B5110541 : Blo 2269435 5110541 := bbase (se 3 (by rfl) ⟨958226, by rfl⟩ : syracuseStep 5110541 = 1916453) (by norm_num)
theorem B3407027 : Blo 2269435 3407027 := bstep (se 1 (by rfl) ⟨2555270, by rfl⟩ : syracuseStep 3407027 = 5110541) B5110541
theorem B2271351 : Blo 2269435 2271351 := bstep (se 1 (by rfl) ⟨1703513, by rfl⟩ : syracuseStep 2271351 = 3407027) B3407027
theorem B2874685 : Blo 2269435 2874685 := bbase (se 3 (by rfl) ⟨539003, by rfl⟩ : syracuseStep 2874685 = 1078007) (by norm_num)
theorem B3832913 : Blo 2269435 3832913 := bstep (se 2 (by rfl) ⟨1437342, by rfl⟩ : syracuseStep 3832913 = 2874685) B2874685
theorem B2555275 : Blo 2269435 2555275 := bstep (se 1 (by rfl) ⟨1916456, by rfl⟩ : syracuseStep 2555275 = 3832913) B3832913
theorem B3407033 : Blo 2269435 3407033 := bstep (se 2 (by rfl) ⟨1277637, by rfl⟩ : syracuseStep 3407033 = 2555275) B2555275
theorem B2271355 : Blo 2269435 2271355 := bstep (se 1 (by rfl) ⟨1703516, by rfl⟩ : syracuseStep 2271355 = 3407033) B3407033
theorem B2302349 : Blo 2269435 2302349 := bbase (se 3 (by rfl) ⟨431690, by rfl⟩ : syracuseStep 2302349 = 863381) (by norm_num)
theorem B24558389 : Blo 2269435 24558389 := bstep (se 5 (by rfl) ⟨1151174, by rfl⟩ : syracuseStep 24558389 = 2302349) B2302349
theorem B16372259 : Blo 2269435 16372259 := bstep (se 1 (by rfl) ⟨12279194, by rfl⟩ : syracuseStep 16372259 = 24558389) B24558389
theorem B10914839 : Blo 2269435 10914839 := bstep (se 1 (by rfl) ⟨8186129, by rfl⟩ : syracuseStep 10914839 = 16372259) B16372259
theorem B7276559 : Blo 2269435 7276559 := bstep (se 1 (by rfl) ⟨5457419, by rfl⟩ : syracuseStep 7276559 = 10914839) B10914839
theorem B19404157 : Blo 2269435 19404157 := bstep (se 3 (by rfl) ⟨3638279, by rfl⟩ : syracuseStep 19404157 = 7276559) B7276559
theorem B25872209 : Blo 2269435 25872209 := bstep (se 2 (by rfl) ⟨9702078, by rfl⟩ : syracuseStep 25872209 = 19404157) B19404157
theorem B17248139 : Blo 2269435 17248139 := bstep (se 1 (by rfl) ⟨12936104, by rfl⟩ : syracuseStep 17248139 = 25872209) B25872209
theorem B11498759 : Blo 2269435 11498759 := bstep (se 1 (by rfl) ⟨8624069, by rfl⟩ : syracuseStep 11498759 = 17248139) B17248139
theorem B7665839 : Blo 2269435 7665839 := bstep (se 1 (by rfl) ⟨5749379, by rfl⟩ : syracuseStep 7665839 = 11498759) B11498759
theorem B5110559 : Blo 2269435 5110559 := bstep (se 1 (by rfl) ⟨3832919, by rfl⟩ : syracuseStep 5110559 = 7665839) B7665839
theorem B3407039 : Blo 2269435 3407039 := bstep (se 1 (by rfl) ⟨2555279, by rfl⟩ : syracuseStep 3407039 = 5110559) B5110559
theorem B2271359 : Blo 2269435 2271359 := bstep (se 1 (by rfl) ⟨1703519, by rfl⟩ : syracuseStep 2271359 = 3407039) B3407039
theorem B3407045 : Blo 2269435 3407045 := bbase (se 4 (by rfl) ⟨319410, by rfl⟩ : syracuseStep 3407045 = 638821) (by norm_num)
theorem B2271363 : Blo 2269435 2271363 := bstep (se 1 (by rfl) ⟨1703522, by rfl⟩ : syracuseStep 2271363 = 3407045) B3407045
theorem B3832933 : Blo 2269435 3832933 := bbase (se 4 (by rfl) ⟨359337, by rfl⟩ : syracuseStep 3832933 = 718675) (by norm_num)
theorem B5110577 : Blo 2269435 5110577 := bstep (se 2 (by rfl) ⟨1916466, by rfl⟩ : syracuseStep 5110577 = 3832933) B3832933
theorem B3407051 : Blo 2269435 3407051 := bstep (se 1 (by rfl) ⟨2555288, by rfl⟩ : syracuseStep 3407051 = 5110577) B5110577
theorem B2271367 : Blo 2269435 2271367 := bstep (se 1 (by rfl) ⟨1703525, by rfl⟩ : syracuseStep 2271367 = 3407051) B3407051
theorem B2555293 : Blo 2269435 2555293 := bbase (se 3 (by rfl) ⟨479117, by rfl⟩ : syracuseStep 2555293 = 958235) (by norm_num)
theorem B3407057 : Blo 2269435 3407057 := bstep (se 2 (by rfl) ⟨1277646, by rfl⟩ : syracuseStep 3407057 = 2555293) B2555293
theorem B2271371 : Blo 2269435 2271371 := bstep (se 1 (by rfl) ⟨1703528, by rfl⟩ : syracuseStep 2271371 = 3407057) B3407057
theorem B7665893 : Blo 2269435 7665893 := bbase (se 4 (by rfl) ⟨718677, by rfl⟩ : syracuseStep 7665893 = 1437355) (by norm_num)
theorem B5110595 : Blo 2269435 5110595 := bstep (se 1 (by rfl) ⟨3832946, by rfl⟩ : syracuseStep 5110595 = 7665893) B7665893
theorem B3407063 : Blo 2269435 3407063 := bstep (se 1 (by rfl) ⟨2555297, by rfl⟩ : syracuseStep 3407063 = 5110595) B5110595
theorem B2271375 : Blo 2269435 2271375 := bstep (se 1 (by rfl) ⟨1703531, by rfl⟩ : syracuseStep 2271375 = 3407063) B3407063
theorem B3407069 : Blo 2269435 3407069 := bbase (se 3 (by rfl) ⟨638825, by rfl⟩ : syracuseStep 3407069 = 1277651) (by norm_num)
theorem B2271379 : Blo 2269435 2271379 := bstep (se 1 (by rfl) ⟨1703534, by rfl⟩ : syracuseStep 2271379 = 3407069) B3407069
theorem B5110613 : Blo 2269435 5110613 := bbase (se 9 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 5110613 = 29945) (by norm_num)
theorem B3407075 : Blo 2269435 3407075 := bstep (se 1 (by rfl) ⟨2555306, by rfl⟩ : syracuseStep 3407075 = 5110613) B5110613
theorem B2271383 : Blo 2269435 2271383 := bstep (se 1 (by rfl) ⟨1703537, by rfl⟩ : syracuseStep 2271383 = 3407075) B3407075
theorem B6468133 : Blo 2269435 6468133 := bbase (se 4 (by rfl) ⟨606387, by rfl⟩ : syracuseStep 6468133 = 1212775) (by norm_num)
theorem B8624177 : Blo 2269435 8624177 := bstep (se 2 (by rfl) ⟨3234066, by rfl⟩ : syracuseStep 8624177 = 6468133) B6468133
theorem B5749451 : Blo 2269435 5749451 := bstep (se 1 (by rfl) ⟨4312088, by rfl⟩ : syracuseStep 5749451 = 8624177) B8624177
theorem B3832967 : Blo 2269435 3832967 := bstep (se 1 (by rfl) ⟨2874725, by rfl⟩ : syracuseStep 3832967 = 5749451) B5749451
theorem B2555311 : Blo 2269435 2555311 := bstep (se 1 (by rfl) ⟨1916483, by rfl⟩ : syracuseStep 2555311 = 3832967) B3832967
theorem B3407081 : Blo 2269435 3407081 := bstep (se 2 (by rfl) ⟨1277655, by rfl⟩ : syracuseStep 3407081 = 2555311) B2555311
theorem B2271387 : Blo 2269435 2271387 := bstep (se 1 (by rfl) ⟨1703540, by rfl⟩ : syracuseStep 2271387 = 3407081) B3407081
theorem B63012437 : Blo 2269435 63012437 := bbase (se 8 (by rfl) ⟨369213, by rfl⟩ : syracuseStep 63012437 = 738427) (by norm_num)
theorem B42008291 : Blo 2269435 42008291 := bstep (se 1 (by rfl) ⟨31506218, by rfl⟩ : syracuseStep 42008291 = 63012437) B63012437
theorem B28005527 : Blo 2269435 28005527 := bstep (se 1 (by rfl) ⟨21004145, by rfl⟩ : syracuseStep 28005527 = 42008291) B42008291
theorem B18670351 : Blo 2269435 18670351 := bstep (se 1 (by rfl) ⟨14002763, by rfl⟩ : syracuseStep 18670351 = 28005527) B28005527
theorem B24893801 : Blo 2269435 24893801 := bstep (se 2 (by rfl) ⟨9335175, by rfl⟩ : syracuseStep 24893801 = 18670351) B18670351
theorem B16595867 : Blo 2269435 16595867 := bstep (se 1 (by rfl) ⟨12446900, by rfl⟩ : syracuseStep 16595867 = 24893801) B24893801
theorem B44255645 : Blo 2269435 44255645 := bstep (se 3 (by rfl) ⟨8297933, by rfl⟩ : syracuseStep 44255645 = 16595867) B16595867
theorem B29503763 : Blo 2269435 29503763 := bstep (se 1 (by rfl) ⟨22127822, by rfl⟩ : syracuseStep 29503763 = 44255645) B44255645
theorem B19669175 : Blo 2269435 19669175 := bstep (se 1 (by rfl) ⟨14751881, by rfl⟩ : syracuseStep 19669175 = 29503763) B29503763
theorem B13112783 : Blo 2269435 13112783 := bstep (se 1 (by rfl) ⟨9834587, by rfl⟩ : syracuseStep 13112783 = 19669175) B19669175
theorem B8741855 : Blo 2269435 8741855 := bstep (se 1 (by rfl) ⟨6556391, by rfl⟩ : syracuseStep 8741855 = 13112783) B13112783
theorem B23311613 : Blo 2269435 23311613 := bstep (se 3 (by rfl) ⟨4370927, by rfl⟩ : syracuseStep 23311613 = 8741855) B8741855
theorem B15541075 : Blo 2269435 15541075 := bstep (se 1 (by rfl) ⟨11655806, by rfl⟩ : syracuseStep 15541075 = 23311613) B23311613
theorem B20721433 : Blo 2269435 20721433 := bstep (se 2 (by rfl) ⟨7770537, by rfl⟩ : syracuseStep 20721433 = 15541075) B15541075
theorem B27628577 : Blo 2269435 27628577 := bstep (se 2 (by rfl) ⟨10360716, by rfl⟩ : syracuseStep 27628577 = 20721433) B20721433
theorem B18419051 : Blo 2269435 18419051 := bstep (se 1 (by rfl) ⟨13814288, by rfl⟩ : syracuseStep 18419051 = 27628577) B27628577
theorem B12279367 : Blo 2269435 12279367 := bstep (se 1 (by rfl) ⟨9209525, by rfl⟩ : syracuseStep 12279367 = 18419051) B18419051
theorem B65489957 : Blo 2269435 65489957 := bstep (se 4 (by rfl) ⟨6139683, by rfl⟩ : syracuseStep 65489957 = 12279367) B12279367
theorem B43659971 : Blo 2269435 43659971 := bstep (se 1 (by rfl) ⟨32744978, by rfl⟩ : syracuseStep 43659971 = 65489957) B65489957
theorem B29106647 : Blo 2269435 29106647 := bstep (se 1 (by rfl) ⟨21829985, by rfl⟩ : syracuseStep 29106647 = 43659971) B43659971
theorem B19404431 : Blo 2269435 19404431 := bstep (se 1 (by rfl) ⟨14553323, by rfl⟩ : syracuseStep 19404431 = 29106647) B29106647
theorem B12936287 : Blo 2269435 12936287 := bstep (se 1 (by rfl) ⟨9702215, by rfl⟩ : syracuseStep 12936287 = 19404431) B19404431
theorem B8624191 : Blo 2269435 8624191 := bstep (se 1 (by rfl) ⟨6468143, by rfl⟩ : syracuseStep 8624191 = 12936287) B12936287
theorem B11498921 : Blo 2269435 11498921 := bstep (se 2 (by rfl) ⟨4312095, by rfl⟩ : syracuseStep 11498921 = 8624191) B8624191
theorem B7665947 : Blo 2269435 7665947 := bstep (se 1 (by rfl) ⟨5749460, by rfl⟩ : syracuseStep 7665947 = 11498921) B11498921
theorem B5110631 : Blo 2269435 5110631 := bstep (se 1 (by rfl) ⟨3832973, by rfl⟩ : syracuseStep 5110631 = 7665947) B7665947
theorem B3407087 : Blo 2269435 3407087 := bstep (se 1 (by rfl) ⟨2555315, by rfl⟩ : syracuseStep 3407087 = 5110631) B5110631
theorem B2271391 : Blo 2269435 2271391 := bstep (se 1 (by rfl) ⟨1703543, by rfl⟩ : syracuseStep 2271391 = 3407087) B3407087
theorem B3407093 : Blo 2269435 3407093 := bbase (se 5 (by rfl) ⟨159707, by rfl⟩ : syracuseStep 3407093 = 319415) (by norm_num)
theorem B2271395 : Blo 2269435 2271395 := bstep (se 1 (by rfl) ⟨1703546, by rfl⟩ : syracuseStep 2271395 = 3407093) B3407093
theorem B12279413 : Blo 2269435 12279413 := bbase (se 5 (by rfl) ⟨575597, by rfl⟩ : syracuseStep 12279413 = 1151195) (by norm_num)
theorem B8186275 : Blo 2269435 8186275 := bstep (se 1 (by rfl) ⟨6139706, by rfl⟩ : syracuseStep 8186275 = 12279413) B12279413
theorem B10915033 : Blo 2269435 10915033 := bstep (se 2 (by rfl) ⟨4093137, by rfl⟩ : syracuseStep 10915033 = 8186275) B8186275
theorem B14553377 : Blo 2269435 14553377 := bstep (se 2 (by rfl) ⟨5457516, by rfl⟩ : syracuseStep 14553377 = 10915033) B10915033
theorem B9702251 : Blo 2269435 9702251 := bstep (se 1 (by rfl) ⟨7276688, by rfl⟩ : syracuseStep 9702251 = 14553377) B14553377
theorem B6468167 : Blo 2269435 6468167 := bstep (se 1 (by rfl) ⟨4851125, by rfl⟩ : syracuseStep 6468167 = 9702251) B9702251
theorem B4312111 : Blo 2269435 4312111 := bstep (se 1 (by rfl) ⟨3234083, by rfl⟩ : syracuseStep 4312111 = 6468167) B6468167
theorem B5749481 : Blo 2269435 5749481 := bstep (se 2 (by rfl) ⟨2156055, by rfl⟩ : syracuseStep 5749481 = 4312111) B4312111
theorem B3832987 : Blo 2269435 3832987 := bstep (se 1 (by rfl) ⟨2874740, by rfl⟩ : syracuseStep 3832987 = 5749481) B5749481
theorem B5110649 : Blo 2269435 5110649 := bstep (se 2 (by rfl) ⟨1916493, by rfl⟩ : syracuseStep 5110649 = 3832987) B3832987
theorem B3407099 : Blo 2269435 3407099 := bstep (se 1 (by rfl) ⟨2555324, by rfl⟩ : syracuseStep 3407099 = 5110649) B5110649
theorem B2271399 : Blo 2269435 2271399 := bstep (se 1 (by rfl) ⟨1703549, by rfl⟩ : syracuseStep 2271399 = 3407099) B3407099
theorem B2555329 : Blo 2269435 2555329 := bbase (se 2 (by rfl) ⟨958248, by rfl⟩ : syracuseStep 2555329 = 1916497) (by norm_num)
theorem B3407105 : Blo 2269435 3407105 := bstep (se 2 (by rfl) ⟨1277664, by rfl⟩ : syracuseStep 3407105 = 2555329) B2555329
theorem B2271403 : Blo 2269435 2271403 := bstep (se 1 (by rfl) ⟨1703552, by rfl⟩ : syracuseStep 2271403 = 3407105) B3407105
theorem B5749501 : Blo 2269435 5749501 := bbase (se 3 (by rfl) ⟨1078031, by rfl⟩ : syracuseStep 5749501 = 2156063) (by norm_num)
theorem B7666001 : Blo 2269435 7666001 := bstep (se 2 (by rfl) ⟨2874750, by rfl⟩ : syracuseStep 7666001 = 5749501) B5749501
theorem B5110667 : Blo 2269435 5110667 := bstep (se 1 (by rfl) ⟨3833000, by rfl⟩ : syracuseStep 5110667 = 7666001) B7666001
theorem B3407111 : Blo 2269435 3407111 := bstep (se 1 (by rfl) ⟨2555333, by rfl⟩ : syracuseStep 3407111 = 5110667) B5110667
theorem B2271407 : Blo 2269435 2271407 := bstep (se 1 (by rfl) ⟨1703555, by rfl⟩ : syracuseStep 2271407 = 3407111) B3407111
theorem B3407117 : Blo 2269435 3407117 := bbase (se 3 (by rfl) ⟨638834, by rfl⟩ : syracuseStep 3407117 = 1277669) (by norm_num)
theorem B2271411 : Blo 2269435 2271411 := bstep (se 1 (by rfl) ⟨1703558, by rfl⟩ : syracuseStep 2271411 = 3407117) B3407117
theorem B5110685 : Blo 2269435 5110685 := bbase (se 3 (by rfl) ⟨958253, by rfl⟩ : syracuseStep 5110685 = 1916507) (by norm_num)
theorem B3407123 : Blo 2269435 3407123 := bstep (se 1 (by rfl) ⟨2555342, by rfl⟩ : syracuseStep 3407123 = 5110685) B5110685
theorem B2271415 : Blo 2269435 2271415 := bstep (se 1 (by rfl) ⟨1703561, by rfl⟩ : syracuseStep 2271415 = 3407123) B3407123
theorem B3833021 : Blo 2269435 3833021 := bbase (se 3 (by rfl) ⟨718691, by rfl⟩ : syracuseStep 3833021 = 1437383) (by norm_num)
theorem B2555347 : Blo 2269435 2555347 := bstep (se 1 (by rfl) ⟨1916510, by rfl⟩ : syracuseStep 2555347 = 3833021) B3833021
theorem B3407129 : Blo 2269435 3407129 := bstep (se 2 (by rfl) ⟨1277673, by rfl⟩ : syracuseStep 3407129 = 2555347) B2555347
theorem B2271419 : Blo 2269435 2271419 := bstep (se 1 (by rfl) ⟨1703564, by rfl⟩ : syracuseStep 2271419 = 3407129) B3407129
theorem B12936469 : Blo 2269435 12936469 := bbase (se 6 (by rfl) ⟨303198, by rfl⟩ : syracuseStep 12936469 = 606397) (by norm_num)
theorem B17248625 : Blo 2269435 17248625 := bstep (se 2 (by rfl) ⟨6468234, by rfl⟩ : syracuseStep 17248625 = 12936469) B12936469
theorem B11499083 : Blo 2269435 11499083 := bstep (se 1 (by rfl) ⟨8624312, by rfl⟩ : syracuseStep 11499083 = 17248625) B17248625
theorem B7666055 : Blo 2269435 7666055 := bstep (se 1 (by rfl) ⟨5749541, by rfl⟩ : syracuseStep 7666055 = 11499083) B11499083
theorem B5110703 : Blo 2269435 5110703 := bstep (se 1 (by rfl) ⟨3833027, by rfl⟩ : syracuseStep 5110703 = 7666055) B7666055
theorem B3407135 : Blo 2269435 3407135 := bstep (se 1 (by rfl) ⟨2555351, by rfl⟩ : syracuseStep 3407135 = 5110703) B5110703
theorem B2271423 : Blo 2269435 2271423 := bstep (se 1 (by rfl) ⟨1703567, by rfl⟩ : syracuseStep 2271423 = 3407135) B3407135
theorem B3407141 : Blo 2269435 3407141 := bbase (se 4 (by rfl) ⟨319419, by rfl⟩ : syracuseStep 3407141 = 638839) (by norm_num)
theorem B2271427 : Blo 2269435 2271427 := bstep (se 1 (by rfl) ⟨1703570, by rfl⟩ : syracuseStep 2271427 = 3407141) B3407141
theorem B2874781 : Blo 2269435 2874781 := bbase (se 3 (by rfl) ⟨539021, by rfl⟩ : syracuseStep 2874781 = 1078043) (by norm_num)
theorem B3833041 : Blo 2269435 3833041 := bstep (se 2 (by rfl) ⟨1437390, by rfl⟩ : syracuseStep 3833041 = 2874781) B2874781
theorem B5110721 : Blo 2269435 5110721 := bstep (se 2 (by rfl) ⟨1916520, by rfl⟩ : syracuseStep 5110721 = 3833041) B3833041
theorem B3407147 : Blo 2269435 3407147 := bstep (se 1 (by rfl) ⟨2555360, by rfl⟩ : syracuseStep 3407147 = 5110721) B5110721
theorem B2271431 : Blo 2269435 2271431 := bstep (se 1 (by rfl) ⟨1703573, by rfl⟩ : syracuseStep 2271431 = 3407147) B3407147
theorem B2555365 : Blo 2269435 2555365 := bbase (se 4 (by rfl) ⟨239565, by rfl⟩ : syracuseStep 2555365 = 479131) (by norm_num)
theorem B3407153 : Blo 2269435 3407153 := bstep (se 2 (by rfl) ⟨1277682, by rfl⟩ : syracuseStep 3407153 = 2555365) B2555365
theorem B2271435 : Blo 2269435 2271435 := bstep (se 1 (by rfl) ⟨1703576, by rfl⟩ : syracuseStep 2271435 = 3407153) B3407153
theorem C0 (j : ℕ) (h1 : 567358 ≤ j) (h2 : j ≤ 567858) : Blo 2269435 (4 * j + 3) := by
  interval_cases j
  · exact B2269435
  · exact B2269439
  · exact B2269443
  · exact B2269447
  · exact B2269451
  · exact B2269455
  · exact B2269459
  · exact B2269463
  · exact B2269467
  · exact B2269471
  · exact B2269475
  · exact B2269479
  · exact B2269483
  · exact B2269487
  · exact B2269491
  · exact B2269495
  · exact B2269499
  · exact B2269503
  · exact B2269507
  · exact B2269511
  · exact B2269515
  · exact B2269519
  · exact B2269523
  · exact B2269527
  · exact B2269531
  · exact B2269535
  · exact B2269539
  · exact B2269543
  · exact B2269547
  · exact B2269551
  · exact B2269555
  · exact B2269559
  · exact B2269563
  · exact B2269567
  · exact B2269571
  · exact B2269575
  · exact B2269579
  · exact B2269583
  · exact B2269587
  · exact B2269591
  · exact B2269595
  · exact B2269599
  · exact B2269603
  · exact B2269607
  · exact B2269611
  · exact B2269615
  · exact B2269619
  · exact B2269623
  · exact B2269627
  · exact B2269631
  · exact B2269635
  · exact B2269639
  · exact B2269643
  · exact B2269647
  · exact B2269651
  · exact B2269655
  · exact B2269659
  · exact B2269663
  · exact B2269667
  · exact B2269671
  · exact B2269675
  · exact B2269679
  · exact B2269683
  · exact B2269687
  · exact B2269691
  · exact B2269695
  · exact B2269699
  · exact B2269703
  · exact B2269707
  · exact B2269711
  · exact B2269715
  · exact B2269719
  · exact B2269723
  · exact B2269727
  · exact B2269731
  · exact B2269735
  · exact B2269739
  · exact B2269743
  · exact B2269747
  · exact B2269751
  · exact B2269755
  · exact B2269759
  · exact B2269763
  · exact B2269767
  · exact B2269771
  · exact B2269775
  · exact B2269779
  · exact B2269783
  · exact B2269787
  · exact B2269791
  · exact B2269795
  · exact B2269799
  · exact B2269803
  · exact B2269807
  · exact B2269811
  · exact B2269815
  · exact B2269819
  · exact B2269823
  · exact B2269827
  · exact B2269831
  · exact B2269835
  · exact B2269839
  · exact B2269843
  · exact B2269847
  · exact B2269851
  · exact B2269855
  · exact B2269859
  · exact B2269863
  · exact B2269867
  · exact B2269871
  · exact B2269875
  · exact B2269879
  · exact B2269883
  · exact B2269887
  · exact B2269891
  · exact B2269895
  · exact B2269899
  · exact B2269903
  · exact B2269907
  · exact B2269911
  · exact B2269915
  · exact B2269919
  · exact B2269923
  · exact B2269927
  · exact B2269931
  · exact B2269935
  · exact B2269939
  · exact B2269943
  · exact B2269947
  · exact B2269951
  · exact B2269955
  · exact B2269959
  · exact B2269963
  · exact B2269967
  · exact B2269971
  · exact B2269975
  · exact B2269979
  · exact B2269983
  · exact B2269987
  · exact B2269991
  · exact B2269995
  · exact B2269999
  · exact B2270003
  · exact B2270007
  · exact B2270011
  · exact B2270015
  · exact B2270019
  · exact B2270023
  · exact B2270027
  · exact B2270031
  · exact B2270035
  · exact B2270039
  · exact B2270043
  · exact B2270047
  · exact B2270051
  · exact B2270055
  · exact B2270059
  · exact B2270063
  · exact B2270067
  · exact B2270071
  · exact B2270075
  · exact B2270079
  · exact B2270083
  · exact B2270087
  · exact B2270091
  · exact B2270095
  · exact B2270099
  · exact B2270103
  · exact B2270107
  · exact B2270111
  · exact B2270115
  · exact B2270119
  · exact B2270123
  · exact B2270127
  · exact B2270131
  · exact B2270135
  · exact B2270139
  · exact B2270143
  · exact B2270147
  · exact B2270151
  · exact B2270155
  · exact B2270159
  · exact B2270163
  · exact B2270167
  · exact B2270171
  · exact B2270175
  · exact B2270179
  · exact B2270183
  · exact B2270187
  · exact B2270191
  · exact B2270195
  · exact B2270199
  · exact B2270203
  · exact B2270207
  · exact B2270211
  · exact B2270215
  · exact B2270219
  · exact B2270223
  · exact B2270227
  · exact B2270231
  · exact B2270235
  · exact B2270239
  · exact B2270243
  · exact B2270247
  · exact B2270251
  · exact B2270255
  · exact B2270259
  · exact B2270263
  · exact B2270267
  · exact B2270271
  · exact B2270275
  · exact B2270279
  · exact B2270283
  · exact B2270287
  · exact B2270291
  · exact B2270295
  · exact B2270299
  · exact B2270303
  · exact B2270307
  · exact B2270311
  · exact B2270315
  · exact B2270319
  · exact B2270323
  · exact B2270327
  · exact B2270331
  · exact B2270335
  · exact B2270339
  · exact B2270343
  · exact B2270347
  · exact B2270351
  · exact B2270355
  · exact B2270359
  · exact B2270363
  · exact B2270367
  · exact B2270371
  · exact B2270375
  · exact B2270379
  · exact B2270383
  · exact B2270387
  · exact B2270391
  · exact B2270395
  · exact B2270399
  · exact B2270403
  · exact B2270407
  · exact B2270411
  · exact B2270415
  · exact B2270419
  · exact B2270423
  · exact B2270427
  · exact B2270431
  · exact B2270435
  · exact B2270439
  · exact B2270443
  · exact B2270447
  · exact B2270451
  · exact B2270455
  · exact B2270459
  · exact B2270463
  · exact B2270467
  · exact B2270471
  · exact B2270475
  · exact B2270479
  · exact B2270483
  · exact B2270487
  · exact B2270491
  · exact B2270495
  · exact B2270499
  · exact B2270503
  · exact B2270507
  · exact B2270511
  · exact B2270515
  · exact B2270519
  · exact B2270523
  · exact B2270527
  · exact B2270531
  · exact B2270535
  · exact B2270539
  · exact B2270543
  · exact B2270547
  · exact B2270551
  · exact B2270555
  · exact B2270559
  · exact B2270563
  · exact B2270567
  · exact B2270571
  · exact B2270575
  · exact B2270579
  · exact B2270583
  · exact B2270587
  · exact B2270591
  · exact B2270595
  · exact B2270599
  · exact B2270603
  · exact B2270607
  · exact B2270611
  · exact B2270615
  · exact B2270619
  · exact B2270623
  · exact B2270627
  · exact B2270631
  · exact B2270635
  · exact B2270639
  · exact B2270643
  · exact B2270647
  · exact B2270651
  · exact B2270655
  · exact B2270659
  · exact B2270663
  · exact B2270667
  · exact B2270671
  · exact B2270675
  · exact B2270679
  · exact B2270683
  · exact B2270687
  · exact B2270691
  · exact B2270695
  · exact B2270699
  · exact B2270703
  · exact B2270707
  · exact B2270711
  · exact B2270715
  · exact B2270719
  · exact B2270723
  · exact B2270727
  · exact B2270731
  · exact B2270735
  · exact B2270739
  · exact B2270743
  · exact B2270747
  · exact B2270751
  · exact B2270755
  · exact B2270759
  · exact B2270763
  · exact B2270767
  · exact B2270771
  · exact B2270775
  · exact B2270779
  · exact B2270783
  · exact B2270787
  · exact B2270791
  · exact B2270795
  · exact B2270799
  · exact B2270803
  · exact B2270807
  · exact B2270811
  · exact B2270815
  · exact B2270819
  · exact B2270823
  · exact B2270827
  · exact B2270831
  · exact B2270835
  · exact B2270839
  · exact B2270843
  · exact B2270847
  · exact B2270851
  · exact B2270855
  · exact B2270859
  · exact B2270863
  · exact B2270867
  · exact B2270871
  · exact B2270875
  · exact B2270879
  · exact B2270883
  · exact B2270887
  · exact B2270891
  · exact B2270895
  · exact B2270899
  · exact B2270903
  · exact B2270907
  · exact B2270911
  · exact B2270915
  · exact B2270919
  · exact B2270923
  · exact B2270927
  · exact B2270931
  · exact B2270935
  · exact B2270939
  · exact B2270943
  · exact B2270947
  · exact B2270951
  · exact B2270955
  · exact B2270959
  · exact B2270963
  · exact B2270967
  · exact B2270971
  · exact B2270975
  · exact B2270979
  · exact B2270983
  · exact B2270987
  · exact B2270991
  · exact B2270995
  · exact B2270999
  · exact B2271003
  · exact B2271007
  · exact B2271011
  · exact B2271015
  · exact B2271019
  · exact B2271023
  · exact B2271027
  · exact B2271031
  · exact B2271035
  · exact B2271039
  · exact B2271043
  · exact B2271047
  · exact B2271051
  · exact B2271055
  · exact B2271059
  · exact B2271063
  · exact B2271067
  · exact B2271071
  · exact B2271075
  · exact B2271079
  · exact B2271083
  · exact B2271087
  · exact B2271091
  · exact B2271095
  · exact B2271099
  · exact B2271103
  · exact B2271107
  · exact B2271111
  · exact B2271115
  · exact B2271119
  · exact B2271123
  · exact B2271127
  · exact B2271131
  · exact B2271135
  · exact B2271139
  · exact B2271143
  · exact B2271147
  · exact B2271151
  · exact B2271155
  · exact B2271159
  · exact B2271163
  · exact B2271167
  · exact B2271171
  · exact B2271175
  · exact B2271179
  · exact B2271183
  · exact B2271187
  · exact B2271191
  · exact B2271195
  · exact B2271199
  · exact B2271203
  · exact B2271207
  · exact B2271211
  · exact B2271215
  · exact B2271219
  · exact B2271223
  · exact B2271227
  · exact B2271231
  · exact B2271235
  · exact B2271239
  · exact B2271243
  · exact B2271247
  · exact B2271251
  · exact B2271255
  · exact B2271259
  · exact B2271263
  · exact B2271267
  · exact B2271271
  · exact B2271275
  · exact B2271279
  · exact B2271283
  · exact B2271287
  · exact B2271291
  · exact B2271295
  · exact B2271299
  · exact B2271303
  · exact B2271307
  · exact B2271311
  · exact B2271315
  · exact B2271319
  · exact B2271323
  · exact B2271327
  · exact B2271331
  · exact B2271335
  · exact B2271339
  · exact B2271343
  · exact B2271347
  · exact B2271351
  · exact B2271355
  · exact B2271359
  · exact B2271363
  · exact B2271367
  · exact B2271371
  · exact B2271375
  · exact B2271379
  · exact B2271383
  · exact B2271387
  · exact B2271391
  · exact B2271395
  · exact B2271399
  · exact B2271403
  · exact B2271407
  · exact B2271411
  · exact B2271415
  · exact B2271419
  · exact B2271423
  · exact B2271427
  · exact B2271431
  · exact B2271435
theorem solution (m : ℕ) (hlo : 2269435 ≤ m) (hhi : m ≤ 2271435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 567358 ≤ j := by omega
    have hj2 : j ≤ 567858 := by omega
    have hb : Blo 2269435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
