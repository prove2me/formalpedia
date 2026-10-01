-- Prove2me | solution 1 for syracuse_descends_range_2013435_2015435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:45.091432+00:00
-- url     : https://prove2.me/submissions/83a1a334-c0bc-450d-947e-88eeadc3dd30

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

theorem B2296021 : Blo 2013435 2296021 := bbase (se 7 (by rfl) ⟨26906, by rfl⟩ : syracuseStep 2296021 = 53813) (by norm_num)
theorem B3061361 : Blo 2013435 3061361 := bstep (se 2 (by rfl) ⟨1148010, by rfl⟩ : syracuseStep 3061361 = 2296021) B2296021
theorem B2040907 : Blo 2013435 2040907 := bstep (se 1 (by rfl) ⟨1530680, by rfl⟩ : syracuseStep 2040907 = 3061361) B3061361
theorem B2721209 : Blo 2013435 2721209 := bstep (se 2 (by rfl) ⟨1020453, by rfl⟩ : syracuseStep 2721209 = 2040907) B2040907
theorem B7256557 : Blo 2013435 7256557 := bstep (se 3 (by rfl) ⟨1360604, by rfl⟩ : syracuseStep 7256557 = 2721209) B2721209
theorem B9675409 : Blo 2013435 9675409 := bstep (se 2 (by rfl) ⟨3628278, by rfl⟩ : syracuseStep 9675409 = 7256557) B7256557
theorem B12900545 : Blo 2013435 12900545 := bstep (se 2 (by rfl) ⟨4837704, by rfl⟩ : syracuseStep 12900545 = 9675409) B9675409
theorem B8600363 : Blo 2013435 8600363 := bstep (se 1 (by rfl) ⟨6450272, by rfl⟩ : syracuseStep 8600363 = 12900545) B12900545
theorem B5733575 : Blo 2013435 5733575 := bstep (se 1 (by rfl) ⟨4300181, by rfl⟩ : syracuseStep 5733575 = 8600363) B8600363
theorem B3822383 : Blo 2013435 3822383 := bstep (se 1 (by rfl) ⟨2866787, by rfl⟩ : syracuseStep 3822383 = 5733575) B5733575
theorem B2548255 : Blo 2013435 2548255 := bstep (se 1 (by rfl) ⟨1911191, by rfl⟩ : syracuseStep 2548255 = 3822383) B3822383
theorem B3397673 : Blo 2013435 3397673 := bstep (se 2 (by rfl) ⟨1274127, by rfl⟩ : syracuseStep 3397673 = 2548255) B2548255
theorem B2265115 : Blo 2013435 2265115 := bstep (se 1 (by rfl) ⟨1698836, by rfl⟩ : syracuseStep 2265115 = 3397673) B3397673
theorem B3020153 : Blo 2013435 3020153 := bstep (se 2 (by rfl) ⟨1132557, by rfl⟩ : syracuseStep 3020153 = 2265115) B2265115
theorem B2013435 : Blo 2013435 2013435 := bstep (se 1 (by rfl) ⟨1510076, by rfl⟩ : syracuseStep 2013435 = 3020153) B3020153
theorem B19614869 : Blo 2013435 19614869 := bbase (se 6 (by rfl) ⟨459723, by rfl⟩ : syracuseStep 19614869 = 919447) (by norm_num)
theorem B13076579 : Blo 2013435 13076579 := bstep (se 1 (by rfl) ⟨9807434, by rfl⟩ : syracuseStep 13076579 = 19614869) B19614869
theorem B8717719 : Blo 2013435 8717719 := bstep (se 1 (by rfl) ⟨6538289, by rfl⟩ : syracuseStep 8717719 = 13076579) B13076579
theorem B11623625 : Blo 2013435 11623625 := bstep (se 2 (by rfl) ⟨4358859, by rfl⟩ : syracuseStep 11623625 = 8717719) B8717719
theorem B7749083 : Blo 2013435 7749083 := bstep (se 1 (by rfl) ⟨5811812, by rfl⟩ : syracuseStep 7749083 = 11623625) B11623625
theorem B5166055 : Blo 2013435 5166055 := bstep (se 1 (by rfl) ⟨3874541, by rfl⟩ : syracuseStep 5166055 = 7749083) B7749083
theorem B6888073 : Blo 2013435 6888073 := bstep (se 2 (by rfl) ⟨2583027, by rfl⟩ : syracuseStep 6888073 = 5166055) B5166055
theorem B9184097 : Blo 2013435 9184097 := bstep (se 2 (by rfl) ⟨3444036, by rfl⟩ : syracuseStep 9184097 = 6888073) B6888073
theorem B6122731 : Blo 2013435 6122731 := bstep (se 1 (by rfl) ⟨4592048, by rfl⟩ : syracuseStep 6122731 = 9184097) B9184097
theorem B8163641 : Blo 2013435 8163641 := bstep (se 2 (by rfl) ⟨3061365, by rfl⟩ : syracuseStep 8163641 = 6122731) B6122731
theorem B5442427 : Blo 2013435 5442427 := bstep (se 1 (by rfl) ⟨4081820, by rfl⟩ : syracuseStep 5442427 = 8163641) B8163641
theorem B7256569 : Blo 2013435 7256569 := bstep (se 2 (by rfl) ⟨2721213, by rfl⟩ : syracuseStep 7256569 = 5442427) B5442427
theorem B9675425 : Blo 2013435 9675425 := bstep (se 2 (by rfl) ⟨3628284, by rfl⟩ : syracuseStep 9675425 = 7256569) B7256569
theorem B6450283 : Blo 2013435 6450283 := bstep (se 1 (by rfl) ⟨4837712, by rfl⟩ : syracuseStep 6450283 = 9675425) B9675425
theorem B34401509 : Blo 2013435 34401509 := bstep (se 4 (by rfl) ⟨3225141, by rfl⟩ : syracuseStep 34401509 = 6450283) B6450283
theorem B22934339 : Blo 2013435 22934339 := bstep (se 1 (by rfl) ⟨17200754, by rfl⟩ : syracuseStep 22934339 = 34401509) B34401509
theorem B15289559 : Blo 2013435 15289559 := bstep (se 1 (by rfl) ⟨11467169, by rfl⟩ : syracuseStep 15289559 = 22934339) B22934339
theorem B10193039 : Blo 2013435 10193039 := bstep (se 1 (by rfl) ⟨7644779, by rfl⟩ : syracuseStep 10193039 = 15289559) B15289559
theorem B6795359 : Blo 2013435 6795359 := bstep (se 1 (by rfl) ⟨5096519, by rfl⟩ : syracuseStep 6795359 = 10193039) B10193039
theorem B4530239 : Blo 2013435 4530239 := bstep (se 1 (by rfl) ⟨3397679, by rfl⟩ : syracuseStep 4530239 = 6795359) B6795359
theorem B3020159 : Blo 2013435 3020159 := bstep (se 1 (by rfl) ⟨2265119, by rfl⟩ : syracuseStep 3020159 = 4530239) B4530239
theorem B2013439 : Blo 2013435 2013439 := bstep (se 1 (by rfl) ⟨1510079, by rfl⟩ : syracuseStep 2013439 = 3020159) B3020159
theorem B3020165 : Blo 2013435 3020165 := bbase (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) (by norm_num)
theorem B2013443 : Blo 2013435 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B3397693 : Blo 2013435 3397693 := bbase (se 3 (by rfl) ⟨637067, by rfl⟩ : syracuseStep 3397693 = 1274135) (by norm_num)
theorem B4530257 : Blo 2013435 4530257 := bstep (se 2 (by rfl) ⟨1698846, by rfl⟩ : syracuseStep 4530257 = 3397693) B3397693
theorem B3020171 : Blo 2013435 3020171 := bstep (se 1 (by rfl) ⟨2265128, by rfl⟩ : syracuseStep 3020171 = 4530257) B4530257
theorem B2013447 : Blo 2013435 2013447 := bstep (se 1 (by rfl) ⟨1510085, by rfl⟩ : syracuseStep 2013447 = 3020171) B3020171
theorem B2265133 : Blo 2013435 2265133 := bbase (se 3 (by rfl) ⟨424712, by rfl⟩ : syracuseStep 2265133 = 849425) (by norm_num)
theorem B3020177 : Blo 2013435 3020177 := bstep (se 2 (by rfl) ⟨1132566, by rfl⟩ : syracuseStep 3020177 = 2265133) B2265133
theorem B2013451 : Blo 2013435 2013451 := bstep (se 1 (by rfl) ⟨1510088, by rfl⟩ : syracuseStep 2013451 = 3020177) B3020177
theorem B6795413 : Blo 2013435 6795413 := bbase (se 6 (by rfl) ⟨159267, by rfl⟩ : syracuseStep 6795413 = 318535) (by norm_num)
theorem B4530275 : Blo 2013435 4530275 := bstep (se 1 (by rfl) ⟨3397706, by rfl⟩ : syracuseStep 4530275 = 6795413) B6795413
theorem B3020183 : Blo 2013435 3020183 := bstep (se 1 (by rfl) ⟨2265137, by rfl⟩ : syracuseStep 3020183 = 4530275) B4530275
theorem B2013455 : Blo 2013435 2013455 := bstep (se 1 (by rfl) ⟨1510091, by rfl⟩ : syracuseStep 2013455 = 3020183) B3020183
theorem B3020189 : Blo 2013435 3020189 := bbase (se 3 (by rfl) ⟨566285, by rfl⟩ : syracuseStep 3020189 = 1132571) (by norm_num)
theorem B2013459 : Blo 2013435 2013459 := bstep (se 1 (by rfl) ⟨1510094, by rfl⟩ : syracuseStep 2013459 = 3020189) B3020189
theorem B4530293 : Blo 2013435 4530293 := bbase (se 5 (by rfl) ⟨212357, by rfl⟩ : syracuseStep 4530293 = 424715) (by norm_num)
theorem B3020195 : Blo 2013435 3020195 := bstep (se 1 (by rfl) ⟨2265146, by rfl⟩ : syracuseStep 3020195 = 4530293) B4530293
theorem B2013463 : Blo 2013435 2013463 := bstep (se 1 (by rfl) ⟨1510097, by rfl⟩ : syracuseStep 2013463 = 3020195) B3020195
theorem B4837781 : Blo 2013435 4837781 := bbase (se 6 (by rfl) ⟨113385, by rfl⟩ : syracuseStep 4837781 = 226771) (by norm_num)
theorem B3225187 : Blo 2013435 3225187 := bstep (se 1 (by rfl) ⟨2418890, by rfl⟩ : syracuseStep 3225187 = 4837781) B4837781
theorem B17200997 : Blo 2013435 17200997 := bstep (se 4 (by rfl) ⟨1612593, by rfl⟩ : syracuseStep 17200997 = 3225187) B3225187
theorem B11467331 : Blo 2013435 11467331 := bstep (se 1 (by rfl) ⟨8600498, by rfl⟩ : syracuseStep 11467331 = 17200997) B17200997
theorem B7644887 : Blo 2013435 7644887 := bstep (se 1 (by rfl) ⟨5733665, by rfl⟩ : syracuseStep 7644887 = 11467331) B11467331
theorem B5096591 : Blo 2013435 5096591 := bstep (se 1 (by rfl) ⟨3822443, by rfl⟩ : syracuseStep 5096591 = 7644887) B7644887
theorem B3397727 : Blo 2013435 3397727 := bstep (se 1 (by rfl) ⟨2548295, by rfl⟩ : syracuseStep 3397727 = 5096591) B5096591
theorem B2265151 : Blo 2013435 2265151 := bstep (se 1 (by rfl) ⟨1698863, by rfl⟩ : syracuseStep 2265151 = 3397727) B3397727
theorem B3020201 : Blo 2013435 3020201 := bstep (se 2 (by rfl) ⟨1132575, by rfl⟩ : syracuseStep 3020201 = 2265151) B2265151
theorem B2013467 : Blo 2013435 2013467 := bstep (se 1 (by rfl) ⟨1510100, by rfl⟩ : syracuseStep 2013467 = 3020201) B3020201
theorem B7644901 : Blo 2013435 7644901 := bbase (se 4 (by rfl) ⟨716709, by rfl⟩ : syracuseStep 7644901 = 1433419) (by norm_num)
theorem B10193201 : Blo 2013435 10193201 := bstep (se 2 (by rfl) ⟨3822450, by rfl⟩ : syracuseStep 10193201 = 7644901) B7644901
theorem B6795467 : Blo 2013435 6795467 := bstep (se 1 (by rfl) ⟨5096600, by rfl⟩ : syracuseStep 6795467 = 10193201) B10193201
theorem B4530311 : Blo 2013435 4530311 := bstep (se 1 (by rfl) ⟨3397733, by rfl⟩ : syracuseStep 4530311 = 6795467) B6795467
theorem B3020207 : Blo 2013435 3020207 := bstep (se 1 (by rfl) ⟨2265155, by rfl⟩ : syracuseStep 3020207 = 4530311) B4530311
theorem B2013471 : Blo 2013435 2013471 := bstep (se 1 (by rfl) ⟨1510103, by rfl⟩ : syracuseStep 2013471 = 3020207) B3020207
theorem B3020213 : Blo 2013435 3020213 := bbase (se 5 (by rfl) ⟨141572, by rfl⟩ : syracuseStep 3020213 = 283145) (by norm_num)
theorem B2013475 : Blo 2013435 2013475 := bstep (se 1 (by rfl) ⟨1510106, by rfl⟩ : syracuseStep 2013475 = 3020213) B3020213
theorem B5096621 : Blo 2013435 5096621 := bbase (se 3 (by rfl) ⟨955616, by rfl⟩ : syracuseStep 5096621 = 1911233) (by norm_num)
theorem B3397747 : Blo 2013435 3397747 := bstep (se 1 (by rfl) ⟨2548310, by rfl⟩ : syracuseStep 3397747 = 5096621) B5096621
theorem B4530329 : Blo 2013435 4530329 := bstep (se 2 (by rfl) ⟨1698873, by rfl⟩ : syracuseStep 4530329 = 3397747) B3397747
theorem B3020219 : Blo 2013435 3020219 := bstep (se 1 (by rfl) ⟨2265164, by rfl⟩ : syracuseStep 3020219 = 4530329) B4530329
theorem B2013479 : Blo 2013435 2013479 := bstep (se 1 (by rfl) ⟨1510109, by rfl⟩ : syracuseStep 2013479 = 3020219) B3020219
theorem B2265169 : Blo 2013435 2265169 := bbase (se 2 (by rfl) ⟨849438, by rfl⟩ : syracuseStep 2265169 = 1698877) (by norm_num)
theorem B3020225 : Blo 2013435 3020225 := bstep (se 2 (by rfl) ⟨1132584, by rfl⟩ : syracuseStep 3020225 = 2265169) B2265169
theorem B2013483 : Blo 2013435 2013483 := bstep (se 1 (by rfl) ⟨1510112, by rfl⟩ : syracuseStep 2013483 = 3020225) B3020225
theorem B2866861 : Blo 2013435 2866861 := bbase (se 3 (by rfl) ⟨537536, by rfl⟩ : syracuseStep 2866861 = 1075073) (by norm_num)
theorem B3822481 : Blo 2013435 3822481 := bstep (se 2 (by rfl) ⟨1433430, by rfl⟩ : syracuseStep 3822481 = 2866861) B2866861
theorem B5096641 : Blo 2013435 5096641 := bstep (se 2 (by rfl) ⟨1911240, by rfl⟩ : syracuseStep 5096641 = 3822481) B3822481
theorem B6795521 : Blo 2013435 6795521 := bstep (se 2 (by rfl) ⟨2548320, by rfl⟩ : syracuseStep 6795521 = 5096641) B5096641
theorem B4530347 : Blo 2013435 4530347 := bstep (se 1 (by rfl) ⟨3397760, by rfl⟩ : syracuseStep 4530347 = 6795521) B6795521
theorem B3020231 : Blo 2013435 3020231 := bstep (se 1 (by rfl) ⟨2265173, by rfl⟩ : syracuseStep 3020231 = 4530347) B4530347
theorem B2013487 : Blo 2013435 2013487 := bstep (se 1 (by rfl) ⟨1510115, by rfl⟩ : syracuseStep 2013487 = 3020231) B3020231
theorem B3020237 : Blo 2013435 3020237 := bbase (se 3 (by rfl) ⟨566294, by rfl⟩ : syracuseStep 3020237 = 1132589) (by norm_num)
theorem B2013491 : Blo 2013435 2013491 := bstep (se 1 (by rfl) ⟨1510118, by rfl⟩ : syracuseStep 2013491 = 3020237) B3020237
theorem B4530365 : Blo 2013435 4530365 := bbase (se 3 (by rfl) ⟨849443, by rfl⟩ : syracuseStep 4530365 = 1698887) (by norm_num)
theorem B3020243 : Blo 2013435 3020243 := bstep (se 1 (by rfl) ⟨2265182, by rfl⟩ : syracuseStep 3020243 = 4530365) B4530365
theorem B2013495 : Blo 2013435 2013495 := bstep (se 1 (by rfl) ⟨1510121, by rfl⟩ : syracuseStep 2013495 = 3020243) B3020243
theorem B3397781 : Blo 2013435 3397781 := bbase (se 6 (by rfl) ⟨79635, by rfl⟩ : syracuseStep 3397781 = 159271) (by norm_num)
theorem B2265187 : Blo 2013435 2265187 := bstep (se 1 (by rfl) ⟨1698890, by rfl⟩ : syracuseStep 2265187 = 3397781) B3397781
theorem B3020249 : Blo 2013435 3020249 := bstep (se 2 (by rfl) ⟨1132593, by rfl⟩ : syracuseStep 3020249 = 2265187) B2265187
theorem B2013499 : Blo 2013435 2013499 := bstep (se 1 (by rfl) ⟨1510124, by rfl⟩ : syracuseStep 2013499 = 3020249) B3020249
theorem B9675733 : Blo 2013435 9675733 := bbase (se 7 (by rfl) ⟨113387, by rfl⟩ : syracuseStep 9675733 = 226775) (by norm_num)
theorem B12900977 : Blo 2013435 12900977 := bstep (se 2 (by rfl) ⟨4837866, by rfl⟩ : syracuseStep 12900977 = 9675733) B9675733
theorem B8600651 : Blo 2013435 8600651 := bstep (se 1 (by rfl) ⟨6450488, by rfl⟩ : syracuseStep 8600651 = 12900977) B12900977
theorem B5733767 : Blo 2013435 5733767 := bstep (se 1 (by rfl) ⟨4300325, by rfl⟩ : syracuseStep 5733767 = 8600651) B8600651
theorem B15290045 : Blo 2013435 15290045 := bstep (se 3 (by rfl) ⟨2866883, by rfl⟩ : syracuseStep 15290045 = 5733767) B5733767
theorem B10193363 : Blo 2013435 10193363 := bstep (se 1 (by rfl) ⟨7645022, by rfl⟩ : syracuseStep 10193363 = 15290045) B15290045
theorem B6795575 : Blo 2013435 6795575 := bstep (se 1 (by rfl) ⟨5096681, by rfl⟩ : syracuseStep 6795575 = 10193363) B10193363
theorem B4530383 : Blo 2013435 4530383 := bstep (se 1 (by rfl) ⟨3397787, by rfl⟩ : syracuseStep 4530383 = 6795575) B6795575
theorem B3020255 : Blo 2013435 3020255 := bstep (se 1 (by rfl) ⟨2265191, by rfl⟩ : syracuseStep 3020255 = 4530383) B4530383
theorem B2013503 : Blo 2013435 2013503 := bstep (se 1 (by rfl) ⟨1510127, by rfl⟩ : syracuseStep 2013503 = 3020255) B3020255
theorem B3020261 : Blo 2013435 3020261 := bbase (se 4 (by rfl) ⟨283149, by rfl⟩ : syracuseStep 3020261 = 566299) (by norm_num)
theorem B2013507 : Blo 2013435 2013507 := bstep (se 1 (by rfl) ⟨1510130, by rfl⟩ : syracuseStep 2013507 = 3020261) B3020261
theorem B16141781 : Blo 2013435 16141781 := bbase (se 7 (by rfl) ⟨189161, by rfl⟩ : syracuseStep 16141781 = 378323) (by norm_num)
theorem B10761187 : Blo 2013435 10761187 := bstep (se 1 (by rfl) ⟨8070890, by rfl⟩ : syracuseStep 10761187 = 16141781) B16141781
theorem B14348249 : Blo 2013435 14348249 := bstep (se 2 (by rfl) ⟨5380593, by rfl⟩ : syracuseStep 14348249 = 10761187) B10761187
theorem B9565499 : Blo 2013435 9565499 := bstep (se 1 (by rfl) ⟨7174124, by rfl⟩ : syracuseStep 9565499 = 14348249) B14348249
theorem B25507997 : Blo 2013435 25507997 := bstep (se 3 (by rfl) ⟨4782749, by rfl⟩ : syracuseStep 25507997 = 9565499) B9565499
theorem B17005331 : Blo 2013435 17005331 := bstep (se 1 (by rfl) ⟨12753998, by rfl⟩ : syracuseStep 17005331 = 25507997) B25507997
theorem B11336887 : Blo 2013435 11336887 := bstep (se 1 (by rfl) ⟨8502665, by rfl⟩ : syracuseStep 11336887 = 17005331) B17005331
theorem B60463397 : Blo 2013435 60463397 := bstep (se 4 (by rfl) ⟨5668443, by rfl⟩ : syracuseStep 60463397 = 11336887) B11336887
theorem B40308931 : Blo 2013435 40308931 := bstep (se 1 (by rfl) ⟨30231698, by rfl⟩ : syracuseStep 40308931 = 60463397) B60463397
theorem B53745241 : Blo 2013435 53745241 := bstep (se 2 (by rfl) ⟨20154465, by rfl⟩ : syracuseStep 53745241 = 40308931) B40308931
theorem B71660321 : Blo 2013435 71660321 := bstep (se 2 (by rfl) ⟨26872620, by rfl⟩ : syracuseStep 71660321 = 53745241) B53745241
theorem B47773547 : Blo 2013435 47773547 := bstep (se 1 (by rfl) ⟨35830160, by rfl⟩ : syracuseStep 47773547 = 71660321) B71660321
theorem B31849031 : Blo 2013435 31849031 := bstep (se 1 (by rfl) ⟨23886773, by rfl⟩ : syracuseStep 31849031 = 47773547) B47773547
theorem B21232687 : Blo 2013435 21232687 := bstep (se 1 (by rfl) ⟨15924515, by rfl⟩ : syracuseStep 21232687 = 31849031) B31849031
theorem B28310249 : Blo 2013435 28310249 := bstep (se 2 (by rfl) ⟨10616343, by rfl⟩ : syracuseStep 28310249 = 21232687) B21232687
theorem B18873499 : Blo 2013435 18873499 := bstep (se 1 (by rfl) ⟨14155124, by rfl⟩ : syracuseStep 18873499 = 28310249) B28310249
theorem B25164665 : Blo 2013435 25164665 := bstep (se 2 (by rfl) ⟨9436749, by rfl⟩ : syracuseStep 25164665 = 18873499) B18873499
theorem B16776443 : Blo 2013435 16776443 := bstep (se 1 (by rfl) ⟨12582332, by rfl⟩ : syracuseStep 16776443 = 25164665) B25164665
theorem B44737181 : Blo 2013435 44737181 := bstep (se 3 (by rfl) ⟨8388221, by rfl⟩ : syracuseStep 44737181 = 16776443) B16776443
theorem B29824787 : Blo 2013435 29824787 := bstep (se 1 (by rfl) ⟨22368590, by rfl⟩ : syracuseStep 29824787 = 44737181) B44737181
theorem B19883191 : Blo 2013435 19883191 := bstep (se 1 (by rfl) ⟨14912393, by rfl⟩ : syracuseStep 19883191 = 29824787) B29824787
theorem B26510921 : Blo 2013435 26510921 := bstep (se 2 (by rfl) ⟨9941595, by rfl⟩ : syracuseStep 26510921 = 19883191) B19883191
theorem B17673947 : Blo 2013435 17673947 := bstep (se 1 (by rfl) ⟨13255460, by rfl⟩ : syracuseStep 17673947 = 26510921) B26510921
theorem B11782631 : Blo 2013435 11782631 := bstep (se 1 (by rfl) ⟨8836973, by rfl⟩ : syracuseStep 11782631 = 17673947) B17673947
theorem B7855087 : Blo 2013435 7855087 := bstep (se 1 (by rfl) ⟨5891315, by rfl⟩ : syracuseStep 7855087 = 11782631) B11782631
theorem B10473449 : Blo 2013435 10473449 := bstep (se 2 (by rfl) ⟨3927543, by rfl⟩ : syracuseStep 10473449 = 7855087) B7855087
theorem B27929197 : Blo 2013435 27929197 := bstep (se 3 (by rfl) ⟨5236724, by rfl⟩ : syracuseStep 27929197 = 10473449) B10473449
theorem B37238929 : Blo 2013435 37238929 := bstep (se 2 (by rfl) ⟨13964598, by rfl⟩ : syracuseStep 37238929 = 27929197) B27929197
theorem B198607621 : Blo 2013435 198607621 := bstep (se 4 (by rfl) ⟨18619464, by rfl⟩ : syracuseStep 198607621 = 37238929) B37238929
theorem B264810161 : Blo 2013435 264810161 := bstep (se 2 (by rfl) ⟨99303810, by rfl⟩ : syracuseStep 264810161 = 198607621) B198607621
theorem B706160429 : Blo 2013435 706160429 := bstep (se 3 (by rfl) ⟨132405080, by rfl⟩ : syracuseStep 706160429 = 264810161) B264810161
theorem B470773619 : Blo 2013435 470773619 := bstep (se 1 (by rfl) ⟨353080214, by rfl⟩ : syracuseStep 470773619 = 706160429) B706160429
theorem B313849079 : Blo 2013435 313849079 := bstep (se 1 (by rfl) ⟨235386809, by rfl⟩ : syracuseStep 313849079 = 470773619) B470773619
theorem B209232719 : Blo 2013435 209232719 := bstep (se 1 (by rfl) ⟨156924539, by rfl⟩ : syracuseStep 209232719 = 313849079) B313849079
theorem B139488479 : Blo 2013435 139488479 := bstep (se 1 (by rfl) ⟨104616359, by rfl⟩ : syracuseStep 139488479 = 209232719) B209232719
theorem B92992319 : Blo 2013435 92992319 := bstep (se 1 (by rfl) ⟨69744239, by rfl⟩ : syracuseStep 92992319 = 139488479) B139488479
theorem B61994879 : Blo 2013435 61994879 := bstep (se 1 (by rfl) ⟨46496159, by rfl⟩ : syracuseStep 61994879 = 92992319) B92992319
theorem B41329919 : Blo 2013435 41329919 := bstep (se 1 (by rfl) ⟨30997439, by rfl⟩ : syracuseStep 41329919 = 61994879) B61994879
theorem B27553279 : Blo 2013435 27553279 := bstep (se 1 (by rfl) ⟨20664959, by rfl⟩ : syracuseStep 27553279 = 41329919) B41329919
theorem B36737705 : Blo 2013435 36737705 := bstep (se 2 (by rfl) ⟨13776639, by rfl⟩ : syracuseStep 36737705 = 27553279) B27553279
theorem B24491803 : Blo 2013435 24491803 := bstep (se 1 (by rfl) ⟨18368852, by rfl⟩ : syracuseStep 24491803 = 36737705) B36737705
theorem B32655737 : Blo 2013435 32655737 := bstep (se 2 (by rfl) ⟨12245901, by rfl⟩ : syracuseStep 32655737 = 24491803) B24491803
theorem B21770491 : Blo 2013435 21770491 := bstep (se 1 (by rfl) ⟨16327868, by rfl⟩ : syracuseStep 21770491 = 32655737) B32655737
theorem B29027321 : Blo 2013435 29027321 := bstep (se 2 (by rfl) ⟨10885245, by rfl⟩ : syracuseStep 29027321 = 21770491) B21770491
theorem B19351547 : Blo 2013435 19351547 := bstep (se 1 (by rfl) ⟨14513660, by rfl⟩ : syracuseStep 19351547 = 29027321) B29027321
theorem B12901031 : Blo 2013435 12901031 := bstep (se 1 (by rfl) ⟨9675773, by rfl⟩ : syracuseStep 12901031 = 19351547) B19351547
theorem B8600687 : Blo 2013435 8600687 := bstep (se 1 (by rfl) ⟨6450515, by rfl⟩ : syracuseStep 8600687 = 12901031) B12901031
theorem B5733791 : Blo 2013435 5733791 := bstep (se 1 (by rfl) ⟨4300343, by rfl⟩ : syracuseStep 5733791 = 8600687) B8600687
theorem B3822527 : Blo 2013435 3822527 := bstep (se 1 (by rfl) ⟨2866895, by rfl⟩ : syracuseStep 3822527 = 5733791) B5733791
theorem B2548351 : Blo 2013435 2548351 := bstep (se 1 (by rfl) ⟨1911263, by rfl⟩ : syracuseStep 2548351 = 3822527) B3822527
theorem B3397801 : Blo 2013435 3397801 := bstep (se 2 (by rfl) ⟨1274175, by rfl⟩ : syracuseStep 3397801 = 2548351) B2548351
theorem B4530401 : Blo 2013435 4530401 := bstep (se 2 (by rfl) ⟨1698900, by rfl⟩ : syracuseStep 4530401 = 3397801) B3397801
theorem B3020267 : Blo 2013435 3020267 := bstep (se 1 (by rfl) ⟨2265200, by rfl⟩ : syracuseStep 3020267 = 4530401) B4530401
theorem B2013511 : Blo 2013435 2013511 := bstep (se 1 (by rfl) ⟨1510133, by rfl⟩ : syracuseStep 2013511 = 3020267) B3020267
theorem B2265205 : Blo 2013435 2265205 := bbase (se 5 (by rfl) ⟨106181, by rfl⟩ : syracuseStep 2265205 = 212363) (by norm_num)
theorem B3020273 : Blo 2013435 3020273 := bstep (se 2 (by rfl) ⟨1132602, by rfl⟩ : syracuseStep 3020273 = 2265205) B2265205
theorem B2013515 : Blo 2013435 2013515 := bstep (se 1 (by rfl) ⟨1510136, by rfl⟩ : syracuseStep 2013515 = 3020273) B3020273
theorem B2548361 : Blo 2013435 2548361 := bbase (se 2 (by rfl) ⟨955635, by rfl⟩ : syracuseStep 2548361 = 1911271) (by norm_num)
theorem B6795629 : Blo 2013435 6795629 := bstep (se 3 (by rfl) ⟨1274180, by rfl⟩ : syracuseStep 6795629 = 2548361) B2548361
theorem B4530419 : Blo 2013435 4530419 := bstep (se 1 (by rfl) ⟨3397814, by rfl⟩ : syracuseStep 4530419 = 6795629) B6795629
theorem B3020279 : Blo 2013435 3020279 := bstep (se 1 (by rfl) ⟨2265209, by rfl⟩ : syracuseStep 3020279 = 4530419) B4530419
theorem B2013519 : Blo 2013435 2013519 := bstep (se 1 (by rfl) ⟨1510139, by rfl⟩ : syracuseStep 2013519 = 3020279) B3020279
theorem B3020285 : Blo 2013435 3020285 := bbase (se 3 (by rfl) ⟨566303, by rfl⟩ : syracuseStep 3020285 = 1132607) (by norm_num)
theorem B2013523 : Blo 2013435 2013523 := bstep (se 1 (by rfl) ⟨1510142, by rfl⟩ : syracuseStep 2013523 = 3020285) B3020285
theorem B4530437 : Blo 2013435 4530437 := bbase (se 4 (by rfl) ⟨424728, by rfl⟩ : syracuseStep 4530437 = 849457) (by norm_num)
theorem B3020291 : Blo 2013435 3020291 := bstep (se 1 (by rfl) ⟨2265218, by rfl⟩ : syracuseStep 3020291 = 4530437) B4530437
theorem B2013527 : Blo 2013435 2013527 := bstep (se 1 (by rfl) ⟨1510145, by rfl⟩ : syracuseStep 2013527 = 3020291) B3020291
theorem B3822565 : Blo 2013435 3822565 := bbase (se 4 (by rfl) ⟨358365, by rfl⟩ : syracuseStep 3822565 = 716731) (by norm_num)
theorem B5096753 : Blo 2013435 5096753 := bstep (se 2 (by rfl) ⟨1911282, by rfl⟩ : syracuseStep 5096753 = 3822565) B3822565
theorem B3397835 : Blo 2013435 3397835 := bstep (se 1 (by rfl) ⟨2548376, by rfl⟩ : syracuseStep 3397835 = 5096753) B5096753
theorem B2265223 : Blo 2013435 2265223 := bstep (se 1 (by rfl) ⟨1698917, by rfl⟩ : syracuseStep 2265223 = 3397835) B3397835
theorem B3020297 : Blo 2013435 3020297 := bstep (se 2 (by rfl) ⟨1132611, by rfl⟩ : syracuseStep 3020297 = 2265223) B2265223
theorem B2013531 : Blo 2013435 2013531 := bstep (se 1 (by rfl) ⟨1510148, by rfl⟩ : syracuseStep 2013531 = 3020297) B3020297
theorem B10193525 : Blo 2013435 10193525 := bbase (se 5 (by rfl) ⟨477821, by rfl⟩ : syracuseStep 10193525 = 955643) (by norm_num)
theorem B6795683 : Blo 2013435 6795683 := bstep (se 1 (by rfl) ⟨5096762, by rfl⟩ : syracuseStep 6795683 = 10193525) B10193525
theorem B4530455 : Blo 2013435 4530455 := bstep (se 1 (by rfl) ⟨3397841, by rfl⟩ : syracuseStep 4530455 = 6795683) B6795683
theorem B3020303 : Blo 2013435 3020303 := bstep (se 1 (by rfl) ⟨2265227, by rfl⟩ : syracuseStep 3020303 = 4530455) B4530455
theorem B2013535 : Blo 2013435 2013535 := bstep (se 1 (by rfl) ⟨1510151, by rfl⟩ : syracuseStep 2013535 = 3020303) B3020303
theorem B3020309 : Blo 2013435 3020309 := bbase (se 6 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 3020309 = 141577) (by norm_num)
theorem B2013539 : Blo 2013435 2013539 := bstep (se 1 (by rfl) ⟨1510154, by rfl⟩ : syracuseStep 2013539 = 3020309) B3020309
theorem B5442709 : Blo 2013435 5442709 := bbase (se 6 (by rfl) ⟨127563, by rfl⟩ : syracuseStep 5442709 = 255127) (by norm_num)
theorem B7256945 : Blo 2013435 7256945 := bstep (se 2 (by rfl) ⟨2721354, by rfl⟩ : syracuseStep 7256945 = 5442709) B5442709
theorem B4837963 : Blo 2013435 4837963 := bstep (se 1 (by rfl) ⟨3628472, by rfl⟩ : syracuseStep 4837963 = 7256945) B7256945
theorem B6450617 : Blo 2013435 6450617 := bstep (se 2 (by rfl) ⟨2418981, by rfl⟩ : syracuseStep 6450617 = 4837963) B4837963
theorem B17201645 : Blo 2013435 17201645 := bstep (se 3 (by rfl) ⟨3225308, by rfl⟩ : syracuseStep 17201645 = 6450617) B6450617
theorem B11467763 : Blo 2013435 11467763 := bstep (se 1 (by rfl) ⟨8600822, by rfl⟩ : syracuseStep 11467763 = 17201645) B17201645
theorem B7645175 : Blo 2013435 7645175 := bstep (se 1 (by rfl) ⟨5733881, by rfl⟩ : syracuseStep 7645175 = 11467763) B11467763
theorem B5096783 : Blo 2013435 5096783 := bstep (se 1 (by rfl) ⟨3822587, by rfl⟩ : syracuseStep 5096783 = 7645175) B7645175
theorem B3397855 : Blo 2013435 3397855 := bstep (se 1 (by rfl) ⟨2548391, by rfl⟩ : syracuseStep 3397855 = 5096783) B5096783
theorem B4530473 : Blo 2013435 4530473 := bstep (se 2 (by rfl) ⟨1698927, by rfl⟩ : syracuseStep 4530473 = 3397855) B3397855
theorem B3020315 : Blo 2013435 3020315 := bstep (se 1 (by rfl) ⟨2265236, by rfl⟩ : syracuseStep 3020315 = 4530473) B4530473
theorem B2013543 : Blo 2013435 2013543 := bstep (se 1 (by rfl) ⟨1510157, by rfl⟩ : syracuseStep 2013543 = 3020315) B3020315
theorem B2265241 : Blo 2013435 2265241 := bbase (se 2 (by rfl) ⟨849465, by rfl⟩ : syracuseStep 2265241 = 1698931) (by norm_num)
theorem B3020321 : Blo 2013435 3020321 := bstep (se 2 (by rfl) ⟨1132620, by rfl⟩ : syracuseStep 3020321 = 2265241) B2265241
theorem B2013547 : Blo 2013435 2013547 := bstep (se 1 (by rfl) ⟨1510160, by rfl⟩ : syracuseStep 2013547 = 3020321) B3020321
theorem B7645205 : Blo 2013435 7645205 := bbase (se 6 (by rfl) ⟨179184, by rfl⟩ : syracuseStep 7645205 = 358369) (by norm_num)
theorem B5096803 : Blo 2013435 5096803 := bstep (se 1 (by rfl) ⟨3822602, by rfl⟩ : syracuseStep 5096803 = 7645205) B7645205
theorem B6795737 : Blo 2013435 6795737 := bstep (se 2 (by rfl) ⟨2548401, by rfl⟩ : syracuseStep 6795737 = 5096803) B5096803
theorem B4530491 : Blo 2013435 4530491 := bstep (se 1 (by rfl) ⟨3397868, by rfl⟩ : syracuseStep 4530491 = 6795737) B6795737
theorem B3020327 : Blo 2013435 3020327 := bstep (se 1 (by rfl) ⟨2265245, by rfl⟩ : syracuseStep 3020327 = 4530491) B4530491
theorem B2013551 : Blo 2013435 2013551 := bstep (se 1 (by rfl) ⟨1510163, by rfl⟩ : syracuseStep 2013551 = 3020327) B3020327
theorem B3020333 : Blo 2013435 3020333 := bbase (se 3 (by rfl) ⟨566312, by rfl⟩ : syracuseStep 3020333 = 1132625) (by norm_num)
theorem B2013555 : Blo 2013435 2013555 := bstep (se 1 (by rfl) ⟨1510166, by rfl⟩ : syracuseStep 2013555 = 3020333) B3020333
theorem B4530509 : Blo 2013435 4530509 := bbase (se 3 (by rfl) ⟨849470, by rfl⟩ : syracuseStep 4530509 = 1698941) (by norm_num)
theorem B3020339 : Blo 2013435 3020339 := bstep (se 1 (by rfl) ⟨2265254, by rfl⟩ : syracuseStep 3020339 = 4530509) B4530509
theorem B2013559 : Blo 2013435 2013559 := bstep (se 1 (by rfl) ⟨1510169, by rfl⟩ : syracuseStep 2013559 = 3020339) B3020339
theorem B2548417 : Blo 2013435 2548417 := bbase (se 2 (by rfl) ⟨955656, by rfl⟩ : syracuseStep 2548417 = 1911313) (by norm_num)
theorem B3397889 : Blo 2013435 3397889 := bstep (se 2 (by rfl) ⟨1274208, by rfl⟩ : syracuseStep 3397889 = 2548417) B2548417
theorem B2265259 : Blo 2013435 2265259 := bstep (se 1 (by rfl) ⟨1698944, by rfl⟩ : syracuseStep 2265259 = 3397889) B3397889
theorem B3020345 : Blo 2013435 3020345 := bstep (se 2 (by rfl) ⟨1132629, by rfl⟩ : syracuseStep 3020345 = 2265259) B2265259
theorem B2013563 : Blo 2013435 2013563 := bstep (se 1 (by rfl) ⟨1510172, by rfl⟩ : syracuseStep 2013563 = 3020345) B3020345
theorem B4838021 : Blo 2013435 4838021 := bbase (se 4 (by rfl) ⟨453564, by rfl⟩ : syracuseStep 4838021 = 907129) (by norm_num)
theorem B3225347 : Blo 2013435 3225347 := bstep (se 1 (by rfl) ⟨2419010, by rfl⟩ : syracuseStep 3225347 = 4838021) B4838021
theorem B2150231 : Blo 2013435 2150231 := bstep (se 1 (by rfl) ⟨1612673, by rfl⟩ : syracuseStep 2150231 = 3225347) B3225347
theorem B22935797 : Blo 2013435 22935797 := bstep (se 5 (by rfl) ⟨1075115, by rfl⟩ : syracuseStep 22935797 = 2150231) B2150231
theorem B15290531 : Blo 2013435 15290531 := bstep (se 1 (by rfl) ⟨11467898, by rfl⟩ : syracuseStep 15290531 = 22935797) B22935797
theorem B10193687 : Blo 2013435 10193687 := bstep (se 1 (by rfl) ⟨7645265, by rfl⟩ : syracuseStep 10193687 = 15290531) B15290531
theorem B6795791 : Blo 2013435 6795791 := bstep (se 1 (by rfl) ⟨5096843, by rfl⟩ : syracuseStep 6795791 = 10193687) B10193687
theorem B4530527 : Blo 2013435 4530527 := bstep (se 1 (by rfl) ⟨3397895, by rfl⟩ : syracuseStep 4530527 = 6795791) B6795791
theorem B3020351 : Blo 2013435 3020351 := bstep (se 1 (by rfl) ⟨2265263, by rfl⟩ : syracuseStep 3020351 = 4530527) B4530527
theorem B2013567 : Blo 2013435 2013567 := bstep (se 1 (by rfl) ⟨1510175, by rfl⟩ : syracuseStep 2013567 = 3020351) B3020351
theorem B3020357 : Blo 2013435 3020357 := bbase (se 4 (by rfl) ⟨283158, by rfl⟩ : syracuseStep 3020357 = 566317) (by norm_num)
theorem B2013571 : Blo 2013435 2013571 := bstep (se 1 (by rfl) ⟨1510178, by rfl⟩ : syracuseStep 2013571 = 3020357) B3020357
theorem B3397909 : Blo 2013435 3397909 := bbase (se 6 (by rfl) ⟨79638, by rfl⟩ : syracuseStep 3397909 = 159277) (by norm_num)
theorem B4530545 : Blo 2013435 4530545 := bstep (se 2 (by rfl) ⟨1698954, by rfl⟩ : syracuseStep 4530545 = 3397909) B3397909
theorem B3020363 : Blo 2013435 3020363 := bstep (se 1 (by rfl) ⟨2265272, by rfl⟩ : syracuseStep 3020363 = 4530545) B4530545
theorem B2013575 : Blo 2013435 2013575 := bstep (se 1 (by rfl) ⟨1510181, by rfl⟩ : syracuseStep 2013575 = 3020363) B3020363
theorem B2265277 : Blo 2013435 2265277 := bbase (se 3 (by rfl) ⟨424739, by rfl⟩ : syracuseStep 2265277 = 849479) (by norm_num)
theorem B3020369 : Blo 2013435 3020369 := bstep (se 2 (by rfl) ⟨1132638, by rfl⟩ : syracuseStep 3020369 = 2265277) B2265277
theorem B2013579 : Blo 2013435 2013579 := bstep (se 1 (by rfl) ⟨1510184, by rfl⟩ : syracuseStep 2013579 = 3020369) B3020369
theorem B6795845 : Blo 2013435 6795845 := bbase (se 4 (by rfl) ⟨637110, by rfl⟩ : syracuseStep 6795845 = 1274221) (by norm_num)
theorem B4530563 : Blo 2013435 4530563 := bstep (se 1 (by rfl) ⟨3397922, by rfl⟩ : syracuseStep 4530563 = 6795845) B6795845
theorem B3020375 : Blo 2013435 3020375 := bstep (se 1 (by rfl) ⟨2265281, by rfl⟩ : syracuseStep 3020375 = 4530563) B4530563
theorem B2013583 : Blo 2013435 2013583 := bstep (se 1 (by rfl) ⟨1510187, by rfl⟩ : syracuseStep 2013583 = 3020375) B3020375
theorem B3020381 : Blo 2013435 3020381 := bbase (se 3 (by rfl) ⟨566321, by rfl⟩ : syracuseStep 3020381 = 1132643) (by norm_num)
theorem B2013587 : Blo 2013435 2013587 := bstep (se 1 (by rfl) ⟨1510190, by rfl⟩ : syracuseStep 2013587 = 3020381) B3020381
theorem B4530581 : Blo 2013435 4530581 := bbase (se 6 (by rfl) ⟨106185, by rfl⟩ : syracuseStep 4530581 = 212371) (by norm_num)
theorem B3020387 : Blo 2013435 3020387 := bstep (se 1 (by rfl) ⟨2265290, by rfl⟩ : syracuseStep 3020387 = 4530581) B4530581
theorem B2013591 : Blo 2013435 2013591 := bstep (se 1 (by rfl) ⟨1510193, by rfl⟩ : syracuseStep 2013591 = 3020387) B3020387
theorem B8164277 : Blo 2013435 8164277 := bbase (se 5 (by rfl) ⟨382700, by rfl⟩ : syracuseStep 8164277 = 765401) (by norm_num)
theorem B5442851 : Blo 2013435 5442851 := bstep (se 1 (by rfl) ⟨4082138, by rfl⟩ : syracuseStep 5442851 = 8164277) B8164277
theorem B3628567 : Blo 2013435 3628567 := bstep (se 1 (by rfl) ⟨2721425, by rfl⟩ : syracuseStep 3628567 = 5442851) B5442851
theorem B4838089 : Blo 2013435 4838089 := bstep (se 2 (by rfl) ⟨1814283, by rfl⟩ : syracuseStep 4838089 = 3628567) B3628567
theorem B6450785 : Blo 2013435 6450785 := bstep (se 2 (by rfl) ⟨2419044, by rfl⟩ : syracuseStep 6450785 = 4838089) B4838089
theorem B4300523 : Blo 2013435 4300523 := bstep (se 1 (by rfl) ⟨3225392, by rfl⟩ : syracuseStep 4300523 = 6450785) B6450785
theorem B2867015 : Blo 2013435 2867015 := bstep (se 1 (by rfl) ⟨2150261, by rfl⟩ : syracuseStep 2867015 = 4300523) B4300523
theorem B7645373 : Blo 2013435 7645373 := bstep (se 3 (by rfl) ⟨1433507, by rfl⟩ : syracuseStep 7645373 = 2867015) B2867015
theorem B5096915 : Blo 2013435 5096915 := bstep (se 1 (by rfl) ⟨3822686, by rfl⟩ : syracuseStep 5096915 = 7645373) B7645373
theorem B3397943 : Blo 2013435 3397943 := bstep (se 1 (by rfl) ⟨2548457, by rfl⟩ : syracuseStep 3397943 = 5096915) B5096915
theorem B2265295 : Blo 2013435 2265295 := bstep (se 1 (by rfl) ⟨1698971, by rfl⟩ : syracuseStep 2265295 = 3397943) B3397943
theorem B3020393 : Blo 2013435 3020393 := bstep (se 2 (by rfl) ⟨1132647, by rfl⟩ : syracuseStep 3020393 = 2265295) B2265295
theorem B2013595 : Blo 2013435 2013595 := bstep (se 1 (by rfl) ⟨1510196, by rfl⟩ : syracuseStep 2013595 = 3020393) B3020393
theorem B8601061 : Blo 2013435 8601061 := bbase (se 4 (by rfl) ⟨806349, by rfl⟩ : syracuseStep 8601061 = 1612699) (by norm_num)
theorem B11468081 : Blo 2013435 11468081 := bstep (se 2 (by rfl) ⟨4300530, by rfl⟩ : syracuseStep 11468081 = 8601061) B8601061
theorem B7645387 : Blo 2013435 7645387 := bstep (se 1 (by rfl) ⟨5734040, by rfl⟩ : syracuseStep 7645387 = 11468081) B11468081
theorem B10193849 : Blo 2013435 10193849 := bstep (se 2 (by rfl) ⟨3822693, by rfl⟩ : syracuseStep 10193849 = 7645387) B7645387
theorem B6795899 : Blo 2013435 6795899 := bstep (se 1 (by rfl) ⟨5096924, by rfl⟩ : syracuseStep 6795899 = 10193849) B10193849
theorem B4530599 : Blo 2013435 4530599 := bstep (se 1 (by rfl) ⟨3397949, by rfl⟩ : syracuseStep 4530599 = 6795899) B6795899
theorem B3020399 : Blo 2013435 3020399 := bstep (se 1 (by rfl) ⟨2265299, by rfl⟩ : syracuseStep 3020399 = 4530599) B4530599
theorem B2013599 : Blo 2013435 2013599 := bstep (se 1 (by rfl) ⟨1510199, by rfl⟩ : syracuseStep 2013599 = 3020399) B3020399
theorem B3020405 : Blo 2013435 3020405 := bbase (se 5 (by rfl) ⟨141581, by rfl⟩ : syracuseStep 3020405 = 283163) (by norm_num)
theorem B2013603 : Blo 2013435 2013603 := bstep (se 1 (by rfl) ⟨1510202, by rfl⟩ : syracuseStep 2013603 = 3020405) B3020405
theorem B3822709 : Blo 2013435 3822709 := bbase (se 5 (by rfl) ⟨179189, by rfl⟩ : syracuseStep 3822709 = 358379) (by norm_num)
theorem B5096945 : Blo 2013435 5096945 := bstep (se 2 (by rfl) ⟨1911354, by rfl⟩ : syracuseStep 5096945 = 3822709) B3822709
theorem B3397963 : Blo 2013435 3397963 := bstep (se 1 (by rfl) ⟨2548472, by rfl⟩ : syracuseStep 3397963 = 5096945) B5096945
theorem B4530617 : Blo 2013435 4530617 := bstep (se 2 (by rfl) ⟨1698981, by rfl⟩ : syracuseStep 4530617 = 3397963) B3397963
theorem B3020411 : Blo 2013435 3020411 := bstep (se 1 (by rfl) ⟨2265308, by rfl⟩ : syracuseStep 3020411 = 4530617) B4530617
theorem B2013607 : Blo 2013435 2013607 := bstep (se 1 (by rfl) ⟨1510205, by rfl⟩ : syracuseStep 2013607 = 3020411) B3020411
theorem B2265313 : Blo 2013435 2265313 := bbase (se 2 (by rfl) ⟨849492, by rfl⟩ : syracuseStep 2265313 = 1698985) (by norm_num)
theorem B3020417 : Blo 2013435 3020417 := bstep (se 2 (by rfl) ⟨1132656, by rfl⟩ : syracuseStep 3020417 = 2265313) B2265313
theorem B2013611 : Blo 2013435 2013611 := bstep (se 1 (by rfl) ⟨1510208, by rfl⟩ : syracuseStep 2013611 = 3020417) B3020417
theorem B5096965 : Blo 2013435 5096965 := bbase (se 4 (by rfl) ⟨477840, by rfl⟩ : syracuseStep 5096965 = 955681) (by norm_num)
theorem B6795953 : Blo 2013435 6795953 := bstep (se 2 (by rfl) ⟨2548482, by rfl⟩ : syracuseStep 6795953 = 5096965) B5096965
theorem B4530635 : Blo 2013435 4530635 := bstep (se 1 (by rfl) ⟨3397976, by rfl⟩ : syracuseStep 4530635 = 6795953) B6795953
theorem B3020423 : Blo 2013435 3020423 := bstep (se 1 (by rfl) ⟨2265317, by rfl⟩ : syracuseStep 3020423 = 4530635) B4530635
theorem B2013615 : Blo 2013435 2013615 := bstep (se 1 (by rfl) ⟨1510211, by rfl⟩ : syracuseStep 2013615 = 3020423) B3020423
theorem B3020429 : Blo 2013435 3020429 := bbase (se 3 (by rfl) ⟨566330, by rfl⟩ : syracuseStep 3020429 = 1132661) (by norm_num)
theorem B2013619 : Blo 2013435 2013619 := bstep (se 1 (by rfl) ⟨1510214, by rfl⟩ : syracuseStep 2013619 = 3020429) B3020429
theorem B4530653 : Blo 2013435 4530653 := bbase (se 3 (by rfl) ⟨849497, by rfl⟩ : syracuseStep 4530653 = 1698995) (by norm_num)
theorem B3020435 : Blo 2013435 3020435 := bstep (se 1 (by rfl) ⟨2265326, by rfl⟩ : syracuseStep 3020435 = 4530653) B4530653
theorem B2013623 : Blo 2013435 2013623 := bstep (se 1 (by rfl) ⟨1510217, by rfl⟩ : syracuseStep 2013623 = 3020435) B3020435
theorem B3397997 : Blo 2013435 3397997 := bbase (se 3 (by rfl) ⟨637124, by rfl⟩ : syracuseStep 3397997 = 1274249) (by norm_num)
theorem B2265331 : Blo 2013435 2265331 := bstep (se 1 (by rfl) ⟨1698998, by rfl⟩ : syracuseStep 2265331 = 3397997) B3397997
theorem B3020441 : Blo 2013435 3020441 := bstep (se 2 (by rfl) ⟨1132665, by rfl⟩ : syracuseStep 3020441 = 2265331) B2265331
theorem B2013627 : Blo 2013435 2013627 := bstep (se 1 (by rfl) ⟨1510220, by rfl⟩ : syracuseStep 2013627 = 3020441) B3020441
theorem B3444365 : Blo 2013435 3444365 := bbase (se 3 (by rfl) ⟨645818, by rfl⟩ : syracuseStep 3444365 = 1291637) (by norm_num)
theorem B2296243 : Blo 2013435 2296243 := bstep (se 1 (by rfl) ⟨1722182, by rfl⟩ : syracuseStep 2296243 = 3444365) B3444365
theorem B3061657 : Blo 2013435 3061657 := bstep (se 2 (by rfl) ⟨1148121, by rfl⟩ : syracuseStep 3061657 = 2296243) B2296243
theorem B16328837 : Blo 2013435 16328837 := bstep (se 4 (by rfl) ⟨1530828, by rfl⟩ : syracuseStep 16328837 = 3061657) B3061657
theorem B43543565 : Blo 2013435 43543565 := bstep (se 3 (by rfl) ⟨8164418, by rfl⟩ : syracuseStep 43543565 = 16328837) B16328837
theorem B29029043 : Blo 2013435 29029043 := bstep (se 1 (by rfl) ⟨21771782, by rfl⟩ : syracuseStep 29029043 = 43543565) B43543565
theorem B19352695 : Blo 2013435 19352695 := bstep (se 1 (by rfl) ⟨14514521, by rfl⟩ : syracuseStep 19352695 = 29029043) B29029043
theorem B25803593 : Blo 2013435 25803593 := bstep (se 2 (by rfl) ⟨9676347, by rfl⟩ : syracuseStep 25803593 = 19352695) B19352695
theorem B17202395 : Blo 2013435 17202395 := bstep (se 1 (by rfl) ⟨12901796, by rfl⟩ : syracuseStep 17202395 = 25803593) B25803593
theorem B11468263 : Blo 2013435 11468263 := bstep (se 1 (by rfl) ⟨8601197, by rfl⟩ : syracuseStep 11468263 = 17202395) B17202395
theorem B15291017 : Blo 2013435 15291017 := bstep (se 2 (by rfl) ⟨5734131, by rfl⟩ : syracuseStep 15291017 = 11468263) B11468263
theorem B10194011 : Blo 2013435 10194011 := bstep (se 1 (by rfl) ⟨7645508, by rfl⟩ : syracuseStep 10194011 = 15291017) B15291017
theorem B6796007 : Blo 2013435 6796007 := bstep (se 1 (by rfl) ⟨5097005, by rfl⟩ : syracuseStep 6796007 = 10194011) B10194011
theorem B4530671 : Blo 2013435 4530671 := bstep (se 1 (by rfl) ⟨3398003, by rfl⟩ : syracuseStep 4530671 = 6796007) B6796007
theorem B3020447 : Blo 2013435 3020447 := bstep (se 1 (by rfl) ⟨2265335, by rfl⟩ : syracuseStep 3020447 = 4530671) B4530671
theorem B2013631 : Blo 2013435 2013631 := bstep (se 1 (by rfl) ⟨1510223, by rfl⟩ : syracuseStep 2013631 = 3020447) B3020447
theorem B3020453 : Blo 2013435 3020453 := bbase (se 4 (by rfl) ⟨283167, by rfl⟩ : syracuseStep 3020453 = 566335) (by norm_num)
theorem B2013635 : Blo 2013435 2013635 := bstep (se 1 (by rfl) ⟨1510226, by rfl⟩ : syracuseStep 2013635 = 3020453) B3020453
theorem B2548513 : Blo 2013435 2548513 := bbase (se 2 (by rfl) ⟨955692, by rfl⟩ : syracuseStep 2548513 = 1911385) (by norm_num)
theorem B3398017 : Blo 2013435 3398017 := bstep (se 2 (by rfl) ⟨1274256, by rfl⟩ : syracuseStep 3398017 = 2548513) B2548513
theorem B4530689 : Blo 2013435 4530689 := bstep (se 2 (by rfl) ⟨1699008, by rfl⟩ : syracuseStep 4530689 = 3398017) B3398017
theorem B3020459 : Blo 2013435 3020459 := bstep (se 1 (by rfl) ⟨2265344, by rfl⟩ : syracuseStep 3020459 = 4530689) B4530689
theorem B2013639 : Blo 2013435 2013639 := bstep (se 1 (by rfl) ⟨1510229, by rfl⟩ : syracuseStep 2013639 = 3020459) B3020459
theorem B2265349 : Blo 2013435 2265349 := bbase (se 4 (by rfl) ⟨212376, by rfl⟩ : syracuseStep 2265349 = 424753) (by norm_num)
theorem B3020465 : Blo 2013435 3020465 := bstep (se 2 (by rfl) ⟨1132674, by rfl⟩ : syracuseStep 3020465 = 2265349) B2265349
theorem B2013643 : Blo 2013435 2013643 := bstep (se 1 (by rfl) ⟨1510232, by rfl⟩ : syracuseStep 2013643 = 3020465) B3020465
theorem B2150317 : Blo 2013435 2150317 := bbase (se 3 (by rfl) ⟨403184, by rfl⟩ : syracuseStep 2150317 = 806369) (by norm_num)
theorem B2867089 : Blo 2013435 2867089 := bstep (se 2 (by rfl) ⟨1075158, by rfl⟩ : syracuseStep 2867089 = 2150317) B2150317
theorem B3822785 : Blo 2013435 3822785 := bstep (se 2 (by rfl) ⟨1433544, by rfl⟩ : syracuseStep 3822785 = 2867089) B2867089
theorem B2548523 : Blo 2013435 2548523 := bstep (se 1 (by rfl) ⟨1911392, by rfl⟩ : syracuseStep 2548523 = 3822785) B3822785
theorem B6796061 : Blo 2013435 6796061 := bstep (se 3 (by rfl) ⟨1274261, by rfl⟩ : syracuseStep 6796061 = 2548523) B2548523
theorem B4530707 : Blo 2013435 4530707 := bstep (se 1 (by rfl) ⟨3398030, by rfl⟩ : syracuseStep 4530707 = 6796061) B6796061
theorem B3020471 : Blo 2013435 3020471 := bstep (se 1 (by rfl) ⟨2265353, by rfl⟩ : syracuseStep 3020471 = 4530707) B4530707
theorem B2013647 : Blo 2013435 2013647 := bstep (se 1 (by rfl) ⟨1510235, by rfl⟩ : syracuseStep 2013647 = 3020471) B3020471
theorem B3020477 : Blo 2013435 3020477 := bbase (se 3 (by rfl) ⟨566339, by rfl⟩ : syracuseStep 3020477 = 1132679) (by norm_num)
theorem B2013651 : Blo 2013435 2013651 := bstep (se 1 (by rfl) ⟨1510238, by rfl⟩ : syracuseStep 2013651 = 3020477) B3020477
theorem B4530725 : Blo 2013435 4530725 := bbase (se 4 (by rfl) ⟨424755, by rfl⟩ : syracuseStep 4530725 = 849511) (by norm_num)
theorem B3020483 : Blo 2013435 3020483 := bstep (se 1 (by rfl) ⟨2265362, by rfl⟩ : syracuseStep 3020483 = 4530725) B4530725
theorem B2013655 : Blo 2013435 2013655 := bstep (se 1 (by rfl) ⟨1510241, by rfl⟩ : syracuseStep 2013655 = 3020483) B3020483
theorem B5097077 : Blo 2013435 5097077 := bbase (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) (by norm_num)
theorem B3398051 : Blo 2013435 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B2265367 : Blo 2013435 2265367 := bstep (se 1 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 2265367 = 3398051) B3398051
theorem B3020489 : Blo 2013435 3020489 := bstep (se 2 (by rfl) ⟨1132683, by rfl⟩ : syracuseStep 3020489 = 2265367) B2265367
theorem B2013659 : Blo 2013435 2013659 := bstep (se 1 (by rfl) ⟨1510244, by rfl⟩ : syracuseStep 2013659 = 3020489) B3020489
theorem B6123413 : Blo 2013435 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B4082275 : Blo 2013435 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B5443033 : Blo 2013435 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B7257377 : Blo 2013435 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B19353005 : Blo 2013435 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B12902003 : Blo 2013435 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B8601335 : Blo 2013435 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B5734223 : Blo 2013435 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B3822815 : Blo 2013435 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B10194173 : Blo 2013435 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B6796115 : Blo 2013435 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B4530743 : Blo 2013435 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B3020495 : Blo 2013435 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B2013663 : Blo 2013435 2013663 := bstep (se 1 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 2013663 = 3020495) B3020495
theorem B3020501 : Blo 2013435 3020501 := bbase (se 7 (by rfl) ⟨35396, by rfl⟩ : syracuseStep 3020501 = 70793) (by norm_num)
theorem B2013667 : Blo 2013435 2013667 := bstep (se 1 (by rfl) ⟨1510250, by rfl⟩ : syracuseStep 2013667 = 3020501) B3020501
theorem B4300685 : Blo 2013435 4300685 := bbase (se 3 (by rfl) ⟨806378, by rfl⟩ : syracuseStep 4300685 = 1612757) (by norm_num)
theorem B2867123 : Blo 2013435 2867123 := bstep (se 1 (by rfl) ⟨2150342, by rfl⟩ : syracuseStep 2867123 = 4300685) B4300685
theorem B7645661 : Blo 2013435 7645661 := bstep (se 3 (by rfl) ⟨1433561, by rfl⟩ : syracuseStep 7645661 = 2867123) B2867123
theorem B5097107 : Blo 2013435 5097107 := bstep (se 1 (by rfl) ⟨3822830, by rfl⟩ : syracuseStep 5097107 = 7645661) B7645661
theorem B3398071 : Blo 2013435 3398071 := bstep (se 1 (by rfl) ⟨2548553, by rfl⟩ : syracuseStep 3398071 = 5097107) B5097107
theorem B4530761 : Blo 2013435 4530761 := bstep (se 2 (by rfl) ⟨1699035, by rfl⟩ : syracuseStep 4530761 = 3398071) B3398071
theorem B3020507 : Blo 2013435 3020507 := bstep (se 1 (by rfl) ⟨2265380, by rfl⟩ : syracuseStep 3020507 = 4530761) B4530761
theorem B2013671 : Blo 2013435 2013671 := bstep (se 1 (by rfl) ⟨1510253, by rfl⟩ : syracuseStep 2013671 = 3020507) B3020507
theorem B2265385 : Blo 2013435 2265385 := bbase (se 2 (by rfl) ⟨849519, by rfl⟩ : syracuseStep 2265385 = 1699039) (by norm_num)
theorem B3020513 : Blo 2013435 3020513 := bstep (se 2 (by rfl) ⟨1132692, by rfl⟩ : syracuseStep 3020513 = 2265385) B2265385
theorem B2013675 : Blo 2013435 2013675 := bstep (se 1 (by rfl) ⟨1510256, by rfl⟩ : syracuseStep 2013675 = 3020513) B3020513
theorem B14514869 : Blo 2013435 14514869 := bbase (se 5 (by rfl) ⟨680384, by rfl⟩ : syracuseStep 14514869 = 1360769) (by norm_num)
theorem B9676579 : Blo 2013435 9676579 := bstep (se 1 (by rfl) ⟨7257434, by rfl⟩ : syracuseStep 9676579 = 14514869) B14514869
theorem B12902105 : Blo 2013435 12902105 := bstep (se 2 (by rfl) ⟨4838289, by rfl⟩ : syracuseStep 12902105 = 9676579) B9676579
theorem B8601403 : Blo 2013435 8601403 := bstep (se 1 (by rfl) ⟨6451052, by rfl⟩ : syracuseStep 8601403 = 12902105) B12902105
theorem B11468537 : Blo 2013435 11468537 := bstep (se 2 (by rfl) ⟨4300701, by rfl⟩ : syracuseStep 11468537 = 8601403) B8601403
theorem B7645691 : Blo 2013435 7645691 := bstep (se 1 (by rfl) ⟨5734268, by rfl⟩ : syracuseStep 7645691 = 11468537) B11468537
theorem B5097127 : Blo 2013435 5097127 := bstep (se 1 (by rfl) ⟨3822845, by rfl⟩ : syracuseStep 5097127 = 7645691) B7645691
theorem B6796169 : Blo 2013435 6796169 := bstep (se 2 (by rfl) ⟨2548563, by rfl⟩ : syracuseStep 6796169 = 5097127) B5097127
theorem B4530779 : Blo 2013435 4530779 := bstep (se 1 (by rfl) ⟨3398084, by rfl⟩ : syracuseStep 4530779 = 6796169) B6796169
theorem B3020519 : Blo 2013435 3020519 := bstep (se 1 (by rfl) ⟨2265389, by rfl⟩ : syracuseStep 3020519 = 4530779) B4530779
theorem B2013679 : Blo 2013435 2013679 := bstep (se 1 (by rfl) ⟨1510259, by rfl⟩ : syracuseStep 2013679 = 3020519) B3020519
theorem B3020525 : Blo 2013435 3020525 := bbase (se 3 (by rfl) ⟨566348, by rfl⟩ : syracuseStep 3020525 = 1132697) (by norm_num)
theorem B2013683 : Blo 2013435 2013683 := bstep (se 1 (by rfl) ⟨1510262, by rfl⟩ : syracuseStep 2013683 = 3020525) B3020525
theorem B4530797 : Blo 2013435 4530797 := bbase (se 3 (by rfl) ⟨849524, by rfl⟩ : syracuseStep 4530797 = 1699049) (by norm_num)
theorem B3020531 : Blo 2013435 3020531 := bstep (se 1 (by rfl) ⟨2265398, by rfl⟩ : syracuseStep 3020531 = 4530797) B4530797
theorem B2013687 : Blo 2013435 2013687 := bstep (se 1 (by rfl) ⟨1510265, by rfl⟩ : syracuseStep 2013687 = 3020531) B3020531
theorem B3822869 : Blo 2013435 3822869 := bbase (se 6 (by rfl) ⟨89598, by rfl⟩ : syracuseStep 3822869 = 179197) (by norm_num)
theorem B2548579 : Blo 2013435 2548579 := bstep (se 1 (by rfl) ⟨1911434, by rfl⟩ : syracuseStep 2548579 = 3822869) B3822869
theorem B3398105 : Blo 2013435 3398105 := bstep (se 2 (by rfl) ⟨1274289, by rfl⟩ : syracuseStep 3398105 = 2548579) B2548579
theorem B2265403 : Blo 2013435 2265403 := bstep (se 1 (by rfl) ⟨1699052, by rfl⟩ : syracuseStep 2265403 = 3398105) B3398105
theorem B3020537 : Blo 2013435 3020537 := bstep (se 2 (by rfl) ⟨1132701, by rfl⟩ : syracuseStep 3020537 = 2265403) B2265403
theorem B2013691 : Blo 2013435 2013691 := bstep (se 1 (by rfl) ⟨1510268, by rfl⟩ : syracuseStep 2013691 = 3020537) B3020537
theorem B4359413 : Blo 2013435 4359413 := bbase (se 5 (by rfl) ⟨204347, by rfl⟩ : syracuseStep 4359413 = 408695) (by norm_num)
theorem B2906275 : Blo 2013435 2906275 := bstep (se 1 (by rfl) ⟨2179706, by rfl⟩ : syracuseStep 2906275 = 4359413) B4359413
theorem B3875033 : Blo 2013435 3875033 := bstep (se 2 (by rfl) ⟨1453137, by rfl⟩ : syracuseStep 3875033 = 2906275) B2906275
theorem B10333421 : Blo 2013435 10333421 := bstep (se 3 (by rfl) ⟨1937516, by rfl⟩ : syracuseStep 10333421 = 3875033) B3875033
theorem B6888947 : Blo 2013435 6888947 := bstep (se 1 (by rfl) ⟨5166710, by rfl⟩ : syracuseStep 6888947 = 10333421) B10333421
theorem B18370525 : Blo 2013435 18370525 := bstep (se 3 (by rfl) ⟨3444473, by rfl⟩ : syracuseStep 18370525 = 6888947) B6888947
theorem B24494033 : Blo 2013435 24494033 := bstep (se 2 (by rfl) ⟨9185262, by rfl⟩ : syracuseStep 24494033 = 18370525) B18370525
theorem B65317421 : Blo 2013435 65317421 := bstep (se 3 (by rfl) ⟨12247016, by rfl⟩ : syracuseStep 65317421 = 24494033) B24494033
theorem B43544947 : Blo 2013435 43544947 := bstep (se 1 (by rfl) ⟨32658710, by rfl⟩ : syracuseStep 43544947 = 65317421) B65317421
theorem B58059929 : Blo 2013435 58059929 := bstep (se 2 (by rfl) ⟨21772473, by rfl⟩ : syracuseStep 58059929 = 43544947) B43544947
theorem B38706619 : Blo 2013435 38706619 := bstep (se 1 (by rfl) ⟨29029964, by rfl⟩ : syracuseStep 38706619 = 58059929) B58059929
theorem B51608825 : Blo 2013435 51608825 := bstep (se 2 (by rfl) ⟨19353309, by rfl⟩ : syracuseStep 51608825 = 38706619) B38706619
theorem B34405883 : Blo 2013435 34405883 := bstep (se 1 (by rfl) ⟨25804412, by rfl⟩ : syracuseStep 34405883 = 51608825) B51608825
theorem B22937255 : Blo 2013435 22937255 := bstep (se 1 (by rfl) ⟨17202941, by rfl⟩ : syracuseStep 22937255 = 34405883) B34405883
theorem B15291503 : Blo 2013435 15291503 := bstep (se 1 (by rfl) ⟨11468627, by rfl⟩ : syracuseStep 15291503 = 22937255) B22937255
theorem B10194335 : Blo 2013435 10194335 := bstep (se 1 (by rfl) ⟨7645751, by rfl⟩ : syracuseStep 10194335 = 15291503) B15291503
theorem B6796223 : Blo 2013435 6796223 := bstep (se 1 (by rfl) ⟨5097167, by rfl⟩ : syracuseStep 6796223 = 10194335) B10194335
theorem B4530815 : Blo 2013435 4530815 := bstep (se 1 (by rfl) ⟨3398111, by rfl⟩ : syracuseStep 4530815 = 6796223) B6796223
theorem B3020543 : Blo 2013435 3020543 := bstep (se 1 (by rfl) ⟨2265407, by rfl⟩ : syracuseStep 3020543 = 4530815) B4530815
theorem B2013695 : Blo 2013435 2013695 := bstep (se 1 (by rfl) ⟨1510271, by rfl⟩ : syracuseStep 2013695 = 3020543) B3020543
theorem B3020549 : Blo 2013435 3020549 := bbase (se 4 (by rfl) ⟨283176, by rfl⟩ : syracuseStep 3020549 = 566353) (by norm_num)
theorem B2013699 : Blo 2013435 2013699 := bstep (se 1 (by rfl) ⟨1510274, by rfl⟩ : syracuseStep 2013699 = 3020549) B3020549
theorem B3398125 : Blo 2013435 3398125 := bbase (se 3 (by rfl) ⟨637148, by rfl⟩ : syracuseStep 3398125 = 1274297) (by norm_num)
theorem B4530833 : Blo 2013435 4530833 := bstep (se 2 (by rfl) ⟨1699062, by rfl⟩ : syracuseStep 4530833 = 3398125) B3398125
theorem B3020555 : Blo 2013435 3020555 := bstep (se 1 (by rfl) ⟨2265416, by rfl⟩ : syracuseStep 3020555 = 4530833) B4530833
theorem B2013703 : Blo 2013435 2013703 := bstep (se 1 (by rfl) ⟨1510277, by rfl⟩ : syracuseStep 2013703 = 3020555) B3020555
theorem B2265421 : Blo 2013435 2265421 := bbase (se 3 (by rfl) ⟨424766, by rfl⟩ : syracuseStep 2265421 = 849533) (by norm_num)
theorem B3020561 : Blo 2013435 3020561 := bstep (se 2 (by rfl) ⟨1132710, by rfl⟩ : syracuseStep 3020561 = 2265421) B2265421
theorem B2013707 : Blo 2013435 2013707 := bstep (se 1 (by rfl) ⟨1510280, by rfl⟩ : syracuseStep 2013707 = 3020561) B3020561
theorem B6796277 : Blo 2013435 6796277 := bbase (se 5 (by rfl) ⟨318575, by rfl⟩ : syracuseStep 6796277 = 637151) (by norm_num)
theorem B4530851 : Blo 2013435 4530851 := bstep (se 1 (by rfl) ⟨3398138, by rfl⟩ : syracuseStep 4530851 = 6796277) B6796277
theorem B3020567 : Blo 2013435 3020567 := bstep (se 1 (by rfl) ⟨2265425, by rfl⟩ : syracuseStep 3020567 = 4530851) B4530851
theorem B2013711 : Blo 2013435 2013711 := bstep (se 1 (by rfl) ⟨1510283, by rfl⟩ : syracuseStep 2013711 = 3020567) B3020567
theorem B3020573 : Blo 2013435 3020573 := bbase (se 3 (by rfl) ⟨566357, by rfl⟩ : syracuseStep 3020573 = 1132715) (by norm_num)
theorem B2013715 : Blo 2013435 2013715 := bstep (se 1 (by rfl) ⟨1510286, by rfl⟩ : syracuseStep 2013715 = 3020573) B3020573
theorem B4530869 : Blo 2013435 4530869 := bbase (se 5 (by rfl) ⟨212384, by rfl⟩ : syracuseStep 4530869 = 424769) (by norm_num)
theorem B3020579 : Blo 2013435 3020579 := bstep (se 1 (by rfl) ⟨2265434, by rfl⟩ : syracuseStep 3020579 = 4530869) B4530869
theorem B2013719 : Blo 2013435 2013719 := bstep (se 1 (by rfl) ⟨1510289, by rfl⟩ : syracuseStep 2013719 = 3020579) B3020579
theorem B11468789 : Blo 2013435 11468789 := bbase (se 5 (by rfl) ⟨537599, by rfl⟩ : syracuseStep 11468789 = 1075199) (by norm_num)
theorem B7645859 : Blo 2013435 7645859 := bstep (se 1 (by rfl) ⟨5734394, by rfl⟩ : syracuseStep 7645859 = 11468789) B11468789
theorem B5097239 : Blo 2013435 5097239 := bstep (se 1 (by rfl) ⟨3822929, by rfl⟩ : syracuseStep 5097239 = 7645859) B7645859
theorem B3398159 : Blo 2013435 3398159 := bstep (se 1 (by rfl) ⟨2548619, by rfl⟩ : syracuseStep 3398159 = 5097239) B5097239
theorem B2265439 : Blo 2013435 2265439 := bstep (se 1 (by rfl) ⟨1699079, by rfl⟩ : syracuseStep 2265439 = 3398159) B3398159
theorem B3020585 : Blo 2013435 3020585 := bstep (se 2 (by rfl) ⟨1132719, by rfl⟩ : syracuseStep 3020585 = 2265439) B2265439
theorem B2013723 : Blo 2013435 2013723 := bstep (se 1 (by rfl) ⟨1510292, by rfl⟩ : syracuseStep 2013723 = 3020585) B3020585
theorem B5734405 : Blo 2013435 5734405 := bbase (se 4 (by rfl) ⟨537600, by rfl⟩ : syracuseStep 5734405 = 1075201) (by norm_num)
theorem B7645873 : Blo 2013435 7645873 := bstep (se 2 (by rfl) ⟨2867202, by rfl⟩ : syracuseStep 7645873 = 5734405) B5734405
theorem B10194497 : Blo 2013435 10194497 := bstep (se 2 (by rfl) ⟨3822936, by rfl⟩ : syracuseStep 10194497 = 7645873) B7645873
theorem B6796331 : Blo 2013435 6796331 := bstep (se 1 (by rfl) ⟨5097248, by rfl⟩ : syracuseStep 6796331 = 10194497) B10194497
theorem B4530887 : Blo 2013435 4530887 := bstep (se 1 (by rfl) ⟨3398165, by rfl⟩ : syracuseStep 4530887 = 6796331) B6796331
theorem B3020591 : Blo 2013435 3020591 := bstep (se 1 (by rfl) ⟨2265443, by rfl⟩ : syracuseStep 3020591 = 4530887) B4530887
theorem B2013727 : Blo 2013435 2013727 := bstep (se 1 (by rfl) ⟨1510295, by rfl⟩ : syracuseStep 2013727 = 3020591) B3020591
theorem B3020597 : Blo 2013435 3020597 := bbase (se 5 (by rfl) ⟨141590, by rfl⟩ : syracuseStep 3020597 = 283181) (by norm_num)
theorem B2013731 : Blo 2013435 2013731 := bstep (se 1 (by rfl) ⟨1510298, by rfl⟩ : syracuseStep 2013731 = 3020597) B3020597
theorem B5097269 : Blo 2013435 5097269 := bbase (se 5 (by rfl) ⟨238934, by rfl⟩ : syracuseStep 5097269 = 477869) (by norm_num)
theorem B3398179 : Blo 2013435 3398179 := bstep (se 1 (by rfl) ⟨2548634, by rfl⟩ : syracuseStep 3398179 = 5097269) B5097269
theorem B4530905 : Blo 2013435 4530905 := bstep (se 2 (by rfl) ⟨1699089, by rfl⟩ : syracuseStep 4530905 = 3398179) B3398179
theorem B3020603 : Blo 2013435 3020603 := bstep (se 1 (by rfl) ⟨2265452, by rfl⟩ : syracuseStep 3020603 = 4530905) B4530905
theorem B2013735 : Blo 2013435 2013735 := bstep (se 1 (by rfl) ⟨1510301, by rfl⟩ : syracuseStep 2013735 = 3020603) B3020603
theorem B2265457 : Blo 2013435 2265457 := bbase (se 2 (by rfl) ⟨849546, by rfl⟩ : syracuseStep 2265457 = 1699093) (by norm_num)
theorem B3020609 : Blo 2013435 3020609 := bstep (se 2 (by rfl) ⟨1132728, by rfl⟩ : syracuseStep 3020609 = 2265457) B2265457
theorem B2013739 : Blo 2013435 2013739 := bstep (se 1 (by rfl) ⟨1510304, by rfl⟩ : syracuseStep 2013739 = 3020609) B3020609
theorem B3225629 : Blo 2013435 3225629 := bbase (se 3 (by rfl) ⟨604805, by rfl⟩ : syracuseStep 3225629 = 1209611) (by norm_num)
theorem B8601677 : Blo 2013435 8601677 := bstep (se 3 (by rfl) ⟨1612814, by rfl⟩ : syracuseStep 8601677 = 3225629) B3225629
theorem B5734451 : Blo 2013435 5734451 := bstep (se 1 (by rfl) ⟨4300838, by rfl⟩ : syracuseStep 5734451 = 8601677) B8601677
theorem B3822967 : Blo 2013435 3822967 := bstep (se 1 (by rfl) ⟨2867225, by rfl⟩ : syracuseStep 3822967 = 5734451) B5734451
theorem B5097289 : Blo 2013435 5097289 := bstep (se 2 (by rfl) ⟨1911483, by rfl⟩ : syracuseStep 5097289 = 3822967) B3822967
theorem B6796385 : Blo 2013435 6796385 := bstep (se 2 (by rfl) ⟨2548644, by rfl⟩ : syracuseStep 6796385 = 5097289) B5097289
theorem B4530923 : Blo 2013435 4530923 := bstep (se 1 (by rfl) ⟨3398192, by rfl⟩ : syracuseStep 4530923 = 6796385) B6796385
theorem B3020615 : Blo 2013435 3020615 := bstep (se 1 (by rfl) ⟨2265461, by rfl⟩ : syracuseStep 3020615 = 4530923) B4530923
theorem B2013743 : Blo 2013435 2013743 := bstep (se 1 (by rfl) ⟨1510307, by rfl⟩ : syracuseStep 2013743 = 3020615) B3020615
theorem B3020621 : Blo 2013435 3020621 := bbase (se 3 (by rfl) ⟨566366, by rfl⟩ : syracuseStep 3020621 = 1132733) (by norm_num)
theorem B2013747 : Blo 2013435 2013747 := bstep (se 1 (by rfl) ⟨1510310, by rfl⟩ : syracuseStep 2013747 = 3020621) B3020621
theorem B4530941 : Blo 2013435 4530941 := bbase (se 3 (by rfl) ⟨849551, by rfl⟩ : syracuseStep 4530941 = 1699103) (by norm_num)
theorem B3020627 : Blo 2013435 3020627 := bstep (se 1 (by rfl) ⟨2265470, by rfl⟩ : syracuseStep 3020627 = 4530941) B4530941
theorem B2013751 : Blo 2013435 2013751 := bstep (se 1 (by rfl) ⟨1510313, by rfl⟩ : syracuseStep 2013751 = 3020627) B3020627
theorem B3398213 : Blo 2013435 3398213 := bbase (se 4 (by rfl) ⟨318582, by rfl⟩ : syracuseStep 3398213 = 637165) (by norm_num)
theorem B2265475 : Blo 2013435 2265475 := bstep (se 1 (by rfl) ⟨1699106, by rfl⟩ : syracuseStep 2265475 = 3398213) B3398213
theorem B3020633 : Blo 2013435 3020633 := bstep (se 2 (by rfl) ⟨1132737, by rfl⟩ : syracuseStep 3020633 = 2265475) B2265475
theorem B2013755 : Blo 2013435 2013755 := bstep (se 1 (by rfl) ⟨1510316, by rfl⟩ : syracuseStep 2013755 = 3020633) B3020633
theorem B15291989 : Blo 2013435 15291989 := bbase (se 8 (by rfl) ⟨89601, by rfl⟩ : syracuseStep 15291989 = 179203) (by norm_num)
theorem B10194659 : Blo 2013435 10194659 := bstep (se 1 (by rfl) ⟨7645994, by rfl⟩ : syracuseStep 10194659 = 15291989) B15291989
theorem B6796439 : Blo 2013435 6796439 := bstep (se 1 (by rfl) ⟨5097329, by rfl⟩ : syracuseStep 6796439 = 10194659) B10194659
theorem B4530959 : Blo 2013435 4530959 := bstep (se 1 (by rfl) ⟨3398219, by rfl⟩ : syracuseStep 4530959 = 6796439) B6796439
theorem B3020639 : Blo 2013435 3020639 := bstep (se 1 (by rfl) ⟨2265479, by rfl⟩ : syracuseStep 3020639 = 4530959) B4530959
theorem B2013759 : Blo 2013435 2013759 := bstep (se 1 (by rfl) ⟨1510319, by rfl⟩ : syracuseStep 2013759 = 3020639) B3020639
theorem B3020645 : Blo 2013435 3020645 := bbase (se 4 (by rfl) ⟨283185, by rfl⟩ : syracuseStep 3020645 = 566371) (by norm_num)
theorem B2013763 : Blo 2013435 2013763 := bstep (se 1 (by rfl) ⟨1510322, by rfl⟩ : syracuseStep 2013763 = 3020645) B3020645
theorem B3823013 : Blo 2013435 3823013 := bbase (se 4 (by rfl) ⟨358407, by rfl⟩ : syracuseStep 3823013 = 716815) (by norm_num)
theorem B2548675 : Blo 2013435 2548675 := bstep (se 1 (by rfl) ⟨1911506, by rfl⟩ : syracuseStep 2548675 = 3823013) B3823013
theorem B3398233 : Blo 2013435 3398233 := bstep (se 2 (by rfl) ⟨1274337, by rfl⟩ : syracuseStep 3398233 = 2548675) B2548675
theorem B4530977 : Blo 2013435 4530977 := bstep (se 2 (by rfl) ⟨1699116, by rfl⟩ : syracuseStep 4530977 = 3398233) B3398233
theorem B3020651 : Blo 2013435 3020651 := bstep (se 1 (by rfl) ⟨2265488, by rfl⟩ : syracuseStep 3020651 = 4530977) B4530977
theorem B2013767 : Blo 2013435 2013767 := bstep (se 1 (by rfl) ⟨1510325, by rfl⟩ : syracuseStep 2013767 = 3020651) B3020651
theorem B2265493 : Blo 2013435 2265493 := bbase (se 6 (by rfl) ⟨53097, by rfl⟩ : syracuseStep 2265493 = 106195) (by norm_num)
theorem B3020657 : Blo 2013435 3020657 := bstep (se 2 (by rfl) ⟨1132746, by rfl⟩ : syracuseStep 3020657 = 2265493) B2265493
theorem B2013771 : Blo 2013435 2013771 := bstep (se 1 (by rfl) ⟨1510328, by rfl⟩ : syracuseStep 2013771 = 3020657) B3020657
theorem B2548685 : Blo 2013435 2548685 := bbase (se 3 (by rfl) ⟨477878, by rfl⟩ : syracuseStep 2548685 = 955757) (by norm_num)
theorem B6796493 : Blo 2013435 6796493 := bstep (se 3 (by rfl) ⟨1274342, by rfl⟩ : syracuseStep 6796493 = 2548685) B2548685
theorem B4530995 : Blo 2013435 4530995 := bstep (se 1 (by rfl) ⟨3398246, by rfl⟩ : syracuseStep 4530995 = 6796493) B6796493
theorem B3020663 : Blo 2013435 3020663 := bstep (se 1 (by rfl) ⟨2265497, by rfl⟩ : syracuseStep 3020663 = 4530995) B4530995
theorem B2013775 : Blo 2013435 2013775 := bstep (se 1 (by rfl) ⟨1510331, by rfl⟩ : syracuseStep 2013775 = 3020663) B3020663
theorem B3020669 : Blo 2013435 3020669 := bbase (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) (by norm_num)
theorem B2013779 : Blo 2013435 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B4531013 : Blo 2013435 4531013 := bbase (se 4 (by rfl) ⟨424782, by rfl⟩ : syracuseStep 4531013 = 849565) (by norm_num)
theorem B3020675 : Blo 2013435 3020675 := bstep (se 1 (by rfl) ⟨2265506, by rfl⟩ : syracuseStep 3020675 = 4531013) B4531013
theorem B2013783 : Blo 2013435 2013783 := bstep (se 1 (by rfl) ⟨1510337, by rfl⟩ : syracuseStep 2013783 = 3020675) B3020675
theorem B4300933 : Blo 2013435 4300933 := bbase (se 4 (by rfl) ⟨403212, by rfl⟩ : syracuseStep 4300933 = 806425) (by norm_num)
theorem B5734577 : Blo 2013435 5734577 := bstep (se 2 (by rfl) ⟨2150466, by rfl⟩ : syracuseStep 5734577 = 4300933) B4300933
theorem B3823051 : Blo 2013435 3823051 := bstep (se 1 (by rfl) ⟨2867288, by rfl⟩ : syracuseStep 3823051 = 5734577) B5734577
theorem B5097401 : Blo 2013435 5097401 := bstep (se 2 (by rfl) ⟨1911525, by rfl⟩ : syracuseStep 5097401 = 3823051) B3823051
theorem B3398267 : Blo 2013435 3398267 := bstep (se 1 (by rfl) ⟨2548700, by rfl⟩ : syracuseStep 3398267 = 5097401) B5097401
theorem B2265511 : Blo 2013435 2265511 := bstep (se 1 (by rfl) ⟨1699133, by rfl⟩ : syracuseStep 2265511 = 3398267) B3398267
theorem B3020681 : Blo 2013435 3020681 := bstep (se 2 (by rfl) ⟨1132755, by rfl⟩ : syracuseStep 3020681 = 2265511) B2265511
theorem B2013787 : Blo 2013435 2013787 := bstep (se 1 (by rfl) ⟨1510340, by rfl⟩ : syracuseStep 2013787 = 3020681) B3020681
theorem B10194821 : Blo 2013435 10194821 := bbase (se 4 (by rfl) ⟨955764, by rfl⟩ : syracuseStep 10194821 = 1911529) (by norm_num)
theorem B6796547 : Blo 2013435 6796547 := bstep (se 1 (by rfl) ⟨5097410, by rfl⟩ : syracuseStep 6796547 = 10194821) B10194821
theorem B4531031 : Blo 2013435 4531031 := bstep (se 1 (by rfl) ⟨3398273, by rfl⟩ : syracuseStep 4531031 = 6796547) B6796547
theorem B3020687 : Blo 2013435 3020687 := bstep (se 1 (by rfl) ⟨2265515, by rfl⟩ : syracuseStep 3020687 = 4531031) B4531031
theorem B2013791 : Blo 2013435 2013791 := bstep (se 1 (by rfl) ⟨1510343, by rfl⟩ : syracuseStep 2013791 = 3020687) B3020687
theorem B3020693 : Blo 2013435 3020693 := bbase (se 6 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 3020693 = 141595) (by norm_num)
theorem B2013795 : Blo 2013435 2013795 := bstep (se 1 (by rfl) ⟨1510346, by rfl⟩ : syracuseStep 2013795 = 3020693) B3020693
theorem B2721701 : Blo 2013435 2721701 := bbase (se 4 (by rfl) ⟨255159, by rfl⟩ : syracuseStep 2721701 = 510319) (by norm_num)
theorem B7257869 : Blo 2013435 7257869 := bstep (se 3 (by rfl) ⟨1360850, by rfl⟩ : syracuseStep 7257869 = 2721701) B2721701
theorem B4838579 : Blo 2013435 4838579 := bstep (se 1 (by rfl) ⟨3628934, by rfl⟩ : syracuseStep 4838579 = 7257869) B7257869
theorem B3225719 : Blo 2013435 3225719 := bstep (se 1 (by rfl) ⟨2419289, by rfl⟩ : syracuseStep 3225719 = 4838579) B4838579
theorem B2150479 : Blo 2013435 2150479 := bstep (se 1 (by rfl) ⟨1612859, by rfl⟩ : syracuseStep 2150479 = 3225719) B3225719
theorem B11469221 : Blo 2013435 11469221 := bstep (se 4 (by rfl) ⟨1075239, by rfl⟩ : syracuseStep 11469221 = 2150479) B2150479
theorem B7646147 : Blo 2013435 7646147 := bstep (se 1 (by rfl) ⟨5734610, by rfl⟩ : syracuseStep 7646147 = 11469221) B11469221
theorem B5097431 : Blo 2013435 5097431 := bstep (se 1 (by rfl) ⟨3823073, by rfl⟩ : syracuseStep 5097431 = 7646147) B7646147
theorem B3398287 : Blo 2013435 3398287 := bstep (se 1 (by rfl) ⟨2548715, by rfl⟩ : syracuseStep 3398287 = 5097431) B5097431
theorem B4531049 : Blo 2013435 4531049 := bstep (se 2 (by rfl) ⟨1699143, by rfl⟩ : syracuseStep 4531049 = 3398287) B3398287
theorem B3020699 : Blo 2013435 3020699 := bstep (se 1 (by rfl) ⟨2265524, by rfl⟩ : syracuseStep 3020699 = 4531049) B4531049
theorem B2013799 : Blo 2013435 2013799 := bstep (se 1 (by rfl) ⟨1510349, by rfl⟩ : syracuseStep 2013799 = 3020699) B3020699
theorem B2265529 : Blo 2013435 2265529 := bbase (se 2 (by rfl) ⟨849573, by rfl⟩ : syracuseStep 2265529 = 1699147) (by norm_num)
theorem B3020705 : Blo 2013435 3020705 := bstep (se 2 (by rfl) ⟨1132764, by rfl⟩ : syracuseStep 3020705 = 2265529) B2265529
theorem B2013803 : Blo 2013435 2013803 := bstep (se 1 (by rfl) ⟨1510352, by rfl⟩ : syracuseStep 2013803 = 3020705) B3020705
theorem B6889333 : Blo 2013435 6889333 := bbase (se 5 (by rfl) ⟨322937, by rfl⟩ : syracuseStep 6889333 = 645875) (by norm_num)
theorem B9185777 : Blo 2013435 9185777 := bstep (se 2 (by rfl) ⟨3444666, by rfl⟩ : syracuseStep 9185777 = 6889333) B6889333
theorem B6123851 : Blo 2013435 6123851 := bstep (se 1 (by rfl) ⟨4592888, by rfl⟩ : syracuseStep 6123851 = 9185777) B9185777
theorem B4082567 : Blo 2013435 4082567 := bstep (se 1 (by rfl) ⟨3061925, by rfl⟩ : syracuseStep 4082567 = 6123851) B6123851
theorem B10886845 : Blo 2013435 10886845 := bstep (se 3 (by rfl) ⟨2041283, by rfl⟩ : syracuseStep 10886845 = 4082567) B4082567
theorem B14515793 : Blo 2013435 14515793 := bstep (se 2 (by rfl) ⟨5443422, by rfl⟩ : syracuseStep 14515793 = 10886845) B10886845
theorem B9677195 : Blo 2013435 9677195 := bstep (se 1 (by rfl) ⟨7257896, by rfl⟩ : syracuseStep 9677195 = 14515793) B14515793
theorem B6451463 : Blo 2013435 6451463 := bstep (se 1 (by rfl) ⟨4838597, by rfl⟩ : syracuseStep 6451463 = 9677195) B9677195
theorem B4300975 : Blo 2013435 4300975 := bstep (se 1 (by rfl) ⟨3225731, by rfl⟩ : syracuseStep 4300975 = 6451463) B6451463
theorem B5734633 : Blo 2013435 5734633 := bstep (se 2 (by rfl) ⟨2150487, by rfl⟩ : syracuseStep 5734633 = 4300975) B4300975
theorem B7646177 : Blo 2013435 7646177 := bstep (se 2 (by rfl) ⟨2867316, by rfl⟩ : syracuseStep 7646177 = 5734633) B5734633
theorem B5097451 : Blo 2013435 5097451 := bstep (se 1 (by rfl) ⟨3823088, by rfl⟩ : syracuseStep 5097451 = 7646177) B7646177
theorem B6796601 : Blo 2013435 6796601 := bstep (se 2 (by rfl) ⟨2548725, by rfl⟩ : syracuseStep 6796601 = 5097451) B5097451
theorem B4531067 : Blo 2013435 4531067 := bstep (se 1 (by rfl) ⟨3398300, by rfl⟩ : syracuseStep 4531067 = 6796601) B6796601
theorem B3020711 : Blo 2013435 3020711 := bstep (se 1 (by rfl) ⟨2265533, by rfl⟩ : syracuseStep 3020711 = 4531067) B4531067
theorem B2013807 : Blo 2013435 2013807 := bstep (se 1 (by rfl) ⟨1510355, by rfl⟩ : syracuseStep 2013807 = 3020711) B3020711
theorem B3020717 : Blo 2013435 3020717 := bbase (se 3 (by rfl) ⟨566384, by rfl⟩ : syracuseStep 3020717 = 1132769) (by norm_num)
theorem B2013811 : Blo 2013435 2013811 := bstep (se 1 (by rfl) ⟨1510358, by rfl⟩ : syracuseStep 2013811 = 3020717) B3020717
theorem B4531085 : Blo 2013435 4531085 := bbase (se 3 (by rfl) ⟨849578, by rfl⟩ : syracuseStep 4531085 = 1699157) (by norm_num)
theorem B3020723 : Blo 2013435 3020723 := bstep (se 1 (by rfl) ⟨2265542, by rfl⟩ : syracuseStep 3020723 = 4531085) B4531085
theorem B2013815 : Blo 2013435 2013815 := bstep (se 1 (by rfl) ⟨1510361, by rfl⟩ : syracuseStep 2013815 = 3020723) B3020723
theorem B2548741 : Blo 2013435 2548741 := bbase (se 4 (by rfl) ⟨238944, by rfl⟩ : syracuseStep 2548741 = 477889) (by norm_num)
theorem B3398321 : Blo 2013435 3398321 := bstep (se 2 (by rfl) ⟨1274370, by rfl⟩ : syracuseStep 3398321 = 2548741) B2548741
theorem B2265547 : Blo 2013435 2265547 := bstep (se 1 (by rfl) ⟨1699160, by rfl⟩ : syracuseStep 2265547 = 3398321) B3398321
theorem B3020729 : Blo 2013435 3020729 := bstep (se 2 (by rfl) ⟨1132773, by rfl⟩ : syracuseStep 3020729 = 2265547) B2265547
theorem B2013819 : Blo 2013435 2013819 := bstep (se 1 (by rfl) ⟨1510364, by rfl⟩ : syracuseStep 2013819 = 3020729) B3020729
theorem B4904653 : Blo 2013435 4904653 := bbase (se 3 (by rfl) ⟨919622, by rfl⟩ : syracuseStep 4904653 = 1839245) (by norm_num)
theorem B6539537 : Blo 2013435 6539537 := bstep (se 2 (by rfl) ⟨2452326, by rfl⟩ : syracuseStep 6539537 = 4904653) B4904653
theorem B4359691 : Blo 2013435 4359691 := bstep (se 1 (by rfl) ⟨3269768, by rfl⟩ : syracuseStep 4359691 = 6539537) B6539537
theorem B5812921 : Blo 2013435 5812921 := bstep (se 2 (by rfl) ⟨2179845, by rfl⟩ : syracuseStep 5812921 = 4359691) B4359691
theorem B7750561 : Blo 2013435 7750561 := bstep (se 2 (by rfl) ⟨2906460, by rfl⟩ : syracuseStep 7750561 = 5812921) B5812921
theorem B10334081 : Blo 2013435 10334081 := bstep (se 2 (by rfl) ⟨3875280, by rfl⟩ : syracuseStep 10334081 = 7750561) B7750561
theorem B6889387 : Blo 2013435 6889387 := bstep (se 1 (by rfl) ⟨5167040, by rfl⟩ : syracuseStep 6889387 = 10334081) B10334081
theorem B9185849 : Blo 2013435 9185849 := bstep (se 2 (by rfl) ⟨3444693, by rfl⟩ : syracuseStep 9185849 = 6889387) B6889387
theorem B6123899 : Blo 2013435 6123899 := bstep (se 1 (by rfl) ⟨4592924, by rfl⟩ : syracuseStep 6123899 = 9185849) B9185849
theorem B4082599 : Blo 2013435 4082599 := bstep (se 1 (by rfl) ⟨3061949, by rfl⟩ : syracuseStep 4082599 = 6123899) B6123899
theorem B5443465 : Blo 2013435 5443465 := bstep (se 2 (by rfl) ⟨2041299, by rfl⟩ : syracuseStep 5443465 = 4082599) B4082599
theorem B7257953 : Blo 2013435 7257953 := bstep (se 2 (by rfl) ⟨2721732, by rfl⟩ : syracuseStep 7257953 = 5443465) B5443465
theorem B4838635 : Blo 2013435 4838635 := bstep (se 1 (by rfl) ⟨3628976, by rfl⟩ : syracuseStep 4838635 = 7257953) B7257953
theorem B25806053 : Blo 2013435 25806053 := bstep (se 4 (by rfl) ⟨2419317, by rfl⟩ : syracuseStep 25806053 = 4838635) B4838635
theorem B17204035 : Blo 2013435 17204035 := bstep (se 1 (by rfl) ⟨12903026, by rfl⟩ : syracuseStep 17204035 = 25806053) B25806053
theorem B22938713 : Blo 2013435 22938713 := bstep (se 2 (by rfl) ⟨8602017, by rfl⟩ : syracuseStep 22938713 = 17204035) B17204035
theorem B15292475 : Blo 2013435 15292475 := bstep (se 1 (by rfl) ⟨11469356, by rfl⟩ : syracuseStep 15292475 = 22938713) B22938713
theorem B10194983 : Blo 2013435 10194983 := bstep (se 1 (by rfl) ⟨7646237, by rfl⟩ : syracuseStep 10194983 = 15292475) B15292475
theorem B6796655 : Blo 2013435 6796655 := bstep (se 1 (by rfl) ⟨5097491, by rfl⟩ : syracuseStep 6796655 = 10194983) B10194983
theorem B4531103 : Blo 2013435 4531103 := bstep (se 1 (by rfl) ⟨3398327, by rfl⟩ : syracuseStep 4531103 = 6796655) B6796655
theorem B3020735 : Blo 2013435 3020735 := bstep (se 1 (by rfl) ⟨2265551, by rfl⟩ : syracuseStep 3020735 = 4531103) B4531103
theorem B2013823 : Blo 2013435 2013823 := bstep (se 1 (by rfl) ⟨1510367, by rfl⟩ : syracuseStep 2013823 = 3020735) B3020735
theorem B3020741 : Blo 2013435 3020741 := bbase (se 4 (by rfl) ⟨283194, by rfl⟩ : syracuseStep 3020741 = 566389) (by norm_num)
theorem B2013827 : Blo 2013435 2013827 := bstep (se 1 (by rfl) ⟨1510370, by rfl⟩ : syracuseStep 2013827 = 3020741) B3020741
theorem B3398341 : Blo 2013435 3398341 := bbase (se 4 (by rfl) ⟨318594, by rfl⟩ : syracuseStep 3398341 = 637189) (by norm_num)
theorem B4531121 : Blo 2013435 4531121 := bstep (se 2 (by rfl) ⟨1699170, by rfl⟩ : syracuseStep 4531121 = 3398341) B3398341
theorem B3020747 : Blo 2013435 3020747 := bstep (se 1 (by rfl) ⟨2265560, by rfl⟩ : syracuseStep 3020747 = 4531121) B4531121
theorem B2013831 : Blo 2013435 2013831 := bstep (se 1 (by rfl) ⟨1510373, by rfl⟩ : syracuseStep 2013831 = 3020747) B3020747
theorem B2265565 : Blo 2013435 2265565 := bbase (se 3 (by rfl) ⟨424793, by rfl⟩ : syracuseStep 2265565 = 849587) (by norm_num)
theorem B3020753 : Blo 2013435 3020753 := bstep (se 2 (by rfl) ⟨1132782, by rfl⟩ : syracuseStep 3020753 = 2265565) B2265565
theorem B2013835 : Blo 2013435 2013835 := bstep (se 1 (by rfl) ⟨1510376, by rfl⟩ : syracuseStep 2013835 = 3020753) B3020753
theorem B6796709 : Blo 2013435 6796709 := bbase (se 4 (by rfl) ⟨637191, by rfl⟩ : syracuseStep 6796709 = 1274383) (by norm_num)
theorem B4531139 : Blo 2013435 4531139 := bstep (se 1 (by rfl) ⟨3398354, by rfl⟩ : syracuseStep 4531139 = 6796709) B6796709
theorem B3020759 : Blo 2013435 3020759 := bstep (se 1 (by rfl) ⟨2265569, by rfl⟩ : syracuseStep 3020759 = 4531139) B4531139
theorem B2013839 : Blo 2013435 2013839 := bstep (se 1 (by rfl) ⟨1510379, by rfl⟩ : syracuseStep 2013839 = 3020759) B3020759
theorem B3020765 : Blo 2013435 3020765 := bbase (se 3 (by rfl) ⟨566393, by rfl⟩ : syracuseStep 3020765 = 1132787) (by norm_num)
theorem B2013843 : Blo 2013435 2013843 := bstep (se 1 (by rfl) ⟨1510382, by rfl⟩ : syracuseStep 2013843 = 3020765) B3020765
theorem B4531157 : Blo 2013435 4531157 := bbase (se 7 (by rfl) ⟨53099, by rfl⟩ : syracuseStep 4531157 = 106199) (by norm_num)
theorem B3020771 : Blo 2013435 3020771 := bstep (se 1 (by rfl) ⟨2265578, by rfl⟩ : syracuseStep 3020771 = 4531157) B4531157
theorem B2013847 : Blo 2013435 2013847 := bstep (se 1 (by rfl) ⟨1510385, by rfl⟩ : syracuseStep 2013847 = 3020771) B3020771
theorem B2906501 : Blo 2013435 2906501 := bbase (se 4 (by rfl) ⟨272484, by rfl⟩ : syracuseStep 2906501 = 544969) (by norm_num)
theorem B7750669 : Blo 2013435 7750669 := bstep (se 3 (by rfl) ⟨1453250, by rfl⟩ : syracuseStep 7750669 = 2906501) B2906501
theorem B10334225 : Blo 2013435 10334225 := bstep (se 2 (by rfl) ⟨3875334, by rfl⟩ : syracuseStep 10334225 = 7750669) B7750669
theorem B6889483 : Blo 2013435 6889483 := bstep (se 1 (by rfl) ⟨5167112, by rfl⟩ : syracuseStep 6889483 = 10334225) B10334225
theorem B9185977 : Blo 2013435 9185977 := bstep (se 2 (by rfl) ⟨3444741, by rfl⟩ : syracuseStep 9185977 = 6889483) B6889483
theorem B48991877 : Blo 2013435 48991877 := bstep (se 4 (by rfl) ⟨4592988, by rfl⟩ : syracuseStep 48991877 = 9185977) B9185977
theorem B32661251 : Blo 2013435 32661251 := bstep (se 1 (by rfl) ⟨24495938, by rfl⟩ : syracuseStep 32661251 = 48991877) B48991877
theorem B21774167 : Blo 2013435 21774167 := bstep (se 1 (by rfl) ⟨16330625, by rfl⟩ : syracuseStep 21774167 = 32661251) B32661251
theorem B14516111 : Blo 2013435 14516111 := bstep (se 1 (by rfl) ⟨10887083, by rfl⟩ : syracuseStep 14516111 = 21774167) B21774167
theorem B9677407 : Blo 2013435 9677407 := bstep (se 1 (by rfl) ⟨7258055, by rfl⟩ : syracuseStep 9677407 = 14516111) B14516111
theorem B12903209 : Blo 2013435 12903209 := bstep (se 2 (by rfl) ⟨4838703, by rfl⟩ : syracuseStep 12903209 = 9677407) B9677407
theorem B8602139 : Blo 2013435 8602139 := bstep (se 1 (by rfl) ⟨6451604, by rfl⟩ : syracuseStep 8602139 = 12903209) B12903209
theorem B5734759 : Blo 2013435 5734759 := bstep (se 1 (by rfl) ⟨4301069, by rfl⟩ : syracuseStep 5734759 = 8602139) B8602139
theorem B7646345 : Blo 2013435 7646345 := bstep (se 2 (by rfl) ⟨2867379, by rfl⟩ : syracuseStep 7646345 = 5734759) B5734759
theorem B5097563 : Blo 2013435 5097563 := bstep (se 1 (by rfl) ⟨3823172, by rfl⟩ : syracuseStep 5097563 = 7646345) B7646345
theorem B3398375 : Blo 2013435 3398375 := bstep (se 1 (by rfl) ⟨2548781, by rfl⟩ : syracuseStep 3398375 = 5097563) B5097563
theorem B2265583 : Blo 2013435 2265583 := bstep (se 1 (by rfl) ⟨1699187, by rfl⟩ : syracuseStep 2265583 = 3398375) B3398375
theorem B3020777 : Blo 2013435 3020777 := bstep (se 2 (by rfl) ⟨1132791, by rfl⟩ : syracuseStep 3020777 = 2265583) B2265583
theorem B2013851 : Blo 2013435 2013851 := bstep (se 1 (by rfl) ⟨1510388, by rfl⟩ : syracuseStep 2013851 = 3020777) B3020777
theorem B17204309 : Blo 2013435 17204309 := bbase (se 8 (by rfl) ⟨100806, by rfl⟩ : syracuseStep 17204309 = 201613) (by norm_num)
theorem B11469539 : Blo 2013435 11469539 := bstep (se 1 (by rfl) ⟨8602154, by rfl⟩ : syracuseStep 11469539 = 17204309) B17204309
theorem B7646359 : Blo 2013435 7646359 := bstep (se 1 (by rfl) ⟨5734769, by rfl⟩ : syracuseStep 7646359 = 11469539) B11469539
theorem B10195145 : Blo 2013435 10195145 := bstep (se 2 (by rfl) ⟨3823179, by rfl⟩ : syracuseStep 10195145 = 7646359) B7646359
theorem B6796763 : Blo 2013435 6796763 := bstep (se 1 (by rfl) ⟨5097572, by rfl⟩ : syracuseStep 6796763 = 10195145) B10195145
theorem B4531175 : Blo 2013435 4531175 := bstep (se 1 (by rfl) ⟨3398381, by rfl⟩ : syracuseStep 4531175 = 6796763) B6796763
theorem B3020783 : Blo 2013435 3020783 := bstep (se 1 (by rfl) ⟨2265587, by rfl⟩ : syracuseStep 3020783 = 4531175) B4531175
theorem B2013855 : Blo 2013435 2013855 := bstep (se 1 (by rfl) ⟨1510391, by rfl⟩ : syracuseStep 2013855 = 3020783) B3020783
theorem B3020789 : Blo 2013435 3020789 := bbase (se 5 (by rfl) ⟨141599, by rfl⟩ : syracuseStep 3020789 = 283199) (by norm_num)
theorem B2013859 : Blo 2013435 2013859 := bstep (se 1 (by rfl) ⟨1510394, by rfl⟩ : syracuseStep 2013859 = 3020789) B3020789
theorem B3103789 : Blo 2013435 3103789 := bbase (se 3 (by rfl) ⟨581960, by rfl⟩ : syracuseStep 3103789 = 1163921) (by norm_num)
theorem B4138385 : Blo 2013435 4138385 := bstep (se 2 (by rfl) ⟨1551894, by rfl⟩ : syracuseStep 4138385 = 3103789) B3103789
theorem B11035693 : Blo 2013435 11035693 := bstep (se 3 (by rfl) ⟨2069192, by rfl⟩ : syracuseStep 11035693 = 4138385) B4138385
theorem B14714257 : Blo 2013435 14714257 := bstep (se 2 (by rfl) ⟨5517846, by rfl⟩ : syracuseStep 14714257 = 11035693) B11035693
theorem B19619009 : Blo 2013435 19619009 := bstep (se 2 (by rfl) ⟨7357128, by rfl⟩ : syracuseStep 19619009 = 14714257) B14714257
theorem B13079339 : Blo 2013435 13079339 := bstep (se 1 (by rfl) ⟨9809504, by rfl⟩ : syracuseStep 13079339 = 19619009) B19619009
theorem B8719559 : Blo 2013435 8719559 := bstep (se 1 (by rfl) ⟨6539669, by rfl⟩ : syracuseStep 8719559 = 13079339) B13079339
theorem B5813039 : Blo 2013435 5813039 := bstep (se 1 (by rfl) ⟨4359779, by rfl⟩ : syracuseStep 5813039 = 8719559) B8719559
theorem B3875359 : Blo 2013435 3875359 := bstep (se 1 (by rfl) ⟨2906519, by rfl⟩ : syracuseStep 3875359 = 5813039) B5813039
theorem B5167145 : Blo 2013435 5167145 := bstep (se 2 (by rfl) ⟨1937679, by rfl⟩ : syracuseStep 5167145 = 3875359) B3875359
theorem B3444763 : Blo 2013435 3444763 := bstep (se 1 (by rfl) ⟨2583572, by rfl⟩ : syracuseStep 3444763 = 5167145) B5167145
theorem B4593017 : Blo 2013435 4593017 := bstep (se 2 (by rfl) ⟨1722381, by rfl⟩ : syracuseStep 4593017 = 3444763) B3444763
theorem B3062011 : Blo 2013435 3062011 := bstep (se 1 (by rfl) ⟨2296508, by rfl⟩ : syracuseStep 3062011 = 4593017) B4593017
theorem B4082681 : Blo 2013435 4082681 := bstep (se 2 (by rfl) ⟨1531005, by rfl⟩ : syracuseStep 4082681 = 3062011) B3062011
theorem B10887149 : Blo 2013435 10887149 := bstep (se 3 (by rfl) ⟨2041340, by rfl⟩ : syracuseStep 10887149 = 4082681) B4082681
theorem B7258099 : Blo 2013435 7258099 := bstep (se 1 (by rfl) ⟨5443574, by rfl⟩ : syracuseStep 7258099 = 10887149) B10887149
theorem B9677465 : Blo 2013435 9677465 := bstep (se 2 (by rfl) ⟨3629049, by rfl⟩ : syracuseStep 9677465 = 7258099) B7258099
theorem B6451643 : Blo 2013435 6451643 := bstep (se 1 (by rfl) ⟨4838732, by rfl⟩ : syracuseStep 6451643 = 9677465) B9677465
theorem B4301095 : Blo 2013435 4301095 := bstep (se 1 (by rfl) ⟨3225821, by rfl⟩ : syracuseStep 4301095 = 6451643) B6451643
theorem B5734793 : Blo 2013435 5734793 := bstep (se 2 (by rfl) ⟨2150547, by rfl⟩ : syracuseStep 5734793 = 4301095) B4301095
theorem B3823195 : Blo 2013435 3823195 := bstep (se 1 (by rfl) ⟨2867396, by rfl⟩ : syracuseStep 3823195 = 5734793) B5734793
theorem B5097593 : Blo 2013435 5097593 := bstep (se 2 (by rfl) ⟨1911597, by rfl⟩ : syracuseStep 5097593 = 3823195) B3823195
theorem B3398395 : Blo 2013435 3398395 := bstep (se 1 (by rfl) ⟨2548796, by rfl⟩ : syracuseStep 3398395 = 5097593) B5097593
theorem B4531193 : Blo 2013435 4531193 := bstep (se 2 (by rfl) ⟨1699197, by rfl⟩ : syracuseStep 4531193 = 3398395) B3398395
theorem B3020795 : Blo 2013435 3020795 := bstep (se 1 (by rfl) ⟨2265596, by rfl⟩ : syracuseStep 3020795 = 4531193) B4531193
theorem B2013863 : Blo 2013435 2013863 := bstep (se 1 (by rfl) ⟨1510397, by rfl⟩ : syracuseStep 2013863 = 3020795) B3020795
theorem B2265601 : Blo 2013435 2265601 := bbase (se 2 (by rfl) ⟨849600, by rfl⟩ : syracuseStep 2265601 = 1699201) (by norm_num)
theorem B3020801 : Blo 2013435 3020801 := bstep (se 2 (by rfl) ⟨1132800, by rfl⟩ : syracuseStep 3020801 = 2265601) B2265601
theorem B2013867 : Blo 2013435 2013867 := bstep (se 1 (by rfl) ⟨1510400, by rfl⟩ : syracuseStep 2013867 = 3020801) B3020801
theorem B5097613 : Blo 2013435 5097613 := bbase (se 3 (by rfl) ⟨955802, by rfl⟩ : syracuseStep 5097613 = 1911605) (by norm_num)
theorem B6796817 : Blo 2013435 6796817 := bstep (se 2 (by rfl) ⟨2548806, by rfl⟩ : syracuseStep 6796817 = 5097613) B5097613
theorem B4531211 : Blo 2013435 4531211 := bstep (se 1 (by rfl) ⟨3398408, by rfl⟩ : syracuseStep 4531211 = 6796817) B6796817
theorem B3020807 : Blo 2013435 3020807 := bstep (se 1 (by rfl) ⟨2265605, by rfl⟩ : syracuseStep 3020807 = 4531211) B4531211
theorem B2013871 : Blo 2013435 2013871 := bstep (se 1 (by rfl) ⟨1510403, by rfl⟩ : syracuseStep 2013871 = 3020807) B3020807
theorem B3020813 : Blo 2013435 3020813 := bbase (se 3 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 3020813 = 1132805) (by norm_num)
theorem B2013875 : Blo 2013435 2013875 := bstep (se 1 (by rfl) ⟨1510406, by rfl⟩ : syracuseStep 2013875 = 3020813) B3020813
theorem B4531229 : Blo 2013435 4531229 := bbase (se 3 (by rfl) ⟨849605, by rfl⟩ : syracuseStep 4531229 = 1699211) (by norm_num)
theorem B3020819 : Blo 2013435 3020819 := bstep (se 1 (by rfl) ⟨2265614, by rfl⟩ : syracuseStep 3020819 = 4531229) B4531229
theorem B2013879 : Blo 2013435 2013879 := bstep (se 1 (by rfl) ⟨1510409, by rfl⟩ : syracuseStep 2013879 = 3020819) B3020819
theorem B3398429 : Blo 2013435 3398429 := bbase (se 3 (by rfl) ⟨637205, by rfl⟩ : syracuseStep 3398429 = 1274411) (by norm_num)
theorem B2265619 : Blo 2013435 2265619 := bstep (se 1 (by rfl) ⟨1699214, by rfl⟩ : syracuseStep 2265619 = 3398429) B3398429
theorem B3020825 : Blo 2013435 3020825 := bstep (se 2 (by rfl) ⟨1132809, by rfl⟩ : syracuseStep 3020825 = 2265619) B2265619
theorem B2013883 : Blo 2013435 2013883 := bstep (se 1 (by rfl) ⟨1510412, by rfl⟩ : syracuseStep 2013883 = 3020825) B3020825
theorem B4838789 : Blo 2013435 4838789 := bbase (se 4 (by rfl) ⟨453636, by rfl⟩ : syracuseStep 4838789 = 907273) (by norm_num)
theorem B12903437 : Blo 2013435 12903437 := bstep (se 3 (by rfl) ⟨2419394, by rfl⟩ : syracuseStep 12903437 = 4838789) B4838789
theorem B8602291 : Blo 2013435 8602291 := bstep (se 1 (by rfl) ⟨6451718, by rfl⟩ : syracuseStep 8602291 = 12903437) B12903437
theorem B11469721 : Blo 2013435 11469721 := bstep (se 2 (by rfl) ⟨4301145, by rfl⟩ : syracuseStep 11469721 = 8602291) B8602291
theorem B15292961 : Blo 2013435 15292961 := bstep (se 2 (by rfl) ⟨5734860, by rfl⟩ : syracuseStep 15292961 = 11469721) B11469721
theorem B10195307 : Blo 2013435 10195307 := bstep (se 1 (by rfl) ⟨7646480, by rfl⟩ : syracuseStep 10195307 = 15292961) B15292961
theorem B6796871 : Blo 2013435 6796871 := bstep (se 1 (by rfl) ⟨5097653, by rfl⟩ : syracuseStep 6796871 = 10195307) B10195307
theorem B4531247 : Blo 2013435 4531247 := bstep (se 1 (by rfl) ⟨3398435, by rfl⟩ : syracuseStep 4531247 = 6796871) B6796871
theorem B3020831 : Blo 2013435 3020831 := bstep (se 1 (by rfl) ⟨2265623, by rfl⟩ : syracuseStep 3020831 = 4531247) B4531247
theorem B2013887 : Blo 2013435 2013887 := bstep (se 1 (by rfl) ⟨1510415, by rfl⟩ : syracuseStep 2013887 = 3020831) B3020831
theorem B3020837 : Blo 2013435 3020837 := bbase (se 4 (by rfl) ⟨283203, by rfl⟩ : syracuseStep 3020837 = 566407) (by norm_num)
theorem B2013891 : Blo 2013435 2013891 := bstep (se 1 (by rfl) ⟨1510418, by rfl⟩ : syracuseStep 2013891 = 3020837) B3020837
theorem B2548837 : Blo 2013435 2548837 := bbase (se 4 (by rfl) ⟨238953, by rfl⟩ : syracuseStep 2548837 = 477907) (by norm_num)
theorem B3398449 : Blo 2013435 3398449 := bstep (se 2 (by rfl) ⟨1274418, by rfl⟩ : syracuseStep 3398449 = 2548837) B2548837
theorem B4531265 : Blo 2013435 4531265 := bstep (se 2 (by rfl) ⟨1699224, by rfl⟩ : syracuseStep 4531265 = 3398449) B3398449
theorem B3020843 : Blo 2013435 3020843 := bstep (se 1 (by rfl) ⟨2265632, by rfl⟩ : syracuseStep 3020843 = 4531265) B4531265
theorem B2013895 : Blo 2013435 2013895 := bstep (se 1 (by rfl) ⟨1510421, by rfl⟩ : syracuseStep 2013895 = 3020843) B3020843
theorem B2265637 : Blo 2013435 2265637 := bbase (se 4 (by rfl) ⟨212403, by rfl⟩ : syracuseStep 2265637 = 424807) (by norm_num)
theorem B3020849 : Blo 2013435 3020849 := bstep (se 2 (by rfl) ⟨1132818, by rfl⟩ : syracuseStep 3020849 = 2265637) B2265637
theorem B2013899 : Blo 2013435 2013899 := bstep (se 1 (by rfl) ⟨1510424, by rfl⟩ : syracuseStep 2013899 = 3020849) B3020849
theorem B2041381 : Blo 2013435 2041381 := bbase (se 4 (by rfl) ⟨191379, by rfl⟩ : syracuseStep 2041381 = 382759) (by norm_num)
theorem B10887365 : Blo 2013435 10887365 := bstep (se 4 (by rfl) ⟨1020690, by rfl⟩ : syracuseStep 10887365 = 2041381) B2041381
theorem B7258243 : Blo 2013435 7258243 := bstep (se 1 (by rfl) ⟨5443682, by rfl⟩ : syracuseStep 7258243 = 10887365) B10887365
theorem B9677657 : Blo 2013435 9677657 := bstep (se 2 (by rfl) ⟨3629121, by rfl⟩ : syracuseStep 9677657 = 7258243) B7258243
theorem B6451771 : Blo 2013435 6451771 := bstep (se 1 (by rfl) ⟨4838828, by rfl⟩ : syracuseStep 6451771 = 9677657) B9677657
theorem B8602361 : Blo 2013435 8602361 := bstep (se 2 (by rfl) ⟨3225885, by rfl⟩ : syracuseStep 8602361 = 6451771) B6451771
theorem B5734907 : Blo 2013435 5734907 := bstep (se 1 (by rfl) ⟨4301180, by rfl⟩ : syracuseStep 5734907 = 8602361) B8602361
theorem B3823271 : Blo 2013435 3823271 := bstep (se 1 (by rfl) ⟨2867453, by rfl⟩ : syracuseStep 3823271 = 5734907) B5734907
theorem B2548847 : Blo 2013435 2548847 := bstep (se 1 (by rfl) ⟨1911635, by rfl⟩ : syracuseStep 2548847 = 3823271) B3823271
theorem B6796925 : Blo 2013435 6796925 := bstep (se 3 (by rfl) ⟨1274423, by rfl⟩ : syracuseStep 6796925 = 2548847) B2548847
theorem B4531283 : Blo 2013435 4531283 := bstep (se 1 (by rfl) ⟨3398462, by rfl⟩ : syracuseStep 4531283 = 6796925) B6796925
theorem B3020855 : Blo 2013435 3020855 := bstep (se 1 (by rfl) ⟨2265641, by rfl⟩ : syracuseStep 3020855 = 4531283) B4531283
theorem B2013903 : Blo 2013435 2013903 := bstep (se 1 (by rfl) ⟨1510427, by rfl⟩ : syracuseStep 2013903 = 3020855) B3020855
theorem B3020861 : Blo 2013435 3020861 := bbase (se 3 (by rfl) ⟨566411, by rfl⟩ : syracuseStep 3020861 = 1132823) (by norm_num)
theorem B2013907 : Blo 2013435 2013907 := bstep (se 1 (by rfl) ⟨1510430, by rfl⟩ : syracuseStep 2013907 = 3020861) B3020861
theorem B4531301 : Blo 2013435 4531301 := bbase (se 4 (by rfl) ⟨424809, by rfl⟩ : syracuseStep 4531301 = 849619) (by norm_num)
theorem B3020867 : Blo 2013435 3020867 := bstep (se 1 (by rfl) ⟨2265650, by rfl⟩ : syracuseStep 3020867 = 4531301) B4531301
theorem B2013911 : Blo 2013435 2013911 := bstep (se 1 (by rfl) ⟨1510433, by rfl⟩ : syracuseStep 2013911 = 3020867) B3020867
theorem B5097725 : Blo 2013435 5097725 := bbase (se 3 (by rfl) ⟨955823, by rfl⟩ : syracuseStep 5097725 = 1911647) (by norm_num)
theorem B3398483 : Blo 2013435 3398483 := bstep (se 1 (by rfl) ⟨2548862, by rfl⟩ : syracuseStep 3398483 = 5097725) B5097725
theorem B2265655 : Blo 2013435 2265655 := bstep (se 1 (by rfl) ⟨1699241, by rfl⟩ : syracuseStep 2265655 = 3398483) B3398483
theorem B3020873 : Blo 2013435 3020873 := bstep (se 2 (by rfl) ⟨1132827, by rfl⟩ : syracuseStep 3020873 = 2265655) B2265655
theorem B2013915 : Blo 2013435 2013915 := bstep (se 1 (by rfl) ⟨1510436, by rfl⟩ : syracuseStep 2013915 = 3020873) B3020873
theorem B3823301 : Blo 2013435 3823301 := bbase (se 4 (by rfl) ⟨358434, by rfl⟩ : syracuseStep 3823301 = 716869) (by norm_num)
theorem B10195469 : Blo 2013435 10195469 := bstep (se 3 (by rfl) ⟨1911650, by rfl⟩ : syracuseStep 10195469 = 3823301) B3823301
theorem B6796979 : Blo 2013435 6796979 := bstep (se 1 (by rfl) ⟨5097734, by rfl⟩ : syracuseStep 6796979 = 10195469) B10195469
theorem B4531319 : Blo 2013435 4531319 := bstep (se 1 (by rfl) ⟨3398489, by rfl⟩ : syracuseStep 4531319 = 6796979) B6796979
theorem B3020879 : Blo 2013435 3020879 := bstep (se 1 (by rfl) ⟨2265659, by rfl⟩ : syracuseStep 3020879 = 4531319) B4531319
theorem B2013919 : Blo 2013435 2013919 := bstep (se 1 (by rfl) ⟨1510439, by rfl⟩ : syracuseStep 2013919 = 3020879) B3020879
theorem B3020885 : Blo 2013435 3020885 := bbase (se 8 (by rfl) ⟨17700, by rfl⟩ : syracuseStep 3020885 = 35401) (by norm_num)
theorem B2013923 : Blo 2013435 2013923 := bstep (se 1 (by rfl) ⟨1510442, by rfl⟩ : syracuseStep 2013923 = 3020885) B3020885
theorem B2041405 : Blo 2013435 2041405 := bbase (se 3 (by rfl) ⟨382763, by rfl⟩ : syracuseStep 2041405 = 765527) (by norm_num)
theorem B43549973 : Blo 2013435 43549973 := bstep (se 6 (by rfl) ⟨1020702, by rfl⟩ : syracuseStep 43549973 = 2041405) B2041405
theorem B29033315 : Blo 2013435 29033315 := bstep (se 1 (by rfl) ⟨21774986, by rfl⟩ : syracuseStep 29033315 = 43549973) B43549973
theorem B19355543 : Blo 2013435 19355543 := bstep (se 1 (by rfl) ⟨14516657, by rfl⟩ : syracuseStep 19355543 = 29033315) B29033315
theorem B12903695 : Blo 2013435 12903695 := bstep (se 1 (by rfl) ⟨9677771, by rfl⟩ : syracuseStep 12903695 = 19355543) B19355543
theorem B8602463 : Blo 2013435 8602463 := bstep (se 1 (by rfl) ⟨6451847, by rfl⟩ : syracuseStep 8602463 = 12903695) B12903695
theorem B5734975 : Blo 2013435 5734975 := bstep (se 1 (by rfl) ⟨4301231, by rfl⟩ : syracuseStep 5734975 = 8602463) B8602463
theorem B7646633 : Blo 2013435 7646633 := bstep (se 2 (by rfl) ⟨2867487, by rfl⟩ : syracuseStep 7646633 = 5734975) B5734975
theorem B5097755 : Blo 2013435 5097755 := bstep (se 1 (by rfl) ⟨3823316, by rfl⟩ : syracuseStep 5097755 = 7646633) B7646633
theorem B3398503 : Blo 2013435 3398503 := bstep (se 1 (by rfl) ⟨2548877, by rfl⟩ : syracuseStep 3398503 = 5097755) B5097755
theorem B4531337 : Blo 2013435 4531337 := bstep (se 2 (by rfl) ⟨1699251, by rfl⟩ : syracuseStep 4531337 = 3398503) B3398503
theorem B3020891 : Blo 2013435 3020891 := bstep (se 1 (by rfl) ⟨2265668, by rfl⟩ : syracuseStep 3020891 = 4531337) B4531337
theorem B2013927 : Blo 2013435 2013927 := bstep (se 1 (by rfl) ⟨1510445, by rfl⟩ : syracuseStep 2013927 = 3020891) B3020891
theorem B2265673 : Blo 2013435 2265673 := bbase (se 2 (by rfl) ⟨849627, by rfl⟩ : syracuseStep 2265673 = 1699255) (by norm_num)
theorem B3020897 : Blo 2013435 3020897 := bstep (se 2 (by rfl) ⟨1132836, by rfl⟩ : syracuseStep 3020897 = 2265673) B2265673
theorem B2013931 : Blo 2013435 2013931 := bstep (se 1 (by rfl) ⟨1510448, by rfl⟩ : syracuseStep 2013931 = 3020897) B3020897
theorem B7258357 : Blo 2013435 7258357 := bbase (se 5 (by rfl) ⟨340235, by rfl⟩ : syracuseStep 7258357 = 680471) (by norm_num)
theorem B9677809 : Blo 2013435 9677809 := bstep (se 2 (by rfl) ⟨3629178, by rfl⟩ : syracuseStep 9677809 = 7258357) B7258357
theorem B12903745 : Blo 2013435 12903745 := bstep (se 2 (by rfl) ⟨4838904, by rfl⟩ : syracuseStep 12903745 = 9677809) B9677809
theorem B17204993 : Blo 2013435 17204993 := bstep (se 2 (by rfl) ⟨6451872, by rfl⟩ : syracuseStep 17204993 = 12903745) B12903745
theorem B11469995 : Blo 2013435 11469995 := bstep (se 1 (by rfl) ⟨8602496, by rfl⟩ : syracuseStep 11469995 = 17204993) B17204993
theorem B7646663 : Blo 2013435 7646663 := bstep (se 1 (by rfl) ⟨5734997, by rfl⟩ : syracuseStep 7646663 = 11469995) B11469995
theorem B5097775 : Blo 2013435 5097775 := bstep (se 1 (by rfl) ⟨3823331, by rfl⟩ : syracuseStep 5097775 = 7646663) B7646663
theorem B6797033 : Blo 2013435 6797033 := bstep (se 2 (by rfl) ⟨2548887, by rfl⟩ : syracuseStep 6797033 = 5097775) B5097775
theorem B4531355 : Blo 2013435 4531355 := bstep (se 1 (by rfl) ⟨3398516, by rfl⟩ : syracuseStep 4531355 = 6797033) B6797033
theorem B3020903 : Blo 2013435 3020903 := bstep (se 1 (by rfl) ⟨2265677, by rfl⟩ : syracuseStep 3020903 = 4531355) B4531355
theorem B2013935 : Blo 2013435 2013935 := bstep (se 1 (by rfl) ⟨1510451, by rfl⟩ : syracuseStep 2013935 = 3020903) B3020903
theorem B3020909 : Blo 2013435 3020909 := bbase (se 3 (by rfl) ⟨566420, by rfl⟩ : syracuseStep 3020909 = 1132841) (by norm_num)
theorem B2013939 : Blo 2013435 2013939 := bstep (se 1 (by rfl) ⟨1510454, by rfl⟩ : syracuseStep 2013939 = 3020909) B3020909
theorem B4531373 : Blo 2013435 4531373 := bbase (se 3 (by rfl) ⟨849632, by rfl⟩ : syracuseStep 4531373 = 1699265) (by norm_num)
theorem B3020915 : Blo 2013435 3020915 := bstep (se 1 (by rfl) ⟨2265686, by rfl⟩ : syracuseStep 3020915 = 4531373) B4531373
theorem B2013943 : Blo 2013435 2013943 := bstep (se 1 (by rfl) ⟨1510457, by rfl⟩ : syracuseStep 2013943 = 3020915) B3020915
theorem B10887605 : Blo 2013435 10887605 := bbase (se 5 (by rfl) ⟨510356, by rfl⟩ : syracuseStep 10887605 = 1020713) (by norm_num)
theorem B7258403 : Blo 2013435 7258403 := bstep (se 1 (by rfl) ⟨5443802, by rfl⟩ : syracuseStep 7258403 = 10887605) B10887605
theorem B4838935 : Blo 2013435 4838935 := bstep (se 1 (by rfl) ⟨3629201, by rfl⟩ : syracuseStep 4838935 = 7258403) B7258403
theorem B6451913 : Blo 2013435 6451913 := bstep (se 2 (by rfl) ⟨2419467, by rfl⟩ : syracuseStep 6451913 = 4838935) B4838935
theorem B4301275 : Blo 2013435 4301275 := bstep (se 1 (by rfl) ⟨3225956, by rfl⟩ : syracuseStep 4301275 = 6451913) B6451913
theorem B5735033 : Blo 2013435 5735033 := bstep (se 2 (by rfl) ⟨2150637, by rfl⟩ : syracuseStep 5735033 = 4301275) B4301275
theorem B3823355 : Blo 2013435 3823355 := bstep (se 1 (by rfl) ⟨2867516, by rfl⟩ : syracuseStep 3823355 = 5735033) B5735033
theorem B2548903 : Blo 2013435 2548903 := bstep (se 1 (by rfl) ⟨1911677, by rfl⟩ : syracuseStep 2548903 = 3823355) B3823355
theorem B3398537 : Blo 2013435 3398537 := bstep (se 2 (by rfl) ⟨1274451, by rfl⟩ : syracuseStep 3398537 = 2548903) B2548903
theorem B2265691 : Blo 2013435 2265691 := bstep (se 1 (by rfl) ⟨1699268, by rfl⟩ : syracuseStep 2265691 = 3398537) B3398537
theorem B3020921 : Blo 2013435 3020921 := bstep (se 2 (by rfl) ⟨1132845, by rfl⟩ : syracuseStep 3020921 = 2265691) B2265691
theorem B2013947 : Blo 2013435 2013947 := bstep (se 1 (by rfl) ⟨1510460, by rfl⟩ : syracuseStep 2013947 = 3020921) B3020921
theorem B8165717 : Blo 2013435 8165717 := bbase (se 10 (by rfl) ⟨11961, by rfl⟩ : syracuseStep 8165717 = 23923) (by norm_num)
theorem B5443811 : Blo 2013435 5443811 := bstep (se 1 (by rfl) ⟨4082858, by rfl⟩ : syracuseStep 5443811 = 8165717) B8165717
theorem B3629207 : Blo 2013435 3629207 := bstep (se 1 (by rfl) ⟨2721905, by rfl⟩ : syracuseStep 3629207 = 5443811) B5443811
theorem B9677885 : Blo 2013435 9677885 := bstep (se 3 (by rfl) ⟨1814603, by rfl⟩ : syracuseStep 9677885 = 3629207) B3629207
theorem B25807693 : Blo 2013435 25807693 := bstep (se 3 (by rfl) ⟨4838942, by rfl⟩ : syracuseStep 25807693 = 9677885) B9677885
theorem B34410257 : Blo 2013435 34410257 := bstep (se 2 (by rfl) ⟨12903846, by rfl⟩ : syracuseStep 34410257 = 25807693) B25807693
theorem B22940171 : Blo 2013435 22940171 := bstep (se 1 (by rfl) ⟨17205128, by rfl⟩ : syracuseStep 22940171 = 34410257) B34410257
theorem B15293447 : Blo 2013435 15293447 := bstep (se 1 (by rfl) ⟨11470085, by rfl⟩ : syracuseStep 15293447 = 22940171) B22940171
theorem B10195631 : Blo 2013435 10195631 := bstep (se 1 (by rfl) ⟨7646723, by rfl⟩ : syracuseStep 10195631 = 15293447) B15293447
theorem B6797087 : Blo 2013435 6797087 := bstep (se 1 (by rfl) ⟨5097815, by rfl⟩ : syracuseStep 6797087 = 10195631) B10195631
theorem B4531391 : Blo 2013435 4531391 := bstep (se 1 (by rfl) ⟨3398543, by rfl⟩ : syracuseStep 4531391 = 6797087) B6797087
theorem B3020927 : Blo 2013435 3020927 := bstep (se 1 (by rfl) ⟨2265695, by rfl⟩ : syracuseStep 3020927 = 4531391) B4531391
theorem B2013951 : Blo 2013435 2013951 := bstep (se 1 (by rfl) ⟨1510463, by rfl⟩ : syracuseStep 2013951 = 3020927) B3020927
theorem B3020933 : Blo 2013435 3020933 := bbase (se 4 (by rfl) ⟨283212, by rfl⟩ : syracuseStep 3020933 = 566425) (by norm_num)
theorem B2013955 : Blo 2013435 2013955 := bstep (se 1 (by rfl) ⟨1510466, by rfl⟩ : syracuseStep 2013955 = 3020933) B3020933
theorem B3398557 : Blo 2013435 3398557 := bbase (se 3 (by rfl) ⟨637229, by rfl⟩ : syracuseStep 3398557 = 1274459) (by norm_num)
theorem B4531409 : Blo 2013435 4531409 := bstep (se 2 (by rfl) ⟨1699278, by rfl⟩ : syracuseStep 4531409 = 3398557) B3398557
theorem B3020939 : Blo 2013435 3020939 := bstep (se 1 (by rfl) ⟨2265704, by rfl⟩ : syracuseStep 3020939 = 4531409) B4531409
theorem B2013959 : Blo 2013435 2013959 := bstep (se 1 (by rfl) ⟨1510469, by rfl⟩ : syracuseStep 2013959 = 3020939) B3020939
theorem B2265709 : Blo 2013435 2265709 := bbase (se 3 (by rfl) ⟨424820, by rfl⟩ : syracuseStep 2265709 = 849641) (by norm_num)
theorem B3020945 : Blo 2013435 3020945 := bstep (se 2 (by rfl) ⟨1132854, by rfl⟩ : syracuseStep 3020945 = 2265709) B2265709
theorem B2013963 : Blo 2013435 2013963 := bstep (se 1 (by rfl) ⟨1510472, by rfl⟩ : syracuseStep 2013963 = 3020945) B3020945
theorem B6797141 : Blo 2013435 6797141 := bbase (se 9 (by rfl) ⟨19913, by rfl⟩ : syracuseStep 6797141 = 39827) (by norm_num)
theorem B4531427 : Blo 2013435 4531427 := bstep (se 1 (by rfl) ⟨3398570, by rfl⟩ : syracuseStep 4531427 = 6797141) B6797141
theorem B3020951 : Blo 2013435 3020951 := bstep (se 1 (by rfl) ⟨2265713, by rfl⟩ : syracuseStep 3020951 = 4531427) B4531427
theorem B2013967 : Blo 2013435 2013967 := bstep (se 1 (by rfl) ⟨1510475, by rfl⟩ : syracuseStep 2013967 = 3020951) B3020951
theorem B3020957 : Blo 2013435 3020957 := bbase (se 3 (by rfl) ⟨566429, by rfl⟩ : syracuseStep 3020957 = 1132859) (by norm_num)
theorem B2013971 : Blo 2013435 2013971 := bstep (se 1 (by rfl) ⟨1510478, by rfl⟩ : syracuseStep 2013971 = 3020957) B3020957
theorem B4531445 : Blo 2013435 4531445 := bbase (se 5 (by rfl) ⟨212411, by rfl⟩ : syracuseStep 4531445 = 424823) (by norm_num)
theorem B3020963 : Blo 2013435 3020963 := bstep (se 1 (by rfl) ⟨2265722, by rfl⟩ : syracuseStep 3020963 = 4531445) B4531445
theorem B2013975 : Blo 2013435 2013975 := bstep (se 1 (by rfl) ⟨1510481, by rfl⟩ : syracuseStep 2013975 = 3020963) B3020963
theorem B4419517 : Blo 2013435 4419517 := bbase (se 3 (by rfl) ⟨828659, by rfl⟩ : syracuseStep 4419517 = 1657319) (by norm_num)
theorem B5892689 : Blo 2013435 5892689 := bstep (se 2 (by rfl) ⟨2209758, by rfl⟩ : syracuseStep 5892689 = 4419517) B4419517
theorem B15713837 : Blo 2013435 15713837 := bstep (se 3 (by rfl) ⟨2946344, by rfl⟩ : syracuseStep 15713837 = 5892689) B5892689
theorem B10475891 : Blo 2013435 10475891 := bstep (se 1 (by rfl) ⟨7856918, by rfl⟩ : syracuseStep 10475891 = 15713837) B15713837
theorem B6983927 : Blo 2013435 6983927 := bstep (se 1 (by rfl) ⟨5237945, by rfl⟩ : syracuseStep 6983927 = 10475891) B10475891
theorem B4655951 : Blo 2013435 4655951 := bstep (se 1 (by rfl) ⟨3491963, by rfl⟩ : syracuseStep 4655951 = 6983927) B6983927
theorem B3103967 : Blo 2013435 3103967 := bstep (se 1 (by rfl) ⟨2327975, by rfl⟩ : syracuseStep 3103967 = 4655951) B4655951
theorem B2069311 : Blo 2013435 2069311 := bstep (se 1 (by rfl) ⟨1551983, by rfl⟩ : syracuseStep 2069311 = 3103967) B3103967
theorem B2759081 : Blo 2013435 2759081 := bstep (se 2 (by rfl) ⟨1034655, by rfl⟩ : syracuseStep 2759081 = 2069311) B2069311
theorem B7357549 : Blo 2013435 7357549 := bstep (se 3 (by rfl) ⟨1379540, by rfl⟩ : syracuseStep 7357549 = 2759081) B2759081
theorem B9810065 : Blo 2013435 9810065 := bstep (se 2 (by rfl) ⟨3678774, by rfl⟩ : syracuseStep 9810065 = 7357549) B7357549
theorem B6540043 : Blo 2013435 6540043 := bstep (se 1 (by rfl) ⟨4905032, by rfl⟩ : syracuseStep 6540043 = 9810065) B9810065
theorem B8720057 : Blo 2013435 8720057 := bstep (se 2 (by rfl) ⟨3270021, by rfl⟩ : syracuseStep 8720057 = 6540043) B6540043
theorem B5813371 : Blo 2013435 5813371 := bstep (se 1 (by rfl) ⟨4360028, by rfl⟩ : syracuseStep 5813371 = 8720057) B8720057
theorem B7751161 : Blo 2013435 7751161 := bstep (se 2 (by rfl) ⟨2906685, by rfl⟩ : syracuseStep 7751161 = 5813371) B5813371
theorem B10334881 : Blo 2013435 10334881 := bstep (se 2 (by rfl) ⟨3875580, by rfl⟩ : syracuseStep 10334881 = 7751161) B7751161
theorem B13779841 : Blo 2013435 13779841 := bstep (se 2 (by rfl) ⟨5167440, by rfl⟩ : syracuseStep 13779841 = 10334881) B10334881
theorem B18373121 : Blo 2013435 18373121 := bstep (se 2 (by rfl) ⟨6889920, by rfl⟩ : syracuseStep 18373121 = 13779841) B13779841
theorem B12248747 : Blo 2013435 12248747 := bstep (se 1 (by rfl) ⟨9186560, by rfl⟩ : syracuseStep 12248747 = 18373121) B18373121
theorem B8165831 : Blo 2013435 8165831 := bstep (se 1 (by rfl) ⟨6124373, by rfl⟩ : syracuseStep 8165831 = 12248747) B12248747
theorem B21775549 : Blo 2013435 21775549 := bstep (se 3 (by rfl) ⟨4082915, by rfl⟩ : syracuseStep 21775549 = 8165831) B8165831
theorem B29034065 : Blo 2013435 29034065 := bstep (se 2 (by rfl) ⟨10887774, by rfl⟩ : syracuseStep 29034065 = 21775549) B21775549
theorem B19356043 : Blo 2013435 19356043 := bstep (se 1 (by rfl) ⟨14517032, by rfl⟩ : syracuseStep 19356043 = 29034065) B29034065
theorem B25808057 : Blo 2013435 25808057 := bstep (se 2 (by rfl) ⟨9678021, by rfl⟩ : syracuseStep 25808057 = 19356043) B19356043
theorem B17205371 : Blo 2013435 17205371 := bstep (se 1 (by rfl) ⟨12904028, by rfl⟩ : syracuseStep 17205371 = 25808057) B25808057
theorem B11470247 : Blo 2013435 11470247 := bstep (se 1 (by rfl) ⟨8602685, by rfl⟩ : syracuseStep 11470247 = 17205371) B17205371
theorem B7646831 : Blo 2013435 7646831 := bstep (se 1 (by rfl) ⟨5735123, by rfl⟩ : syracuseStep 7646831 = 11470247) B11470247
theorem B5097887 : Blo 2013435 5097887 := bstep (se 1 (by rfl) ⟨3823415, by rfl⟩ : syracuseStep 5097887 = 7646831) B7646831
theorem B3398591 : Blo 2013435 3398591 := bstep (se 1 (by rfl) ⟨2548943, by rfl⟩ : syracuseStep 3398591 = 5097887) B5097887
theorem B2265727 : Blo 2013435 2265727 := bstep (se 1 (by rfl) ⟨1699295, by rfl⟩ : syracuseStep 2265727 = 3398591) B3398591
theorem B3020969 : Blo 2013435 3020969 := bstep (se 2 (by rfl) ⟨1132863, by rfl⟩ : syracuseStep 3020969 = 2265727) B2265727
theorem B2013979 : Blo 2013435 2013979 := bstep (se 1 (by rfl) ⟨1510484, by rfl⟩ : syracuseStep 2013979 = 3020969) B3020969
theorem B10887797 : Blo 2013435 10887797 := bbase (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) (by norm_num)
theorem B7258531 : Blo 2013435 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B9678041 : Blo 2013435 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B6452027 : Blo 2013435 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B4301351 : Blo 2013435 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B2867567 : Blo 2013435 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B7646845 : Blo 2013435 7646845 := bstep (se 3 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 7646845 = 2867567) B2867567
theorem B10195793 : Blo 2013435 10195793 := bstep (se 2 (by rfl) ⟨3823422, by rfl⟩ : syracuseStep 10195793 = 7646845) B7646845
theorem B6797195 : Blo 2013435 6797195 := bstep (se 1 (by rfl) ⟨5097896, by rfl⟩ : syracuseStep 6797195 = 10195793) B10195793
theorem B4531463 : Blo 2013435 4531463 := bstep (se 1 (by rfl) ⟨3398597, by rfl⟩ : syracuseStep 4531463 = 6797195) B6797195
theorem B3020975 : Blo 2013435 3020975 := bstep (se 1 (by rfl) ⟨2265731, by rfl⟩ : syracuseStep 3020975 = 4531463) B4531463
theorem B2013983 : Blo 2013435 2013983 := bstep (se 1 (by rfl) ⟨1510487, by rfl⟩ : syracuseStep 2013983 = 3020975) B3020975
theorem B3020981 : Blo 2013435 3020981 := bbase (se 5 (by rfl) ⟨141608, by rfl⟩ : syracuseStep 3020981 = 283217) (by norm_num)
theorem B2013987 : Blo 2013435 2013987 := bstep (se 1 (by rfl) ⟨1510490, by rfl⟩ : syracuseStep 2013987 = 3020981) B3020981
theorem B5097917 : Blo 2013435 5097917 := bbase (se 3 (by rfl) ⟨955859, by rfl⟩ : syracuseStep 5097917 = 1911719) (by norm_num)
theorem B3398611 : Blo 2013435 3398611 := bstep (se 1 (by rfl) ⟨2548958, by rfl⟩ : syracuseStep 3398611 = 5097917) B5097917
theorem B4531481 : Blo 2013435 4531481 := bstep (se 2 (by rfl) ⟨1699305, by rfl⟩ : syracuseStep 4531481 = 3398611) B3398611
theorem B3020987 : Blo 2013435 3020987 := bstep (se 1 (by rfl) ⟨2265740, by rfl⟩ : syracuseStep 3020987 = 4531481) B4531481
theorem B2013991 : Blo 2013435 2013991 := bstep (se 1 (by rfl) ⟨1510493, by rfl⟩ : syracuseStep 2013991 = 3020987) B3020987
theorem B2265745 : Blo 2013435 2265745 := bbase (se 2 (by rfl) ⟨849654, by rfl⟩ : syracuseStep 2265745 = 1699309) (by norm_num)
theorem B3020993 : Blo 2013435 3020993 := bstep (se 2 (by rfl) ⟨1132872, by rfl⟩ : syracuseStep 3020993 = 2265745) B2265745
theorem B2013995 : Blo 2013435 2013995 := bstep (se 1 (by rfl) ⟨1510496, by rfl⟩ : syracuseStep 2013995 = 3020993) B3020993
theorem B3823453 : Blo 2013435 3823453 := bbase (se 3 (by rfl) ⟨716897, by rfl⟩ : syracuseStep 3823453 = 1433795) (by norm_num)
theorem B5097937 : Blo 2013435 5097937 := bstep (se 2 (by rfl) ⟨1911726, by rfl⟩ : syracuseStep 5097937 = 3823453) B3823453
theorem B6797249 : Blo 2013435 6797249 := bstep (se 2 (by rfl) ⟨2548968, by rfl⟩ : syracuseStep 6797249 = 5097937) B5097937
theorem B4531499 : Blo 2013435 4531499 := bstep (se 1 (by rfl) ⟨3398624, by rfl⟩ : syracuseStep 4531499 = 6797249) B6797249
theorem B3020999 : Blo 2013435 3020999 := bstep (se 1 (by rfl) ⟨2265749, by rfl⟩ : syracuseStep 3020999 = 4531499) B4531499
theorem B2013999 : Blo 2013435 2013999 := bstep (se 1 (by rfl) ⟨1510499, by rfl⟩ : syracuseStep 2013999 = 3020999) B3020999
theorem B3021005 : Blo 2013435 3021005 := bbase (se 3 (by rfl) ⟨566438, by rfl⟩ : syracuseStep 3021005 = 1132877) (by norm_num)
theorem B2014003 : Blo 2013435 2014003 := bstep (se 1 (by rfl) ⟨1510502, by rfl⟩ : syracuseStep 2014003 = 3021005) B3021005
theorem B4531517 : Blo 2013435 4531517 := bbase (se 3 (by rfl) ⟨849659, by rfl⟩ : syracuseStep 4531517 = 1699319) (by norm_num)
theorem B3021011 : Blo 2013435 3021011 := bstep (se 1 (by rfl) ⟨2265758, by rfl⟩ : syracuseStep 3021011 = 4531517) B4531517
theorem B2014007 : Blo 2013435 2014007 := bstep (se 1 (by rfl) ⟨1510505, by rfl⟩ : syracuseStep 2014007 = 3021011) B3021011
theorem B3398645 : Blo 2013435 3398645 := bbase (se 5 (by rfl) ⟨159311, by rfl⟩ : syracuseStep 3398645 = 318623) (by norm_num)
theorem B2265763 : Blo 2013435 2265763 := bstep (se 1 (by rfl) ⟨1699322, by rfl⟩ : syracuseStep 2265763 = 3398645) B3398645
theorem B3021017 : Blo 2013435 3021017 := bstep (se 2 (by rfl) ⟨1132881, by rfl⟩ : syracuseStep 3021017 = 2265763) B2265763
theorem B2014011 : Blo 2013435 2014011 := bstep (se 1 (by rfl) ⟨1510508, by rfl⟩ : syracuseStep 2014011 = 3021017) B3021017
theorem B4082989 : Blo 2013435 4082989 := bbase (se 3 (by rfl) ⟨765560, by rfl⟩ : syracuseStep 4082989 = 1531121) (by norm_num)
theorem B5443985 : Blo 2013435 5443985 := bstep (se 2 (by rfl) ⟨2041494, by rfl⟩ : syracuseStep 5443985 = 4082989) B4082989
theorem B3629323 : Blo 2013435 3629323 := bstep (se 1 (by rfl) ⟨2721992, by rfl⟩ : syracuseStep 3629323 = 5443985) B5443985
theorem B4839097 : Blo 2013435 4839097 := bstep (se 2 (by rfl) ⟨1814661, by rfl⟩ : syracuseStep 4839097 = 3629323) B3629323
theorem B6452129 : Blo 2013435 6452129 := bstep (se 2 (by rfl) ⟨2419548, by rfl⟩ : syracuseStep 6452129 = 4839097) B4839097
theorem B4301419 : Blo 2013435 4301419 := bstep (se 1 (by rfl) ⟨3226064, by rfl⟩ : syracuseStep 4301419 = 6452129) B6452129
theorem B5735225 : Blo 2013435 5735225 := bstep (se 2 (by rfl) ⟨2150709, by rfl⟩ : syracuseStep 5735225 = 4301419) B4301419
theorem B15293933 : Blo 2013435 15293933 := bstep (se 3 (by rfl) ⟨2867612, by rfl⟩ : syracuseStep 15293933 = 5735225) B5735225
theorem B10195955 : Blo 2013435 10195955 := bstep (se 1 (by rfl) ⟨7646966, by rfl⟩ : syracuseStep 10195955 = 15293933) B15293933
theorem B6797303 : Blo 2013435 6797303 := bstep (se 1 (by rfl) ⟨5097977, by rfl⟩ : syracuseStep 6797303 = 10195955) B10195955
theorem B4531535 : Blo 2013435 4531535 := bstep (se 1 (by rfl) ⟨3398651, by rfl⟩ : syracuseStep 4531535 = 6797303) B6797303
theorem B3021023 : Blo 2013435 3021023 := bstep (se 1 (by rfl) ⟨2265767, by rfl⟩ : syracuseStep 3021023 = 4531535) B4531535
theorem B2014015 : Blo 2013435 2014015 := bstep (se 1 (by rfl) ⟨1510511, by rfl⟩ : syracuseStep 2014015 = 3021023) B3021023
theorem B3021029 : Blo 2013435 3021029 := bbase (se 4 (by rfl) ⟨283221, by rfl⟩ : syracuseStep 3021029 = 566443) (by norm_num)
theorem B2014019 : Blo 2013435 2014019 := bstep (se 1 (by rfl) ⟨1510514, by rfl⟩ : syracuseStep 2014019 = 3021029) B3021029
theorem B4301437 : Blo 2013435 4301437 := bbase (se 3 (by rfl) ⟨806519, by rfl⟩ : syracuseStep 4301437 = 1613039) (by norm_num)
theorem B5735249 : Blo 2013435 5735249 := bstep (se 2 (by rfl) ⟨2150718, by rfl⟩ : syracuseStep 5735249 = 4301437) B4301437
theorem B3823499 : Blo 2013435 3823499 := bstep (se 1 (by rfl) ⟨2867624, by rfl⟩ : syracuseStep 3823499 = 5735249) B5735249
theorem B2548999 : Blo 2013435 2548999 := bstep (se 1 (by rfl) ⟨1911749, by rfl⟩ : syracuseStep 2548999 = 3823499) B3823499
theorem B3398665 : Blo 2013435 3398665 := bstep (se 2 (by rfl) ⟨1274499, by rfl⟩ : syracuseStep 3398665 = 2548999) B2548999
theorem B4531553 : Blo 2013435 4531553 := bstep (se 2 (by rfl) ⟨1699332, by rfl⟩ : syracuseStep 4531553 = 3398665) B3398665
theorem B3021035 : Blo 2013435 3021035 := bstep (se 1 (by rfl) ⟨2265776, by rfl⟩ : syracuseStep 3021035 = 4531553) B4531553
theorem B2014023 : Blo 2013435 2014023 := bstep (se 1 (by rfl) ⟨1510517, by rfl⟩ : syracuseStep 2014023 = 3021035) B3021035
theorem B2265781 : Blo 2013435 2265781 := bbase (se 5 (by rfl) ⟨106208, by rfl⟩ : syracuseStep 2265781 = 212417) (by norm_num)
theorem B3021041 : Blo 2013435 3021041 := bstep (se 2 (by rfl) ⟨1132890, by rfl⟩ : syracuseStep 3021041 = 2265781) B2265781
theorem B2014027 : Blo 2013435 2014027 := bstep (se 1 (by rfl) ⟨1510520, by rfl⟩ : syracuseStep 2014027 = 3021041) B3021041
theorem B2549009 : Blo 2013435 2549009 := bbase (se 2 (by rfl) ⟨955878, by rfl⟩ : syracuseStep 2549009 = 1911757) (by norm_num)
theorem B6797357 : Blo 2013435 6797357 := bstep (se 3 (by rfl) ⟨1274504, by rfl⟩ : syracuseStep 6797357 = 2549009) B2549009
theorem B4531571 : Blo 2013435 4531571 := bstep (se 1 (by rfl) ⟨3398678, by rfl⟩ : syracuseStep 4531571 = 6797357) B6797357
theorem B3021047 : Blo 2013435 3021047 := bstep (se 1 (by rfl) ⟨2265785, by rfl⟩ : syracuseStep 3021047 = 4531571) B4531571
theorem B2014031 : Blo 2013435 2014031 := bstep (se 1 (by rfl) ⟨1510523, by rfl⟩ : syracuseStep 2014031 = 3021047) B3021047
theorem B3021053 : Blo 2013435 3021053 := bbase (se 3 (by rfl) ⟨566447, by rfl⟩ : syracuseStep 3021053 = 1132895) (by norm_num)
theorem B2014035 : Blo 2013435 2014035 := bstep (se 1 (by rfl) ⟨1510526, by rfl⟩ : syracuseStep 2014035 = 3021053) B3021053
theorem B4531589 : Blo 2013435 4531589 := bbase (se 4 (by rfl) ⟨424836, by rfl⟩ : syracuseStep 4531589 = 849673) (by norm_num)
theorem B3021059 : Blo 2013435 3021059 := bstep (se 1 (by rfl) ⟨2265794, by rfl⟩ : syracuseStep 3021059 = 4531589) B4531589
theorem B2014039 : Blo 2013435 2014039 := bstep (se 1 (by rfl) ⟨1510529, by rfl⟩ : syracuseStep 2014039 = 3021059) B3021059
theorem B2867653 : Blo 2013435 2867653 := bbase (se 4 (by rfl) ⟨268842, by rfl⟩ : syracuseStep 2867653 = 537685) (by norm_num)
theorem B3823537 : Blo 2013435 3823537 := bstep (se 2 (by rfl) ⟨1433826, by rfl⟩ : syracuseStep 3823537 = 2867653) B2867653
theorem B5098049 : Blo 2013435 5098049 := bstep (se 2 (by rfl) ⟨1911768, by rfl⟩ : syracuseStep 5098049 = 3823537) B3823537
theorem B3398699 : Blo 2013435 3398699 := bstep (se 1 (by rfl) ⟨2549024, by rfl⟩ : syracuseStep 3398699 = 5098049) B5098049
theorem B2265799 : Blo 2013435 2265799 := bstep (se 1 (by rfl) ⟨1699349, by rfl⟩ : syracuseStep 2265799 = 3398699) B3398699
theorem B3021065 : Blo 2013435 3021065 := bstep (se 2 (by rfl) ⟨1132899, by rfl⟩ : syracuseStep 3021065 = 2265799) B2265799
theorem B2014043 : Blo 2013435 2014043 := bstep (se 1 (by rfl) ⟨1510532, by rfl⟩ : syracuseStep 2014043 = 3021065) B3021065
theorem B10196117 : Blo 2013435 10196117 := bbase (se 6 (by rfl) ⟨238971, by rfl⟩ : syracuseStep 10196117 = 477943) (by norm_num)
theorem B6797411 : Blo 2013435 6797411 := bstep (se 1 (by rfl) ⟨5098058, by rfl⟩ : syracuseStep 6797411 = 10196117) B10196117
theorem B4531607 : Blo 2013435 4531607 := bstep (se 1 (by rfl) ⟨3398705, by rfl⟩ : syracuseStep 4531607 = 6797411) B6797411
theorem B3021071 : Blo 2013435 3021071 := bstep (se 1 (by rfl) ⟨2265803, by rfl⟩ : syracuseStep 3021071 = 4531607) B4531607
theorem B2014047 : Blo 2013435 2014047 := bstep (se 1 (by rfl) ⟨1510535, by rfl⟩ : syracuseStep 2014047 = 3021071) B3021071
theorem B3021077 : Blo 2013435 3021077 := bbase (se 6 (by rfl) ⟨70806, by rfl⟩ : syracuseStep 3021077 = 141613) (by norm_num)
theorem B2014051 : Blo 2013435 2014051 := bstep (se 1 (by rfl) ⟨1510538, by rfl⟩ : syracuseStep 2014051 = 3021077) B3021077
theorem B8720389 : Blo 2013435 8720389 := bbase (se 4 (by rfl) ⟨817536, by rfl⟩ : syracuseStep 8720389 = 1635073) (by norm_num)
theorem B11627185 : Blo 2013435 11627185 := bstep (se 2 (by rfl) ⟨4360194, by rfl⟩ : syracuseStep 11627185 = 8720389) B8720389
theorem B15502913 : Blo 2013435 15502913 := bstep (se 2 (by rfl) ⟨5813592, by rfl⟩ : syracuseStep 15502913 = 11627185) B11627185
theorem B10335275 : Blo 2013435 10335275 := bstep (se 1 (by rfl) ⟨7751456, by rfl⟩ : syracuseStep 10335275 = 15502913) B15502913
theorem B6890183 : Blo 2013435 6890183 := bstep (se 1 (by rfl) ⟨5167637, by rfl⟩ : syracuseStep 6890183 = 10335275) B10335275
theorem B4593455 : Blo 2013435 4593455 := bstep (se 1 (by rfl) ⟨3445091, by rfl⟩ : syracuseStep 4593455 = 6890183) B6890183
theorem B3062303 : Blo 2013435 3062303 := bstep (se 1 (by rfl) ⟨2296727, by rfl⟩ : syracuseStep 3062303 = 4593455) B4593455
theorem B2041535 : Blo 2013435 2041535 := bstep (se 1 (by rfl) ⟨1531151, by rfl⟩ : syracuseStep 2041535 = 3062303) B3062303
theorem B5444093 : Blo 2013435 5444093 := bstep (se 3 (by rfl) ⟨1020767, by rfl⟩ : syracuseStep 5444093 = 2041535) B2041535
theorem B3629395 : Blo 2013435 3629395 := bstep (se 1 (by rfl) ⟨2722046, by rfl⟩ : syracuseStep 3629395 = 5444093) B5444093
theorem B4839193 : Blo 2013435 4839193 := bstep (se 2 (by rfl) ⟨1814697, by rfl⟩ : syracuseStep 4839193 = 3629395) B3629395
theorem B25809029 : Blo 2013435 25809029 := bstep (se 4 (by rfl) ⟨2419596, by rfl⟩ : syracuseStep 25809029 = 4839193) B4839193
theorem B17206019 : Blo 2013435 17206019 := bstep (se 1 (by rfl) ⟨12904514, by rfl⟩ : syracuseStep 17206019 = 25809029) B25809029
theorem B11470679 : Blo 2013435 11470679 := bstep (se 1 (by rfl) ⟨8603009, by rfl⟩ : syracuseStep 11470679 = 17206019) B17206019
theorem B7647119 : Blo 2013435 7647119 := bstep (se 1 (by rfl) ⟨5735339, by rfl⟩ : syracuseStep 7647119 = 11470679) B11470679
theorem B5098079 : Blo 2013435 5098079 := bstep (se 1 (by rfl) ⟨3823559, by rfl⟩ : syracuseStep 5098079 = 7647119) B7647119
theorem B3398719 : Blo 2013435 3398719 := bstep (se 1 (by rfl) ⟨2549039, by rfl⟩ : syracuseStep 3398719 = 5098079) B5098079
theorem B4531625 : Blo 2013435 4531625 := bstep (se 2 (by rfl) ⟨1699359, by rfl⟩ : syracuseStep 4531625 = 3398719) B3398719
theorem B3021083 : Blo 2013435 3021083 := bstep (se 1 (by rfl) ⟨2265812, by rfl⟩ : syracuseStep 3021083 = 4531625) B4531625
theorem B2014055 : Blo 2013435 2014055 := bstep (se 1 (by rfl) ⟨1510541, by rfl⟩ : syracuseStep 2014055 = 3021083) B3021083
theorem B2265817 : Blo 2013435 2265817 := bbase (se 2 (by rfl) ⟨849681, by rfl⟩ : syracuseStep 2265817 = 1699363) (by norm_num)
theorem B3021089 : Blo 2013435 3021089 := bstep (se 2 (by rfl) ⟨1132908, by rfl⟩ : syracuseStep 3021089 = 2265817) B2265817
theorem B2014059 : Blo 2013435 2014059 := bstep (se 1 (by rfl) ⟨1510544, by rfl⟩ : syracuseStep 2014059 = 3021089) B3021089
theorem B2150761 : Blo 2013435 2150761 := bbase (se 2 (by rfl) ⟨806535, by rfl⟩ : syracuseStep 2150761 = 1613071) (by norm_num)
theorem B2867681 : Blo 2013435 2867681 := bstep (se 2 (by rfl) ⟨1075380, by rfl⟩ : syracuseStep 2867681 = 2150761) B2150761
theorem B7647149 : Blo 2013435 7647149 := bstep (se 3 (by rfl) ⟨1433840, by rfl⟩ : syracuseStep 7647149 = 2867681) B2867681
theorem B5098099 : Blo 2013435 5098099 := bstep (se 1 (by rfl) ⟨3823574, by rfl⟩ : syracuseStep 5098099 = 7647149) B7647149
theorem B6797465 : Blo 2013435 6797465 := bstep (se 2 (by rfl) ⟨2549049, by rfl⟩ : syracuseStep 6797465 = 5098099) B5098099
theorem B4531643 : Blo 2013435 4531643 := bstep (se 1 (by rfl) ⟨3398732, by rfl⟩ : syracuseStep 4531643 = 6797465) B6797465
theorem B3021095 : Blo 2013435 3021095 := bstep (se 1 (by rfl) ⟨2265821, by rfl⟩ : syracuseStep 3021095 = 4531643) B4531643
theorem B2014063 : Blo 2013435 2014063 := bstep (se 1 (by rfl) ⟨1510547, by rfl⟩ : syracuseStep 2014063 = 3021095) B3021095
theorem B3021101 : Blo 2013435 3021101 := bbase (se 3 (by rfl) ⟨566456, by rfl⟩ : syracuseStep 3021101 = 1132913) (by norm_num)
theorem B2014067 : Blo 2013435 2014067 := bstep (se 1 (by rfl) ⟨1510550, by rfl⟩ : syracuseStep 2014067 = 3021101) B3021101
theorem B4531661 : Blo 2013435 4531661 := bbase (se 3 (by rfl) ⟨849686, by rfl⟩ : syracuseStep 4531661 = 1699373) (by norm_num)
theorem B3021107 : Blo 2013435 3021107 := bstep (se 1 (by rfl) ⟨2265830, by rfl⟩ : syracuseStep 3021107 = 4531661) B4531661
theorem B2014071 : Blo 2013435 2014071 := bstep (se 1 (by rfl) ⟨1510553, by rfl⟩ : syracuseStep 2014071 = 3021107) B3021107
theorem B2549065 : Blo 2013435 2549065 := bbase (se 2 (by rfl) ⟨955899, by rfl⟩ : syracuseStep 2549065 = 1911799) (by norm_num)
theorem B3398753 : Blo 2013435 3398753 := bstep (se 2 (by rfl) ⟨1274532, by rfl⟩ : syracuseStep 3398753 = 2549065) B2549065
theorem B2265835 : Blo 2013435 2265835 := bstep (se 1 (by rfl) ⟨1699376, by rfl⟩ : syracuseStep 2265835 = 3398753) B3398753
theorem B3021113 : Blo 2013435 3021113 := bstep (se 2 (by rfl) ⟨1132917, by rfl⟩ : syracuseStep 3021113 = 2265835) B2265835
theorem B2014075 : Blo 2013435 2014075 := bstep (se 1 (by rfl) ⟨1510556, by rfl⟩ : syracuseStep 2014075 = 3021113) B3021113
theorem B11627317 : Blo 2013435 11627317 := bbase (se 5 (by rfl) ⟨545030, by rfl⟩ : syracuseStep 11627317 = 1090061) (by norm_num)
theorem B15503089 : Blo 2013435 15503089 := bstep (se 2 (by rfl) ⟨5813658, by rfl⟩ : syracuseStep 15503089 = 11627317) B11627317
theorem B20670785 : Blo 2013435 20670785 := bstep (se 2 (by rfl) ⟨7751544, by rfl⟩ : syracuseStep 20670785 = 15503089) B15503089
theorem B13780523 : Blo 2013435 13780523 := bstep (se 1 (by rfl) ⟨10335392, by rfl⟩ : syracuseStep 13780523 = 20670785) B20670785
theorem B9187015 : Blo 2013435 9187015 := bstep (se 1 (by rfl) ⟨6890261, by rfl⟩ : syracuseStep 9187015 = 13780523) B13780523
theorem B12249353 : Blo 2013435 12249353 := bstep (se 2 (by rfl) ⟨4593507, by rfl⟩ : syracuseStep 12249353 = 9187015) B9187015
theorem B32664941 : Blo 2013435 32664941 := bstep (se 3 (by rfl) ⟨6124676, by rfl⟩ : syracuseStep 32664941 = 12249353) B12249353
theorem B21776627 : Blo 2013435 21776627 := bstep (se 1 (by rfl) ⟨16332470, by rfl⟩ : syracuseStep 21776627 = 32664941) B32664941
theorem B14517751 : Blo 2013435 14517751 := bstep (se 1 (by rfl) ⟨10888313, by rfl⟩ : syracuseStep 14517751 = 21776627) B21776627
theorem B19357001 : Blo 2013435 19357001 := bstep (se 2 (by rfl) ⟨7258875, by rfl⟩ : syracuseStep 19357001 = 14517751) B14517751
theorem B12904667 : Blo 2013435 12904667 := bstep (se 1 (by rfl) ⟨9678500, by rfl⟩ : syracuseStep 12904667 = 19357001) B19357001
theorem B8603111 : Blo 2013435 8603111 := bstep (se 1 (by rfl) ⟨6452333, by rfl⟩ : syracuseStep 8603111 = 12904667) B12904667
theorem B22941629 : Blo 2013435 22941629 := bstep (se 3 (by rfl) ⟨4301555, by rfl⟩ : syracuseStep 22941629 = 8603111) B8603111
theorem B15294419 : Blo 2013435 15294419 := bstep (se 1 (by rfl) ⟨11470814, by rfl⟩ : syracuseStep 15294419 = 22941629) B22941629
theorem B10196279 : Blo 2013435 10196279 := bstep (se 1 (by rfl) ⟨7647209, by rfl⟩ : syracuseStep 10196279 = 15294419) B15294419
theorem B6797519 : Blo 2013435 6797519 := bstep (se 1 (by rfl) ⟨5098139, by rfl⟩ : syracuseStep 6797519 = 10196279) B10196279
theorem B4531679 : Blo 2013435 4531679 := bstep (se 1 (by rfl) ⟨3398759, by rfl⟩ : syracuseStep 4531679 = 6797519) B6797519
theorem B3021119 : Blo 2013435 3021119 := bstep (se 1 (by rfl) ⟨2265839, by rfl⟩ : syracuseStep 3021119 = 4531679) B4531679
theorem B2014079 : Blo 2013435 2014079 := bstep (se 1 (by rfl) ⟨1510559, by rfl⟩ : syracuseStep 2014079 = 3021119) B3021119
theorem B3021125 : Blo 2013435 3021125 := bbase (se 4 (by rfl) ⟨283230, by rfl⟩ : syracuseStep 3021125 = 566461) (by norm_num)
theorem B2014083 : Blo 2013435 2014083 := bstep (se 1 (by rfl) ⟨1510562, by rfl⟩ : syracuseStep 2014083 = 3021125) B3021125
theorem B3398773 : Blo 2013435 3398773 := bbase (se 5 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 3398773 = 318635) (by norm_num)
theorem B4531697 : Blo 2013435 4531697 := bstep (se 2 (by rfl) ⟨1699386, by rfl⟩ : syracuseStep 4531697 = 3398773) B3398773
theorem B3021131 : Blo 2013435 3021131 := bstep (se 1 (by rfl) ⟨2265848, by rfl⟩ : syracuseStep 3021131 = 4531697) B4531697
theorem B2014087 : Blo 2013435 2014087 := bstep (se 1 (by rfl) ⟨1510565, by rfl⟩ : syracuseStep 2014087 = 3021131) B3021131
theorem B2265853 : Blo 2013435 2265853 := bbase (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) (by norm_num)
theorem B3021137 : Blo 2013435 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B2014091 : Blo 2013435 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B6797573 : Blo 2013435 6797573 := bbase (se 4 (by rfl) ⟨637272, by rfl⟩ : syracuseStep 6797573 = 1274545) (by norm_num)
theorem B4531715 : Blo 2013435 4531715 := bstep (se 1 (by rfl) ⟨3398786, by rfl⟩ : syracuseStep 4531715 = 6797573) B6797573
theorem B3021143 : Blo 2013435 3021143 := bstep (se 1 (by rfl) ⟨2265857, by rfl⟩ : syracuseStep 3021143 = 4531715) B4531715
theorem B2014095 : Blo 2013435 2014095 := bstep (se 1 (by rfl) ⟨1510571, by rfl⟩ : syracuseStep 2014095 = 3021143) B3021143
theorem B3021149 : Blo 2013435 3021149 := bbase (se 3 (by rfl) ⟨566465, by rfl⟩ : syracuseStep 3021149 = 1132931) (by norm_num)
theorem B2014099 : Blo 2013435 2014099 := bstep (se 1 (by rfl) ⟨1510574, by rfl⟩ : syracuseStep 2014099 = 3021149) B3021149
theorem B4531733 : Blo 2013435 4531733 := bbase (se 6 (by rfl) ⟨106212, by rfl⟩ : syracuseStep 4531733 = 212425) (by norm_num)
theorem B3021155 : Blo 2013435 3021155 := bstep (se 1 (by rfl) ⟨2265866, by rfl⟩ : syracuseStep 3021155 = 4531733) B4531733
theorem B2014103 : Blo 2013435 2014103 := bstep (se 1 (by rfl) ⟨1510577, by rfl⟩ : syracuseStep 2014103 = 3021155) B3021155
theorem B7647317 : Blo 2013435 7647317 := bbase (se 8 (by rfl) ⟨44808, by rfl⟩ : syracuseStep 7647317 = 89617) (by norm_num)
theorem B5098211 : Blo 2013435 5098211 := bstep (se 1 (by rfl) ⟨3823658, by rfl⟩ : syracuseStep 5098211 = 7647317) B7647317
theorem B3398807 : Blo 2013435 3398807 := bstep (se 1 (by rfl) ⟨2549105, by rfl⟩ : syracuseStep 3398807 = 5098211) B5098211
theorem B2265871 : Blo 2013435 2265871 := bstep (se 1 (by rfl) ⟨1699403, by rfl⟩ : syracuseStep 2265871 = 3398807) B3398807
theorem B3021161 : Blo 2013435 3021161 := bstep (se 2 (by rfl) ⟨1132935, by rfl⟩ : syracuseStep 3021161 = 2265871) B2265871
theorem B2014107 : Blo 2013435 2014107 := bstep (se 1 (by rfl) ⟨1510580, by rfl⟩ : syracuseStep 2014107 = 3021161) B3021161
theorem B11470997 : Blo 2013435 11470997 := bbase (se 6 (by rfl) ⟨268851, by rfl⟩ : syracuseStep 11470997 = 537703) (by norm_num)
theorem B7647331 : Blo 2013435 7647331 := bstep (se 1 (by rfl) ⟨5735498, by rfl⟩ : syracuseStep 7647331 = 11470997) B11470997
theorem B10196441 : Blo 2013435 10196441 := bstep (se 2 (by rfl) ⟨3823665, by rfl⟩ : syracuseStep 10196441 = 7647331) B7647331
theorem B6797627 : Blo 2013435 6797627 := bstep (se 1 (by rfl) ⟨5098220, by rfl⟩ : syracuseStep 6797627 = 10196441) B10196441
theorem B4531751 : Blo 2013435 4531751 := bstep (se 1 (by rfl) ⟨3398813, by rfl⟩ : syracuseStep 4531751 = 6797627) B6797627
theorem B3021167 : Blo 2013435 3021167 := bstep (se 1 (by rfl) ⟨2265875, by rfl⟩ : syracuseStep 3021167 = 4531751) B4531751
theorem B2014111 : Blo 2013435 2014111 := bstep (se 1 (by rfl) ⟨1510583, by rfl⟩ : syracuseStep 2014111 = 3021167) B3021167
theorem B3021173 : Blo 2013435 3021173 := bbase (se 5 (by rfl) ⟨141617, by rfl⟩ : syracuseStep 3021173 = 283235) (by norm_num)
theorem B2014115 : Blo 2013435 2014115 := bstep (se 1 (by rfl) ⟨1510586, by rfl⟩ : syracuseStep 2014115 = 3021173) B3021173
theorem B2150821 : Blo 2013435 2150821 := bbase (se 4 (by rfl) ⟨201639, by rfl⟩ : syracuseStep 2150821 = 403279) (by norm_num)
theorem B2867761 : Blo 2013435 2867761 := bstep (se 2 (by rfl) ⟨1075410, by rfl⟩ : syracuseStep 2867761 = 2150821) B2150821
theorem B3823681 : Blo 2013435 3823681 := bstep (se 2 (by rfl) ⟨1433880, by rfl⟩ : syracuseStep 3823681 = 2867761) B2867761
theorem B5098241 : Blo 2013435 5098241 := bstep (se 2 (by rfl) ⟨1911840, by rfl⟩ : syracuseStep 5098241 = 3823681) B3823681
theorem B3398827 : Blo 2013435 3398827 := bstep (se 1 (by rfl) ⟨2549120, by rfl⟩ : syracuseStep 3398827 = 5098241) B5098241
theorem B4531769 : Blo 2013435 4531769 := bstep (se 2 (by rfl) ⟨1699413, by rfl⟩ : syracuseStep 4531769 = 3398827) B3398827
theorem B3021179 : Blo 2013435 3021179 := bstep (se 1 (by rfl) ⟨2265884, by rfl⟩ : syracuseStep 3021179 = 4531769) B4531769
theorem B2014119 : Blo 2013435 2014119 := bstep (se 1 (by rfl) ⟨1510589, by rfl⟩ : syracuseStep 2014119 = 3021179) B3021179
theorem B2265889 : Blo 2013435 2265889 := bbase (se 2 (by rfl) ⟨849708, by rfl⟩ : syracuseStep 2265889 = 1699417) (by norm_num)
theorem B3021185 : Blo 2013435 3021185 := bstep (se 2 (by rfl) ⟨1132944, by rfl⟩ : syracuseStep 3021185 = 2265889) B2265889
theorem B2014123 : Blo 2013435 2014123 := bstep (se 1 (by rfl) ⟨1510592, by rfl⟩ : syracuseStep 2014123 = 3021185) B3021185
theorem B5098261 : Blo 2013435 5098261 := bbase (se 6 (by rfl) ⟨119490, by rfl⟩ : syracuseStep 5098261 = 238981) (by norm_num)
theorem B6797681 : Blo 2013435 6797681 := bstep (se 2 (by rfl) ⟨2549130, by rfl⟩ : syracuseStep 6797681 = 5098261) B5098261
theorem B4531787 : Blo 2013435 4531787 := bstep (se 1 (by rfl) ⟨3398840, by rfl⟩ : syracuseStep 4531787 = 6797681) B6797681
theorem B3021191 : Blo 2013435 3021191 := bstep (se 1 (by rfl) ⟨2265893, by rfl⟩ : syracuseStep 3021191 = 4531787) B4531787
theorem B2014127 : Blo 2013435 2014127 := bstep (se 1 (by rfl) ⟨1510595, by rfl⟩ : syracuseStep 2014127 = 3021191) B3021191
theorem B3021197 : Blo 2013435 3021197 := bbase (se 3 (by rfl) ⟨566474, by rfl⟩ : syracuseStep 3021197 = 1132949) (by norm_num)
theorem B2014131 : Blo 2013435 2014131 := bstep (se 1 (by rfl) ⟨1510598, by rfl⟩ : syracuseStep 2014131 = 3021197) B3021197
theorem B4531805 : Blo 2013435 4531805 := bbase (se 3 (by rfl) ⟨849713, by rfl⟩ : syracuseStep 4531805 = 1699427) (by norm_num)
theorem B3021203 : Blo 2013435 3021203 := bstep (se 1 (by rfl) ⟨2265902, by rfl⟩ : syracuseStep 3021203 = 4531805) B4531805
theorem B2014135 : Blo 2013435 2014135 := bstep (se 1 (by rfl) ⟨1510601, by rfl⟩ : syracuseStep 2014135 = 3021203) B3021203
theorem B3398861 : Blo 2013435 3398861 := bbase (se 3 (by rfl) ⟨637286, by rfl⟩ : syracuseStep 3398861 = 1274573) (by norm_num)
theorem B2265907 : Blo 2013435 2265907 := bstep (se 1 (by rfl) ⟨1699430, by rfl⟩ : syracuseStep 2265907 = 3398861) B3398861
theorem B3021209 : Blo 2013435 3021209 := bstep (se 2 (by rfl) ⟨1132953, by rfl⟩ : syracuseStep 3021209 = 2265907) B2265907
theorem B2014139 : Blo 2013435 2014139 := bstep (se 1 (by rfl) ⟨1510604, by rfl⟩ : syracuseStep 2014139 = 3021209) B3021209
theorem B12905077 : Blo 2013435 12905077 := bbase (se 5 (by rfl) ⟨604925, by rfl⟩ : syracuseStep 12905077 = 1209851) (by norm_num)
theorem B17206769 : Blo 2013435 17206769 := bstep (se 2 (by rfl) ⟨6452538, by rfl⟩ : syracuseStep 17206769 = 12905077) B12905077
theorem B11471179 : Blo 2013435 11471179 := bstep (se 1 (by rfl) ⟨8603384, by rfl⟩ : syracuseStep 11471179 = 17206769) B17206769
theorem B15294905 : Blo 2013435 15294905 := bstep (se 2 (by rfl) ⟨5735589, by rfl⟩ : syracuseStep 15294905 = 11471179) B11471179
theorem B10196603 : Blo 2013435 10196603 := bstep (se 1 (by rfl) ⟨7647452, by rfl⟩ : syracuseStep 10196603 = 15294905) B15294905
theorem B6797735 : Blo 2013435 6797735 := bstep (se 1 (by rfl) ⟨5098301, by rfl⟩ : syracuseStep 6797735 = 10196603) B10196603
theorem B4531823 : Blo 2013435 4531823 := bstep (se 1 (by rfl) ⟨3398867, by rfl⟩ : syracuseStep 4531823 = 6797735) B6797735
theorem B3021215 : Blo 2013435 3021215 := bstep (se 1 (by rfl) ⟨2265911, by rfl⟩ : syracuseStep 3021215 = 4531823) B4531823
theorem B2014143 : Blo 2013435 2014143 := bstep (se 1 (by rfl) ⟨1510607, by rfl⟩ : syracuseStep 2014143 = 3021215) B3021215
theorem B3021221 : Blo 2013435 3021221 := bbase (se 4 (by rfl) ⟨283239, by rfl⟩ : syracuseStep 3021221 = 566479) (by norm_num)
theorem B2014147 : Blo 2013435 2014147 := bstep (se 1 (by rfl) ⟨1510610, by rfl⟩ : syracuseStep 2014147 = 3021221) B3021221
theorem B2549161 : Blo 2013435 2549161 := bbase (se 2 (by rfl) ⟨955935, by rfl⟩ : syracuseStep 2549161 = 1911871) (by norm_num)
theorem B3398881 : Blo 2013435 3398881 := bstep (se 2 (by rfl) ⟨1274580, by rfl⟩ : syracuseStep 3398881 = 2549161) B2549161
theorem B4531841 : Blo 2013435 4531841 := bstep (se 2 (by rfl) ⟨1699440, by rfl⟩ : syracuseStep 4531841 = 3398881) B3398881
theorem B3021227 : Blo 2013435 3021227 := bstep (se 1 (by rfl) ⟨2265920, by rfl⟩ : syracuseStep 3021227 = 4531841) B4531841
theorem B2014151 : Blo 2013435 2014151 := bstep (se 1 (by rfl) ⟨1510613, by rfl⟩ : syracuseStep 2014151 = 3021227) B3021227
theorem B2265925 : Blo 2013435 2265925 := bbase (se 4 (by rfl) ⟨212430, by rfl⟩ : syracuseStep 2265925 = 424861) (by norm_num)
theorem B3021233 : Blo 2013435 3021233 := bstep (se 2 (by rfl) ⟨1132962, by rfl⟩ : syracuseStep 3021233 = 2265925) B2265925
theorem B2014155 : Blo 2013435 2014155 := bstep (se 1 (by rfl) ⟨1510616, by rfl⟩ : syracuseStep 2014155 = 3021233) B3021233
theorem B3823757 : Blo 2013435 3823757 := bbase (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) (by norm_num)
theorem B2549171 : Blo 2013435 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B6797789 : Blo 2013435 6797789 := bstep (se 3 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 6797789 = 2549171) B2549171
theorem B4531859 : Blo 2013435 4531859 := bstep (se 1 (by rfl) ⟨3398894, by rfl⟩ : syracuseStep 4531859 = 6797789) B6797789
theorem B3021239 : Blo 2013435 3021239 := bstep (se 1 (by rfl) ⟨2265929, by rfl⟩ : syracuseStep 3021239 = 4531859) B4531859
theorem B2014159 : Blo 2013435 2014159 := bstep (se 1 (by rfl) ⟨1510619, by rfl⟩ : syracuseStep 2014159 = 3021239) B3021239
theorem B3021245 : Blo 2013435 3021245 := bbase (se 3 (by rfl) ⟨566483, by rfl⟩ : syracuseStep 3021245 = 1132967) (by norm_num)
theorem B2014163 : Blo 2013435 2014163 := bstep (se 1 (by rfl) ⟨1510622, by rfl⟩ : syracuseStep 2014163 = 3021245) B3021245
theorem B4531877 : Blo 2013435 4531877 := bbase (se 4 (by rfl) ⟨424863, by rfl⟩ : syracuseStep 4531877 = 849727) (by norm_num)
theorem B3021251 : Blo 2013435 3021251 := bstep (se 1 (by rfl) ⟨2265938, by rfl⟩ : syracuseStep 3021251 = 4531877) B4531877
theorem B2014167 : Blo 2013435 2014167 := bstep (se 1 (by rfl) ⟨1510625, by rfl⟩ : syracuseStep 2014167 = 3021251) B3021251
theorem B5098373 : Blo 2013435 5098373 := bbase (se 4 (by rfl) ⟨477972, by rfl⟩ : syracuseStep 5098373 = 955945) (by norm_num)
theorem B3398915 : Blo 2013435 3398915 := bstep (se 1 (by rfl) ⟨2549186, by rfl⟩ : syracuseStep 3398915 = 5098373) B5098373
theorem B2265943 : Blo 2013435 2265943 := bstep (se 1 (by rfl) ⟨1699457, by rfl⟩ : syracuseStep 2265943 = 3398915) B3398915
theorem B3021257 : Blo 2013435 3021257 := bstep (se 2 (by rfl) ⟨1132971, by rfl⟩ : syracuseStep 3021257 = 2265943) B2265943
theorem B2014171 : Blo 2013435 2014171 := bstep (se 1 (by rfl) ⟨1510628, by rfl⟩ : syracuseStep 2014171 = 3021257) B3021257
theorem B2419741 : Blo 2013435 2419741 := bbase (se 3 (by rfl) ⟨453701, by rfl⟩ : syracuseStep 2419741 = 907403) (by norm_num)
theorem B3226321 : Blo 2013435 3226321 := bstep (se 2 (by rfl) ⟨1209870, by rfl⟩ : syracuseStep 3226321 = 2419741) B2419741
theorem B4301761 : Blo 2013435 4301761 := bstep (se 2 (by rfl) ⟨1613160, by rfl⟩ : syracuseStep 4301761 = 3226321) B3226321
theorem B5735681 : Blo 2013435 5735681 := bstep (se 2 (by rfl) ⟨2150880, by rfl⟩ : syracuseStep 5735681 = 4301761) B4301761
theorem B3823787 : Blo 2013435 3823787 := bstep (se 1 (by rfl) ⟨2867840, by rfl⟩ : syracuseStep 3823787 = 5735681) B5735681
theorem B10196765 : Blo 2013435 10196765 := bstep (se 3 (by rfl) ⟨1911893, by rfl⟩ : syracuseStep 10196765 = 3823787) B3823787
theorem B6797843 : Blo 2013435 6797843 := bstep (se 1 (by rfl) ⟨5098382, by rfl⟩ : syracuseStep 6797843 = 10196765) B10196765
theorem B4531895 : Blo 2013435 4531895 := bstep (se 1 (by rfl) ⟨3398921, by rfl⟩ : syracuseStep 4531895 = 6797843) B6797843
theorem B3021263 : Blo 2013435 3021263 := bstep (se 1 (by rfl) ⟨2265947, by rfl⟩ : syracuseStep 3021263 = 4531895) B4531895
theorem B2014175 : Blo 2013435 2014175 := bstep (se 1 (by rfl) ⟨1510631, by rfl⟩ : syracuseStep 2014175 = 3021263) B3021263
theorem B3021269 : Blo 2013435 3021269 := bbase (se 7 (by rfl) ⟨35405, by rfl⟩ : syracuseStep 3021269 = 70811) (by norm_num)
theorem B2014179 : Blo 2013435 2014179 := bstep (se 1 (by rfl) ⟨1510634, by rfl⟩ : syracuseStep 2014179 = 3021269) B3021269
theorem B7647605 : Blo 2013435 7647605 := bbase (se 5 (by rfl) ⟨358481, by rfl⟩ : syracuseStep 7647605 = 716963) (by norm_num)
theorem B5098403 : Blo 2013435 5098403 := bstep (se 1 (by rfl) ⟨3823802, by rfl⟩ : syracuseStep 5098403 = 7647605) B7647605
theorem B3398935 : Blo 2013435 3398935 := bstep (se 1 (by rfl) ⟨2549201, by rfl⟩ : syracuseStep 3398935 = 5098403) B5098403
theorem B4531913 : Blo 2013435 4531913 := bstep (se 2 (by rfl) ⟨1699467, by rfl⟩ : syracuseStep 4531913 = 3398935) B3398935
theorem B3021275 : Blo 2013435 3021275 := bstep (se 1 (by rfl) ⟨2265956, by rfl⟩ : syracuseStep 3021275 = 4531913) B4531913
theorem B2014183 : Blo 2013435 2014183 := bstep (se 1 (by rfl) ⟨1510637, by rfl⟩ : syracuseStep 2014183 = 3021275) B3021275
theorem B2265961 : Blo 2013435 2265961 := bbase (se 2 (by rfl) ⟨849735, by rfl⟩ : syracuseStep 2265961 = 1699471) (by norm_num)
theorem B3021281 : Blo 2013435 3021281 := bstep (se 2 (by rfl) ⟨1132980, by rfl⟩ : syracuseStep 3021281 = 2265961) B2265961
theorem B2014187 : Blo 2013435 2014187 := bstep (se 1 (by rfl) ⟨1510640, by rfl⟩ : syracuseStep 2014187 = 3021281) B3021281
theorem B6452693 : Blo 2013435 6452693 := bbase (se 7 (by rfl) ⟨75617, by rfl⟩ : syracuseStep 6452693 = 151235) (by norm_num)
theorem B4301795 : Blo 2013435 4301795 := bstep (se 1 (by rfl) ⟨3226346, by rfl⟩ : syracuseStep 4301795 = 6452693) B6452693
theorem B11471453 : Blo 2013435 11471453 := bstep (se 3 (by rfl) ⟨2150897, by rfl⟩ : syracuseStep 11471453 = 4301795) B4301795
theorem B7647635 : Blo 2013435 7647635 := bstep (se 1 (by rfl) ⟨5735726, by rfl⟩ : syracuseStep 7647635 = 11471453) B11471453
theorem B5098423 : Blo 2013435 5098423 := bstep (se 1 (by rfl) ⟨3823817, by rfl⟩ : syracuseStep 5098423 = 7647635) B7647635
theorem B6797897 : Blo 2013435 6797897 := bstep (se 2 (by rfl) ⟨2549211, by rfl⟩ : syracuseStep 6797897 = 5098423) B5098423
theorem B4531931 : Blo 2013435 4531931 := bstep (se 1 (by rfl) ⟨3398948, by rfl⟩ : syracuseStep 4531931 = 6797897) B6797897
theorem B3021287 : Blo 2013435 3021287 := bstep (se 1 (by rfl) ⟨2265965, by rfl⟩ : syracuseStep 3021287 = 4531931) B4531931
theorem B2014191 : Blo 2013435 2014191 := bstep (se 1 (by rfl) ⟨1510643, by rfl⟩ : syracuseStep 2014191 = 3021287) B3021287
theorem B3021293 : Blo 2013435 3021293 := bbase (se 3 (by rfl) ⟨566492, by rfl⟩ : syracuseStep 3021293 = 1132985) (by norm_num)
theorem B2014195 : Blo 2013435 2014195 := bstep (se 1 (by rfl) ⟨1510646, by rfl⟩ : syracuseStep 2014195 = 3021293) B3021293
theorem B4531949 : Blo 2013435 4531949 := bbase (se 3 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 4531949 = 1699481) (by norm_num)
theorem B3021299 : Blo 2013435 3021299 := bstep (se 1 (by rfl) ⟨2265974, by rfl⟩ : syracuseStep 3021299 = 4531949) B4531949
theorem B2014199 : Blo 2013435 2014199 := bstep (se 1 (by rfl) ⟨1510649, by rfl⟩ : syracuseStep 2014199 = 3021299) B3021299
theorem B15504053 : Blo 2013435 15504053 := bbase (se 5 (by rfl) ⟨726752, by rfl⟩ : syracuseStep 15504053 = 1453505) (by norm_num)
theorem B41344141 : Blo 2013435 41344141 := bstep (se 3 (by rfl) ⟨7752026, by rfl⟩ : syracuseStep 41344141 = 15504053) B15504053
theorem B55125521 : Blo 2013435 55125521 := bstep (se 2 (by rfl) ⟨20672070, by rfl⟩ : syracuseStep 55125521 = 41344141) B41344141
theorem B36750347 : Blo 2013435 36750347 := bstep (se 1 (by rfl) ⟨27562760, by rfl⟩ : syracuseStep 36750347 = 55125521) B55125521
theorem B24500231 : Blo 2013435 24500231 := bstep (se 1 (by rfl) ⟨18375173, by rfl⟩ : syracuseStep 24500231 = 36750347) B36750347
theorem B16333487 : Blo 2013435 16333487 := bstep (se 1 (by rfl) ⟨12250115, by rfl⟩ : syracuseStep 16333487 = 24500231) B24500231
theorem B10888991 : Blo 2013435 10888991 := bstep (se 1 (by rfl) ⟨8166743, by rfl⟩ : syracuseStep 10888991 = 16333487) B16333487
theorem B7259327 : Blo 2013435 7259327 := bstep (se 1 (by rfl) ⟨5444495, by rfl⟩ : syracuseStep 7259327 = 10888991) B10888991
theorem B4839551 : Blo 2013435 4839551 := bstep (se 1 (by rfl) ⟨3629663, by rfl⟩ : syracuseStep 4839551 = 7259327) B7259327
theorem B3226367 : Blo 2013435 3226367 := bstep (se 1 (by rfl) ⟨2419775, by rfl⟩ : syracuseStep 3226367 = 4839551) B4839551
theorem B2150911 : Blo 2013435 2150911 := bstep (se 1 (by rfl) ⟨1613183, by rfl⟩ : syracuseStep 2150911 = 3226367) B3226367
theorem B2867881 : Blo 2013435 2867881 := bstep (se 2 (by rfl) ⟨1075455, by rfl⟩ : syracuseStep 2867881 = 2150911) B2150911
theorem B3823841 : Blo 2013435 3823841 := bstep (se 2 (by rfl) ⟨1433940, by rfl⟩ : syracuseStep 3823841 = 2867881) B2867881
theorem B2549227 : Blo 2013435 2549227 := bstep (se 1 (by rfl) ⟨1911920, by rfl⟩ : syracuseStep 2549227 = 3823841) B3823841
theorem B3398969 : Blo 2013435 3398969 := bstep (se 2 (by rfl) ⟨1274613, by rfl⟩ : syracuseStep 3398969 = 2549227) B2549227
theorem B2265979 : Blo 2013435 2265979 := bstep (se 1 (by rfl) ⟨1699484, by rfl⟩ : syracuseStep 2265979 = 3398969) B3398969
theorem B3021305 : Blo 2013435 3021305 := bstep (se 2 (by rfl) ⟨1132989, by rfl⟩ : syracuseStep 3021305 = 2265979) B2265979
theorem B2014203 : Blo 2013435 2014203 := bstep (se 1 (by rfl) ⟨1510652, by rfl⟩ : syracuseStep 2014203 = 3021305) B3021305
theorem B7752037 : Blo 2013435 7752037 := bbase (se 4 (by rfl) ⟨726753, by rfl⟩ : syracuseStep 7752037 = 1453507) (by norm_num)
theorem B10336049 : Blo 2013435 10336049 := bstep (se 2 (by rfl) ⟨3876018, by rfl⟩ : syracuseStep 10336049 = 7752037) B7752037
theorem B6890699 : Blo 2013435 6890699 := bstep (se 1 (by rfl) ⟨5168024, by rfl⟩ : syracuseStep 6890699 = 10336049) B10336049
theorem B4593799 : Blo 2013435 4593799 := bstep (se 1 (by rfl) ⟨3445349, by rfl⟩ : syracuseStep 4593799 = 6890699) B6890699
theorem B24500261 : Blo 2013435 24500261 := bstep (se 4 (by rfl) ⟨2296899, by rfl⟩ : syracuseStep 24500261 = 4593799) B4593799
theorem B16333507 : Blo 2013435 16333507 := bstep (se 1 (by rfl) ⟨12250130, by rfl⟩ : syracuseStep 16333507 = 24500261) B24500261
theorem B87112037 : Blo 2013435 87112037 := bstep (se 4 (by rfl) ⟨8166753, by rfl⟩ : syracuseStep 87112037 = 16333507) B16333507
theorem B58074691 : Blo 2013435 58074691 := bstep (se 1 (by rfl) ⟨43556018, by rfl⟩ : syracuseStep 58074691 = 87112037) B87112037
theorem B77432921 : Blo 2013435 77432921 := bstep (se 2 (by rfl) ⟨29037345, by rfl⟩ : syracuseStep 77432921 = 58074691) B58074691
theorem B51621947 : Blo 2013435 51621947 := bstep (se 1 (by rfl) ⟨38716460, by rfl⟩ : syracuseStep 51621947 = 77432921) B77432921
theorem B34414631 : Blo 2013435 34414631 := bstep (se 1 (by rfl) ⟨25810973, by rfl⟩ : syracuseStep 34414631 = 51621947) B51621947
theorem B22943087 : Blo 2013435 22943087 := bstep (se 1 (by rfl) ⟨17207315, by rfl⟩ : syracuseStep 22943087 = 34414631) B34414631
theorem B15295391 : Blo 2013435 15295391 := bstep (se 1 (by rfl) ⟨11471543, by rfl⟩ : syracuseStep 15295391 = 22943087) B22943087
theorem B10196927 : Blo 2013435 10196927 := bstep (se 1 (by rfl) ⟨7647695, by rfl⟩ : syracuseStep 10196927 = 15295391) B15295391
theorem B6797951 : Blo 2013435 6797951 := bstep (se 1 (by rfl) ⟨5098463, by rfl⟩ : syracuseStep 6797951 = 10196927) B10196927
theorem B4531967 : Blo 2013435 4531967 := bstep (se 1 (by rfl) ⟨3398975, by rfl⟩ : syracuseStep 4531967 = 6797951) B6797951
theorem B3021311 : Blo 2013435 3021311 := bstep (se 1 (by rfl) ⟨2265983, by rfl⟩ : syracuseStep 3021311 = 4531967) B4531967
theorem B2014207 : Blo 2013435 2014207 := bstep (se 1 (by rfl) ⟨1510655, by rfl⟩ : syracuseStep 2014207 = 3021311) B3021311
theorem B3021317 : Blo 2013435 3021317 := bbase (se 4 (by rfl) ⟨283248, by rfl⟩ : syracuseStep 3021317 = 566497) (by norm_num)
theorem B2014211 : Blo 2013435 2014211 := bstep (se 1 (by rfl) ⟨1510658, by rfl⟩ : syracuseStep 2014211 = 3021317) B3021317
theorem B3398989 : Blo 2013435 3398989 := bbase (se 3 (by rfl) ⟨637310, by rfl⟩ : syracuseStep 3398989 = 1274621) (by norm_num)
theorem B4531985 : Blo 2013435 4531985 := bstep (se 2 (by rfl) ⟨1699494, by rfl⟩ : syracuseStep 4531985 = 3398989) B3398989
theorem B3021323 : Blo 2013435 3021323 := bstep (se 1 (by rfl) ⟨2265992, by rfl⟩ : syracuseStep 3021323 = 4531985) B4531985
theorem B2014215 : Blo 2013435 2014215 := bstep (se 1 (by rfl) ⟨1510661, by rfl⟩ : syracuseStep 2014215 = 3021323) B3021323
theorem B2265997 : Blo 2013435 2265997 := bbase (se 3 (by rfl) ⟨424874, by rfl⟩ : syracuseStep 2265997 = 849749) (by norm_num)
theorem B3021329 : Blo 2013435 3021329 := bstep (se 2 (by rfl) ⟨1132998, by rfl⟩ : syracuseStep 3021329 = 2265997) B2265997
theorem B2014219 : Blo 2013435 2014219 := bstep (se 1 (by rfl) ⟨1510664, by rfl⟩ : syracuseStep 2014219 = 3021329) B3021329
theorem B6798005 : Blo 2013435 6798005 := bbase (se 5 (by rfl) ⟨318656, by rfl⟩ : syracuseStep 6798005 = 637313) (by norm_num)
theorem B4532003 : Blo 2013435 4532003 := bstep (se 1 (by rfl) ⟨3399002, by rfl⟩ : syracuseStep 4532003 = 6798005) B6798005
theorem B3021335 : Blo 2013435 3021335 := bstep (se 1 (by rfl) ⟨2266001, by rfl⟩ : syracuseStep 3021335 = 4532003) B4532003
theorem B2014223 : Blo 2013435 2014223 := bstep (se 1 (by rfl) ⟨1510667, by rfl⟩ : syracuseStep 2014223 = 3021335) B3021335
theorem B3021341 : Blo 2013435 3021341 := bbase (se 3 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 3021341 = 1133003) (by norm_num)
theorem B2014227 : Blo 2013435 2014227 := bstep (se 1 (by rfl) ⟨1510670, by rfl⟩ : syracuseStep 2014227 = 3021341) B3021341
theorem B4532021 : Blo 2013435 4532021 := bbase (se 5 (by rfl) ⟨212438, by rfl⟩ : syracuseStep 4532021 = 424877) (by norm_num)
theorem B3021347 : Blo 2013435 3021347 := bstep (se 1 (by rfl) ⟨2266010, by rfl⟩ : syracuseStep 3021347 = 4532021) B4532021
theorem B2014231 : Blo 2013435 2014231 := bstep (se 1 (by rfl) ⟨1510673, by rfl⟩ : syracuseStep 2014231 = 3021347) B3021347
theorem B2419813 : Blo 2013435 2419813 := bbase (se 4 (by rfl) ⟨226857, by rfl⟩ : syracuseStep 2419813 = 453715) (by norm_num)
theorem B12905669 : Blo 2013435 12905669 := bstep (se 4 (by rfl) ⟨1209906, by rfl⟩ : syracuseStep 12905669 = 2419813) B2419813
theorem B8603779 : Blo 2013435 8603779 := bstep (se 1 (by rfl) ⟨6452834, by rfl⟩ : syracuseStep 8603779 = 12905669) B12905669
theorem B11471705 : Blo 2013435 11471705 := bstep (se 2 (by rfl) ⟨4301889, by rfl⟩ : syracuseStep 11471705 = 8603779) B8603779
theorem B7647803 : Blo 2013435 7647803 := bstep (se 1 (by rfl) ⟨5735852, by rfl⟩ : syracuseStep 7647803 = 11471705) B11471705
theorem B5098535 : Blo 2013435 5098535 := bstep (se 1 (by rfl) ⟨3823901, by rfl⟩ : syracuseStep 5098535 = 7647803) B7647803
theorem B3399023 : Blo 2013435 3399023 := bstep (se 1 (by rfl) ⟨2549267, by rfl⟩ : syracuseStep 3399023 = 5098535) B5098535
theorem B2266015 : Blo 2013435 2266015 := bstep (se 1 (by rfl) ⟨1699511, by rfl⟩ : syracuseStep 2266015 = 3399023) B3399023
theorem B3021353 : Blo 2013435 3021353 := bstep (se 2 (by rfl) ⟨1133007, by rfl⟩ : syracuseStep 3021353 = 2266015) B2266015
theorem B2014235 : Blo 2013435 2014235 := bstep (se 1 (by rfl) ⟨1510676, by rfl⟩ : syracuseStep 2014235 = 3021353) B3021353
theorem B2296937 : Blo 2013435 2296937 := bbase (se 2 (by rfl) ⟨861351, by rfl⟩ : syracuseStep 2296937 = 1722703) (by norm_num)
theorem B6125165 : Blo 2013435 6125165 := bstep (se 3 (by rfl) ⟨1148468, by rfl⟩ : syracuseStep 6125165 = 2296937) B2296937
theorem B4083443 : Blo 2013435 4083443 := bstep (se 1 (by rfl) ⟨3062582, by rfl⟩ : syracuseStep 4083443 = 6125165) B6125165
theorem B2722295 : Blo 2013435 2722295 := bstep (se 1 (by rfl) ⟨2041721, by rfl⟩ : syracuseStep 2722295 = 4083443) B4083443
theorem B7259453 : Blo 2013435 7259453 := bstep (se 3 (by rfl) ⟨1361147, by rfl⟩ : syracuseStep 7259453 = 2722295) B2722295
theorem B4839635 : Blo 2013435 4839635 := bstep (se 1 (by rfl) ⟨3629726, by rfl⟩ : syracuseStep 4839635 = 7259453) B7259453
theorem B12905693 : Blo 2013435 12905693 := bstep (se 3 (by rfl) ⟨2419817, by rfl⟩ : syracuseStep 12905693 = 4839635) B4839635
theorem B8603795 : Blo 2013435 8603795 := bstep (se 1 (by rfl) ⟨6452846, by rfl⟩ : syracuseStep 8603795 = 12905693) B12905693
theorem B5735863 : Blo 2013435 5735863 := bstep (se 1 (by rfl) ⟨4301897, by rfl⟩ : syracuseStep 5735863 = 8603795) B8603795
theorem B7647817 : Blo 2013435 7647817 := bstep (se 2 (by rfl) ⟨2867931, by rfl⟩ : syracuseStep 7647817 = 5735863) B5735863
theorem B10197089 : Blo 2013435 10197089 := bstep (se 2 (by rfl) ⟨3823908, by rfl⟩ : syracuseStep 10197089 = 7647817) B7647817
theorem B6798059 : Blo 2013435 6798059 := bstep (se 1 (by rfl) ⟨5098544, by rfl⟩ : syracuseStep 6798059 = 10197089) B10197089
theorem B4532039 : Blo 2013435 4532039 := bstep (se 1 (by rfl) ⟨3399029, by rfl⟩ : syracuseStep 4532039 = 6798059) B6798059
theorem B3021359 : Blo 2013435 3021359 := bstep (se 1 (by rfl) ⟨2266019, by rfl⟩ : syracuseStep 3021359 = 4532039) B4532039
theorem B2014239 : Blo 2013435 2014239 := bstep (se 1 (by rfl) ⟨1510679, by rfl⟩ : syracuseStep 2014239 = 3021359) B3021359
theorem B3021365 : Blo 2013435 3021365 := bbase (se 5 (by rfl) ⟨141626, by rfl⟩ : syracuseStep 3021365 = 283253) (by norm_num)
theorem B2014243 : Blo 2013435 2014243 := bstep (se 1 (by rfl) ⟨1510682, by rfl⟩ : syracuseStep 2014243 = 3021365) B3021365
theorem B5098565 : Blo 2013435 5098565 := bbase (se 4 (by rfl) ⟨477990, by rfl⟩ : syracuseStep 5098565 = 955981) (by norm_num)
theorem B3399043 : Blo 2013435 3399043 := bstep (se 1 (by rfl) ⟨2549282, by rfl⟩ : syracuseStep 3399043 = 5098565) B5098565
theorem B4532057 : Blo 2013435 4532057 := bstep (se 2 (by rfl) ⟨1699521, by rfl⟩ : syracuseStep 4532057 = 3399043) B3399043
theorem B3021371 : Blo 2013435 3021371 := bstep (se 1 (by rfl) ⟨2266028, by rfl⟩ : syracuseStep 3021371 = 4532057) B4532057
theorem B2014247 : Blo 2013435 2014247 := bstep (se 1 (by rfl) ⟨1510685, by rfl⟩ : syracuseStep 2014247 = 3021371) B3021371
theorem B2266033 : Blo 2013435 2266033 := bbase (se 2 (by rfl) ⟨849762, by rfl⟩ : syracuseStep 2266033 = 1699525) (by norm_num)
theorem B3021377 : Blo 2013435 3021377 := bstep (se 2 (by rfl) ⟨1133016, by rfl⟩ : syracuseStep 3021377 = 2266033) B2266033
theorem B2014251 : Blo 2013435 2014251 := bstep (se 1 (by rfl) ⟨1510688, by rfl⟩ : syracuseStep 2014251 = 3021377) B3021377
theorem B5735909 : Blo 2013435 5735909 := bbase (se 4 (by rfl) ⟨537741, by rfl⟩ : syracuseStep 5735909 = 1075483) (by norm_num)
theorem B3823939 : Blo 2013435 3823939 := bstep (se 1 (by rfl) ⟨2867954, by rfl⟩ : syracuseStep 3823939 = 5735909) B5735909
theorem B5098585 : Blo 2013435 5098585 := bstep (se 2 (by rfl) ⟨1911969, by rfl⟩ : syracuseStep 5098585 = 3823939) B3823939
theorem B6798113 : Blo 2013435 6798113 := bstep (se 2 (by rfl) ⟨2549292, by rfl⟩ : syracuseStep 6798113 = 5098585) B5098585
theorem B4532075 : Blo 2013435 4532075 := bstep (se 1 (by rfl) ⟨3399056, by rfl⟩ : syracuseStep 4532075 = 6798113) B6798113
theorem B3021383 : Blo 2013435 3021383 := bstep (se 1 (by rfl) ⟨2266037, by rfl⟩ : syracuseStep 3021383 = 4532075) B4532075
theorem B2014255 : Blo 2013435 2014255 := bstep (se 1 (by rfl) ⟨1510691, by rfl⟩ : syracuseStep 2014255 = 3021383) B3021383
theorem B3021389 : Blo 2013435 3021389 := bbase (se 3 (by rfl) ⟨566510, by rfl⟩ : syracuseStep 3021389 = 1133021) (by norm_num)
theorem B2014259 : Blo 2013435 2014259 := bstep (se 1 (by rfl) ⟨1510694, by rfl⟩ : syracuseStep 2014259 = 3021389) B3021389
theorem B4532093 : Blo 2013435 4532093 := bbase (se 3 (by rfl) ⟨849767, by rfl⟩ : syracuseStep 4532093 = 1699535) (by norm_num)
theorem B3021395 : Blo 2013435 3021395 := bstep (se 1 (by rfl) ⟨2266046, by rfl⟩ : syracuseStep 3021395 = 4532093) B4532093
theorem B2014263 : Blo 2013435 2014263 := bstep (se 1 (by rfl) ⟨1510697, by rfl⟩ : syracuseStep 2014263 = 3021395) B3021395
theorem B3399077 : Blo 2013435 3399077 := bbase (se 4 (by rfl) ⟨318663, by rfl⟩ : syracuseStep 3399077 = 637327) (by norm_num)
theorem B2266051 : Blo 2013435 2266051 := bstep (se 1 (by rfl) ⟨1699538, by rfl⟩ : syracuseStep 2266051 = 3399077) B3399077
theorem B3021401 : Blo 2013435 3021401 := bstep (se 2 (by rfl) ⟨1133025, by rfl⟩ : syracuseStep 3021401 = 2266051) B2266051
theorem B2014267 : Blo 2013435 2014267 := bstep (se 1 (by rfl) ⟨1510700, by rfl⟩ : syracuseStep 2014267 = 3021401) B3021401
theorem B4083509 : Blo 2013435 4083509 := bbase (se 5 (by rfl) ⟨191414, by rfl⟩ : syracuseStep 4083509 = 382829) (by norm_num)
theorem B2722339 : Blo 2013435 2722339 := bstep (se 1 (by rfl) ⟨2041754, by rfl⟩ : syracuseStep 2722339 = 4083509) B4083509
theorem B3629785 : Blo 2013435 3629785 := bstep (se 2 (by rfl) ⟨1361169, by rfl⟩ : syracuseStep 3629785 = 2722339) B2722339
theorem B4839713 : Blo 2013435 4839713 := bstep (se 2 (by rfl) ⟨1814892, by rfl⟩ : syracuseStep 4839713 = 3629785) B3629785
theorem B3226475 : Blo 2013435 3226475 := bstep (se 1 (by rfl) ⟨2419856, by rfl⟩ : syracuseStep 3226475 = 4839713) B4839713
theorem B2150983 : Blo 2013435 2150983 := bstep (se 1 (by rfl) ⟨1613237, by rfl⟩ : syracuseStep 2150983 = 3226475) B3226475
theorem B2867977 : Blo 2013435 2867977 := bstep (se 2 (by rfl) ⟨1075491, by rfl⟩ : syracuseStep 2867977 = 2150983) B2150983
theorem B15295877 : Blo 2013435 15295877 := bstep (se 4 (by rfl) ⟨1433988, by rfl⟩ : syracuseStep 15295877 = 2867977) B2867977
theorem B10197251 : Blo 2013435 10197251 := bstep (se 1 (by rfl) ⟨7647938, by rfl⟩ : syracuseStep 10197251 = 15295877) B15295877
theorem B6798167 : Blo 2013435 6798167 := bstep (se 1 (by rfl) ⟨5098625, by rfl⟩ : syracuseStep 6798167 = 10197251) B10197251
theorem B4532111 : Blo 2013435 4532111 := bstep (se 1 (by rfl) ⟨3399083, by rfl⟩ : syracuseStep 4532111 = 6798167) B6798167
theorem B3021407 : Blo 2013435 3021407 := bstep (se 1 (by rfl) ⟨2266055, by rfl⟩ : syracuseStep 3021407 = 4532111) B4532111
theorem B2014271 : Blo 2013435 2014271 := bstep (se 1 (by rfl) ⟨1510703, by rfl⟩ : syracuseStep 2014271 = 3021407) B3021407
theorem B3021413 : Blo 2013435 3021413 := bbase (se 4 (by rfl) ⟨283257, by rfl⟩ : syracuseStep 3021413 = 566515) (by norm_num)
theorem B2014275 : Blo 2013435 2014275 := bstep (se 1 (by rfl) ⟨1510706, by rfl⟩ : syracuseStep 2014275 = 3021413) B3021413
theorem B2867989 : Blo 2013435 2867989 := bbase (se 6 (by rfl) ⟨67218, by rfl⟩ : syracuseStep 2867989 = 134437) (by norm_num)
theorem B3823985 : Blo 2013435 3823985 := bstep (se 2 (by rfl) ⟨1433994, by rfl⟩ : syracuseStep 3823985 = 2867989) B2867989
theorem B2549323 : Blo 2013435 2549323 := bstep (se 1 (by rfl) ⟨1911992, by rfl⟩ : syracuseStep 2549323 = 3823985) B3823985
theorem B3399097 : Blo 2013435 3399097 := bstep (se 2 (by rfl) ⟨1274661, by rfl⟩ : syracuseStep 3399097 = 2549323) B2549323
theorem B4532129 : Blo 2013435 4532129 := bstep (se 2 (by rfl) ⟨1699548, by rfl⟩ : syracuseStep 4532129 = 3399097) B3399097
theorem B3021419 : Blo 2013435 3021419 := bstep (se 1 (by rfl) ⟨2266064, by rfl⟩ : syracuseStep 3021419 = 4532129) B4532129
theorem B2014279 : Blo 2013435 2014279 := bstep (se 1 (by rfl) ⟨1510709, by rfl⟩ : syracuseStep 2014279 = 3021419) B3021419
theorem B2266069 : Blo 2013435 2266069 := bbase (se 7 (by rfl) ⟨26555, by rfl⟩ : syracuseStep 2266069 = 53111) (by norm_num)
theorem B3021425 : Blo 2013435 3021425 := bstep (se 2 (by rfl) ⟨1133034, by rfl⟩ : syracuseStep 3021425 = 2266069) B2266069
theorem B2014283 : Blo 2013435 2014283 := bstep (se 1 (by rfl) ⟨1510712, by rfl⟩ : syracuseStep 2014283 = 3021425) B3021425
theorem B2549333 : Blo 2013435 2549333 := bbase (se 8 (by rfl) ⟨14937, by rfl⟩ : syracuseStep 2549333 = 29875) (by norm_num)
theorem B6798221 : Blo 2013435 6798221 := bstep (se 3 (by rfl) ⟨1274666, by rfl⟩ : syracuseStep 6798221 = 2549333) B2549333
theorem B4532147 : Blo 2013435 4532147 := bstep (se 1 (by rfl) ⟨3399110, by rfl⟩ : syracuseStep 4532147 = 6798221) B6798221
theorem B3021431 : Blo 2013435 3021431 := bstep (se 1 (by rfl) ⟨2266073, by rfl⟩ : syracuseStep 3021431 = 4532147) B4532147
theorem B2014287 : Blo 2013435 2014287 := bstep (se 1 (by rfl) ⟨1510715, by rfl⟩ : syracuseStep 2014287 = 3021431) B3021431
theorem B3021437 : Blo 2013435 3021437 := bbase (se 3 (by rfl) ⟨566519, by rfl⟩ : syracuseStep 3021437 = 1133039) (by norm_num)
theorem B2014291 : Blo 2013435 2014291 := bstep (se 1 (by rfl) ⟨1510718, by rfl⟩ : syracuseStep 2014291 = 3021437) B3021437
theorem B4532165 : Blo 2013435 4532165 := bbase (se 4 (by rfl) ⟨424890, by rfl⟩ : syracuseStep 4532165 = 849781) (by norm_num)
theorem B3021443 : Blo 2013435 3021443 := bstep (se 1 (by rfl) ⟨2266082, by rfl⟩ : syracuseStep 3021443 = 4532165) B4532165
theorem B2014295 : Blo 2013435 2014295 := bstep (se 1 (by rfl) ⟨1510721, by rfl⟩ : syracuseStep 2014295 = 3021443) B3021443
theorem B8604053 : Blo 2013435 8604053 := bbase (se 6 (by rfl) ⟨201657, by rfl⟩ : syracuseStep 8604053 = 403315) (by norm_num)
theorem B5736035 : Blo 2013435 5736035 := bstep (se 1 (by rfl) ⟨4302026, by rfl⟩ : syracuseStep 5736035 = 8604053) B8604053
theorem B3824023 : Blo 2013435 3824023 := bstep (se 1 (by rfl) ⟨2868017, by rfl⟩ : syracuseStep 3824023 = 5736035) B5736035
theorem B5098697 : Blo 2013435 5098697 := bstep (se 2 (by rfl) ⟨1912011, by rfl⟩ : syracuseStep 5098697 = 3824023) B3824023
theorem B3399131 : Blo 2013435 3399131 := bstep (se 1 (by rfl) ⟨2549348, by rfl⟩ : syracuseStep 3399131 = 5098697) B5098697
theorem B2266087 : Blo 2013435 2266087 := bstep (se 1 (by rfl) ⟨1699565, by rfl⟩ : syracuseStep 2266087 = 3399131) B3399131
theorem B3021449 : Blo 2013435 3021449 := bstep (se 2 (by rfl) ⟨1133043, by rfl⟩ : syracuseStep 3021449 = 2266087) B2266087
theorem B2014299 : Blo 2013435 2014299 := bstep (se 1 (by rfl) ⟨1510724, by rfl⟩ : syracuseStep 2014299 = 3021449) B3021449
theorem B10197413 : Blo 2013435 10197413 := bbase (se 4 (by rfl) ⟨956007, by rfl⟩ : syracuseStep 10197413 = 1912015) (by norm_num)
theorem B6798275 : Blo 2013435 6798275 := bstep (se 1 (by rfl) ⟨5098706, by rfl⟩ : syracuseStep 6798275 = 10197413) B10197413
theorem B4532183 : Blo 2013435 4532183 := bstep (se 1 (by rfl) ⟨3399137, by rfl⟩ : syracuseStep 4532183 = 6798275) B6798275
theorem B3021455 : Blo 2013435 3021455 := bstep (se 1 (by rfl) ⟨2266091, by rfl⟩ : syracuseStep 3021455 = 4532183) B4532183
theorem B2014303 : Blo 2013435 2014303 := bstep (se 1 (by rfl) ⟨1510727, by rfl⟩ : syracuseStep 2014303 = 3021455) B3021455
theorem B3021461 : Blo 2013435 3021461 := bbase (se 6 (by rfl) ⟨70815, by rfl⟩ : syracuseStep 3021461 = 141631) (by norm_num)
theorem B2014307 : Blo 2013435 2014307 := bstep (se 1 (by rfl) ⟨1510730, by rfl⟩ : syracuseStep 2014307 = 3021461) B3021461
theorem B3679381 : Blo 2013435 3679381 := bbase (se 6 (by rfl) ⟨86235, by rfl⟩ : syracuseStep 3679381 = 172471) (by norm_num)
theorem B4905841 : Blo 2013435 4905841 := bstep (se 2 (by rfl) ⟨1839690, by rfl⟩ : syracuseStep 4905841 = 3679381) B3679381
theorem B6541121 : Blo 2013435 6541121 := bstep (se 2 (by rfl) ⟨2452920, by rfl⟩ : syracuseStep 6541121 = 4905841) B4905841
theorem B17442989 : Blo 2013435 17442989 := bstep (se 3 (by rfl) ⟨3270560, by rfl⟩ : syracuseStep 17442989 = 6541121) B6541121
theorem B11628659 : Blo 2013435 11628659 := bstep (se 1 (by rfl) ⟨8721494, by rfl⟩ : syracuseStep 11628659 = 17442989) B17442989
theorem B7752439 : Blo 2013435 7752439 := bstep (se 1 (by rfl) ⟨5814329, by rfl⟩ : syracuseStep 7752439 = 11628659) B11628659
theorem B10336585 : Blo 2013435 10336585 := bstep (se 2 (by rfl) ⟨3876219, by rfl⟩ : syracuseStep 10336585 = 7752439) B7752439
theorem B13782113 : Blo 2013435 13782113 := bstep (se 2 (by rfl) ⟨5168292, by rfl⟩ : syracuseStep 13782113 = 10336585) B10336585
theorem B9188075 : Blo 2013435 9188075 := bstep (se 1 (by rfl) ⟨6891056, by rfl⟩ : syracuseStep 9188075 = 13782113) B13782113
theorem B6125383 : Blo 2013435 6125383 := bstep (se 1 (by rfl) ⟨4594037, by rfl⟩ : syracuseStep 6125383 = 9188075) B9188075
theorem B8167177 : Blo 2013435 8167177 := bstep (se 2 (by rfl) ⟨3062691, by rfl⟩ : syracuseStep 8167177 = 6125383) B6125383
theorem B10889569 : Blo 2013435 10889569 := bstep (se 2 (by rfl) ⟨4083588, by rfl⟩ : syracuseStep 10889569 = 8167177) B8167177
theorem B14519425 : Blo 2013435 14519425 := bstep (se 2 (by rfl) ⟨5444784, by rfl⟩ : syracuseStep 14519425 = 10889569) B10889569
theorem B19359233 : Blo 2013435 19359233 := bstep (se 2 (by rfl) ⟨7259712, by rfl⟩ : syracuseStep 19359233 = 14519425) B14519425
theorem B12906155 : Blo 2013435 12906155 := bstep (se 1 (by rfl) ⟨9679616, by rfl⟩ : syracuseStep 12906155 = 19359233) B19359233
theorem B8604103 : Blo 2013435 8604103 := bstep (se 1 (by rfl) ⟨6453077, by rfl⟩ : syracuseStep 8604103 = 12906155) B12906155
theorem B11472137 : Blo 2013435 11472137 := bstep (se 2 (by rfl) ⟨4302051, by rfl⟩ : syracuseStep 11472137 = 8604103) B8604103
theorem B7648091 : Blo 2013435 7648091 := bstep (se 1 (by rfl) ⟨5736068, by rfl⟩ : syracuseStep 7648091 = 11472137) B11472137
theorem B5098727 : Blo 2013435 5098727 := bstep (se 1 (by rfl) ⟨3824045, by rfl⟩ : syracuseStep 5098727 = 7648091) B7648091
theorem B3399151 : Blo 2013435 3399151 := bstep (se 1 (by rfl) ⟨2549363, by rfl⟩ : syracuseStep 3399151 = 5098727) B5098727
theorem B4532201 : Blo 2013435 4532201 := bstep (se 2 (by rfl) ⟨1699575, by rfl⟩ : syracuseStep 4532201 = 3399151) B3399151
theorem B3021467 : Blo 2013435 3021467 := bstep (se 1 (by rfl) ⟨2266100, by rfl⟩ : syracuseStep 3021467 = 4532201) B4532201
theorem B2014311 : Blo 2013435 2014311 := bstep (se 1 (by rfl) ⟨1510733, by rfl⟩ : syracuseStep 2014311 = 3021467) B3021467
theorem B2266105 : Blo 2013435 2266105 := bbase (se 2 (by rfl) ⟨849789, by rfl⟩ : syracuseStep 2266105 = 1699579) (by norm_num)
theorem B3021473 : Blo 2013435 3021473 := bstep (se 2 (by rfl) ⟨1133052, by rfl⟩ : syracuseStep 3021473 = 2266105) B2266105
theorem B2014315 : Blo 2013435 2014315 := bstep (se 1 (by rfl) ⟨1510736, by rfl⟩ : syracuseStep 2014315 = 3021473) B3021473
theorem B31009877 : Blo 2013435 31009877 := bbase (se 8 (by rfl) ⟨181698, by rfl⟩ : syracuseStep 31009877 = 363397) (by norm_num)
theorem B20673251 : Blo 2013435 20673251 := bstep (se 1 (by rfl) ⟨15504938, by rfl⟩ : syracuseStep 20673251 = 31009877) B31009877
theorem B13782167 : Blo 2013435 13782167 := bstep (se 1 (by rfl) ⟨10336625, by rfl⟩ : syracuseStep 13782167 = 20673251) B20673251
theorem B9188111 : Blo 2013435 9188111 := bstep (se 1 (by rfl) ⟨6891083, by rfl⟩ : syracuseStep 9188111 = 13782167) B13782167
theorem B24501629 : Blo 2013435 24501629 := bstep (se 3 (by rfl) ⟨4594055, by rfl⟩ : syracuseStep 24501629 = 9188111) B9188111
theorem B16334419 : Blo 2013435 16334419 := bstep (se 1 (by rfl) ⟨12250814, by rfl⟩ : syracuseStep 16334419 = 24501629) B24501629
theorem B21779225 : Blo 2013435 21779225 := bstep (se 2 (by rfl) ⟨8167209, by rfl⟩ : syracuseStep 21779225 = 16334419) B16334419
theorem B14519483 : Blo 2013435 14519483 := bstep (se 1 (by rfl) ⟨10889612, by rfl⟩ : syracuseStep 14519483 = 21779225) B21779225
theorem B9679655 : Blo 2013435 9679655 := bstep (se 1 (by rfl) ⟨7259741, by rfl⟩ : syracuseStep 9679655 = 14519483) B14519483
theorem B6453103 : Blo 2013435 6453103 := bstep (se 1 (by rfl) ⟨4839827, by rfl⟩ : syracuseStep 6453103 = 9679655) B9679655
theorem B8604137 : Blo 2013435 8604137 := bstep (se 2 (by rfl) ⟨3226551, by rfl⟩ : syracuseStep 8604137 = 6453103) B6453103
theorem B5736091 : Blo 2013435 5736091 := bstep (se 1 (by rfl) ⟨4302068, by rfl⟩ : syracuseStep 5736091 = 8604137) B8604137
theorem B7648121 : Blo 2013435 7648121 := bstep (se 2 (by rfl) ⟨2868045, by rfl⟩ : syracuseStep 7648121 = 5736091) B5736091
theorem B5098747 : Blo 2013435 5098747 := bstep (se 1 (by rfl) ⟨3824060, by rfl⟩ : syracuseStep 5098747 = 7648121) B7648121
theorem B6798329 : Blo 2013435 6798329 := bstep (se 2 (by rfl) ⟨2549373, by rfl⟩ : syracuseStep 6798329 = 5098747) B5098747
theorem B4532219 : Blo 2013435 4532219 := bstep (se 1 (by rfl) ⟨3399164, by rfl⟩ : syracuseStep 4532219 = 6798329) B6798329
theorem B3021479 : Blo 2013435 3021479 := bstep (se 1 (by rfl) ⟨2266109, by rfl⟩ : syracuseStep 3021479 = 4532219) B4532219
theorem B2014319 : Blo 2013435 2014319 := bstep (se 1 (by rfl) ⟨1510739, by rfl⟩ : syracuseStep 2014319 = 3021479) B3021479
theorem B3021485 : Blo 2013435 3021485 := bbase (se 3 (by rfl) ⟨566528, by rfl⟩ : syracuseStep 3021485 = 1133057) (by norm_num)
theorem B2014323 : Blo 2013435 2014323 := bstep (se 1 (by rfl) ⟨1510742, by rfl⟩ : syracuseStep 2014323 = 3021485) B3021485
theorem B4532237 : Blo 2013435 4532237 := bbase (se 3 (by rfl) ⟨849794, by rfl⟩ : syracuseStep 4532237 = 1699589) (by norm_num)
theorem B3021491 : Blo 2013435 3021491 := bstep (se 1 (by rfl) ⟨2266118, by rfl⟩ : syracuseStep 3021491 = 4532237) B4532237
theorem B2014327 : Blo 2013435 2014327 := bstep (se 1 (by rfl) ⟨1510745, by rfl⟩ : syracuseStep 2014327 = 3021491) B3021491
theorem B2549389 : Blo 2013435 2549389 := bbase (se 3 (by rfl) ⟨478010, by rfl⟩ : syracuseStep 2549389 = 956021) (by norm_num)
theorem B3399185 : Blo 2013435 3399185 := bstep (se 2 (by rfl) ⟨1274694, by rfl⟩ : syracuseStep 3399185 = 2549389) B2549389
theorem B2266123 : Blo 2013435 2266123 := bstep (se 1 (by rfl) ⟨1699592, by rfl⟩ : syracuseStep 2266123 = 3399185) B3399185
theorem B3021497 : Blo 2013435 3021497 := bstep (se 2 (by rfl) ⟨1133061, by rfl⟩ : syracuseStep 3021497 = 2266123) B2266123
theorem B2014331 : Blo 2013435 2014331 := bstep (se 1 (by rfl) ⟨1510748, by rfl⟩ : syracuseStep 2014331 = 3021497) B3021497
theorem B4083637 : Blo 2013435 4083637 := bbase (se 5 (by rfl) ⟨191420, by rfl⟩ : syracuseStep 4083637 = 382841) (by norm_num)
theorem B5444849 : Blo 2013435 5444849 := bstep (se 2 (by rfl) ⟨2041818, by rfl⟩ : syracuseStep 5444849 = 4083637) B4083637
theorem B3629899 : Blo 2013435 3629899 := bstep (se 1 (by rfl) ⟨2722424, by rfl⟩ : syracuseStep 3629899 = 5444849) B5444849
theorem B19359461 : Blo 2013435 19359461 := bstep (se 4 (by rfl) ⟨1814949, by rfl⟩ : syracuseStep 19359461 = 3629899) B3629899
theorem B12906307 : Blo 2013435 12906307 := bstep (se 1 (by rfl) ⟨9679730, by rfl⟩ : syracuseStep 12906307 = 19359461) B19359461
theorem B17208409 : Blo 2013435 17208409 := bstep (se 2 (by rfl) ⟨6453153, by rfl⟩ : syracuseStep 17208409 = 12906307) B12906307
theorem B22944545 : Blo 2013435 22944545 := bstep (se 2 (by rfl) ⟨8604204, by rfl⟩ : syracuseStep 22944545 = 17208409) B17208409
theorem B15296363 : Blo 2013435 15296363 := bstep (se 1 (by rfl) ⟨11472272, by rfl⟩ : syracuseStep 15296363 = 22944545) B22944545
theorem B10197575 : Blo 2013435 10197575 := bstep (se 1 (by rfl) ⟨7648181, by rfl⟩ : syracuseStep 10197575 = 15296363) B15296363
theorem B6798383 : Blo 2013435 6798383 := bstep (se 1 (by rfl) ⟨5098787, by rfl⟩ : syracuseStep 6798383 = 10197575) B10197575
theorem B4532255 : Blo 2013435 4532255 := bstep (se 1 (by rfl) ⟨3399191, by rfl⟩ : syracuseStep 4532255 = 6798383) B6798383
theorem B3021503 : Blo 2013435 3021503 := bstep (se 1 (by rfl) ⟨2266127, by rfl⟩ : syracuseStep 3021503 = 4532255) B4532255
theorem B2014335 : Blo 2013435 2014335 := bstep (se 1 (by rfl) ⟨1510751, by rfl⟩ : syracuseStep 2014335 = 3021503) B3021503
theorem B3021509 : Blo 2013435 3021509 := bbase (se 4 (by rfl) ⟨283266, by rfl⟩ : syracuseStep 3021509 = 566533) (by norm_num)
theorem B2014339 : Blo 2013435 2014339 := bstep (se 1 (by rfl) ⟨1510754, by rfl⟩ : syracuseStep 2014339 = 3021509) B3021509
theorem B3399205 : Blo 2013435 3399205 := bbase (se 4 (by rfl) ⟨318675, by rfl⟩ : syracuseStep 3399205 = 637351) (by norm_num)
theorem B4532273 : Blo 2013435 4532273 := bstep (se 2 (by rfl) ⟨1699602, by rfl⟩ : syracuseStep 4532273 = 3399205) B3399205
theorem B3021515 : Blo 2013435 3021515 := bstep (se 1 (by rfl) ⟨2266136, by rfl⟩ : syracuseStep 3021515 = 4532273) B4532273
theorem B2014343 : Blo 2013435 2014343 := bstep (se 1 (by rfl) ⟨1510757, by rfl⟩ : syracuseStep 2014343 = 3021515) B3021515
theorem B2266141 : Blo 2013435 2266141 := bbase (se 3 (by rfl) ⟨424901, by rfl⟩ : syracuseStep 2266141 = 849803) (by norm_num)
theorem B3021521 : Blo 2013435 3021521 := bstep (se 2 (by rfl) ⟨1133070, by rfl⟩ : syracuseStep 3021521 = 2266141) B2266141
theorem B2014347 : Blo 2013435 2014347 := bstep (se 1 (by rfl) ⟨1510760, by rfl⟩ : syracuseStep 2014347 = 3021521) B3021521
theorem B6798437 : Blo 2013435 6798437 := bbase (se 4 (by rfl) ⟨637353, by rfl⟩ : syracuseStep 6798437 = 1274707) (by norm_num)
theorem B4532291 : Blo 2013435 4532291 := bstep (se 1 (by rfl) ⟨3399218, by rfl⟩ : syracuseStep 4532291 = 6798437) B6798437
theorem B3021527 : Blo 2013435 3021527 := bstep (se 1 (by rfl) ⟨2266145, by rfl⟩ : syracuseStep 3021527 = 4532291) B4532291
theorem B2014351 : Blo 2013435 2014351 := bstep (se 1 (by rfl) ⟨1510763, by rfl⟩ : syracuseStep 2014351 = 3021527) B3021527
theorem B3021533 : Blo 2013435 3021533 := bbase (se 3 (by rfl) ⟨566537, by rfl⟩ : syracuseStep 3021533 = 1133075) (by norm_num)
theorem B2014355 : Blo 2013435 2014355 := bstep (se 1 (by rfl) ⟨1510766, by rfl⟩ : syracuseStep 2014355 = 3021533) B3021533
theorem B4532309 : Blo 2013435 4532309 := bbase (se 8 (by rfl) ⟨26556, by rfl⟩ : syracuseStep 4532309 = 53113) (by norm_num)
theorem B3021539 : Blo 2013435 3021539 := bstep (se 1 (by rfl) ⟨2266154, by rfl⟩ : syracuseStep 3021539 = 4532309) B4532309
theorem B2014359 : Blo 2013435 2014359 := bstep (se 1 (by rfl) ⟨1510769, by rfl⟩ : syracuseStep 2014359 = 3021539) B3021539
theorem B4360861 : Blo 2013435 4360861 := bbase (se 3 (by rfl) ⟨817661, by rfl⟩ : syracuseStep 4360861 = 1635323) (by norm_num)
theorem B23257925 : Blo 2013435 23257925 := bstep (se 4 (by rfl) ⟨2180430, by rfl⟩ : syracuseStep 23257925 = 4360861) B4360861
theorem B15505283 : Blo 2013435 15505283 := bstep (se 1 (by rfl) ⟨11628962, by rfl⟩ : syracuseStep 15505283 = 23257925) B23257925
theorem B41347421 : Blo 2013435 41347421 := bstep (se 3 (by rfl) ⟨7752641, by rfl⟩ : syracuseStep 41347421 = 15505283) B15505283
theorem B27564947 : Blo 2013435 27564947 := bstep (se 1 (by rfl) ⟨20673710, by rfl⟩ : syracuseStep 27564947 = 41347421) B41347421
theorem B18376631 : Blo 2013435 18376631 := bstep (se 1 (by rfl) ⟨13782473, by rfl⟩ : syracuseStep 18376631 = 27564947) B27564947
theorem B12251087 : Blo 2013435 12251087 := bstep (se 1 (by rfl) ⟨9188315, by rfl⟩ : syracuseStep 12251087 = 18376631) B18376631
theorem B8167391 : Blo 2013435 8167391 := bstep (se 1 (by rfl) ⟨6125543, by rfl⟩ : syracuseStep 8167391 = 12251087) B12251087
theorem B5444927 : Blo 2013435 5444927 := bstep (se 1 (by rfl) ⟨4083695, by rfl⟩ : syracuseStep 5444927 = 8167391) B8167391
theorem B3629951 : Blo 2013435 3629951 := bstep (se 1 (by rfl) ⟨2722463, by rfl⟩ : syracuseStep 3629951 = 5444927) B5444927
theorem B2419967 : Blo 2013435 2419967 := bstep (se 1 (by rfl) ⟨1814975, by rfl⟩ : syracuseStep 2419967 = 3629951) B3629951
theorem B6453245 : Blo 2013435 6453245 := bstep (se 3 (by rfl) ⟨1209983, by rfl⟩ : syracuseStep 6453245 = 2419967) B2419967
theorem B4302163 : Blo 2013435 4302163 := bstep (se 1 (by rfl) ⟨3226622, by rfl⟩ : syracuseStep 4302163 = 6453245) B6453245
theorem B5736217 : Blo 2013435 5736217 := bstep (se 2 (by rfl) ⟨2151081, by rfl⟩ : syracuseStep 5736217 = 4302163) B4302163
theorem B7648289 : Blo 2013435 7648289 := bstep (se 2 (by rfl) ⟨2868108, by rfl⟩ : syracuseStep 7648289 = 5736217) B5736217
theorem B5098859 : Blo 2013435 5098859 := bstep (se 1 (by rfl) ⟨3824144, by rfl⟩ : syracuseStep 5098859 = 7648289) B7648289
theorem B3399239 : Blo 2013435 3399239 := bstep (se 1 (by rfl) ⟨2549429, by rfl⟩ : syracuseStep 3399239 = 5098859) B5098859
theorem B2266159 : Blo 2013435 2266159 := bstep (se 1 (by rfl) ⟨1699619, by rfl⟩ : syracuseStep 2266159 = 3399239) B3399239
theorem B3021545 : Blo 2013435 3021545 := bstep (se 2 (by rfl) ⟨1133079, by rfl⟩ : syracuseStep 3021545 = 2266159) B2266159
theorem B2014363 : Blo 2013435 2014363 := bstep (se 1 (by rfl) ⟨1510772, by rfl⟩ : syracuseStep 2014363 = 3021545) B3021545
theorem B4253141 : Blo 2013435 4253141 := bbase (se 7 (by rfl) ⟨49841, by rfl⟩ : syracuseStep 4253141 = 99683) (by norm_num)
theorem B2835427 : Blo 2013435 2835427 := bstep (se 1 (by rfl) ⟨2126570, by rfl⟩ : syracuseStep 2835427 = 4253141) B4253141
theorem B3780569 : Blo 2013435 3780569 := bstep (se 2 (by rfl) ⟨1417713, by rfl⟩ : syracuseStep 3780569 = 2835427) B2835427
theorem B2520379 : Blo 2013435 2520379 := bstep (se 1 (by rfl) ⟨1890284, by rfl⟩ : syracuseStep 2520379 = 3780569) B3780569
theorem B3360505 : Blo 2013435 3360505 := bstep (se 2 (by rfl) ⟨1260189, by rfl⟩ : syracuseStep 3360505 = 2520379) B2520379
theorem B71690773 : Blo 2013435 71690773 := bstep (se 6 (by rfl) ⟨1680252, by rfl⟩ : syracuseStep 71690773 = 3360505) B3360505
theorem B95587697 : Blo 2013435 95587697 := bstep (se 2 (by rfl) ⟨35845386, by rfl⟩ : syracuseStep 95587697 = 71690773) B71690773
theorem B63725131 : Blo 2013435 63725131 := bstep (se 1 (by rfl) ⟨47793848, by rfl⟩ : syracuseStep 63725131 = 95587697) B95587697
theorem B84966841 : Blo 2013435 84966841 := bstep (se 2 (by rfl) ⟨31862565, by rfl⟩ : syracuseStep 84966841 = 63725131) B63725131
theorem B113289121 : Blo 2013435 113289121 := bstep (se 2 (by rfl) ⟨42483420, by rfl⟩ : syracuseStep 113289121 = 84966841) B84966841
theorem B151052161 : Blo 2013435 151052161 := bstep (se 2 (by rfl) ⟨56644560, by rfl⟩ : syracuseStep 151052161 = 113289121) B113289121
theorem B201402881 : Blo 2013435 201402881 := bstep (se 2 (by rfl) ⟨75526080, by rfl⟩ : syracuseStep 201402881 = 151052161) B151052161
theorem B134268587 : Blo 2013435 134268587 := bstep (se 1 (by rfl) ⟨100701440, by rfl⟩ : syracuseStep 134268587 = 201402881) B201402881
theorem B89512391 : Blo 2013435 89512391 := bstep (se 1 (by rfl) ⟨67134293, by rfl⟩ : syracuseStep 89512391 = 134268587) B134268587
theorem B59674927 : Blo 2013435 59674927 := bstep (se 1 (by rfl) ⟨44756195, by rfl⟩ : syracuseStep 59674927 = 89512391) B89512391
theorem B79566569 : Blo 2013435 79566569 := bstep (se 2 (by rfl) ⟨29837463, by rfl⟩ : syracuseStep 79566569 = 59674927) B59674927
theorem B53044379 : Blo 2013435 53044379 := bstep (se 1 (by rfl) ⟨39783284, by rfl⟩ : syracuseStep 53044379 = 79566569) B79566569
theorem B35362919 : Blo 2013435 35362919 := bstep (se 1 (by rfl) ⟨26522189, by rfl⟩ : syracuseStep 35362919 = 53044379) B53044379
theorem B94301117 : Blo 2013435 94301117 := bstep (se 3 (by rfl) ⟨17681459, by rfl⟩ : syracuseStep 94301117 = 35362919) B35362919
theorem B62867411 : Blo 2013435 62867411 := bstep (se 1 (by rfl) ⟨47150558, by rfl⟩ : syracuseStep 62867411 = 94301117) B94301117
theorem B41911607 : Blo 2013435 41911607 := bstep (se 1 (by rfl) ⟨31433705, by rfl⟩ : syracuseStep 41911607 = 62867411) B62867411
theorem B27941071 : Blo 2013435 27941071 := bstep (se 1 (by rfl) ⟨20955803, by rfl⟩ : syracuseStep 27941071 = 41911607) B41911607
theorem B37254761 : Blo 2013435 37254761 := bstep (se 2 (by rfl) ⟨13970535, by rfl⟩ : syracuseStep 37254761 = 27941071) B27941071
theorem B24836507 : Blo 2013435 24836507 := bstep (se 1 (by rfl) ⟨18627380, by rfl⟩ : syracuseStep 24836507 = 37254761) B37254761
theorem B16557671 : Blo 2013435 16557671 := bstep (se 1 (by rfl) ⟨12418253, by rfl⟩ : syracuseStep 16557671 = 24836507) B24836507
theorem B11038447 : Blo 2013435 11038447 := bstep (se 1 (by rfl) ⟨8278835, by rfl⟩ : syracuseStep 11038447 = 16557671) B16557671
theorem B58871717 : Blo 2013435 58871717 := bstep (se 4 (by rfl) ⟨5519223, by rfl⟩ : syracuseStep 58871717 = 11038447) B11038447
theorem B39247811 : Blo 2013435 39247811 := bstep (se 1 (by rfl) ⟨29435858, by rfl⟩ : syracuseStep 39247811 = 58871717) B58871717
theorem B26165207 : Blo 2013435 26165207 := bstep (se 1 (by rfl) ⟨19623905, by rfl⟩ : syracuseStep 26165207 = 39247811) B39247811
theorem B17443471 : Blo 2013435 17443471 := bstep (se 1 (by rfl) ⟨13082603, by rfl⟩ : syracuseStep 17443471 = 26165207) B26165207
theorem B23257961 : Blo 2013435 23257961 := bstep (se 2 (by rfl) ⟨8721735, by rfl⟩ : syracuseStep 23257961 = 17443471) B17443471
theorem B15505307 : Blo 2013435 15505307 := bstep (se 1 (by rfl) ⟨11628980, by rfl⟩ : syracuseStep 15505307 = 23257961) B23257961
theorem B10336871 : Blo 2013435 10336871 := bstep (se 1 (by rfl) ⟨7752653, by rfl⟩ : syracuseStep 10336871 = 15505307) B15505307
theorem B6891247 : Blo 2013435 6891247 := bstep (se 1 (by rfl) ⟨5168435, by rfl⟩ : syracuseStep 6891247 = 10336871) B10336871
theorem B9188329 : Blo 2013435 9188329 := bstep (se 2 (by rfl) ⟨3445623, by rfl⟩ : syracuseStep 9188329 = 6891247) B6891247
theorem B12251105 : Blo 2013435 12251105 := bstep (se 2 (by rfl) ⟨4594164, by rfl⟩ : syracuseStep 12251105 = 9188329) B9188329
theorem B8167403 : Blo 2013435 8167403 := bstep (se 1 (by rfl) ⟨6125552, by rfl⟩ : syracuseStep 8167403 = 12251105) B12251105
theorem B21779741 : Blo 2013435 21779741 := bstep (se 3 (by rfl) ⟨4083701, by rfl⟩ : syracuseStep 21779741 = 8167403) B8167403
theorem B14519827 : Blo 2013435 14519827 := bstep (se 1 (by rfl) ⟨10889870, by rfl⟩ : syracuseStep 14519827 = 21779741) B21779741
theorem B19359769 : Blo 2013435 19359769 := bstep (se 2 (by rfl) ⟨7259913, by rfl⟩ : syracuseStep 19359769 = 14519827) B14519827
theorem B25813025 : Blo 2013435 25813025 := bstep (se 2 (by rfl) ⟨9679884, by rfl⟩ : syracuseStep 25813025 = 19359769) B19359769
theorem B17208683 : Blo 2013435 17208683 := bstep (se 1 (by rfl) ⟨12906512, by rfl⟩ : syracuseStep 17208683 = 25813025) B25813025
theorem B11472455 : Blo 2013435 11472455 := bstep (se 1 (by rfl) ⟨8604341, by rfl⟩ : syracuseStep 11472455 = 17208683) B17208683
theorem B7648303 : Blo 2013435 7648303 := bstep (se 1 (by rfl) ⟨5736227, by rfl⟩ : syracuseStep 7648303 = 11472455) B11472455
theorem B10197737 : Blo 2013435 10197737 := bstep (se 2 (by rfl) ⟨3824151, by rfl⟩ : syracuseStep 10197737 = 7648303) B7648303
theorem B6798491 : Blo 2013435 6798491 := bstep (se 1 (by rfl) ⟨5098868, by rfl⟩ : syracuseStep 6798491 = 10197737) B10197737
theorem B4532327 : Blo 2013435 4532327 := bstep (se 1 (by rfl) ⟨3399245, by rfl⟩ : syracuseStep 4532327 = 6798491) B6798491
theorem B3021551 : Blo 2013435 3021551 := bstep (se 1 (by rfl) ⟨2266163, by rfl⟩ : syracuseStep 3021551 = 4532327) B4532327
theorem B2014367 : Blo 2013435 2014367 := bstep (se 1 (by rfl) ⟨1510775, by rfl⟩ : syracuseStep 2014367 = 3021551) B3021551
theorem B3021557 : Blo 2013435 3021557 := bbase (se 5 (by rfl) ⟨141635, by rfl⟩ : syracuseStep 3021557 = 283271) (by norm_num)
theorem B2014371 : Blo 2013435 2014371 := bstep (se 1 (by rfl) ⟨1510778, by rfl⟩ : syracuseStep 2014371 = 3021557) B3021557
theorem B9679925 : Blo 2013435 9679925 := bbase (se 5 (by rfl) ⟨453746, by rfl⟩ : syracuseStep 9679925 = 907493) (by norm_num)
theorem B6453283 : Blo 2013435 6453283 := bstep (se 1 (by rfl) ⟨4839962, by rfl⟩ : syracuseStep 6453283 = 9679925) B9679925
theorem B8604377 : Blo 2013435 8604377 := bstep (se 2 (by rfl) ⟨3226641, by rfl⟩ : syracuseStep 8604377 = 6453283) B6453283
theorem B5736251 : Blo 2013435 5736251 := bstep (se 1 (by rfl) ⟨4302188, by rfl⟩ : syracuseStep 5736251 = 8604377) B8604377
theorem B3824167 : Blo 2013435 3824167 := bstep (se 1 (by rfl) ⟨2868125, by rfl⟩ : syracuseStep 3824167 = 5736251) B5736251
theorem B5098889 : Blo 2013435 5098889 := bstep (se 2 (by rfl) ⟨1912083, by rfl⟩ : syracuseStep 5098889 = 3824167) B3824167
theorem B3399259 : Blo 2013435 3399259 := bstep (se 1 (by rfl) ⟨2549444, by rfl⟩ : syracuseStep 3399259 = 5098889) B5098889
theorem B4532345 : Blo 2013435 4532345 := bstep (se 2 (by rfl) ⟨1699629, by rfl⟩ : syracuseStep 4532345 = 3399259) B3399259
theorem B3021563 : Blo 2013435 3021563 := bstep (se 1 (by rfl) ⟨2266172, by rfl⟩ : syracuseStep 3021563 = 4532345) B4532345
theorem B2014375 : Blo 2013435 2014375 := bstep (se 1 (by rfl) ⟨1510781, by rfl⟩ : syracuseStep 2014375 = 3021563) B3021563
theorem B2266177 : Blo 2013435 2266177 := bbase (se 2 (by rfl) ⟨849816, by rfl⟩ : syracuseStep 2266177 = 1699633) (by norm_num)
theorem B3021569 : Blo 2013435 3021569 := bstep (se 2 (by rfl) ⟨1133088, by rfl⟩ : syracuseStep 3021569 = 2266177) B2266177
theorem B2014379 : Blo 2013435 2014379 := bstep (se 1 (by rfl) ⟨1510784, by rfl⟩ : syracuseStep 2014379 = 3021569) B3021569
theorem B5098909 : Blo 2013435 5098909 := bbase (se 3 (by rfl) ⟨956045, by rfl⟩ : syracuseStep 5098909 = 1912091) (by norm_num)
theorem B6798545 : Blo 2013435 6798545 := bstep (se 2 (by rfl) ⟨2549454, by rfl⟩ : syracuseStep 6798545 = 5098909) B5098909
theorem B4532363 : Blo 2013435 4532363 := bstep (se 1 (by rfl) ⟨3399272, by rfl⟩ : syracuseStep 4532363 = 6798545) B6798545
theorem B3021575 : Blo 2013435 3021575 := bstep (se 1 (by rfl) ⟨2266181, by rfl⟩ : syracuseStep 3021575 = 4532363) B4532363
theorem B2014383 : Blo 2013435 2014383 := bstep (se 1 (by rfl) ⟨1510787, by rfl⟩ : syracuseStep 2014383 = 3021575) B3021575
theorem B3021581 : Blo 2013435 3021581 := bbase (se 3 (by rfl) ⟨566546, by rfl⟩ : syracuseStep 3021581 = 1133093) (by norm_num)
theorem B2014387 : Blo 2013435 2014387 := bstep (se 1 (by rfl) ⟨1510790, by rfl⟩ : syracuseStep 2014387 = 3021581) B3021581
theorem B4532381 : Blo 2013435 4532381 := bbase (se 3 (by rfl) ⟨849821, by rfl⟩ : syracuseStep 4532381 = 1699643) (by norm_num)
theorem B3021587 : Blo 2013435 3021587 := bstep (se 1 (by rfl) ⟨2266190, by rfl⟩ : syracuseStep 3021587 = 4532381) B4532381
theorem B2014391 : Blo 2013435 2014391 := bstep (se 1 (by rfl) ⟨1510793, by rfl⟩ : syracuseStep 2014391 = 3021587) B3021587
theorem B3399293 : Blo 2013435 3399293 := bbase (se 3 (by rfl) ⟨637367, by rfl⟩ : syracuseStep 3399293 = 1274735) (by norm_num)
theorem B2266195 : Blo 2013435 2266195 := bstep (se 1 (by rfl) ⟨1699646, by rfl⟩ : syracuseStep 2266195 = 3399293) B3399293
theorem B3021593 : Blo 2013435 3021593 := bstep (se 2 (by rfl) ⟨1133097, by rfl⟩ : syracuseStep 3021593 = 2266195) B2266195
theorem B2014395 : Blo 2013435 2014395 := bstep (se 1 (by rfl) ⟨1510796, by rfl⟩ : syracuseStep 2014395 = 3021593) B3021593
theorem B6985381 : Blo 2013435 6985381 := bbase (se 4 (by rfl) ⟨654879, by rfl⟩ : syracuseStep 6985381 = 1309759) (by norm_num)
theorem B9313841 : Blo 2013435 9313841 := bstep (se 2 (by rfl) ⟨3492690, by rfl⟩ : syracuseStep 9313841 = 6985381) B6985381
theorem B6209227 : Blo 2013435 6209227 := bstep (se 1 (by rfl) ⟨4656920, by rfl⟩ : syracuseStep 6209227 = 9313841) B9313841
theorem B8278969 : Blo 2013435 8278969 := bstep (se 2 (by rfl) ⟨3104613, by rfl⟩ : syracuseStep 8278969 = 6209227) B6209227
theorem B11038625 : Blo 2013435 11038625 := bstep (se 2 (by rfl) ⟨4139484, by rfl⟩ : syracuseStep 11038625 = 8278969) B8278969
theorem B7359083 : Blo 2013435 7359083 := bstep (se 1 (by rfl) ⟨5519312, by rfl⟩ : syracuseStep 7359083 = 11038625) B11038625
theorem B4906055 : Blo 2013435 4906055 := bstep (se 1 (by rfl) ⟨3679541, by rfl⟩ : syracuseStep 4906055 = 7359083) B7359083
theorem B3270703 : Blo 2013435 3270703 := bstep (se 1 (by rfl) ⟨2453027, by rfl⟩ : syracuseStep 3270703 = 4906055) B4906055
theorem B4360937 : Blo 2013435 4360937 := bstep (se 2 (by rfl) ⟨1635351, by rfl⟩ : syracuseStep 4360937 = 3270703) B3270703
theorem B11629165 : Blo 2013435 11629165 := bstep (se 3 (by rfl) ⟨2180468, by rfl⟩ : syracuseStep 11629165 = 4360937) B4360937
theorem B15505553 : Blo 2013435 15505553 := bstep (se 2 (by rfl) ⟨5814582, by rfl⟩ : syracuseStep 15505553 = 11629165) B11629165
theorem B41348141 : Blo 2013435 41348141 := bstep (se 3 (by rfl) ⟨7752776, by rfl⟩ : syracuseStep 41348141 = 15505553) B15505553
theorem B27565427 : Blo 2013435 27565427 := bstep (se 1 (by rfl) ⟨20674070, by rfl⟩ : syracuseStep 27565427 = 41348141) B41348141
theorem B18376951 : Blo 2013435 18376951 := bstep (se 1 (by rfl) ⟨13782713, by rfl⟩ : syracuseStep 18376951 = 27565427) B27565427
theorem B24502601 : Blo 2013435 24502601 := bstep (se 2 (by rfl) ⟨9188475, by rfl⟩ : syracuseStep 24502601 = 18376951) B18376951
theorem B16335067 : Blo 2013435 16335067 := bstep (se 1 (by rfl) ⟨12251300, by rfl⟩ : syracuseStep 16335067 = 24502601) B24502601
theorem B21780089 : Blo 2013435 21780089 := bstep (se 2 (by rfl) ⟨8167533, by rfl⟩ : syracuseStep 21780089 = 16335067) B16335067
theorem B14520059 : Blo 2013435 14520059 := bstep (se 1 (by rfl) ⟨10890044, by rfl⟩ : syracuseStep 14520059 = 21780089) B21780089
theorem B9680039 : Blo 2013435 9680039 := bstep (se 1 (by rfl) ⟨7260029, by rfl⟩ : syracuseStep 9680039 = 14520059) B14520059
theorem B6453359 : Blo 2013435 6453359 := bstep (se 1 (by rfl) ⟨4840019, by rfl⟩ : syracuseStep 6453359 = 9680039) B9680039
theorem B4302239 : Blo 2013435 4302239 := bstep (se 1 (by rfl) ⟨3226679, by rfl⟩ : syracuseStep 4302239 = 6453359) B6453359
theorem B11472637 : Blo 2013435 11472637 := bstep (se 3 (by rfl) ⟨2151119, by rfl⟩ : syracuseStep 11472637 = 4302239) B4302239
theorem B15296849 : Blo 2013435 15296849 := bstep (se 2 (by rfl) ⟨5736318, by rfl⟩ : syracuseStep 15296849 = 11472637) B11472637
theorem B10197899 : Blo 2013435 10197899 := bstep (se 1 (by rfl) ⟨7648424, by rfl⟩ : syracuseStep 10197899 = 15296849) B15296849
theorem B6798599 : Blo 2013435 6798599 := bstep (se 1 (by rfl) ⟨5098949, by rfl⟩ : syracuseStep 6798599 = 10197899) B10197899
theorem B4532399 : Blo 2013435 4532399 := bstep (se 1 (by rfl) ⟨3399299, by rfl⟩ : syracuseStep 4532399 = 6798599) B6798599
theorem B3021599 : Blo 2013435 3021599 := bstep (se 1 (by rfl) ⟨2266199, by rfl⟩ : syracuseStep 3021599 = 4532399) B4532399
theorem B2014399 : Blo 2013435 2014399 := bstep (se 1 (by rfl) ⟨1510799, by rfl⟩ : syracuseStep 2014399 = 3021599) B3021599
theorem B3021605 : Blo 2013435 3021605 := bbase (se 4 (by rfl) ⟨283275, by rfl⟩ : syracuseStep 3021605 = 566551) (by norm_num)
theorem B2014403 : Blo 2013435 2014403 := bstep (se 1 (by rfl) ⟨1510802, by rfl⟩ : syracuseStep 2014403 = 3021605) B3021605
theorem B2549485 : Blo 2013435 2549485 := bbase (se 3 (by rfl) ⟨478028, by rfl⟩ : syracuseStep 2549485 = 956057) (by norm_num)
theorem B3399313 : Blo 2013435 3399313 := bstep (se 2 (by rfl) ⟨1274742, by rfl⟩ : syracuseStep 3399313 = 2549485) B2549485
theorem B4532417 : Blo 2013435 4532417 := bstep (se 2 (by rfl) ⟨1699656, by rfl⟩ : syracuseStep 4532417 = 3399313) B3399313
theorem B3021611 : Blo 2013435 3021611 := bstep (se 1 (by rfl) ⟨2266208, by rfl⟩ : syracuseStep 3021611 = 4532417) B4532417
theorem B2014407 : Blo 2013435 2014407 := bstep (se 1 (by rfl) ⟨1510805, by rfl⟩ : syracuseStep 2014407 = 3021611) B3021611
theorem B2266213 : Blo 2013435 2266213 := bbase (se 4 (by rfl) ⟨212457, by rfl⟩ : syracuseStep 2266213 = 424915) (by norm_num)
theorem B3021617 : Blo 2013435 3021617 := bstep (se 2 (by rfl) ⟨1133106, by rfl⟩ : syracuseStep 3021617 = 2266213) B2266213
theorem B2014411 : Blo 2013435 2014411 := bstep (se 1 (by rfl) ⟨1510808, by rfl⟩ : syracuseStep 2014411 = 3021617) B3021617
theorem B2151137 : Blo 2013435 2151137 := bbase (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) (by norm_num)
theorem B5736365 : Blo 2013435 5736365 := bstep (se 3 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 5736365 = 2151137) B2151137
theorem B3824243 : Blo 2013435 3824243 := bstep (se 1 (by rfl) ⟨2868182, by rfl⟩ : syracuseStep 3824243 = 5736365) B5736365
theorem B2549495 : Blo 2013435 2549495 := bstep (se 1 (by rfl) ⟨1912121, by rfl⟩ : syracuseStep 2549495 = 3824243) B3824243
theorem B6798653 : Blo 2013435 6798653 := bstep (se 3 (by rfl) ⟨1274747, by rfl⟩ : syracuseStep 6798653 = 2549495) B2549495
theorem B4532435 : Blo 2013435 4532435 := bstep (se 1 (by rfl) ⟨3399326, by rfl⟩ : syracuseStep 4532435 = 6798653) B6798653
theorem B3021623 : Blo 2013435 3021623 := bstep (se 1 (by rfl) ⟨2266217, by rfl⟩ : syracuseStep 3021623 = 4532435) B4532435
theorem B2014415 : Blo 2013435 2014415 := bstep (se 1 (by rfl) ⟨1510811, by rfl⟩ : syracuseStep 2014415 = 3021623) B3021623
theorem B3021629 : Blo 2013435 3021629 := bbase (se 3 (by rfl) ⟨566555, by rfl⟩ : syracuseStep 3021629 = 1133111) (by norm_num)
theorem B2014419 : Blo 2013435 2014419 := bstep (se 1 (by rfl) ⟨1510814, by rfl⟩ : syracuseStep 2014419 = 3021629) B3021629
theorem B4532453 : Blo 2013435 4532453 := bbase (se 4 (by rfl) ⟨424917, by rfl⟩ : syracuseStep 4532453 = 849835) (by norm_num)
theorem B3021635 : Blo 2013435 3021635 := bstep (se 1 (by rfl) ⟨2266226, by rfl⟩ : syracuseStep 3021635 = 4532453) B4532453
theorem B2014423 : Blo 2013435 2014423 := bstep (se 1 (by rfl) ⟨1510817, by rfl⟩ : syracuseStep 2014423 = 3021635) B3021635
theorem B5099021 : Blo 2013435 5099021 := bbase (se 3 (by rfl) ⟨956066, by rfl⟩ : syracuseStep 5099021 = 1912133) (by norm_num)
theorem B3399347 : Blo 2013435 3399347 := bstep (se 1 (by rfl) ⟨2549510, by rfl⟩ : syracuseStep 3399347 = 5099021) B5099021
theorem B2266231 : Blo 2013435 2266231 := bstep (se 1 (by rfl) ⟨1699673, by rfl⟩ : syracuseStep 2266231 = 3399347) B3399347
theorem B3021641 : Blo 2013435 3021641 := bstep (se 2 (by rfl) ⟨1133115, by rfl⟩ : syracuseStep 3021641 = 2266231) B2266231
theorem B2014427 : Blo 2013435 2014427 := bstep (se 1 (by rfl) ⟨1510820, by rfl⟩ : syracuseStep 2014427 = 3021641) B3021641
theorem B2868205 : Blo 2013435 2868205 := bbase (se 3 (by rfl) ⟨537788, by rfl⟩ : syracuseStep 2868205 = 1075577) (by norm_num)
theorem B3824273 : Blo 2013435 3824273 := bstep (se 2 (by rfl) ⟨1434102, by rfl⟩ : syracuseStep 3824273 = 2868205) B2868205
theorem B10198061 : Blo 2013435 10198061 := bstep (se 3 (by rfl) ⟨1912136, by rfl⟩ : syracuseStep 10198061 = 3824273) B3824273
theorem B6798707 : Blo 2013435 6798707 := bstep (se 1 (by rfl) ⟨5099030, by rfl⟩ : syracuseStep 6798707 = 10198061) B10198061
theorem B4532471 : Blo 2013435 4532471 := bstep (se 1 (by rfl) ⟨3399353, by rfl⟩ : syracuseStep 4532471 = 6798707) B6798707
theorem B3021647 : Blo 2013435 3021647 := bstep (se 1 (by rfl) ⟨2266235, by rfl⟩ : syracuseStep 3021647 = 4532471) B4532471
theorem B2014431 : Blo 2013435 2014431 := bstep (se 1 (by rfl) ⟨1510823, by rfl⟩ : syracuseStep 2014431 = 3021647) B3021647
theorem B3021653 : Blo 2013435 3021653 := bbase (se 9 (by rfl) ⟨8852, by rfl⟩ : syracuseStep 3021653 = 17705) (by norm_num)
theorem B2014435 : Blo 2013435 2014435 := bstep (se 1 (by rfl) ⟨1510826, by rfl⟩ : syracuseStep 2014435 = 3021653) B3021653
theorem B4302325 : Blo 2013435 4302325 := bbase (se 5 (by rfl) ⟨201671, by rfl⟩ : syracuseStep 4302325 = 403343) (by norm_num)
theorem B5736433 : Blo 2013435 5736433 := bstep (se 2 (by rfl) ⟨2151162, by rfl⟩ : syracuseStep 5736433 = 4302325) B4302325
theorem B7648577 : Blo 2013435 7648577 := bstep (se 2 (by rfl) ⟨2868216, by rfl⟩ : syracuseStep 7648577 = 5736433) B5736433
theorem B5099051 : Blo 2013435 5099051 := bstep (se 1 (by rfl) ⟨3824288, by rfl⟩ : syracuseStep 5099051 = 7648577) B7648577
theorem B3399367 : Blo 2013435 3399367 := bstep (se 1 (by rfl) ⟨2549525, by rfl⟩ : syracuseStep 3399367 = 5099051) B5099051
theorem B4532489 : Blo 2013435 4532489 := bstep (se 2 (by rfl) ⟨1699683, by rfl⟩ : syracuseStep 4532489 = 3399367) B3399367
theorem B3021659 : Blo 2013435 3021659 := bstep (se 1 (by rfl) ⟨2266244, by rfl⟩ : syracuseStep 3021659 = 4532489) B4532489
theorem B2014439 : Blo 2013435 2014439 := bstep (se 1 (by rfl) ⟨1510829, by rfl⟩ : syracuseStep 2014439 = 3021659) B3021659
theorem B2266249 : Blo 2013435 2266249 := bbase (se 2 (by rfl) ⟨849843, by rfl⟩ : syracuseStep 2266249 = 1699687) (by norm_num)
theorem B3021665 : Blo 2013435 3021665 := bstep (se 2 (by rfl) ⟨1133124, by rfl⟩ : syracuseStep 3021665 = 2266249) B2266249
theorem B2014443 : Blo 2013435 2014443 := bstep (se 1 (by rfl) ⟨1510832, by rfl⟩ : syracuseStep 2014443 = 3021665) B3021665
theorem B3630101 : Blo 2013435 3630101 := bbase (se 6 (by rfl) ⟨85080, by rfl⟩ : syracuseStep 3630101 = 170161) (by norm_num)
theorem B38721077 : Blo 2013435 38721077 := bstep (se 5 (by rfl) ⟨1815050, by rfl⟩ : syracuseStep 38721077 = 3630101) B3630101
theorem B25814051 : Blo 2013435 25814051 := bstep (se 1 (by rfl) ⟨19360538, by rfl⟩ : syracuseStep 25814051 = 38721077) B38721077
theorem B17209367 : Blo 2013435 17209367 := bstep (se 1 (by rfl) ⟨12907025, by rfl⟩ : syracuseStep 17209367 = 25814051) B25814051
theorem B11472911 : Blo 2013435 11472911 := bstep (se 1 (by rfl) ⟨8604683, by rfl⟩ : syracuseStep 11472911 = 17209367) B17209367
theorem B7648607 : Blo 2013435 7648607 := bstep (se 1 (by rfl) ⟨5736455, by rfl⟩ : syracuseStep 7648607 = 11472911) B11472911
theorem B5099071 : Blo 2013435 5099071 := bstep (se 1 (by rfl) ⟨3824303, by rfl⟩ : syracuseStep 5099071 = 7648607) B7648607
theorem B6798761 : Blo 2013435 6798761 := bstep (se 2 (by rfl) ⟨2549535, by rfl⟩ : syracuseStep 6798761 = 5099071) B5099071
theorem B4532507 : Blo 2013435 4532507 := bstep (se 1 (by rfl) ⟨3399380, by rfl⟩ : syracuseStep 4532507 = 6798761) B6798761
theorem B3021671 : Blo 2013435 3021671 := bstep (se 1 (by rfl) ⟨2266253, by rfl⟩ : syracuseStep 3021671 = 4532507) B4532507
theorem B2014447 : Blo 2013435 2014447 := bstep (se 1 (by rfl) ⟨1510835, by rfl⟩ : syracuseStep 2014447 = 3021671) B3021671
theorem B3021677 : Blo 2013435 3021677 := bbase (se 3 (by rfl) ⟨566564, by rfl⟩ : syracuseStep 3021677 = 1133129) (by norm_num)
theorem B2014451 : Blo 2013435 2014451 := bstep (se 1 (by rfl) ⟨1510838, by rfl⟩ : syracuseStep 2014451 = 3021677) B3021677
theorem B4532525 : Blo 2013435 4532525 := bbase (se 3 (by rfl) ⟨849848, by rfl⟩ : syracuseStep 4532525 = 1699697) (by norm_num)
theorem B3021683 : Blo 2013435 3021683 := bstep (se 1 (by rfl) ⟨2266262, by rfl⟩ : syracuseStep 3021683 = 4532525) B4532525
theorem B2014455 : Blo 2013435 2014455 := bstep (se 1 (by rfl) ⟨1510841, by rfl⟩ : syracuseStep 2014455 = 3021683) B3021683
theorem B4840165 : Blo 2013435 4840165 := bbase (se 4 (by rfl) ⟨453765, by rfl⟩ : syracuseStep 4840165 = 907531) (by norm_num)
theorem B6453553 : Blo 2013435 6453553 := bstep (se 2 (by rfl) ⟨2420082, by rfl⟩ : syracuseStep 6453553 = 4840165) B4840165
theorem B8604737 : Blo 2013435 8604737 := bstep (se 2 (by rfl) ⟨3226776, by rfl⟩ : syracuseStep 8604737 = 6453553) B6453553
theorem B5736491 : Blo 2013435 5736491 := bstep (se 1 (by rfl) ⟨4302368, by rfl⟩ : syracuseStep 5736491 = 8604737) B8604737
theorem B3824327 : Blo 2013435 3824327 := bstep (se 1 (by rfl) ⟨2868245, by rfl⟩ : syracuseStep 3824327 = 5736491) B5736491
theorem B2549551 : Blo 2013435 2549551 := bstep (se 1 (by rfl) ⟨1912163, by rfl⟩ : syracuseStep 2549551 = 3824327) B3824327
theorem B3399401 : Blo 2013435 3399401 := bstep (se 2 (by rfl) ⟨1274775, by rfl⟩ : syracuseStep 3399401 = 2549551) B2549551
theorem B2266267 : Blo 2013435 2266267 := bstep (se 1 (by rfl) ⟨1699700, by rfl⟩ : syracuseStep 2266267 = 3399401) B3399401
theorem B3021689 : Blo 2013435 3021689 := bstep (se 2 (by rfl) ⟨1133133, by rfl⟩ : syracuseStep 3021689 = 2266267) B2266267
theorem B2014459 : Blo 2013435 2014459 := bstep (se 1 (by rfl) ⟨1510844, by rfl⟩ : syracuseStep 2014459 = 3021689) B3021689
theorem B10890389 : Blo 2013435 10890389 := bbase (se 6 (by rfl) ⟨255243, by rfl⟩ : syracuseStep 10890389 = 510487) (by norm_num)
theorem B29041037 : Blo 2013435 29041037 := bstep (se 3 (by rfl) ⟨5445194, by rfl⟩ : syracuseStep 29041037 = 10890389) B10890389
theorem B19360691 : Blo 2013435 19360691 := bstep (se 1 (by rfl) ⟨14520518, by rfl⟩ : syracuseStep 19360691 = 29041037) B29041037
theorem B12907127 : Blo 2013435 12907127 := bstep (se 1 (by rfl) ⟨9680345, by rfl⟩ : syracuseStep 12907127 = 19360691) B19360691
theorem B34419005 : Blo 2013435 34419005 := bstep (se 3 (by rfl) ⟨6453563, by rfl⟩ : syracuseStep 34419005 = 12907127) B12907127
theorem B22946003 : Blo 2013435 22946003 := bstep (se 1 (by rfl) ⟨17209502, by rfl⟩ : syracuseStep 22946003 = 34419005) B34419005
theorem B15297335 : Blo 2013435 15297335 := bstep (se 1 (by rfl) ⟨11473001, by rfl⟩ : syracuseStep 15297335 = 22946003) B22946003
theorem B10198223 : Blo 2013435 10198223 := bstep (se 1 (by rfl) ⟨7648667, by rfl⟩ : syracuseStep 10198223 = 15297335) B15297335
theorem B6798815 : Blo 2013435 6798815 := bstep (se 1 (by rfl) ⟨5099111, by rfl⟩ : syracuseStep 6798815 = 10198223) B10198223
theorem B4532543 : Blo 2013435 4532543 := bstep (se 1 (by rfl) ⟨3399407, by rfl⟩ : syracuseStep 4532543 = 6798815) B6798815
theorem B3021695 : Blo 2013435 3021695 := bstep (se 1 (by rfl) ⟨2266271, by rfl⟩ : syracuseStep 3021695 = 4532543) B4532543
theorem B2014463 : Blo 2013435 2014463 := bstep (se 1 (by rfl) ⟨1510847, by rfl⟩ : syracuseStep 2014463 = 3021695) B3021695
theorem B3021701 : Blo 2013435 3021701 := bbase (se 4 (by rfl) ⟨283284, by rfl⟩ : syracuseStep 3021701 = 566569) (by norm_num)
theorem B2014467 : Blo 2013435 2014467 := bstep (se 1 (by rfl) ⟨1510850, by rfl⟩ : syracuseStep 2014467 = 3021701) B3021701
theorem B3399421 : Blo 2013435 3399421 := bbase (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) (by norm_num)
theorem B4532561 : Blo 2013435 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B3021707 : Blo 2013435 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B2014471 : Blo 2013435 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B2266285 : Blo 2013435 2266285 := bbase (se 3 (by rfl) ⟨424928, by rfl⟩ : syracuseStep 2266285 = 849857) (by norm_num)
theorem B3021713 : Blo 2013435 3021713 := bstep (se 2 (by rfl) ⟨1133142, by rfl⟩ : syracuseStep 3021713 = 2266285) B2266285
theorem B2014475 : Blo 2013435 2014475 := bstep (se 1 (by rfl) ⟨1510856, by rfl⟩ : syracuseStep 2014475 = 3021713) B3021713
theorem B6798869 : Blo 2013435 6798869 := bbase (se 6 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 6798869 = 318697) (by norm_num)
theorem B4532579 : Blo 2013435 4532579 := bstep (se 1 (by rfl) ⟨3399434, by rfl⟩ : syracuseStep 4532579 = 6798869) B6798869
theorem B3021719 : Blo 2013435 3021719 := bstep (se 1 (by rfl) ⟨2266289, by rfl⟩ : syracuseStep 3021719 = 4532579) B4532579
theorem B2014479 : Blo 2013435 2014479 := bstep (se 1 (by rfl) ⟨1510859, by rfl⟩ : syracuseStep 2014479 = 3021719) B3021719
theorem B3021725 : Blo 2013435 3021725 := bbase (se 3 (by rfl) ⟨566573, by rfl⟩ : syracuseStep 3021725 = 1133147) (by norm_num)
theorem B2014483 : Blo 2013435 2014483 := bstep (se 1 (by rfl) ⟨1510862, by rfl⟩ : syracuseStep 2014483 = 3021725) B3021725
theorem B4532597 : Blo 2013435 4532597 := bbase (se 5 (by rfl) ⟨212465, by rfl⟩ : syracuseStep 4532597 = 424931) (by norm_num)
theorem B3021731 : Blo 2013435 3021731 := bstep (se 1 (by rfl) ⟨2266298, by rfl⟩ : syracuseStep 3021731 = 4532597) B4532597
theorem B2014487 : Blo 2013435 2014487 := bstep (se 1 (by rfl) ⟨1510865, by rfl⟩ : syracuseStep 2014487 = 3021731) B3021731
theorem B3630181 : Blo 2013435 3630181 := bbase (se 4 (by rfl) ⟨340329, by rfl⟩ : syracuseStep 3630181 = 680659) (by norm_num)
theorem B4840241 : Blo 2013435 4840241 := bstep (se 2 (by rfl) ⟨1815090, by rfl⟩ : syracuseStep 4840241 = 3630181) B3630181
theorem B12907309 : Blo 2013435 12907309 := bstep (se 3 (by rfl) ⟨2420120, by rfl⟩ : syracuseStep 12907309 = 4840241) B4840241
theorem B17209745 : Blo 2013435 17209745 := bstep (se 2 (by rfl) ⟨6453654, by rfl⟩ : syracuseStep 17209745 = 12907309) B12907309
theorem B11473163 : Blo 2013435 11473163 := bstep (se 1 (by rfl) ⟨8604872, by rfl⟩ : syracuseStep 11473163 = 17209745) B17209745
theorem B7648775 : Blo 2013435 7648775 := bstep (se 1 (by rfl) ⟨5736581, by rfl⟩ : syracuseStep 7648775 = 11473163) B11473163
theorem B5099183 : Blo 2013435 5099183 := bstep (se 1 (by rfl) ⟨3824387, by rfl⟩ : syracuseStep 5099183 = 7648775) B7648775
theorem B3399455 : Blo 2013435 3399455 := bstep (se 1 (by rfl) ⟨2549591, by rfl⟩ : syracuseStep 3399455 = 5099183) B5099183
theorem B2266303 : Blo 2013435 2266303 := bstep (se 1 (by rfl) ⟨1699727, by rfl⟩ : syracuseStep 2266303 = 3399455) B3399455
theorem B3021737 : Blo 2013435 3021737 := bstep (se 2 (by rfl) ⟨1133151, by rfl⟩ : syracuseStep 3021737 = 2266303) B2266303
theorem B2014491 : Blo 2013435 2014491 := bstep (se 1 (by rfl) ⟨1510868, by rfl⟩ : syracuseStep 2014491 = 3021737) B3021737
theorem B7648789 : Blo 2013435 7648789 := bbase (se 6 (by rfl) ⟨179268, by rfl⟩ : syracuseStep 7648789 = 358537) (by norm_num)
theorem B10198385 : Blo 2013435 10198385 := bstep (se 2 (by rfl) ⟨3824394, by rfl⟩ : syracuseStep 10198385 = 7648789) B7648789
theorem B6798923 : Blo 2013435 6798923 := bstep (se 1 (by rfl) ⟨5099192, by rfl⟩ : syracuseStep 6798923 = 10198385) B10198385
theorem B4532615 : Blo 2013435 4532615 := bstep (se 1 (by rfl) ⟨3399461, by rfl⟩ : syracuseStep 4532615 = 6798923) B6798923
theorem B3021743 : Blo 2013435 3021743 := bstep (se 1 (by rfl) ⟨2266307, by rfl⟩ : syracuseStep 3021743 = 4532615) B4532615
theorem B2014495 : Blo 2013435 2014495 := bstep (se 1 (by rfl) ⟨1510871, by rfl⟩ : syracuseStep 2014495 = 3021743) B3021743
theorem B3021749 : Blo 2013435 3021749 := bbase (se 5 (by rfl) ⟨141644, by rfl⟩ : syracuseStep 3021749 = 283289) (by norm_num)
theorem B2014499 : Blo 2013435 2014499 := bstep (se 1 (by rfl) ⟨1510874, by rfl⟩ : syracuseStep 2014499 = 3021749) B3021749
theorem B5099213 : Blo 2013435 5099213 := bbase (se 3 (by rfl) ⟨956102, by rfl⟩ : syracuseStep 5099213 = 1912205) (by norm_num)
theorem B3399475 : Blo 2013435 3399475 := bstep (se 1 (by rfl) ⟨2549606, by rfl⟩ : syracuseStep 3399475 = 5099213) B5099213
theorem B4532633 : Blo 2013435 4532633 := bstep (se 2 (by rfl) ⟨1699737, by rfl⟩ : syracuseStep 4532633 = 3399475) B3399475
theorem B3021755 : Blo 2013435 3021755 := bstep (se 1 (by rfl) ⟨2266316, by rfl⟩ : syracuseStep 3021755 = 4532633) B4532633
theorem B2014503 : Blo 2013435 2014503 := bstep (se 1 (by rfl) ⟨1510877, by rfl⟩ : syracuseStep 2014503 = 3021755) B3021755
theorem B2266321 : Blo 2013435 2266321 := bbase (se 2 (by rfl) ⟨849870, by rfl⟩ : syracuseStep 2266321 = 1699741) (by norm_num)
theorem B3021761 : Blo 2013435 3021761 := bstep (se 2 (by rfl) ⟨1133160, by rfl⟩ : syracuseStep 3021761 = 2266321) B2266321
theorem B2014507 : Blo 2013435 2014507 := bstep (se 1 (by rfl) ⟨1510880, by rfl⟩ : syracuseStep 2014507 = 3021761) B3021761
theorem B5519621 : Blo 2013435 5519621 := bbase (se 4 (by rfl) ⟨517464, by rfl⟩ : syracuseStep 5519621 = 1034929) (by norm_num)
theorem B14718989 : Blo 2013435 14718989 := bstep (se 3 (by rfl) ⟨2759810, by rfl⟩ : syracuseStep 14718989 = 5519621) B5519621
theorem B9812659 : Blo 2013435 9812659 := bstep (se 1 (by rfl) ⟨7359494, by rfl⟩ : syracuseStep 9812659 = 14718989) B14718989
theorem B13083545 : Blo 2013435 13083545 := bstep (se 2 (by rfl) ⟨4906329, by rfl⟩ : syracuseStep 13083545 = 9812659) B9812659
theorem B34889453 : Blo 2013435 34889453 := bstep (se 3 (by rfl) ⟨6541772, by rfl⟩ : syracuseStep 34889453 = 13083545) B13083545
theorem B23259635 : Blo 2013435 23259635 := bstep (se 1 (by rfl) ⟨17444726, by rfl⟩ : syracuseStep 23259635 = 34889453) B34889453
theorem B15506423 : Blo 2013435 15506423 := bstep (se 1 (by rfl) ⟨11629817, by rfl⟩ : syracuseStep 15506423 = 23259635) B23259635
theorem B10337615 : Blo 2013435 10337615 := bstep (se 1 (by rfl) ⟨7753211, by rfl⟩ : syracuseStep 10337615 = 15506423) B15506423
theorem B6891743 : Blo 2013435 6891743 := bstep (se 1 (by rfl) ⟨5168807, by rfl⟩ : syracuseStep 6891743 = 10337615) B10337615
theorem B4594495 : Blo 2013435 4594495 := bstep (se 1 (by rfl) ⟨3445871, by rfl⟩ : syracuseStep 4594495 = 6891743) B6891743
theorem B6125993 : Blo 2013435 6125993 := bstep (se 2 (by rfl) ⟨2297247, by rfl⟩ : syracuseStep 6125993 = 4594495) B4594495
theorem B4083995 : Blo 2013435 4083995 := bstep (se 1 (by rfl) ⟨3062996, by rfl⟩ : syracuseStep 4083995 = 6125993) B6125993
theorem B2722663 : Blo 2013435 2722663 := bstep (se 1 (by rfl) ⟨2041997, by rfl⟩ : syracuseStep 2722663 = 4083995) B4083995
theorem B14520869 : Blo 2013435 14520869 := bstep (se 4 (by rfl) ⟨1361331, by rfl⟩ : syracuseStep 14520869 = 2722663) B2722663
theorem B9680579 : Blo 2013435 9680579 := bstep (se 1 (by rfl) ⟨7260434, by rfl⟩ : syracuseStep 9680579 = 14520869) B14520869
theorem B6453719 : Blo 2013435 6453719 := bstep (se 1 (by rfl) ⟨4840289, by rfl⟩ : syracuseStep 6453719 = 9680579) B9680579
theorem B4302479 : Blo 2013435 4302479 := bstep (se 1 (by rfl) ⟨3226859, by rfl⟩ : syracuseStep 4302479 = 6453719) B6453719
theorem B2868319 : Blo 2013435 2868319 := bstep (se 1 (by rfl) ⟨2151239, by rfl⟩ : syracuseStep 2868319 = 4302479) B4302479
theorem B3824425 : Blo 2013435 3824425 := bstep (se 2 (by rfl) ⟨1434159, by rfl⟩ : syracuseStep 3824425 = 2868319) B2868319
theorem B5099233 : Blo 2013435 5099233 := bstep (se 2 (by rfl) ⟨1912212, by rfl⟩ : syracuseStep 5099233 = 3824425) B3824425
theorem B6798977 : Blo 2013435 6798977 := bstep (se 2 (by rfl) ⟨2549616, by rfl⟩ : syracuseStep 6798977 = 5099233) B5099233
theorem B4532651 : Blo 2013435 4532651 := bstep (se 1 (by rfl) ⟨3399488, by rfl⟩ : syracuseStep 4532651 = 6798977) B6798977
theorem B3021767 : Blo 2013435 3021767 := bstep (se 1 (by rfl) ⟨2266325, by rfl⟩ : syracuseStep 3021767 = 4532651) B4532651
theorem B2014511 : Blo 2013435 2014511 := bstep (se 1 (by rfl) ⟨1510883, by rfl⟩ : syracuseStep 2014511 = 3021767) B3021767
theorem B3021773 : Blo 2013435 3021773 := bbase (se 3 (by rfl) ⟨566582, by rfl⟩ : syracuseStep 3021773 = 1133165) (by norm_num)
theorem B2014515 : Blo 2013435 2014515 := bstep (se 1 (by rfl) ⟨1510886, by rfl⟩ : syracuseStep 2014515 = 3021773) B3021773
theorem B4532669 : Blo 2013435 4532669 := bbase (se 3 (by rfl) ⟨849875, by rfl⟩ : syracuseStep 4532669 = 1699751) (by norm_num)
theorem B3021779 : Blo 2013435 3021779 := bstep (se 1 (by rfl) ⟨2266334, by rfl⟩ : syracuseStep 3021779 = 4532669) B4532669
theorem B2014519 : Blo 2013435 2014519 := bstep (se 1 (by rfl) ⟨1510889, by rfl⟩ : syracuseStep 2014519 = 3021779) B3021779
theorem B3399509 : Blo 2013435 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B2266339 : Blo 2013435 2266339 := bstep (se 1 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 2266339 = 3399509) B3399509
theorem B3021785 : Blo 2013435 3021785 := bstep (se 2 (by rfl) ⟨1133169, by rfl⟩ : syracuseStep 3021785 = 2266339) B2266339
theorem B2014523 : Blo 2013435 2014523 := bstep (se 1 (by rfl) ⟨1510892, by rfl⟩ : syracuseStep 2014523 = 3021785) B3021785
theorem B8168053 : Blo 2013435 8168053 := bbase (se 5 (by rfl) ⟨382877, by rfl⟩ : syracuseStep 8168053 = 765755) (by norm_num)
theorem B10890737 : Blo 2013435 10890737 := bstep (se 2 (by rfl) ⟨4084026, by rfl⟩ : syracuseStep 10890737 = 8168053) B8168053
theorem B7260491 : Blo 2013435 7260491 := bstep (se 1 (by rfl) ⟨5445368, by rfl⟩ : syracuseStep 7260491 = 10890737) B10890737
theorem B4840327 : Blo 2013435 4840327 := bstep (se 1 (by rfl) ⟨3630245, by rfl⟩ : syracuseStep 4840327 = 7260491) B7260491
theorem B6453769 : Blo 2013435 6453769 := bstep (se 2 (by rfl) ⟨2420163, by rfl⟩ : syracuseStep 6453769 = 4840327) B4840327
theorem B8605025 : Blo 2013435 8605025 := bstep (se 2 (by rfl) ⟨3226884, by rfl⟩ : syracuseStep 8605025 = 6453769) B6453769
theorem B5736683 : Blo 2013435 5736683 := bstep (se 1 (by rfl) ⟨4302512, by rfl⟩ : syracuseStep 5736683 = 8605025) B8605025
theorem B15297821 : Blo 2013435 15297821 := bstep (se 3 (by rfl) ⟨2868341, by rfl⟩ : syracuseStep 15297821 = 5736683) B5736683
theorem B10198547 : Blo 2013435 10198547 := bstep (se 1 (by rfl) ⟨7648910, by rfl⟩ : syracuseStep 10198547 = 15297821) B15297821
theorem B6799031 : Blo 2013435 6799031 := bstep (se 1 (by rfl) ⟨5099273, by rfl⟩ : syracuseStep 6799031 = 10198547) B10198547
theorem B4532687 : Blo 2013435 4532687 := bstep (se 1 (by rfl) ⟨3399515, by rfl⟩ : syracuseStep 4532687 = 6799031) B6799031
theorem B3021791 : Blo 2013435 3021791 := bstep (se 1 (by rfl) ⟨2266343, by rfl⟩ : syracuseStep 3021791 = 4532687) B4532687
theorem B2014527 : Blo 2013435 2014527 := bstep (se 1 (by rfl) ⟨1510895, by rfl⟩ : syracuseStep 2014527 = 3021791) B3021791
theorem B3021797 : Blo 2013435 3021797 := bbase (se 4 (by rfl) ⟨283293, by rfl⟩ : syracuseStep 3021797 = 566587) (by norm_num)
theorem B2014531 : Blo 2013435 2014531 := bstep (se 1 (by rfl) ⟨1510898, by rfl⟩ : syracuseStep 2014531 = 3021797) B3021797
theorem B8605061 : Blo 2013435 8605061 := bbase (se 4 (by rfl) ⟨806724, by rfl⟩ : syracuseStep 8605061 = 1613449) (by norm_num)
theorem B5736707 : Blo 2013435 5736707 := bstep (se 1 (by rfl) ⟨4302530, by rfl⟩ : syracuseStep 5736707 = 8605061) B8605061
theorem B3824471 : Blo 2013435 3824471 := bstep (se 1 (by rfl) ⟨2868353, by rfl⟩ : syracuseStep 3824471 = 5736707) B5736707
theorem B2549647 : Blo 2013435 2549647 := bstep (se 1 (by rfl) ⟨1912235, by rfl⟩ : syracuseStep 2549647 = 3824471) B3824471
theorem B3399529 : Blo 2013435 3399529 := bstep (se 2 (by rfl) ⟨1274823, by rfl⟩ : syracuseStep 3399529 = 2549647) B2549647
theorem B4532705 : Blo 2013435 4532705 := bstep (se 2 (by rfl) ⟨1699764, by rfl⟩ : syracuseStep 4532705 = 3399529) B3399529
theorem B3021803 : Blo 2013435 3021803 := bstep (se 1 (by rfl) ⟨2266352, by rfl⟩ : syracuseStep 3021803 = 4532705) B4532705
theorem B2014535 : Blo 2013435 2014535 := bstep (se 1 (by rfl) ⟨1510901, by rfl⟩ : syracuseStep 2014535 = 3021803) B3021803
theorem B2266357 : Blo 2013435 2266357 := bbase (se 5 (by rfl) ⟨106235, by rfl⟩ : syracuseStep 2266357 = 212471) (by norm_num)
theorem B3021809 : Blo 2013435 3021809 := bstep (se 2 (by rfl) ⟨1133178, by rfl⟩ : syracuseStep 3021809 = 2266357) B2266357
theorem B2014539 : Blo 2013435 2014539 := bstep (se 1 (by rfl) ⟨1510904, by rfl⟩ : syracuseStep 2014539 = 3021809) B3021809
theorem B2549657 : Blo 2013435 2549657 := bbase (se 2 (by rfl) ⟨956121, by rfl⟩ : syracuseStep 2549657 = 1912243) (by norm_num)
theorem B6799085 : Blo 2013435 6799085 := bstep (se 3 (by rfl) ⟨1274828, by rfl⟩ : syracuseStep 6799085 = 2549657) B2549657
theorem B4532723 : Blo 2013435 4532723 := bstep (se 1 (by rfl) ⟨3399542, by rfl⟩ : syracuseStep 4532723 = 6799085) B6799085
theorem B3021815 : Blo 2013435 3021815 := bstep (se 1 (by rfl) ⟨2266361, by rfl⟩ : syracuseStep 3021815 = 4532723) B4532723
theorem B2014543 : Blo 2013435 2014543 := bstep (se 1 (by rfl) ⟨1510907, by rfl⟩ : syracuseStep 2014543 = 3021815) B3021815
theorem B3021821 : Blo 2013435 3021821 := bbase (se 3 (by rfl) ⟨566591, by rfl⟩ : syracuseStep 3021821 = 1133183) (by norm_num)
theorem B2014547 : Blo 2013435 2014547 := bstep (se 1 (by rfl) ⟨1510910, by rfl⟩ : syracuseStep 2014547 = 3021821) B3021821
theorem B4532741 : Blo 2013435 4532741 := bbase (se 4 (by rfl) ⟨424944, by rfl⟩ : syracuseStep 4532741 = 849889) (by norm_num)
theorem B3021827 : Blo 2013435 3021827 := bstep (se 1 (by rfl) ⟨2266370, by rfl⟩ : syracuseStep 3021827 = 4532741) B4532741
theorem B2014551 : Blo 2013435 2014551 := bstep (se 1 (by rfl) ⟨1510913, by rfl⟩ : syracuseStep 2014551 = 3021827) B3021827
theorem B3824509 : Blo 2013435 3824509 := bbase (se 3 (by rfl) ⟨717095, by rfl⟩ : syracuseStep 3824509 = 1434191) (by norm_num)
theorem B5099345 : Blo 2013435 5099345 := bstep (se 2 (by rfl) ⟨1912254, by rfl⟩ : syracuseStep 5099345 = 3824509) B3824509
theorem B3399563 : Blo 2013435 3399563 := bstep (se 1 (by rfl) ⟨2549672, by rfl⟩ : syracuseStep 3399563 = 5099345) B5099345
theorem B2266375 : Blo 2013435 2266375 := bstep (se 1 (by rfl) ⟨1699781, by rfl⟩ : syracuseStep 2266375 = 3399563) B3399563
theorem B3021833 : Blo 2013435 3021833 := bstep (se 2 (by rfl) ⟨1133187, by rfl⟩ : syracuseStep 3021833 = 2266375) B2266375
theorem B2014555 : Blo 2013435 2014555 := bstep (se 1 (by rfl) ⟨1510916, by rfl⟩ : syracuseStep 2014555 = 3021833) B3021833
theorem B10198709 : Blo 2013435 10198709 := bbase (se 5 (by rfl) ⟨478064, by rfl⟩ : syracuseStep 10198709 = 956129) (by norm_num)
theorem B6799139 : Blo 2013435 6799139 := bstep (se 1 (by rfl) ⟨5099354, by rfl⟩ : syracuseStep 6799139 = 10198709) B10198709
theorem B4532759 : Blo 2013435 4532759 := bstep (se 1 (by rfl) ⟨3399569, by rfl⟩ : syracuseStep 4532759 = 6799139) B6799139
theorem B3021839 : Blo 2013435 3021839 := bstep (se 1 (by rfl) ⟨2266379, by rfl⟩ : syracuseStep 3021839 = 4532759) B4532759
theorem B2014559 : Blo 2013435 2014559 := bstep (se 1 (by rfl) ⟨1510919, by rfl⟩ : syracuseStep 2014559 = 3021839) B3021839
theorem B3021845 : Blo 2013435 3021845 := bbase (se 6 (by rfl) ⟨70824, by rfl⟩ : syracuseStep 3021845 = 141649) (by norm_num)
theorem B2014563 : Blo 2013435 2014563 := bstep (se 1 (by rfl) ⟨1510922, by rfl⟩ : syracuseStep 2014563 = 3021845) B3021845
theorem B18378485 : Blo 2013435 18378485 := bbase (se 5 (by rfl) ⟨861491, by rfl⟩ : syracuseStep 18378485 = 1722983) (by norm_num)
theorem B12252323 : Blo 2013435 12252323 := bstep (se 1 (by rfl) ⟨9189242, by rfl⟩ : syracuseStep 12252323 = 18378485) B18378485
theorem B8168215 : Blo 2013435 8168215 := bstep (se 1 (by rfl) ⟨6126161, by rfl⟩ : syracuseStep 8168215 = 12252323) B12252323
theorem B10890953 : Blo 2013435 10890953 := bstep (se 2 (by rfl) ⟨4084107, by rfl⟩ : syracuseStep 10890953 = 8168215) B8168215
theorem B7260635 : Blo 2013435 7260635 := bstep (se 1 (by rfl) ⟨5445476, by rfl⟩ : syracuseStep 7260635 = 10890953) B10890953
theorem B19361693 : Blo 2013435 19361693 := bstep (se 3 (by rfl) ⟨3630317, by rfl⟩ : syracuseStep 19361693 = 7260635) B7260635
theorem B12907795 : Blo 2013435 12907795 := bstep (se 1 (by rfl) ⟨9680846, by rfl⟩ : syracuseStep 12907795 = 19361693) B19361693
theorem B17210393 : Blo 2013435 17210393 := bstep (se 2 (by rfl) ⟨6453897, by rfl⟩ : syracuseStep 17210393 = 12907795) B12907795
theorem B11473595 : Blo 2013435 11473595 := bstep (se 1 (by rfl) ⟨8605196, by rfl⟩ : syracuseStep 11473595 = 17210393) B17210393
theorem B7649063 : Blo 2013435 7649063 := bstep (se 1 (by rfl) ⟨5736797, by rfl⟩ : syracuseStep 7649063 = 11473595) B11473595
theorem B5099375 : Blo 2013435 5099375 := bstep (se 1 (by rfl) ⟨3824531, by rfl⟩ : syracuseStep 5099375 = 7649063) B7649063
theorem B3399583 : Blo 2013435 3399583 := bstep (se 1 (by rfl) ⟨2549687, by rfl⟩ : syracuseStep 3399583 = 5099375) B5099375
theorem B4532777 : Blo 2013435 4532777 := bstep (se 2 (by rfl) ⟨1699791, by rfl⟩ : syracuseStep 4532777 = 3399583) B3399583
theorem B3021851 : Blo 2013435 3021851 := bstep (se 1 (by rfl) ⟨2266388, by rfl⟩ : syracuseStep 3021851 = 4532777) B4532777
theorem B2014567 : Blo 2013435 2014567 := bstep (se 1 (by rfl) ⟨1510925, by rfl⟩ : syracuseStep 2014567 = 3021851) B3021851
theorem B2266393 : Blo 2013435 2266393 := bbase (se 2 (by rfl) ⟨849897, by rfl⟩ : syracuseStep 2266393 = 1699795) (by norm_num)
theorem B3021857 : Blo 2013435 3021857 := bstep (se 2 (by rfl) ⟨1133196, by rfl⟩ : syracuseStep 3021857 = 2266393) B2266393
theorem B2014571 : Blo 2013435 2014571 := bstep (se 1 (by rfl) ⟨1510928, by rfl⟩ : syracuseStep 2014571 = 3021857) B3021857
theorem B7649093 : Blo 2013435 7649093 := bbase (se 4 (by rfl) ⟨717102, by rfl⟩ : syracuseStep 7649093 = 1434205) (by norm_num)
theorem B5099395 : Blo 2013435 5099395 := bstep (se 1 (by rfl) ⟨3824546, by rfl⟩ : syracuseStep 5099395 = 7649093) B7649093
theorem B6799193 : Blo 2013435 6799193 := bstep (se 2 (by rfl) ⟨2549697, by rfl⟩ : syracuseStep 6799193 = 5099395) B5099395
theorem B4532795 : Blo 2013435 4532795 := bstep (se 1 (by rfl) ⟨3399596, by rfl⟩ : syracuseStep 4532795 = 6799193) B6799193
theorem B3021863 : Blo 2013435 3021863 := bstep (se 1 (by rfl) ⟨2266397, by rfl⟩ : syracuseStep 3021863 = 4532795) B4532795
theorem B2014575 : Blo 2013435 2014575 := bstep (se 1 (by rfl) ⟨1510931, by rfl⟩ : syracuseStep 2014575 = 3021863) B3021863
theorem B3021869 : Blo 2013435 3021869 := bbase (se 3 (by rfl) ⟨566600, by rfl⟩ : syracuseStep 3021869 = 1133201) (by norm_num)
theorem B2014579 : Blo 2013435 2014579 := bstep (se 1 (by rfl) ⟨1510934, by rfl⟩ : syracuseStep 2014579 = 3021869) B3021869
theorem B4532813 : Blo 2013435 4532813 := bbase (se 3 (by rfl) ⟨849902, by rfl⟩ : syracuseStep 4532813 = 1699805) (by norm_num)
theorem B3021875 : Blo 2013435 3021875 := bstep (se 1 (by rfl) ⟨2266406, by rfl⟩ : syracuseStep 3021875 = 4532813) B4532813
theorem B2014583 : Blo 2013435 2014583 := bstep (se 1 (by rfl) ⟨1510937, by rfl⟩ : syracuseStep 2014583 = 3021875) B3021875
theorem B2549713 : Blo 2013435 2549713 := bbase (se 2 (by rfl) ⟨956142, by rfl⟩ : syracuseStep 2549713 = 1912285) (by norm_num)
theorem B3399617 : Blo 2013435 3399617 := bstep (se 2 (by rfl) ⟨1274856, by rfl⟩ : syracuseStep 3399617 = 2549713) B2549713
theorem B2266411 : Blo 2013435 2266411 := bstep (se 1 (by rfl) ⟨1699808, by rfl⟩ : syracuseStep 2266411 = 3399617) B3399617
theorem B3021881 : Blo 2013435 3021881 := bstep (se 2 (by rfl) ⟨1133205, by rfl⟩ : syracuseStep 3021881 = 2266411) B2266411
theorem B2014587 : Blo 2013435 2014587 := bstep (se 1 (by rfl) ⟨1510940, by rfl⟩ : syracuseStep 2014587 = 3021881) B3021881
theorem B4084157 : Blo 2013435 4084157 := bbase (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) (by norm_num)
theorem B2722771 : Blo 2013435 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B3630361 : Blo 2013435 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B4840481 : Blo 2013435 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B3226987 : Blo 2013435 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B4302649 : Blo 2013435 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B22947461 : Blo 2013435 22947461 := bstep (se 4 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 22947461 = 4302649) B4302649
theorem B15298307 : Blo 2013435 15298307 := bstep (se 1 (by rfl) ⟨11473730, by rfl⟩ : syracuseStep 15298307 = 22947461) B22947461
theorem B10198871 : Blo 2013435 10198871 := bstep (se 1 (by rfl) ⟨7649153, by rfl⟩ : syracuseStep 10198871 = 15298307) B15298307
theorem B6799247 : Blo 2013435 6799247 := bstep (se 1 (by rfl) ⟨5099435, by rfl⟩ : syracuseStep 6799247 = 10198871) B10198871
theorem B4532831 : Blo 2013435 4532831 := bstep (se 1 (by rfl) ⟨3399623, by rfl⟩ : syracuseStep 4532831 = 6799247) B6799247
theorem B3021887 : Blo 2013435 3021887 := bstep (se 1 (by rfl) ⟨2266415, by rfl⟩ : syracuseStep 3021887 = 4532831) B4532831
theorem B2014591 : Blo 2013435 2014591 := bstep (se 1 (by rfl) ⟨1510943, by rfl⟩ : syracuseStep 2014591 = 3021887) B3021887
theorem B3021893 : Blo 2013435 3021893 := bbase (se 4 (by rfl) ⟨283302, by rfl⟩ : syracuseStep 3021893 = 566605) (by norm_num)
theorem B2014595 : Blo 2013435 2014595 := bstep (se 1 (by rfl) ⟨1510946, by rfl⟩ : syracuseStep 2014595 = 3021893) B3021893
theorem B3399637 : Blo 2013435 3399637 := bbase (se 7 (by rfl) ⟨39839, by rfl⟩ : syracuseStep 3399637 = 79679) (by norm_num)
theorem B4532849 : Blo 2013435 4532849 := bstep (se 2 (by rfl) ⟨1699818, by rfl⟩ : syracuseStep 4532849 = 3399637) B3399637
theorem B3021899 : Blo 2013435 3021899 := bstep (se 1 (by rfl) ⟨2266424, by rfl⟩ : syracuseStep 3021899 = 4532849) B4532849
theorem B2014599 : Blo 2013435 2014599 := bstep (se 1 (by rfl) ⟨1510949, by rfl⟩ : syracuseStep 2014599 = 3021899) B3021899
theorem B2266429 : Blo 2013435 2266429 := bbase (se 3 (by rfl) ⟨424955, by rfl⟩ : syracuseStep 2266429 = 849911) (by norm_num)
theorem B3021905 : Blo 2013435 3021905 := bstep (se 2 (by rfl) ⟨1133214, by rfl⟩ : syracuseStep 3021905 = 2266429) B2266429
theorem B2014603 : Blo 2013435 2014603 := bstep (se 1 (by rfl) ⟨1510952, by rfl⟩ : syracuseStep 2014603 = 3021905) B3021905
theorem B6799301 : Blo 2013435 6799301 := bbase (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) (by norm_num)
theorem B4532867 : Blo 2013435 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B3021911 : Blo 2013435 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B2014607 : Blo 2013435 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B3021917 : Blo 2013435 3021917 := bbase (se 3 (by rfl) ⟨566609, by rfl⟩ : syracuseStep 3021917 = 1133219) (by norm_num)
theorem B2014611 : Blo 2013435 2014611 := bstep (se 1 (by rfl) ⟨1510958, by rfl⟩ : syracuseStep 2014611 = 3021917) B3021917
theorem B4532885 : Blo 2013435 4532885 := bbase (se 6 (by rfl) ⟨106239, by rfl⟩ : syracuseStep 4532885 = 212479) (by norm_num)
theorem B3021923 : Blo 2013435 3021923 := bstep (se 1 (by rfl) ⟨2266442, by rfl⟩ : syracuseStep 3021923 = 4532885) B4532885
theorem B2014615 : Blo 2013435 2014615 := bstep (se 1 (by rfl) ⟨1510961, by rfl⟩ : syracuseStep 2014615 = 3021923) B3021923
theorem B3630413 : Blo 2013435 3630413 := bbase (se 3 (by rfl) ⟨680702, by rfl⟩ : syracuseStep 3630413 = 1361405) (by norm_num)
theorem B2420275 : Blo 2013435 2420275 := bstep (se 1 (by rfl) ⟨1815206, by rfl⟩ : syracuseStep 2420275 = 3630413) B3630413
theorem B3227033 : Blo 2013435 3227033 := bstep (se 2 (by rfl) ⟨1210137, by rfl⟩ : syracuseStep 3227033 = 2420275) B2420275
theorem B2151355 : Blo 2013435 2151355 := bstep (se 1 (by rfl) ⟨1613516, by rfl⟩ : syracuseStep 2151355 = 3227033) B3227033
theorem B2868473 : Blo 2013435 2868473 := bstep (se 2 (by rfl) ⟨1075677, by rfl⟩ : syracuseStep 2868473 = 2151355) B2151355
theorem B7649261 : Blo 2013435 7649261 := bstep (se 3 (by rfl) ⟨1434236, by rfl⟩ : syracuseStep 7649261 = 2868473) B2868473
theorem B5099507 : Blo 2013435 5099507 := bstep (se 1 (by rfl) ⟨3824630, by rfl⟩ : syracuseStep 5099507 = 7649261) B7649261
theorem B3399671 : Blo 2013435 3399671 := bstep (se 1 (by rfl) ⟨2549753, by rfl⟩ : syracuseStep 3399671 = 5099507) B5099507
theorem B2266447 : Blo 2013435 2266447 := bstep (se 1 (by rfl) ⟨1699835, by rfl⟩ : syracuseStep 2266447 = 3399671) B3399671
theorem B3021929 : Blo 2013435 3021929 := bstep (se 2 (by rfl) ⟨1133223, by rfl⟩ : syracuseStep 3021929 = 2266447) B2266447
theorem B2014619 : Blo 2013435 2014619 := bstep (se 1 (by rfl) ⟨1510964, by rfl⟩ : syracuseStep 2014619 = 3021929) B3021929
theorem B2947285 : Blo 2013435 2947285 := bbase (se 7 (by rfl) ⟨34538, by rfl⟩ : syracuseStep 2947285 = 69077) (by norm_num)
theorem B15718853 : Blo 2013435 15718853 := bstep (se 4 (by rfl) ⟨1473642, by rfl⟩ : syracuseStep 15718853 = 2947285) B2947285
theorem B10479235 : Blo 2013435 10479235 := bstep (se 1 (by rfl) ⟨7859426, by rfl⟩ : syracuseStep 10479235 = 15718853) B15718853
theorem B13972313 : Blo 2013435 13972313 := bstep (se 2 (by rfl) ⟨5239617, by rfl⟩ : syracuseStep 13972313 = 10479235) B10479235
theorem B9314875 : Blo 2013435 9314875 := bstep (se 1 (by rfl) ⟨6986156, by rfl⟩ : syracuseStep 9314875 = 13972313) B13972313
theorem B12419833 : Blo 2013435 12419833 := bstep (se 2 (by rfl) ⟨4657437, by rfl⟩ : syracuseStep 12419833 = 9314875) B9314875
theorem B16559777 : Blo 2013435 16559777 := bstep (se 2 (by rfl) ⟨6209916, by rfl⟩ : syracuseStep 16559777 = 12419833) B12419833
theorem B11039851 : Blo 2013435 11039851 := bstep (se 1 (by rfl) ⟨8279888, by rfl⟩ : syracuseStep 11039851 = 16559777) B16559777
theorem B14719801 : Blo 2013435 14719801 := bstep (se 2 (by rfl) ⟨5519925, by rfl⟩ : syracuseStep 14719801 = 11039851) B11039851
theorem B19626401 : Blo 2013435 19626401 := bstep (se 2 (by rfl) ⟨7359900, by rfl⟩ : syracuseStep 19626401 = 14719801) B14719801
theorem B13084267 : Blo 2013435 13084267 := bstep (se 1 (by rfl) ⟨9813200, by rfl⟩ : syracuseStep 13084267 = 19626401) B19626401
theorem B17445689 : Blo 2013435 17445689 := bstep (se 2 (by rfl) ⟨6542133, by rfl⟩ : syracuseStep 17445689 = 13084267) B13084267
theorem B11630459 : Blo 2013435 11630459 := bstep (se 1 (by rfl) ⟨8722844, by rfl⟩ : syracuseStep 11630459 = 17445689) B17445689
theorem B7753639 : Blo 2013435 7753639 := bstep (se 1 (by rfl) ⟨5815229, by rfl⟩ : syracuseStep 7753639 = 11630459) B11630459
theorem B10338185 : Blo 2013435 10338185 := bstep (se 2 (by rfl) ⟨3876819, by rfl⟩ : syracuseStep 10338185 = 7753639) B7753639
theorem B6892123 : Blo 2013435 6892123 := bstep (se 1 (by rfl) ⟨5169092, by rfl⟩ : syracuseStep 6892123 = 10338185) B10338185
theorem B9189497 : Blo 2013435 9189497 := bstep (se 2 (by rfl) ⟨3446061, by rfl⟩ : syracuseStep 9189497 = 6892123) B6892123
theorem B24505325 : Blo 2013435 24505325 := bstep (se 3 (by rfl) ⟨4594748, by rfl⟩ : syracuseStep 24505325 = 9189497) B9189497
theorem B16336883 : Blo 2013435 16336883 := bstep (se 1 (by rfl) ⟨12252662, by rfl⟩ : syracuseStep 16336883 = 24505325) B24505325
theorem B10891255 : Blo 2013435 10891255 := bstep (se 1 (by rfl) ⟨8168441, by rfl⟩ : syracuseStep 10891255 = 16336883) B16336883
theorem B14521673 : Blo 2013435 14521673 := bstep (se 2 (by rfl) ⟨5445627, by rfl⟩ : syracuseStep 14521673 = 10891255) B10891255
theorem B9681115 : Blo 2013435 9681115 := bstep (se 1 (by rfl) ⟨7260836, by rfl⟩ : syracuseStep 9681115 = 14521673) B14521673
theorem B12908153 : Blo 2013435 12908153 := bstep (se 2 (by rfl) ⟨4840557, by rfl⟩ : syracuseStep 12908153 = 9681115) B9681115
theorem B8605435 : Blo 2013435 8605435 := bstep (se 1 (by rfl) ⟨6454076, by rfl⟩ : syracuseStep 8605435 = 12908153) B12908153
theorem B11473913 : Blo 2013435 11473913 := bstep (se 2 (by rfl) ⟨4302717, by rfl⟩ : syracuseStep 11473913 = 8605435) B8605435
theorem B7649275 : Blo 2013435 7649275 := bstep (se 1 (by rfl) ⟨5736956, by rfl⟩ : syracuseStep 7649275 = 11473913) B11473913
theorem B10199033 : Blo 2013435 10199033 := bstep (se 2 (by rfl) ⟨3824637, by rfl⟩ : syracuseStep 10199033 = 7649275) B7649275
theorem B6799355 : Blo 2013435 6799355 := bstep (se 1 (by rfl) ⟨5099516, by rfl⟩ : syracuseStep 6799355 = 10199033) B10199033
theorem B4532903 : Blo 2013435 4532903 := bstep (se 1 (by rfl) ⟨3399677, by rfl⟩ : syracuseStep 4532903 = 6799355) B6799355
theorem B3021935 : Blo 2013435 3021935 := bstep (se 1 (by rfl) ⟨2266451, by rfl⟩ : syracuseStep 3021935 = 4532903) B4532903
theorem B2014623 : Blo 2013435 2014623 := bstep (se 1 (by rfl) ⟨1510967, by rfl⟩ : syracuseStep 2014623 = 3021935) B3021935
theorem B3021941 : Blo 2013435 3021941 := bbase (se 5 (by rfl) ⟨141653, by rfl⟩ : syracuseStep 3021941 = 283307) (by norm_num)
theorem B2014627 : Blo 2013435 2014627 := bstep (se 1 (by rfl) ⟨1510970, by rfl⟩ : syracuseStep 2014627 = 3021941) B3021941
theorem B3824653 : Blo 2013435 3824653 := bbase (se 3 (by rfl) ⟨717122, by rfl⟩ : syracuseStep 3824653 = 1434245) (by norm_num)
theorem B5099537 : Blo 2013435 5099537 := bstep (se 2 (by rfl) ⟨1912326, by rfl⟩ : syracuseStep 5099537 = 3824653) B3824653
theorem B3399691 : Blo 2013435 3399691 := bstep (se 1 (by rfl) ⟨2549768, by rfl⟩ : syracuseStep 3399691 = 5099537) B5099537
theorem B4532921 : Blo 2013435 4532921 := bstep (se 2 (by rfl) ⟨1699845, by rfl⟩ : syracuseStep 4532921 = 3399691) B3399691
theorem B3021947 : Blo 2013435 3021947 := bstep (se 1 (by rfl) ⟨2266460, by rfl⟩ : syracuseStep 3021947 = 4532921) B4532921
theorem B2014631 : Blo 2013435 2014631 := bstep (se 1 (by rfl) ⟨1510973, by rfl⟩ : syracuseStep 2014631 = 3021947) B3021947
theorem B2266465 : Blo 2013435 2266465 := bbase (se 2 (by rfl) ⟨849924, by rfl⟩ : syracuseStep 2266465 = 1699849) (by norm_num)
theorem B3021953 : Blo 2013435 3021953 := bstep (se 2 (by rfl) ⟨1133232, by rfl⟩ : syracuseStep 3021953 = 2266465) B2266465
theorem B2014635 : Blo 2013435 2014635 := bstep (se 1 (by rfl) ⟨1510976, by rfl⟩ : syracuseStep 2014635 = 3021953) B3021953
theorem B5099557 : Blo 2013435 5099557 := bbase (se 4 (by rfl) ⟨478083, by rfl⟩ : syracuseStep 5099557 = 956167) (by norm_num)
theorem B6799409 : Blo 2013435 6799409 := bstep (se 2 (by rfl) ⟨2549778, by rfl⟩ : syracuseStep 6799409 = 5099557) B5099557
theorem B4532939 : Blo 2013435 4532939 := bstep (se 1 (by rfl) ⟨3399704, by rfl⟩ : syracuseStep 4532939 = 6799409) B6799409
theorem B3021959 : Blo 2013435 3021959 := bstep (se 1 (by rfl) ⟨2266469, by rfl⟩ : syracuseStep 3021959 = 4532939) B4532939
theorem B2014639 : Blo 2013435 2014639 := bstep (se 1 (by rfl) ⟨1510979, by rfl⟩ : syracuseStep 2014639 = 3021959) B3021959
theorem B3021965 : Blo 2013435 3021965 := bbase (se 3 (by rfl) ⟨566618, by rfl⟩ : syracuseStep 3021965 = 1133237) (by norm_num)
theorem B2014643 : Blo 2013435 2014643 := bstep (se 1 (by rfl) ⟨1510982, by rfl⟩ : syracuseStep 2014643 = 3021965) B3021965
theorem B4532957 : Blo 2013435 4532957 := bbase (se 3 (by rfl) ⟨849929, by rfl⟩ : syracuseStep 4532957 = 1699859) (by norm_num)
theorem B3021971 : Blo 2013435 3021971 := bstep (se 1 (by rfl) ⟨2266478, by rfl⟩ : syracuseStep 3021971 = 4532957) B4532957
theorem B2014647 : Blo 2013435 2014647 := bstep (se 1 (by rfl) ⟨1510985, by rfl⟩ : syracuseStep 2014647 = 3021971) B3021971
theorem B3399725 : Blo 2013435 3399725 := bbase (se 3 (by rfl) ⟨637448, by rfl⟩ : syracuseStep 3399725 = 1274897) (by norm_num)
theorem B2266483 : Blo 2013435 2266483 := bstep (se 1 (by rfl) ⟨1699862, by rfl⟩ : syracuseStep 2266483 = 3399725) B3399725
theorem B3021977 : Blo 2013435 3021977 := bstep (se 2 (by rfl) ⟨1133241, by rfl⟩ : syracuseStep 3021977 = 2266483) B2266483
theorem B2014651 : Blo 2013435 2014651 := bstep (se 1 (by rfl) ⟨1510988, by rfl⟩ : syracuseStep 2014651 = 3021977) B3021977
theorem B16337141 : Blo 2013435 16337141 := bbase (se 5 (by rfl) ⟨765803, by rfl⟩ : syracuseStep 16337141 = 1531607) (by norm_num)
theorem B10891427 : Blo 2013435 10891427 := bstep (se 1 (by rfl) ⟨8168570, by rfl⟩ : syracuseStep 10891427 = 16337141) B16337141
theorem B29043805 : Blo 2013435 29043805 := bstep (se 3 (by rfl) ⟨5445713, by rfl⟩ : syracuseStep 29043805 = 10891427) B10891427
theorem B38725073 : Blo 2013435 38725073 := bstep (se 2 (by rfl) ⟨14521902, by rfl⟩ : syracuseStep 38725073 = 29043805) B29043805
theorem B25816715 : Blo 2013435 25816715 := bstep (se 1 (by rfl) ⟨19362536, by rfl⟩ : syracuseStep 25816715 = 38725073) B38725073
theorem B17211143 : Blo 2013435 17211143 := bstep (se 1 (by rfl) ⟨12908357, by rfl⟩ : syracuseStep 17211143 = 25816715) B25816715
theorem B11474095 : Blo 2013435 11474095 := bstep (se 1 (by rfl) ⟨8605571, by rfl⟩ : syracuseStep 11474095 = 17211143) B17211143
theorem B15298793 : Blo 2013435 15298793 := bstep (se 2 (by rfl) ⟨5737047, by rfl⟩ : syracuseStep 15298793 = 11474095) B11474095
theorem B10199195 : Blo 2013435 10199195 := bstep (se 1 (by rfl) ⟨7649396, by rfl⟩ : syracuseStep 10199195 = 15298793) B15298793
theorem B6799463 : Blo 2013435 6799463 := bstep (se 1 (by rfl) ⟨5099597, by rfl⟩ : syracuseStep 6799463 = 10199195) B10199195
theorem B4532975 : Blo 2013435 4532975 := bstep (se 1 (by rfl) ⟨3399731, by rfl⟩ : syracuseStep 4532975 = 6799463) B6799463
theorem B3021983 : Blo 2013435 3021983 := bstep (se 1 (by rfl) ⟨2266487, by rfl⟩ : syracuseStep 3021983 = 4532975) B4532975
theorem B2014655 : Blo 2013435 2014655 := bstep (se 1 (by rfl) ⟨1510991, by rfl⟩ : syracuseStep 2014655 = 3021983) B3021983
theorem B3021989 : Blo 2013435 3021989 := bbase (se 4 (by rfl) ⟨283311, by rfl⟩ : syracuseStep 3021989 = 566623) (by norm_num)
theorem B2014659 : Blo 2013435 2014659 := bstep (se 1 (by rfl) ⟨1510994, by rfl⟩ : syracuseStep 2014659 = 3021989) B3021989
theorem B2549809 : Blo 2013435 2549809 := bbase (se 2 (by rfl) ⟨956178, by rfl⟩ : syracuseStep 2549809 = 1912357) (by norm_num)
theorem B3399745 : Blo 2013435 3399745 := bstep (se 2 (by rfl) ⟨1274904, by rfl⟩ : syracuseStep 3399745 = 2549809) B2549809
theorem B4532993 : Blo 2013435 4532993 := bstep (se 2 (by rfl) ⟨1699872, by rfl⟩ : syracuseStep 4532993 = 3399745) B3399745
theorem B3021995 : Blo 2013435 3021995 := bstep (se 1 (by rfl) ⟨2266496, by rfl⟩ : syracuseStep 3021995 = 4532993) B4532993
theorem B2014663 : Blo 2013435 2014663 := bstep (se 1 (by rfl) ⟨1510997, by rfl⟩ : syracuseStep 2014663 = 3021995) B3021995
theorem B2266501 : Blo 2013435 2266501 := bbase (se 4 (by rfl) ⟨212484, by rfl⟩ : syracuseStep 2266501 = 424969) (by norm_num)
theorem B3022001 : Blo 2013435 3022001 := bstep (se 2 (by rfl) ⟨1133250, by rfl⟩ : syracuseStep 3022001 = 2266501) B2266501
theorem B2014667 : Blo 2013435 2014667 := bstep (se 1 (by rfl) ⟨1511000, by rfl⟩ : syracuseStep 2014667 = 3022001) B3022001
theorem B4302821 : Blo 2013435 4302821 := bbase (se 4 (by rfl) ⟨403389, by rfl⟩ : syracuseStep 4302821 = 806779) (by norm_num)
theorem B2868547 : Blo 2013435 2868547 := bstep (se 1 (by rfl) ⟨2151410, by rfl⟩ : syracuseStep 2868547 = 4302821) B4302821
theorem B3824729 : Blo 2013435 3824729 := bstep (se 2 (by rfl) ⟨1434273, by rfl⟩ : syracuseStep 3824729 = 2868547) B2868547
theorem B2549819 : Blo 2013435 2549819 := bstep (se 1 (by rfl) ⟨1912364, by rfl⟩ : syracuseStep 2549819 = 3824729) B3824729
theorem B6799517 : Blo 2013435 6799517 := bstep (se 3 (by rfl) ⟨1274909, by rfl⟩ : syracuseStep 6799517 = 2549819) B2549819
theorem B4533011 : Blo 2013435 4533011 := bstep (se 1 (by rfl) ⟨3399758, by rfl⟩ : syracuseStep 4533011 = 6799517) B6799517
theorem B3022007 : Blo 2013435 3022007 := bstep (se 1 (by rfl) ⟨2266505, by rfl⟩ : syracuseStep 3022007 = 4533011) B4533011
theorem B2014671 : Blo 2013435 2014671 := bstep (se 1 (by rfl) ⟨1511003, by rfl⟩ : syracuseStep 2014671 = 3022007) B3022007
theorem B3022013 : Blo 2013435 3022013 := bbase (se 3 (by rfl) ⟨566627, by rfl⟩ : syracuseStep 3022013 = 1133255) (by norm_num)
theorem B2014675 : Blo 2013435 2014675 := bstep (se 1 (by rfl) ⟨1511006, by rfl⟩ : syracuseStep 2014675 = 3022013) B3022013
theorem B4533029 : Blo 2013435 4533029 := bbase (se 4 (by rfl) ⟨424971, by rfl⟩ : syracuseStep 4533029 = 849943) (by norm_num)
theorem B3022019 : Blo 2013435 3022019 := bstep (se 1 (by rfl) ⟨2266514, by rfl⟩ : syracuseStep 3022019 = 4533029) B4533029
theorem B2014679 : Blo 2013435 2014679 := bstep (se 1 (by rfl) ⟨1511009, by rfl⟩ : syracuseStep 2014679 = 3022019) B3022019
theorem B5099669 : Blo 2013435 5099669 := bbase (se 6 (by rfl) ⟨119523, by rfl⟩ : syracuseStep 5099669 = 239047) (by norm_num)
theorem B3399779 : Blo 2013435 3399779 := bstep (se 1 (by rfl) ⟨2549834, by rfl⟩ : syracuseStep 3399779 = 5099669) B5099669
theorem B2266519 : Blo 2013435 2266519 := bstep (se 1 (by rfl) ⟨1699889, by rfl⟩ : syracuseStep 2266519 = 3399779) B3399779
theorem B3022025 : Blo 2013435 3022025 := bstep (se 2 (by rfl) ⟨1133259, by rfl⟩ : syracuseStep 3022025 = 2266519) B2266519
theorem B2014683 : Blo 2013435 2014683 := bstep (se 1 (by rfl) ⟨1511012, by rfl⟩ : syracuseStep 2014683 = 3022025) B3022025
theorem B3227141 : Blo 2013435 3227141 := bbase (se 4 (by rfl) ⟨302544, by rfl⟩ : syracuseStep 3227141 = 605089) (by norm_num)
theorem B8605709 : Blo 2013435 8605709 := bstep (se 3 (by rfl) ⟨1613570, by rfl⟩ : syracuseStep 8605709 = 3227141) B3227141
theorem B5737139 : Blo 2013435 5737139 := bstep (se 1 (by rfl) ⟨4302854, by rfl⟩ : syracuseStep 5737139 = 8605709) B8605709
theorem B3824759 : Blo 2013435 3824759 := bstep (se 1 (by rfl) ⟨2868569, by rfl⟩ : syracuseStep 3824759 = 5737139) B5737139
theorem B10199357 : Blo 2013435 10199357 := bstep (se 3 (by rfl) ⟨1912379, by rfl⟩ : syracuseStep 10199357 = 3824759) B3824759
theorem B6799571 : Blo 2013435 6799571 := bstep (se 1 (by rfl) ⟨5099678, by rfl⟩ : syracuseStep 6799571 = 10199357) B10199357
theorem B4533047 : Blo 2013435 4533047 := bstep (se 1 (by rfl) ⟨3399785, by rfl⟩ : syracuseStep 4533047 = 6799571) B6799571
theorem B3022031 : Blo 2013435 3022031 := bstep (se 1 (by rfl) ⟨2266523, by rfl⟩ : syracuseStep 3022031 = 4533047) B4533047
theorem B2014687 : Blo 2013435 2014687 := bstep (se 1 (by rfl) ⟨1511015, by rfl⟩ : syracuseStep 2014687 = 3022031) B3022031
theorem B3022037 : Blo 2013435 3022037 := bbase (se 7 (by rfl) ⟨35414, by rfl⟩ : syracuseStep 3022037 = 70829) (by norm_num)
theorem B2014691 : Blo 2013435 2014691 := bstep (se 1 (by rfl) ⟨1511018, by rfl⟩ : syracuseStep 2014691 = 3022037) B3022037
theorem B2868581 : Blo 2013435 2868581 := bbase (se 4 (by rfl) ⟨268929, by rfl⟩ : syracuseStep 2868581 = 537859) (by norm_num)
theorem B7649549 : Blo 2013435 7649549 := bstep (se 3 (by rfl) ⟨1434290, by rfl⟩ : syracuseStep 7649549 = 2868581) B2868581
theorem B5099699 : Blo 2013435 5099699 := bstep (se 1 (by rfl) ⟨3824774, by rfl⟩ : syracuseStep 5099699 = 7649549) B7649549
theorem B3399799 : Blo 2013435 3399799 := bstep (se 1 (by rfl) ⟨2549849, by rfl⟩ : syracuseStep 3399799 = 5099699) B5099699
theorem B4533065 : Blo 2013435 4533065 := bstep (se 2 (by rfl) ⟨1699899, by rfl⟩ : syracuseStep 4533065 = 3399799) B3399799
theorem B3022043 : Blo 2013435 3022043 := bstep (se 1 (by rfl) ⟨2266532, by rfl⟩ : syracuseStep 3022043 = 4533065) B4533065
theorem B2014695 : Blo 2013435 2014695 := bstep (se 1 (by rfl) ⟨1511021, by rfl⟩ : syracuseStep 2014695 = 3022043) B3022043
theorem B2266537 : Blo 2013435 2266537 := bbase (se 2 (by rfl) ⟨849951, by rfl⟩ : syracuseStep 2266537 = 1699903) (by norm_num)
theorem B3022049 : Blo 2013435 3022049 := bstep (se 2 (by rfl) ⟨1133268, by rfl⟩ : syracuseStep 3022049 = 2266537) B2266537
theorem B2014699 : Blo 2013435 2014699 := bstep (se 1 (by rfl) ⟨1511024, by rfl⟩ : syracuseStep 2014699 = 3022049) B3022049
theorem B5445845 : Blo 2013435 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B3630563 : Blo 2013435 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B2420375 : Blo 2013435 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B6454333 : Blo 2013435 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B8605777 : Blo 2013435 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B11474369 : Blo 2013435 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B7649579 : Blo 2013435 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B5099719 : Blo 2013435 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B6799625 : Blo 2013435 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B4533083 : Blo 2013435 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B3022055 : Blo 2013435 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B2014703 : Blo 2013435 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B3022061 : Blo 2013435 3022061 := bbase (se 3 (by rfl) ⟨566636, by rfl⟩ : syracuseStep 3022061 = 1133273) (by norm_num)
theorem B2014707 : Blo 2013435 2014707 := bstep (se 1 (by rfl) ⟨1511030, by rfl⟩ : syracuseStep 2014707 = 3022061) B3022061
theorem B4533101 : Blo 2013435 4533101 := bbase (se 3 (by rfl) ⟨849956, by rfl⟩ : syracuseStep 4533101 = 1699913) (by norm_num)
theorem B3022067 : Blo 2013435 3022067 := bstep (se 1 (by rfl) ⟨2266550, by rfl⟩ : syracuseStep 3022067 = 4533101) B4533101
theorem B2014711 : Blo 2013435 2014711 := bstep (se 1 (by rfl) ⟨1511033, by rfl⟩ : syracuseStep 2014711 = 3022067) B3022067
theorem B3824813 : Blo 2013435 3824813 := bbase (se 3 (by rfl) ⟨717152, by rfl⟩ : syracuseStep 3824813 = 1434305) (by norm_num)
theorem B2549875 : Blo 2013435 2549875 := bstep (se 1 (by rfl) ⟨1912406, by rfl⟩ : syracuseStep 2549875 = 3824813) B3824813
theorem B3399833 : Blo 2013435 3399833 := bstep (se 2 (by rfl) ⟨1274937, by rfl⟩ : syracuseStep 3399833 = 2549875) B2549875
theorem B2266555 : Blo 2013435 2266555 := bstep (se 1 (by rfl) ⟨1699916, by rfl⟩ : syracuseStep 2266555 = 3399833) B3399833
theorem B3022073 : Blo 2013435 3022073 := bstep (se 2 (by rfl) ⟨1133277, by rfl⟩ : syracuseStep 3022073 = 2266555) B2266555
theorem B2014715 : Blo 2013435 2014715 := bstep (se 1 (by rfl) ⟨1511036, by rfl⟩ : syracuseStep 2014715 = 3022073) B3022073
theorem B31439189 : Blo 2013435 31439189 := bbase (se 10 (by rfl) ⟨46053, by rfl⟩ : syracuseStep 31439189 = 92107) (by norm_num)
theorem B83837837 : Blo 2013435 83837837 := bstep (se 3 (by rfl) ⟨15719594, by rfl⟩ : syracuseStep 83837837 = 31439189) B31439189
theorem B55891891 : Blo 2013435 55891891 := bstep (se 1 (by rfl) ⟨41918918, by rfl⟩ : syracuseStep 55891891 = 83837837) B83837837
theorem B74522521 : Blo 2013435 74522521 := bstep (se 2 (by rfl) ⟨27945945, by rfl⟩ : syracuseStep 74522521 = 55891891) B55891891
theorem B99363361 : Blo 2013435 99363361 := bstep (se 2 (by rfl) ⟨37261260, by rfl⟩ : syracuseStep 99363361 = 74522521) B74522521
theorem B132484481 : Blo 2013435 132484481 := bstep (se 2 (by rfl) ⟨49681680, by rfl⟩ : syracuseStep 132484481 = 99363361) B99363361
theorem B88322987 : Blo 2013435 88322987 := bstep (se 1 (by rfl) ⟨66242240, by rfl⟩ : syracuseStep 88322987 = 132484481) B132484481
theorem B58881991 : Blo 2013435 58881991 := bstep (se 1 (by rfl) ⟨44161493, by rfl⟩ : syracuseStep 58881991 = 88322987) B88322987
theorem B78509321 : Blo 2013435 78509321 := bstep (se 2 (by rfl) ⟨29440995, by rfl⟩ : syracuseStep 78509321 = 58881991) B58881991
theorem B52339547 : Blo 2013435 52339547 := bstep (se 1 (by rfl) ⟨39254660, by rfl⟩ : syracuseStep 52339547 = 78509321) B78509321
theorem B34893031 : Blo 2013435 34893031 := bstep (se 1 (by rfl) ⟨26169773, by rfl⟩ : syracuseStep 34893031 = 52339547) B52339547
theorem B46524041 : Blo 2013435 46524041 := bstep (se 2 (by rfl) ⟨17446515, by rfl⟩ : syracuseStep 46524041 = 34893031) B34893031
theorem B31016027 : Blo 2013435 31016027 := bstep (se 1 (by rfl) ⟨23262020, by rfl⟩ : syracuseStep 31016027 = 46524041) B46524041
theorem B20677351 : Blo 2013435 20677351 := bstep (se 1 (by rfl) ⟨15508013, by rfl⟩ : syracuseStep 20677351 = 31016027) B31016027
theorem B27569801 : Blo 2013435 27569801 := bstep (se 2 (by rfl) ⟨10338675, by rfl⟩ : syracuseStep 27569801 = 20677351) B20677351
theorem B18379867 : Blo 2013435 18379867 := bstep (se 1 (by rfl) ⟨13784900, by rfl⟩ : syracuseStep 18379867 = 27569801) B27569801
theorem B24506489 : Blo 2013435 24506489 := bstep (se 2 (by rfl) ⟨9189933, by rfl⟩ : syracuseStep 24506489 = 18379867) B18379867
theorem B65350637 : Blo 2013435 65350637 := bstep (se 3 (by rfl) ⟨12253244, by rfl⟩ : syracuseStep 65350637 = 24506489) B24506489
theorem B43567091 : Blo 2013435 43567091 := bstep (se 1 (by rfl) ⟨32675318, by rfl⟩ : syracuseStep 43567091 = 65350637) B65350637
theorem B29044727 : Blo 2013435 29044727 := bstep (se 1 (by rfl) ⟨21783545, by rfl⟩ : syracuseStep 29044727 = 43567091) B43567091
theorem B19363151 : Blo 2013435 19363151 := bstep (se 1 (by rfl) ⟨14522363, by rfl⟩ : syracuseStep 19363151 = 29044727) B29044727
theorem B51635069 : Blo 2013435 51635069 := bstep (se 3 (by rfl) ⟨9681575, by rfl⟩ : syracuseStep 51635069 = 19363151) B19363151
theorem B34423379 : Blo 2013435 34423379 := bstep (se 1 (by rfl) ⟨25817534, by rfl⟩ : syracuseStep 34423379 = 51635069) B51635069
theorem B22948919 : Blo 2013435 22948919 := bstep (se 1 (by rfl) ⟨17211689, by rfl⟩ : syracuseStep 22948919 = 34423379) B34423379
theorem B15299279 : Blo 2013435 15299279 := bstep (se 1 (by rfl) ⟨11474459, by rfl⟩ : syracuseStep 15299279 = 22948919) B22948919
theorem B10199519 : Blo 2013435 10199519 := bstep (se 1 (by rfl) ⟨7649639, by rfl⟩ : syracuseStep 10199519 = 15299279) B15299279
theorem B6799679 : Blo 2013435 6799679 := bstep (se 1 (by rfl) ⟨5099759, by rfl⟩ : syracuseStep 6799679 = 10199519) B10199519
theorem B4533119 : Blo 2013435 4533119 := bstep (se 1 (by rfl) ⟨3399839, by rfl⟩ : syracuseStep 4533119 = 6799679) B6799679
theorem B3022079 : Blo 2013435 3022079 := bstep (se 1 (by rfl) ⟨2266559, by rfl⟩ : syracuseStep 3022079 = 4533119) B4533119
theorem B2014719 : Blo 2013435 2014719 := bstep (se 1 (by rfl) ⟨1511039, by rfl⟩ : syracuseStep 2014719 = 3022079) B3022079
theorem B3022085 : Blo 2013435 3022085 := bbase (se 4 (by rfl) ⟨283320, by rfl⟩ : syracuseStep 3022085 = 566641) (by norm_num)
theorem B2014723 : Blo 2013435 2014723 := bstep (se 1 (by rfl) ⟨1511042, by rfl⟩ : syracuseStep 2014723 = 3022085) B3022085
theorem B3399853 : Blo 2013435 3399853 := bbase (se 3 (by rfl) ⟨637472, by rfl⟩ : syracuseStep 3399853 = 1274945) (by norm_num)
theorem B4533137 : Blo 2013435 4533137 := bstep (se 2 (by rfl) ⟨1699926, by rfl⟩ : syracuseStep 4533137 = 3399853) B3399853
theorem B3022091 : Blo 2013435 3022091 := bstep (se 1 (by rfl) ⟨2266568, by rfl⟩ : syracuseStep 3022091 = 4533137) B4533137
theorem B2014727 : Blo 2013435 2014727 := bstep (se 1 (by rfl) ⟨1511045, by rfl⟩ : syracuseStep 2014727 = 3022091) B3022091
theorem B2266573 : Blo 2013435 2266573 := bbase (se 3 (by rfl) ⟨424982, by rfl⟩ : syracuseStep 2266573 = 849965) (by norm_num)
theorem B3022097 : Blo 2013435 3022097 := bstep (se 2 (by rfl) ⟨1133286, by rfl⟩ : syracuseStep 3022097 = 2266573) B2266573
theorem B2014731 : Blo 2013435 2014731 := bstep (se 1 (by rfl) ⟨1511048, by rfl⟩ : syracuseStep 2014731 = 3022097) B3022097
theorem B6799733 : Blo 2013435 6799733 := bbase (se 5 (by rfl) ⟨318737, by rfl⟩ : syracuseStep 6799733 = 637475) (by norm_num)
theorem B4533155 : Blo 2013435 4533155 := bstep (se 1 (by rfl) ⟨3399866, by rfl⟩ : syracuseStep 4533155 = 6799733) B6799733
theorem B3022103 : Blo 2013435 3022103 := bstep (se 1 (by rfl) ⟨2266577, by rfl⟩ : syracuseStep 3022103 = 4533155) B4533155
theorem B2014735 : Blo 2013435 2014735 := bstep (se 1 (by rfl) ⟨1511051, by rfl⟩ : syracuseStep 2014735 = 3022103) B3022103
theorem B3022109 : Blo 2013435 3022109 := bbase (se 3 (by rfl) ⟨566645, by rfl⟩ : syracuseStep 3022109 = 1133291) (by norm_num)
theorem B2014739 : Blo 2013435 2014739 := bstep (se 1 (by rfl) ⟨1511054, by rfl⟩ : syracuseStep 2014739 = 3022109) B3022109
theorem B4533173 : Blo 2013435 4533173 := bbase (se 5 (by rfl) ⟨212492, by rfl⟩ : syracuseStep 4533173 = 424985) (by norm_num)
theorem B3022115 : Blo 2013435 3022115 := bstep (se 1 (by rfl) ⟨2266586, by rfl⟩ : syracuseStep 3022115 = 4533173) B4533173
theorem B2014743 : Blo 2013435 2014743 := bstep (se 1 (by rfl) ⟨1511057, by rfl⟩ : syracuseStep 2014743 = 3022115) B3022115
theorem B7261285 : Blo 2013435 7261285 := bbase (se 4 (by rfl) ⟨680745, by rfl⟩ : syracuseStep 7261285 = 1361491) (by norm_num)
theorem B9681713 : Blo 2013435 9681713 := bstep (se 2 (by rfl) ⟨3630642, by rfl⟩ : syracuseStep 9681713 = 7261285) B7261285
theorem B6454475 : Blo 2013435 6454475 := bstep (se 1 (by rfl) ⟨4840856, by rfl⟩ : syracuseStep 6454475 = 9681713) B9681713
theorem B4302983 : Blo 2013435 4302983 := bstep (se 1 (by rfl) ⟨3227237, by rfl⟩ : syracuseStep 4302983 = 6454475) B6454475
theorem B11474621 : Blo 2013435 11474621 := bstep (se 3 (by rfl) ⟨2151491, by rfl⟩ : syracuseStep 11474621 = 4302983) B4302983
theorem B7649747 : Blo 2013435 7649747 := bstep (se 1 (by rfl) ⟨5737310, by rfl⟩ : syracuseStep 7649747 = 11474621) B11474621
theorem B5099831 : Blo 2013435 5099831 := bstep (se 1 (by rfl) ⟨3824873, by rfl⟩ : syracuseStep 5099831 = 7649747) B7649747
theorem B3399887 : Blo 2013435 3399887 := bstep (se 1 (by rfl) ⟨2549915, by rfl⟩ : syracuseStep 3399887 = 5099831) B5099831
theorem B2266591 : Blo 2013435 2266591 := bstep (se 1 (by rfl) ⟨1699943, by rfl⟩ : syracuseStep 2266591 = 3399887) B3399887
theorem B3022121 : Blo 2013435 3022121 := bstep (se 2 (by rfl) ⟨1133295, by rfl⟩ : syracuseStep 3022121 = 2266591) B2266591
theorem B2014747 : Blo 2013435 2014747 := bstep (se 1 (by rfl) ⟨1511060, by rfl⟩ : syracuseStep 2014747 = 3022121) B3022121
theorem B2297521 : Blo 2013435 2297521 := bbase (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) (by norm_num)
theorem B3063361 : Blo 2013435 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B4084481 : Blo 2013435 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B2722987 : Blo 2013435 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B14522597 : Blo 2013435 14522597 := bstep (se 4 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 14522597 = 2722987) B2722987
theorem B9681731 : Blo 2013435 9681731 := bstep (se 1 (by rfl) ⟨7261298, by rfl⟩ : syracuseStep 9681731 = 14522597) B14522597
theorem B6454487 : Blo 2013435 6454487 := bstep (se 1 (by rfl) ⟨4840865, by rfl⟩ : syracuseStep 6454487 = 9681731) B9681731
theorem B4302991 : Blo 2013435 4302991 := bstep (se 1 (by rfl) ⟨3227243, by rfl⟩ : syracuseStep 4302991 = 6454487) B6454487
theorem B5737321 : Blo 2013435 5737321 := bstep (se 2 (by rfl) ⟨2151495, by rfl⟩ : syracuseStep 5737321 = 4302991) B4302991
theorem B7649761 : Blo 2013435 7649761 := bstep (se 2 (by rfl) ⟨2868660, by rfl⟩ : syracuseStep 7649761 = 5737321) B5737321
theorem B10199681 : Blo 2013435 10199681 := bstep (se 2 (by rfl) ⟨3824880, by rfl⟩ : syracuseStep 10199681 = 7649761) B7649761
theorem B6799787 : Blo 2013435 6799787 := bstep (se 1 (by rfl) ⟨5099840, by rfl⟩ : syracuseStep 6799787 = 10199681) B10199681
theorem B4533191 : Blo 2013435 4533191 := bstep (se 1 (by rfl) ⟨3399893, by rfl⟩ : syracuseStep 4533191 = 6799787) B6799787
theorem B3022127 : Blo 2013435 3022127 := bstep (se 1 (by rfl) ⟨2266595, by rfl⟩ : syracuseStep 3022127 = 4533191) B4533191
theorem B2014751 : Blo 2013435 2014751 := bstep (se 1 (by rfl) ⟨1511063, by rfl⟩ : syracuseStep 2014751 = 3022127) B3022127
theorem B3022133 : Blo 2013435 3022133 := bbase (se 5 (by rfl) ⟨141662, by rfl⟩ : syracuseStep 3022133 = 283325) (by norm_num)
theorem B2014755 : Blo 2013435 2014755 := bstep (se 1 (by rfl) ⟨1511066, by rfl⟩ : syracuseStep 2014755 = 3022133) B3022133
theorem B5099861 : Blo 2013435 5099861 := bbase (se 10 (by rfl) ⟨7470, by rfl⟩ : syracuseStep 5099861 = 14941) (by norm_num)
theorem B3399907 : Blo 2013435 3399907 := bstep (se 1 (by rfl) ⟨2549930, by rfl⟩ : syracuseStep 3399907 = 5099861) B5099861
theorem B4533209 : Blo 2013435 4533209 := bstep (se 2 (by rfl) ⟨1699953, by rfl⟩ : syracuseStep 4533209 = 3399907) B3399907
theorem B3022139 : Blo 2013435 3022139 := bstep (se 1 (by rfl) ⟨2266604, by rfl⟩ : syracuseStep 3022139 = 4533209) B4533209
theorem B2014759 : Blo 2013435 2014759 := bstep (se 1 (by rfl) ⟨1511069, by rfl⟩ : syracuseStep 2014759 = 3022139) B3022139
theorem B2266609 : Blo 2013435 2266609 := bbase (se 2 (by rfl) ⟨849978, by rfl⟩ : syracuseStep 2266609 = 1699957) (by norm_num)
theorem B3022145 : Blo 2013435 3022145 := bstep (se 2 (by rfl) ⟨1133304, by rfl⟩ : syracuseStep 3022145 = 2266609) B2266609
theorem B2014763 : Blo 2013435 2014763 := bstep (se 1 (by rfl) ⟨1511072, by rfl⟩ : syracuseStep 2014763 = 3022145) B3022145
theorem B12909077 : Blo 2013435 12909077 := bbase (se 6 (by rfl) ⟨302556, by rfl⟩ : syracuseStep 12909077 = 605113) (by norm_num)
theorem B8606051 : Blo 2013435 8606051 := bstep (se 1 (by rfl) ⟨6454538, by rfl⟩ : syracuseStep 8606051 = 12909077) B12909077
theorem B5737367 : Blo 2013435 5737367 := bstep (se 1 (by rfl) ⟨4303025, by rfl⟩ : syracuseStep 5737367 = 8606051) B8606051
theorem B3824911 : Blo 2013435 3824911 := bstep (se 1 (by rfl) ⟨2868683, by rfl⟩ : syracuseStep 3824911 = 5737367) B5737367
theorem B5099881 : Blo 2013435 5099881 := bstep (se 2 (by rfl) ⟨1912455, by rfl⟩ : syracuseStep 5099881 = 3824911) B3824911
theorem B6799841 : Blo 2013435 6799841 := bstep (se 2 (by rfl) ⟨2549940, by rfl⟩ : syracuseStep 6799841 = 5099881) B5099881
theorem B4533227 : Blo 2013435 4533227 := bstep (se 1 (by rfl) ⟨3399920, by rfl⟩ : syracuseStep 4533227 = 6799841) B6799841
theorem B3022151 : Blo 2013435 3022151 := bstep (se 1 (by rfl) ⟨2266613, by rfl⟩ : syracuseStep 3022151 = 4533227) B4533227
theorem B2014767 : Blo 2013435 2014767 := bstep (se 1 (by rfl) ⟨1511075, by rfl⟩ : syracuseStep 2014767 = 3022151) B3022151
theorem B3022157 : Blo 2013435 3022157 := bbase (se 3 (by rfl) ⟨566654, by rfl⟩ : syracuseStep 3022157 = 1133309) (by norm_num)
theorem B2014771 : Blo 2013435 2014771 := bstep (se 1 (by rfl) ⟨1511078, by rfl⟩ : syracuseStep 2014771 = 3022157) B3022157
theorem B4533245 : Blo 2013435 4533245 := bbase (se 3 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 4533245 = 1699967) (by norm_num)
theorem B3022163 : Blo 2013435 3022163 := bstep (se 1 (by rfl) ⟨2266622, by rfl⟩ : syracuseStep 3022163 = 4533245) B4533245
theorem B2014775 : Blo 2013435 2014775 := bstep (se 1 (by rfl) ⟨1511081, by rfl⟩ : syracuseStep 2014775 = 3022163) B3022163
theorem B3399941 : Blo 2013435 3399941 := bbase (se 4 (by rfl) ⟨318744, by rfl⟩ : syracuseStep 3399941 = 637489) (by norm_num)
theorem B2266627 : Blo 2013435 2266627 := bstep (se 1 (by rfl) ⟨1699970, by rfl⟩ : syracuseStep 2266627 = 3399941) B3399941
theorem B3022169 : Blo 2013435 3022169 := bstep (se 2 (by rfl) ⟨1133313, by rfl⟩ : syracuseStep 3022169 = 2266627) B2266627
theorem B2014779 : Blo 2013435 2014779 := bstep (se 1 (by rfl) ⟨1511084, by rfl⟩ : syracuseStep 2014779 = 3022169) B3022169
theorem B15299765 : Blo 2013435 15299765 := bbase (se 5 (by rfl) ⟨717176, by rfl⟩ : syracuseStep 15299765 = 1434353) (by norm_num)
theorem B10199843 : Blo 2013435 10199843 := bstep (se 1 (by rfl) ⟨7649882, by rfl⟩ : syracuseStep 10199843 = 15299765) B15299765
theorem B6799895 : Blo 2013435 6799895 := bstep (se 1 (by rfl) ⟨5099921, by rfl⟩ : syracuseStep 6799895 = 10199843) B10199843
theorem B4533263 : Blo 2013435 4533263 := bstep (se 1 (by rfl) ⟨3399947, by rfl⟩ : syracuseStep 4533263 = 6799895) B6799895
theorem B3022175 : Blo 2013435 3022175 := bstep (se 1 (by rfl) ⟨2266631, by rfl⟩ : syracuseStep 3022175 = 4533263) B4533263
theorem B2014783 : Blo 2013435 2014783 := bstep (se 1 (by rfl) ⟨1511087, by rfl⟩ : syracuseStep 2014783 = 3022175) B3022175
theorem B3022181 : Blo 2013435 3022181 := bbase (se 4 (by rfl) ⟨283329, by rfl⟩ : syracuseStep 3022181 = 566659) (by norm_num)
theorem B2014787 : Blo 2013435 2014787 := bstep (se 1 (by rfl) ⟨1511090, by rfl⟩ : syracuseStep 2014787 = 3022181) B3022181
theorem B3824957 : Blo 2013435 3824957 := bbase (se 3 (by rfl) ⟨717179, by rfl⟩ : syracuseStep 3824957 = 1434359) (by norm_num)
theorem B2549971 : Blo 2013435 2549971 := bstep (se 1 (by rfl) ⟨1912478, by rfl⟩ : syracuseStep 2549971 = 3824957) B3824957
theorem B3399961 : Blo 2013435 3399961 := bstep (se 2 (by rfl) ⟨1274985, by rfl⟩ : syracuseStep 3399961 = 2549971) B2549971
theorem B4533281 : Blo 2013435 4533281 := bstep (se 2 (by rfl) ⟨1699980, by rfl⟩ : syracuseStep 4533281 = 3399961) B3399961
theorem B3022187 : Blo 2013435 3022187 := bstep (se 1 (by rfl) ⟨2266640, by rfl⟩ : syracuseStep 3022187 = 4533281) B4533281
theorem B2014791 : Blo 2013435 2014791 := bstep (se 1 (by rfl) ⟨1511093, by rfl⟩ : syracuseStep 2014791 = 3022187) B3022187
theorem B2266645 : Blo 2013435 2266645 := bbase (se 6 (by rfl) ⟨53124, by rfl⟩ : syracuseStep 2266645 = 106249) (by norm_num)
theorem B3022193 : Blo 2013435 3022193 := bstep (se 2 (by rfl) ⟨1133322, by rfl⟩ : syracuseStep 3022193 = 2266645) B2266645
theorem B2014795 : Blo 2013435 2014795 := bstep (se 1 (by rfl) ⟨1511096, by rfl⟩ : syracuseStep 2014795 = 3022193) B3022193
theorem B2549981 : Blo 2013435 2549981 := bbase (se 3 (by rfl) ⟨478121, by rfl⟩ : syracuseStep 2549981 = 956243) (by norm_num)
theorem B6799949 : Blo 2013435 6799949 := bstep (se 3 (by rfl) ⟨1274990, by rfl⟩ : syracuseStep 6799949 = 2549981) B2549981
theorem B4533299 : Blo 2013435 4533299 := bstep (se 1 (by rfl) ⟨3399974, by rfl⟩ : syracuseStep 4533299 = 6799949) B6799949
theorem B3022199 : Blo 2013435 3022199 := bstep (se 1 (by rfl) ⟨2266649, by rfl⟩ : syracuseStep 3022199 = 4533299) B4533299
theorem B2014799 : Blo 2013435 2014799 := bstep (se 1 (by rfl) ⟨1511099, by rfl⟩ : syracuseStep 2014799 = 3022199) B3022199
theorem B3022205 : Blo 2013435 3022205 := bbase (se 3 (by rfl) ⟨566663, by rfl⟩ : syracuseStep 3022205 = 1133327) (by norm_num)
theorem B2014803 : Blo 2013435 2014803 := bstep (se 1 (by rfl) ⟨1511102, by rfl⟩ : syracuseStep 2014803 = 3022205) B3022205
theorem B4533317 : Blo 2013435 4533317 := bbase (se 4 (by rfl) ⟨424998, by rfl⟩ : syracuseStep 4533317 = 849997) (by norm_num)
theorem B3022211 : Blo 2013435 3022211 := bstep (se 1 (by rfl) ⟨2266658, by rfl⟩ : syracuseStep 3022211 = 4533317) B4533317
theorem B2014807 : Blo 2013435 2014807 := bstep (se 1 (by rfl) ⟨1511105, by rfl⟩ : syracuseStep 2014807 = 3022211) B3022211
theorem B5737493 : Blo 2013435 5737493 := bbase (se 6 (by rfl) ⟨134472, by rfl⟩ : syracuseStep 5737493 = 268945) (by norm_num)
theorem B3824995 : Blo 2013435 3824995 := bstep (se 1 (by rfl) ⟨2868746, by rfl⟩ : syracuseStep 3824995 = 5737493) B5737493
theorem B5099993 : Blo 2013435 5099993 := bstep (se 2 (by rfl) ⟨1912497, by rfl⟩ : syracuseStep 5099993 = 3824995) B3824995
theorem B3399995 : Blo 2013435 3399995 := bstep (se 1 (by rfl) ⟨2549996, by rfl⟩ : syracuseStep 3399995 = 5099993) B5099993
theorem B2266663 : Blo 2013435 2266663 := bstep (se 1 (by rfl) ⟨1699997, by rfl⟩ : syracuseStep 2266663 = 3399995) B3399995
theorem B3022217 : Blo 2013435 3022217 := bstep (se 2 (by rfl) ⟨1133331, by rfl⟩ : syracuseStep 3022217 = 2266663) B2266663
theorem B2014811 : Blo 2013435 2014811 := bstep (se 1 (by rfl) ⟨1511108, by rfl⟩ : syracuseStep 2014811 = 3022217) B3022217
theorem B10200005 : Blo 2013435 10200005 := bbase (se 4 (by rfl) ⟨956250, by rfl⟩ : syracuseStep 10200005 = 1912501) (by norm_num)
theorem B6800003 : Blo 2013435 6800003 := bstep (se 1 (by rfl) ⟨5100002, by rfl⟩ : syracuseStep 6800003 = 10200005) B10200005
theorem B4533335 : Blo 2013435 4533335 := bstep (se 1 (by rfl) ⟨3400001, by rfl⟩ : syracuseStep 4533335 = 6800003) B6800003
theorem B3022223 : Blo 2013435 3022223 := bstep (se 1 (by rfl) ⟨2266667, by rfl⟩ : syracuseStep 3022223 = 4533335) B4533335
theorem B2014815 : Blo 2013435 2014815 := bstep (se 1 (by rfl) ⟨1511111, by rfl⟩ : syracuseStep 2014815 = 3022223) B3022223
theorem B3022229 : Blo 2013435 3022229 := bbase (se 6 (by rfl) ⟨70833, by rfl⟩ : syracuseStep 3022229 = 141667) (by norm_num)
theorem B2014819 : Blo 2013435 2014819 := bstep (se 1 (by rfl) ⟨1511114, by rfl⟩ : syracuseStep 2014819 = 3022229) B3022229
theorem B3446405 : Blo 2013435 3446405 := bbase (se 4 (by rfl) ⟨323100, by rfl⟩ : syracuseStep 3446405 = 646201) (by norm_num)
theorem B2297603 : Blo 2013435 2297603 := bstep (se 1 (by rfl) ⟨1723202, by rfl⟩ : syracuseStep 2297603 = 3446405) B3446405
theorem B6126941 : Blo 2013435 6126941 := bstep (se 3 (by rfl) ⟨1148801, by rfl⟩ : syracuseStep 6126941 = 2297603) B2297603
theorem B16338509 : Blo 2013435 16338509 := bstep (se 3 (by rfl) ⟨3063470, by rfl⟩ : syracuseStep 16338509 = 6126941) B6126941
theorem B10892339 : Blo 2013435 10892339 := bstep (se 1 (by rfl) ⟨8169254, by rfl⟩ : syracuseStep 10892339 = 16338509) B16338509
theorem B7261559 : Blo 2013435 7261559 := bstep (se 1 (by rfl) ⟨5446169, by rfl⟩ : syracuseStep 7261559 = 10892339) B10892339
theorem B4841039 : Blo 2013435 4841039 := bstep (se 1 (by rfl) ⟨3630779, by rfl⟩ : syracuseStep 4841039 = 7261559) B7261559
theorem B3227359 : Blo 2013435 3227359 := bstep (se 1 (by rfl) ⟨2420519, by rfl⟩ : syracuseStep 3227359 = 4841039) B4841039
theorem B4303145 : Blo 2013435 4303145 := bstep (se 2 (by rfl) ⟨1613679, by rfl⟩ : syracuseStep 4303145 = 3227359) B3227359
theorem B11475053 : Blo 2013435 11475053 := bstep (se 3 (by rfl) ⟨2151572, by rfl⟩ : syracuseStep 11475053 = 4303145) B4303145
theorem B7650035 : Blo 2013435 7650035 := bstep (se 1 (by rfl) ⟨5737526, by rfl⟩ : syracuseStep 7650035 = 11475053) B11475053
theorem B5100023 : Blo 2013435 5100023 := bstep (se 1 (by rfl) ⟨3825017, by rfl⟩ : syracuseStep 5100023 = 7650035) B7650035
theorem B3400015 : Blo 2013435 3400015 := bstep (se 1 (by rfl) ⟨2550011, by rfl⟩ : syracuseStep 3400015 = 5100023) B5100023
theorem B4533353 : Blo 2013435 4533353 := bstep (se 2 (by rfl) ⟨1700007, by rfl⟩ : syracuseStep 4533353 = 3400015) B3400015
theorem B3022235 : Blo 2013435 3022235 := bstep (se 1 (by rfl) ⟨2266676, by rfl⟩ : syracuseStep 3022235 = 4533353) B4533353
theorem B2014823 : Blo 2013435 2014823 := bstep (se 1 (by rfl) ⟨1511117, by rfl⟩ : syracuseStep 2014823 = 3022235) B3022235
theorem B2266681 : Blo 2013435 2266681 := bbase (se 2 (by rfl) ⟨850005, by rfl⟩ : syracuseStep 2266681 = 1700011) (by norm_num)
theorem B3022241 : Blo 2013435 3022241 := bstep (se 2 (by rfl) ⟨1133340, by rfl⟩ : syracuseStep 3022241 = 2266681) B2266681
theorem B2014827 : Blo 2013435 2014827 := bstep (se 1 (by rfl) ⟨1511120, by rfl⟩ : syracuseStep 2014827 = 3022241) B3022241
theorem B2151581 : Blo 2013435 2151581 := bbase (se 3 (by rfl) ⟨403421, by rfl⟩ : syracuseStep 2151581 = 806843) (by norm_num)
theorem B5737549 : Blo 2013435 5737549 := bstep (se 3 (by rfl) ⟨1075790, by rfl⟩ : syracuseStep 5737549 = 2151581) B2151581
theorem B7650065 : Blo 2013435 7650065 := bstep (se 2 (by rfl) ⟨2868774, by rfl⟩ : syracuseStep 7650065 = 5737549) B5737549
theorem B5100043 : Blo 2013435 5100043 := bstep (se 1 (by rfl) ⟨3825032, by rfl⟩ : syracuseStep 5100043 = 7650065) B7650065
theorem B6800057 : Blo 2013435 6800057 := bstep (se 2 (by rfl) ⟨2550021, by rfl⟩ : syracuseStep 6800057 = 5100043) B5100043
theorem B4533371 : Blo 2013435 4533371 := bstep (se 1 (by rfl) ⟨3400028, by rfl⟩ : syracuseStep 4533371 = 6800057) B6800057
theorem B3022247 : Blo 2013435 3022247 := bstep (se 1 (by rfl) ⟨2266685, by rfl⟩ : syracuseStep 3022247 = 4533371) B4533371
theorem B2014831 : Blo 2013435 2014831 := bstep (se 1 (by rfl) ⟨1511123, by rfl⟩ : syracuseStep 2014831 = 3022247) B3022247
theorem B3022253 : Blo 2013435 3022253 := bbase (se 3 (by rfl) ⟨566672, by rfl⟩ : syracuseStep 3022253 = 1133345) (by norm_num)
theorem B2014835 : Blo 2013435 2014835 := bstep (se 1 (by rfl) ⟨1511126, by rfl⟩ : syracuseStep 2014835 = 3022253) B3022253
theorem B4533389 : Blo 2013435 4533389 := bbase (se 3 (by rfl) ⟨850010, by rfl⟩ : syracuseStep 4533389 = 1700021) (by norm_num)
theorem B3022259 : Blo 2013435 3022259 := bstep (se 1 (by rfl) ⟨2266694, by rfl⟩ : syracuseStep 3022259 = 4533389) B4533389
theorem B2014839 : Blo 2013435 2014839 := bstep (se 1 (by rfl) ⟨1511129, by rfl⟩ : syracuseStep 2014839 = 3022259) B3022259
theorem B2550037 : Blo 2013435 2550037 := bbase (se 6 (by rfl) ⟨59766, by rfl⟩ : syracuseStep 2550037 = 119533) (by norm_num)
theorem B3400049 : Blo 2013435 3400049 := bstep (se 2 (by rfl) ⟨1275018, by rfl⟩ : syracuseStep 3400049 = 2550037) B2550037
theorem B2266699 : Blo 2013435 2266699 := bstep (se 1 (by rfl) ⟨1700024, by rfl⟩ : syracuseStep 2266699 = 3400049) B3400049
theorem B3022265 : Blo 2013435 3022265 := bstep (se 2 (by rfl) ⟨1133349, by rfl⟩ : syracuseStep 3022265 = 2266699) B2266699
theorem B2014843 : Blo 2013435 2014843 := bstep (se 1 (by rfl) ⟨1511132, by rfl⟩ : syracuseStep 2014843 = 3022265) B3022265
theorem B2760269 : Blo 2013435 2760269 := bbase (se 3 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 2760269 = 1035101) (by norm_num)
theorem B7360717 : Blo 2013435 7360717 := bstep (se 3 (by rfl) ⟨1380134, by rfl⟩ : syracuseStep 7360717 = 2760269) B2760269
theorem B9814289 : Blo 2013435 9814289 := bstep (se 2 (by rfl) ⟨3680358, by rfl⟩ : syracuseStep 9814289 = 7360717) B7360717
theorem B26171437 : Blo 2013435 26171437 := bstep (se 3 (by rfl) ⟨4907144, by rfl⟩ : syracuseStep 26171437 = 9814289) B9814289
theorem B34895249 : Blo 2013435 34895249 := bstep (se 2 (by rfl) ⟨13085718, by rfl⟩ : syracuseStep 34895249 = 26171437) B26171437
theorem B23263499 : Blo 2013435 23263499 := bstep (se 1 (by rfl) ⟨17447624, by rfl⟩ : syracuseStep 23263499 = 34895249) B34895249
theorem B15508999 : Blo 2013435 15508999 := bstep (se 1 (by rfl) ⟨11631749, by rfl⟩ : syracuseStep 15508999 = 23263499) B23263499
theorem B20678665 : Blo 2013435 20678665 := bstep (se 2 (by rfl) ⟨7754499, by rfl⟩ : syracuseStep 20678665 = 15508999) B15508999
theorem B27571553 : Blo 2013435 27571553 := bstep (se 2 (by rfl) ⟨10339332, by rfl⟩ : syracuseStep 27571553 = 20678665) B20678665
theorem B18381035 : Blo 2013435 18381035 := bstep (se 1 (by rfl) ⟨13785776, by rfl⟩ : syracuseStep 18381035 = 27571553) B27571553
theorem B12254023 : Blo 2013435 12254023 := bstep (se 1 (by rfl) ⟨9190517, by rfl⟩ : syracuseStep 12254023 = 18381035) B18381035
theorem B65354789 : Blo 2013435 65354789 := bstep (se 4 (by rfl) ⟨6127011, by rfl⟩ : syracuseStep 65354789 = 12254023) B12254023
theorem B43569859 : Blo 2013435 43569859 := bstep (se 1 (by rfl) ⟨32677394, by rfl⟩ : syracuseStep 43569859 = 65354789) B65354789
theorem B58093145 : Blo 2013435 58093145 := bstep (se 2 (by rfl) ⟨21784929, by rfl⟩ : syracuseStep 58093145 = 43569859) B43569859
theorem B38728763 : Blo 2013435 38728763 := bstep (se 1 (by rfl) ⟨29046572, by rfl⟩ : syracuseStep 38728763 = 58093145) B58093145
theorem B25819175 : Blo 2013435 25819175 := bstep (se 1 (by rfl) ⟨19364381, by rfl⟩ : syracuseStep 25819175 = 38728763) B38728763
theorem B17212783 : Blo 2013435 17212783 := bstep (se 1 (by rfl) ⟨12909587, by rfl⟩ : syracuseStep 17212783 = 25819175) B25819175
theorem B22950377 : Blo 2013435 22950377 := bstep (se 2 (by rfl) ⟨8606391, by rfl⟩ : syracuseStep 22950377 = 17212783) B17212783
theorem B15300251 : Blo 2013435 15300251 := bstep (se 1 (by rfl) ⟨11475188, by rfl⟩ : syracuseStep 15300251 = 22950377) B22950377
theorem B10200167 : Blo 2013435 10200167 := bstep (se 1 (by rfl) ⟨7650125, by rfl⟩ : syracuseStep 10200167 = 15300251) B15300251
theorem B6800111 : Blo 2013435 6800111 := bstep (se 1 (by rfl) ⟨5100083, by rfl⟩ : syracuseStep 6800111 = 10200167) B10200167
theorem B4533407 : Blo 2013435 4533407 := bstep (se 1 (by rfl) ⟨3400055, by rfl⟩ : syracuseStep 4533407 = 6800111) B6800111
theorem B3022271 : Blo 2013435 3022271 := bstep (se 1 (by rfl) ⟨2266703, by rfl⟩ : syracuseStep 3022271 = 4533407) B4533407
theorem B2014847 : Blo 2013435 2014847 := bstep (se 1 (by rfl) ⟨1511135, by rfl⟩ : syracuseStep 2014847 = 3022271) B3022271
theorem B3022277 : Blo 2013435 3022277 := bbase (se 4 (by rfl) ⟨283338, by rfl⟩ : syracuseStep 3022277 = 566677) (by norm_num)
theorem B2014851 : Blo 2013435 2014851 := bstep (se 1 (by rfl) ⟨1511138, by rfl⟩ : syracuseStep 2014851 = 3022277) B3022277
theorem B3400069 : Blo 2013435 3400069 := bbase (se 4 (by rfl) ⟨318756, by rfl⟩ : syracuseStep 3400069 = 637513) (by norm_num)
theorem B4533425 : Blo 2013435 4533425 := bstep (se 2 (by rfl) ⟨1700034, by rfl⟩ : syracuseStep 4533425 = 3400069) B3400069
theorem B3022283 : Blo 2013435 3022283 := bstep (se 1 (by rfl) ⟨2266712, by rfl⟩ : syracuseStep 3022283 = 4533425) B4533425
theorem B2014855 : Blo 2013435 2014855 := bstep (se 1 (by rfl) ⟨1511141, by rfl⟩ : syracuseStep 2014855 = 3022283) B3022283
theorem B2266717 : Blo 2013435 2266717 := bbase (se 3 (by rfl) ⟨425009, by rfl⟩ : syracuseStep 2266717 = 850019) (by norm_num)
theorem B3022289 : Blo 2013435 3022289 := bstep (se 2 (by rfl) ⟨1133358, by rfl⟩ : syracuseStep 3022289 = 2266717) B2266717
theorem B2014859 : Blo 2013435 2014859 := bstep (se 1 (by rfl) ⟨1511144, by rfl⟩ : syracuseStep 2014859 = 3022289) B3022289
theorem B6800165 : Blo 2013435 6800165 := bbase (se 4 (by rfl) ⟨637515, by rfl⟩ : syracuseStep 6800165 = 1275031) (by norm_num)
theorem B4533443 : Blo 2013435 4533443 := bstep (se 1 (by rfl) ⟨3400082, by rfl⟩ : syracuseStep 4533443 = 6800165) B6800165
theorem B3022295 : Blo 2013435 3022295 := bstep (se 1 (by rfl) ⟨2266721, by rfl⟩ : syracuseStep 3022295 = 4533443) B4533443
theorem B2014863 : Blo 2013435 2014863 := bstep (se 1 (by rfl) ⟨1511147, by rfl⟩ : syracuseStep 2014863 = 3022295) B3022295
theorem B3022301 : Blo 2013435 3022301 := bbase (se 3 (by rfl) ⟨566681, by rfl⟩ : syracuseStep 3022301 = 1133363) (by norm_num)
theorem B2014867 : Blo 2013435 2014867 := bstep (se 1 (by rfl) ⟨1511150, by rfl⟩ : syracuseStep 2014867 = 3022301) B3022301
theorem B4533461 : Blo 2013435 4533461 := bbase (se 7 (by rfl) ⟨53126, by rfl⟩ : syracuseStep 4533461 = 106253) (by norm_num)
theorem B3022307 : Blo 2013435 3022307 := bstep (se 1 (by rfl) ⟨2266730, by rfl⟩ : syracuseStep 3022307 = 4533461) B4533461
theorem B2014871 : Blo 2013435 2014871 := bstep (se 1 (by rfl) ⟨1511153, by rfl⟩ : syracuseStep 2014871 = 3022307) B3022307
theorem B6454885 : Blo 2013435 6454885 := bbase (se 4 (by rfl) ⟨605145, by rfl⟩ : syracuseStep 6454885 = 1210291) (by norm_num)
theorem B8606513 : Blo 2013435 8606513 := bstep (se 2 (by rfl) ⟨3227442, by rfl⟩ : syracuseStep 8606513 = 6454885) B6454885
theorem B5737675 : Blo 2013435 5737675 := bstep (se 1 (by rfl) ⟨4303256, by rfl⟩ : syracuseStep 5737675 = 8606513) B8606513
theorem B7650233 : Blo 2013435 7650233 := bstep (se 2 (by rfl) ⟨2868837, by rfl⟩ : syracuseStep 7650233 = 5737675) B5737675
theorem B5100155 : Blo 2013435 5100155 := bstep (se 1 (by rfl) ⟨3825116, by rfl⟩ : syracuseStep 5100155 = 7650233) B7650233
theorem B3400103 : Blo 2013435 3400103 := bstep (se 1 (by rfl) ⟨2550077, by rfl⟩ : syracuseStep 3400103 = 5100155) B5100155
theorem B2266735 : Blo 2013435 2266735 := bstep (se 1 (by rfl) ⟨1700051, by rfl⟩ : syracuseStep 2266735 = 3400103) B3400103
theorem B3022313 : Blo 2013435 3022313 := bstep (se 2 (by rfl) ⟨1133367, by rfl⟩ : syracuseStep 3022313 = 2266735) B2266735
theorem B2014875 : Blo 2013435 2014875 := bstep (se 1 (by rfl) ⟨1511156, by rfl⟩ : syracuseStep 2014875 = 3022313) B3022313
theorem B5169749 : Blo 2013435 5169749 := bbase (se 8 (by rfl) ⟨30291, by rfl⟩ : syracuseStep 5169749 = 60583) (by norm_num)
theorem B55143989 : Blo 2013435 55143989 := bstep (se 5 (by rfl) ⟨2584874, by rfl⟩ : syracuseStep 55143989 = 5169749) B5169749
theorem B36762659 : Blo 2013435 36762659 := bstep (se 1 (by rfl) ⟨27571994, by rfl⟩ : syracuseStep 36762659 = 55143989) B55143989
theorem B24508439 : Blo 2013435 24508439 := bstep (se 1 (by rfl) ⟨18381329, by rfl⟩ : syracuseStep 24508439 = 36762659) B36762659
theorem B16338959 : Blo 2013435 16338959 := bstep (se 1 (by rfl) ⟨12254219, by rfl⟩ : syracuseStep 16338959 = 24508439) B24508439
theorem B10892639 : Blo 2013435 10892639 := bstep (se 1 (by rfl) ⟨8169479, by rfl⟩ : syracuseStep 10892639 = 16338959) B16338959
theorem B7261759 : Blo 2013435 7261759 := bstep (se 1 (by rfl) ⟨5446319, by rfl⟩ : syracuseStep 7261759 = 10892639) B10892639
theorem B9682345 : Blo 2013435 9682345 := bstep (se 2 (by rfl) ⟨3630879, by rfl⟩ : syracuseStep 9682345 = 7261759) B7261759
theorem B12909793 : Blo 2013435 12909793 := bstep (se 2 (by rfl) ⟨4841172, by rfl⟩ : syracuseStep 12909793 = 9682345) B9682345
theorem B17213057 : Blo 2013435 17213057 := bstep (se 2 (by rfl) ⟨6454896, by rfl⟩ : syracuseStep 17213057 = 12909793) B12909793
theorem B11475371 : Blo 2013435 11475371 := bstep (se 1 (by rfl) ⟨8606528, by rfl⟩ : syracuseStep 11475371 = 17213057) B17213057
theorem B7650247 : Blo 2013435 7650247 := bstep (se 1 (by rfl) ⟨5737685, by rfl⟩ : syracuseStep 7650247 = 11475371) B11475371
theorem B10200329 : Blo 2013435 10200329 := bstep (se 2 (by rfl) ⟨3825123, by rfl⟩ : syracuseStep 10200329 = 7650247) B7650247
theorem B6800219 : Blo 2013435 6800219 := bstep (se 1 (by rfl) ⟨5100164, by rfl⟩ : syracuseStep 6800219 = 10200329) B10200329
theorem B4533479 : Blo 2013435 4533479 := bstep (se 1 (by rfl) ⟨3400109, by rfl⟩ : syracuseStep 4533479 = 6800219) B6800219
theorem B3022319 : Blo 2013435 3022319 := bstep (se 1 (by rfl) ⟨2266739, by rfl⟩ : syracuseStep 3022319 = 4533479) B4533479
theorem B2014879 : Blo 2013435 2014879 := bstep (se 1 (by rfl) ⟨1511159, by rfl⟩ : syracuseStep 2014879 = 3022319) B3022319
theorem B3022325 : Blo 2013435 3022325 := bbase (se 5 (by rfl) ⟨141671, by rfl⟩ : syracuseStep 3022325 = 283343) (by norm_num)
theorem B2014883 : Blo 2013435 2014883 := bstep (se 1 (by rfl) ⟨1511162, by rfl⟩ : syracuseStep 2014883 = 3022325) B3022325
theorem B2151641 : Blo 2013435 2151641 := bbase (se 2 (by rfl) ⟨806865, by rfl⟩ : syracuseStep 2151641 = 1613731) (by norm_num)
theorem B5737709 : Blo 2013435 5737709 := bstep (se 3 (by rfl) ⟨1075820, by rfl⟩ : syracuseStep 5737709 = 2151641) B2151641
theorem B3825139 : Blo 2013435 3825139 := bstep (se 1 (by rfl) ⟨2868854, by rfl⟩ : syracuseStep 3825139 = 5737709) B5737709
theorem B5100185 : Blo 2013435 5100185 := bstep (se 2 (by rfl) ⟨1912569, by rfl⟩ : syracuseStep 5100185 = 3825139) B3825139
theorem B3400123 : Blo 2013435 3400123 := bstep (se 1 (by rfl) ⟨2550092, by rfl⟩ : syracuseStep 3400123 = 5100185) B5100185
theorem B4533497 : Blo 2013435 4533497 := bstep (se 2 (by rfl) ⟨1700061, by rfl⟩ : syracuseStep 4533497 = 3400123) B3400123
theorem B3022331 : Blo 2013435 3022331 := bstep (se 1 (by rfl) ⟨2266748, by rfl⟩ : syracuseStep 3022331 = 4533497) B4533497
theorem B2014887 : Blo 2013435 2014887 := bstep (se 1 (by rfl) ⟨1511165, by rfl⟩ : syracuseStep 2014887 = 3022331) B3022331
theorem B2266753 : Blo 2013435 2266753 := bbase (se 2 (by rfl) ⟨850032, by rfl⟩ : syracuseStep 2266753 = 1700065) (by norm_num)
theorem B3022337 : Blo 2013435 3022337 := bstep (se 2 (by rfl) ⟨1133376, by rfl⟩ : syracuseStep 3022337 = 2266753) B2266753
theorem B2014891 : Blo 2013435 2014891 := bstep (se 1 (by rfl) ⟨1511168, by rfl⟩ : syracuseStep 2014891 = 3022337) B3022337
theorem B5100205 : Blo 2013435 5100205 := bbase (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) (by norm_num)
theorem B6800273 : Blo 2013435 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B4533515 : Blo 2013435 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B3022343 : Blo 2013435 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B2014895 : Blo 2013435 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B3022349 : Blo 2013435 3022349 := bbase (se 3 (by rfl) ⟨566690, by rfl⟩ : syracuseStep 3022349 = 1133381) (by norm_num)
theorem B2014899 : Blo 2013435 2014899 := bstep (se 1 (by rfl) ⟨1511174, by rfl⟩ : syracuseStep 2014899 = 3022349) B3022349
theorem B4533533 : Blo 2013435 4533533 := bbase (se 3 (by rfl) ⟨850037, by rfl⟩ : syracuseStep 4533533 = 1700075) (by norm_num)
theorem B3022355 : Blo 2013435 3022355 := bstep (se 1 (by rfl) ⟨2266766, by rfl⟩ : syracuseStep 3022355 = 4533533) B4533533
theorem B2014903 : Blo 2013435 2014903 := bstep (se 1 (by rfl) ⟨1511177, by rfl⟩ : syracuseStep 2014903 = 3022355) B3022355
theorem B3400157 : Blo 2013435 3400157 := bbase (se 3 (by rfl) ⟨637529, by rfl⟩ : syracuseStep 3400157 = 1275059) (by norm_num)
theorem B2266771 : Blo 2013435 2266771 := bstep (se 1 (by rfl) ⟨1700078, by rfl⟩ : syracuseStep 2266771 = 3400157) B3400157
theorem B3022361 : Blo 2013435 3022361 := bstep (se 2 (by rfl) ⟨1133385, by rfl⟩ : syracuseStep 3022361 = 2266771) B2266771
theorem B2014907 : Blo 2013435 2014907 := bstep (se 1 (by rfl) ⟨1511180, by rfl⟩ : syracuseStep 2014907 = 3022361) B3022361
theorem B4084805 : Blo 2013435 4084805 := bbase (se 4 (by rfl) ⟨382950, by rfl⟩ : syracuseStep 4084805 = 765901) (by norm_num)
theorem B2723203 : Blo 2013435 2723203 := bstep (se 1 (by rfl) ⟨2042402, by rfl⟩ : syracuseStep 2723203 = 4084805) B4084805
theorem B14523749 : Blo 2013435 14523749 := bstep (se 4 (by rfl) ⟨1361601, by rfl⟩ : syracuseStep 14523749 = 2723203) B2723203
theorem B9682499 : Blo 2013435 9682499 := bstep (se 1 (by rfl) ⟨7261874, by rfl⟩ : syracuseStep 9682499 = 14523749) B14523749
theorem B6454999 : Blo 2013435 6454999 := bstep (se 1 (by rfl) ⟨4841249, by rfl⟩ : syracuseStep 6454999 = 9682499) B9682499
theorem B8606665 : Blo 2013435 8606665 := bstep (se 2 (by rfl) ⟨3227499, by rfl⟩ : syracuseStep 8606665 = 6454999) B6454999
theorem B11475553 : Blo 2013435 11475553 := bstep (se 2 (by rfl) ⟨4303332, by rfl⟩ : syracuseStep 11475553 = 8606665) B8606665
theorem B15300737 : Blo 2013435 15300737 := bstep (se 2 (by rfl) ⟨5737776, by rfl⟩ : syracuseStep 15300737 = 11475553) B11475553
theorem B10200491 : Blo 2013435 10200491 := bstep (se 1 (by rfl) ⟨7650368, by rfl⟩ : syracuseStep 10200491 = 15300737) B15300737
theorem B6800327 : Blo 2013435 6800327 := bstep (se 1 (by rfl) ⟨5100245, by rfl⟩ : syracuseStep 6800327 = 10200491) B10200491
theorem B4533551 : Blo 2013435 4533551 := bstep (se 1 (by rfl) ⟨3400163, by rfl⟩ : syracuseStep 4533551 = 6800327) B6800327
theorem B3022367 : Blo 2013435 3022367 := bstep (se 1 (by rfl) ⟨2266775, by rfl⟩ : syracuseStep 3022367 = 4533551) B4533551
theorem B2014911 : Blo 2013435 2014911 := bstep (se 1 (by rfl) ⟨1511183, by rfl⟩ : syracuseStep 2014911 = 3022367) B3022367
theorem B3022373 : Blo 2013435 3022373 := bbase (se 4 (by rfl) ⟨283347, by rfl⟩ : syracuseStep 3022373 = 566695) (by norm_num)
theorem B2014915 : Blo 2013435 2014915 := bstep (se 1 (by rfl) ⟨1511186, by rfl⟩ : syracuseStep 2014915 = 3022373) B3022373
theorem B2550133 : Blo 2013435 2550133 := bbase (se 5 (by rfl) ⟨119537, by rfl⟩ : syracuseStep 2550133 = 239075) (by norm_num)
theorem B3400177 : Blo 2013435 3400177 := bstep (se 2 (by rfl) ⟨1275066, by rfl⟩ : syracuseStep 3400177 = 2550133) B2550133
theorem B4533569 : Blo 2013435 4533569 := bstep (se 2 (by rfl) ⟨1700088, by rfl⟩ : syracuseStep 4533569 = 3400177) B3400177
theorem B3022379 : Blo 2013435 3022379 := bstep (se 1 (by rfl) ⟨2266784, by rfl⟩ : syracuseStep 3022379 = 4533569) B4533569
theorem B2014919 : Blo 2013435 2014919 := bstep (se 1 (by rfl) ⟨1511189, by rfl⟩ : syracuseStep 2014919 = 3022379) B3022379
theorem B2266789 : Blo 2013435 2266789 := bbase (se 4 (by rfl) ⟨212511, by rfl⟩ : syracuseStep 2266789 = 425023) (by norm_num)
theorem B3022385 : Blo 2013435 3022385 := bstep (se 2 (by rfl) ⟨1133394, by rfl⟩ : syracuseStep 3022385 = 2266789) B2266789
theorem B2014923 : Blo 2013435 2014923 := bstep (se 1 (by rfl) ⟨1511192, by rfl⟩ : syracuseStep 2014923 = 3022385) B3022385
theorem B3063629 : Blo 2013435 3063629 := bbase (se 3 (by rfl) ⟨574430, by rfl⟩ : syracuseStep 3063629 = 1148861) (by norm_num)
theorem B2042419 : Blo 2013435 2042419 := bstep (se 1 (by rfl) ⟨1531814, by rfl⟩ : syracuseStep 2042419 = 3063629) B3063629
theorem B2723225 : Blo 2013435 2723225 := bstep (se 2 (by rfl) ⟨1021209, by rfl⟩ : syracuseStep 2723225 = 2042419) B2042419
theorem B29047733 : Blo 2013435 29047733 := bstep (se 5 (by rfl) ⟨1361612, by rfl⟩ : syracuseStep 29047733 = 2723225) B2723225
theorem B19365155 : Blo 2013435 19365155 := bstep (se 1 (by rfl) ⟨14523866, by rfl⟩ : syracuseStep 19365155 = 29047733) B29047733
theorem B12910103 : Blo 2013435 12910103 := bstep (se 1 (by rfl) ⟨9682577, by rfl⟩ : syracuseStep 12910103 = 19365155) B19365155
theorem B8606735 : Blo 2013435 8606735 := bstep (se 1 (by rfl) ⟨6455051, by rfl⟩ : syracuseStep 8606735 = 12910103) B12910103
theorem B5737823 : Blo 2013435 5737823 := bstep (se 1 (by rfl) ⟨4303367, by rfl⟩ : syracuseStep 5737823 = 8606735) B8606735
theorem B3825215 : Blo 2013435 3825215 := bstep (se 1 (by rfl) ⟨2868911, by rfl⟩ : syracuseStep 3825215 = 5737823) B5737823
theorem B2550143 : Blo 2013435 2550143 := bstep (se 1 (by rfl) ⟨1912607, by rfl⟩ : syracuseStep 2550143 = 3825215) B3825215
theorem B6800381 : Blo 2013435 6800381 := bstep (se 3 (by rfl) ⟨1275071, by rfl⟩ : syracuseStep 6800381 = 2550143) B2550143
theorem B4533587 : Blo 2013435 4533587 := bstep (se 1 (by rfl) ⟨3400190, by rfl⟩ : syracuseStep 4533587 = 6800381) B6800381
theorem B3022391 : Blo 2013435 3022391 := bstep (se 1 (by rfl) ⟨2266793, by rfl⟩ : syracuseStep 3022391 = 4533587) B4533587
theorem B2014927 : Blo 2013435 2014927 := bstep (se 1 (by rfl) ⟨1511195, by rfl⟩ : syracuseStep 2014927 = 3022391) B3022391
theorem B3022397 : Blo 2013435 3022397 := bbase (se 3 (by rfl) ⟨566699, by rfl⟩ : syracuseStep 3022397 = 1133399) (by norm_num)
theorem B2014931 : Blo 2013435 2014931 := bstep (se 1 (by rfl) ⟨1511198, by rfl⟩ : syracuseStep 2014931 = 3022397) B3022397
theorem B4533605 : Blo 2013435 4533605 := bbase (se 4 (by rfl) ⟨425025, by rfl⟩ : syracuseStep 4533605 = 850051) (by norm_num)
theorem B3022403 : Blo 2013435 3022403 := bstep (se 1 (by rfl) ⟨2266802, by rfl⟩ : syracuseStep 3022403 = 4533605) B4533605
theorem B2014935 : Blo 2013435 2014935 := bstep (se 1 (by rfl) ⟨1511201, by rfl⟩ : syracuseStep 2014935 = 3022403) B3022403
theorem B5100317 : Blo 2013435 5100317 := bbase (se 3 (by rfl) ⟨956309, by rfl⟩ : syracuseStep 5100317 = 1912619) (by norm_num)
theorem B3400211 : Blo 2013435 3400211 := bstep (se 1 (by rfl) ⟨2550158, by rfl⟩ : syracuseStep 3400211 = 5100317) B5100317
theorem B2266807 : Blo 2013435 2266807 := bstep (se 1 (by rfl) ⟨1700105, by rfl⟩ : syracuseStep 2266807 = 3400211) B3400211
theorem B3022409 : Blo 2013435 3022409 := bstep (se 2 (by rfl) ⟨1133403, by rfl⟩ : syracuseStep 3022409 = 2266807) B2266807
theorem B2014939 : Blo 2013435 2014939 := bstep (se 1 (by rfl) ⟨1511204, by rfl⟩ : syracuseStep 2014939 = 3022409) B3022409
theorem B3825245 : Blo 2013435 3825245 := bbase (se 3 (by rfl) ⟨717233, by rfl⟩ : syracuseStep 3825245 = 1434467) (by norm_num)
theorem B10200653 : Blo 2013435 10200653 := bstep (se 3 (by rfl) ⟨1912622, by rfl⟩ : syracuseStep 10200653 = 3825245) B3825245
theorem B6800435 : Blo 2013435 6800435 := bstep (se 1 (by rfl) ⟨5100326, by rfl⟩ : syracuseStep 6800435 = 10200653) B10200653
theorem B4533623 : Blo 2013435 4533623 := bstep (se 1 (by rfl) ⟨3400217, by rfl⟩ : syracuseStep 4533623 = 6800435) B6800435
theorem B3022415 : Blo 2013435 3022415 := bstep (se 1 (by rfl) ⟨2266811, by rfl⟩ : syracuseStep 3022415 = 4533623) B4533623
theorem B2014943 : Blo 2013435 2014943 := bstep (se 1 (by rfl) ⟨1511207, by rfl⟩ : syracuseStep 2014943 = 3022415) B3022415
theorem B3022421 : Blo 2013435 3022421 := bbase (se 8 (by rfl) ⟨17709, by rfl⟩ : syracuseStep 3022421 = 35419) (by norm_num)
theorem B2014947 : Blo 2013435 2014947 := bstep (se 1 (by rfl) ⟨1511210, by rfl⟩ : syracuseStep 2014947 = 3022421) B3022421
theorem B8606837 : Blo 2013435 8606837 := bbase (se 5 (by rfl) ⟨403445, by rfl⟩ : syracuseStep 8606837 = 806891) (by norm_num)
theorem B5737891 : Blo 2013435 5737891 := bstep (se 1 (by rfl) ⟨4303418, by rfl⟩ : syracuseStep 5737891 = 8606837) B8606837
theorem B7650521 : Blo 2013435 7650521 := bstep (se 2 (by rfl) ⟨2868945, by rfl⟩ : syracuseStep 7650521 = 5737891) B5737891
theorem B5100347 : Blo 2013435 5100347 := bstep (se 1 (by rfl) ⟨3825260, by rfl⟩ : syracuseStep 5100347 = 7650521) B7650521
theorem B3400231 : Blo 2013435 3400231 := bstep (se 1 (by rfl) ⟨2550173, by rfl⟩ : syracuseStep 3400231 = 5100347) B5100347
theorem B4533641 : Blo 2013435 4533641 := bstep (se 2 (by rfl) ⟨1700115, by rfl⟩ : syracuseStep 4533641 = 3400231) B3400231
theorem B3022427 : Blo 2013435 3022427 := bstep (se 1 (by rfl) ⟨2266820, by rfl⟩ : syracuseStep 3022427 = 4533641) B4533641
theorem B2014951 : Blo 2013435 2014951 := bstep (se 1 (by rfl) ⟨1511213, by rfl⟩ : syracuseStep 2014951 = 3022427) B3022427
theorem B2266825 : Blo 2013435 2266825 := bbase (se 2 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 2266825 = 1700119) (by norm_num)
theorem B3022433 : Blo 2013435 3022433 := bstep (se 2 (by rfl) ⟨1133412, by rfl⟩ : syracuseStep 3022433 = 2266825) B2266825
theorem B2014955 : Blo 2013435 2014955 := bstep (se 1 (by rfl) ⟨1511216, by rfl⟩ : syracuseStep 2014955 = 3022433) B3022433
theorem B4841365 : Blo 2013435 4841365 := bbase (se 6 (by rfl) ⟨113469, by rfl⟩ : syracuseStep 4841365 = 226939) (by norm_num)
theorem B6455153 : Blo 2013435 6455153 := bstep (se 2 (by rfl) ⟨2420682, by rfl⟩ : syracuseStep 6455153 = 4841365) B4841365
theorem B17213741 : Blo 2013435 17213741 := bstep (se 3 (by rfl) ⟨3227576, by rfl⟩ : syracuseStep 17213741 = 6455153) B6455153
theorem B11475827 : Blo 2013435 11475827 := bstep (se 1 (by rfl) ⟨8606870, by rfl⟩ : syracuseStep 11475827 = 17213741) B17213741
theorem B7650551 : Blo 2013435 7650551 := bstep (se 1 (by rfl) ⟨5737913, by rfl⟩ : syracuseStep 7650551 = 11475827) B11475827
theorem B5100367 : Blo 2013435 5100367 := bstep (se 1 (by rfl) ⟨3825275, by rfl⟩ : syracuseStep 5100367 = 7650551) B7650551
theorem B6800489 : Blo 2013435 6800489 := bstep (se 2 (by rfl) ⟨2550183, by rfl⟩ : syracuseStep 6800489 = 5100367) B5100367
theorem B4533659 : Blo 2013435 4533659 := bstep (se 1 (by rfl) ⟨3400244, by rfl⟩ : syracuseStep 4533659 = 6800489) B6800489
theorem B3022439 : Blo 2013435 3022439 := bstep (se 1 (by rfl) ⟨2266829, by rfl⟩ : syracuseStep 3022439 = 4533659) B4533659
theorem B2014959 : Blo 2013435 2014959 := bstep (se 1 (by rfl) ⟨1511219, by rfl⟩ : syracuseStep 2014959 = 3022439) B3022439
theorem B3022445 : Blo 2013435 3022445 := bbase (se 3 (by rfl) ⟨566708, by rfl⟩ : syracuseStep 3022445 = 1133417) (by norm_num)
theorem B2014963 : Blo 2013435 2014963 := bstep (se 1 (by rfl) ⟨1511222, by rfl⟩ : syracuseStep 2014963 = 3022445) B3022445
theorem B4533677 : Blo 2013435 4533677 := bbase (se 3 (by rfl) ⟨850064, by rfl⟩ : syracuseStep 4533677 = 1700129) (by norm_num)
theorem B3022451 : Blo 2013435 3022451 := bstep (se 1 (by rfl) ⟨2266838, by rfl⟩ : syracuseStep 3022451 = 4533677) B4533677
theorem B2014967 : Blo 2013435 2014967 := bstep (se 1 (by rfl) ⟨1511225, by rfl⟩ : syracuseStep 2014967 = 3022451) B3022451
theorem B3227597 : Blo 2013435 3227597 := bbase (se 3 (by rfl) ⟨605174, by rfl⟩ : syracuseStep 3227597 = 1210349) (by norm_num)
theorem B2151731 : Blo 2013435 2151731 := bstep (se 1 (by rfl) ⟨1613798, by rfl⟩ : syracuseStep 2151731 = 3227597) B3227597
theorem B5737949 : Blo 2013435 5737949 := bstep (se 3 (by rfl) ⟨1075865, by rfl⟩ : syracuseStep 5737949 = 2151731) B2151731
theorem B3825299 : Blo 2013435 3825299 := bstep (se 1 (by rfl) ⟨2868974, by rfl⟩ : syracuseStep 3825299 = 5737949) B5737949
theorem B2550199 : Blo 2013435 2550199 := bstep (se 1 (by rfl) ⟨1912649, by rfl⟩ : syracuseStep 2550199 = 3825299) B3825299
theorem B3400265 : Blo 2013435 3400265 := bstep (se 2 (by rfl) ⟨1275099, by rfl⟩ : syracuseStep 3400265 = 2550199) B2550199
theorem B2266843 : Blo 2013435 2266843 := bstep (se 1 (by rfl) ⟨1700132, by rfl⟩ : syracuseStep 2266843 = 3400265) B3400265
theorem B3022457 : Blo 2013435 3022457 := bstep (se 2 (by rfl) ⟨1133421, by rfl⟩ : syracuseStep 3022457 = 2266843) B2266843
theorem B2014971 : Blo 2013435 2014971 := bstep (se 1 (by rfl) ⟨1511228, by rfl⟩ : syracuseStep 2014971 = 3022457) B3022457
theorem B5816245 : Blo 2013435 5816245 := bbase (se 5 (by rfl) ⟨272636, by rfl⟩ : syracuseStep 5816245 = 545273) (by norm_num)
theorem B7754993 : Blo 2013435 7754993 := bstep (se 2 (by rfl) ⟨2908122, by rfl⟩ : syracuseStep 7754993 = 5816245) B5816245
theorem B5169995 : Blo 2013435 5169995 := bstep (se 1 (by rfl) ⟨3877496, by rfl⟩ : syracuseStep 5169995 = 7754993) B7754993
theorem B3446663 : Blo 2013435 3446663 := bstep (se 1 (by rfl) ⟨2584997, by rfl⟩ : syracuseStep 3446663 = 5169995) B5169995
theorem B36764405 : Blo 2013435 36764405 := bstep (se 5 (by rfl) ⟨1723331, by rfl⟩ : syracuseStep 36764405 = 3446663) B3446663
theorem B24509603 : Blo 2013435 24509603 := bstep (se 1 (by rfl) ⟨18382202, by rfl⟩ : syracuseStep 24509603 = 36764405) B36764405
theorem B16339735 : Blo 2013435 16339735 := bstep (se 1 (by rfl) ⟨12254801, by rfl⟩ : syracuseStep 16339735 = 24509603) B24509603
theorem B87145253 : Blo 2013435 87145253 := bstep (se 4 (by rfl) ⟨8169867, by rfl⟩ : syracuseStep 87145253 = 16339735) B16339735
theorem B58096835 : Blo 2013435 58096835 := bstep (se 1 (by rfl) ⟨43572626, by rfl⟩ : syracuseStep 58096835 = 87145253) B87145253
theorem B38731223 : Blo 2013435 38731223 := bstep (se 1 (by rfl) ⟨29048417, by rfl⟩ : syracuseStep 38731223 = 58096835) B58096835
theorem B25820815 : Blo 2013435 25820815 := bstep (se 1 (by rfl) ⟨19365611, by rfl⟩ : syracuseStep 25820815 = 38731223) B38731223
theorem B34427753 : Blo 2013435 34427753 := bstep (se 2 (by rfl) ⟨12910407, by rfl⟩ : syracuseStep 34427753 = 25820815) B25820815
theorem B22951835 : Blo 2013435 22951835 := bstep (se 1 (by rfl) ⟨17213876, by rfl⟩ : syracuseStep 22951835 = 34427753) B34427753
theorem B15301223 : Blo 2013435 15301223 := bstep (se 1 (by rfl) ⟨11475917, by rfl⟩ : syracuseStep 15301223 = 22951835) B22951835
theorem B10200815 : Blo 2013435 10200815 := bstep (se 1 (by rfl) ⟨7650611, by rfl⟩ : syracuseStep 10200815 = 15301223) B15301223
theorem B6800543 : Blo 2013435 6800543 := bstep (se 1 (by rfl) ⟨5100407, by rfl⟩ : syracuseStep 6800543 = 10200815) B10200815
theorem B4533695 : Blo 2013435 4533695 := bstep (se 1 (by rfl) ⟨3400271, by rfl⟩ : syracuseStep 4533695 = 6800543) B6800543
theorem B3022463 : Blo 2013435 3022463 := bstep (se 1 (by rfl) ⟨2266847, by rfl⟩ : syracuseStep 3022463 = 4533695) B4533695
theorem B2014975 : Blo 2013435 2014975 := bstep (se 1 (by rfl) ⟨1511231, by rfl⟩ : syracuseStep 2014975 = 3022463) B3022463
theorem B3022469 : Blo 2013435 3022469 := bbase (se 4 (by rfl) ⟨283356, by rfl⟩ : syracuseStep 3022469 = 566713) (by norm_num)
theorem B2014979 : Blo 2013435 2014979 := bstep (se 1 (by rfl) ⟨1511234, by rfl⟩ : syracuseStep 2014979 = 3022469) B3022469
theorem B3400285 : Blo 2013435 3400285 := bbase (se 3 (by rfl) ⟨637553, by rfl⟩ : syracuseStep 3400285 = 1275107) (by norm_num)
theorem B4533713 : Blo 2013435 4533713 := bstep (se 2 (by rfl) ⟨1700142, by rfl⟩ : syracuseStep 4533713 = 3400285) B3400285
theorem B3022475 : Blo 2013435 3022475 := bstep (se 1 (by rfl) ⟨2266856, by rfl⟩ : syracuseStep 3022475 = 4533713) B4533713
theorem B2014983 : Blo 2013435 2014983 := bstep (se 1 (by rfl) ⟨1511237, by rfl⟩ : syracuseStep 2014983 = 3022475) B3022475
theorem B2266861 : Blo 2013435 2266861 := bbase (se 3 (by rfl) ⟨425036, by rfl⟩ : syracuseStep 2266861 = 850073) (by norm_num)
theorem B3022481 : Blo 2013435 3022481 := bstep (se 2 (by rfl) ⟨1133430, by rfl⟩ : syracuseStep 3022481 = 2266861) B2266861
theorem B2014987 : Blo 2013435 2014987 := bstep (se 1 (by rfl) ⟨1511240, by rfl⟩ : syracuseStep 2014987 = 3022481) B3022481
theorem B6800597 : Blo 2013435 6800597 := bbase (se 7 (by rfl) ⟨79694, by rfl⟩ : syracuseStep 6800597 = 159389) (by norm_num)
theorem B4533731 : Blo 2013435 4533731 := bstep (se 1 (by rfl) ⟨3400298, by rfl⟩ : syracuseStep 4533731 = 6800597) B6800597
theorem B3022487 : Blo 2013435 3022487 := bstep (se 1 (by rfl) ⟨2266865, by rfl⟩ : syracuseStep 3022487 = 4533731) B4533731
theorem B2014991 : Blo 2013435 2014991 := bstep (se 1 (by rfl) ⟨1511243, by rfl⟩ : syracuseStep 2014991 = 3022487) B3022487
theorem B3022493 : Blo 2013435 3022493 := bbase (se 3 (by rfl) ⟨566717, by rfl⟩ : syracuseStep 3022493 = 1133435) (by norm_num)
theorem B2014995 : Blo 2013435 2014995 := bstep (se 1 (by rfl) ⟨1511246, by rfl⟩ : syracuseStep 2014995 = 3022493) B3022493
theorem B4533749 : Blo 2013435 4533749 := bbase (se 5 (by rfl) ⟨212519, by rfl⟩ : syracuseStep 4533749 = 425039) (by norm_num)
theorem B3022499 : Blo 2013435 3022499 := bstep (se 1 (by rfl) ⟨2266874, by rfl⟩ : syracuseStep 3022499 = 4533749) B4533749
theorem B2014999 : Blo 2013435 2014999 := bstep (se 1 (by rfl) ⟨1511249, by rfl⟩ : syracuseStep 2014999 = 3022499) B3022499
theorem B2127241 : Blo 2013435 2127241 := bbase (se 2 (by rfl) ⟨797715, by rfl⟩ : syracuseStep 2127241 = 1595431) (by norm_num)
theorem B11345285 : Blo 2013435 11345285 := bstep (se 4 (by rfl) ⟨1063620, by rfl⟩ : syracuseStep 11345285 = 2127241) B2127241
theorem B7563523 : Blo 2013435 7563523 := bstep (se 1 (by rfl) ⟨5672642, by rfl⟩ : syracuseStep 7563523 = 11345285) B11345285
theorem B10084697 : Blo 2013435 10084697 := bstep (se 2 (by rfl) ⟨3781761, by rfl⟩ : syracuseStep 10084697 = 7563523) B7563523
theorem B6723131 : Blo 2013435 6723131 := bstep (se 1 (by rfl) ⟨5042348, by rfl⟩ : syracuseStep 6723131 = 10084697) B10084697
theorem B17928349 : Blo 2013435 17928349 := bstep (se 3 (by rfl) ⟨3361565, by rfl⟩ : syracuseStep 17928349 = 6723131) B6723131
theorem B382471445 : Blo 2013435 382471445 := bstep (se 6 (by rfl) ⟨8964174, by rfl⟩ : syracuseStep 382471445 = 17928349) B17928349
theorem B254980963 : Blo 2013435 254980963 := bstep (se 1 (by rfl) ⟨191235722, by rfl⟩ : syracuseStep 254980963 = 382471445) B382471445
theorem B339974617 : Blo 2013435 339974617 := bstep (se 2 (by rfl) ⟨127490481, by rfl⟩ : syracuseStep 339974617 = 254980963) B254980963
theorem B453299489 : Blo 2013435 453299489 := bstep (se 2 (by rfl) ⟨169987308, by rfl⟩ : syracuseStep 453299489 = 339974617) B339974617
theorem B302199659 : Blo 2013435 302199659 := bstep (se 1 (by rfl) ⟨226649744, by rfl⟩ : syracuseStep 302199659 = 453299489) B453299489
theorem B201466439 : Blo 2013435 201466439 := bstep (se 1 (by rfl) ⟨151099829, by rfl⟩ : syracuseStep 201466439 = 302199659) B302199659
theorem B134310959 : Blo 2013435 134310959 := bstep (se 1 (by rfl) ⟨100733219, by rfl⟩ : syracuseStep 134310959 = 201466439) B201466439
theorem B89540639 : Blo 2013435 89540639 := bstep (se 1 (by rfl) ⟨67155479, by rfl⟩ : syracuseStep 89540639 = 134310959) B134310959
theorem B59693759 : Blo 2013435 59693759 := bstep (se 1 (by rfl) ⟨44770319, by rfl⟩ : syracuseStep 59693759 = 89540639) B89540639
theorem B39795839 : Blo 2013435 39795839 := bstep (se 1 (by rfl) ⟨29846879, by rfl⟩ : syracuseStep 39795839 = 59693759) B59693759
theorem B26530559 : Blo 2013435 26530559 := bstep (se 1 (by rfl) ⟨19897919, by rfl⟩ : syracuseStep 26530559 = 39795839) B39795839
theorem B282992629 : Blo 2013435 282992629 := bstep (se 5 (by rfl) ⟨13265279, by rfl⟩ : syracuseStep 282992629 = 26530559) B26530559
theorem B377323505 : Blo 2013435 377323505 := bstep (se 2 (by rfl) ⟨141496314, by rfl⟩ : syracuseStep 377323505 = 282992629) B282992629
theorem B251549003 : Blo 2013435 251549003 := bstep (se 1 (by rfl) ⟨188661752, by rfl⟩ : syracuseStep 251549003 = 377323505) B377323505
theorem B167699335 : Blo 2013435 167699335 := bstep (se 1 (by rfl) ⟨125774501, by rfl⟩ : syracuseStep 167699335 = 251549003) B251549003
theorem B223599113 : Blo 2013435 223599113 := bstep (se 2 (by rfl) ⟨83849667, by rfl⟩ : syracuseStep 223599113 = 167699335) B167699335
theorem B149066075 : Blo 2013435 149066075 := bstep (se 1 (by rfl) ⟨111799556, by rfl⟩ : syracuseStep 149066075 = 223599113) B223599113
theorem B99377383 : Blo 2013435 99377383 := bstep (se 1 (by rfl) ⟨74533037, by rfl⟩ : syracuseStep 99377383 = 149066075) B149066075
theorem B132503177 : Blo 2013435 132503177 := bstep (se 2 (by rfl) ⟨49688691, by rfl⟩ : syracuseStep 132503177 = 99377383) B99377383
theorem B88335451 : Blo 2013435 88335451 := bstep (se 1 (by rfl) ⟨66251588, by rfl⟩ : syracuseStep 88335451 = 132503177) B132503177
theorem B117780601 : Blo 2013435 117780601 := bstep (se 2 (by rfl) ⟨44167725, by rfl⟩ : syracuseStep 117780601 = 88335451) B88335451
theorem B157040801 : Blo 2013435 157040801 := bstep (se 2 (by rfl) ⟨58890300, by rfl⟩ : syracuseStep 157040801 = 117780601) B117780601
theorem B104693867 : Blo 2013435 104693867 := bstep (se 1 (by rfl) ⟨78520400, by rfl⟩ : syracuseStep 104693867 = 157040801) B157040801
theorem B69795911 : Blo 2013435 69795911 := bstep (se 1 (by rfl) ⟨52346933, by rfl⟩ : syracuseStep 69795911 = 104693867) B104693867
theorem B46530607 : Blo 2013435 46530607 := bstep (se 1 (by rfl) ⟨34897955, by rfl⟩ : syracuseStep 46530607 = 69795911) B69795911
theorem B62040809 : Blo 2013435 62040809 := bstep (se 2 (by rfl) ⟨23265303, by rfl⟩ : syracuseStep 62040809 = 46530607) B46530607
theorem B41360539 : Blo 2013435 41360539 := bstep (se 1 (by rfl) ⟨31020404, by rfl⟩ : syracuseStep 41360539 = 62040809) B62040809
theorem B55147385 : Blo 2013435 55147385 := bstep (se 2 (by rfl) ⟨20680269, by rfl⟩ : syracuseStep 55147385 = 41360539) B41360539
theorem B36764923 : Blo 2013435 36764923 := bstep (se 1 (by rfl) ⟨27573692, by rfl⟩ : syracuseStep 36764923 = 55147385) B55147385
theorem B49019897 : Blo 2013435 49019897 := bstep (se 2 (by rfl) ⟨18382461, by rfl⟩ : syracuseStep 49019897 = 36764923) B36764923
theorem B32679931 : Blo 2013435 32679931 := bstep (se 1 (by rfl) ⟨24509948, by rfl⟩ : syracuseStep 32679931 = 49019897) B49019897
theorem B43573241 : Blo 2013435 43573241 := bstep (se 2 (by rfl) ⟨16339965, by rfl⟩ : syracuseStep 43573241 = 32679931) B32679931
theorem B29048827 : Blo 2013435 29048827 := bstep (se 1 (by rfl) ⟨21786620, by rfl⟩ : syracuseStep 29048827 = 43573241) B43573241
theorem B38731769 : Blo 2013435 38731769 := bstep (se 2 (by rfl) ⟨14524413, by rfl⟩ : syracuseStep 38731769 = 29048827) B29048827
theorem B25821179 : Blo 2013435 25821179 := bstep (se 1 (by rfl) ⟨19365884, by rfl⟩ : syracuseStep 25821179 = 38731769) B38731769
theorem B17214119 : Blo 2013435 17214119 := bstep (se 1 (by rfl) ⟨12910589, by rfl⟩ : syracuseStep 17214119 = 25821179) B25821179
theorem B11476079 : Blo 2013435 11476079 := bstep (se 1 (by rfl) ⟨8607059, by rfl⟩ : syracuseStep 11476079 = 17214119) B17214119
theorem B7650719 : Blo 2013435 7650719 := bstep (se 1 (by rfl) ⟨5738039, by rfl⟩ : syracuseStep 7650719 = 11476079) B11476079
theorem B5100479 : Blo 2013435 5100479 := bstep (se 1 (by rfl) ⟨3825359, by rfl⟩ : syracuseStep 5100479 = 7650719) B7650719
theorem B3400319 : Blo 2013435 3400319 := bstep (se 1 (by rfl) ⟨2550239, by rfl⟩ : syracuseStep 3400319 = 5100479) B5100479
theorem B2266879 : Blo 2013435 2266879 := bstep (se 1 (by rfl) ⟨1700159, by rfl⟩ : syracuseStep 2266879 = 3400319) B3400319
theorem B3022505 : Blo 2013435 3022505 := bstep (se 2 (by rfl) ⟨1133439, by rfl⟩ : syracuseStep 3022505 = 2266879) B2266879
theorem B2015003 : Blo 2013435 2015003 := bstep (se 1 (by rfl) ⟨1511252, by rfl⟩ : syracuseStep 2015003 = 3022505) B3022505
theorem B2151769 : Blo 2013435 2151769 := bbase (se 2 (by rfl) ⟨806913, by rfl⟩ : syracuseStep 2151769 = 1613827) (by norm_num)
theorem B2869025 : Blo 2013435 2869025 := bstep (se 2 (by rfl) ⟨1075884, by rfl⟩ : syracuseStep 2869025 = 2151769) B2151769
theorem B7650733 : Blo 2013435 7650733 := bstep (se 3 (by rfl) ⟨1434512, by rfl⟩ : syracuseStep 7650733 = 2869025) B2869025
theorem B10200977 : Blo 2013435 10200977 := bstep (se 2 (by rfl) ⟨3825366, by rfl⟩ : syracuseStep 10200977 = 7650733) B7650733
theorem B6800651 : Blo 2013435 6800651 := bstep (se 1 (by rfl) ⟨5100488, by rfl⟩ : syracuseStep 6800651 = 10200977) B10200977
theorem B4533767 : Blo 2013435 4533767 := bstep (se 1 (by rfl) ⟨3400325, by rfl⟩ : syracuseStep 4533767 = 6800651) B6800651
theorem B3022511 : Blo 2013435 3022511 := bstep (se 1 (by rfl) ⟨2266883, by rfl⟩ : syracuseStep 3022511 = 4533767) B4533767
theorem B2015007 : Blo 2013435 2015007 := bstep (se 1 (by rfl) ⟨1511255, by rfl⟩ : syracuseStep 2015007 = 3022511) B3022511
theorem B3022517 : Blo 2013435 3022517 := bbase (se 5 (by rfl) ⟨141680, by rfl⟩ : syracuseStep 3022517 = 283361) (by norm_num)
theorem B2015011 : Blo 2013435 2015011 := bstep (se 1 (by rfl) ⟨1511258, by rfl⟩ : syracuseStep 2015011 = 3022517) B3022517
theorem B5100509 : Blo 2013435 5100509 := bbase (se 3 (by rfl) ⟨956345, by rfl⟩ : syracuseStep 5100509 = 1912691) (by norm_num)
theorem B3400339 : Blo 2013435 3400339 := bstep (se 1 (by rfl) ⟨2550254, by rfl⟩ : syracuseStep 3400339 = 5100509) B5100509
theorem B4533785 : Blo 2013435 4533785 := bstep (se 2 (by rfl) ⟨1700169, by rfl⟩ : syracuseStep 4533785 = 3400339) B3400339
theorem B3022523 : Blo 2013435 3022523 := bstep (se 1 (by rfl) ⟨2266892, by rfl⟩ : syracuseStep 3022523 = 4533785) B4533785
theorem B2015015 : Blo 2013435 2015015 := bstep (se 1 (by rfl) ⟨1511261, by rfl⟩ : syracuseStep 2015015 = 3022523) B3022523
theorem B2266897 : Blo 2013435 2266897 := bbase (se 2 (by rfl) ⟨850086, by rfl⟩ : syracuseStep 2266897 = 1700173) (by norm_num)
theorem B3022529 : Blo 2013435 3022529 := bstep (se 2 (by rfl) ⟨1133448, by rfl⟩ : syracuseStep 3022529 = 2266897) B2266897
theorem B2015019 : Blo 2013435 2015019 := bstep (se 1 (by rfl) ⟨1511264, by rfl⟩ : syracuseStep 2015019 = 3022529) B3022529
theorem B3825397 : Blo 2013435 3825397 := bbase (se 5 (by rfl) ⟨179315, by rfl⟩ : syracuseStep 3825397 = 358631) (by norm_num)
theorem B5100529 : Blo 2013435 5100529 := bstep (se 2 (by rfl) ⟨1912698, by rfl⟩ : syracuseStep 5100529 = 3825397) B3825397
theorem B6800705 : Blo 2013435 6800705 := bstep (se 2 (by rfl) ⟨2550264, by rfl⟩ : syracuseStep 6800705 = 5100529) B5100529
theorem B4533803 : Blo 2013435 4533803 := bstep (se 1 (by rfl) ⟨3400352, by rfl⟩ : syracuseStep 4533803 = 6800705) B6800705
theorem B3022535 : Blo 2013435 3022535 := bstep (se 1 (by rfl) ⟨2266901, by rfl⟩ : syracuseStep 3022535 = 4533803) B4533803
theorem B2015023 : Blo 2013435 2015023 := bstep (se 1 (by rfl) ⟨1511267, by rfl⟩ : syracuseStep 2015023 = 3022535) B3022535
theorem B3022541 : Blo 2013435 3022541 := bbase (se 3 (by rfl) ⟨566726, by rfl⟩ : syracuseStep 3022541 = 1133453) (by norm_num)
theorem B2015027 : Blo 2013435 2015027 := bstep (se 1 (by rfl) ⟨1511270, by rfl⟩ : syracuseStep 2015027 = 3022541) B3022541
theorem B4533821 : Blo 2013435 4533821 := bbase (se 3 (by rfl) ⟨850091, by rfl⟩ : syracuseStep 4533821 = 1700183) (by norm_num)
theorem B3022547 : Blo 2013435 3022547 := bstep (se 1 (by rfl) ⟨2266910, by rfl⟩ : syracuseStep 3022547 = 4533821) B4533821
theorem B2015031 : Blo 2013435 2015031 := bstep (se 1 (by rfl) ⟨1511273, by rfl⟩ : syracuseStep 2015031 = 3022547) B3022547
theorem B3400373 : Blo 2013435 3400373 := bbase (se 5 (by rfl) ⟨159392, by rfl⟩ : syracuseStep 3400373 = 318785) (by norm_num)
theorem B2266915 : Blo 2013435 2266915 := bstep (se 1 (by rfl) ⟨1700186, by rfl⟩ : syracuseStep 2266915 = 3400373) B3400373
theorem B3022553 : Blo 2013435 3022553 := bstep (se 2 (by rfl) ⟨1133457, by rfl⟩ : syracuseStep 3022553 = 2266915) B2266915
theorem B2015035 : Blo 2013435 2015035 := bstep (se 1 (by rfl) ⟨1511276, by rfl⟩ : syracuseStep 2015035 = 3022553) B3022553
theorem B2042533 : Blo 2013435 2042533 := bbase (se 4 (by rfl) ⟨191487, by rfl⟩ : syracuseStep 2042533 = 382975) (by norm_num)
theorem B2723377 : Blo 2013435 2723377 := bstep (se 2 (by rfl) ⟨1021266, by rfl⟩ : syracuseStep 2723377 = 2042533) B2042533
theorem B3631169 : Blo 2013435 3631169 := bstep (se 2 (by rfl) ⟨1361688, by rfl⟩ : syracuseStep 3631169 = 2723377) B2723377
theorem B2420779 : Blo 2013435 2420779 := bstep (se 1 (by rfl) ⟨1815584, by rfl⟩ : syracuseStep 2420779 = 3631169) B3631169
theorem B3227705 : Blo 2013435 3227705 := bstep (se 2 (by rfl) ⟨1210389, by rfl⟩ : syracuseStep 3227705 = 2420779) B2420779
theorem B2151803 : Blo 2013435 2151803 := bstep (se 1 (by rfl) ⟨1613852, by rfl⟩ : syracuseStep 2151803 = 3227705) B3227705
theorem B5738141 : Blo 2013435 5738141 := bstep (se 3 (by rfl) ⟨1075901, by rfl⟩ : syracuseStep 5738141 = 2151803) B2151803
theorem B15301709 : Blo 2013435 15301709 := bstep (se 3 (by rfl) ⟨2869070, by rfl⟩ : syracuseStep 15301709 = 5738141) B5738141
theorem B10201139 : Blo 2013435 10201139 := bstep (se 1 (by rfl) ⟨7650854, by rfl⟩ : syracuseStep 10201139 = 15301709) B15301709
theorem B6800759 : Blo 2013435 6800759 := bstep (se 1 (by rfl) ⟨5100569, by rfl⟩ : syracuseStep 6800759 = 10201139) B10201139
theorem B4533839 : Blo 2013435 4533839 := bstep (se 1 (by rfl) ⟨3400379, by rfl⟩ : syracuseStep 4533839 = 6800759) B6800759
theorem B3022559 : Blo 2013435 3022559 := bstep (se 1 (by rfl) ⟨2266919, by rfl⟩ : syracuseStep 3022559 = 4533839) B4533839
theorem B2015039 : Blo 2013435 2015039 := bstep (se 1 (by rfl) ⟨1511279, by rfl⟩ : syracuseStep 2015039 = 3022559) B3022559
theorem B3022565 : Blo 2013435 3022565 := bbase (se 4 (by rfl) ⟨283365, by rfl⟩ : syracuseStep 3022565 = 566731) (by norm_num)
theorem B2015043 : Blo 2013435 2015043 := bstep (se 1 (by rfl) ⟨1511282, by rfl⟩ : syracuseStep 2015043 = 3022565) B3022565
theorem B5738165 : Blo 2013435 5738165 := bbase (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) (by norm_num)
theorem B3825443 : Blo 2013435 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B2550295 : Blo 2013435 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B3400393 : Blo 2013435 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B4533857 : Blo 2013435 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B3022571 : Blo 2013435 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B2015047 : Blo 2013435 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B2266933 : Blo 2013435 2266933 := bbase (se 5 (by rfl) ⟨106262, by rfl⟩ : syracuseStep 2266933 = 212525) (by norm_num)
theorem B3022577 : Blo 2013435 3022577 := bstep (se 2 (by rfl) ⟨1133466, by rfl⟩ : syracuseStep 3022577 = 2266933) B2266933
theorem B2015051 : Blo 2013435 2015051 := bstep (se 1 (by rfl) ⟨1511288, by rfl⟩ : syracuseStep 2015051 = 3022577) B3022577
theorem B2550305 : Blo 2013435 2550305 := bbase (se 2 (by rfl) ⟨956364, by rfl⟩ : syracuseStep 2550305 = 1912729) (by norm_num)
theorem B6800813 : Blo 2013435 6800813 := bstep (se 3 (by rfl) ⟨1275152, by rfl⟩ : syracuseStep 6800813 = 2550305) B2550305
theorem B4533875 : Blo 2013435 4533875 := bstep (se 1 (by rfl) ⟨3400406, by rfl⟩ : syracuseStep 4533875 = 6800813) B6800813
theorem B3022583 : Blo 2013435 3022583 := bstep (se 1 (by rfl) ⟨2266937, by rfl⟩ : syracuseStep 3022583 = 4533875) B4533875
theorem B2015055 : Blo 2013435 2015055 := bstep (se 1 (by rfl) ⟨1511291, by rfl⟩ : syracuseStep 2015055 = 3022583) B3022583
theorem B3022589 : Blo 2013435 3022589 := bbase (se 3 (by rfl) ⟨566735, by rfl⟩ : syracuseStep 3022589 = 1133471) (by norm_num)
theorem B2015059 : Blo 2013435 2015059 := bstep (se 1 (by rfl) ⟨1511294, by rfl⟩ : syracuseStep 2015059 = 3022589) B3022589
theorem B4533893 : Blo 2013435 4533893 := bbase (se 4 (by rfl) ⟨425052, by rfl⟩ : syracuseStep 4533893 = 850105) (by norm_num)
theorem B3022595 : Blo 2013435 3022595 := bstep (se 1 (by rfl) ⟨2266946, by rfl⟩ : syracuseStep 3022595 = 4533893) B4533893
theorem B2015063 : Blo 2013435 2015063 := bstep (se 1 (by rfl) ⟨1511297, by rfl⟩ : syracuseStep 2015063 = 3022595) B3022595
theorem B2420813 : Blo 2013435 2420813 := bbase (se 3 (by rfl) ⟨453902, by rfl⟩ : syracuseStep 2420813 = 907805) (by norm_num)
theorem B6455501 : Blo 2013435 6455501 := bstep (se 3 (by rfl) ⟨1210406, by rfl⟩ : syracuseStep 6455501 = 2420813) B2420813
theorem B4303667 : Blo 2013435 4303667 := bstep (se 1 (by rfl) ⟨3227750, by rfl⟩ : syracuseStep 4303667 = 6455501) B6455501
theorem B2869111 : Blo 2013435 2869111 := bstep (se 1 (by rfl) ⟨2151833, by rfl⟩ : syracuseStep 2869111 = 4303667) B4303667
theorem B3825481 : Blo 2013435 3825481 := bstep (se 2 (by rfl) ⟨1434555, by rfl⟩ : syracuseStep 3825481 = 2869111) B2869111
theorem B5100641 : Blo 2013435 5100641 := bstep (se 2 (by rfl) ⟨1912740, by rfl⟩ : syracuseStep 5100641 = 3825481) B3825481
theorem B3400427 : Blo 2013435 3400427 := bstep (se 1 (by rfl) ⟨2550320, by rfl⟩ : syracuseStep 3400427 = 5100641) B5100641
theorem B2266951 : Blo 2013435 2266951 := bstep (se 1 (by rfl) ⟨1700213, by rfl⟩ : syracuseStep 2266951 = 3400427) B3400427
theorem B3022601 : Blo 2013435 3022601 := bstep (se 2 (by rfl) ⟨1133475, by rfl⟩ : syracuseStep 3022601 = 2266951) B2266951
theorem B2015067 : Blo 2013435 2015067 := bstep (se 1 (by rfl) ⟨1511300, by rfl⟩ : syracuseStep 2015067 = 3022601) B3022601
theorem B10201301 : Blo 2013435 10201301 := bbase (se 7 (by rfl) ⟨119546, by rfl⟩ : syracuseStep 10201301 = 239093) (by norm_num)
theorem B6800867 : Blo 2013435 6800867 := bstep (se 1 (by rfl) ⟨5100650, by rfl⟩ : syracuseStep 6800867 = 10201301) B10201301
theorem B4533911 : Blo 2013435 4533911 := bstep (se 1 (by rfl) ⟨3400433, by rfl⟩ : syracuseStep 4533911 = 6800867) B6800867
theorem B3022607 : Blo 2013435 3022607 := bstep (se 1 (by rfl) ⟨2266955, by rfl⟩ : syracuseStep 3022607 = 4533911) B4533911
theorem B2015071 : Blo 2013435 2015071 := bstep (se 1 (by rfl) ⟨1511303, by rfl⟩ : syracuseStep 2015071 = 3022607) B3022607
theorem B3022613 : Blo 2013435 3022613 := bbase (se 6 (by rfl) ⟨70842, by rfl⟩ : syracuseStep 3022613 = 141685) (by norm_num)
theorem B2015075 : Blo 2013435 2015075 := bstep (se 1 (by rfl) ⟨1511306, by rfl⟩ : syracuseStep 2015075 = 3022613) B3022613
theorem B2181205 : Blo 2013435 2181205 := bbase (se 8 (by rfl) ⟨12780, by rfl⟩ : syracuseStep 2181205 = 25561) (by norm_num)
theorem B2908273 : Blo 2013435 2908273 := bstep (se 2 (by rfl) ⟨1090602, by rfl⟩ : syracuseStep 2908273 = 2181205) B2181205
theorem B3877697 : Blo 2013435 3877697 := bstep (se 2 (by rfl) ⟨1454136, by rfl⟩ : syracuseStep 3877697 = 2908273) B2908273
theorem B2585131 : Blo 2013435 2585131 := bstep (se 1 (by rfl) ⟨1938848, by rfl⟩ : syracuseStep 2585131 = 3877697) B3877697
theorem B55149461 : Blo 2013435 55149461 := bstep (se 6 (by rfl) ⟨1292565, by rfl⟩ : syracuseStep 55149461 = 2585131) B2585131
theorem B36766307 : Blo 2013435 36766307 := bstep (se 1 (by rfl) ⟨27574730, by rfl⟩ : syracuseStep 36766307 = 55149461) B55149461
theorem B24510871 : Blo 2013435 24510871 := bstep (se 1 (by rfl) ⟨18383153, by rfl⟩ : syracuseStep 24510871 = 36766307) B36766307
theorem B32681161 : Blo 2013435 32681161 := bstep (se 2 (by rfl) ⟨12255435, by rfl⟩ : syracuseStep 32681161 = 24510871) B24510871
theorem B43574881 : Blo 2013435 43574881 := bstep (se 2 (by rfl) ⟨16340580, by rfl⟩ : syracuseStep 43574881 = 32681161) B32681161
theorem B58099841 : Blo 2013435 58099841 := bstep (se 2 (by rfl) ⟨21787440, by rfl⟩ : syracuseStep 58099841 = 43574881) B43574881
theorem B38733227 : Blo 2013435 38733227 := bstep (se 1 (by rfl) ⟨29049920, by rfl⟩ : syracuseStep 38733227 = 58099841) B58099841
theorem B25822151 : Blo 2013435 25822151 := bstep (se 1 (by rfl) ⟨19366613, by rfl⟩ : syracuseStep 25822151 = 38733227) B38733227
theorem B17214767 : Blo 2013435 17214767 := bstep (se 1 (by rfl) ⟨12911075, by rfl⟩ : syracuseStep 17214767 = 25822151) B25822151
theorem B11476511 : Blo 2013435 11476511 := bstep (se 1 (by rfl) ⟨8607383, by rfl⟩ : syracuseStep 11476511 = 17214767) B17214767
theorem B7651007 : Blo 2013435 7651007 := bstep (se 1 (by rfl) ⟨5738255, by rfl⟩ : syracuseStep 7651007 = 11476511) B11476511
theorem B5100671 : Blo 2013435 5100671 := bstep (se 1 (by rfl) ⟨3825503, by rfl⟩ : syracuseStep 5100671 = 7651007) B7651007
theorem B3400447 : Blo 2013435 3400447 := bstep (se 1 (by rfl) ⟨2550335, by rfl⟩ : syracuseStep 3400447 = 5100671) B5100671
theorem B4533929 : Blo 2013435 4533929 := bstep (se 2 (by rfl) ⟨1700223, by rfl⟩ : syracuseStep 4533929 = 3400447) B3400447
theorem B3022619 : Blo 2013435 3022619 := bstep (se 1 (by rfl) ⟨2266964, by rfl⟩ : syracuseStep 3022619 = 4533929) B4533929
theorem B2015079 : Blo 2013435 2015079 := bstep (se 1 (by rfl) ⟨1511309, by rfl⟩ : syracuseStep 2015079 = 3022619) B3022619
theorem B2266969 : Blo 2013435 2266969 := bbase (se 2 (by rfl) ⟨850113, by rfl⟩ : syracuseStep 2266969 = 1700227) (by norm_num)
theorem B3022625 : Blo 2013435 3022625 := bstep (se 2 (by rfl) ⟨1133484, by rfl⟩ : syracuseStep 3022625 = 2266969) B2266969
theorem B2015083 : Blo 2013435 2015083 := bstep (se 1 (by rfl) ⟨1511312, by rfl⟩ : syracuseStep 2015083 = 3022625) B3022625
theorem B4303709 : Blo 2013435 4303709 := bbase (se 3 (by rfl) ⟨806945, by rfl⟩ : syracuseStep 4303709 = 1613891) (by norm_num)
theorem B2869139 : Blo 2013435 2869139 := bstep (se 1 (by rfl) ⟨2151854, by rfl⟩ : syracuseStep 2869139 = 4303709) B4303709
theorem B7651037 : Blo 2013435 7651037 := bstep (se 3 (by rfl) ⟨1434569, by rfl⟩ : syracuseStep 7651037 = 2869139) B2869139
theorem B5100691 : Blo 2013435 5100691 := bstep (se 1 (by rfl) ⟨3825518, by rfl⟩ : syracuseStep 5100691 = 7651037) B7651037
theorem B6800921 : Blo 2013435 6800921 := bstep (se 2 (by rfl) ⟨2550345, by rfl⟩ : syracuseStep 6800921 = 5100691) B5100691
theorem B4533947 : Blo 2013435 4533947 := bstep (se 1 (by rfl) ⟨3400460, by rfl⟩ : syracuseStep 4533947 = 6800921) B6800921
theorem B3022631 : Blo 2013435 3022631 := bstep (se 1 (by rfl) ⟨2266973, by rfl⟩ : syracuseStep 3022631 = 4533947) B4533947
theorem B2015087 : Blo 2013435 2015087 := bstep (se 1 (by rfl) ⟨1511315, by rfl⟩ : syracuseStep 2015087 = 3022631) B3022631
theorem B3022637 : Blo 2013435 3022637 := bbase (se 3 (by rfl) ⟨566744, by rfl⟩ : syracuseStep 3022637 = 1133489) (by norm_num)
theorem B2015091 : Blo 2013435 2015091 := bstep (se 1 (by rfl) ⟨1511318, by rfl⟩ : syracuseStep 2015091 = 3022637) B3022637
theorem B4533965 : Blo 2013435 4533965 := bbase (se 3 (by rfl) ⟨850118, by rfl⟩ : syracuseStep 4533965 = 1700237) (by norm_num)
theorem B3022643 : Blo 2013435 3022643 := bstep (se 1 (by rfl) ⟨2266982, by rfl⟩ : syracuseStep 3022643 = 4533965) B4533965
theorem B2015095 : Blo 2013435 2015095 := bstep (se 1 (by rfl) ⟨1511321, by rfl⟩ : syracuseStep 2015095 = 3022643) B3022643
theorem B2550361 : Blo 2013435 2550361 := bbase (se 2 (by rfl) ⟨956385, by rfl⟩ : syracuseStep 2550361 = 1912771) (by norm_num)
theorem B3400481 : Blo 2013435 3400481 := bstep (se 2 (by rfl) ⟨1275180, by rfl⟩ : syracuseStep 3400481 = 2550361) B2550361
theorem B2266987 : Blo 2013435 2266987 := bstep (se 1 (by rfl) ⟨1700240, by rfl⟩ : syracuseStep 2266987 = 3400481) B3400481
theorem B3022649 : Blo 2013435 3022649 := bstep (se 2 (by rfl) ⟨1133493, by rfl⟩ : syracuseStep 3022649 = 2266987) B2266987
theorem B2015099 : Blo 2013435 2015099 := bstep (se 1 (by rfl) ⟨1511324, by rfl⟩ : syracuseStep 2015099 = 3022649) B3022649
theorem B6211397 : Blo 2013435 6211397 := bbase (se 4 (by rfl) ⟨582318, by rfl⟩ : syracuseStep 6211397 = 1164637) (by norm_num)
theorem B4140931 : Blo 2013435 4140931 := bstep (se 1 (by rfl) ⟨3105698, by rfl⟩ : syracuseStep 4140931 = 6211397) B6211397
theorem B5521241 : Blo 2013435 5521241 := bstep (se 2 (by rfl) ⟨2070465, by rfl⟩ : syracuseStep 5521241 = 4140931) B4140931
theorem B14723309 : Blo 2013435 14723309 := bstep (se 3 (by rfl) ⟨2760620, by rfl⟩ : syracuseStep 14723309 = 5521241) B5521241
theorem B9815539 : Blo 2013435 9815539 := bstep (se 1 (by rfl) ⟨7361654, by rfl⟩ : syracuseStep 9815539 = 14723309) B14723309
theorem B13087385 : Blo 2013435 13087385 := bstep (se 2 (by rfl) ⟨4907769, by rfl⟩ : syracuseStep 13087385 = 9815539) B9815539
theorem B8724923 : Blo 2013435 8724923 := bstep (se 1 (by rfl) ⟨6543692, by rfl⟩ : syracuseStep 8724923 = 13087385) B13087385
theorem B5816615 : Blo 2013435 5816615 := bstep (se 1 (by rfl) ⟨4362461, by rfl⟩ : syracuseStep 5816615 = 8724923) B8724923
theorem B62043893 : Blo 2013435 62043893 := bstep (se 5 (by rfl) ⟨2908307, by rfl⟩ : syracuseStep 62043893 = 5816615) B5816615
theorem B41362595 : Blo 2013435 41362595 := bstep (se 1 (by rfl) ⟨31021946, by rfl⟩ : syracuseStep 41362595 = 62043893) B62043893
theorem B27575063 : Blo 2013435 27575063 := bstep (se 1 (by rfl) ⟨20681297, by rfl⟩ : syracuseStep 27575063 = 41362595) B41362595
theorem B18383375 : Blo 2013435 18383375 := bstep (se 1 (by rfl) ⟨13787531, by rfl⟩ : syracuseStep 18383375 = 27575063) B27575063
theorem B12255583 : Blo 2013435 12255583 := bstep (se 1 (by rfl) ⟨9191687, by rfl⟩ : syracuseStep 12255583 = 18383375) B18383375
theorem B16340777 : Blo 2013435 16340777 := bstep (se 2 (by rfl) ⟨6127791, by rfl⟩ : syracuseStep 16340777 = 12255583) B12255583
theorem B10893851 : Blo 2013435 10893851 := bstep (se 1 (by rfl) ⟨8170388, by rfl⟩ : syracuseStep 10893851 = 16340777) B16340777
theorem B7262567 : Blo 2013435 7262567 := bstep (se 1 (by rfl) ⟨5446925, by rfl⟩ : syracuseStep 7262567 = 10893851) B10893851
theorem B4841711 : Blo 2013435 4841711 := bstep (se 1 (by rfl) ⟨3631283, by rfl⟩ : syracuseStep 4841711 = 7262567) B7262567
theorem B3227807 : Blo 2013435 3227807 := bstep (se 1 (by rfl) ⟨2420855, by rfl⟩ : syracuseStep 3227807 = 4841711) B4841711
theorem B8607485 : Blo 2013435 8607485 := bstep (se 3 (by rfl) ⟨1613903, by rfl⟩ : syracuseStep 8607485 = 3227807) B3227807
theorem B22953293 : Blo 2013435 22953293 := bstep (se 3 (by rfl) ⟨4303742, by rfl⟩ : syracuseStep 22953293 = 8607485) B8607485
theorem B15302195 : Blo 2013435 15302195 := bstep (se 1 (by rfl) ⟨11476646, by rfl⟩ : syracuseStep 15302195 = 22953293) B22953293
theorem B10201463 : Blo 2013435 10201463 := bstep (se 1 (by rfl) ⟨7651097, by rfl⟩ : syracuseStep 10201463 = 15302195) B15302195
theorem B6800975 : Blo 2013435 6800975 := bstep (se 1 (by rfl) ⟨5100731, by rfl⟩ : syracuseStep 6800975 = 10201463) B10201463
theorem B4533983 : Blo 2013435 4533983 := bstep (se 1 (by rfl) ⟨3400487, by rfl⟩ : syracuseStep 4533983 = 6800975) B6800975
theorem B3022655 : Blo 2013435 3022655 := bstep (se 1 (by rfl) ⟨2266991, by rfl⟩ : syracuseStep 3022655 = 4533983) B4533983
theorem B2015103 : Blo 2013435 2015103 := bstep (se 1 (by rfl) ⟨1511327, by rfl⟩ : syracuseStep 2015103 = 3022655) B3022655
theorem B3022661 : Blo 2013435 3022661 := bbase (se 4 (by rfl) ⟨283374, by rfl⟩ : syracuseStep 3022661 = 566749) (by norm_num)
theorem B2015107 : Blo 2013435 2015107 := bstep (se 1 (by rfl) ⟨1511330, by rfl⟩ : syracuseStep 2015107 = 3022661) B3022661
theorem B3400501 : Blo 2013435 3400501 := bbase (se 5 (by rfl) ⟨159398, by rfl⟩ : syracuseStep 3400501 = 318797) (by norm_num)
theorem B4534001 : Blo 2013435 4534001 := bstep (se 2 (by rfl) ⟨1700250, by rfl⟩ : syracuseStep 4534001 = 3400501) B3400501
theorem B3022667 : Blo 2013435 3022667 := bstep (se 1 (by rfl) ⟨2267000, by rfl⟩ : syracuseStep 3022667 = 4534001) B4534001
theorem B2015111 : Blo 2013435 2015111 := bstep (se 1 (by rfl) ⟨1511333, by rfl⟩ : syracuseStep 2015111 = 3022667) B3022667
theorem B2267005 : Blo 2013435 2267005 := bbase (se 3 (by rfl) ⟨425063, by rfl⟩ : syracuseStep 2267005 = 850127) (by norm_num)
theorem B3022673 : Blo 2013435 3022673 := bstep (se 2 (by rfl) ⟨1133502, by rfl⟩ : syracuseStep 3022673 = 2267005) B2267005
theorem B2015115 : Blo 2013435 2015115 := bstep (se 1 (by rfl) ⟨1511336, by rfl⟩ : syracuseStep 2015115 = 3022673) B3022673
theorem B6801029 : Blo 2013435 6801029 := bbase (se 4 (by rfl) ⟨637596, by rfl⟩ : syracuseStep 6801029 = 1275193) (by norm_num)
theorem B4534019 : Blo 2013435 4534019 := bstep (se 1 (by rfl) ⟨3400514, by rfl⟩ : syracuseStep 4534019 = 6801029) B6801029
theorem B3022679 : Blo 2013435 3022679 := bstep (se 1 (by rfl) ⟨2267009, by rfl⟩ : syracuseStep 3022679 = 4534019) B4534019
theorem B2015119 : Blo 2013435 2015119 := bstep (se 1 (by rfl) ⟨1511339, by rfl⟩ : syracuseStep 2015119 = 3022679) B3022679
theorem B3022685 : Blo 2013435 3022685 := bbase (se 3 (by rfl) ⟨566753, by rfl⟩ : syracuseStep 3022685 = 1133507) (by norm_num)
theorem B2015123 : Blo 2013435 2015123 := bstep (se 1 (by rfl) ⟨1511342, by rfl⟩ : syracuseStep 2015123 = 3022685) B3022685
theorem B4534037 : Blo 2013435 4534037 := bbase (se 6 (by rfl) ⟨106266, by rfl⟩ : syracuseStep 4534037 = 212533) (by norm_num)
theorem B3022691 : Blo 2013435 3022691 := bstep (se 1 (by rfl) ⟨2267018, by rfl⟩ : syracuseStep 3022691 = 4534037) B4534037
theorem B2015127 : Blo 2013435 2015127 := bstep (se 1 (by rfl) ⟨1511345, by rfl⟩ : syracuseStep 2015127 = 3022691) B3022691
theorem B7651205 : Blo 2013435 7651205 := bbase (se 4 (by rfl) ⟨717300, by rfl⟩ : syracuseStep 7651205 = 1434601) (by norm_num)
theorem B5100803 : Blo 2013435 5100803 := bstep (se 1 (by rfl) ⟨3825602, by rfl⟩ : syracuseStep 5100803 = 7651205) B7651205
theorem B3400535 : Blo 2013435 3400535 := bstep (se 1 (by rfl) ⟨2550401, by rfl⟩ : syracuseStep 3400535 = 5100803) B5100803
theorem B2267023 : Blo 2013435 2267023 := bstep (se 1 (by rfl) ⟨1700267, by rfl⟩ : syracuseStep 2267023 = 3400535) B3400535
theorem B3022697 : Blo 2013435 3022697 := bstep (se 2 (by rfl) ⟨1133511, by rfl⟩ : syracuseStep 3022697 = 2267023) B2267023
theorem B2015131 : Blo 2013435 2015131 := bstep (se 1 (by rfl) ⟨1511348, by rfl⟩ : syracuseStep 2015131 = 3022697) B3022697
theorem B6455717 : Blo 2013435 6455717 := bbase (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) (by norm_num)
theorem B4303811 : Blo 2013435 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B11476829 : Blo 2013435 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B7651219 : Blo 2013435 7651219 := bstep (se 1 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 7651219 = 11476829) B11476829
theorem B10201625 : Blo 2013435 10201625 := bstep (se 2 (by rfl) ⟨3825609, by rfl⟩ : syracuseStep 10201625 = 7651219) B7651219
theorem B6801083 : Blo 2013435 6801083 := bstep (se 1 (by rfl) ⟨5100812, by rfl⟩ : syracuseStep 6801083 = 10201625) B10201625
theorem B4534055 : Blo 2013435 4534055 := bstep (se 1 (by rfl) ⟨3400541, by rfl⟩ : syracuseStep 4534055 = 6801083) B6801083
theorem B3022703 : Blo 2013435 3022703 := bstep (se 1 (by rfl) ⟨2267027, by rfl⟩ : syracuseStep 3022703 = 4534055) B4534055
theorem B2015135 : Blo 2013435 2015135 := bstep (se 1 (by rfl) ⟨1511351, by rfl⟩ : syracuseStep 2015135 = 3022703) B3022703
theorem B3022709 : Blo 2013435 3022709 := bbase (se 5 (by rfl) ⟨141689, by rfl⟩ : syracuseStep 3022709 = 283379) (by norm_num)
theorem B2015139 : Blo 2013435 2015139 := bstep (se 1 (by rfl) ⟨1511354, by rfl⟩ : syracuseStep 2015139 = 3022709) B3022709
theorem B4303829 : Blo 2013435 4303829 := bbase (se 7 (by rfl) ⟨50435, by rfl⟩ : syracuseStep 4303829 = 100871) (by norm_num)
theorem B2869219 : Blo 2013435 2869219 := bstep (se 1 (by rfl) ⟨2151914, by rfl⟩ : syracuseStep 2869219 = 4303829) B4303829
theorem B3825625 : Blo 2013435 3825625 := bstep (se 2 (by rfl) ⟨1434609, by rfl⟩ : syracuseStep 3825625 = 2869219) B2869219
theorem B5100833 : Blo 2013435 5100833 := bstep (se 2 (by rfl) ⟨1912812, by rfl⟩ : syracuseStep 5100833 = 3825625) B3825625
theorem B3400555 : Blo 2013435 3400555 := bstep (se 1 (by rfl) ⟨2550416, by rfl⟩ : syracuseStep 3400555 = 5100833) B5100833
theorem B4534073 : Blo 2013435 4534073 := bstep (se 2 (by rfl) ⟨1700277, by rfl⟩ : syracuseStep 4534073 = 3400555) B3400555
theorem B3022715 : Blo 2013435 3022715 := bstep (se 1 (by rfl) ⟨2267036, by rfl⟩ : syracuseStep 3022715 = 4534073) B4534073
theorem B2015143 : Blo 2013435 2015143 := bstep (se 1 (by rfl) ⟨1511357, by rfl⟩ : syracuseStep 2015143 = 3022715) B3022715
theorem B2267041 : Blo 2013435 2267041 := bbase (se 2 (by rfl) ⟨850140, by rfl⟩ : syracuseStep 2267041 = 1700281) (by norm_num)
theorem B3022721 : Blo 2013435 3022721 := bstep (se 2 (by rfl) ⟨1133520, by rfl⟩ : syracuseStep 3022721 = 2267041) B2267041
theorem B2015147 : Blo 2013435 2015147 := bstep (se 1 (by rfl) ⟨1511360, by rfl⟩ : syracuseStep 2015147 = 3022721) B3022721
theorem B5100853 : Blo 2013435 5100853 := bbase (se 5 (by rfl) ⟨239102, by rfl⟩ : syracuseStep 5100853 = 478205) (by norm_num)
theorem B6801137 : Blo 2013435 6801137 := bstep (se 2 (by rfl) ⟨2550426, by rfl⟩ : syracuseStep 6801137 = 5100853) B5100853
theorem B4534091 : Blo 2013435 4534091 := bstep (se 1 (by rfl) ⟨3400568, by rfl⟩ : syracuseStep 4534091 = 6801137) B6801137
theorem B3022727 : Blo 2013435 3022727 := bstep (se 1 (by rfl) ⟨2267045, by rfl⟩ : syracuseStep 3022727 = 4534091) B4534091
theorem B2015151 : Blo 2013435 2015151 := bstep (se 1 (by rfl) ⟨1511363, by rfl⟩ : syracuseStep 2015151 = 3022727) B3022727
theorem B3022733 : Blo 2013435 3022733 := bbase (se 3 (by rfl) ⟨566762, by rfl⟩ : syracuseStep 3022733 = 1133525) (by norm_num)
theorem B2015155 : Blo 2013435 2015155 := bstep (se 1 (by rfl) ⟨1511366, by rfl⟩ : syracuseStep 2015155 = 3022733) B3022733
theorem B4534109 : Blo 2013435 4534109 := bbase (se 3 (by rfl) ⟨850145, by rfl⟩ : syracuseStep 4534109 = 1700291) (by norm_num)
theorem B3022739 : Blo 2013435 3022739 := bstep (se 1 (by rfl) ⟨2267054, by rfl⟩ : syracuseStep 3022739 = 4534109) B4534109
theorem B2015159 : Blo 2013435 2015159 := bstep (se 1 (by rfl) ⟨1511369, by rfl⟩ : syracuseStep 2015159 = 3022739) B3022739
theorem B3400589 : Blo 2013435 3400589 := bbase (se 3 (by rfl) ⟨637610, by rfl⟩ : syracuseStep 3400589 = 1275221) (by norm_num)
theorem B2267059 : Blo 2013435 2267059 := bstep (se 1 (by rfl) ⟨1700294, by rfl⟩ : syracuseStep 2267059 = 3400589) B3400589
theorem B3022745 : Blo 2013435 3022745 := bstep (se 2 (by rfl) ⟨1133529, by rfl⟩ : syracuseStep 3022745 = 2267059) B2267059
theorem B2015163 : Blo 2013435 2015163 := bstep (se 1 (by rfl) ⟨1511372, by rfl⟩ : syracuseStep 2015163 = 3022745) B3022745
theorem B2723549 : Blo 2013435 2723549 := bbase (se 3 (by rfl) ⟨510665, by rfl⟩ : syracuseStep 2723549 = 1021331) (by norm_num)
theorem B7262797 : Blo 2013435 7262797 := bstep (se 3 (by rfl) ⟨1361774, by rfl⟩ : syracuseStep 7262797 = 2723549) B2723549
theorem B9683729 : Blo 2013435 9683729 := bstep (se 2 (by rfl) ⟨3631398, by rfl⟩ : syracuseStep 9683729 = 7262797) B7262797
theorem B6455819 : Blo 2013435 6455819 := bstep (se 1 (by rfl) ⟨4841864, by rfl⟩ : syracuseStep 6455819 = 9683729) B9683729
theorem B17215517 : Blo 2013435 17215517 := bstep (se 3 (by rfl) ⟨3227909, by rfl⟩ : syracuseStep 17215517 = 6455819) B6455819
theorem B11477011 : Blo 2013435 11477011 := bstep (se 1 (by rfl) ⟨8607758, by rfl⟩ : syracuseStep 11477011 = 17215517) B17215517
theorem B15302681 : Blo 2013435 15302681 := bstep (se 2 (by rfl) ⟨5738505, by rfl⟩ : syracuseStep 15302681 = 11477011) B11477011
theorem B10201787 : Blo 2013435 10201787 := bstep (se 1 (by rfl) ⟨7651340, by rfl⟩ : syracuseStep 10201787 = 15302681) B15302681
theorem B6801191 : Blo 2013435 6801191 := bstep (se 1 (by rfl) ⟨5100893, by rfl⟩ : syracuseStep 6801191 = 10201787) B10201787
theorem B4534127 : Blo 2013435 4534127 := bstep (se 1 (by rfl) ⟨3400595, by rfl⟩ : syracuseStep 4534127 = 6801191) B6801191
theorem B3022751 : Blo 2013435 3022751 := bstep (se 1 (by rfl) ⟨2267063, by rfl⟩ : syracuseStep 3022751 = 4534127) B4534127
theorem B2015167 : Blo 2013435 2015167 := bstep (se 1 (by rfl) ⟨1511375, by rfl⟩ : syracuseStep 2015167 = 3022751) B3022751
theorem B3022757 : Blo 2013435 3022757 := bbase (se 4 (by rfl) ⟨283383, by rfl⟩ : syracuseStep 3022757 = 566767) (by norm_num)
theorem B2015171 : Blo 2013435 2015171 := bstep (se 1 (by rfl) ⟨1511378, by rfl⟩ : syracuseStep 2015171 = 3022757) B3022757
theorem B2550457 : Blo 2013435 2550457 := bbase (se 2 (by rfl) ⟨956421, by rfl⟩ : syracuseStep 2550457 = 1912843) (by norm_num)
theorem B3400609 : Blo 2013435 3400609 := bstep (se 2 (by rfl) ⟨1275228, by rfl⟩ : syracuseStep 3400609 = 2550457) B2550457
theorem B4534145 : Blo 2013435 4534145 := bstep (se 2 (by rfl) ⟨1700304, by rfl⟩ : syracuseStep 4534145 = 3400609) B3400609
theorem B3022763 : Blo 2013435 3022763 := bstep (se 1 (by rfl) ⟨2267072, by rfl⟩ : syracuseStep 3022763 = 4534145) B4534145
theorem B2015175 : Blo 2013435 2015175 := bstep (se 1 (by rfl) ⟨1511381, by rfl⟩ : syracuseStep 2015175 = 3022763) B3022763
theorem B2267077 : Blo 2013435 2267077 := bbase (se 4 (by rfl) ⟨212538, by rfl⟩ : syracuseStep 2267077 = 425077) (by norm_num)
theorem B3022769 : Blo 2013435 3022769 := bstep (se 2 (by rfl) ⟨1133538, by rfl⟩ : syracuseStep 3022769 = 2267077) B2267077
theorem B2015179 : Blo 2013435 2015179 := bstep (se 1 (by rfl) ⟨1511384, by rfl⟩ : syracuseStep 2015179 = 3022769) B3022769
theorem B3825701 : Blo 2013435 3825701 := bbase (se 4 (by rfl) ⟨358659, by rfl⟩ : syracuseStep 3825701 = 717319) (by norm_num)
theorem B2550467 : Blo 2013435 2550467 := bstep (se 1 (by rfl) ⟨1912850, by rfl⟩ : syracuseStep 2550467 = 3825701) B3825701
theorem B6801245 : Blo 2013435 6801245 := bstep (se 3 (by rfl) ⟨1275233, by rfl⟩ : syracuseStep 6801245 = 2550467) B2550467
theorem B4534163 : Blo 2013435 4534163 := bstep (se 1 (by rfl) ⟨3400622, by rfl⟩ : syracuseStep 4534163 = 6801245) B6801245
theorem B3022775 : Blo 2013435 3022775 := bstep (se 1 (by rfl) ⟨2267081, by rfl⟩ : syracuseStep 3022775 = 4534163) B4534163
theorem B2015183 : Blo 2013435 2015183 := bstep (se 1 (by rfl) ⟨1511387, by rfl⟩ : syracuseStep 2015183 = 3022775) B3022775
theorem B3022781 : Blo 2013435 3022781 := bbase (se 3 (by rfl) ⟨566771, by rfl⟩ : syracuseStep 3022781 = 1133543) (by norm_num)
theorem B2015187 : Blo 2013435 2015187 := bstep (se 1 (by rfl) ⟨1511390, by rfl⟩ : syracuseStep 2015187 = 3022781) B3022781
theorem B4534181 : Blo 2013435 4534181 := bbase (se 4 (by rfl) ⟨425079, by rfl⟩ : syracuseStep 4534181 = 850159) (by norm_num)
theorem B3022787 : Blo 2013435 3022787 := bstep (se 1 (by rfl) ⟨2267090, by rfl⟩ : syracuseStep 3022787 = 4534181) B4534181
theorem B2015191 : Blo 2013435 2015191 := bstep (se 1 (by rfl) ⟨1511393, by rfl⟩ : syracuseStep 2015191 = 3022787) B3022787
theorem B5100965 : Blo 2013435 5100965 := bbase (se 4 (by rfl) ⟨478215, by rfl⟩ : syracuseStep 5100965 = 956431) (by norm_num)
theorem B3400643 : Blo 2013435 3400643 := bstep (se 1 (by rfl) ⟨2550482, by rfl⟩ : syracuseStep 3400643 = 5100965) B5100965
theorem B2267095 : Blo 2013435 2267095 := bstep (se 1 (by rfl) ⟨1700321, by rfl⟩ : syracuseStep 2267095 = 3400643) B3400643
theorem B3022793 : Blo 2013435 3022793 := bstep (se 2 (by rfl) ⟨1133547, by rfl⟩ : syracuseStep 3022793 = 2267095) B2267095
theorem B2015195 : Blo 2013435 2015195 := bstep (se 1 (by rfl) ⟨1511396, by rfl⟩ : syracuseStep 2015195 = 3022793) B3022793
theorem B5738597 : Blo 2013435 5738597 := bbase (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) (by norm_num)
theorem B3825731 : Blo 2013435 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B10201949 : Blo 2013435 10201949 := bstep (se 3 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 10201949 = 3825731) B3825731
theorem B6801299 : Blo 2013435 6801299 := bstep (se 1 (by rfl) ⟨5100974, by rfl⟩ : syracuseStep 6801299 = 10201949) B10201949
theorem B4534199 : Blo 2013435 4534199 := bstep (se 1 (by rfl) ⟨3400649, by rfl⟩ : syracuseStep 4534199 = 6801299) B6801299
theorem B3022799 : Blo 2013435 3022799 := bstep (se 1 (by rfl) ⟨2267099, by rfl⟩ : syracuseStep 3022799 = 4534199) B4534199
theorem B2015199 : Blo 2013435 2015199 := bstep (se 1 (by rfl) ⟨1511399, by rfl⟩ : syracuseStep 2015199 = 3022799) B3022799
theorem B3022805 : Blo 2013435 3022805 := bbase (se 7 (by rfl) ⟨35423, by rfl⟩ : syracuseStep 3022805 = 70847) (by norm_num)
theorem B2015203 : Blo 2013435 2015203 := bstep (se 1 (by rfl) ⟨1511402, by rfl⟩ : syracuseStep 2015203 = 3022805) B3022805
theorem B7651493 : Blo 2013435 7651493 := bbase (se 4 (by rfl) ⟨717327, by rfl⟩ : syracuseStep 7651493 = 1434655) (by norm_num)
theorem B5100995 : Blo 2013435 5100995 := bstep (se 1 (by rfl) ⟨3825746, by rfl⟩ : syracuseStep 5100995 = 7651493) B7651493
theorem B3400663 : Blo 2013435 3400663 := bstep (se 1 (by rfl) ⟨2550497, by rfl⟩ : syracuseStep 3400663 = 5100995) B5100995
theorem B4534217 : Blo 2013435 4534217 := bstep (se 2 (by rfl) ⟨1700331, by rfl⟩ : syracuseStep 4534217 = 3400663) B3400663
theorem B3022811 : Blo 2013435 3022811 := bstep (se 1 (by rfl) ⟨2267108, by rfl⟩ : syracuseStep 3022811 = 4534217) B4534217
theorem B2015207 : Blo 2013435 2015207 := bstep (se 1 (by rfl) ⟨1511405, by rfl⟩ : syracuseStep 2015207 = 3022811) B3022811
theorem B2267113 : Blo 2013435 2267113 := bbase (se 2 (by rfl) ⟨850167, by rfl⟩ : syracuseStep 2267113 = 1700335) (by norm_num)
theorem B3022817 : Blo 2013435 3022817 := bstep (se 2 (by rfl) ⟨1133556, by rfl⟩ : syracuseStep 3022817 = 2267113) B2267113
theorem B2015211 : Blo 2013435 2015211 := bstep (se 1 (by rfl) ⟨1511408, by rfl⟩ : syracuseStep 2015211 = 3022817) B3022817
theorem B4841981 : Blo 2013435 4841981 := bbase (se 3 (by rfl) ⟨907871, by rfl⟩ : syracuseStep 4841981 = 1815743) (by norm_num)
theorem B3227987 : Blo 2013435 3227987 := bstep (se 1 (by rfl) ⟨2420990, by rfl⟩ : syracuseStep 3227987 = 4841981) B4841981
theorem B2151991 : Blo 2013435 2151991 := bstep (se 1 (by rfl) ⟨1613993, by rfl⟩ : syracuseStep 2151991 = 3227987) B3227987
theorem B11477285 : Blo 2013435 11477285 := bstep (se 4 (by rfl) ⟨1075995, by rfl⟩ : syracuseStep 11477285 = 2151991) B2151991
theorem B7651523 : Blo 2013435 7651523 := bstep (se 1 (by rfl) ⟨5738642, by rfl⟩ : syracuseStep 7651523 = 11477285) B11477285
theorem B5101015 : Blo 2013435 5101015 := bstep (se 1 (by rfl) ⟨3825761, by rfl⟩ : syracuseStep 5101015 = 7651523) B7651523
theorem B6801353 : Blo 2013435 6801353 := bstep (se 2 (by rfl) ⟨2550507, by rfl⟩ : syracuseStep 6801353 = 5101015) B5101015
theorem B4534235 : Blo 2013435 4534235 := bstep (se 1 (by rfl) ⟨3400676, by rfl⟩ : syracuseStep 4534235 = 6801353) B6801353
theorem B3022823 : Blo 2013435 3022823 := bstep (se 1 (by rfl) ⟨2267117, by rfl⟩ : syracuseStep 3022823 = 4534235) B4534235
theorem B2015215 : Blo 2013435 2015215 := bstep (se 1 (by rfl) ⟨1511411, by rfl⟩ : syracuseStep 2015215 = 3022823) B3022823
theorem B3022829 : Blo 2013435 3022829 := bbase (se 3 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 3022829 = 1133561) (by norm_num)
theorem B2015219 : Blo 2013435 2015219 := bstep (se 1 (by rfl) ⟨1511414, by rfl⟩ : syracuseStep 2015219 = 3022829) B3022829
theorem B4534253 : Blo 2013435 4534253 := bbase (se 3 (by rfl) ⟨850172, by rfl⟩ : syracuseStep 4534253 = 1700345) (by norm_num)
theorem B3022835 : Blo 2013435 3022835 := bstep (se 1 (by rfl) ⟨2267126, by rfl⟩ : syracuseStep 3022835 = 4534253) B4534253
theorem B2015223 : Blo 2013435 2015223 := bstep (se 1 (by rfl) ⟨1511417, by rfl⟩ : syracuseStep 2015223 = 3022835) B3022835
theorem B5170645 : Blo 2013435 5170645 := bbase (se 7 (by rfl) ⟨60593, by rfl⟩ : syracuseStep 5170645 = 121187) (by norm_num)
theorem B27576773 : Blo 2013435 27576773 := bstep (se 4 (by rfl) ⟨2585322, by rfl⟩ : syracuseStep 27576773 = 5170645) B5170645
theorem B18384515 : Blo 2013435 18384515 := bstep (se 1 (by rfl) ⟨13788386, by rfl⟩ : syracuseStep 18384515 = 27576773) B27576773
theorem B12256343 : Blo 2013435 12256343 := bstep (se 1 (by rfl) ⟨9192257, by rfl⟩ : syracuseStep 12256343 = 18384515) B18384515
theorem B8170895 : Blo 2013435 8170895 := bstep (se 1 (by rfl) ⟨6128171, by rfl⟩ : syracuseStep 8170895 = 12256343) B12256343
theorem B5447263 : Blo 2013435 5447263 := bstep (se 1 (by rfl) ⟨4085447, by rfl⟩ : syracuseStep 5447263 = 8170895) B8170895
theorem B7263017 : Blo 2013435 7263017 := bstep (se 2 (by rfl) ⟨2723631, by rfl⟩ : syracuseStep 7263017 = 5447263) B5447263
theorem B4842011 : Blo 2013435 4842011 := bstep (se 1 (by rfl) ⟨3631508, by rfl⟩ : syracuseStep 4842011 = 7263017) B7263017
theorem B3228007 : Blo 2013435 3228007 := bstep (se 1 (by rfl) ⟨2421005, by rfl⟩ : syracuseStep 3228007 = 4842011) B4842011
theorem B4304009 : Blo 2013435 4304009 := bstep (se 2 (by rfl) ⟨1614003, by rfl⟩ : syracuseStep 4304009 = 3228007) B3228007
theorem B2869339 : Blo 2013435 2869339 := bstep (se 1 (by rfl) ⟨2152004, by rfl⟩ : syracuseStep 2869339 = 4304009) B4304009
theorem B3825785 : Blo 2013435 3825785 := bstep (se 2 (by rfl) ⟨1434669, by rfl⟩ : syracuseStep 3825785 = 2869339) B2869339
theorem B2550523 : Blo 2013435 2550523 := bstep (se 1 (by rfl) ⟨1912892, by rfl⟩ : syracuseStep 2550523 = 3825785) B3825785
theorem B3400697 : Blo 2013435 3400697 := bstep (se 2 (by rfl) ⟨1275261, by rfl⟩ : syracuseStep 3400697 = 2550523) B2550523
theorem B2267131 : Blo 2013435 2267131 := bstep (se 1 (by rfl) ⟨1700348, by rfl⟩ : syracuseStep 2267131 = 3400697) B3400697
theorem B3022841 : Blo 2013435 3022841 := bstep (se 2 (by rfl) ⟨1133565, by rfl⟩ : syracuseStep 3022841 = 2267131) B2267131
theorem B2015227 : Blo 2013435 2015227 := bstep (se 1 (by rfl) ⟨1511420, by rfl⟩ : syracuseStep 2015227 = 3022841) B3022841
theorem B3272053 : Blo 2013435 3272053 := bbase (se 5 (by rfl) ⟨153377, by rfl⟩ : syracuseStep 3272053 = 306755) (by norm_num)
theorem B4362737 : Blo 2013435 4362737 := bstep (se 2 (by rfl) ⟨1636026, by rfl⟩ : syracuseStep 4362737 = 3272053) B3272053
theorem B11633965 : Blo 2013435 11633965 := bstep (se 3 (by rfl) ⟨2181368, by rfl⟩ : syracuseStep 11633965 = 4362737) B4362737
theorem B62047813 : Blo 2013435 62047813 := bstep (se 4 (by rfl) ⟨5816982, by rfl⟩ : syracuseStep 62047813 = 11633965) B11633965
theorem B82730417 : Blo 2013435 82730417 := bstep (se 2 (by rfl) ⟨31023906, by rfl⟩ : syracuseStep 82730417 = 62047813) B62047813
theorem B220614445 : Blo 2013435 220614445 := bstep (se 3 (by rfl) ⟨41365208, by rfl⟩ : syracuseStep 220614445 = 82730417) B82730417
theorem B294152593 : Blo 2013435 294152593 := bstep (se 2 (by rfl) ⟨110307222, by rfl⟩ : syracuseStep 294152593 = 220614445) B220614445
theorem B392203457 : Blo 2013435 392203457 := bstep (se 2 (by rfl) ⟨147076296, by rfl⟩ : syracuseStep 392203457 = 294152593) B294152593
theorem B261468971 : Blo 2013435 261468971 := bstep (se 1 (by rfl) ⟨196101728, by rfl⟩ : syracuseStep 261468971 = 392203457) B392203457
theorem B174312647 : Blo 2013435 174312647 := bstep (se 1 (by rfl) ⟨130734485, by rfl⟩ : syracuseStep 174312647 = 261468971) B261468971
theorem B116208431 : Blo 2013435 116208431 := bstep (se 1 (by rfl) ⟨87156323, by rfl⟩ : syracuseStep 116208431 = 174312647) B174312647
theorem B77472287 : Blo 2013435 77472287 := bstep (se 1 (by rfl) ⟨58104215, by rfl⟩ : syracuseStep 77472287 = 116208431) B116208431
theorem B51648191 : Blo 2013435 51648191 := bstep (se 1 (by rfl) ⟨38736143, by rfl⟩ : syracuseStep 51648191 = 77472287) B77472287
theorem B34432127 : Blo 2013435 34432127 := bstep (se 1 (by rfl) ⟨25824095, by rfl⟩ : syracuseStep 34432127 = 51648191) B51648191
theorem B22954751 : Blo 2013435 22954751 := bstep (se 1 (by rfl) ⟨17216063, by rfl⟩ : syracuseStep 22954751 = 34432127) B34432127
theorem B15303167 : Blo 2013435 15303167 := bstep (se 1 (by rfl) ⟨11477375, by rfl⟩ : syracuseStep 15303167 = 22954751) B22954751
theorem B10202111 : Blo 2013435 10202111 := bstep (se 1 (by rfl) ⟨7651583, by rfl⟩ : syracuseStep 10202111 = 15303167) B15303167
theorem B6801407 : Blo 2013435 6801407 := bstep (se 1 (by rfl) ⟨5101055, by rfl⟩ : syracuseStep 6801407 = 10202111) B10202111
theorem B4534271 : Blo 2013435 4534271 := bstep (se 1 (by rfl) ⟨3400703, by rfl⟩ : syracuseStep 4534271 = 6801407) B6801407
theorem B3022847 : Blo 2013435 3022847 := bstep (se 1 (by rfl) ⟨2267135, by rfl⟩ : syracuseStep 3022847 = 4534271) B4534271
theorem B2015231 : Blo 2013435 2015231 := bstep (se 1 (by rfl) ⟨1511423, by rfl⟩ : syracuseStep 2015231 = 3022847) B3022847
theorem B3022853 : Blo 2013435 3022853 := bbase (se 4 (by rfl) ⟨283392, by rfl⟩ : syracuseStep 3022853 = 566785) (by norm_num)
theorem B2015235 : Blo 2013435 2015235 := bstep (se 1 (by rfl) ⟨1511426, by rfl⟩ : syracuseStep 2015235 = 3022853) B3022853
theorem B3400717 : Blo 2013435 3400717 := bbase (se 3 (by rfl) ⟨637634, by rfl⟩ : syracuseStep 3400717 = 1275269) (by norm_num)
theorem B4534289 : Blo 2013435 4534289 := bstep (se 2 (by rfl) ⟨1700358, by rfl⟩ : syracuseStep 4534289 = 3400717) B3400717
theorem B3022859 : Blo 2013435 3022859 := bstep (se 1 (by rfl) ⟨2267144, by rfl⟩ : syracuseStep 3022859 = 4534289) B4534289
theorem B2015239 : Blo 2013435 2015239 := bstep (se 1 (by rfl) ⟨1511429, by rfl⟩ : syracuseStep 2015239 = 3022859) B3022859
theorem B2267149 : Blo 2013435 2267149 := bbase (se 3 (by rfl) ⟨425090, by rfl⟩ : syracuseStep 2267149 = 850181) (by norm_num)
theorem B3022865 : Blo 2013435 3022865 := bstep (se 2 (by rfl) ⟨1133574, by rfl⟩ : syracuseStep 3022865 = 2267149) B2267149
theorem B2015243 : Blo 2013435 2015243 := bstep (se 1 (by rfl) ⟨1511432, by rfl⟩ : syracuseStep 2015243 = 3022865) B3022865
theorem B6801461 : Blo 2013435 6801461 := bbase (se 5 (by rfl) ⟨318818, by rfl⟩ : syracuseStep 6801461 = 637637) (by norm_num)
theorem B4534307 : Blo 2013435 4534307 := bstep (se 1 (by rfl) ⟨3400730, by rfl⟩ : syracuseStep 4534307 = 6801461) B6801461
theorem B3022871 : Blo 2013435 3022871 := bstep (se 1 (by rfl) ⟨2267153, by rfl⟩ : syracuseStep 3022871 = 4534307) B4534307
theorem B2015247 : Blo 2013435 2015247 := bstep (se 1 (by rfl) ⟨1511435, by rfl⟩ : syracuseStep 2015247 = 3022871) B3022871
theorem B3022877 : Blo 2013435 3022877 := bbase (se 3 (by rfl) ⟨566789, by rfl⟩ : syracuseStep 3022877 = 1133579) (by norm_num)
theorem B2015251 : Blo 2013435 2015251 := bstep (se 1 (by rfl) ⟨1511438, by rfl⟩ : syracuseStep 2015251 = 3022877) B3022877
theorem B4534325 : Blo 2013435 4534325 := bbase (se 5 (by rfl) ⟨212546, by rfl⟩ : syracuseStep 4534325 = 425093) (by norm_num)
theorem B3022883 : Blo 2013435 3022883 := bstep (se 1 (by rfl) ⟨2267162, by rfl⟩ : syracuseStep 3022883 = 4534325) B4534325
theorem B2015255 : Blo 2013435 2015255 := bstep (se 1 (by rfl) ⟨1511441, by rfl⟩ : syracuseStep 2015255 = 3022883) B3022883
theorem B3631565 : Blo 2013435 3631565 := bbase (se 3 (by rfl) ⟨680918, by rfl⟩ : syracuseStep 3631565 = 1361837) (by norm_num)
theorem B9684173 : Blo 2013435 9684173 := bstep (se 3 (by rfl) ⟨1815782, by rfl⟩ : syracuseStep 9684173 = 3631565) B3631565
theorem B6456115 : Blo 2013435 6456115 := bstep (se 1 (by rfl) ⟨4842086, by rfl⟩ : syracuseStep 6456115 = 9684173) B9684173
theorem B8608153 : Blo 2013435 8608153 := bstep (se 2 (by rfl) ⟨3228057, by rfl⟩ : syracuseStep 8608153 = 6456115) B6456115
theorem B11477537 : Blo 2013435 11477537 := bstep (se 2 (by rfl) ⟨4304076, by rfl⟩ : syracuseStep 11477537 = 8608153) B8608153
theorem B7651691 : Blo 2013435 7651691 := bstep (se 1 (by rfl) ⟨5738768, by rfl⟩ : syracuseStep 7651691 = 11477537) B11477537
theorem B5101127 : Blo 2013435 5101127 := bstep (se 1 (by rfl) ⟨3825845, by rfl⟩ : syracuseStep 5101127 = 7651691) B7651691
theorem B3400751 : Blo 2013435 3400751 := bstep (se 1 (by rfl) ⟨2550563, by rfl⟩ : syracuseStep 3400751 = 5101127) B5101127
theorem B2267167 : Blo 2013435 2267167 := bstep (se 1 (by rfl) ⟨1700375, by rfl⟩ : syracuseStep 2267167 = 3400751) B3400751
theorem B3022889 : Blo 2013435 3022889 := bstep (se 2 (by rfl) ⟨1133583, by rfl⟩ : syracuseStep 3022889 = 2267167) B2267167
theorem B2015259 : Blo 2013435 2015259 := bstep (se 1 (by rfl) ⟨1511444, by rfl⟩ : syracuseStep 2015259 = 3022889) B3022889
theorem B5817077 : Blo 2013435 5817077 := bbase (se 5 (by rfl) ⟨272675, by rfl⟩ : syracuseStep 5817077 = 545351) (by norm_num)
theorem B3878051 : Blo 2013435 3878051 := bstep (se 1 (by rfl) ⟨2908538, by rfl⟩ : syracuseStep 3878051 = 5817077) B5817077
theorem B10341469 : Blo 2013435 10341469 := bstep (se 3 (by rfl) ⟨1939025, by rfl⟩ : syracuseStep 10341469 = 3878051) B3878051
theorem B13788625 : Blo 2013435 13788625 := bstep (se 2 (by rfl) ⟨5170734, by rfl⟩ : syracuseStep 13788625 = 10341469) B10341469
theorem B18384833 : Blo 2013435 18384833 := bstep (se 2 (by rfl) ⟨6894312, by rfl⟩ : syracuseStep 18384833 = 13788625) B13788625
theorem B49026221 : Blo 2013435 49026221 := bstep (se 3 (by rfl) ⟨9192416, by rfl⟩ : syracuseStep 49026221 = 18384833) B18384833
theorem B32684147 : Blo 2013435 32684147 := bstep (se 1 (by rfl) ⟨24513110, by rfl⟩ : syracuseStep 32684147 = 49026221) B49026221
theorem B21789431 : Blo 2013435 21789431 := bstep (se 1 (by rfl) ⟨16342073, by rfl⟩ : syracuseStep 21789431 = 32684147) B32684147
theorem B14526287 : Blo 2013435 14526287 := bstep (se 1 (by rfl) ⟨10894715, by rfl⟩ : syracuseStep 14526287 = 21789431) B21789431
theorem B9684191 : Blo 2013435 9684191 := bstep (se 1 (by rfl) ⟨7263143, by rfl⟩ : syracuseStep 9684191 = 14526287) B14526287
theorem B6456127 : Blo 2013435 6456127 := bstep (se 1 (by rfl) ⟨4842095, by rfl⟩ : syracuseStep 6456127 = 9684191) B9684191
theorem B8608169 : Blo 2013435 8608169 := bstep (se 2 (by rfl) ⟨3228063, by rfl⟩ : syracuseStep 8608169 = 6456127) B6456127
theorem B5738779 : Blo 2013435 5738779 := bstep (se 1 (by rfl) ⟨4304084, by rfl⟩ : syracuseStep 5738779 = 8608169) B8608169
theorem B7651705 : Blo 2013435 7651705 := bstep (se 2 (by rfl) ⟨2869389, by rfl⟩ : syracuseStep 7651705 = 5738779) B5738779
theorem B10202273 : Blo 2013435 10202273 := bstep (se 2 (by rfl) ⟨3825852, by rfl⟩ : syracuseStep 10202273 = 7651705) B7651705
theorem B6801515 : Blo 2013435 6801515 := bstep (se 1 (by rfl) ⟨5101136, by rfl⟩ : syracuseStep 6801515 = 10202273) B10202273
theorem B4534343 : Blo 2013435 4534343 := bstep (se 1 (by rfl) ⟨3400757, by rfl⟩ : syracuseStep 4534343 = 6801515) B6801515
theorem B3022895 : Blo 2013435 3022895 := bstep (se 1 (by rfl) ⟨2267171, by rfl⟩ : syracuseStep 3022895 = 4534343) B4534343
theorem B2015263 : Blo 2013435 2015263 := bstep (se 1 (by rfl) ⟨1511447, by rfl⟩ : syracuseStep 2015263 = 3022895) B3022895
theorem B3022901 : Blo 2013435 3022901 := bbase (se 5 (by rfl) ⟨141698, by rfl⟩ : syracuseStep 3022901 = 283397) (by norm_num)
theorem B2015267 : Blo 2013435 2015267 := bstep (se 1 (by rfl) ⟨1511450, by rfl⟩ : syracuseStep 2015267 = 3022901) B3022901
theorem B5101157 : Blo 2013435 5101157 := bbase (se 4 (by rfl) ⟨478233, by rfl⟩ : syracuseStep 5101157 = 956467) (by norm_num)
theorem B3400771 : Blo 2013435 3400771 := bstep (se 1 (by rfl) ⟨2550578, by rfl⟩ : syracuseStep 3400771 = 5101157) B5101157
theorem B4534361 : Blo 2013435 4534361 := bstep (se 2 (by rfl) ⟨1700385, by rfl⟩ : syracuseStep 4534361 = 3400771) B3400771
theorem B3022907 : Blo 2013435 3022907 := bstep (se 1 (by rfl) ⟨2267180, by rfl⟩ : syracuseStep 3022907 = 4534361) B4534361
theorem B2015271 : Blo 2013435 2015271 := bstep (se 1 (by rfl) ⟨1511453, by rfl⟩ : syracuseStep 2015271 = 3022907) B3022907
theorem B2267185 : Blo 2013435 2267185 := bbase (se 2 (by rfl) ⟨850194, by rfl⟩ : syracuseStep 2267185 = 1700389) (by norm_num)
theorem B3022913 : Blo 2013435 3022913 := bstep (se 2 (by rfl) ⟨1133592, by rfl⟩ : syracuseStep 3022913 = 2267185) B2267185
theorem B2015275 : Blo 2013435 2015275 := bstep (se 1 (by rfl) ⟨1511456, by rfl⟩ : syracuseStep 2015275 = 3022913) B3022913
theorem B2723701 : Blo 2013435 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B3631601 : Blo 2013435 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B9684269 : Blo 2013435 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B6456179 : Blo 2013435 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B4304119 : Blo 2013435 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B5738825 : Blo 2013435 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B3825883 : Blo 2013435 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B5101177 : Blo 2013435 5101177 := bstep (se 2 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 5101177 = 3825883) B3825883
theorem B6801569 : Blo 2013435 6801569 := bstep (se 2 (by rfl) ⟨2550588, by rfl⟩ : syracuseStep 6801569 = 5101177) B5101177
theorem B4534379 : Blo 2013435 4534379 := bstep (se 1 (by rfl) ⟨3400784, by rfl⟩ : syracuseStep 4534379 = 6801569) B6801569
theorem B3022919 : Blo 2013435 3022919 := bstep (se 1 (by rfl) ⟨2267189, by rfl⟩ : syracuseStep 3022919 = 4534379) B4534379
theorem B2015279 : Blo 2013435 2015279 := bstep (se 1 (by rfl) ⟨1511459, by rfl⟩ : syracuseStep 2015279 = 3022919) B3022919
theorem B3022925 : Blo 2013435 3022925 := bbase (se 3 (by rfl) ⟨566798, by rfl⟩ : syracuseStep 3022925 = 1133597) (by norm_num)
theorem B2015283 : Blo 2013435 2015283 := bstep (se 1 (by rfl) ⟨1511462, by rfl⟩ : syracuseStep 2015283 = 3022925) B3022925
theorem B4534397 : Blo 2013435 4534397 := bbase (se 3 (by rfl) ⟨850199, by rfl⟩ : syracuseStep 4534397 = 1700399) (by norm_num)
theorem B3022931 : Blo 2013435 3022931 := bstep (se 1 (by rfl) ⟨2267198, by rfl⟩ : syracuseStep 3022931 = 4534397) B4534397
theorem B2015287 : Blo 2013435 2015287 := bstep (se 1 (by rfl) ⟨1511465, by rfl⟩ : syracuseStep 2015287 = 3022931) B3022931
theorem B3400805 : Blo 2013435 3400805 := bbase (se 4 (by rfl) ⟨318825, by rfl⟩ : syracuseStep 3400805 = 637651) (by norm_num)
theorem B2267203 : Blo 2013435 2267203 := bstep (se 1 (by rfl) ⟨1700402, by rfl⟩ : syracuseStep 2267203 = 3400805) B3400805
theorem B3022937 : Blo 2013435 3022937 := bstep (se 2 (by rfl) ⟨1133601, by rfl⟩ : syracuseStep 3022937 = 2267203) B2267203
theorem B2015291 : Blo 2013435 2015291 := bstep (se 1 (by rfl) ⟨1511468, by rfl⟩ : syracuseStep 2015291 = 3022937) B3022937
theorem B4842173 : Blo 2013435 4842173 := bbase (se 3 (by rfl) ⟨907907, by rfl⟩ : syracuseStep 4842173 = 1815815) (by norm_num)
theorem B3228115 : Blo 2013435 3228115 := bstep (se 1 (by rfl) ⟨2421086, by rfl⟩ : syracuseStep 3228115 = 4842173) B4842173
theorem B4304153 : Blo 2013435 4304153 := bstep (se 2 (by rfl) ⟨1614057, by rfl⟩ : syracuseStep 4304153 = 3228115) B3228115
theorem B2869435 : Blo 2013435 2869435 := bstep (se 1 (by rfl) ⟨2152076, by rfl⟩ : syracuseStep 2869435 = 4304153) B4304153
theorem B15303653 : Blo 2013435 15303653 := bstep (se 4 (by rfl) ⟨1434717, by rfl⟩ : syracuseStep 15303653 = 2869435) B2869435
theorem B10202435 : Blo 2013435 10202435 := bstep (se 1 (by rfl) ⟨7651826, by rfl⟩ : syracuseStep 10202435 = 15303653) B15303653
theorem B6801623 : Blo 2013435 6801623 := bstep (se 1 (by rfl) ⟨5101217, by rfl⟩ : syracuseStep 6801623 = 10202435) B10202435
theorem B4534415 : Blo 2013435 4534415 := bstep (se 1 (by rfl) ⟨3400811, by rfl⟩ : syracuseStep 4534415 = 6801623) B6801623
theorem B3022943 : Blo 2013435 3022943 := bstep (se 1 (by rfl) ⟨2267207, by rfl⟩ : syracuseStep 3022943 = 4534415) B4534415
theorem B2015295 : Blo 2013435 2015295 := bstep (se 1 (by rfl) ⟨1511471, by rfl⟩ : syracuseStep 2015295 = 3022943) B3022943
theorem B3022949 : Blo 2013435 3022949 := bbase (se 4 (by rfl) ⟨283401, by rfl⟩ : syracuseStep 3022949 = 566803) (by norm_num)
theorem B2015299 : Blo 2013435 2015299 := bstep (se 1 (by rfl) ⟨1511474, by rfl⟩ : syracuseStep 2015299 = 3022949) B3022949
theorem B3631645 : Blo 2013435 3631645 := bbase (se 3 (by rfl) ⟨680933, by rfl⟩ : syracuseStep 3631645 = 1361867) (by norm_num)
theorem B4842193 : Blo 2013435 4842193 := bstep (se 2 (by rfl) ⟨1815822, by rfl⟩ : syracuseStep 4842193 = 3631645) B3631645
theorem B6456257 : Blo 2013435 6456257 := bstep (se 2 (by rfl) ⟨2421096, by rfl⟩ : syracuseStep 6456257 = 4842193) B4842193
theorem B4304171 : Blo 2013435 4304171 := bstep (se 1 (by rfl) ⟨3228128, by rfl⟩ : syracuseStep 4304171 = 6456257) B6456257
theorem B2869447 : Blo 2013435 2869447 := bstep (se 1 (by rfl) ⟨2152085, by rfl⟩ : syracuseStep 2869447 = 4304171) B4304171
theorem B3825929 : Blo 2013435 3825929 := bstep (se 2 (by rfl) ⟨1434723, by rfl⟩ : syracuseStep 3825929 = 2869447) B2869447
theorem B2550619 : Blo 2013435 2550619 := bstep (se 1 (by rfl) ⟨1912964, by rfl⟩ : syracuseStep 2550619 = 3825929) B3825929
theorem B3400825 : Blo 2013435 3400825 := bstep (se 2 (by rfl) ⟨1275309, by rfl⟩ : syracuseStep 3400825 = 2550619) B2550619
theorem B4534433 : Blo 2013435 4534433 := bstep (se 2 (by rfl) ⟨1700412, by rfl⟩ : syracuseStep 4534433 = 3400825) B3400825
theorem B3022955 : Blo 2013435 3022955 := bstep (se 1 (by rfl) ⟨2267216, by rfl⟩ : syracuseStep 3022955 = 4534433) B4534433
theorem B2015303 : Blo 2013435 2015303 := bstep (se 1 (by rfl) ⟨1511477, by rfl⟩ : syracuseStep 2015303 = 3022955) B3022955
theorem B2267221 : Blo 2013435 2267221 := bbase (se 8 (by rfl) ⟨13284, by rfl⟩ : syracuseStep 2267221 = 26569) (by norm_num)
theorem B3022961 : Blo 2013435 3022961 := bstep (se 2 (by rfl) ⟨1133610, by rfl⟩ : syracuseStep 3022961 = 2267221) B2267221
theorem B2015307 : Blo 2013435 2015307 := bstep (se 1 (by rfl) ⟨1511480, by rfl⟩ : syracuseStep 2015307 = 3022961) B3022961
theorem B2550629 : Blo 2013435 2550629 := bbase (se 4 (by rfl) ⟨239121, by rfl⟩ : syracuseStep 2550629 = 478243) (by norm_num)
theorem B6801677 : Blo 2013435 6801677 := bstep (se 3 (by rfl) ⟨1275314, by rfl⟩ : syracuseStep 6801677 = 2550629) B2550629
theorem B4534451 : Blo 2013435 4534451 := bstep (se 1 (by rfl) ⟨3400838, by rfl⟩ : syracuseStep 4534451 = 6801677) B6801677
theorem B3022967 : Blo 2013435 3022967 := bstep (se 1 (by rfl) ⟨2267225, by rfl⟩ : syracuseStep 3022967 = 4534451) B4534451
theorem B2015311 : Blo 2013435 2015311 := bstep (se 1 (by rfl) ⟨1511483, by rfl⟩ : syracuseStep 2015311 = 3022967) B3022967
theorem B3022973 : Blo 2013435 3022973 := bbase (se 3 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 3022973 = 1133615) (by norm_num)
theorem B2015315 : Blo 2013435 2015315 := bstep (se 1 (by rfl) ⟨1511486, by rfl⟩ : syracuseStep 2015315 = 3022973) B3022973
theorem B4534469 : Blo 2013435 4534469 := bbase (se 4 (by rfl) ⟨425106, by rfl⟩ : syracuseStep 4534469 = 850213) (by norm_num)
theorem B3022979 : Blo 2013435 3022979 := bstep (se 1 (by rfl) ⟨2267234, by rfl⟩ : syracuseStep 3022979 = 4534469) B4534469
theorem B2015319 : Blo 2013435 2015319 := bstep (se 1 (by rfl) ⟨1511489, by rfl⟩ : syracuseStep 2015319 = 3022979) B3022979
theorem B5817253 : Blo 2013435 5817253 := bbase (se 4 (by rfl) ⟨545367, by rfl⟩ : syracuseStep 5817253 = 1090735) (by norm_num)
theorem B7756337 : Blo 2013435 7756337 := bstep (se 2 (by rfl) ⟨2908626, by rfl⟩ : syracuseStep 7756337 = 5817253) B5817253
theorem B5170891 : Blo 2013435 5170891 := bstep (se 1 (by rfl) ⟨3878168, by rfl⟩ : syracuseStep 5170891 = 7756337) B7756337
theorem B6894521 : Blo 2013435 6894521 := bstep (se 2 (by rfl) ⟨2585445, by rfl⟩ : syracuseStep 6894521 = 5170891) B5170891
theorem B4596347 : Blo 2013435 4596347 := bstep (se 1 (by rfl) ⟨3447260, by rfl⟩ : syracuseStep 4596347 = 6894521) B6894521
theorem B3064231 : Blo 2013435 3064231 := bstep (se 1 (by rfl) ⟨2298173, by rfl⟩ : syracuseStep 3064231 = 4596347) B4596347
theorem B4085641 : Blo 2013435 4085641 := bstep (se 2 (by rfl) ⟨1532115, by rfl⟩ : syracuseStep 4085641 = 3064231) B3064231
theorem B5447521 : Blo 2013435 5447521 := bstep (se 2 (by rfl) ⟨2042820, by rfl⟩ : syracuseStep 5447521 = 4085641) B4085641
theorem B7263361 : Blo 2013435 7263361 := bstep (se 2 (by rfl) ⟨2723760, by rfl⟩ : syracuseStep 7263361 = 5447521) B5447521
theorem B9684481 : Blo 2013435 9684481 := bstep (se 2 (by rfl) ⟨3631680, by rfl⟩ : syracuseStep 9684481 = 7263361) B7263361
theorem B12912641 : Blo 2013435 12912641 := bstep (se 2 (by rfl) ⟨4842240, by rfl⟩ : syracuseStep 12912641 = 9684481) B9684481
theorem B8608427 : Blo 2013435 8608427 := bstep (se 1 (by rfl) ⟨6456320, by rfl⟩ : syracuseStep 8608427 = 12912641) B12912641
theorem B5738951 : Blo 2013435 5738951 := bstep (se 1 (by rfl) ⟨4304213, by rfl⟩ : syracuseStep 5738951 = 8608427) B8608427
theorem B3825967 : Blo 2013435 3825967 := bstep (se 1 (by rfl) ⟨2869475, by rfl⟩ : syracuseStep 3825967 = 5738951) B5738951
theorem B5101289 : Blo 2013435 5101289 := bstep (se 2 (by rfl) ⟨1912983, by rfl⟩ : syracuseStep 5101289 = 3825967) B3825967
theorem B3400859 : Blo 2013435 3400859 := bstep (se 1 (by rfl) ⟨2550644, by rfl⟩ : syracuseStep 3400859 = 5101289) B5101289
theorem B2267239 : Blo 2013435 2267239 := bstep (se 1 (by rfl) ⟨1700429, by rfl⟩ : syracuseStep 2267239 = 3400859) B3400859
theorem B3022985 : Blo 2013435 3022985 := bstep (se 2 (by rfl) ⟨1133619, by rfl⟩ : syracuseStep 3022985 = 2267239) B2267239
theorem B2015323 : Blo 2013435 2015323 := bstep (se 1 (by rfl) ⟨1511492, by rfl⟩ : syracuseStep 2015323 = 3022985) B3022985
theorem B10202597 : Blo 2013435 10202597 := bbase (se 4 (by rfl) ⟨956493, by rfl⟩ : syracuseStep 10202597 = 1912987) (by norm_num)
theorem B6801731 : Blo 2013435 6801731 := bstep (se 1 (by rfl) ⟨5101298, by rfl⟩ : syracuseStep 6801731 = 10202597) B10202597
theorem B4534487 : Blo 2013435 4534487 := bstep (se 1 (by rfl) ⟨3400865, by rfl⟩ : syracuseStep 4534487 = 6801731) B6801731
theorem B3022991 : Blo 2013435 3022991 := bstep (se 1 (by rfl) ⟨2267243, by rfl⟩ : syracuseStep 3022991 = 4534487) B4534487
theorem B2015327 : Blo 2013435 2015327 := bstep (se 1 (by rfl) ⟨1511495, by rfl⟩ : syracuseStep 2015327 = 3022991) B3022991
theorem B3022997 : Blo 2013435 3022997 := bbase (se 6 (by rfl) ⟨70851, by rfl⟩ : syracuseStep 3022997 = 141703) (by norm_num)
theorem B2015331 : Blo 2013435 2015331 := bstep (se 1 (by rfl) ⟨1511498, by rfl⟩ : syracuseStep 2015331 = 3022997) B3022997
theorem B4842269 : Blo 2013435 4842269 := bbase (se 3 (by rfl) ⟨907925, by rfl⟩ : syracuseStep 4842269 = 1815851) (by norm_num)
theorem B3228179 : Blo 2013435 3228179 := bstep (se 1 (by rfl) ⟨2421134, by rfl⟩ : syracuseStep 3228179 = 4842269) B4842269
theorem B8608477 : Blo 2013435 8608477 := bstep (se 3 (by rfl) ⟨1614089, by rfl⟩ : syracuseStep 8608477 = 3228179) B3228179
theorem B11477969 : Blo 2013435 11477969 := bstep (se 2 (by rfl) ⟨4304238, by rfl⟩ : syracuseStep 11477969 = 8608477) B8608477
theorem B7651979 : Blo 2013435 7651979 := bstep (se 1 (by rfl) ⟨5738984, by rfl⟩ : syracuseStep 7651979 = 11477969) B11477969
theorem B5101319 : Blo 2013435 5101319 := bstep (se 1 (by rfl) ⟨3825989, by rfl⟩ : syracuseStep 5101319 = 7651979) B7651979
theorem B3400879 : Blo 2013435 3400879 := bstep (se 1 (by rfl) ⟨2550659, by rfl⟩ : syracuseStep 3400879 = 5101319) B5101319
theorem B4534505 : Blo 2013435 4534505 := bstep (se 2 (by rfl) ⟨1700439, by rfl⟩ : syracuseStep 4534505 = 3400879) B3400879
theorem B3023003 : Blo 2013435 3023003 := bstep (se 1 (by rfl) ⟨2267252, by rfl⟩ : syracuseStep 3023003 = 4534505) B4534505
theorem B2015335 : Blo 2013435 2015335 := bstep (se 1 (by rfl) ⟨1511501, by rfl⟩ : syracuseStep 2015335 = 3023003) B3023003
theorem B2267257 : Blo 2013435 2267257 := bbase (se 2 (by rfl) ⟨850221, by rfl⟩ : syracuseStep 2267257 = 1700443) (by norm_num)
theorem B3023009 : Blo 2013435 3023009 := bstep (se 2 (by rfl) ⟨1133628, by rfl⟩ : syracuseStep 3023009 = 2267257) B2267257
theorem B2015339 : Blo 2013435 2015339 := bstep (se 1 (by rfl) ⟨1511504, by rfl⟩ : syracuseStep 2015339 = 3023009) B3023009
theorem B15724469 : Blo 2013435 15724469 := bbase (se 5 (by rfl) ⟨737084, by rfl⟩ : syracuseStep 15724469 = 1474169) (by norm_num)
theorem B10482979 : Blo 2013435 10482979 := bstep (se 1 (by rfl) ⟨7862234, by rfl⟩ : syracuseStep 10482979 = 15724469) B15724469
theorem B13977305 : Blo 2013435 13977305 := bstep (se 2 (by rfl) ⟨5241489, by rfl⟩ : syracuseStep 13977305 = 10482979) B10482979
theorem B9318203 : Blo 2013435 9318203 := bstep (se 1 (by rfl) ⟨6988652, by rfl⟩ : syracuseStep 9318203 = 13977305) B13977305
theorem B6212135 : Blo 2013435 6212135 := bstep (se 1 (by rfl) ⟨4659101, by rfl⟩ : syracuseStep 6212135 = 9318203) B9318203
theorem B4141423 : Blo 2013435 4141423 := bstep (se 1 (by rfl) ⟨3106067, by rfl⟩ : syracuseStep 4141423 = 6212135) B6212135
theorem B5521897 : Blo 2013435 5521897 := bstep (se 2 (by rfl) ⟨2070711, by rfl⟩ : syracuseStep 5521897 = 4141423) B4141423
theorem B29450117 : Blo 2013435 29450117 := bstep (se 4 (by rfl) ⟨2760948, by rfl⟩ : syracuseStep 29450117 = 5521897) B5521897
theorem B19633411 : Blo 2013435 19633411 := bstep (se 1 (by rfl) ⟨14725058, by rfl⟩ : syracuseStep 19633411 = 29450117) B29450117
theorem B104711525 : Blo 2013435 104711525 := bstep (se 4 (by rfl) ⟨9816705, by rfl⟩ : syracuseStep 104711525 = 19633411) B19633411
theorem B69807683 : Blo 2013435 69807683 := bstep (se 1 (by rfl) ⟨52355762, by rfl⟩ : syracuseStep 69807683 = 104711525) B104711525
theorem B46538455 : Blo 2013435 46538455 := bstep (se 1 (by rfl) ⟨34903841, by rfl⟩ : syracuseStep 46538455 = 69807683) B69807683
theorem B62051273 : Blo 2013435 62051273 := bstep (se 2 (by rfl) ⟨23269227, by rfl⟩ : syracuseStep 62051273 = 46538455) B46538455
theorem B41367515 : Blo 2013435 41367515 := bstep (se 1 (by rfl) ⟨31025636, by rfl⟩ : syracuseStep 41367515 = 62051273) B62051273
theorem B110313373 : Blo 2013435 110313373 := bstep (se 3 (by rfl) ⟨20683757, by rfl⟩ : syracuseStep 110313373 = 41367515) B41367515
theorem B147084497 : Blo 2013435 147084497 := bstep (se 2 (by rfl) ⟨55156686, by rfl⟩ : syracuseStep 147084497 = 110313373) B110313373
theorem B98056331 : Blo 2013435 98056331 := bstep (se 1 (by rfl) ⟨73542248, by rfl⟩ : syracuseStep 98056331 = 147084497) B147084497
theorem B65370887 : Blo 2013435 65370887 := bstep (se 1 (by rfl) ⟨49028165, by rfl⟩ : syracuseStep 65370887 = 98056331) B98056331
theorem B43580591 : Blo 2013435 43580591 := bstep (se 1 (by rfl) ⟨32685443, by rfl⟩ : syracuseStep 43580591 = 65370887) B65370887
theorem B29053727 : Blo 2013435 29053727 := bstep (se 1 (by rfl) ⟨21790295, by rfl⟩ : syracuseStep 29053727 = 43580591) B43580591
theorem B19369151 : Blo 2013435 19369151 := bstep (se 1 (by rfl) ⟨14526863, by rfl⟩ : syracuseStep 19369151 = 29053727) B29053727
theorem B12912767 : Blo 2013435 12912767 := bstep (se 1 (by rfl) ⟨9684575, by rfl⟩ : syracuseStep 12912767 = 19369151) B19369151
theorem B8608511 : Blo 2013435 8608511 := bstep (se 1 (by rfl) ⟨6456383, by rfl⟩ : syracuseStep 8608511 = 12912767) B12912767
theorem B5739007 : Blo 2013435 5739007 := bstep (se 1 (by rfl) ⟨4304255, by rfl⟩ : syracuseStep 5739007 = 8608511) B8608511
theorem B7652009 : Blo 2013435 7652009 := bstep (se 2 (by rfl) ⟨2869503, by rfl⟩ : syracuseStep 7652009 = 5739007) B5739007
theorem B5101339 : Blo 2013435 5101339 := bstep (se 1 (by rfl) ⟨3826004, by rfl⟩ : syracuseStep 5101339 = 7652009) B7652009
theorem B6801785 : Blo 2013435 6801785 := bstep (se 2 (by rfl) ⟨2550669, by rfl⟩ : syracuseStep 6801785 = 5101339) B5101339
theorem B4534523 : Blo 2013435 4534523 := bstep (se 1 (by rfl) ⟨3400892, by rfl⟩ : syracuseStep 4534523 = 6801785) B6801785
theorem B3023015 : Blo 2013435 3023015 := bstep (se 1 (by rfl) ⟨2267261, by rfl⟩ : syracuseStep 3023015 = 4534523) B4534523
theorem B2015343 : Blo 2013435 2015343 := bstep (se 1 (by rfl) ⟨1511507, by rfl⟩ : syracuseStep 2015343 = 3023015) B3023015
theorem B3023021 : Blo 2013435 3023021 := bbase (se 3 (by rfl) ⟨566816, by rfl⟩ : syracuseStep 3023021 = 1133633) (by norm_num)
theorem B2015347 : Blo 2013435 2015347 := bstep (se 1 (by rfl) ⟨1511510, by rfl⟩ : syracuseStep 2015347 = 3023021) B3023021
theorem B4534541 : Blo 2013435 4534541 := bbase (se 3 (by rfl) ⟨850226, by rfl⟩ : syracuseStep 4534541 = 1700453) (by norm_num)
theorem B3023027 : Blo 2013435 3023027 := bstep (se 1 (by rfl) ⟨2267270, by rfl⟩ : syracuseStep 3023027 = 4534541) B4534541
theorem B2015351 : Blo 2013435 2015351 := bstep (se 1 (by rfl) ⟨1511513, by rfl⟩ : syracuseStep 2015351 = 3023027) B3023027
theorem B2550685 : Blo 2013435 2550685 := bbase (se 3 (by rfl) ⟨478253, by rfl⟩ : syracuseStep 2550685 = 956507) (by norm_num)
theorem B3400913 : Blo 2013435 3400913 := bstep (se 2 (by rfl) ⟨1275342, by rfl⟩ : syracuseStep 3400913 = 2550685) B2550685
theorem B2267275 : Blo 2013435 2267275 := bstep (se 1 (by rfl) ⟨1700456, by rfl⟩ : syracuseStep 2267275 = 3400913) B3400913
theorem B3023033 : Blo 2013435 3023033 := bstep (se 2 (by rfl) ⟨1133637, by rfl⟩ : syracuseStep 3023033 = 2267275) B2267275
theorem B2015355 : Blo 2013435 2015355 := bstep (se 1 (by rfl) ⟨1511516, by rfl⟩ : syracuseStep 2015355 = 3023033) B3023033
theorem B2042857 : Blo 2013435 2042857 := bbase (se 2 (by rfl) ⟨766071, by rfl⟩ : syracuseStep 2042857 = 1532143) (by norm_num)
theorem B2723809 : Blo 2013435 2723809 := bstep (se 2 (by rfl) ⟨1021428, by rfl⟩ : syracuseStep 2723809 = 2042857) B2042857
theorem B3631745 : Blo 2013435 3631745 := bstep (se 2 (by rfl) ⟨1361904, by rfl⟩ : syracuseStep 3631745 = 2723809) B2723809
theorem B2421163 : Blo 2013435 2421163 := bstep (se 1 (by rfl) ⟨1815872, by rfl⟩ : syracuseStep 2421163 = 3631745) B3631745
theorem B3228217 : Blo 2013435 3228217 := bstep (se 2 (by rfl) ⟨1210581, by rfl⟩ : syracuseStep 3228217 = 2421163) B2421163
theorem B17217157 : Blo 2013435 17217157 := bstep (se 4 (by rfl) ⟨1614108, by rfl⟩ : syracuseStep 17217157 = 3228217) B3228217
theorem B22956209 : Blo 2013435 22956209 := bstep (se 2 (by rfl) ⟨8608578, by rfl⟩ : syracuseStep 22956209 = 17217157) B17217157
theorem B15304139 : Blo 2013435 15304139 := bstep (se 1 (by rfl) ⟨11478104, by rfl⟩ : syracuseStep 15304139 = 22956209) B22956209
theorem B10202759 : Blo 2013435 10202759 := bstep (se 1 (by rfl) ⟨7652069, by rfl⟩ : syracuseStep 10202759 = 15304139) B15304139
theorem B6801839 : Blo 2013435 6801839 := bstep (se 1 (by rfl) ⟨5101379, by rfl⟩ : syracuseStep 6801839 = 10202759) B10202759
theorem B4534559 : Blo 2013435 4534559 := bstep (se 1 (by rfl) ⟨3400919, by rfl⟩ : syracuseStep 4534559 = 6801839) B6801839
theorem B3023039 : Blo 2013435 3023039 := bstep (se 1 (by rfl) ⟨2267279, by rfl⟩ : syracuseStep 3023039 = 4534559) B4534559
theorem B2015359 : Blo 2013435 2015359 := bstep (se 1 (by rfl) ⟨1511519, by rfl⟩ : syracuseStep 2015359 = 3023039) B3023039
theorem B3023045 : Blo 2013435 3023045 := bbase (se 4 (by rfl) ⟨283410, by rfl⟩ : syracuseStep 3023045 = 566821) (by norm_num)
theorem B2015363 : Blo 2013435 2015363 := bstep (se 1 (by rfl) ⟨1511522, by rfl⟩ : syracuseStep 2015363 = 3023045) B3023045
theorem B3400933 : Blo 2013435 3400933 := bbase (se 4 (by rfl) ⟨318837, by rfl⟩ : syracuseStep 3400933 = 637675) (by norm_num)
theorem B4534577 : Blo 2013435 4534577 := bstep (se 2 (by rfl) ⟨1700466, by rfl⟩ : syracuseStep 4534577 = 3400933) B3400933
theorem B3023051 : Blo 2013435 3023051 := bstep (se 1 (by rfl) ⟨2267288, by rfl⟩ : syracuseStep 3023051 = 4534577) B4534577
theorem B2015367 : Blo 2013435 2015367 := bstep (se 1 (by rfl) ⟨1511525, by rfl⟩ : syracuseStep 2015367 = 3023051) B3023051
theorem B2267293 : Blo 2013435 2267293 := bbase (se 3 (by rfl) ⟨425117, by rfl⟩ : syracuseStep 2267293 = 850235) (by norm_num)
theorem B3023057 : Blo 2013435 3023057 := bstep (se 2 (by rfl) ⟨1133646, by rfl⟩ : syracuseStep 3023057 = 2267293) B2267293
theorem B2015371 : Blo 2013435 2015371 := bstep (se 1 (by rfl) ⟨1511528, by rfl⟩ : syracuseStep 2015371 = 3023057) B3023057
theorem B6801893 : Blo 2013435 6801893 := bbase (se 4 (by rfl) ⟨637677, by rfl⟩ : syracuseStep 6801893 = 1275355) (by norm_num)
theorem B4534595 : Blo 2013435 4534595 := bstep (se 1 (by rfl) ⟨3400946, by rfl⟩ : syracuseStep 4534595 = 6801893) B6801893
theorem B3023063 : Blo 2013435 3023063 := bstep (se 1 (by rfl) ⟨2267297, by rfl⟩ : syracuseStep 3023063 = 4534595) B4534595
theorem B2015375 : Blo 2013435 2015375 := bstep (se 1 (by rfl) ⟨1511531, by rfl⟩ : syracuseStep 2015375 = 3023063) B3023063
theorem B3023069 : Blo 2013435 3023069 := bbase (se 3 (by rfl) ⟨566825, by rfl⟩ : syracuseStep 3023069 = 1133651) (by norm_num)
theorem B2015379 : Blo 2013435 2015379 := bstep (se 1 (by rfl) ⟨1511534, by rfl⟩ : syracuseStep 2015379 = 3023069) B3023069
theorem B4534613 : Blo 2013435 4534613 := bbase (se 10 (by rfl) ⟨6642, by rfl⟩ : syracuseStep 4534613 = 13285) (by norm_num)
theorem B3023075 : Blo 2013435 3023075 := bstep (se 1 (by rfl) ⟨2267306, by rfl⟩ : syracuseStep 3023075 = 4534613) B4534613
theorem B2015383 : Blo 2013435 2015383 := bstep (se 1 (by rfl) ⟨1511537, by rfl⟩ : syracuseStep 2015383 = 3023075) B3023075
theorem B18385973 : Blo 2013435 18385973 := bbase (se 5 (by rfl) ⟨861842, by rfl⟩ : syracuseStep 18385973 = 1723685) (by norm_num)
theorem B12257315 : Blo 2013435 12257315 := bstep (se 1 (by rfl) ⟨9192986, by rfl⟩ : syracuseStep 12257315 = 18385973) B18385973
theorem B8171543 : Blo 2013435 8171543 := bstep (se 1 (by rfl) ⟨6128657, by rfl⟩ : syracuseStep 8171543 = 12257315) B12257315
theorem B5447695 : Blo 2013435 5447695 := bstep (se 1 (by rfl) ⟨4085771, by rfl⟩ : syracuseStep 5447695 = 8171543) B8171543
theorem B7263593 : Blo 2013435 7263593 := bstep (se 2 (by rfl) ⟨2723847, by rfl⟩ : syracuseStep 7263593 = 5447695) B5447695
theorem B4842395 : Blo 2013435 4842395 := bstep (se 1 (by rfl) ⟨3631796, by rfl⟩ : syracuseStep 4842395 = 7263593) B7263593
theorem B3228263 : Blo 2013435 3228263 := bstep (se 1 (by rfl) ⟨2421197, by rfl⟩ : syracuseStep 3228263 = 4842395) B4842395
theorem B2152175 : Blo 2013435 2152175 := bstep (se 1 (by rfl) ⟨1614131, by rfl⟩ : syracuseStep 2152175 = 3228263) B3228263
theorem B5739133 : Blo 2013435 5739133 := bstep (se 3 (by rfl) ⟨1076087, by rfl⟩ : syracuseStep 5739133 = 2152175) B2152175
theorem B7652177 : Blo 2013435 7652177 := bstep (se 2 (by rfl) ⟨2869566, by rfl⟩ : syracuseStep 7652177 = 5739133) B5739133
theorem B5101451 : Blo 2013435 5101451 := bstep (se 1 (by rfl) ⟨3826088, by rfl⟩ : syracuseStep 5101451 = 7652177) B7652177
theorem B3400967 : Blo 2013435 3400967 := bstep (se 1 (by rfl) ⟨2550725, by rfl⟩ : syracuseStep 3400967 = 5101451) B5101451
theorem B2267311 : Blo 2013435 2267311 := bstep (se 1 (by rfl) ⟨1700483, by rfl⟩ : syracuseStep 2267311 = 3400967) B3400967
theorem B3023081 : Blo 2013435 3023081 := bstep (se 2 (by rfl) ⟨1133655, by rfl⟩ : syracuseStep 3023081 = 2267311) B2267311
theorem B2015387 : Blo 2013435 2015387 := bstep (se 1 (by rfl) ⟨1511540, by rfl⟩ : syracuseStep 2015387 = 3023081) B3023081
theorem B38739221 : Blo 2013435 38739221 := bbase (se 6 (by rfl) ⟨907950, by rfl⟩ : syracuseStep 38739221 = 1815901) (by norm_num)
theorem B25826147 : Blo 2013435 25826147 := bstep (se 1 (by rfl) ⟨19369610, by rfl⟩ : syracuseStep 25826147 = 38739221) B38739221
theorem B17217431 : Blo 2013435 17217431 := bstep (se 1 (by rfl) ⟨12913073, by rfl⟩ : syracuseStep 17217431 = 25826147) B25826147
theorem B11478287 : Blo 2013435 11478287 := bstep (se 1 (by rfl) ⟨8608715, by rfl⟩ : syracuseStep 11478287 = 17217431) B17217431
theorem B7652191 : Blo 2013435 7652191 := bstep (se 1 (by rfl) ⟨5739143, by rfl⟩ : syracuseStep 7652191 = 11478287) B11478287
theorem B10202921 : Blo 2013435 10202921 := bstep (se 2 (by rfl) ⟨3826095, by rfl⟩ : syracuseStep 10202921 = 7652191) B7652191
theorem B6801947 : Blo 2013435 6801947 := bstep (se 1 (by rfl) ⟨5101460, by rfl⟩ : syracuseStep 6801947 = 10202921) B10202921
theorem B4534631 : Blo 2013435 4534631 := bstep (se 1 (by rfl) ⟨3400973, by rfl⟩ : syracuseStep 4534631 = 6801947) B6801947
theorem B3023087 : Blo 2013435 3023087 := bstep (se 1 (by rfl) ⟨2267315, by rfl⟩ : syracuseStep 3023087 = 4534631) B4534631
theorem B2015391 : Blo 2013435 2015391 := bstep (se 1 (by rfl) ⟨1511543, by rfl⟩ : syracuseStep 2015391 = 3023087) B3023087
theorem B3023093 : Blo 2013435 3023093 := bbase (se 5 (by rfl) ⟨141707, by rfl⟩ : syracuseStep 3023093 = 283415) (by norm_num)
theorem B2015395 : Blo 2013435 2015395 := bstep (se 1 (by rfl) ⟨1511546, by rfl⟩ : syracuseStep 2015395 = 3023093) B3023093
theorem B9950917 : Blo 2013435 9950917 := bbase (se 4 (by rfl) ⟨932898, by rfl⟩ : syracuseStep 9950917 = 1865797) (by norm_num)
theorem B13267889 : Blo 2013435 13267889 := bstep (se 2 (by rfl) ⟨4975458, by rfl⟩ : syracuseStep 13267889 = 9950917) B9950917
theorem B8845259 : Blo 2013435 8845259 := bstep (se 1 (by rfl) ⟨6633944, by rfl⟩ : syracuseStep 8845259 = 13267889) B13267889
theorem B23587357 : Blo 2013435 23587357 := bstep (se 3 (by rfl) ⟨4422629, by rfl⟩ : syracuseStep 23587357 = 8845259) B8845259
theorem B31449809 : Blo 2013435 31449809 := bstep (se 2 (by rfl) ⟨11793678, by rfl⟩ : syracuseStep 31449809 = 23587357) B23587357
theorem B20966539 : Blo 2013435 20966539 := bstep (se 1 (by rfl) ⟨15724904, by rfl⟩ : syracuseStep 20966539 = 31449809) B31449809
theorem B27955385 : Blo 2013435 27955385 := bstep (se 2 (by rfl) ⟨10483269, by rfl⟩ : syracuseStep 27955385 = 20966539) B20966539
theorem B18636923 : Blo 2013435 18636923 := bstep (se 1 (by rfl) ⟨13977692, by rfl⟩ : syracuseStep 18636923 = 27955385) B27955385
theorem B49698461 : Blo 2013435 49698461 := bstep (se 3 (by rfl) ⟨9318461, by rfl⟩ : syracuseStep 49698461 = 18636923) B18636923
theorem B132529229 : Blo 2013435 132529229 := bstep (se 3 (by rfl) ⟨24849230, by rfl⟩ : syracuseStep 132529229 = 49698461) B49698461
theorem B88352819 : Blo 2013435 88352819 := bstep (se 1 (by rfl) ⟨66264614, by rfl⟩ : syracuseStep 88352819 = 132529229) B132529229
theorem B58901879 : Blo 2013435 58901879 := bstep (se 1 (by rfl) ⟨44176409, by rfl⟩ : syracuseStep 58901879 = 88352819) B88352819
theorem B39267919 : Blo 2013435 39267919 := bstep (se 1 (by rfl) ⟨29450939, by rfl⟩ : syracuseStep 39267919 = 58901879) B58901879
theorem B52357225 : Blo 2013435 52357225 := bstep (se 2 (by rfl) ⟨19633959, by rfl⟩ : syracuseStep 52357225 = 39267919) B39267919
theorem B69809633 : Blo 2013435 69809633 := bstep (se 2 (by rfl) ⟨26178612, by rfl⟩ : syracuseStep 69809633 = 52357225) B52357225
theorem B46539755 : Blo 2013435 46539755 := bstep (se 1 (by rfl) ⟨34904816, by rfl⟩ : syracuseStep 46539755 = 69809633) B69809633
theorem B31026503 : Blo 2013435 31026503 := bstep (se 1 (by rfl) ⟨23269877, by rfl⟩ : syracuseStep 31026503 = 46539755) B46539755
theorem B20684335 : Blo 2013435 20684335 := bstep (se 1 (by rfl) ⟨15513251, by rfl⟩ : syracuseStep 20684335 = 31026503) B31026503
theorem B27579113 : Blo 2013435 27579113 := bstep (se 2 (by rfl) ⟨10342167, by rfl⟩ : syracuseStep 27579113 = 20684335) B20684335
theorem B18386075 : Blo 2013435 18386075 := bstep (se 1 (by rfl) ⟨13789556, by rfl⟩ : syracuseStep 18386075 = 27579113) B27579113
theorem B49029533 : Blo 2013435 49029533 := bstep (se 3 (by rfl) ⟨9193037, by rfl⟩ : syracuseStep 49029533 = 18386075) B18386075
theorem B32686355 : Blo 2013435 32686355 := bstep (se 1 (by rfl) ⟨24514766, by rfl⟩ : syracuseStep 32686355 = 49029533) B49029533
theorem B21790903 : Blo 2013435 21790903 := bstep (se 1 (by rfl) ⟨16343177, by rfl⟩ : syracuseStep 21790903 = 32686355) B32686355
theorem B29054537 : Blo 2013435 29054537 := bstep (se 2 (by rfl) ⟨10895451, by rfl⟩ : syracuseStep 29054537 = 21790903) B21790903
theorem B19369691 : Blo 2013435 19369691 := bstep (se 1 (by rfl) ⟨14527268, by rfl⟩ : syracuseStep 19369691 = 29054537) B29054537
theorem B12913127 : Blo 2013435 12913127 := bstep (se 1 (by rfl) ⟨9684845, by rfl⟩ : syracuseStep 12913127 = 19369691) B19369691
theorem B8608751 : Blo 2013435 8608751 := bstep (se 1 (by rfl) ⟨6456563, by rfl⟩ : syracuseStep 8608751 = 12913127) B12913127
theorem B5739167 : Blo 2013435 5739167 := bstep (se 1 (by rfl) ⟨4304375, by rfl⟩ : syracuseStep 5739167 = 8608751) B8608751
theorem B3826111 : Blo 2013435 3826111 := bstep (se 1 (by rfl) ⟨2869583, by rfl⟩ : syracuseStep 3826111 = 5739167) B5739167
theorem B5101481 : Blo 2013435 5101481 := bstep (se 2 (by rfl) ⟨1913055, by rfl⟩ : syracuseStep 5101481 = 3826111) B3826111
theorem B3400987 : Blo 2013435 3400987 := bstep (se 1 (by rfl) ⟨2550740, by rfl⟩ : syracuseStep 3400987 = 5101481) B5101481
theorem B4534649 : Blo 2013435 4534649 := bstep (se 2 (by rfl) ⟨1700493, by rfl⟩ : syracuseStep 4534649 = 3400987) B3400987
theorem B3023099 : Blo 2013435 3023099 := bstep (se 1 (by rfl) ⟨2267324, by rfl⟩ : syracuseStep 3023099 = 4534649) B4534649
theorem B2015399 : Blo 2013435 2015399 := bstep (se 1 (by rfl) ⟨1511549, by rfl⟩ : syracuseStep 2015399 = 3023099) B3023099
theorem B2267329 : Blo 2013435 2267329 := bbase (se 2 (by rfl) ⟨850248, by rfl⟩ : syracuseStep 2267329 = 1700497) (by norm_num)
theorem B3023105 : Blo 2013435 3023105 := bstep (se 2 (by rfl) ⟨1133664, by rfl⟩ : syracuseStep 3023105 = 2267329) B2267329
theorem B2015403 : Blo 2013435 2015403 := bstep (se 1 (by rfl) ⟨1511552, by rfl⟩ : syracuseStep 2015403 = 3023105) B3023105
theorem B5101501 : Blo 2013435 5101501 := bbase (se 3 (by rfl) ⟨956531, by rfl⟩ : syracuseStep 5101501 = 1913063) (by norm_num)
theorem B6802001 : Blo 2013435 6802001 := bstep (se 2 (by rfl) ⟨2550750, by rfl⟩ : syracuseStep 6802001 = 5101501) B5101501
theorem B4534667 : Blo 2013435 4534667 := bstep (se 1 (by rfl) ⟨3401000, by rfl⟩ : syracuseStep 4534667 = 6802001) B6802001
theorem B3023111 : Blo 2013435 3023111 := bstep (se 1 (by rfl) ⟨2267333, by rfl⟩ : syracuseStep 3023111 = 4534667) B4534667
theorem B2015407 : Blo 2013435 2015407 := bstep (se 1 (by rfl) ⟨1511555, by rfl⟩ : syracuseStep 2015407 = 3023111) B3023111
theorem B3023117 : Blo 2013435 3023117 := bbase (se 3 (by rfl) ⟨566834, by rfl⟩ : syracuseStep 3023117 = 1133669) (by norm_num)
theorem B2015411 : Blo 2013435 2015411 := bstep (se 1 (by rfl) ⟨1511558, by rfl⟩ : syracuseStep 2015411 = 3023117) B3023117
theorem B4534685 : Blo 2013435 4534685 := bbase (se 3 (by rfl) ⟨850253, by rfl⟩ : syracuseStep 4534685 = 1700507) (by norm_num)
theorem B3023123 : Blo 2013435 3023123 := bstep (se 1 (by rfl) ⟨2267342, by rfl⟩ : syracuseStep 3023123 = 4534685) B4534685
theorem B2015415 : Blo 2013435 2015415 := bstep (se 1 (by rfl) ⟨1511561, by rfl⟩ : syracuseStep 2015415 = 3023123) B3023123
theorem B3401021 : Blo 2013435 3401021 := bbase (se 3 (by rfl) ⟨637691, by rfl⟩ : syracuseStep 3401021 = 1275383) (by norm_num)
theorem B2267347 : Blo 2013435 2267347 := bstep (se 1 (by rfl) ⟨1700510, by rfl⟩ : syracuseStep 2267347 = 3401021) B3401021
theorem B3023129 : Blo 2013435 3023129 := bstep (se 2 (by rfl) ⟨1133673, by rfl⟩ : syracuseStep 3023129 = 2267347) B2267347
theorem B2015419 : Blo 2013435 2015419 := bstep (se 1 (by rfl) ⟨1511564, by rfl⟩ : syracuseStep 2015419 = 3023129) B3023129
theorem B2152213 : Blo 2013435 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B11478469 : Blo 2013435 11478469 := bstep (se 4 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 11478469 = 2152213) B2152213
theorem B15304625 : Blo 2013435 15304625 := bstep (se 2 (by rfl) ⟨5739234, by rfl⟩ : syracuseStep 15304625 = 11478469) B11478469
theorem B10203083 : Blo 2013435 10203083 := bstep (se 1 (by rfl) ⟨7652312, by rfl⟩ : syracuseStep 10203083 = 15304625) B15304625
theorem B6802055 : Blo 2013435 6802055 := bstep (se 1 (by rfl) ⟨5101541, by rfl⟩ : syracuseStep 6802055 = 10203083) B10203083
theorem B4534703 : Blo 2013435 4534703 := bstep (se 1 (by rfl) ⟨3401027, by rfl⟩ : syracuseStep 4534703 = 6802055) B6802055
theorem B3023135 : Blo 2013435 3023135 := bstep (se 1 (by rfl) ⟨2267351, by rfl⟩ : syracuseStep 3023135 = 4534703) B4534703
theorem B2015423 : Blo 2013435 2015423 := bstep (se 1 (by rfl) ⟨1511567, by rfl⟩ : syracuseStep 2015423 = 3023135) B3023135
theorem B3023141 : Blo 2013435 3023141 := bbase (se 4 (by rfl) ⟨283419, by rfl⟩ : syracuseStep 3023141 = 566839) (by norm_num)
theorem B2015427 : Blo 2013435 2015427 := bstep (se 1 (by rfl) ⟨1511570, by rfl⟩ : syracuseStep 2015427 = 3023141) B3023141
theorem B2550781 : Blo 2013435 2550781 := bbase (se 3 (by rfl) ⟨478271, by rfl⟩ : syracuseStep 2550781 = 956543) (by norm_num)
theorem B3401041 : Blo 2013435 3401041 := bstep (se 2 (by rfl) ⟨1275390, by rfl⟩ : syracuseStep 3401041 = 2550781) B2550781
theorem B4534721 : Blo 2013435 4534721 := bstep (se 2 (by rfl) ⟨1700520, by rfl⟩ : syracuseStep 4534721 = 3401041) B3401041
theorem B3023147 : Blo 2013435 3023147 := bstep (se 1 (by rfl) ⟨2267360, by rfl⟩ : syracuseStep 3023147 = 4534721) B4534721
theorem B2015431 : Blo 2013435 2015431 := bstep (se 1 (by rfl) ⟨1511573, by rfl⟩ : syracuseStep 2015431 = 3023147) B3023147
theorem B2267365 : Blo 2013435 2267365 := bbase (se 4 (by rfl) ⟨212565, by rfl⟩ : syracuseStep 2267365 = 425131) (by norm_num)
theorem B3023153 : Blo 2013435 3023153 := bstep (se 2 (by rfl) ⟨1133682, by rfl⟩ : syracuseStep 3023153 = 2267365) B2267365
theorem B2015435 : Blo 2013435 2015435 := bstep (se 1 (by rfl) ⟨1511576, by rfl⟩ : syracuseStep 2015435 = 3023153) B3023153
theorem C0 (j : ℕ) (h1 : 503358 ≤ j) (h2 : j ≤ 503858) : Blo 2013435 (4 * j + 3) := by
  interval_cases j
  · exact B2013435
  · exact B2013439
  · exact B2013443
  · exact B2013447
  · exact B2013451
  · exact B2013455
  · exact B2013459
  · exact B2013463
  · exact B2013467
  · exact B2013471
  · exact B2013475
  · exact B2013479
  · exact B2013483
  · exact B2013487
  · exact B2013491
  · exact B2013495
  · exact B2013499
  · exact B2013503
  · exact B2013507
  · exact B2013511
  · exact B2013515
  · exact B2013519
  · exact B2013523
  · exact B2013527
  · exact B2013531
  · exact B2013535
  · exact B2013539
  · exact B2013543
  · exact B2013547
  · exact B2013551
  · exact B2013555
  · exact B2013559
  · exact B2013563
  · exact B2013567
  · exact B2013571
  · exact B2013575
  · exact B2013579
  · exact B2013583
  · exact B2013587
  · exact B2013591
  · exact B2013595
  · exact B2013599
  · exact B2013603
  · exact B2013607
  · exact B2013611
  · exact B2013615
  · exact B2013619
  · exact B2013623
  · exact B2013627
  · exact B2013631
  · exact B2013635
  · exact B2013639
  · exact B2013643
  · exact B2013647
  · exact B2013651
  · exact B2013655
  · exact B2013659
  · exact B2013663
  · exact B2013667
  · exact B2013671
  · exact B2013675
  · exact B2013679
  · exact B2013683
  · exact B2013687
  · exact B2013691
  · exact B2013695
  · exact B2013699
  · exact B2013703
  · exact B2013707
  · exact B2013711
  · exact B2013715
  · exact B2013719
  · exact B2013723
  · exact B2013727
  · exact B2013731
  · exact B2013735
  · exact B2013739
  · exact B2013743
  · exact B2013747
  · exact B2013751
  · exact B2013755
  · exact B2013759
  · exact B2013763
  · exact B2013767
  · exact B2013771
  · exact B2013775
  · exact B2013779
  · exact B2013783
  · exact B2013787
  · exact B2013791
  · exact B2013795
  · exact B2013799
  · exact B2013803
  · exact B2013807
  · exact B2013811
  · exact B2013815
  · exact B2013819
  · exact B2013823
  · exact B2013827
  · exact B2013831
  · exact B2013835
  · exact B2013839
  · exact B2013843
  · exact B2013847
  · exact B2013851
  · exact B2013855
  · exact B2013859
  · exact B2013863
  · exact B2013867
  · exact B2013871
  · exact B2013875
  · exact B2013879
  · exact B2013883
  · exact B2013887
  · exact B2013891
  · exact B2013895
  · exact B2013899
  · exact B2013903
  · exact B2013907
  · exact B2013911
  · exact B2013915
  · exact B2013919
  · exact B2013923
  · exact B2013927
  · exact B2013931
  · exact B2013935
  · exact B2013939
  · exact B2013943
  · exact B2013947
  · exact B2013951
  · exact B2013955
  · exact B2013959
  · exact B2013963
  · exact B2013967
  · exact B2013971
  · exact B2013975
  · exact B2013979
  · exact B2013983
  · exact B2013987
  · exact B2013991
  · exact B2013995
  · exact B2013999
  · exact B2014003
  · exact B2014007
  · exact B2014011
  · exact B2014015
  · exact B2014019
  · exact B2014023
  · exact B2014027
  · exact B2014031
  · exact B2014035
  · exact B2014039
  · exact B2014043
  · exact B2014047
  · exact B2014051
  · exact B2014055
  · exact B2014059
  · exact B2014063
  · exact B2014067
  · exact B2014071
  · exact B2014075
  · exact B2014079
  · exact B2014083
  · exact B2014087
  · exact B2014091
  · exact B2014095
  · exact B2014099
  · exact B2014103
  · exact B2014107
  · exact B2014111
  · exact B2014115
  · exact B2014119
  · exact B2014123
  · exact B2014127
  · exact B2014131
  · exact B2014135
  · exact B2014139
  · exact B2014143
  · exact B2014147
  · exact B2014151
  · exact B2014155
  · exact B2014159
  · exact B2014163
  · exact B2014167
  · exact B2014171
  · exact B2014175
  · exact B2014179
  · exact B2014183
  · exact B2014187
  · exact B2014191
  · exact B2014195
  · exact B2014199
  · exact B2014203
  · exact B2014207
  · exact B2014211
  · exact B2014215
  · exact B2014219
  · exact B2014223
  · exact B2014227
  · exact B2014231
  · exact B2014235
  · exact B2014239
  · exact B2014243
  · exact B2014247
  · exact B2014251
  · exact B2014255
  · exact B2014259
  · exact B2014263
  · exact B2014267
  · exact B2014271
  · exact B2014275
  · exact B2014279
  · exact B2014283
  · exact B2014287
  · exact B2014291
  · exact B2014295
  · exact B2014299
  · exact B2014303
  · exact B2014307
  · exact B2014311
  · exact B2014315
  · exact B2014319
  · exact B2014323
  · exact B2014327
  · exact B2014331
  · exact B2014335
  · exact B2014339
  · exact B2014343
  · exact B2014347
  · exact B2014351
  · exact B2014355
  · exact B2014359
  · exact B2014363
  · exact B2014367
  · exact B2014371
  · exact B2014375
  · exact B2014379
  · exact B2014383
  · exact B2014387
  · exact B2014391
  · exact B2014395
  · exact B2014399
  · exact B2014403
  · exact B2014407
  · exact B2014411
  · exact B2014415
  · exact B2014419
  · exact B2014423
  · exact B2014427
  · exact B2014431
  · exact B2014435
  · exact B2014439
  · exact B2014443
  · exact B2014447
  · exact B2014451
  · exact B2014455
  · exact B2014459
  · exact B2014463
  · exact B2014467
  · exact B2014471
  · exact B2014475
  · exact B2014479
  · exact B2014483
  · exact B2014487
  · exact B2014491
  · exact B2014495
  · exact B2014499
  · exact B2014503
  · exact B2014507
  · exact B2014511
  · exact B2014515
  · exact B2014519
  · exact B2014523
  · exact B2014527
  · exact B2014531
  · exact B2014535
  · exact B2014539
  · exact B2014543
  · exact B2014547
  · exact B2014551
  · exact B2014555
  · exact B2014559
  · exact B2014563
  · exact B2014567
  · exact B2014571
  · exact B2014575
  · exact B2014579
  · exact B2014583
  · exact B2014587
  · exact B2014591
  · exact B2014595
  · exact B2014599
  · exact B2014603
  · exact B2014607
  · exact B2014611
  · exact B2014615
  · exact B2014619
  · exact B2014623
  · exact B2014627
  · exact B2014631
  · exact B2014635
  · exact B2014639
  · exact B2014643
  · exact B2014647
  · exact B2014651
  · exact B2014655
  · exact B2014659
  · exact B2014663
  · exact B2014667
  · exact B2014671
  · exact B2014675
  · exact B2014679
  · exact B2014683
  · exact B2014687
  · exact B2014691
  · exact B2014695
  · exact B2014699
  · exact B2014703
  · exact B2014707
  · exact B2014711
  · exact B2014715
  · exact B2014719
  · exact B2014723
  · exact B2014727
  · exact B2014731
  · exact B2014735
  · exact B2014739
  · exact B2014743
  · exact B2014747
  · exact B2014751
  · exact B2014755
  · exact B2014759
  · exact B2014763
  · exact B2014767
  · exact B2014771
  · exact B2014775
  · exact B2014779
  · exact B2014783
  · exact B2014787
  · exact B2014791
  · exact B2014795
  · exact B2014799
  · exact B2014803
  · exact B2014807
  · exact B2014811
  · exact B2014815
  · exact B2014819
  · exact B2014823
  · exact B2014827
  · exact B2014831
  · exact B2014835
  · exact B2014839
  · exact B2014843
  · exact B2014847
  · exact B2014851
  · exact B2014855
  · exact B2014859
  · exact B2014863
  · exact B2014867
  · exact B2014871
  · exact B2014875
  · exact B2014879
  · exact B2014883
  · exact B2014887
  · exact B2014891
  · exact B2014895
  · exact B2014899
  · exact B2014903
  · exact B2014907
  · exact B2014911
  · exact B2014915
  · exact B2014919
  · exact B2014923
  · exact B2014927
  · exact B2014931
  · exact B2014935
  · exact B2014939
  · exact B2014943
  · exact B2014947
  · exact B2014951
  · exact B2014955
  · exact B2014959
  · exact B2014963
  · exact B2014967
  · exact B2014971
  · exact B2014975
  · exact B2014979
  · exact B2014983
  · exact B2014987
  · exact B2014991
  · exact B2014995
  · exact B2014999
  · exact B2015003
  · exact B2015007
  · exact B2015011
  · exact B2015015
  · exact B2015019
  · exact B2015023
  · exact B2015027
  · exact B2015031
  · exact B2015035
  · exact B2015039
  · exact B2015043
  · exact B2015047
  · exact B2015051
  · exact B2015055
  · exact B2015059
  · exact B2015063
  · exact B2015067
  · exact B2015071
  · exact B2015075
  · exact B2015079
  · exact B2015083
  · exact B2015087
  · exact B2015091
  · exact B2015095
  · exact B2015099
  · exact B2015103
  · exact B2015107
  · exact B2015111
  · exact B2015115
  · exact B2015119
  · exact B2015123
  · exact B2015127
  · exact B2015131
  · exact B2015135
  · exact B2015139
  · exact B2015143
  · exact B2015147
  · exact B2015151
  · exact B2015155
  · exact B2015159
  · exact B2015163
  · exact B2015167
  · exact B2015171
  · exact B2015175
  · exact B2015179
  · exact B2015183
  · exact B2015187
  · exact B2015191
  · exact B2015195
  · exact B2015199
  · exact B2015203
  · exact B2015207
  · exact B2015211
  · exact B2015215
  · exact B2015219
  · exact B2015223
  · exact B2015227
  · exact B2015231
  · exact B2015235
  · exact B2015239
  · exact B2015243
  · exact B2015247
  · exact B2015251
  · exact B2015255
  · exact B2015259
  · exact B2015263
  · exact B2015267
  · exact B2015271
  · exact B2015275
  · exact B2015279
  · exact B2015283
  · exact B2015287
  · exact B2015291
  · exact B2015295
  · exact B2015299
  · exact B2015303
  · exact B2015307
  · exact B2015311
  · exact B2015315
  · exact B2015319
  · exact B2015323
  · exact B2015327
  · exact B2015331
  · exact B2015335
  · exact B2015339
  · exact B2015343
  · exact B2015347
  · exact B2015351
  · exact B2015355
  · exact B2015359
  · exact B2015363
  · exact B2015367
  · exact B2015371
  · exact B2015375
  · exact B2015379
  · exact B2015383
  · exact B2015387
  · exact B2015391
  · exact B2015395
  · exact B2015399
  · exact B2015403
  · exact B2015407
  · exact B2015411
  · exact B2015415
  · exact B2015419
  · exact B2015423
  · exact B2015427
  · exact B2015431
  · exact B2015435
theorem solution (m : ℕ) (hlo : 2013435 ≤ m) (hhi : m ≤ 2015435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 503358 ≤ j := by omega
    have hj2 : j ≤ 503858 := by omega
    have hb : Blo 2013435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
