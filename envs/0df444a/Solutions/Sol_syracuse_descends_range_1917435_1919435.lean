-- Prove2me | solution 1 for syracuse_descends_range_1917435_1919435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:08.190087+00:00
-- url     : https://prove2.me/submissions/8383b084-39af-4b2d-982e-8bdcb6ac2b76

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

theorem B3640133 : Blo 1917435 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B2426755 : Blo 1917435 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B3235673 : Blo 1917435 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B2157115 : Blo 1917435 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B2876153 : Blo 1917435 2876153 := bstep (se 2 (by rfl) ⟨1078557, by rfl⟩ : syracuseStep 2876153 = 2157115) B2157115
theorem B1917435 : Blo 1917435 1917435 := bstep (se 1 (by rfl) ⟨1438076, by rfl⟩ : syracuseStep 1917435 = 2876153) B2876153
theorem B9839477 : Blo 1917435 9839477 := bbase (se 5 (by rfl) ⟨461225, by rfl⟩ : syracuseStep 9839477 = 922451) (by norm_num)
theorem B6559651 : Blo 1917435 6559651 := bstep (se 1 (by rfl) ⟨4919738, by rfl⟩ : syracuseStep 6559651 = 9839477) B9839477
theorem B8746201 : Blo 1917435 8746201 := bstep (se 2 (by rfl) ⟨3279825, by rfl⟩ : syracuseStep 8746201 = 6559651) B6559651
theorem B46646405 : Blo 1917435 46646405 := bstep (se 4 (by rfl) ⟨4373100, by rfl⟩ : syracuseStep 46646405 = 8746201) B8746201
theorem B31097603 : Blo 1917435 31097603 := bstep (se 1 (by rfl) ⟨23323202, by rfl⟩ : syracuseStep 31097603 = 46646405) B46646405
theorem B20731735 : Blo 1917435 20731735 := bstep (se 1 (by rfl) ⟨15548801, by rfl⟩ : syracuseStep 20731735 = 31097603) B31097603
theorem B27642313 : Blo 1917435 27642313 := bstep (se 2 (by rfl) ⟨10365867, by rfl⟩ : syracuseStep 27642313 = 20731735) B20731735
theorem B36856417 : Blo 1917435 36856417 := bstep (se 2 (by rfl) ⟨13821156, by rfl⟩ : syracuseStep 36856417 = 27642313) B27642313
theorem B49141889 : Blo 1917435 49141889 := bstep (se 2 (by rfl) ⟨18428208, by rfl⟩ : syracuseStep 49141889 = 36856417) B36856417
theorem B32761259 : Blo 1917435 32761259 := bstep (se 1 (by rfl) ⟨24570944, by rfl⟩ : syracuseStep 32761259 = 49141889) B49141889
theorem B21840839 : Blo 1917435 21840839 := bstep (se 1 (by rfl) ⟨16380629, by rfl⟩ : syracuseStep 21840839 = 32761259) B32761259
theorem B14560559 : Blo 1917435 14560559 := bstep (se 1 (by rfl) ⟨10920419, by rfl⟩ : syracuseStep 14560559 = 21840839) B21840839
theorem B9707039 : Blo 1917435 9707039 := bstep (se 1 (by rfl) ⟨7280279, by rfl⟩ : syracuseStep 9707039 = 14560559) B14560559
theorem B6471359 : Blo 1917435 6471359 := bstep (se 1 (by rfl) ⟨4853519, by rfl⟩ : syracuseStep 6471359 = 9707039) B9707039
theorem B4314239 : Blo 1917435 4314239 := bstep (se 1 (by rfl) ⟨3235679, by rfl⟩ : syracuseStep 4314239 = 6471359) B6471359
theorem B2876159 : Blo 1917435 2876159 := bstep (se 1 (by rfl) ⟨2157119, by rfl⟩ : syracuseStep 2876159 = 4314239) B4314239
theorem B1917439 : Blo 1917435 1917439 := bstep (se 1 (by rfl) ⟨1438079, by rfl⟩ : syracuseStep 1917439 = 2876159) B2876159
theorem B2876165 : Blo 1917435 2876165 := bbase (se 4 (by rfl) ⟨269640, by rfl⟩ : syracuseStep 2876165 = 539281) (by norm_num)
theorem B1917443 : Blo 1917435 1917443 := bstep (se 1 (by rfl) ⟨1438082, by rfl⟩ : syracuseStep 1917443 = 2876165) B2876165
theorem B3235693 : Blo 1917435 3235693 := bbase (se 3 (by rfl) ⟨606692, by rfl⟩ : syracuseStep 3235693 = 1213385) (by norm_num)
theorem B4314257 : Blo 1917435 4314257 := bstep (se 2 (by rfl) ⟨1617846, by rfl⟩ : syracuseStep 4314257 = 3235693) B3235693
theorem B2876171 : Blo 1917435 2876171 := bstep (se 1 (by rfl) ⟨2157128, by rfl⟩ : syracuseStep 2876171 = 4314257) B4314257
theorem B1917447 : Blo 1917435 1917447 := bstep (se 1 (by rfl) ⟨1438085, by rfl⟩ : syracuseStep 1917447 = 2876171) B2876171
theorem B2157133 : Blo 1917435 2157133 := bbase (se 3 (by rfl) ⟨404462, by rfl⟩ : syracuseStep 2157133 = 808925) (by norm_num)
theorem B2876177 : Blo 1917435 2876177 := bstep (se 2 (by rfl) ⟨1078566, by rfl⟩ : syracuseStep 2876177 = 2157133) B2157133
theorem B1917451 : Blo 1917435 1917451 := bstep (se 1 (by rfl) ⟨1438088, by rfl⟩ : syracuseStep 1917451 = 2876177) B2876177
theorem B6471413 : Blo 1917435 6471413 := bbase (se 5 (by rfl) ⟨303347, by rfl⟩ : syracuseStep 6471413 = 606695) (by norm_num)
theorem B4314275 : Blo 1917435 4314275 := bstep (se 1 (by rfl) ⟨3235706, by rfl⟩ : syracuseStep 4314275 = 6471413) B6471413
theorem B2876183 : Blo 1917435 2876183 := bstep (se 1 (by rfl) ⟨2157137, by rfl⟩ : syracuseStep 2876183 = 4314275) B4314275
theorem B1917455 : Blo 1917435 1917455 := bstep (se 1 (by rfl) ⟨1438091, by rfl⟩ : syracuseStep 1917455 = 2876183) B2876183
theorem B2876189 : Blo 1917435 2876189 := bbase (se 3 (by rfl) ⟨539285, by rfl⟩ : syracuseStep 2876189 = 1078571) (by norm_num)
theorem B1917459 : Blo 1917435 1917459 := bstep (se 1 (by rfl) ⟨1438094, by rfl⟩ : syracuseStep 1917459 = 2876189) B2876189
theorem B4314293 : Blo 1917435 4314293 := bbase (se 5 (by rfl) ⟨202232, by rfl⟩ : syracuseStep 4314293 = 404465) (by norm_num)
theorem B2876195 : Blo 1917435 2876195 := bstep (se 1 (by rfl) ⟨2157146, by rfl⟩ : syracuseStep 2876195 = 4314293) B4314293
theorem B1917463 : Blo 1917435 1917463 := bstep (se 1 (by rfl) ⟨1438097, by rfl⟩ : syracuseStep 1917463 = 2876195) B2876195
theorem B2047609 : Blo 1917435 2047609 := bbase (se 2 (by rfl) ⟨767853, by rfl⟩ : syracuseStep 2047609 = 1535707) (by norm_num)
theorem B10920581 : Blo 1917435 10920581 := bstep (se 4 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 10920581 = 2047609) B2047609
theorem B7280387 : Blo 1917435 7280387 := bstep (se 1 (by rfl) ⟨5460290, by rfl⟩ : syracuseStep 7280387 = 10920581) B10920581
theorem B4853591 : Blo 1917435 4853591 := bstep (se 1 (by rfl) ⟨3640193, by rfl⟩ : syracuseStep 4853591 = 7280387) B7280387
theorem B3235727 : Blo 1917435 3235727 := bstep (se 1 (by rfl) ⟨2426795, by rfl⟩ : syracuseStep 3235727 = 4853591) B4853591
theorem B2157151 : Blo 1917435 2157151 := bstep (se 1 (by rfl) ⟨1617863, by rfl⟩ : syracuseStep 2157151 = 3235727) B3235727
theorem B2876201 : Blo 1917435 2876201 := bstep (se 2 (by rfl) ⟨1078575, by rfl⟩ : syracuseStep 2876201 = 2157151) B2157151
theorem B1917467 : Blo 1917435 1917467 := bstep (se 1 (by rfl) ⟨1438100, by rfl⟩ : syracuseStep 1917467 = 2876201) B2876201
theorem B2047613 : Blo 1917435 2047613 := bbase (se 3 (by rfl) ⟨383927, by rfl⟩ : syracuseStep 2047613 = 767855) (by norm_num)
theorem B5460301 : Blo 1917435 5460301 := bstep (se 3 (by rfl) ⟨1023806, by rfl⟩ : syracuseStep 5460301 = 2047613) B2047613
theorem B7280401 : Blo 1917435 7280401 := bstep (se 2 (by rfl) ⟨2730150, by rfl⟩ : syracuseStep 7280401 = 5460301) B5460301
theorem B9707201 : Blo 1917435 9707201 := bstep (se 2 (by rfl) ⟨3640200, by rfl⟩ : syracuseStep 9707201 = 7280401) B7280401
theorem B6471467 : Blo 1917435 6471467 := bstep (se 1 (by rfl) ⟨4853600, by rfl⟩ : syracuseStep 6471467 = 9707201) B9707201
theorem B4314311 : Blo 1917435 4314311 := bstep (se 1 (by rfl) ⟨3235733, by rfl⟩ : syracuseStep 4314311 = 6471467) B6471467
theorem B2876207 : Blo 1917435 2876207 := bstep (se 1 (by rfl) ⟨2157155, by rfl⟩ : syracuseStep 2876207 = 4314311) B4314311
theorem B1917471 : Blo 1917435 1917471 := bstep (se 1 (by rfl) ⟨1438103, by rfl⟩ : syracuseStep 1917471 = 2876207) B2876207
theorem B2876213 : Blo 1917435 2876213 := bbase (se 5 (by rfl) ⟨134822, by rfl⟩ : syracuseStep 2876213 = 269645) (by norm_num)
theorem B1917475 : Blo 1917435 1917475 := bstep (se 1 (by rfl) ⟨1438106, by rfl⟩ : syracuseStep 1917475 = 2876213) B2876213
theorem B4853621 : Blo 1917435 4853621 := bbase (se 5 (by rfl) ⟨227513, by rfl⟩ : syracuseStep 4853621 = 455027) (by norm_num)
theorem B3235747 : Blo 1917435 3235747 := bstep (se 1 (by rfl) ⟨2426810, by rfl⟩ : syracuseStep 3235747 = 4853621) B4853621
theorem B4314329 : Blo 1917435 4314329 := bstep (se 2 (by rfl) ⟨1617873, by rfl⟩ : syracuseStep 4314329 = 3235747) B3235747
theorem B2876219 : Blo 1917435 2876219 := bstep (se 1 (by rfl) ⟨2157164, by rfl⟩ : syracuseStep 2876219 = 4314329) B4314329
theorem B1917479 : Blo 1917435 1917479 := bstep (se 1 (by rfl) ⟨1438109, by rfl⟩ : syracuseStep 1917479 = 2876219) B2876219
theorem B2157169 : Blo 1917435 2157169 := bbase (se 2 (by rfl) ⟨808938, by rfl⟩ : syracuseStep 2157169 = 1617877) (by norm_num)
theorem B2876225 : Blo 1917435 2876225 := bstep (se 2 (by rfl) ⟨1078584, by rfl⟩ : syracuseStep 2876225 = 2157169) B2157169
theorem B1917483 : Blo 1917435 1917483 := bstep (se 1 (by rfl) ⟨1438112, by rfl⟩ : syracuseStep 1917483 = 2876225) B2876225
theorem B5830949 : Blo 1917435 5830949 := bbase (se 4 (by rfl) ⟨546651, by rfl⟩ : syracuseStep 5830949 = 1093303) (by norm_num)
theorem B3887299 : Blo 1917435 3887299 := bstep (se 1 (by rfl) ⟨2915474, by rfl⟩ : syracuseStep 3887299 = 5830949) B5830949
theorem B5183065 : Blo 1917435 5183065 := bstep (se 2 (by rfl) ⟨1943649, by rfl⟩ : syracuseStep 5183065 = 3887299) B3887299
theorem B6910753 : Blo 1917435 6910753 := bstep (se 2 (by rfl) ⟨2591532, by rfl⟩ : syracuseStep 6910753 = 5183065) B5183065
theorem B9214337 : Blo 1917435 9214337 := bstep (se 2 (by rfl) ⟨3455376, by rfl⟩ : syracuseStep 9214337 = 6910753) B6910753
theorem B6142891 : Blo 1917435 6142891 := bstep (se 1 (by rfl) ⟨4607168, by rfl⟩ : syracuseStep 6142891 = 9214337) B9214337
theorem B8190521 : Blo 1917435 8190521 := bstep (se 2 (by rfl) ⟨3071445, by rfl⟩ : syracuseStep 8190521 = 6142891) B6142891
theorem B5460347 : Blo 1917435 5460347 := bstep (se 1 (by rfl) ⟨4095260, by rfl⟩ : syracuseStep 5460347 = 8190521) B8190521
theorem B3640231 : Blo 1917435 3640231 := bstep (se 1 (by rfl) ⟨2730173, by rfl⟩ : syracuseStep 3640231 = 5460347) B5460347
theorem B4853641 : Blo 1917435 4853641 := bstep (se 2 (by rfl) ⟨1820115, by rfl⟩ : syracuseStep 4853641 = 3640231) B3640231
theorem B6471521 : Blo 1917435 6471521 := bstep (se 2 (by rfl) ⟨2426820, by rfl⟩ : syracuseStep 6471521 = 4853641) B4853641
theorem B4314347 : Blo 1917435 4314347 := bstep (se 1 (by rfl) ⟨3235760, by rfl⟩ : syracuseStep 4314347 = 6471521) B6471521
theorem B2876231 : Blo 1917435 2876231 := bstep (se 1 (by rfl) ⟨2157173, by rfl⟩ : syracuseStep 2876231 = 4314347) B4314347
theorem B1917487 : Blo 1917435 1917487 := bstep (se 1 (by rfl) ⟨1438115, by rfl⟩ : syracuseStep 1917487 = 2876231) B2876231
theorem B2876237 : Blo 1917435 2876237 := bbase (se 3 (by rfl) ⟨539294, by rfl⟩ : syracuseStep 2876237 = 1078589) (by norm_num)
theorem B1917491 : Blo 1917435 1917491 := bstep (se 1 (by rfl) ⟨1438118, by rfl⟩ : syracuseStep 1917491 = 2876237) B2876237
theorem B4314365 : Blo 1917435 4314365 := bbase (se 3 (by rfl) ⟨808943, by rfl⟩ : syracuseStep 4314365 = 1617887) (by norm_num)
theorem B2876243 : Blo 1917435 2876243 := bstep (se 1 (by rfl) ⟨2157182, by rfl⟩ : syracuseStep 2876243 = 4314365) B4314365
theorem B1917495 : Blo 1917435 1917495 := bstep (se 1 (by rfl) ⟨1438121, by rfl⟩ : syracuseStep 1917495 = 2876243) B2876243
theorem B3235781 : Blo 1917435 3235781 := bbase (se 4 (by rfl) ⟨303354, by rfl⟩ : syracuseStep 3235781 = 606709) (by norm_num)
theorem B2157187 : Blo 1917435 2157187 := bstep (se 1 (by rfl) ⟨1617890, by rfl⟩ : syracuseStep 2157187 = 3235781) B3235781
theorem B2876249 : Blo 1917435 2876249 := bstep (se 2 (by rfl) ⟨1078593, by rfl⟩ : syracuseStep 2876249 = 2157187) B2157187
theorem B1917499 : Blo 1917435 1917499 := bstep (se 1 (by rfl) ⟨1438124, by rfl⟩ : syracuseStep 1917499 = 2876249) B2876249
theorem B14561045 : Blo 1917435 14561045 := bbase (se 6 (by rfl) ⟨341274, by rfl⟩ : syracuseStep 14561045 = 682549) (by norm_num)
theorem B9707363 : Blo 1917435 9707363 := bstep (se 1 (by rfl) ⟨7280522, by rfl⟩ : syracuseStep 9707363 = 14561045) B14561045
theorem B6471575 : Blo 1917435 6471575 := bstep (se 1 (by rfl) ⟨4853681, by rfl⟩ : syracuseStep 6471575 = 9707363) B9707363
theorem B4314383 : Blo 1917435 4314383 := bstep (se 1 (by rfl) ⟨3235787, by rfl⟩ : syracuseStep 4314383 = 6471575) B6471575
theorem B2876255 : Blo 1917435 2876255 := bstep (se 1 (by rfl) ⟨2157191, by rfl⟩ : syracuseStep 2876255 = 4314383) B4314383
theorem B1917503 : Blo 1917435 1917503 := bstep (se 1 (by rfl) ⟨1438127, by rfl⟩ : syracuseStep 1917503 = 2876255) B2876255
theorem B2876261 : Blo 1917435 2876261 := bbase (se 4 (by rfl) ⟨269649, by rfl⟩ : syracuseStep 2876261 = 539299) (by norm_num)
theorem B1917507 : Blo 1917435 1917507 := bstep (se 1 (by rfl) ⟨1438130, by rfl⟩ : syracuseStep 1917507 = 2876261) B2876261
theorem B3640277 : Blo 1917435 3640277 := bbase (se 7 (by rfl) ⟨42659, by rfl⟩ : syracuseStep 3640277 = 85319) (by norm_num)
theorem B2426851 : Blo 1917435 2426851 := bstep (se 1 (by rfl) ⟨1820138, by rfl⟩ : syracuseStep 2426851 = 3640277) B3640277
theorem B3235801 : Blo 1917435 3235801 := bstep (se 2 (by rfl) ⟨1213425, by rfl⟩ : syracuseStep 3235801 = 2426851) B2426851
theorem B4314401 : Blo 1917435 4314401 := bstep (se 2 (by rfl) ⟨1617900, by rfl⟩ : syracuseStep 4314401 = 3235801) B3235801
theorem B2876267 : Blo 1917435 2876267 := bstep (se 1 (by rfl) ⟨2157200, by rfl⟩ : syracuseStep 2876267 = 4314401) B4314401
theorem B1917511 : Blo 1917435 1917511 := bstep (se 1 (by rfl) ⟨1438133, by rfl⟩ : syracuseStep 1917511 = 2876267) B2876267
theorem B2157205 : Blo 1917435 2157205 := bbase (se 6 (by rfl) ⟨50559, by rfl⟩ : syracuseStep 2157205 = 101119) (by norm_num)
theorem B2876273 : Blo 1917435 2876273 := bstep (se 2 (by rfl) ⟨1078602, by rfl⟩ : syracuseStep 2876273 = 2157205) B2157205
theorem B1917515 : Blo 1917435 1917515 := bstep (se 1 (by rfl) ⟨1438136, by rfl⟩ : syracuseStep 1917515 = 2876273) B2876273
theorem B2426861 : Blo 1917435 2426861 := bbase (se 3 (by rfl) ⟨455036, by rfl⟩ : syracuseStep 2426861 = 910073) (by norm_num)
theorem B6471629 : Blo 1917435 6471629 := bstep (se 3 (by rfl) ⟨1213430, by rfl⟩ : syracuseStep 6471629 = 2426861) B2426861
theorem B4314419 : Blo 1917435 4314419 := bstep (se 1 (by rfl) ⟨3235814, by rfl⟩ : syracuseStep 4314419 = 6471629) B6471629
theorem B2876279 : Blo 1917435 2876279 := bstep (se 1 (by rfl) ⟨2157209, by rfl⟩ : syracuseStep 2876279 = 4314419) B4314419
theorem B1917519 : Blo 1917435 1917519 := bstep (se 1 (by rfl) ⟨1438139, by rfl⟩ : syracuseStep 1917519 = 2876279) B2876279
theorem B2876285 : Blo 1917435 2876285 := bbase (se 3 (by rfl) ⟨539303, by rfl⟩ : syracuseStep 2876285 = 1078607) (by norm_num)
theorem B1917523 : Blo 1917435 1917523 := bstep (se 1 (by rfl) ⟨1438142, by rfl⟩ : syracuseStep 1917523 = 2876285) B2876285
theorem B4314437 : Blo 1917435 4314437 := bbase (se 4 (by rfl) ⟨404478, by rfl⟩ : syracuseStep 4314437 = 808957) (by norm_num)
theorem B2876291 : Blo 1917435 2876291 := bstep (se 1 (by rfl) ⟨2157218, by rfl⟩ : syracuseStep 2876291 = 4314437) B4314437
theorem B1917527 : Blo 1917435 1917527 := bstep (se 1 (by rfl) ⟨1438145, by rfl⟩ : syracuseStep 1917527 = 2876291) B2876291
theorem B3887389 : Blo 1917435 3887389 := bbase (se 3 (by rfl) ⟨728885, by rfl⟩ : syracuseStep 3887389 = 1457771) (by norm_num)
theorem B5183185 : Blo 1917435 5183185 := bstep (se 2 (by rfl) ⟨1943694, by rfl⟩ : syracuseStep 5183185 = 3887389) B3887389
theorem B6910913 : Blo 1917435 6910913 := bstep (se 2 (by rfl) ⟨2591592, by rfl⟩ : syracuseStep 6910913 = 5183185) B5183185
theorem B4607275 : Blo 1917435 4607275 := bstep (se 1 (by rfl) ⟨3455456, by rfl⟩ : syracuseStep 4607275 = 6910913) B6910913
theorem B6143033 : Blo 1917435 6143033 := bstep (se 2 (by rfl) ⟨2303637, by rfl⟩ : syracuseStep 6143033 = 4607275) B4607275
theorem B4095355 : Blo 1917435 4095355 := bstep (se 1 (by rfl) ⟨3071516, by rfl⟩ : syracuseStep 4095355 = 6143033) B6143033
theorem B5460473 : Blo 1917435 5460473 := bstep (se 2 (by rfl) ⟨2047677, by rfl⟩ : syracuseStep 5460473 = 4095355) B4095355
theorem B3640315 : Blo 1917435 3640315 := bstep (se 1 (by rfl) ⟨2730236, by rfl⟩ : syracuseStep 3640315 = 5460473) B5460473
theorem B4853753 : Blo 1917435 4853753 := bstep (se 2 (by rfl) ⟨1820157, by rfl⟩ : syracuseStep 4853753 = 3640315) B3640315
theorem B3235835 : Blo 1917435 3235835 := bstep (se 1 (by rfl) ⟨2426876, by rfl⟩ : syracuseStep 3235835 = 4853753) B4853753
theorem B2157223 : Blo 1917435 2157223 := bstep (se 1 (by rfl) ⟨1617917, by rfl⟩ : syracuseStep 2157223 = 3235835) B3235835
theorem B2876297 : Blo 1917435 2876297 := bstep (se 2 (by rfl) ⟨1078611, by rfl⟩ : syracuseStep 2876297 = 2157223) B2157223
theorem B1917531 : Blo 1917435 1917531 := bstep (se 1 (by rfl) ⟨1438148, by rfl⟩ : syracuseStep 1917531 = 2876297) B2876297
theorem B9707525 : Blo 1917435 9707525 := bbase (se 4 (by rfl) ⟨910080, by rfl⟩ : syracuseStep 9707525 = 1820161) (by norm_num)
theorem B6471683 : Blo 1917435 6471683 := bstep (se 1 (by rfl) ⟨4853762, by rfl⟩ : syracuseStep 6471683 = 9707525) B9707525
theorem B4314455 : Blo 1917435 4314455 := bstep (se 1 (by rfl) ⟨3235841, by rfl⟩ : syracuseStep 4314455 = 6471683) B6471683
theorem B2876303 : Blo 1917435 2876303 := bstep (se 1 (by rfl) ⟨2157227, by rfl⟩ : syracuseStep 2876303 = 4314455) B4314455
theorem B1917535 : Blo 1917435 1917535 := bstep (se 1 (by rfl) ⟨1438151, by rfl⟩ : syracuseStep 1917535 = 2876303) B2876303
theorem B2876309 : Blo 1917435 2876309 := bbase (se 6 (by rfl) ⟨67413, by rfl⟩ : syracuseStep 2876309 = 134827) (by norm_num)
theorem B1917539 : Blo 1917435 1917539 := bstep (se 1 (by rfl) ⟨1438154, by rfl⟩ : syracuseStep 1917539 = 2876309) B2876309
theorem B10921013 : Blo 1917435 10921013 := bbase (se 5 (by rfl) ⟨511922, by rfl⟩ : syracuseStep 10921013 = 1023845) (by norm_num)
theorem B7280675 : Blo 1917435 7280675 := bstep (se 1 (by rfl) ⟨5460506, by rfl⟩ : syracuseStep 7280675 = 10921013) B10921013
theorem B4853783 : Blo 1917435 4853783 := bstep (se 1 (by rfl) ⟨3640337, by rfl⟩ : syracuseStep 4853783 = 7280675) B7280675
theorem B3235855 : Blo 1917435 3235855 := bstep (se 1 (by rfl) ⟨2426891, by rfl⟩ : syracuseStep 3235855 = 4853783) B4853783
theorem B4314473 : Blo 1917435 4314473 := bstep (se 2 (by rfl) ⟨1617927, by rfl⟩ : syracuseStep 4314473 = 3235855) B3235855
theorem B2876315 : Blo 1917435 2876315 := bstep (se 1 (by rfl) ⟨2157236, by rfl⟩ : syracuseStep 2876315 = 4314473) B4314473
theorem B1917543 : Blo 1917435 1917543 := bstep (se 1 (by rfl) ⟨1438157, by rfl⟩ : syracuseStep 1917543 = 2876315) B2876315
theorem B2157241 : Blo 1917435 2157241 := bbase (se 2 (by rfl) ⟨808965, by rfl⟩ : syracuseStep 2157241 = 1617931) (by norm_num)
theorem B2876321 : Blo 1917435 2876321 := bstep (se 2 (by rfl) ⟨1078620, by rfl⟩ : syracuseStep 2876321 = 2157241) B2157241
theorem B1917547 : Blo 1917435 1917547 := bstep (se 1 (by rfl) ⟨1438160, by rfl⟩ : syracuseStep 1917547 = 2876321) B2876321
theorem B4095397 : Blo 1917435 4095397 := bbase (se 4 (by rfl) ⟨383943, by rfl⟩ : syracuseStep 4095397 = 767887) (by norm_num)
theorem B5460529 : Blo 1917435 5460529 := bstep (se 2 (by rfl) ⟨2047698, by rfl⟩ : syracuseStep 5460529 = 4095397) B4095397
theorem B7280705 : Blo 1917435 7280705 := bstep (se 2 (by rfl) ⟨2730264, by rfl⟩ : syracuseStep 7280705 = 5460529) B5460529
theorem B4853803 : Blo 1917435 4853803 := bstep (se 1 (by rfl) ⟨3640352, by rfl⟩ : syracuseStep 4853803 = 7280705) B7280705
theorem B6471737 : Blo 1917435 6471737 := bstep (se 2 (by rfl) ⟨2426901, by rfl⟩ : syracuseStep 6471737 = 4853803) B4853803
theorem B4314491 : Blo 1917435 4314491 := bstep (se 1 (by rfl) ⟨3235868, by rfl⟩ : syracuseStep 4314491 = 6471737) B6471737
theorem B2876327 : Blo 1917435 2876327 := bstep (se 1 (by rfl) ⟨2157245, by rfl⟩ : syracuseStep 2876327 = 4314491) B4314491
theorem B1917551 : Blo 1917435 1917551 := bstep (se 1 (by rfl) ⟨1438163, by rfl⟩ : syracuseStep 1917551 = 2876327) B2876327
theorem B2876333 : Blo 1917435 2876333 := bbase (se 3 (by rfl) ⟨539312, by rfl⟩ : syracuseStep 2876333 = 1078625) (by norm_num)
theorem B1917555 : Blo 1917435 1917555 := bstep (se 1 (by rfl) ⟨1438166, by rfl⟩ : syracuseStep 1917555 = 2876333) B2876333
theorem B4314509 : Blo 1917435 4314509 := bbase (se 3 (by rfl) ⟨808970, by rfl⟩ : syracuseStep 4314509 = 1617941) (by norm_num)
theorem B2876339 : Blo 1917435 2876339 := bstep (se 1 (by rfl) ⟨2157254, by rfl⟩ : syracuseStep 2876339 = 4314509) B4314509
theorem B1917559 : Blo 1917435 1917559 := bstep (se 1 (by rfl) ⟨1438169, by rfl⟩ : syracuseStep 1917559 = 2876339) B2876339
theorem B2426917 : Blo 1917435 2426917 := bbase (se 4 (by rfl) ⟨227523, by rfl⟩ : syracuseStep 2426917 = 455047) (by norm_num)
theorem B3235889 : Blo 1917435 3235889 := bstep (se 2 (by rfl) ⟨1213458, by rfl⟩ : syracuseStep 3235889 = 2426917) B2426917
theorem B2157259 : Blo 1917435 2157259 := bstep (se 1 (by rfl) ⟨1617944, by rfl⟩ : syracuseStep 2157259 = 3235889) B3235889
theorem B2876345 : Blo 1917435 2876345 := bstep (se 2 (by rfl) ⟨1078629, by rfl⟩ : syracuseStep 2876345 = 2157259) B2157259
theorem B1917563 : Blo 1917435 1917563 := bstep (se 1 (by rfl) ⟨1438172, by rfl⟩ : syracuseStep 1917563 = 2876345) B2876345
theorem B1970249 : Blo 1917435 1970249 := bbase (se 2 (by rfl) ⟨738843, by rfl⟩ : syracuseStep 1970249 = 1477687) (by norm_num)
theorem B21015989 : Blo 1917435 21015989 := bstep (se 5 (by rfl) ⟨985124, by rfl⟩ : syracuseStep 21015989 = 1970249) B1970249
theorem B14010659 : Blo 1917435 14010659 := bstep (se 1 (by rfl) ⟨10507994, by rfl⟩ : syracuseStep 14010659 = 21015989) B21015989
theorem B9340439 : Blo 1917435 9340439 := bstep (se 1 (by rfl) ⟨7005329, by rfl⟩ : syracuseStep 9340439 = 14010659) B14010659
theorem B99631349 : Blo 1917435 99631349 := bstep (se 5 (by rfl) ⟨4670219, by rfl⟩ : syracuseStep 99631349 = 9340439) B9340439
theorem B66420899 : Blo 1917435 66420899 := bstep (se 1 (by rfl) ⟨49815674, by rfl⟩ : syracuseStep 66420899 = 99631349) B99631349
theorem B44280599 : Blo 1917435 44280599 := bstep (se 1 (by rfl) ⟨33210449, by rfl⟩ : syracuseStep 44280599 = 66420899) B66420899
theorem B472326389 : Blo 1917435 472326389 := bstep (se 5 (by rfl) ⟨22140299, by rfl⟩ : syracuseStep 472326389 = 44280599) B44280599
theorem B314884259 : Blo 1917435 314884259 := bstep (se 1 (by rfl) ⟨236163194, by rfl⟩ : syracuseStep 314884259 = 472326389) B472326389
theorem B209922839 : Blo 1917435 209922839 := bstep (se 1 (by rfl) ⟨157442129, by rfl⟩ : syracuseStep 209922839 = 314884259) B314884259
theorem B139948559 : Blo 1917435 139948559 := bstep (se 1 (by rfl) ⟨104961419, by rfl⟩ : syracuseStep 139948559 = 209922839) B209922839
theorem B93299039 : Blo 1917435 93299039 := bstep (se 1 (by rfl) ⟨69974279, by rfl⟩ : syracuseStep 93299039 = 139948559) B139948559
theorem B62199359 : Blo 1917435 62199359 := bstep (se 1 (by rfl) ⟨46649519, by rfl⟩ : syracuseStep 62199359 = 93299039) B93299039
theorem B41466239 : Blo 1917435 41466239 := bstep (se 1 (by rfl) ⟨31099679, by rfl⟩ : syracuseStep 41466239 = 62199359) B62199359
theorem B27644159 : Blo 1917435 27644159 := bstep (se 1 (by rfl) ⟨20733119, by rfl⟩ : syracuseStep 27644159 = 41466239) B41466239
theorem B18429439 : Blo 1917435 18429439 := bstep (se 1 (by rfl) ⟨13822079, by rfl⟩ : syracuseStep 18429439 = 27644159) B27644159
theorem B24572585 : Blo 1917435 24572585 := bstep (se 2 (by rfl) ⟨9214719, by rfl⟩ : syracuseStep 24572585 = 18429439) B18429439
theorem B16381723 : Blo 1917435 16381723 := bstep (se 1 (by rfl) ⟨12286292, by rfl⟩ : syracuseStep 16381723 = 24572585) B24572585
theorem B21842297 : Blo 1917435 21842297 := bstep (se 2 (by rfl) ⟨8190861, by rfl⟩ : syracuseStep 21842297 = 16381723) B16381723
theorem B14561531 : Blo 1917435 14561531 := bstep (se 1 (by rfl) ⟨10921148, by rfl⟩ : syracuseStep 14561531 = 21842297) B21842297
theorem B9707687 : Blo 1917435 9707687 := bstep (se 1 (by rfl) ⟨7280765, by rfl⟩ : syracuseStep 9707687 = 14561531) B14561531
theorem B6471791 : Blo 1917435 6471791 := bstep (se 1 (by rfl) ⟨4853843, by rfl⟩ : syracuseStep 6471791 = 9707687) B9707687
theorem B4314527 : Blo 1917435 4314527 := bstep (se 1 (by rfl) ⟨3235895, by rfl⟩ : syracuseStep 4314527 = 6471791) B6471791
theorem B2876351 : Blo 1917435 2876351 := bstep (se 1 (by rfl) ⟨2157263, by rfl⟩ : syracuseStep 2876351 = 4314527) B4314527
theorem B1917567 : Blo 1917435 1917567 := bstep (se 1 (by rfl) ⟨1438175, by rfl⟩ : syracuseStep 1917567 = 2876351) B2876351
theorem B2876357 : Blo 1917435 2876357 := bbase (se 4 (by rfl) ⟨269658, by rfl⟩ : syracuseStep 2876357 = 539317) (by norm_num)
theorem B1917571 : Blo 1917435 1917571 := bstep (se 1 (by rfl) ⟨1438178, by rfl⟩ : syracuseStep 1917571 = 2876357) B2876357
theorem B3235909 : Blo 1917435 3235909 := bbase (se 4 (by rfl) ⟨303366, by rfl⟩ : syracuseStep 3235909 = 606733) (by norm_num)
theorem B4314545 : Blo 1917435 4314545 := bstep (se 2 (by rfl) ⟨1617954, by rfl⟩ : syracuseStep 4314545 = 3235909) B3235909
theorem B2876363 : Blo 1917435 2876363 := bstep (se 1 (by rfl) ⟨2157272, by rfl⟩ : syracuseStep 2876363 = 4314545) B4314545
theorem B1917575 : Blo 1917435 1917575 := bstep (se 1 (by rfl) ⟨1438181, by rfl⟩ : syracuseStep 1917575 = 2876363) B2876363
theorem B2157277 : Blo 1917435 2157277 := bbase (se 3 (by rfl) ⟨404489, by rfl⟩ : syracuseStep 2157277 = 808979) (by norm_num)
theorem B2876369 : Blo 1917435 2876369 := bstep (se 2 (by rfl) ⟨1078638, by rfl⟩ : syracuseStep 2876369 = 2157277) B2157277
theorem B1917579 : Blo 1917435 1917579 := bstep (se 1 (by rfl) ⟨1438184, by rfl⟩ : syracuseStep 1917579 = 2876369) B2876369
theorem B6471845 : Blo 1917435 6471845 := bbase (se 4 (by rfl) ⟨606735, by rfl⟩ : syracuseStep 6471845 = 1213471) (by norm_num)
theorem B4314563 : Blo 1917435 4314563 := bstep (se 1 (by rfl) ⟨3235922, by rfl⟩ : syracuseStep 4314563 = 6471845) B6471845
theorem B2876375 : Blo 1917435 2876375 := bstep (se 1 (by rfl) ⟨2157281, by rfl⟩ : syracuseStep 2876375 = 4314563) B4314563
theorem B1917583 : Blo 1917435 1917583 := bstep (se 1 (by rfl) ⟨1438187, by rfl⟩ : syracuseStep 1917583 = 2876375) B2876375
theorem B2876381 : Blo 1917435 2876381 := bbase (se 3 (by rfl) ⟨539321, by rfl⟩ : syracuseStep 2876381 = 1078643) (by norm_num)
theorem B1917587 : Blo 1917435 1917587 := bstep (se 1 (by rfl) ⟨1438190, by rfl⟩ : syracuseStep 1917587 = 2876381) B2876381
theorem B4314581 : Blo 1917435 4314581 := bbase (se 7 (by rfl) ⟨50561, by rfl⟩ : syracuseStep 4314581 = 101123) (by norm_num)
theorem B2876387 : Blo 1917435 2876387 := bstep (se 1 (by rfl) ⟨2157290, by rfl⟩ : syracuseStep 2876387 = 4314581) B4314581
theorem B1917591 : Blo 1917435 1917591 := bstep (se 1 (by rfl) ⟨1438193, by rfl⟩ : syracuseStep 1917591 = 2876387) B2876387
theorem B4670293 : Blo 1917435 4670293 := bbase (se 9 (by rfl) ⟨13682, by rfl⟩ : syracuseStep 4670293 = 27365) (by norm_num)
theorem B6227057 : Blo 1917435 6227057 := bstep (se 2 (by rfl) ⟨2335146, by rfl⟩ : syracuseStep 6227057 = 4670293) B4670293
theorem B4151371 : Blo 1917435 4151371 := bstep (se 1 (by rfl) ⟨3113528, by rfl⟩ : syracuseStep 4151371 = 6227057) B6227057
theorem B5535161 : Blo 1917435 5535161 := bstep (se 2 (by rfl) ⟨2075685, by rfl⟩ : syracuseStep 5535161 = 4151371) B4151371
theorem B3690107 : Blo 1917435 3690107 := bstep (se 1 (by rfl) ⟨2767580, by rfl⟩ : syracuseStep 3690107 = 5535161) B5535161
theorem B2460071 : Blo 1917435 2460071 := bstep (se 1 (by rfl) ⟨1845053, by rfl⟩ : syracuseStep 2460071 = 3690107) B3690107
theorem B6560189 : Blo 1917435 6560189 := bstep (se 3 (by rfl) ⟨1230035, by rfl⟩ : syracuseStep 6560189 = 2460071) B2460071
theorem B4373459 : Blo 1917435 4373459 := bstep (se 1 (by rfl) ⟨3280094, by rfl⟩ : syracuseStep 4373459 = 6560189) B6560189
theorem B2915639 : Blo 1917435 2915639 := bstep (se 1 (by rfl) ⟨2186729, by rfl⟩ : syracuseStep 2915639 = 4373459) B4373459
theorem B1943759 : Blo 1917435 1943759 := bstep (se 1 (by rfl) ⟨1457819, by rfl⟩ : syracuseStep 1943759 = 2915639) B2915639
theorem B5183357 : Blo 1917435 5183357 := bstep (se 3 (by rfl) ⟨971879, by rfl⟩ : syracuseStep 5183357 = 1943759) B1943759
theorem B13822285 : Blo 1917435 13822285 := bstep (se 3 (by rfl) ⟨2591678, by rfl⟩ : syracuseStep 13822285 = 5183357) B5183357
theorem B18429713 : Blo 1917435 18429713 := bstep (se 2 (by rfl) ⟨6911142, by rfl⟩ : syracuseStep 18429713 = 13822285) B13822285
theorem B12286475 : Blo 1917435 12286475 := bstep (se 1 (by rfl) ⟨9214856, by rfl⟩ : syracuseStep 12286475 = 18429713) B18429713
theorem B8190983 : Blo 1917435 8190983 := bstep (se 1 (by rfl) ⟨6143237, by rfl⟩ : syracuseStep 8190983 = 12286475) B12286475
theorem B5460655 : Blo 1917435 5460655 := bstep (se 1 (by rfl) ⟨4095491, by rfl⟩ : syracuseStep 5460655 = 8190983) B8190983
theorem B7280873 : Blo 1917435 7280873 := bstep (se 2 (by rfl) ⟨2730327, by rfl⟩ : syracuseStep 7280873 = 5460655) B5460655
theorem B4853915 : Blo 1917435 4853915 := bstep (se 1 (by rfl) ⟨3640436, by rfl⟩ : syracuseStep 4853915 = 7280873) B7280873
theorem B3235943 : Blo 1917435 3235943 := bstep (se 1 (by rfl) ⟨2426957, by rfl⟩ : syracuseStep 3235943 = 4853915) B4853915
theorem B2157295 : Blo 1917435 2157295 := bstep (se 1 (by rfl) ⟨1617971, by rfl⟩ : syracuseStep 2157295 = 3235943) B3235943
theorem B2876393 : Blo 1917435 2876393 := bstep (se 2 (by rfl) ⟨1078647, by rfl⟩ : syracuseStep 2876393 = 2157295) B2157295
theorem B1917595 : Blo 1917435 1917595 := bstep (se 1 (by rfl) ⟨1438196, by rfl⟩ : syracuseStep 1917595 = 2876393) B2876393
theorem B4607437 : Blo 1917435 4607437 := bbase (se 3 (by rfl) ⟨863894, by rfl⟩ : syracuseStep 4607437 = 1727789) (by norm_num)
theorem B6143249 : Blo 1917435 6143249 := bstep (se 2 (by rfl) ⟨2303718, by rfl⟩ : syracuseStep 6143249 = 4607437) B4607437
theorem B16381997 : Blo 1917435 16381997 := bstep (se 3 (by rfl) ⟨3071624, by rfl⟩ : syracuseStep 16381997 = 6143249) B6143249
theorem B10921331 : Blo 1917435 10921331 := bstep (se 1 (by rfl) ⟨8190998, by rfl⟩ : syracuseStep 10921331 = 16381997) B16381997
theorem B7280887 : Blo 1917435 7280887 := bstep (se 1 (by rfl) ⟨5460665, by rfl⟩ : syracuseStep 7280887 = 10921331) B10921331
theorem B9707849 : Blo 1917435 9707849 := bstep (se 2 (by rfl) ⟨3640443, by rfl⟩ : syracuseStep 9707849 = 7280887) B7280887
theorem B6471899 : Blo 1917435 6471899 := bstep (se 1 (by rfl) ⟨4853924, by rfl⟩ : syracuseStep 6471899 = 9707849) B9707849
theorem B4314599 : Blo 1917435 4314599 := bstep (se 1 (by rfl) ⟨3235949, by rfl⟩ : syracuseStep 4314599 = 6471899) B6471899
theorem B2876399 : Blo 1917435 2876399 := bstep (se 1 (by rfl) ⟨2157299, by rfl⟩ : syracuseStep 2876399 = 4314599) B4314599
theorem B1917599 : Blo 1917435 1917599 := bstep (se 1 (by rfl) ⟨1438199, by rfl⟩ : syracuseStep 1917599 = 2876399) B2876399
theorem B2876405 : Blo 1917435 2876405 := bbase (se 5 (by rfl) ⟨134831, by rfl⟩ : syracuseStep 2876405 = 269663) (by norm_num)
theorem B1917603 : Blo 1917435 1917603 := bstep (se 1 (by rfl) ⟨1438202, by rfl⟩ : syracuseStep 1917603 = 2876405) B2876405
theorem B4095517 : Blo 1917435 4095517 := bbase (se 3 (by rfl) ⟨767909, by rfl⟩ : syracuseStep 4095517 = 1535819) (by norm_num)
theorem B5460689 : Blo 1917435 5460689 := bstep (se 2 (by rfl) ⟨2047758, by rfl⟩ : syracuseStep 5460689 = 4095517) B4095517
theorem B3640459 : Blo 1917435 3640459 := bstep (se 1 (by rfl) ⟨2730344, by rfl⟩ : syracuseStep 3640459 = 5460689) B5460689
theorem B4853945 : Blo 1917435 4853945 := bstep (se 2 (by rfl) ⟨1820229, by rfl⟩ : syracuseStep 4853945 = 3640459) B3640459
theorem B3235963 : Blo 1917435 3235963 := bstep (se 1 (by rfl) ⟨2426972, by rfl⟩ : syracuseStep 3235963 = 4853945) B4853945
theorem B4314617 : Blo 1917435 4314617 := bstep (se 2 (by rfl) ⟨1617981, by rfl⟩ : syracuseStep 4314617 = 3235963) B3235963
theorem B2876411 : Blo 1917435 2876411 := bstep (se 1 (by rfl) ⟨2157308, by rfl⟩ : syracuseStep 2876411 = 4314617) B4314617
theorem B1917607 : Blo 1917435 1917607 := bstep (se 1 (by rfl) ⟨1438205, by rfl⟩ : syracuseStep 1917607 = 2876411) B2876411
theorem B2157313 : Blo 1917435 2157313 := bbase (se 2 (by rfl) ⟨808992, by rfl⟩ : syracuseStep 2157313 = 1617985) (by norm_num)
theorem B2876417 : Blo 1917435 2876417 := bstep (se 2 (by rfl) ⟨1078656, by rfl⟩ : syracuseStep 2876417 = 2157313) B2157313
theorem B1917611 : Blo 1917435 1917611 := bstep (se 1 (by rfl) ⟨1438208, by rfl⟩ : syracuseStep 1917611 = 2876417) B2876417
theorem B4853965 : Blo 1917435 4853965 := bbase (se 3 (by rfl) ⟨910118, by rfl⟩ : syracuseStep 4853965 = 1820237) (by norm_num)
theorem B6471953 : Blo 1917435 6471953 := bstep (se 2 (by rfl) ⟨2426982, by rfl⟩ : syracuseStep 6471953 = 4853965) B4853965
theorem B4314635 : Blo 1917435 4314635 := bstep (se 1 (by rfl) ⟨3235976, by rfl⟩ : syracuseStep 4314635 = 6471953) B6471953
theorem B2876423 : Blo 1917435 2876423 := bstep (se 1 (by rfl) ⟨2157317, by rfl⟩ : syracuseStep 2876423 = 4314635) B4314635
theorem B1917615 : Blo 1917435 1917615 := bstep (se 1 (by rfl) ⟨1438211, by rfl⟩ : syracuseStep 1917615 = 2876423) B2876423
theorem B2876429 : Blo 1917435 2876429 := bbase (se 3 (by rfl) ⟨539330, by rfl⟩ : syracuseStep 2876429 = 1078661) (by norm_num)
theorem B1917619 : Blo 1917435 1917619 := bstep (se 1 (by rfl) ⟨1438214, by rfl⟩ : syracuseStep 1917619 = 2876429) B2876429
theorem B4314653 : Blo 1917435 4314653 := bbase (se 3 (by rfl) ⟨808997, by rfl⟩ : syracuseStep 4314653 = 1617995) (by norm_num)
theorem B2876435 : Blo 1917435 2876435 := bstep (se 1 (by rfl) ⟨2157326, by rfl⟩ : syracuseStep 2876435 = 4314653) B4314653
theorem B1917623 : Blo 1917435 1917623 := bstep (se 1 (by rfl) ⟨1438217, by rfl⟩ : syracuseStep 1917623 = 2876435) B2876435
theorem B3235997 : Blo 1917435 3235997 := bbase (se 3 (by rfl) ⟨606749, by rfl⟩ : syracuseStep 3235997 = 1213499) (by norm_num)
theorem B2157331 : Blo 1917435 2157331 := bstep (se 1 (by rfl) ⟨1617998, by rfl⟩ : syracuseStep 2157331 = 3235997) B3235997
theorem B2876441 : Blo 1917435 2876441 := bstep (se 2 (by rfl) ⟨1078665, by rfl⟩ : syracuseStep 2876441 = 2157331) B2157331
theorem B1917627 : Blo 1917435 1917627 := bstep (se 1 (by rfl) ⟨1438220, by rfl⟩ : syracuseStep 1917627 = 2876441) B2876441
theorem B59042773 : Blo 1917435 59042773 := bbase (se 7 (by rfl) ⟨691907, by rfl⟩ : syracuseStep 59042773 = 1383815) (by norm_num)
theorem B78723697 : Blo 1917435 78723697 := bstep (se 2 (by rfl) ⟨29521386, by rfl⟩ : syracuseStep 78723697 = 59042773) B59042773
theorem B104964929 : Blo 1917435 104964929 := bstep (se 2 (by rfl) ⟨39361848, by rfl⟩ : syracuseStep 104964929 = 78723697) B78723697
theorem B69976619 : Blo 1917435 69976619 := bstep (se 1 (by rfl) ⟨52482464, by rfl⟩ : syracuseStep 69976619 = 104964929) B104964929
theorem B46651079 : Blo 1917435 46651079 := bstep (se 1 (by rfl) ⟨34988309, by rfl⟩ : syracuseStep 46651079 = 69976619) B69976619
theorem B31100719 : Blo 1917435 31100719 := bstep (se 1 (by rfl) ⟨23325539, by rfl⟩ : syracuseStep 31100719 = 46651079) B46651079
theorem B41467625 : Blo 1917435 41467625 := bstep (se 2 (by rfl) ⟨15550359, by rfl⟩ : syracuseStep 41467625 = 31100719) B31100719
theorem B27645083 : Blo 1917435 27645083 := bstep (se 1 (by rfl) ⟨20733812, by rfl⟩ : syracuseStep 27645083 = 41467625) B41467625
theorem B18430055 : Blo 1917435 18430055 := bstep (se 1 (by rfl) ⟨13822541, by rfl⟩ : syracuseStep 18430055 = 27645083) B27645083
theorem B12286703 : Blo 1917435 12286703 := bstep (se 1 (by rfl) ⟨9215027, by rfl⟩ : syracuseStep 12286703 = 18430055) B18430055
theorem B8191135 : Blo 1917435 8191135 := bstep (se 1 (by rfl) ⟨6143351, by rfl⟩ : syracuseStep 8191135 = 12286703) B12286703
theorem B10921513 : Blo 1917435 10921513 := bstep (se 2 (by rfl) ⟨4095567, by rfl⟩ : syracuseStep 10921513 = 8191135) B8191135
theorem B14562017 : Blo 1917435 14562017 := bstep (se 2 (by rfl) ⟨5460756, by rfl⟩ : syracuseStep 14562017 = 10921513) B10921513
theorem B9708011 : Blo 1917435 9708011 := bstep (se 1 (by rfl) ⟨7281008, by rfl⟩ : syracuseStep 9708011 = 14562017) B14562017
theorem B6472007 : Blo 1917435 6472007 := bstep (se 1 (by rfl) ⟨4854005, by rfl⟩ : syracuseStep 6472007 = 9708011) B9708011
theorem B4314671 : Blo 1917435 4314671 := bstep (se 1 (by rfl) ⟨3236003, by rfl⟩ : syracuseStep 4314671 = 6472007) B6472007
theorem B2876447 : Blo 1917435 2876447 := bstep (se 1 (by rfl) ⟨2157335, by rfl⟩ : syracuseStep 2876447 = 4314671) B4314671
theorem B1917631 : Blo 1917435 1917631 := bstep (se 1 (by rfl) ⟨1438223, by rfl⟩ : syracuseStep 1917631 = 2876447) B2876447
theorem B2876453 : Blo 1917435 2876453 := bbase (se 4 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 2876453 = 539335) (by norm_num)
theorem B1917635 : Blo 1917435 1917635 := bstep (se 1 (by rfl) ⟨1438226, by rfl⟩ : syracuseStep 1917635 = 2876453) B2876453
theorem B2427013 : Blo 1917435 2427013 := bbase (se 4 (by rfl) ⟨227532, by rfl⟩ : syracuseStep 2427013 = 455065) (by norm_num)
theorem B3236017 : Blo 1917435 3236017 := bstep (se 2 (by rfl) ⟨1213506, by rfl⟩ : syracuseStep 3236017 = 2427013) B2427013
theorem B4314689 : Blo 1917435 4314689 := bstep (se 2 (by rfl) ⟨1618008, by rfl⟩ : syracuseStep 4314689 = 3236017) B3236017
theorem B2876459 : Blo 1917435 2876459 := bstep (se 1 (by rfl) ⟨2157344, by rfl⟩ : syracuseStep 2876459 = 4314689) B4314689
theorem B1917639 : Blo 1917435 1917639 := bstep (se 1 (by rfl) ⟨1438229, by rfl⟩ : syracuseStep 1917639 = 2876459) B2876459
theorem B2157349 : Blo 1917435 2157349 := bbase (se 4 (by rfl) ⟨202251, by rfl⟩ : syracuseStep 2157349 = 404503) (by norm_num)
theorem B2876465 : Blo 1917435 2876465 := bstep (se 2 (by rfl) ⟨1078674, by rfl⟩ : syracuseStep 2876465 = 2157349) B2157349
theorem B1917643 : Blo 1917435 1917643 := bstep (se 1 (by rfl) ⟨1438232, by rfl⟩ : syracuseStep 1917643 = 2876465) B2876465
theorem B8191205 : Blo 1917435 8191205 := bbase (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) (by norm_num)
theorem B5460803 : Blo 1917435 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B3640535 : Blo 1917435 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B2427023 : Blo 1917435 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B6472061 : Blo 1917435 6472061 := bstep (se 3 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 6472061 = 2427023) B2427023
theorem B4314707 : Blo 1917435 4314707 := bstep (se 1 (by rfl) ⟨3236030, by rfl⟩ : syracuseStep 4314707 = 6472061) B6472061
theorem B2876471 : Blo 1917435 2876471 := bstep (se 1 (by rfl) ⟨2157353, by rfl⟩ : syracuseStep 2876471 = 4314707) B4314707
theorem B1917647 : Blo 1917435 1917647 := bstep (se 1 (by rfl) ⟨1438235, by rfl⟩ : syracuseStep 1917647 = 2876471) B2876471
theorem B2876477 : Blo 1917435 2876477 := bbase (se 3 (by rfl) ⟨539339, by rfl⟩ : syracuseStep 2876477 = 1078679) (by norm_num)
theorem B1917651 : Blo 1917435 1917651 := bstep (se 1 (by rfl) ⟨1438238, by rfl⟩ : syracuseStep 1917651 = 2876477) B2876477
theorem B4314725 : Blo 1917435 4314725 := bbase (se 4 (by rfl) ⟨404505, by rfl⟩ : syracuseStep 4314725 = 809011) (by norm_num)
theorem B2876483 : Blo 1917435 2876483 := bstep (se 1 (by rfl) ⟨2157362, by rfl⟩ : syracuseStep 2876483 = 4314725) B4314725
theorem B1917655 : Blo 1917435 1917655 := bstep (se 1 (by rfl) ⟨1438241, by rfl⟩ : syracuseStep 1917655 = 2876483) B2876483
theorem B4854077 : Blo 1917435 4854077 := bbase (se 3 (by rfl) ⟨910139, by rfl⟩ : syracuseStep 4854077 = 1820279) (by norm_num)
theorem B3236051 : Blo 1917435 3236051 := bstep (se 1 (by rfl) ⟨2427038, by rfl⟩ : syracuseStep 3236051 = 4854077) B4854077
theorem B2157367 : Blo 1917435 2157367 := bstep (se 1 (by rfl) ⟨1618025, by rfl⟩ : syracuseStep 2157367 = 3236051) B3236051
theorem B2876489 : Blo 1917435 2876489 := bstep (se 2 (by rfl) ⟨1078683, by rfl⟩ : syracuseStep 2876489 = 2157367) B2157367
theorem B1917659 : Blo 1917435 1917659 := bstep (se 1 (by rfl) ⟨1438244, by rfl⟩ : syracuseStep 1917659 = 2876489) B2876489
theorem B3640565 : Blo 1917435 3640565 := bbase (se 5 (by rfl) ⟨170651, by rfl⟩ : syracuseStep 3640565 = 341303) (by norm_num)
theorem B9708173 : Blo 1917435 9708173 := bstep (se 3 (by rfl) ⟨1820282, by rfl⟩ : syracuseStep 9708173 = 3640565) B3640565
theorem B6472115 : Blo 1917435 6472115 := bstep (se 1 (by rfl) ⟨4854086, by rfl⟩ : syracuseStep 6472115 = 9708173) B9708173
theorem B4314743 : Blo 1917435 4314743 := bstep (se 1 (by rfl) ⟨3236057, by rfl⟩ : syracuseStep 4314743 = 6472115) B6472115
theorem B2876495 : Blo 1917435 2876495 := bstep (se 1 (by rfl) ⟨2157371, by rfl⟩ : syracuseStep 2876495 = 4314743) B4314743
theorem B1917663 : Blo 1917435 1917663 := bstep (se 1 (by rfl) ⟨1438247, by rfl⟩ : syracuseStep 1917663 = 2876495) B2876495
theorem B2876501 : Blo 1917435 2876501 := bbase (se 8 (by rfl) ⟨16854, by rfl⟩ : syracuseStep 2876501 = 33709) (by norm_num)
theorem B1917667 : Blo 1917435 1917667 := bstep (se 1 (by rfl) ⟨1438250, by rfl⟩ : syracuseStep 1917667 = 2876501) B2876501
theorem B9215221 : Blo 1917435 9215221 := bbase (se 5 (by rfl) ⟨431963, by rfl⟩ : syracuseStep 9215221 = 863927) (by norm_num)
theorem B12286961 : Blo 1917435 12286961 := bstep (se 2 (by rfl) ⟨4607610, by rfl⟩ : syracuseStep 12286961 = 9215221) B9215221
theorem B8191307 : Blo 1917435 8191307 := bstep (se 1 (by rfl) ⟨6143480, by rfl⟩ : syracuseStep 8191307 = 12286961) B12286961
theorem B5460871 : Blo 1917435 5460871 := bstep (se 1 (by rfl) ⟨4095653, by rfl⟩ : syracuseStep 5460871 = 8191307) B8191307
theorem B7281161 : Blo 1917435 7281161 := bstep (se 2 (by rfl) ⟨2730435, by rfl⟩ : syracuseStep 7281161 = 5460871) B5460871
theorem B4854107 : Blo 1917435 4854107 := bstep (se 1 (by rfl) ⟨3640580, by rfl⟩ : syracuseStep 4854107 = 7281161) B7281161
theorem B3236071 : Blo 1917435 3236071 := bstep (se 1 (by rfl) ⟨2427053, by rfl⟩ : syracuseStep 3236071 = 4854107) B4854107
theorem B4314761 : Blo 1917435 4314761 := bstep (se 2 (by rfl) ⟨1618035, by rfl⟩ : syracuseStep 4314761 = 3236071) B3236071
theorem B2876507 : Blo 1917435 2876507 := bstep (se 1 (by rfl) ⟨2157380, by rfl⟩ : syracuseStep 2876507 = 4314761) B4314761
theorem B1917671 : Blo 1917435 1917671 := bstep (se 1 (by rfl) ⟨1438253, by rfl⟩ : syracuseStep 1917671 = 2876507) B2876507
theorem B2157385 : Blo 1917435 2157385 := bbase (se 2 (by rfl) ⟨809019, by rfl⟩ : syracuseStep 2157385 = 1618039) (by norm_num)
theorem B2876513 : Blo 1917435 2876513 := bstep (se 2 (by rfl) ⟨1078692, by rfl⟩ : syracuseStep 2876513 = 2157385) B2157385
theorem B1917675 : Blo 1917435 1917675 := bstep (se 1 (by rfl) ⟨1438256, by rfl⟩ : syracuseStep 1917675 = 2876513) B2876513
theorem B18430517 : Blo 1917435 18430517 := bbase (se 5 (by rfl) ⟨863930, by rfl⟩ : syracuseStep 18430517 = 1727861) (by norm_num)
theorem B12287011 : Blo 1917435 12287011 := bstep (se 1 (by rfl) ⟨9215258, by rfl⟩ : syracuseStep 12287011 = 18430517) B18430517
theorem B16382681 : Blo 1917435 16382681 := bstep (se 2 (by rfl) ⟨6143505, by rfl⟩ : syracuseStep 16382681 = 12287011) B12287011
theorem B10921787 : Blo 1917435 10921787 := bstep (se 1 (by rfl) ⟨8191340, by rfl⟩ : syracuseStep 10921787 = 16382681) B16382681
theorem B7281191 : Blo 1917435 7281191 := bstep (se 1 (by rfl) ⟨5460893, by rfl⟩ : syracuseStep 7281191 = 10921787) B10921787
theorem B4854127 : Blo 1917435 4854127 := bstep (se 1 (by rfl) ⟨3640595, by rfl⟩ : syracuseStep 4854127 = 7281191) B7281191
theorem B6472169 : Blo 1917435 6472169 := bstep (se 2 (by rfl) ⟨2427063, by rfl⟩ : syracuseStep 6472169 = 4854127) B4854127
theorem B4314779 : Blo 1917435 4314779 := bstep (se 1 (by rfl) ⟨3236084, by rfl⟩ : syracuseStep 4314779 = 6472169) B6472169
theorem B2876519 : Blo 1917435 2876519 := bstep (se 1 (by rfl) ⟨2157389, by rfl⟩ : syracuseStep 2876519 = 4314779) B4314779
theorem B1917679 : Blo 1917435 1917679 := bstep (se 1 (by rfl) ⟨1438259, by rfl⟩ : syracuseStep 1917679 = 2876519) B2876519
theorem B2876525 : Blo 1917435 2876525 := bbase (se 3 (by rfl) ⟨539348, by rfl⟩ : syracuseStep 2876525 = 1078697) (by norm_num)
theorem B1917683 : Blo 1917435 1917683 := bstep (se 1 (by rfl) ⟨1438262, by rfl⟩ : syracuseStep 1917683 = 2876525) B2876525
theorem B4314797 : Blo 1917435 4314797 := bbase (se 3 (by rfl) ⟨809024, by rfl⟩ : syracuseStep 4314797 = 1618049) (by norm_num)
theorem B2876531 : Blo 1917435 2876531 := bstep (se 1 (by rfl) ⟨2157398, by rfl⟩ : syracuseStep 2876531 = 4314797) B4314797
theorem B1917687 : Blo 1917435 1917687 := bstep (se 1 (by rfl) ⟨1438265, by rfl⟩ : syracuseStep 1917687 = 2876531) B2876531
theorem B3071773 : Blo 1917435 3071773 := bbase (se 3 (by rfl) ⟨575957, by rfl⟩ : syracuseStep 3071773 = 1151915) (by norm_num)
theorem B4095697 : Blo 1917435 4095697 := bstep (se 2 (by rfl) ⟨1535886, by rfl⟩ : syracuseStep 4095697 = 3071773) B3071773
theorem B5460929 : Blo 1917435 5460929 := bstep (se 2 (by rfl) ⟨2047848, by rfl⟩ : syracuseStep 5460929 = 4095697) B4095697
theorem B3640619 : Blo 1917435 3640619 := bstep (se 1 (by rfl) ⟨2730464, by rfl⟩ : syracuseStep 3640619 = 5460929) B5460929
theorem B2427079 : Blo 1917435 2427079 := bstep (se 1 (by rfl) ⟨1820309, by rfl⟩ : syracuseStep 2427079 = 3640619) B3640619
theorem B3236105 : Blo 1917435 3236105 := bstep (se 2 (by rfl) ⟨1213539, by rfl⟩ : syracuseStep 3236105 = 2427079) B2427079
theorem B2157403 : Blo 1917435 2157403 := bstep (se 1 (by rfl) ⟨1618052, by rfl⟩ : syracuseStep 2157403 = 3236105) B3236105
theorem B2876537 : Blo 1917435 2876537 := bstep (se 2 (by rfl) ⟨1078701, by rfl⟩ : syracuseStep 2876537 = 2157403) B2157403
theorem B1917691 : Blo 1917435 1917691 := bstep (se 1 (by rfl) ⟨1438268, by rfl⟩ : syracuseStep 1917691 = 2876537) B2876537
theorem B2591813 : Blo 1917435 2591813 := bbase (se 4 (by rfl) ⟨242982, by rfl⟩ : syracuseStep 2591813 = 485965) (by norm_num)
theorem B6911501 : Blo 1917435 6911501 := bstep (se 3 (by rfl) ⟨1295906, by rfl⟩ : syracuseStep 6911501 = 2591813) B2591813
theorem B18430669 : Blo 1917435 18430669 := bstep (se 3 (by rfl) ⟨3455750, by rfl⟩ : syracuseStep 18430669 = 6911501) B6911501
theorem B24574225 : Blo 1917435 24574225 := bstep (se 2 (by rfl) ⟨9215334, by rfl⟩ : syracuseStep 24574225 = 18430669) B18430669
theorem B32765633 : Blo 1917435 32765633 := bstep (se 2 (by rfl) ⟨12287112, by rfl⟩ : syracuseStep 32765633 = 24574225) B24574225
theorem B21843755 : Blo 1917435 21843755 := bstep (se 1 (by rfl) ⟨16382816, by rfl⟩ : syracuseStep 21843755 = 32765633) B32765633
theorem B14562503 : Blo 1917435 14562503 := bstep (se 1 (by rfl) ⟨10921877, by rfl⟩ : syracuseStep 14562503 = 21843755) B21843755
theorem B9708335 : Blo 1917435 9708335 := bstep (se 1 (by rfl) ⟨7281251, by rfl⟩ : syracuseStep 9708335 = 14562503) B14562503
theorem B6472223 : Blo 1917435 6472223 := bstep (se 1 (by rfl) ⟨4854167, by rfl⟩ : syracuseStep 6472223 = 9708335) B9708335
theorem B4314815 : Blo 1917435 4314815 := bstep (se 1 (by rfl) ⟨3236111, by rfl⟩ : syracuseStep 4314815 = 6472223) B6472223
theorem B2876543 : Blo 1917435 2876543 := bstep (se 1 (by rfl) ⟨2157407, by rfl⟩ : syracuseStep 2876543 = 4314815) B4314815
theorem B1917695 : Blo 1917435 1917695 := bstep (se 1 (by rfl) ⟨1438271, by rfl⟩ : syracuseStep 1917695 = 2876543) B2876543
theorem B2876549 : Blo 1917435 2876549 := bbase (se 4 (by rfl) ⟨269676, by rfl⟩ : syracuseStep 2876549 = 539353) (by norm_num)
theorem B1917699 : Blo 1917435 1917699 := bstep (se 1 (by rfl) ⟨1438274, by rfl⟩ : syracuseStep 1917699 = 2876549) B2876549
theorem B3236125 : Blo 1917435 3236125 := bbase (se 3 (by rfl) ⟨606773, by rfl⟩ : syracuseStep 3236125 = 1213547) (by norm_num)
theorem B4314833 : Blo 1917435 4314833 := bstep (se 2 (by rfl) ⟨1618062, by rfl⟩ : syracuseStep 4314833 = 3236125) B3236125
theorem B2876555 : Blo 1917435 2876555 := bstep (se 1 (by rfl) ⟨2157416, by rfl⟩ : syracuseStep 2876555 = 4314833) B4314833
theorem B1917703 : Blo 1917435 1917703 := bstep (se 1 (by rfl) ⟨1438277, by rfl⟩ : syracuseStep 1917703 = 2876555) B2876555
theorem B2157421 : Blo 1917435 2157421 := bbase (se 3 (by rfl) ⟨404516, by rfl⟩ : syracuseStep 2157421 = 809033) (by norm_num)
theorem B2876561 : Blo 1917435 2876561 := bstep (se 2 (by rfl) ⟨1078710, by rfl⟩ : syracuseStep 2876561 = 2157421) B2157421
theorem B1917707 : Blo 1917435 1917707 := bstep (se 1 (by rfl) ⟨1438280, by rfl⟩ : syracuseStep 1917707 = 2876561) B2876561
theorem B6472277 : Blo 1917435 6472277 := bbase (se 8 (by rfl) ⟨37923, by rfl⟩ : syracuseStep 6472277 = 75847) (by norm_num)
theorem B4314851 : Blo 1917435 4314851 := bstep (se 1 (by rfl) ⟨3236138, by rfl⟩ : syracuseStep 4314851 = 6472277) B6472277
theorem B2876567 : Blo 1917435 2876567 := bstep (se 1 (by rfl) ⟨2157425, by rfl⟩ : syracuseStep 2876567 = 4314851) B4314851
theorem B1917711 : Blo 1917435 1917711 := bstep (se 1 (by rfl) ⟨1438283, by rfl⟩ : syracuseStep 1917711 = 2876567) B2876567
theorem B2876573 : Blo 1917435 2876573 := bbase (se 3 (by rfl) ⟨539357, by rfl⟩ : syracuseStep 2876573 = 1078715) (by norm_num)
theorem B1917715 : Blo 1917435 1917715 := bstep (se 1 (by rfl) ⟨1438286, by rfl⟩ : syracuseStep 1917715 = 2876573) B2876573
theorem B4314869 : Blo 1917435 4314869 := bbase (se 5 (by rfl) ⟨202259, by rfl⟩ : syracuseStep 4314869 = 404519) (by norm_num)
theorem B2876579 : Blo 1917435 2876579 := bstep (se 1 (by rfl) ⟨2157434, by rfl⟩ : syracuseStep 2876579 = 4314869) B4314869
theorem B1917719 : Blo 1917435 1917719 := bstep (se 1 (by rfl) ⟨1438289, by rfl⟩ : syracuseStep 1917719 = 2876579) B2876579
theorem B7198373 : Blo 1917435 7198373 := bbase (se 4 (by rfl) ⟨674847, by rfl⟩ : syracuseStep 7198373 = 1349695) (by norm_num)
theorem B19195661 : Blo 1917435 19195661 := bstep (se 3 (by rfl) ⟨3599186, by rfl⟩ : syracuseStep 19195661 = 7198373) B7198373
theorem B51188429 : Blo 1917435 51188429 := bstep (se 3 (by rfl) ⟨9597830, by rfl⟩ : syracuseStep 51188429 = 19195661) B19195661
theorem B34125619 : Blo 1917435 34125619 := bstep (se 1 (by rfl) ⟨25594214, by rfl⟩ : syracuseStep 34125619 = 51188429) B51188429
theorem B45500825 : Blo 1917435 45500825 := bstep (se 2 (by rfl) ⟨17062809, by rfl⟩ : syracuseStep 45500825 = 34125619) B34125619
theorem B121335533 : Blo 1917435 121335533 := bstep (se 3 (by rfl) ⟨22750412, by rfl⟩ : syracuseStep 121335533 = 45500825) B45500825
theorem B80890355 : Blo 1917435 80890355 := bstep (se 1 (by rfl) ⟨60667766, by rfl⟩ : syracuseStep 80890355 = 121335533) B121335533
theorem B53926903 : Blo 1917435 53926903 := bstep (se 1 (by rfl) ⟨40445177, by rfl⟩ : syracuseStep 53926903 = 80890355) B80890355
theorem B287610149 : Blo 1917435 287610149 := bstep (se 4 (by rfl) ⟨26963451, by rfl⟩ : syracuseStep 287610149 = 53926903) B53926903
theorem B766960397 : Blo 1917435 766960397 := bstep (se 3 (by rfl) ⟨143805074, by rfl⟩ : syracuseStep 766960397 = 287610149) B287610149
theorem B511306931 : Blo 1917435 511306931 := bstep (se 1 (by rfl) ⟨383480198, by rfl⟩ : syracuseStep 511306931 = 766960397) B766960397
theorem B340871287 : Blo 1917435 340871287 := bstep (se 1 (by rfl) ⟨255653465, by rfl⟩ : syracuseStep 340871287 = 511306931) B511306931
theorem B454495049 : Blo 1917435 454495049 := bstep (se 2 (by rfl) ⟨170435643, by rfl⟩ : syracuseStep 454495049 = 340871287) B340871287
theorem B302996699 : Blo 1917435 302996699 := bstep (se 1 (by rfl) ⟨227247524, by rfl⟩ : syracuseStep 302996699 = 454495049) B454495049
theorem B201997799 : Blo 1917435 201997799 := bstep (se 1 (by rfl) ⟨151498349, by rfl⟩ : syracuseStep 201997799 = 302996699) B302996699
theorem B134665199 : Blo 1917435 134665199 := bstep (se 1 (by rfl) ⟨100998899, by rfl⟩ : syracuseStep 134665199 = 201997799) B201997799
theorem B89776799 : Blo 1917435 89776799 := bstep (se 1 (by rfl) ⟨67332599, by rfl⟩ : syracuseStep 89776799 = 134665199) B134665199
theorem B59851199 : Blo 1917435 59851199 := bstep (se 1 (by rfl) ⟨44888399, by rfl⟩ : syracuseStep 59851199 = 89776799) B89776799
theorem B39900799 : Blo 1917435 39900799 := bstep (se 1 (by rfl) ⟨29925599, by rfl⟩ : syracuseStep 39900799 = 59851199) B59851199
theorem B53201065 : Blo 1917435 53201065 := bstep (se 2 (by rfl) ⟨19950399, by rfl⟩ : syracuseStep 53201065 = 39900799) B39900799
theorem B70934753 : Blo 1917435 70934753 := bstep (se 2 (by rfl) ⟨26600532, by rfl⟩ : syracuseStep 70934753 = 53201065) B53201065
theorem B47289835 : Blo 1917435 47289835 := bstep (se 1 (by rfl) ⟨35467376, by rfl⟩ : syracuseStep 47289835 = 70934753) B70934753
theorem B63053113 : Blo 1917435 63053113 := bstep (se 2 (by rfl) ⟨23644917, by rfl⟩ : syracuseStep 63053113 = 47289835) B47289835
theorem B84070817 : Blo 1917435 84070817 := bstep (se 2 (by rfl) ⟨31526556, by rfl⟩ : syracuseStep 84070817 = 63053113) B63053113
theorem B56047211 : Blo 1917435 56047211 := bstep (se 1 (by rfl) ⟨42035408, by rfl⟩ : syracuseStep 56047211 = 84070817) B84070817
theorem B37364807 : Blo 1917435 37364807 := bstep (se 1 (by rfl) ⟨28023605, by rfl⟩ : syracuseStep 37364807 = 56047211) B56047211
theorem B24909871 : Blo 1917435 24909871 := bstep (se 1 (by rfl) ⟨18682403, by rfl⟩ : syracuseStep 24909871 = 37364807) B37364807
theorem B33213161 : Blo 1917435 33213161 := bstep (se 2 (by rfl) ⟨12454935, by rfl⟩ : syracuseStep 33213161 = 24909871) B24909871
theorem B22142107 : Blo 1917435 22142107 := bstep (se 1 (by rfl) ⟨16606580, by rfl⟩ : syracuseStep 22142107 = 33213161) B33213161
theorem B29522809 : Blo 1917435 29522809 := bstep (se 2 (by rfl) ⟨11071053, by rfl⟩ : syracuseStep 29522809 = 22142107) B22142107
theorem B39363745 : Blo 1917435 39363745 := bstep (se 2 (by rfl) ⟨14761404, by rfl⟩ : syracuseStep 39363745 = 29522809) B29522809
theorem B52484993 : Blo 1917435 52484993 := bstep (se 2 (by rfl) ⟨19681872, by rfl⟩ : syracuseStep 52484993 = 39363745) B39363745
theorem B34989995 : Blo 1917435 34989995 := bstep (se 1 (by rfl) ⟨26242496, by rfl⟩ : syracuseStep 34989995 = 52484993) B52484993
theorem B23326663 : Blo 1917435 23326663 := bstep (se 1 (by rfl) ⟨17494997, by rfl⟩ : syracuseStep 23326663 = 34989995) B34989995
theorem B31102217 : Blo 1917435 31102217 := bstep (se 2 (by rfl) ⟨11663331, by rfl⟩ : syracuseStep 31102217 = 23326663) B23326663
theorem B20734811 : Blo 1917435 20734811 := bstep (se 1 (by rfl) ⟨15551108, by rfl⟩ : syracuseStep 20734811 = 31102217) B31102217
theorem B13823207 : Blo 1917435 13823207 := bstep (se 1 (by rfl) ⟨10367405, by rfl⟩ : syracuseStep 13823207 = 20734811) B20734811
theorem B9215471 : Blo 1917435 9215471 := bstep (se 1 (by rfl) ⟨6911603, by rfl⟩ : syracuseStep 9215471 = 13823207) B13823207
theorem B24574589 : Blo 1917435 24574589 := bstep (se 3 (by rfl) ⟨4607735, by rfl⟩ : syracuseStep 24574589 = 9215471) B9215471
theorem B16383059 : Blo 1917435 16383059 := bstep (se 1 (by rfl) ⟨12287294, by rfl⟩ : syracuseStep 16383059 = 24574589) B24574589
theorem B10922039 : Blo 1917435 10922039 := bstep (se 1 (by rfl) ⟨8191529, by rfl⟩ : syracuseStep 10922039 = 16383059) B16383059
theorem B7281359 : Blo 1917435 7281359 := bstep (se 1 (by rfl) ⟨5461019, by rfl⟩ : syracuseStep 7281359 = 10922039) B10922039
theorem B4854239 : Blo 1917435 4854239 := bstep (se 1 (by rfl) ⟨3640679, by rfl⟩ : syracuseStep 4854239 = 7281359) B7281359
theorem B3236159 : Blo 1917435 3236159 := bstep (se 1 (by rfl) ⟨2427119, by rfl⟩ : syracuseStep 3236159 = 4854239) B4854239
theorem B2157439 : Blo 1917435 2157439 := bstep (se 1 (by rfl) ⟨1618079, by rfl⟩ : syracuseStep 2157439 = 3236159) B3236159
theorem B2876585 : Blo 1917435 2876585 := bstep (se 2 (by rfl) ⟨1078719, by rfl⟩ : syracuseStep 2876585 = 2157439) B2157439
theorem B1917723 : Blo 1917435 1917723 := bstep (se 1 (by rfl) ⟨1438292, by rfl⟩ : syracuseStep 1917723 = 2876585) B2876585
theorem B4095773 : Blo 1917435 4095773 := bbase (se 3 (by rfl) ⟨767957, by rfl⟩ : syracuseStep 4095773 = 1535915) (by norm_num)
theorem B2730515 : Blo 1917435 2730515 := bstep (se 1 (by rfl) ⟨2047886, by rfl⟩ : syracuseStep 2730515 = 4095773) B4095773
theorem B7281373 : Blo 1917435 7281373 := bstep (se 3 (by rfl) ⟨1365257, by rfl⟩ : syracuseStep 7281373 = 2730515) B2730515
theorem B9708497 : Blo 1917435 9708497 := bstep (se 2 (by rfl) ⟨3640686, by rfl⟩ : syracuseStep 9708497 = 7281373) B7281373
theorem B6472331 : Blo 1917435 6472331 := bstep (se 1 (by rfl) ⟨4854248, by rfl⟩ : syracuseStep 6472331 = 9708497) B9708497
theorem B4314887 : Blo 1917435 4314887 := bstep (se 1 (by rfl) ⟨3236165, by rfl⟩ : syracuseStep 4314887 = 6472331) B6472331
theorem B2876591 : Blo 1917435 2876591 := bstep (se 1 (by rfl) ⟨2157443, by rfl⟩ : syracuseStep 2876591 = 4314887) B4314887
theorem B1917727 : Blo 1917435 1917727 := bstep (se 1 (by rfl) ⟨1438295, by rfl⟩ : syracuseStep 1917727 = 2876591) B2876591
theorem B2876597 : Blo 1917435 2876597 := bbase (se 5 (by rfl) ⟨134840, by rfl⟩ : syracuseStep 2876597 = 269681) (by norm_num)
theorem B1917731 : Blo 1917435 1917731 := bstep (se 1 (by rfl) ⟨1438298, by rfl⟩ : syracuseStep 1917731 = 2876597) B2876597
theorem B4854269 : Blo 1917435 4854269 := bbase (se 3 (by rfl) ⟨910175, by rfl⟩ : syracuseStep 4854269 = 1820351) (by norm_num)
theorem B3236179 : Blo 1917435 3236179 := bstep (se 1 (by rfl) ⟨2427134, by rfl⟩ : syracuseStep 3236179 = 4854269) B4854269
theorem B4314905 : Blo 1917435 4314905 := bstep (se 2 (by rfl) ⟨1618089, by rfl⟩ : syracuseStep 4314905 = 3236179) B3236179
theorem B2876603 : Blo 1917435 2876603 := bstep (se 1 (by rfl) ⟨2157452, by rfl⟩ : syracuseStep 2876603 = 4314905) B4314905
theorem B1917735 : Blo 1917435 1917735 := bstep (se 1 (by rfl) ⟨1438301, by rfl⟩ : syracuseStep 1917735 = 2876603) B2876603
theorem B2157457 : Blo 1917435 2157457 := bbase (se 2 (by rfl) ⟨809046, by rfl⟩ : syracuseStep 2157457 = 1618093) (by norm_num)
theorem B2876609 : Blo 1917435 2876609 := bstep (se 2 (by rfl) ⟨1078728, by rfl⟩ : syracuseStep 2876609 = 2157457) B2157457
theorem B1917739 : Blo 1917435 1917739 := bstep (se 1 (by rfl) ⟨1438304, by rfl⟩ : syracuseStep 1917739 = 2876609) B2876609
theorem B3640717 : Blo 1917435 3640717 := bbase (se 3 (by rfl) ⟨682634, by rfl⟩ : syracuseStep 3640717 = 1365269) (by norm_num)
theorem B4854289 : Blo 1917435 4854289 := bstep (se 2 (by rfl) ⟨1820358, by rfl⟩ : syracuseStep 4854289 = 3640717) B3640717
theorem B6472385 : Blo 1917435 6472385 := bstep (se 2 (by rfl) ⟨2427144, by rfl⟩ : syracuseStep 6472385 = 4854289) B4854289
theorem B4314923 : Blo 1917435 4314923 := bstep (se 1 (by rfl) ⟨3236192, by rfl⟩ : syracuseStep 4314923 = 6472385) B6472385
theorem B2876615 : Blo 1917435 2876615 := bstep (se 1 (by rfl) ⟨2157461, by rfl⟩ : syracuseStep 2876615 = 4314923) B4314923
theorem B1917743 : Blo 1917435 1917743 := bstep (se 1 (by rfl) ⟨1438307, by rfl⟩ : syracuseStep 1917743 = 2876615) B2876615
theorem B2876621 : Blo 1917435 2876621 := bbase (se 3 (by rfl) ⟨539366, by rfl⟩ : syracuseStep 2876621 = 1078733) (by norm_num)
theorem B1917747 : Blo 1917435 1917747 := bstep (se 1 (by rfl) ⟨1438310, by rfl⟩ : syracuseStep 1917747 = 2876621) B2876621
theorem B4314941 : Blo 1917435 4314941 := bbase (se 3 (by rfl) ⟨809051, by rfl⟩ : syracuseStep 4314941 = 1618103) (by norm_num)
theorem B2876627 : Blo 1917435 2876627 := bstep (se 1 (by rfl) ⟨2157470, by rfl⟩ : syracuseStep 2876627 = 4314941) B4314941
theorem B1917751 : Blo 1917435 1917751 := bstep (se 1 (by rfl) ⟨1438313, by rfl⟩ : syracuseStep 1917751 = 2876627) B2876627
theorem B3236213 : Blo 1917435 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B2157475 : Blo 1917435 2157475 := bstep (se 1 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 2157475 = 3236213) B3236213
theorem B2876633 : Blo 1917435 2876633 := bstep (se 2 (by rfl) ⟨1078737, by rfl⟩ : syracuseStep 2876633 = 2157475) B2157475
theorem B1917755 : Blo 1917435 1917755 := bstep (se 1 (by rfl) ⟨1438316, by rfl⟩ : syracuseStep 1917755 = 2876633) B2876633
theorem B4670693 : Blo 1917435 4670693 := bbase (se 4 (by rfl) ⟨437877, by rfl⟩ : syracuseStep 4670693 = 875755) (by norm_num)
theorem B3113795 : Blo 1917435 3113795 := bstep (se 1 (by rfl) ⟨2335346, by rfl⟩ : syracuseStep 3113795 = 4670693) B4670693
theorem B2075863 : Blo 1917435 2075863 := bstep (se 1 (by rfl) ⟨1556897, by rfl⟩ : syracuseStep 2075863 = 3113795) B3113795
theorem B2767817 : Blo 1917435 2767817 := bstep (se 2 (by rfl) ⟨1037931, by rfl⟩ : syracuseStep 2767817 = 2075863) B2075863
theorem B7380845 : Blo 1917435 7380845 := bstep (se 3 (by rfl) ⟨1383908, by rfl⟩ : syracuseStep 7380845 = 2767817) B2767817
theorem B4920563 : Blo 1917435 4920563 := bstep (se 1 (by rfl) ⟨3690422, by rfl⟩ : syracuseStep 4920563 = 7380845) B7380845
theorem B3280375 : Blo 1917435 3280375 := bstep (se 1 (by rfl) ⟨2460281, by rfl⟩ : syracuseStep 3280375 = 4920563) B4920563
theorem B4373833 : Blo 1917435 4373833 := bstep (se 2 (by rfl) ⟨1640187, by rfl⟩ : syracuseStep 4373833 = 3280375) B3280375
theorem B5831777 : Blo 1917435 5831777 := bstep (se 2 (by rfl) ⟨2186916, by rfl⟩ : syracuseStep 5831777 = 4373833) B4373833
theorem B3887851 : Blo 1917435 3887851 := bstep (se 1 (by rfl) ⟨2915888, by rfl⟩ : syracuseStep 3887851 = 5831777) B5831777
theorem B5183801 : Blo 1917435 5183801 := bstep (se 2 (by rfl) ⟨1943925, by rfl⟩ : syracuseStep 5183801 = 3887851) B3887851
theorem B3455867 : Blo 1917435 3455867 := bstep (se 1 (by rfl) ⟨2591900, by rfl⟩ : syracuseStep 3455867 = 5183801) B5183801
theorem B2303911 : Blo 1917435 2303911 := bstep (se 1 (by rfl) ⟨1727933, by rfl⟩ : syracuseStep 2303911 = 3455867) B3455867
theorem B3071881 : Blo 1917435 3071881 := bstep (se 2 (by rfl) ⟨1151955, by rfl⟩ : syracuseStep 3071881 = 2303911) B2303911
theorem B4095841 : Blo 1917435 4095841 := bstep (se 2 (by rfl) ⟨1535940, by rfl⟩ : syracuseStep 4095841 = 3071881) B3071881
theorem B5461121 : Blo 1917435 5461121 := bstep (se 2 (by rfl) ⟨2047920, by rfl⟩ : syracuseStep 5461121 = 4095841) B4095841
theorem B14562989 : Blo 1917435 14562989 := bstep (se 3 (by rfl) ⟨2730560, by rfl⟩ : syracuseStep 14562989 = 5461121) B5461121
theorem B9708659 : Blo 1917435 9708659 := bstep (se 1 (by rfl) ⟨7281494, by rfl⟩ : syracuseStep 9708659 = 14562989) B14562989
theorem B6472439 : Blo 1917435 6472439 := bstep (se 1 (by rfl) ⟨4854329, by rfl⟩ : syracuseStep 6472439 = 9708659) B9708659
theorem B4314959 : Blo 1917435 4314959 := bstep (se 1 (by rfl) ⟨3236219, by rfl⟩ : syracuseStep 4314959 = 6472439) B6472439
theorem B2876639 : Blo 1917435 2876639 := bstep (se 1 (by rfl) ⟨2157479, by rfl⟩ : syracuseStep 2876639 = 4314959) B4314959
theorem B1917759 : Blo 1917435 1917759 := bstep (se 1 (by rfl) ⟨1438319, by rfl⟩ : syracuseStep 1917759 = 2876639) B2876639
theorem B2876645 : Blo 1917435 2876645 := bbase (se 4 (by rfl) ⟨269685, by rfl⟩ : syracuseStep 2876645 = 539371) (by norm_num)
theorem B1917763 : Blo 1917435 1917763 := bstep (se 1 (by rfl) ⟨1438322, by rfl⟩ : syracuseStep 1917763 = 2876645) B2876645
theorem B2303921 : Blo 1917435 2303921 := bbase (se 2 (by rfl) ⟨863970, by rfl⟩ : syracuseStep 2303921 = 1727941) (by norm_num)
theorem B6143789 : Blo 1917435 6143789 := bstep (se 3 (by rfl) ⟨1151960, by rfl⟩ : syracuseStep 6143789 = 2303921) B2303921
theorem B4095859 : Blo 1917435 4095859 := bstep (se 1 (by rfl) ⟨3071894, by rfl⟩ : syracuseStep 4095859 = 6143789) B6143789
theorem B5461145 : Blo 1917435 5461145 := bstep (se 2 (by rfl) ⟨2047929, by rfl⟩ : syracuseStep 5461145 = 4095859) B4095859
theorem B3640763 : Blo 1917435 3640763 := bstep (se 1 (by rfl) ⟨2730572, by rfl⟩ : syracuseStep 3640763 = 5461145) B5461145
theorem B2427175 : Blo 1917435 2427175 := bstep (se 1 (by rfl) ⟨1820381, by rfl⟩ : syracuseStep 2427175 = 3640763) B3640763
theorem B3236233 : Blo 1917435 3236233 := bstep (se 2 (by rfl) ⟨1213587, by rfl⟩ : syracuseStep 3236233 = 2427175) B2427175
theorem B4314977 : Blo 1917435 4314977 := bstep (se 2 (by rfl) ⟨1618116, by rfl⟩ : syracuseStep 4314977 = 3236233) B3236233
theorem B2876651 : Blo 1917435 2876651 := bstep (se 1 (by rfl) ⟨2157488, by rfl⟩ : syracuseStep 2876651 = 4314977) B4314977
theorem B1917767 : Blo 1917435 1917767 := bstep (se 1 (by rfl) ⟨1438325, by rfl⟩ : syracuseStep 1917767 = 2876651) B2876651
theorem B2157493 : Blo 1917435 2157493 := bbase (se 5 (by rfl) ⟨101132, by rfl⟩ : syracuseStep 2157493 = 202265) (by norm_num)
theorem B2876657 : Blo 1917435 2876657 := bstep (se 2 (by rfl) ⟨1078746, by rfl⟩ : syracuseStep 2876657 = 2157493) B2157493
theorem B1917771 : Blo 1917435 1917771 := bstep (se 1 (by rfl) ⟨1438328, by rfl⟩ : syracuseStep 1917771 = 2876657) B2876657
theorem B2427185 : Blo 1917435 2427185 := bbase (se 2 (by rfl) ⟨910194, by rfl⟩ : syracuseStep 2427185 = 1820389) (by norm_num)
theorem B6472493 : Blo 1917435 6472493 := bstep (se 3 (by rfl) ⟨1213592, by rfl⟩ : syracuseStep 6472493 = 2427185) B2427185
theorem B4314995 : Blo 1917435 4314995 := bstep (se 1 (by rfl) ⟨3236246, by rfl⟩ : syracuseStep 4314995 = 6472493) B6472493
theorem B2876663 : Blo 1917435 2876663 := bstep (se 1 (by rfl) ⟨2157497, by rfl⟩ : syracuseStep 2876663 = 4314995) B4314995
theorem B1917775 : Blo 1917435 1917775 := bstep (se 1 (by rfl) ⟨1438331, by rfl⟩ : syracuseStep 1917775 = 2876663) B2876663
theorem B2876669 : Blo 1917435 2876669 := bbase (se 3 (by rfl) ⟨539375, by rfl⟩ : syracuseStep 2876669 = 1078751) (by norm_num)
theorem B1917779 : Blo 1917435 1917779 := bstep (se 1 (by rfl) ⟨1438334, by rfl⟩ : syracuseStep 1917779 = 2876669) B2876669
theorem B4315013 : Blo 1917435 4315013 := bbase (se 4 (by rfl) ⟨404532, by rfl⟩ : syracuseStep 4315013 = 809065) (by norm_num)
theorem B2876675 : Blo 1917435 2876675 := bstep (se 1 (by rfl) ⟨2157506, by rfl⟩ : syracuseStep 2876675 = 4315013) B4315013
theorem B1917783 : Blo 1917435 1917783 := bstep (se 1 (by rfl) ⟨1438337, by rfl⟩ : syracuseStep 1917783 = 2876675) B2876675
theorem B3887909 : Blo 1917435 3887909 := bbase (se 4 (by rfl) ⟨364491, by rfl⟩ : syracuseStep 3887909 = 728983) (by norm_num)
theorem B2591939 : Blo 1917435 2591939 := bstep (se 1 (by rfl) ⟨1943954, by rfl⟩ : syracuseStep 2591939 = 3887909) B3887909
theorem B6911837 : Blo 1917435 6911837 := bstep (se 3 (by rfl) ⟨1295969, by rfl⟩ : syracuseStep 6911837 = 2591939) B2591939
theorem B4607891 : Blo 1917435 4607891 := bstep (se 1 (by rfl) ⟨3455918, by rfl⟩ : syracuseStep 4607891 = 6911837) B6911837
theorem B3071927 : Blo 1917435 3071927 := bstep (se 1 (by rfl) ⟨2303945, by rfl⟩ : syracuseStep 3071927 = 4607891) B4607891
theorem B2047951 : Blo 1917435 2047951 := bstep (se 1 (by rfl) ⟨1535963, by rfl⟩ : syracuseStep 2047951 = 3071927) B3071927
theorem B2730601 : Blo 1917435 2730601 := bstep (se 2 (by rfl) ⟨1023975, by rfl⟩ : syracuseStep 2730601 = 2047951) B2047951
theorem B3640801 : Blo 1917435 3640801 := bstep (se 2 (by rfl) ⟨1365300, by rfl⟩ : syracuseStep 3640801 = 2730601) B2730601
theorem B4854401 : Blo 1917435 4854401 := bstep (se 2 (by rfl) ⟨1820400, by rfl⟩ : syracuseStep 4854401 = 3640801) B3640801
theorem B3236267 : Blo 1917435 3236267 := bstep (se 1 (by rfl) ⟨2427200, by rfl⟩ : syracuseStep 3236267 = 4854401) B4854401
theorem B2157511 : Blo 1917435 2157511 := bstep (se 1 (by rfl) ⟨1618133, by rfl⟩ : syracuseStep 2157511 = 3236267) B3236267
theorem B2876681 : Blo 1917435 2876681 := bstep (se 2 (by rfl) ⟨1078755, by rfl⟩ : syracuseStep 2876681 = 2157511) B2157511
theorem B1917787 : Blo 1917435 1917787 := bstep (se 1 (by rfl) ⟨1438340, by rfl⟩ : syracuseStep 1917787 = 2876681) B2876681
theorem B9708821 : Blo 1917435 9708821 := bbase (se 6 (by rfl) ⟨227550, by rfl⟩ : syracuseStep 9708821 = 455101) (by norm_num)
theorem B6472547 : Blo 1917435 6472547 := bstep (se 1 (by rfl) ⟨4854410, by rfl⟩ : syracuseStep 6472547 = 9708821) B9708821
theorem B4315031 : Blo 1917435 4315031 := bstep (se 1 (by rfl) ⟨3236273, by rfl⟩ : syracuseStep 4315031 = 6472547) B6472547
theorem B2876687 : Blo 1917435 2876687 := bstep (se 1 (by rfl) ⟨2157515, by rfl⟩ : syracuseStep 2876687 = 4315031) B4315031
theorem B1917791 : Blo 1917435 1917791 := bstep (se 1 (by rfl) ⟨1438343, by rfl⟩ : syracuseStep 1917791 = 2876687) B2876687
theorem B2876693 : Blo 1917435 2876693 := bbase (se 6 (by rfl) ⟨67422, by rfl⟩ : syracuseStep 2876693 = 134845) (by norm_num)
theorem B1917795 : Blo 1917435 1917795 := bstep (se 1 (by rfl) ⟨1438346, by rfl⟩ : syracuseStep 1917795 = 2876693) B2876693
theorem B2627317 : Blo 1917435 2627317 := bbase (se 5 (by rfl) ⟨123155, by rfl⟩ : syracuseStep 2627317 = 246311) (by norm_num)
theorem B14012357 : Blo 1917435 14012357 := bstep (se 4 (by rfl) ⟨1313658, by rfl⟩ : syracuseStep 14012357 = 2627317) B2627317
theorem B37366285 : Blo 1917435 37366285 := bstep (se 3 (by rfl) ⟨7006178, by rfl⟩ : syracuseStep 37366285 = 14012357) B14012357
theorem B49821713 : Blo 1917435 49821713 := bstep (se 2 (by rfl) ⟨18683142, by rfl⟩ : syracuseStep 49821713 = 37366285) B37366285
theorem B33214475 : Blo 1917435 33214475 := bstep (se 1 (by rfl) ⟨24910856, by rfl⟩ : syracuseStep 33214475 = 49821713) B49821713
theorem B22142983 : Blo 1917435 22142983 := bstep (se 1 (by rfl) ⟨16607237, by rfl⟩ : syracuseStep 22142983 = 33214475) B33214475
theorem B29523977 : Blo 1917435 29523977 := bstep (se 2 (by rfl) ⟨11071491, by rfl⟩ : syracuseStep 29523977 = 22142983) B22142983
theorem B19682651 : Blo 1917435 19682651 := bstep (se 1 (by rfl) ⟨14761988, by rfl⟩ : syracuseStep 19682651 = 29523977) B29523977
theorem B13121767 : Blo 1917435 13121767 := bstep (se 1 (by rfl) ⟨9841325, by rfl⟩ : syracuseStep 13121767 = 19682651) B19682651
theorem B17495689 : Blo 1917435 17495689 := bstep (se 2 (by rfl) ⟨6560883, by rfl⟩ : syracuseStep 17495689 = 13121767) B13121767
theorem B23327585 : Blo 1917435 23327585 := bstep (se 2 (by rfl) ⟨8747844, by rfl⟩ : syracuseStep 23327585 = 17495689) B17495689
theorem B15551723 : Blo 1917435 15551723 := bstep (se 1 (by rfl) ⟨11663792, by rfl⟩ : syracuseStep 15551723 = 23327585) B23327585
theorem B41471261 : Blo 1917435 41471261 := bstep (se 3 (by rfl) ⟨7775861, by rfl⟩ : syracuseStep 41471261 = 15551723) B15551723
theorem B27647507 : Blo 1917435 27647507 := bstep (se 1 (by rfl) ⟨20735630, by rfl⟩ : syracuseStep 27647507 = 41471261) B41471261
theorem B18431671 : Blo 1917435 18431671 := bstep (se 1 (by rfl) ⟨13823753, by rfl⟩ : syracuseStep 18431671 = 27647507) B27647507
theorem B24575561 : Blo 1917435 24575561 := bstep (se 2 (by rfl) ⟨9215835, by rfl⟩ : syracuseStep 24575561 = 18431671) B18431671
theorem B16383707 : Blo 1917435 16383707 := bstep (se 1 (by rfl) ⟨12287780, by rfl⟩ : syracuseStep 16383707 = 24575561) B24575561
theorem B10922471 : Blo 1917435 10922471 := bstep (se 1 (by rfl) ⟨8191853, by rfl⟩ : syracuseStep 10922471 = 16383707) B16383707
theorem B7281647 : Blo 1917435 7281647 := bstep (se 1 (by rfl) ⟨5461235, by rfl⟩ : syracuseStep 7281647 = 10922471) B10922471
theorem B4854431 : Blo 1917435 4854431 := bstep (se 1 (by rfl) ⟨3640823, by rfl⟩ : syracuseStep 4854431 = 7281647) B7281647
theorem B3236287 : Blo 1917435 3236287 := bstep (se 1 (by rfl) ⟨2427215, by rfl⟩ : syracuseStep 3236287 = 4854431) B4854431
theorem B4315049 : Blo 1917435 4315049 := bstep (se 2 (by rfl) ⟨1618143, by rfl⟩ : syracuseStep 4315049 = 3236287) B3236287
theorem B2876699 : Blo 1917435 2876699 := bstep (se 1 (by rfl) ⟨2157524, by rfl⟩ : syracuseStep 2876699 = 4315049) B4315049
theorem B1917799 : Blo 1917435 1917799 := bstep (se 1 (by rfl) ⟨1438349, by rfl⟩ : syracuseStep 1917799 = 2876699) B2876699
theorem B2157529 : Blo 1917435 2157529 := bbase (se 2 (by rfl) ⟨809073, by rfl⟩ : syracuseStep 2157529 = 1618147) (by norm_num)
theorem B2876705 : Blo 1917435 2876705 := bstep (se 2 (by rfl) ⟨1078764, by rfl⟩ : syracuseStep 2876705 = 2157529) B2157529
theorem B1917803 : Blo 1917435 1917803 := bstep (se 1 (by rfl) ⟨1438352, by rfl⟩ : syracuseStep 1917803 = 2876705) B2876705
theorem B2730629 : Blo 1917435 2730629 := bbase (se 4 (by rfl) ⟨255996, by rfl⟩ : syracuseStep 2730629 = 511993) (by norm_num)
theorem B7281677 : Blo 1917435 7281677 := bstep (se 3 (by rfl) ⟨1365314, by rfl⟩ : syracuseStep 7281677 = 2730629) B2730629
theorem B4854451 : Blo 1917435 4854451 := bstep (se 1 (by rfl) ⟨3640838, by rfl⟩ : syracuseStep 4854451 = 7281677) B7281677
theorem B6472601 : Blo 1917435 6472601 := bstep (se 2 (by rfl) ⟨2427225, by rfl⟩ : syracuseStep 6472601 = 4854451) B4854451
theorem B4315067 : Blo 1917435 4315067 := bstep (se 1 (by rfl) ⟨3236300, by rfl⟩ : syracuseStep 4315067 = 6472601) B6472601
theorem B2876711 : Blo 1917435 2876711 := bstep (se 1 (by rfl) ⟨2157533, by rfl⟩ : syracuseStep 2876711 = 4315067) B4315067
theorem B1917807 : Blo 1917435 1917807 := bstep (se 1 (by rfl) ⟨1438355, by rfl⟩ : syracuseStep 1917807 = 2876711) B2876711
theorem B2876717 : Blo 1917435 2876717 := bbase (se 3 (by rfl) ⟨539384, by rfl⟩ : syracuseStep 2876717 = 1078769) (by norm_num)
theorem B1917811 : Blo 1917435 1917811 := bstep (se 1 (by rfl) ⟨1438358, by rfl⟩ : syracuseStep 1917811 = 2876717) B2876717
theorem B4315085 : Blo 1917435 4315085 := bbase (se 3 (by rfl) ⟨809078, by rfl⟩ : syracuseStep 4315085 = 1618157) (by norm_num)
theorem B2876723 : Blo 1917435 2876723 := bstep (se 1 (by rfl) ⟨2157542, by rfl⟩ : syracuseStep 2876723 = 4315085) B4315085
theorem B1917815 : Blo 1917435 1917815 := bstep (se 1 (by rfl) ⟨1438361, by rfl⟩ : syracuseStep 1917815 = 2876723) B2876723
theorem B2427241 : Blo 1917435 2427241 := bbase (se 2 (by rfl) ⟨910215, by rfl⟩ : syracuseStep 2427241 = 1820431) (by norm_num)
theorem B3236321 : Blo 1917435 3236321 := bstep (se 2 (by rfl) ⟨1213620, by rfl⟩ : syracuseStep 3236321 = 2427241) B2427241
theorem B2157547 : Blo 1917435 2157547 := bstep (se 1 (by rfl) ⟨1618160, by rfl⟩ : syracuseStep 2157547 = 3236321) B3236321
theorem B2876729 : Blo 1917435 2876729 := bstep (se 2 (by rfl) ⟨1078773, by rfl⟩ : syracuseStep 2876729 = 2157547) B2157547
theorem B1917819 : Blo 1917435 1917819 := bstep (se 1 (by rfl) ⟨1438364, by rfl⟩ : syracuseStep 1917819 = 2876729) B2876729
theorem B4920725 : Blo 1917435 4920725 := bbase (se 6 (by rfl) ⟨115329, by rfl⟩ : syracuseStep 4920725 = 230659) (by norm_num)
theorem B3280483 : Blo 1917435 3280483 := bstep (se 1 (by rfl) ⟨2460362, by rfl⟩ : syracuseStep 3280483 = 4920725) B4920725
theorem B17495909 : Blo 1917435 17495909 := bstep (se 4 (by rfl) ⟨1640241, by rfl⟩ : syracuseStep 17495909 = 3280483) B3280483
theorem B11663939 : Blo 1917435 11663939 := bstep (se 1 (by rfl) ⟨8747954, by rfl⟩ : syracuseStep 11663939 = 17495909) B17495909
theorem B7775959 : Blo 1917435 7775959 := bstep (se 1 (by rfl) ⟨5831969, by rfl⟩ : syracuseStep 7775959 = 11663939) B11663939
theorem B10367945 : Blo 1917435 10367945 := bstep (se 2 (by rfl) ⟨3887979, by rfl⟩ : syracuseStep 10367945 = 7775959) B7775959
theorem B6911963 : Blo 1917435 6911963 := bstep (se 1 (by rfl) ⟨5183972, by rfl⟩ : syracuseStep 6911963 = 10367945) B10367945
theorem B4607975 : Blo 1917435 4607975 := bstep (se 1 (by rfl) ⟨3455981, by rfl⟩ : syracuseStep 4607975 = 6911963) B6911963
theorem B12287933 : Blo 1917435 12287933 := bstep (se 3 (by rfl) ⟨2303987, by rfl⟩ : syracuseStep 12287933 = 4607975) B4607975
theorem B8191955 : Blo 1917435 8191955 := bstep (se 1 (by rfl) ⟨6143966, by rfl⟩ : syracuseStep 8191955 = 12287933) B12287933
theorem B21845213 : Blo 1917435 21845213 := bstep (se 3 (by rfl) ⟨4095977, by rfl⟩ : syracuseStep 21845213 = 8191955) B8191955
theorem B14563475 : Blo 1917435 14563475 := bstep (se 1 (by rfl) ⟨10922606, by rfl⟩ : syracuseStep 14563475 = 21845213) B21845213
theorem B9708983 : Blo 1917435 9708983 := bstep (se 1 (by rfl) ⟨7281737, by rfl⟩ : syracuseStep 9708983 = 14563475) B14563475
theorem B6472655 : Blo 1917435 6472655 := bstep (se 1 (by rfl) ⟨4854491, by rfl⟩ : syracuseStep 6472655 = 9708983) B9708983
theorem B4315103 : Blo 1917435 4315103 := bstep (se 1 (by rfl) ⟨3236327, by rfl⟩ : syracuseStep 4315103 = 6472655) B6472655
theorem B2876735 : Blo 1917435 2876735 := bstep (se 1 (by rfl) ⟨2157551, by rfl⟩ : syracuseStep 2876735 = 4315103) B4315103
theorem B1917823 : Blo 1917435 1917823 := bstep (se 1 (by rfl) ⟨1438367, by rfl⟩ : syracuseStep 1917823 = 2876735) B2876735
theorem B2876741 : Blo 1917435 2876741 := bbase (se 4 (by rfl) ⟨269694, by rfl⟩ : syracuseStep 2876741 = 539389) (by norm_num)
theorem B1917827 : Blo 1917435 1917827 := bstep (se 1 (by rfl) ⟨1438370, by rfl⟩ : syracuseStep 1917827 = 2876741) B2876741
theorem B3236341 : Blo 1917435 3236341 := bbase (se 5 (by rfl) ⟨151703, by rfl⟩ : syracuseStep 3236341 = 303407) (by norm_num)
theorem B4315121 : Blo 1917435 4315121 := bstep (se 2 (by rfl) ⟨1618170, by rfl⟩ : syracuseStep 4315121 = 3236341) B3236341
theorem B2876747 : Blo 1917435 2876747 := bstep (se 1 (by rfl) ⟨2157560, by rfl⟩ : syracuseStep 2876747 = 4315121) B4315121
theorem B1917831 : Blo 1917435 1917831 := bstep (se 1 (by rfl) ⟨1438373, by rfl⟩ : syracuseStep 1917831 = 2876747) B2876747
theorem B2157565 : Blo 1917435 2157565 := bbase (se 3 (by rfl) ⟨404543, by rfl⟩ : syracuseStep 2157565 = 809087) (by norm_num)
theorem B2876753 : Blo 1917435 2876753 := bstep (se 2 (by rfl) ⟨1078782, by rfl⟩ : syracuseStep 2876753 = 2157565) B2157565
theorem B1917835 : Blo 1917435 1917835 := bstep (se 1 (by rfl) ⟨1438376, by rfl⟩ : syracuseStep 1917835 = 2876753) B2876753
theorem B6472709 : Blo 1917435 6472709 := bbase (se 4 (by rfl) ⟨606816, by rfl⟩ : syracuseStep 6472709 = 1213633) (by norm_num)
theorem B4315139 : Blo 1917435 4315139 := bstep (se 1 (by rfl) ⟨3236354, by rfl⟩ : syracuseStep 4315139 = 6472709) B6472709
theorem B2876759 : Blo 1917435 2876759 := bstep (se 1 (by rfl) ⟨2157569, by rfl⟩ : syracuseStep 2876759 = 4315139) B4315139
theorem B1917839 : Blo 1917435 1917839 := bstep (se 1 (by rfl) ⟨1438379, by rfl⟩ : syracuseStep 1917839 = 2876759) B2876759
theorem B2876765 : Blo 1917435 2876765 := bbase (se 3 (by rfl) ⟨539393, by rfl⟩ : syracuseStep 2876765 = 1078787) (by norm_num)
theorem B1917843 : Blo 1917435 1917843 := bstep (se 1 (by rfl) ⟨1438382, by rfl⟩ : syracuseStep 1917843 = 2876765) B2876765
theorem B4315157 : Blo 1917435 4315157 := bbase (se 6 (by rfl) ⟨101136, by rfl⟩ : syracuseStep 4315157 = 202273) (by norm_num)
theorem B2876771 : Blo 1917435 2876771 := bstep (se 1 (by rfl) ⟨2157578, by rfl⟩ : syracuseStep 2876771 = 4315157) B4315157
theorem B1917847 : Blo 1917435 1917847 := bstep (se 1 (by rfl) ⟨1438385, by rfl⟩ : syracuseStep 1917847 = 2876771) B2876771
theorem B7281845 : Blo 1917435 7281845 := bbase (se 5 (by rfl) ⟨341336, by rfl⟩ : syracuseStep 7281845 = 682673) (by norm_num)
theorem B4854563 : Blo 1917435 4854563 := bstep (se 1 (by rfl) ⟨3640922, by rfl⟩ : syracuseStep 4854563 = 7281845) B7281845
theorem B3236375 : Blo 1917435 3236375 := bstep (se 1 (by rfl) ⟨2427281, by rfl⟩ : syracuseStep 3236375 = 4854563) B4854563
theorem B2157583 : Blo 1917435 2157583 := bstep (se 1 (by rfl) ⟨1618187, by rfl⟩ : syracuseStep 2157583 = 3236375) B3236375
theorem B2876777 : Blo 1917435 2876777 := bstep (se 2 (by rfl) ⟨1078791, by rfl⟩ : syracuseStep 2876777 = 2157583) B2157583
theorem B1917851 : Blo 1917435 1917851 := bstep (se 1 (by rfl) ⟨1438388, by rfl⟩ : syracuseStep 1917851 = 2876777) B2876777
theorem B4608053 : Blo 1917435 4608053 := bbase (se 5 (by rfl) ⟨216002, by rfl⟩ : syracuseStep 4608053 = 432005) (by norm_num)
theorem B3072035 : Blo 1917435 3072035 := bstep (se 1 (by rfl) ⟨2304026, by rfl⟩ : syracuseStep 3072035 = 4608053) B4608053
theorem B2048023 : Blo 1917435 2048023 := bstep (se 1 (by rfl) ⟨1536017, by rfl⟩ : syracuseStep 2048023 = 3072035) B3072035
theorem B10922789 : Blo 1917435 10922789 := bstep (se 4 (by rfl) ⟨1024011, by rfl⟩ : syracuseStep 10922789 = 2048023) B2048023
theorem B7281859 : Blo 1917435 7281859 := bstep (se 1 (by rfl) ⟨5461394, by rfl⟩ : syracuseStep 7281859 = 10922789) B10922789
theorem B9709145 : Blo 1917435 9709145 := bstep (se 2 (by rfl) ⟨3640929, by rfl⟩ : syracuseStep 9709145 = 7281859) B7281859
theorem B6472763 : Blo 1917435 6472763 := bstep (se 1 (by rfl) ⟨4854572, by rfl⟩ : syracuseStep 6472763 = 9709145) B9709145
theorem B4315175 : Blo 1917435 4315175 := bstep (se 1 (by rfl) ⟨3236381, by rfl⟩ : syracuseStep 4315175 = 6472763) B6472763
theorem B2876783 : Blo 1917435 2876783 := bstep (se 1 (by rfl) ⟨2157587, by rfl⟩ : syracuseStep 2876783 = 4315175) B4315175
theorem B1917855 : Blo 1917435 1917855 := bstep (se 1 (by rfl) ⟨1438391, by rfl⟩ : syracuseStep 1917855 = 2876783) B2876783
theorem B2876789 : Blo 1917435 2876789 := bbase (se 5 (by rfl) ⟨134849, by rfl⟩ : syracuseStep 2876789 = 269699) (by norm_num)
theorem B1917859 : Blo 1917435 1917859 := bstep (se 1 (by rfl) ⟨1438394, by rfl⟩ : syracuseStep 1917859 = 2876789) B2876789
theorem B2730709 : Blo 1917435 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B3640945 : Blo 1917435 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B4854593 : Blo 1917435 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B3236395 : Blo 1917435 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B4315193 : Blo 1917435 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B2876795 : Blo 1917435 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B1917863 : Blo 1917435 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B2157601 : Blo 1917435 2157601 := bbase (se 2 (by rfl) ⟨809100, by rfl⟩ : syracuseStep 2157601 = 1618201) (by norm_num)
theorem B2876801 : Blo 1917435 2876801 := bstep (se 2 (by rfl) ⟨1078800, by rfl⟩ : syracuseStep 2876801 = 2157601) B2157601
theorem B1917867 : Blo 1917435 1917867 := bstep (se 1 (by rfl) ⟨1438400, by rfl⟩ : syracuseStep 1917867 = 2876801) B2876801
theorem B4854613 : Blo 1917435 4854613 := bbase (se 9 (by rfl) ⟨14222, by rfl⟩ : syracuseStep 4854613 = 28445) (by norm_num)
theorem B6472817 : Blo 1917435 6472817 := bstep (se 2 (by rfl) ⟨2427306, by rfl⟩ : syracuseStep 6472817 = 4854613) B4854613
theorem B4315211 : Blo 1917435 4315211 := bstep (se 1 (by rfl) ⟨3236408, by rfl⟩ : syracuseStep 4315211 = 6472817) B6472817
theorem B2876807 : Blo 1917435 2876807 := bstep (se 1 (by rfl) ⟨2157605, by rfl⟩ : syracuseStep 2876807 = 4315211) B4315211
theorem B1917871 : Blo 1917435 1917871 := bstep (se 1 (by rfl) ⟨1438403, by rfl⟩ : syracuseStep 1917871 = 2876807) B2876807
theorem B2876813 : Blo 1917435 2876813 := bbase (se 3 (by rfl) ⟨539402, by rfl⟩ : syracuseStep 2876813 = 1078805) (by norm_num)
theorem B1917875 : Blo 1917435 1917875 := bstep (se 1 (by rfl) ⟨1438406, by rfl⟩ : syracuseStep 1917875 = 2876813) B2876813
theorem B4315229 : Blo 1917435 4315229 := bbase (se 3 (by rfl) ⟨809105, by rfl⟩ : syracuseStep 4315229 = 1618211) (by norm_num)
theorem B2876819 : Blo 1917435 2876819 := bstep (se 1 (by rfl) ⟨2157614, by rfl⟩ : syracuseStep 2876819 = 4315229) B4315229
theorem B1917879 : Blo 1917435 1917879 := bstep (se 1 (by rfl) ⟨1438409, by rfl⟩ : syracuseStep 1917879 = 2876819) B2876819
theorem B3236429 : Blo 1917435 3236429 := bbase (se 3 (by rfl) ⟨606830, by rfl⟩ : syracuseStep 3236429 = 1213661) (by norm_num)
theorem B2157619 : Blo 1917435 2157619 := bstep (se 1 (by rfl) ⟨1618214, by rfl⟩ : syracuseStep 2157619 = 3236429) B3236429
theorem B2876825 : Blo 1917435 2876825 := bstep (se 2 (by rfl) ⟨1078809, by rfl⟩ : syracuseStep 2876825 = 2157619) B2157619
theorem B1917883 : Blo 1917435 1917883 := bstep (se 1 (by rfl) ⟨1438412, by rfl⟩ : syracuseStep 1917883 = 2876825) B2876825
theorem B3888109 : Blo 1917435 3888109 := bbase (se 3 (by rfl) ⟨729020, by rfl⟩ : syracuseStep 3888109 = 1458041) (by norm_num)
theorem B5184145 : Blo 1917435 5184145 := bstep (se 2 (by rfl) ⟨1944054, by rfl⟩ : syracuseStep 5184145 = 3888109) B3888109
theorem B27648773 : Blo 1917435 27648773 := bstep (se 4 (by rfl) ⟨2592072, by rfl⟩ : syracuseStep 27648773 = 5184145) B5184145
theorem B18432515 : Blo 1917435 18432515 := bstep (se 1 (by rfl) ⟨13824386, by rfl⟩ : syracuseStep 18432515 = 27648773) B27648773
theorem B12288343 : Blo 1917435 12288343 := bstep (se 1 (by rfl) ⟨9216257, by rfl⟩ : syracuseStep 12288343 = 18432515) B18432515
theorem B16384457 : Blo 1917435 16384457 := bstep (se 2 (by rfl) ⟨6144171, by rfl⟩ : syracuseStep 16384457 = 12288343) B12288343
theorem B10922971 : Blo 1917435 10922971 := bstep (se 1 (by rfl) ⟨8192228, by rfl⟩ : syracuseStep 10922971 = 16384457) B16384457
theorem B14563961 : Blo 1917435 14563961 := bstep (se 2 (by rfl) ⟨5461485, by rfl⟩ : syracuseStep 14563961 = 10922971) B10922971
theorem B9709307 : Blo 1917435 9709307 := bstep (se 1 (by rfl) ⟨7281980, by rfl⟩ : syracuseStep 9709307 = 14563961) B14563961
theorem B6472871 : Blo 1917435 6472871 := bstep (se 1 (by rfl) ⟨4854653, by rfl⟩ : syracuseStep 6472871 = 9709307) B9709307
theorem B4315247 : Blo 1917435 4315247 := bstep (se 1 (by rfl) ⟨3236435, by rfl⟩ : syracuseStep 4315247 = 6472871) B6472871
theorem B2876831 : Blo 1917435 2876831 := bstep (se 1 (by rfl) ⟨2157623, by rfl⟩ : syracuseStep 2876831 = 4315247) B4315247
theorem B1917887 : Blo 1917435 1917887 := bstep (se 1 (by rfl) ⟨1438415, by rfl⟩ : syracuseStep 1917887 = 2876831) B2876831
theorem B2876837 : Blo 1917435 2876837 := bbase (se 4 (by rfl) ⟨269703, by rfl⟩ : syracuseStep 2876837 = 539407) (by norm_num)
theorem B1917891 : Blo 1917435 1917891 := bstep (se 1 (by rfl) ⟨1438418, by rfl⟩ : syracuseStep 1917891 = 2876837) B2876837
theorem B2427337 : Blo 1917435 2427337 := bbase (se 2 (by rfl) ⟨910251, by rfl⟩ : syracuseStep 2427337 = 1820503) (by norm_num)
theorem B3236449 : Blo 1917435 3236449 := bstep (se 2 (by rfl) ⟨1213668, by rfl⟩ : syracuseStep 3236449 = 2427337) B2427337
theorem B4315265 : Blo 1917435 4315265 := bstep (se 2 (by rfl) ⟨1618224, by rfl⟩ : syracuseStep 4315265 = 3236449) B3236449
theorem B2876843 : Blo 1917435 2876843 := bstep (se 1 (by rfl) ⟨2157632, by rfl⟩ : syracuseStep 2876843 = 4315265) B4315265
theorem B1917895 : Blo 1917435 1917895 := bstep (se 1 (by rfl) ⟨1438421, by rfl⟩ : syracuseStep 1917895 = 2876843) B2876843
theorem B2157637 : Blo 1917435 2157637 := bbase (se 4 (by rfl) ⟨202278, by rfl⟩ : syracuseStep 2157637 = 404557) (by norm_num)
theorem B2876849 : Blo 1917435 2876849 := bstep (se 2 (by rfl) ⟨1078818, by rfl⟩ : syracuseStep 2876849 = 2157637) B2157637
theorem B1917899 : Blo 1917435 1917899 := bstep (se 1 (by rfl) ⟨1438424, by rfl⟩ : syracuseStep 1917899 = 2876849) B2876849
theorem B3641021 : Blo 1917435 3641021 := bbase (se 3 (by rfl) ⟨682691, by rfl⟩ : syracuseStep 3641021 = 1365383) (by norm_num)
theorem B2427347 : Blo 1917435 2427347 := bstep (se 1 (by rfl) ⟨1820510, by rfl⟩ : syracuseStep 2427347 = 3641021) B3641021
theorem B6472925 : Blo 1917435 6472925 := bstep (se 3 (by rfl) ⟨1213673, by rfl⟩ : syracuseStep 6472925 = 2427347) B2427347
theorem B4315283 : Blo 1917435 4315283 := bstep (se 1 (by rfl) ⟨3236462, by rfl⟩ : syracuseStep 4315283 = 6472925) B6472925
theorem B2876855 : Blo 1917435 2876855 := bstep (se 1 (by rfl) ⟨2157641, by rfl⟩ : syracuseStep 2876855 = 4315283) B4315283
theorem B1917903 : Blo 1917435 1917903 := bstep (se 1 (by rfl) ⟨1438427, by rfl⟩ : syracuseStep 1917903 = 2876855) B2876855
theorem B2876861 : Blo 1917435 2876861 := bbase (se 3 (by rfl) ⟨539411, by rfl⟩ : syracuseStep 2876861 = 1078823) (by norm_num)
theorem B1917907 : Blo 1917435 1917907 := bstep (se 1 (by rfl) ⟨1438430, by rfl⟩ : syracuseStep 1917907 = 2876861) B2876861
theorem B4315301 : Blo 1917435 4315301 := bbase (se 4 (by rfl) ⟨404559, by rfl⟩ : syracuseStep 4315301 = 809119) (by norm_num)
theorem B2876867 : Blo 1917435 2876867 := bstep (se 1 (by rfl) ⟨2157650, by rfl⟩ : syracuseStep 2876867 = 4315301) B4315301
theorem B1917911 : Blo 1917435 1917911 := bstep (se 1 (by rfl) ⟨1438433, by rfl⟩ : syracuseStep 1917911 = 2876867) B2876867
theorem B4854725 : Blo 1917435 4854725 := bbase (se 4 (by rfl) ⟨455130, by rfl⟩ : syracuseStep 4854725 = 910261) (by norm_num)
theorem B3236483 : Blo 1917435 3236483 := bstep (se 1 (by rfl) ⟨2427362, by rfl⟩ : syracuseStep 3236483 = 4854725) B4854725
theorem B2157655 : Blo 1917435 2157655 := bstep (se 1 (by rfl) ⟨1618241, by rfl⟩ : syracuseStep 2157655 = 3236483) B3236483
theorem B2876873 : Blo 1917435 2876873 := bstep (se 2 (by rfl) ⟨1078827, by rfl⟩ : syracuseStep 2876873 = 2157655) B2157655
theorem B1917915 : Blo 1917435 1917915 := bstep (se 1 (by rfl) ⟨1438436, by rfl⟩ : syracuseStep 1917915 = 2876873) B2876873
theorem B9976229 : Blo 1917435 9976229 := bbase (se 4 (by rfl) ⟨935271, by rfl⟩ : syracuseStep 9976229 = 1870543) (by norm_num)
theorem B6650819 : Blo 1917435 6650819 := bstep (se 1 (by rfl) ⟨4988114, by rfl⟩ : syracuseStep 6650819 = 9976229) B9976229
theorem B4433879 : Blo 1917435 4433879 := bstep (se 1 (by rfl) ⟨3325409, by rfl⟩ : syracuseStep 4433879 = 6650819) B6650819
theorem B2955919 : Blo 1917435 2955919 := bstep (se 1 (by rfl) ⟨2216939, by rfl⟩ : syracuseStep 2955919 = 4433879) B4433879
theorem B3941225 : Blo 1917435 3941225 := bstep (se 2 (by rfl) ⟨1477959, by rfl⟩ : syracuseStep 3941225 = 2955919) B2955919
theorem B2627483 : Blo 1917435 2627483 := bstep (se 1 (by rfl) ⟨1970612, by rfl⟩ : syracuseStep 2627483 = 3941225) B3941225
theorem B7006621 : Blo 1917435 7006621 := bstep (se 3 (by rfl) ⟨1313741, by rfl⟩ : syracuseStep 7006621 = 2627483) B2627483
theorem B9342161 : Blo 1917435 9342161 := bstep (se 2 (by rfl) ⟨3503310, by rfl⟩ : syracuseStep 9342161 = 7006621) B7006621
theorem B6228107 : Blo 1917435 6228107 := bstep (se 1 (by rfl) ⟨4671080, by rfl⟩ : syracuseStep 6228107 = 9342161) B9342161
theorem B4152071 : Blo 1917435 4152071 := bstep (se 1 (by rfl) ⟨3114053, by rfl⟩ : syracuseStep 4152071 = 6228107) B6228107
theorem B11072189 : Blo 1917435 11072189 := bstep (se 3 (by rfl) ⟨2076035, by rfl⟩ : syracuseStep 11072189 = 4152071) B4152071
theorem B7381459 : Blo 1917435 7381459 := bstep (se 1 (by rfl) ⟨5536094, by rfl⟩ : syracuseStep 7381459 = 11072189) B11072189
theorem B9841945 : Blo 1917435 9841945 := bstep (se 2 (by rfl) ⟨3690729, by rfl⟩ : syracuseStep 9841945 = 7381459) B7381459
theorem B13122593 : Blo 1917435 13122593 := bstep (se 2 (by rfl) ⟨4920972, by rfl⟩ : syracuseStep 13122593 = 9841945) B9841945
theorem B8748395 : Blo 1917435 8748395 := bstep (se 1 (by rfl) ⟨6561296, by rfl⟩ : syracuseStep 8748395 = 13122593) B13122593
theorem B5832263 : Blo 1917435 5832263 := bstep (se 1 (by rfl) ⟨4374197, by rfl⟩ : syracuseStep 5832263 = 8748395) B8748395
theorem B3888175 : Blo 1917435 3888175 := bstep (se 1 (by rfl) ⟨2916131, by rfl⟩ : syracuseStep 3888175 = 5832263) B5832263
theorem B5184233 : Blo 1917435 5184233 := bstep (se 2 (by rfl) ⟨1944087, by rfl⟩ : syracuseStep 5184233 = 3888175) B3888175
theorem B3456155 : Blo 1917435 3456155 := bstep (se 1 (by rfl) ⟨2592116, by rfl⟩ : syracuseStep 3456155 = 5184233) B5184233
theorem B9216413 : Blo 1917435 9216413 := bstep (se 3 (by rfl) ⟨1728077, by rfl⟩ : syracuseStep 9216413 = 3456155) B3456155
theorem B6144275 : Blo 1917435 6144275 := bstep (se 1 (by rfl) ⟨4608206, by rfl⟩ : syracuseStep 6144275 = 9216413) B9216413
theorem B4096183 : Blo 1917435 4096183 := bstep (se 1 (by rfl) ⟨3072137, by rfl⟩ : syracuseStep 4096183 = 6144275) B6144275
theorem B5461577 : Blo 1917435 5461577 := bstep (se 2 (by rfl) ⟨2048091, by rfl⟩ : syracuseStep 5461577 = 4096183) B4096183
theorem B3641051 : Blo 1917435 3641051 := bstep (se 1 (by rfl) ⟨2730788, by rfl⟩ : syracuseStep 3641051 = 5461577) B5461577
theorem B9709469 : Blo 1917435 9709469 := bstep (se 3 (by rfl) ⟨1820525, by rfl⟩ : syracuseStep 9709469 = 3641051) B3641051
theorem B6472979 : Blo 1917435 6472979 := bstep (se 1 (by rfl) ⟨4854734, by rfl⟩ : syracuseStep 6472979 = 9709469) B9709469
theorem B4315319 : Blo 1917435 4315319 := bstep (se 1 (by rfl) ⟨3236489, by rfl⟩ : syracuseStep 4315319 = 6472979) B6472979
theorem B2876879 : Blo 1917435 2876879 := bstep (se 1 (by rfl) ⟨2157659, by rfl⟩ : syracuseStep 2876879 = 4315319) B4315319
theorem B1917919 : Blo 1917435 1917919 := bstep (se 1 (by rfl) ⟨1438439, by rfl⟩ : syracuseStep 1917919 = 2876879) B2876879
theorem B2876885 : Blo 1917435 2876885 := bbase (se 7 (by rfl) ⟨33713, by rfl⟩ : syracuseStep 2876885 = 67427) (by norm_num)
theorem B1917923 : Blo 1917435 1917923 := bstep (se 1 (by rfl) ⟨1438442, by rfl⟩ : syracuseStep 1917923 = 2876885) B2876885
theorem B7282133 : Blo 1917435 7282133 := bbase (se 7 (by rfl) ⟨85337, by rfl⟩ : syracuseStep 7282133 = 170675) (by norm_num)
theorem B4854755 : Blo 1917435 4854755 := bstep (se 1 (by rfl) ⟨3641066, by rfl⟩ : syracuseStep 4854755 = 7282133) B7282133
theorem B3236503 : Blo 1917435 3236503 := bstep (se 1 (by rfl) ⟨2427377, by rfl⟩ : syracuseStep 3236503 = 4854755) B4854755
theorem B4315337 : Blo 1917435 4315337 := bstep (se 2 (by rfl) ⟨1618251, by rfl⟩ : syracuseStep 4315337 = 3236503) B3236503
theorem B2876891 : Blo 1917435 2876891 := bstep (se 1 (by rfl) ⟨2157668, by rfl⟩ : syracuseStep 2876891 = 4315337) B4315337
theorem B1917927 : Blo 1917435 1917927 := bstep (se 1 (by rfl) ⟨1438445, by rfl⟩ : syracuseStep 1917927 = 2876891) B2876891
theorem B2157673 : Blo 1917435 2157673 := bbase (se 2 (by rfl) ⟨809127, by rfl⟩ : syracuseStep 2157673 = 1618255) (by norm_num)
theorem B2876897 : Blo 1917435 2876897 := bstep (se 2 (by rfl) ⟨1078836, by rfl⟩ : syracuseStep 2876897 = 2157673) B2157673
theorem B1917931 : Blo 1917435 1917931 := bstep (se 1 (by rfl) ⟨1438448, by rfl⟩ : syracuseStep 1917931 = 2876897) B2876897
theorem B4608245 : Blo 1917435 4608245 := bbase (se 5 (by rfl) ⟨216011, by rfl⟩ : syracuseStep 4608245 = 432023) (by norm_num)
theorem B3072163 : Blo 1917435 3072163 := bstep (se 1 (by rfl) ⟨2304122, by rfl⟩ : syracuseStep 3072163 = 4608245) B4608245
theorem B4096217 : Blo 1917435 4096217 := bstep (se 2 (by rfl) ⟨1536081, by rfl⟩ : syracuseStep 4096217 = 3072163) B3072163
theorem B10923245 : Blo 1917435 10923245 := bstep (se 3 (by rfl) ⟨2048108, by rfl⟩ : syracuseStep 10923245 = 4096217) B4096217
theorem B7282163 : Blo 1917435 7282163 := bstep (se 1 (by rfl) ⟨5461622, by rfl⟩ : syracuseStep 7282163 = 10923245) B10923245
theorem B4854775 : Blo 1917435 4854775 := bstep (se 1 (by rfl) ⟨3641081, by rfl⟩ : syracuseStep 4854775 = 7282163) B7282163
theorem B6473033 : Blo 1917435 6473033 := bstep (se 2 (by rfl) ⟨2427387, by rfl⟩ : syracuseStep 6473033 = 4854775) B4854775
theorem B4315355 : Blo 1917435 4315355 := bstep (se 1 (by rfl) ⟨3236516, by rfl⟩ : syracuseStep 4315355 = 6473033) B6473033
theorem B2876903 : Blo 1917435 2876903 := bstep (se 1 (by rfl) ⟨2157677, by rfl⟩ : syracuseStep 2876903 = 4315355) B4315355
theorem B1917935 : Blo 1917435 1917935 := bstep (se 1 (by rfl) ⟨1438451, by rfl⟩ : syracuseStep 1917935 = 2876903) B2876903
theorem B2876909 : Blo 1917435 2876909 := bbase (se 3 (by rfl) ⟨539420, by rfl⟩ : syracuseStep 2876909 = 1078841) (by norm_num)
theorem B1917939 : Blo 1917435 1917939 := bstep (se 1 (by rfl) ⟨1438454, by rfl⟩ : syracuseStep 1917939 = 2876909) B2876909
theorem B4315373 : Blo 1917435 4315373 := bbase (se 3 (by rfl) ⟨809132, by rfl⟩ : syracuseStep 4315373 = 1618265) (by norm_num)
theorem B2876915 : Blo 1917435 2876915 := bstep (se 1 (by rfl) ⟨2157686, by rfl⟩ : syracuseStep 2876915 = 4315373) B4315373
theorem B1917943 : Blo 1917435 1917943 := bstep (se 1 (by rfl) ⟨1438457, by rfl⟩ : syracuseStep 1917943 = 2876915) B2876915
theorem B2730829 : Blo 1917435 2730829 := bbase (se 3 (by rfl) ⟨512030, by rfl⟩ : syracuseStep 2730829 = 1024061) (by norm_num)
theorem B3641105 : Blo 1917435 3641105 := bstep (se 2 (by rfl) ⟨1365414, by rfl⟩ : syracuseStep 3641105 = 2730829) B2730829
theorem B2427403 : Blo 1917435 2427403 := bstep (se 1 (by rfl) ⟨1820552, by rfl⟩ : syracuseStep 2427403 = 3641105) B3641105
theorem B3236537 : Blo 1917435 3236537 := bstep (se 2 (by rfl) ⟨1213701, by rfl⟩ : syracuseStep 3236537 = 2427403) B2427403
theorem B2157691 : Blo 1917435 2157691 := bstep (se 1 (by rfl) ⟨1618268, by rfl⟩ : syracuseStep 2157691 = 3236537) B3236537
theorem B2876921 : Blo 1917435 2876921 := bstep (se 2 (by rfl) ⟨1078845, by rfl⟩ : syracuseStep 2876921 = 2157691) B2157691
theorem B1917947 : Blo 1917435 1917947 := bstep (se 1 (by rfl) ⟨1438460, by rfl⟩ : syracuseStep 1917947 = 2876921) B2876921
theorem B13122805 : Blo 1917435 13122805 := bbase (se 5 (by rfl) ⟨615131, by rfl⟩ : syracuseStep 13122805 = 1230263) (by norm_num)
theorem B17497073 : Blo 1917435 17497073 := bstep (se 2 (by rfl) ⟨6561402, by rfl⟩ : syracuseStep 17497073 = 13122805) B13122805
theorem B46658861 : Blo 1917435 46658861 := bstep (se 3 (by rfl) ⟨8748536, by rfl⟩ : syracuseStep 46658861 = 17497073) B17497073
theorem B31105907 : Blo 1917435 31105907 := bstep (se 1 (by rfl) ⟨23329430, by rfl⟩ : syracuseStep 31105907 = 46658861) B46658861
theorem B20737271 : Blo 1917435 20737271 := bstep (se 1 (by rfl) ⟨15552953, by rfl⟩ : syracuseStep 20737271 = 31105907) B31105907
theorem B13824847 : Blo 1917435 13824847 := bstep (se 1 (by rfl) ⟨10368635, by rfl⟩ : syracuseStep 13824847 = 20737271) B20737271
theorem B73732517 : Blo 1917435 73732517 := bstep (se 4 (by rfl) ⟨6912423, by rfl⟩ : syracuseStep 73732517 = 13824847) B13824847
theorem B49155011 : Blo 1917435 49155011 := bstep (se 1 (by rfl) ⟨36866258, by rfl⟩ : syracuseStep 49155011 = 73732517) B73732517
theorem B32770007 : Blo 1917435 32770007 := bstep (se 1 (by rfl) ⟨24577505, by rfl⟩ : syracuseStep 32770007 = 49155011) B49155011
theorem B21846671 : Blo 1917435 21846671 := bstep (se 1 (by rfl) ⟨16385003, by rfl⟩ : syracuseStep 21846671 = 32770007) B32770007
theorem B14564447 : Blo 1917435 14564447 := bstep (se 1 (by rfl) ⟨10923335, by rfl⟩ : syracuseStep 14564447 = 21846671) B21846671
theorem B9709631 : Blo 1917435 9709631 := bstep (se 1 (by rfl) ⟨7282223, by rfl⟩ : syracuseStep 9709631 = 14564447) B14564447
theorem B6473087 : Blo 1917435 6473087 := bstep (se 1 (by rfl) ⟨4854815, by rfl⟩ : syracuseStep 6473087 = 9709631) B9709631
theorem B4315391 : Blo 1917435 4315391 := bstep (se 1 (by rfl) ⟨3236543, by rfl⟩ : syracuseStep 4315391 = 6473087) B6473087
theorem B2876927 : Blo 1917435 2876927 := bstep (se 1 (by rfl) ⟨2157695, by rfl⟩ : syracuseStep 2876927 = 4315391) B4315391
theorem B1917951 : Blo 1917435 1917951 := bstep (se 1 (by rfl) ⟨1438463, by rfl⟩ : syracuseStep 1917951 = 2876927) B2876927
theorem B2876933 : Blo 1917435 2876933 := bbase (se 4 (by rfl) ⟨269712, by rfl⟩ : syracuseStep 2876933 = 539425) (by norm_num)
theorem B1917955 : Blo 1917435 1917955 := bstep (se 1 (by rfl) ⟨1438466, by rfl⟩ : syracuseStep 1917955 = 2876933) B2876933
theorem B3236557 : Blo 1917435 3236557 := bbase (se 3 (by rfl) ⟨606854, by rfl⟩ : syracuseStep 3236557 = 1213709) (by norm_num)
theorem B4315409 : Blo 1917435 4315409 := bstep (se 2 (by rfl) ⟨1618278, by rfl⟩ : syracuseStep 4315409 = 3236557) B3236557
theorem B2876939 : Blo 1917435 2876939 := bstep (se 1 (by rfl) ⟨2157704, by rfl⟩ : syracuseStep 2876939 = 4315409) B4315409
theorem B1917959 : Blo 1917435 1917959 := bstep (se 1 (by rfl) ⟨1438469, by rfl⟩ : syracuseStep 1917959 = 2876939) B2876939
theorem B2157709 : Blo 1917435 2157709 := bbase (se 3 (by rfl) ⟨404570, by rfl⟩ : syracuseStep 2157709 = 809141) (by norm_num)
theorem B2876945 : Blo 1917435 2876945 := bstep (se 2 (by rfl) ⟨1078854, by rfl⟩ : syracuseStep 2876945 = 2157709) B2157709
theorem B1917963 : Blo 1917435 1917963 := bstep (se 1 (by rfl) ⟨1438472, by rfl⟩ : syracuseStep 1917963 = 2876945) B2876945
theorem B6473141 : Blo 1917435 6473141 := bbase (se 5 (by rfl) ⟨303428, by rfl⟩ : syracuseStep 6473141 = 606857) (by norm_num)
theorem B4315427 : Blo 1917435 4315427 := bstep (se 1 (by rfl) ⟨3236570, by rfl⟩ : syracuseStep 4315427 = 6473141) B6473141
theorem B2876951 : Blo 1917435 2876951 := bstep (se 1 (by rfl) ⟨2157713, by rfl⟩ : syracuseStep 2876951 = 4315427) B4315427
theorem B1917967 : Blo 1917435 1917967 := bstep (se 1 (by rfl) ⟨1438475, by rfl⟩ : syracuseStep 1917967 = 2876951) B2876951
theorem B2876957 : Blo 1917435 2876957 := bbase (se 3 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 2876957 = 1078859) (by norm_num)
theorem B1917971 : Blo 1917435 1917971 := bstep (se 1 (by rfl) ⟨1438478, by rfl⟩ : syracuseStep 1917971 = 2876957) B2876957
theorem B4315445 : Blo 1917435 4315445 := bbase (se 5 (by rfl) ⟨202286, by rfl⟩ : syracuseStep 4315445 = 404573) (by norm_num)
theorem B2876963 : Blo 1917435 2876963 := bstep (se 1 (by rfl) ⟨2157722, by rfl⟩ : syracuseStep 2876963 = 4315445) B4315445
theorem B1917975 : Blo 1917435 1917975 := bstep (se 1 (by rfl) ⟨1438481, by rfl⟩ : syracuseStep 1917975 = 2876963) B2876963
theorem B17497333 : Blo 1917435 17497333 := bbase (se 5 (by rfl) ⟨820187, by rfl⟩ : syracuseStep 17497333 = 1640375) (by norm_num)
theorem B23329777 : Blo 1917435 23329777 := bstep (se 2 (by rfl) ⟨8748666, by rfl⟩ : syracuseStep 23329777 = 17497333) B17497333
theorem B31106369 : Blo 1917435 31106369 := bstep (se 2 (by rfl) ⟨11664888, by rfl⟩ : syracuseStep 31106369 = 23329777) B23329777
theorem B20737579 : Blo 1917435 20737579 := bstep (se 1 (by rfl) ⟨15553184, by rfl⟩ : syracuseStep 20737579 = 31106369) B31106369
theorem B27650105 : Blo 1917435 27650105 := bstep (se 2 (by rfl) ⟨10368789, by rfl⟩ : syracuseStep 27650105 = 20737579) B20737579
theorem B18433403 : Blo 1917435 18433403 := bstep (se 1 (by rfl) ⟨13825052, by rfl⟩ : syracuseStep 18433403 = 27650105) B27650105
theorem B12288935 : Blo 1917435 12288935 := bstep (se 1 (by rfl) ⟨9216701, by rfl⟩ : syracuseStep 12288935 = 18433403) B18433403
theorem B8192623 : Blo 1917435 8192623 := bstep (se 1 (by rfl) ⟨6144467, by rfl⟩ : syracuseStep 8192623 = 12288935) B12288935
theorem B10923497 : Blo 1917435 10923497 := bstep (se 2 (by rfl) ⟨4096311, by rfl⟩ : syracuseStep 10923497 = 8192623) B8192623
theorem B7282331 : Blo 1917435 7282331 := bstep (se 1 (by rfl) ⟨5461748, by rfl⟩ : syracuseStep 7282331 = 10923497) B10923497
theorem B4854887 : Blo 1917435 4854887 := bstep (se 1 (by rfl) ⟨3641165, by rfl⟩ : syracuseStep 4854887 = 7282331) B7282331
theorem B3236591 : Blo 1917435 3236591 := bstep (se 1 (by rfl) ⟨2427443, by rfl⟩ : syracuseStep 3236591 = 4854887) B4854887
theorem B2157727 : Blo 1917435 2157727 := bstep (se 1 (by rfl) ⟨1618295, by rfl⟩ : syracuseStep 2157727 = 3236591) B3236591
theorem B2876969 : Blo 1917435 2876969 := bstep (se 2 (by rfl) ⟨1078863, by rfl⟩ : syracuseStep 2876969 = 2157727) B2157727
theorem B1917979 : Blo 1917435 1917979 := bstep (se 1 (by rfl) ⟨1438484, by rfl⟩ : syracuseStep 1917979 = 2876969) B2876969
theorem B4734965 : Blo 1917435 4734965 := bbase (se 5 (by rfl) ⟨221951, by rfl⟩ : syracuseStep 4734965 = 443903) (by norm_num)
theorem B3156643 : Blo 1917435 3156643 := bstep (se 1 (by rfl) ⟨2367482, by rfl⟩ : syracuseStep 3156643 = 4734965) B4734965
theorem B4208857 : Blo 1917435 4208857 := bstep (se 2 (by rfl) ⟨1578321, by rfl⟩ : syracuseStep 4208857 = 3156643) B3156643
theorem B22447237 : Blo 1917435 22447237 := bstep (se 4 (by rfl) ⟨2104428, by rfl⟩ : syracuseStep 22447237 = 4208857) B4208857
theorem B478874389 : Blo 1917435 478874389 := bstep (se 6 (by rfl) ⟨11223618, by rfl⟩ : syracuseStep 478874389 = 22447237) B22447237
theorem B638499185 : Blo 1917435 638499185 := bstep (se 2 (by rfl) ⟨239437194, by rfl⟩ : syracuseStep 638499185 = 478874389) B478874389
theorem B425666123 : Blo 1917435 425666123 := bstep (se 1 (by rfl) ⟨319249592, by rfl⟩ : syracuseStep 425666123 = 638499185) B638499185
theorem B283777415 : Blo 1917435 283777415 := bstep (se 1 (by rfl) ⟨212833061, by rfl⟩ : syracuseStep 283777415 = 425666123) B425666123
theorem B189184943 : Blo 1917435 189184943 := bstep (se 1 (by rfl) ⟨141888707, by rfl⟩ : syracuseStep 189184943 = 283777415) B283777415
theorem B504493181 : Blo 1917435 504493181 := bstep (se 3 (by rfl) ⟨94592471, by rfl⟩ : syracuseStep 504493181 = 189184943) B189184943
theorem B336328787 : Blo 1917435 336328787 := bstep (se 1 (by rfl) ⟨252246590, by rfl⟩ : syracuseStep 336328787 = 504493181) B504493181
theorem B224219191 : Blo 1917435 224219191 := bstep (se 1 (by rfl) ⟨168164393, by rfl⟩ : syracuseStep 224219191 = 336328787) B336328787
theorem B298958921 : Blo 1917435 298958921 := bstep (se 2 (by rfl) ⟨112109595, by rfl⟩ : syracuseStep 298958921 = 224219191) B224219191
theorem B199305947 : Blo 1917435 199305947 := bstep (se 1 (by rfl) ⟨149479460, by rfl⟩ : syracuseStep 199305947 = 298958921) B298958921
theorem B132870631 : Blo 1917435 132870631 := bstep (se 1 (by rfl) ⟨99652973, by rfl⟩ : syracuseStep 132870631 = 199305947) B199305947
theorem B177160841 : Blo 1917435 177160841 := bstep (se 2 (by rfl) ⟨66435315, by rfl⟩ : syracuseStep 177160841 = 132870631) B132870631
theorem B118107227 : Blo 1917435 118107227 := bstep (se 1 (by rfl) ⟨88580420, by rfl⟩ : syracuseStep 118107227 = 177160841) B177160841
theorem B78738151 : Blo 1917435 78738151 := bstep (se 1 (by rfl) ⟨59053613, by rfl⟩ : syracuseStep 78738151 = 118107227) B118107227
theorem B104984201 : Blo 1917435 104984201 := bstep (se 2 (by rfl) ⟨39369075, by rfl⟩ : syracuseStep 104984201 = 78738151) B78738151
theorem B69989467 : Blo 1917435 69989467 := bstep (se 1 (by rfl) ⟨52492100, by rfl⟩ : syracuseStep 69989467 = 104984201) B104984201
theorem B93319289 : Blo 1917435 93319289 := bstep (se 2 (by rfl) ⟨34994733, by rfl⟩ : syracuseStep 93319289 = 69989467) B69989467
theorem B62212859 : Blo 1917435 62212859 := bstep (se 1 (by rfl) ⟨46659644, by rfl⟩ : syracuseStep 62212859 = 93319289) B93319289
theorem B41475239 : Blo 1917435 41475239 := bstep (se 1 (by rfl) ⟨31106429, by rfl⟩ : syracuseStep 41475239 = 62212859) B62212859
theorem B27650159 : Blo 1917435 27650159 := bstep (se 1 (by rfl) ⟨20737619, by rfl⟩ : syracuseStep 27650159 = 41475239) B41475239
theorem B18433439 : Blo 1917435 18433439 := bstep (se 1 (by rfl) ⟨13825079, by rfl⟩ : syracuseStep 18433439 = 27650159) B27650159
theorem B12288959 : Blo 1917435 12288959 := bstep (se 1 (by rfl) ⟨9216719, by rfl⟩ : syracuseStep 12288959 = 18433439) B18433439
theorem B8192639 : Blo 1917435 8192639 := bstep (se 1 (by rfl) ⟨6144479, by rfl⟩ : syracuseStep 8192639 = 12288959) B12288959
theorem B5461759 : Blo 1917435 5461759 := bstep (se 1 (by rfl) ⟨4096319, by rfl⟩ : syracuseStep 5461759 = 8192639) B8192639
theorem B7282345 : Blo 1917435 7282345 := bstep (se 2 (by rfl) ⟨2730879, by rfl⟩ : syracuseStep 7282345 = 5461759) B5461759
theorem B9709793 : Blo 1917435 9709793 := bstep (se 2 (by rfl) ⟨3641172, by rfl⟩ : syracuseStep 9709793 = 7282345) B7282345
theorem B6473195 : Blo 1917435 6473195 := bstep (se 1 (by rfl) ⟨4854896, by rfl⟩ : syracuseStep 6473195 = 9709793) B9709793
theorem B4315463 : Blo 1917435 4315463 := bstep (se 1 (by rfl) ⟨3236597, by rfl⟩ : syracuseStep 4315463 = 6473195) B6473195
theorem B2876975 : Blo 1917435 2876975 := bstep (se 1 (by rfl) ⟨2157731, by rfl⟩ : syracuseStep 2876975 = 4315463) B4315463
theorem B1917983 : Blo 1917435 1917983 := bstep (se 1 (by rfl) ⟨1438487, by rfl⟩ : syracuseStep 1917983 = 2876975) B2876975
theorem B2876981 : Blo 1917435 2876981 := bbase (se 5 (by rfl) ⟨134858, by rfl⟩ : syracuseStep 2876981 = 269717) (by norm_num)
theorem B1917987 : Blo 1917435 1917987 := bstep (se 1 (by rfl) ⟨1438490, by rfl⟩ : syracuseStep 1917987 = 2876981) B2876981
theorem B4854917 : Blo 1917435 4854917 := bbase (se 4 (by rfl) ⟨455148, by rfl⟩ : syracuseStep 4854917 = 910297) (by norm_num)
theorem B3236611 : Blo 1917435 3236611 := bstep (se 1 (by rfl) ⟨2427458, by rfl⟩ : syracuseStep 3236611 = 4854917) B4854917
theorem B4315481 : Blo 1917435 4315481 := bstep (se 2 (by rfl) ⟨1618305, by rfl⟩ : syracuseStep 4315481 = 3236611) B3236611
theorem B2876987 : Blo 1917435 2876987 := bstep (se 1 (by rfl) ⟨2157740, by rfl⟩ : syracuseStep 2876987 = 4315481) B4315481
theorem B1917991 : Blo 1917435 1917991 := bstep (se 1 (by rfl) ⟨1438493, by rfl⟩ : syracuseStep 1917991 = 2876987) B2876987
theorem B2157745 : Blo 1917435 2157745 := bbase (se 2 (by rfl) ⟨809154, by rfl⟩ : syracuseStep 2157745 = 1618309) (by norm_num)
theorem B2876993 : Blo 1917435 2876993 := bstep (se 2 (by rfl) ⟨1078872, by rfl⟩ : syracuseStep 2876993 = 2157745) B2157745
theorem B1917995 : Blo 1917435 1917995 := bstep (se 1 (by rfl) ⟨1438496, by rfl⟩ : syracuseStep 1917995 = 2876993) B2876993
theorem B2048177 : Blo 1917435 2048177 := bbase (se 2 (by rfl) ⟨768066, by rfl⟩ : syracuseStep 2048177 = 1536133) (by norm_num)
theorem B5461805 : Blo 1917435 5461805 := bstep (se 3 (by rfl) ⟨1024088, by rfl⟩ : syracuseStep 5461805 = 2048177) B2048177
theorem B3641203 : Blo 1917435 3641203 := bstep (se 1 (by rfl) ⟨2730902, by rfl⟩ : syracuseStep 3641203 = 5461805) B5461805
theorem B4854937 : Blo 1917435 4854937 := bstep (se 2 (by rfl) ⟨1820601, by rfl⟩ : syracuseStep 4854937 = 3641203) B3641203
theorem B6473249 : Blo 1917435 6473249 := bstep (se 2 (by rfl) ⟨2427468, by rfl⟩ : syracuseStep 6473249 = 4854937) B4854937
theorem B4315499 : Blo 1917435 4315499 := bstep (se 1 (by rfl) ⟨3236624, by rfl⟩ : syracuseStep 4315499 = 6473249) B6473249
theorem B2876999 : Blo 1917435 2876999 := bstep (se 1 (by rfl) ⟨2157749, by rfl⟩ : syracuseStep 2876999 = 4315499) B4315499
theorem B1917999 : Blo 1917435 1917999 := bstep (se 1 (by rfl) ⟨1438499, by rfl⟩ : syracuseStep 1917999 = 2876999) B2876999
theorem B2877005 : Blo 1917435 2877005 := bbase (se 3 (by rfl) ⟨539438, by rfl⟩ : syracuseStep 2877005 = 1078877) (by norm_num)
theorem B1918003 : Blo 1917435 1918003 := bstep (se 1 (by rfl) ⟨1438502, by rfl⟩ : syracuseStep 1918003 = 2877005) B2877005
theorem B4315517 : Blo 1917435 4315517 := bbase (se 3 (by rfl) ⟨809159, by rfl⟩ : syracuseStep 4315517 = 1618319) (by norm_num)
theorem B2877011 : Blo 1917435 2877011 := bstep (se 1 (by rfl) ⟨2157758, by rfl⟩ : syracuseStep 2877011 = 4315517) B4315517
theorem B1918007 : Blo 1917435 1918007 := bstep (se 1 (by rfl) ⟨1438505, by rfl⟩ : syracuseStep 1918007 = 2877011) B2877011
theorem B3236645 : Blo 1917435 3236645 := bbase (se 4 (by rfl) ⟨303435, by rfl⟩ : syracuseStep 3236645 = 606871) (by norm_num)
theorem B2157763 : Blo 1917435 2157763 := bstep (se 1 (by rfl) ⟨1618322, by rfl⟩ : syracuseStep 2157763 = 3236645) B3236645
theorem B2877017 : Blo 1917435 2877017 := bstep (se 2 (by rfl) ⟨1078881, by rfl⟩ : syracuseStep 2877017 = 2157763) B2157763
theorem B1918011 : Blo 1917435 1918011 := bstep (se 1 (by rfl) ⟨1438508, by rfl⟩ : syracuseStep 1918011 = 2877017) B2877017
theorem B2730925 : Blo 1917435 2730925 := bbase (se 3 (by rfl) ⟨512048, by rfl⟩ : syracuseStep 2730925 = 1024097) (by norm_num)
theorem B14564933 : Blo 1917435 14564933 := bstep (se 4 (by rfl) ⟨1365462, by rfl⟩ : syracuseStep 14564933 = 2730925) B2730925
theorem B9709955 : Blo 1917435 9709955 := bstep (se 1 (by rfl) ⟨7282466, by rfl⟩ : syracuseStep 9709955 = 14564933) B14564933
theorem B6473303 : Blo 1917435 6473303 := bstep (se 1 (by rfl) ⟨4854977, by rfl⟩ : syracuseStep 6473303 = 9709955) B9709955
theorem B4315535 : Blo 1917435 4315535 := bstep (se 1 (by rfl) ⟨3236651, by rfl⟩ : syracuseStep 4315535 = 6473303) B6473303
theorem B2877023 : Blo 1917435 2877023 := bstep (se 1 (by rfl) ⟨2157767, by rfl⟩ : syracuseStep 2877023 = 4315535) B4315535
theorem B1918015 : Blo 1917435 1918015 := bstep (se 1 (by rfl) ⟨1438511, by rfl⟩ : syracuseStep 1918015 = 2877023) B2877023
theorem B2877029 : Blo 1917435 2877029 := bbase (se 4 (by rfl) ⟨269721, by rfl⟩ : syracuseStep 2877029 = 539443) (by norm_num)
theorem B1918019 : Blo 1917435 1918019 := bstep (se 1 (by rfl) ⟨1438514, by rfl⟩ : syracuseStep 1918019 = 2877029) B2877029
theorem B2304229 : Blo 1917435 2304229 := bbase (se 4 (by rfl) ⟨216021, by rfl⟩ : syracuseStep 2304229 = 432043) (by norm_num)
theorem B3072305 : Blo 1917435 3072305 := bstep (se 2 (by rfl) ⟨1152114, by rfl⟩ : syracuseStep 3072305 = 2304229) B2304229
theorem B2048203 : Blo 1917435 2048203 := bstep (se 1 (by rfl) ⟨1536152, by rfl⟩ : syracuseStep 2048203 = 3072305) B3072305
theorem B2730937 : Blo 1917435 2730937 := bstep (se 2 (by rfl) ⟨1024101, by rfl⟩ : syracuseStep 2730937 = 2048203) B2048203
theorem B3641249 : Blo 1917435 3641249 := bstep (se 2 (by rfl) ⟨1365468, by rfl⟩ : syracuseStep 3641249 = 2730937) B2730937
theorem B2427499 : Blo 1917435 2427499 := bstep (se 1 (by rfl) ⟨1820624, by rfl⟩ : syracuseStep 2427499 = 3641249) B3641249
theorem B3236665 : Blo 1917435 3236665 := bstep (se 2 (by rfl) ⟨1213749, by rfl⟩ : syracuseStep 3236665 = 2427499) B2427499
theorem B4315553 : Blo 1917435 4315553 := bstep (se 2 (by rfl) ⟨1618332, by rfl⟩ : syracuseStep 4315553 = 3236665) B3236665
theorem B2877035 : Blo 1917435 2877035 := bstep (se 1 (by rfl) ⟨2157776, by rfl⟩ : syracuseStep 2877035 = 4315553) B4315553
theorem B1918023 : Blo 1917435 1918023 := bstep (se 1 (by rfl) ⟨1438517, by rfl⟩ : syracuseStep 1918023 = 2877035) B2877035
theorem B2157781 : Blo 1917435 2157781 := bbase (se 7 (by rfl) ⟨25286, by rfl⟩ : syracuseStep 2157781 = 50573) (by norm_num)
theorem B2877041 : Blo 1917435 2877041 := bstep (se 2 (by rfl) ⟨1078890, by rfl⟩ : syracuseStep 2877041 = 2157781) B2157781
theorem B1918027 : Blo 1917435 1918027 := bstep (se 1 (by rfl) ⟨1438520, by rfl⟩ : syracuseStep 1918027 = 2877041) B2877041
theorem B2427509 : Blo 1917435 2427509 := bbase (se 5 (by rfl) ⟨113789, by rfl⟩ : syracuseStep 2427509 = 227579) (by norm_num)
theorem B6473357 : Blo 1917435 6473357 := bstep (se 3 (by rfl) ⟨1213754, by rfl⟩ : syracuseStep 6473357 = 2427509) B2427509
theorem B4315571 : Blo 1917435 4315571 := bstep (se 1 (by rfl) ⟨3236678, by rfl⟩ : syracuseStep 4315571 = 6473357) B6473357
theorem B2877047 : Blo 1917435 2877047 := bstep (se 1 (by rfl) ⟨2157785, by rfl⟩ : syracuseStep 2877047 = 4315571) B4315571
theorem B1918031 : Blo 1917435 1918031 := bstep (se 1 (by rfl) ⟨1438523, by rfl⟩ : syracuseStep 1918031 = 2877047) B2877047
theorem B2877053 : Blo 1917435 2877053 := bbase (se 3 (by rfl) ⟨539447, by rfl⟩ : syracuseStep 2877053 = 1078895) (by norm_num)
theorem B1918035 : Blo 1917435 1918035 := bstep (se 1 (by rfl) ⟨1438526, by rfl⟩ : syracuseStep 1918035 = 2877053) B2877053
theorem B4315589 : Blo 1917435 4315589 := bbase (se 4 (by rfl) ⟨404586, by rfl⟩ : syracuseStep 4315589 = 809173) (by norm_num)
theorem B2877059 : Blo 1917435 2877059 := bstep (se 1 (by rfl) ⟨2157794, by rfl⟩ : syracuseStep 2877059 = 4315589) B4315589
theorem B1918039 : Blo 1917435 1918039 := bstep (se 1 (by rfl) ⟨1438529, by rfl⟩ : syracuseStep 1918039 = 2877059) B2877059
theorem B3280861 : Blo 1917435 3280861 := bbase (se 3 (by rfl) ⟨615161, by rfl⟩ : syracuseStep 3280861 = 1230323) (by norm_num)
theorem B4374481 : Blo 1917435 4374481 := bstep (se 2 (by rfl) ⟨1640430, by rfl⟩ : syracuseStep 4374481 = 3280861) B3280861
theorem B5832641 : Blo 1917435 5832641 := bstep (se 2 (by rfl) ⟨2187240, by rfl⟩ : syracuseStep 5832641 = 4374481) B4374481
theorem B3888427 : Blo 1917435 3888427 := bstep (se 1 (by rfl) ⟨2916320, by rfl⟩ : syracuseStep 3888427 = 5832641) B5832641
theorem B5184569 : Blo 1917435 5184569 := bstep (se 2 (by rfl) ⟨1944213, by rfl⟩ : syracuseStep 5184569 = 3888427) B3888427
theorem B3456379 : Blo 1917435 3456379 := bstep (se 1 (by rfl) ⟨2592284, by rfl⟩ : syracuseStep 3456379 = 5184569) B5184569
theorem B4608505 : Blo 1917435 4608505 := bstep (se 2 (by rfl) ⟨1728189, by rfl⟩ : syracuseStep 4608505 = 3456379) B3456379
theorem B6144673 : Blo 1917435 6144673 := bstep (se 2 (by rfl) ⟨2304252, by rfl⟩ : syracuseStep 6144673 = 4608505) B4608505
theorem B8192897 : Blo 1917435 8192897 := bstep (se 2 (by rfl) ⟨3072336, by rfl⟩ : syracuseStep 8192897 = 6144673) B6144673
theorem B5461931 : Blo 1917435 5461931 := bstep (se 1 (by rfl) ⟨4096448, by rfl⟩ : syracuseStep 5461931 = 8192897) B8192897
theorem B3641287 : Blo 1917435 3641287 := bstep (se 1 (by rfl) ⟨2730965, by rfl⟩ : syracuseStep 3641287 = 5461931) B5461931
theorem B4855049 : Blo 1917435 4855049 := bstep (se 2 (by rfl) ⟨1820643, by rfl⟩ : syracuseStep 4855049 = 3641287) B3641287
theorem B3236699 : Blo 1917435 3236699 := bstep (se 1 (by rfl) ⟨2427524, by rfl⟩ : syracuseStep 3236699 = 4855049) B4855049
theorem B2157799 : Blo 1917435 2157799 := bstep (se 1 (by rfl) ⟨1618349, by rfl⟩ : syracuseStep 2157799 = 3236699) B3236699
theorem B2877065 : Blo 1917435 2877065 := bstep (se 2 (by rfl) ⟨1078899, by rfl⟩ : syracuseStep 2877065 = 2157799) B2157799
theorem B1918043 : Blo 1917435 1918043 := bstep (se 1 (by rfl) ⟨1438532, by rfl⟩ : syracuseStep 1918043 = 2877065) B2877065
theorem B9710117 : Blo 1917435 9710117 := bbase (se 4 (by rfl) ⟨910323, by rfl⟩ : syracuseStep 9710117 = 1820647) (by norm_num)
theorem B6473411 : Blo 1917435 6473411 := bstep (se 1 (by rfl) ⟨4855058, by rfl⟩ : syracuseStep 6473411 = 9710117) B9710117
theorem B4315607 : Blo 1917435 4315607 := bstep (se 1 (by rfl) ⟨3236705, by rfl⟩ : syracuseStep 4315607 = 6473411) B6473411
theorem B2877071 : Blo 1917435 2877071 := bstep (se 1 (by rfl) ⟨2157803, by rfl⟩ : syracuseStep 2877071 = 4315607) B4315607
theorem B1918047 : Blo 1917435 1918047 := bstep (se 1 (by rfl) ⟨1438535, by rfl⟩ : syracuseStep 1918047 = 2877071) B2877071
theorem B2877077 : Blo 1917435 2877077 := bbase (se 6 (by rfl) ⟨67431, by rfl⟩ : syracuseStep 2877077 = 134863) (by norm_num)
theorem B1918051 : Blo 1917435 1918051 := bstep (se 1 (by rfl) ⟨1438538, by rfl⟩ : syracuseStep 1918051 = 2877077) B2877077
theorem B4608533 : Blo 1917435 4608533 := bbase (se 6 (by rfl) ⟨108012, by rfl⟩ : syracuseStep 4608533 = 216025) (by norm_num)
theorem B12289421 : Blo 1917435 12289421 := bstep (se 3 (by rfl) ⟨2304266, by rfl⟩ : syracuseStep 12289421 = 4608533) B4608533
theorem B8192947 : Blo 1917435 8192947 := bstep (se 1 (by rfl) ⟨6144710, by rfl⟩ : syracuseStep 8192947 = 12289421) B12289421
theorem B10923929 : Blo 1917435 10923929 := bstep (se 2 (by rfl) ⟨4096473, by rfl⟩ : syracuseStep 10923929 = 8192947) B8192947
theorem B7282619 : Blo 1917435 7282619 := bstep (se 1 (by rfl) ⟨5461964, by rfl⟩ : syracuseStep 7282619 = 10923929) B10923929
theorem B4855079 : Blo 1917435 4855079 := bstep (se 1 (by rfl) ⟨3641309, by rfl⟩ : syracuseStep 4855079 = 7282619) B7282619
theorem B3236719 : Blo 1917435 3236719 := bstep (se 1 (by rfl) ⟨2427539, by rfl⟩ : syracuseStep 3236719 = 4855079) B4855079
theorem B4315625 : Blo 1917435 4315625 := bstep (se 2 (by rfl) ⟨1618359, by rfl⟩ : syracuseStep 4315625 = 3236719) B3236719
theorem B2877083 : Blo 1917435 2877083 := bstep (se 1 (by rfl) ⟨2157812, by rfl⟩ : syracuseStep 2877083 = 4315625) B4315625
theorem B1918055 : Blo 1917435 1918055 := bstep (se 1 (by rfl) ⟨1438541, by rfl⟩ : syracuseStep 1918055 = 2877083) B2877083
theorem B2157817 : Blo 1917435 2157817 := bbase (se 2 (by rfl) ⟨809181, by rfl⟩ : syracuseStep 2157817 = 1618363) (by norm_num)
theorem B2877089 : Blo 1917435 2877089 := bstep (se 2 (by rfl) ⟨1078908, by rfl⟩ : syracuseStep 2877089 = 2157817) B2157817
theorem B1918059 : Blo 1917435 1918059 := bstep (se 1 (by rfl) ⟨1438544, by rfl⟩ : syracuseStep 1918059 = 2877089) B2877089
theorem B8192981 : Blo 1917435 8192981 := bbase (se 7 (by rfl) ⟨96011, by rfl⟩ : syracuseStep 8192981 = 192023) (by norm_num)
theorem B5461987 : Blo 1917435 5461987 := bstep (se 1 (by rfl) ⟨4096490, by rfl⟩ : syracuseStep 5461987 = 8192981) B8192981
theorem B7282649 : Blo 1917435 7282649 := bstep (se 2 (by rfl) ⟨2730993, by rfl⟩ : syracuseStep 7282649 = 5461987) B5461987
theorem B4855099 : Blo 1917435 4855099 := bstep (se 1 (by rfl) ⟨3641324, by rfl⟩ : syracuseStep 4855099 = 7282649) B7282649
theorem B6473465 : Blo 1917435 6473465 := bstep (se 2 (by rfl) ⟨2427549, by rfl⟩ : syracuseStep 6473465 = 4855099) B4855099
theorem B4315643 : Blo 1917435 4315643 := bstep (se 1 (by rfl) ⟨3236732, by rfl⟩ : syracuseStep 4315643 = 6473465) B6473465
theorem B2877095 : Blo 1917435 2877095 := bstep (se 1 (by rfl) ⟨2157821, by rfl⟩ : syracuseStep 2877095 = 4315643) B4315643
theorem B1918063 : Blo 1917435 1918063 := bstep (se 1 (by rfl) ⟨1438547, by rfl⟩ : syracuseStep 1918063 = 2877095) B2877095
theorem B2877101 : Blo 1917435 2877101 := bbase (se 3 (by rfl) ⟨539456, by rfl⟩ : syracuseStep 2877101 = 1078913) (by norm_num)
theorem B1918067 : Blo 1917435 1918067 := bstep (se 1 (by rfl) ⟨1438550, by rfl⟩ : syracuseStep 1918067 = 2877101) B2877101
theorem B4315661 : Blo 1917435 4315661 := bbase (se 3 (by rfl) ⟨809186, by rfl⟩ : syracuseStep 4315661 = 1618373) (by norm_num)
theorem B2877107 : Blo 1917435 2877107 := bstep (se 1 (by rfl) ⟨2157830, by rfl⟩ : syracuseStep 2877107 = 4315661) B4315661
theorem B1918071 : Blo 1917435 1918071 := bstep (se 1 (by rfl) ⟨1438553, by rfl⟩ : syracuseStep 1918071 = 2877107) B2877107
theorem B2427565 : Blo 1917435 2427565 := bbase (se 3 (by rfl) ⟨455168, by rfl⟩ : syracuseStep 2427565 = 910337) (by norm_num)
theorem B3236753 : Blo 1917435 3236753 := bstep (se 2 (by rfl) ⟨1213782, by rfl⟩ : syracuseStep 3236753 = 2427565) B2427565
theorem B2157835 : Blo 1917435 2157835 := bstep (se 1 (by rfl) ⟨1618376, by rfl⟩ : syracuseStep 2157835 = 3236753) B3236753
theorem B2877113 : Blo 1917435 2877113 := bstep (se 2 (by rfl) ⟨1078917, by rfl⟩ : syracuseStep 2877113 = 2157835) B2157835
theorem B1918075 : Blo 1917435 1918075 := bstep (se 1 (by rfl) ⟨1438556, by rfl⟩ : syracuseStep 1918075 = 2877113) B2877113
theorem B2187281 : Blo 1917435 2187281 := bbase (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) (by norm_num)
theorem B5832749 : Blo 1917435 5832749 := bstep (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) B2187281
theorem B3888499 : Blo 1917435 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B5184665 : Blo 1917435 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B3456443 : Blo 1917435 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B2304295 : Blo 1917435 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B12289573 : Blo 1917435 12289573 := bstep (se 4 (by rfl) ⟨1152147, by rfl⟩ : syracuseStep 12289573 = 2304295) B2304295
theorem B16386097 : Blo 1917435 16386097 := bstep (se 2 (by rfl) ⟨6144786, by rfl⟩ : syracuseStep 16386097 = 12289573) B12289573
theorem B21848129 : Blo 1917435 21848129 := bstep (se 2 (by rfl) ⟨8193048, by rfl⟩ : syracuseStep 21848129 = 16386097) B16386097
theorem B14565419 : Blo 1917435 14565419 := bstep (se 1 (by rfl) ⟨10924064, by rfl⟩ : syracuseStep 14565419 = 21848129) B21848129
theorem B9710279 : Blo 1917435 9710279 := bstep (se 1 (by rfl) ⟨7282709, by rfl⟩ : syracuseStep 9710279 = 14565419) B14565419
theorem B6473519 : Blo 1917435 6473519 := bstep (se 1 (by rfl) ⟨4855139, by rfl⟩ : syracuseStep 6473519 = 9710279) B9710279
theorem B4315679 : Blo 1917435 4315679 := bstep (se 1 (by rfl) ⟨3236759, by rfl⟩ : syracuseStep 4315679 = 6473519) B6473519
theorem B2877119 : Blo 1917435 2877119 := bstep (se 1 (by rfl) ⟨2157839, by rfl⟩ : syracuseStep 2877119 = 4315679) B4315679
theorem B1918079 : Blo 1917435 1918079 := bstep (se 1 (by rfl) ⟨1438559, by rfl⟩ : syracuseStep 1918079 = 2877119) B2877119
theorem B2877125 : Blo 1917435 2877125 := bbase (se 4 (by rfl) ⟨269730, by rfl⟩ : syracuseStep 2877125 = 539461) (by norm_num)
theorem B1918083 : Blo 1917435 1918083 := bstep (se 1 (by rfl) ⟨1438562, by rfl⟩ : syracuseStep 1918083 = 2877125) B2877125
theorem B3236773 : Blo 1917435 3236773 := bbase (se 4 (by rfl) ⟨303447, by rfl⟩ : syracuseStep 3236773 = 606895) (by norm_num)
theorem B4315697 : Blo 1917435 4315697 := bstep (se 2 (by rfl) ⟨1618386, by rfl⟩ : syracuseStep 4315697 = 3236773) B3236773
theorem B2877131 : Blo 1917435 2877131 := bstep (se 1 (by rfl) ⟨2157848, by rfl⟩ : syracuseStep 2877131 = 4315697) B4315697
theorem B1918087 : Blo 1917435 1918087 := bstep (se 1 (by rfl) ⟨1438565, by rfl⟩ : syracuseStep 1918087 = 2877131) B2877131
theorem B2157853 : Blo 1917435 2157853 := bbase (se 3 (by rfl) ⟨404597, by rfl⟩ : syracuseStep 2157853 = 809195) (by norm_num)
theorem B2877137 : Blo 1917435 2877137 := bstep (se 2 (by rfl) ⟨1078926, by rfl⟩ : syracuseStep 2877137 = 2157853) B2157853
theorem B1918091 : Blo 1917435 1918091 := bstep (se 1 (by rfl) ⟨1438568, by rfl⟩ : syracuseStep 1918091 = 2877137) B2877137
theorem B6473573 : Blo 1917435 6473573 := bbase (se 4 (by rfl) ⟨606897, by rfl⟩ : syracuseStep 6473573 = 1213795) (by norm_num)
theorem B4315715 : Blo 1917435 4315715 := bstep (se 1 (by rfl) ⟨3236786, by rfl⟩ : syracuseStep 4315715 = 6473573) B6473573
theorem B2877143 : Blo 1917435 2877143 := bstep (se 1 (by rfl) ⟨2157857, by rfl⟩ : syracuseStep 2877143 = 4315715) B4315715
theorem B1918095 : Blo 1917435 1918095 := bstep (se 1 (by rfl) ⟨1438571, by rfl⟩ : syracuseStep 1918095 = 2877143) B2877143
theorem B2877149 : Blo 1917435 2877149 := bbase (se 3 (by rfl) ⟨539465, by rfl⟩ : syracuseStep 2877149 = 1078931) (by norm_num)
theorem B1918099 : Blo 1917435 1918099 := bstep (se 1 (by rfl) ⟨1438574, by rfl⟩ : syracuseStep 1918099 = 2877149) B2877149
theorem B4315733 : Blo 1917435 4315733 := bbase (se 8 (by rfl) ⟨25287, by rfl⟩ : syracuseStep 4315733 = 50575) (by norm_num)
theorem B2877155 : Blo 1917435 2877155 := bstep (se 1 (by rfl) ⟨2157866, by rfl⟩ : syracuseStep 2877155 = 4315733) B4315733
theorem B1918103 : Blo 1917435 1918103 := bstep (se 1 (by rfl) ⟨1438577, by rfl⟩ : syracuseStep 1918103 = 2877155) B2877155
theorem B3888557 : Blo 1917435 3888557 := bbase (se 3 (by rfl) ⟨729104, by rfl⟩ : syracuseStep 3888557 = 1458209) (by norm_num)
theorem B2592371 : Blo 1917435 2592371 := bstep (se 1 (by rfl) ⟨1944278, by rfl⟩ : syracuseStep 2592371 = 3888557) B3888557
theorem B6912989 : Blo 1917435 6912989 := bstep (se 3 (by rfl) ⟨1296185, by rfl⟩ : syracuseStep 6912989 = 2592371) B2592371
theorem B4608659 : Blo 1917435 4608659 := bstep (se 1 (by rfl) ⟨3456494, by rfl⟩ : syracuseStep 4608659 = 6912989) B6912989
theorem B3072439 : Blo 1917435 3072439 := bstep (se 1 (by rfl) ⟨2304329, by rfl⟩ : syracuseStep 3072439 = 4608659) B4608659
theorem B4096585 : Blo 1917435 4096585 := bstep (se 2 (by rfl) ⟨1536219, by rfl⟩ : syracuseStep 4096585 = 3072439) B3072439
theorem B5462113 : Blo 1917435 5462113 := bstep (se 2 (by rfl) ⟨2048292, by rfl⟩ : syracuseStep 5462113 = 4096585) B4096585
theorem B7282817 : Blo 1917435 7282817 := bstep (se 2 (by rfl) ⟨2731056, by rfl⟩ : syracuseStep 7282817 = 5462113) B5462113
theorem B4855211 : Blo 1917435 4855211 := bstep (se 1 (by rfl) ⟨3641408, by rfl⟩ : syracuseStep 4855211 = 7282817) B7282817
theorem B3236807 : Blo 1917435 3236807 := bstep (se 1 (by rfl) ⟨2427605, by rfl⟩ : syracuseStep 3236807 = 4855211) B4855211
theorem B2157871 : Blo 1917435 2157871 := bstep (se 1 (by rfl) ⟨1618403, by rfl⟩ : syracuseStep 2157871 = 3236807) B3236807
theorem B2877161 : Blo 1917435 2877161 := bstep (se 2 (by rfl) ⟨1078935, by rfl⟩ : syracuseStep 2877161 = 2157871) B2157871
theorem B1918107 : Blo 1917435 1918107 := bstep (se 1 (by rfl) ⟨1438580, by rfl⟩ : syracuseStep 1918107 = 2877161) B2877161
theorem B2806093 : Blo 1917435 2806093 := bbase (se 3 (by rfl) ⟨526142, by rfl⟩ : syracuseStep 2806093 = 1052285) (by norm_num)
theorem B3741457 : Blo 1917435 3741457 := bstep (se 2 (by rfl) ⟨1403046, by rfl⟩ : syracuseStep 3741457 = 2806093) B2806093
theorem B4988609 : Blo 1917435 4988609 := bstep (se 2 (by rfl) ⟨1870728, by rfl⟩ : syracuseStep 4988609 = 3741457) B3741457
theorem B53211829 : Blo 1917435 53211829 := bstep (se 5 (by rfl) ⟨2494304, by rfl⟩ : syracuseStep 53211829 = 4988609) B4988609
theorem B70949105 : Blo 1917435 70949105 := bstep (se 2 (by rfl) ⟨26605914, by rfl⟩ : syracuseStep 70949105 = 53211829) B53211829
theorem B47299403 : Blo 1917435 47299403 := bstep (se 1 (by rfl) ⟨35474552, by rfl⟩ : syracuseStep 47299403 = 70949105) B70949105
theorem B126131741 : Blo 1917435 126131741 := bstep (se 3 (by rfl) ⟨23649701, by rfl⟩ : syracuseStep 126131741 = 47299403) B47299403
theorem B84087827 : Blo 1917435 84087827 := bstep (se 1 (by rfl) ⟨63065870, by rfl⟩ : syracuseStep 84087827 = 126131741) B126131741
theorem B56058551 : Blo 1917435 56058551 := bstep (se 1 (by rfl) ⟨42043913, by rfl⟩ : syracuseStep 56058551 = 84087827) B84087827
theorem B37372367 : Blo 1917435 37372367 := bstep (se 1 (by rfl) ⟨28029275, by rfl⟩ : syracuseStep 37372367 = 56058551) B56058551
theorem B99659645 : Blo 1917435 99659645 := bstep (se 3 (by rfl) ⟨18686183, by rfl⟩ : syracuseStep 99659645 = 37372367) B37372367
theorem B66439763 : Blo 1917435 66439763 := bstep (se 1 (by rfl) ⟨49829822, by rfl⟩ : syracuseStep 66439763 = 99659645) B99659645
theorem B44293175 : Blo 1917435 44293175 := bstep (se 1 (by rfl) ⟨33219881, by rfl⟩ : syracuseStep 44293175 = 66439763) B66439763
theorem B29528783 : Blo 1917435 29528783 := bstep (se 1 (by rfl) ⟨22146587, by rfl⟩ : syracuseStep 29528783 = 44293175) B44293175
theorem B19685855 : Blo 1917435 19685855 := bstep (se 1 (by rfl) ⟨14764391, by rfl⟩ : syracuseStep 19685855 = 29528783) B29528783
theorem B13123903 : Blo 1917435 13123903 := bstep (se 1 (by rfl) ⟨9842927, by rfl⟩ : syracuseStep 13123903 = 19685855) B19685855
theorem B17498537 : Blo 1917435 17498537 := bstep (se 2 (by rfl) ⟨6561951, by rfl⟩ : syracuseStep 17498537 = 13123903) B13123903
theorem B11665691 : Blo 1917435 11665691 := bstep (se 1 (by rfl) ⟨8749268, by rfl⟩ : syracuseStep 11665691 = 17498537) B17498537
theorem B7777127 : Blo 1917435 7777127 := bstep (se 1 (by rfl) ⟨5832845, by rfl⟩ : syracuseStep 7777127 = 11665691) B11665691
theorem B5184751 : Blo 1917435 5184751 := bstep (se 1 (by rfl) ⟨3888563, by rfl⟩ : syracuseStep 5184751 = 7777127) B7777127
theorem B6913001 : Blo 1917435 6913001 := bstep (se 2 (by rfl) ⟨2592375, by rfl⟩ : syracuseStep 6913001 = 5184751) B5184751
theorem B4608667 : Blo 1917435 4608667 := bstep (se 1 (by rfl) ⟨3456500, by rfl⟩ : syracuseStep 4608667 = 6913001) B6913001
theorem B24579557 : Blo 1917435 24579557 := bstep (se 4 (by rfl) ⟨2304333, by rfl⟩ : syracuseStep 24579557 = 4608667) B4608667
theorem B16386371 : Blo 1917435 16386371 := bstep (se 1 (by rfl) ⟨12289778, by rfl⟩ : syracuseStep 16386371 = 24579557) B24579557
theorem B10924247 : Blo 1917435 10924247 := bstep (se 1 (by rfl) ⟨8193185, by rfl⟩ : syracuseStep 10924247 = 16386371) B16386371
theorem B7282831 : Blo 1917435 7282831 := bstep (se 1 (by rfl) ⟨5462123, by rfl⟩ : syracuseStep 7282831 = 10924247) B10924247
theorem B9710441 : Blo 1917435 9710441 := bstep (se 2 (by rfl) ⟨3641415, by rfl⟩ : syracuseStep 9710441 = 7282831) B7282831
theorem B6473627 : Blo 1917435 6473627 := bstep (se 1 (by rfl) ⟨4855220, by rfl⟩ : syracuseStep 6473627 = 9710441) B9710441
theorem B4315751 : Blo 1917435 4315751 := bstep (se 1 (by rfl) ⟨3236813, by rfl⟩ : syracuseStep 4315751 = 6473627) B6473627
theorem B2877167 : Blo 1917435 2877167 := bstep (se 1 (by rfl) ⟨2157875, by rfl⟩ : syracuseStep 2877167 = 4315751) B4315751
theorem B1918111 : Blo 1917435 1918111 := bstep (se 1 (by rfl) ⟨1438583, by rfl⟩ : syracuseStep 1918111 = 2877167) B2877167
theorem B2877173 : Blo 1917435 2877173 := bbase (se 5 (by rfl) ⟨134867, by rfl⟩ : syracuseStep 2877173 = 269735) (by norm_num)
theorem B1918115 : Blo 1917435 1918115 := bstep (se 1 (by rfl) ⟨1438586, by rfl⟩ : syracuseStep 1918115 = 2877173) B2877173
theorem B8193221 : Blo 1917435 8193221 := bbase (se 4 (by rfl) ⟨768114, by rfl⟩ : syracuseStep 8193221 = 1536229) (by norm_num)
theorem B5462147 : Blo 1917435 5462147 := bstep (se 1 (by rfl) ⟨4096610, by rfl⟩ : syracuseStep 5462147 = 8193221) B8193221
theorem B3641431 : Blo 1917435 3641431 := bstep (se 1 (by rfl) ⟨2731073, by rfl⟩ : syracuseStep 3641431 = 5462147) B5462147
theorem B4855241 : Blo 1917435 4855241 := bstep (se 2 (by rfl) ⟨1820715, by rfl⟩ : syracuseStep 4855241 = 3641431) B3641431
theorem B3236827 : Blo 1917435 3236827 := bstep (se 1 (by rfl) ⟨2427620, by rfl⟩ : syracuseStep 3236827 = 4855241) B4855241
theorem B4315769 : Blo 1917435 4315769 := bstep (se 2 (by rfl) ⟨1618413, by rfl⟩ : syracuseStep 4315769 = 3236827) B3236827
theorem B2877179 : Blo 1917435 2877179 := bstep (se 1 (by rfl) ⟨2157884, by rfl⟩ : syracuseStep 2877179 = 4315769) B4315769
theorem B1918119 : Blo 1917435 1918119 := bstep (se 1 (by rfl) ⟨1438589, by rfl⟩ : syracuseStep 1918119 = 2877179) B2877179
theorem B2157889 : Blo 1917435 2157889 := bbase (se 2 (by rfl) ⟨809208, by rfl⟩ : syracuseStep 2157889 = 1618417) (by norm_num)
theorem B2877185 : Blo 1917435 2877185 := bstep (se 2 (by rfl) ⟨1078944, by rfl⟩ : syracuseStep 2877185 = 2157889) B2157889
theorem B1918123 : Blo 1917435 1918123 := bstep (se 1 (by rfl) ⟨1438592, by rfl⟩ : syracuseStep 1918123 = 2877185) B2877185
theorem B4855261 : Blo 1917435 4855261 := bbase (se 3 (by rfl) ⟨910361, by rfl⟩ : syracuseStep 4855261 = 1820723) (by norm_num)
theorem B6473681 : Blo 1917435 6473681 := bstep (se 2 (by rfl) ⟨2427630, by rfl⟩ : syracuseStep 6473681 = 4855261) B4855261
theorem B4315787 : Blo 1917435 4315787 := bstep (se 1 (by rfl) ⟨3236840, by rfl⟩ : syracuseStep 4315787 = 6473681) B6473681
theorem B2877191 : Blo 1917435 2877191 := bstep (se 1 (by rfl) ⟨2157893, by rfl⟩ : syracuseStep 2877191 = 4315787) B4315787
theorem B1918127 : Blo 1917435 1918127 := bstep (se 1 (by rfl) ⟨1438595, by rfl⟩ : syracuseStep 1918127 = 2877191) B2877191
theorem B2877197 : Blo 1917435 2877197 := bbase (se 3 (by rfl) ⟨539474, by rfl⟩ : syracuseStep 2877197 = 1078949) (by norm_num)
theorem B1918131 : Blo 1917435 1918131 := bstep (se 1 (by rfl) ⟨1438598, by rfl⟩ : syracuseStep 1918131 = 2877197) B2877197
theorem B4315805 : Blo 1917435 4315805 := bbase (se 3 (by rfl) ⟨809213, by rfl⟩ : syracuseStep 4315805 = 1618427) (by norm_num)
theorem B2877203 : Blo 1917435 2877203 := bstep (se 1 (by rfl) ⟨2157902, by rfl⟩ : syracuseStep 2877203 = 4315805) B4315805
theorem B1918135 : Blo 1917435 1918135 := bstep (se 1 (by rfl) ⟨1438601, by rfl⟩ : syracuseStep 1918135 = 2877203) B2877203
theorem B3236861 : Blo 1917435 3236861 := bbase (se 3 (by rfl) ⟨606911, by rfl⟩ : syracuseStep 3236861 = 1213823) (by norm_num)
theorem B2157907 : Blo 1917435 2157907 := bstep (se 1 (by rfl) ⟨1618430, by rfl⟩ : syracuseStep 2157907 = 3236861) B3236861
theorem B2877209 : Blo 1917435 2877209 := bstep (se 2 (by rfl) ⟨1078953, by rfl⟩ : syracuseStep 2877209 = 2157907) B2157907
theorem B1918139 : Blo 1917435 1918139 := bstep (se 1 (by rfl) ⟨1438604, by rfl⟩ : syracuseStep 1918139 = 2877209) B2877209
theorem B4096661 : Blo 1917435 4096661 := bbase (se 6 (by rfl) ⟨96015, by rfl⟩ : syracuseStep 4096661 = 192031) (by norm_num)
theorem B10924429 : Blo 1917435 10924429 := bstep (se 3 (by rfl) ⟨2048330, by rfl⟩ : syracuseStep 10924429 = 4096661) B4096661
theorem B14565905 : Blo 1917435 14565905 := bstep (se 2 (by rfl) ⟨5462214, by rfl⟩ : syracuseStep 14565905 = 10924429) B10924429
theorem B9710603 : Blo 1917435 9710603 := bstep (se 1 (by rfl) ⟨7282952, by rfl⟩ : syracuseStep 9710603 = 14565905) B14565905
theorem B6473735 : Blo 1917435 6473735 := bstep (se 1 (by rfl) ⟨4855301, by rfl⟩ : syracuseStep 6473735 = 9710603) B9710603
theorem B4315823 : Blo 1917435 4315823 := bstep (se 1 (by rfl) ⟨3236867, by rfl⟩ : syracuseStep 4315823 = 6473735) B6473735
theorem B2877215 : Blo 1917435 2877215 := bstep (se 1 (by rfl) ⟨2157911, by rfl⟩ : syracuseStep 2877215 = 4315823) B4315823
theorem B1918143 : Blo 1917435 1918143 := bstep (se 1 (by rfl) ⟨1438607, by rfl⟩ : syracuseStep 1918143 = 2877215) B2877215
theorem B2877221 : Blo 1917435 2877221 := bbase (se 4 (by rfl) ⟨269739, by rfl⟩ : syracuseStep 2877221 = 539479) (by norm_num)
theorem B1918147 : Blo 1917435 1918147 := bstep (se 1 (by rfl) ⟨1438610, by rfl⟩ : syracuseStep 1918147 = 2877221) B2877221
theorem B2427661 : Blo 1917435 2427661 := bbase (se 3 (by rfl) ⟨455186, by rfl⟩ : syracuseStep 2427661 = 910373) (by norm_num)
theorem B3236881 : Blo 1917435 3236881 := bstep (se 2 (by rfl) ⟨1213830, by rfl⟩ : syracuseStep 3236881 = 2427661) B2427661
theorem B4315841 : Blo 1917435 4315841 := bstep (se 2 (by rfl) ⟨1618440, by rfl⟩ : syracuseStep 4315841 = 3236881) B3236881
theorem B2877227 : Blo 1917435 2877227 := bstep (se 1 (by rfl) ⟨2157920, by rfl⟩ : syracuseStep 2877227 = 4315841) B4315841
theorem B1918151 : Blo 1917435 1918151 := bstep (se 1 (by rfl) ⟨1438613, by rfl⟩ : syracuseStep 1918151 = 2877227) B2877227
theorem B2157925 : Blo 1917435 2157925 := bbase (se 4 (by rfl) ⟨202305, by rfl⟩ : syracuseStep 2157925 = 404611) (by norm_num)
theorem B2877233 : Blo 1917435 2877233 := bstep (se 2 (by rfl) ⟨1078962, by rfl⟩ : syracuseStep 2877233 = 2157925) B2157925
theorem B1918155 : Blo 1917435 1918155 := bstep (se 1 (by rfl) ⟨1438616, by rfl⟩ : syracuseStep 1918155 = 2877233) B2877233
theorem B5462261 : Blo 1917435 5462261 := bbase (se 5 (by rfl) ⟨256043, by rfl⟩ : syracuseStep 5462261 = 512087) (by norm_num)
theorem B3641507 : Blo 1917435 3641507 := bstep (se 1 (by rfl) ⟨2731130, by rfl⟩ : syracuseStep 3641507 = 5462261) B5462261
theorem B2427671 : Blo 1917435 2427671 := bstep (se 1 (by rfl) ⟨1820753, by rfl⟩ : syracuseStep 2427671 = 3641507) B3641507
theorem B6473789 : Blo 1917435 6473789 := bstep (se 3 (by rfl) ⟨1213835, by rfl⟩ : syracuseStep 6473789 = 2427671) B2427671
theorem B4315859 : Blo 1917435 4315859 := bstep (se 1 (by rfl) ⟨3236894, by rfl⟩ : syracuseStep 4315859 = 6473789) B6473789
theorem B2877239 : Blo 1917435 2877239 := bstep (se 1 (by rfl) ⟨2157929, by rfl⟩ : syracuseStep 2877239 = 4315859) B4315859
theorem B1918159 : Blo 1917435 1918159 := bstep (se 1 (by rfl) ⟨1438619, by rfl⟩ : syracuseStep 1918159 = 2877239) B2877239
theorem B2877245 : Blo 1917435 2877245 := bbase (se 3 (by rfl) ⟨539483, by rfl⟩ : syracuseStep 2877245 = 1078967) (by norm_num)
theorem B1918163 : Blo 1917435 1918163 := bstep (se 1 (by rfl) ⟨1438622, by rfl⟩ : syracuseStep 1918163 = 2877245) B2877245
theorem B4315877 : Blo 1917435 4315877 := bbase (se 4 (by rfl) ⟨404613, by rfl⟩ : syracuseStep 4315877 = 809227) (by norm_num)
theorem B2877251 : Blo 1917435 2877251 := bstep (se 1 (by rfl) ⟨2157938, by rfl⟩ : syracuseStep 2877251 = 4315877) B4315877
theorem B1918167 : Blo 1917435 1918167 := bstep (se 1 (by rfl) ⟨1438625, by rfl⟩ : syracuseStep 1918167 = 2877251) B2877251
theorem B4855373 : Blo 1917435 4855373 := bbase (se 3 (by rfl) ⟨910382, by rfl⟩ : syracuseStep 4855373 = 1820765) (by norm_num)
theorem B3236915 : Blo 1917435 3236915 := bstep (se 1 (by rfl) ⟨2427686, by rfl⟩ : syracuseStep 3236915 = 4855373) B4855373
theorem B2157943 : Blo 1917435 2157943 := bstep (se 1 (by rfl) ⟨1618457, by rfl⟩ : syracuseStep 2157943 = 3236915) B3236915
theorem B2877257 : Blo 1917435 2877257 := bstep (se 2 (by rfl) ⟨1078971, by rfl⟩ : syracuseStep 2877257 = 2157943) B2157943
theorem B1918171 : Blo 1917435 1918171 := bstep (se 1 (by rfl) ⟨1438628, by rfl⟩ : syracuseStep 1918171 = 2877257) B2877257
theorem B2048365 : Blo 1917435 2048365 := bbase (se 3 (by rfl) ⟨384068, by rfl⟩ : syracuseStep 2048365 = 768137) (by norm_num)
theorem B2731153 : Blo 1917435 2731153 := bstep (se 2 (by rfl) ⟨1024182, by rfl⟩ : syracuseStep 2731153 = 2048365) B2048365
theorem B3641537 : Blo 1917435 3641537 := bstep (se 2 (by rfl) ⟨1365576, by rfl⟩ : syracuseStep 3641537 = 2731153) B2731153
theorem B9710765 : Blo 1917435 9710765 := bstep (se 3 (by rfl) ⟨1820768, by rfl⟩ : syracuseStep 9710765 = 3641537) B3641537
theorem B6473843 : Blo 1917435 6473843 := bstep (se 1 (by rfl) ⟨4855382, by rfl⟩ : syracuseStep 6473843 = 9710765) B9710765
theorem B4315895 : Blo 1917435 4315895 := bstep (se 1 (by rfl) ⟨3236921, by rfl⟩ : syracuseStep 4315895 = 6473843) B6473843
theorem B2877263 : Blo 1917435 2877263 := bstep (se 1 (by rfl) ⟨2157947, by rfl⟩ : syracuseStep 2877263 = 4315895) B4315895
theorem B1918175 : Blo 1917435 1918175 := bstep (se 1 (by rfl) ⟨1438631, by rfl⟩ : syracuseStep 1918175 = 2877263) B2877263
theorem B2877269 : Blo 1917435 2877269 := bbase (se 9 (by rfl) ⟨8429, by rfl⟩ : syracuseStep 2877269 = 16859) (by norm_num)
theorem B1918179 : Blo 1917435 1918179 := bstep (se 1 (by rfl) ⟨1438634, by rfl⟩ : syracuseStep 1918179 = 2877269) B2877269
theorem B2916533 : Blo 1917435 2916533 := bbase (se 5 (by rfl) ⟨136712, by rfl⟩ : syracuseStep 2916533 = 273425) (by norm_num)
theorem B7777421 : Blo 1917435 7777421 := bstep (se 3 (by rfl) ⟨1458266, by rfl⟩ : syracuseStep 7777421 = 2916533) B2916533
theorem B5184947 : Blo 1917435 5184947 := bstep (se 1 (by rfl) ⟨3888710, by rfl⟩ : syracuseStep 5184947 = 7777421) B7777421
theorem B3456631 : Blo 1917435 3456631 := bstep (se 1 (by rfl) ⟨2592473, by rfl⟩ : syracuseStep 3456631 = 5184947) B5184947
theorem B4608841 : Blo 1917435 4608841 := bstep (se 2 (by rfl) ⟨1728315, by rfl⟩ : syracuseStep 4608841 = 3456631) B3456631
theorem B6145121 : Blo 1917435 6145121 := bstep (se 2 (by rfl) ⟨2304420, by rfl⟩ : syracuseStep 6145121 = 4608841) B4608841
theorem B4096747 : Blo 1917435 4096747 := bstep (se 1 (by rfl) ⟨3072560, by rfl⟩ : syracuseStep 4096747 = 6145121) B6145121
theorem B5462329 : Blo 1917435 5462329 := bstep (se 2 (by rfl) ⟨2048373, by rfl⟩ : syracuseStep 5462329 = 4096747) B4096747
theorem B7283105 : Blo 1917435 7283105 := bstep (se 2 (by rfl) ⟨2731164, by rfl⟩ : syracuseStep 7283105 = 5462329) B5462329
theorem B4855403 : Blo 1917435 4855403 := bstep (se 1 (by rfl) ⟨3641552, by rfl⟩ : syracuseStep 4855403 = 7283105) B7283105
theorem B3236935 : Blo 1917435 3236935 := bstep (se 1 (by rfl) ⟨2427701, by rfl⟩ : syracuseStep 3236935 = 4855403) B4855403
theorem B4315913 : Blo 1917435 4315913 := bstep (se 2 (by rfl) ⟨1618467, by rfl⟩ : syracuseStep 4315913 = 3236935) B3236935
theorem B2877275 : Blo 1917435 2877275 := bstep (se 1 (by rfl) ⟨2157956, by rfl⟩ : syracuseStep 2877275 = 4315913) B4315913
theorem B1918183 : Blo 1917435 1918183 := bstep (se 1 (by rfl) ⟨1438637, by rfl⟩ : syracuseStep 1918183 = 2877275) B2877275
theorem B2157961 : Blo 1917435 2157961 := bbase (se 2 (by rfl) ⟨809235, by rfl⟩ : syracuseStep 2157961 = 1618471) (by norm_num)
theorem B2877281 : Blo 1917435 2877281 := bstep (se 2 (by rfl) ⟨1078980, by rfl⟩ : syracuseStep 2877281 = 2157961) B2157961
theorem B1918187 : Blo 1917435 1918187 := bstep (se 1 (by rfl) ⟨1438640, by rfl⟩ : syracuseStep 1918187 = 2877281) B2877281
theorem B8418629 : Blo 1917435 8418629 := bbase (se 4 (by rfl) ⟨789246, by rfl⟩ : syracuseStep 8418629 = 1578493) (by norm_num)
theorem B5612419 : Blo 1917435 5612419 := bstep (se 1 (by rfl) ⟨4209314, by rfl⟩ : syracuseStep 5612419 = 8418629) B8418629
theorem B29932901 : Blo 1917435 29932901 := bstep (se 4 (by rfl) ⟨2806209, by rfl⟩ : syracuseStep 29932901 = 5612419) B5612419
theorem B19955267 : Blo 1917435 19955267 := bstep (se 1 (by rfl) ⟨14966450, by rfl⟩ : syracuseStep 19955267 = 29932901) B29932901
theorem B13303511 : Blo 1917435 13303511 := bstep (se 1 (by rfl) ⟨9977633, by rfl⟩ : syracuseStep 13303511 = 19955267) B19955267
theorem B8869007 : Blo 1917435 8869007 := bstep (se 1 (by rfl) ⟨6651755, by rfl⟩ : syracuseStep 8869007 = 13303511) B13303511
theorem B5912671 : Blo 1917435 5912671 := bstep (se 1 (by rfl) ⟨4434503, by rfl⟩ : syracuseStep 5912671 = 8869007) B8869007
theorem B7883561 : Blo 1917435 7883561 := bstep (se 2 (by rfl) ⟨2956335, by rfl⟩ : syracuseStep 7883561 = 5912671) B5912671
theorem B5255707 : Blo 1917435 5255707 := bstep (se 1 (by rfl) ⟨3941780, by rfl⟩ : syracuseStep 5255707 = 7883561) B7883561
theorem B112121749 : Blo 1917435 112121749 := bstep (se 6 (by rfl) ⟨2627853, by rfl⟩ : syracuseStep 112121749 = 5255707) B5255707
theorem B597982661 : Blo 1917435 597982661 := bstep (se 4 (by rfl) ⟨56060874, by rfl⟩ : syracuseStep 597982661 = 112121749) B112121749
theorem B398655107 : Blo 1917435 398655107 := bstep (se 1 (by rfl) ⟨298991330, by rfl⟩ : syracuseStep 398655107 = 597982661) B597982661
theorem B265770071 : Blo 1917435 265770071 := bstep (se 1 (by rfl) ⟨199327553, by rfl⟩ : syracuseStep 265770071 = 398655107) B398655107
theorem B177180047 : Blo 1917435 177180047 := bstep (se 1 (by rfl) ⟨132885035, by rfl⟩ : syracuseStep 177180047 = 265770071) B265770071
theorem B118120031 : Blo 1917435 118120031 := bstep (se 1 (by rfl) ⟨88590023, by rfl⟩ : syracuseStep 118120031 = 177180047) B177180047
theorem B78746687 : Blo 1917435 78746687 := bstep (se 1 (by rfl) ⟨59060015, by rfl⟩ : syracuseStep 78746687 = 118120031) B118120031
theorem B52497791 : Blo 1917435 52497791 := bstep (se 1 (by rfl) ⟨39373343, by rfl⟩ : syracuseStep 52497791 = 78746687) B78746687
theorem B34998527 : Blo 1917435 34998527 := bstep (se 1 (by rfl) ⟨26248895, by rfl⟩ : syracuseStep 34998527 = 52497791) B52497791
theorem B93329405 : Blo 1917435 93329405 := bstep (se 3 (by rfl) ⟨17499263, by rfl⟩ : syracuseStep 93329405 = 34998527) B34998527
theorem B62219603 : Blo 1917435 62219603 := bstep (se 1 (by rfl) ⟨46664702, by rfl⟩ : syracuseStep 62219603 = 93329405) B93329405
theorem B41479735 : Blo 1917435 41479735 := bstep (se 1 (by rfl) ⟨31109801, by rfl⟩ : syracuseStep 41479735 = 62219603) B62219603
theorem B55306313 : Blo 1917435 55306313 := bstep (se 2 (by rfl) ⟨20739867, by rfl⟩ : syracuseStep 55306313 = 41479735) B41479735
theorem B36870875 : Blo 1917435 36870875 := bstep (se 1 (by rfl) ⟨27653156, by rfl⟩ : syracuseStep 36870875 = 55306313) B55306313
theorem B24580583 : Blo 1917435 24580583 := bstep (se 1 (by rfl) ⟨18435437, by rfl⟩ : syracuseStep 24580583 = 36870875) B36870875
theorem B16387055 : Blo 1917435 16387055 := bstep (se 1 (by rfl) ⟨12290291, by rfl⟩ : syracuseStep 16387055 = 24580583) B24580583
theorem B10924703 : Blo 1917435 10924703 := bstep (se 1 (by rfl) ⟨8193527, by rfl⟩ : syracuseStep 10924703 = 16387055) B16387055
theorem B7283135 : Blo 1917435 7283135 := bstep (se 1 (by rfl) ⟨5462351, by rfl⟩ : syracuseStep 7283135 = 10924703) B10924703
theorem B4855423 : Blo 1917435 4855423 := bstep (se 1 (by rfl) ⟨3641567, by rfl⟩ : syracuseStep 4855423 = 7283135) B7283135
theorem B6473897 : Blo 1917435 6473897 := bstep (se 2 (by rfl) ⟨2427711, by rfl⟩ : syracuseStep 6473897 = 4855423) B4855423
theorem B4315931 : Blo 1917435 4315931 := bstep (se 1 (by rfl) ⟨3236948, by rfl⟩ : syracuseStep 4315931 = 6473897) B6473897
theorem B2877287 : Blo 1917435 2877287 := bstep (se 1 (by rfl) ⟨2157965, by rfl⟩ : syracuseStep 2877287 = 4315931) B4315931
theorem B1918191 : Blo 1917435 1918191 := bstep (se 1 (by rfl) ⟨1438643, by rfl⟩ : syracuseStep 1918191 = 2877287) B2877287
theorem B2877293 : Blo 1917435 2877293 := bbase (se 3 (by rfl) ⟨539492, by rfl⟩ : syracuseStep 2877293 = 1078985) (by norm_num)
theorem B1918195 : Blo 1917435 1918195 := bstep (se 1 (by rfl) ⟨1438646, by rfl⟩ : syracuseStep 1918195 = 2877293) B2877293
theorem B4315949 : Blo 1917435 4315949 := bbase (se 3 (by rfl) ⟨809240, by rfl⟩ : syracuseStep 4315949 = 1618481) (by norm_num)
theorem B2877299 : Blo 1917435 2877299 := bstep (se 1 (by rfl) ⟨2157974, by rfl⟩ : syracuseStep 2877299 = 4315949) B4315949
theorem B1918199 : Blo 1917435 1918199 := bstep (se 1 (by rfl) ⟨1438649, by rfl⟩ : syracuseStep 1918199 = 2877299) B2877299
theorem B2304445 : Blo 1917435 2304445 := bbase (se 3 (by rfl) ⟨432083, by rfl⟩ : syracuseStep 2304445 = 864167) (by norm_num)
theorem B3072593 : Blo 1917435 3072593 := bstep (se 2 (by rfl) ⟨1152222, by rfl⟩ : syracuseStep 3072593 = 2304445) B2304445
theorem B8193581 : Blo 1917435 8193581 := bstep (se 3 (by rfl) ⟨1536296, by rfl⟩ : syracuseStep 8193581 = 3072593) B3072593
theorem B5462387 : Blo 1917435 5462387 := bstep (se 1 (by rfl) ⟨4096790, by rfl⟩ : syracuseStep 5462387 = 8193581) B8193581
theorem B3641591 : Blo 1917435 3641591 := bstep (se 1 (by rfl) ⟨2731193, by rfl⟩ : syracuseStep 3641591 = 5462387) B5462387
theorem B2427727 : Blo 1917435 2427727 := bstep (se 1 (by rfl) ⟨1820795, by rfl⟩ : syracuseStep 2427727 = 3641591) B3641591
theorem B3236969 : Blo 1917435 3236969 := bstep (se 2 (by rfl) ⟨1213863, by rfl⟩ : syracuseStep 3236969 = 2427727) B2427727
theorem B2157979 : Blo 1917435 2157979 := bstep (se 1 (by rfl) ⟨1618484, by rfl⟩ : syracuseStep 2157979 = 3236969) B3236969
theorem B2877305 : Blo 1917435 2877305 := bstep (se 2 (by rfl) ⟨1078989, by rfl⟩ : syracuseStep 2877305 = 2157979) B2157979
theorem B1918203 : Blo 1917435 1918203 := bstep (se 1 (by rfl) ⟨1438652, by rfl⟩ : syracuseStep 1918203 = 2877305) B2877305
theorem B3281141 : Blo 1917435 3281141 := bbase (se 5 (by rfl) ⟨153803, by rfl⟩ : syracuseStep 3281141 = 307607) (by norm_num)
theorem B2187427 : Blo 1917435 2187427 := bstep (se 1 (by rfl) ⟨1640570, by rfl⟩ : syracuseStep 2187427 = 3281141) B3281141
theorem B2916569 : Blo 1917435 2916569 := bstep (se 2 (by rfl) ⟨1093713, by rfl⟩ : syracuseStep 2916569 = 2187427) B2187427
theorem B1944379 : Blo 1917435 1944379 := bstep (se 1 (by rfl) ⟨1458284, by rfl⟩ : syracuseStep 1944379 = 2916569) B2916569
theorem B2592505 : Blo 1917435 2592505 := bstep (se 2 (by rfl) ⟨972189, by rfl⟩ : syracuseStep 2592505 = 1944379) B1944379
theorem B13826693 : Blo 1917435 13826693 := bstep (se 4 (by rfl) ⟨1296252, by rfl⟩ : syracuseStep 13826693 = 2592505) B2592505
theorem B9217795 : Blo 1917435 9217795 := bstep (se 1 (by rfl) ⟨6913346, by rfl⟩ : syracuseStep 9217795 = 13826693) B13826693
theorem B12290393 : Blo 1917435 12290393 := bstep (se 2 (by rfl) ⟨4608897, by rfl⟩ : syracuseStep 12290393 = 9217795) B9217795
theorem B32774381 : Blo 1917435 32774381 := bstep (se 3 (by rfl) ⟨6145196, by rfl⟩ : syracuseStep 32774381 = 12290393) B12290393
theorem B21849587 : Blo 1917435 21849587 := bstep (se 1 (by rfl) ⟨16387190, by rfl⟩ : syracuseStep 21849587 = 32774381) B32774381
theorem B14566391 : Blo 1917435 14566391 := bstep (se 1 (by rfl) ⟨10924793, by rfl⟩ : syracuseStep 14566391 = 21849587) B21849587
theorem B9710927 : Blo 1917435 9710927 := bstep (se 1 (by rfl) ⟨7283195, by rfl⟩ : syracuseStep 9710927 = 14566391) B14566391
theorem B6473951 : Blo 1917435 6473951 := bstep (se 1 (by rfl) ⟨4855463, by rfl⟩ : syracuseStep 6473951 = 9710927) B9710927
theorem B4315967 : Blo 1917435 4315967 := bstep (se 1 (by rfl) ⟨3236975, by rfl⟩ : syracuseStep 4315967 = 6473951) B6473951
theorem B2877311 : Blo 1917435 2877311 := bstep (se 1 (by rfl) ⟨2157983, by rfl⟩ : syracuseStep 2877311 = 4315967) B4315967
theorem B1918207 : Blo 1917435 1918207 := bstep (se 1 (by rfl) ⟨1438655, by rfl⟩ : syracuseStep 1918207 = 2877311) B2877311
theorem B2877317 : Blo 1917435 2877317 := bbase (se 4 (by rfl) ⟨269748, by rfl⟩ : syracuseStep 2877317 = 539497) (by norm_num)
theorem B1918211 : Blo 1917435 1918211 := bstep (se 1 (by rfl) ⟨1438658, by rfl⟩ : syracuseStep 1918211 = 2877317) B2877317
theorem B3236989 : Blo 1917435 3236989 := bbase (se 3 (by rfl) ⟨606935, by rfl⟩ : syracuseStep 3236989 = 1213871) (by norm_num)
theorem B4315985 : Blo 1917435 4315985 := bstep (se 2 (by rfl) ⟨1618494, by rfl⟩ : syracuseStep 4315985 = 3236989) B3236989
theorem B2877323 : Blo 1917435 2877323 := bstep (se 1 (by rfl) ⟨2157992, by rfl⟩ : syracuseStep 2877323 = 4315985) B4315985
theorem B1918215 : Blo 1917435 1918215 := bstep (se 1 (by rfl) ⟨1438661, by rfl⟩ : syracuseStep 1918215 = 2877323) B2877323
theorem B2157997 : Blo 1917435 2157997 := bbase (se 3 (by rfl) ⟨404624, by rfl⟩ : syracuseStep 2157997 = 809249) (by norm_num)
theorem B2877329 : Blo 1917435 2877329 := bstep (se 2 (by rfl) ⟨1078998, by rfl⟩ : syracuseStep 2877329 = 2157997) B2157997
theorem B1918219 : Blo 1917435 1918219 := bstep (se 1 (by rfl) ⟨1438664, by rfl⟩ : syracuseStep 1918219 = 2877329) B2877329
theorem B6474005 : Blo 1917435 6474005 := bbase (se 6 (by rfl) ⟨151734, by rfl⟩ : syracuseStep 6474005 = 303469) (by norm_num)
theorem B4316003 : Blo 1917435 4316003 := bstep (se 1 (by rfl) ⟨3237002, by rfl⟩ : syracuseStep 4316003 = 6474005) B6474005
theorem B2877335 : Blo 1917435 2877335 := bstep (se 1 (by rfl) ⟨2158001, by rfl⟩ : syracuseStep 2877335 = 4316003) B4316003
theorem B1918223 : Blo 1917435 1918223 := bstep (se 1 (by rfl) ⟨1438667, by rfl⟩ : syracuseStep 1918223 = 2877335) B2877335
theorem B2877341 : Blo 1917435 2877341 := bbase (se 3 (by rfl) ⟨539501, by rfl⟩ : syracuseStep 2877341 = 1079003) (by norm_num)
theorem B1918227 : Blo 1917435 1918227 := bstep (se 1 (by rfl) ⟨1438670, by rfl⟩ : syracuseStep 1918227 = 2877341) B2877341
theorem B4316021 : Blo 1917435 4316021 := bbase (se 5 (by rfl) ⟨202313, by rfl⟩ : syracuseStep 4316021 = 404627) (by norm_num)
theorem B2877347 : Blo 1917435 2877347 := bstep (se 1 (by rfl) ⟨2158010, by rfl⟩ : syracuseStep 2877347 = 4316021) B4316021
theorem B1918231 : Blo 1917435 1918231 := bstep (se 1 (by rfl) ⟨1438673, by rfl⟩ : syracuseStep 1918231 = 2877347) B2877347
theorem B2335925 : Blo 1917435 2335925 := bbase (se 5 (by rfl) ⟨109496, by rfl⟩ : syracuseStep 2335925 = 218993) (by norm_num)
theorem B6229133 : Blo 1917435 6229133 := bstep (se 3 (by rfl) ⟨1167962, by rfl⟩ : syracuseStep 6229133 = 2335925) B2335925
theorem B4152755 : Blo 1917435 4152755 := bstep (se 1 (by rfl) ⟨3114566, by rfl⟩ : syracuseStep 4152755 = 6229133) B6229133
theorem B2768503 : Blo 1917435 2768503 := bstep (se 1 (by rfl) ⟨2076377, by rfl⟩ : syracuseStep 2768503 = 4152755) B4152755
theorem B3691337 : Blo 1917435 3691337 := bstep (se 2 (by rfl) ⟨1384251, by rfl⟩ : syracuseStep 3691337 = 2768503) B2768503
theorem B9843565 : Blo 1917435 9843565 := bstep (se 3 (by rfl) ⟨1845668, by rfl⟩ : syracuseStep 9843565 = 3691337) B3691337
theorem B13124753 : Blo 1917435 13124753 := bstep (se 2 (by rfl) ⟨4921782, by rfl⟩ : syracuseStep 13124753 = 9843565) B9843565
theorem B8749835 : Blo 1917435 8749835 := bstep (se 1 (by rfl) ⟨6562376, by rfl⟩ : syracuseStep 8749835 = 13124753) B13124753
theorem B5833223 : Blo 1917435 5833223 := bstep (se 1 (by rfl) ⟨4374917, by rfl⟩ : syracuseStep 5833223 = 8749835) B8749835
theorem B3888815 : Blo 1917435 3888815 := bstep (se 1 (by rfl) ⟨2916611, by rfl⟩ : syracuseStep 3888815 = 5833223) B5833223
theorem B41480693 : Blo 1917435 41480693 := bstep (se 5 (by rfl) ⟨1944407, by rfl⟩ : syracuseStep 41480693 = 3888815) B3888815
theorem B27653795 : Blo 1917435 27653795 := bstep (se 1 (by rfl) ⟨20740346, by rfl⟩ : syracuseStep 27653795 = 41480693) B41480693
theorem B18435863 : Blo 1917435 18435863 := bstep (se 1 (by rfl) ⟨13826897, by rfl⟩ : syracuseStep 18435863 = 27653795) B27653795
theorem B12290575 : Blo 1917435 12290575 := bstep (se 1 (by rfl) ⟨9217931, by rfl⟩ : syracuseStep 12290575 = 18435863) B18435863
theorem B16387433 : Blo 1917435 16387433 := bstep (se 2 (by rfl) ⟨6145287, by rfl⟩ : syracuseStep 16387433 = 12290575) B12290575
theorem B10924955 : Blo 1917435 10924955 := bstep (se 1 (by rfl) ⟨8193716, by rfl⟩ : syracuseStep 10924955 = 16387433) B16387433
theorem B7283303 : Blo 1917435 7283303 := bstep (se 1 (by rfl) ⟨5462477, by rfl⟩ : syracuseStep 7283303 = 10924955) B10924955
theorem B4855535 : Blo 1917435 4855535 := bstep (se 1 (by rfl) ⟨3641651, by rfl⟩ : syracuseStep 4855535 = 7283303) B7283303
theorem B3237023 : Blo 1917435 3237023 := bstep (se 1 (by rfl) ⟨2427767, by rfl⟩ : syracuseStep 3237023 = 4855535) B4855535
theorem B2158015 : Blo 1917435 2158015 := bstep (se 1 (by rfl) ⟨1618511, by rfl⟩ : syracuseStep 2158015 = 3237023) B3237023
theorem B2877353 : Blo 1917435 2877353 := bstep (se 2 (by rfl) ⟨1079007, by rfl⟩ : syracuseStep 2877353 = 2158015) B2158015
theorem B1918235 : Blo 1917435 1918235 := bstep (se 1 (by rfl) ⟨1438676, by rfl⟩ : syracuseStep 1918235 = 2877353) B2877353
theorem B7283317 : Blo 1917435 7283317 := bbase (se 5 (by rfl) ⟨341405, by rfl⟩ : syracuseStep 7283317 = 682811) (by norm_num)
theorem B9711089 : Blo 1917435 9711089 := bstep (se 2 (by rfl) ⟨3641658, by rfl⟩ : syracuseStep 9711089 = 7283317) B7283317
theorem B6474059 : Blo 1917435 6474059 := bstep (se 1 (by rfl) ⟨4855544, by rfl⟩ : syracuseStep 6474059 = 9711089) B9711089
theorem B4316039 : Blo 1917435 4316039 := bstep (se 1 (by rfl) ⟨3237029, by rfl⟩ : syracuseStep 4316039 = 6474059) B6474059
theorem B2877359 : Blo 1917435 2877359 := bstep (se 1 (by rfl) ⟨2158019, by rfl⟩ : syracuseStep 2877359 = 4316039) B4316039
theorem B1918239 : Blo 1917435 1918239 := bstep (se 1 (by rfl) ⟨1438679, by rfl⟩ : syracuseStep 1918239 = 2877359) B2877359
theorem B2877365 : Blo 1917435 2877365 := bbase (se 5 (by rfl) ⟨134876, by rfl⟩ : syracuseStep 2877365 = 269753) (by norm_num)
theorem B1918243 : Blo 1917435 1918243 := bstep (se 1 (by rfl) ⟨1438682, by rfl⟩ : syracuseStep 1918243 = 2877365) B2877365
theorem B4855565 : Blo 1917435 4855565 := bbase (se 3 (by rfl) ⟨910418, by rfl⟩ : syracuseStep 4855565 = 1820837) (by norm_num)
theorem B3237043 : Blo 1917435 3237043 := bstep (se 1 (by rfl) ⟨2427782, by rfl⟩ : syracuseStep 3237043 = 4855565) B4855565
theorem B4316057 : Blo 1917435 4316057 := bstep (se 2 (by rfl) ⟨1618521, by rfl⟩ : syracuseStep 4316057 = 3237043) B3237043
theorem B2877371 : Blo 1917435 2877371 := bstep (se 1 (by rfl) ⟨2158028, by rfl⟩ : syracuseStep 2877371 = 4316057) B4316057
theorem B1918247 : Blo 1917435 1918247 := bstep (se 1 (by rfl) ⟨1438685, by rfl⟩ : syracuseStep 1918247 = 2877371) B2877371
theorem B2158033 : Blo 1917435 2158033 := bbase (se 2 (by rfl) ⟨809262, by rfl⟩ : syracuseStep 2158033 = 1618525) (by norm_num)
theorem B2877377 : Blo 1917435 2877377 := bstep (se 2 (by rfl) ⟨1079016, by rfl⟩ : syracuseStep 2877377 = 2158033) B2158033
theorem B1918251 : Blo 1917435 1918251 := bstep (se 1 (by rfl) ⟨1438688, by rfl⟩ : syracuseStep 1918251 = 2877377) B2877377
theorem B4096901 : Blo 1917435 4096901 := bbase (se 4 (by rfl) ⟨384084, by rfl⟩ : syracuseStep 4096901 = 768169) (by norm_num)
theorem B2731267 : Blo 1917435 2731267 := bstep (se 1 (by rfl) ⟨2048450, by rfl⟩ : syracuseStep 2731267 = 4096901) B4096901
theorem B3641689 : Blo 1917435 3641689 := bstep (se 2 (by rfl) ⟨1365633, by rfl⟩ : syracuseStep 3641689 = 2731267) B2731267
theorem B4855585 : Blo 1917435 4855585 := bstep (se 2 (by rfl) ⟨1820844, by rfl⟩ : syracuseStep 4855585 = 3641689) B3641689
theorem B6474113 : Blo 1917435 6474113 := bstep (se 2 (by rfl) ⟨2427792, by rfl⟩ : syracuseStep 6474113 = 4855585) B4855585
theorem B4316075 : Blo 1917435 4316075 := bstep (se 1 (by rfl) ⟨3237056, by rfl⟩ : syracuseStep 4316075 = 6474113) B6474113
theorem B2877383 : Blo 1917435 2877383 := bstep (se 1 (by rfl) ⟨2158037, by rfl⟩ : syracuseStep 2877383 = 4316075) B4316075
theorem B1918255 : Blo 1917435 1918255 := bstep (se 1 (by rfl) ⟨1438691, by rfl⟩ : syracuseStep 1918255 = 2877383) B2877383
theorem B2877389 : Blo 1917435 2877389 := bbase (se 3 (by rfl) ⟨539510, by rfl⟩ : syracuseStep 2877389 = 1079021) (by norm_num)
theorem B1918259 : Blo 1917435 1918259 := bstep (se 1 (by rfl) ⟨1438694, by rfl⟩ : syracuseStep 1918259 = 2877389) B2877389
theorem B4316093 : Blo 1917435 4316093 := bbase (se 3 (by rfl) ⟨809267, by rfl⟩ : syracuseStep 4316093 = 1618535) (by norm_num)
theorem B2877395 : Blo 1917435 2877395 := bstep (se 1 (by rfl) ⟨2158046, by rfl⟩ : syracuseStep 2877395 = 4316093) B4316093
theorem B1918263 : Blo 1917435 1918263 := bstep (se 1 (by rfl) ⟨1438697, by rfl⟩ : syracuseStep 1918263 = 2877395) B2877395
theorem B3237077 : Blo 1917435 3237077 := bbase (se 7 (by rfl) ⟨37934, by rfl⟩ : syracuseStep 3237077 = 75869) (by norm_num)
theorem B2158051 : Blo 1917435 2158051 := bstep (se 1 (by rfl) ⟨1618538, by rfl⟩ : syracuseStep 2158051 = 3237077) B3237077
theorem B2877401 : Blo 1917435 2877401 := bstep (se 2 (by rfl) ⟨1079025, by rfl⟩ : syracuseStep 2877401 = 2158051) B2158051
theorem B1918267 : Blo 1917435 1918267 := bstep (se 1 (by rfl) ⟨1438700, by rfl⟩ : syracuseStep 1918267 = 2877401) B2877401
theorem B3072701 : Blo 1917435 3072701 := bbase (se 3 (by rfl) ⟨576131, by rfl⟩ : syracuseStep 3072701 = 1152263) (by norm_num)
theorem B8193869 : Blo 1917435 8193869 := bstep (se 3 (by rfl) ⟨1536350, by rfl⟩ : syracuseStep 8193869 = 3072701) B3072701
theorem B5462579 : Blo 1917435 5462579 := bstep (se 1 (by rfl) ⟨4096934, by rfl⟩ : syracuseStep 5462579 = 8193869) B8193869
theorem B14566877 : Blo 1917435 14566877 := bstep (se 3 (by rfl) ⟨2731289, by rfl⟩ : syracuseStep 14566877 = 5462579) B5462579
theorem B9711251 : Blo 1917435 9711251 := bstep (se 1 (by rfl) ⟨7283438, by rfl⟩ : syracuseStep 9711251 = 14566877) B14566877
theorem B6474167 : Blo 1917435 6474167 := bstep (se 1 (by rfl) ⟨4855625, by rfl⟩ : syracuseStep 6474167 = 9711251) B9711251
theorem B4316111 : Blo 1917435 4316111 := bstep (se 1 (by rfl) ⟨3237083, by rfl⟩ : syracuseStep 4316111 = 6474167) B6474167
theorem B2877407 : Blo 1917435 2877407 := bstep (se 1 (by rfl) ⟨2158055, by rfl⟩ : syracuseStep 2877407 = 4316111) B4316111
theorem B1918271 : Blo 1917435 1918271 := bstep (se 1 (by rfl) ⟨1438703, by rfl⟩ : syracuseStep 1918271 = 2877407) B2877407
theorem B2877413 : Blo 1917435 2877413 := bbase (se 4 (by rfl) ⟨269757, by rfl⟩ : syracuseStep 2877413 = 539515) (by norm_num)
theorem B1918275 : Blo 1917435 1918275 := bstep (se 1 (by rfl) ⟨1438706, by rfl⟩ : syracuseStep 1918275 = 2877413) B2877413
theorem B6145429 : Blo 1917435 6145429 := bbase (se 6 (by rfl) ⟨144033, by rfl⟩ : syracuseStep 6145429 = 288067) (by norm_num)
theorem B8193905 : Blo 1917435 8193905 := bstep (se 2 (by rfl) ⟨3072714, by rfl⟩ : syracuseStep 8193905 = 6145429) B6145429
theorem B5462603 : Blo 1917435 5462603 := bstep (se 1 (by rfl) ⟨4096952, by rfl⟩ : syracuseStep 5462603 = 8193905) B8193905
theorem B3641735 : Blo 1917435 3641735 := bstep (se 1 (by rfl) ⟨2731301, by rfl⟩ : syracuseStep 3641735 = 5462603) B5462603
theorem B2427823 : Blo 1917435 2427823 := bstep (se 1 (by rfl) ⟨1820867, by rfl⟩ : syracuseStep 2427823 = 3641735) B3641735
theorem B3237097 : Blo 1917435 3237097 := bstep (se 2 (by rfl) ⟨1213911, by rfl⟩ : syracuseStep 3237097 = 2427823) B2427823
theorem B4316129 : Blo 1917435 4316129 := bstep (se 2 (by rfl) ⟨1618548, by rfl⟩ : syracuseStep 4316129 = 3237097) B3237097
theorem B2877419 : Blo 1917435 2877419 := bstep (se 1 (by rfl) ⟨2158064, by rfl⟩ : syracuseStep 2877419 = 4316129) B4316129
theorem B1918279 : Blo 1917435 1918279 := bstep (se 1 (by rfl) ⟨1438709, by rfl⟩ : syracuseStep 1918279 = 2877419) B2877419
theorem B2158069 : Blo 1917435 2158069 := bbase (se 5 (by rfl) ⟨101159, by rfl⟩ : syracuseStep 2158069 = 202319) (by norm_num)
theorem B2877425 : Blo 1917435 2877425 := bstep (se 2 (by rfl) ⟨1079034, by rfl⟩ : syracuseStep 2877425 = 2158069) B2158069
theorem B1918283 : Blo 1917435 1918283 := bstep (se 1 (by rfl) ⟨1438712, by rfl⟩ : syracuseStep 1918283 = 2877425) B2877425
theorem B2427833 : Blo 1917435 2427833 := bbase (se 2 (by rfl) ⟨910437, by rfl⟩ : syracuseStep 2427833 = 1820875) (by norm_num)
theorem B6474221 : Blo 1917435 6474221 := bstep (se 3 (by rfl) ⟨1213916, by rfl⟩ : syracuseStep 6474221 = 2427833) B2427833
theorem B4316147 : Blo 1917435 4316147 := bstep (se 1 (by rfl) ⟨3237110, by rfl⟩ : syracuseStep 4316147 = 6474221) B6474221
theorem B2877431 : Blo 1917435 2877431 := bstep (se 1 (by rfl) ⟨2158073, by rfl⟩ : syracuseStep 2877431 = 4316147) B4316147
theorem B1918287 : Blo 1917435 1918287 := bstep (se 1 (by rfl) ⟨1438715, by rfl⟩ : syracuseStep 1918287 = 2877431) B2877431
theorem B2877437 : Blo 1917435 2877437 := bbase (se 3 (by rfl) ⟨539519, by rfl⟩ : syracuseStep 2877437 = 1079039) (by norm_num)
theorem B1918291 : Blo 1917435 1918291 := bstep (se 1 (by rfl) ⟨1438718, by rfl⟩ : syracuseStep 1918291 = 2877437) B2877437
theorem B4316165 : Blo 1917435 4316165 := bbase (se 4 (by rfl) ⟨404640, by rfl⟩ : syracuseStep 4316165 = 809281) (by norm_num)
theorem B2877443 : Blo 1917435 2877443 := bstep (se 1 (by rfl) ⟨2158082, by rfl⟩ : syracuseStep 2877443 = 4316165) B4316165
theorem B1918295 : Blo 1917435 1918295 := bstep (se 1 (by rfl) ⟨1438721, by rfl⟩ : syracuseStep 1918295 = 2877443) B2877443
theorem B3641773 : Blo 1917435 3641773 := bbase (se 3 (by rfl) ⟨682832, by rfl⟩ : syracuseStep 3641773 = 1365665) (by norm_num)
theorem B4855697 : Blo 1917435 4855697 := bstep (se 2 (by rfl) ⟨1820886, by rfl⟩ : syracuseStep 4855697 = 3641773) B3641773
theorem B3237131 : Blo 1917435 3237131 := bstep (se 1 (by rfl) ⟨2427848, by rfl⟩ : syracuseStep 3237131 = 4855697) B4855697
theorem B2158087 : Blo 1917435 2158087 := bstep (se 1 (by rfl) ⟨1618565, by rfl⟩ : syracuseStep 2158087 = 3237131) B3237131
theorem B2877449 : Blo 1917435 2877449 := bstep (se 2 (by rfl) ⟨1079043, by rfl⟩ : syracuseStep 2877449 = 2158087) B2158087
theorem B1918299 : Blo 1917435 1918299 := bstep (se 1 (by rfl) ⟨1438724, by rfl⟩ : syracuseStep 1918299 = 2877449) B2877449
theorem B9711413 : Blo 1917435 9711413 := bbase (se 5 (by rfl) ⟨455222, by rfl⟩ : syracuseStep 9711413 = 910445) (by norm_num)
theorem B6474275 : Blo 1917435 6474275 := bstep (se 1 (by rfl) ⟨4855706, by rfl⟩ : syracuseStep 6474275 = 9711413) B9711413
theorem B4316183 : Blo 1917435 4316183 := bstep (se 1 (by rfl) ⟨3237137, by rfl⟩ : syracuseStep 4316183 = 6474275) B6474275
theorem B2877455 : Blo 1917435 2877455 := bstep (se 1 (by rfl) ⟨2158091, by rfl⟩ : syracuseStep 2877455 = 4316183) B4316183
theorem B1918303 : Blo 1917435 1918303 := bstep (se 1 (by rfl) ⟨1438727, by rfl⟩ : syracuseStep 1918303 = 2877455) B2877455
theorem B2877461 : Blo 1917435 2877461 := bbase (se 6 (by rfl) ⟨67440, by rfl⟩ : syracuseStep 2877461 = 134881) (by norm_num)
theorem B1918307 : Blo 1917435 1918307 := bstep (se 1 (by rfl) ⟨1438730, by rfl⟩ : syracuseStep 1918307 = 2877461) B2877461
theorem B12291061 : Blo 1917435 12291061 := bbase (se 5 (by rfl) ⟨576143, by rfl⟩ : syracuseStep 12291061 = 1152287) (by norm_num)
theorem B16388081 : Blo 1917435 16388081 := bstep (se 2 (by rfl) ⟨6145530, by rfl⟩ : syracuseStep 16388081 = 12291061) B12291061
theorem B10925387 : Blo 1917435 10925387 := bstep (se 1 (by rfl) ⟨8194040, by rfl⟩ : syracuseStep 10925387 = 16388081) B16388081
theorem B7283591 : Blo 1917435 7283591 := bstep (se 1 (by rfl) ⟨5462693, by rfl⟩ : syracuseStep 7283591 = 10925387) B10925387
theorem B4855727 : Blo 1917435 4855727 := bstep (se 1 (by rfl) ⟨3641795, by rfl⟩ : syracuseStep 4855727 = 7283591) B7283591
theorem B3237151 : Blo 1917435 3237151 := bstep (se 1 (by rfl) ⟨2427863, by rfl⟩ : syracuseStep 3237151 = 4855727) B4855727
theorem B4316201 : Blo 1917435 4316201 := bstep (se 2 (by rfl) ⟨1618575, by rfl⟩ : syracuseStep 4316201 = 3237151) B3237151
theorem B2877467 : Blo 1917435 2877467 := bstep (se 1 (by rfl) ⟨2158100, by rfl⟩ : syracuseStep 2877467 = 4316201) B4316201
theorem B1918311 : Blo 1917435 1918311 := bstep (se 1 (by rfl) ⟨1438733, by rfl⟩ : syracuseStep 1918311 = 2877467) B2877467
theorem B2158105 : Blo 1917435 2158105 := bbase (se 2 (by rfl) ⟨809289, by rfl⟩ : syracuseStep 2158105 = 1618579) (by norm_num)
theorem B2877473 : Blo 1917435 2877473 := bstep (se 2 (by rfl) ⟨1079052, by rfl⟩ : syracuseStep 2877473 = 2158105) B2158105
theorem B1918315 : Blo 1917435 1918315 := bstep (se 1 (by rfl) ⟨1438736, by rfl⟩ : syracuseStep 1918315 = 2877473) B2877473
theorem B7283621 : Blo 1917435 7283621 := bbase (se 4 (by rfl) ⟨682839, by rfl⟩ : syracuseStep 7283621 = 1365679) (by norm_num)
theorem B4855747 : Blo 1917435 4855747 := bstep (se 1 (by rfl) ⟨3641810, by rfl⟩ : syracuseStep 4855747 = 7283621) B7283621
theorem B6474329 : Blo 1917435 6474329 := bstep (se 2 (by rfl) ⟨2427873, by rfl⟩ : syracuseStep 6474329 = 4855747) B4855747
theorem B4316219 : Blo 1917435 4316219 := bstep (se 1 (by rfl) ⟨3237164, by rfl⟩ : syracuseStep 4316219 = 6474329) B6474329
theorem B2877479 : Blo 1917435 2877479 := bstep (se 1 (by rfl) ⟨2158109, by rfl⟩ : syracuseStep 2877479 = 4316219) B4316219
theorem B1918319 : Blo 1917435 1918319 := bstep (se 1 (by rfl) ⟨1438739, by rfl⟩ : syracuseStep 1918319 = 2877479) B2877479
theorem B2877485 : Blo 1917435 2877485 := bbase (se 3 (by rfl) ⟨539528, by rfl⟩ : syracuseStep 2877485 = 1079057) (by norm_num)
theorem B1918323 : Blo 1917435 1918323 := bstep (se 1 (by rfl) ⟨1438742, by rfl⟩ : syracuseStep 1918323 = 2877485) B2877485
theorem B4316237 : Blo 1917435 4316237 := bbase (se 3 (by rfl) ⟨809294, by rfl⟩ : syracuseStep 4316237 = 1618589) (by norm_num)
theorem B2877491 : Blo 1917435 2877491 := bstep (se 1 (by rfl) ⟨2158118, by rfl⟩ : syracuseStep 2877491 = 4316237) B4316237
theorem B1918327 : Blo 1917435 1918327 := bstep (se 1 (by rfl) ⟨1438745, by rfl⟩ : syracuseStep 1918327 = 2877491) B2877491
theorem B2427889 : Blo 1917435 2427889 := bbase (se 2 (by rfl) ⟨910458, by rfl⟩ : syracuseStep 2427889 = 1820917) (by norm_num)
theorem B3237185 : Blo 1917435 3237185 := bstep (se 2 (by rfl) ⟨1213944, by rfl⟩ : syracuseStep 3237185 = 2427889) B2427889
theorem B2158123 : Blo 1917435 2158123 := bstep (se 1 (by rfl) ⟨1618592, by rfl⟩ : syracuseStep 2158123 = 3237185) B3237185
theorem B2877497 : Blo 1917435 2877497 := bstep (se 2 (by rfl) ⟨1079061, by rfl⟩ : syracuseStep 2877497 = 2158123) B2158123
theorem B1918331 : Blo 1917435 1918331 := bstep (se 1 (by rfl) ⟨1438748, by rfl⟩ : syracuseStep 1918331 = 2877497) B2877497
theorem B4672093 : Blo 1917435 4672093 := bbase (se 3 (by rfl) ⟨876017, by rfl⟩ : syracuseStep 4672093 = 1752035) (by norm_num)
theorem B6229457 : Blo 1917435 6229457 := bstep (se 2 (by rfl) ⟨2336046, by rfl⟩ : syracuseStep 6229457 = 4672093) B4672093
theorem B4152971 : Blo 1917435 4152971 := bstep (se 1 (by rfl) ⟨3114728, by rfl⟩ : syracuseStep 4152971 = 6229457) B6229457
theorem B11074589 : Blo 1917435 11074589 := bstep (se 3 (by rfl) ⟨2076485, by rfl⟩ : syracuseStep 11074589 = 4152971) B4152971
theorem B7383059 : Blo 1917435 7383059 := bstep (se 1 (by rfl) ⟨5537294, by rfl⟩ : syracuseStep 7383059 = 11074589) B11074589
theorem B4922039 : Blo 1917435 4922039 := bstep (se 1 (by rfl) ⟨3691529, by rfl⟩ : syracuseStep 4922039 = 7383059) B7383059
theorem B3281359 : Blo 1917435 3281359 := bstep (se 1 (by rfl) ⟨2461019, by rfl⟩ : syracuseStep 3281359 = 4922039) B4922039
theorem B4375145 : Blo 1917435 4375145 := bstep (se 2 (by rfl) ⟨1640679, by rfl⟩ : syracuseStep 4375145 = 3281359) B3281359
theorem B11667053 : Blo 1917435 11667053 := bstep (se 3 (by rfl) ⟨2187572, by rfl⟩ : syracuseStep 11667053 = 4375145) B4375145
theorem B7778035 : Blo 1917435 7778035 := bstep (se 1 (by rfl) ⟨5833526, by rfl⟩ : syracuseStep 7778035 = 11667053) B11667053
theorem B10370713 : Blo 1917435 10370713 := bstep (se 2 (by rfl) ⟨3889017, by rfl⟩ : syracuseStep 10370713 = 7778035) B7778035
theorem B13827617 : Blo 1917435 13827617 := bstep (se 2 (by rfl) ⟨5185356, by rfl⟩ : syracuseStep 13827617 = 10370713) B10370713
theorem B9218411 : Blo 1917435 9218411 := bstep (se 1 (by rfl) ⟨6913808, by rfl⟩ : syracuseStep 9218411 = 13827617) B13827617
theorem B6145607 : Blo 1917435 6145607 := bstep (se 1 (by rfl) ⟨4609205, by rfl⟩ : syracuseStep 6145607 = 9218411) B9218411
theorem B4097071 : Blo 1917435 4097071 := bstep (se 1 (by rfl) ⟨3072803, by rfl⟩ : syracuseStep 4097071 = 6145607) B6145607
theorem B21851045 : Blo 1917435 21851045 := bstep (se 4 (by rfl) ⟨2048535, by rfl⟩ : syracuseStep 21851045 = 4097071) B4097071
theorem B14567363 : Blo 1917435 14567363 := bstep (se 1 (by rfl) ⟨10925522, by rfl⟩ : syracuseStep 14567363 = 21851045) B21851045
theorem B9711575 : Blo 1917435 9711575 := bstep (se 1 (by rfl) ⟨7283681, by rfl⟩ : syracuseStep 9711575 = 14567363) B14567363
theorem B6474383 : Blo 1917435 6474383 := bstep (se 1 (by rfl) ⟨4855787, by rfl⟩ : syracuseStep 6474383 = 9711575) B9711575
theorem B4316255 : Blo 1917435 4316255 := bstep (se 1 (by rfl) ⟨3237191, by rfl⟩ : syracuseStep 4316255 = 6474383) B6474383
theorem B2877503 : Blo 1917435 2877503 := bstep (se 1 (by rfl) ⟨2158127, by rfl⟩ : syracuseStep 2877503 = 4316255) B4316255
theorem B1918335 : Blo 1917435 1918335 := bstep (se 1 (by rfl) ⟨1438751, by rfl⟩ : syracuseStep 1918335 = 2877503) B2877503
theorem B2877509 : Blo 1917435 2877509 := bbase (se 4 (by rfl) ⟨269766, by rfl⟩ : syracuseStep 2877509 = 539533) (by norm_num)
theorem B1918339 : Blo 1917435 1918339 := bstep (se 1 (by rfl) ⟨1438754, by rfl⟩ : syracuseStep 1918339 = 2877509) B2877509
theorem B3237205 : Blo 1917435 3237205 := bbase (se 12 (by rfl) ⟨1185, by rfl⟩ : syracuseStep 3237205 = 2371) (by norm_num)
theorem B4316273 : Blo 1917435 4316273 := bstep (se 2 (by rfl) ⟨1618602, by rfl⟩ : syracuseStep 4316273 = 3237205) B3237205
theorem B2877515 : Blo 1917435 2877515 := bstep (se 1 (by rfl) ⟨2158136, by rfl⟩ : syracuseStep 2877515 = 4316273) B4316273
theorem B1918343 : Blo 1917435 1918343 := bstep (se 1 (by rfl) ⟨1438757, by rfl⟩ : syracuseStep 1918343 = 2877515) B2877515
theorem B2158141 : Blo 1917435 2158141 := bbase (se 3 (by rfl) ⟨404651, by rfl⟩ : syracuseStep 2158141 = 809303) (by norm_num)
theorem B2877521 : Blo 1917435 2877521 := bstep (se 2 (by rfl) ⟨1079070, by rfl⟩ : syracuseStep 2877521 = 2158141) B2158141
theorem B1918347 : Blo 1917435 1918347 := bstep (se 1 (by rfl) ⟨1438760, by rfl⟩ : syracuseStep 1918347 = 2877521) B2877521
theorem B6474437 : Blo 1917435 6474437 := bbase (se 4 (by rfl) ⟨606978, by rfl⟩ : syracuseStep 6474437 = 1213957) (by norm_num)
theorem B4316291 : Blo 1917435 4316291 := bstep (se 1 (by rfl) ⟨3237218, by rfl⟩ : syracuseStep 4316291 = 6474437) B6474437
theorem B2877527 : Blo 1917435 2877527 := bstep (se 1 (by rfl) ⟨2158145, by rfl⟩ : syracuseStep 2877527 = 4316291) B4316291
theorem B1918351 : Blo 1917435 1918351 := bstep (se 1 (by rfl) ⟨1438763, by rfl⟩ : syracuseStep 1918351 = 2877527) B2877527
theorem B2877533 : Blo 1917435 2877533 := bbase (se 3 (by rfl) ⟨539537, by rfl⟩ : syracuseStep 2877533 = 1079075) (by norm_num)
theorem B1918355 : Blo 1917435 1918355 := bstep (se 1 (by rfl) ⟨1438766, by rfl⟩ : syracuseStep 1918355 = 2877533) B2877533
theorem B4316309 : Blo 1917435 4316309 := bbase (se 6 (by rfl) ⟨101163, by rfl⟩ : syracuseStep 4316309 = 202327) (by norm_num)
theorem B2877539 : Blo 1917435 2877539 := bstep (se 1 (by rfl) ⟨2158154, by rfl⟩ : syracuseStep 2877539 = 4316309) B4316309
theorem B1918359 : Blo 1917435 1918359 := bstep (se 1 (by rfl) ⟨1438769, by rfl⟩ : syracuseStep 1918359 = 2877539) B2877539
theorem B2731421 : Blo 1917435 2731421 := bbase (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) (by norm_num)
theorem B7283789 : Blo 1917435 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B4855859 : Blo 1917435 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B3237239 : Blo 1917435 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B2158159 : Blo 1917435 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B2877545 : Blo 1917435 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B1918363 : Blo 1917435 1918363 := bstep (se 1 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 1918363 = 2877545) B2877545
theorem B13125653 : Blo 1917435 13125653 := bbase (se 6 (by rfl) ⟨307632, by rfl⟩ : syracuseStep 13125653 = 615265) (by norm_num)
theorem B8750435 : Blo 1917435 8750435 := bstep (se 1 (by rfl) ⟨6562826, by rfl⟩ : syracuseStep 8750435 = 13125653) B13125653
theorem B23334493 : Blo 1917435 23334493 := bstep (se 3 (by rfl) ⟨4375217, by rfl⟩ : syracuseStep 23334493 = 8750435) B8750435
theorem B31112657 : Blo 1917435 31112657 := bstep (se 2 (by rfl) ⟨11667246, by rfl⟩ : syracuseStep 31112657 = 23334493) B23334493
theorem B20741771 : Blo 1917435 20741771 := bstep (se 1 (by rfl) ⟨15556328, by rfl⟩ : syracuseStep 20741771 = 31112657) B31112657
theorem B13827847 : Blo 1917435 13827847 := bstep (se 1 (by rfl) ⟨10370885, by rfl⟩ : syracuseStep 13827847 = 20741771) B20741771
theorem B18437129 : Blo 1917435 18437129 := bstep (se 2 (by rfl) ⟨6913923, by rfl⟩ : syracuseStep 18437129 = 13827847) B13827847
theorem B12291419 : Blo 1917435 12291419 := bstep (se 1 (by rfl) ⟨9218564, by rfl⟩ : syracuseStep 12291419 = 18437129) B18437129
theorem B8194279 : Blo 1917435 8194279 := bstep (se 1 (by rfl) ⟨6145709, by rfl⟩ : syracuseStep 8194279 = 12291419) B12291419
theorem B10925705 : Blo 1917435 10925705 := bstep (se 2 (by rfl) ⟨4097139, by rfl⟩ : syracuseStep 10925705 = 8194279) B8194279
theorem B7283803 : Blo 1917435 7283803 := bstep (se 1 (by rfl) ⟨5462852, by rfl⟩ : syracuseStep 7283803 = 10925705) B10925705
theorem B9711737 : Blo 1917435 9711737 := bstep (se 2 (by rfl) ⟨3641901, by rfl⟩ : syracuseStep 9711737 = 7283803) B7283803
theorem B6474491 : Blo 1917435 6474491 := bstep (se 1 (by rfl) ⟨4855868, by rfl⟩ : syracuseStep 6474491 = 9711737) B9711737
theorem B4316327 : Blo 1917435 4316327 := bstep (se 1 (by rfl) ⟨3237245, by rfl⟩ : syracuseStep 4316327 = 6474491) B6474491
theorem B2877551 : Blo 1917435 2877551 := bstep (se 1 (by rfl) ⟨2158163, by rfl⟩ : syracuseStep 2877551 = 4316327) B4316327
theorem B1918367 : Blo 1917435 1918367 := bstep (se 1 (by rfl) ⟨1438775, by rfl⟩ : syracuseStep 1918367 = 2877551) B2877551
theorem B2877557 : Blo 1917435 2877557 := bbase (se 5 (by rfl) ⟨134885, by rfl⟩ : syracuseStep 2877557 = 269771) (by norm_num)
theorem B1918371 : Blo 1917435 1918371 := bstep (se 1 (by rfl) ⟨1438778, by rfl⟩ : syracuseStep 1918371 = 2877557) B2877557
theorem B3641917 : Blo 1917435 3641917 := bbase (se 3 (by rfl) ⟨682859, by rfl⟩ : syracuseStep 3641917 = 1365719) (by norm_num)
theorem B4855889 : Blo 1917435 4855889 := bstep (se 2 (by rfl) ⟨1820958, by rfl⟩ : syracuseStep 4855889 = 3641917) B3641917
theorem B3237259 : Blo 1917435 3237259 := bstep (se 1 (by rfl) ⟨2427944, by rfl⟩ : syracuseStep 3237259 = 4855889) B4855889
theorem B4316345 : Blo 1917435 4316345 := bstep (se 2 (by rfl) ⟨1618629, by rfl⟩ : syracuseStep 4316345 = 3237259) B3237259
theorem B2877563 : Blo 1917435 2877563 := bstep (se 1 (by rfl) ⟨2158172, by rfl⟩ : syracuseStep 2877563 = 4316345) B4316345
theorem B1918375 : Blo 1917435 1918375 := bstep (se 1 (by rfl) ⟨1438781, by rfl⟩ : syracuseStep 1918375 = 2877563) B2877563
theorem B2158177 : Blo 1917435 2158177 := bbase (se 2 (by rfl) ⟨809316, by rfl⟩ : syracuseStep 2158177 = 1618633) (by norm_num)
theorem B2877569 : Blo 1917435 2877569 := bstep (se 2 (by rfl) ⟨1079088, by rfl⟩ : syracuseStep 2877569 = 2158177) B2158177
theorem B1918379 : Blo 1917435 1918379 := bstep (se 1 (by rfl) ⟨1438784, by rfl⟩ : syracuseStep 1918379 = 2877569) B2877569
theorem B4855909 : Blo 1917435 4855909 := bbase (se 4 (by rfl) ⟨455241, by rfl⟩ : syracuseStep 4855909 = 910483) (by norm_num)
theorem B6474545 : Blo 1917435 6474545 := bstep (se 2 (by rfl) ⟨2427954, by rfl⟩ : syracuseStep 6474545 = 4855909) B4855909
theorem B4316363 : Blo 1917435 4316363 := bstep (se 1 (by rfl) ⟨3237272, by rfl⟩ : syracuseStep 4316363 = 6474545) B6474545
theorem B2877575 : Blo 1917435 2877575 := bstep (se 1 (by rfl) ⟨2158181, by rfl⟩ : syracuseStep 2877575 = 4316363) B4316363
theorem B1918383 : Blo 1917435 1918383 := bstep (se 1 (by rfl) ⟨1438787, by rfl⟩ : syracuseStep 1918383 = 2877575) B2877575
theorem B2877581 : Blo 1917435 2877581 := bbase (se 3 (by rfl) ⟨539546, by rfl⟩ : syracuseStep 2877581 = 1079093) (by norm_num)
theorem B1918387 : Blo 1917435 1918387 := bstep (se 1 (by rfl) ⟨1438790, by rfl⟩ : syracuseStep 1918387 = 2877581) B2877581
theorem B4316381 : Blo 1917435 4316381 := bbase (se 3 (by rfl) ⟨809321, by rfl⟩ : syracuseStep 4316381 = 1618643) (by norm_num)
theorem B2877587 : Blo 1917435 2877587 := bstep (se 1 (by rfl) ⟨2158190, by rfl⟩ : syracuseStep 2877587 = 4316381) B4316381
theorem B1918391 : Blo 1917435 1918391 := bstep (se 1 (by rfl) ⟨1438793, by rfl⟩ : syracuseStep 1918391 = 2877587) B2877587
theorem B3237293 : Blo 1917435 3237293 := bbase (se 3 (by rfl) ⟨606992, by rfl⟩ : syracuseStep 3237293 = 1213985) (by norm_num)
theorem B2158195 : Blo 1917435 2158195 := bstep (se 1 (by rfl) ⟨1618646, by rfl⟩ : syracuseStep 2158195 = 3237293) B3237293
theorem B2877593 : Blo 1917435 2877593 := bstep (se 2 (by rfl) ⟨1079097, by rfl⟩ : syracuseStep 2877593 = 2158195) B2158195
theorem B1918395 : Blo 1917435 1918395 := bstep (se 1 (by rfl) ⟨1438796, by rfl⟩ : syracuseStep 1918395 = 2877593) B2877593
theorem B31113173 : Blo 1917435 31113173 := bbase (se 7 (by rfl) ⟨364607, by rfl⟩ : syracuseStep 31113173 = 729215) (by norm_num)
theorem B82968461 : Blo 1917435 82968461 := bstep (se 3 (by rfl) ⟨15556586, by rfl⟩ : syracuseStep 82968461 = 31113173) B31113173
theorem B55312307 : Blo 1917435 55312307 := bstep (se 1 (by rfl) ⟨41484230, by rfl⟩ : syracuseStep 55312307 = 82968461) B82968461
theorem B36874871 : Blo 1917435 36874871 := bstep (se 1 (by rfl) ⟨27656153, by rfl⟩ : syracuseStep 36874871 = 55312307) B55312307
theorem B24583247 : Blo 1917435 24583247 := bstep (se 1 (by rfl) ⟨18437435, by rfl⟩ : syracuseStep 24583247 = 36874871) B36874871
theorem B16388831 : Blo 1917435 16388831 := bstep (se 1 (by rfl) ⟨12291623, by rfl⟩ : syracuseStep 16388831 = 24583247) B24583247
theorem B10925887 : Blo 1917435 10925887 := bstep (se 1 (by rfl) ⟨8194415, by rfl⟩ : syracuseStep 10925887 = 16388831) B16388831
theorem B14567849 : Blo 1917435 14567849 := bstep (se 2 (by rfl) ⟨5462943, by rfl⟩ : syracuseStep 14567849 = 10925887) B10925887
theorem B9711899 : Blo 1917435 9711899 := bstep (se 1 (by rfl) ⟨7283924, by rfl⟩ : syracuseStep 9711899 = 14567849) B14567849
theorem B6474599 : Blo 1917435 6474599 := bstep (se 1 (by rfl) ⟨4855949, by rfl⟩ : syracuseStep 6474599 = 9711899) B9711899
theorem B4316399 : Blo 1917435 4316399 := bstep (se 1 (by rfl) ⟨3237299, by rfl⟩ : syracuseStep 4316399 = 6474599) B6474599
theorem B2877599 : Blo 1917435 2877599 := bstep (se 1 (by rfl) ⟨2158199, by rfl⟩ : syracuseStep 2877599 = 4316399) B4316399
theorem B1918399 : Blo 1917435 1918399 := bstep (se 1 (by rfl) ⟨1438799, by rfl⟩ : syracuseStep 1918399 = 2877599) B2877599
theorem B2877605 : Blo 1917435 2877605 := bbase (se 4 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 2877605 = 539551) (by norm_num)
theorem B1918403 : Blo 1917435 1918403 := bstep (se 1 (by rfl) ⟨1438802, by rfl⟩ : syracuseStep 1918403 = 2877605) B2877605
theorem B2427985 : Blo 1917435 2427985 := bbase (se 2 (by rfl) ⟨910494, by rfl⟩ : syracuseStep 2427985 = 1820989) (by norm_num)
theorem B3237313 : Blo 1917435 3237313 := bstep (se 2 (by rfl) ⟨1213992, by rfl⟩ : syracuseStep 3237313 = 2427985) B2427985
theorem B4316417 : Blo 1917435 4316417 := bstep (se 2 (by rfl) ⟨1618656, by rfl⟩ : syracuseStep 4316417 = 3237313) B3237313
theorem B2877611 : Blo 1917435 2877611 := bstep (se 1 (by rfl) ⟨2158208, by rfl⟩ : syracuseStep 2877611 = 4316417) B4316417
theorem B1918407 : Blo 1917435 1918407 := bstep (se 1 (by rfl) ⟨1438805, by rfl⟩ : syracuseStep 1918407 = 2877611) B2877611
theorem B2158213 : Blo 1917435 2158213 := bbase (se 4 (by rfl) ⟨202332, by rfl⟩ : syracuseStep 2158213 = 404665) (by norm_num)
theorem B2877617 : Blo 1917435 2877617 := bstep (se 2 (by rfl) ⟨1079106, by rfl⟩ : syracuseStep 2877617 = 2158213) B2158213
theorem B1918411 : Blo 1917435 1918411 := bstep (se 1 (by rfl) ⟨1438808, by rfl⟩ : syracuseStep 1918411 = 2877617) B2877617
theorem B3889181 : Blo 1917435 3889181 := bbase (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) (by norm_num)
theorem B10371149 : Blo 1917435 10371149 := bstep (se 3 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 10371149 = 3889181) B3889181
theorem B6914099 : Blo 1917435 6914099 := bstep (se 1 (by rfl) ⟨5185574, by rfl⟩ : syracuseStep 6914099 = 10371149) B10371149
theorem B4609399 : Blo 1917435 4609399 := bstep (se 1 (by rfl) ⟨3457049, by rfl⟩ : syracuseStep 4609399 = 6914099) B6914099
theorem B6145865 : Blo 1917435 6145865 := bstep (se 2 (by rfl) ⟨2304699, by rfl⟩ : syracuseStep 6145865 = 4609399) B4609399
theorem B4097243 : Blo 1917435 4097243 := bstep (se 1 (by rfl) ⟨3072932, by rfl⟩ : syracuseStep 4097243 = 6145865) B6145865
theorem B2731495 : Blo 1917435 2731495 := bstep (se 1 (by rfl) ⟨2048621, by rfl⟩ : syracuseStep 2731495 = 4097243) B4097243
theorem B3641993 : Blo 1917435 3641993 := bstep (se 2 (by rfl) ⟨1365747, by rfl⟩ : syracuseStep 3641993 = 2731495) B2731495
theorem B2427995 : Blo 1917435 2427995 := bstep (se 1 (by rfl) ⟨1820996, by rfl⟩ : syracuseStep 2427995 = 3641993) B3641993
theorem B6474653 : Blo 1917435 6474653 := bstep (se 3 (by rfl) ⟨1213997, by rfl⟩ : syracuseStep 6474653 = 2427995) B2427995
theorem B4316435 : Blo 1917435 4316435 := bstep (se 1 (by rfl) ⟨3237326, by rfl⟩ : syracuseStep 4316435 = 6474653) B6474653
theorem B2877623 : Blo 1917435 2877623 := bstep (se 1 (by rfl) ⟨2158217, by rfl⟩ : syracuseStep 2877623 = 4316435) B4316435
theorem B1918415 : Blo 1917435 1918415 := bstep (se 1 (by rfl) ⟨1438811, by rfl⟩ : syracuseStep 1918415 = 2877623) B2877623
theorem B2877629 : Blo 1917435 2877629 := bbase (se 3 (by rfl) ⟨539555, by rfl⟩ : syracuseStep 2877629 = 1079111) (by norm_num)
theorem B1918419 : Blo 1917435 1918419 := bstep (se 1 (by rfl) ⟨1438814, by rfl⟩ : syracuseStep 1918419 = 2877629) B2877629
theorem B4316453 : Blo 1917435 4316453 := bbase (se 4 (by rfl) ⟨404667, by rfl⟩ : syracuseStep 4316453 = 809335) (by norm_num)
theorem B2877635 : Blo 1917435 2877635 := bstep (se 1 (by rfl) ⟨2158226, by rfl⟩ : syracuseStep 2877635 = 4316453) B4316453
theorem B1918423 : Blo 1917435 1918423 := bstep (se 1 (by rfl) ⟨1438817, by rfl⟩ : syracuseStep 1918423 = 2877635) B2877635
theorem B4856021 : Blo 1917435 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B3237347 : Blo 1917435 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B2158231 : Blo 1917435 2158231 := bstep (se 1 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 2158231 = 3237347) B3237347
theorem B2877641 : Blo 1917435 2877641 := bstep (se 2 (by rfl) ⟨1079115, by rfl⟩ : syracuseStep 2877641 = 2158231) B2158231
theorem B1918427 : Blo 1917435 1918427 := bstep (se 1 (by rfl) ⟨1438820, by rfl⟩ : syracuseStep 1918427 = 2877641) B2877641
theorem B7484165 : Blo 1917435 7484165 := bbase (se 4 (by rfl) ⟨701640, by rfl⟩ : syracuseStep 7484165 = 1403281) (by norm_num)
theorem B4989443 : Blo 1917435 4989443 := bstep (se 1 (by rfl) ⟨3742082, by rfl⟩ : syracuseStep 4989443 = 7484165) B7484165
theorem B13305181 : Blo 1917435 13305181 := bstep (se 3 (by rfl) ⟨2494721, by rfl⟩ : syracuseStep 13305181 = 4989443) B4989443
theorem B17740241 : Blo 1917435 17740241 := bstep (se 2 (by rfl) ⟨6652590, by rfl⟩ : syracuseStep 17740241 = 13305181) B13305181
theorem B11826827 : Blo 1917435 11826827 := bstep (se 1 (by rfl) ⟨8870120, by rfl⟩ : syracuseStep 11826827 = 17740241) B17740241
theorem B7884551 : Blo 1917435 7884551 := bstep (se 1 (by rfl) ⟨5913413, by rfl⟩ : syracuseStep 7884551 = 11826827) B11826827
theorem B21025469 : Blo 1917435 21025469 := bstep (se 3 (by rfl) ⟨3942275, by rfl⟩ : syracuseStep 21025469 = 7884551) B7884551
theorem B14016979 : Blo 1917435 14016979 := bstep (se 1 (by rfl) ⟨10512734, by rfl⟩ : syracuseStep 14016979 = 21025469) B21025469
theorem B18689305 : Blo 1917435 18689305 := bstep (se 2 (by rfl) ⟨7008489, by rfl⟩ : syracuseStep 18689305 = 14016979) B14016979
theorem B24919073 : Blo 1917435 24919073 := bstep (se 2 (by rfl) ⟨9344652, by rfl⟩ : syracuseStep 24919073 = 18689305) B18689305
theorem B16612715 : Blo 1917435 16612715 := bstep (se 1 (by rfl) ⟨12459536, by rfl⟩ : syracuseStep 16612715 = 24919073) B24919073
theorem B11075143 : Blo 1917435 11075143 := bstep (se 1 (by rfl) ⟨8306357, by rfl⟩ : syracuseStep 11075143 = 16612715) B16612715
theorem B14766857 : Blo 1917435 14766857 := bstep (se 2 (by rfl) ⟨5537571, by rfl⟩ : syracuseStep 14766857 = 11075143) B11075143
theorem B9844571 : Blo 1917435 9844571 := bstep (se 1 (by rfl) ⟨7383428, by rfl⟩ : syracuseStep 9844571 = 14766857) B14766857
theorem B6563047 : Blo 1917435 6563047 := bstep (se 1 (by rfl) ⟨4922285, by rfl⟩ : syracuseStep 6563047 = 9844571) B9844571
theorem B8750729 : Blo 1917435 8750729 := bstep (se 2 (by rfl) ⟨3281523, by rfl⟩ : syracuseStep 8750729 = 6563047) B6563047
theorem B5833819 : Blo 1917435 5833819 := bstep (se 1 (by rfl) ⟨4375364, by rfl⟩ : syracuseStep 5833819 = 8750729) B8750729
theorem B7778425 : Blo 1917435 7778425 := bstep (se 2 (by rfl) ⟨2916909, by rfl⟩ : syracuseStep 7778425 = 5833819) B5833819
theorem B10371233 : Blo 1917435 10371233 := bstep (se 2 (by rfl) ⟨3889212, by rfl⟩ : syracuseStep 10371233 = 7778425) B7778425
theorem B6914155 : Blo 1917435 6914155 := bstep (se 1 (by rfl) ⟨5185616, by rfl⟩ : syracuseStep 6914155 = 10371233) B10371233
theorem B9218873 : Blo 1917435 9218873 := bstep (se 2 (by rfl) ⟨3457077, by rfl⟩ : syracuseStep 9218873 = 6914155) B6914155
theorem B6145915 : Blo 1917435 6145915 := bstep (se 1 (by rfl) ⟨4609436, by rfl⟩ : syracuseStep 6145915 = 9218873) B9218873
theorem B8194553 : Blo 1917435 8194553 := bstep (se 2 (by rfl) ⟨3072957, by rfl⟩ : syracuseStep 8194553 = 6145915) B6145915
theorem B5463035 : Blo 1917435 5463035 := bstep (se 1 (by rfl) ⟨4097276, by rfl⟩ : syracuseStep 5463035 = 8194553) B8194553
theorem B3642023 : Blo 1917435 3642023 := bstep (se 1 (by rfl) ⟨2731517, by rfl⟩ : syracuseStep 3642023 = 5463035) B5463035
theorem B9712061 : Blo 1917435 9712061 := bstep (se 3 (by rfl) ⟨1821011, by rfl⟩ : syracuseStep 9712061 = 3642023) B3642023
theorem B6474707 : Blo 1917435 6474707 := bstep (se 1 (by rfl) ⟨4856030, by rfl⟩ : syracuseStep 6474707 = 9712061) B9712061
theorem B4316471 : Blo 1917435 4316471 := bstep (se 1 (by rfl) ⟨3237353, by rfl⟩ : syracuseStep 4316471 = 6474707) B6474707
theorem B2877647 : Blo 1917435 2877647 := bstep (se 1 (by rfl) ⟨2158235, by rfl⟩ : syracuseStep 2877647 = 4316471) B4316471
theorem B1918431 : Blo 1917435 1918431 := bstep (se 1 (by rfl) ⟨1438823, by rfl⟩ : syracuseStep 1918431 = 2877647) B2877647
theorem B2877653 : Blo 1917435 2877653 := bbase (se 7 (by rfl) ⟨33722, by rfl⟩ : syracuseStep 2877653 = 67445) (by norm_num)
theorem B1918435 : Blo 1917435 1918435 := bstep (se 1 (by rfl) ⟨1438826, by rfl⟩ : syracuseStep 1918435 = 2877653) B2877653
theorem B3457093 : Blo 1917435 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B4609457 : Blo 1917435 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B3072971 : Blo 1917435 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B2048647 : Blo 1917435 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B2731529 : Blo 1917435 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B7284077 : Blo 1917435 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B4856051 : Blo 1917435 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B3237367 : Blo 1917435 3237367 := bstep (se 1 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 3237367 = 4856051) B4856051
theorem B4316489 : Blo 1917435 4316489 := bstep (se 2 (by rfl) ⟨1618683, by rfl⟩ : syracuseStep 4316489 = 3237367) B3237367
theorem B2877659 : Blo 1917435 2877659 := bstep (se 1 (by rfl) ⟨2158244, by rfl⟩ : syracuseStep 2877659 = 4316489) B4316489
theorem B1918439 : Blo 1917435 1918439 := bstep (se 1 (by rfl) ⟨1438829, by rfl⟩ : syracuseStep 1918439 = 2877659) B2877659
theorem B2158249 : Blo 1917435 2158249 := bbase (se 2 (by rfl) ⟨809343, by rfl⟩ : syracuseStep 2158249 = 1618687) (by norm_num)
theorem B2877665 : Blo 1917435 2877665 := bstep (se 2 (by rfl) ⟨1079124, by rfl⟩ : syracuseStep 2877665 = 2158249) B2158249
theorem B1918443 : Blo 1917435 1918443 := bstep (se 1 (by rfl) ⟨1438832, by rfl⟩ : syracuseStep 1918443 = 2877665) B2877665
theorem B6914213 : Blo 1917435 6914213 := bbase (se 4 (by rfl) ⟨648207, by rfl⟩ : syracuseStep 6914213 = 1296415) (by norm_num)
theorem B4609475 : Blo 1917435 4609475 := bstep (se 1 (by rfl) ⟨3457106, by rfl⟩ : syracuseStep 4609475 = 6914213) B6914213
theorem B3072983 : Blo 1917435 3072983 := bstep (se 1 (by rfl) ⟨2304737, by rfl⟩ : syracuseStep 3072983 = 4609475) B4609475
theorem B8194621 : Blo 1917435 8194621 := bstep (se 3 (by rfl) ⟨1536491, by rfl⟩ : syracuseStep 8194621 = 3072983) B3072983
theorem B10926161 : Blo 1917435 10926161 := bstep (se 2 (by rfl) ⟨4097310, by rfl⟩ : syracuseStep 10926161 = 8194621) B8194621
theorem B7284107 : Blo 1917435 7284107 := bstep (se 1 (by rfl) ⟨5463080, by rfl⟩ : syracuseStep 7284107 = 10926161) B10926161
theorem B4856071 : Blo 1917435 4856071 := bstep (se 1 (by rfl) ⟨3642053, by rfl⟩ : syracuseStep 4856071 = 7284107) B7284107
theorem B6474761 : Blo 1917435 6474761 := bstep (se 2 (by rfl) ⟨2428035, by rfl⟩ : syracuseStep 6474761 = 4856071) B4856071
theorem B4316507 : Blo 1917435 4316507 := bstep (se 1 (by rfl) ⟨3237380, by rfl⟩ : syracuseStep 4316507 = 6474761) B6474761
theorem B2877671 : Blo 1917435 2877671 := bstep (se 1 (by rfl) ⟨2158253, by rfl⟩ : syracuseStep 2877671 = 4316507) B4316507
theorem B1918447 : Blo 1917435 1918447 := bstep (se 1 (by rfl) ⟨1438835, by rfl⟩ : syracuseStep 1918447 = 2877671) B2877671
theorem B2877677 : Blo 1917435 2877677 := bbase (se 3 (by rfl) ⟨539564, by rfl⟩ : syracuseStep 2877677 = 1079129) (by norm_num)
theorem B1918451 : Blo 1917435 1918451 := bstep (se 1 (by rfl) ⟨1438838, by rfl⟩ : syracuseStep 1918451 = 2877677) B2877677
theorem B4316525 : Blo 1917435 4316525 := bbase (se 3 (by rfl) ⟨809348, by rfl⟩ : syracuseStep 4316525 = 1618697) (by norm_num)
theorem B2877683 : Blo 1917435 2877683 := bstep (se 1 (by rfl) ⟨2158262, by rfl⟩ : syracuseStep 2877683 = 4316525) B4316525
theorem B1918455 : Blo 1917435 1918455 := bstep (se 1 (by rfl) ⟨1438841, by rfl⟩ : syracuseStep 1918455 = 2877683) B2877683
theorem B3642077 : Blo 1917435 3642077 := bbase (se 3 (by rfl) ⟨682889, by rfl⟩ : syracuseStep 3642077 = 1365779) (by norm_num)
theorem B2428051 : Blo 1917435 2428051 := bstep (se 1 (by rfl) ⟨1821038, by rfl⟩ : syracuseStep 2428051 = 3642077) B3642077
theorem B3237401 : Blo 1917435 3237401 := bstep (se 2 (by rfl) ⟨1214025, by rfl⟩ : syracuseStep 3237401 = 2428051) B2428051
theorem B2158267 : Blo 1917435 2158267 := bstep (se 1 (by rfl) ⟨1618700, by rfl⟩ : syracuseStep 2158267 = 3237401) B3237401
theorem B2877689 : Blo 1917435 2877689 := bstep (se 2 (by rfl) ⟨1079133, by rfl⟩ : syracuseStep 2877689 = 2158267) B2158267
theorem B1918459 : Blo 1917435 1918459 := bstep (se 1 (by rfl) ⟨1438844, by rfl⟩ : syracuseStep 1918459 = 2877689) B2877689
theorem B3889277 : Blo 1917435 3889277 := bbase (se 3 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 3889277 = 1458479) (by norm_num)
theorem B2592851 : Blo 1917435 2592851 := bstep (se 1 (by rfl) ⟨1944638, by rfl⟩ : syracuseStep 2592851 = 3889277) B3889277
theorem B6914269 : Blo 1917435 6914269 := bstep (se 3 (by rfl) ⟨1296425, by rfl⟩ : syracuseStep 6914269 = 2592851) B2592851
theorem B9219025 : Blo 1917435 9219025 := bstep (se 2 (by rfl) ⟨3457134, by rfl⟩ : syracuseStep 9219025 = 6914269) B6914269
theorem B49168133 : Blo 1917435 49168133 := bstep (se 4 (by rfl) ⟨4609512, by rfl⟩ : syracuseStep 49168133 = 9219025) B9219025
theorem B32778755 : Blo 1917435 32778755 := bstep (se 1 (by rfl) ⟨24584066, by rfl⟩ : syracuseStep 32778755 = 49168133) B49168133
theorem B21852503 : Blo 1917435 21852503 := bstep (se 1 (by rfl) ⟨16389377, by rfl⟩ : syracuseStep 21852503 = 32778755) B32778755
theorem B14568335 : Blo 1917435 14568335 := bstep (se 1 (by rfl) ⟨10926251, by rfl⟩ : syracuseStep 14568335 = 21852503) B21852503
theorem B9712223 : Blo 1917435 9712223 := bstep (se 1 (by rfl) ⟨7284167, by rfl⟩ : syracuseStep 9712223 = 14568335) B14568335
theorem B6474815 : Blo 1917435 6474815 := bstep (se 1 (by rfl) ⟨4856111, by rfl⟩ : syracuseStep 6474815 = 9712223) B9712223
theorem B4316543 : Blo 1917435 4316543 := bstep (se 1 (by rfl) ⟨3237407, by rfl⟩ : syracuseStep 4316543 = 6474815) B6474815
theorem B2877695 : Blo 1917435 2877695 := bstep (se 1 (by rfl) ⟨2158271, by rfl⟩ : syracuseStep 2877695 = 4316543) B4316543
theorem B1918463 : Blo 1917435 1918463 := bstep (se 1 (by rfl) ⟨1438847, by rfl⟩ : syracuseStep 1918463 = 2877695) B2877695
theorem B2877701 : Blo 1917435 2877701 := bbase (se 4 (by rfl) ⟨269784, by rfl⟩ : syracuseStep 2877701 = 539569) (by norm_num)
theorem B1918467 : Blo 1917435 1918467 := bstep (se 1 (by rfl) ⟨1438850, by rfl⟩ : syracuseStep 1918467 = 2877701) B2877701
theorem B3237421 : Blo 1917435 3237421 := bbase (se 3 (by rfl) ⟨607016, by rfl⟩ : syracuseStep 3237421 = 1214033) (by norm_num)
theorem B4316561 : Blo 1917435 4316561 := bstep (se 2 (by rfl) ⟨1618710, by rfl⟩ : syracuseStep 4316561 = 3237421) B3237421
theorem B2877707 : Blo 1917435 2877707 := bstep (se 1 (by rfl) ⟨2158280, by rfl⟩ : syracuseStep 2877707 = 4316561) B4316561
theorem B1918471 : Blo 1917435 1918471 := bstep (se 1 (by rfl) ⟨1438853, by rfl⟩ : syracuseStep 1918471 = 2877707) B2877707
theorem B2158285 : Blo 1917435 2158285 := bbase (se 3 (by rfl) ⟨404678, by rfl⟩ : syracuseStep 2158285 = 809357) (by norm_num)
theorem B2877713 : Blo 1917435 2877713 := bstep (se 2 (by rfl) ⟨1079142, by rfl⟩ : syracuseStep 2877713 = 2158285) B2158285
theorem B1918475 : Blo 1917435 1918475 := bstep (se 1 (by rfl) ⟨1438856, by rfl⟩ : syracuseStep 1918475 = 2877713) B2877713
theorem B6474869 : Blo 1917435 6474869 := bbase (se 5 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 6474869 = 607019) (by norm_num)
theorem B4316579 : Blo 1917435 4316579 := bstep (se 1 (by rfl) ⟨3237434, by rfl⟩ : syracuseStep 4316579 = 6474869) B6474869
theorem B2877719 : Blo 1917435 2877719 := bstep (se 1 (by rfl) ⟨2158289, by rfl⟩ : syracuseStep 2877719 = 4316579) B4316579
theorem B1918479 : Blo 1917435 1918479 := bstep (se 1 (by rfl) ⟨1438859, by rfl⟩ : syracuseStep 1918479 = 2877719) B2877719
theorem B2877725 : Blo 1917435 2877725 := bbase (se 3 (by rfl) ⟨539573, by rfl⟩ : syracuseStep 2877725 = 1079147) (by norm_num)
theorem B1918483 : Blo 1917435 1918483 := bstep (se 1 (by rfl) ⟨1438862, by rfl⟩ : syracuseStep 1918483 = 2877725) B2877725
theorem B4316597 : Blo 1917435 4316597 := bbase (se 5 (by rfl) ⟨202340, by rfl⟩ : syracuseStep 4316597 = 404681) (by norm_num)
theorem B2877731 : Blo 1917435 2877731 := bstep (se 1 (by rfl) ⟨2158298, by rfl⟩ : syracuseStep 2877731 = 4316597) B4316597
theorem B1918487 : Blo 1917435 1918487 := bstep (se 1 (by rfl) ⟨1438865, by rfl⟩ : syracuseStep 1918487 = 2877731) B2877731
theorem B4097405 : Blo 1917435 4097405 := bbase (se 3 (by rfl) ⟨768263, by rfl⟩ : syracuseStep 4097405 = 1536527) (by norm_num)
theorem B10926413 : Blo 1917435 10926413 := bstep (se 3 (by rfl) ⟨2048702, by rfl⟩ : syracuseStep 10926413 = 4097405) B4097405
theorem B7284275 : Blo 1917435 7284275 := bstep (se 1 (by rfl) ⟨5463206, by rfl⟩ : syracuseStep 7284275 = 10926413) B10926413
theorem B4856183 : Blo 1917435 4856183 := bstep (se 1 (by rfl) ⟨3642137, by rfl⟩ : syracuseStep 4856183 = 7284275) B7284275
theorem B3237455 : Blo 1917435 3237455 := bstep (se 1 (by rfl) ⟨2428091, by rfl⟩ : syracuseStep 3237455 = 4856183) B4856183
theorem B2158303 : Blo 1917435 2158303 := bstep (se 1 (by rfl) ⟨1618727, by rfl⟩ : syracuseStep 2158303 = 3237455) B3237455
theorem B2877737 : Blo 1917435 2877737 := bstep (se 2 (by rfl) ⟨1079151, by rfl⟩ : syracuseStep 2877737 = 2158303) B2158303
theorem B1918491 : Blo 1917435 1918491 := bstep (se 1 (by rfl) ⟨1438868, by rfl⟩ : syracuseStep 1918491 = 2877737) B2877737
theorem B4097413 : Blo 1917435 4097413 := bbase (se 4 (by rfl) ⟨384132, by rfl⟩ : syracuseStep 4097413 = 768265) (by norm_num)
theorem B5463217 : Blo 1917435 5463217 := bstep (se 2 (by rfl) ⟨2048706, by rfl⟩ : syracuseStep 5463217 = 4097413) B4097413
theorem B7284289 : Blo 1917435 7284289 := bstep (se 2 (by rfl) ⟨2731608, by rfl⟩ : syracuseStep 7284289 = 5463217) B5463217
theorem B9712385 : Blo 1917435 9712385 := bstep (se 2 (by rfl) ⟨3642144, by rfl⟩ : syracuseStep 9712385 = 7284289) B7284289
theorem B6474923 : Blo 1917435 6474923 := bstep (se 1 (by rfl) ⟨4856192, by rfl⟩ : syracuseStep 6474923 = 9712385) B9712385
theorem B4316615 : Blo 1917435 4316615 := bstep (se 1 (by rfl) ⟨3237461, by rfl⟩ : syracuseStep 4316615 = 6474923) B6474923
theorem B2877743 : Blo 1917435 2877743 := bstep (se 1 (by rfl) ⟨2158307, by rfl⟩ : syracuseStep 2877743 = 4316615) B4316615
theorem B1918495 : Blo 1917435 1918495 := bstep (se 1 (by rfl) ⟨1438871, by rfl⟩ : syracuseStep 1918495 = 2877743) B2877743
theorem B2877749 : Blo 1917435 2877749 := bbase (se 5 (by rfl) ⟨134894, by rfl⟩ : syracuseStep 2877749 = 269789) (by norm_num)
theorem B1918499 : Blo 1917435 1918499 := bstep (se 1 (by rfl) ⟨1438874, by rfl⟩ : syracuseStep 1918499 = 2877749) B2877749
theorem B4856213 : Blo 1917435 4856213 := bbase (se 6 (by rfl) ⟨113817, by rfl⟩ : syracuseStep 4856213 = 227635) (by norm_num)
theorem B3237475 : Blo 1917435 3237475 := bstep (se 1 (by rfl) ⟨2428106, by rfl⟩ : syracuseStep 3237475 = 4856213) B4856213
theorem B4316633 : Blo 1917435 4316633 := bstep (se 2 (by rfl) ⟨1618737, by rfl⟩ : syracuseStep 4316633 = 3237475) B3237475
theorem B2877755 : Blo 1917435 2877755 := bstep (se 1 (by rfl) ⟨2158316, by rfl⟩ : syracuseStep 2877755 = 4316633) B4316633
theorem B1918503 : Blo 1917435 1918503 := bstep (se 1 (by rfl) ⟨1438877, by rfl⟩ : syracuseStep 1918503 = 2877755) B2877755
theorem B2158321 : Blo 1917435 2158321 := bbase (se 2 (by rfl) ⟨809370, by rfl⟩ : syracuseStep 2158321 = 1618741) (by norm_num)
theorem B2877761 : Blo 1917435 2877761 := bstep (se 2 (by rfl) ⟨1079160, by rfl⟩ : syracuseStep 2877761 = 2158321) B2158321
theorem B1918507 : Blo 1917435 1918507 := bstep (se 1 (by rfl) ⟨1438880, by rfl⟩ : syracuseStep 1918507 = 2877761) B2877761
theorem B2336261 : Blo 1917435 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B6230029 : Blo 1917435 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B8306705 : Blo 1917435 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B5537803 : Blo 1917435 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B7383737 : Blo 1917435 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B4922491 : Blo 1917435 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B6563321 : Blo 1917435 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B4375547 : Blo 1917435 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B2917031 : Blo 1917435 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B7778749 : Blo 1917435 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B10371665 : Blo 1917435 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B27657773 : Blo 1917435 27657773 := bstep (se 3 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 27657773 = 10371665) B10371665
theorem B18438515 : Blo 1917435 18438515 := bstep (se 1 (by rfl) ⟨13828886, by rfl⟩ : syracuseStep 18438515 = 27657773) B27657773
theorem B12292343 : Blo 1917435 12292343 := bstep (se 1 (by rfl) ⟨9219257, by rfl⟩ : syracuseStep 12292343 = 18438515) B18438515
theorem B8194895 : Blo 1917435 8194895 := bstep (se 1 (by rfl) ⟨6146171, by rfl⟩ : syracuseStep 8194895 = 12292343) B12292343
theorem B5463263 : Blo 1917435 5463263 := bstep (se 1 (by rfl) ⟨4097447, by rfl⟩ : syracuseStep 5463263 = 8194895) B8194895
theorem B3642175 : Blo 1917435 3642175 := bstep (se 1 (by rfl) ⟨2731631, by rfl⟩ : syracuseStep 3642175 = 5463263) B5463263
theorem B4856233 : Blo 1917435 4856233 := bstep (se 2 (by rfl) ⟨1821087, by rfl⟩ : syracuseStep 4856233 = 3642175) B3642175
theorem B6474977 : Blo 1917435 6474977 := bstep (se 2 (by rfl) ⟨2428116, by rfl⟩ : syracuseStep 6474977 = 4856233) B4856233
theorem B4316651 : Blo 1917435 4316651 := bstep (se 1 (by rfl) ⟨3237488, by rfl⟩ : syracuseStep 4316651 = 6474977) B6474977
theorem B2877767 : Blo 1917435 2877767 := bstep (se 1 (by rfl) ⟨2158325, by rfl⟩ : syracuseStep 2877767 = 4316651) B4316651
theorem B1918511 : Blo 1917435 1918511 := bstep (se 1 (by rfl) ⟨1438883, by rfl⟩ : syracuseStep 1918511 = 2877767) B2877767
theorem B2877773 : Blo 1917435 2877773 := bbase (se 3 (by rfl) ⟨539582, by rfl⟩ : syracuseStep 2877773 = 1079165) (by norm_num)
theorem B1918515 : Blo 1917435 1918515 := bstep (se 1 (by rfl) ⟨1438886, by rfl⟩ : syracuseStep 1918515 = 2877773) B2877773
theorem B4316669 : Blo 1917435 4316669 := bbase (se 3 (by rfl) ⟨809375, by rfl⟩ : syracuseStep 4316669 = 1618751) (by norm_num)
theorem B2877779 : Blo 1917435 2877779 := bstep (se 1 (by rfl) ⟨2158334, by rfl⟩ : syracuseStep 2877779 = 4316669) B4316669
theorem B1918519 : Blo 1917435 1918519 := bstep (se 1 (by rfl) ⟨1438889, by rfl⟩ : syracuseStep 1918519 = 2877779) B2877779
theorem B3237509 : Blo 1917435 3237509 := bbase (se 4 (by rfl) ⟨303516, by rfl⟩ : syracuseStep 3237509 = 607033) (by norm_num)
theorem B2158339 : Blo 1917435 2158339 := bstep (se 1 (by rfl) ⟨1618754, by rfl⟩ : syracuseStep 2158339 = 3237509) B3237509
theorem B2877785 : Blo 1917435 2877785 := bstep (se 2 (by rfl) ⟨1079169, by rfl⟩ : syracuseStep 2877785 = 2158339) B2158339
theorem B1918523 : Blo 1917435 1918523 := bstep (se 1 (by rfl) ⟨1438892, by rfl⟩ : syracuseStep 1918523 = 2877785) B2877785
theorem B14568821 : Blo 1917435 14568821 := bbase (se 5 (by rfl) ⟨682913, by rfl⟩ : syracuseStep 14568821 = 1365827) (by norm_num)
theorem B9712547 : Blo 1917435 9712547 := bstep (se 1 (by rfl) ⟨7284410, by rfl⟩ : syracuseStep 9712547 = 14568821) B14568821
theorem B6475031 : Blo 1917435 6475031 := bstep (se 1 (by rfl) ⟨4856273, by rfl⟩ : syracuseStep 6475031 = 9712547) B9712547
theorem B4316687 : Blo 1917435 4316687 := bstep (se 1 (by rfl) ⟨3237515, by rfl⟩ : syracuseStep 4316687 = 6475031) B6475031
theorem B2877791 : Blo 1917435 2877791 := bstep (se 1 (by rfl) ⟨2158343, by rfl⟩ : syracuseStep 2877791 = 4316687) B4316687
theorem B1918527 : Blo 1917435 1918527 := bstep (se 1 (by rfl) ⟨1438895, by rfl⟩ : syracuseStep 1918527 = 2877791) B2877791
theorem B2877797 : Blo 1917435 2877797 := bbase (se 4 (by rfl) ⟨269793, by rfl⟩ : syracuseStep 2877797 = 539587) (by norm_num)
theorem B1918531 : Blo 1917435 1918531 := bstep (se 1 (by rfl) ⟨1438898, by rfl⟩ : syracuseStep 1918531 = 2877797) B2877797
theorem B3642221 : Blo 1917435 3642221 := bbase (se 3 (by rfl) ⟨682916, by rfl⟩ : syracuseStep 3642221 = 1365833) (by norm_num)
theorem B2428147 : Blo 1917435 2428147 := bstep (se 1 (by rfl) ⟨1821110, by rfl⟩ : syracuseStep 2428147 = 3642221) B3642221
theorem B3237529 : Blo 1917435 3237529 := bstep (se 2 (by rfl) ⟨1214073, by rfl⟩ : syracuseStep 3237529 = 2428147) B2428147
theorem B4316705 : Blo 1917435 4316705 := bstep (se 2 (by rfl) ⟨1618764, by rfl⟩ : syracuseStep 4316705 = 3237529) B3237529
theorem B2877803 : Blo 1917435 2877803 := bstep (se 1 (by rfl) ⟨2158352, by rfl⟩ : syracuseStep 2877803 = 4316705) B4316705
theorem B1918535 : Blo 1917435 1918535 := bstep (se 1 (by rfl) ⟨1438901, by rfl⟩ : syracuseStep 1918535 = 2877803) B2877803
theorem B2158357 : Blo 1917435 2158357 := bbase (se 6 (by rfl) ⟨50586, by rfl⟩ : syracuseStep 2158357 = 101173) (by norm_num)
theorem B2877809 : Blo 1917435 2877809 := bstep (se 2 (by rfl) ⟨1079178, by rfl⟩ : syracuseStep 2877809 = 2158357) B2158357
theorem B1918539 : Blo 1917435 1918539 := bstep (se 1 (by rfl) ⟨1438904, by rfl⟩ : syracuseStep 1918539 = 2877809) B2877809
theorem B2428157 : Blo 1917435 2428157 := bbase (se 3 (by rfl) ⟨455279, by rfl⟩ : syracuseStep 2428157 = 910559) (by norm_num)
theorem B6475085 : Blo 1917435 6475085 := bstep (se 3 (by rfl) ⟨1214078, by rfl⟩ : syracuseStep 6475085 = 2428157) B2428157
theorem B4316723 : Blo 1917435 4316723 := bstep (se 1 (by rfl) ⟨3237542, by rfl⟩ : syracuseStep 4316723 = 6475085) B6475085
theorem B2877815 : Blo 1917435 2877815 := bstep (se 1 (by rfl) ⟨2158361, by rfl⟩ : syracuseStep 2877815 = 4316723) B4316723
theorem B1918543 : Blo 1917435 1918543 := bstep (se 1 (by rfl) ⟨1438907, by rfl⟩ : syracuseStep 1918543 = 2877815) B2877815
theorem B2877821 : Blo 1917435 2877821 := bbase (se 3 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 2877821 = 1079183) (by norm_num)
theorem B1918547 : Blo 1917435 1918547 := bstep (se 1 (by rfl) ⟨1438910, by rfl⟩ : syracuseStep 1918547 = 2877821) B2877821
theorem B4316741 : Blo 1917435 4316741 := bbase (se 4 (by rfl) ⟨404694, by rfl⟩ : syracuseStep 4316741 = 809389) (by norm_num)
theorem B2877827 : Blo 1917435 2877827 := bstep (se 1 (by rfl) ⟨2158370, by rfl⟩ : syracuseStep 2877827 = 4316741) B4316741
theorem B1918551 : Blo 1917435 1918551 := bstep (se 1 (by rfl) ⟨1438913, by rfl⟩ : syracuseStep 1918551 = 2877827) B2877827
theorem B3073157 : Blo 1917435 3073157 := bbase (se 4 (by rfl) ⟨288108, by rfl⟩ : syracuseStep 3073157 = 576217) (by norm_num)
theorem B2048771 : Blo 1917435 2048771 := bstep (se 1 (by rfl) ⟨1536578, by rfl⟩ : syracuseStep 2048771 = 3073157) B3073157
theorem B5463389 : Blo 1917435 5463389 := bstep (se 3 (by rfl) ⟨1024385, by rfl⟩ : syracuseStep 5463389 = 2048771) B2048771
theorem B3642259 : Blo 1917435 3642259 := bstep (se 1 (by rfl) ⟨2731694, by rfl⟩ : syracuseStep 3642259 = 5463389) B5463389
theorem B4856345 : Blo 1917435 4856345 := bstep (se 2 (by rfl) ⟨1821129, by rfl⟩ : syracuseStep 4856345 = 3642259) B3642259
theorem B3237563 : Blo 1917435 3237563 := bstep (se 1 (by rfl) ⟨2428172, by rfl⟩ : syracuseStep 3237563 = 4856345) B4856345
theorem B2158375 : Blo 1917435 2158375 := bstep (se 1 (by rfl) ⟨1618781, by rfl⟩ : syracuseStep 2158375 = 3237563) B3237563
theorem B2877833 : Blo 1917435 2877833 := bstep (se 2 (by rfl) ⟨1079187, by rfl⟩ : syracuseStep 2877833 = 2158375) B2158375
theorem B1918555 : Blo 1917435 1918555 := bstep (se 1 (by rfl) ⟨1438916, by rfl⟩ : syracuseStep 1918555 = 2877833) B2877833
theorem B9712709 : Blo 1917435 9712709 := bbase (se 4 (by rfl) ⟨910566, by rfl⟩ : syracuseStep 9712709 = 1821133) (by norm_num)
theorem B6475139 : Blo 1917435 6475139 := bstep (se 1 (by rfl) ⟨4856354, by rfl⟩ : syracuseStep 6475139 = 9712709) B9712709
theorem B4316759 : Blo 1917435 4316759 := bstep (se 1 (by rfl) ⟨3237569, by rfl⟩ : syracuseStep 4316759 = 6475139) B6475139
theorem B2877839 : Blo 1917435 2877839 := bstep (se 1 (by rfl) ⟨2158379, by rfl⟩ : syracuseStep 2877839 = 4316759) B4316759
theorem B1918559 : Blo 1917435 1918559 := bstep (se 1 (by rfl) ⟨1438919, by rfl⟩ : syracuseStep 1918559 = 2877839) B2877839
theorem B2877845 : Blo 1917435 2877845 := bbase (se 6 (by rfl) ⟨67449, by rfl⟩ : syracuseStep 2877845 = 134899) (by norm_num)
theorem B1918563 : Blo 1917435 1918563 := bstep (se 1 (by rfl) ⟨1438922, by rfl⟩ : syracuseStep 1918563 = 2877845) B2877845
theorem B8751349 : Blo 1917435 8751349 := bbase (se 5 (by rfl) ⟨410219, by rfl⟩ : syracuseStep 8751349 = 820439) (by norm_num)
theorem B11668465 : Blo 1917435 11668465 := bstep (se 2 (by rfl) ⟨4375674, by rfl⟩ : syracuseStep 11668465 = 8751349) B8751349
theorem B15557953 : Blo 1917435 15557953 := bstep (se 2 (by rfl) ⟨5834232, by rfl⟩ : syracuseStep 15557953 = 11668465) B11668465
theorem B20743937 : Blo 1917435 20743937 := bstep (se 2 (by rfl) ⟨7778976, by rfl⟩ : syracuseStep 20743937 = 15557953) B15557953
theorem B13829291 : Blo 1917435 13829291 := bstep (se 1 (by rfl) ⟨10371968, by rfl⟩ : syracuseStep 13829291 = 20743937) B20743937
theorem B9219527 : Blo 1917435 9219527 := bstep (se 1 (by rfl) ⟨6914645, by rfl⟩ : syracuseStep 9219527 = 13829291) B13829291
theorem B6146351 : Blo 1917435 6146351 := bstep (se 1 (by rfl) ⟨4609763, by rfl⟩ : syracuseStep 6146351 = 9219527) B9219527
theorem B4097567 : Blo 1917435 4097567 := bstep (se 1 (by rfl) ⟨3073175, by rfl⟩ : syracuseStep 4097567 = 6146351) B6146351
theorem B10926845 : Blo 1917435 10926845 := bstep (se 3 (by rfl) ⟨2048783, by rfl⟩ : syracuseStep 10926845 = 4097567) B4097567
theorem B7284563 : Blo 1917435 7284563 := bstep (se 1 (by rfl) ⟨5463422, by rfl⟩ : syracuseStep 7284563 = 10926845) B10926845
theorem B4856375 : Blo 1917435 4856375 := bstep (se 1 (by rfl) ⟨3642281, by rfl⟩ : syracuseStep 4856375 = 7284563) B7284563
theorem B3237583 : Blo 1917435 3237583 := bstep (se 1 (by rfl) ⟨2428187, by rfl⟩ : syracuseStep 3237583 = 4856375) B4856375
theorem B4316777 : Blo 1917435 4316777 := bstep (se 2 (by rfl) ⟨1618791, by rfl⟩ : syracuseStep 4316777 = 3237583) B3237583
theorem B2877851 : Blo 1917435 2877851 := bstep (se 1 (by rfl) ⟨2158388, by rfl⟩ : syracuseStep 2877851 = 4316777) B4316777
theorem B1918567 : Blo 1917435 1918567 := bstep (se 1 (by rfl) ⟨1438925, by rfl⟩ : syracuseStep 1918567 = 2877851) B2877851
theorem B2158393 : Blo 1917435 2158393 := bbase (se 2 (by rfl) ⟨809397, by rfl⟩ : syracuseStep 2158393 = 1618795) (by norm_num)
theorem B2877857 : Blo 1917435 2877857 := bstep (se 2 (by rfl) ⟨1079196, by rfl⟩ : syracuseStep 2877857 = 2158393) B2158393
theorem B1918571 : Blo 1917435 1918571 := bstep (se 1 (by rfl) ⟨1438928, by rfl⟩ : syracuseStep 1918571 = 2877857) B2877857
theorem B5463445 : Blo 1917435 5463445 := bbase (se 6 (by rfl) ⟨128049, by rfl⟩ : syracuseStep 5463445 = 256099) (by norm_num)
theorem B7284593 : Blo 1917435 7284593 := bstep (se 2 (by rfl) ⟨2731722, by rfl⟩ : syracuseStep 7284593 = 5463445) B5463445
theorem B4856395 : Blo 1917435 4856395 := bstep (se 1 (by rfl) ⟨3642296, by rfl⟩ : syracuseStep 4856395 = 7284593) B7284593
theorem B6475193 : Blo 1917435 6475193 := bstep (se 2 (by rfl) ⟨2428197, by rfl⟩ : syracuseStep 6475193 = 4856395) B4856395
theorem B4316795 : Blo 1917435 4316795 := bstep (se 1 (by rfl) ⟨3237596, by rfl⟩ : syracuseStep 4316795 = 6475193) B6475193
theorem B2877863 : Blo 1917435 2877863 := bstep (se 1 (by rfl) ⟨2158397, by rfl⟩ : syracuseStep 2877863 = 4316795) B4316795
theorem B1918575 : Blo 1917435 1918575 := bstep (se 1 (by rfl) ⟨1438931, by rfl⟩ : syracuseStep 1918575 = 2877863) B2877863
theorem B2877869 : Blo 1917435 2877869 := bbase (se 3 (by rfl) ⟨539600, by rfl⟩ : syracuseStep 2877869 = 1079201) (by norm_num)
theorem B1918579 : Blo 1917435 1918579 := bstep (se 1 (by rfl) ⟨1438934, by rfl⟩ : syracuseStep 1918579 = 2877869) B2877869
theorem B4316813 : Blo 1917435 4316813 := bbase (se 3 (by rfl) ⟨809402, by rfl⟩ : syracuseStep 4316813 = 1618805) (by norm_num)
theorem B2877875 : Blo 1917435 2877875 := bstep (se 1 (by rfl) ⟨2158406, by rfl⟩ : syracuseStep 2877875 = 4316813) B4316813
theorem B1918583 : Blo 1917435 1918583 := bstep (se 1 (by rfl) ⟨1438937, by rfl⟩ : syracuseStep 1918583 = 2877875) B2877875
theorem B2428213 : Blo 1917435 2428213 := bbase (se 5 (by rfl) ⟨113822, by rfl⟩ : syracuseStep 2428213 = 227645) (by norm_num)
theorem B3237617 : Blo 1917435 3237617 := bstep (se 2 (by rfl) ⟨1214106, by rfl⟩ : syracuseStep 3237617 = 2428213) B2428213
theorem B2158411 : Blo 1917435 2158411 := bstep (se 1 (by rfl) ⟨1618808, by rfl⟩ : syracuseStep 2158411 = 3237617) B3237617
theorem B2877881 : Blo 1917435 2877881 := bstep (se 2 (by rfl) ⟨1079205, by rfl⟩ : syracuseStep 2877881 = 2158411) B2158411
theorem B1918587 : Blo 1917435 1918587 := bstep (se 1 (by rfl) ⟨1438940, by rfl⟩ : syracuseStep 1918587 = 2877881) B2877881
theorem B1971301 : Blo 1917435 1971301 := bbase (se 4 (by rfl) ⟨184809, by rfl⟩ : syracuseStep 1971301 = 369619) (by norm_num)
theorem B42054421 : Blo 1917435 42054421 := bstep (se 6 (by rfl) ⟨985650, by rfl⟩ : syracuseStep 42054421 = 1971301) B1971301
theorem B897160981 : Blo 1917435 897160981 := bstep (se 6 (by rfl) ⟨21027210, by rfl⟩ : syracuseStep 897160981 = 42054421) B42054421
theorem B1196214641 : Blo 1917435 1196214641 := bstep (se 2 (by rfl) ⟨448580490, by rfl⟩ : syracuseStep 1196214641 = 897160981) B897160981
theorem B797476427 : Blo 1917435 797476427 := bstep (se 1 (by rfl) ⟨598107320, by rfl⟩ : syracuseStep 797476427 = 1196214641) B1196214641
theorem B531650951 : Blo 1917435 531650951 := bstep (se 1 (by rfl) ⟨398738213, by rfl⟩ : syracuseStep 531650951 = 797476427) B797476427
theorem B354433967 : Blo 1917435 354433967 := bstep (se 1 (by rfl) ⟨265825475, by rfl⟩ : syracuseStep 354433967 = 531650951) B531650951
theorem B236289311 : Blo 1917435 236289311 := bstep (se 1 (by rfl) ⟨177216983, by rfl⟩ : syracuseStep 236289311 = 354433967) B354433967
theorem B157526207 : Blo 1917435 157526207 := bstep (se 1 (by rfl) ⟨118144655, by rfl⟩ : syracuseStep 157526207 = 236289311) B236289311
theorem B105017471 : Blo 1917435 105017471 := bstep (se 1 (by rfl) ⟨78763103, by rfl⟩ : syracuseStep 105017471 = 157526207) B157526207
theorem B70011647 : Blo 1917435 70011647 := bstep (se 1 (by rfl) ⟨52508735, by rfl⟩ : syracuseStep 70011647 = 105017471) B105017471
theorem B46674431 : Blo 1917435 46674431 := bstep (se 1 (by rfl) ⟨35005823, by rfl⟩ : syracuseStep 46674431 = 70011647) B70011647
theorem B31116287 : Blo 1917435 31116287 := bstep (se 1 (by rfl) ⟨23337215, by rfl⟩ : syracuseStep 31116287 = 46674431) B46674431
theorem B20744191 : Blo 1917435 20744191 := bstep (se 1 (by rfl) ⟨15558143, by rfl⟩ : syracuseStep 20744191 = 31116287) B31116287
theorem B27658921 : Blo 1917435 27658921 := bstep (se 2 (by rfl) ⟨10372095, by rfl⟩ : syracuseStep 27658921 = 20744191) B20744191
theorem B36878561 : Blo 1917435 36878561 := bstep (se 2 (by rfl) ⟨13829460, by rfl⟩ : syracuseStep 36878561 = 27658921) B27658921
theorem B24585707 : Blo 1917435 24585707 := bstep (se 1 (by rfl) ⟨18439280, by rfl⟩ : syracuseStep 24585707 = 36878561) B36878561
theorem B16390471 : Blo 1917435 16390471 := bstep (se 1 (by rfl) ⟨12292853, by rfl⟩ : syracuseStep 16390471 = 24585707) B24585707
theorem B21853961 : Blo 1917435 21853961 := bstep (se 2 (by rfl) ⟨8195235, by rfl⟩ : syracuseStep 21853961 = 16390471) B16390471
theorem B14569307 : Blo 1917435 14569307 := bstep (se 1 (by rfl) ⟨10926980, by rfl⟩ : syracuseStep 14569307 = 21853961) B21853961
theorem B9712871 : Blo 1917435 9712871 := bstep (se 1 (by rfl) ⟨7284653, by rfl⟩ : syracuseStep 9712871 = 14569307) B14569307
theorem B6475247 : Blo 1917435 6475247 := bstep (se 1 (by rfl) ⟨4856435, by rfl⟩ : syracuseStep 6475247 = 9712871) B9712871
theorem B4316831 : Blo 1917435 4316831 := bstep (se 1 (by rfl) ⟨3237623, by rfl⟩ : syracuseStep 4316831 = 6475247) B6475247
theorem B2877887 : Blo 1917435 2877887 := bstep (se 1 (by rfl) ⟨2158415, by rfl⟩ : syracuseStep 2877887 = 4316831) B4316831
theorem B1918591 : Blo 1917435 1918591 := bstep (se 1 (by rfl) ⟨1438943, by rfl⟩ : syracuseStep 1918591 = 2877887) B2877887
theorem B2877893 : Blo 1917435 2877893 := bbase (se 4 (by rfl) ⟨269802, by rfl⟩ : syracuseStep 2877893 = 539605) (by norm_num)
theorem B1918595 : Blo 1917435 1918595 := bstep (se 1 (by rfl) ⟨1438946, by rfl⟩ : syracuseStep 1918595 = 2877893) B2877893
theorem B3237637 : Blo 1917435 3237637 := bbase (se 4 (by rfl) ⟨303528, by rfl⟩ : syracuseStep 3237637 = 607057) (by norm_num)
theorem B4316849 : Blo 1917435 4316849 := bstep (se 2 (by rfl) ⟨1618818, by rfl⟩ : syracuseStep 4316849 = 3237637) B3237637
theorem B2877899 : Blo 1917435 2877899 := bstep (se 1 (by rfl) ⟨2158424, by rfl⟩ : syracuseStep 2877899 = 4316849) B4316849
theorem B1918599 : Blo 1917435 1918599 := bstep (se 1 (by rfl) ⟨1438949, by rfl⟩ : syracuseStep 1918599 = 2877899) B2877899
theorem B2158429 : Blo 1917435 2158429 := bbase (se 3 (by rfl) ⟨404705, by rfl⟩ : syracuseStep 2158429 = 809411) (by norm_num)
theorem B2877905 : Blo 1917435 2877905 := bstep (se 2 (by rfl) ⟨1079214, by rfl⟩ : syracuseStep 2877905 = 2158429) B2158429
theorem B1918603 : Blo 1917435 1918603 := bstep (se 1 (by rfl) ⟨1438952, by rfl⟩ : syracuseStep 1918603 = 2877905) B2877905
theorem B6475301 : Blo 1917435 6475301 := bbase (se 4 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 6475301 = 1214119) (by norm_num)
theorem B4316867 : Blo 1917435 4316867 := bstep (se 1 (by rfl) ⟨3237650, by rfl⟩ : syracuseStep 4316867 = 6475301) B6475301
theorem B2877911 : Blo 1917435 2877911 := bstep (se 1 (by rfl) ⟨2158433, by rfl⟩ : syracuseStep 2877911 = 4316867) B4316867
theorem B1918607 : Blo 1917435 1918607 := bstep (se 1 (by rfl) ⟨1438955, by rfl⟩ : syracuseStep 1918607 = 2877911) B2877911
theorem B2877917 : Blo 1917435 2877917 := bbase (se 3 (by rfl) ⟨539609, by rfl⟩ : syracuseStep 2877917 = 1079219) (by norm_num)
theorem B1918611 : Blo 1917435 1918611 := bstep (se 1 (by rfl) ⟨1438958, by rfl⟩ : syracuseStep 1918611 = 2877917) B2877917
theorem B4316885 : Blo 1917435 4316885 := bbase (se 7 (by rfl) ⟨50588, by rfl⟩ : syracuseStep 4316885 = 101177) (by norm_num)
theorem B2877923 : Blo 1917435 2877923 := bstep (se 1 (by rfl) ⟨2158442, by rfl⟩ : syracuseStep 2877923 = 4316885) B4316885
theorem B1918615 : Blo 1917435 1918615 := bstep (se 1 (by rfl) ⟨1438961, by rfl⟩ : syracuseStep 1918615 = 2877923) B2877923
theorem B2461385 : Blo 1917435 2461385 := bbase (se 2 (by rfl) ⟨923019, by rfl⟩ : syracuseStep 2461385 = 1846039) (by norm_num)
theorem B6563693 : Blo 1917435 6563693 := bstep (se 3 (by rfl) ⟨1230692, by rfl⟩ : syracuseStep 6563693 = 2461385) B2461385
theorem B4375795 : Blo 1917435 4375795 := bstep (se 1 (by rfl) ⟨3281846, by rfl⟩ : syracuseStep 4375795 = 6563693) B6563693
theorem B5834393 : Blo 1917435 5834393 := bstep (se 2 (by rfl) ⟨2187897, by rfl⟩ : syracuseStep 5834393 = 4375795) B4375795
theorem B3889595 : Blo 1917435 3889595 := bstep (se 1 (by rfl) ⟨2917196, by rfl⟩ : syracuseStep 3889595 = 5834393) B5834393
theorem B2593063 : Blo 1917435 2593063 := bstep (se 1 (by rfl) ⟨1944797, by rfl⟩ : syracuseStep 2593063 = 3889595) B3889595
theorem B3457417 : Blo 1917435 3457417 := bstep (se 2 (by rfl) ⟨1296531, by rfl⟩ : syracuseStep 3457417 = 2593063) B2593063
theorem B4609889 : Blo 1917435 4609889 := bstep (se 2 (by rfl) ⟨1728708, by rfl⟩ : syracuseStep 4609889 = 3457417) B3457417
theorem B3073259 : Blo 1917435 3073259 := bstep (se 1 (by rfl) ⟨2304944, by rfl⟩ : syracuseStep 3073259 = 4609889) B4609889
theorem B8195357 : Blo 1917435 8195357 := bstep (se 3 (by rfl) ⟨1536629, by rfl⟩ : syracuseStep 8195357 = 3073259) B3073259
theorem B5463571 : Blo 1917435 5463571 := bstep (se 1 (by rfl) ⟨4097678, by rfl⟩ : syracuseStep 5463571 = 8195357) B8195357
theorem B7284761 : Blo 1917435 7284761 := bstep (se 2 (by rfl) ⟨2731785, by rfl⟩ : syracuseStep 7284761 = 5463571) B5463571
theorem B4856507 : Blo 1917435 4856507 := bstep (se 1 (by rfl) ⟨3642380, by rfl⟩ : syracuseStep 4856507 = 7284761) B7284761
theorem B3237671 : Blo 1917435 3237671 := bstep (se 1 (by rfl) ⟨2428253, by rfl⟩ : syracuseStep 3237671 = 4856507) B4856507
theorem B2158447 : Blo 1917435 2158447 := bstep (se 1 (by rfl) ⟨1618835, by rfl⟩ : syracuseStep 2158447 = 3237671) B3237671
theorem B2877929 : Blo 1917435 2877929 := bstep (se 2 (by rfl) ⟨1079223, by rfl⟩ : syracuseStep 2877929 = 2158447) B2158447
theorem B1918619 : Blo 1917435 1918619 := bstep (se 1 (by rfl) ⟨1438964, by rfl⟩ : syracuseStep 1918619 = 2877929) B2877929
theorem B2187901 : Blo 1917435 2187901 := bbase (se 3 (by rfl) ⟨410231, by rfl⟩ : syracuseStep 2187901 = 820463) (by norm_num)
theorem B11668805 : Blo 1917435 11668805 := bstep (se 4 (by rfl) ⟨1093950, by rfl⟩ : syracuseStep 11668805 = 2187901) B2187901
theorem B7779203 : Blo 1917435 7779203 := bstep (se 1 (by rfl) ⟨5834402, by rfl⟩ : syracuseStep 7779203 = 11668805) B11668805
theorem B5186135 : Blo 1917435 5186135 := bstep (se 1 (by rfl) ⟨3889601, by rfl⟩ : syracuseStep 5186135 = 7779203) B7779203
theorem B3457423 : Blo 1917435 3457423 := bstep (se 1 (by rfl) ⟨2593067, by rfl⟩ : syracuseStep 3457423 = 5186135) B5186135
theorem B18439589 : Blo 1917435 18439589 := bstep (se 4 (by rfl) ⟨1728711, by rfl⟩ : syracuseStep 18439589 = 3457423) B3457423
theorem B12293059 : Blo 1917435 12293059 := bstep (se 1 (by rfl) ⟨9219794, by rfl⟩ : syracuseStep 12293059 = 18439589) B18439589
theorem B16390745 : Blo 1917435 16390745 := bstep (se 2 (by rfl) ⟨6146529, by rfl⟩ : syracuseStep 16390745 = 12293059) B12293059
theorem B10927163 : Blo 1917435 10927163 := bstep (se 1 (by rfl) ⟨8195372, by rfl⟩ : syracuseStep 10927163 = 16390745) B16390745
theorem B7284775 : Blo 1917435 7284775 := bstep (se 1 (by rfl) ⟨5463581, by rfl⟩ : syracuseStep 7284775 = 10927163) B10927163
theorem B9713033 : Blo 1917435 9713033 := bstep (se 2 (by rfl) ⟨3642387, by rfl⟩ : syracuseStep 9713033 = 7284775) B7284775
theorem B6475355 : Blo 1917435 6475355 := bstep (se 1 (by rfl) ⟨4856516, by rfl⟩ : syracuseStep 6475355 = 9713033) B9713033
theorem B4316903 : Blo 1917435 4316903 := bstep (se 1 (by rfl) ⟨3237677, by rfl⟩ : syracuseStep 4316903 = 6475355) B6475355
theorem B2877935 : Blo 1917435 2877935 := bstep (se 1 (by rfl) ⟨2158451, by rfl⟩ : syracuseStep 2877935 = 4316903) B4316903
theorem B1918623 : Blo 1917435 1918623 := bstep (se 1 (by rfl) ⟨1438967, by rfl⟩ : syracuseStep 1918623 = 2877935) B2877935
theorem B2877941 : Blo 1917435 2877941 := bbase (se 5 (by rfl) ⟨134903, by rfl⟩ : syracuseStep 2877941 = 269807) (by norm_num)
theorem B1918627 : Blo 1917435 1918627 := bstep (se 1 (by rfl) ⟨1438970, by rfl⟩ : syracuseStep 1918627 = 2877941) B2877941
theorem B5463605 : Blo 1917435 5463605 := bbase (se 5 (by rfl) ⟨256106, by rfl⟩ : syracuseStep 5463605 = 512213) (by norm_num)
theorem B3642403 : Blo 1917435 3642403 := bstep (se 1 (by rfl) ⟨2731802, by rfl⟩ : syracuseStep 3642403 = 5463605) B5463605
theorem B4856537 : Blo 1917435 4856537 := bstep (se 2 (by rfl) ⟨1821201, by rfl⟩ : syracuseStep 4856537 = 3642403) B3642403
theorem B3237691 : Blo 1917435 3237691 := bstep (se 1 (by rfl) ⟨2428268, by rfl⟩ : syracuseStep 3237691 = 4856537) B4856537
theorem B4316921 : Blo 1917435 4316921 := bstep (se 2 (by rfl) ⟨1618845, by rfl⟩ : syracuseStep 4316921 = 3237691) B3237691
theorem B2877947 : Blo 1917435 2877947 := bstep (se 1 (by rfl) ⟨2158460, by rfl⟩ : syracuseStep 2877947 = 4316921) B4316921
theorem B1918631 : Blo 1917435 1918631 := bstep (se 1 (by rfl) ⟨1438973, by rfl⟩ : syracuseStep 1918631 = 2877947) B2877947
theorem B2158465 : Blo 1917435 2158465 := bbase (se 2 (by rfl) ⟨809424, by rfl⟩ : syracuseStep 2158465 = 1618849) (by norm_num)
theorem B2877953 : Blo 1917435 2877953 := bstep (se 2 (by rfl) ⟨1079232, by rfl⟩ : syracuseStep 2877953 = 2158465) B2158465
theorem B1918635 : Blo 1917435 1918635 := bstep (se 1 (by rfl) ⟨1438976, by rfl⟩ : syracuseStep 1918635 = 2877953) B2877953
theorem B4856557 : Blo 1917435 4856557 := bbase (se 3 (by rfl) ⟨910604, by rfl⟩ : syracuseStep 4856557 = 1821209) (by norm_num)
theorem B6475409 : Blo 1917435 6475409 := bstep (se 2 (by rfl) ⟨2428278, by rfl⟩ : syracuseStep 6475409 = 4856557) B4856557
theorem B4316939 : Blo 1917435 4316939 := bstep (se 1 (by rfl) ⟨3237704, by rfl⟩ : syracuseStep 4316939 = 6475409) B6475409
theorem B2877959 : Blo 1917435 2877959 := bstep (se 1 (by rfl) ⟨2158469, by rfl⟩ : syracuseStep 2877959 = 4316939) B4316939
theorem B1918639 : Blo 1917435 1918639 := bstep (se 1 (by rfl) ⟨1438979, by rfl⟩ : syracuseStep 1918639 = 2877959) B2877959
theorem B2877965 : Blo 1917435 2877965 := bbase (se 3 (by rfl) ⟨539618, by rfl⟩ : syracuseStep 2877965 = 1079237) (by norm_num)
theorem B1918643 : Blo 1917435 1918643 := bstep (se 1 (by rfl) ⟨1438982, by rfl⟩ : syracuseStep 1918643 = 2877965) B2877965
theorem B4316957 : Blo 1917435 4316957 := bbase (se 3 (by rfl) ⟨809429, by rfl⟩ : syracuseStep 4316957 = 1618859) (by norm_num)
theorem B2877971 : Blo 1917435 2877971 := bstep (se 1 (by rfl) ⟨2158478, by rfl⟩ : syracuseStep 2877971 = 4316957) B4316957
theorem B1918647 : Blo 1917435 1918647 := bstep (se 1 (by rfl) ⟨1438985, by rfl⟩ : syracuseStep 1918647 = 2877971) B2877971
theorem B3237725 : Blo 1917435 3237725 := bbase (se 3 (by rfl) ⟨607073, by rfl⟩ : syracuseStep 3237725 = 1214147) (by norm_num)
theorem B2158483 : Blo 1917435 2158483 := bstep (se 1 (by rfl) ⟨1618862, by rfl⟩ : syracuseStep 2158483 = 3237725) B3237725
theorem B2877977 : Blo 1917435 2877977 := bstep (se 2 (by rfl) ⟨1079241, by rfl⟩ : syracuseStep 2877977 = 2158483) B2158483
theorem B1918651 : Blo 1917435 1918651 := bstep (se 1 (by rfl) ⟨1438988, by rfl⟩ : syracuseStep 1918651 = 2877977) B2877977
theorem B8195509 : Blo 1917435 8195509 := bbase (se 5 (by rfl) ⟨384164, by rfl⟩ : syracuseStep 8195509 = 768329) (by norm_num)
theorem B10927345 : Blo 1917435 10927345 := bstep (se 2 (by rfl) ⟨4097754, by rfl⟩ : syracuseStep 10927345 = 8195509) B8195509
theorem B14569793 : Blo 1917435 14569793 := bstep (se 2 (by rfl) ⟨5463672, by rfl⟩ : syracuseStep 14569793 = 10927345) B10927345
theorem B9713195 : Blo 1917435 9713195 := bstep (se 1 (by rfl) ⟨7284896, by rfl⟩ : syracuseStep 9713195 = 14569793) B14569793
theorem B6475463 : Blo 1917435 6475463 := bstep (se 1 (by rfl) ⟨4856597, by rfl⟩ : syracuseStep 6475463 = 9713195) B9713195
theorem B4316975 : Blo 1917435 4316975 := bstep (se 1 (by rfl) ⟨3237731, by rfl⟩ : syracuseStep 4316975 = 6475463) B6475463
theorem B2877983 : Blo 1917435 2877983 := bstep (se 1 (by rfl) ⟨2158487, by rfl⟩ : syracuseStep 2877983 = 4316975) B4316975
theorem B1918655 : Blo 1917435 1918655 := bstep (se 1 (by rfl) ⟨1438991, by rfl⟩ : syracuseStep 1918655 = 2877983) B2877983
theorem B2877989 : Blo 1917435 2877989 := bbase (se 4 (by rfl) ⟨269811, by rfl⟩ : syracuseStep 2877989 = 539623) (by norm_num)
theorem B1918659 : Blo 1917435 1918659 := bstep (se 1 (by rfl) ⟨1438994, by rfl⟩ : syracuseStep 1918659 = 2877989) B2877989
theorem B2428309 : Blo 1917435 2428309 := bbase (se 6 (by rfl) ⟨56913, by rfl⟩ : syracuseStep 2428309 = 113827) (by norm_num)
theorem B3237745 : Blo 1917435 3237745 := bstep (se 2 (by rfl) ⟨1214154, by rfl⟩ : syracuseStep 3237745 = 2428309) B2428309
theorem B4316993 : Blo 1917435 4316993 := bstep (se 2 (by rfl) ⟨1618872, by rfl⟩ : syracuseStep 4316993 = 3237745) B3237745
theorem B2877995 : Blo 1917435 2877995 := bstep (se 1 (by rfl) ⟨2158496, by rfl⟩ : syracuseStep 2877995 = 4316993) B4316993
theorem B1918663 : Blo 1917435 1918663 := bstep (se 1 (by rfl) ⟨1438997, by rfl⟩ : syracuseStep 1918663 = 2877995) B2877995
theorem B2158501 : Blo 1917435 2158501 := bbase (se 4 (by rfl) ⟨202359, by rfl⟩ : syracuseStep 2158501 = 404719) (by norm_num)
theorem B2878001 : Blo 1917435 2878001 := bstep (se 2 (by rfl) ⟨1079250, by rfl⟩ : syracuseStep 2878001 = 2158501) B2158501
theorem B1918667 : Blo 1917435 1918667 := bstep (se 1 (by rfl) ⟨1439000, by rfl⟩ : syracuseStep 1918667 = 2878001) B2878001
theorem B5834549 : Blo 1917435 5834549 := bbase (se 5 (by rfl) ⟨273494, by rfl⟩ : syracuseStep 5834549 = 546989) (by norm_num)
theorem B15558797 : Blo 1917435 15558797 := bstep (se 3 (by rfl) ⟨2917274, by rfl⟩ : syracuseStep 15558797 = 5834549) B5834549
theorem B10372531 : Blo 1917435 10372531 := bstep (se 1 (by rfl) ⟨7779398, by rfl⟩ : syracuseStep 10372531 = 15558797) B15558797
theorem B13830041 : Blo 1917435 13830041 := bstep (se 2 (by rfl) ⟨5186265, by rfl⟩ : syracuseStep 13830041 = 10372531) B10372531
theorem B9220027 : Blo 1917435 9220027 := bstep (se 1 (by rfl) ⟨6915020, by rfl⟩ : syracuseStep 9220027 = 13830041) B13830041
theorem B12293369 : Blo 1917435 12293369 := bstep (se 2 (by rfl) ⟨4610013, by rfl⟩ : syracuseStep 12293369 = 9220027) B9220027
theorem B8195579 : Blo 1917435 8195579 := bstep (se 1 (by rfl) ⟨6146684, by rfl⟩ : syracuseStep 8195579 = 12293369) B12293369
theorem B5463719 : Blo 1917435 5463719 := bstep (se 1 (by rfl) ⟨4097789, by rfl⟩ : syracuseStep 5463719 = 8195579) B8195579
theorem B3642479 : Blo 1917435 3642479 := bstep (se 1 (by rfl) ⟨2731859, by rfl⟩ : syracuseStep 3642479 = 5463719) B5463719
theorem B2428319 : Blo 1917435 2428319 := bstep (se 1 (by rfl) ⟨1821239, by rfl⟩ : syracuseStep 2428319 = 3642479) B3642479
theorem B6475517 : Blo 1917435 6475517 := bstep (se 3 (by rfl) ⟨1214159, by rfl⟩ : syracuseStep 6475517 = 2428319) B2428319
theorem B4317011 : Blo 1917435 4317011 := bstep (se 1 (by rfl) ⟨3237758, by rfl⟩ : syracuseStep 4317011 = 6475517) B6475517
theorem B2878007 : Blo 1917435 2878007 := bstep (se 1 (by rfl) ⟨2158505, by rfl⟩ : syracuseStep 2878007 = 4317011) B4317011
theorem B1918671 : Blo 1917435 1918671 := bstep (se 1 (by rfl) ⟨1439003, by rfl⟩ : syracuseStep 1918671 = 2878007) B2878007
theorem B2878013 : Blo 1917435 2878013 := bbase (se 3 (by rfl) ⟨539627, by rfl⟩ : syracuseStep 2878013 = 1079255) (by norm_num)
theorem B1918675 : Blo 1917435 1918675 := bstep (se 1 (by rfl) ⟨1439006, by rfl⟩ : syracuseStep 1918675 = 2878013) B2878013
theorem B4317029 : Blo 1917435 4317029 := bbase (se 4 (by rfl) ⟨404721, by rfl⟩ : syracuseStep 4317029 = 809443) (by norm_num)
theorem B2878019 : Blo 1917435 2878019 := bstep (se 1 (by rfl) ⟨2158514, by rfl⟩ : syracuseStep 2878019 = 4317029) B4317029
theorem B1918679 : Blo 1917435 1918679 := bstep (se 1 (by rfl) ⟨1439009, by rfl⟩ : syracuseStep 1918679 = 2878019) B2878019
theorem B4856669 : Blo 1917435 4856669 := bbase (se 3 (by rfl) ⟨910625, by rfl⟩ : syracuseStep 4856669 = 1821251) (by norm_num)
theorem B3237779 : Blo 1917435 3237779 := bstep (se 1 (by rfl) ⟨2428334, by rfl⟩ : syracuseStep 3237779 = 4856669) B4856669
theorem B2158519 : Blo 1917435 2158519 := bstep (se 1 (by rfl) ⟨1618889, by rfl⟩ : syracuseStep 2158519 = 3237779) B3237779
theorem B2878025 : Blo 1917435 2878025 := bstep (se 2 (by rfl) ⟨1079259, by rfl⟩ : syracuseStep 2878025 = 2158519) B2158519
theorem B1918683 : Blo 1917435 1918683 := bstep (se 1 (by rfl) ⟨1439012, by rfl⟩ : syracuseStep 1918683 = 2878025) B2878025
theorem B3642509 : Blo 1917435 3642509 := bbase (se 3 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 3642509 = 1365941) (by norm_num)
theorem B9713357 : Blo 1917435 9713357 := bstep (se 3 (by rfl) ⟨1821254, by rfl⟩ : syracuseStep 9713357 = 3642509) B3642509
theorem B6475571 : Blo 1917435 6475571 := bstep (se 1 (by rfl) ⟨4856678, by rfl⟩ : syracuseStep 6475571 = 9713357) B9713357
theorem B4317047 : Blo 1917435 4317047 := bstep (se 1 (by rfl) ⟨3237785, by rfl⟩ : syracuseStep 4317047 = 6475571) B6475571
theorem B2878031 : Blo 1917435 2878031 := bstep (se 1 (by rfl) ⟨2158523, by rfl⟩ : syracuseStep 2878031 = 4317047) B4317047
theorem B1918687 : Blo 1917435 1918687 := bstep (se 1 (by rfl) ⟨1439015, by rfl⟩ : syracuseStep 1918687 = 2878031) B2878031
theorem B2878037 : Blo 1917435 2878037 := bbase (se 8 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 2878037 = 33727) (by norm_num)
theorem B1918691 : Blo 1917435 1918691 := bstep (se 1 (by rfl) ⟨1439018, by rfl⟩ : syracuseStep 1918691 = 2878037) B2878037
theorem B10372661 : Blo 1917435 10372661 := bbase (se 5 (by rfl) ⟨486218, by rfl⟩ : syracuseStep 10372661 = 972437) (by norm_num)
theorem B6915107 : Blo 1917435 6915107 := bstep (se 1 (by rfl) ⟨5186330, by rfl⟩ : syracuseStep 6915107 = 10372661) B10372661
theorem B4610071 : Blo 1917435 4610071 := bstep (se 1 (by rfl) ⟨3457553, by rfl⟩ : syracuseStep 4610071 = 6915107) B6915107
theorem B6146761 : Blo 1917435 6146761 := bstep (se 2 (by rfl) ⟨2305035, by rfl⟩ : syracuseStep 6146761 = 4610071) B4610071
theorem B8195681 : Blo 1917435 8195681 := bstep (se 2 (by rfl) ⟨3073380, by rfl⟩ : syracuseStep 8195681 = 6146761) B6146761
theorem B5463787 : Blo 1917435 5463787 := bstep (se 1 (by rfl) ⟨4097840, by rfl⟩ : syracuseStep 5463787 = 8195681) B8195681
theorem B7285049 : Blo 1917435 7285049 := bstep (se 2 (by rfl) ⟨2731893, by rfl⟩ : syracuseStep 7285049 = 5463787) B5463787
theorem B4856699 : Blo 1917435 4856699 := bstep (se 1 (by rfl) ⟨3642524, by rfl⟩ : syracuseStep 4856699 = 7285049) B7285049
theorem B3237799 : Blo 1917435 3237799 := bstep (se 1 (by rfl) ⟨2428349, by rfl⟩ : syracuseStep 3237799 = 4856699) B4856699
theorem B4317065 : Blo 1917435 4317065 := bstep (se 2 (by rfl) ⟨1618899, by rfl⟩ : syracuseStep 4317065 = 3237799) B3237799
theorem B2878043 : Blo 1917435 2878043 := bstep (se 1 (by rfl) ⟨2158532, by rfl⟩ : syracuseStep 2878043 = 4317065) B4317065
theorem B1918695 : Blo 1917435 1918695 := bstep (se 1 (by rfl) ⟨1439021, by rfl⟩ : syracuseStep 1918695 = 2878043) B2878043
theorem B2158537 : Blo 1917435 2158537 := bbase (se 2 (by rfl) ⟨809451, by rfl⟩ : syracuseStep 2158537 = 1618903) (by norm_num)
theorem B2878049 : Blo 1917435 2878049 := bstep (se 2 (by rfl) ⟨1079268, by rfl⟩ : syracuseStep 2878049 = 2158537) B2158537
theorem B1918699 : Blo 1917435 1918699 := bstep (se 1 (by rfl) ⟨1439024, by rfl⟩ : syracuseStep 1918699 = 2878049) B2878049
theorem B2305045 : Blo 1917435 2305045 := bbase (se 6 (by rfl) ⟨54024, by rfl⟩ : syracuseStep 2305045 = 108049) (by norm_num)
theorem B3073393 : Blo 1917435 3073393 := bstep (se 2 (by rfl) ⟨1152522, by rfl⟩ : syracuseStep 3073393 = 2305045) B2305045
theorem B16391429 : Blo 1917435 16391429 := bstep (se 4 (by rfl) ⟨1536696, by rfl⟩ : syracuseStep 16391429 = 3073393) B3073393
theorem B10927619 : Blo 1917435 10927619 := bstep (se 1 (by rfl) ⟨8195714, by rfl⟩ : syracuseStep 10927619 = 16391429) B16391429
theorem B7285079 : Blo 1917435 7285079 := bstep (se 1 (by rfl) ⟨5463809, by rfl⟩ : syracuseStep 7285079 = 10927619) B10927619
theorem B4856719 : Blo 1917435 4856719 := bstep (se 1 (by rfl) ⟨3642539, by rfl⟩ : syracuseStep 4856719 = 7285079) B7285079
theorem B6475625 : Blo 1917435 6475625 := bstep (se 2 (by rfl) ⟨2428359, by rfl⟩ : syracuseStep 6475625 = 4856719) B4856719
theorem B4317083 : Blo 1917435 4317083 := bstep (se 1 (by rfl) ⟨3237812, by rfl⟩ : syracuseStep 4317083 = 6475625) B6475625
theorem B2878055 : Blo 1917435 2878055 := bstep (se 1 (by rfl) ⟨2158541, by rfl⟩ : syracuseStep 2878055 = 4317083) B4317083
theorem B1918703 : Blo 1917435 1918703 := bstep (se 1 (by rfl) ⟨1439027, by rfl⟩ : syracuseStep 1918703 = 2878055) B2878055
theorem B2878061 : Blo 1917435 2878061 := bbase (se 3 (by rfl) ⟨539636, by rfl⟩ : syracuseStep 2878061 = 1079273) (by norm_num)
theorem B1918707 : Blo 1917435 1918707 := bstep (se 1 (by rfl) ⟨1439030, by rfl⟩ : syracuseStep 1918707 = 2878061) B2878061
theorem B4317101 : Blo 1917435 4317101 := bbase (se 3 (by rfl) ⟨809456, by rfl⟩ : syracuseStep 4317101 = 1618913) (by norm_num)
theorem B2878067 : Blo 1917435 2878067 := bstep (se 1 (by rfl) ⟨2158550, by rfl⟩ : syracuseStep 2878067 = 4317101) B4317101
theorem B1918711 : Blo 1917435 1918711 := bstep (se 1 (by rfl) ⟨1439033, by rfl⟩ : syracuseStep 1918711 = 2878067) B2878067
theorem B5463845 : Blo 1917435 5463845 := bbase (se 4 (by rfl) ⟨512235, by rfl⟩ : syracuseStep 5463845 = 1024471) (by norm_num)
theorem B3642563 : Blo 1917435 3642563 := bstep (se 1 (by rfl) ⟨2731922, by rfl⟩ : syracuseStep 3642563 = 5463845) B5463845
theorem B2428375 : Blo 1917435 2428375 := bstep (se 1 (by rfl) ⟨1821281, by rfl⟩ : syracuseStep 2428375 = 3642563) B3642563
theorem B3237833 : Blo 1917435 3237833 := bstep (se 2 (by rfl) ⟨1214187, by rfl⟩ : syracuseStep 3237833 = 2428375) B2428375
theorem B2158555 : Blo 1917435 2158555 := bstep (se 1 (by rfl) ⟨1618916, by rfl⟩ : syracuseStep 2158555 = 3237833) B3237833
theorem B2878073 : Blo 1917435 2878073 := bstep (se 2 (by rfl) ⟨1079277, by rfl⟩ : syracuseStep 2878073 = 2158555) B2158555
theorem B1918715 : Blo 1917435 1918715 := bstep (se 1 (by rfl) ⟨1439036, by rfl⟩ : syracuseStep 1918715 = 2878073) B2878073
theorem B4990189 : Blo 1917435 4990189 := bbase (se 3 (by rfl) ⟨935660, by rfl⟩ : syracuseStep 4990189 = 1871321) (by norm_num)
theorem B6653585 : Blo 1917435 6653585 := bstep (se 2 (by rfl) ⟨2495094, by rfl⟩ : syracuseStep 6653585 = 4990189) B4990189
theorem B17742893 : Blo 1917435 17742893 := bstep (se 3 (by rfl) ⟨3326792, by rfl⟩ : syracuseStep 17742893 = 6653585) B6653585
theorem B189257525 : Blo 1917435 189257525 := bstep (se 5 (by rfl) ⟨8871446, by rfl⟩ : syracuseStep 189257525 = 17742893) B17742893
theorem B126171683 : Blo 1917435 126171683 := bstep (se 1 (by rfl) ⟨94628762, by rfl⟩ : syracuseStep 126171683 = 189257525) B189257525
theorem B84114455 : Blo 1917435 84114455 := bstep (se 1 (by rfl) ⟨63085841, by rfl⟩ : syracuseStep 84114455 = 126171683) B126171683
theorem B224305213 : Blo 1917435 224305213 := bstep (se 3 (by rfl) ⟨42057227, by rfl⟩ : syracuseStep 224305213 = 84114455) B84114455
theorem B299073617 : Blo 1917435 299073617 := bstep (se 2 (by rfl) ⟨112152606, by rfl⟩ : syracuseStep 299073617 = 224305213) B224305213
theorem B199382411 : Blo 1917435 199382411 := bstep (se 1 (by rfl) ⟨149536808, by rfl⟩ : syracuseStep 199382411 = 299073617) B299073617
theorem B132921607 : Blo 1917435 132921607 := bstep (se 1 (by rfl) ⟨99691205, by rfl⟩ : syracuseStep 132921607 = 199382411) B199382411
theorem B177228809 : Blo 1917435 177228809 := bstep (se 2 (by rfl) ⟨66460803, by rfl⟩ : syracuseStep 177228809 = 132921607) B132921607
theorem B118152539 : Blo 1917435 118152539 := bstep (se 1 (by rfl) ⟨88614404, by rfl⟩ : syracuseStep 118152539 = 177228809) B177228809
theorem B78768359 : Blo 1917435 78768359 := bstep (se 1 (by rfl) ⟨59076269, by rfl⟩ : syracuseStep 78768359 = 118152539) B118152539
theorem B52512239 : Blo 1917435 52512239 := bstep (se 1 (by rfl) ⟨39384179, by rfl⟩ : syracuseStep 52512239 = 78768359) B78768359
theorem B35008159 : Blo 1917435 35008159 := bstep (se 1 (by rfl) ⟨26256119, by rfl⟩ : syracuseStep 35008159 = 52512239) B52512239
theorem B46677545 : Blo 1917435 46677545 := bstep (se 2 (by rfl) ⟨17504079, by rfl⟩ : syracuseStep 46677545 = 35008159) B35008159
theorem B31118363 : Blo 1917435 31118363 := bstep (se 1 (by rfl) ⟨23338772, by rfl⟩ : syracuseStep 31118363 = 46677545) B46677545
theorem B20745575 : Blo 1917435 20745575 := bstep (se 1 (by rfl) ⟨15559181, by rfl⟩ : syracuseStep 20745575 = 31118363) B31118363
theorem B13830383 : Blo 1917435 13830383 := bstep (se 1 (by rfl) ⟨10372787, by rfl⟩ : syracuseStep 13830383 = 20745575) B20745575
theorem B36881021 : Blo 1917435 36881021 := bstep (se 3 (by rfl) ⟨6915191, by rfl⟩ : syracuseStep 36881021 = 13830383) B13830383
theorem B24587347 : Blo 1917435 24587347 := bstep (se 1 (by rfl) ⟨18440510, by rfl⟩ : syracuseStep 24587347 = 36881021) B36881021
theorem B32783129 : Blo 1917435 32783129 := bstep (se 2 (by rfl) ⟨12293673, by rfl⟩ : syracuseStep 32783129 = 24587347) B24587347
theorem B21855419 : Blo 1917435 21855419 := bstep (se 1 (by rfl) ⟨16391564, by rfl⟩ : syracuseStep 21855419 = 32783129) B32783129
theorem B14570279 : Blo 1917435 14570279 := bstep (se 1 (by rfl) ⟨10927709, by rfl⟩ : syracuseStep 14570279 = 21855419) B21855419
theorem B9713519 : Blo 1917435 9713519 := bstep (se 1 (by rfl) ⟨7285139, by rfl⟩ : syracuseStep 9713519 = 14570279) B14570279
theorem B6475679 : Blo 1917435 6475679 := bstep (se 1 (by rfl) ⟨4856759, by rfl⟩ : syracuseStep 6475679 = 9713519) B9713519
theorem B4317119 : Blo 1917435 4317119 := bstep (se 1 (by rfl) ⟨3237839, by rfl⟩ : syracuseStep 4317119 = 6475679) B6475679
theorem B2878079 : Blo 1917435 2878079 := bstep (se 1 (by rfl) ⟨2158559, by rfl⟩ : syracuseStep 2878079 = 4317119) B4317119
theorem B1918719 : Blo 1917435 1918719 := bstep (se 1 (by rfl) ⟨1439039, by rfl⟩ : syracuseStep 1918719 = 2878079) B2878079
theorem B2878085 : Blo 1917435 2878085 := bbase (se 4 (by rfl) ⟨269820, by rfl⟩ : syracuseStep 2878085 = 539641) (by norm_num)
theorem B1918723 : Blo 1917435 1918723 := bstep (se 1 (by rfl) ⟨1439042, by rfl⟩ : syracuseStep 1918723 = 2878085) B2878085
theorem B3237853 : Blo 1917435 3237853 := bbase (se 3 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 3237853 = 1214195) (by norm_num)
theorem B4317137 : Blo 1917435 4317137 := bstep (se 2 (by rfl) ⟨1618926, by rfl⟩ : syracuseStep 4317137 = 3237853) B3237853
theorem B2878091 : Blo 1917435 2878091 := bstep (se 1 (by rfl) ⟨2158568, by rfl⟩ : syracuseStep 2878091 = 4317137) B4317137
theorem B1918727 : Blo 1917435 1918727 := bstep (se 1 (by rfl) ⟨1439045, by rfl⟩ : syracuseStep 1918727 = 2878091) B2878091
theorem B2158573 : Blo 1917435 2158573 := bbase (se 3 (by rfl) ⟨404732, by rfl⟩ : syracuseStep 2158573 = 809465) (by norm_num)
theorem B2878097 : Blo 1917435 2878097 := bstep (se 2 (by rfl) ⟨1079286, by rfl⟩ : syracuseStep 2878097 = 2158573) B2158573
theorem B1918731 : Blo 1917435 1918731 := bstep (se 1 (by rfl) ⟨1439048, by rfl⟩ : syracuseStep 1918731 = 2878097) B2878097
theorem B6475733 : Blo 1917435 6475733 := bbase (se 7 (by rfl) ⟨75887, by rfl⟩ : syracuseStep 6475733 = 151775) (by norm_num)
theorem B4317155 : Blo 1917435 4317155 := bstep (se 1 (by rfl) ⟨3237866, by rfl⟩ : syracuseStep 4317155 = 6475733) B6475733
theorem B2878103 : Blo 1917435 2878103 := bstep (se 1 (by rfl) ⟨2158577, by rfl⟩ : syracuseStep 2878103 = 4317155) B4317155
theorem B1918735 : Blo 1917435 1918735 := bstep (se 1 (by rfl) ⟨1439051, by rfl⟩ : syracuseStep 1918735 = 2878103) B2878103
theorem B2878109 : Blo 1917435 2878109 := bbase (se 3 (by rfl) ⟨539645, by rfl⟩ : syracuseStep 2878109 = 1079291) (by norm_num)
theorem B1918739 : Blo 1917435 1918739 := bstep (se 1 (by rfl) ⟨1439054, by rfl⟩ : syracuseStep 1918739 = 2878109) B2878109
theorem B4317173 : Blo 1917435 4317173 := bbase (se 5 (by rfl) ⟨202367, by rfl⟩ : syracuseStep 4317173 = 404735) (by norm_num)
theorem B2878115 : Blo 1917435 2878115 := bstep (se 1 (by rfl) ⟨2158586, by rfl⟩ : syracuseStep 2878115 = 4317173) B4317173
theorem B1918743 : Blo 1917435 1918743 := bstep (se 1 (by rfl) ⟨1439057, by rfl⟩ : syracuseStep 1918743 = 2878115) B2878115
theorem B9473701 : Blo 1917435 9473701 := bbase (se 4 (by rfl) ⟨888159, by rfl⟩ : syracuseStep 9473701 = 1776319) (by norm_num)
theorem B202105621 : Blo 1917435 202105621 := bstep (se 6 (by rfl) ⟨4736850, by rfl⟩ : syracuseStep 202105621 = 9473701) B9473701
theorem B1077896645 : Blo 1917435 1077896645 := bstep (se 4 (by rfl) ⟨101052810, by rfl⟩ : syracuseStep 1077896645 = 202105621) B202105621
theorem B718597763 : Blo 1917435 718597763 := bstep (se 1 (by rfl) ⟨538948322, by rfl⟩ : syracuseStep 718597763 = 1077896645) B1077896645
theorem B479065175 : Blo 1917435 479065175 := bstep (se 1 (by rfl) ⟨359298881, by rfl⟩ : syracuseStep 479065175 = 718597763) B718597763
theorem B319376783 : Blo 1917435 319376783 := bstep (se 1 (by rfl) ⟨239532587, by rfl⟩ : syracuseStep 319376783 = 479065175) B479065175
theorem B212917855 : Blo 1917435 212917855 := bstep (se 1 (by rfl) ⟨159688391, by rfl⟩ : syracuseStep 212917855 = 319376783) B319376783
theorem B283890473 : Blo 1917435 283890473 := bstep (se 2 (by rfl) ⟨106458927, by rfl⟩ : syracuseStep 283890473 = 212917855) B212917855
theorem B189260315 : Blo 1917435 189260315 := bstep (se 1 (by rfl) ⟨141945236, by rfl⟩ : syracuseStep 189260315 = 283890473) B283890473
theorem B126173543 : Blo 1917435 126173543 := bstep (se 1 (by rfl) ⟨94630157, by rfl⟩ : syracuseStep 126173543 = 189260315) B189260315
theorem B336462781 : Blo 1917435 336462781 := bstep (se 3 (by rfl) ⟨63086771, by rfl⟩ : syracuseStep 336462781 = 126173543) B126173543
theorem B448617041 : Blo 1917435 448617041 := bstep (se 2 (by rfl) ⟨168231390, by rfl⟩ : syracuseStep 448617041 = 336462781) B336462781
theorem B299078027 : Blo 1917435 299078027 := bstep (se 1 (by rfl) ⟨224308520, by rfl⟩ : syracuseStep 299078027 = 448617041) B448617041
theorem B199385351 : Blo 1917435 199385351 := bstep (se 1 (by rfl) ⟨149539013, by rfl⟩ : syracuseStep 199385351 = 299078027) B299078027
theorem B132923567 : Blo 1917435 132923567 := bstep (se 1 (by rfl) ⟨99692675, by rfl⟩ : syracuseStep 132923567 = 199385351) B199385351
theorem B88615711 : Blo 1917435 88615711 := bstep (se 1 (by rfl) ⟨66461783, by rfl⟩ : syracuseStep 88615711 = 132923567) B132923567
theorem B472617125 : Blo 1917435 472617125 := bstep (se 4 (by rfl) ⟨44307855, by rfl⟩ : syracuseStep 472617125 = 88615711) B88615711
theorem B315078083 : Blo 1917435 315078083 := bstep (se 1 (by rfl) ⟨236308562, by rfl⟩ : syracuseStep 315078083 = 472617125) B472617125
theorem B210052055 : Blo 1917435 210052055 := bstep (se 1 (by rfl) ⟨157539041, by rfl⟩ : syracuseStep 210052055 = 315078083) B315078083
theorem B140034703 : Blo 1917435 140034703 := bstep (se 1 (by rfl) ⟨105026027, by rfl⟩ : syracuseStep 140034703 = 210052055) B210052055
theorem B186712937 : Blo 1917435 186712937 := bstep (se 2 (by rfl) ⟨70017351, by rfl⟩ : syracuseStep 186712937 = 140034703) B140034703
theorem B124475291 : Blo 1917435 124475291 := bstep (se 1 (by rfl) ⟨93356468, by rfl⟩ : syracuseStep 124475291 = 186712937) B186712937
theorem B82983527 : Blo 1917435 82983527 := bstep (se 1 (by rfl) ⟨62237645, by rfl⟩ : syracuseStep 82983527 = 124475291) B124475291
theorem B55322351 : Blo 1917435 55322351 := bstep (se 1 (by rfl) ⟨41491763, by rfl⟩ : syracuseStep 55322351 = 82983527) B82983527
theorem B36881567 : Blo 1917435 36881567 := bstep (se 1 (by rfl) ⟨27661175, by rfl⟩ : syracuseStep 36881567 = 55322351) B55322351
theorem B24587711 : Blo 1917435 24587711 := bstep (se 1 (by rfl) ⟨18440783, by rfl⟩ : syracuseStep 24587711 = 36881567) B36881567
theorem B16391807 : Blo 1917435 16391807 := bstep (se 1 (by rfl) ⟨12293855, by rfl⟩ : syracuseStep 16391807 = 24587711) B24587711
theorem B10927871 : Blo 1917435 10927871 := bstep (se 1 (by rfl) ⟨8195903, by rfl⟩ : syracuseStep 10927871 = 16391807) B16391807
theorem B7285247 : Blo 1917435 7285247 := bstep (se 1 (by rfl) ⟨5463935, by rfl⟩ : syracuseStep 7285247 = 10927871) B10927871
theorem B4856831 : Blo 1917435 4856831 := bstep (se 1 (by rfl) ⟨3642623, by rfl⟩ : syracuseStep 4856831 = 7285247) B7285247
theorem B3237887 : Blo 1917435 3237887 := bstep (se 1 (by rfl) ⟨2428415, by rfl⟩ : syracuseStep 3237887 = 4856831) B4856831
theorem B2158591 : Blo 1917435 2158591 := bstep (se 1 (by rfl) ⟨1618943, by rfl⟩ : syracuseStep 2158591 = 3237887) B3237887
theorem B2878121 : Blo 1917435 2878121 := bstep (se 2 (by rfl) ⟨1079295, by rfl⟩ : syracuseStep 2878121 = 2158591) B2158591
theorem B1918747 : Blo 1917435 1918747 := bstep (se 1 (by rfl) ⟨1439060, by rfl⟩ : syracuseStep 1918747 = 2878121) B2878121
theorem B2731973 : Blo 1917435 2731973 := bbase (se 4 (by rfl) ⟨256122, by rfl⟩ : syracuseStep 2731973 = 512245) (by norm_num)
theorem B7285261 : Blo 1917435 7285261 := bstep (se 3 (by rfl) ⟨1365986, by rfl⟩ : syracuseStep 7285261 = 2731973) B2731973
theorem B9713681 : Blo 1917435 9713681 := bstep (se 2 (by rfl) ⟨3642630, by rfl⟩ : syracuseStep 9713681 = 7285261) B7285261
theorem B6475787 : Blo 1917435 6475787 := bstep (se 1 (by rfl) ⟨4856840, by rfl⟩ : syracuseStep 6475787 = 9713681) B9713681
theorem B4317191 : Blo 1917435 4317191 := bstep (se 1 (by rfl) ⟨3237893, by rfl⟩ : syracuseStep 4317191 = 6475787) B6475787
theorem B2878127 : Blo 1917435 2878127 := bstep (se 1 (by rfl) ⟨2158595, by rfl⟩ : syracuseStep 2878127 = 4317191) B4317191
theorem B1918751 : Blo 1917435 1918751 := bstep (se 1 (by rfl) ⟨1439063, by rfl⟩ : syracuseStep 1918751 = 2878127) B2878127
theorem B2878133 : Blo 1917435 2878133 := bbase (se 5 (by rfl) ⟨134912, by rfl⟩ : syracuseStep 2878133 = 269825) (by norm_num)
theorem B1918755 : Blo 1917435 1918755 := bstep (se 1 (by rfl) ⟨1439066, by rfl⟩ : syracuseStep 1918755 = 2878133) B2878133
theorem B4856861 : Blo 1917435 4856861 := bbase (se 3 (by rfl) ⟨910661, by rfl⟩ : syracuseStep 4856861 = 1821323) (by norm_num)
theorem B3237907 : Blo 1917435 3237907 := bstep (se 1 (by rfl) ⟨2428430, by rfl⟩ : syracuseStep 3237907 = 4856861) B4856861
theorem B4317209 : Blo 1917435 4317209 := bstep (se 2 (by rfl) ⟨1618953, by rfl⟩ : syracuseStep 4317209 = 3237907) B3237907
theorem B2878139 : Blo 1917435 2878139 := bstep (se 1 (by rfl) ⟨2158604, by rfl⟩ : syracuseStep 2878139 = 4317209) B4317209
theorem B1918759 : Blo 1917435 1918759 := bstep (se 1 (by rfl) ⟨1439069, by rfl⟩ : syracuseStep 1918759 = 2878139) B2878139
theorem B2158609 : Blo 1917435 2158609 := bbase (se 2 (by rfl) ⟨809478, by rfl⟩ : syracuseStep 2158609 = 1618957) (by norm_num)
theorem B2878145 : Blo 1917435 2878145 := bstep (se 2 (by rfl) ⟨1079304, by rfl⟩ : syracuseStep 2878145 = 2158609) B2158609
theorem B1918763 : Blo 1917435 1918763 := bstep (se 1 (by rfl) ⟨1439072, by rfl⟩ : syracuseStep 1918763 = 2878145) B2878145
theorem B3642661 : Blo 1917435 3642661 := bbase (se 4 (by rfl) ⟨341499, by rfl⟩ : syracuseStep 3642661 = 682999) (by norm_num)
theorem B4856881 : Blo 1917435 4856881 := bstep (se 2 (by rfl) ⟨1821330, by rfl⟩ : syracuseStep 4856881 = 3642661) B3642661
theorem B6475841 : Blo 1917435 6475841 := bstep (se 2 (by rfl) ⟨2428440, by rfl⟩ : syracuseStep 6475841 = 4856881) B4856881
theorem B4317227 : Blo 1917435 4317227 := bstep (se 1 (by rfl) ⟨3237920, by rfl⟩ : syracuseStep 4317227 = 6475841) B6475841
theorem B2878151 : Blo 1917435 2878151 := bstep (se 1 (by rfl) ⟨2158613, by rfl⟩ : syracuseStep 2878151 = 4317227) B4317227
theorem B1918767 : Blo 1917435 1918767 := bstep (se 1 (by rfl) ⟨1439075, by rfl⟩ : syracuseStep 1918767 = 2878151) B2878151
theorem B2878157 : Blo 1917435 2878157 := bbase (se 3 (by rfl) ⟨539654, by rfl⟩ : syracuseStep 2878157 = 1079309) (by norm_num)
theorem B1918771 : Blo 1917435 1918771 := bstep (se 1 (by rfl) ⟨1439078, by rfl⟩ : syracuseStep 1918771 = 2878157) B2878157
theorem B4317245 : Blo 1917435 4317245 := bbase (se 3 (by rfl) ⟨809483, by rfl⟩ : syracuseStep 4317245 = 1618967) (by norm_num)
theorem B2878163 : Blo 1917435 2878163 := bstep (se 1 (by rfl) ⟨2158622, by rfl⟩ : syracuseStep 2878163 = 4317245) B4317245
theorem B1918775 : Blo 1917435 1918775 := bstep (se 1 (by rfl) ⟨1439081, by rfl⟩ : syracuseStep 1918775 = 2878163) B2878163
theorem B3237941 : Blo 1917435 3237941 := bbase (se 5 (by rfl) ⟨151778, by rfl⟩ : syracuseStep 3237941 = 303557) (by norm_num)
theorem B2158627 : Blo 1917435 2158627 := bstep (se 1 (by rfl) ⟨1618970, by rfl⟩ : syracuseStep 2158627 = 3237941) B3237941
theorem B2878169 : Blo 1917435 2878169 := bstep (se 2 (by rfl) ⟨1079313, by rfl⟩ : syracuseStep 2878169 = 2158627) B2158627
theorem B1918779 : Blo 1917435 1918779 := bstep (se 1 (by rfl) ⟨1439084, by rfl⟩ : syracuseStep 1918779 = 2878169) B2878169
theorem B5464037 : Blo 1917435 5464037 := bbase (se 4 (by rfl) ⟨512253, by rfl⟩ : syracuseStep 5464037 = 1024507) (by norm_num)
theorem B14570765 : Blo 1917435 14570765 := bstep (se 3 (by rfl) ⟨2732018, by rfl⟩ : syracuseStep 14570765 = 5464037) B5464037
theorem B9713843 : Blo 1917435 9713843 := bstep (se 1 (by rfl) ⟨7285382, by rfl⟩ : syracuseStep 9713843 = 14570765) B14570765
theorem B6475895 : Blo 1917435 6475895 := bstep (se 1 (by rfl) ⟨4856921, by rfl⟩ : syracuseStep 6475895 = 9713843) B9713843
theorem B4317263 : Blo 1917435 4317263 := bstep (se 1 (by rfl) ⟨3237947, by rfl⟩ : syracuseStep 4317263 = 6475895) B6475895
theorem B2878175 : Blo 1917435 2878175 := bstep (se 1 (by rfl) ⟨2158631, by rfl⟩ : syracuseStep 2878175 = 4317263) B4317263
theorem B1918783 : Blo 1917435 1918783 := bstep (se 1 (by rfl) ⟨1439087, by rfl⟩ : syracuseStep 1918783 = 2878175) B2878175
theorem B2878181 : Blo 1917435 2878181 := bbase (se 4 (by rfl) ⟨269829, by rfl⟩ : syracuseStep 2878181 = 539659) (by norm_num)
theorem B1918787 : Blo 1917435 1918787 := bstep (se 1 (by rfl) ⟨1439090, by rfl⟩ : syracuseStep 1918787 = 2878181) B2878181
theorem B2368481 : Blo 1917435 2368481 := bbase (se 2 (by rfl) ⟨888180, by rfl⟩ : syracuseStep 2368481 = 1776361) (by norm_num)
theorem B25263797 : Blo 1917435 25263797 := bstep (se 5 (by rfl) ⟨1184240, by rfl⟩ : syracuseStep 25263797 = 2368481) B2368481
theorem B67370125 : Blo 1917435 67370125 := bstep (se 3 (by rfl) ⟨12631898, by rfl⟩ : syracuseStep 67370125 = 25263797) B25263797
theorem B89826833 : Blo 1917435 89826833 := bstep (se 2 (by rfl) ⟨33685062, by rfl⟩ : syracuseStep 89826833 = 67370125) B67370125
theorem B59884555 : Blo 1917435 59884555 := bstep (se 1 (by rfl) ⟨44913416, by rfl⟩ : syracuseStep 59884555 = 89826833) B89826833
theorem B79846073 : Blo 1917435 79846073 := bstep (se 2 (by rfl) ⟨29942277, by rfl⟩ : syracuseStep 79846073 = 59884555) B59884555
theorem B53230715 : Blo 1917435 53230715 := bstep (se 1 (by rfl) ⟨39923036, by rfl⟩ : syracuseStep 53230715 = 79846073) B79846073
theorem B35487143 : Blo 1917435 35487143 := bstep (se 1 (by rfl) ⟨26615357, by rfl⟩ : syracuseStep 35487143 = 53230715) B53230715
theorem B23658095 : Blo 1917435 23658095 := bstep (se 1 (by rfl) ⟨17743571, by rfl⟩ : syracuseStep 23658095 = 35487143) B35487143
theorem B63088253 : Blo 1917435 63088253 := bstep (se 3 (by rfl) ⟨11829047, by rfl⟩ : syracuseStep 63088253 = 23658095) B23658095
theorem B42058835 : Blo 1917435 42058835 := bstep (se 1 (by rfl) ⟨31544126, by rfl⟩ : syracuseStep 42058835 = 63088253) B63088253
theorem B28039223 : Blo 1917435 28039223 := bstep (se 1 (by rfl) ⟨21029417, by rfl⟩ : syracuseStep 28039223 = 42058835) B42058835
theorem B74771261 : Blo 1917435 74771261 := bstep (se 3 (by rfl) ⟨14019611, by rfl⟩ : syracuseStep 74771261 = 28039223) B28039223
theorem B49847507 : Blo 1917435 49847507 := bstep (se 1 (by rfl) ⟨37385630, by rfl⟩ : syracuseStep 49847507 = 74771261) B74771261
theorem B33231671 : Blo 1917435 33231671 := bstep (se 1 (by rfl) ⟨24923753, by rfl⟩ : syracuseStep 33231671 = 49847507) B49847507
theorem B22154447 : Blo 1917435 22154447 := bstep (se 1 (by rfl) ⟨16615835, by rfl⟩ : syracuseStep 22154447 = 33231671) B33231671
theorem B14769631 : Blo 1917435 14769631 := bstep (se 1 (by rfl) ⟨11077223, by rfl⟩ : syracuseStep 14769631 = 22154447) B22154447
theorem B78771365 : Blo 1917435 78771365 := bstep (se 4 (by rfl) ⟨7384815, by rfl⟩ : syracuseStep 78771365 = 14769631) B14769631
theorem B52514243 : Blo 1917435 52514243 := bstep (se 1 (by rfl) ⟨39385682, by rfl⟩ : syracuseStep 52514243 = 78771365) B78771365
theorem B35009495 : Blo 1917435 35009495 := bstep (se 1 (by rfl) ⟨26257121, by rfl⟩ : syracuseStep 35009495 = 52514243) B52514243
theorem B23339663 : Blo 1917435 23339663 := bstep (se 1 (by rfl) ⟨17504747, by rfl⟩ : syracuseStep 23339663 = 35009495) B35009495
theorem B15559775 : Blo 1917435 15559775 := bstep (se 1 (by rfl) ⟨11669831, by rfl⟩ : syracuseStep 15559775 = 23339663) B23339663
theorem B10373183 : Blo 1917435 10373183 := bstep (se 1 (by rfl) ⟨7779887, by rfl⟩ : syracuseStep 10373183 = 15559775) B15559775
theorem B6915455 : Blo 1917435 6915455 := bstep (se 1 (by rfl) ⟨5186591, by rfl⟩ : syracuseStep 6915455 = 10373183) B10373183
theorem B4610303 : Blo 1917435 4610303 := bstep (se 1 (by rfl) ⟨3457727, by rfl⟩ : syracuseStep 4610303 = 6915455) B6915455
theorem B3073535 : Blo 1917435 3073535 := bstep (se 1 (by rfl) ⟨2305151, by rfl⟩ : syracuseStep 3073535 = 4610303) B4610303
theorem B2049023 : Blo 1917435 2049023 := bstep (se 1 (by rfl) ⟨1536767, by rfl⟩ : syracuseStep 2049023 = 3073535) B3073535
theorem B5464061 : Blo 1917435 5464061 := bstep (se 3 (by rfl) ⟨1024511, by rfl⟩ : syracuseStep 5464061 = 2049023) B2049023
theorem B3642707 : Blo 1917435 3642707 := bstep (se 1 (by rfl) ⟨2732030, by rfl⟩ : syracuseStep 3642707 = 5464061) B5464061
theorem B2428471 : Blo 1917435 2428471 := bstep (se 1 (by rfl) ⟨1821353, by rfl⟩ : syracuseStep 2428471 = 3642707) B3642707
theorem B3237961 : Blo 1917435 3237961 := bstep (se 2 (by rfl) ⟨1214235, by rfl⟩ : syracuseStep 3237961 = 2428471) B2428471
theorem B4317281 : Blo 1917435 4317281 := bstep (se 2 (by rfl) ⟨1618980, by rfl⟩ : syracuseStep 4317281 = 3237961) B3237961
theorem B2878187 : Blo 1917435 2878187 := bstep (se 1 (by rfl) ⟨2158640, by rfl⟩ : syracuseStep 2878187 = 4317281) B4317281
theorem B1918791 : Blo 1917435 1918791 := bstep (se 1 (by rfl) ⟨1439093, by rfl⟩ : syracuseStep 1918791 = 2878187) B2878187
theorem B2158645 : Blo 1917435 2158645 := bbase (se 5 (by rfl) ⟨101186, by rfl⟩ : syracuseStep 2158645 = 202373) (by norm_num)
theorem B2878193 : Blo 1917435 2878193 := bstep (se 2 (by rfl) ⟨1079322, by rfl⟩ : syracuseStep 2878193 = 2158645) B2158645
theorem B1918795 : Blo 1917435 1918795 := bstep (se 1 (by rfl) ⟨1439096, by rfl⟩ : syracuseStep 1918795 = 2878193) B2878193
theorem B2428481 : Blo 1917435 2428481 := bbase (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) (by norm_num)
theorem B6475949 : Blo 1917435 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B4317299 : Blo 1917435 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B2878199 : Blo 1917435 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B1918799 : Blo 1917435 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B2878205 : Blo 1917435 2878205 := bbase (se 3 (by rfl) ⟨539663, by rfl⟩ : syracuseStep 2878205 = 1079327) (by norm_num)
theorem B1918803 : Blo 1917435 1918803 := bstep (se 1 (by rfl) ⟨1439102, by rfl⟩ : syracuseStep 1918803 = 2878205) B2878205
theorem B4317317 : Blo 1917435 4317317 := bbase (se 4 (by rfl) ⟨404748, by rfl⟩ : syracuseStep 4317317 = 809497) (by norm_num)
theorem B2878211 : Blo 1917435 2878211 := bstep (se 1 (by rfl) ⟨2158658, by rfl⟩ : syracuseStep 2878211 = 4317317) B4317317
theorem B1918807 : Blo 1917435 1918807 := bstep (se 1 (by rfl) ⟨1439105, by rfl⟩ : syracuseStep 1918807 = 2878211) B2878211
theorem B7886117 : Blo 1917435 7886117 := bbase (se 4 (by rfl) ⟨739323, by rfl⟩ : syracuseStep 7886117 = 1478647) (by norm_num)
theorem B21029645 : Blo 1917435 21029645 := bstep (se 3 (by rfl) ⟨3943058, by rfl⟩ : syracuseStep 21029645 = 7886117) B7886117
theorem B14019763 : Blo 1917435 14019763 := bstep (se 1 (by rfl) ⟨10514822, by rfl⟩ : syracuseStep 14019763 = 21029645) B21029645
theorem B18693017 : Blo 1917435 18693017 := bstep (se 2 (by rfl) ⟨7009881, by rfl⟩ : syracuseStep 18693017 = 14019763) B14019763
theorem B12462011 : Blo 1917435 12462011 := bstep (se 1 (by rfl) ⟨9346508, by rfl⟩ : syracuseStep 12462011 = 18693017) B18693017
theorem B8308007 : Blo 1917435 8308007 := bstep (se 1 (by rfl) ⟨6231005, by rfl⟩ : syracuseStep 8308007 = 12462011) B12462011
theorem B5538671 : Blo 1917435 5538671 := bstep (se 1 (by rfl) ⟨4154003, by rfl⟩ : syracuseStep 5538671 = 8308007) B8308007
theorem B3692447 : Blo 1917435 3692447 := bstep (se 1 (by rfl) ⟨2769335, by rfl⟩ : syracuseStep 3692447 = 5538671) B5538671
theorem B2461631 : Blo 1917435 2461631 := bstep (se 1 (by rfl) ⟨1846223, by rfl⟩ : syracuseStep 2461631 = 3692447) B3692447
theorem B6564349 : Blo 1917435 6564349 := bstep (se 3 (by rfl) ⟨1230815, by rfl⟩ : syracuseStep 6564349 = 2461631) B2461631
theorem B8752465 : Blo 1917435 8752465 := bstep (se 2 (by rfl) ⟨3282174, by rfl⟩ : syracuseStep 8752465 = 6564349) B6564349
theorem B11669953 : Blo 1917435 11669953 := bstep (se 2 (by rfl) ⟨4376232, by rfl⟩ : syracuseStep 11669953 = 8752465) B8752465
theorem B15559937 : Blo 1917435 15559937 := bstep (se 2 (by rfl) ⟨5834976, by rfl⟩ : syracuseStep 15559937 = 11669953) B11669953
theorem B10373291 : Blo 1917435 10373291 := bstep (se 1 (by rfl) ⟨7779968, by rfl⟩ : syracuseStep 10373291 = 15559937) B15559937
theorem B6915527 : Blo 1917435 6915527 := bstep (se 1 (by rfl) ⟨5186645, by rfl⟩ : syracuseStep 6915527 = 10373291) B10373291
theorem B4610351 : Blo 1917435 4610351 := bstep (se 1 (by rfl) ⟨3457763, by rfl⟩ : syracuseStep 4610351 = 6915527) B6915527
theorem B3073567 : Blo 1917435 3073567 := bstep (se 1 (by rfl) ⟨2305175, by rfl⟩ : syracuseStep 3073567 = 4610351) B4610351
theorem B4098089 : Blo 1917435 4098089 := bstep (se 2 (by rfl) ⟨1536783, by rfl⟩ : syracuseStep 4098089 = 3073567) B3073567
theorem B2732059 : Blo 1917435 2732059 := bstep (se 1 (by rfl) ⟨2049044, by rfl⟩ : syracuseStep 2732059 = 4098089) B4098089
theorem B3642745 : Blo 1917435 3642745 := bstep (se 2 (by rfl) ⟨1366029, by rfl⟩ : syracuseStep 3642745 = 2732059) B2732059
theorem B4856993 : Blo 1917435 4856993 := bstep (se 2 (by rfl) ⟨1821372, by rfl⟩ : syracuseStep 4856993 = 3642745) B3642745
theorem B3237995 : Blo 1917435 3237995 := bstep (se 1 (by rfl) ⟨2428496, by rfl⟩ : syracuseStep 3237995 = 4856993) B4856993
theorem B2158663 : Blo 1917435 2158663 := bstep (se 1 (by rfl) ⟨1618997, by rfl⟩ : syracuseStep 2158663 = 3237995) B3237995
theorem B2878217 : Blo 1917435 2878217 := bstep (se 2 (by rfl) ⟨1079331, by rfl⟩ : syracuseStep 2878217 = 2158663) B2158663
theorem B1918811 : Blo 1917435 1918811 := bstep (se 1 (by rfl) ⟨1439108, by rfl⟩ : syracuseStep 1918811 = 2878217) B2878217
theorem B9714005 : Blo 1917435 9714005 := bbase (se 10 (by rfl) ⟨14229, by rfl⟩ : syracuseStep 9714005 = 28459) (by norm_num)
theorem B6476003 : Blo 1917435 6476003 := bstep (se 1 (by rfl) ⟨4857002, by rfl⟩ : syracuseStep 6476003 = 9714005) B9714005
theorem B4317335 : Blo 1917435 4317335 := bstep (se 1 (by rfl) ⟨3238001, by rfl⟩ : syracuseStep 4317335 = 6476003) B6476003
theorem B2878223 : Blo 1917435 2878223 := bstep (se 1 (by rfl) ⟨2158667, by rfl⟩ : syracuseStep 2878223 = 4317335) B4317335
theorem B1918815 : Blo 1917435 1918815 := bstep (se 1 (by rfl) ⟨1439111, by rfl⟩ : syracuseStep 1918815 = 2878223) B2878223
theorem B2878229 : Blo 1917435 2878229 := bbase (se 6 (by rfl) ⟨67458, by rfl⟩ : syracuseStep 2878229 = 134917) (by norm_num)
theorem B1918819 : Blo 1917435 1918819 := bstep (se 1 (by rfl) ⟨1439114, by rfl⟩ : syracuseStep 1918819 = 2878229) B2878229
theorem B3372365 : Blo 1917435 3372365 := bbase (se 3 (by rfl) ⟨632318, by rfl⟩ : syracuseStep 3372365 = 1264637) (by norm_num)
theorem B8992973 : Blo 1917435 8992973 := bstep (se 3 (by rfl) ⟨1686182, by rfl⟩ : syracuseStep 8992973 = 3372365) B3372365
theorem B5995315 : Blo 1917435 5995315 := bstep (se 1 (by rfl) ⟨4496486, by rfl⟩ : syracuseStep 5995315 = 8992973) B8992973
theorem B7993753 : Blo 1917435 7993753 := bstep (se 2 (by rfl) ⟨2997657, by rfl⟩ : syracuseStep 7993753 = 5995315) B5995315
theorem B170533397 : Blo 1917435 170533397 := bstep (se 6 (by rfl) ⟨3996876, by rfl⟩ : syracuseStep 170533397 = 7993753) B7993753
theorem B454755725 : Blo 1917435 454755725 := bstep (se 3 (by rfl) ⟨85266698, by rfl⟩ : syracuseStep 454755725 = 170533397) B170533397
theorem B303170483 : Blo 1917435 303170483 := bstep (se 1 (by rfl) ⟨227377862, by rfl⟩ : syracuseStep 303170483 = 454755725) B454755725
theorem B808454621 : Blo 1917435 808454621 := bstep (se 3 (by rfl) ⟨151585241, by rfl⟩ : syracuseStep 808454621 = 303170483) B303170483
theorem B538969747 : Blo 1917435 538969747 := bstep (se 1 (by rfl) ⟨404227310, by rfl⟩ : syracuseStep 538969747 = 808454621) B808454621
theorem B718626329 : Blo 1917435 718626329 := bstep (se 2 (by rfl) ⟨269484873, by rfl⟩ : syracuseStep 718626329 = 538969747) B538969747
theorem B479084219 : Blo 1917435 479084219 := bstep (se 1 (by rfl) ⟨359313164, by rfl⟩ : syracuseStep 479084219 = 718626329) B718626329
theorem B319389479 : Blo 1917435 319389479 := bstep (se 1 (by rfl) ⟨239542109, by rfl⟩ : syracuseStep 319389479 = 479084219) B479084219
theorem B212926319 : Blo 1917435 212926319 := bstep (se 1 (by rfl) ⟨159694739, by rfl⟩ : syracuseStep 212926319 = 319389479) B319389479
theorem B141950879 : Blo 1917435 141950879 := bstep (se 1 (by rfl) ⟨106463159, by rfl⟩ : syracuseStep 141950879 = 212926319) B212926319
theorem B94633919 : Blo 1917435 94633919 := bstep (se 1 (by rfl) ⟨70975439, by rfl⟩ : syracuseStep 94633919 = 141950879) B141950879
theorem B63089279 : Blo 1917435 63089279 := bstep (se 1 (by rfl) ⟨47316959, by rfl⟩ : syracuseStep 63089279 = 94633919) B94633919
theorem B42059519 : Blo 1917435 42059519 := bstep (se 1 (by rfl) ⟨31544639, by rfl⟩ : syracuseStep 42059519 = 63089279) B63089279
theorem B28039679 : Blo 1917435 28039679 := bstep (se 1 (by rfl) ⟨21029759, by rfl⟩ : syracuseStep 28039679 = 42059519) B42059519
theorem B18693119 : Blo 1917435 18693119 := bstep (se 1 (by rfl) ⟨14019839, by rfl⟩ : syracuseStep 18693119 = 28039679) B28039679
theorem B12462079 : Blo 1917435 12462079 := bstep (se 1 (by rfl) ⟨9346559, by rfl⟩ : syracuseStep 12462079 = 18693119) B18693119
theorem B16616105 : Blo 1917435 16616105 := bstep (se 2 (by rfl) ⟨6231039, by rfl⟩ : syracuseStep 16616105 = 12462079) B12462079
theorem B11077403 : Blo 1917435 11077403 := bstep (se 1 (by rfl) ⟨8308052, by rfl⟩ : syracuseStep 11077403 = 16616105) B16616105
theorem B29539741 : Blo 1917435 29539741 := bstep (se 3 (by rfl) ⟨5538701, by rfl⟩ : syracuseStep 29539741 = 11077403) B11077403
theorem B39386321 : Blo 1917435 39386321 := bstep (se 2 (by rfl) ⟨14769870, by rfl⟩ : syracuseStep 39386321 = 29539741) B29539741
theorem B26257547 : Blo 1917435 26257547 := bstep (se 1 (by rfl) ⟨19693160, by rfl⟩ : syracuseStep 26257547 = 39386321) B39386321
theorem B17505031 : Blo 1917435 17505031 := bstep (se 1 (by rfl) ⟨13128773, by rfl⟩ : syracuseStep 17505031 = 26257547) B26257547
theorem B23340041 : Blo 1917435 23340041 := bstep (se 2 (by rfl) ⟨8752515, by rfl⟩ : syracuseStep 23340041 = 17505031) B17505031
theorem B15560027 : Blo 1917435 15560027 := bstep (se 1 (by rfl) ⟨11670020, by rfl⟩ : syracuseStep 15560027 = 23340041) B23340041
theorem B10373351 : Blo 1917435 10373351 := bstep (se 1 (by rfl) ⟨7780013, by rfl⟩ : syracuseStep 10373351 = 15560027) B15560027
theorem B27662269 : Blo 1917435 27662269 := bstep (se 3 (by rfl) ⟨5186675, by rfl⟩ : syracuseStep 27662269 = 10373351) B10373351
theorem B36883025 : Blo 1917435 36883025 := bstep (se 2 (by rfl) ⟨13831134, by rfl⟩ : syracuseStep 36883025 = 27662269) B27662269
theorem B24588683 : Blo 1917435 24588683 := bstep (se 1 (by rfl) ⟨18441512, by rfl⟩ : syracuseStep 24588683 = 36883025) B36883025
theorem B16392455 : Blo 1917435 16392455 := bstep (se 1 (by rfl) ⟨12294341, by rfl⟩ : syracuseStep 16392455 = 24588683) B24588683
theorem B10928303 : Blo 1917435 10928303 := bstep (se 1 (by rfl) ⟨8196227, by rfl⟩ : syracuseStep 10928303 = 16392455) B16392455
theorem B7285535 : Blo 1917435 7285535 := bstep (se 1 (by rfl) ⟨5464151, by rfl⟩ : syracuseStep 7285535 = 10928303) B10928303
theorem B4857023 : Blo 1917435 4857023 := bstep (se 1 (by rfl) ⟨3642767, by rfl⟩ : syracuseStep 4857023 = 7285535) B7285535
theorem B3238015 : Blo 1917435 3238015 := bstep (se 1 (by rfl) ⟨2428511, by rfl⟩ : syracuseStep 3238015 = 4857023) B4857023
theorem B4317353 : Blo 1917435 4317353 := bstep (se 2 (by rfl) ⟨1619007, by rfl⟩ : syracuseStep 4317353 = 3238015) B3238015
theorem B2878235 : Blo 1917435 2878235 := bstep (se 1 (by rfl) ⟨2158676, by rfl⟩ : syracuseStep 2878235 = 4317353) B4317353
theorem B1918823 : Blo 1917435 1918823 := bstep (se 1 (by rfl) ⟨1439117, by rfl⟩ : syracuseStep 1918823 = 2878235) B2878235
theorem B2158681 : Blo 1917435 2158681 := bbase (se 2 (by rfl) ⟨809505, by rfl⟩ : syracuseStep 2158681 = 1619011) (by norm_num)
theorem B2878241 : Blo 1917435 2878241 := bstep (se 2 (by rfl) ⟨1079340, by rfl⟩ : syracuseStep 2878241 = 2158681) B2158681
theorem B1918827 : Blo 1917435 1918827 := bstep (se 1 (by rfl) ⟨1439120, by rfl⟩ : syracuseStep 1918827 = 2878241) B2878241
theorem B2461657 : Blo 1917435 2461657 := bbase (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) (by norm_num)
theorem B3282209 : Blo 1917435 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B2188139 : Blo 1917435 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B5835037 : Blo 1917435 5835037 := bstep (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) B2188139
theorem B7780049 : Blo 1917435 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B5186699 : Blo 1917435 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B3457799 : Blo 1917435 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B2305199 : Blo 1917435 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B6147197 : Blo 1917435 6147197 := bstep (se 3 (by rfl) ⟨1152599, by rfl⟩ : syracuseStep 6147197 = 2305199) B2305199
theorem B4098131 : Blo 1917435 4098131 := bstep (se 1 (by rfl) ⟨3073598, by rfl⟩ : syracuseStep 4098131 = 6147197) B6147197
theorem B2732087 : Blo 1917435 2732087 := bstep (se 1 (by rfl) ⟨2049065, by rfl⟩ : syracuseStep 2732087 = 4098131) B4098131
theorem B7285565 : Blo 1917435 7285565 := bstep (se 3 (by rfl) ⟨1366043, by rfl⟩ : syracuseStep 7285565 = 2732087) B2732087
theorem B4857043 : Blo 1917435 4857043 := bstep (se 1 (by rfl) ⟨3642782, by rfl⟩ : syracuseStep 4857043 = 7285565) B7285565
theorem B6476057 : Blo 1917435 6476057 := bstep (se 2 (by rfl) ⟨2428521, by rfl⟩ : syracuseStep 6476057 = 4857043) B4857043
theorem B4317371 : Blo 1917435 4317371 := bstep (se 1 (by rfl) ⟨3238028, by rfl⟩ : syracuseStep 4317371 = 6476057) B6476057
theorem B2878247 : Blo 1917435 2878247 := bstep (se 1 (by rfl) ⟨2158685, by rfl⟩ : syracuseStep 2878247 = 4317371) B4317371
theorem B1918831 : Blo 1917435 1918831 := bstep (se 1 (by rfl) ⟨1439123, by rfl⟩ : syracuseStep 1918831 = 2878247) B2878247
theorem B2878253 : Blo 1917435 2878253 := bbase (se 3 (by rfl) ⟨539672, by rfl⟩ : syracuseStep 2878253 = 1079345) (by norm_num)
theorem B1918835 : Blo 1917435 1918835 := bstep (se 1 (by rfl) ⟨1439126, by rfl⟩ : syracuseStep 1918835 = 2878253) B2878253
theorem B4317389 : Blo 1917435 4317389 := bbase (se 3 (by rfl) ⟨809510, by rfl⟩ : syracuseStep 4317389 = 1619021) (by norm_num)
theorem B2878259 : Blo 1917435 2878259 := bstep (se 1 (by rfl) ⟨2158694, by rfl⟩ : syracuseStep 2878259 = 4317389) B4317389
theorem B1918839 : Blo 1917435 1918839 := bstep (se 1 (by rfl) ⟨1439129, by rfl⟩ : syracuseStep 1918839 = 2878259) B2878259
theorem B2428537 : Blo 1917435 2428537 := bbase (se 2 (by rfl) ⟨910701, by rfl⟩ : syracuseStep 2428537 = 1821403) (by norm_num)
theorem B3238049 : Blo 1917435 3238049 := bstep (se 2 (by rfl) ⟨1214268, by rfl⟩ : syracuseStep 3238049 = 2428537) B2428537
theorem B2158699 : Blo 1917435 2158699 := bstep (se 1 (by rfl) ⟨1619024, by rfl⟩ : syracuseStep 2158699 = 3238049) B3238049
theorem B2878265 : Blo 1917435 2878265 := bstep (se 2 (by rfl) ⟨1079349, by rfl⟩ : syracuseStep 2878265 = 2158699) B2158699
theorem B1918843 : Blo 1917435 1918843 := bstep (se 1 (by rfl) ⟨1439132, by rfl⟩ : syracuseStep 1918843 = 2878265) B2878265
theorem B6564469 : Blo 1917435 6564469 := bbase (se 5 (by rfl) ⟨307709, by rfl⟩ : syracuseStep 6564469 = 615419) (by norm_num)
theorem B8752625 : Blo 1917435 8752625 := bstep (se 2 (by rfl) ⟨3282234, by rfl⟩ : syracuseStep 8752625 = 6564469) B6564469
theorem B5835083 : Blo 1917435 5835083 := bstep (se 1 (by rfl) ⟨4376312, by rfl⟩ : syracuseStep 5835083 = 8752625) B8752625
theorem B15560221 : Blo 1917435 15560221 := bstep (se 3 (by rfl) ⟨2917541, by rfl⟩ : syracuseStep 15560221 = 5835083) B5835083
theorem B20746961 : Blo 1917435 20746961 := bstep (se 2 (by rfl) ⟨7780110, by rfl⟩ : syracuseStep 20746961 = 15560221) B15560221
theorem B13831307 : Blo 1917435 13831307 := bstep (se 1 (by rfl) ⟨10373480, by rfl⟩ : syracuseStep 13831307 = 20746961) B20746961
theorem B9220871 : Blo 1917435 9220871 := bstep (se 1 (by rfl) ⟨6915653, by rfl⟩ : syracuseStep 9220871 = 13831307) B13831307
theorem B6147247 : Blo 1917435 6147247 := bstep (se 1 (by rfl) ⟨4610435, by rfl⟩ : syracuseStep 6147247 = 9220871) B9220871
theorem B8196329 : Blo 1917435 8196329 := bstep (se 2 (by rfl) ⟨3073623, by rfl⟩ : syracuseStep 8196329 = 6147247) B6147247
theorem B21856877 : Blo 1917435 21856877 := bstep (se 3 (by rfl) ⟨4098164, by rfl⟩ : syracuseStep 21856877 = 8196329) B8196329
theorem B14571251 : Blo 1917435 14571251 := bstep (se 1 (by rfl) ⟨10928438, by rfl⟩ : syracuseStep 14571251 = 21856877) B21856877
theorem B9714167 : Blo 1917435 9714167 := bstep (se 1 (by rfl) ⟨7285625, by rfl⟩ : syracuseStep 9714167 = 14571251) B14571251
theorem B6476111 : Blo 1917435 6476111 := bstep (se 1 (by rfl) ⟨4857083, by rfl⟩ : syracuseStep 6476111 = 9714167) B9714167
theorem B4317407 : Blo 1917435 4317407 := bstep (se 1 (by rfl) ⟨3238055, by rfl⟩ : syracuseStep 4317407 = 6476111) B6476111
theorem B2878271 : Blo 1917435 2878271 := bstep (se 1 (by rfl) ⟨2158703, by rfl⟩ : syracuseStep 2878271 = 4317407) B4317407
theorem B1918847 : Blo 1917435 1918847 := bstep (se 1 (by rfl) ⟨1439135, by rfl⟩ : syracuseStep 1918847 = 2878271) B2878271
theorem B2878277 : Blo 1917435 2878277 := bbase (se 4 (by rfl) ⟨269838, by rfl⟩ : syracuseStep 2878277 = 539677) (by norm_num)
theorem B1918851 : Blo 1917435 1918851 := bstep (se 1 (by rfl) ⟨1439138, by rfl⟩ : syracuseStep 1918851 = 2878277) B2878277
theorem B3238069 : Blo 1917435 3238069 := bbase (se 5 (by rfl) ⟨151784, by rfl⟩ : syracuseStep 3238069 = 303569) (by norm_num)
theorem B4317425 : Blo 1917435 4317425 := bstep (se 2 (by rfl) ⟨1619034, by rfl⟩ : syracuseStep 4317425 = 3238069) B3238069
theorem B2878283 : Blo 1917435 2878283 := bstep (se 1 (by rfl) ⟨2158712, by rfl⟩ : syracuseStep 2878283 = 4317425) B4317425
theorem B1918855 : Blo 1917435 1918855 := bstep (se 1 (by rfl) ⟨1439141, by rfl⟩ : syracuseStep 1918855 = 2878283) B2878283
theorem B2158717 : Blo 1917435 2158717 := bbase (se 3 (by rfl) ⟨404759, by rfl⟩ : syracuseStep 2158717 = 809519) (by norm_num)
theorem B2878289 : Blo 1917435 2878289 := bstep (se 2 (by rfl) ⟨1079358, by rfl⟩ : syracuseStep 2878289 = 2158717) B2158717
theorem B1918859 : Blo 1917435 1918859 := bstep (se 1 (by rfl) ⟨1439144, by rfl⟩ : syracuseStep 1918859 = 2878289) B2878289
theorem B6476165 : Blo 1917435 6476165 := bbase (se 4 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 6476165 = 1214281) (by norm_num)
theorem B4317443 : Blo 1917435 4317443 := bstep (se 1 (by rfl) ⟨3238082, by rfl⟩ : syracuseStep 4317443 = 6476165) B6476165
theorem B2878295 : Blo 1917435 2878295 := bstep (se 1 (by rfl) ⟨2158721, by rfl⟩ : syracuseStep 2878295 = 4317443) B4317443
theorem B1918863 : Blo 1917435 1918863 := bstep (se 1 (by rfl) ⟨1439147, by rfl⟩ : syracuseStep 1918863 = 2878295) B2878295
theorem B2878301 : Blo 1917435 2878301 := bbase (se 3 (by rfl) ⟨539681, by rfl⟩ : syracuseStep 2878301 = 1079363) (by norm_num)
theorem B1918867 : Blo 1917435 1918867 := bstep (se 1 (by rfl) ⟨1439150, by rfl⟩ : syracuseStep 1918867 = 2878301) B2878301
theorem B4317461 : Blo 1917435 4317461 := bbase (se 6 (by rfl) ⟨101190, by rfl⟩ : syracuseStep 4317461 = 202381) (by norm_num)
theorem B2878307 : Blo 1917435 2878307 := bstep (se 1 (by rfl) ⟨2158730, by rfl⟩ : syracuseStep 2878307 = 4317461) B4317461
theorem B1918871 : Blo 1917435 1918871 := bstep (se 1 (by rfl) ⟨1439153, by rfl⟩ : syracuseStep 1918871 = 2878307) B2878307
theorem B7285733 : Blo 1917435 7285733 := bbase (se 4 (by rfl) ⟨683037, by rfl⟩ : syracuseStep 7285733 = 1366075) (by norm_num)
theorem B4857155 : Blo 1917435 4857155 := bstep (se 1 (by rfl) ⟨3642866, by rfl⟩ : syracuseStep 4857155 = 7285733) B7285733
theorem B3238103 : Blo 1917435 3238103 := bstep (se 1 (by rfl) ⟨2428577, by rfl⟩ : syracuseStep 3238103 = 4857155) B4857155
theorem B2158735 : Blo 1917435 2158735 := bstep (se 1 (by rfl) ⟨1619051, by rfl⟩ : syracuseStep 2158735 = 3238103) B3238103
theorem B2878313 : Blo 1917435 2878313 := bstep (se 2 (by rfl) ⟨1079367, by rfl⟩ : syracuseStep 2878313 = 2158735) B2158735
theorem B1918875 : Blo 1917435 1918875 := bstep (se 1 (by rfl) ⟨1439156, by rfl⟩ : syracuseStep 1918875 = 2878313) B2878313
theorem B3457885 : Blo 1917435 3457885 := bbase (se 3 (by rfl) ⟨648353, by rfl⟩ : syracuseStep 3457885 = 1296707) (by norm_num)
theorem B4610513 : Blo 1917435 4610513 := bstep (se 2 (by rfl) ⟨1728942, by rfl⟩ : syracuseStep 4610513 = 3457885) B3457885
theorem B3073675 : Blo 1917435 3073675 := bstep (se 1 (by rfl) ⟨2305256, by rfl⟩ : syracuseStep 3073675 = 4610513) B4610513
theorem B4098233 : Blo 1917435 4098233 := bstep (se 2 (by rfl) ⟨1536837, by rfl⟩ : syracuseStep 4098233 = 3073675) B3073675
theorem B10928621 : Blo 1917435 10928621 := bstep (se 3 (by rfl) ⟨2049116, by rfl⟩ : syracuseStep 10928621 = 4098233) B4098233
theorem B7285747 : Blo 1917435 7285747 := bstep (se 1 (by rfl) ⟨5464310, by rfl⟩ : syracuseStep 7285747 = 10928621) B10928621
theorem B9714329 : Blo 1917435 9714329 := bstep (se 2 (by rfl) ⟨3642873, by rfl⟩ : syracuseStep 9714329 = 7285747) B7285747
theorem B6476219 : Blo 1917435 6476219 := bstep (se 1 (by rfl) ⟨4857164, by rfl⟩ : syracuseStep 6476219 = 9714329) B9714329
theorem B4317479 : Blo 1917435 4317479 := bstep (se 1 (by rfl) ⟨3238109, by rfl⟩ : syracuseStep 4317479 = 6476219) B6476219
theorem B2878319 : Blo 1917435 2878319 := bstep (se 1 (by rfl) ⟨2158739, by rfl⟩ : syracuseStep 2878319 = 4317479) B4317479
theorem B1918879 : Blo 1917435 1918879 := bstep (se 1 (by rfl) ⟨1439159, by rfl⟩ : syracuseStep 1918879 = 2878319) B2878319
theorem B2878325 : Blo 1917435 2878325 := bbase (se 5 (by rfl) ⟨134921, by rfl⟩ : syracuseStep 2878325 = 269843) (by norm_num)
theorem B1918883 : Blo 1917435 1918883 := bstep (se 1 (by rfl) ⟨1439162, by rfl⟩ : syracuseStep 1918883 = 2878325) B2878325
theorem B4610533 : Blo 1917435 4610533 := bbase (se 4 (by rfl) ⟨432237, by rfl⟩ : syracuseStep 4610533 = 864475) (by norm_num)
theorem B6147377 : Blo 1917435 6147377 := bstep (se 2 (by rfl) ⟨2305266, by rfl⟩ : syracuseStep 6147377 = 4610533) B4610533
theorem B4098251 : Blo 1917435 4098251 := bstep (se 1 (by rfl) ⟨3073688, by rfl⟩ : syracuseStep 4098251 = 6147377) B6147377
theorem B2732167 : Blo 1917435 2732167 := bstep (se 1 (by rfl) ⟨2049125, by rfl⟩ : syracuseStep 2732167 = 4098251) B4098251
theorem B3642889 : Blo 1917435 3642889 := bstep (se 2 (by rfl) ⟨1366083, by rfl⟩ : syracuseStep 3642889 = 2732167) B2732167
theorem B4857185 : Blo 1917435 4857185 := bstep (se 2 (by rfl) ⟨1821444, by rfl⟩ : syracuseStep 4857185 = 3642889) B3642889
theorem B3238123 : Blo 1917435 3238123 := bstep (se 1 (by rfl) ⟨2428592, by rfl⟩ : syracuseStep 3238123 = 4857185) B4857185
theorem B4317497 : Blo 1917435 4317497 := bstep (se 2 (by rfl) ⟨1619061, by rfl⟩ : syracuseStep 4317497 = 3238123) B3238123
theorem B2878331 : Blo 1917435 2878331 := bstep (se 1 (by rfl) ⟨2158748, by rfl⟩ : syracuseStep 2878331 = 4317497) B4317497
theorem B1918887 : Blo 1917435 1918887 := bstep (se 1 (by rfl) ⟨1439165, by rfl⟩ : syracuseStep 1918887 = 2878331) B2878331
theorem B2158753 : Blo 1917435 2158753 := bbase (se 2 (by rfl) ⟨809532, by rfl⟩ : syracuseStep 2158753 = 1619065) (by norm_num)
theorem B2878337 : Blo 1917435 2878337 := bstep (se 2 (by rfl) ⟨1079376, by rfl⟩ : syracuseStep 2878337 = 2158753) B2158753
theorem B1918891 : Blo 1917435 1918891 := bstep (se 1 (by rfl) ⟨1439168, by rfl⟩ : syracuseStep 1918891 = 2878337) B2878337
theorem B4857205 : Blo 1917435 4857205 := bbase (se 5 (by rfl) ⟨227681, by rfl⟩ : syracuseStep 4857205 = 455363) (by norm_num)
theorem B6476273 : Blo 1917435 6476273 := bstep (se 2 (by rfl) ⟨2428602, by rfl⟩ : syracuseStep 6476273 = 4857205) B4857205
theorem B4317515 : Blo 1917435 4317515 := bstep (se 1 (by rfl) ⟨3238136, by rfl⟩ : syracuseStep 4317515 = 6476273) B6476273
theorem B2878343 : Blo 1917435 2878343 := bstep (se 1 (by rfl) ⟨2158757, by rfl⟩ : syracuseStep 2878343 = 4317515) B4317515
theorem B1918895 : Blo 1917435 1918895 := bstep (se 1 (by rfl) ⟨1439171, by rfl⟩ : syracuseStep 1918895 = 2878343) B2878343
theorem B2878349 : Blo 1917435 2878349 := bbase (se 3 (by rfl) ⟨539690, by rfl⟩ : syracuseStep 2878349 = 1079381) (by norm_num)
theorem B1918899 : Blo 1917435 1918899 := bstep (se 1 (by rfl) ⟨1439174, by rfl⟩ : syracuseStep 1918899 = 2878349) B2878349
theorem B4317533 : Blo 1917435 4317533 := bbase (se 3 (by rfl) ⟨809537, by rfl⟩ : syracuseStep 4317533 = 1619075) (by norm_num)
theorem B2878355 : Blo 1917435 2878355 := bstep (se 1 (by rfl) ⟨2158766, by rfl⟩ : syracuseStep 2878355 = 4317533) B4317533
theorem B1918903 : Blo 1917435 1918903 := bstep (se 1 (by rfl) ⟨1439177, by rfl⟩ : syracuseStep 1918903 = 2878355) B2878355
theorem B3238157 : Blo 1917435 3238157 := bbase (se 3 (by rfl) ⟨607154, by rfl⟩ : syracuseStep 3238157 = 1214309) (by norm_num)
theorem B2158771 : Blo 1917435 2158771 := bstep (se 1 (by rfl) ⟨1619078, by rfl⟩ : syracuseStep 2158771 = 3238157) B3238157
theorem B2878361 : Blo 1917435 2878361 := bstep (se 2 (by rfl) ⟨1079385, by rfl⟩ : syracuseStep 2878361 = 2158771) B2158771
theorem B1918907 : Blo 1917435 1918907 := bstep (se 1 (by rfl) ⟨1439180, by rfl⟩ : syracuseStep 1918907 = 2878361) B2878361
theorem B16393205 : Blo 1917435 16393205 := bbase (se 5 (by rfl) ⟨768431, by rfl⟩ : syracuseStep 16393205 = 1536863) (by norm_num)
theorem B10928803 : Blo 1917435 10928803 := bstep (se 1 (by rfl) ⟨8196602, by rfl⟩ : syracuseStep 10928803 = 16393205) B16393205
theorem B14571737 : Blo 1917435 14571737 := bstep (se 2 (by rfl) ⟨5464401, by rfl⟩ : syracuseStep 14571737 = 10928803) B10928803
theorem B9714491 : Blo 1917435 9714491 := bstep (se 1 (by rfl) ⟨7285868, by rfl⟩ : syracuseStep 9714491 = 14571737) B14571737
theorem B6476327 : Blo 1917435 6476327 := bstep (se 1 (by rfl) ⟨4857245, by rfl⟩ : syracuseStep 6476327 = 9714491) B9714491
theorem B4317551 : Blo 1917435 4317551 := bstep (se 1 (by rfl) ⟨3238163, by rfl⟩ : syracuseStep 4317551 = 6476327) B6476327
theorem B2878367 : Blo 1917435 2878367 := bstep (se 1 (by rfl) ⟨2158775, by rfl⟩ : syracuseStep 2878367 = 4317551) B4317551
theorem B1918911 : Blo 1917435 1918911 := bstep (se 1 (by rfl) ⟨1439183, by rfl⟩ : syracuseStep 1918911 = 2878367) B2878367
theorem B2878373 : Blo 1917435 2878373 := bbase (se 4 (by rfl) ⟨269847, by rfl⟩ : syracuseStep 2878373 = 539695) (by norm_num)
theorem B1918915 : Blo 1917435 1918915 := bstep (se 1 (by rfl) ⟨1439186, by rfl⟩ : syracuseStep 1918915 = 2878373) B2878373
theorem B2428633 : Blo 1917435 2428633 := bbase (se 2 (by rfl) ⟨910737, by rfl⟩ : syracuseStep 2428633 = 1821475) (by norm_num)
theorem B3238177 : Blo 1917435 3238177 := bstep (se 2 (by rfl) ⟨1214316, by rfl⟩ : syracuseStep 3238177 = 2428633) B2428633
theorem B4317569 : Blo 1917435 4317569 := bstep (se 2 (by rfl) ⟨1619088, by rfl⟩ : syracuseStep 4317569 = 3238177) B3238177
theorem B2878379 : Blo 1917435 2878379 := bstep (se 1 (by rfl) ⟨2158784, by rfl⟩ : syracuseStep 2878379 = 4317569) B4317569
theorem B1918919 : Blo 1917435 1918919 := bstep (se 1 (by rfl) ⟨1439189, by rfl⟩ : syracuseStep 1918919 = 2878379) B2878379
theorem B2158789 : Blo 1917435 2158789 := bbase (se 4 (by rfl) ⟨202386, by rfl⟩ : syracuseStep 2158789 = 404773) (by norm_num)
theorem B2878385 : Blo 1917435 2878385 := bstep (se 2 (by rfl) ⟨1079394, by rfl⟩ : syracuseStep 2878385 = 2158789) B2158789
theorem B1918923 : Blo 1917435 1918923 := bstep (se 1 (by rfl) ⟨1439192, by rfl⟩ : syracuseStep 1918923 = 2878385) B2878385
theorem B3642965 : Blo 1917435 3642965 := bbase (se 8 (by rfl) ⟨21345, by rfl⟩ : syracuseStep 3642965 = 42691) (by norm_num)
theorem B2428643 : Blo 1917435 2428643 := bstep (se 1 (by rfl) ⟨1821482, by rfl⟩ : syracuseStep 2428643 = 3642965) B3642965
theorem B6476381 : Blo 1917435 6476381 := bstep (se 3 (by rfl) ⟨1214321, by rfl⟩ : syracuseStep 6476381 = 2428643) B2428643
theorem B4317587 : Blo 1917435 4317587 := bstep (se 1 (by rfl) ⟨3238190, by rfl⟩ : syracuseStep 4317587 = 6476381) B6476381
theorem B2878391 : Blo 1917435 2878391 := bstep (se 1 (by rfl) ⟨2158793, by rfl⟩ : syracuseStep 2878391 = 4317587) B4317587
theorem B1918927 : Blo 1917435 1918927 := bstep (se 1 (by rfl) ⟨1439195, by rfl⟩ : syracuseStep 1918927 = 2878391) B2878391
theorem B2878397 : Blo 1917435 2878397 := bbase (se 3 (by rfl) ⟨539699, by rfl⟩ : syracuseStep 2878397 = 1079399) (by norm_num)
theorem B1918931 : Blo 1917435 1918931 := bstep (se 1 (by rfl) ⟨1439198, by rfl⟩ : syracuseStep 1918931 = 2878397) B2878397
theorem B4317605 : Blo 1917435 4317605 := bbase (se 4 (by rfl) ⟨404775, by rfl⟩ : syracuseStep 4317605 = 809551) (by norm_num)
theorem B2878403 : Blo 1917435 2878403 := bstep (se 1 (by rfl) ⟨2158802, by rfl⟩ : syracuseStep 2878403 = 4317605) B4317605
theorem B1918935 : Blo 1917435 1918935 := bstep (se 1 (by rfl) ⟨1439201, by rfl⟩ : syracuseStep 1918935 = 2878403) B2878403
theorem B4857317 : Blo 1917435 4857317 := bbase (se 4 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 4857317 = 910747) (by norm_num)
theorem B3238211 : Blo 1917435 3238211 := bstep (se 1 (by rfl) ⟨2428658, by rfl⟩ : syracuseStep 3238211 = 4857317) B4857317
theorem B2158807 : Blo 1917435 2158807 := bstep (se 1 (by rfl) ⟨1619105, by rfl⟩ : syracuseStep 2158807 = 3238211) B3238211
theorem B2878409 : Blo 1917435 2878409 := bstep (se 2 (by rfl) ⟨1079403, by rfl⟩ : syracuseStep 2878409 = 2158807) B2158807
theorem B1918939 : Blo 1917435 1918939 := bstep (se 1 (by rfl) ⟨1439204, by rfl⟩ : syracuseStep 1918939 = 2878409) B2878409
theorem B2049185 : Blo 1917435 2049185 := bbase (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) (by norm_num)
theorem B5464493 : Blo 1917435 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B3642995 : Blo 1917435 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B9714653 : Blo 1917435 9714653 := bstep (se 3 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 9714653 = 3642995) B3642995
theorem B6476435 : Blo 1917435 6476435 := bstep (se 1 (by rfl) ⟨4857326, by rfl⟩ : syracuseStep 6476435 = 9714653) B9714653
theorem B4317623 : Blo 1917435 4317623 := bstep (se 1 (by rfl) ⟨3238217, by rfl⟩ : syracuseStep 4317623 = 6476435) B6476435
theorem B2878415 : Blo 1917435 2878415 := bstep (se 1 (by rfl) ⟨2158811, by rfl⟩ : syracuseStep 2878415 = 4317623) B4317623
theorem B1918943 : Blo 1917435 1918943 := bstep (se 1 (by rfl) ⟨1439207, by rfl⟩ : syracuseStep 1918943 = 2878415) B2878415
theorem B2878421 : Blo 1917435 2878421 := bbase (se 7 (by rfl) ⟨33731, by rfl⟩ : syracuseStep 2878421 = 67463) (by norm_num)
theorem B1918947 : Blo 1917435 1918947 := bstep (se 1 (by rfl) ⟨1439210, by rfl⟩ : syracuseStep 1918947 = 2878421) B2878421
theorem B7286021 : Blo 1917435 7286021 := bbase (se 4 (by rfl) ⟨683064, by rfl⟩ : syracuseStep 7286021 = 1366129) (by norm_num)
theorem B4857347 : Blo 1917435 4857347 := bstep (se 1 (by rfl) ⟨3643010, by rfl⟩ : syracuseStep 4857347 = 7286021) B7286021
theorem B3238231 : Blo 1917435 3238231 := bstep (se 1 (by rfl) ⟨2428673, by rfl⟩ : syracuseStep 3238231 = 4857347) B4857347
theorem B4317641 : Blo 1917435 4317641 := bstep (se 2 (by rfl) ⟨1619115, by rfl⟩ : syracuseStep 4317641 = 3238231) B3238231
theorem B2878427 : Blo 1917435 2878427 := bstep (se 1 (by rfl) ⟨2158820, by rfl⟩ : syracuseStep 2878427 = 4317641) B4317641
theorem B1918951 : Blo 1917435 1918951 := bstep (se 1 (by rfl) ⟨1439213, by rfl⟩ : syracuseStep 1918951 = 2878427) B2878427
theorem B2158825 : Blo 1917435 2158825 := bbase (se 2 (by rfl) ⟨809559, by rfl⟩ : syracuseStep 2158825 = 1619119) (by norm_num)
theorem B2878433 : Blo 1917435 2878433 := bstep (se 2 (by rfl) ⟨1079412, by rfl⟩ : syracuseStep 2878433 = 2158825) B2158825
theorem B1918955 : Blo 1917435 1918955 := bstep (se 1 (by rfl) ⟨1439216, by rfl⟩ : syracuseStep 1918955 = 2878433) B2878433
theorem B10929077 : Blo 1917435 10929077 := bbase (se 5 (by rfl) ⟨512300, by rfl⟩ : syracuseStep 10929077 = 1024601) (by norm_num)
theorem B7286051 : Blo 1917435 7286051 := bstep (se 1 (by rfl) ⟨5464538, by rfl⟩ : syracuseStep 7286051 = 10929077) B10929077
theorem B4857367 : Blo 1917435 4857367 := bstep (se 1 (by rfl) ⟨3643025, by rfl⟩ : syracuseStep 4857367 = 7286051) B7286051
theorem B6476489 : Blo 1917435 6476489 := bstep (se 2 (by rfl) ⟨2428683, by rfl⟩ : syracuseStep 6476489 = 4857367) B4857367
theorem B4317659 : Blo 1917435 4317659 := bstep (se 1 (by rfl) ⟨3238244, by rfl⟩ : syracuseStep 4317659 = 6476489) B6476489
theorem B2878439 : Blo 1917435 2878439 := bstep (se 1 (by rfl) ⟨2158829, by rfl⟩ : syracuseStep 2878439 = 4317659) B4317659
theorem B1918959 : Blo 1917435 1918959 := bstep (se 1 (by rfl) ⟨1439219, by rfl⟩ : syracuseStep 1918959 = 2878439) B2878439
theorem B2878445 : Blo 1917435 2878445 := bbase (se 3 (by rfl) ⟨539708, by rfl⟩ : syracuseStep 2878445 = 1079417) (by norm_num)
theorem B1918963 : Blo 1917435 1918963 := bstep (se 1 (by rfl) ⟨1439222, by rfl⟩ : syracuseStep 1918963 = 2878445) B2878445
theorem B4317677 : Blo 1917435 4317677 := bbase (se 3 (by rfl) ⟨809564, by rfl⟩ : syracuseStep 4317677 = 1619129) (by norm_num)
theorem B2878451 : Blo 1917435 2878451 := bstep (se 1 (by rfl) ⟨2158838, by rfl⟩ : syracuseStep 2878451 = 4317677) B4317677
theorem B1918967 : Blo 1917435 1918967 := bstep (se 1 (by rfl) ⟨1439225, by rfl⟩ : syracuseStep 1918967 = 2878451) B2878451
theorem B4376597 : Blo 1917435 4376597 := bbase (se 6 (by rfl) ⟨102576, by rfl⟩ : syracuseStep 4376597 = 205153) (by norm_num)
theorem B46683701 : Blo 1917435 46683701 := bstep (se 5 (by rfl) ⟨2188298, by rfl⟩ : syracuseStep 46683701 = 4376597) B4376597
theorem B31122467 : Blo 1917435 31122467 := bstep (se 1 (by rfl) ⟨23341850, by rfl⟩ : syracuseStep 31122467 = 46683701) B46683701
theorem B20748311 : Blo 1917435 20748311 := bstep (se 1 (by rfl) ⟨15561233, by rfl⟩ : syracuseStep 20748311 = 31122467) B31122467
theorem B13832207 : Blo 1917435 13832207 := bstep (se 1 (by rfl) ⟨10374155, by rfl⟩ : syracuseStep 13832207 = 20748311) B20748311
theorem B9221471 : Blo 1917435 9221471 := bstep (se 1 (by rfl) ⟨6916103, by rfl⟩ : syracuseStep 9221471 = 13832207) B13832207
theorem B6147647 : Blo 1917435 6147647 := bstep (se 1 (by rfl) ⟨4610735, by rfl⟩ : syracuseStep 6147647 = 9221471) B9221471
theorem B4098431 : Blo 1917435 4098431 := bstep (se 1 (by rfl) ⟨3073823, by rfl⟩ : syracuseStep 4098431 = 6147647) B6147647
theorem B2732287 : Blo 1917435 2732287 := bstep (se 1 (by rfl) ⟨2049215, by rfl⟩ : syracuseStep 2732287 = 4098431) B4098431
theorem B3643049 : Blo 1917435 3643049 := bstep (se 2 (by rfl) ⟨1366143, by rfl⟩ : syracuseStep 3643049 = 2732287) B2732287
theorem B2428699 : Blo 1917435 2428699 := bstep (se 1 (by rfl) ⟨1821524, by rfl⟩ : syracuseStep 2428699 = 3643049) B3643049
theorem B3238265 : Blo 1917435 3238265 := bstep (se 2 (by rfl) ⟨1214349, by rfl⟩ : syracuseStep 3238265 = 2428699) B2428699
theorem B2158843 : Blo 1917435 2158843 := bstep (se 1 (by rfl) ⟨1619132, by rfl⟩ : syracuseStep 2158843 = 3238265) B3238265
theorem B2878457 : Blo 1917435 2878457 := bstep (se 2 (by rfl) ⟨1079421, by rfl⟩ : syracuseStep 2878457 = 2158843) B2158843
theorem B1918971 : Blo 1917435 1918971 := bstep (se 1 (by rfl) ⟨1439228, by rfl⟩ : syracuseStep 1918971 = 2878457) B2878457
theorem B3505237 : Blo 1917435 3505237 := bbase (se 8 (by rfl) ⟨20538, by rfl⟩ : syracuseStep 3505237 = 41077) (by norm_num)
theorem B18694597 : Blo 1917435 18694597 := bstep (se 4 (by rfl) ⟨1752618, by rfl⟩ : syracuseStep 18694597 = 3505237) B3505237
theorem B24926129 : Blo 1917435 24926129 := bstep (se 2 (by rfl) ⟨9347298, by rfl⟩ : syracuseStep 24926129 = 18694597) B18694597
theorem B16617419 : Blo 1917435 16617419 := bstep (se 1 (by rfl) ⟨12463064, by rfl⟩ : syracuseStep 16617419 = 24926129) B24926129
theorem B11078279 : Blo 1917435 11078279 := bstep (se 1 (by rfl) ⟨8308709, by rfl⟩ : syracuseStep 11078279 = 16617419) B16617419
theorem B7385519 : Blo 1917435 7385519 := bstep (se 1 (by rfl) ⟨5539139, by rfl⟩ : syracuseStep 7385519 = 11078279) B11078279
theorem B19694717 : Blo 1917435 19694717 := bstep (se 3 (by rfl) ⟨3692759, by rfl⟩ : syracuseStep 19694717 = 7385519) B7385519
theorem B13129811 : Blo 1917435 13129811 := bstep (se 1 (by rfl) ⟨9847358, by rfl⟩ : syracuseStep 13129811 = 19694717) B19694717
theorem B8753207 : Blo 1917435 8753207 := bstep (se 1 (by rfl) ⟨6564905, by rfl⟩ : syracuseStep 8753207 = 13129811) B13129811
theorem B93367541 : Blo 1917435 93367541 := bstep (se 5 (by rfl) ⟨4376603, by rfl⟩ : syracuseStep 93367541 = 8753207) B8753207
theorem B62245027 : Blo 1917435 62245027 := bstep (se 1 (by rfl) ⟨46683770, by rfl⟩ : syracuseStep 62245027 = 93367541) B93367541
theorem B82993369 : Blo 1917435 82993369 := bstep (se 2 (by rfl) ⟨31122513, by rfl⟩ : syracuseStep 82993369 = 62245027) B62245027
theorem B110657825 : Blo 1917435 110657825 := bstep (se 2 (by rfl) ⟨41496684, by rfl⟩ : syracuseStep 110657825 = 82993369) B82993369
theorem B73771883 : Blo 1917435 73771883 := bstep (se 1 (by rfl) ⟨55328912, by rfl⟩ : syracuseStep 73771883 = 110657825) B110657825
theorem B49181255 : Blo 1917435 49181255 := bstep (se 1 (by rfl) ⟨36885941, by rfl⟩ : syracuseStep 49181255 = 73771883) B73771883
theorem B32787503 : Blo 1917435 32787503 := bstep (se 1 (by rfl) ⟨24590627, by rfl⟩ : syracuseStep 32787503 = 49181255) B49181255
theorem B21858335 : Blo 1917435 21858335 := bstep (se 1 (by rfl) ⟨16393751, by rfl⟩ : syracuseStep 21858335 = 32787503) B32787503
theorem B14572223 : Blo 1917435 14572223 := bstep (se 1 (by rfl) ⟨10929167, by rfl⟩ : syracuseStep 14572223 = 21858335) B21858335
theorem B9714815 : Blo 1917435 9714815 := bstep (se 1 (by rfl) ⟨7286111, by rfl⟩ : syracuseStep 9714815 = 14572223) B14572223
theorem B6476543 : Blo 1917435 6476543 := bstep (se 1 (by rfl) ⟨4857407, by rfl⟩ : syracuseStep 6476543 = 9714815) B9714815
theorem B4317695 : Blo 1917435 4317695 := bstep (se 1 (by rfl) ⟨3238271, by rfl⟩ : syracuseStep 4317695 = 6476543) B6476543
theorem B2878463 : Blo 1917435 2878463 := bstep (se 1 (by rfl) ⟨2158847, by rfl⟩ : syracuseStep 2878463 = 4317695) B4317695
theorem B1918975 : Blo 1917435 1918975 := bstep (se 1 (by rfl) ⟨1439231, by rfl⟩ : syracuseStep 1918975 = 2878463) B2878463
theorem B2878469 : Blo 1917435 2878469 := bbase (se 4 (by rfl) ⟨269856, by rfl⟩ : syracuseStep 2878469 = 539713) (by norm_num)
theorem B1918979 : Blo 1917435 1918979 := bstep (se 1 (by rfl) ⟨1439234, by rfl⟩ : syracuseStep 1918979 = 2878469) B2878469
theorem B3238285 : Blo 1917435 3238285 := bbase (se 3 (by rfl) ⟨607178, by rfl⟩ : syracuseStep 3238285 = 1214357) (by norm_num)
theorem B4317713 : Blo 1917435 4317713 := bstep (se 2 (by rfl) ⟨1619142, by rfl⟩ : syracuseStep 4317713 = 3238285) B3238285
theorem B2878475 : Blo 1917435 2878475 := bstep (se 1 (by rfl) ⟨2158856, by rfl⟩ : syracuseStep 2878475 = 4317713) B4317713
theorem B1918983 : Blo 1917435 1918983 := bstep (se 1 (by rfl) ⟨1439237, by rfl⟩ : syracuseStep 1918983 = 2878475) B2878475
theorem B2158861 : Blo 1917435 2158861 := bbase (se 3 (by rfl) ⟨404786, by rfl⟩ : syracuseStep 2158861 = 809573) (by norm_num)
theorem B2878481 : Blo 1917435 2878481 := bstep (se 2 (by rfl) ⟨1079430, by rfl⟩ : syracuseStep 2878481 = 2158861) B2158861
theorem B1918987 : Blo 1917435 1918987 := bstep (se 1 (by rfl) ⟨1439240, by rfl⟩ : syracuseStep 1918987 = 2878481) B2878481
theorem B6476597 : Blo 1917435 6476597 := bbase (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) (by norm_num)
theorem B4317731 : Blo 1917435 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B2878487 : Blo 1917435 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B1918991 : Blo 1917435 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B2878493 : Blo 1917435 2878493 := bbase (se 3 (by rfl) ⟨539717, by rfl⟩ : syracuseStep 2878493 = 1079435) (by norm_num)
theorem B1918995 : Blo 1917435 1918995 := bstep (se 1 (by rfl) ⟨1439246, by rfl⟩ : syracuseStep 1918995 = 2878493) B2878493
theorem B4317749 : Blo 1917435 4317749 := bbase (se 5 (by rfl) ⟨202394, by rfl⟩ : syracuseStep 4317749 = 404789) (by norm_num)
theorem B2878499 : Blo 1917435 2878499 := bstep (se 1 (by rfl) ⟨2158874, by rfl⟩ : syracuseStep 2878499 = 4317749) B4317749
theorem B1918999 : Blo 1917435 1918999 := bstep (se 1 (by rfl) ⟨1439249, by rfl⟩ : syracuseStep 1918999 = 2878499) B2878499
theorem B8196997 : Blo 1917435 8196997 := bbase (se 4 (by rfl) ⟨768468, by rfl⟩ : syracuseStep 8196997 = 1536937) (by norm_num)
theorem B10929329 : Blo 1917435 10929329 := bstep (se 2 (by rfl) ⟨4098498, by rfl⟩ : syracuseStep 10929329 = 8196997) B8196997
theorem B7286219 : Blo 1917435 7286219 := bstep (se 1 (by rfl) ⟨5464664, by rfl⟩ : syracuseStep 7286219 = 10929329) B10929329
theorem B4857479 : Blo 1917435 4857479 := bstep (se 1 (by rfl) ⟨3643109, by rfl⟩ : syracuseStep 4857479 = 7286219) B7286219
theorem B3238319 : Blo 1917435 3238319 := bstep (se 1 (by rfl) ⟨2428739, by rfl⟩ : syracuseStep 3238319 = 4857479) B4857479
theorem B2158879 : Blo 1917435 2158879 := bstep (se 1 (by rfl) ⟨1619159, by rfl⟩ : syracuseStep 2158879 = 3238319) B3238319
theorem B2878505 : Blo 1917435 2878505 := bstep (se 2 (by rfl) ⟨1079439, by rfl⟩ : syracuseStep 2878505 = 2158879) B2158879
theorem B1919003 : Blo 1917435 1919003 := bstep (se 1 (by rfl) ⟨1439252, by rfl⟩ : syracuseStep 1919003 = 2878505) B2878505
theorem B8197013 : Blo 1917435 8197013 := bbase (se 6 (by rfl) ⟨192117, by rfl⟩ : syracuseStep 8197013 = 384235) (by norm_num)
theorem B5464675 : Blo 1917435 5464675 := bstep (se 1 (by rfl) ⟨4098506, by rfl⟩ : syracuseStep 5464675 = 8197013) B8197013
theorem B7286233 : Blo 1917435 7286233 := bstep (se 2 (by rfl) ⟨2732337, by rfl⟩ : syracuseStep 7286233 = 5464675) B5464675
theorem B9714977 : Blo 1917435 9714977 := bstep (se 2 (by rfl) ⟨3643116, by rfl⟩ : syracuseStep 9714977 = 7286233) B7286233
theorem B6476651 : Blo 1917435 6476651 := bstep (se 1 (by rfl) ⟨4857488, by rfl⟩ : syracuseStep 6476651 = 9714977) B9714977
theorem B4317767 : Blo 1917435 4317767 := bstep (se 1 (by rfl) ⟨3238325, by rfl⟩ : syracuseStep 4317767 = 6476651) B6476651
theorem B2878511 : Blo 1917435 2878511 := bstep (se 1 (by rfl) ⟨2158883, by rfl⟩ : syracuseStep 2878511 = 4317767) B4317767
theorem B1919007 : Blo 1917435 1919007 := bstep (se 1 (by rfl) ⟨1439255, by rfl⟩ : syracuseStep 1919007 = 2878511) B2878511
theorem B2878517 : Blo 1917435 2878517 := bbase (se 5 (by rfl) ⟨134930, by rfl⟩ : syracuseStep 2878517 = 269861) (by norm_num)
theorem B1919011 : Blo 1917435 1919011 := bstep (se 1 (by rfl) ⟨1439258, by rfl⟩ : syracuseStep 1919011 = 2878517) B2878517
theorem B4857509 : Blo 1917435 4857509 := bbase (se 4 (by rfl) ⟨455391, by rfl⟩ : syracuseStep 4857509 = 910783) (by norm_num)
theorem B3238339 : Blo 1917435 3238339 := bstep (se 1 (by rfl) ⟨2428754, by rfl⟩ : syracuseStep 3238339 = 4857509) B4857509
theorem B4317785 : Blo 1917435 4317785 := bstep (se 2 (by rfl) ⟨1619169, by rfl⟩ : syracuseStep 4317785 = 3238339) B3238339
theorem B2878523 : Blo 1917435 2878523 := bstep (se 1 (by rfl) ⟨2158892, by rfl⟩ : syracuseStep 2878523 = 4317785) B4317785
theorem B1919015 : Blo 1917435 1919015 := bstep (se 1 (by rfl) ⟨1439261, by rfl⟩ : syracuseStep 1919015 = 2878523) B2878523
theorem B2158897 : Blo 1917435 2158897 := bbase (se 2 (by rfl) ⟨809586, by rfl⟩ : syracuseStep 2158897 = 1619173) (by norm_num)
theorem B2878529 : Blo 1917435 2878529 := bstep (se 2 (by rfl) ⟨1079448, by rfl⟩ : syracuseStep 2878529 = 2158897) B2158897
theorem B1919019 : Blo 1917435 1919019 := bstep (se 1 (by rfl) ⟨1439264, by rfl⟩ : syracuseStep 1919019 = 2878529) B2878529
theorem B4098541 : Blo 1917435 4098541 := bbase (se 3 (by rfl) ⟨768476, by rfl⟩ : syracuseStep 4098541 = 1536953) (by norm_num)
theorem B5464721 : Blo 1917435 5464721 := bstep (se 2 (by rfl) ⟨2049270, by rfl⟩ : syracuseStep 5464721 = 4098541) B4098541
theorem B3643147 : Blo 1917435 3643147 := bstep (se 1 (by rfl) ⟨2732360, by rfl⟩ : syracuseStep 3643147 = 5464721) B5464721
theorem B4857529 : Blo 1917435 4857529 := bstep (se 2 (by rfl) ⟨1821573, by rfl⟩ : syracuseStep 4857529 = 3643147) B3643147
theorem B6476705 : Blo 1917435 6476705 := bstep (se 2 (by rfl) ⟨2428764, by rfl⟩ : syracuseStep 6476705 = 4857529) B4857529
theorem B4317803 : Blo 1917435 4317803 := bstep (se 1 (by rfl) ⟨3238352, by rfl⟩ : syracuseStep 4317803 = 6476705) B6476705
theorem B2878535 : Blo 1917435 2878535 := bstep (se 1 (by rfl) ⟨2158901, by rfl⟩ : syracuseStep 2878535 = 4317803) B4317803
theorem B1919023 : Blo 1917435 1919023 := bstep (se 1 (by rfl) ⟨1439267, by rfl⟩ : syracuseStep 1919023 = 2878535) B2878535
theorem B2878541 : Blo 1917435 2878541 := bbase (se 3 (by rfl) ⟨539726, by rfl⟩ : syracuseStep 2878541 = 1079453) (by norm_num)
theorem B1919027 : Blo 1917435 1919027 := bstep (se 1 (by rfl) ⟨1439270, by rfl⟩ : syracuseStep 1919027 = 2878541) B2878541
theorem B4317821 : Blo 1917435 4317821 := bbase (se 3 (by rfl) ⟨809591, by rfl⟩ : syracuseStep 4317821 = 1619183) (by norm_num)
theorem B2878547 : Blo 1917435 2878547 := bstep (se 1 (by rfl) ⟨2158910, by rfl⟩ : syracuseStep 2878547 = 4317821) B4317821
theorem B1919031 : Blo 1917435 1919031 := bstep (se 1 (by rfl) ⟨1439273, by rfl⟩ : syracuseStep 1919031 = 2878547) B2878547
theorem B3238373 : Blo 1917435 3238373 := bbase (se 4 (by rfl) ⟨303597, by rfl⟩ : syracuseStep 3238373 = 607195) (by norm_num)
theorem B2158915 : Blo 1917435 2158915 := bstep (se 1 (by rfl) ⟨1619186, by rfl⟩ : syracuseStep 2158915 = 3238373) B3238373
theorem B2878553 : Blo 1917435 2878553 := bstep (se 2 (by rfl) ⟨1079457, by rfl⟩ : syracuseStep 2878553 = 2158915) B2158915
theorem B1919035 : Blo 1917435 1919035 := bstep (se 1 (by rfl) ⟨1439276, by rfl⟩ : syracuseStep 1919035 = 2878553) B2878553
theorem B13832693 : Blo 1917435 13832693 := bbase (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) (by norm_num)
theorem B9221795 : Blo 1917435 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B6147863 : Blo 1917435 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B4098575 : Blo 1917435 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B2732383 : Blo 1917435 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B14572709 : Blo 1917435 14572709 := bstep (se 4 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 14572709 = 2732383) B2732383
theorem B9715139 : Blo 1917435 9715139 := bstep (se 1 (by rfl) ⟨7286354, by rfl⟩ : syracuseStep 9715139 = 14572709) B14572709
theorem B6476759 : Blo 1917435 6476759 := bstep (se 1 (by rfl) ⟨4857569, by rfl⟩ : syracuseStep 6476759 = 9715139) B9715139
theorem B4317839 : Blo 1917435 4317839 := bstep (se 1 (by rfl) ⟨3238379, by rfl⟩ : syracuseStep 4317839 = 6476759) B6476759
theorem B2878559 : Blo 1917435 2878559 := bstep (se 1 (by rfl) ⟨2158919, by rfl⟩ : syracuseStep 2878559 = 4317839) B4317839
theorem B1919039 : Blo 1917435 1919039 := bstep (se 1 (by rfl) ⟨1439279, by rfl⟩ : syracuseStep 1919039 = 2878559) B2878559
theorem B2878565 : Blo 1917435 2878565 := bbase (se 4 (by rfl) ⟨269865, by rfl⟩ : syracuseStep 2878565 = 539731) (by norm_num)
theorem B1919043 : Blo 1917435 1919043 := bstep (se 1 (by rfl) ⟨1439282, by rfl⟩ : syracuseStep 1919043 = 2878565) B2878565
theorem B3458189 : Blo 1917435 3458189 := bbase (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) (by norm_num)
theorem B2305459 : Blo 1917435 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B3073945 : Blo 1917435 3073945 := bstep (se 2 (by rfl) ⟨1152729, by rfl⟩ : syracuseStep 3073945 = 2305459) B2305459
theorem B4098593 : Blo 1917435 4098593 := bstep (se 2 (by rfl) ⟨1536972, by rfl⟩ : syracuseStep 4098593 = 3073945) B3073945
theorem B2732395 : Blo 1917435 2732395 := bstep (se 1 (by rfl) ⟨2049296, by rfl⟩ : syracuseStep 2732395 = 4098593) B4098593
theorem B3643193 : Blo 1917435 3643193 := bstep (se 2 (by rfl) ⟨1366197, by rfl⟩ : syracuseStep 3643193 = 2732395) B2732395
theorem B2428795 : Blo 1917435 2428795 := bstep (se 1 (by rfl) ⟨1821596, by rfl⟩ : syracuseStep 2428795 = 3643193) B3643193
theorem B3238393 : Blo 1917435 3238393 := bstep (se 2 (by rfl) ⟨1214397, by rfl⟩ : syracuseStep 3238393 = 2428795) B2428795
theorem B4317857 : Blo 1917435 4317857 := bstep (se 2 (by rfl) ⟨1619196, by rfl⟩ : syracuseStep 4317857 = 3238393) B3238393
theorem B2878571 : Blo 1917435 2878571 := bstep (se 1 (by rfl) ⟨2158928, by rfl⟩ : syracuseStep 2878571 = 4317857) B4317857
theorem B1919047 : Blo 1917435 1919047 := bstep (se 1 (by rfl) ⟨1439285, by rfl⟩ : syracuseStep 1919047 = 2878571) B2878571
theorem B2158933 : Blo 1917435 2158933 := bbase (se 10 (by rfl) ⟨3162, by rfl⟩ : syracuseStep 2158933 = 6325) (by norm_num)
theorem B2878577 : Blo 1917435 2878577 := bstep (se 2 (by rfl) ⟨1079466, by rfl⟩ : syracuseStep 2878577 = 2158933) B2158933
theorem B1919051 : Blo 1917435 1919051 := bstep (se 1 (by rfl) ⟨1439288, by rfl⟩ : syracuseStep 1919051 = 2878577) B2878577
theorem B2428805 : Blo 1917435 2428805 := bbase (se 4 (by rfl) ⟨227700, by rfl⟩ : syracuseStep 2428805 = 455401) (by norm_num)
theorem B6476813 : Blo 1917435 6476813 := bstep (se 3 (by rfl) ⟨1214402, by rfl⟩ : syracuseStep 6476813 = 2428805) B2428805
theorem B4317875 : Blo 1917435 4317875 := bstep (se 1 (by rfl) ⟨3238406, by rfl⟩ : syracuseStep 4317875 = 6476813) B6476813
theorem B2878583 : Blo 1917435 2878583 := bstep (se 1 (by rfl) ⟨2158937, by rfl⟩ : syracuseStep 2878583 = 4317875) B4317875
theorem B1919055 : Blo 1917435 1919055 := bstep (se 1 (by rfl) ⟨1439291, by rfl⟩ : syracuseStep 1919055 = 2878583) B2878583
theorem B2878589 : Blo 1917435 2878589 := bbase (se 3 (by rfl) ⟨539735, by rfl⟩ : syracuseStep 2878589 = 1079471) (by norm_num)
theorem B1919059 : Blo 1917435 1919059 := bstep (se 1 (by rfl) ⟨1439294, by rfl⟩ : syracuseStep 1919059 = 2878589) B2878589
theorem B4317893 : Blo 1917435 4317893 := bbase (se 4 (by rfl) ⟨404802, by rfl⟩ : syracuseStep 4317893 = 809605) (by norm_num)
theorem B2878595 : Blo 1917435 2878595 := bstep (se 1 (by rfl) ⟨2158946, by rfl⟩ : syracuseStep 2878595 = 4317893) B4317893
theorem B1919063 : Blo 1917435 1919063 := bstep (se 1 (by rfl) ⟨1439297, by rfl⟩ : syracuseStep 1919063 = 2878595) B2878595
theorem B18443861 : Blo 1917435 18443861 := bbase (se 8 (by rfl) ⟨108069, by rfl⟩ : syracuseStep 18443861 = 216139) (by norm_num)
theorem B12295907 : Blo 1917435 12295907 := bstep (se 1 (by rfl) ⟨9221930, by rfl⟩ : syracuseStep 12295907 = 18443861) B18443861
theorem B8197271 : Blo 1917435 8197271 := bstep (se 1 (by rfl) ⟨6147953, by rfl⟩ : syracuseStep 8197271 = 12295907) B12295907
theorem B5464847 : Blo 1917435 5464847 := bstep (se 1 (by rfl) ⟨4098635, by rfl⟩ : syracuseStep 5464847 = 8197271) B8197271
theorem B3643231 : Blo 1917435 3643231 := bstep (se 1 (by rfl) ⟨2732423, by rfl⟩ : syracuseStep 3643231 = 5464847) B5464847
theorem B4857641 : Blo 1917435 4857641 := bstep (se 2 (by rfl) ⟨1821615, by rfl⟩ : syracuseStep 4857641 = 3643231) B3643231
theorem B3238427 : Blo 1917435 3238427 := bstep (se 1 (by rfl) ⟨2428820, by rfl⟩ : syracuseStep 3238427 = 4857641) B4857641
theorem B2158951 : Blo 1917435 2158951 := bstep (se 1 (by rfl) ⟨1619213, by rfl⟩ : syracuseStep 2158951 = 3238427) B3238427
theorem B2878601 : Blo 1917435 2878601 := bstep (se 2 (by rfl) ⟨1079475, by rfl⟩ : syracuseStep 2878601 = 2158951) B2158951
theorem B1919067 : Blo 1917435 1919067 := bstep (se 1 (by rfl) ⟨1439300, by rfl⟩ : syracuseStep 1919067 = 2878601) B2878601
theorem B9715301 : Blo 1917435 9715301 := bbase (se 4 (by rfl) ⟨910809, by rfl⟩ : syracuseStep 9715301 = 1821619) (by norm_num)
theorem B6476867 : Blo 1917435 6476867 := bstep (se 1 (by rfl) ⟨4857650, by rfl⟩ : syracuseStep 6476867 = 9715301) B9715301
theorem B4317911 : Blo 1917435 4317911 := bstep (se 1 (by rfl) ⟨3238433, by rfl⟩ : syracuseStep 4317911 = 6476867) B6476867
theorem B2878607 : Blo 1917435 2878607 := bstep (se 1 (by rfl) ⟨2158955, by rfl⟩ : syracuseStep 2878607 = 4317911) B4317911
theorem B1919071 : Blo 1917435 1919071 := bstep (se 1 (by rfl) ⟨1439303, by rfl⟩ : syracuseStep 1919071 = 2878607) B2878607
theorem B2878613 : Blo 1917435 2878613 := bbase (se 6 (by rfl) ⟨67467, by rfl⟩ : syracuseStep 2878613 = 134935) (by norm_num)
theorem B1919075 : Blo 1917435 1919075 := bstep (se 1 (by rfl) ⟨1439306, by rfl⟩ : syracuseStep 1919075 = 2878613) B2878613
theorem B13832981 : Blo 1917435 13832981 := bbase (se 6 (by rfl) ⟨324210, by rfl⟩ : syracuseStep 13832981 = 648421) (by norm_num)
theorem B9221987 : Blo 1917435 9221987 := bstep (se 1 (by rfl) ⟨6916490, by rfl⟩ : syracuseStep 9221987 = 13832981) B13832981
theorem B6147991 : Blo 1917435 6147991 := bstep (se 1 (by rfl) ⟨4610993, by rfl⟩ : syracuseStep 6147991 = 9221987) B9221987
theorem B8197321 : Blo 1917435 8197321 := bstep (se 2 (by rfl) ⟨3073995, by rfl⟩ : syracuseStep 8197321 = 6147991) B6147991
theorem B10929761 : Blo 1917435 10929761 := bstep (se 2 (by rfl) ⟨4098660, by rfl⟩ : syracuseStep 10929761 = 8197321) B8197321
theorem B7286507 : Blo 1917435 7286507 := bstep (se 1 (by rfl) ⟨5464880, by rfl⟩ : syracuseStep 7286507 = 10929761) B10929761
theorem B4857671 : Blo 1917435 4857671 := bstep (se 1 (by rfl) ⟨3643253, by rfl⟩ : syracuseStep 4857671 = 7286507) B7286507
theorem B3238447 : Blo 1917435 3238447 := bstep (se 1 (by rfl) ⟨2428835, by rfl⟩ : syracuseStep 3238447 = 4857671) B4857671
theorem B4317929 : Blo 1917435 4317929 := bstep (se 2 (by rfl) ⟨1619223, by rfl⟩ : syracuseStep 4317929 = 3238447) B3238447
theorem B2878619 : Blo 1917435 2878619 := bstep (se 1 (by rfl) ⟨2158964, by rfl⟩ : syracuseStep 2878619 = 4317929) B4317929
theorem B1919079 : Blo 1917435 1919079 := bstep (se 1 (by rfl) ⟨1439309, by rfl⟩ : syracuseStep 1919079 = 2878619) B2878619
theorem B2158969 : Blo 1917435 2158969 := bbase (se 2 (by rfl) ⟨809613, by rfl⟩ : syracuseStep 2158969 = 1619227) (by norm_num)
theorem B2878625 : Blo 1917435 2878625 := bstep (se 2 (by rfl) ⟨1079484, by rfl⟩ : syracuseStep 2878625 = 2158969) B2158969
theorem B1919083 : Blo 1917435 1919083 := bstep (se 1 (by rfl) ⟨1439312, by rfl⟩ : syracuseStep 1919083 = 2878625) B2878625
theorem B13130581 : Blo 1917435 13130581 := bbase (se 9 (by rfl) ⟨38468, by rfl⟩ : syracuseStep 13130581 = 76937) (by norm_num)
theorem B17507441 : Blo 1917435 17507441 := bstep (se 2 (by rfl) ⟨6565290, by rfl⟩ : syracuseStep 17507441 = 13130581) B13130581
theorem B11671627 : Blo 1917435 11671627 := bstep (se 1 (by rfl) ⟨8753720, by rfl⟩ : syracuseStep 11671627 = 17507441) B17507441
theorem B15562169 : Blo 1917435 15562169 := bstep (se 2 (by rfl) ⟨5835813, by rfl⟩ : syracuseStep 15562169 = 11671627) B11671627
theorem B10374779 : Blo 1917435 10374779 := bstep (se 1 (by rfl) ⟨7781084, by rfl⟩ : syracuseStep 10374779 = 15562169) B15562169
theorem B6916519 : Blo 1917435 6916519 := bstep (se 1 (by rfl) ⟨5187389, by rfl⟩ : syracuseStep 6916519 = 10374779) B10374779
theorem B9222025 : Blo 1917435 9222025 := bstep (se 2 (by rfl) ⟨3458259, by rfl⟩ : syracuseStep 9222025 = 6916519) B6916519
theorem B12296033 : Blo 1917435 12296033 := bstep (se 2 (by rfl) ⟨4611012, by rfl⟩ : syracuseStep 12296033 = 9222025) B9222025
theorem B8197355 : Blo 1917435 8197355 := bstep (se 1 (by rfl) ⟨6148016, by rfl⟩ : syracuseStep 8197355 = 12296033) B12296033
theorem B5464903 : Blo 1917435 5464903 := bstep (se 1 (by rfl) ⟨4098677, by rfl⟩ : syracuseStep 5464903 = 8197355) B8197355
theorem B7286537 : Blo 1917435 7286537 := bstep (se 2 (by rfl) ⟨2732451, by rfl⟩ : syracuseStep 7286537 = 5464903) B5464903
theorem B4857691 : Blo 1917435 4857691 := bstep (se 1 (by rfl) ⟨3643268, by rfl⟩ : syracuseStep 4857691 = 7286537) B7286537
theorem B6476921 : Blo 1917435 6476921 := bstep (se 2 (by rfl) ⟨2428845, by rfl⟩ : syracuseStep 6476921 = 4857691) B4857691
theorem B4317947 : Blo 1917435 4317947 := bstep (se 1 (by rfl) ⟨3238460, by rfl⟩ : syracuseStep 4317947 = 6476921) B6476921
theorem B2878631 : Blo 1917435 2878631 := bstep (se 1 (by rfl) ⟨2158973, by rfl⟩ : syracuseStep 2878631 = 4317947) B4317947
theorem B1919087 : Blo 1917435 1919087 := bstep (se 1 (by rfl) ⟨1439315, by rfl⟩ : syracuseStep 1919087 = 2878631) B2878631
theorem B2878637 : Blo 1917435 2878637 := bbase (se 3 (by rfl) ⟨539744, by rfl⟩ : syracuseStep 2878637 = 1079489) (by norm_num)
theorem B1919091 : Blo 1917435 1919091 := bstep (se 1 (by rfl) ⟨1439318, by rfl⟩ : syracuseStep 1919091 = 2878637) B2878637
theorem B4317965 : Blo 1917435 4317965 := bbase (se 3 (by rfl) ⟨809618, by rfl⟩ : syracuseStep 4317965 = 1619237) (by norm_num)
theorem B2878643 : Blo 1917435 2878643 := bstep (se 1 (by rfl) ⟨2158982, by rfl⟩ : syracuseStep 2878643 = 4317965) B4317965
theorem B1919095 : Blo 1917435 1919095 := bstep (se 1 (by rfl) ⟨1439321, by rfl⟩ : syracuseStep 1919095 = 2878643) B2878643
theorem B2428861 : Blo 1917435 2428861 := bbase (se 3 (by rfl) ⟨455411, by rfl⟩ : syracuseStep 2428861 = 910823) (by norm_num)
theorem B3238481 : Blo 1917435 3238481 := bstep (se 2 (by rfl) ⟨1214430, by rfl⟩ : syracuseStep 3238481 = 2428861) B2428861
theorem B2158987 : Blo 1917435 2158987 := bstep (se 1 (by rfl) ⟨1619240, by rfl⟩ : syracuseStep 2158987 = 3238481) B3238481
theorem B2878649 : Blo 1917435 2878649 := bstep (se 2 (by rfl) ⟨1079493, by rfl⟩ : syracuseStep 2878649 = 2158987) B2158987
theorem B1919099 : Blo 1917435 1919099 := bstep (se 1 (by rfl) ⟨1439324, by rfl⟩ : syracuseStep 1919099 = 2878649) B2878649
theorem B9222101 : Blo 1917435 9222101 := bbase (se 7 (by rfl) ⟨108071, by rfl⟩ : syracuseStep 9222101 = 216143) (by norm_num)
theorem B6148067 : Blo 1917435 6148067 := bstep (se 1 (by rfl) ⟨4611050, by rfl⟩ : syracuseStep 6148067 = 9222101) B9222101
theorem B16394845 : Blo 1917435 16394845 := bstep (se 3 (by rfl) ⟨3074033, by rfl⟩ : syracuseStep 16394845 = 6148067) B6148067
theorem B21859793 : Blo 1917435 21859793 := bstep (se 2 (by rfl) ⟨8197422, by rfl⟩ : syracuseStep 21859793 = 16394845) B16394845
theorem B14573195 : Blo 1917435 14573195 := bstep (se 1 (by rfl) ⟨10929896, by rfl⟩ : syracuseStep 14573195 = 21859793) B21859793
theorem B9715463 : Blo 1917435 9715463 := bstep (se 1 (by rfl) ⟨7286597, by rfl⟩ : syracuseStep 9715463 = 14573195) B14573195
theorem B6476975 : Blo 1917435 6476975 := bstep (se 1 (by rfl) ⟨4857731, by rfl⟩ : syracuseStep 6476975 = 9715463) B9715463
theorem B4317983 : Blo 1917435 4317983 := bstep (se 1 (by rfl) ⟨3238487, by rfl⟩ : syracuseStep 4317983 = 6476975) B6476975
theorem B2878655 : Blo 1917435 2878655 := bstep (se 1 (by rfl) ⟨2158991, by rfl⟩ : syracuseStep 2878655 = 4317983) B4317983
theorem B1919103 : Blo 1917435 1919103 := bstep (se 1 (by rfl) ⟨1439327, by rfl⟩ : syracuseStep 1919103 = 2878655) B2878655
theorem B2878661 : Blo 1917435 2878661 := bbase (se 4 (by rfl) ⟨269874, by rfl⟩ : syracuseStep 2878661 = 539749) (by norm_num)
theorem B1919107 : Blo 1917435 1919107 := bstep (se 1 (by rfl) ⟨1439330, by rfl⟩ : syracuseStep 1919107 = 2878661) B2878661
theorem B3238501 : Blo 1917435 3238501 := bbase (se 4 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 3238501 = 607219) (by norm_num)
theorem B4318001 : Blo 1917435 4318001 := bstep (se 2 (by rfl) ⟨1619250, by rfl⟩ : syracuseStep 4318001 = 3238501) B3238501
theorem B2878667 : Blo 1917435 2878667 := bstep (se 1 (by rfl) ⟨2159000, by rfl⟩ : syracuseStep 2878667 = 4318001) B4318001
theorem B1919111 : Blo 1917435 1919111 := bstep (se 1 (by rfl) ⟨1439333, by rfl⟩ : syracuseStep 1919111 = 2878667) B2878667
theorem B2159005 : Blo 1917435 2159005 := bbase (se 3 (by rfl) ⟨404813, by rfl⟩ : syracuseStep 2159005 = 809627) (by norm_num)
theorem B2878673 : Blo 1917435 2878673 := bstep (se 2 (by rfl) ⟨1079502, by rfl⟩ : syracuseStep 2878673 = 2159005) B2159005
theorem B1919115 : Blo 1917435 1919115 := bstep (se 1 (by rfl) ⟨1439336, by rfl⟩ : syracuseStep 1919115 = 2878673) B2878673
theorem B6477029 : Blo 1917435 6477029 := bbase (se 4 (by rfl) ⟨607221, by rfl⟩ : syracuseStep 6477029 = 1214443) (by norm_num)
theorem B4318019 : Blo 1917435 4318019 := bstep (se 1 (by rfl) ⟨3238514, by rfl⟩ : syracuseStep 4318019 = 6477029) B6477029
theorem B2878679 : Blo 1917435 2878679 := bstep (se 1 (by rfl) ⟨2159009, by rfl⟩ : syracuseStep 2878679 = 4318019) B4318019
theorem B1919119 : Blo 1917435 1919119 := bstep (se 1 (by rfl) ⟨1439339, by rfl⟩ : syracuseStep 1919119 = 2878679) B2878679
theorem B2878685 : Blo 1917435 2878685 := bbase (se 3 (by rfl) ⟨539753, by rfl⟩ : syracuseStep 2878685 = 1079507) (by norm_num)
theorem B1919123 : Blo 1917435 1919123 := bstep (se 1 (by rfl) ⟨1439342, by rfl⟩ : syracuseStep 1919123 = 2878685) B2878685
theorem B4318037 : Blo 1917435 4318037 := bbase (se 9 (by rfl) ⟨12650, by rfl⟩ : syracuseStep 4318037 = 25301) (by norm_num)
theorem B2878691 : Blo 1917435 2878691 := bstep (se 1 (by rfl) ⟨2159018, by rfl⟩ : syracuseStep 2878691 = 4318037) B4318037
theorem B1919127 : Blo 1917435 1919127 := bstep (se 1 (by rfl) ⟨1439345, by rfl⟩ : syracuseStep 1919127 = 2878691) B2878691
theorem B5465029 : Blo 1917435 5465029 := bbase (se 4 (by rfl) ⟨512346, by rfl⟩ : syracuseStep 5465029 = 1024693) (by norm_num)
theorem B7286705 : Blo 1917435 7286705 := bstep (se 2 (by rfl) ⟨2732514, by rfl⟩ : syracuseStep 7286705 = 5465029) B5465029
theorem B4857803 : Blo 1917435 4857803 := bstep (se 1 (by rfl) ⟨3643352, by rfl⟩ : syracuseStep 4857803 = 7286705) B7286705
theorem B3238535 : Blo 1917435 3238535 := bstep (se 1 (by rfl) ⟨2428901, by rfl⟩ : syracuseStep 3238535 = 4857803) B4857803
theorem B2159023 : Blo 1917435 2159023 := bstep (se 1 (by rfl) ⟨1619267, by rfl⟩ : syracuseStep 2159023 = 3238535) B3238535
theorem B2878697 : Blo 1917435 2878697 := bstep (se 2 (by rfl) ⟨1079511, by rfl⟩ : syracuseStep 2878697 = 2159023) B2159023
theorem B1919131 : Blo 1917435 1919131 := bstep (se 1 (by rfl) ⟨1439348, by rfl⟩ : syracuseStep 1919131 = 2878697) B2878697
theorem B2462045 : Blo 1917435 2462045 := bbase (se 3 (by rfl) ⟨461633, by rfl⟩ : syracuseStep 2462045 = 923267) (by norm_num)
theorem B26261813 : Blo 1917435 26261813 := bstep (se 5 (by rfl) ⟨1231022, by rfl⟩ : syracuseStep 26261813 = 2462045) B2462045
theorem B17507875 : Blo 1917435 17507875 := bstep (se 1 (by rfl) ⟨13130906, by rfl⟩ : syracuseStep 17507875 = 26261813) B26261813
theorem B23343833 : Blo 1917435 23343833 := bstep (se 2 (by rfl) ⟨8753937, by rfl⟩ : syracuseStep 23343833 = 17507875) B17507875
theorem B62250221 : Blo 1917435 62250221 := bstep (se 3 (by rfl) ⟨11671916, by rfl⟩ : syracuseStep 62250221 = 23343833) B23343833
theorem B41500147 : Blo 1917435 41500147 := bstep (se 1 (by rfl) ⟨31125110, by rfl⟩ : syracuseStep 41500147 = 62250221) B62250221
theorem B55333529 : Blo 1917435 55333529 := bstep (se 2 (by rfl) ⟨20750073, by rfl⟩ : syracuseStep 55333529 = 41500147) B41500147
theorem B36889019 : Blo 1917435 36889019 := bstep (se 1 (by rfl) ⟨27666764, by rfl⟩ : syracuseStep 36889019 = 55333529) B55333529
theorem B24592679 : Blo 1917435 24592679 := bstep (se 1 (by rfl) ⟨18444509, by rfl⟩ : syracuseStep 24592679 = 36889019) B36889019
theorem B16395119 : Blo 1917435 16395119 := bstep (se 1 (by rfl) ⟨12296339, by rfl⟩ : syracuseStep 16395119 = 24592679) B24592679
theorem B10930079 : Blo 1917435 10930079 := bstep (se 1 (by rfl) ⟨8197559, by rfl⟩ : syracuseStep 10930079 = 16395119) B16395119
theorem B7286719 : Blo 1917435 7286719 := bstep (se 1 (by rfl) ⟨5465039, by rfl⟩ : syracuseStep 7286719 = 10930079) B10930079
theorem B9715625 : Blo 1917435 9715625 := bstep (se 2 (by rfl) ⟨3643359, by rfl⟩ : syracuseStep 9715625 = 7286719) B7286719
theorem B6477083 : Blo 1917435 6477083 := bstep (se 1 (by rfl) ⟨4857812, by rfl⟩ : syracuseStep 6477083 = 9715625) B9715625
theorem B4318055 : Blo 1917435 4318055 := bstep (se 1 (by rfl) ⟨3238541, by rfl⟩ : syracuseStep 4318055 = 6477083) B6477083
theorem B2878703 : Blo 1917435 2878703 := bstep (se 1 (by rfl) ⟨2159027, by rfl⟩ : syracuseStep 2878703 = 4318055) B4318055
theorem B1919135 : Blo 1917435 1919135 := bstep (se 1 (by rfl) ⟨1439351, by rfl⟩ : syracuseStep 1919135 = 2878703) B2878703
theorem B2878709 : Blo 1917435 2878709 := bbase (se 5 (by rfl) ⟨134939, by rfl⟩ : syracuseStep 2878709 = 269879) (by norm_num)
theorem B1919139 : Blo 1917435 1919139 := bstep (se 1 (by rfl) ⟨1439354, by rfl⟩ : syracuseStep 1919139 = 2878709) B2878709
theorem B20750165 : Blo 1917435 20750165 := bbase (se 9 (by rfl) ⟨60791, by rfl⟩ : syracuseStep 20750165 = 121583) (by norm_num)
theorem B13833443 : Blo 1917435 13833443 := bstep (se 1 (by rfl) ⟨10375082, by rfl⟩ : syracuseStep 13833443 = 20750165) B20750165
theorem B9222295 : Blo 1917435 9222295 := bstep (se 1 (by rfl) ⟨6916721, by rfl⟩ : syracuseStep 9222295 = 13833443) B13833443
theorem B12296393 : Blo 1917435 12296393 := bstep (se 2 (by rfl) ⟨4611147, by rfl⟩ : syracuseStep 12296393 = 9222295) B9222295
theorem B8197595 : Blo 1917435 8197595 := bstep (se 1 (by rfl) ⟨6148196, by rfl⟩ : syracuseStep 8197595 = 12296393) B12296393
theorem B5465063 : Blo 1917435 5465063 := bstep (se 1 (by rfl) ⟨4098797, by rfl⟩ : syracuseStep 5465063 = 8197595) B8197595
theorem B3643375 : Blo 1917435 3643375 := bstep (se 1 (by rfl) ⟨2732531, by rfl⟩ : syracuseStep 3643375 = 5465063) B5465063
theorem B4857833 : Blo 1917435 4857833 := bstep (se 2 (by rfl) ⟨1821687, by rfl⟩ : syracuseStep 4857833 = 3643375) B3643375
theorem B3238555 : Blo 1917435 3238555 := bstep (se 1 (by rfl) ⟨2428916, by rfl⟩ : syracuseStep 3238555 = 4857833) B4857833
theorem B4318073 : Blo 1917435 4318073 := bstep (se 2 (by rfl) ⟨1619277, by rfl⟩ : syracuseStep 4318073 = 3238555) B3238555
theorem B2878715 : Blo 1917435 2878715 := bstep (se 1 (by rfl) ⟨2159036, by rfl⟩ : syracuseStep 2878715 = 4318073) B4318073
theorem B1919143 : Blo 1917435 1919143 := bstep (se 1 (by rfl) ⟨1439357, by rfl⟩ : syracuseStep 1919143 = 2878715) B2878715
theorem B2159041 : Blo 1917435 2159041 := bbase (se 2 (by rfl) ⟨809640, by rfl⟩ : syracuseStep 2159041 = 1619281) (by norm_num)
theorem B2878721 : Blo 1917435 2878721 := bstep (se 2 (by rfl) ⟨1079520, by rfl⟩ : syracuseStep 2878721 = 2159041) B2159041
theorem B1919147 : Blo 1917435 1919147 := bstep (se 1 (by rfl) ⟨1439360, by rfl⟩ : syracuseStep 1919147 = 2878721) B2878721
theorem B4857853 : Blo 1917435 4857853 := bbase (se 3 (by rfl) ⟨910847, by rfl⟩ : syracuseStep 4857853 = 1821695) (by norm_num)
theorem B6477137 : Blo 1917435 6477137 := bstep (se 2 (by rfl) ⟨2428926, by rfl⟩ : syracuseStep 6477137 = 4857853) B4857853
theorem B4318091 : Blo 1917435 4318091 := bstep (se 1 (by rfl) ⟨3238568, by rfl⟩ : syracuseStep 4318091 = 6477137) B6477137
theorem B2878727 : Blo 1917435 2878727 := bstep (se 1 (by rfl) ⟨2159045, by rfl⟩ : syracuseStep 2878727 = 4318091) B4318091
theorem B1919151 : Blo 1917435 1919151 := bstep (se 1 (by rfl) ⟨1439363, by rfl⟩ : syracuseStep 1919151 = 2878727) B2878727
theorem B2878733 : Blo 1917435 2878733 := bbase (se 3 (by rfl) ⟨539762, by rfl⟩ : syracuseStep 2878733 = 1079525) (by norm_num)
theorem B1919155 : Blo 1917435 1919155 := bstep (se 1 (by rfl) ⟨1439366, by rfl⟩ : syracuseStep 1919155 = 2878733) B2878733
theorem B4318109 : Blo 1917435 4318109 := bbase (se 3 (by rfl) ⟨809645, by rfl⟩ : syracuseStep 4318109 = 1619291) (by norm_num)
theorem B2878739 : Blo 1917435 2878739 := bstep (se 1 (by rfl) ⟨2159054, by rfl⟩ : syracuseStep 2878739 = 4318109) B4318109
theorem B1919159 : Blo 1917435 1919159 := bstep (se 1 (by rfl) ⟨1439369, by rfl⟩ : syracuseStep 1919159 = 2878739) B2878739
theorem B3238589 : Blo 1917435 3238589 := bbase (se 3 (by rfl) ⟨607235, by rfl⟩ : syracuseStep 3238589 = 1214471) (by norm_num)
theorem B2159059 : Blo 1917435 2159059 := bstep (se 1 (by rfl) ⟨1619294, by rfl⟩ : syracuseStep 2159059 = 3238589) B3238589
theorem B2878745 : Blo 1917435 2878745 := bstep (se 2 (by rfl) ⟨1079529, by rfl⟩ : syracuseStep 2878745 = 2159059) B2159059
theorem B1919163 : Blo 1917435 1919163 := bstep (se 1 (by rfl) ⟨1439372, by rfl⟩ : syracuseStep 1919163 = 2878745) B2878745
theorem B10930261 : Blo 1917435 10930261 := bbase (se 8 (by rfl) ⟨64044, by rfl⟩ : syracuseStep 10930261 = 128089) (by norm_num)
theorem B14573681 : Blo 1917435 14573681 := bstep (se 2 (by rfl) ⟨5465130, by rfl⟩ : syracuseStep 14573681 = 10930261) B10930261
theorem B9715787 : Blo 1917435 9715787 := bstep (se 1 (by rfl) ⟨7286840, by rfl⟩ : syracuseStep 9715787 = 14573681) B14573681
theorem B6477191 : Blo 1917435 6477191 := bstep (se 1 (by rfl) ⟨4857893, by rfl⟩ : syracuseStep 6477191 = 9715787) B9715787
theorem B4318127 : Blo 1917435 4318127 := bstep (se 1 (by rfl) ⟨3238595, by rfl⟩ : syracuseStep 4318127 = 6477191) B6477191
theorem B2878751 : Blo 1917435 2878751 := bstep (se 1 (by rfl) ⟨2159063, by rfl⟩ : syracuseStep 2878751 = 4318127) B4318127
theorem B1919167 : Blo 1917435 1919167 := bstep (se 1 (by rfl) ⟨1439375, by rfl⟩ : syracuseStep 1919167 = 2878751) B2878751
theorem B2878757 : Blo 1917435 2878757 := bbase (se 4 (by rfl) ⟨269883, by rfl⟩ : syracuseStep 2878757 = 539767) (by norm_num)
theorem B1919171 : Blo 1917435 1919171 := bstep (se 1 (by rfl) ⟨1439378, by rfl⟩ : syracuseStep 1919171 = 2878757) B2878757
theorem B2428957 : Blo 1917435 2428957 := bbase (se 3 (by rfl) ⟨455429, by rfl⟩ : syracuseStep 2428957 = 910859) (by norm_num)
theorem B3238609 : Blo 1917435 3238609 := bstep (se 2 (by rfl) ⟨1214478, by rfl⟩ : syracuseStep 3238609 = 2428957) B2428957
theorem B4318145 : Blo 1917435 4318145 := bstep (se 2 (by rfl) ⟨1619304, by rfl⟩ : syracuseStep 4318145 = 3238609) B3238609
theorem B2878763 : Blo 1917435 2878763 := bstep (se 1 (by rfl) ⟨2159072, by rfl⟩ : syracuseStep 2878763 = 4318145) B4318145
theorem B1919175 : Blo 1917435 1919175 := bstep (se 1 (by rfl) ⟨1439381, by rfl⟩ : syracuseStep 1919175 = 2878763) B2878763
theorem B2159077 : Blo 1917435 2159077 := bbase (se 4 (by rfl) ⟨202413, by rfl⟩ : syracuseStep 2159077 = 404827) (by norm_num)
theorem B2878769 : Blo 1917435 2878769 := bstep (se 2 (by rfl) ⟨1079538, by rfl⟩ : syracuseStep 2878769 = 2159077) B2159077
theorem B1919179 : Blo 1917435 1919179 := bstep (se 1 (by rfl) ⟨1439384, by rfl⟩ : syracuseStep 1919179 = 2878769) B2878769
theorem B6148325 : Blo 1917435 6148325 := bbase (se 4 (by rfl) ⟨576405, by rfl⟩ : syracuseStep 6148325 = 1152811) (by norm_num)
theorem B4098883 : Blo 1917435 4098883 := bstep (se 1 (by rfl) ⟨3074162, by rfl⟩ : syracuseStep 4098883 = 6148325) B6148325
theorem B5465177 : Blo 1917435 5465177 := bstep (se 2 (by rfl) ⟨2049441, by rfl⟩ : syracuseStep 5465177 = 4098883) B4098883
theorem B3643451 : Blo 1917435 3643451 := bstep (se 1 (by rfl) ⟨2732588, by rfl⟩ : syracuseStep 3643451 = 5465177) B5465177
theorem B2428967 : Blo 1917435 2428967 := bstep (se 1 (by rfl) ⟨1821725, by rfl⟩ : syracuseStep 2428967 = 3643451) B3643451
theorem B6477245 : Blo 1917435 6477245 := bstep (se 3 (by rfl) ⟨1214483, by rfl⟩ : syracuseStep 6477245 = 2428967) B2428967
theorem B4318163 : Blo 1917435 4318163 := bstep (se 1 (by rfl) ⟨3238622, by rfl⟩ : syracuseStep 4318163 = 6477245) B6477245
theorem B2878775 : Blo 1917435 2878775 := bstep (se 1 (by rfl) ⟨2159081, by rfl⟩ : syracuseStep 2878775 = 4318163) B4318163
theorem B1919183 : Blo 1917435 1919183 := bstep (se 1 (by rfl) ⟨1439387, by rfl⟩ : syracuseStep 1919183 = 2878775) B2878775
theorem B2878781 : Blo 1917435 2878781 := bbase (se 3 (by rfl) ⟨539771, by rfl⟩ : syracuseStep 2878781 = 1079543) (by norm_num)
theorem B1919187 : Blo 1917435 1919187 := bstep (se 1 (by rfl) ⟨1439390, by rfl⟩ : syracuseStep 1919187 = 2878781) B2878781
theorem B4318181 : Blo 1917435 4318181 := bbase (se 4 (by rfl) ⟨404829, by rfl⟩ : syracuseStep 4318181 = 809659) (by norm_num)
theorem B2878787 : Blo 1917435 2878787 := bstep (se 1 (by rfl) ⟨2159090, by rfl⟩ : syracuseStep 2878787 = 4318181) B4318181
theorem B1919191 : Blo 1917435 1919191 := bstep (se 1 (by rfl) ⟨1439393, by rfl⟩ : syracuseStep 1919191 = 2878787) B2878787
theorem B4857965 : Blo 1917435 4857965 := bbase (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) (by norm_num)
theorem B3238643 : Blo 1917435 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B2159095 : Blo 1917435 2159095 := bstep (se 1 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 2159095 = 3238643) B3238643
theorem B2878793 : Blo 1917435 2878793 := bstep (se 2 (by rfl) ⟨1079547, by rfl⟩ : syracuseStep 2878793 = 2159095) B2159095
theorem B1919195 : Blo 1917435 1919195 := bstep (se 1 (by rfl) ⟨1439396, by rfl⟩ : syracuseStep 1919195 = 2878793) B2878793
theorem B4098917 : Blo 1917435 4098917 := bbase (se 4 (by rfl) ⟨384273, by rfl⟩ : syracuseStep 4098917 = 768547) (by norm_num)
theorem B2732611 : Blo 1917435 2732611 := bstep (se 1 (by rfl) ⟨2049458, by rfl⟩ : syracuseStep 2732611 = 4098917) B4098917
theorem B3643481 : Blo 1917435 3643481 := bstep (se 2 (by rfl) ⟨1366305, by rfl⟩ : syracuseStep 3643481 = 2732611) B2732611
theorem B9715949 : Blo 1917435 9715949 := bstep (se 3 (by rfl) ⟨1821740, by rfl⟩ : syracuseStep 9715949 = 3643481) B3643481
theorem B6477299 : Blo 1917435 6477299 := bstep (se 1 (by rfl) ⟨4857974, by rfl⟩ : syracuseStep 6477299 = 9715949) B9715949
theorem B4318199 : Blo 1917435 4318199 := bstep (se 1 (by rfl) ⟨3238649, by rfl⟩ : syracuseStep 4318199 = 6477299) B6477299
theorem B2878799 : Blo 1917435 2878799 := bstep (se 1 (by rfl) ⟨2159099, by rfl⟩ : syracuseStep 2878799 = 4318199) B4318199
theorem B1919199 : Blo 1917435 1919199 := bstep (se 1 (by rfl) ⟨1439399, by rfl⟩ : syracuseStep 1919199 = 2878799) B2878799
theorem B2878805 : Blo 1917435 2878805 := bbase (se 11 (by rfl) ⟨2108, by rfl⟩ : syracuseStep 2878805 = 4217) (by norm_num)
theorem B1919203 : Blo 1917435 1919203 := bstep (se 1 (by rfl) ⟨1439402, by rfl⟩ : syracuseStep 1919203 = 2878805) B2878805
theorem B3458477 : Blo 1917435 3458477 := bbase (se 3 (by rfl) ⟨648464, by rfl⟩ : syracuseStep 3458477 = 1296929) (by norm_num)
theorem B2305651 : Blo 1917435 2305651 := bstep (se 1 (by rfl) ⟨1729238, by rfl⟩ : syracuseStep 2305651 = 3458477) B3458477
theorem B3074201 : Blo 1917435 3074201 := bstep (se 2 (by rfl) ⟨1152825, by rfl⟩ : syracuseStep 3074201 = 2305651) B2305651
theorem B2049467 : Blo 1917435 2049467 := bstep (se 1 (by rfl) ⟨1537100, by rfl⟩ : syracuseStep 2049467 = 3074201) B3074201
theorem B5465245 : Blo 1917435 5465245 := bstep (se 3 (by rfl) ⟨1024733, by rfl⟩ : syracuseStep 5465245 = 2049467) B2049467
theorem B7286993 : Blo 1917435 7286993 := bstep (se 2 (by rfl) ⟨2732622, by rfl⟩ : syracuseStep 7286993 = 5465245) B5465245
theorem B4857995 : Blo 1917435 4857995 := bstep (se 1 (by rfl) ⟨3643496, by rfl⟩ : syracuseStep 4857995 = 7286993) B7286993
theorem B3238663 : Blo 1917435 3238663 := bstep (se 1 (by rfl) ⟨2428997, by rfl⟩ : syracuseStep 3238663 = 4857995) B4857995
theorem B4318217 : Blo 1917435 4318217 := bstep (se 2 (by rfl) ⟨1619331, by rfl⟩ : syracuseStep 4318217 = 3238663) B3238663
theorem B2878811 : Blo 1917435 2878811 := bstep (se 1 (by rfl) ⟨2159108, by rfl⟩ : syracuseStep 2878811 = 4318217) B4318217
theorem B1919207 : Blo 1917435 1919207 := bstep (se 1 (by rfl) ⟨1439405, by rfl⟩ : syracuseStep 1919207 = 2878811) B2878811
theorem B2159113 : Blo 1917435 2159113 := bbase (se 2 (by rfl) ⟨809667, by rfl⟩ : syracuseStep 2159113 = 1619335) (by norm_num)
theorem B2878817 : Blo 1917435 2878817 := bstep (se 2 (by rfl) ⟨1079556, by rfl⟩ : syracuseStep 2878817 = 2159113) B2159113
theorem B1919211 : Blo 1917435 1919211 := bstep (se 1 (by rfl) ⟨1439408, by rfl⟩ : syracuseStep 1919211 = 2878817) B2878817
theorem B3802621 : Blo 1917435 3802621 := bbase (se 3 (by rfl) ⟨712991, by rfl⟩ : syracuseStep 3802621 = 1425983) (by norm_num)
theorem B5070161 : Blo 1917435 5070161 := bstep (se 2 (by rfl) ⟨1901310, by rfl⟩ : syracuseStep 5070161 = 3802621) B3802621
theorem B13520429 : Blo 1917435 13520429 := bstep (se 3 (by rfl) ⟨2535080, by rfl⟩ : syracuseStep 13520429 = 5070161) B5070161
theorem B9013619 : Blo 1917435 9013619 := bstep (se 1 (by rfl) ⟨6760214, by rfl⟩ : syracuseStep 9013619 = 13520429) B13520429
theorem B24036317 : Blo 1917435 24036317 := bstep (se 3 (by rfl) ⟨4506809, by rfl⟩ : syracuseStep 24036317 = 9013619) B9013619
theorem B16024211 : Blo 1917435 16024211 := bstep (se 1 (by rfl) ⟨12018158, by rfl⟩ : syracuseStep 16024211 = 24036317) B24036317
theorem B10682807 : Blo 1917435 10682807 := bstep (se 1 (by rfl) ⟨8012105, by rfl⟩ : syracuseStep 10682807 = 16024211) B16024211
theorem B28487485 : Blo 1917435 28487485 := bstep (se 3 (by rfl) ⟨5341403, by rfl⟩ : syracuseStep 28487485 = 10682807) B10682807
theorem B37983313 : Blo 1917435 37983313 := bstep (se 2 (by rfl) ⟨14243742, by rfl⟩ : syracuseStep 37983313 = 28487485) B28487485
theorem B50644417 : Blo 1917435 50644417 := bstep (se 2 (by rfl) ⟨18991656, by rfl⟩ : syracuseStep 50644417 = 37983313) B37983313
theorem B67525889 : Blo 1917435 67525889 := bstep (se 2 (by rfl) ⟨25322208, by rfl⟩ : syracuseStep 67525889 = 50644417) B50644417
theorem B180069037 : Blo 1917435 180069037 := bstep (se 3 (by rfl) ⟨33762944, by rfl⟩ : syracuseStep 180069037 = 67525889) B67525889
theorem B960368197 : Blo 1917435 960368197 := bstep (se 4 (by rfl) ⟨90034518, by rfl⟩ : syracuseStep 960368197 = 180069037) B180069037
theorem B1280490929 : Blo 1917435 1280490929 := bstep (se 2 (by rfl) ⟨480184098, by rfl⟩ : syracuseStep 1280490929 = 960368197) B960368197
theorem B853660619 : Blo 1917435 853660619 := bstep (se 1 (by rfl) ⟨640245464, by rfl⟩ : syracuseStep 853660619 = 1280490929) B1280490929
theorem B569107079 : Blo 1917435 569107079 := bstep (se 1 (by rfl) ⟨426830309, by rfl⟩ : syracuseStep 569107079 = 853660619) B853660619
theorem B379404719 : Blo 1917435 379404719 := bstep (se 1 (by rfl) ⟨284553539, by rfl⟩ : syracuseStep 379404719 = 569107079) B569107079
theorem B252936479 : Blo 1917435 252936479 := bstep (se 1 (by rfl) ⟨189702359, by rfl⟩ : syracuseStep 252936479 = 379404719) B379404719
theorem B168624319 : Blo 1917435 168624319 := bstep (se 1 (by rfl) ⟨126468239, by rfl⟩ : syracuseStep 168624319 = 252936479) B252936479
theorem B224832425 : Blo 1917435 224832425 := bstep (se 2 (by rfl) ⟨84312159, by rfl⟩ : syracuseStep 224832425 = 168624319) B168624319
theorem B599553133 : Blo 1917435 599553133 := bstep (se 3 (by rfl) ⟨112416212, by rfl⟩ : syracuseStep 599553133 = 224832425) B224832425
theorem B3197616709 : Blo 1917435 3197616709 := bstep (se 4 (by rfl) ⟨299776566, by rfl⟩ : syracuseStep 3197616709 = 599553133) B599553133
theorem B4263488945 : Blo 1917435 4263488945 := bstep (se 2 (by rfl) ⟨1598808354, by rfl⟩ : syracuseStep 4263488945 = 3197616709) B3197616709
theorem B2842325963 : Blo 1917435 2842325963 := bstep (se 1 (by rfl) ⟨2131744472, by rfl⟩ : syracuseStep 2842325963 = 4263488945) B4263488945
theorem B1894883975 : Blo 1917435 1894883975 := bstep (se 1 (by rfl) ⟨1421162981, by rfl⟩ : syracuseStep 1894883975 = 2842325963) B2842325963
theorem B1263255983 : Blo 1917435 1263255983 := bstep (se 1 (by rfl) ⟨947441987, by rfl⟩ : syracuseStep 1263255983 = 1894883975) B1894883975
theorem B842170655 : Blo 1917435 842170655 := bstep (se 1 (by rfl) ⟨631627991, by rfl⟩ : syracuseStep 842170655 = 1263255983) B1263255983
theorem B2245788413 : Blo 1917435 2245788413 := bstep (se 3 (by rfl) ⟨421085327, by rfl⟩ : syracuseStep 2245788413 = 842170655) B842170655
theorem B1497192275 : Blo 1917435 1497192275 := bstep (se 1 (by rfl) ⟨1122894206, by rfl⟩ : syracuseStep 1497192275 = 2245788413) B2245788413
theorem B998128183 : Blo 1917435 998128183 := bstep (se 1 (by rfl) ⟨748596137, by rfl⟩ : syracuseStep 998128183 = 1497192275) B1497192275
theorem B1330837577 : Blo 1917435 1330837577 := bstep (se 2 (by rfl) ⟨499064091, by rfl⟩ : syracuseStep 1330837577 = 998128183) B998128183
theorem B887225051 : Blo 1917435 887225051 := bstep (se 1 (by rfl) ⟨665418788, by rfl⟩ : syracuseStep 887225051 = 1330837577) B1330837577
theorem B591483367 : Blo 1917435 591483367 := bstep (se 1 (by rfl) ⟨443612525, by rfl⟩ : syracuseStep 591483367 = 887225051) B887225051
theorem B3154577957 : Blo 1917435 3154577957 := bstep (se 4 (by rfl) ⟨295741683, by rfl⟩ : syracuseStep 3154577957 = 591483367) B591483367
theorem B2103051971 : Blo 1917435 2103051971 := bstep (se 1 (by rfl) ⟨1577288978, by rfl⟩ : syracuseStep 2103051971 = 3154577957) B3154577957
theorem B5608138589 : Blo 1917435 5608138589 := bstep (se 3 (by rfl) ⟨1051525985, by rfl⟩ : syracuseStep 5608138589 = 2103051971) B2103051971
theorem B3738759059 : Blo 1917435 3738759059 := bstep (se 1 (by rfl) ⟨2804069294, by rfl⟩ : syracuseStep 3738759059 = 5608138589) B5608138589
theorem B2492506039 : Blo 1917435 2492506039 := bstep (se 1 (by rfl) ⟨1869379529, by rfl⟩ : syracuseStep 2492506039 = 3738759059) B3738759059
theorem B3323341385 : Blo 1917435 3323341385 := bstep (se 2 (by rfl) ⟨1246253019, by rfl⟩ : syracuseStep 3323341385 = 2492506039) B2492506039
theorem B2215560923 : Blo 1917435 2215560923 := bstep (se 1 (by rfl) ⟨1661670692, by rfl⟩ : syracuseStep 2215560923 = 3323341385) B3323341385
theorem B1477040615 : Blo 1917435 1477040615 := bstep (se 1 (by rfl) ⟨1107780461, by rfl⟩ : syracuseStep 1477040615 = 2215560923) B2215560923
theorem B984693743 : Blo 1917435 984693743 := bstep (se 1 (by rfl) ⟨738520307, by rfl⟩ : syracuseStep 984693743 = 1477040615) B1477040615
theorem B656462495 : Blo 1917435 656462495 := bstep (se 1 (by rfl) ⟨492346871, by rfl⟩ : syracuseStep 656462495 = 984693743) B984693743
theorem B437641663 : Blo 1917435 437641663 := bstep (se 1 (by rfl) ⟨328231247, by rfl⟩ : syracuseStep 437641663 = 656462495) B656462495
theorem B583522217 : Blo 1917435 583522217 := bstep (se 2 (by rfl) ⟨218820831, by rfl⟩ : syracuseStep 583522217 = 437641663) B437641663
theorem B389014811 : Blo 1917435 389014811 := bstep (se 1 (by rfl) ⟨291761108, by rfl⟩ : syracuseStep 389014811 = 583522217) B583522217
theorem B259343207 : Blo 1917435 259343207 := bstep (se 1 (by rfl) ⟨194507405, by rfl⟩ : syracuseStep 259343207 = 389014811) B389014811
theorem B172895471 : Blo 1917435 172895471 := bstep (se 1 (by rfl) ⟨129671603, by rfl⟩ : syracuseStep 172895471 = 259343207) B259343207
theorem B115263647 : Blo 1917435 115263647 := bstep (se 1 (by rfl) ⟨86447735, by rfl⟩ : syracuseStep 115263647 = 172895471) B172895471
theorem B76842431 : Blo 1917435 76842431 := bstep (se 1 (by rfl) ⟨57631823, by rfl⟩ : syracuseStep 76842431 = 115263647) B115263647
theorem B51228287 : Blo 1917435 51228287 := bstep (se 1 (by rfl) ⟨38421215, by rfl⟩ : syracuseStep 51228287 = 76842431) B76842431
theorem B34152191 : Blo 1917435 34152191 := bstep (se 1 (by rfl) ⟨25614143, by rfl⟩ : syracuseStep 34152191 = 51228287) B51228287
theorem B22768127 : Blo 1917435 22768127 := bstep (se 1 (by rfl) ⟨17076095, by rfl⟩ : syracuseStep 22768127 = 34152191) B34152191
theorem B15178751 : Blo 1917435 15178751 := bstep (se 1 (by rfl) ⟨11384063, by rfl⟩ : syracuseStep 15178751 = 22768127) B22768127
theorem B10119167 : Blo 1917435 10119167 := bstep (se 1 (by rfl) ⟨7589375, by rfl⟩ : syracuseStep 10119167 = 15178751) B15178751
theorem B6746111 : Blo 1917435 6746111 := bstep (se 1 (by rfl) ⟨5059583, by rfl⟩ : syracuseStep 6746111 = 10119167) B10119167
theorem B4497407 : Blo 1917435 4497407 := bstep (se 1 (by rfl) ⟨3373055, by rfl⟩ : syracuseStep 4497407 = 6746111) B6746111
theorem B2998271 : Blo 1917435 2998271 := bstep (se 1 (by rfl) ⟨2248703, by rfl⟩ : syracuseStep 2998271 = 4497407) B4497407
theorem B1998847 : Blo 1917435 1998847 := bstep (se 1 (by rfl) ⟨1499135, by rfl⟩ : syracuseStep 1998847 = 2998271) B2998271
theorem B2665129 : Blo 1917435 2665129 := bstep (se 2 (by rfl) ⟨999423, by rfl⟩ : syracuseStep 2665129 = 1998847) B1998847
theorem B3553505 : Blo 1917435 3553505 := bstep (se 2 (by rfl) ⟨1332564, by rfl⟩ : syracuseStep 3553505 = 2665129) B2665129
theorem B2369003 : Blo 1917435 2369003 := bstep (se 1 (by rfl) ⟨1776752, by rfl⟩ : syracuseStep 2369003 = 3553505) B3553505
theorem B25269365 : Blo 1917435 25269365 := bstep (se 5 (by rfl) ⟨1184501, by rfl⟩ : syracuseStep 25269365 = 2369003) B2369003
theorem B67384973 : Blo 1917435 67384973 := bstep (se 3 (by rfl) ⟨12634682, by rfl⟩ : syracuseStep 67384973 = 25269365) B25269365
theorem B179693261 : Blo 1917435 179693261 := bstep (se 3 (by rfl) ⟨33692486, by rfl⟩ : syracuseStep 179693261 = 67384973) B67384973
theorem B119795507 : Blo 1917435 119795507 := bstep (se 1 (by rfl) ⟨89846630, by rfl⟩ : syracuseStep 119795507 = 179693261) B179693261
theorem B79863671 : Blo 1917435 79863671 := bstep (se 1 (by rfl) ⟨59897753, by rfl⟩ : syracuseStep 79863671 = 119795507) B119795507
theorem B53242447 : Blo 1917435 53242447 := bstep (se 1 (by rfl) ⟨39931835, by rfl⟩ : syracuseStep 53242447 = 79863671) B79863671
theorem B70989929 : Blo 1917435 70989929 := bstep (se 2 (by rfl) ⟨26621223, by rfl⟩ : syracuseStep 70989929 = 53242447) B53242447
theorem B47326619 : Blo 1917435 47326619 := bstep (se 1 (by rfl) ⟨35494964, by rfl⟩ : syracuseStep 47326619 = 70989929) B70989929
theorem B31551079 : Blo 1917435 31551079 := bstep (se 1 (by rfl) ⟨23663309, by rfl⟩ : syracuseStep 31551079 = 47326619) B47326619
theorem B42068105 : Blo 1917435 42068105 := bstep (se 2 (by rfl) ⟨15775539, by rfl⟩ : syracuseStep 42068105 = 31551079) B31551079
theorem B28045403 : Blo 1917435 28045403 := bstep (se 1 (by rfl) ⟨21034052, by rfl⟩ : syracuseStep 28045403 = 42068105) B42068105
theorem B18696935 : Blo 1917435 18696935 := bstep (se 1 (by rfl) ⟨14022701, by rfl⟩ : syracuseStep 18696935 = 28045403) B28045403
theorem B12464623 : Blo 1917435 12464623 := bstep (se 1 (by rfl) ⟨9348467, by rfl⟩ : syracuseStep 12464623 = 18696935) B18696935
theorem B66477989 : Blo 1917435 66477989 := bstep (se 4 (by rfl) ⟨6232311, by rfl⟩ : syracuseStep 66477989 = 12464623) B12464623
theorem B44318659 : Blo 1917435 44318659 := bstep (se 1 (by rfl) ⟨33238994, by rfl⟩ : syracuseStep 44318659 = 66477989) B66477989
theorem B59091545 : Blo 1917435 59091545 := bstep (se 2 (by rfl) ⟨22159329, by rfl⟩ : syracuseStep 59091545 = 44318659) B44318659
theorem B39394363 : Blo 1917435 39394363 := bstep (se 1 (by rfl) ⟨29545772, by rfl⟩ : syracuseStep 39394363 = 59091545) B59091545
theorem B52525817 : Blo 1917435 52525817 := bstep (se 2 (by rfl) ⟨19697181, by rfl⟩ : syracuseStep 52525817 = 39394363) B39394363
theorem B35017211 : Blo 1917435 35017211 := bstep (se 1 (by rfl) ⟨26262908, by rfl⟩ : syracuseStep 35017211 = 52525817) B52525817
theorem B93379229 : Blo 1917435 93379229 := bstep (se 3 (by rfl) ⟨17508605, by rfl⟩ : syracuseStep 93379229 = 35017211) B35017211
theorem B62252819 : Blo 1917435 62252819 := bstep (se 1 (by rfl) ⟨46689614, by rfl⟩ : syracuseStep 62252819 = 93379229) B93379229
theorem B41501879 : Blo 1917435 41501879 := bstep (se 1 (by rfl) ⟨31126409, by rfl⟩ : syracuseStep 41501879 = 62252819) B62252819
theorem B27667919 : Blo 1917435 27667919 := bstep (se 1 (by rfl) ⟨20750939, by rfl⟩ : syracuseStep 27667919 = 41501879) B41501879
theorem B18445279 : Blo 1917435 18445279 := bstep (se 1 (by rfl) ⟨13833959, by rfl⟩ : syracuseStep 18445279 = 27667919) B27667919
theorem B24593705 : Blo 1917435 24593705 := bstep (se 2 (by rfl) ⟨9222639, by rfl⟩ : syracuseStep 24593705 = 18445279) B18445279
theorem B16395803 : Blo 1917435 16395803 := bstep (se 1 (by rfl) ⟨12296852, by rfl⟩ : syracuseStep 16395803 = 24593705) B24593705
theorem B10930535 : Blo 1917435 10930535 := bstep (se 1 (by rfl) ⟨8197901, by rfl⟩ : syracuseStep 10930535 = 16395803) B16395803
theorem B7287023 : Blo 1917435 7287023 := bstep (se 1 (by rfl) ⟨5465267, by rfl⟩ : syracuseStep 7287023 = 10930535) B10930535
theorem B4858015 : Blo 1917435 4858015 := bstep (se 1 (by rfl) ⟨3643511, by rfl⟩ : syracuseStep 4858015 = 7287023) B7287023
theorem B6477353 : Blo 1917435 6477353 := bstep (se 2 (by rfl) ⟨2429007, by rfl⟩ : syracuseStep 6477353 = 4858015) B4858015
theorem B4318235 : Blo 1917435 4318235 := bstep (se 1 (by rfl) ⟨3238676, by rfl⟩ : syracuseStep 4318235 = 6477353) B6477353
theorem B2878823 : Blo 1917435 2878823 := bstep (se 1 (by rfl) ⟨2159117, by rfl⟩ : syracuseStep 2878823 = 4318235) B4318235
theorem B1919215 : Blo 1917435 1919215 := bstep (se 1 (by rfl) ⟨1439411, by rfl⟩ : syracuseStep 1919215 = 2878823) B2878823
theorem B2878829 : Blo 1917435 2878829 := bbase (se 3 (by rfl) ⟨539780, by rfl⟩ : syracuseStep 2878829 = 1079561) (by norm_num)
theorem B1919219 : Blo 1917435 1919219 := bstep (se 1 (by rfl) ⟨1439414, by rfl⟩ : syracuseStep 1919219 = 2878829) B2878829
theorem B4318253 : Blo 1917435 4318253 := bbase (se 3 (by rfl) ⟨809672, by rfl⟩ : syracuseStep 4318253 = 1619345) (by norm_num)
theorem B2878835 : Blo 1917435 2878835 := bstep (se 1 (by rfl) ⟨2159126, by rfl⟩ : syracuseStep 2878835 = 4318253) B4318253
theorem B1919223 : Blo 1917435 1919223 := bstep (se 1 (by rfl) ⟨1439417, by rfl⟩ : syracuseStep 1919223 = 2878835) B2878835
theorem B2593885 : Blo 1917435 2593885 := bbase (se 3 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 2593885 = 972707) (by norm_num)
theorem B3458513 : Blo 1917435 3458513 := bstep (se 2 (by rfl) ⟨1296942, by rfl⟩ : syracuseStep 3458513 = 2593885) B2593885
theorem B2305675 : Blo 1917435 2305675 := bstep (se 1 (by rfl) ⟨1729256, by rfl⟩ : syracuseStep 2305675 = 3458513) B3458513
theorem B12296933 : Blo 1917435 12296933 := bstep (se 4 (by rfl) ⟨1152837, by rfl⟩ : syracuseStep 12296933 = 2305675) B2305675
theorem B8197955 : Blo 1917435 8197955 := bstep (se 1 (by rfl) ⟨6148466, by rfl⟩ : syracuseStep 8197955 = 12296933) B12296933
theorem B5465303 : Blo 1917435 5465303 := bstep (se 1 (by rfl) ⟨4098977, by rfl⟩ : syracuseStep 5465303 = 8197955) B8197955
theorem B3643535 : Blo 1917435 3643535 := bstep (se 1 (by rfl) ⟨2732651, by rfl⟩ : syracuseStep 3643535 = 5465303) B5465303
theorem B2429023 : Blo 1917435 2429023 := bstep (se 1 (by rfl) ⟨1821767, by rfl⟩ : syracuseStep 2429023 = 3643535) B3643535
theorem B3238697 : Blo 1917435 3238697 := bstep (se 2 (by rfl) ⟨1214511, by rfl⟩ : syracuseStep 3238697 = 2429023) B2429023
theorem B2159131 : Blo 1917435 2159131 := bstep (se 1 (by rfl) ⟨1619348, by rfl⟩ : syracuseStep 2159131 = 3238697) B3238697
theorem B2878841 : Blo 1917435 2878841 := bstep (se 2 (by rfl) ⟨1079565, by rfl⟩ : syracuseStep 2878841 = 2159131) B2159131
theorem B1919227 : Blo 1917435 1919227 := bstep (se 1 (by rfl) ⟨1439420, by rfl⟩ : syracuseStep 1919227 = 2878841) B2878841
theorem B7781669 : Blo 1917435 7781669 := bbase (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) (by norm_num)
theorem B5187779 : Blo 1917435 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B3458519 : Blo 1917435 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B2305679 : Blo 1917435 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B6148477 : Blo 1917435 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B32791877 : Blo 1917435 32791877 := bstep (se 4 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 32791877 = 6148477) B6148477
theorem B21861251 : Blo 1917435 21861251 := bstep (se 1 (by rfl) ⟨16395938, by rfl⟩ : syracuseStep 21861251 = 32791877) B32791877
theorem B14574167 : Blo 1917435 14574167 := bstep (se 1 (by rfl) ⟨10930625, by rfl⟩ : syracuseStep 14574167 = 21861251) B21861251
theorem B9716111 : Blo 1917435 9716111 := bstep (se 1 (by rfl) ⟨7287083, by rfl⟩ : syracuseStep 9716111 = 14574167) B14574167
theorem B6477407 : Blo 1917435 6477407 := bstep (se 1 (by rfl) ⟨4858055, by rfl⟩ : syracuseStep 6477407 = 9716111) B9716111
theorem B4318271 : Blo 1917435 4318271 := bstep (se 1 (by rfl) ⟨3238703, by rfl⟩ : syracuseStep 4318271 = 6477407) B6477407
theorem B2878847 : Blo 1917435 2878847 := bstep (se 1 (by rfl) ⟨2159135, by rfl⟩ : syracuseStep 2878847 = 4318271) B4318271
theorem B1919231 : Blo 1917435 1919231 := bstep (se 1 (by rfl) ⟨1439423, by rfl⟩ : syracuseStep 1919231 = 2878847) B2878847
theorem B2878853 : Blo 1917435 2878853 := bbase (se 4 (by rfl) ⟨269892, by rfl⟩ : syracuseStep 2878853 = 539785) (by norm_num)
theorem B1919235 : Blo 1917435 1919235 := bstep (se 1 (by rfl) ⟨1439426, by rfl⟩ : syracuseStep 1919235 = 2878853) B2878853
theorem B3238717 : Blo 1917435 3238717 := bbase (se 3 (by rfl) ⟨607259, by rfl⟩ : syracuseStep 3238717 = 1214519) (by norm_num)
theorem B4318289 : Blo 1917435 4318289 := bstep (se 2 (by rfl) ⟨1619358, by rfl⟩ : syracuseStep 4318289 = 3238717) B3238717
theorem B2878859 : Blo 1917435 2878859 := bstep (se 1 (by rfl) ⟨2159144, by rfl⟩ : syracuseStep 2878859 = 4318289) B4318289
theorem B1919239 : Blo 1917435 1919239 := bstep (se 1 (by rfl) ⟨1439429, by rfl⟩ : syracuseStep 1919239 = 2878859) B2878859
theorem B2159149 : Blo 1917435 2159149 := bbase (se 3 (by rfl) ⟨404840, by rfl⟩ : syracuseStep 2159149 = 809681) (by norm_num)
theorem B2878865 : Blo 1917435 2878865 := bstep (se 2 (by rfl) ⟨1079574, by rfl⟩ : syracuseStep 2878865 = 2159149) B2159149
theorem B1919243 : Blo 1917435 1919243 := bstep (se 1 (by rfl) ⟨1439432, by rfl⟩ : syracuseStep 1919243 = 2878865) B2878865
theorem B6477461 : Blo 1917435 6477461 := bbase (se 6 (by rfl) ⟨151815, by rfl⟩ : syracuseStep 6477461 = 303631) (by norm_num)
theorem B4318307 : Blo 1917435 4318307 := bstep (se 1 (by rfl) ⟨3238730, by rfl⟩ : syracuseStep 4318307 = 6477461) B6477461
theorem B2878871 : Blo 1917435 2878871 := bstep (se 1 (by rfl) ⟨2159153, by rfl⟩ : syracuseStep 2878871 = 4318307) B4318307
theorem B1919247 : Blo 1917435 1919247 := bstep (se 1 (by rfl) ⟨1439435, by rfl⟩ : syracuseStep 1919247 = 2878871) B2878871
theorem B2878877 : Blo 1917435 2878877 := bbase (se 3 (by rfl) ⟨539789, by rfl⟩ : syracuseStep 2878877 = 1079579) (by norm_num)
theorem B1919251 : Blo 1917435 1919251 := bstep (se 1 (by rfl) ⟨1439438, by rfl⟩ : syracuseStep 1919251 = 2878877) B2878877
theorem B4318325 : Blo 1917435 4318325 := bbase (se 5 (by rfl) ⟨202421, by rfl⟩ : syracuseStep 4318325 = 404843) (by norm_num)
theorem B2878883 : Blo 1917435 2878883 := bstep (se 1 (by rfl) ⟨2159162, by rfl⟩ : syracuseStep 2878883 = 4318325) B4318325
theorem B1919255 : Blo 1917435 1919255 := bstep (se 1 (by rfl) ⟨1439441, by rfl⟩ : syracuseStep 1919255 = 2878883) B2878883
theorem B16396181 : Blo 1917435 16396181 := bbase (se 6 (by rfl) ⟨384285, by rfl⟩ : syracuseStep 16396181 = 768571) (by norm_num)
theorem B10930787 : Blo 1917435 10930787 := bstep (se 1 (by rfl) ⟨8198090, by rfl⟩ : syracuseStep 10930787 = 16396181) B16396181
theorem B7287191 : Blo 1917435 7287191 := bstep (se 1 (by rfl) ⟨5465393, by rfl⟩ : syracuseStep 7287191 = 10930787) B10930787
theorem B4858127 : Blo 1917435 4858127 := bstep (se 1 (by rfl) ⟨3643595, by rfl⟩ : syracuseStep 4858127 = 7287191) B7287191
theorem B3238751 : Blo 1917435 3238751 := bstep (se 1 (by rfl) ⟨2429063, by rfl⟩ : syracuseStep 3238751 = 4858127) B4858127
theorem B2159167 : Blo 1917435 2159167 := bstep (se 1 (by rfl) ⟨1619375, by rfl⟩ : syracuseStep 2159167 = 3238751) B3238751
theorem B2878889 : Blo 1917435 2878889 := bstep (se 2 (by rfl) ⟨1079583, by rfl⟩ : syracuseStep 2878889 = 2159167) B2159167
theorem B1919259 : Blo 1917435 1919259 := bstep (se 1 (by rfl) ⟨1439444, by rfl⟩ : syracuseStep 1919259 = 2878889) B2878889
theorem B7287205 : Blo 1917435 7287205 := bbase (se 4 (by rfl) ⟨683175, by rfl⟩ : syracuseStep 7287205 = 1366351) (by norm_num)
theorem B9716273 : Blo 1917435 9716273 := bstep (se 2 (by rfl) ⟨3643602, by rfl⟩ : syracuseStep 9716273 = 7287205) B7287205
theorem B6477515 : Blo 1917435 6477515 := bstep (se 1 (by rfl) ⟨4858136, by rfl⟩ : syracuseStep 6477515 = 9716273) B9716273
theorem B4318343 : Blo 1917435 4318343 := bstep (se 1 (by rfl) ⟨3238757, by rfl⟩ : syracuseStep 4318343 = 6477515) B6477515
theorem B2878895 : Blo 1917435 2878895 := bstep (se 1 (by rfl) ⟨2159171, by rfl⟩ : syracuseStep 2878895 = 4318343) B4318343
theorem B1919263 : Blo 1917435 1919263 := bstep (se 1 (by rfl) ⟨1439447, by rfl⟩ : syracuseStep 1919263 = 2878895) B2878895
theorem B2878901 : Blo 1917435 2878901 := bbase (se 5 (by rfl) ⟨134948, by rfl⟩ : syracuseStep 2878901 = 269897) (by norm_num)
theorem B1919267 : Blo 1917435 1919267 := bstep (se 1 (by rfl) ⟨1439450, by rfl⟩ : syracuseStep 1919267 = 2878901) B2878901
theorem B4858157 : Blo 1917435 4858157 := bbase (se 3 (by rfl) ⟨910904, by rfl⟩ : syracuseStep 4858157 = 1821809) (by norm_num)
theorem B3238771 : Blo 1917435 3238771 := bstep (se 1 (by rfl) ⟨2429078, by rfl⟩ : syracuseStep 3238771 = 4858157) B4858157
theorem B4318361 : Blo 1917435 4318361 := bstep (se 2 (by rfl) ⟨1619385, by rfl⟩ : syracuseStep 4318361 = 3238771) B3238771
theorem B2878907 : Blo 1917435 2878907 := bstep (se 1 (by rfl) ⟨2159180, by rfl⟩ : syracuseStep 2878907 = 4318361) B4318361
theorem B1919271 : Blo 1917435 1919271 := bstep (se 1 (by rfl) ⟨1439453, by rfl⟩ : syracuseStep 1919271 = 2878907) B2878907
theorem B2159185 : Blo 1917435 2159185 := bbase (se 2 (by rfl) ⟨809694, by rfl⟩ : syracuseStep 2159185 = 1619389) (by norm_num)
theorem B2878913 : Blo 1917435 2878913 := bstep (se 2 (by rfl) ⟨1079592, by rfl⟩ : syracuseStep 2878913 = 2159185) B2159185
theorem B1919275 : Blo 1917435 1919275 := bstep (se 1 (by rfl) ⟨1439456, by rfl⟩ : syracuseStep 1919275 = 2878913) B2878913
theorem B2732725 : Blo 1917435 2732725 := bbase (se 5 (by rfl) ⟨128096, by rfl⟩ : syracuseStep 2732725 = 256193) (by norm_num)
theorem B3643633 : Blo 1917435 3643633 := bstep (se 2 (by rfl) ⟨1366362, by rfl⟩ : syracuseStep 3643633 = 2732725) B2732725
theorem B4858177 : Blo 1917435 4858177 := bstep (se 2 (by rfl) ⟨1821816, by rfl⟩ : syracuseStep 4858177 = 3643633) B3643633
theorem B6477569 : Blo 1917435 6477569 := bstep (se 2 (by rfl) ⟨2429088, by rfl⟩ : syracuseStep 6477569 = 4858177) B4858177
theorem B4318379 : Blo 1917435 4318379 := bstep (se 1 (by rfl) ⟨3238784, by rfl⟩ : syracuseStep 4318379 = 6477569) B6477569
theorem B2878919 : Blo 1917435 2878919 := bstep (se 1 (by rfl) ⟨2159189, by rfl⟩ : syracuseStep 2878919 = 4318379) B4318379
theorem B1919279 : Blo 1917435 1919279 := bstep (se 1 (by rfl) ⟨1439459, by rfl⟩ : syracuseStep 1919279 = 2878919) B2878919
theorem B2878925 : Blo 1917435 2878925 := bbase (se 3 (by rfl) ⟨539798, by rfl⟩ : syracuseStep 2878925 = 1079597) (by norm_num)
theorem B1919283 : Blo 1917435 1919283 := bstep (se 1 (by rfl) ⟨1439462, by rfl⟩ : syracuseStep 1919283 = 2878925) B2878925
theorem B4318397 : Blo 1917435 4318397 := bbase (se 3 (by rfl) ⟨809699, by rfl⟩ : syracuseStep 4318397 = 1619399) (by norm_num)
theorem B2878931 : Blo 1917435 2878931 := bstep (se 1 (by rfl) ⟨2159198, by rfl⟩ : syracuseStep 2878931 = 4318397) B4318397
theorem B1919287 : Blo 1917435 1919287 := bstep (se 1 (by rfl) ⟨1439465, by rfl⟩ : syracuseStep 1919287 = 2878931) B2878931
theorem B3238805 : Blo 1917435 3238805 := bbase (se 6 (by rfl) ⟨75909, by rfl⟩ : syracuseStep 3238805 = 151819) (by norm_num)
theorem B2159203 : Blo 1917435 2159203 := bstep (se 1 (by rfl) ⟨1619402, by rfl⟩ : syracuseStep 2159203 = 3238805) B3238805
theorem B2878937 : Blo 1917435 2878937 := bstep (se 2 (by rfl) ⟨1079601, by rfl⟩ : syracuseStep 2878937 = 2159203) B2159203
theorem B1919291 : Blo 1917435 1919291 := bstep (se 1 (by rfl) ⟨1439468, by rfl⟩ : syracuseStep 1919291 = 2878937) B2878937
theorem B12297365 : Blo 1917435 12297365 := bbase (se 6 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 12297365 = 576439) (by norm_num)
theorem B8198243 : Blo 1917435 8198243 := bstep (se 1 (by rfl) ⟨6148682, by rfl⟩ : syracuseStep 8198243 = 12297365) B12297365
theorem B5465495 : Blo 1917435 5465495 := bstep (se 1 (by rfl) ⟨4099121, by rfl⟩ : syracuseStep 5465495 = 8198243) B8198243
theorem B14574653 : Blo 1917435 14574653 := bstep (se 3 (by rfl) ⟨2732747, by rfl⟩ : syracuseStep 14574653 = 5465495) B5465495
theorem B9716435 : Blo 1917435 9716435 := bstep (se 1 (by rfl) ⟨7287326, by rfl⟩ : syracuseStep 9716435 = 14574653) B14574653
theorem B6477623 : Blo 1917435 6477623 := bstep (se 1 (by rfl) ⟨4858217, by rfl⟩ : syracuseStep 6477623 = 9716435) B9716435
theorem B4318415 : Blo 1917435 4318415 := bstep (se 1 (by rfl) ⟨3238811, by rfl⟩ : syracuseStep 4318415 = 6477623) B6477623
theorem B2878943 : Blo 1917435 2878943 := bstep (se 1 (by rfl) ⟨2159207, by rfl⟩ : syracuseStep 2878943 = 4318415) B4318415
theorem B1919295 : Blo 1917435 1919295 := bstep (se 1 (by rfl) ⟨1439471, by rfl⟩ : syracuseStep 1919295 = 2878943) B2878943
theorem B2878949 : Blo 1917435 2878949 := bbase (se 4 (by rfl) ⟨269901, by rfl⟩ : syracuseStep 2878949 = 539803) (by norm_num)
theorem B1919299 : Blo 1917435 1919299 := bstep (se 1 (by rfl) ⟨1439474, by rfl⟩ : syracuseStep 1919299 = 2878949) B2878949
theorem B3890981 : Blo 1917435 3890981 := bbase (se 4 (by rfl) ⟨364779, by rfl⟩ : syracuseStep 3890981 = 729559) (by norm_num)
theorem B2593987 : Blo 1917435 2593987 := bstep (se 1 (by rfl) ⟨1945490, by rfl⟩ : syracuseStep 2593987 = 3890981) B3890981
theorem B13834597 : Blo 1917435 13834597 := bstep (se 4 (by rfl) ⟨1296993, by rfl⟩ : syracuseStep 13834597 = 2593987) B2593987
theorem B18446129 : Blo 1917435 18446129 := bstep (se 2 (by rfl) ⟨6917298, by rfl⟩ : syracuseStep 18446129 = 13834597) B13834597
theorem B12297419 : Blo 1917435 12297419 := bstep (se 1 (by rfl) ⟨9223064, by rfl⟩ : syracuseStep 12297419 = 18446129) B18446129
theorem B8198279 : Blo 1917435 8198279 := bstep (se 1 (by rfl) ⟨6148709, by rfl⟩ : syracuseStep 8198279 = 12297419) B12297419
theorem B5465519 : Blo 1917435 5465519 := bstep (se 1 (by rfl) ⟨4099139, by rfl⟩ : syracuseStep 5465519 = 8198279) B8198279
theorem B3643679 : Blo 1917435 3643679 := bstep (se 1 (by rfl) ⟨2732759, by rfl⟩ : syracuseStep 3643679 = 5465519) B5465519
theorem B2429119 : Blo 1917435 2429119 := bstep (se 1 (by rfl) ⟨1821839, by rfl⟩ : syracuseStep 2429119 = 3643679) B3643679
theorem B3238825 : Blo 1917435 3238825 := bstep (se 2 (by rfl) ⟨1214559, by rfl⟩ : syracuseStep 3238825 = 2429119) B2429119
theorem B4318433 : Blo 1917435 4318433 := bstep (se 2 (by rfl) ⟨1619412, by rfl⟩ : syracuseStep 4318433 = 3238825) B3238825
theorem B2878955 : Blo 1917435 2878955 := bstep (se 1 (by rfl) ⟨2159216, by rfl⟩ : syracuseStep 2878955 = 4318433) B4318433
theorem B1919303 : Blo 1917435 1919303 := bstep (se 1 (by rfl) ⟨1439477, by rfl⟩ : syracuseStep 1919303 = 2878955) B2878955
theorem B2159221 : Blo 1917435 2159221 := bbase (se 5 (by rfl) ⟨101213, by rfl⟩ : syracuseStep 2159221 = 202427) (by norm_num)
theorem B2878961 : Blo 1917435 2878961 := bstep (se 2 (by rfl) ⟨1079610, by rfl⟩ : syracuseStep 2878961 = 2159221) B2159221
theorem B1919307 : Blo 1917435 1919307 := bstep (se 1 (by rfl) ⟨1439480, by rfl⟩ : syracuseStep 1919307 = 2878961) B2878961
theorem B2429129 : Blo 1917435 2429129 := bbase (se 2 (by rfl) ⟨910923, by rfl⟩ : syracuseStep 2429129 = 1821847) (by norm_num)
theorem B6477677 : Blo 1917435 6477677 := bstep (se 3 (by rfl) ⟨1214564, by rfl⟩ : syracuseStep 6477677 = 2429129) B2429129
theorem B4318451 : Blo 1917435 4318451 := bstep (se 1 (by rfl) ⟨3238838, by rfl⟩ : syracuseStep 4318451 = 6477677) B6477677
theorem B2878967 : Blo 1917435 2878967 := bstep (se 1 (by rfl) ⟨2159225, by rfl⟩ : syracuseStep 2878967 = 4318451) B4318451
theorem B1919311 : Blo 1917435 1919311 := bstep (se 1 (by rfl) ⟨1439483, by rfl⟩ : syracuseStep 1919311 = 2878967) B2878967
theorem B2878973 : Blo 1917435 2878973 := bbase (se 3 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 2878973 = 1079615) (by norm_num)
theorem B1919315 : Blo 1917435 1919315 := bstep (se 1 (by rfl) ⟨1439486, by rfl⟩ : syracuseStep 1919315 = 2878973) B2878973
theorem B4318469 : Blo 1917435 4318469 := bbase (se 4 (by rfl) ⟨404856, by rfl⟩ : syracuseStep 4318469 = 809713) (by norm_num)
theorem B2878979 : Blo 1917435 2878979 := bstep (se 1 (by rfl) ⟨2159234, by rfl⟩ : syracuseStep 2878979 = 4318469) B4318469
theorem B1919319 : Blo 1917435 1919319 := bstep (se 1 (by rfl) ⟨1439489, by rfl⟩ : syracuseStep 1919319 = 2878979) B2878979
theorem B3643717 : Blo 1917435 3643717 := bbase (se 4 (by rfl) ⟨341598, by rfl⟩ : syracuseStep 3643717 = 683197) (by norm_num)
theorem B4858289 : Blo 1917435 4858289 := bstep (se 2 (by rfl) ⟨1821858, by rfl⟩ : syracuseStep 4858289 = 3643717) B3643717
theorem B3238859 : Blo 1917435 3238859 := bstep (se 1 (by rfl) ⟨2429144, by rfl⟩ : syracuseStep 3238859 = 4858289) B4858289
theorem B2159239 : Blo 1917435 2159239 := bstep (se 1 (by rfl) ⟨1619429, by rfl⟩ : syracuseStep 2159239 = 3238859) B3238859
theorem B2878985 : Blo 1917435 2878985 := bstep (se 2 (by rfl) ⟨1079619, by rfl⟩ : syracuseStep 2878985 = 2159239) B2159239
theorem B1919323 : Blo 1917435 1919323 := bstep (se 1 (by rfl) ⟨1439492, by rfl⟩ : syracuseStep 1919323 = 2878985) B2878985
theorem B9716597 : Blo 1917435 9716597 := bbase (se 5 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 9716597 = 910931) (by norm_num)
theorem B6477731 : Blo 1917435 6477731 := bstep (se 1 (by rfl) ⟨4858298, by rfl⟩ : syracuseStep 6477731 = 9716597) B9716597
theorem B4318487 : Blo 1917435 4318487 := bstep (se 1 (by rfl) ⟨3238865, by rfl⟩ : syracuseStep 4318487 = 6477731) B6477731
theorem B2878991 : Blo 1917435 2878991 := bstep (se 1 (by rfl) ⟨2159243, by rfl⟩ : syracuseStep 2878991 = 4318487) B4318487
theorem B1919327 : Blo 1917435 1919327 := bstep (se 1 (by rfl) ⟨1439495, by rfl⟩ : syracuseStep 1919327 = 2878991) B2878991
theorem B2878997 : Blo 1917435 2878997 := bbase (se 6 (by rfl) ⟨67476, by rfl⟩ : syracuseStep 2878997 = 134953) (by norm_num)
theorem B1919331 : Blo 1917435 1919331 := bstep (se 1 (by rfl) ⟨1439498, by rfl⟩ : syracuseStep 1919331 = 2878997) B2878997
theorem B6917413 : Blo 1917435 6917413 := bbase (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) (by norm_num)
theorem B9223217 : Blo 1917435 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B6148811 : Blo 1917435 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B16396829 : Blo 1917435 16396829 := bstep (se 3 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 16396829 = 6148811) B6148811
theorem B10931219 : Blo 1917435 10931219 := bstep (se 1 (by rfl) ⟨8198414, by rfl⟩ : syracuseStep 10931219 = 16396829) B16396829
theorem B7287479 : Blo 1917435 7287479 := bstep (se 1 (by rfl) ⟨5465609, by rfl⟩ : syracuseStep 7287479 = 10931219) B10931219
theorem B4858319 : Blo 1917435 4858319 := bstep (se 1 (by rfl) ⟨3643739, by rfl⟩ : syracuseStep 4858319 = 7287479) B7287479
theorem B3238879 : Blo 1917435 3238879 := bstep (se 1 (by rfl) ⟨2429159, by rfl⟩ : syracuseStep 3238879 = 4858319) B4858319
theorem B4318505 : Blo 1917435 4318505 := bstep (se 2 (by rfl) ⟨1619439, by rfl⟩ : syracuseStep 4318505 = 3238879) B3238879
theorem B2879003 : Blo 1917435 2879003 := bstep (se 1 (by rfl) ⟨2159252, by rfl⟩ : syracuseStep 2879003 = 4318505) B4318505
theorem B1919335 : Blo 1917435 1919335 := bstep (se 1 (by rfl) ⟨1439501, by rfl⟩ : syracuseStep 1919335 = 2879003) B2879003
theorem B2159257 : Blo 1917435 2159257 := bbase (se 2 (by rfl) ⟨809721, by rfl⟩ : syracuseStep 2159257 = 1619443) (by norm_num)
theorem B2879009 : Blo 1917435 2879009 := bstep (se 2 (by rfl) ⟨1079628, by rfl⟩ : syracuseStep 2879009 = 2159257) B2159257
theorem B1919339 : Blo 1917435 1919339 := bstep (se 1 (by rfl) ⟨1439504, by rfl⟩ : syracuseStep 1919339 = 2879009) B2879009
theorem B7287509 : Blo 1917435 7287509 := bbase (se 7 (by rfl) ⟨85400, by rfl⟩ : syracuseStep 7287509 = 170801) (by norm_num)
theorem B4858339 : Blo 1917435 4858339 := bstep (se 1 (by rfl) ⟨3643754, by rfl⟩ : syracuseStep 4858339 = 7287509) B7287509
theorem B6477785 : Blo 1917435 6477785 := bstep (se 2 (by rfl) ⟨2429169, by rfl⟩ : syracuseStep 6477785 = 4858339) B4858339
theorem B4318523 : Blo 1917435 4318523 := bstep (se 1 (by rfl) ⟨3238892, by rfl⟩ : syracuseStep 4318523 = 6477785) B6477785
theorem B2879015 : Blo 1917435 2879015 := bstep (se 1 (by rfl) ⟨2159261, by rfl⟩ : syracuseStep 2879015 = 4318523) B4318523
theorem B1919343 : Blo 1917435 1919343 := bstep (se 1 (by rfl) ⟨1439507, by rfl⟩ : syracuseStep 1919343 = 2879015) B2879015
theorem B2879021 : Blo 1917435 2879021 := bbase (se 3 (by rfl) ⟨539816, by rfl⟩ : syracuseStep 2879021 = 1079633) (by norm_num)
theorem B1919347 : Blo 1917435 1919347 := bstep (se 1 (by rfl) ⟨1439510, by rfl⟩ : syracuseStep 1919347 = 2879021) B2879021
theorem B4318541 : Blo 1917435 4318541 := bbase (se 3 (by rfl) ⟨809726, by rfl⟩ : syracuseStep 4318541 = 1619453) (by norm_num)
theorem B2879027 : Blo 1917435 2879027 := bstep (se 1 (by rfl) ⟨2159270, by rfl⟩ : syracuseStep 2879027 = 4318541) B4318541
theorem B1919351 : Blo 1917435 1919351 := bstep (se 1 (by rfl) ⟨1439513, by rfl⟩ : syracuseStep 1919351 = 2879027) B2879027
theorem B2429185 : Blo 1917435 2429185 := bbase (se 2 (by rfl) ⟨910944, by rfl⟩ : syracuseStep 2429185 = 1821889) (by norm_num)
theorem B3238913 : Blo 1917435 3238913 := bstep (se 2 (by rfl) ⟨1214592, by rfl⟩ : syracuseStep 3238913 = 2429185) B2429185
theorem B2159275 : Blo 1917435 2159275 := bstep (se 1 (by rfl) ⟨1619456, by rfl⟩ : syracuseStep 2159275 = 3238913) B3238913
theorem B2879033 : Blo 1917435 2879033 := bstep (se 2 (by rfl) ⟨1079637, by rfl⟩ : syracuseStep 2879033 = 2159275) B2159275
theorem B1919355 : Blo 1917435 1919355 := bstep (se 1 (by rfl) ⟨1439516, by rfl⟩ : syracuseStep 1919355 = 2879033) B2879033
theorem B2049629 : Blo 1917435 2049629 := bbase (se 3 (by rfl) ⟨384305, by rfl⟩ : syracuseStep 2049629 = 768611) (by norm_num)
theorem B21862709 : Blo 1917435 21862709 := bstep (se 5 (by rfl) ⟨1024814, by rfl⟩ : syracuseStep 21862709 = 2049629) B2049629
theorem B14575139 : Blo 1917435 14575139 := bstep (se 1 (by rfl) ⟨10931354, by rfl⟩ : syracuseStep 14575139 = 21862709) B21862709
theorem B9716759 : Blo 1917435 9716759 := bstep (se 1 (by rfl) ⟨7287569, by rfl⟩ : syracuseStep 9716759 = 14575139) B14575139
theorem B6477839 : Blo 1917435 6477839 := bstep (se 1 (by rfl) ⟨4858379, by rfl⟩ : syracuseStep 6477839 = 9716759) B9716759
theorem B4318559 : Blo 1917435 4318559 := bstep (se 1 (by rfl) ⟨3238919, by rfl⟩ : syracuseStep 4318559 = 6477839) B6477839
theorem B2879039 : Blo 1917435 2879039 := bstep (se 1 (by rfl) ⟨2159279, by rfl⟩ : syracuseStep 2879039 = 4318559) B4318559
theorem B1919359 : Blo 1917435 1919359 := bstep (se 1 (by rfl) ⟨1439519, by rfl⟩ : syracuseStep 1919359 = 2879039) B2879039
theorem B2879045 : Blo 1917435 2879045 := bbase (se 4 (by rfl) ⟨269910, by rfl⟩ : syracuseStep 2879045 = 539821) (by norm_num)
theorem B1919363 : Blo 1917435 1919363 := bstep (se 1 (by rfl) ⟨1439522, by rfl⟩ : syracuseStep 1919363 = 2879045) B2879045
theorem B3238933 : Blo 1917435 3238933 := bbase (se 6 (by rfl) ⟨75912, by rfl⟩ : syracuseStep 3238933 = 151825) (by norm_num)
theorem B4318577 : Blo 1917435 4318577 := bstep (se 2 (by rfl) ⟨1619466, by rfl⟩ : syracuseStep 4318577 = 3238933) B3238933
theorem B2879051 : Blo 1917435 2879051 := bstep (se 1 (by rfl) ⟨2159288, by rfl⟩ : syracuseStep 2879051 = 4318577) B4318577
theorem B1919367 : Blo 1917435 1919367 := bstep (se 1 (by rfl) ⟨1439525, by rfl⟩ : syracuseStep 1919367 = 2879051) B2879051
theorem B2159293 : Blo 1917435 2159293 := bbase (se 3 (by rfl) ⟨404867, by rfl⟩ : syracuseStep 2159293 = 809735) (by norm_num)
theorem B2879057 : Blo 1917435 2879057 := bstep (se 2 (by rfl) ⟨1079646, by rfl⟩ : syracuseStep 2879057 = 2159293) B2159293
theorem B1919371 : Blo 1917435 1919371 := bstep (se 1 (by rfl) ⟨1439528, by rfl⟩ : syracuseStep 1919371 = 2879057) B2879057
theorem B6477893 : Blo 1917435 6477893 := bbase (se 4 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 6477893 = 1214605) (by norm_num)
theorem B4318595 : Blo 1917435 4318595 := bstep (se 1 (by rfl) ⟨3238946, by rfl⟩ : syracuseStep 4318595 = 6477893) B6477893
theorem B2879063 : Blo 1917435 2879063 := bstep (se 1 (by rfl) ⟨2159297, by rfl⟩ : syracuseStep 2879063 = 4318595) B4318595
theorem B1919375 : Blo 1917435 1919375 := bstep (se 1 (by rfl) ⟨1439531, by rfl⟩ : syracuseStep 1919375 = 2879063) B2879063
theorem B2879069 : Blo 1917435 2879069 := bbase (se 3 (by rfl) ⟨539825, by rfl⟩ : syracuseStep 2879069 = 1079651) (by norm_num)
theorem B1919379 : Blo 1917435 1919379 := bstep (se 1 (by rfl) ⟨1439534, by rfl⟩ : syracuseStep 1919379 = 2879069) B2879069
theorem B4318613 : Blo 1917435 4318613 := bbase (se 6 (by rfl) ⟨101217, by rfl⟩ : syracuseStep 4318613 = 202435) (by norm_num)
theorem B2879075 : Blo 1917435 2879075 := bstep (se 1 (by rfl) ⟨2159306, by rfl⟩ : syracuseStep 2879075 = 4318613) B4318613
theorem B1919383 : Blo 1917435 1919383 := bstep (se 1 (by rfl) ⟨1439537, by rfl⟩ : syracuseStep 1919383 = 2879075) B2879075
theorem B2594101 : Blo 1917435 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B3458801 : Blo 1917435 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B9223469 : Blo 1917435 9223469 := bstep (se 3 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 9223469 = 3458801) B3458801
theorem B6148979 : Blo 1917435 6148979 := bstep (se 1 (by rfl) ⟨4611734, by rfl⟩ : syracuseStep 6148979 = 9223469) B9223469
theorem B4099319 : Blo 1917435 4099319 := bstep (se 1 (by rfl) ⟨3074489, by rfl⟩ : syracuseStep 4099319 = 6148979) B6148979
theorem B2732879 : Blo 1917435 2732879 := bstep (se 1 (by rfl) ⟨2049659, by rfl⟩ : syracuseStep 2732879 = 4099319) B4099319
theorem B7287677 : Blo 1917435 7287677 := bstep (se 3 (by rfl) ⟨1366439, by rfl⟩ : syracuseStep 7287677 = 2732879) B2732879
theorem B4858451 : Blo 1917435 4858451 := bstep (se 1 (by rfl) ⟨3643838, by rfl⟩ : syracuseStep 4858451 = 7287677) B7287677
theorem B3238967 : Blo 1917435 3238967 := bstep (se 1 (by rfl) ⟨2429225, by rfl⟩ : syracuseStep 3238967 = 4858451) B4858451
theorem B2159311 : Blo 1917435 2159311 := bstep (se 1 (by rfl) ⟨1619483, by rfl⟩ : syracuseStep 2159311 = 3238967) B3238967
theorem B2879081 : Blo 1917435 2879081 := bstep (se 2 (by rfl) ⟨1079655, by rfl⟩ : syracuseStep 2879081 = 2159311) B2159311
theorem B1919387 : Blo 1917435 1919387 := bstep (se 1 (by rfl) ⟨1439540, by rfl⟩ : syracuseStep 1919387 = 2879081) B2879081
theorem B9476885 : Blo 1917435 9476885 := bbase (se 6 (by rfl) ⟨222114, by rfl⟩ : syracuseStep 9476885 = 444229) (by norm_num)
theorem B6317923 : Blo 1917435 6317923 := bstep (se 1 (by rfl) ⟨4738442, by rfl⟩ : syracuseStep 6317923 = 9476885) B9476885
theorem B8423897 : Blo 1917435 8423897 := bstep (se 2 (by rfl) ⟨3158961, by rfl⟩ : syracuseStep 8423897 = 6317923) B6317923
theorem B22463725 : Blo 1917435 22463725 := bstep (se 3 (by rfl) ⟨4211948, by rfl⟩ : syracuseStep 22463725 = 8423897) B8423897
theorem B29951633 : Blo 1917435 29951633 := bstep (se 2 (by rfl) ⟨11231862, by rfl⟩ : syracuseStep 29951633 = 22463725) B22463725
theorem B19967755 : Blo 1917435 19967755 := bstep (se 1 (by rfl) ⟨14975816, by rfl⟩ : syracuseStep 19967755 = 29951633) B29951633
theorem B26623673 : Blo 1917435 26623673 := bstep (se 2 (by rfl) ⟨9983877, by rfl⟩ : syracuseStep 26623673 = 19967755) B19967755
theorem B17749115 : Blo 1917435 17749115 := bstep (se 1 (by rfl) ⟨13311836, by rfl⟩ : syracuseStep 17749115 = 26623673) B26623673
theorem B11832743 : Blo 1917435 11832743 := bstep (se 1 (by rfl) ⟨8874557, by rfl⟩ : syracuseStep 11832743 = 17749115) B17749115
theorem B31553981 : Blo 1917435 31553981 := bstep (se 3 (by rfl) ⟨5916371, by rfl⟩ : syracuseStep 31553981 = 11832743) B11832743
theorem B21035987 : Blo 1917435 21035987 := bstep (se 1 (by rfl) ⟨15776990, by rfl⟩ : syracuseStep 21035987 = 31553981) B31553981
theorem B14023991 : Blo 1917435 14023991 := bstep (se 1 (by rfl) ⟨10517993, by rfl⟩ : syracuseStep 14023991 = 21035987) B21035987
theorem B9349327 : Blo 1917435 9349327 := bstep (se 1 (by rfl) ⟨7011995, by rfl⟩ : syracuseStep 9349327 = 14023991) B14023991
theorem B49863077 : Blo 1917435 49863077 := bstep (se 4 (by rfl) ⟨4674663, by rfl⟩ : syracuseStep 49863077 = 9349327) B9349327
theorem B33242051 : Blo 1917435 33242051 := bstep (se 1 (by rfl) ⟨24931538, by rfl⟩ : syracuseStep 33242051 = 49863077) B49863077
theorem B22161367 : Blo 1917435 22161367 := bstep (se 1 (by rfl) ⟨16621025, by rfl⟩ : syracuseStep 22161367 = 33242051) B33242051
theorem B29548489 : Blo 1917435 29548489 := bstep (se 2 (by rfl) ⟨11080683, by rfl⟩ : syracuseStep 29548489 = 22161367) B22161367
theorem B39397985 : Blo 1917435 39397985 := bstep (se 2 (by rfl) ⟨14774244, by rfl⟩ : syracuseStep 39397985 = 29548489) B29548489
theorem B26265323 : Blo 1917435 26265323 := bstep (se 1 (by rfl) ⟨19698992, by rfl⟩ : syracuseStep 26265323 = 39397985) B39397985
theorem B17510215 : Blo 1917435 17510215 := bstep (se 1 (by rfl) ⟨13132661, by rfl⟩ : syracuseStep 17510215 = 26265323) B26265323
theorem B23346953 : Blo 1917435 23346953 := bstep (se 2 (by rfl) ⟨8755107, by rfl⟩ : syracuseStep 23346953 = 17510215) B17510215
theorem B15564635 : Blo 1917435 15564635 := bstep (se 1 (by rfl) ⟨11673476, by rfl⟩ : syracuseStep 15564635 = 23346953) B23346953
theorem B10376423 : Blo 1917435 10376423 := bstep (se 1 (by rfl) ⟨7782317, by rfl⟩ : syracuseStep 10376423 = 15564635) B15564635
theorem B6917615 : Blo 1917435 6917615 := bstep (se 1 (by rfl) ⟨5188211, by rfl⟩ : syracuseStep 6917615 = 10376423) B10376423
theorem B4611743 : Blo 1917435 4611743 := bstep (se 1 (by rfl) ⟨3458807, by rfl⟩ : syracuseStep 4611743 = 6917615) B6917615
theorem B3074495 : Blo 1917435 3074495 := bstep (se 1 (by rfl) ⟨2305871, by rfl⟩ : syracuseStep 3074495 = 4611743) B4611743
theorem B8198653 : Blo 1917435 8198653 := bstep (se 3 (by rfl) ⟨1537247, by rfl⟩ : syracuseStep 8198653 = 3074495) B3074495
theorem B10931537 : Blo 1917435 10931537 := bstep (se 2 (by rfl) ⟨4099326, by rfl⟩ : syracuseStep 10931537 = 8198653) B8198653
theorem B7287691 : Blo 1917435 7287691 := bstep (se 1 (by rfl) ⟨5465768, by rfl⟩ : syracuseStep 7287691 = 10931537) B10931537
theorem B9716921 : Blo 1917435 9716921 := bstep (se 2 (by rfl) ⟨3643845, by rfl⟩ : syracuseStep 9716921 = 7287691) B7287691
theorem B6477947 : Blo 1917435 6477947 := bstep (se 1 (by rfl) ⟨4858460, by rfl⟩ : syracuseStep 6477947 = 9716921) B9716921
theorem B4318631 : Blo 1917435 4318631 := bstep (se 1 (by rfl) ⟨3238973, by rfl⟩ : syracuseStep 4318631 = 6477947) B6477947
theorem B2879087 : Blo 1917435 2879087 := bstep (se 1 (by rfl) ⟨2159315, by rfl⟩ : syracuseStep 2879087 = 4318631) B4318631
theorem B1919391 : Blo 1917435 1919391 := bstep (se 1 (by rfl) ⟨1439543, by rfl⟩ : syracuseStep 1919391 = 2879087) B2879087
theorem B2879093 : Blo 1917435 2879093 := bbase (se 5 (by rfl) ⟨134957, by rfl⟩ : syracuseStep 2879093 = 269915) (by norm_num)
theorem B1919395 : Blo 1917435 1919395 := bstep (se 1 (by rfl) ⟨1439546, by rfl⟩ : syracuseStep 1919395 = 2879093) B2879093
theorem B3643861 : Blo 1917435 3643861 := bbase (se 7 (by rfl) ⟨42701, by rfl⟩ : syracuseStep 3643861 = 85403) (by norm_num)
theorem B4858481 : Blo 1917435 4858481 := bstep (se 2 (by rfl) ⟨1821930, by rfl⟩ : syracuseStep 4858481 = 3643861) B3643861
theorem B3238987 : Blo 1917435 3238987 := bstep (se 1 (by rfl) ⟨2429240, by rfl⟩ : syracuseStep 3238987 = 4858481) B4858481
theorem B4318649 : Blo 1917435 4318649 := bstep (se 2 (by rfl) ⟨1619493, by rfl⟩ : syracuseStep 4318649 = 3238987) B3238987
theorem B2879099 : Blo 1917435 2879099 := bstep (se 1 (by rfl) ⟨2159324, by rfl⟩ : syracuseStep 2879099 = 4318649) B4318649
theorem B1919399 : Blo 1917435 1919399 := bstep (se 1 (by rfl) ⟨1439549, by rfl⟩ : syracuseStep 1919399 = 2879099) B2879099
theorem B2159329 : Blo 1917435 2159329 := bbase (se 2 (by rfl) ⟨809748, by rfl⟩ : syracuseStep 2159329 = 1619497) (by norm_num)
theorem B2879105 : Blo 1917435 2879105 := bstep (se 2 (by rfl) ⟨1079664, by rfl⟩ : syracuseStep 2879105 = 2159329) B2159329
theorem B1919403 : Blo 1917435 1919403 := bstep (se 1 (by rfl) ⟨1439552, by rfl⟩ : syracuseStep 1919403 = 2879105) B2879105
theorem B4858501 : Blo 1917435 4858501 := bbase (se 4 (by rfl) ⟨455484, by rfl⟩ : syracuseStep 4858501 = 910969) (by norm_num)
theorem B6478001 : Blo 1917435 6478001 := bstep (se 2 (by rfl) ⟨2429250, by rfl⟩ : syracuseStep 6478001 = 4858501) B4858501
theorem B4318667 : Blo 1917435 4318667 := bstep (se 1 (by rfl) ⟨3239000, by rfl⟩ : syracuseStep 4318667 = 6478001) B6478001
theorem B2879111 : Blo 1917435 2879111 := bstep (se 1 (by rfl) ⟨2159333, by rfl⟩ : syracuseStep 2879111 = 4318667) B4318667
theorem B1919407 : Blo 1917435 1919407 := bstep (se 1 (by rfl) ⟨1439555, by rfl⟩ : syracuseStep 1919407 = 2879111) B2879111
theorem B2879117 : Blo 1917435 2879117 := bbase (se 3 (by rfl) ⟨539834, by rfl⟩ : syracuseStep 2879117 = 1079669) (by norm_num)
theorem B1919411 : Blo 1917435 1919411 := bstep (se 1 (by rfl) ⟨1439558, by rfl⟩ : syracuseStep 1919411 = 2879117) B2879117
theorem B4318685 : Blo 1917435 4318685 := bbase (se 3 (by rfl) ⟨809753, by rfl⟩ : syracuseStep 4318685 = 1619507) (by norm_num)
theorem B2879123 : Blo 1917435 2879123 := bstep (se 1 (by rfl) ⟨2159342, by rfl⟩ : syracuseStep 2879123 = 4318685) B4318685
theorem B1919415 : Blo 1917435 1919415 := bstep (se 1 (by rfl) ⟨1439561, by rfl⟩ : syracuseStep 1919415 = 2879123) B2879123
theorem B3239021 : Blo 1917435 3239021 := bbase (se 3 (by rfl) ⟨607316, by rfl⟩ : syracuseStep 3239021 = 1214633) (by norm_num)
theorem B2159347 : Blo 1917435 2159347 := bstep (se 1 (by rfl) ⟨1619510, by rfl⟩ : syracuseStep 2159347 = 3239021) B3239021
theorem B2879129 : Blo 1917435 2879129 := bstep (se 2 (by rfl) ⟨1079673, by rfl⟩ : syracuseStep 2879129 = 2159347) B2159347
theorem B1919419 : Blo 1917435 1919419 := bstep (se 1 (by rfl) ⟨1439564, by rfl⟩ : syracuseStep 1919419 = 2879129) B2879129
theorem B8755253 : Blo 1917435 8755253 := bbase (se 5 (by rfl) ⟨410402, by rfl⟩ : syracuseStep 8755253 = 820805) (by norm_num)
theorem B5836835 : Blo 1917435 5836835 := bstep (se 1 (by rfl) ⟨4377626, by rfl⟩ : syracuseStep 5836835 = 8755253) B8755253
theorem B3891223 : Blo 1917435 3891223 := bstep (se 1 (by rfl) ⟨2918417, by rfl⟩ : syracuseStep 3891223 = 5836835) B5836835
theorem B5188297 : Blo 1917435 5188297 := bstep (se 2 (by rfl) ⟨1945611, by rfl⟩ : syracuseStep 5188297 = 3891223) B3891223
theorem B6917729 : Blo 1917435 6917729 := bstep (se 2 (by rfl) ⟨2594148, by rfl⟩ : syracuseStep 6917729 = 5188297) B5188297
theorem B18447277 : Blo 1917435 18447277 := bstep (se 3 (by rfl) ⟨3458864, by rfl⟩ : syracuseStep 18447277 = 6917729) B6917729
theorem B24596369 : Blo 1917435 24596369 := bstep (se 2 (by rfl) ⟨9223638, by rfl⟩ : syracuseStep 24596369 = 18447277) B18447277
theorem B16397579 : Blo 1917435 16397579 := bstep (se 1 (by rfl) ⟨12298184, by rfl⟩ : syracuseStep 16397579 = 24596369) B24596369
theorem B10931719 : Blo 1917435 10931719 := bstep (se 1 (by rfl) ⟨8198789, by rfl⟩ : syracuseStep 10931719 = 16397579) B16397579
theorem B14575625 : Blo 1917435 14575625 := bstep (se 2 (by rfl) ⟨5465859, by rfl⟩ : syracuseStep 14575625 = 10931719) B10931719
theorem B9717083 : Blo 1917435 9717083 := bstep (se 1 (by rfl) ⟨7287812, by rfl⟩ : syracuseStep 9717083 = 14575625) B14575625
theorem B6478055 : Blo 1917435 6478055 := bstep (se 1 (by rfl) ⟨4858541, by rfl⟩ : syracuseStep 6478055 = 9717083) B9717083
theorem B4318703 : Blo 1917435 4318703 := bstep (se 1 (by rfl) ⟨3239027, by rfl⟩ : syracuseStep 4318703 = 6478055) B6478055
theorem B2879135 : Blo 1917435 2879135 := bstep (se 1 (by rfl) ⟨2159351, by rfl⟩ : syracuseStep 2879135 = 4318703) B4318703
theorem B1919423 : Blo 1917435 1919423 := bstep (se 1 (by rfl) ⟨1439567, by rfl⟩ : syracuseStep 1919423 = 2879135) B2879135
theorem B2879141 : Blo 1917435 2879141 := bbase (se 4 (by rfl) ⟨269919, by rfl⟩ : syracuseStep 2879141 = 539839) (by norm_num)
theorem B1919427 : Blo 1917435 1919427 := bstep (se 1 (by rfl) ⟨1439570, by rfl⟩ : syracuseStep 1919427 = 2879141) B2879141
theorem B2429281 : Blo 1917435 2429281 := bbase (se 2 (by rfl) ⟨910980, by rfl⟩ : syracuseStep 2429281 = 1821961) (by norm_num)
theorem B3239041 : Blo 1917435 3239041 := bstep (se 2 (by rfl) ⟨1214640, by rfl⟩ : syracuseStep 3239041 = 2429281) B2429281
theorem B4318721 : Blo 1917435 4318721 := bstep (se 2 (by rfl) ⟨1619520, by rfl⟩ : syracuseStep 4318721 = 3239041) B3239041
theorem B2879147 : Blo 1917435 2879147 := bstep (se 1 (by rfl) ⟨2159360, by rfl⟩ : syracuseStep 2879147 = 4318721) B4318721
theorem B1919431 : Blo 1917435 1919431 := bstep (se 1 (by rfl) ⟨1439573, by rfl⟩ : syracuseStep 1919431 = 2879147) B2879147
theorem B2159365 : Blo 1917435 2159365 := bbase (se 4 (by rfl) ⟨202440, by rfl⟩ : syracuseStep 2159365 = 404881) (by norm_num)
theorem B2879153 : Blo 1917435 2879153 := bstep (se 2 (by rfl) ⟨1079682, by rfl⟩ : syracuseStep 2879153 = 2159365) B2159365
theorem B1919435 : Blo 1917435 1919435 := bstep (se 1 (by rfl) ⟨1439576, by rfl⟩ : syracuseStep 1919435 = 2879153) B2879153
theorem C0 (j : ℕ) (h1 : 479358 ≤ j) (h2 : j ≤ 479858) : Blo 1917435 (4 * j + 3) := by
  interval_cases j
  · exact B1917435
  · exact B1917439
  · exact B1917443
  · exact B1917447
  · exact B1917451
  · exact B1917455
  · exact B1917459
  · exact B1917463
  · exact B1917467
  · exact B1917471
  · exact B1917475
  · exact B1917479
  · exact B1917483
  · exact B1917487
  · exact B1917491
  · exact B1917495
  · exact B1917499
  · exact B1917503
  · exact B1917507
  · exact B1917511
  · exact B1917515
  · exact B1917519
  · exact B1917523
  · exact B1917527
  · exact B1917531
  · exact B1917535
  · exact B1917539
  · exact B1917543
  · exact B1917547
  · exact B1917551
  · exact B1917555
  · exact B1917559
  · exact B1917563
  · exact B1917567
  · exact B1917571
  · exact B1917575
  · exact B1917579
  · exact B1917583
  · exact B1917587
  · exact B1917591
  · exact B1917595
  · exact B1917599
  · exact B1917603
  · exact B1917607
  · exact B1917611
  · exact B1917615
  · exact B1917619
  · exact B1917623
  · exact B1917627
  · exact B1917631
  · exact B1917635
  · exact B1917639
  · exact B1917643
  · exact B1917647
  · exact B1917651
  · exact B1917655
  · exact B1917659
  · exact B1917663
  · exact B1917667
  · exact B1917671
  · exact B1917675
  · exact B1917679
  · exact B1917683
  · exact B1917687
  · exact B1917691
  · exact B1917695
  · exact B1917699
  · exact B1917703
  · exact B1917707
  · exact B1917711
  · exact B1917715
  · exact B1917719
  · exact B1917723
  · exact B1917727
  · exact B1917731
  · exact B1917735
  · exact B1917739
  · exact B1917743
  · exact B1917747
  · exact B1917751
  · exact B1917755
  · exact B1917759
  · exact B1917763
  · exact B1917767
  · exact B1917771
  · exact B1917775
  · exact B1917779
  · exact B1917783
  · exact B1917787
  · exact B1917791
  · exact B1917795
  · exact B1917799
  · exact B1917803
  · exact B1917807
  · exact B1917811
  · exact B1917815
  · exact B1917819
  · exact B1917823
  · exact B1917827
  · exact B1917831
  · exact B1917835
  · exact B1917839
  · exact B1917843
  · exact B1917847
  · exact B1917851
  · exact B1917855
  · exact B1917859
  · exact B1917863
  · exact B1917867
  · exact B1917871
  · exact B1917875
  · exact B1917879
  · exact B1917883
  · exact B1917887
  · exact B1917891
  · exact B1917895
  · exact B1917899
  · exact B1917903
  · exact B1917907
  · exact B1917911
  · exact B1917915
  · exact B1917919
  · exact B1917923
  · exact B1917927
  · exact B1917931
  · exact B1917935
  · exact B1917939
  · exact B1917943
  · exact B1917947
  · exact B1917951
  · exact B1917955
  · exact B1917959
  · exact B1917963
  · exact B1917967
  · exact B1917971
  · exact B1917975
  · exact B1917979
  · exact B1917983
  · exact B1917987
  · exact B1917991
  · exact B1917995
  · exact B1917999
  · exact B1918003
  · exact B1918007
  · exact B1918011
  · exact B1918015
  · exact B1918019
  · exact B1918023
  · exact B1918027
  · exact B1918031
  · exact B1918035
  · exact B1918039
  · exact B1918043
  · exact B1918047
  · exact B1918051
  · exact B1918055
  · exact B1918059
  · exact B1918063
  · exact B1918067
  · exact B1918071
  · exact B1918075
  · exact B1918079
  · exact B1918083
  · exact B1918087
  · exact B1918091
  · exact B1918095
  · exact B1918099
  · exact B1918103
  · exact B1918107
  · exact B1918111
  · exact B1918115
  · exact B1918119
  · exact B1918123
  · exact B1918127
  · exact B1918131
  · exact B1918135
  · exact B1918139
  · exact B1918143
  · exact B1918147
  · exact B1918151
  · exact B1918155
  · exact B1918159
  · exact B1918163
  · exact B1918167
  · exact B1918171
  · exact B1918175
  · exact B1918179
  · exact B1918183
  · exact B1918187
  · exact B1918191
  · exact B1918195
  · exact B1918199
  · exact B1918203
  · exact B1918207
  · exact B1918211
  · exact B1918215
  · exact B1918219
  · exact B1918223
  · exact B1918227
  · exact B1918231
  · exact B1918235
  · exact B1918239
  · exact B1918243
  · exact B1918247
  · exact B1918251
  · exact B1918255
  · exact B1918259
  · exact B1918263
  · exact B1918267
  · exact B1918271
  · exact B1918275
  · exact B1918279
  · exact B1918283
  · exact B1918287
  · exact B1918291
  · exact B1918295
  · exact B1918299
  · exact B1918303
  · exact B1918307
  · exact B1918311
  · exact B1918315
  · exact B1918319
  · exact B1918323
  · exact B1918327
  · exact B1918331
  · exact B1918335
  · exact B1918339
  · exact B1918343
  · exact B1918347
  · exact B1918351
  · exact B1918355
  · exact B1918359
  · exact B1918363
  · exact B1918367
  · exact B1918371
  · exact B1918375
  · exact B1918379
  · exact B1918383
  · exact B1918387
  · exact B1918391
  · exact B1918395
  · exact B1918399
  · exact B1918403
  · exact B1918407
  · exact B1918411
  · exact B1918415
  · exact B1918419
  · exact B1918423
  · exact B1918427
  · exact B1918431
  · exact B1918435
  · exact B1918439
  · exact B1918443
  · exact B1918447
  · exact B1918451
  · exact B1918455
  · exact B1918459
  · exact B1918463
  · exact B1918467
  · exact B1918471
  · exact B1918475
  · exact B1918479
  · exact B1918483
  · exact B1918487
  · exact B1918491
  · exact B1918495
  · exact B1918499
  · exact B1918503
  · exact B1918507
  · exact B1918511
  · exact B1918515
  · exact B1918519
  · exact B1918523
  · exact B1918527
  · exact B1918531
  · exact B1918535
  · exact B1918539
  · exact B1918543
  · exact B1918547
  · exact B1918551
  · exact B1918555
  · exact B1918559
  · exact B1918563
  · exact B1918567
  · exact B1918571
  · exact B1918575
  · exact B1918579
  · exact B1918583
  · exact B1918587
  · exact B1918591
  · exact B1918595
  · exact B1918599
  · exact B1918603
  · exact B1918607
  · exact B1918611
  · exact B1918615
  · exact B1918619
  · exact B1918623
  · exact B1918627
  · exact B1918631
  · exact B1918635
  · exact B1918639
  · exact B1918643
  · exact B1918647
  · exact B1918651
  · exact B1918655
  · exact B1918659
  · exact B1918663
  · exact B1918667
  · exact B1918671
  · exact B1918675
  · exact B1918679
  · exact B1918683
  · exact B1918687
  · exact B1918691
  · exact B1918695
  · exact B1918699
  · exact B1918703
  · exact B1918707
  · exact B1918711
  · exact B1918715
  · exact B1918719
  · exact B1918723
  · exact B1918727
  · exact B1918731
  · exact B1918735
  · exact B1918739
  · exact B1918743
  · exact B1918747
  · exact B1918751
  · exact B1918755
  · exact B1918759
  · exact B1918763
  · exact B1918767
  · exact B1918771
  · exact B1918775
  · exact B1918779
  · exact B1918783
  · exact B1918787
  · exact B1918791
  · exact B1918795
  · exact B1918799
  · exact B1918803
  · exact B1918807
  · exact B1918811
  · exact B1918815
  · exact B1918819
  · exact B1918823
  · exact B1918827
  · exact B1918831
  · exact B1918835
  · exact B1918839
  · exact B1918843
  · exact B1918847
  · exact B1918851
  · exact B1918855
  · exact B1918859
  · exact B1918863
  · exact B1918867
  · exact B1918871
  · exact B1918875
  · exact B1918879
  · exact B1918883
  · exact B1918887
  · exact B1918891
  · exact B1918895
  · exact B1918899
  · exact B1918903
  · exact B1918907
  · exact B1918911
  · exact B1918915
  · exact B1918919
  · exact B1918923
  · exact B1918927
  · exact B1918931
  · exact B1918935
  · exact B1918939
  · exact B1918943
  · exact B1918947
  · exact B1918951
  · exact B1918955
  · exact B1918959
  · exact B1918963
  · exact B1918967
  · exact B1918971
  · exact B1918975
  · exact B1918979
  · exact B1918983
  · exact B1918987
  · exact B1918991
  · exact B1918995
  · exact B1918999
  · exact B1919003
  · exact B1919007
  · exact B1919011
  · exact B1919015
  · exact B1919019
  · exact B1919023
  · exact B1919027
  · exact B1919031
  · exact B1919035
  · exact B1919039
  · exact B1919043
  · exact B1919047
  · exact B1919051
  · exact B1919055
  · exact B1919059
  · exact B1919063
  · exact B1919067
  · exact B1919071
  · exact B1919075
  · exact B1919079
  · exact B1919083
  · exact B1919087
  · exact B1919091
  · exact B1919095
  · exact B1919099
  · exact B1919103
  · exact B1919107
  · exact B1919111
  · exact B1919115
  · exact B1919119
  · exact B1919123
  · exact B1919127
  · exact B1919131
  · exact B1919135
  · exact B1919139
  · exact B1919143
  · exact B1919147
  · exact B1919151
  · exact B1919155
  · exact B1919159
  · exact B1919163
  · exact B1919167
  · exact B1919171
  · exact B1919175
  · exact B1919179
  · exact B1919183
  · exact B1919187
  · exact B1919191
  · exact B1919195
  · exact B1919199
  · exact B1919203
  · exact B1919207
  · exact B1919211
  · exact B1919215
  · exact B1919219
  · exact B1919223
  · exact B1919227
  · exact B1919231
  · exact B1919235
  · exact B1919239
  · exact B1919243
  · exact B1919247
  · exact B1919251
  · exact B1919255
  · exact B1919259
  · exact B1919263
  · exact B1919267
  · exact B1919271
  · exact B1919275
  · exact B1919279
  · exact B1919283
  · exact B1919287
  · exact B1919291
  · exact B1919295
  · exact B1919299
  · exact B1919303
  · exact B1919307
  · exact B1919311
  · exact B1919315
  · exact B1919319
  · exact B1919323
  · exact B1919327
  · exact B1919331
  · exact B1919335
  · exact B1919339
  · exact B1919343
  · exact B1919347
  · exact B1919351
  · exact B1919355
  · exact B1919359
  · exact B1919363
  · exact B1919367
  · exact B1919371
  · exact B1919375
  · exact B1919379
  · exact B1919383
  · exact B1919387
  · exact B1919391
  · exact B1919395
  · exact B1919399
  · exact B1919403
  · exact B1919407
  · exact B1919411
  · exact B1919415
  · exact B1919419
  · exact B1919423
  · exact B1919427
  · exact B1919431
  · exact B1919435
theorem solution (m : ℕ) (hlo : 1917435 ≤ m) (hhi : m ≤ 1919435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 479358 ≤ j := by omega
    have hj2 : j ≤ 479858 := by omega
    have hb : Blo 1917435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
