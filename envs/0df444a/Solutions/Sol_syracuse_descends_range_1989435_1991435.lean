-- Prove2me | solution 1 for syracuse_descends_range_1989435_1991435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:22.563029+00:00
-- url     : https://prove2.me/submissions/392b6f1b-3bb5-4dee-88a8-8ac22df2e27a

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

theorem B3357173 : Blo 1989435 3357173 := bbase (se 5 (by rfl) ⟨157367, by rfl⟩ : syracuseStep 3357173 = 314735) (by norm_num)
theorem B2238115 : Blo 1989435 2238115 := bstep (se 1 (by rfl) ⟨1678586, by rfl⟩ : syracuseStep 2238115 = 3357173) B3357173
theorem B2984153 : Blo 1989435 2984153 := bstep (se 2 (by rfl) ⟨1119057, by rfl⟩ : syracuseStep 2984153 = 2238115) B2238115
theorem B1989435 : Blo 1989435 1989435 := bstep (se 1 (by rfl) ⟨1492076, by rfl⟩ : syracuseStep 1989435 = 2984153) B2984153
theorem B6373397 : Blo 1989435 6373397 := bbase (se 6 (by rfl) ⟨149376, by rfl⟩ : syracuseStep 6373397 = 298753) (by norm_num)
theorem B4248931 : Blo 1989435 4248931 := bstep (se 1 (by rfl) ⟨3186698, by rfl⟩ : syracuseStep 4248931 = 6373397) B6373397
theorem B5665241 : Blo 1989435 5665241 := bstep (se 2 (by rfl) ⟨2124465, by rfl⟩ : syracuseStep 5665241 = 4248931) B4248931
theorem B15107309 : Blo 1989435 15107309 := bstep (se 3 (by rfl) ⟨2832620, by rfl⟩ : syracuseStep 15107309 = 5665241) B5665241
theorem B10071539 : Blo 1989435 10071539 := bstep (se 1 (by rfl) ⟨7553654, by rfl⟩ : syracuseStep 10071539 = 15107309) B15107309
theorem B6714359 : Blo 1989435 6714359 := bstep (se 1 (by rfl) ⟨5035769, by rfl⟩ : syracuseStep 6714359 = 10071539) B10071539
theorem B4476239 : Blo 1989435 4476239 := bstep (se 1 (by rfl) ⟨3357179, by rfl⟩ : syracuseStep 4476239 = 6714359) B6714359
theorem B2984159 : Blo 1989435 2984159 := bstep (se 1 (by rfl) ⟨2238119, by rfl⟩ : syracuseStep 2984159 = 4476239) B4476239
theorem B1989439 : Blo 1989435 1989439 := bstep (se 1 (by rfl) ⟨1492079, by rfl⟩ : syracuseStep 1989439 = 2984159) B2984159
theorem B2984165 : Blo 1989435 2984165 := bbase (se 4 (by rfl) ⟨279765, by rfl⟩ : syracuseStep 2984165 = 559531) (by norm_num)
theorem B1989443 : Blo 1989435 1989443 := bstep (se 1 (by rfl) ⟨1492082, by rfl⟩ : syracuseStep 1989443 = 2984165) B2984165
theorem B4248949 : Blo 1989435 4248949 := bbase (se 5 (by rfl) ⟨199169, by rfl⟩ : syracuseStep 4248949 = 398339) (by norm_num)
theorem B5665265 : Blo 1989435 5665265 := bstep (se 2 (by rfl) ⟨2124474, by rfl⟩ : syracuseStep 5665265 = 4248949) B4248949
theorem B3776843 : Blo 1989435 3776843 := bstep (se 1 (by rfl) ⟨2832632, by rfl⟩ : syracuseStep 3776843 = 5665265) B5665265
theorem B2517895 : Blo 1989435 2517895 := bstep (se 1 (by rfl) ⟨1888421, by rfl⟩ : syracuseStep 2517895 = 3776843) B3776843
theorem B3357193 : Blo 1989435 3357193 := bstep (se 2 (by rfl) ⟨1258947, by rfl⟩ : syracuseStep 3357193 = 2517895) B2517895
theorem B4476257 : Blo 1989435 4476257 := bstep (se 2 (by rfl) ⟨1678596, by rfl⟩ : syracuseStep 4476257 = 3357193) B3357193
theorem B2984171 : Blo 1989435 2984171 := bstep (se 1 (by rfl) ⟨2238128, by rfl⟩ : syracuseStep 2984171 = 4476257) B4476257
theorem B1989447 : Blo 1989435 1989447 := bstep (se 1 (by rfl) ⟨1492085, by rfl⟩ : syracuseStep 1989447 = 2984171) B2984171
theorem B2238133 : Blo 1989435 2238133 := bbase (se 5 (by rfl) ⟨104912, by rfl⟩ : syracuseStep 2238133 = 209825) (by norm_num)
theorem B2984177 : Blo 1989435 2984177 := bstep (se 2 (by rfl) ⟨1119066, by rfl⟩ : syracuseStep 2984177 = 2238133) B2238133
theorem B1989451 : Blo 1989435 1989451 := bstep (se 1 (by rfl) ⟨1492088, by rfl⟩ : syracuseStep 1989451 = 2984177) B2984177
theorem B2517905 : Blo 1989435 2517905 := bbase (se 2 (by rfl) ⟨944214, by rfl⟩ : syracuseStep 2517905 = 1888429) (by norm_num)
theorem B6714413 : Blo 1989435 6714413 := bstep (se 3 (by rfl) ⟨1258952, by rfl⟩ : syracuseStep 6714413 = 2517905) B2517905
theorem B4476275 : Blo 1989435 4476275 := bstep (se 1 (by rfl) ⟨3357206, by rfl⟩ : syracuseStep 4476275 = 6714413) B6714413
theorem B2984183 : Blo 1989435 2984183 := bstep (se 1 (by rfl) ⟨2238137, by rfl⟩ : syracuseStep 2984183 = 4476275) B4476275
theorem B1989455 : Blo 1989435 1989455 := bstep (se 1 (by rfl) ⟨1492091, by rfl⟩ : syracuseStep 1989455 = 2984183) B2984183
theorem B2984189 : Blo 1989435 2984189 := bbase (se 3 (by rfl) ⟨559535, by rfl⟩ : syracuseStep 2984189 = 1119071) (by norm_num)
theorem B1989459 : Blo 1989435 1989459 := bstep (se 1 (by rfl) ⟨1492094, by rfl⟩ : syracuseStep 1989459 = 2984189) B2984189
theorem B4476293 : Blo 1989435 4476293 := bbase (se 4 (by rfl) ⟨419652, by rfl⟩ : syracuseStep 4476293 = 839305) (by norm_num)
theorem B2984195 : Blo 1989435 2984195 := bstep (se 1 (by rfl) ⟨2238146, by rfl⟩ : syracuseStep 2984195 = 4476293) B4476293
theorem B1989463 : Blo 1989435 1989463 := bstep (se 1 (by rfl) ⟨1492097, by rfl⟩ : syracuseStep 1989463 = 2984195) B2984195
theorem B2832661 : Blo 1989435 2832661 := bbase (se 6 (by rfl) ⟨66390, by rfl⟩ : syracuseStep 2832661 = 132781) (by norm_num)
theorem B3776881 : Blo 1989435 3776881 := bstep (se 2 (by rfl) ⟨1416330, by rfl⟩ : syracuseStep 3776881 = 2832661) B2832661
theorem B5035841 : Blo 1989435 5035841 := bstep (se 2 (by rfl) ⟨1888440, by rfl⟩ : syracuseStep 5035841 = 3776881) B3776881
theorem B3357227 : Blo 1989435 3357227 := bstep (se 1 (by rfl) ⟨2517920, by rfl⟩ : syracuseStep 3357227 = 5035841) B5035841
theorem B2238151 : Blo 1989435 2238151 := bstep (se 1 (by rfl) ⟨1678613, by rfl⟩ : syracuseStep 2238151 = 3357227) B3357227
theorem B2984201 : Blo 1989435 2984201 := bstep (se 2 (by rfl) ⟨1119075, by rfl⟩ : syracuseStep 2984201 = 2238151) B2238151
theorem B1989467 : Blo 1989435 1989467 := bstep (se 1 (by rfl) ⟨1492100, by rfl⟩ : syracuseStep 1989467 = 2984201) B2984201
theorem B10071701 : Blo 1989435 10071701 := bbase (se 6 (by rfl) ⟨236055, by rfl⟩ : syracuseStep 10071701 = 472111) (by norm_num)
theorem B6714467 : Blo 1989435 6714467 := bstep (se 1 (by rfl) ⟨5035850, by rfl⟩ : syracuseStep 6714467 = 10071701) B10071701
theorem B4476311 : Blo 1989435 4476311 := bstep (se 1 (by rfl) ⟨3357233, by rfl⟩ : syracuseStep 4476311 = 6714467) B6714467
theorem B2984207 : Blo 1989435 2984207 := bstep (se 1 (by rfl) ⟨2238155, by rfl⟩ : syracuseStep 2984207 = 4476311) B4476311
theorem B1989471 : Blo 1989435 1989471 := bstep (se 1 (by rfl) ⟨1492103, by rfl⟩ : syracuseStep 1989471 = 2984207) B2984207
theorem B2984213 : Blo 1989435 2984213 := bbase (se 6 (by rfl) ⟨69942, by rfl⟩ : syracuseStep 2984213 = 139885) (by norm_num)
theorem B1989475 : Blo 1989435 1989475 := bstep (se 1 (by rfl) ⟨1492106, by rfl⟩ : syracuseStep 1989475 = 2984213) B2984213
theorem B25494101 : Blo 1989435 25494101 := bbase (se 8 (by rfl) ⟨149379, by rfl⟩ : syracuseStep 25494101 = 298759) (by norm_num)
theorem B16996067 : Blo 1989435 16996067 := bstep (se 1 (by rfl) ⟨12747050, by rfl⟩ : syracuseStep 16996067 = 25494101) B25494101
theorem B11330711 : Blo 1989435 11330711 := bstep (se 1 (by rfl) ⟨8498033, by rfl⟩ : syracuseStep 11330711 = 16996067) B16996067
theorem B7553807 : Blo 1989435 7553807 := bstep (se 1 (by rfl) ⟨5665355, by rfl⟩ : syracuseStep 7553807 = 11330711) B11330711
theorem B5035871 : Blo 1989435 5035871 := bstep (se 1 (by rfl) ⟨3776903, by rfl⟩ : syracuseStep 5035871 = 7553807) B7553807
theorem B3357247 : Blo 1989435 3357247 := bstep (se 1 (by rfl) ⟨2517935, by rfl⟩ : syracuseStep 3357247 = 5035871) B5035871
theorem B4476329 : Blo 1989435 4476329 := bstep (se 2 (by rfl) ⟨1678623, by rfl⟩ : syracuseStep 4476329 = 3357247) B3357247
theorem B2984219 : Blo 1989435 2984219 := bstep (se 1 (by rfl) ⟨2238164, by rfl⟩ : syracuseStep 2984219 = 4476329) B4476329
theorem B1989479 : Blo 1989435 1989479 := bstep (se 1 (by rfl) ⟨1492109, by rfl⟩ : syracuseStep 1989479 = 2984219) B2984219
theorem B2238169 : Blo 1989435 2238169 := bbase (se 2 (by rfl) ⟨839313, by rfl⟩ : syracuseStep 2238169 = 1678627) (by norm_num)
theorem B2984225 : Blo 1989435 2984225 := bstep (se 2 (by rfl) ⟨1119084, by rfl⟩ : syracuseStep 2984225 = 2238169) B2238169
theorem B1989483 : Blo 1989435 1989483 := bstep (se 1 (by rfl) ⟨1492112, by rfl⟩ : syracuseStep 1989483 = 2984225) B2984225
theorem B2124517 : Blo 1989435 2124517 := bbase (se 4 (by rfl) ⟨199173, by rfl⟩ : syracuseStep 2124517 = 398347) (by norm_num)
theorem B2832689 : Blo 1989435 2832689 := bstep (se 2 (by rfl) ⟨1062258, by rfl⟩ : syracuseStep 2832689 = 2124517) B2124517
theorem B7553837 : Blo 1989435 7553837 := bstep (se 3 (by rfl) ⟨1416344, by rfl⟩ : syracuseStep 7553837 = 2832689) B2832689
theorem B5035891 : Blo 1989435 5035891 := bstep (se 1 (by rfl) ⟨3776918, by rfl⟩ : syracuseStep 5035891 = 7553837) B7553837
theorem B6714521 : Blo 1989435 6714521 := bstep (se 2 (by rfl) ⟨2517945, by rfl⟩ : syracuseStep 6714521 = 5035891) B5035891
theorem B4476347 : Blo 1989435 4476347 := bstep (se 1 (by rfl) ⟨3357260, by rfl⟩ : syracuseStep 4476347 = 6714521) B6714521
theorem B2984231 : Blo 1989435 2984231 := bstep (se 1 (by rfl) ⟨2238173, by rfl⟩ : syracuseStep 2984231 = 4476347) B4476347
theorem B1989487 : Blo 1989435 1989487 := bstep (se 1 (by rfl) ⟨1492115, by rfl⟩ : syracuseStep 1989487 = 2984231) B2984231
theorem B2984237 : Blo 1989435 2984237 := bbase (se 3 (by rfl) ⟨559544, by rfl⟩ : syracuseStep 2984237 = 1119089) (by norm_num)
theorem B1989491 : Blo 1989435 1989491 := bstep (se 1 (by rfl) ⟨1492118, by rfl⟩ : syracuseStep 1989491 = 2984237) B2984237
theorem B4476365 : Blo 1989435 4476365 := bbase (se 3 (by rfl) ⟨839318, by rfl⟩ : syracuseStep 4476365 = 1678637) (by norm_num)
theorem B2984243 : Blo 1989435 2984243 := bstep (se 1 (by rfl) ⟨2238182, by rfl⟩ : syracuseStep 2984243 = 4476365) B4476365
theorem B1989495 : Blo 1989435 1989495 := bstep (se 1 (by rfl) ⟨1492121, by rfl⟩ : syracuseStep 1989495 = 2984243) B2984243
theorem B2517961 : Blo 1989435 2517961 := bbase (se 2 (by rfl) ⟨944235, by rfl⟩ : syracuseStep 2517961 = 1888471) (by norm_num)
theorem B3357281 : Blo 1989435 3357281 := bstep (se 2 (by rfl) ⟨1258980, by rfl⟩ : syracuseStep 3357281 = 2517961) B2517961
theorem B2238187 : Blo 1989435 2238187 := bstep (se 1 (by rfl) ⟨1678640, by rfl⟩ : syracuseStep 2238187 = 3357281) B3357281
theorem B2984249 : Blo 1989435 2984249 := bstep (se 2 (by rfl) ⟨1119093, by rfl⟩ : syracuseStep 2984249 = 2238187) B2238187
theorem B1989499 : Blo 1989435 1989499 := bstep (se 1 (by rfl) ⟨1492124, by rfl⟩ : syracuseStep 1989499 = 2984249) B2984249
theorem B10902197 : Blo 1989435 10902197 := bbase (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) (by norm_num)
theorem B7268131 : Blo 1989435 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B9690841 : Blo 1989435 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B12921121 : Blo 1989435 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B17228161 : Blo 1989435 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B22970881 : Blo 1989435 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B30627841 : Blo 1989435 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B40837121 : Blo 1989435 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B27224747 : Blo 1989435 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B18149831 : Blo 1989435 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B12099887 : Blo 1989435 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B8066591 : Blo 1989435 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B5377727 : Blo 1989435 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B3585151 : Blo 1989435 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B19120805 : Blo 1989435 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B12747203 : Blo 1989435 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B8498135 : Blo 1989435 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B22661693 : Blo 1989435 22661693 := bstep (se 3 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 22661693 = 8498135) B8498135
theorem B15107795 : Blo 1989435 15107795 := bstep (se 1 (by rfl) ⟨11330846, by rfl⟩ : syracuseStep 15107795 = 22661693) B22661693
theorem B10071863 : Blo 1989435 10071863 := bstep (se 1 (by rfl) ⟨7553897, by rfl⟩ : syracuseStep 10071863 = 15107795) B15107795
theorem B6714575 : Blo 1989435 6714575 := bstep (se 1 (by rfl) ⟨5035931, by rfl⟩ : syracuseStep 6714575 = 10071863) B10071863
theorem B4476383 : Blo 1989435 4476383 := bstep (se 1 (by rfl) ⟨3357287, by rfl⟩ : syracuseStep 4476383 = 6714575) B6714575
theorem B2984255 : Blo 1989435 2984255 := bstep (se 1 (by rfl) ⟨2238191, by rfl⟩ : syracuseStep 2984255 = 4476383) B4476383
theorem B1989503 : Blo 1989435 1989503 := bstep (se 1 (by rfl) ⟨1492127, by rfl⟩ : syracuseStep 1989503 = 2984255) B2984255
theorem B2984261 : Blo 1989435 2984261 := bbase (se 4 (by rfl) ⟨279774, by rfl⟩ : syracuseStep 2984261 = 559549) (by norm_num)
theorem B1989507 : Blo 1989435 1989507 := bstep (se 1 (by rfl) ⟨1492130, by rfl⟩ : syracuseStep 1989507 = 2984261) B2984261
theorem B3357301 : Blo 1989435 3357301 := bbase (se 5 (by rfl) ⟨157373, by rfl⟩ : syracuseStep 3357301 = 314747) (by norm_num)
theorem B4476401 : Blo 1989435 4476401 := bstep (se 2 (by rfl) ⟨1678650, by rfl⟩ : syracuseStep 4476401 = 3357301) B3357301
theorem B2984267 : Blo 1989435 2984267 := bstep (se 1 (by rfl) ⟨2238200, by rfl⟩ : syracuseStep 2984267 = 4476401) B4476401
theorem B1989511 : Blo 1989435 1989511 := bstep (se 1 (by rfl) ⟨1492133, by rfl⟩ : syracuseStep 1989511 = 2984267) B2984267
theorem B2238205 : Blo 1989435 2238205 := bbase (se 3 (by rfl) ⟨419663, by rfl⟩ : syracuseStep 2238205 = 839327) (by norm_num)
theorem B2984273 : Blo 1989435 2984273 := bstep (se 2 (by rfl) ⟨1119102, by rfl⟩ : syracuseStep 2984273 = 2238205) B2238205
theorem B1989515 : Blo 1989435 1989515 := bstep (se 1 (by rfl) ⟨1492136, by rfl⟩ : syracuseStep 1989515 = 2984273) B2984273
theorem B6714629 : Blo 1989435 6714629 := bbase (se 4 (by rfl) ⟨629496, by rfl⟩ : syracuseStep 6714629 = 1258993) (by norm_num)
theorem B4476419 : Blo 1989435 4476419 := bstep (se 1 (by rfl) ⟨3357314, by rfl⟩ : syracuseStep 4476419 = 6714629) B6714629
theorem B2984279 : Blo 1989435 2984279 := bstep (se 1 (by rfl) ⟨2238209, by rfl⟩ : syracuseStep 2984279 = 4476419) B4476419
theorem B1989519 : Blo 1989435 1989519 := bstep (se 1 (by rfl) ⟨1492139, by rfl⟩ : syracuseStep 1989519 = 2984279) B2984279
theorem B2984285 : Blo 1989435 2984285 := bbase (se 3 (by rfl) ⟨559553, by rfl⟩ : syracuseStep 2984285 = 1119107) (by norm_num)
theorem B1989523 : Blo 1989435 1989523 := bstep (se 1 (by rfl) ⟨1492142, by rfl⟩ : syracuseStep 1989523 = 2984285) B2984285
theorem B4476437 : Blo 1989435 4476437 := bbase (se 6 (by rfl) ⟨104916, by rfl⟩ : syracuseStep 4476437 = 209833) (by norm_num)
theorem B2984291 : Blo 1989435 2984291 := bstep (se 1 (by rfl) ⟨2238218, by rfl⟩ : syracuseStep 2984291 = 4476437) B4476437
theorem B1989527 : Blo 1989435 1989527 := bstep (se 1 (by rfl) ⟨1492145, by rfl⟩ : syracuseStep 1989527 = 2984291) B2984291
theorem B7554005 : Blo 1989435 7554005 := bbase (se 7 (by rfl) ⟨88523, by rfl⟩ : syracuseStep 7554005 = 177047) (by norm_num)
theorem B5036003 : Blo 1989435 5036003 := bstep (se 1 (by rfl) ⟨3777002, by rfl⟩ : syracuseStep 5036003 = 7554005) B7554005
theorem B3357335 : Blo 1989435 3357335 := bstep (se 1 (by rfl) ⟨2518001, by rfl⟩ : syracuseStep 3357335 = 5036003) B5036003
theorem B2238223 : Blo 1989435 2238223 := bstep (se 1 (by rfl) ⟨1678667, by rfl⟩ : syracuseStep 2238223 = 3357335) B3357335
theorem B2984297 : Blo 1989435 2984297 := bstep (se 2 (by rfl) ⟨1119111, by rfl⟩ : syracuseStep 2984297 = 2238223) B2238223
theorem B1989531 : Blo 1989435 1989531 := bstep (se 1 (by rfl) ⟨1492148, by rfl⟩ : syracuseStep 1989531 = 2984297) B2984297
theorem B11331029 : Blo 1989435 11331029 := bbase (se 7 (by rfl) ⟨132785, by rfl⟩ : syracuseStep 11331029 = 265571) (by norm_num)
theorem B7554019 : Blo 1989435 7554019 := bstep (se 1 (by rfl) ⟨5665514, by rfl⟩ : syracuseStep 7554019 = 11331029) B11331029
theorem B10072025 : Blo 1989435 10072025 := bstep (se 2 (by rfl) ⟨3777009, by rfl⟩ : syracuseStep 10072025 = 7554019) B7554019
theorem B6714683 : Blo 1989435 6714683 := bstep (se 1 (by rfl) ⟨5036012, by rfl⟩ : syracuseStep 6714683 = 10072025) B10072025
theorem B4476455 : Blo 1989435 4476455 := bstep (se 1 (by rfl) ⟨3357341, by rfl⟩ : syracuseStep 4476455 = 6714683) B6714683
theorem B2984303 : Blo 1989435 2984303 := bstep (se 1 (by rfl) ⟨2238227, by rfl⟩ : syracuseStep 2984303 = 4476455) B4476455
theorem B1989535 : Blo 1989435 1989535 := bstep (se 1 (by rfl) ⟨1492151, by rfl⟩ : syracuseStep 1989535 = 2984303) B2984303
theorem B2984309 : Blo 1989435 2984309 := bbase (se 5 (by rfl) ⟨139889, by rfl⟩ : syracuseStep 2984309 = 279779) (by norm_num)
theorem B1989539 : Blo 1989435 1989539 := bstep (se 1 (by rfl) ⟨1492154, by rfl⟩ : syracuseStep 1989539 = 2984309) B2984309
theorem B2124577 : Blo 1989435 2124577 := bbase (se 2 (by rfl) ⟨796716, by rfl⟩ : syracuseStep 2124577 = 1593433) (by norm_num)
theorem B2832769 : Blo 1989435 2832769 := bstep (se 2 (by rfl) ⟨1062288, by rfl⟩ : syracuseStep 2832769 = 2124577) B2124577
theorem B3777025 : Blo 1989435 3777025 := bstep (se 2 (by rfl) ⟨1416384, by rfl⟩ : syracuseStep 3777025 = 2832769) B2832769
theorem B5036033 : Blo 1989435 5036033 := bstep (se 2 (by rfl) ⟨1888512, by rfl⟩ : syracuseStep 5036033 = 3777025) B3777025
theorem B3357355 : Blo 1989435 3357355 := bstep (se 1 (by rfl) ⟨2518016, by rfl⟩ : syracuseStep 3357355 = 5036033) B5036033
theorem B4476473 : Blo 1989435 4476473 := bstep (se 2 (by rfl) ⟨1678677, by rfl⟩ : syracuseStep 4476473 = 3357355) B3357355
theorem B2984315 : Blo 1989435 2984315 := bstep (se 1 (by rfl) ⟨2238236, by rfl⟩ : syracuseStep 2984315 = 4476473) B4476473
theorem B1989543 : Blo 1989435 1989543 := bstep (se 1 (by rfl) ⟨1492157, by rfl⟩ : syracuseStep 1989543 = 2984315) B2984315
theorem B2238241 : Blo 1989435 2238241 := bbase (se 2 (by rfl) ⟨839340, by rfl⟩ : syracuseStep 2238241 = 1678681) (by norm_num)
theorem B2984321 : Blo 1989435 2984321 := bstep (se 2 (by rfl) ⟨1119120, by rfl⟩ : syracuseStep 2984321 = 2238241) B2238241
theorem B1989547 : Blo 1989435 1989547 := bstep (se 1 (by rfl) ⟨1492160, by rfl⟩ : syracuseStep 1989547 = 2984321) B2984321
theorem B5036053 : Blo 1989435 5036053 := bbase (se 6 (by rfl) ⟨118032, by rfl⟩ : syracuseStep 5036053 = 236065) (by norm_num)
theorem B6714737 : Blo 1989435 6714737 := bstep (se 2 (by rfl) ⟨2518026, by rfl⟩ : syracuseStep 6714737 = 5036053) B5036053
theorem B4476491 : Blo 1989435 4476491 := bstep (se 1 (by rfl) ⟨3357368, by rfl⟩ : syracuseStep 4476491 = 6714737) B6714737
theorem B2984327 : Blo 1989435 2984327 := bstep (se 1 (by rfl) ⟨2238245, by rfl⟩ : syracuseStep 2984327 = 4476491) B4476491
theorem B1989551 : Blo 1989435 1989551 := bstep (se 1 (by rfl) ⟨1492163, by rfl⟩ : syracuseStep 1989551 = 2984327) B2984327
theorem B2984333 : Blo 1989435 2984333 := bbase (se 3 (by rfl) ⟨559562, by rfl⟩ : syracuseStep 2984333 = 1119125) (by norm_num)
theorem B1989555 : Blo 1989435 1989555 := bstep (se 1 (by rfl) ⟨1492166, by rfl⟩ : syracuseStep 1989555 = 2984333) B2984333
theorem B4476509 : Blo 1989435 4476509 := bbase (se 3 (by rfl) ⟨839345, by rfl⟩ : syracuseStep 4476509 = 1678691) (by norm_num)
theorem B2984339 : Blo 1989435 2984339 := bstep (se 1 (by rfl) ⟨2238254, by rfl⟩ : syracuseStep 2984339 = 4476509) B4476509
theorem B1989559 : Blo 1989435 1989559 := bstep (se 1 (by rfl) ⟨1492169, by rfl⟩ : syracuseStep 1989559 = 2984339) B2984339
theorem B3357389 : Blo 1989435 3357389 := bbase (se 3 (by rfl) ⟨629510, by rfl⟩ : syracuseStep 3357389 = 1259021) (by norm_num)
theorem B2238259 : Blo 1989435 2238259 := bstep (se 1 (by rfl) ⟨1678694, by rfl⟩ : syracuseStep 2238259 = 3357389) B3357389
theorem B2984345 : Blo 1989435 2984345 := bstep (se 2 (by rfl) ⟨1119129, by rfl⟩ : syracuseStep 2984345 = 2238259) B2238259
theorem B1989563 : Blo 1989435 1989563 := bstep (se 1 (by rfl) ⟨1492172, by rfl⟩ : syracuseStep 1989563 = 2984345) B2984345
theorem B7170533 : Blo 1989435 7170533 := bbase (se 4 (by rfl) ⟨672237, by rfl⟩ : syracuseStep 7170533 = 1344475) (by norm_num)
theorem B4780355 : Blo 1989435 4780355 := bstep (se 1 (by rfl) ⟨3585266, by rfl⟩ : syracuseStep 4780355 = 7170533) B7170533
theorem B12747613 : Blo 1989435 12747613 := bstep (se 3 (by rfl) ⟨2390177, by rfl⟩ : syracuseStep 12747613 = 4780355) B4780355
theorem B16996817 : Blo 1989435 16996817 := bstep (se 2 (by rfl) ⟨6373806, by rfl⟩ : syracuseStep 16996817 = 12747613) B12747613
theorem B11331211 : Blo 1989435 11331211 := bstep (se 1 (by rfl) ⟨8498408, by rfl⟩ : syracuseStep 11331211 = 16996817) B16996817
theorem B15108281 : Blo 1989435 15108281 := bstep (se 2 (by rfl) ⟨5665605, by rfl⟩ : syracuseStep 15108281 = 11331211) B11331211
theorem B10072187 : Blo 1989435 10072187 := bstep (se 1 (by rfl) ⟨7554140, by rfl⟩ : syracuseStep 10072187 = 15108281) B15108281
theorem B6714791 : Blo 1989435 6714791 := bstep (se 1 (by rfl) ⟨5036093, by rfl⟩ : syracuseStep 6714791 = 10072187) B10072187
theorem B4476527 : Blo 1989435 4476527 := bstep (se 1 (by rfl) ⟨3357395, by rfl⟩ : syracuseStep 4476527 = 6714791) B6714791
theorem B2984351 : Blo 1989435 2984351 := bstep (se 1 (by rfl) ⟨2238263, by rfl⟩ : syracuseStep 2984351 = 4476527) B4476527
theorem B1989567 : Blo 1989435 1989567 := bstep (se 1 (by rfl) ⟨1492175, by rfl⟩ : syracuseStep 1989567 = 2984351) B2984351
theorem B2984357 : Blo 1989435 2984357 := bbase (se 4 (by rfl) ⟨279783, by rfl⟩ : syracuseStep 2984357 = 559567) (by norm_num)
theorem B1989571 : Blo 1989435 1989571 := bstep (se 1 (by rfl) ⟨1492178, by rfl⟩ : syracuseStep 1989571 = 2984357) B2984357
theorem B2518057 : Blo 1989435 2518057 := bbase (se 2 (by rfl) ⟨944271, by rfl⟩ : syracuseStep 2518057 = 1888543) (by norm_num)
theorem B3357409 : Blo 1989435 3357409 := bstep (se 2 (by rfl) ⟨1259028, by rfl⟩ : syracuseStep 3357409 = 2518057) B2518057
theorem B4476545 : Blo 1989435 4476545 := bstep (se 2 (by rfl) ⟨1678704, by rfl⟩ : syracuseStep 4476545 = 3357409) B3357409
theorem B2984363 : Blo 1989435 2984363 := bstep (se 1 (by rfl) ⟨2238272, by rfl⟩ : syracuseStep 2984363 = 4476545) B4476545
theorem B1989575 : Blo 1989435 1989575 := bstep (se 1 (by rfl) ⟨1492181, by rfl⟩ : syracuseStep 1989575 = 2984363) B2984363
theorem B2238277 : Blo 1989435 2238277 := bbase (se 4 (by rfl) ⟨209838, by rfl⟩ : syracuseStep 2238277 = 419677) (by norm_num)
theorem B2984369 : Blo 1989435 2984369 := bstep (se 2 (by rfl) ⟨1119138, by rfl⟩ : syracuseStep 2984369 = 2238277) B2238277
theorem B1989579 : Blo 1989435 1989579 := bstep (se 1 (by rfl) ⟨1492184, by rfl⟩ : syracuseStep 1989579 = 2984369) B2984369
theorem B3777101 : Blo 1989435 3777101 := bbase (se 3 (by rfl) ⟨708206, by rfl⟩ : syracuseStep 3777101 = 1416413) (by norm_num)
theorem B2518067 : Blo 1989435 2518067 := bstep (se 1 (by rfl) ⟨1888550, by rfl⟩ : syracuseStep 2518067 = 3777101) B3777101
theorem B6714845 : Blo 1989435 6714845 := bstep (se 3 (by rfl) ⟨1259033, by rfl⟩ : syracuseStep 6714845 = 2518067) B2518067
theorem B4476563 : Blo 1989435 4476563 := bstep (se 1 (by rfl) ⟨3357422, by rfl⟩ : syracuseStep 4476563 = 6714845) B6714845
theorem B2984375 : Blo 1989435 2984375 := bstep (se 1 (by rfl) ⟨2238281, by rfl⟩ : syracuseStep 2984375 = 4476563) B4476563
theorem B1989583 : Blo 1989435 1989583 := bstep (se 1 (by rfl) ⟨1492187, by rfl⟩ : syracuseStep 1989583 = 2984375) B2984375
theorem B2984381 : Blo 1989435 2984381 := bbase (se 3 (by rfl) ⟨559571, by rfl⟩ : syracuseStep 2984381 = 1119143) (by norm_num)
theorem B1989587 : Blo 1989435 1989587 := bstep (se 1 (by rfl) ⟨1492190, by rfl⟩ : syracuseStep 1989587 = 2984381) B2984381
theorem B4476581 : Blo 1989435 4476581 := bbase (se 4 (by rfl) ⟨419679, by rfl⟩ : syracuseStep 4476581 = 839359) (by norm_num)
theorem B2984387 : Blo 1989435 2984387 := bstep (se 1 (by rfl) ⟨2238290, by rfl⟩ : syracuseStep 2984387 = 4476581) B4476581
theorem B1989591 : Blo 1989435 1989591 := bstep (se 1 (by rfl) ⟨1492193, by rfl⟩ : syracuseStep 1989591 = 2984387) B2984387
theorem B5036165 : Blo 1989435 5036165 := bbase (se 4 (by rfl) ⟨472140, by rfl⟩ : syracuseStep 5036165 = 944281) (by norm_num)
theorem B3357443 : Blo 1989435 3357443 := bstep (se 1 (by rfl) ⟨2518082, by rfl⟩ : syracuseStep 3357443 = 5036165) B5036165
theorem B2238295 : Blo 1989435 2238295 := bstep (se 1 (by rfl) ⟨1678721, by rfl⟩ : syracuseStep 2238295 = 3357443) B3357443
theorem B2984393 : Blo 1989435 2984393 := bstep (se 2 (by rfl) ⟨1119147, by rfl⟩ : syracuseStep 2984393 = 2238295) B2238295
theorem B1989595 : Blo 1989435 1989595 := bstep (se 1 (by rfl) ⟨1492196, by rfl⟩ : syracuseStep 1989595 = 2984393) B2984393
theorem B3585325 : Blo 1989435 3585325 := bbase (se 3 (by rfl) ⟨672248, by rfl⟩ : syracuseStep 3585325 = 1344497) (by norm_num)
theorem B4780433 : Blo 1989435 4780433 := bstep (se 2 (by rfl) ⟨1792662, by rfl⟩ : syracuseStep 4780433 = 3585325) B3585325
theorem B3186955 : Blo 1989435 3186955 := bstep (se 1 (by rfl) ⟨2390216, by rfl⟩ : syracuseStep 3186955 = 4780433) B4780433
theorem B4249273 : Blo 1989435 4249273 := bstep (se 2 (by rfl) ⟨1593477, by rfl⟩ : syracuseStep 4249273 = 3186955) B3186955
theorem B5665697 : Blo 1989435 5665697 := bstep (se 2 (by rfl) ⟨2124636, by rfl⟩ : syracuseStep 5665697 = 4249273) B4249273
theorem B3777131 : Blo 1989435 3777131 := bstep (se 1 (by rfl) ⟨2832848, by rfl⟩ : syracuseStep 3777131 = 5665697) B5665697
theorem B10072349 : Blo 1989435 10072349 := bstep (se 3 (by rfl) ⟨1888565, by rfl⟩ : syracuseStep 10072349 = 3777131) B3777131
theorem B6714899 : Blo 1989435 6714899 := bstep (se 1 (by rfl) ⟨5036174, by rfl⟩ : syracuseStep 6714899 = 10072349) B10072349
theorem B4476599 : Blo 1989435 4476599 := bstep (se 1 (by rfl) ⟨3357449, by rfl⟩ : syracuseStep 4476599 = 6714899) B6714899
theorem B2984399 : Blo 1989435 2984399 := bstep (se 1 (by rfl) ⟨2238299, by rfl⟩ : syracuseStep 2984399 = 4476599) B4476599
theorem B1989599 : Blo 1989435 1989599 := bstep (se 1 (by rfl) ⟨1492199, by rfl⟩ : syracuseStep 1989599 = 2984399) B2984399
theorem B2984405 : Blo 1989435 2984405 := bbase (se 7 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 2984405 = 69947) (by norm_num)
theorem B1989603 : Blo 1989435 1989603 := bstep (se 1 (by rfl) ⟨1492202, by rfl⟩ : syracuseStep 1989603 = 2984405) B2984405
theorem B7554293 : Blo 1989435 7554293 := bbase (se 5 (by rfl) ⟨354107, by rfl⟩ : syracuseStep 7554293 = 708215) (by norm_num)
theorem B5036195 : Blo 1989435 5036195 := bstep (se 1 (by rfl) ⟨3777146, by rfl⟩ : syracuseStep 5036195 = 7554293) B7554293
theorem B3357463 : Blo 1989435 3357463 := bstep (se 1 (by rfl) ⟨2518097, by rfl⟩ : syracuseStep 3357463 = 5036195) B5036195
theorem B4476617 : Blo 1989435 4476617 := bstep (se 2 (by rfl) ⟨1678731, by rfl⟩ : syracuseStep 4476617 = 3357463) B3357463
theorem B2984411 : Blo 1989435 2984411 := bstep (se 1 (by rfl) ⟨2238308, by rfl⟩ : syracuseStep 2984411 = 4476617) B4476617
theorem B1989607 : Blo 1989435 1989607 := bstep (se 1 (by rfl) ⟨1492205, by rfl⟩ : syracuseStep 1989607 = 2984411) B2984411
theorem B2238313 : Blo 1989435 2238313 := bbase (se 2 (by rfl) ⟨839367, by rfl⟩ : syracuseStep 2238313 = 1678735) (by norm_num)
theorem B2984417 : Blo 1989435 2984417 := bstep (se 2 (by rfl) ⟨1119156, by rfl⟩ : syracuseStep 2984417 = 2238313) B2238313
theorem B1989611 : Blo 1989435 1989611 := bstep (se 1 (by rfl) ⟨1492208, by rfl⟩ : syracuseStep 1989611 = 2984417) B2984417
theorem B2268857 : Blo 1989435 2268857 := bbase (se 2 (by rfl) ⟨850821, by rfl⟩ : syracuseStep 2268857 = 1701643) (by norm_num)
theorem B6050285 : Blo 1989435 6050285 := bstep (se 3 (by rfl) ⟨1134428, by rfl⟩ : syracuseStep 6050285 = 2268857) B2268857
theorem B4033523 : Blo 1989435 4033523 := bstep (se 1 (by rfl) ⟨3025142, by rfl⟩ : syracuseStep 4033523 = 6050285) B6050285
theorem B10756061 : Blo 1989435 10756061 := bstep (se 3 (by rfl) ⟨2016761, by rfl⟩ : syracuseStep 10756061 = 4033523) B4033523
theorem B7170707 : Blo 1989435 7170707 := bstep (se 1 (by rfl) ⟨5378030, by rfl⟩ : syracuseStep 7170707 = 10756061) B10756061
theorem B4780471 : Blo 1989435 4780471 := bstep (se 1 (by rfl) ⟨3585353, by rfl⟩ : syracuseStep 4780471 = 7170707) B7170707
theorem B6373961 : Blo 1989435 6373961 := bstep (se 2 (by rfl) ⟨2390235, by rfl⟩ : syracuseStep 6373961 = 4780471) B4780471
theorem B4249307 : Blo 1989435 4249307 := bstep (se 1 (by rfl) ⟨3186980, by rfl⟩ : syracuseStep 4249307 = 6373961) B6373961
theorem B11331485 : Blo 1989435 11331485 := bstep (se 3 (by rfl) ⟨2124653, by rfl⟩ : syracuseStep 11331485 = 4249307) B4249307
theorem B7554323 : Blo 1989435 7554323 := bstep (se 1 (by rfl) ⟨5665742, by rfl⟩ : syracuseStep 7554323 = 11331485) B11331485
theorem B5036215 : Blo 1989435 5036215 := bstep (se 1 (by rfl) ⟨3777161, by rfl⟩ : syracuseStep 5036215 = 7554323) B7554323
theorem B6714953 : Blo 1989435 6714953 := bstep (se 2 (by rfl) ⟨2518107, by rfl⟩ : syracuseStep 6714953 = 5036215) B5036215
theorem B4476635 : Blo 1989435 4476635 := bstep (se 1 (by rfl) ⟨3357476, by rfl⟩ : syracuseStep 4476635 = 6714953) B6714953
theorem B2984423 : Blo 1989435 2984423 := bstep (se 1 (by rfl) ⟨2238317, by rfl⟩ : syracuseStep 2984423 = 4476635) B4476635
theorem B1989615 : Blo 1989435 1989615 := bstep (se 1 (by rfl) ⟨1492211, by rfl⟩ : syracuseStep 1989615 = 2984423) B2984423
theorem B2984429 : Blo 1989435 2984429 := bbase (se 3 (by rfl) ⟨559580, by rfl⟩ : syracuseStep 2984429 = 1119161) (by norm_num)
theorem B1989619 : Blo 1989435 1989619 := bstep (se 1 (by rfl) ⟨1492214, by rfl⟩ : syracuseStep 1989619 = 2984429) B2984429
theorem B4476653 : Blo 1989435 4476653 := bbase (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) (by norm_num)
theorem B2984435 : Blo 1989435 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B1989623 : Blo 1989435 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B3403309 : Blo 1989435 3403309 := bbase (se 3 (by rfl) ⟨638120, by rfl⟩ : syracuseStep 3403309 = 1276241) (by norm_num)
theorem B4537745 : Blo 1989435 4537745 := bstep (se 2 (by rfl) ⟨1701654, by rfl⟩ : syracuseStep 4537745 = 3403309) B3403309
theorem B3025163 : Blo 1989435 3025163 := bstep (se 1 (by rfl) ⟨2268872, by rfl⟩ : syracuseStep 3025163 = 4537745) B4537745
theorem B2016775 : Blo 1989435 2016775 := bstep (se 1 (by rfl) ⟨1512581, by rfl⟩ : syracuseStep 2016775 = 3025163) B3025163
theorem B2689033 : Blo 1989435 2689033 := bstep (se 2 (by rfl) ⟨1008387, by rfl⟩ : syracuseStep 2689033 = 2016775) B2016775
theorem B3585377 : Blo 1989435 3585377 := bstep (se 2 (by rfl) ⟨1344516, by rfl⟩ : syracuseStep 3585377 = 2689033) B2689033
theorem B2390251 : Blo 1989435 2390251 := bstep (se 1 (by rfl) ⟨1792688, by rfl⟩ : syracuseStep 2390251 = 3585377) B3585377
theorem B3187001 : Blo 1989435 3187001 := bstep (se 2 (by rfl) ⟨1195125, by rfl⟩ : syracuseStep 3187001 = 2390251) B2390251
theorem B2124667 : Blo 1989435 2124667 := bstep (se 1 (by rfl) ⟨1593500, by rfl⟩ : syracuseStep 2124667 = 3187001) B3187001
theorem B2832889 : Blo 1989435 2832889 := bstep (se 2 (by rfl) ⟨1062333, by rfl⟩ : syracuseStep 2832889 = 2124667) B2124667
theorem B3777185 : Blo 1989435 3777185 := bstep (se 2 (by rfl) ⟨1416444, by rfl⟩ : syracuseStep 3777185 = 2832889) B2832889
theorem B2518123 : Blo 1989435 2518123 := bstep (se 1 (by rfl) ⟨1888592, by rfl⟩ : syracuseStep 2518123 = 3777185) B3777185
theorem B3357497 : Blo 1989435 3357497 := bstep (se 2 (by rfl) ⟨1259061, by rfl⟩ : syracuseStep 3357497 = 2518123) B2518123
theorem B2238331 : Blo 1989435 2238331 := bstep (se 1 (by rfl) ⟨1678748, by rfl⟩ : syracuseStep 2238331 = 3357497) B3357497
theorem B2984441 : Blo 1989435 2984441 := bstep (se 2 (by rfl) ⟨1119165, by rfl⟩ : syracuseStep 2984441 = 2238331) B2238331
theorem B1989627 : Blo 1989435 1989627 := bstep (se 1 (by rfl) ⟨1492220, by rfl⟩ : syracuseStep 1989627 = 2984441) B2984441
theorem B3108277 : Blo 1989435 3108277 := bbase (se 5 (by rfl) ⟨145700, by rfl⟩ : syracuseStep 3108277 = 291401) (by norm_num)
theorem B4144369 : Blo 1989435 4144369 := bstep (se 2 (by rfl) ⟨1554138, by rfl⟩ : syracuseStep 4144369 = 3108277) B3108277
theorem B5525825 : Blo 1989435 5525825 := bstep (se 2 (by rfl) ⟨2072184, by rfl⟩ : syracuseStep 5525825 = 4144369) B4144369
theorem B14735533 : Blo 1989435 14735533 := bstep (se 3 (by rfl) ⟨2762912, by rfl⟩ : syracuseStep 14735533 = 5525825) B5525825
theorem B19647377 : Blo 1989435 19647377 := bstep (se 2 (by rfl) ⟨7367766, by rfl⟩ : syracuseStep 19647377 = 14735533) B14735533
theorem B13098251 : Blo 1989435 13098251 := bstep (se 1 (by rfl) ⟨9823688, by rfl⟩ : syracuseStep 13098251 = 19647377) B19647377
theorem B8732167 : Blo 1989435 8732167 := bstep (se 1 (by rfl) ⟨6549125, by rfl⟩ : syracuseStep 8732167 = 13098251) B13098251
theorem B46571557 : Blo 1989435 46571557 := bstep (se 4 (by rfl) ⟨4366083, by rfl⟩ : syracuseStep 46571557 = 8732167) B8732167
theorem B62095409 : Blo 1989435 62095409 := bstep (se 2 (by rfl) ⟨23285778, by rfl⟩ : syracuseStep 62095409 = 46571557) B46571557
theorem B41396939 : Blo 1989435 41396939 := bstep (se 1 (by rfl) ⟨31047704, by rfl⟩ : syracuseStep 41396939 = 62095409) B62095409
theorem B27597959 : Blo 1989435 27597959 := bstep (se 1 (by rfl) ⟨20698469, by rfl⟩ : syracuseStep 27597959 = 41396939) B41396939
theorem B18398639 : Blo 1989435 18398639 := bstep (se 1 (by rfl) ⟨13798979, by rfl⟩ : syracuseStep 18398639 = 27597959) B27597959
theorem B12265759 : Blo 1989435 12265759 := bstep (se 1 (by rfl) ⟨9199319, by rfl⟩ : syracuseStep 12265759 = 18398639) B18398639
theorem B16354345 : Blo 1989435 16354345 := bstep (se 2 (by rfl) ⟨6132879, by rfl⟩ : syracuseStep 16354345 = 12265759) B12265759
theorem B21805793 : Blo 1989435 21805793 := bstep (se 2 (by rfl) ⟨8177172, by rfl⟩ : syracuseStep 21805793 = 16354345) B16354345
theorem B14537195 : Blo 1989435 14537195 := bstep (se 1 (by rfl) ⟨10902896, by rfl⟩ : syracuseStep 14537195 = 21805793) B21805793
theorem B9691463 : Blo 1989435 9691463 := bstep (se 1 (by rfl) ⟨7268597, by rfl⟩ : syracuseStep 9691463 = 14537195) B14537195
theorem B6460975 : Blo 1989435 6460975 := bstep (se 1 (by rfl) ⟨4845731, by rfl⟩ : syracuseStep 6460975 = 9691463) B9691463
theorem B34458533 : Blo 1989435 34458533 := bstep (se 4 (by rfl) ⟨3230487, by rfl⟩ : syracuseStep 34458533 = 6460975) B6460975
theorem B22972355 : Blo 1989435 22972355 := bstep (se 1 (by rfl) ⟨17229266, by rfl⟩ : syracuseStep 22972355 = 34458533) B34458533
theorem B15314903 : Blo 1989435 15314903 := bstep (se 1 (by rfl) ⟨11486177, by rfl⟩ : syracuseStep 15314903 = 22972355) B22972355
theorem B10209935 : Blo 1989435 10209935 := bstep (se 1 (by rfl) ⟨7657451, by rfl⟩ : syracuseStep 10209935 = 15314903) B15314903
theorem B6806623 : Blo 1989435 6806623 := bstep (se 1 (by rfl) ⟨5104967, by rfl⟩ : syracuseStep 6806623 = 10209935) B10209935
theorem B9075497 : Blo 1989435 9075497 := bstep (se 2 (by rfl) ⟨3403311, by rfl⟩ : syracuseStep 9075497 = 6806623) B6806623
theorem B24201325 : Blo 1989435 24201325 := bstep (se 3 (by rfl) ⟨4537748, by rfl⟩ : syracuseStep 24201325 = 9075497) B9075497
theorem B129073733 : Blo 1989435 129073733 := bstep (se 4 (by rfl) ⟨12100662, by rfl⟩ : syracuseStep 129073733 = 24201325) B24201325
theorem B86049155 : Blo 1989435 86049155 := bstep (se 1 (by rfl) ⟨64536866, by rfl⟩ : syracuseStep 86049155 = 129073733) B129073733
theorem B57366103 : Blo 1989435 57366103 := bstep (se 1 (by rfl) ⟨43024577, by rfl⟩ : syracuseStep 57366103 = 86049155) B86049155
theorem B76488137 : Blo 1989435 76488137 := bstep (se 2 (by rfl) ⟨28683051, by rfl⟩ : syracuseStep 76488137 = 57366103) B57366103
theorem B50992091 : Blo 1989435 50992091 := bstep (se 1 (by rfl) ⟨38244068, by rfl⟩ : syracuseStep 50992091 = 76488137) B76488137
theorem B33994727 : Blo 1989435 33994727 := bstep (se 1 (by rfl) ⟨25496045, by rfl⟩ : syracuseStep 33994727 = 50992091) B50992091
theorem B22663151 : Blo 1989435 22663151 := bstep (se 1 (by rfl) ⟨16997363, by rfl⟩ : syracuseStep 22663151 = 33994727) B33994727
theorem B15108767 : Blo 1989435 15108767 := bstep (se 1 (by rfl) ⟨11331575, by rfl⟩ : syracuseStep 15108767 = 22663151) B22663151
theorem B10072511 : Blo 1989435 10072511 := bstep (se 1 (by rfl) ⟨7554383, by rfl⟩ : syracuseStep 10072511 = 15108767) B15108767
theorem B6715007 : Blo 1989435 6715007 := bstep (se 1 (by rfl) ⟨5036255, by rfl⟩ : syracuseStep 6715007 = 10072511) B10072511
theorem B4476671 : Blo 1989435 4476671 := bstep (se 1 (by rfl) ⟨3357503, by rfl⟩ : syracuseStep 4476671 = 6715007) B6715007
theorem B2984447 : Blo 1989435 2984447 := bstep (se 1 (by rfl) ⟨2238335, by rfl⟩ : syracuseStep 2984447 = 4476671) B4476671
theorem B1989631 : Blo 1989435 1989631 := bstep (se 1 (by rfl) ⟨1492223, by rfl⟩ : syracuseStep 1989631 = 2984447) B2984447
theorem B2984453 : Blo 1989435 2984453 := bbase (se 4 (by rfl) ⟨279792, by rfl⟩ : syracuseStep 2984453 = 559585) (by norm_num)
theorem B1989635 : Blo 1989435 1989635 := bstep (se 1 (by rfl) ⟨1492226, by rfl⟩ : syracuseStep 1989635 = 2984453) B2984453
theorem B3357517 : Blo 1989435 3357517 := bbase (se 3 (by rfl) ⟨629534, by rfl⟩ : syracuseStep 3357517 = 1259069) (by norm_num)
theorem B4476689 : Blo 1989435 4476689 := bstep (se 2 (by rfl) ⟨1678758, by rfl⟩ : syracuseStep 4476689 = 3357517) B3357517
theorem B2984459 : Blo 1989435 2984459 := bstep (se 1 (by rfl) ⟨2238344, by rfl⟩ : syracuseStep 2984459 = 4476689) B4476689
theorem B1989639 : Blo 1989435 1989639 := bstep (se 1 (by rfl) ⟨1492229, by rfl⟩ : syracuseStep 1989639 = 2984459) B2984459
theorem B2238349 : Blo 1989435 2238349 := bbase (se 3 (by rfl) ⟨419690, by rfl⟩ : syracuseStep 2238349 = 839381) (by norm_num)
theorem B2984465 : Blo 1989435 2984465 := bstep (se 2 (by rfl) ⟨1119174, by rfl⟩ : syracuseStep 2984465 = 2238349) B2238349
theorem B1989643 : Blo 1989435 1989643 := bstep (se 1 (by rfl) ⟨1492232, by rfl⟩ : syracuseStep 1989643 = 2984465) B2984465
theorem B6715061 : Blo 1989435 6715061 := bbase (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) (by norm_num)
theorem B4476707 : Blo 1989435 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B2984471 : Blo 1989435 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B1989647 : Blo 1989435 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B2984477 : Blo 1989435 2984477 := bbase (se 3 (by rfl) ⟨559589, by rfl⟩ : syracuseStep 2984477 = 1119179) (by norm_num)
theorem B1989651 : Blo 1989435 1989651 := bstep (se 1 (by rfl) ⟨1492238, by rfl⟩ : syracuseStep 1989651 = 2984477) B2984477
theorem B4476725 : Blo 1989435 4476725 := bbase (se 5 (by rfl) ⟨209846, by rfl⟩ : syracuseStep 4476725 = 419693) (by norm_num)
theorem B2984483 : Blo 1989435 2984483 := bstep (se 1 (by rfl) ⟨2238362, by rfl⟩ : syracuseStep 2984483 = 4476725) B4476725
theorem B1989655 : Blo 1989435 1989655 := bstep (se 1 (by rfl) ⟨1492241, by rfl⟩ : syracuseStep 1989655 = 2984483) B2984483
theorem B4033613 : Blo 1989435 4033613 := bbase (se 3 (by rfl) ⟨756302, by rfl⟩ : syracuseStep 4033613 = 1512605) (by norm_num)
theorem B2689075 : Blo 1989435 2689075 := bstep (se 1 (by rfl) ⟨2016806, by rfl⟩ : syracuseStep 2689075 = 4033613) B4033613
theorem B3585433 : Blo 1989435 3585433 := bstep (se 2 (by rfl) ⟨1344537, by rfl⟩ : syracuseStep 3585433 = 2689075) B2689075
theorem B4780577 : Blo 1989435 4780577 := bstep (se 2 (by rfl) ⟨1792716, by rfl⟩ : syracuseStep 4780577 = 3585433) B3585433
theorem B12748205 : Blo 1989435 12748205 := bstep (se 3 (by rfl) ⟨2390288, by rfl⟩ : syracuseStep 12748205 = 4780577) B4780577
theorem B8498803 : Blo 1989435 8498803 := bstep (se 1 (by rfl) ⟨6374102, by rfl⟩ : syracuseStep 8498803 = 12748205) B12748205
theorem B11331737 : Blo 1989435 11331737 := bstep (se 2 (by rfl) ⟨4249401, by rfl⟩ : syracuseStep 11331737 = 8498803) B8498803
theorem B7554491 : Blo 1989435 7554491 := bstep (se 1 (by rfl) ⟨5665868, by rfl⟩ : syracuseStep 7554491 = 11331737) B11331737
theorem B5036327 : Blo 1989435 5036327 := bstep (se 1 (by rfl) ⟨3777245, by rfl⟩ : syracuseStep 5036327 = 7554491) B7554491
theorem B3357551 : Blo 1989435 3357551 := bstep (se 1 (by rfl) ⟨2518163, by rfl⟩ : syracuseStep 3357551 = 5036327) B5036327
theorem B2238367 : Blo 1989435 2238367 := bstep (se 1 (by rfl) ⟨1678775, by rfl⟩ : syracuseStep 2238367 = 3357551) B3357551
theorem B2984489 : Blo 1989435 2984489 := bstep (se 2 (by rfl) ⟨1119183, by rfl⟩ : syracuseStep 2984489 = 2238367) B2238367
theorem B1989659 : Blo 1989435 1989659 := bstep (se 1 (by rfl) ⟨1492244, by rfl⟩ : syracuseStep 1989659 = 2984489) B2984489
theorem B2390293 : Blo 1989435 2390293 := bbase (se 6 (by rfl) ⟨56022, by rfl⟩ : syracuseStep 2390293 = 112045) (by norm_num)
theorem B12748229 : Blo 1989435 12748229 := bstep (se 4 (by rfl) ⟨1195146, by rfl⟩ : syracuseStep 12748229 = 2390293) B2390293
theorem B8498819 : Blo 1989435 8498819 := bstep (se 1 (by rfl) ⟨6374114, by rfl⟩ : syracuseStep 8498819 = 12748229) B12748229
theorem B5665879 : Blo 1989435 5665879 := bstep (se 1 (by rfl) ⟨4249409, by rfl⟩ : syracuseStep 5665879 = 8498819) B8498819
theorem B7554505 : Blo 1989435 7554505 := bstep (se 2 (by rfl) ⟨2832939, by rfl⟩ : syracuseStep 7554505 = 5665879) B5665879
theorem B10072673 : Blo 1989435 10072673 := bstep (se 2 (by rfl) ⟨3777252, by rfl⟩ : syracuseStep 10072673 = 7554505) B7554505
theorem B6715115 : Blo 1989435 6715115 := bstep (se 1 (by rfl) ⟨5036336, by rfl⟩ : syracuseStep 6715115 = 10072673) B10072673
theorem B4476743 : Blo 1989435 4476743 := bstep (se 1 (by rfl) ⟨3357557, by rfl⟩ : syracuseStep 4476743 = 6715115) B6715115
theorem B2984495 : Blo 1989435 2984495 := bstep (se 1 (by rfl) ⟨2238371, by rfl⟩ : syracuseStep 2984495 = 4476743) B4476743
theorem B1989663 : Blo 1989435 1989663 := bstep (se 1 (by rfl) ⟨1492247, by rfl⟩ : syracuseStep 1989663 = 2984495) B2984495
theorem B2984501 : Blo 1989435 2984501 := bbase (se 5 (by rfl) ⟨139898, by rfl⟩ : syracuseStep 2984501 = 279797) (by norm_num)
theorem B1989667 : Blo 1989435 1989667 := bstep (se 1 (by rfl) ⟨1492250, by rfl⟩ : syracuseStep 1989667 = 2984501) B2984501
theorem B5036357 : Blo 1989435 5036357 := bbase (se 4 (by rfl) ⟨472158, by rfl⟩ : syracuseStep 5036357 = 944317) (by norm_num)
theorem B3357571 : Blo 1989435 3357571 := bstep (se 1 (by rfl) ⟨2518178, by rfl⟩ : syracuseStep 3357571 = 5036357) B5036357
theorem B4476761 : Blo 1989435 4476761 := bstep (se 2 (by rfl) ⟨1678785, by rfl⟩ : syracuseStep 4476761 = 3357571) B3357571
theorem B2984507 : Blo 1989435 2984507 := bstep (se 1 (by rfl) ⟨2238380, by rfl⟩ : syracuseStep 2984507 = 4476761) B4476761
theorem B1989671 : Blo 1989435 1989671 := bstep (se 1 (by rfl) ⟨1492253, by rfl⟩ : syracuseStep 1989671 = 2984507) B2984507
theorem B2238385 : Blo 1989435 2238385 := bbase (se 2 (by rfl) ⟨839394, by rfl⟩ : syracuseStep 2238385 = 1678789) (by norm_num)
theorem B2984513 : Blo 1989435 2984513 := bstep (se 2 (by rfl) ⟨1119192, by rfl⟩ : syracuseStep 2984513 = 2238385) B2238385
theorem B1989675 : Blo 1989435 1989675 := bstep (se 1 (by rfl) ⟨1492256, by rfl⟩ : syracuseStep 1989675 = 2984513) B2984513
theorem B5665925 : Blo 1989435 5665925 := bbase (se 4 (by rfl) ⟨531180, by rfl⟩ : syracuseStep 5665925 = 1062361) (by norm_num)
theorem B3777283 : Blo 1989435 3777283 := bstep (se 1 (by rfl) ⟨2832962, by rfl⟩ : syracuseStep 3777283 = 5665925) B5665925
theorem B5036377 : Blo 1989435 5036377 := bstep (se 2 (by rfl) ⟨1888641, by rfl⟩ : syracuseStep 5036377 = 3777283) B3777283
theorem B6715169 : Blo 1989435 6715169 := bstep (se 2 (by rfl) ⟨2518188, by rfl⟩ : syracuseStep 6715169 = 5036377) B5036377
theorem B4476779 : Blo 1989435 4476779 := bstep (se 1 (by rfl) ⟨3357584, by rfl⟩ : syracuseStep 4476779 = 6715169) B6715169
theorem B2984519 : Blo 1989435 2984519 := bstep (se 1 (by rfl) ⟨2238389, by rfl⟩ : syracuseStep 2984519 = 4476779) B4476779
theorem B1989679 : Blo 1989435 1989679 := bstep (se 1 (by rfl) ⟨1492259, by rfl⟩ : syracuseStep 1989679 = 2984519) B2984519
theorem B2984525 : Blo 1989435 2984525 := bbase (se 3 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 2984525 = 1119197) (by norm_num)
theorem B1989683 : Blo 1989435 1989683 := bstep (se 1 (by rfl) ⟨1492262, by rfl⟩ : syracuseStep 1989683 = 2984525) B2984525
theorem B4476797 : Blo 1989435 4476797 := bbase (se 3 (by rfl) ⟨839399, by rfl⟩ : syracuseStep 4476797 = 1678799) (by norm_num)
theorem B2984531 : Blo 1989435 2984531 := bstep (se 1 (by rfl) ⟨2238398, by rfl⟩ : syracuseStep 2984531 = 4476797) B4476797
theorem B1989687 : Blo 1989435 1989687 := bstep (se 1 (by rfl) ⟨1492265, by rfl⟩ : syracuseStep 1989687 = 2984531) B2984531
theorem B3357605 : Blo 1989435 3357605 := bbase (se 4 (by rfl) ⟨314775, by rfl⟩ : syracuseStep 3357605 = 629551) (by norm_num)
theorem B2238403 : Blo 1989435 2238403 := bstep (se 1 (by rfl) ⟨1678802, by rfl⟩ : syracuseStep 2238403 = 3357605) B3357605
theorem B2984537 : Blo 1989435 2984537 := bstep (se 2 (by rfl) ⟨1119201, by rfl⟩ : syracuseStep 2984537 = 2238403) B2238403
theorem B1989691 : Blo 1989435 1989691 := bstep (se 1 (by rfl) ⟨1492268, by rfl⟩ : syracuseStep 1989691 = 2984537) B2984537
theorem B3187109 : Blo 1989435 3187109 := bbase (se 4 (by rfl) ⟨298791, by rfl⟩ : syracuseStep 3187109 = 597583) (by norm_num)
theorem B2124739 : Blo 1989435 2124739 := bstep (se 1 (by rfl) ⟨1593554, by rfl⟩ : syracuseStep 2124739 = 3187109) B3187109
theorem B2832985 : Blo 1989435 2832985 := bstep (se 2 (by rfl) ⟨1062369, by rfl⟩ : syracuseStep 2832985 = 2124739) B2124739
theorem B15109253 : Blo 1989435 15109253 := bstep (se 4 (by rfl) ⟨1416492, by rfl⟩ : syracuseStep 15109253 = 2832985) B2832985
theorem B10072835 : Blo 1989435 10072835 := bstep (se 1 (by rfl) ⟨7554626, by rfl⟩ : syracuseStep 10072835 = 15109253) B15109253
theorem B6715223 : Blo 1989435 6715223 := bstep (se 1 (by rfl) ⟨5036417, by rfl⟩ : syracuseStep 6715223 = 10072835) B10072835
theorem B4476815 : Blo 1989435 4476815 := bstep (se 1 (by rfl) ⟨3357611, by rfl⟩ : syracuseStep 4476815 = 6715223) B6715223
theorem B2984543 : Blo 1989435 2984543 := bstep (se 1 (by rfl) ⟨2238407, by rfl⟩ : syracuseStep 2984543 = 4476815) B4476815
theorem B1989695 : Blo 1989435 1989695 := bstep (se 1 (by rfl) ⟨1492271, by rfl⟩ : syracuseStep 1989695 = 2984543) B2984543
theorem B2984549 : Blo 1989435 2984549 := bbase (se 4 (by rfl) ⟨279801, by rfl⟩ : syracuseStep 2984549 = 559603) (by norm_num)
theorem B1989699 : Blo 1989435 1989699 := bstep (se 1 (by rfl) ⟨1492274, by rfl⟩ : syracuseStep 1989699 = 2984549) B2984549
theorem B2832997 : Blo 1989435 2832997 := bbase (se 4 (by rfl) ⟨265593, by rfl⟩ : syracuseStep 2832997 = 531187) (by norm_num)
theorem B3777329 : Blo 1989435 3777329 := bstep (se 2 (by rfl) ⟨1416498, by rfl⟩ : syracuseStep 3777329 = 2832997) B2832997
theorem B2518219 : Blo 1989435 2518219 := bstep (se 1 (by rfl) ⟨1888664, by rfl⟩ : syracuseStep 2518219 = 3777329) B3777329
theorem B3357625 : Blo 1989435 3357625 := bstep (se 2 (by rfl) ⟨1259109, by rfl⟩ : syracuseStep 3357625 = 2518219) B2518219
theorem B4476833 : Blo 1989435 4476833 := bstep (se 2 (by rfl) ⟨1678812, by rfl⟩ : syracuseStep 4476833 = 3357625) B3357625
theorem B2984555 : Blo 1989435 2984555 := bstep (se 1 (by rfl) ⟨2238416, by rfl⟩ : syracuseStep 2984555 = 4476833) B4476833
theorem B1989703 : Blo 1989435 1989703 := bstep (se 1 (by rfl) ⟨1492277, by rfl⟩ : syracuseStep 1989703 = 2984555) B2984555
theorem B2238421 : Blo 1989435 2238421 := bbase (se 7 (by rfl) ⟨26231, by rfl⟩ : syracuseStep 2238421 = 52463) (by norm_num)
theorem B2984561 : Blo 1989435 2984561 := bstep (se 2 (by rfl) ⟨1119210, by rfl⟩ : syracuseStep 2984561 = 2238421) B2238421
theorem B1989707 : Blo 1989435 1989707 := bstep (se 1 (by rfl) ⟨1492280, by rfl⟩ : syracuseStep 1989707 = 2984561) B2984561
theorem B2518229 : Blo 1989435 2518229 := bbase (se 7 (by rfl) ⟨29510, by rfl⟩ : syracuseStep 2518229 = 59021) (by norm_num)
theorem B6715277 : Blo 1989435 6715277 := bstep (se 3 (by rfl) ⟨1259114, by rfl⟩ : syracuseStep 6715277 = 2518229) B2518229
theorem B4476851 : Blo 1989435 4476851 := bstep (se 1 (by rfl) ⟨3357638, by rfl⟩ : syracuseStep 4476851 = 6715277) B6715277
theorem B2984567 : Blo 1989435 2984567 := bstep (se 1 (by rfl) ⟨2238425, by rfl⟩ : syracuseStep 2984567 = 4476851) B4476851
theorem B1989711 : Blo 1989435 1989711 := bstep (se 1 (by rfl) ⟨1492283, by rfl⟩ : syracuseStep 1989711 = 2984567) B2984567
theorem B2984573 : Blo 1989435 2984573 := bbase (se 3 (by rfl) ⟨559607, by rfl⟩ : syracuseStep 2984573 = 1119215) (by norm_num)
theorem B1989715 : Blo 1989435 1989715 := bstep (se 1 (by rfl) ⟨1492286, by rfl⟩ : syracuseStep 1989715 = 2984573) B2984573
theorem B4476869 : Blo 1989435 4476869 := bbase (se 4 (by rfl) ⟨419706, by rfl⟩ : syracuseStep 4476869 = 839413) (by norm_num)
theorem B2984579 : Blo 1989435 2984579 := bstep (se 1 (by rfl) ⟨2238434, by rfl⟩ : syracuseStep 2984579 = 4476869) B4476869
theorem B1989719 : Blo 1989435 1989719 := bstep (se 1 (by rfl) ⟨1492289, by rfl⟩ : syracuseStep 1989719 = 2984579) B2984579
theorem B8499077 : Blo 1989435 8499077 := bbase (se 4 (by rfl) ⟨796788, by rfl⟩ : syracuseStep 8499077 = 1593577) (by norm_num)
theorem B5666051 : Blo 1989435 5666051 := bstep (se 1 (by rfl) ⟨4249538, by rfl⟩ : syracuseStep 5666051 = 8499077) B8499077
theorem B3777367 : Blo 1989435 3777367 := bstep (se 1 (by rfl) ⟨2833025, by rfl⟩ : syracuseStep 3777367 = 5666051) B5666051
theorem B5036489 : Blo 1989435 5036489 := bstep (se 2 (by rfl) ⟨1888683, by rfl⟩ : syracuseStep 5036489 = 3777367) B3777367
theorem B3357659 : Blo 1989435 3357659 := bstep (se 1 (by rfl) ⟨2518244, by rfl⟩ : syracuseStep 3357659 = 5036489) B5036489
theorem B2238439 : Blo 1989435 2238439 := bstep (se 1 (by rfl) ⟨1678829, by rfl⟩ : syracuseStep 2238439 = 3357659) B3357659
theorem B2984585 : Blo 1989435 2984585 := bstep (se 2 (by rfl) ⟨1119219, by rfl⟩ : syracuseStep 2984585 = 2238439) B2238439
theorem B1989723 : Blo 1989435 1989723 := bstep (se 1 (by rfl) ⟨1492292, by rfl⟩ : syracuseStep 1989723 = 2984585) B2984585
theorem B10072997 : Blo 1989435 10072997 := bbase (se 4 (by rfl) ⟨944343, by rfl⟩ : syracuseStep 10072997 = 1888687) (by norm_num)
theorem B6715331 : Blo 1989435 6715331 := bstep (se 1 (by rfl) ⟨5036498, by rfl⟩ : syracuseStep 6715331 = 10072997) B10072997
theorem B4476887 : Blo 1989435 4476887 := bstep (se 1 (by rfl) ⟨3357665, by rfl⟩ : syracuseStep 4476887 = 6715331) B6715331
theorem B2984591 : Blo 1989435 2984591 := bstep (se 1 (by rfl) ⟨2238443, by rfl⟩ : syracuseStep 2984591 = 4476887) B4476887
theorem B1989727 : Blo 1989435 1989727 := bstep (se 1 (by rfl) ⟨1492295, by rfl⟩ : syracuseStep 1989727 = 2984591) B2984591
theorem B2984597 : Blo 1989435 2984597 := bbase (se 6 (by rfl) ⟨69951, by rfl⟩ : syracuseStep 2984597 = 139903) (by norm_num)
theorem B1989731 : Blo 1989435 1989731 := bstep (se 1 (by rfl) ⟨1492298, by rfl⟩ : syracuseStep 1989731 = 2984597) B2984597
theorem B3025325 : Blo 1989435 3025325 := bbase (se 3 (by rfl) ⟨567248, by rfl⟩ : syracuseStep 3025325 = 1134497) (by norm_num)
theorem B2016883 : Blo 1989435 2016883 := bstep (se 1 (by rfl) ⟨1512662, by rfl⟩ : syracuseStep 2016883 = 3025325) B3025325
theorem B10756709 : Blo 1989435 10756709 := bstep (se 4 (by rfl) ⟨1008441, by rfl⟩ : syracuseStep 10756709 = 2016883) B2016883
theorem B7171139 : Blo 1989435 7171139 := bstep (se 1 (by rfl) ⟨5378354, by rfl⟩ : syracuseStep 7171139 = 10756709) B10756709
theorem B19123037 : Blo 1989435 19123037 := bstep (se 3 (by rfl) ⟨3585569, by rfl⟩ : syracuseStep 19123037 = 7171139) B7171139
theorem B12748691 : Blo 1989435 12748691 := bstep (se 1 (by rfl) ⟨9561518, by rfl⟩ : syracuseStep 12748691 = 19123037) B19123037
theorem B8499127 : Blo 1989435 8499127 := bstep (se 1 (by rfl) ⟨6374345, by rfl⟩ : syracuseStep 8499127 = 12748691) B12748691
theorem B11332169 : Blo 1989435 11332169 := bstep (se 2 (by rfl) ⟨4249563, by rfl⟩ : syracuseStep 11332169 = 8499127) B8499127
theorem B7554779 : Blo 1989435 7554779 := bstep (se 1 (by rfl) ⟨5666084, by rfl⟩ : syracuseStep 7554779 = 11332169) B11332169
theorem B5036519 : Blo 1989435 5036519 := bstep (se 1 (by rfl) ⟨3777389, by rfl⟩ : syracuseStep 5036519 = 7554779) B7554779
theorem B3357679 : Blo 1989435 3357679 := bstep (se 1 (by rfl) ⟨2518259, by rfl⟩ : syracuseStep 3357679 = 5036519) B5036519
theorem B4476905 : Blo 1989435 4476905 := bstep (se 2 (by rfl) ⟨1678839, by rfl⟩ : syracuseStep 4476905 = 3357679) B3357679
theorem B2984603 : Blo 1989435 2984603 := bstep (se 1 (by rfl) ⟨2238452, by rfl⟩ : syracuseStep 2984603 = 4476905) B4476905
theorem B1989735 : Blo 1989435 1989735 := bstep (se 1 (by rfl) ⟨1492301, by rfl⟩ : syracuseStep 1989735 = 2984603) B2984603
theorem B2238457 : Blo 1989435 2238457 := bbase (se 2 (by rfl) ⟨839421, by rfl⟩ : syracuseStep 2238457 = 1678843) (by norm_num)
theorem B2984609 : Blo 1989435 2984609 := bstep (se 2 (by rfl) ⟨1119228, by rfl⟩ : syracuseStep 2984609 = 2238457) B2238457
theorem B1989739 : Blo 1989435 1989739 := bstep (se 1 (by rfl) ⟨1492304, by rfl⟩ : syracuseStep 1989739 = 2984609) B2984609
theorem B9561557 : Blo 1989435 9561557 := bbase (se 7 (by rfl) ⟨112049, by rfl⟩ : syracuseStep 9561557 = 224099) (by norm_num)
theorem B6374371 : Blo 1989435 6374371 := bstep (se 1 (by rfl) ⟨4780778, by rfl⟩ : syracuseStep 6374371 = 9561557) B9561557
theorem B8499161 : Blo 1989435 8499161 := bstep (se 2 (by rfl) ⟨3187185, by rfl⟩ : syracuseStep 8499161 = 6374371) B6374371
theorem B5666107 : Blo 1989435 5666107 := bstep (se 1 (by rfl) ⟨4249580, by rfl⟩ : syracuseStep 5666107 = 8499161) B8499161
theorem B7554809 : Blo 1989435 7554809 := bstep (se 2 (by rfl) ⟨2833053, by rfl⟩ : syracuseStep 7554809 = 5666107) B5666107
theorem B5036539 : Blo 1989435 5036539 := bstep (se 1 (by rfl) ⟨3777404, by rfl⟩ : syracuseStep 5036539 = 7554809) B7554809
theorem B6715385 : Blo 1989435 6715385 := bstep (se 2 (by rfl) ⟨2518269, by rfl⟩ : syracuseStep 6715385 = 5036539) B5036539
theorem B4476923 : Blo 1989435 4476923 := bstep (se 1 (by rfl) ⟨3357692, by rfl⟩ : syracuseStep 4476923 = 6715385) B6715385
theorem B2984615 : Blo 1989435 2984615 := bstep (se 1 (by rfl) ⟨2238461, by rfl⟩ : syracuseStep 2984615 = 4476923) B4476923
theorem B1989743 : Blo 1989435 1989743 := bstep (se 1 (by rfl) ⟨1492307, by rfl⟩ : syracuseStep 1989743 = 2984615) B2984615
theorem B2984621 : Blo 1989435 2984621 := bbase (se 3 (by rfl) ⟨559616, by rfl⟩ : syracuseStep 2984621 = 1119233) (by norm_num)
theorem B1989747 : Blo 1989435 1989747 := bstep (se 1 (by rfl) ⟨1492310, by rfl⟩ : syracuseStep 1989747 = 2984621) B2984621
theorem B4476941 : Blo 1989435 4476941 := bbase (se 3 (by rfl) ⟨839426, by rfl⟩ : syracuseStep 4476941 = 1678853) (by norm_num)
theorem B2984627 : Blo 1989435 2984627 := bstep (se 1 (by rfl) ⟨2238470, by rfl⟩ : syracuseStep 2984627 = 4476941) B4476941
theorem B1989751 : Blo 1989435 1989751 := bstep (se 1 (by rfl) ⟨1492313, by rfl⟩ : syracuseStep 1989751 = 2984627) B2984627
theorem B2518285 : Blo 1989435 2518285 := bbase (se 3 (by rfl) ⟨472178, by rfl⟩ : syracuseStep 2518285 = 944357) (by norm_num)
theorem B3357713 : Blo 1989435 3357713 := bstep (se 2 (by rfl) ⟨1259142, by rfl⟩ : syracuseStep 3357713 = 2518285) B2518285
theorem B2238475 : Blo 1989435 2238475 := bstep (se 1 (by rfl) ⟨1678856, by rfl⟩ : syracuseStep 2238475 = 3357713) B3357713
theorem B2984633 : Blo 1989435 2984633 := bstep (se 2 (by rfl) ⟨1119237, by rfl⟩ : syracuseStep 2984633 = 2238475) B2238475
theorem B1989755 : Blo 1989435 1989755 := bstep (se 1 (by rfl) ⟨1492316, by rfl⟩ : syracuseStep 1989755 = 2984633) B2984633
theorem B2269021 : Blo 1989435 2269021 := bbase (se 3 (by rfl) ⟨425441, by rfl⟩ : syracuseStep 2269021 = 850883) (by norm_num)
theorem B3025361 : Blo 1989435 3025361 := bstep (se 2 (by rfl) ⟨1134510, by rfl⟩ : syracuseStep 3025361 = 2269021) B2269021
theorem B2016907 : Blo 1989435 2016907 := bstep (se 1 (by rfl) ⟨1512680, by rfl⟩ : syracuseStep 2016907 = 3025361) B3025361
theorem B10756837 : Blo 1989435 10756837 := bstep (se 4 (by rfl) ⟨1008453, by rfl⟩ : syracuseStep 10756837 = 2016907) B2016907
theorem B14342449 : Blo 1989435 14342449 := bstep (se 2 (by rfl) ⟨5378418, by rfl⟩ : syracuseStep 14342449 = 10756837) B10756837
theorem B19123265 : Blo 1989435 19123265 := bstep (se 2 (by rfl) ⟨7171224, by rfl⟩ : syracuseStep 19123265 = 14342449) B14342449
theorem B12748843 : Blo 1989435 12748843 := bstep (se 1 (by rfl) ⟨9561632, by rfl⟩ : syracuseStep 12748843 = 19123265) B19123265
theorem B16998457 : Blo 1989435 16998457 := bstep (se 2 (by rfl) ⟨6374421, by rfl⟩ : syracuseStep 16998457 = 12748843) B12748843
theorem B22664609 : Blo 1989435 22664609 := bstep (se 2 (by rfl) ⟨8499228, by rfl⟩ : syracuseStep 22664609 = 16998457) B16998457
theorem B15109739 : Blo 1989435 15109739 := bstep (se 1 (by rfl) ⟨11332304, by rfl⟩ : syracuseStep 15109739 = 22664609) B22664609
theorem B10073159 : Blo 1989435 10073159 := bstep (se 1 (by rfl) ⟨7554869, by rfl⟩ : syracuseStep 10073159 = 15109739) B15109739
theorem B6715439 : Blo 1989435 6715439 := bstep (se 1 (by rfl) ⟨5036579, by rfl⟩ : syracuseStep 6715439 = 10073159) B10073159
theorem B4476959 : Blo 1989435 4476959 := bstep (se 1 (by rfl) ⟨3357719, by rfl⟩ : syracuseStep 4476959 = 6715439) B6715439
theorem B2984639 : Blo 1989435 2984639 := bstep (se 1 (by rfl) ⟨2238479, by rfl⟩ : syracuseStep 2984639 = 4476959) B4476959
theorem B1989759 : Blo 1989435 1989759 := bstep (se 1 (by rfl) ⟨1492319, by rfl⟩ : syracuseStep 1989759 = 2984639) B2984639
theorem B2984645 : Blo 1989435 2984645 := bbase (se 4 (by rfl) ⟨279810, by rfl⟩ : syracuseStep 2984645 = 559621) (by norm_num)
theorem B1989763 : Blo 1989435 1989763 := bstep (se 1 (by rfl) ⟨1492322, by rfl⟩ : syracuseStep 1989763 = 2984645) B2984645
theorem B3357733 : Blo 1989435 3357733 := bbase (se 4 (by rfl) ⟨314787, by rfl⟩ : syracuseStep 3357733 = 629575) (by norm_num)
theorem B4476977 : Blo 1989435 4476977 := bstep (se 2 (by rfl) ⟨1678866, by rfl⟩ : syracuseStep 4476977 = 3357733) B3357733
theorem B2984651 : Blo 1989435 2984651 := bstep (se 1 (by rfl) ⟨2238488, by rfl⟩ : syracuseStep 2984651 = 4476977) B4476977
theorem B1989767 : Blo 1989435 1989767 := bstep (se 1 (by rfl) ⟨1492325, by rfl⟩ : syracuseStep 1989767 = 2984651) B2984651
theorem B2238493 : Blo 1989435 2238493 := bbase (se 3 (by rfl) ⟨419717, by rfl⟩ : syracuseStep 2238493 = 839435) (by norm_num)
theorem B2984657 : Blo 1989435 2984657 := bstep (se 2 (by rfl) ⟨1119246, by rfl⟩ : syracuseStep 2984657 = 2238493) B2238493
theorem B1989771 : Blo 1989435 1989771 := bstep (se 1 (by rfl) ⟨1492328, by rfl⟩ : syracuseStep 1989771 = 2984657) B2984657
theorem B6715493 : Blo 1989435 6715493 := bbase (se 4 (by rfl) ⟨629577, by rfl⟩ : syracuseStep 6715493 = 1259155) (by norm_num)
theorem B4476995 : Blo 1989435 4476995 := bstep (se 1 (by rfl) ⟨3357746, by rfl⟩ : syracuseStep 4476995 = 6715493) B6715493
theorem B2984663 : Blo 1989435 2984663 := bstep (se 1 (by rfl) ⟨2238497, by rfl⟩ : syracuseStep 2984663 = 4476995) B4476995
theorem B1989775 : Blo 1989435 1989775 := bstep (se 1 (by rfl) ⟨1492331, by rfl⟩ : syracuseStep 1989775 = 2984663) B2984663
theorem B2984669 : Blo 1989435 2984669 := bbase (se 3 (by rfl) ⟨559625, by rfl⟩ : syracuseStep 2984669 = 1119251) (by norm_num)
theorem B1989779 : Blo 1989435 1989779 := bstep (se 1 (by rfl) ⟨1492334, by rfl⟩ : syracuseStep 1989779 = 2984669) B2984669
theorem B4477013 : Blo 1989435 4477013 := bbase (se 8 (by rfl) ⟨26232, by rfl⟩ : syracuseStep 4477013 = 52465) (by norm_num)
theorem B2984675 : Blo 1989435 2984675 := bstep (se 1 (by rfl) ⟨2238506, by rfl⟩ : syracuseStep 2984675 = 4477013) B4477013
theorem B1989783 : Blo 1989435 1989783 := bstep (se 1 (by rfl) ⟨1492337, by rfl⟩ : syracuseStep 1989783 = 2984675) B2984675
theorem B4780885 : Blo 1989435 4780885 := bbase (se 9 (by rfl) ⟨14006, by rfl⟩ : syracuseStep 4780885 = 28013) (by norm_num)
theorem B6374513 : Blo 1989435 6374513 := bstep (se 2 (by rfl) ⟨2390442, by rfl⟩ : syracuseStep 6374513 = 4780885) B4780885
theorem B4249675 : Blo 1989435 4249675 := bstep (se 1 (by rfl) ⟨3187256, by rfl⟩ : syracuseStep 4249675 = 6374513) B6374513
theorem B5666233 : Blo 1989435 5666233 := bstep (se 2 (by rfl) ⟨2124837, by rfl⟩ : syracuseStep 5666233 = 4249675) B4249675
theorem B7554977 : Blo 1989435 7554977 := bstep (se 2 (by rfl) ⟨2833116, by rfl⟩ : syracuseStep 7554977 = 5666233) B5666233
theorem B5036651 : Blo 1989435 5036651 := bstep (se 1 (by rfl) ⟨3777488, by rfl⟩ : syracuseStep 5036651 = 7554977) B7554977
theorem B3357767 : Blo 1989435 3357767 := bstep (se 1 (by rfl) ⟨2518325, by rfl⟩ : syracuseStep 3357767 = 5036651) B5036651
theorem B2238511 : Blo 1989435 2238511 := bstep (se 1 (by rfl) ⟨1678883, by rfl⟩ : syracuseStep 2238511 = 3357767) B3357767
theorem B2984681 : Blo 1989435 2984681 := bstep (se 2 (by rfl) ⟨1119255, by rfl⟩ : syracuseStep 2984681 = 2238511) B2238511
theorem B1989787 : Blo 1989435 1989787 := bstep (se 1 (by rfl) ⟨1492340, by rfl⟩ : syracuseStep 1989787 = 2984681) B2984681
theorem B19123573 : Blo 1989435 19123573 := bbase (se 5 (by rfl) ⟨896417, by rfl⟩ : syracuseStep 19123573 = 1792835) (by norm_num)
theorem B25498097 : Blo 1989435 25498097 := bstep (se 2 (by rfl) ⟨9561786, by rfl⟩ : syracuseStep 25498097 = 19123573) B19123573
theorem B16998731 : Blo 1989435 16998731 := bstep (se 1 (by rfl) ⟨12749048, by rfl⟩ : syracuseStep 16998731 = 25498097) B25498097
theorem B11332487 : Blo 1989435 11332487 := bstep (se 1 (by rfl) ⟨8499365, by rfl⟩ : syracuseStep 11332487 = 16998731) B16998731
theorem B7554991 : Blo 1989435 7554991 := bstep (se 1 (by rfl) ⟨5666243, by rfl⟩ : syracuseStep 7554991 = 11332487) B11332487
theorem B10073321 : Blo 1989435 10073321 := bstep (se 2 (by rfl) ⟨3777495, by rfl⟩ : syracuseStep 10073321 = 7554991) B7554991
theorem B6715547 : Blo 1989435 6715547 := bstep (se 1 (by rfl) ⟨5036660, by rfl⟩ : syracuseStep 6715547 = 10073321) B10073321
theorem B4477031 : Blo 1989435 4477031 := bstep (se 1 (by rfl) ⟨3357773, by rfl⟩ : syracuseStep 4477031 = 6715547) B6715547
theorem B2984687 : Blo 1989435 2984687 := bstep (se 1 (by rfl) ⟨2238515, by rfl⟩ : syracuseStep 2984687 = 4477031) B4477031
theorem B1989791 : Blo 1989435 1989791 := bstep (se 1 (by rfl) ⟨1492343, by rfl⟩ : syracuseStep 1989791 = 2984687) B2984687
theorem B2984693 : Blo 1989435 2984693 := bbase (se 5 (by rfl) ⟨139907, by rfl⟩ : syracuseStep 2984693 = 279815) (by norm_num)
theorem B1989795 : Blo 1989435 1989795 := bstep (se 1 (by rfl) ⟨1492346, by rfl⟩ : syracuseStep 1989795 = 2984693) B2984693
theorem B14342741 : Blo 1989435 14342741 := bbase (se 8 (by rfl) ⟨84039, by rfl⟩ : syracuseStep 14342741 = 168079) (by norm_num)
theorem B9561827 : Blo 1989435 9561827 := bstep (se 1 (by rfl) ⟨7171370, by rfl⟩ : syracuseStep 9561827 = 14342741) B14342741
theorem B6374551 : Blo 1989435 6374551 := bstep (se 1 (by rfl) ⟨4780913, by rfl⟩ : syracuseStep 6374551 = 9561827) B9561827
theorem B8499401 : Blo 1989435 8499401 := bstep (se 2 (by rfl) ⟨3187275, by rfl⟩ : syracuseStep 8499401 = 6374551) B6374551
theorem B5666267 : Blo 1989435 5666267 := bstep (se 1 (by rfl) ⟨4249700, by rfl⟩ : syracuseStep 5666267 = 8499401) B8499401
theorem B3777511 : Blo 1989435 3777511 := bstep (se 1 (by rfl) ⟨2833133, by rfl⟩ : syracuseStep 3777511 = 5666267) B5666267
theorem B5036681 : Blo 1989435 5036681 := bstep (se 2 (by rfl) ⟨1888755, by rfl⟩ : syracuseStep 5036681 = 3777511) B3777511
theorem B3357787 : Blo 1989435 3357787 := bstep (se 1 (by rfl) ⟨2518340, by rfl⟩ : syracuseStep 3357787 = 5036681) B5036681
theorem B4477049 : Blo 1989435 4477049 := bstep (se 2 (by rfl) ⟨1678893, by rfl⟩ : syracuseStep 4477049 = 3357787) B3357787
theorem B2984699 : Blo 1989435 2984699 := bstep (se 1 (by rfl) ⟨2238524, by rfl⟩ : syracuseStep 2984699 = 4477049) B4477049
theorem B1989799 : Blo 1989435 1989799 := bstep (se 1 (by rfl) ⟨1492349, by rfl⟩ : syracuseStep 1989799 = 2984699) B2984699
theorem B2238529 : Blo 1989435 2238529 := bbase (se 2 (by rfl) ⟨839448, by rfl⟩ : syracuseStep 2238529 = 1678897) (by norm_num)
theorem B2984705 : Blo 1989435 2984705 := bstep (se 2 (by rfl) ⟨1119264, by rfl⟩ : syracuseStep 2984705 = 2238529) B2238529
theorem B1989803 : Blo 1989435 1989803 := bstep (se 1 (by rfl) ⟨1492352, by rfl⟩ : syracuseStep 1989803 = 2984705) B2984705
theorem B5036701 : Blo 1989435 5036701 := bbase (se 3 (by rfl) ⟨944381, by rfl⟩ : syracuseStep 5036701 = 1888763) (by norm_num)
theorem B6715601 : Blo 1989435 6715601 := bstep (se 2 (by rfl) ⟨2518350, by rfl⟩ : syracuseStep 6715601 = 5036701) B5036701
theorem B4477067 : Blo 1989435 4477067 := bstep (se 1 (by rfl) ⟨3357800, by rfl⟩ : syracuseStep 4477067 = 6715601) B6715601
theorem B2984711 : Blo 1989435 2984711 := bstep (se 1 (by rfl) ⟨2238533, by rfl⟩ : syracuseStep 2984711 = 4477067) B4477067
theorem B1989807 : Blo 1989435 1989807 := bstep (se 1 (by rfl) ⟨1492355, by rfl⟩ : syracuseStep 1989807 = 2984711) B2984711
theorem B2984717 : Blo 1989435 2984717 := bbase (se 3 (by rfl) ⟨559634, by rfl⟩ : syracuseStep 2984717 = 1119269) (by norm_num)
theorem B1989811 : Blo 1989435 1989811 := bstep (se 1 (by rfl) ⟨1492358, by rfl⟩ : syracuseStep 1989811 = 2984717) B2984717
theorem B4477085 : Blo 1989435 4477085 := bbase (se 3 (by rfl) ⟨839453, by rfl⟩ : syracuseStep 4477085 = 1678907) (by norm_num)
theorem B2984723 : Blo 1989435 2984723 := bstep (se 1 (by rfl) ⟨2238542, by rfl⟩ : syracuseStep 2984723 = 4477085) B4477085
theorem B1989815 : Blo 1989435 1989815 := bstep (se 1 (by rfl) ⟨1492361, by rfl⟩ : syracuseStep 1989815 = 2984723) B2984723
theorem B3357821 : Blo 1989435 3357821 := bbase (se 3 (by rfl) ⟨629591, by rfl⟩ : syracuseStep 3357821 = 1259183) (by norm_num)
theorem B2238547 : Blo 1989435 2238547 := bstep (se 1 (by rfl) ⟨1678910, by rfl⟩ : syracuseStep 2238547 = 3357821) B3357821
theorem B2984729 : Blo 1989435 2984729 := bstep (se 2 (by rfl) ⟨1119273, by rfl⟩ : syracuseStep 2984729 = 2238547) B2238547
theorem B1989819 : Blo 1989435 1989819 := bstep (se 1 (by rfl) ⟨1492364, by rfl⟩ : syracuseStep 1989819 = 2984729) B2984729
theorem B9561941 : Blo 1989435 9561941 := bbase (se 9 (by rfl) ⟨28013, by rfl⟩ : syracuseStep 9561941 = 56027) (by norm_num)
theorem B6374627 : Blo 1989435 6374627 := bstep (se 1 (by rfl) ⟨4780970, by rfl⟩ : syracuseStep 6374627 = 9561941) B9561941
theorem B4249751 : Blo 1989435 4249751 := bstep (se 1 (by rfl) ⟨3187313, by rfl⟩ : syracuseStep 4249751 = 6374627) B6374627
theorem B11332669 : Blo 1989435 11332669 := bstep (se 3 (by rfl) ⟨2124875, by rfl⟩ : syracuseStep 11332669 = 4249751) B4249751
theorem B15110225 : Blo 1989435 15110225 := bstep (se 2 (by rfl) ⟨5666334, by rfl⟩ : syracuseStep 15110225 = 11332669) B11332669
theorem B10073483 : Blo 1989435 10073483 := bstep (se 1 (by rfl) ⟨7555112, by rfl⟩ : syracuseStep 10073483 = 15110225) B15110225
theorem B6715655 : Blo 1989435 6715655 := bstep (se 1 (by rfl) ⟨5036741, by rfl⟩ : syracuseStep 6715655 = 10073483) B10073483
theorem B4477103 : Blo 1989435 4477103 := bstep (se 1 (by rfl) ⟨3357827, by rfl⟩ : syracuseStep 4477103 = 6715655) B6715655
theorem B2984735 : Blo 1989435 2984735 := bstep (se 1 (by rfl) ⟨2238551, by rfl⟩ : syracuseStep 2984735 = 4477103) B4477103
theorem B1989823 : Blo 1989435 1989823 := bstep (se 1 (by rfl) ⟨1492367, by rfl⟩ : syracuseStep 1989823 = 2984735) B2984735
theorem B2984741 : Blo 1989435 2984741 := bbase (se 4 (by rfl) ⟨279819, by rfl⟩ : syracuseStep 2984741 = 559639) (by norm_num)
theorem B1989827 : Blo 1989435 1989827 := bstep (se 1 (by rfl) ⟨1492370, by rfl⟩ : syracuseStep 1989827 = 2984741) B2984741
theorem B2518381 : Blo 1989435 2518381 := bbase (se 3 (by rfl) ⟨472196, by rfl⟩ : syracuseStep 2518381 = 944393) (by norm_num)
theorem B3357841 : Blo 1989435 3357841 := bstep (se 2 (by rfl) ⟨1259190, by rfl⟩ : syracuseStep 3357841 = 2518381) B2518381
theorem B4477121 : Blo 1989435 4477121 := bstep (se 2 (by rfl) ⟨1678920, by rfl⟩ : syracuseStep 4477121 = 3357841) B3357841
theorem B2984747 : Blo 1989435 2984747 := bstep (se 1 (by rfl) ⟨2238560, by rfl⟩ : syracuseStep 2984747 = 4477121) B4477121
theorem B1989831 : Blo 1989435 1989831 := bstep (se 1 (by rfl) ⟨1492373, by rfl⟩ : syracuseStep 1989831 = 2984747) B2984747
theorem B2238565 : Blo 1989435 2238565 := bbase (se 4 (by rfl) ⟨209865, by rfl⟩ : syracuseStep 2238565 = 419731) (by norm_num)
theorem B2984753 : Blo 1989435 2984753 := bstep (se 2 (by rfl) ⟨1119282, by rfl⟩ : syracuseStep 2984753 = 2238565) B2238565
theorem B1989835 : Blo 1989435 1989835 := bstep (se 1 (by rfl) ⟨1492376, by rfl⟩ : syracuseStep 1989835 = 2984753) B2984753
theorem B2124893 : Blo 1989435 2124893 := bbase (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) (by norm_num)
theorem B5666381 : Blo 1989435 5666381 := bstep (se 3 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 5666381 = 2124893) B2124893
theorem B3777587 : Blo 1989435 3777587 := bstep (se 1 (by rfl) ⟨2833190, by rfl⟩ : syracuseStep 3777587 = 5666381) B5666381
theorem B2518391 : Blo 1989435 2518391 := bstep (se 1 (by rfl) ⟨1888793, by rfl⟩ : syracuseStep 2518391 = 3777587) B3777587
theorem B6715709 : Blo 1989435 6715709 := bstep (se 3 (by rfl) ⟨1259195, by rfl⟩ : syracuseStep 6715709 = 2518391) B2518391
theorem B4477139 : Blo 1989435 4477139 := bstep (se 1 (by rfl) ⟨3357854, by rfl⟩ : syracuseStep 4477139 = 6715709) B6715709
theorem B2984759 : Blo 1989435 2984759 := bstep (se 1 (by rfl) ⟨2238569, by rfl⟩ : syracuseStep 2984759 = 4477139) B4477139
theorem B1989839 : Blo 1989435 1989839 := bstep (se 1 (by rfl) ⟨1492379, by rfl⟩ : syracuseStep 1989839 = 2984759) B2984759
theorem B2984765 : Blo 1989435 2984765 := bbase (se 3 (by rfl) ⟨559643, by rfl⟩ : syracuseStep 2984765 = 1119287) (by norm_num)
theorem B1989843 : Blo 1989435 1989843 := bstep (se 1 (by rfl) ⟨1492382, by rfl⟩ : syracuseStep 1989843 = 2984765) B2984765
theorem B4477157 : Blo 1989435 4477157 := bbase (se 4 (by rfl) ⟨419733, by rfl⟩ : syracuseStep 4477157 = 839467) (by norm_num)
theorem B2984771 : Blo 1989435 2984771 := bstep (se 1 (by rfl) ⟨2238578, by rfl⟩ : syracuseStep 2984771 = 4477157) B4477157
theorem B1989847 : Blo 1989435 1989847 := bstep (se 1 (by rfl) ⟨1492385, by rfl⟩ : syracuseStep 1989847 = 2984771) B2984771
theorem B5036813 : Blo 1989435 5036813 := bbase (se 3 (by rfl) ⟨944402, by rfl⟩ : syracuseStep 5036813 = 1888805) (by norm_num)
theorem B3357875 : Blo 1989435 3357875 := bstep (se 1 (by rfl) ⟨2518406, by rfl⟩ : syracuseStep 3357875 = 5036813) B5036813
theorem B2238583 : Blo 1989435 2238583 := bstep (se 1 (by rfl) ⟨1678937, by rfl⟩ : syracuseStep 2238583 = 3357875) B3357875
theorem B2984777 : Blo 1989435 2984777 := bstep (se 2 (by rfl) ⟨1119291, by rfl⟩ : syracuseStep 2984777 = 2238583) B2238583
theorem B1989851 : Blo 1989435 1989851 := bstep (se 1 (by rfl) ⟨1492388, by rfl⟩ : syracuseStep 1989851 = 2984777) B2984777
theorem B2833213 : Blo 1989435 2833213 := bbase (se 3 (by rfl) ⟨531227, by rfl⟩ : syracuseStep 2833213 = 1062455) (by norm_num)
theorem B3777617 : Blo 1989435 3777617 := bstep (se 2 (by rfl) ⟨1416606, by rfl⟩ : syracuseStep 3777617 = 2833213) B2833213
theorem B10073645 : Blo 1989435 10073645 := bstep (se 3 (by rfl) ⟨1888808, by rfl⟩ : syracuseStep 10073645 = 3777617) B3777617
theorem B6715763 : Blo 1989435 6715763 := bstep (se 1 (by rfl) ⟨5036822, by rfl⟩ : syracuseStep 6715763 = 10073645) B10073645
theorem B4477175 : Blo 1989435 4477175 := bstep (se 1 (by rfl) ⟨3357881, by rfl⟩ : syracuseStep 4477175 = 6715763) B6715763
theorem B2984783 : Blo 1989435 2984783 := bstep (se 1 (by rfl) ⟨2238587, by rfl⟩ : syracuseStep 2984783 = 4477175) B4477175
theorem B1989855 : Blo 1989435 1989855 := bstep (se 1 (by rfl) ⟨1492391, by rfl⟩ : syracuseStep 1989855 = 2984783) B2984783
theorem B2984789 : Blo 1989435 2984789 := bbase (se 9 (by rfl) ⟨8744, by rfl⟩ : syracuseStep 2984789 = 17489) (by norm_num)
theorem B1989859 : Blo 1989435 1989859 := bstep (se 1 (by rfl) ⟨1492394, by rfl⟩ : syracuseStep 1989859 = 2984789) B2984789
theorem B4249837 : Blo 1989435 4249837 := bbase (se 3 (by rfl) ⟨796844, by rfl⟩ : syracuseStep 4249837 = 1593689) (by norm_num)
theorem B5666449 : Blo 1989435 5666449 := bstep (se 2 (by rfl) ⟨2124918, by rfl⟩ : syracuseStep 5666449 = 4249837) B4249837
theorem B7555265 : Blo 1989435 7555265 := bstep (se 2 (by rfl) ⟨2833224, by rfl⟩ : syracuseStep 7555265 = 5666449) B5666449
theorem B5036843 : Blo 1989435 5036843 := bstep (se 1 (by rfl) ⟨3777632, by rfl⟩ : syracuseStep 5036843 = 7555265) B7555265
theorem B3357895 : Blo 1989435 3357895 := bstep (se 1 (by rfl) ⟨2518421, by rfl⟩ : syracuseStep 3357895 = 5036843) B5036843
theorem B4477193 : Blo 1989435 4477193 := bstep (se 2 (by rfl) ⟨1678947, by rfl⟩ : syracuseStep 4477193 = 3357895) B3357895
theorem B2984795 : Blo 1989435 2984795 := bstep (se 1 (by rfl) ⟨2238596, by rfl⟩ : syracuseStep 2984795 = 4477193) B4477193
theorem B1989863 : Blo 1989435 1989863 := bstep (se 1 (by rfl) ⟨1492397, by rfl⟩ : syracuseStep 1989863 = 2984795) B2984795
theorem B2238601 : Blo 1989435 2238601 := bbase (se 2 (by rfl) ⟨839475, by rfl⟩ : syracuseStep 2238601 = 1678951) (by norm_num)
theorem B2984801 : Blo 1989435 2984801 := bstep (se 2 (by rfl) ⟨1119300, by rfl⟩ : syracuseStep 2984801 = 2238601) B2238601
theorem B1989867 : Blo 1989435 1989867 := bstep (se 1 (by rfl) ⟨1492400, by rfl⟩ : syracuseStep 1989867 = 2984801) B2984801
theorem B3829189 : Blo 1989435 3829189 := bbase (se 4 (by rfl) ⟨358986, by rfl⟩ : syracuseStep 3829189 = 717973) (by norm_num)
theorem B5105585 : Blo 1989435 5105585 := bstep (se 2 (by rfl) ⟨1914594, by rfl⟩ : syracuseStep 5105585 = 3829189) B3829189
theorem B3403723 : Blo 1989435 3403723 := bstep (se 1 (by rfl) ⟨2552792, by rfl⟩ : syracuseStep 3403723 = 5105585) B5105585
theorem B4538297 : Blo 1989435 4538297 := bstep (se 2 (by rfl) ⟨1701861, by rfl⟩ : syracuseStep 4538297 = 3403723) B3403723
theorem B3025531 : Blo 1989435 3025531 := bstep (se 1 (by rfl) ⟨2269148, by rfl⟩ : syracuseStep 3025531 = 4538297) B4538297
theorem B16136165 : Blo 1989435 16136165 := bstep (se 4 (by rfl) ⟨1512765, by rfl⟩ : syracuseStep 16136165 = 3025531) B3025531
theorem B10757443 : Blo 1989435 10757443 := bstep (se 1 (by rfl) ⟨8068082, by rfl⟩ : syracuseStep 10757443 = 16136165) B16136165
theorem B14343257 : Blo 1989435 14343257 := bstep (se 2 (by rfl) ⟨5378721, by rfl⟩ : syracuseStep 14343257 = 10757443) B10757443
theorem B38248685 : Blo 1989435 38248685 := bstep (se 3 (by rfl) ⟨7171628, by rfl⟩ : syracuseStep 38248685 = 14343257) B14343257
theorem B25499123 : Blo 1989435 25499123 := bstep (se 1 (by rfl) ⟨19124342, by rfl⟩ : syracuseStep 25499123 = 38248685) B38248685
theorem B16999415 : Blo 1989435 16999415 := bstep (se 1 (by rfl) ⟨12749561, by rfl⟩ : syracuseStep 16999415 = 25499123) B25499123
theorem B11332943 : Blo 1989435 11332943 := bstep (se 1 (by rfl) ⟨8499707, by rfl⟩ : syracuseStep 11332943 = 16999415) B16999415
theorem B7555295 : Blo 1989435 7555295 := bstep (se 1 (by rfl) ⟨5666471, by rfl⟩ : syracuseStep 7555295 = 11332943) B11332943
theorem B5036863 : Blo 1989435 5036863 := bstep (se 1 (by rfl) ⟨3777647, by rfl⟩ : syracuseStep 5036863 = 7555295) B7555295
theorem B6715817 : Blo 1989435 6715817 := bstep (se 2 (by rfl) ⟨2518431, by rfl⟩ : syracuseStep 6715817 = 5036863) B5036863
theorem B4477211 : Blo 1989435 4477211 := bstep (se 1 (by rfl) ⟨3357908, by rfl⟩ : syracuseStep 4477211 = 6715817) B6715817
theorem B2984807 : Blo 1989435 2984807 := bstep (se 1 (by rfl) ⟨2238605, by rfl⟩ : syracuseStep 2984807 = 4477211) B4477211
theorem B1989871 : Blo 1989435 1989871 := bstep (se 1 (by rfl) ⟨1492403, by rfl⟩ : syracuseStep 1989871 = 2984807) B2984807
theorem B2984813 : Blo 1989435 2984813 := bbase (se 3 (by rfl) ⟨559652, by rfl⟩ : syracuseStep 2984813 = 1119305) (by norm_num)
theorem B1989875 : Blo 1989435 1989875 := bstep (se 1 (by rfl) ⟨1492406, by rfl⟩ : syracuseStep 1989875 = 2984813) B2984813
theorem B4477229 : Blo 1989435 4477229 := bbase (se 3 (by rfl) ⟨839480, by rfl⟩ : syracuseStep 4477229 = 1678961) (by norm_num)
theorem B2984819 : Blo 1989435 2984819 := bstep (se 1 (by rfl) ⟨2238614, by rfl⟩ : syracuseStep 2984819 = 4477229) B4477229
theorem B1989879 : Blo 1989435 1989879 := bstep (se 1 (by rfl) ⟨1492409, by rfl⟩ : syracuseStep 1989879 = 2984819) B2984819
theorem B6374821 : Blo 1989435 6374821 := bbase (se 4 (by rfl) ⟨597639, by rfl⟩ : syracuseStep 6374821 = 1195279) (by norm_num)
theorem B8499761 : Blo 1989435 8499761 := bstep (se 2 (by rfl) ⟨3187410, by rfl⟩ : syracuseStep 8499761 = 6374821) B6374821
theorem B5666507 : Blo 1989435 5666507 := bstep (se 1 (by rfl) ⟨4249880, by rfl⟩ : syracuseStep 5666507 = 8499761) B8499761
theorem B3777671 : Blo 1989435 3777671 := bstep (se 1 (by rfl) ⟨2833253, by rfl⟩ : syracuseStep 3777671 = 5666507) B5666507
theorem B2518447 : Blo 1989435 2518447 := bstep (se 1 (by rfl) ⟨1888835, by rfl⟩ : syracuseStep 2518447 = 3777671) B3777671
theorem B3357929 : Blo 1989435 3357929 := bstep (se 2 (by rfl) ⟨1259223, by rfl⟩ : syracuseStep 3357929 = 2518447) B2518447
theorem B2238619 : Blo 1989435 2238619 := bstep (se 1 (by rfl) ⟨1678964, by rfl⟩ : syracuseStep 2238619 = 3357929) B3357929
theorem B2984825 : Blo 1989435 2984825 := bstep (se 2 (by rfl) ⟨1119309, by rfl⟩ : syracuseStep 2984825 = 2238619) B2238619
theorem B1989883 : Blo 1989435 1989883 := bstep (se 1 (by rfl) ⟨1492412, by rfl⟩ : syracuseStep 1989883 = 2984825) B2984825
theorem B4538333 : Blo 1989435 4538333 := bbase (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) (by norm_num)
theorem B3025555 : Blo 1989435 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B64545173 : Blo 1989435 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B43030115 : Blo 1989435 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B28686743 : Blo 1989435 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B19124495 : Blo 1989435 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B12749663 : Blo 1989435 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B33999101 : Blo 1989435 33999101 := bstep (se 3 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 33999101 = 12749663) B12749663
theorem B22666067 : Blo 1989435 22666067 := bstep (se 1 (by rfl) ⟨16999550, by rfl⟩ : syracuseStep 22666067 = 33999101) B33999101
theorem B15110711 : Blo 1989435 15110711 := bstep (se 1 (by rfl) ⟨11333033, by rfl⟩ : syracuseStep 15110711 = 22666067) B22666067
theorem B10073807 : Blo 1989435 10073807 := bstep (se 1 (by rfl) ⟨7555355, by rfl⟩ : syracuseStep 10073807 = 15110711) B15110711
theorem B6715871 : Blo 1989435 6715871 := bstep (se 1 (by rfl) ⟨5036903, by rfl⟩ : syracuseStep 6715871 = 10073807) B10073807
theorem B4477247 : Blo 1989435 4477247 := bstep (se 1 (by rfl) ⟨3357935, by rfl⟩ : syracuseStep 4477247 = 6715871) B6715871
theorem B2984831 : Blo 1989435 2984831 := bstep (se 1 (by rfl) ⟨2238623, by rfl⟩ : syracuseStep 2984831 = 4477247) B4477247
theorem B1989887 : Blo 1989435 1989887 := bstep (se 1 (by rfl) ⟨1492415, by rfl⟩ : syracuseStep 1989887 = 2984831) B2984831
theorem B2984837 : Blo 1989435 2984837 := bbase (se 4 (by rfl) ⟨279828, by rfl⟩ : syracuseStep 2984837 = 559657) (by norm_num)
theorem B1989891 : Blo 1989435 1989891 := bstep (se 1 (by rfl) ⟨1492418, by rfl⟩ : syracuseStep 1989891 = 2984837) B2984837
theorem B3357949 : Blo 1989435 3357949 := bbase (se 3 (by rfl) ⟨629615, by rfl⟩ : syracuseStep 3357949 = 1259231) (by norm_num)
theorem B4477265 : Blo 1989435 4477265 := bstep (se 2 (by rfl) ⟨1678974, by rfl⟩ : syracuseStep 4477265 = 3357949) B3357949
theorem B2984843 : Blo 1989435 2984843 := bstep (se 1 (by rfl) ⟨2238632, by rfl⟩ : syracuseStep 2984843 = 4477265) B4477265
theorem B1989895 : Blo 1989435 1989895 := bstep (se 1 (by rfl) ⟨1492421, by rfl⟩ : syracuseStep 1989895 = 2984843) B2984843
theorem B2238637 : Blo 1989435 2238637 := bbase (se 3 (by rfl) ⟨419744, by rfl⟩ : syracuseStep 2238637 = 839489) (by norm_num)
theorem B2984849 : Blo 1989435 2984849 := bstep (se 2 (by rfl) ⟨1119318, by rfl⟩ : syracuseStep 2984849 = 2238637) B2238637
theorem B1989899 : Blo 1989435 1989899 := bstep (se 1 (by rfl) ⟨1492424, by rfl⟩ : syracuseStep 1989899 = 2984849) B2984849
theorem B6715925 : Blo 1989435 6715925 := bbase (se 6 (by rfl) ⟨157404, by rfl⟩ : syracuseStep 6715925 = 314809) (by norm_num)
theorem B4477283 : Blo 1989435 4477283 := bstep (se 1 (by rfl) ⟨3357962, by rfl⟩ : syracuseStep 4477283 = 6715925) B6715925
theorem B2984855 : Blo 1989435 2984855 := bstep (se 1 (by rfl) ⟨2238641, by rfl⟩ : syracuseStep 2984855 = 4477283) B4477283
theorem B1989903 : Blo 1989435 1989903 := bstep (se 1 (by rfl) ⟨1492427, by rfl⟩ : syracuseStep 1989903 = 2984855) B2984855
theorem B2984861 : Blo 1989435 2984861 := bbase (se 3 (by rfl) ⟨559661, by rfl⟩ : syracuseStep 2984861 = 1119323) (by norm_num)
theorem B1989907 : Blo 1989435 1989907 := bstep (se 1 (by rfl) ⟨1492430, by rfl⟩ : syracuseStep 1989907 = 2984861) B2984861
theorem B4477301 : Blo 1989435 4477301 := bbase (se 5 (by rfl) ⟨209873, by rfl⟩ : syracuseStep 4477301 = 419747) (by norm_num)
theorem B2984867 : Blo 1989435 2984867 := bstep (se 1 (by rfl) ⟨2238650, by rfl⟩ : syracuseStep 2984867 = 4477301) B4477301
theorem B1989911 : Blo 1989435 1989911 := bstep (se 1 (by rfl) ⟨1492433, by rfl⟩ : syracuseStep 1989911 = 2984867) B2984867
theorem B12749845 : Blo 1989435 12749845 := bbase (se 6 (by rfl) ⟨298824, by rfl⟩ : syracuseStep 12749845 = 597649) (by norm_num)
theorem B16999793 : Blo 1989435 16999793 := bstep (se 2 (by rfl) ⟨6374922, by rfl⟩ : syracuseStep 16999793 = 12749845) B12749845
theorem B11333195 : Blo 1989435 11333195 := bstep (se 1 (by rfl) ⟨8499896, by rfl⟩ : syracuseStep 11333195 = 16999793) B16999793
theorem B7555463 : Blo 1989435 7555463 := bstep (se 1 (by rfl) ⟨5666597, by rfl⟩ : syracuseStep 7555463 = 11333195) B11333195
theorem B5036975 : Blo 1989435 5036975 := bstep (se 1 (by rfl) ⟨3777731, by rfl⟩ : syracuseStep 5036975 = 7555463) B7555463
theorem B3357983 : Blo 1989435 3357983 := bstep (se 1 (by rfl) ⟨2518487, by rfl⟩ : syracuseStep 3357983 = 5036975) B5036975
theorem B2238655 : Blo 1989435 2238655 := bstep (se 1 (by rfl) ⟨1678991, by rfl⟩ : syracuseStep 2238655 = 3357983) B3357983
theorem B2984873 : Blo 1989435 2984873 := bstep (se 2 (by rfl) ⟨1119327, by rfl⟩ : syracuseStep 2984873 = 2238655) B2238655
theorem B1989915 : Blo 1989435 1989915 := bstep (se 1 (by rfl) ⟨1492436, by rfl⟩ : syracuseStep 1989915 = 2984873) B2984873
theorem B7555477 : Blo 1989435 7555477 := bbase (se 6 (by rfl) ⟨177081, by rfl⟩ : syracuseStep 7555477 = 354163) (by norm_num)
theorem B10073969 : Blo 1989435 10073969 := bstep (se 2 (by rfl) ⟨3777738, by rfl⟩ : syracuseStep 10073969 = 7555477) B7555477
theorem B6715979 : Blo 1989435 6715979 := bstep (se 1 (by rfl) ⟨5036984, by rfl⟩ : syracuseStep 6715979 = 10073969) B10073969
theorem B4477319 : Blo 1989435 4477319 := bstep (se 1 (by rfl) ⟨3357989, by rfl⟩ : syracuseStep 4477319 = 6715979) B6715979
theorem B2984879 : Blo 1989435 2984879 := bstep (se 1 (by rfl) ⟨2238659, by rfl⟩ : syracuseStep 2984879 = 4477319) B4477319
theorem B1989919 : Blo 1989435 1989919 := bstep (se 1 (by rfl) ⟨1492439, by rfl⟩ : syracuseStep 1989919 = 2984879) B2984879
theorem B2984885 : Blo 1989435 2984885 := bbase (se 5 (by rfl) ⟨139916, by rfl⟩ : syracuseStep 2984885 = 279833) (by norm_num)
theorem B1989923 : Blo 1989435 1989923 := bstep (se 1 (by rfl) ⟨1492442, by rfl⟩ : syracuseStep 1989923 = 2984885) B2984885
theorem B5037005 : Blo 1989435 5037005 := bbase (se 3 (by rfl) ⟨944438, by rfl⟩ : syracuseStep 5037005 = 1888877) (by norm_num)
theorem B3358003 : Blo 1989435 3358003 := bstep (se 1 (by rfl) ⟨2518502, by rfl⟩ : syracuseStep 3358003 = 5037005) B5037005
theorem B4477337 : Blo 1989435 4477337 := bstep (se 2 (by rfl) ⟨1679001, by rfl⟩ : syracuseStep 4477337 = 3358003) B3358003
theorem B2984891 : Blo 1989435 2984891 := bstep (se 1 (by rfl) ⟨2238668, by rfl⟩ : syracuseStep 2984891 = 4477337) B4477337
theorem B1989927 : Blo 1989435 1989927 := bstep (se 1 (by rfl) ⟨1492445, by rfl⟩ : syracuseStep 1989927 = 2984891) B2984891
theorem B2238673 : Blo 1989435 2238673 := bbase (se 2 (by rfl) ⟨839502, by rfl⟩ : syracuseStep 2238673 = 1679005) (by norm_num)
theorem B2984897 : Blo 1989435 2984897 := bstep (se 2 (by rfl) ⟨1119336, by rfl⟩ : syracuseStep 2984897 = 2238673) B2238673
theorem B1989931 : Blo 1989435 1989931 := bstep (se 1 (by rfl) ⟨1492448, by rfl⟩ : syracuseStep 1989931 = 2984897) B2984897
theorem B7171861 : Blo 1989435 7171861 := bbase (se 6 (by rfl) ⟨168090, by rfl⟩ : syracuseStep 7171861 = 336181) (by norm_num)
theorem B9562481 : Blo 1989435 9562481 := bstep (se 2 (by rfl) ⟨3585930, by rfl⟩ : syracuseStep 9562481 = 7171861) B7171861
theorem B6374987 : Blo 1989435 6374987 := bstep (se 1 (by rfl) ⟨4781240, by rfl⟩ : syracuseStep 6374987 = 9562481) B9562481
theorem B4249991 : Blo 1989435 4249991 := bstep (se 1 (by rfl) ⟨3187493, by rfl⟩ : syracuseStep 4249991 = 6374987) B6374987
theorem B2833327 : Blo 1989435 2833327 := bstep (se 1 (by rfl) ⟨2124995, by rfl⟩ : syracuseStep 2833327 = 4249991) B4249991
theorem B3777769 : Blo 1989435 3777769 := bstep (se 2 (by rfl) ⟨1416663, by rfl⟩ : syracuseStep 3777769 = 2833327) B2833327
theorem B5037025 : Blo 1989435 5037025 := bstep (se 2 (by rfl) ⟨1888884, by rfl⟩ : syracuseStep 5037025 = 3777769) B3777769
theorem B6716033 : Blo 1989435 6716033 := bstep (se 2 (by rfl) ⟨2518512, by rfl⟩ : syracuseStep 6716033 = 5037025) B5037025
theorem B4477355 : Blo 1989435 4477355 := bstep (se 1 (by rfl) ⟨3358016, by rfl⟩ : syracuseStep 4477355 = 6716033) B6716033
theorem B2984903 : Blo 1989435 2984903 := bstep (se 1 (by rfl) ⟨2238677, by rfl⟩ : syracuseStep 2984903 = 4477355) B4477355
theorem B1989935 : Blo 1989435 1989935 := bstep (se 1 (by rfl) ⟨1492451, by rfl⟩ : syracuseStep 1989935 = 2984903) B2984903
theorem B2984909 : Blo 1989435 2984909 := bbase (se 3 (by rfl) ⟨559670, by rfl⟩ : syracuseStep 2984909 = 1119341) (by norm_num)
theorem B1989939 : Blo 1989435 1989939 := bstep (se 1 (by rfl) ⟨1492454, by rfl⟩ : syracuseStep 1989939 = 2984909) B2984909
theorem B4477373 : Blo 1989435 4477373 := bbase (se 3 (by rfl) ⟨839507, by rfl⟩ : syracuseStep 4477373 = 1679015) (by norm_num)
theorem B2984915 : Blo 1989435 2984915 := bstep (se 1 (by rfl) ⟨2238686, by rfl⟩ : syracuseStep 2984915 = 4477373) B4477373
theorem B1989943 : Blo 1989435 1989943 := bstep (se 1 (by rfl) ⟨1492457, by rfl⟩ : syracuseStep 1989943 = 2984915) B2984915
theorem B3358037 : Blo 1989435 3358037 := bbase (se 11 (by rfl) ⟨2459, by rfl⟩ : syracuseStep 3358037 = 4919) (by norm_num)
theorem B2238691 : Blo 1989435 2238691 := bstep (se 1 (by rfl) ⟨1679018, by rfl⟩ : syracuseStep 2238691 = 3358037) B3358037
theorem B2984921 : Blo 1989435 2984921 := bstep (se 2 (by rfl) ⟨1119345, by rfl⟩ : syracuseStep 2984921 = 2238691) B2238691
theorem B1989947 : Blo 1989435 1989947 := bstep (se 1 (by rfl) ⟨1492460, by rfl⟩ : syracuseStep 1989947 = 2984921) B2984921
theorem B13801205 : Blo 1989435 13801205 := bbase (se 5 (by rfl) ⟨646931, by rfl⟩ : syracuseStep 13801205 = 1293863) (by norm_num)
theorem B36803213 : Blo 1989435 36803213 := bstep (se 3 (by rfl) ⟨6900602, by rfl⟩ : syracuseStep 36803213 = 13801205) B13801205
theorem B24535475 : Blo 1989435 24535475 := bstep (se 1 (by rfl) ⟨18401606, by rfl⟩ : syracuseStep 24535475 = 36803213) B36803213
theorem B16356983 : Blo 1989435 16356983 := bstep (se 1 (by rfl) ⟨12267737, by rfl⟩ : syracuseStep 16356983 = 24535475) B24535475
theorem B43618621 : Blo 1989435 43618621 := bstep (se 3 (by rfl) ⟨8178491, by rfl⟩ : syracuseStep 43618621 = 16356983) B16356983
theorem B58158161 : Blo 1989435 58158161 := bstep (se 2 (by rfl) ⟨21809310, by rfl⟩ : syracuseStep 58158161 = 43618621) B43618621
theorem B38772107 : Blo 1989435 38772107 := bstep (se 1 (by rfl) ⟨29079080, by rfl⟩ : syracuseStep 38772107 = 58158161) B58158161
theorem B25848071 : Blo 1989435 25848071 := bstep (se 1 (by rfl) ⟨19386053, by rfl⟩ : syracuseStep 25848071 = 38772107) B38772107
theorem B17232047 : Blo 1989435 17232047 := bstep (se 1 (by rfl) ⟨12924035, by rfl⟩ : syracuseStep 17232047 = 25848071) B25848071
theorem B11488031 : Blo 1989435 11488031 := bstep (se 1 (by rfl) ⟨8616023, by rfl⟩ : syracuseStep 11488031 = 17232047) B17232047
theorem B7658687 : Blo 1989435 7658687 := bstep (se 1 (by rfl) ⟨5744015, by rfl⟩ : syracuseStep 7658687 = 11488031) B11488031
theorem B5105791 : Blo 1989435 5105791 := bstep (se 1 (by rfl) ⟨3829343, by rfl⟩ : syracuseStep 5105791 = 7658687) B7658687
theorem B6807721 : Blo 1989435 6807721 := bstep (se 2 (by rfl) ⟨2552895, by rfl⟩ : syracuseStep 6807721 = 5105791) B5105791
theorem B9076961 : Blo 1989435 9076961 := bstep (se 2 (by rfl) ⟨3403860, by rfl⟩ : syracuseStep 9076961 = 6807721) B6807721
theorem B6051307 : Blo 1989435 6051307 := bstep (se 1 (by rfl) ⟨4538480, by rfl⟩ : syracuseStep 6051307 = 9076961) B9076961
theorem B8068409 : Blo 1989435 8068409 := bstep (se 2 (by rfl) ⟨3025653, by rfl⟩ : syracuseStep 8068409 = 6051307) B6051307
theorem B5378939 : Blo 1989435 5378939 := bstep (se 1 (by rfl) ⟨4034204, by rfl⟩ : syracuseStep 5378939 = 8068409) B8068409
theorem B3585959 : Blo 1989435 3585959 := bstep (se 1 (by rfl) ⟨2689469, by rfl⟩ : syracuseStep 3585959 = 5378939) B5378939
theorem B2390639 : Blo 1989435 2390639 := bstep (se 1 (by rfl) ⟨1792979, by rfl⟩ : syracuseStep 2390639 = 3585959) B3585959
theorem B6375037 : Blo 1989435 6375037 := bstep (se 3 (by rfl) ⟨1195319, by rfl⟩ : syracuseStep 6375037 = 2390639) B2390639
theorem B8500049 : Blo 1989435 8500049 := bstep (se 2 (by rfl) ⟨3187518, by rfl⟩ : syracuseStep 8500049 = 6375037) B6375037
theorem B5666699 : Blo 1989435 5666699 := bstep (se 1 (by rfl) ⟨4250024, by rfl⟩ : syracuseStep 5666699 = 8500049) B8500049
theorem B15111197 : Blo 1989435 15111197 := bstep (se 3 (by rfl) ⟨2833349, by rfl⟩ : syracuseStep 15111197 = 5666699) B5666699
theorem B10074131 : Blo 1989435 10074131 := bstep (se 1 (by rfl) ⟨7555598, by rfl⟩ : syracuseStep 10074131 = 15111197) B15111197
theorem B6716087 : Blo 1989435 6716087 := bstep (se 1 (by rfl) ⟨5037065, by rfl⟩ : syracuseStep 6716087 = 10074131) B10074131
theorem B4477391 : Blo 1989435 4477391 := bstep (se 1 (by rfl) ⟨3358043, by rfl⟩ : syracuseStep 4477391 = 6716087) B6716087
theorem B2984927 : Blo 1989435 2984927 := bstep (se 1 (by rfl) ⟨2238695, by rfl⟩ : syracuseStep 2984927 = 4477391) B4477391
theorem B1989951 : Blo 1989435 1989951 := bstep (se 1 (by rfl) ⟨1492463, by rfl⟩ : syracuseStep 1989951 = 2984927) B2984927
theorem B2984933 : Blo 1989435 2984933 := bbase (se 4 (by rfl) ⟨279837, by rfl⟩ : syracuseStep 2984933 = 559675) (by norm_num)
theorem B1989955 : Blo 1989435 1989955 := bstep (se 1 (by rfl) ⟨1492466, by rfl⟩ : syracuseStep 1989955 = 2984933) B2984933
theorem B8500085 : Blo 1989435 8500085 := bbase (se 5 (by rfl) ⟨398441, by rfl⟩ : syracuseStep 8500085 = 796883) (by norm_num)
theorem B5666723 : Blo 1989435 5666723 := bstep (se 1 (by rfl) ⟨4250042, by rfl⟩ : syracuseStep 5666723 = 8500085) B8500085
theorem B3777815 : Blo 1989435 3777815 := bstep (se 1 (by rfl) ⟨2833361, by rfl⟩ : syracuseStep 3777815 = 5666723) B5666723
theorem B2518543 : Blo 1989435 2518543 := bstep (se 1 (by rfl) ⟨1888907, by rfl⟩ : syracuseStep 2518543 = 3777815) B3777815
theorem B3358057 : Blo 1989435 3358057 := bstep (se 2 (by rfl) ⟨1259271, by rfl⟩ : syracuseStep 3358057 = 2518543) B2518543
theorem B4477409 : Blo 1989435 4477409 := bstep (se 2 (by rfl) ⟨1679028, by rfl⟩ : syracuseStep 4477409 = 3358057) B3358057
theorem B2984939 : Blo 1989435 2984939 := bstep (se 1 (by rfl) ⟨2238704, by rfl⟩ : syracuseStep 2984939 = 4477409) B4477409
theorem B1989959 : Blo 1989435 1989959 := bstep (se 1 (by rfl) ⟨1492469, by rfl⟩ : syracuseStep 1989959 = 2984939) B2984939
theorem B2238709 : Blo 1989435 2238709 := bbase (se 5 (by rfl) ⟨104939, by rfl⟩ : syracuseStep 2238709 = 209879) (by norm_num)
theorem B2984945 : Blo 1989435 2984945 := bstep (se 2 (by rfl) ⟨1119354, by rfl⟩ : syracuseStep 2984945 = 2238709) B2238709
theorem B1989963 : Blo 1989435 1989963 := bstep (se 1 (by rfl) ⟨1492472, by rfl⟩ : syracuseStep 1989963 = 2984945) B2984945
theorem B2518553 : Blo 1989435 2518553 := bbase (se 2 (by rfl) ⟨944457, by rfl⟩ : syracuseStep 2518553 = 1888915) (by norm_num)
theorem B6716141 : Blo 1989435 6716141 := bstep (se 3 (by rfl) ⟨1259276, by rfl⟩ : syracuseStep 6716141 = 2518553) B2518553
theorem B4477427 : Blo 1989435 4477427 := bstep (se 1 (by rfl) ⟨3358070, by rfl⟩ : syracuseStep 4477427 = 6716141) B6716141
theorem B2984951 : Blo 1989435 2984951 := bstep (se 1 (by rfl) ⟨2238713, by rfl⟩ : syracuseStep 2984951 = 4477427) B4477427
theorem B1989967 : Blo 1989435 1989967 := bstep (se 1 (by rfl) ⟨1492475, by rfl⟩ : syracuseStep 1989967 = 2984951) B2984951
theorem B2984957 : Blo 1989435 2984957 := bbase (se 3 (by rfl) ⟨559679, by rfl⟩ : syracuseStep 2984957 = 1119359) (by norm_num)
theorem B1989971 : Blo 1989435 1989971 := bstep (se 1 (by rfl) ⟨1492478, by rfl⟩ : syracuseStep 1989971 = 2984957) B2984957
theorem B4477445 : Blo 1989435 4477445 := bbase (se 4 (by rfl) ⟨419760, by rfl⟩ : syracuseStep 4477445 = 839521) (by norm_num)
theorem B2984963 : Blo 1989435 2984963 := bstep (se 1 (by rfl) ⟨2238722, by rfl⟩ : syracuseStep 2984963 = 4477445) B4477445
theorem B1989975 : Blo 1989435 1989975 := bstep (se 1 (by rfl) ⟨1492481, by rfl⟩ : syracuseStep 1989975 = 2984963) B2984963
theorem B3777853 : Blo 1989435 3777853 := bbase (se 3 (by rfl) ⟨708347, by rfl⟩ : syracuseStep 3777853 = 1416695) (by norm_num)
theorem B5037137 : Blo 1989435 5037137 := bstep (se 2 (by rfl) ⟨1888926, by rfl⟩ : syracuseStep 5037137 = 3777853) B3777853
theorem B3358091 : Blo 1989435 3358091 := bstep (se 1 (by rfl) ⟨2518568, by rfl⟩ : syracuseStep 3358091 = 5037137) B5037137
theorem B2238727 : Blo 1989435 2238727 := bstep (se 1 (by rfl) ⟨1679045, by rfl⟩ : syracuseStep 2238727 = 3358091) B3358091
theorem B2984969 : Blo 1989435 2984969 := bstep (se 2 (by rfl) ⟨1119363, by rfl⟩ : syracuseStep 2984969 = 2238727) B2238727
theorem B1989979 : Blo 1989435 1989979 := bstep (se 1 (by rfl) ⟨1492484, by rfl⟩ : syracuseStep 1989979 = 2984969) B2984969
theorem B10074293 : Blo 1989435 10074293 := bbase (se 5 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 10074293 = 944465) (by norm_num)
theorem B6716195 : Blo 1989435 6716195 := bstep (se 1 (by rfl) ⟨5037146, by rfl⟩ : syracuseStep 6716195 = 10074293) B10074293
theorem B4477463 : Blo 1989435 4477463 := bstep (se 1 (by rfl) ⟨3358097, by rfl⟩ : syracuseStep 4477463 = 6716195) B6716195
theorem B2984975 : Blo 1989435 2984975 := bstep (se 1 (by rfl) ⟨2238731, by rfl⟩ : syracuseStep 2984975 = 4477463) B4477463
theorem B1989983 : Blo 1989435 1989983 := bstep (se 1 (by rfl) ⟨1492487, by rfl⟩ : syracuseStep 1989983 = 2984975) B2984975
theorem B2984981 : Blo 1989435 2984981 := bbase (se 6 (by rfl) ⟨69960, by rfl⟩ : syracuseStep 2984981 = 139921) (by norm_num)
theorem B1989987 : Blo 1989435 1989987 := bstep (se 1 (by rfl) ⟨1492490, by rfl⟩ : syracuseStep 1989987 = 2984981) B2984981
theorem B9077141 : Blo 1989435 9077141 := bbase (se 6 (by rfl) ⟨212745, by rfl⟩ : syracuseStep 9077141 = 425491) (by norm_num)
theorem B24205709 : Blo 1989435 24205709 := bstep (se 3 (by rfl) ⟨4538570, by rfl⟩ : syracuseStep 24205709 = 9077141) B9077141
theorem B16137139 : Blo 1989435 16137139 := bstep (se 1 (by rfl) ⟨12102854, by rfl⟩ : syracuseStep 16137139 = 24205709) B24205709
theorem B21516185 : Blo 1989435 21516185 := bstep (se 2 (by rfl) ⟨8068569, by rfl⟩ : syracuseStep 21516185 = 16137139) B16137139
theorem B14344123 : Blo 1989435 14344123 := bstep (se 1 (by rfl) ⟨10758092, by rfl⟩ : syracuseStep 14344123 = 21516185) B21516185
theorem B19125497 : Blo 1989435 19125497 := bstep (se 2 (by rfl) ⟨7172061, by rfl⟩ : syracuseStep 19125497 = 14344123) B14344123
theorem B12750331 : Blo 1989435 12750331 := bstep (se 1 (by rfl) ⟨9562748, by rfl⟩ : syracuseStep 12750331 = 19125497) B19125497
theorem B17000441 : Blo 1989435 17000441 := bstep (se 2 (by rfl) ⟨6375165, by rfl⟩ : syracuseStep 17000441 = 12750331) B12750331
theorem B11333627 : Blo 1989435 11333627 := bstep (se 1 (by rfl) ⟨8500220, by rfl⟩ : syracuseStep 11333627 = 17000441) B17000441
theorem B7555751 : Blo 1989435 7555751 := bstep (se 1 (by rfl) ⟨5666813, by rfl⟩ : syracuseStep 7555751 = 11333627) B11333627
theorem B5037167 : Blo 1989435 5037167 := bstep (se 1 (by rfl) ⟨3777875, by rfl⟩ : syracuseStep 5037167 = 7555751) B7555751
theorem B3358111 : Blo 1989435 3358111 := bstep (se 1 (by rfl) ⟨2518583, by rfl⟩ : syracuseStep 3358111 = 5037167) B5037167
theorem B4477481 : Blo 1989435 4477481 := bstep (se 2 (by rfl) ⟨1679055, by rfl⟩ : syracuseStep 4477481 = 3358111) B3358111
theorem B2984987 : Blo 1989435 2984987 := bstep (se 1 (by rfl) ⟨2238740, by rfl⟩ : syracuseStep 2984987 = 4477481) B4477481
theorem B1989991 : Blo 1989435 1989991 := bstep (se 1 (by rfl) ⟨1492493, by rfl⟩ : syracuseStep 1989991 = 2984987) B2984987
theorem B2238745 : Blo 1989435 2238745 := bbase (se 2 (by rfl) ⟨839529, by rfl⟩ : syracuseStep 2238745 = 1679059) (by norm_num)
theorem B2984993 : Blo 1989435 2984993 := bstep (se 2 (by rfl) ⟨1119372, by rfl⟩ : syracuseStep 2984993 = 2238745) B2238745
theorem B1989995 : Blo 1989435 1989995 := bstep (se 1 (by rfl) ⟨1492496, by rfl⟩ : syracuseStep 1989995 = 2984993) B2984993
theorem B7555781 : Blo 1989435 7555781 := bbase (se 4 (by rfl) ⟨708354, by rfl⟩ : syracuseStep 7555781 = 1416709) (by norm_num)
theorem B5037187 : Blo 1989435 5037187 := bstep (se 1 (by rfl) ⟨3777890, by rfl⟩ : syracuseStep 5037187 = 7555781) B7555781
theorem B6716249 : Blo 1989435 6716249 := bstep (se 2 (by rfl) ⟨2518593, by rfl⟩ : syracuseStep 6716249 = 5037187) B5037187
theorem B4477499 : Blo 1989435 4477499 := bstep (se 1 (by rfl) ⟨3358124, by rfl⟩ : syracuseStep 4477499 = 6716249) B6716249
theorem B2984999 : Blo 1989435 2984999 := bstep (se 1 (by rfl) ⟨2238749, by rfl⟩ : syracuseStep 2984999 = 4477499) B4477499
theorem B1989999 : Blo 1989435 1989999 := bstep (se 1 (by rfl) ⟨1492499, by rfl⟩ : syracuseStep 1989999 = 2984999) B2984999
theorem B2985005 : Blo 1989435 2985005 := bbase (se 3 (by rfl) ⟨559688, by rfl⟩ : syracuseStep 2985005 = 1119377) (by norm_num)
theorem B1990003 : Blo 1989435 1990003 := bstep (se 1 (by rfl) ⟨1492502, by rfl⟩ : syracuseStep 1990003 = 2985005) B2985005
theorem B4477517 : Blo 1989435 4477517 := bbase (se 3 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 4477517 = 1679069) (by norm_num)
theorem B2985011 : Blo 1989435 2985011 := bstep (se 1 (by rfl) ⟨2238758, by rfl⟩ : syracuseStep 2985011 = 4477517) B4477517
theorem B1990007 : Blo 1989435 1990007 := bstep (se 1 (by rfl) ⟨1492505, by rfl⟩ : syracuseStep 1990007 = 2985011) B2985011
theorem B2518609 : Blo 1989435 2518609 := bbase (se 2 (by rfl) ⟨944478, by rfl⟩ : syracuseStep 2518609 = 1888957) (by norm_num)
theorem B3358145 : Blo 1989435 3358145 := bstep (se 2 (by rfl) ⟨1259304, by rfl⟩ : syracuseStep 3358145 = 2518609) B2518609
theorem B2238763 : Blo 1989435 2238763 := bstep (se 1 (by rfl) ⟨1679072, by rfl⟩ : syracuseStep 2238763 = 3358145) B3358145
theorem B2985017 : Blo 1989435 2985017 := bstep (se 2 (by rfl) ⟨1119381, by rfl⟩ : syracuseStep 2985017 = 2238763) B2238763
theorem B1990011 : Blo 1989435 1990011 := bstep (se 1 (by rfl) ⟨1492508, by rfl⟩ : syracuseStep 1990011 = 2985017) B2985017
theorem B3187621 : Blo 1989435 3187621 := bbase (se 4 (by rfl) ⟨298839, by rfl⟩ : syracuseStep 3187621 = 597679) (by norm_num)
theorem B4250161 : Blo 1989435 4250161 := bstep (se 2 (by rfl) ⟨1593810, by rfl⟩ : syracuseStep 4250161 = 3187621) B3187621
theorem B22667525 : Blo 1989435 22667525 := bstep (se 4 (by rfl) ⟨2125080, by rfl⟩ : syracuseStep 22667525 = 4250161) B4250161
theorem B15111683 : Blo 1989435 15111683 := bstep (se 1 (by rfl) ⟨11333762, by rfl⟩ : syracuseStep 15111683 = 22667525) B22667525
theorem B10074455 : Blo 1989435 10074455 := bstep (se 1 (by rfl) ⟨7555841, by rfl⟩ : syracuseStep 10074455 = 15111683) B15111683
theorem B6716303 : Blo 1989435 6716303 := bstep (se 1 (by rfl) ⟨5037227, by rfl⟩ : syracuseStep 6716303 = 10074455) B10074455
theorem B4477535 : Blo 1989435 4477535 := bstep (se 1 (by rfl) ⟨3358151, by rfl⟩ : syracuseStep 4477535 = 6716303) B6716303
theorem B2985023 : Blo 1989435 2985023 := bstep (se 1 (by rfl) ⟨2238767, by rfl⟩ : syracuseStep 2985023 = 4477535) B4477535
theorem B1990015 : Blo 1989435 1990015 := bstep (se 1 (by rfl) ⟨1492511, by rfl⟩ : syracuseStep 1990015 = 2985023) B2985023
theorem B2985029 : Blo 1989435 2985029 := bbase (se 4 (by rfl) ⟨279846, by rfl⟩ : syracuseStep 2985029 = 559693) (by norm_num)
theorem B1990019 : Blo 1989435 1990019 := bstep (se 1 (by rfl) ⟨1492514, by rfl⟩ : syracuseStep 1990019 = 2985029) B2985029
theorem B3358165 : Blo 1989435 3358165 := bbase (se 7 (by rfl) ⟨39353, by rfl⟩ : syracuseStep 3358165 = 78707) (by norm_num)
theorem B4477553 : Blo 1989435 4477553 := bstep (se 2 (by rfl) ⟨1679082, by rfl⟩ : syracuseStep 4477553 = 3358165) B3358165
theorem B2985035 : Blo 1989435 2985035 := bstep (se 1 (by rfl) ⟨2238776, by rfl⟩ : syracuseStep 2985035 = 4477553) B4477553
theorem B1990023 : Blo 1989435 1990023 := bstep (se 1 (by rfl) ⟨1492517, by rfl⟩ : syracuseStep 1990023 = 2985035) B2985035
theorem B2238781 : Blo 1989435 2238781 := bbase (se 3 (by rfl) ⟨419771, by rfl⟩ : syracuseStep 2238781 = 839543) (by norm_num)
theorem B2985041 : Blo 1989435 2985041 := bstep (se 2 (by rfl) ⟨1119390, by rfl⟩ : syracuseStep 2985041 = 2238781) B2238781
theorem B1990027 : Blo 1989435 1990027 := bstep (se 1 (by rfl) ⟨1492520, by rfl⟩ : syracuseStep 1990027 = 2985041) B2985041
theorem B6716357 : Blo 1989435 6716357 := bbase (se 4 (by rfl) ⟨629658, by rfl⟩ : syracuseStep 6716357 = 1259317) (by norm_num)
theorem B4477571 : Blo 1989435 4477571 := bstep (se 1 (by rfl) ⟨3358178, by rfl⟩ : syracuseStep 4477571 = 6716357) B6716357
theorem B2985047 : Blo 1989435 2985047 := bstep (se 1 (by rfl) ⟨2238785, by rfl⟩ : syracuseStep 2985047 = 4477571) B4477571
theorem B1990031 : Blo 1989435 1990031 := bstep (se 1 (by rfl) ⟨1492523, by rfl⟩ : syracuseStep 1990031 = 2985047) B2985047
theorem B2985053 : Blo 1989435 2985053 := bbase (se 3 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 2985053 = 1119395) (by norm_num)
theorem B1990035 : Blo 1989435 1990035 := bstep (se 1 (by rfl) ⟨1492526, by rfl⟩ : syracuseStep 1990035 = 2985053) B2985053
theorem B4477589 : Blo 1989435 4477589 := bbase (se 6 (by rfl) ⟨104943, by rfl⟩ : syracuseStep 4477589 = 209887) (by norm_num)
theorem B2985059 : Blo 1989435 2985059 := bstep (se 1 (by rfl) ⟨2238794, by rfl⟩ : syracuseStep 2985059 = 4477589) B4477589
theorem B1990039 : Blo 1989435 1990039 := bstep (se 1 (by rfl) ⟨1492529, by rfl⟩ : syracuseStep 1990039 = 2985059) B2985059
theorem B4781501 : Blo 1989435 4781501 := bbase (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) (by norm_num)
theorem B3187667 : Blo 1989435 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B2125111 : Blo 1989435 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B2833481 : Blo 1989435 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B7555949 : Blo 1989435 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B5037299 : Blo 1989435 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B3358199 : Blo 1989435 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B2238799 : Blo 1989435 2238799 := bstep (se 1 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 2238799 = 3358199) B3358199
theorem B2985065 : Blo 1989435 2985065 := bstep (se 2 (by rfl) ⟨1119399, by rfl⟩ : syracuseStep 2985065 = 2238799) B2238799
theorem B1990043 : Blo 1989435 1990043 := bstep (se 1 (by rfl) ⟨1492532, by rfl⟩ : syracuseStep 1990043 = 2985065) B2985065
theorem B5175701 : Blo 1989435 5175701 := bbase (se 6 (by rfl) ⟨121305, by rfl⟩ : syracuseStep 5175701 = 242611) (by norm_num)
theorem B3450467 : Blo 1989435 3450467 := bstep (se 1 (by rfl) ⟨2587850, by rfl⟩ : syracuseStep 3450467 = 5175701) B5175701
theorem B2300311 : Blo 1989435 2300311 := bstep (se 1 (by rfl) ⟨1725233, by rfl⟩ : syracuseStep 2300311 = 3450467) B3450467
theorem B3067081 : Blo 1989435 3067081 := bstep (se 2 (by rfl) ⟨1150155, by rfl⟩ : syracuseStep 3067081 = 2300311) B2300311
theorem B65431061 : Blo 1989435 65431061 := bstep (se 6 (by rfl) ⟨1533540, by rfl⟩ : syracuseStep 65431061 = 3067081) B3067081
theorem B43620707 : Blo 1989435 43620707 := bstep (se 1 (by rfl) ⟨32715530, by rfl⟩ : syracuseStep 43620707 = 65431061) B65431061
theorem B29080471 : Blo 1989435 29080471 := bstep (se 1 (by rfl) ⟨21810353, by rfl⟩ : syracuseStep 29080471 = 43620707) B43620707
theorem B38773961 : Blo 1989435 38773961 := bstep (se 2 (by rfl) ⟨14540235, by rfl⟩ : syracuseStep 38773961 = 29080471) B29080471
theorem B25849307 : Blo 1989435 25849307 := bstep (se 1 (by rfl) ⟨19386980, by rfl⟩ : syracuseStep 25849307 = 38773961) B38773961
theorem B68931485 : Blo 1989435 68931485 := bstep (se 3 (by rfl) ⟨12924653, by rfl⟩ : syracuseStep 68931485 = 25849307) B25849307
theorem B45954323 : Blo 1989435 45954323 := bstep (se 1 (by rfl) ⟨34465742, by rfl⟩ : syracuseStep 45954323 = 68931485) B68931485
theorem B30636215 : Blo 1989435 30636215 := bstep (se 1 (by rfl) ⟨22977161, by rfl⟩ : syracuseStep 30636215 = 45954323) B45954323
theorem B20424143 : Blo 1989435 20424143 := bstep (se 1 (by rfl) ⟨15318107, by rfl⟩ : syracuseStep 20424143 = 30636215) B30636215
theorem B13616095 : Blo 1989435 13616095 := bstep (se 1 (by rfl) ⟨10212071, by rfl⟩ : syracuseStep 13616095 = 20424143) B20424143
theorem B18154793 : Blo 1989435 18154793 := bstep (se 2 (by rfl) ⟨6808047, by rfl⟩ : syracuseStep 18154793 = 13616095) B13616095
theorem B12103195 : Blo 1989435 12103195 := bstep (se 1 (by rfl) ⟨9077396, by rfl⟩ : syracuseStep 12103195 = 18154793) B18154793
theorem B16137593 : Blo 1989435 16137593 := bstep (se 2 (by rfl) ⟨6051597, by rfl⟩ : syracuseStep 16137593 = 12103195) B12103195
theorem B10758395 : Blo 1989435 10758395 := bstep (se 1 (by rfl) ⟨8068796, by rfl⟩ : syracuseStep 10758395 = 16137593) B16137593
theorem B7172263 : Blo 1989435 7172263 := bstep (se 1 (by rfl) ⟨5379197, by rfl⟩ : syracuseStep 7172263 = 10758395) B10758395
theorem B9563017 : Blo 1989435 9563017 := bstep (se 2 (by rfl) ⟨3586131, by rfl⟩ : syracuseStep 9563017 = 7172263) B7172263
theorem B12750689 : Blo 1989435 12750689 := bstep (se 2 (by rfl) ⟨4781508, by rfl⟩ : syracuseStep 12750689 = 9563017) B9563017
theorem B8500459 : Blo 1989435 8500459 := bstep (se 1 (by rfl) ⟨6375344, by rfl⟩ : syracuseStep 8500459 = 12750689) B12750689
theorem B11333945 : Blo 1989435 11333945 := bstep (se 2 (by rfl) ⟨4250229, by rfl⟩ : syracuseStep 11333945 = 8500459) B8500459
theorem B7555963 : Blo 1989435 7555963 := bstep (se 1 (by rfl) ⟨5666972, by rfl⟩ : syracuseStep 7555963 = 11333945) B11333945
theorem B10074617 : Blo 1989435 10074617 := bstep (se 2 (by rfl) ⟨3777981, by rfl⟩ : syracuseStep 10074617 = 7555963) B7555963
theorem B6716411 : Blo 1989435 6716411 := bstep (se 1 (by rfl) ⟨5037308, by rfl⟩ : syracuseStep 6716411 = 10074617) B10074617
theorem B4477607 : Blo 1989435 4477607 := bstep (se 1 (by rfl) ⟨3358205, by rfl⟩ : syracuseStep 4477607 = 6716411) B6716411
theorem B2985071 : Blo 1989435 2985071 := bstep (se 1 (by rfl) ⟨2238803, by rfl⟩ : syracuseStep 2985071 = 4477607) B4477607
theorem B1990047 : Blo 1989435 1990047 := bstep (se 1 (by rfl) ⟨1492535, by rfl⟩ : syracuseStep 1990047 = 2985071) B2985071
theorem B2985077 : Blo 1989435 2985077 := bbase (se 5 (by rfl) ⟨139925, by rfl⟩ : syracuseStep 2985077 = 279851) (by norm_num)
theorem B1990051 : Blo 1989435 1990051 := bstep (se 1 (by rfl) ⟨1492538, by rfl⟩ : syracuseStep 1990051 = 2985077) B2985077
theorem B3777997 : Blo 1989435 3777997 := bbase (se 3 (by rfl) ⟨708374, by rfl⟩ : syracuseStep 3777997 = 1416749) (by norm_num)
theorem B5037329 : Blo 1989435 5037329 := bstep (se 2 (by rfl) ⟨1888998, by rfl⟩ : syracuseStep 5037329 = 3777997) B3777997
theorem B3358219 : Blo 1989435 3358219 := bstep (se 1 (by rfl) ⟨2518664, by rfl⟩ : syracuseStep 3358219 = 5037329) B5037329
theorem B4477625 : Blo 1989435 4477625 := bstep (se 2 (by rfl) ⟨1679109, by rfl⟩ : syracuseStep 4477625 = 3358219) B3358219
theorem B2985083 : Blo 1989435 2985083 := bstep (se 1 (by rfl) ⟨2238812, by rfl⟩ : syracuseStep 2985083 = 4477625) B4477625
theorem B1990055 : Blo 1989435 1990055 := bstep (se 1 (by rfl) ⟨1492541, by rfl⟩ : syracuseStep 1990055 = 2985083) B2985083
theorem B2238817 : Blo 1989435 2238817 := bbase (se 2 (by rfl) ⟨839556, by rfl⟩ : syracuseStep 2238817 = 1679113) (by norm_num)
theorem B2985089 : Blo 1989435 2985089 := bstep (se 2 (by rfl) ⟨1119408, by rfl⟩ : syracuseStep 2985089 = 2238817) B2238817
theorem B1990059 : Blo 1989435 1990059 := bstep (se 1 (by rfl) ⟨1492544, by rfl⟩ : syracuseStep 1990059 = 2985089) B2985089
theorem B5037349 : Blo 1989435 5037349 := bbase (se 4 (by rfl) ⟨472251, by rfl⟩ : syracuseStep 5037349 = 944503) (by norm_num)
theorem B6716465 : Blo 1989435 6716465 := bstep (se 2 (by rfl) ⟨2518674, by rfl⟩ : syracuseStep 6716465 = 5037349) B5037349
theorem B4477643 : Blo 1989435 4477643 := bstep (se 1 (by rfl) ⟨3358232, by rfl⟩ : syracuseStep 4477643 = 6716465) B6716465
theorem B2985095 : Blo 1989435 2985095 := bstep (se 1 (by rfl) ⟨2238821, by rfl⟩ : syracuseStep 2985095 = 4477643) B4477643
theorem B1990063 : Blo 1989435 1990063 := bstep (se 1 (by rfl) ⟨1492547, by rfl⟩ : syracuseStep 1990063 = 2985095) B2985095
theorem B2985101 : Blo 1989435 2985101 := bbase (se 3 (by rfl) ⟨559706, by rfl⟩ : syracuseStep 2985101 = 1119413) (by norm_num)
theorem B1990067 : Blo 1989435 1990067 := bstep (se 1 (by rfl) ⟨1492550, by rfl⟩ : syracuseStep 1990067 = 2985101) B2985101
theorem B4477661 : Blo 1989435 4477661 := bbase (se 3 (by rfl) ⟨839561, by rfl⟩ : syracuseStep 4477661 = 1679123) (by norm_num)
theorem B2985107 : Blo 1989435 2985107 := bstep (se 1 (by rfl) ⟨2238830, by rfl⟩ : syracuseStep 2985107 = 4477661) B4477661
theorem B1990071 : Blo 1989435 1990071 := bstep (se 1 (by rfl) ⟨1492553, by rfl⟩ : syracuseStep 1990071 = 2985107) B2985107
theorem B3358253 : Blo 1989435 3358253 := bbase (se 3 (by rfl) ⟨629672, by rfl⟩ : syracuseStep 3358253 = 1259345) (by norm_num)
theorem B2238835 : Blo 1989435 2238835 := bstep (se 1 (by rfl) ⟨1679126, by rfl⟩ : syracuseStep 2238835 = 3358253) B3358253
theorem B2985113 : Blo 1989435 2985113 := bstep (se 2 (by rfl) ⟨1119417, by rfl⟩ : syracuseStep 2985113 = 2238835) B2238835
theorem B1990075 : Blo 1989435 1990075 := bstep (se 1 (by rfl) ⟨1492556, by rfl⟩ : syracuseStep 1990075 = 2985113) B2985113
theorem B20703125 : Blo 1989435 20703125 := bbase (se 6 (by rfl) ⟨485229, by rfl⟩ : syracuseStep 20703125 = 970459) (by norm_num)
theorem B13802083 : Blo 1989435 13802083 := bstep (se 1 (by rfl) ⟨10351562, by rfl⟩ : syracuseStep 13802083 = 20703125) B20703125
theorem B73611109 : Blo 1989435 73611109 := bstep (se 4 (by rfl) ⟨6901041, by rfl⟩ : syracuseStep 73611109 = 13802083) B13802083
theorem B98148145 : Blo 1989435 98148145 := bstep (se 2 (by rfl) ⟨36805554, by rfl⟩ : syracuseStep 98148145 = 73611109) B73611109
theorem B130864193 : Blo 1989435 130864193 := bstep (se 2 (by rfl) ⟨49074072, by rfl⟩ : syracuseStep 130864193 = 98148145) B98148145
theorem B87242795 : Blo 1989435 87242795 := bstep (se 1 (by rfl) ⟨65432096, by rfl⟩ : syracuseStep 87242795 = 130864193) B130864193
theorem B58161863 : Blo 1989435 58161863 := bstep (se 1 (by rfl) ⟨43621397, by rfl⟩ : syracuseStep 58161863 = 87242795) B87242795
theorem B38774575 : Blo 1989435 38774575 := bstep (se 1 (by rfl) ⟨29080931, by rfl⟩ : syracuseStep 38774575 = 58161863) B58161863
theorem B51699433 : Blo 1989435 51699433 := bstep (se 2 (by rfl) ⟨19387287, by rfl⟩ : syracuseStep 51699433 = 38774575) B38774575
theorem B68932577 : Blo 1989435 68932577 := bstep (se 2 (by rfl) ⟨25849716, by rfl⟩ : syracuseStep 68932577 = 51699433) B51699433
theorem B183820205 : Blo 1989435 183820205 := bstep (se 3 (by rfl) ⟨34466288, by rfl⟩ : syracuseStep 183820205 = 68932577) B68932577
theorem B122546803 : Blo 1989435 122546803 := bstep (se 1 (by rfl) ⟨91910102, by rfl⟩ : syracuseStep 122546803 = 183820205) B183820205
theorem B163395737 : Blo 1989435 163395737 := bstep (se 2 (by rfl) ⟨61273401, by rfl⟩ : syracuseStep 163395737 = 122546803) B122546803
theorem B108930491 : Blo 1989435 108930491 := bstep (se 1 (by rfl) ⟨81697868, by rfl⟩ : syracuseStep 108930491 = 163395737) B163395737
theorem B72620327 : Blo 1989435 72620327 := bstep (se 1 (by rfl) ⟨54465245, by rfl⟩ : syracuseStep 72620327 = 108930491) B108930491
theorem B48413551 : Blo 1989435 48413551 := bstep (se 1 (by rfl) ⟨36310163, by rfl⟩ : syracuseStep 48413551 = 72620327) B72620327
theorem B64551401 : Blo 1989435 64551401 := bstep (se 2 (by rfl) ⟨24206775, by rfl⟩ : syracuseStep 64551401 = 48413551) B48413551
theorem B43034267 : Blo 1989435 43034267 := bstep (se 1 (by rfl) ⟨32275700, by rfl⟩ : syracuseStep 43034267 = 64551401) B64551401
theorem B28689511 : Blo 1989435 28689511 := bstep (se 1 (by rfl) ⟨21517133, by rfl⟩ : syracuseStep 28689511 = 43034267) B43034267
theorem B38252681 : Blo 1989435 38252681 := bstep (se 2 (by rfl) ⟨14344755, by rfl⟩ : syracuseStep 38252681 = 28689511) B28689511
theorem B25501787 : Blo 1989435 25501787 := bstep (se 1 (by rfl) ⟨19126340, by rfl⟩ : syracuseStep 25501787 = 38252681) B38252681
theorem B17001191 : Blo 1989435 17001191 := bstep (se 1 (by rfl) ⟨12750893, by rfl⟩ : syracuseStep 17001191 = 25501787) B25501787
theorem B11334127 : Blo 1989435 11334127 := bstep (se 1 (by rfl) ⟨8500595, by rfl⟩ : syracuseStep 11334127 = 17001191) B17001191
theorem B15112169 : Blo 1989435 15112169 := bstep (se 2 (by rfl) ⟨5667063, by rfl⟩ : syracuseStep 15112169 = 11334127) B11334127
theorem B10074779 : Blo 1989435 10074779 := bstep (se 1 (by rfl) ⟨7556084, by rfl⟩ : syracuseStep 10074779 = 15112169) B15112169
theorem B6716519 : Blo 1989435 6716519 := bstep (se 1 (by rfl) ⟨5037389, by rfl⟩ : syracuseStep 6716519 = 10074779) B10074779
theorem B4477679 : Blo 1989435 4477679 := bstep (se 1 (by rfl) ⟨3358259, by rfl⟩ : syracuseStep 4477679 = 6716519) B6716519
theorem B2985119 : Blo 1989435 2985119 := bstep (se 1 (by rfl) ⟨2238839, by rfl⟩ : syracuseStep 2985119 = 4477679) B4477679
theorem B1990079 : Blo 1989435 1990079 := bstep (se 1 (by rfl) ⟨1492559, by rfl⟩ : syracuseStep 1990079 = 2985119) B2985119
theorem B2985125 : Blo 1989435 2985125 := bbase (se 4 (by rfl) ⟨279855, by rfl⟩ : syracuseStep 2985125 = 559711) (by norm_num)
theorem B1990083 : Blo 1989435 1990083 := bstep (se 1 (by rfl) ⟨1492562, by rfl⟩ : syracuseStep 1990083 = 2985125) B2985125
theorem B2518705 : Blo 1989435 2518705 := bbase (se 2 (by rfl) ⟨944514, by rfl⟩ : syracuseStep 2518705 = 1889029) (by norm_num)
theorem B3358273 : Blo 1989435 3358273 := bstep (se 2 (by rfl) ⟨1259352, by rfl⟩ : syracuseStep 3358273 = 2518705) B2518705
theorem B4477697 : Blo 1989435 4477697 := bstep (se 2 (by rfl) ⟨1679136, by rfl⟩ : syracuseStep 4477697 = 3358273) B3358273
theorem B2985131 : Blo 1989435 2985131 := bstep (se 1 (by rfl) ⟨2238848, by rfl⟩ : syracuseStep 2985131 = 4477697) B4477697
theorem B1990087 : Blo 1989435 1990087 := bstep (se 1 (by rfl) ⟨1492565, by rfl⟩ : syracuseStep 1990087 = 2985131) B2985131
theorem B2238853 : Blo 1989435 2238853 := bbase (se 4 (by rfl) ⟨209892, by rfl⟩ : syracuseStep 2238853 = 419785) (by norm_num)
theorem B2985137 : Blo 1989435 2985137 := bstep (se 2 (by rfl) ⟨1119426, by rfl⟩ : syracuseStep 2985137 = 2238853) B2238853
theorem B1990091 : Blo 1989435 1990091 := bstep (se 1 (by rfl) ⟨1492568, by rfl⟩ : syracuseStep 1990091 = 2985137) B2985137
theorem B4250333 : Blo 1989435 4250333 := bbase (se 3 (by rfl) ⟨796937, by rfl⟩ : syracuseStep 4250333 = 1593875) (by norm_num)
theorem B2833555 : Blo 1989435 2833555 := bstep (se 1 (by rfl) ⟨2125166, by rfl⟩ : syracuseStep 2833555 = 4250333) B4250333
theorem B3778073 : Blo 1989435 3778073 := bstep (se 2 (by rfl) ⟨1416777, by rfl⟩ : syracuseStep 3778073 = 2833555) B2833555
theorem B2518715 : Blo 1989435 2518715 := bstep (se 1 (by rfl) ⟨1889036, by rfl⟩ : syracuseStep 2518715 = 3778073) B3778073
theorem B6716573 : Blo 1989435 6716573 := bstep (se 3 (by rfl) ⟨1259357, by rfl⟩ : syracuseStep 6716573 = 2518715) B2518715
theorem B4477715 : Blo 1989435 4477715 := bstep (se 1 (by rfl) ⟨3358286, by rfl⟩ : syracuseStep 4477715 = 6716573) B6716573
theorem B2985143 : Blo 1989435 2985143 := bstep (se 1 (by rfl) ⟨2238857, by rfl⟩ : syracuseStep 2985143 = 4477715) B4477715
theorem B1990095 : Blo 1989435 1990095 := bstep (se 1 (by rfl) ⟨1492571, by rfl⟩ : syracuseStep 1990095 = 2985143) B2985143
theorem B2985149 : Blo 1989435 2985149 := bbase (se 3 (by rfl) ⟨559715, by rfl⟩ : syracuseStep 2985149 = 1119431) (by norm_num)
theorem B1990099 : Blo 1989435 1990099 := bstep (se 1 (by rfl) ⟨1492574, by rfl⟩ : syracuseStep 1990099 = 2985149) B2985149
theorem B4477733 : Blo 1989435 4477733 := bbase (se 4 (by rfl) ⟨419787, by rfl⟩ : syracuseStep 4477733 = 839575) (by norm_num)
theorem B2985155 : Blo 1989435 2985155 := bstep (se 1 (by rfl) ⟨2238866, by rfl⟩ : syracuseStep 2985155 = 4477733) B4477733
theorem B1990103 : Blo 1989435 1990103 := bstep (se 1 (by rfl) ⟨1492577, by rfl⟩ : syracuseStep 1990103 = 2985155) B2985155
theorem B5037461 : Blo 1989435 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B3358307 : Blo 1989435 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B2238871 : Blo 1989435 2238871 := bstep (se 1 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 2238871 = 3358307) B3358307
theorem B2985161 : Blo 1989435 2985161 := bstep (se 2 (by rfl) ⟨1119435, by rfl⟩ : syracuseStep 2985161 = 2238871) B2238871
theorem B1990107 : Blo 1989435 1990107 := bstep (se 1 (by rfl) ⟨1492580, by rfl⟩ : syracuseStep 1990107 = 2985161) B2985161
theorem B4538845 : Blo 1989435 4538845 := bbase (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) (by norm_num)
theorem B24207173 : Blo 1989435 24207173 := bstep (se 4 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 24207173 = 4538845) B4538845
theorem B16138115 : Blo 1989435 16138115 := bstep (se 1 (by rfl) ⟨12103586, by rfl⟩ : syracuseStep 16138115 = 24207173) B24207173
theorem B10758743 : Blo 1989435 10758743 := bstep (se 1 (by rfl) ⟨8069057, by rfl⟩ : syracuseStep 10758743 = 16138115) B16138115
theorem B7172495 : Blo 1989435 7172495 := bstep (se 1 (by rfl) ⟨5379371, by rfl⟩ : syracuseStep 7172495 = 10758743) B10758743
theorem B4781663 : Blo 1989435 4781663 := bstep (se 1 (by rfl) ⟨3586247, by rfl⟩ : syracuseStep 4781663 = 7172495) B7172495
theorem B3187775 : Blo 1989435 3187775 := bstep (se 1 (by rfl) ⟨2390831, by rfl⟩ : syracuseStep 3187775 = 4781663) B4781663
theorem B8500733 : Blo 1989435 8500733 := bstep (se 3 (by rfl) ⟨1593887, by rfl⟩ : syracuseStep 8500733 = 3187775) B3187775
theorem B5667155 : Blo 1989435 5667155 := bstep (se 1 (by rfl) ⟨4250366, by rfl⟩ : syracuseStep 5667155 = 8500733) B8500733
theorem B3778103 : Blo 1989435 3778103 := bstep (se 1 (by rfl) ⟨2833577, by rfl⟩ : syracuseStep 3778103 = 5667155) B5667155
theorem B10074941 : Blo 1989435 10074941 := bstep (se 3 (by rfl) ⟨1889051, by rfl⟩ : syracuseStep 10074941 = 3778103) B3778103
theorem B6716627 : Blo 1989435 6716627 := bstep (se 1 (by rfl) ⟨5037470, by rfl⟩ : syracuseStep 6716627 = 10074941) B10074941
theorem B4477751 : Blo 1989435 4477751 := bstep (se 1 (by rfl) ⟨3358313, by rfl⟩ : syracuseStep 4477751 = 6716627) B6716627
theorem B2985167 : Blo 1989435 2985167 := bstep (se 1 (by rfl) ⟨2238875, by rfl⟩ : syracuseStep 2985167 = 4477751) B4477751
theorem B1990111 : Blo 1989435 1990111 := bstep (se 1 (by rfl) ⟨1492583, by rfl⟩ : syracuseStep 1990111 = 2985167) B2985167
theorem B2985173 : Blo 1989435 2985173 := bbase (se 7 (by rfl) ⟨34982, by rfl⟩ : syracuseStep 2985173 = 69965) (by norm_num)
theorem B1990115 : Blo 1989435 1990115 := bstep (se 1 (by rfl) ⟨1492586, by rfl⟩ : syracuseStep 1990115 = 2985173) B2985173
theorem B2833589 : Blo 1989435 2833589 := bbase (se 5 (by rfl) ⟨132824, by rfl⟩ : syracuseStep 2833589 = 265649) (by norm_num)
theorem B7556237 : Blo 1989435 7556237 := bstep (se 3 (by rfl) ⟨1416794, by rfl⟩ : syracuseStep 7556237 = 2833589) B2833589
theorem B5037491 : Blo 1989435 5037491 := bstep (se 1 (by rfl) ⟨3778118, by rfl⟩ : syracuseStep 5037491 = 7556237) B7556237
theorem B3358327 : Blo 1989435 3358327 := bstep (se 1 (by rfl) ⟨2518745, by rfl⟩ : syracuseStep 3358327 = 5037491) B5037491
theorem B4477769 : Blo 1989435 4477769 := bstep (se 2 (by rfl) ⟨1679163, by rfl⟩ : syracuseStep 4477769 = 3358327) B3358327
theorem B2985179 : Blo 1989435 2985179 := bstep (se 1 (by rfl) ⟨2238884, by rfl⟩ : syracuseStep 2985179 = 4477769) B4477769
theorem B1990119 : Blo 1989435 1990119 := bstep (se 1 (by rfl) ⟨1492589, by rfl⟩ : syracuseStep 1990119 = 2985179) B2985179
theorem B2238889 : Blo 1989435 2238889 := bbase (se 2 (by rfl) ⟨839583, by rfl⟩ : syracuseStep 2238889 = 1679167) (by norm_num)
theorem B2985185 : Blo 1989435 2985185 := bstep (se 2 (by rfl) ⟨1119444, by rfl⟩ : syracuseStep 2985185 = 2238889) B2238889
theorem B1990123 : Blo 1989435 1990123 := bstep (se 1 (by rfl) ⟨1492592, by rfl⟩ : syracuseStep 1990123 = 2985185) B2985185
theorem B4781701 : Blo 1989435 4781701 := bbase (se 4 (by rfl) ⟨448284, by rfl⟩ : syracuseStep 4781701 = 896569) (by norm_num)
theorem B6375601 : Blo 1989435 6375601 := bstep (se 2 (by rfl) ⟨2390850, by rfl⟩ : syracuseStep 6375601 = 4781701) B4781701
theorem B8500801 : Blo 1989435 8500801 := bstep (se 2 (by rfl) ⟨3187800, by rfl⟩ : syracuseStep 8500801 = 6375601) B6375601
theorem B11334401 : Blo 1989435 11334401 := bstep (se 2 (by rfl) ⟨4250400, by rfl⟩ : syracuseStep 11334401 = 8500801) B8500801
theorem B7556267 : Blo 1989435 7556267 := bstep (se 1 (by rfl) ⟨5667200, by rfl⟩ : syracuseStep 7556267 = 11334401) B11334401
theorem B5037511 : Blo 1989435 5037511 := bstep (se 1 (by rfl) ⟨3778133, by rfl⟩ : syracuseStep 5037511 = 7556267) B7556267
theorem B6716681 : Blo 1989435 6716681 := bstep (se 2 (by rfl) ⟨2518755, by rfl⟩ : syracuseStep 6716681 = 5037511) B5037511
theorem B4477787 : Blo 1989435 4477787 := bstep (se 1 (by rfl) ⟨3358340, by rfl⟩ : syracuseStep 4477787 = 6716681) B6716681
theorem B2985191 : Blo 1989435 2985191 := bstep (se 1 (by rfl) ⟨2238893, by rfl⟩ : syracuseStep 2985191 = 4477787) B4477787
theorem B1990127 : Blo 1989435 1990127 := bstep (se 1 (by rfl) ⟨1492595, by rfl⟩ : syracuseStep 1990127 = 2985191) B2985191
theorem B2985197 : Blo 1989435 2985197 := bbase (se 3 (by rfl) ⟨559724, by rfl⟩ : syracuseStep 2985197 = 1119449) (by norm_num)
theorem B1990131 : Blo 1989435 1990131 := bstep (se 1 (by rfl) ⟨1492598, by rfl⟩ : syracuseStep 1990131 = 2985197) B2985197
theorem B4477805 : Blo 1989435 4477805 := bbase (se 3 (by rfl) ⟨839588, by rfl⟩ : syracuseStep 4477805 = 1679177) (by norm_num)
theorem B2985203 : Blo 1989435 2985203 := bstep (se 1 (by rfl) ⟨2238902, by rfl⟩ : syracuseStep 2985203 = 4477805) B4477805
theorem B1990135 : Blo 1989435 1990135 := bstep (se 1 (by rfl) ⟨1492601, by rfl⟩ : syracuseStep 1990135 = 2985203) B2985203
theorem B3778157 : Blo 1989435 3778157 := bbase (se 3 (by rfl) ⟨708404, by rfl⟩ : syracuseStep 3778157 = 1416809) (by norm_num)
theorem B2518771 : Blo 1989435 2518771 := bstep (se 1 (by rfl) ⟨1889078, by rfl⟩ : syracuseStep 2518771 = 3778157) B3778157
theorem B3358361 : Blo 1989435 3358361 := bstep (se 2 (by rfl) ⟨1259385, by rfl⟩ : syracuseStep 3358361 = 2518771) B2518771
theorem B2238907 : Blo 1989435 2238907 := bstep (se 1 (by rfl) ⟨1679180, by rfl⟩ : syracuseStep 2238907 = 3358361) B3358361
theorem B2985209 : Blo 1989435 2985209 := bstep (se 2 (by rfl) ⟨1119453, by rfl⟩ : syracuseStep 2985209 = 2238907) B2238907
theorem B1990139 : Blo 1989435 1990139 := bstep (se 1 (by rfl) ⟨1492604, by rfl⟩ : syracuseStep 1990139 = 2985209) B2985209
theorem B7270469 : Blo 1989435 7270469 := bbase (se 4 (by rfl) ⟨681606, by rfl⟩ : syracuseStep 7270469 = 1363213) (by norm_num)
theorem B4846979 : Blo 1989435 4846979 := bstep (se 1 (by rfl) ⟨3635234, by rfl⟩ : syracuseStep 4846979 = 7270469) B7270469
theorem B12925277 : Blo 1989435 12925277 := bstep (se 3 (by rfl) ⟨2423489, by rfl⟩ : syracuseStep 12925277 = 4846979) B4846979
theorem B8616851 : Blo 1989435 8616851 := bstep (se 1 (by rfl) ⟨6462638, by rfl⟩ : syracuseStep 8616851 = 12925277) B12925277
theorem B5744567 : Blo 1989435 5744567 := bstep (se 1 (by rfl) ⟨4308425, by rfl⟩ : syracuseStep 5744567 = 8616851) B8616851
theorem B15318845 : Blo 1989435 15318845 := bstep (se 3 (by rfl) ⟨2872283, by rfl⟩ : syracuseStep 15318845 = 5744567) B5744567
theorem B10212563 : Blo 1989435 10212563 := bstep (se 1 (by rfl) ⟨7659422, by rfl⟩ : syracuseStep 10212563 = 15318845) B15318845
theorem B6808375 : Blo 1989435 6808375 := bstep (se 1 (by rfl) ⟨5106281, by rfl⟩ : syracuseStep 6808375 = 10212563) B10212563
theorem B9077833 : Blo 1989435 9077833 := bstep (se 2 (by rfl) ⟨3404187, by rfl⟩ : syracuseStep 9077833 = 6808375) B6808375
theorem B12103777 : Blo 1989435 12103777 := bstep (se 2 (by rfl) ⟨4538916, by rfl⟩ : syracuseStep 12103777 = 9077833) B9077833
theorem B16138369 : Blo 1989435 16138369 := bstep (se 2 (by rfl) ⟨6051888, by rfl⟩ : syracuseStep 16138369 = 12103777) B12103777
theorem B21517825 : Blo 1989435 21517825 := bstep (se 2 (by rfl) ⟨8069184, by rfl⟩ : syracuseStep 21517825 = 16138369) B16138369
theorem B28690433 : Blo 1989435 28690433 := bstep (se 2 (by rfl) ⟨10758912, by rfl⟩ : syracuseStep 28690433 = 21517825) B21517825
theorem B19126955 : Blo 1989435 19126955 := bstep (se 1 (by rfl) ⟨14345216, by rfl⟩ : syracuseStep 19126955 = 28690433) B28690433
theorem B51005213 : Blo 1989435 51005213 := bstep (se 3 (by rfl) ⟨9563477, by rfl⟩ : syracuseStep 51005213 = 19126955) B19126955
theorem B34003475 : Blo 1989435 34003475 := bstep (se 1 (by rfl) ⟨25502606, by rfl⟩ : syracuseStep 34003475 = 51005213) B51005213
theorem B22668983 : Blo 1989435 22668983 := bstep (se 1 (by rfl) ⟨17001737, by rfl⟩ : syracuseStep 22668983 = 34003475) B34003475
theorem B15112655 : Blo 1989435 15112655 := bstep (se 1 (by rfl) ⟨11334491, by rfl⟩ : syracuseStep 15112655 = 22668983) B22668983
theorem B10075103 : Blo 1989435 10075103 := bstep (se 1 (by rfl) ⟨7556327, by rfl⟩ : syracuseStep 10075103 = 15112655) B15112655
theorem B6716735 : Blo 1989435 6716735 := bstep (se 1 (by rfl) ⟨5037551, by rfl⟩ : syracuseStep 6716735 = 10075103) B10075103
theorem B4477823 : Blo 1989435 4477823 := bstep (se 1 (by rfl) ⟨3358367, by rfl⟩ : syracuseStep 4477823 = 6716735) B6716735
theorem B2985215 : Blo 1989435 2985215 := bstep (se 1 (by rfl) ⟨2238911, by rfl⟩ : syracuseStep 2985215 = 4477823) B4477823
theorem B1990143 : Blo 1989435 1990143 := bstep (se 1 (by rfl) ⟨1492607, by rfl⟩ : syracuseStep 1990143 = 2985215) B2985215
theorem B2985221 : Blo 1989435 2985221 := bbase (se 4 (by rfl) ⟨279864, by rfl⟩ : syracuseStep 2985221 = 559729) (by norm_num)
theorem B1990147 : Blo 1989435 1990147 := bstep (se 1 (by rfl) ⟨1492610, by rfl⟩ : syracuseStep 1990147 = 2985221) B2985221
theorem B3358381 : Blo 1989435 3358381 := bbase (se 3 (by rfl) ⟨629696, by rfl⟩ : syracuseStep 3358381 = 1259393) (by norm_num)
theorem B4477841 : Blo 1989435 4477841 := bstep (se 2 (by rfl) ⟨1679190, by rfl⟩ : syracuseStep 4477841 = 3358381) B3358381
theorem B2985227 : Blo 1989435 2985227 := bstep (se 1 (by rfl) ⟨2238920, by rfl⟩ : syracuseStep 2985227 = 4477841) B4477841
theorem B1990151 : Blo 1989435 1990151 := bstep (se 1 (by rfl) ⟨1492613, by rfl⟩ : syracuseStep 1990151 = 2985227) B2985227
theorem B2238925 : Blo 1989435 2238925 := bbase (se 3 (by rfl) ⟨419798, by rfl⟩ : syracuseStep 2238925 = 839597) (by norm_num)
theorem B2985233 : Blo 1989435 2985233 := bstep (se 2 (by rfl) ⟨1119462, by rfl⟩ : syracuseStep 2985233 = 2238925) B2238925
theorem B1990155 : Blo 1989435 1990155 := bstep (se 1 (by rfl) ⟨1492616, by rfl⟩ : syracuseStep 1990155 = 2985233) B2985233
theorem B6716789 : Blo 1989435 6716789 := bbase (se 5 (by rfl) ⟨314849, by rfl⟩ : syracuseStep 6716789 = 629699) (by norm_num)
theorem B4477859 : Blo 1989435 4477859 := bstep (se 1 (by rfl) ⟨3358394, by rfl⟩ : syracuseStep 4477859 = 6716789) B6716789
theorem B2985239 : Blo 1989435 2985239 := bstep (se 1 (by rfl) ⟨2238929, by rfl⟩ : syracuseStep 2985239 = 4477859) B4477859
theorem B1990159 : Blo 1989435 1990159 := bstep (se 1 (by rfl) ⟨1492619, by rfl⟩ : syracuseStep 1990159 = 2985239) B2985239
theorem B2985245 : Blo 1989435 2985245 := bbase (se 3 (by rfl) ⟨559733, by rfl⟩ : syracuseStep 2985245 = 1119467) (by norm_num)
theorem B1990163 : Blo 1989435 1990163 := bstep (se 1 (by rfl) ⟨1492622, by rfl⟩ : syracuseStep 1990163 = 2985245) B2985245
theorem B4477877 : Blo 1989435 4477877 := bbase (se 5 (by rfl) ⟨209900, by rfl⟩ : syracuseStep 4477877 = 419801) (by norm_num)
theorem B2985251 : Blo 1989435 2985251 := bstep (se 1 (by rfl) ⟨2238938, by rfl⟩ : syracuseStep 2985251 = 4477877) B4477877
theorem B1990167 : Blo 1989435 1990167 := bstep (se 1 (by rfl) ⟨1492625, by rfl⟩ : syracuseStep 1990167 = 2985251) B2985251
theorem B40850837 : Blo 1989435 40850837 := bbase (se 6 (by rfl) ⟨957441, by rfl⟩ : syracuseStep 40850837 = 1914883) (by norm_num)
theorem B27233891 : Blo 1989435 27233891 := bstep (se 1 (by rfl) ⟨20425418, by rfl⟩ : syracuseStep 27233891 = 40850837) B40850837
theorem B18155927 : Blo 1989435 18155927 := bstep (se 1 (by rfl) ⟨13616945, by rfl⟩ : syracuseStep 18155927 = 27233891) B27233891
theorem B48415805 : Blo 1989435 48415805 := bstep (se 3 (by rfl) ⟨9077963, by rfl⟩ : syracuseStep 48415805 = 18155927) B18155927
theorem B32277203 : Blo 1989435 32277203 := bstep (se 1 (by rfl) ⟨24207902, by rfl⟩ : syracuseStep 32277203 = 48415805) B48415805
theorem B21518135 : Blo 1989435 21518135 := bstep (se 1 (by rfl) ⟨16138601, by rfl⟩ : syracuseStep 21518135 = 32277203) B32277203
theorem B14345423 : Blo 1989435 14345423 := bstep (se 1 (by rfl) ⟨10759067, by rfl⟩ : syracuseStep 14345423 = 21518135) B21518135
theorem B9563615 : Blo 1989435 9563615 := bstep (se 1 (by rfl) ⟨7172711, by rfl⟩ : syracuseStep 9563615 = 14345423) B14345423
theorem B6375743 : Blo 1989435 6375743 := bstep (se 1 (by rfl) ⟨4781807, by rfl⟩ : syracuseStep 6375743 = 9563615) B9563615
theorem B4250495 : Blo 1989435 4250495 := bstep (se 1 (by rfl) ⟨3187871, by rfl⟩ : syracuseStep 4250495 = 6375743) B6375743
theorem B11334653 : Blo 1989435 11334653 := bstep (se 3 (by rfl) ⟨2125247, by rfl⟩ : syracuseStep 11334653 = 4250495) B4250495
theorem B7556435 : Blo 1989435 7556435 := bstep (se 1 (by rfl) ⟨5667326, by rfl⟩ : syracuseStep 7556435 = 11334653) B11334653
theorem B5037623 : Blo 1989435 5037623 := bstep (se 1 (by rfl) ⟨3778217, by rfl⟩ : syracuseStep 5037623 = 7556435) B7556435
theorem B3358415 : Blo 1989435 3358415 := bstep (se 1 (by rfl) ⟨2518811, by rfl⟩ : syracuseStep 3358415 = 5037623) B5037623
theorem B2238943 : Blo 1989435 2238943 := bstep (se 1 (by rfl) ⟨1679207, by rfl⟩ : syracuseStep 2238943 = 3358415) B3358415
theorem B2985257 : Blo 1989435 2985257 := bstep (se 2 (by rfl) ⟨1119471, by rfl⟩ : syracuseStep 2985257 = 2238943) B2238943
theorem B1990171 : Blo 1989435 1990171 := bstep (se 1 (by rfl) ⟨1492628, by rfl⟩ : syracuseStep 1990171 = 2985257) B2985257
theorem B7172725 : Blo 1989435 7172725 := bbase (se 5 (by rfl) ⟨336221, by rfl⟩ : syracuseStep 7172725 = 672443) (by norm_num)
theorem B9563633 : Blo 1989435 9563633 := bstep (se 2 (by rfl) ⟨3586362, by rfl⟩ : syracuseStep 9563633 = 7172725) B7172725
theorem B6375755 : Blo 1989435 6375755 := bstep (se 1 (by rfl) ⟨4781816, by rfl⟩ : syracuseStep 6375755 = 9563633) B9563633
theorem B4250503 : Blo 1989435 4250503 := bstep (se 1 (by rfl) ⟨3187877, by rfl⟩ : syracuseStep 4250503 = 6375755) B6375755
theorem B5667337 : Blo 1989435 5667337 := bstep (se 2 (by rfl) ⟨2125251, by rfl⟩ : syracuseStep 5667337 = 4250503) B4250503
theorem B7556449 : Blo 1989435 7556449 := bstep (se 2 (by rfl) ⟨2833668, by rfl⟩ : syracuseStep 7556449 = 5667337) B5667337
theorem B10075265 : Blo 1989435 10075265 := bstep (se 2 (by rfl) ⟨3778224, by rfl⟩ : syracuseStep 10075265 = 7556449) B7556449
theorem B6716843 : Blo 1989435 6716843 := bstep (se 1 (by rfl) ⟨5037632, by rfl⟩ : syracuseStep 6716843 = 10075265) B10075265
theorem B4477895 : Blo 1989435 4477895 := bstep (se 1 (by rfl) ⟨3358421, by rfl⟩ : syracuseStep 4477895 = 6716843) B6716843
theorem B2985263 : Blo 1989435 2985263 := bstep (se 1 (by rfl) ⟨2238947, by rfl⟩ : syracuseStep 2985263 = 4477895) B4477895
theorem B1990175 : Blo 1989435 1990175 := bstep (se 1 (by rfl) ⟨1492631, by rfl⟩ : syracuseStep 1990175 = 2985263) B2985263
theorem B2985269 : Blo 1989435 2985269 := bbase (se 5 (by rfl) ⟨139934, by rfl⟩ : syracuseStep 2985269 = 279869) (by norm_num)
theorem B1990179 : Blo 1989435 1990179 := bstep (se 1 (by rfl) ⟨1492634, by rfl⟩ : syracuseStep 1990179 = 2985269) B2985269
theorem B5037653 : Blo 1989435 5037653 := bbase (se 8 (by rfl) ⟨29517, by rfl⟩ : syracuseStep 5037653 = 59035) (by norm_num)
theorem B3358435 : Blo 1989435 3358435 := bstep (se 1 (by rfl) ⟨2518826, by rfl⟩ : syracuseStep 3358435 = 5037653) B5037653
theorem B4477913 : Blo 1989435 4477913 := bstep (se 2 (by rfl) ⟨1679217, by rfl⟩ : syracuseStep 4477913 = 3358435) B3358435
theorem B2985275 : Blo 1989435 2985275 := bstep (se 1 (by rfl) ⟨2238956, by rfl⟩ : syracuseStep 2985275 = 4477913) B4477913
theorem B1990183 : Blo 1989435 1990183 := bstep (se 1 (by rfl) ⟨1492637, by rfl⟩ : syracuseStep 1990183 = 2985275) B2985275
theorem B2238961 : Blo 1989435 2238961 := bbase (se 2 (by rfl) ⟨839610, by rfl⟩ : syracuseStep 2238961 = 1679221) (by norm_num)
theorem B2985281 : Blo 1989435 2985281 := bstep (se 2 (by rfl) ⟨1119480, by rfl⟩ : syracuseStep 2985281 = 2238961) B2238961
theorem B1990187 : Blo 1989435 1990187 := bstep (se 1 (by rfl) ⟨1492640, by rfl⟩ : syracuseStep 1990187 = 2985281) B2985281
theorem B3829805 : Blo 1989435 3829805 := bbase (se 3 (by rfl) ⟨718088, by rfl⟩ : syracuseStep 3829805 = 1436177) (by norm_num)
theorem B2553203 : Blo 1989435 2553203 := bstep (se 1 (by rfl) ⟨1914902, by rfl⟩ : syracuseStep 2553203 = 3829805) B3829805
theorem B6808541 : Blo 1989435 6808541 := bstep (se 3 (by rfl) ⟨1276601, by rfl⟩ : syracuseStep 6808541 = 2553203) B2553203
theorem B18156109 : Blo 1989435 18156109 := bstep (se 3 (by rfl) ⟨3404270, by rfl⟩ : syracuseStep 18156109 = 6808541) B6808541
theorem B24208145 : Blo 1989435 24208145 := bstep (se 2 (by rfl) ⟨9078054, by rfl⟩ : syracuseStep 24208145 = 18156109) B18156109
theorem B16138763 : Blo 1989435 16138763 := bstep (se 1 (by rfl) ⟨12104072, by rfl⟩ : syracuseStep 16138763 = 24208145) B24208145
theorem B10759175 : Blo 1989435 10759175 := bstep (se 1 (by rfl) ⟨8069381, by rfl⟩ : syracuseStep 10759175 = 16138763) B16138763
theorem B7172783 : Blo 1989435 7172783 := bstep (se 1 (by rfl) ⟨5379587, by rfl⟩ : syracuseStep 7172783 = 10759175) B10759175
theorem B4781855 : Blo 1989435 4781855 := bstep (se 1 (by rfl) ⟨3586391, by rfl⟩ : syracuseStep 4781855 = 7172783) B7172783
theorem B12751613 : Blo 1989435 12751613 := bstep (se 3 (by rfl) ⟨2390927, by rfl⟩ : syracuseStep 12751613 = 4781855) B4781855
theorem B8501075 : Blo 1989435 8501075 := bstep (se 1 (by rfl) ⟨6375806, by rfl⟩ : syracuseStep 8501075 = 12751613) B12751613
theorem B5667383 : Blo 1989435 5667383 := bstep (se 1 (by rfl) ⟨4250537, by rfl⟩ : syracuseStep 5667383 = 8501075) B8501075
theorem B3778255 : Blo 1989435 3778255 := bstep (se 1 (by rfl) ⟨2833691, by rfl⟩ : syracuseStep 3778255 = 5667383) B5667383
theorem B5037673 : Blo 1989435 5037673 := bstep (se 2 (by rfl) ⟨1889127, by rfl⟩ : syracuseStep 5037673 = 3778255) B3778255
theorem B6716897 : Blo 1989435 6716897 := bstep (se 2 (by rfl) ⟨2518836, by rfl⟩ : syracuseStep 6716897 = 5037673) B5037673
theorem B4477931 : Blo 1989435 4477931 := bstep (se 1 (by rfl) ⟨3358448, by rfl⟩ : syracuseStep 4477931 = 6716897) B6716897
theorem B2985287 : Blo 1989435 2985287 := bstep (se 1 (by rfl) ⟨2238965, by rfl⟩ : syracuseStep 2985287 = 4477931) B4477931
theorem B1990191 : Blo 1989435 1990191 := bstep (se 1 (by rfl) ⟨1492643, by rfl⟩ : syracuseStep 1990191 = 2985287) B2985287
theorem B2985293 : Blo 1989435 2985293 := bbase (se 3 (by rfl) ⟨559742, by rfl⟩ : syracuseStep 2985293 = 1119485) (by norm_num)
theorem B1990195 : Blo 1989435 1990195 := bstep (se 1 (by rfl) ⟨1492646, by rfl⟩ : syracuseStep 1990195 = 2985293) B2985293
theorem B4477949 : Blo 1989435 4477949 := bbase (se 3 (by rfl) ⟨839615, by rfl⟩ : syracuseStep 4477949 = 1679231) (by norm_num)
theorem B2985299 : Blo 1989435 2985299 := bstep (se 1 (by rfl) ⟨2238974, by rfl⟩ : syracuseStep 2985299 = 4477949) B4477949
theorem B1990199 : Blo 1989435 1990199 := bstep (se 1 (by rfl) ⟨1492649, by rfl⟩ : syracuseStep 1990199 = 2985299) B2985299
theorem B3358469 : Blo 1989435 3358469 := bbase (se 4 (by rfl) ⟨314856, by rfl⟩ : syracuseStep 3358469 = 629713) (by norm_num)
theorem B2238979 : Blo 1989435 2238979 := bstep (se 1 (by rfl) ⟨1679234, by rfl⟩ : syracuseStep 2238979 = 3358469) B3358469
theorem B2985305 : Blo 1989435 2985305 := bstep (se 2 (by rfl) ⟨1119489, by rfl⟩ : syracuseStep 2985305 = 2238979) B2238979
theorem B1990203 : Blo 1989435 1990203 := bstep (se 1 (by rfl) ⟨1492652, by rfl⟩ : syracuseStep 1990203 = 2985305) B2985305
theorem B15113141 : Blo 1989435 15113141 := bbase (se 5 (by rfl) ⟨708428, by rfl⟩ : syracuseStep 15113141 = 1416857) (by norm_num)
theorem B10075427 : Blo 1989435 10075427 := bstep (se 1 (by rfl) ⟨7556570, by rfl⟩ : syracuseStep 10075427 = 15113141) B15113141
theorem B6716951 : Blo 1989435 6716951 := bstep (se 1 (by rfl) ⟨5037713, by rfl⟩ : syracuseStep 6716951 = 10075427) B10075427
theorem B4477967 : Blo 1989435 4477967 := bstep (se 1 (by rfl) ⟨3358475, by rfl⟩ : syracuseStep 4477967 = 6716951) B6716951
theorem B2985311 : Blo 1989435 2985311 := bstep (se 1 (by rfl) ⟨2238983, by rfl⟩ : syracuseStep 2985311 = 4477967) B4477967
theorem B1990207 : Blo 1989435 1990207 := bstep (se 1 (by rfl) ⟨1492655, by rfl⟩ : syracuseStep 1990207 = 2985311) B2985311
theorem B2985317 : Blo 1989435 2985317 := bbase (se 4 (by rfl) ⟨279873, by rfl⟩ : syracuseStep 2985317 = 559747) (by norm_num)
theorem B1990211 : Blo 1989435 1990211 := bstep (se 1 (by rfl) ⟨1492658, by rfl⟩ : syracuseStep 1990211 = 2985317) B2985317
theorem B3778301 : Blo 1989435 3778301 := bbase (se 3 (by rfl) ⟨708431, by rfl⟩ : syracuseStep 3778301 = 1416863) (by norm_num)
theorem B2518867 : Blo 1989435 2518867 := bstep (se 1 (by rfl) ⟨1889150, by rfl⟩ : syracuseStep 2518867 = 3778301) B3778301
theorem B3358489 : Blo 1989435 3358489 := bstep (se 2 (by rfl) ⟨1259433, by rfl⟩ : syracuseStep 3358489 = 2518867) B2518867
theorem B4477985 : Blo 1989435 4477985 := bstep (se 2 (by rfl) ⟨1679244, by rfl⟩ : syracuseStep 4477985 = 3358489) B3358489
theorem B2985323 : Blo 1989435 2985323 := bstep (se 1 (by rfl) ⟨2238992, by rfl⟩ : syracuseStep 2985323 = 4477985) B4477985
theorem B1990215 : Blo 1989435 1990215 := bstep (se 1 (by rfl) ⟨1492661, by rfl⟩ : syracuseStep 1990215 = 2985323) B2985323
theorem B2238997 : Blo 1989435 2238997 := bbase (se 6 (by rfl) ⟨52476, by rfl⟩ : syracuseStep 2238997 = 104953) (by norm_num)
theorem B2985329 : Blo 1989435 2985329 := bstep (se 2 (by rfl) ⟨1119498, by rfl⟩ : syracuseStep 2985329 = 2238997) B2238997
theorem B1990219 : Blo 1989435 1990219 := bstep (se 1 (by rfl) ⟨1492664, by rfl⟩ : syracuseStep 1990219 = 2985329) B2985329
theorem B2518877 : Blo 1989435 2518877 := bbase (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) (by norm_num)
theorem B6717005 : Blo 1989435 6717005 := bstep (se 3 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 6717005 = 2518877) B2518877
theorem B4478003 : Blo 1989435 4478003 := bstep (se 1 (by rfl) ⟨3358502, by rfl⟩ : syracuseStep 4478003 = 6717005) B6717005
theorem B2985335 : Blo 1989435 2985335 := bstep (se 1 (by rfl) ⟨2239001, by rfl⟩ : syracuseStep 2985335 = 4478003) B4478003
theorem B1990223 : Blo 1989435 1990223 := bstep (se 1 (by rfl) ⟨1492667, by rfl⟩ : syracuseStep 1990223 = 2985335) B2985335
theorem B2985341 : Blo 1989435 2985341 := bbase (se 3 (by rfl) ⟨559751, by rfl⟩ : syracuseStep 2985341 = 1119503) (by norm_num)
theorem B1990227 : Blo 1989435 1990227 := bstep (se 1 (by rfl) ⟨1492670, by rfl⟩ : syracuseStep 1990227 = 2985341) B2985341
theorem B4478021 : Blo 1989435 4478021 := bbase (se 4 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 4478021 = 839629) (by norm_num)
theorem B2985347 : Blo 1989435 2985347 := bstep (se 1 (by rfl) ⟨2239010, by rfl⟩ : syracuseStep 2985347 = 4478021) B4478021
theorem B1990231 : Blo 1989435 1990231 := bstep (se 1 (by rfl) ⟨1492673, by rfl⟩ : syracuseStep 1990231 = 2985347) B2985347
theorem B5667509 : Blo 1989435 5667509 := bbase (se 5 (by rfl) ⟨265664, by rfl⟩ : syracuseStep 5667509 = 531329) (by norm_num)
theorem B3778339 : Blo 1989435 3778339 := bstep (se 1 (by rfl) ⟨2833754, by rfl⟩ : syracuseStep 3778339 = 5667509) B5667509
theorem B5037785 : Blo 1989435 5037785 := bstep (se 2 (by rfl) ⟨1889169, by rfl⟩ : syracuseStep 5037785 = 3778339) B3778339
theorem B3358523 : Blo 1989435 3358523 := bstep (se 1 (by rfl) ⟨2518892, by rfl⟩ : syracuseStep 3358523 = 5037785) B5037785
theorem B2239015 : Blo 1989435 2239015 := bstep (se 1 (by rfl) ⟨1679261, by rfl⟩ : syracuseStep 2239015 = 3358523) B3358523
theorem B2985353 : Blo 1989435 2985353 := bstep (se 2 (by rfl) ⟨1119507, by rfl⟩ : syracuseStep 2985353 = 2239015) B2239015
theorem B1990235 : Blo 1989435 1990235 := bstep (se 1 (by rfl) ⟨1492676, by rfl⟩ : syracuseStep 1990235 = 2985353) B2985353
theorem B10075589 : Blo 1989435 10075589 := bbase (se 4 (by rfl) ⟨944586, by rfl⟩ : syracuseStep 10075589 = 1889173) (by norm_num)
theorem B6717059 : Blo 1989435 6717059 := bstep (se 1 (by rfl) ⟨5037794, by rfl⟩ : syracuseStep 6717059 = 10075589) B10075589
theorem B4478039 : Blo 1989435 4478039 := bstep (se 1 (by rfl) ⟨3358529, by rfl⟩ : syracuseStep 4478039 = 6717059) B6717059
theorem B2985359 : Blo 1989435 2985359 := bstep (se 1 (by rfl) ⟨2239019, by rfl⟩ : syracuseStep 2985359 = 4478039) B4478039
theorem B1990239 : Blo 1989435 1990239 := bstep (se 1 (by rfl) ⟨1492679, by rfl⟩ : syracuseStep 1990239 = 2985359) B2985359
theorem B2985365 : Blo 1989435 2985365 := bbase (se 6 (by rfl) ⟨69969, by rfl⟩ : syracuseStep 2985365 = 139939) (by norm_num)
theorem B1990243 : Blo 1989435 1990243 := bstep (se 1 (by rfl) ⟨1492682, by rfl⟩ : syracuseStep 1990243 = 2985365) B2985365
theorem B3586493 : Blo 1989435 3586493 := bbase (se 3 (by rfl) ⟨672467, by rfl⟩ : syracuseStep 3586493 = 1344935) (by norm_num)
theorem B2390995 : Blo 1989435 2390995 := bstep (se 1 (by rfl) ⟨1793246, by rfl⟩ : syracuseStep 2390995 = 3586493) B3586493
theorem B3187993 : Blo 1989435 3187993 := bstep (se 2 (by rfl) ⟨1195497, by rfl⟩ : syracuseStep 3187993 = 2390995) B2390995
theorem B4250657 : Blo 1989435 4250657 := bstep (se 2 (by rfl) ⟨1593996, by rfl⟩ : syracuseStep 4250657 = 3187993) B3187993
theorem B11335085 : Blo 1989435 11335085 := bstep (se 3 (by rfl) ⟨2125328, by rfl⟩ : syracuseStep 11335085 = 4250657) B4250657
theorem B7556723 : Blo 1989435 7556723 := bstep (se 1 (by rfl) ⟨5667542, by rfl⟩ : syracuseStep 7556723 = 11335085) B11335085
theorem B5037815 : Blo 1989435 5037815 := bstep (se 1 (by rfl) ⟨3778361, by rfl⟩ : syracuseStep 5037815 = 7556723) B7556723
theorem B3358543 : Blo 1989435 3358543 := bstep (se 1 (by rfl) ⟨2518907, by rfl⟩ : syracuseStep 3358543 = 5037815) B5037815
theorem B4478057 : Blo 1989435 4478057 := bstep (se 2 (by rfl) ⟨1679271, by rfl⟩ : syracuseStep 4478057 = 3358543) B3358543
theorem B2985371 : Blo 1989435 2985371 := bstep (se 1 (by rfl) ⟨2239028, by rfl⟩ : syracuseStep 2985371 = 4478057) B4478057
theorem B1990247 : Blo 1989435 1990247 := bstep (se 1 (by rfl) ⟨1492685, by rfl⟩ : syracuseStep 1990247 = 2985371) B2985371
theorem B2239033 : Blo 1989435 2239033 := bbase (se 2 (by rfl) ⟨839637, by rfl⟩ : syracuseStep 2239033 = 1679275) (by norm_num)
theorem B2985377 : Blo 1989435 2985377 := bstep (se 2 (by rfl) ⟨1119516, by rfl⟩ : syracuseStep 2985377 = 2239033) B2239033
theorem B1990251 : Blo 1989435 1990251 := bstep (se 1 (by rfl) ⟨1492688, by rfl⟩ : syracuseStep 1990251 = 2985377) B2985377
theorem B2125337 : Blo 1989435 2125337 := bbase (se 2 (by rfl) ⟨797001, by rfl⟩ : syracuseStep 2125337 = 1594003) (by norm_num)
theorem B5667565 : Blo 1989435 5667565 := bstep (se 3 (by rfl) ⟨1062668, by rfl⟩ : syracuseStep 5667565 = 2125337) B2125337
theorem B7556753 : Blo 1989435 7556753 := bstep (se 2 (by rfl) ⟨2833782, by rfl⟩ : syracuseStep 7556753 = 5667565) B5667565
theorem B5037835 : Blo 1989435 5037835 := bstep (se 1 (by rfl) ⟨3778376, by rfl⟩ : syracuseStep 5037835 = 7556753) B7556753
theorem B6717113 : Blo 1989435 6717113 := bstep (se 2 (by rfl) ⟨2518917, by rfl⟩ : syracuseStep 6717113 = 5037835) B5037835
theorem B4478075 : Blo 1989435 4478075 := bstep (se 1 (by rfl) ⟨3358556, by rfl⟩ : syracuseStep 4478075 = 6717113) B6717113
theorem B2985383 : Blo 1989435 2985383 := bstep (se 1 (by rfl) ⟨2239037, by rfl⟩ : syracuseStep 2985383 = 4478075) B4478075
theorem B1990255 : Blo 1989435 1990255 := bstep (se 1 (by rfl) ⟨1492691, by rfl⟩ : syracuseStep 1990255 = 2985383) B2985383
theorem B2985389 : Blo 1989435 2985389 := bbase (se 3 (by rfl) ⟨559760, by rfl⟩ : syracuseStep 2985389 = 1119521) (by norm_num)
theorem B1990259 : Blo 1989435 1990259 := bstep (se 1 (by rfl) ⟨1492694, by rfl⟩ : syracuseStep 1990259 = 2985389) B2985389
theorem B4478093 : Blo 1989435 4478093 := bbase (se 3 (by rfl) ⟨839642, by rfl⟩ : syracuseStep 4478093 = 1679285) (by norm_num)
theorem B2985395 : Blo 1989435 2985395 := bstep (se 1 (by rfl) ⟨2239046, by rfl⟩ : syracuseStep 2985395 = 4478093) B4478093
theorem B1990263 : Blo 1989435 1990263 := bstep (se 1 (by rfl) ⟨1492697, by rfl⟩ : syracuseStep 1990263 = 2985395) B2985395
theorem B2518933 : Blo 1989435 2518933 := bbase (se 6 (by rfl) ⟨59037, by rfl⟩ : syracuseStep 2518933 = 118075) (by norm_num)
theorem B3358577 : Blo 1989435 3358577 := bstep (se 2 (by rfl) ⟨1259466, by rfl⟩ : syracuseStep 3358577 = 2518933) B2518933
theorem B2239051 : Blo 1989435 2239051 := bstep (se 1 (by rfl) ⟨1679288, by rfl⟩ : syracuseStep 2239051 = 3358577) B3358577
theorem B2985401 : Blo 1989435 2985401 := bstep (se 2 (by rfl) ⟨1119525, by rfl⟩ : syracuseStep 2985401 = 2239051) B2239051
theorem B1990267 : Blo 1989435 1990267 := bstep (se 1 (by rfl) ⟨1492700, by rfl⟩ : syracuseStep 1990267 = 2985401) B2985401
theorem B15319829 : Blo 1989435 15319829 := bbase (se 6 (by rfl) ⟨359058, by rfl⟩ : syracuseStep 15319829 = 718117) (by norm_num)
theorem B10213219 : Blo 1989435 10213219 := bstep (se 1 (by rfl) ⟨7659914, by rfl⟩ : syracuseStep 10213219 = 15319829) B15319829
theorem B54470501 : Blo 1989435 54470501 := bstep (se 4 (by rfl) ⟨5106609, by rfl⟩ : syracuseStep 54470501 = 10213219) B10213219
theorem B36313667 : Blo 1989435 36313667 := bstep (se 1 (by rfl) ⟨27235250, by rfl⟩ : syracuseStep 36313667 = 54470501) B54470501
theorem B24209111 : Blo 1989435 24209111 := bstep (se 1 (by rfl) ⟨18156833, by rfl⟩ : syracuseStep 24209111 = 36313667) B36313667
theorem B16139407 : Blo 1989435 16139407 := bstep (se 1 (by rfl) ⟨12104555, by rfl⟩ : syracuseStep 16139407 = 24209111) B24209111
theorem B21519209 : Blo 1989435 21519209 := bstep (se 2 (by rfl) ⟨8069703, by rfl⟩ : syracuseStep 21519209 = 16139407) B16139407
theorem B57384557 : Blo 1989435 57384557 := bstep (se 3 (by rfl) ⟨10759604, by rfl⟩ : syracuseStep 57384557 = 21519209) B21519209
theorem B38256371 : Blo 1989435 38256371 := bstep (se 1 (by rfl) ⟨28692278, by rfl⟩ : syracuseStep 38256371 = 57384557) B57384557
theorem B25504247 : Blo 1989435 25504247 := bstep (se 1 (by rfl) ⟨19128185, by rfl⟩ : syracuseStep 25504247 = 38256371) B38256371
theorem B17002831 : Blo 1989435 17002831 := bstep (se 1 (by rfl) ⟨12752123, by rfl⟩ : syracuseStep 17002831 = 25504247) B25504247
theorem B22670441 : Blo 1989435 22670441 := bstep (se 2 (by rfl) ⟨8501415, by rfl⟩ : syracuseStep 22670441 = 17002831) B17002831
theorem B15113627 : Blo 1989435 15113627 := bstep (se 1 (by rfl) ⟨11335220, by rfl⟩ : syracuseStep 15113627 = 22670441) B22670441
theorem B10075751 : Blo 1989435 10075751 := bstep (se 1 (by rfl) ⟨7556813, by rfl⟩ : syracuseStep 10075751 = 15113627) B15113627
theorem B6717167 : Blo 1989435 6717167 := bstep (se 1 (by rfl) ⟨5037875, by rfl⟩ : syracuseStep 6717167 = 10075751) B10075751
theorem B4478111 : Blo 1989435 4478111 := bstep (se 1 (by rfl) ⟨3358583, by rfl⟩ : syracuseStep 4478111 = 6717167) B6717167
theorem B2985407 : Blo 1989435 2985407 := bstep (se 1 (by rfl) ⟨2239055, by rfl⟩ : syracuseStep 2985407 = 4478111) B4478111
theorem B1990271 : Blo 1989435 1990271 := bstep (se 1 (by rfl) ⟨1492703, by rfl⟩ : syracuseStep 1990271 = 2985407) B2985407
theorem B2985413 : Blo 1989435 2985413 := bbase (se 4 (by rfl) ⟨279882, by rfl⟩ : syracuseStep 2985413 = 559765) (by norm_num)
theorem B1990275 : Blo 1989435 1990275 := bstep (se 1 (by rfl) ⟨1492706, by rfl⟩ : syracuseStep 1990275 = 2985413) B2985413
theorem B3358597 : Blo 1989435 3358597 := bbase (se 4 (by rfl) ⟨314868, by rfl⟩ : syracuseStep 3358597 = 629737) (by norm_num)
theorem B4478129 : Blo 1989435 4478129 := bstep (se 2 (by rfl) ⟨1679298, by rfl⟩ : syracuseStep 4478129 = 3358597) B3358597
theorem B2985419 : Blo 1989435 2985419 := bstep (se 1 (by rfl) ⟨2239064, by rfl⟩ : syracuseStep 2985419 = 4478129) B4478129
theorem B1990279 : Blo 1989435 1990279 := bstep (se 1 (by rfl) ⟨1492709, by rfl⟩ : syracuseStep 1990279 = 2985419) B2985419
theorem B2239069 : Blo 1989435 2239069 := bbase (se 3 (by rfl) ⟨419825, by rfl⟩ : syracuseStep 2239069 = 839651) (by norm_num)
theorem B2985425 : Blo 1989435 2985425 := bstep (se 2 (by rfl) ⟨1119534, by rfl⟩ : syracuseStep 2985425 = 2239069) B2239069
theorem B1990283 : Blo 1989435 1990283 := bstep (se 1 (by rfl) ⟨1492712, by rfl⟩ : syracuseStep 1990283 = 2985425) B2985425
theorem B6717221 : Blo 1989435 6717221 := bbase (se 4 (by rfl) ⟨629739, by rfl⟩ : syracuseStep 6717221 = 1259479) (by norm_num)
theorem B4478147 : Blo 1989435 4478147 := bstep (se 1 (by rfl) ⟨3358610, by rfl⟩ : syracuseStep 4478147 = 6717221) B6717221
theorem B2985431 : Blo 1989435 2985431 := bstep (se 1 (by rfl) ⟨2239073, by rfl⟩ : syracuseStep 2985431 = 4478147) B4478147
theorem B1990287 : Blo 1989435 1990287 := bstep (se 1 (by rfl) ⟨1492715, by rfl⟩ : syracuseStep 1990287 = 2985431) B2985431
theorem B2985437 : Blo 1989435 2985437 := bbase (se 3 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 2985437 = 1119539) (by norm_num)
theorem B1990291 : Blo 1989435 1990291 := bstep (se 1 (by rfl) ⟨1492718, by rfl⟩ : syracuseStep 1990291 = 2985437) B2985437
theorem B4478165 : Blo 1989435 4478165 := bbase (se 7 (by rfl) ⟨52478, by rfl⟩ : syracuseStep 4478165 = 104957) (by norm_num)
theorem B2985443 : Blo 1989435 2985443 := bstep (se 1 (by rfl) ⟨2239082, by rfl⟩ : syracuseStep 2985443 = 4478165) B4478165
theorem B1990295 : Blo 1989435 1990295 := bstep (se 1 (by rfl) ⟨1492721, by rfl⟩ : syracuseStep 1990295 = 2985443) B2985443
theorem B7173173 : Blo 1989435 7173173 := bbase (se 5 (by rfl) ⟨336242, by rfl⟩ : syracuseStep 7173173 = 672485) (by norm_num)
theorem B4782115 : Blo 1989435 4782115 := bstep (se 1 (by rfl) ⟨3586586, by rfl⟩ : syracuseStep 4782115 = 7173173) B7173173
theorem B6376153 : Blo 1989435 6376153 := bstep (se 2 (by rfl) ⟨2391057, by rfl⟩ : syracuseStep 6376153 = 4782115) B4782115
theorem B8501537 : Blo 1989435 8501537 := bstep (se 2 (by rfl) ⟨3188076, by rfl⟩ : syracuseStep 8501537 = 6376153) B6376153
theorem B5667691 : Blo 1989435 5667691 := bstep (se 1 (by rfl) ⟨4250768, by rfl⟩ : syracuseStep 5667691 = 8501537) B8501537
theorem B7556921 : Blo 1989435 7556921 := bstep (se 2 (by rfl) ⟨2833845, by rfl⟩ : syracuseStep 7556921 = 5667691) B5667691
theorem B5037947 : Blo 1989435 5037947 := bstep (se 1 (by rfl) ⟨3778460, by rfl⟩ : syracuseStep 5037947 = 7556921) B7556921
theorem B3358631 : Blo 1989435 3358631 := bstep (se 1 (by rfl) ⟨2518973, by rfl⟩ : syracuseStep 3358631 = 5037947) B5037947
theorem B2239087 : Blo 1989435 2239087 := bstep (se 1 (by rfl) ⟨1679315, by rfl⟩ : syracuseStep 2239087 = 3358631) B3358631
theorem B2985449 : Blo 1989435 2985449 := bstep (se 2 (by rfl) ⟨1119543, by rfl⟩ : syracuseStep 2985449 = 2239087) B2239087
theorem B1990299 : Blo 1989435 1990299 := bstep (se 1 (by rfl) ⟨1492724, by rfl⟩ : syracuseStep 1990299 = 2985449) B2985449
theorem B4034917 : Blo 1989435 4034917 := bbase (se 4 (by rfl) ⟨378273, by rfl⟩ : syracuseStep 4034917 = 756547) (by norm_num)
theorem B21519557 : Blo 1989435 21519557 := bstep (se 4 (by rfl) ⟨2017458, by rfl⟩ : syracuseStep 21519557 = 4034917) B4034917
theorem B14346371 : Blo 1989435 14346371 := bstep (se 1 (by rfl) ⟨10759778, by rfl⟩ : syracuseStep 14346371 = 21519557) B21519557
theorem B9564247 : Blo 1989435 9564247 := bstep (se 1 (by rfl) ⟨7173185, by rfl⟩ : syracuseStep 9564247 = 14346371) B14346371
theorem B12752329 : Blo 1989435 12752329 := bstep (se 2 (by rfl) ⟨4782123, by rfl⟩ : syracuseStep 12752329 = 9564247) B9564247
theorem B17003105 : Blo 1989435 17003105 := bstep (se 2 (by rfl) ⟨6376164, by rfl⟩ : syracuseStep 17003105 = 12752329) B12752329
theorem B11335403 : Blo 1989435 11335403 := bstep (se 1 (by rfl) ⟨8501552, by rfl⟩ : syracuseStep 11335403 = 17003105) B17003105
theorem B7556935 : Blo 1989435 7556935 := bstep (se 1 (by rfl) ⟨5667701, by rfl⟩ : syracuseStep 7556935 = 11335403) B11335403
theorem B10075913 : Blo 1989435 10075913 := bstep (se 2 (by rfl) ⟨3778467, by rfl⟩ : syracuseStep 10075913 = 7556935) B7556935
theorem B6717275 : Blo 1989435 6717275 := bstep (se 1 (by rfl) ⟨5037956, by rfl⟩ : syracuseStep 6717275 = 10075913) B10075913
theorem B4478183 : Blo 1989435 4478183 := bstep (se 1 (by rfl) ⟨3358637, by rfl⟩ : syracuseStep 4478183 = 6717275) B6717275
theorem B2985455 : Blo 1989435 2985455 := bstep (se 1 (by rfl) ⟨2239091, by rfl⟩ : syracuseStep 2985455 = 4478183) B4478183
theorem B1990303 : Blo 1989435 1990303 := bstep (se 1 (by rfl) ⟨1492727, by rfl⟩ : syracuseStep 1990303 = 2985455) B2985455
theorem B2985461 : Blo 1989435 2985461 := bbase (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) (by norm_num)
theorem B1990307 : Blo 1989435 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B2125397 : Blo 1989435 2125397 := bbase (se 8 (by rfl) ⟨12453, by rfl⟩ : syracuseStep 2125397 = 24907) (by norm_num)
theorem B5667725 : Blo 1989435 5667725 := bstep (se 3 (by rfl) ⟨1062698, by rfl⟩ : syracuseStep 5667725 = 2125397) B2125397
theorem B3778483 : Blo 1989435 3778483 := bstep (se 1 (by rfl) ⟨2833862, by rfl⟩ : syracuseStep 3778483 = 5667725) B5667725
theorem B5037977 : Blo 1989435 5037977 := bstep (se 2 (by rfl) ⟨1889241, by rfl⟩ : syracuseStep 5037977 = 3778483) B3778483
theorem B3358651 : Blo 1989435 3358651 := bstep (se 1 (by rfl) ⟨2518988, by rfl⟩ : syracuseStep 3358651 = 5037977) B5037977
theorem B4478201 : Blo 1989435 4478201 := bstep (se 2 (by rfl) ⟨1679325, by rfl⟩ : syracuseStep 4478201 = 3358651) B3358651
theorem B2985467 : Blo 1989435 2985467 := bstep (se 1 (by rfl) ⟨2239100, by rfl⟩ : syracuseStep 2985467 = 4478201) B4478201
theorem B1990311 : Blo 1989435 1990311 := bstep (se 1 (by rfl) ⟨1492733, by rfl⟩ : syracuseStep 1990311 = 2985467) B2985467
theorem B2239105 : Blo 1989435 2239105 := bbase (se 2 (by rfl) ⟨839664, by rfl⟩ : syracuseStep 2239105 = 1679329) (by norm_num)
theorem B2985473 : Blo 1989435 2985473 := bstep (se 2 (by rfl) ⟨1119552, by rfl⟩ : syracuseStep 2985473 = 2239105) B2239105
theorem B1990315 : Blo 1989435 1990315 := bstep (se 1 (by rfl) ⟨1492736, by rfl⟩ : syracuseStep 1990315 = 2985473) B2985473
theorem B5037997 : Blo 1989435 5037997 := bbase (se 3 (by rfl) ⟨944624, by rfl⟩ : syracuseStep 5037997 = 1889249) (by norm_num)
theorem B6717329 : Blo 1989435 6717329 := bstep (se 2 (by rfl) ⟨2518998, by rfl⟩ : syracuseStep 6717329 = 5037997) B5037997
theorem B4478219 : Blo 1989435 4478219 := bstep (se 1 (by rfl) ⟨3358664, by rfl⟩ : syracuseStep 4478219 = 6717329) B6717329
theorem B2985479 : Blo 1989435 2985479 := bstep (se 1 (by rfl) ⟨2239109, by rfl⟩ : syracuseStep 2985479 = 4478219) B4478219
theorem B1990319 : Blo 1989435 1990319 := bstep (se 1 (by rfl) ⟨1492739, by rfl⟩ : syracuseStep 1990319 = 2985479) B2985479
theorem B2985485 : Blo 1989435 2985485 := bbase (se 3 (by rfl) ⟨559778, by rfl⟩ : syracuseStep 2985485 = 1119557) (by norm_num)
theorem B1990323 : Blo 1989435 1990323 := bstep (se 1 (by rfl) ⟨1492742, by rfl⟩ : syracuseStep 1990323 = 2985485) B2985485
theorem B4478237 : Blo 1989435 4478237 := bbase (se 3 (by rfl) ⟨839669, by rfl⟩ : syracuseStep 4478237 = 1679339) (by norm_num)
theorem B2985491 : Blo 1989435 2985491 := bstep (se 1 (by rfl) ⟨2239118, by rfl⟩ : syracuseStep 2985491 = 4478237) B4478237
theorem B1990327 : Blo 1989435 1990327 := bstep (se 1 (by rfl) ⟨1492745, by rfl⟩ : syracuseStep 1990327 = 2985491) B2985491
theorem B3358685 : Blo 1989435 3358685 := bbase (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) (by norm_num)
theorem B2239123 : Blo 1989435 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B2985497 : Blo 1989435 2985497 := bstep (se 2 (by rfl) ⟨1119561, by rfl⟩ : syracuseStep 2985497 = 2239123) B2239123
theorem B1990331 : Blo 1989435 1990331 := bstep (se 1 (by rfl) ⟨1492748, by rfl⟩ : syracuseStep 1990331 = 2985497) B2985497
theorem B7173301 : Blo 1989435 7173301 := bbase (se 5 (by rfl) ⟨336248, by rfl⟩ : syracuseStep 7173301 = 672497) (by norm_num)
theorem B9564401 : Blo 1989435 9564401 := bstep (se 2 (by rfl) ⟨3586650, by rfl⟩ : syracuseStep 9564401 = 7173301) B7173301
theorem B6376267 : Blo 1989435 6376267 := bstep (se 1 (by rfl) ⟨4782200, by rfl⟩ : syracuseStep 6376267 = 9564401) B9564401
theorem B8501689 : Blo 1989435 8501689 := bstep (se 2 (by rfl) ⟨3188133, by rfl⟩ : syracuseStep 8501689 = 6376267) B6376267
theorem B11335585 : Blo 1989435 11335585 := bstep (se 2 (by rfl) ⟨4250844, by rfl⟩ : syracuseStep 11335585 = 8501689) B8501689
theorem B15114113 : Blo 1989435 15114113 := bstep (se 2 (by rfl) ⟨5667792, by rfl⟩ : syracuseStep 15114113 = 11335585) B11335585
theorem B10076075 : Blo 1989435 10076075 := bstep (se 1 (by rfl) ⟨7557056, by rfl⟩ : syracuseStep 10076075 = 15114113) B15114113
theorem B6717383 : Blo 1989435 6717383 := bstep (se 1 (by rfl) ⟨5038037, by rfl⟩ : syracuseStep 6717383 = 10076075) B10076075
theorem B4478255 : Blo 1989435 4478255 := bstep (se 1 (by rfl) ⟨3358691, by rfl⟩ : syracuseStep 4478255 = 6717383) B6717383
theorem B2985503 : Blo 1989435 2985503 := bstep (se 1 (by rfl) ⟨2239127, by rfl⟩ : syracuseStep 2985503 = 4478255) B4478255
theorem B1990335 : Blo 1989435 1990335 := bstep (se 1 (by rfl) ⟨1492751, by rfl⟩ : syracuseStep 1990335 = 2985503) B2985503
theorem B2985509 : Blo 1989435 2985509 := bbase (se 4 (by rfl) ⟨279891, by rfl⟩ : syracuseStep 2985509 = 559783) (by norm_num)
theorem B1990339 : Blo 1989435 1990339 := bstep (se 1 (by rfl) ⟨1492754, by rfl⟩ : syracuseStep 1990339 = 2985509) B2985509
theorem B2519029 : Blo 1989435 2519029 := bbase (se 5 (by rfl) ⟨118079, by rfl⟩ : syracuseStep 2519029 = 236159) (by norm_num)
theorem B3358705 : Blo 1989435 3358705 := bstep (se 2 (by rfl) ⟨1259514, by rfl⟩ : syracuseStep 3358705 = 2519029) B2519029
theorem B4478273 : Blo 1989435 4478273 := bstep (se 2 (by rfl) ⟨1679352, by rfl⟩ : syracuseStep 4478273 = 3358705) B3358705
theorem B2985515 : Blo 1989435 2985515 := bstep (se 1 (by rfl) ⟨2239136, by rfl⟩ : syracuseStep 2985515 = 4478273) B4478273
theorem B1990343 : Blo 1989435 1990343 := bstep (se 1 (by rfl) ⟨1492757, by rfl⟩ : syracuseStep 1990343 = 2985515) B2985515
theorem B2239141 : Blo 1989435 2239141 := bbase (se 4 (by rfl) ⟨209919, by rfl⟩ : syracuseStep 2239141 = 419839) (by norm_num)
theorem B2985521 : Blo 1989435 2985521 := bstep (se 2 (by rfl) ⟨1119570, by rfl⟩ : syracuseStep 2985521 = 2239141) B2239141
theorem B1990347 : Blo 1989435 1990347 := bstep (se 1 (by rfl) ⟨1492760, by rfl⟩ : syracuseStep 1990347 = 2985521) B2985521
theorem B41976917 : Blo 1989435 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B27984611 : Blo 1989435 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B18656407 : Blo 1989435 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B24875209 : Blo 1989435 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B33166945 : Blo 1989435 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B44222593 : Blo 1989435 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B58963457 : Blo 1989435 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B39308971 : Blo 1989435 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B52411961 : Blo 1989435 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B34941307 : Blo 1989435 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B46588409 : Blo 1989435 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B31058939 : Blo 1989435 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B20705959 : Blo 1989435 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B27607945 : Blo 1989435 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B36810593 : Blo 1989435 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B24540395 : Blo 1989435 24540395 := bstep (se 1 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 24540395 = 36810593) B36810593
theorem B65441053 : Blo 1989435 65441053 := bstep (se 3 (by rfl) ⟨12270197, by rfl⟩ : syracuseStep 65441053 = 24540395) B24540395
theorem B349018949 : Blo 1989435 349018949 := bstep (se 4 (by rfl) ⟨32720526, by rfl⟩ : syracuseStep 349018949 = 65441053) B65441053
theorem B232679299 : Blo 1989435 232679299 := bstep (se 1 (by rfl) ⟨174509474, by rfl⟩ : syracuseStep 232679299 = 349018949) B349018949
theorem B310239065 : Blo 1989435 310239065 := bstep (se 2 (by rfl) ⟨116339649, by rfl⟩ : syracuseStep 310239065 = 232679299) B232679299
theorem B206826043 : Blo 1989435 206826043 := bstep (se 1 (by rfl) ⟨155119532, by rfl⟩ : syracuseStep 206826043 = 310239065) B310239065
theorem B275768057 : Blo 1989435 275768057 := bstep (se 2 (by rfl) ⟨103413021, by rfl⟩ : syracuseStep 275768057 = 206826043) B206826043
theorem B183845371 : Blo 1989435 183845371 := bstep (se 1 (by rfl) ⟨137884028, by rfl⟩ : syracuseStep 183845371 = 275768057) B275768057
theorem B245127161 : Blo 1989435 245127161 := bstep (se 2 (by rfl) ⟨91922685, by rfl⟩ : syracuseStep 245127161 = 183845371) B183845371
theorem B163418107 : Blo 1989435 163418107 := bstep (se 1 (by rfl) ⟨122563580, by rfl⟩ : syracuseStep 163418107 = 245127161) B245127161
theorem B217890809 : Blo 1989435 217890809 := bstep (se 2 (by rfl) ⟨81709053, by rfl⟩ : syracuseStep 217890809 = 163418107) B163418107
theorem B145260539 : Blo 1989435 145260539 := bstep (se 1 (by rfl) ⟨108945404, by rfl⟩ : syracuseStep 145260539 = 217890809) B217890809
theorem B96840359 : Blo 1989435 96840359 := bstep (se 1 (by rfl) ⟨72630269, by rfl⟩ : syracuseStep 96840359 = 145260539) B145260539
theorem B64560239 : Blo 1989435 64560239 := bstep (se 1 (by rfl) ⟨48420179, by rfl⟩ : syracuseStep 64560239 = 96840359) B96840359
theorem B43040159 : Blo 1989435 43040159 := bstep (se 1 (by rfl) ⟨32280119, by rfl⟩ : syracuseStep 43040159 = 64560239) B64560239
theorem B28693439 : Blo 1989435 28693439 := bstep (se 1 (by rfl) ⟨21520079, by rfl⟩ : syracuseStep 28693439 = 43040159) B43040159
theorem B19128959 : Blo 1989435 19128959 := bstep (se 1 (by rfl) ⟨14346719, by rfl⟩ : syracuseStep 19128959 = 28693439) B28693439
theorem B12752639 : Blo 1989435 12752639 := bstep (se 1 (by rfl) ⟨9564479, by rfl⟩ : syracuseStep 12752639 = 19128959) B19128959
theorem B8501759 : Blo 1989435 8501759 := bstep (se 1 (by rfl) ⟨6376319, by rfl⟩ : syracuseStep 8501759 = 12752639) B12752639
theorem B5667839 : Blo 1989435 5667839 := bstep (se 1 (by rfl) ⟨4250879, by rfl⟩ : syracuseStep 5667839 = 8501759) B8501759
theorem B3778559 : Blo 1989435 3778559 := bstep (se 1 (by rfl) ⟨2833919, by rfl⟩ : syracuseStep 3778559 = 5667839) B5667839
theorem B2519039 : Blo 1989435 2519039 := bstep (se 1 (by rfl) ⟨1889279, by rfl⟩ : syracuseStep 2519039 = 3778559) B3778559
theorem B6717437 : Blo 1989435 6717437 := bstep (se 3 (by rfl) ⟨1259519, by rfl⟩ : syracuseStep 6717437 = 2519039) B2519039
theorem B4478291 : Blo 1989435 4478291 := bstep (se 1 (by rfl) ⟨3358718, by rfl⟩ : syracuseStep 4478291 = 6717437) B6717437
theorem B2985527 : Blo 1989435 2985527 := bstep (se 1 (by rfl) ⟨2239145, by rfl⟩ : syracuseStep 2985527 = 4478291) B4478291
theorem B1990351 : Blo 1989435 1990351 := bstep (se 1 (by rfl) ⟨1492763, by rfl⟩ : syracuseStep 1990351 = 2985527) B2985527
theorem B2985533 : Blo 1989435 2985533 := bbase (se 3 (by rfl) ⟨559787, by rfl⟩ : syracuseStep 2985533 = 1119575) (by norm_num)
theorem B1990355 : Blo 1989435 1990355 := bstep (se 1 (by rfl) ⟨1492766, by rfl⟩ : syracuseStep 1990355 = 2985533) B2985533
theorem B4478309 : Blo 1989435 4478309 := bbase (se 4 (by rfl) ⟨419841, by rfl⟩ : syracuseStep 4478309 = 839683) (by norm_num)
theorem B2985539 : Blo 1989435 2985539 := bstep (se 1 (by rfl) ⟨2239154, by rfl⟩ : syracuseStep 2985539 = 4478309) B4478309
theorem B1990359 : Blo 1989435 1990359 := bstep (se 1 (by rfl) ⟨1492769, by rfl⟩ : syracuseStep 1990359 = 2985539) B2985539
theorem B5038109 : Blo 1989435 5038109 := bbase (se 3 (by rfl) ⟨944645, by rfl⟩ : syracuseStep 5038109 = 1889291) (by norm_num)
theorem B3358739 : Blo 1989435 3358739 := bstep (se 1 (by rfl) ⟨2519054, by rfl⟩ : syracuseStep 3358739 = 5038109) B5038109
theorem B2239159 : Blo 1989435 2239159 := bstep (se 1 (by rfl) ⟨1679369, by rfl⟩ : syracuseStep 2239159 = 3358739) B3358739
theorem B2985545 : Blo 1989435 2985545 := bstep (se 2 (by rfl) ⟨1119579, by rfl⟩ : syracuseStep 2985545 = 2239159) B2239159
theorem B1990363 : Blo 1989435 1990363 := bstep (se 1 (by rfl) ⟨1492772, by rfl⟩ : syracuseStep 1990363 = 2985545) B2985545
theorem B3778589 : Blo 1989435 3778589 := bbase (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) (by norm_num)
theorem B10076237 : Blo 1989435 10076237 := bstep (se 3 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 10076237 = 3778589) B3778589
theorem B6717491 : Blo 1989435 6717491 := bstep (se 1 (by rfl) ⟨5038118, by rfl⟩ : syracuseStep 6717491 = 10076237) B10076237
theorem B4478327 : Blo 1989435 4478327 := bstep (se 1 (by rfl) ⟨3358745, by rfl⟩ : syracuseStep 4478327 = 6717491) B6717491
theorem B2985551 : Blo 1989435 2985551 := bstep (se 1 (by rfl) ⟨2239163, by rfl⟩ : syracuseStep 2985551 = 4478327) B4478327
theorem B1990367 : Blo 1989435 1990367 := bstep (se 1 (by rfl) ⟨1492775, by rfl⟩ : syracuseStep 1990367 = 2985551) B2985551
theorem B2985557 : Blo 1989435 2985557 := bbase (se 8 (by rfl) ⟨17493, by rfl⟩ : syracuseStep 2985557 = 34987) (by norm_num)
theorem B1990371 : Blo 1989435 1990371 := bstep (se 1 (by rfl) ⟨1492778, by rfl⟩ : syracuseStep 1990371 = 2985557) B2985557
theorem B8501861 : Blo 1989435 8501861 := bbase (se 4 (by rfl) ⟨797049, by rfl⟩ : syracuseStep 8501861 = 1594099) (by norm_num)
theorem B5667907 : Blo 1989435 5667907 := bstep (se 1 (by rfl) ⟨4250930, by rfl⟩ : syracuseStep 5667907 = 8501861) B8501861
theorem B7557209 : Blo 1989435 7557209 := bstep (se 2 (by rfl) ⟨2833953, by rfl⟩ : syracuseStep 7557209 = 5667907) B5667907
theorem B5038139 : Blo 1989435 5038139 := bstep (se 1 (by rfl) ⟨3778604, by rfl⟩ : syracuseStep 5038139 = 7557209) B7557209
theorem B3358759 : Blo 1989435 3358759 := bstep (se 1 (by rfl) ⟨2519069, by rfl⟩ : syracuseStep 3358759 = 5038139) B5038139
theorem B4478345 : Blo 1989435 4478345 := bstep (se 2 (by rfl) ⟨1679379, by rfl⟩ : syracuseStep 4478345 = 3358759) B3358759
theorem B2985563 : Blo 1989435 2985563 := bstep (se 1 (by rfl) ⟨2239172, by rfl⟩ : syracuseStep 2985563 = 4478345) B4478345
theorem B1990375 : Blo 1989435 1990375 := bstep (se 1 (by rfl) ⟨1492781, by rfl⟩ : syracuseStep 1990375 = 2985563) B2985563
theorem B2239177 : Blo 1989435 2239177 := bbase (se 2 (by rfl) ⟨839691, by rfl⟩ : syracuseStep 2239177 = 1679383) (by norm_num)
theorem B2985569 : Blo 1989435 2985569 := bstep (se 2 (by rfl) ⟨1119588, by rfl⟩ : syracuseStep 2985569 = 2239177) B2239177
theorem B1990379 : Blo 1989435 1990379 := bstep (se 1 (by rfl) ⟨1492784, by rfl⟩ : syracuseStep 1990379 = 2985569) B2985569
theorem B6376421 : Blo 1989435 6376421 := bbase (se 4 (by rfl) ⟨597789, by rfl⟩ : syracuseStep 6376421 = 1195579) (by norm_num)
theorem B17003789 : Blo 1989435 17003789 := bstep (se 3 (by rfl) ⟨3188210, by rfl⟩ : syracuseStep 17003789 = 6376421) B6376421
theorem B11335859 : Blo 1989435 11335859 := bstep (se 1 (by rfl) ⟨8501894, by rfl⟩ : syracuseStep 11335859 = 17003789) B17003789
theorem B7557239 : Blo 1989435 7557239 := bstep (se 1 (by rfl) ⟨5667929, by rfl⟩ : syracuseStep 7557239 = 11335859) B11335859
theorem B5038159 : Blo 1989435 5038159 := bstep (se 1 (by rfl) ⟨3778619, by rfl⟩ : syracuseStep 5038159 = 7557239) B7557239
theorem B6717545 : Blo 1989435 6717545 := bstep (se 2 (by rfl) ⟨2519079, by rfl⟩ : syracuseStep 6717545 = 5038159) B5038159
theorem B4478363 : Blo 1989435 4478363 := bstep (se 1 (by rfl) ⟨3358772, by rfl⟩ : syracuseStep 4478363 = 6717545) B6717545
theorem B2985575 : Blo 1989435 2985575 := bstep (se 1 (by rfl) ⟨2239181, by rfl⟩ : syracuseStep 2985575 = 4478363) B4478363
theorem B1990383 : Blo 1989435 1990383 := bstep (se 1 (by rfl) ⟨1492787, by rfl⟩ : syracuseStep 1990383 = 2985575) B2985575
theorem B2985581 : Blo 1989435 2985581 := bbase (se 3 (by rfl) ⟨559796, by rfl⟩ : syracuseStep 2985581 = 1119593) (by norm_num)
theorem B1990387 : Blo 1989435 1990387 := bstep (se 1 (by rfl) ⟨1492790, by rfl⟩ : syracuseStep 1990387 = 2985581) B2985581
theorem B4478381 : Blo 1989435 4478381 := bbase (se 3 (by rfl) ⟨839696, by rfl⟩ : syracuseStep 4478381 = 1679393) (by norm_num)
theorem B2985587 : Blo 1989435 2985587 := bstep (se 1 (by rfl) ⟨2239190, by rfl⟩ : syracuseStep 2985587 = 4478381) B4478381
theorem B1990391 : Blo 1989435 1990391 := bstep (se 1 (by rfl) ⟨1492793, by rfl⟩ : syracuseStep 1990391 = 2985587) B2985587
theorem B2017553 : Blo 1989435 2017553 := bbase (se 2 (by rfl) ⟨756582, by rfl⟩ : syracuseStep 2017553 = 1513165) (by norm_num)
theorem B5380141 : Blo 1989435 5380141 := bstep (se 3 (by rfl) ⟨1008776, by rfl⟩ : syracuseStep 5380141 = 2017553) B2017553
theorem B7173521 : Blo 1989435 7173521 := bstep (se 2 (by rfl) ⟨2690070, by rfl⟩ : syracuseStep 7173521 = 5380141) B5380141
theorem B4782347 : Blo 1989435 4782347 := bstep (se 1 (by rfl) ⟨3586760, by rfl⟩ : syracuseStep 4782347 = 7173521) B7173521
theorem B3188231 : Blo 1989435 3188231 := bstep (se 1 (by rfl) ⟨2391173, by rfl⟩ : syracuseStep 3188231 = 4782347) B4782347
theorem B2125487 : Blo 1989435 2125487 := bstep (se 1 (by rfl) ⟨1594115, by rfl⟩ : syracuseStep 2125487 = 3188231) B3188231
theorem B5667965 : Blo 1989435 5667965 := bstep (se 3 (by rfl) ⟨1062743, by rfl⟩ : syracuseStep 5667965 = 2125487) B2125487
theorem B3778643 : Blo 1989435 3778643 := bstep (se 1 (by rfl) ⟨2833982, by rfl⟩ : syracuseStep 3778643 = 5667965) B5667965
theorem B2519095 : Blo 1989435 2519095 := bstep (se 1 (by rfl) ⟨1889321, by rfl⟩ : syracuseStep 2519095 = 3778643) B3778643
theorem B3358793 : Blo 1989435 3358793 := bstep (se 2 (by rfl) ⟨1259547, by rfl⟩ : syracuseStep 3358793 = 2519095) B2519095
theorem B2239195 : Blo 1989435 2239195 := bstep (se 1 (by rfl) ⟨1679396, by rfl⟩ : syracuseStep 2239195 = 3358793) B3358793
theorem B2985593 : Blo 1989435 2985593 := bstep (se 2 (by rfl) ⟨1119597, by rfl⟩ : syracuseStep 2985593 = 2239195) B2239195
theorem B1990395 : Blo 1989435 1990395 := bstep (se 1 (by rfl) ⟨1492796, by rfl⟩ : syracuseStep 1990395 = 2985593) B2985593
theorem B3635701 : Blo 1989435 3635701 := bbase (se 5 (by rfl) ⟨170423, by rfl⟩ : syracuseStep 3635701 = 340847) (by norm_num)
theorem B77561621 : Blo 1989435 77561621 := bstep (se 6 (by rfl) ⟨1817850, by rfl⟩ : syracuseStep 77561621 = 3635701) B3635701
theorem B51707747 : Blo 1989435 51707747 := bstep (se 1 (by rfl) ⟨38780810, by rfl⟩ : syracuseStep 51707747 = 77561621) B77561621
theorem B34471831 : Blo 1989435 34471831 := bstep (se 1 (by rfl) ⟨25853873, by rfl⟩ : syracuseStep 34471831 = 51707747) B51707747
theorem B45962441 : Blo 1989435 45962441 := bstep (se 2 (by rfl) ⟨17235915, by rfl⟩ : syracuseStep 45962441 = 34471831) B34471831
theorem B30641627 : Blo 1989435 30641627 := bstep (se 1 (by rfl) ⟨22981220, by rfl⟩ : syracuseStep 30641627 = 45962441) B45962441
theorem B20427751 : Blo 1989435 20427751 := bstep (se 1 (by rfl) ⟨15320813, by rfl⟩ : syracuseStep 20427751 = 30641627) B30641627
theorem B27237001 : Blo 1989435 27237001 := bstep (se 2 (by rfl) ⟨10213875, by rfl⟩ : syracuseStep 27237001 = 20427751) B20427751
theorem B36316001 : Blo 1989435 36316001 := bstep (se 2 (by rfl) ⟨13618500, by rfl⟩ : syracuseStep 36316001 = 27237001) B27237001
theorem B24210667 : Blo 1989435 24210667 := bstep (se 1 (by rfl) ⟨18158000, by rfl⟩ : syracuseStep 24210667 = 36316001) B36316001
theorem B129123557 : Blo 1989435 129123557 := bstep (se 4 (by rfl) ⟨12105333, by rfl⟩ : syracuseStep 129123557 = 24210667) B24210667
theorem B86082371 : Blo 1989435 86082371 := bstep (se 1 (by rfl) ⟨64561778, by rfl⟩ : syracuseStep 86082371 = 129123557) B129123557
theorem B57388247 : Blo 1989435 57388247 := bstep (se 1 (by rfl) ⟨43041185, by rfl⟩ : syracuseStep 57388247 = 86082371) B86082371
theorem B38258831 : Blo 1989435 38258831 := bstep (se 1 (by rfl) ⟨28694123, by rfl⟩ : syracuseStep 38258831 = 57388247) B57388247
theorem B25505887 : Blo 1989435 25505887 := bstep (se 1 (by rfl) ⟨19129415, by rfl⟩ : syracuseStep 25505887 = 38258831) B38258831
theorem B34007849 : Blo 1989435 34007849 := bstep (se 2 (by rfl) ⟨12752943, by rfl⟩ : syracuseStep 34007849 = 25505887) B25505887
theorem B22671899 : Blo 1989435 22671899 := bstep (se 1 (by rfl) ⟨17003924, by rfl⟩ : syracuseStep 22671899 = 34007849) B34007849
theorem B15114599 : Blo 1989435 15114599 := bstep (se 1 (by rfl) ⟨11335949, by rfl⟩ : syracuseStep 15114599 = 22671899) B22671899
theorem B10076399 : Blo 1989435 10076399 := bstep (se 1 (by rfl) ⟨7557299, by rfl⟩ : syracuseStep 10076399 = 15114599) B15114599
theorem B6717599 : Blo 1989435 6717599 := bstep (se 1 (by rfl) ⟨5038199, by rfl⟩ : syracuseStep 6717599 = 10076399) B10076399
theorem B4478399 : Blo 1989435 4478399 := bstep (se 1 (by rfl) ⟨3358799, by rfl⟩ : syracuseStep 4478399 = 6717599) B6717599
theorem B2985599 : Blo 1989435 2985599 := bstep (se 1 (by rfl) ⟨2239199, by rfl⟩ : syracuseStep 2985599 = 4478399) B4478399
theorem B1990399 : Blo 1989435 1990399 := bstep (se 1 (by rfl) ⟨1492799, by rfl⟩ : syracuseStep 1990399 = 2985599) B2985599
theorem B2985605 : Blo 1989435 2985605 := bbase (se 4 (by rfl) ⟨279900, by rfl⟩ : syracuseStep 2985605 = 559801) (by norm_num)
theorem B1990403 : Blo 1989435 1990403 := bstep (se 1 (by rfl) ⟨1492802, by rfl⟩ : syracuseStep 1990403 = 2985605) B2985605
theorem B3358813 : Blo 1989435 3358813 := bbase (se 3 (by rfl) ⟨629777, by rfl⟩ : syracuseStep 3358813 = 1259555) (by norm_num)
theorem B4478417 : Blo 1989435 4478417 := bstep (se 2 (by rfl) ⟨1679406, by rfl⟩ : syracuseStep 4478417 = 3358813) B3358813
theorem B2985611 : Blo 1989435 2985611 := bstep (se 1 (by rfl) ⟨2239208, by rfl⟩ : syracuseStep 2985611 = 4478417) B4478417
theorem B1990407 : Blo 1989435 1990407 := bstep (se 1 (by rfl) ⟨1492805, by rfl⟩ : syracuseStep 1990407 = 2985611) B2985611
theorem B2239213 : Blo 1989435 2239213 := bbase (se 3 (by rfl) ⟨419852, by rfl⟩ : syracuseStep 2239213 = 839705) (by norm_num)
theorem B2985617 : Blo 1989435 2985617 := bstep (se 2 (by rfl) ⟨1119606, by rfl⟩ : syracuseStep 2985617 = 2239213) B2239213
theorem B1990411 : Blo 1989435 1990411 := bstep (se 1 (by rfl) ⟨1492808, by rfl⟩ : syracuseStep 1990411 = 2985617) B2985617
theorem B6717653 : Blo 1989435 6717653 := bbase (se 7 (by rfl) ⟨78722, by rfl⟩ : syracuseStep 6717653 = 157445) (by norm_num)
theorem B4478435 : Blo 1989435 4478435 := bstep (se 1 (by rfl) ⟨3358826, by rfl⟩ : syracuseStep 4478435 = 6717653) B6717653
theorem B2985623 : Blo 1989435 2985623 := bstep (se 1 (by rfl) ⟨2239217, by rfl⟩ : syracuseStep 2985623 = 4478435) B4478435
theorem B1990415 : Blo 1989435 1990415 := bstep (se 1 (by rfl) ⟨1492811, by rfl⟩ : syracuseStep 1990415 = 2985623) B2985623
theorem B2985629 : Blo 1989435 2985629 := bbase (se 3 (by rfl) ⟨559805, by rfl⟩ : syracuseStep 2985629 = 1119611) (by norm_num)
theorem B1990419 : Blo 1989435 1990419 := bstep (se 1 (by rfl) ⟨1492814, by rfl⟩ : syracuseStep 1990419 = 2985629) B2985629
theorem B4478453 : Blo 1989435 4478453 := bbase (se 5 (by rfl) ⟨209927, by rfl⟩ : syracuseStep 4478453 = 419855) (by norm_num)
theorem B2985635 : Blo 1989435 2985635 := bstep (se 1 (by rfl) ⟨2239226, by rfl⟩ : syracuseStep 2985635 = 4478453) B4478453
theorem B1990423 : Blo 1989435 1990423 := bstep (se 1 (by rfl) ⟨1492817, by rfl⟩ : syracuseStep 1990423 = 2985635) B2985635
theorem B5107013 : Blo 1989435 5107013 := bbase (se 4 (by rfl) ⟨478782, by rfl⟩ : syracuseStep 5107013 = 957565) (by norm_num)
theorem B3404675 : Blo 1989435 3404675 := bstep (se 1 (by rfl) ⟨2553506, by rfl⟩ : syracuseStep 3404675 = 5107013) B5107013
theorem B2269783 : Blo 1989435 2269783 := bstep (se 1 (by rfl) ⟨1702337, by rfl⟩ : syracuseStep 2269783 = 3404675) B3404675
theorem B3026377 : Blo 1989435 3026377 := bstep (se 2 (by rfl) ⟨1134891, by rfl⟩ : syracuseStep 3026377 = 2269783) B2269783
theorem B4035169 : Blo 1989435 4035169 := bstep (se 2 (by rfl) ⟨1513188, by rfl⟩ : syracuseStep 4035169 = 3026377) B3026377
theorem B5380225 : Blo 1989435 5380225 := bstep (se 2 (by rfl) ⟨2017584, by rfl⟩ : syracuseStep 5380225 = 4035169) B4035169
theorem B28694533 : Blo 1989435 28694533 := bstep (se 4 (by rfl) ⟨2690112, by rfl⟩ : syracuseStep 28694533 = 5380225) B5380225
theorem B38259377 : Blo 1989435 38259377 := bstep (se 2 (by rfl) ⟨14347266, by rfl⟩ : syracuseStep 38259377 = 28694533) B28694533
theorem B25506251 : Blo 1989435 25506251 := bstep (se 1 (by rfl) ⟨19129688, by rfl⟩ : syracuseStep 25506251 = 38259377) B38259377
theorem B17004167 : Blo 1989435 17004167 := bstep (se 1 (by rfl) ⟨12753125, by rfl⟩ : syracuseStep 17004167 = 25506251) B25506251
theorem B11336111 : Blo 1989435 11336111 := bstep (se 1 (by rfl) ⟨8502083, by rfl⟩ : syracuseStep 11336111 = 17004167) B17004167
theorem B7557407 : Blo 1989435 7557407 := bstep (se 1 (by rfl) ⟨5668055, by rfl⟩ : syracuseStep 7557407 = 11336111) B11336111
theorem B5038271 : Blo 1989435 5038271 := bstep (se 1 (by rfl) ⟨3778703, by rfl⟩ : syracuseStep 5038271 = 7557407) B7557407
theorem B3358847 : Blo 1989435 3358847 := bstep (se 1 (by rfl) ⟨2519135, by rfl⟩ : syracuseStep 3358847 = 5038271) B5038271
theorem B2239231 : Blo 1989435 2239231 := bstep (se 1 (by rfl) ⟨1679423, by rfl⟩ : syracuseStep 2239231 = 3358847) B3358847
theorem B2985641 : Blo 1989435 2985641 := bstep (se 2 (by rfl) ⟨1119615, by rfl⟩ : syracuseStep 2985641 = 2239231) B2239231
theorem B1990427 : Blo 1989435 1990427 := bstep (se 1 (by rfl) ⟨1492820, by rfl⟩ : syracuseStep 1990427 = 2985641) B2985641
theorem B2125525 : Blo 1989435 2125525 := bbase (se 7 (by rfl) ⟨24908, by rfl⟩ : syracuseStep 2125525 = 49817) (by norm_num)
theorem B2834033 : Blo 1989435 2834033 := bstep (se 2 (by rfl) ⟨1062762, by rfl⟩ : syracuseStep 2834033 = 2125525) B2125525
theorem B7557421 : Blo 1989435 7557421 := bstep (se 3 (by rfl) ⟨1417016, by rfl⟩ : syracuseStep 7557421 = 2834033) B2834033
theorem B10076561 : Blo 1989435 10076561 := bstep (se 2 (by rfl) ⟨3778710, by rfl⟩ : syracuseStep 10076561 = 7557421) B7557421
theorem B6717707 : Blo 1989435 6717707 := bstep (se 1 (by rfl) ⟨5038280, by rfl⟩ : syracuseStep 6717707 = 10076561) B10076561
theorem B4478471 : Blo 1989435 4478471 := bstep (se 1 (by rfl) ⟨3358853, by rfl⟩ : syracuseStep 4478471 = 6717707) B6717707
theorem B2985647 : Blo 1989435 2985647 := bstep (se 1 (by rfl) ⟨2239235, by rfl⟩ : syracuseStep 2985647 = 4478471) B4478471
theorem B1990431 : Blo 1989435 1990431 := bstep (se 1 (by rfl) ⟨1492823, by rfl⟩ : syracuseStep 1990431 = 2985647) B2985647
theorem B2985653 : Blo 1989435 2985653 := bbase (se 5 (by rfl) ⟨139952, by rfl⟩ : syracuseStep 2985653 = 279905) (by norm_num)
theorem B1990435 : Blo 1989435 1990435 := bstep (se 1 (by rfl) ⟨1492826, by rfl⟩ : syracuseStep 1990435 = 2985653) B2985653
theorem B5038301 : Blo 1989435 5038301 := bbase (se 3 (by rfl) ⟨944681, by rfl⟩ : syracuseStep 5038301 = 1889363) (by norm_num)
theorem B3358867 : Blo 1989435 3358867 := bstep (se 1 (by rfl) ⟨2519150, by rfl⟩ : syracuseStep 3358867 = 5038301) B5038301
theorem B4478489 : Blo 1989435 4478489 := bstep (se 2 (by rfl) ⟨1679433, by rfl⟩ : syracuseStep 4478489 = 3358867) B3358867
theorem B2985659 : Blo 1989435 2985659 := bstep (se 1 (by rfl) ⟨2239244, by rfl⟩ : syracuseStep 2985659 = 4478489) B4478489
theorem B1990439 : Blo 1989435 1990439 := bstep (se 1 (by rfl) ⟨1492829, by rfl⟩ : syracuseStep 1990439 = 2985659) B2985659
theorem B2239249 : Blo 1989435 2239249 := bbase (se 2 (by rfl) ⟨839718, by rfl⟩ : syracuseStep 2239249 = 1679437) (by norm_num)
theorem B2985665 : Blo 1989435 2985665 := bstep (se 2 (by rfl) ⟨1119624, by rfl⟩ : syracuseStep 2985665 = 2239249) B2239249
theorem B1990443 : Blo 1989435 1990443 := bstep (se 1 (by rfl) ⟨1492832, by rfl⟩ : syracuseStep 1990443 = 2985665) B2985665
theorem B3778741 : Blo 1989435 3778741 := bbase (se 5 (by rfl) ⟨177128, by rfl⟩ : syracuseStep 3778741 = 354257) (by norm_num)
theorem B5038321 : Blo 1989435 5038321 := bstep (se 2 (by rfl) ⟨1889370, by rfl⟩ : syracuseStep 5038321 = 3778741) B3778741
theorem B6717761 : Blo 1989435 6717761 := bstep (se 2 (by rfl) ⟨2519160, by rfl⟩ : syracuseStep 6717761 = 5038321) B5038321
theorem B4478507 : Blo 1989435 4478507 := bstep (se 1 (by rfl) ⟨3358880, by rfl⟩ : syracuseStep 4478507 = 6717761) B6717761
theorem B2985671 : Blo 1989435 2985671 := bstep (se 1 (by rfl) ⟨2239253, by rfl⟩ : syracuseStep 2985671 = 4478507) B4478507
theorem B1990447 : Blo 1989435 1990447 := bstep (se 1 (by rfl) ⟨1492835, by rfl⟩ : syracuseStep 1990447 = 2985671) B2985671
theorem B2985677 : Blo 1989435 2985677 := bbase (se 3 (by rfl) ⟨559814, by rfl⟩ : syracuseStep 2985677 = 1119629) (by norm_num)
theorem B1990451 : Blo 1989435 1990451 := bstep (se 1 (by rfl) ⟨1492838, by rfl⟩ : syracuseStep 1990451 = 2985677) B2985677
theorem B4478525 : Blo 1989435 4478525 := bbase (se 3 (by rfl) ⟨839723, by rfl⟩ : syracuseStep 4478525 = 1679447) (by norm_num)
theorem B2985683 : Blo 1989435 2985683 := bstep (se 1 (by rfl) ⟨2239262, by rfl⟩ : syracuseStep 2985683 = 4478525) B4478525
theorem B1990455 : Blo 1989435 1990455 := bstep (se 1 (by rfl) ⟨1492841, by rfl⟩ : syracuseStep 1990455 = 2985683) B2985683
theorem B3358901 : Blo 1989435 3358901 := bbase (se 5 (by rfl) ⟨157448, by rfl⟩ : syracuseStep 3358901 = 314897) (by norm_num)
theorem B2239267 : Blo 1989435 2239267 := bstep (se 1 (by rfl) ⟨1679450, by rfl⟩ : syracuseStep 2239267 = 3358901) B3358901
theorem B2985689 : Blo 1989435 2985689 := bstep (se 2 (by rfl) ⟨1119633, by rfl⟩ : syracuseStep 2985689 = 2239267) B2239267
theorem B1990459 : Blo 1989435 1990459 := bstep (se 1 (by rfl) ⟨1492844, by rfl⟩ : syracuseStep 1990459 = 2985689) B2985689
theorem B4782509 : Blo 1989435 4782509 := bbase (se 3 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 4782509 = 1793441) (by norm_num)
theorem B3188339 : Blo 1989435 3188339 := bstep (se 1 (by rfl) ⟨2391254, by rfl⟩ : syracuseStep 3188339 = 4782509) B4782509
theorem B2125559 : Blo 1989435 2125559 := bstep (se 1 (by rfl) ⟨1594169, by rfl⟩ : syracuseStep 2125559 = 3188339) B3188339
theorem B5668157 : Blo 1989435 5668157 := bstep (se 3 (by rfl) ⟨1062779, by rfl⟩ : syracuseStep 5668157 = 2125559) B2125559
theorem B15115085 : Blo 1989435 15115085 := bstep (se 3 (by rfl) ⟨2834078, by rfl⟩ : syracuseStep 15115085 = 5668157) B5668157
theorem B10076723 : Blo 1989435 10076723 := bstep (se 1 (by rfl) ⟨7557542, by rfl⟩ : syracuseStep 10076723 = 15115085) B15115085
theorem B6717815 : Blo 1989435 6717815 := bstep (se 1 (by rfl) ⟨5038361, by rfl⟩ : syracuseStep 6717815 = 10076723) B10076723
theorem B4478543 : Blo 1989435 4478543 := bstep (se 1 (by rfl) ⟨3358907, by rfl⟩ : syracuseStep 4478543 = 6717815) B6717815
theorem B2985695 : Blo 1989435 2985695 := bstep (se 1 (by rfl) ⟨2239271, by rfl⟩ : syracuseStep 2985695 = 4478543) B4478543
theorem B1990463 : Blo 1989435 1990463 := bstep (se 1 (by rfl) ⟨1492847, by rfl⟩ : syracuseStep 1990463 = 2985695) B2985695
theorem B2985701 : Blo 1989435 2985701 := bbase (se 4 (by rfl) ⟨279909, by rfl⟩ : syracuseStep 2985701 = 559819) (by norm_num)
theorem B1990467 : Blo 1989435 1990467 := bstep (se 1 (by rfl) ⟨1492850, by rfl⟩ : syracuseStep 1990467 = 2985701) B2985701
theorem B5668181 : Blo 1989435 5668181 := bbase (se 11 (by rfl) ⟨4151, by rfl⟩ : syracuseStep 5668181 = 8303) (by norm_num)
theorem B3778787 : Blo 1989435 3778787 := bstep (se 1 (by rfl) ⟨2834090, by rfl⟩ : syracuseStep 3778787 = 5668181) B5668181
theorem B2519191 : Blo 1989435 2519191 := bstep (se 1 (by rfl) ⟨1889393, by rfl⟩ : syracuseStep 2519191 = 3778787) B3778787
theorem B3358921 : Blo 1989435 3358921 := bstep (se 2 (by rfl) ⟨1259595, by rfl⟩ : syracuseStep 3358921 = 2519191) B2519191
theorem B4478561 : Blo 1989435 4478561 := bstep (se 2 (by rfl) ⟨1679460, by rfl⟩ : syracuseStep 4478561 = 3358921) B3358921
theorem B2985707 : Blo 1989435 2985707 := bstep (se 1 (by rfl) ⟨2239280, by rfl⟩ : syracuseStep 2985707 = 4478561) B4478561
theorem B1990471 : Blo 1989435 1990471 := bstep (se 1 (by rfl) ⟨1492853, by rfl⟩ : syracuseStep 1990471 = 2985707) B2985707
theorem B2239285 : Blo 1989435 2239285 := bbase (se 5 (by rfl) ⟨104966, by rfl⟩ : syracuseStep 2239285 = 209933) (by norm_num)
theorem B2985713 : Blo 1989435 2985713 := bstep (se 2 (by rfl) ⟨1119642, by rfl⟩ : syracuseStep 2985713 = 2239285) B2239285
theorem B1990475 : Blo 1989435 1990475 := bstep (se 1 (by rfl) ⟨1492856, by rfl⟩ : syracuseStep 1990475 = 2985713) B2985713
theorem B2519201 : Blo 1989435 2519201 := bbase (se 2 (by rfl) ⟨944700, by rfl⟩ : syracuseStep 2519201 = 1889401) (by norm_num)
theorem B6717869 : Blo 1989435 6717869 := bstep (se 3 (by rfl) ⟨1259600, by rfl⟩ : syracuseStep 6717869 = 2519201) B2519201
theorem B4478579 : Blo 1989435 4478579 := bstep (se 1 (by rfl) ⟨3358934, by rfl⟩ : syracuseStep 4478579 = 6717869) B6717869
theorem B2985719 : Blo 1989435 2985719 := bstep (se 1 (by rfl) ⟨2239289, by rfl⟩ : syracuseStep 2985719 = 4478579) B4478579
theorem B1990479 : Blo 1989435 1990479 := bstep (se 1 (by rfl) ⟨1492859, by rfl⟩ : syracuseStep 1990479 = 2985719) B2985719
theorem B2985725 : Blo 1989435 2985725 := bbase (se 3 (by rfl) ⟨559823, by rfl⟩ : syracuseStep 2985725 = 1119647) (by norm_num)
theorem B1990483 : Blo 1989435 1990483 := bstep (se 1 (by rfl) ⟨1492862, by rfl⟩ : syracuseStep 1990483 = 2985725) B2985725
theorem B4478597 : Blo 1989435 4478597 := bbase (se 4 (by rfl) ⟨419868, by rfl⟩ : syracuseStep 4478597 = 839737) (by norm_num)
theorem B2985731 : Blo 1989435 2985731 := bstep (se 1 (by rfl) ⟨2239298, by rfl⟩ : syracuseStep 2985731 = 4478597) B4478597
theorem B1990487 : Blo 1989435 1990487 := bstep (se 1 (by rfl) ⟨1492865, by rfl⟩ : syracuseStep 1990487 = 2985731) B2985731
theorem B3586933 : Blo 1989435 3586933 := bbase (se 5 (by rfl) ⟨168137, by rfl⟩ : syracuseStep 3586933 = 336275) (by norm_num)
theorem B4782577 : Blo 1989435 4782577 := bstep (se 2 (by rfl) ⟨1793466, by rfl⟩ : syracuseStep 4782577 = 3586933) B3586933
theorem B6376769 : Blo 1989435 6376769 := bstep (se 2 (by rfl) ⟨2391288, by rfl⟩ : syracuseStep 6376769 = 4782577) B4782577
theorem B4251179 : Blo 1989435 4251179 := bstep (se 1 (by rfl) ⟨3188384, by rfl⟩ : syracuseStep 4251179 = 6376769) B6376769
theorem B2834119 : Blo 1989435 2834119 := bstep (se 1 (by rfl) ⟨2125589, by rfl⟩ : syracuseStep 2834119 = 4251179) B4251179
theorem B3778825 : Blo 1989435 3778825 := bstep (se 2 (by rfl) ⟨1417059, by rfl⟩ : syracuseStep 3778825 = 2834119) B2834119
theorem B5038433 : Blo 1989435 5038433 := bstep (se 2 (by rfl) ⟨1889412, by rfl⟩ : syracuseStep 5038433 = 3778825) B3778825
theorem B3358955 : Blo 1989435 3358955 := bstep (se 1 (by rfl) ⟨2519216, by rfl⟩ : syracuseStep 3358955 = 5038433) B5038433
theorem B2239303 : Blo 1989435 2239303 := bstep (se 1 (by rfl) ⟨1679477, by rfl⟩ : syracuseStep 2239303 = 3358955) B3358955
theorem B2985737 : Blo 1989435 2985737 := bstep (se 2 (by rfl) ⟨1119651, by rfl⟩ : syracuseStep 2985737 = 2239303) B2239303
theorem B1990491 : Blo 1989435 1990491 := bstep (se 1 (by rfl) ⟨1492868, by rfl⟩ : syracuseStep 1990491 = 2985737) B2985737
theorem B10076885 : Blo 1989435 10076885 := bbase (se 7 (by rfl) ⟨118088, by rfl⟩ : syracuseStep 10076885 = 236177) (by norm_num)
theorem B6717923 : Blo 1989435 6717923 := bstep (se 1 (by rfl) ⟨5038442, by rfl⟩ : syracuseStep 6717923 = 10076885) B10076885
theorem B4478615 : Blo 1989435 4478615 := bstep (se 1 (by rfl) ⟨3358961, by rfl⟩ : syracuseStep 4478615 = 6717923) B6717923
theorem B2985743 : Blo 1989435 2985743 := bstep (se 1 (by rfl) ⟨2239307, by rfl⟩ : syracuseStep 2985743 = 4478615) B4478615
theorem B1990495 : Blo 1989435 1990495 := bstep (se 1 (by rfl) ⟨1492871, by rfl⟩ : syracuseStep 1990495 = 2985743) B2985743
theorem B2985749 : Blo 1989435 2985749 := bbase (se 6 (by rfl) ⟨69978, by rfl⟩ : syracuseStep 2985749 = 139957) (by norm_num)
theorem B1990499 : Blo 1989435 1990499 := bstep (se 1 (by rfl) ⟨1492874, by rfl⟩ : syracuseStep 1990499 = 2985749) B2985749
theorem B2423929 : Blo 1989435 2423929 := bbase (se 2 (by rfl) ⟨908973, by rfl⟩ : syracuseStep 2423929 = 1817947) (by norm_num)
theorem B3231905 : Blo 1989435 3231905 := bstep (se 2 (by rfl) ⟨1211964, by rfl⟩ : syracuseStep 3231905 = 2423929) B2423929
theorem B8618413 : Blo 1989435 8618413 := bstep (se 3 (by rfl) ⟨1615952, by rfl⟩ : syracuseStep 8618413 = 3231905) B3231905
theorem B11491217 : Blo 1989435 11491217 := bstep (se 2 (by rfl) ⟨4309206, by rfl⟩ : syracuseStep 11491217 = 8618413) B8618413
theorem B7660811 : Blo 1989435 7660811 := bstep (se 1 (by rfl) ⟨5745608, by rfl⟩ : syracuseStep 7660811 = 11491217) B11491217
theorem B5107207 : Blo 1989435 5107207 := bstep (se 1 (by rfl) ⟨3830405, by rfl⟩ : syracuseStep 5107207 = 7660811) B7660811
theorem B6809609 : Blo 1989435 6809609 := bstep (se 2 (by rfl) ⟨2553603, by rfl⟩ : syracuseStep 6809609 = 5107207) B5107207
theorem B4539739 : Blo 1989435 4539739 := bstep (se 1 (by rfl) ⟨3404804, by rfl⟩ : syracuseStep 4539739 = 6809609) B6809609
theorem B6052985 : Blo 1989435 6052985 := bstep (se 2 (by rfl) ⟨2269869, by rfl⟩ : syracuseStep 6052985 = 4539739) B4539739
theorem B4035323 : Blo 1989435 4035323 := bstep (se 1 (by rfl) ⟨3026492, by rfl⟩ : syracuseStep 4035323 = 6052985) B6052985
theorem B2690215 : Blo 1989435 2690215 := bstep (se 1 (by rfl) ⟨2017661, by rfl⟩ : syracuseStep 2690215 = 4035323) B4035323
theorem B57391253 : Blo 1989435 57391253 := bstep (se 6 (by rfl) ⟨1345107, by rfl⟩ : syracuseStep 57391253 = 2690215) B2690215
theorem B38260835 : Blo 1989435 38260835 := bstep (se 1 (by rfl) ⟨28695626, by rfl⟩ : syracuseStep 38260835 = 57391253) B57391253
theorem B25507223 : Blo 1989435 25507223 := bstep (se 1 (by rfl) ⟨19130417, by rfl⟩ : syracuseStep 25507223 = 38260835) B38260835
theorem B17004815 : Blo 1989435 17004815 := bstep (se 1 (by rfl) ⟨12753611, by rfl⟩ : syracuseStep 17004815 = 25507223) B25507223
theorem B11336543 : Blo 1989435 11336543 := bstep (se 1 (by rfl) ⟨8502407, by rfl⟩ : syracuseStep 11336543 = 17004815) B17004815
theorem B7557695 : Blo 1989435 7557695 := bstep (se 1 (by rfl) ⟨5668271, by rfl⟩ : syracuseStep 7557695 = 11336543) B11336543
theorem B5038463 : Blo 1989435 5038463 := bstep (se 1 (by rfl) ⟨3778847, by rfl⟩ : syracuseStep 5038463 = 7557695) B7557695
theorem B3358975 : Blo 1989435 3358975 := bstep (se 1 (by rfl) ⟨2519231, by rfl⟩ : syracuseStep 3358975 = 5038463) B5038463
theorem B4478633 : Blo 1989435 4478633 := bstep (se 2 (by rfl) ⟨1679487, by rfl⟩ : syracuseStep 4478633 = 3358975) B3358975
theorem B2985755 : Blo 1989435 2985755 := bstep (se 1 (by rfl) ⟨2239316, by rfl⟩ : syracuseStep 2985755 = 4478633) B4478633
theorem B1990503 : Blo 1989435 1990503 := bstep (se 1 (by rfl) ⟨1492877, by rfl⟩ : syracuseStep 1990503 = 2985755) B2985755
theorem B2239321 : Blo 1989435 2239321 := bbase (se 2 (by rfl) ⟨839745, by rfl⟩ : syracuseStep 2239321 = 1679491) (by norm_num)
theorem B2985761 : Blo 1989435 2985761 := bstep (se 2 (by rfl) ⟨1119660, by rfl⟩ : syracuseStep 2985761 = 2239321) B2239321
theorem B1990507 : Blo 1989435 1990507 := bstep (se 1 (by rfl) ⟨1492880, by rfl⟩ : syracuseStep 1990507 = 2985761) B2985761
theorem B4251221 : Blo 1989435 4251221 := bbase (se 8 (by rfl) ⟨24909, by rfl⟩ : syracuseStep 4251221 = 49819) (by norm_num)
theorem B2834147 : Blo 1989435 2834147 := bstep (se 1 (by rfl) ⟨2125610, by rfl⟩ : syracuseStep 2834147 = 4251221) B4251221
theorem B7557725 : Blo 1989435 7557725 := bstep (se 3 (by rfl) ⟨1417073, by rfl⟩ : syracuseStep 7557725 = 2834147) B2834147
theorem B5038483 : Blo 1989435 5038483 := bstep (se 1 (by rfl) ⟨3778862, by rfl⟩ : syracuseStep 5038483 = 7557725) B7557725
theorem B6717977 : Blo 1989435 6717977 := bstep (se 2 (by rfl) ⟨2519241, by rfl⟩ : syracuseStep 6717977 = 5038483) B5038483
theorem B4478651 : Blo 1989435 4478651 := bstep (se 1 (by rfl) ⟨3358988, by rfl⟩ : syracuseStep 4478651 = 6717977) B6717977
theorem B2985767 : Blo 1989435 2985767 := bstep (se 1 (by rfl) ⟨2239325, by rfl⟩ : syracuseStep 2985767 = 4478651) B4478651
theorem B1990511 : Blo 1989435 1990511 := bstep (se 1 (by rfl) ⟨1492883, by rfl⟩ : syracuseStep 1990511 = 2985767) B2985767
theorem B2985773 : Blo 1989435 2985773 := bbase (se 3 (by rfl) ⟨559832, by rfl⟩ : syracuseStep 2985773 = 1119665) (by norm_num)
theorem B1990515 : Blo 1989435 1990515 := bstep (se 1 (by rfl) ⟨1492886, by rfl⟩ : syracuseStep 1990515 = 2985773) B2985773
theorem B4478669 : Blo 1989435 4478669 := bbase (se 3 (by rfl) ⟨839750, by rfl⟩ : syracuseStep 4478669 = 1679501) (by norm_num)
theorem B2985779 : Blo 1989435 2985779 := bstep (se 1 (by rfl) ⟨2239334, by rfl⟩ : syracuseStep 2985779 = 4478669) B4478669
theorem B1990519 : Blo 1989435 1990519 := bstep (se 1 (by rfl) ⟨1492889, by rfl⟩ : syracuseStep 1990519 = 2985779) B2985779
theorem B2519257 : Blo 1989435 2519257 := bbase (se 2 (by rfl) ⟨944721, by rfl⟩ : syracuseStep 2519257 = 1889443) (by norm_num)
theorem B3359009 : Blo 1989435 3359009 := bstep (se 2 (by rfl) ⟨1259628, by rfl⟩ : syracuseStep 3359009 = 2519257) B2519257
theorem B2239339 : Blo 1989435 2239339 := bstep (se 1 (by rfl) ⟨1679504, by rfl⟩ : syracuseStep 2239339 = 3359009) B3359009
theorem B2985785 : Blo 1989435 2985785 := bstep (se 2 (by rfl) ⟨1119669, by rfl⟩ : syracuseStep 2985785 = 2239339) B2239339
theorem B1990523 : Blo 1989435 1990523 := bstep (se 1 (by rfl) ⟨1492892, by rfl⟩ : syracuseStep 1990523 = 2985785) B2985785
theorem B3586997 : Blo 1989435 3586997 := bbase (se 5 (by rfl) ⟨168140, by rfl⟩ : syracuseStep 3586997 = 336281) (by norm_num)
theorem B2391331 : Blo 1989435 2391331 := bstep (se 1 (by rfl) ⟨1793498, by rfl⟩ : syracuseStep 2391331 = 3586997) B3586997
theorem B3188441 : Blo 1989435 3188441 := bstep (se 2 (by rfl) ⟨1195665, by rfl⟩ : syracuseStep 3188441 = 2391331) B2391331
theorem B8502509 : Blo 1989435 8502509 := bstep (se 3 (by rfl) ⟨1594220, by rfl⟩ : syracuseStep 8502509 = 3188441) B3188441
theorem B22673357 : Blo 1989435 22673357 := bstep (se 3 (by rfl) ⟨4251254, by rfl⟩ : syracuseStep 22673357 = 8502509) B8502509
theorem B15115571 : Blo 1989435 15115571 := bstep (se 1 (by rfl) ⟨11336678, by rfl⟩ : syracuseStep 15115571 = 22673357) B22673357
theorem B10077047 : Blo 1989435 10077047 := bstep (se 1 (by rfl) ⟨7557785, by rfl⟩ : syracuseStep 10077047 = 15115571) B15115571
theorem B6718031 : Blo 1989435 6718031 := bstep (se 1 (by rfl) ⟨5038523, by rfl⟩ : syracuseStep 6718031 = 10077047) B10077047
theorem B4478687 : Blo 1989435 4478687 := bstep (se 1 (by rfl) ⟨3359015, by rfl⟩ : syracuseStep 4478687 = 6718031) B6718031
theorem B2985791 : Blo 1989435 2985791 := bstep (se 1 (by rfl) ⟨2239343, by rfl⟩ : syracuseStep 2985791 = 4478687) B4478687
theorem B1990527 : Blo 1989435 1990527 := bstep (se 1 (by rfl) ⟨1492895, by rfl⟩ : syracuseStep 1990527 = 2985791) B2985791
theorem B2985797 : Blo 1989435 2985797 := bbase (se 4 (by rfl) ⟨279918, by rfl⟩ : syracuseStep 2985797 = 559837) (by norm_num)
theorem B1990531 : Blo 1989435 1990531 := bstep (se 1 (by rfl) ⟨1492898, by rfl⟩ : syracuseStep 1990531 = 2985797) B2985797
theorem B3359029 : Blo 1989435 3359029 := bbase (se 5 (by rfl) ⟨157454, by rfl⟩ : syracuseStep 3359029 = 314909) (by norm_num)
theorem B4478705 : Blo 1989435 4478705 := bstep (se 2 (by rfl) ⟨1679514, by rfl⟩ : syracuseStep 4478705 = 3359029) B3359029
theorem B2985803 : Blo 1989435 2985803 := bstep (se 1 (by rfl) ⟨2239352, by rfl⟩ : syracuseStep 2985803 = 4478705) B4478705
theorem B1990535 : Blo 1989435 1990535 := bstep (se 1 (by rfl) ⟨1492901, by rfl⟩ : syracuseStep 1990535 = 2985803) B2985803
theorem B2239357 : Blo 1989435 2239357 := bbase (se 3 (by rfl) ⟨419879, by rfl⟩ : syracuseStep 2239357 = 839759) (by norm_num)
theorem B2985809 : Blo 1989435 2985809 := bstep (se 2 (by rfl) ⟨1119678, by rfl⟩ : syracuseStep 2985809 = 2239357) B2239357
theorem B1990539 : Blo 1989435 1990539 := bstep (se 1 (by rfl) ⟨1492904, by rfl⟩ : syracuseStep 1990539 = 2985809) B2985809
theorem B6718085 : Blo 1989435 6718085 := bbase (se 4 (by rfl) ⟨629820, by rfl⟩ : syracuseStep 6718085 = 1259641) (by norm_num)
theorem B4478723 : Blo 1989435 4478723 := bstep (se 1 (by rfl) ⟨3359042, by rfl⟩ : syracuseStep 4478723 = 6718085) B6718085
theorem B2985815 : Blo 1989435 2985815 := bstep (se 1 (by rfl) ⟨2239361, by rfl⟩ : syracuseStep 2985815 = 4478723) B4478723
theorem B1990543 : Blo 1989435 1990543 := bstep (se 1 (by rfl) ⟨1492907, by rfl⟩ : syracuseStep 1990543 = 2985815) B2985815
theorem B2985821 : Blo 1989435 2985821 := bbase (se 3 (by rfl) ⟨559841, by rfl⟩ : syracuseStep 2985821 = 1119683) (by norm_num)
theorem B1990547 : Blo 1989435 1990547 := bstep (se 1 (by rfl) ⟨1492910, by rfl⟩ : syracuseStep 1990547 = 2985821) B2985821
theorem B4478741 : Blo 1989435 4478741 := bbase (se 6 (by rfl) ⟨104970, by rfl⟩ : syracuseStep 4478741 = 209941) (by norm_num)
theorem B2985827 : Blo 1989435 2985827 := bstep (se 1 (by rfl) ⟨2239370, by rfl⟩ : syracuseStep 2985827 = 4478741) B4478741
theorem B1990551 : Blo 1989435 1990551 := bstep (se 1 (by rfl) ⟨1492913, by rfl⟩ : syracuseStep 1990551 = 2985827) B2985827
theorem B7557893 : Blo 1989435 7557893 := bbase (se 4 (by rfl) ⟨708552, by rfl⟩ : syracuseStep 7557893 = 1417105) (by norm_num)
theorem B5038595 : Blo 1989435 5038595 := bstep (se 1 (by rfl) ⟨3778946, by rfl⟩ : syracuseStep 5038595 = 7557893) B7557893
theorem B3359063 : Blo 1989435 3359063 := bstep (se 1 (by rfl) ⟨2519297, by rfl⟩ : syracuseStep 3359063 = 5038595) B5038595
theorem B2239375 : Blo 1989435 2239375 := bstep (se 1 (by rfl) ⟨1679531, by rfl⟩ : syracuseStep 2239375 = 3359063) B3359063
theorem B2985833 : Blo 1989435 2985833 := bstep (se 2 (by rfl) ⟨1119687, by rfl⟩ : syracuseStep 2985833 = 2239375) B2239375
theorem B1990555 : Blo 1989435 1990555 := bstep (se 1 (by rfl) ⟨1492916, by rfl⟩ : syracuseStep 1990555 = 2985833) B2985833
theorem B4035437 : Blo 1989435 4035437 := bbase (se 3 (by rfl) ⟨756644, by rfl⟩ : syracuseStep 4035437 = 1513289) (by norm_num)
theorem B2690291 : Blo 1989435 2690291 := bstep (se 1 (by rfl) ⟨2017718, by rfl⟩ : syracuseStep 2690291 = 4035437) B4035437
theorem B7174109 : Blo 1989435 7174109 := bstep (se 3 (by rfl) ⟨1345145, by rfl⟩ : syracuseStep 7174109 = 2690291) B2690291
theorem B4782739 : Blo 1989435 4782739 := bstep (se 1 (by rfl) ⟨3587054, by rfl⟩ : syracuseStep 4782739 = 7174109) B7174109
theorem B6376985 : Blo 1989435 6376985 := bstep (se 2 (by rfl) ⟨2391369, by rfl⟩ : syracuseStep 6376985 = 4782739) B4782739
theorem B4251323 : Blo 1989435 4251323 := bstep (se 1 (by rfl) ⟨3188492, by rfl⟩ : syracuseStep 4251323 = 6376985) B6376985
theorem B11336861 : Blo 1989435 11336861 := bstep (se 3 (by rfl) ⟨2125661, by rfl⟩ : syracuseStep 11336861 = 4251323) B4251323
theorem B7557907 : Blo 1989435 7557907 := bstep (se 1 (by rfl) ⟨5668430, by rfl⟩ : syracuseStep 7557907 = 11336861) B11336861
theorem B10077209 : Blo 1989435 10077209 := bstep (se 2 (by rfl) ⟨3778953, by rfl⟩ : syracuseStep 10077209 = 7557907) B7557907
theorem B6718139 : Blo 1989435 6718139 := bstep (se 1 (by rfl) ⟨5038604, by rfl⟩ : syracuseStep 6718139 = 10077209) B10077209
theorem B4478759 : Blo 1989435 4478759 := bstep (se 1 (by rfl) ⟨3359069, by rfl⟩ : syracuseStep 4478759 = 6718139) B6718139
theorem B2985839 : Blo 1989435 2985839 := bstep (se 1 (by rfl) ⟨2239379, by rfl⟩ : syracuseStep 2985839 = 4478759) B4478759
theorem B1990559 : Blo 1989435 1990559 := bstep (se 1 (by rfl) ⟨1492919, by rfl⟩ : syracuseStep 1990559 = 2985839) B2985839
theorem B2985845 : Blo 1989435 2985845 := bbase (se 5 (by rfl) ⟨139961, by rfl⟩ : syracuseStep 2985845 = 279923) (by norm_num)
theorem B1990563 : Blo 1989435 1990563 := bstep (se 1 (by rfl) ⟨1492922, by rfl⟩ : syracuseStep 1990563 = 2985845) B2985845
theorem B4251341 : Blo 1989435 4251341 := bbase (se 3 (by rfl) ⟨797126, by rfl⟩ : syracuseStep 4251341 = 1594253) (by norm_num)
theorem B2834227 : Blo 1989435 2834227 := bstep (se 1 (by rfl) ⟨2125670, by rfl⟩ : syracuseStep 2834227 = 4251341) B4251341
theorem B3778969 : Blo 1989435 3778969 := bstep (se 2 (by rfl) ⟨1417113, by rfl⟩ : syracuseStep 3778969 = 2834227) B2834227
theorem B5038625 : Blo 1989435 5038625 := bstep (se 2 (by rfl) ⟨1889484, by rfl⟩ : syracuseStep 5038625 = 3778969) B3778969
theorem B3359083 : Blo 1989435 3359083 := bstep (se 1 (by rfl) ⟨2519312, by rfl⟩ : syracuseStep 3359083 = 5038625) B5038625
theorem B4478777 : Blo 1989435 4478777 := bstep (se 2 (by rfl) ⟨1679541, by rfl⟩ : syracuseStep 4478777 = 3359083) B3359083
theorem B2985851 : Blo 1989435 2985851 := bstep (se 1 (by rfl) ⟨2239388, by rfl⟩ : syracuseStep 2985851 = 4478777) B4478777
theorem B1990567 : Blo 1989435 1990567 := bstep (se 1 (by rfl) ⟨1492925, by rfl⟩ : syracuseStep 1990567 = 2985851) B2985851
theorem B2239393 : Blo 1989435 2239393 := bbase (se 2 (by rfl) ⟨839772, by rfl⟩ : syracuseStep 2239393 = 1679545) (by norm_num)
theorem B2985857 : Blo 1989435 2985857 := bstep (se 2 (by rfl) ⟨1119696, by rfl⟩ : syracuseStep 2985857 = 2239393) B2239393
theorem B1990571 : Blo 1989435 1990571 := bstep (se 1 (by rfl) ⟨1492928, by rfl⟩ : syracuseStep 1990571 = 2985857) B2985857
theorem B5038645 : Blo 1989435 5038645 := bbase (se 5 (by rfl) ⟨236186, by rfl⟩ : syracuseStep 5038645 = 472373) (by norm_num)
theorem B6718193 : Blo 1989435 6718193 := bstep (se 2 (by rfl) ⟨2519322, by rfl⟩ : syracuseStep 6718193 = 5038645) B5038645
theorem B4478795 : Blo 1989435 4478795 := bstep (se 1 (by rfl) ⟨3359096, by rfl⟩ : syracuseStep 4478795 = 6718193) B6718193
theorem B2985863 : Blo 1989435 2985863 := bstep (se 1 (by rfl) ⟨2239397, by rfl⟩ : syracuseStep 2985863 = 4478795) B4478795
theorem B1990575 : Blo 1989435 1990575 := bstep (se 1 (by rfl) ⟨1492931, by rfl⟩ : syracuseStep 1990575 = 2985863) B2985863
theorem B2985869 : Blo 1989435 2985869 := bbase (se 3 (by rfl) ⟨559850, by rfl⟩ : syracuseStep 2985869 = 1119701) (by norm_num)
theorem B1990579 : Blo 1989435 1990579 := bstep (se 1 (by rfl) ⟨1492934, by rfl⟩ : syracuseStep 1990579 = 2985869) B2985869
theorem B4478813 : Blo 1989435 4478813 := bbase (se 3 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 4478813 = 1679555) (by norm_num)
theorem B2985875 : Blo 1989435 2985875 := bstep (se 1 (by rfl) ⟨2239406, by rfl⟩ : syracuseStep 2985875 = 4478813) B4478813
theorem B1990583 : Blo 1989435 1990583 := bstep (se 1 (by rfl) ⟨1492937, by rfl⟩ : syracuseStep 1990583 = 2985875) B2985875
theorem B3359117 : Blo 1989435 3359117 := bbase (se 3 (by rfl) ⟨629834, by rfl⟩ : syracuseStep 3359117 = 1259669) (by norm_num)
theorem B2239411 : Blo 1989435 2239411 := bstep (se 1 (by rfl) ⟨1679558, by rfl⟩ : syracuseStep 2239411 = 3359117) B3359117
theorem B2985881 : Blo 1989435 2985881 := bstep (se 2 (by rfl) ⟨1119705, by rfl⟩ : syracuseStep 2985881 = 2239411) B2239411
theorem B1990587 : Blo 1989435 1990587 := bstep (se 1 (by rfl) ⟨1492940, by rfl⟩ : syracuseStep 1990587 = 2985881) B2985881
theorem B17472757 : Blo 1989435 17472757 := bbase (se 5 (by rfl) ⟨819035, by rfl⟩ : syracuseStep 17472757 = 1638071) (by norm_num)
theorem B23297009 : Blo 1989435 23297009 := bstep (se 2 (by rfl) ⟨8736378, by rfl⟩ : syracuseStep 23297009 = 17472757) B17472757
theorem B248501429 : Blo 1989435 248501429 := bstep (se 5 (by rfl) ⟨11648504, by rfl⟩ : syracuseStep 248501429 = 23297009) B23297009
theorem B165667619 : Blo 1989435 165667619 := bstep (se 1 (by rfl) ⟨124250714, by rfl⟩ : syracuseStep 165667619 = 248501429) B248501429
theorem B441780317 : Blo 1989435 441780317 := bstep (se 3 (by rfl) ⟨82833809, by rfl⟩ : syracuseStep 441780317 = 165667619) B165667619
theorem B294520211 : Blo 1989435 294520211 := bstep (se 1 (by rfl) ⟨220890158, by rfl⟩ : syracuseStep 294520211 = 441780317) B441780317
theorem B196346807 : Blo 1989435 196346807 := bstep (se 1 (by rfl) ⟨147260105, by rfl⟩ : syracuseStep 196346807 = 294520211) B294520211
theorem B130897871 : Blo 1989435 130897871 := bstep (se 1 (by rfl) ⟨98173403, by rfl⟩ : syracuseStep 130897871 = 196346807) B196346807
theorem B87265247 : Blo 1989435 87265247 := bstep (se 1 (by rfl) ⟨65448935, by rfl⟩ : syracuseStep 87265247 = 130897871) B130897871
theorem B232707325 : Blo 1989435 232707325 := bstep (se 3 (by rfl) ⟨43632623, by rfl⟩ : syracuseStep 232707325 = 87265247) B87265247
theorem B310276433 : Blo 1989435 310276433 := bstep (se 2 (by rfl) ⟨116353662, by rfl⟩ : syracuseStep 310276433 = 232707325) B232707325
theorem B206850955 : Blo 1989435 206850955 := bstep (se 1 (by rfl) ⟨155138216, by rfl⟩ : syracuseStep 206850955 = 310276433) B310276433
theorem B275801273 : Blo 1989435 275801273 := bstep (se 2 (by rfl) ⟨103425477, by rfl⟩ : syracuseStep 275801273 = 206850955) B206850955
theorem B183867515 : Blo 1989435 183867515 := bstep (se 1 (by rfl) ⟨137900636, by rfl⟩ : syracuseStep 183867515 = 275801273) B275801273
theorem B122578343 : Blo 1989435 122578343 := bstep (se 1 (by rfl) ⟨91933757, by rfl⟩ : syracuseStep 122578343 = 183867515) B183867515
theorem B81718895 : Blo 1989435 81718895 := bstep (se 1 (by rfl) ⟨61289171, by rfl⟩ : syracuseStep 81718895 = 122578343) B122578343
theorem B54479263 : Blo 1989435 54479263 := bstep (se 1 (by rfl) ⟨40859447, by rfl⟩ : syracuseStep 54479263 = 81718895) B81718895
theorem B72639017 : Blo 1989435 72639017 := bstep (se 2 (by rfl) ⟨27239631, by rfl⟩ : syracuseStep 72639017 = 54479263) B54479263
theorem B48426011 : Blo 1989435 48426011 := bstep (se 1 (by rfl) ⟨36319508, by rfl⟩ : syracuseStep 48426011 = 72639017) B72639017
theorem B32284007 : Blo 1989435 32284007 := bstep (se 1 (by rfl) ⟨24213005, by rfl⟩ : syracuseStep 32284007 = 48426011) B48426011
theorem B21522671 : Blo 1989435 21522671 := bstep (se 1 (by rfl) ⟨16142003, by rfl⟩ : syracuseStep 21522671 = 32284007) B32284007
theorem B14348447 : Blo 1989435 14348447 := bstep (se 1 (by rfl) ⟨10761335, by rfl⟩ : syracuseStep 14348447 = 21522671) B21522671
theorem B9565631 : Blo 1989435 9565631 := bstep (se 1 (by rfl) ⟨7174223, by rfl⟩ : syracuseStep 9565631 = 14348447) B14348447
theorem B6377087 : Blo 1989435 6377087 := bstep (se 1 (by rfl) ⟨4782815, by rfl⟩ : syracuseStep 6377087 = 9565631) B9565631
theorem B17005565 : Blo 1989435 17005565 := bstep (se 3 (by rfl) ⟨3188543, by rfl⟩ : syracuseStep 17005565 = 6377087) B6377087
theorem B11337043 : Blo 1989435 11337043 := bstep (se 1 (by rfl) ⟨8502782, by rfl⟩ : syracuseStep 11337043 = 17005565) B17005565
theorem B15116057 : Blo 1989435 15116057 := bstep (se 2 (by rfl) ⟨5668521, by rfl⟩ : syracuseStep 15116057 = 11337043) B11337043
theorem B10077371 : Blo 1989435 10077371 := bstep (se 1 (by rfl) ⟨7558028, by rfl⟩ : syracuseStep 10077371 = 15116057) B15116057
theorem B6718247 : Blo 1989435 6718247 := bstep (se 1 (by rfl) ⟨5038685, by rfl⟩ : syracuseStep 6718247 = 10077371) B10077371
theorem B4478831 : Blo 1989435 4478831 := bstep (se 1 (by rfl) ⟨3359123, by rfl⟩ : syracuseStep 4478831 = 6718247) B6718247
theorem B2985887 : Blo 1989435 2985887 := bstep (se 1 (by rfl) ⟨2239415, by rfl⟩ : syracuseStep 2985887 = 4478831) B4478831
theorem B1990591 : Blo 1989435 1990591 := bstep (se 1 (by rfl) ⟨1492943, by rfl⟩ : syracuseStep 1990591 = 2985887) B2985887
theorem B2985893 : Blo 1989435 2985893 := bbase (se 4 (by rfl) ⟨279927, by rfl⟩ : syracuseStep 2985893 = 559855) (by norm_num)
theorem B1990595 : Blo 1989435 1990595 := bstep (se 1 (by rfl) ⟨1492946, by rfl⟩ : syracuseStep 1990595 = 2985893) B2985893
theorem B2519353 : Blo 1989435 2519353 := bbase (se 2 (by rfl) ⟨944757, by rfl⟩ : syracuseStep 2519353 = 1889515) (by norm_num)
theorem B3359137 : Blo 1989435 3359137 := bstep (se 2 (by rfl) ⟨1259676, by rfl⟩ : syracuseStep 3359137 = 2519353) B2519353
theorem B4478849 : Blo 1989435 4478849 := bstep (se 2 (by rfl) ⟨1679568, by rfl⟩ : syracuseStep 4478849 = 3359137) B3359137
theorem B2985899 : Blo 1989435 2985899 := bstep (se 1 (by rfl) ⟨2239424, by rfl⟩ : syracuseStep 2985899 = 4478849) B4478849
theorem B1990599 : Blo 1989435 1990599 := bstep (se 1 (by rfl) ⟨1492949, by rfl⟩ : syracuseStep 1990599 = 2985899) B2985899
theorem B2239429 : Blo 1989435 2239429 := bbase (se 4 (by rfl) ⟨209946, by rfl⟩ : syracuseStep 2239429 = 419893) (by norm_num)
theorem B2985905 : Blo 1989435 2985905 := bstep (se 2 (by rfl) ⟨1119714, by rfl⟩ : syracuseStep 2985905 = 2239429) B2239429
theorem B1990603 : Blo 1989435 1990603 := bstep (se 1 (by rfl) ⟨1492952, by rfl⟩ : syracuseStep 1990603 = 2985905) B2985905
theorem B3779045 : Blo 1989435 3779045 := bbase (se 4 (by rfl) ⟨354285, by rfl⟩ : syracuseStep 3779045 = 708571) (by norm_num)
theorem B2519363 : Blo 1989435 2519363 := bstep (se 1 (by rfl) ⟨1889522, by rfl⟩ : syracuseStep 2519363 = 3779045) B3779045
theorem B6718301 : Blo 1989435 6718301 := bstep (se 3 (by rfl) ⟨1259681, by rfl⟩ : syracuseStep 6718301 = 2519363) B2519363
theorem B4478867 : Blo 1989435 4478867 := bstep (se 1 (by rfl) ⟨3359150, by rfl⟩ : syracuseStep 4478867 = 6718301) B6718301
theorem B2985911 : Blo 1989435 2985911 := bstep (se 1 (by rfl) ⟨2239433, by rfl⟩ : syracuseStep 2985911 = 4478867) B4478867
theorem B1990607 : Blo 1989435 1990607 := bstep (se 1 (by rfl) ⟨1492955, by rfl⟩ : syracuseStep 1990607 = 2985911) B2985911
theorem B2985917 : Blo 1989435 2985917 := bbase (se 3 (by rfl) ⟨559859, by rfl⟩ : syracuseStep 2985917 = 1119719) (by norm_num)
theorem B1990611 : Blo 1989435 1990611 := bstep (se 1 (by rfl) ⟨1492958, by rfl⟩ : syracuseStep 1990611 = 2985917) B2985917
theorem B4478885 : Blo 1989435 4478885 := bbase (se 4 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 4478885 = 839791) (by norm_num)
theorem B2985923 : Blo 1989435 2985923 := bstep (se 1 (by rfl) ⟨2239442, by rfl⟩ : syracuseStep 2985923 = 4478885) B4478885
theorem B1990615 : Blo 1989435 1990615 := bstep (se 1 (by rfl) ⟨1492961, by rfl⟩ : syracuseStep 1990615 = 2985923) B2985923
theorem B5038757 : Blo 1989435 5038757 := bbase (se 4 (by rfl) ⟨472383, by rfl⟩ : syracuseStep 5038757 = 944767) (by norm_num)
theorem B3359171 : Blo 1989435 3359171 := bstep (se 1 (by rfl) ⟨2519378, by rfl⟩ : syracuseStep 3359171 = 5038757) B5038757
theorem B2239447 : Blo 1989435 2239447 := bstep (se 1 (by rfl) ⟨1679585, by rfl⟩ : syracuseStep 2239447 = 3359171) B3359171
theorem B2985929 : Blo 1989435 2985929 := bstep (se 2 (by rfl) ⟨1119723, by rfl⟩ : syracuseStep 2985929 = 2239447) B2239447
theorem B1990619 : Blo 1989435 1990619 := bstep (se 1 (by rfl) ⟨1492964, by rfl⟩ : syracuseStep 1990619 = 2985929) B2985929
theorem B5668613 : Blo 1989435 5668613 := bbase (se 4 (by rfl) ⟨531432, by rfl⟩ : syracuseStep 5668613 = 1062865) (by norm_num)
theorem B3779075 : Blo 1989435 3779075 := bstep (se 1 (by rfl) ⟨2834306, by rfl⟩ : syracuseStep 3779075 = 5668613) B5668613
theorem B10077533 : Blo 1989435 10077533 := bstep (se 3 (by rfl) ⟨1889537, by rfl⟩ : syracuseStep 10077533 = 3779075) B3779075
theorem B6718355 : Blo 1989435 6718355 := bstep (se 1 (by rfl) ⟨5038766, by rfl⟩ : syracuseStep 6718355 = 10077533) B10077533
theorem B4478903 : Blo 1989435 4478903 := bstep (se 1 (by rfl) ⟨3359177, by rfl⟩ : syracuseStep 4478903 = 6718355) B6718355
theorem B2985935 : Blo 1989435 2985935 := bstep (se 1 (by rfl) ⟨2239451, by rfl⟩ : syracuseStep 2985935 = 4478903) B4478903
theorem B1990623 : Blo 1989435 1990623 := bstep (se 1 (by rfl) ⟨1492967, by rfl⟩ : syracuseStep 1990623 = 2985935) B2985935
theorem B2985941 : Blo 1989435 2985941 := bbase (se 7 (by rfl) ⟨34991, by rfl⟩ : syracuseStep 2985941 = 69983) (by norm_num)
theorem B1990627 : Blo 1989435 1990627 := bstep (se 1 (by rfl) ⟨1492970, by rfl⟩ : syracuseStep 1990627 = 2985941) B2985941
theorem B7558181 : Blo 1989435 7558181 := bbase (se 4 (by rfl) ⟨708579, by rfl⟩ : syracuseStep 7558181 = 1417159) (by norm_num)
theorem B5038787 : Blo 1989435 5038787 := bstep (se 1 (by rfl) ⟨3779090, by rfl⟩ : syracuseStep 5038787 = 7558181) B7558181
theorem B3359191 : Blo 1989435 3359191 := bstep (se 1 (by rfl) ⟨2519393, by rfl⟩ : syracuseStep 3359191 = 5038787) B5038787
theorem B4478921 : Blo 1989435 4478921 := bstep (se 2 (by rfl) ⟨1679595, by rfl⟩ : syracuseStep 4478921 = 3359191) B3359191
theorem B2985947 : Blo 1989435 2985947 := bstep (se 1 (by rfl) ⟨2239460, by rfl⟩ : syracuseStep 2985947 = 4478921) B4478921
theorem B1990631 : Blo 1989435 1990631 := bstep (se 1 (by rfl) ⟨1492973, by rfl⟩ : syracuseStep 1990631 = 2985947) B2985947
theorem B2239465 : Blo 1989435 2239465 := bbase (se 2 (by rfl) ⟨839799, by rfl⟩ : syracuseStep 2239465 = 1679599) (by norm_num)
theorem B2985953 : Blo 1989435 2985953 := bstep (se 2 (by rfl) ⟨1119732, by rfl⟩ : syracuseStep 2985953 = 2239465) B2239465
theorem B1990635 : Blo 1989435 1990635 := bstep (se 1 (by rfl) ⟨1492976, by rfl⟩ : syracuseStep 1990635 = 2985953) B2985953
theorem B3188621 : Blo 1989435 3188621 := bbase (se 3 (by rfl) ⟨597866, by rfl⟩ : syracuseStep 3188621 = 1195733) (by norm_num)
theorem B2125747 : Blo 1989435 2125747 := bstep (se 1 (by rfl) ⟨1594310, by rfl⟩ : syracuseStep 2125747 = 3188621) B3188621
theorem B11337317 : Blo 1989435 11337317 := bstep (se 4 (by rfl) ⟨1062873, by rfl⟩ : syracuseStep 11337317 = 2125747) B2125747
theorem B7558211 : Blo 1989435 7558211 := bstep (se 1 (by rfl) ⟨5668658, by rfl⟩ : syracuseStep 7558211 = 11337317) B11337317
theorem B5038807 : Blo 1989435 5038807 := bstep (se 1 (by rfl) ⟨3779105, by rfl⟩ : syracuseStep 5038807 = 7558211) B7558211
theorem B6718409 : Blo 1989435 6718409 := bstep (se 2 (by rfl) ⟨2519403, by rfl⟩ : syracuseStep 6718409 = 5038807) B5038807
theorem B4478939 : Blo 1989435 4478939 := bstep (se 1 (by rfl) ⟨3359204, by rfl⟩ : syracuseStep 4478939 = 6718409) B6718409
theorem B2985959 : Blo 1989435 2985959 := bstep (se 1 (by rfl) ⟨2239469, by rfl⟩ : syracuseStep 2985959 = 4478939) B4478939
theorem B1990639 : Blo 1989435 1990639 := bstep (se 1 (by rfl) ⟨1492979, by rfl⟩ : syracuseStep 1990639 = 2985959) B2985959
theorem B2985965 : Blo 1989435 2985965 := bbase (se 3 (by rfl) ⟨559868, by rfl⟩ : syracuseStep 2985965 = 1119737) (by norm_num)
theorem B1990643 : Blo 1989435 1990643 := bstep (se 1 (by rfl) ⟨1492982, by rfl⟩ : syracuseStep 1990643 = 2985965) B2985965
theorem B4478957 : Blo 1989435 4478957 := bbase (se 3 (by rfl) ⟨839804, by rfl⟩ : syracuseStep 4478957 = 1679609) (by norm_num)
theorem B2985971 : Blo 1989435 2985971 := bstep (se 1 (by rfl) ⟨2239478, by rfl⟩ : syracuseStep 2985971 = 4478957) B4478957
theorem B1990647 : Blo 1989435 1990647 := bstep (se 1 (by rfl) ⟨1492985, by rfl⟩ : syracuseStep 1990647 = 2985971) B2985971
theorem B2391481 : Blo 1989435 2391481 := bbase (se 2 (by rfl) ⟨896805, by rfl⟩ : syracuseStep 2391481 = 1793611) (by norm_num)
theorem B3188641 : Blo 1989435 3188641 := bstep (se 2 (by rfl) ⟨1195740, by rfl⟩ : syracuseStep 3188641 = 2391481) B2391481
theorem B4251521 : Blo 1989435 4251521 := bstep (se 2 (by rfl) ⟨1594320, by rfl⟩ : syracuseStep 4251521 = 3188641) B3188641
theorem B2834347 : Blo 1989435 2834347 := bstep (se 1 (by rfl) ⟨2125760, by rfl⟩ : syracuseStep 2834347 = 4251521) B4251521
theorem B3779129 : Blo 1989435 3779129 := bstep (se 2 (by rfl) ⟨1417173, by rfl⟩ : syracuseStep 3779129 = 2834347) B2834347
theorem B2519419 : Blo 1989435 2519419 := bstep (se 1 (by rfl) ⟨1889564, by rfl⟩ : syracuseStep 2519419 = 3779129) B3779129
theorem B3359225 : Blo 1989435 3359225 := bstep (se 2 (by rfl) ⟨1259709, by rfl⟩ : syracuseStep 3359225 = 2519419) B2519419
theorem B2239483 : Blo 1989435 2239483 := bstep (se 1 (by rfl) ⟨1679612, by rfl⟩ : syracuseStep 2239483 = 3359225) B3359225
theorem B2985977 : Blo 1989435 2985977 := bstep (se 2 (by rfl) ⟨1119741, by rfl⟩ : syracuseStep 2985977 = 2239483) B2239483
theorem B1990651 : Blo 1989435 1990651 := bstep (se 1 (by rfl) ⟨1492988, by rfl⟩ : syracuseStep 1990651 = 2985977) B2985977
theorem B4981421 : Blo 1989435 4981421 := bbase (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) (by norm_num)
theorem B3320947 : Blo 1989435 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B4427929 : Blo 1989435 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B23615621 : Blo 1989435 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B15743747 : Blo 1989435 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B10495831 : Blo 1989435 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B13994441 : Blo 1989435 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B9329627 : Blo 1989435 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B24879005 : Blo 1989435 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B16586003 : Blo 1989435 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B44229341 : Blo 1989435 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B29486227 : Blo 1989435 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B39314969 : Blo 1989435 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B26209979 : Blo 1989435 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B17473319 : Blo 1989435 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B11648879 : Blo 1989435 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B7765919 : Blo 1989435 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B5177279 : Blo 1989435 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B13806077 : Blo 1989435 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B36816205 : Blo 1989435 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B49088273 : Blo 1989435 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B523608245 : Blo 1989435 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B349072163 : Blo 1989435 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B232714775 : Blo 1989435 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B155143183 : Blo 1989435 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B206857577 : Blo 1989435 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B137905051 : Blo 1989435 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B183873401 : Blo 1989435 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B122582267 : Blo 1989435 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B81721511 : Blo 1989435 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B54481007 : Blo 1989435 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B36320671 : Blo 1989435 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B48427561 : Blo 1989435 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B258280325 : Blo 1989435 258280325 := bstep (se 4 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 258280325 = 48427561) B48427561
theorem B172186883 : Blo 1989435 172186883 := bstep (se 1 (by rfl) ⟨129140162, by rfl⟩ : syracuseStep 172186883 = 258280325) B258280325
theorem B114791255 : Blo 1989435 114791255 := bstep (se 1 (by rfl) ⟨86093441, by rfl⟩ : syracuseStep 114791255 = 172186883) B172186883
theorem B76527503 : Blo 1989435 76527503 := bstep (se 1 (by rfl) ⟨57395627, by rfl⟩ : syracuseStep 76527503 = 114791255) B114791255
theorem B51018335 : Blo 1989435 51018335 := bstep (se 1 (by rfl) ⟨38263751, by rfl⟩ : syracuseStep 51018335 = 76527503) B76527503
theorem B34012223 : Blo 1989435 34012223 := bstep (se 1 (by rfl) ⟨25509167, by rfl⟩ : syracuseStep 34012223 = 51018335) B51018335
theorem B22674815 : Blo 1989435 22674815 := bstep (se 1 (by rfl) ⟨17006111, by rfl⟩ : syracuseStep 22674815 = 34012223) B34012223
theorem B15116543 : Blo 1989435 15116543 := bstep (se 1 (by rfl) ⟨11337407, by rfl⟩ : syracuseStep 15116543 = 22674815) B22674815
theorem B10077695 : Blo 1989435 10077695 := bstep (se 1 (by rfl) ⟨7558271, by rfl⟩ : syracuseStep 10077695 = 15116543) B15116543
theorem B6718463 : Blo 1989435 6718463 := bstep (se 1 (by rfl) ⟨5038847, by rfl⟩ : syracuseStep 6718463 = 10077695) B10077695
theorem B4478975 : Blo 1989435 4478975 := bstep (se 1 (by rfl) ⟨3359231, by rfl⟩ : syracuseStep 4478975 = 6718463) B6718463
theorem B2985983 : Blo 1989435 2985983 := bstep (se 1 (by rfl) ⟨2239487, by rfl⟩ : syracuseStep 2985983 = 4478975) B4478975
theorem B1990655 : Blo 1989435 1990655 := bstep (se 1 (by rfl) ⟨1492991, by rfl⟩ : syracuseStep 1990655 = 2985983) B2985983
theorem B2985989 : Blo 1989435 2985989 := bbase (se 4 (by rfl) ⟨279936, by rfl⟩ : syracuseStep 2985989 = 559873) (by norm_num)
theorem B1990659 : Blo 1989435 1990659 := bstep (se 1 (by rfl) ⟨1492994, by rfl⟩ : syracuseStep 1990659 = 2985989) B2985989
theorem B3359245 : Blo 1989435 3359245 := bbase (se 3 (by rfl) ⟨629858, by rfl⟩ : syracuseStep 3359245 = 1259717) (by norm_num)
theorem B4478993 : Blo 1989435 4478993 := bstep (se 2 (by rfl) ⟨1679622, by rfl⟩ : syracuseStep 4478993 = 3359245) B3359245
theorem B2985995 : Blo 1989435 2985995 := bstep (se 1 (by rfl) ⟨2239496, by rfl⟩ : syracuseStep 2985995 = 4478993) B4478993
theorem B1990663 : Blo 1989435 1990663 := bstep (se 1 (by rfl) ⟨1492997, by rfl⟩ : syracuseStep 1990663 = 2985995) B2985995
theorem B2239501 : Blo 1989435 2239501 := bbase (se 3 (by rfl) ⟨419906, by rfl⟩ : syracuseStep 2239501 = 839813) (by norm_num)
theorem B2986001 : Blo 1989435 2986001 := bstep (se 2 (by rfl) ⟨1119750, by rfl⟩ : syracuseStep 2986001 = 2239501) B2239501
theorem B1990667 : Blo 1989435 1990667 := bstep (se 1 (by rfl) ⟨1493000, by rfl⟩ : syracuseStep 1990667 = 2986001) B2986001
theorem B6718517 : Blo 1989435 6718517 := bbase (se 5 (by rfl) ⟨314930, by rfl⟩ : syracuseStep 6718517 = 629861) (by norm_num)
theorem B4479011 : Blo 1989435 4479011 := bstep (se 1 (by rfl) ⟨3359258, by rfl⟩ : syracuseStep 4479011 = 6718517) B6718517
theorem B2986007 : Blo 1989435 2986007 := bstep (se 1 (by rfl) ⟨2239505, by rfl⟩ : syracuseStep 2986007 = 4479011) B4479011
theorem B1990671 : Blo 1989435 1990671 := bstep (se 1 (by rfl) ⟨1493003, by rfl⟩ : syracuseStep 1990671 = 2986007) B2986007
theorem B2986013 : Blo 1989435 2986013 := bbase (se 3 (by rfl) ⟨559877, by rfl⟩ : syracuseStep 2986013 = 1119755) (by norm_num)
theorem B1990675 : Blo 1989435 1990675 := bstep (se 1 (by rfl) ⟨1493006, by rfl⟩ : syracuseStep 1990675 = 2986013) B2986013
theorem B4479029 : Blo 1989435 4479029 := bbase (se 5 (by rfl) ⟨209954, by rfl⟩ : syracuseStep 4479029 = 419909) (by norm_num)
theorem B2986019 : Blo 1989435 2986019 := bstep (se 1 (by rfl) ⟨2239514, by rfl⟩ : syracuseStep 2986019 = 4479029) B4479029
theorem B1990679 : Blo 1989435 1990679 := bstep (se 1 (by rfl) ⟨1493009, by rfl⟩ : syracuseStep 1990679 = 2986019) B2986019
theorem B65451989 : Blo 1989435 65451989 := bbase (se 7 (by rfl) ⟨767015, by rfl⟩ : syracuseStep 65451989 = 1534031) (by norm_num)
theorem B43634659 : Blo 1989435 43634659 := bstep (se 1 (by rfl) ⟨32725994, by rfl⟩ : syracuseStep 43634659 = 65451989) B65451989
theorem B58179545 : Blo 1989435 58179545 := bstep (se 2 (by rfl) ⟨21817329, by rfl⟩ : syracuseStep 58179545 = 43634659) B43634659
theorem B38786363 : Blo 1989435 38786363 := bstep (se 1 (by rfl) ⟨29089772, by rfl⟩ : syracuseStep 38786363 = 58179545) B58179545
theorem B25857575 : Blo 1989435 25857575 := bstep (se 1 (by rfl) ⟨19393181, by rfl⟩ : syracuseStep 25857575 = 38786363) B38786363
theorem B17238383 : Blo 1989435 17238383 := bstep (se 1 (by rfl) ⟨12928787, by rfl⟩ : syracuseStep 17238383 = 25857575) B25857575
theorem B11492255 : Blo 1989435 11492255 := bstep (se 1 (by rfl) ⟨8619191, by rfl⟩ : syracuseStep 11492255 = 17238383) B17238383
theorem B7661503 : Blo 1989435 7661503 := bstep (se 1 (by rfl) ⟨5746127, by rfl⟩ : syracuseStep 7661503 = 11492255) B11492255
theorem B10215337 : Blo 1989435 10215337 := bstep (se 2 (by rfl) ⟨3830751, by rfl⟩ : syracuseStep 10215337 = 7661503) B7661503
theorem B13620449 : Blo 1989435 13620449 := bstep (se 2 (by rfl) ⟨5107668, by rfl⟩ : syracuseStep 13620449 = 10215337) B10215337
theorem B9080299 : Blo 1989435 9080299 := bstep (se 1 (by rfl) ⟨6810224, by rfl⟩ : syracuseStep 9080299 = 13620449) B13620449
theorem B12107065 : Blo 1989435 12107065 := bstep (se 2 (by rfl) ⟨4540149, by rfl⟩ : syracuseStep 12107065 = 9080299) B9080299
theorem B16142753 : Blo 1989435 16142753 := bstep (se 2 (by rfl) ⟨6053532, by rfl⟩ : syracuseStep 16142753 = 12107065) B12107065
theorem B10761835 : Blo 1989435 10761835 := bstep (se 1 (by rfl) ⟨8071376, by rfl⟩ : syracuseStep 10761835 = 16142753) B16142753
theorem B14349113 : Blo 1989435 14349113 := bstep (se 2 (by rfl) ⟨5380917, by rfl⟩ : syracuseStep 14349113 = 10761835) B10761835
theorem B9566075 : Blo 1989435 9566075 := bstep (se 1 (by rfl) ⟨7174556, by rfl⟩ : syracuseStep 9566075 = 14349113) B14349113
theorem B6377383 : Blo 1989435 6377383 := bstep (se 1 (by rfl) ⟨4783037, by rfl⟩ : syracuseStep 6377383 = 9566075) B9566075
theorem B8503177 : Blo 1989435 8503177 := bstep (se 2 (by rfl) ⟨3188691, by rfl⟩ : syracuseStep 8503177 = 6377383) B6377383
theorem B11337569 : Blo 1989435 11337569 := bstep (se 2 (by rfl) ⟨4251588, by rfl⟩ : syracuseStep 11337569 = 8503177) B8503177
theorem B7558379 : Blo 1989435 7558379 := bstep (se 1 (by rfl) ⟨5668784, by rfl⟩ : syracuseStep 7558379 = 11337569) B11337569
theorem B5038919 : Blo 1989435 5038919 := bstep (se 1 (by rfl) ⟨3779189, by rfl⟩ : syracuseStep 5038919 = 7558379) B7558379
theorem B3359279 : Blo 1989435 3359279 := bstep (se 1 (by rfl) ⟨2519459, by rfl⟩ : syracuseStep 3359279 = 5038919) B5038919
theorem B2239519 : Blo 1989435 2239519 := bstep (se 1 (by rfl) ⟨1679639, by rfl⟩ : syracuseStep 2239519 = 3359279) B3359279
theorem B2986025 : Blo 1989435 2986025 := bstep (se 2 (by rfl) ⟨1119759, by rfl⟩ : syracuseStep 2986025 = 2239519) B2239519
theorem B1990683 : Blo 1989435 1990683 := bstep (se 1 (by rfl) ⟨1493012, by rfl⟩ : syracuseStep 1990683 = 2986025) B2986025
theorem B3587285 : Blo 1989435 3587285 := bbase (se 7 (by rfl) ⟨42038, by rfl⟩ : syracuseStep 3587285 = 84077) (by norm_num)
theorem B9566093 : Blo 1989435 9566093 := bstep (se 3 (by rfl) ⟨1793642, by rfl⟩ : syracuseStep 9566093 = 3587285) B3587285
theorem B6377395 : Blo 1989435 6377395 := bstep (se 1 (by rfl) ⟨4783046, by rfl⟩ : syracuseStep 6377395 = 9566093) B9566093
theorem B8503193 : Blo 1989435 8503193 := bstep (se 2 (by rfl) ⟨3188697, by rfl⟩ : syracuseStep 8503193 = 6377395) B6377395
theorem B5668795 : Blo 1989435 5668795 := bstep (se 1 (by rfl) ⟨4251596, by rfl⟩ : syracuseStep 5668795 = 8503193) B8503193
theorem B7558393 : Blo 1989435 7558393 := bstep (se 2 (by rfl) ⟨2834397, by rfl⟩ : syracuseStep 7558393 = 5668795) B5668795
theorem B10077857 : Blo 1989435 10077857 := bstep (se 2 (by rfl) ⟨3779196, by rfl⟩ : syracuseStep 10077857 = 7558393) B7558393
theorem B6718571 : Blo 1989435 6718571 := bstep (se 1 (by rfl) ⟨5038928, by rfl⟩ : syracuseStep 6718571 = 10077857) B10077857
theorem B4479047 : Blo 1989435 4479047 := bstep (se 1 (by rfl) ⟨3359285, by rfl⟩ : syracuseStep 4479047 = 6718571) B6718571
theorem B2986031 : Blo 1989435 2986031 := bstep (se 1 (by rfl) ⟨2239523, by rfl⟩ : syracuseStep 2986031 = 4479047) B4479047
theorem B1990687 : Blo 1989435 1990687 := bstep (se 1 (by rfl) ⟨1493015, by rfl⟩ : syracuseStep 1990687 = 2986031) B2986031
theorem B2986037 : Blo 1989435 2986037 := bbase (se 5 (by rfl) ⟨139970, by rfl⟩ : syracuseStep 2986037 = 279941) (by norm_num)
theorem B1990691 : Blo 1989435 1990691 := bstep (se 1 (by rfl) ⟨1493018, by rfl⟩ : syracuseStep 1990691 = 2986037) B2986037
theorem B5038949 : Blo 1989435 5038949 := bbase (se 4 (by rfl) ⟨472401, by rfl⟩ : syracuseStep 5038949 = 944803) (by norm_num)
theorem B3359299 : Blo 1989435 3359299 := bstep (se 1 (by rfl) ⟨2519474, by rfl⟩ : syracuseStep 3359299 = 5038949) B5038949
theorem B4479065 : Blo 1989435 4479065 := bstep (se 2 (by rfl) ⟨1679649, by rfl⟩ : syracuseStep 4479065 = 3359299) B3359299
theorem B2986043 : Blo 1989435 2986043 := bstep (se 1 (by rfl) ⟨2239532, by rfl⟩ : syracuseStep 2986043 = 4479065) B4479065
theorem B1990695 : Blo 1989435 1990695 := bstep (se 1 (by rfl) ⟨1493021, by rfl⟩ : syracuseStep 1990695 = 2986043) B2986043
theorem B2239537 : Blo 1989435 2239537 := bbase (se 2 (by rfl) ⟨839826, by rfl⟩ : syracuseStep 2239537 = 1679653) (by norm_num)
theorem B2986049 : Blo 1989435 2986049 := bstep (se 2 (by rfl) ⟨1119768, by rfl⟩ : syracuseStep 2986049 = 2239537) B2239537
theorem B1990699 : Blo 1989435 1990699 := bstep (se 1 (by rfl) ⟨1493024, by rfl⟩ : syracuseStep 1990699 = 2986049) B2986049
theorem B6810293 : Blo 1989435 6810293 := bbase (se 5 (by rfl) ⟨319232, by rfl⟩ : syracuseStep 6810293 = 638465) (by norm_num)
theorem B4540195 : Blo 1989435 4540195 := bstep (se 1 (by rfl) ⟨3405146, by rfl⟩ : syracuseStep 4540195 = 6810293) B6810293
theorem B24214373 : Blo 1989435 24214373 := bstep (se 4 (by rfl) ⟨2270097, by rfl⟩ : syracuseStep 24214373 = 4540195) B4540195
theorem B16142915 : Blo 1989435 16142915 := bstep (se 1 (by rfl) ⟨12107186, by rfl⟩ : syracuseStep 16142915 = 24214373) B24214373
theorem B10761943 : Blo 1989435 10761943 := bstep (se 1 (by rfl) ⟨8071457, by rfl⟩ : syracuseStep 10761943 = 16142915) B16142915
theorem B14349257 : Blo 1989435 14349257 := bstep (se 2 (by rfl) ⟨5380971, by rfl⟩ : syracuseStep 14349257 = 10761943) B10761943
theorem B9566171 : Blo 1989435 9566171 := bstep (se 1 (by rfl) ⟨7174628, by rfl⟩ : syracuseStep 9566171 = 14349257) B14349257
theorem B6377447 : Blo 1989435 6377447 := bstep (se 1 (by rfl) ⟨4783085, by rfl⟩ : syracuseStep 6377447 = 9566171) B9566171
theorem B4251631 : Blo 1989435 4251631 := bstep (se 1 (by rfl) ⟨3188723, by rfl⟩ : syracuseStep 4251631 = 6377447) B6377447
theorem B5668841 : Blo 1989435 5668841 := bstep (se 2 (by rfl) ⟨2125815, by rfl⟩ : syracuseStep 5668841 = 4251631) B4251631
theorem B3779227 : Blo 1989435 3779227 := bstep (se 1 (by rfl) ⟨2834420, by rfl⟩ : syracuseStep 3779227 = 5668841) B5668841
theorem B5038969 : Blo 1989435 5038969 := bstep (se 2 (by rfl) ⟨1889613, by rfl⟩ : syracuseStep 5038969 = 3779227) B3779227
theorem B6718625 : Blo 1989435 6718625 := bstep (se 2 (by rfl) ⟨2519484, by rfl⟩ : syracuseStep 6718625 = 5038969) B5038969
theorem B4479083 : Blo 1989435 4479083 := bstep (se 1 (by rfl) ⟨3359312, by rfl⟩ : syracuseStep 4479083 = 6718625) B6718625
theorem B2986055 : Blo 1989435 2986055 := bstep (se 1 (by rfl) ⟨2239541, by rfl⟩ : syracuseStep 2986055 = 4479083) B4479083
theorem B1990703 : Blo 1989435 1990703 := bstep (se 1 (by rfl) ⟨1493027, by rfl⟩ : syracuseStep 1990703 = 2986055) B2986055
theorem B2986061 : Blo 1989435 2986061 := bbase (se 3 (by rfl) ⟨559886, by rfl⟩ : syracuseStep 2986061 = 1119773) (by norm_num)
theorem B1990707 : Blo 1989435 1990707 := bstep (se 1 (by rfl) ⟨1493030, by rfl⟩ : syracuseStep 1990707 = 2986061) B2986061
theorem B4479101 : Blo 1989435 4479101 := bbase (se 3 (by rfl) ⟨839831, by rfl⟩ : syracuseStep 4479101 = 1679663) (by norm_num)
theorem B2986067 : Blo 1989435 2986067 := bstep (se 1 (by rfl) ⟨2239550, by rfl⟩ : syracuseStep 2986067 = 4479101) B4479101
theorem B1990711 : Blo 1989435 1990711 := bstep (se 1 (by rfl) ⟨1493033, by rfl⟩ : syracuseStep 1990711 = 2986067) B2986067
theorem B3359333 : Blo 1989435 3359333 := bbase (se 4 (by rfl) ⟨314937, by rfl⟩ : syracuseStep 3359333 = 629875) (by norm_num)
theorem B2239555 : Blo 1989435 2239555 := bstep (se 1 (by rfl) ⟨1679666, by rfl⟩ : syracuseStep 2239555 = 3359333) B3359333
theorem B2986073 : Blo 1989435 2986073 := bstep (se 2 (by rfl) ⟨1119777, by rfl⟩ : syracuseStep 2986073 = 2239555) B2239555
theorem B1990715 : Blo 1989435 1990715 := bstep (se 1 (by rfl) ⟨1493036, by rfl⟩ : syracuseStep 1990715 = 2986073) B2986073
theorem B3188749 : Blo 1989435 3188749 := bbase (se 3 (by rfl) ⟨597890, by rfl⟩ : syracuseStep 3188749 = 1195781) (by norm_num)
theorem B4251665 : Blo 1989435 4251665 := bstep (se 2 (by rfl) ⟨1594374, by rfl⟩ : syracuseStep 4251665 = 3188749) B3188749
theorem B2834443 : Blo 1989435 2834443 := bstep (se 1 (by rfl) ⟨2125832, by rfl⟩ : syracuseStep 2834443 = 4251665) B4251665
theorem B15117029 : Blo 1989435 15117029 := bstep (se 4 (by rfl) ⟨1417221, by rfl⟩ : syracuseStep 15117029 = 2834443) B2834443
theorem B10078019 : Blo 1989435 10078019 := bstep (se 1 (by rfl) ⟨7558514, by rfl⟩ : syracuseStep 10078019 = 15117029) B15117029
theorem B6718679 : Blo 1989435 6718679 := bstep (se 1 (by rfl) ⟨5039009, by rfl⟩ : syracuseStep 6718679 = 10078019) B10078019
theorem B4479119 : Blo 1989435 4479119 := bstep (se 1 (by rfl) ⟨3359339, by rfl⟩ : syracuseStep 4479119 = 6718679) B6718679
theorem B2986079 : Blo 1989435 2986079 := bstep (se 1 (by rfl) ⟨2239559, by rfl⟩ : syracuseStep 2986079 = 4479119) B4479119
theorem B1990719 : Blo 1989435 1990719 := bstep (se 1 (by rfl) ⟨1493039, by rfl⟩ : syracuseStep 1990719 = 2986079) B2986079
theorem B2986085 : Blo 1989435 2986085 := bbase (se 4 (by rfl) ⟨279945, by rfl⟩ : syracuseStep 2986085 = 559891) (by norm_num)
theorem B1990723 : Blo 1989435 1990723 := bstep (se 1 (by rfl) ⟨1493042, by rfl⟩ : syracuseStep 1990723 = 2986085) B2986085
theorem B6377525 : Blo 1989435 6377525 := bbase (se 5 (by rfl) ⟨298946, by rfl⟩ : syracuseStep 6377525 = 597893) (by norm_num)
theorem B4251683 : Blo 1989435 4251683 := bstep (se 1 (by rfl) ⟨3188762, by rfl⟩ : syracuseStep 4251683 = 6377525) B6377525
theorem B2834455 : Blo 1989435 2834455 := bstep (se 1 (by rfl) ⟨2125841, by rfl⟩ : syracuseStep 2834455 = 4251683) B4251683
theorem B3779273 : Blo 1989435 3779273 := bstep (se 2 (by rfl) ⟨1417227, by rfl⟩ : syracuseStep 3779273 = 2834455) B2834455
theorem B2519515 : Blo 1989435 2519515 := bstep (se 1 (by rfl) ⟨1889636, by rfl⟩ : syracuseStep 2519515 = 3779273) B3779273
theorem B3359353 : Blo 1989435 3359353 := bstep (se 2 (by rfl) ⟨1259757, by rfl⟩ : syracuseStep 3359353 = 2519515) B2519515
theorem B4479137 : Blo 1989435 4479137 := bstep (se 2 (by rfl) ⟨1679676, by rfl⟩ : syracuseStep 4479137 = 3359353) B3359353
theorem B2986091 : Blo 1989435 2986091 := bstep (se 1 (by rfl) ⟨2239568, by rfl⟩ : syracuseStep 2986091 = 4479137) B4479137
theorem B1990727 : Blo 1989435 1990727 := bstep (se 1 (by rfl) ⟨1493045, by rfl⟩ : syracuseStep 1990727 = 2986091) B2986091
theorem B2239573 : Blo 1989435 2239573 := bbase (se 8 (by rfl) ⟨13122, by rfl⟩ : syracuseStep 2239573 = 26245) (by norm_num)
theorem B2986097 : Blo 1989435 2986097 := bstep (se 2 (by rfl) ⟨1119786, by rfl⟩ : syracuseStep 2986097 = 2239573) B2239573
theorem B1990731 : Blo 1989435 1990731 := bstep (se 1 (by rfl) ⟨1493048, by rfl⟩ : syracuseStep 1990731 = 2986097) B2986097
theorem B2519525 : Blo 1989435 2519525 := bbase (se 4 (by rfl) ⟨236205, by rfl⟩ : syracuseStep 2519525 = 472411) (by norm_num)
theorem B6718733 : Blo 1989435 6718733 := bstep (se 3 (by rfl) ⟨1259762, by rfl⟩ : syracuseStep 6718733 = 2519525) B2519525
theorem B4479155 : Blo 1989435 4479155 := bstep (se 1 (by rfl) ⟨3359366, by rfl⟩ : syracuseStep 4479155 = 6718733) B6718733
theorem B2986103 : Blo 1989435 2986103 := bstep (se 1 (by rfl) ⟨2239577, by rfl⟩ : syracuseStep 2986103 = 4479155) B4479155
theorem B1990735 : Blo 1989435 1990735 := bstep (se 1 (by rfl) ⟨1493051, by rfl⟩ : syracuseStep 1990735 = 2986103) B2986103
theorem B2986109 : Blo 1989435 2986109 := bbase (se 3 (by rfl) ⟨559895, by rfl⟩ : syracuseStep 2986109 = 1119791) (by norm_num)
theorem B1990739 : Blo 1989435 1990739 := bstep (se 1 (by rfl) ⟨1493054, by rfl⟩ : syracuseStep 1990739 = 2986109) B2986109
theorem B4479173 : Blo 1989435 4479173 := bbase (se 4 (by rfl) ⟨419922, by rfl⟩ : syracuseStep 4479173 = 839845) (by norm_num)
theorem B2986115 : Blo 1989435 2986115 := bstep (se 1 (by rfl) ⟨2239586, by rfl⟩ : syracuseStep 2986115 = 4479173) B4479173
theorem B1990743 : Blo 1989435 1990743 := bstep (se 1 (by rfl) ⟨1493057, by rfl⟩ : syracuseStep 1990743 = 2986115) B2986115
theorem B30646997 : Blo 1989435 30646997 := bbase (se 7 (by rfl) ⟨359144, by rfl⟩ : syracuseStep 30646997 = 718289) (by norm_num)
theorem B20431331 : Blo 1989435 20431331 := bstep (se 1 (by rfl) ⟨15323498, by rfl⟩ : syracuseStep 20431331 = 30646997) B30646997
theorem B13620887 : Blo 1989435 13620887 := bstep (se 1 (by rfl) ⟨10215665, by rfl⟩ : syracuseStep 13620887 = 20431331) B20431331
theorem B9080591 : Blo 1989435 9080591 := bstep (se 1 (by rfl) ⟨6810443, by rfl⟩ : syracuseStep 9080591 = 13620887) B13620887
theorem B24214909 : Blo 1989435 24214909 := bstep (se 3 (by rfl) ⟨4540295, by rfl⟩ : syracuseStep 24214909 = 9080591) B9080591
theorem B32286545 : Blo 1989435 32286545 := bstep (se 2 (by rfl) ⟨12107454, by rfl⟩ : syracuseStep 32286545 = 24214909) B24214909
theorem B21524363 : Blo 1989435 21524363 := bstep (se 1 (by rfl) ⟨16143272, by rfl⟩ : syracuseStep 21524363 = 32286545) B32286545
theorem B14349575 : Blo 1989435 14349575 := bstep (se 1 (by rfl) ⟨10762181, by rfl⟩ : syracuseStep 14349575 = 21524363) B21524363
theorem B9566383 : Blo 1989435 9566383 := bstep (se 1 (by rfl) ⟨7174787, by rfl⟩ : syracuseStep 9566383 = 14349575) B14349575
theorem B12755177 : Blo 1989435 12755177 := bstep (se 2 (by rfl) ⟨4783191, by rfl⟩ : syracuseStep 12755177 = 9566383) B9566383
theorem B8503451 : Blo 1989435 8503451 := bstep (se 1 (by rfl) ⟨6377588, by rfl⟩ : syracuseStep 8503451 = 12755177) B12755177
theorem B5668967 : Blo 1989435 5668967 := bstep (se 1 (by rfl) ⟨4251725, by rfl⟩ : syracuseStep 5668967 = 8503451) B8503451
theorem B3779311 : Blo 1989435 3779311 := bstep (se 1 (by rfl) ⟨2834483, by rfl⟩ : syracuseStep 3779311 = 5668967) B5668967
theorem B5039081 : Blo 1989435 5039081 := bstep (se 2 (by rfl) ⟨1889655, by rfl⟩ : syracuseStep 5039081 = 3779311) B3779311
theorem B3359387 : Blo 1989435 3359387 := bstep (se 1 (by rfl) ⟨2519540, by rfl⟩ : syracuseStep 3359387 = 5039081) B5039081
theorem B2239591 : Blo 1989435 2239591 := bstep (se 1 (by rfl) ⟨1679693, by rfl⟩ : syracuseStep 2239591 = 3359387) B3359387
theorem B2986121 : Blo 1989435 2986121 := bstep (se 2 (by rfl) ⟨1119795, by rfl⟩ : syracuseStep 2986121 = 2239591) B2239591
theorem B1990747 : Blo 1989435 1990747 := bstep (se 1 (by rfl) ⟨1493060, by rfl⟩ : syracuseStep 1990747 = 2986121) B2986121
theorem B10078181 : Blo 1989435 10078181 := bbase (se 4 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 10078181 = 1889659) (by norm_num)
theorem B6718787 : Blo 1989435 6718787 := bstep (se 1 (by rfl) ⟨5039090, by rfl⟩ : syracuseStep 6718787 = 10078181) B10078181
theorem B4479191 : Blo 1989435 4479191 := bstep (se 1 (by rfl) ⟨3359393, by rfl⟩ : syracuseStep 4479191 = 6718787) B6718787
theorem B2986127 : Blo 1989435 2986127 := bstep (se 1 (by rfl) ⟨2239595, by rfl⟩ : syracuseStep 2986127 = 4479191) B4479191
theorem B1990751 : Blo 1989435 1990751 := bstep (se 1 (by rfl) ⟨1493063, by rfl⟩ : syracuseStep 1990751 = 2986127) B2986127
theorem B2986133 : Blo 1989435 2986133 := bbase (se 6 (by rfl) ⟨69987, by rfl⟩ : syracuseStep 2986133 = 139975) (by norm_num)
theorem B1990755 : Blo 1989435 1990755 := bstep (se 1 (by rfl) ⟨1493066, by rfl⟩ : syracuseStep 1990755 = 2986133) B2986133
theorem B3188813 : Blo 1989435 3188813 := bbase (se 3 (by rfl) ⟨597902, by rfl⟩ : syracuseStep 3188813 = 1195805) (by norm_num)
theorem B8503501 : Blo 1989435 8503501 := bstep (se 3 (by rfl) ⟨1594406, by rfl⟩ : syracuseStep 8503501 = 3188813) B3188813
theorem B11338001 : Blo 1989435 11338001 := bstep (se 2 (by rfl) ⟨4251750, by rfl⟩ : syracuseStep 11338001 = 8503501) B8503501
theorem B7558667 : Blo 1989435 7558667 := bstep (se 1 (by rfl) ⟨5669000, by rfl⟩ : syracuseStep 7558667 = 11338001) B11338001
theorem B5039111 : Blo 1989435 5039111 := bstep (se 1 (by rfl) ⟨3779333, by rfl⟩ : syracuseStep 5039111 = 7558667) B7558667
theorem B3359407 : Blo 1989435 3359407 := bstep (se 1 (by rfl) ⟨2519555, by rfl⟩ : syracuseStep 3359407 = 5039111) B5039111
theorem B4479209 : Blo 1989435 4479209 := bstep (se 2 (by rfl) ⟨1679703, by rfl⟩ : syracuseStep 4479209 = 3359407) B3359407
theorem B2986139 : Blo 1989435 2986139 := bstep (se 1 (by rfl) ⟨2239604, by rfl⟩ : syracuseStep 2986139 = 4479209) B4479209
theorem B1990759 : Blo 1989435 1990759 := bstep (se 1 (by rfl) ⟨1493069, by rfl⟩ : syracuseStep 1990759 = 2986139) B2986139
theorem B2239609 : Blo 1989435 2239609 := bbase (se 2 (by rfl) ⟨839853, by rfl⟩ : syracuseStep 2239609 = 1679707) (by norm_num)
theorem B2986145 : Blo 1989435 2986145 := bstep (se 2 (by rfl) ⟨1119804, by rfl⟩ : syracuseStep 2986145 = 2239609) B2239609
theorem B1990763 : Blo 1989435 1990763 := bstep (se 1 (by rfl) ⟨1493072, by rfl⟩ : syracuseStep 1990763 = 2986145) B2986145
theorem B9696997 : Blo 1989435 9696997 := bbase (se 4 (by rfl) ⟨909093, by rfl⟩ : syracuseStep 9696997 = 1818187) (by norm_num)
theorem B12929329 : Blo 1989435 12929329 := bstep (se 2 (by rfl) ⟨4848498, by rfl⟩ : syracuseStep 12929329 = 9696997) B9696997
theorem B17239105 : Blo 1989435 17239105 := bstep (se 2 (by rfl) ⟨6464664, by rfl⟩ : syracuseStep 17239105 = 12929329) B12929329
theorem B22985473 : Blo 1989435 22985473 := bstep (se 2 (by rfl) ⟨8619552, by rfl⟩ : syracuseStep 22985473 = 17239105) B17239105
theorem B30647297 : Blo 1989435 30647297 := bstep (se 2 (by rfl) ⟨11492736, by rfl⟩ : syracuseStep 30647297 = 22985473) B22985473
theorem B20431531 : Blo 1989435 20431531 := bstep (se 1 (by rfl) ⟨15323648, by rfl⟩ : syracuseStep 20431531 = 30647297) B30647297
theorem B108968165 : Blo 1989435 108968165 := bstep (se 4 (by rfl) ⟨10215765, by rfl⟩ : syracuseStep 108968165 = 20431531) B20431531
theorem B72645443 : Blo 1989435 72645443 := bstep (se 1 (by rfl) ⟨54484082, by rfl⟩ : syracuseStep 72645443 = 108968165) B108968165
theorem B48430295 : Blo 1989435 48430295 := bstep (se 1 (by rfl) ⟨36322721, by rfl⟩ : syracuseStep 48430295 = 72645443) B72645443
theorem B32286863 : Blo 1989435 32286863 := bstep (se 1 (by rfl) ⟨24215147, by rfl⟩ : syracuseStep 32286863 = 48430295) B48430295
theorem B21524575 : Blo 1989435 21524575 := bstep (se 1 (by rfl) ⟨16143431, by rfl⟩ : syracuseStep 21524575 = 32286863) B32286863
theorem B28699433 : Blo 1989435 28699433 := bstep (se 2 (by rfl) ⟨10762287, by rfl⟩ : syracuseStep 28699433 = 21524575) B21524575
theorem B19132955 : Blo 1989435 19132955 := bstep (se 1 (by rfl) ⟨14349716, by rfl⟩ : syracuseStep 19132955 = 28699433) B28699433
theorem B12755303 : Blo 1989435 12755303 := bstep (se 1 (by rfl) ⟨9566477, by rfl⟩ : syracuseStep 12755303 = 19132955) B19132955
theorem B8503535 : Blo 1989435 8503535 := bstep (se 1 (by rfl) ⟨6377651, by rfl⟩ : syracuseStep 8503535 = 12755303) B12755303
theorem B5669023 : Blo 1989435 5669023 := bstep (se 1 (by rfl) ⟨4251767, by rfl⟩ : syracuseStep 5669023 = 8503535) B8503535
theorem B7558697 : Blo 1989435 7558697 := bstep (se 2 (by rfl) ⟨2834511, by rfl⟩ : syracuseStep 7558697 = 5669023) B5669023
theorem B5039131 : Blo 1989435 5039131 := bstep (se 1 (by rfl) ⟨3779348, by rfl⟩ : syracuseStep 5039131 = 7558697) B7558697
theorem B6718841 : Blo 1989435 6718841 := bstep (se 2 (by rfl) ⟨2519565, by rfl⟩ : syracuseStep 6718841 = 5039131) B5039131
theorem B4479227 : Blo 1989435 4479227 := bstep (se 1 (by rfl) ⟨3359420, by rfl⟩ : syracuseStep 4479227 = 6718841) B6718841
theorem B2986151 : Blo 1989435 2986151 := bstep (se 1 (by rfl) ⟨2239613, by rfl⟩ : syracuseStep 2986151 = 4479227) B4479227
theorem B1990767 : Blo 1989435 1990767 := bstep (se 1 (by rfl) ⟨1493075, by rfl⟩ : syracuseStep 1990767 = 2986151) B2986151
theorem B2986157 : Blo 1989435 2986157 := bbase (se 3 (by rfl) ⟨559904, by rfl⟩ : syracuseStep 2986157 = 1119809) (by norm_num)
theorem B1990771 : Blo 1989435 1990771 := bstep (se 1 (by rfl) ⟨1493078, by rfl⟩ : syracuseStep 1990771 = 2986157) B2986157
theorem B4479245 : Blo 1989435 4479245 := bbase (se 3 (by rfl) ⟨839858, by rfl⟩ : syracuseStep 4479245 = 1679717) (by norm_num)
theorem B2986163 : Blo 1989435 2986163 := bstep (se 1 (by rfl) ⟨2239622, by rfl⟩ : syracuseStep 2986163 = 4479245) B4479245
theorem B1990775 : Blo 1989435 1990775 := bstep (se 1 (by rfl) ⟨1493081, by rfl⟩ : syracuseStep 1990775 = 2986163) B2986163
theorem B2519581 : Blo 1989435 2519581 := bbase (se 3 (by rfl) ⟨472421, by rfl⟩ : syracuseStep 2519581 = 944843) (by norm_num)
theorem B3359441 : Blo 1989435 3359441 := bstep (se 2 (by rfl) ⟨1259790, by rfl⟩ : syracuseStep 3359441 = 2519581) B2519581
theorem B2239627 : Blo 1989435 2239627 := bstep (se 1 (by rfl) ⟨1679720, by rfl⟩ : syracuseStep 2239627 = 3359441) B3359441
theorem B2986169 : Blo 1989435 2986169 := bstep (se 2 (by rfl) ⟨1119813, by rfl⟩ : syracuseStep 2986169 = 2239627) B2239627
theorem B1990779 : Blo 1989435 1990779 := bstep (se 1 (by rfl) ⟨1493084, by rfl⟩ : syracuseStep 1990779 = 2986169) B2986169
theorem B4783277 : Blo 1989435 4783277 := bbase (se 3 (by rfl) ⟨896864, by rfl⟩ : syracuseStep 4783277 = 1793729) (by norm_num)
theorem B3188851 : Blo 1989435 3188851 := bstep (se 1 (by rfl) ⟨2391638, by rfl⟩ : syracuseStep 3188851 = 4783277) B4783277
theorem B17007205 : Blo 1989435 17007205 := bstep (se 4 (by rfl) ⟨1594425, by rfl⟩ : syracuseStep 17007205 = 3188851) B3188851
theorem B22676273 : Blo 1989435 22676273 := bstep (se 2 (by rfl) ⟨8503602, by rfl⟩ : syracuseStep 22676273 = 17007205) B17007205
theorem B15117515 : Blo 1989435 15117515 := bstep (se 1 (by rfl) ⟨11338136, by rfl⟩ : syracuseStep 15117515 = 22676273) B22676273
theorem B10078343 : Blo 1989435 10078343 := bstep (se 1 (by rfl) ⟨7558757, by rfl⟩ : syracuseStep 10078343 = 15117515) B15117515
theorem B6718895 : Blo 1989435 6718895 := bstep (se 1 (by rfl) ⟨5039171, by rfl⟩ : syracuseStep 6718895 = 10078343) B10078343
theorem B4479263 : Blo 1989435 4479263 := bstep (se 1 (by rfl) ⟨3359447, by rfl⟩ : syracuseStep 4479263 = 6718895) B6718895
theorem B2986175 : Blo 1989435 2986175 := bstep (se 1 (by rfl) ⟨2239631, by rfl⟩ : syracuseStep 2986175 = 4479263) B4479263
theorem B1990783 : Blo 1989435 1990783 := bstep (se 1 (by rfl) ⟨1493087, by rfl⟩ : syracuseStep 1990783 = 2986175) B2986175
theorem B2986181 : Blo 1989435 2986181 := bbase (se 4 (by rfl) ⟨279954, by rfl⟩ : syracuseStep 2986181 = 559909) (by norm_num)
theorem B1990787 : Blo 1989435 1990787 := bstep (se 1 (by rfl) ⟨1493090, by rfl⟩ : syracuseStep 1990787 = 2986181) B2986181
theorem B3359461 : Blo 1989435 3359461 := bbase (se 4 (by rfl) ⟨314949, by rfl⟩ : syracuseStep 3359461 = 629899) (by norm_num)
theorem B4479281 : Blo 1989435 4479281 := bstep (se 2 (by rfl) ⟨1679730, by rfl⟩ : syracuseStep 4479281 = 3359461) B3359461
theorem B2986187 : Blo 1989435 2986187 := bstep (se 1 (by rfl) ⟨2239640, by rfl⟩ : syracuseStep 2986187 = 4479281) B4479281
theorem B1990791 : Blo 1989435 1990791 := bstep (se 1 (by rfl) ⟨1493093, by rfl⟩ : syracuseStep 1990791 = 2986187) B2986187
theorem B2239645 : Blo 1989435 2239645 := bbase (se 3 (by rfl) ⟨419933, by rfl⟩ : syracuseStep 2239645 = 839867) (by norm_num)
theorem B2986193 : Blo 1989435 2986193 := bstep (se 2 (by rfl) ⟨1119822, by rfl⟩ : syracuseStep 2986193 = 2239645) B2239645
theorem B1990795 : Blo 1989435 1990795 := bstep (se 1 (by rfl) ⟨1493096, by rfl⟩ : syracuseStep 1990795 = 2986193) B2986193
theorem B6718949 : Blo 1989435 6718949 := bbase (se 4 (by rfl) ⟨629901, by rfl⟩ : syracuseStep 6718949 = 1259803) (by norm_num)
theorem B4479299 : Blo 1989435 4479299 := bstep (se 1 (by rfl) ⟨3359474, by rfl⟩ : syracuseStep 4479299 = 6718949) B6718949
theorem B2986199 : Blo 1989435 2986199 := bstep (se 1 (by rfl) ⟨2239649, by rfl⟩ : syracuseStep 2986199 = 4479299) B4479299
theorem B1990799 : Blo 1989435 1990799 := bstep (se 1 (by rfl) ⟨1493099, by rfl⟩ : syracuseStep 1990799 = 2986199) B2986199
theorem B2986205 : Blo 1989435 2986205 := bbase (se 3 (by rfl) ⟨559913, by rfl⟩ : syracuseStep 2986205 = 1119827) (by norm_num)
theorem B1990803 : Blo 1989435 1990803 := bstep (se 1 (by rfl) ⟨1493102, by rfl⟩ : syracuseStep 1990803 = 2986205) B2986205
theorem B4479317 : Blo 1989435 4479317 := bbase (se 10 (by rfl) ⟨6561, by rfl⟩ : syracuseStep 4479317 = 13123) (by norm_num)
theorem B2986211 : Blo 1989435 2986211 := bstep (se 1 (by rfl) ⟨2239658, by rfl⟩ : syracuseStep 2986211 = 4479317) B4479317
theorem B1990807 : Blo 1989435 1990807 := bstep (se 1 (by rfl) ⟨1493105, by rfl⟩ : syracuseStep 1990807 = 2986211) B2986211
theorem B2391673 : Blo 1989435 2391673 := bbase (se 2 (by rfl) ⟨896877, by rfl⟩ : syracuseStep 2391673 = 1793755) (by norm_num)
theorem B3188897 : Blo 1989435 3188897 := bstep (se 2 (by rfl) ⟨1195836, by rfl⟩ : syracuseStep 3188897 = 2391673) B2391673
theorem B2125931 : Blo 1989435 2125931 := bstep (se 1 (by rfl) ⟨1594448, by rfl⟩ : syracuseStep 2125931 = 3188897) B3188897
theorem B5669149 : Blo 1989435 5669149 := bstep (se 3 (by rfl) ⟨1062965, by rfl⟩ : syracuseStep 5669149 = 2125931) B2125931
theorem B7558865 : Blo 1989435 7558865 := bstep (se 2 (by rfl) ⟨2834574, by rfl⟩ : syracuseStep 7558865 = 5669149) B5669149
theorem B5039243 : Blo 1989435 5039243 := bstep (se 1 (by rfl) ⟨3779432, by rfl⟩ : syracuseStep 5039243 = 7558865) B7558865
theorem B3359495 : Blo 1989435 3359495 := bstep (se 1 (by rfl) ⟨2519621, by rfl⟩ : syracuseStep 3359495 = 5039243) B5039243
theorem B2239663 : Blo 1989435 2239663 := bstep (se 1 (by rfl) ⟨1679747, by rfl⟩ : syracuseStep 2239663 = 3359495) B3359495
theorem B2986217 : Blo 1989435 2986217 := bstep (se 2 (by rfl) ⟨1119831, by rfl⟩ : syracuseStep 2986217 = 2239663) B2239663
theorem B1990811 : Blo 1989435 1990811 := bstep (se 1 (by rfl) ⟨1493108, by rfl⟩ : syracuseStep 1990811 = 2986217) B2986217
theorem B2270225 : Blo 1989435 2270225 := bbase (se 2 (by rfl) ⟨851334, by rfl⟩ : syracuseStep 2270225 = 1702669) (by norm_num)
theorem B6053933 : Blo 1989435 6053933 := bstep (se 3 (by rfl) ⟨1135112, by rfl⟩ : syracuseStep 6053933 = 2270225) B2270225
theorem B4035955 : Blo 1989435 4035955 := bstep (se 1 (by rfl) ⟨3026966, by rfl⟩ : syracuseStep 4035955 = 6053933) B6053933
theorem B5381273 : Blo 1989435 5381273 := bstep (se 2 (by rfl) ⟨2017977, by rfl⟩ : syracuseStep 5381273 = 4035955) B4035955
theorem B14350061 : Blo 1989435 14350061 := bstep (se 3 (by rfl) ⟨2690636, by rfl⟩ : syracuseStep 14350061 = 5381273) B5381273
theorem B38266829 : Blo 1989435 38266829 := bstep (se 3 (by rfl) ⟨7175030, by rfl⟩ : syracuseStep 38266829 = 14350061) B14350061
theorem B25511219 : Blo 1989435 25511219 := bstep (se 1 (by rfl) ⟨19133414, by rfl⟩ : syracuseStep 25511219 = 38266829) B38266829
theorem B17007479 : Blo 1989435 17007479 := bstep (se 1 (by rfl) ⟨12755609, by rfl⟩ : syracuseStep 17007479 = 25511219) B25511219
theorem B11338319 : Blo 1989435 11338319 := bstep (se 1 (by rfl) ⟨8503739, by rfl⟩ : syracuseStep 11338319 = 17007479) B17007479
theorem B7558879 : Blo 1989435 7558879 := bstep (se 1 (by rfl) ⟨5669159, by rfl⟩ : syracuseStep 7558879 = 11338319) B11338319
theorem B10078505 : Blo 1989435 10078505 := bstep (se 2 (by rfl) ⟨3779439, by rfl⟩ : syracuseStep 10078505 = 7558879) B7558879
theorem B6719003 : Blo 1989435 6719003 := bstep (se 1 (by rfl) ⟨5039252, by rfl⟩ : syracuseStep 6719003 = 10078505) B10078505
theorem B4479335 : Blo 1989435 4479335 := bstep (se 1 (by rfl) ⟨3359501, by rfl⟩ : syracuseStep 4479335 = 6719003) B6719003
theorem B2986223 : Blo 1989435 2986223 := bstep (se 1 (by rfl) ⟨2239667, by rfl⟩ : syracuseStep 2986223 = 4479335) B4479335
theorem B1990815 : Blo 1989435 1990815 := bstep (se 1 (by rfl) ⟨1493111, by rfl⟩ : syracuseStep 1990815 = 2986223) B2986223
theorem B2986229 : Blo 1989435 2986229 := bbase (se 5 (by rfl) ⟨139979, by rfl⟩ : syracuseStep 2986229 = 279959) (by norm_num)
theorem B1990819 : Blo 1989435 1990819 := bstep (se 1 (by rfl) ⟨1493114, by rfl⟩ : syracuseStep 1990819 = 2986229) B2986229
theorem B8619797 : Blo 1989435 8619797 := bbase (se 6 (by rfl) ⟨202026, by rfl⟩ : syracuseStep 8619797 = 404053) (by norm_num)
theorem B5746531 : Blo 1989435 5746531 := bstep (se 1 (by rfl) ⟨4309898, by rfl⟩ : syracuseStep 5746531 = 8619797) B8619797
theorem B7662041 : Blo 1989435 7662041 := bstep (se 2 (by rfl) ⟨2873265, by rfl⟩ : syracuseStep 7662041 = 5746531) B5746531
theorem B5108027 : Blo 1989435 5108027 := bstep (se 1 (by rfl) ⟨3831020, by rfl⟩ : syracuseStep 5108027 = 7662041) B7662041
theorem B54485621 : Blo 1989435 54485621 := bstep (se 5 (by rfl) ⟨2554013, by rfl⟩ : syracuseStep 54485621 = 5108027) B5108027
theorem B36323747 : Blo 1989435 36323747 := bstep (se 1 (by rfl) ⟨27242810, by rfl⟩ : syracuseStep 36323747 = 54485621) B54485621
theorem B24215831 : Blo 1989435 24215831 := bstep (se 1 (by rfl) ⟨18161873, by rfl⟩ : syracuseStep 24215831 = 36323747) B36323747
theorem B16143887 : Blo 1989435 16143887 := bstep (se 1 (by rfl) ⟨12107915, by rfl⟩ : syracuseStep 16143887 = 24215831) B24215831
theorem B43050365 : Blo 1989435 43050365 := bstep (se 3 (by rfl) ⟨8071943, by rfl⟩ : syracuseStep 43050365 = 16143887) B16143887
theorem B28700243 : Blo 1989435 28700243 := bstep (se 1 (by rfl) ⟨21525182, by rfl⟩ : syracuseStep 28700243 = 43050365) B43050365
theorem B19133495 : Blo 1989435 19133495 := bstep (se 1 (by rfl) ⟨14350121, by rfl⟩ : syracuseStep 19133495 = 28700243) B28700243
theorem B12755663 : Blo 1989435 12755663 := bstep (se 1 (by rfl) ⟨9566747, by rfl⟩ : syracuseStep 12755663 = 19133495) B19133495
theorem B8503775 : Blo 1989435 8503775 := bstep (se 1 (by rfl) ⟨6377831, by rfl⟩ : syracuseStep 8503775 = 12755663) B12755663
theorem B5669183 : Blo 1989435 5669183 := bstep (se 1 (by rfl) ⟨4251887, by rfl⟩ : syracuseStep 5669183 = 8503775) B8503775
theorem B3779455 : Blo 1989435 3779455 := bstep (se 1 (by rfl) ⟨2834591, by rfl⟩ : syracuseStep 3779455 = 5669183) B5669183
theorem B5039273 : Blo 1989435 5039273 := bstep (se 2 (by rfl) ⟨1889727, by rfl⟩ : syracuseStep 5039273 = 3779455) B3779455
theorem B3359515 : Blo 1989435 3359515 := bstep (se 1 (by rfl) ⟨2519636, by rfl⟩ : syracuseStep 3359515 = 5039273) B5039273
theorem B4479353 : Blo 1989435 4479353 := bstep (se 2 (by rfl) ⟨1679757, by rfl⟩ : syracuseStep 4479353 = 3359515) B3359515
theorem B2986235 : Blo 1989435 2986235 := bstep (se 1 (by rfl) ⟨2239676, by rfl⟩ : syracuseStep 2986235 = 4479353) B4479353
theorem B1990823 : Blo 1989435 1990823 := bstep (se 1 (by rfl) ⟨1493117, by rfl⟩ : syracuseStep 1990823 = 2986235) B2986235
theorem B2239681 : Blo 1989435 2239681 := bbase (se 2 (by rfl) ⟨839880, by rfl⟩ : syracuseStep 2239681 = 1679761) (by norm_num)
theorem B2986241 : Blo 1989435 2986241 := bstep (se 2 (by rfl) ⟨1119840, by rfl⟩ : syracuseStep 2986241 = 2239681) B2239681
theorem B1990827 : Blo 1989435 1990827 := bstep (se 1 (by rfl) ⟨1493120, by rfl⟩ : syracuseStep 1990827 = 2986241) B2986241
theorem B5039293 : Blo 1989435 5039293 := bbase (se 3 (by rfl) ⟨944867, by rfl⟩ : syracuseStep 5039293 = 1889735) (by norm_num)
theorem B6719057 : Blo 1989435 6719057 := bstep (se 2 (by rfl) ⟨2519646, by rfl⟩ : syracuseStep 6719057 = 5039293) B5039293
theorem B4479371 : Blo 1989435 4479371 := bstep (se 1 (by rfl) ⟨3359528, by rfl⟩ : syracuseStep 4479371 = 6719057) B6719057
theorem B2986247 : Blo 1989435 2986247 := bstep (se 1 (by rfl) ⟨2239685, by rfl⟩ : syracuseStep 2986247 = 4479371) B4479371
theorem B1990831 : Blo 1989435 1990831 := bstep (se 1 (by rfl) ⟨1493123, by rfl⟩ : syracuseStep 1990831 = 2986247) B2986247
theorem B2986253 : Blo 1989435 2986253 := bbase (se 3 (by rfl) ⟨559922, by rfl⟩ : syracuseStep 2986253 = 1119845) (by norm_num)
theorem B1990835 : Blo 1989435 1990835 := bstep (se 1 (by rfl) ⟨1493126, by rfl⟩ : syracuseStep 1990835 = 2986253) B2986253
theorem B4479389 : Blo 1989435 4479389 := bbase (se 3 (by rfl) ⟨839885, by rfl⟩ : syracuseStep 4479389 = 1679771) (by norm_num)
theorem B2986259 : Blo 1989435 2986259 := bstep (se 1 (by rfl) ⟨2239694, by rfl⟩ : syracuseStep 2986259 = 4479389) B4479389
theorem B1990839 : Blo 1989435 1990839 := bstep (se 1 (by rfl) ⟨1493129, by rfl⟩ : syracuseStep 1990839 = 2986259) B2986259
theorem B3359549 : Blo 1989435 3359549 := bbase (se 3 (by rfl) ⟨629915, by rfl⟩ : syracuseStep 3359549 = 1259831) (by norm_num)
theorem B2239699 : Blo 1989435 2239699 := bstep (se 1 (by rfl) ⟨1679774, by rfl⟩ : syracuseStep 2239699 = 3359549) B3359549
theorem B2986265 : Blo 1989435 2986265 := bstep (se 2 (by rfl) ⟨1119849, by rfl⟩ : syracuseStep 2986265 = 2239699) B2239699
theorem B1990843 : Blo 1989435 1990843 := bstep (se 1 (by rfl) ⟨1493132, by rfl⟩ : syracuseStep 1990843 = 2986265) B2986265
theorem B2125969 : Blo 1989435 2125969 := bbase (se 2 (by rfl) ⟨797238, by rfl⟩ : syracuseStep 2125969 = 1594477) (by norm_num)
theorem B11338501 : Blo 1989435 11338501 := bstep (se 4 (by rfl) ⟨1062984, by rfl⟩ : syracuseStep 11338501 = 2125969) B2125969
theorem B15118001 : Blo 1989435 15118001 := bstep (se 2 (by rfl) ⟨5669250, by rfl⟩ : syracuseStep 15118001 = 11338501) B11338501
theorem B10078667 : Blo 1989435 10078667 := bstep (se 1 (by rfl) ⟨7559000, by rfl⟩ : syracuseStep 10078667 = 15118001) B15118001
theorem B6719111 : Blo 1989435 6719111 := bstep (se 1 (by rfl) ⟨5039333, by rfl⟩ : syracuseStep 6719111 = 10078667) B10078667
theorem B4479407 : Blo 1989435 4479407 := bstep (se 1 (by rfl) ⟨3359555, by rfl⟩ : syracuseStep 4479407 = 6719111) B6719111
theorem B2986271 : Blo 1989435 2986271 := bstep (se 1 (by rfl) ⟨2239703, by rfl⟩ : syracuseStep 2986271 = 4479407) B4479407
theorem B1990847 : Blo 1989435 1990847 := bstep (se 1 (by rfl) ⟨1493135, by rfl⟩ : syracuseStep 1990847 = 2986271) B2986271
theorem B2986277 : Blo 1989435 2986277 := bbase (se 4 (by rfl) ⟨279963, by rfl⟩ : syracuseStep 2986277 = 559927) (by norm_num)
theorem B1990851 : Blo 1989435 1990851 := bstep (se 1 (by rfl) ⟨1493138, by rfl⟩ : syracuseStep 1990851 = 2986277) B2986277
theorem B2519677 : Blo 1989435 2519677 := bbase (se 3 (by rfl) ⟨472439, by rfl⟩ : syracuseStep 2519677 = 944879) (by norm_num)
theorem B3359569 : Blo 1989435 3359569 := bstep (se 2 (by rfl) ⟨1259838, by rfl⟩ : syracuseStep 3359569 = 2519677) B2519677
theorem B4479425 : Blo 1989435 4479425 := bstep (se 2 (by rfl) ⟨1679784, by rfl⟩ : syracuseStep 4479425 = 3359569) B3359569
theorem B2986283 : Blo 1989435 2986283 := bstep (se 1 (by rfl) ⟨2239712, by rfl⟩ : syracuseStep 2986283 = 4479425) B4479425
theorem B1990855 : Blo 1989435 1990855 := bstep (se 1 (by rfl) ⟨1493141, by rfl⟩ : syracuseStep 1990855 = 2986283) B2986283
theorem B2239717 : Blo 1989435 2239717 := bbase (se 4 (by rfl) ⟨209973, by rfl⟩ : syracuseStep 2239717 = 419947) (by norm_num)
theorem B2986289 : Blo 1989435 2986289 := bstep (se 2 (by rfl) ⟨1119858, by rfl⟩ : syracuseStep 2986289 = 2239717) B2239717
theorem B1990859 : Blo 1989435 1990859 := bstep (se 1 (by rfl) ⟨1493144, by rfl⟩ : syracuseStep 1990859 = 2986289) B2986289
theorem B4251973 : Blo 1989435 4251973 := bbase (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) (by norm_num)
theorem B5669297 : Blo 1989435 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B3779531 : Blo 1989435 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B2519687 : Blo 1989435 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B6719165 : Blo 1989435 6719165 := bstep (se 3 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 6719165 = 2519687) B2519687
theorem B4479443 : Blo 1989435 4479443 := bstep (se 1 (by rfl) ⟨3359582, by rfl⟩ : syracuseStep 4479443 = 6719165) B6719165
theorem B2986295 : Blo 1989435 2986295 := bstep (se 1 (by rfl) ⟨2239721, by rfl⟩ : syracuseStep 2986295 = 4479443) B4479443
theorem B1990863 : Blo 1989435 1990863 := bstep (se 1 (by rfl) ⟨1493147, by rfl⟩ : syracuseStep 1990863 = 2986295) B2986295
theorem B2986301 : Blo 1989435 2986301 := bbase (se 3 (by rfl) ⟨559931, by rfl⟩ : syracuseStep 2986301 = 1119863) (by norm_num)
theorem B1990867 : Blo 1989435 1990867 := bstep (se 1 (by rfl) ⟨1493150, by rfl⟩ : syracuseStep 1990867 = 2986301) B2986301
theorem B4479461 : Blo 1989435 4479461 := bbase (se 4 (by rfl) ⟨419949, by rfl⟩ : syracuseStep 4479461 = 839899) (by norm_num)
theorem B2986307 : Blo 1989435 2986307 := bstep (se 1 (by rfl) ⟨2239730, by rfl⟩ : syracuseStep 2986307 = 4479461) B4479461
theorem B1990871 : Blo 1989435 1990871 := bstep (se 1 (by rfl) ⟨1493153, by rfl⟩ : syracuseStep 1990871 = 2986307) B2986307
theorem B5039405 : Blo 1989435 5039405 := bbase (se 3 (by rfl) ⟨944888, by rfl⟩ : syracuseStep 5039405 = 1889777) (by norm_num)
theorem B3359603 : Blo 1989435 3359603 := bstep (se 1 (by rfl) ⟨2519702, by rfl⟩ : syracuseStep 3359603 = 5039405) B5039405
theorem B2239735 : Blo 1989435 2239735 := bstep (se 1 (by rfl) ⟨1679801, by rfl⟩ : syracuseStep 2239735 = 3359603) B3359603
theorem B2986313 : Blo 1989435 2986313 := bstep (se 2 (by rfl) ⟨1119867, by rfl⟩ : syracuseStep 2986313 = 2239735) B2239735
theorem B1990875 : Blo 1989435 1990875 := bstep (se 1 (by rfl) ⟨1493156, by rfl⟩ : syracuseStep 1990875 = 2986313) B2986313
theorem B22986773 : Blo 1989435 22986773 := bbase (se 6 (by rfl) ⟨538752, by rfl⟩ : syracuseStep 22986773 = 1077505) (by norm_num)
theorem B15324515 : Blo 1989435 15324515 := bstep (se 1 (by rfl) ⟨11493386, by rfl⟩ : syracuseStep 15324515 = 22986773) B22986773
theorem B10216343 : Blo 1989435 10216343 := bstep (se 1 (by rfl) ⟨7662257, by rfl⟩ : syracuseStep 10216343 = 15324515) B15324515
theorem B6810895 : Blo 1989435 6810895 := bstep (se 1 (by rfl) ⟨5108171, by rfl⟩ : syracuseStep 6810895 = 10216343) B10216343
theorem B36324773 : Blo 1989435 36324773 := bstep (se 4 (by rfl) ⟨3405447, by rfl⟩ : syracuseStep 36324773 = 6810895) B6810895
theorem B24216515 : Blo 1989435 24216515 := bstep (se 1 (by rfl) ⟨18162386, by rfl⟩ : syracuseStep 24216515 = 36324773) B36324773
theorem B16144343 : Blo 1989435 16144343 := bstep (se 1 (by rfl) ⟨12108257, by rfl⟩ : syracuseStep 16144343 = 24216515) B24216515
theorem B10762895 : Blo 1989435 10762895 := bstep (se 1 (by rfl) ⟨8072171, by rfl⟩ : syracuseStep 10762895 = 16144343) B16144343
theorem B7175263 : Blo 1989435 7175263 := bstep (se 1 (by rfl) ⟨5381447, by rfl⟩ : syracuseStep 7175263 = 10762895) B10762895
theorem B9567017 : Blo 1989435 9567017 := bstep (se 2 (by rfl) ⟨3587631, by rfl⟩ : syracuseStep 9567017 = 7175263) B7175263
theorem B6378011 : Blo 1989435 6378011 := bstep (se 1 (by rfl) ⟨4783508, by rfl⟩ : syracuseStep 6378011 = 9567017) B9567017
theorem B4252007 : Blo 1989435 4252007 := bstep (se 1 (by rfl) ⟨3189005, by rfl⟩ : syracuseStep 4252007 = 6378011) B6378011
theorem B2834671 : Blo 1989435 2834671 := bstep (se 1 (by rfl) ⟨2126003, by rfl⟩ : syracuseStep 2834671 = 4252007) B4252007
theorem B3779561 : Blo 1989435 3779561 := bstep (se 2 (by rfl) ⟨1417335, by rfl⟩ : syracuseStep 3779561 = 2834671) B2834671
theorem B10078829 : Blo 1989435 10078829 := bstep (se 3 (by rfl) ⟨1889780, by rfl⟩ : syracuseStep 10078829 = 3779561) B3779561
theorem B6719219 : Blo 1989435 6719219 := bstep (se 1 (by rfl) ⟨5039414, by rfl⟩ : syracuseStep 6719219 = 10078829) B10078829
theorem B4479479 : Blo 1989435 4479479 := bstep (se 1 (by rfl) ⟨3359609, by rfl⟩ : syracuseStep 4479479 = 6719219) B6719219
theorem B2986319 : Blo 1989435 2986319 := bstep (se 1 (by rfl) ⟨2239739, by rfl⟩ : syracuseStep 2986319 = 4479479) B4479479
theorem B1990879 : Blo 1989435 1990879 := bstep (se 1 (by rfl) ⟨1493159, by rfl⟩ : syracuseStep 1990879 = 2986319) B2986319
theorem B2986325 : Blo 1989435 2986325 := bbase (se 10 (by rfl) ⟨4374, by rfl⟩ : syracuseStep 2986325 = 8749) (by norm_num)
theorem B1990883 : Blo 1989435 1990883 := bstep (se 1 (by rfl) ⟨1493162, by rfl⟩ : syracuseStep 1990883 = 2986325) B2986325
theorem B5669365 : Blo 1989435 5669365 := bbase (se 5 (by rfl) ⟨265751, by rfl⟩ : syracuseStep 5669365 = 531503) (by norm_num)
theorem B7559153 : Blo 1989435 7559153 := bstep (se 2 (by rfl) ⟨2834682, by rfl⟩ : syracuseStep 7559153 = 5669365) B5669365
theorem B5039435 : Blo 1989435 5039435 := bstep (se 1 (by rfl) ⟨3779576, by rfl⟩ : syracuseStep 5039435 = 7559153) B7559153
theorem B3359623 : Blo 1989435 3359623 := bstep (se 1 (by rfl) ⟨2519717, by rfl⟩ : syracuseStep 3359623 = 5039435) B5039435
theorem B4479497 : Blo 1989435 4479497 := bstep (se 2 (by rfl) ⟨1679811, by rfl⟩ : syracuseStep 4479497 = 3359623) B3359623
theorem B2986331 : Blo 1989435 2986331 := bstep (se 1 (by rfl) ⟨2239748, by rfl⟩ : syracuseStep 2986331 = 4479497) B4479497
theorem B1990887 : Blo 1989435 1990887 := bstep (se 1 (by rfl) ⟨1493165, by rfl⟩ : syracuseStep 1990887 = 2986331) B2986331
theorem B2239753 : Blo 1989435 2239753 := bbase (se 2 (by rfl) ⟨839907, by rfl⟩ : syracuseStep 2239753 = 1679815) (by norm_num)
theorem B2986337 : Blo 1989435 2986337 := bstep (se 2 (by rfl) ⟨1119876, by rfl⟩ : syracuseStep 2986337 = 2239753) B2239753
theorem B1990891 : Blo 1989435 1990891 := bstep (se 1 (by rfl) ⟨1493168, by rfl⟩ : syracuseStep 1990891 = 2986337) B2986337
theorem B2391773 : Blo 1989435 2391773 := bbase (se 3 (by rfl) ⟨448457, by rfl⟩ : syracuseStep 2391773 = 896915) (by norm_num)
theorem B25512245 : Blo 1989435 25512245 := bstep (se 5 (by rfl) ⟨1195886, by rfl⟩ : syracuseStep 25512245 = 2391773) B2391773
theorem B17008163 : Blo 1989435 17008163 := bstep (se 1 (by rfl) ⟨12756122, by rfl⟩ : syracuseStep 17008163 = 25512245) B25512245
theorem B11338775 : Blo 1989435 11338775 := bstep (se 1 (by rfl) ⟨8504081, by rfl⟩ : syracuseStep 11338775 = 17008163) B17008163
theorem B7559183 : Blo 1989435 7559183 := bstep (se 1 (by rfl) ⟨5669387, by rfl⟩ : syracuseStep 7559183 = 11338775) B11338775
theorem B5039455 : Blo 1989435 5039455 := bstep (se 1 (by rfl) ⟨3779591, by rfl⟩ : syracuseStep 5039455 = 7559183) B7559183
theorem B6719273 : Blo 1989435 6719273 := bstep (se 2 (by rfl) ⟨2519727, by rfl⟩ : syracuseStep 6719273 = 5039455) B5039455
theorem B4479515 : Blo 1989435 4479515 := bstep (se 1 (by rfl) ⟨3359636, by rfl⟩ : syracuseStep 4479515 = 6719273) B6719273
theorem B2986343 : Blo 1989435 2986343 := bstep (se 1 (by rfl) ⟨2239757, by rfl⟩ : syracuseStep 2986343 = 4479515) B4479515
theorem B1990895 : Blo 1989435 1990895 := bstep (se 1 (by rfl) ⟨1493171, by rfl⟩ : syracuseStep 1990895 = 2986343) B2986343
theorem B2986349 : Blo 1989435 2986349 := bbase (se 3 (by rfl) ⟨559940, by rfl⟩ : syracuseStep 2986349 = 1119881) (by norm_num)
theorem B1990899 : Blo 1989435 1990899 := bstep (se 1 (by rfl) ⟨1493174, by rfl⟩ : syracuseStep 1990899 = 2986349) B2986349
theorem B4479533 : Blo 1989435 4479533 := bbase (se 3 (by rfl) ⟨839912, by rfl⟩ : syracuseStep 4479533 = 1679825) (by norm_num)
theorem B2986355 : Blo 1989435 2986355 := bstep (se 1 (by rfl) ⟨2239766, by rfl⟩ : syracuseStep 2986355 = 4479533) B4479533
theorem B1990903 : Blo 1989435 1990903 := bstep (se 1 (by rfl) ⟨1493177, by rfl⟩ : syracuseStep 1990903 = 2986355) B2986355
theorem B8182421 : Blo 1989435 8182421 := bbase (se 6 (by rfl) ⟨191775, by rfl⟩ : syracuseStep 8182421 = 383551) (by norm_num)
theorem B5454947 : Blo 1989435 5454947 := bstep (se 1 (by rfl) ⟨4091210, by rfl⟩ : syracuseStep 5454947 = 8182421) B8182421
theorem B3636631 : Blo 1989435 3636631 := bstep (se 1 (by rfl) ⟨2727473, by rfl⟩ : syracuseStep 3636631 = 5454947) B5454947
theorem B4848841 : Blo 1989435 4848841 := bstep (se 2 (by rfl) ⟨1818315, by rfl⟩ : syracuseStep 4848841 = 3636631) B3636631
theorem B25860485 : Blo 1989435 25860485 := bstep (se 4 (by rfl) ⟨2424420, by rfl⟩ : syracuseStep 25860485 = 4848841) B4848841
theorem B17240323 : Blo 1989435 17240323 := bstep (se 1 (by rfl) ⟨12930242, by rfl⟩ : syracuseStep 17240323 = 25860485) B25860485
theorem B22987097 : Blo 1989435 22987097 := bstep (se 2 (by rfl) ⟨8620161, by rfl⟩ : syracuseStep 22987097 = 17240323) B17240323
theorem B15324731 : Blo 1989435 15324731 := bstep (se 1 (by rfl) ⟨11493548, by rfl⟩ : syracuseStep 15324731 = 22987097) B22987097
theorem B10216487 : Blo 1989435 10216487 := bstep (se 1 (by rfl) ⟨7662365, by rfl⟩ : syracuseStep 10216487 = 15324731) B15324731
theorem B27243965 : Blo 1989435 27243965 := bstep (se 3 (by rfl) ⟨5108243, by rfl⟩ : syracuseStep 27243965 = 10216487) B10216487
theorem B18162643 : Blo 1989435 18162643 := bstep (se 1 (by rfl) ⟨13621982, by rfl⟩ : syracuseStep 18162643 = 27243965) B27243965
theorem B24216857 : Blo 1989435 24216857 := bstep (se 2 (by rfl) ⟨9081321, by rfl⟩ : syracuseStep 24216857 = 18162643) B18162643
theorem B16144571 : Blo 1989435 16144571 := bstep (se 1 (by rfl) ⟨12108428, by rfl⟩ : syracuseStep 16144571 = 24216857) B24216857
theorem B10763047 : Blo 1989435 10763047 := bstep (se 1 (by rfl) ⟨8072285, by rfl⟩ : syracuseStep 10763047 = 16144571) B16144571
theorem B14350729 : Blo 1989435 14350729 := bstep (se 2 (by rfl) ⟨5381523, by rfl⟩ : syracuseStep 14350729 = 10763047) B10763047
theorem B19134305 : Blo 1989435 19134305 := bstep (se 2 (by rfl) ⟨7175364, by rfl⟩ : syracuseStep 19134305 = 14350729) B14350729
theorem B12756203 : Blo 1989435 12756203 := bstep (se 1 (by rfl) ⟨9567152, by rfl⟩ : syracuseStep 12756203 = 19134305) B19134305
theorem B8504135 : Blo 1989435 8504135 := bstep (se 1 (by rfl) ⟨6378101, by rfl⟩ : syracuseStep 8504135 = 12756203) B12756203
theorem B5669423 : Blo 1989435 5669423 := bstep (se 1 (by rfl) ⟨4252067, by rfl⟩ : syracuseStep 5669423 = 8504135) B8504135
theorem B3779615 : Blo 1989435 3779615 := bstep (se 1 (by rfl) ⟨2834711, by rfl⟩ : syracuseStep 3779615 = 5669423) B5669423
theorem B2519743 : Blo 1989435 2519743 := bstep (se 1 (by rfl) ⟨1889807, by rfl⟩ : syracuseStep 2519743 = 3779615) B3779615
theorem B3359657 : Blo 1989435 3359657 := bstep (se 2 (by rfl) ⟨1259871, by rfl⟩ : syracuseStep 3359657 = 2519743) B2519743
theorem B2239771 : Blo 1989435 2239771 := bstep (se 1 (by rfl) ⟨1679828, by rfl⟩ : syracuseStep 2239771 = 3359657) B3359657
theorem B2986361 : Blo 1989435 2986361 := bstep (se 2 (by rfl) ⟨1119885, by rfl⟩ : syracuseStep 2986361 = 2239771) B2239771
theorem B1990907 : Blo 1989435 1990907 := bstep (se 1 (by rfl) ⟨1493180, by rfl⟩ : syracuseStep 1990907 = 2986361) B2986361
theorem B34016597 : Blo 1989435 34016597 := bbase (se 11 (by rfl) ⟨24914, by rfl⟩ : syracuseStep 34016597 = 49829) (by norm_num)
theorem B22677731 : Blo 1989435 22677731 := bstep (se 1 (by rfl) ⟨17008298, by rfl⟩ : syracuseStep 22677731 = 34016597) B34016597
theorem B15118487 : Blo 1989435 15118487 := bstep (se 1 (by rfl) ⟨11338865, by rfl⟩ : syracuseStep 15118487 = 22677731) B22677731
theorem B10078991 : Blo 1989435 10078991 := bstep (se 1 (by rfl) ⟨7559243, by rfl⟩ : syracuseStep 10078991 = 15118487) B15118487
theorem B6719327 : Blo 1989435 6719327 := bstep (se 1 (by rfl) ⟨5039495, by rfl⟩ : syracuseStep 6719327 = 10078991) B10078991
theorem B4479551 : Blo 1989435 4479551 := bstep (se 1 (by rfl) ⟨3359663, by rfl⟩ : syracuseStep 4479551 = 6719327) B6719327
theorem B2986367 : Blo 1989435 2986367 := bstep (se 1 (by rfl) ⟨2239775, by rfl⟩ : syracuseStep 2986367 = 4479551) B4479551
theorem B1990911 : Blo 1989435 1990911 := bstep (se 1 (by rfl) ⟨1493183, by rfl⟩ : syracuseStep 1990911 = 2986367) B2986367
theorem B2986373 : Blo 1989435 2986373 := bbase (se 4 (by rfl) ⟨279972, by rfl⟩ : syracuseStep 2986373 = 559945) (by norm_num)
theorem B1990915 : Blo 1989435 1990915 := bstep (se 1 (by rfl) ⟨1493186, by rfl⟩ : syracuseStep 1990915 = 2986373) B2986373
theorem B3359677 : Blo 1989435 3359677 := bbase (se 3 (by rfl) ⟨629939, by rfl⟩ : syracuseStep 3359677 = 1259879) (by norm_num)
theorem B4479569 : Blo 1989435 4479569 := bstep (se 2 (by rfl) ⟨1679838, by rfl⟩ : syracuseStep 4479569 = 3359677) B3359677
theorem B2986379 : Blo 1989435 2986379 := bstep (se 1 (by rfl) ⟨2239784, by rfl⟩ : syracuseStep 2986379 = 4479569) B4479569
theorem B1990919 : Blo 1989435 1990919 := bstep (se 1 (by rfl) ⟨1493189, by rfl⟩ : syracuseStep 1990919 = 2986379) B2986379
theorem B2239789 : Blo 1989435 2239789 := bbase (se 3 (by rfl) ⟨419960, by rfl⟩ : syracuseStep 2239789 = 839921) (by norm_num)
theorem B2986385 : Blo 1989435 2986385 := bstep (se 2 (by rfl) ⟨1119894, by rfl⟩ : syracuseStep 2986385 = 2239789) B2239789
theorem B1990923 : Blo 1989435 1990923 := bstep (se 1 (by rfl) ⟨1493192, by rfl⟩ : syracuseStep 1990923 = 2986385) B2986385
theorem B6719381 : Blo 1989435 6719381 := bbase (se 6 (by rfl) ⟨157485, by rfl⟩ : syracuseStep 6719381 = 314971) (by norm_num)
theorem B4479587 : Blo 1989435 4479587 := bstep (se 1 (by rfl) ⟨3359690, by rfl⟩ : syracuseStep 4479587 = 6719381) B6719381
theorem B2986391 : Blo 1989435 2986391 := bstep (se 1 (by rfl) ⟨2239793, by rfl⟩ : syracuseStep 2986391 = 4479587) B4479587
theorem B1990927 : Blo 1989435 1990927 := bstep (se 1 (by rfl) ⟨1493195, by rfl⟩ : syracuseStep 1990927 = 2986391) B2986391
theorem B2986397 : Blo 1989435 2986397 := bbase (se 3 (by rfl) ⟨559949, by rfl⟩ : syracuseStep 2986397 = 1119899) (by norm_num)
theorem B1990931 : Blo 1989435 1990931 := bstep (se 1 (by rfl) ⟨1493198, by rfl⟩ : syracuseStep 1990931 = 2986397) B2986397
theorem B4479605 : Blo 1989435 4479605 := bbase (se 5 (by rfl) ⟨209981, by rfl⟩ : syracuseStep 4479605 = 419963) (by norm_num)
theorem B2986403 : Blo 1989435 2986403 := bstep (se 1 (by rfl) ⟨2239802, by rfl⟩ : syracuseStep 2986403 = 4479605) B4479605
theorem B1990935 : Blo 1989435 1990935 := bstep (se 1 (by rfl) ⟨1493201, by rfl⟩ : syracuseStep 1990935 = 2986403) B2986403
theorem B3232613 : Blo 1989435 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B2155075 : Blo 1989435 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B11493733 : Blo 1989435 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B15324977 : Blo 1989435 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B10216651 : Blo 1989435 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B13622201 : Blo 1989435 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B9081467 : Blo 1989435 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B6054311 : Blo 1989435 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B16144829 : Blo 1989435 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B10763219 : Blo 1989435 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B7175479 : Blo 1989435 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B9567305 : Blo 1989435 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B6378203 : Blo 1989435 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B17008541 : Blo 1989435 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B11339027 : Blo 1989435 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B7559351 : Blo 1989435 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B5039567 : Blo 1989435 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B3359711 : Blo 1989435 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B2239807 : Blo 1989435 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B2986409 : Blo 1989435 2986409 := bstep (se 2 (by rfl) ⟨1119903, by rfl⟩ : syracuseStep 2986409 = 2239807) B2239807
theorem B1990939 : Blo 1989435 1990939 := bstep (se 1 (by rfl) ⟨1493204, by rfl⟩ : syracuseStep 1990939 = 2986409) B2986409
theorem B7559365 : Blo 1989435 7559365 := bbase (se 4 (by rfl) ⟨708690, by rfl⟩ : syracuseStep 7559365 = 1417381) (by norm_num)
theorem B10079153 : Blo 1989435 10079153 := bstep (se 2 (by rfl) ⟨3779682, by rfl⟩ : syracuseStep 10079153 = 7559365) B7559365
theorem B6719435 : Blo 1989435 6719435 := bstep (se 1 (by rfl) ⟨5039576, by rfl⟩ : syracuseStep 6719435 = 10079153) B10079153
theorem B4479623 : Blo 1989435 4479623 := bstep (se 1 (by rfl) ⟨3359717, by rfl⟩ : syracuseStep 4479623 = 6719435) B6719435
theorem B2986415 : Blo 1989435 2986415 := bstep (se 1 (by rfl) ⟨2239811, by rfl⟩ : syracuseStep 2986415 = 4479623) B4479623
theorem B1990943 : Blo 1989435 1990943 := bstep (se 1 (by rfl) ⟨1493207, by rfl⟩ : syracuseStep 1990943 = 2986415) B2986415
theorem B2986421 : Blo 1989435 2986421 := bbase (se 5 (by rfl) ⟨139988, by rfl⟩ : syracuseStep 2986421 = 279977) (by norm_num)
theorem B1990947 : Blo 1989435 1990947 := bstep (se 1 (by rfl) ⟨1493210, by rfl⟩ : syracuseStep 1990947 = 2986421) B2986421
theorem B5039597 : Blo 1989435 5039597 := bbase (se 3 (by rfl) ⟨944924, by rfl⟩ : syracuseStep 5039597 = 1889849) (by norm_num)
theorem B3359731 : Blo 1989435 3359731 := bstep (se 1 (by rfl) ⟨2519798, by rfl⟩ : syracuseStep 3359731 = 5039597) B5039597
theorem B4479641 : Blo 1989435 4479641 := bstep (se 2 (by rfl) ⟨1679865, by rfl⟩ : syracuseStep 4479641 = 3359731) B3359731
theorem B2986427 : Blo 1989435 2986427 := bstep (se 1 (by rfl) ⟨2239820, by rfl⟩ : syracuseStep 2986427 = 4479641) B4479641
theorem B1990951 : Blo 1989435 1990951 := bstep (se 1 (by rfl) ⟨1493213, by rfl⟩ : syracuseStep 1990951 = 2986427) B2986427
theorem B2239825 : Blo 1989435 2239825 := bbase (se 2 (by rfl) ⟨839934, by rfl⟩ : syracuseStep 2239825 = 1679869) (by norm_num)
theorem B2986433 : Blo 1989435 2986433 := bstep (se 2 (by rfl) ⟨1119912, by rfl⟩ : syracuseStep 2986433 = 2239825) B2239825
theorem B1990955 : Blo 1989435 1990955 := bstep (se 1 (by rfl) ⟨1493216, by rfl⟩ : syracuseStep 1990955 = 2986433) B2986433
theorem B2126089 : Blo 1989435 2126089 := bbase (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) (by norm_num)
theorem B2834785 : Blo 1989435 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B3779713 : Blo 1989435 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B5039617 : Blo 1989435 5039617 := bstep (se 2 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 5039617 = 3779713) B3779713
theorem B6719489 : Blo 1989435 6719489 := bstep (se 2 (by rfl) ⟨2519808, by rfl⟩ : syracuseStep 6719489 = 5039617) B5039617
theorem B4479659 : Blo 1989435 4479659 := bstep (se 1 (by rfl) ⟨3359744, by rfl⟩ : syracuseStep 4479659 = 6719489) B6719489
theorem B2986439 : Blo 1989435 2986439 := bstep (se 1 (by rfl) ⟨2239829, by rfl⟩ : syracuseStep 2986439 = 4479659) B4479659
theorem B1990959 : Blo 1989435 1990959 := bstep (se 1 (by rfl) ⟨1493219, by rfl⟩ : syracuseStep 1990959 = 2986439) B2986439
theorem B2986445 : Blo 1989435 2986445 := bbase (se 3 (by rfl) ⟨559958, by rfl⟩ : syracuseStep 2986445 = 1119917) (by norm_num)
theorem B1990963 : Blo 1989435 1990963 := bstep (se 1 (by rfl) ⟨1493222, by rfl⟩ : syracuseStep 1990963 = 2986445) B2986445
theorem B4479677 : Blo 1989435 4479677 := bbase (se 3 (by rfl) ⟨839939, by rfl⟩ : syracuseStep 4479677 = 1679879) (by norm_num)
theorem B2986451 : Blo 1989435 2986451 := bstep (se 1 (by rfl) ⟨2239838, by rfl⟩ : syracuseStep 2986451 = 4479677) B4479677
theorem B1990967 : Blo 1989435 1990967 := bstep (se 1 (by rfl) ⟨1493225, by rfl⟩ : syracuseStep 1990967 = 2986451) B2986451
theorem B3359765 : Blo 1989435 3359765 := bbase (se 6 (by rfl) ⟨78744, by rfl⟩ : syracuseStep 3359765 = 157489) (by norm_num)
theorem B2239843 : Blo 1989435 2239843 := bstep (se 1 (by rfl) ⟨1679882, by rfl⟩ : syracuseStep 2239843 = 3359765) B3359765
theorem B2986457 : Blo 1989435 2986457 := bstep (se 2 (by rfl) ⟨1119921, by rfl⟩ : syracuseStep 2986457 = 2239843) B2239843
theorem B1990971 : Blo 1989435 1990971 := bstep (se 1 (by rfl) ⟨1493228, by rfl⟩ : syracuseStep 1990971 = 2986457) B2986457
theorem B8620453 : Blo 1989435 8620453 := bbase (se 4 (by rfl) ⟨808167, by rfl⟩ : syracuseStep 8620453 = 1616335) (by norm_num)
theorem B11493937 : Blo 1989435 11493937 := bstep (se 2 (by rfl) ⟨4310226, by rfl⟩ : syracuseStep 11493937 = 8620453) B8620453
theorem B15325249 : Blo 1989435 15325249 := bstep (se 2 (by rfl) ⟨5746968, by rfl⟩ : syracuseStep 15325249 = 11493937) B11493937
theorem B20433665 : Blo 1989435 20433665 := bstep (se 2 (by rfl) ⟨7662624, by rfl⟩ : syracuseStep 20433665 = 15325249) B15325249
theorem B54489773 : Blo 1989435 54489773 := bstep (se 3 (by rfl) ⟨10216832, by rfl⟩ : syracuseStep 54489773 = 20433665) B20433665
theorem B36326515 : Blo 1989435 36326515 := bstep (se 1 (by rfl) ⟨27244886, by rfl⟩ : syracuseStep 36326515 = 54489773) B54489773
theorem B48435353 : Blo 1989435 48435353 := bstep (se 2 (by rfl) ⟨18163257, by rfl⟩ : syracuseStep 48435353 = 36326515) B36326515
theorem B32290235 : Blo 1989435 32290235 := bstep (se 1 (by rfl) ⟨24217676, by rfl⟩ : syracuseStep 32290235 = 48435353) B48435353
theorem B21526823 : Blo 1989435 21526823 := bstep (se 1 (by rfl) ⟨16145117, by rfl⟩ : syracuseStep 21526823 = 32290235) B32290235
theorem B14351215 : Blo 1989435 14351215 := bstep (se 1 (by rfl) ⟨10763411, by rfl⟩ : syracuseStep 14351215 = 21526823) B21526823
theorem B19134953 : Blo 1989435 19134953 := bstep (se 2 (by rfl) ⟨7175607, by rfl⟩ : syracuseStep 19134953 = 14351215) B14351215
theorem B12756635 : Blo 1989435 12756635 := bstep (se 1 (by rfl) ⟨9567476, by rfl⟩ : syracuseStep 12756635 = 19134953) B19134953
theorem B8504423 : Blo 1989435 8504423 := bstep (se 1 (by rfl) ⟨6378317, by rfl⟩ : syracuseStep 8504423 = 12756635) B12756635
theorem B5669615 : Blo 1989435 5669615 := bstep (se 1 (by rfl) ⟨4252211, by rfl⟩ : syracuseStep 5669615 = 8504423) B8504423
theorem B15118973 : Blo 1989435 15118973 := bstep (se 3 (by rfl) ⟨2834807, by rfl⟩ : syracuseStep 15118973 = 5669615) B5669615
theorem B10079315 : Blo 1989435 10079315 := bstep (se 1 (by rfl) ⟨7559486, by rfl⟩ : syracuseStep 10079315 = 15118973) B15118973
theorem B6719543 : Blo 1989435 6719543 := bstep (se 1 (by rfl) ⟨5039657, by rfl⟩ : syracuseStep 6719543 = 10079315) B10079315
theorem B4479695 : Blo 1989435 4479695 := bstep (se 1 (by rfl) ⟨3359771, by rfl⟩ : syracuseStep 4479695 = 6719543) B6719543
theorem B2986463 : Blo 1989435 2986463 := bstep (se 1 (by rfl) ⟨2239847, by rfl⟩ : syracuseStep 2986463 = 4479695) B4479695
theorem B1990975 : Blo 1989435 1990975 := bstep (se 1 (by rfl) ⟨1493231, by rfl⟩ : syracuseStep 1990975 = 2986463) B2986463
theorem B2986469 : Blo 1989435 2986469 := bbase (se 4 (by rfl) ⟨279981, by rfl⟩ : syracuseStep 2986469 = 559963) (by norm_num)
theorem B1990979 : Blo 1989435 1990979 := bstep (se 1 (by rfl) ⟨1493234, by rfl⟩ : syracuseStep 1990979 = 2986469) B2986469
theorem B6811253 : Blo 1989435 6811253 := bbase (se 5 (by rfl) ⟨319277, by rfl⟩ : syracuseStep 6811253 = 638555) (by norm_num)
theorem B4540835 : Blo 1989435 4540835 := bstep (se 1 (by rfl) ⟨3405626, by rfl⟩ : syracuseStep 4540835 = 6811253) B6811253
theorem B3027223 : Blo 1989435 3027223 := bstep (se 1 (by rfl) ⟨2270417, by rfl⟩ : syracuseStep 3027223 = 4540835) B4540835
theorem B4036297 : Blo 1989435 4036297 := bstep (se 2 (by rfl) ⟨1513611, by rfl⟩ : syracuseStep 4036297 = 3027223) B3027223
theorem B5381729 : Blo 1989435 5381729 := bstep (se 2 (by rfl) ⟨2018148, by rfl⟩ : syracuseStep 5381729 = 4036297) B4036297
theorem B3587819 : Blo 1989435 3587819 := bstep (se 1 (by rfl) ⟨2690864, by rfl⟩ : syracuseStep 3587819 = 5381729) B5381729
theorem B9567517 : Blo 1989435 9567517 := bstep (se 3 (by rfl) ⟨1793909, by rfl⟩ : syracuseStep 9567517 = 3587819) B3587819
theorem B12756689 : Blo 1989435 12756689 := bstep (se 2 (by rfl) ⟨4783758, by rfl⟩ : syracuseStep 12756689 = 9567517) B9567517
theorem B8504459 : Blo 1989435 8504459 := bstep (se 1 (by rfl) ⟨6378344, by rfl⟩ : syracuseStep 8504459 = 12756689) B12756689
theorem B5669639 : Blo 1989435 5669639 := bstep (se 1 (by rfl) ⟨4252229, by rfl⟩ : syracuseStep 5669639 = 8504459) B8504459
theorem B3779759 : Blo 1989435 3779759 := bstep (se 1 (by rfl) ⟨2834819, by rfl⟩ : syracuseStep 3779759 = 5669639) B5669639
theorem B2519839 : Blo 1989435 2519839 := bstep (se 1 (by rfl) ⟨1889879, by rfl⟩ : syracuseStep 2519839 = 3779759) B3779759
theorem B3359785 : Blo 1989435 3359785 := bstep (se 2 (by rfl) ⟨1259919, by rfl⟩ : syracuseStep 3359785 = 2519839) B2519839
theorem B4479713 : Blo 1989435 4479713 := bstep (se 2 (by rfl) ⟨1679892, by rfl⟩ : syracuseStep 4479713 = 3359785) B3359785
theorem B2986475 : Blo 1989435 2986475 := bstep (se 1 (by rfl) ⟨2239856, by rfl⟩ : syracuseStep 2986475 = 4479713) B4479713
theorem B1990983 : Blo 1989435 1990983 := bstep (se 1 (by rfl) ⟨1493237, by rfl⟩ : syracuseStep 1990983 = 2986475) B2986475
theorem B2239861 : Blo 1989435 2239861 := bbase (se 5 (by rfl) ⟨104993, by rfl⟩ : syracuseStep 2239861 = 209987) (by norm_num)
theorem B2986481 : Blo 1989435 2986481 := bstep (se 2 (by rfl) ⟨1119930, by rfl⟩ : syracuseStep 2986481 = 2239861) B2239861
theorem B1990987 : Blo 1989435 1990987 := bstep (se 1 (by rfl) ⟨1493240, by rfl⟩ : syracuseStep 1990987 = 2986481) B2986481
theorem B2519849 : Blo 1989435 2519849 := bbase (se 2 (by rfl) ⟨944943, by rfl⟩ : syracuseStep 2519849 = 1889887) (by norm_num)
theorem B6719597 : Blo 1989435 6719597 := bstep (se 3 (by rfl) ⟨1259924, by rfl⟩ : syracuseStep 6719597 = 2519849) B2519849
theorem B4479731 : Blo 1989435 4479731 := bstep (se 1 (by rfl) ⟨3359798, by rfl⟩ : syracuseStep 4479731 = 6719597) B6719597
theorem B2986487 : Blo 1989435 2986487 := bstep (se 1 (by rfl) ⟨2239865, by rfl⟩ : syracuseStep 2986487 = 4479731) B4479731
theorem B1990991 : Blo 1989435 1990991 := bstep (se 1 (by rfl) ⟨1493243, by rfl⟩ : syracuseStep 1990991 = 2986487) B2986487
theorem B2986493 : Blo 1989435 2986493 := bbase (se 3 (by rfl) ⟨559967, by rfl⟩ : syracuseStep 2986493 = 1119935) (by norm_num)
theorem B1990995 : Blo 1989435 1990995 := bstep (se 1 (by rfl) ⟨1493246, by rfl⟩ : syracuseStep 1990995 = 2986493) B2986493
theorem B4479749 : Blo 1989435 4479749 := bbase (se 4 (by rfl) ⟨419976, by rfl⟩ : syracuseStep 4479749 = 839953) (by norm_num)
theorem B2986499 : Blo 1989435 2986499 := bstep (se 1 (by rfl) ⟨2239874, by rfl⟩ : syracuseStep 2986499 = 4479749) B4479749
theorem B1990999 : Blo 1989435 1990999 := bstep (se 1 (by rfl) ⟨1493249, by rfl⟩ : syracuseStep 1990999 = 2986499) B2986499
theorem B3779797 : Blo 1989435 3779797 := bbase (se 7 (by rfl) ⟨44294, by rfl⟩ : syracuseStep 3779797 = 88589) (by norm_num)
theorem B5039729 : Blo 1989435 5039729 := bstep (se 2 (by rfl) ⟨1889898, by rfl⟩ : syracuseStep 5039729 = 3779797) B3779797
theorem B3359819 : Blo 1989435 3359819 := bstep (se 1 (by rfl) ⟨2519864, by rfl⟩ : syracuseStep 3359819 = 5039729) B5039729
theorem B2239879 : Blo 1989435 2239879 := bstep (se 1 (by rfl) ⟨1679909, by rfl⟩ : syracuseStep 2239879 = 3359819) B3359819
theorem B2986505 : Blo 1989435 2986505 := bstep (se 2 (by rfl) ⟨1119939, by rfl⟩ : syracuseStep 2986505 = 2239879) B2239879
theorem B1991003 : Blo 1989435 1991003 := bstep (se 1 (by rfl) ⟨1493252, by rfl⟩ : syracuseStep 1991003 = 2986505) B2986505
theorem B10079477 : Blo 1989435 10079477 := bbase (se 5 (by rfl) ⟨472475, by rfl⟩ : syracuseStep 10079477 = 944951) (by norm_num)
theorem B6719651 : Blo 1989435 6719651 := bstep (se 1 (by rfl) ⟨5039738, by rfl⟩ : syracuseStep 6719651 = 10079477) B10079477
theorem B4479767 : Blo 1989435 4479767 := bstep (se 1 (by rfl) ⟨3359825, by rfl⟩ : syracuseStep 4479767 = 6719651) B6719651
theorem B2986511 : Blo 1989435 2986511 := bstep (se 1 (by rfl) ⟨2239883, by rfl⟩ : syracuseStep 2986511 = 4479767) B4479767
theorem B1991007 : Blo 1989435 1991007 := bstep (se 1 (by rfl) ⟨1493255, by rfl⟩ : syracuseStep 1991007 = 2986511) B2986511
theorem B2986517 : Blo 1989435 2986517 := bbase (se 6 (by rfl) ⟨69996, by rfl⟩ : syracuseStep 2986517 = 139993) (by norm_num)
theorem B1991011 : Blo 1989435 1991011 := bstep (se 1 (by rfl) ⟨1493258, by rfl⟩ : syracuseStep 1991011 = 2986517) B2986517
theorem B3636829 : Blo 1989435 3636829 := bbase (se 3 (by rfl) ⟨681905, by rfl⟩ : syracuseStep 3636829 = 1363811) (by norm_num)
theorem B19396421 : Blo 1989435 19396421 := bstep (se 4 (by rfl) ⟨1818414, by rfl⟩ : syracuseStep 19396421 = 3636829) B3636829
theorem B12930947 : Blo 1989435 12930947 := bstep (se 1 (by rfl) ⟨9698210, by rfl⟩ : syracuseStep 12930947 = 19396421) B19396421
theorem B8620631 : Blo 1989435 8620631 := bstep (se 1 (by rfl) ⟨6465473, by rfl⟩ : syracuseStep 8620631 = 12930947) B12930947
theorem B5747087 : Blo 1989435 5747087 := bstep (se 1 (by rfl) ⟨4310315, by rfl⟩ : syracuseStep 5747087 = 8620631) B8620631
theorem B3831391 : Blo 1989435 3831391 := bstep (se 1 (by rfl) ⟨2873543, by rfl⟩ : syracuseStep 3831391 = 5747087) B5747087
theorem B5108521 : Blo 1989435 5108521 := bstep (se 2 (by rfl) ⟨1915695, by rfl⟩ : syracuseStep 5108521 = 3831391) B3831391
theorem B6811361 : Blo 1989435 6811361 := bstep (se 2 (by rfl) ⟨2554260, by rfl⟩ : syracuseStep 6811361 = 5108521) B5108521
theorem B4540907 : Blo 1989435 4540907 := bstep (se 1 (by rfl) ⟨3405680, by rfl⟩ : syracuseStep 4540907 = 6811361) B6811361
theorem B12109085 : Blo 1989435 12109085 := bstep (se 3 (by rfl) ⟨2270453, by rfl⟩ : syracuseStep 12109085 = 4540907) B4540907
theorem B8072723 : Blo 1989435 8072723 := bstep (se 1 (by rfl) ⟨6054542, by rfl⟩ : syracuseStep 8072723 = 12109085) B12109085
theorem B5381815 : Blo 1989435 5381815 := bstep (se 1 (by rfl) ⟨4036361, by rfl⟩ : syracuseStep 5381815 = 8072723) B8072723
theorem B7175753 : Blo 1989435 7175753 := bstep (se 2 (by rfl) ⟨2690907, by rfl⟩ : syracuseStep 7175753 = 5381815) B5381815
theorem B4783835 : Blo 1989435 4783835 := bstep (se 1 (by rfl) ⟨3587876, by rfl⟩ : syracuseStep 4783835 = 7175753) B7175753
theorem B3189223 : Blo 1989435 3189223 := bstep (se 1 (by rfl) ⟨2391917, by rfl⟩ : syracuseStep 3189223 = 4783835) B4783835
theorem B17009189 : Blo 1989435 17009189 := bstep (se 4 (by rfl) ⟨1594611, by rfl⟩ : syracuseStep 17009189 = 3189223) B3189223
theorem B11339459 : Blo 1989435 11339459 := bstep (se 1 (by rfl) ⟨8504594, by rfl⟩ : syracuseStep 11339459 = 17009189) B17009189
theorem B7559639 : Blo 1989435 7559639 := bstep (se 1 (by rfl) ⟨5669729, by rfl⟩ : syracuseStep 7559639 = 11339459) B11339459
theorem B5039759 : Blo 1989435 5039759 := bstep (se 1 (by rfl) ⟨3779819, by rfl⟩ : syracuseStep 5039759 = 7559639) B7559639
theorem B3359839 : Blo 1989435 3359839 := bstep (se 1 (by rfl) ⟨2519879, by rfl⟩ : syracuseStep 3359839 = 5039759) B5039759
theorem B4479785 : Blo 1989435 4479785 := bstep (se 2 (by rfl) ⟨1679919, by rfl⟩ : syracuseStep 4479785 = 3359839) B3359839
theorem B2986523 : Blo 1989435 2986523 := bstep (se 1 (by rfl) ⟨2239892, by rfl⟩ : syracuseStep 2986523 = 4479785) B4479785
theorem B1991015 : Blo 1989435 1991015 := bstep (se 1 (by rfl) ⟨1493261, by rfl⟩ : syracuseStep 1991015 = 2986523) B2986523
theorem B2239897 : Blo 1989435 2239897 := bbase (se 2 (by rfl) ⟨839961, by rfl⟩ : syracuseStep 2239897 = 1679923) (by norm_num)
theorem B2986529 : Blo 1989435 2986529 := bstep (se 2 (by rfl) ⟨1119948, by rfl⟩ : syracuseStep 2986529 = 2239897) B2239897
theorem B1991019 : Blo 1989435 1991019 := bstep (se 1 (by rfl) ⟨1493264, by rfl⟩ : syracuseStep 1991019 = 2986529) B2986529
theorem B7559669 : Blo 1989435 7559669 := bbase (se 5 (by rfl) ⟨354359, by rfl⟩ : syracuseStep 7559669 = 708719) (by norm_num)
theorem B5039779 : Blo 1989435 5039779 := bstep (se 1 (by rfl) ⟨3779834, by rfl⟩ : syracuseStep 5039779 = 7559669) B7559669
theorem B6719705 : Blo 1989435 6719705 := bstep (se 2 (by rfl) ⟨2519889, by rfl⟩ : syracuseStep 6719705 = 5039779) B5039779
theorem B4479803 : Blo 1989435 4479803 := bstep (se 1 (by rfl) ⟨3359852, by rfl⟩ : syracuseStep 4479803 = 6719705) B6719705
theorem B2986535 : Blo 1989435 2986535 := bstep (se 1 (by rfl) ⟨2239901, by rfl⟩ : syracuseStep 2986535 = 4479803) B4479803
theorem B1991023 : Blo 1989435 1991023 := bstep (se 1 (by rfl) ⟨1493267, by rfl⟩ : syracuseStep 1991023 = 2986535) B2986535
theorem B2986541 : Blo 1989435 2986541 := bbase (se 3 (by rfl) ⟨559976, by rfl⟩ : syracuseStep 2986541 = 1119953) (by norm_num)
theorem B1991027 : Blo 1989435 1991027 := bstep (se 1 (by rfl) ⟨1493270, by rfl⟩ : syracuseStep 1991027 = 2986541) B2986541
theorem B4479821 : Blo 1989435 4479821 := bbase (se 3 (by rfl) ⟨839966, by rfl⟩ : syracuseStep 4479821 = 1679933) (by norm_num)
theorem B2986547 : Blo 1989435 2986547 := bstep (se 1 (by rfl) ⟨2239910, by rfl⟩ : syracuseStep 2986547 = 4479821) B4479821
theorem B1991031 : Blo 1989435 1991031 := bstep (se 1 (by rfl) ⟨1493273, by rfl⟩ : syracuseStep 1991031 = 2986547) B2986547
theorem B2519905 : Blo 1989435 2519905 := bbase (se 2 (by rfl) ⟨944964, by rfl⟩ : syracuseStep 2519905 = 1889929) (by norm_num)
theorem B3359873 : Blo 1989435 3359873 := bstep (se 2 (by rfl) ⟨1259952, by rfl⟩ : syracuseStep 3359873 = 2519905) B2519905
theorem B2239915 : Blo 1989435 2239915 := bstep (se 1 (by rfl) ⟨1679936, by rfl⟩ : syracuseStep 2239915 = 3359873) B3359873
theorem B2986553 : Blo 1989435 2986553 := bstep (se 2 (by rfl) ⟨1119957, by rfl⟩ : syracuseStep 2986553 = 2239915) B2239915
theorem B1991035 : Blo 1989435 1991035 := bstep (se 1 (by rfl) ⟨1493276, by rfl⟩ : syracuseStep 1991035 = 2986553) B2986553
theorem B22679189 : Blo 1989435 22679189 := bbase (se 6 (by rfl) ⟨531543, by rfl⟩ : syracuseStep 22679189 = 1063087) (by norm_num)
theorem B15119459 : Blo 1989435 15119459 := bstep (se 1 (by rfl) ⟨11339594, by rfl⟩ : syracuseStep 15119459 = 22679189) B22679189
theorem B10079639 : Blo 1989435 10079639 := bstep (se 1 (by rfl) ⟨7559729, by rfl⟩ : syracuseStep 10079639 = 15119459) B15119459
theorem B6719759 : Blo 1989435 6719759 := bstep (se 1 (by rfl) ⟨5039819, by rfl⟩ : syracuseStep 6719759 = 10079639) B10079639
theorem B4479839 : Blo 1989435 4479839 := bstep (se 1 (by rfl) ⟨3359879, by rfl⟩ : syracuseStep 4479839 = 6719759) B6719759
theorem B2986559 : Blo 1989435 2986559 := bstep (se 1 (by rfl) ⟨2239919, by rfl⟩ : syracuseStep 2986559 = 4479839) B4479839
theorem B1991039 : Blo 1989435 1991039 := bstep (se 1 (by rfl) ⟨1493279, by rfl⟩ : syracuseStep 1991039 = 2986559) B2986559
theorem B2986565 : Blo 1989435 2986565 := bbase (se 4 (by rfl) ⟨279990, by rfl⟩ : syracuseStep 2986565 = 559981) (by norm_num)
theorem B1991043 : Blo 1989435 1991043 := bstep (se 1 (by rfl) ⟨1493282, by rfl⟩ : syracuseStep 1991043 = 2986565) B2986565
theorem B3359893 : Blo 1989435 3359893 := bbase (se 6 (by rfl) ⟨78747, by rfl⟩ : syracuseStep 3359893 = 157495) (by norm_num)
theorem B4479857 : Blo 1989435 4479857 := bstep (se 2 (by rfl) ⟨1679946, by rfl⟩ : syracuseStep 4479857 = 3359893) B3359893
theorem B2986571 : Blo 1989435 2986571 := bstep (se 1 (by rfl) ⟨2239928, by rfl⟩ : syracuseStep 2986571 = 4479857) B4479857
theorem B1991047 : Blo 1989435 1991047 := bstep (se 1 (by rfl) ⟨1493285, by rfl⟩ : syracuseStep 1991047 = 2986571) B2986571
theorem B2239933 : Blo 1989435 2239933 := bbase (se 3 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 2239933 = 839975) (by norm_num)
theorem B2986577 : Blo 1989435 2986577 := bstep (se 2 (by rfl) ⟨1119966, by rfl⟩ : syracuseStep 2986577 = 2239933) B2239933
theorem B1991051 : Blo 1989435 1991051 := bstep (se 1 (by rfl) ⟨1493288, by rfl⟩ : syracuseStep 1991051 = 2986577) B2986577
theorem B6719813 : Blo 1989435 6719813 := bbase (se 4 (by rfl) ⟨629982, by rfl⟩ : syracuseStep 6719813 = 1259965) (by norm_num)
theorem B4479875 : Blo 1989435 4479875 := bstep (se 1 (by rfl) ⟨3359906, by rfl⟩ : syracuseStep 4479875 = 6719813) B6719813
theorem B2986583 : Blo 1989435 2986583 := bstep (se 1 (by rfl) ⟨2239937, by rfl⟩ : syracuseStep 2986583 = 4479875) B4479875
theorem B1991055 : Blo 1989435 1991055 := bstep (se 1 (by rfl) ⟨1493291, by rfl⟩ : syracuseStep 1991055 = 2986583) B2986583
theorem B2986589 : Blo 1989435 2986589 := bbase (se 3 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 2986589 = 1119971) (by norm_num)
theorem B1991059 : Blo 1989435 1991059 := bstep (se 1 (by rfl) ⟨1493294, by rfl⟩ : syracuseStep 1991059 = 2986589) B2986589
theorem B4479893 : Blo 1989435 4479893 := bbase (se 6 (by rfl) ⟨104997, by rfl⟩ : syracuseStep 4479893 = 209995) (by norm_num)
theorem B2986595 : Blo 1989435 2986595 := bstep (se 1 (by rfl) ⟨2239946, by rfl⟩ : syracuseStep 2986595 = 4479893) B4479893
theorem B1991063 : Blo 1989435 1991063 := bstep (se 1 (by rfl) ⟨1493297, by rfl⟩ : syracuseStep 1991063 = 2986595) B2986595
theorem B5381957 : Blo 1989435 5381957 := bbase (se 4 (by rfl) ⟨504558, by rfl⟩ : syracuseStep 5381957 = 1009117) (by norm_num)
theorem B3587971 : Blo 1989435 3587971 := bstep (se 1 (by rfl) ⟨2690978, by rfl⟩ : syracuseStep 3587971 = 5381957) B5381957
theorem B4783961 : Blo 1989435 4783961 := bstep (se 2 (by rfl) ⟨1793985, by rfl⟩ : syracuseStep 4783961 = 3587971) B3587971
theorem B3189307 : Blo 1989435 3189307 := bstep (se 1 (by rfl) ⟨2391980, by rfl⟩ : syracuseStep 3189307 = 4783961) B4783961
theorem B4252409 : Blo 1989435 4252409 := bstep (se 2 (by rfl) ⟨1594653, by rfl⟩ : syracuseStep 4252409 = 3189307) B3189307
theorem B2834939 : Blo 1989435 2834939 := bstep (se 1 (by rfl) ⟨2126204, by rfl⟩ : syracuseStep 2834939 = 4252409) B4252409
theorem B7559837 : Blo 1989435 7559837 := bstep (se 3 (by rfl) ⟨1417469, by rfl⟩ : syracuseStep 7559837 = 2834939) B2834939
theorem B5039891 : Blo 1989435 5039891 := bstep (se 1 (by rfl) ⟨3779918, by rfl⟩ : syracuseStep 5039891 = 7559837) B7559837
theorem B3359927 : Blo 1989435 3359927 := bstep (se 1 (by rfl) ⟨2519945, by rfl⟩ : syracuseStep 3359927 = 5039891) B5039891
theorem B2239951 : Blo 1989435 2239951 := bstep (se 1 (by rfl) ⟨1679963, by rfl⟩ : syracuseStep 2239951 = 3359927) B3359927
theorem B2986601 : Blo 1989435 2986601 := bstep (se 2 (by rfl) ⟨1119975, by rfl⟩ : syracuseStep 2986601 = 2239951) B2239951
theorem B1991067 : Blo 1989435 1991067 := bstep (se 1 (by rfl) ⟨1493300, by rfl⟩ : syracuseStep 1991067 = 2986601) B2986601
theorem B4310437 : Blo 1989435 4310437 := bbase (se 4 (by rfl) ⟨404103, by rfl⟩ : syracuseStep 4310437 = 808207) (by norm_num)
theorem B5747249 : Blo 1989435 5747249 := bstep (se 2 (by rfl) ⟨2155218, by rfl⟩ : syracuseStep 5747249 = 4310437) B4310437
theorem B3831499 : Blo 1989435 3831499 := bstep (se 1 (by rfl) ⟨2873624, by rfl⟩ : syracuseStep 3831499 = 5747249) B5747249
theorem B5108665 : Blo 1989435 5108665 := bstep (se 2 (by rfl) ⟨1915749, by rfl⟩ : syracuseStep 5108665 = 3831499) B3831499
theorem B6811553 : Blo 1989435 6811553 := bstep (se 2 (by rfl) ⟨2554332, by rfl⟩ : syracuseStep 6811553 = 5108665) B5108665
theorem B4541035 : Blo 1989435 4541035 := bstep (se 1 (by rfl) ⟨3405776, by rfl⟩ : syracuseStep 4541035 = 6811553) B6811553
theorem B6054713 : Blo 1989435 6054713 := bstep (se 2 (by rfl) ⟨2270517, by rfl⟩ : syracuseStep 6054713 = 4541035) B4541035
theorem B4036475 : Blo 1989435 4036475 := bstep (se 1 (by rfl) ⟨3027356, by rfl⟩ : syracuseStep 4036475 = 6054713) B6054713
theorem B2690983 : Blo 1989435 2690983 := bstep (se 1 (by rfl) ⟨2018237, by rfl⟩ : syracuseStep 2690983 = 4036475) B4036475
theorem B3587977 : Blo 1989435 3587977 := bstep (se 2 (by rfl) ⟨1345491, by rfl⟩ : syracuseStep 3587977 = 2690983) B2690983
theorem B4783969 : Blo 1989435 4783969 := bstep (se 2 (by rfl) ⟨1793988, by rfl⟩ : syracuseStep 4783969 = 3587977) B3587977
theorem B6378625 : Blo 1989435 6378625 := bstep (se 2 (by rfl) ⟨2391984, by rfl⟩ : syracuseStep 6378625 = 4783969) B4783969
theorem B8504833 : Blo 1989435 8504833 := bstep (se 2 (by rfl) ⟨3189312, by rfl⟩ : syracuseStep 8504833 = 6378625) B6378625
theorem B11339777 : Blo 1989435 11339777 := bstep (se 2 (by rfl) ⟨4252416, by rfl⟩ : syracuseStep 11339777 = 8504833) B8504833
theorem B7559851 : Blo 1989435 7559851 := bstep (se 1 (by rfl) ⟨5669888, by rfl⟩ : syracuseStep 7559851 = 11339777) B11339777
theorem B10079801 : Blo 1989435 10079801 := bstep (se 2 (by rfl) ⟨3779925, by rfl⟩ : syracuseStep 10079801 = 7559851) B7559851
theorem B6719867 : Blo 1989435 6719867 := bstep (se 1 (by rfl) ⟨5039900, by rfl⟩ : syracuseStep 6719867 = 10079801) B10079801
theorem B4479911 : Blo 1989435 4479911 := bstep (se 1 (by rfl) ⟨3359933, by rfl⟩ : syracuseStep 4479911 = 6719867) B6719867
theorem B2986607 : Blo 1989435 2986607 := bstep (se 1 (by rfl) ⟨2239955, by rfl⟩ : syracuseStep 2986607 = 4479911) B4479911
theorem B1991071 : Blo 1989435 1991071 := bstep (se 1 (by rfl) ⟨1493303, by rfl⟩ : syracuseStep 1991071 = 2986607) B2986607
theorem B2986613 : Blo 1989435 2986613 := bbase (se 5 (by rfl) ⟨139997, by rfl⟩ : syracuseStep 2986613 = 279995) (by norm_num)
theorem B1991075 : Blo 1989435 1991075 := bstep (se 1 (by rfl) ⟨1493306, by rfl⟩ : syracuseStep 1991075 = 2986613) B2986613
theorem B3779941 : Blo 1989435 3779941 := bbase (se 4 (by rfl) ⟨354369, by rfl⟩ : syracuseStep 3779941 = 708739) (by norm_num)
theorem B5039921 : Blo 1989435 5039921 := bstep (se 2 (by rfl) ⟨1889970, by rfl⟩ : syracuseStep 5039921 = 3779941) B3779941
theorem B3359947 : Blo 1989435 3359947 := bstep (se 1 (by rfl) ⟨2519960, by rfl⟩ : syracuseStep 3359947 = 5039921) B5039921
theorem B4479929 : Blo 1989435 4479929 := bstep (se 2 (by rfl) ⟨1679973, by rfl⟩ : syracuseStep 4479929 = 3359947) B3359947
theorem B2986619 : Blo 1989435 2986619 := bstep (se 1 (by rfl) ⟨2239964, by rfl⟩ : syracuseStep 2986619 = 4479929) B4479929
theorem B1991079 : Blo 1989435 1991079 := bstep (se 1 (by rfl) ⟨1493309, by rfl⟩ : syracuseStep 1991079 = 2986619) B2986619
theorem B2239969 : Blo 1989435 2239969 := bbase (se 2 (by rfl) ⟨839988, by rfl⟩ : syracuseStep 2239969 = 1679977) (by norm_num)
theorem B2986625 : Blo 1989435 2986625 := bstep (se 2 (by rfl) ⟨1119984, by rfl⟩ : syracuseStep 2986625 = 2239969) B2239969
theorem B1991083 : Blo 1989435 1991083 := bstep (se 1 (by rfl) ⟨1493312, by rfl⟩ : syracuseStep 1991083 = 2986625) B2986625
theorem B5039941 : Blo 1989435 5039941 := bbase (se 4 (by rfl) ⟨472494, by rfl⟩ : syracuseStep 5039941 = 944989) (by norm_num)
theorem B6719921 : Blo 1989435 6719921 := bstep (se 2 (by rfl) ⟨2519970, by rfl⟩ : syracuseStep 6719921 = 5039941) B5039941
theorem B4479947 : Blo 1989435 4479947 := bstep (se 1 (by rfl) ⟨3359960, by rfl⟩ : syracuseStep 4479947 = 6719921) B6719921
theorem B2986631 : Blo 1989435 2986631 := bstep (se 1 (by rfl) ⟨2239973, by rfl⟩ : syracuseStep 2986631 = 4479947) B4479947
theorem B1991087 : Blo 1989435 1991087 := bstep (se 1 (by rfl) ⟨1493315, by rfl⟩ : syracuseStep 1991087 = 2986631) B2986631
theorem B2986637 : Blo 1989435 2986637 := bbase (se 3 (by rfl) ⟨559994, by rfl⟩ : syracuseStep 2986637 = 1119989) (by norm_num)
theorem B1991091 : Blo 1989435 1991091 := bstep (se 1 (by rfl) ⟨1493318, by rfl⟩ : syracuseStep 1991091 = 2986637) B2986637
theorem B4479965 : Blo 1989435 4479965 := bbase (se 3 (by rfl) ⟨839993, by rfl⟩ : syracuseStep 4479965 = 1679987) (by norm_num)
theorem B2986643 : Blo 1989435 2986643 := bstep (se 1 (by rfl) ⟨2239982, by rfl⟩ : syracuseStep 2986643 = 4479965) B4479965
theorem B1991095 : Blo 1989435 1991095 := bstep (se 1 (by rfl) ⟨1493321, by rfl⟩ : syracuseStep 1991095 = 2986643) B2986643
theorem B3359981 : Blo 1989435 3359981 := bbase (se 3 (by rfl) ⟨629996, by rfl⟩ : syracuseStep 3359981 = 1259993) (by norm_num)
theorem B2239987 : Blo 1989435 2239987 := bstep (se 1 (by rfl) ⟨1679990, by rfl⟩ : syracuseStep 2239987 = 3359981) B3359981
theorem B2986649 : Blo 1989435 2986649 := bstep (se 2 (by rfl) ⟨1119993, by rfl⟩ : syracuseStep 2986649 = 2239987) B2239987
theorem B1991099 : Blo 1989435 1991099 := bstep (se 1 (by rfl) ⟨1493324, by rfl⟩ : syracuseStep 1991099 = 2986649) B2986649
theorem B2873669 : Blo 1989435 2873669 := bbase (se 4 (by rfl) ⟨269406, by rfl⟩ : syracuseStep 2873669 = 538813) (by norm_num)
theorem B30652469 : Blo 1989435 30652469 := bstep (se 5 (by rfl) ⟨1436834, by rfl⟩ : syracuseStep 30652469 = 2873669) B2873669
theorem B20434979 : Blo 1989435 20434979 := bstep (se 1 (by rfl) ⟨15326234, by rfl⟩ : syracuseStep 20434979 = 30652469) B30652469
theorem B13623319 : Blo 1989435 13623319 := bstep (se 1 (by rfl) ⟨10217489, by rfl⟩ : syracuseStep 13623319 = 20434979) B20434979
theorem B18164425 : Blo 1989435 18164425 := bstep (se 2 (by rfl) ⟨6811659, by rfl⟩ : syracuseStep 18164425 = 13623319) B13623319
theorem B24219233 : Blo 1989435 24219233 := bstep (se 2 (by rfl) ⟨9082212, by rfl⟩ : syracuseStep 24219233 = 18164425) B18164425
theorem B16146155 : Blo 1989435 16146155 := bstep (se 1 (by rfl) ⟨12109616, by rfl⟩ : syracuseStep 16146155 = 24219233) B24219233
theorem B10764103 : Blo 1989435 10764103 := bstep (se 1 (by rfl) ⟨8073077, by rfl⟩ : syracuseStep 10764103 = 16146155) B16146155
theorem B14352137 : Blo 1989435 14352137 := bstep (se 2 (by rfl) ⟨5382051, by rfl⟩ : syracuseStep 14352137 = 10764103) B10764103
theorem B9568091 : Blo 1989435 9568091 := bstep (se 1 (by rfl) ⟨7176068, by rfl⟩ : syracuseStep 9568091 = 14352137) B14352137
theorem B25514909 : Blo 1989435 25514909 := bstep (se 3 (by rfl) ⟨4784045, by rfl⟩ : syracuseStep 25514909 = 9568091) B9568091
theorem B17009939 : Blo 1989435 17009939 := bstep (se 1 (by rfl) ⟨12757454, by rfl⟩ : syracuseStep 17009939 = 25514909) B25514909
theorem B11339959 : Blo 1989435 11339959 := bstep (se 1 (by rfl) ⟨8504969, by rfl⟩ : syracuseStep 11339959 = 17009939) B17009939
theorem B15119945 : Blo 1989435 15119945 := bstep (se 2 (by rfl) ⟨5669979, by rfl⟩ : syracuseStep 15119945 = 11339959) B11339959
theorem B10079963 : Blo 1989435 10079963 := bstep (se 1 (by rfl) ⟨7559972, by rfl⟩ : syracuseStep 10079963 = 15119945) B15119945
theorem B6719975 : Blo 1989435 6719975 := bstep (se 1 (by rfl) ⟨5039981, by rfl⟩ : syracuseStep 6719975 = 10079963) B10079963
theorem B4479983 : Blo 1989435 4479983 := bstep (se 1 (by rfl) ⟨3359987, by rfl⟩ : syracuseStep 4479983 = 6719975) B6719975
theorem B2986655 : Blo 1989435 2986655 := bstep (se 1 (by rfl) ⟨2239991, by rfl⟩ : syracuseStep 2986655 = 4479983) B4479983
theorem B1991103 : Blo 1989435 1991103 := bstep (se 1 (by rfl) ⟨1493327, by rfl⟩ : syracuseStep 1991103 = 2986655) B2986655
theorem B2986661 : Blo 1989435 2986661 := bbase (se 4 (by rfl) ⟨279999, by rfl⟩ : syracuseStep 2986661 = 559999) (by norm_num)
theorem B1991107 : Blo 1989435 1991107 := bstep (se 1 (by rfl) ⟨1493330, by rfl⟩ : syracuseStep 1991107 = 2986661) B2986661
theorem B2520001 : Blo 1989435 2520001 := bbase (se 2 (by rfl) ⟨945000, by rfl⟩ : syracuseStep 2520001 = 1890001) (by norm_num)
theorem B3360001 : Blo 1989435 3360001 := bstep (se 2 (by rfl) ⟨1260000, by rfl⟩ : syracuseStep 3360001 = 2520001) B2520001
theorem B4480001 : Blo 1989435 4480001 := bstep (se 2 (by rfl) ⟨1680000, by rfl⟩ : syracuseStep 4480001 = 3360001) B3360001
theorem B2986667 : Blo 1989435 2986667 := bstep (se 1 (by rfl) ⟨2240000, by rfl⟩ : syracuseStep 2986667 = 4480001) B4480001
theorem B1991111 : Blo 1989435 1991111 := bstep (se 1 (by rfl) ⟨1493333, by rfl⟩ : syracuseStep 1991111 = 2986667) B2986667
theorem B2240005 : Blo 1989435 2240005 := bbase (se 4 (by rfl) ⟨210000, by rfl⟩ : syracuseStep 2240005 = 420001) (by norm_num)
theorem B2986673 : Blo 1989435 2986673 := bstep (se 2 (by rfl) ⟨1120002, by rfl⟩ : syracuseStep 2986673 = 2240005) B2240005
theorem B1991115 : Blo 1989435 1991115 := bstep (se 1 (by rfl) ⟨1493336, by rfl⟩ : syracuseStep 1991115 = 2986673) B2986673
theorem B2835013 : Blo 1989435 2835013 := bbase (se 4 (by rfl) ⟨265782, by rfl⟩ : syracuseStep 2835013 = 531565) (by norm_num)
theorem B3780017 : Blo 1989435 3780017 := bstep (se 2 (by rfl) ⟨1417506, by rfl⟩ : syracuseStep 3780017 = 2835013) B2835013
theorem B2520011 : Blo 1989435 2520011 := bstep (se 1 (by rfl) ⟨1890008, by rfl⟩ : syracuseStep 2520011 = 3780017) B3780017
theorem B6720029 : Blo 1989435 6720029 := bstep (se 3 (by rfl) ⟨1260005, by rfl⟩ : syracuseStep 6720029 = 2520011) B2520011
theorem B4480019 : Blo 1989435 4480019 := bstep (se 1 (by rfl) ⟨3360014, by rfl⟩ : syracuseStep 4480019 = 6720029) B6720029
theorem B2986679 : Blo 1989435 2986679 := bstep (se 1 (by rfl) ⟨2240009, by rfl⟩ : syracuseStep 2986679 = 4480019) B4480019
theorem B1991119 : Blo 1989435 1991119 := bstep (se 1 (by rfl) ⟨1493339, by rfl⟩ : syracuseStep 1991119 = 2986679) B2986679
theorem B2986685 : Blo 1989435 2986685 := bbase (se 3 (by rfl) ⟨560003, by rfl⟩ : syracuseStep 2986685 = 1120007) (by norm_num)
theorem B1991123 : Blo 1989435 1991123 := bstep (se 1 (by rfl) ⟨1493342, by rfl⟩ : syracuseStep 1991123 = 2986685) B2986685
theorem B4480037 : Blo 1989435 4480037 := bbase (se 4 (by rfl) ⟨420003, by rfl⟩ : syracuseStep 4480037 = 840007) (by norm_num)
theorem B2986691 : Blo 1989435 2986691 := bstep (se 1 (by rfl) ⟨2240018, by rfl⟩ : syracuseStep 2986691 = 4480037) B4480037
theorem B1991127 : Blo 1989435 1991127 := bstep (se 1 (by rfl) ⟨1493345, by rfl⟩ : syracuseStep 1991127 = 2986691) B2986691
theorem B5040053 : Blo 1989435 5040053 := bbase (se 5 (by rfl) ⟨236252, by rfl⟩ : syracuseStep 5040053 = 472505) (by norm_num)
theorem B3360035 : Blo 1989435 3360035 := bstep (se 1 (by rfl) ⟨2520026, by rfl⟩ : syracuseStep 3360035 = 5040053) B5040053
theorem B2240023 : Blo 1989435 2240023 := bstep (se 1 (by rfl) ⟨1680017, by rfl⟩ : syracuseStep 2240023 = 3360035) B3360035
theorem B2986697 : Blo 1989435 2986697 := bstep (se 2 (by rfl) ⟨1120011, by rfl⟩ : syracuseStep 2986697 = 2240023) B2240023
theorem B1991131 : Blo 1989435 1991131 := bstep (se 1 (by rfl) ⟨1493348, by rfl⟩ : syracuseStep 1991131 = 2986697) B2986697
theorem B4849397 : Blo 1989435 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B3232931 : Blo 1989435 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B8621149 : Blo 1989435 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B11494865 : Blo 1989435 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B7663243 : Blo 1989435 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B10217657 : Blo 1989435 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B6811771 : Blo 1989435 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B9082361 : Blo 1989435 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B6054907 : Blo 1989435 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B8073209 : Blo 1989435 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B5382139 : Blo 1989435 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B7176185 : Blo 1989435 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B4784123 : Blo 1989435 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B12757661 : Blo 1989435 12757661 := bstep (se 3 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 12757661 = 4784123) B4784123
theorem B8505107 : Blo 1989435 8505107 := bstep (se 1 (by rfl) ⟨6378830, by rfl⟩ : syracuseStep 8505107 = 12757661) B12757661
theorem B5670071 : Blo 1989435 5670071 := bstep (se 1 (by rfl) ⟨4252553, by rfl⟩ : syracuseStep 5670071 = 8505107) B8505107
theorem B3780047 : Blo 1989435 3780047 := bstep (se 1 (by rfl) ⟨2835035, by rfl⟩ : syracuseStep 3780047 = 5670071) B5670071
theorem B10080125 : Blo 1989435 10080125 := bstep (se 3 (by rfl) ⟨1890023, by rfl⟩ : syracuseStep 10080125 = 3780047) B3780047
theorem B6720083 : Blo 1989435 6720083 := bstep (se 1 (by rfl) ⟨5040062, by rfl⟩ : syracuseStep 6720083 = 10080125) B10080125
theorem B4480055 : Blo 1989435 4480055 := bstep (se 1 (by rfl) ⟨3360041, by rfl⟩ : syracuseStep 4480055 = 6720083) B6720083
theorem B2986703 : Blo 1989435 2986703 := bstep (se 1 (by rfl) ⟨2240027, by rfl⟩ : syracuseStep 2986703 = 4480055) B4480055
theorem B1991135 : Blo 1989435 1991135 := bstep (se 1 (by rfl) ⟨1493351, by rfl⟩ : syracuseStep 1991135 = 2986703) B2986703
theorem B2986709 : Blo 1989435 2986709 := bbase (se 7 (by rfl) ⟨35000, by rfl⟩ : syracuseStep 2986709 = 70001) (by norm_num)
theorem B1991139 : Blo 1989435 1991139 := bstep (se 1 (by rfl) ⟨1493354, by rfl⟩ : syracuseStep 1991139 = 2986709) B2986709
theorem B16146485 : Blo 1989435 16146485 := bbase (se 5 (by rfl) ⟨756866, by rfl⟩ : syracuseStep 16146485 = 1513733) (by norm_num)
theorem B10764323 : Blo 1989435 10764323 := bstep (se 1 (by rfl) ⟨8073242, by rfl⟩ : syracuseStep 10764323 = 16146485) B16146485
theorem B7176215 : Blo 1989435 7176215 := bstep (se 1 (by rfl) ⟨5382161, by rfl⟩ : syracuseStep 7176215 = 10764323) B10764323
theorem B4784143 : Blo 1989435 4784143 := bstep (se 1 (by rfl) ⟨3588107, by rfl⟩ : syracuseStep 4784143 = 7176215) B7176215
theorem B6378857 : Blo 1989435 6378857 := bstep (se 2 (by rfl) ⟨2392071, by rfl⟩ : syracuseStep 6378857 = 4784143) B4784143
theorem B4252571 : Blo 1989435 4252571 := bstep (se 1 (by rfl) ⟨3189428, by rfl⟩ : syracuseStep 4252571 = 6378857) B6378857
theorem B2835047 : Blo 1989435 2835047 := bstep (se 1 (by rfl) ⟨2126285, by rfl⟩ : syracuseStep 2835047 = 4252571) B4252571
theorem B7560125 : Blo 1989435 7560125 := bstep (se 3 (by rfl) ⟨1417523, by rfl⟩ : syracuseStep 7560125 = 2835047) B2835047
theorem B5040083 : Blo 1989435 5040083 := bstep (se 1 (by rfl) ⟨3780062, by rfl⟩ : syracuseStep 5040083 = 7560125) B7560125
theorem B3360055 : Blo 1989435 3360055 := bstep (se 1 (by rfl) ⟨2520041, by rfl⟩ : syracuseStep 3360055 = 5040083) B5040083
theorem B4480073 : Blo 1989435 4480073 := bstep (se 2 (by rfl) ⟨1680027, by rfl⟩ : syracuseStep 4480073 = 3360055) B3360055
theorem B2986715 : Blo 1989435 2986715 := bstep (se 1 (by rfl) ⟨2240036, by rfl⟩ : syracuseStep 2986715 = 4480073) B4480073
theorem B1991143 : Blo 1989435 1991143 := bstep (se 1 (by rfl) ⟨1493357, by rfl⟩ : syracuseStep 1991143 = 2986715) B2986715
theorem B2240041 : Blo 1989435 2240041 := bbase (se 2 (by rfl) ⟨840015, by rfl⟩ : syracuseStep 2240041 = 1680031) (by norm_num)
theorem B2986721 : Blo 1989435 2986721 := bstep (se 2 (by rfl) ⟨1120020, by rfl⟩ : syracuseStep 2986721 = 2240041) B2240041
theorem B1991147 : Blo 1989435 1991147 := bstep (se 1 (by rfl) ⟨1493360, by rfl⟩ : syracuseStep 1991147 = 2986721) B2986721
theorem B4036637 : Blo 1989435 4036637 := bbase (se 3 (by rfl) ⟨756869, by rfl⟩ : syracuseStep 4036637 = 1513739) (by norm_num)
theorem B2691091 : Blo 1989435 2691091 := bstep (se 1 (by rfl) ⟨2018318, by rfl⟩ : syracuseStep 2691091 = 4036637) B4036637
theorem B3588121 : Blo 1989435 3588121 := bstep (se 2 (by rfl) ⟨1345545, by rfl⟩ : syracuseStep 3588121 = 2691091) B2691091
theorem B19136645 : Blo 1989435 19136645 := bstep (se 4 (by rfl) ⟨1794060, by rfl⟩ : syracuseStep 19136645 = 3588121) B3588121
theorem B12757763 : Blo 1989435 12757763 := bstep (se 1 (by rfl) ⟨9568322, by rfl⟩ : syracuseStep 12757763 = 19136645) B19136645
theorem B8505175 : Blo 1989435 8505175 := bstep (se 1 (by rfl) ⟨6378881, by rfl⟩ : syracuseStep 8505175 = 12757763) B12757763
theorem B11340233 : Blo 1989435 11340233 := bstep (se 2 (by rfl) ⟨4252587, by rfl⟩ : syracuseStep 11340233 = 8505175) B8505175
theorem B7560155 : Blo 1989435 7560155 := bstep (se 1 (by rfl) ⟨5670116, by rfl⟩ : syracuseStep 7560155 = 11340233) B11340233
theorem B5040103 : Blo 1989435 5040103 := bstep (se 1 (by rfl) ⟨3780077, by rfl⟩ : syracuseStep 5040103 = 7560155) B7560155
theorem B6720137 : Blo 1989435 6720137 := bstep (se 2 (by rfl) ⟨2520051, by rfl⟩ : syracuseStep 6720137 = 5040103) B5040103
theorem B4480091 : Blo 1989435 4480091 := bstep (se 1 (by rfl) ⟨3360068, by rfl⟩ : syracuseStep 4480091 = 6720137) B6720137
theorem B2986727 : Blo 1989435 2986727 := bstep (se 1 (by rfl) ⟨2240045, by rfl⟩ : syracuseStep 2986727 = 4480091) B4480091
theorem B1991151 : Blo 1989435 1991151 := bstep (se 1 (by rfl) ⟨1493363, by rfl⟩ : syracuseStep 1991151 = 2986727) B2986727
theorem B2986733 : Blo 1989435 2986733 := bbase (se 3 (by rfl) ⟨560012, by rfl⟩ : syracuseStep 2986733 = 1120025) (by norm_num)
theorem B1991155 : Blo 1989435 1991155 := bstep (se 1 (by rfl) ⟨1493366, by rfl⟩ : syracuseStep 1991155 = 2986733) B2986733
theorem B4480109 : Blo 1989435 4480109 := bbase (se 3 (by rfl) ⟨840020, by rfl⟩ : syracuseStep 4480109 = 1680041) (by norm_num)
theorem B2986739 : Blo 1989435 2986739 := bstep (se 1 (by rfl) ⟨2240054, by rfl⟩ : syracuseStep 2986739 = 4480109) B4480109
theorem B1991159 : Blo 1989435 1991159 := bstep (se 1 (by rfl) ⟨1493369, by rfl⟩ : syracuseStep 1991159 = 2986739) B2986739
theorem B3780101 : Blo 1989435 3780101 := bbase (se 4 (by rfl) ⟨354384, by rfl⟩ : syracuseStep 3780101 = 708769) (by norm_num)
theorem B2520067 : Blo 1989435 2520067 := bstep (se 1 (by rfl) ⟨1890050, by rfl⟩ : syracuseStep 2520067 = 3780101) B3780101
theorem B3360089 : Blo 1989435 3360089 := bstep (se 2 (by rfl) ⟨1260033, by rfl⟩ : syracuseStep 3360089 = 2520067) B2520067
theorem B2240059 : Blo 1989435 2240059 := bstep (se 1 (by rfl) ⟨1680044, by rfl⟩ : syracuseStep 2240059 = 3360089) B3360089
theorem B2986745 : Blo 1989435 2986745 := bstep (se 2 (by rfl) ⟨1120029, by rfl⟩ : syracuseStep 2986745 = 2240059) B2240059
theorem B1991163 : Blo 1989435 1991163 := bstep (se 1 (by rfl) ⟨1493372, by rfl⟩ : syracuseStep 1991163 = 2986745) B2986745
theorem B2155321 : Blo 1989435 2155321 := bbase (se 2 (by rfl) ⟨808245, by rfl⟩ : syracuseStep 2155321 = 1616491) (by norm_num)
theorem B2873761 : Blo 1989435 2873761 := bstep (se 2 (by rfl) ⟨1077660, by rfl⟩ : syracuseStep 2873761 = 2155321) B2155321
theorem B61306901 : Blo 1989435 61306901 := bstep (se 6 (by rfl) ⟨1436880, by rfl⟩ : syracuseStep 61306901 = 2873761) B2873761
theorem B40871267 : Blo 1989435 40871267 := bstep (se 1 (by rfl) ⟨30653450, by rfl⟩ : syracuseStep 40871267 = 61306901) B61306901
theorem B27247511 : Blo 1989435 27247511 := bstep (se 1 (by rfl) ⟨20435633, by rfl⟩ : syracuseStep 27247511 = 40871267) B40871267
theorem B18165007 : Blo 1989435 18165007 := bstep (se 1 (by rfl) ⟨13623755, by rfl⟩ : syracuseStep 18165007 = 27247511) B27247511
theorem B24220009 : Blo 1989435 24220009 := bstep (se 2 (by rfl) ⟨9082503, by rfl⟩ : syracuseStep 24220009 = 18165007) B18165007
theorem B32293345 : Blo 1989435 32293345 := bstep (se 2 (by rfl) ⟨12110004, by rfl⟩ : syracuseStep 32293345 = 24220009) B24220009
theorem B43057793 : Blo 1989435 43057793 := bstep (se 2 (by rfl) ⟨16146672, by rfl⟩ : syracuseStep 43057793 = 32293345) B32293345
theorem B28705195 : Blo 1989435 28705195 := bstep (se 1 (by rfl) ⟨21528896, by rfl⟩ : syracuseStep 28705195 = 43057793) B43057793
theorem B38273593 : Blo 1989435 38273593 := bstep (se 2 (by rfl) ⟨14352597, by rfl⟩ : syracuseStep 38273593 = 28705195) B28705195
theorem B51031457 : Blo 1989435 51031457 := bstep (se 2 (by rfl) ⟨19136796, by rfl⟩ : syracuseStep 51031457 = 38273593) B38273593
theorem B34020971 : Blo 1989435 34020971 := bstep (se 1 (by rfl) ⟨25515728, by rfl⟩ : syracuseStep 34020971 = 51031457) B51031457
theorem B22680647 : Blo 1989435 22680647 := bstep (se 1 (by rfl) ⟨17010485, by rfl⟩ : syracuseStep 22680647 = 34020971) B34020971
theorem B15120431 : Blo 1989435 15120431 := bstep (se 1 (by rfl) ⟨11340323, by rfl⟩ : syracuseStep 15120431 = 22680647) B22680647
theorem B10080287 : Blo 1989435 10080287 := bstep (se 1 (by rfl) ⟨7560215, by rfl⟩ : syracuseStep 10080287 = 15120431) B15120431
theorem B6720191 : Blo 1989435 6720191 := bstep (se 1 (by rfl) ⟨5040143, by rfl⟩ : syracuseStep 6720191 = 10080287) B10080287
theorem B4480127 : Blo 1989435 4480127 := bstep (se 1 (by rfl) ⟨3360095, by rfl⟩ : syracuseStep 4480127 = 6720191) B6720191
theorem B2986751 : Blo 1989435 2986751 := bstep (se 1 (by rfl) ⟨2240063, by rfl⟩ : syracuseStep 2986751 = 4480127) B4480127
theorem B1991167 : Blo 1989435 1991167 := bstep (se 1 (by rfl) ⟨1493375, by rfl⟩ : syracuseStep 1991167 = 2986751) B2986751
theorem B2986757 : Blo 1989435 2986757 := bbase (se 4 (by rfl) ⟨280008, by rfl⟩ : syracuseStep 2986757 = 560017) (by norm_num)
theorem B1991171 : Blo 1989435 1991171 := bstep (se 1 (by rfl) ⟨1493378, by rfl⟩ : syracuseStep 1991171 = 2986757) B2986757
theorem B3360109 : Blo 1989435 3360109 := bbase (se 3 (by rfl) ⟨630020, by rfl⟩ : syracuseStep 3360109 = 1260041) (by norm_num)
theorem B4480145 : Blo 1989435 4480145 := bstep (se 2 (by rfl) ⟨1680054, by rfl⟩ : syracuseStep 4480145 = 3360109) B3360109
theorem B2986763 : Blo 1989435 2986763 := bstep (se 1 (by rfl) ⟨2240072, by rfl⟩ : syracuseStep 2986763 = 4480145) B4480145
theorem B1991175 : Blo 1989435 1991175 := bstep (se 1 (by rfl) ⟨1493381, by rfl⟩ : syracuseStep 1991175 = 2986763) B2986763
theorem B2240077 : Blo 1989435 2240077 := bbase (se 3 (by rfl) ⟨420014, by rfl⟩ : syracuseStep 2240077 = 840029) (by norm_num)
theorem B2986769 : Blo 1989435 2986769 := bstep (se 2 (by rfl) ⟨1120038, by rfl⟩ : syracuseStep 2986769 = 2240077) B2240077
theorem B1991179 : Blo 1989435 1991179 := bstep (se 1 (by rfl) ⟨1493384, by rfl⟩ : syracuseStep 1991179 = 2986769) B2986769
theorem B6720245 : Blo 1989435 6720245 := bbase (se 5 (by rfl) ⟨315011, by rfl⟩ : syracuseStep 6720245 = 630023) (by norm_num)
theorem B4480163 : Blo 1989435 4480163 := bstep (se 1 (by rfl) ⟨3360122, by rfl⟩ : syracuseStep 4480163 = 6720245) B6720245
theorem B2986775 : Blo 1989435 2986775 := bstep (se 1 (by rfl) ⟨2240081, by rfl⟩ : syracuseStep 2986775 = 4480163) B4480163
theorem B1991183 : Blo 1989435 1991183 := bstep (se 1 (by rfl) ⟨1493387, by rfl⟩ : syracuseStep 1991183 = 2986775) B2986775
theorem B2986781 : Blo 1989435 2986781 := bbase (se 3 (by rfl) ⟨560021, by rfl⟩ : syracuseStep 2986781 = 1120043) (by norm_num)
theorem B1991187 : Blo 1989435 1991187 := bstep (se 1 (by rfl) ⟨1493390, by rfl⟩ : syracuseStep 1991187 = 2986781) B2986781
theorem B4480181 : Blo 1989435 4480181 := bbase (se 5 (by rfl) ⟨210008, by rfl⟩ : syracuseStep 4480181 = 420017) (by norm_num)
theorem B2986787 : Blo 1989435 2986787 := bstep (se 1 (by rfl) ⟨2240090, by rfl⟩ : syracuseStep 2986787 = 4480181) B4480181
theorem B1991191 : Blo 1989435 1991191 := bstep (se 1 (by rfl) ⟨1493393, by rfl⟩ : syracuseStep 1991191 = 2986787) B2986787
theorem B2126341 : Blo 1989435 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B11340485 : Blo 1989435 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B7560323 : Blo 1989435 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B5040215 : Blo 1989435 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B3360143 : Blo 1989435 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B2240095 : Blo 1989435 2240095 := bstep (se 1 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 2240095 = 3360143) B3360143
theorem B2986793 : Blo 1989435 2986793 := bstep (se 2 (by rfl) ⟨1120047, by rfl⟩ : syracuseStep 2986793 = 2240095) B2240095
theorem B1991195 : Blo 1989435 1991195 := bstep (se 1 (by rfl) ⟨1493396, by rfl⟩ : syracuseStep 1991195 = 2986793) B2986793
theorem B2126345 : Blo 1989435 2126345 := bbase (se 2 (by rfl) ⟨797379, by rfl⟩ : syracuseStep 2126345 = 1594759) (by norm_num)
theorem B5670253 : Blo 1989435 5670253 := bstep (se 3 (by rfl) ⟨1063172, by rfl⟩ : syracuseStep 5670253 = 2126345) B2126345
theorem B7560337 : Blo 1989435 7560337 := bstep (se 2 (by rfl) ⟨2835126, by rfl⟩ : syracuseStep 7560337 = 5670253) B5670253
theorem B10080449 : Blo 1989435 10080449 := bstep (se 2 (by rfl) ⟨3780168, by rfl⟩ : syracuseStep 10080449 = 7560337) B7560337
theorem B6720299 : Blo 1989435 6720299 := bstep (se 1 (by rfl) ⟨5040224, by rfl⟩ : syracuseStep 6720299 = 10080449) B10080449
theorem B4480199 : Blo 1989435 4480199 := bstep (se 1 (by rfl) ⟨3360149, by rfl⟩ : syracuseStep 4480199 = 6720299) B6720299
theorem B2986799 : Blo 1989435 2986799 := bstep (se 1 (by rfl) ⟨2240099, by rfl⟩ : syracuseStep 2986799 = 4480199) B4480199
theorem B1991199 : Blo 1989435 1991199 := bstep (se 1 (by rfl) ⟨1493399, by rfl⟩ : syracuseStep 1991199 = 2986799) B2986799
theorem B2986805 : Blo 1989435 2986805 := bbase (se 5 (by rfl) ⟨140006, by rfl⟩ : syracuseStep 2986805 = 280013) (by norm_num)
theorem B1991203 : Blo 1989435 1991203 := bstep (se 1 (by rfl) ⟨1493402, by rfl⟩ : syracuseStep 1991203 = 2986805) B2986805
theorem B5040245 : Blo 1989435 5040245 := bbase (se 5 (by rfl) ⟨236261, by rfl⟩ : syracuseStep 5040245 = 472523) (by norm_num)
theorem B3360163 : Blo 1989435 3360163 := bstep (se 1 (by rfl) ⟨2520122, by rfl⟩ : syracuseStep 3360163 = 5040245) B5040245
theorem B4480217 : Blo 1989435 4480217 := bstep (se 2 (by rfl) ⟨1680081, by rfl⟩ : syracuseStep 4480217 = 3360163) B3360163
theorem B2986811 : Blo 1989435 2986811 := bstep (se 1 (by rfl) ⟨2240108, by rfl⟩ : syracuseStep 2986811 = 4480217) B4480217
theorem B1991207 : Blo 1989435 1991207 := bstep (se 1 (by rfl) ⟨1493405, by rfl⟩ : syracuseStep 1991207 = 2986811) B2986811
theorem B2240113 : Blo 1989435 2240113 := bbase (se 2 (by rfl) ⟨840042, by rfl⟩ : syracuseStep 2240113 = 1680085) (by norm_num)
theorem B2986817 : Blo 1989435 2986817 := bstep (se 2 (by rfl) ⟨1120056, by rfl⟩ : syracuseStep 2986817 = 2240113) B2240113
theorem B1991211 : Blo 1989435 1991211 := bstep (se 1 (by rfl) ⟨1493408, by rfl⟩ : syracuseStep 1991211 = 2986817) B2986817
theorem B2554517 : Blo 1989435 2554517 := bbase (se 6 (by rfl) ⟨59871, by rfl⟩ : syracuseStep 2554517 = 119743) (by norm_num)
theorem B6812045 : Blo 1989435 6812045 := bstep (se 3 (by rfl) ⟨1277258, by rfl⟩ : syracuseStep 6812045 = 2554517) B2554517
theorem B4541363 : Blo 1989435 4541363 := bstep (se 1 (by rfl) ⟨3406022, by rfl⟩ : syracuseStep 4541363 = 6812045) B6812045
theorem B3027575 : Blo 1989435 3027575 := bstep (se 1 (by rfl) ⟨2270681, by rfl⟩ : syracuseStep 3027575 = 4541363) B4541363
theorem B8073533 : Blo 1989435 8073533 := bstep (se 3 (by rfl) ⟨1513787, by rfl⟩ : syracuseStep 8073533 = 3027575) B3027575
theorem B21529421 : Blo 1989435 21529421 := bstep (se 3 (by rfl) ⟨4036766, by rfl⟩ : syracuseStep 21529421 = 8073533) B8073533
theorem B14352947 : Blo 1989435 14352947 := bstep (se 1 (by rfl) ⟨10764710, by rfl⟩ : syracuseStep 14352947 = 21529421) B21529421
theorem B9568631 : Blo 1989435 9568631 := bstep (se 1 (by rfl) ⟨7176473, by rfl⟩ : syracuseStep 9568631 = 14352947) B14352947
theorem B6379087 : Blo 1989435 6379087 := bstep (se 1 (by rfl) ⟨4784315, by rfl⟩ : syracuseStep 6379087 = 9568631) B9568631
theorem B8505449 : Blo 1989435 8505449 := bstep (se 2 (by rfl) ⟨3189543, by rfl⟩ : syracuseStep 8505449 = 6379087) B6379087
theorem B5670299 : Blo 1989435 5670299 := bstep (se 1 (by rfl) ⟨4252724, by rfl⟩ : syracuseStep 5670299 = 8505449) B8505449
theorem B3780199 : Blo 1989435 3780199 := bstep (se 1 (by rfl) ⟨2835149, by rfl⟩ : syracuseStep 3780199 = 5670299) B5670299
theorem B5040265 : Blo 1989435 5040265 := bstep (se 2 (by rfl) ⟨1890099, by rfl⟩ : syracuseStep 5040265 = 3780199) B3780199
theorem B6720353 : Blo 1989435 6720353 := bstep (se 2 (by rfl) ⟨2520132, by rfl⟩ : syracuseStep 6720353 = 5040265) B5040265
theorem B4480235 : Blo 1989435 4480235 := bstep (se 1 (by rfl) ⟨3360176, by rfl⟩ : syracuseStep 4480235 = 6720353) B6720353
theorem B2986823 : Blo 1989435 2986823 := bstep (se 1 (by rfl) ⟨2240117, by rfl⟩ : syracuseStep 2986823 = 4480235) B4480235
theorem B1991215 : Blo 1989435 1991215 := bstep (se 1 (by rfl) ⟨1493411, by rfl⟩ : syracuseStep 1991215 = 2986823) B2986823
theorem B2986829 : Blo 1989435 2986829 := bbase (se 3 (by rfl) ⟨560030, by rfl⟩ : syracuseStep 2986829 = 1120061) (by norm_num)
theorem B1991219 : Blo 1989435 1991219 := bstep (se 1 (by rfl) ⟨1493414, by rfl⟩ : syracuseStep 1991219 = 2986829) B2986829
theorem B4480253 : Blo 1989435 4480253 := bbase (se 3 (by rfl) ⟨840047, by rfl⟩ : syracuseStep 4480253 = 1680095) (by norm_num)
theorem B2986835 : Blo 1989435 2986835 := bstep (se 1 (by rfl) ⟨2240126, by rfl⟩ : syracuseStep 2986835 = 4480253) B4480253
theorem B1991223 : Blo 1989435 1991223 := bstep (se 1 (by rfl) ⟨1493417, by rfl⟩ : syracuseStep 1991223 = 2986835) B2986835
theorem B3360197 : Blo 1989435 3360197 := bbase (se 4 (by rfl) ⟨315018, by rfl⟩ : syracuseStep 3360197 = 630037) (by norm_num)
theorem B2240131 : Blo 1989435 2240131 := bstep (se 1 (by rfl) ⟨1680098, by rfl⟩ : syracuseStep 2240131 = 3360197) B3360197
theorem B2986841 : Blo 1989435 2986841 := bstep (se 2 (by rfl) ⟨1120065, by rfl⟩ : syracuseStep 2986841 = 2240131) B2240131
theorem B1991227 : Blo 1989435 1991227 := bstep (se 1 (by rfl) ⟨1493420, by rfl⟩ : syracuseStep 1991227 = 2986841) B2986841
theorem B15120917 : Blo 1989435 15120917 := bbase (se 6 (by rfl) ⟨354396, by rfl⟩ : syracuseStep 15120917 = 708793) (by norm_num)
theorem B10080611 : Blo 1989435 10080611 := bstep (se 1 (by rfl) ⟨7560458, by rfl⟩ : syracuseStep 10080611 = 15120917) B15120917
theorem B6720407 : Blo 1989435 6720407 := bstep (se 1 (by rfl) ⟨5040305, by rfl⟩ : syracuseStep 6720407 = 10080611) B10080611
theorem B4480271 : Blo 1989435 4480271 := bstep (se 1 (by rfl) ⟨3360203, by rfl⟩ : syracuseStep 4480271 = 6720407) B6720407
theorem B2986847 : Blo 1989435 2986847 := bstep (se 1 (by rfl) ⟨2240135, by rfl⟩ : syracuseStep 2986847 = 4480271) B4480271
theorem B1991231 : Blo 1989435 1991231 := bstep (se 1 (by rfl) ⟨1493423, by rfl⟩ : syracuseStep 1991231 = 2986847) B2986847
theorem B2986853 : Blo 1989435 2986853 := bbase (se 4 (by rfl) ⟨280017, by rfl⟩ : syracuseStep 2986853 = 560035) (by norm_num)
theorem B1991235 : Blo 1989435 1991235 := bstep (se 1 (by rfl) ⟨1493426, by rfl⟩ : syracuseStep 1991235 = 2986853) B2986853
theorem B3780245 : Blo 1989435 3780245 := bbase (se 6 (by rfl) ⟨88599, by rfl⟩ : syracuseStep 3780245 = 177199) (by norm_num)
theorem B2520163 : Blo 1989435 2520163 := bstep (se 1 (by rfl) ⟨1890122, by rfl⟩ : syracuseStep 2520163 = 3780245) B3780245
theorem B3360217 : Blo 1989435 3360217 := bstep (se 2 (by rfl) ⟨1260081, by rfl⟩ : syracuseStep 3360217 = 2520163) B2520163
theorem B4480289 : Blo 1989435 4480289 := bstep (se 2 (by rfl) ⟨1680108, by rfl⟩ : syracuseStep 4480289 = 3360217) B3360217
theorem B2986859 : Blo 1989435 2986859 := bstep (se 1 (by rfl) ⟨2240144, by rfl⟩ : syracuseStep 2986859 = 4480289) B4480289
theorem B1991239 : Blo 1989435 1991239 := bstep (se 1 (by rfl) ⟨1493429, by rfl⟩ : syracuseStep 1991239 = 2986859) B2986859
theorem B2240149 : Blo 1989435 2240149 := bbase (se 6 (by rfl) ⟨52503, by rfl⟩ : syracuseStep 2240149 = 105007) (by norm_num)
theorem B2986865 : Blo 1989435 2986865 := bstep (se 2 (by rfl) ⟨1120074, by rfl⟩ : syracuseStep 2986865 = 2240149) B2240149
theorem B1991243 : Blo 1989435 1991243 := bstep (se 1 (by rfl) ⟨1493432, by rfl⟩ : syracuseStep 1991243 = 2986865) B2986865
theorem B2520173 : Blo 1989435 2520173 := bbase (se 3 (by rfl) ⟨472532, by rfl⟩ : syracuseStep 2520173 = 945065) (by norm_num)
theorem B6720461 : Blo 1989435 6720461 := bstep (se 3 (by rfl) ⟨1260086, by rfl⟩ : syracuseStep 6720461 = 2520173) B2520173
theorem B4480307 : Blo 1989435 4480307 := bstep (se 1 (by rfl) ⟨3360230, by rfl⟩ : syracuseStep 4480307 = 6720461) B6720461
theorem B2986871 : Blo 1989435 2986871 := bstep (se 1 (by rfl) ⟨2240153, by rfl⟩ : syracuseStep 2986871 = 4480307) B4480307
theorem B1991247 : Blo 1989435 1991247 := bstep (se 1 (by rfl) ⟨1493435, by rfl⟩ : syracuseStep 1991247 = 2986871) B2986871
theorem B2986877 : Blo 1989435 2986877 := bbase (se 3 (by rfl) ⟨560039, by rfl⟩ : syracuseStep 2986877 = 1120079) (by norm_num)
theorem B1991251 : Blo 1989435 1991251 := bstep (se 1 (by rfl) ⟨1493438, by rfl⟩ : syracuseStep 1991251 = 2986877) B2986877
theorem B4480325 : Blo 1989435 4480325 := bbase (se 4 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 4480325 = 840061) (by norm_num)
theorem B2986883 : Blo 1989435 2986883 := bstep (se 1 (by rfl) ⟨2240162, by rfl⟩ : syracuseStep 2986883 = 4480325) B4480325
theorem B1991255 : Blo 1989435 1991255 := bstep (se 1 (by rfl) ⟨1493441, by rfl⟩ : syracuseStep 1991255 = 2986883) B2986883
theorem B3588317 : Blo 1989435 3588317 := bbase (se 3 (by rfl) ⟨672809, by rfl⟩ : syracuseStep 3588317 = 1345619) (by norm_num)
theorem B2392211 : Blo 1989435 2392211 := bstep (se 1 (by rfl) ⟨1794158, by rfl⟩ : syracuseStep 2392211 = 3588317) B3588317
theorem B6379229 : Blo 1989435 6379229 := bstep (se 3 (by rfl) ⟨1196105, by rfl⟩ : syracuseStep 6379229 = 2392211) B2392211
theorem B4252819 : Blo 1989435 4252819 := bstep (se 1 (by rfl) ⟨3189614, by rfl⟩ : syracuseStep 4252819 = 6379229) B6379229
theorem B5670425 : Blo 1989435 5670425 := bstep (se 2 (by rfl) ⟨2126409, by rfl⟩ : syracuseStep 5670425 = 4252819) B4252819
theorem B3780283 : Blo 1989435 3780283 := bstep (se 1 (by rfl) ⟨2835212, by rfl⟩ : syracuseStep 3780283 = 5670425) B5670425
theorem B5040377 : Blo 1989435 5040377 := bstep (se 2 (by rfl) ⟨1890141, by rfl⟩ : syracuseStep 5040377 = 3780283) B3780283
theorem B3360251 : Blo 1989435 3360251 := bstep (se 1 (by rfl) ⟨2520188, by rfl⟩ : syracuseStep 3360251 = 5040377) B5040377
theorem B2240167 : Blo 1989435 2240167 := bstep (se 1 (by rfl) ⟨1680125, by rfl⟩ : syracuseStep 2240167 = 3360251) B3360251
theorem B2986889 : Blo 1989435 2986889 := bstep (se 2 (by rfl) ⟨1120083, by rfl⟩ : syracuseStep 2986889 = 2240167) B2240167
theorem B1991259 : Blo 1989435 1991259 := bstep (se 1 (by rfl) ⟨1493444, by rfl⟩ : syracuseStep 1991259 = 2986889) B2986889
theorem B10080773 : Blo 1989435 10080773 := bbase (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) (by norm_num)
theorem B6720515 : Blo 1989435 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B4480343 : Blo 1989435 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B2986895 : Blo 1989435 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B1991263 : Blo 1989435 1991263 := bstep (se 1 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 1991263 = 2986895) B2986895
theorem B2986901 : Blo 1989435 2986901 := bbase (se 6 (by rfl) ⟨70005, by rfl⟩ : syracuseStep 2986901 = 140011) (by norm_num)
theorem B1991267 : Blo 1989435 1991267 := bstep (se 1 (by rfl) ⟨1493450, by rfl⟩ : syracuseStep 1991267 = 2986901) B2986901
theorem B11340917 : Blo 1989435 11340917 := bbase (se 5 (by rfl) ⟨531605, by rfl⟩ : syracuseStep 11340917 = 1063211) (by norm_num)
theorem B7560611 : Blo 1989435 7560611 := bstep (se 1 (by rfl) ⟨5670458, by rfl⟩ : syracuseStep 7560611 = 11340917) B11340917
theorem B5040407 : Blo 1989435 5040407 := bstep (se 1 (by rfl) ⟨3780305, by rfl⟩ : syracuseStep 5040407 = 7560611) B7560611
theorem B3360271 : Blo 1989435 3360271 := bstep (se 1 (by rfl) ⟨2520203, by rfl⟩ : syracuseStep 3360271 = 5040407) B5040407
theorem B4480361 : Blo 1989435 4480361 := bstep (se 2 (by rfl) ⟨1680135, by rfl⟩ : syracuseStep 4480361 = 3360271) B3360271
theorem B2986907 : Blo 1989435 2986907 := bstep (se 1 (by rfl) ⟨2240180, by rfl⟩ : syracuseStep 2986907 = 4480361) B4480361
theorem B1991271 : Blo 1989435 1991271 := bstep (se 1 (by rfl) ⟨1493453, by rfl⟩ : syracuseStep 1991271 = 2986907) B2986907
theorem B2240185 : Blo 1989435 2240185 := bbase (se 2 (by rfl) ⟨840069, by rfl⟩ : syracuseStep 2240185 = 1680139) (by norm_num)
theorem B2986913 : Blo 1989435 2986913 := bstep (se 2 (by rfl) ⟨1120092, by rfl⟩ : syracuseStep 2986913 = 2240185) B2240185
theorem B1991275 : Blo 1989435 1991275 := bstep (se 1 (by rfl) ⟨1493456, by rfl⟩ : syracuseStep 1991275 = 2986913) B2986913
theorem B4252861 : Blo 1989435 4252861 := bbase (se 3 (by rfl) ⟨797411, by rfl⟩ : syracuseStep 4252861 = 1594823) (by norm_num)
theorem B5670481 : Blo 1989435 5670481 := bstep (se 2 (by rfl) ⟨2126430, by rfl⟩ : syracuseStep 5670481 = 4252861) B4252861
theorem B7560641 : Blo 1989435 7560641 := bstep (se 2 (by rfl) ⟨2835240, by rfl⟩ : syracuseStep 7560641 = 5670481) B5670481
theorem B5040427 : Blo 1989435 5040427 := bstep (se 1 (by rfl) ⟨3780320, by rfl⟩ : syracuseStep 5040427 = 7560641) B7560641
theorem B6720569 : Blo 1989435 6720569 := bstep (se 2 (by rfl) ⟨2520213, by rfl⟩ : syracuseStep 6720569 = 5040427) B5040427
theorem B4480379 : Blo 1989435 4480379 := bstep (se 1 (by rfl) ⟨3360284, by rfl⟩ : syracuseStep 4480379 = 6720569) B6720569
theorem B2986919 : Blo 1989435 2986919 := bstep (se 1 (by rfl) ⟨2240189, by rfl⟩ : syracuseStep 2986919 = 4480379) B4480379
theorem B1991279 : Blo 1989435 1991279 := bstep (se 1 (by rfl) ⟨1493459, by rfl⟩ : syracuseStep 1991279 = 2986919) B2986919
theorem B2986925 : Blo 1989435 2986925 := bbase (se 3 (by rfl) ⟨560048, by rfl⟩ : syracuseStep 2986925 = 1120097) (by norm_num)
theorem B1991283 : Blo 1989435 1991283 := bstep (se 1 (by rfl) ⟨1493462, by rfl⟩ : syracuseStep 1991283 = 2986925) B2986925
theorem B4480397 : Blo 1989435 4480397 := bbase (se 3 (by rfl) ⟨840074, by rfl⟩ : syracuseStep 4480397 = 1680149) (by norm_num)
theorem B2986931 : Blo 1989435 2986931 := bstep (se 1 (by rfl) ⟨2240198, by rfl⟩ : syracuseStep 2986931 = 4480397) B4480397
theorem B1991287 : Blo 1989435 1991287 := bstep (se 1 (by rfl) ⟨1493465, by rfl⟩ : syracuseStep 1991287 = 2986931) B2986931
theorem B2520229 : Blo 1989435 2520229 := bbase (se 4 (by rfl) ⟨236271, by rfl⟩ : syracuseStep 2520229 = 472543) (by norm_num)
theorem B3360305 : Blo 1989435 3360305 := bstep (se 2 (by rfl) ⟨1260114, by rfl⟩ : syracuseStep 3360305 = 2520229) B2520229
theorem B2240203 : Blo 1989435 2240203 := bstep (se 1 (by rfl) ⟨1680152, by rfl⟩ : syracuseStep 2240203 = 3360305) B3360305
theorem B2986937 : Blo 1989435 2986937 := bstep (se 2 (by rfl) ⟨1120101, by rfl⟩ : syracuseStep 2986937 = 2240203) B2240203
theorem B1991291 : Blo 1989435 1991291 := bstep (se 1 (by rfl) ⟨1493468, by rfl⟩ : syracuseStep 1991291 = 2986937) B2986937
theorem B2624801 : Blo 1989435 2624801 := bbase (se 2 (by rfl) ⟨984300, by rfl⟩ : syracuseStep 2624801 = 1968601) (by norm_num)
theorem B6999469 : Blo 1989435 6999469 := bstep (se 3 (by rfl) ⟨1312400, by rfl⟩ : syracuseStep 6999469 = 2624801) B2624801
theorem B149322005 : Blo 1989435 149322005 := bstep (se 6 (by rfl) ⟨3499734, by rfl⟩ : syracuseStep 149322005 = 6999469) B6999469
theorem B99548003 : Blo 1989435 99548003 := bstep (se 1 (by rfl) ⟨74661002, by rfl⟩ : syracuseStep 99548003 = 149322005) B149322005
theorem B66365335 : Blo 1989435 66365335 := bstep (se 1 (by rfl) ⟨49774001, by rfl⟩ : syracuseStep 66365335 = 99548003) B99548003
theorem B353948453 : Blo 1989435 353948453 := bstep (se 4 (by rfl) ⟨33182667, by rfl⟩ : syracuseStep 353948453 = 66365335) B66365335
theorem B235965635 : Blo 1989435 235965635 := bstep (se 1 (by rfl) ⟨176974226, by rfl⟩ : syracuseStep 235965635 = 353948453) B353948453
theorem B157310423 : Blo 1989435 157310423 := bstep (se 1 (by rfl) ⟨117982817, by rfl⟩ : syracuseStep 157310423 = 235965635) B235965635
theorem B104873615 : Blo 1989435 104873615 := bstep (se 1 (by rfl) ⟨78655211, by rfl⟩ : syracuseStep 104873615 = 157310423) B157310423
theorem B69915743 : Blo 1989435 69915743 := bstep (se 1 (by rfl) ⟨52436807, by rfl⟩ : syracuseStep 69915743 = 104873615) B104873615
theorem B46610495 : Blo 1989435 46610495 := bstep (se 1 (by rfl) ⟨34957871, by rfl⟩ : syracuseStep 46610495 = 69915743) B69915743
theorem B31073663 : Blo 1989435 31073663 := bstep (se 1 (by rfl) ⟨23305247, by rfl⟩ : syracuseStep 31073663 = 46610495) B46610495
theorem B82863101 : Blo 1989435 82863101 := bstep (se 3 (by rfl) ⟨15536831, by rfl⟩ : syracuseStep 82863101 = 31073663) B31073663
theorem B220968269 : Blo 1989435 220968269 := bstep (se 3 (by rfl) ⟨41431550, by rfl⟩ : syracuseStep 220968269 = 82863101) B82863101
theorem B147312179 : Blo 1989435 147312179 := bstep (se 1 (by rfl) ⟨110484134, by rfl⟩ : syracuseStep 147312179 = 220968269) B220968269
theorem B98208119 : Blo 1989435 98208119 := bstep (se 1 (by rfl) ⟨73656089, by rfl⟩ : syracuseStep 98208119 = 147312179) B147312179
theorem B65472079 : Blo 1989435 65472079 := bstep (se 1 (by rfl) ⟨49104059, by rfl⟩ : syracuseStep 65472079 = 98208119) B98208119
theorem B87296105 : Blo 1989435 87296105 := bstep (se 2 (by rfl) ⟨32736039, by rfl⟩ : syracuseStep 87296105 = 65472079) B65472079
theorem B58197403 : Blo 1989435 58197403 := bstep (se 1 (by rfl) ⟨43648052, by rfl⟩ : syracuseStep 58197403 = 87296105) B87296105
theorem B77596537 : Blo 1989435 77596537 := bstep (se 2 (by rfl) ⟨29098701, by rfl⟩ : syracuseStep 77596537 = 58197403) B58197403
theorem B103462049 : Blo 1989435 103462049 := bstep (se 2 (by rfl) ⟨38798268, by rfl⟩ : syracuseStep 103462049 = 77596537) B77596537
theorem B275898797 : Blo 1989435 275898797 := bstep (se 3 (by rfl) ⟨51731024, by rfl⟩ : syracuseStep 275898797 = 103462049) B103462049
theorem B183932531 : Blo 1989435 183932531 := bstep (se 1 (by rfl) ⟨137949398, by rfl⟩ : syracuseStep 183932531 = 275898797) B275898797
theorem B122621687 : Blo 1989435 122621687 := bstep (se 1 (by rfl) ⟨91966265, by rfl⟩ : syracuseStep 122621687 = 183932531) B183932531
theorem B81747791 : Blo 1989435 81747791 := bstep (se 1 (by rfl) ⟨61310843, by rfl⟩ : syracuseStep 81747791 = 122621687) B122621687
theorem B54498527 : Blo 1989435 54498527 := bstep (se 1 (by rfl) ⟨40873895, by rfl⟩ : syracuseStep 54498527 = 81747791) B81747791
theorem B36332351 : Blo 1989435 36332351 := bstep (se 1 (by rfl) ⟨27249263, by rfl⟩ : syracuseStep 36332351 = 54498527) B54498527
theorem B24221567 : Blo 1989435 24221567 := bstep (se 1 (by rfl) ⟨18166175, by rfl⟩ : syracuseStep 24221567 = 36332351) B36332351
theorem B16147711 : Blo 1989435 16147711 := bstep (se 1 (by rfl) ⟨12110783, by rfl⟩ : syracuseStep 16147711 = 24221567) B24221567
theorem B21530281 : Blo 1989435 21530281 := bstep (se 2 (by rfl) ⟨8073855, by rfl⟩ : syracuseStep 21530281 = 16147711) B16147711
theorem B28707041 : Blo 1989435 28707041 := bstep (se 2 (by rfl) ⟨10765140, by rfl⟩ : syracuseStep 28707041 = 21530281) B21530281
theorem B19138027 : Blo 1989435 19138027 := bstep (se 1 (by rfl) ⟨14353520, by rfl⟩ : syracuseStep 19138027 = 28707041) B28707041
theorem B25517369 : Blo 1989435 25517369 := bstep (se 2 (by rfl) ⟨9569013, by rfl⟩ : syracuseStep 25517369 = 19138027) B19138027
theorem B17011579 : Blo 1989435 17011579 := bstep (se 1 (by rfl) ⟨12758684, by rfl⟩ : syracuseStep 17011579 = 25517369) B25517369
theorem B22682105 : Blo 1989435 22682105 := bstep (se 2 (by rfl) ⟨8505789, by rfl⟩ : syracuseStep 22682105 = 17011579) B17011579
theorem B15121403 : Blo 1989435 15121403 := bstep (se 1 (by rfl) ⟨11341052, by rfl⟩ : syracuseStep 15121403 = 22682105) B22682105
theorem B10080935 : Blo 1989435 10080935 := bstep (se 1 (by rfl) ⟨7560701, by rfl⟩ : syracuseStep 10080935 = 15121403) B15121403
theorem B6720623 : Blo 1989435 6720623 := bstep (se 1 (by rfl) ⟨5040467, by rfl⟩ : syracuseStep 6720623 = 10080935) B10080935
theorem B4480415 : Blo 1989435 4480415 := bstep (se 1 (by rfl) ⟨3360311, by rfl⟩ : syracuseStep 4480415 = 6720623) B6720623
theorem B2986943 : Blo 1989435 2986943 := bstep (se 1 (by rfl) ⟨2240207, by rfl⟩ : syracuseStep 2986943 = 4480415) B4480415
theorem B1991295 : Blo 1989435 1991295 := bstep (se 1 (by rfl) ⟨1493471, by rfl⟩ : syracuseStep 1991295 = 2986943) B2986943
theorem B2986949 : Blo 1989435 2986949 := bbase (se 4 (by rfl) ⟨280026, by rfl⟩ : syracuseStep 2986949 = 560053) (by norm_num)
theorem B1991299 : Blo 1989435 1991299 := bstep (se 1 (by rfl) ⟨1493474, by rfl⟩ : syracuseStep 1991299 = 2986949) B2986949
theorem B3360325 : Blo 1989435 3360325 := bbase (se 4 (by rfl) ⟨315030, by rfl⟩ : syracuseStep 3360325 = 630061) (by norm_num)
theorem B4480433 : Blo 1989435 4480433 := bstep (se 2 (by rfl) ⟨1680162, by rfl⟩ : syracuseStep 4480433 = 3360325) B3360325
theorem B2986955 : Blo 1989435 2986955 := bstep (se 1 (by rfl) ⟨2240216, by rfl⟩ : syracuseStep 2986955 = 4480433) B4480433
theorem B1991303 : Blo 1989435 1991303 := bstep (se 1 (by rfl) ⟨1493477, by rfl⟩ : syracuseStep 1991303 = 2986955) B2986955
theorem B2240221 : Blo 1989435 2240221 := bbase (se 3 (by rfl) ⟨420041, by rfl⟩ : syracuseStep 2240221 = 840083) (by norm_num)
theorem B2986961 : Blo 1989435 2986961 := bstep (se 2 (by rfl) ⟨1120110, by rfl⟩ : syracuseStep 2986961 = 2240221) B2240221
theorem B1991307 : Blo 1989435 1991307 := bstep (se 1 (by rfl) ⟨1493480, by rfl⟩ : syracuseStep 1991307 = 2986961) B2986961
theorem B6720677 : Blo 1989435 6720677 := bbase (se 4 (by rfl) ⟨630063, by rfl⟩ : syracuseStep 6720677 = 1260127) (by norm_num)
theorem B4480451 : Blo 1989435 4480451 := bstep (se 1 (by rfl) ⟨3360338, by rfl⟩ : syracuseStep 4480451 = 6720677) B6720677
theorem B2986967 : Blo 1989435 2986967 := bstep (se 1 (by rfl) ⟨2240225, by rfl⟩ : syracuseStep 2986967 = 4480451) B4480451
theorem B1991311 : Blo 1989435 1991311 := bstep (se 1 (by rfl) ⟨1493483, by rfl⟩ : syracuseStep 1991311 = 2986967) B2986967
theorem B2986973 : Blo 1989435 2986973 := bbase (se 3 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 2986973 = 1120115) (by norm_num)
theorem B1991315 : Blo 1989435 1991315 := bstep (se 1 (by rfl) ⟨1493486, by rfl⟩ : syracuseStep 1991315 = 2986973) B2986973
theorem B4480469 : Blo 1989435 4480469 := bbase (se 7 (by rfl) ⟨52505, by rfl⟩ : syracuseStep 4480469 = 105011) (by norm_num)
theorem B2986979 : Blo 1989435 2986979 := bstep (se 1 (by rfl) ⟨2240234, by rfl⟩ : syracuseStep 2986979 = 4480469) B4480469
theorem B1991319 : Blo 1989435 1991319 := bstep (se 1 (by rfl) ⟨1493489, by rfl⟩ : syracuseStep 1991319 = 2986979) B2986979
theorem B3277349 : Blo 1989435 3277349 := bbase (se 4 (by rfl) ⟨307251, by rfl⟩ : syracuseStep 3277349 = 614503) (by norm_num)
theorem B2184899 : Blo 1989435 2184899 := bstep (se 1 (by rfl) ⟨1638674, by rfl⟩ : syracuseStep 2184899 = 3277349) B3277349
theorem B23305589 : Blo 1989435 23305589 := bstep (se 5 (by rfl) ⟨1092449, by rfl⟩ : syracuseStep 23305589 = 2184899) B2184899
theorem B15537059 : Blo 1989435 15537059 := bstep (se 1 (by rfl) ⟨11652794, by rfl⟩ : syracuseStep 15537059 = 23305589) B23305589
theorem B10358039 : Blo 1989435 10358039 := bstep (se 1 (by rfl) ⟨7768529, by rfl⟩ : syracuseStep 10358039 = 15537059) B15537059
theorem B6905359 : Blo 1989435 6905359 := bstep (se 1 (by rfl) ⟨5179019, by rfl⟩ : syracuseStep 6905359 = 10358039) B10358039
theorem B9207145 : Blo 1989435 9207145 := bstep (se 2 (by rfl) ⟨3452679, by rfl⟩ : syracuseStep 9207145 = 6905359) B6905359
theorem B12276193 : Blo 1989435 12276193 := bstep (se 2 (by rfl) ⟨4603572, by rfl⟩ : syracuseStep 12276193 = 9207145) B9207145
theorem B16368257 : Blo 1989435 16368257 := bstep (se 2 (by rfl) ⟨6138096, by rfl⟩ : syracuseStep 16368257 = 12276193) B12276193
theorem B10912171 : Blo 1989435 10912171 := bstep (se 1 (by rfl) ⟨8184128, by rfl⟩ : syracuseStep 10912171 = 16368257) B16368257
theorem B14549561 : Blo 1989435 14549561 := bstep (se 2 (by rfl) ⟨5456085, by rfl⟩ : syracuseStep 14549561 = 10912171) B10912171
theorem B9699707 : Blo 1989435 9699707 := bstep (se 1 (by rfl) ⟨7274780, by rfl⟩ : syracuseStep 9699707 = 14549561) B14549561
theorem B25865885 : Blo 1989435 25865885 := bstep (se 3 (by rfl) ⟨4849853, by rfl⟩ : syracuseStep 25865885 = 9699707) B9699707
theorem B17243923 : Blo 1989435 17243923 := bstep (se 1 (by rfl) ⟨12932942, by rfl⟩ : syracuseStep 17243923 = 25865885) B25865885
theorem B22991897 : Blo 1989435 22991897 := bstep (se 2 (by rfl) ⟨8621961, by rfl⟩ : syracuseStep 22991897 = 17243923) B17243923
theorem B61311725 : Blo 1989435 61311725 := bstep (se 3 (by rfl) ⟨11495948, by rfl⟩ : syracuseStep 61311725 = 22991897) B22991897
theorem B40874483 : Blo 1989435 40874483 := bstep (se 1 (by rfl) ⟨30655862, by rfl⟩ : syracuseStep 40874483 = 61311725) B61311725
theorem B27249655 : Blo 1989435 27249655 := bstep (se 1 (by rfl) ⟨20437241, by rfl⟩ : syracuseStep 27249655 = 40874483) B40874483
theorem B36332873 : Blo 1989435 36332873 := bstep (se 2 (by rfl) ⟨13624827, by rfl⟩ : syracuseStep 36332873 = 27249655) B27249655
theorem B24221915 : Blo 1989435 24221915 := bstep (se 1 (by rfl) ⟨18166436, by rfl⟩ : syracuseStep 24221915 = 36332873) B36332873
theorem B16147943 : Blo 1989435 16147943 := bstep (se 1 (by rfl) ⟨12110957, by rfl⟩ : syracuseStep 16147943 = 24221915) B24221915
theorem B10765295 : Blo 1989435 10765295 := bstep (se 1 (by rfl) ⟨8073971, by rfl⟩ : syracuseStep 10765295 = 16147943) B16147943
theorem B7176863 : Blo 1989435 7176863 := bstep (se 1 (by rfl) ⟨5382647, by rfl⟩ : syracuseStep 7176863 = 10765295) B10765295
theorem B19138301 : Blo 1989435 19138301 := bstep (se 3 (by rfl) ⟨3588431, by rfl⟩ : syracuseStep 19138301 = 7176863) B7176863
theorem B12758867 : Blo 1989435 12758867 := bstep (se 1 (by rfl) ⟨9569150, by rfl⟩ : syracuseStep 12758867 = 19138301) B19138301
theorem B8505911 : Blo 1989435 8505911 := bstep (se 1 (by rfl) ⟨6379433, by rfl⟩ : syracuseStep 8505911 = 12758867) B12758867
theorem B5670607 : Blo 1989435 5670607 := bstep (se 1 (by rfl) ⟨4252955, by rfl⟩ : syracuseStep 5670607 = 8505911) B8505911
theorem B7560809 : Blo 1989435 7560809 := bstep (se 2 (by rfl) ⟨2835303, by rfl⟩ : syracuseStep 7560809 = 5670607) B5670607
theorem B5040539 : Blo 1989435 5040539 := bstep (se 1 (by rfl) ⟨3780404, by rfl⟩ : syracuseStep 5040539 = 7560809) B7560809
theorem B3360359 : Blo 1989435 3360359 := bstep (se 1 (by rfl) ⟨2520269, by rfl⟩ : syracuseStep 3360359 = 5040539) B5040539
theorem B2240239 : Blo 1989435 2240239 := bstep (se 1 (by rfl) ⟨1680179, by rfl⟩ : syracuseStep 2240239 = 3360359) B3360359
theorem B2986985 : Blo 1989435 2986985 := bstep (se 2 (by rfl) ⟨1120119, by rfl⟩ : syracuseStep 2986985 = 2240239) B2240239
theorem B1991323 : Blo 1989435 1991323 := bstep (se 1 (by rfl) ⟨1493492, by rfl⟩ : syracuseStep 1991323 = 2986985) B2986985
theorem B6379445 : Blo 1989435 6379445 := bbase (se 5 (by rfl) ⟨299036, by rfl⟩ : syracuseStep 6379445 = 598073) (by norm_num)
theorem B17011853 : Blo 1989435 17011853 := bstep (se 3 (by rfl) ⟨3189722, by rfl⟩ : syracuseStep 17011853 = 6379445) B6379445
theorem B11341235 : Blo 1989435 11341235 := bstep (se 1 (by rfl) ⟨8505926, by rfl⟩ : syracuseStep 11341235 = 17011853) B17011853
theorem B7560823 : Blo 1989435 7560823 := bstep (se 1 (by rfl) ⟨5670617, by rfl⟩ : syracuseStep 7560823 = 11341235) B11341235
theorem B10081097 : Blo 1989435 10081097 := bstep (se 2 (by rfl) ⟨3780411, by rfl⟩ : syracuseStep 10081097 = 7560823) B7560823
theorem B6720731 : Blo 1989435 6720731 := bstep (se 1 (by rfl) ⟨5040548, by rfl⟩ : syracuseStep 6720731 = 10081097) B10081097
theorem B4480487 : Blo 1989435 4480487 := bstep (se 1 (by rfl) ⟨3360365, by rfl⟩ : syracuseStep 4480487 = 6720731) B6720731
theorem B2986991 : Blo 1989435 2986991 := bstep (se 1 (by rfl) ⟨2240243, by rfl⟩ : syracuseStep 2986991 = 4480487) B4480487
theorem B1991327 : Blo 1989435 1991327 := bstep (se 1 (by rfl) ⟨1493495, by rfl⟩ : syracuseStep 1991327 = 2986991) B2986991
theorem B2986997 : Blo 1989435 2986997 := bbase (se 5 (by rfl) ⟨140015, by rfl⟩ : syracuseStep 2986997 = 280031) (by norm_num)
theorem B1991331 : Blo 1989435 1991331 := bstep (se 1 (by rfl) ⟨1493498, by rfl⟩ : syracuseStep 1991331 = 2986997) B2986997
theorem B4252981 : Blo 1989435 4252981 := bbase (se 5 (by rfl) ⟨199358, by rfl⟩ : syracuseStep 4252981 = 398717) (by norm_num)
theorem B5670641 : Blo 1989435 5670641 := bstep (se 2 (by rfl) ⟨2126490, by rfl⟩ : syracuseStep 5670641 = 4252981) B4252981
theorem B3780427 : Blo 1989435 3780427 := bstep (se 1 (by rfl) ⟨2835320, by rfl⟩ : syracuseStep 3780427 = 5670641) B5670641
theorem B5040569 : Blo 1989435 5040569 := bstep (se 2 (by rfl) ⟨1890213, by rfl⟩ : syracuseStep 5040569 = 3780427) B3780427
theorem B3360379 : Blo 1989435 3360379 := bstep (se 1 (by rfl) ⟨2520284, by rfl⟩ : syracuseStep 3360379 = 5040569) B5040569
theorem B4480505 : Blo 1989435 4480505 := bstep (se 2 (by rfl) ⟨1680189, by rfl⟩ : syracuseStep 4480505 = 3360379) B3360379
theorem B2987003 : Blo 1989435 2987003 := bstep (se 1 (by rfl) ⟨2240252, by rfl⟩ : syracuseStep 2987003 = 4480505) B4480505
theorem B1991335 : Blo 1989435 1991335 := bstep (se 1 (by rfl) ⟨1493501, by rfl⟩ : syracuseStep 1991335 = 2987003) B2987003
theorem B2240257 : Blo 1989435 2240257 := bbase (se 2 (by rfl) ⟨840096, by rfl⟩ : syracuseStep 2240257 = 1680193) (by norm_num)
theorem B2987009 : Blo 1989435 2987009 := bstep (se 2 (by rfl) ⟨1120128, by rfl⟩ : syracuseStep 2987009 = 2240257) B2240257
theorem B1991339 : Blo 1989435 1991339 := bstep (se 1 (by rfl) ⟨1493504, by rfl⟩ : syracuseStep 1991339 = 2987009) B2987009
theorem B5040589 : Blo 1989435 5040589 := bbase (se 3 (by rfl) ⟨945110, by rfl⟩ : syracuseStep 5040589 = 1890221) (by norm_num)
theorem B6720785 : Blo 1989435 6720785 := bstep (se 2 (by rfl) ⟨2520294, by rfl⟩ : syracuseStep 6720785 = 5040589) B5040589
theorem B4480523 : Blo 1989435 4480523 := bstep (se 1 (by rfl) ⟨3360392, by rfl⟩ : syracuseStep 4480523 = 6720785) B6720785
theorem B2987015 : Blo 1989435 2987015 := bstep (se 1 (by rfl) ⟨2240261, by rfl⟩ : syracuseStep 2987015 = 4480523) B4480523
theorem B1991343 : Blo 1989435 1991343 := bstep (se 1 (by rfl) ⟨1493507, by rfl⟩ : syracuseStep 1991343 = 2987015) B2987015
theorem B2987021 : Blo 1989435 2987021 := bbase (se 3 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 2987021 = 1120133) (by norm_num)
theorem B1991347 : Blo 1989435 1991347 := bstep (se 1 (by rfl) ⟨1493510, by rfl⟩ : syracuseStep 1991347 = 2987021) B2987021
theorem B4480541 : Blo 1989435 4480541 := bbase (se 3 (by rfl) ⟨840101, by rfl⟩ : syracuseStep 4480541 = 1680203) (by norm_num)
theorem B2987027 : Blo 1989435 2987027 := bstep (se 1 (by rfl) ⟨2240270, by rfl⟩ : syracuseStep 2987027 = 4480541) B4480541
theorem B1991351 : Blo 1989435 1991351 := bstep (se 1 (by rfl) ⟨1493513, by rfl⟩ : syracuseStep 1991351 = 2987027) B2987027
theorem B3360413 : Blo 1989435 3360413 := bbase (se 3 (by rfl) ⟨630077, by rfl⟩ : syracuseStep 3360413 = 1260155) (by norm_num)
theorem B2240275 : Blo 1989435 2240275 := bstep (se 1 (by rfl) ⟨1680206, by rfl⟩ : syracuseStep 2240275 = 3360413) B3360413
theorem B2987033 : Blo 1989435 2987033 := bstep (se 2 (by rfl) ⟨1120137, by rfl⟩ : syracuseStep 2987033 = 2240275) B2240275
theorem B1991355 : Blo 1989435 1991355 := bstep (se 1 (by rfl) ⟨1493516, by rfl⟩ : syracuseStep 1991355 = 2987033) B2987033
theorem B2155529 : Blo 1989435 2155529 := bbase (se 2 (by rfl) ⟨808323, by rfl⟩ : syracuseStep 2155529 = 1616647) (by norm_num)
theorem B5748077 : Blo 1989435 5748077 := bstep (se 3 (by rfl) ⟨1077764, by rfl⟩ : syracuseStep 5748077 = 2155529) B2155529
theorem B15328205 : Blo 1989435 15328205 := bstep (se 3 (by rfl) ⟨2874038, by rfl⟩ : syracuseStep 15328205 = 5748077) B5748077
theorem B10218803 : Blo 1989435 10218803 := bstep (se 1 (by rfl) ⟨7664102, by rfl⟩ : syracuseStep 10218803 = 15328205) B15328205
theorem B27250141 : Blo 1989435 27250141 := bstep (se 3 (by rfl) ⟨5109401, by rfl⟩ : syracuseStep 27250141 = 10218803) B10218803
theorem B36333521 : Blo 1989435 36333521 := bstep (se 2 (by rfl) ⟨13625070, by rfl⟩ : syracuseStep 36333521 = 27250141) B27250141
theorem B24222347 : Blo 1989435 24222347 := bstep (se 1 (by rfl) ⟨18166760, by rfl⟩ : syracuseStep 24222347 = 36333521) B36333521
theorem B16148231 : Blo 1989435 16148231 := bstep (se 1 (by rfl) ⟨12111173, by rfl⟩ : syracuseStep 16148231 = 24222347) B24222347
theorem B10765487 : Blo 1989435 10765487 := bstep (se 1 (by rfl) ⟨8074115, by rfl⟩ : syracuseStep 10765487 = 16148231) B16148231
theorem B28707965 : Blo 1989435 28707965 := bstep (se 3 (by rfl) ⟨5382743, by rfl⟩ : syracuseStep 28707965 = 10765487) B10765487
theorem B19138643 : Blo 1989435 19138643 := bstep (se 1 (by rfl) ⟨14353982, by rfl⟩ : syracuseStep 19138643 = 28707965) B28707965
theorem B12759095 : Blo 1989435 12759095 := bstep (se 1 (by rfl) ⟨9569321, by rfl⟩ : syracuseStep 12759095 = 19138643) B19138643
theorem B8506063 : Blo 1989435 8506063 := bstep (se 1 (by rfl) ⟨6379547, by rfl⟩ : syracuseStep 8506063 = 12759095) B12759095
theorem B11341417 : Blo 1989435 11341417 := bstep (se 2 (by rfl) ⟨4253031, by rfl⟩ : syracuseStep 11341417 = 8506063) B8506063
theorem B15121889 : Blo 1989435 15121889 := bstep (se 2 (by rfl) ⟨5670708, by rfl⟩ : syracuseStep 15121889 = 11341417) B11341417
theorem B10081259 : Blo 1989435 10081259 := bstep (se 1 (by rfl) ⟨7560944, by rfl⟩ : syracuseStep 10081259 = 15121889) B15121889
theorem B6720839 : Blo 1989435 6720839 := bstep (se 1 (by rfl) ⟨5040629, by rfl⟩ : syracuseStep 6720839 = 10081259) B10081259
theorem B4480559 : Blo 1989435 4480559 := bstep (se 1 (by rfl) ⟨3360419, by rfl⟩ : syracuseStep 4480559 = 6720839) B6720839
theorem B2987039 : Blo 1989435 2987039 := bstep (se 1 (by rfl) ⟨2240279, by rfl⟩ : syracuseStep 2987039 = 4480559) B4480559
theorem B1991359 : Blo 1989435 1991359 := bstep (se 1 (by rfl) ⟨1493519, by rfl⟩ : syracuseStep 1991359 = 2987039) B2987039
theorem B2987045 : Blo 1989435 2987045 := bbase (se 4 (by rfl) ⟨280035, by rfl⟩ : syracuseStep 2987045 = 560071) (by norm_num)
theorem B1991363 : Blo 1989435 1991363 := bstep (se 1 (by rfl) ⟨1493522, by rfl⟩ : syracuseStep 1991363 = 2987045) B2987045
theorem B2520325 : Blo 1989435 2520325 := bbase (se 4 (by rfl) ⟨236280, by rfl⟩ : syracuseStep 2520325 = 472561) (by norm_num)
theorem B3360433 : Blo 1989435 3360433 := bstep (se 2 (by rfl) ⟨1260162, by rfl⟩ : syracuseStep 3360433 = 2520325) B2520325
theorem B4480577 : Blo 1989435 4480577 := bstep (se 2 (by rfl) ⟨1680216, by rfl⟩ : syracuseStep 4480577 = 3360433) B3360433
theorem B2987051 : Blo 1989435 2987051 := bstep (se 1 (by rfl) ⟨2240288, by rfl⟩ : syracuseStep 2987051 = 4480577) B4480577
theorem B1991367 : Blo 1989435 1991367 := bstep (se 1 (by rfl) ⟨1493525, by rfl⟩ : syracuseStep 1991367 = 2987051) B2987051
theorem B2240293 : Blo 1989435 2240293 := bbase (se 4 (by rfl) ⟨210027, by rfl⟩ : syracuseStep 2240293 = 420055) (by norm_num)
theorem B2987057 : Blo 1989435 2987057 := bstep (se 2 (by rfl) ⟨1120146, by rfl⟩ : syracuseStep 2987057 = 2240293) B2240293
theorem B1991371 : Blo 1989435 1991371 := bstep (se 1 (by rfl) ⟨1493528, by rfl⟩ : syracuseStep 1991371 = 2987057) B2987057
theorem B8506133 : Blo 1989435 8506133 := bbase (se 6 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 8506133 = 398725) (by norm_num)
theorem B5670755 : Blo 1989435 5670755 := bstep (se 1 (by rfl) ⟨4253066, by rfl⟩ : syracuseStep 5670755 = 8506133) B8506133
theorem B3780503 : Blo 1989435 3780503 := bstep (se 1 (by rfl) ⟨2835377, by rfl⟩ : syracuseStep 3780503 = 5670755) B5670755
theorem B2520335 : Blo 1989435 2520335 := bstep (se 1 (by rfl) ⟨1890251, by rfl⟩ : syracuseStep 2520335 = 3780503) B3780503
theorem B6720893 : Blo 1989435 6720893 := bstep (se 3 (by rfl) ⟨1260167, by rfl⟩ : syracuseStep 6720893 = 2520335) B2520335
theorem B4480595 : Blo 1989435 4480595 := bstep (se 1 (by rfl) ⟨3360446, by rfl⟩ : syracuseStep 4480595 = 6720893) B6720893
theorem B2987063 : Blo 1989435 2987063 := bstep (se 1 (by rfl) ⟨2240297, by rfl⟩ : syracuseStep 2987063 = 4480595) B4480595
theorem B1991375 : Blo 1989435 1991375 := bstep (se 1 (by rfl) ⟨1493531, by rfl⟩ : syracuseStep 1991375 = 2987063) B2987063
theorem B2987069 : Blo 1989435 2987069 := bbase (se 3 (by rfl) ⟨560075, by rfl⟩ : syracuseStep 2987069 = 1120151) (by norm_num)
theorem B1991379 : Blo 1989435 1991379 := bstep (se 1 (by rfl) ⟨1493534, by rfl⟩ : syracuseStep 1991379 = 2987069) B2987069
theorem B4480613 : Blo 1989435 4480613 := bbase (se 4 (by rfl) ⟨420057, by rfl⟩ : syracuseStep 4480613 = 840115) (by norm_num)
theorem B2987075 : Blo 1989435 2987075 := bstep (se 1 (by rfl) ⟨2240306, by rfl⟩ : syracuseStep 2987075 = 4480613) B4480613
theorem B1991383 : Blo 1989435 1991383 := bstep (se 1 (by rfl) ⟨1493537, by rfl⟩ : syracuseStep 1991383 = 2987075) B2987075
theorem B5040701 : Blo 1989435 5040701 := bbase (se 3 (by rfl) ⟨945131, by rfl⟩ : syracuseStep 5040701 = 1890263) (by norm_num)
theorem B3360467 : Blo 1989435 3360467 := bstep (se 1 (by rfl) ⟨2520350, by rfl⟩ : syracuseStep 3360467 = 5040701) B5040701
theorem B2240311 : Blo 1989435 2240311 := bstep (se 1 (by rfl) ⟨1680233, by rfl⟩ : syracuseStep 2240311 = 3360467) B3360467
theorem B2987081 : Blo 1989435 2987081 := bstep (se 2 (by rfl) ⟨1120155, by rfl⟩ : syracuseStep 2987081 = 2240311) B2240311
theorem B1991387 : Blo 1989435 1991387 := bstep (se 1 (by rfl) ⟨1493540, by rfl⟩ : syracuseStep 1991387 = 2987081) B2987081
theorem B3780533 : Blo 1989435 3780533 := bbase (se 5 (by rfl) ⟨177212, by rfl⟩ : syracuseStep 3780533 = 354425) (by norm_num)
theorem B10081421 : Blo 1989435 10081421 := bstep (se 3 (by rfl) ⟨1890266, by rfl⟩ : syracuseStep 10081421 = 3780533) B3780533
theorem B6720947 : Blo 1989435 6720947 := bstep (se 1 (by rfl) ⟨5040710, by rfl⟩ : syracuseStep 6720947 = 10081421) B10081421
theorem B4480631 : Blo 1989435 4480631 := bstep (se 1 (by rfl) ⟨3360473, by rfl⟩ : syracuseStep 4480631 = 6720947) B6720947
theorem B2987087 : Blo 1989435 2987087 := bstep (se 1 (by rfl) ⟨2240315, by rfl⟩ : syracuseStep 2987087 = 4480631) B4480631
theorem B1991391 : Blo 1989435 1991391 := bstep (se 1 (by rfl) ⟨1493543, by rfl⟩ : syracuseStep 1991391 = 2987087) B2987087
theorem B2987093 : Blo 1989435 2987093 := bbase (se 8 (by rfl) ⟨17502, by rfl⟩ : syracuseStep 2987093 = 35005) (by norm_num)
theorem B1991395 : Blo 1989435 1991395 := bstep (se 1 (by rfl) ⟨1493546, by rfl⟩ : syracuseStep 1991395 = 2987093) B2987093
theorem B2155573 : Blo 1989435 2155573 := bbase (se 5 (by rfl) ⟨101042, by rfl⟩ : syracuseStep 2155573 = 202085) (by norm_num)
theorem B2874097 : Blo 1989435 2874097 := bstep (se 2 (by rfl) ⟨1077786, by rfl⟩ : syracuseStep 2874097 = 2155573) B2155573
theorem B3832129 : Blo 1989435 3832129 := bstep (se 2 (by rfl) ⟨1437048, by rfl⟩ : syracuseStep 3832129 = 2874097) B2874097
theorem B20438021 : Blo 1989435 20438021 := bstep (se 4 (by rfl) ⟨1916064, by rfl⟩ : syracuseStep 20438021 = 3832129) B3832129
theorem B13625347 : Blo 1989435 13625347 := bstep (se 1 (by rfl) ⟨10219010, by rfl⟩ : syracuseStep 13625347 = 20438021) B20438021
theorem B18167129 : Blo 1989435 18167129 := bstep (se 2 (by rfl) ⟨6812673, by rfl⟩ : syracuseStep 18167129 = 13625347) B13625347
theorem B12111419 : Blo 1989435 12111419 := bstep (se 1 (by rfl) ⟨9083564, by rfl⟩ : syracuseStep 12111419 = 18167129) B18167129
theorem B8074279 : Blo 1989435 8074279 := bstep (se 1 (by rfl) ⟨6055709, by rfl⟩ : syracuseStep 8074279 = 12111419) B12111419
theorem B10765705 : Blo 1989435 10765705 := bstep (se 2 (by rfl) ⟨4037139, by rfl⟩ : syracuseStep 10765705 = 8074279) B8074279
theorem B14354273 : Blo 1989435 14354273 := bstep (se 2 (by rfl) ⟨5382852, by rfl⟩ : syracuseStep 14354273 = 10765705) B10765705
theorem B9569515 : Blo 1989435 9569515 := bstep (se 1 (by rfl) ⟨7177136, by rfl⟩ : syracuseStep 9569515 = 14354273) B14354273
theorem B12759353 : Blo 1989435 12759353 := bstep (se 2 (by rfl) ⟨4784757, by rfl⟩ : syracuseStep 12759353 = 9569515) B9569515
theorem B8506235 : Blo 1989435 8506235 := bstep (se 1 (by rfl) ⟨6379676, by rfl⟩ : syracuseStep 8506235 = 12759353) B12759353
theorem B5670823 : Blo 1989435 5670823 := bstep (se 1 (by rfl) ⟨4253117, by rfl⟩ : syracuseStep 5670823 = 8506235) B8506235
theorem B7561097 : Blo 1989435 7561097 := bstep (se 2 (by rfl) ⟨2835411, by rfl⟩ : syracuseStep 7561097 = 5670823) B5670823
theorem B5040731 : Blo 1989435 5040731 := bstep (se 1 (by rfl) ⟨3780548, by rfl⟩ : syracuseStep 5040731 = 7561097) B7561097
theorem B3360487 : Blo 1989435 3360487 := bstep (se 1 (by rfl) ⟨2520365, by rfl⟩ : syracuseStep 3360487 = 5040731) B5040731
theorem B4480649 : Blo 1989435 4480649 := bstep (se 2 (by rfl) ⟨1680243, by rfl⟩ : syracuseStep 4480649 = 3360487) B3360487
theorem B2987099 : Blo 1989435 2987099 := bstep (se 1 (by rfl) ⟨2240324, by rfl⟩ : syracuseStep 2987099 = 4480649) B4480649
theorem B1991399 : Blo 1989435 1991399 := bstep (se 1 (by rfl) ⟨1493549, by rfl⟩ : syracuseStep 1991399 = 2987099) B2987099
theorem B2240329 : Blo 1989435 2240329 := bbase (se 2 (by rfl) ⟨840123, by rfl⟩ : syracuseStep 2240329 = 1680247) (by norm_num)
theorem B2987105 : Blo 1989435 2987105 := bstep (se 2 (by rfl) ⟨1120164, by rfl⟩ : syracuseStep 2987105 = 2240329) B2240329
theorem B1991403 : Blo 1989435 1991403 := bstep (se 1 (by rfl) ⟨1493552, by rfl⟩ : syracuseStep 1991403 = 2987105) B2987105
theorem B6055733 : Blo 1989435 6055733 := bbase (se 5 (by rfl) ⟨283862, by rfl⟩ : syracuseStep 6055733 = 567725) (by norm_num)
theorem B16148621 : Blo 1989435 16148621 := bstep (se 3 (by rfl) ⟨3027866, by rfl⟩ : syracuseStep 16148621 = 6055733) B6055733
theorem B10765747 : Blo 1989435 10765747 := bstep (se 1 (by rfl) ⟨8074310, by rfl⟩ : syracuseStep 10765747 = 16148621) B16148621
theorem B14354329 : Blo 1989435 14354329 := bstep (se 2 (by rfl) ⟨5382873, by rfl⟩ : syracuseStep 14354329 = 10765747) B10765747
theorem B19139105 : Blo 1989435 19139105 := bstep (se 2 (by rfl) ⟨7177164, by rfl⟩ : syracuseStep 19139105 = 14354329) B14354329
theorem B12759403 : Blo 1989435 12759403 := bstep (se 1 (by rfl) ⟨9569552, by rfl⟩ : syracuseStep 12759403 = 19139105) B19139105
theorem B17012537 : Blo 1989435 17012537 := bstep (se 2 (by rfl) ⟨6379701, by rfl⟩ : syracuseStep 17012537 = 12759403) B12759403
theorem B11341691 : Blo 1989435 11341691 := bstep (se 1 (by rfl) ⟨8506268, by rfl⟩ : syracuseStep 11341691 = 17012537) B17012537
theorem B7561127 : Blo 1989435 7561127 := bstep (se 1 (by rfl) ⟨5670845, by rfl⟩ : syracuseStep 7561127 = 11341691) B11341691
theorem B5040751 : Blo 1989435 5040751 := bstep (se 1 (by rfl) ⟨3780563, by rfl⟩ : syracuseStep 5040751 = 7561127) B7561127
theorem B6721001 : Blo 1989435 6721001 := bstep (se 2 (by rfl) ⟨2520375, by rfl⟩ : syracuseStep 6721001 = 5040751) B5040751
theorem B4480667 : Blo 1989435 4480667 := bstep (se 1 (by rfl) ⟨3360500, by rfl⟩ : syracuseStep 4480667 = 6721001) B6721001
theorem B2987111 : Blo 1989435 2987111 := bstep (se 1 (by rfl) ⟨2240333, by rfl⟩ : syracuseStep 2987111 = 4480667) B4480667
theorem B1991407 : Blo 1989435 1991407 := bstep (se 1 (by rfl) ⟨1493555, by rfl⟩ : syracuseStep 1991407 = 2987111) B2987111
theorem B2987117 : Blo 1989435 2987117 := bbase (se 3 (by rfl) ⟨560084, by rfl⟩ : syracuseStep 2987117 = 1120169) (by norm_num)
theorem B1991411 : Blo 1989435 1991411 := bstep (se 1 (by rfl) ⟨1493558, by rfl⟩ : syracuseStep 1991411 = 2987117) B2987117
theorem B4480685 : Blo 1989435 4480685 := bbase (se 3 (by rfl) ⟨840128, by rfl⟩ : syracuseStep 4480685 = 1680257) (by norm_num)
theorem B2987123 : Blo 1989435 2987123 := bstep (se 1 (by rfl) ⟨2240342, by rfl⟩ : syracuseStep 2987123 = 4480685) B4480685
theorem B1991415 : Blo 1989435 1991415 := bstep (se 1 (by rfl) ⟨1493561, by rfl⟩ : syracuseStep 1991415 = 2987123) B2987123
theorem B9700181 : Blo 1989435 9700181 := bbase (se 9 (by rfl) ⟨28418, by rfl⟩ : syracuseStep 9700181 = 56837) (by norm_num)
theorem B6466787 : Blo 1989435 6466787 := bstep (se 1 (by rfl) ⟨4850090, by rfl⟩ : syracuseStep 6466787 = 9700181) B9700181
theorem B4311191 : Blo 1989435 4311191 := bstep (se 1 (by rfl) ⟨3233393, by rfl⟩ : syracuseStep 4311191 = 6466787) B6466787
theorem B2874127 : Blo 1989435 2874127 := bstep (se 1 (by rfl) ⟨2155595, by rfl⟩ : syracuseStep 2874127 = 4311191) B4311191
theorem B3832169 : Blo 1989435 3832169 := bstep (se 2 (by rfl) ⟨1437063, by rfl⟩ : syracuseStep 3832169 = 2874127) B2874127
theorem B10219117 : Blo 1989435 10219117 := bstep (se 3 (by rfl) ⟨1916084, by rfl⟩ : syracuseStep 10219117 = 3832169) B3832169
theorem B13625489 : Blo 1989435 13625489 := bstep (se 2 (by rfl) ⟨5109558, by rfl⟩ : syracuseStep 13625489 = 10219117) B10219117
theorem B9083659 : Blo 1989435 9083659 := bstep (se 1 (by rfl) ⟨6812744, by rfl⟩ : syracuseStep 9083659 = 13625489) B13625489
theorem B12111545 : Blo 1989435 12111545 := bstep (se 2 (by rfl) ⟨4541829, by rfl⟩ : syracuseStep 12111545 = 9083659) B9083659
theorem B8074363 : Blo 1989435 8074363 := bstep (se 1 (by rfl) ⟨6055772, by rfl⟩ : syracuseStep 8074363 = 12111545) B12111545
theorem B10765817 : Blo 1989435 10765817 := bstep (se 2 (by rfl) ⟨4037181, by rfl⟩ : syracuseStep 10765817 = 8074363) B8074363
theorem B7177211 : Blo 1989435 7177211 := bstep (se 1 (by rfl) ⟨5382908, by rfl⟩ : syracuseStep 7177211 = 10765817) B10765817
theorem B4784807 : Blo 1989435 4784807 := bstep (se 1 (by rfl) ⟨3588605, by rfl⟩ : syracuseStep 4784807 = 7177211) B7177211
theorem B3189871 : Blo 1989435 3189871 := bstep (se 1 (by rfl) ⟨2392403, by rfl⟩ : syracuseStep 3189871 = 4784807) B4784807
theorem B4253161 : Blo 1989435 4253161 := bstep (se 2 (by rfl) ⟨1594935, by rfl⟩ : syracuseStep 4253161 = 3189871) B3189871
theorem B5670881 : Blo 1989435 5670881 := bstep (se 2 (by rfl) ⟨2126580, by rfl⟩ : syracuseStep 5670881 = 4253161) B4253161
theorem B3780587 : Blo 1989435 3780587 := bstep (se 1 (by rfl) ⟨2835440, by rfl⟩ : syracuseStep 3780587 = 5670881) B5670881
theorem B2520391 : Blo 1989435 2520391 := bstep (se 1 (by rfl) ⟨1890293, by rfl⟩ : syracuseStep 2520391 = 3780587) B3780587
theorem B3360521 : Blo 1989435 3360521 := bstep (se 2 (by rfl) ⟨1260195, by rfl⟩ : syracuseStep 3360521 = 2520391) B2520391
theorem B2240347 : Blo 1989435 2240347 := bstep (se 1 (by rfl) ⟨1680260, by rfl⟩ : syracuseStep 2240347 = 3360521) B3360521
theorem B2987129 : Blo 1989435 2987129 := bstep (se 2 (by rfl) ⟨1120173, by rfl⟩ : syracuseStep 2987129 = 2240347) B2240347
theorem B1991419 : Blo 1989435 1991419 := bstep (se 1 (by rfl) ⟨1493564, by rfl⟩ : syracuseStep 1991419 = 2987129) B2987129
theorem B6055781 : Blo 1989435 6055781 := bbase (se 4 (by rfl) ⟨567729, by rfl⟩ : syracuseStep 6055781 = 1135459) (by norm_num)
theorem B16148749 : Blo 1989435 16148749 := bstep (se 3 (by rfl) ⟨3027890, by rfl⟩ : syracuseStep 16148749 = 6055781) B6055781
theorem B21531665 : Blo 1989435 21531665 := bstep (se 2 (by rfl) ⟨8074374, by rfl⟩ : syracuseStep 21531665 = 16148749) B16148749
theorem B14354443 : Blo 1989435 14354443 := bstep (se 1 (by rfl) ⟨10765832, by rfl⟩ : syracuseStep 14354443 = 21531665) B21531665
theorem B19139257 : Blo 1989435 19139257 := bstep (se 2 (by rfl) ⟨7177221, by rfl⟩ : syracuseStep 19139257 = 14354443) B14354443
theorem B25519009 : Blo 1989435 25519009 := bstep (se 2 (by rfl) ⟨9569628, by rfl⟩ : syracuseStep 25519009 = 19139257) B19139257
theorem B34025345 : Blo 1989435 34025345 := bstep (se 2 (by rfl) ⟨12759504, by rfl⟩ : syracuseStep 34025345 = 25519009) B25519009
theorem B22683563 : Blo 1989435 22683563 := bstep (se 1 (by rfl) ⟨17012672, by rfl⟩ : syracuseStep 22683563 = 34025345) B34025345
theorem B15122375 : Blo 1989435 15122375 := bstep (se 1 (by rfl) ⟨11341781, by rfl⟩ : syracuseStep 15122375 = 22683563) B22683563
theorem B10081583 : Blo 1989435 10081583 := bstep (se 1 (by rfl) ⟨7561187, by rfl⟩ : syracuseStep 10081583 = 15122375) B15122375
theorem B6721055 : Blo 1989435 6721055 := bstep (se 1 (by rfl) ⟨5040791, by rfl⟩ : syracuseStep 6721055 = 10081583) B10081583
theorem B4480703 : Blo 1989435 4480703 := bstep (se 1 (by rfl) ⟨3360527, by rfl⟩ : syracuseStep 4480703 = 6721055) B6721055
theorem B2987135 : Blo 1989435 2987135 := bstep (se 1 (by rfl) ⟨2240351, by rfl⟩ : syracuseStep 2987135 = 4480703) B4480703
theorem B1991423 : Blo 1989435 1991423 := bstep (se 1 (by rfl) ⟨1493567, by rfl⟩ : syracuseStep 1991423 = 2987135) B2987135
theorem B2987141 : Blo 1989435 2987141 := bbase (se 4 (by rfl) ⟨280044, by rfl⟩ : syracuseStep 2987141 = 560089) (by norm_num)
theorem B1991427 : Blo 1989435 1991427 := bstep (se 1 (by rfl) ⟨1493570, by rfl⟩ : syracuseStep 1991427 = 2987141) B2987141
theorem B3360541 : Blo 1989435 3360541 := bbase (se 3 (by rfl) ⟨630101, by rfl⟩ : syracuseStep 3360541 = 1260203) (by norm_num)
theorem B4480721 : Blo 1989435 4480721 := bstep (se 2 (by rfl) ⟨1680270, by rfl⟩ : syracuseStep 4480721 = 3360541) B3360541
theorem B2987147 : Blo 1989435 2987147 := bstep (se 1 (by rfl) ⟨2240360, by rfl⟩ : syracuseStep 2987147 = 4480721) B4480721
theorem B1991431 : Blo 1989435 1991431 := bstep (se 1 (by rfl) ⟨1493573, by rfl⟩ : syracuseStep 1991431 = 2987147) B2987147
theorem B2240365 : Blo 1989435 2240365 := bbase (se 3 (by rfl) ⟨420068, by rfl⟩ : syracuseStep 2240365 = 840137) (by norm_num)
theorem B2987153 : Blo 1989435 2987153 := bstep (se 2 (by rfl) ⟨1120182, by rfl⟩ : syracuseStep 2987153 = 2240365) B2240365
theorem B1991435 : Blo 1989435 1991435 := bstep (se 1 (by rfl) ⟨1493576, by rfl⟩ : syracuseStep 1991435 = 2987153) B2987153
theorem C0 (j : ℕ) (h1 : 497358 ≤ j) (h2 : j ≤ 497858) : Blo 1989435 (4 * j + 3) := by
  interval_cases j
  · exact B1989435
  · exact B1989439
  · exact B1989443
  · exact B1989447
  · exact B1989451
  · exact B1989455
  · exact B1989459
  · exact B1989463
  · exact B1989467
  · exact B1989471
  · exact B1989475
  · exact B1989479
  · exact B1989483
  · exact B1989487
  · exact B1989491
  · exact B1989495
  · exact B1989499
  · exact B1989503
  · exact B1989507
  · exact B1989511
  · exact B1989515
  · exact B1989519
  · exact B1989523
  · exact B1989527
  · exact B1989531
  · exact B1989535
  · exact B1989539
  · exact B1989543
  · exact B1989547
  · exact B1989551
  · exact B1989555
  · exact B1989559
  · exact B1989563
  · exact B1989567
  · exact B1989571
  · exact B1989575
  · exact B1989579
  · exact B1989583
  · exact B1989587
  · exact B1989591
  · exact B1989595
  · exact B1989599
  · exact B1989603
  · exact B1989607
  · exact B1989611
  · exact B1989615
  · exact B1989619
  · exact B1989623
  · exact B1989627
  · exact B1989631
  · exact B1989635
  · exact B1989639
  · exact B1989643
  · exact B1989647
  · exact B1989651
  · exact B1989655
  · exact B1989659
  · exact B1989663
  · exact B1989667
  · exact B1989671
  · exact B1989675
  · exact B1989679
  · exact B1989683
  · exact B1989687
  · exact B1989691
  · exact B1989695
  · exact B1989699
  · exact B1989703
  · exact B1989707
  · exact B1989711
  · exact B1989715
  · exact B1989719
  · exact B1989723
  · exact B1989727
  · exact B1989731
  · exact B1989735
  · exact B1989739
  · exact B1989743
  · exact B1989747
  · exact B1989751
  · exact B1989755
  · exact B1989759
  · exact B1989763
  · exact B1989767
  · exact B1989771
  · exact B1989775
  · exact B1989779
  · exact B1989783
  · exact B1989787
  · exact B1989791
  · exact B1989795
  · exact B1989799
  · exact B1989803
  · exact B1989807
  · exact B1989811
  · exact B1989815
  · exact B1989819
  · exact B1989823
  · exact B1989827
  · exact B1989831
  · exact B1989835
  · exact B1989839
  · exact B1989843
  · exact B1989847
  · exact B1989851
  · exact B1989855
  · exact B1989859
  · exact B1989863
  · exact B1989867
  · exact B1989871
  · exact B1989875
  · exact B1989879
  · exact B1989883
  · exact B1989887
  · exact B1989891
  · exact B1989895
  · exact B1989899
  · exact B1989903
  · exact B1989907
  · exact B1989911
  · exact B1989915
  · exact B1989919
  · exact B1989923
  · exact B1989927
  · exact B1989931
  · exact B1989935
  · exact B1989939
  · exact B1989943
  · exact B1989947
  · exact B1989951
  · exact B1989955
  · exact B1989959
  · exact B1989963
  · exact B1989967
  · exact B1989971
  · exact B1989975
  · exact B1989979
  · exact B1989983
  · exact B1989987
  · exact B1989991
  · exact B1989995
  · exact B1989999
  · exact B1990003
  · exact B1990007
  · exact B1990011
  · exact B1990015
  · exact B1990019
  · exact B1990023
  · exact B1990027
  · exact B1990031
  · exact B1990035
  · exact B1990039
  · exact B1990043
  · exact B1990047
  · exact B1990051
  · exact B1990055
  · exact B1990059
  · exact B1990063
  · exact B1990067
  · exact B1990071
  · exact B1990075
  · exact B1990079
  · exact B1990083
  · exact B1990087
  · exact B1990091
  · exact B1990095
  · exact B1990099
  · exact B1990103
  · exact B1990107
  · exact B1990111
  · exact B1990115
  · exact B1990119
  · exact B1990123
  · exact B1990127
  · exact B1990131
  · exact B1990135
  · exact B1990139
  · exact B1990143
  · exact B1990147
  · exact B1990151
  · exact B1990155
  · exact B1990159
  · exact B1990163
  · exact B1990167
  · exact B1990171
  · exact B1990175
  · exact B1990179
  · exact B1990183
  · exact B1990187
  · exact B1990191
  · exact B1990195
  · exact B1990199
  · exact B1990203
  · exact B1990207
  · exact B1990211
  · exact B1990215
  · exact B1990219
  · exact B1990223
  · exact B1990227
  · exact B1990231
  · exact B1990235
  · exact B1990239
  · exact B1990243
  · exact B1990247
  · exact B1990251
  · exact B1990255
  · exact B1990259
  · exact B1990263
  · exact B1990267
  · exact B1990271
  · exact B1990275
  · exact B1990279
  · exact B1990283
  · exact B1990287
  · exact B1990291
  · exact B1990295
  · exact B1990299
  · exact B1990303
  · exact B1990307
  · exact B1990311
  · exact B1990315
  · exact B1990319
  · exact B1990323
  · exact B1990327
  · exact B1990331
  · exact B1990335
  · exact B1990339
  · exact B1990343
  · exact B1990347
  · exact B1990351
  · exact B1990355
  · exact B1990359
  · exact B1990363
  · exact B1990367
  · exact B1990371
  · exact B1990375
  · exact B1990379
  · exact B1990383
  · exact B1990387
  · exact B1990391
  · exact B1990395
  · exact B1990399
  · exact B1990403
  · exact B1990407
  · exact B1990411
  · exact B1990415
  · exact B1990419
  · exact B1990423
  · exact B1990427
  · exact B1990431
  · exact B1990435
  · exact B1990439
  · exact B1990443
  · exact B1990447
  · exact B1990451
  · exact B1990455
  · exact B1990459
  · exact B1990463
  · exact B1990467
  · exact B1990471
  · exact B1990475
  · exact B1990479
  · exact B1990483
  · exact B1990487
  · exact B1990491
  · exact B1990495
  · exact B1990499
  · exact B1990503
  · exact B1990507
  · exact B1990511
  · exact B1990515
  · exact B1990519
  · exact B1990523
  · exact B1990527
  · exact B1990531
  · exact B1990535
  · exact B1990539
  · exact B1990543
  · exact B1990547
  · exact B1990551
  · exact B1990555
  · exact B1990559
  · exact B1990563
  · exact B1990567
  · exact B1990571
  · exact B1990575
  · exact B1990579
  · exact B1990583
  · exact B1990587
  · exact B1990591
  · exact B1990595
  · exact B1990599
  · exact B1990603
  · exact B1990607
  · exact B1990611
  · exact B1990615
  · exact B1990619
  · exact B1990623
  · exact B1990627
  · exact B1990631
  · exact B1990635
  · exact B1990639
  · exact B1990643
  · exact B1990647
  · exact B1990651
  · exact B1990655
  · exact B1990659
  · exact B1990663
  · exact B1990667
  · exact B1990671
  · exact B1990675
  · exact B1990679
  · exact B1990683
  · exact B1990687
  · exact B1990691
  · exact B1990695
  · exact B1990699
  · exact B1990703
  · exact B1990707
  · exact B1990711
  · exact B1990715
  · exact B1990719
  · exact B1990723
  · exact B1990727
  · exact B1990731
  · exact B1990735
  · exact B1990739
  · exact B1990743
  · exact B1990747
  · exact B1990751
  · exact B1990755
  · exact B1990759
  · exact B1990763
  · exact B1990767
  · exact B1990771
  · exact B1990775
  · exact B1990779
  · exact B1990783
  · exact B1990787
  · exact B1990791
  · exact B1990795
  · exact B1990799
  · exact B1990803
  · exact B1990807
  · exact B1990811
  · exact B1990815
  · exact B1990819
  · exact B1990823
  · exact B1990827
  · exact B1990831
  · exact B1990835
  · exact B1990839
  · exact B1990843
  · exact B1990847
  · exact B1990851
  · exact B1990855
  · exact B1990859
  · exact B1990863
  · exact B1990867
  · exact B1990871
  · exact B1990875
  · exact B1990879
  · exact B1990883
  · exact B1990887
  · exact B1990891
  · exact B1990895
  · exact B1990899
  · exact B1990903
  · exact B1990907
  · exact B1990911
  · exact B1990915
  · exact B1990919
  · exact B1990923
  · exact B1990927
  · exact B1990931
  · exact B1990935
  · exact B1990939
  · exact B1990943
  · exact B1990947
  · exact B1990951
  · exact B1990955
  · exact B1990959
  · exact B1990963
  · exact B1990967
  · exact B1990971
  · exact B1990975
  · exact B1990979
  · exact B1990983
  · exact B1990987
  · exact B1990991
  · exact B1990995
  · exact B1990999
  · exact B1991003
  · exact B1991007
  · exact B1991011
  · exact B1991015
  · exact B1991019
  · exact B1991023
  · exact B1991027
  · exact B1991031
  · exact B1991035
  · exact B1991039
  · exact B1991043
  · exact B1991047
  · exact B1991051
  · exact B1991055
  · exact B1991059
  · exact B1991063
  · exact B1991067
  · exact B1991071
  · exact B1991075
  · exact B1991079
  · exact B1991083
  · exact B1991087
  · exact B1991091
  · exact B1991095
  · exact B1991099
  · exact B1991103
  · exact B1991107
  · exact B1991111
  · exact B1991115
  · exact B1991119
  · exact B1991123
  · exact B1991127
  · exact B1991131
  · exact B1991135
  · exact B1991139
  · exact B1991143
  · exact B1991147
  · exact B1991151
  · exact B1991155
  · exact B1991159
  · exact B1991163
  · exact B1991167
  · exact B1991171
  · exact B1991175
  · exact B1991179
  · exact B1991183
  · exact B1991187
  · exact B1991191
  · exact B1991195
  · exact B1991199
  · exact B1991203
  · exact B1991207
  · exact B1991211
  · exact B1991215
  · exact B1991219
  · exact B1991223
  · exact B1991227
  · exact B1991231
  · exact B1991235
  · exact B1991239
  · exact B1991243
  · exact B1991247
  · exact B1991251
  · exact B1991255
  · exact B1991259
  · exact B1991263
  · exact B1991267
  · exact B1991271
  · exact B1991275
  · exact B1991279
  · exact B1991283
  · exact B1991287
  · exact B1991291
  · exact B1991295
  · exact B1991299
  · exact B1991303
  · exact B1991307
  · exact B1991311
  · exact B1991315
  · exact B1991319
  · exact B1991323
  · exact B1991327
  · exact B1991331
  · exact B1991335
  · exact B1991339
  · exact B1991343
  · exact B1991347
  · exact B1991351
  · exact B1991355
  · exact B1991359
  · exact B1991363
  · exact B1991367
  · exact B1991371
  · exact B1991375
  · exact B1991379
  · exact B1991383
  · exact B1991387
  · exact B1991391
  · exact B1991395
  · exact B1991399
  · exact B1991403
  · exact B1991407
  · exact B1991411
  · exact B1991415
  · exact B1991419
  · exact B1991423
  · exact B1991427
  · exact B1991431
  · exact B1991435
theorem solution (m : ℕ) (hlo : 1989435 ≤ m) (hhi : m ≤ 1991435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 497358 ≤ j := by omega
    have hj2 : j ≤ 497858 := by omega
    have hb : Blo 1989435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
