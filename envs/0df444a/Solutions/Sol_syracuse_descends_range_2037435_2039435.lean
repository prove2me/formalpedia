-- Prove2me | solution 1 for syracuse_descends_range_2037435_2039435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:12.78366+00:00
-- url     : https://prove2.me/submissions/67603e99-90f0-407d-89df-15d0ec1af10f

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

theorem B3438173 : Blo 2037435 3438173 := bbase (se 3 (by rfl) ⟨644657, by rfl⟩ : syracuseStep 3438173 = 1289315) (by norm_num)
theorem B2292115 : Blo 2037435 2292115 := bstep (se 1 (by rfl) ⟨1719086, by rfl⟩ : syracuseStep 2292115 = 3438173) B3438173
theorem B3056153 : Blo 2037435 3056153 := bstep (se 2 (by rfl) ⟨1146057, by rfl⟩ : syracuseStep 3056153 = 2292115) B2292115
theorem B2037435 : Blo 2037435 2037435 := bstep (se 1 (by rfl) ⟨1528076, by rfl⟩ : syracuseStep 2037435 = 3056153) B3056153
theorem B2447689 : Blo 2037435 2447689 := bbase (se 2 (by rfl) ⟨917883, by rfl⟩ : syracuseStep 2447689 = 1835767) (by norm_num)
theorem B3263585 : Blo 2037435 3263585 := bstep (se 2 (by rfl) ⟨1223844, by rfl⟩ : syracuseStep 3263585 = 2447689) B2447689
theorem B8702893 : Blo 2037435 8702893 := bstep (se 3 (by rfl) ⟨1631792, by rfl⟩ : syracuseStep 8702893 = 3263585) B3263585
theorem B11603857 : Blo 2037435 11603857 := bstep (se 2 (by rfl) ⟨4351446, by rfl⟩ : syracuseStep 11603857 = 8702893) B8702893
theorem B15471809 : Blo 2037435 15471809 := bstep (se 2 (by rfl) ⟨5801928, by rfl⟩ : syracuseStep 15471809 = 11603857) B11603857
theorem B10314539 : Blo 2037435 10314539 := bstep (se 1 (by rfl) ⟨7735904, by rfl⟩ : syracuseStep 10314539 = 15471809) B15471809
theorem B6876359 : Blo 2037435 6876359 := bstep (se 1 (by rfl) ⟨5157269, by rfl⟩ : syracuseStep 6876359 = 10314539) B10314539
theorem B4584239 : Blo 2037435 4584239 := bstep (se 1 (by rfl) ⟨3438179, by rfl⟩ : syracuseStep 4584239 = 6876359) B6876359
theorem B3056159 : Blo 2037435 3056159 := bstep (se 1 (by rfl) ⟨2292119, by rfl⟩ : syracuseStep 3056159 = 4584239) B4584239
theorem B2037439 : Blo 2037435 2037439 := bstep (se 1 (by rfl) ⟨1528079, by rfl⟩ : syracuseStep 2037439 = 3056159) B3056159
theorem B3056165 : Blo 2037435 3056165 := bbase (se 4 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 3056165 = 573031) (by norm_num)
theorem B2037443 : Blo 2037435 2037443 := bstep (se 1 (by rfl) ⟨1528082, by rfl⟩ : syracuseStep 2037443 = 3056165) B3056165
theorem B2578645 : Blo 2037435 2578645 := bbase (se 7 (by rfl) ⟨30218, by rfl⟩ : syracuseStep 2578645 = 60437) (by norm_num)
theorem B3438193 : Blo 2037435 3438193 := bstep (se 2 (by rfl) ⟨1289322, by rfl⟩ : syracuseStep 3438193 = 2578645) B2578645
theorem B4584257 : Blo 2037435 4584257 := bstep (se 2 (by rfl) ⟨1719096, by rfl⟩ : syracuseStep 4584257 = 3438193) B3438193
theorem B3056171 : Blo 2037435 3056171 := bstep (se 1 (by rfl) ⟨2292128, by rfl⟩ : syracuseStep 3056171 = 4584257) B4584257
theorem B2037447 : Blo 2037435 2037447 := bstep (se 1 (by rfl) ⟨1528085, by rfl⟩ : syracuseStep 2037447 = 3056171) B3056171
theorem B2292133 : Blo 2037435 2292133 := bbase (se 4 (by rfl) ⟨214887, by rfl⟩ : syracuseStep 2292133 = 429775) (by norm_num)
theorem B3056177 : Blo 2037435 3056177 := bstep (se 2 (by rfl) ⟨1146066, by rfl⟩ : syracuseStep 3056177 = 2292133) B2292133
theorem B2037451 : Blo 2037435 2037451 := bstep (se 1 (by rfl) ⟨1528088, by rfl⟩ : syracuseStep 2037451 = 3056177) B3056177
theorem B4130509 : Blo 2037435 4130509 := bbase (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) (by norm_num)
theorem B5507345 : Blo 2037435 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B3671563 : Blo 2037435 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B4895417 : Blo 2037435 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B13054445 : Blo 2037435 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B8702963 : Blo 2037435 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B5801975 : Blo 2037435 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B3867983 : Blo 2037435 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B2578655 : Blo 2037435 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B6876413 : Blo 2037435 6876413 := bstep (se 3 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 6876413 = 2578655) B2578655
theorem B4584275 : Blo 2037435 4584275 := bstep (se 1 (by rfl) ⟨3438206, by rfl⟩ : syracuseStep 4584275 = 6876413) B6876413
theorem B3056183 : Blo 2037435 3056183 := bstep (se 1 (by rfl) ⟨2292137, by rfl⟩ : syracuseStep 3056183 = 4584275) B4584275
theorem B2037455 : Blo 2037435 2037455 := bstep (se 1 (by rfl) ⟨1528091, by rfl⟩ : syracuseStep 2037455 = 3056183) B3056183
theorem B3056189 : Blo 2037435 3056189 := bbase (se 3 (by rfl) ⟨573035, by rfl⟩ : syracuseStep 3056189 = 1146071) (by norm_num)
theorem B2037459 : Blo 2037435 2037459 := bstep (se 1 (by rfl) ⟨1528094, by rfl⟩ : syracuseStep 2037459 = 3056189) B3056189
theorem B4584293 : Blo 2037435 4584293 := bbase (se 4 (by rfl) ⟨429777, by rfl⟩ : syracuseStep 4584293 = 859555) (by norm_num)
theorem B3056195 : Blo 2037435 3056195 := bstep (se 1 (by rfl) ⟨2292146, by rfl⟩ : syracuseStep 3056195 = 4584293) B4584293
theorem B2037463 : Blo 2037435 2037463 := bstep (se 1 (by rfl) ⟨1528097, by rfl⟩ : syracuseStep 2037463 = 3056195) B3056195
theorem B5157341 : Blo 2037435 5157341 := bbase (se 3 (by rfl) ⟨967001, by rfl⟩ : syracuseStep 5157341 = 1934003) (by norm_num)
theorem B3438227 : Blo 2037435 3438227 := bstep (se 1 (by rfl) ⟨2578670, by rfl⟩ : syracuseStep 3438227 = 5157341) B5157341
theorem B2292151 : Blo 2037435 2292151 := bstep (se 1 (by rfl) ⟨1719113, by rfl⟩ : syracuseStep 2292151 = 3438227) B3438227
theorem B3056201 : Blo 2037435 3056201 := bstep (se 2 (by rfl) ⟨1146075, by rfl⟩ : syracuseStep 3056201 = 2292151) B2292151
theorem B2037467 : Blo 2037435 2037467 := bstep (se 1 (by rfl) ⟨1528100, by rfl⟩ : syracuseStep 2037467 = 3056201) B3056201
theorem B3868013 : Blo 2037435 3868013 := bbase (se 3 (by rfl) ⟨725252, by rfl⟩ : syracuseStep 3868013 = 1450505) (by norm_num)
theorem B10314701 : Blo 2037435 10314701 := bstep (se 3 (by rfl) ⟨1934006, by rfl⟩ : syracuseStep 10314701 = 3868013) B3868013
theorem B6876467 : Blo 2037435 6876467 := bstep (se 1 (by rfl) ⟨5157350, by rfl⟩ : syracuseStep 6876467 = 10314701) B10314701
theorem B4584311 : Blo 2037435 4584311 := bstep (se 1 (by rfl) ⟨3438233, by rfl⟩ : syracuseStep 4584311 = 6876467) B6876467
theorem B3056207 : Blo 2037435 3056207 := bstep (se 1 (by rfl) ⟨2292155, by rfl⟩ : syracuseStep 3056207 = 4584311) B4584311
theorem B2037471 : Blo 2037435 2037471 := bstep (se 1 (by rfl) ⟨1528103, by rfl⟩ : syracuseStep 2037471 = 3056207) B3056207
theorem B3056213 : Blo 2037435 3056213 := bbase (se 8 (by rfl) ⟨17907, by rfl⟩ : syracuseStep 3056213 = 35815) (by norm_num)
theorem B2037475 : Blo 2037435 2037475 := bstep (se 1 (by rfl) ⟨1528106, by rfl⟩ : syracuseStep 2037475 = 3056213) B3056213
theorem B9790949 : Blo 2037435 9790949 := bbase (se 4 (by rfl) ⟨917901, by rfl⟩ : syracuseStep 9790949 = 1835803) (by norm_num)
theorem B6527299 : Blo 2037435 6527299 := bstep (se 1 (by rfl) ⟨4895474, by rfl⟩ : syracuseStep 6527299 = 9790949) B9790949
theorem B8703065 : Blo 2037435 8703065 := bstep (se 2 (by rfl) ⟨3263649, by rfl⟩ : syracuseStep 8703065 = 6527299) B6527299
theorem B5802043 : Blo 2037435 5802043 := bstep (se 1 (by rfl) ⟨4351532, by rfl⟩ : syracuseStep 5802043 = 8703065) B8703065
theorem B7736057 : Blo 2037435 7736057 := bstep (se 2 (by rfl) ⟨2901021, by rfl⟩ : syracuseStep 7736057 = 5802043) B5802043
theorem B5157371 : Blo 2037435 5157371 := bstep (se 1 (by rfl) ⟨3868028, by rfl⟩ : syracuseStep 5157371 = 7736057) B7736057
theorem B3438247 : Blo 2037435 3438247 := bstep (se 1 (by rfl) ⟨2578685, by rfl⟩ : syracuseStep 3438247 = 5157371) B5157371
theorem B4584329 : Blo 2037435 4584329 := bstep (se 2 (by rfl) ⟨1719123, by rfl⟩ : syracuseStep 4584329 = 3438247) B3438247
theorem B3056219 : Blo 2037435 3056219 := bstep (se 1 (by rfl) ⟨2292164, by rfl⟩ : syracuseStep 3056219 = 4584329) B4584329
theorem B2037479 : Blo 2037435 2037479 := bstep (se 1 (by rfl) ⟨1528109, by rfl⟩ : syracuseStep 2037479 = 3056219) B3056219
theorem B2292169 : Blo 2037435 2292169 := bbase (se 2 (by rfl) ⟨859563, by rfl⟩ : syracuseStep 2292169 = 1719127) (by norm_num)
theorem B3056225 : Blo 2037435 3056225 := bstep (se 2 (by rfl) ⟨1146084, by rfl⟩ : syracuseStep 3056225 = 2292169) B2292169
theorem B2037483 : Blo 2037435 2037483 := bstep (se 1 (by rfl) ⟨1528112, by rfl⟩ : syracuseStep 2037483 = 3056225) B3056225
theorem B17406197 : Blo 2037435 17406197 := bbase (se 5 (by rfl) ⟨815915, by rfl⟩ : syracuseStep 17406197 = 1631831) (by norm_num)
theorem B11604131 : Blo 2037435 11604131 := bstep (se 1 (by rfl) ⟨8703098, by rfl⟩ : syracuseStep 11604131 = 17406197) B17406197
theorem B7736087 : Blo 2037435 7736087 := bstep (se 1 (by rfl) ⟨5802065, by rfl⟩ : syracuseStep 7736087 = 11604131) B11604131
theorem B5157391 : Blo 2037435 5157391 := bstep (se 1 (by rfl) ⟨3868043, by rfl⟩ : syracuseStep 5157391 = 7736087) B7736087
theorem B6876521 : Blo 2037435 6876521 := bstep (se 2 (by rfl) ⟨2578695, by rfl⟩ : syracuseStep 6876521 = 5157391) B5157391
theorem B4584347 : Blo 2037435 4584347 := bstep (se 1 (by rfl) ⟨3438260, by rfl⟩ : syracuseStep 4584347 = 6876521) B6876521
theorem B3056231 : Blo 2037435 3056231 := bstep (se 1 (by rfl) ⟨2292173, by rfl⟩ : syracuseStep 3056231 = 4584347) B4584347
theorem B2037487 : Blo 2037435 2037487 := bstep (se 1 (by rfl) ⟨1528115, by rfl⟩ : syracuseStep 2037487 = 3056231) B3056231
theorem B3056237 : Blo 2037435 3056237 := bbase (se 3 (by rfl) ⟨573044, by rfl⟩ : syracuseStep 3056237 = 1146089) (by norm_num)
theorem B2037491 : Blo 2037435 2037491 := bstep (se 1 (by rfl) ⟨1528118, by rfl⟩ : syracuseStep 2037491 = 3056237) B3056237
theorem B4584365 : Blo 2037435 4584365 := bbase (se 3 (by rfl) ⟨859568, by rfl⟩ : syracuseStep 4584365 = 1719137) (by norm_num)
theorem B3056243 : Blo 2037435 3056243 := bstep (se 1 (by rfl) ⟨2292182, by rfl⟩ : syracuseStep 3056243 = 4584365) B4584365
theorem B2037495 : Blo 2037435 2037495 := bstep (se 1 (by rfl) ⟨1528121, by rfl⟩ : syracuseStep 2037495 = 3056243) B3056243
theorem B5802101 : Blo 2037435 5802101 := bbase (se 5 (by rfl) ⟨271973, by rfl⟩ : syracuseStep 5802101 = 543947) (by norm_num)
theorem B3868067 : Blo 2037435 3868067 := bstep (se 1 (by rfl) ⟨2901050, by rfl⟩ : syracuseStep 3868067 = 5802101) B5802101
theorem B2578711 : Blo 2037435 2578711 := bstep (se 1 (by rfl) ⟨1934033, by rfl⟩ : syracuseStep 2578711 = 3868067) B3868067
theorem B3438281 : Blo 2037435 3438281 := bstep (se 2 (by rfl) ⟨1289355, by rfl⟩ : syracuseStep 3438281 = 2578711) B2578711
theorem B2292187 : Blo 2037435 2292187 := bstep (se 1 (by rfl) ⟨1719140, by rfl⟩ : syracuseStep 2292187 = 3438281) B3438281
theorem B3056249 : Blo 2037435 3056249 := bstep (se 2 (by rfl) ⟨1146093, by rfl⟩ : syracuseStep 3056249 = 2292187) B2292187
theorem B2037499 : Blo 2037435 2037499 := bstep (se 1 (by rfl) ⟨1528124, by rfl⟩ : syracuseStep 2037499 = 3056249) B3056249
theorem B9293861 : Blo 2037435 9293861 := bbase (se 4 (by rfl) ⟨871299, by rfl⟩ : syracuseStep 9293861 = 1742599) (by norm_num)
theorem B6195907 : Blo 2037435 6195907 := bstep (se 1 (by rfl) ⟨4646930, by rfl⟩ : syracuseStep 6195907 = 9293861) B9293861
theorem B8261209 : Blo 2037435 8261209 := bstep (se 2 (by rfl) ⟨3097953, by rfl⟩ : syracuseStep 8261209 = 6195907) B6195907
theorem B44059781 : Blo 2037435 44059781 := bstep (se 4 (by rfl) ⟨4130604, by rfl⟩ : syracuseStep 44059781 = 8261209) B8261209
theorem B29373187 : Blo 2037435 29373187 := bstep (se 1 (by rfl) ⟨22029890, by rfl⟩ : syracuseStep 29373187 = 44059781) B44059781
theorem B39164249 : Blo 2037435 39164249 := bstep (se 2 (by rfl) ⟨14686593, by rfl⟩ : syracuseStep 39164249 = 29373187) B29373187
theorem B26109499 : Blo 2037435 26109499 := bstep (se 1 (by rfl) ⟨19582124, by rfl⟩ : syracuseStep 26109499 = 39164249) B39164249
theorem B34812665 : Blo 2037435 34812665 := bstep (se 2 (by rfl) ⟨13054749, by rfl⟩ : syracuseStep 34812665 = 26109499) B26109499
theorem B23208443 : Blo 2037435 23208443 := bstep (se 1 (by rfl) ⟨17406332, by rfl⟩ : syracuseStep 23208443 = 34812665) B34812665
theorem B15472295 : Blo 2037435 15472295 := bstep (se 1 (by rfl) ⟨11604221, by rfl⟩ : syracuseStep 15472295 = 23208443) B23208443
theorem B10314863 : Blo 2037435 10314863 := bstep (se 1 (by rfl) ⟨7736147, by rfl⟩ : syracuseStep 10314863 = 15472295) B15472295
theorem B6876575 : Blo 2037435 6876575 := bstep (se 1 (by rfl) ⟨5157431, by rfl⟩ : syracuseStep 6876575 = 10314863) B10314863
theorem B4584383 : Blo 2037435 4584383 := bstep (se 1 (by rfl) ⟨3438287, by rfl⟩ : syracuseStep 4584383 = 6876575) B6876575
theorem B3056255 : Blo 2037435 3056255 := bstep (se 1 (by rfl) ⟨2292191, by rfl⟩ : syracuseStep 3056255 = 4584383) B4584383
theorem B2037503 : Blo 2037435 2037503 := bstep (se 1 (by rfl) ⟨1528127, by rfl⟩ : syracuseStep 2037503 = 3056255) B3056255
theorem B3056261 : Blo 2037435 3056261 := bbase (se 4 (by rfl) ⟨286524, by rfl⟩ : syracuseStep 3056261 = 573049) (by norm_num)
theorem B2037507 : Blo 2037435 2037507 := bstep (se 1 (by rfl) ⟨1528130, by rfl⟩ : syracuseStep 2037507 = 3056261) B3056261
theorem B3438301 : Blo 2037435 3438301 := bbase (se 3 (by rfl) ⟨644681, by rfl⟩ : syracuseStep 3438301 = 1289363) (by norm_num)
theorem B4584401 : Blo 2037435 4584401 := bstep (se 2 (by rfl) ⟨1719150, by rfl⟩ : syracuseStep 4584401 = 3438301) B3438301
theorem B3056267 : Blo 2037435 3056267 := bstep (se 1 (by rfl) ⟨2292200, by rfl⟩ : syracuseStep 3056267 = 4584401) B4584401
theorem B2037511 : Blo 2037435 2037511 := bstep (se 1 (by rfl) ⟨1528133, by rfl⟩ : syracuseStep 2037511 = 3056267) B3056267
theorem B2292205 : Blo 2037435 2292205 := bbase (se 3 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 2292205 = 859577) (by norm_num)
theorem B3056273 : Blo 2037435 3056273 := bstep (se 2 (by rfl) ⟨1146102, by rfl⟩ : syracuseStep 3056273 = 2292205) B2292205
theorem B2037515 : Blo 2037435 2037515 := bstep (se 1 (by rfl) ⟨1528136, by rfl⟩ : syracuseStep 2037515 = 3056273) B3056273
theorem B6876629 : Blo 2037435 6876629 := bbase (se 7 (by rfl) ⟨80585, by rfl⟩ : syracuseStep 6876629 = 161171) (by norm_num)
theorem B4584419 : Blo 2037435 4584419 := bstep (se 1 (by rfl) ⟨3438314, by rfl⟩ : syracuseStep 4584419 = 6876629) B6876629
theorem B3056279 : Blo 2037435 3056279 := bstep (se 1 (by rfl) ⟨2292209, by rfl⟩ : syracuseStep 3056279 = 4584419) B4584419
theorem B2037519 : Blo 2037435 2037519 := bstep (se 1 (by rfl) ⟨1528139, by rfl⟩ : syracuseStep 2037519 = 3056279) B3056279
theorem B3056285 : Blo 2037435 3056285 := bbase (se 3 (by rfl) ⟨573053, by rfl⟩ : syracuseStep 3056285 = 1146107) (by norm_num)
theorem B2037523 : Blo 2037435 2037523 := bstep (se 1 (by rfl) ⟨1528142, by rfl⟩ : syracuseStep 2037523 = 3056285) B3056285
theorem B4584437 : Blo 2037435 4584437 := bbase (se 5 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 4584437 = 429791) (by norm_num)
theorem B3056291 : Blo 2037435 3056291 := bstep (se 1 (by rfl) ⟨2292218, by rfl⟩ : syracuseStep 3056291 = 4584437) B4584437
theorem B2037527 : Blo 2037435 2037527 := bstep (se 1 (by rfl) ⟨1528145, by rfl⟩ : syracuseStep 2037527 = 3056291) B3056291
theorem B83645909 : Blo 2037435 83645909 := bbase (se 7 (by rfl) ⟨980225, by rfl⟩ : syracuseStep 83645909 = 1960451) (by norm_num)
theorem B55763939 : Blo 2037435 55763939 := bstep (se 1 (by rfl) ⟨41822954, by rfl⟩ : syracuseStep 55763939 = 83645909) B83645909
theorem B37175959 : Blo 2037435 37175959 := bstep (se 1 (by rfl) ⟨27881969, by rfl⟩ : syracuseStep 37175959 = 55763939) B55763939
theorem B49567945 : Blo 2037435 49567945 := bstep (se 2 (by rfl) ⟨18587979, by rfl⟩ : syracuseStep 49567945 = 37175959) B37175959
theorem B66090593 : Blo 2037435 66090593 := bstep (se 2 (by rfl) ⟨24783972, by rfl⟩ : syracuseStep 66090593 = 49567945) B49567945
theorem B44060395 : Blo 2037435 44060395 := bstep (se 1 (by rfl) ⟨33045296, by rfl⟩ : syracuseStep 44060395 = 66090593) B66090593
theorem B58747193 : Blo 2037435 58747193 := bstep (se 2 (by rfl) ⟨22030197, by rfl⟩ : syracuseStep 58747193 = 44060395) B44060395
theorem B39164795 : Blo 2037435 39164795 := bstep (se 1 (by rfl) ⟨29373596, by rfl⟩ : syracuseStep 39164795 = 58747193) B58747193
theorem B26109863 : Blo 2037435 26109863 := bstep (se 1 (by rfl) ⟨19582397, by rfl⟩ : syracuseStep 26109863 = 39164795) B39164795
theorem B17406575 : Blo 2037435 17406575 := bstep (se 1 (by rfl) ⟨13054931, by rfl⟩ : syracuseStep 17406575 = 26109863) B26109863
theorem B11604383 : Blo 2037435 11604383 := bstep (se 1 (by rfl) ⟨8703287, by rfl⟩ : syracuseStep 11604383 = 17406575) B17406575
theorem B7736255 : Blo 2037435 7736255 := bstep (se 1 (by rfl) ⟨5802191, by rfl⟩ : syracuseStep 7736255 = 11604383) B11604383
theorem B5157503 : Blo 2037435 5157503 := bstep (se 1 (by rfl) ⟨3868127, by rfl⟩ : syracuseStep 5157503 = 7736255) B7736255
theorem B3438335 : Blo 2037435 3438335 := bstep (se 1 (by rfl) ⟨2578751, by rfl⟩ : syracuseStep 3438335 = 5157503) B5157503
theorem B2292223 : Blo 2037435 2292223 := bstep (se 1 (by rfl) ⟨1719167, by rfl⟩ : syracuseStep 2292223 = 3438335) B3438335
theorem B3056297 : Blo 2037435 3056297 := bstep (se 2 (by rfl) ⟨1146111, by rfl⟩ : syracuseStep 3056297 = 2292223) B2292223
theorem B2037531 : Blo 2037435 2037531 := bstep (se 1 (by rfl) ⟨1528148, by rfl⟩ : syracuseStep 2037531 = 3056297) B3056297
theorem B2901101 : Blo 2037435 2901101 := bbase (se 3 (by rfl) ⟨543956, by rfl⟩ : syracuseStep 2901101 = 1087913) (by norm_num)
theorem B7736269 : Blo 2037435 7736269 := bstep (se 3 (by rfl) ⟨1450550, by rfl⟩ : syracuseStep 7736269 = 2901101) B2901101
theorem B10315025 : Blo 2037435 10315025 := bstep (se 2 (by rfl) ⟨3868134, by rfl⟩ : syracuseStep 10315025 = 7736269) B7736269
theorem B6876683 : Blo 2037435 6876683 := bstep (se 1 (by rfl) ⟨5157512, by rfl⟩ : syracuseStep 6876683 = 10315025) B10315025
theorem B4584455 : Blo 2037435 4584455 := bstep (se 1 (by rfl) ⟨3438341, by rfl⟩ : syracuseStep 4584455 = 6876683) B6876683
theorem B3056303 : Blo 2037435 3056303 := bstep (se 1 (by rfl) ⟨2292227, by rfl⟩ : syracuseStep 3056303 = 4584455) B4584455
theorem B2037535 : Blo 2037435 2037535 := bstep (se 1 (by rfl) ⟨1528151, by rfl⟩ : syracuseStep 2037535 = 3056303) B3056303
theorem B3056309 : Blo 2037435 3056309 := bbase (se 5 (by rfl) ⟨143264, by rfl⟩ : syracuseStep 3056309 = 286529) (by norm_num)
theorem B2037539 : Blo 2037435 2037539 := bstep (se 1 (by rfl) ⟨1528154, by rfl⟩ : syracuseStep 2037539 = 3056309) B3056309
theorem B5157533 : Blo 2037435 5157533 := bbase (se 3 (by rfl) ⟨967037, by rfl⟩ : syracuseStep 5157533 = 1934075) (by norm_num)
theorem B3438355 : Blo 2037435 3438355 := bstep (se 1 (by rfl) ⟨2578766, by rfl⟩ : syracuseStep 3438355 = 5157533) B5157533
theorem B4584473 : Blo 2037435 4584473 := bstep (se 2 (by rfl) ⟨1719177, by rfl⟩ : syracuseStep 4584473 = 3438355) B3438355
theorem B3056315 : Blo 2037435 3056315 := bstep (se 1 (by rfl) ⟨2292236, by rfl⟩ : syracuseStep 3056315 = 4584473) B4584473
theorem B2037543 : Blo 2037435 2037543 := bstep (se 1 (by rfl) ⟨1528157, by rfl⟩ : syracuseStep 2037543 = 3056315) B3056315
theorem B2292241 : Blo 2037435 2292241 := bbase (se 2 (by rfl) ⟨859590, by rfl⟩ : syracuseStep 2292241 = 1719181) (by norm_num)
theorem B3056321 : Blo 2037435 3056321 := bstep (se 2 (by rfl) ⟨1146120, by rfl⟩ : syracuseStep 3056321 = 2292241) B2292241
theorem B2037547 : Blo 2037435 2037547 := bstep (se 1 (by rfl) ⟨1528160, by rfl⟩ : syracuseStep 2037547 = 3056321) B3056321
theorem B3868165 : Blo 2037435 3868165 := bbase (se 4 (by rfl) ⟨362640, by rfl⟩ : syracuseStep 3868165 = 725281) (by norm_num)
theorem B5157553 : Blo 2037435 5157553 := bstep (se 2 (by rfl) ⟨1934082, by rfl⟩ : syracuseStep 5157553 = 3868165) B3868165
theorem B6876737 : Blo 2037435 6876737 := bstep (se 2 (by rfl) ⟨2578776, by rfl⟩ : syracuseStep 6876737 = 5157553) B5157553
theorem B4584491 : Blo 2037435 4584491 := bstep (se 1 (by rfl) ⟨3438368, by rfl⟩ : syracuseStep 4584491 = 6876737) B6876737
theorem B3056327 : Blo 2037435 3056327 := bstep (se 1 (by rfl) ⟨2292245, by rfl⟩ : syracuseStep 3056327 = 4584491) B4584491
theorem B2037551 : Blo 2037435 2037551 := bstep (se 1 (by rfl) ⟨1528163, by rfl⟩ : syracuseStep 2037551 = 3056327) B3056327
theorem B3056333 : Blo 2037435 3056333 := bbase (se 3 (by rfl) ⟨573062, by rfl⟩ : syracuseStep 3056333 = 1146125) (by norm_num)
theorem B2037555 : Blo 2037435 2037555 := bstep (se 1 (by rfl) ⟨1528166, by rfl⟩ : syracuseStep 2037555 = 3056333) B3056333
theorem B4584509 : Blo 2037435 4584509 := bbase (se 3 (by rfl) ⟨859595, by rfl⟩ : syracuseStep 4584509 = 1719191) (by norm_num)
theorem B3056339 : Blo 2037435 3056339 := bstep (se 1 (by rfl) ⟨2292254, by rfl⟩ : syracuseStep 3056339 = 4584509) B4584509
theorem B2037559 : Blo 2037435 2037559 := bstep (se 1 (by rfl) ⟨1528169, by rfl⟩ : syracuseStep 2037559 = 3056339) B3056339
theorem B3438389 : Blo 2037435 3438389 := bbase (se 5 (by rfl) ⟨161174, by rfl⟩ : syracuseStep 3438389 = 322349) (by norm_num)
theorem B2292259 : Blo 2037435 2292259 := bstep (se 1 (by rfl) ⟨1719194, by rfl⟩ : syracuseStep 2292259 = 3438389) B3438389
theorem B3056345 : Blo 2037435 3056345 := bstep (se 2 (by rfl) ⟨1146129, by rfl⟩ : syracuseStep 3056345 = 2292259) B2292259
theorem B2037563 : Blo 2037435 2037563 := bstep (se 1 (by rfl) ⟨1528172, by rfl⟩ : syracuseStep 2037563 = 3056345) B3056345
theorem B5802293 : Blo 2037435 5802293 := bbase (se 5 (by rfl) ⟨271982, by rfl⟩ : syracuseStep 5802293 = 543965) (by norm_num)
theorem B15472781 : Blo 2037435 15472781 := bstep (se 3 (by rfl) ⟨2901146, by rfl⟩ : syracuseStep 15472781 = 5802293) B5802293
theorem B10315187 : Blo 2037435 10315187 := bstep (se 1 (by rfl) ⟨7736390, by rfl⟩ : syracuseStep 10315187 = 15472781) B15472781
theorem B6876791 : Blo 2037435 6876791 := bstep (se 1 (by rfl) ⟨5157593, by rfl⟩ : syracuseStep 6876791 = 10315187) B10315187
theorem B4584527 : Blo 2037435 4584527 := bstep (se 1 (by rfl) ⟨3438395, by rfl⟩ : syracuseStep 4584527 = 6876791) B6876791
theorem B3056351 : Blo 2037435 3056351 := bstep (se 1 (by rfl) ⟨2292263, by rfl⟩ : syracuseStep 3056351 = 4584527) B4584527
theorem B2037567 : Blo 2037435 2037567 := bstep (se 1 (by rfl) ⟨1528175, by rfl⟩ : syracuseStep 2037567 = 3056351) B3056351
theorem B3056357 : Blo 2037435 3056357 := bbase (se 4 (by rfl) ⟨286533, by rfl⟩ : syracuseStep 3056357 = 573067) (by norm_num)
theorem B2037571 : Blo 2037435 2037571 := bstep (se 1 (by rfl) ⟨1528178, by rfl⟩ : syracuseStep 2037571 = 3056357) B3056357
theorem B2175869 : Blo 2037435 2175869 := bbase (se 3 (by rfl) ⟨407975, by rfl⟩ : syracuseStep 2175869 = 815951) (by norm_num)
theorem B5802317 : Blo 2037435 5802317 := bstep (se 3 (by rfl) ⟨1087934, by rfl⟩ : syracuseStep 5802317 = 2175869) B2175869
theorem B3868211 : Blo 2037435 3868211 := bstep (se 1 (by rfl) ⟨2901158, by rfl⟩ : syracuseStep 3868211 = 5802317) B5802317
theorem B2578807 : Blo 2037435 2578807 := bstep (se 1 (by rfl) ⟨1934105, by rfl⟩ : syracuseStep 2578807 = 3868211) B3868211
theorem B3438409 : Blo 2037435 3438409 := bstep (se 2 (by rfl) ⟨1289403, by rfl⟩ : syracuseStep 3438409 = 2578807) B2578807
theorem B4584545 : Blo 2037435 4584545 := bstep (se 2 (by rfl) ⟨1719204, by rfl⟩ : syracuseStep 4584545 = 3438409) B3438409
theorem B3056363 : Blo 2037435 3056363 := bstep (se 1 (by rfl) ⟨2292272, by rfl⟩ : syracuseStep 3056363 = 4584545) B4584545
theorem B2037575 : Blo 2037435 2037575 := bstep (se 1 (by rfl) ⟨1528181, by rfl⟩ : syracuseStep 2037575 = 3056363) B3056363
theorem B2292277 : Blo 2037435 2292277 := bbase (se 5 (by rfl) ⟨107450, by rfl⟩ : syracuseStep 2292277 = 214901) (by norm_num)
theorem B3056369 : Blo 2037435 3056369 := bstep (se 2 (by rfl) ⟨1146138, by rfl⟩ : syracuseStep 3056369 = 2292277) B2292277
theorem B2037579 : Blo 2037435 2037579 := bstep (se 1 (by rfl) ⟨1528184, by rfl⟩ : syracuseStep 2037579 = 3056369) B3056369
theorem B2578817 : Blo 2037435 2578817 := bbase (se 2 (by rfl) ⟨967056, by rfl⟩ : syracuseStep 2578817 = 1934113) (by norm_num)
theorem B6876845 : Blo 2037435 6876845 := bstep (se 3 (by rfl) ⟨1289408, by rfl⟩ : syracuseStep 6876845 = 2578817) B2578817
theorem B4584563 : Blo 2037435 4584563 := bstep (se 1 (by rfl) ⟨3438422, by rfl⟩ : syracuseStep 4584563 = 6876845) B6876845
theorem B3056375 : Blo 2037435 3056375 := bstep (se 1 (by rfl) ⟨2292281, by rfl⟩ : syracuseStep 3056375 = 4584563) B4584563
theorem B2037583 : Blo 2037435 2037583 := bstep (se 1 (by rfl) ⟨1528187, by rfl⟩ : syracuseStep 2037583 = 3056375) B3056375
theorem B3056381 : Blo 2037435 3056381 := bbase (se 3 (by rfl) ⟨573071, by rfl⟩ : syracuseStep 3056381 = 1146143) (by norm_num)
theorem B2037587 : Blo 2037435 2037587 := bstep (se 1 (by rfl) ⟨1528190, by rfl⟩ : syracuseStep 2037587 = 3056381) B3056381
theorem B4584581 : Blo 2037435 4584581 := bbase (se 4 (by rfl) ⟨429804, by rfl⟩ : syracuseStep 4584581 = 859609) (by norm_num)
theorem B3056387 : Blo 2037435 3056387 := bstep (se 1 (by rfl) ⟨2292290, by rfl⟩ : syracuseStep 3056387 = 4584581) B4584581
theorem B2037591 : Blo 2037435 2037591 := bstep (se 1 (by rfl) ⟨1528193, by rfl⟩ : syracuseStep 2037591 = 3056387) B3056387
theorem B4351781 : Blo 2037435 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B2901187 : Blo 2037435 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B3868249 : Blo 2037435 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B5157665 : Blo 2037435 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B3438443 : Blo 2037435 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B2292295 : Blo 2037435 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B3056393 : Blo 2037435 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B2037595 : Blo 2037435 2037595 := bstep (se 1 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 2037595 = 3056393) B3056393
theorem B10315349 : Blo 2037435 10315349 := bbase (se 8 (by rfl) ⟨60441, by rfl⟩ : syracuseStep 10315349 = 120883) (by norm_num)
theorem B6876899 : Blo 2037435 6876899 := bstep (se 1 (by rfl) ⟨5157674, by rfl⟩ : syracuseStep 6876899 = 10315349) B10315349
theorem B4584599 : Blo 2037435 4584599 := bstep (se 1 (by rfl) ⟨3438449, by rfl⟩ : syracuseStep 4584599 = 6876899) B6876899
theorem B3056399 : Blo 2037435 3056399 := bstep (se 1 (by rfl) ⟨2292299, by rfl⟩ : syracuseStep 3056399 = 4584599) B4584599
theorem B2037599 : Blo 2037435 2037599 := bstep (se 1 (by rfl) ⟨1528199, by rfl⟩ : syracuseStep 2037599 = 3056399) B3056399
theorem B3056405 : Blo 2037435 3056405 := bbase (se 6 (by rfl) ⟨71634, by rfl⟩ : syracuseStep 3056405 = 143269) (by norm_num)
theorem B2037603 : Blo 2037435 2037603 := bstep (se 1 (by rfl) ⟨1528202, by rfl⟩ : syracuseStep 2037603 = 3056405) B3056405
theorem B11015509 : Blo 2037435 11015509 := bbase (se 14 (by rfl) ⟨1008, by rfl⟩ : syracuseStep 11015509 = 2017) (by norm_num)
theorem B14687345 : Blo 2037435 14687345 := bstep (se 2 (by rfl) ⟨5507754, by rfl⟩ : syracuseStep 14687345 = 11015509) B11015509
theorem B39166253 : Blo 2037435 39166253 := bstep (se 3 (by rfl) ⟨7343672, by rfl⟩ : syracuseStep 39166253 = 14687345) B14687345
theorem B26110835 : Blo 2037435 26110835 := bstep (se 1 (by rfl) ⟨19583126, by rfl⟩ : syracuseStep 26110835 = 39166253) B39166253
theorem B17407223 : Blo 2037435 17407223 := bstep (se 1 (by rfl) ⟨13055417, by rfl⟩ : syracuseStep 17407223 = 26110835) B26110835
theorem B11604815 : Blo 2037435 11604815 := bstep (se 1 (by rfl) ⟨8703611, by rfl⟩ : syracuseStep 11604815 = 17407223) B17407223
theorem B7736543 : Blo 2037435 7736543 := bstep (se 1 (by rfl) ⟨5802407, by rfl⟩ : syracuseStep 7736543 = 11604815) B11604815
theorem B5157695 : Blo 2037435 5157695 := bstep (se 1 (by rfl) ⟨3868271, by rfl⟩ : syracuseStep 5157695 = 7736543) B7736543
theorem B3438463 : Blo 2037435 3438463 := bstep (se 1 (by rfl) ⟨2578847, by rfl⟩ : syracuseStep 3438463 = 5157695) B5157695
theorem B4584617 : Blo 2037435 4584617 := bstep (se 2 (by rfl) ⟨1719231, by rfl⟩ : syracuseStep 4584617 = 3438463) B3438463
theorem B3056411 : Blo 2037435 3056411 := bstep (se 1 (by rfl) ⟨2292308, by rfl⟩ : syracuseStep 3056411 = 4584617) B4584617
theorem B2037607 : Blo 2037435 2037607 := bstep (se 1 (by rfl) ⟨1528205, by rfl⟩ : syracuseStep 2037607 = 3056411) B3056411
theorem B2292313 : Blo 2037435 2292313 := bbase (se 2 (by rfl) ⟨859617, by rfl⟩ : syracuseStep 2292313 = 1719235) (by norm_num)
theorem B3056417 : Blo 2037435 3056417 := bstep (se 2 (by rfl) ⟨1146156, by rfl⟩ : syracuseStep 3056417 = 2292313) B2292313
theorem B2037611 : Blo 2037435 2037611 := bstep (se 1 (by rfl) ⟨1528208, by rfl⟩ : syracuseStep 2037611 = 3056417) B3056417
theorem B3098125 : Blo 2037435 3098125 := bbase (se 3 (by rfl) ⟨580898, by rfl⟩ : syracuseStep 3098125 = 1161797) (by norm_num)
theorem B4130833 : Blo 2037435 4130833 := bstep (se 2 (by rfl) ⟨1549062, by rfl⟩ : syracuseStep 4130833 = 3098125) B3098125
theorem B5507777 : Blo 2037435 5507777 := bstep (se 2 (by rfl) ⟨2065416, by rfl⟩ : syracuseStep 5507777 = 4130833) B4130833
theorem B14687405 : Blo 2037435 14687405 := bstep (se 3 (by rfl) ⟨2753888, by rfl⟩ : syracuseStep 14687405 = 5507777) B5507777
theorem B9791603 : Blo 2037435 9791603 := bstep (se 1 (by rfl) ⟨7343702, by rfl⟩ : syracuseStep 9791603 = 14687405) B14687405
theorem B6527735 : Blo 2037435 6527735 := bstep (se 1 (by rfl) ⟨4895801, by rfl⟩ : syracuseStep 6527735 = 9791603) B9791603
theorem B4351823 : Blo 2037435 4351823 := bstep (se 1 (by rfl) ⟨3263867, by rfl⟩ : syracuseStep 4351823 = 6527735) B6527735
theorem B2901215 : Blo 2037435 2901215 := bstep (se 1 (by rfl) ⟨2175911, by rfl⟩ : syracuseStep 2901215 = 4351823) B4351823
theorem B7736573 : Blo 2037435 7736573 := bstep (se 3 (by rfl) ⟨1450607, by rfl⟩ : syracuseStep 7736573 = 2901215) B2901215
theorem B5157715 : Blo 2037435 5157715 := bstep (se 1 (by rfl) ⟨3868286, by rfl⟩ : syracuseStep 5157715 = 7736573) B7736573
theorem B6876953 : Blo 2037435 6876953 := bstep (se 2 (by rfl) ⟨2578857, by rfl⟩ : syracuseStep 6876953 = 5157715) B5157715
theorem B4584635 : Blo 2037435 4584635 := bstep (se 1 (by rfl) ⟨3438476, by rfl⟩ : syracuseStep 4584635 = 6876953) B6876953
theorem B3056423 : Blo 2037435 3056423 := bstep (se 1 (by rfl) ⟨2292317, by rfl⟩ : syracuseStep 3056423 = 4584635) B4584635
theorem B2037615 : Blo 2037435 2037615 := bstep (se 1 (by rfl) ⟨1528211, by rfl⟩ : syracuseStep 2037615 = 3056423) B3056423
theorem B3056429 : Blo 2037435 3056429 := bbase (se 3 (by rfl) ⟨573080, by rfl⟩ : syracuseStep 3056429 = 1146161) (by norm_num)
theorem B2037619 : Blo 2037435 2037619 := bstep (se 1 (by rfl) ⟨1528214, by rfl⟩ : syracuseStep 2037619 = 3056429) B3056429
theorem B4584653 : Blo 2037435 4584653 := bbase (se 3 (by rfl) ⟨859622, by rfl⟩ : syracuseStep 4584653 = 1719245) (by norm_num)
theorem B3056435 : Blo 2037435 3056435 := bstep (se 1 (by rfl) ⟨2292326, by rfl⟩ : syracuseStep 3056435 = 4584653) B4584653
theorem B2037623 : Blo 2037435 2037623 := bstep (se 1 (by rfl) ⟨1528217, by rfl⟩ : syracuseStep 2037623 = 3056435) B3056435
theorem B2578873 : Blo 2037435 2578873 := bbase (se 2 (by rfl) ⟨967077, by rfl⟩ : syracuseStep 2578873 = 1934155) (by norm_num)
theorem B3438497 : Blo 2037435 3438497 := bstep (se 2 (by rfl) ⟨1289436, by rfl⟩ : syracuseStep 3438497 = 2578873) B2578873
theorem B2292331 : Blo 2037435 2292331 := bstep (se 1 (by rfl) ⟨1719248, by rfl⟩ : syracuseStep 2292331 = 3438497) B3438497
theorem B3056441 : Blo 2037435 3056441 := bstep (se 2 (by rfl) ⟨1146165, by rfl⟩ : syracuseStep 3056441 = 2292331) B2292331
theorem B2037627 : Blo 2037435 2037627 := bstep (se 1 (by rfl) ⟨1528220, by rfl⟩ : syracuseStep 2037627 = 3056441) B3056441
theorem B4962637 : Blo 2037435 4962637 := bbase (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) (by norm_num)
theorem B6616849 : Blo 2037435 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B8822465 : Blo 2037435 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B5881643 : Blo 2037435 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B3921095 : Blo 2037435 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B10456253 : Blo 2037435 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B6970835 : Blo 2037435 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B4647223 : Blo 2037435 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B24785189 : Blo 2037435 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B16523459 : Blo 2037435 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B11015639 : Blo 2037435 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B7343759 : Blo 2037435 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B4895839 : Blo 2037435 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B6527785 : Blo 2037435 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B8703713 : Blo 2037435 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B23209901 : Blo 2037435 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B15473267 : Blo 2037435 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B10315511 : Blo 2037435 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B6877007 : Blo 2037435 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B4584671 : Blo 2037435 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B3056447 : Blo 2037435 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B2037631 : Blo 2037435 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B3056453 : Blo 2037435 3056453 := bbase (se 4 (by rfl) ⟨286542, by rfl⟩ : syracuseStep 3056453 = 573085) (by norm_num)
theorem B2037635 : Blo 2037435 2037635 := bstep (se 1 (by rfl) ⟨1528226, by rfl⟩ : syracuseStep 2037635 = 3056453) B3056453
theorem B3438517 : Blo 2037435 3438517 := bbase (se 5 (by rfl) ⟨161180, by rfl⟩ : syracuseStep 3438517 = 322361) (by norm_num)
theorem B4584689 : Blo 2037435 4584689 := bstep (se 2 (by rfl) ⟨1719258, by rfl⟩ : syracuseStep 4584689 = 3438517) B3438517
theorem B3056459 : Blo 2037435 3056459 := bstep (se 1 (by rfl) ⟨2292344, by rfl⟩ : syracuseStep 3056459 = 4584689) B4584689
theorem B2037639 : Blo 2037435 2037639 := bstep (se 1 (by rfl) ⟨1528229, by rfl⟩ : syracuseStep 2037639 = 3056459) B3056459
theorem B2292349 : Blo 2037435 2292349 := bbase (se 3 (by rfl) ⟨429815, by rfl⟩ : syracuseStep 2292349 = 859631) (by norm_num)
theorem B3056465 : Blo 2037435 3056465 := bstep (se 2 (by rfl) ⟨1146174, by rfl⟩ : syracuseStep 3056465 = 2292349) B2292349
theorem B2037643 : Blo 2037435 2037643 := bstep (se 1 (by rfl) ⟨1528232, by rfl⟩ : syracuseStep 2037643 = 3056465) B3056465
theorem B6877061 : Blo 2037435 6877061 := bbase (se 4 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 6877061 = 1289449) (by norm_num)
theorem B4584707 : Blo 2037435 4584707 := bstep (se 1 (by rfl) ⟨3438530, by rfl⟩ : syracuseStep 4584707 = 6877061) B6877061
theorem B3056471 : Blo 2037435 3056471 := bstep (se 1 (by rfl) ⟨2292353, by rfl⟩ : syracuseStep 3056471 = 4584707) B4584707
theorem B2037647 : Blo 2037435 2037647 := bstep (se 1 (by rfl) ⟨1528235, by rfl⟩ : syracuseStep 2037647 = 3056471) B3056471
theorem B3056477 : Blo 2037435 3056477 := bbase (se 3 (by rfl) ⟨573089, by rfl⟩ : syracuseStep 3056477 = 1146179) (by norm_num)
theorem B2037651 : Blo 2037435 2037651 := bstep (se 1 (by rfl) ⟨1528238, by rfl⟩ : syracuseStep 2037651 = 3056477) B3056477
theorem B4584725 : Blo 2037435 4584725 := bbase (se 6 (by rfl) ⟨107454, by rfl⟩ : syracuseStep 4584725 = 214909) (by norm_num)
theorem B3056483 : Blo 2037435 3056483 := bstep (se 1 (by rfl) ⟨2292362, by rfl⟩ : syracuseStep 3056483 = 4584725) B4584725
theorem B2037655 : Blo 2037435 2037655 := bstep (se 1 (by rfl) ⟨1528241, by rfl⟩ : syracuseStep 2037655 = 3056483) B3056483
theorem B7736741 : Blo 2037435 7736741 := bbase (se 4 (by rfl) ⟨725319, by rfl⟩ : syracuseStep 7736741 = 1450639) (by norm_num)
theorem B5157827 : Blo 2037435 5157827 := bstep (se 1 (by rfl) ⟨3868370, by rfl⟩ : syracuseStep 5157827 = 7736741) B7736741
theorem B3438551 : Blo 2037435 3438551 := bstep (se 1 (by rfl) ⟨2578913, by rfl⟩ : syracuseStep 3438551 = 5157827) B5157827
theorem B2292367 : Blo 2037435 2292367 := bstep (se 1 (by rfl) ⟨1719275, by rfl⟩ : syracuseStep 2292367 = 3438551) B3438551
theorem B3056489 : Blo 2037435 3056489 := bstep (se 2 (by rfl) ⟨1146183, by rfl⟩ : syracuseStep 3056489 = 2292367) B2292367
theorem B2037659 : Blo 2037435 2037659 := bstep (se 1 (by rfl) ⟨1528244, by rfl⟩ : syracuseStep 2037659 = 3056489) B3056489
theorem B4351925 : Blo 2037435 4351925 := bbase (se 5 (by rfl) ⟨203996, by rfl⟩ : syracuseStep 4351925 = 407993) (by norm_num)
theorem B11605133 : Blo 2037435 11605133 := bstep (se 3 (by rfl) ⟨2175962, by rfl⟩ : syracuseStep 11605133 = 4351925) B4351925
theorem B7736755 : Blo 2037435 7736755 := bstep (se 1 (by rfl) ⟨5802566, by rfl⟩ : syracuseStep 7736755 = 11605133) B11605133
theorem B10315673 : Blo 2037435 10315673 := bstep (se 2 (by rfl) ⟨3868377, by rfl⟩ : syracuseStep 10315673 = 7736755) B7736755
theorem B6877115 : Blo 2037435 6877115 := bstep (se 1 (by rfl) ⟨5157836, by rfl⟩ : syracuseStep 6877115 = 10315673) B10315673
theorem B4584743 : Blo 2037435 4584743 := bstep (se 1 (by rfl) ⟨3438557, by rfl⟩ : syracuseStep 4584743 = 6877115) B6877115
theorem B3056495 : Blo 2037435 3056495 := bstep (se 1 (by rfl) ⟨2292371, by rfl⟩ : syracuseStep 3056495 = 4584743) B4584743
theorem B2037663 : Blo 2037435 2037663 := bstep (se 1 (by rfl) ⟨1528247, by rfl⟩ : syracuseStep 2037663 = 3056495) B3056495
theorem B3056501 : Blo 2037435 3056501 := bbase (se 5 (by rfl) ⟨143273, by rfl⟩ : syracuseStep 3056501 = 286547) (by norm_num)
theorem B2037667 : Blo 2037435 2037667 := bstep (se 1 (by rfl) ⟨1528250, by rfl⟩ : syracuseStep 2037667 = 3056501) B3056501
theorem B6196421 : Blo 2037435 6196421 := bbase (se 4 (by rfl) ⟨580914, by rfl⟩ : syracuseStep 6196421 = 1161829) (by norm_num)
theorem B4130947 : Blo 2037435 4130947 := bstep (se 1 (by rfl) ⟨3098210, by rfl⟩ : syracuseStep 4130947 = 6196421) B6196421
theorem B5507929 : Blo 2037435 5507929 := bstep (se 2 (by rfl) ⟨2065473, by rfl⟩ : syracuseStep 5507929 = 4130947) B4130947
theorem B7343905 : Blo 2037435 7343905 := bstep (se 2 (by rfl) ⟨2753964, by rfl⟩ : syracuseStep 7343905 = 5507929) B5507929
theorem B9791873 : Blo 2037435 9791873 := bstep (se 2 (by rfl) ⟨3671952, by rfl⟩ : syracuseStep 9791873 = 7343905) B7343905
theorem B6527915 : Blo 2037435 6527915 := bstep (se 1 (by rfl) ⟨4895936, by rfl⟩ : syracuseStep 6527915 = 9791873) B9791873
theorem B4351943 : Blo 2037435 4351943 := bstep (se 1 (by rfl) ⟨3263957, by rfl⟩ : syracuseStep 4351943 = 6527915) B6527915
theorem B2901295 : Blo 2037435 2901295 := bstep (se 1 (by rfl) ⟨2175971, by rfl⟩ : syracuseStep 2901295 = 4351943) B4351943
theorem B3868393 : Blo 2037435 3868393 := bstep (se 2 (by rfl) ⟨1450647, by rfl⟩ : syracuseStep 3868393 = 2901295) B2901295
theorem B5157857 : Blo 2037435 5157857 := bstep (se 2 (by rfl) ⟨1934196, by rfl⟩ : syracuseStep 5157857 = 3868393) B3868393
theorem B3438571 : Blo 2037435 3438571 := bstep (se 1 (by rfl) ⟨2578928, by rfl⟩ : syracuseStep 3438571 = 5157857) B5157857
theorem B4584761 : Blo 2037435 4584761 := bstep (se 2 (by rfl) ⟨1719285, by rfl⟩ : syracuseStep 4584761 = 3438571) B3438571
theorem B3056507 : Blo 2037435 3056507 := bstep (se 1 (by rfl) ⟨2292380, by rfl⟩ : syracuseStep 3056507 = 4584761) B4584761
theorem B2037671 : Blo 2037435 2037671 := bstep (se 1 (by rfl) ⟨1528253, by rfl⟩ : syracuseStep 2037671 = 3056507) B3056507
theorem B2292385 : Blo 2037435 2292385 := bbase (se 2 (by rfl) ⟨859644, by rfl⟩ : syracuseStep 2292385 = 1719289) (by norm_num)
theorem B3056513 : Blo 2037435 3056513 := bstep (se 2 (by rfl) ⟨1146192, by rfl⟩ : syracuseStep 3056513 = 2292385) B2292385
theorem B2037675 : Blo 2037435 2037675 := bstep (se 1 (by rfl) ⟨1528256, by rfl⟩ : syracuseStep 2037675 = 3056513) B3056513
theorem B5157877 : Blo 2037435 5157877 := bbase (se 5 (by rfl) ⟨241775, by rfl⟩ : syracuseStep 5157877 = 483551) (by norm_num)
theorem B6877169 : Blo 2037435 6877169 := bstep (se 2 (by rfl) ⟨2578938, by rfl⟩ : syracuseStep 6877169 = 5157877) B5157877
theorem B4584779 : Blo 2037435 4584779 := bstep (se 1 (by rfl) ⟨3438584, by rfl⟩ : syracuseStep 4584779 = 6877169) B6877169
theorem B3056519 : Blo 2037435 3056519 := bstep (se 1 (by rfl) ⟨2292389, by rfl⟩ : syracuseStep 3056519 = 4584779) B4584779
theorem B2037679 : Blo 2037435 2037679 := bstep (se 1 (by rfl) ⟨1528259, by rfl⟩ : syracuseStep 2037679 = 3056519) B3056519
theorem B3056525 : Blo 2037435 3056525 := bbase (se 3 (by rfl) ⟨573098, by rfl⟩ : syracuseStep 3056525 = 1146197) (by norm_num)
theorem B2037683 : Blo 2037435 2037683 := bstep (se 1 (by rfl) ⟨1528262, by rfl⟩ : syracuseStep 2037683 = 3056525) B3056525
theorem B4584797 : Blo 2037435 4584797 := bbase (se 3 (by rfl) ⟨859649, by rfl⟩ : syracuseStep 4584797 = 1719299) (by norm_num)
theorem B3056531 : Blo 2037435 3056531 := bstep (se 1 (by rfl) ⟨2292398, by rfl⟩ : syracuseStep 3056531 = 4584797) B4584797
theorem B2037687 : Blo 2037435 2037687 := bstep (se 1 (by rfl) ⟨1528265, by rfl⟩ : syracuseStep 2037687 = 3056531) B3056531
theorem B3438605 : Blo 2037435 3438605 := bbase (se 3 (by rfl) ⟨644738, by rfl⟩ : syracuseStep 3438605 = 1289477) (by norm_num)
theorem B2292403 : Blo 2037435 2292403 := bstep (se 1 (by rfl) ⟨1719302, by rfl⟩ : syracuseStep 2292403 = 3438605) B3438605
theorem B3056537 : Blo 2037435 3056537 := bstep (se 2 (by rfl) ⟨1146201, by rfl⟩ : syracuseStep 3056537 = 2292403) B2292403
theorem B2037691 : Blo 2037435 2037691 := bstep (se 1 (by rfl) ⟨1528268, by rfl⟩ : syracuseStep 2037691 = 3056537) B3056537
theorem B2323685 : Blo 2037435 2323685 := bbase (se 4 (by rfl) ⟨217845, by rfl⟩ : syracuseStep 2323685 = 435691) (by norm_num)
theorem B6196493 : Blo 2037435 6196493 := bstep (se 3 (by rfl) ⟨1161842, by rfl⟩ : syracuseStep 6196493 = 2323685) B2323685
theorem B4130995 : Blo 2037435 4130995 := bstep (se 1 (by rfl) ⟨3098246, by rfl⟩ : syracuseStep 4130995 = 6196493) B6196493
theorem B5507993 : Blo 2037435 5507993 := bstep (se 2 (by rfl) ⟨2065497, by rfl⟩ : syracuseStep 5507993 = 4130995) B4130995
theorem B3671995 : Blo 2037435 3671995 := bstep (se 1 (by rfl) ⟨2753996, by rfl⟩ : syracuseStep 3671995 = 5507993) B5507993
theorem B4895993 : Blo 2037435 4895993 := bstep (se 2 (by rfl) ⟨1835997, by rfl⟩ : syracuseStep 4895993 = 3671995) B3671995
theorem B3263995 : Blo 2037435 3263995 := bstep (se 1 (by rfl) ⟨2447996, by rfl⟩ : syracuseStep 3263995 = 4895993) B4895993
theorem B17407973 : Blo 2037435 17407973 := bstep (se 4 (by rfl) ⟨1631997, by rfl⟩ : syracuseStep 17407973 = 3263995) B3263995
theorem B11605315 : Blo 2037435 11605315 := bstep (se 1 (by rfl) ⟨8703986, by rfl⟩ : syracuseStep 11605315 = 17407973) B17407973
theorem B15473753 : Blo 2037435 15473753 := bstep (se 2 (by rfl) ⟨5802657, by rfl⟩ : syracuseStep 15473753 = 11605315) B11605315
theorem B10315835 : Blo 2037435 10315835 := bstep (se 1 (by rfl) ⟨7736876, by rfl⟩ : syracuseStep 10315835 = 15473753) B15473753
theorem B6877223 : Blo 2037435 6877223 := bstep (se 1 (by rfl) ⟨5157917, by rfl⟩ : syracuseStep 6877223 = 10315835) B10315835
theorem B4584815 : Blo 2037435 4584815 := bstep (se 1 (by rfl) ⟨3438611, by rfl⟩ : syracuseStep 4584815 = 6877223) B6877223
theorem B3056543 : Blo 2037435 3056543 := bstep (se 1 (by rfl) ⟨2292407, by rfl⟩ : syracuseStep 3056543 = 4584815) B4584815
theorem B2037695 : Blo 2037435 2037695 := bstep (se 1 (by rfl) ⟨1528271, by rfl⟩ : syracuseStep 2037695 = 3056543) B3056543
theorem B3056549 : Blo 2037435 3056549 := bbase (se 4 (by rfl) ⟨286551, by rfl⟩ : syracuseStep 3056549 = 573103) (by norm_num)
theorem B2037699 : Blo 2037435 2037699 := bstep (se 1 (by rfl) ⟨1528274, by rfl⟩ : syracuseStep 2037699 = 3056549) B3056549
theorem B2578969 : Blo 2037435 2578969 := bbase (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) (by norm_num)
theorem B3438625 : Blo 2037435 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B4584833 : Blo 2037435 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B3056555 : Blo 2037435 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B2037703 : Blo 2037435 2037703 := bstep (se 1 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 2037703 = 3056555) B3056555
theorem B2292421 : Blo 2037435 2292421 := bbase (se 4 (by rfl) ⟨214914, by rfl⟩ : syracuseStep 2292421 = 429829) (by norm_num)
theorem B3056561 : Blo 2037435 3056561 := bstep (se 2 (by rfl) ⟨1146210, by rfl⟩ : syracuseStep 3056561 = 2292421) B2292421
theorem B2037707 : Blo 2037435 2037707 := bstep (se 1 (by rfl) ⟨1528280, by rfl⟩ : syracuseStep 2037707 = 3056561) B3056561
theorem B3868469 : Blo 2037435 3868469 := bbase (se 5 (by rfl) ⟨181334, by rfl⟩ : syracuseStep 3868469 = 362669) (by norm_num)
theorem B2578979 : Blo 2037435 2578979 := bstep (se 1 (by rfl) ⟨1934234, by rfl⟩ : syracuseStep 2578979 = 3868469) B3868469
theorem B6877277 : Blo 2037435 6877277 := bstep (se 3 (by rfl) ⟨1289489, by rfl⟩ : syracuseStep 6877277 = 2578979) B2578979
theorem B4584851 : Blo 2037435 4584851 := bstep (se 1 (by rfl) ⟨3438638, by rfl⟩ : syracuseStep 4584851 = 6877277) B6877277
theorem B3056567 : Blo 2037435 3056567 := bstep (se 1 (by rfl) ⟨2292425, by rfl⟩ : syracuseStep 3056567 = 4584851) B4584851
theorem B2037711 : Blo 2037435 2037711 := bstep (se 1 (by rfl) ⟨1528283, by rfl⟩ : syracuseStep 2037711 = 3056567) B3056567
theorem B3056573 : Blo 2037435 3056573 := bbase (se 3 (by rfl) ⟨573107, by rfl⟩ : syracuseStep 3056573 = 1146215) (by norm_num)
theorem B2037715 : Blo 2037435 2037715 := bstep (se 1 (by rfl) ⟨1528286, by rfl⟩ : syracuseStep 2037715 = 3056573) B3056573
theorem B4584869 : Blo 2037435 4584869 := bbase (se 4 (by rfl) ⟨429831, by rfl⟩ : syracuseStep 4584869 = 859663) (by norm_num)
theorem B3056579 : Blo 2037435 3056579 := bstep (se 1 (by rfl) ⟨2292434, by rfl⟩ : syracuseStep 3056579 = 4584869) B4584869
theorem B2037719 : Blo 2037435 2037719 := bstep (se 1 (by rfl) ⟨1528289, by rfl⟩ : syracuseStep 2037719 = 3056579) B3056579
theorem B5157989 : Blo 2037435 5157989 := bbase (se 4 (by rfl) ⟨483561, by rfl⟩ : syracuseStep 5157989 = 967123) (by norm_num)
theorem B3438659 : Blo 2037435 3438659 := bstep (se 1 (by rfl) ⟨2578994, by rfl⟩ : syracuseStep 3438659 = 5157989) B5157989
theorem B2292439 : Blo 2037435 2292439 := bstep (se 1 (by rfl) ⟨1719329, by rfl⟩ : syracuseStep 2292439 = 3438659) B3438659
theorem B3056585 : Blo 2037435 3056585 := bstep (se 2 (by rfl) ⟨1146219, by rfl⟩ : syracuseStep 3056585 = 2292439) B2292439
theorem B2037723 : Blo 2037435 2037723 := bstep (se 1 (by rfl) ⟨1528292, by rfl⟩ : syracuseStep 2037723 = 3056585) B3056585
theorem B3308581 : Blo 2037435 3308581 := bbase (se 4 (by rfl) ⟨310179, by rfl⟩ : syracuseStep 3308581 = 620359) (by norm_num)
theorem B4411441 : Blo 2037435 4411441 := bstep (se 2 (by rfl) ⟨1654290, by rfl⟩ : syracuseStep 4411441 = 3308581) B3308581
theorem B23527685 : Blo 2037435 23527685 := bstep (se 4 (by rfl) ⟨2205720, by rfl⟩ : syracuseStep 23527685 = 4411441) B4411441
theorem B15685123 : Blo 2037435 15685123 := bstep (se 1 (by rfl) ⟨11763842, by rfl⟩ : syracuseStep 15685123 = 23527685) B23527685
theorem B20913497 : Blo 2037435 20913497 := bstep (se 2 (by rfl) ⟨7842561, by rfl⟩ : syracuseStep 20913497 = 15685123) B15685123
theorem B13942331 : Blo 2037435 13942331 := bstep (se 1 (by rfl) ⟨10456748, by rfl⟩ : syracuseStep 13942331 = 20913497) B20913497
theorem B9294887 : Blo 2037435 9294887 := bstep (se 1 (by rfl) ⟨6971165, by rfl⟩ : syracuseStep 9294887 = 13942331) B13942331
theorem B6196591 : Blo 2037435 6196591 := bstep (se 1 (by rfl) ⟨4647443, by rfl⟩ : syracuseStep 6196591 = 9294887) B9294887
theorem B8262121 : Blo 2037435 8262121 := bstep (se 2 (by rfl) ⟨3098295, by rfl⟩ : syracuseStep 8262121 = 6196591) B6196591
theorem B11016161 : Blo 2037435 11016161 := bstep (se 2 (by rfl) ⟨4131060, by rfl⟩ : syracuseStep 11016161 = 8262121) B8262121
theorem B7344107 : Blo 2037435 7344107 := bstep (se 1 (by rfl) ⟨5508080, by rfl⟩ : syracuseStep 7344107 = 11016161) B11016161
theorem B4896071 : Blo 2037435 4896071 := bstep (se 1 (by rfl) ⟨3672053, by rfl⟩ : syracuseStep 4896071 = 7344107) B7344107
theorem B3264047 : Blo 2037435 3264047 := bstep (se 1 (by rfl) ⟨2448035, by rfl⟩ : syracuseStep 3264047 = 4896071) B4896071
theorem B2176031 : Blo 2037435 2176031 := bstep (se 1 (by rfl) ⟨1632023, by rfl⟩ : syracuseStep 2176031 = 3264047) B3264047
theorem B5802749 : Blo 2037435 5802749 := bstep (se 3 (by rfl) ⟨1088015, by rfl⟩ : syracuseStep 5802749 = 2176031) B2176031
theorem B3868499 : Blo 2037435 3868499 := bstep (se 1 (by rfl) ⟨2901374, by rfl⟩ : syracuseStep 3868499 = 5802749) B5802749
theorem B10315997 : Blo 2037435 10315997 := bstep (se 3 (by rfl) ⟨1934249, by rfl⟩ : syracuseStep 10315997 = 3868499) B3868499
theorem B6877331 : Blo 2037435 6877331 := bstep (se 1 (by rfl) ⟨5157998, by rfl⟩ : syracuseStep 6877331 = 10315997) B10315997
theorem B4584887 : Blo 2037435 4584887 := bstep (se 1 (by rfl) ⟨3438665, by rfl⟩ : syracuseStep 4584887 = 6877331) B6877331
theorem B3056591 : Blo 2037435 3056591 := bstep (se 1 (by rfl) ⟨2292443, by rfl⟩ : syracuseStep 3056591 = 4584887) B4584887
theorem B2037727 : Blo 2037435 2037727 := bstep (se 1 (by rfl) ⟨1528295, by rfl⟩ : syracuseStep 2037727 = 3056591) B3056591
theorem B3056597 : Blo 2037435 3056597 := bbase (se 7 (by rfl) ⟨35819, by rfl⟩ : syracuseStep 3056597 = 71639) (by norm_num)
theorem B2037731 : Blo 2037435 2037731 := bstep (se 1 (by rfl) ⟨1528298, by rfl⟩ : syracuseStep 2037731 = 3056597) B3056597
theorem B7737029 : Blo 2037435 7737029 := bbase (se 4 (by rfl) ⟨725346, by rfl⟩ : syracuseStep 7737029 = 1450693) (by norm_num)
theorem B5158019 : Blo 2037435 5158019 := bstep (se 1 (by rfl) ⟨3868514, by rfl⟩ : syracuseStep 5158019 = 7737029) B7737029
theorem B3438679 : Blo 2037435 3438679 := bstep (se 1 (by rfl) ⟨2579009, by rfl⟩ : syracuseStep 3438679 = 5158019) B5158019
theorem B4584905 : Blo 2037435 4584905 := bstep (se 2 (by rfl) ⟨1719339, by rfl⟩ : syracuseStep 4584905 = 3438679) B3438679
theorem B3056603 : Blo 2037435 3056603 := bstep (se 1 (by rfl) ⟨2292452, by rfl⟩ : syracuseStep 3056603 = 4584905) B4584905
theorem B2037735 : Blo 2037435 2037735 := bstep (se 1 (by rfl) ⟨1528301, by rfl⟩ : syracuseStep 2037735 = 3056603) B3056603
theorem B2292457 : Blo 2037435 2292457 := bbase (se 2 (by rfl) ⟨859671, by rfl⟩ : syracuseStep 2292457 = 1719343) (by norm_num)
theorem B3056609 : Blo 2037435 3056609 := bstep (se 2 (by rfl) ⟨1146228, by rfl⟩ : syracuseStep 3056609 = 2292457) B2292457
theorem B2037739 : Blo 2037435 2037739 := bstep (se 1 (by rfl) ⟨1528304, by rfl⟩ : syracuseStep 2037739 = 3056609) B3056609
theorem B11605589 : Blo 2037435 11605589 := bbase (se 8 (by rfl) ⟨68001, by rfl⟩ : syracuseStep 11605589 = 136003) (by norm_num)
theorem B7737059 : Blo 2037435 7737059 := bstep (se 1 (by rfl) ⟨5802794, by rfl⟩ : syracuseStep 7737059 = 11605589) B11605589
theorem B5158039 : Blo 2037435 5158039 := bstep (se 1 (by rfl) ⟨3868529, by rfl⟩ : syracuseStep 5158039 = 7737059) B7737059
theorem B6877385 : Blo 2037435 6877385 := bstep (se 2 (by rfl) ⟨2579019, by rfl⟩ : syracuseStep 6877385 = 5158039) B5158039
theorem B4584923 : Blo 2037435 4584923 := bstep (se 1 (by rfl) ⟨3438692, by rfl⟩ : syracuseStep 4584923 = 6877385) B6877385
theorem B3056615 : Blo 2037435 3056615 := bstep (se 1 (by rfl) ⟨2292461, by rfl⟩ : syracuseStep 3056615 = 4584923) B4584923
theorem B2037743 : Blo 2037435 2037743 := bstep (se 1 (by rfl) ⟨1528307, by rfl⟩ : syracuseStep 2037743 = 3056615) B3056615
theorem B3056621 : Blo 2037435 3056621 := bbase (se 3 (by rfl) ⟨573116, by rfl⟩ : syracuseStep 3056621 = 1146233) (by norm_num)
theorem B2037747 : Blo 2037435 2037747 := bstep (se 1 (by rfl) ⟨1528310, by rfl⟩ : syracuseStep 2037747 = 3056621) B3056621
theorem B4584941 : Blo 2037435 4584941 := bbase (se 3 (by rfl) ⟨859676, by rfl⟩ : syracuseStep 4584941 = 1719353) (by norm_num)
theorem B3056627 : Blo 2037435 3056627 := bstep (se 1 (by rfl) ⟨2292470, by rfl⟩ : syracuseStep 3056627 = 4584941) B4584941
theorem B2037751 : Blo 2037435 2037751 := bstep (se 1 (by rfl) ⟨1528313, by rfl⟩ : syracuseStep 2037751 = 3056627) B3056627
theorem B4647509 : Blo 2037435 4647509 := bbase (se 8 (by rfl) ⟨27231, by rfl⟩ : syracuseStep 4647509 = 54463) (by norm_num)
theorem B3098339 : Blo 2037435 3098339 := bstep (se 1 (by rfl) ⟨2323754, by rfl⟩ : syracuseStep 3098339 = 4647509) B4647509
theorem B2065559 : Blo 2037435 2065559 := bstep (se 1 (by rfl) ⟨1549169, by rfl⟩ : syracuseStep 2065559 = 3098339) B3098339
theorem B5508157 : Blo 2037435 5508157 := bstep (se 3 (by rfl) ⟨1032779, by rfl⟩ : syracuseStep 5508157 = 2065559) B2065559
theorem B7344209 : Blo 2037435 7344209 := bstep (se 2 (by rfl) ⟨2754078, by rfl⟩ : syracuseStep 7344209 = 5508157) B5508157
theorem B4896139 : Blo 2037435 4896139 := bstep (se 1 (by rfl) ⟨3672104, by rfl⟩ : syracuseStep 4896139 = 7344209) B7344209
theorem B6528185 : Blo 2037435 6528185 := bstep (se 2 (by rfl) ⟨2448069, by rfl⟩ : syracuseStep 6528185 = 4896139) B4896139
theorem B4352123 : Blo 2037435 4352123 := bstep (se 1 (by rfl) ⟨3264092, by rfl⟩ : syracuseStep 4352123 = 6528185) B6528185
theorem B2901415 : Blo 2037435 2901415 := bstep (se 1 (by rfl) ⟨2176061, by rfl⟩ : syracuseStep 2901415 = 4352123) B4352123
theorem B3868553 : Blo 2037435 3868553 := bstep (se 2 (by rfl) ⟨1450707, by rfl⟩ : syracuseStep 3868553 = 2901415) B2901415
theorem B2579035 : Blo 2037435 2579035 := bstep (se 1 (by rfl) ⟨1934276, by rfl⟩ : syracuseStep 2579035 = 3868553) B3868553
theorem B3438713 : Blo 2037435 3438713 := bstep (se 2 (by rfl) ⟨1289517, by rfl⟩ : syracuseStep 3438713 = 2579035) B2579035
theorem B2292475 : Blo 2037435 2292475 := bstep (se 1 (by rfl) ⟨1719356, by rfl⟩ : syracuseStep 2292475 = 3438713) B3438713
theorem B3056633 : Blo 2037435 3056633 := bstep (se 2 (by rfl) ⟨1146237, by rfl⟩ : syracuseStep 3056633 = 2292475) B2292475
theorem B2037755 : Blo 2037435 2037755 := bstep (se 1 (by rfl) ⟨1528316, by rfl⟩ : syracuseStep 2037755 = 3056633) B3056633
theorem B47056085 : Blo 2037435 47056085 := bbase (se 7 (by rfl) ⟨551438, by rfl⟩ : syracuseStep 47056085 = 1102877) (by norm_num)
theorem B31370723 : Blo 2037435 31370723 := bstep (se 1 (by rfl) ⟨23528042, by rfl⟩ : syracuseStep 31370723 = 47056085) B47056085
theorem B20913815 : Blo 2037435 20913815 := bstep (se 1 (by rfl) ⟨15685361, by rfl⟩ : syracuseStep 20913815 = 31370723) B31370723
theorem B13942543 : Blo 2037435 13942543 := bstep (se 1 (by rfl) ⟨10456907, by rfl⟩ : syracuseStep 13942543 = 20913815) B20913815
theorem B18590057 : Blo 2037435 18590057 := bstep (se 2 (by rfl) ⟨6971271, by rfl⟩ : syracuseStep 18590057 = 13942543) B13942543
theorem B12393371 : Blo 2037435 12393371 := bstep (se 1 (by rfl) ⟨9295028, by rfl⟩ : syracuseStep 12393371 = 18590057) B18590057
theorem B8262247 : Blo 2037435 8262247 := bstep (se 1 (by rfl) ⟨6196685, by rfl⟩ : syracuseStep 8262247 = 12393371) B12393371
theorem B11016329 : Blo 2037435 11016329 := bstep (se 2 (by rfl) ⟨4131123, by rfl⟩ : syracuseStep 11016329 = 8262247) B8262247
theorem B117507509 : Blo 2037435 117507509 := bstep (se 5 (by rfl) ⟨5508164, by rfl⟩ : syracuseStep 117507509 = 11016329) B11016329
theorem B78338339 : Blo 2037435 78338339 := bstep (se 1 (by rfl) ⟨58753754, by rfl⟩ : syracuseStep 78338339 = 117507509) B117507509
theorem B52225559 : Blo 2037435 52225559 := bstep (se 1 (by rfl) ⟨39169169, by rfl⟩ : syracuseStep 52225559 = 78338339) B78338339
theorem B34817039 : Blo 2037435 34817039 := bstep (se 1 (by rfl) ⟨26112779, by rfl⟩ : syracuseStep 34817039 = 52225559) B52225559
theorem B23211359 : Blo 2037435 23211359 := bstep (se 1 (by rfl) ⟨17408519, by rfl⟩ : syracuseStep 23211359 = 34817039) B34817039
theorem B15474239 : Blo 2037435 15474239 := bstep (se 1 (by rfl) ⟨11605679, by rfl⟩ : syracuseStep 15474239 = 23211359) B23211359
theorem B10316159 : Blo 2037435 10316159 := bstep (se 1 (by rfl) ⟨7737119, by rfl⟩ : syracuseStep 10316159 = 15474239) B15474239
theorem B6877439 : Blo 2037435 6877439 := bstep (se 1 (by rfl) ⟨5158079, by rfl⟩ : syracuseStep 6877439 = 10316159) B10316159
theorem B4584959 : Blo 2037435 4584959 := bstep (se 1 (by rfl) ⟨3438719, by rfl⟩ : syracuseStep 4584959 = 6877439) B6877439
theorem B3056639 : Blo 2037435 3056639 := bstep (se 1 (by rfl) ⟨2292479, by rfl⟩ : syracuseStep 3056639 = 4584959) B4584959
theorem B2037759 : Blo 2037435 2037759 := bstep (se 1 (by rfl) ⟨1528319, by rfl⟩ : syracuseStep 2037759 = 3056639) B3056639
theorem B3056645 : Blo 2037435 3056645 := bbase (se 4 (by rfl) ⟨286560, by rfl⟩ : syracuseStep 3056645 = 573121) (by norm_num)
theorem B2037763 : Blo 2037435 2037763 := bstep (se 1 (by rfl) ⟨1528322, by rfl⟩ : syracuseStep 2037763 = 3056645) B3056645
theorem B3438733 : Blo 2037435 3438733 := bbase (se 3 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 3438733 = 1289525) (by norm_num)
theorem B4584977 : Blo 2037435 4584977 := bstep (se 2 (by rfl) ⟨1719366, by rfl⟩ : syracuseStep 4584977 = 3438733) B3438733
theorem B3056651 : Blo 2037435 3056651 := bstep (se 1 (by rfl) ⟨2292488, by rfl⟩ : syracuseStep 3056651 = 4584977) B4584977
theorem B2037767 : Blo 2037435 2037767 := bstep (se 1 (by rfl) ⟨1528325, by rfl⟩ : syracuseStep 2037767 = 3056651) B3056651
theorem B2292493 : Blo 2037435 2292493 := bbase (se 3 (by rfl) ⟨429842, by rfl⟩ : syracuseStep 2292493 = 859685) (by norm_num)
theorem B3056657 : Blo 2037435 3056657 := bstep (se 2 (by rfl) ⟨1146246, by rfl⟩ : syracuseStep 3056657 = 2292493) B2292493
theorem B2037771 : Blo 2037435 2037771 := bstep (se 1 (by rfl) ⟨1528328, by rfl⟩ : syracuseStep 2037771 = 3056657) B3056657
theorem B6877493 : Blo 2037435 6877493 := bbase (se 5 (by rfl) ⟨322382, by rfl⟩ : syracuseStep 6877493 = 644765) (by norm_num)
theorem B4584995 : Blo 2037435 4584995 := bstep (se 1 (by rfl) ⟨3438746, by rfl⟩ : syracuseStep 4584995 = 6877493) B6877493
theorem B3056663 : Blo 2037435 3056663 := bstep (se 1 (by rfl) ⟨2292497, by rfl⟩ : syracuseStep 3056663 = 4584995) B4584995
theorem B2037775 : Blo 2037435 2037775 := bstep (se 1 (by rfl) ⟨1528331, by rfl⟩ : syracuseStep 2037775 = 3056663) B3056663
theorem B3056669 : Blo 2037435 3056669 := bbase (se 3 (by rfl) ⟨573125, by rfl⟩ : syracuseStep 3056669 = 1146251) (by norm_num)
theorem B2037779 : Blo 2037435 2037779 := bstep (se 1 (by rfl) ⟨1528334, by rfl⟩ : syracuseStep 2037779 = 3056669) B3056669
theorem B4585013 : Blo 2037435 4585013 := bbase (se 5 (by rfl) ⟨214922, by rfl⟩ : syracuseStep 4585013 = 429845) (by norm_num)
theorem B3056675 : Blo 2037435 3056675 := bstep (se 1 (by rfl) ⟨2292506, by rfl⟩ : syracuseStep 3056675 = 4585013) B4585013
theorem B2037783 : Blo 2037435 2037783 := bstep (se 1 (by rfl) ⟨1528337, by rfl⟩ : syracuseStep 2037783 = 3056675) B3056675
theorem B4647581 : Blo 2037435 4647581 := bbase (se 3 (by rfl) ⟨871421, by rfl⟩ : syracuseStep 4647581 = 1742843) (by norm_num)
theorem B3098387 : Blo 2037435 3098387 := bstep (se 1 (by rfl) ⟨2323790, by rfl⟩ : syracuseStep 3098387 = 4647581) B4647581
theorem B2065591 : Blo 2037435 2065591 := bstep (se 1 (by rfl) ⟨1549193, by rfl⟩ : syracuseStep 2065591 = 3098387) B3098387
theorem B11016485 : Blo 2037435 11016485 := bstep (se 4 (by rfl) ⟨1032795, by rfl⟩ : syracuseStep 11016485 = 2065591) B2065591
theorem B7344323 : Blo 2037435 7344323 := bstep (se 1 (by rfl) ⟨5508242, by rfl⟩ : syracuseStep 7344323 = 11016485) B11016485
theorem B4896215 : Blo 2037435 4896215 := bstep (se 1 (by rfl) ⟨3672161, by rfl⟩ : syracuseStep 4896215 = 7344323) B7344323
theorem B3264143 : Blo 2037435 3264143 := bstep (se 1 (by rfl) ⟨2448107, by rfl⟩ : syracuseStep 3264143 = 4896215) B4896215
theorem B8704381 : Blo 2037435 8704381 := bstep (se 3 (by rfl) ⟨1632071, by rfl⟩ : syracuseStep 8704381 = 3264143) B3264143
theorem B11605841 : Blo 2037435 11605841 := bstep (se 2 (by rfl) ⟨4352190, by rfl⟩ : syracuseStep 11605841 = 8704381) B8704381
theorem B7737227 : Blo 2037435 7737227 := bstep (se 1 (by rfl) ⟨5802920, by rfl⟩ : syracuseStep 7737227 = 11605841) B11605841
theorem B5158151 : Blo 2037435 5158151 := bstep (se 1 (by rfl) ⟨3868613, by rfl⟩ : syracuseStep 5158151 = 7737227) B7737227
theorem B3438767 : Blo 2037435 3438767 := bstep (se 1 (by rfl) ⟨2579075, by rfl⟩ : syracuseStep 3438767 = 5158151) B5158151
theorem B2292511 : Blo 2037435 2292511 := bstep (se 1 (by rfl) ⟨1719383, by rfl⟩ : syracuseStep 2292511 = 3438767) B3438767
theorem B3056681 : Blo 2037435 3056681 := bstep (se 2 (by rfl) ⟨1146255, by rfl⟩ : syracuseStep 3056681 = 2292511) B2292511
theorem B2037787 : Blo 2037435 2037787 := bstep (se 1 (by rfl) ⟨1528340, by rfl⟩ : syracuseStep 2037787 = 3056681) B3056681
theorem B3264149 : Blo 2037435 3264149 := bbase (se 6 (by rfl) ⟨76503, by rfl⟩ : syracuseStep 3264149 = 153007) (by norm_num)
theorem B8704397 : Blo 2037435 8704397 := bstep (se 3 (by rfl) ⟨1632074, by rfl⟩ : syracuseStep 8704397 = 3264149) B3264149
theorem B5802931 : Blo 2037435 5802931 := bstep (se 1 (by rfl) ⟨4352198, by rfl⟩ : syracuseStep 5802931 = 8704397) B8704397
theorem B7737241 : Blo 2037435 7737241 := bstep (se 2 (by rfl) ⟨2901465, by rfl⟩ : syracuseStep 7737241 = 5802931) B5802931
theorem B10316321 : Blo 2037435 10316321 := bstep (se 2 (by rfl) ⟨3868620, by rfl⟩ : syracuseStep 10316321 = 7737241) B7737241
theorem B6877547 : Blo 2037435 6877547 := bstep (se 1 (by rfl) ⟨5158160, by rfl⟩ : syracuseStep 6877547 = 10316321) B10316321
theorem B4585031 : Blo 2037435 4585031 := bstep (se 1 (by rfl) ⟨3438773, by rfl⟩ : syracuseStep 4585031 = 6877547) B6877547
theorem B3056687 : Blo 2037435 3056687 := bstep (se 1 (by rfl) ⟨2292515, by rfl⟩ : syracuseStep 3056687 = 4585031) B4585031
theorem B2037791 : Blo 2037435 2037791 := bstep (se 1 (by rfl) ⟨1528343, by rfl⟩ : syracuseStep 2037791 = 3056687) B3056687
theorem B3056693 : Blo 2037435 3056693 := bbase (se 5 (by rfl) ⟨143282, by rfl⟩ : syracuseStep 3056693 = 286565) (by norm_num)
theorem B2037795 : Blo 2037435 2037795 := bstep (se 1 (by rfl) ⟨1528346, by rfl⟩ : syracuseStep 2037795 = 3056693) B3056693
theorem B5158181 : Blo 2037435 5158181 := bbase (se 4 (by rfl) ⟨483579, by rfl⟩ : syracuseStep 5158181 = 967159) (by norm_num)
theorem B3438787 : Blo 2037435 3438787 := bstep (se 1 (by rfl) ⟨2579090, by rfl⟩ : syracuseStep 3438787 = 5158181) B5158181
theorem B4585049 : Blo 2037435 4585049 := bstep (se 2 (by rfl) ⟨1719393, by rfl⟩ : syracuseStep 4585049 = 3438787) B3438787
theorem B3056699 : Blo 2037435 3056699 := bstep (se 1 (by rfl) ⟨2292524, by rfl⟩ : syracuseStep 3056699 = 4585049) B4585049
theorem B2037799 : Blo 2037435 2037799 := bstep (se 1 (by rfl) ⟨1528349, by rfl⟩ : syracuseStep 2037799 = 3056699) B3056699
theorem B2292529 : Blo 2037435 2292529 := bbase (se 2 (by rfl) ⟨859698, by rfl⟩ : syracuseStep 2292529 = 1719397) (by norm_num)
theorem B3056705 : Blo 2037435 3056705 := bstep (se 2 (by rfl) ⟨1146264, by rfl⟩ : syracuseStep 3056705 = 2292529) B2292529
theorem B2037803 : Blo 2037435 2037803 := bstep (se 1 (by rfl) ⟨1528352, by rfl⟩ : syracuseStep 2037803 = 3056705) B3056705
theorem B2323813 : Blo 2037435 2323813 := bbase (se 4 (by rfl) ⟨217857, by rfl⟩ : syracuseStep 2323813 = 435715) (by norm_num)
theorem B3098417 : Blo 2037435 3098417 := bstep (se 2 (by rfl) ⟨1161906, by rfl⟩ : syracuseStep 3098417 = 2323813) B2323813
theorem B8262445 : Blo 2037435 8262445 := bstep (se 3 (by rfl) ⟨1549208, by rfl⟩ : syracuseStep 8262445 = 3098417) B3098417
theorem B11016593 : Blo 2037435 11016593 := bstep (se 2 (by rfl) ⟨4131222, by rfl⟩ : syracuseStep 11016593 = 8262445) B8262445
theorem B7344395 : Blo 2037435 7344395 := bstep (se 1 (by rfl) ⟨5508296, by rfl⟩ : syracuseStep 7344395 = 11016593) B11016593
theorem B4896263 : Blo 2037435 4896263 := bstep (se 1 (by rfl) ⟨3672197, by rfl⟩ : syracuseStep 4896263 = 7344395) B7344395
theorem B3264175 : Blo 2037435 3264175 := bstep (se 1 (by rfl) ⟨2448131, by rfl⟩ : syracuseStep 3264175 = 4896263) B4896263
theorem B4352233 : Blo 2037435 4352233 := bstep (se 2 (by rfl) ⟨1632087, by rfl⟩ : syracuseStep 4352233 = 3264175) B3264175
theorem B5802977 : Blo 2037435 5802977 := bstep (se 2 (by rfl) ⟨2176116, by rfl⟩ : syracuseStep 5802977 = 4352233) B4352233
theorem B3868651 : Blo 2037435 3868651 := bstep (se 1 (by rfl) ⟨2901488, by rfl⟩ : syracuseStep 3868651 = 5802977) B5802977
theorem B5158201 : Blo 2037435 5158201 := bstep (se 2 (by rfl) ⟨1934325, by rfl⟩ : syracuseStep 5158201 = 3868651) B3868651
theorem B6877601 : Blo 2037435 6877601 := bstep (se 2 (by rfl) ⟨2579100, by rfl⟩ : syracuseStep 6877601 = 5158201) B5158201
theorem B4585067 : Blo 2037435 4585067 := bstep (se 1 (by rfl) ⟨3438800, by rfl⟩ : syracuseStep 4585067 = 6877601) B6877601
theorem B3056711 : Blo 2037435 3056711 := bstep (se 1 (by rfl) ⟨2292533, by rfl⟩ : syracuseStep 3056711 = 4585067) B4585067
theorem B2037807 : Blo 2037435 2037807 := bstep (se 1 (by rfl) ⟨1528355, by rfl⟩ : syracuseStep 2037807 = 3056711) B3056711
theorem B3056717 : Blo 2037435 3056717 := bbase (se 3 (by rfl) ⟨573134, by rfl⟩ : syracuseStep 3056717 = 1146269) (by norm_num)
theorem B2037811 : Blo 2037435 2037811 := bstep (se 1 (by rfl) ⟨1528358, by rfl⟩ : syracuseStep 2037811 = 3056717) B3056717
theorem B4585085 : Blo 2037435 4585085 := bbase (se 3 (by rfl) ⟨859703, by rfl⟩ : syracuseStep 4585085 = 1719407) (by norm_num)
theorem B3056723 : Blo 2037435 3056723 := bstep (se 1 (by rfl) ⟨2292542, by rfl⟩ : syracuseStep 3056723 = 4585085) B4585085
theorem B2037815 : Blo 2037435 2037815 := bstep (se 1 (by rfl) ⟨1528361, by rfl⟩ : syracuseStep 2037815 = 3056723) B3056723
theorem B3438821 : Blo 2037435 3438821 := bbase (se 4 (by rfl) ⟨322389, by rfl⟩ : syracuseStep 3438821 = 644779) (by norm_num)
theorem B2292547 : Blo 2037435 2292547 := bstep (se 1 (by rfl) ⟨1719410, by rfl⟩ : syracuseStep 2292547 = 3438821) B3438821
theorem B3056729 : Blo 2037435 3056729 := bstep (se 2 (by rfl) ⟨1146273, by rfl⟩ : syracuseStep 3056729 = 2292547) B2292547
theorem B2037819 : Blo 2037435 2037819 := bstep (se 1 (by rfl) ⟨1528364, by rfl⟩ : syracuseStep 2037819 = 3056729) B3056729
theorem B4896301 : Blo 2037435 4896301 := bbase (se 3 (by rfl) ⟨918056, by rfl⟩ : syracuseStep 4896301 = 1836113) (by norm_num)
theorem B6528401 : Blo 2037435 6528401 := bstep (se 2 (by rfl) ⟨2448150, by rfl⟩ : syracuseStep 6528401 = 4896301) B4896301
theorem B4352267 : Blo 2037435 4352267 := bstep (se 1 (by rfl) ⟨3264200, by rfl⟩ : syracuseStep 4352267 = 6528401) B6528401
theorem B2901511 : Blo 2037435 2901511 := bstep (se 1 (by rfl) ⟨2176133, by rfl⟩ : syracuseStep 2901511 = 4352267) B4352267
theorem B15474725 : Blo 2037435 15474725 := bstep (se 4 (by rfl) ⟨1450755, by rfl⟩ : syracuseStep 15474725 = 2901511) B2901511
theorem B10316483 : Blo 2037435 10316483 := bstep (se 1 (by rfl) ⟨7737362, by rfl⟩ : syracuseStep 10316483 = 15474725) B15474725
theorem B6877655 : Blo 2037435 6877655 := bstep (se 1 (by rfl) ⟨5158241, by rfl⟩ : syracuseStep 6877655 = 10316483) B10316483
theorem B4585103 : Blo 2037435 4585103 := bstep (se 1 (by rfl) ⟨3438827, by rfl⟩ : syracuseStep 4585103 = 6877655) B6877655
theorem B3056735 : Blo 2037435 3056735 := bstep (se 1 (by rfl) ⟨2292551, by rfl⟩ : syracuseStep 3056735 = 4585103) B4585103
theorem B2037823 : Blo 2037435 2037823 := bstep (se 1 (by rfl) ⟨1528367, by rfl⟩ : syracuseStep 2037823 = 3056735) B3056735
theorem B3056741 : Blo 2037435 3056741 := bbase (se 4 (by rfl) ⟨286569, by rfl⟩ : syracuseStep 3056741 = 573139) (by norm_num)
theorem B2037827 : Blo 2037435 2037827 := bstep (se 1 (by rfl) ⟨1528370, by rfl⟩ : syracuseStep 2037827 = 3056741) B3056741
theorem B4352285 : Blo 2037435 4352285 := bbase (se 3 (by rfl) ⟨816053, by rfl⟩ : syracuseStep 4352285 = 1632107) (by norm_num)
theorem B2901523 : Blo 2037435 2901523 := bstep (se 1 (by rfl) ⟨2176142, by rfl⟩ : syracuseStep 2901523 = 4352285) B4352285
theorem B3868697 : Blo 2037435 3868697 := bstep (se 2 (by rfl) ⟨1450761, by rfl⟩ : syracuseStep 3868697 = 2901523) B2901523
theorem B2579131 : Blo 2037435 2579131 := bstep (se 1 (by rfl) ⟨1934348, by rfl⟩ : syracuseStep 2579131 = 3868697) B3868697
theorem B3438841 : Blo 2037435 3438841 := bstep (se 2 (by rfl) ⟨1289565, by rfl⟩ : syracuseStep 3438841 = 2579131) B2579131
theorem B4585121 : Blo 2037435 4585121 := bstep (se 2 (by rfl) ⟨1719420, by rfl⟩ : syracuseStep 4585121 = 3438841) B3438841
theorem B3056747 : Blo 2037435 3056747 := bstep (se 1 (by rfl) ⟨2292560, by rfl⟩ : syracuseStep 3056747 = 4585121) B4585121
theorem B2037831 : Blo 2037435 2037831 := bstep (se 1 (by rfl) ⟨1528373, by rfl⟩ : syracuseStep 2037831 = 3056747) B3056747
theorem B2292565 : Blo 2037435 2292565 := bbase (se 9 (by rfl) ⟨6716, by rfl⟩ : syracuseStep 2292565 = 13433) (by norm_num)
theorem B3056753 : Blo 2037435 3056753 := bstep (se 2 (by rfl) ⟨1146282, by rfl⟩ : syracuseStep 3056753 = 2292565) B2292565
theorem B2037835 : Blo 2037435 2037835 := bstep (se 1 (by rfl) ⟨1528376, by rfl⟩ : syracuseStep 2037835 = 3056753) B3056753
theorem B2579141 : Blo 2037435 2579141 := bbase (se 4 (by rfl) ⟨241794, by rfl⟩ : syracuseStep 2579141 = 483589) (by norm_num)
theorem B6877709 : Blo 2037435 6877709 := bstep (se 3 (by rfl) ⟨1289570, by rfl⟩ : syracuseStep 6877709 = 2579141) B2579141
theorem B4585139 : Blo 2037435 4585139 := bstep (se 1 (by rfl) ⟨3438854, by rfl⟩ : syracuseStep 4585139 = 6877709) B6877709
theorem B3056759 : Blo 2037435 3056759 := bstep (se 1 (by rfl) ⟨2292569, by rfl⟩ : syracuseStep 3056759 = 4585139) B4585139
theorem B2037839 : Blo 2037435 2037839 := bstep (se 1 (by rfl) ⟨1528379, by rfl⟩ : syracuseStep 2037839 = 3056759) B3056759
theorem B3056765 : Blo 2037435 3056765 := bbase (se 3 (by rfl) ⟨573143, by rfl⟩ : syracuseStep 3056765 = 1146287) (by norm_num)
theorem B2037843 : Blo 2037435 2037843 := bstep (se 1 (by rfl) ⟨1528382, by rfl⟩ : syracuseStep 2037843 = 3056765) B3056765
theorem B4585157 : Blo 2037435 4585157 := bbase (se 4 (by rfl) ⟨429858, by rfl⟩ : syracuseStep 4585157 = 859717) (by norm_num)
theorem B3056771 : Blo 2037435 3056771 := bstep (se 1 (by rfl) ⟨2292578, by rfl⟩ : syracuseStep 3056771 = 4585157) B4585157
theorem B2037847 : Blo 2037435 2037847 := bstep (se 1 (by rfl) ⟨1528385, by rfl⟩ : syracuseStep 2037847 = 3056771) B3056771
theorem B16750709 : Blo 2037435 16750709 := bbase (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) (by norm_num)
theorem B11167139 : Blo 2037435 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B7444759 : Blo 2037435 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B9926345 : Blo 2037435 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B26470253 : Blo 2037435 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B17646835 : Blo 2037435 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B23529113 : Blo 2037435 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B15686075 : Blo 2037435 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B41829533 : Blo 2037435 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B27886355 : Blo 2037435 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B18590903 : Blo 2037435 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B12393935 : Blo 2037435 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B8262623 : Blo 2037435 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B5508415 : Blo 2037435 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B29378213 : Blo 2037435 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B19585475 : Blo 2037435 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B13056983 : Blo 2037435 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B8704655 : Blo 2037435 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B5803103 : Blo 2037435 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B3868735 : Blo 2037435 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B5158313 : Blo 2037435 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B3438875 : Blo 2037435 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B2292583 : Blo 2037435 2292583 := bstep (se 1 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 2292583 = 3438875) B3438875
theorem B3056777 : Blo 2037435 3056777 := bstep (se 2 (by rfl) ⟨1146291, by rfl⟩ : syracuseStep 3056777 = 2292583) B2292583
theorem B2037851 : Blo 2037435 2037851 := bstep (se 1 (by rfl) ⟨1528388, by rfl⟩ : syracuseStep 2037851 = 3056777) B3056777
theorem B10316645 : Blo 2037435 10316645 := bbase (se 4 (by rfl) ⟨967185, by rfl⟩ : syracuseStep 10316645 = 1934371) (by norm_num)
theorem B6877763 : Blo 2037435 6877763 := bstep (se 1 (by rfl) ⟨5158322, by rfl⟩ : syracuseStep 6877763 = 10316645) B10316645
theorem B4585175 : Blo 2037435 4585175 := bstep (se 1 (by rfl) ⟨3438881, by rfl⟩ : syracuseStep 4585175 = 6877763) B6877763
theorem B3056783 : Blo 2037435 3056783 := bstep (se 1 (by rfl) ⟨2292587, by rfl⟩ : syracuseStep 3056783 = 4585175) B4585175
theorem B2037855 : Blo 2037435 2037855 := bstep (se 1 (by rfl) ⟨1528391, by rfl⟩ : syracuseStep 2037855 = 3056783) B3056783
theorem B3056789 : Blo 2037435 3056789 := bbase (se 6 (by rfl) ⟨71643, by rfl⟩ : syracuseStep 3056789 = 143287) (by norm_num)
theorem B2037859 : Blo 2037435 2037859 := bstep (se 1 (by rfl) ⟨1528394, by rfl⟩ : syracuseStep 2037859 = 3056789) B3056789
theorem B4896397 : Blo 2037435 4896397 := bbase (se 3 (by rfl) ⟨918074, by rfl⟩ : syracuseStep 4896397 = 1836149) (by norm_num)
theorem B6528529 : Blo 2037435 6528529 := bstep (se 2 (by rfl) ⟨2448198, by rfl⟩ : syracuseStep 6528529 = 4896397) B4896397
theorem B8704705 : Blo 2037435 8704705 := bstep (se 2 (by rfl) ⟨3264264, by rfl⟩ : syracuseStep 8704705 = 6528529) B6528529
theorem B11606273 : Blo 2037435 11606273 := bstep (se 2 (by rfl) ⟨4352352, by rfl⟩ : syracuseStep 11606273 = 8704705) B8704705
theorem B7737515 : Blo 2037435 7737515 := bstep (se 1 (by rfl) ⟨5803136, by rfl⟩ : syracuseStep 7737515 = 11606273) B11606273
theorem B5158343 : Blo 2037435 5158343 := bstep (se 1 (by rfl) ⟨3868757, by rfl⟩ : syracuseStep 5158343 = 7737515) B7737515
theorem B3438895 : Blo 2037435 3438895 := bstep (se 1 (by rfl) ⟨2579171, by rfl⟩ : syracuseStep 3438895 = 5158343) B5158343
theorem B4585193 : Blo 2037435 4585193 := bstep (se 2 (by rfl) ⟨1719447, by rfl⟩ : syracuseStep 4585193 = 3438895) B3438895
theorem B3056795 : Blo 2037435 3056795 := bstep (se 1 (by rfl) ⟨2292596, by rfl⟩ : syracuseStep 3056795 = 4585193) B4585193
theorem B2037863 : Blo 2037435 2037863 := bstep (se 1 (by rfl) ⟨1528397, by rfl⟩ : syracuseStep 2037863 = 3056795) B3056795
theorem B2292601 : Blo 2037435 2292601 := bbase (se 2 (by rfl) ⟨859725, by rfl⟩ : syracuseStep 2292601 = 1719451) (by norm_num)
theorem B3056801 : Blo 2037435 3056801 := bstep (se 2 (by rfl) ⟨1146300, by rfl⟩ : syracuseStep 3056801 = 2292601) B2292601
theorem B2037867 : Blo 2037435 2037867 := bstep (se 1 (by rfl) ⟨1528400, by rfl⟩ : syracuseStep 2037867 = 3056801) B3056801
theorem B13057109 : Blo 2037435 13057109 := bbase (se 8 (by rfl) ⟨76506, by rfl⟩ : syracuseStep 13057109 = 153013) (by norm_num)
theorem B8704739 : Blo 2037435 8704739 := bstep (se 1 (by rfl) ⟨6528554, by rfl⟩ : syracuseStep 8704739 = 13057109) B13057109
theorem B5803159 : Blo 2037435 5803159 := bstep (se 1 (by rfl) ⟨4352369, by rfl⟩ : syracuseStep 5803159 = 8704739) B8704739
theorem B7737545 : Blo 2037435 7737545 := bstep (se 2 (by rfl) ⟨2901579, by rfl⟩ : syracuseStep 7737545 = 5803159) B5803159
theorem B5158363 : Blo 2037435 5158363 := bstep (se 1 (by rfl) ⟨3868772, by rfl⟩ : syracuseStep 5158363 = 7737545) B7737545
theorem B6877817 : Blo 2037435 6877817 := bstep (se 2 (by rfl) ⟨2579181, by rfl⟩ : syracuseStep 6877817 = 5158363) B5158363
theorem B4585211 : Blo 2037435 4585211 := bstep (se 1 (by rfl) ⟨3438908, by rfl⟩ : syracuseStep 4585211 = 6877817) B6877817
theorem B3056807 : Blo 2037435 3056807 := bstep (se 1 (by rfl) ⟨2292605, by rfl⟩ : syracuseStep 3056807 = 4585211) B4585211
theorem B2037871 : Blo 2037435 2037871 := bstep (se 1 (by rfl) ⟨1528403, by rfl⟩ : syracuseStep 2037871 = 3056807) B3056807
theorem B3056813 : Blo 2037435 3056813 := bbase (se 3 (by rfl) ⟨573152, by rfl⟩ : syracuseStep 3056813 = 1146305) (by norm_num)
theorem B2037875 : Blo 2037435 2037875 := bstep (se 1 (by rfl) ⟨1528406, by rfl⟩ : syracuseStep 2037875 = 3056813) B3056813
theorem B4585229 : Blo 2037435 4585229 := bbase (se 3 (by rfl) ⟨859730, by rfl⟩ : syracuseStep 4585229 = 1719461) (by norm_num)
theorem B3056819 : Blo 2037435 3056819 := bstep (se 1 (by rfl) ⟨2292614, by rfl⟩ : syracuseStep 3056819 = 4585229) B4585229
theorem B2037879 : Blo 2037435 2037879 := bstep (se 1 (by rfl) ⟨1528409, by rfl⟩ : syracuseStep 2037879 = 3056819) B3056819
theorem B2579197 : Blo 2037435 2579197 := bbase (se 3 (by rfl) ⟨483599, by rfl⟩ : syracuseStep 2579197 = 967199) (by norm_num)
theorem B3438929 : Blo 2037435 3438929 := bstep (se 2 (by rfl) ⟨1289598, by rfl⟩ : syracuseStep 3438929 = 2579197) B2579197
theorem B2292619 : Blo 2037435 2292619 := bstep (se 1 (by rfl) ⟨1719464, by rfl⟩ : syracuseStep 2292619 = 3438929) B3438929
theorem B3056825 : Blo 2037435 3056825 := bstep (se 2 (by rfl) ⟨1146309, by rfl⟩ : syracuseStep 3056825 = 2292619) B2292619
theorem B2037883 : Blo 2037435 2037883 := bstep (se 1 (by rfl) ⟨1528412, by rfl⟩ : syracuseStep 2037883 = 3056825) B3056825
theorem B3672341 : Blo 2037435 3672341 := bbase (se 6 (by rfl) ⟨86070, by rfl⟩ : syracuseStep 3672341 = 172141) (by norm_num)
theorem B2448227 : Blo 2037435 2448227 := bstep (se 1 (by rfl) ⟨1836170, by rfl⟩ : syracuseStep 2448227 = 3672341) B3672341
theorem B6528605 : Blo 2037435 6528605 := bstep (se 3 (by rfl) ⟨1224113, by rfl⟩ : syracuseStep 6528605 = 2448227) B2448227
theorem B17409613 : Blo 2037435 17409613 := bstep (se 3 (by rfl) ⟨3264302, by rfl⟩ : syracuseStep 17409613 = 6528605) B6528605
theorem B23212817 : Blo 2037435 23212817 := bstep (se 2 (by rfl) ⟨8704806, by rfl⟩ : syracuseStep 23212817 = 17409613) B17409613
theorem B15475211 : Blo 2037435 15475211 := bstep (se 1 (by rfl) ⟨11606408, by rfl⟩ : syracuseStep 15475211 = 23212817) B23212817
theorem B10316807 : Blo 2037435 10316807 := bstep (se 1 (by rfl) ⟨7737605, by rfl⟩ : syracuseStep 10316807 = 15475211) B15475211
theorem B6877871 : Blo 2037435 6877871 := bstep (se 1 (by rfl) ⟨5158403, by rfl⟩ : syracuseStep 6877871 = 10316807) B10316807
theorem B4585247 : Blo 2037435 4585247 := bstep (se 1 (by rfl) ⟨3438935, by rfl⟩ : syracuseStep 4585247 = 6877871) B6877871
theorem B3056831 : Blo 2037435 3056831 := bstep (se 1 (by rfl) ⟨2292623, by rfl⟩ : syracuseStep 3056831 = 4585247) B4585247
theorem B2037887 : Blo 2037435 2037887 := bstep (se 1 (by rfl) ⟨1528415, by rfl⟩ : syracuseStep 2037887 = 3056831) B3056831
theorem B3056837 : Blo 2037435 3056837 := bbase (se 4 (by rfl) ⟨286578, by rfl⟩ : syracuseStep 3056837 = 573157) (by norm_num)
theorem B2037891 : Blo 2037435 2037891 := bstep (se 1 (by rfl) ⟨1528418, by rfl⟩ : syracuseStep 2037891 = 3056837) B3056837
theorem B3438949 : Blo 2037435 3438949 := bbase (se 4 (by rfl) ⟨322401, by rfl⟩ : syracuseStep 3438949 = 644803) (by norm_num)
theorem B4585265 : Blo 2037435 4585265 := bstep (se 2 (by rfl) ⟨1719474, by rfl⟩ : syracuseStep 4585265 = 3438949) B3438949
theorem B3056843 : Blo 2037435 3056843 := bstep (se 1 (by rfl) ⟨2292632, by rfl⟩ : syracuseStep 3056843 = 4585265) B4585265
theorem B2037895 : Blo 2037435 2037895 := bstep (se 1 (by rfl) ⟨1528421, by rfl⟩ : syracuseStep 2037895 = 3056843) B3056843
theorem B2292637 : Blo 2037435 2292637 := bbase (se 3 (by rfl) ⟨429869, by rfl⟩ : syracuseStep 2292637 = 859739) (by norm_num)
theorem B3056849 : Blo 2037435 3056849 := bstep (se 2 (by rfl) ⟨1146318, by rfl⟩ : syracuseStep 3056849 = 2292637) B2292637
theorem B2037899 : Blo 2037435 2037899 := bstep (se 1 (by rfl) ⟨1528424, by rfl⟩ : syracuseStep 2037899 = 3056849) B3056849
theorem B6877925 : Blo 2037435 6877925 := bbase (se 4 (by rfl) ⟨644805, by rfl⟩ : syracuseStep 6877925 = 1289611) (by norm_num)
theorem B4585283 : Blo 2037435 4585283 := bstep (se 1 (by rfl) ⟨3438962, by rfl⟩ : syracuseStep 4585283 = 6877925) B6877925
theorem B3056855 : Blo 2037435 3056855 := bstep (se 1 (by rfl) ⟨2292641, by rfl⟩ : syracuseStep 3056855 = 4585283) B4585283
theorem B2037903 : Blo 2037435 2037903 := bstep (se 1 (by rfl) ⟨1528427, by rfl⟩ : syracuseStep 2037903 = 3056855) B3056855
theorem B3056861 : Blo 2037435 3056861 := bbase (se 3 (by rfl) ⟨573161, by rfl⟩ : syracuseStep 3056861 = 1146323) (by norm_num)
theorem B2037907 : Blo 2037435 2037907 := bstep (se 1 (by rfl) ⟨1528430, by rfl⟩ : syracuseStep 2037907 = 3056861) B3056861
theorem B4585301 : Blo 2037435 4585301 := bbase (se 9 (by rfl) ⟨13433, by rfl⟩ : syracuseStep 4585301 = 26867) (by norm_num)
theorem B3056867 : Blo 2037435 3056867 := bstep (se 1 (by rfl) ⟨2292650, by rfl⟩ : syracuseStep 3056867 = 4585301) B4585301
theorem B2037911 : Blo 2037435 2037911 := bstep (se 1 (by rfl) ⟨1528433, by rfl⟩ : syracuseStep 2037911 = 3056867) B3056867
theorem B5803285 : Blo 2037435 5803285 := bbase (se 6 (by rfl) ⟨136014, by rfl⟩ : syracuseStep 5803285 = 272029) (by norm_num)
theorem B7737713 : Blo 2037435 7737713 := bstep (se 2 (by rfl) ⟨2901642, by rfl⟩ : syracuseStep 7737713 = 5803285) B5803285
theorem B5158475 : Blo 2037435 5158475 := bstep (se 1 (by rfl) ⟨3868856, by rfl⟩ : syracuseStep 5158475 = 7737713) B7737713
theorem B3438983 : Blo 2037435 3438983 := bstep (se 1 (by rfl) ⟨2579237, by rfl⟩ : syracuseStep 3438983 = 5158475) B5158475
theorem B2292655 : Blo 2037435 2292655 := bstep (se 1 (by rfl) ⟨1719491, by rfl⟩ : syracuseStep 2292655 = 3438983) B3438983
theorem B3056873 : Blo 2037435 3056873 := bstep (se 2 (by rfl) ⟨1146327, by rfl⟩ : syracuseStep 3056873 = 2292655) B2292655
theorem B2037915 : Blo 2037435 2037915 := bstep (se 1 (by rfl) ⟨1528436, by rfl⟩ : syracuseStep 2037915 = 3056873) B3056873
theorem B88137557 : Blo 2037435 88137557 := bbase (se 9 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 88137557 = 516431) (by norm_num)
theorem B58758371 : Blo 2037435 58758371 := bstep (se 1 (by rfl) ⟨44068778, by rfl⟩ : syracuseStep 58758371 = 88137557) B88137557
theorem B39172247 : Blo 2037435 39172247 := bstep (se 1 (by rfl) ⟨29379185, by rfl⟩ : syracuseStep 39172247 = 58758371) B58758371
theorem B26114831 : Blo 2037435 26114831 := bstep (se 1 (by rfl) ⟨19586123, by rfl⟩ : syracuseStep 26114831 = 39172247) B39172247
theorem B17409887 : Blo 2037435 17409887 := bstep (se 1 (by rfl) ⟨13057415, by rfl⟩ : syracuseStep 17409887 = 26114831) B26114831
theorem B11606591 : Blo 2037435 11606591 := bstep (se 1 (by rfl) ⟨8704943, by rfl⟩ : syracuseStep 11606591 = 17409887) B17409887
theorem B7737727 : Blo 2037435 7737727 := bstep (se 1 (by rfl) ⟨5803295, by rfl⟩ : syracuseStep 7737727 = 11606591) B11606591
theorem B10316969 : Blo 2037435 10316969 := bstep (se 2 (by rfl) ⟨3868863, by rfl⟩ : syracuseStep 10316969 = 7737727) B7737727
theorem B6877979 : Blo 2037435 6877979 := bstep (se 1 (by rfl) ⟨5158484, by rfl⟩ : syracuseStep 6877979 = 10316969) B10316969
theorem B4585319 : Blo 2037435 4585319 := bstep (se 1 (by rfl) ⟨3438989, by rfl⟩ : syracuseStep 4585319 = 6877979) B6877979
theorem B3056879 : Blo 2037435 3056879 := bstep (se 1 (by rfl) ⟨2292659, by rfl⟩ : syracuseStep 3056879 = 4585319) B4585319
theorem B2037919 : Blo 2037435 2037919 := bstep (se 1 (by rfl) ⟨1528439, by rfl⟩ : syracuseStep 2037919 = 3056879) B3056879
theorem B3056885 : Blo 2037435 3056885 := bbase (se 5 (by rfl) ⟨143291, by rfl⟩ : syracuseStep 3056885 = 286583) (by norm_num)
theorem B2037923 : Blo 2037435 2037923 := bstep (se 1 (by rfl) ⟨1528442, by rfl⟩ : syracuseStep 2037923 = 3056885) B3056885
theorem B2205937 : Blo 2037435 2205937 := bbase (se 2 (by rfl) ⟨827226, by rfl⟩ : syracuseStep 2205937 = 1654453) (by norm_num)
theorem B11764997 : Blo 2037435 11764997 := bstep (se 4 (by rfl) ⟨1102968, by rfl⟩ : syracuseStep 11764997 = 2205937) B2205937
theorem B7843331 : Blo 2037435 7843331 := bstep (se 1 (by rfl) ⟨5882498, by rfl⟩ : syracuseStep 7843331 = 11764997) B11764997
theorem B5228887 : Blo 2037435 5228887 := bstep (se 1 (by rfl) ⟨3921665, by rfl⟩ : syracuseStep 5228887 = 7843331) B7843331
theorem B6971849 : Blo 2037435 6971849 := bstep (se 2 (by rfl) ⟨2614443, by rfl⟩ : syracuseStep 6971849 = 5228887) B5228887
theorem B4647899 : Blo 2037435 4647899 := bstep (se 1 (by rfl) ⟨3485924, by rfl⟩ : syracuseStep 4647899 = 6971849) B6971849
theorem B12394397 : Blo 2037435 12394397 := bstep (se 3 (by rfl) ⟨2323949, by rfl⟩ : syracuseStep 12394397 = 4647899) B4647899
theorem B8262931 : Blo 2037435 8262931 := bstep (se 1 (by rfl) ⟨6197198, by rfl⟩ : syracuseStep 8262931 = 12394397) B12394397
theorem B11017241 : Blo 2037435 11017241 := bstep (se 2 (by rfl) ⟨4131465, by rfl⟩ : syracuseStep 11017241 = 8262931) B8262931
theorem B7344827 : Blo 2037435 7344827 := bstep (se 1 (by rfl) ⟨5508620, by rfl⟩ : syracuseStep 7344827 = 11017241) B11017241
theorem B4896551 : Blo 2037435 4896551 := bstep (se 1 (by rfl) ⟨3672413, by rfl⟩ : syracuseStep 4896551 = 7344827) B7344827
theorem B13057469 : Blo 2037435 13057469 := bstep (se 3 (by rfl) ⟨2448275, by rfl⟩ : syracuseStep 13057469 = 4896551) B4896551
theorem B8704979 : Blo 2037435 8704979 := bstep (se 1 (by rfl) ⟨6528734, by rfl⟩ : syracuseStep 8704979 = 13057469) B13057469
theorem B5803319 : Blo 2037435 5803319 := bstep (se 1 (by rfl) ⟨4352489, by rfl⟩ : syracuseStep 5803319 = 8704979) B8704979
theorem B3868879 : Blo 2037435 3868879 := bstep (se 1 (by rfl) ⟨2901659, by rfl⟩ : syracuseStep 3868879 = 5803319) B5803319
theorem B5158505 : Blo 2037435 5158505 := bstep (se 2 (by rfl) ⟨1934439, by rfl⟩ : syracuseStep 5158505 = 3868879) B3868879
theorem B3439003 : Blo 2037435 3439003 := bstep (se 1 (by rfl) ⟨2579252, by rfl⟩ : syracuseStep 3439003 = 5158505) B5158505
theorem B4585337 : Blo 2037435 4585337 := bstep (se 2 (by rfl) ⟨1719501, by rfl⟩ : syracuseStep 4585337 = 3439003) B3439003
theorem B3056891 : Blo 2037435 3056891 := bstep (se 1 (by rfl) ⟨2292668, by rfl⟩ : syracuseStep 3056891 = 4585337) B4585337
theorem B2037927 : Blo 2037435 2037927 := bstep (se 1 (by rfl) ⟨1528445, by rfl⟩ : syracuseStep 2037927 = 3056891) B3056891
theorem B2292673 : Blo 2037435 2292673 := bbase (se 2 (by rfl) ⟨859752, by rfl⟩ : syracuseStep 2292673 = 1719505) (by norm_num)
theorem B3056897 : Blo 2037435 3056897 := bstep (se 2 (by rfl) ⟨1146336, by rfl⟩ : syracuseStep 3056897 = 2292673) B2292673
theorem B2037931 : Blo 2037435 2037931 := bstep (se 1 (by rfl) ⟨1528448, by rfl⟩ : syracuseStep 2037931 = 3056897) B3056897
theorem B5158525 : Blo 2037435 5158525 := bbase (se 3 (by rfl) ⟨967223, by rfl⟩ : syracuseStep 5158525 = 1934447) (by norm_num)
theorem B6878033 : Blo 2037435 6878033 := bstep (se 2 (by rfl) ⟨2579262, by rfl⟩ : syracuseStep 6878033 = 5158525) B5158525
theorem B4585355 : Blo 2037435 4585355 := bstep (se 1 (by rfl) ⟨3439016, by rfl⟩ : syracuseStep 4585355 = 6878033) B6878033
theorem B3056903 : Blo 2037435 3056903 := bstep (se 1 (by rfl) ⟨2292677, by rfl⟩ : syracuseStep 3056903 = 4585355) B4585355
theorem B2037935 : Blo 2037435 2037935 := bstep (se 1 (by rfl) ⟨1528451, by rfl⟩ : syracuseStep 2037935 = 3056903) B3056903
theorem B3056909 : Blo 2037435 3056909 := bbase (se 3 (by rfl) ⟨573170, by rfl⟩ : syracuseStep 3056909 = 1146341) (by norm_num)
theorem B2037939 : Blo 2037435 2037939 := bstep (se 1 (by rfl) ⟨1528454, by rfl⟩ : syracuseStep 2037939 = 3056909) B3056909
theorem B4585373 : Blo 2037435 4585373 := bbase (se 3 (by rfl) ⟨859757, by rfl⟩ : syracuseStep 4585373 = 1719515) (by norm_num)
theorem B3056915 : Blo 2037435 3056915 := bstep (se 1 (by rfl) ⟨2292686, by rfl⟩ : syracuseStep 3056915 = 4585373) B4585373
theorem B2037943 : Blo 2037435 2037943 := bstep (se 1 (by rfl) ⟨1528457, by rfl⟩ : syracuseStep 2037943 = 3056915) B3056915
theorem B3439037 : Blo 2037435 3439037 := bbase (se 3 (by rfl) ⟨644819, by rfl⟩ : syracuseStep 3439037 = 1289639) (by norm_num)
theorem B2292691 : Blo 2037435 2292691 := bstep (se 1 (by rfl) ⟨1719518, by rfl⟩ : syracuseStep 2292691 = 3439037) B3439037
theorem B3056921 : Blo 2037435 3056921 := bstep (se 2 (by rfl) ⟨1146345, by rfl⟩ : syracuseStep 3056921 = 2292691) B2292691
theorem B2037947 : Blo 2037435 2037947 := bstep (se 1 (by rfl) ⟨1528460, by rfl⟩ : syracuseStep 2037947 = 3056921) B3056921
theorem B11606773 : Blo 2037435 11606773 := bbase (se 5 (by rfl) ⟨544067, by rfl⟩ : syracuseStep 11606773 = 1088135) (by norm_num)
theorem B15475697 : Blo 2037435 15475697 := bstep (se 2 (by rfl) ⟨5803386, by rfl⟩ : syracuseStep 15475697 = 11606773) B11606773
theorem B10317131 : Blo 2037435 10317131 := bstep (se 1 (by rfl) ⟨7737848, by rfl⟩ : syracuseStep 10317131 = 15475697) B15475697
theorem B6878087 : Blo 2037435 6878087 := bstep (se 1 (by rfl) ⟨5158565, by rfl⟩ : syracuseStep 6878087 = 10317131) B10317131
theorem B4585391 : Blo 2037435 4585391 := bstep (se 1 (by rfl) ⟨3439043, by rfl⟩ : syracuseStep 4585391 = 6878087) B6878087
theorem B3056927 : Blo 2037435 3056927 := bstep (se 1 (by rfl) ⟨2292695, by rfl⟩ : syracuseStep 3056927 = 4585391) B4585391
theorem B2037951 : Blo 2037435 2037951 := bstep (se 1 (by rfl) ⟨1528463, by rfl⟩ : syracuseStep 2037951 = 3056927) B3056927
theorem B3056933 : Blo 2037435 3056933 := bbase (se 4 (by rfl) ⟨286587, by rfl⟩ : syracuseStep 3056933 = 573175) (by norm_num)
theorem B2037955 : Blo 2037435 2037955 := bstep (se 1 (by rfl) ⟨1528466, by rfl⟩ : syracuseStep 2037955 = 3056933) B3056933
theorem B2579293 : Blo 2037435 2579293 := bbase (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) (by norm_num)
theorem B3439057 : Blo 2037435 3439057 := bstep (se 2 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 3439057 = 2579293) B2579293
theorem B4585409 : Blo 2037435 4585409 := bstep (se 2 (by rfl) ⟨1719528, by rfl⟩ : syracuseStep 4585409 = 3439057) B3439057
theorem B3056939 : Blo 2037435 3056939 := bstep (se 1 (by rfl) ⟨2292704, by rfl⟩ : syracuseStep 3056939 = 4585409) B4585409
theorem B2037959 : Blo 2037435 2037959 := bstep (se 1 (by rfl) ⟨1528469, by rfl⟩ : syracuseStep 2037959 = 3056939) B3056939
theorem B2292709 : Blo 2037435 2292709 := bbase (se 4 (by rfl) ⟨214941, by rfl⟩ : syracuseStep 2292709 = 429883) (by norm_num)
theorem B3056945 : Blo 2037435 3056945 := bstep (se 2 (by rfl) ⟨1146354, by rfl⟩ : syracuseStep 3056945 = 2292709) B2292709
theorem B2037963 : Blo 2037435 2037963 := bstep (se 1 (by rfl) ⟨1528472, by rfl⟩ : syracuseStep 2037963 = 3056945) B3056945
theorem B33052373 : Blo 2037435 33052373 := bbase (se 7 (by rfl) ⟨387332, by rfl⟩ : syracuseStep 33052373 = 774665) (by norm_num)
theorem B22034915 : Blo 2037435 22034915 := bstep (se 1 (by rfl) ⟨16526186, by rfl⟩ : syracuseStep 22034915 = 33052373) B33052373
theorem B14689943 : Blo 2037435 14689943 := bstep (se 1 (by rfl) ⟨11017457, by rfl⟩ : syracuseStep 14689943 = 22034915) B22034915
theorem B9793295 : Blo 2037435 9793295 := bstep (se 1 (by rfl) ⟨7344971, by rfl⟩ : syracuseStep 9793295 = 14689943) B14689943
theorem B6528863 : Blo 2037435 6528863 := bstep (se 1 (by rfl) ⟨4896647, by rfl⟩ : syracuseStep 6528863 = 9793295) B9793295
theorem B4352575 : Blo 2037435 4352575 := bstep (se 1 (by rfl) ⟨3264431, by rfl⟩ : syracuseStep 4352575 = 6528863) B6528863
theorem B5803433 : Blo 2037435 5803433 := bstep (se 2 (by rfl) ⟨2176287, by rfl⟩ : syracuseStep 5803433 = 4352575) B4352575
theorem B3868955 : Blo 2037435 3868955 := bstep (se 1 (by rfl) ⟨2901716, by rfl⟩ : syracuseStep 3868955 = 5803433) B5803433
theorem B2579303 : Blo 2037435 2579303 := bstep (se 1 (by rfl) ⟨1934477, by rfl⟩ : syracuseStep 2579303 = 3868955) B3868955
theorem B6878141 : Blo 2037435 6878141 := bstep (se 3 (by rfl) ⟨1289651, by rfl⟩ : syracuseStep 6878141 = 2579303) B2579303
theorem B4585427 : Blo 2037435 4585427 := bstep (se 1 (by rfl) ⟨3439070, by rfl⟩ : syracuseStep 4585427 = 6878141) B6878141
theorem B3056951 : Blo 2037435 3056951 := bstep (se 1 (by rfl) ⟨2292713, by rfl⟩ : syracuseStep 3056951 = 4585427) B4585427
theorem B2037967 : Blo 2037435 2037967 := bstep (se 1 (by rfl) ⟨1528475, by rfl⟩ : syracuseStep 2037967 = 3056951) B3056951
theorem B3056957 : Blo 2037435 3056957 := bbase (se 3 (by rfl) ⟨573179, by rfl⟩ : syracuseStep 3056957 = 1146359) (by norm_num)
theorem B2037971 : Blo 2037435 2037971 := bstep (se 1 (by rfl) ⟨1528478, by rfl⟩ : syracuseStep 2037971 = 3056957) B3056957
theorem B4585445 : Blo 2037435 4585445 := bbase (se 4 (by rfl) ⟨429885, by rfl⟩ : syracuseStep 4585445 = 859771) (by norm_num)
theorem B3056963 : Blo 2037435 3056963 := bstep (se 1 (by rfl) ⟨2292722, by rfl⟩ : syracuseStep 3056963 = 4585445) B4585445
theorem B2037975 : Blo 2037435 2037975 := bstep (se 1 (by rfl) ⟨1528481, by rfl⟩ : syracuseStep 2037975 = 3056963) B3056963
theorem B5158637 : Blo 2037435 5158637 := bbase (se 3 (by rfl) ⟨967244, by rfl⟩ : syracuseStep 5158637 = 1934489) (by norm_num)
theorem B3439091 : Blo 2037435 3439091 := bstep (se 1 (by rfl) ⟨2579318, by rfl⟩ : syracuseStep 3439091 = 5158637) B5158637
theorem B2292727 : Blo 2037435 2292727 := bstep (se 1 (by rfl) ⟨1719545, by rfl⟩ : syracuseStep 2292727 = 3439091) B3439091
theorem B3056969 : Blo 2037435 3056969 := bstep (se 2 (by rfl) ⟨1146363, by rfl⟩ : syracuseStep 3056969 = 2292727) B2292727
theorem B2037979 : Blo 2037435 2037979 := bstep (se 1 (by rfl) ⟨1528484, by rfl⟩ : syracuseStep 2037979 = 3056969) B3056969
theorem B5508773 : Blo 2037435 5508773 := bbase (se 4 (by rfl) ⟨516447, by rfl⟩ : syracuseStep 5508773 = 1032895) (by norm_num)
theorem B3672515 : Blo 2037435 3672515 := bstep (se 1 (by rfl) ⟨2754386, by rfl⟩ : syracuseStep 3672515 = 5508773) B5508773
theorem B2448343 : Blo 2037435 2448343 := bstep (se 1 (by rfl) ⟨1836257, by rfl⟩ : syracuseStep 2448343 = 3672515) B3672515
theorem B3264457 : Blo 2037435 3264457 := bstep (se 2 (by rfl) ⟨1224171, by rfl⟩ : syracuseStep 3264457 = 2448343) B2448343
theorem B4352609 : Blo 2037435 4352609 := bstep (se 2 (by rfl) ⟨1632228, by rfl⟩ : syracuseStep 4352609 = 3264457) B3264457
theorem B2901739 : Blo 2037435 2901739 := bstep (se 1 (by rfl) ⟨2176304, by rfl⟩ : syracuseStep 2901739 = 4352609) B4352609
theorem B3868985 : Blo 2037435 3868985 := bstep (se 2 (by rfl) ⟨1450869, by rfl⟩ : syracuseStep 3868985 = 2901739) B2901739
theorem B10317293 : Blo 2037435 10317293 := bstep (se 3 (by rfl) ⟨1934492, by rfl⟩ : syracuseStep 10317293 = 3868985) B3868985
theorem B6878195 : Blo 2037435 6878195 := bstep (se 1 (by rfl) ⟨5158646, by rfl⟩ : syracuseStep 6878195 = 10317293) B10317293
theorem B4585463 : Blo 2037435 4585463 := bstep (se 1 (by rfl) ⟨3439097, by rfl⟩ : syracuseStep 4585463 = 6878195) B6878195
theorem B3056975 : Blo 2037435 3056975 := bstep (se 1 (by rfl) ⟨2292731, by rfl⟩ : syracuseStep 3056975 = 4585463) B4585463
theorem B2037983 : Blo 2037435 2037983 := bstep (se 1 (by rfl) ⟨1528487, by rfl⟩ : syracuseStep 2037983 = 3056975) B3056975
theorem B3056981 : Blo 2037435 3056981 := bbase (se 12 (by rfl) ⟨1119, by rfl⟩ : syracuseStep 3056981 = 2239) (by norm_num)
theorem B2037987 : Blo 2037435 2037987 := bstep (se 1 (by rfl) ⟨1528490, by rfl⟩ : syracuseStep 2037987 = 3056981) B3056981
theorem B2176313 : Blo 2037435 2176313 := bbase (se 2 (by rfl) ⟨816117, by rfl⟩ : syracuseStep 2176313 = 1632235) (by norm_num)
theorem B5803501 : Blo 2037435 5803501 := bstep (se 3 (by rfl) ⟨1088156, by rfl⟩ : syracuseStep 5803501 = 2176313) B2176313
theorem B7738001 : Blo 2037435 7738001 := bstep (se 2 (by rfl) ⟨2901750, by rfl⟩ : syracuseStep 7738001 = 5803501) B5803501
theorem B5158667 : Blo 2037435 5158667 := bstep (se 1 (by rfl) ⟨3869000, by rfl⟩ : syracuseStep 5158667 = 7738001) B7738001
theorem B3439111 : Blo 2037435 3439111 := bstep (se 1 (by rfl) ⟨2579333, by rfl⟩ : syracuseStep 3439111 = 5158667) B5158667
theorem B4585481 : Blo 2037435 4585481 := bstep (se 2 (by rfl) ⟨1719555, by rfl⟩ : syracuseStep 4585481 = 3439111) B3439111
theorem B3056987 : Blo 2037435 3056987 := bstep (se 1 (by rfl) ⟨2292740, by rfl⟩ : syracuseStep 3056987 = 4585481) B4585481
theorem B2037991 : Blo 2037435 2037991 := bstep (se 1 (by rfl) ⟨1528493, by rfl⟩ : syracuseStep 2037991 = 3056987) B3056987
theorem B2292745 : Blo 2037435 2292745 := bbase (se 2 (by rfl) ⟨859779, by rfl⟩ : syracuseStep 2292745 = 1719559) (by norm_num)
theorem B3056993 : Blo 2037435 3056993 := bstep (se 2 (by rfl) ⟨1146372, by rfl⟩ : syracuseStep 3056993 = 2292745) B2292745
theorem B2037995 : Blo 2037435 2037995 := bstep (se 1 (by rfl) ⟨1528496, by rfl⟩ : syracuseStep 2037995 = 3056993) B3056993
theorem B68848597 : Blo 2037435 68848597 := bbase (se 7 (by rfl) ⟨806819, by rfl⟩ : syracuseStep 68848597 = 1613639) (by norm_num)
theorem B91798129 : Blo 2037435 91798129 := bstep (se 2 (by rfl) ⟨34424298, by rfl⟩ : syracuseStep 91798129 = 68848597) B68848597
theorem B489590021 : Blo 2037435 489590021 := bstep (se 4 (by rfl) ⟨45899064, by rfl⟩ : syracuseStep 489590021 = 91798129) B91798129
theorem B326393347 : Blo 2037435 326393347 := bstep (se 1 (by rfl) ⟨244795010, by rfl⟩ : syracuseStep 326393347 = 489590021) B489590021
theorem B435191129 : Blo 2037435 435191129 := bstep (se 2 (by rfl) ⟨163196673, by rfl⟩ : syracuseStep 435191129 = 326393347) B326393347
theorem B290127419 : Blo 2037435 290127419 := bstep (se 1 (by rfl) ⟨217595564, by rfl⟩ : syracuseStep 290127419 = 435191129) B435191129
theorem B193418279 : Blo 2037435 193418279 := bstep (se 1 (by rfl) ⟨145063709, by rfl⟩ : syracuseStep 193418279 = 290127419) B290127419
theorem B128945519 : Blo 2037435 128945519 := bstep (se 1 (by rfl) ⟨96709139, by rfl⟩ : syracuseStep 128945519 = 193418279) B193418279
theorem B85963679 : Blo 2037435 85963679 := bstep (se 1 (by rfl) ⟨64472759, by rfl⟩ : syracuseStep 85963679 = 128945519) B128945519
theorem B57309119 : Blo 2037435 57309119 := bstep (se 1 (by rfl) ⟨42981839, by rfl⟩ : syracuseStep 57309119 = 85963679) B85963679
theorem B38206079 : Blo 2037435 38206079 := bstep (se 1 (by rfl) ⟨28654559, by rfl⟩ : syracuseStep 38206079 = 57309119) B57309119
theorem B25470719 : Blo 2037435 25470719 := bstep (se 1 (by rfl) ⟨19103039, by rfl⟩ : syracuseStep 25470719 = 38206079) B38206079
theorem B16980479 : Blo 2037435 16980479 := bstep (se 1 (by rfl) ⟨12735359, by rfl⟩ : syracuseStep 16980479 = 25470719) B25470719
theorem B11320319 : Blo 2037435 11320319 := bstep (se 1 (by rfl) ⟨8490239, by rfl⟩ : syracuseStep 11320319 = 16980479) B16980479
theorem B7546879 : Blo 2037435 7546879 := bstep (se 1 (by rfl) ⟨5660159, by rfl⟩ : syracuseStep 7546879 = 11320319) B11320319
theorem B10062505 : Blo 2037435 10062505 := bstep (se 2 (by rfl) ⟨3773439, by rfl⟩ : syracuseStep 10062505 = 7546879) B7546879
theorem B13416673 : Blo 2037435 13416673 := bstep (se 2 (by rfl) ⟨5031252, by rfl⟩ : syracuseStep 13416673 = 10062505) B10062505
theorem B17888897 : Blo 2037435 17888897 := bstep (se 2 (by rfl) ⟨6708336, by rfl⟩ : syracuseStep 17888897 = 13416673) B13416673
theorem B47703725 : Blo 2037435 47703725 := bstep (se 3 (by rfl) ⟨8944448, by rfl⟩ : syracuseStep 47703725 = 17888897) B17888897
theorem B31802483 : Blo 2037435 31802483 := bstep (se 1 (by rfl) ⟨23851862, by rfl⟩ : syracuseStep 31802483 = 47703725) B47703725
theorem B84806621 : Blo 2037435 84806621 := bstep (se 3 (by rfl) ⟨15901241, by rfl⟩ : syracuseStep 84806621 = 31802483) B31802483
theorem B56537747 : Blo 2037435 56537747 := bstep (se 1 (by rfl) ⟨42403310, by rfl⟩ : syracuseStep 56537747 = 84806621) B84806621
theorem B37691831 : Blo 2037435 37691831 := bstep (se 1 (by rfl) ⟨28268873, by rfl⟩ : syracuseStep 37691831 = 56537747) B56537747
theorem B100511549 : Blo 2037435 100511549 := bstep (se 3 (by rfl) ⟨18845915, by rfl⟩ : syracuseStep 100511549 = 37691831) B37691831
theorem B67007699 : Blo 2037435 67007699 := bstep (se 1 (by rfl) ⟨50255774, by rfl⟩ : syracuseStep 67007699 = 100511549) B100511549
theorem B44671799 : Blo 2037435 44671799 := bstep (se 1 (by rfl) ⟨33503849, by rfl⟩ : syracuseStep 44671799 = 67007699) B67007699
theorem B29781199 : Blo 2037435 29781199 := bstep (se 1 (by rfl) ⟨22335899, by rfl⟩ : syracuseStep 29781199 = 44671799) B44671799
theorem B39708265 : Blo 2037435 39708265 := bstep (se 2 (by rfl) ⟨14890599, by rfl⟩ : syracuseStep 39708265 = 29781199) B29781199
theorem B52944353 : Blo 2037435 52944353 := bstep (se 2 (by rfl) ⟨19854132, by rfl⟩ : syracuseStep 52944353 = 39708265) B39708265
theorem B35296235 : Blo 2037435 35296235 := bstep (se 1 (by rfl) ⟨26472176, by rfl⟩ : syracuseStep 35296235 = 52944353) B52944353
theorem B23530823 : Blo 2037435 23530823 := bstep (se 1 (by rfl) ⟨17648117, by rfl⟩ : syracuseStep 23530823 = 35296235) B35296235
theorem B15687215 : Blo 2037435 15687215 := bstep (se 1 (by rfl) ⟨11765411, by rfl⟩ : syracuseStep 15687215 = 23530823) B23530823
theorem B10458143 : Blo 2037435 10458143 := bstep (se 1 (by rfl) ⟨7843607, by rfl⟩ : syracuseStep 10458143 = 15687215) B15687215
theorem B6972095 : Blo 2037435 6972095 := bstep (se 1 (by rfl) ⟨5229071, by rfl⟩ : syracuseStep 6972095 = 10458143) B10458143
theorem B4648063 : Blo 2037435 4648063 := bstep (se 1 (by rfl) ⟨3486047, by rfl⟩ : syracuseStep 4648063 = 6972095) B6972095
theorem B6197417 : Blo 2037435 6197417 := bstep (se 2 (by rfl) ⟨2324031, by rfl⟩ : syracuseStep 6197417 = 4648063) B4648063
theorem B4131611 : Blo 2037435 4131611 := bstep (se 1 (by rfl) ⟨3098708, by rfl⟩ : syracuseStep 4131611 = 6197417) B6197417
theorem B2754407 : Blo 2037435 2754407 := bstep (se 1 (by rfl) ⟨2065805, by rfl⟩ : syracuseStep 2754407 = 4131611) B4131611
theorem B7345085 : Blo 2037435 7345085 := bstep (se 3 (by rfl) ⟨1377203, by rfl⟩ : syracuseStep 7345085 = 2754407) B2754407
theorem B19586893 : Blo 2037435 19586893 := bstep (se 3 (by rfl) ⟨3672542, by rfl⟩ : syracuseStep 19586893 = 7345085) B7345085
theorem B26115857 : Blo 2037435 26115857 := bstep (se 2 (by rfl) ⟨9793446, by rfl⟩ : syracuseStep 26115857 = 19586893) B19586893
theorem B17410571 : Blo 2037435 17410571 := bstep (se 1 (by rfl) ⟨13057928, by rfl⟩ : syracuseStep 17410571 = 26115857) B26115857
theorem B11607047 : Blo 2037435 11607047 := bstep (se 1 (by rfl) ⟨8705285, by rfl⟩ : syracuseStep 11607047 = 17410571) B17410571
theorem B7738031 : Blo 2037435 7738031 := bstep (se 1 (by rfl) ⟨5803523, by rfl⟩ : syracuseStep 7738031 = 11607047) B11607047
theorem B5158687 : Blo 2037435 5158687 := bstep (se 1 (by rfl) ⟨3869015, by rfl⟩ : syracuseStep 5158687 = 7738031) B7738031
theorem B6878249 : Blo 2037435 6878249 := bstep (se 2 (by rfl) ⟨2579343, by rfl⟩ : syracuseStep 6878249 = 5158687) B5158687
theorem B4585499 : Blo 2037435 4585499 := bstep (se 1 (by rfl) ⟨3439124, by rfl⟩ : syracuseStep 4585499 = 6878249) B6878249
theorem B3056999 : Blo 2037435 3056999 := bstep (se 1 (by rfl) ⟨2292749, by rfl⟩ : syracuseStep 3056999 = 4585499) B4585499
theorem B2037999 : Blo 2037435 2037999 := bstep (se 1 (by rfl) ⟨1528499, by rfl⟩ : syracuseStep 2037999 = 3056999) B3056999
theorem B3057005 : Blo 2037435 3057005 := bbase (se 3 (by rfl) ⟨573188, by rfl⟩ : syracuseStep 3057005 = 1146377) (by norm_num)
theorem B2038003 : Blo 2037435 2038003 := bstep (se 1 (by rfl) ⟨1528502, by rfl⟩ : syracuseStep 2038003 = 3057005) B3057005
theorem B4585517 : Blo 2037435 4585517 := bbase (se 3 (by rfl) ⟨859784, by rfl⟩ : syracuseStep 4585517 = 1719569) (by norm_num)
theorem B3057011 : Blo 2037435 3057011 := bstep (se 1 (by rfl) ⟨2292758, by rfl⟩ : syracuseStep 3057011 = 4585517) B4585517
theorem B2038007 : Blo 2037435 2038007 := bstep (se 1 (by rfl) ⟨1528505, by rfl⟩ : syracuseStep 2038007 = 3057011) B3057011
theorem B14690261 : Blo 2037435 14690261 := bbase (se 7 (by rfl) ⟨172151, by rfl⟩ : syracuseStep 14690261 = 344303) (by norm_num)
theorem B9793507 : Blo 2037435 9793507 := bstep (se 1 (by rfl) ⟨7345130, by rfl⟩ : syracuseStep 9793507 = 14690261) B14690261
theorem B13058009 : Blo 2037435 13058009 := bstep (se 2 (by rfl) ⟨4896753, by rfl⟩ : syracuseStep 13058009 = 9793507) B9793507
theorem B8705339 : Blo 2037435 8705339 := bstep (se 1 (by rfl) ⟨6529004, by rfl⟩ : syracuseStep 8705339 = 13058009) B13058009
theorem B5803559 : Blo 2037435 5803559 := bstep (se 1 (by rfl) ⟨4352669, by rfl⟩ : syracuseStep 5803559 = 8705339) B8705339
theorem B3869039 : Blo 2037435 3869039 := bstep (se 1 (by rfl) ⟨2901779, by rfl⟩ : syracuseStep 3869039 = 5803559) B5803559
theorem B2579359 : Blo 2037435 2579359 := bstep (se 1 (by rfl) ⟨1934519, by rfl⟩ : syracuseStep 2579359 = 3869039) B3869039
theorem B3439145 : Blo 2037435 3439145 := bstep (se 2 (by rfl) ⟨1289679, by rfl⟩ : syracuseStep 3439145 = 2579359) B2579359
theorem B2292763 : Blo 2037435 2292763 := bstep (se 1 (by rfl) ⟨1719572, by rfl⟩ : syracuseStep 2292763 = 3439145) B3439145
theorem B3057017 : Blo 2037435 3057017 := bstep (se 2 (by rfl) ⟨1146381, by rfl⟩ : syracuseStep 3057017 = 2292763) B2292763
theorem B2038011 : Blo 2037435 2038011 := bstep (se 1 (by rfl) ⟨1528508, by rfl⟩ : syracuseStep 2038011 = 3057017) B3057017
theorem B6972149 : Blo 2037435 6972149 := bbase (se 5 (by rfl) ⟨326819, by rfl⟩ : syracuseStep 6972149 = 653639) (by norm_num)
theorem B4648099 : Blo 2037435 4648099 := bstep (se 1 (by rfl) ⟨3486074, by rfl⟩ : syracuseStep 4648099 = 6972149) B6972149
theorem B6197465 : Blo 2037435 6197465 := bstep (se 2 (by rfl) ⟨2324049, by rfl⟩ : syracuseStep 6197465 = 4648099) B4648099
theorem B4131643 : Blo 2037435 4131643 := bstep (se 1 (by rfl) ⟨3098732, by rfl⟩ : syracuseStep 4131643 = 6197465) B6197465
theorem B5508857 : Blo 2037435 5508857 := bstep (se 2 (by rfl) ⟨2065821, by rfl⟩ : syracuseStep 5508857 = 4131643) B4131643
theorem B14690285 : Blo 2037435 14690285 := bstep (se 3 (by rfl) ⟨2754428, by rfl⟩ : syracuseStep 14690285 = 5508857) B5508857
theorem B9793523 : Blo 2037435 9793523 := bstep (se 1 (by rfl) ⟨7345142, by rfl⟩ : syracuseStep 9793523 = 14690285) B14690285
theorem B6529015 : Blo 2037435 6529015 := bstep (se 1 (by rfl) ⟨4896761, by rfl⟩ : syracuseStep 6529015 = 9793523) B9793523
theorem B34821413 : Blo 2037435 34821413 := bstep (se 4 (by rfl) ⟨3264507, by rfl⟩ : syracuseStep 34821413 = 6529015) B6529015
theorem B23214275 : Blo 2037435 23214275 := bstep (se 1 (by rfl) ⟨17410706, by rfl⟩ : syracuseStep 23214275 = 34821413) B34821413
theorem B15476183 : Blo 2037435 15476183 := bstep (se 1 (by rfl) ⟨11607137, by rfl⟩ : syracuseStep 15476183 = 23214275) B23214275
theorem B10317455 : Blo 2037435 10317455 := bstep (se 1 (by rfl) ⟨7738091, by rfl⟩ : syracuseStep 10317455 = 15476183) B15476183
theorem B6878303 : Blo 2037435 6878303 := bstep (se 1 (by rfl) ⟨5158727, by rfl⟩ : syracuseStep 6878303 = 10317455) B10317455
theorem B4585535 : Blo 2037435 4585535 := bstep (se 1 (by rfl) ⟨3439151, by rfl⟩ : syracuseStep 4585535 = 6878303) B6878303
theorem B3057023 : Blo 2037435 3057023 := bstep (se 1 (by rfl) ⟨2292767, by rfl⟩ : syracuseStep 3057023 = 4585535) B4585535
theorem B2038015 : Blo 2037435 2038015 := bstep (se 1 (by rfl) ⟨1528511, by rfl⟩ : syracuseStep 2038015 = 3057023) B3057023
theorem B3057029 : Blo 2037435 3057029 := bbase (se 4 (by rfl) ⟨286596, by rfl⟩ : syracuseStep 3057029 = 573193) (by norm_num)
theorem B2038019 : Blo 2037435 2038019 := bstep (se 1 (by rfl) ⟨1528514, by rfl⟩ : syracuseStep 2038019 = 3057029) B3057029
theorem B3439165 : Blo 2037435 3439165 := bbase (se 3 (by rfl) ⟨644843, by rfl⟩ : syracuseStep 3439165 = 1289687) (by norm_num)
theorem B4585553 : Blo 2037435 4585553 := bstep (se 2 (by rfl) ⟨1719582, by rfl⟩ : syracuseStep 4585553 = 3439165) B3439165
theorem B3057035 : Blo 2037435 3057035 := bstep (se 1 (by rfl) ⟨2292776, by rfl⟩ : syracuseStep 3057035 = 4585553) B4585553
theorem B2038023 : Blo 2037435 2038023 := bstep (se 1 (by rfl) ⟨1528517, by rfl⟩ : syracuseStep 2038023 = 3057035) B3057035
theorem B2292781 : Blo 2037435 2292781 := bbase (se 3 (by rfl) ⟨429896, by rfl⟩ : syracuseStep 2292781 = 859793) (by norm_num)
theorem B3057041 : Blo 2037435 3057041 := bstep (se 2 (by rfl) ⟨1146390, by rfl⟩ : syracuseStep 3057041 = 2292781) B2292781
theorem B2038027 : Blo 2037435 2038027 := bstep (se 1 (by rfl) ⟨1528520, by rfl⟩ : syracuseStep 2038027 = 3057041) B3057041
theorem B6878357 : Blo 2037435 6878357 := bbase (se 6 (by rfl) ⟨161211, by rfl⟩ : syracuseStep 6878357 = 322423) (by norm_num)
theorem B4585571 : Blo 2037435 4585571 := bstep (se 1 (by rfl) ⟨3439178, by rfl⟩ : syracuseStep 4585571 = 6878357) B6878357
theorem B3057047 : Blo 2037435 3057047 := bstep (se 1 (by rfl) ⟨2292785, by rfl⟩ : syracuseStep 3057047 = 4585571) B4585571
theorem B2038031 : Blo 2037435 2038031 := bstep (se 1 (by rfl) ⟨1528523, by rfl⟩ : syracuseStep 2038031 = 3057047) B3057047
theorem B3057053 : Blo 2037435 3057053 := bbase (se 3 (by rfl) ⟨573197, by rfl⟩ : syracuseStep 3057053 = 1146395) (by norm_num)
theorem B2038035 : Blo 2037435 2038035 := bstep (se 1 (by rfl) ⟨1528526, by rfl⟩ : syracuseStep 2038035 = 3057053) B3057053
theorem B4585589 : Blo 2037435 4585589 := bbase (se 5 (by rfl) ⟨214949, by rfl⟩ : syracuseStep 4585589 = 429899) (by norm_num)
theorem B3057059 : Blo 2037435 3057059 := bstep (se 1 (by rfl) ⟨2292794, by rfl⟩ : syracuseStep 3057059 = 4585589) B4585589
theorem B2038039 : Blo 2037435 2038039 := bstep (se 1 (by rfl) ⟨1528529, by rfl⟩ : syracuseStep 2038039 = 3057059) B3057059
theorem B8376149 : Blo 2037435 8376149 := bbase (se 9 (by rfl) ⟨24539, by rfl⟩ : syracuseStep 8376149 = 49079) (by norm_num)
theorem B5584099 : Blo 2037435 5584099 := bstep (se 1 (by rfl) ⟨4188074, by rfl⟩ : syracuseStep 5584099 = 8376149) B8376149
theorem B7445465 : Blo 2037435 7445465 := bstep (se 2 (by rfl) ⟨2792049, by rfl⟩ : syracuseStep 7445465 = 5584099) B5584099
theorem B4963643 : Blo 2037435 4963643 := bstep (se 1 (by rfl) ⟨3722732, by rfl⟩ : syracuseStep 4963643 = 7445465) B7445465
theorem B3309095 : Blo 2037435 3309095 := bstep (se 1 (by rfl) ⟨2481821, by rfl⟩ : syracuseStep 3309095 = 4963643) B4963643
theorem B2206063 : Blo 2037435 2206063 := bstep (se 1 (by rfl) ⟨1654547, by rfl⟩ : syracuseStep 2206063 = 3309095) B3309095
theorem B2941417 : Blo 2037435 2941417 := bstep (se 2 (by rfl) ⟨1103031, by rfl⟩ : syracuseStep 2941417 = 2206063) B2206063
theorem B15687557 : Blo 2037435 15687557 := bstep (se 4 (by rfl) ⟨1470708, by rfl⟩ : syracuseStep 15687557 = 2941417) B2941417
theorem B10458371 : Blo 2037435 10458371 := bstep (se 1 (by rfl) ⟨7843778, by rfl⟩ : syracuseStep 10458371 = 15687557) B15687557
theorem B6972247 : Blo 2037435 6972247 := bstep (se 1 (by rfl) ⟨5229185, by rfl⟩ : syracuseStep 6972247 = 10458371) B10458371
theorem B9296329 : Blo 2037435 9296329 := bstep (se 2 (by rfl) ⟨3486123, by rfl⟩ : syracuseStep 9296329 = 6972247) B6972247
theorem B12395105 : Blo 2037435 12395105 := bstep (se 2 (by rfl) ⟨4648164, by rfl⟩ : syracuseStep 12395105 = 9296329) B9296329
theorem B8263403 : Blo 2037435 8263403 := bstep (se 1 (by rfl) ⟨6197552, by rfl⟩ : syracuseStep 8263403 = 12395105) B12395105
theorem B5508935 : Blo 2037435 5508935 := bstep (se 1 (by rfl) ⟨4131701, by rfl⟩ : syracuseStep 5508935 = 8263403) B8263403
theorem B3672623 : Blo 2037435 3672623 := bstep (se 1 (by rfl) ⟨2754467, by rfl⟩ : syracuseStep 3672623 = 5508935) B5508935
theorem B2448415 : Blo 2037435 2448415 := bstep (se 1 (by rfl) ⟨1836311, by rfl⟩ : syracuseStep 2448415 = 3672623) B3672623
theorem B3264553 : Blo 2037435 3264553 := bstep (se 2 (by rfl) ⟨1224207, by rfl⟩ : syracuseStep 3264553 = 2448415) B2448415
theorem B17410949 : Blo 2037435 17410949 := bstep (se 4 (by rfl) ⟨1632276, by rfl⟩ : syracuseStep 17410949 = 3264553) B3264553
theorem B11607299 : Blo 2037435 11607299 := bstep (se 1 (by rfl) ⟨8705474, by rfl⟩ : syracuseStep 11607299 = 17410949) B17410949
theorem B7738199 : Blo 2037435 7738199 := bstep (se 1 (by rfl) ⟨5803649, by rfl⟩ : syracuseStep 7738199 = 11607299) B11607299
theorem B5158799 : Blo 2037435 5158799 := bstep (se 1 (by rfl) ⟨3869099, by rfl⟩ : syracuseStep 5158799 = 7738199) B7738199
theorem B3439199 : Blo 2037435 3439199 := bstep (se 1 (by rfl) ⟨2579399, by rfl⟩ : syracuseStep 3439199 = 5158799) B5158799
theorem B2292799 : Blo 2037435 2292799 := bstep (se 1 (by rfl) ⟨1719599, by rfl⟩ : syracuseStep 2292799 = 3439199) B3439199
theorem B3057065 : Blo 2037435 3057065 := bstep (se 2 (by rfl) ⟨1146399, by rfl⟩ : syracuseStep 3057065 = 2292799) B2292799
theorem B2038043 : Blo 2037435 2038043 := bstep (se 1 (by rfl) ⟨1528532, by rfl⟩ : syracuseStep 2038043 = 3057065) B3057065
theorem B7738213 : Blo 2037435 7738213 := bbase (se 4 (by rfl) ⟨725457, by rfl⟩ : syracuseStep 7738213 = 1450915) (by norm_num)
theorem B10317617 : Blo 2037435 10317617 := bstep (se 2 (by rfl) ⟨3869106, by rfl⟩ : syracuseStep 10317617 = 7738213) B7738213
theorem B6878411 : Blo 2037435 6878411 := bstep (se 1 (by rfl) ⟨5158808, by rfl⟩ : syracuseStep 6878411 = 10317617) B10317617
theorem B4585607 : Blo 2037435 4585607 := bstep (se 1 (by rfl) ⟨3439205, by rfl⟩ : syracuseStep 4585607 = 6878411) B6878411
theorem B3057071 : Blo 2037435 3057071 := bstep (se 1 (by rfl) ⟨2292803, by rfl⟩ : syracuseStep 3057071 = 4585607) B4585607
theorem B2038047 : Blo 2037435 2038047 := bstep (se 1 (by rfl) ⟨1528535, by rfl⟩ : syracuseStep 2038047 = 3057071) B3057071
theorem B3057077 : Blo 2037435 3057077 := bbase (se 5 (by rfl) ⟨143300, by rfl⟩ : syracuseStep 3057077 = 286601) (by norm_num)
theorem B2038051 : Blo 2037435 2038051 := bstep (se 1 (by rfl) ⟨1528538, by rfl⟩ : syracuseStep 2038051 = 3057077) B3057077
theorem B5158829 : Blo 2037435 5158829 := bbase (se 3 (by rfl) ⟨967280, by rfl⟩ : syracuseStep 5158829 = 1934561) (by norm_num)
theorem B3439219 : Blo 2037435 3439219 := bstep (se 1 (by rfl) ⟨2579414, by rfl⟩ : syracuseStep 3439219 = 5158829) B5158829
theorem B4585625 : Blo 2037435 4585625 := bstep (se 2 (by rfl) ⟨1719609, by rfl⟩ : syracuseStep 4585625 = 3439219) B3439219
theorem B3057083 : Blo 2037435 3057083 := bstep (se 1 (by rfl) ⟨2292812, by rfl⟩ : syracuseStep 3057083 = 4585625) B4585625
theorem B2038055 : Blo 2037435 2038055 := bstep (se 1 (by rfl) ⟨1528541, by rfl⟩ : syracuseStep 2038055 = 3057083) B3057083
theorem B2292817 : Blo 2037435 2292817 := bbase (se 2 (by rfl) ⟨859806, by rfl⟩ : syracuseStep 2292817 = 1719613) (by norm_num)
theorem B3057089 : Blo 2037435 3057089 := bstep (se 2 (by rfl) ⟨1146408, by rfl⟩ : syracuseStep 3057089 = 2292817) B2292817
theorem B2038059 : Blo 2037435 2038059 := bstep (se 1 (by rfl) ⟨1528544, by rfl⟩ : syracuseStep 2038059 = 3057089) B3057089
theorem B2901853 : Blo 2037435 2901853 := bbase (se 3 (by rfl) ⟨544097, by rfl⟩ : syracuseStep 2901853 = 1088195) (by norm_num)
theorem B3869137 : Blo 2037435 3869137 := bstep (se 2 (by rfl) ⟨1450926, by rfl⟩ : syracuseStep 3869137 = 2901853) B2901853
theorem B5158849 : Blo 2037435 5158849 := bstep (se 2 (by rfl) ⟨1934568, by rfl⟩ : syracuseStep 5158849 = 3869137) B3869137
theorem B6878465 : Blo 2037435 6878465 := bstep (se 2 (by rfl) ⟨2579424, by rfl⟩ : syracuseStep 6878465 = 5158849) B5158849
theorem B4585643 : Blo 2037435 4585643 := bstep (se 1 (by rfl) ⟨3439232, by rfl⟩ : syracuseStep 4585643 = 6878465) B6878465
theorem B3057095 : Blo 2037435 3057095 := bstep (se 1 (by rfl) ⟨2292821, by rfl⟩ : syracuseStep 3057095 = 4585643) B4585643
theorem B2038063 : Blo 2037435 2038063 := bstep (se 1 (by rfl) ⟨1528547, by rfl⟩ : syracuseStep 2038063 = 3057095) B3057095
theorem B3057101 : Blo 2037435 3057101 := bbase (se 3 (by rfl) ⟨573206, by rfl⟩ : syracuseStep 3057101 = 1146413) (by norm_num)
theorem B2038067 : Blo 2037435 2038067 := bstep (se 1 (by rfl) ⟨1528550, by rfl⟩ : syracuseStep 2038067 = 3057101) B3057101
theorem B4585661 : Blo 2037435 4585661 := bbase (se 3 (by rfl) ⟨859811, by rfl⟩ : syracuseStep 4585661 = 1719623) (by norm_num)
theorem B3057107 : Blo 2037435 3057107 := bstep (se 1 (by rfl) ⟨2292830, by rfl⟩ : syracuseStep 3057107 = 4585661) B4585661
theorem B2038071 : Blo 2037435 2038071 := bstep (se 1 (by rfl) ⟨1528553, by rfl⟩ : syracuseStep 2038071 = 3057107) B3057107
theorem B3439253 : Blo 2037435 3439253 := bbase (se 6 (by rfl) ⟨80607, by rfl⟩ : syracuseStep 3439253 = 161215) (by norm_num)
theorem B2292835 : Blo 2037435 2292835 := bstep (se 1 (by rfl) ⟨1719626, by rfl⟩ : syracuseStep 2292835 = 3439253) B3439253
theorem B3057113 : Blo 2037435 3057113 := bstep (se 2 (by rfl) ⟨1146417, by rfl⟩ : syracuseStep 3057113 = 2292835) B2292835
theorem B2038075 : Blo 2037435 2038075 := bstep (se 1 (by rfl) ⟨1528556, by rfl⟩ : syracuseStep 2038075 = 3057113) B3057113
theorem B3141109 : Blo 2037435 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B16752581 : Blo 2037435 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B11168387 : Blo 2037435 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B7445591 : Blo 2037435 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B4963727 : Blo 2037435 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B13236605 : Blo 2037435 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B8824403 : Blo 2037435 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B23531741 : Blo 2037435 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B15687827 : Blo 2037435 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B10458551 : Blo 2037435 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B6972367 : Blo 2037435 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B9296489 : Blo 2037435 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B24790637 : Blo 2037435 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B16527091 : Blo 2037435 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B22036121 : Blo 2037435 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B14690747 : Blo 2037435 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B9793831 : Blo 2037435 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B13058441 : Blo 2037435 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B8705627 : Blo 2037435 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B5803751 : Blo 2037435 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B15476669 : Blo 2037435 15476669 := bstep (se 3 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 15476669 = 5803751) B5803751
theorem B10317779 : Blo 2037435 10317779 := bstep (se 1 (by rfl) ⟨7738334, by rfl⟩ : syracuseStep 10317779 = 15476669) B15476669
theorem B6878519 : Blo 2037435 6878519 := bstep (se 1 (by rfl) ⟨5158889, by rfl⟩ : syracuseStep 6878519 = 10317779) B10317779
theorem B4585679 : Blo 2037435 4585679 := bstep (se 1 (by rfl) ⟨3439259, by rfl⟩ : syracuseStep 4585679 = 6878519) B6878519
theorem B3057119 : Blo 2037435 3057119 := bstep (se 1 (by rfl) ⟨2292839, by rfl⟩ : syracuseStep 3057119 = 4585679) B4585679
theorem B2038079 : Blo 2037435 2038079 := bstep (se 1 (by rfl) ⟨1528559, by rfl⟩ : syracuseStep 2038079 = 3057119) B3057119
theorem B3057125 : Blo 2037435 3057125 := bbase (se 4 (by rfl) ⟨286605, by rfl⟩ : syracuseStep 3057125 = 573211) (by norm_num)
theorem B2038083 : Blo 2037435 2038083 := bstep (se 1 (by rfl) ⟨1528562, by rfl⟩ : syracuseStep 2038083 = 3057125) B3057125
theorem B7445621 : Blo 2037435 7445621 := bbase (se 5 (by rfl) ⟨349013, by rfl⟩ : syracuseStep 7445621 = 698027) (by norm_num)
theorem B4963747 : Blo 2037435 4963747 := bstep (se 1 (by rfl) ⟨3722810, by rfl⟩ : syracuseStep 4963747 = 7445621) B7445621
theorem B6618329 : Blo 2037435 6618329 := bstep (se 2 (by rfl) ⟨2481873, by rfl⟩ : syracuseStep 6618329 = 4963747) B4963747
theorem B4412219 : Blo 2037435 4412219 := bstep (se 1 (by rfl) ⟨3309164, by rfl⟩ : syracuseStep 4412219 = 6618329) B6618329
theorem B11765917 : Blo 2037435 11765917 := bstep (se 3 (by rfl) ⟨2206109, by rfl⟩ : syracuseStep 11765917 = 4412219) B4412219
theorem B62751557 : Blo 2037435 62751557 := bstep (se 4 (by rfl) ⟨5882958, by rfl⟩ : syracuseStep 62751557 = 11765917) B11765917
theorem B167337485 : Blo 2037435 167337485 := bstep (se 3 (by rfl) ⟨31375778, by rfl⟩ : syracuseStep 167337485 = 62751557) B62751557
theorem B111558323 : Blo 2037435 111558323 := bstep (se 1 (by rfl) ⟨83668742, by rfl⟩ : syracuseStep 111558323 = 167337485) B167337485
theorem B74372215 : Blo 2037435 74372215 := bstep (se 1 (by rfl) ⟨55779161, by rfl⟩ : syracuseStep 74372215 = 111558323) B111558323
theorem B99162953 : Blo 2037435 99162953 := bstep (se 2 (by rfl) ⟨37186107, by rfl⟩ : syracuseStep 99162953 = 74372215) B74372215
theorem B66108635 : Blo 2037435 66108635 := bstep (se 1 (by rfl) ⟨49581476, by rfl⟩ : syracuseStep 66108635 = 99162953) B99162953
theorem B44072423 : Blo 2037435 44072423 := bstep (se 1 (by rfl) ⟨33054317, by rfl⟩ : syracuseStep 44072423 = 66108635) B66108635
theorem B29381615 : Blo 2037435 29381615 := bstep (se 1 (by rfl) ⟨22036211, by rfl⟩ : syracuseStep 29381615 = 44072423) B44072423
theorem B19587743 : Blo 2037435 19587743 := bstep (se 1 (by rfl) ⟨14690807, by rfl⟩ : syracuseStep 19587743 = 29381615) B29381615
theorem B13058495 : Blo 2037435 13058495 := bstep (se 1 (by rfl) ⟨9793871, by rfl⟩ : syracuseStep 13058495 = 19587743) B19587743
theorem B8705663 : Blo 2037435 8705663 := bstep (se 1 (by rfl) ⟨6529247, by rfl⟩ : syracuseStep 8705663 = 13058495) B13058495
theorem B5803775 : Blo 2037435 5803775 := bstep (se 1 (by rfl) ⟨4352831, by rfl⟩ : syracuseStep 5803775 = 8705663) B8705663
theorem B3869183 : Blo 2037435 3869183 := bstep (se 1 (by rfl) ⟨2901887, by rfl⟩ : syracuseStep 3869183 = 5803775) B5803775
theorem B2579455 : Blo 2037435 2579455 := bstep (se 1 (by rfl) ⟨1934591, by rfl⟩ : syracuseStep 2579455 = 3869183) B3869183
theorem B3439273 : Blo 2037435 3439273 := bstep (se 2 (by rfl) ⟨1289727, by rfl⟩ : syracuseStep 3439273 = 2579455) B2579455
theorem B4585697 : Blo 2037435 4585697 := bstep (se 2 (by rfl) ⟨1719636, by rfl⟩ : syracuseStep 4585697 = 3439273) B3439273
theorem B3057131 : Blo 2037435 3057131 := bstep (se 1 (by rfl) ⟨2292848, by rfl⟩ : syracuseStep 3057131 = 4585697) B4585697
theorem B2038087 : Blo 2037435 2038087 := bstep (se 1 (by rfl) ⟨1528565, by rfl⟩ : syracuseStep 2038087 = 3057131) B3057131
theorem B2292853 : Blo 2037435 2292853 := bbase (se 5 (by rfl) ⟨107477, by rfl⟩ : syracuseStep 2292853 = 214955) (by norm_num)
theorem B3057137 : Blo 2037435 3057137 := bstep (se 2 (by rfl) ⟨1146426, by rfl⟩ : syracuseStep 3057137 = 2292853) B2292853
theorem B2038091 : Blo 2037435 2038091 := bstep (se 1 (by rfl) ⟨1528568, by rfl⟩ : syracuseStep 2038091 = 3057137) B3057137
theorem B2579465 : Blo 2037435 2579465 := bbase (se 2 (by rfl) ⟨967299, by rfl⟩ : syracuseStep 2579465 = 1934599) (by norm_num)
theorem B6878573 : Blo 2037435 6878573 := bstep (se 3 (by rfl) ⟨1289732, by rfl⟩ : syracuseStep 6878573 = 2579465) B2579465
theorem B4585715 : Blo 2037435 4585715 := bstep (se 1 (by rfl) ⟨3439286, by rfl⟩ : syracuseStep 4585715 = 6878573) B6878573
theorem B3057143 : Blo 2037435 3057143 := bstep (se 1 (by rfl) ⟨2292857, by rfl⟩ : syracuseStep 3057143 = 4585715) B4585715
theorem B2038095 : Blo 2037435 2038095 := bstep (se 1 (by rfl) ⟨1528571, by rfl⟩ : syracuseStep 2038095 = 3057143) B3057143
theorem B3057149 : Blo 2037435 3057149 := bbase (se 3 (by rfl) ⟨573215, by rfl⟩ : syracuseStep 3057149 = 1146431) (by norm_num)
theorem B2038099 : Blo 2037435 2038099 := bstep (se 1 (by rfl) ⟨1528574, by rfl⟩ : syracuseStep 2038099 = 3057149) B3057149
theorem B4585733 : Blo 2037435 4585733 := bbase (se 4 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 4585733 = 859825) (by norm_num)
theorem B3057155 : Blo 2037435 3057155 := bstep (se 1 (by rfl) ⟨2292866, by rfl⟩ : syracuseStep 3057155 = 4585733) B4585733
theorem B2038103 : Blo 2037435 2038103 := bstep (se 1 (by rfl) ⟨1528577, by rfl⟩ : syracuseStep 2038103 = 3057155) B3057155
theorem B3869221 : Blo 2037435 3869221 := bbase (se 4 (by rfl) ⟨362739, by rfl⟩ : syracuseStep 3869221 = 725479) (by norm_num)
theorem B5158961 : Blo 2037435 5158961 := bstep (se 2 (by rfl) ⟨1934610, by rfl⟩ : syracuseStep 5158961 = 3869221) B3869221
theorem B3439307 : Blo 2037435 3439307 := bstep (se 1 (by rfl) ⟨2579480, by rfl⟩ : syracuseStep 3439307 = 5158961) B5158961
theorem B2292871 : Blo 2037435 2292871 := bstep (se 1 (by rfl) ⟨1719653, by rfl⟩ : syracuseStep 2292871 = 3439307) B3439307
theorem B3057161 : Blo 2037435 3057161 := bstep (se 2 (by rfl) ⟨1146435, by rfl⟩ : syracuseStep 3057161 = 2292871) B2292871
theorem B2038107 : Blo 2037435 2038107 := bstep (se 1 (by rfl) ⟨1528580, by rfl⟩ : syracuseStep 2038107 = 3057161) B3057161
theorem B10317941 : Blo 2037435 10317941 := bbase (se 5 (by rfl) ⟨483653, by rfl⟩ : syracuseStep 10317941 = 967307) (by norm_num)
theorem B6878627 : Blo 2037435 6878627 := bstep (se 1 (by rfl) ⟨5158970, by rfl⟩ : syracuseStep 6878627 = 10317941) B10317941
theorem B4585751 : Blo 2037435 4585751 := bstep (se 1 (by rfl) ⟨3439313, by rfl⟩ : syracuseStep 4585751 = 6878627) B6878627
theorem B3057167 : Blo 2037435 3057167 := bstep (se 1 (by rfl) ⟨2292875, by rfl⟩ : syracuseStep 3057167 = 4585751) B4585751
theorem B2038111 : Blo 2037435 2038111 := bstep (se 1 (by rfl) ⟨1528583, by rfl⟩ : syracuseStep 2038111 = 3057167) B3057167
theorem B3057173 : Blo 2037435 3057173 := bbase (se 6 (by rfl) ⟨71652, by rfl⟩ : syracuseStep 3057173 = 143305) (by norm_num)
theorem B2038115 : Blo 2037435 2038115 := bstep (se 1 (by rfl) ⟨1528586, by rfl⟩ : syracuseStep 2038115 = 3057173) B3057173
theorem B6529349 : Blo 2037435 6529349 := bbase (se 4 (by rfl) ⟨612126, by rfl⟩ : syracuseStep 6529349 = 1224253) (by norm_num)
theorem B17411597 : Blo 2037435 17411597 := bstep (se 3 (by rfl) ⟨3264674, by rfl⟩ : syracuseStep 17411597 = 6529349) B6529349
theorem B11607731 : Blo 2037435 11607731 := bstep (se 1 (by rfl) ⟨8705798, by rfl⟩ : syracuseStep 11607731 = 17411597) B17411597
theorem B7738487 : Blo 2037435 7738487 := bstep (se 1 (by rfl) ⟨5803865, by rfl⟩ : syracuseStep 7738487 = 11607731) B11607731
theorem B5158991 : Blo 2037435 5158991 := bstep (se 1 (by rfl) ⟨3869243, by rfl⟩ : syracuseStep 5158991 = 7738487) B7738487
theorem B3439327 : Blo 2037435 3439327 := bstep (se 1 (by rfl) ⟨2579495, by rfl⟩ : syracuseStep 3439327 = 5158991) B5158991
theorem B4585769 : Blo 2037435 4585769 := bstep (se 2 (by rfl) ⟨1719663, by rfl⟩ : syracuseStep 4585769 = 3439327) B3439327
theorem B3057179 : Blo 2037435 3057179 := bstep (se 1 (by rfl) ⟨2292884, by rfl⟩ : syracuseStep 3057179 = 4585769) B4585769
theorem B2038119 : Blo 2037435 2038119 := bstep (se 1 (by rfl) ⟨1528589, by rfl⟩ : syracuseStep 2038119 = 3057179) B3057179
theorem B2292889 : Blo 2037435 2292889 := bbase (se 2 (by rfl) ⟨859833, by rfl⟩ : syracuseStep 2292889 = 1719667) (by norm_num)
theorem B3057185 : Blo 2037435 3057185 := bstep (se 2 (by rfl) ⟨1146444, by rfl⟩ : syracuseStep 3057185 = 2292889) B2292889
theorem B2038123 : Blo 2037435 2038123 := bstep (se 1 (by rfl) ⟨1528592, by rfl⟩ : syracuseStep 2038123 = 3057185) B3057185
theorem B7738517 : Blo 2037435 7738517 := bbase (se 6 (by rfl) ⟨181371, by rfl⟩ : syracuseStep 7738517 = 362743) (by norm_num)
theorem B5159011 : Blo 2037435 5159011 := bstep (se 1 (by rfl) ⟨3869258, by rfl⟩ : syracuseStep 5159011 = 7738517) B7738517
theorem B6878681 : Blo 2037435 6878681 := bstep (se 2 (by rfl) ⟨2579505, by rfl⟩ : syracuseStep 6878681 = 5159011) B5159011
theorem B4585787 : Blo 2037435 4585787 := bstep (se 1 (by rfl) ⟨3439340, by rfl⟩ : syracuseStep 4585787 = 6878681) B6878681
theorem B3057191 : Blo 2037435 3057191 := bstep (se 1 (by rfl) ⟨2292893, by rfl⟩ : syracuseStep 3057191 = 4585787) B4585787
theorem B2038127 : Blo 2037435 2038127 := bstep (se 1 (by rfl) ⟨1528595, by rfl⟩ : syracuseStep 2038127 = 3057191) B3057191
theorem B3057197 : Blo 2037435 3057197 := bbase (se 3 (by rfl) ⟨573224, by rfl⟩ : syracuseStep 3057197 = 1146449) (by norm_num)
theorem B2038131 : Blo 2037435 2038131 := bstep (se 1 (by rfl) ⟨1528598, by rfl⟩ : syracuseStep 2038131 = 3057197) B3057197
theorem B4585805 : Blo 2037435 4585805 := bbase (se 3 (by rfl) ⟨859838, by rfl⟩ : syracuseStep 4585805 = 1719677) (by norm_num)
theorem B3057203 : Blo 2037435 3057203 := bstep (se 1 (by rfl) ⟨2292902, by rfl⟩ : syracuseStep 3057203 = 4585805) B4585805
theorem B2038135 : Blo 2037435 2038135 := bstep (se 1 (by rfl) ⟨1528601, by rfl⟩ : syracuseStep 2038135 = 3057203) B3057203
theorem B2579521 : Blo 2037435 2579521 := bbase (se 2 (by rfl) ⟨967320, by rfl⟩ : syracuseStep 2579521 = 1934641) (by norm_num)
theorem B3439361 : Blo 2037435 3439361 := bstep (se 2 (by rfl) ⟨1289760, by rfl⟩ : syracuseStep 3439361 = 2579521) B2579521
theorem B2292907 : Blo 2037435 2292907 := bstep (se 1 (by rfl) ⟨1719680, by rfl⟩ : syracuseStep 2292907 = 3439361) B3439361
theorem B3057209 : Blo 2037435 3057209 := bstep (se 2 (by rfl) ⟨1146453, by rfl⟩ : syracuseStep 3057209 = 2292907) B2292907
theorem B2038139 : Blo 2037435 2038139 := bstep (se 1 (by rfl) ⟨1528604, by rfl⟩ : syracuseStep 2038139 = 3057209) B3057209
theorem B5509205 : Blo 2037435 5509205 := bbase (se 8 (by rfl) ⟨32280, by rfl⟩ : syracuseStep 5509205 = 64561) (by norm_num)
theorem B3672803 : Blo 2037435 3672803 := bstep (se 1 (by rfl) ⟨2754602, by rfl⟩ : syracuseStep 3672803 = 5509205) B5509205
theorem B2448535 : Blo 2037435 2448535 := bstep (se 1 (by rfl) ⟨1836401, by rfl⟩ : syracuseStep 2448535 = 3672803) B3672803
theorem B3264713 : Blo 2037435 3264713 := bstep (se 2 (by rfl) ⟨1224267, by rfl⟩ : syracuseStep 3264713 = 2448535) B2448535
theorem B2176475 : Blo 2037435 2176475 := bstep (se 1 (by rfl) ⟨1632356, by rfl⟩ : syracuseStep 2176475 = 3264713) B3264713
theorem B23215733 : Blo 2037435 23215733 := bstep (se 5 (by rfl) ⟨1088237, by rfl⟩ : syracuseStep 23215733 = 2176475) B2176475
theorem B15477155 : Blo 2037435 15477155 := bstep (se 1 (by rfl) ⟨11607866, by rfl⟩ : syracuseStep 15477155 = 23215733) B23215733
theorem B10318103 : Blo 2037435 10318103 := bstep (se 1 (by rfl) ⟨7738577, by rfl⟩ : syracuseStep 10318103 = 15477155) B15477155
theorem B6878735 : Blo 2037435 6878735 := bstep (se 1 (by rfl) ⟨5159051, by rfl⟩ : syracuseStep 6878735 = 10318103) B10318103
theorem B4585823 : Blo 2037435 4585823 := bstep (se 1 (by rfl) ⟨3439367, by rfl⟩ : syracuseStep 4585823 = 6878735) B6878735
theorem B3057215 : Blo 2037435 3057215 := bstep (se 1 (by rfl) ⟨2292911, by rfl⟩ : syracuseStep 3057215 = 4585823) B4585823
theorem B2038143 : Blo 2037435 2038143 := bstep (se 1 (by rfl) ⟨1528607, by rfl⟩ : syracuseStep 2038143 = 3057215) B3057215
theorem B3057221 : Blo 2037435 3057221 := bbase (se 4 (by rfl) ⟨286614, by rfl⟩ : syracuseStep 3057221 = 573229) (by norm_num)
theorem B2038147 : Blo 2037435 2038147 := bstep (se 1 (by rfl) ⟨1528610, by rfl⟩ : syracuseStep 2038147 = 3057221) B3057221
theorem B3439381 : Blo 2037435 3439381 := bbase (se 6 (by rfl) ⟨80610, by rfl⟩ : syracuseStep 3439381 = 161221) (by norm_num)
theorem B4585841 : Blo 2037435 4585841 := bstep (se 2 (by rfl) ⟨1719690, by rfl⟩ : syracuseStep 4585841 = 3439381) B3439381
theorem B3057227 : Blo 2037435 3057227 := bstep (se 1 (by rfl) ⟨2292920, by rfl⟩ : syracuseStep 3057227 = 4585841) B4585841
theorem B2038151 : Blo 2037435 2038151 := bstep (se 1 (by rfl) ⟨1528613, by rfl⟩ : syracuseStep 2038151 = 3057227) B3057227
theorem B2292925 : Blo 2037435 2292925 := bbase (se 3 (by rfl) ⟨429923, by rfl⟩ : syracuseStep 2292925 = 859847) (by norm_num)
theorem B3057233 : Blo 2037435 3057233 := bstep (se 2 (by rfl) ⟨1146462, by rfl⟩ : syracuseStep 3057233 = 2292925) B2292925
theorem B2038155 : Blo 2037435 2038155 := bstep (se 1 (by rfl) ⟨1528616, by rfl⟩ : syracuseStep 2038155 = 3057233) B3057233
theorem B6878789 : Blo 2037435 6878789 := bbase (se 4 (by rfl) ⟨644886, by rfl⟩ : syracuseStep 6878789 = 1289773) (by norm_num)
theorem B4585859 : Blo 2037435 4585859 := bstep (se 1 (by rfl) ⟨3439394, by rfl⟩ : syracuseStep 4585859 = 6878789) B6878789
theorem B3057239 : Blo 2037435 3057239 := bstep (se 1 (by rfl) ⟨2292929, by rfl⟩ : syracuseStep 3057239 = 4585859) B4585859
theorem B2038159 : Blo 2037435 2038159 := bstep (se 1 (by rfl) ⟨1528619, by rfl⟩ : syracuseStep 2038159 = 3057239) B3057239
theorem B3057245 : Blo 2037435 3057245 := bbase (se 3 (by rfl) ⟨573233, by rfl⟩ : syracuseStep 3057245 = 1146467) (by norm_num)
theorem B2038163 : Blo 2037435 2038163 := bstep (se 1 (by rfl) ⟨1528622, by rfl⟩ : syracuseStep 2038163 = 3057245) B3057245
theorem B4585877 : Blo 2037435 4585877 := bbase (se 6 (by rfl) ⟨107481, by rfl⟩ : syracuseStep 4585877 = 214963) (by norm_num)
theorem B3057251 : Blo 2037435 3057251 := bstep (se 1 (by rfl) ⟨2292938, by rfl⟩ : syracuseStep 3057251 = 4585877) B4585877
theorem B2038167 : Blo 2037435 2038167 := bstep (se 1 (by rfl) ⟨1528625, by rfl⟩ : syracuseStep 2038167 = 3057251) B3057251
theorem B2448569 : Blo 2037435 2448569 := bbase (se 2 (by rfl) ⟨918213, by rfl⟩ : syracuseStep 2448569 = 1836427) (by norm_num)
theorem B6529517 : Blo 2037435 6529517 := bstep (se 3 (by rfl) ⟨1224284, by rfl⟩ : syracuseStep 6529517 = 2448569) B2448569
theorem B4353011 : Blo 2037435 4353011 := bstep (se 1 (by rfl) ⟨3264758, by rfl⟩ : syracuseStep 4353011 = 6529517) B6529517
theorem B2902007 : Blo 2037435 2902007 := bstep (se 1 (by rfl) ⟨2176505, by rfl⟩ : syracuseStep 2902007 = 4353011) B4353011
theorem B7738685 : Blo 2037435 7738685 := bstep (se 3 (by rfl) ⟨1451003, by rfl⟩ : syracuseStep 7738685 = 2902007) B2902007
theorem B5159123 : Blo 2037435 5159123 := bstep (se 1 (by rfl) ⟨3869342, by rfl⟩ : syracuseStep 5159123 = 7738685) B7738685
theorem B3439415 : Blo 2037435 3439415 := bstep (se 1 (by rfl) ⟨2579561, by rfl⟩ : syracuseStep 3439415 = 5159123) B5159123
theorem B2292943 : Blo 2037435 2292943 := bstep (se 1 (by rfl) ⟨1719707, by rfl⟩ : syracuseStep 2292943 = 3439415) B3439415
theorem B3057257 : Blo 2037435 3057257 := bstep (se 2 (by rfl) ⟨1146471, by rfl⟩ : syracuseStep 3057257 = 2292943) B2292943
theorem B2038171 : Blo 2037435 2038171 := bstep (se 1 (by rfl) ⟨1528628, by rfl⟩ : syracuseStep 2038171 = 3057257) B3057257
theorem B8706037 : Blo 2037435 8706037 := bbase (se 5 (by rfl) ⟨408095, by rfl⟩ : syracuseStep 8706037 = 816191) (by norm_num)
theorem B11608049 : Blo 2037435 11608049 := bstep (se 2 (by rfl) ⟨4353018, by rfl⟩ : syracuseStep 11608049 = 8706037) B8706037
theorem B7738699 : Blo 2037435 7738699 := bstep (se 1 (by rfl) ⟨5804024, by rfl⟩ : syracuseStep 7738699 = 11608049) B11608049
theorem B10318265 : Blo 2037435 10318265 := bstep (se 2 (by rfl) ⟨3869349, by rfl⟩ : syracuseStep 10318265 = 7738699) B7738699
theorem B6878843 : Blo 2037435 6878843 := bstep (se 1 (by rfl) ⟨5159132, by rfl⟩ : syracuseStep 6878843 = 10318265) B10318265
theorem B4585895 : Blo 2037435 4585895 := bstep (se 1 (by rfl) ⟨3439421, by rfl⟩ : syracuseStep 4585895 = 6878843) B6878843
theorem B3057263 : Blo 2037435 3057263 := bstep (se 1 (by rfl) ⟨2292947, by rfl⟩ : syracuseStep 3057263 = 4585895) B4585895
theorem B2038175 : Blo 2037435 2038175 := bstep (se 1 (by rfl) ⟨1528631, by rfl⟩ : syracuseStep 2038175 = 3057263) B3057263
theorem B3057269 : Blo 2037435 3057269 := bbase (se 5 (by rfl) ⟨143309, by rfl⟩ : syracuseStep 3057269 = 286619) (by norm_num)
theorem B2038179 : Blo 2037435 2038179 := bstep (se 1 (by rfl) ⟨1528634, by rfl⟩ : syracuseStep 2038179 = 3057269) B3057269
theorem B3869365 : Blo 2037435 3869365 := bbase (se 5 (by rfl) ⟨181376, by rfl⟩ : syracuseStep 3869365 = 362753) (by norm_num)
theorem B5159153 : Blo 2037435 5159153 := bstep (se 2 (by rfl) ⟨1934682, by rfl⟩ : syracuseStep 5159153 = 3869365) B3869365
theorem B3439435 : Blo 2037435 3439435 := bstep (se 1 (by rfl) ⟨2579576, by rfl⟩ : syracuseStep 3439435 = 5159153) B5159153
theorem B4585913 : Blo 2037435 4585913 := bstep (se 2 (by rfl) ⟨1719717, by rfl⟩ : syracuseStep 4585913 = 3439435) B3439435
theorem B3057275 : Blo 2037435 3057275 := bstep (se 1 (by rfl) ⟨2292956, by rfl⟩ : syracuseStep 3057275 = 4585913) B4585913
theorem B2038183 : Blo 2037435 2038183 := bstep (se 1 (by rfl) ⟨1528637, by rfl⟩ : syracuseStep 2038183 = 3057275) B3057275
theorem B2292961 : Blo 2037435 2292961 := bbase (se 2 (by rfl) ⟨859860, by rfl⟩ : syracuseStep 2292961 = 1719721) (by norm_num)
theorem B3057281 : Blo 2037435 3057281 := bstep (se 2 (by rfl) ⟨1146480, by rfl⟩ : syracuseStep 3057281 = 2292961) B2292961
theorem B2038187 : Blo 2037435 2038187 := bstep (se 1 (by rfl) ⟨1528640, by rfl⟩ : syracuseStep 2038187 = 3057281) B3057281
theorem B5159173 : Blo 2037435 5159173 := bbase (se 4 (by rfl) ⟨483672, by rfl⟩ : syracuseStep 5159173 = 967345) (by norm_num)
theorem B6878897 : Blo 2037435 6878897 := bstep (se 2 (by rfl) ⟨2579586, by rfl⟩ : syracuseStep 6878897 = 5159173) B5159173
theorem B4585931 : Blo 2037435 4585931 := bstep (se 1 (by rfl) ⟨3439448, by rfl⟩ : syracuseStep 4585931 = 6878897) B6878897
theorem B3057287 : Blo 2037435 3057287 := bstep (se 1 (by rfl) ⟨2292965, by rfl⟩ : syracuseStep 3057287 = 4585931) B4585931
theorem B2038191 : Blo 2037435 2038191 := bstep (se 1 (by rfl) ⟨1528643, by rfl⟩ : syracuseStep 2038191 = 3057287) B3057287
theorem B3057293 : Blo 2037435 3057293 := bbase (se 3 (by rfl) ⟨573242, by rfl⟩ : syracuseStep 3057293 = 1146485) (by norm_num)
theorem B2038195 : Blo 2037435 2038195 := bstep (se 1 (by rfl) ⟨1528646, by rfl⟩ : syracuseStep 2038195 = 3057293) B3057293
theorem B4585949 : Blo 2037435 4585949 := bbase (se 3 (by rfl) ⟨859865, by rfl⟩ : syracuseStep 4585949 = 1719731) (by norm_num)
theorem B3057299 : Blo 2037435 3057299 := bstep (se 1 (by rfl) ⟨2292974, by rfl⟩ : syracuseStep 3057299 = 4585949) B4585949
theorem B2038199 : Blo 2037435 2038199 := bstep (se 1 (by rfl) ⟨1528649, by rfl⟩ : syracuseStep 2038199 = 3057299) B3057299
theorem B3439469 : Blo 2037435 3439469 := bbase (se 3 (by rfl) ⟨644900, by rfl⟩ : syracuseStep 3439469 = 1289801) (by norm_num)
theorem B2292979 : Blo 2037435 2292979 := bstep (se 1 (by rfl) ⟨1719734, by rfl⟩ : syracuseStep 2292979 = 3439469) B3439469
theorem B3057305 : Blo 2037435 3057305 := bstep (se 2 (by rfl) ⟨1146489, by rfl⟩ : syracuseStep 3057305 = 2292979) B2292979
theorem B2038203 : Blo 2037435 2038203 := bstep (se 1 (by rfl) ⟨1528652, by rfl⟩ : syracuseStep 2038203 = 3057305) B3057305
theorem B12910421 : Blo 2037435 12910421 := bbase (se 9 (by rfl) ⟨37823, by rfl⟩ : syracuseStep 12910421 = 75647) (by norm_num)
theorem B8606947 : Blo 2037435 8606947 := bstep (se 1 (by rfl) ⟨6455210, by rfl⟩ : syracuseStep 8606947 = 12910421) B12910421
theorem B11475929 : Blo 2037435 11475929 := bstep (se 2 (by rfl) ⟨4303473, by rfl⟩ : syracuseStep 11475929 = 8606947) B8606947
theorem B30602477 : Blo 2037435 30602477 := bstep (se 3 (by rfl) ⟨5737964, by rfl⟩ : syracuseStep 30602477 = 11475929) B11475929
theorem B20401651 : Blo 2037435 20401651 := bstep (se 1 (by rfl) ⟨15301238, by rfl⟩ : syracuseStep 20401651 = 30602477) B30602477
theorem B108808805 : Blo 2037435 108808805 := bstep (se 4 (by rfl) ⟨10200825, by rfl⟩ : syracuseStep 108808805 = 20401651) B20401651
theorem B290156813 : Blo 2037435 290156813 := bstep (se 3 (by rfl) ⟨54404402, by rfl⟩ : syracuseStep 290156813 = 108808805) B108808805
theorem B193437875 : Blo 2037435 193437875 := bstep (se 1 (by rfl) ⟨145078406, by rfl⟩ : syracuseStep 193437875 = 290156813) B290156813
theorem B128958583 : Blo 2037435 128958583 := bstep (se 1 (by rfl) ⟨96718937, by rfl⟩ : syracuseStep 128958583 = 193437875) B193437875
theorem B171944777 : Blo 2037435 171944777 := bstep (se 2 (by rfl) ⟨64479291, by rfl⟩ : syracuseStep 171944777 = 128958583) B128958583
theorem B114629851 : Blo 2037435 114629851 := bstep (se 1 (by rfl) ⟨85972388, by rfl⟩ : syracuseStep 114629851 = 171944777) B171944777
theorem B152839801 : Blo 2037435 152839801 := bstep (se 2 (by rfl) ⟨57314925, by rfl⟩ : syracuseStep 152839801 = 114629851) B114629851
theorem B203786401 : Blo 2037435 203786401 := bstep (se 2 (by rfl) ⟨76419900, by rfl⟩ : syracuseStep 203786401 = 152839801) B152839801
theorem B271715201 : Blo 2037435 271715201 := bstep (se 2 (by rfl) ⟨101893200, by rfl⟩ : syracuseStep 271715201 = 203786401) B203786401
theorem B181143467 : Blo 2037435 181143467 := bstep (se 1 (by rfl) ⟨135857600, by rfl⟩ : syracuseStep 181143467 = 271715201) B271715201
theorem B120762311 : Blo 2037435 120762311 := bstep (se 1 (by rfl) ⟨90571733, by rfl⟩ : syracuseStep 120762311 = 181143467) B181143467
theorem B322032829 : Blo 2037435 322032829 := bstep (se 3 (by rfl) ⟨60381155, by rfl⟩ : syracuseStep 322032829 = 120762311) B120762311
theorem B429377105 : Blo 2037435 429377105 := bstep (se 2 (by rfl) ⟨161016414, by rfl⟩ : syracuseStep 429377105 = 322032829) B322032829
theorem B286251403 : Blo 2037435 286251403 := bstep (se 1 (by rfl) ⟨214688552, by rfl⟩ : syracuseStep 286251403 = 429377105) B429377105
theorem B381668537 : Blo 2037435 381668537 := bstep (se 2 (by rfl) ⟨143125701, by rfl⟩ : syracuseStep 381668537 = 286251403) B286251403
theorem B1017782765 : Blo 2037435 1017782765 := bstep (se 3 (by rfl) ⟨190834268, by rfl⟩ : syracuseStep 1017782765 = 381668537) B381668537
theorem B678521843 : Blo 2037435 678521843 := bstep (se 1 (by rfl) ⟨508891382, by rfl⟩ : syracuseStep 678521843 = 1017782765) B1017782765
theorem B452347895 : Blo 2037435 452347895 := bstep (se 1 (by rfl) ⟨339260921, by rfl⟩ : syracuseStep 452347895 = 678521843) B678521843
theorem B301565263 : Blo 2037435 301565263 := bstep (se 1 (by rfl) ⟨226173947, by rfl⟩ : syracuseStep 301565263 = 452347895) B452347895
theorem B402087017 : Blo 2037435 402087017 := bstep (se 2 (by rfl) ⟨150782631, by rfl⟩ : syracuseStep 402087017 = 301565263) B301565263
theorem B268058011 : Blo 2037435 268058011 := bstep (se 1 (by rfl) ⟨201043508, by rfl⟩ : syracuseStep 268058011 = 402087017) B402087017
theorem B357410681 : Blo 2037435 357410681 := bstep (se 2 (by rfl) ⟨134029005, by rfl⟩ : syracuseStep 357410681 = 268058011) B268058011
theorem B238273787 : Blo 2037435 238273787 := bstep (se 1 (by rfl) ⟨178705340, by rfl⟩ : syracuseStep 238273787 = 357410681) B357410681
theorem B158849191 : Blo 2037435 158849191 := bstep (se 1 (by rfl) ⟨119136893, by rfl⟩ : syracuseStep 158849191 = 238273787) B238273787
theorem B847195685 : Blo 2037435 847195685 := bstep (se 4 (by rfl) ⟨79424595, by rfl⟩ : syracuseStep 847195685 = 158849191) B158849191
theorem B564797123 : Blo 2037435 564797123 := bstep (se 1 (by rfl) ⟨423597842, by rfl⟩ : syracuseStep 564797123 = 847195685) B847195685
theorem B376531415 : Blo 2037435 376531415 := bstep (se 1 (by rfl) ⟨282398561, by rfl⟩ : syracuseStep 376531415 = 564797123) B564797123
theorem B251020943 : Blo 2037435 251020943 := bstep (se 1 (by rfl) ⟨188265707, by rfl⟩ : syracuseStep 251020943 = 376531415) B376531415
theorem B167347295 : Blo 2037435 167347295 := bstep (se 1 (by rfl) ⟨125510471, by rfl⟩ : syracuseStep 167347295 = 251020943) B251020943
theorem B111564863 : Blo 2037435 111564863 := bstep (se 1 (by rfl) ⟨83673647, by rfl⟩ : syracuseStep 111564863 = 167347295) B167347295
theorem B74376575 : Blo 2037435 74376575 := bstep (se 1 (by rfl) ⟨55782431, by rfl⟩ : syracuseStep 74376575 = 111564863) B111564863
theorem B49584383 : Blo 2037435 49584383 := bstep (se 1 (by rfl) ⟨37188287, by rfl⟩ : syracuseStep 49584383 = 74376575) B74376575
theorem B33056255 : Blo 2037435 33056255 := bstep (se 1 (by rfl) ⟨24792191, by rfl⟩ : syracuseStep 33056255 = 49584383) B49584383
theorem B22037503 : Blo 2037435 22037503 := bstep (se 1 (by rfl) ⟨16528127, by rfl⟩ : syracuseStep 22037503 = 33056255) B33056255
theorem B29383337 : Blo 2037435 29383337 := bstep (se 2 (by rfl) ⟨11018751, by rfl⟩ : syracuseStep 29383337 = 22037503) B22037503
theorem B19588891 : Blo 2037435 19588891 := bstep (se 1 (by rfl) ⟨14691668, by rfl⟩ : syracuseStep 19588891 = 29383337) B29383337
theorem B26118521 : Blo 2037435 26118521 := bstep (se 2 (by rfl) ⟨9794445, by rfl⟩ : syracuseStep 26118521 = 19588891) B19588891
theorem B17412347 : Blo 2037435 17412347 := bstep (se 1 (by rfl) ⟨13059260, by rfl⟩ : syracuseStep 17412347 = 26118521) B26118521
theorem B11608231 : Blo 2037435 11608231 := bstep (se 1 (by rfl) ⟨8706173, by rfl⟩ : syracuseStep 11608231 = 17412347) B17412347
theorem B15477641 : Blo 2037435 15477641 := bstep (se 2 (by rfl) ⟨5804115, by rfl⟩ : syracuseStep 15477641 = 11608231) B11608231
theorem B10318427 : Blo 2037435 10318427 := bstep (se 1 (by rfl) ⟨7738820, by rfl⟩ : syracuseStep 10318427 = 15477641) B15477641
theorem B6878951 : Blo 2037435 6878951 := bstep (se 1 (by rfl) ⟨5159213, by rfl⟩ : syracuseStep 6878951 = 10318427) B10318427
theorem B4585967 : Blo 2037435 4585967 := bstep (se 1 (by rfl) ⟨3439475, by rfl⟩ : syracuseStep 4585967 = 6878951) B6878951
theorem B3057311 : Blo 2037435 3057311 := bstep (se 1 (by rfl) ⟨2292983, by rfl⟩ : syracuseStep 3057311 = 4585967) B4585967
theorem B2038207 : Blo 2037435 2038207 := bstep (se 1 (by rfl) ⟨1528655, by rfl⟩ : syracuseStep 2038207 = 3057311) B3057311
theorem B3057317 : Blo 2037435 3057317 := bbase (se 4 (by rfl) ⟨286623, by rfl⟩ : syracuseStep 3057317 = 573247) (by norm_num)
theorem B2038211 : Blo 2037435 2038211 := bstep (se 1 (by rfl) ⟨1528658, by rfl⟩ : syracuseStep 2038211 = 3057317) B3057317
theorem B2579617 : Blo 2037435 2579617 := bbase (se 2 (by rfl) ⟨967356, by rfl⟩ : syracuseStep 2579617 = 1934713) (by norm_num)
theorem B3439489 : Blo 2037435 3439489 := bstep (se 2 (by rfl) ⟨1289808, by rfl⟩ : syracuseStep 3439489 = 2579617) B2579617
theorem B4585985 : Blo 2037435 4585985 := bstep (se 2 (by rfl) ⟨1719744, by rfl⟩ : syracuseStep 4585985 = 3439489) B3439489
theorem B3057323 : Blo 2037435 3057323 := bstep (se 1 (by rfl) ⟨2292992, by rfl⟩ : syracuseStep 3057323 = 4585985) B4585985
theorem B2038215 : Blo 2037435 2038215 := bstep (se 1 (by rfl) ⟨1528661, by rfl⟩ : syracuseStep 2038215 = 3057323) B3057323
theorem B2292997 : Blo 2037435 2292997 := bbase (se 4 (by rfl) ⟨214968, by rfl⟩ : syracuseStep 2292997 = 429937) (by norm_num)
theorem B3057329 : Blo 2037435 3057329 := bstep (se 2 (by rfl) ⟨1146498, by rfl⟩ : syracuseStep 3057329 = 2292997) B2292997
theorem B2038219 : Blo 2037435 2038219 := bstep (se 1 (by rfl) ⟨1528664, by rfl⟩ : syracuseStep 2038219 = 3057329) B3057329
theorem B2176561 : Blo 2037435 2176561 := bbase (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) (by norm_num)
theorem B2902081 : Blo 2037435 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B3869441 : Blo 2037435 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B2579627 : Blo 2037435 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B6879005 : Blo 2037435 6879005 := bstep (se 3 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 6879005 = 2579627) B2579627
theorem B4586003 : Blo 2037435 4586003 := bstep (se 1 (by rfl) ⟨3439502, by rfl⟩ : syracuseStep 4586003 = 6879005) B6879005
theorem B3057335 : Blo 2037435 3057335 := bstep (se 1 (by rfl) ⟨2293001, by rfl⟩ : syracuseStep 3057335 = 4586003) B4586003
theorem B2038223 : Blo 2037435 2038223 := bstep (se 1 (by rfl) ⟨1528667, by rfl⟩ : syracuseStep 2038223 = 3057335) B3057335
theorem B3057341 : Blo 2037435 3057341 := bbase (se 3 (by rfl) ⟨573251, by rfl⟩ : syracuseStep 3057341 = 1146503) (by norm_num)
theorem B2038227 : Blo 2037435 2038227 := bstep (se 1 (by rfl) ⟨1528670, by rfl⟩ : syracuseStep 2038227 = 3057341) B3057341
theorem B4586021 : Blo 2037435 4586021 := bbase (se 4 (by rfl) ⟨429939, by rfl⟩ : syracuseStep 4586021 = 859879) (by norm_num)
theorem B3057347 : Blo 2037435 3057347 := bstep (se 1 (by rfl) ⟨2293010, by rfl⟩ : syracuseStep 3057347 = 4586021) B4586021
theorem B2038231 : Blo 2037435 2038231 := bstep (se 1 (by rfl) ⟨1528673, by rfl⟩ : syracuseStep 2038231 = 3057347) B3057347
theorem B5159285 : Blo 2037435 5159285 := bbase (se 5 (by rfl) ⟨241841, by rfl⟩ : syracuseStep 5159285 = 483683) (by norm_num)
theorem B3439523 : Blo 2037435 3439523 := bstep (se 1 (by rfl) ⟨2579642, by rfl⟩ : syracuseStep 3439523 = 5159285) B5159285
theorem B2293015 : Blo 2037435 2293015 := bstep (se 1 (by rfl) ⟨1719761, by rfl⟩ : syracuseStep 2293015 = 3439523) B3439523
theorem B3057353 : Blo 2037435 3057353 := bstep (se 2 (by rfl) ⟨1146507, by rfl⟩ : syracuseStep 3057353 = 2293015) B2293015
theorem B2038235 : Blo 2037435 2038235 := bstep (se 1 (by rfl) ⟨1528676, by rfl⟩ : syracuseStep 2038235 = 3057353) B3057353
theorem B2324305 : Blo 2037435 2324305 := bbase (se 2 (by rfl) ⟨871614, by rfl⟩ : syracuseStep 2324305 = 1743229) (by norm_num)
theorem B12396293 : Blo 2037435 12396293 := bstep (se 4 (by rfl) ⟨1162152, by rfl⟩ : syracuseStep 12396293 = 2324305) B2324305
theorem B8264195 : Blo 2037435 8264195 := bstep (se 1 (by rfl) ⟨6198146, by rfl⟩ : syracuseStep 8264195 = 12396293) B12396293
theorem B5509463 : Blo 2037435 5509463 := bstep (se 1 (by rfl) ⟨4132097, by rfl⟩ : syracuseStep 5509463 = 8264195) B8264195
theorem B14691901 : Blo 2037435 14691901 := bstep (se 3 (by rfl) ⟨2754731, by rfl⟩ : syracuseStep 14691901 = 5509463) B5509463
theorem B19589201 : Blo 2037435 19589201 := bstep (se 2 (by rfl) ⟨7345950, by rfl⟩ : syracuseStep 19589201 = 14691901) B14691901
theorem B13059467 : Blo 2037435 13059467 := bstep (se 1 (by rfl) ⟨9794600, by rfl⟩ : syracuseStep 13059467 = 19589201) B19589201
theorem B8706311 : Blo 2037435 8706311 := bstep (se 1 (by rfl) ⟨6529733, by rfl⟩ : syracuseStep 8706311 = 13059467) B13059467
theorem B5804207 : Blo 2037435 5804207 := bstep (se 1 (by rfl) ⟨4353155, by rfl⟩ : syracuseStep 5804207 = 8706311) B8706311
theorem B3869471 : Blo 2037435 3869471 := bstep (se 1 (by rfl) ⟨2902103, by rfl⟩ : syracuseStep 3869471 = 5804207) B5804207
theorem B10318589 : Blo 2037435 10318589 := bstep (se 3 (by rfl) ⟨1934735, by rfl⟩ : syracuseStep 10318589 = 3869471) B3869471
theorem B6879059 : Blo 2037435 6879059 := bstep (se 1 (by rfl) ⟨5159294, by rfl⟩ : syracuseStep 6879059 = 10318589) B10318589
theorem B4586039 : Blo 2037435 4586039 := bstep (se 1 (by rfl) ⟨3439529, by rfl⟩ : syracuseStep 4586039 = 6879059) B6879059
theorem B3057359 : Blo 2037435 3057359 := bstep (se 1 (by rfl) ⟨2293019, by rfl⟩ : syracuseStep 3057359 = 4586039) B4586039
theorem B2038239 : Blo 2037435 2038239 := bstep (se 1 (by rfl) ⟨1528679, by rfl⟩ : syracuseStep 2038239 = 3057359) B3057359
theorem B3057365 : Blo 2037435 3057365 := bbase (se 7 (by rfl) ⟨35828, by rfl⟩ : syracuseStep 3057365 = 71657) (by norm_num)
theorem B2038243 : Blo 2037435 2038243 := bstep (se 1 (by rfl) ⟨1528682, by rfl⟩ : syracuseStep 2038243 = 3057365) B3057365
theorem B4353173 : Blo 2037435 4353173 := bbase (se 6 (by rfl) ⟨102027, by rfl⟩ : syracuseStep 4353173 = 204055) (by norm_num)
theorem B2902115 : Blo 2037435 2902115 := bstep (se 1 (by rfl) ⟨2176586, by rfl⟩ : syracuseStep 2902115 = 4353173) B4353173
theorem B7738973 : Blo 2037435 7738973 := bstep (se 3 (by rfl) ⟨1451057, by rfl⟩ : syracuseStep 7738973 = 2902115) B2902115
theorem B5159315 : Blo 2037435 5159315 := bstep (se 1 (by rfl) ⟨3869486, by rfl⟩ : syracuseStep 5159315 = 7738973) B7738973
theorem B3439543 : Blo 2037435 3439543 := bstep (se 1 (by rfl) ⟨2579657, by rfl⟩ : syracuseStep 3439543 = 5159315) B5159315
theorem B4586057 : Blo 2037435 4586057 := bstep (se 2 (by rfl) ⟨1719771, by rfl⟩ : syracuseStep 4586057 = 3439543) B3439543
theorem B3057371 : Blo 2037435 3057371 := bstep (se 1 (by rfl) ⟨2293028, by rfl⟩ : syracuseStep 3057371 = 4586057) B4586057
theorem B2038247 : Blo 2037435 2038247 := bstep (se 1 (by rfl) ⟨1528685, by rfl⟩ : syracuseStep 2038247 = 3057371) B3057371
theorem B2293033 : Blo 2037435 2293033 := bbase (se 2 (by rfl) ⟨859887, by rfl⟩ : syracuseStep 2293033 = 1719775) (by norm_num)
theorem B3057377 : Blo 2037435 3057377 := bstep (se 2 (by rfl) ⟨1146516, by rfl⟩ : syracuseStep 3057377 = 2293033) B2293033
theorem B2038251 : Blo 2037435 2038251 := bstep (se 1 (by rfl) ⟨1528688, by rfl⟩ : syracuseStep 2038251 = 3057377) B3057377
theorem B9794677 : Blo 2037435 9794677 := bbase (se 5 (by rfl) ⟨459125, by rfl⟩ : syracuseStep 9794677 = 918251) (by norm_num)
theorem B13059569 : Blo 2037435 13059569 := bstep (se 2 (by rfl) ⟨4897338, by rfl⟩ : syracuseStep 13059569 = 9794677) B9794677
theorem B8706379 : Blo 2037435 8706379 := bstep (se 1 (by rfl) ⟨6529784, by rfl⟩ : syracuseStep 8706379 = 13059569) B13059569
theorem B11608505 : Blo 2037435 11608505 := bstep (se 2 (by rfl) ⟨4353189, by rfl⟩ : syracuseStep 11608505 = 8706379) B8706379
theorem B7739003 : Blo 2037435 7739003 := bstep (se 1 (by rfl) ⟨5804252, by rfl⟩ : syracuseStep 7739003 = 11608505) B11608505
theorem B5159335 : Blo 2037435 5159335 := bstep (se 1 (by rfl) ⟨3869501, by rfl⟩ : syracuseStep 5159335 = 7739003) B7739003
theorem B6879113 : Blo 2037435 6879113 := bstep (se 2 (by rfl) ⟨2579667, by rfl⟩ : syracuseStep 6879113 = 5159335) B5159335
theorem B4586075 : Blo 2037435 4586075 := bstep (se 1 (by rfl) ⟨3439556, by rfl⟩ : syracuseStep 4586075 = 6879113) B6879113
theorem B3057383 : Blo 2037435 3057383 := bstep (se 1 (by rfl) ⟨2293037, by rfl⟩ : syracuseStep 3057383 = 4586075) B4586075
theorem B2038255 : Blo 2037435 2038255 := bstep (se 1 (by rfl) ⟨1528691, by rfl⟩ : syracuseStep 2038255 = 3057383) B3057383
theorem B3057389 : Blo 2037435 3057389 := bbase (se 3 (by rfl) ⟨573260, by rfl⟩ : syracuseStep 3057389 = 1146521) (by norm_num)
theorem B2038259 : Blo 2037435 2038259 := bstep (se 1 (by rfl) ⟨1528694, by rfl⟩ : syracuseStep 2038259 = 3057389) B3057389
theorem B4586093 : Blo 2037435 4586093 := bbase (se 3 (by rfl) ⟨859892, by rfl⟩ : syracuseStep 4586093 = 1719785) (by norm_num)
theorem B3057395 : Blo 2037435 3057395 := bstep (se 1 (by rfl) ⟨2293046, by rfl⟩ : syracuseStep 3057395 = 4586093) B4586093
theorem B2038263 : Blo 2037435 2038263 := bstep (se 1 (by rfl) ⟨1528697, by rfl⟩ : syracuseStep 2038263 = 3057395) B3057395
theorem B3869525 : Blo 2037435 3869525 := bbase (se 9 (by rfl) ⟨11336, by rfl⟩ : syracuseStep 3869525 = 22673) (by norm_num)
theorem B2579683 : Blo 2037435 2579683 := bstep (se 1 (by rfl) ⟨1934762, by rfl⟩ : syracuseStep 2579683 = 3869525) B3869525
theorem B3439577 : Blo 2037435 3439577 := bstep (se 2 (by rfl) ⟨1289841, by rfl⟩ : syracuseStep 3439577 = 2579683) B2579683
theorem B2293051 : Blo 2037435 2293051 := bstep (se 1 (by rfl) ⟨1719788, by rfl⟩ : syracuseStep 2293051 = 3439577) B3439577
theorem B3057401 : Blo 2037435 3057401 := bstep (se 2 (by rfl) ⟨1146525, by rfl⟩ : syracuseStep 3057401 = 2293051) B2293051
theorem B2038267 : Blo 2037435 2038267 := bstep (se 1 (by rfl) ⟨1528700, by rfl⟩ : syracuseStep 2038267 = 3057401) B3057401
theorem B2324341 : Blo 2037435 2324341 := bbase (se 5 (by rfl) ⟨108953, by rfl⟩ : syracuseStep 2324341 = 217907) (by norm_num)
theorem B12396485 : Blo 2037435 12396485 := bstep (se 4 (by rfl) ⟨1162170, by rfl⟩ : syracuseStep 12396485 = 2324341) B2324341
theorem B8264323 : Blo 2037435 8264323 := bstep (se 1 (by rfl) ⟨6198242, by rfl⟩ : syracuseStep 8264323 = 12396485) B12396485
theorem B11019097 : Blo 2037435 11019097 := bstep (se 2 (by rfl) ⟨4132161, by rfl⟩ : syracuseStep 11019097 = 8264323) B8264323
theorem B58768517 : Blo 2037435 58768517 := bstep (se 4 (by rfl) ⟨5509548, by rfl⟩ : syracuseStep 58768517 = 11019097) B11019097
theorem B39179011 : Blo 2037435 39179011 := bstep (se 1 (by rfl) ⟨29384258, by rfl⟩ : syracuseStep 39179011 = 58768517) B58768517
theorem B52238681 : Blo 2037435 52238681 := bstep (se 2 (by rfl) ⟨19589505, by rfl⟩ : syracuseStep 52238681 = 39179011) B39179011
theorem B34825787 : Blo 2037435 34825787 := bstep (se 1 (by rfl) ⟨26119340, by rfl⟩ : syracuseStep 34825787 = 52238681) B52238681
theorem B23217191 : Blo 2037435 23217191 := bstep (se 1 (by rfl) ⟨17412893, by rfl⟩ : syracuseStep 23217191 = 34825787) B34825787
theorem B15478127 : Blo 2037435 15478127 := bstep (se 1 (by rfl) ⟨11608595, by rfl⟩ : syracuseStep 15478127 = 23217191) B23217191
theorem B10318751 : Blo 2037435 10318751 := bstep (se 1 (by rfl) ⟨7739063, by rfl⟩ : syracuseStep 10318751 = 15478127) B15478127
theorem B6879167 : Blo 2037435 6879167 := bstep (se 1 (by rfl) ⟨5159375, by rfl⟩ : syracuseStep 6879167 = 10318751) B10318751
theorem B4586111 : Blo 2037435 4586111 := bstep (se 1 (by rfl) ⟨3439583, by rfl⟩ : syracuseStep 4586111 = 6879167) B6879167
theorem B3057407 : Blo 2037435 3057407 := bstep (se 1 (by rfl) ⟨2293055, by rfl⟩ : syracuseStep 3057407 = 4586111) B4586111
theorem B2038271 : Blo 2037435 2038271 := bstep (se 1 (by rfl) ⟨1528703, by rfl⟩ : syracuseStep 2038271 = 3057407) B3057407
theorem B3057413 : Blo 2037435 3057413 := bbase (se 4 (by rfl) ⟨286632, by rfl⟩ : syracuseStep 3057413 = 573265) (by norm_num)
theorem B2038275 : Blo 2037435 2038275 := bstep (se 1 (by rfl) ⟨1528706, by rfl⟩ : syracuseStep 2038275 = 3057413) B3057413
theorem B3439597 : Blo 2037435 3439597 := bbase (se 3 (by rfl) ⟨644924, by rfl⟩ : syracuseStep 3439597 = 1289849) (by norm_num)
theorem B4586129 : Blo 2037435 4586129 := bstep (se 2 (by rfl) ⟨1719798, by rfl⟩ : syracuseStep 4586129 = 3439597) B3439597
theorem B3057419 : Blo 2037435 3057419 := bstep (se 1 (by rfl) ⟨2293064, by rfl⟩ : syracuseStep 3057419 = 4586129) B4586129
theorem B2038279 : Blo 2037435 2038279 := bstep (se 1 (by rfl) ⟨1528709, by rfl⟩ : syracuseStep 2038279 = 3057419) B3057419
theorem B2293069 : Blo 2037435 2293069 := bbase (se 3 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 2293069 = 859901) (by norm_num)
theorem B3057425 : Blo 2037435 3057425 := bstep (se 2 (by rfl) ⟨1146534, by rfl⟩ : syracuseStep 3057425 = 2293069) B2293069
theorem B2038283 : Blo 2037435 2038283 := bstep (se 1 (by rfl) ⟨1528712, by rfl⟩ : syracuseStep 2038283 = 3057425) B3057425
theorem B6879221 : Blo 2037435 6879221 := bbase (se 5 (by rfl) ⟨322463, by rfl⟩ : syracuseStep 6879221 = 644927) (by norm_num)
theorem B4586147 : Blo 2037435 4586147 := bstep (se 1 (by rfl) ⟨3439610, by rfl⟩ : syracuseStep 4586147 = 6879221) B6879221
theorem B3057431 : Blo 2037435 3057431 := bstep (se 1 (by rfl) ⟨2293073, by rfl⟩ : syracuseStep 3057431 = 4586147) B4586147
theorem B2038287 : Blo 2037435 2038287 := bstep (se 1 (by rfl) ⟨1528715, by rfl⟩ : syracuseStep 2038287 = 3057431) B3057431
theorem B3057437 : Blo 2037435 3057437 := bbase (se 3 (by rfl) ⟨573269, by rfl⟩ : syracuseStep 3057437 = 1146539) (by norm_num)
theorem B2038291 : Blo 2037435 2038291 := bstep (se 1 (by rfl) ⟨1528718, by rfl⟩ : syracuseStep 2038291 = 3057437) B3057437
theorem B4586165 : Blo 2037435 4586165 := bbase (se 5 (by rfl) ⟨214976, by rfl⟩ : syracuseStep 4586165 = 429953) (by norm_num)
theorem B3057443 : Blo 2037435 3057443 := bstep (se 1 (by rfl) ⟨2293082, by rfl⟩ : syracuseStep 3057443 = 4586165) B4586165
theorem B2038295 : Blo 2037435 2038295 := bstep (se 1 (by rfl) ⟨1528721, by rfl⟩ : syracuseStep 2038295 = 3057443) B3057443
theorem B11608757 : Blo 2037435 11608757 := bbase (se 5 (by rfl) ⟨544160, by rfl⟩ : syracuseStep 11608757 = 1088321) (by norm_num)
theorem B7739171 : Blo 2037435 7739171 := bstep (se 1 (by rfl) ⟨5804378, by rfl⟩ : syracuseStep 7739171 = 11608757) B11608757
theorem B5159447 : Blo 2037435 5159447 := bstep (se 1 (by rfl) ⟨3869585, by rfl⟩ : syracuseStep 5159447 = 7739171) B7739171
theorem B3439631 : Blo 2037435 3439631 := bstep (se 1 (by rfl) ⟨2579723, by rfl⟩ : syracuseStep 3439631 = 5159447) B5159447
theorem B2293087 : Blo 2037435 2293087 := bstep (se 1 (by rfl) ⟨1719815, by rfl⟩ : syracuseStep 2293087 = 3439631) B3439631
theorem B3057449 : Blo 2037435 3057449 := bstep (se 2 (by rfl) ⟨1146543, by rfl⟩ : syracuseStep 3057449 = 2293087) B2293087
theorem B2038299 : Blo 2037435 2038299 := bstep (se 1 (by rfl) ⟨1528724, by rfl⟩ : syracuseStep 2038299 = 3057449) B3057449
theorem B5804389 : Blo 2037435 5804389 := bbase (se 4 (by rfl) ⟨544161, by rfl⟩ : syracuseStep 5804389 = 1088323) (by norm_num)
theorem B7739185 : Blo 2037435 7739185 := bstep (se 2 (by rfl) ⟨2902194, by rfl⟩ : syracuseStep 7739185 = 5804389) B5804389
theorem B10318913 : Blo 2037435 10318913 := bstep (se 2 (by rfl) ⟨3869592, by rfl⟩ : syracuseStep 10318913 = 7739185) B7739185
theorem B6879275 : Blo 2037435 6879275 := bstep (se 1 (by rfl) ⟨5159456, by rfl⟩ : syracuseStep 6879275 = 10318913) B10318913
theorem B4586183 : Blo 2037435 4586183 := bstep (se 1 (by rfl) ⟨3439637, by rfl⟩ : syracuseStep 4586183 = 6879275) B6879275
theorem B3057455 : Blo 2037435 3057455 := bstep (se 1 (by rfl) ⟨2293091, by rfl⟩ : syracuseStep 3057455 = 4586183) B4586183
theorem B2038303 : Blo 2037435 2038303 := bstep (se 1 (by rfl) ⟨1528727, by rfl⟩ : syracuseStep 2038303 = 3057455) B3057455
theorem B3057461 : Blo 2037435 3057461 := bbase (se 5 (by rfl) ⟨143318, by rfl⟩ : syracuseStep 3057461 = 286637) (by norm_num)
theorem B2038307 : Blo 2037435 2038307 := bstep (se 1 (by rfl) ⟨1528730, by rfl⟩ : syracuseStep 2038307 = 3057461) B3057461
theorem B5159477 : Blo 2037435 5159477 := bbase (se 5 (by rfl) ⟨241850, by rfl⟩ : syracuseStep 5159477 = 483701) (by norm_num)
theorem B3439651 : Blo 2037435 3439651 := bstep (se 1 (by rfl) ⟨2579738, by rfl⟩ : syracuseStep 3439651 = 5159477) B5159477
theorem B4586201 : Blo 2037435 4586201 := bstep (se 2 (by rfl) ⟨1719825, by rfl⟩ : syracuseStep 4586201 = 3439651) B3439651
theorem B3057467 : Blo 2037435 3057467 := bstep (se 1 (by rfl) ⟨2293100, by rfl⟩ : syracuseStep 3057467 = 4586201) B4586201
theorem B2038311 : Blo 2037435 2038311 := bstep (se 1 (by rfl) ⟨1528733, by rfl⟩ : syracuseStep 2038311 = 3057467) B3057467
theorem B2293105 : Blo 2037435 2293105 := bbase (se 2 (by rfl) ⟨859914, by rfl⟩ : syracuseStep 2293105 = 1719829) (by norm_num)
theorem B3057473 : Blo 2037435 3057473 := bstep (se 2 (by rfl) ⟨1146552, by rfl⟩ : syracuseStep 3057473 = 2293105) B2293105
theorem B2038315 : Blo 2037435 2038315 := bstep (se 1 (by rfl) ⟨1528736, by rfl⟩ : syracuseStep 2038315 = 3057473) B3057473
theorem B4897493 : Blo 2037435 4897493 := bbase (se 7 (by rfl) ⟨57392, by rfl⟩ : syracuseStep 4897493 = 114785) (by norm_num)
theorem B3264995 : Blo 2037435 3264995 := bstep (se 1 (by rfl) ⟨2448746, by rfl⟩ : syracuseStep 3264995 = 4897493) B4897493
theorem B8706653 : Blo 2037435 8706653 := bstep (se 3 (by rfl) ⟨1632497, by rfl⟩ : syracuseStep 8706653 = 3264995) B3264995
theorem B5804435 : Blo 2037435 5804435 := bstep (se 1 (by rfl) ⟨4353326, by rfl⟩ : syracuseStep 5804435 = 8706653) B8706653
theorem B3869623 : Blo 2037435 3869623 := bstep (se 1 (by rfl) ⟨2902217, by rfl⟩ : syracuseStep 3869623 = 5804435) B5804435
theorem B5159497 : Blo 2037435 5159497 := bstep (se 2 (by rfl) ⟨1934811, by rfl⟩ : syracuseStep 5159497 = 3869623) B3869623
theorem B6879329 : Blo 2037435 6879329 := bstep (se 2 (by rfl) ⟨2579748, by rfl⟩ : syracuseStep 6879329 = 5159497) B5159497
theorem B4586219 : Blo 2037435 4586219 := bstep (se 1 (by rfl) ⟨3439664, by rfl⟩ : syracuseStep 4586219 = 6879329) B6879329
theorem B3057479 : Blo 2037435 3057479 := bstep (se 1 (by rfl) ⟨2293109, by rfl⟩ : syracuseStep 3057479 = 4586219) B4586219
theorem B2038319 : Blo 2037435 2038319 := bstep (se 1 (by rfl) ⟨1528739, by rfl⟩ : syracuseStep 2038319 = 3057479) B3057479
theorem B3057485 : Blo 2037435 3057485 := bbase (se 3 (by rfl) ⟨573278, by rfl⟩ : syracuseStep 3057485 = 1146557) (by norm_num)
theorem B2038323 : Blo 2037435 2038323 := bstep (se 1 (by rfl) ⟨1528742, by rfl⟩ : syracuseStep 2038323 = 3057485) B3057485
theorem B4586237 : Blo 2037435 4586237 := bbase (se 3 (by rfl) ⟨859919, by rfl⟩ : syracuseStep 4586237 = 1719839) (by norm_num)
theorem B3057491 : Blo 2037435 3057491 := bstep (se 1 (by rfl) ⟨2293118, by rfl⟩ : syracuseStep 3057491 = 4586237) B4586237
theorem B2038327 : Blo 2037435 2038327 := bstep (se 1 (by rfl) ⟨1528745, by rfl⟩ : syracuseStep 2038327 = 3057491) B3057491
theorem B3439685 : Blo 2037435 3439685 := bbase (se 4 (by rfl) ⟨322470, by rfl⟩ : syracuseStep 3439685 = 644941) (by norm_num)
theorem B2293123 : Blo 2037435 2293123 := bstep (se 1 (by rfl) ⟨1719842, by rfl⟩ : syracuseStep 2293123 = 3439685) B3439685
theorem B3057497 : Blo 2037435 3057497 := bstep (se 2 (by rfl) ⟨1146561, by rfl⟩ : syracuseStep 3057497 = 2293123) B2293123
theorem B2038331 : Blo 2037435 2038331 := bstep (se 1 (by rfl) ⟨1528748, by rfl⟩ : syracuseStep 2038331 = 3057497) B3057497
theorem B15478613 : Blo 2037435 15478613 := bbase (se 9 (by rfl) ⟨45347, by rfl⟩ : syracuseStep 15478613 = 90695) (by norm_num)
theorem B10319075 : Blo 2037435 10319075 := bstep (se 1 (by rfl) ⟨7739306, by rfl⟩ : syracuseStep 10319075 = 15478613) B15478613
theorem B6879383 : Blo 2037435 6879383 := bstep (se 1 (by rfl) ⟨5159537, by rfl⟩ : syracuseStep 6879383 = 10319075) B10319075
theorem B4586255 : Blo 2037435 4586255 := bstep (se 1 (by rfl) ⟨3439691, by rfl⟩ : syracuseStep 4586255 = 6879383) B6879383
theorem B3057503 : Blo 2037435 3057503 := bstep (se 1 (by rfl) ⟨2293127, by rfl⟩ : syracuseStep 3057503 = 4586255) B4586255
theorem B2038335 : Blo 2037435 2038335 := bstep (se 1 (by rfl) ⟨1528751, by rfl⟩ : syracuseStep 2038335 = 3057503) B3057503
theorem B3057509 : Blo 2037435 3057509 := bbase (se 4 (by rfl) ⟨286641, by rfl⟩ : syracuseStep 3057509 = 573283) (by norm_num)
theorem B2038339 : Blo 2037435 2038339 := bstep (se 1 (by rfl) ⟨1528754, by rfl⟩ : syracuseStep 2038339 = 3057509) B3057509
theorem B3869669 : Blo 2037435 3869669 := bbase (se 4 (by rfl) ⟨362781, by rfl⟩ : syracuseStep 3869669 = 725563) (by norm_num)
theorem B2579779 : Blo 2037435 2579779 := bstep (se 1 (by rfl) ⟨1934834, by rfl⟩ : syracuseStep 2579779 = 3869669) B3869669
theorem B3439705 : Blo 2037435 3439705 := bstep (se 2 (by rfl) ⟨1289889, by rfl⟩ : syracuseStep 3439705 = 2579779) B2579779
theorem B4586273 : Blo 2037435 4586273 := bstep (se 2 (by rfl) ⟨1719852, by rfl⟩ : syracuseStep 4586273 = 3439705) B3439705
theorem B3057515 : Blo 2037435 3057515 := bstep (se 1 (by rfl) ⟨2293136, by rfl⟩ : syracuseStep 3057515 = 4586273) B4586273
theorem B2038343 : Blo 2037435 2038343 := bstep (se 1 (by rfl) ⟨1528757, by rfl⟩ : syracuseStep 2038343 = 3057515) B3057515
theorem B2293141 : Blo 2037435 2293141 := bbase (se 6 (by rfl) ⟨53745, by rfl⟩ : syracuseStep 2293141 = 107491) (by norm_num)
theorem B3057521 : Blo 2037435 3057521 := bstep (se 2 (by rfl) ⟨1146570, by rfl⟩ : syracuseStep 3057521 = 2293141) B2293141
theorem B2038347 : Blo 2037435 2038347 := bstep (se 1 (by rfl) ⟨1528760, by rfl⟩ : syracuseStep 2038347 = 3057521) B3057521
theorem B2579789 : Blo 2037435 2579789 := bbase (se 3 (by rfl) ⟨483710, by rfl⟩ : syracuseStep 2579789 = 967421) (by norm_num)
theorem B6879437 : Blo 2037435 6879437 := bstep (se 3 (by rfl) ⟨1289894, by rfl⟩ : syracuseStep 6879437 = 2579789) B2579789
theorem B4586291 : Blo 2037435 4586291 := bstep (se 1 (by rfl) ⟨3439718, by rfl⟩ : syracuseStep 4586291 = 6879437) B6879437
theorem B3057527 : Blo 2037435 3057527 := bstep (se 1 (by rfl) ⟨2293145, by rfl⟩ : syracuseStep 3057527 = 4586291) B4586291
theorem B2038351 : Blo 2037435 2038351 := bstep (se 1 (by rfl) ⟨1528763, by rfl⟩ : syracuseStep 2038351 = 3057527) B3057527
theorem B3057533 : Blo 2037435 3057533 := bbase (se 3 (by rfl) ⟨573287, by rfl⟩ : syracuseStep 3057533 = 1146575) (by norm_num)
theorem B2038355 : Blo 2037435 2038355 := bstep (se 1 (by rfl) ⟨1528766, by rfl⟩ : syracuseStep 2038355 = 3057533) B3057533
theorem B4586309 : Blo 2037435 4586309 := bbase (se 4 (by rfl) ⟨429966, by rfl⟩ : syracuseStep 4586309 = 859933) (by norm_num)
theorem B3057539 : Blo 2037435 3057539 := bstep (se 1 (by rfl) ⟨2293154, by rfl⟩ : syracuseStep 3057539 = 4586309) B4586309
theorem B2038359 : Blo 2037435 2038359 := bstep (se 1 (by rfl) ⟨1528769, by rfl⟩ : syracuseStep 2038359 = 3057539) B3057539
theorem B4353421 : Blo 2037435 4353421 := bbase (se 3 (by rfl) ⟨816266, by rfl⟩ : syracuseStep 4353421 = 1632533) (by norm_num)
theorem B5804561 : Blo 2037435 5804561 := bstep (se 2 (by rfl) ⟨2176710, by rfl⟩ : syracuseStep 5804561 = 4353421) B4353421
theorem B3869707 : Blo 2037435 3869707 := bstep (se 1 (by rfl) ⟨2902280, by rfl⟩ : syracuseStep 3869707 = 5804561) B5804561
theorem B5159609 : Blo 2037435 5159609 := bstep (se 2 (by rfl) ⟨1934853, by rfl⟩ : syracuseStep 5159609 = 3869707) B3869707
theorem B3439739 : Blo 2037435 3439739 := bstep (se 1 (by rfl) ⟨2579804, by rfl⟩ : syracuseStep 3439739 = 5159609) B5159609
theorem B2293159 : Blo 2037435 2293159 := bstep (se 1 (by rfl) ⟨1719869, by rfl⟩ : syracuseStep 2293159 = 3439739) B3439739
theorem B3057545 : Blo 2037435 3057545 := bstep (se 2 (by rfl) ⟨1146579, by rfl⟩ : syracuseStep 3057545 = 2293159) B2293159
theorem B2038363 : Blo 2037435 2038363 := bstep (se 1 (by rfl) ⟨1528772, by rfl⟩ : syracuseStep 2038363 = 3057545) B3057545
theorem B10319237 : Blo 2037435 10319237 := bbase (se 4 (by rfl) ⟨967428, by rfl⟩ : syracuseStep 10319237 = 1934857) (by norm_num)
theorem B6879491 : Blo 2037435 6879491 := bstep (se 1 (by rfl) ⟨5159618, by rfl⟩ : syracuseStep 6879491 = 10319237) B10319237
theorem B4586327 : Blo 2037435 4586327 := bstep (se 1 (by rfl) ⟨3439745, by rfl⟩ : syracuseStep 4586327 = 6879491) B6879491
theorem B3057551 : Blo 2037435 3057551 := bstep (se 1 (by rfl) ⟨2293163, by rfl⟩ : syracuseStep 3057551 = 4586327) B4586327
theorem B2038367 : Blo 2037435 2038367 := bstep (se 1 (by rfl) ⟨1528775, by rfl⟩ : syracuseStep 2038367 = 3057551) B3057551
theorem B3057557 : Blo 2037435 3057557 := bbase (se 6 (by rfl) ⟨71661, by rfl⟩ : syracuseStep 3057557 = 143323) (by norm_num)
theorem B2038371 : Blo 2037435 2038371 := bstep (se 1 (by rfl) ⟨1528778, by rfl⟩ : syracuseStep 2038371 = 3057557) B3057557
theorem B3265085 : Blo 2037435 3265085 := bbase (se 3 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 3265085 = 1224407) (by norm_num)
theorem B2176723 : Blo 2037435 2176723 := bstep (se 1 (by rfl) ⟨1632542, by rfl⟩ : syracuseStep 2176723 = 3265085) B3265085
theorem B11609189 : Blo 2037435 11609189 := bstep (se 4 (by rfl) ⟨1088361, by rfl⟩ : syracuseStep 11609189 = 2176723) B2176723
theorem B7739459 : Blo 2037435 7739459 := bstep (se 1 (by rfl) ⟨5804594, by rfl⟩ : syracuseStep 7739459 = 11609189) B11609189
theorem B5159639 : Blo 2037435 5159639 := bstep (se 1 (by rfl) ⟨3869729, by rfl⟩ : syracuseStep 5159639 = 7739459) B7739459
theorem B3439759 : Blo 2037435 3439759 := bstep (se 1 (by rfl) ⟨2579819, by rfl⟩ : syracuseStep 3439759 = 5159639) B5159639
theorem B4586345 : Blo 2037435 4586345 := bstep (se 2 (by rfl) ⟨1719879, by rfl⟩ : syracuseStep 4586345 = 3439759) B3439759
theorem B3057563 : Blo 2037435 3057563 := bstep (se 1 (by rfl) ⟨2293172, by rfl⟩ : syracuseStep 3057563 = 4586345) B4586345
theorem B2038375 : Blo 2037435 2038375 := bstep (se 1 (by rfl) ⟨1528781, by rfl⟩ : syracuseStep 2038375 = 3057563) B3057563
theorem B2293177 : Blo 2037435 2293177 := bbase (se 2 (by rfl) ⟨859941, by rfl⟩ : syracuseStep 2293177 = 1719883) (by norm_num)
theorem B3057569 : Blo 2037435 3057569 := bstep (se 2 (by rfl) ⟨1146588, by rfl⟩ : syracuseStep 3057569 = 2293177) B2293177
theorem B2038379 : Blo 2037435 2038379 := bstep (se 1 (by rfl) ⟨1528784, by rfl⟩ : syracuseStep 2038379 = 3057569) B3057569
theorem B3099293 : Blo 2037435 3099293 := bbase (se 3 (by rfl) ⟨581117, by rfl⟩ : syracuseStep 3099293 = 1162235) (by norm_num)
theorem B2066195 : Blo 2037435 2066195 := bstep (se 1 (by rfl) ⟨1549646, by rfl⟩ : syracuseStep 2066195 = 3099293) B3099293
theorem B5509853 : Blo 2037435 5509853 := bstep (se 3 (by rfl) ⟨1033097, by rfl⟩ : syracuseStep 5509853 = 2066195) B2066195
theorem B3673235 : Blo 2037435 3673235 := bstep (se 1 (by rfl) ⟨2754926, by rfl⟩ : syracuseStep 3673235 = 5509853) B5509853
theorem B9795293 : Blo 2037435 9795293 := bstep (se 3 (by rfl) ⟨1836617, by rfl⟩ : syracuseStep 9795293 = 3673235) B3673235
theorem B6530195 : Blo 2037435 6530195 := bstep (se 1 (by rfl) ⟨4897646, by rfl⟩ : syracuseStep 6530195 = 9795293) B9795293
theorem B4353463 : Blo 2037435 4353463 := bstep (se 1 (by rfl) ⟨3265097, by rfl⟩ : syracuseStep 4353463 = 6530195) B6530195
theorem B5804617 : Blo 2037435 5804617 := bstep (se 2 (by rfl) ⟨2176731, by rfl⟩ : syracuseStep 5804617 = 4353463) B4353463
theorem B7739489 : Blo 2037435 7739489 := bstep (se 2 (by rfl) ⟨2902308, by rfl⟩ : syracuseStep 7739489 = 5804617) B5804617
theorem B5159659 : Blo 2037435 5159659 := bstep (se 1 (by rfl) ⟨3869744, by rfl⟩ : syracuseStep 5159659 = 7739489) B7739489
theorem B6879545 : Blo 2037435 6879545 := bstep (se 2 (by rfl) ⟨2579829, by rfl⟩ : syracuseStep 6879545 = 5159659) B5159659
theorem B4586363 : Blo 2037435 4586363 := bstep (se 1 (by rfl) ⟨3439772, by rfl⟩ : syracuseStep 4586363 = 6879545) B6879545
theorem B3057575 : Blo 2037435 3057575 := bstep (se 1 (by rfl) ⟨2293181, by rfl⟩ : syracuseStep 3057575 = 4586363) B4586363
theorem B2038383 : Blo 2037435 2038383 := bstep (se 1 (by rfl) ⟨1528787, by rfl⟩ : syracuseStep 2038383 = 3057575) B3057575
theorem B3057581 : Blo 2037435 3057581 := bbase (se 3 (by rfl) ⟨573296, by rfl⟩ : syracuseStep 3057581 = 1146593) (by norm_num)
theorem B2038387 : Blo 2037435 2038387 := bstep (se 1 (by rfl) ⟨1528790, by rfl⟩ : syracuseStep 2038387 = 3057581) B3057581
theorem B4586381 : Blo 2037435 4586381 := bbase (se 3 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 4586381 = 1719893) (by norm_num)
theorem B3057587 : Blo 2037435 3057587 := bstep (se 1 (by rfl) ⟨2293190, by rfl⟩ : syracuseStep 3057587 = 4586381) B4586381
theorem B2038391 : Blo 2037435 2038391 := bstep (se 1 (by rfl) ⟨1528793, by rfl⟩ : syracuseStep 2038391 = 3057587) B3057587
theorem B2579845 : Blo 2037435 2579845 := bbase (se 4 (by rfl) ⟨241860, by rfl⟩ : syracuseStep 2579845 = 483721) (by norm_num)
theorem B3439793 : Blo 2037435 3439793 := bstep (se 2 (by rfl) ⟨1289922, by rfl⟩ : syracuseStep 3439793 = 2579845) B2579845
theorem B2293195 : Blo 2037435 2293195 := bstep (se 1 (by rfl) ⟨1719896, by rfl⟩ : syracuseStep 2293195 = 3439793) B3439793
theorem B3057593 : Blo 2037435 3057593 := bstep (se 2 (by rfl) ⟨1146597, by rfl⟩ : syracuseStep 3057593 = 2293195) B2293195
theorem B2038395 : Blo 2037435 2038395 := bstep (se 1 (by rfl) ⟨1528796, by rfl⟩ : syracuseStep 2038395 = 3057593) B3057593
theorem B26120981 : Blo 2037435 26120981 := bbase (se 6 (by rfl) ⟨612210, by rfl⟩ : syracuseStep 26120981 = 1224421) (by norm_num)
theorem B17413987 : Blo 2037435 17413987 := bstep (se 1 (by rfl) ⟨13060490, by rfl⟩ : syracuseStep 17413987 = 26120981) B26120981
theorem B23218649 : Blo 2037435 23218649 := bstep (se 2 (by rfl) ⟨8706993, by rfl⟩ : syracuseStep 23218649 = 17413987) B17413987
theorem B15479099 : Blo 2037435 15479099 := bstep (se 1 (by rfl) ⟨11609324, by rfl⟩ : syracuseStep 15479099 = 23218649) B23218649
theorem B10319399 : Blo 2037435 10319399 := bstep (se 1 (by rfl) ⟨7739549, by rfl⟩ : syracuseStep 10319399 = 15479099) B15479099
theorem B6879599 : Blo 2037435 6879599 := bstep (se 1 (by rfl) ⟨5159699, by rfl⟩ : syracuseStep 6879599 = 10319399) B10319399
theorem B4586399 : Blo 2037435 4586399 := bstep (se 1 (by rfl) ⟨3439799, by rfl⟩ : syracuseStep 4586399 = 6879599) B6879599
theorem B3057599 : Blo 2037435 3057599 := bstep (se 1 (by rfl) ⟨2293199, by rfl⟩ : syracuseStep 3057599 = 4586399) B4586399
theorem B2038399 : Blo 2037435 2038399 := bstep (se 1 (by rfl) ⟨1528799, by rfl⟩ : syracuseStep 2038399 = 3057599) B3057599
theorem B3057605 : Blo 2037435 3057605 := bbase (se 4 (by rfl) ⟨286650, by rfl⟩ : syracuseStep 3057605 = 573301) (by norm_num)
theorem B2038403 : Blo 2037435 2038403 := bstep (se 1 (by rfl) ⟨1528802, by rfl⟩ : syracuseStep 2038403 = 3057605) B3057605
theorem B3439813 : Blo 2037435 3439813 := bbase (se 4 (by rfl) ⟨322482, by rfl⟩ : syracuseStep 3439813 = 644965) (by norm_num)
theorem B4586417 : Blo 2037435 4586417 := bstep (se 2 (by rfl) ⟨1719906, by rfl⟩ : syracuseStep 4586417 = 3439813) B3439813
theorem B3057611 : Blo 2037435 3057611 := bstep (se 1 (by rfl) ⟨2293208, by rfl⟩ : syracuseStep 3057611 = 4586417) B4586417
theorem B2038407 : Blo 2037435 2038407 := bstep (se 1 (by rfl) ⟨1528805, by rfl⟩ : syracuseStep 2038407 = 3057611) B3057611
theorem B2293213 : Blo 2037435 2293213 := bbase (se 3 (by rfl) ⟨429977, by rfl⟩ : syracuseStep 2293213 = 859955) (by norm_num)
theorem B3057617 : Blo 2037435 3057617 := bstep (se 2 (by rfl) ⟨1146606, by rfl⟩ : syracuseStep 3057617 = 2293213) B2293213
theorem B2038411 : Blo 2037435 2038411 := bstep (se 1 (by rfl) ⟨1528808, by rfl⟩ : syracuseStep 2038411 = 3057617) B3057617
theorem B6879653 : Blo 2037435 6879653 := bbase (se 4 (by rfl) ⟨644967, by rfl⟩ : syracuseStep 6879653 = 1289935) (by norm_num)
theorem B4586435 : Blo 2037435 4586435 := bstep (se 1 (by rfl) ⟨3439826, by rfl⟩ : syracuseStep 4586435 = 6879653) B6879653
theorem B3057623 : Blo 2037435 3057623 := bstep (se 1 (by rfl) ⟨2293217, by rfl⟩ : syracuseStep 3057623 = 4586435) B4586435
theorem B2038415 : Blo 2037435 2038415 := bstep (se 1 (by rfl) ⟨1528811, by rfl⟩ : syracuseStep 2038415 = 3057623) B3057623
theorem B3057629 : Blo 2037435 3057629 := bbase (se 3 (by rfl) ⟨573305, by rfl⟩ : syracuseStep 3057629 = 1146611) (by norm_num)
theorem B2038419 : Blo 2037435 2038419 := bstep (se 1 (by rfl) ⟨1528814, by rfl⟩ : syracuseStep 2038419 = 3057629) B3057629
theorem B4586453 : Blo 2037435 4586453 := bbase (se 7 (by rfl) ⟨53747, by rfl⟩ : syracuseStep 4586453 = 107495) (by norm_num)
theorem B3057635 : Blo 2037435 3057635 := bstep (se 1 (by rfl) ⟨2293226, by rfl⟩ : syracuseStep 3057635 = 4586453) B4586453
theorem B2038423 : Blo 2037435 2038423 := bstep (se 1 (by rfl) ⟨1528817, by rfl⟩ : syracuseStep 2038423 = 3057635) B3057635
theorem B7346629 : Blo 2037435 7346629 := bbase (se 4 (by rfl) ⟨688746, by rfl⟩ : syracuseStep 7346629 = 1377493) (by norm_num)
theorem B9795505 : Blo 2037435 9795505 := bstep (se 2 (by rfl) ⟨3673314, by rfl⟩ : syracuseStep 9795505 = 7346629) B7346629
theorem B13060673 : Blo 2037435 13060673 := bstep (se 2 (by rfl) ⟨4897752, by rfl⟩ : syracuseStep 13060673 = 9795505) B9795505
theorem B8707115 : Blo 2037435 8707115 := bstep (se 1 (by rfl) ⟨6530336, by rfl⟩ : syracuseStep 8707115 = 13060673) B13060673
theorem B5804743 : Blo 2037435 5804743 := bstep (se 1 (by rfl) ⟨4353557, by rfl⟩ : syracuseStep 5804743 = 8707115) B8707115
theorem B7739657 : Blo 2037435 7739657 := bstep (se 2 (by rfl) ⟨2902371, by rfl⟩ : syracuseStep 7739657 = 5804743) B5804743
theorem B5159771 : Blo 2037435 5159771 := bstep (se 1 (by rfl) ⟨3869828, by rfl⟩ : syracuseStep 5159771 = 7739657) B7739657
theorem B3439847 : Blo 2037435 3439847 := bstep (se 1 (by rfl) ⟨2579885, by rfl⟩ : syracuseStep 3439847 = 5159771) B5159771
theorem B2293231 : Blo 2037435 2293231 := bstep (se 1 (by rfl) ⟨1719923, by rfl⟩ : syracuseStep 2293231 = 3439847) B3439847
theorem B3057641 : Blo 2037435 3057641 := bstep (se 2 (by rfl) ⟨1146615, by rfl⟩ : syracuseStep 3057641 = 2293231) B2293231
theorem B2038427 : Blo 2037435 2038427 := bstep (se 1 (by rfl) ⟨1528820, by rfl⟩ : syracuseStep 2038427 = 3057641) B3057641
theorem B17414261 : Blo 2037435 17414261 := bbase (se 5 (by rfl) ⟨816293, by rfl⟩ : syracuseStep 17414261 = 1632587) (by norm_num)
theorem B11609507 : Blo 2037435 11609507 := bstep (se 1 (by rfl) ⟨8707130, by rfl⟩ : syracuseStep 11609507 = 17414261) B17414261
theorem B7739671 : Blo 2037435 7739671 := bstep (se 1 (by rfl) ⟨5804753, by rfl⟩ : syracuseStep 7739671 = 11609507) B11609507
theorem B10319561 : Blo 2037435 10319561 := bstep (se 2 (by rfl) ⟨3869835, by rfl⟩ : syracuseStep 10319561 = 7739671) B7739671
theorem B6879707 : Blo 2037435 6879707 := bstep (se 1 (by rfl) ⟨5159780, by rfl⟩ : syracuseStep 6879707 = 10319561) B10319561
theorem B4586471 : Blo 2037435 4586471 := bstep (se 1 (by rfl) ⟨3439853, by rfl⟩ : syracuseStep 4586471 = 6879707) B6879707
theorem B3057647 : Blo 2037435 3057647 := bstep (se 1 (by rfl) ⟨2293235, by rfl⟩ : syracuseStep 3057647 = 4586471) B4586471
theorem B2038431 : Blo 2037435 2038431 := bstep (se 1 (by rfl) ⟨1528823, by rfl⟩ : syracuseStep 2038431 = 3057647) B3057647
theorem B3057653 : Blo 2037435 3057653 := bbase (se 5 (by rfl) ⟨143327, by rfl⟩ : syracuseStep 3057653 = 286655) (by norm_num)
theorem B2038435 : Blo 2037435 2038435 := bstep (se 1 (by rfl) ⟨1528826, by rfl⟩ : syracuseStep 2038435 = 3057653) B3057653
theorem B7165189 : Blo 2037435 7165189 := bbase (se 4 (by rfl) ⟨671736, by rfl⟩ : syracuseStep 7165189 = 1343473) (by norm_num)
theorem B38214341 : Blo 2037435 38214341 := bstep (se 4 (by rfl) ⟨3582594, by rfl⟩ : syracuseStep 38214341 = 7165189) B7165189
theorem B25476227 : Blo 2037435 25476227 := bstep (se 1 (by rfl) ⟨19107170, by rfl⟩ : syracuseStep 25476227 = 38214341) B38214341
theorem B16984151 : Blo 2037435 16984151 := bstep (se 1 (by rfl) ⟨12738113, by rfl⟩ : syracuseStep 16984151 = 25476227) B25476227
theorem B11322767 : Blo 2037435 11322767 := bstep (se 1 (by rfl) ⟨8492075, by rfl⟩ : syracuseStep 11322767 = 16984151) B16984151
theorem B7548511 : Blo 2037435 7548511 := bstep (se 1 (by rfl) ⟨5661383, by rfl⟩ : syracuseStep 7548511 = 11322767) B11322767
theorem B10064681 : Blo 2037435 10064681 := bstep (se 2 (by rfl) ⟨3774255, by rfl⟩ : syracuseStep 10064681 = 7548511) B7548511
theorem B6709787 : Blo 2037435 6709787 := bstep (se 1 (by rfl) ⟨5032340, by rfl⟩ : syracuseStep 6709787 = 10064681) B10064681
theorem B4473191 : Blo 2037435 4473191 := bstep (se 1 (by rfl) ⟨3354893, by rfl⟩ : syracuseStep 4473191 = 6709787) B6709787
theorem B11928509 : Blo 2037435 11928509 := bstep (se 3 (by rfl) ⟨2236595, by rfl⟩ : syracuseStep 11928509 = 4473191) B4473191
theorem B7952339 : Blo 2037435 7952339 := bstep (se 1 (by rfl) ⟨5964254, by rfl⟩ : syracuseStep 7952339 = 11928509) B11928509
theorem B5301559 : Blo 2037435 5301559 := bstep (se 1 (by rfl) ⟨3976169, by rfl⟩ : syracuseStep 5301559 = 7952339) B7952339
theorem B7068745 : Blo 2037435 7068745 := bstep (se 2 (by rfl) ⟨2650779, by rfl⟩ : syracuseStep 7068745 = 5301559) B5301559
theorem B9424993 : Blo 2037435 9424993 := bstep (se 2 (by rfl) ⟨3534372, by rfl⟩ : syracuseStep 9424993 = 7068745) B7068745
theorem B12566657 : Blo 2037435 12566657 := bstep (se 2 (by rfl) ⟨4712496, by rfl⟩ : syracuseStep 12566657 = 9424993) B9424993
theorem B8377771 : Blo 2037435 8377771 := bstep (se 1 (by rfl) ⟨6283328, by rfl⟩ : syracuseStep 8377771 = 12566657) B12566657
theorem B11170361 : Blo 2037435 11170361 := bstep (se 2 (by rfl) ⟨4188885, by rfl⟩ : syracuseStep 11170361 = 8377771) B8377771
theorem B7446907 : Blo 2037435 7446907 := bstep (se 1 (by rfl) ⟨5585180, by rfl⟩ : syracuseStep 7446907 = 11170361) B11170361
theorem B39716837 : Blo 2037435 39716837 := bstep (se 4 (by rfl) ⟨3723453, by rfl⟩ : syracuseStep 39716837 = 7446907) B7446907
theorem B26477891 : Blo 2037435 26477891 := bstep (se 1 (by rfl) ⟨19858418, by rfl⟩ : syracuseStep 26477891 = 39716837) B39716837
theorem B17651927 : Blo 2037435 17651927 := bstep (se 1 (by rfl) ⟨13238945, by rfl⟩ : syracuseStep 17651927 = 26477891) B26477891
theorem B11767951 : Blo 2037435 11767951 := bstep (se 1 (by rfl) ⟨8825963, by rfl⟩ : syracuseStep 11767951 = 17651927) B17651927
theorem B15690601 : Blo 2037435 15690601 := bstep (se 2 (by rfl) ⟨5883975, by rfl⟩ : syracuseStep 15690601 = 11767951) B11767951
theorem B20920801 : Blo 2037435 20920801 := bstep (se 2 (by rfl) ⟨7845300, by rfl⟩ : syracuseStep 20920801 = 15690601) B15690601
theorem B27894401 : Blo 2037435 27894401 := bstep (se 2 (by rfl) ⟨10460400, by rfl⟩ : syracuseStep 27894401 = 20920801) B20920801
theorem B18596267 : Blo 2037435 18596267 := bstep (se 1 (by rfl) ⟨13947200, by rfl⟩ : syracuseStep 18596267 = 27894401) B27894401
theorem B12397511 : Blo 2037435 12397511 := bstep (se 1 (by rfl) ⟨9298133, by rfl⟩ : syracuseStep 12397511 = 18596267) B18596267
theorem B8265007 : Blo 2037435 8265007 := bstep (se 1 (by rfl) ⟨6198755, by rfl⟩ : syracuseStep 8265007 = 12397511) B12397511
theorem B11020009 : Blo 2037435 11020009 := bstep (se 2 (by rfl) ⟨4132503, by rfl⟩ : syracuseStep 11020009 = 8265007) B8265007
theorem B14693345 : Blo 2037435 14693345 := bstep (se 2 (by rfl) ⟨5510004, by rfl⟩ : syracuseStep 14693345 = 11020009) B11020009
theorem B9795563 : Blo 2037435 9795563 := bstep (se 1 (by rfl) ⟨7346672, by rfl⟩ : syracuseStep 9795563 = 14693345) B14693345
theorem B6530375 : Blo 2037435 6530375 := bstep (se 1 (by rfl) ⟨4897781, by rfl⟩ : syracuseStep 6530375 = 9795563) B9795563
theorem B4353583 : Blo 2037435 4353583 := bstep (se 1 (by rfl) ⟨3265187, by rfl⟩ : syracuseStep 4353583 = 6530375) B6530375
theorem B5804777 : Blo 2037435 5804777 := bstep (se 2 (by rfl) ⟨2176791, by rfl⟩ : syracuseStep 5804777 = 4353583) B4353583
theorem B3869851 : Blo 2037435 3869851 := bstep (se 1 (by rfl) ⟨2902388, by rfl⟩ : syracuseStep 3869851 = 5804777) B5804777
theorem B5159801 : Blo 2037435 5159801 := bstep (se 2 (by rfl) ⟨1934925, by rfl⟩ : syracuseStep 5159801 = 3869851) B3869851
theorem B3439867 : Blo 2037435 3439867 := bstep (se 1 (by rfl) ⟨2579900, by rfl⟩ : syracuseStep 3439867 = 5159801) B5159801
theorem B4586489 : Blo 2037435 4586489 := bstep (se 2 (by rfl) ⟨1719933, by rfl⟩ : syracuseStep 4586489 = 3439867) B3439867
theorem B3057659 : Blo 2037435 3057659 := bstep (se 1 (by rfl) ⟨2293244, by rfl⟩ : syracuseStep 3057659 = 4586489) B4586489
theorem B2038439 : Blo 2037435 2038439 := bstep (se 1 (by rfl) ⟨1528829, by rfl⟩ : syracuseStep 2038439 = 3057659) B3057659
theorem B2293249 : Blo 2037435 2293249 := bbase (se 2 (by rfl) ⟨859968, by rfl⟩ : syracuseStep 2293249 = 1719937) (by norm_num)
theorem B3057665 : Blo 2037435 3057665 := bstep (se 2 (by rfl) ⟨1146624, by rfl⟩ : syracuseStep 3057665 = 2293249) B2293249
theorem B2038443 : Blo 2037435 2038443 := bstep (se 1 (by rfl) ⟨1528832, by rfl⟩ : syracuseStep 2038443 = 3057665) B3057665
theorem B5159821 : Blo 2037435 5159821 := bbase (se 3 (by rfl) ⟨967466, by rfl⟩ : syracuseStep 5159821 = 1934933) (by norm_num)
theorem B6879761 : Blo 2037435 6879761 := bstep (se 2 (by rfl) ⟨2579910, by rfl⟩ : syracuseStep 6879761 = 5159821) B5159821
theorem B4586507 : Blo 2037435 4586507 := bstep (se 1 (by rfl) ⟨3439880, by rfl⟩ : syracuseStep 4586507 = 6879761) B6879761
theorem B3057671 : Blo 2037435 3057671 := bstep (se 1 (by rfl) ⟨2293253, by rfl⟩ : syracuseStep 3057671 = 4586507) B4586507
theorem B2038447 : Blo 2037435 2038447 := bstep (se 1 (by rfl) ⟨1528835, by rfl⟩ : syracuseStep 2038447 = 3057671) B3057671
theorem B3057677 : Blo 2037435 3057677 := bbase (se 3 (by rfl) ⟨573314, by rfl⟩ : syracuseStep 3057677 = 1146629) (by norm_num)
theorem B2038451 : Blo 2037435 2038451 := bstep (se 1 (by rfl) ⟨1528838, by rfl⟩ : syracuseStep 2038451 = 3057677) B3057677
theorem B4586525 : Blo 2037435 4586525 := bbase (se 3 (by rfl) ⟨859973, by rfl⟩ : syracuseStep 4586525 = 1719947) (by norm_num)
theorem B3057683 : Blo 2037435 3057683 := bstep (se 1 (by rfl) ⟨2293262, by rfl⟩ : syracuseStep 3057683 = 4586525) B4586525
theorem B2038455 : Blo 2037435 2038455 := bstep (se 1 (by rfl) ⟨1528841, by rfl⟩ : syracuseStep 2038455 = 3057683) B3057683
theorem B3439901 : Blo 2037435 3439901 := bbase (se 3 (by rfl) ⟨644981, by rfl⟩ : syracuseStep 3439901 = 1289963) (by norm_num)
theorem B2293267 : Blo 2037435 2293267 := bstep (se 1 (by rfl) ⟨1719950, by rfl⟩ : syracuseStep 2293267 = 3439901) B3439901
theorem B3057689 : Blo 2037435 3057689 := bstep (se 2 (by rfl) ⟨1146633, by rfl⟩ : syracuseStep 3057689 = 2293267) B2293267
theorem B2038459 : Blo 2037435 2038459 := bstep (se 1 (by rfl) ⟨1528844, by rfl⟩ : syracuseStep 2038459 = 3057689) B3057689
theorem B5510069 : Blo 2037435 5510069 := bbase (se 5 (by rfl) ⟨258284, by rfl⟩ : syracuseStep 5510069 = 516569) (by norm_num)
theorem B3673379 : Blo 2037435 3673379 := bstep (se 1 (by rfl) ⟨2755034, by rfl⟩ : syracuseStep 3673379 = 5510069) B5510069
theorem B2448919 : Blo 2037435 2448919 := bstep (se 1 (by rfl) ⟨1836689, by rfl⟩ : syracuseStep 2448919 = 3673379) B3673379
theorem B13060901 : Blo 2037435 13060901 := bstep (se 4 (by rfl) ⟨1224459, by rfl⟩ : syracuseStep 13060901 = 2448919) B2448919
theorem B8707267 : Blo 2037435 8707267 := bstep (se 1 (by rfl) ⟨6530450, by rfl⟩ : syracuseStep 8707267 = 13060901) B13060901
theorem B11609689 : Blo 2037435 11609689 := bstep (se 2 (by rfl) ⟨4353633, by rfl⟩ : syracuseStep 11609689 = 8707267) B8707267
theorem B15479585 : Blo 2037435 15479585 := bstep (se 2 (by rfl) ⟨5804844, by rfl⟩ : syracuseStep 15479585 = 11609689) B11609689
theorem B10319723 : Blo 2037435 10319723 := bstep (se 1 (by rfl) ⟨7739792, by rfl⟩ : syracuseStep 10319723 = 15479585) B15479585
theorem B6879815 : Blo 2037435 6879815 := bstep (se 1 (by rfl) ⟨5159861, by rfl⟩ : syracuseStep 6879815 = 10319723) B10319723
theorem B4586543 : Blo 2037435 4586543 := bstep (se 1 (by rfl) ⟨3439907, by rfl⟩ : syracuseStep 4586543 = 6879815) B6879815
theorem B3057695 : Blo 2037435 3057695 := bstep (se 1 (by rfl) ⟨2293271, by rfl⟩ : syracuseStep 3057695 = 4586543) B4586543
theorem B2038463 : Blo 2037435 2038463 := bstep (se 1 (by rfl) ⟨1528847, by rfl⟩ : syracuseStep 2038463 = 3057695) B3057695
theorem B3057701 : Blo 2037435 3057701 := bbase (se 4 (by rfl) ⟨286659, by rfl⟩ : syracuseStep 3057701 = 573319) (by norm_num)
theorem B2038467 : Blo 2037435 2038467 := bstep (se 1 (by rfl) ⟨1528850, by rfl⟩ : syracuseStep 2038467 = 3057701) B3057701
theorem B2579941 : Blo 2037435 2579941 := bbase (se 4 (by rfl) ⟨241869, by rfl⟩ : syracuseStep 2579941 = 483739) (by norm_num)
theorem B3439921 : Blo 2037435 3439921 := bstep (se 2 (by rfl) ⟨1289970, by rfl⟩ : syracuseStep 3439921 = 2579941) B2579941
theorem B4586561 : Blo 2037435 4586561 := bstep (se 2 (by rfl) ⟨1719960, by rfl⟩ : syracuseStep 4586561 = 3439921) B3439921
theorem B3057707 : Blo 2037435 3057707 := bstep (se 1 (by rfl) ⟨2293280, by rfl⟩ : syracuseStep 3057707 = 4586561) B4586561
theorem B2038471 : Blo 2037435 2038471 := bstep (se 1 (by rfl) ⟨1528853, by rfl⟩ : syracuseStep 2038471 = 3057707) B3057707
theorem B2293285 : Blo 2037435 2293285 := bbase (se 4 (by rfl) ⟨214995, by rfl⟩ : syracuseStep 2293285 = 429991) (by norm_num)
theorem B3057713 : Blo 2037435 3057713 := bstep (se 2 (by rfl) ⟨1146642, by rfl⟩ : syracuseStep 3057713 = 2293285) B2293285
theorem B2038475 : Blo 2037435 2038475 := bstep (se 1 (by rfl) ⟨1528856, by rfl⟩ : syracuseStep 2038475 = 3057713) B3057713
theorem B3486869 : Blo 2037435 3486869 := bbase (se 6 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 3486869 = 163447) (by norm_num)
theorem B2324579 : Blo 2037435 2324579 := bstep (se 1 (by rfl) ⟨1743434, by rfl⟩ : syracuseStep 2324579 = 3486869) B3486869
theorem B6198877 : Blo 2037435 6198877 := bstep (se 3 (by rfl) ⟨1162289, by rfl⟩ : syracuseStep 6198877 = 2324579) B2324579
theorem B8265169 : Blo 2037435 8265169 := bstep (se 2 (by rfl) ⟨3099438, by rfl⟩ : syracuseStep 8265169 = 6198877) B6198877
theorem B11020225 : Blo 2037435 11020225 := bstep (se 2 (by rfl) ⟨4132584, by rfl⟩ : syracuseStep 11020225 = 8265169) B8265169
theorem B14693633 : Blo 2037435 14693633 := bstep (se 2 (by rfl) ⟨5510112, by rfl⟩ : syracuseStep 14693633 = 11020225) B11020225
theorem B9795755 : Blo 2037435 9795755 := bstep (se 1 (by rfl) ⟨7346816, by rfl⟩ : syracuseStep 9795755 = 14693633) B14693633
theorem B6530503 : Blo 2037435 6530503 := bstep (se 1 (by rfl) ⟨4897877, by rfl⟩ : syracuseStep 6530503 = 9795755) B9795755
theorem B8707337 : Blo 2037435 8707337 := bstep (se 2 (by rfl) ⟨3265251, by rfl⟩ : syracuseStep 8707337 = 6530503) B6530503
theorem B5804891 : Blo 2037435 5804891 := bstep (se 1 (by rfl) ⟨4353668, by rfl⟩ : syracuseStep 5804891 = 8707337) B8707337
theorem B3869927 : Blo 2037435 3869927 := bstep (se 1 (by rfl) ⟨2902445, by rfl⟩ : syracuseStep 3869927 = 5804891) B5804891
theorem B2579951 : Blo 2037435 2579951 := bstep (se 1 (by rfl) ⟨1934963, by rfl⟩ : syracuseStep 2579951 = 3869927) B3869927
theorem B6879869 : Blo 2037435 6879869 := bstep (se 3 (by rfl) ⟨1289975, by rfl⟩ : syracuseStep 6879869 = 2579951) B2579951
theorem B4586579 : Blo 2037435 4586579 := bstep (se 1 (by rfl) ⟨3439934, by rfl⟩ : syracuseStep 4586579 = 6879869) B6879869
theorem B3057719 : Blo 2037435 3057719 := bstep (se 1 (by rfl) ⟨2293289, by rfl⟩ : syracuseStep 3057719 = 4586579) B4586579
theorem B2038479 : Blo 2037435 2038479 := bstep (se 1 (by rfl) ⟨1528859, by rfl⟩ : syracuseStep 2038479 = 3057719) B3057719
theorem B3057725 : Blo 2037435 3057725 := bbase (se 3 (by rfl) ⟨573323, by rfl⟩ : syracuseStep 3057725 = 1146647) (by norm_num)
theorem B2038483 : Blo 2037435 2038483 := bstep (se 1 (by rfl) ⟨1528862, by rfl⟩ : syracuseStep 2038483 = 3057725) B3057725
theorem B4586597 : Blo 2037435 4586597 := bbase (se 4 (by rfl) ⟨429993, by rfl⟩ : syracuseStep 4586597 = 859987) (by norm_num)
theorem B3057731 : Blo 2037435 3057731 := bstep (se 1 (by rfl) ⟨2293298, by rfl⟩ : syracuseStep 3057731 = 4586597) B4586597
theorem B2038487 : Blo 2037435 2038487 := bstep (se 1 (by rfl) ⟨1528865, by rfl⟩ : syracuseStep 2038487 = 3057731) B3057731
theorem B5159933 : Blo 2037435 5159933 := bbase (se 3 (by rfl) ⟨967487, by rfl⟩ : syracuseStep 5159933 = 1934975) (by norm_num)
theorem B3439955 : Blo 2037435 3439955 := bstep (se 1 (by rfl) ⟨2579966, by rfl⟩ : syracuseStep 3439955 = 5159933) B5159933
theorem B2293303 : Blo 2037435 2293303 := bstep (se 1 (by rfl) ⟨1719977, by rfl⟩ : syracuseStep 2293303 = 3439955) B3439955
theorem B3057737 : Blo 2037435 3057737 := bstep (se 2 (by rfl) ⟨1146651, by rfl⟩ : syracuseStep 3057737 = 2293303) B2293303
theorem B2038491 : Blo 2037435 2038491 := bstep (se 1 (by rfl) ⟨1528868, by rfl⟩ : syracuseStep 2038491 = 3057737) B3057737
theorem B3869957 : Blo 2037435 3869957 := bbase (se 4 (by rfl) ⟨362808, by rfl⟩ : syracuseStep 3869957 = 725617) (by norm_num)
theorem B10319885 : Blo 2037435 10319885 := bstep (se 3 (by rfl) ⟨1934978, by rfl⟩ : syracuseStep 10319885 = 3869957) B3869957
theorem B6879923 : Blo 2037435 6879923 := bstep (se 1 (by rfl) ⟨5159942, by rfl⟩ : syracuseStep 6879923 = 10319885) B10319885
theorem B4586615 : Blo 2037435 4586615 := bstep (se 1 (by rfl) ⟨3439961, by rfl⟩ : syracuseStep 4586615 = 6879923) B6879923
theorem B3057743 : Blo 2037435 3057743 := bstep (se 1 (by rfl) ⟨2293307, by rfl⟩ : syracuseStep 3057743 = 4586615) B4586615
theorem B2038495 : Blo 2037435 2038495 := bstep (se 1 (by rfl) ⟨1528871, by rfl⟩ : syracuseStep 2038495 = 3057743) B3057743
theorem B3057749 : Blo 2037435 3057749 := bbase (se 8 (by rfl) ⟨17916, by rfl⟩ : syracuseStep 3057749 = 35833) (by norm_num)
theorem B2038499 : Blo 2037435 2038499 := bstep (se 1 (by rfl) ⟨1528874, by rfl⟩ : syracuseStep 2038499 = 3057749) B3057749
theorem B6198949 : Blo 2037435 6198949 := bbase (se 4 (by rfl) ⟨581151, by rfl⟩ : syracuseStep 6198949 = 1162303) (by norm_num)
theorem B33061061 : Blo 2037435 33061061 := bstep (se 4 (by rfl) ⟨3099474, by rfl⟩ : syracuseStep 33061061 = 6198949) B6198949
theorem B22040707 : Blo 2037435 22040707 := bstep (se 1 (by rfl) ⟨16530530, by rfl⟩ : syracuseStep 22040707 = 33061061) B33061061
theorem B29387609 : Blo 2037435 29387609 := bstep (se 2 (by rfl) ⟨11020353, by rfl⟩ : syracuseStep 29387609 = 22040707) B22040707
theorem B19591739 : Blo 2037435 19591739 := bstep (se 1 (by rfl) ⟨14693804, by rfl⟩ : syracuseStep 19591739 = 29387609) B29387609
theorem B13061159 : Blo 2037435 13061159 := bstep (se 1 (by rfl) ⟨9795869, by rfl⟩ : syracuseStep 13061159 = 19591739) B19591739
theorem B8707439 : Blo 2037435 8707439 := bstep (se 1 (by rfl) ⟨6530579, by rfl⟩ : syracuseStep 8707439 = 13061159) B13061159
theorem B5804959 : Blo 2037435 5804959 := bstep (se 1 (by rfl) ⟨4353719, by rfl⟩ : syracuseStep 5804959 = 8707439) B8707439
theorem B7739945 : Blo 2037435 7739945 := bstep (se 2 (by rfl) ⟨2902479, by rfl⟩ : syracuseStep 7739945 = 5804959) B5804959
theorem B5159963 : Blo 2037435 5159963 := bstep (se 1 (by rfl) ⟨3869972, by rfl⟩ : syracuseStep 5159963 = 7739945) B7739945
theorem B3439975 : Blo 2037435 3439975 := bstep (se 1 (by rfl) ⟨2579981, by rfl⟩ : syracuseStep 3439975 = 5159963) B5159963
theorem B4586633 : Blo 2037435 4586633 := bstep (se 2 (by rfl) ⟨1719987, by rfl⟩ : syracuseStep 4586633 = 3439975) B3439975
theorem B3057755 : Blo 2037435 3057755 := bstep (se 1 (by rfl) ⟨2293316, by rfl⟩ : syracuseStep 3057755 = 4586633) B4586633
theorem B2038503 : Blo 2037435 2038503 := bstep (se 1 (by rfl) ⟨1528877, by rfl⟩ : syracuseStep 2038503 = 3057755) B3057755
theorem B2293321 : Blo 2037435 2293321 := bbase (se 2 (by rfl) ⟨859995, by rfl⟩ : syracuseStep 2293321 = 1719991) (by norm_num)
theorem B3057761 : Blo 2037435 3057761 := bstep (se 2 (by rfl) ⟨1146660, by rfl⟩ : syracuseStep 3057761 = 2293321) B2293321
theorem B2038507 : Blo 2037435 2038507 := bstep (se 1 (by rfl) ⟨1528880, by rfl⟩ : syracuseStep 2038507 = 3057761) B3057761
theorem B15691157 : Blo 2037435 15691157 := bbase (se 6 (by rfl) ⟨367761, by rfl⟩ : syracuseStep 15691157 = 735523) (by norm_num)
theorem B10460771 : Blo 2037435 10460771 := bstep (se 1 (by rfl) ⟨7845578, by rfl⟩ : syracuseStep 10460771 = 15691157) B15691157
theorem B6973847 : Blo 2037435 6973847 := bstep (se 1 (by rfl) ⟨5230385, by rfl⟩ : syracuseStep 6973847 = 10460771) B10460771
theorem B4649231 : Blo 2037435 4649231 := bstep (se 1 (by rfl) ⟨3486923, by rfl⟩ : syracuseStep 4649231 = 6973847) B6973847
theorem B3099487 : Blo 2037435 3099487 := bstep (se 1 (by rfl) ⟨2324615, by rfl⟩ : syracuseStep 3099487 = 4649231) B4649231
theorem B4132649 : Blo 2037435 4132649 := bstep (se 2 (by rfl) ⟨1549743, by rfl⟩ : syracuseStep 4132649 = 3099487) B3099487
theorem B2755099 : Blo 2037435 2755099 := bstep (se 1 (by rfl) ⟨2066324, by rfl⟩ : syracuseStep 2755099 = 4132649) B4132649
theorem B14693861 : Blo 2037435 14693861 := bstep (se 4 (by rfl) ⟨1377549, by rfl⟩ : syracuseStep 14693861 = 2755099) B2755099
theorem B9795907 : Blo 2037435 9795907 := bstep (se 1 (by rfl) ⟨7346930, by rfl⟩ : syracuseStep 9795907 = 14693861) B14693861
theorem B13061209 : Blo 2037435 13061209 := bstep (se 2 (by rfl) ⟨4897953, by rfl⟩ : syracuseStep 13061209 = 9795907) B9795907
theorem B17414945 : Blo 2037435 17414945 := bstep (se 2 (by rfl) ⟨6530604, by rfl⟩ : syracuseStep 17414945 = 13061209) B13061209
theorem B11609963 : Blo 2037435 11609963 := bstep (se 1 (by rfl) ⟨8707472, by rfl⟩ : syracuseStep 11609963 = 17414945) B17414945
theorem B7739975 : Blo 2037435 7739975 := bstep (se 1 (by rfl) ⟨5804981, by rfl⟩ : syracuseStep 7739975 = 11609963) B11609963
theorem B5159983 : Blo 2037435 5159983 := bstep (se 1 (by rfl) ⟨3869987, by rfl⟩ : syracuseStep 5159983 = 7739975) B7739975
theorem B6879977 : Blo 2037435 6879977 := bstep (se 2 (by rfl) ⟨2579991, by rfl⟩ : syracuseStep 6879977 = 5159983) B5159983
theorem B4586651 : Blo 2037435 4586651 := bstep (se 1 (by rfl) ⟨3439988, by rfl⟩ : syracuseStep 4586651 = 6879977) B6879977
theorem B3057767 : Blo 2037435 3057767 := bstep (se 1 (by rfl) ⟨2293325, by rfl⟩ : syracuseStep 3057767 = 4586651) B4586651
theorem B2038511 : Blo 2037435 2038511 := bstep (se 1 (by rfl) ⟨1528883, by rfl⟩ : syracuseStep 2038511 = 3057767) B3057767
theorem B3057773 : Blo 2037435 3057773 := bbase (se 3 (by rfl) ⟨573332, by rfl⟩ : syracuseStep 3057773 = 1146665) (by norm_num)
theorem B2038515 : Blo 2037435 2038515 := bstep (se 1 (by rfl) ⟨1528886, by rfl⟩ : syracuseStep 2038515 = 3057773) B3057773
theorem B4586669 : Blo 2037435 4586669 := bbase (se 3 (by rfl) ⟨860000, by rfl⟩ : syracuseStep 4586669 = 1720001) (by norm_num)
theorem B3057779 : Blo 2037435 3057779 := bstep (se 1 (by rfl) ⟨2293334, by rfl⟩ : syracuseStep 3057779 = 4586669) B4586669
theorem B2038519 : Blo 2037435 2038519 := bstep (se 1 (by rfl) ⟨1528889, by rfl⟩ : syracuseStep 2038519 = 3057779) B3057779
theorem B6530645 : Blo 2037435 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B4353763 : Blo 2037435 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B5805017 : Blo 2037435 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B3870011 : Blo 2037435 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B2580007 : Blo 2037435 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B3440009 : Blo 2037435 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B2293339 : Blo 2037435 2293339 := bstep (se 1 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 2293339 = 3440009) B3440009
theorem B3057785 : Blo 2037435 3057785 := bstep (se 2 (by rfl) ⟨1146669, by rfl⟩ : syracuseStep 3057785 = 2293339) B2293339
theorem B2038523 : Blo 2037435 2038523 := bstep (se 1 (by rfl) ⟨1528892, by rfl⟩ : syracuseStep 2038523 = 3057785) B3057785
theorem B2324633 : Blo 2037435 2324633 := bbase (se 2 (by rfl) ⟨871737, by rfl⟩ : syracuseStep 2324633 = 1743475) (by norm_num)
theorem B6199021 : Blo 2037435 6199021 := bstep (se 3 (by rfl) ⟨1162316, by rfl⟩ : syracuseStep 6199021 = 2324633) B2324633
theorem B33061445 : Blo 2037435 33061445 := bstep (se 4 (by rfl) ⟨3099510, by rfl⟩ : syracuseStep 33061445 = 6199021) B6199021
theorem B22040963 : Blo 2037435 22040963 := bstep (se 1 (by rfl) ⟨16530722, by rfl⟩ : syracuseStep 22040963 = 33061445) B33061445
theorem B14693975 : Blo 2037435 14693975 := bstep (se 1 (by rfl) ⟨11020481, by rfl⟩ : syracuseStep 14693975 = 22040963) B22040963
theorem B9795983 : Blo 2037435 9795983 := bstep (se 1 (by rfl) ⟨7346987, by rfl⟩ : syracuseStep 9795983 = 14693975) B14693975
theorem B26122621 : Blo 2037435 26122621 := bstep (se 3 (by rfl) ⟨4897991, by rfl⟩ : syracuseStep 26122621 = 9795983) B9795983
theorem B34830161 : Blo 2037435 34830161 := bstep (se 2 (by rfl) ⟨13061310, by rfl⟩ : syracuseStep 34830161 = 26122621) B26122621
theorem B23220107 : Blo 2037435 23220107 := bstep (se 1 (by rfl) ⟨17415080, by rfl⟩ : syracuseStep 23220107 = 34830161) B34830161
theorem B15480071 : Blo 2037435 15480071 := bstep (se 1 (by rfl) ⟨11610053, by rfl⟩ : syracuseStep 15480071 = 23220107) B23220107
theorem B10320047 : Blo 2037435 10320047 := bstep (se 1 (by rfl) ⟨7740035, by rfl⟩ : syracuseStep 10320047 = 15480071) B15480071
theorem B6880031 : Blo 2037435 6880031 := bstep (se 1 (by rfl) ⟨5160023, by rfl⟩ : syracuseStep 6880031 = 10320047) B10320047
theorem B4586687 : Blo 2037435 4586687 := bstep (se 1 (by rfl) ⟨3440015, by rfl⟩ : syracuseStep 4586687 = 6880031) B6880031
theorem B3057791 : Blo 2037435 3057791 := bstep (se 1 (by rfl) ⟨2293343, by rfl⟩ : syracuseStep 3057791 = 4586687) B4586687
theorem B2038527 : Blo 2037435 2038527 := bstep (se 1 (by rfl) ⟨1528895, by rfl⟩ : syracuseStep 2038527 = 3057791) B3057791
theorem B3057797 : Blo 2037435 3057797 := bbase (se 4 (by rfl) ⟨286668, by rfl⟩ : syracuseStep 3057797 = 573337) (by norm_num)
theorem B2038531 : Blo 2037435 2038531 := bstep (se 1 (by rfl) ⟨1528898, by rfl⟩ : syracuseStep 2038531 = 3057797) B3057797
theorem B3440029 : Blo 2037435 3440029 := bbase (se 3 (by rfl) ⟨645005, by rfl⟩ : syracuseStep 3440029 = 1290011) (by norm_num)
theorem B4586705 : Blo 2037435 4586705 := bstep (se 2 (by rfl) ⟨1720014, by rfl⟩ : syracuseStep 4586705 = 3440029) B3440029
theorem B3057803 : Blo 2037435 3057803 := bstep (se 1 (by rfl) ⟨2293352, by rfl⟩ : syracuseStep 3057803 = 4586705) B4586705
theorem B2038535 : Blo 2037435 2038535 := bstep (se 1 (by rfl) ⟨1528901, by rfl⟩ : syracuseStep 2038535 = 3057803) B3057803
theorem B2293357 : Blo 2037435 2293357 := bbase (se 3 (by rfl) ⟨430004, by rfl⟩ : syracuseStep 2293357 = 860009) (by norm_num)
theorem B3057809 : Blo 2037435 3057809 := bstep (se 2 (by rfl) ⟨1146678, by rfl⟩ : syracuseStep 3057809 = 2293357) B2293357
theorem B2038539 : Blo 2037435 2038539 := bstep (se 1 (by rfl) ⟨1528904, by rfl⟩ : syracuseStep 2038539 = 3057809) B3057809
theorem B6880085 : Blo 2037435 6880085 := bbase (se 9 (by rfl) ⟨20156, by rfl⟩ : syracuseStep 6880085 = 40313) (by norm_num)
theorem B4586723 : Blo 2037435 4586723 := bstep (se 1 (by rfl) ⟨3440042, by rfl⟩ : syracuseStep 4586723 = 6880085) B6880085
theorem B3057815 : Blo 2037435 3057815 := bstep (se 1 (by rfl) ⟨2293361, by rfl⟩ : syracuseStep 3057815 = 4586723) B4586723
theorem B2038543 : Blo 2037435 2038543 := bstep (se 1 (by rfl) ⟨1528907, by rfl⟩ : syracuseStep 2038543 = 3057815) B3057815
theorem B3057821 : Blo 2037435 3057821 := bbase (se 3 (by rfl) ⟨573341, by rfl⟩ : syracuseStep 3057821 = 1146683) (by norm_num)
theorem B2038547 : Blo 2037435 2038547 := bstep (se 1 (by rfl) ⟨1528910, by rfl⟩ : syracuseStep 2038547 = 3057821) B3057821
theorem B4586741 : Blo 2037435 4586741 := bbase (se 5 (by rfl) ⟨215003, by rfl⟩ : syracuseStep 4586741 = 430007) (by norm_num)
theorem B3057827 : Blo 2037435 3057827 := bstep (se 1 (by rfl) ⟨2293370, by rfl⟩ : syracuseStep 3057827 = 4586741) B4586741
theorem B2038551 : Blo 2037435 2038551 := bstep (se 1 (by rfl) ⟨1528913, by rfl⟩ : syracuseStep 2038551 = 3057827) B3057827
theorem B5884309 : Blo 2037435 5884309 := bbase (se 6 (by rfl) ⟨137913, by rfl⟩ : syracuseStep 5884309 = 275827) (by norm_num)
theorem B31382981 : Blo 2037435 31382981 := bstep (se 4 (by rfl) ⟨2942154, by rfl⟩ : syracuseStep 31382981 = 5884309) B5884309
theorem B20921987 : Blo 2037435 20921987 := bstep (se 1 (by rfl) ⟨15691490, by rfl⟩ : syracuseStep 20921987 = 31382981) B31382981
theorem B55791965 : Blo 2037435 55791965 := bstep (se 3 (by rfl) ⟨10460993, by rfl⟩ : syracuseStep 55791965 = 20921987) B20921987
theorem B37194643 : Blo 2037435 37194643 := bstep (se 1 (by rfl) ⟨27895982, by rfl⟩ : syracuseStep 37194643 = 55791965) B55791965
theorem B49592857 : Blo 2037435 49592857 := bstep (se 2 (by rfl) ⟨18597321, by rfl⟩ : syracuseStep 49592857 = 37194643) B37194643
theorem B66123809 : Blo 2037435 66123809 := bstep (se 2 (by rfl) ⟨24796428, by rfl⟩ : syracuseStep 66123809 = 49592857) B49592857
theorem B44082539 : Blo 2037435 44082539 := bstep (se 1 (by rfl) ⟨33061904, by rfl⟩ : syracuseStep 44082539 = 66123809) B66123809
theorem B29388359 : Blo 2037435 29388359 := bstep (se 1 (by rfl) ⟨22041269, by rfl⟩ : syracuseStep 29388359 = 44082539) B44082539
theorem B19592239 : Blo 2037435 19592239 := bstep (se 1 (by rfl) ⟨14694179, by rfl⟩ : syracuseStep 19592239 = 29388359) B29388359
theorem B26122985 : Blo 2037435 26122985 := bstep (se 2 (by rfl) ⟨9796119, by rfl⟩ : syracuseStep 26122985 = 19592239) B19592239
theorem B17415323 : Blo 2037435 17415323 := bstep (se 1 (by rfl) ⟨13061492, by rfl⟩ : syracuseStep 17415323 = 26122985) B26122985
theorem B11610215 : Blo 2037435 11610215 := bstep (se 1 (by rfl) ⟨8707661, by rfl⟩ : syracuseStep 11610215 = 17415323) B17415323
theorem B7740143 : Blo 2037435 7740143 := bstep (se 1 (by rfl) ⟨5805107, by rfl⟩ : syracuseStep 7740143 = 11610215) B11610215
theorem B5160095 : Blo 2037435 5160095 := bstep (se 1 (by rfl) ⟨3870071, by rfl⟩ : syracuseStep 5160095 = 7740143) B7740143
theorem B3440063 : Blo 2037435 3440063 := bstep (se 1 (by rfl) ⟨2580047, by rfl⟩ : syracuseStep 3440063 = 5160095) B5160095
theorem B2293375 : Blo 2037435 2293375 := bstep (se 1 (by rfl) ⟨1720031, by rfl⟩ : syracuseStep 2293375 = 3440063) B3440063
theorem B3057833 : Blo 2037435 3057833 := bstep (se 2 (by rfl) ⟨1146687, by rfl⟩ : syracuseStep 3057833 = 2293375) B2293375
theorem B2038555 : Blo 2037435 2038555 := bstep (se 1 (by rfl) ⟨1528916, by rfl⟩ : syracuseStep 2038555 = 3057833) B3057833
theorem B8265493 : Blo 2037435 8265493 := bbase (se 6 (by rfl) ⟨193722, by rfl⟩ : syracuseStep 8265493 = 387445) (by norm_num)
theorem B11020657 : Blo 2037435 11020657 := bstep (se 2 (by rfl) ⟨4132746, by rfl⟩ : syracuseStep 11020657 = 8265493) B8265493
theorem B14694209 : Blo 2037435 14694209 := bstep (se 2 (by rfl) ⟨5510328, by rfl⟩ : syracuseStep 14694209 = 11020657) B11020657
theorem B9796139 : Blo 2037435 9796139 := bstep (se 1 (by rfl) ⟨7347104, by rfl⟩ : syracuseStep 9796139 = 14694209) B14694209
theorem B6530759 : Blo 2037435 6530759 := bstep (se 1 (by rfl) ⟨4898069, by rfl⟩ : syracuseStep 6530759 = 9796139) B9796139
theorem B4353839 : Blo 2037435 4353839 := bstep (se 1 (by rfl) ⟨3265379, by rfl⟩ : syracuseStep 4353839 = 6530759) B6530759
theorem B2902559 : Blo 2037435 2902559 := bstep (se 1 (by rfl) ⟨2176919, by rfl⟩ : syracuseStep 2902559 = 4353839) B4353839
theorem B7740157 : Blo 2037435 7740157 := bstep (se 3 (by rfl) ⟨1451279, by rfl⟩ : syracuseStep 7740157 = 2902559) B2902559
theorem B10320209 : Blo 2037435 10320209 := bstep (se 2 (by rfl) ⟨3870078, by rfl⟩ : syracuseStep 10320209 = 7740157) B7740157
theorem B6880139 : Blo 2037435 6880139 := bstep (se 1 (by rfl) ⟨5160104, by rfl⟩ : syracuseStep 6880139 = 10320209) B10320209
theorem B4586759 : Blo 2037435 4586759 := bstep (se 1 (by rfl) ⟨3440069, by rfl⟩ : syracuseStep 4586759 = 6880139) B6880139
theorem B3057839 : Blo 2037435 3057839 := bstep (se 1 (by rfl) ⟨2293379, by rfl⟩ : syracuseStep 3057839 = 4586759) B4586759
theorem B2038559 : Blo 2037435 2038559 := bstep (se 1 (by rfl) ⟨1528919, by rfl⟩ : syracuseStep 2038559 = 3057839) B3057839
theorem B3057845 : Blo 2037435 3057845 := bbase (se 5 (by rfl) ⟨143336, by rfl⟩ : syracuseStep 3057845 = 286673) (by norm_num)
theorem B2038563 : Blo 2037435 2038563 := bstep (se 1 (by rfl) ⟨1528922, by rfl⟩ : syracuseStep 2038563 = 3057845) B3057845
theorem B5160125 : Blo 2037435 5160125 := bbase (se 3 (by rfl) ⟨967523, by rfl⟩ : syracuseStep 5160125 = 1935047) (by norm_num)
theorem B3440083 : Blo 2037435 3440083 := bstep (se 1 (by rfl) ⟨2580062, by rfl⟩ : syracuseStep 3440083 = 5160125) B5160125
theorem B4586777 : Blo 2037435 4586777 := bstep (se 2 (by rfl) ⟨1720041, by rfl⟩ : syracuseStep 4586777 = 3440083) B3440083
theorem B3057851 : Blo 2037435 3057851 := bstep (se 1 (by rfl) ⟨2293388, by rfl⟩ : syracuseStep 3057851 = 4586777) B4586777
theorem B2038567 : Blo 2037435 2038567 := bstep (se 1 (by rfl) ⟨1528925, by rfl⟩ : syracuseStep 2038567 = 3057851) B3057851
theorem B2293393 : Blo 2037435 2293393 := bbase (se 2 (by rfl) ⟨860022, by rfl⟩ : syracuseStep 2293393 = 1720045) (by norm_num)
theorem B3057857 : Blo 2037435 3057857 := bstep (se 2 (by rfl) ⟨1146696, by rfl⟩ : syracuseStep 3057857 = 2293393) B2293393
theorem B2038571 : Blo 2037435 2038571 := bstep (se 1 (by rfl) ⟨1528928, by rfl⟩ : syracuseStep 2038571 = 3057857) B3057857
theorem B3870109 : Blo 2037435 3870109 := bbase (se 3 (by rfl) ⟨725645, by rfl⟩ : syracuseStep 3870109 = 1451291) (by norm_num)
theorem B5160145 : Blo 2037435 5160145 := bstep (se 2 (by rfl) ⟨1935054, by rfl⟩ : syracuseStep 5160145 = 3870109) B3870109
theorem B6880193 : Blo 2037435 6880193 := bstep (se 2 (by rfl) ⟨2580072, by rfl⟩ : syracuseStep 6880193 = 5160145) B5160145
theorem B4586795 : Blo 2037435 4586795 := bstep (se 1 (by rfl) ⟨3440096, by rfl⟩ : syracuseStep 4586795 = 6880193) B6880193
theorem B3057863 : Blo 2037435 3057863 := bstep (se 1 (by rfl) ⟨2293397, by rfl⟩ : syracuseStep 3057863 = 4586795) B4586795
theorem B2038575 : Blo 2037435 2038575 := bstep (se 1 (by rfl) ⟨1528931, by rfl⟩ : syracuseStep 2038575 = 3057863) B3057863
theorem B3057869 : Blo 2037435 3057869 := bbase (se 3 (by rfl) ⟨573350, by rfl⟩ : syracuseStep 3057869 = 1146701) (by norm_num)
theorem B2038579 : Blo 2037435 2038579 := bstep (se 1 (by rfl) ⟨1528934, by rfl⟩ : syracuseStep 2038579 = 3057869) B3057869
theorem B4586813 : Blo 2037435 4586813 := bbase (se 3 (by rfl) ⟨860027, by rfl⟩ : syracuseStep 4586813 = 1720055) (by norm_num)
theorem B3057875 : Blo 2037435 3057875 := bstep (se 1 (by rfl) ⟨2293406, by rfl⟩ : syracuseStep 3057875 = 4586813) B4586813
theorem B2038583 : Blo 2037435 2038583 := bstep (se 1 (by rfl) ⟨1528937, by rfl⟩ : syracuseStep 2038583 = 3057875) B3057875
theorem B3440117 : Blo 2037435 3440117 := bbase (se 5 (by rfl) ⟨161255, by rfl⟩ : syracuseStep 3440117 = 322511) (by norm_num)
theorem B2293411 : Blo 2037435 2293411 := bstep (se 1 (by rfl) ⟨1720058, by rfl⟩ : syracuseStep 2293411 = 3440117) B3440117
theorem B3057881 : Blo 2037435 3057881 := bstep (se 2 (by rfl) ⟨1146705, by rfl⟩ : syracuseStep 3057881 = 2293411) B2293411
theorem B2038587 : Blo 2037435 2038587 := bstep (se 1 (by rfl) ⟨1528940, by rfl⟩ : syracuseStep 2038587 = 3057881) B3057881
theorem B2449073 : Blo 2037435 2449073 := bbase (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) (by norm_num)
theorem B6530861 : Blo 2037435 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B4353907 : Blo 2037435 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B5805209 : Blo 2037435 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B15480557 : Blo 2037435 15480557 := bstep (se 3 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 15480557 = 5805209) B5805209
theorem B10320371 : Blo 2037435 10320371 := bstep (se 1 (by rfl) ⟨7740278, by rfl⟩ : syracuseStep 10320371 = 15480557) B15480557
theorem B6880247 : Blo 2037435 6880247 := bstep (se 1 (by rfl) ⟨5160185, by rfl⟩ : syracuseStep 6880247 = 10320371) B10320371
theorem B4586831 : Blo 2037435 4586831 := bstep (se 1 (by rfl) ⟨3440123, by rfl⟩ : syracuseStep 4586831 = 6880247) B6880247
theorem B3057887 : Blo 2037435 3057887 := bstep (se 1 (by rfl) ⟨2293415, by rfl⟩ : syracuseStep 3057887 = 4586831) B4586831
theorem B2038591 : Blo 2037435 2038591 := bstep (se 1 (by rfl) ⟨1528943, by rfl⟩ : syracuseStep 2038591 = 3057887) B3057887
theorem B3057893 : Blo 2037435 3057893 := bbase (se 4 (by rfl) ⟨286677, by rfl⟩ : syracuseStep 3057893 = 573355) (by norm_num)
theorem B2038595 : Blo 2037435 2038595 := bstep (se 1 (by rfl) ⟨1528946, by rfl⟩ : syracuseStep 2038595 = 3057893) B3057893
theorem B4353925 : Blo 2037435 4353925 := bbase (se 4 (by rfl) ⟨408180, by rfl⟩ : syracuseStep 4353925 = 816361) (by norm_num)
theorem B5805233 : Blo 2037435 5805233 := bstep (se 2 (by rfl) ⟨2176962, by rfl⟩ : syracuseStep 5805233 = 4353925) B4353925
theorem B3870155 : Blo 2037435 3870155 := bstep (se 1 (by rfl) ⟨2902616, by rfl⟩ : syracuseStep 3870155 = 5805233) B5805233
theorem B2580103 : Blo 2037435 2580103 := bstep (se 1 (by rfl) ⟨1935077, by rfl⟩ : syracuseStep 2580103 = 3870155) B3870155
theorem B3440137 : Blo 2037435 3440137 := bstep (se 2 (by rfl) ⟨1290051, by rfl⟩ : syracuseStep 3440137 = 2580103) B2580103
theorem B4586849 : Blo 2037435 4586849 := bstep (se 2 (by rfl) ⟨1720068, by rfl⟩ : syracuseStep 4586849 = 3440137) B3440137
theorem B3057899 : Blo 2037435 3057899 := bstep (se 1 (by rfl) ⟨2293424, by rfl⟩ : syracuseStep 3057899 = 4586849) B4586849
theorem B2038599 : Blo 2037435 2038599 := bstep (se 1 (by rfl) ⟨1528949, by rfl⟩ : syracuseStep 2038599 = 3057899) B3057899
theorem B2293429 : Blo 2037435 2293429 := bbase (se 5 (by rfl) ⟨107504, by rfl⟩ : syracuseStep 2293429 = 215009) (by norm_num)
theorem B3057905 : Blo 2037435 3057905 := bstep (se 2 (by rfl) ⟨1146714, by rfl⟩ : syracuseStep 3057905 = 2293429) B2293429
theorem B2038603 : Blo 2037435 2038603 := bstep (se 1 (by rfl) ⟨1528952, by rfl⟩ : syracuseStep 2038603 = 3057905) B3057905
theorem B2580113 : Blo 2037435 2580113 := bbase (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) (by norm_num)
theorem B6880301 : Blo 2037435 6880301 := bstep (se 3 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 6880301 = 2580113) B2580113
theorem B4586867 : Blo 2037435 4586867 := bstep (se 1 (by rfl) ⟨3440150, by rfl⟩ : syracuseStep 4586867 = 6880301) B6880301
theorem B3057911 : Blo 2037435 3057911 := bstep (se 1 (by rfl) ⟨2293433, by rfl⟩ : syracuseStep 3057911 = 4586867) B4586867
theorem B2038607 : Blo 2037435 2038607 := bstep (se 1 (by rfl) ⟨1528955, by rfl⟩ : syracuseStep 2038607 = 3057911) B3057911
theorem B3057917 : Blo 2037435 3057917 := bbase (se 3 (by rfl) ⟨573359, by rfl⟩ : syracuseStep 3057917 = 1146719) (by norm_num)
theorem B2038611 : Blo 2037435 2038611 := bstep (se 1 (by rfl) ⟨1528958, by rfl⟩ : syracuseStep 2038611 = 3057917) B3057917
theorem B4586885 : Blo 2037435 4586885 := bbase (se 4 (by rfl) ⟨430020, by rfl⟩ : syracuseStep 4586885 = 860041) (by norm_num)
theorem B3057923 : Blo 2037435 3057923 := bstep (se 1 (by rfl) ⟨2293442, by rfl⟩ : syracuseStep 3057923 = 4586885) B4586885
theorem B2038615 : Blo 2037435 2038615 := bstep (se 1 (by rfl) ⟨1528961, by rfl⟩ : syracuseStep 2038615 = 3057923) B3057923
theorem B2902645 : Blo 2037435 2902645 := bbase (se 5 (by rfl) ⟨136061, by rfl⟩ : syracuseStep 2902645 = 272123) (by norm_num)
theorem B3870193 : Blo 2037435 3870193 := bstep (se 2 (by rfl) ⟨1451322, by rfl⟩ : syracuseStep 3870193 = 2902645) B2902645
theorem B5160257 : Blo 2037435 5160257 := bstep (se 2 (by rfl) ⟨1935096, by rfl⟩ : syracuseStep 5160257 = 3870193) B3870193
theorem B3440171 : Blo 2037435 3440171 := bstep (se 1 (by rfl) ⟨2580128, by rfl⟩ : syracuseStep 3440171 = 5160257) B5160257
theorem B2293447 : Blo 2037435 2293447 := bstep (se 1 (by rfl) ⟨1720085, by rfl⟩ : syracuseStep 2293447 = 3440171) B3440171
theorem B3057929 : Blo 2037435 3057929 := bstep (se 2 (by rfl) ⟨1146723, by rfl⟩ : syracuseStep 3057929 = 2293447) B2293447
theorem B2038619 : Blo 2037435 2038619 := bstep (se 1 (by rfl) ⟨1528964, by rfl⟩ : syracuseStep 2038619 = 3057929) B3057929
theorem B10320533 : Blo 2037435 10320533 := bbase (se 6 (by rfl) ⟨241887, by rfl⟩ : syracuseStep 10320533 = 483775) (by norm_num)
theorem B6880355 : Blo 2037435 6880355 := bstep (se 1 (by rfl) ⟨5160266, by rfl⟩ : syracuseStep 6880355 = 10320533) B10320533
theorem B4586903 : Blo 2037435 4586903 := bstep (se 1 (by rfl) ⟨3440177, by rfl⟩ : syracuseStep 4586903 = 6880355) B6880355
theorem B3057935 : Blo 2037435 3057935 := bstep (se 1 (by rfl) ⟨2293451, by rfl⟩ : syracuseStep 3057935 = 4586903) B4586903
theorem B2038623 : Blo 2037435 2038623 := bstep (se 1 (by rfl) ⟨1528967, by rfl⟩ : syracuseStep 2038623 = 3057935) B3057935
theorem B3057941 : Blo 2037435 3057941 := bbase (se 6 (by rfl) ⟨71670, by rfl⟩ : syracuseStep 3057941 = 143341) (by norm_num)
theorem B2038627 : Blo 2037435 2038627 := bstep (se 1 (by rfl) ⟨1528970, by rfl⟩ : syracuseStep 2038627 = 3057941) B3057941
theorem B2449121 : Blo 2037435 2449121 := bbase (se 2 (by rfl) ⟨918420, by rfl⟩ : syracuseStep 2449121 = 1836841) (by norm_num)
theorem B26123957 : Blo 2037435 26123957 := bstep (se 5 (by rfl) ⟨1224560, by rfl⟩ : syracuseStep 26123957 = 2449121) B2449121
theorem B17415971 : Blo 2037435 17415971 := bstep (se 1 (by rfl) ⟨13061978, by rfl⟩ : syracuseStep 17415971 = 26123957) B26123957
theorem B11610647 : Blo 2037435 11610647 := bstep (se 1 (by rfl) ⟨8707985, by rfl⟩ : syracuseStep 11610647 = 17415971) B17415971
theorem B7740431 : Blo 2037435 7740431 := bstep (se 1 (by rfl) ⟨5805323, by rfl⟩ : syracuseStep 7740431 = 11610647) B11610647
theorem B5160287 : Blo 2037435 5160287 := bstep (se 1 (by rfl) ⟨3870215, by rfl⟩ : syracuseStep 5160287 = 7740431) B7740431
theorem B3440191 : Blo 2037435 3440191 := bstep (se 1 (by rfl) ⟨2580143, by rfl⟩ : syracuseStep 3440191 = 5160287) B5160287
theorem B4586921 : Blo 2037435 4586921 := bstep (se 2 (by rfl) ⟨1720095, by rfl⟩ : syracuseStep 4586921 = 3440191) B3440191
theorem B3057947 : Blo 2037435 3057947 := bstep (se 1 (by rfl) ⟨2293460, by rfl⟩ : syracuseStep 3057947 = 4586921) B4586921
theorem B2038631 : Blo 2037435 2038631 := bstep (se 1 (by rfl) ⟨1528973, by rfl⟩ : syracuseStep 2038631 = 3057947) B3057947
theorem B2293465 : Blo 2037435 2293465 := bbase (se 2 (by rfl) ⟨860049, by rfl⟩ : syracuseStep 2293465 = 1720099) (by norm_num)
theorem B3057953 : Blo 2037435 3057953 := bstep (se 2 (by rfl) ⟨1146732, by rfl⟩ : syracuseStep 3057953 = 2293465) B2293465
theorem B2038635 : Blo 2037435 2038635 := bstep (se 1 (by rfl) ⟨1528976, by rfl⟩ : syracuseStep 2038635 = 3057953) B3057953
theorem B2177005 : Blo 2037435 2177005 := bbase (se 3 (by rfl) ⟨408188, by rfl⟩ : syracuseStep 2177005 = 816377) (by norm_num)
theorem B2902673 : Blo 2037435 2902673 := bstep (se 2 (by rfl) ⟨1088502, by rfl⟩ : syracuseStep 2902673 = 2177005) B2177005
theorem B7740461 : Blo 2037435 7740461 := bstep (se 3 (by rfl) ⟨1451336, by rfl⟩ : syracuseStep 7740461 = 2902673) B2902673
theorem B5160307 : Blo 2037435 5160307 := bstep (se 1 (by rfl) ⟨3870230, by rfl⟩ : syracuseStep 5160307 = 7740461) B7740461
theorem B6880409 : Blo 2037435 6880409 := bstep (se 2 (by rfl) ⟨2580153, by rfl⟩ : syracuseStep 6880409 = 5160307) B5160307
theorem B4586939 : Blo 2037435 4586939 := bstep (se 1 (by rfl) ⟨3440204, by rfl⟩ : syracuseStep 4586939 = 6880409) B6880409
theorem B3057959 : Blo 2037435 3057959 := bstep (se 1 (by rfl) ⟨2293469, by rfl⟩ : syracuseStep 3057959 = 4586939) B4586939
theorem B2038639 : Blo 2037435 2038639 := bstep (se 1 (by rfl) ⟨1528979, by rfl⟩ : syracuseStep 2038639 = 3057959) B3057959
theorem B3057965 : Blo 2037435 3057965 := bbase (se 3 (by rfl) ⟨573368, by rfl⟩ : syracuseStep 3057965 = 1146737) (by norm_num)
theorem B2038643 : Blo 2037435 2038643 := bstep (se 1 (by rfl) ⟨1528982, by rfl⟩ : syracuseStep 2038643 = 3057965) B3057965
theorem B4586957 : Blo 2037435 4586957 := bbase (se 3 (by rfl) ⟨860054, by rfl⟩ : syracuseStep 4586957 = 1720109) (by norm_num)
theorem B3057971 : Blo 2037435 3057971 := bstep (se 1 (by rfl) ⟨2293478, by rfl⟩ : syracuseStep 3057971 = 4586957) B4586957
theorem B2038647 : Blo 2037435 2038647 := bstep (se 1 (by rfl) ⟨1528985, by rfl⟩ : syracuseStep 2038647 = 3057971) B3057971
theorem B2580169 : Blo 2037435 2580169 := bbase (se 2 (by rfl) ⟨967563, by rfl⟩ : syracuseStep 2580169 = 1935127) (by norm_num)
theorem B3440225 : Blo 2037435 3440225 := bstep (se 2 (by rfl) ⟨1290084, by rfl⟩ : syracuseStep 3440225 = 2580169) B2580169
theorem B2293483 : Blo 2037435 2293483 := bstep (se 1 (by rfl) ⟨1720112, by rfl⟩ : syracuseStep 2293483 = 3440225) B3440225
theorem B3057977 : Blo 2037435 3057977 := bstep (se 2 (by rfl) ⟨1146741, by rfl⟩ : syracuseStep 3057977 = 2293483) B2293483
theorem B2038651 : Blo 2037435 2038651 := bstep (se 1 (by rfl) ⟨1528988, by rfl⟩ : syracuseStep 2038651 = 3057977) B3057977
theorem B2615377 : Blo 2037435 2615377 := bbase (se 2 (by rfl) ⟨980766, by rfl⟩ : syracuseStep 2615377 = 1961533) (by norm_num)
theorem B3487169 : Blo 2037435 3487169 := bstep (se 2 (by rfl) ⟨1307688, by rfl⟩ : syracuseStep 3487169 = 2615377) B2615377
theorem B9299117 : Blo 2037435 9299117 := bstep (se 3 (by rfl) ⟨1743584, by rfl⟩ : syracuseStep 9299117 = 3487169) B3487169
theorem B6199411 : Blo 2037435 6199411 := bstep (se 1 (by rfl) ⟨4649558, by rfl⟩ : syracuseStep 6199411 = 9299117) B9299117
theorem B8265881 : Blo 2037435 8265881 := bstep (se 2 (by rfl) ⟨3099705, by rfl⟩ : syracuseStep 8265881 = 6199411) B6199411
theorem B5510587 : Blo 2037435 5510587 := bstep (se 1 (by rfl) ⟨4132940, by rfl⟩ : syracuseStep 5510587 = 8265881) B8265881
theorem B7347449 : Blo 2037435 7347449 := bstep (se 2 (by rfl) ⟨2755293, by rfl⟩ : syracuseStep 7347449 = 5510587) B5510587
theorem B19593197 : Blo 2037435 19593197 := bstep (se 3 (by rfl) ⟨3673724, by rfl⟩ : syracuseStep 19593197 = 7347449) B7347449
theorem B13062131 : Blo 2037435 13062131 := bstep (se 1 (by rfl) ⟨9796598, by rfl⟩ : syracuseStep 13062131 = 19593197) B19593197
theorem B8708087 : Blo 2037435 8708087 := bstep (se 1 (by rfl) ⟨6531065, by rfl⟩ : syracuseStep 8708087 = 13062131) B13062131
theorem B23221565 : Blo 2037435 23221565 := bstep (se 3 (by rfl) ⟨4354043, by rfl⟩ : syracuseStep 23221565 = 8708087) B8708087
theorem B15481043 : Blo 2037435 15481043 := bstep (se 1 (by rfl) ⟨11610782, by rfl⟩ : syracuseStep 15481043 = 23221565) B23221565
theorem B10320695 : Blo 2037435 10320695 := bstep (se 1 (by rfl) ⟨7740521, by rfl⟩ : syracuseStep 10320695 = 15481043) B15481043
theorem B6880463 : Blo 2037435 6880463 := bstep (se 1 (by rfl) ⟨5160347, by rfl⟩ : syracuseStep 6880463 = 10320695) B10320695
theorem B4586975 : Blo 2037435 4586975 := bstep (se 1 (by rfl) ⟨3440231, by rfl⟩ : syracuseStep 4586975 = 6880463) B6880463
theorem B3057983 : Blo 2037435 3057983 := bstep (se 1 (by rfl) ⟨2293487, by rfl⟩ : syracuseStep 3057983 = 4586975) B4586975
theorem B2038655 : Blo 2037435 2038655 := bstep (se 1 (by rfl) ⟨1528991, by rfl⟩ : syracuseStep 2038655 = 3057983) B3057983
theorem B3057989 : Blo 2037435 3057989 := bbase (se 4 (by rfl) ⟨286686, by rfl⟩ : syracuseStep 3057989 = 573373) (by norm_num)
theorem B2038659 : Blo 2037435 2038659 := bstep (se 1 (by rfl) ⟨1528994, by rfl⟩ : syracuseStep 2038659 = 3057989) B3057989
theorem B3440245 : Blo 2037435 3440245 := bbase (se 5 (by rfl) ⟨161261, by rfl⟩ : syracuseStep 3440245 = 322523) (by norm_num)
theorem B4586993 : Blo 2037435 4586993 := bstep (se 2 (by rfl) ⟨1720122, by rfl⟩ : syracuseStep 4586993 = 3440245) B3440245
theorem B3057995 : Blo 2037435 3057995 := bstep (se 1 (by rfl) ⟨2293496, by rfl⟩ : syracuseStep 3057995 = 4586993) B4586993
theorem B2038663 : Blo 2037435 2038663 := bstep (se 1 (by rfl) ⟨1528997, by rfl⟩ : syracuseStep 2038663 = 3057995) B3057995
theorem B2293501 : Blo 2037435 2293501 := bbase (se 3 (by rfl) ⟨430031, by rfl⟩ : syracuseStep 2293501 = 860063) (by norm_num)
theorem B3058001 : Blo 2037435 3058001 := bstep (se 2 (by rfl) ⟨1146750, by rfl⟩ : syracuseStep 3058001 = 2293501) B2293501
theorem B2038667 : Blo 2037435 2038667 := bstep (se 1 (by rfl) ⟨1529000, by rfl⟩ : syracuseStep 2038667 = 3058001) B3058001
theorem B6880517 : Blo 2037435 6880517 := bbase (se 4 (by rfl) ⟨645048, by rfl⟩ : syracuseStep 6880517 = 1290097) (by norm_num)
theorem B4587011 : Blo 2037435 4587011 := bstep (se 1 (by rfl) ⟨3440258, by rfl⟩ : syracuseStep 4587011 = 6880517) B6880517
theorem B3058007 : Blo 2037435 3058007 := bstep (se 1 (by rfl) ⟨2293505, by rfl⟩ : syracuseStep 3058007 = 4587011) B4587011
theorem B2038671 : Blo 2037435 2038671 := bstep (se 1 (by rfl) ⟨1529003, by rfl⟩ : syracuseStep 2038671 = 3058007) B3058007
theorem B3058013 : Blo 2037435 3058013 := bbase (se 3 (by rfl) ⟨573377, by rfl⟩ : syracuseStep 3058013 = 1146755) (by norm_num)
theorem B2038675 : Blo 2037435 2038675 := bstep (se 1 (by rfl) ⟨1529006, by rfl⟩ : syracuseStep 2038675 = 3058013) B3058013
theorem B4587029 : Blo 2037435 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B3058019 : Blo 2037435 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B2038679 : Blo 2037435 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B7740629 : Blo 2037435 7740629 := bbase (se 7 (by rfl) ⟨90710, by rfl⟩ : syracuseStep 7740629 = 181421) (by norm_num)
theorem B5160419 : Blo 2037435 5160419 := bstep (se 1 (by rfl) ⟨3870314, by rfl⟩ : syracuseStep 5160419 = 7740629) B7740629
theorem B3440279 : Blo 2037435 3440279 := bstep (se 1 (by rfl) ⟨2580209, by rfl⟩ : syracuseStep 3440279 = 5160419) B5160419
theorem B2293519 : Blo 2037435 2293519 := bstep (se 1 (by rfl) ⟨1720139, by rfl⟩ : syracuseStep 2293519 = 3440279) B3440279
theorem B3058025 : Blo 2037435 3058025 := bstep (se 2 (by rfl) ⟨1146759, by rfl⟩ : syracuseStep 3058025 = 2293519) B2293519
theorem B2038683 : Blo 2037435 2038683 := bstep (se 1 (by rfl) ⟨1529012, by rfl⟩ : syracuseStep 2038683 = 3058025) B3058025
theorem B11610965 : Blo 2037435 11610965 := bbase (se 9 (by rfl) ⟨34016, by rfl⟩ : syracuseStep 11610965 = 68033) (by norm_num)
theorem B7740643 : Blo 2037435 7740643 := bstep (se 1 (by rfl) ⟨5805482, by rfl⟩ : syracuseStep 7740643 = 11610965) B11610965
theorem B10320857 : Blo 2037435 10320857 := bstep (se 2 (by rfl) ⟨3870321, by rfl⟩ : syracuseStep 10320857 = 7740643) B7740643
theorem B6880571 : Blo 2037435 6880571 := bstep (se 1 (by rfl) ⟨5160428, by rfl⟩ : syracuseStep 6880571 = 10320857) B10320857
theorem B4587047 : Blo 2037435 4587047 := bstep (se 1 (by rfl) ⟨3440285, by rfl⟩ : syracuseStep 4587047 = 6880571) B6880571
theorem B3058031 : Blo 2037435 3058031 := bstep (se 1 (by rfl) ⟨2293523, by rfl⟩ : syracuseStep 3058031 = 4587047) B4587047
theorem B2038687 : Blo 2037435 2038687 := bstep (se 1 (by rfl) ⟨1529015, by rfl⟩ : syracuseStep 2038687 = 3058031) B3058031
theorem B3058037 : Blo 2037435 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B2038691 : Blo 2037435 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B2177065 : Blo 2037435 2177065 := bbase (se 2 (by rfl) ⟨816399, by rfl⟩ : syracuseStep 2177065 = 1632799) (by norm_num)
theorem B2902753 : Blo 2037435 2902753 := bstep (se 2 (by rfl) ⟨1088532, by rfl⟩ : syracuseStep 2902753 = 2177065) B2177065
theorem B3870337 : Blo 2037435 3870337 := bstep (se 2 (by rfl) ⟨1451376, by rfl⟩ : syracuseStep 3870337 = 2902753) B2902753
theorem B5160449 : Blo 2037435 5160449 := bstep (se 2 (by rfl) ⟨1935168, by rfl⟩ : syracuseStep 5160449 = 3870337) B3870337
theorem B3440299 : Blo 2037435 3440299 := bstep (se 1 (by rfl) ⟨2580224, by rfl⟩ : syracuseStep 3440299 = 5160449) B5160449
theorem B4587065 : Blo 2037435 4587065 := bstep (se 2 (by rfl) ⟨1720149, by rfl⟩ : syracuseStep 4587065 = 3440299) B3440299
theorem B3058043 : Blo 2037435 3058043 := bstep (se 1 (by rfl) ⟨2293532, by rfl⟩ : syracuseStep 3058043 = 4587065) B4587065
theorem B2038695 : Blo 2037435 2038695 := bstep (se 1 (by rfl) ⟨1529021, by rfl⟩ : syracuseStep 2038695 = 3058043) B3058043
theorem B2293537 : Blo 2037435 2293537 := bbase (se 2 (by rfl) ⟨860076, by rfl⟩ : syracuseStep 2293537 = 1720153) (by norm_num)
theorem B3058049 : Blo 2037435 3058049 := bstep (se 2 (by rfl) ⟨1146768, by rfl⟩ : syracuseStep 3058049 = 2293537) B2293537
theorem B2038699 : Blo 2037435 2038699 := bstep (se 1 (by rfl) ⟨1529024, by rfl⟩ : syracuseStep 2038699 = 3058049) B3058049
theorem B5160469 : Blo 2037435 5160469 := bbase (se 6 (by rfl) ⟨120948, by rfl⟩ : syracuseStep 5160469 = 241897) (by norm_num)
theorem B6880625 : Blo 2037435 6880625 := bstep (se 2 (by rfl) ⟨2580234, by rfl⟩ : syracuseStep 6880625 = 5160469) B5160469
theorem B4587083 : Blo 2037435 4587083 := bstep (se 1 (by rfl) ⟨3440312, by rfl⟩ : syracuseStep 4587083 = 6880625) B6880625
theorem B3058055 : Blo 2037435 3058055 := bstep (se 1 (by rfl) ⟨2293541, by rfl⟩ : syracuseStep 3058055 = 4587083) B4587083
theorem B2038703 : Blo 2037435 2038703 := bstep (se 1 (by rfl) ⟨1529027, by rfl⟩ : syracuseStep 2038703 = 3058055) B3058055
theorem B3058061 : Blo 2037435 3058061 := bbase (se 3 (by rfl) ⟨573386, by rfl⟩ : syracuseStep 3058061 = 1146773) (by norm_num)
theorem B2038707 : Blo 2037435 2038707 := bstep (se 1 (by rfl) ⟨1529030, by rfl⟩ : syracuseStep 2038707 = 3058061) B3058061
theorem B4587101 : Blo 2037435 4587101 := bbase (se 3 (by rfl) ⟨860081, by rfl⟩ : syracuseStep 4587101 = 1720163) (by norm_num)
theorem B3058067 : Blo 2037435 3058067 := bstep (se 1 (by rfl) ⟨2293550, by rfl⟩ : syracuseStep 3058067 = 4587101) B4587101
theorem B2038711 : Blo 2037435 2038711 := bstep (se 1 (by rfl) ⟨1529033, by rfl⟩ : syracuseStep 2038711 = 3058067) B3058067
theorem B3440333 : Blo 2037435 3440333 := bbase (se 3 (by rfl) ⟨645062, by rfl⟩ : syracuseStep 3440333 = 1290125) (by norm_num)
theorem B2293555 : Blo 2037435 2293555 := bstep (se 1 (by rfl) ⟨1720166, by rfl⟩ : syracuseStep 2293555 = 3440333) B3440333
theorem B3058073 : Blo 2037435 3058073 := bstep (se 2 (by rfl) ⟨1146777, by rfl⟩ : syracuseStep 3058073 = 2293555) B2293555
theorem B2038715 : Blo 2037435 2038715 := bstep (se 1 (by rfl) ⟨1529036, by rfl⟩ : syracuseStep 2038715 = 3058073) B3058073
theorem B4898453 : Blo 2037435 4898453 := bbase (se 6 (by rfl) ⟨114807, by rfl⟩ : syracuseStep 4898453 = 229615) (by norm_num)
theorem B13062541 : Blo 2037435 13062541 := bstep (se 3 (by rfl) ⟨2449226, by rfl⟩ : syracuseStep 13062541 = 4898453) B4898453
theorem B17416721 : Blo 2037435 17416721 := bstep (se 2 (by rfl) ⟨6531270, by rfl⟩ : syracuseStep 17416721 = 13062541) B13062541
theorem B11611147 : Blo 2037435 11611147 := bstep (se 1 (by rfl) ⟨8708360, by rfl⟩ : syracuseStep 11611147 = 17416721) B17416721
theorem B15481529 : Blo 2037435 15481529 := bstep (se 2 (by rfl) ⟨5805573, by rfl⟩ : syracuseStep 15481529 = 11611147) B11611147
theorem B10321019 : Blo 2037435 10321019 := bstep (se 1 (by rfl) ⟨7740764, by rfl⟩ : syracuseStep 10321019 = 15481529) B15481529
theorem B6880679 : Blo 2037435 6880679 := bstep (se 1 (by rfl) ⟨5160509, by rfl⟩ : syracuseStep 6880679 = 10321019) B10321019
theorem B4587119 : Blo 2037435 4587119 := bstep (se 1 (by rfl) ⟨3440339, by rfl⟩ : syracuseStep 4587119 = 6880679) B6880679
theorem B3058079 : Blo 2037435 3058079 := bstep (se 1 (by rfl) ⟨2293559, by rfl⟩ : syracuseStep 3058079 = 4587119) B4587119
theorem B2038719 : Blo 2037435 2038719 := bstep (se 1 (by rfl) ⟨1529039, by rfl⟩ : syracuseStep 2038719 = 3058079) B3058079
theorem B3058085 : Blo 2037435 3058085 := bbase (se 4 (by rfl) ⟨286695, by rfl⟩ : syracuseStep 3058085 = 573391) (by norm_num)
theorem B2038723 : Blo 2037435 2038723 := bstep (se 1 (by rfl) ⟨1529042, by rfl⟩ : syracuseStep 2038723 = 3058085) B3058085
theorem B2580265 : Blo 2037435 2580265 := bbase (se 2 (by rfl) ⟨967599, by rfl⟩ : syracuseStep 2580265 = 1935199) (by norm_num)
theorem B3440353 : Blo 2037435 3440353 := bstep (se 2 (by rfl) ⟨1290132, by rfl⟩ : syracuseStep 3440353 = 2580265) B2580265
theorem B4587137 : Blo 2037435 4587137 := bstep (se 2 (by rfl) ⟨1720176, by rfl⟩ : syracuseStep 4587137 = 3440353) B3440353
theorem B3058091 : Blo 2037435 3058091 := bstep (se 1 (by rfl) ⟨2293568, by rfl⟩ : syracuseStep 3058091 = 4587137) B4587137
theorem B2038727 : Blo 2037435 2038727 := bstep (se 1 (by rfl) ⟨1529045, by rfl⟩ : syracuseStep 2038727 = 3058091) B3058091
theorem B2293573 : Blo 2037435 2293573 := bbase (se 4 (by rfl) ⟨215022, by rfl⟩ : syracuseStep 2293573 = 430045) (by norm_num)
theorem B3058097 : Blo 2037435 3058097 := bstep (se 2 (by rfl) ⟨1146786, by rfl⟩ : syracuseStep 3058097 = 2293573) B2293573
theorem B2038731 : Blo 2037435 2038731 := bstep (se 1 (by rfl) ⟨1529048, by rfl⟩ : syracuseStep 2038731 = 3058097) B3058097
theorem B3870413 : Blo 2037435 3870413 := bbase (se 3 (by rfl) ⟨725702, by rfl⟩ : syracuseStep 3870413 = 1451405) (by norm_num)
theorem B2580275 : Blo 2037435 2580275 := bstep (se 1 (by rfl) ⟨1935206, by rfl⟩ : syracuseStep 2580275 = 3870413) B3870413
theorem B6880733 : Blo 2037435 6880733 := bstep (se 3 (by rfl) ⟨1290137, by rfl⟩ : syracuseStep 6880733 = 2580275) B2580275
theorem B4587155 : Blo 2037435 4587155 := bstep (se 1 (by rfl) ⟨3440366, by rfl⟩ : syracuseStep 4587155 = 6880733) B6880733
theorem B3058103 : Blo 2037435 3058103 := bstep (se 1 (by rfl) ⟨2293577, by rfl⟩ : syracuseStep 3058103 = 4587155) B4587155
theorem B2038735 : Blo 2037435 2038735 := bstep (se 1 (by rfl) ⟨1529051, by rfl⟩ : syracuseStep 2038735 = 3058103) B3058103
theorem B3058109 : Blo 2037435 3058109 := bbase (se 3 (by rfl) ⟨573395, by rfl⟩ : syracuseStep 3058109 = 1146791) (by norm_num)
theorem B2038739 : Blo 2037435 2038739 := bstep (se 1 (by rfl) ⟨1529054, by rfl⟩ : syracuseStep 2038739 = 3058109) B3058109
theorem B4587173 : Blo 2037435 4587173 := bbase (se 4 (by rfl) ⟨430047, by rfl⟩ : syracuseStep 4587173 = 860095) (by norm_num)
theorem B3058115 : Blo 2037435 3058115 := bstep (se 1 (by rfl) ⟨2293586, by rfl⟩ : syracuseStep 3058115 = 4587173) B4587173
theorem B2038743 : Blo 2037435 2038743 := bstep (se 1 (by rfl) ⟨1529057, by rfl⟩ : syracuseStep 2038743 = 3058115) B3058115
theorem B5160581 : Blo 2037435 5160581 := bbase (se 4 (by rfl) ⟨483804, by rfl⟩ : syracuseStep 5160581 = 967609) (by norm_num)
theorem B3440387 : Blo 2037435 3440387 := bstep (se 1 (by rfl) ⟨2580290, by rfl⟩ : syracuseStep 3440387 = 5160581) B5160581
theorem B2293591 : Blo 2037435 2293591 := bstep (se 1 (by rfl) ⟨1720193, by rfl⟩ : syracuseStep 2293591 = 3440387) B3440387
theorem B3058121 : Blo 2037435 3058121 := bstep (se 2 (by rfl) ⟨1146795, by rfl⟩ : syracuseStep 3058121 = 2293591) B2293591
theorem B2038747 : Blo 2037435 2038747 := bstep (se 1 (by rfl) ⟨1529060, by rfl⟩ : syracuseStep 2038747 = 3058121) B3058121
theorem B7347797 : Blo 2037435 7347797 := bbase (se 8 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 7347797 = 86107) (by norm_num)
theorem B4898531 : Blo 2037435 4898531 := bstep (se 1 (by rfl) ⟨3673898, by rfl⟩ : syracuseStep 4898531 = 7347797) B7347797
theorem B3265687 : Blo 2037435 3265687 := bstep (se 1 (by rfl) ⟨2449265, by rfl⟩ : syracuseStep 3265687 = 4898531) B4898531
theorem B4354249 : Blo 2037435 4354249 := bstep (se 2 (by rfl) ⟨1632843, by rfl⟩ : syracuseStep 4354249 = 3265687) B3265687
theorem B5805665 : Blo 2037435 5805665 := bstep (se 2 (by rfl) ⟨2177124, by rfl⟩ : syracuseStep 5805665 = 4354249) B4354249
theorem B3870443 : Blo 2037435 3870443 := bstep (se 1 (by rfl) ⟨2902832, by rfl⟩ : syracuseStep 3870443 = 5805665) B5805665
theorem B10321181 : Blo 2037435 10321181 := bstep (se 3 (by rfl) ⟨1935221, by rfl⟩ : syracuseStep 10321181 = 3870443) B3870443
theorem B6880787 : Blo 2037435 6880787 := bstep (se 1 (by rfl) ⟨5160590, by rfl⟩ : syracuseStep 6880787 = 10321181) B10321181
theorem B4587191 : Blo 2037435 4587191 := bstep (se 1 (by rfl) ⟨3440393, by rfl⟩ : syracuseStep 4587191 = 6880787) B6880787
theorem B3058127 : Blo 2037435 3058127 := bstep (se 1 (by rfl) ⟨2293595, by rfl⟩ : syracuseStep 3058127 = 4587191) B4587191
theorem B2038751 : Blo 2037435 2038751 := bstep (se 1 (by rfl) ⟨1529063, by rfl⟩ : syracuseStep 2038751 = 3058127) B3058127
theorem B3058133 : Blo 2037435 3058133 := bbase (se 7 (by rfl) ⟨35837, by rfl⟩ : syracuseStep 3058133 = 71675) (by norm_num)
theorem B2038755 : Blo 2037435 2038755 := bstep (se 1 (by rfl) ⟨1529066, by rfl⟩ : syracuseStep 2038755 = 3058133) B3058133
theorem B7740917 : Blo 2037435 7740917 := bbase (se 5 (by rfl) ⟨362855, by rfl⟩ : syracuseStep 7740917 = 725711) (by norm_num)
theorem B5160611 : Blo 2037435 5160611 := bstep (se 1 (by rfl) ⟨3870458, by rfl⟩ : syracuseStep 5160611 = 7740917) B7740917
theorem B3440407 : Blo 2037435 3440407 := bstep (se 1 (by rfl) ⟨2580305, by rfl⟩ : syracuseStep 3440407 = 5160611) B5160611
theorem B4587209 : Blo 2037435 4587209 := bstep (se 2 (by rfl) ⟨1720203, by rfl⟩ : syracuseStep 4587209 = 3440407) B3440407
theorem B3058139 : Blo 2037435 3058139 := bstep (se 1 (by rfl) ⟨2293604, by rfl⟩ : syracuseStep 3058139 = 4587209) B4587209
theorem B2038759 : Blo 2037435 2038759 := bstep (se 1 (by rfl) ⟨1529069, by rfl⟩ : syracuseStep 2038759 = 3058139) B3058139
theorem B2293609 : Blo 2037435 2293609 := bbase (se 2 (by rfl) ⟨860103, by rfl⟩ : syracuseStep 2293609 = 1720207) (by norm_num)
theorem B3058145 : Blo 2037435 3058145 := bstep (se 2 (by rfl) ⟨1146804, by rfl⟩ : syracuseStep 3058145 = 2293609) B2293609
theorem B2038763 : Blo 2037435 2038763 := bstep (se 1 (by rfl) ⟨1529072, by rfl⟩ : syracuseStep 2038763 = 3058145) B3058145
theorem B10462085 : Blo 2037435 10462085 := bbase (se 4 (by rfl) ⟨980820, by rfl⟩ : syracuseStep 10462085 = 1961641) (by norm_num)
theorem B6974723 : Blo 2037435 6974723 := bstep (se 1 (by rfl) ⟨5231042, by rfl⟩ : syracuseStep 6974723 = 10462085) B10462085
theorem B4649815 : Blo 2037435 4649815 := bstep (se 1 (by rfl) ⟨3487361, by rfl⟩ : syracuseStep 4649815 = 6974723) B6974723
theorem B6199753 : Blo 2037435 6199753 := bstep (se 2 (by rfl) ⟨2324907, by rfl⟩ : syracuseStep 6199753 = 4649815) B4649815
theorem B8266337 : Blo 2037435 8266337 := bstep (se 2 (by rfl) ⟨3099876, by rfl⟩ : syracuseStep 8266337 = 6199753) B6199753
theorem B5510891 : Blo 2037435 5510891 := bstep (se 1 (by rfl) ⟨4133168, by rfl⟩ : syracuseStep 5510891 = 8266337) B8266337
theorem B3673927 : Blo 2037435 3673927 := bstep (se 1 (by rfl) ⟨2755445, by rfl⟩ : syracuseStep 3673927 = 5510891) B5510891
theorem B4898569 : Blo 2037435 4898569 := bstep (se 2 (by rfl) ⟨1836963, by rfl⟩ : syracuseStep 4898569 = 3673927) B3673927
theorem B6531425 : Blo 2037435 6531425 := bstep (se 2 (by rfl) ⟨2449284, by rfl⟩ : syracuseStep 6531425 = 4898569) B4898569
theorem B4354283 : Blo 2037435 4354283 := bstep (se 1 (by rfl) ⟨3265712, by rfl⟩ : syracuseStep 4354283 = 6531425) B6531425
theorem B11611421 : Blo 2037435 11611421 := bstep (se 3 (by rfl) ⟨2177141, by rfl⟩ : syracuseStep 11611421 = 4354283) B4354283
theorem B7740947 : Blo 2037435 7740947 := bstep (se 1 (by rfl) ⟨5805710, by rfl⟩ : syracuseStep 7740947 = 11611421) B11611421
theorem B5160631 : Blo 2037435 5160631 := bstep (se 1 (by rfl) ⟨3870473, by rfl⟩ : syracuseStep 5160631 = 7740947) B7740947
theorem B6880841 : Blo 2037435 6880841 := bstep (se 2 (by rfl) ⟨2580315, by rfl⟩ : syracuseStep 6880841 = 5160631) B5160631
theorem B4587227 : Blo 2037435 4587227 := bstep (se 1 (by rfl) ⟨3440420, by rfl⟩ : syracuseStep 4587227 = 6880841) B6880841
theorem B3058151 : Blo 2037435 3058151 := bstep (se 1 (by rfl) ⟨2293613, by rfl⟩ : syracuseStep 3058151 = 4587227) B4587227
theorem B2038767 : Blo 2037435 2038767 := bstep (se 1 (by rfl) ⟨1529075, by rfl⟩ : syracuseStep 2038767 = 3058151) B3058151
theorem B3058157 : Blo 2037435 3058157 := bbase (se 3 (by rfl) ⟨573404, by rfl⟩ : syracuseStep 3058157 = 1146809) (by norm_num)
theorem B2038771 : Blo 2037435 2038771 := bstep (se 1 (by rfl) ⟨1529078, by rfl⟩ : syracuseStep 2038771 = 3058157) B3058157
theorem B4587245 : Blo 2037435 4587245 := bbase (se 3 (by rfl) ⟨860108, by rfl⟩ : syracuseStep 4587245 = 1720217) (by norm_num)
theorem B3058163 : Blo 2037435 3058163 := bstep (se 1 (by rfl) ⟨2293622, by rfl⟩ : syracuseStep 3058163 = 4587245) B4587245
theorem B2038775 : Blo 2037435 2038775 := bstep (se 1 (by rfl) ⟨1529081, by rfl⟩ : syracuseStep 2038775 = 3058163) B3058163
theorem B3265733 : Blo 2037435 3265733 := bbase (se 4 (by rfl) ⟨306162, by rfl⟩ : syracuseStep 3265733 = 612325) (by norm_num)
theorem B2177155 : Blo 2037435 2177155 := bstep (se 1 (by rfl) ⟨1632866, by rfl⟩ : syracuseStep 2177155 = 3265733) B3265733
theorem B2902873 : Blo 2037435 2902873 := bstep (se 2 (by rfl) ⟨1088577, by rfl⟩ : syracuseStep 2902873 = 2177155) B2177155
theorem B3870497 : Blo 2037435 3870497 := bstep (se 2 (by rfl) ⟨1451436, by rfl⟩ : syracuseStep 3870497 = 2902873) B2902873
theorem B2580331 : Blo 2037435 2580331 := bstep (se 1 (by rfl) ⟨1935248, by rfl⟩ : syracuseStep 2580331 = 3870497) B3870497
theorem B3440441 : Blo 2037435 3440441 := bstep (se 2 (by rfl) ⟨1290165, by rfl⟩ : syracuseStep 3440441 = 2580331) B2580331
theorem B2293627 : Blo 2037435 2293627 := bstep (se 1 (by rfl) ⟨1720220, by rfl⟩ : syracuseStep 2293627 = 3440441) B3440441
theorem B3058169 : Blo 2037435 3058169 := bstep (se 2 (by rfl) ⟨1146813, by rfl⟩ : syracuseStep 3058169 = 2293627) B2293627
theorem B2038779 : Blo 2037435 2038779 := bstep (se 1 (by rfl) ⟨1529084, by rfl⟩ : syracuseStep 2038779 = 3058169) B3058169
theorem B6046645 : Blo 2037435 6046645 := bbase (se 5 (by rfl) ⟨283436, by rfl⟩ : syracuseStep 6046645 = 566873) (by norm_num)
theorem B8062193 : Blo 2037435 8062193 := bstep (se 2 (by rfl) ⟨3023322, by rfl⟩ : syracuseStep 8062193 = 6046645) B6046645
theorem B21499181 : Blo 2037435 21499181 := bstep (se 3 (by rfl) ⟨4031096, by rfl⟩ : syracuseStep 21499181 = 8062193) B8062193
theorem B14332787 : Blo 2037435 14332787 := bstep (se 1 (by rfl) ⟨10749590, by rfl⟩ : syracuseStep 14332787 = 21499181) B21499181
theorem B9555191 : Blo 2037435 9555191 := bstep (se 1 (by rfl) ⟨7166393, by rfl⟩ : syracuseStep 9555191 = 14332787) B14332787
theorem B6370127 : Blo 2037435 6370127 := bstep (se 1 (by rfl) ⟨4777595, by rfl⟩ : syracuseStep 6370127 = 9555191) B9555191
theorem B4246751 : Blo 2037435 4246751 := bstep (se 1 (by rfl) ⟨3185063, by rfl⟩ : syracuseStep 4246751 = 6370127) B6370127
theorem B2831167 : Blo 2037435 2831167 := bstep (se 1 (by rfl) ⟨2123375, by rfl⟩ : syracuseStep 2831167 = 4246751) B4246751
theorem B3774889 : Blo 2037435 3774889 := bstep (se 2 (by rfl) ⟨1415583, by rfl⟩ : syracuseStep 3774889 = 2831167) B2831167
theorem B5033185 : Blo 2037435 5033185 := bstep (se 2 (by rfl) ⟨1887444, by rfl⟩ : syracuseStep 5033185 = 3774889) B3774889
theorem B26843653 : Blo 2037435 26843653 := bstep (se 4 (by rfl) ⟨2516592, by rfl⟩ : syracuseStep 26843653 = 5033185) B5033185
theorem B35791537 : Blo 2037435 35791537 := bstep (se 2 (by rfl) ⟨13421826, by rfl⟩ : syracuseStep 35791537 = 26843653) B26843653
theorem B47722049 : Blo 2037435 47722049 := bstep (se 2 (by rfl) ⟨17895768, by rfl⟩ : syracuseStep 47722049 = 35791537) B35791537
theorem B31814699 : Blo 2037435 31814699 := bstep (se 1 (by rfl) ⟨23861024, by rfl⟩ : syracuseStep 31814699 = 47722049) B47722049
theorem B339356789 : Blo 2037435 339356789 := bstep (se 5 (by rfl) ⟨15907349, by rfl⟩ : syracuseStep 339356789 = 31814699) B31814699
theorem B226237859 : Blo 2037435 226237859 := bstep (se 1 (by rfl) ⟨169678394, by rfl⟩ : syracuseStep 226237859 = 339356789) B339356789
theorem B150825239 : Blo 2037435 150825239 := bstep (se 1 (by rfl) ⟨113118929, by rfl⟩ : syracuseStep 150825239 = 226237859) B226237859
theorem B100550159 : Blo 2037435 100550159 := bstep (se 1 (by rfl) ⟨75412619, by rfl⟩ : syracuseStep 100550159 = 150825239) B150825239
theorem B67033439 : Blo 2037435 67033439 := bstep (se 1 (by rfl) ⟨50275079, by rfl⟩ : syracuseStep 67033439 = 100550159) B100550159
theorem B44688959 : Blo 2037435 44688959 := bstep (se 1 (by rfl) ⟨33516719, by rfl⟩ : syracuseStep 44688959 = 67033439) B67033439
theorem B29792639 : Blo 2037435 29792639 := bstep (se 1 (by rfl) ⟨22344479, by rfl⟩ : syracuseStep 29792639 = 44688959) B44688959
theorem B19861759 : Blo 2037435 19861759 := bstep (se 1 (by rfl) ⟨14896319, by rfl⟩ : syracuseStep 19861759 = 29792639) B29792639
theorem B26482345 : Blo 2037435 26482345 := bstep (se 2 (by rfl) ⟨9930879, by rfl⟩ : syracuseStep 26482345 = 19861759) B19861759
theorem B564956693 : Blo 2037435 564956693 := bstep (se 6 (by rfl) ⟨13241172, by rfl⟩ : syracuseStep 564956693 = 26482345) B26482345
theorem B376637795 : Blo 2037435 376637795 := bstep (se 1 (by rfl) ⟨282478346, by rfl⟩ : syracuseStep 376637795 = 564956693) B564956693
theorem B251091863 : Blo 2037435 251091863 := bstep (se 1 (by rfl) ⟨188318897, by rfl⟩ : syracuseStep 251091863 = 376637795) B376637795
theorem B167394575 : Blo 2037435 167394575 := bstep (se 1 (by rfl) ⟨125545931, by rfl⟩ : syracuseStep 167394575 = 251091863) B251091863
theorem B111596383 : Blo 2037435 111596383 := bstep (se 1 (by rfl) ⟨83697287, by rfl⟩ : syracuseStep 111596383 = 167394575) B167394575
theorem B148795177 : Blo 2037435 148795177 := bstep (se 2 (by rfl) ⟨55798191, by rfl⟩ : syracuseStep 148795177 = 111596383) B111596383
theorem B198393569 : Blo 2037435 198393569 := bstep (se 2 (by rfl) ⟨74397588, by rfl⟩ : syracuseStep 198393569 = 148795177) B148795177
theorem B132262379 : Blo 2037435 132262379 := bstep (se 1 (by rfl) ⟨99196784, by rfl⟩ : syracuseStep 132262379 = 198393569) B198393569
theorem B88174919 : Blo 2037435 88174919 := bstep (se 1 (by rfl) ⟨66131189, by rfl⟩ : syracuseStep 88174919 = 132262379) B132262379
theorem B58783279 : Blo 2037435 58783279 := bstep (se 1 (by rfl) ⟨44087459, by rfl⟩ : syracuseStep 58783279 = 88174919) B88174919
theorem B78377705 : Blo 2037435 78377705 := bstep (se 2 (by rfl) ⟨29391639, by rfl⟩ : syracuseStep 78377705 = 58783279) B58783279
theorem B52251803 : Blo 2037435 52251803 := bstep (se 1 (by rfl) ⟨39188852, by rfl⟩ : syracuseStep 52251803 = 78377705) B78377705
theorem B34834535 : Blo 2037435 34834535 := bstep (se 1 (by rfl) ⟨26125901, by rfl⟩ : syracuseStep 34834535 = 52251803) B52251803
theorem B23223023 : Blo 2037435 23223023 := bstep (se 1 (by rfl) ⟨17417267, by rfl⟩ : syracuseStep 23223023 = 34834535) B34834535
theorem B15482015 : Blo 2037435 15482015 := bstep (se 1 (by rfl) ⟨11611511, by rfl⟩ : syracuseStep 15482015 = 23223023) B23223023
theorem B10321343 : Blo 2037435 10321343 := bstep (se 1 (by rfl) ⟨7741007, by rfl⟩ : syracuseStep 10321343 = 15482015) B15482015
theorem B6880895 : Blo 2037435 6880895 := bstep (se 1 (by rfl) ⟨5160671, by rfl⟩ : syracuseStep 6880895 = 10321343) B10321343
theorem B4587263 : Blo 2037435 4587263 := bstep (se 1 (by rfl) ⟨3440447, by rfl⟩ : syracuseStep 4587263 = 6880895) B6880895
theorem B3058175 : Blo 2037435 3058175 := bstep (se 1 (by rfl) ⟨2293631, by rfl⟩ : syracuseStep 3058175 = 4587263) B4587263
theorem B2038783 : Blo 2037435 2038783 := bstep (se 1 (by rfl) ⟨1529087, by rfl⟩ : syracuseStep 2038783 = 3058175) B3058175
theorem B3058181 : Blo 2037435 3058181 := bbase (se 4 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 3058181 = 573409) (by norm_num)
theorem B2038787 : Blo 2037435 2038787 := bstep (se 1 (by rfl) ⟨1529090, by rfl⟩ : syracuseStep 2038787 = 3058181) B3058181
theorem B3440461 : Blo 2037435 3440461 := bbase (se 3 (by rfl) ⟨645086, by rfl⟩ : syracuseStep 3440461 = 1290173) (by norm_num)
theorem B4587281 : Blo 2037435 4587281 := bstep (se 2 (by rfl) ⟨1720230, by rfl⟩ : syracuseStep 4587281 = 3440461) B3440461
theorem B3058187 : Blo 2037435 3058187 := bstep (se 1 (by rfl) ⟨2293640, by rfl⟩ : syracuseStep 3058187 = 4587281) B4587281
theorem B2038791 : Blo 2037435 2038791 := bstep (se 1 (by rfl) ⟨1529093, by rfl⟩ : syracuseStep 2038791 = 3058187) B3058187
theorem B2293645 : Blo 2037435 2293645 := bbase (se 3 (by rfl) ⟨430058, by rfl⟩ : syracuseStep 2293645 = 860117) (by norm_num)
theorem B3058193 : Blo 2037435 3058193 := bstep (se 2 (by rfl) ⟨1146822, by rfl⟩ : syracuseStep 3058193 = 2293645) B2293645
theorem B2038795 : Blo 2037435 2038795 := bstep (se 1 (by rfl) ⟨1529096, by rfl⟩ : syracuseStep 2038795 = 3058193) B3058193
theorem B6880949 : Blo 2037435 6880949 := bbase (se 5 (by rfl) ⟨322544, by rfl⟩ : syracuseStep 6880949 = 645089) (by norm_num)
theorem B4587299 : Blo 2037435 4587299 := bstep (se 1 (by rfl) ⟨3440474, by rfl⟩ : syracuseStep 4587299 = 6880949) B6880949
theorem B3058199 : Blo 2037435 3058199 := bstep (se 1 (by rfl) ⟨2293649, by rfl⟩ : syracuseStep 3058199 = 4587299) B4587299
theorem B2038799 : Blo 2037435 2038799 := bstep (se 1 (by rfl) ⟨1529099, by rfl⟩ : syracuseStep 2038799 = 3058199) B3058199
theorem B3058205 : Blo 2037435 3058205 := bbase (se 3 (by rfl) ⟨573413, by rfl⟩ : syracuseStep 3058205 = 1146827) (by norm_num)
theorem B2038803 : Blo 2037435 2038803 := bstep (se 1 (by rfl) ⟨1529102, by rfl⟩ : syracuseStep 2038803 = 3058205) B3058205
theorem B4587317 : Blo 2037435 4587317 := bbase (se 5 (by rfl) ⟨215030, by rfl⟩ : syracuseStep 4587317 = 430061) (by norm_num)
theorem B3058211 : Blo 2037435 3058211 := bstep (se 1 (by rfl) ⟨2293658, by rfl⟩ : syracuseStep 3058211 = 4587317) B4587317
theorem B2038807 : Blo 2037435 2038807 := bstep (se 1 (by rfl) ⟨1529105, by rfl⟩ : syracuseStep 2038807 = 3058211) B3058211
theorem B2066629 : Blo 2037435 2066629 := bbase (se 4 (by rfl) ⟨193746, by rfl⟩ : syracuseStep 2066629 = 387493) (by norm_num)
theorem B2755505 : Blo 2037435 2755505 := bstep (se 2 (by rfl) ⟨1033314, by rfl⟩ : syracuseStep 2755505 = 2066629) B2066629
theorem B7348013 : Blo 2037435 7348013 := bstep (se 3 (by rfl) ⟨1377752, by rfl⟩ : syracuseStep 7348013 = 2755505) B2755505
theorem B4898675 : Blo 2037435 4898675 := bstep (se 1 (by rfl) ⟨3674006, by rfl⟩ : syracuseStep 4898675 = 7348013) B7348013
theorem B13063133 : Blo 2037435 13063133 := bstep (se 3 (by rfl) ⟨2449337, by rfl⟩ : syracuseStep 13063133 = 4898675) B4898675
theorem B8708755 : Blo 2037435 8708755 := bstep (se 1 (by rfl) ⟨6531566, by rfl⟩ : syracuseStep 8708755 = 13063133) B13063133
theorem B11611673 : Blo 2037435 11611673 := bstep (se 2 (by rfl) ⟨4354377, by rfl⟩ : syracuseStep 11611673 = 8708755) B8708755
theorem B7741115 : Blo 2037435 7741115 := bstep (se 1 (by rfl) ⟨5805836, by rfl⟩ : syracuseStep 7741115 = 11611673) B11611673
theorem B5160743 : Blo 2037435 5160743 := bstep (se 1 (by rfl) ⟨3870557, by rfl⟩ : syracuseStep 5160743 = 7741115) B7741115
theorem B3440495 : Blo 2037435 3440495 := bstep (se 1 (by rfl) ⟨2580371, by rfl⟩ : syracuseStep 3440495 = 5160743) B5160743
theorem B2293663 : Blo 2037435 2293663 := bstep (se 1 (by rfl) ⟨1720247, by rfl⟩ : syracuseStep 2293663 = 3440495) B3440495
theorem B3058217 : Blo 2037435 3058217 := bstep (se 2 (by rfl) ⟨1146831, by rfl⟩ : syracuseStep 3058217 = 2293663) B2293663
theorem B2038811 : Blo 2037435 2038811 := bstep (se 1 (by rfl) ⟨1529108, by rfl⟩ : syracuseStep 2038811 = 3058217) B3058217
theorem B13063157 : Blo 2037435 13063157 := bbase (se 5 (by rfl) ⟨612335, by rfl⟩ : syracuseStep 13063157 = 1224671) (by norm_num)
theorem B8708771 : Blo 2037435 8708771 := bstep (se 1 (by rfl) ⟨6531578, by rfl⟩ : syracuseStep 8708771 = 13063157) B13063157
theorem B5805847 : Blo 2037435 5805847 := bstep (se 1 (by rfl) ⟨4354385, by rfl⟩ : syracuseStep 5805847 = 8708771) B8708771
theorem B7741129 : Blo 2037435 7741129 := bstep (se 2 (by rfl) ⟨2902923, by rfl⟩ : syracuseStep 7741129 = 5805847) B5805847
theorem B10321505 : Blo 2037435 10321505 := bstep (se 2 (by rfl) ⟨3870564, by rfl⟩ : syracuseStep 10321505 = 7741129) B7741129
theorem B6881003 : Blo 2037435 6881003 := bstep (se 1 (by rfl) ⟨5160752, by rfl⟩ : syracuseStep 6881003 = 10321505) B10321505
theorem B4587335 : Blo 2037435 4587335 := bstep (se 1 (by rfl) ⟨3440501, by rfl⟩ : syracuseStep 4587335 = 6881003) B6881003
theorem B3058223 : Blo 2037435 3058223 := bstep (se 1 (by rfl) ⟨2293667, by rfl⟩ : syracuseStep 3058223 = 4587335) B4587335
theorem B2038815 : Blo 2037435 2038815 := bstep (se 1 (by rfl) ⟨1529111, by rfl⟩ : syracuseStep 2038815 = 3058223) B3058223
theorem B3058229 : Blo 2037435 3058229 := bbase (se 5 (by rfl) ⟨143354, by rfl⟩ : syracuseStep 3058229 = 286709) (by norm_num)
theorem B2038819 : Blo 2037435 2038819 := bstep (se 1 (by rfl) ⟨1529114, by rfl⟩ : syracuseStep 2038819 = 3058229) B3058229
theorem B5160773 : Blo 2037435 5160773 := bbase (se 4 (by rfl) ⟨483822, by rfl⟩ : syracuseStep 5160773 = 967645) (by norm_num)
theorem B3440515 : Blo 2037435 3440515 := bstep (se 1 (by rfl) ⟨2580386, by rfl⟩ : syracuseStep 3440515 = 5160773) B5160773
theorem B4587353 : Blo 2037435 4587353 := bstep (se 2 (by rfl) ⟨1720257, by rfl⟩ : syracuseStep 4587353 = 3440515) B3440515
theorem B3058235 : Blo 2037435 3058235 := bstep (se 1 (by rfl) ⟨2293676, by rfl⟩ : syracuseStep 3058235 = 4587353) B4587353
theorem B2038823 : Blo 2037435 2038823 := bstep (se 1 (by rfl) ⟨1529117, by rfl⟩ : syracuseStep 2038823 = 3058235) B3058235
theorem B2293681 : Blo 2037435 2293681 := bbase (se 2 (by rfl) ⟨860130, by rfl⟩ : syracuseStep 2293681 = 1720261) (by norm_num)
theorem B3058241 : Blo 2037435 3058241 := bstep (se 2 (by rfl) ⟨1146840, by rfl⟩ : syracuseStep 3058241 = 2293681) B2293681
theorem B2038827 : Blo 2037435 2038827 := bstep (se 1 (by rfl) ⟨1529120, by rfl⟩ : syracuseStep 2038827 = 3058241) B3058241
theorem B5805893 : Blo 2037435 5805893 := bbase (se 4 (by rfl) ⟨544302, by rfl⟩ : syracuseStep 5805893 = 1088605) (by norm_num)
theorem B3870595 : Blo 2037435 3870595 := bstep (se 1 (by rfl) ⟨2902946, by rfl⟩ : syracuseStep 3870595 = 5805893) B5805893
theorem B5160793 : Blo 2037435 5160793 := bstep (se 2 (by rfl) ⟨1935297, by rfl⟩ : syracuseStep 5160793 = 3870595) B3870595
theorem B6881057 : Blo 2037435 6881057 := bstep (se 2 (by rfl) ⟨2580396, by rfl⟩ : syracuseStep 6881057 = 5160793) B5160793
theorem B4587371 : Blo 2037435 4587371 := bstep (se 1 (by rfl) ⟨3440528, by rfl⟩ : syracuseStep 4587371 = 6881057) B6881057
theorem B3058247 : Blo 2037435 3058247 := bstep (se 1 (by rfl) ⟨2293685, by rfl⟩ : syracuseStep 3058247 = 4587371) B4587371
theorem B2038831 : Blo 2037435 2038831 := bstep (se 1 (by rfl) ⟨1529123, by rfl⟩ : syracuseStep 2038831 = 3058247) B3058247
theorem B3058253 : Blo 2037435 3058253 := bbase (se 3 (by rfl) ⟨573422, by rfl⟩ : syracuseStep 3058253 = 1146845) (by norm_num)
theorem B2038835 : Blo 2037435 2038835 := bstep (se 1 (by rfl) ⟨1529126, by rfl⟩ : syracuseStep 2038835 = 3058253) B3058253
theorem B4587389 : Blo 2037435 4587389 := bbase (se 3 (by rfl) ⟨860135, by rfl⟩ : syracuseStep 4587389 = 1720271) (by norm_num)
theorem B3058259 : Blo 2037435 3058259 := bstep (se 1 (by rfl) ⟨2293694, by rfl⟩ : syracuseStep 3058259 = 4587389) B4587389
theorem B2038839 : Blo 2037435 2038839 := bstep (se 1 (by rfl) ⟨1529129, by rfl⟩ : syracuseStep 2038839 = 3058259) B3058259
theorem B3440549 : Blo 2037435 3440549 := bbase (se 4 (by rfl) ⟨322551, by rfl⟩ : syracuseStep 3440549 = 645103) (by norm_num)
theorem B2293699 : Blo 2037435 2293699 := bstep (se 1 (by rfl) ⟨1720274, by rfl⟩ : syracuseStep 2293699 = 3440549) B3440549
theorem B3058265 : Blo 2037435 3058265 := bstep (se 2 (by rfl) ⟨1146849, by rfl⟩ : syracuseStep 3058265 = 2293699) B2293699
theorem B2038843 : Blo 2037435 2038843 := bstep (se 1 (by rfl) ⟨1529132, by rfl⟩ : syracuseStep 2038843 = 3058265) B3058265
theorem B2449381 : Blo 2037435 2449381 := bbase (se 4 (by rfl) ⟨229629, by rfl⟩ : syracuseStep 2449381 = 459259) (by norm_num)
theorem B3265841 : Blo 2037435 3265841 := bstep (se 2 (by rfl) ⟨1224690, by rfl⟩ : syracuseStep 3265841 = 2449381) B2449381
theorem B2177227 : Blo 2037435 2177227 := bstep (se 1 (by rfl) ⟨1632920, by rfl⟩ : syracuseStep 2177227 = 3265841) B3265841
theorem B2902969 : Blo 2037435 2902969 := bstep (se 2 (by rfl) ⟨1088613, by rfl⟩ : syracuseStep 2902969 = 2177227) B2177227
theorem B15482501 : Blo 2037435 15482501 := bstep (se 4 (by rfl) ⟨1451484, by rfl⟩ : syracuseStep 15482501 = 2902969) B2902969
theorem B10321667 : Blo 2037435 10321667 := bstep (se 1 (by rfl) ⟨7741250, by rfl⟩ : syracuseStep 10321667 = 15482501) B15482501
theorem B6881111 : Blo 2037435 6881111 := bstep (se 1 (by rfl) ⟨5160833, by rfl⟩ : syracuseStep 6881111 = 10321667) B10321667
theorem B4587407 : Blo 2037435 4587407 := bstep (se 1 (by rfl) ⟨3440555, by rfl⟩ : syracuseStep 4587407 = 6881111) B6881111
theorem B3058271 : Blo 2037435 3058271 := bstep (se 1 (by rfl) ⟨2293703, by rfl⟩ : syracuseStep 3058271 = 4587407) B4587407
theorem B2038847 : Blo 2037435 2038847 := bstep (se 1 (by rfl) ⟨1529135, by rfl⟩ : syracuseStep 2038847 = 3058271) B3058271
theorem B3058277 : Blo 2037435 3058277 := bbase (se 4 (by rfl) ⟨286713, by rfl⟩ : syracuseStep 3058277 = 573427) (by norm_num)
theorem B2038851 : Blo 2037435 2038851 := bstep (se 1 (by rfl) ⟨1529138, by rfl⟩ : syracuseStep 2038851 = 3058277) B3058277
theorem B2902981 : Blo 2037435 2902981 := bbase (se 4 (by rfl) ⟨272154, by rfl⟩ : syracuseStep 2902981 = 544309) (by norm_num)
theorem B3870641 : Blo 2037435 3870641 := bstep (se 2 (by rfl) ⟨1451490, by rfl⟩ : syracuseStep 3870641 = 2902981) B2902981
theorem B2580427 : Blo 2037435 2580427 := bstep (se 1 (by rfl) ⟨1935320, by rfl⟩ : syracuseStep 2580427 = 3870641) B3870641
theorem B3440569 : Blo 2037435 3440569 := bstep (se 2 (by rfl) ⟨1290213, by rfl⟩ : syracuseStep 3440569 = 2580427) B2580427
theorem B4587425 : Blo 2037435 4587425 := bstep (se 2 (by rfl) ⟨1720284, by rfl⟩ : syracuseStep 4587425 = 3440569) B3440569
theorem B3058283 : Blo 2037435 3058283 := bstep (se 1 (by rfl) ⟨2293712, by rfl⟩ : syracuseStep 3058283 = 4587425) B4587425
theorem B2038855 : Blo 2037435 2038855 := bstep (se 1 (by rfl) ⟨1529141, by rfl⟩ : syracuseStep 2038855 = 3058283) B3058283
theorem B2293717 : Blo 2037435 2293717 := bbase (se 7 (by rfl) ⟨26879, by rfl⟩ : syracuseStep 2293717 = 53759) (by norm_num)
theorem B3058289 : Blo 2037435 3058289 := bstep (se 2 (by rfl) ⟨1146858, by rfl⟩ : syracuseStep 3058289 = 2293717) B2293717
theorem B2038859 : Blo 2037435 2038859 := bstep (se 1 (by rfl) ⟨1529144, by rfl⟩ : syracuseStep 2038859 = 3058289) B3058289
theorem B2580437 : Blo 2037435 2580437 := bbase (se 7 (by rfl) ⟨30239, by rfl⟩ : syracuseStep 2580437 = 60479) (by norm_num)
theorem B6881165 : Blo 2037435 6881165 := bstep (se 3 (by rfl) ⟨1290218, by rfl⟩ : syracuseStep 6881165 = 2580437) B2580437
theorem B4587443 : Blo 2037435 4587443 := bstep (se 1 (by rfl) ⟨3440582, by rfl⟩ : syracuseStep 4587443 = 6881165) B6881165
theorem B3058295 : Blo 2037435 3058295 := bstep (se 1 (by rfl) ⟨2293721, by rfl⟩ : syracuseStep 3058295 = 4587443) B4587443
theorem B2038863 : Blo 2037435 2038863 := bstep (se 1 (by rfl) ⟨1529147, by rfl⟩ : syracuseStep 2038863 = 3058295) B3058295
theorem B3058301 : Blo 2037435 3058301 := bbase (se 3 (by rfl) ⟨573431, by rfl⟩ : syracuseStep 3058301 = 1146863) (by norm_num)
theorem B2038867 : Blo 2037435 2038867 := bstep (se 1 (by rfl) ⟨1529150, by rfl⟩ : syracuseStep 2038867 = 3058301) B3058301
theorem B4587461 : Blo 2037435 4587461 := bbase (se 4 (by rfl) ⟨430074, by rfl⟩ : syracuseStep 4587461 = 860149) (by norm_num)
theorem B3058307 : Blo 2037435 3058307 := bstep (se 1 (by rfl) ⟨2293730, by rfl⟩ : syracuseStep 3058307 = 4587461) B4587461
theorem B2038871 : Blo 2037435 2038871 := bstep (se 1 (by rfl) ⟨1529153, by rfl⟩ : syracuseStep 2038871 = 3058307) B3058307
theorem B8709029 : Blo 2037435 8709029 := bbase (se 4 (by rfl) ⟨816471, by rfl⟩ : syracuseStep 8709029 = 1632943) (by norm_num)
theorem B5806019 : Blo 2037435 5806019 := bstep (se 1 (by rfl) ⟨4354514, by rfl⟩ : syracuseStep 5806019 = 8709029) B8709029
theorem B3870679 : Blo 2037435 3870679 := bstep (se 1 (by rfl) ⟨2903009, by rfl⟩ : syracuseStep 3870679 = 5806019) B5806019
theorem B5160905 : Blo 2037435 5160905 := bstep (se 2 (by rfl) ⟨1935339, by rfl⟩ : syracuseStep 5160905 = 3870679) B3870679
theorem B3440603 : Blo 2037435 3440603 := bstep (se 1 (by rfl) ⟨2580452, by rfl⟩ : syracuseStep 3440603 = 5160905) B5160905
theorem B2293735 : Blo 2037435 2293735 := bstep (se 1 (by rfl) ⟨1720301, by rfl⟩ : syracuseStep 2293735 = 3440603) B3440603
theorem B3058313 : Blo 2037435 3058313 := bstep (se 2 (by rfl) ⟨1146867, by rfl⟩ : syracuseStep 3058313 = 2293735) B2293735
theorem B2038875 : Blo 2037435 2038875 := bstep (se 1 (by rfl) ⟨1529156, by rfl⟩ : syracuseStep 2038875 = 3058313) B3058313
theorem B10321829 : Blo 2037435 10321829 := bbase (se 4 (by rfl) ⟨967671, by rfl⟩ : syracuseStep 10321829 = 1935343) (by norm_num)
theorem B6881219 : Blo 2037435 6881219 := bstep (se 1 (by rfl) ⟨5160914, by rfl⟩ : syracuseStep 6881219 = 10321829) B10321829
theorem B4587479 : Blo 2037435 4587479 := bstep (se 1 (by rfl) ⟨3440609, by rfl⟩ : syracuseStep 4587479 = 6881219) B6881219
theorem B3058319 : Blo 2037435 3058319 := bstep (se 1 (by rfl) ⟨2293739, by rfl⟩ : syracuseStep 3058319 = 4587479) B4587479
theorem B2038879 : Blo 2037435 2038879 := bstep (se 1 (by rfl) ⟨1529159, by rfl⟩ : syracuseStep 2038879 = 3058319) B3058319
theorem B3058325 : Blo 2037435 3058325 := bbase (se 6 (by rfl) ⟨71679, by rfl⟩ : syracuseStep 3058325 = 143359) (by norm_num)
theorem B2038883 : Blo 2037435 2038883 := bstep (se 1 (by rfl) ⟨1529162, by rfl⟩ : syracuseStep 2038883 = 3058325) B3058325
theorem B3583381 : Blo 2037435 3583381 := bbase (se 6 (by rfl) ⟨83985, by rfl⟩ : syracuseStep 3583381 = 167971) (by norm_num)
theorem B4777841 : Blo 2037435 4777841 := bstep (se 2 (by rfl) ⟨1791690, by rfl⟩ : syracuseStep 4777841 = 3583381) B3583381
theorem B3185227 : Blo 2037435 3185227 := bstep (se 1 (by rfl) ⟨2388920, by rfl⟩ : syracuseStep 3185227 = 4777841) B4777841
theorem B16987877 : Blo 2037435 16987877 := bstep (se 4 (by rfl) ⟨1592613, by rfl⟩ : syracuseStep 16987877 = 3185227) B3185227
theorem B11325251 : Blo 2037435 11325251 := bstep (se 1 (by rfl) ⟨8493938, by rfl⟩ : syracuseStep 11325251 = 16987877) B16987877
theorem B7550167 : Blo 2037435 7550167 := bstep (se 1 (by rfl) ⟨5662625, by rfl⟩ : syracuseStep 7550167 = 11325251) B11325251
theorem B10066889 : Blo 2037435 10066889 := bstep (se 2 (by rfl) ⟨3775083, by rfl⟩ : syracuseStep 10066889 = 7550167) B7550167
theorem B26845037 : Blo 2037435 26845037 := bstep (se 3 (by rfl) ⟨5033444, by rfl⟩ : syracuseStep 26845037 = 10066889) B10066889
theorem B17896691 : Blo 2037435 17896691 := bstep (se 1 (by rfl) ⟨13422518, by rfl⟩ : syracuseStep 17896691 = 26845037) B26845037
theorem B47724509 : Blo 2037435 47724509 := bstep (se 3 (by rfl) ⟨8948345, by rfl⟩ : syracuseStep 47724509 = 17896691) B17896691
theorem B127265357 : Blo 2037435 127265357 := bstep (se 3 (by rfl) ⟨23862254, by rfl⟩ : syracuseStep 127265357 = 47724509) B47724509
theorem B339374285 : Blo 2037435 339374285 := bstep (se 3 (by rfl) ⟨63632678, by rfl⟩ : syracuseStep 339374285 = 127265357) B127265357
theorem B226249523 : Blo 2037435 226249523 := bstep (se 1 (by rfl) ⟨169687142, by rfl⟩ : syracuseStep 226249523 = 339374285) B339374285
theorem B150833015 : Blo 2037435 150833015 := bstep (se 1 (by rfl) ⟨113124761, by rfl⟩ : syracuseStep 150833015 = 226249523) B226249523
theorem B100555343 : Blo 2037435 100555343 := bstep (se 1 (by rfl) ⟨75416507, by rfl⟩ : syracuseStep 100555343 = 150833015) B150833015
theorem B67036895 : Blo 2037435 67036895 := bstep (se 1 (by rfl) ⟨50277671, by rfl⟩ : syracuseStep 67036895 = 100555343) B100555343
theorem B44691263 : Blo 2037435 44691263 := bstep (se 1 (by rfl) ⟨33518447, by rfl⟩ : syracuseStep 44691263 = 67036895) B67036895
theorem B29794175 : Blo 2037435 29794175 := bstep (se 1 (by rfl) ⟨22345631, by rfl⟩ : syracuseStep 29794175 = 44691263) B44691263
theorem B19862783 : Blo 2037435 19862783 := bstep (se 1 (by rfl) ⟨14897087, by rfl⟩ : syracuseStep 19862783 = 29794175) B29794175
theorem B13241855 : Blo 2037435 13241855 := bstep (se 1 (by rfl) ⟨9931391, by rfl⟩ : syracuseStep 13241855 = 19862783) B19862783
theorem B8827903 : Blo 2037435 8827903 := bstep (se 1 (by rfl) ⟨6620927, by rfl⟩ : syracuseStep 8827903 = 13241855) B13241855
theorem B11770537 : Blo 2037435 11770537 := bstep (se 2 (by rfl) ⟨4413951, by rfl⟩ : syracuseStep 11770537 = 8827903) B8827903
theorem B15694049 : Blo 2037435 15694049 := bstep (se 2 (by rfl) ⟨5885268, by rfl⟩ : syracuseStep 15694049 = 11770537) B11770537
theorem B10462699 : Blo 2037435 10462699 := bstep (se 1 (by rfl) ⟨7847024, by rfl⟩ : syracuseStep 10462699 = 15694049) B15694049
theorem B13950265 : Blo 2037435 13950265 := bstep (se 2 (by rfl) ⟨5231349, by rfl⟩ : syracuseStep 13950265 = 10462699) B10462699
theorem B18600353 : Blo 2037435 18600353 := bstep (se 2 (by rfl) ⟨6975132, by rfl⟩ : syracuseStep 18600353 = 13950265) B13950265
theorem B12400235 : Blo 2037435 12400235 := bstep (se 1 (by rfl) ⟨9300176, by rfl⟩ : syracuseStep 12400235 = 18600353) B18600353
theorem B8266823 : Blo 2037435 8266823 := bstep (se 1 (by rfl) ⟨6200117, by rfl⟩ : syracuseStep 8266823 = 12400235) B12400235
theorem B5511215 : Blo 2037435 5511215 := bstep (se 1 (by rfl) ⟨4133411, by rfl⟩ : syracuseStep 5511215 = 8266823) B8266823
theorem B3674143 : Blo 2037435 3674143 := bstep (se 1 (by rfl) ⟨2755607, by rfl⟩ : syracuseStep 3674143 = 5511215) B5511215
theorem B19595429 : Blo 2037435 19595429 := bstep (se 4 (by rfl) ⟨1837071, by rfl⟩ : syracuseStep 19595429 = 3674143) B3674143
theorem B13063619 : Blo 2037435 13063619 := bstep (se 1 (by rfl) ⟨9797714, by rfl⟩ : syracuseStep 13063619 = 19595429) B19595429
theorem B8709079 : Blo 2037435 8709079 := bstep (se 1 (by rfl) ⟨6531809, by rfl⟩ : syracuseStep 8709079 = 13063619) B13063619
theorem B11612105 : Blo 2037435 11612105 := bstep (se 2 (by rfl) ⟨4354539, by rfl⟩ : syracuseStep 11612105 = 8709079) B8709079
theorem B7741403 : Blo 2037435 7741403 := bstep (se 1 (by rfl) ⟨5806052, by rfl⟩ : syracuseStep 7741403 = 11612105) B11612105
theorem B5160935 : Blo 2037435 5160935 := bstep (se 1 (by rfl) ⟨3870701, by rfl⟩ : syracuseStep 5160935 = 7741403) B7741403
theorem B3440623 : Blo 2037435 3440623 := bstep (se 1 (by rfl) ⟨2580467, by rfl⟩ : syracuseStep 3440623 = 5160935) B5160935
theorem B4587497 : Blo 2037435 4587497 := bstep (se 2 (by rfl) ⟨1720311, by rfl⟩ : syracuseStep 4587497 = 3440623) B3440623
theorem B3058331 : Blo 2037435 3058331 := bstep (se 1 (by rfl) ⟨2293748, by rfl⟩ : syracuseStep 3058331 = 4587497) B4587497
theorem B2038887 : Blo 2037435 2038887 := bstep (se 1 (by rfl) ⟨1529165, by rfl⟩ : syracuseStep 2038887 = 3058331) B3058331
theorem B2293753 : Blo 2037435 2293753 := bbase (se 2 (by rfl) ⟨860157, by rfl⟩ : syracuseStep 2293753 = 1720315) (by norm_num)
theorem B3058337 : Blo 2037435 3058337 := bstep (se 2 (by rfl) ⟨1146876, by rfl⟩ : syracuseStep 3058337 = 2293753) B2293753
theorem B2038891 : Blo 2037435 2038891 := bstep (se 1 (by rfl) ⟨1529168, by rfl⟩ : syracuseStep 2038891 = 3058337) B3058337
theorem B9931429 : Blo 2037435 9931429 := bbase (se 4 (by rfl) ⟨931071, by rfl⟩ : syracuseStep 9931429 = 1862143) (by norm_num)
theorem B52967621 : Blo 2037435 52967621 := bstep (se 4 (by rfl) ⟨4965714, by rfl⟩ : syracuseStep 52967621 = 9931429) B9931429
theorem B35311747 : Blo 2037435 35311747 := bstep (se 1 (by rfl) ⟨26483810, by rfl⟩ : syracuseStep 35311747 = 52967621) B52967621
theorem B47082329 : Blo 2037435 47082329 := bstep (se 2 (by rfl) ⟨17655873, by rfl⟩ : syracuseStep 47082329 = 35311747) B35311747
theorem B31388219 : Blo 2037435 31388219 := bstep (se 1 (by rfl) ⟨23541164, by rfl⟩ : syracuseStep 31388219 = 47082329) B47082329
theorem B20925479 : Blo 2037435 20925479 := bstep (se 1 (by rfl) ⟨15694109, by rfl⟩ : syracuseStep 20925479 = 31388219) B31388219
theorem B13950319 : Blo 2037435 13950319 := bstep (se 1 (by rfl) ⟨10462739, by rfl⟩ : syracuseStep 13950319 = 20925479) B20925479
theorem B18600425 : Blo 2037435 18600425 := bstep (se 2 (by rfl) ⟨6975159, by rfl⟩ : syracuseStep 18600425 = 13950319) B13950319
theorem B12400283 : Blo 2037435 12400283 := bstep (se 1 (by rfl) ⟨9300212, by rfl⟩ : syracuseStep 12400283 = 18600425) B18600425
theorem B8266855 : Blo 2037435 8266855 := bstep (se 1 (by rfl) ⟨6200141, by rfl⟩ : syracuseStep 8266855 = 12400283) B12400283
theorem B11022473 : Blo 2037435 11022473 := bstep (se 2 (by rfl) ⟨4133427, by rfl⟩ : syracuseStep 11022473 = 8266855) B8266855
theorem B7348315 : Blo 2037435 7348315 := bstep (se 1 (by rfl) ⟨5511236, by rfl⟩ : syracuseStep 7348315 = 11022473) B11022473
theorem B9797753 : Blo 2037435 9797753 := bstep (se 2 (by rfl) ⟨3674157, by rfl⟩ : syracuseStep 9797753 = 7348315) B7348315
theorem B6531835 : Blo 2037435 6531835 := bstep (se 1 (by rfl) ⟨4898876, by rfl⟩ : syracuseStep 6531835 = 9797753) B9797753
theorem B8709113 : Blo 2037435 8709113 := bstep (se 2 (by rfl) ⟨3265917, by rfl⟩ : syracuseStep 8709113 = 6531835) B6531835
theorem B5806075 : Blo 2037435 5806075 := bstep (se 1 (by rfl) ⟨4354556, by rfl⟩ : syracuseStep 5806075 = 8709113) B8709113
theorem B7741433 : Blo 2037435 7741433 := bstep (se 2 (by rfl) ⟨2903037, by rfl⟩ : syracuseStep 7741433 = 5806075) B5806075
theorem B5160955 : Blo 2037435 5160955 := bstep (se 1 (by rfl) ⟨3870716, by rfl⟩ : syracuseStep 5160955 = 7741433) B7741433
theorem B6881273 : Blo 2037435 6881273 := bstep (se 2 (by rfl) ⟨2580477, by rfl⟩ : syracuseStep 6881273 = 5160955) B5160955
theorem B4587515 : Blo 2037435 4587515 := bstep (se 1 (by rfl) ⟨3440636, by rfl⟩ : syracuseStep 4587515 = 6881273) B6881273
theorem B3058343 : Blo 2037435 3058343 := bstep (se 1 (by rfl) ⟨2293757, by rfl⟩ : syracuseStep 3058343 = 4587515) B4587515
theorem B2038895 : Blo 2037435 2038895 := bstep (se 1 (by rfl) ⟨1529171, by rfl⟩ : syracuseStep 2038895 = 3058343) B3058343
theorem B3058349 : Blo 2037435 3058349 := bbase (se 3 (by rfl) ⟨573440, by rfl⟩ : syracuseStep 3058349 = 1146881) (by norm_num)
theorem B2038899 : Blo 2037435 2038899 := bstep (se 1 (by rfl) ⟨1529174, by rfl⟩ : syracuseStep 2038899 = 3058349) B3058349
theorem B4587533 : Blo 2037435 4587533 := bbase (se 3 (by rfl) ⟨860162, by rfl⟩ : syracuseStep 4587533 = 1720325) (by norm_num)
theorem B3058355 : Blo 2037435 3058355 := bstep (se 1 (by rfl) ⟨2293766, by rfl⟩ : syracuseStep 3058355 = 4587533) B4587533
theorem B2038903 : Blo 2037435 2038903 := bstep (se 1 (by rfl) ⟨1529177, by rfl⟩ : syracuseStep 2038903 = 3058355) B3058355
theorem B2580493 : Blo 2037435 2580493 := bbase (se 3 (by rfl) ⟨483842, by rfl⟩ : syracuseStep 2580493 = 967685) (by norm_num)
theorem B3440657 : Blo 2037435 3440657 := bstep (se 2 (by rfl) ⟨1290246, by rfl⟩ : syracuseStep 3440657 = 2580493) B2580493
theorem B2293771 : Blo 2037435 2293771 := bstep (se 1 (by rfl) ⟨1720328, by rfl⟩ : syracuseStep 2293771 = 3440657) B3440657
theorem B3058361 : Blo 2037435 3058361 := bstep (se 2 (by rfl) ⟨1146885, by rfl⟩ : syracuseStep 3058361 = 2293771) B2293771
theorem B2038907 : Blo 2037435 2038907 := bstep (se 1 (by rfl) ⟨1529180, by rfl⟩ : syracuseStep 2038907 = 3058361) B3058361
theorem B15694229 : Blo 2037435 15694229 := bbase (se 6 (by rfl) ⟨367833, by rfl⟩ : syracuseStep 15694229 = 735667) (by norm_num)
theorem B10462819 : Blo 2037435 10462819 := bstep (se 1 (by rfl) ⟨7847114, by rfl⟩ : syracuseStep 10462819 = 15694229) B15694229
theorem B13950425 : Blo 2037435 13950425 := bstep (se 2 (by rfl) ⟨5231409, by rfl⟩ : syracuseStep 13950425 = 10462819) B10462819
theorem B37201133 : Blo 2037435 37201133 := bstep (se 3 (by rfl) ⟨6975212, by rfl⟩ : syracuseStep 37201133 = 13950425) B13950425
theorem B24800755 : Blo 2037435 24800755 := bstep (se 1 (by rfl) ⟨18600566, by rfl⟩ : syracuseStep 24800755 = 37201133) B37201133
theorem B33067673 : Blo 2037435 33067673 := bstep (se 2 (by rfl) ⟨12400377, by rfl⟩ : syracuseStep 33067673 = 24800755) B24800755
theorem B22045115 : Blo 2037435 22045115 := bstep (se 1 (by rfl) ⟨16533836, by rfl⟩ : syracuseStep 22045115 = 33067673) B33067673
theorem B14696743 : Blo 2037435 14696743 := bstep (se 1 (by rfl) ⟨11022557, by rfl⟩ : syracuseStep 14696743 = 22045115) B22045115
theorem B19595657 : Blo 2037435 19595657 := bstep (se 2 (by rfl) ⟨7348371, by rfl⟩ : syracuseStep 19595657 = 14696743) B14696743
theorem B13063771 : Blo 2037435 13063771 := bstep (se 1 (by rfl) ⟨9797828, by rfl⟩ : syracuseStep 13063771 = 19595657) B19595657
theorem B17418361 : Blo 2037435 17418361 := bstep (se 2 (by rfl) ⟨6531885, by rfl⟩ : syracuseStep 17418361 = 13063771) B13063771
theorem B23224481 : Blo 2037435 23224481 := bstep (se 2 (by rfl) ⟨8709180, by rfl⟩ : syracuseStep 23224481 = 17418361) B17418361
theorem B15482987 : Blo 2037435 15482987 := bstep (se 1 (by rfl) ⟨11612240, by rfl⟩ : syracuseStep 15482987 = 23224481) B23224481
theorem B10321991 : Blo 2037435 10321991 := bstep (se 1 (by rfl) ⟨7741493, by rfl⟩ : syracuseStep 10321991 = 15482987) B15482987
theorem B6881327 : Blo 2037435 6881327 := bstep (se 1 (by rfl) ⟨5160995, by rfl⟩ : syracuseStep 6881327 = 10321991) B10321991
theorem B4587551 : Blo 2037435 4587551 := bstep (se 1 (by rfl) ⟨3440663, by rfl⟩ : syracuseStep 4587551 = 6881327) B6881327
theorem B3058367 : Blo 2037435 3058367 := bstep (se 1 (by rfl) ⟨2293775, by rfl⟩ : syracuseStep 3058367 = 4587551) B4587551
theorem B2038911 : Blo 2037435 2038911 := bstep (se 1 (by rfl) ⟨1529183, by rfl⟩ : syracuseStep 2038911 = 3058367) B3058367
theorem B3058373 : Blo 2037435 3058373 := bbase (se 4 (by rfl) ⟨286722, by rfl⟩ : syracuseStep 3058373 = 573445) (by norm_num)
theorem B2038915 : Blo 2037435 2038915 := bstep (se 1 (by rfl) ⟨1529186, by rfl⟩ : syracuseStep 2038915 = 3058373) B3058373
theorem B3440677 : Blo 2037435 3440677 := bbase (se 4 (by rfl) ⟨322563, by rfl⟩ : syracuseStep 3440677 = 645127) (by norm_num)
theorem B4587569 : Blo 2037435 4587569 := bstep (se 2 (by rfl) ⟨1720338, by rfl⟩ : syracuseStep 4587569 = 3440677) B3440677
theorem B3058379 : Blo 2037435 3058379 := bstep (se 1 (by rfl) ⟨2293784, by rfl⟩ : syracuseStep 3058379 = 4587569) B4587569
theorem B2038919 : Blo 2037435 2038919 := bstep (se 1 (by rfl) ⟨1529189, by rfl⟩ : syracuseStep 2038919 = 3058379) B3058379
theorem B2293789 : Blo 2037435 2293789 := bbase (se 3 (by rfl) ⟨430085, by rfl⟩ : syracuseStep 2293789 = 860171) (by norm_num)
theorem B3058385 : Blo 2037435 3058385 := bstep (se 2 (by rfl) ⟨1146894, by rfl⟩ : syracuseStep 3058385 = 2293789) B2293789
theorem B2038923 : Blo 2037435 2038923 := bstep (se 1 (by rfl) ⟨1529192, by rfl⟩ : syracuseStep 2038923 = 3058385) B3058385
theorem B6881381 : Blo 2037435 6881381 := bbase (se 4 (by rfl) ⟨645129, by rfl⟩ : syracuseStep 6881381 = 1290259) (by norm_num)
theorem B4587587 : Blo 2037435 4587587 := bstep (se 1 (by rfl) ⟨3440690, by rfl⟩ : syracuseStep 4587587 = 6881381) B6881381
theorem B3058391 : Blo 2037435 3058391 := bstep (se 1 (by rfl) ⟨2293793, by rfl⟩ : syracuseStep 3058391 = 4587587) B4587587
theorem B2038927 : Blo 2037435 2038927 := bstep (se 1 (by rfl) ⟨1529195, by rfl⟩ : syracuseStep 2038927 = 3058391) B3058391
theorem B3058397 : Blo 2037435 3058397 := bbase (se 3 (by rfl) ⟨573449, by rfl⟩ : syracuseStep 3058397 = 1146899) (by norm_num)
theorem B2038931 : Blo 2037435 2038931 := bstep (se 1 (by rfl) ⟨1529198, by rfl⟩ : syracuseStep 2038931 = 3058397) B3058397
theorem B4587605 : Blo 2037435 4587605 := bbase (se 8 (by rfl) ⟨26880, by rfl⟩ : syracuseStep 4587605 = 53761) (by norm_num)
theorem B3058403 : Blo 2037435 3058403 := bstep (se 1 (by rfl) ⟨2293802, by rfl⟩ : syracuseStep 3058403 = 4587605) B4587605
theorem B2038935 : Blo 2037435 2038935 := bstep (se 1 (by rfl) ⟨1529201, by rfl⟩ : syracuseStep 2038935 = 3058403) B3058403
theorem B42422869 : Blo 2037435 42422869 := bbase (se 8 (by rfl) ⟨248571, by rfl⟩ : syracuseStep 42422869 = 497143) (by norm_num)
theorem B226255301 : Blo 2037435 226255301 := bstep (se 4 (by rfl) ⟨21211434, by rfl⟩ : syracuseStep 226255301 = 42422869) B42422869
theorem B150836867 : Blo 2037435 150836867 := bstep (se 1 (by rfl) ⟨113127650, by rfl⟩ : syracuseStep 150836867 = 226255301) B226255301
theorem B100557911 : Blo 2037435 100557911 := bstep (se 1 (by rfl) ⟨75418433, by rfl⟩ : syracuseStep 100557911 = 150836867) B150836867
theorem B67038607 : Blo 2037435 67038607 := bstep (se 1 (by rfl) ⟨50278955, by rfl⟩ : syracuseStep 67038607 = 100557911) B100557911
theorem B89384809 : Blo 2037435 89384809 := bstep (se 2 (by rfl) ⟨33519303, by rfl⟩ : syracuseStep 89384809 = 67038607) B67038607
theorem B119179745 : Blo 2037435 119179745 := bstep (se 2 (by rfl) ⟨44692404, by rfl⟩ : syracuseStep 119179745 = 89384809) B89384809
theorem B79453163 : Blo 2037435 79453163 := bstep (se 1 (by rfl) ⟨59589872, by rfl⟩ : syracuseStep 79453163 = 119179745) B119179745
theorem B52968775 : Blo 2037435 52968775 := bstep (se 1 (by rfl) ⟨39726581, by rfl⟩ : syracuseStep 52968775 = 79453163) B79453163
theorem B70625033 : Blo 2037435 70625033 := bstep (se 2 (by rfl) ⟨26484387, by rfl⟩ : syracuseStep 70625033 = 52968775) B52968775
theorem B47083355 : Blo 2037435 47083355 := bstep (se 1 (by rfl) ⟨35312516, by rfl⟩ : syracuseStep 47083355 = 70625033) B70625033
theorem B31388903 : Blo 2037435 31388903 := bstep (se 1 (by rfl) ⟨23541677, by rfl⟩ : syracuseStep 31388903 = 47083355) B47083355
theorem B20925935 : Blo 2037435 20925935 := bstep (se 1 (by rfl) ⟨15694451, by rfl⟩ : syracuseStep 20925935 = 31388903) B31388903
theorem B13950623 : Blo 2037435 13950623 := bstep (se 1 (by rfl) ⟨10462967, by rfl⟩ : syracuseStep 13950623 = 20925935) B20925935
theorem B9300415 : Blo 2037435 9300415 := bstep (se 1 (by rfl) ⟨6975311, by rfl⟩ : syracuseStep 9300415 = 13950623) B13950623
theorem B12400553 : Blo 2037435 12400553 := bstep (se 2 (by rfl) ⟨4650207, by rfl⟩ : syracuseStep 12400553 = 9300415) B9300415
theorem B8267035 : Blo 2037435 8267035 := bstep (se 1 (by rfl) ⟨6200276, by rfl⟩ : syracuseStep 8267035 = 12400553) B12400553
theorem B11022713 : Blo 2037435 11022713 := bstep (se 2 (by rfl) ⟨4133517, by rfl⟩ : syracuseStep 11022713 = 8267035) B8267035
theorem B7348475 : Blo 2037435 7348475 := bstep (se 1 (by rfl) ⟨5511356, by rfl⟩ : syracuseStep 7348475 = 11022713) B11022713
theorem B4898983 : Blo 2037435 4898983 := bstep (se 1 (by rfl) ⟨3674237, by rfl⟩ : syracuseStep 4898983 = 7348475) B7348475
theorem B6531977 : Blo 2037435 6531977 := bstep (se 2 (by rfl) ⟨2449491, by rfl⟩ : syracuseStep 6531977 = 4898983) B4898983
theorem B4354651 : Blo 2037435 4354651 := bstep (se 1 (by rfl) ⟨3265988, by rfl⟩ : syracuseStep 4354651 = 6531977) B6531977
theorem B5806201 : Blo 2037435 5806201 := bstep (se 2 (by rfl) ⟨2177325, by rfl⟩ : syracuseStep 5806201 = 4354651) B4354651
theorem B7741601 : Blo 2037435 7741601 := bstep (se 2 (by rfl) ⟨2903100, by rfl⟩ : syracuseStep 7741601 = 5806201) B5806201
theorem B5161067 : Blo 2037435 5161067 := bstep (se 1 (by rfl) ⟨3870800, by rfl⟩ : syracuseStep 5161067 = 7741601) B7741601
theorem B3440711 : Blo 2037435 3440711 := bstep (se 1 (by rfl) ⟨2580533, by rfl⟩ : syracuseStep 3440711 = 5161067) B5161067
theorem B2293807 : Blo 2037435 2293807 := bstep (se 1 (by rfl) ⟨1720355, by rfl⟩ : syracuseStep 2293807 = 3440711) B3440711
theorem B3058409 : Blo 2037435 3058409 := bstep (se 2 (by rfl) ⟨1146903, by rfl⟩ : syracuseStep 3058409 = 2293807) B2293807
theorem B2038939 : Blo 2037435 2038939 := bstep (se 1 (by rfl) ⟨1529204, by rfl⟩ : syracuseStep 2038939 = 3058409) B3058409
theorem B4713661 : Blo 2037435 4713661 := bbase (se 3 (by rfl) ⟨883811, by rfl⟩ : syracuseStep 4713661 = 1767623) (by norm_num)
theorem B6284881 : Blo 2037435 6284881 := bstep (se 2 (by rfl) ⟨2356830, by rfl⟩ : syracuseStep 6284881 = 4713661) B4713661
theorem B33519365 : Blo 2037435 33519365 := bstep (se 4 (by rfl) ⟨3142440, by rfl⟩ : syracuseStep 33519365 = 6284881) B6284881
theorem B22346243 : Blo 2037435 22346243 := bstep (se 1 (by rfl) ⟨16759682, by rfl⟩ : syracuseStep 22346243 = 33519365) B33519365
theorem B14897495 : Blo 2037435 14897495 := bstep (se 1 (by rfl) ⟨11173121, by rfl⟩ : syracuseStep 14897495 = 22346243) B22346243
theorem B9931663 : Blo 2037435 9931663 := bstep (se 1 (by rfl) ⟨7448747, by rfl⟩ : syracuseStep 9931663 = 14897495) B14897495
theorem B13242217 : Blo 2037435 13242217 := bstep (se 2 (by rfl) ⟨4965831, by rfl⟩ : syracuseStep 13242217 = 9931663) B9931663
theorem B17656289 : Blo 2037435 17656289 := bstep (se 2 (by rfl) ⟨6621108, by rfl⟩ : syracuseStep 17656289 = 13242217) B13242217
theorem B11770859 : Blo 2037435 11770859 := bstep (se 1 (by rfl) ⟨8828144, by rfl⟩ : syracuseStep 11770859 = 17656289) B17656289
theorem B7847239 : Blo 2037435 7847239 := bstep (se 1 (by rfl) ⟨5885429, by rfl⟩ : syracuseStep 7847239 = 11770859) B11770859
theorem B10462985 : Blo 2037435 10462985 := bstep (se 2 (by rfl) ⟨3923619, by rfl⟩ : syracuseStep 10462985 = 7847239) B7847239
theorem B6975323 : Blo 2037435 6975323 := bstep (se 1 (by rfl) ⟨5231492, by rfl⟩ : syracuseStep 6975323 = 10462985) B10462985
theorem B4650215 : Blo 2037435 4650215 := bstep (se 1 (by rfl) ⟨3487661, by rfl⟩ : syracuseStep 4650215 = 6975323) B6975323
theorem B12400573 : Blo 2037435 12400573 := bstep (se 3 (by rfl) ⟨2325107, by rfl⟩ : syracuseStep 12400573 = 4650215) B4650215
theorem B16534097 : Blo 2037435 16534097 := bstep (se 2 (by rfl) ⟨6200286, by rfl⟩ : syracuseStep 16534097 = 12400573) B12400573
theorem B11022731 : Blo 2037435 11022731 := bstep (se 1 (by rfl) ⟨8267048, by rfl⟩ : syracuseStep 11022731 = 16534097) B16534097
theorem B7348487 : Blo 2037435 7348487 := bstep (se 1 (by rfl) ⟨5511365, by rfl⟩ : syracuseStep 7348487 = 11022731) B11022731
theorem B19595965 : Blo 2037435 19595965 := bstep (se 3 (by rfl) ⟨3674243, by rfl⟩ : syracuseStep 19595965 = 7348487) B7348487
theorem B26127953 : Blo 2037435 26127953 := bstep (se 2 (by rfl) ⟨9797982, by rfl⟩ : syracuseStep 26127953 = 19595965) B19595965
theorem B17418635 : Blo 2037435 17418635 := bstep (se 1 (by rfl) ⟨13063976, by rfl⟩ : syracuseStep 17418635 = 26127953) B26127953
theorem B11612423 : Blo 2037435 11612423 := bstep (se 1 (by rfl) ⟨8709317, by rfl⟩ : syracuseStep 11612423 = 17418635) B17418635
theorem B7741615 : Blo 2037435 7741615 := bstep (se 1 (by rfl) ⟨5806211, by rfl⟩ : syracuseStep 7741615 = 11612423) B11612423
theorem B10322153 : Blo 2037435 10322153 := bstep (se 2 (by rfl) ⟨3870807, by rfl⟩ : syracuseStep 10322153 = 7741615) B7741615
theorem B6881435 : Blo 2037435 6881435 := bstep (se 1 (by rfl) ⟨5161076, by rfl⟩ : syracuseStep 6881435 = 10322153) B10322153
theorem B4587623 : Blo 2037435 4587623 := bstep (se 1 (by rfl) ⟨3440717, by rfl⟩ : syracuseStep 4587623 = 6881435) B6881435
theorem B3058415 : Blo 2037435 3058415 := bstep (se 1 (by rfl) ⟨2293811, by rfl⟩ : syracuseStep 3058415 = 4587623) B4587623
theorem B2038943 : Blo 2037435 2038943 := bstep (se 1 (by rfl) ⟨1529207, by rfl⟩ : syracuseStep 2038943 = 3058415) B3058415
theorem B3058421 : Blo 2037435 3058421 := bbase (se 5 (by rfl) ⟨143363, by rfl⟩ : syracuseStep 3058421 = 286727) (by norm_num)
theorem B2038947 : Blo 2037435 2038947 := bstep (se 1 (by rfl) ⟨1529210, by rfl⟩ : syracuseStep 2038947 = 3058421) B3058421
theorem B16534165 : Blo 2037435 16534165 := bbase (se 6 (by rfl) ⟨387519, by rfl⟩ : syracuseStep 16534165 = 775039) (by norm_num)
theorem B22045553 : Blo 2037435 22045553 := bstep (se 2 (by rfl) ⟨8267082, by rfl⟩ : syracuseStep 22045553 = 16534165) B16534165
theorem B14697035 : Blo 2037435 14697035 := bstep (se 1 (by rfl) ⟨11022776, by rfl⟩ : syracuseStep 14697035 = 22045553) B22045553
theorem B9798023 : Blo 2037435 9798023 := bstep (se 1 (by rfl) ⟨7348517, by rfl⟩ : syracuseStep 9798023 = 14697035) B14697035
theorem B6532015 : Blo 2037435 6532015 := bstep (se 1 (by rfl) ⟨4899011, by rfl⟩ : syracuseStep 6532015 = 9798023) B9798023
theorem B8709353 : Blo 2037435 8709353 := bstep (se 2 (by rfl) ⟨3266007, by rfl⟩ : syracuseStep 8709353 = 6532015) B6532015
theorem B5806235 : Blo 2037435 5806235 := bstep (se 1 (by rfl) ⟨4354676, by rfl⟩ : syracuseStep 5806235 = 8709353) B8709353
theorem B3870823 : Blo 2037435 3870823 := bstep (se 1 (by rfl) ⟨2903117, by rfl⟩ : syracuseStep 3870823 = 5806235) B5806235
theorem B5161097 : Blo 2037435 5161097 := bstep (se 2 (by rfl) ⟨1935411, by rfl⟩ : syracuseStep 5161097 = 3870823) B3870823
theorem B3440731 : Blo 2037435 3440731 := bstep (se 1 (by rfl) ⟨2580548, by rfl⟩ : syracuseStep 3440731 = 5161097) B5161097
theorem B4587641 : Blo 2037435 4587641 := bstep (se 2 (by rfl) ⟨1720365, by rfl⟩ : syracuseStep 4587641 = 3440731) B3440731
theorem B3058427 : Blo 2037435 3058427 := bstep (se 1 (by rfl) ⟨2293820, by rfl⟩ : syracuseStep 3058427 = 4587641) B4587641
theorem B2038951 : Blo 2037435 2038951 := bstep (se 1 (by rfl) ⟨1529213, by rfl⟩ : syracuseStep 2038951 = 3058427) B3058427
theorem B2293825 : Blo 2037435 2293825 := bbase (se 2 (by rfl) ⟨860184, by rfl⟩ : syracuseStep 2293825 = 1720369) (by norm_num)
theorem B3058433 : Blo 2037435 3058433 := bstep (se 2 (by rfl) ⟨1146912, by rfl⟩ : syracuseStep 3058433 = 2293825) B2293825
theorem B2038955 : Blo 2037435 2038955 := bstep (se 1 (by rfl) ⟨1529216, by rfl⟩ : syracuseStep 2038955 = 3058433) B3058433
theorem B5161117 : Blo 2037435 5161117 := bbase (se 3 (by rfl) ⟨967709, by rfl⟩ : syracuseStep 5161117 = 1935419) (by norm_num)
theorem B6881489 : Blo 2037435 6881489 := bstep (se 2 (by rfl) ⟨2580558, by rfl⟩ : syracuseStep 6881489 = 5161117) B5161117
theorem B4587659 : Blo 2037435 4587659 := bstep (se 1 (by rfl) ⟨3440744, by rfl⟩ : syracuseStep 4587659 = 6881489) B6881489
theorem B3058439 : Blo 2037435 3058439 := bstep (se 1 (by rfl) ⟨2293829, by rfl⟩ : syracuseStep 3058439 = 4587659) B4587659
theorem B2038959 : Blo 2037435 2038959 := bstep (se 1 (by rfl) ⟨1529219, by rfl⟩ : syracuseStep 2038959 = 3058439) B3058439
theorem B3058445 : Blo 2037435 3058445 := bbase (se 3 (by rfl) ⟨573458, by rfl⟩ : syracuseStep 3058445 = 1146917) (by norm_num)
theorem B2038963 : Blo 2037435 2038963 := bstep (se 1 (by rfl) ⟨1529222, by rfl⟩ : syracuseStep 2038963 = 3058445) B3058445
theorem B4587677 : Blo 2037435 4587677 := bbase (se 3 (by rfl) ⟨860189, by rfl⟩ : syracuseStep 4587677 = 1720379) (by norm_num)
theorem B3058451 : Blo 2037435 3058451 := bstep (se 1 (by rfl) ⟨2293838, by rfl⟩ : syracuseStep 3058451 = 4587677) B4587677
theorem B2038967 : Blo 2037435 2038967 := bstep (se 1 (by rfl) ⟨1529225, by rfl⟩ : syracuseStep 2038967 = 3058451) B3058451
theorem B3440765 : Blo 2037435 3440765 := bbase (se 3 (by rfl) ⟨645143, by rfl⟩ : syracuseStep 3440765 = 1290287) (by norm_num)
theorem B2293843 : Blo 2037435 2293843 := bstep (se 1 (by rfl) ⟨1720382, by rfl⟩ : syracuseStep 2293843 = 3440765) B3440765
theorem B3058457 : Blo 2037435 3058457 := bstep (se 2 (by rfl) ⟨1146921, by rfl⟩ : syracuseStep 3058457 = 2293843) B2293843
theorem B2038971 : Blo 2037435 2038971 := bstep (se 1 (by rfl) ⟨1529228, by rfl⟩ : syracuseStep 2038971 = 3058457) B3058457
theorem B11173301 : Blo 2037435 11173301 := bbase (se 5 (by rfl) ⟨523748, by rfl⟩ : syracuseStep 11173301 = 1047497) (by norm_num)
theorem B7448867 : Blo 2037435 7448867 := bstep (se 1 (by rfl) ⟨5586650, by rfl⟩ : syracuseStep 7448867 = 11173301) B11173301
theorem B4965911 : Blo 2037435 4965911 := bstep (se 1 (by rfl) ⟨3724433, by rfl⟩ : syracuseStep 4965911 = 7448867) B7448867
theorem B3310607 : Blo 2037435 3310607 := bstep (se 1 (by rfl) ⟨2482955, by rfl⟩ : syracuseStep 3310607 = 4965911) B4965911
theorem B2207071 : Blo 2037435 2207071 := bstep (se 1 (by rfl) ⟨1655303, by rfl⟩ : syracuseStep 2207071 = 3310607) B3310607
theorem B11771045 : Blo 2037435 11771045 := bstep (se 4 (by rfl) ⟨1103535, by rfl⟩ : syracuseStep 11771045 = 2207071) B2207071
theorem B7847363 : Blo 2037435 7847363 := bstep (se 1 (by rfl) ⟨5885522, by rfl⟩ : syracuseStep 7847363 = 11771045) B11771045
theorem B5231575 : Blo 2037435 5231575 := bstep (se 1 (by rfl) ⟨3923681, by rfl⟩ : syracuseStep 5231575 = 7847363) B7847363
theorem B6975433 : Blo 2037435 6975433 := bstep (se 2 (by rfl) ⟨2615787, by rfl⟩ : syracuseStep 6975433 = 5231575) B5231575
theorem B9300577 : Blo 2037435 9300577 := bstep (se 2 (by rfl) ⟨3487716, by rfl⟩ : syracuseStep 9300577 = 6975433) B6975433
theorem B12400769 : Blo 2037435 12400769 := bstep (se 2 (by rfl) ⟨4650288, by rfl⟩ : syracuseStep 12400769 = 9300577) B9300577
theorem B8267179 : Blo 2037435 8267179 := bstep (se 1 (by rfl) ⟨6200384, by rfl⟩ : syracuseStep 8267179 = 12400769) B12400769
theorem B11022905 : Blo 2037435 11022905 := bstep (se 2 (by rfl) ⟨4133589, by rfl⟩ : syracuseStep 11022905 = 8267179) B8267179
theorem B7348603 : Blo 2037435 7348603 := bstep (se 1 (by rfl) ⟨5511452, by rfl⟩ : syracuseStep 7348603 = 11022905) B11022905
theorem B9798137 : Blo 2037435 9798137 := bstep (se 2 (by rfl) ⟨3674301, by rfl⟩ : syracuseStep 9798137 = 7348603) B7348603
theorem B6532091 : Blo 2037435 6532091 := bstep (se 1 (by rfl) ⟨4899068, by rfl⟩ : syracuseStep 6532091 = 9798137) B9798137
theorem B4354727 : Blo 2037435 4354727 := bstep (se 1 (by rfl) ⟨3266045, by rfl⟩ : syracuseStep 4354727 = 6532091) B6532091
theorem B11612605 : Blo 2037435 11612605 := bstep (se 3 (by rfl) ⟨2177363, by rfl⟩ : syracuseStep 11612605 = 4354727) B4354727
theorem B15483473 : Blo 2037435 15483473 := bstep (se 2 (by rfl) ⟨5806302, by rfl⟩ : syracuseStep 15483473 = 11612605) B11612605
theorem B10322315 : Blo 2037435 10322315 := bstep (se 1 (by rfl) ⟨7741736, by rfl⟩ : syracuseStep 10322315 = 15483473) B15483473
theorem B6881543 : Blo 2037435 6881543 := bstep (se 1 (by rfl) ⟨5161157, by rfl⟩ : syracuseStep 6881543 = 10322315) B10322315
theorem B4587695 : Blo 2037435 4587695 := bstep (se 1 (by rfl) ⟨3440771, by rfl⟩ : syracuseStep 4587695 = 6881543) B6881543
theorem B3058463 : Blo 2037435 3058463 := bstep (se 1 (by rfl) ⟨2293847, by rfl⟩ : syracuseStep 3058463 = 4587695) B4587695
theorem B2038975 : Blo 2037435 2038975 := bstep (se 1 (by rfl) ⟨1529231, by rfl⟩ : syracuseStep 2038975 = 3058463) B3058463
theorem B3058469 : Blo 2037435 3058469 := bbase (se 4 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 3058469 = 573463) (by norm_num)
theorem B2038979 : Blo 2037435 2038979 := bstep (se 1 (by rfl) ⟨1529234, by rfl⟩ : syracuseStep 2038979 = 3058469) B3058469
theorem B2580589 : Blo 2037435 2580589 := bbase (se 3 (by rfl) ⟨483860, by rfl⟩ : syracuseStep 2580589 = 967721) (by norm_num)
theorem B3440785 : Blo 2037435 3440785 := bstep (se 2 (by rfl) ⟨1290294, by rfl⟩ : syracuseStep 3440785 = 2580589) B2580589
theorem B4587713 : Blo 2037435 4587713 := bstep (se 2 (by rfl) ⟨1720392, by rfl⟩ : syracuseStep 4587713 = 3440785) B3440785
theorem B3058475 : Blo 2037435 3058475 := bstep (se 1 (by rfl) ⟨2293856, by rfl⟩ : syracuseStep 3058475 = 4587713) B4587713
theorem B2038983 : Blo 2037435 2038983 := bstep (se 1 (by rfl) ⟨1529237, by rfl⟩ : syracuseStep 2038983 = 3058475) B3058475
theorem B2293861 : Blo 2037435 2293861 := bbase (se 4 (by rfl) ⟨215049, by rfl⟩ : syracuseStep 2293861 = 430099) (by norm_num)
theorem B3058481 : Blo 2037435 3058481 := bstep (se 2 (by rfl) ⟨1146930, by rfl⟩ : syracuseStep 3058481 = 2293861) B2293861
theorem B2038987 : Blo 2037435 2038987 := bstep (se 1 (by rfl) ⟨1529240, by rfl⟩ : syracuseStep 2038987 = 3058481) B3058481
theorem B2177381 : Blo 2037435 2177381 := bbase (se 4 (by rfl) ⟨204129, by rfl⟩ : syracuseStep 2177381 = 408259) (by norm_num)
theorem B5806349 : Blo 2037435 5806349 := bstep (se 3 (by rfl) ⟨1088690, by rfl⟩ : syracuseStep 5806349 = 2177381) B2177381
theorem B3870899 : Blo 2037435 3870899 := bstep (se 1 (by rfl) ⟨2903174, by rfl⟩ : syracuseStep 3870899 = 5806349) B5806349
theorem B2580599 : Blo 2037435 2580599 := bstep (se 1 (by rfl) ⟨1935449, by rfl⟩ : syracuseStep 2580599 = 3870899) B3870899
theorem B6881597 : Blo 2037435 6881597 := bstep (se 3 (by rfl) ⟨1290299, by rfl⟩ : syracuseStep 6881597 = 2580599) B2580599
theorem B4587731 : Blo 2037435 4587731 := bstep (se 1 (by rfl) ⟨3440798, by rfl⟩ : syracuseStep 4587731 = 6881597) B6881597
theorem B3058487 : Blo 2037435 3058487 := bstep (se 1 (by rfl) ⟨2293865, by rfl⟩ : syracuseStep 3058487 = 4587731) B4587731
theorem B2038991 : Blo 2037435 2038991 := bstep (se 1 (by rfl) ⟨1529243, by rfl⟩ : syracuseStep 2038991 = 3058487) B3058487
theorem B3058493 : Blo 2037435 3058493 := bbase (se 3 (by rfl) ⟨573467, by rfl⟩ : syracuseStep 3058493 = 1146935) (by norm_num)
theorem B2038995 : Blo 2037435 2038995 := bstep (se 1 (by rfl) ⟨1529246, by rfl⟩ : syracuseStep 2038995 = 3058493) B3058493
theorem B4587749 : Blo 2037435 4587749 := bbase (se 4 (by rfl) ⟨430101, by rfl⟩ : syracuseStep 4587749 = 860203) (by norm_num)
theorem B3058499 : Blo 2037435 3058499 := bstep (se 1 (by rfl) ⟨2293874, by rfl⟩ : syracuseStep 3058499 = 4587749) B4587749
theorem B2038999 : Blo 2037435 2038999 := bstep (se 1 (by rfl) ⟨1529249, by rfl⟩ : syracuseStep 2038999 = 3058499) B3058499
theorem B5161229 : Blo 2037435 5161229 := bbase (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) (by norm_num)
theorem B3440819 : Blo 2037435 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B2293879 : Blo 2037435 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B3058505 : Blo 2037435 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B2039003 : Blo 2037435 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B2903197 : Blo 2037435 2903197 := bbase (se 3 (by rfl) ⟨544349, by rfl⟩ : syracuseStep 2903197 = 1088699) (by norm_num)
theorem B3870929 : Blo 2037435 3870929 := bstep (se 2 (by rfl) ⟨1451598, by rfl⟩ : syracuseStep 3870929 = 2903197) B2903197
theorem B10322477 : Blo 2037435 10322477 := bstep (se 3 (by rfl) ⟨1935464, by rfl⟩ : syracuseStep 10322477 = 3870929) B3870929
theorem B6881651 : Blo 2037435 6881651 := bstep (se 1 (by rfl) ⟨5161238, by rfl⟩ : syracuseStep 6881651 = 10322477) B10322477
theorem B4587767 : Blo 2037435 4587767 := bstep (se 1 (by rfl) ⟨3440825, by rfl⟩ : syracuseStep 4587767 = 6881651) B6881651
theorem B3058511 : Blo 2037435 3058511 := bstep (se 1 (by rfl) ⟨2293883, by rfl⟩ : syracuseStep 3058511 = 4587767) B4587767
theorem B2039007 : Blo 2037435 2039007 := bstep (se 1 (by rfl) ⟨1529255, by rfl⟩ : syracuseStep 2039007 = 3058511) B3058511
theorem B3058517 : Blo 2037435 3058517 := bbase (se 9 (by rfl) ⟨8960, by rfl⟩ : syracuseStep 3058517 = 17921) (by norm_num)
theorem B2039011 : Blo 2037435 2039011 := bstep (se 1 (by rfl) ⟨1529258, by rfl⟩ : syracuseStep 2039011 = 3058517) B3058517
theorem B4354813 : Blo 2037435 4354813 := bbase (se 3 (by rfl) ⟨816527, by rfl⟩ : syracuseStep 4354813 = 1633055) (by norm_num)
theorem B5806417 : Blo 2037435 5806417 := bstep (se 2 (by rfl) ⟨2177406, by rfl⟩ : syracuseStep 5806417 = 4354813) B4354813
theorem B7741889 : Blo 2037435 7741889 := bstep (se 2 (by rfl) ⟨2903208, by rfl⟩ : syracuseStep 7741889 = 5806417) B5806417
theorem B5161259 : Blo 2037435 5161259 := bstep (se 1 (by rfl) ⟨3870944, by rfl⟩ : syracuseStep 5161259 = 7741889) B7741889
theorem B3440839 : Blo 2037435 3440839 := bstep (se 1 (by rfl) ⟨2580629, by rfl⟩ : syracuseStep 3440839 = 5161259) B5161259
theorem B4587785 : Blo 2037435 4587785 := bstep (se 2 (by rfl) ⟨1720419, by rfl⟩ : syracuseStep 4587785 = 3440839) B3440839
theorem B3058523 : Blo 2037435 3058523 := bstep (se 1 (by rfl) ⟨2293892, by rfl⟩ : syracuseStep 3058523 = 4587785) B4587785
theorem B2039015 : Blo 2037435 2039015 := bstep (se 1 (by rfl) ⟨1529261, by rfl⟩ : syracuseStep 2039015 = 3058523) B3058523
theorem B2293897 : Blo 2037435 2293897 := bbase (se 2 (by rfl) ⟨860211, by rfl⟩ : syracuseStep 2293897 = 1720423) (by norm_num)
theorem B3058529 : Blo 2037435 3058529 := bstep (se 2 (by rfl) ⟨1146948, by rfl⟩ : syracuseStep 3058529 = 2293897) B2293897
theorem B2039019 : Blo 2037435 2039019 := bstep (se 1 (by rfl) ⟨1529264, by rfl⟩ : syracuseStep 2039019 = 3058529) B3058529
theorem B18601589 : Blo 2037435 18601589 := bbase (se 5 (by rfl) ⟨871949, by rfl⟩ : syracuseStep 18601589 = 1743899) (by norm_num)
theorem B49604237 : Blo 2037435 49604237 := bstep (se 3 (by rfl) ⟨9300794, by rfl⟩ : syracuseStep 49604237 = 18601589) B18601589
theorem B33069491 : Blo 2037435 33069491 := bstep (se 1 (by rfl) ⟨24802118, by rfl⟩ : syracuseStep 33069491 = 49604237) B49604237
theorem B22046327 : Blo 2037435 22046327 := bstep (se 1 (by rfl) ⟨16534745, by rfl⟩ : syracuseStep 22046327 = 33069491) B33069491
theorem B14697551 : Blo 2037435 14697551 := bstep (se 1 (by rfl) ⟨11023163, by rfl⟩ : syracuseStep 14697551 = 22046327) B22046327
theorem B39193469 : Blo 2037435 39193469 := bstep (se 3 (by rfl) ⟨7348775, by rfl⟩ : syracuseStep 39193469 = 14697551) B14697551
theorem B26128979 : Blo 2037435 26128979 := bstep (se 1 (by rfl) ⟨19596734, by rfl⟩ : syracuseStep 26128979 = 39193469) B39193469
theorem B17419319 : Blo 2037435 17419319 := bstep (se 1 (by rfl) ⟨13064489, by rfl⟩ : syracuseStep 17419319 = 26128979) B26128979
theorem B11612879 : Blo 2037435 11612879 := bstep (se 1 (by rfl) ⟨8709659, by rfl⟩ : syracuseStep 11612879 = 17419319) B17419319
theorem B7741919 : Blo 2037435 7741919 := bstep (se 1 (by rfl) ⟨5806439, by rfl⟩ : syracuseStep 7741919 = 11612879) B11612879
theorem B5161279 : Blo 2037435 5161279 := bstep (se 1 (by rfl) ⟨3870959, by rfl⟩ : syracuseStep 5161279 = 7741919) B7741919
theorem B6881705 : Blo 2037435 6881705 := bstep (se 2 (by rfl) ⟨2580639, by rfl⟩ : syracuseStep 6881705 = 5161279) B5161279
theorem B4587803 : Blo 2037435 4587803 := bstep (se 1 (by rfl) ⟨3440852, by rfl⟩ : syracuseStep 4587803 = 6881705) B6881705
theorem B3058535 : Blo 2037435 3058535 := bstep (se 1 (by rfl) ⟨2293901, by rfl⟩ : syracuseStep 3058535 = 4587803) B4587803
theorem B2039023 : Blo 2037435 2039023 := bstep (se 1 (by rfl) ⟨1529267, by rfl⟩ : syracuseStep 2039023 = 3058535) B3058535
theorem B3058541 : Blo 2037435 3058541 := bbase (se 3 (by rfl) ⟨573476, by rfl⟩ : syracuseStep 3058541 = 1146953) (by norm_num)
theorem B2039027 : Blo 2037435 2039027 := bstep (se 1 (by rfl) ⟨1529270, by rfl⟩ : syracuseStep 2039027 = 3058541) B3058541
theorem B4587821 : Blo 2037435 4587821 := bbase (se 3 (by rfl) ⟨860216, by rfl⟩ : syracuseStep 4587821 = 1720433) (by norm_num)
theorem B3058547 : Blo 2037435 3058547 := bstep (se 1 (by rfl) ⟨2293910, by rfl⟩ : syracuseStep 3058547 = 4587821) B4587821
theorem B2039031 : Blo 2037435 2039031 := bstep (se 1 (by rfl) ⟨1529273, by rfl⟩ : syracuseStep 2039031 = 3058547) B3058547
theorem B3100285 : Blo 2037435 3100285 := bbase (se 3 (by rfl) ⟨581303, by rfl⟩ : syracuseStep 3100285 = 1162607) (by norm_num)
theorem B4133713 : Blo 2037435 4133713 := bstep (se 2 (by rfl) ⟨1550142, by rfl⟩ : syracuseStep 4133713 = 3100285) B3100285
theorem B5511617 : Blo 2037435 5511617 := bstep (se 2 (by rfl) ⟨2066856, by rfl⟩ : syracuseStep 5511617 = 4133713) B4133713
theorem B3674411 : Blo 2037435 3674411 := bstep (se 1 (by rfl) ⟨2755808, by rfl⟩ : syracuseStep 3674411 = 5511617) B5511617
theorem B2449607 : Blo 2037435 2449607 := bstep (se 1 (by rfl) ⟨1837205, by rfl⟩ : syracuseStep 2449607 = 3674411) B3674411
theorem B6532285 : Blo 2037435 6532285 := bstep (se 3 (by rfl) ⟨1224803, by rfl⟩ : syracuseStep 6532285 = 2449607) B2449607
theorem B8709713 : Blo 2037435 8709713 := bstep (se 2 (by rfl) ⟨3266142, by rfl⟩ : syracuseStep 8709713 = 6532285) B6532285
theorem B5806475 : Blo 2037435 5806475 := bstep (se 1 (by rfl) ⟨4354856, by rfl⟩ : syracuseStep 5806475 = 8709713) B8709713
theorem B3870983 : Blo 2037435 3870983 := bstep (se 1 (by rfl) ⟨2903237, by rfl⟩ : syracuseStep 3870983 = 5806475) B5806475
theorem B2580655 : Blo 2037435 2580655 := bstep (se 1 (by rfl) ⟨1935491, by rfl⟩ : syracuseStep 2580655 = 3870983) B3870983
theorem B3440873 : Blo 2037435 3440873 := bstep (se 2 (by rfl) ⟨1290327, by rfl⟩ : syracuseStep 3440873 = 2580655) B2580655
theorem B2293915 : Blo 2037435 2293915 := bstep (se 1 (by rfl) ⟨1720436, by rfl⟩ : syracuseStep 2293915 = 3440873) B3440873
theorem B3058553 : Blo 2037435 3058553 := bstep (se 2 (by rfl) ⟨1146957, by rfl⟩ : syracuseStep 3058553 = 2293915) B2293915
theorem B2039035 : Blo 2037435 2039035 := bstep (se 1 (by rfl) ⟨1529276, by rfl⟩ : syracuseStep 2039035 = 3058553) B3058553
theorem B2325217 : Blo 2037435 2325217 := bbase (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) (by norm_num)
theorem B3100289 : Blo 2037435 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B8267437 : Blo 2037435 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B44092997 : Blo 2037435 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B29395331 : Blo 2037435 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B19596887 : Blo 2037435 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B13064591 : Blo 2037435 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B34838909 : Blo 2037435 34838909 := bstep (se 3 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 34838909 = 13064591) B13064591
theorem B23225939 : Blo 2037435 23225939 := bstep (se 1 (by rfl) ⟨17419454, by rfl⟩ : syracuseStep 23225939 = 34838909) B34838909
theorem B15483959 : Blo 2037435 15483959 := bstep (se 1 (by rfl) ⟨11612969, by rfl⟩ : syracuseStep 15483959 = 23225939) B23225939
theorem B10322639 : Blo 2037435 10322639 := bstep (se 1 (by rfl) ⟨7741979, by rfl⟩ : syracuseStep 10322639 = 15483959) B15483959
theorem B6881759 : Blo 2037435 6881759 := bstep (se 1 (by rfl) ⟨5161319, by rfl⟩ : syracuseStep 6881759 = 10322639) B10322639
theorem B4587839 : Blo 2037435 4587839 := bstep (se 1 (by rfl) ⟨3440879, by rfl⟩ : syracuseStep 4587839 = 6881759) B6881759
theorem B3058559 : Blo 2037435 3058559 := bstep (se 1 (by rfl) ⟨2293919, by rfl⟩ : syracuseStep 3058559 = 4587839) B4587839
theorem B2039039 : Blo 2037435 2039039 := bstep (se 1 (by rfl) ⟨1529279, by rfl⟩ : syracuseStep 2039039 = 3058559) B3058559
theorem B3058565 : Blo 2037435 3058565 := bbase (se 4 (by rfl) ⟨286740, by rfl⟩ : syracuseStep 3058565 = 573481) (by norm_num)
theorem B2039043 : Blo 2037435 2039043 := bstep (se 1 (by rfl) ⟨1529282, by rfl⟩ : syracuseStep 2039043 = 3058565) B3058565
theorem B3440893 : Blo 2037435 3440893 := bbase (se 3 (by rfl) ⟨645167, by rfl⟩ : syracuseStep 3440893 = 1290335) (by norm_num)
theorem B4587857 : Blo 2037435 4587857 := bstep (se 2 (by rfl) ⟨1720446, by rfl⟩ : syracuseStep 4587857 = 3440893) B3440893
theorem B3058571 : Blo 2037435 3058571 := bstep (se 1 (by rfl) ⟨2293928, by rfl⟩ : syracuseStep 3058571 = 4587857) B4587857
theorem B2039047 : Blo 2037435 2039047 := bstep (se 1 (by rfl) ⟨1529285, by rfl⟩ : syracuseStep 2039047 = 3058571) B3058571
theorem B2293933 : Blo 2037435 2293933 := bbase (se 3 (by rfl) ⟨430112, by rfl⟩ : syracuseStep 2293933 = 860225) (by norm_num)
theorem B3058577 : Blo 2037435 3058577 := bstep (se 2 (by rfl) ⟨1146966, by rfl⟩ : syracuseStep 3058577 = 2293933) B2293933
theorem B2039051 : Blo 2037435 2039051 := bstep (se 1 (by rfl) ⟨1529288, by rfl⟩ : syracuseStep 2039051 = 3058577) B3058577
theorem B6881813 : Blo 2037435 6881813 := bbase (se 6 (by rfl) ⟨161292, by rfl⟩ : syracuseStep 6881813 = 322585) (by norm_num)
theorem B4587875 : Blo 2037435 4587875 := bstep (se 1 (by rfl) ⟨3440906, by rfl⟩ : syracuseStep 4587875 = 6881813) B6881813
theorem B3058583 : Blo 2037435 3058583 := bstep (se 1 (by rfl) ⟨2293937, by rfl⟩ : syracuseStep 3058583 = 4587875) B4587875
theorem B2039055 : Blo 2037435 2039055 := bstep (se 1 (by rfl) ⟨1529291, by rfl⟩ : syracuseStep 2039055 = 3058583) B3058583
theorem B3058589 : Blo 2037435 3058589 := bbase (se 3 (by rfl) ⟨573485, by rfl⟩ : syracuseStep 3058589 = 1146971) (by norm_num)
theorem B2039059 : Blo 2037435 2039059 := bstep (se 1 (by rfl) ⟨1529294, by rfl⟩ : syracuseStep 2039059 = 3058589) B3058589
theorem B4587893 : Blo 2037435 4587893 := bbase (se 5 (by rfl) ⟨215057, by rfl⟩ : syracuseStep 4587893 = 430115) (by norm_num)
theorem B3058595 : Blo 2037435 3058595 := bstep (se 1 (by rfl) ⟨2293946, by rfl⟩ : syracuseStep 3058595 = 4587893) B4587893
theorem B2039063 : Blo 2037435 2039063 := bstep (se 1 (by rfl) ⟨1529297, by rfl⟩ : syracuseStep 2039063 = 3058595) B3058595
theorem B2449645 : Blo 2037435 2449645 := bbase (se 3 (by rfl) ⟨459308, by rfl⟩ : syracuseStep 2449645 = 918617) (by norm_num)
theorem B13064773 : Blo 2037435 13064773 := bstep (se 4 (by rfl) ⟨1224822, by rfl⟩ : syracuseStep 13064773 = 2449645) B2449645
theorem B17419697 : Blo 2037435 17419697 := bstep (se 2 (by rfl) ⟨6532386, by rfl⟩ : syracuseStep 17419697 = 13064773) B13064773
theorem B11613131 : Blo 2037435 11613131 := bstep (se 1 (by rfl) ⟨8709848, by rfl⟩ : syracuseStep 11613131 = 17419697) B17419697
theorem B7742087 : Blo 2037435 7742087 := bstep (se 1 (by rfl) ⟨5806565, by rfl⟩ : syracuseStep 7742087 = 11613131) B11613131
theorem B5161391 : Blo 2037435 5161391 := bstep (se 1 (by rfl) ⟨3871043, by rfl⟩ : syracuseStep 5161391 = 7742087) B7742087
theorem B3440927 : Blo 2037435 3440927 := bstep (se 1 (by rfl) ⟨2580695, by rfl⟩ : syracuseStep 3440927 = 5161391) B5161391
theorem B2293951 : Blo 2037435 2293951 := bstep (se 1 (by rfl) ⟨1720463, by rfl⟩ : syracuseStep 2293951 = 3440927) B3440927
theorem B3058601 : Blo 2037435 3058601 := bstep (se 2 (by rfl) ⟨1146975, by rfl⟩ : syracuseStep 3058601 = 2293951) B2293951
theorem B2039067 : Blo 2037435 2039067 := bstep (se 1 (by rfl) ⟨1529300, by rfl⟩ : syracuseStep 2039067 = 3058601) B3058601
theorem B7742101 : Blo 2037435 7742101 := bbase (se 6 (by rfl) ⟨181455, by rfl⟩ : syracuseStep 7742101 = 362911) (by norm_num)
theorem B10322801 : Blo 2037435 10322801 := bstep (se 2 (by rfl) ⟨3871050, by rfl⟩ : syracuseStep 10322801 = 7742101) B7742101
theorem B6881867 : Blo 2037435 6881867 := bstep (se 1 (by rfl) ⟨5161400, by rfl⟩ : syracuseStep 6881867 = 10322801) B10322801
theorem B4587911 : Blo 2037435 4587911 := bstep (se 1 (by rfl) ⟨3440933, by rfl⟩ : syracuseStep 4587911 = 6881867) B6881867
theorem B3058607 : Blo 2037435 3058607 := bstep (se 1 (by rfl) ⟨2293955, by rfl⟩ : syracuseStep 3058607 = 4587911) B4587911
theorem B2039071 : Blo 2037435 2039071 := bstep (se 1 (by rfl) ⟨1529303, by rfl⟩ : syracuseStep 2039071 = 3058607) B3058607
theorem B3058613 : Blo 2037435 3058613 := bbase (se 5 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 3058613 = 286745) (by norm_num)
theorem B2039075 : Blo 2037435 2039075 := bstep (se 1 (by rfl) ⟨1529306, by rfl⟩ : syracuseStep 2039075 = 3058613) B3058613
theorem B5161421 : Blo 2037435 5161421 := bbase (se 3 (by rfl) ⟨967766, by rfl⟩ : syracuseStep 5161421 = 1935533) (by norm_num)
theorem B3440947 : Blo 2037435 3440947 := bstep (se 1 (by rfl) ⟨2580710, by rfl⟩ : syracuseStep 3440947 = 5161421) B5161421
theorem B4587929 : Blo 2037435 4587929 := bstep (se 2 (by rfl) ⟨1720473, by rfl⟩ : syracuseStep 4587929 = 3440947) B3440947
theorem B3058619 : Blo 2037435 3058619 := bstep (se 1 (by rfl) ⟨2293964, by rfl⟩ : syracuseStep 3058619 = 4587929) B4587929
theorem B2039079 : Blo 2037435 2039079 := bstep (se 1 (by rfl) ⟨1529309, by rfl⟩ : syracuseStep 2039079 = 3058619) B3058619
theorem B2293969 : Blo 2037435 2293969 := bbase (se 2 (by rfl) ⟨860238, by rfl⟩ : syracuseStep 2293969 = 1720477) (by norm_num)
theorem B3058625 : Blo 2037435 3058625 := bstep (se 2 (by rfl) ⟨1146984, by rfl⟩ : syracuseStep 3058625 = 2293969) B2293969
theorem B2039083 : Blo 2037435 2039083 := bstep (se 1 (by rfl) ⟨1529312, by rfl⟩ : syracuseStep 2039083 = 3058625) B3058625
theorem B9798677 : Blo 2037435 9798677 := bbase (se 6 (by rfl) ⟨229656, by rfl⟩ : syracuseStep 9798677 = 459313) (by norm_num)
theorem B6532451 : Blo 2037435 6532451 := bstep (se 1 (by rfl) ⟨4899338, by rfl⟩ : syracuseStep 6532451 = 9798677) B9798677
theorem B4354967 : Blo 2037435 4354967 := bstep (se 1 (by rfl) ⟨3266225, by rfl⟩ : syracuseStep 4354967 = 6532451) B6532451
theorem B2903311 : Blo 2037435 2903311 := bstep (se 1 (by rfl) ⟨2177483, by rfl⟩ : syracuseStep 2903311 = 4354967) B4354967
theorem B3871081 : Blo 2037435 3871081 := bstep (se 2 (by rfl) ⟨1451655, by rfl⟩ : syracuseStep 3871081 = 2903311) B2903311
theorem B5161441 : Blo 2037435 5161441 := bstep (se 2 (by rfl) ⟨1935540, by rfl⟩ : syracuseStep 5161441 = 3871081) B3871081
theorem B6881921 : Blo 2037435 6881921 := bstep (se 2 (by rfl) ⟨2580720, by rfl⟩ : syracuseStep 6881921 = 5161441) B5161441
theorem B4587947 : Blo 2037435 4587947 := bstep (se 1 (by rfl) ⟨3440960, by rfl⟩ : syracuseStep 4587947 = 6881921) B6881921
theorem B3058631 : Blo 2037435 3058631 := bstep (se 1 (by rfl) ⟨2293973, by rfl⟩ : syracuseStep 3058631 = 4587947) B4587947
theorem B2039087 : Blo 2037435 2039087 := bstep (se 1 (by rfl) ⟨1529315, by rfl⟩ : syracuseStep 2039087 = 3058631) B3058631
theorem B3058637 : Blo 2037435 3058637 := bbase (se 3 (by rfl) ⟨573494, by rfl⟩ : syracuseStep 3058637 = 1146989) (by norm_num)
theorem B2039091 : Blo 2037435 2039091 := bstep (se 1 (by rfl) ⟨1529318, by rfl⟩ : syracuseStep 2039091 = 3058637) B3058637
theorem B4587965 : Blo 2037435 4587965 := bbase (se 3 (by rfl) ⟨860243, by rfl⟩ : syracuseStep 4587965 = 1720487) (by norm_num)
theorem B3058643 : Blo 2037435 3058643 := bstep (se 1 (by rfl) ⟨2293982, by rfl⟩ : syracuseStep 3058643 = 4587965) B4587965
theorem B2039095 : Blo 2037435 2039095 := bstep (se 1 (by rfl) ⟨1529321, by rfl⟩ : syracuseStep 2039095 = 3058643) B3058643
theorem B3440981 : Blo 2037435 3440981 := bbase (se 10 (by rfl) ⟨5040, by rfl⟩ : syracuseStep 3440981 = 10081) (by norm_num)
theorem B2293987 : Blo 2037435 2293987 := bstep (se 1 (by rfl) ⟨1720490, by rfl⟩ : syracuseStep 2293987 = 3440981) B3440981
theorem B3058649 : Blo 2037435 3058649 := bstep (se 2 (by rfl) ⟨1146993, by rfl⟩ : syracuseStep 3058649 = 2293987) B2293987
theorem B2039099 : Blo 2037435 2039099 := bstep (se 1 (by rfl) ⟨1529324, by rfl⟩ : syracuseStep 2039099 = 3058649) B3058649
theorem B6532501 : Blo 2037435 6532501 := bbase (se 6 (by rfl) ⟨153105, by rfl⟩ : syracuseStep 6532501 = 306211) (by norm_num)
theorem B8710001 : Blo 2037435 8710001 := bstep (se 2 (by rfl) ⟨3266250, by rfl⟩ : syracuseStep 8710001 = 6532501) B6532501
theorem B5806667 : Blo 2037435 5806667 := bstep (se 1 (by rfl) ⟨4355000, by rfl⟩ : syracuseStep 5806667 = 8710001) B8710001
theorem B15484445 : Blo 2037435 15484445 := bstep (se 3 (by rfl) ⟨2903333, by rfl⟩ : syracuseStep 15484445 = 5806667) B5806667
theorem B10322963 : Blo 2037435 10322963 := bstep (se 1 (by rfl) ⟨7742222, by rfl⟩ : syracuseStep 10322963 = 15484445) B15484445
theorem B6881975 : Blo 2037435 6881975 := bstep (se 1 (by rfl) ⟨5161481, by rfl⟩ : syracuseStep 6881975 = 10322963) B10322963
theorem B4587983 : Blo 2037435 4587983 := bstep (se 1 (by rfl) ⟨3440987, by rfl⟩ : syracuseStep 4587983 = 6881975) B6881975
theorem B3058655 : Blo 2037435 3058655 := bstep (se 1 (by rfl) ⟨2293991, by rfl⟩ : syracuseStep 3058655 = 4587983) B4587983
theorem B2039103 : Blo 2037435 2039103 := bstep (se 1 (by rfl) ⟨1529327, by rfl⟩ : syracuseStep 2039103 = 3058655) B3058655
theorem B3058661 : Blo 2037435 3058661 := bbase (se 4 (by rfl) ⟨286749, by rfl⟩ : syracuseStep 3058661 = 573499) (by norm_num)
theorem B2039107 : Blo 2037435 2039107 := bstep (se 1 (by rfl) ⟨1529330, by rfl⟩ : syracuseStep 2039107 = 3058661) B3058661
theorem B8710037 : Blo 2037435 8710037 := bbase (se 6 (by rfl) ⟨204141, by rfl⟩ : syracuseStep 8710037 = 408283) (by norm_num)
theorem B5806691 : Blo 2037435 5806691 := bstep (se 1 (by rfl) ⟨4355018, by rfl⟩ : syracuseStep 5806691 = 8710037) B8710037
theorem B3871127 : Blo 2037435 3871127 := bstep (se 1 (by rfl) ⟨2903345, by rfl⟩ : syracuseStep 3871127 = 5806691) B5806691
theorem B2580751 : Blo 2037435 2580751 := bstep (se 1 (by rfl) ⟨1935563, by rfl⟩ : syracuseStep 2580751 = 3871127) B3871127
theorem B3441001 : Blo 2037435 3441001 := bstep (se 2 (by rfl) ⟨1290375, by rfl⟩ : syracuseStep 3441001 = 2580751) B2580751
theorem B4588001 : Blo 2037435 4588001 := bstep (se 2 (by rfl) ⟨1720500, by rfl⟩ : syracuseStep 4588001 = 3441001) B3441001
theorem B3058667 : Blo 2037435 3058667 := bstep (se 1 (by rfl) ⟨2294000, by rfl⟩ : syracuseStep 3058667 = 4588001) B4588001
theorem B2039111 : Blo 2037435 2039111 := bstep (se 1 (by rfl) ⟨1529333, by rfl⟩ : syracuseStep 2039111 = 3058667) B3058667
theorem B2294005 : Blo 2037435 2294005 := bbase (se 5 (by rfl) ⟨107531, by rfl⟩ : syracuseStep 2294005 = 215063) (by norm_num)
theorem B3058673 : Blo 2037435 3058673 := bstep (se 2 (by rfl) ⟨1147002, by rfl⟩ : syracuseStep 3058673 = 2294005) B2294005
theorem B2039115 : Blo 2037435 2039115 := bstep (se 1 (by rfl) ⟨1529336, by rfl⟩ : syracuseStep 2039115 = 3058673) B3058673
theorem B2580761 : Blo 2037435 2580761 := bbase (se 2 (by rfl) ⟨967785, by rfl⟩ : syracuseStep 2580761 = 1935571) (by norm_num)
theorem B6882029 : Blo 2037435 6882029 := bstep (se 3 (by rfl) ⟨1290380, by rfl⟩ : syracuseStep 6882029 = 2580761) B2580761
theorem B4588019 : Blo 2037435 4588019 := bstep (se 1 (by rfl) ⟨3441014, by rfl⟩ : syracuseStep 4588019 = 6882029) B6882029
theorem B3058679 : Blo 2037435 3058679 := bstep (se 1 (by rfl) ⟨2294009, by rfl⟩ : syracuseStep 3058679 = 4588019) B4588019
theorem B2039119 : Blo 2037435 2039119 := bstep (se 1 (by rfl) ⟨1529339, by rfl⟩ : syracuseStep 2039119 = 3058679) B3058679
theorem B3058685 : Blo 2037435 3058685 := bbase (se 3 (by rfl) ⟨573503, by rfl⟩ : syracuseStep 3058685 = 1147007) (by norm_num)
theorem B2039123 : Blo 2037435 2039123 := bstep (se 1 (by rfl) ⟨1529342, by rfl⟩ : syracuseStep 2039123 = 3058685) B3058685
theorem B4588037 : Blo 2037435 4588037 := bbase (se 4 (by rfl) ⟨430128, by rfl⟩ : syracuseStep 4588037 = 860257) (by norm_num)
theorem B3058691 : Blo 2037435 3058691 := bstep (se 1 (by rfl) ⟨2294018, by rfl⟩ : syracuseStep 3058691 = 4588037) B4588037
theorem B2039127 : Blo 2037435 2039127 := bstep (se 1 (by rfl) ⟨1529345, by rfl⟩ : syracuseStep 2039127 = 3058691) B3058691
theorem B3871165 : Blo 2037435 3871165 := bbase (se 3 (by rfl) ⟨725843, by rfl⟩ : syracuseStep 3871165 = 1451687) (by norm_num)
theorem B5161553 : Blo 2037435 5161553 := bstep (se 2 (by rfl) ⟨1935582, by rfl⟩ : syracuseStep 5161553 = 3871165) B3871165
theorem B3441035 : Blo 2037435 3441035 := bstep (se 1 (by rfl) ⟨2580776, by rfl⟩ : syracuseStep 3441035 = 5161553) B5161553
theorem B2294023 : Blo 2037435 2294023 := bstep (se 1 (by rfl) ⟨1720517, by rfl⟩ : syracuseStep 2294023 = 3441035) B3441035
theorem B3058697 : Blo 2037435 3058697 := bstep (se 2 (by rfl) ⟨1147011, by rfl⟩ : syracuseStep 3058697 = 2294023) B2294023
theorem B2039131 : Blo 2037435 2039131 := bstep (se 1 (by rfl) ⟨1529348, by rfl⟩ : syracuseStep 2039131 = 3058697) B3058697
theorem B10323125 : Blo 2037435 10323125 := bbase (se 5 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 10323125 = 967793) (by norm_num)
theorem B6882083 : Blo 2037435 6882083 := bstep (se 1 (by rfl) ⟨5161562, by rfl⟩ : syracuseStep 6882083 = 10323125) B10323125
theorem B4588055 : Blo 2037435 4588055 := bstep (se 1 (by rfl) ⟨3441041, by rfl⟩ : syracuseStep 4588055 = 6882083) B6882083
theorem B3058703 : Blo 2037435 3058703 := bstep (se 1 (by rfl) ⟨2294027, by rfl⟩ : syracuseStep 3058703 = 4588055) B4588055
theorem B2039135 : Blo 2037435 2039135 := bstep (se 1 (by rfl) ⟨1529351, by rfl⟩ : syracuseStep 2039135 = 3058703) B3058703
theorem B3058709 : Blo 2037435 3058709 := bbase (se 6 (by rfl) ⟨71688, by rfl⟩ : syracuseStep 3058709 = 143377) (by norm_num)
theorem B2039139 : Blo 2037435 2039139 := bstep (se 1 (by rfl) ⟨1529354, by rfl⟩ : syracuseStep 2039139 = 3058709) B3058709
theorem B2066965 : Blo 2037435 2066965 := bbase (se 6 (by rfl) ⟨48444, by rfl⟩ : syracuseStep 2066965 = 96889) (by norm_num)
theorem B11023813 : Blo 2037435 11023813 := bstep (se 4 (by rfl) ⟨1033482, by rfl⟩ : syracuseStep 11023813 = 2066965) B2066965
theorem B14698417 : Blo 2037435 14698417 := bstep (se 2 (by rfl) ⟨5511906, by rfl⟩ : syracuseStep 14698417 = 11023813) B11023813
theorem B19597889 : Blo 2037435 19597889 := bstep (se 2 (by rfl) ⟨7349208, by rfl⟩ : syracuseStep 19597889 = 14698417) B14698417
theorem B13065259 : Blo 2037435 13065259 := bstep (se 1 (by rfl) ⟨9798944, by rfl⟩ : syracuseStep 13065259 = 19597889) B19597889
theorem B17420345 : Blo 2037435 17420345 := bstep (se 2 (by rfl) ⟨6532629, by rfl⟩ : syracuseStep 17420345 = 13065259) B13065259
theorem B11613563 : Blo 2037435 11613563 := bstep (se 1 (by rfl) ⟨8710172, by rfl⟩ : syracuseStep 11613563 = 17420345) B17420345
theorem B7742375 : Blo 2037435 7742375 := bstep (se 1 (by rfl) ⟨5806781, by rfl⟩ : syracuseStep 7742375 = 11613563) B11613563
theorem B5161583 : Blo 2037435 5161583 := bstep (se 1 (by rfl) ⟨3871187, by rfl⟩ : syracuseStep 5161583 = 7742375) B7742375
theorem B3441055 : Blo 2037435 3441055 := bstep (se 1 (by rfl) ⟨2580791, by rfl⟩ : syracuseStep 3441055 = 5161583) B5161583
theorem B4588073 : Blo 2037435 4588073 := bstep (se 2 (by rfl) ⟨1720527, by rfl⟩ : syracuseStep 4588073 = 3441055) B3441055
theorem B3058715 : Blo 2037435 3058715 := bstep (se 1 (by rfl) ⟨2294036, by rfl⟩ : syracuseStep 3058715 = 4588073) B4588073
theorem B2039143 : Blo 2037435 2039143 := bstep (se 1 (by rfl) ⟨1529357, by rfl⟩ : syracuseStep 2039143 = 3058715) B3058715
theorem B2294041 : Blo 2037435 2294041 := bbase (se 2 (by rfl) ⟨860265, by rfl⟩ : syracuseStep 2294041 = 1720531) (by norm_num)
theorem B3058721 : Blo 2037435 3058721 := bstep (se 2 (by rfl) ⟨1147020, by rfl⟩ : syracuseStep 3058721 = 2294041) B2294041
theorem B2039147 : Blo 2037435 2039147 := bstep (se 1 (by rfl) ⟨1529360, by rfl⟩ : syracuseStep 2039147 = 3058721) B3058721
theorem B7742405 : Blo 2037435 7742405 := bbase (se 4 (by rfl) ⟨725850, by rfl⟩ : syracuseStep 7742405 = 1451701) (by norm_num)
theorem B5161603 : Blo 2037435 5161603 := bstep (se 1 (by rfl) ⟨3871202, by rfl⟩ : syracuseStep 5161603 = 7742405) B7742405
theorem B6882137 : Blo 2037435 6882137 := bstep (se 2 (by rfl) ⟨2580801, by rfl⟩ : syracuseStep 6882137 = 5161603) B5161603
theorem B4588091 : Blo 2037435 4588091 := bstep (se 1 (by rfl) ⟨3441068, by rfl⟩ : syracuseStep 4588091 = 6882137) B6882137
theorem B3058727 : Blo 2037435 3058727 := bstep (se 1 (by rfl) ⟨2294045, by rfl⟩ : syracuseStep 3058727 = 4588091) B4588091
theorem B2039151 : Blo 2037435 2039151 := bstep (se 1 (by rfl) ⟨1529363, by rfl⟩ : syracuseStep 2039151 = 3058727) B3058727
theorem B3058733 : Blo 2037435 3058733 := bbase (se 3 (by rfl) ⟨573512, by rfl⟩ : syracuseStep 3058733 = 1147025) (by norm_num)
theorem B2039155 : Blo 2037435 2039155 := bstep (se 1 (by rfl) ⟨1529366, by rfl⟩ : syracuseStep 2039155 = 3058733) B3058733
theorem B4588109 : Blo 2037435 4588109 := bbase (se 3 (by rfl) ⟨860270, by rfl⟩ : syracuseStep 4588109 = 1720541) (by norm_num)
theorem B3058739 : Blo 2037435 3058739 := bstep (se 1 (by rfl) ⟨2294054, by rfl⟩ : syracuseStep 3058739 = 4588109) B4588109
theorem B2039159 : Blo 2037435 2039159 := bstep (se 1 (by rfl) ⟨1529369, by rfl⟩ : syracuseStep 2039159 = 3058739) B3058739
theorem B2580817 : Blo 2037435 2580817 := bbase (se 2 (by rfl) ⟨967806, by rfl⟩ : syracuseStep 2580817 = 1935613) (by norm_num)
theorem B3441089 : Blo 2037435 3441089 := bstep (se 2 (by rfl) ⟨1290408, by rfl⟩ : syracuseStep 3441089 = 2580817) B2580817
theorem B2294059 : Blo 2037435 2294059 := bstep (se 1 (by rfl) ⟨1720544, by rfl⟩ : syracuseStep 2294059 = 3441089) B3441089
theorem B3058745 : Blo 2037435 3058745 := bstep (se 2 (by rfl) ⟨1147029, by rfl⟩ : syracuseStep 3058745 = 2294059) B2294059
theorem B2039163 : Blo 2037435 2039163 := bstep (se 1 (by rfl) ⟨1529372, by rfl⟩ : syracuseStep 2039163 = 3058745) B3058745
theorem B2449765 : Blo 2037435 2449765 := bbase (se 4 (by rfl) ⟨229665, by rfl⟩ : syracuseStep 2449765 = 459331) (by norm_num)
theorem B3266353 : Blo 2037435 3266353 := bstep (se 2 (by rfl) ⟨1224882, by rfl⟩ : syracuseStep 3266353 = 2449765) B2449765
theorem B4355137 : Blo 2037435 4355137 := bstep (se 2 (by rfl) ⟨1633176, by rfl⟩ : syracuseStep 4355137 = 3266353) B3266353
theorem B23227397 : Blo 2037435 23227397 := bstep (se 4 (by rfl) ⟨2177568, by rfl⟩ : syracuseStep 23227397 = 4355137) B4355137
theorem B15484931 : Blo 2037435 15484931 := bstep (se 1 (by rfl) ⟨11613698, by rfl⟩ : syracuseStep 15484931 = 23227397) B23227397
theorem B10323287 : Blo 2037435 10323287 := bstep (se 1 (by rfl) ⟨7742465, by rfl⟩ : syracuseStep 10323287 = 15484931) B15484931
theorem B6882191 : Blo 2037435 6882191 := bstep (se 1 (by rfl) ⟨5161643, by rfl⟩ : syracuseStep 6882191 = 10323287) B10323287
theorem B4588127 : Blo 2037435 4588127 := bstep (se 1 (by rfl) ⟨3441095, by rfl⟩ : syracuseStep 4588127 = 6882191) B6882191
theorem B3058751 : Blo 2037435 3058751 := bstep (se 1 (by rfl) ⟨2294063, by rfl⟩ : syracuseStep 3058751 = 4588127) B4588127
theorem B2039167 : Blo 2037435 2039167 := bstep (se 1 (by rfl) ⟨1529375, by rfl⟩ : syracuseStep 2039167 = 3058751) B3058751
theorem B3058757 : Blo 2037435 3058757 := bbase (se 4 (by rfl) ⟨286758, by rfl⟩ : syracuseStep 3058757 = 573517) (by norm_num)
theorem B2039171 : Blo 2037435 2039171 := bstep (se 1 (by rfl) ⟨1529378, by rfl⟩ : syracuseStep 2039171 = 3058757) B3058757
theorem B3441109 : Blo 2037435 3441109 := bbase (se 7 (by rfl) ⟨40325, by rfl⟩ : syracuseStep 3441109 = 80651) (by norm_num)
theorem B4588145 : Blo 2037435 4588145 := bstep (se 2 (by rfl) ⟨1720554, by rfl⟩ : syracuseStep 4588145 = 3441109) B3441109
theorem B3058763 : Blo 2037435 3058763 := bstep (se 1 (by rfl) ⟨2294072, by rfl⟩ : syracuseStep 3058763 = 4588145) B4588145
theorem B2039175 : Blo 2037435 2039175 := bstep (se 1 (by rfl) ⟨1529381, by rfl⟩ : syracuseStep 2039175 = 3058763) B3058763
theorem B2294077 : Blo 2037435 2294077 := bbase (se 3 (by rfl) ⟨430139, by rfl⟩ : syracuseStep 2294077 = 860279) (by norm_num)
theorem B3058769 : Blo 2037435 3058769 := bstep (se 2 (by rfl) ⟨1147038, by rfl⟩ : syracuseStep 3058769 = 2294077) B2294077
theorem B2039179 : Blo 2037435 2039179 := bstep (se 1 (by rfl) ⟨1529384, by rfl⟩ : syracuseStep 2039179 = 3058769) B3058769
theorem B6882245 : Blo 2037435 6882245 := bbase (se 4 (by rfl) ⟨645210, by rfl⟩ : syracuseStep 6882245 = 1290421) (by norm_num)
theorem B4588163 : Blo 2037435 4588163 := bstep (se 1 (by rfl) ⟨3441122, by rfl⟩ : syracuseStep 4588163 = 6882245) B6882245
theorem B3058775 : Blo 2037435 3058775 := bstep (se 1 (by rfl) ⟨2294081, by rfl⟩ : syracuseStep 3058775 = 4588163) B4588163
theorem B2039183 : Blo 2037435 2039183 := bstep (se 1 (by rfl) ⟨1529387, by rfl⟩ : syracuseStep 2039183 = 3058775) B3058775
theorem B3058781 : Blo 2037435 3058781 := bbase (se 3 (by rfl) ⟨573521, by rfl⟩ : syracuseStep 3058781 = 1147043) (by norm_num)
theorem B2039187 : Blo 2037435 2039187 := bstep (se 1 (by rfl) ⟨1529390, by rfl⟩ : syracuseStep 2039187 = 3058781) B3058781
theorem B4588181 : Blo 2037435 4588181 := bbase (se 6 (by rfl) ⟨107535, by rfl⟩ : syracuseStep 4588181 = 215071) (by norm_num)
theorem B3058787 : Blo 2037435 3058787 := bstep (se 1 (by rfl) ⟨2294090, by rfl⟩ : syracuseStep 3058787 = 4588181) B4588181
theorem B2039191 : Blo 2037435 2039191 := bstep (se 1 (by rfl) ⟨1529393, by rfl⟩ : syracuseStep 2039191 = 3058787) B3058787
theorem B16536149 : Blo 2037435 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B11024099 : Blo 2037435 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B7349399 : Blo 2037435 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B4899599 : Blo 2037435 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B3266399 : Blo 2037435 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B2177599 : Blo 2037435 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B2903465 : Blo 2037435 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B7742573 : Blo 2037435 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B5161715 : Blo 2037435 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B3441143 : Blo 2037435 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B2294095 : Blo 2037435 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B3058793 : Blo 2037435 3058793 := bstep (se 2 (by rfl) ⟨1147047, by rfl⟩ : syracuseStep 3058793 = 2294095) B2294095
theorem B2039195 : Blo 2037435 2039195 := bstep (se 1 (by rfl) ⟨1529396, by rfl⟩ : syracuseStep 2039195 = 3058793) B3058793
theorem B2756029 : Blo 2037435 2756029 := bbase (se 3 (by rfl) ⟨516755, by rfl⟩ : syracuseStep 2756029 = 1033511) (by norm_num)
theorem B3674705 : Blo 2037435 3674705 := bstep (se 2 (by rfl) ⟨1378014, by rfl⟩ : syracuseStep 3674705 = 2756029) B2756029
theorem B9799213 : Blo 2037435 9799213 := bstep (se 3 (by rfl) ⟨1837352, by rfl⟩ : syracuseStep 9799213 = 3674705) B3674705
theorem B13065617 : Blo 2037435 13065617 := bstep (se 2 (by rfl) ⟨4899606, by rfl⟩ : syracuseStep 13065617 = 9799213) B9799213
theorem B8710411 : Blo 2037435 8710411 := bstep (se 1 (by rfl) ⟨6532808, by rfl⟩ : syracuseStep 8710411 = 13065617) B13065617
theorem B11613881 : Blo 2037435 11613881 := bstep (se 2 (by rfl) ⟨4355205, by rfl⟩ : syracuseStep 11613881 = 8710411) B8710411
theorem B7742587 : Blo 2037435 7742587 := bstep (se 1 (by rfl) ⟨5806940, by rfl⟩ : syracuseStep 7742587 = 11613881) B11613881
theorem B10323449 : Blo 2037435 10323449 := bstep (se 2 (by rfl) ⟨3871293, by rfl⟩ : syracuseStep 10323449 = 7742587) B7742587
theorem B6882299 : Blo 2037435 6882299 := bstep (se 1 (by rfl) ⟨5161724, by rfl⟩ : syracuseStep 6882299 = 10323449) B10323449
theorem B4588199 : Blo 2037435 4588199 := bstep (se 1 (by rfl) ⟨3441149, by rfl⟩ : syracuseStep 4588199 = 6882299) B6882299
theorem B3058799 : Blo 2037435 3058799 := bstep (se 1 (by rfl) ⟨2294099, by rfl⟩ : syracuseStep 3058799 = 4588199) B4588199
theorem B2039199 : Blo 2037435 2039199 := bstep (se 1 (by rfl) ⟨1529399, by rfl⟩ : syracuseStep 2039199 = 3058799) B3058799
theorem B3058805 : Blo 2037435 3058805 := bbase (se 5 (by rfl) ⟨143381, by rfl⟩ : syracuseStep 3058805 = 286763) (by norm_num)
theorem B2039203 : Blo 2037435 2039203 := bstep (se 1 (by rfl) ⟨1529402, by rfl⟩ : syracuseStep 2039203 = 3058805) B3058805
theorem B3871309 : Blo 2037435 3871309 := bbase (se 3 (by rfl) ⟨725870, by rfl⟩ : syracuseStep 3871309 = 1451741) (by norm_num)
theorem B5161745 : Blo 2037435 5161745 := bstep (se 2 (by rfl) ⟨1935654, by rfl⟩ : syracuseStep 5161745 = 3871309) B3871309
theorem B3441163 : Blo 2037435 3441163 := bstep (se 1 (by rfl) ⟨2580872, by rfl⟩ : syracuseStep 3441163 = 5161745) B5161745
theorem B4588217 : Blo 2037435 4588217 := bstep (se 2 (by rfl) ⟨1720581, by rfl⟩ : syracuseStep 4588217 = 3441163) B3441163
theorem B3058811 : Blo 2037435 3058811 := bstep (se 1 (by rfl) ⟨2294108, by rfl⟩ : syracuseStep 3058811 = 4588217) B4588217
theorem B2039207 : Blo 2037435 2039207 := bstep (se 1 (by rfl) ⟨1529405, by rfl⟩ : syracuseStep 2039207 = 3058811) B3058811
theorem B2294113 : Blo 2037435 2294113 := bbase (se 2 (by rfl) ⟨860292, by rfl⟩ : syracuseStep 2294113 = 1720585) (by norm_num)
theorem B3058817 : Blo 2037435 3058817 := bstep (se 2 (by rfl) ⟨1147056, by rfl⟩ : syracuseStep 3058817 = 2294113) B2294113
theorem B2039211 : Blo 2037435 2039211 := bstep (se 1 (by rfl) ⟨1529408, by rfl⟩ : syracuseStep 2039211 = 3058817) B3058817
theorem B5161765 : Blo 2037435 5161765 := bbase (se 4 (by rfl) ⟨483915, by rfl⟩ : syracuseStep 5161765 = 967831) (by norm_num)
theorem B6882353 : Blo 2037435 6882353 := bstep (se 2 (by rfl) ⟨2580882, by rfl⟩ : syracuseStep 6882353 = 5161765) B5161765
theorem B4588235 : Blo 2037435 4588235 := bstep (se 1 (by rfl) ⟨3441176, by rfl⟩ : syracuseStep 4588235 = 6882353) B6882353
theorem B3058823 : Blo 2037435 3058823 := bstep (se 1 (by rfl) ⟨2294117, by rfl⟩ : syracuseStep 3058823 = 4588235) B4588235
theorem B2039215 : Blo 2037435 2039215 := bstep (se 1 (by rfl) ⟨1529411, by rfl⟩ : syracuseStep 2039215 = 3058823) B3058823
theorem B3058829 : Blo 2037435 3058829 := bbase (se 3 (by rfl) ⟨573530, by rfl⟩ : syracuseStep 3058829 = 1147061) (by norm_num)
theorem B2039219 : Blo 2037435 2039219 := bstep (se 1 (by rfl) ⟨1529414, by rfl⟩ : syracuseStep 2039219 = 3058829) B3058829
theorem B4588253 : Blo 2037435 4588253 := bbase (se 3 (by rfl) ⟨860297, by rfl⟩ : syracuseStep 4588253 = 1720595) (by norm_num)
theorem B3058835 : Blo 2037435 3058835 := bstep (se 1 (by rfl) ⟨2294126, by rfl⟩ : syracuseStep 3058835 = 4588253) B4588253
theorem B2039223 : Blo 2037435 2039223 := bstep (se 1 (by rfl) ⟨1529417, by rfl⟩ : syracuseStep 2039223 = 3058835) B3058835
theorem B3441197 : Blo 2037435 3441197 := bbase (se 3 (by rfl) ⟨645224, by rfl⟩ : syracuseStep 3441197 = 1290449) (by norm_num)
theorem B2294131 : Blo 2037435 2294131 := bstep (se 1 (by rfl) ⟨1720598, by rfl⟩ : syracuseStep 2294131 = 3441197) B3441197
theorem B3058841 : Blo 2037435 3058841 := bstep (se 2 (by rfl) ⟨1147065, by rfl⟩ : syracuseStep 3058841 = 2294131) B2294131
theorem B2039227 : Blo 2037435 2039227 := bstep (se 1 (by rfl) ⟨1529420, by rfl⟩ : syracuseStep 2039227 = 3058841) B3058841
theorem B3311021 : Blo 2037435 3311021 := bbase (se 3 (by rfl) ⟨620816, by rfl⟩ : syracuseStep 3311021 = 1241633) (by norm_num)
theorem B8829389 : Blo 2037435 8829389 := bstep (se 3 (by rfl) ⟨1655510, by rfl⟩ : syracuseStep 8829389 = 3311021) B3311021
theorem B23545037 : Blo 2037435 23545037 := bstep (se 3 (by rfl) ⟨4414694, by rfl⟩ : syracuseStep 23545037 = 8829389) B8829389
theorem B62786765 : Blo 2037435 62786765 := bstep (se 3 (by rfl) ⟨11772518, by rfl⟩ : syracuseStep 62786765 = 23545037) B23545037
theorem B41857843 : Blo 2037435 41857843 := bstep (se 1 (by rfl) ⟨31393382, by rfl⟩ : syracuseStep 41857843 = 62786765) B62786765
theorem B55810457 : Blo 2037435 55810457 := bstep (se 2 (by rfl) ⟨20928921, by rfl⟩ : syracuseStep 55810457 = 41857843) B41857843
theorem B37206971 : Blo 2037435 37206971 := bstep (se 1 (by rfl) ⟨27905228, by rfl⟩ : syracuseStep 37206971 = 55810457) B55810457
theorem B24804647 : Blo 2037435 24804647 := bstep (se 1 (by rfl) ⟨18603485, by rfl⟩ : syracuseStep 24804647 = 37206971) B37206971
theorem B16536431 : Blo 2037435 16536431 := bstep (se 1 (by rfl) ⟨12402323, by rfl⟩ : syracuseStep 16536431 = 24804647) B24804647
theorem B44097149 : Blo 2037435 44097149 := bstep (se 3 (by rfl) ⟨8268215, by rfl⟩ : syracuseStep 44097149 = 16536431) B16536431
theorem B29398099 : Blo 2037435 29398099 := bstep (se 1 (by rfl) ⟨22048574, by rfl⟩ : syracuseStep 29398099 = 44097149) B44097149
theorem B39197465 : Blo 2037435 39197465 := bstep (se 2 (by rfl) ⟨14699049, by rfl⟩ : syracuseStep 39197465 = 29398099) B29398099
theorem B26131643 : Blo 2037435 26131643 := bstep (se 1 (by rfl) ⟨19598732, by rfl⟩ : syracuseStep 26131643 = 39197465) B39197465
theorem B17421095 : Blo 2037435 17421095 := bstep (se 1 (by rfl) ⟨13065821, by rfl⟩ : syracuseStep 17421095 = 26131643) B26131643
theorem B11614063 : Blo 2037435 11614063 := bstep (se 1 (by rfl) ⟨8710547, by rfl⟩ : syracuseStep 11614063 = 17421095) B17421095
theorem B15485417 : Blo 2037435 15485417 := bstep (se 2 (by rfl) ⟨5807031, by rfl⟩ : syracuseStep 15485417 = 11614063) B11614063
theorem B10323611 : Blo 2037435 10323611 := bstep (se 1 (by rfl) ⟨7742708, by rfl⟩ : syracuseStep 10323611 = 15485417) B15485417
theorem B6882407 : Blo 2037435 6882407 := bstep (se 1 (by rfl) ⟨5161805, by rfl⟩ : syracuseStep 6882407 = 10323611) B10323611
theorem B4588271 : Blo 2037435 4588271 := bstep (se 1 (by rfl) ⟨3441203, by rfl⟩ : syracuseStep 4588271 = 6882407) B6882407
theorem B3058847 : Blo 2037435 3058847 := bstep (se 1 (by rfl) ⟨2294135, by rfl⟩ : syracuseStep 3058847 = 4588271) B4588271
theorem B2039231 : Blo 2037435 2039231 := bstep (se 1 (by rfl) ⟨1529423, by rfl⟩ : syracuseStep 2039231 = 3058847) B3058847
theorem B3058853 : Blo 2037435 3058853 := bbase (se 4 (by rfl) ⟨286767, by rfl⟩ : syracuseStep 3058853 = 573535) (by norm_num)
theorem B2039235 : Blo 2037435 2039235 := bstep (se 1 (by rfl) ⟨1529426, by rfl⟩ : syracuseStep 2039235 = 3058853) B3058853
theorem B2580913 : Blo 2037435 2580913 := bbase (se 2 (by rfl) ⟨967842, by rfl⟩ : syracuseStep 2580913 = 1935685) (by norm_num)
theorem B3441217 : Blo 2037435 3441217 := bstep (se 2 (by rfl) ⟨1290456, by rfl⟩ : syracuseStep 3441217 = 2580913) B2580913
theorem B4588289 : Blo 2037435 4588289 := bstep (se 2 (by rfl) ⟨1720608, by rfl⟩ : syracuseStep 4588289 = 3441217) B3441217
theorem B3058859 : Blo 2037435 3058859 := bstep (se 1 (by rfl) ⟨2294144, by rfl⟩ : syracuseStep 3058859 = 4588289) B4588289
theorem B2039239 : Blo 2037435 2039239 := bstep (se 1 (by rfl) ⟨1529429, by rfl⟩ : syracuseStep 2039239 = 3058859) B3058859
theorem B2294149 : Blo 2037435 2294149 := bbase (se 4 (by rfl) ⟨215076, by rfl⟩ : syracuseStep 2294149 = 430153) (by norm_num)
theorem B3058865 : Blo 2037435 3058865 := bstep (se 2 (by rfl) ⟨1147074, by rfl⟩ : syracuseStep 3058865 = 2294149) B2294149
theorem B2039243 : Blo 2037435 2039243 := bstep (se 1 (by rfl) ⟨1529432, by rfl⟩ : syracuseStep 2039243 = 3058865) B3058865
theorem B4355309 : Blo 2037435 4355309 := bbase (se 3 (by rfl) ⟨816620, by rfl⟩ : syracuseStep 4355309 = 1633241) (by norm_num)
theorem B2903539 : Blo 2037435 2903539 := bstep (se 1 (by rfl) ⟨2177654, by rfl⟩ : syracuseStep 2903539 = 4355309) B4355309
theorem B3871385 : Blo 2037435 3871385 := bstep (se 2 (by rfl) ⟨1451769, by rfl⟩ : syracuseStep 3871385 = 2903539) B2903539
theorem B2580923 : Blo 2037435 2580923 := bstep (se 1 (by rfl) ⟨1935692, by rfl⟩ : syracuseStep 2580923 = 3871385) B3871385
theorem B6882461 : Blo 2037435 6882461 := bstep (se 3 (by rfl) ⟨1290461, by rfl⟩ : syracuseStep 6882461 = 2580923) B2580923
theorem B4588307 : Blo 2037435 4588307 := bstep (se 1 (by rfl) ⟨3441230, by rfl⟩ : syracuseStep 4588307 = 6882461) B6882461
theorem B3058871 : Blo 2037435 3058871 := bstep (se 1 (by rfl) ⟨2294153, by rfl⟩ : syracuseStep 3058871 = 4588307) B4588307
theorem B2039247 : Blo 2037435 2039247 := bstep (se 1 (by rfl) ⟨1529435, by rfl⟩ : syracuseStep 2039247 = 3058871) B3058871
theorem B3058877 : Blo 2037435 3058877 := bbase (se 3 (by rfl) ⟨573539, by rfl⟩ : syracuseStep 3058877 = 1147079) (by norm_num)
theorem B2039251 : Blo 2037435 2039251 := bstep (se 1 (by rfl) ⟨1529438, by rfl⟩ : syracuseStep 2039251 = 3058877) B3058877
theorem B4588325 : Blo 2037435 4588325 := bbase (se 4 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 4588325 = 860311) (by norm_num)
theorem B3058883 : Blo 2037435 3058883 := bstep (se 1 (by rfl) ⟨2294162, by rfl⟩ : syracuseStep 3058883 = 4588325) B4588325
theorem B2039255 : Blo 2037435 2039255 := bstep (se 1 (by rfl) ⟨1529441, by rfl⟩ : syracuseStep 2039255 = 3058883) B3058883
theorem B5161877 : Blo 2037435 5161877 := bbase (se 6 (by rfl) ⟨120981, by rfl⟩ : syracuseStep 5161877 = 241963) (by norm_num)
theorem B3441251 : Blo 2037435 3441251 := bstep (se 1 (by rfl) ⟨2580938, by rfl⟩ : syracuseStep 3441251 = 5161877) B5161877
theorem B2294167 : Blo 2037435 2294167 := bstep (se 1 (by rfl) ⟨1720625, by rfl⟩ : syracuseStep 2294167 = 3441251) B3441251
theorem B3058889 : Blo 2037435 3058889 := bstep (se 2 (by rfl) ⟨1147083, by rfl⟩ : syracuseStep 3058889 = 2294167) B2294167
theorem B2039259 : Blo 2037435 2039259 := bstep (se 1 (by rfl) ⟨1529444, by rfl⟩ : syracuseStep 2039259 = 3058889) B3058889
theorem B3674821 : Blo 2037435 3674821 := bbase (se 4 (by rfl) ⟨344514, by rfl⟩ : syracuseStep 3674821 = 689029) (by norm_num)
theorem B4899761 : Blo 2037435 4899761 := bstep (se 2 (by rfl) ⟨1837410, by rfl⟩ : syracuseStep 4899761 = 3674821) B3674821
theorem B3266507 : Blo 2037435 3266507 := bstep (se 1 (by rfl) ⟨2449880, by rfl⟩ : syracuseStep 3266507 = 4899761) B4899761
theorem B8710685 : Blo 2037435 8710685 := bstep (se 3 (by rfl) ⟨1633253, by rfl⟩ : syracuseStep 8710685 = 3266507) B3266507
theorem B5807123 : Blo 2037435 5807123 := bstep (se 1 (by rfl) ⟨4355342, by rfl⟩ : syracuseStep 5807123 = 8710685) B8710685
theorem B3871415 : Blo 2037435 3871415 := bstep (se 1 (by rfl) ⟨2903561, by rfl⟩ : syracuseStep 3871415 = 5807123) B5807123
theorem B10323773 : Blo 2037435 10323773 := bstep (se 3 (by rfl) ⟨1935707, by rfl⟩ : syracuseStep 10323773 = 3871415) B3871415
theorem B6882515 : Blo 2037435 6882515 := bstep (se 1 (by rfl) ⟨5161886, by rfl⟩ : syracuseStep 6882515 = 10323773) B10323773
theorem B4588343 : Blo 2037435 4588343 := bstep (se 1 (by rfl) ⟨3441257, by rfl⟩ : syracuseStep 4588343 = 6882515) B6882515
theorem B3058895 : Blo 2037435 3058895 := bstep (se 1 (by rfl) ⟨2294171, by rfl⟩ : syracuseStep 3058895 = 4588343) B4588343
theorem B2039263 : Blo 2037435 2039263 := bstep (se 1 (by rfl) ⟨1529447, by rfl⟩ : syracuseStep 2039263 = 3058895) B3058895
theorem B3058901 : Blo 2037435 3058901 := bbase (se 7 (by rfl) ⟨35846, by rfl⟩ : syracuseStep 3058901 = 71693) (by norm_num)
theorem B2039267 : Blo 2037435 2039267 := bstep (se 1 (by rfl) ⟨1529450, by rfl⟩ : syracuseStep 2039267 = 3058901) B3058901
theorem B2903573 : Blo 2037435 2903573 := bbase (se 6 (by rfl) ⟨68052, by rfl⟩ : syracuseStep 2903573 = 136105) (by norm_num)
theorem B7742861 : Blo 2037435 7742861 := bstep (se 3 (by rfl) ⟨1451786, by rfl⟩ : syracuseStep 7742861 = 2903573) B2903573
theorem B5161907 : Blo 2037435 5161907 := bstep (se 1 (by rfl) ⟨3871430, by rfl⟩ : syracuseStep 5161907 = 7742861) B7742861
theorem B3441271 : Blo 2037435 3441271 := bstep (se 1 (by rfl) ⟨2580953, by rfl⟩ : syracuseStep 3441271 = 5161907) B5161907
theorem B4588361 : Blo 2037435 4588361 := bstep (se 2 (by rfl) ⟨1720635, by rfl⟩ : syracuseStep 4588361 = 3441271) B3441271
theorem B3058907 : Blo 2037435 3058907 := bstep (se 1 (by rfl) ⟨2294180, by rfl⟩ : syracuseStep 3058907 = 4588361) B4588361
theorem B2039271 : Blo 2037435 2039271 := bstep (se 1 (by rfl) ⟨1529453, by rfl⟩ : syracuseStep 2039271 = 3058907) B3058907
theorem B2294185 : Blo 2037435 2294185 := bbase (se 2 (by rfl) ⟨860319, by rfl⟩ : syracuseStep 2294185 = 1720639) (by norm_num)
theorem B3058913 : Blo 2037435 3058913 := bstep (se 2 (by rfl) ⟨1147092, by rfl⟩ : syracuseStep 3058913 = 2294185) B2294185
theorem B2039275 : Blo 2037435 2039275 := bstep (se 1 (by rfl) ⟨1529456, by rfl⟩ : syracuseStep 2039275 = 3058913) B3058913
theorem B3311101 : Blo 2037435 3311101 := bbase (se 3 (by rfl) ⟨620831, by rfl⟩ : syracuseStep 3311101 = 1241663) (by norm_num)
theorem B17659205 : Blo 2037435 17659205 := bstep (se 4 (by rfl) ⟨1655550, by rfl⟩ : syracuseStep 17659205 = 3311101) B3311101
theorem B11772803 : Blo 2037435 11772803 := bstep (se 1 (by rfl) ⟨8829602, by rfl⟩ : syracuseStep 11772803 = 17659205) B17659205
theorem B7848535 : Blo 2037435 7848535 := bstep (se 1 (by rfl) ⟨5886401, by rfl⟩ : syracuseStep 7848535 = 11772803) B11772803
theorem B10464713 : Blo 2037435 10464713 := bstep (se 2 (by rfl) ⟨3924267, by rfl⟩ : syracuseStep 10464713 = 7848535) B7848535
theorem B6976475 : Blo 2037435 6976475 := bstep (se 1 (by rfl) ⟨5232356, by rfl⟩ : syracuseStep 6976475 = 10464713) B10464713
theorem B4650983 : Blo 2037435 4650983 := bstep (se 1 (by rfl) ⟨3488237, by rfl⟩ : syracuseStep 4650983 = 6976475) B6976475
theorem B3100655 : Blo 2037435 3100655 := bstep (se 1 (by rfl) ⟨2325491, by rfl⟩ : syracuseStep 3100655 = 4650983) B4650983
theorem B2067103 : Blo 2037435 2067103 := bstep (se 1 (by rfl) ⟨1550327, by rfl⟩ : syracuseStep 2067103 = 3100655) B3100655
theorem B11024549 : Blo 2037435 11024549 := bstep (se 4 (by rfl) ⟨1033551, by rfl⟩ : syracuseStep 11024549 = 2067103) B2067103
theorem B7349699 : Blo 2037435 7349699 := bstep (se 1 (by rfl) ⟨5512274, by rfl⟩ : syracuseStep 7349699 = 11024549) B11024549
theorem B4899799 : Blo 2037435 4899799 := bstep (se 1 (by rfl) ⟨3674849, by rfl⟩ : syracuseStep 4899799 = 7349699) B7349699
theorem B6533065 : Blo 2037435 6533065 := bstep (se 2 (by rfl) ⟨2449899, by rfl⟩ : syracuseStep 6533065 = 4899799) B4899799
theorem B8710753 : Blo 2037435 8710753 := bstep (se 2 (by rfl) ⟨3266532, by rfl⟩ : syracuseStep 8710753 = 6533065) B6533065
theorem B11614337 : Blo 2037435 11614337 := bstep (se 2 (by rfl) ⟨4355376, by rfl⟩ : syracuseStep 11614337 = 8710753) B8710753
theorem B7742891 : Blo 2037435 7742891 := bstep (se 1 (by rfl) ⟨5807168, by rfl⟩ : syracuseStep 7742891 = 11614337) B11614337
theorem B5161927 : Blo 2037435 5161927 := bstep (se 1 (by rfl) ⟨3871445, by rfl⟩ : syracuseStep 5161927 = 7742891) B7742891
theorem B6882569 : Blo 2037435 6882569 := bstep (se 2 (by rfl) ⟨2580963, by rfl⟩ : syracuseStep 6882569 = 5161927) B5161927
theorem B4588379 : Blo 2037435 4588379 := bstep (se 1 (by rfl) ⟨3441284, by rfl⟩ : syracuseStep 4588379 = 6882569) B6882569
theorem B3058919 : Blo 2037435 3058919 := bstep (se 1 (by rfl) ⟨2294189, by rfl⟩ : syracuseStep 3058919 = 4588379) B4588379
theorem B2039279 : Blo 2037435 2039279 := bstep (se 1 (by rfl) ⟨1529459, by rfl⟩ : syracuseStep 2039279 = 3058919) B3058919
theorem B3058925 : Blo 2037435 3058925 := bbase (se 3 (by rfl) ⟨573548, by rfl⟩ : syracuseStep 3058925 = 1147097) (by norm_num)
theorem B2039283 : Blo 2037435 2039283 := bstep (se 1 (by rfl) ⟨1529462, by rfl⟩ : syracuseStep 2039283 = 3058925) B3058925
theorem B4588397 : Blo 2037435 4588397 := bbase (se 3 (by rfl) ⟨860324, by rfl⟩ : syracuseStep 4588397 = 1720649) (by norm_num)
theorem B3058931 : Blo 2037435 3058931 := bstep (se 1 (by rfl) ⟨2294198, by rfl⟩ : syracuseStep 3058931 = 4588397) B4588397
theorem B2039287 : Blo 2037435 2039287 := bstep (se 1 (by rfl) ⟨1529465, by rfl⟩ : syracuseStep 2039287 = 3058931) B3058931
theorem B3871469 : Blo 2037435 3871469 := bbase (se 3 (by rfl) ⟨725900, by rfl⟩ : syracuseStep 3871469 = 1451801) (by norm_num)
theorem B2580979 : Blo 2037435 2580979 := bstep (se 1 (by rfl) ⟨1935734, by rfl⟩ : syracuseStep 2580979 = 3871469) B3871469
theorem B3441305 : Blo 2037435 3441305 := bstep (se 2 (by rfl) ⟨1290489, by rfl⟩ : syracuseStep 3441305 = 2580979) B2580979
theorem B2294203 : Blo 2037435 2294203 := bstep (se 1 (by rfl) ⟨1720652, by rfl⟩ : syracuseStep 2294203 = 3441305) B3441305
theorem B3058937 : Blo 2037435 3058937 := bstep (se 2 (by rfl) ⟨1147101, by rfl⟩ : syracuseStep 3058937 = 2294203) B2294203
theorem B2039291 : Blo 2037435 2039291 := bstep (se 1 (by rfl) ⟨1529468, by rfl⟩ : syracuseStep 2039291 = 3058937) B3058937
theorem B2207417 : Blo 2037435 2207417 := bbase (se 2 (by rfl) ⟨827781, by rfl⟩ : syracuseStep 2207417 = 1655563) (by norm_num)
theorem B5886445 : Blo 2037435 5886445 := bstep (se 3 (by rfl) ⟨1103708, by rfl⟩ : syracuseStep 5886445 = 2207417) B2207417
theorem B7848593 : Blo 2037435 7848593 := bstep (se 2 (by rfl) ⟨2943222, by rfl⟩ : syracuseStep 7848593 = 5886445) B5886445
theorem B5232395 : Blo 2037435 5232395 := bstep (se 1 (by rfl) ⟨3924296, by rfl⟩ : syracuseStep 5232395 = 7848593) B7848593
theorem B13953053 : Blo 2037435 13953053 := bstep (se 3 (by rfl) ⟨2616197, by rfl⟩ : syracuseStep 13953053 = 5232395) B5232395
theorem B9302035 : Blo 2037435 9302035 := bstep (se 1 (by rfl) ⟨6976526, by rfl⟩ : syracuseStep 9302035 = 13953053) B13953053
theorem B12402713 : Blo 2037435 12402713 := bstep (se 2 (by rfl) ⟨4651017, by rfl⟩ : syracuseStep 12402713 = 9302035) B9302035
theorem B8268475 : Blo 2037435 8268475 := bstep (se 1 (by rfl) ⟨6201356, by rfl⟩ : syracuseStep 8268475 = 12402713) B12402713
theorem B11024633 : Blo 2037435 11024633 := bstep (se 2 (by rfl) ⟨4134237, by rfl⟩ : syracuseStep 11024633 = 8268475) B8268475
theorem B29399021 : Blo 2037435 29399021 := bstep (se 3 (by rfl) ⟨5512316, by rfl⟩ : syracuseStep 29399021 = 11024633) B11024633
theorem B19599347 : Blo 2037435 19599347 := bstep (se 1 (by rfl) ⟨14699510, by rfl⟩ : syracuseStep 19599347 = 29399021) B29399021
theorem B52264925 : Blo 2037435 52264925 := bstep (se 3 (by rfl) ⟨9799673, by rfl⟩ : syracuseStep 52264925 = 19599347) B19599347
theorem B34843283 : Blo 2037435 34843283 := bstep (se 1 (by rfl) ⟨26132462, by rfl⟩ : syracuseStep 34843283 = 52264925) B52264925
theorem B23228855 : Blo 2037435 23228855 := bstep (se 1 (by rfl) ⟨17421641, by rfl⟩ : syracuseStep 23228855 = 34843283) B34843283
theorem B15485903 : Blo 2037435 15485903 := bstep (se 1 (by rfl) ⟨11614427, by rfl⟩ : syracuseStep 15485903 = 23228855) B23228855
theorem B10323935 : Blo 2037435 10323935 := bstep (se 1 (by rfl) ⟨7742951, by rfl⟩ : syracuseStep 10323935 = 15485903) B15485903
theorem B6882623 : Blo 2037435 6882623 := bstep (se 1 (by rfl) ⟨5161967, by rfl⟩ : syracuseStep 6882623 = 10323935) B10323935
theorem B4588415 : Blo 2037435 4588415 := bstep (se 1 (by rfl) ⟨3441311, by rfl⟩ : syracuseStep 4588415 = 6882623) B6882623
theorem B3058943 : Blo 2037435 3058943 := bstep (se 1 (by rfl) ⟨2294207, by rfl⟩ : syracuseStep 3058943 = 4588415) B4588415
theorem B2039295 : Blo 2037435 2039295 := bstep (se 1 (by rfl) ⟨1529471, by rfl⟩ : syracuseStep 2039295 = 3058943) B3058943
theorem B3058949 : Blo 2037435 3058949 := bbase (se 4 (by rfl) ⟨286776, by rfl⟩ : syracuseStep 3058949 = 573553) (by norm_num)
theorem B2039299 : Blo 2037435 2039299 := bstep (se 1 (by rfl) ⟨1529474, by rfl⟩ : syracuseStep 2039299 = 3058949) B3058949
theorem B3441325 : Blo 2037435 3441325 := bbase (se 3 (by rfl) ⟨645248, by rfl⟩ : syracuseStep 3441325 = 1290497) (by norm_num)
theorem B4588433 : Blo 2037435 4588433 := bstep (se 2 (by rfl) ⟨1720662, by rfl⟩ : syracuseStep 4588433 = 3441325) B3441325
theorem B3058955 : Blo 2037435 3058955 := bstep (se 1 (by rfl) ⟨2294216, by rfl⟩ : syracuseStep 3058955 = 4588433) B4588433
theorem B2039303 : Blo 2037435 2039303 := bstep (se 1 (by rfl) ⟨1529477, by rfl⟩ : syracuseStep 2039303 = 3058955) B3058955
theorem B2294221 : Blo 2037435 2294221 := bbase (se 3 (by rfl) ⟨430166, by rfl⟩ : syracuseStep 2294221 = 860333) (by norm_num)
theorem B3058961 : Blo 2037435 3058961 := bstep (se 2 (by rfl) ⟨1147110, by rfl⟩ : syracuseStep 3058961 = 2294221) B2294221
theorem B2039307 : Blo 2037435 2039307 := bstep (se 1 (by rfl) ⟨1529480, by rfl⟩ : syracuseStep 2039307 = 3058961) B3058961
theorem B6882677 : Blo 2037435 6882677 := bbase (se 5 (by rfl) ⟨322625, by rfl⟩ : syracuseStep 6882677 = 645251) (by norm_num)
theorem B4588451 : Blo 2037435 4588451 := bstep (se 1 (by rfl) ⟨3441338, by rfl⟩ : syracuseStep 4588451 = 6882677) B6882677
theorem B3058967 : Blo 2037435 3058967 := bstep (se 1 (by rfl) ⟨2294225, by rfl⟩ : syracuseStep 3058967 = 4588451) B4588451
theorem B2039311 : Blo 2037435 2039311 := bstep (se 1 (by rfl) ⟨1529483, by rfl⟩ : syracuseStep 2039311 = 3058967) B3058967
theorem B3058973 : Blo 2037435 3058973 := bbase (se 3 (by rfl) ⟨573557, by rfl⟩ : syracuseStep 3058973 = 1147115) (by norm_num)
theorem B2039315 : Blo 2037435 2039315 := bstep (se 1 (by rfl) ⟨1529486, by rfl⟩ : syracuseStep 2039315 = 3058973) B3058973
theorem B4588469 : Blo 2037435 4588469 := bbase (se 5 (by rfl) ⟨215084, by rfl⟩ : syracuseStep 4588469 = 430169) (by norm_num)
theorem B3058979 : Blo 2037435 3058979 := bstep (se 1 (by rfl) ⟨2294234, by rfl⟩ : syracuseStep 3058979 = 4588469) B4588469
theorem B2039319 : Blo 2037435 2039319 := bstep (se 1 (by rfl) ⟨1529489, by rfl⟩ : syracuseStep 2039319 = 3058979) B3058979
theorem B2756197 : Blo 2037435 2756197 := bbase (se 4 (by rfl) ⟨258393, by rfl⟩ : syracuseStep 2756197 = 516787) (by norm_num)
theorem B14699717 : Blo 2037435 14699717 := bstep (se 4 (by rfl) ⟨1378098, by rfl⟩ : syracuseStep 14699717 = 2756197) B2756197
theorem B9799811 : Blo 2037435 9799811 := bstep (se 1 (by rfl) ⟨7349858, by rfl⟩ : syracuseStep 9799811 = 14699717) B14699717
theorem B6533207 : Blo 2037435 6533207 := bstep (se 1 (by rfl) ⟨4899905, by rfl⟩ : syracuseStep 6533207 = 9799811) B9799811
theorem B4355471 : Blo 2037435 4355471 := bstep (se 1 (by rfl) ⟨3266603, by rfl⟩ : syracuseStep 4355471 = 6533207) B6533207
theorem B11614589 : Blo 2037435 11614589 := bstep (se 3 (by rfl) ⟨2177735, by rfl⟩ : syracuseStep 11614589 = 4355471) B4355471
theorem B7743059 : Blo 2037435 7743059 := bstep (se 1 (by rfl) ⟨5807294, by rfl⟩ : syracuseStep 7743059 = 11614589) B11614589
theorem B5162039 : Blo 2037435 5162039 := bstep (se 1 (by rfl) ⟨3871529, by rfl⟩ : syracuseStep 5162039 = 7743059) B7743059
theorem B3441359 : Blo 2037435 3441359 := bstep (se 1 (by rfl) ⟨2581019, by rfl⟩ : syracuseStep 3441359 = 5162039) B5162039
theorem B2294239 : Blo 2037435 2294239 := bstep (se 1 (by rfl) ⟨1720679, by rfl⟩ : syracuseStep 2294239 = 3441359) B3441359
theorem B3058985 : Blo 2037435 3058985 := bstep (se 2 (by rfl) ⟨1147119, by rfl⟩ : syracuseStep 3058985 = 2294239) B2294239
theorem B2039323 : Blo 2037435 2039323 := bstep (se 1 (by rfl) ⟨1529492, by rfl⟩ : syracuseStep 2039323 = 3058985) B3058985
theorem B9799829 : Blo 2037435 9799829 := bbase (se 6 (by rfl) ⟨229683, by rfl⟩ : syracuseStep 9799829 = 459367) (by norm_num)
theorem B6533219 : Blo 2037435 6533219 := bstep (se 1 (by rfl) ⟨4899914, by rfl⟩ : syracuseStep 6533219 = 9799829) B9799829
theorem B4355479 : Blo 2037435 4355479 := bstep (se 1 (by rfl) ⟨3266609, by rfl⟩ : syracuseStep 4355479 = 6533219) B6533219
theorem B5807305 : Blo 2037435 5807305 := bstep (se 2 (by rfl) ⟨2177739, by rfl⟩ : syracuseStep 5807305 = 4355479) B4355479
theorem B7743073 : Blo 2037435 7743073 := bstep (se 2 (by rfl) ⟨2903652, by rfl⟩ : syracuseStep 7743073 = 5807305) B5807305
theorem B10324097 : Blo 2037435 10324097 := bstep (se 2 (by rfl) ⟨3871536, by rfl⟩ : syracuseStep 10324097 = 7743073) B7743073
theorem B6882731 : Blo 2037435 6882731 := bstep (se 1 (by rfl) ⟨5162048, by rfl⟩ : syracuseStep 6882731 = 10324097) B10324097
theorem B4588487 : Blo 2037435 4588487 := bstep (se 1 (by rfl) ⟨3441365, by rfl⟩ : syracuseStep 4588487 = 6882731) B6882731
theorem B3058991 : Blo 2037435 3058991 := bstep (se 1 (by rfl) ⟨2294243, by rfl⟩ : syracuseStep 3058991 = 4588487) B4588487
theorem B2039327 : Blo 2037435 2039327 := bstep (se 1 (by rfl) ⟨1529495, by rfl⟩ : syracuseStep 2039327 = 3058991) B3058991
theorem B3058997 : Blo 2037435 3058997 := bbase (se 5 (by rfl) ⟨143390, by rfl⟩ : syracuseStep 3058997 = 286781) (by norm_num)
theorem B2039331 : Blo 2037435 2039331 := bstep (se 1 (by rfl) ⟨1529498, by rfl⟩ : syracuseStep 2039331 = 3058997) B3058997
theorem B5162069 : Blo 2037435 5162069 := bbase (se 8 (by rfl) ⟨30246, by rfl⟩ : syracuseStep 5162069 = 60493) (by norm_num)
theorem B3441379 : Blo 2037435 3441379 := bstep (se 1 (by rfl) ⟨2581034, by rfl⟩ : syracuseStep 3441379 = 5162069) B5162069
theorem B4588505 : Blo 2037435 4588505 := bstep (se 2 (by rfl) ⟨1720689, by rfl⟩ : syracuseStep 4588505 = 3441379) B3441379
theorem B3059003 : Blo 2037435 3059003 := bstep (se 1 (by rfl) ⟨2294252, by rfl⟩ : syracuseStep 3059003 = 4588505) B4588505
theorem B2039335 : Blo 2037435 2039335 := bstep (se 1 (by rfl) ⟨1529501, by rfl⟩ : syracuseStep 2039335 = 3059003) B3059003
theorem B2294257 : Blo 2037435 2294257 := bbase (se 2 (by rfl) ⟨860346, by rfl⟩ : syracuseStep 2294257 = 1720693) (by norm_num)
theorem B3059009 : Blo 2037435 3059009 := bstep (se 2 (by rfl) ⟨1147128, by rfl⟩ : syracuseStep 3059009 = 2294257) B2294257
theorem B2039339 : Blo 2037435 2039339 := bstep (se 1 (by rfl) ⟨1529504, by rfl⟩ : syracuseStep 2039339 = 3059009) B3059009
theorem B3674965 : Blo 2037435 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B4899953 : Blo 2037435 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B13066541 : Blo 2037435 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B8711027 : Blo 2037435 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B5807351 : Blo 2037435 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B3871567 : Blo 2037435 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B5162089 : Blo 2037435 5162089 := bstep (se 2 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 5162089 = 3871567) B3871567
theorem B6882785 : Blo 2037435 6882785 := bstep (se 2 (by rfl) ⟨2581044, by rfl⟩ : syracuseStep 6882785 = 5162089) B5162089
theorem B4588523 : Blo 2037435 4588523 := bstep (se 1 (by rfl) ⟨3441392, by rfl⟩ : syracuseStep 4588523 = 6882785) B6882785
theorem B3059015 : Blo 2037435 3059015 := bstep (se 1 (by rfl) ⟨2294261, by rfl⟩ : syracuseStep 3059015 = 4588523) B4588523
theorem B2039343 : Blo 2037435 2039343 := bstep (se 1 (by rfl) ⟨1529507, by rfl⟩ : syracuseStep 2039343 = 3059015) B3059015
theorem B3059021 : Blo 2037435 3059021 := bbase (se 3 (by rfl) ⟨573566, by rfl⟩ : syracuseStep 3059021 = 1147133) (by norm_num)
theorem B2039347 : Blo 2037435 2039347 := bstep (se 1 (by rfl) ⟨1529510, by rfl⟩ : syracuseStep 2039347 = 3059021) B3059021
theorem B4588541 : Blo 2037435 4588541 := bbase (se 3 (by rfl) ⟨860351, by rfl⟩ : syracuseStep 4588541 = 1720703) (by norm_num)
theorem B3059027 : Blo 2037435 3059027 := bstep (se 1 (by rfl) ⟨2294270, by rfl⟩ : syracuseStep 3059027 = 4588541) B4588541
theorem B2039351 : Blo 2037435 2039351 := bstep (se 1 (by rfl) ⟨1529513, by rfl⟩ : syracuseStep 2039351 = 3059027) B3059027
theorem B3441413 : Blo 2037435 3441413 := bbase (se 4 (by rfl) ⟨322632, by rfl⟩ : syracuseStep 3441413 = 645265) (by norm_num)
theorem B2294275 : Blo 2037435 2294275 := bstep (se 1 (by rfl) ⟨1720706, by rfl⟩ : syracuseStep 2294275 = 3441413) B3441413
theorem B3059033 : Blo 2037435 3059033 := bstep (se 2 (by rfl) ⟨1147137, by rfl⟩ : syracuseStep 3059033 = 2294275) B2294275
theorem B2039355 : Blo 2037435 2039355 := bstep (se 1 (by rfl) ⟨1529516, by rfl⟩ : syracuseStep 2039355 = 3059033) B3059033
theorem B15486389 : Blo 2037435 15486389 := bbase (se 5 (by rfl) ⟨725924, by rfl⟩ : syracuseStep 15486389 = 1451849) (by norm_num)
theorem B10324259 : Blo 2037435 10324259 := bstep (se 1 (by rfl) ⟨7743194, by rfl⟩ : syracuseStep 10324259 = 15486389) B15486389
theorem B6882839 : Blo 2037435 6882839 := bstep (se 1 (by rfl) ⟨5162129, by rfl⟩ : syracuseStep 6882839 = 10324259) B10324259
theorem B4588559 : Blo 2037435 4588559 := bstep (se 1 (by rfl) ⟨3441419, by rfl⟩ : syracuseStep 4588559 = 6882839) B6882839
theorem B3059039 : Blo 2037435 3059039 := bstep (se 1 (by rfl) ⟨2294279, by rfl⟩ : syracuseStep 3059039 = 4588559) B4588559
theorem B2039359 : Blo 2037435 2039359 := bstep (se 1 (by rfl) ⟨1529519, by rfl⟩ : syracuseStep 2039359 = 3059039) B3059039
theorem B3059045 : Blo 2037435 3059045 := bbase (se 4 (by rfl) ⟨286785, by rfl⟩ : syracuseStep 3059045 = 573571) (by norm_num)
theorem B2039363 : Blo 2037435 2039363 := bstep (se 1 (by rfl) ⟨1529522, by rfl⟩ : syracuseStep 2039363 = 3059045) B3059045
theorem B3871613 : Blo 2037435 3871613 := bbase (se 3 (by rfl) ⟨725927, by rfl⟩ : syracuseStep 3871613 = 1451855) (by norm_num)
theorem B2581075 : Blo 2037435 2581075 := bstep (se 1 (by rfl) ⟨1935806, by rfl⟩ : syracuseStep 2581075 = 3871613) B3871613
theorem B3441433 : Blo 2037435 3441433 := bstep (se 2 (by rfl) ⟨1290537, by rfl⟩ : syracuseStep 3441433 = 2581075) B2581075
theorem B4588577 : Blo 2037435 4588577 := bstep (se 2 (by rfl) ⟨1720716, by rfl⟩ : syracuseStep 4588577 = 3441433) B3441433
theorem B3059051 : Blo 2037435 3059051 := bstep (se 1 (by rfl) ⟨2294288, by rfl⟩ : syracuseStep 3059051 = 4588577) B4588577
theorem B2039367 : Blo 2037435 2039367 := bstep (se 1 (by rfl) ⟨1529525, by rfl⟩ : syracuseStep 2039367 = 3059051) B3059051
theorem B2294293 : Blo 2037435 2294293 := bbase (se 6 (by rfl) ⟨53772, by rfl⟩ : syracuseStep 2294293 = 107545) (by norm_num)
theorem B3059057 : Blo 2037435 3059057 := bstep (se 2 (by rfl) ⟨1147146, by rfl⟩ : syracuseStep 3059057 = 2294293) B2294293
theorem B2039371 : Blo 2037435 2039371 := bstep (se 1 (by rfl) ⟨1529528, by rfl⟩ : syracuseStep 2039371 = 3059057) B3059057
theorem B2581085 : Blo 2037435 2581085 := bbase (se 3 (by rfl) ⟨483953, by rfl⟩ : syracuseStep 2581085 = 967907) (by norm_num)
theorem B6882893 : Blo 2037435 6882893 := bstep (se 3 (by rfl) ⟨1290542, by rfl⟩ : syracuseStep 6882893 = 2581085) B2581085
theorem B4588595 : Blo 2037435 4588595 := bstep (se 1 (by rfl) ⟨3441446, by rfl⟩ : syracuseStep 4588595 = 6882893) B6882893
theorem B3059063 : Blo 2037435 3059063 := bstep (se 1 (by rfl) ⟨2294297, by rfl⟩ : syracuseStep 3059063 = 4588595) B4588595
theorem B2039375 : Blo 2037435 2039375 := bstep (se 1 (by rfl) ⟨1529531, by rfl⟩ : syracuseStep 2039375 = 3059063) B3059063
theorem B3059069 : Blo 2037435 3059069 := bbase (se 3 (by rfl) ⟨573575, by rfl⟩ : syracuseStep 3059069 = 1147151) (by norm_num)
theorem B2039379 : Blo 2037435 2039379 := bstep (se 1 (by rfl) ⟨1529534, by rfl⟩ : syracuseStep 2039379 = 3059069) B3059069
theorem B4588613 : Blo 2037435 4588613 := bbase (se 4 (by rfl) ⟨430182, by rfl⟩ : syracuseStep 4588613 = 860365) (by norm_num)
theorem B3059075 : Blo 2037435 3059075 := bstep (se 1 (by rfl) ⟨2294306, by rfl⟩ : syracuseStep 3059075 = 4588613) B4588613
theorem B2039383 : Blo 2037435 2039383 := bstep (se 1 (by rfl) ⟨1529537, by rfl⟩ : syracuseStep 2039383 = 3059075) B3059075
theorem B5807477 : Blo 2037435 5807477 := bbase (se 5 (by rfl) ⟨272225, by rfl⟩ : syracuseStep 5807477 = 544451) (by norm_num)
theorem B3871651 : Blo 2037435 3871651 := bstep (se 1 (by rfl) ⟨2903738, by rfl⟩ : syracuseStep 3871651 = 5807477) B5807477
theorem B5162201 : Blo 2037435 5162201 := bstep (se 2 (by rfl) ⟨1935825, by rfl⟩ : syracuseStep 5162201 = 3871651) B3871651
theorem B3441467 : Blo 2037435 3441467 := bstep (se 1 (by rfl) ⟨2581100, by rfl⟩ : syracuseStep 3441467 = 5162201) B5162201
theorem B2294311 : Blo 2037435 2294311 := bstep (se 1 (by rfl) ⟨1720733, by rfl⟩ : syracuseStep 2294311 = 3441467) B3441467
theorem B3059081 : Blo 2037435 3059081 := bstep (se 2 (by rfl) ⟨1147155, by rfl⟩ : syracuseStep 3059081 = 2294311) B2294311
theorem B2039387 : Blo 2037435 2039387 := bstep (se 1 (by rfl) ⟨1529540, by rfl⟩ : syracuseStep 2039387 = 3059081) B3059081
theorem B10324421 : Blo 2037435 10324421 := bbase (se 4 (by rfl) ⟨967914, by rfl⟩ : syracuseStep 10324421 = 1935829) (by norm_num)
theorem B6882947 : Blo 2037435 6882947 := bstep (se 1 (by rfl) ⟨5162210, by rfl⟩ : syracuseStep 6882947 = 10324421) B10324421
theorem B4588631 : Blo 2037435 4588631 := bstep (se 1 (by rfl) ⟨3441473, by rfl⟩ : syracuseStep 4588631 = 6882947) B6882947
theorem B3059087 : Blo 2037435 3059087 := bstep (se 1 (by rfl) ⟨2294315, by rfl⟩ : syracuseStep 3059087 = 4588631) B4588631
theorem B2039391 : Blo 2037435 2039391 := bstep (se 1 (by rfl) ⟨1529543, by rfl⟩ : syracuseStep 2039391 = 3059087) B3059087
theorem B3059093 : Blo 2037435 3059093 := bbase (se 6 (by rfl) ⟨71697, by rfl⟩ : syracuseStep 3059093 = 143395) (by norm_num)
theorem B2039395 : Blo 2037435 2039395 := bstep (se 1 (by rfl) ⟨1529546, by rfl⟩ : syracuseStep 2039395 = 3059093) B3059093
theorem B3266725 : Blo 2037435 3266725 := bbase (se 4 (by rfl) ⟨306255, by rfl⟩ : syracuseStep 3266725 = 612511) (by norm_num)
theorem B4355633 : Blo 2037435 4355633 := bstep (se 2 (by rfl) ⟨1633362, by rfl⟩ : syracuseStep 4355633 = 3266725) B3266725
theorem B11615021 : Blo 2037435 11615021 := bstep (se 3 (by rfl) ⟨2177816, by rfl⟩ : syracuseStep 11615021 = 4355633) B4355633
theorem B7743347 : Blo 2037435 7743347 := bstep (se 1 (by rfl) ⟨5807510, by rfl⟩ : syracuseStep 7743347 = 11615021) B11615021
theorem B5162231 : Blo 2037435 5162231 := bstep (se 1 (by rfl) ⟨3871673, by rfl⟩ : syracuseStep 5162231 = 7743347) B7743347
theorem B3441487 : Blo 2037435 3441487 := bstep (se 1 (by rfl) ⟨2581115, by rfl⟩ : syracuseStep 3441487 = 5162231) B5162231
theorem B4588649 : Blo 2037435 4588649 := bstep (se 2 (by rfl) ⟨1720743, by rfl⟩ : syracuseStep 4588649 = 3441487) B3441487
theorem B3059099 : Blo 2037435 3059099 := bstep (se 1 (by rfl) ⟨2294324, by rfl⟩ : syracuseStep 3059099 = 4588649) B4588649
theorem B2039399 : Blo 2037435 2039399 := bstep (se 1 (by rfl) ⟨1529549, by rfl⟩ : syracuseStep 2039399 = 3059099) B3059099
theorem B2294329 : Blo 2037435 2294329 := bbase (se 2 (by rfl) ⟨860373, by rfl⟩ : syracuseStep 2294329 = 1720747) (by norm_num)
theorem B3059105 : Blo 2037435 3059105 := bstep (se 2 (by rfl) ⟨1147164, by rfl⟩ : syracuseStep 3059105 = 2294329) B2294329
theorem B2039403 : Blo 2037435 2039403 := bstep (se 1 (by rfl) ⟨1529552, by rfl⟩ : syracuseStep 2039403 = 3059105) B3059105
theorem B2177825 : Blo 2037435 2177825 := bbase (se 2 (by rfl) ⟨816684, by rfl⟩ : syracuseStep 2177825 = 1633369) (by norm_num)
theorem B5807533 : Blo 2037435 5807533 := bstep (se 3 (by rfl) ⟨1088912, by rfl⟩ : syracuseStep 5807533 = 2177825) B2177825
theorem B7743377 : Blo 2037435 7743377 := bstep (se 2 (by rfl) ⟨2903766, by rfl⟩ : syracuseStep 7743377 = 5807533) B5807533
theorem B5162251 : Blo 2037435 5162251 := bstep (se 1 (by rfl) ⟨3871688, by rfl⟩ : syracuseStep 5162251 = 7743377) B7743377
theorem B6883001 : Blo 2037435 6883001 := bstep (se 2 (by rfl) ⟨2581125, by rfl⟩ : syracuseStep 6883001 = 5162251) B5162251
theorem B4588667 : Blo 2037435 4588667 := bstep (se 1 (by rfl) ⟨3441500, by rfl⟩ : syracuseStep 4588667 = 6883001) B6883001
theorem B3059111 : Blo 2037435 3059111 := bstep (se 1 (by rfl) ⟨2294333, by rfl⟩ : syracuseStep 3059111 = 4588667) B4588667
theorem B2039407 : Blo 2037435 2039407 := bstep (se 1 (by rfl) ⟨1529555, by rfl⟩ : syracuseStep 2039407 = 3059111) B3059111
theorem B3059117 : Blo 2037435 3059117 := bbase (se 3 (by rfl) ⟨573584, by rfl⟩ : syracuseStep 3059117 = 1147169) (by norm_num)
theorem B2039411 : Blo 2037435 2039411 := bstep (se 1 (by rfl) ⟨1529558, by rfl⟩ : syracuseStep 2039411 = 3059117) B3059117
theorem B4588685 : Blo 2037435 4588685 := bbase (se 3 (by rfl) ⟨860378, by rfl⟩ : syracuseStep 4588685 = 1720757) (by norm_num)
theorem B3059123 : Blo 2037435 3059123 := bstep (se 1 (by rfl) ⟨2294342, by rfl⟩ : syracuseStep 3059123 = 4588685) B4588685
theorem B2039415 : Blo 2037435 2039415 := bstep (se 1 (by rfl) ⟨1529561, by rfl⟩ : syracuseStep 2039415 = 3059123) B3059123
theorem B2581141 : Blo 2037435 2581141 := bbase (se 6 (by rfl) ⟨60495, by rfl⟩ : syracuseStep 2581141 = 120991) (by norm_num)
theorem B3441521 : Blo 2037435 3441521 := bstep (se 2 (by rfl) ⟨1290570, by rfl⟩ : syracuseStep 3441521 = 2581141) B2581141
theorem B2294347 : Blo 2037435 2294347 := bstep (se 1 (by rfl) ⟨1720760, by rfl⟩ : syracuseStep 2294347 = 3441521) B3441521
theorem B3059129 : Blo 2037435 3059129 := bstep (se 2 (by rfl) ⟨1147173, by rfl⟩ : syracuseStep 3059129 = 2294347) B2294347
theorem B2039419 : Blo 2037435 2039419 := bstep (se 1 (by rfl) ⟨1529564, by rfl⟩ : syracuseStep 2039419 = 3059129) B3059129
theorem B5232725 : Blo 2037435 5232725 := bbase (se 8 (by rfl) ⟨30660, by rfl⟩ : syracuseStep 5232725 = 61321) (by norm_num)
theorem B3488483 : Blo 2037435 3488483 := bstep (se 1 (by rfl) ⟨2616362, by rfl⟩ : syracuseStep 3488483 = 5232725) B5232725
theorem B2325655 : Blo 2037435 2325655 := bstep (se 1 (by rfl) ⟨1744241, by rfl⟩ : syracuseStep 2325655 = 3488483) B3488483
theorem B3100873 : Blo 2037435 3100873 := bstep (se 2 (by rfl) ⟨1162827, by rfl⟩ : syracuseStep 3100873 = 2325655) B2325655
theorem B4134497 : Blo 2037435 4134497 := bstep (se 2 (by rfl) ⟨1550436, by rfl⟩ : syracuseStep 4134497 = 3100873) B3100873
theorem B11025325 : Blo 2037435 11025325 := bstep (se 3 (by rfl) ⟨2067248, by rfl⟩ : syracuseStep 11025325 = 4134497) B4134497
theorem B58801733 : Blo 2037435 58801733 := bstep (se 4 (by rfl) ⟨5512662, by rfl⟩ : syracuseStep 58801733 = 11025325) B11025325
theorem B39201155 : Blo 2037435 39201155 := bstep (se 1 (by rfl) ⟨29400866, by rfl⟩ : syracuseStep 39201155 = 58801733) B58801733
theorem B26134103 : Blo 2037435 26134103 := bstep (se 1 (by rfl) ⟨19600577, by rfl⟩ : syracuseStep 26134103 = 39201155) B39201155
theorem B17422735 : Blo 2037435 17422735 := bstep (se 1 (by rfl) ⟨13067051, by rfl⟩ : syracuseStep 17422735 = 26134103) B26134103
theorem B23230313 : Blo 2037435 23230313 := bstep (se 2 (by rfl) ⟨8711367, by rfl⟩ : syracuseStep 23230313 = 17422735) B17422735
theorem B15486875 : Blo 2037435 15486875 := bstep (se 1 (by rfl) ⟨11615156, by rfl⟩ : syracuseStep 15486875 = 23230313) B23230313
theorem B10324583 : Blo 2037435 10324583 := bstep (se 1 (by rfl) ⟨7743437, by rfl⟩ : syracuseStep 10324583 = 15486875) B15486875
theorem B6883055 : Blo 2037435 6883055 := bstep (se 1 (by rfl) ⟨5162291, by rfl⟩ : syracuseStep 6883055 = 10324583) B10324583
theorem B4588703 : Blo 2037435 4588703 := bstep (se 1 (by rfl) ⟨3441527, by rfl⟩ : syracuseStep 4588703 = 6883055) B6883055
theorem B3059135 : Blo 2037435 3059135 := bstep (se 1 (by rfl) ⟨2294351, by rfl⟩ : syracuseStep 3059135 = 4588703) B4588703
theorem B2039423 : Blo 2037435 2039423 := bstep (se 1 (by rfl) ⟨1529567, by rfl⟩ : syracuseStep 2039423 = 3059135) B3059135
theorem B3059141 : Blo 2037435 3059141 := bbase (se 4 (by rfl) ⟨286794, by rfl⟩ : syracuseStep 3059141 = 573589) (by norm_num)
theorem B2039427 : Blo 2037435 2039427 := bstep (se 1 (by rfl) ⟨1529570, by rfl⟩ : syracuseStep 2039427 = 3059141) B3059141
theorem B3441541 : Blo 2037435 3441541 := bbase (se 4 (by rfl) ⟨322644, by rfl⟩ : syracuseStep 3441541 = 645289) (by norm_num)
theorem B4588721 : Blo 2037435 4588721 := bstep (se 2 (by rfl) ⟨1720770, by rfl⟩ : syracuseStep 4588721 = 3441541) B3441541
theorem B3059147 : Blo 2037435 3059147 := bstep (se 1 (by rfl) ⟨2294360, by rfl⟩ : syracuseStep 3059147 = 4588721) B4588721
theorem B2039431 : Blo 2037435 2039431 := bstep (se 1 (by rfl) ⟨1529573, by rfl⟩ : syracuseStep 2039431 = 3059147) B3059147
theorem B2294365 : Blo 2037435 2294365 := bbase (se 3 (by rfl) ⟨430193, by rfl⟩ : syracuseStep 2294365 = 860387) (by norm_num)
theorem B3059153 : Blo 2037435 3059153 := bstep (se 2 (by rfl) ⟨1147182, by rfl⟩ : syracuseStep 3059153 = 2294365) B2294365
theorem B2039435 : Blo 2037435 2039435 := bstep (se 1 (by rfl) ⟨1529576, by rfl⟩ : syracuseStep 2039435 = 3059153) B3059153
theorem C0 (j : ℕ) (h1 : 509358 ≤ j) (h2 : j ≤ 509858) : Blo 2037435 (4 * j + 3) := by
  interval_cases j
  · exact B2037435
  · exact B2037439
  · exact B2037443
  · exact B2037447
  · exact B2037451
  · exact B2037455
  · exact B2037459
  · exact B2037463
  · exact B2037467
  · exact B2037471
  · exact B2037475
  · exact B2037479
  · exact B2037483
  · exact B2037487
  · exact B2037491
  · exact B2037495
  · exact B2037499
  · exact B2037503
  · exact B2037507
  · exact B2037511
  · exact B2037515
  · exact B2037519
  · exact B2037523
  · exact B2037527
  · exact B2037531
  · exact B2037535
  · exact B2037539
  · exact B2037543
  · exact B2037547
  · exact B2037551
  · exact B2037555
  · exact B2037559
  · exact B2037563
  · exact B2037567
  · exact B2037571
  · exact B2037575
  · exact B2037579
  · exact B2037583
  · exact B2037587
  · exact B2037591
  · exact B2037595
  · exact B2037599
  · exact B2037603
  · exact B2037607
  · exact B2037611
  · exact B2037615
  · exact B2037619
  · exact B2037623
  · exact B2037627
  · exact B2037631
  · exact B2037635
  · exact B2037639
  · exact B2037643
  · exact B2037647
  · exact B2037651
  · exact B2037655
  · exact B2037659
  · exact B2037663
  · exact B2037667
  · exact B2037671
  · exact B2037675
  · exact B2037679
  · exact B2037683
  · exact B2037687
  · exact B2037691
  · exact B2037695
  · exact B2037699
  · exact B2037703
  · exact B2037707
  · exact B2037711
  · exact B2037715
  · exact B2037719
  · exact B2037723
  · exact B2037727
  · exact B2037731
  · exact B2037735
  · exact B2037739
  · exact B2037743
  · exact B2037747
  · exact B2037751
  · exact B2037755
  · exact B2037759
  · exact B2037763
  · exact B2037767
  · exact B2037771
  · exact B2037775
  · exact B2037779
  · exact B2037783
  · exact B2037787
  · exact B2037791
  · exact B2037795
  · exact B2037799
  · exact B2037803
  · exact B2037807
  · exact B2037811
  · exact B2037815
  · exact B2037819
  · exact B2037823
  · exact B2037827
  · exact B2037831
  · exact B2037835
  · exact B2037839
  · exact B2037843
  · exact B2037847
  · exact B2037851
  · exact B2037855
  · exact B2037859
  · exact B2037863
  · exact B2037867
  · exact B2037871
  · exact B2037875
  · exact B2037879
  · exact B2037883
  · exact B2037887
  · exact B2037891
  · exact B2037895
  · exact B2037899
  · exact B2037903
  · exact B2037907
  · exact B2037911
  · exact B2037915
  · exact B2037919
  · exact B2037923
  · exact B2037927
  · exact B2037931
  · exact B2037935
  · exact B2037939
  · exact B2037943
  · exact B2037947
  · exact B2037951
  · exact B2037955
  · exact B2037959
  · exact B2037963
  · exact B2037967
  · exact B2037971
  · exact B2037975
  · exact B2037979
  · exact B2037983
  · exact B2037987
  · exact B2037991
  · exact B2037995
  · exact B2037999
  · exact B2038003
  · exact B2038007
  · exact B2038011
  · exact B2038015
  · exact B2038019
  · exact B2038023
  · exact B2038027
  · exact B2038031
  · exact B2038035
  · exact B2038039
  · exact B2038043
  · exact B2038047
  · exact B2038051
  · exact B2038055
  · exact B2038059
  · exact B2038063
  · exact B2038067
  · exact B2038071
  · exact B2038075
  · exact B2038079
  · exact B2038083
  · exact B2038087
  · exact B2038091
  · exact B2038095
  · exact B2038099
  · exact B2038103
  · exact B2038107
  · exact B2038111
  · exact B2038115
  · exact B2038119
  · exact B2038123
  · exact B2038127
  · exact B2038131
  · exact B2038135
  · exact B2038139
  · exact B2038143
  · exact B2038147
  · exact B2038151
  · exact B2038155
  · exact B2038159
  · exact B2038163
  · exact B2038167
  · exact B2038171
  · exact B2038175
  · exact B2038179
  · exact B2038183
  · exact B2038187
  · exact B2038191
  · exact B2038195
  · exact B2038199
  · exact B2038203
  · exact B2038207
  · exact B2038211
  · exact B2038215
  · exact B2038219
  · exact B2038223
  · exact B2038227
  · exact B2038231
  · exact B2038235
  · exact B2038239
  · exact B2038243
  · exact B2038247
  · exact B2038251
  · exact B2038255
  · exact B2038259
  · exact B2038263
  · exact B2038267
  · exact B2038271
  · exact B2038275
  · exact B2038279
  · exact B2038283
  · exact B2038287
  · exact B2038291
  · exact B2038295
  · exact B2038299
  · exact B2038303
  · exact B2038307
  · exact B2038311
  · exact B2038315
  · exact B2038319
  · exact B2038323
  · exact B2038327
  · exact B2038331
  · exact B2038335
  · exact B2038339
  · exact B2038343
  · exact B2038347
  · exact B2038351
  · exact B2038355
  · exact B2038359
  · exact B2038363
  · exact B2038367
  · exact B2038371
  · exact B2038375
  · exact B2038379
  · exact B2038383
  · exact B2038387
  · exact B2038391
  · exact B2038395
  · exact B2038399
  · exact B2038403
  · exact B2038407
  · exact B2038411
  · exact B2038415
  · exact B2038419
  · exact B2038423
  · exact B2038427
  · exact B2038431
  · exact B2038435
  · exact B2038439
  · exact B2038443
  · exact B2038447
  · exact B2038451
  · exact B2038455
  · exact B2038459
  · exact B2038463
  · exact B2038467
  · exact B2038471
  · exact B2038475
  · exact B2038479
  · exact B2038483
  · exact B2038487
  · exact B2038491
  · exact B2038495
  · exact B2038499
  · exact B2038503
  · exact B2038507
  · exact B2038511
  · exact B2038515
  · exact B2038519
  · exact B2038523
  · exact B2038527
  · exact B2038531
  · exact B2038535
  · exact B2038539
  · exact B2038543
  · exact B2038547
  · exact B2038551
  · exact B2038555
  · exact B2038559
  · exact B2038563
  · exact B2038567
  · exact B2038571
  · exact B2038575
  · exact B2038579
  · exact B2038583
  · exact B2038587
  · exact B2038591
  · exact B2038595
  · exact B2038599
  · exact B2038603
  · exact B2038607
  · exact B2038611
  · exact B2038615
  · exact B2038619
  · exact B2038623
  · exact B2038627
  · exact B2038631
  · exact B2038635
  · exact B2038639
  · exact B2038643
  · exact B2038647
  · exact B2038651
  · exact B2038655
  · exact B2038659
  · exact B2038663
  · exact B2038667
  · exact B2038671
  · exact B2038675
  · exact B2038679
  · exact B2038683
  · exact B2038687
  · exact B2038691
  · exact B2038695
  · exact B2038699
  · exact B2038703
  · exact B2038707
  · exact B2038711
  · exact B2038715
  · exact B2038719
  · exact B2038723
  · exact B2038727
  · exact B2038731
  · exact B2038735
  · exact B2038739
  · exact B2038743
  · exact B2038747
  · exact B2038751
  · exact B2038755
  · exact B2038759
  · exact B2038763
  · exact B2038767
  · exact B2038771
  · exact B2038775
  · exact B2038779
  · exact B2038783
  · exact B2038787
  · exact B2038791
  · exact B2038795
  · exact B2038799
  · exact B2038803
  · exact B2038807
  · exact B2038811
  · exact B2038815
  · exact B2038819
  · exact B2038823
  · exact B2038827
  · exact B2038831
  · exact B2038835
  · exact B2038839
  · exact B2038843
  · exact B2038847
  · exact B2038851
  · exact B2038855
  · exact B2038859
  · exact B2038863
  · exact B2038867
  · exact B2038871
  · exact B2038875
  · exact B2038879
  · exact B2038883
  · exact B2038887
  · exact B2038891
  · exact B2038895
  · exact B2038899
  · exact B2038903
  · exact B2038907
  · exact B2038911
  · exact B2038915
  · exact B2038919
  · exact B2038923
  · exact B2038927
  · exact B2038931
  · exact B2038935
  · exact B2038939
  · exact B2038943
  · exact B2038947
  · exact B2038951
  · exact B2038955
  · exact B2038959
  · exact B2038963
  · exact B2038967
  · exact B2038971
  · exact B2038975
  · exact B2038979
  · exact B2038983
  · exact B2038987
  · exact B2038991
  · exact B2038995
  · exact B2038999
  · exact B2039003
  · exact B2039007
  · exact B2039011
  · exact B2039015
  · exact B2039019
  · exact B2039023
  · exact B2039027
  · exact B2039031
  · exact B2039035
  · exact B2039039
  · exact B2039043
  · exact B2039047
  · exact B2039051
  · exact B2039055
  · exact B2039059
  · exact B2039063
  · exact B2039067
  · exact B2039071
  · exact B2039075
  · exact B2039079
  · exact B2039083
  · exact B2039087
  · exact B2039091
  · exact B2039095
  · exact B2039099
  · exact B2039103
  · exact B2039107
  · exact B2039111
  · exact B2039115
  · exact B2039119
  · exact B2039123
  · exact B2039127
  · exact B2039131
  · exact B2039135
  · exact B2039139
  · exact B2039143
  · exact B2039147
  · exact B2039151
  · exact B2039155
  · exact B2039159
  · exact B2039163
  · exact B2039167
  · exact B2039171
  · exact B2039175
  · exact B2039179
  · exact B2039183
  · exact B2039187
  · exact B2039191
  · exact B2039195
  · exact B2039199
  · exact B2039203
  · exact B2039207
  · exact B2039211
  · exact B2039215
  · exact B2039219
  · exact B2039223
  · exact B2039227
  · exact B2039231
  · exact B2039235
  · exact B2039239
  · exact B2039243
  · exact B2039247
  · exact B2039251
  · exact B2039255
  · exact B2039259
  · exact B2039263
  · exact B2039267
  · exact B2039271
  · exact B2039275
  · exact B2039279
  · exact B2039283
  · exact B2039287
  · exact B2039291
  · exact B2039295
  · exact B2039299
  · exact B2039303
  · exact B2039307
  · exact B2039311
  · exact B2039315
  · exact B2039319
  · exact B2039323
  · exact B2039327
  · exact B2039331
  · exact B2039335
  · exact B2039339
  · exact B2039343
  · exact B2039347
  · exact B2039351
  · exact B2039355
  · exact B2039359
  · exact B2039363
  · exact B2039367
  · exact B2039371
  · exact B2039375
  · exact B2039379
  · exact B2039383
  · exact B2039387
  · exact B2039391
  · exact B2039395
  · exact B2039399
  · exact B2039403
  · exact B2039407
  · exact B2039411
  · exact B2039415
  · exact B2039419
  · exact B2039423
  · exact B2039427
  · exact B2039431
  · exact B2039435
theorem solution (m : ℕ) (hlo : 2037435 ≤ m) (hhi : m ≤ 2039435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 509358 ≤ j := by omega
    have hj2 : j ≤ 509858 := by omega
    have hb : Blo 2037435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
